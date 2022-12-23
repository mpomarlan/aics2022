import os
import sys
import time
import pickle
import functools

def qualityPrefix(s):
    if '_' in s:
        return s[:s.find('_')]
    return ''

def getConclusionRankingInternal(premise, theory):
    retq = []
    for r in reversed(theory):
        if (not r[0].difference(premise)) and (not r[1] in retq):
            retq.append(r[1])
    return retq

def getConclusionsRanking(premise, theories):
    if not theories:
        return []
    conclusions = [getConclusionRankingInternal(premise, t) for t in theories]
    minlen = min([len(x) for x in conclusions])
    conclusions = [x[:minlen] for x in conclusions]
    return [tuple([x[k] for x in conclusions]) for k, _ in enumerate(conclusions[0])]

def evaluateEntry(premise, correctConclusions, theories, atK):
    conclusions = getConclusionsRanking(premise, theories)
    if not conclusions:
        return 0, 0.0, 0
    accInc = 0
    mrrInc = 0.0
    hitsInc = 0
    if correctConclusions == conclusions[0]:
        accInc = 1
    if correctConclusions in conclusions:
        mrrInc = 1.0/(1.0 + conclusions.index(correctConclusions))
        if correctConclusions in conclusions[:atK]:
            hitsInc = 1
    return accInc, mrrInc, hitsInc

def makePairs(records, premisePrefs, conclusionPrefs):
    concsPrefS = set(conclusionPrefs)
    retq = [(frozenset([y for y in x if qualityPrefix(y) in premisePrefs]), {qualityPrefix(y): y for y in x if qualityPrefix(y) in conclusionPrefs}) for x in records]
    retq = [r for r in retq if not concsPrefS.difference(set(r[1].keys()))]
    return [(r[0], tuple([r[1][pref] for pref in conclusionPrefs])) for r in retq]

def argMaxUnique(d):
    maxval = None
    argmax = []
    for k, v in d.items():
        if (None == maxval) or (maxval < v):
            argmax = [k]
            maxval = v
        elif maxval == v:
            argmax.append(k)
    if 1 == len(argmax):
        return argmax[0]
    return None

def makeConsistentTraining(pairs):
    retq = {}
    for pair in pairs:
        if pair[0] not in retq:
            retq[pair[0]] = {}
        if pair[1] not in retq[pair[0]]:
            retq[pair[0]][pair[1]] = 0
        retq[pair[0]][pair[1]] += 0
    retq = {k: argMaxUnique(retq[k]) for k in retq}
    return {k: v for k, v in retq.items() if (None != v)}

def makeFairTest(pairsTest, consistentTraining):
    def asPerTraining(x, consistentTraining):
        if x[0] in consistentTraining:
            return (x[0], consistentTraining[x[0]])
        return (x[0], x[1])
    conclusionVocabulary = functools.reduce(lambda x,y: x.union(y), [frozenset()] + list(consistentTraining.values()))
    return [asPerTraining(x, consistentTraining) for x in pairsTest if not set(x[1]).difference(conclusionVocabulary)]

def makeSplitEntries(records, splitRatio, premisePrefs, conclusionPrefs, theories):
    cut = int(splitRatio*len(records))
    pairsTrainRaw = makePairs(records[:cut], premisePrefs, conclusionPrefs)
    pairsTestRaw = makePairs(records[cut:], premisePrefs, conclusionPrefs)
    pairsTrainConsistent = makeConsistentTraining(pairsTrainRaw)
    pairsTestFair = makeFairTest(pairsTestRaw, pairsTrainConsistent)
    return list(pairsTrainConsistent.items()), pairsTestFair

def testTheories(records, splitRatio, premisePrefs, conclusionPrefs, theories, atK):
    _, pairsTest = makeSplitEntries(records, splitRatio, premisePrefs, conclusionPrefs, theories)
    acc = 0
    mrr = 0.0
    hits = 0
    n = len(pairsTest)
    startT = time.perf_counter()
    for t in pairsTest:
        accInc, mrrInc, hitsInc = evaluateEntry(t[0], t[1], theories, atK)
        acc = acc + accInc
        mrr = mrr + mrrInc
        hits = hits + hitsInc
    endT = time.perf_counter()
    return 100*acc/n, 100*mrr/n, 100*hits/n, endT-startT

#allPrefixes = ['', 'color', 'dimension', 'material', 'physical', 'price', 'shape', 'size', 'transparency', 'weight', 'cleanliness', 'dampness', 'fullness', 'place', 'room', 'temperature']
allPrefixes = ['', 'material', 'color', 'transparency', 'dimension', 'physical', 'shape', 'temperature', 'fullness', 'dampness', 'cleanliness', 'room', 'place', 'price', 'weight', 'size']
def allButPrefix(pref):
    return [x for x in allPrefixes if x != pref]

def runTestInternal(pathTemplate, splitRatio, testCaption):
    def qName(pref):
        if '' == pref:
            return 'class'
        return pref
    def guessingTask(taskName, premisePrefs, conclusionPrefs):
        results = [testTheories(x['records'], 0.7, premisePrefs, conclusionPrefs, [x['theory'][prefix2Idx[pref]] for pref in conclusionPrefs], 3) for x in data]
        guessResults = [sum([x[0] for x in results])/len(data), sum([x[1] for x in results])/len(data), sum([x[2] for x in results])/len(data), sum([x[3] for x in results])]
        print("%s results (acc, mrr, hits@3): %3.02f %3.02f %3.02f" % (taskName, guessResults[0], guessResults[1], guessResults[2]))
    print(testCaption)
    data = []
    for k in range(10):
        with open(pathTemplate % (splitRatio, k), 'rb') as outfile:
            data.append(pickle.load(outfile))
    prefix2Idx = {qualityPrefix(list(x)[0]): k for k, x in enumerate(data[0]['mutexsets'])}
    basicResults = {}
    print("Basic results for guessing a quality from all others:")
    for pref in allPrefixes:
        results = [testTheories(x['records'], 0.7, allButPrefix(pref), [pref], [x['theory'][prefix2Idx[pref]]], 3) for x in data]
        basicResults[pref] = [sum([x[0] for x in results])/len(data), sum([x[1] for x in results])/len(data), sum([x[2] for x in results])/len(data), sum([x[3] for x in results])]
        print("\tBasic test for quality '%s' (acc mrr hits@3 | time): %3.02f %3.02f %3.02f | %3.02f" % (qName(pref), basicResults[0], basicResults[1], basicResults[2]), basicResults[pref])
    print("Total time for basic tests: %f" % sum([x[3] for x in basicResults]))
    guessingTask('Guess-Room', ['', 'cleanliness', 'temperature'], ['room'])
    guessingTask('Guess-Place', ['', 'cleanliness', 'temperature', 'room'], ['place'])
    guessingTask('Guess-Fullness', ['', 'cleanliness', 'temperature', 'room', 'place'], ['fullness'])

def runTest():
    runTestInternal("no_bias_log_%0.02f_%d.log", 0.7, "Running tests for NO BIAS HeRO search")
    runTestInternal("kn_bias_log_%0.02f_%d.log", 0.7, "Running tests for KNOWLEDGE-BASED BIAS HeRO search")

def getPrefix(p):
    idx = p.find('_')
    if -1 == idx:
        return ''
    return p[:idx]

def makePref2TheoryMap(theories):
    retq = {}
    for t in theories:
        mset = getPrefix(t[0][1])
        retq[mset] = t
    return retq

def makeTestcase(entry, mset):
    premise = set([])
    conclusion = None
    for e in entry:
        pref = getPrefix(e)
        if mset == pref:
            conclusion = e
        else:
            premise.add(e)
    return conclusion, premise

def getAndExplainConclusion(premise, theory):
    maxSupportingRule = None
    otherSupportingRules = []
    for r in reversed(theory):
        if (not r[0].difference(premise)):
            if maxSupportingRule is None:
                maxSupportingRule = r
            elif maxSupportingRule[1] == r[1]:
                otherSupportingRules.append(r)
            else:
                break
    return maxSupportingRule, otherSupportingRules

def getAndCounterfactuallyExplainConclusion(premise, theory, counterfactualConclusion):
    def setPremiseForRule(premise, rule):
        diff = set()
        newPremise = set(premise)
        prefs = {getPrefix(x): x for x in newPremise}
        for e in rule[0]:
            if e not in premise:
                mset = getPrefix(e)
                if mset in prefs:
                    newPremise.remove(prefs[mset])
                newPremise.add(e)
                prefs[mset] = e
                diff.add(e)
        return diff, newPremise
    def updatePremise(diff, premise, makeTrue=None, makeFalse=None):
        diff = set(diff)
        newPremise = set(premise)
        prefs = {getPrefix(x): x for x in newPremise}
        if makeTrue is None:
            makeTrue = []
        if makeFalse is None:
            makeFalse = []
        for p in makeTrue:
            mset = getPrefix(p)
            if (mset in prefs) and (p not in newPremise):
                newPremise.remove(prefs[mset])
                diff.add(p)
                newPremise.add(p)
            else:
                diff.add(p)
                newPremise.add(p)
            prefs[mset] = p
        for p in makeFalse:
            mset = getPrefix(p)
            np = '-'+p
            if mset in prefs:
                if p in newPremise:
                    newPremise.remove(p)
                    diff.add(np)
                    newPremise.add(np)
                    prefs[mset] = np
            else:
                diff.add(np)
                newPremise.add(np)
                prefs[mset] = np
        return diff, newPremise
    def makeItWork(premise, rule, ruleIdx, theory):
        diff, newPremise = setPremiseForRule(premise, rule)
        for r in theory[ruleIdx+1:]:
            if (r[1] != rule[1]) and (not r[0].difference(newPremise)):
                diff, newPremise = updatePremise(diff, newPremise, makeTrue=None, makeFalse=r[0].difference(rule))
        return diff, newPremise
    maxSupportingRule, otherSupportingRules = getAndExplainConclusion(premise, theory)
    if maxSupportingRule[1] == counterfactualConclusion:
        return [], maxSupportingRule, otherSupportingRules, maxSupportingRule, otherSupportingRules
    answer = None
    counterfactualPremise = None
    for k, r in enumerate(theory):
        if counterfactualConclusion == r[1]:
            candidate, newPremise = makeItWork(premise, r, k, theory)
            if (answer is None) or (len(answer) > len(candidate)):
                answer = candidate
                counterfactualPremise = newPremise
    maxCounterfactualRule, otherCounterfactualRules = getAndExplainConclusion(counterfactualPremise, theory)
    return answer, maxSupportingRule, otherSupportingRules, maxCounterfactualRule, otherCounterfactualRules

def getDefaultExemplar(conclusion, theory):
    supportingRules = []
    for r in theory:
        if conclusion == r[1]:
                supportingRules.append(r)
    if [] == supportingRules:
        return None, []
    return supportingRules[0], supportingRules[1:]

def updateTheory(oldRule, theory, newRule):
    if oldRule not in theory:
        return None
    k = theory.index(oldRule)
    theory[k] = newRule
    askAbout = []
    for r in theory[k+1:]:
        if (not oldRule[0].difference(r[0])) or (not newRule[0].difference(r[0])):
            askAbout.append(r)
    return askAbout

def printRule(rule):
    ants = sorted([(getPrefix(x), x) for x in rule[0]])
    retq = ""
    for a in ants:
        retq = retq + a[1] + ', '
    retq = retq[:-2] + ' => ' + rule[1]
    return retq

if "__main__" == __name__:
    runTest()
