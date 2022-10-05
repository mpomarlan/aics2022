import ast
import pickle
import random
import time
from heapq import *

def qualityPrefix(s):
    if '_' in s:
        return s[:s.find('_')]
    return ''

def datasetFromRecords(records):
    dataset = []
    for r in records:
        for k, d in enumerate(r):
            dataset.append((frozenset(r[:k] + r[k+1:]), d))
    return dataset

def splitDataset(pairs, mutexsets):
    retq = {}
    for pair in pairs:
        premise, conclusion = pair
        prefix = qualityPrefix(conclusion)
        if prefix not in retq:
            retq[prefix] = []
        retq[prefix].append(pair)
    return list(retq.values())

def getMutexMap(mutexsets):
    retq = {}
    for ms in mutexsets:
        for e in ms:
            retq[e] = ms.difference([e])
    return retq
    
def argMaxUnique(d):
    maxVal = None
    argMax = []
    for k, v in d.items():
        if (None == maxVal) or (maxVal < v):
            argMax = [k]
        elif (maxVal == v):
            argMax.append(k)
    if 1 == len(argMax):
        return argMax[0]
    return None

def prepConflictDataset(pairs, mutexset):
    dataset = {}
    for pair in pairs:
        premise, conclusion = pair
        premise = frozenset(premise)
        if premise not in dataset:
            dataset[premise] = {}
        if conclusion not in dataset[premise]:
            dataset[premise][conclusion] = 0
        dataset[premise][conclusion] = dataset[premise][conclusion] + 1
    retq = []
    for premise in dataset:
        argMax = argMaxUnique(dataset[premise])
        if None != argMax:
           retq.append((premise, argMax))
    return retq

def compatible(premise, term, mutexMap):
    if term not in mutexMap:
        return True
    for t in premise:
        if t in mutexMap[term]:
            return False
    return True
    
def preferredConclusion(dataset, decidedByRule):
    surprises = {}
    corrects = {}
    for e in dataset:
        fact, conc = e
        expected = None
        if None != decidedByRule[e]:
            expected = decidedByRule[e][1]
        if (None == expected) or (conc != expected):
            if conc not in surprises:
                surprises[conc] = 0
            surprises[conc] = surprises[conc] + 1
        elif conc == expected:
            if conc not in corrects:
                corrects[conc] = 0
            corrects[conc] = corrects[conc] + 1
    if not surprises:
        return None, -1, -100, -100
    surprises = sorted([(-surprises[x], x) for x in surprises])
    maxgain = -surprises[0][0]
    conclusion = surprises[0][1]
    gain = maxgain
    for c in corrects:
        if conclusion != c:
            gain = gain - corrects[c]
    correctConclusion = maxgain
    if conclusion in corrects:
        correctConclusion = correctConclusion + corrects[conclusion]
    reliability = (correctConclusion)/len(dataset)
    return conclusion, reliability, gain, maxgain

def ruleSearch(dataset, mutexset, mutexMap, theory, vocabulary, decidedByRule, ruleAtLevel, epoch):
    bestGain = 0
    bestPremise = None
    bestConclusion = None
    bestLevel = None
    bestApplicable = None
    levelRange = [len(theory)]
    levelRange = range(1 + len(theory))
    addedPrems = set([x[0] for x in theory])
    for level in levelRange:
        theoryUpToLevel = [(frozenset(), None)] + theory[:level]
        datasetUpToLevel = [x for x in dataset if (None == decidedByRule[x]) or (level > ruleAtLevel[decidedByRule[x]])]
        queue = []
        for r in theoryUpToLevel:
            for v in vocabulary:
                if (v not in mutexset) and (v not in r[0]):
                    if not compatible(r[0], v, mutexMap):
                        continue
                    premise = r[0].union([v])
                    if premise in addedPrems:
                        continue
                    addedPrems.add(premise)
                    aux = [x for x in datasetUpToLevel if not premise.difference(x[0])]
                    conclusion, reliability, gain, maxgain = preferredConclusion(aux, decidedByRule)
                    if conclusion in epoch:
                        continue
                    if (None != conclusion) and (bestGain < maxgain):
                        heappush(queue, (-reliability, -maxgain, -gain, premise, aux, conclusion))
                    if bestGain < gain:
                        bestGain = gain
                        bestPremise = premise
                        bestConclusion = conclusion
                        bestLevel = level
                        bestApplicable = aux
                        #queue = []
        queue = queue[:10]
        while queue:
            _, _, _, premise, applicableDataset, _ = heappop(queue)
            for v in vocabulary:
                if (v not in mutexset) and (v not in premise) and compatible(premise, v, mutexMap):
                    crpremise = premise.union([v])
                    if crpremise in addedPrems:
                        continue
                    addedPrems.add(crpremise)
                    aux = [x for x in applicableDataset if v in x[0]]
                    if aux:
                        nconclusion, reliability, ngain, nmaxgain = preferredConclusion(aux, decidedByRule)
                        if (None == nconclusion) or (conclusion in epoch):
                            continue
                        if bestGain < nmaxgain:
                            heappush(queue, (-reliability, -nmaxgain, -ngain, crpremise, aux, nconclusion))
                        if 10 < len(queue):
                            queue = queue[:10]
                        if bestGain < ngain:
                            bestGain = ngain
                            bestPremise = crpremise
                            bestConclusion = nconclusion
                            bestLevel = level
                            bestApplicable = aux
                            #queue = []
    if 0 < bestGain:
        return True, (bestPremise, bestConclusion), bestLevel, bestApplicable
    else:
        return False, None, None, None

def HeRO(dataset, mutexset, mutexMap, vocabulary, epochal=True, restrictions=None):
    dataset = prepConflictDataset(dataset, mutexset)
    theory = []
    work = True
    decidedByRule = {x: None for x in dataset}
    ruleAtLevel = {}
    epoch = set()
    vocabularySel = vocabulary
    print("HeRO for prefix '%s'" % qualityPrefix(list(mutexset)[0]))
    if None != restrictions:
        crProp = qualityPrefix(list(mutexset)[0])
        if crProp in restrictions:
            vocabularySel = [x for x in vocabulary if qualityPrefix(x) in restrictions[crProp]]
    while work:
        work, rule, level, bestApplicable = ruleSearch(dataset, mutexset, mutexMap, theory, vocabularySel, decidedByRule, ruleAtLevel, epoch)
        print("    ", work, rule, level)
        if work:
            if epochal:
                epoch.add(rule[1])
                if not mutexset.difference(epoch):
                    epoch = set()
            theory = theory[:level] + [rule] + theory[level:]
            for r in ruleAtLevel:
                if level <= ruleAtLevel[r]:
                    ruleAtLevel[r] = ruleAtLevel[r] + 1
            ruleAtLevel[rule] = level
            for e in bestApplicable:
                decidedByRule[e] = rule
    return theory

def multiHeRO(dataset, mutexsets, vocabulary, epochal=True, restrictions=None):
    datasets = splitDataset(dataset, mutexsets)
    mutexMap = getMutexMap(mutexsets)
    theories = []
    results = []
    for ms, ds in zip(mutexsets, datasets):
        theory = HeRO(ds, ms, mutexMap, vocabulary, epochal=epochal, restrictions=restrictions)
        theories.append(theory)
    return theories
    
def trainWithSplitInternal(recordsDFL, splitRatio, mutexsets, runIndex, pathTemplate, restrictions=None):
    recordsShuffled = list(recordsDFL)
    random.shuffle(recordsShuffled)
    cut = int(len(records)*splitRatio)
    trainRecords = recordsShuffled[:cut]
    vocabulary = set().union(*trainRecords)
    train = datasetFromRecords(trainRecords)
    startTrain = time.perf_counter()
    theories = multiHeRO(train, mutexsets, vocabulary, restrictions=restrictions)
    endTrain = time.perf_counter()
    with open(pathTemplate % (splitRatio, runIndex), "wb") as outfile:
            pickle.dump({"durationTrain": endTrain-startTrain, "theory": theories, "mutexsets": mutexsets, "records": recordsShuffled, "restrictions": restrictions}, outfile)

def trainWithSplit(recordsDFL, splitRatio, mutexsets, runCount, pathTemplate, restrictions=None):
    for k in range(runCount):
        trainWithSplitInternal(recordsDFL, splitRatio, mutexsets, k, pathTemplate, restrictions=restrictions)


records = [ast.literal_eval(x) for x in open("records_dfl.txt").read().splitlines() if x.strip()]

restrictionBias = {
    '': {'color', 'dimension', 'material', 'physical', 'price', 'shape', 'size', 'transparency', 'weight'},
    'color': {'', 'material', 'physical', 'price', 'transparency'},
    'dimension': {'', 'material', 'physical', 'price', 'shape', 'size', 'weight'},
    'material': {'', 'color', 'dimension', 'physical', 'price', 'shape', 'size', 'transparency', 'weight'},
    'physical': {'', 'color', 'dimension', 'material', 'shape', 'size', 'transparency', 'weight'},
    'price': {'', 'material', 'size', 'weight'},
    'shape': {'', 'dimension', 'material', 'physical', 'size', 'transparency', 'weight'},
    'size': {'', 'dimension', 'material', 'physical', 'shape', 'weight'},
    'transparency': {'', 'color', 'dimension', 'material', 'physical', 'price', 'size'},
    'weight': {'', 'dimension', 'material', 'size'},
    'cleanliness': {'dampness', 'fullness', 'place', 'room', 'temperature', '', 'material', 'physical', 'price', 'transparency'},
    'dampness': {'room', 'place', '', 'cleanliness', 'fullness', 'temperature'},
    'fullness': {'cleanliness', 'dampness', 'place', 'room', 'temperature', '', 'material', 'physical'},
    'place': {'cleanliness', 'dampness', 'fullness', 'room', 'temperature', '', 'dimension', 'material', 'physical', 'price', 'shape', 'size'},
    'room': {'cleanliness', 'dampness', 'fullness', 'place', 'temperature', '', 'dimension', 'material', 'physical', 'price', 'shape', 'size'},
    'temperature': {'room', 'place', 'dampness', 'fullness'},
}

def runTraining():
    mutexsetsByKey = {}
    for r in records:
        for e in r:
            k = qualityPrefix(e)
            if k not in mutexsetsByKey:
                mutexsetsByKey[k] = set()
            mutexsetsByKey[k].add(e)
    mutexsets = list(mutexsetsByKey.values())
    trainWithSplit(records, 0.7, mutexsets, 10, "no_bias_log_%0.02f_%d.log", restrictions=None)
    trainWithSplit(records, 0.7, mutexsets, 10, "kn_bias_log_%0.02f_%d.log", restrictions=restrictionBias)

if "__main__" == __name__:
    runTraining()
