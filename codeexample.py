import pickle
import testing

dataFileName = 'knrestriction_log_0.70_9.log'

# Initialization:
#    load from pickle file
with open(dataFileName, 'rb') as infile:
    data = pickle.load(infile)

#
#    theories, mutexsets etc are in a list in the pickle, but it is convenient to just have access to a theory for
# a given prefix directly
#    e.g., pref2Theory[''] is the theory to identify object type from the provided data
#    pref2Theory['transparency'] is the theory for transparency etc.
pref2Theory = testing.makePref2TheoryMap(data['theory'])
#
#    get a list of records used for test; each record is a complete situation, i.e. full knowledge of the object
# a query is made by splitting this information into a conclusion, ie one of the facts in the situation, and all
# other facts of the situation make up the premise
testRecords = data['records'][int(len(data['records'])*0.7):]
#
#    create a list of test records on which the theory and human annotators do not agree
def getFailedRecords(records, prefix):
    failedRecords = []
    for r in testRecords:
        conc, prem = testing.makeTestcase(r, prefix)
        msr, osr = testing.getAndExplainConclusion(prem, pref2Theory[prefix])
        if (msr is not None) and (conc != msr[1]):
            failedRecords.append(r)
    return failedRecords


# Example: how to get a "typical" something
#     input arguments: what sort of thing is sought; what theory to use
#     outputs: the typical exemplar; a list of other exemplars. All these are rules from the theory with conclusion
#       equal to the sought thing
answer, others = testing.getDefaultExemplar('transparency_transparent', pref2Theory['transparency'])
print(testing.printRule(answer))
_ = [print(testing.printRule(x)) for x in others]



# Example: how to get a simple explanation
#     input arguments: premise for the reasoning; which theory to use
#     outputs: maximum priority rule applicable to the situation of the premise; a list of other rules supporting
#       the SAME conclusion, applicable in the situation of the premise, NOT defeated by any opponents, in descending 
#       priority order
# The semantics here is that any of the rules among max.., other.. are able to establish the conclusion in the given
#   situation without being defeated by any rules supporting another conclusion.
# Rules have the form (premise, conclusion) where premise is a [frozen]set and conclusion is a string.
conclusion, premise = testing.makeTestcase(testRecords[0], '')
maxSupportingRule, otherSupportingRules = testing.getAndExplainConclusion(premise, pref2Theory[''])
print(testing.printRule(maxSupportingRule))
_ = [print(testing.printRule(x)) for x in otherSupportingRules]



# Example: how to get a counterfactual explanation
#     input arguments: premise for the reasoning; which theory to use; what conclusion to use as counterfactual
#     outputs: a set of differences that would be needed to make the counterfactual conclusion hold; the maximum
#       priority rule applicable in the situation of the premise; a list of other rules supporting the SAME 
#       conclusion, applicable in the situation of the premise, NOT defeated by any opponents, in descending 
#       priority order; maximum priority rule that would support the counterfactual conclusion if the 
#         counterfactual differences were true; other rules supporting the counterfactual conclusion if the 
#         counterfactual differences were true
# If the counterfactual conclusion is the same as the conclusion the theory actually produces, then msr=cmr,
#   osr=csr, and diff=[]
diff, msr, osr, cmr, csr = testing.getAndCounterfactuallyExplainConclusion(premise,pref2Theory[''], 'box')
#
# What if we actually changed the premise as indicated, would the counterfactual conclusion hold?
counterfactualPremise = testing.modifyPremise(premise, diff)
maxSupportingRule, otherSupportingRules = testing.getAndExplainConclusion(counterfactualPremise, pref2Theory[''])
print(testing.printRule(maxSupportingRule))
_ = [print(testing.printRule(x)) for x in otherSupportingRules]



# Example: how to update the theory by replacing an existing rule
#     input arguments: rule to replace; theory to work in; new rule
#     output: a list of rules of higher priority than the replaced rule to "ask the human about"
# The ask about rules are produced with this heuristic: if a rule has an antecedent that is a superset of
#   either the antecedent of the old rule or the new rule, then it is a rule to ask about.
#
# Let's first identify a rule producing a bad output:
failedTypeGuesses = getFailedRecords(testRecords, '')
#     asking about failure 1 because failure 0 produces nothing to ask about :P
conc, prem = testing.makeTestcase(failedTypeGuesses[1], '')
rule, _ = testing.getAndExplainConclusion(prem, pref2Theory[''])
newRule = (rule[0], conc)
askAbout = testing.updateTheory(rule, pref2Theory[''], newRule)
print("Replace\n\t(%s)\nwith\n\t(%s)\nask about:" % (testing.printRule(rule), testing.printRule(newRule)))
for e in askAbout:
    print("\t(%s)\n" % testing.printRule(e))

