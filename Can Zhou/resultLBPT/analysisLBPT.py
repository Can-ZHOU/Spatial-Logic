'''
Result Analysis -- LBPT
Written by Can Zhou
'''

# init
fileName = "south_output.txt"
reportFileName = "analysisLBPT_report_south_t-2.txt"
reportFileNameClean = "south_LBPT.txt"
myFile = open(fileName,"r+").readlines()

# find objects
results = []
for line in myFile:
    if "[[" in line:
        splited = line.split(" ")
        nogood = []
        length = len(splited)
        nogood.append(splited[length-5])
        nogood.append(splited[length-4].split("]")[0])
        nogood.append(splited[length-2])
        nogood.append(splited[length-1].split("]")[0])
        results.append(nogood)

# write report
def prettyPrint(fileList):
    result = ""
    for i in range(len(fileList)):
        tmp = fileList[i]
        result += "[(" + str(tmp[0]) + ", " + str(tmp[1]) + ") (" + str(tmp[2]) + ", " + str(tmp[3]) + ")]  "
        if (i+1)%2 == 0:
            result += "\n"
    return result

def cleanPrint(fileList):
    result = ""
    for tmp in fileList:
        result += tmp[0] + "," + tmp[1] + "," + tmp[2] + "," + tmp[3] + "\n"
    return result

report = "All nogoods: " + str(len(results)) +"\n" + prettyPrint(results)
reportFile = open(reportFileName, "w")
reportFile.write(report)
reportFile.close()
reportFile = open(reportFileNameClean, "w")
reportFile.write(cleanPrint(results))
reportFile.close()