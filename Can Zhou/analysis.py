'''
Result Analysis
Written by Can Zhou
'''

# init
fileName1 = "south_LBPT.txt"
fileName2 = "south_LD.txt"
reportFileName = "south.txt"

# find objects
def findObjects(fileName):
    myFile = open(fileName,"r+").readlines()
    result = []
    for line in myFile:
        nogood = line.split(",")
        tmp = nogood[3].split("\n")[0]
        nogood[3] = tmp
        result.append(tuple(nogood))
    return result

file1List = findObjects(fileName1)
file2List = findObjects(fileName2)

# analysis
duplicate = []
file1Unique = []
file2Unique = file2List.copy()
for nogood in file1List:
    if nogood in file2List:
        duplicate.append(nogood)
        file2Unique.remove(nogood)
    else:
        file1Unique.append(nogood)

# write report
reportFile = open(reportFileName, "w")
report = "Summary:" + "\n" + str(fileName1) + ":" \
    + "\nTotoal nogoods: " + str(len(file1List)) + "; unique nogoods: " + str(len(file1Unique)) + "; duplicate nogoods: " + str(len(duplicate)) \
    + "\n" + str(fileName2) + ":" \
    + "\nTotoal nogoods: " + str(len(file2List)) + "; unique nogoods: " + str(len(file2Unique)) + "; duplicate nogoods: " + str(len(duplicate)) \
    + "\n\n---------------------------------------" \
    + "\nDetails:"

def prettyPrint(fileList):
    result = ""
    for i in range(len(fileList)):
        tmp = fileList[i]
        result += "[(" + str(tmp[0]) + ", " + str(tmp[1]) + ") (" + str(tmp[2]) + ", " + str(tmp[3]) + ")]  "
        if (i+1)%2 == 0:
            result += "\n"
    return result

def fileReport(fileName, fileList, fileUnique):
    filetmp = "\n\n" + fileName + ":\n"
    filetmp += "\nTotal nogoods:\n" + prettyPrint(fileList)
    filetmp += "\nUnique nogoods:\n" + prettyPrint(fileUnique)
    return filetmp

report += fileReport(fileName1, file1List, file1Unique)
report += fileReport(fileName2, file2List, file2Unique)
report += "\n\nDuplicate:\n\n" + prettyPrint(duplicate)
    
reportFile.write(report)
reportFile.close()