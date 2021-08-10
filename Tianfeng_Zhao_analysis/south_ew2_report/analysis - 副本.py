'''
Result Analysis
Written by Can Zhou
'''

# init
fileName1 = "south_ew2_result.txt"
fileName2 = "south_output.txt"
reportFileName = "analysis_report_south_t-2.txt"

# find nogoods in each file
def findNogoods(fileName):
    myFile = open(fileName,"r+").readlines()
    searchString1 = "nogoods = [["
    searchString2 = "]]]"
    fileList = []
    for i in range(len(myFile)):
        if searchString1 in myFile[i]:
            tmp = myFile[i].split(']] [[')
            for t in tmp:
                tmp2 = t.split('] [')
                nogood = []
                for t2 in tmp2:
                    tmp3 = t2.split(' ')
                    lenght = len(tmp3)
                    tmp3_0 = tmp3[lenght-2]
                    tmp3_1 = tmp3[lenght-1]
                    if searchString2 in tmp3_1:
                        tmp3_1 = tmp3_1.split(']]]')[0]
                    nogood.append(tmp3_0)
                    nogood.append(tmp3_1)
                fileList.append(tuple(nogood))
    return fileList



def findNogoods1(fileName):
    myFile = open(fileName,"r+").readlines()
    searchString1 = "[["
    searchString2 = "]]]"
    fileList = []
    for i in range(len(myFile)):
        if searchString1 in myFile[i]:
            tmp = myFile[i].split(']] [[')
            for t in tmp:
                tmp2 = t.split('] [')
                nogood = []
                for t2 in tmp2:
                    tmp3 = t2.split(' ')
                    lenght = len(tmp3)
                    tmp3_0 = tmp3[lenght-2]
                    tmp3_1 = tmp3[lenght-1]
                    if searchString2 in tmp3_1:
                        tmp3_1 = tmp3_1.split(']]]')[0]
                    nogood.append(tmp3_0)
                    nogood.append(tmp3_1)
                fileList.append(tuple(nogood))
    return fileList



file1List = findNogoods(fileName1)
file2List = findNogoods1(fileName2)

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