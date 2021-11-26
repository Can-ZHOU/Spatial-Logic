import os

path = ""

def findNogoods(fileName):
    myFile = open(fileName,"r+").readlines()
    fileList = []
    for i in range(len(myFile)):
        tmp = myFile[i].split('\n')[0].split(',')
        nogood = []
        nogood.append([tmp[0], tmp[1]])
        nogood.append([tmp[2], tmp[3]])
        fileList.append(nogood)
    return fileList

def prettyPrint(fileList):
    result = ""
    for i in range(len(fileList)):
        tmp = fileList[i]
        result += "[(" + str(tmp[0][0]) + ", " + str(tmp[0][1]) + ") (" + str(tmp[1][0]) + ", " + str(tmp[1][1]) + ")]  "
        if (i+1)%2 == 0:
            result += "\n"
    return result

def analysisClean(fileName1, fileName2, reportFileName):
    file1List = findNogoods(fileName1)
    file2List = findNogoods(fileName2)

    # analysis
    unique_t2 = []
    unique_t3 = []
    for nogood in file1List:
        tmp1 = [nogood[0], nogood[1]]
        tmp2 = [nogood[1], nogood[0]]

        if (tmp1 not in file2List) and (tmp2 not in file2List):
            unique_t2.append(nogood)
    
    for nogood in file2List:
        tmp1 = [nogood[0], nogood[1]]
        tmp2 = [nogood[1], nogood[0]]

        if (tmp1 not in file1List) and (tmp2 not in file1List):
            unique_t3.append(nogood)


    # write report
    reportFile = open(reportFileName, "w")
    report = "Summary:" + "\n" + str(fileName1) + " and " + str(fileName2) + ":" \
        + "\n\n---------------------------------------" \
        + "\nDetails:\n"

    report += "\nUnique t=2:\n" + prettyPrint(unique_t2)
    report += "\nUnique t=3:\n" + prettyPrint(unique_t3)

    reportFile.write(report)
    reportFile.close()


fileName1 = path + "nott_LD_t2.txt"
fileName2 = path + "nott_LD_t3.txt"
reportFileName = path + "compare_nott.txt"
analysisClean(fileName1, fileName2, reportFileName)

fileName1 = path + "south_LD_t2.txt"
fileName2 = path + "south_LD_t3.txt"
reportFileName = path + "compare_south.txt"
analysisClean(fileName1, fileName2, reportFileName)