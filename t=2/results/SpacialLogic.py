import os
from subprocess import Popen

path = ""
# os.makedirs(path, exist_ok=True)

# ################################################################################################################
# get and save all the results
# Popen(['pop11', 'new_LD_reasoner_south_ew.p'], stdout = open(path+'/south_ew.txt', 'w'))
# Popen(['pop11', 'new_LD_reasoner_south_ns.p'], stdout = open(path+'/south_ns.txt', 'w'))
# Popen(['pop11', 'new_LD_reasoner_nott_ew.p'], stdout = open(path+'/nott_ew.txt', 'w'))
# Popen(['pop11', 'new_LD_reasoner_nott_ns.p'], stdout = open(path+'/nott_ns.txt', 'w'))

##################################################################################################################
# analysis and get clean file
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

def cleanPrint(fileList):
    result = ""
    for tmp in fileList:
        result += tmp[0] + "," + tmp[1] + "," + tmp[2] + "," + tmp[3] + "\n"
    return result

def orderedList(myList):
    orderedList = []
    for item in myList:
        tmp = []
        tmp.clear()
        if "os" in item[0]:
            tmp.append(item[0])
            tmp.append(item[1])
        else:
            tmp.append(item[1])
            tmp.append(item[0])
        if "os" in item[2]:
            tmp.append(item[2])
            tmp.append(item[3])
        else:
            tmp.append(item[3])
            tmp.append(item[2])
        orderedList.append(tmp)
    return orderedList

def analysisClean(fileName1, fileName2, reportFileName, reportFileNameClean):
    file1List = findNogoods(fileName1)
    file2List = findNogoods(fileName2)

    # ordered
    file1ListOrdered = orderedList(file1List)
    file2ListOrdered = orderedList(file2List)

    # analysis
    unique = []
    for nogood in file1ListOrdered:
        tmp1 = [nogood[0], nogood[1], nogood[2], nogood[3]]
        tmp2 = [nogood[2], nogood[3], nogood[0], nogood[1]]

        if (tmp1 not in unique) and (tmp2 not in unique):
            unique.append(nogood)
    
    for nogood in file2ListOrdered:
        tmp1 = [nogood[0], nogood[1], nogood[2], nogood[3]]
        tmp2 = [nogood[2], nogood[3], nogood[0], nogood[1]]

        if (tmp1 not in unique) and (tmp2 not in unique):
            unique.append(nogood)


    # write report
    reportFile = open(reportFileName, "w")
    report = "Summary:" + "\n" + str(fileName1) + " and " + str(fileName2) + ":" \
        + "\n\nAll nogoods:" + str(len(unique)) \
        + "\n\n---------------------------------------" \
        + "\nDetails:"

    report += prettyPrint(unique)

    reportFile.write(report)
    reportFile.close()

    results = unique
    reportFile = open(reportFileNameClean, "w")
    reportFile.write(cleanPrint(results))
    reportFile.close()


fileName1 = path + "results_south_ns.txt"
fileName2 = path + "results_south_ew.txt"
reportFileName = path + "analysis_report_south_t-3.txt"
reportFileNameClean = path + "south_LD.txt"
analysisClean(fileName1, fileName2, reportFileName, reportFileNameClean)

fileName1 = path + "results_nott_ns.txt"
fileName2 = path + "results_nott_ew.txt"
reportFileName = path + "analysis_report_nott_t-3.txt"
reportFileNameClean = path + "nott_LD.txt"
analysisClean(fileName1, fileName2, reportFileName, reportFileNameClean)