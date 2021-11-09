import os

allFiles = os.listdir("./Data")

for fileName in allFiles:
    tmpPath = "./Data/"+fileName
    tmpWrite = "./CleanedData/"+fileName
    myFile = open(tmpPath,"r+").readlines()
    condition = "BPT"
    tmpFile = ""
    for line in myFile:
        if condition not in line:
            tmpFile += line
    reportFile = open(tmpWrite, "w")
    reportFile.write(tmpFile)
    reportFile.close()