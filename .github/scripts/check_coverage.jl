# SPDX-License-Identifier: MPL-2.0
# Reject empty/unrelated reports before any external upload.
function check_coverage(report;require_extension=false)
    files=String[];executed=0;measured=0;extension_executed=0;current=""
    for line in eachline(report)
        if startswith(line,"SF:")
            path=replace(chopprefix(line,"SF:"),'\\'=>'/')
            (startswith(path,"src/") || startswith(path,"ext/")) && isfile(path) ||
                error("coverage path is not package source: $path")
            push!(files,path)
            current=path
        elseif startswith(line,"DA:")
            fields=split(chopprefix(line,"DA:"),',')
            hits=parse(Int,fields[2]);measured+=1;executed+=hits>0
            startswith(current,"ext/") && hits>0 && (extension_executed+=1)
        end
    end
    isempty(files) && error("report contains no package source")
    executed>0 || error("report contains no executed package source lines")
    require_extension && extension_executed==0 && error("optional report contains no executed extension lines")
    println("Package source coverage: $executed / $measured measured lines in $(length(files)) files")
end
length(ARGS) in (1,2) && (length(ARGS)==1 || ARGS[2]=="--require-extension") ||
    error("usage: check_coverage.jl REPORT [--require-extension]")
check_coverage(ARGS[1];require_extension=length(ARGS)==2)
