#!/bin/bash


[[ $_ != $0 ]] && export ss=0 || ss=1
[[ ss -eq 0 ]] && echo "Script is being sourced" || echo "Script is a subshell"

export me="${BASH_SOURCE[${#BASH_SOURCE[@]} - 1]}"
export me=`basename $BASH_SOURCE`
echo call="$me $1 $2"
export exitcode=4
      


exitPrompt(){
    read -p "Do you wish to continue? [y]es or [n]o: " ans
    if [ $ans == 'n' ]
    then
        echo "Exiting the script. Have a nice day!"
        break
    else
        continue
    fi
}

declare -a listOfNames=( "*01*.p*"
                        #   "*02*.p*" "*03*.p*" "*04*.p*" "*05*.p*" "*6*.p*" "*7*.p*" "*8*.p*" "*9*.p*" "*10*.p*" 
                         "*11*.p*"
                         )
                                                                                                                 
#// For test_prolog  (no args)
if [ $# -eq 0 ]; then  
   for ele in ${listOfNames[@]}
   do 
      ./$0 $ele ; export exitcode=$? 
      if [ $exitcode -ne 4 ]
      then 
         exit $exitcode
      fi
      continue
   done
   exit $exitcode
#// For test_prolog attvar_01.pl attvar_04.pl   attvar_08.pfc  attvar_12.pfc
elif [ $# -ne 1 ]; then  
   for ele in $*
      do 
         ./$0 $ele ; export exitcode=$? 
         if [ $exitcode -ne 4 ]
         then 
            exit $exitcode
         fi
         continue
      done
      exit $exitcode
#// For test_prolog 'fc_01*'
elif [[ $1 == *"*"* ]] ; then 
   listOfNames=`find . -name '$1' `
   for ele in ${listOfNames[@]}
   do 
      ./$0 $ele ; export exitcode=$? 
      if [ $exitcode -ne 4 ]
      then 
         exit $exitcode
      fi
      continue
   done
   exit $exitcode
#// For test_prolog fc_08.pfc
elif [ -f $1 ] ; then 
   echo swipl -f /dev/null -g 'set_prolog_flag(runtime_testing,4)' -g "['$1']" -g 'halt(4)'
    eval "swipl -f /dev/null -g 'set_prolog_flag(runtime_testing,4)' -g \"['$1']\" -g 'halt(4)'"
   echo exitcode=$?
   exit $exitcode
#// For test_prolog fc_08.pfc
else
   echo swipl -f /dev/null -g 'set_prolog_flag(runtime_testing,4)' -g "['$1']" -g 'halt(4)'
    eval "swipl -f /dev/null -g 'set_prolog_flag(runtime_testing,4)' -g \"['$1']\" -g 'halt(4)'"
   echo exitcode=$?
   exit $exitcode
fi
