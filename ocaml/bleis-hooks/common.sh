#! /bin/sh

getGitBranchName()
{
    branch="$(git symbolic-ref HEAD 2>/dev/null)" ||
            "$(git describe --contains --all HEAD)"
    echo ${branch##refs/heads/}
}

isOnMasterBranch()
{
    if [ "$(getGitBranchName)" = "master" ]; then
        return 0
    fi
    return 1
}

appendMsgTo1stLine()
{
    mv $1 $1.$$
    if [ -s "$1.$$" ]; then
    if head -1 "$1.$$" | grep "$2" > /dev/null; then
        cp "$1.$$" "$1"
    else
            sed '1s/$/ '"$2"'/' "$1.$$" > $1
    fi
    else
        echo "$2" > "$1"
    fi
    rm -f $1.$$
}

extractTicketId()
{
    echo "$(getGitBranchName)" \
    | awk 'BEGIN{ FS="[/]"}
           $1 == "id" { printf "refs #%s", $2 }
           $2 == "id" { printf "refs #%s", $3 }'
}

hasTicketId()
{
    first="$(git cat-file -p $1 \
    | sed '1,/^$/d' | head -1 \
    | sed '/.*refs #[0-9][0-9]*.*/!d')"

    if [ -n "${first}" ]; then
        echo "true"
    else
        echo "false"
    fi
}

extractParents()
{
    parents="$(git cat-file -p $1 \
    | grep '^parent [0-9a-f]\{40\}$')"
    echo "${parents##parent }"
}

