# docker build --tag dafny .
# docker run -v ~/local/dir:/home/local -it dafny
#
# Based on https://hub.docker.com/r/ssaavedra/dafny/dockerfile
FROM alpine AS unzipper
LABEL maintainer="rui@computer.org"

WORKDIR /opt

RUN apk add -U curl unzip
RUN curl -L https://github.com/Microsoft/dafny/releases/download/v2.2.0/dafny-2.2.0.10923-x64-ubuntu-14.04.zip -o /opt/dafny.zip \
&& (cd /opt && unzip dafny.zip && rm dafny.zip)

FROM mono:5

RUN apt update && apt install -qy libgomp1 zip unzip && rm -rf /var/lib/apt/lists/*

COPY --from=0 /opt/dafny /opt/dafny

ENV PATH /usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/opt/dafny:/opt/dafny/z3/bin
