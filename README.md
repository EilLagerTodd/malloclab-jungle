#####################################################################

# CS:APP Malloc Lab

# Handout files for students

# Copyright (c) 2002, R. Bryant and D. O'Hallaron, All rights reserved.

# May not be used, modified, or copied without permission.

######################################################################

---

Main Files:

---

mm.{c,h}
Your solution malloc package. mm.c is the file that you
will be handing in, and is the only file you should modify.

mdriver.c
The malloc driver that tests your mm.c file

short{1,2}-bal.rep
Two tiny tracefiles to help you get started.

Makefile
Builds the driver

---

Other support files for the driver

---

config.h Configures the malloc lab driver
fsecs.{c,h} Wrapper function for the different timer packages
clock.{c,h} Routines for accessing the Pentium and Alpha cycle counters
fcyc.{c,h} Timer functions based on cycle counters
ftimer.{c,h} Timer functions based on interval timers and gettimeofday()
memlib.{c,h} Models the heap and sbrk function

---

Building and running the driver

---

To build the driver, type "make" to the shell.

To run the driver on a tiny test trace:

    unix> mdriver -V -f short1-bal.rep

The -V option prints out helpful tracing and summary information.

To get a list of the driver flags:

<<<<<<< HEAD
unix> mdriver -h

---

# 번역

mm.{c,h} :

    당신이 제출해야하는 파일로 수정해야하 하는 유일한 파일입니다.

mdriver.c :

    mm.c 파일을 테스트하는 malloc 드라이버

short{1,2}-bal.rep :

    시작하는데 도움이 되는 두개의 추적파일입니다.

Makefile :

    드라이버를 빌드합니다

---

기타 드라이버 지원 파일

---

config.h :

    malloc lab driver 를 구성합니다.

fsecs.{c,h} :

    다른 타이머 패키지에 대한 래퍼 함수

> 래퍼함수(Wraaper) : 기존함수를 한 번감싸서 원래 동작에 약간의 처리를 추가하는 함수. 말 그대로 뭔가를 감싸는 함수

clock.{c,h} :

    펜티엄 및 알파 사이클 카운터에 액세스하는 루틴

fcyc.{c,h} :

    주기 카운터에 기반한 타이머 함수

ftimer.{c,h} :

    간격 타이머 및 get time of day()를 기반으로 하는 타이머 함수

memlib.{c,h} :

    heap 및 sbrk 함수를 모델링합니다.

---

드라이버 구축 및 실행

---

드라이버를 빌드하려면 셸에 "make"를 입력합니다.

작은 테스트 추적에서 드라이버를 실행하려면(To run the driver on a tiny test trace):

    unix> mdriver -V -f short1-bal.rep

-V 옵션은 유용한 추적 및 요약 정보를 출력합니다.

드라이버 플래그 목록을 가져오려면(To get a list of the driver flags):

    unix> mdriver -h

---

진행방법

    1. make 후 ./mdriver 를 실행하면 out of memory 에러 발생
    2. 책에 있는 implicit list 방식대로 malloc을 구현해서 해당 에러를 없애기
    3. 이후 (시간이 된다면) explicit list와 seglist 등을 활용해 점수를 높이기

    Tip: ./mdriver -f traces/binary2-bal.rep 와 같이 특정 세트로만 채점 할 수 있다.
