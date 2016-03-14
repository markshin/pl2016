# Programming Languages, SNU 4190.310, 2016 Spring

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
- TA: [Jeehoon Kang](http://sf.snu.ac.kr/jeehoon.kang)
    + Email address: [pl2016@sf.snu.ac.kr](mailto:pl2016@sf.snu.ac.kr).
        * Send emails for administrative matters only. Use the [GitHub repository issue tracker](https://github.com/snu-sf-class/pl2016/issues).
        * *DO NOT* send emails to `jee...@sf.snu.ac.kr`.
        * In the case of sending TA an email, specify sender's name and student ID.
    + Place: Bldg 301 Rm 554-1
    + Office Hour: Please email me to make an appointment.

## Announcements

- There will be a lab session on 2016/03/08 (Tue).

## Assignments

| Due        	| Description                   	 	 	 	 	 	 	 	 	 	 	 	 	 	| Notes 	|
|------------	|-----------------------------------------------------------------------------------	|-------	|
| 20160320 23:59| [Assignment 01](https://github.com/snu-sf-class/pl2016/tree/master/assignments/01)    | 70		|
| NO			| [Assignment 00](https://github.com/snu-sf-class/pl2016/tree/master/assignments/00)    | No scores	|

## Must Read

- *READ VERY CAREFULLY* this section.

### Grading

- Assignments: 45%
    + Coq problems in the [software foundations material](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html). Read carefully the next subsections.
- Exams: 50% (mid-term 20% and final 30%)
    + You will solve Coq problems at the lab during the exam.
- Attendance: 5%
    + -1% per absence.  *IMPORTANT: 6 absences make an F*.

### Questions

- Ask questions in the [GitHub repository issue tracker](https://github.com/snu-sf-class/pl2016/issues).
- Send email for *PERSONAL MATTERS ONLY*.
- If you want to post a piece of source code, please DO NOT upload an image of it. Because it is hard to reconstruct texts from images.
    + Instead, use GitHub Markdown's ["fenced code blocks" feature](https://help.github.com/articles/github-flavored-markdown/#fenced-code-blocks).
    + Or, you can always use [GitHub Gist](https://gist.github.com/).

### Coq

- Use Coq [8.4pl5](https://coq.inria.fr/coq-84).  *DO NOT* use Coq 8.5!
    + If not, your submissions (assignments & exams) will not be properly graded.

- Install Coq.
    + Linux
        * Install [opam](http://opam.ocaml.org/doc/Install.html), and make sure you can use OCaml 4.02.3.
        * Install `libgtk2` by `sudo apt-get install libgtk2.0-dev` or `sudo yum install gtk2-devel`.
        * Install lablgtk2 by `opam install lablgtk`
        * Download [tarball](https://coq.inria.fr/distrib/V8.4pl5/files/coq-8.4pl5.tar.gz) file.
        * Extract the tarball, `./configure -coqide opt`, `make`, and then `make install`.
        * Test by `coqc -v` in the command line. Check your `PATH` variable if you get an error.
        * Run CoqIDE by `coqide`.
    + For Windows / OS X
        * Install [Coq for Windows](https://coq.inria.fr/distrib/V8.4pl5/files/coq-installer-8.4pl5.exe)
        * Install [Coq for OS X](https://coq.inria.fr/distrib/V8.4pl5/files/coqide-8.4pl5.dmg)

- Use IDEs supporting Coq.
    + CoqIDE: Download those bundled with CoqIDE in the [Download page](https://coq.inria.fr/coq-84).
        * In OS X, at first run, you may see an error message saying "Failed to load coqtop." Then click "No", and then find `/Applications/CoqIDE_8.4pl5.app/Contents/Resources/bin/coqtop` and open for once. Then goto `CoqIDE` > `Preferences` > `Externals`. And then change `coqtop` into `/Applications/CoqIDE_8.4pl5.app/Contents/Resources/bin/coqtop`.
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.

### Textbook: Software Foundations

- The textbook is in this repository's `sf/` directory.
- *DO NOT DOWNLOAD* the textbook from [The official Software Foundation website](https://www.cis.upenn.edu/~bcpierce/sf/current/index.html) in order to keep in sync.

### Assignment

#### Honor Code: *DO NOT CHEAT*

- If you copy others' source code, you will get F.
- "Others' source code" includes other students' and resources around the web. Especially, do not consult with public repositories on software foundations.
- Note that we have a good automatic clone detector. I found out that a lot of students cheated last time. I hope we all be happy at the end of the semester..

#### Submission

- `assignments/$NAME` directory is the assignment `$NAME`.
    + You submit `P??.v` files.  You should edit only `P??.v`. *DO NOT TOUCH ANYTHING ELSE*.
    + `E??.v` files are for evaluation.
    + Everything else are for relevant the definitions for the assignment.
- Edit `P??.v` files to do the assignment.
- `make` to compile your submission.  `make eval` to grade your submission yourself. 
- Both `make` and `make eval` *SHOULD SUCCEED*. If not, your score will be 0.
- `make eval` will check your submission.
    + `P??.v` files *SHOULD NOT* contain `admit`, `Admitted`, and anything in `forbidden.txt`.
    + If a `P??.v` file contains string `GIVEUP`, then it will be scored 0.
- `make submission` to prepare your submission.
    + `zip` should be installed. Otherwise, you can just zip `P??.v`.
- Submit at: http://147.46.15.109:9480/
    + *DO NOT ATTACK*. Please.
    + *DO NOT USE A STRONG PASSWORD*. It is `http`.
    + If your submission status is `SYSTEM ERROR` or `RUNNING` for a long time, please ask the TA.

### Misc.

- I strongly recommend you to use [Git](http://git-scm.com/) for the course. Register at [GitHub](https://github.com). [Try Git](https://try.github.io/levels/1/challenges/1).
