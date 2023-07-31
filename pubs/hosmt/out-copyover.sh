#!/bin/bash

scp index.html uiowa2:/homepage/hbarbosa/papers/hosmt/
scp style.css uiowa2:/homepage/hbarbosa/papers/hosmt/
scp ../conf.pdf uiowa2:/homepage/hbarbosa/papers/hosmt/hosmt_paper.pdf
scp ../rep.pdf uiowa2:/homepage/hbarbosa/papers/hosmt/hosmt_report.pdf
ssh uiowa2 "chmod 755 -R /homepage/hbarbosa/papers/hosmt"
