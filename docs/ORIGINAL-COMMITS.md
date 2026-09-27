# Original Commits Mapping

Old-repository commit SHAs (from `georgeee/mini-consensus-lean`) cited anywhere in this repository or in historical review/rollout records can be looked up in the table below or via `git log --grep <sha>` using the `Original-commit:` trailer.

| Original Short SHA | Original Full SHA | New Full SHA | Subject |
| :--- | :--- | :--- | :--- |
| `3a22bf1` | `3a22bf11bc3fce950a2dab24aa86c886df0854dc` | `d2e5d396fc378de4a5e25d8d9272875ab2e5a219` | memory: three-way audit round record (the truths not to regress) |
| `e21376d` | `e21376d39025a8e0f134430bad0ad7661050133c` | `a1c78fa95cf16af7bd52e6f300bc5c876e83a748` | paper2 p1: abstract + intro (AN/1, AN/2, AN/3, AN/4) |
| `7d8890c` | `7d8890c908f48ebda02b118ec2b6526f2279cf26` | `e62194127b14e7383f5e7ec7c09f3f4f986901eb` | paper2 p2: intro engineering claim + modes 1-2 (AN/5, AN/6, AN/7, AN/8) |
| `3ee3deb` | `3ee3debe337025ea8e48b25388629527c208c8c3` | `baac9d8fb0d33cf719bcc35645b78e2644a03716` | paper2 p4: chain validity + what a node holds (AN/10, AN/11) |
| `07e95f4` | `07e95f4f58d6611db6f309e27287fac1f8c27ef5` | `9c7133f5937d41fe6c9412e1eee8bf1d2013ea04` | paper2 p6: Assumptions 2 and 3 (AN/12, AN/13) |
| `3077827` | `3077827f20a7f698808b84c8e64e44e24823109e` | `249312342c622b6e1fec6fdc463f9676a8735825` | paper2 p7: results order, Thm 1 caveat, timed model (AN/14, AN/15, AN/16) |
| `fcd6452` | `fcd6452ae4c87254d5ec6271ce19b7c6a64f7610` | `ed1ee89e23a0a2a5a56e55c821a7173bcbb94008` | paper2 p9: state the 5n budget before deriving it (AN/18, AN/19) |
| `e527ee5` | `e527ee5a77114bccdafbeaa37ff44b8eca7cfd47` | `276d602ff7ef61378a9e74664a63310b161e95d6` | paper2 p10: gloss the floor, say what theft times buy (AN/22, AN/24) |
| `4d950bb` | `4d950bbfbad6e913e40b7cd1fb5ad35c339f234b` | `367e43aab4b5dbdc86fbfb76032bea9c02f771cb` | paper2 p11: drop the redundant length clause (AN/25) |
| `60bd4bd` | `60bd4bd2e41f0f62613fabc6e3a25cc96fea4255` | `a675c35340842a5a28199293447182584b62969e` | paper2 p13: trim the prover-cost aside (AN/32) |
| `8b8b766` | `8b8b766b51b52be1c066625652d011dcc486e004` | `a9bad188cf5f62979f8135ef83817a9af1d00960` | paper2 p16: appendix -- recency window, no-back-dating scope (AN/33, AN/34) |
| `557f52b` | `557f52b9a2bf2d781f784820b2cf6be85f8c9008` | `059e2c0c612a5753d1bc90cbc2d0b0e36dcf318d` | rollout: preserve the planning record (maps, three designs, salvage) |
| `64fbf03` | `64fbf0398427022780c5e3fcc5b01e038ddb6d42` | `71f92f7b5a22c0f20e6187b430bb06c9e246f8ac` | rollout: salvage the last two interrupted runs; answers + provisional ordering |
| `b6b9f09` | `b6b9f097369cf835b9ec16dd463eae7c1f445f19` | `cc29d6bbb2a5d42c610307288883b081c2948d3d` | rollout: close the completeness audit |
| `3314664` | `33146646bffe7a4820cbd72eed4259d1eb8276fb` | `33d3711813b74ab763ab71a7ed2798866961d8a7` | rollout notes: log the plan-completion phase kickoff |
| `0de355b` | `0de355b459070a5841ef5d2a8157db30b543297f` | `843fa5cdaed31b73a45c0d9d4210082abce82fdf` | rollout: finalize ROLLOUT_PLAN.md from the completed design+review pass |
| `b832419` | `b83241971af8004aa6774316f8017d72ae748f5f` | `181df53e6c99decb963c3daa6b6b46198b063753` | rollout: add the recovered sequencer output as supplementary record |
| `9332430` | `93324309726a2f12bd33c941c3747aa80a3d91a5` | `8286b6b91847ac39ef8fc50277da75837cd5920b` | rollout: land the design+verdict artifacts backing ROLLOUT_PLAN.md |
| `9eaadcd` | `9eaadcd0b8a7b4f4cd95d14f1a5254db1368d3a8` | `8cbb971d31da344e01c6a15d1ca4496a8b401046` | W6: no-back-dating obstruction witnesses, landed and axiom-clean |
| `7017446` | `7017446f3e07a0d9a3a016a88a8fbee40cc3ea44` | `868bdab3e9542cc4b09f4e7165bc26d91b106b0d` | W4: induction over syncs, landed and axiom-clean |
| `71a5fa3` | `71a5fa3fe6bb9e0c3e49065974d84b008feb27d3` | `7cecb69392cc0d7bc0308550c1e1322c3f6b5836` | W3a: timed theft layer for mode 1, landed and axiom-clean |
| `fc3d08b` | `fc3d08bf5cde480d0fa7c9592b6687952d85f6b6` | `cc8db25726abe916afc6dd10f1c543ff1ee4cc0a` | W2: mode 1 anchored/trailing-5n client rule at the certificate level |
| `d59d244` | `d59d244153ba3b74a62af1288adfab7ddf107401` | `ba87cf3bf525ed6ebed2af9f6aeec3489a8e4831` | W1: mode 3 (free-cadence lockstep) at the certificate level |
| `8df8b0c` | `8df8b0cb77ab39cc71701330c6636f8069d3e7c9` | `2ba6f97326c4ee9e3293a044acbcedbcf7cc8914` | W5: mode 3 per-generation census (D1-prime-full), confirmation depth 2n |
| `726d320` | `726d320d0be27407fc0090075d60852796b7cda7` | `e3eeb0de327e277b5edade1f41ca496a72196dda` | W3b: time-aware signature surface, tightened census, larger F_max (stretch) |
| `5413d0d` | `5413d0da6e3229855ac88ec1d82dfeab3ffe5855` | `a821321bb4cd6df31acdab276a0fe3794a22770e` | Close out the rollout plan: all seven scoped work items landed |
| `14d2d11` | `14d2d1167f437d5f88c19b0e9172dad3238b14c2` | `adc095932dffc33669a4a554b9281f6401ea835d` | Review pass: fix a vacuous separation theorem, prove what replaces it |
| `29527a9` | `29527a917a77f02e1635ddb769c73565cf3e685e` | `23006bfd2993291eddac68b5c081d0aeebf55e3a` | Second review round: paper edits vs Lean, sharp-depth lemma, wording proposal |
| `a8b0ab3` | `a8b0ab3810f8ca652b67847f58c43c0bafc933da` | `3c17751c91e0b01f16b111547f287179cb0c5077` | Annotation review report (HTML), adversarially reviewed |
| `9271ba5` | `9271ba56e5496eb430f1ed325ce03a18ae69e135` | *(dropped — became empty after filtering)* | Add HANDOFF.md for session continuity |
| `31535ec` | `31535ec74f08a934588e6d466932eda67fda4253` | `082a5c38cb562de2fedf080ae251f3f26df40447` | Add the Yak header to the paper |

