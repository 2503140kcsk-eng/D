# Hakui Koyori Number — concept grounding

Audit date: 2026-11-03.

This is an independent fan-inspired mathematics project, not an official Hololive or Cover Corp project.

## Official character and channel facts

The official Hololive talent profile describes Hakui Koyori as the researcher of Secret Society holoX, research-minded and curious, interested in observing human behavior, and self-described as holoX's brains. The profile also links her official YouTube channel and uses the stream tag #こより実験中 and the 🧪 fan mark.

- Official profile: https://hololive.hololivepro.com/talents/hakui-koyori
- Official YouTube channel: https://www.youtube.com/channel/UC6eWCld0KwmyHFbAqK3V-Rw

The channel's public identity calls her “holoX's brain” and shows original releases that include:

- RISING 酸 / RISING Acid (official video: https://www.youtube.com/watch?v=WOZTqdQ6bnE; listed on the channel in October 2026).
- 爆ラブ＋ケミストリー (official video: https://www.youtube.com/watch?v=65R4ZpEuzvM).
- 管制塔より (official video: https://www.youtube.com/watch?v=-4ZiokRXZ6g).
- NaN GAME (official video: https://www.youtube.com/watch?v=W3Gl0bSvwTU).

Cover Corp's 2026-09-12 announcement describes the upcoming 2nd album Chemical Spark as based on her “理系女子（リケジョ）” concept. As of the audit date 2026-11-03, the album's announced release date, 2026-12-02, and her 1st solo live's announced date, 2026-12-22, are future dates.

- Official album/live announcement: https://hololive.hololivepro.com/news/20260912-02-83/
- 1st live site: https://dream-spark.hololivepro.com/

## Mathematical interpretation used by the project

The mathematical construction does not claim that the performer or her songs imply any theorem. It uses public character motifs only as a design metaphor.

| Public motif | Mathematical design choice |
|---|---|
| Researcher / experimental work | A sequence of finite, explicitly indexed mathematical experiments |
| #こより実験中 | Each input n represents one finite experiment stage |
| Research notebook / accumulated findings | \(M_f(n)=\max_{0\le j\le n}f(j)\), retaining the best value observed in the finite history |
| Chemical Spark / science-girl concept | The Koyori Spark transformation \(S_f(n)=2^{M_f(n)+n+3}\), a precisely defined exponential amplification |
| Repeated challenge and iterative activity | Ten applications of \(S_f\), matching the tenfold iteration shape in the LNGN comparator |
| Spark cascade | A second finite exponentiation tower based on the result of the ten experiments |

The running maximum is not decorative: it makes \(S_f\) monotone even when the source function \(f\) is arbitrary. That technical property is what allows the strict comparison proof to work without assuming f is monotone.

The mathematical name “Koyori Spark transformation” is original to this project. It is a metaphor for repeatable, cumulative, amplified experiments, not a claim about official lore or an official Hololive mathematical concept.
