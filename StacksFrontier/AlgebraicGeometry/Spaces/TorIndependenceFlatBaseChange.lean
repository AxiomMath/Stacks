module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Tor independence after a flat base change of algebraic spaces

Let `S` be a scheme and let
```
Z' ⟶ Y'
↓     ↓
X' ⟶ B'
```
be a commutative square of algebraic spaces over `S` with `Y' ⟶ B'` and `Z' ⟶ X'` flat.  Write
`X` and `Y` for the base changes of `X'` and of `Y'` along a morphism `B ⟶ B'`.  Stacks 0CTQ
asserts that `X ×_B Y` and `Z'` are then Tor independent over `X' ×_{B'} Y'`.

The source proves this by checking Tor independence on étale charts, which is Stacks 08IQ, and
quoting the case of schemes, Stacks 0CTA.  The reduction is carried out in the source's own
footnote: choose a surjective étale chart `W' ⟶ B'`, then charts `U' ⟶ X' ×_{B'} W'` and
`V' ⟶ Y' ×_{B'} W'`, observe that `U' ×_{W'} V' ⟶ X' ×_{B'} Y'` is surjective étale, choose a
chart `T'` of `Z' ×_{X' ×_{B'} Y'} (U' ×_{W'} V')`, and apply the case of schemes to the square
with corners `T'`, `U'`, `V'`, `W'`.  The last sentence of the footnote is the observation that
flatness of `Y' ⟶ B'` and of `Z' ⟶ X'` gives flatness of `V' ⟶ W'` and of `T' ⟶ U'`.

That last step, together with the application of Stacks 0CTA to the chart square, is
`AlgebraicGeometry.Space.torIndependent_schemeCharts_of_isFlat`:
`AlgebraicGeometry.Space.IsFlat` of Stacks 03ML is by definition flatness of the morphism of
schemes underlying *every* commuting square of étale charts, so the flatness of the two chart
morphisms is read off from the two commuting chart squares.
`AlgebraicGeometry.Space.exists_etaleChart_square_flat` records that such chart squares exist
over any given étale chart of the target, which is how the source produces them.

Stacks 0CTQ itself, `AlgebraicGeometry.Space.torIndependent_baseChange_product_of_isFlat`, is
assembled from that and from Stacks 08IQ, condition (4) implies condition (1).  The whole chart
tower of the footnote is built in the proof.  The one point where some care is needed is that
condition (4) of Stacks 08IQ wants the three upper terms of the étale diagram to be *schemes*:
the conclusion of Stacks 0CTA is Tor independence of schemes in the sense of Stacks 08IA, a
condition on *ordinary* local rings, while Tor independence of algebraic spaces, Stacks 08IP, is
a condition on *étale* local rings, and the comparison of the two is available exactly for a
diagram of representable algebraic spaces.  The tower of the footnote is a tower of charts, so
its three upper terms are representable and
`AlgebraicGeometry.Space.torIndependent_of_torIndependent_scheme_diagram` applies to it
directly.

## Main results

* `AlgebraicGeometry.Space.exists_etaleChart_square_flat`: over any étale chart of the target of
  a flat morphism of algebraic spaces there is a commuting square of étale charts whose
  underlying morphism of schemes is flat.
* `AlgebraicGeometry.Space.torIndependent_schemeCharts_of_isFlat`: Stacks 0CTA applied to the
  chart square of the footnote of Stacks 0CTQ, with the flatness of the two chart morphisms
  deduced from flatness of the two morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.torIndependent_baseChange_product_of_isFlat`: Stacks 0CTQ.

## Implementation notes

The base change in `AlgebraicGeometry.Space.torIndependent_schemeCharts_of_isFlat` is along an
arbitrary morphism of schemes into the chart `W'`, as in Stacks 0CTA, rather than along the
morphism of schemes underlying a chart of `B ×_{B'} W'`; this is more general and shortens the
statement.  The two comparison morphisms into `U' ×_{W'} V'` are produced as an existential
characterised by their two composites with the projections, rather than written out as the
`CategoryTheory.Limits.pullback.lift` terms of Stacks 0CTA, so that the statement carries no
proof term; the proof identifies them with those terms by
`CategoryTheory.Limits.pullback.hom_ext`.

The square of algebraic spaces, the two base changes and the two fibre products appear in the
statement of `AlgebraicGeometry.Space.torIndependent_baseChange_product_of_isFlat` as arbitrary
cartesian squares rather than as the chosen presheaf pullbacks, and the two comparison
morphisms are given by their factorisations through the projections.  Both are how a fibre
product of algebraic spaces is presented elsewhere in this directory, and the proof uses
nothing else about them.

Two objects of the big fppf site are built by hand in the proof, the chart `U' ×_{W'} V'` of
`X' ×_{B'} Y'` and the chart of `(X ×_B Y) ×_{X' ×_{B'} Y'} (U' ×_{W'} V')`, each as the fibre
product of *schemes* carrying the structure morphism of the corresponding fibre product in the
site.  Taking the fibre product in the site instead would leave the morphism of schemes
underlying the chart equal to the comparison morphism of Stacks 0CTA only up to the canonical
isomorphism of Stacks 021U, and Stacks 0CTA concludes about the comparison morphism itself.

## References

* [Stacks Project, Tag 0CTQ](https://stacks.math.columbia.edu/tag/0CTQ)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-! ### Two cartesian squares of a fibre product of base changes -/

/-- The comparison morphism from the fibre product over `W` of two base changes along `X ⟶ B`
and `Y ⟶ B` to the fibre product of `X` and `Y` over `B` is a base change of `W ⟶ B`.

Both squares of the statement are given as arbitrary cartesian squares, and the comparison
morphism by its two factorisations through the projections of the target. -/
private lemma product_baseChange
    {C : Type u} [Category.{v} C]
    {X Y B W X₀ Y₀ P₀ P : C}
    {x : X ⟶ B} {y : Y ⟶ B} {w : W ⟶ B}
    {ux : X₀ ⟶ X} {uw : X₀ ⟶ W} {vy : Y₀ ⟶ Y} {vw : Y₀ ⟶ W}
    (hx : IsPullback ux uw x w) (hy : IsPullback vy vw y w)
    {p₁ : P₀ ⟶ X₀} {p₂ : P₀ ⟶ Y₀} (h₀ : IsPullback p₁ p₂ uw vw)
    {q₁ : P ⟶ X} {q₂ : P ⟶ Y} (h : IsPullback q₁ q₂ x y)
    {f : P₀ ⟶ P} (hf₁ : f ≫ q₁ = p₁ ≫ ux) (hf₂ : f ≫ q₂ = p₂ ≫ vy) :
    IsPullback f (p₁ ≫ uw) (q₁ ≫ x) w := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← Category.assoc, hf₁, Category.assoc, hx.w, Category.assoc]
  · intro T a b h₁ h₂
    apply h₀.hom_ext
    · apply hx.hom_ext
      · simpa only [Category.assoc, ← hf₁] using congrArg (fun k => k ≫ q₁) h₁
      · simpa only [Category.assoc] using h₂
    · apply hy.hom_ext
      · simpa only [Category.assoc, ← hf₂] using congrArg (fun k => k ≫ q₂) h₁
      · simpa only [Category.assoc, ← h₀.w] using h₂
  · intro T a b hab
    let l₁ := hx.lift (a ≫ q₁) b (by simpa only [Category.assoc] using hab)
    let l₂ := hy.lift (a ≫ q₂) b (by simpa only [Category.assoc, ← h.w] using hab)
    have hl : l₁ ≫ uw = l₂ ≫ vw := by simp [l₁, l₂]
    refine ⟨h₀.lift l₁ l₂ hl, ?_, ?_⟩
    · apply h.hom_ext <;> simp [Category.assoc, hf₁, hf₂, l₁, l₂]
    · simp [← Category.assoc, l₁]

/-- A morphism property stable under base change and composition holds for the morphism of
fibre products induced by a pair of morphisms with that property over a fixed base. -/
private lemma property_product_map
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {X Y X' Y' B A A' : C}
    {x : X ⟶ B} {y : Y ⟶ B} {x' : X' ⟶ B} {y' : Y' ⟶ B}
    {u : X ⟶ X'} {v : Y ⟶ Y'} (hu : P u) (hv : P v)
    (hx : x = u ≫ x') (hy : y = v ≫ y')
    {a : A ⟶ X} {b : A ⟶ Y} (h : IsPullback a b x y)
    {a' : A' ⟶ X'} {b' : A' ⟶ Y'} (h' : IsPullback a' b' x' y')
    {f : A ⟶ A'} (hf₁ : f ≫ a' = a ≫ u) (hf₂ : f ≫ b' = b ≫ v) : P f := by
  have he : f = h.isoPullback.hom ≫
      pullback.map x y x' y' u v (𝟙 B) (by simpa using hx) (by simpa using hy) ≫
      h'.isoPullback.inv := by
    apply h'.hom_ext <;>
      simp [Category.assoc, hf₁, hf₂, pullback.map, pullback.lift_fst, pullback.lift_snd]
  rw [he, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact P.pullbackMap hu hv hx hy

/-- A morphism property stable under base change and composition holds for the morphism
`U ×_W V ⟶ X ×_B Y` induced by charts `U ⟶ X ×_B W` and `V ⟶ Y ×_B W` with that property over
a morphism `W ⟶ B` with that property. -/
private lemma property_product_chart
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (R : MorphismProperty C) [R.IsStableUnderBaseChange] [R.IsStableUnderComposition]
    {X Y B W X₀ Y₀ U V A P : C}
    {x : X ⟶ B} {y : Y ⟶ B} {w : W ⟶ B}
    {ux : X₀ ⟶ X} {uw : X₀ ⟶ W} {vy : Y₀ ⟶ Y} {vw : Y₀ ⟶ W}
    (hx : IsPullback ux uw x w) (hy : IsPullback vy vw y w)
    {u : U ⟶ X₀} {v : V ⟶ Y₀} (hu : R u) (hv : R v) (hw : R w)
    {a : A ⟶ U} {b : A ⟶ V} (hA : IsPullback a b (u ≫ uw) (v ≫ vw))
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ x y)
    {f : A ⟶ P} (hf₁ : f ≫ p₁ = a ≫ u ≫ ux)
    (hf₂ : f ≫ p₂ = b ≫ v ≫ vy) : R f := by
  let m := pullback.lift (a ≫ u) (b ≫ v) (by simpa only [Category.assoc] using hA.w)
  let n := hP.lift (pullback.fst uw vw ≫ ux) (pullback.snd uw vw ≫ vy)
    (by rw [Category.assoc, Category.assoc, hx.w, hy.w,
      ← Category.assoc, ← Category.assoc, pullback.condition])
  have hm : R m := property_product_map R hu hv rfl rfl hA
    (IsPullback.of_hasPullback uw vw)
    (by simp [m, pullback.lift_fst]) (by simp [m, pullback.lift_snd])
  have hn : R n := R.of_isPullback
    (product_baseChange hx hy (IsPullback.of_hasPullback uw vw) hP
      (by simp [n]) (by simp [n])).flip hw
  have hf : f = m ≫ n := by
    apply hP.hom_ext <;>
      simp [Category.assoc, hf₁, hf₂, n, m, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [hf]
  exact R.comp_mem _ _ hm hn

/-- **The chart of a fibre product is a fibre product of charts.**  Let `P' = X ×_B Y`, let
`Qy = Y ×_B W`, let `Cc = U ×_W V` for morphisms `U ⟶ W` and `V ⟶ W` and let `ZU = Z ×_X U`
for a morphism `U ⟶ X`.  Suppose `V ⟶ Qy` and `ZU ⟶ Qy` are compatible with all of these,
and let `Qz = ZU ×_{Qy} V`.  Then `Qz = Z ×_{P'} Cc`. -/
private lemma isPullback_productChartFibre
    {C : Type u} [Category.{v} C]
    {X Y Bs W Zs U V P' Qy ZU Qz Cc : C}
    {x : X ⟶ Bs} {y : Y ⟶ Bs} {w : W ⟶ Bs}
    {p₁ : P' ⟶ X} {p₂ : P' ⟶ Y} (hP' : IsPullback p₁ p₂ x y)
    {qyY : Qy ⟶ Y} {qyW : Qy ⟶ W} (hQy : IsPullback qyY qyW y w)
    {cu : Cc ⟶ U} {cv : Cc ⟶ V} {uw : U ⟶ W} {vw : V ⟶ W}
    (hCc : IsPullback cu cv uw vw)
    {a : U ⟶ X} {b : V ⟶ Y} {zx : Zs ⟶ X} {zy : Zs ⟶ Y}
    {zuZ : ZU ⟶ Zs} {zuU : ZU ⟶ U} (hZU : IsPullback zuZ zuU zx a)
    {m : ZU ⟶ Qy} (hm₁ : m ≫ qyY = zuZ ≫ zy) (hm₂ : m ≫ qyW = zuU ≫ uw)
    {n : V ⟶ Qy} (hn₁ : n ≫ qyY = b) (hn₂ : n ≫ qyW = vw)
    {qzZU : Qz ⟶ ZU} {qzV : Qz ⟶ V} (hQz : IsPullback qzZU qzV m n)
    {z : Zs ⟶ P'} (hz₁ : z ≫ p₁ = zx) (hz₂ : z ≫ p₂ = zy)
    {c : Cc ⟶ P'} (hc₁ : c ≫ p₁ = cu ≫ a) (hc₂ : c ≫ p₂ = cv ≫ b)
    {q : Qz ⟶ Cc} (hq₁ : q ≫ cu = qzZU ≫ zuU) (hq₂ : q ≫ cv = qzV) :
    IsPullback (qzZU ≫ zuZ) q z c := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply hP'.hom_ext
    · calc
        ((qzZU ≫ zuZ) ≫ z) ≫ p₁ = qzZU ≫ zuZ ≫ z ≫ p₁ := by simp only [Category.assoc]
        _ = qzZU ≫ zuU ≫ a := by rw [hz₁, hZU.w]
        _ = (q ≫ cu) ≫ a := by rw [hq₁, Category.assoc]
        _ = (q ≫ c) ≫ p₁ := by simp only [Category.assoc, hc₁]
    · calc
        ((qzZU ≫ zuZ) ≫ z) ≫ p₂ = qzZU ≫ zuZ ≫ z ≫ p₂ := by simp only [Category.assoc]
        _ = qzZU ≫ m ≫ qyY := by rw [hz₂, hm₁]
        _ = (qzV ≫ n) ≫ qyY := by rw [← Category.assoc, hQz.w]
        _ = (q ≫ cv) ≫ b := by simp only [Category.assoc, hn₁, hq₂]
        _ = (q ≫ c) ≫ p₂ := by simp only [Category.assoc, hc₂]
  · intro T φ φ' h₁ h₂
    apply hQz.hom_ext
    · apply hZU.hom_ext
      · simpa only [Category.assoc] using h₁
      · calc
          (φ ≫ qzZU) ≫ zuU = (φ ≫ q) ≫ cu := by simp only [Category.assoc, hq₁]
          _ = (φ' ≫ q) ≫ cu := by rw [h₂]
          _ = (φ' ≫ qzZU) ≫ zuU := by simp only [Category.assoc, hq₁]
    · calc
        φ ≫ qzV = (φ ≫ q) ≫ cv := by simp only [Category.assoc, hq₂]
        _ = (φ' ≫ q) ≫ cv := by rw [h₂]
        _ = φ' ≫ qzV := by simp only [Category.assoc, hq₂]
  · intro T rZ rC hr
    have hrX : rZ ≫ zx = (rC ≫ cu) ≫ a := by
      simpa only [Category.assoc, hz₁, hc₁] using hr =≫ p₁
    have hrY : rZ ≫ zy = (rC ≫ cv) ≫ b := by
      simpa only [Category.assoc, hz₂, hc₂] using hr =≫ p₂
    let rZU := hZU.lift rZ (rC ≫ cu) hrX
    have hrZUfst : rZU ≫ zuZ = rZ := hZU.lift_fst _ _ _
    have hrZUsnd : rZU ≫ zuU = rC ≫ cu := hZU.lift_snd _ _ _
    have hrQV : rZU ≫ m = (rC ≫ cv) ≫ n := by
      apply hQy.hom_ext
      · calc
          (rZU ≫ m) ≫ qyY = (rZU ≫ zuZ) ≫ zy := by
            simp only [Category.assoc, hm₁]
          _ = rZ ≫ zy := by rw [hrZUfst]
          _ = (rC ≫ cv) ≫ b := hrY
          _ = ((rC ≫ cv) ≫ n) ≫ qyY := by simp only [Category.assoc, hn₁]
      · calc
          (rZU ≫ m) ≫ qyW = (rZU ≫ zuU) ≫ uw := by
            simp only [Category.assoc, hm₂]
          _ = rC ≫ cu ≫ uw := by simp only [Category.assoc, hrZUsnd]
          _ = rC ≫ cv ≫ vw := by rw [hCc.w]
          _ = ((rC ≫ cv) ≫ n) ≫ qyW := by simp only [Category.assoc, hn₂]
    refine ⟨hQz.lift rZU (rC ≫ cv) hrQV, ?_, ?_⟩
    · rw [← Category.assoc, hQz.lift_fst, hrZUfst]
    · apply hCc.hom_ext
      · rw [Category.assoc, hq₁, ← Category.assoc, hQz.lift_fst, hrZUsnd]
      · rw [Category.assoc, hq₂]
        exact hQz.lift_snd _ _ _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A chart of `(X ×_B Y) ×_{X' ×_{B'} Y'} Cc` is a base change of a chart of `B ×_{B'} W`.**
Let `P` be a fibre product of `P'` and `Bb` over `B'`, let `Qb` be one of `Bb` and `W` over
`B'`, let `Cc ⟶ P'` be a morphism commuting with the two maps to `B'` through `W`, let `PU` be
a fibre product of `P` and `Cc` over `P'`, and let `Ac ⟶ Cc` be a base change of a morphism
`Kc ⟶ Qb` along the resulting `Cc ⟶ W` over `Qb`.  Then the induced `Ac ⟶ PU` is a base change
of `Kc ⟶ Qb` as well. -/
private lemma exists_isPullback_productChartBaseChange
    {C : Type u} [Category.{v} C]
    {P P' Bb B' W Qb Cc Ac Kc PU : C}
    {pp' : P ⟶ P'} {pB : P ⟶ Bb} {pBase : P' ⟶ B'} {bb : Bb ⟶ B'}
    (hPPB : IsPullback pp' pB pBase bb)
    {qbB : Qb ⟶ Bb} {qbW : Qb ⟶ W} {w : W ⟶ B'} (hQb : IsPullback qbB qbW bb w)
    {cChart : Cc ⟶ P'} {cW : Cc ⟶ W} (hcW : cChart ≫ pBase = cW ≫ w)
    {pu₁ : PU ⟶ P} {pu₂ : PU ⟶ Cc} (hPU : IsPullback pu₁ pu₂ pp' cChart)
    {pc : Ac ⟶ Cc} {k1 : Ac ⟶ Kc} {k : Kc ⟶ Qb}
    (hpPB : IsPullback pc k1 cW (k ≫ qbW))
    {a : Ac ⟶ P} (haB : a ≫ pB = k1 ≫ k ≫ qbB)
    {l : Ac ⟶ PU} (hl₁ : l ≫ pu₁ = a) (hl₂ : l ≫ pu₂ = pc) :
    ∃ lQ : PU ⟶ Qb, IsPullback l k1 lQ k := by
  have hcompat : (pu₁ ≫ pB) ≫ bb = (pu₂ ≫ cW) ≫ w := by
    calc
      (pu₁ ≫ pB) ≫ bb = pu₁ ≫ pp' ≫ pBase := by
        simp only [Category.assoc, hPPB.w]
      _ = (pu₂ ≫ cChart) ≫ pBase := by
        rw [← Category.assoc, hPU.w]
      _ = (pu₂ ≫ cW) ≫ w := by simp only [Category.assoc, hcW]
  refine ⟨hQb.lift (pu₁ ≫ pB) (pu₂ ≫ cW) hcompat, ?_⟩
  have hlQ₁ : hQb.lift (pu₁ ≫ pB) (pu₂ ≫ cW) hcompat ≫ qbB = pu₁ ≫ pB :=
    hQb.lift_fst _ _ _
  have hlQ₂ : hQb.lift (pu₁ ≫ pB) (pu₂ ≫ cW) hcompat ≫ qbW = pu₂ ≫ cW :=
    hQb.lift_snd _ _ _
  have hlPB : IsPullback pu₂ (hQb.lift (pu₁ ≫ pB) (pu₂ ≫ cW) hcompat) cW qbW := by
    apply IsPullback.of_bot ?_ hlQ₂.symm hQb.flip
    have hbase := hPU.flip.paste_vert hPPB
    rw [hcW, ← hlQ₁] at hbase
    exact hbase
  refine IsPullback.of_right ?_ ?_ hlPB
  · rw [hl₂]
    exact hpPB
  · apply hQb.hom_ext
    · calc
        (l ≫ hQb.lift (pu₁ ≫ pB) (pu₂ ≫ cW) hcompat) ≫ qbB = (l ≫ pu₁) ≫ pB := by
          simp only [Category.assoc, hlQ₁]
        _ = a ≫ pB := by rw [hl₁]
        _ = (k1 ≫ k) ≫ qbB := by simp only [Category.assoc, haB]
    · calc
        (l ≫ hQb.lift (pu₁ ≫ pB) (pu₂ ≫ cW) hcompat) ≫ qbW = (l ≫ pu₂) ≫ cW := by
          simp only [Category.assoc, hlQ₂]
        _ = pc ≫ cW := by rw [hl₂]
        _ = (k1 ≫ k) ≫ qbW := by simp only [Category.assoc, hpPB.w]

/-- **The chart `U ×_W V` of `X ×_B Y` is surjective étale.**  Let `w` be a surjective étale
chart of an algebraic space `B'`, let `u` and `v` be surjective étale charts of `X' ×_{B'} w`
and of `Y' ×_{B'} w`, let `C₀` be the fibre product of `u` and `v` over `w` in the big fppf
site, and let `cChart` be the induced morphism to a fibre product `P'` of `X'` and `Y'` over
`B'`.  Then `cChart` is étale and surjective. -/
private theorem isEtale_isSurjective_productChart
    {B' X' Y' P' : AlgebraicSpaces B S hS} {x : X' ⟶ B'} {y : Y' ⟶ B'}
    {p'X : P' ⟶ X'} {p'Y : P' ⟶ Y'} (sqP' : IsPullback p'X.hom p'Y.hom x.hom y.hom)
    {W₀ U₀ V₀ C₀ : BigFppfOver B S hS} {w : yoneda.obj W₀ ⟶ B'.1}
    {u : yoneda.obj U₀ ⟶ pullback x.hom w} {v : yoneda.obj V₀ ⟶ pullback y.hom w}
    {cToU : C₀ ⟶ U₀} {cToV : C₀ ⟶ V₀}
    (hcPB : IsPullback (yoneda.map cToU) (yoneda.map cToV)
      (u ≫ pullback.snd x.hom w) (v ≫ pullback.snd y.hom w))
    {cChart : yoneda.obj C₀ ⟶ P'.1}
    (hc₁ : cChart ≫ p'X.hom = yoneda.map cToU ≫ u ≫ pullback.fst x.hom w)
    (hc₂ : cChart ≫ p'Y.hom = yoneda.map cToV ≫ v ≫ pullback.fst y.hom w)
    (hwE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (hwS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (huE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    (huS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    (hvE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v)
    (hvS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v) :
    IsEtale B S hS cChart ∧ IsSurjective B S hS cChart := by
  let : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) := by
    refine ⟨?_⟩
    intro X₁ Y₁ Z₁ f g hf hg
    let : AlgebraicGeometry.Surjective f := hf
    let : AlgebraicGeometry.Surjective g := hg
    infer_instance
  let T := BigFppfOver.toScheme B S hS
  let PE := (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
  let PS := (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T).presheaf
  let : PE.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  let : PS.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  let : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        T).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (F := T)
  let : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        T).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (F := T)
  let : PE.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition _
  let : PS.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition _
  refine ⟨(isEtale_iff_presheaf_of_yoneda B S hS cChart).2
      (property_product_chart PE (IsPullback.of_hasPullback x.hom w)
        (IsPullback.of_hasPullback y.hom w) huE hvE hwE hcPB sqP' hc₁ hc₂),
    isSurjective_of_presheafSurjective B S hS cChart
      (property_product_chart PS (IsPullback.of_hasPullback x.hom w)
        (IsPullback.of_hasPullback y.hom w) huS hvS hwS hcPB sqP' hc₁ hc₂)⟩

/-- **Flat chart squares exist over any étale chart of the target.**  Let `f : F ⟶ G` be a flat
morphism of algebraic spaces over `S` in the sense of Stacks 03ML and let `cG` be an étale chart
of `G`.  Then there is an étale chart `cF` of `F` and a morphism `h` of the big fppf site making
```
cF ⟶ cG
↓     ↓
F  ⟶ G
```
commute, whose underlying morphism of schemes is flat. -/
public theorem exists_etaleChart_square_flat
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G} (hf : IsFlat B S hS f)
    {V₀ : BigFppfOver B S hS} {cG : yoneda.obj V₀ ⟶ G} (hcG : IsEtale B S hS cG) :
    ∃ (U₀ : BigFppfOver B S hS) (cF : yoneda.obj U₀ ⟶ F) (h : U₀ ⟶ V₀),
      IsEtale B S hS cF ∧ yoneda.map h ≫ cG = cF ≫ f ∧
        AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map h) := by
  have hV₀ : IsAlgebraicSpace B S hS (yoneda.obj V₀) := isAlgebraicSpace_yoneda B S hS V₀
  have hQ : IsAlgebraicSpace B S hS (pullback f cG) :=
    isAlgebraicSpace_pullback B S hS f cG hF hV₀ hG
  obtain ⟨U₀, α, _, hαE⟩ := hQ.exists_atlas
  have hfstE : IsEtale B S hS (pullback.fst f cG) :=
    isEtale_of_isPullback B S hS _ _ _ _
      (isPullback_homMk B S hS hV₀ hF hG hQ (IsPullback.of_hasPullback f cG).flip) hcG
  have hcFE : IsEtale B S hS (α ≫ pullback.fst f cG) :=
    isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS α).2 hαE) hfstE
  have hsq : yoneda.map (yoneda.preimage (α ≫ pullback.snd f cG)) ≫ cG =
      (α ≫ pullback.fst f cG) ≫ f := by
    rw [yoneda.map_preimage, Category.assoc, Category.assoc, pullback.condition]
  exact ⟨U₀, α ≫ pullback.fst f cG, yoneda.preimage (α ≫ pullback.snd f cG), hcFE, hsq,
    hf U₀ V₀ (α ≫ pullback.fst f cG) cG _
      ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hcFE)
      ((isEtale_iff_presheaf_of_yoneda B S hS cG).1 hcG) hsq⟩

/-- **The chart square of the footnote of Stacks 0CTQ, through Stacks 0CTA.**  Let `y : Y' ⟶ B'`
and `zx : Z' ⟶ X'` be flat morphisms of algebraic spaces over `S` in the sense of Stacks 03ML.
Let `cB'`, `cX'`, `cY'` and `cZ'` be étale charts of `B'`, `X'`, `Y'` and `Z'`, let `yV` and
`zxT` be morphisms of the big fppf site making the two squares
```
cY' ⟶ cB'          cZ' ⟶ cX'
 ↓       ↓           ↓       ↓
Y'  ⟶  B'          Z'  ⟶  X'
```
commute, and let `xU` and `zyT` complete the chart square of schemes.  Then, for an arbitrary
morphism `s` of schemes into the chart of `B'`, the fibre product of the base changes of the
charts of `X'` and of `Y'` along `s` is Tor independent from the chart of `Z'` over the fibre
product of the charts of `X'` and of `Y'`, in the sense of Stacks 08IA. -/
public theorem torIndependent_schemeCharts_of_isFlat
    {B' X' Y' Z' : AlgebraicSpaces B S hS} {y : Y' ⟶ B'} {zx : Z' ⟶ X'}
    (hy : IsFlat B S hS y.hom) (hzx : IsFlat B S hS zx.hom)
    {W'₀ U'₀ V'₀ T'₀ : BigFppfOver B S hS}
    {xU : U'₀ ⟶ W'₀} {yV : V'₀ ⟶ W'₀} {zxT : T'₀ ⟶ U'₀} {zyT : T'₀ ⟶ V'₀}
    (hzT : zxT ≫ xU = zyT ≫ yV)
    {cB' : yoneda.obj W'₀ ⟶ B'.1} {cX' : yoneda.obj U'₀ ⟶ X'.1}
    {cY' : yoneda.obj V'₀ ⟶ Y'.1} {cZ' : yoneda.obj T'₀ ⟶ Z'.1}
    (hcB' : IsEtale B S hS cB') (hcX' : IsEtale B S hS cX')
    (hcY' : IsEtale B S hS cY') (hcZ' : IsEtale B S hS cZ')
    (hsqY : yoneda.map yV ≫ cB' = cY' ≫ y.hom)
    (hsqZ : yoneda.map zxT ≫ cX' = cZ' ≫ zx.hom)
    {Ws : Scheme.{u}} (s : Ws ⟶ (BigFppfOver.toScheme B S hS).obj W'₀) :
    ∃ (pp : pullback (pullback.snd ((BigFppfOver.toScheme B S hS).map xU) s)
          (pullback.snd ((BigFppfOver.toScheme B S hS).map yV) s) ⟶
        pullback ((BigFppfOver.toScheme B S hS).map xU)
          ((BigFppfOver.toScheme B S hS).map yV))
      (zz : (BigFppfOver.toScheme B S hS).obj T'₀ ⟶
        pullback ((BigFppfOver.toScheme B S hS).map xU)
          ((BigFppfOver.toScheme B S hS).map yV)),
      pp ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map xU)
            ((BigFppfOver.toScheme B S hS).map yV) =
          pullback.fst (pullback.snd ((BigFppfOver.toScheme B S hS).map xU) s)
            (pullback.snd ((BigFppfOver.toScheme B S hS).map yV) s) ≫
            pullback.fst ((BigFppfOver.toScheme B S hS).map xU) s ∧
        pp ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map xU)
              ((BigFppfOver.toScheme B S hS).map yV) =
            pullback.snd (pullback.snd ((BigFppfOver.toScheme B S hS).map xU) s)
              (pullback.snd ((BigFppfOver.toScheme B S hS).map yV) s) ≫
              pullback.fst ((BigFppfOver.toScheme B S hS).map yV) s ∧
        zz ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map xU)
              ((BigFppfOver.toScheme B S hS).map yV) =
            (BigFppfOver.toScheme B S hS).map zxT ∧
        zz ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map xU)
              ((BigFppfOver.toScheme B S hS).map yV) =
            (BigFppfOver.toScheme B S hS).map zyT ∧
        AlgebraicGeometry.TorIndependent pp zz := by
  have hflatY : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map yV) :=
    hy V'₀ W'₀ cY' cB' yV ((isEtale_iff_presheaf_of_yoneda B S hS cY').1 hcY')
      ((isEtale_iff_presheaf_of_yoneda B S hS cB').1 hcB') hsqY
  have hflatZ : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map zxT) :=
    hzx T'₀ U'₀ cZ' cX' zxT ((isEtale_iff_presheaf_of_yoneda B S hS cZ').1 hcZ')
      ((isEtale_iff_presheaf_of_yoneda B S hS cX').1 hcX') hsqZ
  have hzs : (BigFppfOver.toScheme B S hS).map zxT ≫ (BigFppfOver.toScheme B S hS).map xU =
      (BigFppfOver.toScheme B S hS).map zyT ≫ (BigFppfOver.toScheme B S hS).map yV := by
    rw [← Functor.map_comp, ← Functor.map_comp, hzT]
  exact ⟨_, _, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _,
    torIndependent_pullback_product_of_flat s ((BigFppfOver.toScheme B S hS).map xU)
      ((BigFppfOver.toScheme B S hS).map yV) ((BigFppfOver.toScheme B S hS).map zxT)
      ((BigFppfOver.toScheme B S hS).map zyT) hzs⟩

/-- Let `S` be a scheme, let
```
Z' ⟶ Y'
↓     ↓
X' ⟶ B'
```
be a commutative square of algebraic spaces over `S`, let `Bb ⟶ B'` be a morphism and let `Xb`
and `Yb` be the base changes of `X'` and `Y'` to `Bb`.  If `Y' ⟶ B'` and `Z' ⟶ X'` are flat,
then `Xb ×_{Bb} Yb` and `Z'` are Tor independent over `X' ×_{B'} Y'`. -/
@[stacks 0CTQ]
public theorem torIndependent_baseChange_product_of_isFlat
    {Bb B' X' Y' Z' Xb Yb P P' : AlgebraicSpaces B S hS}
    {bb : Bb ⟶ B'} {x : X' ⟶ B'} {y : Y' ⟶ B'} {zx : Z' ⟶ X'} {zy : Z' ⟶ Y'}
    (hz : zx ≫ x = zy ≫ y)
    {xX' : Xb ⟶ X'} {xB : Xb ⟶ Bb} (sqX : IsPullback xX'.hom xB.hom x.hom bb.hom)
    {yY' : Yb ⟶ Y'} {yB : Yb ⟶ Bb} (sqY : IsPullback yY'.hom yB.hom y.hom bb.hom)
    {pXb : P ⟶ Xb} {pYb : P ⟶ Yb} (sqP : IsPullback pXb.hom pYb.hom xB.hom yB.hom)
    {p'X : P' ⟶ X'} {p'Y : P' ⟶ Y'} (sqP' : IsPullback p'X.hom p'Y.hom x.hom y.hom)
    (pp' : P ⟶ P') (hpp'X : pp' ≫ p'X = pXb ≫ xX') (hpp'Y : pp' ≫ p'Y = pYb ≫ yY')
    (zp' : Z' ⟶ P') (hzp'X : zp' ≫ p'X = zx) (hzp'Y : zp' ≫ p'Y = zy)
    (hy : IsFlat B S hS y.hom) (hzx : IsFlat B S hS zx.hom) :
    TorIndependent P.2 Z'.2 P'.2 pp'.hom zp'.hom := by
  let T := BigFppfOver.toScheme B S hS
  -- the four factorisations, read on the underlying presheaves
  have hpp'X' : pp'.hom ≫ p'X.hom = pXb.hom ≫ xX'.hom :=
    congrArg (fun f : P ⟶ X' => f.hom) hpp'X
  have hpp'Y' : pp'.hom ≫ p'Y.hom = pYb.hom ≫ yY'.hom :=
    congrArg (fun f : P ⟶ Y' => f.hom) hpp'Y
  have hzp'X' : zp'.hom ≫ p'X.hom = zx.hom :=
    congrArg (fun f : Z' ⟶ X' => f.hom) hzp'X
  have hzp'Y' : zp'.hom ≫ p'Y.hom = zy.hom :=
    congrArg (fun f : Z' ⟶ Y' => f.hom) hzp'Y
  -- a surjective étale chart of `B'`
  obtain ⟨W₀, w, hwS, hwE⟩ := B'.2.exists_atlas
  have hwEtale : IsEtale B S hS w := (isEtale_iff_presheaf_of_yoneda B S hS w).2 hwE
  let Ws : AlgebraicSpaces B S hS := representedAlgebraicSpace B S hS W₀
  let ws : Ws ⟶ B' := ObjectProperty.homMk w
  -- charts of the three base changes of the diagram to `W₀`
  let Qx := AlgebraicSpaces.fiberProduct B S hS x ws
  let qxX : Qx ⟶ X' := ObjectProperty.homMk (pullback.fst x.hom ws.hom)
  let qxW : Qx ⟶ Ws := ObjectProperty.homMk (pullback.snd x.hom ws.hom)
  obtain ⟨U₀, u, huS, huE⟩ := Qx.2.exists_atlas
  let Qy := AlgebraicSpaces.fiberProduct B S hS y ws
  let qyY : Qy ⟶ Y' := ObjectProperty.homMk (pullback.fst y.hom ws.hom)
  let qyW : Qy ⟶ Ws := ObjectProperty.homMk (pullback.snd y.hom ws.hom)
  obtain ⟨V₀, v, hvS, hvE⟩ := Qy.2.exists_atlas
  let Qb := AlgebraicSpaces.fiberProduct B S hS bb ws
  let qbB : Qb ⟶ Bb := ObjectProperty.homMk (pullback.fst bb.hom ws.hom)
  let qbW : Qb ⟶ Ws := ObjectProperty.homMk (pullback.snd bb.hom ws.hom)
  obtain ⟨K₀, k, hkS, hkE⟩ := Qb.2.exists_atlas
  have hqx : qxX.hom ≫ x.hom = qxW.hom ≫ ws.hom :=
    congrArg (fun f : Qx ⟶ B' => f.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS x ws).w
  have hqy : qyY.hom ≫ y.hom = qyW.hom ≫ ws.hom :=
    congrArg (fun f : Qy ⟶ B' => f.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS y ws).w
  have hqb : qbB.hom ≫ bb.hom = qbW.hom ≫ ws.hom :=
    congrArg (fun f : Qb ⟶ B' => f.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS bb ws).w
  -- the three morphisms of the site to the chart of `B'`
  let xsite : U₀ ⟶ W₀ := yoneda.preimage (u ≫ qxW.hom)
  let ysite : V₀ ⟶ W₀ := yoneda.preimage (v ≫ qyW.hom)
  let ssite : K₀ ⟶ W₀ := yoneda.preimage (k ≫ qbW.hom)
  have hxsite : yoneda.map xsite = u ≫ qxW.hom := yoneda.map_preimage _
  have hysite : yoneda.map ysite = v ≫ qyW.hom := yoneda.map_preimage _
  have hssite : yoneda.map ssite = k ≫ qbW.hom := yoneda.map_preimage _
  let Us : AlgebraicSpaces B S hS := representedAlgebraicSpace B S hS U₀
  let Vs : AlgebraicSpaces B S hS := representedAlgebraicSpace B S hS V₀
  let uX : Us ⟶ X' := ObjectProperty.homMk (u ≫ qxX.hom)
  let vSpace : Vs ⟶ Qy := ObjectProperty.homMk v
  have huXhom : uX.hom = u ≫ qxX.hom := rfl
  have hvSpacehom : vSpace.hom = v := rfl
  -- the chart `U' ×_{W'} V'` of `X' ×_{B'} Y'`, as the fibre product of schemes
  have hbase : ∀ {M N : BigFppfOver B S hS} (f : M ⟶ N),
      T.map f ≫ B.inclusion.map (Over.hom N) = B.inclusion.map (Over.hom M) :=
    fun f => congrArg B.inclusion.map (Over.w f)
  let Csite : BigFppfOver B S hS := pullback xsite ysite
  let cLimitIso : T.obj Csite ≅ pullback (T.map xsite) (T.map ysite) :=
    ((IsPullback.of_hasPullback xsite ysite).map T).isoPullback
  have hcLimitFst : cLimitIso.hom ≫ pullback.fst (T.map xsite) (T.map ysite) =
      T.map (pullback.fst xsite ysite) :=
    ((IsPullback.of_hasPullback xsite ysite).map T).isoPullback_hom_fst
  have hcLimitSnd : cLimitIso.hom ≫ pullback.snd (T.map xsite) (T.map ysite) =
      T.map (pullback.snd xsite ysite) :=
    ((IsPullback.of_hasPullback xsite ysite).map T).isoPullback_hom_snd
  have hCsize : (AlgebraicGeometry.schemeSizeBelow B.cutoff) (T.obj Csite) :=
    Csite.left.property
  have hCschemeSize :
      (AlgebraicGeometry.schemeSizeBelow B.cutoff) (pullback (T.map xsite) (T.map ysite)) := by
    show (pullback (T.map xsite) (T.map ysite)).size < B.cutoff
    change (T.obj Csite).size < B.cutoff at hCsize
    rw [← Scheme.size_congr cLimitIso]
    exact hCsize
  let Cscheme : B.Schemes := ⟨pullback (T.map xsite) (T.map ysite), hCschemeSize⟩
  let CschemeToS : Cscheme ⟶ B.obj hS := ObjectProperty.homMk
    (pullback.fst (T.map xsite) (T.map ysite) ≫ B.inclusion.map U₀.hom)
  let C : BigFppfOver B S hS := Over.mk CschemeToS
  let cToU : C ⟶ U₀ := Over.homMk
    (ObjectProperty.homMk (pullback.fst (T.map xsite) (T.map ysite))) (by
      apply ObjectProperty.hom_ext
      simp [C, CschemeToS])
  let cToV : C ⟶ V₀ := Over.homMk
    (ObjectProperty.homMk (pullback.snd (T.map xsite) (T.map ysite))) (by
      apply ObjectProperty.hom_ext
      show pullback.snd (T.map xsite) (T.map ysite) ≫
        B.inclusion.map (Over.hom V₀) =
        pullback.fst (T.map xsite) (T.map ysite) ≫ B.inclusion.map (Over.hom U₀)
      rw [← hbase ysite, ← hbase xsite, ← Category.assoc, ← Category.assoc, pullback.condition])
  let cSiteToC : Csite ⟶ C := Over.homMk
    (ObjectProperty.homMk cLimitIso.hom) (by
      apply ObjectProperty.hom_ext
      show cLimitIso.hom ≫
          (pullback.fst (T.map xsite) (T.map ysite) ≫
            B.inclusion.map (Over.hom U₀)) =
        B.inclusion.map (Over.hom Csite)
      rw [← Category.assoc, hcLimitFst]
      exact hbase _)
  have hcSiteToU : cSiteToC ≫ cToU = pullback.fst xsite ysite :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hcLimitFst)
  have hcSiteToV : cSiteToC ≫ cToV = pullback.snd xsite ysite :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hcLimitSnd)
  have : IsIso (T.map cSiteToC) := by
    show IsIso cLimitIso.hom
    infer_instance
  have : IsIso cSiteToC := isIso_of_reflects_iso cSiteToC T
  have hcPBsite : IsPullback cToU cToV xsite ysite :=
    (IsPullback.of_hasPullback xsite ysite).of_iso
      (asIso cSiteToC) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using hcSiteToU.symm) (by simpa using hcSiteToV.symm)
      (by simp) (by simp)
  have hcPB := hcPBsite.map yoneda
  have hcPB' : IsPullback (yoneda.map cToU) (yoneda.map cToV)
      (u ≫ qxW.hom) (v ≫ qyW.hom) := by
    simpa only [hxsite, hysite] using hcPB
  -- the chart of `X' ×_{B'} Y'`
  let cX : yoneda.obj C ⟶ X'.1 := yoneda.map cToU ≫ u ≫ qxX.hom
  let cY : yoneda.obj C ⟶ Y'.1 := yoneda.map cToV ≫ v ≫ qyY.hom
  have hcSite : cToU ≫ xsite = cToV ≫ ysite := hcPBsite.w
  have hcCompat : cX ≫ x.hom = cY ≫ y.hom := by
    have h := congrArg (fun f => yoneda.map f ≫ ws.hom) hcSite
    simp only [Functor.map_comp, hxsite, hysite, Category.assoc] at h
    simp only [cX, cY, Category.assoc, hqx, hqy, h]
  let cChart : yoneda.obj C ⟶ P'.1 := sqP'.lift cX cY hcCompat
  have hcChartX : cChart ≫ p'X.hom = yoneda.map cToU ≫ u ≫ qxX.hom :=
    sqP'.lift_fst _ _ _
  have hcChartY : cChart ≫ p'Y.hom = yoneda.map cToV ≫ v ≫ qyY.hom :=
    sqP'.lift_snd _ _ _
  -- the chart of `Z' ×_{X' ×_{B'} Y'} (U' ×_{W'} V')`
  let ZU := AlgebraicSpaces.fiberProduct B S hS zx uX
  let zuZ : ZU ⟶ Z' := ObjectProperty.homMk (pullback.fst zx.hom uX.hom)
  let zuU : ZU ⟶ Us := ObjectProperty.homMk (pullback.snd zx.hom uX.hom)
  have hzu : zuZ.hom ≫ zx.hom = zuU.hom ≫ uX.hom :=
    congrArg (fun f : ZU ⟶ X' => f.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS zx uX).w
  have hzhom : zx.hom ≫ x.hom = zy.hom ≫ y.hom :=
    congrArg (fun f : Z' ⟶ B' => f.hom) hz
  have hzuCompat : (zuZ.hom ≫ zy.hom) ≫ y.hom =
      (zuU.hom ≫ u ≫ qxW.hom) ≫ ws.hom := by
    simp only [Category.assoc, ← hzhom, reassoc_of% hzu, huXhom, hqx]
  let zuQy : ZU ⟶ Qy := ObjectProperty.homMk
    (pullback.lift (zuZ.hom ≫ zy.hom) (zuU.hom ≫ u ≫ qxW.hom) hzuCompat)
  let Qz := AlgebraicSpaces.fiberProduct B S hS zuQy vSpace
  obtain ⟨T₀, t, htS, htE⟩ := Qz.2.exists_atlas
  let qzZU : Qz ⟶ ZU := ObjectProperty.homMk (pullback.fst zuQy.hom vSpace.hom)
  let qzV : Qz ⟶ Vs := ObjectProperty.homMk (pullback.snd zuQy.hom vSpace.hom)
  have hqz : qzZU.hom ≫ zuQy.hom = qzV.hom ≫ vSpace.hom :=
    congrArg (fun f : Qz ⟶ Qy => f.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS zuQy vSpace).w
  let qzZ : Qz ⟶ Z' := qzZU ≫ zuZ
  let tZ : yoneda.obj T₀ ⟶ Z'.1 := t ≫ qzZ.hom
  let tU : yoneda.obj T₀ ⟶ Us.1 := t ≫ qzZU.hom ≫ zuU.hom
  let tV : yoneda.obj T₀ ⟶ Vs.1 := t ≫ qzV.hom
  let tUsite : T₀ ⟶ U₀ := yoneda.preimage tU
  let tVsite : T₀ ⟶ V₀ := yoneda.preimage tV
  have htUsite : yoneda.map tUsite = tU := yoneda.map_preimage _
  have htVsite : yoneda.map tVsite = tV := yoneda.map_preimage _
  have hzuQyY : zuQy.hom ≫ qyY.hom = zuZ.hom ≫ zy.hom := pullback.lift_fst _ _ _
  have hzuQyW : zuQy.hom ≫ qyW.hom = zuU.hom ≫ u ≫ qxW.hom := pullback.lift_snd _ _ _
  have htCompat : tUsite ≫ xsite = tVsite ≫ ysite := by
    apply yoneda.map_injective
    simpa [Functor.map_comp, htUsite, htVsite, tU, tV, hxsite, hysite, hvSpacehom, hzuQyW,
      Category.assoc] using t ≫= hqz =≫ qyW.hom
  let zsite : T₀ ⟶ Csite := pullback.lift tUsite tVsite htCompat
  let zC : T₀ ⟶ C := zsite ≫ cSiteToC
  have hzsiteFst : zsite ≫ pullback.fst xsite ysite = tUsite := pullback.lift_fst _ _ _
  have hzsiteSnd : zsite ≫ pullback.snd xsite ysite = tVsite := pullback.lift_snd _ _ _
  have hzCU : zC ≫ cToU = tUsite := by
    rw [show zC ≫ cToU = zsite ≫ cSiteToC ≫ cToU from Category.assoc _ _ _, hcSiteToU,
      hzsiteFst]
  have hzCV : zC ≫ cToV = tVsite := by
    rw [show zC ≫ cToV = zsite ≫ cSiteToC ≫ cToV from Category.assoc _ _ _, hcSiteToV,
      hzsiteSnd]
  -- the chart `(U' ×_{W'} K) ×_K (V' ×_{W'} K)`
  let Pchart : BigFppfOver B S hS :=
    pullback (pullback.snd xsite ssite) (pullback.snd ysite ssite)
  let pX : Pchart ⟶ U₀ :=
    pullback.fst (pullback.snd xsite ssite) (pullback.snd ysite ssite) ≫
      pullback.fst xsite ssite
  let pY : Pchart ⟶ V₀ :=
    pullback.snd (pullback.snd xsite ssite) (pullback.snd ysite ssite) ≫
      pullback.fst ysite ssite
  let k1 : Pchart ⟶ K₀ :=
    pullback.fst (pullback.snd xsite ssite) (pullback.snd ysite ssite) ≫
      pullback.snd xsite ssite
  have hpX : pX ≫ xsite = k1 ≫ ssite := by
    dsimp only [pX, k1]
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hpY : pY ≫ ysite = k1 ≫ ssite := by
    calc
      pY ≫ ysite = pullback.snd (pullback.snd xsite ssite) (pullback.snd ysite ssite) ≫
          (pullback.fst ysite ssite ≫ ysite) := by
        simp [pY, Category.assoc]
      _ = pullback.snd (pullback.snd xsite ssite) (pullback.snd ysite ssite) ≫
          (pullback.snd ysite ssite ≫ ssite) := by rw [pullback.condition]
      _ = k1 ≫ ssite := by
        rw [← Category.assoc, ← pullback.condition]
  have hpCompat : pX ≫ xsite = pY ≫ ysite := by rw [hpX, hpY]
  have hpCompatT : T.map pX ≫ T.map xsite = T.map pY ≫ T.map ysite := by
    simpa only [Functor.map_comp] using congrArg T.map hpCompat
  let pMap : T.obj Pchart ⟶ pullback (T.map xsite) (T.map ysite) :=
    pullback.lift (T.map pX) (T.map pY) hpCompatT
  let p : Pchart ⟶ C := Over.homMk (ObjectProperty.homMk pMap) (by
    apply ObjectProperty.hom_ext
    show pMap ≫ pullback.fst (T.map xsite) (T.map ysite) ≫
      (Over.hom U₀).hom = (Over.hom Pchart).hom
    calc
      _ = T.map pX ≫ (Over.hom U₀).hom := by
        show (pullback.lift (T.map pX) (T.map pY) hpCompatT ≫
          pullback.fst (T.map xsite) (T.map ysite)) ≫ (Over.hom U₀).hom = _
        rw [pullback.lift_fst]
      _ = (Over.hom Pchart).hom := hbase pX)
  have hp₁ : p ≫ cToU = pX :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _))
  have hp₂ : p ≫ cToV = pY :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _))
  -- the morphism of the chart of the fibre product into `Xb ×_{Bb} Yb`
  let aX' : yoneda.obj Pchart ⟶ X'.1 := yoneda.map pX ≫ u ≫ qxX.hom
  let aY' : yoneda.obj Pchart ⟶ Y'.1 := yoneda.map pY ≫ v ≫ qyY.hom
  let aB : yoneda.obj Pchart ⟶ Bb.1 := yoneda.map k1 ≫ k ≫ qbB.hom
  have hcomm : ∀ {M₀ : BigFppfOver B S hS} {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (pm : Pchart ⟶ M₀) (msite : M₀ ⟶ W₀) (m : yoneda.obj M₀ ⟶ E) (qE : E ⟶ F)
      (qW : E ⟶ yoneda.obj W₀) (f : F ⟶ B'.1), pm ≫ msite = k1 ≫ ssite →
      yoneda.map msite = m ≫ qW → qE ≫ f = qW ≫ ws.hom →
      (yoneda.map pm ≫ m ≫ qE) ≫ f = (yoneda.map k1 ≫ k ≫ qbB.hom) ≫ bb.hom := by
    intro M₀ E F pm msite m qE qW f hpm hm hq
    calc
      (yoneda.map pm ≫ m ≫ qE) ≫ f = yoneda.map (pm ≫ msite) ≫ ws.hom := by
        rw [Functor.map_comp, hm]
        simp only [Category.assoc, hq]
      _ = yoneda.map (k1 ≫ ssite) ≫ ws.hom := by rw [hpm]
      _ = (yoneda.map k1 ≫ k ≫ qbB.hom) ≫ bb.hom := by
        rw [Functor.map_comp, hssite]
        simp only [Category.assoc, hqb]
  have haX : aX' ≫ x.hom = aB ≫ bb.hom := hcomm pX xsite u qxX.hom qxW.hom x.hom hpX hxsite hqx
  have haY : aY' ≫ y.hom = aB ≫ bb.hom := hcomm pY ysite v qyY.hom qyW.hom y.hom hpY hysite hqy
  let aX : yoneda.obj Pchart ⟶ Xb.1 := sqX.lift aX' aB haX
  let aY : yoneda.obj Pchart ⟶ Yb.1 := sqY.lift aY' aB haY
  have haXfst : aX ≫ xX'.hom = aX' := sqX.lift_fst _ _ _
  have haXsnd : aX ≫ xB.hom = aB := sqX.lift_snd _ _ _
  have haYfst : aY ≫ yY'.hom = aY' := sqY.lift_fst _ _ _
  have haYsnd : aY ≫ yB.hom = aB := sqY.lift_snd _ _ _
  have haXY : aX ≫ xB.hom = aY ≫ yB.hom := by rw [haXsnd, haYsnd]
  let a : yoneda.obj Pchart ⟶ P.1 := sqP.lift aX aY haXY
  have hafst : a ≫ pXb.hom = aX := sqP.lift_fst _ _ _
  have hasnd : a ≫ pYb.hom = aY := sqP.lift_snd _ _ _
  have hchart : ∀ {M₀ : BigFppfOver B S hS} (c : M₀ ⟶ C) (l : yoneda.obj M₀ ⟶ P'.1),
      l ≫ p'X.hom = yoneda.map (c ≫ cToU) ≫ u ≫ qxX.hom →
      l ≫ p'Y.hom = yoneda.map (c ≫ cToV) ≫ v ≫ qyY.hom → l = yoneda.map c ≫ cChart := by
    intro M₀ c l h₁ h₂
    apply sqP'.hom_ext
    · simp only [h₁, Category.assoc, hcChartX, Functor.map_comp]
    · simp only [h₂, Category.assoc, hcChartY, Functor.map_comp]
  have hp : a ≫ pp'.hom = yoneda.map p ≫ cChart :=
    hchart p _ (by simp only [hp₁, Category.assoc, hpp'X', reassoc_of% hafst, haXfst, aX'])
      (by simp only [hp₂, Category.assoc, hpp'Y', reassoc_of% hasnd, haYfst, aY'])
  -- the morphism of the chart of `Z' ×_{X' ×_{B'} Y'} (U' ×_{W'} V')` into `Z'`
  have hqzX : qzZ.hom ≫ zx.hom = qzZU.hom ≫ zuU.hom ≫ u ≫ qxX.hom := by
    show (qzZU.hom ≫ zuZ.hom) ≫ zx.hom = _
    rw [Category.assoc, hzu, huXhom]
  have hqzY : qzZ.hom ≫ zy.hom = qzV.hom ≫ v ≫ qyY.hom := by
    have h := congrArg (fun f => f ≫ qyY.hom) hqz
    rw [Category.assoc, hzuQyY, Category.assoc] at h
    exact h
  have hq : tZ ≫ zp'.hom = yoneda.map zC ≫ cChart :=
    hchart zC _
      (by simp only [hzCU, htUsite, Category.assoc, hzp'X', tZ, tU, hqzX])
      (by simp only [hzCV, htVsite, Category.assoc, hzp'Y', tZ, tV, hqzY])
  -- Stacks 0CTA on the chart square
  have huXEtale : IsEtale B S hS uX.hom := by
    refine isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS u).2 huE) ?_
    exact isEtale_of_isPullback B S hS qxW qxX ws x
      (AlgebraicSpaces.isPullback_fiberProduct B S hS x ws).flip hwEtale
  have hcY'Etale : IsEtale B S hS (v ≫ qyY.hom) := by
    refine isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS v).2 hvE) ?_
    exact isEtale_of_isPullback B S hS qyW qyY ws y
      (AlgebraicSpaces.isPullback_fiberProduct B S hS y ws).flip hwEtale
  have hzuZEtale : IsEtale B S hS zuZ.hom :=
    isEtale_of_isPullback B S hS zuU zuZ uX zx
      (AlgebraicSpaces.isPullback_fiberProduct B S hS zx uX).flip huXEtale
  have hqzZUEtale : IsEtale B S hS qzZU.hom :=
    isEtale_of_isPullback B S hS qzV qzZU vSpace zuQy
      (AlgebraicSpaces.isPullback_fiberProduct B S hS zuQy vSpace).flip
      ((isEtale_iff_presheaf_of_yoneda B S hS v).2 hvE)
  have htZEtale : IsEtale B S hS tZ :=
    isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS t).2 htE)
      (isEtale_comp B S hS hqzZUEtale hzuZEtale)
  have hsqYchart : yoneda.map ysite ≫ w = (v ≫ qyY.hom) ≫ y.hom := by
    rw [hysite, Category.assoc, Category.assoc]
    exact congrArg (fun m => v ≫ m) hqy.symm
  have hsqZchart : yoneda.map tUsite ≫ uX.hom = tZ ≫ zx.hom := by
    rw [htUsite]
    dsimp only [tU, tZ]
    simp only [huXhom, Category.assoc]
    rw [hqzX]
  obtain ⟨pp, zz, hpp₁, hpp₂, hzz₁, hzz₂, htor⟩ :=
    torIndependent_schemeCharts_of_isFlat B S hS hy hzx htCompat hwEtale huXEtale hcY'Etale
      htZEtale hsqYchart hsqZchart (T.map ssite)
  -- the chart of the fibre product, as the fibre product of schemes
  have hcPBsiteT := hcPBsite.map T
  have hpPBsite : IsPullback p k1 (cToU ≫ xsite) ssite :=
    product_baseChange (IsPullback.of_hasPullback xsite ssite)
      (IsPullback.of_hasPullback ysite ssite)
      (IsPullback.of_hasPullback (pullback.snd xsite ssite) (pullback.snd ysite ssite))
      hcPBsite hp₁ hp₂
  have hSchemePB : IsPullback pp
      (pullback.fst (pullback.snd (T.map xsite) (T.map ssite))
        (pullback.snd (T.map ysite) (T.map ssite)) ≫
        pullback.snd (T.map xsite) (T.map ssite))
      (T.map (cToU ≫ xsite)) (T.map ssite) := by
    have hpp : pp = pullback.lift
        (pullback.fst (pullback.snd (T.map xsite) (T.map ssite))
          (pullback.snd (T.map ysite) (T.map ssite)) ≫
          pullback.fst (T.map xsite) (T.map ssite))
        (pullback.snd (pullback.snd (T.map xsite) (T.map ssite))
          (pullback.snd (T.map ysite) (T.map ssite)) ≫
          pullback.fst (T.map ysite) (T.map ssite))
        (by
          rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition,
            ← Category.assoc, ← Category.assoc, pullback.condition]) := by
      apply pullback.hom_ext
      · rw [hpp₁, pullback.lift_fst]
      · rw [hpp₂, pullback.lift_snd]
    rw [hpp, Functor.map_comp]
    exact product_baseChange (IsPullback.of_hasPullback (T.map xsite) (T.map ssite))
      (IsPullback.of_hasPullback (T.map ysite) (T.map ssite))
      (IsPullback.of_hasPullback (pullback.snd (T.map xsite) (T.map ssite))
        (pullback.snd (T.map ysite) (T.map ssite)))
      (IsPullback.of_hasPullback (T.map xsite) (T.map ysite))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  let eScheme := hSchemePB.isoPullback ≪≫ (hpPBsite.map T).isoPullback.symm
  have heScheme : eScheme.hom ≫ T.map p = pp := by
    simp [eScheme, IsPullback.isoPullback_inv_fst]
  have hPsize : (AlgebraicGeometry.schemeSizeBelow B.cutoff)
      (pullback (pullback.snd (T.map xsite) (T.map ssite))
        (pullback.snd (T.map ysite) (T.map ssite))) := by
    show _ < B.cutoff
    rw [Scheme.size_congr eScheme]
    exact Pchart.left.property
  let Aleft : B.Schemes := ⟨_, hPsize⟩
  let A : BigFppfOver B S hS := Over.mk
    (ObjectProperty.homMk (eScheme.hom ≫ B.inclusion.map Pchart.hom) :
      Aleft ⟶ B.obj hS)
  let e : A ⟶ Pchart := Over.homMk (ObjectProperty.homMk eScheme.hom) (by rfl)
  have : IsIso (T.map e) := by change IsIso eScheme.hom; infer_instance
  have : IsIso e := isIso_of_reflects_iso e T
  let pNew : A ⟶ C := e ≫ p
  let aNew : yoneda.obj A ⟶ P.1 := yoneda.map e ≫ a
  have hpNew : aNew ≫ pp'.hom = yoneda.map pNew ≫ cChart := by
    simp only [aNew, pNew, Category.assoc, hp, Functor.map_comp]
  -- the Tor independence of the two upper corners of the étale diagram
  have hzzC : T.map zC = zz := by
    apply pullback.hom_ext
    · rw [hzz₁]
      show T.map zC ≫ T.map cToU = _
      rw [← Functor.map_comp, hzCU]
    · rw [hzz₂]
      show T.map zC ≫ T.map cToV = _
      rw [← Functor.map_comp, hzCV]
  have hTorNew : AlgebraicGeometry.TorIndependent (T.map pNew) (T.map zC) := by
    rw [hzzC, show T.map pNew = pp by
      rw [show pNew = e ≫ p from rfl, Functor.map_comp,
        show T.map e = eScheme.hom from rfl, heScheme]]
    exact htor
  -- the two étale surjective charts of the fibre products of the étale diagram
  let pB : P.1 ⟶ Bb.1 := pXb.hom ≫ xB.hom
  let pBase : P'.1 ⟶ B'.1 := p'X.hom ≫ x.hom
  have hPPB : IsPullback pp'.hom pB pBase bb.hom :=
    product_baseChange sqX sqY sqP sqP' hpp'X' hpp'Y'
  let cW : yoneda.obj C ⟶ yoneda.obj W₀ := yoneda.map cToU ≫ yoneda.map xsite
  have hcW : cChart ≫ pBase = cW ≫ ws.hom := by
    show cChart ≫ p'X.hom ≫ x.hom =
      (yoneda.map cToU ≫ yoneda.map xsite) ≫ ws.hom
    calc
      cChart ≫ p'X.hom ≫ x.hom = (cChart ≫ p'X.hom) ≫ x.hom :=
        (Category.assoc _ _ _).symm
      _ = (yoneda.map cToU ≫ u ≫ qxX.hom) ≫ x.hom := by rw [hcChartX]
      _ = yoneda.map cToU ≫ u ≫ qxX.hom ≫ x.hom := by simp only [Category.assoc]
      _ = yoneda.map cToU ≫ u ≫ qxW.hom ≫ ws.hom := by rw [hqx]
      _ = yoneda.map cToU ≫ yoneda.map xsite ≫ ws.hom := by
        simp only [hxsite, Category.assoc]
      _ = (yoneda.map cToU ≫ yoneda.map xsite) ≫ ws.hom :=
        (Category.assoc _ _ _).symm
  have hpPB : IsPullback (yoneda.map p) (yoneda.map k1) cW (k ≫ qbW.hom) := by
    simpa only [Functor.map_comp, hssite] using hpPBsite.map yoneda
  let liftA := pullback.lift a (yoneda.map p) hp
  have haB : a ≫ pB = yoneda.map k1 ≫ k ≫ qbB.hom := by
    dsimp only [pB]
    rw [reassoc_of% hafst, haXsnd]
  have hliftAfst : liftA ≫ pullback.fst pp'.hom cChart = a := pullback.lift_fst _ _ _
  have hliftAsnd : liftA ≫ pullback.snd pp'.hom cChart = yoneda.map p :=
    pullback.lift_snd _ _ _
  obtain ⟨lQ, hAPB⟩ := exists_isPullback_productChartBaseChange hPPB
    (IsPullback.of_hasPullback bb.hom ws.hom) hcW
    (IsPullback.of_hasPullback pp'.hom cChart) hpPB haB hliftAfst hliftAsnd
  have hqzW : (qzZU.hom ≫ zuU.hom) ≫ u ≫ qxW.hom = qzV.hom ≫ v ≫ qyW.hom := by
    calc
      (qzZU.hom ≫ zuU.hom) ≫ u ≫ qxW.hom = qzZU.hom ≫ zuQy.hom ≫ qyW.hom := by
        rw [hzuQyW]
        simp only [Category.assoc]
      _ = (qzV.hom ≫ vSpace.hom) ≫ qyW.hom := by rw [← Category.assoc, hqz]
      _ = qzV.hom ≫ v ≫ qyW.hom := by
        simp only [hvSpacehom, Category.assoc]
  let qC : Qz.1 ⟶ yoneda.obj C := hcPB'.lift (qzZU.hom ≫ zuU.hom) qzV.hom hqzW
  have hqC₁ : qC ≫ yoneda.map cToU = qzZU.hom ≫ zuU.hom := hcPB'.lift_fst _ _ _
  have hqC₂ : qC ≫ yoneda.map cToV = qzV.hom := hcPB'.lift_snd _ _ _
  have hQPB : IsPullback qzZ.hom qC zp'.hom cChart :=
    isPullback_productChartFibre sqP' (IsPullback.of_hasPullback y.hom ws.hom) hcPB'
      (a := uX.hom) (b := v ≫ qyY.hom) (IsPullback.of_hasPullback zx.hom uX.hom)
      hzuQyY hzuQyW rfl rfl (IsPullback.of_hasPullback zuQy.hom vSpace.hom)
      hzp'X' hzp'Y' hcChartX hcChartY hqC₁ hqC₂
  have htqC : t ≫ qC = yoneda.map zC := by
    apply hcPB'.hom_ext
    · rw [Category.assoc, hqC₁, ← Functor.map_comp, hzCU, htUsite]
    · rw [Category.assoc, hqC₂, ← Functor.map_comp, hzCV, htVsite]
  -- étaleness and surjectivity of the morphisms of the étale diagram
  obtain ⟨hcChartEtale, hcChartSurj⟩ :=
    isEtale_isSurjective_productChart B S hS sqP' hcPB' hcChartX hcChartY hwE hwS huE huS
      hvE hvS
  let Cs : AlgebraicSpaces B S hS := representedAlgebraicSpace B S hS C
  let cChartSpace : Cs ⟶ P' := ObjectProperty.homMk cChart
  let PU := AlgebraicSpaces.fiberProduct B S hS pp' cChartSpace
  let puP : PU ⟶ P := ObjectProperty.homMk (pullback.fst pp'.hom cChart)
  let puC : PU ⟶ Cs := ObjectProperty.homMk (pullback.snd pp'.hom cChart)
  have sqPU : IsPullback puP puC pp' cChartSpace :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS pp' cChartSpace
  have hpuPEtale : IsEtale B S hS puP.hom :=
    isEtale_of_isPullback B S hS puC puP cChartSpace pp' sqPU.flip hcChartEtale
  let PE := (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
  let PS := (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T).presheaf
  let : PE.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  let : PS.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have hliftAE : PE liftA := PE.of_isPullback hAPB.flip hkE
  have hliftAS : PS liftA := PS.of_isPullback hAPB.flip hkS
  let liftANew := pullback.lift aNew (yoneda.map pNew) hpNew
  have hliftANew : liftANew = yoneda.map e ≫ liftA := by
    apply pullback.hom_ext
    · calc
        liftANew ≫ pullback.fst pp'.hom cChart = aNew := pullback.lift_fst _ _ _
        _ = yoneda.map e ≫ a := rfl
        _ = yoneda.map e ≫ liftA ≫ pullback.fst pp'.hom cChart := by rw [hliftAfst]
        _ = (yoneda.map e ≫ liftA) ≫ pullback.fst pp'.hom cChart :=
          (Category.assoc _ _ _).symm
    · calc
        liftANew ≫ pullback.snd pp'.hom cChart = yoneda.map pNew := pullback.lift_snd _ _ _
        _ = yoneda.map e ≫ yoneda.map p := by
          rw [show pNew = e ≫ p from rfl, Functor.map_comp]
        _ = yoneda.map e ≫ liftA ≫ pullback.snd pp'.hom cChart := by rw [hliftAsnd]
        _ = (yoneda.map e ≫ liftA) ≫ pullback.snd pp'.hom cChart :=
          (Category.assoc _ _ _).symm
  have hliftANewE : PE liftANew := by
    rw [hliftANew, PE.cancel_left_of_respectsIso]; exact hliftAE
  have hliftANewS : PS liftANew := by
    rw [hliftANew, PS.cancel_left_of_respectsIso]; exact hliftAS
  have haEtale : IsEtale B S hS a := by
    rw [← hliftAfst]
    exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS liftA).2 hliftAE)
      hpuPEtale
  have haNewEtale : IsEtale B S hS aNew :=
    isEtale_comp B S hS (isEtale_of_isIso B S hS (yoneda.map e)) haEtale
  -- Stacks 08IQ, condition (4) implies condition (1), on the diagram just built
  exact torIndependent_of_torIndependent_scheme_diagram B S hS pp' zp' cChart aNew pNew tZ zC
    puP (pullback.snd pp'.hom cChart) qzZ qC liftANew t
    (IsPullback.of_hasPullback _ _) hQPB
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) rfl htqC
    hcChartEtale hcChartSurj haNewEtale htZEtale
    ((isEtale_iff_presheaf_of_yoneda B S hS liftANew).2 hliftANewE)
    (isSurjective_of_presheafSurjective B S hS liftANew hliftANewS)
    ((isEtale_iff_presheaf_of_yoneda B S hS t).2 htE)
    (isSurjective_of_presheafSurjective B S hS t htS) hTorNew

end AlgebraicGeometry.Space

end
