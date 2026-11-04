module

public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.ProjImmersion
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.Effective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending quasi-projective schemes

Let `f : X ⟶ Y` be a surjective finite locally free morphism and let `V` be a scheme over `X`.
A descent datum on `V/X/Y` is effective as soon as `V` carries an ample, an `X`-ample or an
`X`-very ample invertible sheaf, or `V ⟶ X` is projective or quasi-projective.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_isAmple`: condition (3) of
  [Stacks, Tag 0CCJ], an ample invertible sheaf on `V`.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isRelativelyAmple`: condition (4), an
  `X`-ample invertible sheaf on `V`.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isQuasiProjective`: condition (2), `V ⟶ X`
  quasi-projective.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isProjective`: condition (1), `V ⟶ X`
  projective in the sense of clause (1) of [Stacks, Tag 01W8].
* `AlgebraicGeometry.DescentDatum.isEffective_of_isProjectiveMorphism`: condition (1) again, for
  the H-projectivity of clause (2) of [Stacks, Tag 01W8].
* `AlgebraicGeometry.DescentDatum.isEffective_of_isRelativelyVeryAmple`: condition (5), an
  `X`-very ample invertible sheaf on `V`.

## The route

All of them go through the effectivity criterion of [Stacks, Tag 0CCI],
`AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_isAffineOpen`, whose hypothesis is
that any finite nonempty collection of points of `V` lying over one point of `Y` has a common
affine open neighbourhood. The source's reduction chain is followed for (2), (4) and (3):
condition (2) unfolds to condition (4) by the definition of quasi-projectivity in
[Stacks, Tag 01VW], and condition (4) gives condition (3) over an affine open of `X`, where
[Stacks, Tag 01VH] turns relative ampleness into ampleness. Condition (3) is where the geometry
is: part (3) of [Stacks, Tag 01ZY] puts a finite set of points of a scheme with an ample
invertible sheaf into a single affine open.

Conditions (1), (4) and (5) are the only places the hypotheses on `f` beyond surjectivity and
finite local freeness are used, and they use only that `f` is affine: an affine open `Y₀ ∋ y` of
`Y` has affine preimage `B = f⁻¹(Y₀)` in `X`, and the given points all lie in `g⁻¹(B)` for
`g : V ⟶ X`. In condition (4) the restriction of the relatively ample sheaf to `g⁻¹(B)` is
ample, and the affine open that part (3) of Tag 01ZY produces in `g⁻¹(B)` is carried into `V` by
an open immersion.

Conditions (1) and (5) do not go through condition (4); they go through part (4) of
[Stacks, Tag 01ZY] instead. Over `B` the projective bundle `𝐏(ℰ)` of [Stacks, Tag 01OB] is the
`Proj` of the graded ring of sections, by the cartesian chart square of [Stacks, Tag 01NQ], so
an immersion `V ⟶ 𝐏(ℰ)` over `X` restricts to an immersion of `g⁻¹(B)` into that `Proj`, and
part (4) puts a finite set of points of a locally closed subscheme of a `Proj` into an affine
open. Both conditions produce such an immersion directly — condition (1) because that is what
projectivity in the sense of clause (1) of [Stacks, Tag 01W8] asserts, with the closed immersion
of `AlgebraicGeometry.IsProjective` read as an immersion, and condition (5) because that is what
relative very ampleness asserts.

The one shared private lemma is
`AlgebraicGeometry.DescentDatum.exists_isAffineOpen_forall_mem_of_isImmersion_relativeProj`,
stated for an arbitrary `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`; conditions (1)
and (5) differ only in which relative homogeneous spectrum they feed it. For condition (1) that
is `Stacks.SymGraded.schemeProjectiveBundle`, which is the term `AlgebraicGeometry.IsProjective`
is stated over and is by definition
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of the sheaf symmetric algebra, so no
comparison of presentations is needed.

## Implementation notes

Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple` of [Stacks, Tag 01VH], the
reading whose restriction clause is stated at `Stacks.Ample.IsAmple`, which is the ampleness
predicate part (3) of [Stacks, Tag 01ZY] is proved for. Quasi-projectivity is
`AlgebraicGeometry.IsQuasiProjective`, stated at the other reading of Tag 01VH;
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple` passes between them, which is what
`AlgebraicGeometry.isQuasiProjective_iff_hProjectiveIsQuasiProjective` packages.

Condition (1) is delivered at the source's generality, for `AlgebraicGeometry.IsProjective`, the
projectivity of clause (1) of [Stacks, Tag 01W8]: a closed immersion over the base into the
projective bundle `𝐏(ℰ)` of a quasi-coherent `𝒪_X`-module of finite type. It is **not** routed
through condition (2): that is the source's route, and it would need [Stacks, Tag 07RL] for
clause (1) — `AlgebraicGeometry.IsProjective.isQuasiProjective` — whose argument takes the twist
`𝒪_{𝐏(ℰ)}(1)` and its relative ampleness.
The route through part (4) of [Stacks, Tag 01ZY] used here needs no twist at all: it
consumes the immersion into `𝐏(ℰ)` that clause (1) hands over, which is also why the H-projective
case is kept beside it — `AlgebraicGeometry.DescentDatum.isEffective_of_isProjectiveMorphism`
is not a corollary of the general statement, H-projectivity not being known to imply clause (1)
in this repository (that is the second assertion of [Stacks, Tag 01W9], which needs the
identification `ℙⁿ_S ≅ 𝐏(𝒪_S^{⊕ n + 1})` of [Stacks, Tag 01OE]).

Relative very ampleness is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` of
[Stacks, Tag 01VM], which names the twist `𝒪_{𝐏(ℰ)}(1)`. The source's reduction of condition (5)
to condition (4) by [Stacks, Tag 01VN] is deliberately not used: Tag 01VN needs `V ⟶ X`
quasi-compact, which relative very ampleness does not give — the immersion into `𝐏(ℰ)` is not
assumed quasi-compact — and the source gets it only by replacing `V` by a quasi-compact open
containing the given points. The route through part (4) of [Stacks, Tag 01ZY] needs neither that
replacement nor the twist, and the common affine open neighbourhood it produces is the same one.

## References

* [Stacks Project, Tag 0CCJ](https://stacks.math.columbia.edu/tag/0CCJ)
* [Stacks Project, Tag 0CCI](https://stacks.math.columbia.edu/tag/0CCI)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry

namespace DescentDatum

/-- Finitely many points of `V` over one point of `Y` lie over a common affine open of `X`, when
`f : X ⟶ Y` is affine. -/
private theorem exists_isAffineOpen_forall_mem_preimage
    {X Y V : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (g : V ⟶ X)
    {n : ℕ} (y : Y) (v : Fin (n + 1) → V) (hv : ∀ i, (g ≫ f) (v i) = y) :
    ∃ B : X.Opens, IsAffineOpen B ∧ ∀ i, v i ∈ g ⁻¹ᵁ B := by
  obtain ⟨Y₀, hY₀, hyY₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  refine ⟨f ⁻¹ᵁ Y₀, hY₀.preimage f, fun i => ?_⟩
  have h : (g ≫ f) (v i) ∈ Y₀ := by rw [hv i]; exact hyY₀
  simpa using h

/-- Points of an open `T` of `V` that lie in an affine open of the scheme `T` lie in an affine open
of `V`. -/
private theorem exists_isAffineOpen_forall_mem_of_restrict
    {V : Scheme.{u}} (T : V.Opens) {n : ℕ} (v : Fin (n + 1) → V) (hv : ∀ i, v i ∈ T)
    (h : ∃ W : T.toScheme.Opens, IsAffineOpen W ∧
      Set.range (fun i => (⟨v i, hv i⟩ : T.toScheme)) ⊆ (W : Set T.toScheme)) :
    ∃ U : V.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U := by
  obtain ⟨W, hW, hEW⟩ := h
  exact ⟨T.ι ''ᵁ W, hW.image_of_isOpenImmersion _,
    fun i => ⟨⟨v i, hv i⟩, hEW (Set.mem_range_self i), rfl⟩⟩

/-- Finitely many points of `V` lying over one point of `Y` have a common affine open
neighbourhood, when `V` carries an invertible `𝒪_V`-module ample relative to `g : V ⟶ X` and
`f : X ⟶ Y` is affine. -/
private theorem exists_isAffineOpen_forall_mem_of_isRelativelyAmple
    {X Y V : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (g : V ⟶ X) (L : V.Modules)
    [Stacks.Ample.IsInvertibleModule V L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple g L)
    {n : ℕ} (y : Y) (v : Fin (n + 1) → V) (hv : ∀ i, (g ≫ f) (v i) = y) :
    ∃ U : V.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U := by
  obtain ⟨B, hB, hvB⟩ := exists_isAffineOpen_forall_mem_preimage f g y v hv
  exact exists_isAffineOpen_forall_mem_of_restrict _ v hvB
    (Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample _
      (Stacks.RelativeAmple.IsRelativelyAmple.isAmple_preimage g L hL B hB)
      (Set.finite_range fun i => (⟨v i, hvB i⟩ : (g ⁻¹ᵁ B).toScheme)))

/-- **Stacks Project, Tag 0CCJ, condition (3).** Let `f : X ⟶ Y` be a surjective finite locally
free morphism. A descent datum on `V/X/Y` whose scheme `V` carries an ample invertible
`𝒪_V`-module is effective. -/
@[stacks 0CCJ "condition (3), an ample invertible sheaf on V",
  sga "1 VIII 7.6" "special case",
  sga "1 VIII 7.7" "special case"]
theorem isEffective_of_isAmple {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    [IsFiniteLocallyFree f] (D : DescentDatum f) (L : D.over.left.Modules)
    [Stacks.Ample.IsInvertibleModule D.over.left L]
    (hL : Stacks.Ample.IsAmple D.over.left L) :
    DescentData.IsEffective D :=
  isEffective_of_forall_exists_isAffineOpen D fun _ _ v _ => by
    obtain ⟨U, hU, hEU⟩ :=
      Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample L hL
        (Set.finite_range v)
    exact ⟨U, hU, fun i => hEU (Set.mem_range_self i)⟩

/-- **Stacks Project, Tag 0CCJ, condition (4).** Let `f : X ⟶ Y` be a surjective finite locally
free morphism. A descent datum on `V/X/Y` whose scheme `V` carries an invertible `𝒪_V`-module
ample relative to `V ⟶ X` is effective. -/
@[stacks 0CCJ "condition (4), an X-ample invertible sheaf on V",
  sga "1 VIII 7.6" "more general",
  sga "1 VIII 7.7" "more general",
  sga "1 VIII 7.8" "partial",
  sga "1 XI 4.6" "partial"]
theorem isEffective_of_isRelativelyAmple {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    [IsFiniteLocallyFree f] (D : DescentDatum f) (L : D.over.left.Modules)
    [Stacks.Ample.IsInvertibleModule D.over.left L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple D.over.hom L) :
    DescentData.IsEffective D :=
  isEffective_of_forall_exists_isAffineOpen D fun _ y v hv =>
    exists_isAffineOpen_forall_mem_of_isRelativelyAmple f D.over.hom L hL y v hv

/-- **Stacks Project, Tag 0CCJ, condition (2).** Let `f : X ⟶ Y` be a surjective finite locally
free morphism. A descent datum on `V/X/Y` whose scheme `V` is quasi-projective over `X` is
effective. -/
@[stacks 0CCJ "condition (2), V ⟶ X quasi-projective",
  sga "1 VIII 7.6",
  sga "1 VIII 7.7" "Effectivity clause",
  sga "1 XI 4.6" "partial"]
theorem isEffective_of_isQuasiProjective {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    [IsFiniteLocallyFree f] (D : DescentDatum f) (hV : IsQuasiProjective D.over.hom) :
    DescentData.IsEffective D := by
  obtain ⟨-, L, hL, hrel⟩ :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective D.over.hom).mp hV
  have := hL
  exact isEffective_of_isRelativelyAmple D L hrel

/-- **Stacks Project, Tag 0CCJ, condition (1), H-projective case.** Let `f : X ⟶ Y` be a
surjective finite locally free morphism. A descent datum on `V/X/Y` whose scheme `V` is
H-projective over `X` is effective. -/
@[stacks 0CCJ "condition (1), V ⟶ X H-projective",
  sga "1 VIII 7.6" "special case",
  sga "1 VIII 7.7" "special case",
  sga "1 XI 4.6" "partial"]
theorem isEffective_of_isProjectiveMorphism {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    [IsFiniteLocallyFree f] (D : DescentDatum f) (hV : IsProjectiveMorphism D.over.hom) :
    DescentData.IsEffective D :=
  isEffective_of_isQuasiProjective D hV.isQuasiProjective

/-- Finitely many points of a locally closed subscheme `V` of a relative homogeneous spectrum
over `X` that lie over an affine open `B` of `X` have a common affine open neighbourhood: over
`B` the spectrum is a `Proj`, so part (4) of Stacks Tag 01ZY applies to the restriction. -/
private theorem exists_isAffineOpen_forall_mem_of_isImmersion_relativeProj
    {X V : Scheme.{u}} {A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X}
    (P : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A) (g : V ⟶ X)
    (i : V ⟶ P.scheme) [IsImmersion i] (hover : i ≫ P.toBase = g) (B : X.Opens)
    (hB : IsAffineOpen B) {n : ℕ} (v : Fin (n + 1) → V) (hv : ∀ k, v k ∈ g ⁻¹ᵁ B) :
    ∃ U : V.Opens, IsAffineOpen U ∧ ∀ k, v k ∈ U := by
  have hsq := P.chart_isPullback B hB
  have hbase : ((g ⁻¹ᵁ B).ι ≫ i) ≫ P.toBase =
      g.resLE B (g ⁻¹ᵁ B) le_rfl ≫ B.ι := by
    rw [Category.assoc, hover]
    exact (Scheme.Hom.resLE_comp_ι g (e := le_rfl)).symm
  obtain ⟨j, hjchart⟩ : ∃ j, j ≫ P.chart B hB = (g ⁻¹ᵁ B).ι ≫ i :=
    ⟨hsq.lift _ _ hbase, hsq.lift_fst _ _ hbase⟩
  have : IsOpenImmersion (P.chart B hB) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip inferInstance
  have : IsImmersion (j ≫ P.chart B hB) := by rw [hjchart]; infer_instance
  have : IsImmersion j := IsImmersion.of_comp j (P.chart B hB)
  exact exists_isAffineOpen_forall_mem_of_restrict _ v hv
    (Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj (A.grading B) j
      (Set.finite_range fun k => (⟨v k, hv k⟩ : (g ⁻¹ᵁ B).toScheme)))

/-- Finitely many points of `V` lying over one point of `Y` have a common affine open
neighbourhood, when `g : V ⟶ X` is projective and `f : X ⟶ Y` is affine: the closed immersion
of `V` into the projective bundle `𝐏(ℰ)` is an immersion into a relative homogeneous spectrum,
and the affine open of `X` is the preimage of one of `Y`. -/
private theorem exists_isAffineOpen_forall_mem_of_isProjective
    {X Y V : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (g : V ⟶ X) (hg : IsProjective g)
    {n : ℕ} (y : Y) (v : Fin (n + 1) → V) (hv : ∀ i, (g ≫ f) (v i) = y) :
    ∃ U : V.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U := by
  obtain ⟨E, -, -, hqc, i, hi, hover⟩ := hg
  have := hi
  obtain ⟨B, hB, hvB⟩ := exists_isAffineOpen_forall_mem_preimage f g y v hv
  exact exists_isAffineOpen_forall_mem_of_isImmersion_relativeProj
    (Stacks.SymGraded.schemeProjectiveBundle E hqc) g i hover B hB v hvB

/-- **Stacks Project, Tag 0CCJ, condition (1).** Let `f : X ⟶ Y` be a surjective finite locally
free morphism. A descent datum on `V/X/Y` whose scheme `V` is projective over `X` — in the sense
of clause (1) of [Stacks, Tag 01W8], a closed immersion over `X` into the projective bundle of a
quasi-coherent `𝒪_X`-module of finite type — is effective. -/
@[stacks 0CCJ "condition (1), V ⟶ X projective",
  sga "1 VIII 7.6" "special case",
  sga "1 VIII 7.7" "special case",
  sga "1 XI 4.6" "partial"]
theorem isEffective_of_isProjective {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    [IsFiniteLocallyFree f] (D : DescentDatum f) (hV : IsProjective D.over.hom) :
    DescentData.IsEffective D :=
  isEffective_of_forall_exists_isAffineOpen D fun _ y v hv =>
    exists_isAffineOpen_forall_mem_of_isProjective f D.over.hom hV y v hv

/-- Finitely many points of `V` lying over one point of `Y` have a common affine open
neighbourhood, when `V` carries an invertible `𝒪_V`-module very ample relative to `g : V ⟶ X`
and `f : X ⟶ Y` is affine: the affine open of `X` is the preimage of one of `Y`. -/
private theorem exists_isAffineOpen_forall_mem_of_isRelativelyVeryAmple
    {X Y V : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (g : V ⟶ X) (L : V.Modules)
    [Stacks.Ample.IsInvertibleModule V L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple g L)
    {n : ℕ} (y : Y) (v : Fin (n + 1) → V) (hv : ∀ i, (g ≫ f) (v i) = y) :
    ∃ U : V.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U := by
  obtain ⟨E, hE, i, hi, hover, -⟩ := hL
  have := hE
  have := hi
  obtain ⟨B, hB, hvB⟩ := exists_isAffineOpen_forall_mem_preimage f g y v hv
  exact exists_isAffineOpen_forall_mem_of_isImmersion_relativeProj
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E))
    g i hover B hB v hvB

/-- **Stacks Project, Tag 0CCJ, condition (5).** Let `f : X ⟶ Y` be a surjective finite locally
free morphism. A descent datum on `V/X/Y` whose scheme `V` carries an invertible `𝒪_V`-module
very ample relative to `V ⟶ X` is effective. -/
@[stacks 0CCJ "condition (5), an X-very ample invertible sheaf on V",
  sga "1 VIII 7.6" "special case",
  sga "1 VIII 7.7" "special case",
  sga "1 VIII 7.8" "partial"]
theorem isEffective_of_isRelativelyVeryAmple {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    [IsFiniteLocallyFree f] (D : DescentDatum f) (L : D.over.left.Modules)
    [Stacks.Ample.IsInvertibleModule D.over.left L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple D.over.hom L) :
    DescentData.IsEffective D :=
  isEffective_of_forall_exists_isAffineOpen D fun _ y v hv =>
    exists_isAffineOpen_forall_mem_of_isRelativelyVeryAmple f D.over.hom L hL y v hv

end DescentDatum

end AlgebraicGeometry

end
