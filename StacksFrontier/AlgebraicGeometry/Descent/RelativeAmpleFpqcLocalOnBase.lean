module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0D2P: relative ampleness and an fpqc covering of the base

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module, and
`{g i : S' i ⟶ S}` an fpqc covering of the base. Write `f' i : X' i ⟶ S' i` for the base change
of `f` along `g i` and `p i : X' i ⟶ X` for the other projection, so that `(p i)^* L` is the
pullback of `L`. [Stacks, Tag 0D2P] asserts

> `L` is ample relative to `f` **if and only if** `(p i)^* L` is ample relative to `f' i` for
> every `i`.

The implication `(1) ⟹ (2)` is proved here in full generality, and so is the whole
biconditional for a module isomorphic to the structure sheaf. The implication `(2) ⟹ (1)` is
*not* proved for a general module; what is proved of it are its first two steps, that `f` is
quasi-compact and that `f` is separated. The exact missing input is named in "What is not done".
Following the precedent of [Stacks, Tag 0B5V] in
`StacksFrontier/AlgebraicGeometry/AmpleFiniteSurjective/Basic.lean`, no declaration carries the bare
tag, the source statement being a single unlabelled biconditional; every declaration that carries
it does so under a scoped clause naming exactly what it covers.

Relative ampleness throughout is `Stacks.RelativeAmple.IsRelativelyAmple`, the library's form of
[Stacks, Tag 01VH]; no new predicate is introduced.

## Main results

* `Stacks.Descent.isRelativelyAmple_pullbackModule_of_fpqcCover`: **Tag 0D2P, (1) implies (2)**.
  A relatively ample module stays relatively ample after base change along every member of the
  covering. No property of the covering is used: this is [Stacks, Tag 0893] applied to each
  cartesian square, and the fpqc hypothesis is carried only so that the statement is literally
  the implication the source asserts.
* `Stacks.Descent.quasiCompact_of_forall_isRelativelyAmple_of_fpqcCover` and
  `Stacks.Descent.isSeparated_of_forall_isRelativelyAmple_of_fpqcCover`: **the first two steps of
  (2) implies (1)**. If every `(p i)^* L` is ample relative to `f' i`, then `f` is quasi-compact
  and `f` is separated.
* `Stacks.Descent.isRelativelyAmple_iff_forall_of_fpqcCover_of_iso_unitModule`: **Tag 0D2P in
  full, both directions, for a module isomorphic to `𝒪_X`**.
* `Stacks.Descent.forall_iff_of_fpqcCover`: the bridge between a property of morphisms that is
  fpqc local on the base and an fpqc covering presented as a family of cartesian squares, which
  is the form Tag 0D2P states its hypotheses in.

## The route

For `(1) ⟹ (2)` the base change of a relatively ample module along an arbitrary cartesian square
is [Stacks, Tag 0893], proved as
`Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback`, and nothing else is needed.

The source's proof of `(2) ⟹ (1)` begins by extracting from clause (2) two properties of `f`
alone: quasi-compactness, which is part of the definition of relative ampleness
([Stacks, Tag 01VH]), and separatedness, which is [Stacks, Tag 01VI], proved as

`AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated`. Both descend along the
covering because each is fpqc local on the base — [Stacks, Tag 02KQ],
`Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc`, and
`AlgebraicGeometry.isSeparated_isLocalAtTarget_fpqc`. That much is proved below.

For a module isomorphic to `𝒪_X` the biconditional needs none of the rest. Relative ampleness of
such a module is quasi-affineness of `f`
(`Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule`, [Stacks, Tag
0891] in the form that tolerates an isomorphism rather than demanding the structure sheaf on the
nose), the pullback of the module is again isomorphic to the structure sheaf
(`Stacks.AmplePullback.modulePullbackIsoUnitModule`), and quasi-affine morphisms are fpqc local
on the base by [Stacks, Tag 02L7], `Stacks.Descent.isQuasiAffineHom_isLocalAtTarget_fpqc`. So
both sides of Tag 0D2P are, in that case, the two sides of Tag 02L7.

## What is not done

`(2) ⟹ (1)` for a general invertible module. After quasi-compactness and separatedness of `f`,
the source forms the quasi-coherent graded `𝒪_S`-algebra `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}`, the graded
map `ψ_d : f^* 𝒜_d ⟶ L^{⊗ d}`, and the morphism `r_{L, ψ} : X ⟶ Proj_S(𝒜)` of
[Stacks, Tag 01O9]; ampleness is then the statement that `r_{L, ψ}` is an open immersion
([Stacks, Tag 01VJ], clauses (4)–(6)), the formation of `𝒜` commutes with flat base change
([Stacks, Tag 02KH]), so `r_{L_i, ψ_i}` is the base change of `r_{L, ψ}`, and being an open
immersion descends by [Stacks, Tag 02L3].

**Two** of those inputs are absent from this repository, and the flat base change is not one of
them. Clauses (4)–(6) of Tag 01VJ are not proved —
`StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean` records this, only clauses (1) and
(3) being proved there. And the relative `ψ` cannot even be written at the spelling the library's
Tag 01O9, `Stacks.AlgebraicGeometry.RelativeProjFromSections.glued`, consumes: that file takes
the local Tag 01NK data over an affine open cover of the base *as hypotheses* precisely because
there is no sheaf-level restriction of an invertible module along an open immersion at the needed
spelling. So the missing input is the relative `Proj` half of Tag 01VJ, not a lemma about
descent; no gap hypothesis for it is introduced here, since any proposition strong enough to
close `(2) ⟹ (1)` from the material below would be the conclusion itself in another spelling.

The flat base change **is** available. Tag 02KH is proved for an arbitrary quasi-coherent sheaf
of modules over an arbitrary base in degree zero,
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`, and
`StacksFrontier/AlgebraicGeometry/RelativeAmple/GradedDirectImageBaseChange.lean` applies it to the
tensor powers of `L` and composes with the comparison of the pullback of a tensor power with the
tensor power of the pullback, giving `g^* 𝒜_d ≅ 𝒜'_d` degreewise for the homogeneous pieces
`Stacks.RelativeAmple.gradedDirectImage` of `𝒜`
(`Stacks.RelativeAmple.gradedDirectImageBaseChangeIso`). What is not assembled is `𝒜` itself as a
graded algebra, its multiplication not being built; the module docstring of
`StacksFrontier/AlgebraicGeometry/RelativeAmple/GradedDirectImage.lean` records what that costs.

## References

* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VI](https://stacks.math.columbia.edu/tag/01VI)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 02KQ](https://stacks.math.columbia.edu/tag/02KQ)
* [Stacks Project, Tag 02L7](https://stacks.math.columbia.edu/tag/02L7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample (IsInvertibleModule unitModule)
open Stacks.AmpleLocallyClosed (pullbackModule)

universe v u

namespace Stacks.Descent

/-! ### An fpqc covering presented as a family of cartesian squares -/

section Transfer

variable {P : MorphismProperty Scheme.{u}}

/-- **A property that respects isomorphisms holds of the second projection of a chosen fibre
product exactly when it holds of the corresponding side of any cartesian square over the same
pair of morphisms.** The two morphisms differ by the canonical isomorphism of the square's vertex
with the chosen fibre product. -/
theorem isPullback_snd_iff [P.RespectsIso] {X S X' S' : Scheme.{u}} {p : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback p f' f g) [HasPullback f g] :
    P (pullback.snd f g) ↔ P f' := by
  rw [← hsq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

/-- **A property of morphisms which is fpqc local on the base, read on a family of cartesian
squares.** If `{g i : S' i ⟶ S}` is an fpqc covering and each square with sides `p i`, `f' i`,
`f` and `g i` is cartesian, then `P` holds for `f` exactly when it holds for every `f' i`.

This is `CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd` for the
presieve `Presieve.ofArrows`, with the chosen fibre products traded for the given squares by
`Stacks.Descent.isPullback_snd_iff`. It is the shape in which [Stacks, Tag 0D2P] states its
hypotheses. -/
theorem forall_iff_of_fpqcCover [P.IsLocalAtTarget Scheme.fpqcPrecoverage] {S : Scheme.{u}}
    {I : Type v} {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S}
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) {X : Scheme.{u}} {f : X ⟶ S}
    {X' : I → Scheme.{u}} {p : ∀ i, X' i ⟶ X} {f' : ∀ i, X' i ⟶ S' i}
    (hsq : ∀ i, IsPullback (p i) (f' i) f (g i)) :
    P f ↔ ∀ i, P (f' i) := by
  rw [IsLocalAtTarget.iff_of_forall_pullbackSnd (P := P) (K := Scheme.fpqcPrecoverage) hg
    (f := f)]
  refine ⟨fun h i => ?_, fun h U g'' _ hg'' => ?_⟩
  · have := (hsq i).hasPullback
    exact (isPullback_snd_iff (hsq i)).mp (h (g i) (Presieve.ofArrows.mk i))
  · cases hg'' with
    | mk i => exact (isPullback_snd_iff (hsq i)).mpr (h i)

end Transfer

/-! ### Tag 0D2P, clause (1) implies clause (2) -/

/-- **Stacks Tag 0D2P, clause (1) implies clause (2).** Let `f : X ⟶ S` be a morphism of schemes,
`L` an invertible `𝒪_X`-module and `{g i : S' i ⟶ S}` an fpqc covering of `S`. Let `f' i` be the
base change of `f` along `g i`, presented by a cartesian square with the other projection
`p i : X' i ⟶ X`. If `L` is ample relative to `f`, then `(p i)^* L` is ample relative to `f' i`
for every `i`.

This is [Stacks, Tag 0893] for a cartesian square,
`Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback`, applied one index at a time;
no property of the covering enters, and the fpqc hypothesis is carried only so that the statement
is literally the implication of the source. -/
@[stacks 0D2P "(1) implies (2)"]
theorem isRelativelyAmple_pullbackModule_of_fpqcCover {S : Scheme.{u}} {I : Type v}
    {S' : I → Scheme.{u}} (g : ∀ i, S' i ⟶ S)
    (_hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) {X : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] {X' : I → Scheme.{u}} {p : ∀ i, X' i ⟶ X}
    {f' : ∀ i, X' i ⟶ S' i} (hsq : ∀ i, IsPullback (p i) (f' i) f (g i))
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f' i) (pullbackModule (p i) L) :=
  fun i => Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback (hsq i) L hL

/-! ### The first two steps of clause (2) implies clause (1) -/

section Descent

variable {S : Scheme.{u}} {I : Type v} {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S}
  {X : Scheme.{u}} {f : X ⟶ S} {X' : I → Scheme.{u}} {p : ∀ i, X' i ⟶ X}
  {f' : ∀ i, X' i ⟶ S' i}

/-- **The morphism is quasi-compact: the first step of Tag 0D2P, clause (2) implies clause (1).**
Quasi-compactness of `f' i` is part of relative ampleness of `(p i)^* L` by [Stacks, Tag 01VH],
and quasi-compactness is fpqc local on the base by [Stacks, Tag 02KQ]. -/
theorem quasiCompact_of_forall_isRelativelyAmple_of_fpqcCover
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) (L : X.Modules)
    [IsInvertibleModule X L] (hsq : ∀ i, IsPullback (p i) (f' i) f (g i))
    (h : ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f' i) (pullbackModule (p i) L)) :
    QuasiCompact f :=
  (forall_iff_of_fpqcCover (P := @QuasiCompact) hg hsq).mpr fun i =>
    Stacks.RelativeAmple.IsRelativelyAmple.quasiCompact _ _ (h i)

/-- **The morphism is separated: the second step of Tag 0D2P, clause (2) implies clause (1).**
Relative ampleness of `(p i)^* L` makes `f' i` separated by [Stacks, Tag 01VI], and separatedness
is fpqc local on the base. -/
@[ega "II 4.6.3" "more general"]
theorem isSeparated_of_forall_isRelativelyAmple_of_fpqcCover
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) (L : X.Modules)
    [IsInvertibleModule X L] (hsq : ∀ i, IsPullback (p i) (f' i) f (g i))
    (h : ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f' i) (pullbackModule (p i) L)) :
    IsSeparated f :=
  (forall_iff_of_fpqcCover (P := @IsSeparated) hg hsq).mpr fun i =>
    AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated (h i)

end Descent

/-! ### Tag 0D2P in full for a module isomorphic to the structure sheaf -/

/-- **Stacks Tag 0D2P, both directions, for an invertible module isomorphic to `𝒪_X`.** With
`{g i : S' i ⟶ S}` an fpqc covering of `S` and each square with sides `p i`, `f' i`, `f` and
`g i` cartesian, a module `L` isomorphic to the structure sheaf is ample relative to `f` if and
only if `(p i)^* L` is ample relative to `f' i` for every `i`.

Both sides are quasi-affineness: on the left by
`Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule`, which is
[Stacks, Tag 0891] for a module merely isomorphic to `𝒪_X`, and on the right by the same lemma
applied to the isomorphism `Stacks.AmplePullback.modulePullbackIsoUnitModule` of `(p i)^* L` with
`𝒪_{X' i}`. The equivalence between them is then [Stacks, Tag 02L7], that quasi-affine morphisms
are fpqc local on the base. -/
@[stacks 0D2P "the full equivalence for an invertible module isomorphic to the structure sheaf",
  sga "1 VIII 7.8" "special case"]
theorem isRelativelyAmple_iff_forall_of_fpqcCover_of_iso_unitModule {S : Scheme.{u}} {I : Type v}
    {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S}
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) {X : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (e : L ≅ unitModule X) {X' : I → Scheme.{u}}
    {p : ∀ i, X' i ⟶ X} {f' : ∀ i, X' i ⟶ S' i}
    (hsq : ∀ i, IsPullback (p i) (f' i) f (g i)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f' i) (pullbackModule (p i) L) := by
  rw [Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule f L e,
    forall_iff_of_fpqcCover (P := @IsQuasiAffineHom) hg hsq]
  exact forall_congr' fun i =>
    (Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule (f' i)
      (pullbackModule (p i) L) (Stacks.AmplePullback.modulePullbackIsoUnitModule (p i) L e)).symm

end Stacks.Descent

end
