module

public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.BaseChange
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists
public import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sheaf of a section of a projective bundle (Stacks 0B3V)

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module, `π : 𝐏(F) ⟶ X` the projection of its
projective bundle, and `σ` a section of `π`. [Stacks, Tag 0B3V] asserts, for the surjection
`q : F ⟶ L` onto an invertible module that `σ` classifies, that

`𝒞_{σ(X)/𝐏(F)} ≅ ker q ⊗ L^{⊗ -1}`.

**This file constructs the canonical map of that clause and proves nothing about its
invertibility.** No tag is attached: a map is not the assertion.

## Main definitions

* `Stacks.RelativeProj.TautologicalDatum.kernelTwistMap`: the map `π^*(ker q) ⟶ 𝒪(1)`, the
  restriction of the tautological surjection to the kernel of `q`.
* `Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap`: that map tensored with `𝒪(-1)`,
  `π^*(ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(F)}`.
* `Stacks.RelativeProj.TautologicalDatum.kernelTwistIdealMap`: its factorisation through the
  ideal sheaf `ℐ_{σ(X)}` of the section.
* `Stacks.RelativeProj.TautologicalDatum.conormalMap`: **the canonical conormal map**
  `ker q ⊗ L^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(F)}`.
* `Stacks.RelativeProj.conormalMapOfSection`: the same with no datum and no quotient
  quantified over — the datum is `Stacks.RelativeProj.tautologicalDatum`, at the genuine
  `𝒪(1)`, and the quotient is the one `σ` classifies.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.pullback_kernelTwistMap_eq_zero` and
  `Stacks.RelativeProj.TautologicalDatum.pullback_kernelTwistUnitMap_eq_zero`: the canonical map
  restricts to zero along `σ`, which is what lets it be lifted into `ℐ_{σ(X)}`.
* `Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap_comp_structureSheafModuleHom`: the
  composite `π^*(ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(F)} ⟶ σ_* 𝒪_X` vanishes.

## Route

The map is built globally; no chart is used, and [Stacks, Tag 0B3V]'s remark that the
construction is independent of the choice of a local generator of `L` is therefore not a step
that has to be formalised at all.

1. `c := π^*(ker q ⟶ F) ≫ τ : π^*(ker q) ⟶ 𝒪(1)`, where `τ` is the tautological surjection.
2. Tensor with `𝒪(-1)` and trivialise `𝒪(1) ⊗ 𝒪(-1)` by
   `Stacks.SheafOfModules.Invertible.tensorProductBraiding` and
   `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` in degree `-1`, giving
   `e : π^*(ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(F)}`.
3. `σ^* c = 0`: pulling `c` back along `σ` turns the three comparison isomorphisms of
   `Stacks.RelativeProj.sectionPullbackNatIso` into the identity and the tautological surjection
   into `q`, so the composite is `ker q ⟶ F ⟶ L`, which is `kernel.condition`. Then `σ^* e = 0`,
   because Tag 01CD's comparison (`Stacks.RingedSpace.comparisonBifunctorIso`) is natural in its
   first variable and tensoring by the invertible `σ^*𝒪(-1)` is an equivalence, hence additive.
4. `e ≫ (𝒪_{𝐏(F)} ⟶ σ_* 𝒪_X) = 0` by transposing along
   `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` — the technique of
   `Stacks.ClosedImmersion.pullbackIdealSheaf_comp_eq_zero` — so `kernel.lift` lands `e` in
   `ℐ_{σ(X)}`.
5. Apply `σ^*` and use `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` (Tag 0B3P's
   conormal clause, for an arbitrary immersion) to reach `𝒞_{σ(X)/𝐏(F)}`.
6. Identify the source with `ker q ⊗ L^{⊗ -1}` by Tag 01CD
   (`Stacks.RingedSpace.pullbackTensorIsoApp`, unconditional), the three comparisons of
   `Stacks.RelativeProj.sectionPullbackNatIso`, and Tag 0B3V's inverse-line base change
   `Stacks.Divisors.inverseQuotientBaseChange`.

## No hypothesis beyond the tag's

`F` is quasi-coherent and nothing more: not invertible, not finite locally free, and the base is
not affine; `q` is an arbitrary surjection onto an invertible module and is not assumed split;
`ker q` is not assumed invertible.

The datum `D : Stacks.RelativeProj.TautologicalDatum X F` is not a hypothesis of
`Stacks.RelativeProj.conormalMapOfSection`: `Stacks.RelativeProj.tautologicalDatum` is that
datum at the genuine `𝒪(1)`, for every quasi-coherent `F`. The pair `(α, hα)` carried by
`Stacks.RelativeProj.TautologicalDatum.conormalMap` is exactly the content of
`Stacks.RelativeProj.TautologicalDatum.classifies_iff`, i.e. the assertion that `σ` is *the*
section attached to `q`, which is how Tag 0B3V's statement pairs the two; at the quotient `σ`
pulls back it is `Iso.refl`, which is what `conormalMapOfSection` supplies.

## What is not done: invertibility, and a reduction that fails

The clause of Tag 0B3V is the *isomorphism*, and the canonical map is not known here to be one.

**A tempting reduction is false.** It is *not* true that the whole remaining content is the
single statement

```
theorem isIso_pullback_conormalMap
    (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hL : (Scheme.Modules.pullback U.ι).obj Q.L ≅
            SheafOfModules.unit U.toScheme.ringCatSheaf) :
    IsIso ((Scheme.Modules.pullback U.ι).map (D.conormalMap σ hσ Q α hα))
```

— the canonical map is an isomorphism over an affine open of the base trivialising `L`. That
statement is **not** Tag 0B3V's clause and is not true, because it quantifies over the
tautological datum. `Stacks.RelativeProj.TautologicalDatum` records only an invertible module on
`𝐏(F)` with an epimorphism onto it from `π^*F`, and
`Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient` inhabits it, for every quasi-coherent
`F`, at a twist *pulled back from the base*: `π^*L` for an invertible quotient `q : F ⟶ L` on `X`,
with universal surjection `π^*q`. At that datum

* every section of `π` classifies one and the same quotient `Q`
  (`Stacks.RelativeProj.TautologicalDatum.classifies_ofInvertibleQuotient`), so the source
  `ker q ⊗ L^{⊗ -1}` of the conormal map does not depend on `σ` while `𝒞_{σ(X)/𝐏(F)}` does; and
* the conormal map is the **zero** morphism, because it is built from
  `π^*(ker q ⟶ F ⟶ L)`, so the displayed `IsIso` would force `ker q ⊗ L^{⊗ -1}` to vanish on `U`
  (`TautologicalDatum.isZero_pullback_of_isIso_conormalMap_ofInvertibleQuotient` in
  `Stacks.RelativeProj`).

Both are proved in `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionConormalBaseDatum.lean`
beside this file, which also records the arithmetic of the counterexample: on a curve with
`F = L₁ ⊕ L₂` the two obvious sections have conormal sheaves `L₂ ⊗ L₁^{⊗ -1}` and
`L₁ ⊗ L₂^{⊗ -1}`.

**What the clause actually is, and where it is blocked.** Tag 0B3V speaks of the genuine
`𝒪_{𝐏(F)}(1)`, so the statement to prove is the invertibility of
`Stacks.RelativeProj.conormalMapOfSection` — no datum quantified, the datum being
`Stacks.RelativeProj.tautologicalDatum`. Invertibility of a morphism of `𝒪_X`-modules is
detected on stalks by `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`, so the
statement is local on `X`, and `L` being invertible every point has an affine neighbourhood on
which `q` is a surjection onto the structure sheaf and so splits. But localising does not avoid
the geometry: the stalk of the ideal sheaf of `σ` at a point of `σ(X)` is computable only from a
local description of `σ(X)` inside `𝐏(F)`, and
`Stacks.RelativeProj.TautologicalDatum.classifies_iff` characterises `σ` by its quotient and
never by a chart.

**The obstruction in the datum has been removed; what is left is the section.** An earlier
revision of this paragraph located the obstruction in `Stacks.RelativeProj.tautologicalDatum`,
which was `Nonempty.some` of `Stacks.RelativeProj.tautologicalDatum` — and so
`Classical.choice`, carrying no equation, with the consequence that *no* statement separating the
genuine `𝒪(1)` from the data of `Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient` could
ever have been proved about it, the refutation above being exactly such a statement. That is
fixed: `tautologicalDatum`
(`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalDatumExists.lean`) is now the
explicit term built from `Stacks.RelativeProj.tautologicalDatumTwist` and
`Stacks.RelativeProj.tautologicalDatumUniv` over the *named* comparison of presentations
`Stacks.RelativeProj.bundlePresentationIso` (that is, `Stacks.ProjectiveBundle.presentationIso`),
with the two projection lemmas `Stacks.RelativeProj.tautologicalDatum_twist` and
`Stacks.RelativeProj.tautologicalDatum_univ` by `rfl`; by its definition the universal surjection
is `Stacks.ProjectiveBundleSplitting.tautologicalMap` pulled back along that comparison and read
out of `π^*F` through `Scheme.Modules.pullbackCongr` and `Scheme.Modules.pullbackComp`. That
map *is* described on a
chart, by `Stacks.Chow.GenuineChern.tautologicalMap_unitSection` and
`Stacks.Chow.GenuineChern.chartIso_inv_degreeSection`
(`StacksFrontier/AlgebraicGeometry/Chow/GenuineChern/ChartTautological.lean:49,65`), and the
pullback comparison is carried across pulled-back sections by
`Stacks.Chow.GenuineChern.pullbackComp_hom_unitSection` and
`Stacks.Chow.GenuineChern.pullbackCongr_hom_unitSection`. So the datum's universal surjection is
now computable over every affine open of the base, and the clause no longer has to be re-stated
at the other presentation and transported.

**Where it is blocked now.** On the *section*. The local computation needs `σ|_U` identified with
the zero section of `𝐕(ker q|_U)` inside the standard open `D₊(t)` of the chart, and that needs
two things this repository does not have. First, that `σ` factors through `D₊(t)` at all: the
classifying datum gives `σ^*τ = q`, so the pullback along `σ` of the degree-one section of `𝒪(1)`
attached to a `t ∈ Γ(U, F)` with `q t = 1` is a unit, and what is wanted is that a section of an
invertible module whose pullback along `σ` generates makes `σ` factor through its non-vanishing
locus, that locus being `D₊(t)`. Second, that the factored morphism is the augmentation: `σ` is
characterised by `Stacks.RelativeProj.TautologicalDatum.classifies_iff`, which says what `σ` does
to `𝒪(1)` and nothing about where `σ` goes, so recovering the morphism from the quotient is the
*uniqueness* half of the mapping-in property of relative `Proj`. That property is absent, and
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/Universal.lean` measures its absence precisely:
`Stacks.RelativeProj.TautologicalDatum.isUniversal_ofInvertible_iff_sections` shows that at a
rank-one datum `IsUniversal` *is* the assertion that `π` has exactly one section, and the only
inhabitant of `IsUniversal` in the repository is over the empty scheme. Nothing here compares a
section of a relative `Proj` with a section of a relative `Spec`.

**The algebraic inputs of the local computation all exist**, and they are what a proof at a
chart-computable datum would consume. Over an affine `U = Spec A` trivialising `L` write
`M := Γ(U, F)`, so that `q` splits as `M ≅ N ⊕ A` with `N = Γ(U, ker q)`. The section lands in
the standard open `D₊(t)` of `Proj (Sym_A M)` cut out by the degree-one element `t = (0, 1)`,
that chart is `Spec` of the degree-zero part of `(Sym_A M)_t`, which for the split `M` is
`Sym_A N`, and `σ|_U` is the zero section of `V(N) = Spec_A(Sym_A N)`, whose ideal is the
irrelevant ideal and whose conormal sheaf is `N`. Each piece of that sentence is available:

* **The chart ring of `Sym` at a split degree-one element.**
  `Stacks.SymmetricAway.chartAlgEquivOfSection`
  (`StacksFrontier/RingTheory/GradedAlgebra/SymmetricAway/SplitDegreeOneChart.lean`) is exactly the
  shape the consumer needs: given a linear form `q : M →ₗ[A] A` and a lift `s` of `1`, the
  degree-zero part of `(Sym_A M)_s` is `Sym_A (ker q)`. `chartAlgEquivOfSplit` is the same for a
  presented splitting.
* **The zero section of a general `V(E)`, and its conormal module.**
  `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`
  (`StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleZeroSection.lean`) is the zero
  section of `𝐕(ℰ) = Spec_X(Sym(ℰ))` for an arbitrary quasi-coherent `ℰ`, a closed immersion
  splitting the projection. On the chart over an affine open of the base it cuts out the
  augmentation ideal — `Stacks.VectorBundleConormal.comap_ker_appLE_vectorBundleZeroSection` —
  and the cotangent module `I/I²` of that ideal is
  `Stacks.VectorBundleConormal.zeroSectionCotangentIso`, which
  `SymmetricAlgebra.augmentationCotangentEquiv`
  (`StacksFrontier/RingTheory/AugmentationIdealSymmetricAlgebra.lean`, `I/I² ≅ K` for an arbitrary
  module `K`) evaluates as `Γ(ℰ, V)`. All of this is in
  `StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleZeroSectionConormal.lean`. Passing
  from that cotangent module to the *sections of the conormal sheaf* over the chart is
  `Stacks.Conormal.affineIdealPullbackIsoCotangent`, which is stated at
  `RingHom.ker (i.app W)` rather than at the `Scheme.Hom.appLE` of the equality
  `i ⁻¹ᵁ W = V` used above; the two differ by the restriction isomorphism along that equality.
* **A standard open of the relative `Proj` as a relative `Spec`.** Not a wall:
  `Stacks.RelativeProj.Data.chartIso`
  (`StacksFrontier/AlgebraicGeometry/RelativeProj/LocalAtBase.lean`) identifies the chart over `U`
  with the preimage of `U`, after which Mathlib's `AlgebraicGeometry.Proj.awayι` and
  `AlgebraicGeometry.Proj.opensRange_awayι` supply the standard open as a `Spec`. What is left
  of it is the transport.
* **The affine model of a conormal sheaf.** `Stacks.Conormal.affineConormalIsoCotangent`
  (`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/AffineIdentification.lean`), Tag 01R3 (2),
  computes the sections of the conormal sheaf over an affine chart as `I/I²`; for a closed
  immersion `Stacks.Conormal.affineIdealPullbackIsoCotangent` does it with no model datum.
  It has **no naturality in the chart**, so local isomorphisms produced from it cannot be glued
  directly — the route to a global statement is `isIso_of_isIso_stalk` above.

What joins those pieces to a section of `𝐏(F)` is the identification of `σ|_U` with the zero
section of `𝐕(ker q|_U)`, which is the two missing steps of the paragraph above: no tag is
attached to the map below.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.Divisors
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso
  tensorProductBraiding tensorProductIso tensorPower_isInvertible
  tensorRightFunctor_isEquivalence)

universe u

namespace Stacks

/-- In a commuting square whose right-hand vertical map is invertible, the left-hand horizontal
map vanishes as soon as the right-hand one does. -/
theorem eq_zero_of_isIso_sq {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {a b a' b' : C} {u : a ⟶ a'} (v : b ≅ b') {f : a ⟶ b} {f' : a' ⟶ b'}
    (h : f ≫ v.hom = u ≫ f') (hf' : f' = 0) : f = 0 := by
  rw [hf', comp_zero] at h
  rw [← Category.comp_id f, ← v.hom_inv_id, ← Category.assoc, h, zero_comp]

/-- A functor carries a composite whose first factor it kills to zero. -/
theorem functor_map_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms D] (G : C ⥤ D) {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    (hf : G.map f = 0) : G.map (f ≫ g) = 0 := by
  rw [G.map_comp, hf, zero_comp]

/-- **A morphism killed by a left adjoint is killed by the transpose of any morphism out of its
image.** If `L.map e = 0` then `e ≫ adj.homEquiv g = 0`, for any `g` out of `L.obj b`. The
hypothesis `hR` is that the right adjoint preserves zero morphisms. -/
theorem comp_homEquiv_eq_zero {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (hR : ∀ x y : D, R.map (0 : x ⟶ y) = 0)
    {a b : C} {c : D} (e : a ⟶ b) (g : L.obj b ⟶ c) (he : L.map e = 0) :
    e ≫ adj.homEquiv b c g = 0 := by
  rw [← Adjunction.homEquiv_naturality_left, he, zero_comp, Adjunction.homEquiv_unit, hR,
    comp_zero]

end Stacks

namespace Stacks.Divisors

/-- The quotient line of an invertible quotient is invertible. This is the structure field
`Stacks.Divisors.InvertibleQuotient.invertible`, registered as an instance so that its integer
tensor powers can be formed without a `letI`. -/
instance InvertibleQuotient.isInvertible_L {X : Scheme.{u}} {E : X.Modules}
    (Q : InvertibleQuotient X E) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 Q.L :=
  Q.invertible

end Stacks.Divisors

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- The twist of a tautological datum is invertible. This is the structure field
`Stacks.RelativeProj.TautologicalDatum.invertible`, registered as an instance so that the
integer tensor powers of the twist can be formed without a `letI`. -/
instance TautologicalDatum.isInvertible_twist (D : TautologicalDatum X F) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveBundle X F).presheaf
      (projectiveBundle X F).ringCatSheaf.2 D.twist :=
  D.invertible

/-- The natural identification of an `𝒪_X`-module with its pullback along a section of the
projective bundle followed by the projection. This is the composite of the three comparison
isomorphisms appearing in `Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap`. -/
def sectionPullbackNatIso (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    𝟭 X.Modules ≅
      Scheme.Modules.pullback (projectiveBundleToBase X F) ⋙ Scheme.Modules.pullback σ :=
  (Scheme.Modules.pullbackId X).symm ≪≫ (Scheme.Modules.pullbackCongr hσ).symm ≪≫
    (Scheme.Modules.pullbackComp σ (projectiveBundleToBase X F)).symm

/-- `Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap` is the pullback of the
tautological surjection along `σ`, preceded by the natural identification
`Stacks.RelativeProj.sectionPullbackNatIso`. The two sides are the same term. -/
theorem TautologicalDatum.pullbackQuotientMap_eq (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    D.pullbackQuotientMap σ hσ =
      (sectionPullbackNatIso σ hσ).hom.app F ≫ (Scheme.Modules.pullback σ).map D.univ :=
  rfl

/-- The map `π^*(ker q) ⟶ 𝒪(1)` obtained by restricting the tautological surjection to the
kernel of an invertible quotient of `F`. -/
def TautologicalDatum.kernelTwistMap (D : TautologicalDatum X F) (Q : InvertibleQuotient X F) :
    (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj (kernel Q.q) ⟶ D.twist :=
  (Scheme.Modules.pullback (projectiveBundleToBase X F)).map (kernel.ι Q.q) ≫ D.univ

/-- **The restriction of `Stacks.RelativeProj.TautologicalDatum.kernelTwistMap` along the
section vanishes.** Pulling back along `σ` turns the tautological surjection into `Q.q` and the
inclusion of the kernel into itself, so the composite is `ker q ⟶ F ⟶ L`, which is zero. -/
theorem TautologicalDatum.pullback_kernelTwistMap_eq_zero (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) :
    (Scheme.Modules.pullback σ).map (D.kernelTwistMap Q) = 0 := by
  have hpb : D.pullbackQuotientMap σ hσ = Q.q ≫ α.inv := by
    rw [← hα, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hnat := (sectionPullbackNatIso σ hσ).hom.naturality (kernel.ι Q.q)
  rw [← Iso.cancel_iso_hom_left ((sectionPullbackNatIso σ hσ).app (kernel Q.q)), Iso.app_hom,
    comp_zero,
    kernelTwistMap, Functor.map_comp, ← Category.assoc]
  rw [show (sectionPullbackNatIso σ hσ).hom.app (kernel Q.q) ≫
      (Scheme.Modules.pullback σ).map
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map (kernel.ι Q.q)) =
      kernel.ι Q.q ≫ (sectionPullbackNatIso σ hσ).hom.app F from hnat.symm]
  rw [Category.assoc, ← D.pullbackQuotientMap_eq σ hσ, hpb, ← Category.assoc,
    kernel.condition, zero_comp]

/-- The inverse twist `𝒪(-1)` of a tautological datum. -/
abbrev TautologicalDatum.twistInv (D : TautologicalDatum X F) : (projectiveBundle X F).Modules :=
  tensorPower (projectiveBundle X F).presheaf (projectiveBundle X F).ringCatSheaf.2 D.twist (-1)

/-- The module `π^*(ker q) ⊗ 𝒪(-1)` on the projective bundle. -/
abbrev TautologicalDatum.kernelTwist (D : TautologicalDatum X F)
    (Q : InvertibleQuotient X F) :
    SheafOfModules.{u} (structureSheafRing (projectiveBundle X F).toRingedSpace) :=
  ((sheafTensor ⟨(projectiveBundle X F).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (projectiveBundle X F).presheaf
          (forget₂ CommRingCat RingCat) (projectiveBundle X F).ringCatSheaf.2⟩).obj
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj (kernel Q.q))).obj D.twistInv

/-- The map `π^*(ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(F)}` obtained from
`Stacks.RelativeProj.TautologicalDatum.kernelTwistMap` by tensoring with `𝒪(-1)` and
trivializing `𝒪(1) ⊗ 𝒪(-1)`. -/
def TautologicalDatum.kernelTwistUnitMap (D : TautologicalDatum X F)
    (Q : InvertibleQuotient X F) :
    D.kernelTwist Q ⟶
      SheafOfModules.unit (structureSheafRing (projectiveBundle X F).toRingedSpace) :=
  ((sheafTensor ⟨(projectiveBundle X F).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (projectiveBundle X F).presheaf
          (forget₂ CommRingCat RingCat)
          (projectiveBundle X F).ringCatSheaf.2⟩).flip.obj
      D.twistInv).map (D.kernelTwistMap Q) ≫
    (tensorProductBraiding (projectiveBundle X F).presheaf
      (projectiveBundle X F).ringCatSheaf.2 D.twist D.twistInv).hom ≫
    (tensorPowerSuccIso (projectiveBundle X F).presheaf
      (projectiveBundle X F).ringCatSheaf.2 D.twist (-1)).hom

/-- Tensoring on the right by a fixed module is the uncurried tensor bifunctor at `(f, 𝟙)`. -/
private theorem sheafTensor_flip_map_eq_uncurry_map {Y : Scheme.{u}} {A A' : Y.Modules}
    (f : A ⟶ A') (B : Y.Modules) :
    (((sheafTensor ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
        (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).flip.obj B).map f) =
      (Functor.uncurry.obj (sheafTensor ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
        (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩)).map ((f, 𝟙 B) : (A, B) ⟶ (A', B)) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).symm

/-- **The restriction of `Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap` along the
section vanishes.** The Tag 01CD comparison is natural in its first variable, so the pullback
of `c ⊗ 𝟙_{𝒪(-1)}` is `σ^*c ⊗ 𝟙`, which is zero by
`Stacks.RelativeProj.TautologicalDatum.pullback_kernelTwistMap_eq_zero` and the additivity of
tensoring by the invertible module `σ^*𝒪(-1)`. -/
theorem TautologicalDatum.pullback_kernelTwistUnitMap_eq_zero (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) :
    (Scheme.Modules.pullback σ).map (D.kernelTwistUnitMap Q) = 0 := by
  have := tensorPower_isInvertible (projectiveBundle X F).presheaf
    (projectiveBundle X F).ringCatSheaf.2 D.twist (-1)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback σ).obj D.twistInv) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback σ.toLRSHom.toShHom D.twistInv
  have := tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2
    ((Scheme.Modules.pullback σ).obj D.twistInv)
  have : ((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj
      ((Scheme.Modules.pullback σ).obj D.twistInv)).PreservesZeroMorphisms := inferInstance
  have hnat := (Stacks.RingedSpace.comparisonNatTrans σ.toLRSHom.toShHom).naturality
    ((D.kernelTwistMap Q, 𝟙 D.twistInv) :
      (((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj (kernel Q.q), D.twistInv) :
        SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
            (projectiveBundle X F).toRingedSpace) ×
          SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
            (projectiveBundle X F).toRingedSpace)) ⟶ (D.twist, D.twistInv))
  have hsq : (Scheme.Modules.pullback σ).map
        (((sheafTensor ⟨(projectiveBundle X F).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (projectiveBundle X F).presheaf
              (forget₂ CommRingCat RingCat)
              (projectiveBundle X F).ringCatSheaf.2⟩).flip.obj
          D.twistInv).map (D.kernelTwistMap Q)) ≫
      (Stacks.RingedSpace.pullbackTensorIsoApp σ.toLRSHom.toShHom D.twist D.twistInv).hom =
    (Stacks.RingedSpace.pullbackTensorIsoApp σ.toLRSHom.toShHom
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj (kernel Q.q))
        D.twistInv).hom ≫
      ((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj
        ((Scheme.Modules.pullback σ).obj D.twistInv)).map
          ((Scheme.Modules.pullback σ).map (D.kernelTwistMap Q)) := by
    rw [sheafTensor_flip_map_eq_uncurry_map]
    erw [sheafTensor_flip_map_eq_uncurry_map (Y := X)]
    rw [← (Scheme.Modules.pullback σ).map_id D.twistInv]
    exact hnat
  have hmz : ((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj
      ((Scheme.Modules.pullback σ).obj D.twistInv)).map
        ((Scheme.Modules.pullback σ).map (D.kernelTwistMap Q)) = 0 := by
    rw [D.pullback_kernelTwistMap_eq_zero σ hσ Q α hα]
    exact Functor.map_zero _ _ _
  have hz : (Scheme.Modules.pullback σ).map
      (((sheafTensor ⟨(projectiveBundle X F).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (projectiveBundle X F).presheaf
            (forget₂ CommRingCat RingCat)
            (projectiveBundle X F).ringCatSheaf.2⟩).flip.obj
        D.twistInv).map (D.kernelTwistMap Q)) = 0 :=
    Stacks.eq_zero_of_isIso_sq _ hsq hmz
  exact Stacks.functor_map_comp_eq_zero _ _ _ hz

/-- **The canonical map lands in the ideal sheaf of the section.** Transposing along
`σ^* ⊣ σ_*` turns the assertion into
`Stacks.RelativeProj.TautologicalDatum.pullback_kernelTwistUnitMap_eq_zero`. -/
theorem TautologicalDatum.kernelTwistUnitMap_comp_structureSheafModuleHom
    (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) :
    D.kernelTwistUnitMap Q ≫ structureSheafModuleHom σ.toLRSHom.toShHom = 0 := by
  rw [← homEquiv_modulePullbackUnitToUnit σ.toLRSHom.toShHom]
  exact Stacks.comp_homEquiv_eq_zero _ (fun _ _ => modulePushforward_map_zero _ _ _) _ _
    (D.pullback_kernelTwistUnitMap_eq_zero σ hσ Q α hα)

/-- **The canonical map `π^*(ker q) ⊗ 𝒪(-1) ⟶ ℐ_{σ(X)}` into the ideal sheaf of the section.**
It is `Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap` factored through the kernel of
`𝒪_{𝐏(F)} ⟶ σ_* 𝒪_X`, which is possible by
`Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap_comp_structureSheafModuleHom`. -/
def TautologicalDatum.kernelTwistIdealMap (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) :
    D.kernelTwist Q ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom :=
  kernel.lift _ _ (D.kernelTwistUnitMap_comp_structureSheafModuleHom σ hσ Q α hα)

/-- The tautological surjection, read as an invertible quotient of `π^*F` on `𝐏(F)`. -/
def TautologicalDatum.toInvertibleQuotient (D : TautologicalDatum X F) :
    InvertibleQuotient (projectiveBundle X F)
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F) where
  L := D.twist
  invertible := D.invertible
  q := D.univ
  epi := D.epi_univ

/-- **The canonical conormal map of [Stacks, Tag 0B3V]**,
`ker q ⊗ L^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(F)}`.

Here `σ` is a section of `π : 𝐏(F) ⟶ X`, `Q` an invertible quotient `q : F ⟶ L` of `F`, and
`α` an identification of `L` with the pullback `σ^*𝒪(1)` of the tautological twist carrying
`q` to the tautological quotient map — that is, `σ` classifies `Q` in the sense of
`Stacks.RelativeProj.TautologicalDatum.classifies_iff`.

The map is `Stacks.RelativeProj.TautologicalDatum.kernelTwistIdealMap` pulled back along `σ`,
followed by `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, with the source identified
by Tag 01CD (`Stacks.RingedSpace.pullbackTensorIsoApp`), the three pullback comparisons of
`Stacks.RelativeProj.sectionPullbackNatIso`, and Tag 0B3V's inverse-line base change
`Stacks.Divisors.inverseQuotientBaseChange`. -/
def TautologicalDatum.conormalMap (D : TautologicalDatum X F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) :
    ((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (kernel Q.q)).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ⟶
      letI := Stacks.ConormalSequenceSplit.isImmersion_of_section (projectiveBundleToBase X F) σ hσ
      Stacks.Conormal.conormalSheaf σ :=
  letI := Stacks.ConormalSequenceSplit.isImmersion_of_section (projectiveBundleToBase X F) σ hσ
  (tensorProductIso X.presheaf X.ringCatSheaf.2
      ((sectionPullbackNatIso σ hσ).app (kernel Q.q))
      (Stacks.Divisors.inverseQuotientBaseChange σ
        ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F) F
        D.toInvertibleQuotient Q α.symm).symm).hom ≫
    (Stacks.RingedSpace.pullbackTensorIsoApp σ.toLRSHom.toShHom
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj (kernel Q.q))
      D.twistInv).inv ≫
    (Scheme.Modules.pullback σ).map (D.kernelTwistIdealMap σ hσ Q α hα) ≫
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv

/-- **Tag 0B3V's canonical conormal map, with no datum hypothesis**: for a section `σ` of
`π : 𝐏(F) ⟶ X` and the invertible quotient `q : F ⟶ L` that `σ` classifies, a canonical map
`ker q ⊗ L^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(F)}`.

The tautological datum is `Stacks.RelativeProj.tautologicalDatum`, the one at the genuine
`𝒪(1)`, and the quotient is the one it pulls back along `σ`; so nothing is quantified over and
no hypothesis beyond `σ ≫ π = 𝟙 X` is carried.

**Invertibility is not proved here.** See the module documentation for what it is still
blocked on. -/
def conormalMapOfSection (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    ((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj
        (kernel ((tautologicalDatum F).pullbackQuotient σ hσ).q)).obj
        (tensorPower X.presheaf X.ringCatSheaf.2
          ((tautologicalDatum F).pullbackQuotient σ hσ).L (-1)) ⟶
      letI := Stacks.ConormalSequenceSplit.isImmersion_of_section (projectiveBundleToBase X F) σ hσ
      Stacks.Conormal.conormalSheaf σ :=
  (tautologicalDatum F).conormalMap σ hσ ((tautologicalDatum F).pullbackQuotient σ hσ)
    (Iso.refl _) (Category.comp_id _)

end Stacks.RelativeProj

end
