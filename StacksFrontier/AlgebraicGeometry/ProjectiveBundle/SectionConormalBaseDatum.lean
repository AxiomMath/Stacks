module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionConormal
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalRankTwo

/-!
# The conormal map of a section at a tautological datum pulled back from the base

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `π : 𝐏(F) ⟶ X` the projection of its
projective bundle. `Stacks.RelativeProj.TautologicalDatum.conormalMap`
(`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionConormal.lean`) builds, for a section `σ`
of `π`, a tautological datum `D` on `𝐏(F)` and an invertible quotient `q : F ⟶ L` that `σ`
classifies with respect to `D`, the canonical map

`ker q ⊗ L^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(F)}`

of [Stacks, Tag 0B3V]. This file computes that map at the datum
`Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient`, whose twist is `π^*L` for an
invertible quotient `q : F ⟶ L` **on the base**, and finds that it is **zero**.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap_eq_zero_of_kernelTwistMap_eq_zero` and
  `Stacks.RelativeProj.TautologicalDatum.kernelTwistIdealMap_eq_zero_of_kernelTwistMap_eq_zero`:
  for an arbitrary datum, the two intermediate maps of the construction vanish as soon as the
  restriction of the tautological surjection to `ker q` does.
* `Stacks.RelativeProj.TautologicalDatum.isZero_of_isIso_conormalMap_of_kernelTwistMap_eq_zero` and
  `TautologicalDatum.isZero_pullback_of_isIso_pullback_conormalMap_of_kernelTwistMap_eq_zero`:
  consequently the conormal map is then an isomorphism only where `ker q ⊗ L^{⊗ -1}` vanishes.
* `Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap_ofInvertibleQuotient`: at the datum
  of an invertible quotient on the base, the quotient map a section pulls back is `q` itself,
  composed with the comparison `Stacks.RelativeProj.sectionPullbackNatIso`; it does not depend on
  `σ` at all.
* `Stacks.RelativeProj.TautologicalDatum.classifies_ofInvertibleQuotient`: consequently **every**
  section of `π` classifies the **same** invertible quotient `Q` at this datum.
* `Stacks.RelativeProj.TautologicalDatum.kernelTwistMap_ofInvertibleQuotient_eq_zero`: at this
  datum the restriction of the tautological surjection to `ker q` is the zero morphism.
* `Stacks.RelativeProj.TautologicalDatum.isZero_of_isIso_conormalMap_ofInvertibleQuotient` and
  `TautologicalDatum.isZero_pullback_of_isIso_conormalMap_ofInvertibleQuotient`:
  therefore invertibility of the conormal map at this datum — globally, or after pullback along
  any morphism into `X`, in particular along the inclusion of an affine open trivialising `L` —
  forces `ker q ⊗ L^{⊗ -1}` to vanish.

## What this settles

Tag 0B3V's conormal clause **cannot be stated at an arbitrary tautological datum.** The
reduction of that clause recorded in the module documentation of `SectionConormal.lean` — that
what remains is

```
IsIso ((Scheme.Modules.pullback U.ι).map (D.conormalMap σ hσ Q α hα))
```

for an arbitrary `D : Stacks.RelativeProj.TautologicalDatum X F`, an affine open `U` of the base
trivialising `L` and a section `σ` classifying `Q` — is **false**, and the results below are its
refutation rather than an approach to it.

`Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient` is an inhabitant of
`TautologicalDatum X F` for every invertible quotient `q : F ⟶ L` of `F` on the base, at every
quasi-coherent `F`; its universal surjection is `π^*q`, so `ker q ⟶ F ⟶ L` being zero makes the
composite `π^*(ker q) ⟶ π^*F ⟶ π^*L` zero, and the whole of
`Stacks.RelativeProj.TautologicalDatum.conormalMap` is built out of that composite. At the same
time `classifies_ofInvertibleQuotient` shows that *every* section of `π` classifies `Q` at this
datum, while `𝒞_{σ(X)/𝐏(F)}` genuinely depends on `σ`: for `X` a curve, `F = L₁ ⊕ L₂` with `L₁`,
`L₂` invertible and `σᵢ` the section cut out by the projection onto `Lᵢ`, Tag 0B3V's own clause
gives `𝒞_{σ₁(X)/𝐏(F)} ≅ L₂ ⊗ L₁^{⊗ -1}` and `𝒞_{σ₂(X)/𝐏(F)} ≅ L₁ ⊗ L₂^{⊗ -1}`, which are not
isomorphic unless `(L₁ ⊗ L₂^{⊗ -1})^{⊗ 2} ≅ 𝒪_X`. So no datum-general statement can hold, and
the quantifier over `D` has to go: the clause is about the **genuine** `𝒪_{𝐏(F)}(1)`, that is
about `Stacks.RelativeProj.conormalMapOfSection`, whose datum is
`Stacks.RelativeProj.tautologicalDatum`.

The refutation is stated as a vanishing consequence rather than as a `¬ ∀ …` because the
instance that would turn it into one is not assembled here. A section is available: lacking the
mapping-in universal property of relative `Proj`, the only sections this repository produces are
`Stacks.ProjectiveBundleSplitting.exists_section_freeProjectiveBundle` at a free module — on the
`Stacks.SymGraded.schemeProjectiveBundle` presentation, so a transport across a witness of
`AlgebraicGeometry.projectiveBundlePresentationsAgree`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Projective/BaseChange.lean:233`) is needed, which for
an existence statement costs nothing. What is missing is the rest: an invertible quotient of
`Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex n)` given by a coordinate projection,
the non-vanishing of its kernel for `n ≥ 1`, the fact that tensoring by an invertible module
reflects zero objects, and the non-vanishing of the structure sheaf of the chosen base. None of
the four is computed anywhere here.

## No hypothesis beyond the tag's

`F` is quasi-coherent and nothing more, `q` is an arbitrary surjection onto an invertible module
and is not assumed split, `ker q` is not assumed invertible, and the base is not affine. The
morphism `g` of the pullback statement is arbitrary: it is not assumed to be an open immersion,
and its source is not assumed affine.

## Implementation notes

The proofs are written as compositions of equalities rather than as `rw`/`simp` chains wherever
a morphism of `Scheme.Modules` meets an isomorphism of functors. `Scheme.Modules` is a plain
`def` carrying its own `Category` instance, so `≫`, `0` and `Functor.map` take different
instance arguments according to their neighbours and the two sides of a `rw` can be
syntactically equal and still not match; the module documentation of `SectionConormal.lean`
records the same pitfall.

The same pitfall is why the vanishing of the conormal map is recorded as a consequence — the
`IsZero` statements — and never as an equation `conormalMap … = 0`: the source of
`Stacks.RelativeProj.TautologicalDatum.conormalMap` is spelled as a `sheafTensor` over
`X.presheaf` while its target is an object of `X.Modules`, so its hom-type mixes two spellings
of one category and `Zero` is not synthesised for it. The three generic lemmas in the `Stacks`
namespace below carry the zero-morphism algebra into a category where it does work, and are
applied as terms so that the unifier, not `rw`, matches the composite.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Divisors
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible
  tensorRightFunctor_isEquivalence)

universe u

namespace Stacks

/-- **An invertible fourfold composite whose third factor vanishes has a zero source.** The
composite is spelled out rather than abstracted because the consumer's morphism is a composite
of four factors in a category whose zero morphisms `rw` cannot see; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionConormalBaseDatum.lean`. -/
theorem isZero_src_of_isIso_comp_mid_eq_zero {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) {h : c ⟶ d} (k : d ⟶ e)
    (hh : h = 0) (hiso : IsIso (f ≫ g ≫ h ≫ k)) : Limits.IsZero a :=
  have := hiso
  Limits.IsZero.of_mono_eq_zero (f ≫ g ≫ h ≫ k) (by
    rw [hh, Limits.zero_comp, Limits.comp_zero, Limits.comp_zero])

/-- **The same under a functor preserving zero morphisms**: if the image of such a composite is
invertible then the image of its source is a zero object. -/
theorem isZero_obj_of_isIso_map_comp_mid_eq_zero {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (G : C ⥤ D)
    [G.PreservesZeroMorphisms] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) {h : c ⟶ d} (k : d ⟶ e)
    (hh : h = 0) (hiso : IsIso (G.map (f ≫ g ≫ h ≫ k))) : Limits.IsZero (G.obj a) :=
  have := hiso
  Limits.IsZero.of_mono_eq_zero (G.map (f ≫ g ≫ h ≫ k)) (by
    rw [hh, Limits.zero_comp, Limits.comp_zero, Limits.comp_zero, G.map_zero])

end Stacks

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- **Tensoring the restriction of the tautological surjection to `ker q` by `𝒪(-1)` kills it as
soon as the restriction itself is zero.** Tensoring by the invertible `𝒪(-1)` is an equivalence,
hence additive, so it preserves the zero morphism; the remaining two factors of
`Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap` are isomorphisms. -/
theorem TautologicalDatum.kernelTwistUnitMap_eq_zero_of_kernelTwistMap_eq_zero
    (D : TautologicalDatum X F) (Q : InvertibleQuotient X F) (h : D.kernelTwistMap Q = 0) :
    D.kernelTwistUnitMap Q = 0 := by
  have := tensorPower_isInvertible (projectiveBundle X F).presheaf
    (projectiveBundle X F).ringCatSheaf.2 D.twist (-1)
  have := tensorRightFunctor_isEquivalence (projectiveBundle X F).presheaf
    (projectiveBundle X F).ringCatSheaf.2 D.twistInv
  have : ((sheafTensor ⟨(projectiveBundle X F).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (projectiveBundle X F).presheaf
          (forget₂ CommRingCat RingCat)
          (projectiveBundle X F).ringCatSheaf.2⟩).flip.obj
      D.twistInv).PreservesZeroMorphisms := inferInstance
  have hmz : ((sheafTensor ⟨(projectiveBundle X F).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (projectiveBundle X F).presheaf
          (forget₂ CommRingCat RingCat)
          (projectiveBundle X F).ringCatSheaf.2⟩).flip.obj
      D.twistInv).map (D.kernelTwistMap Q) = 0 := by
    rw [h]
    exact Functor.map_zero _ _ _
  rw [TautologicalDatum.kernelTwistUnitMap, hmz]
  exact zero_comp

/-- **The factorisation of the conormal map through the ideal sheaf of the section vanishes as
soon as the restriction of the tautological surjection to `ker q` does.** The factorisation is
`kernel.lift` of `Stacks.RelativeProj.TautologicalDatum.kernelTwistUnitMap`, and `kernel.ι` is a
monomorphism. -/
theorem TautologicalDatum.kernelTwistIdealMap_eq_zero_of_kernelTwistMap_eq_zero
    (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F)
    (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) (h : D.kernelTwistMap Q = 0) :
    D.kernelTwistIdealMap σ hσ Q α hα = 0 :=
  have hcomp : D.kernelTwistIdealMap σ hσ Q α hα ≫ kernel.ι _ = D.kernelTwistUnitMap Q :=
    kernel.lift_ι _ _ (D.kernelTwistUnitMap_comp_structureSheafModuleHom σ hσ Q α hα)
  zero_of_comp_mono (kernel.ι _)
    (hcomp.trans (D.kernelTwistUnitMap_eq_zero_of_kernelTwistMap_eq_zero Q h))

/-- Pulling back along the section kills the ideal-sheaf factorisation when `kernelTwistMap` is
zero. -/
private theorem pullback_kernelTwistIdealMap_eq_zero
    (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F)
    (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) (h : D.kernelTwistMap Q = 0) :
    (Scheme.Modules.pullback σ).map (D.kernelTwistIdealMap σ hσ Q α hα) = 0 := by
  have : (Scheme.Modules.pullback σ).Additive := inferInstance
  rw [D.kernelTwistIdealMap_eq_zero_of_kernelTwistMap_eq_zero σ hσ Q α hα h]
  exact Functor.map_zero _ _ _

/-- **The conormal map of Tag 0B3V, pulled back along an arbitrary morphism into the base, is an
isomorphism only if `ker q ⊗ L^{⊗ -1}` vanishes there** — whenever the restriction of the
tautological surjection to `ker q` is zero.

The map is a fourfold composite whose third factor is
`Stacks.RelativeProj.TautologicalDatum.kernelTwistIdealMap` pulled back along `σ`, so it is the
zero morphism; `Stacks.isZero_obj_of_isIso_map_comp_mid_eq_zero` then forces its source to be a
zero object.

The vanishing is phrased this way, rather than as an equation `conormalMap … = 0`, because that
equation cannot be *stated*: the source of
`Stacks.RelativeProj.TautologicalDatum.conormalMap` is spelled as a `sheafTensor` over
`X.presheaf` and its target as an object of `X.Modules`, so the hom-type mixes two spellings of
one category and `Zero` is not found for it. See the implementation notes. -/
theorem TautologicalDatum.isZero_pullback_of_isIso_pullback_conormalMap_of_kernelTwistMap_eq_zero
    (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F)
    (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) (h : D.kernelTwistMap Q = 0)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hiso : IsIso ((Scheme.Modules.pullback g).map (D.conormalMap σ hσ Q α hα))) :
    IsZero ((Scheme.Modules.pullback g).obj
      (((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (kernel Q.q)).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)))) :=
  have : (Scheme.Modules.pullback g).PreservesZeroMorphisms := inferInstance
  Stacks.isZero_obj_of_isIso_map_comp_mid_eq_zero _ _ _ _
    (pullback_kernelTwistIdealMap_eq_zero D σ hσ Q α hα h) hiso

/-- **The same before any pullback**: the conormal map itself is an isomorphism only if
`ker q ⊗ L^{⊗ -1}` is a zero object, whenever the restriction of the tautological surjection to
`ker q` is zero. -/
theorem TautologicalDatum.isZero_of_isIso_conormalMap_of_kernelTwistMap_eq_zero
    (D : TautologicalDatum X F) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : InvertibleQuotient X F)
    (α : (Scheme.Modules.pullback σ).obj D.twist ≅ Q.L)
    (hα : D.pullbackQuotientMap σ hσ ≫ α.hom = Q.q) (h : D.kernelTwistMap Q = 0)
    (hiso : IsIso (D.conormalMap σ hσ Q α hα)) :
    IsZero (((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (kernel Q.q)).obj
      (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))) :=
  Stacks.isZero_src_of_isIso_comp_mid_eq_zero _ _ _
    (pullback_kernelTwistIdealMap_eq_zero D σ hσ Q α hα h) hiso

section OfInvertibleQuotient

variable (Q : InvertibleQuotient X F) (σ : X ⟶ projectiveBundle X F)
  (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)

/-- **At the tautological datum of an invertible quotient on the base, the quotient map a
section pulls back is that quotient map itself.** The datum's universal surjection is `π^*q`, so
its pullback along `σ` is `q` read through the comparison
`Stacks.RelativeProj.sectionPullbackNatIso`, by naturality of that comparison; the section
enters only through the comparison, never through the map. -/
theorem TautologicalDatum.pullbackQuotientMap_ofInvertibleQuotient :
    (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q
        Q.epi).pullbackQuotientMap σ hσ =
      Q.q ≫ (sectionPullbackNatIso σ hσ).hom.app Q.L := by
  rw [TautologicalDatum.pullbackQuotientMap_eq]
  exact ((sectionPullbackNatIso σ hσ).hom.naturality Q.q).symm

/-- **Every section of `π` classifies one and the same invertible quotient at the tautological
datum of an invertible quotient on the base.** The identification is the comparison
`Stacks.RelativeProj.sectionPullbackNatIso` at `L`, and compatibility with the quotient maps is
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap_ofInvertibleQuotient`.

This is why Tag 0B3V's conormal clause cannot be stated at an arbitrary tautological datum: the
quotient classified, hence the source `ker q ⊗ L^{⊗ -1}` of the conormal map, is independent of
`σ`, while the conormal sheaf of `σ(X)` is not. -/
theorem TautologicalDatum.classifies_ofInvertibleQuotient :
    (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q Q.epi).Classifies σ hσ Q := by
  refine ⟨((sectionPullbackNatIso σ hσ).app Q.L).symm, ?_⟩
  have key : (sectionPullbackNatIso σ hσ).hom.app Q.L ≫
      ((sectionPullbackNatIso σ hσ).app Q.L).symm.hom = 𝟙 Q.L :=
    ((sectionPullbackNatIso σ hσ).app Q.L).hom_inv_id
  rw [TautologicalDatum.pullbackQuotient_q,
    TautologicalDatum.pullbackQuotientMap_ofInvertibleQuotient]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m : Q.L ⟶ Q.L => Q.q ≫ m) key).trans (Category.comp_id Q.q))

/-- **The restriction of the tautological surjection to the kernel vanishes identically at a
datum pulled back from the base.** The universal surjection is `π^*q`, so the map is
`π^*(ker q ⟶ F ⟶ L)`, and `ker q ⟶ F ⟶ L` is zero. -/
theorem TautologicalDatum.kernelTwistMap_ofInvertibleQuotient_eq_zero :
    (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q Q.epi).kernelTwistMap Q =
      0 :=
  have : (Scheme.Modules.pullback (projectiveBundleToBase X F)).Additive := inferInstance
  show (Scheme.Modules.pullback (projectiveBundleToBase X F)).map (kernel.ι Q.q) ≫
      (Scheme.Modules.pullback (projectiveBundleToBase X F)).map Q.q = 0 from
    ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map_comp (kernel.ι Q.q) Q.q).symm.trans
      ((congrArg (Scheme.Modules.pullback (projectiveBundleToBase X F)).map
        (kernel.condition Q.q)).trans (Functor.map_zero _ _ _))

/-- **Invertibility of the canonical conormal map at a datum pulled back from the base forces
`ker q ⊗ L^{⊗ -1}` to vanish.** This is
`Stacks.RelativeProj.TautologicalDatum.isZero_of_isIso_conormalMap_of_kernelTwistMap_eq_zero`
with its hypothesis discharged by
`Stacks.RelativeProj.TautologicalDatum.kernelTwistMap_ofInvertibleQuotient_eq_zero`. -/
theorem TautologicalDatum.isZero_of_isIso_conormalMap_ofInvertibleQuotient
    (α : (Scheme.Modules.pullback σ).obj
        (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q Q.epi).twist ≅ Q.L)
    (hα : (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q
      Q.epi).pullbackQuotientMap σ hσ ≫ α.hom = Q.q)
    (hiso : IsIso ((TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q
      Q.epi).conormalMap σ hσ Q α hα)) :
    IsZero (((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (kernel Q.q)).obj
      (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))) :=
  TautologicalDatum.isZero_of_isIso_conormalMap_of_kernelTwistMap_eq_zero _ σ hσ Q α hα
    (TautologicalDatum.kernelTwistMap_ofInvertibleQuotient_eq_zero Q) hiso

/-- **The same after pullback along an arbitrary morphism into the base.** This is the form that
refutes the local reduction of Tag 0B3V's conormal clause recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionConormal.lean`: taking `g` to be the
inclusion of an affine open `U` of the base trivialising `L`, invertibility of the pulled-back
conormal map at the datum `Stacks.RelativeProj.TautologicalDatum.ofInvertibleQuotient` would
force `ker q ⊗ L^{⊗ -1}` to vanish on `U`. -/
theorem TautologicalDatum.isZero_pullback_of_isIso_conormalMap_ofInvertibleQuotient
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (α : (Scheme.Modules.pullback σ).obj
        (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q Q.epi).twist ≅ Q.L)
    (hα : (TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q
      Q.epi).pullbackQuotientMap σ hσ ≫ α.hom = Q.q)
    (hiso : IsIso ((Scheme.Modules.pullback g).map
      ((TautologicalDatum.ofInvertibleQuotient X F Q.L Q.invertible Q.q
        Q.epi).conormalMap σ hσ Q α hα))) :
    IsZero ((Scheme.Modules.pullback g).obj
      (((sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (kernel Q.q)).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)))) :=
  TautologicalDatum.isZero_pullback_of_isIso_pullback_conormalMap_of_kernelTwistMap_eq_zero _ σ hσ
    Q α hα (TautologicalDatum.kernelTwistMap_ofInvertibleQuotient_eq_zero Q) g hiso

end OfInvertibleQuotient

end Stacks.RelativeProj

end
