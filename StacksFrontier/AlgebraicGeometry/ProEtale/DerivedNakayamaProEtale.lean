module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteProEtaleSlices
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence

/-!
# Derived Nakayama on the small pro-étale site

[Stacks, Tag 09BY] says that a derived complete sheaf of `Λ`-modules on `X_proétale` whose
quotient by a finitely generated ideal `I ⊂ Λ` vanishes is itself zero. This file reads the
chapter's statement of that lemma,
`RingedSite.isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_slicedObjectsSituation`, at
the small pro-étale site of a scheme — the tag's own site — ringed by an arbitrary sheaf of
commutative rings.

The site is a `AlgebraicGeometry.RingedSite.{u + 1, u, u + 1}`: its objects live in
`Type (u + 1)` and its morphisms in `Type u`, so its sheaves of modules take sections in
`Type (u + 1)`. The chapter's hypothesis is
`Stacks.WeaklyContractible.SlicedObjectsSituation`, a covering collection of objects which test
surjectivity of sheaves of sets *in that section universe*, on the site and on each of its slice
sites; for this site it is
`AlgebraicGeometry.Scheme.ProEt.slicedObjectsSituation`, whose collection is the affine weakly
contractible objects. Weak contractibility at the morphism universe `Type u` would not do, and
is not even available: `Small.{u} X.ProEt` is false.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetaleRingedSite`: the small pro-étale site of a scheme, ringed
  by a given sheaf of commutative rings on it.

## Main results

* `AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_proetale`: derived Nakayama at the
  small pro-étale site, for an arbitrary sheaf of rings and sheaf of ideals.

## Implementation notes

The two sheafification hypotheses of the chapter's statement are discharged here by explicitly
universe-pinned readings of existing results,
`AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ` and
`AlgebraicGeometry.ProEtale.wEqualsLocallyBijective_proetale_addCommGrpCat_succ`, made local
instances. Pinning is necessary: both sources state their value universe as `max (u + 1) v` with
`v` free, so typeclass search at `AddCommGrpCat.{u + 1}` is stuck on the universe constraint
`u + 1 =?= max (u + 1) ?v` and finds nothing.

## References

* [Stacks Project, Tag 09BY](https://stacks.math.columbia.edu/tag/09BY)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.ProEtale

/-- Presheaves of abelian groups valued in `Type (u + 1)` on the small pro-étale site of a
scheme in `Scheme.{u}` admit sheafification.

This is `AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat` with its value universe
pinned to `u + 1`, the universe in which sheaves of modules on this site take their sections.
The pinning cannot be left to typeclass search: the source states the value universe as
`max (u + 1) v` with `v` free, so search at `AddCommGrpCat.{u + 1}` is stuck on
`u + 1 =?= max (u + 1) ?v`. -/
theorem hasSheafify_proetale_addCommGrpCat_succ (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  hasSheafify_proetale_addCommGrpCat.{u, u} X

/-- On the small pro-étale site of a scheme in `Scheme.{u}`, the weak equivalences of presheaves
of abelian groups valued in `Type (u + 1)` are the locally bijective morphisms.

This is `AlgebraicGeometry.RingedSite.wEqualsLocallyBijectiveAddCommGroup` with its universes
pinned to this site, which typeclass search cannot do for the same reason as for
`AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ`. -/
theorem wEqualsLocallyBijective_proetale_addCommGrpCat_succ (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  RingedSite.wEqualsLocallyBijectiveAddCommGroup.{u + 1, u, u + 1} (Scheme.ProEt.topology X)

attribute [local instance] hasSheafify_proetale_addCommGrpCat_succ
  wEqualsLocallyBijective_proetale_addCommGrpCat_succ

/-- The small pro-étale site of `X`, ringed by a sheaf of commutative rings `𝒪` on it.

The sheaf of rings is valued in `CommRingCat.{u + 1}`, the universe in which sheaves of modules
on this site take their sections, so that the resulting ringed site is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u + 1}` — the shape at which the derived-completeness
chapter is stated. The constant coefficient ringed site
`AlgebraicGeometry.ProEtale.constantCoefficientRingedSite` of a ring `Λ` is the case where `𝒪`
is the constant sheaf of `Λ`. -/
abbrev proetaleRingedSite (X : Scheme.{u})
    (O : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    RingedSite.{u + 1, u, u + 1} where
  C := X.ProEt
  J := Scheme.ProEt.topology X
  O := O

/-- **Derived Nakayama on the small pro-étale site of a scheme.** Let `𝒪` be a sheaf of commutative
rings on `X_proétale`, let `ℐ ⊂ 𝒪` be a sheaf of ideals which is finitely generated on sections
over the affine weakly contractible objects, and let `ℱ` be a sheaf of `𝒪`-modules which is
derived complete along `ℐ` and satisfies `ℐℱ = ℱ`, that is whose adic quotient `ℱ/ℐℱ` vanishes.
Then `ℱ` is zero.

This is the chapter's
`RingedSite.isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_slicedObjectsSituation` read
at this site. Its hypothesis on the site is supplied by
`AlgebraicGeometry.Scheme.ProEt.slicedObjectsSituation`: the affine weakly contractible objects
cover `X_proétale` ([Stacks, Tag 0990]) and test surjectivity of sheaves of sets valued in
`Type (u + 1)` both on the site and on each of its slice sites.

The source's coefficients are a constant ring `Λ` with a finitely generated ideal `I ⊂ Λ`;
`𝒪` here is any sheaf of rings, which includes the constant sheaf `Λ̲`, and `ℐ` is any sheaf of
ideals, which includes the constant ideal sheaf
`AlgebraicGeometry.ProEtale.constantCoefficientIdealSheaf` of `I`. That specialization is taken
in `AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_constantCoefficients`, which is the
tag read at its own objects. The finite-generation hypothesis below is discharged there from
`I.FG` alone — nothing more is assumed of `Λ`, in particular not that it is Noetherian — by
`AlgebraicGeometry.ProEtale.fg_constantCoefficientIdealSheaf_obj`.

The sections themselves need no local-to-global step: the constant ideal sheaf is
`SheafOfModules.kerIdeal` of reduction, and `SheafOfModules.kerIdeal_obj` says its sections are
the sectionwise kernel of the reduction ring map. What that lemma then has to supply is the
finite generation of the kernel, over the *ring* `Γ(W, Λ̲)`, and the input for it is
`Stacks.ConstantSheaf.fg_ker_constantSheaf_ringCatMap_app`, which asks only that the kernel
ideal of the coefficient ring map be finitely generated. Its statement is about the
sheafification of the constant presheaf of *rings*, whereas this ideal sheaf is a kernel of
constant sheaves of `CommRingCat` composed with `forget₂ CommRingCat RingCat` — two different
sheaves, which `CategoryTheory.constantCommuteCompose` identifies. -/
theorem isZero_of_isDerivedComplete_proetale (X : Scheme.{u})
    (O : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O)))
    (hI : ∀ W : X.ProEt, IsAffine W.left →
      (Scheme.ProEt.topology X).IsWeaklyContractible W →
      (I.toSubmodule.obj (op W)).FG)
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1} (proetaleRingedSite X O) I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O))
          0).obj F))
    (hIF : RingedSite.idealPowerProduct (proetaleRingedSite X O) I F 1 = ⊤) :
    IsZero F :=
  RingedSite.isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_slicedObjectsSituation
    (proetaleRingedSite X O)
    (Scheme.ProEt.slicedObjectsSituation X
      (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O))
    I (fun W hW ↦ hI W hW.1 hW.2) F hF hIF

end AlgebraicGeometry.ProEtale

end
