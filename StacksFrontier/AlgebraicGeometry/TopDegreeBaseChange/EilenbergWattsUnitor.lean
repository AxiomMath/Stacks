module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsSituation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep

/-!
# Identifying the Eilenberg-Watts module with the top-degree cohomology of `F`

`EilenbergWattsSituation.lean` proves that for a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` with affine base and a quasi-coherent
module `F` on `X'`, the endofunctor

> `Φ(M) = H^d(X', F ⊗_{𝒪_{X'}} (f')^* M~)`

of `Γ(Y', ⊤)`-modules **is** tensoring with the single module `Φ(Γ(Y', ⊤))`. The source reads its
conclusion with that module named instead:

> `Φ(M) = H^d(X', F) ⊗_{R'} M`.

This file supplies the identification `Φ(R') ≅ H^d(X', F)` and so states the conclusion in the
source's own form. It is the composite of three isomorphisms at the three factors of the geometric
factor `M ↦ F ⊗ (f')^* M~`: `R'~ ≅ 𝒪_{Spec R'}`, then `(f')^* 𝒪 ≅ 𝒪`, then the **right** unitor
`F ⊗ 𝒪 ≅ F`.

It then removes the affineness of the base from that conclusion in the only way the source itself
does: a situation restricts to any open of its base — `f'⁻¹(V)` is `X ×_Y V`, so the restricted
square is cartesian and no hypothesis on the open or on the base is needed — and over an affine
open the conclusion above applies. The affine opens cover the base, so the conclusion holds at
every point of an **arbitrary** base. Conclusion (b) itself is a single canonical map of sheaves
on `Y'`, and is inverted in `TensorComparisonBase.lean`; see *Where conclusion (b) is proved*
below.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorLeftFunctorObjUnitIso`: the **right** unitor
  `F ⊗ 𝒪 ≅ F` of the sheafified tensor product on an arbitrary site.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeCohomology`:
  `H^d(X', F)`, read as a module over the ring `Γ(Y', ⊤)` of the affine base.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorObjSelfIso`: the geometric factor
  of the affine case takes the base ring to `F` itself.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTopDegreeTensorCohomologyIso`:
  Eilenberg-Watts for the affine case **with its module named**: `M ↦ H^d(X', F ⊗ (f')^* M~)` is
  tensoring with `H^d(X', F)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeFunctorObjSelfIso`:
  `Φ(Γ(Y', ⊤)) ≅ H^d(X', F)` in a situation with affine base, unconditionally.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeTensorCohomologyIso` and
  `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeTensorCohomologyLinearEquiv`:
  the conclusion of the affine case of [Stacks, Tag 0EX3] (b) in the source's own form,
  as an isomorphism of functors and module by module.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase`: a situation restricted to
  an open of its base, with no hypothesis on either.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBaseTopDegreeTensorCohomologyIso`
  and
  `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`
  `.restrictBaseTopDegreeTensorCohomologyLinearEquiv`: **the same conclusion over an arbitrary
  base, on each affine open of that base**, again in both forms. The base of the situation
  carries no hypothesis; only the open does.

## Implementation notes

*The right unitor costs three lines, because symmetry was already there.* Two left unitors
`𝒪 ⊗ - ≅ 𝟭` are available (`Stacks.InvertibleLocallyFree.tensorLeftFunctorUnitIso` and
`Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso`), and an argument order is not a
spelling: the unit has to sit in the *argument* slot, not in the left factor. What closes the gap
is `Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap`, the symmetry of the sheafified tensor
product, which is proved beside the second of those two unitors. Re-running the
`leftUnitorNatIso`-and-sheafification argument with the right unitor would be strictly more work
than composing the two.

*The two `tensorLeftFunctor` constants.* `Stacks.SheafOfModules.tensorLeftFunctor` and
`AlgebraicGeometry.SheafOfModules.tensorLeftFunctor` are different constants with the same
definition; `tensorLeftFunctorSwap` is stated at the first and
`tensorLeftFunctorUnitIso` at the second, because inside the namespace
`Stacks.SheafOfModules.Invertible` the relative name wins over the file's explicit
`open AlgebraicGeometry.SheafOfModules`. They are `rfl`-equal, so the composite below needs no
bridge; the names are written out in full so that which one is meant does not depend on the
ambient namespace.

*Nothing had to be built for the other two factors.* `AlgebraicGeometry.tildeSelf` is Mathlib's,
and is `Iso.refl`; `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` carries
`f^* 𝒪_Y ≅ 𝒪_X` for an **arbitrary** morphism of schemes, the finality of `Opens.map f.base`
being supplied there by `CategoryTheory.final_of_representablyFlat`.

## Where conclusion (b) is proved

Conclusion (b) of [Stacks, Tag 0EX3] is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_higherDirectImageTensorMap`, in
`TensorComparisonBase.lean`: the canonical map
`R^d f'_* F' ⊗ G ⟶ R^d f'_*(F' ⊗ (f')^* G)` of `TensorComparisonCanonical.lean` is invertible
for a situation whose base carries no hypothesis, and
`...topDirectImageTensorComparison` packages it as the isomorphism the tag asserts, with the
canonicity condition that pins the map down.  Both carry the tag.

The results below are the other reading of the same mathematics, and they keep their own value:
they name the module one tensors with — `H^d(f'⁻¹(V), F)` — and state the conclusion as the
displayed tensor identity of the source, module by module over the ring of an affine open, which
is the shape the source's own Eilenberg-Watts argument produces.  They carry no tag because the
tag is registered where the single canonical map of sheaves on `Y'` is inverted; the last two
also present the quasi-coherent module on the base as `M~` for a module `M` over the ring of the
open, which over an affine scheme is a choice of presentation rather than a restriction.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe v u w

noncomputable section

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The right unitor of the sheafified tensor product**: `F ⊗ 𝒪 ≅ F`, with the structure sheaf
in the *argument* slot of the tensor functor rather than in the left factor. The existing unitors
put it in the left factor, so this is not a respelling of them; the symmetry
`tensorLeftFunctorSwap` moves the unit across and `tensorLeftFunctorUnitIso` then cancels it. -/
def tensorLeftFunctorObjUnitIso (F : _root_.SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F))).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ≅ F :=
  Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap O hO
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        F ≪≫
    (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso O hO).app F

end Stacks.SheafOfModules.Invertible

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable (R : Type u) [CommRing R] (W : Over (Spec (CommRingCat.of R)))

/-- **The tilde factor takes the base ring to the structure sheaf.** This is Mathlib's
`AlgebraicGeometry.tildeSelf`, which is `Iso.refl`; the content is only that
`CommRingCat.of_carrier` is `rfl`, so `R` and the carrier of `CommRingCat.of R` are the same
ring. -/
def tildeFactorObjSelfIso :
    (tildeFactor R).obj (ModuleCat.of R R) ≅
      (show (Spec (CommRingCat.of R)).Modules from
        _root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :=
  AlgebraicGeometry.tildeSelf (R := CommRingCat.of R)

/-- **The pullback factor takes the structure sheaf to the structure sheaf**, `(f')^* 𝒪 ≅ 𝒪`. The
morphism is arbitrary: the comparison map always exists and is invertible because
`Opens.map W.hom.base` is final. -/
def pullbackFactorObjUnitIso :
    (pullbackFactor R W).obj
        (show (Spec (CommRingCat.of R)).Modules from
          _root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≅
      (show W.left.Modules from _root_.SheafOfModules.unit W.left.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.pullbackUnitIso W.hom

/-- **The tensor factor takes the structure sheaf to `F`**, `F ⊗ 𝒪 ≅ F`. This is the right unitor
at the spelling `tensorFactor` is written in. -/
def tensorFactorObjUnitIso (F : _root_.SheafOfModules.{u} W.left.ringCatSheaf) :
    (tensorFactor R W F).obj
      (show W.left.Modules from _root_.SheafOfModules.unit W.left.ringCatSheaf) ≅ F :=
  Stacks.SheafOfModules.Invertible.tensorLeftFunctorObjUnitIso W.left.presheaf
    (ringSheafCond W.left) F

/-- **The geometric factor takes the base ring to `F` itself**: `F ⊗ (f')^* R~ ≅ F`. The three
isomorphisms above, composed at the three factors of `M ↦ F ⊗ (f')^* M~`. -/
def geometricFactorFormulaObjSelfIso (F : _root_.SheafOfModules.{u} W.left.ringCatSheaf) :
    (geometricFactorFormula R W F).obj (ModuleCat.of R R) ≅ (show W.left.Modules from F) :=
  (pullbackFactor R W ⋙ tensorFactor R W F).mapIso (tildeFactorObjSelfIso R) ≪≫
    (tensorFactor R W F).mapIso (pullbackFactorObjUnitIso R W) ≪≫
    tensorFactorObjUnitIso R W F

/-- **The geometric factor `T` of the affine case takes the base ring to `F`**, inside the full
subcategory of quasi-coherent modules. The inclusion is fully faithful, so the isomorphism of the
underlying modules suffices. -/
def geometricFactorObjSelfIso
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory) :
    (geometricFactor R W F).obj (ModuleCat.of R R) ≅ F :=
  (ObjectProperty.fullyFaithfulι
      (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf)).preimageIso
    (geometricFactorFormulaObjSelfIso R W F.obj)

section Cohomology

variable (d : ℕ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- **The Eilenberg-Watts module of the affine case is the top-degree cohomology of `F`**:
`Φ(R) ≅ H^d(X', F)`, as `R`-modules. This is `geometricFactorObjSelfIso` carried through the
cohomological tail of `affineTopDegreeFunctor`. -/
def affineTopDegreeFunctorObjSelfIso
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory) :
    (affineTopDegreeFunctor R W d (geometricFactor R W F)).obj (ModuleCat.of R R) ≅
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        ((qcohCohomology W.left d).obj F) :=
  (qcohCohomology W.left d ⋙
    ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).mapIso (geometricFactorObjSelfIso R W F)

/-- **Eilenberg-Watts for the affine case of [Stacks, Tag 0EX3] (b), with its module named.** The
endofunctor `M ↦ H^d(X', F ⊗ (f')^* M~)` of `R`-modules is tensoring with `H^d(X', F)` — which is
the form the source states, where `affineTopDegreeTensorIso` concludes only that it is tensoring
with `Φ(R)`. -/
def affineTopDegreeTensorCohomologyIso
    (F : (_root_.SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj G)) :
    MonoidalCategory.tensorLeft
        ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
          ((qcohCohomology W.left d).obj F)) ≅
      affineTopDegreeFunctor R W d (geometricFactor R W F) :=
  (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapIso
      (affineTopDegreeFunctorObjSelfIso R W d F).symm ≪≫
    affineTopDegreeTensorIso R W F d hvan

end Cohomology

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable (S : TopDegreeBaseChangeSituation.{u}) [IsAffine S.Y']
  (F : (SheafOfModules.isQuasicoherent (S.affineBaseOver).left.ringCatSheaf).FullSubcategory)

/-- **`H^d(X', F)`, as a module over the ring `Γ(Y', ⊤)` of the affine base.** This is the
`H^d(X', F')` of [Stacks, Tag 0EX3] (b), read as an `R'`-module through the structure morphism. -/
abbrev topDegreeCohomology : ModuleCat.{u} S.affineBaseRing :=
  (ModuleCat.restrictScalars
      (algebraMap S.affineBaseRing Γ((S.affineBaseOver).left, ⊤))).obj
    ((qcohCohomology (S.affineBaseOver).left S.d).obj F)

/-- **The Eilenberg-Watts module of the situation is `H^d(X', F)`**, unconditionally:
`Φ(Γ(Y', ⊤)) ≅ H^d(X', F)`. -/
def topDegreeFunctorObjSelfIso :
    (S.topDegreeFunctor F).obj (ModuleCat.of S.affineBaseRing S.affineBaseRing) ≅
      S.topDegreeCohomology F :=
  affineTopDegreeFunctorObjSelfIso S.affineBaseRing S.affineBaseOver S.d F

/-- **The affine case of [Stacks, Tag 0EX3] (b) in the source's own form.** For a top-degree
base-change situation whose base `Y'` is affine and a quasi-coherent module `F` on `X'`, the
endofunctor `M ↦ H^d(X', F ⊗ (f')^* M~)` of `Γ(Y', ⊤)`-modules **is** tensoring with
`H^d(X', F)`.

This strengthens `topDegreeTensorIso`, which names the module only as `Φ(Γ(Y', ⊤))`; the two are
interchanged by `topDegreeFunctorObjSelfIso`. -/
@[stacks 0EX3 "(b) over an affine base, as an isomorphism of functors"]
def topDegreeTensorCohomologyIso :
    MonoidalCategory.tensorLeft (S.topDegreeCohomology F) ≅ S.topDegreeFunctor F :=
  (MonoidalCategory.curriedTensor (ModuleCat.{u} S.affineBaseRing)).mapIso
      (S.topDegreeFunctorObjSelfIso F).symm ≪≫
    S.topDegreeTensorIso F

/-- **The affine case of [Stacks, Tag 0EX3] (b), module by module, in the source's own form**: a
`Γ(Y', ⊤)`-linear equivalence `H^d(X', F) ⊗_{R'} M ≃ₗ H^d(X', F ⊗ (f')^* M~)`, natural in `M` by
`topDegreeTensorCohomologyIso`. This is the displayed equation of the source. -/
@[stacks 0EX3 "(b) over an affine base, the displayed tensor identity"]
def topDegreeTensorCohomologyLinearEquiv (M : ModuleCat.{u} S.affineBaseRing) :
    (S.topDegreeCohomology F) ⊗[S.affineBaseRing] M ≃ₗ[S.affineBaseRing]
      (S.topDegreeFunctor F).obj M :=
  (TensorProduct.congr (S.topDegreeFunctorObjSelfIso F).toLinearEquiv
    (LinearEquiv.refl S.affineBaseRing M)).symm.trans (S.topDegreeTensorLinearEquiv F M)

end Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

noncomputable section

variable (S : TopDegreeBaseChangeSituation.{u}) (V : S.Y'.Opens)

/-- **A top-degree base-change situation restricted to an open of its base.** The morphism `f`,
the degree `d` and the finiteness and vanishing hypotheses are untouched; only the cartesian
square is replaced, by the square

```
f'⁻¹(V) --ι ≫ g'--> X
   |f' ∣_ V          |f
   V ----ι ≫ g-----> Y
```

This is again cartesian, being the horizontal pasting of
`AlgebraicGeometry.isPullback_morphismRestrict` with the situation's own square: `f'⁻¹(V)` is
both `X' ×_{Y'} V` and therefore `X ×_Y V`. So no hypothesis is needed on `V`, and nothing about
the situation has to be reproved — in particular the base `Y'` of the original situation is
arbitrary. -/
def restrictBase : TopDegreeBaseChangeSituation.{u} where
  X := S.X
  Y := S.Y
  f := S.f
  d := S.d
  isCompact_X := S.isCompact_X
  isQuasiSeparated_X := S.isQuasiSeparated_X
  isCompact_Y := S.isCompact_Y
  isQuasiSeparated_Y := S.isQuasiSeparated_Y
  vanishes_above := S.vanishes_above
  X' := (S.f' ⁻¹ᵁ V : Scheme)
  Y' := (V : Scheme)
  g' := (S.f' ⁻¹ᵁ V).ι ≫ S.g'
  f' := S.f' ∣_ V
  g := V.ι ≫ S.g
  isPullback := (isPullback_morphismRestrict S.f' V).flip.paste_horiz S.isPullback

/-- The restricted situation has the same morphism `f`. -/
@[simp]
theorem restrictBase_f : (S.restrictBase V).f = S.f := rfl

/-- The restricted situation has the same degree. -/
@[simp]
theorem restrictBase_d : (S.restrictBase V).d = S.d := rfl

/-- The base of the restricted situation is `V`. -/
theorem restrictBase_Y' : (S.restrictBase V).Y' = (V : Scheme) := rfl

/-- The source of the restricted situation is `f'⁻¹(V)`. -/
theorem restrictBase_X' : (S.restrictBase V).X' = (S.f' ⁻¹ᵁ V : Scheme) := rfl

/-- The base-changed morphism of the restricted situation is `f' ∣_ V`. -/
@[simp]
theorem restrictBase_f' : (S.restrictBase V).f' = S.f' ∣_ V := rfl

/-- **An affine open of the base makes the restricted situation one with affine base**, which is
what the affine case of conclusion (b) consumes. -/
instance isAffine_restrictBase_Y' [IsAffine (V : Scheme)] : IsAffine (S.restrictBase V).Y' :=
  ‹IsAffine (V : Scheme)›

variable [IsAffine (V : Scheme)]
  (F : (SheafOfModules.isQuasicoherent
    ((S.restrictBase V).affineBaseOver).left.ringCatSheaf).FullSubcategory)

/-- **[Stacks, Tag 0EX3] (b) over an arbitrary base, on each affine open of the base.** For a
top-degree base-change situation with **no hypothesis on its base `Y'`**, an affine open `V` of
`Y'` and a quasi-coherent module `F` on `f'⁻¹(V)`, the endofunctor
`M ↦ H^d(f'⁻¹(V), F ⊗ (f' ∣_ V)^* M~)` of `Γ(V, ⊤)`-modules **is** tensoring with
`H^d(f'⁻¹(V), F)`.

This is `topDegreeTensorCohomologyIso` applied to `restrictBase`, whose base is `V`; the
affineness hypothesis that declaration carries is therefore discharged by the affineness of the
open and not assumed of `Y'`. The affine opens of `Y'` cover it
(`AlgebraicGeometry.iSup_affineOpens_eq_top`), so this is the conclusion at every point of an
arbitrary base — it is the source's own reduction, performed over an arbitrary base rather than
assumed of it.

The reading of conclusion (b) as a single canonical map of sheaves on `Y'` is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_higherDirectImageTensorMap`, which this
statement names the tensor factor of.
-/
def restrictBaseTopDegreeTensorCohomologyIso :
    MonoidalCategory.tensorLeft ((S.restrictBase V).topDegreeCohomology F) ≅
      (S.restrictBase V).topDegreeFunctor F :=
  (S.restrictBase V).topDegreeTensorCohomologyIso F

/-- **The displayed tensor identity of [Stacks, Tag 0EX3] (b) over an arbitrary base, on each
affine open of the base**: a `Γ(V, ⊤)`-linear equivalence
`H^d(f'⁻¹(V), F) ⊗_{Γ(V, ⊤)} M ≃ₗ H^d(f'⁻¹(V), F ⊗ (f' ∣_ V)^* M~)`, natural in `M` by
`restrictBaseTopDegreeTensorCohomologyIso`. The base `Y'` of the situation is arbitrary; only the
open `V` is affine. -/
def restrictBaseTopDegreeTensorCohomologyLinearEquiv
    (M : ModuleCat.{u} (S.restrictBase V).affineBaseRing) :
    ((S.restrictBase V).topDegreeCohomology F) ⊗[(S.restrictBase V).affineBaseRing] M
        ≃ₗ[(S.restrictBase V).affineBaseRing]
      ((S.restrictBase V).topDegreeFunctor F).obj M :=
  (S.restrictBase V).topDegreeTensorCohomologyLinearEquiv F M

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

end

end
