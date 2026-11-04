module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxTotal
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham Künneth isomorphism in each degree

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `W = X ×_S Y`. In degree `n` the
total complex `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`, `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotal`, is the
biproduct of the `Ω^p_{X/S} ⊠ Ω^q_{Y/S}` with `p + q = n`, and that biproduct is canonically
isomorphic to `Ω^n_{W/S}`:

`⨁_{p + q = n} (Ω^p_{X/S} ⊠ Ω^q_{Y/S}) ≅ Ω^n_{W/S}`.

The isomorphism is the composite of three known ones. By [Stacks, Tag 01V1] the sheaf of
relative differentials of the fibre product splits, `pr₁^*Ω_{X/S} ⊕ pr₂^*Ω_{Y/S} ≅ Ω_{W/S}`; by
the Künneth decomposition of an exterior power of a direct sum,
`⨁_{p + q = n} (⋀ᵖ pr₁^*Ω_{X/S} ⊗ ⋀^q pr₂^*Ω_{Y/S}) ≅ ⋀ⁿ(pr₁^*Ω_{X/S} ⊕ pr₂^*Ω_{Y/S})`; and by
[Stacks, Tag 01CI] each summand is the external tensor product
`Ω^p_{X/S} ⊠ Ω^q_{Y/S} = pr₁^*(⋀ᵖΩ_{X/S}) ⊗ pr₂^*(⋀^qΩ_{Y/S})`.

**Compatibility with the differentials is not proved here**: this file gives the isomorphism in
each degree only, not a morphism of complexes.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxSplitIso`: Tag 01V1 as an isomorphism
  `pr₁^*Ω_{X/S} ⊞ pr₂^*Ω_{Y/S} ≅ Ω_{W/S}`.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalXIso`: the degree-`n` term of the total complex is
  the biproduct of the `Ω^p_{X/S} ⊠ Ω^q_{Y/S}` with `p + q = n`.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso`: the underlying isomorphism of sheaves of
  modules `⨁_{p + q = n} (Ω^p_{X/S} ⊠ Ω^q_{Y/S}) ≅ Ω^n_{W/S}`.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalDegreeIso`: **the degreewise de Rham Künneth
  isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})^n ≅ Ω^n_{W/S}`** of [Stacks, Tag 0FMA].

## Main results

* `AlgebraicGeometry.Scheme.Hom.ιTotal_comp_deRhamBoxTotalDegreeIso_hom`: on the `(p, q)`
  summand of the total complex the isomorphism is the inclusion of the `(p, q)` summand of the
  biproduct followed by the isomorphism of sheaves of modules, read as a differential operator of
  order zero.

## Implementation notes

The degree-`n` term of a total complex is the coproduct of the summands over the subtype
`{(p, q) | p + q = n}`; the category of finite-order differential operators has only finite
biproducts, so that coproduct is exhibited through the explicit bicone
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.bicone`, whose point is the biproduct of
the underlying sheaves of modules. The whole construction is then a single isomorphism of sheaves
of modules read as an operator of order zero,
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.isoOfModuleIso`.

The Künneth decomposition of an exterior power is stated over a sheaf of commutative rings on a
topological space, in the `CategoryTheory.Sheaf.toRingCat` spelling of the sheaf of rings, and
`AlgebraicGeometry.Scheme.Modules` is a semireducible definition, so instance search finds neither
the biproducts nor the coproducts of that category at that spelling. The two instances are
therefore named here, at the `toRingCat` spelling, and the binary one is passed explicitly.

## References

* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The category of sheaves of modules on a scheme has binary biproducts, named at the
`CategoryTheory.Sheaf.toRingCat` spelling of the structure sheaf. -/
theorem hasBinaryBiproducts_sheafOfModules_toRingCat (W : Scheme.{u}) :
    HasBinaryBiproducts (SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥W) W.sheaf)) :=
  inferInstanceAs (HasBinaryBiproducts W.Modules)

/-- Two sheaves of modules on a scheme have a biproduct, named at the
`CategoryTheory.Sheaf.toRingCat` spelling of the structure sheaf. -/
theorem hasBinaryBiproduct_sheafOfModules_toRingCat (W : Scheme.{u})
    (A B : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥W) W.sheaf)) :
    HasBinaryBiproduct A B :=
  (hasBinaryBiproducts_sheafOfModules_toRingCat W).has_binary_biproduct A B

/-- The category of sheaves of modules on a scheme has colimits, named at the
`CategoryTheory.Sheaf.toRingCat` spelling of the structure sheaf. -/
theorem hasColimits_sheafOfModules_toRingCat (W : Scheme.{u}) :
    HasColimits (SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥W) W.sheaf)) :=
  inferInstanceAs (HasColimits W.Modules)

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace FiniteOrderDifferentialOperatorCategory

/-- **An isomorphism of the underlying sheaves of modules is an isomorphism of the category of
finite-order differential operators**: both directions are operators of order zero, and reading a
morphism of modules as such an operator is compatible with composition and identities. -/
noncomputable def isoOfModuleIso {X S : Scheme.{u}} {a : X ⟶ S}
    {F G : FiniteOrderDifferentialOperatorCategory a} (e : F.module ≅ G.module) : F ≅ G where
  hom := homOrderZeroAddMonoidHom F G e.hom
  inv := homOrderZeroAddMonoidHom G F e.inv
  hom_inv_id := by
    rw [homOrderZeroAddMonoidHom_comp, e.hom_inv_id, homOrderZeroAddMonoidHom_id]
  inv_hom_id := by
    rw [homOrderZeroAddMonoidHom_comp, e.inv_hom_id, homOrderZeroAddMonoidHom_id]

end FiniteOrderDifferentialOperatorCategory

namespace Scheme.Hom

open FiniteOrderDifferentialOperatorCategory

/-- The index type of the degree-`n` term of a total complex of `ℕ`-indexed cochain complexes:
the pairs `(p, q)` of natural numbers with `p + q = n`. -/
abbrev deRhamBoxIndex (n : ℕ) : Type :=
  ↥(ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) ⁻¹' {n})

/-- The antidiagonal of `n` in `ℕ × ℕ` is finite. -/
noncomputable instance fintypeDeRhamBoxIndex (n : ℕ) : Fintype (deRhamBoxIndex n) :=
  Set.Finite.fintype
    (Set.Finite.ofFinset (Finset.antidiagonal n) (fun _ => Finset.mem_antidiagonal))

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The family of summands of the degree-`n` term of `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`: the term of
the double complex in degree `(p, q)` for each pair with `p + q = n`. -/
noncomputable abbrev deRhamBoxSummand (n : ℕ) : deRhamBoxIndex n →
    FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a) :=
  (deRhamBoxDoubleComplex a b).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) n

/-- The summand of index `(p, q)` is `Ω^p_{X/S} ⊠ Ω^q_{Y/S}`. -/
theorem deRhamBoxSummand_eq (n : ℕ) (j : deRhamBoxIndex n) :
    deRhamBoxSummand a b n j =
      boxProductObj (deRhamDiffOpTerm a j.1.1) (deRhamDiffOpTerm b j.1.2) :=
  rfl

/-- **The degree-`n` term of `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})` is the biproduct of the
`Ω^p_{X/S} ⊠ Ω^q_{Y/S}` with `p + q = n`.** The category of finite-order differential operators
has finite biproducts, with the biproduct of the underlying quasi-coherent modules and the
inclusions and projections read as operators of order zero, and a finite biproduct is a
coproduct. -/
noncomputable def deRhamBoxTotalXIso (n : ℕ) :
    biproductObj (deRhamBoxSummand a b n) ≅ (deRhamBoxTotal a b).X n :=
  GradedObject.CofanMapObjFun.iso (c := (bicone (deRhamBoxSummand a b n)).toCocone)
    (isBilimitOfTotal _ (bicone_total (deRhamBoxSummand a b n))).isColimit

/-- The inclusion of the summand of index `(p, q)` into the degree-`n` term of the total
complex. -/
theorem bicone_ι_comp_deRhamBoxTotalXIso_hom (n : ℕ) (j : deRhamBoxIndex n) :
    (bicone (deRhamBoxSummand a b n)).ι j ≫ (deRhamBoxTotalXIso a b n).hom =
      (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) j.1.1 j.1.2 n j.2 :=
  GradedObject.CofanMapObjFun.inj_iso_hom (c := (bicone (deRhamBoxSummand a b n)).toCocone)
    (isBilimitOfTotal _ (bicone_total (deRhamBoxSummand a b n))).isColimit j.1 j.2

/-- **Stacks Project, Tag 01V1, as an isomorphism.** The two canonical maps of Tag 01UV exhibit
the sheaf of relative differentials of `X ×_S Y / S` as the direct sum of the pullbacks of
`Ω_{X/S}` and of `Ω_{Y/S}`. -/
noncomputable def deRhamBoxSplitIso :
    ((Scheme.Modules.pullback (pullback.fst a b)).obj (relativeDifferentials a) ⊞
        (Scheme.Modules.pullback (pullback.snd a b)).obj (relativeDifferentials b)) ≅
      relativeDifferentials (pullback.fst a b ≫ a) :=
  letI := isIso_biprodDesc_relativeDifferentialsMap (pullback.fst a b) (pullback.snd a b) a b
    (IsPullback.of_hasPullback a b)
  asIso (biprod.desc
    (relativeDifferentialsMap (pullback.fst a b) a (pullback.fst a b ≫ a) (𝟙 S)
      (Category.comp_id (pullback.fst a b ≫ a)).symm)
    (relativeDifferentialsMap (pullback.snd a b) b (pullback.fst a b ≫ a) (𝟙 S)
      ((IsPullback.of_hasPullback a b).w.symm.trans
        (Category.comp_id (pullback.fst a b ≫ a)).symm)))

/-- The chosen tensor, exterior and symmetric algebras of `pr₁^*Ω_{X/S}`. -/
noncomputable abbrev deRhamBoxAlgebrasLeft := SheafOfModules.algebras _
  ((Scheme.Modules.pullback (pullback.fst a b)).obj (relativeDifferentials a))

/-- The chosen tensor, exterior and symmetric algebras of `pr₂^*Ω_{Y/S}`. -/
noncomputable abbrev deRhamBoxAlgebrasRight := SheafOfModules.algebras _
  ((Scheme.Modules.pullback (pullback.snd a b)).obj (relativeDifferentials b))

/-- The direct sum `pr₁^*Ω_{X/S} ⊞ pr₂^*Ω_{Y/S}` of the two pullbacks of the sheaves of relative
differentials to the fibre product. -/
noncomputable abbrev deRhamBoxSplitSum : (pullback a b).Modules :=
  (Scheme.Modules.pullback (pullback.fst a b)).obj (relativeDifferentials a) ⊞
    (Scheme.Modules.pullback (pullback.snd a b)).obj (relativeDifferentials b)

/-- The chosen tensor, exterior and symmetric algebras of
`pr₁^*Ω_{X/S} ⊞ pr₂^*Ω_{Y/S}`. -/
noncomputable abbrev deRhamBoxAlgebrasSum :=
  SheafOfModules.algebras _ (deRhamBoxSplitSum a b)

/-- **The `(p, q)` summand of the Künneth decomposition of an exterior power is the external
tensor product `Ω^p_{X/S} ⊠ Ω^q_{Y/S}`**: by [Stacks, Tag 01CI] the exterior power of a
pullback is the pullback of the exterior power, in each of the two factors. -/
noncomputable def deRhamBoxSummandIso (n : ℕ) (j : deRhamBoxIndex n) :
    SheafOfModules.exteriorPowerProdSummand (deRhamBoxAlgebrasLeft a b)
        (deRhamBoxAlgebrasRight a b) n (ULift.up j) ≅
      (deRhamBoxSummand a b n j).module :=
  Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
    (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst a b) (relativeDifferentials a)
      (j.1.1 : ℤ)).symm
    (Scheme.Modules.exteriorPowerPullbackIso (pullback.snd a b) (relativeDifferentials b)
      (j.1.2 : ℤ)).symm

/-- **The de Rham Künneth isomorphism in degree `n`, on the underlying sheaves of modules:**
`⨁_{p + q = n} (Ω^p_{X/S} ⊠ Ω^q_{Y/S}) ≅ Ω^n_{X ×_S Y / S}`. The biproduct is a coproduct, its
summands are the summands of the Künneth decomposition of an exterior power of a direct sum by
[Stacks, Tag 01CI], that decomposition identifies the coproduct with
`⋀ⁿ(pr₁^*Ω_{X/S} ⊞ pr₂^*Ω_{Y/S})`, and [Stacks, Tag 01V1] identifies the latter with
`⋀ⁿΩ_{X ×_S Y / S}`. -/
noncomputable def deRhamBoxModuleIso (n : ℕ) :
    (biproductObj (deRhamBoxSummand a b n)).module ≅
      relativeDifferentialForms (pullback.fst a b ≫ a) (n : ℤ) :=
  biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv (g := SheafOfModules.exteriorPowerProdSummand
        (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b) n)
      (Equiv.ulift (α := deRhamBoxIndex n)).symm (fun j => deRhamBoxSummandIso a b n j) ≪≫
    @SheafOfModules.exteriorPowerBiprodIso _ _ _ _
      (hasBinaryBiproduct_sheafOfModules_toRingCat (pullback a b) _ _)
      (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b) (deRhamBoxAlgebrasSum a b) n ≪≫
    (Scheme.Modules.exteriorPowerFunctor (pullback a b) (n : ℤ)).mapIso (deRhamBoxSplitIso a b)

/-- The degreewise Künneth isomorphism read on the biproduct of the summands: the isomorphism of
sheaves of modules `AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso`, as a differential operator
of order zero. -/
noncomputable def deRhamBoxBiproductIso (n : ℕ) :
    biproductObj (deRhamBoxSummand a b n) ≅
      (deRhamDiffOpComplex (pullback.fst a b ≫ a)).X n :=
  isoOfModuleIso (deRhamBoxModuleIso a b n)

/-- **Stacks Project, Tag 0FMA, the degreewise isomorphism.** In each degree `n` the total
complex `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})` of the box product of the two relative de Rham complexes is
canonically isomorphic to `Ω^n_{X ×_S Y / S}`, as objects of the category of finite-order
differential operators on `X ×_S Y / S`.

**Compatibility with the differentials is not included**: this is an isomorphism of the terms in
each fixed degree, not a morphism of complexes. -/
@[stacks 0FMA "the degreewise isomorphism: in each degree `n` an isomorphism \
`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})^n ≅ Ω^n_{X ×_S Y/S}`. NOT compatibility with the differentials, \
and so NOT the isomorphism of complexes"]
noncomputable def deRhamBoxTotalDegreeIso (n : ℕ) :
    (deRhamBoxTotal a b).X n ≅ (deRhamDiffOpComplex (pullback.fst a b ≫ a)).X n :=
  (deRhamBoxTotalXIso a b n).symm ≪≫ deRhamBoxBiproductIso a b n

/-- **The degreewise Künneth isomorphism on the `(p, q)` summand of the total complex**: it is
the inclusion of the `(p, q)` summand of the biproduct of sheaves of modules followed by
`AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso`, read as a differential operator of order
zero. -/
theorem ιTotal_comp_deRhamBoxTotalDegreeIso_hom (n : ℕ) (j : deRhamBoxIndex n) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) j.1.1 j.1.2 n j.2 ≫
        (deRhamBoxTotalDegreeIso a b n).hom =
      homOrderZeroAddMonoidHom _ _
        (biproduct.ι (fun k => (deRhamBoxSummand a b n k).module) j ≫
          (deRhamBoxModuleIso a b n).hom) :=
  ((Category.assoc
        ((deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) j.1.1 j.1.2 n j.2)
        (deRhamBoxTotalXIso a b n).inv (deRhamBoxBiproductIso a b n).hom).symm.trans
      (congrArg (fun z => z ≫ (deRhamBoxBiproductIso a b n).hom)
        (GradedObject.CofanMapObjFun.ιMapObj_iso_inv
          (c := (bicone (deRhamBoxSummand a b n)).toCocone)
          (isBilimitOfTotal _ (bicone_total (deRhamBoxSummand a b n))).isColimit
          j.1 j.2))).trans
    (homOrderZeroAddMonoidHom_comp _ _)

end Scheme.Hom

end AlgebraicGeometry

end
