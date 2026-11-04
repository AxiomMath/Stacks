module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal

/-!
# A `D_QCoh` object on an affine algebraic space is `𝒪_X ⊗_A C`

Let `X` be an algebraic space with an isomorphism `g : X ≅ h_T` to the algebraic space
represented by an object `T` of the big fppf site with scheme `Spec A`.  This file puts an
*arbitrary* object of `D_QCoh(𝒪_X)` into the image of `𝒪_X ⊗_A -`, in the shape
`Q(T_ψ(C))` that the point-tensor engine of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomUnitColimPointTensorKFlat.lean`
consumes:  `T_ψ` is `AlgebraicGeometry.Space.spacesEtaleModelPointTensor`, the inverse image
along `X ⟶ (pt, A)` read on the spaces-étale model, and `ψ` the ring isomorphism
`A ≅ Γ(X, 𝒪_X)` of `AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`.

This is the quasi-coherent counterpart of
`AlgebraicGeometry.Space.exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso`, whose
crossing step — `AlgebraicGeometry.Space.pointTensorIsoRepresentedTildeOfIso` together with
`CategoryTheory.Functor.mapHomologicalComplexCompIso` — uses neither finiteness nor
projectivity and is reused verbatim.  What changes is the model produced on the represented
space:  for a perfect object it is a bounded complex of finite projective modules, and here it
is an arbitrary complex of `A`-modules, which is all the point-tensor engine needs — that engine
resolves the complex by a sequential colimit of bounded above complexes of flat modules and asks
nothing of the complex itself.

## The chain

* `E` has quasi-coherent cohomology on the small étale site of `X`, hence so does its pullback
  along `g⁻¹ : h_T ⟶ X`, an étale pullback being exact and preserving quasi-coherence
  (`AlgebraicGeometry.Space.derivedQuasicoherentPullback_iff` at
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`).
* On `h_T` the comparison of Stacks 071Q carries it to an object of `D_QCoh(𝒪_{Spec A})`
  (`AlgebraicGeometry.Space.exists_representedDerivedAssociatedModule_iso`), and Stacks 06Z0
  presents that as `M̃` for an object `M` of `D(A)`
  (`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`).  Replacing `M` by a
  representing complex gives `E ≅ Q((ε^* ∘ ~)(C))` on `h_T`.
* The crossing step of the perfect case then rewrites `g^*(ε^*(C̃))` as `e_X(T_ψ(C))` and
  descends the isomorphism through the derived equivalence
  `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`.

## Main results

* `AlgebraicGeometry.Space.exists_representedTilde_iso_of_isQuasicoherentOnSite`: an object of
  `D_QCoh(𝒪_{h_{Spec A}})` is `Q((ε^* ∘ ~)(C))` for a complex `C` of `A`-modules.
* `AlgebraicGeometry.Space.exists_pointTensor_iso_of_isQuasicoherentOnSite_of_iso`: **an object
  of `D_QCoh(𝒪_X)`, read on the spaces-étale model of `X ≅ h_{Spec A}`, is `Q(T_ψ(C))`** for a
  complex `C` of `A`-modules.
* `AlgebraicGeometry.Space.exists_pointTensor_iso_of_isQuasicoherentOnSite`: the same
  isomorphism stated on the small étale site of `X`, which is where the quasi-coherence
  hypothesis of Stacks 09RI lives.

## Implementation notes

The quasi-coherence hypothesis is stated on the `𝒪_X`-modules — on the image of the object under
`AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv` — and not on the spaces-étale model's own
ringed site.  That is the side the hypothesis of Stacks 09RI is given on, and it is the idiom of
`AlgebraicGeometry.Space.modelQcohDerived`, which is likewise defined as the inverse image of
`D_QCoh(𝒪_X)` along the derived equivalence rather than intrinsically on the model.  No transport
of quasi-coherence through `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` is needed, and
none is proved here.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S)

/-- **An object of `D_QCoh(𝒪_{h_{Spec A}})` is the complex of associated sheaves of a complex of
`A`-modules.**  The comparison of Stacks 071Q carries it to `D_QCoh(𝒪_{Spec A})`, Stacks 06Z0
presents that as `M̃` for an object `M` of `D(A)`, and a representing complex of `M` gives the
statement.

Nothing is assumed beyond quasi-coherence of the cohomology sheaves; this is the unbounded
counterpart of
`AlgebraicGeometry.Space.exists_finiteProjective_representedTilde_iso_of_isPerfect`. -/
theorem exists_representedTilde_iso_of_isQuasicoherentOnSite
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)) n).obj E).IsQuasicoherentOnSite) :
    ∃ C : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj
        (((representedTilde B S hS hA p).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≅
          E) := by
  let T := BigFppfOver.mk B S hS hA p
  obtain ⟨N, hNq, ⟨eN⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T E hE
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory
    (CommRingCat.of A) N hNq
  let ε : (Spec (CommRingCat.of A)).Modules ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  have : (tilde.functor (CommRingCat.of A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  have : ε.Additive := additive_representedAssociatedModule B S hS T _
  have : PreservesFiniteColimits ε :=
    preservesFiniteColimits_representedAssociatedModule B S hS T _
  have : PreservesFiniteLimits ε := preservesFiniteLimits_representedAssociatedModule B S hS T _
  refine ⟨DerivedCategory.Q.objPreimage M, ⟨?_⟩⟩
  exact DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (representedTilde B S hS hA p))
        (ComplexShape.up ℤ)).app _).symm ≪≫
    (ε.mapDerivedCategoryFactors.app _).symm ≪≫
    ε.mapDerivedCategory.mapIso
      ((((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors).app _).symm ≪≫
        (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso
          (DerivedCategory.Q.objObjPreimageIso M) ≪≫ eM) ≪≫ eN

variable {X : AlgebraicSpaces B S hS}
  (g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩)

/-- **An object of `D_QCoh(𝒪_X)` on the spaces-étale model of `X ≅ h_{Spec A}` is `𝒪_X ⊗_A C`**
for a complex `C` of `A`-modules, with `ψ : A ≅ Γ(X, 𝒪_X)` the ring isomorphism of
`AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`.

The quasi-coherence hypothesis is on the `𝒪_X`-modules, that is on the image of `E` under the
derived equivalence `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`.

Compared with `exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso` the complex carries
no boundedness, finiteness or projectivity — and the point-tensor engine of
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit` asks for none. -/
theorem exists_pointTensor_iso_of_isQuasicoherentOnSite_of_iso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS X).O)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
      ((spacesEtaleModelDerivedEquiv B S hS X).functor.obj E)).IsQuasicoherentOnSite) :
    ∃ C : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (E ≅ DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) := by
  let eX := spacesEtaleModelModulesEquiv B S hS X
  let Eq := etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g
  have : PreservesFiniteLimits eX.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ eX.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits eX.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      eX.toAdjunction.leftAdjoint_preservesColimits
  have : eX.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits Eq.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ Eq.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits Eq.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      Eq.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteLimits Eq.inverse := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ Eq.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits Eq.inverse :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      Eq.symm.toAdjunction.leftAdjoint_preservesColimits
  have : Eq.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : Eq.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let K := eX.functor.mapDerivedCategory.obj E
  have hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) n).obj K).IsQuasicoherentOnSite := hE
  have hK' := (derivedQuasicoherentPullback_iff B S hS g.inv
    (isEtale_hom_of_iso B S hS g.symm) K).2 fun n =>
      isQuasicoherentOnSite_etaleModulePullback B S hS _ _ _ (hK n)
  obtain ⟨C, ⟨eC⟩⟩ :=
    exists_representedTilde_iso_of_isQuasicoherentOnSite B S hS hA p _ hK'
  let DE := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence Eq.functor Eq.inverse Eq.unitIso
    Eq.counitIso
  let T := spacesEtaleModelPointTensor B S hS (representedTildeOfIsoPointRingHom B S hS hA p g)
  let i₁ : K ≅ Eq.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
      (((representedTilde B S hS hA p).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
    (DE.counitIso.app K).symm ≪≫ Eq.functor.mapDerivedCategory.mapIso eC.symm
  let i₂ : Eq.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
      (((representedTilde B S hS hA p).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) ≅
      eX.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
    Eq.functor.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        (((Functor.mapHomologicalComplexCompIso (F := representedTilde B S hS hA p)
          (G := Eq.functor) (H := representedTildeOfIso B S hS hA p g) (Iso.refl _)
            (ComplexShape.up ℤ)).app C) ≪≫
          ((Functor.mapHomologicalComplexCompIso (F := T) (G := eX.functor)
            (H := representedTildeOfIso B S hS hA p g)
              (pointTensorIsoRepresentedTildeOfIso B S hS hA p g)
                (ComplexShape.up ℤ)).app C).symm) ≪≫
      (eX.functor.mapDerivedCategoryFactors.app _).symm
  exact ⟨C, ⟨(spacesEtaleModelDerivedEquiv B S hS X).fullyFaithfulFunctor.preimageIso
    (i₁ ≪≫ i₂)⟩⟩

/-- **An object of `D_QCoh(𝒪_X)` is `𝒪_X ⊗_A C`** for `X ≅ h_{Spec A}` and a complex `C` of
`A`-modules, stated on the small étale site of `X`: this is
`exists_pointTensor_iso_of_isQuasicoherentOnSite_of_iso` read through the derived equivalence
`AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`, which is the side the quasi-coherence
hypothesis of Stacks 09RI is given on. -/
theorem exists_pointTensor_iso_of_isQuasicoherentOnSite
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
      K).IsQuasicoherentOnSite) :
    ∃ C : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (K ≅ (spacesEtaleModelDerivedEquiv B S hS X).functor.obj
        (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C))) := by
  let e := spacesEtaleModelDerivedEquiv B S hS X
  obtain ⟨C, ⟨eC⟩⟩ := exists_pointTensor_iso_of_isQuasicoherentOnSite_of_iso B S hS hA p g
    (e.inverse.obj K) fun n => (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).mapIso
        (e.counitIso.app K)).symm (hK n)
  exact ⟨C, ⟨(e.counitIso.app K).symm ≪≫ e.functor.mapIso eC⟩⟩

/-- **An object of `D_QCoh(𝒪_V)` on an affine algebraic space `V` is `𝒪_V ⊗_A C`** for a ring `A`
with `V ≅ h_{Spec A}` and a complex `C` of `A`-modules.  The presentation of `V` is produced here
rather than assumed:  an affine algebraic space is isomorphic to the one represented by an object
of the site with affine underlying scheme, and that object is isomorphic to `Spec` of its global
functions, which the site contains
(`AlgebraicGeometry.Space.exists_iso_mk_spec`).

This is the form the affine leaf of Stacks 09RI needs — the hypothesis there is `IsAffineSpace`
on the base of the base-changed system together with quasi-coherence of the second argument. -/
theorem exists_pointTensor_iso_of_isQuasicoherentOnSite_of_isAffineSpace
    (hX : IsAffineSpace B S hS X.1) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
      K).IsQuasicoherentOnSite) :
    ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (CommRingCat.of A)))
      (p : Spec (CommRingCat.of A) ⟶ S)
      (g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩)
      (C : CochainComplex (ModuleCat.{u} A) ℤ),
      Nonempty (K ≅ (spacesEtaleModelDerivedEquiv B S hS X).functor.obj
        (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C))) := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := hX
  obtain ⟨A, _, hA, p, ⟨eA⟩⟩ := exists_iso_mk_spec B S hS T hT
  let g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (eT ≪≫ yoneda.mapIso eA)
  obtain ⟨C, hC⟩ := exists_pointTensor_iso_of_isQuasicoherentOnSite B S hS hA p g K hK
  exact ⟨A, _, hA, p, g, C, hC⟩

end AlgebraicGeometry.Space

end
