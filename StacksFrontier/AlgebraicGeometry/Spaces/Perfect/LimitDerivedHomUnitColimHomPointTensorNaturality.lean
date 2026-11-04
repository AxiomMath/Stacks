module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimPointTensorKFlat

/-!
# The derived pullback of `𝒪_X ⊗_A C` on a K-flat point tensor, and its naturality in `C`

Let `X` be an algebraic space, `ψ : A ⟶ Γ(X, 𝒪_X)` a ring map and `T_ψ : M ↦ 𝒪_X ⊗_A M` the
inverse image along `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)`.

`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomUnitColimPointTensorKFlat.lean`
produces the isomorphism `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` for `C` a sequential colimit of
bounded above complexes of flat `A`-modules, with no hypothesis on `C` itself.  What that file
does not give is **naturality in `C`**, and naturality is what a Hom-group computation needs: a
morphism `Q(T_ψ(C)) ⟶ Q(T_ψ(C'))` is only transported to the stages by a *square*, not by the
two isomorphisms separately.

This file supplies it.  Both the hypothesis of the colimit computation and the hypothesis of the
bounded-above-flat computation
(`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfFlat`) are instances of one condition —
that `T_ψ(C)` is K-flat with flat terms, the hypothesis of Stacks 06YY — so the isomorphism is
restated at that condition, once, and its naturality proved there.  A single square then has a
bounded above complex of flat modules on one side and an arbitrary colimit-presented complex on
the other, which is the shape the affine leaf of Stacks 09RI meets: its first argument is the
structure sheaf `𝒪_X = T_ψ(A)`, a one-term complex of a flat module, and its second argument is
an arbitrary object of `D_QCoh(𝒪_X)`, which
`AlgebraicGeometry.Space.exists_pointTensor_iso_of_isQuasicoherentOnSite_of_isAffineSpace`
presents as `T_ψ(C)` for an *unbounded* `C`.

`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat` agrees with
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit` on the nose, by
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit_eq`: the colimit computation is
this one at the K-flatness proof it establishes, the two Prop-valued hypotheses being
irrelevant.  It does **not** agree with
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfFlat`, which is built from
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfIsIsoComparison` rather
than from `Stacks.Sheaves.DerivedPullback.flatPullbackIso` and carries an extra
`CategoryTheory.Functor.mapHomotopyCategoryFactors` factor; no identification of the two is
claimed or proved here.  A consumer that wants one square covering both arguments should use
`derivedPullbackPointTensorIsoOfKFlat` on both sides, which
`AlgebraicGeometry.Space.kFlat_spacesEtaleModelPointTensor_of_isStrictlyLE` makes possible for a
bounded above complex of flat modules.

## Main results

* `AlgebraicGeometry.Space.kFlat_spacesEtaleModelPointTensor_of_isStrictlyLE`: `T_ψ(C)` is
  K-flat for `C` a bounded above complex of flat `A`-modules (Stacks 06YQ).
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat`:
  `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` whenever `T_ψ(C)` is K-flat with flat terms.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit_eq`: the colimit computation
  is that isomorphism.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat_hom_naturality`: **the
  computation is natural in `C`**, with no boundedness, finiteness or projectivity hypothesis on
  either complex.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))

/-- **`T_ψ(C)` is K-flat** for `C` a bounded above complex of flat `A`-modules: `T_ψ(C)` is then
bounded above with flat terms, and a bounded above complex of flat sheaves of modules is K-flat
by Stacks 06YQ.

This is the single-complex counterpart of
`AlgebraicGeometry.Space.kFlat_spacesEtaleModelPointTensor_colimit`, and it is what lets the
structure sheaf `𝒪_X = T_ψ(A)` and an arbitrary colimit-presented complex be treated by the one
isomorphism `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat`. -/
theorem kFlat_spacesEtaleModelPointTensor_of_isStrictlyLE
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) (hb : C.IsStrictlyLE b)
    (hflat : ∀ i : ℤ, Module.Flat A (C.X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (spacesEtaleModelRingedTopos B S hS X).O)
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C) :=
  have := isStrictlyLE_spacesEtaleModelPointTensor_mapHomologicalComplex B S hS ψ C b hb
  CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ _ b
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor _)
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules _)
    fun q => Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ _
      (isFlat_spacesEtaleModelPointTensor_mapHomologicalComplex_X B S hS ψ C hflat q) q

/-- **A flat module placed in a single degree gives a complex of flat modules**: the term in
degree `j` is the module and every other term is zero.

The same statement is proved as `flat_single_X` in the course of
`StacksFrontier/Homology/HomComplex/RHom/BaseChange.lean`, where it is `private` and so cannot be
used from another module; the proof here is its proof. -/
theorem flat_single_obj_X (M : ModuleCat.{u} A) (hM : Module.Flat A M) (j i : ℤ) :
    Module.Flat A
      (((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) j).obj M).X i) := by
  by_cases h : i = j
  · subst h
    have := hM
    exact Module.Flat.of_linearEquiv
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M).toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j M i h)
    infer_instance

/-- **The structure sheaf is the point tensor of the single complex `A`**, in the derived
category: `T_ψ` carries `A` to `𝒪_X` (`spacesEtaleModelPointTensorObjSelfIso`) and commutes with
placing a module in a single degree.

This is the first argument of the affine leaf of Stacks 09RI, read as a point tensor, which is
what puts it inside the naturality square of
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat_hom_naturality`. -/
def pointTensorSingleSelfIso :
    DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS X).O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS X).O)) :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (spacesEtaleModelPointTensor B S hS ψ)
          (ComplexShape.up ℤ) 0).app (ModuleCat.of A A) ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (spacesEtaleModelPointTensorObjSelfIso B S hS ψ)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- **The point tensor of the single complex `A` is K-flat with flat terms**, so the derived
pullback of the structure sheaf is covered by
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat`. -/
theorem kFlat_spacesEtaleModelPointTensor_single :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (spacesEtaleModelRingedTopos B S hS X).O)
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A))) :=
  kFlat_spacesEtaleModelPointTensor_of_isStrictlyLE B S hS ψ _ 0
    (inferInstanceAs (CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A)) 0))
    (flat_single_obj_X (ModuleCat.of A A) inferInstance 0)

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {A' : Type u} [CommRing A']
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))
  (α : A →+* A') (hψ : ∀ a, globalFunctionsMap B S hS g (ψ a) = ψ' (α a))

include hψ in
/-- **`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` whenever `T_ψ(C)` is K-flat with flat terms**, which is
the hypothesis under which the comparison of Stacks 06YY is invertible; termwise
`g^* T_ψ ≅ T_{ψ'} ∘ (A' ⊗_A -)`.

Nothing at all is assumed about `C`.  Both of the computations already in the tree are instances:
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit` is this one at
`AlgebraicGeometry.Space.kFlat_spacesEtaleModelPointTensor_colimit`, on the nose
(`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit_eq`), and a bounded above
complex of flat modules satisfies the hypothesis by
`AlgebraicGeometry.Space.kFlat_spacesEtaleModelPointTensor_of_isStrictlyLE`. -/
def derivedPullbackPointTensorIsoOfKFlat (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hKF : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (spacesEtaleModelRingedTopos B S hS X).O)
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C))
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (spacesEtaleModelRingedTopos B S hS X).O)
      ((((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).X i)) :
    (derivedPullback (spacesEtaleModelHom B S hS g)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) ≅
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) :=
  letI : (ModuleCat.extendScalars.{u, u, u} α).Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj α)
  Stacks.Sheaves.DerivedPullback.flatPullbackIso (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g) _ hKF hflat ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (F := spacesEtaleModelPointTensor B S hS ψ)
        (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
        (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
        (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ) (ComplexShape.up ℤ)).app C)

include hψ in
/-- **The colimit computation of the derived pullback of a point tensor is the K-flat one.**  The
two definitions have the same body; the K-flatness and flatness arguments are `Prop`s, so the
ones `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit` supplies and the ones
passed here are interchangeable. -/
theorem derivedPullbackPointTensorIsoOfColimit_eq
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, CochainComplex.IsStrictlyLE (D.obj n) b)
    (hflat : ∀ (n : ℕ) (i : ℤ), Module.Flat A ((D.obj n).X i)) :
    derivedPullbackPointTensorIsoOfColimit B S hS ψ D g ψ' α hψ hLE hflat =
      derivedPullbackPointTensorIsoOfKFlat B S hS ψ g ψ' α hψ (colimit D)
        (kFlat_spacesEtaleModelPointTensor_colimit B S hS ψ D hLE hflat)
        (isFlat_spacesEtaleModelPointTensor_colimit_X B S hS ψ D hflat) :=
  rfl

include hψ in
/-- **The computation `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` is natural in `C`**: for a map
`v : C ⟶ C'` of complexes of `A`-modules whose point tensors are K-flat with flat terms, it
intertwines `Lg^* T_ψ(v)` and `T_{ψ'}(A' ⊗_A v)`.

This is `AlgebraicGeometry.Space.derivedPullbackPointTensorIso_hom_naturality` with every
hypothesis on the terms of the two complexes — finite support, finite terms, projective terms,
boundedness — replaced by the hypothesis of Stacks 06YY on their point tensors.  Nothing forces
the two complexes to satisfy it for the same reason, so one side may be a bounded above complex
of flat modules and the other an arbitrary colimit-presented complex.

The proof is `Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality` followed by naturality
of the termwise comparison `g^* T_ψ ≅ T_{ψ'} ∘ (A' ⊗_A -)`. -/
theorem derivedPullbackPointTensorIsoOfKFlat_hom_naturality
    {C C' : CochainComplex (ModuleCat.{u} A) ℤ} (v : C ⟶ C')
    (hKF : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (spacesEtaleModelRingedTopos B S hS X).O)
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C))
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (spacesEtaleModelRingedTopos B S hS X).O)
      ((((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).X i))
    (hKF' : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (spacesEtaleModelRingedTopos B S hS X).O)
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C'))
    (hflat' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (spacesEtaleModelRingedTopos B S hS X).O)
      ((((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C').X i)) :
    (derivedPullback (spacesEtaleModelHom B S hS g)).map (DerivedCategory.Q.map
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v)) ≫
        (derivedPullbackPointTensorIsoOfKFlat B S hS ψ g ψ' α hψ C' hKF' hflat').hom =
      (derivedPullbackPointTensorIsoOfKFlat B S hS ψ g ψ' α hψ C hKF hflat).hom ≫
        DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
            (ComplexShape.up ℤ)).map v)) := by
  let _ : (ModuleCat.extendScalars.{u, u, u} α).Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj α)
  simp only [derivedPullbackPointTensorIsoOfKFlat, Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% (Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality
    (spacesEtaleModelHom B S hS g) (isMorphismOfSites_spacesEtaleModelHom B S hS g)
    (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map v)
    hKF hKF' hflat hflat')]
  rw [Category.assoc, cancel_epi, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
    (F := spacesEtaleModelPointTensor B S hS ψ)
    (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
    (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
    (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ)
      (ComplexShape.up ℤ)).hom.naturality v)

end AlgebraicGeometry.Space

end
