module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimPointTensorFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.LadderResolution

/-!
# The derived pullback of `𝒪_X ⊗_A C` for an unbounded `C`, through a resolution by a colimit

Let `X` be an algebraic space, `ψ : A ⟶ Γ(X, 𝒪_X)` a ring map and `T_ψ : M ↦ 𝒪_X ⊗_A M` the
inverse image along `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)`.

For the derived pullback of `T_ψ(C)` to be computed termwise, `T_ψ(C)` must be K-flat with flat
terms (Stacks 06YY).  K-flatness of `C` itself is of no use here: as
`Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit` records, K-flatness does not
transport along a functor.  What does transport is the *presentation* of Stacks 06YS — a
sequential colimit of bounded above complexes with flat terms — because each of its three
clauses transports separately: `T_ψ` carries flat modules to flat sheaves of modules
(`AlgebraicGeometry.Space.isFlat_spacesEtaleModelPointTensor_obj`), carries a complex bounded
above to one bounded above, and commutes with sequential colimits, being a left adjoint.

So for `C = colim_n C_n` with each `C_n` bounded above with flat terms, `T_ψ(C)` is the colimit
of the bounded above complexes `T_ψ(C_n)` with flat terms, hence K-flat with flat terms
(Stacks 06YQ and 06YR), and

`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`

with no boundedness, finiteness or projectivity hypothesis on `C` at all.  Every complex of
`A`-modules receives a termwise surjective quasi-isomorphism from such a colimit, by
`CochainComplex.KFlatBifunctor.exists_resolution_colimit_of_flat` at the class of flat modules,
so this covers every object of `D(A)`.

## Main results

* `AlgebraicGeometry.Space.isFlat_spacesEtaleModelPointTensor_colimit_X`: the terms of
  `T_ψ(colim C_n)` are flat.
* `AlgebraicGeometry.Space.kFlat_spacesEtaleModelPointTensor_colimit`: `T_ψ(colim C_n)` is
  K-flat.
* `AlgebraicGeometry.Space.exists_colimit_resolution_flat_moduleCat`: every complex of
  `A`-modules receives a termwise surjective quasi-isomorphism from such a colimit.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit`:
  `Lg^* T_ψ(colim C_n) ≅ T_{ψ'}(A' ⊗_A colim C_n)`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
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

/-- `T_ψ` commutes with sequential colimits, being a left adjoint. -/
theorem preservesColimitsOfShape_nat_spacesEtaleModelPointTensor :
    PreservesColimitsOfShape ℕ (spacesEtaleModelPointTensor B S hS ψ) :=
  have : PreservesColimitsOfSize.{0, 0} (spacesEtaleModelPointTensor B S hS ψ) :=
    (spacesEtaleModelPointTensorAdjunction B S hS ψ).leftAdjoint_preservesColimits
  inferInstance

variable (D : ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ)

/-- **The terms of `T_ψ(colim C_n)` are flat** when the terms of each `C_n` are: a sequential
colimit of flat modules is flat (Stacks 05UT), evaluation in a degree commutes with the colimit,
and `T_ψ` carries a flat module to a flat sheaf of modules. -/
theorem isFlat_spacesEtaleModelPointTensor_colimit_X
    (hflat : ∀ (n : ℕ) (i : ℤ), Module.Flat A ((D.obj n).X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (spacesEtaleModelRingedTopos B S hS X).O)
      ((((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (colimit D)).X i) := by
  refine isFlat_spacesEtaleModelPointTensor_obj B S hS ψ _ ?_
  have : Module.Flat A ((colimit (D ⋙ HomologicalComplex.eval (ModuleCat.{u} A)
      (ComplexShape.up ℤ) i) : ModuleCat.{u} A)) :=
    CochainComplex.KFlat.flat_colimit.{u, u}
      (D ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i)
      (fun n => hflat n i)
  exact Module.Flat.of_linearEquiv
    ((preservesColimitIso (HomologicalComplex.eval (ModuleCat.{u} A)
      (ComplexShape.up ℤ) i) D).toLinearEquiv)

/-- **`T_ψ(colim C_n)` is K-flat** when each `C_n` is bounded above with flat terms: each
`T_ψ(C_n)` is then bounded above with flat terms, hence K-flat by Stacks 06YQ, and `T_ψ`
commutes with the colimit, K-flatness passing to a sequential colimit by Stacks 06YR. -/
theorem kFlat_spacesEtaleModelPointTensor_colimit
    (hLE : ∀ n : ℕ, ∃ b : ℤ, CochainComplex.IsStrictlyLE (D.obj n) b)
    (hflat : ∀ (n : ℕ) (i : ℤ), Module.Flat A ((D.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (spacesEtaleModelRingedTopos B S hS X).O)
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (colimit D)) := by
  have := preservesColimitsOfShape_nat_spacesEtaleModelPointTensor B S hS ψ
  have : PreservesColimit D ((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)) :=
    CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
      (spacesEtaleModelPointTensor B S hS ψ)
  refine CochainComplex.KFlatBifunctor.KFlat.of_iso _
    (Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat
      (spacesEtaleModelRingedTopos B S hS X).O
      (D ⋙ (spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ))
      (fun n => by
        obtain ⟨b, hb⟩ := hLE n
        exact ⟨b, isStrictlyLE_spacesEtaleModelPointTensor_mapHomologicalComplex B S hS ψ
          (D.obj n) b hb⟩)
      (fun n i => isFlat_spacesEtaleModelPointTensor_mapHomologicalComplex_X B S hS ψ
        (D.obj n) (fun j => hflat n j) i))
    (preservesColimitIso ((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)) D).symm

/-- **Every complex of `A`-modules receives a termwise surjective quasi-isomorphism from a
sequential colimit of bounded above complexes of flat modules.**  This is Stacks 06YS in the
presentation `CochainComplex.KFlatBifunctor.exists_resolution_colimit_of_flat` gives it, at the
class of projective modules — the class the ladder of Stacks 077J is built from — whose members
are flat.

It is this presentation, and not K-flatness of the resolution, that
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfColimit` consumes, so together the two
compute the derived pullback of `T_ψ(C')` for a representative `C'` of every object of
`D(A)`. -/
theorem exists_colimit_resolution_flat_moduleCat (C : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) (f : colimit D ⟶ C),
      (∀ n : ℕ, CochainComplex.IsStrictlyLE (D.obj n) (n : ℤ)) ∧
      (∀ (n : ℕ) (i : ℤ), Module.Flat A ((D.obj n).X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  have : AB5OfSize.{0, 0, u, u + 1} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{0, 0, u, u} AddCommGrpCat.{u}
  have : HasExactColimitsOfShape ℕ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.domain_of_functor ℕ
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
  let P : ObjectProperty (ModuleCat.{u} A) := fun Y => Projective Y
  have : P.ContainsZero := ⟨ModuleCat.of A (Fin 0 → A),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun {Y Z} e hY => Projective.of_iso e hY⟩
  have hsum : ∀ Y Z : ModuleCat.{u} A, P Y → P Z → P (Y ⊞ Z) := by
    intro Y Z hY hZ
    change Projective Y at hY
    change Projective Z at hZ
    have := hY
    have := hZ
    infer_instance
  have hcover : ∀ Y : ModuleCat.{u} A, ∃ (Z : ModuleCat.{u} A) (_ : P Z) (p : Z ⟶ Y), Epi p :=
    fun Y => ⟨Projective.over Y, inferInstance, Projective.π Y, inferInstance⟩
  obtain ⟨D, f, hle, hproj, hqis, hepi⟩ :=
    CochainComplex.KFlatBifunctor.exists_resolution_colimit_of_flat P hsum hcover C
  refine ⟨D, f, hle, fun n i => ?_, hqis, hepi⟩
  have : Projective ((D.obj n).X i) := hproj n i
  infer_instance

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {A' : Type u} [CommRing A']
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))
  (α : A →+* A') (hψ : ∀ a, globalFunctionsMap B S hS g (ψ a) = ψ' (α a))

include hψ in
/-- **`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`** for `C = colim_n C_n` a sequential colimit of bounded
above complexes of flat `A`-modules — with no hypothesis on `C` itself.  `T_ψ(C)` is K-flat with
flat terms, so the comparison of Stacks 06YY is invertible on it, and termwise
`g^* T_ψ ≅ T_{ψ'} ∘ (A' ⊗_A -)`.

Every complex of `A`-modules receives a termwise surjective quasi-isomorphism from such a
colimit (Stacks 06YS, `CochainComplex.KFlatBifunctor.exists_resolution_colimit_of_flat` at the
class of flat modules), so this applies to a representative of every object of `D(A)`. -/
def derivedPullbackPointTensorIsoOfColimit
    (hLE : ∀ n : ℕ, ∃ b : ℤ, CochainComplex.IsStrictlyLE (D.obj n) b)
    (hflat : ∀ (n : ℕ) (i : ℤ), Module.Flat A ((D.obj n).X i)) :
    (derivedPullback (spacesEtaleModelHom B S hS g)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (colimit D))) ≅
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (colimit D))) :=
  letI : (ModuleCat.extendScalars.{u, u, u} α).Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj α)
  Stacks.Sheaves.DerivedPullback.flatPullbackIso (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g) _
      (kFlat_spacesEtaleModelPointTensor_colimit B S hS ψ D hLE hflat)
      (isFlat_spacesEtaleModelPointTensor_colimit_X B S hS ψ D hflat) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (F := spacesEtaleModelPointTensor B S hS ψ)
        (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
        (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
        (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ)
          (ComplexShape.up ℤ)).app (colimit D))

end AlgebraicGeometry.Space

end
