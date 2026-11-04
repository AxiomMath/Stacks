module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KProjectiveMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorPerfect
public import StacksFrontier.Homology.Perfect.FiniteProjectiveColimitDescent

/-!
# Descent of `𝒪_X ⊗_A C` along a filtered colimit of base rings

Let `X` be an algebraic space with a ring map `ψ : A ⟶ Γ(X, 𝒪_X)`, where `A = colim A_i` is a
filtered colimit of commutative rings, and let `g_i : X ⟶ X_i` be morphisms to algebraic spaces
with ring maps `ψ_i : A_i ⟶ Γ(X_i, 𝒪_{X_i})` such that `g_i^* ∘ ψ_i = ψ ∘ (A_i ⟶ A)`. Then every
object `E` of the derived category of the spaces-étale model of `X` isomorphic to
`𝒪_X ⊗_A C = T_ψ(C)` for a bounded complex `C` of finite projective `A`-modules descends: for
some `i` there is a perfect object `E_i` on `X_i` with `Lg_i^* E_i ≅ E`.

Indeed `C` descends to a bounded complex `C_i` of finite projective `A_i`-modules with
`A ⊗_{A_i} C_i ≅ C` in `D(A)` (Stacks 0BC7); take `E_i = T_{ψ_i}(C_i)`, which is perfect. Its
derived pullback is `T_ψ(A ⊗_{A_i} C_i)`, computed termwise, and the two K-projective complexes
`A ⊗_{A_i} C_i` and `C` are homotopy equivalent, so their images under the additive functor `T_ψ`
are isomorphic in the derived category.

This is the affine case of the descent of perfect objects along a limit of algebraic spaces
(Stacks 09RJ), once a perfect object on an affine limit is known to be of the form `T_ψ(C)`.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_derivedPullback_iso_of_pointTensor`.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7)
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

/-- **`𝒪_X ⊗_A C` descends along a filtered colimit `A = colim A_i` of base rings.** With
`g_i : X ⟶ X_i` and `ψ_i : A_i ⟶ Γ(X_i, 𝒪)` compatible with `ψ : A ⟶ Γ(X, 𝒪)`, an object
isomorphic to `T_ψ(C)` for a bounded complex `C` of finite projective `A`-modules is
`Lg_i^* E_i` for some `i` and some perfect `E_i` on `X_i`. -/
theorem exists_isPerfect_derivedPullback_iso_of_pointTensor
    {I : Type u} [Category.{u} I] [IsFiltered I] (R : I ⥤ CommRingCat.{u})
    [PreservesColimit R (forget CommRingCat.{u})] (c : Cocone R) (hc : IsColimit c)
    {X : AlgebraicSpaces B S hS}
    (ψ : c.pt →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))
    (Xs : I → AlgebraicSpaces B S hS) (g : ∀ i, X ⟶ Xs i)
    (ψs : ∀ i, R.obj i →+*
      (SpacesEtale.structurePresheaf B S hS (Xs i)).obj (op (SpacesEtale.idObj B S hS (Xs i))))
    (hψ : ∀ i a, globalFunctionsMap B S hS (g i) (ψs i a) = ψ (c.ι.app i a))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS X).O)))
    (C : CochainComplex (ModuleCat.{u} c.pt) ℤ) (a b : ℤ) (ha : C.IsStrictlyGE a)
    (hb : C.IsStrictlyLE b) (hfin : ∀ n : ℤ, Module.Finite c.pt (C.X n))
    (hproj : ∀ n : ℤ, Module.Projective c.pt (C.X n))
    (eE : E ≅ DerivedCategory.Q.obj
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :
    ∃ (i : I) (Eᵢ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS (Xs i)).O))),
      (spacesEtaleModelRingedSite B S hS (Xs i)).IsPerfect Eᵢ ∧
        Nonempty ((derivedPullback (spacesEtaleModelHom B S hS (g i))).obj Eᵢ ≅ E) := by
  obtain ⟨i, Cᵢ, a', b', ha', hb', hfinᵢ, hprojᵢ, ⟨eC⟩⟩ :=
    StacksDraft.Perfect.exists_finiteProjective_extendScalars_iso R c hc C a b ha hb hfin hproj
  have hbd : {n : ℤ | ¬ IsZero (Cᵢ.X n)}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc a' b') fun n hn => ?_
    simp only [Set.mem_ofPred_eq] at hn
    refine Set.mem_Icc.2 ⟨?_, ?_⟩ <;> by_contra hcon
    · exact hn (Cᵢ.isZero_of_isStrictlyGE a' n (by lia))
    · exact hn (Cᵢ.isZero_of_isStrictlyLE b' n (by lia))
  let α : R.obj i →+* c.pt := (c.ι.app i).hom
  let : (ModuleCat.extendScalars.{u, u, u} α).Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj α)
  let C' : CochainComplex (ModuleCat.{u} c.pt) ℤ :=
    ((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex (ComplexShape.up ℤ)).obj Cᵢ
  have : C'.IsStrictlyLE b' := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => (ModuleCat.extendScalars.{u, u, u} α).map_isZero
      (Cᵢ.isZero_of_isStrictlyLE b' n hn)
  have : ∀ n, Module.Projective c.pt (C'.X n) := fun n =>
    have := hfinᵢ n
    have := hprojᵢ n
    (StacksDraft.Perfect.finite_projective_extendScalars_obj α (Cᵢ.X n)).2
  have : C'.IsKProjective := CochainComplex.isKProjective_of_projective C' b'
  have : C.IsKProjective := CochainComplex.isKProjective_of_projective C b
  obtain ⟨eT⟩ := CochainComplex.IsKProjective.nonempty_Q_obj_mapHomologicalComplex_iso
    (spacesEtaleModelPointTensor B S hS ψ) C' C eC
  exact ⟨i, _, isPerfect_Q_spacesEtaleModelPointTensor B S hS (ψs i) Cᵢ hbd hfinᵢ hprojᵢ,
    ⟨derivedPullbackPointTensorIso B S hS (ψs i) (g i) ψ α (hψ i) Cᵢ b' hb' hbd hfinᵢ hprojᵢ ≪≫
      eT ≪≫ eE.symm⟩⟩

end AlgebraicGeometry.Space

end
