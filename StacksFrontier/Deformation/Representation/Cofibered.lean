module

public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Representation.Basic
public import StacksFrontier.Deformation.Smallness

/-!
# The deformation category of a representation is cofibered in groupoids

The functor `ℱ ⥤ 𝒞_Λ` of Stacks Project, Tag 0D3J is cofibered in groupoids. Pushing a
finite projective representation `(A, M, ρ)` forward along `f : A ⟶ B` is extension of
scalars: the module is `B ⊗_A M` and the action is `ρ` tensored with the identity. Fill-ins
are unique because the structure map of a morphism exhibits its target as a base change,
and a map out of a base change is determined by its restriction.

The module universe is independent of the ring universe, so the tensor product has to be
transported back into the module universe. This is possible: a finite projective module
over an object of `𝒞_Λ` is free, so either it is trivial — and then so is every base
change — or the coefficient algebra embeds into it, and
`Deformation.ArtinianLocalAlgCat.small` makes every coefficient algebra, hence every base
change, small in the module universe.

Since the residue field is a terminal object of `𝒞_Λ`, slicing at the special fibre
preserves the property, by `Deformation.isCofiberedInGroupoids_overForget`.

## Main definitions

* `Deformation.representationBaseChange`: extension of scalars of a representation.
* `Deformation.representationCongr`: transport of a representation along a linear
  equivalence.

## Main results

* `Deformation.RepresentationCategory.representationProjection_isCofiberedInGroupoids`:
  the category of finite projective representations is cofibered in groupoids.
* `Deformation.deformationCategoryProjection_isCofiberedInGroupoids`: the deformation
  category of a representation is cofibered in groupoids.

## References

* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w m x

/-! ### Base change and transport of representations -/

/-- Extension of scalars of a representation: the representation of `G` on `B ⊗_A M`
obtained from a representation on `M` by tensoring with the identity of `B`. -/
noncomputable def representationBaseChange {A : Type*} (B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] {M : Type*} [AddCommGroup M] [Module A M] {G : Type*} [Monoid G]
    (ρ : Representation A G M) : Representation B G (TensorProduct A B M) where
  toFun γ := LinearMap.baseChange B (ρ γ)
  map_one' := by
    change LinearMap.baseChange B (ρ 1) = 1
    rw [map_one]
    exact LinearMap.baseChange_id
  map_mul' γ δ := by
    change LinearMap.baseChange B (ρ (γ * δ)) = _
    rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact LinearMap.baseChange_comp _ _

/-- The base-changed action of `γ` sends `b ⊗ₜ mm` to `b ⊗ₜ ρ γ mm`. -/
@[simp]
theorem representationBaseChange_tmul {A : Type*} (B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] {M : Type*} [AddCommGroup M] [Module A M] {G : Type*} [Monoid G]
    (ρ : Representation A G M) (γ : G) (b : B) (mm : M) :
    representationBaseChange B ρ γ (b ⊗ₜ[A] mm) = b ⊗ₜ[A] ρ γ mm :=
  LinearMap.baseChange_tmul _ _ _

/-- Transport of a representation along a linear equivalence. -/
def representationCongr {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {G : Type*} [Monoid G] (e : M ≃ₗ[R] N)
    (ρ : Representation R G M) : Representation R G N where
  toFun γ := (e : M →ₗ[R] N) ∘ₗ (ρ γ) ∘ₗ (e.symm : N →ₗ[R] M)
  map_one' := by
    ext nn
    simp
  map_mul' γ δ := by
    ext nn
    simp [Module.End.mul_eq_comp]

/-- The transported action of `γ` on `nn` is `e (ρ γ (e.symm nn))`. -/
@[simp]
theorem representationCongr_apply {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {G : Type*} [Monoid G] (e : M ≃ₗ[R] N)
    (ρ : Representation R G M) (γ : G) (nn : N) :
    representationCongr e ρ γ nn = e (ρ γ (e.symm nn)) := rfl

namespace RepresentationCategory

variable {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k] [Algebra Λ k]
  [Group Γ]

/-- The residue field is small in the module universe, as soon as the module of a finite
projective representation is nontrivial. -/
theorem small_residueField_of_nontrivial
    (X : RepresentationCategory.{u, v, w, m, x} Λ k Γ) [Nontrivial X.carrier] :
    Small.{m} k := by
  classical
  have hfree : Module.Free X.base X.carrier := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis X.base X.carrier
  have : Finite (Module.Free.ChooseBasisIndex X.base X.carrier) :=
    Module.Finite.finite_basis b
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex X.base X.carrier) := by
    by_contra h
    have : IsEmpty (Module.Free.ChooseBasisIndex X.base X.carrier) := not_nonempty_iff.mp h
    have : Subsingleton X.carrier := b.repr.toEquiv.subsingleton
    exact (not_nontrivial_iff_subsingleton.mpr ‹Subsingleton X.carrier›)
      ‹Nontrivial X.carrier›
  have : Small.{m} X.carrier := UnivLE.small X.carrier
  have hbase : Small.{m} X.base := small_of_injective
    (f := fun a : X.base => a • b i) (by
      intro a a' haa
      simpa using congrArg (fun z => b.repr z i) haa)
  have : Small.{m} (IsLocalRing.ResidueField X.base) :=
    small_of_surjective (f := IsLocalRing.residue X.base) IsLocalRing.residue_surjective
  exact small_map X.base.residueEquiv.toEquiv.symm

/-- Every base change of the module of a finite projective representation is small in the
module universe. -/
theorem small_tensorProduct (X : RepresentationCategory.{u, v, w, m, x} Λ k Γ)
    (B : ArtinianLocalAlgCat.{u, v, w} Λ k) [Algebra X.base B] :
    Small.{m} (TensorProduct X.base B X.carrier) := by
  classical
  rcases subsingleton_or_nontrivial X.carrier with hsub | hnt
  · exact small_subsingleton _
  · have : Small.{m} k := small_residueField_of_nontrivial X
    have : Small.{m} B := ArtinianLocalAlgCat.small B
    have : Module.Finite B (TensorProduct X.base B X.carrier) :=
      Module.Finite.base_change X.base B X.carrier
    exact Module.Finite.small B (TensorProduct X.base B X.carrier)

/-- Pushforward of a finite projective representation along a morphism of coefficient
algebras exists: extension of scalars, transported back into the module universe. -/
theorem exists_isHomLift (X : RepresentationCategory.{u, v, w, m, x} Λ k Γ)
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : X.base ⟶ B) :
    ∃ (Y : RepresentationCategory.{u, v, w, m, x} Λ k Γ) (φ : X ⟶ Y),
      representationProjection.IsHomLift f φ := by
  classical
  let : Algebra X.base B := f.hom.toRingHom.toAlgebra
  have hsm : Small.{m} (TensorProduct X.base B X.carrier) := small_tensorProduct X B
  have : Module.Finite B (TensorProduct X.base B X.carrier) :=
    Module.Finite.base_change X.base B X.carrier
  have : Module.Projective B (TensorProduct X.base B X.carrier) :=
    Module.Projective.tensorProduct
  let e := Shrink.linearEquiv B (TensorProduct X.base B X.carrier)
  let ι : X.carrier →+ Shrink.{m} (TensorProduct X.base B X.carrier) :=
    { toFun := fun mm => e.symm ((1 : B) ⊗ₜ[X.base] mm)
      map_zero' := by simp
      map_add' := fun a b => by simp [TensorProduct.tmul_add] }
  have hsmul : ∀ (r : X.base) (mm : X.carrier), ι (r • mm) = f.hom r • ι mm := by
    intro r mm
    show e.symm ((1 : B) ⊗ₜ[X.base] (r • mm)) = f.hom r • e.symm ((1 : B) ⊗ₜ[X.base] mm)
    rw [← map_smul]
    congr 1
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      smul_eq_mul, mul_one]
    rfl
  let ρ' : Representation B Γ (Shrink.{m} (TensorProduct X.base B X.carrier)) :=
    representationCongr e.symm (representationBaseChange B X.action)
  have hequiv : ∀ (γ : Γ) (mm : X.carrier), ι (X.action γ mm) = ρ' γ (ι mm) := by
    intro γ mm
    show e.symm ((1 : B) ⊗ₜ[X.base] X.action γ mm) =
      representationCongr e.symm (representationBaseChange B X.action) γ
        (e.symm ((1 : B) ⊗ₜ[X.base] mm))
    rw [representationCongr_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      representationBaseChange_tmul]
  let Y : RepresentationCategory.{u, v, w, m, x} Λ k Γ :=
    { base := B
      carrier := Shrink.{m} (TensorProduct X.base B X.carrier)
      finite := Module.Finite.equiv e.symm
      projective := Module.Projective.of_equiv e.symm
      action := ρ' }
  let φ : X ⟶ Y := Hom.ofEquiv (X := X) (Y := Y) f ι hsmul hequiv e.symm (fun _ => rfl)
  exact ⟨Y, φ, Functor.IsHomLift.map φ⟩

/-- Fill-ins in the representation category exist and are unique: the target of a morphism
is the base change of its source, so a morphism out of it is determined by its restriction,
and the base-change universal property produces it. -/
theorem exists_unique_hom {X Y Z : RepresentationCategory.{u, v, w, m, x} Λ k Γ}
    (φ : X ⟶ Y) (ψ : X ⟶ Z) (f : Y.base ⟶ Z.base)
    (hf : representationProjection.map φ ≫ f = representationProjection.map ψ) :
    ∃! χ : Y ⟶ Z, representationProjection.map χ = f ∧ φ ≫ χ = ψ := by
  have hfh : ∀ r : X.base, f.hom (φ.base.hom r) = ψ.base.hom r := fun r =>
    congrArg (fun q : X.base ⟶ Z.base => q.hom r) hf
  let : Algebra X.base Y.base := φ.base.hom.toRingHom.toAlgebra
  let : Algebra Y.base Z.base := f.hom.toRingHom.toAlgebra
  let : Algebra X.base Z.base := ψ.base.hom.toRingHom.toAlgebra
  let : Module X.base Y.carrier := Module.compHom Y.carrier φ.base.hom.toRingHom
  let : Module Y.base Z.carrier := Module.compHom Z.carrier f.hom.toRingHom
  let : Module X.base Z.carrier := Module.compHom Z.carrier ψ.base.hom.toRingHom
  have : IsScalarTower X.base Y.base Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Y.base Z.base Z.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower X.base Z.base Z.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower X.base Y.base Z.base :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (hfh r).symm
  have htower : IsScalarTower X.base Y.base Z.carrier :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      show f.hom (φ.base.hom r) • z = ψ.base.hom r • z
      rw [hfh]
  have hφbc : IsBaseChange (Y.base : Type v)
      (restrictAddHom φ.base.hom.toRingHom φ.map φ.map_smul) := φ.isBaseChange
  have hψbc : IsBaseChange (Z.base : Type v)
      (restrictAddHom ψ.base.hom.toRingHom ψ.map ψ.map_smul) := ψ.isBaseChange
  set L : Y.carrier →ₗ[Y.base] Z.carrier :=
    hφbc.lift (restrictAddHom ψ.base.hom.toRingHom ψ.map ψ.map_smul) with hL
  have hLeq : ∀ xx : X.carrier, L (φ.map xx) = ψ.map xx :=
    hφbc.lift_eq (restrictAddHom ψ.base.hom.toRingHom ψ.map ψ.map_smul)
  have hLsmul : ∀ (r : Y.base) (y : Y.carrier), L (r • y) = f.hom r • L y := fun r y ↦
    L.map_smul r y
  have hLequiv : ∀ (γ : Γ) (y : Y.carrier), L (Y.action γ y) = Z.action γ (L y) := by
    intro γ
    have hext : L ∘ₗ Y.action γ = (Z.action γ).restrictScalars Y.base ∘ₗ L := by
      refine hφbc.algHom_ext _ _ fun xx ↦ ?_
      show L (Y.action γ (φ.map xx)) = Z.action γ (L (φ.map xx))
      rw [← φ.equivariant, hLeq, hLeq, ψ.equivariant]
    exact LinearMap.congr_fun hext
  have hLbc : IsBaseChange (Z.base : Type v)
      (restrictAddHom f.hom.toRingHom L.toAddMonoidHom hLsmul) := by
    refine IsBaseChange.of_comp hφbc (h := L) ?_
    have hcomp : (L : Y.carrier →ₗ[X.base] Z.carrier) ∘ₗ
        restrictAddHom φ.base.hom.toRingHom φ.map φ.map_smul =
        restrictAddHom ψ.base.hom.toRingHom ψ.map ψ.map_smul := by
      exact LinearMap.ext hLeq
    rw [hcomp]
    exact hψbc
  refine ⟨{ base := f
            map := L.toAddMonoidHom
            map_smul := hLsmul
            equivariant := hLequiv
            isBaseChange := hLbc }, ⟨rfl, ?_⟩, ?_⟩
  · exact Hom.ext hf (AddMonoidHom.ext hLeq)
  · intro χ hχ
    have hb : χ.base = f := hχ.1
    have hsm' : ∀ (r : Y.base) (y : Y.carrier), χ.map (r • y) = f.hom r • χ.map y := by
      intro r y
      rw [χ.map_smul, hb]
    have hfac : ∀ xx : X.carrier, χ.map (φ.map xx) = ψ.map xx := fun xx =>
      congrArg (fun q : Hom X Z => q.map xx) hχ.2
    have hLL : restrictAddHom f.hom.toRingHom χ.map hsm' = L := by
      refine hφbc.algHom_ext _ _ fun xx ↦ ?_
      show χ.map (φ.map xx) = L (φ.map xx)
      rw [hfac, hLeq]
    exact Hom.ext hb (AddMonoidHom.ext (LinearMap.congr_fun hLL))

/-- The category of finite projective representations is cofibered in groupoids over the
category of Artinian local coefficient algebras. -/
@[stacks 0D3J "second presentation: representation_category"]
theorem representationProjection_isCofiberedInGroupoids :
    IsCofiberedInGroupoids
      (representationProjection.{u, v, w, m, x} (Λ := Λ) (k := k) (Γ := Γ)) := by
  refine isCofiberedInGroupoids_of_lifts ?_ ?_
  · intro A B g a ha
    subst ha
    exact exists_isHomLift a g
  · intro a b c φ ψ g hg
    exact exists_unique_hom φ ψ g hg

end RepresentationCategory

/-- The deformation category of a finite-dimensional representation is cofibered in
groupoids over the category of Artinian local coefficient algebras. -/
theorem deformationCategoryProjection_isCofiberedInGroupoids
    {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) :
    IsCofiberedInGroupoids (deformationCategoryProjection (Λ := Λ) V ρ₀) :=
  isCofiberedInGroupoids_overForget
    RepresentationCategory.representationProjection_isCofiberedInGroupoids
    (RepresentationCategory.specialFiber (Λ := Λ) V ρ₀)
    Examples.isTerminal_residueFieldBase

end Deformation

end
