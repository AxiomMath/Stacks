module

public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Linear.Representations

/-!
# Representations of a group are cofibered in groupoids over the base category

The projection sending a finite projective representation of `Γ` to its coefficient algebra is
cofibered in groupoids. The pushforward of `(A, M, ρ)` along `A → B` is extension of scalars
with the induced action, and the filling morphism between two representations over a given map
of coefficient algebras is the unique base-change extension of the given map of modules, which
is automatically equivariant.

## Main definitions

* `Deformation.Examples.FiniteProjectiveRepresentation.projection`: the functor forgetting the
  module and the action.

## Main results

* `Deformation.Examples.FiniteProjectiveRepresentation.projection_isCofiberedInGroupoids`: that
  projection is cofibered in groupoids.

## Implementation notes

The module universe is required to contain the universe of the coefficient algebras, so that
extension of scalars again produces an object of the representation category.

## References

* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveRepresentation

universe u v w m

variable {Λ : Type u} {k : Type w} {Γ : Type*}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]

/-- Extension of scalars of a finite projective representation along a map of coefficient
algebras, with the action extended linearly. -/
@[reducible] private def scalarExtension
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FiniteProjectiveRepresentation.{u, v, w, max v m} Λ k Γ) (f : X.base ⟶ B) :
    FiniteProjectiveRepresentation.{u, v, w, max v m} Λ k Γ := by
  letI : Algebra X.base B := f.hom.toAlgebra
  refine ⟨B, TensorProduct X.base B X.carrier, ?_⟩
  exact
    { toFun := fun γ =>
        TensorProduct.AlgebraTensorModule.map
          (LinearMap.id (R := (B : Type v)) (M := (B : Type v))) (X.action γ)
      map_one' := by ext b; simp
      map_mul' := by intro γ δ; ext b; simp [map_mul] }

/-- The canonical morphism from a representation to its extension of scalars. -/
private noncomputable def scalarExtensionArrow
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FiniteProjectiveRepresentation.{u, v, w, max v m} Λ k Γ) (f : X.base ⟶ B) :
    FiniteProjectiveRepresentation.Hom X (scalarExtension X f) := by
  letI : Algebra X.base B := f.hom.toAlgebra
  letI : Module X.base (TensorProduct X.base B X.carrier) :=
    Module.compHom _ f.hom.toRingHom
  let g : X.carrier →ₗ[X.base] TensorProduct X.base B X.carrier :=
    TensorProduct.mk X.base B X.carrier (1 : B)
  refine ⟨f, g.toAddMonoidHom, fun r x => g.map_smul r x, (by intro γ x; rfl), ?_⟩
  · change IsBaseChange B
      (TensorProduct.mk X.base B X.carrier (1 : B))
    exact TensorProduct.isBaseChange X.base X.carrier B

/-- Given morphisms `φ : X ⟶ Y` and `ψ : X ⟶ Z` of representations and a map `f` of the
coefficient algebras of `Y` and `Z` with `φ.base ≫ f = ψ.base`, there is a unique morphism
`Y ⟶ Z` over `f` through which `ψ` factors. -/
private lemma hom_fillIn
    (X Y Z : FiniteProjectiveRepresentation.{u, v, w, max v m} Λ k Γ)
    (φ : X ⟶ Y) (ψ : X ⟶ Z)
    (f : Y.base ⟶ Z.base) (hbase : φ.base ≫ f = ψ.base) :
    ∃! χ : Y ⟶ Z, χ.base = f ∧ φ ≫ χ = ψ := by
  let : Algebra X.base Y.base := φ.base.hom.toAlgebra
  let : Algebra Y.base Z.base := f.hom.toAlgebra
  let : Algebra X.base Z.base := ψ.base.hom.toAlgebra
  let : Module X.base Y.carrier := Module.compHom Y.carrier φ.base.hom.toRingHom
  let : Module X.base Z.carrier := Module.compHom Z.carrier ψ.base.hom.toRingHom
  let : Module Y.base Z.carrier := Module.compHom Z.carrier f.hom.toRingHom
  let : IsScalarTower X.base Y.base Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower X.base Z.base Z.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Y.base Z.base Z.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hhom : f.hom.comp φ.base.hom = ψ.base.hom := by
    rw [← hbase, ArtinianLocalAlgCat.comp_hom]
  let : IsScalarTower X.base Y.base Z.base :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change ψ.base.hom.toRingHom r =
        f.hom.toRingHom (φ.base.hom.toRingHom r)
      have h := congrArg (fun g : X.base →ₐ[Λ] Z.base => g.toRingHom r) hhom
      change f.hom.toRingHom (φ.base.hom.toRingHom r) = ψ.base.hom.toRingHom r at h
      exact h.symm
  let : IsScalarTower X.base Y.base Z.carrier :=
    IsScalarTower.of_algebraMap_smul fun r z => by
      change (f.hom.comp φ.base.hom) r • z = ψ.base.hom r • z
      rw [hhom]
  let φlin : X.carrier →ₗ[X.base] Y.carrier :=
    restrictAddHom φ.base.hom.toRingHom φ.map φ.map_smul
  let ψlin : X.carrier →ₗ[X.base] Z.carrier :=
    restrictAddHom ψ.base.hom.toRingHom ψ.map ψ.map_smul
  have hφbc : IsBaseChange Y.base φlin := φ.isBaseChange
  have hψbc : IsBaseChange Z.base ψlin := ψ.isBaseChange
  let χlin : Y.carrier →ₗ[Y.base] Z.carrier := hφbc.lift ψlin
  have hχfac : (χlin.restrictScalars X.base).comp φlin = ψlin := hφbc.lift_comp ψlin
  have hχeq (x : X.carrier) : χlin (φ.map x) = ψ.map x :=
    LinearMap.congr_fun hχfac x
  have hχbc : IsBaseChange Z.base χlin :=
    (IsBaseChange.comp_iff hφbc).mp (by rw [hχfac]; exact hψbc)
  let χ : Y ⟶ Z :=
    { base := f
      map := χlin.toAddMonoidHom
      map_smul := fun r y => χlin.map_smul r y
      equivariant := by
        intro γ y
        have heq : χlin.comp (Y.action γ) =
            ((Z.action γ).restrictScalars Y.base).comp χlin := hφbc.algHom_ext _ _ fun x => by
          change χlin (Y.action γ (φ.map x)) = Z.action γ (χlin (φ.map x))
          calc
            χlin (Y.action γ (φ.map x)) = χlin (φ.map (X.action γ x)) := by
              rw [← φ.equivariant]
            _ = ψ.map (X.action γ x) := hχeq _
            _ = Z.action γ (ψ.map x) := ψ.equivariant γ x
            _ = Z.action γ (χlin (φ.map x)) := by rw [← hχeq x]
        exact LinearMap.congr_fun heq y
      isBaseChange := hχbc }
  refine ⟨χ, ⟨rfl, ?_⟩, ?_⟩
  · exact FiniteProjectiveRepresentation.Hom.ext hbase <| AddMonoidHom.ext fun x =>
      LinearMap.congr_fun hχfac x
  · rintro χ' ⟨hχ'base, hχ'comp⟩
    refine FiniteProjectiveRepresentation.Hom.ext hχ'base (AddMonoidHom.ext fun y => ?_)
    have hχ'hom : χ'.base.hom = f.hom :=
      congrArg (fun g : Y.base ⟶ Z.base => g.hom) hχ'base
    let χ'lin : Y.carrier →ₗ[Y.base] Z.carrier :=
      restrictAddHom f.hom.toRingHom χ'.map (by
        intro r z
        rw [← hχ'hom]
        exact χ'.map_smul r z)
    have hlin : χ'lin = χlin := hφbc.algHom_ext _ _ fun x =>
      (congrArg (fun g : X ⟶ Z => g.map x) hχ'comp).trans (hχeq x).symm
    exact LinearMap.congr_fun hlin y

/-- Forget the module and action of a finite projective representation, retaining its
coefficient algebra. -/
@[stacks 0D3J "the projection"]
public def projection :
    FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ ⥤
      ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj X := X.base
  map f := f.base
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The category of finite projective representations is cofibered in groupoids over the
category of Artinian local coefficient algebras. -/
@[stacks 0D3J "cofibered in groupoids"]
public theorem projection_isCofiberedInGroupoids :
    IsCofiberedInGroupoids
      (projection (Λ := Λ) (k := k) (Γ := Γ) :
        FiniteProjectiveRepresentation.{u, v, w, max v m} Λ k Γ ⥤
          ArtinianLocalAlgCat.{u, v, w} Λ k) := by
  change Functor.IsFiberedInGroupoids
    (projection (Λ := Λ) (k := k) (Γ := Γ) :
      FiniteProjectiveRepresentation.{u, v, w, max v m} Λ k Γ ⥤
        ArtinianLocalAlgCat.{u, v, w} Λ k).op
  refine ⟨?_, ?_⟩
  · intro V U f x hx
    rcases V with ⟨V⟩; rcases U with ⟨U⟩; rcases x with ⟨X⟩; rcases f with ⟨f⟩
    have hx' : X.base = U := congrArg Opposite.unop hx
    subst U
    let f' : X.base ⟶ V := f
    refine ⟨Opposite.op (scalarExtension X f'),
      Quiver.Hom.op (scalarExtensionArrow X f'), ?_⟩
    apply IsHomLift.of_fac'
      (p := (projection (Λ := Λ) (k := k) (Γ := Γ)).op)
      (Quiver.Hom.op f) (Quiver.Hom.op (scalarExtensionArrow X f')) rfl rfl
    change (projection.map (scalarExtensionArrow X f')).op = f.op
    rfl
  · intro x y z φ ψ f hf
    rcases x with ⟨X⟩; rcases y with ⟨Y⟩; rcases z with ⟨Z⟩
    let φ' : X ⟶ Y := Quiver.Hom.unop φ
    let ψ' : X ⟶ Z := Quiver.Hom.unop ψ
    let f' : Y.base ⟶ Z.base := Quiver.Hom.unop f
    have hcomm : φ'.base ≫ f' = ψ'.base := by
      have h := congrArg Quiver.Hom.unop hf
      rw [unop_comp] at h
      simpa [projection, φ', ψ', f'] using h
    obtain ⟨χ, ⟨hχbase, hχcomp⟩, huniq⟩ :=
      hom_fillIn X Y Z φ' ψ' f' hcomm
    refine ⟨Quiver.Hom.op χ, ?_, ?_⟩
    · constructor
      · apply Quiver.Hom.unop_inj
        simpa [projection, f'] using hχbase
      · apply Quiver.Hom.unop_inj
        simpa [φ', ψ'] using hχcomp
    · intro χ' hχ'
      have hprops : χ'.unop.base = f' ∧ φ' ≫ χ'.unop = ψ' := ⟨by
        simpa [projection, f'] using congrArg Quiver.Hom.unop hχ'.1, by
        simpa [φ', ψ'] using congrArg Quiver.Hom.unop hχ'.2⟩
      simpa using congrArg Quiver.Hom.op (huniq χ'.unop hprops)

end Deformation.Examples.FiniteProjectiveRepresentation
