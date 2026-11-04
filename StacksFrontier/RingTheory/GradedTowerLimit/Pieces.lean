module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.RingTheory.GradedTowerLimit.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Lifting.Projective

/-!
# The homogeneous pieces of a graded inverse limit

For an admissible tower of graded algebras (`Stacks.GradedTowerLimit.GradedTower.IsAdmissible`),
the degree-`d` piece `lim (Aₙ)_d` of the graded inverse limit is a finite projective module over
`lim Rₙ` whose base change to every `Rₙ` is `(Aₙ)_d`. This is Stacks Tag 0D4B applied degree by
degree, as in the proof of Stacks Tag 0D4T.

## Main definitions

* `Stacks.GradedTowerLimit.GradedTower.pieceSystem`: the inverse system `n ↦ (Aₙ)_d` of modules
  over the limit ring.
* `Stacks.GradedTowerLimit.GradedTower.limitPieceEquiv`: its limit is the degree-`d` piece.

## Main results

* `Stacks.GradedTowerLimit.GradedTower.finite_projective_baseChange_piece`: the degree-`d` piece
  of the graded inverse limit is a finite projective module whose base change to `Rₙ` is
  `(Aₙ)_d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace Stacks.GradedTowerLimit

namespace GradedTower

variable {Rg : ℕᵒᵖ ⥤ CommRingCat.{u}} (T : GradedTower Rg)

/-- The degree-`d` transition map `(Aₙ₊₁)_d → (Aₙ)_d`, linear over the limit ring. -/
def trLimit (n d : ℕ) : T.𝒜 (n + 1) d →ₗ[(limit Rg : CommRingCat.{u})] T.𝒜 n d where
  toFun x := ⟨T.ρ n x, T.ρ_mem n d x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext <| by
    change T.ρ n (r • (x : T.A (n + 1))) = r • T.ρ n x
    rw [Algebra.smul_def, map_mul, limitAlgebraA_algebraMap, T.ρ_algebraMap, tr_limit_π,
      Algebra.smul_def, limitAlgebraA_algebraMap]

/-- The transition map `trLimit` sends `x` to `ρₙ x`. -/
@[simp]
theorem coe_trLimit (n d : ℕ) (x : T.𝒜 (n + 1) d) : (T.trLimit n d x : T.A n) = T.ρ n x := rfl

/-- **The inverse system of degree-`d` pieces** `n ↦ (Aₙ)_d` over the limit ring, with
transition maps `trLimit`. -/
abbrev pieceSystem (d : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} (limit Rg : CommRingCat.{u}) where
  obj i := ModuleCat.of (limit Rg : CommRingCat.{u}) (T.𝒜 i.unop d)
  map f := (Functor.ofOpSequence (X := fun n => ModuleCat.of (limit Rg : CommRingCat.{u})
    (T.𝒜 n d)) fun n => ModuleCat.ofHom (T.trLimit n d)).map f
  map_id i := (Functor.ofOpSequence (X := fun n => ModuleCat.of (limit Rg : CommRingCat.{u})
    (T.𝒜 n d)) fun n => ModuleCat.ofHom (T.trLimit n d)).map_id i
  map_comp f g := (Functor.ofOpSequence (X := fun n => ModuleCat.of (limit Rg : CommRingCat.{u})
    (T.𝒜 n d)) fun n => ModuleCat.ofHom (T.trLimit n d)).map_comp f g

/-- The map of `pieceSystem d` along `n ≤ n + 1` is the transition map `trLimit n d`. -/
theorem pieceSystem_map_succ (d n : ℕ) (x : T.𝒜 (n + 1) d) :
    (T.pieceSystem d).map (homOfLE (Nat.le_succ n)).op x = T.trLimit n d x := by
  show (Functor.ofOpSequence (X := fun n => ModuleCat.of (limit Rg : CommRingCat.{u})
    (T.𝒜 n d)) fun n => ModuleCat.ofHom (T.trLimit n d)).map (homOfLE (Nat.le_succ n)).op x = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- The projection of the degree-`d` piece to `(Aₙ)_d`. -/
def pieceProj (d n : ℕ) : T.piece d →ₗ[(limit Rg : CommRingCat.{u})] T.𝒜 n d where
  toFun y := ⟨(y : ∀ n, T.A n) n, (T.mem_piece.1 y.2 n).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection `pieceProj d n` sends a compatible family `y` to its `n`-th component. -/
@[simp]
theorem coe_pieceProj (d n : ℕ) (y : T.piece d) :
    (T.pieceProj d n y : T.A n) = (y : ∀ n, T.A n) n := rfl

/-- The cone over the inverse system of degree-`d` pieces with apex the degree-`d` piece of the
graded inverse limit. -/
abbrev pieceCone (d : ℕ) : Cone (T.pieceSystem d) where
  pt := ModuleCat.of (limit Rg : CommRingCat.{u}) (T.piece d)
  π :=
    { app i := ModuleCat.ofHom (T.pieceProj d i.unop)
      naturality i j f := by
        refine (Category.id_comp _).trans ?_
        refine (comp_map_eq_of_succ (F := T.pieceSystem d)
          (fun n => ModuleCat.ofHom (T.pieceProj d n)) (fun n => ?_) f).symm
        ext y
        rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
        exact (congrArg Subtype.val (T.pieceSystem_map_succ d n (T.pieceProj d (n + 1) y))).trans
          (T.mem_piece.1 y.2 n).2 }

/-- The linear map sending an element of the limit of `pieceSystem d` to the compatible family
of its projections, an element of the degree-`d` piece. -/
def limitToPiece (d : ℕ) :
    (limit (T.pieceSystem d) : ModuleCat.{u} (limit Rg : CommRingCat.{u})) →ₗ[
      (limit Rg : CommRingCat.{u})] T.piece d where
  toFun x := ⟨fun n => ((limit.π (T.pieceSystem d) (op n) x : T.𝒜 n d) : T.A n),
    fun n => ⟨(limit.π (T.pieceSystem d) (op n) x : T.𝒜 n d).2, by
      have h := limit.w_apply (T.pieceSystem d) (homOfLE (Nat.le_succ n)).op x
      rw [pieceSystem_map_succ] at h
      exact congrArg Subtype.val h⟩⟩
  map_add' x y := by
    ext n
    exact congrArg Subtype.val (map_add (limit.π (T.pieceSystem d) (op n)).hom x y)
  map_smul' r x := by
    ext n
    exact congrArg Subtype.val (map_smul (limit.π (T.pieceSystem d) (op n)).hom r x)

/-- **The limit of the inverse system of degree-`d` pieces is the degree-`d` piece.** -/
def limitPieceEquiv (d : ℕ) :
    (limit (T.pieceSystem d) : ModuleCat.{u} (limit Rg : CommRingCat.{u})) ≃ₗ[
      (limit Rg : CommRingCat.{u})] T.piece d :=
  LinearEquiv.ofLinear (T.limitToPiece d) (limit.lift (T.pieceSystem d) (T.pieceCone d)).hom
    (by
      ext y n
      change ((limit.π (T.pieceSystem d) (op n) (limit.lift _ (T.pieceCone d) y) : T.𝒜 n d) :
        T.A n) = _
      rw [limit.lift_π_apply]
      rfl)
    (by
      ext x
      refine Concrete.limit_ext (T.pieceSystem d) _ _ fun i => ?_
      change limit.π (T.pieceSystem d) i
        (limit.lift _ (T.pieceCone d) (T.limitToPiece d x)) = _
      rw [limit.lift_π_apply]
      rfl)

/-- The `n`-th component of `limitPieceEquiv d x` is the projection of `x` to `(Aₙ)_d`. -/
theorem limitPieceEquiv_apply (d n : ℕ)
    (x : (limit (T.pieceSystem d) : ModuleCat.{u} (limit Rg : CommRingCat.{u}))) :
    ((T.limitPieceEquiv d x : ∀ n, T.A n) n) =
      ((limit.π (T.pieceSystem d) (op n) x : T.𝒜 n d) : T.A n) := rfl

/-- The limit ring acts compatibly on `Rₙ` and on `(Aₙ)_d`. -/
instance isScalarTower_piece (n d : ℕ) :
    IsScalarTower (limit Rg : CommRingCat.{u}) (Rg.obj (op n)) (T.𝒜 n d) :=
  ⟨fun r s x => Subtype.ext (smul_assoc r s (x : T.A n))⟩

/-- The degree-`d` transition map as a morphism of `Rₙ₊₁`-modules into the restriction of scalars
of `(Aₙ)_d`. -/
def trPieceHom (n d : ℕ) :
    ModuleCat.of (Rg.obj (op (n + 1))) (T.𝒜 (n + 1) d) ⟶
      (ModuleCat.restrictScalars (tr Rg n).hom).obj (ModuleCat.of (Rg.obj (op n)) (T.𝒜 n d)) :=
  ConcreteCategory.ofHom
    { toFun := fun x => T.trPiece n d x,
      map_add' := fun x y => map_add _ x y,
      map_smul' := fun s x => Subtype.ext <| by
        change T.ρ n (s • (x : T.A (n + 1))) = (tr Rg n).hom s • T.ρ n x
        rw [Algebra.smul_def, map_mul, T.ρ_algebraMap, ← Algebra.smul_def] }

/-- The morphism `trPieceHom n d` acts as the transition map `trPiece n d`. -/
theorem trPieceHom_apply (n d : ℕ) (x : T.𝒜 (n + 1) d) :
    T.trPieceHom n d x = T.trPiece n d x := rfl

variable {T}

/-- For an admissible tower, the degree-`d` piece of the graded inverse limit is a finite
projective module over the limit ring, whose base change to every `Rₙ` is `(Aₙ)_d` through the
projection `pieceProj d n`. -/
theorem finite_projective_baseChange_piece (hT : T.IsAdmissible) (d : ℕ) :
    Module.Finite (limit Rg : CommRingCat.{u}) (T.piece d) ∧
      Module.Projective (limit Rg : CommRingCat.{u}) (T.piece d) ∧
      ∀ n : ℕ, ∃ e : Rg.obj (op n) ⊗[(limit Rg : CommRingCat.{u})] T.piece d
          ≃ₗ[Rg.obj (op n)] T.𝒜 n d,
        ∀ (a : Rg.obj (op n)) (y : T.piece d), e (a ⊗ₜ y) = a • T.pieceProj d n y := by
  obtain ⟨hf, hp, hbc⟩ := finiteProjective_limit_of_finiteFlat_of_isBaseChange Rg
    (limit.cone Rg) (limit.isLimit Rg) (T.pieceSystem d)
    (fun n => inferInstanceAs (Module (Rg.obj (op n)) (T.𝒜 n d)))
    (fun n => T.isScalarTower_piece n d)
    (fun n => T.trPieceHom n d)
    (fun n x => (T.pieceSystem_map_succ d n x).symm)
    (fun n => ⟨hT.surjective n, hT.ker_le_nilradical n⟩)
    ⟨hT.finite 0 d, hT.projective 0 d⟩
    (fun n => ⟨hT.finite n d, by
      have := hT.projective n d
      exact (inferInstance : Module.Flat (Rg.obj (op n)) (T.𝒜 n d))⟩)
    (fun n => ⟨LinearEquiv.ofBijective (T.baseChangeMap n d) (hT.baseChange_bijective n d),
      fun a x => (T.baseChangeMap_tmul n d a x).trans rfl⟩)
  let E := T.limitPieceEquiv d
  have : Module.Finite (limit Rg : CommRingCat.{u})
      (limit (T.pieceSystem d) : ModuleCat.{u} (limit Rg : CommRingCat.{u})) := hf
  have : Module.Projective (limit Rg : CommRingCat.{u})
      (limit (T.pieceSystem d) : ModuleCat.{u} (limit Rg : CommRingCat.{u})) := hp
  refine ⟨Module.Finite.equiv E, Module.Projective.of_equiv E, fun n => ?_⟩
  obtain ⟨e, he⟩ := hbc n
  let e' : Rg.obj (op n) ⊗[(limit Rg : CommRingCat.{u})]
      (limit (T.pieceSystem d) : ModuleCat.{u} (limit Rg : CommRingCat.{u}))
        ≃ₗ[Rg.obj (op n)] T.𝒜 n d := e
  refine ⟨(LinearEquiv.baseChange (limit Rg : CommRingCat.{u}) (Rg.obj (op n)) _ _ E.symm).trans
    e', fun a y => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  refine (he a (E.symm y)).trans ?_
  congr 1
  refine Subtype.ext ?_
  have h := T.limitPieceEquiv_apply d n (E.symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end GradedTower

end Stacks.GradedTowerLimit
