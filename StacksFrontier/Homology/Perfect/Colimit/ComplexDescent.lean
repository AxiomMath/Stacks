module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Colimit.ModuleDescent
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Perfect complexes over filtered colimits of rings: descent of complexes

Bounded complexes of finite projective modules over the colimit `c.pt` of a filtered system of
commutative rings `R : I ⥤ CommRingCat` descend to a finite stage, through their models by
idempotent and square-zero matrices; consequently every perfect object of the derived category of
`c.pt`-modules is the derived extension of scalars of a perfect object over some `R.obj i`.
This is the descent half of [stacks 0BC7].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct

open scoped Matrix

universe uI uR uM uA

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- Expressions in a finite collection of square matrices. -/
private inductive MatrixExpr (α : Type uA) where
  | atom (a : α) : MatrixExpr α
  | zero : MatrixExpr α
  | one : MatrixExpr α
  | add (x y : MatrixExpr α) : MatrixExpr α
  | mul (x y : MatrixExpr α) : MatrixExpr α

private def MatrixExpr.eval {α : Type uA} {n : Type uA} [Fintype n] [DecidableEq n]
    {S : Type uR} [CommRing S] (M : α → Matrix n n S) :
    MatrixExpr α → Matrix n n S
  | .atom a => M a
  | .zero => 0
  | .one => 1
  | .add x y => x.eval M + y.eval M
  | .mul x y => x.eval M * y.eval M

/-- Evaluation of matrix expressions commutes with scalar extension. -/
private theorem MatrixExpr.eval_map
    {α : Type uA} {n : Type uA} [Fintype n] [DecidableEq n]
    {S T : Type uR} [CommRing S] [CommRing T]
    (f : S →+* T) (M : α → Matrix n n S) (e : MatrixExpr α) :
    (e.eval M).map f = e.eval (fun a => (M a).map f) := by
  induction e with
  | atom a => rfl
  | zero => simp [MatrixExpr.eval]
  | one => simp [MatrixExpr.eval]
  | add x y hx hy => simp only [MatrixExpr.eval, Matrix.map_add f f.map_add, hx, hy]
  | mul x y hx hy => simp only [MatrixExpr.eval, Matrix.map_mul, hx, hy]

/-- If finitely many polynomial matrix relations hold after passage to the colimit, they
already hold after one transition from the given stage. -/
private theorem matrix_presentation_eventually
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {n α β : Type uA} [Fintype n] [DecidableEq n] [Finite β]
    (i : I) (M : α → Matrix n n (R.obj i))
    (lhs rhs : β → MatrixExpr α)
    (h : ∀ b, (lhs b).eval (fun a => (M a).map (c.ι.app i).hom) =
      (rhs b).eval (fun a => (M a).map (c.ι.app i).hom)) :
    ∃ (j : I) (f : i ⟶ j),
      ∀ b, (lhs b).eval (fun a => (M a).map (R.map f).hom) =
        (rhs b).eval (fun a => (M a).map (R.map f).hom) := by
  classical
  have heq (t : β × n × n) :
      (c.ι.app i).hom (((lhs t.1).eval M) t.2.1 t.2.2) =
        (c.ι.app i).hom (((rhs t.1).eval M) t.2.1 t.2.2) := by
    have h' : ((lhs t.1).eval M).map (c.ι.app i).hom =
        ((rhs t.1).eval M).map (c.ι.app i).hom := by
      rw [MatrixExpr.eval_map, MatrixExpr.eval_map]
      exact h t.1
    exact congrArg (fun X : Matrix n n c.pt => X t.2.1 t.2.2) h'
  obtain ⟨j, f, hf⟩ := finite_stage_eq R c hc i
    (fun t : β × n × n => ((lhs t.1).eval M) t.2.1 t.2.2)
    (fun t : β × n × n => ((rhs t.1).eval M) t.2.1 t.2.2) heq
  refine ⟨j, f, ?_⟩
  intro b
  rw [← MatrixExpr.eval_map, ← MatrixExpr.eval_map]
  ext p q
  exact hf (b, p, q)

/-- A finite presentation by matrix generators and polynomial relations descends to one stage.
The relations can encode idempotents, zero composites, and compatibility of maps between
projective summands. -/
private theorem matrix_presentation_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {n α β : Type uA} [Fintype n] [DecidableEq n] [Finite α] [Finite β]
    (M : α → Matrix n n c.pt) (lhs rhs : β → MatrixExpr α)
    (h : ∀ b, (lhs b).eval M = (rhs b).eval M) :
    ∃ (j : I) (N : α → Matrix n n (R.obj j)),
      (∀ b, (lhs b).eval N = (rhs b).eval N) ∧
      (∀ a, (N a).map (c.ι.app j).hom = M a) := by
  classical
  obtain ⟨j, y, hy⟩ := finite_stage_exists R c hc
    (fun t : α × n × n => M t.1 t.2.1 t.2.2)
  let N : α → Matrix n n (R.obj j) := fun a p q => y (a, p, q)
  have hN (a : α) : (N a).map (c.ι.app j).hom = M a := by
    ext p q
    exact hy (a, p, q)
  obtain ⟨k, f, hf⟩ := matrix_presentation_eventually R c hc j N lhs rhs
    (fun b => by simp only [hN]; exact h b)
  exact ⟨k, fun a => (N a).map (R.map f).hom, hf,
    fun a => (matrix_map_cocone R c f (N a)).trans (hN a)⟩

/-- Left-hand sides of the relations on idempotents `E` and differentials `D`. -/
private def differentialRelLhs {α : Type uA} (next : α → α) :
    Sum α (Sum α (Sum α α)) → MatrixExpr (Sum α α)
  | .inl a => .mul (.atom (.inl a)) (.atom (.inl a))
  | .inr (.inl a) => .mul (.atom (.inl (next a))) (.atom (.inr a))
  | .inr (.inr (.inl a)) => .mul (.atom (.inr a)) (.atom (.inl a))
  | .inr (.inr (.inr a)) => .mul (.atom (.inr (next a))) (.atom (.inr a))

/-- Right-hand sides of the relations on idempotents `E` and differentials `D`. -/
private def differentialRelRhs {α : Type uA} :
    Sum α (Sum α (Sum α α)) → MatrixExpr (Sum α α)
  | .inl a => .atom (.inl a)
  | .inr (.inl a) => .atom (.inr a)
  | .inr (.inr (.inl a)) => .atom (.inr a)
  | .inr (.inr (.inr _)) => .zero

/-- The relations encode idempotency, compatibility on both sides, and square zero. -/
private theorem differentialRel_iff
    {α n : Type uA} [Fintype n] [DecidableEq n] {S : Type uR} [CommRing S]
    (next : α → α) (M : Sum α α → Matrix n n S) :
    (∀ t, (differentialRelLhs next t).eval M = (differentialRelRhs t).eval M) ↔
    (∀ a, M (.inl a) * M (.inl a) = M (.inl a)) ∧
      (∀ a, M (.inl (next a)) * M (.inr a) = M (.inr a)) ∧
      (∀ a, M (.inr a) * M (.inl a) = M (.inr a)) ∧
      (∀ a, M (.inr (next a)) * M (.inr a) = 0) := by
  constructor
  · intro h
    refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_⟩
    · simpa [differentialRelLhs, differentialRelRhs, MatrixExpr.eval] using h (.inl a)
    · simpa [differentialRelLhs, differentialRelRhs, MatrixExpr.eval] using h (.inr (.inl a))
    · simpa [differentialRelLhs, differentialRelRhs, MatrixExpr.eval] using
        h (.inr (.inr (.inl a)))
    · simpa [differentialRelLhs, differentialRelRhs, MatrixExpr.eval] using
        h (.inr (.inr (.inr a)))
  · rintro ⟨hE, hleft, hright, hsquare⟩ (a | a | a | a) <;>
      simp [differentialRelLhs, differentialRelRhs, MatrixExpr.eval, hE, hleft, hright, hsquare]

/-- A finite system of projective summands represented in one finite free module, together
with compatible square-zero differentials, descends to a single stage. -/
private theorem uniform_projective_differentials_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {α n : Type uA} [Finite α] [Fintype n]
    (next : α → α) (E D : α → Matrix n n c.pt)
    (hE : ∀ a, E a * E a = E a)
    (hleft : ∀ a, E (next a) * D a = D a)
    (hright : ∀ a, D a * E a = D a)
    (hsquare : ∀ a, D (next a) * D a = 0) :
    ∃ (j : I) (E' D' : α → Matrix n n (R.obj j)),
      (∀ a, E' a * E' a = E' a) ∧
      (∀ a, E' (next a) * D' a = D' a) ∧
      (∀ a, D' a * E' a = D' a) ∧
      (∀ a, D' (next a) * D' a = 0) ∧
      (∀ a, (E' a).map (c.ι.app j).hom = E a) ∧
      (∀ a, (D' a).map (c.ι.app j).hom = D a) := by
  classical
  obtain ⟨j, N, hN, hmap⟩ := matrix_presentation_stage_exists R c hc (Sum.elim E D)
    (differentialRelLhs next) differentialRelRhs
    ((differentialRel_iff next _).2 ⟨hE, hleft, hright, hsquare⟩)
  obtain ⟨h1, h2, h3, h4⟩ := (differentialRel_iff next N).1 hN
  exact ⟨j, fun a => N (.inl a), fun a => N (.inr a), h1, h2, h3, h4,
    fun a => hmap (.inl a), fun a => hmap (.inr a)⟩

/-- A finite system of projective summands and differentials already present at one stage
acquires its idempotent, compatibility, and square-zero equations after one transition if
those equations hold over the colimit. -/
private theorem uniform_projective_differentials_eventually
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {α n : Type uA} [Finite α] [Fintype n]
    (i : I) (next : α → α) (E D : α → Matrix n n (R.obj i))
    (hE : ∀ a, (E a).map (c.ι.app i).hom * (E a).map (c.ι.app i).hom =
      (E a).map (c.ι.app i).hom)
    (hleft : ∀ a, (E (next a)).map (c.ι.app i).hom *
      (D a).map (c.ι.app i).hom = (D a).map (c.ι.app i).hom)
    (hright : ∀ a, (D a).map (c.ι.app i).hom *
      (E a).map (c.ι.app i).hom = (D a).map (c.ι.app i).hom)
    (hsquare : ∀ a, (D (next a)).map (c.ι.app i).hom *
      (D a).map (c.ι.app i).hom = 0) :
    ∃ (j : I) (f : i ⟶ j),
      (∀ a, (E a).map (R.map f).hom * (E a).map (R.map f).hom =
        (E a).map (R.map f).hom) ∧
      (∀ a, (E (next a)).map (R.map f).hom * (D a).map (R.map f).hom =
        (D a).map (R.map f).hom) ∧
      (∀ a, (D a).map (R.map f).hom * (E a).map (R.map f).hom =
        (D a).map (R.map f).hom) ∧
      (∀ a, (D (next a)).map (R.map f).hom * (D a).map (R.map f).hom = 0) := by
  classical
  obtain ⟨j, f, hf⟩ := matrix_presentation_eventually R c hc i (Sum.elim E D)
    (differentialRelLhs next) differentialRelRhs
    ((differentialRel_iff next _).2 ⟨hE, hleft, hright, hsquare⟩)
  exact ⟨j, f, (differentialRel_iff next _).1 hf⟩

/-- Composition of linear maps given by matrices whose product is known. -/
private theorem toLin'_comp_of_mul_eq {A : Type uR} [CommRing A] {n : Type uA} [Fintype n]
    [DecidableEq n] {X Y Z : Matrix n n A} (h : X * Y = Z) :
    (Matrix.toLin' X).comp (Matrix.toLin' Y) = Matrix.toLin' Z := by
  rw [← Matrix.toLin'_mul, h]

/-- A matrix compatible with two idempotents induces a map between their image modules. -/
private noncomputable def idempotentDifferential
    {A : Type uR} [CommRing A]
    {α : Type uA} {n : Type uA} [Fintype n] [DecidableEq n]
    (next : α → α) (E D : α → Matrix n n A)
    (hleft : ∀ a, E (next a) * D a = D a) (a : α) :
    (Matrix.toLin' (E a)).range →ₗ[A] (Matrix.toLin' (E (next a))).range := by
  let u := Matrix.toLin' (D a)
  let v := Matrix.toLin' (E (next a))
  have hv : v.comp u = u := toLin'_comp_of_mul_eq (hleft a)
  refine (u.comp (Matrix.toLin' (E a)).range.subtype).codRestrict v.range ?_
  intro x
  refine ⟨u x.1, ?_⟩
  change v (u x.1) = u x.1
  rw [← LinearMap.comp_apply, hv]

/-- Matrix square-zero equations imply that the induced maps between projective summands
compose to zero. -/
private theorem idempotentDifferential_comp_zero
    {A : Type uR} [CommRing A]
    {α : Type uA} {n : Type uA} [Fintype n] [DecidableEq n]
    (next : α → α) (E D : α → Matrix n n A)
    (hleft : ∀ a, E (next a) * D a = D a)
    (hsquare : ∀ a, D (next a) * D a = 0) (a : α) :
    (idempotentDifferential next E D hleft (next a)).comp
      (idempotentDifferential next E D hleft a) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Matrix.toLin' (D (next a)) (Matrix.toLin' (D a) x.1) = 0
  have h := toLin'_comp_of_mul_eq (hsquare a)
  simpa using DFunLike.congr_fun h x.1

/-- A sequence of idempotent matrices and compatible square-zero matrices defines a
cochain complex of their image modules. -/
private noncomputable def idempotentComplex
    {A : Type uR} [CommRing A] (n : ℕ)
    (E D : ℤ → Matrix (Fin n) (Fin n) A)
    (hleft : ∀ i, E (i + 1) * D i = D i)
    (hsquare : ∀ i, D (i + 1) * D i = 0) :
    CochainComplex (ModuleCat.{max uM uR} A) ℤ := by
  apply ((ModuleCat.uliftFunctor.{uM, uR} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  refine CochainComplex.of
    (fun i => ModuleCat.of A (Matrix.toLin' (E i)).range)
    (fun i => ModuleCat.ofHom
      (idempotentDifferential (fun j : ℤ => j + 1) E D hleft i))
    fun i => ModuleCat.hom_ext
      (idempotentDifferential_comp_zero (fun j : ℤ => j + 1) E D hleft hsquare i)

/-- Each term of the complex constructed from idempotent matrices is finite projective. -/
private theorem idempotentComplex_finite_projective
    {A : Type uR} [CommRing A] (n : ℕ)
    (E D : ℤ → Matrix (Fin n) (Fin n) A)
    (hE : ∀ i, E i * E i = E i)
    (hleft : ∀ i, E (i + 1) * D i = D i)
    (hsquare : ∀ i, D (i + 1) * D i = 0) (i : ℤ) :
    Module.Finite A ((idempotentComplex.{uR, uM} n E D hleft hsquare).X i) ∧
      Module.Projective A ((idempotentComplex.{uR, uM} n E D hleft hsquare).X i) := by
  obtain ⟨hf, hp⟩ := idempotent_range_finite_projective n (Matrix.toLin' (E i))
    (toLin'_comp_of_mul_eq (hE i))
  have := hf
  have := hp
  change Module.Finite A (ULift.{uM} (Matrix.toLin' (E i)).range) ∧
    Module.Projective A (ULift.{uM} (Matrix.toLin' (E i)).range)
  constructor <;> infer_instance

/-- Zero idempotent matrices outside an interval give strict bounds on the resulting
cochain complex. -/
private theorem idempotentComplex_bounded
    {A : Type uR} [CommRing A] (n : ℕ)
    (E D : ℤ → Matrix (Fin n) (Fin n) A)
    (hleft : ∀ i, E (i + 1) * D i = D i)
    (hsquare : ∀ i, D (i + 1) * D i = 0)
    (a b : ℤ) (hbelow : ∀ i < a, E i = 0)
    (habove : ∀ i > b, E i = 0) :
    (idempotentComplex.{uR, uM} n E D hleft hsquare).IsStrictlyGE a ∧
      (idempotentComplex.{uR, uM} n E D hleft hsquare).IsStrictlyLE b := by
  have hzero (i : ℤ) (h : E i = 0) :
      IsZero ((idempotentComplex.{uR, uM} n E D hleft hsquare).X i) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (ULift.{uM} (Matrix.toLin' (E i)).range)
    rw [h, map_zero, LinearMap.range_zero]
    infer_instance
  exact ⟨CochainComplex.isStrictlyGE_iff _ _ |>.2 fun i hi => hzero i (hbelow i hi),
    CochainComplex.isStrictlyLE_iff _ _ |>.2 fun i hi => hzero i (habove i hi)⟩


/-- A finite family of finite projective modules admits retractions from a common finite
free module. -/
private theorem finite_projective_family_retract
    {A : Type uR} [CommRing A] {α : Type} [Finite α]
    (P : α → ModuleCat.{max uM uR} A)
    [∀ i, Module.Finite A (P i)] [∀ i, Module.Projective A (P i)] :
    ∃ (n : ℕ) (f : ∀ i, (Fin n → A) →ₗ[A] P i)
      (g : ∀ i, P i →ₗ[A] (Fin n → A)),
      ∀ i, (f i).comp (g i) = LinearMap.id := by
  classical
  let := Fintype.ofFinite α
  have : Module.Projective A (∀ i, P i) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := A) (M := fun i => P i))
  obtain ⟨n, f, g, hfg, _⟩ := finite_projective_retract (A := A) (∀ i, P i)
  refine ⟨n, (fun i => (LinearMap.proj i).comp f),
    (fun i => g.comp (LinearMap.single A (fun i => P i) i)), ?_⟩
  intro i
  apply LinearMap.ext
  intro x
  change (f (g (Pi.single i x))) i = x
  rw [← LinearMap.comp_apply f g, hfg]
  simp

/-- The terms of a bounded complex of finite projectives are retractions of one finite
free module, with zero retraction maps outside the bounds. -/
private theorem bounded_projective_retract
    {A : Type uR} [CommRing A]
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Projective A (P.X i)] :
    ∃ (n : ℕ) (f : ∀ i, (Fin n → A) →ₗ[A] P.X i)
      (g : ∀ i, P.X i →ₗ[A] (Fin n → A)),
      (∀ i, (f i).comp (g i) = LinearMap.id) ∧
      (∀ i, i ∉ Finset.Icc a b → f i = 0 ∧ g i = 0) := by
  classical
  obtain ⟨n, f, g, hfg⟩ := finite_projective_family_retract
    (fun i : Finset.Icc a b => P.X i)
  let f' (i : ℤ) : (Fin n → A) →ₗ[A] P.X i :=
    if h : i ∈ Finset.Icc a b then f ⟨i, h⟩ else 0
  let g' (i : ℤ) : P.X i →ₗ[A] (Fin n → A) :=
    if h : i ∈ Finset.Icc a b then g ⟨i, h⟩ else 0
  refine ⟨n, f', g', ?_, fun i hi => by simp only [f', g', dite_eq_right hi, and_self]⟩
  intro i
  by_cases hi : i ∈ Finset.Icc a b
  · simpa only [f', g', dite_eq_left hi] using hfg ⟨i, hi⟩
  · have hz : IsZero (P.X i) := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hi
      rcases hi with hi | hi
      · exact P.isZero_of_isStrictlyGE a i hi
      · exact P.isZero_of_isStrictlyLE b i hi
    have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.1 hz
    exact Subsingleton.elim _ _

/-- Retractions of the terms of a complex encode its differentials as square matrices. -/
private theorem projective_retract_matrices
    {A : Type uR} [CommRing A]
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (n : ℕ)
    (f : ∀ i, (Fin n → A) →ₗ[A] P.X i)
    (g : ∀ i, P.X i →ₗ[A] (Fin n → A))
    (hfg : ∀ i, (f i).comp (g i) = LinearMap.id) :
    let E := fun i => LinearMap.toMatrix' ((g i).comp (f i))
    let D := fun i => LinearMap.toMatrix'
      ((g (i + 1)).comp ((P.d i (i + 1)).hom.comp (f i)))
    (∀ i, E i * E i = E i) ∧
      (∀ i, E (i + 1) * D i = D i) ∧
      (∀ i, D i * E i = D i) ∧
      (∀ i, D (i + 1) * D i = 0) := by
  dsimp only
  have hfg_apply (i : ℤ) (x : P.X i) : f i (g i x) = x :=
    DFunLike.congr_fun (hfg i) x
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  iterate 3
    rw [← LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, hfg_apply])
  · rw [← LinearMap.toMatrix'_comp, ← map_zero LinearMap.toMatrix']
    apply congrArg LinearMap.toMatrix'
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, hfg_apply, LinearMap.zero_apply]
    have hd : (P.d (i + 1) (i + 1 + 1)).hom ((P.d i (i + 1)).hom (f i x)) = 0 := by
      change ((P.d i (i + 1) ≫ P.d (i + 1) (i + 1 + 1)).hom) (f i x) = 0
      rw [P.d_comp_d]
      rfl
    rw [hd, map_zero]

/-- Finite families of matrices supported on a fixed finite set lift to one stage, with
the same support. -/
private theorem supported_matrix_family_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {α : Type} [Finite α] (s : Finset ℤ) (n : ℕ)
    (M : α → ℤ → Matrix (Fin n) (Fin n) c.pt)
    (hs : ∀ a i, i ∉ s → M a i = 0) :
    ∃ (j : I) (N : α → ℤ → Matrix (Fin n) (Fin n) (R.obj j)),
      (∀ a i, (N a i).map (c.ι.app j).hom = M a i) ∧
      (∀ a i, i ∉ s → N a i = 0) := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨j, v, hv⟩ := finite_stage_exists R c hc
    (fun t : α × s × Fin n × Fin n => M t.1 t.2.1 t.2.2.1 t.2.2.2)
  let N (a : α) (i : ℤ) : Matrix (Fin n) (Fin n) (R.obj j) :=
    if hi : i ∈ s then fun p q => v (a, ⟨i, hi⟩, p, q) else 0
  have hpos (a : α) (i : ℤ) (hi : i ∈ s) :
      N a i = fun p q => v (a, ⟨i, hi⟩, p, q) := dite_eq_left hi
  have hneg (a : α) (i : ℤ) (hi : i ∉ s) : N a i = 0 := dite_eq_right hi
  refine ⟨j, N, ?_, hneg⟩
  intro a i
  by_cases hi : i ∈ s
  · rw [hpos a i hi]
    ext p q
    exact hv (a, ⟨i, hi⟩, p, q)
  · rw [hneg a i hi, hs a i hi]
    exact Matrix.map_zero _ (map_zero _)

/-- A bounded system of idempotents and differentials descends with its support and all
its equations. -/
private theorem bounded_projective_differentials_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c) (s : Finset ℤ) (n : ℕ)
    (E D : ℤ → Matrix (Fin n) (Fin n) c.pt)
    (hE : ∀ i, E i * E i = E i)
    (hleft : ∀ i, E (i + 1) * D i = D i)
    (hright : ∀ i, D i * E i = D i)
    (hsquare : ∀ i, D (i + 1) * D i = 0)
    (hs : ∀ i, i ∉ s → E i = 0 ∧ D i = 0) :
    ∃ (j : I) (E' D' : ℤ → Matrix (Fin n) (Fin n) (R.obj j)),
      (∀ i, E' i * E' i = E' i) ∧
      (∀ i, E' (i + 1) * D' i = D' i) ∧
      (∀ i, D' i * E' i = D' i) ∧
      (∀ i, D' (i + 1) * D' i = 0) ∧
      (∀ i, (E' i).map (c.ι.app j).hom = E i) ∧
      (∀ i, (D' i).map (c.ι.app j).hom = D i) ∧
      (∀ i, i ∉ s → E' i = 0 ∧ D' i = 0) := by
  classical
  let M : Bool → ℤ → Matrix (Fin n) (Fin n) c.pt
    | false => E
    | true => D
  obtain ⟨j, N, hN, hNs⟩ := supported_matrix_family_stage_exists R c hc s n M
    (fun a i hi => by cases a; exacts [(hs i hi).1, (hs i hi).2])
  let lhs : Fin 4 × s → Matrix (Fin n) (Fin n) (R.obj j) := fun t =>
    if t.1 = 0 then N false t.2 * N false t.2
    else if t.1 = 1 then N false (t.2 + 1) * N true t.2
    else if t.1 = 2 then N true t.2 * N false t.2
    else N true (t.2 + 1) * N true t.2
  let rhs : Fin 4 × s → Matrix (Fin n) (Fin n) (R.obj j) := fun t =>
    if t.1 = 0 then N false t.2 else if t.1 = 3 then 0 else N true t.2
  have heq (t : (Fin 4 × s) × Fin n × Fin n) :
      (c.ι.app j).hom (lhs t.1 t.2.1 t.2.2) =
        (c.ι.app j).hom (rhs t.1 t.2.1 t.2.2) := by
    have h : (lhs t.1).map (c.ι.app j).hom = (rhs t.1).map (c.ι.app j).hom := by
      rcases t with ⟨⟨k, i⟩, p, q⟩
      fin_cases k <;> simp [lhs, rhs, Matrix.map_mul, hN, M, hE, hleft, hright, hsquare]
    exact congrArg (fun X => X t.2.1 t.2.2) h
  obtain ⟨k, f, hf⟩ := finite_stage_eq R c hc j
    (fun t : (Fin 4 × s) × Fin n × Fin n => lhs t.1 t.2.1 t.2.2)
    (fun t : (Fin 4 × s) × Fin n × Fin n => rhs t.1 t.2.1 t.2.2) heq
  have hrel (t : Fin 4 × s) : (lhs t).map (R.map f).hom = (rhs t).map (R.map f).hom := by
    ext p q
    exact hf (t, p, q)
  let E' := fun i => (N false i).map (R.map f).hom
  let D' := fun i => (N true i).map (R.map f).hom
  have hs' (i : ℤ) (hi : i ∉ s) : E' i = 0 ∧ D' i = 0 := by
    simp [E', D', hNs _ i hi]
  refine ⟨k, E', D', fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => (matrix_map_cocone R c f (N false i)).trans (hN false i),
    fun i => (matrix_map_cocone R c f (N true i)).trans (hN true i), hs'⟩
  · by_cases hi : i ∈ s
    · simpa [lhs, rhs, E', D', Matrix.map_mul] using hrel (0, ⟨i, hi⟩)
    · simp [(hs' i hi).1]
  · by_cases hi : i ∈ s
    · simpa [lhs, rhs, E', D', Matrix.map_mul] using hrel (1, ⟨i, hi⟩)
    · simp [(hs' i hi).2]
  · by_cases hi : i ∈ s
    · simpa [lhs, rhs, E', D', Matrix.map_mul] using hrel (2, ⟨i, hi⟩)
    · simp [(hs' i hi).2]
  · by_cases hi : i ∈ s
    · simpa [lhs, rhs, E', D', Matrix.map_mul] using hrel (3, ⟨i, hi⟩)
    · simp [(hs' i hi).2]

/-- The image model of a split summand sends an element to its given inclusion. -/
private theorem split_range_equiv_apply
    {A : Type uR} [CommRing A]
    {P : Type uM} {M : Type uA} [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M]
    (i : P →ₗ[A] M) (r : M →ₗ[A] P) (h : r.comp i = LinearMap.id) (x : P) :
    (split_range_equiv i r h x).1 = i x := rfl

/-- A complex whose terms split from one finite free module is isomorphic to its matrix
image model. -/
private noncomputable def projective_retract_complex_iso
    {A : Type uR} [CommRing A]
    (P : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (n : ℕ)
    (f : ∀ i, (Fin n → A) →ₗ[A] P.X i)
    (g : ∀ i, P.X i →ₗ[A] (Fin n → A))
    (hfg : ∀ i, (f i).comp (g i) = LinearMap.id) :
    let E := fun i => LinearMap.toMatrix' ((g i).comp (f i))
    let D := fun i => LinearMap.toMatrix'
      ((g (i + 1)).comp ((P.d i (i + 1)).hom.comp (f i)))
    let h := projective_retract_matrices P n f g hfg
    P ≅ idempotentComplex.{uR, uM} n E D h.2.1 h.2.2.2 := by
  let E := fun i => LinearMap.toMatrix' ((g i).comp (f i))
  let D := fun i => LinearMap.toMatrix'
    ((g (i + 1)).comp ((P.d i (i + 1)).hom.comp (f i)))
  let h := projective_retract_matrices P n f g hfg
  let e (i : ℤ) : P.X i ≃ₗ[A] (Matrix.toLin' (E i)).range := by
    exact (split_range_equiv (g i) (f i) (hfg i)).trans
      (LinearEquiv.ofEq _ _ (congrArg LinearMap.range (Matrix.toLin'_toMatrix' _).symm))
  have he (i : ℤ) (x : P.X i) : (e i x).1 = g i x := rfl
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => ((e i).trans ULift.moduleEquiv.symm).toModuleIso) ?_
  intro i j hij
  obtain rfl : j = i + 1 := hij.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply Subtype.ext
  dsimp only [idempotentComplex, Functor.mapHomologicalComplex_obj_d]
  rw [CochainComplex.of_d]
  change Matrix.toLin' (D i) (e i x).1 = (e (i + 1) ((P.d i (i + 1)).hom x)).1
  rw [he, he]
  simp only [D, Matrix.toLin'_toMatrix', LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (f i) (g i) x, hfg]
  rfl

/-- The scalar extension of an idempotent image is carried into free coordinates by the
scalar extension of the inclusion. -/
private theorem idempotent_range_baseChange_equiv_apply
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ)
    (e : (Fin n → A) →ₗ[A] (Fin n → A)) (he : e.comp e = e) :
    letI : Algebra A B := f.toAlgebra
    ∀ x : B ⊗[A] e.range,
      (idempotent_range_baseChange_equiv f n e he x).1 =
        finite_free_baseChange_equiv f n (e.range.subtype.baseChange B x) := by
  let : Algebra A B := f.toAlgebra
  intro x
  rfl

/-- Scalar extension identifies the lifted image of an idempotent matrix with the lifted
image of its entrywise scalar extension. -/
private noncomputable def idempotentMatrixRangeBaseChange
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E) :
    letI : Algebra A B := f.toAlgebra
    (B ⊗[A] ULift.{uM} (Matrix.toLin' E).range) ≃ₗ[B]
      ULift.{uM} (Matrix.toLin' (E.map f)).range := by
  letI : Algebra A B := f.toAlgebra
  exact (LinearEquiv.baseChange A B _ _ ULift.moduleEquiv).trans
    ((idempotent_range_baseChange_equiv f n (Matrix.toLin' E) (toLin'_comp_of_mul_eq hE)).trans
      ((LinearEquiv.ofEq _ _ (by rw [LinearMap.toMatrix'_toLin'])).trans
        ULift.moduleEquiv.symm))

set_option backward.isDefEq.respectTransparency false in
/-- In free coordinates the scalar-extension comparison on an idempotent image has the
usual tensor formula. -/
private theorem idempotentMatrixRangeBaseChange_tmul
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E) :
    letI : Algebra A B := f.toAlgebra
    ∀ (b : B) (x : ULift.{uM} (Matrix.toLin' E).range),
      ((idempotentMatrixRangeBaseChange f n E hE (b ⊗ₜ[A] x)).down).1 =
        fun j => b * f (x.down.1 j) := by
  let : Algebra A B := f.toAlgebra
  intro b x
  change (idempotent_range_baseChange_equiv f n (Matrix.toLin' E) (toLin'_comp_of_mul_eq hE)
    ((LinearEquiv.baseChange A B _ _ ULift.moduleEquiv) (b ⊗ₜ[A] x))).1 = _
  rw [idempotent_range_baseChange_equiv_apply]
  ext j
  simp [finite_free_baseChange_equiv, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The idempotent matrix model of a complex commutes with extension of scalars. -/
private noncomputable def idempotentComplexBaseChange
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (E D : ℤ → Matrix (Fin n) (Fin n) A)
    (hE : ∀ i, E i * E i = E i)
    (hleft : ∀ i, E (i + 1) * D i = D i)
    (hsquare : ∀ i, D (i + 1) * D i = 0) :
    ((ModuleCat.extendScalars.{uR, uR, max uM uR} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (idempotentComplex.{uR, uM} n E D hleft hsquare) ≅
      idempotentComplex.{uR, uM} n (fun i => (E i).map f) (fun i => (D i).map f)
        (fun i => by rw [← Matrix.map_mul, hleft])
        (fun i => by rw [← Matrix.map_mul, hsquare]; simp) := by
  letI : Algebra A B := f.toAlgebra
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (idempotentMatrixRangeBaseChange f n (E i) (hE i)).toModuleIso) ?_
  intro i j hij
  obtain rfl : j = i + 1 := hij.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change B ⊗[A] ULift.{uM} (Matrix.toLin' (E i)).range at z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b x =>
    apply ULift.ext
    apply Subtype.ext
    dsimp only [idempotentComplex, Functor.mapHomologicalComplex_obj_d]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    change Matrix.toLin' ((D i).map f)
        ((idempotentMatrixRangeBaseChange f n (E i) (hE i) (b ⊗ₜ[A] x)).down).1 =
      ((idempotentMatrixRangeBaseChange f n (E (i + 1)) (hE (i + 1))
        (b ⊗ₜ[A] _)).down).1
    rw [idempotentMatrixRangeBaseChange_tmul, idempotentMatrixRangeBaseChange_tmul]
    change (D i).map f *ᵥ (fun j => b * f (x.down.1 j)) =
      fun j => b * f ((D i *ᵥ x.down.1) j)
    have hvec : (fun j => b * f (x.down.1 j)) = b • (f ∘ x.down.1) := rfl
    rw [hvec, Matrix.mulVec_smul]
    ext j
    change b * ((D i).map f *ᵥ (f ∘ x.down.1)) j = b * f ((D i *ᵥ x.down.1) j)
    rw [← RingHom.map_mulVec]

/-- A bounded complex of finite projective modules over a filtered colimit descends, with
its strict bounds, to a bounded complex of finite projectives at one stage. -/
private theorem bounded_projective_complex_descends
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    (P : CochainComplex (ModuleCat.{max uM uR} c.pt) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i, Module.Finite c.pt (P.X i)] [∀ i, Module.Projective c.pt (P.X i)] :
    ∃ (j : I) (Q : CochainComplex (ModuleCat.{max uM uR} (R.obj j)) ℤ),
      Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
      (∀ i, Module.Finite (R.obj j) (Q.X i)) ∧
      (∀ i, Module.Projective (R.obj j) (Q.X i)) ∧
      Nonempty (P ≅ ((ModuleCat.extendScalars.{uR, uR, max uM uR}
        (c.ι.app j).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) := by
  obtain ⟨n, f, g, hfg, hzero⟩ := bounded_projective_retract P a b
  let E := fun i => LinearMap.toMatrix' ((g i).comp (f i))
  let D := fun i => LinearMap.toMatrix'
    ((g (i + 1)).comp ((P.d i (i + 1)).hom.comp (f i)))
  obtain ⟨hE, hleft, hright, hsquare⟩ := projective_retract_matrices P n f g hfg
  have hs (i : ℤ) (hi : i ∉ Finset.Icc a b) : E i = 0 ∧ D i = 0 := by
    simp [E, D, (hzero i hi).1]
  obtain ⟨j, E', D', hE', hleft', _, hsquare', hmapE, hmapD, hs'⟩ :=
    bounded_projective_differentials_stage_exists R c hc (Finset.Icc a b) n E D
      hE hleft hright hsquare hs
  let Q := idempotentComplex.{uR, uM} n E' D' hleft' hsquare'
  obtain ⟨ha, hb⟩ := idempotentComplex_bounded.{uR, uM} n E' D' hleft' hsquare' a b
    (fun i hi => (hs' i (by simp only [Finset.mem_Icc]; omega)).1)
    (fun i hi => (hs' i (by simp only [Finset.mem_Icc]; omega)).1)
  have hfinite := idempotentComplex_finite_projective.{uR, uM} n E' D' hE' hleft' hsquare'
  refine ⟨j, Q, ha, hb, (fun i => (hfinite i).1), (fun i => (hfinite i).2), ?_⟩
  have ebase := idempotentComplexBaseChange.{uR, uM} (c.ι.app j).hom n E' D'
    hE' hleft' hsquare'
  simp only [hmapE, hmapD] at ebase
  exact ⟨projective_retract_complex_iso P n f g hfg ≪≫ ebase.symm⟩

/-- Perfect objects descend along filtered colimits of rings computed on underlying sets. -/
theorem perfect_object_descends (E : DerivedExtendScalars.{uR})
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    (K : DerivedCategory (ModuleCat.{uR} c.pt)) (hK : IsPerfect K) :
    ∃ (j : I) (Kj : DerivedCategory (ModuleCat.{uR} (R.obj j))),
      IsPerfect Kj ∧ Nonempty (K ≅
        (E (c.ι.app j).hom).functor.obj Kj) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨eP⟩⟩ := hK
  have := ha
  have := hb
  have := hf
  have := hp
  obtain ⟨j, Q, hQa, hQb, hQf, hQp, ⟨eQ⟩⟩ := bounded_projective_complex_descends R c hc P a b
  have := hQb
  have : ∀ i, Projective (Q.X i) := fun i => by
    have := hQp i
    infer_instance
  let E := E (c.ι.app j).hom
  have := E.comparison_isIso_of_projective Q b
  refine ⟨j, DerivedCategory.Q.obj Q, ⟨Q, a, b, hQa, hQb, hQf, hQp, ⟨Iso.refl _⟩⟩, ?_⟩
  exact ⟨eP ≪≫ DerivedCategory.Q.mapIso eQ ≪≫ (asIso (E.comparison.app Q)).symm⟩

end StacksDraft.Perfect

end
