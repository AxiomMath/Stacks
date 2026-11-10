module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration.CechNerve
public import StacksFrontier.Cotangent.CellAttachment
public import StacksFrontier.Cotangent.FiniteTypeCoskeletal
public import StacksFrontier.Cotangent.StandardResolution

/-!
# Polynomial simplicial resolutions

A finite type algebra over a Noetherian ring admits an augmented simplicial algebra whose terms
are polynomial algebras of finite type and whose underlying augmentation is a trivial Kan
fibration.

## Main results

* `CommAlgCat.exists_trivialKanFibration_from_finiteType_polynomial_simplicialAlgebra`: existence
  of the polynomial simplicial resolution.

## Implementation notes

A polynomial algebra of finite type is expressed by an algebra equivalence with
`MvPolynomial (Fin k) A` for some natural number `k`. The augmentation is a natural
transformation to the constant simplicial algebra on `B`; whiskering it with the forgetful
functor gives the map of simplicial sets to which the trivial Kan fibration condition applies.

The resolution is built one coskeletal stage at a time. At each stage new polynomial generators
are attached in the single degree `n + 1`, indexed by the surjections onto that simplex; the
resulting simplicial algebra is again degreewise polynomial, the comparison map to the previous
stage is a trivial Kan fibration, and the stages are eventually constant in every fixed degree,
so the limit of the tower is the required resolution.

The attachment of the new generators itself — a `CommAlgCat.CellBoundary` in a single degree, the
simplicial algebra `CommAlgCat.attachCells` obtained by adjoining one generator for each cell and
each surjection onto that degree, and the maps into and out of it — is
`StacksFrontier/Cotangent/CellAttachment.lean`, which states it for generators indexed by a `Type v`
over `CommAlgCat.{max u v} A`. It is used here at `v = 0`, generators indexed by `Type`, which is
all that Stacks 08PX needs; Stacks 09D4 in
`StacksFrontier/AlgebraicGeometry/Simplicial/Degeneracies/Degeneracies.lean` uses it at
`v = max u v'`.
The private `Cells` section below is the stagewise extension argument on top of it, in the finite
type form: each stage is a polynomial algebra in finitely many variables.

## References

* [Stacks Project, Tag 08PX](https://stacks.math.columbia.edu/tag/08PX)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u

namespace CommAlgCat

/-- Forgetting the map to `B` turns a simplicial object of `A`-algebras over `B` into an
augmented simplicial `A`-algebra. The augmentation on underlying simplicial sets is exactly the
canonical one used in the 08PW successor theorem. -/
private def overResolutionAugmentation {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : SimplicialObject (Over (CommAlgCat.of A B))) :
    P ⋙ Over.forget (CommAlgCat.of A B) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (CommAlgCat.of A B) where
  app j := (P.obj j).hom
  naturality _ _ f := Over.w (P.map f)

/-- An over-`B` resolution whose terms are finite-variable polynomial algebras gives the exact
publicly stated resolution after forgetting the structure maps to `B`. -/
private theorem exists_result_of_over_resolution {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (P : SimplicialObject (Over (CommAlgCat.of A B)))
    (hpoly : ∀ n : ℕ, ∃ k : ℕ, Nonempty
      ((P.obj (op (SimplexCategory.mk n))).left ≃ₐ[A] MvPolynomial (Fin k) A))
    (hkan : SSet.trivialKanFibrations (underlyingAugmentation A B P)) :
    ∃ (Q : SimplicialObject (CommAlgCat.{u} A))
      (ε : Q ⟶ (Functor.const _).obj (CommAlgCat.of A B)),
      (∀ n : ℕ, ∃ k : ℕ,
        Nonempty ((Q.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A)) ∧
      SSet.trivialKanFibrations
        (Functor.whiskerRight ε (CategoryTheory.forget (CommAlgCat.{u} A))) :=
  ⟨P ⋙ Over.forget (CommAlgCat.of A B), overResolutionAugmentation P, hpoly, hkan⟩

section Cells

variable {A : Type u} [CommRing A] {P : SimplicialObject (CommAlgCat.{u} A)}
  {d : ℕ} {I : Type}

private lemma finitePolynomial_attachCells (b : CellBoundary P d I) [Finite I]
    (hP : ∀ n : ℕ, ∃ k : ℕ, Nonempty
      ((P.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A)) :
    ∀ n : ℕ, ∃ k : ℕ, Nonempty
      (((attachCells b).obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A) := by
  classical
  intro n
  obtain ⟨k, ⟨e⟩⟩ := hP n
  let V := CellVariable d I ⦋n⦌
  let e' := (MvPolynomial.mapAlgEquiv V e).trans (MvPolynomial.sumAlgEquiv A V (Fin k)).symm
  let _ : Fintype (V ⊕ Fin k) := Fintype.ofFinite _
  exact ⟨Fintype.card (V ⊕ Fin k),
    ⟨e'.trans (MvPolynomial.renameEquiv A (Fintype.equivFin _))⟩⟩

/-- The unit of the `n`-coskeleton adjunction is an isomorphism in every degree at most `n`,
because it is an isomorphism after `n`-truncation. -/
public lemma isIso_cosk_unit_app {C : Type*} [Category C] [CategoryTheory.Limits.HasLimits C]
    (X : SimplicialObject C) (n : ℕ) (Δ : SimplexCategory) (hΔ : Δ.len ≤ n) :
    IsIso (((SimplicialObject.coskAdj n).unit.app X).app (op Δ)) :=
  NatIso.isIso_app_of_isIso
    ((SimplicialObject.truncation n).map ((SimplicialObject.coskAdj n).unit.app X))
    (op (⟨Δ, hΔ⟩ : SimplexCategory.Truncated n))

-- Elaborating the polynomial extension involves nested functor and algebra coercions.
private lemma exists_polynomial_extension {Q : SimplicialObject (CommAlgCat.{u} A)}
    (f : P ⟶ Q) (n : ℕ)
    (hf : ∀ k, k ≤ n → Function.Bijective (f.app (op ⦋k⦌)))
    (hP : ∀ n : ℕ, ∃ k : ℕ, Nonempty
      ((P.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A))
    (hQ : Algebra.FiniteType A (Q.obj (op ⦋n + 1⦌))) :
    ∃ (P' : SimplicialObject (CommAlgCat.{u} A)) (i : P ⟶ P') (q : P' ⟶ Q),
      i ≫ q = f ∧
      (∀ n : ℕ, ∃ k : ℕ, Nonempty
        ((P'.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A)) ∧
      (∀ k, k ≤ n → IsIso (i.app (op ⦋k⦌))) ∧
      Function.Surjective (q.app (op ⦋n + 1⦌)) := by
  classical
  obtain ⟨k, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hQ
  obtain ⟨b, hb⟩ := exists_cellBoundary_of_bijective f n hf
    (fun i => π (MvPolynomial.X i))
  let q := cellDesc b f (fun i => π (MvPolynomial.X i)) hb
  refine ⟨attachCells b, attachCellsι b, q, attachCellsι_cellDesc b f _ hb,
    finitePolynomial_attachCells b hP,
    fun j hj => isIso_attachCellsι_app b _ (by simpa using hj), ?_⟩
  let v (i : Fin k) : CellVariable (n + 1) (Fin k) ⦋n + 1⦌ :=
    (i, ⟨𝟙 _, Function.surjective_id⟩)
  let l : MvPolynomial (Fin k) A →ₐ[A] (attachCells b).obj (op ⦋n + 1⦌) :=
    MvPolynomial.aeval (fun i => MvPolynomial.X (v i))
  have h : (q.app (op ⦋n + 1⦌)).hom.comp l = π := by
    apply MvPolynomial.algHom_ext
    intro i
    change cellDescApp b f (fun j => π (MvPolynomial.X j)) (op ⦋n + 1⦌)
      (l (MvPolynomial.X i)) = π (MvPolynomial.X i)
    rw [show l (MvPolynomial.X i) = MvPolynomial.X (v i) from MvPolynomial.aeval_X _ _,
      cellDescApp_X]
    simp [v]
  have hs : Function.Surjective ((q.app (op ⦋n + 1⦌)).hom.comp l) := h.symm ▸ hπ
  exact Function.Surjective.of_comp hs

lemma isCoskeletal_comp {C D : Type*} [Category C] [Category D]
    (X : SimplicialObject C) (n : ℕ) [X.IsCoskeletal n]
    (G : C ⥤ D)
    [G.PreservesRightKanExtension ((SimplexCategory.Truncated.inclusion n).op ⋙ X)
      (SimplexCategory.Truncated.inclusion n).op] :
    SimplicialObject.IsCoskeletal (X ⋙ G) n := by
  have h : X.IsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)) :=
    SimplicialObject.IsCoskeletal.isRightKanExtension
  constructor
  convert (Functor.PreservesRightKanExtension.preserves
    (G := G) X (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X))) using 1 <;>
    first | rfl | (ext Δ; simp)

private lemma underlying_isCoskeletal {B : Type u} [CommRing B] [Algebra A B]
    (X : SimplicialObject (Over (CommAlgCat.of A B))) (n : ℕ)
    [X.IsCoskeletal (n + 1)] :
    SimplicialObject.IsCoskeletal (X ⋙ Over.forget _ ⋙ forget (CommAlgCat A)) (n + 1) := by
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{0, 0} (forget (CommAlgCat.{u} A)) :=
    (adj.{u, u} A).rightAdjoint_preservesLimits
  have : SimplicialObject.IsCoskeletal (X ⋙ Over.forget (CommAlgCat.of A B)) (n + 1) :=
    isCoskeletal_comp X (n + 1) (Over.forget _)
  exact isCoskeletal_comp (X ⋙ Over.forget _) (n + 1) (forget (CommAlgCat A))

/-- The structure maps of a simplicial object of the slice over `T` assemble into an
augmentation of the underlying simplicial object of the ambient category. -/
public def overAugmentation {C : Type*} [Category C] {T : C}
    (X : SimplicialObject (Over T)) :
    X ⋙ Over.forget T ⟶ (Functor.const _).obj T where
  app Δ := (X.obj Δ).hom
  naturality _ _ f := by simp

/-- Conversely, an augmentation `ε : X ⟶ T` lifts `X` to a simplicial object of the slice
over `T`. -/
public def toOverAugmentation {C : Type*} [Category C] {T : C}
    {X : SimplicialObject C} (ε : X ⟶ (Functor.const _).obj T) :
    SimplicialObject (Over T) :=
  X.toOver T ε.app (fun _ => by simp)

/-- A morphism of simplicial objects of the slice, from a morphism of the underlying objects
commuting with the structure maps. -/
private def overHom {C : Type*} [Category C] {T : C} {X Y : SimplicialObject (Over T)}
    (g : X ⋙ Over.forget T ⟶ Y ⋙ Over.forget T)
    (w : ∀ Δ, g.app Δ ≫ (Y.obj Δ).hom = (X.obj Δ).hom) : X ⟶ Y where
  app Δ := Over.homMk (g.app Δ) (w Δ)
  naturality _ _ f := Over.OverMorphism.ext (g.naturality f)

-- Transporting the extension to the slice category involves nested functor coercions.
private lemma exists_polynomial_extension_over {B : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (X Y : SimplicialObject (Over (CommAlgCat.of A B))) (f : X ⟶ Y) (n : ℕ)
    (hf : ∀ k, k ≤ n → Function.Bijective ((f.app (op ⦋k⦌)).left))
    (hX : ∀ k : ℕ, ∃ r : ℕ, Nonempty
      ((X.obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A))
    (hkan : SSet.trivialKanFibrations (underlyingAugmentation A B Y))
    (hcosk : IsIso ((SimplicialObject.coskAdj n).unit.app Y)) :
    ∃ (X' : SimplicialObject (Over (CommAlgCat.of A B))) (i : X ⟶ X') (q : X' ⟶ Y),
      i ≫ q = f ∧
      (∀ k : ℕ, ∃ r : ℕ, Nonempty
        ((X'.obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A)) ∧
      (∀ k, k ≤ n → IsIso (i.app (op ⦋k⦌))) ∧
      Function.Surjective ((q.app (op ⦋n + 1⦌)).left) := by
  have hfinite (k : ℕ) (hk : k ≤ n) :
      Algebra.FiniteType A (Y.obj (op ⦋k⦌)).left := by
    obtain ⟨r, ⟨e⟩⟩ := hX k
    have : Algebra.FiniteType A (X.obj (op ⦋k⦌)).left :=
      Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
    exact Algebra.FiniteType.of_surjective (f.app (op ⦋k⦌)).left.hom (hf k hk).surjective
  have hnext := finiteType_succ_of_trivialKanFibration_of_isCoskeletal
    A B Y n hkan hcosk hfinite
  obtain ⟨P', i, q, hfac, hP', hi, hq⟩ := exists_polynomial_extension
    (Functor.whiskerRight f (Over.forget _)) n hf hX hnext
  let ε := q ≫ overAugmentation Y
  let X' := toOverAugmentation ε
  let q' : X' ⟶ Y := overHom q fun _ => rfl
  have hiw (Δ : SimplexCategoryᵒᵖ) : i.app Δ ≫ (X'.obj Δ).hom = (X.obj Δ).hom := by
    change i.app Δ ≫ q.app Δ ≫ (Y.obj Δ).hom = _
    rw [← Category.assoc, ← NatTrans.comp_app, hfac]
    exact Over.w (f.app Δ)
  let i' : X ⟶ X' := overHom i hiw
  refine ⟨X', i', q', ?_, hP', ?_, hq⟩
  · exact NatTrans.ext (funext fun Δ => Over.OverMorphism.ext (congr_app hfac Δ))
  · intro k hk
    have hm : IsIso ((Over.forget _).map (i'.app (op ⦋k⦌))) := hi k hk
    exact isIso_of_reflects_iso (i'.app (op ⦋k⦌)) (Over.forget _)

/-- Naturality of the unit of the `n`-coskeleton adjunction. -/
private lemma comp_cosk_unit_app {C : Type*} [Category C] [CategoryTheory.Limits.HasLimits C]
    {V W : SimplicialObject C} (n : ℕ) (a : V ⟶ W) :
    a ≫ (SimplicialObject.coskAdj n).unit.app W =
      (SimplicialObject.coskAdj n).unit.app V ≫ (SimplicialObject.cosk n).map a := by
  simp

private lemma exists_factor_of_truncation_iso {C : Type*} [Category C]
    [CategoryTheory.Limits.HasLimits C] {V W R : SimplicialObject C}
    (i : V ⟶ W) (a : V ⟶ R) (n : ℕ)
    [IsIso ((SimplicialObject.truncation n).map i)] [R.IsCoskeletal n] :
    ∃ l : W ⟶ R, i ≫ l = a := by
  have : IsIso ((SimplicialObject.cosk n).map i) :=
    inferInstanceAs (IsIso ((SimplicialObject.Truncated.cosk n).map
      ((SimplicialObject.truncation n).map i)))
  refine ⟨(SimplicialObject.coskAdj n).unit.app W ≫
    inv ((SimplicialObject.cosk n).map i) ≫
    (SimplicialObject.cosk n).map a ≫ inv ((SimplicialObject.coskAdj n).unit.app R), ?_⟩
  rw [← Category.assoc, comp_cosk_unit_app]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← comp_cosk_unit_app]
  simp

private lemma trivialKanFibrations_of_relative_zeroCoskeletal {B : Type u}
    (X : SimplicialObject (Over B)) [X.IsCoskeletal 0]
    (h : Function.Surjective (X.obj (op ⦋0⦌)).hom) :
    SSet.trivialKanFibrations (overAugmentation X) := by
  rw [SSet.trivialKanFibrations_iff_surjective_and_hasLiftingProperty]
  refine ⟨h, ?_⟩
  intro m hm
  constructor
  intro a b sq
  let V := toOverAugmentation (∂Δ[m].ι ≫ b)
  let W := toOverAugmentation b
  let i : V ⟶ W := overHom ∂Δ[m].ι fun _ => rfl
  let a' : V ⟶ X := overHom a (congr_app sq.w)
  have hiApp (Δ : (SimplexCategory.Truncated 0)ᵒᵖ) :
      IsIso (((SimplicialObject.truncation 0).map i).app Δ) := by
    apply (isIso_iff_of_reflects_iso _ (Over.forget B)).mp
    rw [isIso_iff_bijective]
    refine ⟨fun _ _ h => Subtype.ext h, fun x => ⟨⟨x, ?_⟩, rfl⟩⟩
    intro hs
    have hc := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at hc
    change m + 1 ≤ Δ.unop.obj.len + 1 at hc
    have hd := Δ.unop.property
    simp only [Nat.le_zero] at hd
    omega
  have hi : IsIso ((SimplicialObject.truncation 0).map i) :=
    NatIso.isIso_of_isIso_app _
  obtain ⟨l, hl⟩ := exists_factor_of_truncation_iso i a' 0
  refine ⟨⟨⟨Functor.whiskerRight l (Over.forget B), ?_, ?_⟩⟩⟩
  · exact congrArg (fun f => Functor.whiskerRight f (Over.forget B)) hl
  · exact NatTrans.ext (funext fun Δ => Over.w (l.app Δ))

private lemma initial_coskeleton_trivialKan {B : Type u} [CommRing B] [Algebra A B]
    (X : SimplicialObject (Over (CommAlgCat.of A B))) [X.IsCoskeletal 0]
    (h : Function.Surjective (X.obj (op ⦋0⦌)).hom) :
    SSet.trivialKanFibrations (underlyingAugmentation A B X) := by
  let G := Over.post (forget (CommAlgCat.{u} A)) (X := CommAlgCat.of A B)
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{0, 0} G :=
    (Over.postAdjunctionRight (Y := CommAlgCat.of A B)
      (adj.{u, u} A)).rightAdjoint_preservesLimits
  have : SimplicialObject.IsCoskeletal (X ⋙ G) 0 := isCoskeletal_comp X 0 G
  exact trivialKanFibrations_of_relative_zeroCoskeletal (X ⋙ G) h

lemma cosk_isCoskeletal {C : Type*} [Category C]
    [CategoryTheory.Limits.HasLimits C] (X : SimplicialObject C) (n : ℕ) :
    ((SimplicialObject.cosk n).obj X).IsCoskeletal n :=
  (SimplicialObject.isCoskeletal_iff_isIso _ n).mpr
    ((SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (C := C) (Nat.le_refl n)).2.1 _)

private lemma over_augmentation_naturality {B : Type u} [CommRing B] [Algebra A B]
    {X Y : SimplicialObject (Over (CommAlgCat.of A B))} (f : X ⟶ Y) :
    Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat A)) ≫
      underlyingAugmentation A B Y = underlyingAugmentation A B X :=
  NatTrans.ext (funext fun Δ => congrArg (forget (CommAlgCat A)).map (Over.w (f.app Δ)))

private lemma exists_next_stage {B : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (X : SimplicialObject (Over (CommAlgCat.of A B))) (n : ℕ)
    (hX : ∀ k : ℕ, ∃ r : ℕ, Nonempty
      ((X.obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A))
    (hkan : SSet.trivialKanFibrations
      (underlyingAugmentation A B ((SimplicialObject.cosk n).obj X))) :
    ∃ (X' : SimplicialObject (Over (CommAlgCat.of A B)))
      (f : (SimplicialObject.cosk (n + 1)).obj X' ⟶ (SimplicialObject.cosk n).obj X),
      (∀ k : ℕ, ∃ r : ℕ, Nonempty
        ((X'.obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A)) ∧
      SSet.trivialKanFibrations
        (underlyingAugmentation A B ((SimplicialObject.cosk (n + 1)).obj X')) ∧
      SSet.trivialKanFibrations
        (Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat A))) ∧
      (∀ k, k ≤ n → IsIso (f.app (op ⦋k⦌))) := by
  let R := (SimplicialObject.cosk n).obj X
  have hR : R.IsCoskeletal n := cosk_isCoskeletal X n
  have hRn : IsIso ((SimplicialObject.coskAdj (n + 1)).unit.app R) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (C := Over (CommAlgCat.of A B)) (Nat.le_succ n)).2.2 R inferInstance
  have hRn' : R.IsCoskeletal (n + 1) :=
    (SimplicialObject.isCoskeletal_iff_isIso _ _).mpr hRn
  let η := (SimplicialObject.coskAdj n).unit.app X
  have hη (k : ℕ) (hk : k ≤ n) : IsIso (η.app (op ⦋k⦌)) :=
    isIso_cosk_unit_app X n ⦋k⦌ hk
  obtain ⟨X', i, q, hfac, hX', hi, hq⟩ :=
    exists_polynomial_extension_over X R η n
      (fun k hk => have := hη k hk; over_bijective_of_isIso _) hX hkan inferInstance
  let R' := (SimplicialObject.cosk (n + 1)).obj X'
  have hR' : R'.IsCoskeletal (n + 1) := cosk_isCoskeletal X' (n + 1)
  let η' := (SimplicialObject.coskAdj (n + 1)).unit.app X'
  let f : R' ⟶ R := (SimplicialObject.cosk (n + 1)).map q ≫
    inv ((SimplicialObject.coskAdj (n + 1)).unit.app R)
  have hf : η' ≫ f = q := by
    dsimp only [f, η']
    rw [← Category.assoc, ← comp_cosk_unit_app]
    simp
  have hfiso (k : ℕ) (hk : k ≤ n) : IsIso (f.app (op ⦋k⦌)) := by
    have := hi k hk
    have := hη k hk
    have hqi : i.app (op ⦋k⦌) ≫ q.app (op ⦋k⦌) = η.app (op ⦋k⦌) := congr_app hfac _
    have : IsIso (q.app (op ⦋k⦌)) := IsIso.of_isIso_fac_left hqi
    have : IsIso (η'.app (op ⦋k⦌)) :=
      isIso_cosk_unit_app X' (n + 1) ⦋k⦌ (by simpa using Nat.le_succ_of_le hk)
    exact IsIso.of_isIso_fac_left (congr_app hf _)
  have hfsurj : Function.Surjective (f.app (op ⦋n + 1⦌)).left := by
    have hfapp : (η'.app (op ⦋n + 1⦌)).left ≫ (f.app (op ⦋n + 1⦌)).left =
        (q.app (op ⦋n + 1⦌)).left :=
      congrArg (fun t => (t.app (op ⦋n + 1⦌)).left) hf
    exact Function.Surjective.of_comp (hfapp ▸ hq)
  have hfk : SSet.trivialKanFibrations
      (Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat A))) :=
    SSet.trivialKanFibrations_of_coskeletal _ (n + 1)
      (fun k hk => have := hfiso k (by omega); over_bijective_of_isIso (f.app (op ⦋k⦌)))
      hfsurj
      ((SimplicialObject.isCoskeletal_iff_isIso _ _).mp (underlying_isCoskeletal R n))
      ((SimplicialObject.isCoskeletal_iff_isIso _ _).mp (underlying_isCoskeletal R' n))
  refine ⟨X', f, hX', ?_, hfk, hfiso⟩
  rw [← over_augmentation_naturality f]
  exact SSet.trivialKanFibrations_comp _ _ hfk hkan

/-- Polynomial algebra structure transfers along an isomorphism of objects over `B`. -/
private lemma nonempty_algEquiv_of_isIso {B : Type u} [CommRing B] [Algebra A B]
    {X Y : Over (CommAlgCat.of A B)} (g : X ⟶ Y) [IsIso g] {r : ℕ}
    (e : Nonempty (Y.left ≃ₐ[A] MvPolynomial (Fin r) A)) :
    Nonempty (X.left ≃ₐ[A] MvPolynomial (Fin r) A) :=
  ⟨(CommAlgCat.algEquivOfIso ((Over.forget _).mapIso (asIso g))).trans e.some⟩

private lemma exists_polynomial_tower {B : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] :
    ∃ F : ℕᵒᵖ ⥤ SimplicialObject (Over (CommAlgCat.of A B)),
      SSet.trivialKanFibrations (underlyingAugmentation A B (F.obj (op 0))) ∧
      (∀ n : ℕ, SSet.trivialKanFibrations (Functor.whiskerRight
        (F.map (homOfLE (Nat.le_succ n)).op) (Over.forget _ ⋙ forget (CommAlgCat A)))) ∧
      (∀ n k : ℕ, k ≤ n →
        IsIso ((F.map (homOfLE (Nat.le_succ n)).op).app (op ⦋k⦌))) ∧
      (∀ n k : ℕ, k ≤ n → ∃ r : ℕ, Nonempty
        (((F.obj (op n)).obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A)) := by
  classical
  let S (n : ℕ) := {X : SimplicialObject (Over (CommAlgCat.of A B)) //
    (∀ k : ℕ, ∃ r : ℕ, Nonempty
      ((X.obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A)) ∧
    SSet.trivialKanFibrations
      (underlyingAugmentation A B ((SimplicialObject.cosk n).obj X))}
  obtain ⟨k, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let X₀ : SimplicialObject (Over (CommAlgCat.of A B)) :=
    (Functor.const _).obj (Over.mk (CommAlgCat.ofHom π))
  let R₀ := (SimplicialObject.cosk 0).obj X₀
  have hR₀ : R₀.IsCoskeletal 0 := cosk_isCoskeletal X₀ 0
  have hk₀ : SSet.trivialKanFibrations (underlyingAugmentation A B R₀) := by
    apply initial_coskeleton_trivialKan
    have hfac : (((SimplicialObject.coskAdj 0).unit.app X₀).app (op ⦋0⦌)).left ≫
        (R₀.obj (op ⦋0⦌)).hom = CommAlgCat.ofHom π :=
      Over.w (((SimplicialObject.coskAdj 0).unit.app X₀).app (op ⦋0⦌))
    have hs : Function.Surjective
        ((((SimplicialObject.coskAdj 0).unit.app X₀).app (op ⦋0⦌)).left ≫
          (R₀.obj (op ⦋0⦌)).hom) := by
      rw [hfac]
      exact hπ
    exact Function.Surjective.of_comp hs
  let s₀ : S 0 := ⟨X₀, (fun _ => ⟨k, ⟨AlgEquiv.refl⟩⟩), hk₀⟩
  have hnext (n : ℕ) (s : S n) :
      ∃ (t : S (n + 1))
        (f : (SimplicialObject.cosk (n + 1)).obj t.val ⟶
          (SimplicialObject.cosk n).obj s.val),
        SSet.trivialKanFibrations
          (Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat A))) ∧
        (∀ k, k ≤ n → IsIso (f.app (op ⦋k⦌))) := by
    obtain ⟨X', f, hp, hk, hf, hi⟩ := exists_next_stage s.val n s.prop.1 s.prop.2
    exact ⟨⟨X', hp, hk⟩, f, hf, hi⟩
  choose next f hf hi using hnext
  let s : ∀ n, S n := Nat.rec s₀ (fun n sn => next n sn)
  let F := Functor.ofOpSequence
    (X := fun n => (SimplicialObject.cosk n).obj (s n).val) (fun n => f n (s n))
  have hF (n : ℕ) : F.map (homOfLE (Nat.le_succ n)).op = f n (s n) :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  refine ⟨F, (s 0).prop.2, fun n => ?_, fun n k hk => ?_, ?_⟩
  · rw [hF]
    exact hf n (s n)
  · rw [hF]
    exact hi n (s n) k hk
  · intro n k hk
    obtain ⟨r, e⟩ := (s n).prop.1 k
    have := isIso_cosk_unit_app (s n).val n ⦋k⦌ hk
    exact ⟨r, nonempty_algEquiv_of_isIso
      (inv (((SimplicialObject.coskAdj n).unit.app (s n).val).app (op ⦋k⦌))) e⟩

lemma eventuallyConstantTo_of_isIso_succ {C : Type*} [Category C]
    (F : ℕᵒᵖ ⥤ C) (n : ℕ)
    (h : ∀ j, n ≤ j → IsIso (F.map (homOfLE (Nat.le_succ j)).op)) :
    F.IsEventuallyConstantTo (op n) := by
  have hmap (j : ℕ) (hj : n ≤ j) : IsIso (F.map (homOfLE hj).op) := by
    induction j, hj using Nat.le_induction with
    | base =>
        have he : (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) := Subsingleton.elim _ _
        rw [he, F.map_id]
        infer_instance
    | succ j hj ih =>
        have he : (homOfLE (Nat.le_succ_of_le hj)).op =
            (homOfLE (Nat.le_succ j)).op ≫ (homOfLE hj).op := Subsingleton.elim _ _
        rw [he, F.map_comp]
        have := h j hj
        infer_instance
  intro i f
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf]
  exact hmap i.unop (leOfHom f.unop)

private lemma polynomial_limit_of_stabilizing_tower {B : Type u}
    [CommRing B] [Algebra A B]
    (F : ℕᵒᵖ ⥤ SimplicialObject (Over (CommAlgCat.of A B)))
    (hi : ∀ n k : ℕ, k ≤ n →
      IsIso ((F.map (homOfLE (Nat.le_succ n)).op).app (op ⦋k⦌)))
    (hp : ∀ n k : ℕ, k ≤ n → ∃ r : ℕ, Nonempty
      (((F.obj (op n)).obj (op ⦋k⦌)).left ≃ₐ[A] MvPolynomial (Fin r) A)) :
    ∀ k : ℕ, ∃ r : ℕ, Nonempty
      (((CategoryTheory.Limits.limit F).obj (op ⦋k⦌)).left ≃ₐ[A]
        MvPolynomial (Fin r) A) := by
  intro k
  let E := (evaluation SimplexCategoryᵒᵖ (Over (CommAlgCat.of A B))).obj (op ⦋k⦌)
  have hE : (F ⋙ E).IsEventuallyConstantTo (op k) :=
    eventuallyConstantTo_of_isIso_succ (F ⋙ E) k (fun n hn => hi n k hn)
  have hπ : IsIso ((CategoryTheory.Limits.limit.π F (op k)).app (op ⦋k⦌)) :=
    hE.isIso_π_of_isLimit
      (CategoryTheory.Limits.isLimitOfPreserves E (CategoryTheory.Limits.limit.isLimit F))
  obtain ⟨r, e⟩ := hp k k (Nat.le_refl k)
  exact ⟨r, nonempty_algEquiv_of_isIso
    ((CategoryTheory.Limits.limit.π F (op k)).app (op ⦋k⦌)) e⟩

private lemma trivialKanFibrations_limit_augmentation {B : Type u}
    [CommRing B] [Algebra A B]
    (F : ℕᵒᵖ ⥤ SimplicialObject (Over (CommAlgCat.of A B)))
    (h₀ : SSet.trivialKanFibrations (underlyingAugmentation A B (F.obj (op 0))))
    (h : ∀ n : ℕ, SSet.trivialKanFibrations (Functor.whiskerRight
      (F.map (homOfLE (Nat.le_succ n)).op) (Over.forget _ ⋙ forget (CommAlgCat A)))) :
    SSet.trivialKanFibrations (underlyingAugmentation A B (CategoryTheory.Limits.limit F)) := by
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{0, 0} (forget (CommAlgCat.{u} A)) :=
    (adj.{u, u} A).rightAdjoint_preservesLimits
  let G := (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (Over.forget (CommAlgCat.of A B) ⋙ forget (CommAlgCat.{u} A))
  have hlim := SSet.trivialKanFibrations_limit_π_zero (F ⋙ G) h
  have hπ : SSet.trivialKanFibrations (G.map (CategoryTheory.Limits.limit.π F (op 0))) := by
    rw [← preservesLimitIso_hom_π G F (op 0)]
    exact SSet.trivialKanFibrations_comp _ _
      (SSet.modelCategoryQuillen.I.rlp_of_isIso _) hlim
  rw [← over_augmentation_naturality (CategoryTheory.Limits.limit.π F (op 0))]
  exact SSet.trivialKanFibrations_comp _ _ hπ h₀

end Cells

/-- **Stacks 08PX.** A finite type algebra over a Noetherian ring has a simplicial resolution by
polynomial algebras of finite type whose augmentation is a trivial Kan fibration on underlying
simplicial sets. -/
@[stacks 08PX]
theorem exists_trivialKanFibration_from_finiteType_polynomial_simplicialAlgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] :
    ∃ (P : SimplicialObject (CommAlgCat.{u} A))
      (ε : P ⟶ (Functor.const _).obj (CommAlgCat.of A B)),
      (∀ n : ℕ, ∃ k : ℕ,
        Nonempty ((P.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A)) ∧
      SSet.trivialKanFibrations
        (Functor.whiskerRight ε (CategoryTheory.forget (CommAlgCat.{u} A))) := by
  obtain ⟨F, h₀, hf, hi, hp⟩ := exists_polynomial_tower (A := A) (B := B)
  exact exists_result_of_over_resolution (CategoryTheory.Limits.limit F)
    (polynomial_limit_of_stabilizing_tower F hi hp)
    (trivialKanFibrations_limit_augmentation F h₀ hf)

end CommAlgCat

end
