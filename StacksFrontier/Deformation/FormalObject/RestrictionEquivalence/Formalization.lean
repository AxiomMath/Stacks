module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.AdicQuotient
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory

/-!
# Formal objects from Artinian objects

The first step of the comparison of Tag 06SJ: the truncation isomorphisms of Artinian local
algebras, the chosen truncation lifts, the functor sending an object of the original category to
the formal object of its truncation lifts, and the fact that the restriction of the formal objects
to Artinian local algebras is cofibered in groupoids.
-/

@[expose] public section

namespace Deformation

/-! ### Restricting a completion to Artinian local algebras -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
/-! ### The evaluation comparison

The constructions in this namespace build the comparison functor of Tag 06SJ and
establish that it is an equivalence over the Artinian base.
-/

namespace FormalEvaluation

/-- The adic quotient map of an Artinian local algebra, read as an identification of the
`n`-th truncation with the algebra; this is `Deformation.artinianTruncationIso` in the
orientation this section uses. -/
noncomputable def artinianTruncationIso
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥) :
    AdicTruncation.obj (artinianToComplete.obj A) n ≅ A :=
  (_root_.Deformation.artinianTruncationIso A n (by
    change maximalIdeal A ^ (n + 1) = ⊥
    exact hn)).symm

/-- The isomorphism `artinianTruncationIso A n hn` sends the class of `r` in the `n`-th adic
truncation to `r`. -/
theorem artinianTruncationIso_mk
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥) (r : A) :
    (artinianTruncationIso A n hn).hom.hom
      (Ideal.Quotient.mk (AdicTruncation.ideal (artinianToComplete.obj A) n) r) = r := by
  have hI : AdicTruncation.ideal (artinianToComplete.obj A) n = ⊥ := by
    show maximalIdeal A ^ (n + 1) = ⊥
    exact hn
  have h : artinianAdicQuotient A n ≫ (artinianTruncationIso A n hn).hom = 𝟙 A :=
    (_root_.Deformation.artinianTruncationIso A n hI).hom_inv_id
  exact congrArg (fun g : A ⟶ A => g.hom r) h

/-- Two maps out of an adic truncation of an Artinian local algebra agree if they agree on
classes of elements. -/
private theorem truncation_hom_ext
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    {f g : AdicTruncation.obj (artinianToComplete.obj A) n ⟶ B}
    (h : ∀ r : A, f.hom (Ideal.Quotient.mk _ r) = g.hom (Ideal.Quotient.mk _ r)) : f = g := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact h r

/-- The isomorphisms `artinianTruncationIso` are natural in morphisms of Artinian local algebras.
-/
theorem artinianTruncationIso_naturality
    (A B : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hnA : maximalIdeal A ^ (n + 1) = ⊥)
    (hnB : maximalIdeal B ^ (n + 1) = ⊥) (f : A ⟶ B) :
    (AdicTruncation.functor n).map (artinianToComplete.map f) ≫
        (artinianTruncationIso B n hnB).hom =
      (artinianTruncationIso A n hnA).hom ≫ f := by
  refine truncation_hom_ext fun r => ?_
  show (artinianTruncationIso B n hnB).hom.hom
      (Ideal.Quotient.mk _ (f.hom r)) =
    f.hom ((artinianTruncationIso A n hnA).hom.hom
      (Ideal.Quotient.mk _ r))
  rw [artinianTruncationIso_mk, artinianTruncationIso_mk]

/-- The isomorphisms `artinianTruncationIso` at levels `n` and `n + 1` are compatible with the
transition map between the adic truncations. -/
theorem artinianTruncationIso_transition
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥)
    (hn' : maximalIdeal A ^ (n + 1 + 1) = ⊥) :
    (AdicTruncation.transitionNat n).app
        (artinianToComplete.obj A) ≫
      (artinianTruncationIso A n hn).hom =
        (artinianTruncationIso A (n + 1) hn').hom := by
  refine truncation_hom_ext fun r => ?_
  show (artinianTruncationIso A n hn).hom.hom
      (Ideal.Quotient.mk
        (AdicTruncation.ideal (artinianToComplete.obj A) n) r) =
    (artinianTruncationIso A (n + 1) hn').hom.hom
      (Ideal.Quotient.mk
        (AdicTruncation.ideal (artinianToComplete.obj A) (n + 1)) r)
  rw [artinianTruncationIso_mk, artinianTruncationIso_mk]

/-- If the `(n + 1)`-st and `(n + 2)`-nd powers of the maximal ideal of an Artinian local algebra
vanish, the transition map from its `(n + 1)`-st to its `n`-th adic truncation is an isomorphism.
-/
theorem adicTransition_isIso_of_vanishing
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥)
    (hn' : maximalIdeal A ^ (n + 1 + 1) = ⊥) :
    IsIso (AdicTruncation.transition (artinianToComplete.obj A) n) := by
  let e₀ := artinianTruncationIso A n hn
  let e₁ := artinianTruncationIso A (n + 1) hn'
  have hcomp : AdicTruncation.transition (artinianToComplete.obj A) n ≫ e₀.hom = e₁.hom :=
    artinianTruncationIso_transition A n hn hn'
  let e : AdicTruncation.obj (artinianToComplete.obj A) (n + 1) ≅
      AdicTruncation.obj (artinianToComplete.obj A) n := e₁ ≪≫ e₀.symm
  have he : AdicTruncation.transition (artinianToComplete.obj A) n = e.hom := by
    calc
      _ = (AdicTruncation.transition (artinianToComplete.obj A) n ≫ e₀.hom) ≫ e₀.inv := by simp
      _ = e₁.hom ≫ e₀.inv := by rw [hcomp]
      _ = e.hom := by simp [e]
  rw [he]
  infer_instance

/-- If the `(n + 1)`-st and `(n + 2)`-nd powers of the maximal ideal of `X.fst` vanish, the
transition map from the `(n + 1)`-st to the `n`-th adic truncation of the base of the formal object
`X.snd` is an isomorphism. -/
theorem formalBaseTransition_isIso
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥)
    (hn' : maximalIdeal X.fst ^ (n + 1 + 1) = ⊥) :
    IsIso ((AdicTruncation.transitionNat n).app X.snd.base) := by
  let t₀ := (AdicTruncation.transitionNat n).app
    (artinianToComplete.obj X.fst)
  let t := (AdicTruncation.transitionNat n).app X.snd.base
  have hnat' : ((AdicTruncation.functor (n + 1)).map X.iso.hom) ≫ t =
      t₀ ≫ ((AdicTruncation.functor n).map X.iso.hom) := by
    simp [t, t₀]
  have ht₀ : IsIso t₀ := by
    dsimp [t₀]
    exact adicTransition_isIso_of_vanishing X.fst n hn hn'
  let := ht₀
  let : IsIso ((AdicTruncation.functor n).map X.iso.hom) := Functor.map_isIso _ _
  let : IsIso ((AdicTruncation.functor (n + 1)).map X.iso.inv) := Functor.map_isIso _ _
  have ht : t = ((AdicTruncation.functor (n + 1)).map X.iso.inv) ≫ t₀ ≫
      ((AdicTruncation.functor n).map X.iso.hom) := by
    calc
      t = 𝟙 _ ≫ t := by simp
      _ = (((AdicTruncation.functor (n + 1)).map X.iso.inv) ≫
          ((AdicTruncation.functor (n + 1)).map X.iso.hom)) ≫ t := by simp
      _ = ((AdicTruncation.functor (n + 1)).map X.iso.inv) ≫
          (((AdicTruncation.functor (n + 1)).map X.iso.hom) ≫ t) := by simp
      _ = ((AdicTruncation.functor (n + 1)).map X.iso.inv) ≫
          (t₀ ≫ ((AdicTruncation.functor n).map X.iso.hom)) := by
            rw [hnat']
      _ = _ := by simp [t₀]
  have hRhs : IsIso (((AdicTruncation.functor (n + 1)).map X.iso.inv) ≫ t₀ ≫
      ((AdicTruncation.functor n).map X.iso.hom)) := by infer_instance
  rw [← ht] at hRhs
  exact hRhs

/-- In a category cofibered in groupoids, a morphism lying over an isomorphism is an
isomorphism. -/
lemma _root_.Deformation.isIso_of_isCofiberedInGroupoids_of_base_isIso
    {F : Type uF} [Category.{vF} F]
    {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {R S : C} {a b : F}
    (f : R ⟶ S) (φ : a ⟶ b) (hφ : p.IsHomLift f φ) [IsIso f] : IsIso φ := by
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp f φ hφ
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p f φ

/-- If the `(n + 1)`-st and `(n + 2)`-nd powers of the maximal ideal of `X.fst` vanish, the `n`-th
transition morphism of the formal object `X.snd` is an isomorphism. -/
theorem formalTransition_isIso
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥)
    (hn' : maximalIdeal X.fst ^ (n + 1 + 1) = ⊥) :
    IsIso (X.snd.transition n) := by
  let : IsIso ((AdicTruncation.transitionNat n).app X.snd.base) :=
    formalBaseTransition_isIso p X n hn hn'
  exact isIso_of_isCofiberedInGroupoids_of_base_isIso hp _ _ (X.snd.transition_lift n)

/-- Once a power of the maximal ideal vanishes, so do all later powers. -/
theorem _root_.Deformation.maximalIdeal_pow_succ_eq_bot_of_le
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {n m : ℕ}
    (hnm : n ≤ m) (hn : maximalIdeal A ^ (n + 1) = ⊥) :
    maximalIdeal A ^ (m + 1) = ⊥ := by
  have hle : maximalIdeal A ^ (m + 1) ≤ maximalIdeal A ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)
  rw [hn] at hle
  exact le_antisymm hle bot_le

/-- When the `(n+1)`-st power of the maximal ideal vanishes, the canonical map to the
`n`-th adic truncation is an isomorphism. -/
theorem _root_.Deformation.artinianAdicQuotient_isIso
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥) :
    IsIso (artinianAdicQuotient A n) := by
  let q := artinianAdicQuotient A n
  let e := artinianTruncationIso A n hn
  have hqe : q ≫ e.hom = 𝟙 A := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    show (artinianTruncationIso A n hn).hom.hom
      (Ideal.Quotient.mk
        (AdicTruncation.ideal (artinianToComplete.obj A) n) x) = x
    exact artinianTruncationIso_mk A n hn x
  show IsIso q
  rw [(Iso.comp_hom_eq_id e).1 hqe]
  infer_instance

/-- An object of `F` together with a morphism from `A` lying over the canonical map from `p.obj A`
to its `n`-th adic truncation. -/
structure ArtinianTruncationLift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) (n : ℕ) where
  /-- The target object. -/
  object : F
  /-- The morphism from `A`. -/
  arrow : A ⟶ object
  /-- The morphism lies over the canonical map to the `n`-th adic truncation. -/
  lift : p.IsHomLift (artinianAdicQuotient (p.obj A) n) arrow

/-- A chosen lift, to a morphism out of `A`, of the canonical map from `p.obj A` to its `n`-th adic
truncation. -/
noncomputable def artinianTruncationLift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) (n : ℕ) :
    ArtinianTruncationLift p hp A n := by
  let q := artinianAdicQuotient (p.obj A) n
  let h := hp.exists_lift q.op (Opposite.op A) rfl
  let y := Classical.choose h
  let φ := Classical.choose (Classical.choose_spec h)
  have hφ := Classical.choose_spec (Classical.choose_spec h)
  let B := Opposite.unop y
  let θ := φ.unop
  have hB : p.obj B = AdicTruncation.obj
      (artinianToComplete.obj (p.obj A)) n := by
    simpa [B, q] using congrArg Opposite.unop
      (IsHomLift.domain_eq p.op q.op φ)
  have hθ : p.IsHomLift q θ := by
    apply IsHomLift.of_fac p q θ rfl hB
    have hfac := IsHomLift.fac p.op q.op φ
    have hfac' : q = p.map θ ≫ eqToHom hB := by
      simpa [q, θ] using congrArg (fun f => f.unop) hfac
    simpa using hfac'
  exact ⟨B, θ, hθ⟩

/-- The morphism from the chosen lift at level `n + 1` to the chosen lift at level `n`, induced by
the cocartesian property of the former. -/
noncomputable def artinianTruncationLiftTransition
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) (n : ℕ) :
    (artinianTruncationLift p hp A (n + 1)).object ⟶
      (artinianTruncationLift p hp A n).object := by
  let L₁ := artinianTruncationLift p hp A (n + 1)
  let L₀ := artinianTruncationLift p hp A n
  let q₁ := artinianAdicQuotient (p.obj A) (n + 1)
  let q₀ := artinianAdicQuotient (p.obj A) n
  let t := AdicTruncation.transition
    (artinianToComplete.obj (p.obj A)) n
  have hcomp : q₀ = q₁ ≫ t := by
    simpa [q₀, q₁, t] using
      (artinianAdicQuotient_transition (p.obj A) n).symm
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp q₁ L₁.arrow L₁.lift
  letI : p.IsHomLift q₀ L₀.arrow := L₀.lift
  exact Functor.IsStronglyCocartesian.map p q₁ L₁.arrow hcomp L₀.arrow

/-- The transition morphism between chosen lifts lies over the transition map between the adic
truncations. -/
theorem artinianTruncationLiftTransition_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) (n : ℕ) :
    p.IsHomLift (AdicTruncation.transition
      (artinianToComplete.obj (p.obj A)) n)
      (artinianTruncationLiftTransition p hp A n) := by
  let L₁ := artinianTruncationLift p hp A (n + 1)
  let L₀ := artinianTruncationLift p hp A n
  let q₁ := artinianAdicQuotient (p.obj A) (n + 1)
  let q₀ := artinianAdicQuotient (p.obj A) n
  let t := AdicTruncation.transition
    (artinianToComplete.obj (p.obj A)) n
  have hcomp : q₀ = q₁ ≫ t := (artinianAdicQuotient_transition (p.obj A) n).symm
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp q₁ L₁.arrow L₁.lift
  let : p.IsHomLift q₀ L₀.arrow := L₀.lift
  show p.IsHomLift t
    (Functor.IsStronglyCocartesian.map p q₁ L₁.arrow hcomp L₀.arrow)
  exact Functor.IsStronglyCocartesian.map_isHomLift p q₁ L₁.arrow hcomp L₀.arrow

/-- The transition morphism between chosen lifts commutes with the arrows out of `A`. -/
theorem artinianTruncationLiftTransition_fac
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) (n : ℕ) :
    (artinianTruncationLift p hp A (n + 1)).arrow ≫
        artinianTruncationLiftTransition p hp A n =
      (artinianTruncationLift p hp A n).arrow := by
  let L₁ := artinianTruncationLift p hp A (n + 1)
  let L₀ := artinianTruncationLift p hp A n
  let q₁ := artinianAdicQuotient (p.obj A) (n + 1)
  let q₀ := artinianAdicQuotient (p.obj A) n
  let t := AdicTruncation.transition
    (artinianToComplete.obj (p.obj A)) n
  have hcomp : q₀ = q₁ ≫ t := (artinianAdicQuotient_transition (p.obj A) n).symm
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp q₁ L₁.arrow L₁.lift
  let : p.IsHomLift q₀ L₀.arrow := L₀.lift
  show L₁.arrow ≫
      Functor.IsStronglyCocartesian.map p q₁ L₁.arrow hcomp L₀.arrow = L₀.arrow
  exact Functor.IsStronglyCocartesian.fac p q₁ L₁.arrow hcomp L₀.arrow

/-- The formal object whose levels are the chosen lifts of the adic truncations of `p.obj A`. -/
noncomputable def formalObjectFromArtinianObject
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) : FormalObject p where
  base := artinianToComplete.obj (p.obj A)
  level n := (artinianTruncationLift p hp A n).object
  level_eq n := by
    let L := artinianTruncationLift p hp A n
    let := L.lift
    exact IsHomLift.codomain_eq p (artinianAdicQuotient (p.obj A) n) L.arrow
  transition n := artinianTruncationLiftTransition p hp A n
  transition_lift n := artinianTruncationLiftTransition_lift p hp A n

/-- The morphism between the chosen lifts at level `n` induced by a morphism `f : A ⟶ B`. -/
noncomputable def artinianTruncationLiftMap
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A B : F} (f : A ⟶ B) (n : ℕ) :
    (artinianTruncationLift p hp A n).object ⟶
      (artinianTruncationLift p hp B n).object := by
  let LA := artinianTruncationLift p hp A n
  let LB := artinianTruncationLift p hp B n
  let qA := artinianAdicQuotient (p.obj A) n
  let qB := artinianAdicQuotient (p.obj B) n
  let g := (AdicTruncation.functor n).map (artinianToComplete.map (p.map f))
  have hcomm : qA ≫ g = p.map f ≫ qB := by
    simpa [qA, qB, g] using artinianAdicQuotient_naturality (p.map f) n
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp qA LA.arrow LA.lift
  letI : p.IsHomLift (p.map f) f := by infer_instance
  letI : p.IsHomLift qB LB.arrow := LB.lift
  letI : p.IsHomLift (p.map f ≫ qB) (f ≫ LB.arrow) := by infer_instance
  exact Functor.IsStronglyCocartesian.map p qA LA.arrow hcomm.symm (f ≫ LB.arrow)

/-- The morphism induced by `f` between chosen lifts lies over the map of `n`-th adic truncations
induced by `p.map f`. -/
theorem artinianTruncationLiftMap_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A B : F} (f : A ⟶ B) (n : ℕ) :
    p.IsHomLift
      ((AdicTruncation.functor n).map (artinianToComplete.map (p.map f)))
      (artinianTruncationLiftMap p hp f n) := by
  let LA := artinianTruncationLift p hp A n
  let LB := artinianTruncationLift p hp B n
  let qA := artinianAdicQuotient (p.obj A) n
  let qB := artinianAdicQuotient (p.obj B) n
  let g := (AdicTruncation.functor n).map (artinianToComplete.map (p.map f))
  have hcomm : qA ≫ g = p.map f ≫ qB := artinianAdicQuotient_naturality (p.map f) n
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp qA LA.arrow LA.lift
  let : p.IsHomLift (p.map f) f := by infer_instance
  let : p.IsHomLift qB LB.arrow := LB.lift
  let : p.IsHomLift (p.map f ≫ qB) (f ≫ LB.arrow) := by infer_instance
  show p.IsHomLift g
    (Functor.IsStronglyCocartesian.map p qA LA.arrow hcomm.symm (f ≫ LB.arrow))
  exact Functor.IsStronglyCocartesian.map_isHomLift p qA LA.arrow hcomm.symm (f ≫ LB.arrow)

/-- The morphism induced by `f` between chosen lifts commutes with the arrows out of `A` and `B`.
-/
theorem artinianTruncationLiftMap_fac
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A B : F} (f : A ⟶ B) (n : ℕ) :
    (artinianTruncationLift p hp A n).arrow ≫ artinianTruncationLiftMap p hp f n =
      f ≫ (artinianTruncationLift p hp B n).arrow := by
  let LA := artinianTruncationLift p hp A n
  let LB := artinianTruncationLift p hp B n
  let qA := artinianAdicQuotient (p.obj A) n
  let qB := artinianAdicQuotient (p.obj B) n
  let g := (AdicTruncation.functor n).map (artinianToComplete.map (p.map f))
  have hcomm : qA ≫ g = p.map f ≫ qB := artinianAdicQuotient_naturality (p.map f) n
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp qA LA.arrow LA.lift
  let : p.IsHomLift (p.map f) f := by infer_instance
  let : p.IsHomLift qB LB.arrow := LB.lift
  let : p.IsHomLift (p.map f ≫ qB) (f ≫ LB.arrow) := by infer_instance
  show LA.arrow ≫
      Functor.IsStronglyCocartesian.map p qA LA.arrow hcomm.symm (f ≫ LB.arrow) = _
  exact Functor.IsStronglyCocartesian.fac p qA LA.arrow hcomm.symm (f ≫ LB.arrow)

/-- The morphisms induced by `f` between chosen lifts commute with the transition morphisms. -/
theorem artinianTruncationLiftMap_naturality
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A B : F} (f : A ⟶ B) (n : ℕ) :
    artinianTruncationLiftMap p hp f (n + 1) ≫
        artinianTruncationLiftTransition p hp B n =
      artinianTruncationLiftTransition p hp A n ≫ artinianTruncationLiftMap p hp f n := by
  let LA := artinianTruncationLift p hp A (n + 1)
  let LB := artinianTruncationLift p hp B (n + 1)
  let qA := artinianAdicQuotient (p.obj A) (n + 1)
  let qB := artinianAdicQuotient (p.obj B) (n + 1)
  let gA := (AdicTruncation.functor (n + 1)).map
    (artinianToComplete.map (p.map f))
  let gB := (AdicTruncation.functor n).map
    (artinianToComplete.map (p.map f))
  let tA := AdicTruncation.transition (artinianToComplete.obj (p.obj A)) n
  let tB := AdicTruncation.transition (artinianToComplete.obj (p.obj B)) n
  have hbase : gA ≫ tB = tA ≫ gB := by
    show (AdicTruncation.functor (n + 1)).map
          (artinianToComplete.map (p.map f)) ≫
        (AdicTruncation.transitionNat n).app (artinianToComplete.obj (p.obj B)) =
      (AdicTruncation.transitionNat n).app (artinianToComplete.obj (p.obj A)) ≫
        (AdicTruncation.functor n).map
          (artinianToComplete.map (p.map f))
    exact (AdicTruncation.transitionNat n).naturality
      (artinianToComplete.map (p.map f))
  have hfacA := artinianTruncationLiftTransition_fac p hp A n
  have hfacB := artinianTruncationLiftTransition_fac p hp B n
  have hfacMap := artinianTruncationLiftMap_fac p hp f (n + 1)
  have hfacMap' := artinianTruncationLiftMap_fac p hp f n
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp qA LA.arrow LA.lift
  let : p.IsHomLift gA (artinianTruncationLiftMap p hp f (n + 1)) :=
    artinianTruncationLiftMap_lift p hp f (n + 1)
  let : p.IsHomLift tB (artinianTruncationLiftTransition p hp B n) :=
    artinianTruncationLiftTransition_lift p hp B n
  let : p.IsHomLift tA (artinianTruncationLiftTransition p hp A n) :=
    artinianTruncationLiftTransition_lift p hp A n
  let : p.IsHomLift gB (artinianTruncationLiftMap p hp f n) :=
    artinianTruncationLiftMap_lift p hp f n
  let : p.IsHomLift (tA ≫ gB)
      (artinianTruncationLiftTransition p hp A n ≫ artinianTruncationLiftMap p hp f n) :=
    IsHomLift.comp p tA gB
      (artinianTruncationLiftTransition p hp A n)
      (artinianTruncationLiftMap p hp f n)
  let : p.IsHomLift (tA ≫ gB)
      (artinianTruncationLiftMap p hp f (n + 1) ≫
        artinianTruncationLiftTransition p hp B n) :=
    hbase ▸ IsHomLift.comp p gA tB
      (artinianTruncationLiftMap p hp f (n + 1))
      (artinianTruncationLiftTransition p hp B n)
  apply Functor.IsStronglyCocartesian.ext p qA LA.arrow (tA ≫ gB)
  calc
    LA.arrow ≫ (artinianTruncationLiftMap p hp f (n + 1) ≫
        artinianTruncationLiftTransition p hp B n) =
      (LA.arrow ≫ artinianTruncationLiftMap p hp f (n + 1)) ≫
        artinianTruncationLiftTransition p hp B n := by simp [Category.assoc]
    _ = (f ≫ LB.arrow) ≫ artinianTruncationLiftTransition p hp B n := by rw [hfacMap]
    _ = f ≫ (LB.arrow ≫ artinianTruncationLiftTransition p hp B n) := by
      simp [Category.assoc]
    _ = f ≫ (artinianTruncationLift p hp B n).arrow := by rw [hfacB]
    _ = (artinianTruncationLift p hp A n).arrow ≫
        artinianTruncationLiftMap p hp f n := by rw [← hfacMap']
    _ = (LA.arrow ≫ artinianTruncationLiftTransition p hp A n) ≫
        artinianTruncationLiftMap p hp f n := by rw [← hfacA]
    _ = LA.arrow ≫ (artinianTruncationLiftTransition p hp A n ≫
        artinianTruncationLiftMap p hp f n) := by simp [Category.assoc]

/-- The identity of `A` induces the identity between chosen lifts. -/
theorem artinianTruncationLiftMap_id
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : F) (n : ℕ) :
    artinianTruncationLiftMap p hp (𝟙 A) n =
      𝟙 (artinianTruncationLift p hp A n).object := by
  let L := artinianTruncationLift p hp A n
  let q := artinianAdicQuotient (p.obj A) n
  let g := (AdicTruncation.functor n).map
    (artinianToComplete.map (p.map (𝟙 A)))
  have hg : g = 𝟙 (AdicTruncation.obj
      (artinianToComplete.obj (p.obj A)) n) := by
    show (AdicTruncation.functor n).map
      (artinianToComplete.map (p.map (𝟙 A))) = 𝟙 _
    simp [artinianToComplete]
  have hcomm : p.map (𝟙 A) ≫ q = q ≫ g := by
    rw [hg]
    simp
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp q L.arrow L.lift
  let : p.IsHomLift (p.map (𝟙 A)) (𝟙 A) := by infer_instance
  let : p.IsHomLift q L.arrow := L.lift
  let : p.IsHomLift (p.map (𝟙 A) ≫ q) (𝟙 A ≫ L.arrow) := by infer_instance
  have hB : p.obj L.object = AdicTruncation.obj
      (artinianToComplete.obj (p.obj A)) n := by
    let := L.lift
    exact IsHomLift.codomain_eq p q L.arrow
  have hId : p.IsHomLift (𝟙 (AdicTruncation.obj
      (artinianToComplete.obj (p.obj A)) n)) (𝟙 L.object) := by
    apply IsHomLift.of_fac p _ _ hB hB
    simp
  let : p.IsHomLift g (𝟙 L.object) := hg.symm ▸ hId
  show Functor.IsStronglyCocartesian.map p q L.arrow hcomm
      (𝟙 A ≫ L.arrow) = 𝟙 L.object
  simp [L, q, g]

/-- The morphisms induced between chosen lifts are compatible with composition. -/
theorem artinianTruncationLiftMap_comp
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A B C : F}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    artinianTruncationLiftMap p hp f n ≫ artinianTruncationLiftMap p hp g n =
      artinianTruncationLiftMap p hp (f ≫ g) n := by
  let LA := artinianTruncationLift p hp A n
  let LB := artinianTruncationLift p hp B n
  let LC := artinianTruncationLift p hp C n
  let qA := artinianAdicQuotient (p.obj A) n
  let qB := artinianAdicQuotient (p.obj B) n
  let qC := artinianAdicQuotient (p.obj C) n
  let gf := (AdicTruncation.functor n).map
    (artinianToComplete.map (p.map f))
  let gg := (AdicTruncation.functor n).map
    (artinianToComplete.map (p.map g))
  let gfg := (AdicTruncation.functor n).map
    (artinianToComplete.map (p.map (f ≫ g)))
  have hbase : gfg = gf ≫ gg := by simp [gfg, gf, gg]
  have hfacf := artinianTruncationLiftMap_fac p hp f n
  have hfacg := artinianTruncationLiftMap_fac p hp g n
  have hfacfg := artinianTruncationLiftMap_fac p hp (f ≫ g) n
  let := isStronglyCocartesian_of_isCofiberedInGroupoids
    hp qA LA.arrow LA.lift
  let : p.IsHomLift gf (artinianTruncationLiftMap p hp f n) :=
    artinianTruncationLiftMap_lift p hp f n
  let : p.IsHomLift gg (artinianTruncationLiftMap p hp g n) :=
    artinianTruncationLiftMap_lift p hp g n
  let : p.IsHomLift gfg (artinianTruncationLiftMap p hp (f ≫ g) n) :=
    artinianTruncationLiftMap_lift p hp (f ≫ g) n
  have hcompLift : p.IsHomLift gfg
      (artinianTruncationLiftMap p hp f n ≫ artinianTruncationLiftMap p hp g n) := by
    have h : p.IsHomLift (gf ≫ gg)
        (artinianTruncationLiftMap p hp f n ≫ artinianTruncationLiftMap p hp g n) := by
      infer_instance
    exact hbase ▸ h
  have hdirect : p.map (f ≫ g) ≫ qC = qA ≫ gfg := by
    simpa [gfg, qA, qC] using
      (artinianAdicQuotient_naturality (p.map (f ≫ g)) n).symm
  have hfac : LA.arrow ≫
      (artinianTruncationLiftMap p hp f n ≫ artinianTruncationLiftMap p hp g n) =
        (f ≫ g) ≫ LC.arrow := by
    calc
    LA.arrow ≫ (artinianTruncationLiftMap p hp f n ≫
        artinianTruncationLiftMap p hp g n) =
      (LA.arrow ≫ artinianTruncationLiftMap p hp f n) ≫
        artinianTruncationLiftMap p hp g n := by simp [Category.assoc]
    _ = (f ≫ LB.arrow) ≫ artinianTruncationLiftMap p hp g n := by rw [hfacf]
    _ = f ≫ (LB.arrow ≫ artinianTruncationLiftMap p hp g n) := by
      simp [Category.assoc]
    _ = f ≫ (g ≫ LC.arrow) := by rw [hfacg]
    _ = (f ≫ g) ≫ LC.arrow := by simp [Category.assoc]
  let : p.IsHomLift gfg
      (artinianTruncationLiftMap p hp f n ≫ artinianTruncationLiftMap p hp g n) :=
    hcompLift
  let : p.IsHomLift gfg (artinianTruncationLiftMap p hp (f ≫ g) n) :=
    artinianTruncationLiftMap_lift p hp (f ≫ g) n
  exact Functor.IsStronglyCocartesian.ext p qA LA.arrow gfg (hfac.trans hfacfg.symm)

/-- The morphism of formal objects induced by a morphism `f : A ⟶ B`. -/
noncomputable def formalObjectFromArtinianObjectHom
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {A B : F} (f : A ⟶ B) :
    (formalObjectFromArtinianObject p hp A) ⟶
      (formalObjectFromArtinianObject p hp B) where
  base := artinianToComplete.map (p.map f)
  app n := artinianTruncationLiftMap p hp f n
  app_lift n := artinianTruncationLiftMap_lift p hp f n
  naturality n := (artinianTruncationLiftMap_naturality p hp f n).symm

/-- The functor from `F` to the restriction of its formal objects to Artinian local algebras,
sending `A` to the formal object of chosen lifts of the adic truncations of `p.obj A`. -/
noncomputable def formalizationFunctor
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    F ⥤ CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)) where
  obj A :=
    { fst := p.obj A
      snd := formalObjectFromArtinianObject p hp A
      iso := Iso.refl _ }
  map {A B} f :=
    { fst := p.map f
      snd := formalObjectFromArtinianObjectHom p hp f }
  map_id A := by
    apply CategoricalPullback.hom_ext
    · simp
    · apply FormalObject.Hom.ext
      · change artinianToComplete.map (p.map (𝟙 A)) =
          𝟙 (artinianToComplete.obj (p.obj A))
        simp
      · intro n
        change artinianTruncationLiftMap p hp (𝟙 A) n =
          (𝟙 ((artinianTruncationLift p hp A n).object) :
            (artinianTruncationLift p hp A n).object ⟶
              (artinianTruncationLift p hp A n).object)
        exact artinianTruncationLiftMap_id p hp A n
  map_comp {A B C} f g := by
    apply CategoricalPullback.hom_ext
    · simp
    · apply FormalObject.Hom.ext
      · change artinianToComplete.map (p.map (f ≫ g)) =
          artinianToComplete.map (p.map f) ≫
            artinianToComplete.map (p.map g)
        simp
      · intro n
        change artinianTruncationLiftMap p hp (f ≫ g) n =
          artinianTruncationLiftMap p hp f n ≫
            artinianTruncationLiftMap p hp g n
        exact (artinianTruncationLiftMap_comp p hp f g n).symm

/-- Every morphism of Artinian local algebras out of the Artinian component of an object of the
restriction lifts to a morphism of the restriction. -/
theorem restrictionPullback_exists_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (hA : X.fst = A) :
    ∃ (Y : CategoricalPullback artinianToComplete
        (FormalObject.projection (p := p))) (φ : X ⟶ Y),
      (CategoricalPullback.π₁ artinianToComplete
        (FormalObject.projection (p := p))).IsHomLift f φ := by
  subst A
  let q := FormalObject.projection (p := p)
  let f' := X.iso.inv ≫ artinianToComplete.map f
  obtain ⟨Yo, ψ, hψ⟩ :=
    (formalObjectProjection_isCofiberedInGroupoids p hp).exists_lift
      f'.op (Opposite.op X.snd) rfl
  let Y' := Yo.unop
  let ψ' := ψ.unop
  have hY : Y'.base = artinianToComplete.obj B := by
    show Opposite.unop (q.op.obj Yo) = artinianToComplete.obj B
    exact congrArg Opposite.unop (IsHomLift.domain_eq q.op f'.op ψ)
  have hmap : q.map ψ' = f' ≫ eqToHom hY.symm := by
    have h := congrArg Quiver.Hom.unop (IsHomLift.fac' q.op f'.op ψ)
    simpa [q, ψ', hY] using h
  let Y : CategoricalPullback artinianToComplete q :=
    ⟨B, Y', eqToIso hY.symm⟩
  have hw : artinianToComplete.map f ≫ Y.iso.hom =
      X.iso.hom ≫ q.map ψ' := by
    rw [hmap]
    simp [Y, f', Category.assoc]
  let φ : X ⟶ Y := ⟨f, ψ', hw⟩
  refine ⟨Y, φ, ?_⟩
  show (CategoricalPullback.π₁ artinianToComplete
      (FormalObject.projection (p := p))).IsHomLift
    ((CategoricalPullback.π₁ artinianToComplete
      (FormalObject.projection (p := p))).map φ) φ
  exact IsHomLift.map _ _

/-- The restriction of the formal objects of `p` to Artinian local algebras is cofibered in
groupoids. -/
theorem restrictionPullback_isCofiberedInGroupoids
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    IsCofiberedInGroupoids
      (CategoricalPullback.π₁ artinianToComplete
        (FormalObject.projection (p := p))) := by
  let q := FormalObject.projection (p := p)
  let r := CategoricalPullback.π₁ artinianToComplete q
  have hq : IsCofiberedInGroupoids q :=
    formalObjectProjection_isCofiberedInGroupoids p hp
  show r.op.IsFiberedInGroupoids
  refine ⟨?_, ?_⟩
  · intro V U f X hX
    change Opposite.op (r.obj X.unop) = U at hX
    subst U
    obtain ⟨Y, φ, hφ⟩ := restrictionPullback_exists_lift p hp f.unop X.unop rfl
    refine ⟨Opposite.op Y, φ.op, ?_⟩
    let := hφ
    exact isHomLift_op r f.unop φ
  · intro X Y Z φ ψ f hcomp
    let X' := X.unop
    let Y' := Y.unop
    let Z' := Z.unop
    let Φ := φ.unop
    let Ψ := ψ.unop
    let d : Y'.fst ⟶ Z'.fst := f.unop
    have hfst : Φ.fst ≫ d = Ψ.fst := by
      have hcomp' : r.map Φ ≫ d = r.map Ψ := by
        show (r.op.map φ).unop ≫ f.unop = (r.op.map ψ).unop
        exact congrArg Quiver.Hom.unop hcomp
      change Φ.fst ≫ d = Ψ.fst at hcomp'
      exact hcomp'
    let s := Y'.iso.inv ≫ artinianToComplete.map d ≫ Z'.iso.hom
    have key : ∀ {U V : CategoricalPullback artinianToComplete q} (g : U ⟶ V),
        q.map g.snd = U.iso.inv ≫ artinianToComplete.map g.fst ≫ V.iso.hom :=
      fun {U _} g => U.iso.eq_inv_comp.2 g.w.symm
    have hbase : q.map Φ.snd ≫ s = q.map Ψ.snd := by
      rw [key Φ, key Ψ, ← hfst]
      simp only [s, Y', Z', Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
    have hbaseOp : s.op ≫ q.op.map Φ.snd.op = q.op.map Ψ.snd.op := congrArg Quiver.Hom.op hbase
    obtain ⟨χop, hχ, hχuniq⟩ := hq.unique_lift Φ.snd.op Ψ.snd.op s.op hbaseOp
    let χsnd := χop.unop
    have hχmap : q.map χsnd = s := congrArg Quiver.Hom.unop hχ.1
    have hχfac : Φ.snd ≫ χsnd = Ψ.snd := congrArg Quiver.Hom.unop hχ.2
    have hw : artinianToComplete.map d ≫ Z'.iso.hom =
        Y'.iso.hom ≫ q.map χsnd := by
      rw [hχmap]
      dsimp [s]
      simp
    let χ : Y' ⟶ Z' := ⟨d, χsnd, hw⟩
    have hχmapEq : r.op.map χ.op = f := rfl
    have hχlift : r.op.IsHomLift f χ.op :=
      IsHomLift.of_fac r.op f χ.op rfl rfl hχmapEq.symm
    have hχfactor : χ.op ≫ φ = ψ :=
      Quiver.Hom.unop_inj (CategoricalPullback.hom_ext hfst hχfac)
    refine ⟨χ.op, ⟨hχmapEq, hχfactor⟩, ?_⟩
    intro θ hθ
    let θ' := θ.unop
    let : r.op.IsHomLift f θ :=
      IsHomLift.of_fac r.op f θ rfl rfl hθ.1.symm
    have hθfst : θ'.fst = d := by
      have h := congrArg Quiver.Hom.unop hθ.1
      dsimp [r, CategoricalPullback.π₁, θ', d] at h
      exact h
    have hθmap : q.map θ'.snd = s := by
      rw [key θ', hθfst]
    have hθFormal : θ'.snd.op = χop := hχuniq _ ⟨congrArg Quiver.Hom.op hθmap,
      congrArg (fun k => k.op) (congrArg (fun k => k.snd) (congrArg Quiver.Hom.unop hθ.2))⟩
    exact Quiver.Hom.unop_inj
      (CategoricalPullback.hom_ext hθfst (congrArg Quiver.Hom.unop hθFormal))

end FormalEvaluation

end

end Deformation

end
