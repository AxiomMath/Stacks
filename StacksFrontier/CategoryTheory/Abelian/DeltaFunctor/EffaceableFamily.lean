module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable

/-!
# Morphisms out of an effaceable δ-functor into a family with connecting morphisms

Let `F` be an effaceable cohomological δ-functor from an abelian category `𝒜` (Stacks 010T).
Grothendieck's argument extending `t : F⁰ ⟶ G⁰` to all degrees uses of the target `G` only its
connecting morphisms, their naturality in the short exact sequence, and the vanishing of
`Gⁿ(X₂) → Gⁿ(X₃) → Gⁿ⁺¹(X₁)`; exactness of the long sequence of `G` plays no role. A
*δ-family* is exactly that data. The motivating example is a δ-functor followed by an additive
functor that is not exact, such as `g_* ∘ R^q f_*`.

## Main definitions

* `CategoryTheory.DeltaFunctor.DeltaFamily`: additive functors `Gⁿ` with natural connecting
  morphisms `Gⁿ(X₃) ⟶ Gⁿ⁺¹(X₁)` such that `Gⁿ(X₂) → Gⁿ(X₃) → Gⁿ⁺¹(X₁)` vanishes.
* `CategoryTheory.DeltaFunctor.DeltaFamily.postcomp`: a δ-functor followed by an additive
  functor.
* `CategoryTheory.DeltaFunctor.DeltaFamily.liftFamily`: the extension of `t : F⁰ ⟶ G⁰` to all
  degrees, for `F` effaceable.

## Main results

* `CategoryTheory.DeltaFunctor.DeltaFamily.δ_comp_liftFamily`: the extension commutes with the
  connecting morphisms of every short exact sequence.
* `CategoryTheory.DeltaFunctor.DeltaFamily.liftFamily_ext`: a family of natural transformations
  commuting with the connecting morphisms is determined by its degree-zero component.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.DeltaFunctor

open Limits Category

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  [Preadditive B]

variable (A B) in
/-- A **δ-family** from `𝒜` to `ℬ`: additive functors `Gⁿ` and, for every short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, connecting morphisms `Gⁿ(X₃) ⟶ Gⁿ⁺¹(X₁)`, natural in the sequence,
with `Gⁿ(X₂) → Gⁿ(X₃) → Gⁿ⁺¹(X₁)` zero. -/
structure DeltaFamily where
  /-- The functors `Gⁿ`, `n ≥ 0`. -/
  functor : ℕ → A ⥤ B
  /-- The connecting morphism `δ : Gⁿ(X₃) ⟶ Gⁿ⁺¹(X₁)` of a short exact sequence. -/
  δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
    (functor n).obj S.X₃ ⟶ (functor (n + 1)).obj S.X₁
  /-- `Gⁿ(X₂) → Gⁿ(X₃) → Gⁿ⁺¹(X₁)` composes to zero. -/
  map_g_δ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ), (functor n).map S.g ≫ δ hS n = 0
  /-- `δ` is natural in the short exact sequence. -/
  δ_naturality : ∀ {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (n : ℕ), (functor n).map φ.τ₃ ≫ δ hT n = δ hS n ≫ (functor (n + 1)).map φ.τ₁

namespace DeltaFamily

variable {C : Type*} [Category* C] [Preadditive C]

/-- **A δ-functor followed by an additive functor** is a δ-family, with connecting morphisms the
images of those of the δ-functor. -/
def postcomp (H : DeltaFunctor A B) (Q : B ⥤ C) [Q.Additive] : DeltaFamily A C where
  functor n := H.functor n ⋙ Q
  δ hS n := Q.map (H.δ hS n)
  map_g_δ hS n := by
    rw [Functor.comp_map, ← Q.map_comp, H.map_g_δ hS n, Q.map_zero]
  δ_naturality hS hT φ n := by
    rw [Functor.comp_map, Functor.comp_map, ← Q.map_comp, ← Q.map_comp,
      H.δ_naturality hS hT φ n]

@[simp]
lemma postcomp_functor (H : DeltaFunctor A B) (Q : B ⥤ C) [Q.Additive] (n : ℕ) :
    (postcomp H Q).functor n = H.functor n ⋙ Q := rfl

@[simp]
lemma postcomp_δ (H : DeltaFunctor A B) (Q : B ⥤ C) [Q.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) : (postcomp H Q).δ hS n = Q.map (H.δ hS n) := rfl

variable {F : DeltaFunctor A B} (G : DeltaFamily A B)

section Lift

variable {X : A} {n : ℕ} (e : F.Effacement X n) (η : F.functor n ⟶ G.functor n)

variable [Balanced B]

/-- The lift of `η : Fⁿ ⟶ Gⁿ` to degree `n + 1` at `X`, computed with the effacement `e`: the
descent of `η_{I/X} ≫ δ_G` along the cokernel `δ_F : Fⁿ(I/X) ⟶ Fⁿ⁺¹(X)`. -/
noncomputable def lift : (F.functor (n + 1)).obj X ⟶ (G.functor (n + 1)).obj X :=
  (CokernelCofork.IsColimit.desc' e.δIsCokernel (η.app (cokernel e.ι) ≫ G.δ e.sc_shortExact n)
    (by rw [η.naturality_assoc, G.map_g_δ e.sc_shortExact n, comp_zero])).1

/-- The characterising property of `lift`: `δ_F ≫ lift η = η ≫ δ_G`. -/
@[reassoc]
lemma δ_comp_lift :
    F.δ e.sc_shortExact n ≫ G.lift e η = η.app (cokernel e.ι) ≫ G.δ e.sc_shortExact n :=
  (CokernelCofork.IsColimit.desc' e.δIsCokernel _
    (by rw [η.naturality_assoc, G.map_g_δ e.sc_shortExact n, comp_zero])).2

/-- Naturality of the lift against a morphism `φ` from a short exact sequence `S` to the
sequence of an effacement. -/
private lemma δ_comp_map_comp_lift {Y : A} (e' : F.Effacement Y n) {S : ShortComplex A}
    (hS : S.ShortExact) (φ : S ⟶ e'.sc) :
    F.δ hS n ≫ (F.functor (n + 1)).map φ.τ₁ ≫ G.lift e' η =
      η.app S.X₃ ≫ G.δ hS n ≫ (G.functor (n + 1)).map φ.τ₁ := by
  rw [← reassoc_of% F.δ_naturality hS e'.sc_shortExact φ n, δ_comp_lift, η.naturality_assoc,
    G.δ_naturality hS e'.sc_shortExact φ n]

/-- Lifts along effacements `e` of `X` and `e'` of `Y` commute with `f : X ⟶ Y` whenever `f`
extends to `t : e.I ⟶ e'.I`. -/
lemma lift_comm {Y : A} (e' : F.Effacement Y n) (f : X ⟶ Y) (t : e.I ⟶ e'.I)
    (w : e.ι ≫ t = f ≫ e'.ι) :
    G.lift e η ≫ (G.functor (n + 1)).map f = (F.functor (n + 1)).map f ≫ G.lift e' η := by
  have := e.epi_δ
  rw [← cancel_epi (F.δ e.sc_shortExact n), δ_comp_lift_assoc]
  exact (G.δ_comp_map_comp_lift η e' e.sc_shortExact (e.scHom e' f t w)).symm

/-- The lift does not depend on the effacement. -/
lemma lift_eq (e₁ e₂ : F.Effacement X n) : G.lift e₁ η = G.lift e₂ η := by
  have h₁ := G.lift_comm (e₁.ofBiprod e₂ (𝟙 X)) η e₁ (𝟙 X) biprod.fst
    (e₁.ofBiprod_ι_comp_fst e₂ _)
  have h₂ := G.lift_comm (e₁.ofBiprod e₂ (𝟙 X)) η e₂ (𝟙 X) biprod.snd
    (e₁.ofBiprod_ι_comp_snd e₂ _)
  simp only [Functor.map_id, comp_id, id_comp] at h₁ h₂
  rw [← h₁, ← h₂]

/-- The lifts along any effacements of `X` and `Y` commute with every `f : X ⟶ Y`. -/
lemma lift_naturality {Y : A} (e' : F.Effacement Y n) (f : X ⟶ Y) :
    G.lift e η ≫ (G.functor (n + 1)).map f = (F.functor (n + 1)).map f ≫ G.lift e' η := by
  rw [G.lift_eq η e (e.ofBiprod e' f)]
  exact G.lift_comm (e.ofBiprod e' f) η e' f biprod.snd (e.ofBiprod_ι_comp_snd e' f)

/-- The lift is compatible with the connecting morphism of an arbitrary short exact sequence. -/
lemma lift_δ {S : ShortComplex A} (hS : S.ShortExact) (e : F.Effacement S.X₁ n) :
    F.δ hS n ≫ G.lift e η = η.app S.X₃ ≫ G.δ hS n := by
  rw [G.lift_eq η e (e.ofPushout hS)]
  simpa using G.δ_comp_map_comp_lift η (e.ofPushout hS) hS (e.pushoutHom hS)

end Lift

variable [F.Effaceable] [Balanced B]

/-- The extension of `η : Fⁿ ⟶ Gⁿ` to degree `n + 1`, as a natural transformation. -/
noncomputable def liftNatTrans {n : ℕ} (η : F.functor n ⟶ G.functor n) :
    F.functor (n + 1) ⟶ G.functor (n + 1) where
  app X := G.lift (Effaceable.effacement F X n) η
  naturality _ _ f := (G.lift_naturality _ η _ f).symm

/-- The extension commutes with the connecting morphisms. -/
lemma δ_comp_liftNatTrans {n : ℕ} (η : F.functor n ⟶ G.functor n) {S : ShortComplex A}
    (hS : S.ShortExact) :
    F.δ hS n ≫ (G.liftNatTrans η).app S.X₁ = η.app S.X₃ ≫ G.δ hS n :=
  G.lift_δ η hS _

variable (F) in
/-- **The extension of `t : F⁰ ⟶ G⁰` to all degrees**, by recursion, for `F` effaceable. -/
noncomputable def liftFamily (t : F.functor 0 ⟶ G.functor 0) : ∀ n, F.functor n ⟶ G.functor n
  | 0 => t
  | n + 1 => G.liftNatTrans (liftFamily t n)

@[simp]
lemma liftFamily_zero (t : F.functor 0 ⟶ G.functor 0) : G.liftFamily F t 0 = t := rfl

/-- **The extension commutes with the connecting morphism of every short exact sequence.** -/
@[reassoc]
lemma δ_comp_liftFamily (t : F.functor 0 ⟶ G.functor 0) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    F.δ hS n ≫ (G.liftFamily F t (n + 1)).app S.X₁ = (G.liftFamily F t n).app S.X₃ ≫ G.δ hS n :=
  G.δ_comp_liftNatTrans _ hS

/-- **A family of natural transformations commuting with the connecting morphisms is determined
by its degree-zero component**: it is the extension of that component. -/
lemma liftFamily_ext (η : ∀ n, F.functor n ⟶ G.functor n)
    (hη : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
      F.δ hS n ≫ (η (n + 1)).app S.X₁ = (η n).app S.X₃ ≫ G.δ hS n) (n : ℕ) :
    η n = G.liftFamily F (η 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext X
    have := (Effaceable.effacement F X n).epi_δ
    rw [← cancel_epi (F.δ (Effaceable.effacement F X n).sc_shortExact n), hη, ih,
      ← δ_comp_liftFamily]

end DeltaFamily

end CategoryTheory.DeltaFunctor
