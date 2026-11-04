module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Effaceable δ-functors are universal: Stacks 010T and 010U

Stacks 010T: let `F` be a δ-functor from an abelian category `𝒜` to an abelian category `ℬ`.
If for every `n > 0` and every `A` there is a monomorphism `u : A → B` with `Fⁿ(u) = 0`, then
`F` is universal. Stacks 010U: a universal δ-functor is determined by `F⁰` up to unique
isomorphism of δ-functors.

## The argument (Grothendieck's Tohoku argument, as in the Liquid Tensor Experiment)

An *effacement* of `X` in degree `n + 1` is a monomorphism `ι : X ⟶ I` with `Fⁿ⁺¹(ι) = 0`
(`DeltaFunctor.Effacement`). For the short exact sequence `X → I → I/X` of an effacement the
connecting morphism `δ : Fⁿ(I/X) ⟶ Fⁿ⁺¹(X)` is an epimorphism, and in fact a cokernel of
`Fⁿ(I) → Fⁿ(I/X)` (`Effacement.δIsCokernel`). Given `η : Fⁿ ⟶ Gⁿ`, the morphism
`η_{I/X} ≫ δ_G : Fⁿ(I/X) ⟶ Gⁿ⁺¹(X)` kills `Fⁿ(I)`, hence descends along that cokernel to
`Effacement.lift η : Fⁿ⁺¹(X) ⟶ Gⁿ⁺¹(X)`, characterised by `δ_F ≫ lift = η ≫ δ_G`
(`Effacement.δ_comp_lift`). Everything else follows from one lemma, `Effacement.lift_comm`: the
lifts along two effacements `e` of `X` and `e'` of `Y` commute with `f : X ⟶ Y` as soon as there
is `t : e.I ⟶ e'.I` with `e.ι ≫ t = f ≫ e'.ι`. Two constructions of effacements feed it:
`Effacement.ofBiprod e e' f` (`X ⟶ e.I ⊞ e'.I`), which dominates both `e` and `e'` and gives
independence of the lift from the effacement and its naturality in `X`; and
`Effacement.ofPushout hS e` (`X₁ ⟶ pushout S.f e.ι` for a short exact `S` starting at `X₁`),
which receives a morphism of short exact sequences from `S` and gives the compatibility of the
lift with `δ` for *every* short exact sequence (`Effacement.lift_δ`), the verification Stacks
omits. The extension `F ⟶ G` of `t : F⁰ ⟶ G⁰` is then built degree by degree
(`Effaceable.liftHom`) and is unique because the `δ` of effacements are epimorphisms.

The source category is abelian (cokernels, pushouts and biproducts are used); the target only
needs to be preadditive, and balanced where `DeltaFunctor.δIsCokernel` is used (this
assumption is stated on the declarations that need it).
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.DeltaFunctor

open Limits Category

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] (F : DeltaFunctor A B)

/-- An effacement of `X` in degree `n + 1` for the δ-functor `F`: a monomorphism `ι : X ⟶ I`
with `Fⁿ⁺¹(ι) = 0`. -/
structure Effacement (X : A) (n : ℕ) where
  /-- The target of the effacing monomorphism. -/
  I : A
  /-- The effacing monomorphism. -/
  ι : X ⟶ I
  [mono : Mono ι]
  /-- `Fⁿ⁺¹` kills the effacing monomorphism. -/
  map_ι : (F.functor (n + 1)).map ι = 0

/-- Stacks' hypothesis in 010T: for every `n > 0` and every `X` there is a monomorphism
`u : X ⟶ I` with `Fⁿ(u) = 0`. -/
class Effaceable : Prop where
  /-- Every object has an effacement in every positive degree. -/
  nonempty (X : A) (n : ℕ) : Nonempty (F.Effacement X n)

namespace Effacement

attribute [instance] mono

attribute [simp] map_ι

variable {F} {X : A} {n : ℕ} (e : F.Effacement X n)

/-- The short exact sequence `X → I → I/X` of an effacement. An `abbrev`, so that its terms
are reducibly `X`, `e.I` and `cokernel e.ι` in every statement below. -/
noncomputable abbrev sc : ShortComplex A :=
  ShortComplex.mk e.ι (cokernel.π e.ι) (cokernel.condition e.ι)

lemma sc_shortExact : e.sc.ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel e.ι))
    e.mono inferInstance

/-- The connecting morphism of the short exact sequence of an effacement is an epimorphism. -/
lemma epi_δ : Epi (F.δ e.sc_shortExact n) :=
  F.epi_δ_of_map_f_eq_zero e.sc_shortExact n e.map_ι

/-- `δ : Fⁿ(I/X) ⟶ Fⁿ⁺¹(X)` is a cokernel of `Fⁿ(I) → Fⁿ(I/X)`, i.e.
`Fⁿ⁺¹(X) = Coker(Fⁿ(I) → Fⁿ(I/X))` (Stacks' description in the proof of 010T). -/
noncomputable def δIsCokernel [Balanced B] :
    IsColimit (CokernelCofork.ofπ (F.δ e.sc_shortExact n) (F.map_g_δ e.sc_shortExact n)) :=
  F.δIsCokernel e.sc_shortExact n e.map_ι

/-- `Hⁿ(I) → Hⁿ(I/X) → Hⁿ⁺¹(X)` composes to zero, for the short exact sequence of an effacement
and any δ-functor `H` (the specialisation of `DeltaFunctor.map_g_δ`). -/
@[reassoc (attr := simp)]
lemma map_π_comp_δ (H : DeltaFunctor A B) :
    (H.functor n).map (cokernel.π e.ι) ≫ H.δ e.sc_shortExact n = 0 :=
  H.map_g_δ e.sc_shortExact n

variable {G : DeltaFunctor A B} (η : F.functor n ⟶ G.functor n)

lemma map_g_comp_app_comp_δ :
    (F.functor n).map (cokernel.π e.ι) ≫ η.app (cokernel e.ι) ≫ G.δ e.sc_shortExact n = 0 := by
  rw [η.naturality_assoc, e.map_π_comp_δ G, comp_zero]

variable {Y : A} (e' : F.Effacement Y n)

/-- The morphism of short exact sequences `e.sc ⟶ e'.sc` induced by `f : X ⟶ Y` and a
compatible `t : e.I ⟶ e'.I`. -/
@[simps]
noncomputable def scHom (f : X ⟶ Y) (t : e.I ⟶ e'.I) (w : e.ι ≫ t = f ≫ e'.ι) :
    e.sc ⟶ e'.sc where
  τ₁ := f
  τ₂ := t
  τ₃ := cokernel.map e.ι e'.ι f t w
  comm₁₂ := w.symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

section Lift

variable [Balanced B]

/-- The lift of `η : Fⁿ ⟶ Gⁿ` to degree `n + 1` at `X`, computed with the effacement `e`:
the descent of `η_{I/X} ≫ δ_G` along the cokernel `δ_F : Fⁿ(I/X) ⟶ Fⁿ⁺¹(X)`. -/
noncomputable def lift : (F.functor (n + 1)).obj X ⟶ (G.functor (n + 1)).obj X :=
  (CokernelCofork.IsColimit.desc' e.δIsCokernel (η.app (cokernel e.ι) ≫ G.δ e.sc_shortExact n)
    (e.map_g_comp_app_comp_δ η)).1

/-- The characterising property of `lift`: `δ_F ≫ lift η = η ≫ δ_G`. -/
@[reassoc (attr := simp)]
lemma δ_comp_lift :
    F.δ e.sc_shortExact n ≫ e.lift η = η.app (cokernel e.ι) ≫ G.δ e.sc_shortExact n :=
  (CokernelCofork.IsColimit.desc' e.δIsCokernel _ (e.map_g_comp_app_comp_δ η)).2

/-- `lift` is determined by its characterising property. -/
lemma lift_unique (k : (F.functor (n + 1)).obj X ⟶ (G.functor (n + 1)).obj X)
    (hk : F.δ e.sc_shortExact n ≫ k = η.app (cokernel e.ι) ≫ G.δ e.sc_shortExact n) :
    k = e.lift η := by
  have := e.epi_δ
  rw [← cancel_epi (F.δ e.sc_shortExact n), δ_comp_lift, hk]

/-- Naturality of `δ` along a morphism `φ` of short exact sequences into the sequence of the
effacement `e'`, expressed with the lift along `e'`. -/
private lemma δ_comp_map_comp_lift {S : ShortComplex A} (hS : S.ShortExact) (φ : S ⟶ e'.sc) :
    F.δ hS n ≫ (F.functor (n + 1)).map φ.τ₁ ≫ e'.lift η =
      η.app S.X₃ ≫ G.δ hS n ≫ (G.functor (n + 1)).map φ.τ₁ := by
  have hF := F.δ_naturality hS e'.sc_shortExact φ n
  have hG := G.δ_naturality hS e'.sc_shortExact φ n
  rw [← hG, ← η.naturality_assoc, ← reassoc_of% hF, δ_comp_lift]

/-- The one lemma behind independence, naturality and δ-compatibility of the lift: lifts along
effacements `e` of `X` and `e'` of `Y` commute with `f : X ⟶ Y` whenever `f` extends to
`t : e.I ⟶ e'.I`. -/
lemma lift_comm (f : X ⟶ Y) (t : e.I ⟶ e'.I) (w : e.ι ≫ t = f ≫ e'.ι) :
    e.lift η ≫ (G.functor (n + 1)).map f = (F.functor (n + 1)).map f ≫ e'.lift η := by
  have := e.epi_δ
  rw [← cancel_epi (F.δ e.sc_shortExact n), δ_comp_lift_assoc]
  exact (δ_comp_map_comp_lift η e' e.sc_shortExact (e.scHom e' f t w)).symm

end Lift

section Biprod

variable (f : X ⟶ Y)

/-- The effacement `X ⟶ e.I ⊞ e'.I`, `x ↦ (ι x, ι' (f x))`, dominating the effacement `e` of `X`
and mapping to the effacement `e'` of `Y` over `f`. An `abbrev`, so that its `I` and `ι` are
reducibly `e.I ⊞ e'.I` and `biprod.lift e.ι (f ≫ e'.ι)` in the statements below. -/
noncomputable abbrev ofBiprod : F.Effacement X n where
  I := e.I ⊞ e'.I
  ι := biprod.lift e.ι (f ≫ e'.ι)
  map_ι := by
    rw [biprod.lift_eq, Functor.map_add, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      e.map_ι, e'.map_ι, zero_comp, comp_zero, zero_comp, add_zero]

lemma ofBiprod_ι : (e.ofBiprod e' f).ι = biprod.lift e.ι (f ≫ e'.ι) := rfl

lemma ofBiprod_ι_comp_fst : (e.ofBiprod e' f).ι ≫ biprod.fst = 𝟙 X ≫ e.ι := by
  rw [ofBiprod_ι, biprod.lift_fst, id_comp]

lemma ofBiprod_ι_comp_snd : (e.ofBiprod e' f).ι ≫ biprod.snd = f ≫ e'.ι := by
  rw [ofBiprod_ι, biprod.lift_snd]

variable [Balanced B]

/-- The lift does not depend on the effacement. -/
lemma lift_eq (e₁ e₂ : F.Effacement X n) : e₁.lift η = e₂.lift η := by
  have h₁ := (e₁.ofBiprod e₂ (𝟙 X)).lift_comm η e₁ (𝟙 X) biprod.fst (e₁.ofBiprod_ι_comp_fst e₂ _)
  have h₂ := (e₁.ofBiprod e₂ (𝟙 X)).lift_comm η e₂ (𝟙 X) biprod.snd (e₁.ofBiprod_ι_comp_snd e₂ _)
  simp only [Functor.map_id, comp_id, id_comp] at h₁ h₂
  rw [← h₁, ← h₂]

/-- The lifts along any effacements of `X` and `Y` commute with every `f : X ⟶ Y`. -/
lemma lift_naturality :
    e.lift η ≫ (G.functor (n + 1)).map f = (F.functor (n + 1)).map f ≫ e'.lift η := by
  rw [e.lift_eq η (e.ofBiprod e' f)]
  exact (e.ofBiprod e' f).lift_comm η e' f biprod.snd (e.ofBiprod_ι_comp_snd e' f)

end Biprod

section Pushout

variable {S : ShortComplex A} (hS : S.ShortExact) (e : F.Effacement S.X₁ n)

/-- The effacement `X₁ ⟶ pushout S.f e.ι` of the first term of a short exact sequence `S`,
dominating `e` and receiving a morphism of short exact sequences from `S`. An `abbrev`, so that
its `I` and `ι` are reducibly `pushout S.f e.ι` and `e.ι ≫ pushout.inr S.f e.ι`. -/
noncomputable abbrev ofPushout : F.Effacement S.X₁ n where
  I := pushout S.f e.ι
  ι := e.ι ≫ pushout.inr S.f e.ι
  mono := by
    have := hS.mono_f
    infer_instance
  map_ι := by rw [Functor.map_comp, e.map_ι, zero_comp]

lemma ofPushout_ι : (e.ofPushout hS).ι = e.ι ≫ pushout.inr S.f e.ι := rfl

lemma ofPushout_ι_eq : (e.ofPushout hS).ι = S.f ≫ pushout.inl S.f e.ι := by
  rw [ofPushout_ι, pushout.condition]

/-- `S.f ≫ pushout.inl ≫ cokernel.π = 0` for the pushout effacement. -/
lemma f_comp_inl_comp_π :
    S.f ≫ pushout.inl S.f e.ι ≫ cokernel.π (e.ofPushout hS).ι = 0 := by
  rw [← assoc, ← e.ofPushout_ι_eq hS, cokernel.condition]

/-- The morphism of short exact sequences `S ⟶ (e.ofPushout hS).sc`, identity on `X₁`. -/
@[simps]
noncomputable def pushoutHom : S ⟶ (e.ofPushout hS).sc where
  τ₁ := 𝟙 _
  τ₂ := pushout.inl S.f e.ι
  τ₃ := (CokernelCofork.IsColimit.desc' hS.gIsCokernel
    (pushout.inl S.f e.ι ≫ cokernel.π (e.ofPushout hS).ι) (e.f_comp_inl_comp_π hS)).1
  comm₁₂ := by
    rw [id_comp]
    exact e.ofPushout_ι_eq hS
  comm₂₃ := (CokernelCofork.IsColimit.desc' hS.gIsCokernel _ (e.f_comp_inl_comp_π hS)).2.symm

variable [Balanced B]

/-- The compatibility of the lift with the connecting morphism of an arbitrary short exact
sequence `S`: `δ_F ≫ lift η = η ≫ δ_G`. This is the verification Stacks omits in 010T. -/
lemma lift_δ : F.δ hS n ≫ e.lift η = η.app S.X₃ ≫ G.δ hS n := by
  rw [e.lift_eq η (e.ofPushout hS)]
  simpa using δ_comp_map_comp_lift η (e.ofPushout hS) hS (e.pushoutHom hS)

end Pushout

end Effacement

namespace Effaceable

variable [F.Effaceable]

/-- A choice of effacement of `X` in degree `n + 1`. -/
noncomputable def effacement (X : A) (n : ℕ) : F.Effacement X n :=
  (Effaceable.nonempty (F := F) X n).some

variable {F} {G : DeltaFunctor A B}

/-- Morphisms of δ-functors out of an effaceable δ-functor are determined by their degree-zero
component. -/
lemma hom_ext {η γ : F ⟶ G} (h : η.app 0 = γ.app 0) : η = γ := by
  apply DeltaFunctor.hom_ext
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    ext X
    have := (effacement F X n).epi_δ
    rw [← cancel_epi (F.δ (effacement F X n).sc_shortExact n), ← η.comm, ← γ.comm, ih]

variable [Balanced B]

/-- The extension of `η : Fⁿ ⟶ Gⁿ` to degree `n + 1`, as a natural transformation. -/
noncomputable def liftNatTrans {n : ℕ} (η : F.functor n ⟶ G.functor n) :
    F.functor (n + 1) ⟶ G.functor (n + 1) where
  app X := (effacement F X n).lift η
  naturality _ _ f := (Effacement.lift_naturality _ η _ f).symm

lemma liftNatTrans_app {n : ℕ} (η : F.functor n ⟶ G.functor n) {X : A} (e : F.Effacement X n) :
    (liftNatTrans η).app X = e.lift η :=
  Effacement.lift_eq η _ e

/-- The extension is compatible with the connecting morphisms. -/
lemma δ_comp_liftNatTrans {n : ℕ} (η : F.functor n ⟶ G.functor n) {S : ShortComplex A}
    (hS : S.ShortExact) :
    F.δ hS n ≫ (liftNatTrans η).app S.X₁ = η.app S.X₃ ≫ G.δ hS n := by
  rw [liftNatTrans_app η (effacement F S.X₁ n), Effacement.lift_δ]

/-- The extension of `t : F⁰ ⟶ G⁰` to all degrees, by recursion. -/
noncomputable def liftFamily (t : F.functor 0 ⟶ G.functor 0) : ∀ n, F.functor n ⟶ G.functor n
  | 0 => t
  | n + 1 => liftNatTrans (liftFamily t n)

lemma liftFamily_zero (t : F.functor 0 ⟶ G.functor 0) : liftFamily t 0 = t := rfl

lemma liftFamily_succ (t : F.functor 0 ⟶ G.functor 0) (n : ℕ) :
    liftFamily t (n + 1) = liftNatTrans (liftFamily t n) := rfl

/-- The extension of `t : F⁰ ⟶ G⁰` to a morphism of δ-functors. -/
noncomputable def liftHom (t : F.functor 0 ⟶ G.functor 0) : F ⟶ G where
  app := liftFamily t
  comm hS n := by rw [liftFamily_succ, δ_comp_liftNatTrans]

@[simp]
lemma liftHom_app_zero (t : F.functor 0 ⟶ G.functor 0) : (liftHom t).app 0 = t := rfl

end Effaceable

section Universal

variable [Balanced B]

/-- Stacks 010T: an effaceable δ-functor is universal. -/
@[stacks 010T "an effaceable δ-functor is universal (Grothendieck's Tohoku argument)"]
theorem isUniversal_of_effaceable [F.Effaceable] : F.IsUniversal where
  existsUnique _ t :=
    ⟨Effaceable.liftHom t, Effaceable.liftHom_app_zero t,
      fun _ hη ↦ Effaceable.hom_ext (hη.trans (Effaceable.liftHom_app_zero t).symm)⟩

/-- Stacks 010T in its literal form: if for every `n > 0` and every `X` there is a monomorphism
`u : X ⟶ I` with `Fⁿ(u) = 0`, then `F` is universal. -/
@[stacks 010T "literal form: monos `u : A → B` with `Fⁿ(u) = 0` for all `n > 0`, `A`"]
theorem isUniversal_of_forall_exists_mono
    (h : ∀ (n : ℕ) (X : A), ∃ (I : A) (u : X ⟶ I), Mono u ∧ (F.functor (n + 1)).map u = 0) :
    F.IsUniversal :=
  have : F.Effaceable := ⟨fun X n ↦ by
    obtain ⟨I, u, hu, hu'⟩ := h n X
    exact ⟨{ I := I, ι := u, map_ι := hu' }⟩⟩
  isUniversal_of_effaceable F

end Universal

/-- If `A` has enough injectives and `Fⁿ` vanishes on injectives for `n > 0`, then `F` is
effaceable (embed `X` into the injective `Injective.under X`). -/
theorem Effaceable.of_isZero_injective [EnoughInjectives A]
    (h : ∀ (n : ℕ) (I : A) [Injective I], IsZero ((F.functor (n + 1)).obj I)) : F.Effaceable where
  nonempty X n := ⟨{ I := Injective.under X, ι := Injective.ι X, map_ι := (h n _).eq_of_tgt _ _ }⟩

/-- Stacks 010T for the standard source of effaceability: if `A` has enough injectives and `Fⁿ`
vanishes on injectives for `n > 0`, then `F` is universal. This is the form used for derived
functors and Čech cohomology. -/
@[stacks 010T "enough injectives and `Fⁿ(I) = 0` for `I` injective, `n > 0`: universal"]
theorem isUniversal_of_isZero_injective [Balanced B] [EnoughInjectives A]
    (h : ∀ (n : ℕ) (I : A) [Injective I], IsZero ((F.functor (n + 1)).obj I)) : F.IsUniversal :=
  have := Effaceable.of_isZero_injective F h
  isUniversal_of_effaceable F

namespace IsUniversal

variable {F} {G : DeltaFunctor A B} [F.IsUniversal]

/-- Stacks 010U, uniqueness: an isomorphism of universal δ-functors is determined by its
degree-zero component. -/
@[stacks 010U "the isomorphism is unique: it is determined by its degree-zero component"]
lemma iso_ext {α β : F ≅ G} (h : α.hom.app 0 = β.hom.app 0) : α = β :=
  Iso.ext (hom_ext_zero F h)

variable [G.IsUniversal]

/-- Stacks 010U: two universal δ-functors with isomorphic degree-zero parts are isomorphic as
δ-functors, by the isomorphism extending the given one. -/
@[stacks 010U "universal δ-functors with the same `F⁰` are isomorphic, extending `F⁰ ≅ G⁰`"]
noncomputable def isoOfIso (e : F.functor 0 ≅ G.functor 0) : F ≅ G where
  hom := lift F e.hom
  inv := lift G e.inv
  hom_inv_id := hom_ext_zero F (by simp)
  inv_hom_id := hom_ext_zero G (by simp)

@[simp]
lemma isoOfIso_hom_app_zero (e : F.functor 0 ≅ G.functor 0) : (isoOfIso e).hom.app 0 = e.hom :=
  lift_app_zero F e.hom

@[simp]
lemma isoOfIso_inv_app_zero (e : F.functor 0 ≅ G.functor 0) : (isoOfIso e).inv.app 0 = e.inv :=
  lift_app_zero G e.inv

end IsUniversal

end CategoryTheory.DeltaFunctor
