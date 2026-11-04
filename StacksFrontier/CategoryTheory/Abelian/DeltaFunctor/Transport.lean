module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable

/-! # Transporting a cohomological δ-functor along degreewise isomorphisms

A cohomological δ-functor (`CategoryTheory.DeltaFunctor`, Stacks 010Q) is a family of additive
functors together with connecting morphisms and exactness axioms. All of that data and all of
those axioms are invariant under replacing each component functor by an isomorphic one: this
file performs the replacement.

## Main definitions and results

* `DeltaFunctor.ofIso D G e`: for a δ-functor `D` and natural isomorphisms `e n : Dⁿ ≅ Gⁿ`, the
  δ-functor with component functors `Gⁿ` and connecting morphism the conjugate
  `δ = e⁻¹ ≫ δ_D ≫ e` of the connecting morphism of `D` (`DeltaFunctor.ofIso_δ`).
* `DeltaFunctor.ofIsoIso`: the transported δ-functor is isomorphic to the original one *in the
  category of δ-functors* (Stacks 010R), by the morphism whose components are the `e n`.
* `DeltaFunctor.IsUniversal.of_iso`: universality (Stacks 010S) is invariant under isomorphism
  of δ-functors, hence `DeltaFunctor.ofIso_isUniversal`: the transport of a universal δ-functor
  is universal. This needs no hypotheses beyond preadditivity of the two categories.
* `DeltaFunctor.ofIsoSucc`: the special case in which the isomorphisms are given in positive
  degrees and in degree zero separately, which is the shape a comparison of derived functors
  with `Ext` naturally takes.
* `DeltaFunctor.isUniversal_of_functor_iso_rightDerived`: a δ-functor whose positive-degree
  components are *isomorphic* to the right derived functors of its degree-zero component is
  universal — the isomorphism-valued form of the statement that is available for an equality of
  component functors.

## Design

The construction is built in term mode from `Iso` composition, and the proofs of the exactness
axioms go through the isomorphism of short complexes `ShortComplex.isoMk` relating the long
exact sequence of `D` to that of the transport, so that `ShortComplex.exact_of_iso` does the
work. Nothing here is specific to abelian categories: `DeltaFunctor.ofIso` and the universality
transport only use preadditivity of the source and the target.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.DeltaFunctor

open Limits Category

section OfIso

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] (D : DeltaFunctor A B) (G : ℕ → A ⥤ B) (e : ∀ n, D.functor n ≅ G n)

/-- **Transport of a cohomological δ-functor along degreewise isomorphisms.** Given a δ-functor
`D` and natural isomorphisms `e n : Dⁿ ≅ Gⁿ`, this is the δ-functor whose component functors
are the `Gⁿ` and whose connecting morphism is the conjugate `e⁻¹ ≫ δ_D ≫ e` of the connecting
morphism of `D`. Marked `implicit_reducible`, so that its component functors are reducibly the
`Gⁿ` in every statement below. -/
@[implicit_reducible]
def ofIso : DeltaFunctor A B where
  functor := G
  additive := fun n ↦ Functor.additive_of_iso (e n)
  δ := fun {S} hS n ↦ (e n).inv.app S.X₃ ≫ D.δ hS n ≫ (e (n + 1)).hom.app S.X₁
  map_g_δ := fun {S} hS n ↦ by
    rw [← assoc, (e n).inv.naturality S.g, assoc, D.map_g_δ_assoc, zero_comp, comp_zero]
  δ_map_f := fun {S} hS n ↦ by
    rw [assoc, assoc, ← (e (n + 1)).hom.naturality S.f, D.δ_map_f_assoc, zero_comp, comp_zero]
  mono_map_f := fun {S} hS ↦ by
    have := D.mono_map_f hS
    have h : (G 0).map S.f
        = (e 0).inv.app S.X₁ ≫ (D.functor 0).map S.f ≫ (e 0).hom.app S.X₂ := by
      rw [(e 0).hom.naturality S.f, Iso.inv_hom_id_app_assoc]
    rw [h]
    infer_instance
  exact_map := fun {S} hS n ↦ by
    have := Functor.additive_of_iso (e n)
    exact ShortComplex.exact_of_iso (S.mapNatIso (e n)) (D.exact_map hS n)
  exact_δ₁ := fun {S} hS n ↦
    ShortComplex.exact_of_iso
      (ShortComplex.isoMk ((e n).app S.X₂) ((e n).app S.X₃) ((e (n + 1)).app S.X₁)
        ((e n).hom.naturality S.g).symm ((e n).hom_inv_id_app_assoc S.X₃ _))
      (D.exact_δ₁ hS n)
  exact_δ₂ := fun {S} hS n ↦
    ShortComplex.exact_of_iso
      (ShortComplex.isoMk ((e n).app S.X₃) ((e (n + 1)).app S.X₁) ((e (n + 1)).app S.X₂)
        ((e n).hom_inv_id_app_assoc S.X₃ _) ((e (n + 1)).hom.naturality S.f).symm)
      (D.exact_δ₂ hS n)
  δ_naturality := fun {S T} hS hT φ n ↦ by
    rw [(e n).inv.naturality_assoc, D.δ_naturality_assoc hS hT φ n, assoc, assoc,
      ← (e (n + 1)).hom.naturality φ.τ₁]

/-- The component functors of the transported δ-functor are the given ones. -/
@[simp]
lemma ofIso_functor : (D.ofIso G e).functor = G := rfl

/-- The connecting morphism of the transported δ-functor is the conjugate of the connecting
morphism of the original one. Every consumer of `DeltaFunctor.ofIso` needs this. -/
@[simp]
lemma ofIso_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (D.ofIso G e).δ hS n = (e n).inv.app S.X₃ ≫ D.δ hS n ≫ (e (n + 1)).hom.app S.X₁ :=
  rfl

/-- The morphism of δ-functors `D.ofIso G e ⟶ D` (Stacks 010R) whose degree-`n` component is
the inverse of the transporting isomorphism `e n`. -/
def ofIsoHom : D.ofIso G e ⟶ D where
  app n := (e n).inv
  comm := fun {S} hS n ↦ by
    rw [ofIso_δ, assoc, assoc, Iso.hom_inv_id_app, comp_id]

/-- The degree-`n` component of `DeltaFunctor.ofIsoHom` is the inverse of `e n`. -/
@[simp]
lemma ofIsoHom_app (n : ℕ) : (D.ofIsoHom G e).app n = (e n).inv := rfl

/-- The morphism of δ-functors `D ⟶ D.ofIso G e` (Stacks 010R) whose degree-`n` component is
the transporting isomorphism `e n`. -/
def ofIsoInv : D ⟶ D.ofIso G e where
  app n := (e n).hom
  comm := fun {S} _ n ↦ (e n).hom_inv_id_app_assoc S.X₃ _

/-- The degree-`n` component of `DeltaFunctor.ofIsoInv` is `e n`. -/
@[simp]
lemma ofIsoInv_app (n : ℕ) : (D.ofIsoInv G e).app n = (e n).hom := rfl

/-- **The transport of a δ-functor is isomorphic to it in the category of δ-functors.** The
compatibility axiom of `DeltaFunctor.Hom` is satisfied by the transporting isomorphisms in both
directions, because the connecting morphism of the transport is the conjugate of the original
one. -/
@[simps]
def ofIsoIso : D.ofIso G e ≅ D where
  hom := D.ofIsoHom G e
  inv := D.ofIsoInv G e
  hom_inv_id := DeltaFunctor.hom_ext fun n ↦ (e n).inv_hom_id
  inv_hom_id := DeltaFunctor.hom_ext fun n ↦ (e n).hom_inv_id

/-- **Universality of a δ-functor is invariant under isomorphism of δ-functors.** Stacks 010S is
a property of the isomorphism class of a δ-functor in the category of δ-functors of Stacks
010R. -/
theorem IsUniversal.of_iso {F F' : DeltaFunctor A B} (α : F ≅ F') [F.IsUniversal] :
    F'.IsUniversal where
  existsUnique H t := by
    obtain ⟨η, hη, hu⟩ := IsUniversal.existsUnique (F := F) H (α.hom.app 0 ≫ t)
    have key : α.inv.app 0 ≫ α.hom.app 0 = 𝟙 (F'.functor 0) :=
      congrArg (fun h : F' ⟶ F' ↦ h.app 0) α.inv_hom_id
    refine ⟨α.inv ≫ η, ?_, fun γ hγ ↦ ?_⟩
    · change α.inv.app 0 ≫ η.app 0 = t
      rw [hη, ← assoc, key, id_comp]
    · have h : α.hom ≫ γ = η := hu _ (by
        change α.hom.app 0 ≫ γ.app 0 = α.hom.app 0 ≫ t
        rw [hγ])
      rw [← h, α.inv_hom_id_assoc]

/-- **Universality transports along degreewise isomorphisms.** If `D` is a universal δ-functor
(Stacks 010S) then so is its transport along any family of degreewise isomorphisms. -/
theorem ofIso_isUniversal [D.IsUniversal] : (D.ofIso G e).IsUniversal :=
  IsUniversal.of_iso (D.ofIsoIso G e).symm

end OfIso

section OfIsoSucc

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] (D : DeltaFunctor A B) (G : ℕ → A ⥤ B) (e₀ : D.functor 0 ≅ G 0)
  (e : ∀ n : ℕ, D.functor (n + 1) ≅ G (n + 1))

/-- The family of degreewise isomorphisms assembled from an isomorphism in degree zero and a
family of isomorphisms in the positive degrees. -/
def isoFamilyOfSucc : ∀ n, D.functor n ≅ G n
  | 0 => e₀
  | n + 1 => e n

/-- In degree zero, `DeltaFunctor.isoFamilyOfSucc` is the degree-zero isomorphism. -/
@[simp]
lemma isoFamilyOfSucc_zero : D.isoFamilyOfSucc G e₀ e 0 = e₀ := rfl

/-- In degree `n + 1`, `DeltaFunctor.isoFamilyOfSucc` is the `n`-th positive-degree isomorphism. -/
@[simp]
lemma isoFamilyOfSucc_succ (n : ℕ) : D.isoFamilyOfSucc G e₀ e (n + 1) = e n := rfl

/-- **Transport of a cohomological δ-functor along isomorphisms given in positive degrees and in
degree zero separately.** This is the shape in which a comparison of derived functors with `Ext`
arrives: a family `Dⁿ⁺¹ ≅ Gⁿ⁺¹` indexed by `n : ℕ`, together with an unrelated degree-zero
isomorphism. -/
def ofIsoSucc : DeltaFunctor A B :=
  D.ofIso G (D.isoFamilyOfSucc G e₀ e)

/-- The component functors of `DeltaFunctor.ofIsoSucc` are the given ones. -/
@[simp]
lemma ofIsoSucc_functor : (D.ofIsoSucc G e₀ e).functor = G := rfl

/-- The degree-zero connecting morphism of `DeltaFunctor.ofIsoSucc`. -/
@[simp]
lemma ofIsoSucc_δ_zero {S : ShortComplex A} (hS : S.ShortExact) :
    (D.ofIsoSucc G e₀ e).δ hS 0 = e₀.inv.app S.X₃ ≫ D.δ hS 0 ≫ (e 0).hom.app S.X₁ :=
  rfl

/-- The positive-degree connecting morphisms of `DeltaFunctor.ofIsoSucc`. -/
@[simp]
lemma ofIsoSucc_δ_succ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (D.ofIsoSucc G e₀ e).δ hS (n + 1)
      = (e n).inv.app S.X₃ ≫ D.δ hS (n + 1) ≫ (e (n + 1)).hom.app S.X₁ :=
  rfl

/-- `DeltaFunctor.ofIsoSucc` is isomorphic to the original δ-functor. -/
def ofIsoSuccIso : D.ofIsoSucc G e₀ e ≅ D :=
  D.ofIsoIso G (D.isoFamilyOfSucc G e₀ e)

/-- Universality transports along isomorphisms given in positive degrees and in degree zero
separately. -/
theorem ofIsoSucc_isUniversal [D.IsUniversal] : (D.ofIsoSucc G e₀ e).IsUniversal :=
  D.ofIso_isUniversal G (D.isoFamilyOfSucc G e₀ e)

end OfIsoSucc

section RightDerived

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] {B : Type u'}
  [Category.{v'} B] [Abelian B]

/-- **A δ-functor whose positive-degree components are isomorphic to the right derived functors
of its degree-zero component is universal.** The isomorphism-valued form of the corresponding
statement for an *equality* of component functors: the higher right derived functors vanish on
injective objects, so Stacks 010T applies. Only the positive degrees are used, and only on
injective objects. -/
theorem isUniversal_of_functor_iso_rightDerived (D : DeltaFunctor A B)
    (hD : ∀ n : ℕ, D.functor (n + 1) ≅ (D.functor 0).rightDerived (n + 1)) : D.IsUniversal :=
  isUniversal_of_isZero_injective D fun n I _ ↦
    IsZero.of_iso (Functor.isZero_rightDerived_obj_injective_succ _ n I) ((hD n).app I)

end RightDerived

end CategoryTheory.DeltaFunctor
