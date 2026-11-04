module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Transporting groupoid descent laws across the pullback comparison isomorphisms

A morphism `f` of groupoid schemes over a base scheme `S` pulls a descent morphism on the
target groupoid back to one on the source groupoid,
`Stacks.Groupoids.GroupoidScheme.pullbackDescent`.  Pullback of modules is a pseudofunctor, not
a functor, so the two groupoid laws for the pulled-back descent morphism cannot be checked by
composing equalities of functors; they are transports of the laws for `M.alpha` across the
comparison isomorphisms `AlgebraicGeometry.Scheme.Modules.pullbackComp`.  This file carries out
that transport for an abstract family of pullback functors, and supplies the groupoid
identities that instantiate it.

## Main definitions

* `Stacks.Modules.rdx` reindexes a descent datum along a morphism, for an abstract family of
  pullback functors with comparison isomorphisms.

## Main results

* `Stacks.Modules.cocycle_transport` and `Stacks.Modules.identity_transport` transport the
  cocycle law and the normalization law along the identity across the comparison isomorphisms.
* `Stacks.Groupoids.GroupoidScheme.successiveDescent_eq`,
  `Stacks.Groupoids.GroupoidScheme.identityDescent_eq` and
  `Stacks.Groupoids.GroupoidScheme.pullbackDescent_eq` rewrite the composites of
  `AlgebraicGeometry.Scheme.Modules.pullbackCongr` coming from
  `StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback` using the canonical `eqToHom`s, which is
  the form in which the transported laws are stated.
* `Stacks.Groupoids.GroupoidScheme.reindexHom_identity_alpha`: pulling `M.alpha` back along the
  identity section is the canonical isomorphism between the two pullbacks along the two legs of
  that section, which is the content of the normalization law carried by every quasi-coherent
  module on a groupoid scheme.

## Implementation notes

The two groupoid laws themselves, and the pullback functor `Tag 03LJ` they feed, are proved
directly in `StacksFrontier/AlgebraicGeometry/Groupoids/Equivariant/PullbackDescent.lean` and
`StacksFrontier/AlgebraicGeometry/Groupoids/Equivariant/PullbackFunctor.lean`
(`Stacks.Groupoids.GroupoidScheme.pullbackDescent_identity`,
`Stacks.Groupoids.GroupoidScheme.pullbackDescent_cocycle` and
`Stacks.Groupoids.GroupoidScheme.pullbackFunctor`); what is kept here is the abstract transport
machinery and the groupoid identities it consumes.

## References

* [Stacks Project, Tag 03LI](https://stacks.math.columbia.edu/tag/03LI)
* [Stacks Project, Tag 03LJ](https://stacks.math.columbia.edu/tag/03LJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Modules

section Abstract

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : C → Type u₂} [∀ X, Category.{v₂} (D X)]
  (Pb : ∀ {X Y : C}, (X ⟶ Y) → (D Y ⥤ D X))
  (Cmp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), Pb g ⋙ Pb f ≅ Pb (f ≫ g))

/-- Reindexing a descent datum `α : p^* F ⟶ q^* F` along a morphism `f`, for an abstract
family of pullback functors `Pb` with comparison isomorphisms `Cmp`. -/
def rdx {X Y Z : C} (f : X ⟶ Y) {g h : Y ⟶ Z} {F : D Z}
    (α : (Pb g).obj F ⟶ (Pb h).obj F) :
    (Pb (f ≫ g)).obj F ⟶ (Pb (f ≫ h)).obj F :=
  (Cmp f g).inv.app F ≫ (Pb f).map α ≫ (Cmp f h).hom.app F

variable {X Y Z W : C}

/-- Reindexing is compatible with composition of descent data. -/
theorem rdx_comp (f : X ⟶ Y) {g h i : Y ⟶ Z} {F : D Z}
    (α : (Pb g).obj F ⟶ (Pb h).obj F) (β : (Pb h).obj F ⟶ (Pb i).obj F) :
    rdx Pb Cmp f (α ≫ β) = rdx Pb Cmp f α ≫ rdx Pb Cmp f β := by
  simp [rdx]

/-- Reindexing the canonical isomorphism between pullbacks along equal morphisms gives again
the canonical isomorphism. -/
theorem rdx_eqToHom (f : X ⟶ Y) {g h : Y ⟶ Z} (hg : g = h) (F : D Z) :
    rdx Pb Cmp f (eqToHom (by rw [hg]) : (Pb g).obj F ⟶ (Pb h).obj F) =
      eqToHom (by rw [hg]) := by
  subst hg; simp [rdx]

/-- Reindexing along equal morphisms agrees up to the canonical isomorphisms. -/
theorem rdx_congr {f f' : X ⟶ Y} (hf : f = f') {g h : Y ⟶ Z} {F : D Z}
    (α : (Pb g).obj F ⟶ (Pb h).obj F) :
    rdx Pb Cmp f α = eqToHom (by rw [hf]) ≫ rdx Pb Cmp f' α ≫ eqToHom (by rw [hf]) := by
  subst hf; simp

variable (hP : ∀ {X Y Z W : C} (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W) (F : D W),
  (Cmp u (g ≫ v)).inv.app F ≫ (Pb u).map ((Cmp g v).inv.app F) ≫
      (Cmp u g).hom.app ((Pb v).obj F) ≫ (Cmp (u ≫ g) v).hom.app F =
    eqToHom (by rw [Category.assoc]))

include hP

/-- The associativity constraint with the outer comparison isomorphism moved to the right. -/
theorem pentagon' (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W) (F : D W) :
    (Pb u).map ((Cmp g v).inv.app F) ≫ (Cmp u g).hom.app ((Pb v).obj F) ≫
        (Cmp (u ≫ g) v).hom.app F =
      (Cmp u (g ≫ v)).hom.app F ≫ eqToHom (by rw [Category.assoc]) := by
  have h := hP u g v F
  rw [show (Cmp u (g ≫ v)).inv.app F = ((Cmp u (g ≫ v)).app F).inv from rfl,
    Iso.inv_comp_eq] at h
  simpa using h

/-- Associativity in the form used to push an inner comparison isomorphism outwards. -/
theorem Cmp_inv_map_hom (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W) (F : D W) :
    (Cmp u g).inv.app ((Pb v).obj F) ≫ (Pb u).map ((Cmp g v).hom.app F) =
      (Cmp (u ≫ g) v).hom.app F ≫ eqToHom (by rw [Category.assoc]) ≫
        (Cmp u (g ≫ v)).inv.app F := by
  have h := pentagon' Pb Cmp hP u g v F
  rw [← cancel_epi ((Cmp u g).hom.app ((Pb v).obj F)),
    ← cancel_epi ((Pb u).map ((Cmp g v).inv.app F))]
  rw [Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, reassoc_of% h]
  simp

/-- Associativity in the form used to pull an inner comparison isomorphism inwards. -/
theorem Cmp_map_inv_hom (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W) (F : D W) :
    (Pb u).map ((Cmp g v).inv.app F) ≫ (Cmp u g).hom.app ((Pb v).obj F) =
      (Cmp u (g ≫ v)).hom.app F ≫ eqToHom (by rw [Category.assoc]) ≫
        (Cmp (u ≫ g) v).inv.app F := by
  rw [← cancel_mono ((Cmp (u ≫ g) v).hom.app F)]
  simpa using pentagon' Pb Cmp hP u g v F

/-- Associativity between the two inverse comparison isomorphisms. -/
theorem Cmp_inv_map_inv (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W) (F : D W) :
    (Cmp u (g ≫ v)).inv.app F ≫ (Pb u).map ((Cmp g v).inv.app F) =
      eqToHom (by rw [Category.assoc]) ≫ (Cmp (u ≫ g) v).inv.app F ≫
        (Cmp u g).inv.app ((Pb v).obj F) := by
  rw [← cancel_mono ((Cmp u g).hom.app ((Pb v).obj F))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Cmp_map_inv_hom Pb Cmp hP u g v F]
  simp

/-- Reindexing a descent datum conjugated by the comparison isomorphisms for a further
pullback: reindexing commutes with changing the base of the module. -/
theorem rdx_Cmp_conj (u : X ⟶ Y) (g h : Y ⟶ Z) (v : Z ⟶ W) (F : D W)
    (γ : (Pb (g ≫ v)).obj F ⟶ (Pb (h ≫ v)).obj F) :
    rdx Pb Cmp u ((Cmp g v).hom.app F ≫ γ ≫ (Cmp h v).inv.app F) =
      (Cmp (u ≫ g) v).hom.app F ≫ eqToHom (by rw [Category.assoc]) ≫
        rdx Pb Cmp u γ ≫ eqToHom (by rw [Category.assoc]) ≫
        (Cmp (u ≫ h) v).inv.app F := by
  simp only [rdx, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (Cmp_inv_map_hom Pb Cmp hP u g v F), Cmp_map_inv_hom Pb Cmp hP u h v F]

/-- Reindexing twice is reindexing along the composite, up to the canonical isomorphisms. -/
theorem rdx_rdx (u : X ⟶ Y) (w : Y ⟶ Z) {g h : Z ⟶ W} (F : D W)
    (α : (Pb g).obj F ⟶ (Pb h).obj F) :
    rdx Pb Cmp u (rdx Pb Cmp w α) =
      eqToHom (by rw [Category.assoc]) ≫ rdx Pb Cmp (u ≫ w) α ≫
        eqToHom (by rw [Category.assoc]) := by
  have hnat := (Cmp u w).inv.naturality α
  simp only [rdx, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (Cmp_inv_map_inv Pb Cmp hP u w g F)]
  simp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat, reassoc_of% (Cmp_inv_map_hom Pb Cmp hP u w h F)]
  simp

/-- Reindexing along a composite is reindexing twice, up to the canonical isomorphisms. -/
theorem rdx_comp_left (u : X ⟶ Y) (w : Y ⟶ Z) {g h : Z ⟶ W} (F : D W)
    (α : (Pb g).obj F ⟶ (Pb h).obj F) :
    rdx Pb Cmp (u ≫ w) α =
      eqToHom (by rw [Category.assoc]) ≫ rdx Pb Cmp u (rdx Pb Cmp w α) ≫
        eqToHom (by rw [Category.assoc]) := by
  rw [rdx_rdx Pb Cmp hP]
  simp

omit hP

/-- A canonical isomorphism between pullbacks along equal morphisms, conjugated by the
comparison isomorphisms for a further pullback, is again a canonical isomorphism. -/
theorem Cmp_inv_eqToHom_hom {P : C} {m m' : P ⟶ Y} (hm : m = m') (a : Y ⟶ Z) (F : D Z) :
    (Cmp m a).inv.app F ≫
        eqToHom (show (Pb m).obj ((Pb a).obj F) = (Pb m').obj ((Pb a).obj F) by rw [hm]) ≫
        (Cmp m' a).hom.app F =
      eqToHom (by rw [hm]) := by
  subst hm; simp

/-- The same conjugation, with the comparison isomorphisms the other way round. -/
theorem Cmp_hom_eqToHom_inv {P : C} {m m' : P ⟶ Y} (hm : m = m') (a : Y ⟶ Z) (F : D Z) :
    (Cmp m a).hom.app F ≫
        eqToHom (show (Pb (m ≫ a)).obj F = (Pb (m' ≫ a)).obj F by rw [hm]) ≫
        (Cmp m' a).inv.app F =
      eqToHom (by rw [hm]) := by
  subst hm; simp

/-- Moving a canonical isomorphism between pullbacks along equal morphisms past a comparison
isomorphism. -/
theorem eqToHom_Cmp_hom {P : C} {m m' : P ⟶ Y} (hm : m = m') (a : Y ⟶ Z) (F : D Z) :
    eqToHom (show (Pb m).obj ((Pb a).obj F) = (Pb m').obj ((Pb a).obj F) by rw [hm]) ≫
        (Cmp m' a).hom.app F =
      (Cmp m a).hom.app F ≫ eqToHom (by rw [hm]) := by
  subst hm; simp

/-- Moving a canonical isomorphism between pullbacks along equal morphisms past an inverse
comparison isomorphism. -/
theorem Cmp_inv_eqToHom {P : C} {m m' : P ⟶ Y} (hm : m = m') (a : Y ⟶ Z) (F : D Z) :
    (Cmp m a).inv.app F ≫
        eqToHom (show (Pb m).obj ((Pb a).obj F) = (Pb m').obj ((Pb a).obj F) by rw [hm]) =
      eqToHom (by rw [hm]) ≫ (Cmp m' a).inv.app F := by
  subst hm; simp

section Transport

variable {U U' A A' P P' T : C} {s t : A ⟶ U} {σ τ : A' ⟶ U'} {a : U ⟶ U'} {b : A ⟶ A'}

include hP

/-- Reindexing a datum that has been transported along a base change.  Here `β` is the
transport of `α` along `a` across the squares `b ≫ σ = s ≫ a` and `b ≫ τ = t ≫ a`. -/
theorem rdx_conj (hs : b ≫ σ = s ≫ a) (ht : b ≫ τ = t ≫ a) (F : D U')
    (α : (Pb τ).obj F ⟶ (Pb σ).obj F) (u : T ⟶ A) :
    rdx Pb Cmp u ((Cmp t a).hom.app F ≫
        (eqToHom (by rw [ht]) ≫ rdx Pb Cmp b α ≫ eqToHom (by rw [hs])) ≫
        (Cmp s a).inv.app F) =
      (Cmp (u ≫ t) a).hom.app F ≫
        (eqToHom (by rw [Category.assoc, ← ht, ← Category.assoc]) ≫
          rdx Pb Cmp (u ≫ b) α ≫
          eqToHom (by rw [Category.assoc, hs, ← Category.assoc])) ≫
        (Cmp (u ≫ s) a).inv.app F := by
  rw [rdx_Cmp_conj Pb Cmp hP, rdx_comp, rdx_comp, rdx_eqToHom Pb Cmp u ht.symm F,
    rdx_eqToHom Pb Cmp u hs F, rdx_rdx Pb Cmp hP]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

omit hP

/-- The three junctions of the cocycle square, after each leg has been transported along a
base change. -/
theorem fiveFold_junction {c p₁ p₂ : T ⟶ A} (htc : c ≫ t = p₁ ≫ t)
    (hcond : p₁ ≫ s = p₂ ≫ t) (hsc : c ≫ s = p₂ ≫ s) (a : U ⟶ U') (F : D U')
    (X₁ : (Pb ((p₁ ≫ t) ≫ a)).obj F ⟶ (Pb ((p₁ ≫ s) ≫ a)).obj F)
    (X₂ : (Pb ((p₂ ≫ t) ≫ a)).obj F ⟶ (Pb ((p₂ ≫ s) ≫ a)).obj F) :
    eqToHom (by rw [htc]) ≫
        ((Cmp (p₁ ≫ t) a).hom.app F ≫ X₁ ≫ (Cmp (p₁ ≫ s) a).inv.app F) ≫
        eqToHom (by rw [hcond]) ≫
        ((Cmp (p₂ ≫ t) a).hom.app F ≫ X₂ ≫ (Cmp (p₂ ≫ s) a).inv.app F) ≫
        eqToHom (by rw [hsc]) =
      (Cmp (c ≫ t) a).hom.app F ≫
        (eqToHom (by rw [htc]) ≫ X₁ ≫ eqToHom (by rw [hcond]) ≫ X₂ ≫
          eqToHom (by rw [hsc])) ≫
        (Cmp (c ≫ s) a).inv.app F := by
  simp only [Category.assoc]
  rw [reassoc_of% (eqToHom_Cmp_hom Pb Cmp htc a F),
    reassoc_of% (Cmp_inv_eqToHom_hom Pb Cmp hcond a F),
    Cmp_inv_eqToHom Pb Cmp hsc.symm a F]

include hP

/-- Reindexing the successive-descent morphism of a cocycle square. -/
theorem rdx_fiveFold {γ q₁ q₂ : P' ⟶ A'} (κ : P ⟶ P') (htc : γ ≫ τ = q₁ ≫ τ)
    (hcond : q₁ ≫ σ = q₂ ≫ τ) (hsc : γ ≫ σ = q₂ ≫ σ) (F : D U')
    (α : (Pb τ).obj F ⟶ (Pb σ).obj F) :
    rdx Pb Cmp κ ((eqToHom (by rw [htc]) ≫ rdx Pb Cmp q₁ α ≫ eqToHom (by rw [hcond]) ≫
        rdx Pb Cmp q₂ α ≫ eqToHom (by rw [hsc]) :
      (Pb (γ ≫ τ)).obj F ⟶ (Pb (γ ≫ σ)).obj F)) =
      eqToHom (by rw [Category.assoc, htc, ← Category.assoc]) ≫
        rdx Pb Cmp (κ ≫ q₁) α ≫
        eqToHom (by rw [Category.assoc, hcond, ← Category.assoc]) ≫
        rdx Pb Cmp (κ ≫ q₂) α ≫
        eqToHom (by rw [Category.assoc, ← hsc, ← Category.assoc]) := by
  rw [rdx_comp, rdx_comp, rdx_comp, rdx_comp, rdx_eqToHom Pb Cmp κ htc F,
    rdx_eqToHom Pb Cmp κ hcond F, rdx_eqToHom Pb Cmp κ hsc.symm F]
  simp only [rdx_rdx Pb Cmp hP]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- The cocycle law for a transported datum, in the world of the target of the base change. -/
theorem rdx_transport_cocycle {c p₁ p₂ : P ⟶ A} {γ q₁ q₂ : P' ⟶ A'} {κ : P ⟶ P'}
    (hκ₁ : κ ≫ q₁ = p₁ ≫ b) (hκ₂ : κ ≫ q₂ = p₂ ≫ b) (hκc : c ≫ b = κ ≫ γ)
    (htc : γ ≫ τ = q₁ ≫ τ) (hcond : q₁ ≫ σ = q₂ ≫ τ) (hsc : γ ≫ σ = q₂ ≫ σ)
    (F : D U') (α : (Pb τ).obj F ⟶ (Pb σ).obj F)
    (hα : eqToHom (by rw [htc]) ≫ rdx Pb Cmp q₁ α ≫ eqToHom (by rw [hcond]) ≫
        rdx Pb Cmp q₂ α ≫ eqToHom (by rw [hsc]) = rdx Pb Cmp γ α) :
    eqToHom (by rw [hκc, Category.assoc, htc, ← Category.assoc, hκ₁]) ≫
        rdx Pb Cmp (p₁ ≫ b) α ≫
        eqToHom (by rw [← hκ₁, Category.assoc, hcond, ← Category.assoc, hκ₂]) ≫
        rdx Pb Cmp (p₂ ≫ b) α ≫
        eqToHom (by rw [← hκ₂, Category.assoc, ← hsc, ← Category.assoc, ← hκc]) =
      rdx Pb Cmp (c ≫ b) α := by
  have h := rdx_fiveFold Pb Cmp hP κ htc hcond hsc F α
  rw [hα, rdx_rdx Pb Cmp hP, rdx_congr Pb Cmp hκ₁ α, rdx_congr Pb Cmp hκ₂ α,
    rdx_congr Pb Cmp hκc.symm α] at h
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] at h
  rw [← cancel_epi (eqToHom (show (Pb (κ ≫ γ ≫ τ)).obj F = (Pb ((c ≫ b) ≫ τ)).obj F by
      rw [hκc, Category.assoc])),
    ← cancel_mono (eqToHom (show (Pb ((c ≫ b) ≫ σ)).obj F = (Pb (κ ≫ γ ≫ σ)).obj F by
      rw [hκc, Category.assoc]))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  exact h.symm

/-- **The cocycle law for a transported descent datum.**  If `α` satisfies the cocycle law for
the square `(γ, q₁, q₂)` and `β` is its transport along the base change `(a, b, κ)`, then `β`
satisfies the cocycle law for the square `(c, p₁, p₂)`. -/
theorem cocycle_transport {c p₁ p₂ : P ⟶ A} {γ q₁ q₂ : P' ⟶ A'} {κ : P ⟶ P'}
    (hs : b ≫ σ = s ≫ a) (ht : b ≫ τ = t ≫ a)
    (hκ₁ : κ ≫ q₁ = p₁ ≫ b) (hκ₂ : κ ≫ q₂ = p₂ ≫ b) (hκc : c ≫ b = κ ≫ γ)
    (htc : c ≫ t = p₁ ≫ t) (hcond : p₁ ≫ s = p₂ ≫ t) (hsc : c ≫ s = p₂ ≫ s)
    (htc' : γ ≫ τ = q₁ ≫ τ) (hcond' : q₁ ≫ σ = q₂ ≫ τ) (hsc' : γ ≫ σ = q₂ ≫ σ)
    (F : D U') (α : (Pb τ).obj F ⟶ (Pb σ).obj F)
    (hα : eqToHom (by rw [htc']) ≫ rdx Pb Cmp q₁ α ≫ eqToHom (by rw [hcond']) ≫
        rdx Pb Cmp q₂ α ≫ eqToHom (by rw [hsc']) = rdx Pb Cmp γ α)
    (β : (Pb t).obj ((Pb a).obj F) ⟶ (Pb s).obj ((Pb a).obj F))
    (hβ : β = (Cmp t a).hom.app F ≫
      (eqToHom (by rw [ht]) ≫ rdx Pb Cmp b α ≫ eqToHom (by rw [hs])) ≫
      (Cmp s a).inv.app F) :
    eqToHom (by rw [htc]) ≫ rdx Pb Cmp p₁ β ≫ eqToHom (by rw [hcond]) ≫
        rdx Pb Cmp p₂ β ≫ eqToHom (by rw [hsc]) = rdx Pb Cmp c β := by
  subst hβ
  simp only [rdx_conj Pb Cmp hP hs ht F α]
  rw [fiveFold_junction Pb Cmp htc hcond hsc a F]
  rw [← cancel_epi ((Cmp (c ≫ t) a).inv.app F)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← cancel_mono ((Cmp (c ≫ s) a).hom.app F)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← cancel_epi (eqToHom (show (Pb ((c ≫ b) ≫ τ)).obj F = (Pb ((c ≫ t) ≫ a)).obj F by
      rw [Category.assoc, Category.assoc, ht])),
    ← cancel_mono (eqToHom (show (Pb ((c ≫ s) ≫ a)).obj F = (Pb ((c ≫ b) ≫ σ)).obj F by
      rw [Category.assoc, Category.assoc, hs]))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact rdx_transport_cocycle Pb Cmp hP hκ₁ hκ₂ hκc htc' hcond' hsc' F α hα

/-- **The normalization law for a transported descent datum.**  If `α` is normalized along the
identity section `eH` and `β` is its transport along the base change `(a, b)`, then `β` is
normalized along the identity section `eG`. -/
theorem identity_transport {eG : U ⟶ A} {eH : U' ⟶ A'}
    (hs : b ≫ σ = s ≫ a) (ht : b ≫ τ = t ≫ a) (hid : eG ≫ b = a ≫ eH)
    (hGt : eG ≫ t = 𝟙 U) (hGs : eG ≫ s = 𝟙 U)
    (hHt : eH ≫ τ = 𝟙 U') (hHs : eH ≫ σ = 𝟙 U')
    (F : D U') (α : (Pb τ).obj F ⟶ (Pb σ).obj F)
    (hα : rdx Pb Cmp eH α = eqToHom (by rw [hHt, hHs]))
    (β : (Pb t).obj ((Pb a).obj F) ⟶ (Pb s).obj ((Pb a).obj F))
    (hβ : β = (Cmp t a).hom.app F ≫
      (eqToHom (by rw [ht]) ≫ rdx Pb Cmp b α ≫ eqToHom (by rw [hs])) ≫
      (Cmp s a).inv.app F) :
    rdx Pb Cmp eG β = eqToHom (by rw [hGt, hGs]) := by
  subst hβ
  rw [rdx_conj Pb Cmp hP hs ht F α eG, rdx_congr Pb Cmp hid α, rdx_comp_left Pb Cmp hP,
    hα, rdx_eqToHom Pb Cmp a (show eH ≫ τ = eH ≫ σ by rw [hHt, hHs]) F]
  simp only [eqToHom_trans]
  rw [Cmp_hom_eqToHom_inv Pb Cmp (show eG ≫ t = eG ≫ s by rw [hGt, hGs]) a F]

end Transport

end Abstract

section Schemes

variable {X Y Z W : Scheme.{u}}

open AlgebraicGeometry.Scheme.Modules

/-- `Stacks.Groupoids.reindexHom` is the abstract reindexing for the pullback of sheaves of
modules along morphisms of schemes. -/
theorem rdx_eq_reindexHom (f : X ⟶ Y) {g h : Y ⟶ Z} {F : Z.Modules}
    (α : (pullback g).obj F ⟶ (pullback h).obj F) :
    rdx (fun {_ _} m ↦ pullback m) (fun {_ _ _} m n ↦ pullbackComp m n) f α =
      Stacks.Groupoids.reindexHom f α :=
  rfl

/-- The associativity constraint of the pullback pseudofunctor of sheaves of modules on
schemes, evaluated at a module. -/
theorem pullbackComp_pentagon (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W) (F : W.Modules) :
    (pullbackComp u (g ≫ v)).inv.app F ≫
        (pullback u).map ((pullbackComp g v).inv.app F) ≫
        (pullbackComp u g).hom.app ((pullback v).obj F) ≫
        (pullbackComp (u ≫ g) v).hom.app F =
      eqToHom (by rw [Category.assoc]) :=
  by simpa using NatTrans.congr_app (pseudofunctor_associativity u g v) F

/-- The comparison isomorphism for pullback along equal morphisms is the canonical
`eqToHom`. -/
theorem pullbackCongr_hom_app {f g : X ⟶ Y} (hf : f = g) (F : Y.Modules) :
    (pullbackCongr hf).hom.app F = eqToHom (by rw [hf]) := by
  subst hf; simp [pullbackCongr]

end Schemes

end Stacks.Modules

namespace Stacks.Groupoids

namespace GroupoidScheme

open AlgebraicGeometry.Scheme.Modules Stacks.Modules

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- The composition morphism of a groupoid scheme followed by the target, on underlying
schemes. -/
theorem comp_left_comp_target_left (G : GroupoidScheme S) :
    G.comp.left ≫ G.target.left =
      (Limits.pullback.fst G.source G.target).left ≫ G.target.left := by
  rw [← Over.comp_left, ← Over.comp_left, G.target_comp]

/-- The composition morphism of a groupoid scheme followed by the source, on underlying
schemes. -/
theorem comp_left_comp_source_left (G : GroupoidScheme S) :
    G.comp.left ≫ G.source.left =
      (Limits.pullback.snd G.source G.target).left ≫ G.source.left := by
  rw [← Over.comp_left, ← Over.comp_left, G.source_comp]

/-- Composability of the two projections of the scheme of composable arrows, on underlying
schemes. -/
theorem fst_left_comp_source_left (G : GroupoidScheme S) :
    (Limits.pullback.fst G.source G.target).left ≫ G.source.left =
      (Limits.pullback.snd G.source G.target).left ≫ G.target.left := by
  rw [← Over.comp_left, ← Over.comp_left, Limits.pullback.condition]

/-- The composable-arrows map of a morphism of groupoid schemes commutes with the first
projection, on underlying schemes. -/
theorem mapComposable_left_comp_fst_left (f : Hom G H) :
    f.mapComposable.left ≫ (Limits.pullback.fst H.source H.target).left =
      (Limits.pullback.fst G.source G.target).left ≫ f.mapArrows.left := by
  rw [← Over.comp_left, ← Over.comp_left, Hom.mapComposable, Limits.pullback.lift_fst]

/-- The composable-arrows map of a morphism of groupoid schemes commutes with the second
projection, on underlying schemes. -/
theorem mapComposable_left_comp_snd_left (f : Hom G H) :
    f.mapComposable.left ≫ (Limits.pullback.snd H.source H.target).left =
      (Limits.pullback.snd G.source G.target).left ≫ f.mapArrows.left := by
  rw [← Over.comp_left, ← Over.comp_left, Hom.mapComposable, Limits.pullback.lift_snd]

/-- A morphism of groupoid schemes commutes with composition of arrows, on underlying
schemes. -/
theorem comp_left_comp_mapArrows_left (f : Hom G H) :
    G.comp.left ≫ f.mapArrows.left = f.mapComposable.left ≫ H.comp.left := by
  rw [← Over.comp_left, ← Over.comp_left, f.comp_mapArrows]

/-- A morphism of groupoid schemes commutes with the identity sections, on underlying
schemes. -/
theorem mapObjects_left_comp_identity_left (f : Hom G H) :
    f.mapObjects.left ≫ H.identity.left = G.identity.left ≫ f.mapArrows.left := by
  rw [← Over.comp_left, ← Over.comp_left, f.map_identity]

/-- The successive-descent morphism, with the comparisons between pullbacks along equal
morphisms written as canonical `eqToHom`s. -/
theorem successiveDescent_eq (G : GroupoidScheme S) {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) :
    successiveDescent G α =
      eqToHom (by rw [comp_left_comp_target_left G]) ≫
        reindexHom (Limits.pullback.fst G.source G.target).left α ≫
        eqToHom (by rw [fst_left_comp_source_left G]) ≫
        reindexHom (Limits.pullback.snd G.source G.target).left α ≫
        eqToHom (by rw [comp_left_comp_source_left G]) := by
  rw [successiveDescent]
  simp only [pullbackCongr_hom_app]

/-- The identity-descent morphism, with the comparisons between pullbacks along equal
morphisms written as canonical `eqToHom`s. -/
theorem identityDescent_eq (G : GroupoidScheme S) {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) :
    identityDescent G α =
      (pullbackId G.objects.left).inv.app F ≫
        eqToHom (by rw [identity_left_comp_target_left G]) ≫
        reindexHom G.identity.left α ≫
        eqToHom (by rw [identity_left_comp_source_left G]) ≫
        (pullbackId G.objects.left).hom.app F := by
  rw [identityDescent]
  simp only [pullbackCongr_hom_app]

/-- The pulled-back descent morphism, with the comparisons between pullbacks along equal
morphisms written as canonical `eqToHom`s and the middle part bracketed. -/
theorem pullbackDescent_eq (f : Hom G H) (M : QuasicoherentModule H) :
    pullbackDescent f M =
      (pullbackComp G.target.left f.mapObjects.left).hom.app M.module ≫
        (eqToHom (by rw [f.map_target_left]) ≫
          reindexHom f.mapArrows.left M.alpha ≫
          eqToHom (by rw [f.map_source_left])) ≫
        (pullbackComp G.source.left f.mapObjects.left).inv.app M.module := by
  rw [pullbackDescent]
  simp only [pullbackCongr_hom_app, Category.assoc]

/-- A descent morphism is normalized along the identity section as soon as its reindexing
along that section is the canonical isomorphism between the two pullbacks. -/
theorem identityDescent_eq_id (G : GroupoidScheme S) {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (h : reindexHom G.identity.left α = eqToHom (by
      rw [identity_left_comp_target_left G, identity_left_comp_source_left G])) :
    identityDescent G α = 𝟙 F := by
  rw [identityDescent_eq, h]
  simp

/-- Pulling `M.alpha` back along the identity section is the canonical isomorphism between the
two pullbacks along the legs of that section.  This is the content of the normalization law
carried by every quasi-coherent module on a groupoid scheme. -/
theorem reindexHom_identity_alpha (M : QuasicoherentModule H) :
    reindexHom H.identity.left M.alpha = eqToHom (by
      rw [identity_left_comp_target_left H, identity_left_comp_source_left H]) := by
  have h := M.identity
  rw [identityDescent_eq] at h
  rw [← cancel_epi (eqToHom (show
        (Scheme.Modules.pullback (𝟙 H.objects.left)).obj M.module =
        (Scheme.Modules.pullback (H.identity.left ≫ H.target.left)).obj M.module by
      rw [identity_left_comp_target_left H])),
    ← cancel_mono (eqToHom (show
        (Scheme.Modules.pullback (H.identity.left ≫ H.source.left)).obj M.module =
        (Scheme.Modules.pullback (𝟙 H.objects.left)).obj M.module by
      rw [identity_left_comp_source_left H])),
    ← cancel_epi ((pullbackId H.objects.left).inv.app M.module),
    ← cancel_mono ((pullbackId H.objects.left).hom.app M.module)]
  simp only [Category.assoc] at h ⊢
  rw [h]
  simp

end GroupoidScheme

end Stacks.Groupoids

namespace Stacks.Modules

/-- **The cocycle law for the canonical comparison of iterated inverse images.**  Let `G` be a
groupoid scheme with object scheme `U` and arrow scheme `R`, and let `𝒢` be a module on `U`.
The equality `t ∘ c = t ∘ pr₀` of morphisms from the scheme of composable arrows to `U` gives a
canonical identification `θ : pr₀^* t^* 𝒢 ⟶ c^* t^* 𝒢`, and this says that `θ` satisfies the
cocycle law of the auxiliary groupoid `(R, R ×_{s, U, t} R, c, pr₀)` on any scheme carrying three
morphisms into the scheme of composable arrows which satisfy that groupoid's three identities.

The reason is that `θ` is the transport, along the base change `t`, of the trivial descent
morphism on `𝒢`, so `Stacks.Modules.cocycle_transport` applies; `θ` is taken as an argument,
pinned down by `hθ`, so that the statement does not mention any particular construction of it. -/
theorem cocycle_of_trivialDescent {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (𝒢 : G.objects.left.Modules) {T : Scheme.{u}}
    (p₀ p₁ cc : T ⟶ (Limits.pullback G.source G.target).left)
    (htc : cc ≫ (Limits.pullback.fst G.source G.target).left =
      p₀ ≫ (Limits.pullback.fst G.source G.target).left)
    (hcond : p₀ ≫ G.comp.left = p₁ ≫ (Limits.pullback.fst G.source G.target).left)
    (hsc : cc ≫ G.comp.left = p₁ ≫ G.comp.left)
    (θ : (Scheme.Modules.pullback (Limits.pullback.fst G.source G.target).left).obj
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ⟶
        (Scheme.Modules.pullback G.comp.left).obj
          ((Scheme.Modules.pullback G.target.left).obj 𝒢))
    (hθ : θ = (Scheme.Modules.pullbackComp
          (Limits.pullback.fst G.source G.target).left G.target.left).hom.app 𝒢 ≫
        (Scheme.Modules.pullbackCongr
            (Stacks.Groupoids.GroupoidScheme.comp_left_comp_target_left G).symm).hom.app 𝒢 ≫
        (Scheme.Modules.pullbackComp G.comp.left G.target.left).inv.app 𝒢) :
    (Scheme.Modules.pullbackCongr htc).hom.app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        Stacks.Groupoids.reindexHom p₀ θ ≫
        (Scheme.Modules.pullbackCongr hcond).hom.app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        Stacks.Groupoids.reindexHom p₁ θ ≫
        (Scheme.Modules.pullbackCongr hsc.symm).hom.app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) =
      Stacks.Groupoids.reindexHom cc θ := by
  have hb : p₀ ≫ G.comp.left ≫ G.target.left = p₁ ≫ G.comp.left ≫ G.target.left := by
    rw [← Category.assoc, hcond, Category.assoc,
      Stacks.Groupoids.GroupoidScheme.comp_left_comp_target_left G]
  have hs : (G.comp.left ≫ G.target.left) ≫ 𝟙 G.objects.left = G.comp.left ≫ G.target.left :=
    Category.comp_id _
  have ht : (G.comp.left ≫ G.target.left) ≫ 𝟙 G.objects.left =
      (Limits.pullback.fst G.source G.target).left ≫ G.target.left := by
    rw [Category.comp_id, Stacks.Groupoids.GroupoidScheme.comp_left_comp_target_left G]
  have hk₁ : (p₀ ≫ G.comp.left ≫ G.target.left) ≫ 𝟙 G.objects.left =
      p₀ ≫ (G.comp.left ≫ G.target.left) := Category.comp_id _
  have hk₂ : (p₀ ≫ G.comp.left ≫ G.target.left) ≫ 𝟙 G.objects.left =
      p₁ ≫ (G.comp.left ≫ G.target.left) := by
    rw [Category.comp_id]; exact hb
  have hkc : cc ≫ (G.comp.left ≫ G.target.left) =
      (p₀ ≫ G.comp.left ≫ G.target.left) ≫ 𝟙 G.objects.left := by
    rw [Category.comp_id, ← Category.assoc, hsc, Category.assoc]
    exact hb.symm
  simp only [pullbackCongr_hom_app]
  exact cocycle_transport
    (D := fun X : Scheme.{u} => X.Modules)
    (fun {_ _} m ↦ Scheme.Modules.pullback m)
    (fun {_ _ _} m n ↦ Scheme.Modules.pullbackComp m n)
    (fun {_ _ _ _} u g v F ↦ pullbackComp_pentagon u g v F)
    (s := G.comp.left) (t := (Limits.pullback.fst G.source G.target).left)
    (σ := 𝟙 G.objects.left) (τ := 𝟙 G.objects.left)
    (a := G.target.left) (b := G.comp.left ≫ G.target.left)
    (c := cc) (p₁ := p₀) (p₂ := p₁)
    (γ := 𝟙 G.objects.left) (q₁ := 𝟙 G.objects.left) (q₂ := 𝟙 G.objects.left)
    (κ := p₀ ≫ G.comp.left ≫ G.target.left)
    hs ht hk₁ hk₂ hkc htc hcond hsc rfl rfl rfl 𝒢 (𝟙 _)
    (by simp [rdx]) θ (by rw [hθ]; simp [rdx, pullbackCongr_hom_app])

end Stacks.Modules

end
