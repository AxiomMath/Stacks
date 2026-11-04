module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered

/-!
# Lifting and factoring morphisms in a category cofibered in groupoids

A category cofibered in groupoids has a pushforward along every morphism of the base, and
every morphism of the total category is strongly cocartesian over its image. This file
collects the consequences used repeatedly in deformation theory: a morphism lying over an
isomorphism is an isomorphism, a morphism lying over a composite factors accordingly, a
morphism out of a pushforward is determined by its composite with the pushforward morphism,
and a prescribed isomorphism of the base is realized by an isomorphism of the total category.

Nothing here is a statement of the Stacks Project; these are the shared tools for testing
smoothness and Schlessinger's conditions on small extensions.

## Main results

* `Deformation.isHomLift_comp`: lifts compose.
* `Deformation.isIso_of_isIso_map`: a morphism over an isomorphism is an isomorphism.
* `Deformation.exists_factor_of_isHomLift_comp`: a morphism over `f ≫ g` factors as a
  morphism over `f` followed by one over `g`.
* `Deformation.exists_isHomLift_of_iso`: an isomorphism of the base with prescribed target
  object is realized by an isomorphism of the total category.
* `Deformation.exists_factor_through_pushforward`: factoring through a pushforward.
* `Deformation.eq_of_factor_through_pushforward`: two such factorizations agree.
* `Deformation.existsUnique_factor_of_isHomLift`: the factorization through a pushforward is
  unique.
* `Deformation.exists_pushforward_codomain`: the pushforward of an object, together with the
  identification of its image.
* `Deformation.exists_pow_maximalIdeal_eq_bot`: a power of the maximal ideal of an object of
  `𝒞_Λ` vanishes.

## Implementation notes

The cofibered condition is `Functor.IsFiberedInGroupoids` on the opposite functor, so these
proofs pass to opposites, use the fibered API there, and come back. Where the argument can be
phrased with `Deformation.isStronglyCocartesian_of_isCofiberedInGroupoids` it is, since the
strongly cocartesian universal property is the direct form needed.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
universe u v u₁ v₁ u₂ v₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}

/-- A morphism over `f` followed by a morphism over `g` lies over `f ≫ g`. -/
theorem isHomLift_comp {R S T : C} {x y z : F} {f : R ⟶ S} {g : S ⟶ T}
    {a : x ⟶ y} {b : y ⟶ z} (ha : p.IsHomLift f a) (hb : p.IsHomLift g b) :
    p.IsHomLift (f ≫ g) (a ≫ b) := by
  let _ : p.IsHomLift f a := ha
  let _ : p.IsHomLift g b := hb
  exact IsHomLift.comp p f g a b

/-- In a category cofibered in groupoids, a morphism whose image is an isomorphism is itself
an isomorphism. -/
theorem isIso_of_isIso_map (hp : IsCofiberedInGroupoids p) {x y : F} (f : x ⟶ y)
    [IsIso (p.map f)] : IsIso f := by
  let _ : p.IsStronglyCocartesian (p.map f) f :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp (p.map f) f (IsHomLift.map p f)
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p (p.map f) f

/-- A morphism of the total category lying over a composite factors as a morphism over the
first factor followed by a morphism over the second. -/
theorem exists_factor_of_isHomLift_comp (hp : IsCofiberedInGroupoids p)
    {R S T : C} (f : R ⟶ S) (g : S ⟶ T) {x z : F} (m : x ⟶ z)
    (hm : p.IsHomLift (f ≫ g) m) :
    ∃ (y : F) (q : x ⟶ y) (r : y ⟶ z),
      p.IsHomLift f q ∧ p.IsHomLift g r ∧ q ≫ r = m := by
  let _ : p.IsHomLift (f ≫ g) m := hm
  have hx : p.obj x = R := IsHomLift.domain_eq p (f ≫ g) m
  have hz : p.obj z = T := IsHomLift.codomain_eq p (f ≫ g) m
  subst R T
  obtain ⟨yop, qop, hqop⟩ := hp.exists_lift f.op (Opposite.op x) rfl
  let y := Opposite.unop yop
  have hy : p.obj y = S := by
    have h := IsHomLift.domain_eq p.op f.op qop
    simpa [y] using congrArg Opposite.unop h
  subst S
  let q := qop.unop
  let _ : p.op.IsHomLift f.op qop := hqop
  have hq : p.IsHomLift f q := by
    have hmap := IsHomLift.eq_of_isHomLift p.op f.op qop
    have hmap' : p.map q = f := by
      simpa [q] using (congrArg Quiver.Hom.unop hmap).symm
    exact hmap' ▸ IsHomLift.map p q
  let _ : p.op.IsStronglyCartesian f.op qop := hp.isStronglyCartesian_homLift _ _
  have hmop : p.op.IsHomLift (g.op ≫ f.op) m.op := by
    have heq : f ≫ g = p.map m := IsHomLift.eq_of_isHomLift p (f ≫ g) m
    have hmap : p.op.map m.op = g.op ≫ f.op := by
      show (p.map m).op = g.op ≫ f.op
      rw [← heq, op_comp]
    exact hmap ▸ IsHomLift.map p.op m.op
  let _ : p.op.IsHomLift (g.op ≫ f.op) m.op := hmop
  obtain ⟨rop, ⟨hrop, hfac⟩, -⟩ :=
    (inferInstance : p.op.IsStronglyCartesian f.op qop).universal_property' g.op m.op
  let r := rop.unop
  have hr : p.IsHomLift g r := by
    have hmap := IsHomLift.eq_of_isHomLift p.op g.op rop
    have hmap' : p.map r = g := by
      simpa [r] using (congrArg Quiver.Hom.unop hmap).symm
    exact hmap' ▸ IsHomLift.map p r
  refine ⟨y, q, r, hq, hr, ?_⟩
  apply Quiver.Hom.op_inj
  simpa [q, r] using hfac

/-- An isomorphism of the base lifts to an isomorphism of the total category with a prescribed
target object. -/
theorem exists_isHomLift_of_iso (hp : IsCofiberedInGroupoids p)
    {R S : C} (e : R ≅ S) {x : F} (hx : p.obj x = S) :
    ∃ (y : F) (l : y ⟶ x), p.IsHomLift e.hom l ∧ IsIso l := by
  subst S
  obtain ⟨yop, qop, hqop⟩ := hp.exists_lift e.inv.op (Opposite.op x) rfl
  let y := Opposite.unop yop
  have hy : p.obj y = R := by
    have h := IsHomLift.domain_eq p.op e.inv.op qop
    simpa [y] using congrArg Opposite.unop h
  subst R
  let m : x ⟶ y := qop.unop
  let _ : p.op.IsHomLift e.inv.op qop := hqop
  let _ : p.op.IsStronglyCartesian e.inv.op qop := hp.isStronglyCartesian_homLift _ _
  let _ : IsIso e.inv.op := isIso_op e.inv
  have hqiso : IsIso qop :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p.op) (f := e.inv.op) qop
  let _ : IsIso m := isIso_of_op m
  have hm : p.IsHomLift e.inv m := by
    have hmap := IsHomLift.eq_of_isHomLift p.op e.inv.op qop
    have hmap' : p.map m = e.inv := by
      show (p.op.map qop).unop = e.inv
      exact congrArg Quiver.Hom.unop hmap.symm
    exact hmap' ▸ IsHomLift.map p m
  have hl : p.IsHomLift e.hom (inv m) := by
    let _ : p.IsHomLift e.inv m := hm
    simpa using IsHomLift.inv p e.inv m
  exact ⟨y, inv m, hl, inferInstance⟩

/-- A morphism out of the source of a pushforward whose image factors through the base of the
pushforward factors through the pushforward. -/
theorem exists_factor_through_pushforward (hp : IsCofiberedInGroupoids p)
    {B : C} {a b c : F} (f : p.obj a ⟶ B) (i : a ⟶ b) (hi : p.IsHomLift f i)
    (g : B ⟶ p.obj c) (φ : a ⟶ c) (hbase : p.map φ = f ≫ g) :
    ∃ ψ : b ⟶ c, p.IsHomLift g ψ ∧ i ≫ ψ = φ := by
  let _ : p.IsStronglyCocartesian f i :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp f i hi
  obtain ⟨ψ, ⟨hψ, hfac⟩, -⟩ :=
    Functor.IsStronglyCocartesian.universal_property p f i g (p.map φ) hbase φ
  exact ⟨ψ, hψ, hfac⟩

/-- Two factorizations of one morphism through a pushforward, both lying over the same base
morphism, are equal. -/
theorem eq_of_factor_through_pushforward (hp : IsCofiberedInGroupoids p)
    {a b c : F} (f : p.obj a ⟶ p.obj b) (i : a ⟶ b) (hi : p.IsHomLift f i)
    (g : p.obj b ⟶ p.obj c) {φ : a ⟶ c} (hbase : p.map φ = f ≫ g)
    (θ₁ θ₂ : b ⟶ c) (hθ₁ : p.IsHomLift g θ₁) (hθ₂ : p.IsHomLift g θ₂)
    (hfac₁ : i ≫ θ₁ = φ) (hfac₂ : i ≫ θ₂ = φ) : θ₁ = θ₂ := by
  let _ : p.IsStronglyCocartesian f i :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp f i hi
  obtain ⟨ψ, -, huniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property p f i g (p.map φ) hbase φ
  exact (huniq θ₁ ⟨hθ₁, hfac₁⟩).trans (huniq θ₂ ⟨hθ₂, hfac₂⟩).symm

/-- The factorization of a morphism through a pushforward is unique. -/
theorem existsUnique_factor_of_isHomLift (hp : IsCofiberedInGroupoids p)
    {a b c : F} (φ : a ⟶ b) (ψ : a ⟶ c) (f : p.obj b ⟶ p.obj c)
    (h : p.map φ ≫ f = p.map ψ) :
    ∃! χ : b ⟶ c, p.map χ = f ∧ φ ≫ χ = ψ := by
  have hop : f.op ≫ p.op.map φ.op = p.op.map ψ.op := by
    show (p.map φ ≫ f).op = (p.map ψ).op
    exact congrArg Opposite.op h
  obtain ⟨χop, hχ, hχuniq⟩ := hp.unique_lift φ.op ψ.op f.op hop
  refine ⟨χop.unop, ?_, ?_⟩
  · rcases hχ with ⟨hmap, hcomp⟩
    refine ⟨?_, ?_⟩
    · change (p.map χop.unop).op = f.op at hmap
      exact Opposite.op_injective hmap
    · change (φ ≫ χop.unop).op = ψ.op at hcomp
      exact Opposite.op_injective hcomp
  · intro χ hχ'
    have hEq : χ.op = χop := hχuniq χ.op (by
      refine ⟨?_, ?_⟩
      · show (p.map χ).op = f.op
        exact congrArg Opposite.op hχ'.1
      · show χ.op ≫ φ.op = ψ.op
        exact congrArg Quiver.Hom.op hχ'.2)
    cases hEq
    rfl

/-- The pushforward of an object along a morphism of the base, together with the
identification of the image of the pushforward. -/
theorem exists_pushforward_codomain (hp : IsCofiberedInGroupoids p)
    {a : F} {A B : C} (ha : p.obj a = A) (f : A ⟶ B) :
    ∃ (b : F) (φ : a ⟶ b), p.obj b = B ∧ p.IsHomLift f φ := by
  obtain ⟨b, φ, hφ⟩ := exists_pushforward hp f a ha
  exact ⟨b, φ, IsHomLift.codomain_eq p f φ, hφ⟩

end

/-! ### Nilpotence of the maximal ideal in the base category -/

section
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The maximal ideal of an Artinian local algebra is nilpotent: some power of it, and hence
every later power, is the zero ideal. -/
theorem exists_pow_maximalIdeal_eq_bot (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp A.isArtinianRing
  exact ⟨n, by simp [pow_succ, hn]⟩

end

end Deformation

end
