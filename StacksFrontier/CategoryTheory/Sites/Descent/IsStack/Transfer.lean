module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.ClosureProperties

/-!
# Transfer along the inclusion of a full subcategory

Lifting, cartesianness and the fibres of `P.ι ⋙ p` are read off from those of `p`: a morphism of
`P.FullSubcategory` lifts `f` exactly when its image does, and it is (strongly) cartesian when its
image is. If the source of every strongly cartesian morphism into an object with property `P` is
isomorphic over the identity to an object with property `P`, then every morphism of the base has a
cartesian lift inside the subcategory at every object of it, and `P.ι` preserves cartesian
morphisms.

## Main definitions

* `CategoryTheory.Functor.fiberι` and `CategoryTheory.Functor.fiberιFunctor`, the inclusion read
  fibrewise.

## Main results

* `CategoryTheory.Functor.isHomLift_restrict_iff`,
  `CategoryTheory.Functor.isCartesian_of_isCartesian_map_ι` and
  `CategoryTheory.Functor.isStronglyCartesian_of_isStronglyCartesian_map_ι`, the transfer of the
  three predicates;
* `CategoryTheory.Functor.exists_isCartesian_restrict` and
  `CategoryTheory.Functor.isCartesian_map_ι`, the existence of cartesian lifts in the subcategory
  and the converse transfer of cartesianness, under the closure hypothesis above.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A morphism of `P.FullSubcategory` lifts `f` for `P.ι ⋙ p` exactly when its image lifts `f`
for `p`. -/
theorem isHomLift_restrict_iff (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳)
    {V U : 𝒮} {a b : P.FullSubcategory} (f : V ⟶ U) (φ : a ⟶ b) :
    (restrict p P).IsHomLift f φ ↔ p.IsHomLift f (P.ι.map φ) := by
  constructor
  · intro h
    refine IsHomLift.of_fac p f (P.ι.map φ) (IsHomLift.domain_eq (restrict p P) f φ)
      (IsHomLift.codomain_eq (restrict p P) f φ) ?_
    simpa using IsHomLift.fac (restrict p P) f φ
  · intro h
    refine IsHomLift.of_fac (restrict p P) f φ (IsHomLift.domain_eq p f (P.ι.map φ))
      (IsHomLift.codomain_eq p f (P.ι.map φ)) ?_
    simpa using IsHomLift.fac p f (P.ι.map φ)

/-- Unique factorisations through `P.ι.map φ` over `g` in `𝒳` yield unique factorisations through
`φ` over `g` in `P.FullSubcategory`. -/
private theorem existsUnique_restrict_of_existsUnique_map_ι (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳)
    {V' V : 𝒮} {a b a' : P.FullSubcategory} (g : V' ⟶ V) (φ : a ⟶ b) (φ' : a' ⟶ b)
    (H : ∃! χ : P.ι.obj a' ⟶ P.ι.obj a, p.IsHomLift g χ ∧ χ ≫ P.ι.map φ = P.ι.map φ') :
    ∃! χ : a' ⟶ a, (restrict p P).IsHomLift g χ ∧ χ ≫ φ = φ' := by
  obtain ⟨χ, ⟨hχlift, hχfac⟩, huniq⟩ := H
  obtain ⟨χ₀, hχ₀⟩ := P.ι.map_surjective χ
  refine ⟨χ₀, ⟨?_, ?_⟩, ?_⟩
  · exact (isHomLift_restrict_iff p P g χ₀).2 (hχ₀ ▸ hχlift)
  · apply P.ι.map_injective; rw [Functor.map_comp, hχ₀, hχfac]
  · intro y ⟨hy1, hy2⟩
    apply P.ι.map_injective; rw [hχ₀]
    exact huniq (P.ι.map y)
      ⟨(isHomLift_restrict_iff p P g y).1 hy1, by rw [← Functor.map_comp, hy2]⟩

/-- A morphism of `P.FullSubcategory` whose image under `P.ι` is `p`-cartesian is
`P.ι ⋙ p`-cartesian. -/
theorem isCartesian_of_isCartesian_map_ι (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳)
    {V U : 𝒮} {a b : P.FullSubcategory} (f : V ⟶ U) (φ : a ⟶ b)
    (h : p.IsCartesian f (P.ι.map φ)) : (restrict p P).IsCartesian f φ := by
  have : (restrict p P).IsHomLift f φ := (isHomLift_restrict_iff p P f φ).2 h.toIsHomLift
  apply IsCartesian.mk
  intro a' φ' hlift
  have hp' : p.IsHomLift f (P.ι.map φ') := (isHomLift_restrict_iff p P f φ').1 hlift
  exact existsUnique_restrict_of_existsUnique_map_ι p P (𝟙 V) φ φ'
    (h.universal_property (P.ι.map φ'))

/-- A morphism of `P.FullSubcategory` whose image under `P.ι` is strongly `p`-cartesian is
strongly `P.ι ⋙ p`-cartesian. -/
theorem isStronglyCartesian_of_isStronglyCartesian_map_ι (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳)
    {V U : 𝒮} {a b : P.FullSubcategory} (f : V ⟶ U) (φ : a ⟶ b)
    (h : p.IsStronglyCartesian f (P.ι.map φ)) : (restrict p P).IsStronglyCartesian f φ := by
  have : (restrict p P).IsHomLift f φ := (isHomLift_restrict_iff p P f φ).2 h.toIsHomLift
  apply IsStronglyCartesian.mk
  intro a' g φ' hlift
  have hp' : p.IsHomLift (g ≫ f) (P.ι.map φ') := (isHomLift_restrict_iff p P (g ≫ f) φ').1 hlift
  exact existsUnique_restrict_of_existsUnique_map_ι p P g φ φ'
    (h.universal_property' g (P.ι.map φ'))

/-- An object of the fibre of `P.ι ⋙ p` over `U`, viewed in the fibre of `p` over `U`. -/
@[implicit_reducible]
def fiberι (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) {U : 𝒮}
    (x : (restrict p P).Fiber U) : p.Fiber U := ⟨P.ι.obj x.1, x.2⟩

/-- The inclusion of the fibre of `P.ι ⋙ p` over `U` into the fibre of `p` over `U`, given by
`P.ι`; on objects it is `CategoryTheory.Functor.fiberι`. -/
@[implicit_reducible]
def fiberιFunctor (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) (U : 𝒮) :
    (restrict p P).Fiber U ⥤ p.Fiber U where
  obj x := fiberι p P x
  map φ := ⟨P.ι.map (Fiber.fiberInclusion.map φ),
    (isHomLift_restrict_iff p P (𝟙 U) _).1 φ.2⟩
  map_id _ := Fiber.hom_ext (P.ι.map_id _)
  map_comp _ _ := Fiber.hom_ext (P.ι.map_comp _ _)

/-- `fiberιFunctor` acts on morphisms of the fibre by `P.ι`. -/
@[simp]
lemma fiberInclusion_map_fiberιFunctor_map (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) {U : 𝒮}
    {x y : (restrict p P).Fiber U} (φ : x ⟶ y) :
    Fiber.fiberInclusion.map ((fiberιFunctor p P U).map φ) =
      P.ι.map (Fiber.fiberInclusion.map φ) := rfl

/-- Two composable morphisms in the fibre over `V` compose to a morphism in the fibre over `V`. -/
theorem isHomLift_id_comp (p : 𝒳 ⥤ 𝒮) {V : 𝒮} {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    (hφ : p.IsHomLift (𝟙 V) φ) (hψ : p.IsHomLift (𝟙 V) ψ) :
    p.IsHomLift (𝟙 V) (φ ≫ ψ) :=
  have := hφ
  have := hψ
  inferInstance

/-- If the source of every strongly cartesian morphism into an object with property `P` is
isomorphic over the identity to an object with property `P`, then every morphism `f` of the base
with target `p.obj b`, for `b` in the full subcategory, has a lift with target `b` inside the
subcategory which is cartesian both for `P.ι ⋙ p` and for `p`. -/
theorem exists_isCartesian_restrict (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) {V U : 𝒮} {b : P.FullSubcategory}
    (hb : p.obj (P.ι.obj b) = U) (f : V ⟶ U) :
    ∃ (a₀ : P.FullSubcategory) (θ' : a₀ ⟶ b),
      (restrict p P).IsCartesian f θ' ∧ p.IsCartesian f (P.ι.map θ') := by
  obtain ⟨w, ψ, hψ⟩ := IsPreFibered.exists_isCartesian p hb f
  obtain ⟨y', hy', e, he⟩ := h1 f ψ inferInstance b.2
  obtain rfl : p.obj w = V := IsHomLift.domain_eq p f ψ
  obtain ⟨θ', hθ'⟩ := P.ι.map_surjective (X := ⟨y', hy'⟩) (Y := b) (e.symm.hom ≫ ψ)
  have : p.IsHomLift (𝟙 (p.obj w)) e.symm.hom := IsHomLift.lift_id_inv p _ e
  have : p.IsCartesian f (P.ι.map θ') := hθ' ▸ inferInstance
  exact ⟨⟨y', hy'⟩, θ', isCartesian_of_isCartesian_map_ι p P f θ' this, this⟩

/-- If the source of every strongly cartesian morphism into an object with property `P` is
isomorphic over the identity to an object with property `P`, then the image under `P.ι` of a
`P.ι ⋙ p`-cartesian morphism is `p`-cartesian. -/
theorem isCartesian_map_ι (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) {V U : 𝒮} {a b : P.FullSubcategory}
    (f : V ⟶ U) (φ : a ⟶ b) (h : (restrict p P).IsCartesian f φ) :
    p.IsCartesian f (P.ι.map φ) := by
  have := h
  have : p.IsHomLift f (P.ι.map φ) := (isHomLift_restrict_iff p P f φ).1 inferInstance
  obtain ⟨a₀, θ', _, _⟩ :=
    exists_isCartesian_restrict p P h1 (IsHomLift.codomain_eq p f (P.ι.map φ)) f
  let e := IsCartesian.domainUniqueUpToIso (restrict p P) f θ' φ
  have : p.IsHomLift (𝟙 V) (P.ι.mapIso e).hom :=
    (isHomLift_restrict_iff p P (𝟙 V) e.hom).1 inferInstance
  have key : p.IsCartesian f ((P.ι.mapIso e).hom ≫ P.ι.map θ') := inferInstance
  rwa [Functor.mapIso_hom, ← Functor.map_comp, show e.hom ≫ θ' = φ by
    simpa only [e, IsCartesian.domainUniqueUpToIso_hom] using
      IsCartesian.fac (restrict p P) f θ' φ] at key

end Functor

end CategoryTheory
