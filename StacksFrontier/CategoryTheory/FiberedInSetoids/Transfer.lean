module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid

/-!
# Transferring the setoid condition

Two ways of recognising that a category is a setoid (`IsSetoidCategory`), and the companion
statements for the condition "any two objects are isomorphic", which together say that a category
is a setoid with exactly one isomorphism class.

The first is descent along a category fibred in groupoids: if `p : 𝒞 ⥤ 𝒟` is fibred in
groupoids, `𝒟` is a setoid and every fibre of `p` is a setoid, then `𝒞` is a setoid. The second
is transport along a functor: a groupoid admitting a faithful functor to a setoid is a setoid.

## Main results

* `IsSetoidCategory.of_isFiberedInGroupoids` and `nonempty_iso_of_isFiberedInGroupoids`:
  descent of the two conditions along a category fibred in groupoids.
* `IsSetoidCategory.of_faithful` and `nonempty_iso_of_isEquivalence`: transport of the two
  conditions along a faithful functor, respectively an equivalence.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]

/-- A morphism lying over an isomorphism in a category fibred in groupoids is an isomorphism. -/
private theorem isIso_of_isHomLift {p : 𝒞 ⥤ 𝒟} (hp : p.IsFiberedInGroupoids) {R S : 𝒟} {a b : 𝒞}
    {f : R ⟶ S} (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso f] : IsIso φ :=
  have := hp.isStronglyCartesian_homLift f φ
  Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := f) φ

/-- **Descent of the setoid condition along a category fibred in groupoids.** If `p : 𝒞 ⥤ 𝒟` is
fibred in groupoids, `𝒟` is a setoid and every fibre of `p` is a setoid, then so is `𝒞`. -/
theorem IsSetoidCategory.of_isFiberedInGroupoids (p : 𝒞 ⥤ 𝒟) (hp : p.IsFiberedInGroupoids)
    (h𝒟 : IsSetoidCategory 𝒟) (hfib : ∀ d : 𝒟, IsSetoidCategory (p.Fiber d)) :
    IsSetoidCategory 𝒞 := by
  refine ⟨fun g => ?_, fun x g => ?_⟩
  · have := h𝒟.1 (p.map g)
    exact isIso_of_isHomLift hp (f := p.map g) g
  · have : p.IsHomLift (𝟙 (p.obj x)) g :=
      IsHomLift.of_fac' p (𝟙 (p.obj x)) g rfl rfl (by simpa using h𝒟.2 (p.obj x) (p.map g))
    exact congrArg Functor.Fiber.fiberInclusion.map
      ((hfib (p.obj x)).2 _ (Functor.Fiber.homMk p (p.obj x) g))

/-- **Descent of "any two objects are isomorphic" along a category fibred in groupoids.** If
`p : 𝒞 ⥤ 𝒟` is fibred in groupoids, any two objects of `𝒟` are isomorphic and any two objects
of each fibre of `p` are isomorphic, then any two objects of `𝒞` are isomorphic. -/
theorem nonempty_iso_of_isFiberedInGroupoids (p : 𝒞 ⥤ 𝒟) (hp : p.IsFiberedInGroupoids)
    (h𝒟 : ∀ a b : 𝒟, Nonempty (a ≅ b))
    (hfib : ∀ (d : 𝒟) (a b : p.Fiber d), Nonempty (a ≅ b)) :
    ∀ x y : 𝒞, Nonempty (x ≅ y) := by
  intro x y
  obtain ⟨e⟩ := h𝒟 (p.obj x) (p.obj y)
  obtain ⟨x', φ, hφ⟩ := hp.exists_lift e.hom y rfl
  have : p.IsHomLift e.hom φ := hφ
  obtain ⟨eF⟩ := hfib (p.obj x) ⟨x, rfl⟩ ⟨x', IsHomLift.domain_eq p e.hom φ⟩
  exact ⟨Functor.Fiber.fiberInclusion.mapIso eF ≪≫
    @asIso _ _ _ _ φ (isIso_of_isHomLift hp (f := e.hom) φ)⟩

/-- **A groupoid with a faithful functor to a setoid is a setoid.** If `𝒞` is a groupoid and
`E : 𝒞 ⥤ 𝒟` is faithful with `𝒟` a setoid, then `𝒞` is a setoid. -/
theorem IsSetoidCategory.of_faithful (E : 𝒞 ⥤ 𝒟) (hE : E.Faithful) (h𝒞 : IsGroupoid 𝒞)
    (h𝒟 : IsSetoidCategory 𝒟) : IsSetoidCategory 𝒞 :=
  ⟨fun g => h𝒞.all_isIso g,
    fun x g => hE.map_injective ((h𝒟.2 (E.obj x) (E.map g)).trans (E.map_id x).symm)⟩

/-- **Transport of "any two objects are isomorphic" along an equivalence.** If `E : 𝒞 ⥤ 𝒟` is
an equivalence and any two objects of `𝒟` are isomorphic, then any two objects of `𝒞` are
isomorphic. -/
theorem nonempty_iso_of_isEquivalence (E : 𝒞 ⥤ 𝒟) (hE : E.IsEquivalence)
    (h𝒟 : ∀ a b : 𝒟, Nonempty (a ≅ b)) : ∀ x y : 𝒞, Nonempty (x ≅ y) := by
  intro x y
  have := hE
  exact (h𝒟 (E.obj x) (E.obj y)).map E.preimageIso

end
