module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.TwoFibreProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The 2-fibre product of categories fibred in groupoids (Stacks 0041)

Fix a base category `𝒞`. Let `p𝒳`, `p𝒴`, `p𝒮` be categories fibred in groupoids over `𝒞` and
let `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` be 1-morphisms over `𝒞`. Stacks 0041 (Lemma 4.35.7) says that the
2-fibre product `𝒳 ×_𝒮 𝒴` of Stacks 0040 — `CategoryTheory.TwoFibreProductOver`, the same
construction used for fibred categories in Stacks 02XQ — is again fibred in groupoids over `𝒞`.

The proof is the one in the Stacks Project. By Stacks 02XQ the structure functor is a fibred
category, so by Stacks 003V
(`CategoryTheory.Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid`) it remains to
see that every fibre is a groupoid; and a morphism of the 2-fibre product lying over an identity
has both components lying over an isomorphism of `𝒞`, hence both components invertible, hence is
itself invertible. The hypotheses on `F` and `G` are only that they are strictly over `𝒞`: in a
category fibred in groupoids *every* morphism is strongly cartesian, so a functor strictly over
`𝒞` between categories fibred in groupoids is automatically a 1-morphism of fibred categories
(`CategoryTheory.Functor.IsFiberedInGroupoids.isFibredOneMorphism`), which is what feeds Stacks
02XQ.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.isFibredOneMorphism`: a functor strictly over `𝒞`
  into a category fibred in groupoids is a 1-morphism of fibred categories.
* `CategoryTheory.TwoFibreProductOver.isIso_of_components`: a morphism of the 2-fibre product with
  invertible data is invertible.
* `CategoryTheory.TwoFibreProductOver.isIso_of_isHomLift_id`: a vertical morphism of the
  2-fibre product of categories fibred in groupoids is invertible.
* `CategoryTheory.TwoFibreProductOver.fiber_isGroupoid`: the fibres are groupoids.
* `CategoryTheory.TwoFibreProductOver.isFiberedInGroupoids`: **Stacks 0041**.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {𝒮 : Type u₄} [Category.{v₄} 𝒮]

/-- A functor `F : 𝒳 ⥤ 𝒮` strictly over `𝒞` whose target `p𝒮` is fibred in groupoids is a
1-morphism of fibred categories over `𝒞`: preservation of strongly cartesian morphisms is free,
because in a category fibred in groupoids every morphism is strongly cartesian over its image. -/
@[sga "4 XVIII 1.4.6" "more general"]
theorem Functor.IsFiberedInGroupoids.isFibredOneMorphism {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞}
    (hp𝒮 : p𝒮.IsFiberedInGroupoids) {F : 𝒳 ⥤ 𝒮} (hF : F ⋙ p𝒮 = p𝒳) :
    Functor.IsFibredOneMorphism p𝒳 p𝒮 F where
  comp_eq := hF
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ hφ
    have := hφ.toIsHomLift
    have := Functor.isHomLift_map_of_comp_eq hF f φ
    exact hp𝒮.isStronglyCartesian_homLift f (F.map φ)

namespace TwoFibreProductOver

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- A morphism of the 2-fibre product all three of whose data are invertible is invertible: the
inverse is the componentwise inverse, and its comparison square is the inverted square. -/
lemma isIso_of_components {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (Φ : P ⟶ Q)
    [IsIso Φ.hbase] [IsIso Φ.a] [IsIso Φ.b] : IsIso Φ := by
  have := Φ.ha
  have := Φ.hb
  refine ⟨⟨{ hbase := inv Φ.hbase, a := inv Φ.a, b := inv Φ.b
             ha := IsHomLift.inv p𝒳 Φ.hbase Φ.a
             hb := IsHomLift.inv p𝒴 Φ.hbase Φ.b
             w := ?_ }, ?_, ?_⟩⟩
  · simp only [Functor.map_inv]
    rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq]
    exact Φ.w.symm
  · exact Hom.ext' (by simp) (by simp)
  · exact Hom.ext' (by simp) (by simp)

/-- A morphism of the 2-fibre product lying over an identity of `𝒞` is an isomorphism, as soon as
`p𝒳` and `p𝒴` are fibred in groupoids.

Its base morphism is an `eqToHom` and hence invertible; each of its two components lies over that
base morphism and is therefore strongly cartesian over an isomorphism, hence invertible; so
`isIso_of_components` applies. -/
lemma isIso_of_isHomLift_id (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    {U : 𝒞} {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (Φ : P ⟶ Q)
    (hΦ : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 U) Φ) : IsIso Φ := by
  have := hΦ
  have hbase : IsIso ((structureFunctor p𝒳 p𝒴 p𝒮 F G).map Φ) := by
    rw [IsHomLift.fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) (𝟙 U) Φ]; infer_instance
  have : IsIso Φ.hbase := by rwa [structureFunctor_map] at hbase
  have := Φ.ha
  have := Φ.hb
  have := h𝒳.isStronglyCartesian_homLift Φ.hbase Φ.a
  have := h𝒴.isStronglyCartesian_homLift Φ.hbase Φ.b
  have : IsIso Φ.a :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p𝒳) (f := Φ.hbase) Φ.a
  have : IsIso Φ.b :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p𝒴) (f := Φ.hbase) Φ.b
  exact isIso_of_components Φ

/-- The fibre inclusion sends a morphism of the fibre, given as a morphism lying over the
identity, back to that morphism. -/
private lemma fiberInclusion_map_mk {𝒟 𝒵 : Type*} [Category 𝒟] [Category 𝒵] {q : 𝒵 ⥤ 𝒟}
    {U : 𝒟} {X Y : q.Fiber U}
    (f : Functor.Fiber.fiberInclusion.obj X ⟶ Functor.Fiber.fiberInclusion.obj Y)
    (h : q.IsHomLift (𝟙 U) f) : Functor.Fiber.fiberInclusion.map (⟨f, h⟩ : X ⟶ Y) = f :=
  rfl

/-- Every fibre of the 2-fibre product of categories fibred in groupoids is a groupoid: a morphism
of the fibre over `U` lies over `𝟙 U`, so `isIso_of_isHomLift_id` applies. -/
lemma fiber_isGroupoid (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids) (U : 𝒞) :
    IsGroupoid ((structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) where
  all_isIso {X Y} m := by
    have hM : IsIso (Functor.Fiber.fiberInclusion.map m) :=
      isIso_of_isHomLift_id h𝒳 h𝒴 _ m.2
    have hinv : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 U)
        (@inv _ _ _ _ (Functor.Fiber.fiberInclusion.map m) hM) :=
      IsHomLift.lift_id_inv_isIso _ U _
    refine ⟨⟨⟨_, hinv⟩, ?_, ?_⟩⟩ <;>
      exact Functor.Fiber.fiberInclusion.map_injective (by simp [fiberInclusion_map_mk])

/-- **Stacks 0041.** The 2-category of categories fibred in groupoids over `𝒞` has 2-fibre
products, given by the construction of Stacks 0040: if `p𝒳`, `p𝒴`, `p𝒮` are fibred in groupoids
and `F`, `G` are strictly over `𝒞`, then the structure functor of `𝒳 ×_𝒮 𝒴` is fibred in
groupoids. -/
@[stacks 0041]
theorem isFiberedInGroupoids (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒮 : p𝒮.IsFiberedInGroupoids) (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFiberedInGroupoids := by
  have := h𝒳.isFibered
  have := h𝒴.isFibered
  have := h𝒮.isFibered
  have := TwoFibreProductOver.isFibered_structureFunctor p𝒳 p𝒴 p𝒮 F G (h𝒮.isFibredOneMorphism hF)
    (h𝒮.isFibredOneMorphism hG)
  exact Functor.IsFiberedInGroupoids.mk' (fiber_isGroupoid h𝒳 h𝒴)

end TwoFibreProductOver

end CategoryTheory
