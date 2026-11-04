module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase

/-!
# Stacks 04Y2: auxiliary lemmas on the 2-fibre product and its morphism presheaves

This file is the first part of the proof of Stacks 04Y2 (the stackification of a 2-fibre product
is the 2-fibre product of the stackifications), assembled in
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid`. It collects the
auxiliary material: morphisms and isomorphisms of the 2-fibre product `TwoFibreProductOver`
read through their components, the diagram chase at the heart of Stacks 04Y2, the behaviour of the
map of Stacks 042V on sections of the presheaves `Mor(x, y)`, and the `𝒳`- and `𝒵`-components
`morFstSection`, `morSndSection` of a section of the morphism presheaf of the 2-fibre product.

## References

* [StacksProject 04Y2](https://stacks.math.columbia.edu/tag/04Y2)
-/

@[expose] public section

-- The endpoints of the chosen cartesian lifts compared below are spelled through
-- `Functor.pullbackFiber`, `Functor.Fiber.fiberInclusion` and `Functor.fiberFunctorOfCompEq`, so
-- the instance arguments of `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe vb v u₀ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type u₀} [Category.{vb} 𝒞] {𝒳 : Type u₁} [Category.{v} 𝒳] {𝒴 : Type u₂}
  [Category.{v} 𝒴] {𝒵 : Type u₃} [Category.{v} 𝒵] {𝒳' : Type u₄} [Category.{v} 𝒳'] {𝒴' : Type u₅}
  [Category.{v} 𝒴'] {𝒵' : Type u₆} [Category.{v} 𝒵']

/-! ### Auxiliary material

The private lemmas below are the ingredients of the proof of Stacks 04Y2. -/

open Opposite _root_.CategoryTheory.Functor in
/-- A morphism of the 2-fibre product whose `𝒳`-component lies over `u` lies over `u`: the base
morphism is determined by the `𝒳`-component. -/
lemma isHomLift_of_isHomLift_a {𝒜 ℬ 𝒮 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒮]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮} {G : ℬ ⥤ 𝒮}
    {P Q : TwoFibreProductOver p𝒜 pℬ p𝒮 F G} (Φ : P ⟶ Q) {R T : 𝒞} (u : R ⟶ T)
    (hΦ : p𝒜.IsHomLift u Φ.a) : (structureFunctor p𝒜 pℬ p𝒮 F G).IsHomLift u Φ := by
  have := hΦ
  have hdom : p𝒜.obj P.x = R := IsHomLift.domain_eq p𝒜 u Φ.a
  have hcod : p𝒜.obj Q.x = T := IsHomLift.codomain_eq p𝒜 u Φ.a
  refine IsHomLift.of_fac' _ u Φ (P.hx.symm.trans hdom) (Q.hx.symm.trans hcod) ?_
  rw [structureFunctor_map, Hom.hbase_eq Φ, IsHomLift.fac' p𝒜 u Φ.a]
  simp

open Opposite _root_.CategoryTheory.Functor in
/-- The inverse of a vertical component of a natural isomorphism is vertical. -/
private lemma isHomLift_inv_app {𝒜 : Type*} [Category 𝒜] {p𝒜 : 𝒜 ⥤ 𝒞} {D : Type*} [Category D]
    {F G : D ⥤ 𝒜} (e : F ≅ G) {V : 𝒞} (X : D) (h : p𝒜.IsHomLift (𝟙 V) (e.hom.app X)) :
    p𝒜.IsHomLift (𝟙 V) (e.inv.app X) := by
  have := h
  have h3 : p𝒜.IsHomLift (𝟙 V) (inv (e.hom.app X)) := IsHomLift.lift_id_inv_isIso _ V (e.hom.app X)
  have heq : inv (e.hom.app X) = e.inv.app X := IsIso.inv_eq_of_hom_inv_id (by simp)
  rwa [heq] at h3

section

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'} {i : 𝒳 ⥤ 𝒳'} {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'}
  {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}

open Opposite _root_.CategoryTheory.Functor in
/-- The `𝒳`-component of `H` on a morphism, read through `γ`. -/
private lemma map_a_eq (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (φ : P ⟶ Q) :
    (H.map φ).a = γ.hom.app P ≫ i.map φ.a ≫ γ.inv.app Q := by
  have hn := γ.hom.naturality φ
  simp only [Functor.comp_map, fst_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

open Opposite _root_.CategoryTheory.Functor in
/-- The `𝒵`-component of `H` on a morphism, read through `δ`. -/
private lemma map_b_eq (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
    {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (φ : P ⟶ Q) :
    (H.map φ).b = δ.hom.app P ≫ k.map φ.b ≫ δ.inv.app Q := by
  have hn := δ.hom.naturality φ
  simp only [Functor.comp_map, snd_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

open Opposite _root_.CategoryTheory.Functor in
/-- `H` is strictly over `𝒞`: on objects because `γ` is vertical, on morphisms because the base
morphism of a morphism of the 2-fibre product is determined by its `𝒳`-component. -/
lemma comp_eq_of_gamma (hi : i ⋙ p𝒳' = p𝒳)
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    (hγ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒳'.IsHomLift (𝟙 P.base) (γ.hom.app P)) :
    H ⋙ structureFunctor p𝒳' p𝒵' p𝒴' f' g' = structureFunctor p𝒳 p𝒵 p𝒴 f g := by
  have key :
    ∀ (P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) (φ : P ⟶ Q), p𝒳'.IsHomLift φ.hbase (H.map φ).a := by
    intro P Q φ
    have := φ.ha
    have h1 : p𝒳'.IsHomLift φ.hbase (i.map φ.a) := Functor.isHomLift_map_of_comp_eq hi φ.hbase φ.a
    have h2 := hγ P
    have h3 := isHomLift_inv_app γ Q (hγ Q)
    rw [map_a_eq γ φ]
    infer_instance
  refine Functor.ext (fun P => ?_) (fun P Q φ => ?_)
  · have := hγ P
    exact ((H.obj P).hx).symm.trans (IsHomLift.domain_eq p𝒳' (𝟙 P.base) (γ.hom.app P))
  · have := isHomLift_of_isHomLift_a (H.map φ) φ.hbase (key P Q φ)
    exact IsHomLift.fac' (structureFunctor p𝒳' p𝒵' p𝒴' f' g') φ.hbase (H.map φ)

open Opposite _root_.CategoryTheory.Functor in
/-- The `𝒳`-component of an isomorphism of the 2-fibre product is an isomorphism. -/
lemma isIso_a {𝒜 ℬ 𝒮 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒮] {p𝒜 : 𝒜 ⥤ 𝒞}
    {pℬ : ℬ ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮} {G : ℬ ⥤ 𝒮} {P Q : TwoFibreProductOver p𝒜 pℬ p𝒮 F G}
    (Φ : P ⟶ Q) [IsIso Φ] : IsIso Φ.a :=
  ⟨(inv Φ).a, by rw [← comp_a, IsIso.hom_inv_id, id_a], by rw [← comp_a, IsIso.inv_hom_id, id_a]⟩

open Opposite _root_.CategoryTheory.Functor in
/-- The `𝒵`-component of an isomorphism of the 2-fibre product is an isomorphism. -/
private lemma isIso_b {𝒜 ℬ 𝒮 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒮] {p𝒜 : 𝒜 ⥤ 𝒞}
    {pℬ : ℬ ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮} {G : ℬ ⥤ 𝒮} {P Q : TwoFibreProductOver p𝒜 pℬ p𝒮 F G}
    (Φ : P ⟶ Q) [IsIso Φ] : IsIso Φ.b :=
  ⟨(inv Φ).b, by rw [← comp_b, IsIso.hom_inv_id, id_b], by rw [← comp_b, IsIso.inv_hom_id, id_b]⟩

open Opposite _root_.CategoryTheory.Functor in
/-- The component of the compatibility hypothesis `hψ` at an object `P₁`, composed with a morphism
`e : R ⟶ H P₁` of the 2-fibre product of the stackifications: the composite of `e` with `γ`, pushed
through `f'` and `α`, meets `j` of the comparison isomorphism of `P₁` in the comparison isomorphism
of `R`. This is the only place the compatibility hypothesis is used. -/
lemma compat_of_hpsi (α : i ⋙ f' ≅ f ⋙ j) (β : k ⋙ g' ≅ g ⋙ j)
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫ Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv)
    (P₁ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) {R : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    (e : R ⟶ H.obj P₁) :
    f'.map (e.a ≫ γ.hom.app P₁) ≫ α.hom.app P₁.x ≫ j.map P₁.iso.hom ≫ β.inv.app P₁.y =
      R.iso.hom ≫ g'.map (e.b ≫ δ.hom.app P₁) := by
  have hc := NatTrans.congr_app hψ P₁
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, psi_app] at hc
  calc
    f'.map (e.a ≫ γ.hom.app P₁) ≫ α.hom.app P₁.x ≫ j.map P₁.iso.hom ≫ β.inv.app P₁.y =
        f'.map e.a ≫
          (f'.map (γ.hom.app P₁) ≫ α.hom.app P₁.x ≫ j.map P₁.iso.hom ≫ β.inv.app P₁.y) := by
      rw [Functor.map_comp]
      simp [Category.assoc]
    _ = f'.map e.a ≫ (H.obj P₁).iso.hom ≫ g'.map (δ.hom.app P₁) := by
      rw [hc]
      rfl
    _ = R.iso.hom ≫ g'.map (e.b ≫ δ.hom.app P₁) := by
      rw [Functor.map_comp, ← Category.assoc, e.w]
      simp [Category.assoc]

open Opposite _root_.CategoryTheory.Functor in
/-- **The diagram chase at the heart of Stacks 04Y2.** If a morphism `M` of the 2-fibre product of
the stackifications is matched, through comparisons `EP`, `FP`, `EQ`, `FQ` satisfying the
compatibility of `CategoryTheory.TwoFibreProductOver.compat_of_hpsi`, by a pair of morphisms `a`,
`b` of `𝒳` and `𝒵`, then that pair satisfies the commuting square of the 2-fibre product *after*
applying `j`. -/
lemma heart (α : i ⋙ f' ≅ f ⋙ j) (β : k ⋙ g' ≅ g ⋙ j)
    {P₁ Q₁ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} {R S : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    {EP : R.x ⟶ i.obj P₁.x} {FP : R.y ⟶ k.obj P₁.y} {EQ : S.x ⟶ i.obj Q₁.x} {FQ : S.y ⟶ k.obj Q₁.y}
    [IsIso EP]
    (hP : f'.map EP ≫ α.hom.app P₁.x ≫ j.map P₁.iso.hom ≫ β.inv.app P₁.y = R.iso.hom ≫ g'.map FP)
    (hQ : f'.map EQ ≫ α.hom.app Q₁.x ≫ j.map Q₁.iso.hom ≫ β.inv.app Q₁.y = S.iso.hom ≫ g'.map FQ)
    (M : R ⟶ S) {a : P₁.x ⟶ Q₁.x} {b : P₁.y ⟶ Q₁.y} (ha : EP ≫ i.map a = M.a ≫ EQ)
    (hb : FP ≫ k.map b = M.b ≫ FQ) :
    j.map (f.map a ≫ Q₁.iso.hom) = j.map (P₁.iso.hom ≫ g.map b) := by
  have hαnat : α.hom.app P₁.x ≫ j.map (f.map a) = f'.map (i.map a) ≫ α.hom.app Q₁.x := by
    simpa only [Functor.comp_map] using (α.hom.naturality a).symm
  have hβnat : j.map (g.map b) ≫ β.inv.app Q₁.y = β.inv.app P₁.y ≫ g'.map (k.map b) := by
    simpa only [Functor.comp_map] using β.inv.naturality b
  have hA :
    f'.map EP ≫ α.hom.app P₁.x ≫ j.map (f.map a ≫ Q₁.iso.hom) ≫ β.inv.app Q₁.y =
      R.iso.hom ≫ g'.map FP ≫ g'.map (k.map b) := by
    calc
      f'.map EP ≫ α.hom.app P₁.x ≫ j.map (f.map a ≫ Q₁.iso.hom) ≫ β.inv.app Q₁.y =
          f'.map EP ≫ (α.hom.app P₁.x ≫ j.map (f.map a)) ≫ j.map Q₁.iso.hom ≫ β.inv.app Q₁.y := by
        rw [Functor.map_comp]
        simp [Category.assoc]
      _ = f'.map EP ≫ f'.map (i.map a) ≫ α.hom.app Q₁.x ≫ j.map Q₁.iso.hom ≫ β.inv.app Q₁.y := by
        rw [hαnat]
        simp [Category.assoc]
      _ = f'.map M.a ≫ f'.map EQ ≫ α.hom.app Q₁.x ≫ j.map Q₁.iso.hom ≫ β.inv.app Q₁.y := by
        rw [← Functor.map_comp_assoc, ha, Functor.map_comp]
        simp [Category.assoc]
      _ = f'.map M.a ≫ S.iso.hom ≫ g'.map FQ := by rw [hQ]
      _ = R.iso.hom ≫ g'.map M.b ≫ g'.map FQ := by
        rw [← Category.assoc, M.w]
        simp [Category.assoc]
      _ = R.iso.hom ≫ g'.map FP ≫ g'.map (k.map b) := by
        rw [← Functor.map_comp, ← Functor.map_comp, ← hb]
  have hB :
    f'.map EP ≫ α.hom.app P₁.x ≫ j.map (P₁.iso.hom ≫ g.map b) ≫ β.inv.app Q₁.y =
      R.iso.hom ≫ g'.map FP ≫ g'.map (k.map b) := by
    calc
      f'.map EP ≫ α.hom.app P₁.x ≫ j.map (P₁.iso.hom ≫ g.map b) ≫ β.inv.app Q₁.y =
          f'.map EP ≫ α.hom.app P₁.x ≫ j.map P₁.iso.hom ≫ j.map (g.map b) ≫ β.inv.app Q₁.y := by
        rw [Functor.map_comp]
        simp [Category.assoc]
      _ = (f'.map EP ≫ α.hom.app P₁.x ≫ j.map P₁.iso.hom ≫ β.inv.app P₁.y) ≫ g'.map (k.map b) := by
        rw [hβnat]
        simp [Category.assoc]
      _ = (R.iso.hom ≫ g'.map FP) ≫ g'.map (k.map b) := by rw [hP]
      _ = R.iso.hom ≫ g'.map FP ≫ g'.map (k.map b) := by simp [Category.assoc]
  exact
    (cancel_mono (β.inv.app Q₁.y)).mp
      ((cancel_epi (α.hom.app P₁.x)).mp ((cancel_epi (f'.map EP)).mp (hA.trans hB.symm)))

/-- Cancelling an epimorphism on the left and a monomorphism on the right. -/
private lemma cancel_epi_comp_mono {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X} {b : Y ⟶ Z}
    [Epi a] [Mono b] {x y : X ⟶ Y} : a ≫ x ≫ b = a ≫ y ≫ b ↔ x = y := by
  rw [cancel_epi, cancel_mono]

open Opposite _root_.CategoryTheory.Functor in
/-- Two morphisms of the 2-fibre product have the same image under `H` exactly when their two
components have the same images under `i` and `k`: `γ` and `δ` conjugate the components of `H Φ`
into the images of the components of `Φ`. -/
lemma H_map_eq_iff (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k) {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g}
    (Φ Φ' : P ⟶ Q) : H.map Φ = H.map Φ' ↔ i.map Φ.a = i.map Φ'.a ∧ k.map Φ.b = k.map Φ'.b := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ =>
    Hom.ext' (by rw [map_a_eq γ, map_a_eq γ, h₁]) (by rw [map_b_eq δ, map_b_eq δ, h₂])⟩
  · have h₁ := congrArg Hom.a h
    rw [map_a_eq γ, map_a_eq γ] at h₁
    exact cancel_epi_comp_mono.mp h₁
  · have h₁ := congrArg Hom.b h
    rw [map_b_eq δ, map_b_eq δ] at h₁
    exact cancel_epi_comp_mono.mp h₁

end

section

variable {𝒜 𝒮 : Type*} [Category 𝒜] [Category 𝒮] {p : 𝒜 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮} [p.IsFibered]
  [r.IsFibered]

open Opposite _root_.CategoryTheory.Functor in
/-- Base change of an isomorphism of a fibre is an isomorphism. -/
private lemma isIso_pullbackFiberHom_hom {W : 𝒞} {y y' : p.Fiber W} (e : y ≅ y') {Z : 𝒞}
    (b : Z ⟶ W) : IsIso (pullbackFiberHom e.hom b) := by
  rw [← pullbackFiberIso_hom]
  infer_instance

open Opposite _root_.CategoryTheory.Functor in
/-- Base change of the inverse of an isomorphism of a fibre is an isomorphism. -/
lemma isIso_pullbackFiberHom_inv {W : 𝒞} {y y' : p.Fiber W} (e : y ≅ y') {Z : 𝒞}
    (b : Z ⟶ W) : IsIso (pullbackFiberHom e.inv b) := by
  rw [← pullbackFiberIso_inv]
  infer_instance

open Opposite _root_.CategoryTheory.Functor in
/-- The underlying morphism of `𝒮` of a section of `Mor(F x, F y)` in the image of the map of
Stacks 042V: the image under `F` of the section, conjugated by the comparisons. -/
lemma fiberInclusion_morPresheafMap_app (hF : Functor.IsFibredOneMorphism p r F) {U : 𝒞}
    (x y : p.Fiber U) (X : (Over U)ᵒᵖ) (m : (morPresheaf p x y).obj X) :
    Fiber.fiberInclusion.map ((hF.morPresheafMap x y).app X m) =
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso x X.unop.hom).hom ≫
        F.map (Fiber.fiberInclusion.map m) ≫
        Fiber.fiberInclusion.map (hF.mapPullbackFiberIso y X.unop.hom).inv := by
  rw [Functor.IsFibredOneMorphism.morPresheafMap_app]
  simp

open Opposite _root_.CategoryTheory.Functor in
/-- The map of Stacks 042V is injective on sections exactly where `F` is: the two comparison
isomorphisms cancel. -/
lemma morPresheafMap_app_inj_iff (hF : Functor.IsFibredOneMorphism p r F) {U : 𝒞}
    (x y : p.Fiber U) (X : (Over U)ᵒᵖ) (m n : (morPresheaf p x y).obj X) :
    (hF.morPresheafMap x y).app X m = (hF.morPresheafMap x y).app X n ↔
      F.map (Fiber.fiberInclusion.map m) = F.map (Fiber.fiberInclusion.map n) := by
  refine ⟨fun h => ?_, fun h => Fiber.hom_ext ?_⟩
  · have h1 := congrArg Fiber.fiberInclusion.map h
    rw [fiberInclusion_morPresheafMap_app, fiberInclusion_morPresheafMap_app] at h1
    exact cancel_epi_comp_mono.mp h1
  · rw [fiberInclusion_morPresheafMap_app, fiberInclusion_morPresheafMap_app, h]

open Opposite _root_.CategoryTheory.Functor in
/-- A section of `Mor(F x, F y)` is the image of `m` under the map of Stacks 042V exactly when the
image of `m` under `F`, conjugated by the comparisons, is its underlying morphism. -/
private lemma morPresheafMap_app_eq_iff (hF : Functor.IsFibredOneMorphism p r F) {U : 𝒞}
    (x y : p.Fiber U) (X : (Over U)ᵒᵖ) (m : (morPresheaf p x y).obj X)
    (w :
      (morPresheaf r ((fiberFunctorOfCompEq hF.comp_eq U).obj x)
            ((fiberFunctorOfCompEq hF.comp_eq U).obj y)).obj
        X) :
    (hF.morPresheafMap x y).app X m = w ↔
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso x X.unop.hom).hom ≫
          F.map (Fiber.fiberInclusion.map m) ≫
          Fiber.fiberInclusion.map (hF.mapPullbackFiberIso y X.unop.hom).inv =
        Fiber.fiberInclusion.map w := by
  rw [← fiberInclusion_morPresheafMap_app]
  exact ⟨fun h => by rw [h], fun h => Fiber.hom_ext h⟩

end

section

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'} {i : 𝒳 ⥤ 𝒳'} {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'}
  {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'} [p𝒳.IsFibered]
  [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered] [p𝒵'.IsFibered]
  [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]
  (hf₁ : Functor.IsFibredOneMorphism p𝒳 p𝒴 f) (hg₁ : Functor.IsFibredOneMorphism p𝒵 p𝒴 g)

open Opposite _root_.CategoryTheory.Functor in
/-- The `𝒳`-component of a section of the morphism presheaf of the 2-fibre product, transported to
the chosen pullbacks taken in `𝒳`; the first component of
`CategoryTheory.TwoFibreProductOver.morSectionEquiv`. -/
noncomputable def morFstSection {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (X : (Over U)ᵒᵖ) (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    (morPresheaf p𝒳 (fibFst P) (fibFst Q)).obj X :=
  (pullbackFiberFstIso hf₁ hg₁ P X.unop.hom).homCongr (pullbackFiberFstIso hf₁ hg₁ Q X.unop.hom)
    (fibFstHom s)

open Opposite _root_.CategoryTheory.Functor in
/-- The `𝒵`-component of a section of the morphism presheaf of the 2-fibre product, transported to
the chosen pullbacks taken in `𝒵`. -/
noncomputable def morSndSection {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (X : (Over U)ᵒᵖ) (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    (morPresheaf p𝒵 (fibSnd P) (fibSnd Q)).obj X :=
  (pullbackFiberSndIso hf₁ hg₁ P X.unop.hom).homCongr (pullbackFiberSndIso hf₁ hg₁ Q X.unop.hom)
    (fibSndHom s)

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- The underlying morphism of `𝒳` of the `𝒳`-component of a section. -/
private lemma fiberInclusion_morFstSection {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (X : (Over U)ᵒᵖ) (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    Fiber.fiberInclusion.map (morFstSection hf₁ hg₁ P Q X s) =
      Fiber.fiberInclusion.map (pullbackFiberFstIso hf₁ hg₁ P X.unop.hom).inv ≫
        (Fiber.fiberInclusion.map s).a ≫
        Fiber.fiberInclusion.map (pullbackFiberFstIso hf₁ hg₁ Q X.unop.hom).hom := by
  rw [morFstSection]
  simp

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- The underlying morphism of `𝒵` of the `𝒵`-component of a section. -/
private lemma fiberInclusion_morSndSection {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (X : (Over U)ᵒᵖ) (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    Fiber.fiberInclusion.map (morSndSection hf₁ hg₁ P Q X s) =
      Fiber.fiberInclusion.map (pullbackFiberSndIso hf₁ hg₁ P X.unop.hom).inv ≫
        (Fiber.fiberInclusion.map s).b ≫
        Fiber.fiberInclusion.map (pullbackFiberSndIso hf₁ hg₁ Q X.unop.hom).hom := by
  rw [morSndSection]
  simp

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- A section of the morphism presheaf of the 2-fibre product is determined by its two
components. -/
lemma section_ext {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (X : (Over U)ᵒᵖ)
    (s t : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X)
    (ha : morFstSection hf₁ hg₁ P Q X s = morFstSection hf₁ hg₁ P Q X t)
    (hb : morSndSection hf₁ hg₁ P Q X s = morSndSection hf₁ hg₁ P Q X t) : s = t := by
  have ha' := congrArg Fiber.fiberInclusion.map ha
  have hb' := congrArg Fiber.fiberInclusion.map hb
  rw [fiberInclusion_morFstSection, fiberInclusion_morFstSection] at ha'
  rw [fiberInclusion_morSndSection, fiberInclusion_morSndSection] at hb'
  exact Fiber.hom_ext (Hom.ext' (cancel_epi_comp_mono.mp ha') (cancel_epi_comp_mono.mp hb'))

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- The map of Stacks 042V along `i`, evaluated at the `𝒳`-component of a section, is injective
exactly where `i` is on the `𝒳`-components. -/
lemma morPresheafMap_morFstSection_inj_iff (hi₁ : Functor.IsFibredOneMorphism p𝒳 p𝒳' i)
    {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (X : (Over U)ᵒᵖ)
    (s t : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    (hi₁.morPresheafMap (fibFst P) (fibFst Q)).app X (morFstSection hf₁ hg₁ P Q X s) =
        (hi₁.morPresheafMap (fibFst P) (fibFst Q)).app X (morFstSection hf₁ hg₁ P Q X t) ↔
      i.map (Fiber.fiberInclusion.map s).a = i.map (Fiber.fiberInclusion.map t).a := by
  rw [morPresheafMap_app_inj_iff, fiberInclusion_morFstSection, fiberInclusion_morFstSection]
  simp only [Functor.map_comp]
  exact cancel_epi_comp_mono

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- The map of Stacks 042V along `k`, evaluated at the `𝒵`-component of a section, is injective
exactly where `k` is on the `𝒵`-components. -/
lemma morPresheafMap_morSndSection_inj_iff (hk₁ : Functor.IsFibredOneMorphism p𝒵 p𝒵' k)
    {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (X : (Over U)ᵒᵖ)
    (s t : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)).app X (morSndSection hf₁ hg₁ P Q X s) =
        (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)).app X (morSndSection hf₁ hg₁ P Q X t) ↔
      k.map (Fiber.fiberInclusion.map s).b = k.map (Fiber.fiberInclusion.map t).b := by
  rw [morPresheafMap_app_inj_iff, fiberInclusion_morSndSection, fiberInclusion_morSndSection]
  simp only [Functor.map_comp]
  exact cancel_epi_comp_mono

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- Taking the `𝒳`-component of a section commutes with restriction. -/
lemma morFstSection_naturality {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    {W : Over U} {X : (Over U)ᵒᵖ} (hw : W ⟶ X.unop)
    (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    morFstSection hf₁ hg₁ P Q (op W)
        ((morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).map hw.op s) =
      (morPresheaf p𝒳 (fibFst P) (fibFst Q)).map hw.op (morFstSection hf₁ hg₁ P Q X s) := by
  rw [morFstSection, morFstSection]
  exact morSectionEquiv_naturality_fst hf₁ hg₁ P Q hw s

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- Taking the `𝒵`-component of a section commutes with restriction. -/
lemma morSndSection_naturality {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    {W : Over U} {X : (Over U)ᵒᵖ} (hw : W ⟶ X.unop)
    (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    morSndSection hf₁ hg₁ P Q (op W)
        ((morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).map hw.op s) =
      (morPresheaf p𝒵 (fibSnd P) (fibSnd Q)).map hw.op (morSndSection hf₁ hg₁ P Q X s) := by
  rw [morSndSection, morSndSection]
  exact morSectionEquiv_naturality_snd hf₁ hg₁ P Q hw s

end

end CategoryTheory.TwoFibreProductOver

end
