module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationLift
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp
public import StacksFrontier.CategoryTheory.Sites.Stack.FullyFaithfulOfLocalEssImage
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EquivalenceOverMorSheafTarget
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# The moduli square of a base-changed chart is cartesian (proof of Stacks 0DUQ)

Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks, `x : 𝒮_U ⟶ 𝒳` a chart and
`x' : 𝒮_W ⟶ 𝒳'` its base change, with `f : W ⟶ U` the morphism of the site the projection
`𝒮_W ⟶ 𝒮_U` names. Let `f_𝒳 : 𝒳 ⟶ M` and `f_𝒳' : 𝒳' ⟶ M'` be 1-morphisms to the categories
attached to objects `M`, `M'` of the site, with `f_𝒳 ∘ x` and `f_𝒳' ∘ x'` attached to morphisms
`q : U ⟶ M` and `q' : W ⟶ M'` of the site, and let `g : M' ⟶ M` make the square
`f_𝒳' ; g = h ; f_𝒳` commute. Suppose that `W = M' ×_M U` (the second conclusion of Stacks 0DT9)
and that `h` is fully faithful on the arrows between objects of the chart with one image in `M'`.
Then the square

    𝒳' ---h---> 𝒳
    |           |
    v           v
    M' ---g---> M

is a 2-fibre product: this is the last sentence of the proof of Stacks 0DUQ.

This file proves the essential surjectivity half: the comparison `𝒳' ⟶ M' ×_M 𝒳` is locally
essentially surjective on fibres. An object `(m', a, ·)` of `M' ×_M 𝒳` over `V` is, after
restriction to a covering sieve, of the form `(m', x(u), ·)`; the pair `(u, m')` is a point of
`M' ×_M U = W`, and the image of `x'` at that point is a lift.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.locallyEssSurjOnFibers_cartesianComparison`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U W : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)
  {M M' : BigFppfOver B S hS} (gM : M' ⟶ M)
  (f : 𝒳.val ⟶ fibredCategory B S hS (yoneda.obj M))
  (f' : 𝒳'.val ⟶ fibredCategory B S hS (yoneda.obj M'))
  (hcomm : f' ≫ (associatedMap B S hS (yoneda.map gM)).1 = h.hom ≫ f)

/-- The 2-commutative square of the moduli maps. -/
noncomputable abbrev moduliSquare :
    Bicategory.TwoCommSq (associatedMap B S hS (yoneda.map gM)).1 f :=
  ⟨𝒳'.val, f', h.hom, eqToIso hcomm⟩

/-- The comparison 1-morphism `𝒳' ⟶ M' ×_M 𝒳` into the canonical 2-fibre product. -/
noncomputable abbrev cartesianComparison :
    𝒳'.val ⟶ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS (yoneda.map gM)).1 f).pt :=
  CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
    (moduliSquare h gM f f' hcomm)

/-- An object of the category attached to a presheaf of sets is the pair of its base and the
element it names. -/
theorem fibredCategory_obj_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : (fibredCategory B S hS F).val.obj) :
    X = ⟨X.base, Discrete.mk (PresheafOfCategories.elementOf F (X := X) rfl)⟩ := rfl

/-- A morphism of the category attached to a presheaf of sets lying over `k` identifies the element
named by its source with the restriction of the element named by its target. -/
theorem fibredCategory_elementOf_eq_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X Y : (fibredCategory B S hS F).val.obj} {V V' : BigFppfOver B S hS} (hX : X.base = V)
    (hY : Y.base = V') (k : V ⟶ V') (φ : X ⟶ Y)
    (hφ : (fibredCategory B S hS F).val.p.IsHomLift k φ) :
    PresheafOfCategories.elementOf F hX = F.map k.op (PresheafOfCategories.elementOf F hY) :=
  PresheafOfCategories.elementOf_eq_map (P := F) hX hY k φ hφ

/-- The element named by an object of the category attached to a presheaf of sets which is the
canonical object of an element is that element. -/
theorem fibredCategory_elementOf_eq_of_obj_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : (fibredCategory B S hS F).val.obj} {V : BigFppfOver B S hS} (a : F.obj (op V))
    (hX : X = ⟨V, Discrete.mk a⟩) (h : X.base = V) :
    PresheafOfCategories.elementOf F h = a := by
  subst hX
  rfl

/-- The section of the presheaf represented by `T` named by an object of the slice over `T` is its
structure morphism, read over the prescribed base. -/
theorem sectionOfObj_sliceElementsEquivalenceOver' {C : Type*} [Category C] {T : C}
    (o : Over T) {V : C} (h : o.left = V) :
    PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver T) o h =
      eqToHom h.symm ≫ o.hom := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- Precomposing a lift with an `eqToHom` in the source and in the base keeps it a lift. -/
theorem isHomLift_eqToHom_comp_eqToHom {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R R' T : 𝒞} (e₁ : R' = R) (k : R ⟶ T) {a a' b : 𝒜} (e₂ : a' = a) (φ : a ⟶ b)
    (h : p.IsHomLift k φ) : p.IsHomLift (eqToHom e₁ ≫ k) (eqToHom e₂ ≫ φ) := by
  subst e₁ e₂
  simpa using h

/-- Precomposing the base of a lift with an `eqToHom` keeps it a lift. -/
theorem isHomLift_eqToHom_comp {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R R' T : 𝒞} (e : R' = R) (k : R ⟶ T) {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift k φ) :
    p.IsHomLift (eqToHom e ≫ k) φ := by
  subst e
  simpa using h

/-- A lift over `k` followed by a morphism over an identity lies over `k`. -/
theorem isHomLift_comp_vertical_right {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R T : 𝒞} (k : R ⟶ T) {a b c : 𝒜} (l : a ⟶ b) (f₁ : b ⟶ c)
    (hl : p.IsHomLift k l) (h₁ : p.IsHomLift (𝟙 T) f₁) : p.IsHomLift k (l ≫ f₁) := by
  have := h₁
  have := hl
  infer_instance

/-- **A morphism of a 2-fibre product over a category fibred in setoids** is a pair of morphisms
over one base morphism: the compatibility square holds automatically, both of its composites lying
over that base morphism. -/
noncomputable def twoFibreProductHomOfSetoids {𝒞 𝒳₁ 𝒴₁ 𝒮₁ : Type*} [Category 𝒞] [Category 𝒳₁]
    [Category 𝒴₁] [Category 𝒮₁] {p𝒳 : 𝒳₁ ⥤ 𝒞} {p𝒴 : 𝒴₁ ⥤ 𝒞} {p𝒮 : 𝒮₁ ⥤ 𝒞}
    [p𝒮.IsFiberedInSetoids] {F : 𝒳₁ ⥤ 𝒮₁} {G : 𝒴₁ ⥤ 𝒮₁} (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮 = p𝒴) {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (hbase : P.base ⟶ Q.base)
    (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y) (ha : p𝒳.IsHomLift hbase a) (hb : p𝒴.IsHomLift hbase b) :
    P ⟶ Q where
  hbase := hbase
  a := a
  b := b
  ha := ha
  hb := hb
  w := by
    have h₁ : p𝒮.IsHomLift hbase (F.map a) := Functor.isHomLift_map_of_comp_eq hF hbase a
    have h₂ : p𝒮.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
    have h₃ : p𝒮.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    have h₄ : p𝒮.IsHomLift hbase (G.map b) := Functor.isHomLift_map_of_comp_eq hG hbase b
    have hL : p𝒮.IsHomLift hbase (F.map a ≫ Q.iso.hom) := inferInstance
    have hR : p𝒮.IsHomLift hbase (P.iso.hom ≫ G.map b) := inferInstance
    exact Functor.hom_unique_of_isFiberedInSetoids (q := p𝒮) hbase _ _ hL hR

/-- The underlying morphism of the image of a morphism of fibres. -/
theorem fiberFunctorOfCompEq_map_val {𝒞 𝒜 𝒮₁ : Type*} [Category 𝒞] [Category 𝒜] [Category 𝒮₁]
    {p : 𝒜 ⥤ 𝒞} {r : 𝒮₁ ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮₁} (hF : F ⋙ r = p) (U : 𝒞) {a b : p.Fiber U}
    (φ : a ⟶ b) : ((Functor.fiberFunctorOfCompEq hF U).map φ).1 = F.map φ.1 :=
  rfl

/-- A morphism of fibres is in the image of a functor of fibres as soon as its conjugate by two
vertical isomorphisms is the image of a vertical morphism. -/
theorem exists_fiber_preimage_of_conj {𝒞 𝒜 𝒮₁ : Type*} [Category 𝒞] [Category 𝒜]
    [Category 𝒮₁] {p : 𝒜 ⥤ 𝒞} {r : 𝒮₁ ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮₁} (hF : F ⋙ r = p) {U : 𝒞}
    {a b : p.Fiber U} {xa xb : 𝒜} (Ea : xa ≅ a.1) (Eb : xb ≅ b.1)
    (hEa : p.IsHomLift (𝟙 U) Ea.hom) (hEb : p.IsHomLift (𝟙 U) Eb.hom)
    (Φ : (Functor.fiberFunctorOfCompEq hF U).obj a ⟶ (Functor.fiberFunctorOfCompEq hF U).obj b)
    (ψ : xa ⟶ xb) (hψ : p.IsHomLift (𝟙 U) ψ) (hFψ : F.map ψ = F.map Ea.hom ≫ Φ.1 ≫ F.map Eb.inv) :
    ∃ m : a ⟶ b, (Functor.fiberFunctorOfCompEq hF U).map m = Φ := by
  have hEa' : p.IsHomLift (𝟙 U) Ea.inv := IsHomLift.lift_id_inv p U Ea
  refine ⟨⟨Ea.inv ≫ ψ ≫ Eb.hom, inferInstance⟩, Functor.Fiber.hom_ext ?_⟩
  change F.map (Ea.inv ≫ ψ ≫ Eb.hom) = Φ.1
  rw [F.map_comp, F.map_comp, hFψ]
  simp [← F.map_comp_assoc, ← F.map_comp]

/-- A morphism of fibres is in the image of a functor of fibres as soon as every vertical morphism
between the images of two objects isomorphic to its source and target is the image of a vertical
morphism. -/
theorem exists_fiber_preimage_of_conj' {𝒞 𝒜 𝒮₁ : Type*} [Category 𝒞] [Category 𝒜]
    [Category 𝒮₁] {p : 𝒜 ⥤ 𝒞} {r : 𝒮₁ ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮₁} (hF : F ⋙ r = p) {U : 𝒞}
    {a b : p.Fiber U} {xa xb : 𝒜} (Ea : xa ≅ a.1) (Eb : xb ≅ b.1)
    (hEa : p.IsHomLift (𝟙 U) Ea.hom) (hEb : p.IsHomLift (𝟙 U) Eb.hom)
    (Φ : (Functor.fiberFunctorOfCompEq hF U).obj a ⟶ (Functor.fiberFunctorOfCompEq hF U).obj b)
    (hpre : ∀ Ψ : F.obj xa ⟶ F.obj xb, r.IsHomLift (𝟙 U) Ψ →
      ∃ ψ : xa ⟶ xb, p.IsHomLift (𝟙 U) ψ ∧ F.map ψ = Ψ) :
    ∃ m : a ⟶ b, (Functor.fiberFunctorOfCompEq hF U).map m = Φ := by
  have hEb' : p.IsHomLift (𝟙 U) Eb.inv := IsHomLift.lift_id_inv p U Eb
  have h₁ : r.IsHomLift (𝟙 U) (F.map Ea.hom) := Functor.isHomLift_map_of_comp_eq hF (𝟙 U) Ea.hom
  have h₂ : r.IsHomLift (𝟙 U) (F.map Eb.inv) := Functor.isHomLift_map_of_comp_eq hF (𝟙 U) Eb.inv
  have h₃ : r.IsHomLift (𝟙 U) Φ.1 := Φ.2
  obtain ⟨ψ, hψ, hFψ⟩ := hpre (F.map Ea.hom ≫ Φ.1 ≫ F.map Eb.inv) inferInstance
  exact exists_fiber_preimage_of_conj hF Ea Eb hEa hEb Φ ψ hψ hFψ

/-- If a functor sends `ψ : X ⟶ X'` to the conjugate of `Φ` by the images of isomorphisms
`e₁ : X ≅ Y` and `e₂ : X' ≅ Y'`, then it sends the conjugate `e₁.inv ≫ ψ ≫ e₂.hom` to `Φ`. -/
theorem functor_map_conj {A B : Type*} [Category A] [Category B] (L : A ⥤ B) {X Y X' Y' : A}
    (e₁ : X ≅ Y) (e₂ : X' ≅ Y') (Φ : L.obj Y ⟶ L.obj Y') (ψ : X ⟶ X')
    (hψ : L.map ψ = L.map e₁.hom ≫ Φ ≫ L.map e₂.inv) : L.map (e₁.inv ≫ ψ ≫ e₂.hom) = Φ := by
  rw [L.map_comp, L.map_comp, hψ]
  simp [← L.map_comp_assoc, ← L.map_comp]

/-- A composite of three morphisms over identities followed by one over `k` lies over `k`. -/
theorem isHomLift_comp_vertical₃ {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R T : 𝒞} (k : R ⟶ T) {a b c d e : 𝒜} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (f₃ : c ⟶ d) (l : d ⟶ e)
    (h₁ : p.IsHomLift (𝟙 R) f₁) (h₂ : p.IsHomLift (𝟙 R) f₂) (h₃ : p.IsHomLift (𝟙 R) f₃)
    (hl : p.IsHomLift k l) : p.IsHomLift k (f₁ ≫ f₂ ≫ f₃ ≫ l) := by
  have := h₁
  have := h₂
  have := h₃
  have := hl
  infer_instance

/-- A morphism over an identity followed by one over `k` lies over `k`. -/
theorem isHomLift_comp_vertical₁ {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R T : 𝒞} (k : R ⟶ T) {a b c : 𝒜} (f₁ : a ⟶ b) (l : b ⟶ c)
    (h₁ : p.IsHomLift (𝟙 R) f₁) (hl : p.IsHomLift k l) : p.IsHomLift k (f₁ ≫ l) := by
  have := h₁
  have := hl
  infer_instance

variable {gM f f' hcomm} in
/-- **The comparison `𝒳' ⟶ M' ×_M 𝒳` is locally essentially surjective on fibres.** -/
theorem locallyEssSurjOnFibers_cartesianComparison (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK))
    (q : U ⟶ M) (q' : W ⟶ M')
    (hq : BasedFunctor.comp x.hom.hom f.hom = BasedFunctor.comp (sliceElementsComparison B S hS U)
      (associatedMap B S hS (yoneda.map q)).1.hom)
    (hq' : BasedFunctor.comp (chart' h x eK).hom f'.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS W)
        (associatedMap B S hS (yoneda.map q')).1.hom)
    (hH2 : IsPullback (yoneda.map fU) (yoneda.map q') (yoneda.map q) (yoneda.map gM))
    (hx : Functor.LocallyEssSurjOnFibers 𝒳.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p x.hom) (BigFppfOver.topology B S hS)) :
    Functor.LocallyEssSurjOnFibers
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS (yoneda.map gM)).1 f).pt.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p (cartesianComparison h gM f f' hcomm))
      (BigFppfOver.topology B S hS) := by
  let P := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (associatedMap B S hS (yoneda.map gM)).1 f
  have hPf : P.pt.val.p.IsFibered := P.pt.isFiberedInGroupoids.isFibered
  have h𝒳f : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  intro V₀ ⟨y, hy⟩
  obtain ⟨b, yx, yy, hxb, hyb, φ, hφ⟩ := y
  change b = V₀ at hy
  subst hy
  change yx.base = b at hxb
  subst hxb
  obtain ⟨R, hR, hRl⟩ := hx yx.base ⟨yy, hyb⟩
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨⟨z₀, hz₀⟩, ⟨e⟩⟩ := hRl k hk
  change z₀.left = V at hz₀
  subst hz₀
  let gS := (associatedMap B S hS (yoneda.map gM)).1
  -- the element of `M` named by `f yy` is `m'₀ ≫ g`
  have hfyy : (f.hom.obj yy).base = yx.base := (Functor.congr_obj f.hom.w yy).trans hyb
  have hgyx : gS.hom.obj yx = ⟨yx.base, Discrete.mk (yx.fiber.as ≫ gM)⟩ :=
    associatedMap_obj B S hS (yoneda.map gM) yx
  have h₁ : yx.fiber.as ≫ gM =
      PresheafOfCategories.elementOf (yoneda.obj M) (X := f.hom.obj yy) hfyy := by
    have := fibredCategory_elementOf_eq_map (F := yoneda.obj M) (X := gS.hom.obj yx)
      (Y := f.hom.obj yy) (congrArg (fun X => X.base) hgyx) hfyy (𝟙 yx.base) φ.hom hφ
    rw [fibredCategory_elementOf_eq_of_obj_eq _ hgyx] at this
    simpa using this
  -- the element named by `f (x z₀)` is `z₀ ≫ q`
  have hfxz : f.hom.obj (x.hom.hom.obj z₀) = ⟨z₀.left, Discrete.mk (z₀.hom ≫ q)⟩ := by
    have := congrArg (fun F => F.obj z₀) hq
    exact this.trans (associatedMap_obj B S hS (yoneda.map q) _)
  -- the morphism `x z₀ ⟶ yy` over `k`
  let χ := e.hom.1 ≫ Functor.IsPreFibered.pullbackMap hyb k
  have hχ : 𝒳.val.val.p.IsHomLift k χ :=
    isHomLift_comp_vertical₁ _ k e.hom.1 _ e.hom.2 inferInstance
  have h₂ : z₀.hom ≫ q = k ≫ yx.fiber.as ≫ gM := by
    have := fibredCategory_elementOf_eq_map (F := yoneda.obj M) (X := f.hom.obj (x.hom.hom.obj z₀))
      (Y := f.hom.obj yy) (congrArg (fun X => X.base) hfxz) hfyy k (f.hom.map χ)
      (Functor.isHomLift_map_of_comp_eq f.hom.w k χ)
    rw [fibredCategory_elementOf_eq_of_obj_eq _ hfxz, ← h₁] at this
    exact this
  -- the point of `W = M' ×_M U`
  have hpbV := hH2.map ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (op z₀.left))
  obtain ⟨w, hw₁, hw₂⟩ := Types.exists_of_isPullback hpbV z₀.hom (k ≫ yx.fiber.as) h₂
  change w ≫ fU = z₀.hom at hw₁
  change w ≫ q' = k ≫ yx.fiber.as at hw₂
  -- the lift `x'(w)`
  let wo : Over W := Over.mk w
  let K := eK.hom.functor
  let a' := (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj wo
  have hwo : 𝒳'.val.val.p.obj a' = z₀.left :=
    Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (chart' h x eK)) wo
  -- its image in `M'`
  have hf'a : f'.hom.obj a' = ⟨z₀.left, Discrete.mk (k ≫ yx.fiber.as)⟩ := by
    have := congrArg (fun F => F.obj wo) hq'
    refine this.trans ((associatedMap_obj B S hS (yoneda.map q') _).trans ?_)
    change (⟨z₀.left, Discrete.mk (w ≫ q')⟩ : (fibredCategory B S hS (yoneda.obj M')).val.obj) = _
    rw [hw₂]
  let ψa : f'.hom.obj a' ⟶ yx := eqToHom hf'a ≫ PresheafOfCategories.homMk k yx.fiber.as
  have hψa : (fibredCategory B S hS (yoneda.obj M')).val.p.IsHomLift (eqToHom hwo ≫ k) ψa :=
    isHomLift_eqToHom_comp_eqToHom _ hwo k hf'a _
      (IsHomLift.map (fibredCategory B S hS (yoneda.obj M')).val.p
        (PresheafOfCategories.homMk (P := yoneda.obj M') k yx.fiber.as))
  -- the vertical isomorphism `f(wo) ≅ z₀` of `𝒮_U`
  have hsec : PresheafOfCategories.sectionOfObj
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      ((CatFiberedInGroupoids.homFunctor (chartMap h x eK)).obj wo)
      ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (chartMap h x eK)) wo).trans
        rfl) =
      PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver U)
        z₀ rfl := by
    refine (representingMap_app_sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK) wo rfl).symm.trans ?_
    rw [← hfU]
    change (PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver W)
      wo rfl) ≫ fU = _
    rw [sectionOfObj_sliceElementsEquivalenceOver']
    refine Eq.trans ?_ (sectionOfObj_sliceElementsEquivalenceOver' z₀ rfl).symm
    simp only [eqToHom_refl, Category.id_comp]
    exact hw₁
  let θ := PresheafOfCategories.fiberIsoOfSectionOfObj_eq
    (PresheafOfCategories.sliceElementsEquivalenceOver U) _ _ hsec
  -- the `𝒳`-component of the lift
  have hKb : (K.obj wo).base = z₀.left := comparison_base h x eK wo
  have hK₁ : 𝒳.val.val.p.IsHomLift (𝟙 z₀.left) (K.obj wo).iso.hom := by
    rw [← hKb]; exact (K.obj wo).vertical
  have hK₂ : 𝒳.val.val.p.IsHomLift (𝟙 z₀.left) (x.hom.hom.map θ.hom.1) := by
    have : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift (𝟙 z₀.left) θ.hom.1 := θ.hom.2
    exact Functor.isHomLift_map_of_comp_eq x.hom.hom.w (𝟙 z₀.left) θ.hom.1
  let ψb : h.hom.hom.obj a' ⟶ yy := (K.obj wo).iso.hom ≫ x.hom.hom.map θ.hom.1 ≫ e.hom.1 ≫
    Functor.IsPreFibered.pullbackMap hyb k
  have hψb₀ : 𝒳.val.val.p.IsHomLift k ψb :=
    isHomLift_comp_vertical₃ _ k _ _ _ _ hK₁ hK₂ e.hom.2 inferInstance
  have hψb : 𝒳.val.val.p.IsHomLift (eqToHom hwo ≫ k) ψb :=
    isHomLift_eqToHom_comp _ hwo k ψb hψb₀
  have hMset : (fibredCategory B S hS (yoneda.obj M)).val.p.IsFiberedInSetoids :=
    PresheafOfCategories.isFiberedInSetoids_discreteProjection (yoneda.obj M)
  let La' := (cartesianComparison h gM f f' hcomm).hom.toFunctor.obj a'
  let y₀ : P.pt.val.obj := ⟨yx.base, yx, yy, rfl, hyb, φ, hφ⟩
  let ψ : La' ⟶ y₀ :=
    twoFibreProductHomOfSetoids (p𝒮 := (fibredCategory B S hS (yoneda.obj M)).val.p)
      gS.hom.w f.hom.w (eqToHom hwo ≫ k) ψa ψb hψa hψb
  have hψ : P.pt.val.p.IsHomLift k ψ :=
    IsHomLift.of_fac' _ k ψ hwo rfl
      (by change eqToHom hwo ≫ k = eqToHom hwo ≫ k ≫ 𝟙 yx.base; simp)
  have hcart : P.pt.val.p.IsStronglyCartesian k ψ :=
    P.pt.isFiberedInGroupoids.isStronglyCartesian_homLift k ψ
  exact ⟨⟨a', hwo⟩, ⟨Functor.fiberIsoPullbackFiber P.pt.val.p ⟨y₀, rfl⟩ k
    ⟨La', (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p
      (cartesianComparison h gM f f' hcomm)) a').trans hwo⟩ ψ hcart⟩⟩

variable {gM f f' hcomm} in
/-- **On objects of the chart, the comparison `𝒳' ⟶ M' ×_M 𝒳` is full on vertical morphisms.** -/
theorem exists_preimage_cartesianComparison (q' : W ⟶ M')
    (hq' : BasedFunctor.comp (chart' h x eK).hom f'.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS W)
        (associatedMap B S hS (yoneda.map q')).1.hom)
    (hH3 : ∀ (V : BigFppfOver B S hS) (w₁ w₂ : V ⟶ W), w₁ ≫ q' = w₂ ≫ q' →
      ∀ α : (CatFiberedInGroupoids.homFunctor h.hom).obj
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁)) ⟶
        (CatFiberedInGroupoids.homFunctor h.hom).obj
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂)),
        𝒳.val.val.p.IsHomLift (𝟙 V) α →
      ∃ ψ : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁) ⟶
          (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂),
        𝒳'.val.val.p.IsHomLift (𝟙 V) ψ ∧ (CatFiberedInGroupoids.homFunctor h.hom).map ψ = α)
    {V : BigFppfOver B S hS} (w₁ w₂ : V ⟶ W)
    (Φ : (CatFiberedInGroupoids.homFunctor (cartesianComparison h gM f f' hcomm)).obj
        ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁)) ⟶
      (CatFiberedInGroupoids.homFunctor (cartesianComparison h gM f f' hcomm)).obj
        ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂)))
    (hΦ : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS (yoneda.map gM)).1 f).pt.val.p.IsHomLift (𝟙 V) Φ) :
    ∃ ψ : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁) ⟶
        (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂),
      𝒳'.val.val.p.IsHomLift (𝟙 V) ψ ∧
        (CatFiberedInGroupoids.homFunctor (cartesianComparison h gM f f' hcomm)).map ψ = Φ := by
  have hM'set : (fibredCategory B S hS (yoneda.obj M')).val.p.IsFiberedInSetoids :=
    PresheafOfCategories.isFiberedInSetoids_discreteProjection (yoneda.obj M')
  let xa := (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁)
  let xb := (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂)
  have hfa : f'.hom.obj xa = ⟨V, Discrete.mk (w₁ ≫ q')⟩ :=
    (congrArg (fun F => F.obj (Over.mk w₁)) hq').trans
      (associatedMap_obj B S hS (yoneda.map q') _)
  have hfb : f'.hom.obj xb = ⟨V, Discrete.mk (w₂ ≫ q')⟩ :=
    (congrArg (fun F => F.obj (Over.mk w₂)) hq').trans
      (associatedMap_obj B S hS (yoneda.map q') _)
  have hΦa : (fibredCategory B S hS (yoneda.obj M')).val.p.IsHomLift (𝟙 V) Φ.a :=
    isHomLift_a Φ (𝟙 V) (hφ := hΦ)
  have hsec : w₁ ≫ q' = w₂ ≫ q' := by
    have := fibredCategory_elementOf_eq_map (F := yoneda.obj M') (X := f'.hom.obj xa)
      (Y := f'.hom.obj xb) (congrArg (fun X => X.base) hfa) (congrArg (fun X => X.base) hfb)
      (𝟙 V) Φ.a hΦa
    rw [fibredCategory_elementOf_eq_of_obj_eq _ hfa, fibredCategory_elementOf_eq_of_obj_eq _ hfb]
      at this
    simpa using this
  have hΦb : 𝒳.val.val.p.IsHomLift (𝟙 V) Φ.b := isHomLift_b Φ (𝟙 V) (hφ := hΦ)
  obtain ⟨ψ, hψv, hψh⟩ := hH3 V w₁ w₂ hsec Φ.b hΦb
  refine ⟨ψ, hψv, ?_⟩
  apply TwoFibreProductOver.Hom.ext'
  · have := hψv
    exact Functor.hom_unique_of_isFiberedInSetoids
      (q := (fibredCategory B S hS (yoneda.obj M')).val.p)
      (𝟙 V) _ _ (Functor.isHomLift_map_of_comp_eq f'.hom.w (𝟙 V) ψ) hΦa
  · exact hψh

variable {gM f f' hcomm} in
/-- **The comparison `𝒳' ⟶ M' ×_M 𝒳` is full**, as soon as `h` is fully faithful on the arrows
between objects of the chart with one image in `M'`. -/
theorem full_cartesianComparison (q' : W ⟶ M')
    (hq' : BasedFunctor.comp (chart' h x eK).hom f'.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS W)
        (associatedMap B S hS (yoneda.map q')).1.hom)
    (hx' : Functor.LocallyEssSurjOnFibers 𝒳'.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p (chart' h x eK)) (BigFppfOver.topology B S hS))
    (hhf : (CatFiberedInGroupoids.homFunctor h.hom).Faithful)
    (hH3 : ∀ (V : BigFppfOver B S hS) (w₁ w₂ : V ⟶ W), w₁ ≫ q' = w₂ ≫ q' →
      ∀ α : (CatFiberedInGroupoids.homFunctor h.hom).obj
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁)) ⟶
        (CatFiberedInGroupoids.homFunctor h.hom).obj
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂)),
        𝒳.val.val.p.IsHomLift (𝟙 V) α →
      ∃ ψ : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁) ⟶
          (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂),
        𝒳'.val.val.p.IsHomLift (𝟙 V) ψ ∧ (CatFiberedInGroupoids.homFunctor h.hom).map ψ = α) :
    (CatFiberedInGroupoids.homFunctor (cartesianComparison h gM f f' hcomm)).Full := by
  let P := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (associatedMap B S hS (yoneda.map gM)).1 f
  let L := CatFiberedInGroupoids.homFunctor (cartesianComparison h gM f f' hcomm)
  have hPg : P.pt.val.p.IsFiberedInGroupoids := P.pt.isFiberedInGroupoids
  have hPf : P.pt.val.p.IsFibered := hPg.isFibered
  have h𝒳'f : 𝒳'.val.val.p.IsFibered := 𝒳'.val.isFiberedInGroupoids.isFibered
  have hF : 𝒳'.val.val.p.IsFibredOneMorphism P.pt.val.p L :=
    Functor.IsFibredOneMorphism.of_isFiberedInGroupoids hPg
      (CatFiberedInGroupoids.homFunctor_comp_p _)
  obtain ⟨-, ⟨hst', -⟩, -⟩ := 𝒳'.property
  obtain ⟨-, ⟨hstP, -⟩, -⟩ := isAlgebraicStack_twoFibreProductSquare.{u, w} B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj M') (isAlgebraicSpace_yoneda B S hS M'))
    (𝒵 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj M) (isAlgebraicSpace_yoneda B S hS M))
    (Bicategory.InducedBicategory.mkHom (associatedMap B S hS (yoneda.map gM)).1)
    (Bicategory.InducedBicategory.mkHom f)
  have hLf : L.Faithful := ⟨fun {X Y} φ₁ φ₂ hφ => hhf.map_injective
    (congrArg TwoFibreProductOver.Hom.b hφ)⟩
  have hM'set : (fibredCategory B S hS (yoneda.obj M')).val.p.IsFiberedInSetoids :=
    PresheafOfCategories.isFiberedInSetoids_discreteProjection (yoneda.obj M')
  refine (Functor.fullyFaithful_of_locallyBijective_of_isMorSheaf hF
    𝒳'.val.isFiberedInGroupoids hPg (BigFppfOver.topology B S hS)
    (fun U a b => hst'.isMorSheaf U a b) (fun U a b => hstP.isMorSheaf U a b) ?_).elim
    fun e => e.full
  intro U₀ a b
  obtain ⟨Ra, hRa, hRal⟩ := hx' U₀ a
  obtain ⟨Rb, hRb, hRbl⟩ := hx' U₀ b
  refine ⟨Ra ⊓ Rb, (BigFppfOver.topology B S hS).intersection_covering hRa hRb,
    fun {V} k hk => ⟨fun m₁ m₂ hm => ?_, fun Φ => ?_⟩⟩
  · exact Functor.Fiber.hom_ext (hLf.map_injective (congrArg (fun φ => φ.1) hm))
  obtain ⟨⟨⟨zal, ⟨⟨⟩⟩, zah⟩, hza⟩, ⟨ea⟩⟩ := hRal k hk.1
  obtain ⟨⟨⟨zbl, ⟨⟨⟩⟩, zbh⟩, hzb⟩, ⟨eb⟩⟩ := hRbl k hk.2
  change zal = V at hza
  change zbl = V at hzb
  subst hza
  subst zbl
  let Ea : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk zah) ≅
      (Functor.pullbackFiber 𝒳'.val.val.p a k).1 := Functor.Fiber.fiberInclusion.mapIso ea
  let Eb : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk zbh) ≅
      (Functor.pullbackFiber 𝒳'.val.val.p b k).1 := Functor.Fiber.fiberInclusion.mapIso eb
  have hEa : 𝒳'.val.val.p.IsHomLift (𝟙 zal) Ea.hom := ea.hom.2
  have hEb : 𝒳'.val.val.p.IsHomLift (𝟙 zal) Eb.hom := eb.hom.2
  exact exists_fiber_preimage_of_conj' hF.comp_eq Ea Eb hEa hEb Φ
    (fun Ψ hΨ => exists_preimage_cartesianComparison h x eK q' hq' hH3 zah zbh Ψ hΨ)

variable {gM f f' hcomm} in
/-- **The moduli square of a base-changed chart is a 2-fibre product.** The comparison
`𝒳' ⟶ M' ×_M 𝒳` is faithful (because `h` is), full and locally essentially surjective on fibres,
hence an equivalence over the site, `𝒳'` being a stack and `M' ×_M 𝒳` a prestack. -/
theorem nonempty_isTwoFibreProduct_moduliSquare (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK))
    (q : U ⟶ M) (q' : W ⟶ M')
    (hq : BasedFunctor.comp x.hom.hom f.hom = BasedFunctor.comp (sliceElementsComparison B S hS U)
      (associatedMap B S hS (yoneda.map q)).1.hom)
    (hq' : BasedFunctor.comp (chart' h x eK).hom f'.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS W)
        (associatedMap B S hS (yoneda.map q')).1.hom)
    (hH2 : IsPullback (yoneda.map fU) (yoneda.map q') (yoneda.map q) (yoneda.map gM))
    (hx : Functor.LocallyEssSurjOnFibers 𝒳.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p x.hom) (BigFppfOver.topology B S hS))
    (hx' : Functor.LocallyEssSurjOnFibers 𝒳'.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p (chart' h x eK)) (BigFppfOver.topology B S hS))
    (hhf : (CatFiberedInGroupoids.homFunctor h.hom).Faithful)
    (hH3 : ∀ (V : BigFppfOver B S hS) (w₁ w₂ : V ⟶ W), w₁ ≫ q' = w₂ ≫ q' →
      ∀ α : (CatFiberedInGroupoids.homFunctor h.hom).obj
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁)) ⟶
        (CatFiberedInGroupoids.homFunctor h.hom).obj
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂)),
        𝒳.val.val.p.IsHomLift (𝟙 V) α →
      ∃ ψ : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁) ⟶
          (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂),
        𝒳'.val.val.p.IsHomLift (𝟙 V) ψ ∧ (CatFiberedInGroupoids.homFunctor h.hom).map ψ = α)
 :
    Nonempty (Bicategory.IsTwoFibreProduct (moduliSquare h gM f f' hcomm)) := by
  let P := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (associatedMap B S hS (yoneda.map gM)).1 f
  let L := CatFiberedInGroupoids.homFunctor (cartesianComparison h gM f f' hcomm)
  have hPg : P.pt.val.p.IsFiberedInGroupoids := P.pt.isFiberedInGroupoids
  have hPf : P.pt.val.p.IsFibered := hPg.isFibered
  have h𝒳'f : 𝒳'.val.val.p.IsFibered := 𝒳'.val.isFiberedInGroupoids.isFibered
  have hF : 𝒳'.val.val.p.IsFibredOneMorphism P.pt.val.p L :=
    Functor.IsFibredOneMorphism.of_isFiberedInGroupoids hPg
      (CatFiberedInGroupoids.homFunctor_comp_p _)
  obtain ⟨-, ⟨hst', -⟩, -⟩ := 𝒳'.property
  obtain ⟨-, ⟨hstP, -⟩, -⟩ := isAlgebraicStack_twoFibreProductSquare.{u, w} B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj M') (isAlgebraicSpace_yoneda B S hS M'))
    (𝒵 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj M) (isAlgebraicSpace_yoneda B S hS M))
    (Bicategory.InducedBicategory.mkHom (associatedMap B S hS (yoneda.map gM)).1)
    (Bicategory.InducedBicategory.mkHom f)
  have hLf : L.Faithful := ⟨fun {X Y} φ₁ φ₂ hφ => hhf.map_injective
    (congrArg TwoFibreProductOver.Hom.b hφ)⟩
  have hLF : L.Full := full_cartesianComparison (hcomm := hcomm) h x eK q' hq' hx' hhf hH3
  have hloc := locallyEssSurjOnFibers_cartesianComparison (hcomm := hcomm) h x eK fU hfU q q' hq
    hq' hH2 hx
  have hE := Functor.isEquivalenceOver_of_locallyEssSurjOnFibers (F := L)
    hst'.hasEffectiveDescent (fun U a b => hstP.isMorSheaf U a b) hF hloc
  obtain ⟨E⟩ := hE
  exact ⟨Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
      (moduliSquare h gM f f' hcomm))
    (CategoryTheory.Equivalence.mk L E.inv E.unitIso.symm E.counitIso).isEquivalence_functor⟩

end ChartBaseChange

end AlgebraicGeometry.Stack

end
