module

public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjects
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonCocone

/-!
# Formal smoothness on objects, read through morphisms and cocones

A 1-morphism `P : 𝒲 ⟶ 𝒳` of categories fibred in groupoids over the big fppf site of `S` is
formally smooth on objects ([Stacks Project, Tag 06D0]) when objects of `𝒳` over an affine
first-order thickening `U'` of an affine `U` lift along `P` compatibly with a given lift over `U`.
This file restates the condition without chosen pullbacks: for a morphism `φ : P(x) ⟶ y'` lying
over the thickening `i : U ⟶ U'`, there are an object `x'` of `𝒲` over `U'`, a morphism `x ⟶ x'`
over `i` and an isomorphism `P(x') ≅ y'` over `U'` through which `φ` factors.

In that form it moves cocones. Let `Q` be a commutative square of the site whose second map is an
affine first-order thickening, and suppose every span of `𝒲` over `Q` has a cocone. Then a span of
`𝒳` over `Q` has a cocone as soon as its object over the first middle corner comes from `𝒲`: the
other two objects of the span are lifted, one by pulling back and one by formal smoothness on
objects, and the cocone in `𝒲` is carried back along `P`.

## Main results

* `AlgebraicGeometry.Stack.HasLiftsAlong.comp` and
  `AlgebraicGeometry.Stack.hasLiftsAlong_of_isIso`: lifts along composites and along isomorphisms.
* `AlgebraicGeometry.Stack.IsFormallySmoothOnObjectsOn.exists_lift` and
  `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects.exists_lift`: the lifting property for a
  morphism lying over the thickening.
* `AlgebraicGeometry.Stack.HasLiftsAlong`: lifts of morphisms along a morphism of the site.
* `AlgebraicGeometry.Stack.nonempty_cocone_of_hasLiftsAlong` and
  `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects.nonempty_cocone`: cocones over a span of
  `𝒳` from cocones over spans of `𝒲`, given lifts along the thickening.

## References

* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

universe u v w

namespace AlgebraicGeometry.Stack


/-- Composites in a category, cancelling two sections: the bookkeeping step of
`CategoryTheory.Functor.map_pullbackMap_comp_eq`. -/
private lemma comp_eq_of_section {C : Type*} [Category C] {A B D E G H : C} (ch : A ⟶ B)
    (ci : B ⟶ A) (hc : ci ≫ ch = 𝟙 B) (Fbh : B ⟶ D) (Fbi : D ⟶ B) (hb : Fbi ≫ Fbh = 𝟙 D)
    (g : D ⟶ E) (πy : E ⟶ G) (πF : A ⟶ H) (γ' : H ⟶ G) (Fπx : B ⟶ H)
    (e1 : (ch ≫ Fbh ≫ g) ≫ πy = πF ≫ γ') (e2 : ci ≫ πF = Fπx) :
    (Fbi ≫ Fπx) ≫ γ' = g ≫ πy := by
  rw [← e2, Category.assoc, Category.assoc, ← e1]
  simp only [Category.assoc, reassoc_of% hc, reassoc_of% hb]

/-- **The compatibility equation of Stacks 06D0, read in the total category.** For a functor
`F` over the base, isomorphisms `β : i^*x' ≅ x`, `γ : F(x) ≅ i^*y'` and `γ' : F(x') ≅ y'` of fibres
satisfying the equation of `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`, the morphism
`F(β⁻¹ ≫ (i^*x' ⟶ x'))` followed by `γ'` is `γ` followed by the chosen cartesian lift
`i^*y' ⟶ y'`. -/
lemma _root_.CategoryTheory.Functor.map_pullbackMap_comp_eq
    {𝒮 : Type*} [Category 𝒮] {𝒳 : Type*} [Category 𝒳] {𝒴 : Type*} [Category 𝒴]
    {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [p.IsPreFibered] [q.IsPreFibered] (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p)
    {U U' : 𝒮} (i : U ⟶ U') (x' : p.Fiber U') (xF : p.Fiber U) (yF : q.Fiber U')
    (β : pullbackFiber p x' i ≅ xF)
    (γ : (Fiber.mapOfComp p q F hF U).obj xF ≅ pullbackFiber q yF i)
    (γ' : (Fiber.mapOfComp p q F hF U').obj x' ≅ yF)
    (h₁ : q.IsCartesian i (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF U').obj x').2 i))
    (h₂ : q.IsCartesian i (F.map (IsPreFibered.pullbackMap x'.2 i)))
    (heq : ((fiberIsoOfCartesian i
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF U').obj x').2 i)
        (F.map (IsPreFibered.pullbackMap x'.2 i)) h₁ h₂).hom ≫
          (Fiber.mapOfComp p q F hF U).map β.hom) ≫ γ.hom = pullbackFiberHom γ'.hom i) :
    F.map (Fiber.fiberInclusion.map β.inv ≫ IsPreFibered.pullbackMap x'.2 i) ≫
        Fiber.fiberInclusion.map γ'.hom =
      Fiber.fiberInclusion.map γ.hom ≫ IsPreFibered.pullbackMap yF.2 i := by
  have e1 := congrArg (fun t => Fiber.fiberInclusion.map t ≫ IsPreFibered.pullbackMap yF.2 i) heq
  simp only [Functor.map_comp, Category.assoc, pullbackFiberHom_fac,
    Fiber.fiberInclusion_map_mapOfComp_map] at e1
  have e2 := @fiberIsoOfCartesian_inv_fac _ _ _ _ q _ _ i (F.obj x'.1)
        (pullbackFiber q ((Fiber.mapOfComp p q F hF U').obj x') i)
        ((Fiber.mapOfComp p q F hF U).obj (pullbackFiber p x' i))
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF U').obj x').2 i)
        (F.map (IsPreFibered.pullbackMap x'.2 i)) h₁ h₂
  refine (congrArg (fun t => t ≫ Fiber.fiberInclusion.map γ'.hom) (F.map_comp _ _)).trans ?_
  exact comp_eq_of_section _ _
    ((Fiber.fiberInclusion.map_comp _ _).symm.trans
      ((congrArg Fiber.fiberInclusion.map (Iso.inv_hom_id _)).trans
        (Fiber.fiberInclusion.map_id _)))
    _ _ ((F.map_comp _ _).symm.trans ((congrArg F.map
      ((Fiber.fiberInclusion.map_comp _ _).symm.trans
      ((congrArg Fiber.fiberInclusion.map (Iso.inv_hom_id β)).trans
        (Fiber.fiberInclusion.map_id _)))).trans (F.map_id _)))
    _ _ _ _ _ e1 e2

/-- If `F` lies over the base and `F(x) ⟶ y` lifts `f : R ⟶ S`, then `x` lies over `R`. -/
private lemma obj_eq_of_comp_eq {𝒮 𝒳 𝒴 : Type*} [Category 𝒮] [Category 𝒳] [Category 𝒴]
    {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p) {x : 𝒳} {y : 𝒴} {R S : 𝒮}
    (f : R ⟶ S) (φ : F.obj x ⟶ y) [q.IsHomLift f φ] : p.obj x = R := by
  rw [← hF]; exact IsHomLift.domain_eq q f φ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Lifts of morphisms along a morphism of the site.** A 1-morphism `P : 𝒳 ⟶ 𝒴` has lifts along
`i : U ⟶ U'` when every morphism `φ : P(x) ⟶ y'` lying over `i` is the image `P(ψ)` of a morphism
`ψ : x ⟶ x'` over `i` followed by a morphism `θ : P(x') ⟶ y'` over the identity of `U'`. For an
affine first-order thickening `i` this is formal smoothness on objects
(`AlgebraicGeometry.Stack.IsFormallySmoothOnObjectsOn.exists_lift`). -/
def HasLiftsAlong {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (P : 𝒳 ⟶ 𝒴) {U U' : BigFppfOver B S hS} (i : U ⟶ U') : Prop :=
  ∀ ⦃x : 𝒳.val.obj⦄ ⦃y' : 𝒴.val.obj⦄ (φ : (CatFiberedInGroupoids.homFunctor P).obj x ⟶ y'),
    𝒴.val.p.IsHomLift i φ →
    ∃ (x' : 𝒳.val.obj) (ψ : x ⟶ x') (θ : (CatFiberedInGroupoids.homFunctor P).obj x' ⟶ y'),
      𝒳.val.p.IsHomLift i ψ ∧ 𝒴.val.p.IsHomLift (𝟙 U') θ ∧
      (CatFiberedInGroupoids.homFunctor P).map ψ ≫ θ = φ

/-- Lifts along two composable morphisms give lifts along the composite: a morphism over the
composite factors through a cartesian lift over the second, and is lifted in two steps. -/
theorem HasLiftsAlong.comp
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒳 ⟶ 𝒴}
    {U U₁ U' : BigFppfOver B S hS} {i₁ : U ⟶ U₁} {i₂ : U₁ ⟶ U'} (h₁ : HasLiftsAlong P i₁)
    (h₂ : HasLiftsAlong P i₂) : HasLiftsAlong P (i₁ ≫ i₂) := by
  intro x y' φ hφ
  have h𝒴 := 𝒴.isFiberedInGroupoids
  have hy' : 𝒴.val.p.obj y' = U' := IsHomLift.codomain_eq _ (i₁ ≫ i₂) φ
  obtain ⟨y₁, π, hπ⟩ := h𝒴.exists_lift' i₂ y' hy'
  let φ₁ := h𝒴.fill (f := i₂) (g := i₁) (f' := i₁ ≫ i₂) rfl π φ
  have hφ₁ : 𝒴.val.p.IsHomLift i₁ φ₁ := h𝒴.fill_isHomLift _ _ _
  have eφ₁ : φ₁ ≫ π = φ := h𝒴.fill_fac _ _ _
  obtain ⟨x₁, ψ₁, θ₁, hψ₁, hθ₁, e₁⟩ := h₁ φ₁ hφ₁
  obtain ⟨x', ψ₂, θ, hψ₂, hθ, e₂⟩ := h₂ (θ₁ ≫ π) inferInstance
  refine ⟨x', ψ₁ ≫ ψ₂, θ, IsHomLift.comp 𝒳.val.p i₁ i₂ ψ₁ ψ₂, hθ, ?_⟩
  rw [Functor.map_comp, Category.assoc, e₂, ← Category.assoc, e₁, eφ₁]

/-- A 1-morphism has lifts along every isomorphism of the site. -/
theorem hasLiftsAlong_of_isIso
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (P : 𝒳 ⟶ 𝒴)
    {U U' : BigFppfOver B S hS} (e : U ⟶ U') [IsIso e] : HasLiftsAlong P e := by
  intro x y' φ hφ
  let F := CatFiberedInGroupoids.homFunctor P
  have hF : F ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p P
  have h𝒳 := 𝒳.isFiberedInGroupoids
  have hx := obj_eq_of_comp_eq hF e φ
  obtain ⟨a, α, hα⟩ := h𝒳.exists_lift' (inv e) x hx
  have : IsIso α := h𝒳.isIso_of_isHomLift_isIso (inv e) α
  have hFα : 𝒴.val.p.IsHomLift (inv e) (F.map α) := isHomLift_map_of_comp_eq hF (inv e) α
  refine ⟨a, inv α, F.map α ≫ φ, ?_, ?_, ?_⟩
  · have h := IsHomLift.inv 𝒳.val.p (inv e) α
    rwa [IsIso.inv_inv] at h
  · have h := IsHomLift.comp 𝒴.val.p (inv e) e (F.map α) φ
    rwa [IsIso.inv_hom_id] at h
  · rw [← Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id, Category.id_comp]

/-- **Formal smoothness on objects against a class of test objects, for a morphism over the
thickening.** If `P` is formally smooth on objects for the larger test objects in a class `C`,
`i : U ⟶ U'` an affine first-order thickening with `U'` in `C` and `φ : P(x) ⟶ y'` a morphism
over `i`, there are an object `x'` of `𝒳` over `U'`, a morphism `ψ : x ⟶ x'` over `i` and a
morphism `θ : P(x') ⟶ y'` over the identity of `U'` with `P(ψ) ≫ θ = φ`. -/
theorem IsFormallySmoothOnObjectsOn.exists_lift {C : BigFppfOver B S hS → Prop}
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒳 ⟶ 𝒴}
    (hP : IsFormallySmoothOnObjectsOn B S hS C 𝒳 𝒴 P)
    {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U')) (hCU' : C U')
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    {x : 𝒳.val.obj} {y' : 𝒴.val.obj} (φ : (CatFiberedInGroupoids.homFunctor P).obj x ⟶ y')
    [𝒴.val.p.IsHomLift i φ] :
    ∃ (x' : 𝒳.val.obj) (ψ : x ⟶ x') (θ : (CatFiberedInGroupoids.homFunctor P).obj x' ⟶ y'),
      𝒳.val.p.IsHomLift i ψ ∧ 𝒴.val.p.IsHomLift (𝟙 U') θ ∧
      (CatFiberedInGroupoids.homFunctor P).map ψ ≫ θ = φ := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor P
  have hF : F ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p P
  have hy' : 𝒴.val.p.obj y' = U' := IsHomLift.codomain_eq _ i φ
  have hx := obj_eq_of_comp_eq hF i φ
  let xF : 𝒳.val.p.Fiber U := ⟨x, hx⟩
  let yF : 𝒴.val.p.Fiber U' := ⟨y', hy'⟩
  let π := IsPreFibered.pullbackMap hy' i
  have : 𝒴.val.p.IsHomLift i π := inferInstance
  let g₀ :=
    𝒴.isFiberedInGroupoids.fill (a := (pullbackFiber 𝒴.val.p yF i).1) (f := i) (g := 𝟙 U)
      (f' := i) (by simp) π φ
  have : 𝒴.val.p.IsHomLift (𝟙 U) g₀ := 𝒴.isFiberedInGroupoids.fill_isHomLift _ _ _
  have eg₀ : g₀ ≫ π = φ := 𝒴.isFiberedInGroupoids.fill_fac _ _ _
  let γ : (Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF U).obj xF ≅ pullbackFiber 𝒴.val.p yF i :=
    have : 𝒴.val.p.IsHomLift (𝟙 U)
        (show ((Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF U).obj xF).1 ⟶
          (pullbackFiber 𝒴.val.p yF i).1 from g₀) := by assumption
    Deformation.Artin.fiberIsoOfIsHomLift 𝒴.isFiberedInGroupoids
      (show ((Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF U).obj xF).1 ⟶
          (pullbackFiber 𝒴.val.p yF i).1 from g₀)
  obtain ⟨x', β, γ', heq⟩ := hP U U' i hU hU' hCU' hi xF yF γ
  beta_reduce at heq
  have hβ : 𝒳.val.p.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map β.inv) := β.inv.2
  let πx := IsPreFibered.pullbackMap x'.2 i
  have hπx : 𝒳.val.p.IsHomLift i πx := inferInstance
  have : 𝒴.val.p.IsHomLift (𝟙 U') (Fiber.fiberInclusion.map γ'.hom) := γ'.hom.2
  refine ⟨x'.1, Fiber.fiberInclusion.map β.inv ≫ πx, Fiber.fiberInclusion.map γ'.hom,
    @IsHomLift.comp_lift_id_left' _ _ _ _ _ _ _ _ U _ hβ _ _ i _ hπx, γ'.hom.2, ?_⟩
  have h1 := map_pullbackMap_comp_eq F hF i x' xF yF β γ γ' _ _ heq
  have h2 : Fiber.fiberInclusion.map γ.hom ≫ IsPreFibered.pullbackMap yF.2 i = φ := eg₀
  exact h1.trans h2

/-- **Formal smoothness on objects, for a morphism over the thickening.** If `P` is formally
smooth on objects, `i : U ⟶ U'` an affine first-order thickening and `φ : P(x) ⟶ y'` a morphism
over `i`, there are an object `x'` of `𝒳` over `U'`, a morphism `ψ : x ⟶ x'` over `i` and a
morphism `θ : P(x') ⟶ y'` over the identity of `U'` with `P(ψ) ≫ θ = φ`. -/
theorem IsFormallySmoothOnObjects.exists_lift
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒳 ⟶ 𝒴}
    (hP : IsFormallySmoothOnObjects B S hS 𝒳 𝒴 P)
    {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U'))
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    {x : 𝒳.val.obj} {y' : 𝒴.val.obj} (φ : (CatFiberedInGroupoids.homFunctor P).obj x ⟶ y')
    [𝒴.val.p.IsHomLift i φ] :
    ∃ (x' : 𝒳.val.obj) (ψ : x ⟶ x') (θ : (CatFiberedInGroupoids.homFunctor P).obj x' ⟶ y'),
      𝒳.val.p.IsHomLift i ψ ∧ 𝒴.val.p.IsHomLift (𝟙 U') θ ∧
      (CatFiberedInGroupoids.homFunctor P).map ψ ≫ θ = φ :=
  (hP.isFormallySmoothOnObjectsOn fun _ => True).exists_lift i hU hU' trivial hi φ

/-- **Cocones along a 1-morphism with lifts along a thickening.** Let `P : 𝒲 ⟶ 𝒳` be a
1-morphism and `Q` a commutative square of the site such that every morphism `P(x) ⟶ y'` over the
second map `Q.g` factors as the image of a morphism `x ⟶ x'` over `Q.g` followed by a morphism over
the identity, and such that every span of `𝒲` over `Q` has a cocone. Then a span `s` of `𝒳` over
`Q` has a cocone as soon as its object over the first middle corner is, up to an isomorphism over
the identity, the image `P(a)` of an object of `𝒲`. -/
theorem nonempty_cocone_of_hasLiftsAlong
    {𝒲 𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒲 ⟶ 𝒳}
    (Q : BaseSquare (BigFppfOver B S hS)) (hlift : HasLiftsAlong P Q.g)
    (hcoc : ∀ t : SquareSpan 𝒲.val.p Q.f Q.g, Nonempty (t.Cocone Q.i Q.j))
    (s : SquareSpan 𝒳.val.p Q.f Q.g) (a : 𝒲.val.obj)
    (ε : (CatFiberedInGroupoids.homFunctor P).obj a ⟶ s.x) [𝒳.val.p.IsHomLift (𝟙 Q.V) ε] :
    Nonempty (s.Cocone Q.i Q.j) := by
  let F := CatFiberedInGroupoids.homFunctor P
  have hF : F ⋙ 𝒳.val.p = 𝒲.val.p := CatFiberedInGroupoids.homFunctor_comp_p P
  have h𝒲 := 𝒲.isFiberedInGroupoids
  have h𝒳 := 𝒳.isFiberedInGroupoids
  have ha := obj_eq_of_comp_eq hF (𝟙 Q.V) ε
  obtain ⟨x0, αt, hαt⟩ := h𝒲.exists_lift' Q.f a ha
  have hFαt : 𝒳.val.p.IsHomLift Q.f (F.map αt) := isHomLift_map_of_comp_eq hF Q.f αt
  have : IsIso ε := h𝒳.isIso_of_isHomLift_isIso (𝟙 Q.V) ε
  let mu := h𝒳.fill (f := Q.f) (g := 𝟙 Q.U) (f' := Q.f) (by simp) (F.map αt) (s.α ≫ inv ε)
  have hmu : 𝒳.val.p.IsHomLift (𝟙 Q.U) mu := h𝒳.fill_isHomLift _ _ _
  have emu : mu ≫ F.map αt = s.α ≫ inv ε := h𝒳.fill_fac _ _ _
  have : IsIso mu := h𝒳.isIso_of_isHomLift_isIso (𝟙 Q.U) mu
  have hφ : 𝒳.val.p.IsHomLift Q.g (inv mu ≫ s.β) := inferInstance
  obtain ⟨x', ψ, θ, hψ, hθ, hψθ⟩ := hlift (inv mu ≫ s.β) hφ
  have : IsIso θ := h𝒳.isIso_of_isHomLift_isIso (𝟙 Q.W) θ
  let t : SquareSpan 𝒲.val.p Q.f Q.g := ⟨x0, a, x', αt, ψ, hαt, hψ⟩
  let mx := inv ε
  let my := inv θ
  have hmx : 𝒳.val.p.IsHomLift (𝟙 Q.V) mx := inferInstance
  have hmy : 𝒳.val.p.IsHomLift (𝟙 Q.W) my := inferInstance
  obtain ⟨c⟩ := hcoc t
  let m : SquareSpan.Hom (BaseSquare.Hom.id Q) s (t.map hF) :=
    { mu := mu
      mx := mx
      my := my
      isHomLift_mu := hmu
      isHomLift_mx := hmx
      isHomLift_my := hmy
      comm_α := emu.symm
      comm_β := by
        show s.β ≫ my = mu ≫ F.map ψ
        rw [← cancel_mono θ, Category.assoc, Category.assoc, hψθ, IsIso.inv_hom_id,
          Category.comp_id, IsIso.hom_inv_id_assoc] }
  obtain ⟨c', -⟩ := SquareSpan.exists_pull h𝒳 m (c.map hF)
  exact ⟨c'⟩

/-- **Cocones along a 1-morphism formally smooth on objects.** Let `P : 𝒲 ⟶ 𝒳` be formally
smooth on objects and `Q` a commutative square of the site whose second map `Q.g` is a first-order
thickening of affine schemes, such that every span of `𝒲` over `Q` has a cocone. Then a span `s`
of `𝒳` over `Q` has a cocone as soon as its object over the first middle corner is, up to an
isomorphism over the identity, the image `P(a)` of an object of `𝒲`. -/
theorem IsFormallySmoothOnObjects.nonempty_cocone
    {𝒲 𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒲 ⟶ 𝒳}
    (hP : IsFormallySmoothOnObjects B S hS 𝒲 𝒳 P) (Q : BaseSquare (BigFppfOver B S hS))
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W))
    (hg : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map Q.g))
    (hcoc : ∀ t : SquareSpan 𝒲.val.p Q.f Q.g, Nonempty (t.Cocone Q.i Q.j))
    (s : SquareSpan 𝒳.val.p Q.f Q.g) (a : 𝒲.val.obj)
    (ε : (CatFiberedInGroupoids.homFunctor P).obj a ⟶ s.x) [𝒳.val.p.IsHomLift (𝟙 Q.V) ε] :
    Nonempty (s.Cocone Q.i Q.j) :=
  nonempty_cocone_of_hasLiftsAlong Q (fun _ _ φ _ => hP.exists_lift Q.g hU hW hg φ) hcoc s a ε

end AlgebraicGeometry.Stack

end
