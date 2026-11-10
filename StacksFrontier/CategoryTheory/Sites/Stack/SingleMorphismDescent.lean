module

public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence

/-!
# Descent along one covering morphism, read in the total category

Let `p : 𝒳 ⥤ 𝒮` be a stack over a site `(𝒮, J)` with fibre products, and let `c : V ⟶ U` be a
morphism generating a covering sieve of `U`. Stacks 02ZF says that the functor from the fibre over
`U` to the category of descent data relative to `{c}` is an equivalence. This file reads the three
halves of that statement in the shape in which they are used to *construct* objects and morphisms
locally: with descent data written over the chosen fibre product `V ×_U V`
(Mathlib's `CategoryTheory.Pseudofunctor.DescentData'`), and with the outputs written as morphisms
of the total category `𝒳` lying over morphisms of `𝒮`.

## Main results

* `CategoryTheory.Functor.eq_of_comp_eq_of_mem_singleton_sieve`: two morphisms out of an object
  over `U`, lying over one and the same morphism, are equal once they agree after composing with a
  strongly cartesian morphism over `c`.
* `CategoryTheory.Functor.exists_comp_eq_of_mem_singleton_sieve`: a morphism out of the source of a
  strongly cartesian morphism `τ` over `c` factors through `τ` as soon as its two restrictions to
  `V ×_U V` agree.
* `CategoryTheory.Functor.exists_descends_of_mem_singleton_sieve`: every descent datum relative to
  `{c}` written over the chosen fibre product descends, to an object `y` over `U` with a strongly
  cartesian morphism over `c` which coequalizes the two restrictions of the datum to `V ×_U V`.
* `CategoryTheory.Functor.exists_descent_of_mem_singleton_sieve`: the same, with the descent datum
  itself written in the total category, as a pair of morphisms `d₁, d₂ : P ⟶ η` over the two
  projections of `V ×_U V` which is reflexive and transitive.
* `CategoryTheory.Functor.fiberInclusion_map_pullHom_comp`: the pullback of a morphism between two
  chosen pullbacks, in the sense of Mathlib's descent API, is determined by its composite with a
  chosen cartesian lift.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite Limits Pseudofunctor IsFibered

universe v₁ v₂ u₁ u₂

-- `Fiber` and its inclusion must unfold for the endpoints of the composites below to be seen as
-- equal at `implicit` transparency.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒮) [p.IsFibered]

/-! ### Mathlib's pullback of a morphism between chosen pullbacks -/

/-- Mathlib's pullback `LocallyDiscreteOpToCat.pullHom` of a morphism `φ : f₁^* M₁ ⟶ f₂^* M₂`
between chosen pullbacks along `g` is the base change of `φ` along `g`, conjugated by the
canonical contractions of the iterated chosen pullbacks. This is
`CategoryTheory.Functor.pullHom_eq` with the two composites named. -/
lemma pullHom_eq' {X₁ X₂ Y Y' : 𝒮} (M₁ : p.Fiber X₁) (M₂ : p.Fiber X₂)
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (φ : pullbackFiber p M₁ f₁ ⟶ pullbackFiber p M₂ f₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor p) (M₁ := M₁) (M₂ := M₂)
        (f₁ := f₁) (f₂ := f₂) φ g gf₁ gf₂ hgf₁ hgf₂ =
      (pullbackFiberCompIso' M₁ f₁ g gf₁ hgf₁).inv ≫ pullbackFiberHom φ g ≫
        (pullbackFiberCompIso' M₂ f₂ g gf₂ hgf₂).hom := by
  subst hgf₁ hgf₂
  exact pullHom_eq p M₁ M₂ f₁ f₂ g φ

/-- The base change of `φ : f₁^* M₁ ⟶ f₂^* M₂` along `g`, conjugated by the canonical
contractions, followed by the chosen cartesian lift of `g ≫ f₂`, is `φ` followed by the chosen
cartesian lift of `f₂`, precomposed with the morphism over `g` which carries the chosen lift of
`g ≫ f₁` to that of `f₁`. -/
lemma fiberInclusion_map_pullbackFiberHom_conj_comp {X₁ X₂ Y Y' : 𝒮} {M₁ : p.Fiber X₁}
    {M₂ : p.Fiber X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : pullbackFiber p M₁ f₁ ⟶ pullbackFiber p M₂ f₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (κ : (pullbackFiber p M₁ gf₁).1 ⟶ (pullbackFiber p M₁ f₁).1) (hκl : p.IsHomLift g κ)
    (hκ : κ ≫ IsPreFibered.pullbackMap M₁.2 f₁ = IsPreFibered.pullbackMap M₁.2 gf₁) :
    Fiber.fiberInclusion.map ((pullbackFiberCompIso' M₁ f₁ g gf₁ hgf₁).inv ≫
        pullbackFiberHom φ g ≫ (pullbackFiberCompIso' M₂ f₂ g gf₂ hgf₂).hom) ≫
        IsPreFibered.pullbackMap M₂.2 gf₂ =
      κ ≫ Fiber.fiberInclusion.map φ ≫ IsPreFibered.pullbackMap M₂.2 f₂ := by
  have hκ' : κ = Fiber.fiberInclusion.map (pullbackFiberCompIso' M₁ f₁ g gf₁ hgf₁).inv ≫
      IsPreFibered.pullbackMap (pullbackFiber p M₁ f₁).2 g := by
    have := hκl
    refine IsStronglyCartesian.ext p f₁ (IsPreFibered.pullbackMap M₁.2 f₁) g ?_
    rw [hκ, Category.assoc, pullbackFiberCompIso'_inv_fac]
  rw [hκ', Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    pullbackFiberCompIso'_hom_fac, pullbackFiberHom_fac_assoc, Category.assoc]

/-- A morphism `α` out of an object `x` of the fibre over `R`, lying over `g`, is the composite of a
morphism of the fibre into the chosen pullback along `g` with the chosen cartesian lift. -/
private lemma exists_fiberInclusion_map_comp_eq {R S : 𝒮} (x : p.Fiber R) (y : p.Fiber S)
    (g : R ⟶ S) (α : x.1 ⟶ y.1) (hα : p.IsHomLift g α) :
    ∃ α' : x ⟶ pullbackFiber p y g,
      Fiber.fiberInclusion.map α' ≫ IsPreFibered.pullbackMap y.2 g = α :=
  ⟨⟨IsStronglyCartesian.map p g (IsPreFibered.pullbackMap y.2 g) (f' := g) (g := 𝟙 R)
    (Category.id_comp g).symm α, inferInstance⟩,
    IsStronglyCartesian.fac p g (IsPreFibered.pullbackMap y.2 g) (f' := g) (g := 𝟙 R)
      (Category.id_comp g).symm α⟩

/-! ### The equivalence with descent data relative to one morphism -/

section SingleMorphism

variable [HasPullbacks 𝒮] {V U : 𝒮} (c : V ⟶ U)

/-- The chosen fibre product `V ×_U V` of `c` with itself. -/
noncomputable abbrev singleChosenPullback : ChosenPullback c c :=
  ChosenPullback.ofHasPullback c c

/-- The chosen triple fibre product `V ×_U V ×_U V`. -/
noncomputable abbrev singleChosenPullback₃ :
    ChosenPullback₃ (singleChosenPullback c) (singleChosenPullback c) (singleChosenPullback c) :=
  ChosenPullback₃.ofHasPullbacks _ _ _

/-- The category of descent data relative to the one-element family `{c}`, written over the chosen
fibre products. -/
abbrev SingleDescentData :=
  (pullbackPseudofunctor p).DescentData' (f := fun _ : Unit => c)
    (fun _ _ => singleChosenPullback c) (fun _ _ _ => singleChosenPullback₃ c)

/-- The functor from the fibre over `U` to the descent data relative to `{c}` written over the
chosen fibre products. -/
noncomputable def singleDescentFunctor : p.Fiber U ⥤ SingleDescentData p c :=
  (pullbackPseudofunctor p).toDescentData (fun _ : Unit => c) ⋙
    DescentData'.fromDescentDataFunctor _ _ _

variable {p} in
/-- Over a stack, the functor to the descent data relative to a morphism generating a covering
sieve is an equivalence: Stacks 02ZF composed with Mathlib's comparison of the two presentations
of descent data. -/
lemma isEquivalence_singleDescentFunctor {J : GrothendieckTopology 𝒮} (hp : p.IsStack J)
    (hc : Sieve.generate (Presieve.singleton c) ∈ J U) :
    (singleDescentFunctor p c).IsEquivalence := by
  have hc' : Sieve.ofArrows (fun _ : Unit => V) (fun _ => c) ∈ J U := by
    rwa [Sieve.ofArrows, Presieve.ofArrows_pUnit]
  have h₁ := isEquivalence_toDescentData_of_isStack p hp (fun _ : Unit => c) hc'
  have h₂ : (DescentData'.fromDescentDataFunctor (pullbackPseudofunctor p)
      (f := fun _ : Unit => c) (fun _ _ => singleChosenPullback c)
      (fun _ _ _ => singleChosenPullback₃ c)).IsEquivalence :=
    (DescentData'.descentDataEquivalence _ _ _).isEquivalence_inverse
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h₁ h₂

/-- The component of the image of a morphism under `singleDescentFunctor` is its base change. -/
lemma singleDescentFunctor_map_hom {x y : p.Fiber U} (α : x ⟶ y) :
    ((singleDescentFunctor p c).map α).hom () = pullbackFiberHom α c :=
  pullbackPseudofunctor_map_map p c α

/-- The gluing morphism of the descent datum of an object is the canonical comparison of its two
iterated chosen pullbacks. -/
lemma singleDescentFunctor_obj_hom (x : p.Fiber U) :
    ((singleDescentFunctor p c).obj x).hom () () =
      (pullbackFiberComparison x (pullback.fst c c) (pullback.snd c c) pullback.condition).hom :=
  toDescentData_obj_hom p (fun _ : Unit => c) x (i₁ := ()) (i₂ := ()) (pullback.fst c c ≫ c)
    (pullback.fst c c)
    (pullback.snd c c) rfl pullback.condition.symm pullback.condition

/-! ### The three halves, in the total category -/

variable {p} {J : GrothendieckTopology 𝒮} (hp : p.IsStack J)
  (hc : Sieve.generate (Presieve.singleton c) ∈ J U)
include hp hc

/-- Base change along a morphism generating a covering sieve is injective on morphisms of the
fibre. -/
lemma eq_of_pullbackFiberHom_eq_of_mem {x y : p.Fiber U} {α β : x ⟶ y}
    (h : pullbackFiberHom α c = pullbackFiberHom β c) : α = β := by
  have := isEquivalence_singleDescentFunctor c hp hc
  refine (singleDescentFunctor p c).map_injective ?_
  ext ⟨⟩
  rw [singleDescentFunctor_map_hom, singleDescentFunctor_map_hom, h]

/-- **Separation along one covering morphism.** Two morphisms out of an object `x` over `U`, lying
over one and the same morphism `g`, are equal once they agree after composing with a strongly
cartesian morphism `λ` over `c`. -/
theorem eq_of_comp_eq_of_mem_singleton_sieve {v : 𝒳} {x : p.Fiber U} (l : v ⟶ x.1)
    [p.IsStronglyCartesian c l] {W : 𝒮} (g : U ⟶ W) {y : 𝒳} (α β : x.1 ⟶ y)
    (hα : p.IsHomLift g α) (hβ : p.IsHomLift g β) (h : l ≫ α = l ≫ β) : α = β := by
  have hy : p.obj y = W := IsHomLift.codomain_eq p g α
  let y' : p.Fiber W := ⟨y, hy⟩
  let yg := pullbackFiber p y' g
  -- the two morphisms, read in the fibre over `U`
  obtain ⟨α', hα'⟩ := exists_fiberInclusion_map_comp_eq p x y' g α hα
  obtain ⟨β', hβ'⟩ := exists_fiberInclusion_map_comp_eq p x y' g β hβ
  -- `l` through the chosen lift of `c`
  let μ : v ⟶ (pullbackFiber p x c).1 :=
    (IsCartesian.domainUniqueUpToIso p c (IsPreFibered.pullbackMap x.2 c) l).hom
  have hμ : μ ≫ IsPreFibered.pullbackMap x.2 c = l := IsCartesian.fac p c _ l
  have : IsIso μ := inferInstance
  have key : ∀ γ : x ⟶ yg, l ≫ Fiber.fiberInclusion.map γ ≫ IsPreFibered.pullbackMap y'.2 g =
      μ ≫ Fiber.fiberInclusion.map (pullbackFiberHom γ c) ≫
        IsPreFibered.pullbackMap yg.2 c ≫ IsPreFibered.pullbackMap y'.2 g := by
    intro γ
    rw [← hμ, pullbackFiberHom_fac_assoc, Category.assoc]
  have hmap : μ ≫ Fiber.fiberInclusion.map (pullbackFiberHom α' c) =
      μ ≫ Fiber.fiberInclusion.map (pullbackFiberHom β' c) := by
    refine IsStronglyCartesian.ext p (c ≫ g)
      (IsPreFibered.pullbackMap yg.2 c ≫ IsPreFibered.pullbackMap y'.2 g) (𝟙 V) ?_
    simp only [Category.assoc]
    rw [← key, ← key, hα', hβ', h]
  have h2 : pullbackFiberHom α' c = pullbackFiberHom β' c :=
    Fiber.hom_ext ((cancel_epi μ).1 hmap)
  rw [← hα', ← hβ', eq_of_pullbackFiberHom_eq_of_mem c hp hc h2]

/-- **Gluing along one covering morphism, in the fibre.** A morphism `c^* x ⟶ c^* y` of the fibre
over `V` whose two pullbacks to `V ×_U V` agree, through the canonical comparisons, is the base
change of a morphism `x ⟶ y` of the fibre over `U`. -/
lemma exists_pullbackFiberHom_eq_of_mem {x y : p.Fiber U}
    (μ : pullbackFiber p x c ⟶ pullbackFiber p y c)
    (hμ : pullbackFiberHom μ (pullback.fst c c) ≫ (pullbackFiberComparison y (pullback.fst c c)
        (pullback.snd c c) pullback.condition).hom =
      (pullbackFiberComparison x (pullback.fst c c) (pullback.snd c c)
        pullback.condition).hom ≫ pullbackFiberHom μ (pullback.snd c c)) :
    ∃ α : x ⟶ y, pullbackFiberHom α c = μ := by
  have := isEquivalence_singleDescentFunctor c hp hc
  let ψ : (singleDescentFunctor p c).obj x ⟶ (singleDescentFunctor p c).obj y :=
    { hom := fun _ => μ
      comm := fun _ _ => by
        rw [singleDescentFunctor_obj_hom, singleDescentFunctor_obj_hom]
        exact (pullbackPseudofunctor_map_map p (pullback.fst c c) μ ▸
          pullbackPseudofunctor_map_map p (pullback.snd c c) μ ▸ hμ) }
  refine ⟨(singleDescentFunctor p c).preimage ψ, ?_⟩
  rw [← singleDescentFunctor_map_hom, Functor.map_preimage]

/-- **Gluing along one covering morphism.** Let `τ : v ⟶ x` be strongly cartesian over `c`, with
`x` over `U`, and let `m : v ⟶ y` lie over `c ≫ g`. If the two restrictions of `m` to `V ×_U V`
agree — any two morphisms into `v` over the two projections which agree after `τ` also agree after
`m` — then `m` factors through `τ` by a morphism over `g`. -/
theorem exists_comp_eq_of_mem_singleton_sieve {v : 𝒳} {x : p.Fiber U} (τ : v ⟶ x.1)
    [p.IsStronglyCartesian c τ] {W : 𝒮} (g : U ⟶ W) {y : 𝒳} (m : v ⟶ y)
    [p.IsHomLift (c ≫ g) m]
    (hm : ∀ {t : 𝒳} (α₁ α₂ : t ⟶ v), p.IsHomLift (pullback.fst c c) α₁ →
      p.IsHomLift (pullback.snd c c) α₂ → α₁ ≫ τ = α₂ ≫ τ → α₁ ≫ m = α₂ ≫ m) :
    ∃ u : x.1 ⟶ y, p.IsHomLift g u ∧ τ ≫ u = m := by
  have hy : p.obj y = W := IsHomLift.codomain_eq p (c ≫ g) m
  let y' : p.Fiber W := ⟨y, hy⟩
  let yg := pullbackFiber p y' g
  -- `m` through the chosen lifts of `g` and `c`
  let m₁ : v ⟶ yg.1 := IsStronglyCartesian.map p g (IsPreFibered.pullbackMap y'.2 g)
    (f' := c ≫ g) (g := c) rfl m
  have hm₁ : m₁ ≫ IsPreFibered.pullbackMap y'.2 g = m :=
    IsStronglyCartesian.fac p g (IsPreFibered.pullbackMap y'.2 g) (f' := c ≫ g) (g := c) rfl m
  let ν : v ⟶ (pullbackFiber p yg c).1 := IsStronglyCartesian.map p c
    (IsPreFibered.pullbackMap yg.2 c) (f' := c) (g := 𝟙 V) (Category.id_comp c).symm m₁
  have hν : ν ≫ IsPreFibered.pullbackMap yg.2 c = m₁ :=
    IsStronglyCartesian.fac p c (IsPreFibered.pullbackMap yg.2 c) (f' := c) (g := 𝟙 V)
      (Category.id_comp c).symm m₁
  -- `τ` through the chosen lift of `c`
  let μ₀ : v ⟶ (pullbackFiber p x c).1 :=
    (IsCartesian.domainUniqueUpToIso p c (IsPreFibered.pullbackMap x.2 c) τ).hom
  have hμ₀ : μ₀ ≫ IsPreFibered.pullbackMap x.2 c = τ := IsCartesian.fac p c _ τ
  have : IsIso μ₀ := inferInstance
  -- the morphism of the fibre over `V` to be glued
  let μ : pullbackFiber p x c ⟶ pullbackFiber p yg c := ⟨CategoryTheory.inv μ₀ ≫ ν, inferInstance⟩
  have hμν : μ₀ ≫ Fiber.fiberInclusion.map μ = ν := by
    change μ₀ ≫ CategoryTheory.inv μ₀ ≫ ν = ν
    simp
  have hμ₀' : CategoryTheory.inv μ₀ ≫ τ = IsPreFibered.pullbackMap x.2 c := by
    rw [← hμ₀, IsIso.inv_hom_id_assoc]
  have hμm : Fiber.fiberInclusion.map μ ≫ IsPreFibered.pullbackMap yg.2 c ≫
      IsPreFibered.pullbackMap y'.2 g = CategoryTheory.inv μ₀ ≫ m := by
    change (CategoryTheory.inv μ₀ ≫ ν) ≫ _ ≫ _ = _
    rw [Category.assoc, reassoc_of% hν, hm₁]
  -- the two restrictions of `m` to `V ×_U V`
  let α₁ : (pullbackFiber p (pullbackFiber p x c) (pullback.fst c c)).1 ⟶ v :=
    IsPreFibered.pullbackMap (pullbackFiber p x c).2 (pullback.fst c c) ≫ CategoryTheory.inv μ₀
  let α₂ : (pullbackFiber p (pullbackFiber p x c) (pullback.fst c c)).1 ⟶ v :=
    Fiber.fiberInclusion.map (pullbackFiberComparison x (pullback.fst c c) (pullback.snd c c)
      pullback.condition).hom ≫
      IsPreFibered.pullbackMap (pullbackFiber p x c).2 (pullback.snd c c) ≫ CategoryTheory.inv μ₀
  have hα₁ : p.IsHomLift (pullback.fst c c) α₁ := inferInstance
  have hα₂ : p.IsHomLift (pullback.snd c c) α₂ := by
    have : p.IsHomLift (𝟙 (pullback c c)) (Fiber.fiberInclusion.map (pullbackFiberComparison x
      (pullback.fst c c) (pullback.snd c c) pullback.condition).hom) :=
      (pullbackFiberComparison x (pullback.fst c c) (pullback.snd c c) pullback.condition).hom.2
    infer_instance
  have hατ : α₁ ≫ τ = α₂ ≫ τ := by
    simp only [α₁, α₂, Category.assoc, hμ₀']
    exact (pullbackFiberComparison_hom_fac x (pullback.fst c c) (pullback.snd c c)
      pullback.condition).symm
  have hαm := hm α₁ α₂ hα₁ hα₂ hατ
  have hcart : p.IsStronglyCartesian (pullback.snd c c ≫ c ≫ g)
      (IsPreFibered.pullbackMap (pullbackFiber p yg c).2 (pullback.snd c c) ≫
        IsPreFibered.pullbackMap yg.2 c ≫ IsPreFibered.pullbackMap y'.2 g) := inferInstance
  obtain ⟨α, hα⟩ := exists_pullbackFiberHom_eq_of_mem c hp hc μ (by
    refine fiber_hom_ext_of_cartesian (pullback.snd c c ≫ c ≫ g)
      (IsPreFibered.pullbackMap (pullbackFiber p yg c).2 (pullback.snd c c) ≫
        IsPreFibered.pullbackMap yg.2 c ≫ IsPreFibered.pullbackMap y'.2 g) inferInstance _ _ ?_
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% pullbackFiberComparison_hom_fac yg (pullback.fst c c) (pullback.snd c c)
        pullback.condition, reassoc_of% pullbackFiberHom_fac μ (pullback.fst c c),
      reassoc_of% pullbackFiberHom_fac μ (pullback.snd c c), hμm]
    simpa only [α₁, α₂, Category.assoc] using hαm)
  refine ⟨Fiber.fiberInclusion.map α ≫ IsPreFibered.pullbackMap y'.2 g, inferInstance, ?_⟩
  rw [← hμ₀, Category.assoc, ← pullbackFiberHom_fac_assoc, hα, ← Category.assoc, hμν, ← hm₁,
    ← hν, Category.assoc]

/-- **Effective descent along one covering morphism.** A descent datum relative to `{c}`, written
over the chosen fibre product `V ×_U V`, descends: there is an object `y` over `U` with a strongly
cartesian morphism `ζ` over `c` from the object of the datum, which coequalizes the two morphisms
to it over the two projections of `V ×_U V` that the datum provides. -/
theorem exists_descends_of_mem_singleton_sieve (D : SingleDescentData p c) :
    ∃ (y : p.Fiber U) (ζ : (D.obj () : p.Fiber V).1 ⟶ y.1), p.IsStronglyCartesian c ζ ∧
      IsPreFibered.pullbackMap (D.obj () : p.Fiber V).2 (pullback.fst c c) ≫ ζ =
        (Fiber.fiberInclusion.map (show pullbackFiber p (D.obj ()) (pullback.fst c c) ⟶
          pullbackFiber p (D.obj ()) (pullback.snd c c) from D.hom () ()) ≫
          IsPreFibered.pullbackMap (D.obj () : p.Fiber V).2 (pullback.snd c c)) ≫ ζ := by
  have := isEquivalence_singleDescentFunctor c hp hc
  let y := (singleDescentFunctor p c).objPreimage D
  let e : (singleDescentFunctor p c).obj y ≅ D := (singleDescentFunctor p c).objObjPreimageIso D
  let D₀ : p.Fiber V := D.obj ()
  let ψ : D₀ ⟶ pullbackFiber p y c := e.inv.hom ()
  let ψ' : pullbackFiber p y c ⟶ D₀ := e.hom.hom ()
  let θ : pullbackFiber p D₀ (pullback.fst c c) ⟶ pullbackFiber p D₀ (pullback.snd c c) :=
    D.hom () ()
  have hcomm : pullbackFiberHom ψ (pullback.fst c c) ≫ (pullbackFiberComparison y
      (pullback.fst c c) (pullback.snd c c) pullback.condition).hom =
      θ ≫ pullbackFiberHom ψ (pullback.snd c c) := by
    have h := e.inv.comm () ()
    rw [singleDescentFunctor_obj_hom] at h
    exact (pullbackPseudofunctor_map_map p (pullback.fst c c) ψ ▸
      pullbackPseudofunctor_map_map p (pullback.snd c c) ψ ▸ h)
  have : IsIso ψ := ⟨ψ',
    congrArg (fun φ : D ⟶ D => DescentData'.Hom.hom φ ()) e.inv_hom_id,
    congrArg (fun φ : (singleDescentFunctor p c).obj y ⟶ (singleDescentFunctor p c).obj y =>
      DescentData'.Hom.hom φ ()) e.hom_inv_id⟩
  have : IsIso (Fiber.fiberInclusion.map ψ) := Functor.map_isIso _ ψ
  refine ⟨y, Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap y.2 c, ?_, ?_⟩
  · have : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map ψ) := ψ.2
    have : p.IsStronglyCartesian (𝟙 V ≫ c)
        (Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap y.2 c) := inferInstance
    rwa [Category.id_comp] at this
  · rw [← reassoc_of% pullbackFiberHom_fac ψ (pullback.fst c c),
      ← pullbackFiberComparison_hom_fac y (pullback.fst c c) (pullback.snd c c) pullback.condition,
      ← Functor.map_comp_assoc, hcomm, Functor.map_comp_assoc,
      reassoc_of% pullbackFiberHom_fac ψ (pullback.snd c c), Category.assoc]

omit hp hc in
/-- Mathlib's pullback `DescentData'.pullHom'` of a gluing morphism over `V ×_U V` along a pair
of morphisms to `V` is the base change along the induced morphism to `V ×_U V`, conjugated by the
canonical contractions of the iterated chosen pullbacks. -/
lemma pullHom'_single_eq (η : p.Fiber V)
    (φ : pullbackFiber p η (pullback.fst c c) ⟶ pullbackFiber p η (pullback.snd c c))
    {Y : 𝒮} (q : Y ⟶ U) (f₁ f₂ : Y ⟶ V) (hf₁ : f₁ ≫ c = q) (hf₂ : f₂ ≫ c = q) :
    DescentData'.pullHom' (F := pullbackPseudofunctor p) (f := fun _ : Unit => c)
        (sq := fun _ _ => singleChosenPullback c) (obj := fun _ => η) (obj' := fun _ => η)
        (fun _ _ => φ) q (i₁ := ()) (i₂ := ()) f₁ f₂ hf₁ hf₂ =
      (pullbackFiberCompIso' η (pullback.fst c c) (pullback.lift f₁ f₂ (hf₁.trans hf₂.symm))
          f₁ (pullback.lift_fst _ _ _)).inv ≫
        pullbackFiberHom φ (pullback.lift f₁ f₂ (hf₁.trans hf₂.symm)) ≫
        (pullbackFiberCompIso' η (pullback.snd c c) (pullback.lift f₁ f₂ (hf₁.trans hf₂.symm))
          f₂ (pullback.lift_snd _ _ _)).hom :=
  (DescentData'.pullHom'_eq_pullHom (F := pullbackPseudofunctor p) (f := fun _ : Unit => c)
    (sq := fun _ _ => singleChosenPullback c) (obj := fun _ => η) (obj' := fun _ => η)
    (fun _ _ => φ) q f₁ f₂ (pullback.lift f₁ f₂ (hf₁.trans hf₂.symm)) hf₁ hf₂
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans
    (pullHom_eq' p η η _ _ φ _ f₁ f₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))

/-- **Effective descent along one covering morphism, in the total category.** Let `η` lie over
`V`, and let `d₁, d₂ : P ⟶ η` lie over the two projections of `V ×_U V`, with `d₁` strongly
cartesian. Suppose that the pair `(d₁, d₂)` is reflexive — a morphism into `P` over the diagonal
which `d₁` sends to `u` is sent to `u` by `d₂` as well — and transitive over `V ×_U V ×_U V`. Then
`η` descends: there is an object `y` over `U` and a strongly cartesian morphism `η ⟶ y` over `c`
which coequalizes `d₁` and `d₂`. -/
theorem exists_descent_of_mem_singleton_sieve (η : p.Fiber V) {P : 𝒳} (d₁ d₂ : P ⟶ η.1)
    [p.IsStronglyCartesian (pullback.fst c c) d₁] [p.IsHomLift (pullback.snd c c) d₂]
    (hrefl : ∀ {A : 𝒳} (ℓ : V ⟶ pullback c c), ℓ ≫ pullback.fst c c = 𝟙 V →
      ℓ ≫ pullback.snd c c = 𝟙 V → ∀ (s : A ⟶ P) (u : A ⟶ η.1), p.IsHomLift ℓ s →
        s ≫ d₁ = u → s ≫ d₂ = u)
    (htrans : ∀ {A : 𝒳} (ℓ : pullback (pullback.snd c c) (pullback.fst c c) ⟶ pullback c c),
      ℓ ≫ pullback.fst c c = pullback.fst (pullback.snd c c) (pullback.fst c c) ≫ pullback.fst c c →
      ℓ ≫ pullback.snd c c = pullback.snd (pullback.snd c c) (pullback.fst c c) ≫ pullback.snd c c →
      ∀ (m m' m'' : A ⟶ P), p.IsHomLift (pullback.fst (pullback.snd c c) (pullback.fst c c)) m →
        p.IsHomLift (pullback.snd (pullback.snd c c) (pullback.fst c c)) m' →
        p.IsHomLift ℓ m'' → m ≫ d₂ = m' ≫ d₁ → m'' ≫ d₁ = m ≫ d₁ → m'' ≫ d₂ = m' ≫ d₂) :
    ∃ (y : p.Fiber U) (ζ : η.1 ⟶ y.1), p.IsStronglyCartesian c ζ ∧ d₁ ≫ ζ = d₂ ≫ ζ := by
  -- the gluing morphism in the fibre over `V ×_U V`
  let j : (pullbackFiber p η (pullback.fst c c)).1 ⟶ P :=
    (IsCartesian.domainUniqueUpToIso p (pullback.fst c c) d₁
      (IsPreFibered.pullbackMap η.2 (pullback.fst c c))).hom
  have hj : j ≫ d₁ = IsPreFibered.pullbackMap η.2 (pullback.fst c c) :=
    IsCartesian.fac p (pullback.fst c c) d₁ _
  have : IsIso j := inferInstance
  have : p.IsHomLift (𝟙 (pullback c c)) j := inferInstance
  have hjd₂ : p.IsHomLift (pullback.snd c c) (j ≫ d₂) := inferInstance
  obtain ⟨φ, hφ⟩ := exists_fiberInclusion_map_comp_eq p (pullbackFiber p η (pullback.fst c c))
    η (pullback.snd c c) (j ≫ d₂) hjd₂
  -- the base change of `φ` along `ℓ`, conjugated by the contractions, and the lifts it is
  -- compared with
  have step : ∀ {Y : 𝒮} (ℓ : Y ⟶ pullback c c) (g₁ g₂ : Y ⟶ V) (h₁ : ℓ ≫ pullback.fst c c = g₁)
      (h₂ : ℓ ≫ pullback.snd c c = g₂),
      ∃ (A : pullbackFiber p η g₁ ⟶ pullbackFiber p η g₂)
        (κ : (pullbackFiber p η g₁).1 ⟶ (pullbackFiber p η (pullback.fst c c)).1),
      A = (pullbackFiberCompIso' η (pullback.fst c c) ℓ g₁ h₁).inv ≫ pullbackFiberHom φ ℓ ≫
        (pullbackFiberCompIso' η (pullback.snd c c) ℓ g₂ h₂).hom ∧
      p.IsHomLift ℓ κ ∧ κ ≫ IsPreFibered.pullbackMap η.2 (pullback.fst c c) =
        IsPreFibered.pullbackMap η.2 g₁ ∧
      Fiber.fiberInclusion.map A ≫ IsPreFibered.pullbackMap η.2 g₂ = κ ≫ j ≫ d₂ := by
    intro Y ℓ g₁ g₂ h₁ h₂
    have hκ := IsStronglyCartesian.fac p (pullback.fst c c)
      (IsPreFibered.pullbackMap η.2 (pullback.fst c c)) (f' := g₁) (g := ℓ) h₁.symm
      (IsPreFibered.pullbackMap η.2 g₁)
    refine ⟨_, _, rfl, inferInstance, hκ, ?_⟩
    rw [← hφ]
    exact fiberInclusion_map_pullbackFiberHom_conj_comp p φ ℓ g₁ g₂ h₁ h₂ _ inferInstance hκ
  let D : SingleDescentData p c :=
    { obj := fun _ => η
      hom := fun _ _ => φ
      pullHom'_hom_self := fun _ => by
        refine (pullHom'_single_eq (p := p) c η φ c (𝟙 V) (𝟙 V) (Category.id_comp c)
          (Category.id_comp c)).trans ?_
        obtain ⟨A, κ, rfl, hκ, hκ', hκφ⟩ := step (pullback.lift (𝟙 V) (𝟙 V) rfl) (𝟙 V) (𝟙 V)
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        refine fiber_hom_ext_of_cartesian (𝟙 V) (IsPreFibered.pullbackMap η.2 (𝟙 V))
          inferInstance _ _ ?_
        rw [hκφ]
        exact ((Category.assoc _ _ _).symm.trans (hrefl (pullback.lift (𝟙 V) (𝟙 V) rfl)
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (κ ≫ j) _ inferInstance
          (by rw [Category.assoc, hj, hκ']))).trans (Category.id_comp _).symm
      pullHom'_hom_comp := fun _ _ _ => by
        let W := pullback (pullback.snd c c) (pullback.fst c c)
        let q₁ : W ⟶ V := pullback.fst _ _ ≫ pullback.fst c c
        let q₂ : W ⟶ V := pullback.fst _ _ ≫ pullback.snd c c
        let q₃ : W ⟶ V := pullback.snd _ _ ≫ pullback.snd c c
        let qq : W ⟶ U := pullback.fst (pullback.snd c c) (pullback.fst c c) ≫
          (pullback.fst c c ≫ c)
        have h₁ : q₁ ≫ c = qq := Category.assoc _ _ _
        have h₂ : q₂ ≫ c = qq := by simp only [q₂, qq, Category.assoc, pullback.condition (f := c)]
        have h₃ : q₃ ≫ c = qq := by
          simp only [q₃, qq, Category.assoc]
          rw [← pullback.condition (f := c), ← pullback.condition_assoc (f := pullback.snd c c),
            pullback.condition (f := c)]
        have e₁₂ := pullHom'_single_eq (p := p) c η φ qq q₁ q₂ h₁ h₂
        have e₂₃ := pullHom'_single_eq (p := p) c η φ qq q₂ q₃ h₂ h₃
        have e₁₃ := pullHom'_single_eq (p := p) c η φ qq q₁ q₃ h₁ h₃
        refine Eq.trans (congrArg₂ (· ≫ ·) e₁₂ e₂₃) (Eq.trans ?_ e₁₃.symm)
        obtain ⟨A₁₂, κ₁₂, hA₁₂, hκ₁₂, hκ₁₂', c₁₂⟩ :=
          step (pullback.lift q₁ q₂ (h₁.trans h₂.symm)) q₁ q₂
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        obtain ⟨A₂₃, κ₂₃, hA₂₃, hκ₂₃, hκ₂₃', c₂₃⟩ :=
          step (pullback.lift q₂ q₃ (h₂.trans h₃.symm)) q₂ q₃
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        obtain ⟨A₁₃, κ₁₃, hA₁₃, hκ₁₃, hκ₁₃', c₁₃⟩ :=
          step (pullback.lift q₁ q₃ (h₁.trans h₃.symm)) q₁ q₃
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        have l₁₂ : pullback.lift q₁ q₂ (h₁.trans h₂.symm) =
            pullback.fst (pullback.snd c c) (pullback.fst c c) :=
          pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        have l₂₃ : pullback.lift q₂ q₃ (h₂.trans h₃.symm) =
            pullback.snd (pullback.snd c c) (pullback.fst c c) :=
          pullback.hom_ext ((pullback.lift_fst _ _ _).trans pullback.condition)
            (pullback.lift_snd _ _ _)
        have hκ₁₂f : p.IsHomLift (pullback.fst (pullback.snd c c) (pullback.fst c c)) κ₁₂ :=
          l₁₂ ▸ hκ₁₂
        have hκ₂₃f : p.IsHomLift (pullback.snd (pullback.snd c c) (pullback.fst c c)) κ₂₃ :=
          l₂₃ ▸ hκ₂₃
        have key := htrans (pullback.lift q₁ q₃ (h₁.trans h₃.symm))
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (κ₁₂ ≫ j)
          (Fiber.fiberInclusion.map A₁₂ ≫ κ₂₃ ≫ j) (κ₁₃ ≫ j) inferInstance inferInstance
          inferInstance (by
            rw [Category.assoc, Category.assoc, Category.assoc, hj, hκ₂₃', ← c₁₂])
          (by rw [Category.assoc, Category.assoc, hj, hκ₁₃', hκ₁₂'])
        rw [← hA₁₂, ← hA₂₃, ← hA₁₃]
        change A₁₂ ≫ A₂₃ = A₁₃
        refine fiber_hom_ext_of_cartesian q₃ (IsPreFibered.pullbackMap η.2 q₃)
          (IsPreFibered.pullbackMap.IsCartesian η.2 q₃) _ _ ?_
        rw [Functor.map_comp, Category.assoc, c₂₃, c₁₃]
        simpa only [Category.assoc] using key.symm }
  obtain ⟨y, ζ, hζ, hζ'⟩ := exists_descends_of_mem_singleton_sieve c hp hc D
  have hζ'' : IsPreFibered.pullbackMap η.2 (pullback.fst c c) ≫ ζ =
      (Fiber.fiberInclusion.map φ ≫ IsPreFibered.pullbackMap η.2 (pullback.snd c c)) ≫ ζ := hζ'
  refine ⟨y, ζ, hζ, ?_⟩
  rw [← cancel_epi j, reassoc_of% hj, hζ'', Category.assoc, reassoc_of% hφ]

end SingleMorphism

end CategoryTheory.Functor
