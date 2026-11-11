module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardFiber

/-!
# Effective descent for a pushforward of a fibred category

Let `u : 𝒞 ⥤ 𝒟` be a continuous functor of sites and `p : 𝒮 ⥤ 𝒟` a stack. This file proves
condition (3) of Stacks 026F for the pushforward `u^p𝒮 ⥤ 𝒞`: descent along a covering sieve of `𝒞`
is effective.

A descent datum for `u^p𝒮` relative to a covering sieve `R` of `U` is transported to a descent
datum for `p` relative to the pushforward of `R` to `𝒟`, which is a covering sieve because `u` is
continuous. Two things have to be checked of the transported datum, and both are where the work of
this file lies.

* Its gluing isomorphisms have to be *defined* over every object of `𝒟` mapping compatibly into the
  images of two sources, whereas the given datum supplies them only over objects of `𝒞`. This is
  where `u` has to commute with the fibre product `V₁ ×_U V₂`: the pair of morphisms out of `Y`
  factors through `u (V₁ ×_U V₂)`, and the isomorphism over `Y` is the base change of the given
  one. That is `CategoryTheory.StrictPullback.glue`.
* Its cocycle condition and its compatibility with base change have to be proved. The first is the
  cocycle condition of the given datum over the *triple* fibre product `V₁ ×_U V₂ ×_U V₃`, to which
  the three binary gluing isomorphisms are base changed using the base-change compatibility of the
  given datum: `CategoryTheory.StrictPullback.glue_cocycle`, whose engine is
  `CategoryTheory.StrictPullback.core_refine`, saying that `glue` does not depend on the object of
  `𝒞` used to compare the two arrows. The second is `CategoryTheory.StrictPullback.glue_pullback`.

Both steps are stated for `CategoryTheory.StrictPullback.core`, the transported gluing isomorphism
computed over a *given* object of `𝒞`; `glue` is the case of the fibre product.

Throughout, taking chosen pullbacks does not commute with passing from `u^p𝒮` to `𝒮` on the nose,
only up to `CategoryTheory.StrictPullback.fiberFibPullbackIso`, and the bookkeeping of that
comparison — `CategoryTheory.StrictPullback.fiberCmp` and its four compatibilities — is what the
first half of the file is.

## Main definitions

* `CategoryTheory.StrictPullback.fiberCmp`, the comparison of the chosen pullback of an object of
  `𝒮` underlying an object of `u^p𝒮` with the object underlying a chosen pullback;
* `CategoryTheory.StrictPullback.core` and `CategoryTheory.StrictPullback.glue`, the transported
  gluing isomorphisms;
* `CategoryTheory.StrictPullback.pushforwardDatum`, the transported descent datum;
* `CategoryTheory.StrictPullback.PreservesBaseChanges`,
  `CategoryTheory.StrictPullback.glueOfPreservesBaseChanges` and
  `CategoryTheory.StrictPullback.pushforwardDatumThrough`, the same along a covering with fibre
  products, for a base with no other fibre products.

## Main results

* `CategoryTheory.StrictPullback.glue_cocycle` and
  `CategoryTheory.StrictPullback.glue_pullback`, the two conditions on the transported gluing
  isomorphisms;
* `CategoryTheory.StrictPullback.hasEffectiveDescent_structureFunctor`, condition (3) of
  Stacks 026F for the pushforward, over a base with all fibre products preserved by `u`;
* `CategoryTheory.StrictPullback.isEffective_of_preservesBaseChanges`, effectivity of a descent
  datum relative to a sieve containing a covering whose fibre products with arbitrary morphisms
  exist and are preserved by `u`, which is what Stacks 00VH and 00WU provide.
-/

@[expose] public section

namespace CategoryTheory

open Limits

-- As in `StacksFrontier.CategoryTheory.Sites.Descent.IsStack`: the instance arguments of
-- `IsHomLift`
-- and `IsCartesian` are only found after unfolding the chosen pullbacks.
set_option backward.isDefEq.respectTransparency false

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Functor

variable {𝒴 : Type u₄} [Category.{v₄} 𝒴] {𝒳 : Type u₅} [Category.{v₅} 𝒳] {P : 𝒳 ⥤ 𝒴}

end Functor

namespace StrictPullback

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {u : 𝒞 ⥤ 𝒟} {p : 𝒮 ⥤ 𝒟}

/-! ### Transport of a descent datum across the strict pullback -/

/-- A factorization of an arrow of the pushforward `R.functorPushforward u` of a sieve `R` through
the image of an arrow of `R`. -/
structure Factorization (u : 𝒞 ⥤ 𝒟) {U : 𝒞} (R : Sieve U) {Y : 𝒟} (h : Y ⟶ u.obj U) where
  /-- The source of the arrow of `R`. -/
  src : 𝒞
  /-- The arrow of `R`. -/
  arrow : src ⟶ U
  /-- The arrow belongs to `R`. -/
  mem : R arrow
  /-- The morphism of `𝒟` through which `h` factors. -/
  lift : Y ⟶ u.obj src
  /-- The factorization itself. -/
  fac : h = lift ≫ u.map arrow

/-- Every arrow of `R.functorPushforward u` factors through the image of an arrow of `R`. -/
lemma nonempty_factorization {U : 𝒞} {R : Sieve U} {Y : 𝒟} {h : Y ⟶ u.obj U}
    (hh : (R.functorPushforward u) h) : Nonempty (Factorization u R h) := by
  obtain ⟨V, f, a, hf, hfac⟩ := hh
  exact ⟨V, f, hf, a, hfac⟩

/-- A choice of factorization of an arrow of `R.functorPushforward u`. -/
noncomputable def factorization {U : 𝒞} {R : Sieve U} {Y : 𝒟} {h : Y ⟶ u.obj U}
    (hh : (R.functorPushforward u) h) : Factorization u R h :=
  Classical.choice (nonempty_factorization hh)

/-! ### The two chosen pullbacks of an object of a fibre of the pushforward

An object `y` of the fibre of `u^p𝒮` over `V` has an underlying object `fiberFib y` of the fibre of
`p` over `u V`, and taking chosen pullbacks commutes with that only up to a canonical isomorphism:
for `c : Z ⟶ V` in `𝒞` and `t : Y ⟶ u Z` in `𝒟` with `t ≫ u c = b`, both `b^* (fiberFib y)` and
`t^* (fiberFib (c^* y))` carry a cartesian morphism over `b` to `fiberFib y`, so they are
canonically isomorphic in the fibre of `p` over `Y`
(`CategoryTheory.StrictPullback.fiberCmp`). Every identity below is proved from the factorizations
of these canonical comparisons through the chosen cartesian lifts they compare, by
`CategoryTheory.Functor.fiber_hom_ext_of_cartesian`. -/

/-- The inclusion of the fibre of `u^p𝒮` over `U` into the fibre of `p` over `u U`, on objects
`CategoryTheory.StrictPullback.fiberFib`: an object of `u^p𝒮` over `U` *is* an object of `𝒮` over
`u U`, and a morphism over `𝟙 U` *is* a morphism over `𝟙 (u U)`. -/
@[implicit_reducible]
def fiberFibFunctor (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒟) (U : 𝒞) :
    (structureFunctor u p).Fiber U ⥤ p.Fiber (u.obj U) where
  obj y := fiberFib y
  map φ := ⟨(Functor.Fiber.fiberInclusion.map φ).fib, isHomLift_id_fib _ φ.2⟩
  map_id _ := Functor.Fiber.hom_ext rfl
  map_comp _ _ := Functor.Fiber.hom_ext rfl

/-- `StrictPullback.fiberFibFunctor` acts on a morphism of the fibre of `u^p𝒮` over `U` by taking
the `𝒮`-component of the underlying morphism of `u^p𝒮`. -/
@[simp]
lemma fiberInclusion_map_fiberFibFunctor_map {U : 𝒞} {x y : (structureFunctor u p).Fiber U}
    (φ : x ⟶ y) :
    Functor.Fiber.fiberInclusion.map ((fiberFibFunctor u p U).map φ) =
      (Functor.Fiber.fiberInclusion.map φ).fib := rfl

/-- `StrictPullback.fiberFibFunctor` acts on objects by `StrictPullback.fiberFib`. -/
@[simp]
lemma fiberFibFunctor_obj {U : 𝒞} (y : (structureFunctor u p).Fiber U) :
    (fiberFibFunctor u p U).obj y = fiberFib y := rfl

/-- The `𝒮`-components of the two directions of an isomorphism of a fibre of `u^p𝒮` are inverse to
one another. -/
@[reassoc (attr := simp)]
lemma fiberInclusion_hom_inv_id_fib {W : 𝒞} {x y : (structureFunctor u p).Fiber W} (e : x ≅ y) :
    (Functor.Fiber.fiberInclusion.map e.hom).fib ≫ (Functor.Fiber.fiberInclusion.map e.inv).fib =
      𝟙 _ := by
  rw [← comp_fib, ← Functor.map_comp, e.hom_inv_id, Functor.map_id, id_fib]

/-- `StrictPullback.fiberInclusion_hom_inv_id_fib` in the other order. -/
@[reassoc (attr := simp)]
lemma fiberInclusion_inv_hom_id_fib {W : 𝒞} {x y : (structureFunctor u p).Fiber W} (e : x ≅ y) :
    (Functor.Fiber.fiberInclusion.map e.inv).fib ≫ (Functor.Fiber.fiberInclusion.map e.hom).fib =
      𝟙 _ := by
  rw [← comp_fib, ← Functor.map_comp, e.inv_hom_id, Functor.map_id, id_fib]

section Descent

variable [p.IsFibered]

/-- The chosen pullback along `t` of the object underlying `c^* y`, together with its cartesian
morphism to `fiberFib y` over `b = t ≫ u c`. -/
lemma isCartesian_pullbackMap_comp_fib {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) :
    p.IsCartesian b
      (Functor.IsPreFibered.pullbackMap
          (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)).2 t ≫
        (Functor.IsPreFibered.pullbackMap y.2 c).fib) := by
  have := isStronglyCartesian_pullbackMap_fib y c
  have : p.IsCartesian t (Functor.IsPreFibered.pullbackMap
      (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)).2 t) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  have h0 : p.IsCartesian (t ≫ u.map c)
      (Functor.IsPreFibered.pullbackMap
          (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)).2 t ≫
        (Functor.IsPreFibered.pullbackMap y.2 c).fib) := inferInstance
  rwa [h] at h0

/-- The canonical isomorphism `b^* (fiberFib y) ≅ t^* (fiberFib (c^* y))` of the fibre of `p` over
`Y`, for `b = t ≫ u c`. -/
noncomputable def fiberCmp {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) :
    Functor.pullbackFiber p (fiberFib y) b ≅
      Functor.pullbackFiber p (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)) t :=
  Functor.fiberIsoOfCartesian b (Functor.IsPreFibered.pullbackMap (fiberFib y).2 b) _
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
    (isCartesian_pullbackMap_comp_fib y c t b h)

/-- `StrictPullback.fiberCmp` factors the chosen cartesian lift of `b` through the composite of the
chosen cartesian lift of `t` with the `𝒮`-component of the chosen cartesian lift of `c`. -/
@[reassoc (attr := simp)]
lemma fiberCmp_hom_fac {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) :
    Functor.Fiber.fiberInclusion.map (fiberCmp y c t b h).hom ≫
        Functor.IsPreFibered.pullbackMap
            (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)).2 t ≫
          (Functor.IsPreFibered.pullbackMap y.2 c).fib =
      Functor.IsPreFibered.pullbackMap (fiberFib y).2 b :=
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- `StrictPullback.fiberCmp_hom_fac` in the other direction: the inverse of the comparison factors
the composite of the two chosen cartesian lifts through the chosen cartesian lift of `b`. -/
@[reassoc (attr := simp)]
lemma fiberCmp_inv_fac {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) :
    Functor.Fiber.fiberInclusion.map (fiberCmp y c t b h).inv ≫
        Functor.IsPreFibered.pullbackMap (fiberFib y).2 b =
      Functor.IsPreFibered.pullbackMap
          (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)).2 t ≫
        (Functor.IsPreFibered.pullbackMap y.2 c).fib :=
  Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- The comparison is natural: base changing a morphism of a fibre of `u^p𝒮` and passing to `𝒮`
commute with it. -/
@[reassoc]
lemma fiberCmp_naturality {V Z : 𝒞} {y y' : (structureFunctor u p).Fiber V} (α : y ⟶ y')
    (c : Z ⟶ V) {Y : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) :
    Functor.pullbackFiberHom ((fiberFibFunctor u p V).map α) b ≫ (fiberCmp y' c t b h).hom =
      (fiberCmp y c t b h).hom ≫
        Functor.pullbackFiberHom
          ((fiberFibFunctor u p Z).map (Functor.pullbackFiberHom α c)) t := by
  refine Functor.fiber_hom_ext_of_cartesian b _
    (isCartesian_pullbackMap_comp_fib y' c t b h) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberCmp_hom_fac,
    Functor.pullbackFiberHom_fac, Functor.pullbackFiberHom_fac_assoc,
    fiberInclusion_map_fiberFibFunctor_map, ← comp_fib, Functor.pullbackFiberHom_fac]
  rw [comp_fib, fiberCmp_hom_fac_assoc]

/-- The comparison for a composite in `𝒞` is the composite of the comparisons, after contracting
the iterated chosen pullback inside `u^p𝒮`. -/
@[reassoc]
lemma fiberCmp_comp {V Z Z' : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V) (k : Z' ⟶ Z)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (t' : Y ⟶ u.obj Z') (b : Y ⟶ u.obj V) (hk : t' ≫ u.map k = t)
    (h : t ≫ u.map c = b) (h' : t' ≫ u.map (k ≫ c) = b) :
    (fiberCmp y (k ≫ c) t' b h').hom =
      (fiberCmp y c t b h).hom ≫
        (fiberCmp (Functor.pullbackFiber (structureFunctor u p) y c) k t' t hk).hom ≫
        Functor.pullbackFiberHom
          ((fiberFibFunctor u p Z').map (Functor.pullbackFiberCompIso y c k).hom) t' := by
  refine Functor.fiber_hom_ext_of_cartesian b _
    (isCartesian_pullbackMap_comp_fib y (k ≫ c) t' b h') _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberCmp_hom_fac,
    Functor.pullbackFiberHom_fac_assoc, fiberInclusion_map_fiberFibFunctor_map, ← comp_fib,
    Functor.pullbackFiberCompIso_hom_fac]
  rw [comp_fib]
  simp [fiberCmp_hom_fac_assoc, fiberCmp_hom_fac]

/-- The comparison is compatible with base change in `𝒟`. -/
@[reassoc]
lemma fiberCmp_pullback {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V)
    {Y Y' : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) (γ : Y' ⟶ Y) :
    (fiberCmp y c (γ ≫ t) (γ ≫ b) (by rw [Category.assoc, h])).hom =
      (Functor.pullbackFiberCompIso (fiberFib y) b γ).inv ≫
        Functor.pullbackFiberHom (fiberCmp y c t b h).hom γ ≫
        (Functor.pullbackFiberCompIso
          (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)) t γ).hom := by
  refine Functor.fiber_hom_ext_of_cartesian (γ ≫ b) _
    (isCartesian_pullbackMap_comp_fib y c (γ ≫ t) (γ ≫ b) (by rw [Category.assoc, h])) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberCmp_hom_fac,
    Functor.pullbackFiberCompIso_hom_fac_assoc, Functor.pullbackFiberHom_fac_assoc]
  rw [Functor.pullbackFiberCompIso_inv_fac]

/-- `fiberCmp_pullback` as an equality of isomorphisms. -/
lemma fiberCmp_pullback_iso {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V)
    {Y Y' : 𝒟} (t : Y ⟶ u.obj Z) (b : Y ⟶ u.obj V) (h : t ≫ u.map c = b) (γ : Y' ⟶ Y) :
    fiberCmp y c (γ ≫ t) (γ ≫ b) (by rw [Category.assoc, h]) =
      (Functor.pullbackFiberCompIso (fiberFib y) b γ).symm ≪≫
        Functor.pullbackFiberIso (fiberCmp y c t b h) γ ≪≫
        Functor.pullbackFiberCompIso
          (fiberFib (Functor.pullbackFiber (structureFunctor u p) y c)) t γ :=
  Iso.ext (by simpa using fiberCmp_pullback y c t b h γ)

/-- `fiberCmp` at the identity is `fiberFibPullbackIso`, after contracting the chosen pullback
along the identity. -/
lemma fiberCmp_id {V Z : 𝒞} (y : (structureFunctor u p).Fiber V) (c : Z ⟶ V) :
    fiberCmp y c (𝟙 (u.obj Z)) (u.map c) (Category.id_comp _) ≪≫
        Functor.pullbackFiberIdIso _ = fiberFibPullbackIso y c := by
  have := isStronglyCartesian_pullbackMap_fib y c
  refine Iso.ext (Functor.fiber_hom_ext_of_cartesian (u.map c)
    ((Functor.IsPreFibered.pullbackMap y.2 c).fib) inferInstance _ _ ?_)
  simp [Iso.trans_hom, Functor.map_comp, Category.assoc, fiberFibPullbackIso_hom_fac,
    Functor.pullbackFiberIdIso_hom_fac, fiberCmp_hom_fac]

omit [p.IsFibered] in
/-- A morphism of `u^p𝒮` is determined by its `𝒮`-component together with the morphism of `𝒞` it
lies over. -/
lemma hom_ext_of_fib {V W : 𝒞} {X Y : StrictPullback u p} (a : V ⟶ W) (φ ψ : X ⟶ Y)
    (hφ : (structureFunctor u p).IsHomLift a φ) (hψ : (structureFunctor u p).IsHomLift a ψ)
    (h : φ.fib = ψ.fib) : φ = ψ := by
  have := hφ
  have := hψ
  have h1 : X.base = V := IsHomLift.domain_eq (structureFunctor u p) a φ
  have h2 : Y.base = W := IsHomLift.codomain_eq (structureFunctor u p) a φ
  subst h1 h2
  exact Hom.ext ((base_eq a φ).trans (base_eq a ψ).symm) h

/-! ### The transported gluing isomorphisms -/

section Datum

variable {U : 𝒞} {R : Sieve U} (D : Functor.SieveDescentDatum (structureFunctor u p) R)

/-- The gluing isomorphism of a descent datum for `u^p𝒮`, transported to `𝒮`: for two arrows `f₁`,
`f₂` of the sieve, an object `Z` of `𝒞` mapping to both their sources compatibly over `U`, and a
morphism `t` of `𝒟` into `u Z`, the chosen pullbacks along `bᵢ = t ≫ u cᵢ` of the two objects the
datum attaches are isomorphic in the fibre of `p` over `Y`. -/
noncomputable def core {V₁ V₂ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) {Y : 𝒟} (t : Y ⟶ u.obj Z)
    (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (h₁ : t ≫ u.map c₁ = b₁) (h₂ : t ≫ u.map c₂ = b₂) :
    Functor.pullbackFiber p (fiberFib (D.obj f₁ hf₁)) b₁ ≅
      Functor.pullbackFiber p (fiberFib (D.obj f₂ hf₂)) b₂ :=
  fiberCmp (D.obj f₁ hf₁) c₁ t b₁ h₁ ≪≫
    Functor.pullbackFiberIso ((fiberFibFunctor u p Z).mapIso (D.iso hf₁ hf₂ c₁ c₂ hc)) t ≪≫
    (fiberCmp (D.obj f₂ hf₂) c₂ t b₂ h₂).symm

/-- `core` is pinned down by its composite with the chosen cartesian lift of `b₂`: that composite
is built from the comparison at `f₁` and the gluing isomorphism of the datum. -/
@[reassoc]
lemma core_fac {V₁ V₂ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) {Y : 𝒟} (t : Y ⟶ u.obj Z)
    (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (h₁ : t ≫ u.map c₁ = b₁) (h₂ : t ≫ u.map c₂ = b₂) :
    Functor.Fiber.fiberInclusion.map (core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂).hom ≫
        Functor.IsPreFibered.pullbackMap (fiberFib (D.obj f₂ hf₂)).2 b₂ =
      Functor.Fiber.fiberInclusion.map (fiberCmp (D.obj f₁ hf₁) c₁ t b₁ h₁).hom ≫
        Functor.IsPreFibered.pullbackMap
            (fiberFib (Functor.pullbackFiber (structureFunctor u p) (D.obj f₁ hf₁) c₁)).2 t ≫
          (Functor.Fiber.fiberInclusion.map (D.iso hf₁ hf₂ c₁ c₂ hc).hom).fib ≫
          (Functor.IsPreFibered.pullbackMap (D.obj f₂ hf₂).2 c₂).fib := by
  simp [core, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    fiberCmp_inv_fac, Functor.pullbackFiberIso_hom, Functor.mapIso_hom,
    Functor.pullbackFiberHom_fac_assoc, fiberInclusion_map_fiberFibFunctor_map]

/-- The cocycle condition for `core`, at three arrows compared over one and the same object of `𝒞`:
it is the cocycle condition of the datum, conjugated by the comparisons. -/
lemma core_cocycle {V₁ V₂ V₃ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    {f₃ : V₃ ⟶ U} (hf₃ : R f₃) (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (c₃ : Z ⟶ V₃)
    (h₁₂ : c₁ ≫ f₁ = c₂ ≫ f₂) (h₂₃ : c₂ ≫ f₂ = c₃ ≫ f₃) (h₁₃ : c₁ ≫ f₁ = c₃ ≫ f₃)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (b₃ : Y ⟶ u.obj V₃)
    (hb₁ : t ≫ u.map c₁ = b₁) (hb₂ : t ≫ u.map c₂ = b₂) (hb₃ : t ≫ u.map c₃ = b₃) :
    (core D hf₁ hf₂ c₁ c₂ h₁₂ t b₁ b₂ hb₁ hb₂).hom ≫
        (core D hf₂ hf₃ c₂ c₃ h₂₃ t b₂ b₃ hb₂ hb₃).hom =
      (core D hf₁ hf₃ c₁ c₃ h₁₃ t b₁ b₃ hb₁ hb₃).hom := by
  simp only [core, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.pullbackFiberIso_hom, Functor.mapIso_hom]
  rw [← Functor.pullbackFiberHom_comp_assoc, ← Functor.map_comp,
    D.cocycle hf₁ hf₂ hf₃ c₁ c₂ c₃ h₁₂ h₂₃ h₁₃]

/-- `core` does not depend on the object of `𝒞` chosen to compare the two arrows over: refining
that
object along `k` leaves it unchanged. This is the one place the base-change compatibility of the
datum is used. -/
lemma core_refine {V₁ V₂ Z Z' : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) (k : Z' ⟶ Z)
    {Y : 𝒟} (t : Y ⟶ u.obj Z) (t' : Y ⟶ u.obj Z') (hk : t' ≫ u.map k = t)
    (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (h₁ : t ≫ u.map c₁ = b₁) (h₂ : t ≫ u.map c₂ = b₂)
    (h₁' : t' ≫ u.map (k ≫ c₁) = b₁) (h₂' : t' ≫ u.map (k ≫ c₂) = b₂) :
    core D hf₁ hf₂ (k ≫ c₁) (k ≫ c₂)
        (by rw [Category.assoc, Category.assoc, hc]) t' b₁ b₂ h₁' h₂' =
      core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂ := by
  refine Iso.ext (Functor.fiber_hom_ext_of_cartesian b₂
    (Functor.IsPreFibered.pullbackMap (fiberFib (D.obj f₂ hf₂)).2 b₂)
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_)
  rw [core_fac, core_fac, ← D.iso_pullback hf₁ hf₂ c₁ c₂ hc k,
    fiberCmp_comp (D.obj f₁ hf₁) c₁ k t t' b₁ hk h₁ h₁']
  simp only [Functor.map_comp, Category.assoc, Functor.pullbackFiberIso_hom,
    fiberInclusion_map_fiberFibFunctor_map, Functor.pullbackFiberHom_fac_assoc,
    fiberFibFunctor_obj, ← comp_fib, Functor.pullbackFiberCompIso_hom_fac]
  simp

/-- `core` is compatible with base change in `𝒟`. -/
lemma core_pullback {V₁ V₂ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) {Y Y' : 𝒟} (t : Y ⟶ u.obj Z)
    (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (h₁ : t ≫ u.map c₁ = b₁) (h₂ : t ≫ u.map c₂ = b₂)
    (γ : Y' ⟶ Y) :
    (core D hf₁ hf₂ c₁ c₂ hc (γ ≫ t) (γ ≫ b₁) (γ ≫ b₂)
        (by rw [Category.assoc, h₁]) (by rw [Category.assoc, h₂])).hom =
      (Functor.pullbackFiberCompIso (fiberFib (D.obj f₁ hf₁)) b₁ γ).inv ≫
        Functor.pullbackFiberHom (core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂).hom γ ≫
        (Functor.pullbackFiberCompIso (fiberFib (D.obj f₂ hf₂)) b₂ γ).hom := by
  simp only [core, fiberCmp_pullback_iso (D.obj f₁ hf₁) c₁ t b₁ h₁ γ,
    fiberCmp_pullback_iso (D.obj f₂ hf₂) c₂ t b₂ h₂ γ, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Category.assoc, fiberFibFunctor_obj, Functor.pullbackFiberIso_hom,
    Functor.pullbackFiberIso_inv, Functor.mapIso_hom, Functor.pullbackFiberHom_comp,
    Functor.pullbackFiberHom_comp_base _ t γ]
  simp [Iso.hom_inv_id_assoc]

/-- `core_refine` with the refined pair of morphisms named. -/
lemma core_refine' {V₁ V₂ Z Z' : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) (k : Z' ⟶ Z)
    (c₁' : Z' ⟶ V₁) (c₂' : Z' ⟶ V₂) (hk₁ : k ≫ c₁ = c₁') (hk₂ : k ≫ c₂ = c₂')
    (hc' : c₁' ≫ f₁ = c₂' ≫ f₂) {Y : 𝒟} (t : Y ⟶ u.obj Z) (t' : Y ⟶ u.obj Z')
    (hk : t' ≫ u.map k = t) (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂)
    (h₁ : t ≫ u.map c₁ = b₁) (h₂ : t ≫ u.map c₂ = b₂)
    (h₁' : t' ≫ u.map c₁' = b₁) (h₂' : t' ≫ u.map c₂' = b₂) :
    core D hf₁ hf₂ c₁' c₂' hc' t' b₁ b₂ h₁' h₂' = core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂ := by
  subst hk₁; subst hk₂
  exact core_refine D hf₁ hf₂ c₁ c₂ hc k t t' hk b₁ b₂ h₁ h₂ h₁' h₂'

end Datum

section Glue

variable [HasPullbacks 𝒞] [PreservesLimitsOfShape WalkingCospan u]
  {U : 𝒞} {R : Sieve U} (D : Functor.SieveDescentDatum (structureFunctor u p) R)

omit [HasPullbacks 𝒞] in
/-- `u` commutes with the fibre product of two morphisms of `𝒞`. This is the assumption on `u` that
Stacks 00WU makes over and above continuity, and the only place it is used. -/
lemma isPullback_map_pullback (u : 𝒞 ⥤ 𝒟) [PreservesLimitsOfShape WalkingCospan u]
    {V₁ V₂ W : 𝒞} (f₁ : V₁ ⟶ W) (f₂ : V₂ ⟶ W) [HasPullback f₁ f₂] :
    IsPullback (u.map (pullback.fst f₁ f₂)) (u.map (pullback.snd f₁ f₂)) (u.map f₁) (u.map f₂) :=
  (IsPullback.of_hasPullback f₁ f₂).map u

/-- The gluing isomorphism of a descent datum for `u^p𝒮`, transported to `𝒮`: for two arrows `f₁`,
`f₂` of the sieve and two morphisms `b₁`, `b₂` of `𝒟` into the images of their sources agreeing
over
`u U`, the chosen pullbacks of the two attached objects are isomorphic in the fibre of `p` over
`Y`.

This is the step of the proof of Stacks 04WC at which `u` has to commute with the fibre product
`V₁ ×_U V₂`: the datum supplies gluing isomorphisms only over objects of `𝒞`, and the pair
`(b₁, b₂)` is obtained from the pair of projections of that fibre product by base change along the
induced morphism `Y ⟶ u (V₁ ×_U V₂)`. -/
noncomputable def glue {V₁ V₂ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    {Y : 𝒟} (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂) :
    Functor.pullbackFiber p (fiberFib (D.obj f₁ hf₁)) b₁ ≅
      Functor.pullbackFiber p (fiberFib (D.obj f₂ hf₂)) b₂ :=
  core D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition
    ((isPullback_map_pullback u f₁ f₂).lift b₁ b₂ hb) b₁ b₂
    ((isPullback_map_pullback u f₁ f₂).lift_fst b₁ b₂ hb)
    ((isPullback_map_pullback u f₁ f₂).lift_snd b₁ b₂ hb)

/-- `glue` is computed by *any* object of `𝒞` comparing the two arrows: the fibre product is only
one choice of such an object. -/
lemma glue_eq_core {V₁ V₂ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) {Y : 𝒟} (t : Y ⟶ u.obj Z)
    (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (h₁ : t ≫ u.map c₁ = b₁) (h₂ : t ≫ u.map c₂ = b₂)
    (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂) :
    glue D hf₁ hf₂ b₁ b₂ hb = core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂ := by
  have hk : t ≫ u.map (pullback.lift c₁ c₂ hc) =
      (isPullback_map_pullback u f₁ f₂).lift b₁ b₂ hb := by
    refine (isPullback_map_pullback u f₁ f₂).hom_ext ?_ ?_
    · rw [Category.assoc, ← u.map_comp, pullback.lift_fst, h₁,
        (isPullback_map_pullback u f₁ f₂).lift_fst]
    · rw [Category.assoc, ← u.map_comp, pullback.lift_snd, h₂,
        (isPullback_map_pullback u f₁ f₂).lift_snd]
  exact (core_refine' D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition
    (pullback.lift c₁ c₂ hc) c₁ c₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hc _ t hk
    b₁ b₂ _ _ h₁ h₂).symm

/-- The cocycle condition for `glue`: it is the cocycle condition of the datum over the triple
fibre product `V₁ ×_U V₂ ×_U V₃`, to which all three gluing isomorphisms are base changed. -/
@[reassoc]
lemma glue_cocycle {V₁ V₂ V₃ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    {f₃ : V₃ ⟶ U} (hf₃ : R f₃) {Y : 𝒟} (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂)
    (b₃ : Y ⟶ u.obj V₃) (h₁₂ : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂)
    (h₂₃ : b₂ ≫ u.map f₂ = b₃ ≫ u.map f₃) (h₁₃ : b₁ ≫ u.map f₁ = b₃ ≫ u.map f₃) :
    (glue D hf₁ hf₂ b₁ b₂ h₁₂).hom ≫ (glue D hf₂ hf₃ b₂ b₃ h₂₃).hom =
      (glue D hf₁ hf₃ b₁ b₃ h₁₃).hom := by
  have hpb₁₂ := isPullback_map_pullback u f₁ f₂
  have hpb₂₃ := isPullback_map_pullback u f₂ f₃
  have hpbT := isPullback_map_pullback u (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)
  have hcomm : hpb₁₂.lift b₁ b₂ h₁₂ ≫ u.map (pullback.snd f₁ f₂) =
      hpb₂₃.lift b₂ b₃ h₂₃ ≫ u.map (pullback.fst f₂ f₃) := by
    rw [hpb₁₂.lift_snd, hpb₂₃.lift_fst]
  have hts := hpbT.lift_fst (hpb₁₂.lift b₁ b₂ h₁₂) (hpb₂₃.lift b₂ b₃ h₂₃) hcomm
  have hts' := hpbT.lift_snd (hpb₁₂.lift b₁ b₂ h₁₂) (hpb₂₃.lift b₂ b₃ h₂₃) hcomm
  have hd₁ : hpbT.lift (hpb₁₂.lift b₁ b₂ h₁₂) (hpb₂₃.lift b₂ b₃ h₂₃) hcomm ≫
      u.map (pullback.fst (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.fst f₁ f₂) = b₁ := by
    rw [u.map_comp, ← Category.assoc, hts, hpb₁₂.lift_fst]
  have hd₂ : hpbT.lift (hpb₁₂.lift b₁ b₂ h₁₂) (hpb₂₃.lift b₂ b₃ h₂₃) hcomm ≫
      u.map (pullback.fst (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.snd f₁ f₂) = b₂ := by
    rw [u.map_comp, ← Category.assoc, hts, hpb₁₂.lift_snd]
  have hd₃ : hpbT.lift (hpb₁₂.lift b₁ b₂ h₁₂) (hpb₂₃.lift b₂ b₃ h₂₃) hcomm ≫
      u.map (pullback.snd (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.snd f₂ f₃) = b₃ := by
    rw [u.map_comp, ← Category.assoc, hts', hpb₂₃.lift_snd]
  have hc₁₂ : (pullback.fst (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.fst f₁ f₂) ≫ f₁ =
      (pullback.fst (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.snd f₁ f₂) ≫ f₂ := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc₂₃ : (pullback.fst (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.snd f₁ f₂) ≫ f₂ =
      (pullback.snd (pullback.snd f₁ f₂) (pullback.fst f₂ f₃) ≫ pullback.snd f₂ f₃) ≫ f₃ := by
    rw [Category.assoc, Category.assoc, ← pullback.condition (f := f₂) (g := f₃)]
    simp only [← Category.assoc]
    rw [pullback.condition]
  rw [glue_eq_core D hf₁ hf₂ _ _ hc₁₂ _ b₁ b₂ hd₁ hd₂ h₁₂,
    glue_eq_core D hf₂ hf₃ _ _ hc₂₃ _ b₂ b₃ hd₂ hd₃ h₂₃,
    glue_eq_core D hf₁ hf₃ _ _ (hc₁₂.trans hc₂₃) _ b₁ b₃ hd₁ hd₃ h₁₃]
  exact core_cocycle D hf₁ hf₂ hf₃ _ _ _ hc₁₂ hc₂₃ (hc₁₂.trans hc₂₃) _ b₁ b₂ b₃ hd₁ hd₂ hd₃

/-- `glue` is compatible with base change in `𝒟`. -/
lemma glue_pullback {V₁ V₂ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    {Y Y' : 𝒟} (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂)
    (γ : Y' ⟶ Y) :
    (glue D hf₁ hf₂ (γ ≫ b₁) (γ ≫ b₂)
        (by rw [Category.assoc, Category.assoc, hb])).hom =
      (Functor.pullbackFiberCompIso (fiberFib (D.obj f₁ hf₁)) b₁ γ).inv ≫
        Functor.pullbackFiberHom (glue D hf₁ hf₂ b₁ b₂ hb).hom γ ≫
        (Functor.pullbackFiberCompIso (fiberFib (D.obj f₂ hf₂)) b₂ γ).hom := by
  rw [glue_eq_core D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition
      (γ ≫ (isPullback_map_pullback u f₁ f₂).lift b₁ b₂ hb) (γ ≫ b₁) (γ ≫ b₂)
      (by rw [Category.assoc, (isPullback_map_pullback u f₁ f₂).lift_fst])
      (by rw [Category.assoc, (isPullback_map_pullback u f₁ f₂).lift_snd])
      (by rw [Category.assoc, Category.assoc, hb]),
    glue]
  exact core_pullback D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition _
    b₁ b₂ _ _ γ

/-- `glue_pullback` with the base-changed pair of morphisms named. -/
lemma glue_pullback' {V₁ V₂ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁) {f₂ : V₂ ⟶ U} (hf₂ : R f₂)
    {Y Y' : 𝒟} (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂)
    (γ : Y' ⟶ Y) (b₁' : Y' ⟶ u.obj V₁) (b₂' : Y' ⟶ u.obj V₂) (hg₁ : γ ≫ b₁ = b₁')
    (hg₂ : γ ≫ b₂ = b₂') (hb' : b₁' ≫ u.map f₁ = b₂' ≫ u.map f₂) :
    (glue D hf₁ hf₂ b₁' b₂' hb').hom =
      (Functor.pullbackFiberCompIso' (fiberFib (D.obj f₁ hf₁)) b₁ γ b₁' hg₁).inv ≫
        Functor.pullbackFiberHom (glue D hf₁ hf₂ b₁ b₂ hb).hom γ ≫
        (Functor.pullbackFiberCompIso' (fiberFib (D.obj f₂ hf₂)) b₂ γ b₂' hg₂).hom := by
  subst hg₁; subst hg₂
  exact glue_pullback D hf₁ hf₂ b₁ b₂ hb γ

/-- The descent datum for `p` on the pushforward of the covering sieve, attached to a descent datum
for `u^p𝒮`: an arrow of the pushforward sieve is sent to the chosen pullback, along a chosen
factorization, of the object of `𝒮` underlying what the given datum attaches to the corresponding
arrow of `R`. -/
noncomputable def pushforwardDatum : Functor.SieveDescentDatum p (R.functorPushforward u) where
  obj {Y} h hh := Functor.pullbackFiber p
    (fiberFib (D.obj (factorization hh).arrow (factorization hh).mem)) (factorization hh).lift
  iso {Y₁ Y₂ Z} {h₁} hh₁ {h₂} hh₂ ε ε' heq :=
    Functor.pullbackFiberCompIso _ _ ε ≪≫
      glue D (factorization hh₁).mem (factorization hh₂).mem (ε ≫ (factorization hh₁).lift)
        (ε' ≫ (factorization hh₂).lift) (by
          rw [Category.assoc, Category.assoc, ← (factorization hh₁).fac,
            ← (factorization hh₂).fac]
          exact heq) ≪≫
      (Functor.pullbackFiberCompIso _ _ ε').symm
  cocycle {Y₁ Y₂ Y₃ Z} {h₁} hh₁ {h₂} hh₂ {h₃} hh₃ ε₁ ε₂ ε₃ k₁₂ k₂₃ k₁₃ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [glue_cocycle_assoc D (factorization hh₁).mem (factorization hh₂).mem
      (factorization hh₃).mem]
  iso_pullback {Y₁ Y₂ Z Z'} {h₁} hh₁ {h₂} hh₂ ε ε' heq γ := by
    have hp₁ := Functor.pullbackFiberCompIso_pentagon
      (fiberFib (D.obj (factorization hh₁).arrow (factorization hh₁).mem))
      (factorization hh₁).lift ε γ
    have hp₂ := Functor.pullbackFiberCompIso_pentagon
      (fiberFib (D.obj (factorization hh₂).arrow (factorization hh₂).mem))
      (factorization hh₂).lift ε' γ
    have e₁ : (Functor.pullbackFiberCompIso
          (Functor.pullbackFiber p
            (fiberFib (D.obj (factorization hh₁).arrow (factorization hh₁).mem))
            (factorization hh₁).lift) ε γ).inv ≫
        Functor.pullbackFiberHom (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorization hh₁).arrow (factorization hh₁).mem))
          (factorization hh₁).lift ε).hom γ =
        (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorization hh₁).arrow (factorization hh₁).mem))
          (factorization hh₁).lift (γ ≫ ε)).hom ≫
          (Functor.pullbackFiberCompIso'
            (fiberFib (D.obj (factorization hh₁).arrow (factorization hh₁).mem))
            (ε ≫ (factorization hh₁).lift) γ ((γ ≫ ε) ≫ (factorization hh₁).lift)
            (Category.assoc _ _ _).symm).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hp₁, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have e₂ : Functor.pullbackFiberHom (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorization hh₂).arrow (factorization hh₂).mem))
          (factorization hh₂).lift ε').inv γ ≫
        (Functor.pullbackFiberCompIso
          (Functor.pullbackFiber p
            (fiberFib (D.obj (factorization hh₂).arrow (factorization hh₂).mem))
            (factorization hh₂).lift) ε' γ).hom =
        (Functor.pullbackFiberCompIso'
            (fiberFib (D.obj (factorization hh₂).arrow (factorization hh₂).mem))
            (ε' ≫ (factorization hh₂).lift) γ ((γ ≫ ε') ≫ (factorization hh₂).lift)
            (Category.assoc _ _ _).symm).hom ≫
          (Functor.pullbackFiberCompIso
            (fiberFib (D.obj (factorization hh₂).arrow (factorization hh₂).mem))
            (factorization hh₂).lift (γ ≫ ε')).inv := by
      rw [← Functor.pullbackFiberIso_inv, Iso.inv_comp_eq, Functor.pullbackFiberIso_hom,
        ← Category.assoc, hp₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.pullbackFiberIso_hom,
      Functor.pullbackFiberHom_comp]
    rw [glue_pullback' D (factorization hh₁).mem (factorization hh₂).mem
        (ε ≫ (factorization hh₁).lift) (ε' ≫ (factorization hh₂).lift) _ γ _ _
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm _,
      ← Category.assoc, e₁]
    · simp only [Category.assoc]
      rw [← e₂]

/-- The object `StrictPullback.pushforwardDatum` attaches to an arrow of the pushforward sieve: the
chosen pullback, along the chosen factorization, of the object of `𝒮` underlying what `D` attaches
to the corresponding arrow of `R`. -/
@[simp]
lemma pushforwardDatum_obj {Y : 𝒟} (h : Y ⟶ u.obj U) (hh : (R.functorPushforward u) h) :
    (pushforwardDatum D).obj h hh =
      Functor.pullbackFiber p
        (fiberFib (D.obj (factorization hh).arrow (factorization hh).mem))
        (factorization hh).lift := rfl

/-- The gluing isomorphism of `StrictPullback.pushforwardDatum` is `StrictPullback.glue` between
the chosen factorizations, conjugated by the contractions of the iterated chosen pullbacks. -/
@[simp]
lemma pushforwardDatum_iso {Y₁ Y₂ Z : 𝒟} {h₁ : Y₁ ⟶ u.obj U}
    (hh₁ : (R.functorPushforward u) h₁) {h₂ : Y₂ ⟶ u.obj U} (hh₂ : (R.functorPushforward u) h₂)
    (ε : Z ⟶ Y₁) (ε' : Z ⟶ Y₂) (heq : ε ≫ h₁ = ε' ≫ h₂) :
    (pushforwardDatum D).iso hh₁ hh₂ ε ε' heq =
      Functor.pullbackFiberCompIso _ _ ε ≪≫
        glue D (factorization hh₁).mem (factorization hh₂).mem (ε ≫ (factorization hh₁).lift)
          (ε' ≫ (factorization hh₂).lift) (by
            rw [Category.assoc, Category.assoc, ← (factorization hh₁).fac,
              ← (factorization hh₂).fac]
            exact heq) ≪≫
        (Functor.pullbackFiberCompIso _ _ ε').symm := rfl

omit [HasPullbacks 𝒞] [PreservesLimitsOfShape WalkingCospan u] in
/-- The image of an arrow of `R` is an arrow of the pushforward sieve. -/
lemma mem_functorPushforward {V : 𝒞} (f : V ⟶ U) (hf : R f) :
    (R.functorPushforward u) (u.map f) := ⟨V, f, 𝟙 _, hf, by simp⟩

/-- The object `pushforwardDatum` attaches to `u f` is canonically isomorphic, in the fibre of `p`
over `u V`, to the object of `𝒮` underlying what `D` attaches to `f`: the chosen factorization of
`u f` need not be `f` itself, and `glue` compares the two. -/
noncomputable def pushforwardObjIso {V : 𝒞} (f : V ⟶ U) (hf : R f) :
    fiberFib (D.obj f hf) ≅ (pushforwardDatum D).obj (u.map f) (mem_functorPushforward f hf) :=
  (Functor.pullbackFiberIdIso (fiberFib (D.obj f hf))).symm ≪≫
    glue D hf (factorization (mem_functorPushforward f hf)).mem (𝟙 (u.obj V))
      (factorization (mem_functorPushforward f hf)).lift (by
        rw [Category.id_comp]
        exact (factorization (mem_functorPushforward f hf)).fac)

/-- Base changing `pushforwardObjIso` along `b` and contracting is `glue`. -/
lemma pushforwardObjIso_pullback {V : 𝒞} (f : V ⟶ U) (hf : R f) {Y : 𝒟} (b : Y ⟶ u.obj V) :
    Functor.pullbackFiberHom (pushforwardObjIso D f hf).hom b ≫
        (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorization (mem_functorPushforward f hf)).arrow
            (factorization (mem_functorPushforward f hf)).mem))
          (factorization (mem_functorPushforward f hf)).lift b).hom =
      (glue D hf (factorization (mem_functorPushforward f hf)).mem b
        (b ≫ (factorization (mem_functorPushforward f hf)).lift) (by
          rw [Category.assoc, ← (factorization (mem_functorPushforward f hf)).fac])).hom := by
  rw [glue_pullback' D hf (factorization (mem_functorPushforward f hf)).mem (𝟙 (u.obj V))
      (factorization (mem_functorPushforward f hf)).lift
      (by rw [Category.id_comp]; exact (factorization (mem_functorPushforward f hf)).fac) b b
      (b ≫ (factorization (mem_functorPushforward f hf)).lift) (Category.comp_id b) rfl
      (by rw [Category.assoc, ← (factorization (mem_functorPushforward f hf)).fac])]
  simp [pushforwardObjIso, Iso.trans_hom, Iso.symm_hom, Functor.pullbackFiberHom_comp,
    Functor.pullbackFiberCompIso'_rfl, Category.assoc,
    Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq]

/-- The gluing isomorphism of `pushforwardDatum` at the image of a pair of morphisms of `𝒞` is
`glue`, conjugated by `pushforwardObjIso`. -/
lemma pushforwardDatum_iso_map {V W Z : 𝒞} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Functor.pullbackFiberHom (pushforwardObjIso D f hf).hom (u.map ε) ≫
        ((pushforwardDatum D).iso (mem_functorPushforward f hf) (mem_functorPushforward g hg)
          (u.map ε) (u.map ε') (by rw [← u.map_comp, ← u.map_comp, heq])).hom =
      (glue D hf hg (u.map ε) (u.map ε') (by rw [← u.map_comp, ← u.map_comp, heq])).hom ≫
        Functor.pullbackFiberHom (pushforwardObjIso D g hg).hom (u.map ε') := by
  rw [pushforwardDatum_iso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  have hlast : u.map ε ≫ u.map f =
      (u.map ε' ≫ (factorization (mem_functorPushforward g hg)).lift) ≫
        u.map (factorization (mem_functorPushforward g hg)).arrow := by
    rw [Category.assoc, ← (factorization (mem_functorPushforward g hg)).fac, ← u.map_comp,
      ← u.map_comp, heq]
  rw [← Category.assoc, pushforwardObjIso_pullback D f hf (u.map ε),
    ← Category.assoc, glue_cocycle D hf (factorization (mem_functorPushforward f hf)).mem
      (factorization (mem_functorPushforward g hg)).mem (h₁₃ := hlast)]
  rw [Iso.comp_inv_eq, Category.assoc, pushforwardObjIso_pullback D g hg (u.map ε'),
    glue_cocycle D hf hg (factorization (mem_functorPushforward g hg)).mem (h₁₃ := hlast)]

/-- The transported gluing isomorphism at the image of a pair of morphisms of `𝒞` is the gluing
isomorphism of the datum itself, read in `𝒮` through `fiberFibPullbackIso`. -/
lemma glue_map {V W Z : 𝒞} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) :
    glue D hf hg (u.map ε) (u.map ε') (by rw [← u.map_comp, ← u.map_comp, heq]) =
      fiberFibPullbackIso (D.obj f hf) ε ≪≫
        (fiberFibFunctor u p Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
        (fiberFibPullbackIso (D.obj g hg) ε').symm := by
  rw [glue_eq_core D hf hg ε ε' heq (𝟙 (u.obj Z)) (u.map ε) (u.map ε') (Category.id_comp _)
    (Category.id_comp _) _]
  refine Iso.ext (Functor.fiber_hom_ext_of_cartesian (u.map ε')
    (Functor.IsPreFibered.pullbackMap (fiberFib (D.obj g hg)).2 (u.map ε'))
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_)
  rw [core_fac, ← fiberCmp_id]
  simp [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Functor.pullbackFiberIdIso_hom_fac, fiberFibPullbackIso_inv_fac,
    fiberInclusion_map_fiberFibFunctor_map, Functor.mapIso_hom]

end Glue

end Descent

/-- **Stacks 026F (3)** for the pushforward: descent along a covering sieve of `𝒞` is effective for
`u^p𝒮` as soon as it is effective for `p` along covering sieves of `𝒟`.

The proof pushes the covering sieve forward to `𝒟`, which is again covering because `u` is
continuous, transports the datum there — `StrictPullback.pushforwardDatum`, the step at which `u`
has to commute with fibre products — and descends it. The compatibility of the resulting cartesian
morphisms with the *given* gluing isomorphisms is the compatibility of the descended ones, read
back through `StrictPullback.pushforwardObjIso` and `StrictPullback.glue_map`. -/
theorem hasEffectiveDescent_structureFunctor (J : GrothendieckTopology 𝒞)
    (K : GrothendieckTopology 𝒟) (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] [HasPullbacks 𝒞]
    [PreservesLimitsOfShape WalkingCospan u] (p : 𝒮 ⥤ 𝒟) [p.IsFibered]
    (hp : Functor.HasEffectiveDescent p K) :
    Functor.HasEffectiveDescent (structureFunctor u p) J := by
  intro U R hR D
  have hcov : R.functorPushforward u ∈ K (u.obj U) :=
    (CoverPreserving.of_isContinuous u J K).cover_preserve hR
  obtain ⟨X, ζ, hζ, hcompat⟩ := hp _ hcov (pushforwardDatum D)
  have hη : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      p.IsStronglyCartesian (u.map f)
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D f hf).hom ≫
          ζ (u.map f) (mem_functorPushforward f hf)) := by
    intro V f hf
    have hθ : p.IsHomLift (𝟙 (u.obj V))
        (Functor.Fiber.fiberInclusion.mapIso (pushforwardObjIso D f hf)).hom :=
      (pushforwardObjIso D f hf).hom.2
    have hθs : p.IsStronglyCartesian (𝟙 (u.obj V))
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D f hf).hom) :=
      have := hθ
      Functor.IsStronglyCartesian.of_iso p _
        (Functor.Fiber.fiberInclusion.mapIso (pushforwardObjIso D f hf))
    have hζc : p.IsCartesian (u.map f) (ζ (u.map f) (mem_functorPushforward f hf)) :=
      hζ _ (mem_functorPushforward f hf)
    have hζs : p.IsStronglyCartesian (u.map f) (ζ (u.map f) (mem_functorPushforward f hf)) :=
      inferInstance
    have h : p.IsStronglyCartesian (𝟙 (u.obj V) ≫ u.map f)
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D f hf).hom ≫
          ζ (u.map f) (mem_functorPushforward f hf)) := inferInstance
    rwa [Category.id_comp] at h
  have hsc : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      p.IsStronglyCartesian (u.map (eqToHom (D.obj f hf).2 ≫ f))
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D f hf).hom ≫
          ζ (u.map f) (mem_functorPushforward f hf)) := by
    intro V f hf
    rw [u.map_comp, eqToHom_map]
    exact Functor.IsStronglyCartesian.eqToHom_comp _ _ _ (hη f hf)
  let φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (D.obj f hf).1 ⟶ (fiberMk X).1 := fun _ f hf =>
    homMk' (X := (D.obj f hf).1) (Y := (fiberMk X).1) (eqToHom (D.obj f hf).2 ≫ f)
      (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D f hf).hom ≫
        ζ (u.map f) (mem_functorPushforward f hf)) (hsc f hf).toIsHomLift
  have hξ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (structureFunctor u p).IsCartesian f (φ f hf) := by
    intro V f hf
    have h1 := isStronglyCartesian_of_fib' (φ f hf) (hsc f hf)
    have := Functor.IsStronglyCartesian.of_eqToHom_comp (D.obj f hf).2 f _ h1
    infer_instance
  refine ⟨fiberMk X, φ, fun {V} f hf => hξ f hf, ?_⟩
  intro V W Z f hf g hg ε ε' heq
  have hue : u.map ε ≫ u.map f = u.map ε' ≫ u.map g := by
    rw [← u.map_comp, ← u.map_comp, heq]
  -- the compatibility of the *descended* gluing isomorphisms, read back along `pushforwardObjIso`
  have hQ' : Functor.Fiber.fiberInclusion.map
        (glue D hf hg (u.map ε) (u.map ε') hue).hom ≫
        Functor.IsPreFibered.pullbackMap (fiberFib (D.obj g hg)).2 (u.map ε') ≫
          (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D g hg).hom ≫
            ζ (u.map g) (mem_functorPushforward g hg)) =
      Functor.IsPreFibered.pullbackMap (fiberFib (D.obj f hf)).2 (u.map ε) ≫
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIso D f hf).hom ≫
          ζ (u.map f) (mem_functorPushforward f hf)) := by
    have hc := hcompat (mem_functorPushforward f hf) (mem_functorPushforward g hg)
      (u.map ε) (u.map ε') hue
    have hPmap := congrArg Functor.Fiber.fiberInclusion.map
      (pushforwardDatum_iso_map D hf hg ε ε' heq)
    simp only [Functor.map_comp] at hPmap
    rw [← Functor.pullbackFiberHom_fac_assoc (pushforwardObjIso D g hg).hom (u.map ε'),
      ← Functor.pullbackFiberHom_fac_assoc (pushforwardObjIso D f hf).hom (u.map ε),
      ← hc, reassoc_of% hPmap]
  -- and its translation into the gluing isomorphisms of `D` itself
  rw [glue_map D hf hg ε ε' heq] at hQ'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    fiberFibPullbackIso_inv_fac_assoc, fiberInclusion_map_fiberFibFunctor_map] at hQ'
  rw [← fiberFibPullbackIso_hom_fac_assoc (D.obj f hf) ε] at hQ'
  refine hom_ext_of_fib (ε ≫ f) _ _ ?_ ?_ ?_
  · have hdiso : (structureFunctor u p).IsHomLift (𝟙 Z)
        (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) :=
      (D.iso hf hg ε ε' heq).hom.2
    have hpg : (structureFunctor u p).IsCartesian ε'
        (Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε') :=
      Functor.IsPreFibered.pullbackMap.IsCartesian _ _
    have hg' := hξ g hg
    have h : (structureFunctor u p).IsHomLift (𝟙 Z ≫ ε' ≫ g)
        (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
          Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ φ g hg) :=
      inferInstance
    rwa [Category.id_comp, ← heq] at h
  · have hpf : (structureFunctor u p).IsCartesian ε
        (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε) :=
      Functor.IsPreFibered.pullbackMap.IsCartesian _ _
    have hf' := hξ f hf
    infer_instance
  · simpa only [φ, comp_fib, homMk'_fib, Category.assoc] using (cancel_epi
      (Functor.Fiber.fiberInclusion.map (fiberFibPullbackIso (D.obj f hf) ε).hom)).1 hQ'

end StrictPullback

/-! ### Effective descent along a covering with fibre products

The results above assume that `𝒞` has all fibre products and that `u` preserves them. Stacks 00VH
asks of a site only the fibre products `Vⱼ ×_V T` of the members of a covering with arbitrary
morphisms, and Stacks 00WU asks of a continuous functor only that it commute with those. What
follows proves effectivity of descent under exactly that assumption: a descent datum relative to
a sieve `R` is effective as soon as `R` contains a family `P` whose members have fibre products
with every morphism of `𝒞`, with which `u` commutes
(`CategoryTheory.StrictPullback.PreservesBaseChanges`), and such that `u` sends `R` into the
covering sieve generated by `u(P)`. The argument is the one above, with the arrows of the
transported sieve factored through the images of the members of `P`
(`CategoryTheory.StrictPullback.pushforwardDatumThrough`), and every cocycle condition checked
over a fibre product of an object of `𝒞` with a member of `P`. -/

namespace StrictPullback

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {u : 𝒞 ⥤ 𝒟} {p : 𝒮 ⥤ 𝒟}

/-- The morphism `f : V ⟶ U` has a fibre product `T ×_U V` with every morphism `T ⟶ U`, and `u`
commutes with it: condition (2) of Stacks 00WU, for the member `f` of a covering. -/
def PreservesBaseChanges (u : 𝒞 ⥤ 𝒟) {V U : 𝒞} (f : V ⟶ U) : Prop :=
  ∀ ⦃T : 𝒞⦄ (g : T ⟶ U), HasPullback g f ∧ PreservesLimit (cospan g f) u

/-- A factorization of an arrow of the sieve generated by the image `u(P)` of a presieve `P`
through the image of a member of `P`. -/
structure FactorizationThrough (u : 𝒞 ⥤ 𝒟) {U : 𝒞} (P : Presieve U) {Y : 𝒟}
    (h : Y ⟶ u.obj U) where
  /-- The source of the member of `P`. -/
  src : 𝒞
  /-- The member of `P`. -/
  arrow : src ⟶ U
  /-- The arrow belongs to `P`. -/
  mem : P arrow
  /-- The morphism of `𝒟` through which `h` factors. -/
  lift : Y ⟶ u.obj src
  /-- The factorization itself. -/
  fac : h = lift ≫ u.map arrow

/-- Every arrow of the sieve generated by `u(P)` factors through the image of a member of `P`. -/
lemma nonempty_factorizationThrough {U : 𝒞} {P : Presieve U} {Y : 𝒟} {h : Y ⟶ u.obj U}
    (hh : Sieve.generate (P.map u) h) : Nonempty (FactorizationThrough u P h) := by
  obtain ⟨W, a, g, ⟨hf⟩, rfl⟩ := hh
  exact ⟨⟨_, _, hf, a, rfl⟩⟩

/-- A choice of factorization of an arrow of the sieve generated by `u(P)`. -/
noncomputable def factorizationThrough {U : 𝒞} {P : Presieve U} {Y : 𝒟} {h : Y ⟶ u.obj U}
    (hh : Sieve.generate (P.map u) h) : FactorizationThrough u P h :=
  Classical.choice (nonempty_factorizationThrough hh)

variable [p.IsFibered]

section Datum

variable {U : 𝒞} {R : Sieve U} (D : Functor.SieveDescentDatum (structureFunctor u p) R)

/-- `StrictPullback.core` over the identity of the image of an object `Z` of `𝒞` mapping to two
arrows of the sieve is the gluing isomorphism of the datum over `Z`, read in `𝒮` through
`fiberFibPullbackIso`. -/
lemma core_id_map {V W Z : 𝒞} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g) (ε : Z ⟶ V)
    (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    core D hf hg ε ε' heq (𝟙 (u.obj Z)) (u.map ε) (u.map ε') (Category.id_comp _)
        (Category.id_comp _) =
      fiberFibPullbackIso (D.obj f hf) ε ≪≫
        (fiberFibFunctor u p Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
        (fiberFibPullbackIso (D.obj g hg) ε').symm := by
  refine Iso.ext (Functor.fiber_hom_ext_of_cartesian (u.map ε')
    (Functor.IsPreFibered.pullbackMap (fiberFib (D.obj g hg)).2 (u.map ε'))
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_)
  rw [core_fac, ← fiberCmp_id]
  simp [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Functor.pullbackFiberIdIso_hom_fac, fiberFibPullbackIso_inv_fac,
    fiberInclusion_map_fiberFibFunctor_map, Functor.mapIso_hom]

/-- The gluing isomorphism of a descent datum for `u^p𝒮`, transported to `𝒮`, between an arrow
`f₁` of the sieve and an arrow `f₂` of the sieve along which `u` commutes with base change. For
two morphisms `b₁`, `b₂` of `𝒟` into the images of their sources agreeing over `u U`, the pair
`(b₁, b₂)` factors through `u (V₁ ×_U V₂)`, and the isomorphism is the base change of the gluing
isomorphism of the datum over `V₁ ×_U V₂`. -/
noncomputable def glueOfPreservesBaseChanges {V₁ V₂ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁)
    {f₂ : V₂ ⟶ U} (hf₂ : R f₂) (h₂ : PreservesBaseChanges u f₂) {Y : 𝒟} (b₁ : Y ⟶ u.obj V₁)
    (b₂ : Y ⟶ u.obj V₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂) :
    Functor.pullbackFiber p (fiberFib (D.obj f₁ hf₁)) b₁ ≅
      Functor.pullbackFiber p (fiberFib (D.obj f₂ hf₂)) b₂ :=
  haveI := (h₂ f₁).1
  haveI := (h₂ f₁).2
  core D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition
    (((IsPullback.of_hasPullback f₁ f₂).map u).lift b₁ b₂ hb) b₁ b₂
    (((IsPullback.of_hasPullback f₁ f₂).map u).lift_fst b₁ b₂ hb)
    (((IsPullback.of_hasPullback f₁ f₂).map u).lift_snd b₁ b₂ hb)

/-- `glueOfPreservesBaseChanges` is computed by *any* object of `𝒞` comparing the two arrows: the
fibre product is only one choice of such an object. -/
lemma glueOfPreservesBaseChanges_eq_core {V₁ V₂ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁)
    {f₂ : V₂ ⟶ U} (hf₂ : R f₂) (h₂ : PreservesBaseChanges u f₂) (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂)
    (hc : c₁ ≫ f₁ = c₂ ≫ f₂) {Y : 𝒟} (t : Y ⟶ u.obj Z) (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂)
    (h₁ : t ≫ u.map c₁ = b₁) (h₂' : t ≫ u.map c₂ = b₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂) :
    glueOfPreservesBaseChanges D hf₁ hf₂ h₂ b₁ b₂ hb = core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂' := by
  have := (h₂ f₁).1
  have := (h₂ f₁).2
  have hpb := (IsPullback.of_hasPullback f₁ f₂).map u
  have hk : t ≫ u.map (pullback.lift c₁ c₂ hc) = hpb.lift b₁ b₂ hb := by
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, ← u.map_comp, pullback.lift_fst, h₁, hpb.lift_fst]
    · rw [Category.assoc, ← u.map_comp, pullback.lift_snd, h₂', hpb.lift_snd]
  exact (core_refine' D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition
    (pullback.lift c₁ c₂ hc) c₁ c₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hc _ t hk
    b₁ b₂ _ _ h₁ h₂').symm

/-- A cocycle condition mixing `StrictPullback.core` and `glueOfPreservesBaseChanges`: it is the
cocycle condition of the datum over the fibre product `Z ×_U V₃`, which exists because `u`
commutes with base change along `f₃`. -/
lemma core_glueOfPreservesBaseChanges_cocycle {V₁ V₂ V₃ Z : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁)
    {f₂ : V₂ ⟶ U} (hf₂ : R f₂) {f₃ : V₃ ⟶ U} (hf₃ : R f₃) (h₃ : PreservesBaseChanges u f₃)
    (c₁ : Z ⟶ V₁) (c₂ : Z ⟶ V₂) (hc : c₁ ≫ f₁ = c₂ ≫ f₂) {Y : 𝒟} (t : Y ⟶ u.obj Z)
    (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂) (b₃ : Y ⟶ u.obj V₃) (h₁ : t ≫ u.map c₁ = b₁)
    (h₂ : t ≫ u.map c₂ = b₂) (h₂₃ : b₂ ≫ u.map f₂ = b₃ ≫ u.map f₃)
    (h₁₃ : b₁ ≫ u.map f₁ = b₃ ≫ u.map f₃) :
    (core D hf₁ hf₂ c₁ c₂ hc t b₁ b₂ h₁ h₂).hom ≫
        (glueOfPreservesBaseChanges D hf₂ hf₃ h₃ b₂ b₃ h₂₃).hom =
      (glueOfPreservesBaseChanges D hf₁ hf₃ h₃ b₁ b₃ h₁₃).hom := by
  have := (h₃ (c₁ ≫ f₁)).1
  have := (h₃ (c₁ ≫ f₁)).2
  have hpb := (IsPullback.of_hasPullback (c₁ ≫ f₁) f₃).map u
  have ht : t ≫ u.map (c₁ ≫ f₁) = b₃ ≫ u.map f₃ := by
    rw [u.map_comp, ← Category.assoc, h₁, h₁₃]
  obtain ⟨t', ht₁, ht₂⟩ : ∃ t' : Y ⟶ u.obj (pullback (c₁ ≫ f₁) f₃),
      t' ≫ u.map (pullback.fst (c₁ ≫ f₁) f₃) = t ∧ t' ≫ u.map (pullback.snd (c₁ ≫ f₁) f₃) = b₃ :=
    ⟨hpb.lift t b₃ ht, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have e₁ : t' ≫ u.map (pullback.fst (c₁ ≫ f₁) f₃ ≫ c₁) = b₁ := by
    rw [u.map_comp, ← Category.assoc, ht₁, h₁]
  have e₂ : t' ≫ u.map (pullback.fst (c₁ ≫ f₁) f₃ ≫ c₂) = b₂ := by
    rw [u.map_comp, ← Category.assoc, ht₁, h₂]
  have k₁₂ : (pullback.fst (c₁ ≫ f₁) f₃ ≫ c₁) ≫ f₁ = (pullback.fst (c₁ ≫ f₁) f₃ ≫ c₂) ≫ f₂ :=
    (Category.assoc _ _ _).trans ((congrArg (pullback.fst (c₁ ≫ f₁) f₃ ≫ ·) hc).trans
      (Category.assoc _ _ _).symm)
  have k₁₃ : (pullback.fst (c₁ ≫ f₁) f₃ ≫ c₁) ≫ f₁ = pullback.snd (c₁ ≫ f₁) f₃ ≫ f₃ := by
    rw [Category.assoc, pullback.condition]
  have k₂₃ : (pullback.fst (c₁ ≫ f₁) f₃ ≫ c₂) ≫ f₂ = pullback.snd (c₁ ≫ f₁) f₃ ≫ f₃ :=
    k₁₂.symm.trans k₁₃
  rw [← core_refine' D hf₁ hf₂ c₁ c₂ hc (pullback.fst (c₁ ≫ f₁) f₃) _ _ rfl rfl k₁₂ t t' ht₁
      b₁ b₂ h₁ h₂ e₁ e₂,
    glueOfPreservesBaseChanges_eq_core D hf₂ hf₃ h₃ _ _ k₂₃ t' b₂ b₃ e₂ ht₂ h₂₃,
    glueOfPreservesBaseChanges_eq_core D hf₁ hf₃ h₃ _ _ k₁₃ t' b₁ b₃ e₁ ht₂ h₁₃]
  exact core_cocycle D hf₁ hf₂ hf₃ _ _ _ k₁₂ k₂₃ k₁₃ t' b₁ b₂ b₃ e₁ e₂ ht₂

/-- The cocycle condition for `glueOfPreservesBaseChanges`. -/
@[reassoc]
lemma glueOfPreservesBaseChanges_cocycle {V₁ V₂ V₃ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁)
    {f₂ : V₂ ⟶ U} (hf₂ : R f₂) {f₃ : V₃ ⟶ U} (hf₃ : R f₃) (h₂ : PreservesBaseChanges u f₂)
    (h₃ : PreservesBaseChanges u f₃) {Y : 𝒟} (b₁ : Y ⟶ u.obj V₁) (b₂ : Y ⟶ u.obj V₂)
    (b₃ : Y ⟶ u.obj V₃) (h₁₂ : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂)
    (h₂₃ : b₂ ≫ u.map f₂ = b₃ ≫ u.map f₃) (h₁₃ : b₁ ≫ u.map f₁ = b₃ ≫ u.map f₃) :
    (glueOfPreservesBaseChanges D hf₁ hf₂ h₂ b₁ b₂ h₁₂).hom ≫
        (glueOfPreservesBaseChanges D hf₂ hf₃ h₃ b₂ b₃ h₂₃).hom =
      (glueOfPreservesBaseChanges D hf₁ hf₃ h₃ b₁ b₃ h₁₃).hom := by
  have := (h₂ f₁).1
  have := (h₂ f₁).2
  have hpb := (IsPullback.of_hasPullback f₁ f₂).map u
  rw [glueOfPreservesBaseChanges_eq_core D hf₁ hf₂ h₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
    pullback.condition (hpb.lift b₁ b₂ h₁₂) b₁ b₂ (hpb.lift_fst _ _ _) (hpb.lift_snd _ _ _) h₁₂]
  exact core_glueOfPreservesBaseChanges_cocycle D hf₁ hf₂ hf₃ h₃ _ _ _ _ b₁ b₂ b₃ _ _ h₂₃ h₁₃

/-- `glueOfPreservesBaseChanges` is compatible with base change in `𝒟`. -/
lemma glueOfPreservesBaseChanges_pullback {V₁ V₂ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁)
    {f₂ : V₂ ⟶ U} (hf₂ : R f₂) (h₂ : PreservesBaseChanges u f₂) {Y Y' : 𝒟} (b₁ : Y ⟶ u.obj V₁)
    (b₂ : Y ⟶ u.obj V₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂) (γ : Y' ⟶ Y) :
    (glueOfPreservesBaseChanges D hf₁ hf₂ h₂ (γ ≫ b₁) (γ ≫ b₂)
        (by rw [Category.assoc, Category.assoc, hb])).hom =
      (Functor.pullbackFiberCompIso (fiberFib (D.obj f₁ hf₁)) b₁ γ).inv ≫
        Functor.pullbackFiberHom (glueOfPreservesBaseChanges D hf₁ hf₂ h₂ b₁ b₂ hb).hom γ ≫
        (Functor.pullbackFiberCompIso (fiberFib (D.obj f₂ hf₂)) b₂ γ).hom := by
  have := (h₂ f₁).1
  have := (h₂ f₁).2
  have hpb := (IsPullback.of_hasPullback f₁ f₂).map u
  rw [glueOfPreservesBaseChanges_eq_core D hf₁ hf₂ h₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
      pullback.condition (γ ≫ hpb.lift b₁ b₂ hb) (γ ≫ b₁) (γ ≫ b₂)
      (by rw [Category.assoc, hpb.lift_fst]) (by rw [Category.assoc, hpb.lift_snd]) _,
    glueOfPreservesBaseChanges_eq_core D hf₁ hf₂ h₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
      pullback.condition (hpb.lift b₁ b₂ hb) b₁ b₂ (hpb.lift_fst _ _ _) (hpb.lift_snd _ _ _) hb]
  exact core_pullback D hf₁ hf₂ (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) pullback.condition _
    b₁ b₂ _ _ γ

/-- `glueOfPreservesBaseChanges_pullback` with the base-changed pair of morphisms named. -/
lemma glueOfPreservesBaseChanges_pullback' {V₁ V₂ : 𝒞} {f₁ : V₁ ⟶ U} (hf₁ : R f₁)
    {f₂ : V₂ ⟶ U} (hf₂ : R f₂) (h₂ : PreservesBaseChanges u f₂) {Y Y' : 𝒟} (b₁ : Y ⟶ u.obj V₁)
    (b₂ : Y ⟶ u.obj V₂) (hb : b₁ ≫ u.map f₁ = b₂ ≫ u.map f₂) (γ : Y' ⟶ Y)
    (b₁' : Y' ⟶ u.obj V₁) (b₂' : Y' ⟶ u.obj V₂) (hg₁ : γ ≫ b₁ = b₁') (hg₂ : γ ≫ b₂ = b₂')
    (hb' : b₁' ≫ u.map f₁ = b₂' ≫ u.map f₂) :
    (glueOfPreservesBaseChanges D hf₁ hf₂ h₂ b₁' b₂' hb').hom =
      (Functor.pullbackFiberCompIso' (fiberFib (D.obj f₁ hf₁)) b₁ γ b₁' hg₁).inv ≫
        Functor.pullbackFiberHom (glueOfPreservesBaseChanges D hf₁ hf₂ h₂ b₁ b₂ hb).hom γ ≫
        (Functor.pullbackFiberCompIso' (fiberFib (D.obj f₂ hf₂)) b₂ γ b₂' hg₂).hom := by
  subst hg₁; subst hg₂
  exact glueOfPreservesBaseChanges_pullback D hf₁ hf₂ h₂ b₁ b₂ hb γ

/-- The descent datum for `p` on the sieve generated by `u(P)`, attached to a descent datum for
`u^p𝒮` relative to a sieve `R` containing `P`: an arrow of the sieve generated by `u(P)` is sent
to the chosen pullback, along a chosen factorization through a member of `P`, of the object of
`𝒮` underlying what the given datum attaches to that member. -/
noncomputable def pushforwardDatumThrough {P : Presieve U}
    (hPR : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → R f)
    (hP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → PreservesBaseChanges u f) :
    Functor.SieveDescentDatum p (Sieve.generate (P.map u)) where
  obj {Y} h hh := Functor.pullbackFiber p
    (fiberFib (D.obj (factorizationThrough hh).arrow (hPR (factorizationThrough hh).mem)))
    (factorizationThrough hh).lift
  iso {Y₁ Y₂ Z} {h₁} hh₁ {h₂} hh₂ ε ε' heq :=
    Functor.pullbackFiberCompIso _ _ ε ≪≫
      glueOfPreservesBaseChanges D (hPR (factorizationThrough hh₁).mem)
        (hPR (factorizationThrough hh₂).mem) (hP (factorizationThrough hh₂).mem)
        (ε ≫ (factorizationThrough hh₁).lift) (ε' ≫ (factorizationThrough hh₂).lift) (by
          rw [Category.assoc, Category.assoc, ← (factorizationThrough hh₁).fac,
            ← (factorizationThrough hh₂).fac]
          exact heq) ≪≫
      (Functor.pullbackFiberCompIso _ _ ε').symm
  cocycle {Y₁ Y₂ Y₃ Z} {h₁} hh₁ {h₂} hh₂ {h₃} hh₃ ε₁ ε₂ ε₃ k₁₂ k₂₃ k₁₃ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [glueOfPreservesBaseChanges_cocycle_assoc D (hPR (factorizationThrough hh₁).mem)
      (hPR (factorizationThrough hh₂).mem) (hPR (factorizationThrough hh₃).mem)
      (hP (factorizationThrough hh₂).mem) (hP (factorizationThrough hh₃).mem)]
  iso_pullback {Y₁ Y₂ Z Z'} {h₁} hh₁ {h₂} hh₂ ε ε' heq γ := by
    have hp₁ := Functor.pullbackFiberCompIso_pentagon
      (fiberFib (D.obj (factorizationThrough hh₁).arrow (hPR (factorizationThrough hh₁).mem)))
      (factorizationThrough hh₁).lift ε γ
    have hp₂ := Functor.pullbackFiberCompIso_pentagon
      (fiberFib (D.obj (factorizationThrough hh₂).arrow (hPR (factorizationThrough hh₂).mem)))
      (factorizationThrough hh₂).lift ε' γ
    have e₁ : (Functor.pullbackFiberCompIso
          (Functor.pullbackFiber p
            (fiberFib (D.obj (factorizationThrough hh₁).arrow
              (hPR (factorizationThrough hh₁).mem)))
            (factorizationThrough hh₁).lift) ε γ).inv ≫
        Functor.pullbackFiberHom (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorizationThrough hh₁).arrow (hPR (factorizationThrough hh₁).mem)))
          (factorizationThrough hh₁).lift ε).hom γ =
        (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorizationThrough hh₁).arrow (hPR (factorizationThrough hh₁).mem)))
          (factorizationThrough hh₁).lift (γ ≫ ε)).hom ≫
          (Functor.pullbackFiberCompIso'
            (fiberFib (D.obj (factorizationThrough hh₁).arrow
              (hPR (factorizationThrough hh₁).mem)))
            (ε ≫ (factorizationThrough hh₁).lift) γ ((γ ≫ ε) ≫ (factorizationThrough hh₁).lift)
            (Category.assoc _ _ _).symm).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hp₁, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have e₂ : Functor.pullbackFiberHom (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorizationThrough hh₂).arrow (hPR (factorizationThrough hh₂).mem)))
          (factorizationThrough hh₂).lift ε').inv γ ≫
        (Functor.pullbackFiberCompIso
          (Functor.pullbackFiber p
            (fiberFib (D.obj (factorizationThrough hh₂).arrow
              (hPR (factorizationThrough hh₂).mem)))
            (factorizationThrough hh₂).lift) ε' γ).hom =
        (Functor.pullbackFiberCompIso'
            (fiberFib (D.obj (factorizationThrough hh₂).arrow
              (hPR (factorizationThrough hh₂).mem)))
            (ε' ≫ (factorizationThrough hh₂).lift) γ ((γ ≫ ε') ≫ (factorizationThrough hh₂).lift)
            (Category.assoc _ _ _).symm).hom ≫
          (Functor.pullbackFiberCompIso
            (fiberFib (D.obj (factorizationThrough hh₂).arrow
              (hPR (factorizationThrough hh₂).mem)))
            (factorizationThrough hh₂).lift (γ ≫ ε')).inv := by
      rw [← Functor.pullbackFiberIso_inv, Iso.inv_comp_eq, Functor.pullbackFiberIso_hom,
        ← Category.assoc, hp₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.pullbackFiberIso_hom,
      Functor.pullbackFiberHom_comp]
    rw [glueOfPreservesBaseChanges_pullback' D (hPR (factorizationThrough hh₁).mem)
        (hPR (factorizationThrough hh₂).mem) (hP (factorizationThrough hh₂).mem)
        (ε ≫ (factorizationThrough hh₁).lift) (ε' ≫ (factorizationThrough hh₂).lift) _ γ _ _
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm _,
      ← Category.assoc, e₁]
    · simp only [Category.assoc]
      rw [← e₂]

/-- The gluing isomorphism of `StrictPullback.pushforwardDatumThrough` is
`glueOfPreservesBaseChanges` between the chosen factorizations, conjugated by the contractions of
the iterated chosen pullbacks. -/
lemma pushforwardDatumThrough_iso {P : Presieve U} (hPR : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → R f)
    (hP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → PreservesBaseChanges u f) {Y₁ Y₂ Z : 𝒟}
    {h₁ : Y₁ ⟶ u.obj U} (hh₁ : Sieve.generate (P.map u) h₁) {h₂ : Y₂ ⟶ u.obj U}
    (hh₂ : Sieve.generate (P.map u) h₂) (ε : Z ⟶ Y₁) (ε' : Z ⟶ Y₂) (heq : ε ≫ h₁ = ε' ≫ h₂) :
    (pushforwardDatumThrough D hPR hP).iso hh₁ hh₂ ε ε' heq =
      Functor.pullbackFiberCompIso _ _ ε ≪≫
        glueOfPreservesBaseChanges D (hPR (factorizationThrough hh₁).mem)
          (hPR (factorizationThrough hh₂).mem) (hP (factorizationThrough hh₂).mem)
          (ε ≫ (factorizationThrough hh₁).lift) (ε' ≫ (factorizationThrough hh₂).lift) (by
            rw [Category.assoc, Category.assoc, ← (factorizationThrough hh₁).fac,
              ← (factorizationThrough hh₂).fac]
            exact heq) ≪≫
        (Functor.pullbackFiberCompIso _ _ ε').symm := rfl

/-- The object `pushforwardDatumThrough` attaches to the image `u f` of an arrow `f` of `R` is
canonically isomorphic, in the fibre of `p` over `u V`, to the object of `𝒮` underlying what `D`
attaches to `f`: `glueOfPreservesBaseChanges` compares `f` with the member of `P` the chosen
factorization of `u f` goes through. -/
noncomputable def pushforwardObjIsoThrough {P : Presieve U}
    (hPR : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → R f)
    (hP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → PreservesBaseChanges u f)
    (hRP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R f → Sieve.generate (P.map u) (u.map f))
    {V : 𝒞} (f : V ⟶ U) (hf : R f) :
    fiberFib (D.obj f hf) ≅ (pushforwardDatumThrough D hPR hP).obj (u.map f) (hRP hf) :=
  (Functor.pullbackFiberIdIso (fiberFib (D.obj f hf))).symm ≪≫
    glueOfPreservesBaseChanges D hf (hPR (factorizationThrough (hRP hf)).mem)
      (hP (factorizationThrough (hRP hf)).mem) (𝟙 (u.obj V)) (factorizationThrough (hRP hf)).lift
      (by
        rw [Category.id_comp]
        exact (factorizationThrough (hRP hf)).fac)

/-- Base changing `pushforwardObjIsoThrough` along `b` and contracting is
`glueOfPreservesBaseChanges`. -/
lemma pushforwardObjIsoThrough_pullback {P : Presieve U}
    (hPR : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → R f)
    (hP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → PreservesBaseChanges u f)
    (hRP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R f → Sieve.generate (P.map u) (u.map f))
    {V : 𝒞} (f : V ⟶ U) (hf : R f) {Y : 𝒟} (b : Y ⟶ u.obj V) :
    Functor.pullbackFiberHom (pushforwardObjIsoThrough D hPR hP hRP f hf).hom b ≫
        (Functor.pullbackFiberCompIso
          (fiberFib (D.obj (factorizationThrough (hRP hf)).arrow
            (hPR (factorizationThrough (hRP hf)).mem)))
          (factorizationThrough (hRP hf)).lift b).hom =
      (glueOfPreservesBaseChanges D hf (hPR (factorizationThrough (hRP hf)).mem)
        (hP (factorizationThrough (hRP hf)).mem) b (b ≫ (factorizationThrough (hRP hf)).lift) (by
          rw [Category.assoc, ← (factorizationThrough (hRP hf)).fac])).hom := by
  rw [glueOfPreservesBaseChanges_pullback' D hf (hPR (factorizationThrough (hRP hf)).mem)
      (hP (factorizationThrough (hRP hf)).mem) (𝟙 (u.obj V)) (factorizationThrough (hRP hf)).lift
      (by rw [Category.id_comp]; exact (factorizationThrough (hRP hf)).fac) b b
      (b ≫ (factorizationThrough (hRP hf)).lift) (Category.comp_id b) rfl
      (by rw [Category.assoc, ← (factorizationThrough (hRP hf)).fac])]
  simp [pushforwardObjIsoThrough, Iso.trans_hom, Iso.symm_hom, Functor.pullbackFiberHom_comp,
    Functor.pullbackFiberCompIso'_rfl, Category.assoc,
    Functor.pullbackFiberHom_pullbackFiberIdIso_inv_eq]

/-- The gluing isomorphism of `pushforwardDatumThrough` at the image of a pair of morphisms of `𝒞`
is the gluing isomorphism of the datum, through `StrictPullback.core`, conjugated by
`pushforwardObjIsoThrough`. -/
lemma pushforwardDatumThrough_iso_map {P : Presieve U}
    (hPR : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → R f)
    (hP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → PreservesBaseChanges u f)
    (hRP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R f → Sieve.generate (P.map u) (u.map f))
    {V W Z : 𝒞} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) :
    Functor.pullbackFiberHom (pushforwardObjIsoThrough D hPR hP hRP f hf).hom (u.map ε) ≫
        ((pushforwardDatumThrough D hPR hP).iso (hRP hf) (hRP hg) (u.map ε) (u.map ε')
          (by rw [← u.map_comp, ← u.map_comp, heq])).hom =
      (core D hf hg ε ε' heq (𝟙 (u.obj Z)) (u.map ε) (u.map ε') (Category.id_comp _)
          (Category.id_comp _)).hom ≫
        Functor.pullbackFiberHom (pushforwardObjIsoThrough D hPR hP hRP g hg).hom (u.map ε') := by
  rw [pushforwardDatumThrough_iso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  have hlast : u.map ε ≫ u.map f =
      (u.map ε' ≫ (factorizationThrough (hRP hg)).lift) ≫
        u.map (factorizationThrough (hRP hg)).arrow := by
    rw [Category.assoc, ← (factorizationThrough (hRP hg)).fac, ← u.map_comp, ← u.map_comp, heq]
  rw [← Category.assoc, pushforwardObjIsoThrough_pullback D hPR hP hRP f hf (u.map ε),
    ← Category.assoc, glueOfPreservesBaseChanges_cocycle D hf
      (hPR (factorizationThrough (hRP hf)).mem) (hPR (factorizationThrough (hRP hg)).mem)
      (hP (factorizationThrough (hRP hf)).mem) (hP (factorizationThrough (hRP hg)).mem)
      (h₁₃ := hlast)]
  rw [Iso.comp_inv_eq, Category.assoc,
    pushforwardObjIsoThrough_pullback D hPR hP hRP g hg (u.map ε'),
    core_glueOfPreservesBaseChanges_cocycle D hf hg (hPR (factorizationThrough (hRP hg)).mem)
      (hP (factorizationThrough (hRP hg)).mem) (h₁₃ := hlast)]

end Datum

/-- **Effective descent for the pushforward, along a covering with fibre products.** Let `R` be
a sieve of `U` and `P ≤ R` a family whose members have fibre products with every morphism of `𝒞`,
with which `u` commutes, and such that `u` sends every arrow of `R` into the sieve generated by
`u(P)`. If that sieve is a covering sieve of `(𝒟, K)` along which descent in `𝒮` is effective,
every descent datum for `u^p𝒮` relative to `R` is effective.

The proof transports the datum to the sieve generated by `u(P)`
(`StrictPullback.pushforwardDatumThrough`), descends it, and reads the compatibility of the
resulting cartesian morphisms with the given gluing isomorphisms back through
`StrictPullback.pushforwardObjIsoThrough` and `StrictPullback.core_id_map`. -/
theorem isEffective_of_preservesBaseChanges (K : GrothendieckTopology 𝒟)
    (hp : Functor.HasEffectiveDescent p K) {U : 𝒞} {R : Sieve U}
    (D : Functor.SieveDescentDatum (structureFunctor u p) R) {P : Presieve U}
    (hPR : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → R f)
    (hP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, P f → PreservesBaseChanges u f)
    (hRP : ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R f → Sieve.generate (P.map u) (u.map f))
    (hcov : Sieve.generate (P.map u) ∈ K (u.obj U)) :
    D.IsEffective := by
  obtain ⟨X, ζ, hζ, hcompat⟩ := hp _ hcov (pushforwardDatumThrough D hPR hP)
  have hη : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      p.IsStronglyCartesian (u.map f)
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP f hf).hom ≫
          ζ (u.map f) (hRP hf)) := by
    intro V f hf
    have hθ : p.IsHomLift (𝟙 (u.obj V))
        (Functor.Fiber.fiberInclusion.mapIso (pushforwardObjIsoThrough D hPR hP hRP f hf)).hom :=
      (pushforwardObjIsoThrough D hPR hP hRP f hf).hom.2
    have hθs : p.IsStronglyCartesian (𝟙 (u.obj V))
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP f hf).hom) :=
      have := hθ
      Functor.IsStronglyCartesian.of_iso p _
        (Functor.Fiber.fiberInclusion.mapIso (pushforwardObjIsoThrough D hPR hP hRP f hf))
    have hζc : p.IsCartesian (u.map f) (ζ (u.map f) (hRP hf)) := hζ _ (hRP hf)
    have hζs : p.IsStronglyCartesian (u.map f) (ζ (u.map f) (hRP hf)) := inferInstance
    have h : p.IsStronglyCartesian (𝟙 (u.obj V) ≫ u.map f)
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP f hf).hom ≫
          ζ (u.map f) (hRP hf)) := inferInstance
    rwa [Category.id_comp] at h
  have hsc : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      p.IsStronglyCartesian (u.map (eqToHom (D.obj f hf).2 ≫ f))
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP f hf).hom ≫
          ζ (u.map f) (hRP hf)) := by
    intro V f hf
    rw [u.map_comp, eqToHom_map]
    exact Functor.IsStronglyCartesian.eqToHom_comp _ _ _ (hη f hf)
  let φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (D.obj f hf).1 ⟶ (fiberMk X).1 := fun _ f hf =>
    homMk' (X := (D.obj f hf).1) (Y := (fiberMk X).1) (eqToHom (D.obj f hf).2 ≫ f)
      (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP f hf).hom ≫
        ζ (u.map f) (hRP hf)) (hsc f hf).toIsHomLift
  have hξ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (structureFunctor u p).IsCartesian f (φ f hf) := by
    intro V f hf
    have h1 := isStronglyCartesian_of_fib' (φ f hf) (hsc f hf)
    have := Functor.IsStronglyCartesian.of_eqToHom_comp (D.obj f hf).2 f _ h1
    infer_instance
  refine ⟨fiberMk X, φ, fun {V} f hf => hξ f hf, ?_⟩
  intro V W Z f hf g hg ε ε' heq
  have hue : u.map ε ≫ u.map f = u.map ε' ≫ u.map g := by
    rw [← u.map_comp, ← u.map_comp, heq]
  -- the compatibility of the *descended* gluing isomorphisms, read back along
  -- `pushforwardObjIsoThrough`
  have hQ' : Functor.Fiber.fiberInclusion.map
        (core D hf hg ε ε' heq (𝟙 (u.obj Z)) (u.map ε) (u.map ε') (Category.id_comp _)
          (Category.id_comp _)).hom ≫
        Functor.IsPreFibered.pullbackMap (fiberFib (D.obj g hg)).2 (u.map ε') ≫
          (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP g hg).hom ≫
            ζ (u.map g) (hRP hg)) =
      Functor.IsPreFibered.pullbackMap (fiberFib (D.obj f hf)).2 (u.map ε) ≫
        (Functor.Fiber.fiberInclusion.map (pushforwardObjIsoThrough D hPR hP hRP f hf).hom ≫
          ζ (u.map f) (hRP hf)) := by
    have hc := hcompat (hRP hf) (hRP hg) (u.map ε) (u.map ε') hue
    have hPmap := congrArg Functor.Fiber.fiberInclusion.map
      (pushforwardDatumThrough_iso_map D hPR hP hRP hf hg ε ε' heq)
    simp only [Functor.map_comp] at hPmap
    rw [← Functor.pullbackFiberHom_fac_assoc
        (pushforwardObjIsoThrough D hPR hP hRP g hg).hom (u.map ε'),
      ← Functor.pullbackFiberHom_fac_assoc
        (pushforwardObjIsoThrough D hPR hP hRP f hf).hom (u.map ε),
      ← hc, reassoc_of% hPmap]
  -- and its translation into the gluing isomorphisms of `D` itself
  rw [core_id_map D hf hg ε ε' heq] at hQ'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    fiberFibPullbackIso_inv_fac_assoc, fiberInclusion_map_fiberFibFunctor_map] at hQ'
  rw [← fiberFibPullbackIso_hom_fac_assoc (D.obj f hf) ε] at hQ'
  refine hom_ext_of_fib (ε ≫ f) _ _ ?_ ?_ ?_
  · have hdiso : (structureFunctor u p).IsHomLift (𝟙 Z)
        (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) :=
      (D.iso hf hg ε ε' heq).hom.2
    have hpg : (structureFunctor u p).IsCartesian ε'
        (Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε') :=
      Functor.IsPreFibered.pullbackMap.IsCartesian _ _
    have hg' := hξ g hg
    have h : (structureFunctor u p).IsHomLift (𝟙 Z ≫ ε' ≫ g)
        (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
          Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ φ g hg) :=
      inferInstance
    rwa [Category.id_comp, ← heq] at h
  · have hpf : (structureFunctor u p).IsCartesian ε
        (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε) :=
      Functor.IsPreFibered.pullbackMap.IsCartesian _ _
    have hf' := hξ f hf
    infer_instance
  · simpa only [φ, comp_fib, homMk'_fib, Category.assoc] using (cancel_epi
      (Functor.Fiber.fiberInclusion.map (fiberFibPullbackIso (D.obj f hf) ε).hom)).1 hQ'

end StrictPullback

end CategoryTheory
