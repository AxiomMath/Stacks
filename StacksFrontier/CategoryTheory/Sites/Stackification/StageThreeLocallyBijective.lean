module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeMorSheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProduct

/-!
# Clause (1) of Stacks 02ZN: the morphism presheaves are sheafified

Clause (1) of Stacks 02ZN asserts, for the 1-morphism `G : 𝒳 ⥤ 𝒳'` from a fibred category into
its stackification, that the induced map of morphism presheaves
`Mor(x, y) ⟶ Mor(G x, G y)` of Stacks 042V identifies the target with the sheafification of the
source, i.e. is locally injective and locally surjective.

The file first proves a **criterion** that turns the two conditions into statements about
morphisms of the total categories, where the three stages of the construction of the
stackification state their results:

* local injectivity of `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` follows from
  the implication "`F u = F v` implies `u` and `v` are locally equal"
  (`CategoryTheory.Functor.isLocallyInjective_morPresheafMap`);
* local surjectivity follows from "every morphism between objects in the image of `F` is, on a
  covering sieve of the base, the image of a morphism"
  (`CategoryTheory.Functor.isLocallySurjective_morPresheafMap`).

Both are proved by reading a section of `Mor(x, y)` over `g : 𝒞/U` in the total category through
`CategoryTheory.Functor.morSectionHom`, exactly as in `StageTwoMorSheaf.lean`, and testing
against the chosen restriction maps `CategoryTheory.Functor.pullbackFiberMap`.

The criterion is then fed with the two elementary statements for each of the two remaining stages:

* for the composite of the first two stages, `CategoryTheory.Functor.toStageTwo_map_eq_iff` and
  `CategoryTheory.Functor.exists_covering_toStageTwo_map_comp` (the latter proved here from
  `CategoryTheory.Functor.exists_covering_toMorPlus_map_comp` and fullness of
  `CategoryTheory.Functor.toMorQuotient`);
* for the third stage, `CategoryTheory.Functor.locallyEqual_of_toDescentPair_map_eq` and
  `CategoryTheory.Functor.exists_covering_toDescentPair_map_comp`, both proved here from the
  description of `CategoryTheory.Functor.DescentMor` as a quotient of morphism data defined on a
  covering sieve.

The two halves are combined with `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_comp`
and Mathlib's `CategoryTheory.Presheaf.isLocallyInjective_comp` and
`CategoryTheory.Presheaf.isLocallySurjective_comp`.

## Main results

* `CategoryTheory.Functor.isLocallyInjective_morPresheafMap` and
  `CategoryTheory.Functor.isLocallySurjective_morPresheafMap`, the criterion;
* `CategoryTheory.Functor.exists_covering_toStageTwo_map_comp`,
  `CategoryTheory.Functor.locallyEqual_of_toDescentPair_map_eq` and
  `CategoryTheory.Functor.exists_covering_toDescentPair_map_comp`, the elementary inputs;
* `CategoryTheory.Functor.isLocallyBijective_morPresheafMap_toStageThree`, **clause (1) of
  Stacks 02ZN** for the composite of the three stages.

## Obligations that remain before Stacks 02ZN

This file carries no `@[stacks 02ZN]` tag and nothing in it may be read as claiming Stacks 02ZN.
Only clause (1) is proved here; clause (2) is
`CategoryTheory.Functor.essImage_pullbackFiber_toStageThree` in `StageThreeStack.lean`. That the
morphism presheaves of the third stage are sheaves, that descent data for it are effective, and
the assembly of Stacks 02ZN itself, are all still open.
-/

@[expose] public section

universe vb

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

namespace CategoryTheory.Functor

open CategoryTheory Category Opposite

universe v v₂ v₃ u₁ u₂ u₃

/-! ### A functor strictly over the base reflects `IsHomLift` -/

section Reflect

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- A functor `G` strictly over `𝒞` *reflects* `IsHomLift`: if `G φ` lies over `f` for the target
structure functor then `φ` lies over `f` for the source one. This is the converse of
`CategoryTheory.Functor.isHomLift_map_of_comp_eq`. -/
lemma isHomLift_of_isHomLift_map_of_comp_eq {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {G : 𝒳 ⥤ 𝒴}
    (hG : G ⋙ q = p) {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b)
    (h : q.IsHomLift f (G.map φ)) : p.IsHomLift f φ := by
  subst hG
  have := h
  subst_hom_lift q f (G.map φ)
  exact .map φ

/-- If `φ` lies over `f` and `ψ` lies over `g`, then `φ ≫ ψ` lies over any `h` equal to `f ≫ g`. -/
private lemma isHomLift_comp_of_comp_eq {p : 𝒳 ⥤ 𝒞} {R S T : 𝒞} {f : R ⟶ S} {g : S ⟶ T}
    {h : R ⟶ T} (hfg : f ≫ g = h) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [p.IsHomLift f φ]
    [p.IsHomLift g ψ] : p.IsHomLift h (φ ≫ ψ) := by
  subst hfg
  infer_instance

end Reflect

/-! ### The criterion

Throughout this section `F : 𝒳 ⥤ 𝒴` is a 1-morphism of fibred categories over `𝒞`. The morphism
presheaf API of Stacks 042V uses a common hom universe for source and target;
the base hom universe is independent. -/

section Criterion

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒴 : Type u₃} [Category.{v} 𝒴]
  {p : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} [p.IsFibered] [r.IsFibered]
  {J : GrothendieckTopology 𝒞}

/-- The base of the chosen restriction map of `x` along `k : g' ⟶ g`, written out: it is `k.left`,
conjugated by the comparisons of the bases of the two chosen pullbacks with `g'.left` and
`g.left`. -/
lemma map_pullbackFiberMap_eq {U : 𝒞} (x : p.Fiber U) {g g' : Over U} (k : g' ⟶ g) :
    p.map (pullbackFiberMap p x k) =
      eqToHom (pullbackFiber p x g'.hom).2 ≫ k.left ≫
        eqToHom (pullbackFiber p x g.hom).2.symm := by
  have h : p.map (pullbackFiberMap p x k) ≫ eqToHom (pullbackFiber p x g.hom).2 =
      eqToHom (pullbackFiber p x g'.hom).2 ≫ k.left :=
    testBase_pullbackFiberMap (r := p) x k
  rw [← assoc, ← h, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- If `k.left` lies in the transport to `g.left` of a sieve on the base of the chosen pullback of
`x` along `g.hom`, then the chosen restriction map along `k` lies over a member of that sieve. -/
lemma mem_sieve_map_pullbackFiberMap {U : 𝒞} (x : p.Fiber U) {g g' : Over U} (k : g' ⟶ g)
    {S : Sieve (p.obj (pullbackFiber p x g.hom).1)}
    (hk : S.arrows (k.left ≫ eqToHom (pullbackFiber p x g.hom).2.symm)) :
    S.arrows (p.map (pullbackFiberMap p x k)) := by
  rw [map_pullbackFiberMap_eq]
  exact S.downward_closed hk _

/-- A sieve on `g` is covering as soon as it contains every arrow `k` whose chosen restriction map
of `x` lies over a member of a covering sieve of the base of the chosen pullback of `x`. -/
private lemma mem_over_of_forall_pullbackFiberMap {U : 𝒞} (x : p.Fiber U) (g : Over U)
    {S : Sieve (p.obj (pullbackFiber p x g.hom).1)}
    (hS : S ∈ J (p.obj (pullbackFiber p x g.hom).1)) {R : Sieve g}
    (h : ∀ ⦃g' : Over U⦄ (k : g' ⟶ g), S.arrows (p.map (pullbackFiberMap p x k)) → R.arrows k) :
    R ∈ (J.over U) g :=
  (J.over U).superset_covering (fun _ k hk ↦ h k (mem_sieve_map_pullbackFiberMap x k
      ((Sieve.overEquiv_symm_iff _ k).1 hk)))
    (J.overEquiv_symm_mem_over g (S.pullback (eqToHom (pullbackFiber p x g.hom).2.symm))
      (J.pullback_stable _ hS))

/-- **Local injectivity of the map of morphism presheaves of Stacks 042V**, from the statement
that `F` identifies only locally equal morphisms. Two sections of `Mor(x, y)` over `g` with the
same image have the same image under `F` in the total category, hence agree after composing with
every morphism lying over a member of a covering sieve; the chosen restriction maps along the
arrows of the transported sieve are such morphisms. -/
theorem isLocallyInjective_morPresheafMap (hF : IsFibredOneMorphism p r F)
    (hinj : ∀ {a b : 𝒳} (u v : a ⟶ b), F.map u = F.map v → p.LocallyEqual J u v)
    (U : 𝒞) (x y : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap x y) := by
  refine ⟨fun {X} m n h ↦ ?_⟩
  obtain ⟨g⟩ := X
  have h1 : (fiberFunctorOfCompEq hF.comp_eq g.left).map m =
      (fiberFunctorOfCompEq hF.comp_eq g.left).map n := by
    have e := congrArg (fun s ↦ (hF.mapPullbackFiberIso x g.hom).inv ≫ s ≫
      (hF.mapPullbackFiberIso y g.hom).hom) h
    simpa using e
  have h2 : F.map (Fiber.fiberInclusion.map m) = F.map (Fiber.fiberInclusion.map n) := by
    rw [← fiberInclusion_map_fiberFunctorOfCompEq_map hF.comp_eq m,
      ← fiberInclusion_map_fiberFunctorOfCompEq_map hF.comp_eq n, h1]
  obtain ⟨-, R₀, hR₀, hagree⟩ := hinj _ _ h2
  refine mem_over_of_forall_pullbackFiberMap x g hR₀ fun g' k hk ↦ ?_
  change morRestrict p x y k m = morRestrict p x y k n
  refine morSectionHom_injective ?_
  rw [morSectionHom_morRestrict, morSectionHom_morRestrict]
  simp only [morSectionHom]
  rw [← assoc, ← assoc, hagree (pullbackFiberMap p x k) hk]

/-- **Local surjectivity of the map of morphism presheaves of Stacks 042V**, from the statement
that every morphism between objects in the image of `F` is, on a covering sieve of the base, the
image of a morphism. A section of `Mor(F x, F y)` over `g` is, conjugated by the comparison
isomorphisms, a morphism `F (g^* x) ⟶ F (g^* y)`; composing it with the image of the chosen
restriction map along an arrow of the covering sieve exhibits it as `F` of a morphism, and that
morphism, followed by the chosen cartesian lift, is a section of `Mor(x, y)` mapping to the
restriction. -/
theorem isLocallySurjective_morPresheafMap (hF : IsFibredOneMorphism p r F)
    (hsurj : ∀ {a b : 𝒳} (G : F.obj a ⟶ F.obj b), ∃ S ∈ J (p.obj a),
      ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ a), S.arrows (p.map ρ) → ∃ f : w ⟶ b, F.map ρ ≫ G = F.map f)
    (U : 𝒞) (x y : p.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap x y) := by
  refine ⟨fun {g} t ↦ ?_⟩
  set τ : (fiberFunctorOfCompEq hF.comp_eq g.left).obj (pullbackFiber p x g.hom) ⟶
      (fiberFunctorOfCompEq hF.comp_eq g.left).obj (pullbackFiber p y g.hom) :=
    (hF.mapPullbackFiberIso x g.hom).inv ≫ t ≫ (hF.mapPullbackFiberIso y g.hom).hom with hτ
  set t' : F.obj (pullbackFiber p x g.hom).1 ⟶ F.obj (pullbackFiber p y g.hom).1 :=
    Fiber.fiberInclusion.map τ with ht'
  obtain ⟨S, hS, hspec⟩ := hsurj t'
  refine mem_over_of_forall_pullbackFiberMap x g hS fun g' k hk ↦ ?_
  obtain ⟨f, hf⟩ := hspec (pullbackFiberMap p x k) hk
  -- `f` lies over `k.left`, so `f` followed by the chosen cartesian lift lies over `g'.hom`.
  have h1 : r.IsHomLift k.left (F.map (pullbackFiberMap p x k)) :=
    hF.map_isHomLift k.left (pullbackFiberMap p x k)
  have h2 : r.IsHomLift (𝟙 g.left) t' := τ.2
  have hlift0 : r.IsHomLift k.left (F.map f) := by
    rw [← hf]
    exact isHomLift_comp_of_comp_eq (comp_id _) _ _
  have hliftf : p.IsHomLift k.left f :=
    isHomLift_of_isHomLift_map_of_comp_eq hF.comp_eq k.left f hlift0
  have hn : p.IsHomLift g'.hom (f ≫ IsPreFibered.pullbackMap y.2 g.hom) :=
    isHomLift_comp_of_comp_eq (Over.w k) _ _
  obtain ⟨m, hm⟩ := exists_morSectionHom_eq (r := p) (x := x) (y := y) (g := g')
    (f ≫ IsPreFibered.pullbackMap y.2 g.hom)
  refine ⟨m, ?_⟩
  change (hF.morPresheafMap x y).app (op g') m =
    morRestrict r ((fiberFunctorOfCompEq hF.comp_eq U).obj x)
      ((fiberFunctorOfCompEq hF.comp_eq U).obj y) k t
  refine morSectionHom_injective ?_
  rw [morSectionHom_morRestrict]
  -- The two sides, read in `𝒴`.
  have hleft : morSectionHom ((hF.morPresheafMap x y).app (op g') m) =
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso x g'.hom).hom ≫
        F.map f ≫ F.map (IsPreFibered.pullbackMap y.2 g.hom) := by
    simp only [morSectionHom, IsFibredOneMorphism.morPresheafMap_app, unop_op, Functor.map_comp,
      assoc, IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
      fiberInclusion_map_fiberFunctorOfCompEq_map]
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg (fun s ↦ Fiber.fiberInclusion.map (hF.mapPullbackFiberIso x g'.hom).hom ≫
      F.map s) hm
  have hincl : Fiber.fiberInclusion.map t =
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso x g.hom).hom ≫ t' ≫
        Fiber.fiberInclusion.map (hF.mapPullbackFiberIso y g.hom).inv := by
    rw [ht', hτ]
    simp
  have hright : pullbackFiberMap r ((fiberFunctorOfCompEq hF.comp_eq U).obj x) k ≫
      morSectionHom t =
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso x g'.hom).hom ≫
        F.map (pullbackFiberMap p x k) ≫ t' ≫ F.map (IsPreFibered.pullbackMap y.2 g.hom) := by
    simp only [morSectionHom, hincl, assoc,
      IsFibredOneMorphism.mapPullbackFiberIso_inv_fac]
    rw [← assoc (pullbackFiberMap r ((fiberFunctorOfCompEq hF.comp_eq U).obj x) k),
      IsFibredOneMorphism.pullbackFiberMap_mapPullbackFiberIso_hom hF x k, assoc]
  rw [hleft, hright, ← hf]
  simp [assoc]

end Criterion

/-! ### The elementary input for the first two stages

Local injectivity for the composite of the first two stages is
`CategoryTheory.Functor.toStageTwo_map_eq_iff`, proved in `StageTwo.lean`. Local surjectivity is
proved here: the second stage supplies it by
`CategoryTheory.Functor.exists_covering_toMorPlus_map_comp`, and the first stage is full, so no
further covering is needed. -/

section StageTwo

variable {𝒮 : Type u₁} [Category.{vb} 𝒮] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

omit [p.IsFibered] in
/-- **Every morphism of the second stage between objects in the image of the 1-morphism is, on a
covering sieve of the base, the image of a morphism of `𝒳`.** The second stage supplies the
covering sieve; the first stage is the identity on objects and full, so the morphism of the
quotient produced there lifts to `𝒳` outright. -/
theorem exists_covering_toStageTwo_map_comp {a b : 𝒳}
    (G : (p.toStageTwo J).obj a ⟶ (p.toStageTwo J).obj b) :
    ∃ S ∈ J (p.obj a), ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ a), S.arrows (p.map ρ) →
      ∃ f : w ⟶ b, (p.toStageTwo J).map ρ ≫ G = (p.toStageTwo J).map f := by
  obtain ⟨S, hS, hspec⟩ :=
    exists_covering_toMorPlus_map_comp (p := p.morQuotientProj J) (J := J) G
  refine ⟨S, hS, fun w ρ hρ ↦ ?_⟩
  obtain ⟨f', hf'⟩ := hspec ((p.toMorQuotient J).map ρ) hρ
  obtain ⟨f, rfl⟩ := (p.toMorQuotient J).map_surjective f'
  exact ⟨f, hf'⟩

end StageTwo

/-! ### The elementary input for the third stage

A morphism of the third stage between the descent pairs of two objects is represented by a
morphism datum: a covering sieve of the base together with a morphism of fibres for each of its
arrows, compatible with the gluing isomorphisms. Read in the total category, the morphism of
fibres attached to an arrow `a` becomes a morphism `a^* x ⟶ y`
(`CategoryTheory.Functor.DescentPairData.totalMap`), and the compatibility with the gluing
isomorphisms becomes the statement that these morphisms are compatible with restriction
(`CategoryTheory.Functor.DescentPairData.totalMap_restrict`). Local surjectivity is then the
observation that the morphism attached to `p.map ρ` is a preimage of the datum along `ρ`, and
local injectivity is the observation that agreement of two data on a covering sieve is local
equality. -/

section StageThree

variable {𝒮 : Type u₁} [Category.{vb} 𝒮] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

/-- Every morphism `ρ : w ⟶ x` factors through the chosen cartesian lift of `p.map ρ` at `x`, by a
morphism lying over the identity of `p.obj w`. -/
private lemma exists_factor_pullbackMap {x w : 𝒳} (ρ : w ⟶ x) :
    ∃ ρ' : w ⟶ (pullbackFiber p (fiberSelf p x) (p.map ρ)).1,
      p.IsHomLift (𝟙 (p.obj w)) ρ' ∧
        ρ' ≫ IsPreFibered.pullbackMap (fiberSelf p x).2 (p.map ρ) = ρ :=
  ⟨IsStronglyCartesian.map p (p.map ρ)
      (IsPreFibered.pullbackMap (fiberSelf p x).2 (p.map ρ)) (id_comp _).symm ρ, inferInstance,
    IsStronglyCartesian.fac p (p.map ρ) _ (id_comp _).symm ρ⟩

/-- **The 1-morphism into the third stage identifies only locally equal morphisms.** Two morphisms
with the same image are related by agreement of the attached morphisms of fibres on a covering
sieve, and composing those with the chosen cartesian lifts says exactly that the two morphisms
agree after restriction along the arrows of that sieve. -/
theorem locallyEqual_of_toDescentPair_map_eq {x y : 𝒳} (u v : x ⟶ y)
    (h : (toDescentPair p J).map u = (toDescentPair p J).map v) : p.LocallyEqual J u v := by
  obtain ⟨hbase, T, hT, hT₁, hT₂, hagree⟩ :=
    (DescentMor.mk_eq_iff (DescentPairData.ofHom (p := p) (J := J) u)
      (DescentPairData.ofHom v)).mp h
  refine ⟨hbase, T, hT, fun w φ hφ ↦ ?_⟩
  have key : IsPreFibered.pullbackMap (fiberSelf p x).2 (p.map φ) ≫ u =
      IsPreFibered.pullbackMap (fiberSelf p x).2 (p.map φ) ≫ v := by
    have hb' : p.map u = p.map v := hbase
    have e := hagree (p.map φ) hφ (g := p.map φ ≫ p.map u) trivial rfl
      (by simp only [DescentPairData.ofHom_base]; rw [hb'])
    have e2 := congrArg (fun t ↦ Fiber.fiberInclusion.map t ≫
      IsPreFibered.pullbackMap (fiberSelf p y).2 (p.map φ ≫ p.map u)) e
    simpa only [DescentPairData.ofHom_map, pullbackFiberOfHom_fac] using e2
  obtain ⟨φ', -, hφ⟩ := exists_factor_pullbackMap (p := p) φ
  rw [← hφ, assoc, assoc, key]

/-! #### The morphisms of the total category attached by a morphism datum -/

/-- The canonical morphism from the chosen pullback of `x` along `e ≫ a` to the chosen pullback
along `a`, lying over `e`. -/
noncomputable def pullbackFiberRestrictHom (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (x : 𝒳) {V V' : 𝒮}
    (a : V ⟶ p.obj x) (e : V' ⟶ V) :
    (pullbackFiber p (fiberSelf p x) (e ≫ a)).1 ⟶ (pullbackFiber p (fiberSelf p x) a).1 :=
  Fiber.fiberInclusion.map (pullbackFiberIdIso (pullbackFiber p (fiberSelf p x) (e ≫ a))).inv ≫
    Fiber.fiberInclusion.map
      (pullbackFiberComparison (fiberSelf p x) (𝟙 V') e (id_comp (e ≫ a))).hom ≫
    IsPreFibered.pullbackMap (pullbackFiber p (fiberSelf p x) a).2 e

/-- The morphism `CategoryTheory.Functor.pullbackFiberRestrictHom p x a e` lies over `e`. -/
instance isHomLift_pullbackFiberRestrictHom (x : 𝒳) {V V' : 𝒮} (a : V ⟶ p.obj x) (e : V' ⟶ V) :
    p.IsHomLift e (pullbackFiberRestrictHom p x a e) := by
  have h₁ : p.IsHomLift (𝟙 V') (Fiber.fiberInclusion.map
      (pullbackFiberIdIso (pullbackFiber p (fiberSelf p x) (e ≫ a))).inv) :=
    (pullbackFiberIdIso (pullbackFiber p (fiberSelf p x) (e ≫ a))).inv.2
  have h₂ : p.IsHomLift (𝟙 V') (Fiber.fiberInclusion.map
      (pullbackFiberComparison (fiberSelf p x) (𝟙 V') e (id_comp (e ≫ a))).hom) :=
    (pullbackFiberComparison (fiberSelf p x) (𝟙 V') e (id_comp (e ≫ a))).hom.2
  have h0 : p.IsHomLift (𝟙 V' ≫ 𝟙 V' ≫ e) (pullbackFiberRestrictHom p x a e) := by
    simp only [pullbackFiberRestrictHom]
    infer_instance
  rwa [id_comp, id_comp] at h0

/-- The equation that determines `CategoryTheory.Functor.pullbackFiberRestrictHom`. -/
@[reassoc]
lemma pullbackFiberRestrictHom_fac (x : 𝒳) {V V' : 𝒮} (a : V ⟶ p.obj x) (e : V' ⟶ V) :
    pullbackFiberRestrictHom p x a e ≫ IsPreFibered.pullbackMap (fiberSelf p x).2 a =
      IsPreFibered.pullbackMap (fiberSelf p x).2 (e ≫ a) := by
  rw [pullbackFiberRestrictHom, assoc, assoc, pullbackFiberComparison_hom_fac, ← assoc,
    pullbackFiberIdIso_inv_fac, id_comp]

/-- The morphism of the total category attached by a morphism datum of the descent pairs of two
objects to an arrow `a` of its defining sieve: the attached morphism of fibres, followed by the
chosen cartesian lift of `a ≫ base` at the target object. -/
noncomputable def DescentPairData.totalMap {x y : 𝒳}
    (X : DescentPairData (DescentPair.ofObj p J x) (DescentPair.ofObj p J y))
    {V : 𝒮} (a : V ⟶ p.obj x) (ha : X.hom.sieve.arrows a) :
    (pullbackFiber p (fiberSelf p x) a).1 ⟶ y :=
  Fiber.fiberInclusion.map (X.hom.map a ha (g := a ≫ X.base) trivial rfl) ≫
    IsPreFibered.pullbackMap (fiberSelf p y).2 (a ≫ X.base)

/-- `CategoryTheory.Functor.DescentPairData.totalMap` does not depend on which arrow of the target
the composite `a ≫ base` is presented as. -/
lemma DescentPairData.totalMap_eq {x y : 𝒳}
    (X : DescentPairData (DescentPair.ofObj p J x) (DescentPair.ofObj p J y))
    {V : 𝒮} (a : V ⟶ p.obj x) (ha : X.hom.sieve.arrows a)
    {b : V ⟶ p.obj y} (hb : (⊤ : Sieve (p.obj y)).arrows b) (hab : a ≫ X.base = b) :
    Fiber.fiberInclusion.map (X.hom.map a ha hb hab) ≫
        IsPreFibered.pullbackMap (fiberSelf p y).2 b =
      X.totalMap a ha := by
  subst hab
  rfl

/-- The morphism attached to an arrow lies over that arrow composed with the base morphism. -/
lemma DescentPairData.isHomLift_totalMap {x y : 𝒳}
    (X : DescentPairData (DescentPair.ofObj p J x) (DescentPair.ofObj p J y))
    {V : 𝒮} (a : V ⟶ p.obj x) (ha : X.hom.sieve.arrows a) :
    p.IsHomLift (a ≫ X.base) (X.totalMap a ha) := by
  have hm : p.IsHomLift (𝟙 V)
      (Fiber.fiberInclusion.map (X.hom.map a ha (g := a ≫ X.base) trivial rfl)) :=
    (X.hom.map a ha (g := a ≫ X.base) trivial rfl).2
  simp only [DescentPairData.totalMap]
  exact isHomLift_comp_of_comp_eq (id_comp _) _ _

/-- **The morphisms attached by a morphism datum are compatible with restriction.** This is the
compatibility of the datum with the gluing isomorphisms of the two descent pairs, read at the pair
of arrows `(e ≫ a, a)` and the pair of morphisms `(𝟙, e)` and then contracted through the chosen
cartesian lifts. -/
theorem DescentPairData.totalMap_restrict {x y : 𝒳}
    (X : DescentPairData (DescentPair.ofObj p J x) (DescentPair.ofObj p J y))
    {V V' : 𝒮} {a : V ⟶ p.obj x} (ha : X.hom.sieve.arrows a) (e : V' ⟶ V)
    (hea : X.hom.sieve.arrows (e ≫ a)) :
    X.totalMap (e ≫ a) hea = pullbackFiberRestrictHom p x a e ≫ X.totalMap a ha := by
  have hglue := X.hom.map_glue (e ≫ a) hea a ha (g := (e ≫ a) ≫ X.base) trivial rfl
    (g' := a ≫ X.base) trivial rfl (𝟙 V') e (id_comp (e ≫ a))
  have e2 := congrArg (fun s ↦ Fiber.fiberInclusion.map
      (pullbackFiberIdIso (pullbackFiber p (fiberSelf p x) (e ≫ a))).inv ≫
      Fiber.fiberInclusion.map s ≫
      IsPreFibered.pullbackMap (pullbackFiber p (fiberSelf p y) (a ≫ X.base)).2 e ≫
      IsPreFibered.pullbackMap (fiberSelf p y).2 (a ≫ X.base)) hglue
  simp only [SieveDescentDatum.ofFiber_iso, Functor.map_comp, assoc,
    pullbackFiberComparison_hom_fac, pullbackFiberHom_fac_assoc,
    pullbackFiberIdIso_inv_fac_assoc] at e2
  rw [DescentPairData.totalMap, DescentPairData.totalMap, pullbackFiberRestrictHom]
  refine Eq.trans (Category.id_comp _).symm ?_
  simpa only [assoc] using e2

/-- **Every morphism of the third stage between objects in the image of the 1-morphism is, on a
covering sieve of the base, the image of a morphism.** The defining sieve of a representing
morphism datum is the covering sieve, and the preimage of the datum along `ρ` is the morphism the
datum attaches to `p.map ρ`, precomposed with the factorisation of `ρ` through the chosen
cartesian lift. -/
theorem exists_covering_toDescentPair_map_comp {x y : 𝒳}
    (G : (toDescentPair p J).obj x ⟶ (toDescentPair p J).obj y) :
    ∃ S ∈ J (p.obj x), ∀ ⦃w : 𝒳⦄ (ρ : w ⟶ x), S.arrows (p.map ρ) →
      ∃ f : w ⟶ y, (toDescentPair p J).map ρ ≫ G = (toDescentPair p J).map f := by
  obtain ⟨X, rfl⟩ := DescentMor.exists_rep G
  refine ⟨X.hom.sieve, X.hom.sieve_mem, fun w ρ hρmem ↦ ?_⟩
  obtain ⟨ρ', hρ'lift, hρfac⟩ := exists_factor_pullbackMap (p := p) ρ
  have hflift : p.IsHomLift (p.map ρ ≫ X.base) (ρ' ≫ X.totalMap (p.map ρ) hρmem) := by
    have := X.isHomLift_totalMap (p.map ρ) hρmem
    exact isHomLift_comp_of_comp_eq (id_comp _) _ _
  have hfbase : p.map (ρ' ≫ X.totalMap (p.map ρ) hρmem) = p.map ρ ≫ X.base := by
    have := hflift
    simpa using IsHomLift.fac' p (p.map ρ ≫ X.base) (ρ' ≫ X.totalMap (p.map ρ) hρmem)
  refine ⟨ρ' ≫ X.totalMap (p.map ρ) hρmem, ?_⟩
  refine (DescentMor.mk_eq_iff ((DescentPairData.ofHom ρ).comp X)
    (DescentPairData.ofHom (ρ' ≫ X.totalMap (p.map ρ) hρmem))).mpr
    (DescentPairData.rel_of_agree ?_ ?_)
  · exact hfbase.symm
  intro V' d hd hd' k hk h h'
  obtain rfl : (d ≫ p.map ρ) ≫ X.base = k := (assoc _ _ _).trans h
  have hd₂ : X.hom.sieve.arrows (d ≫ p.map ρ) := hd.2
  refine fiber_hom_ext_of_cartesian ((d ≫ p.map ρ) ≫ X.base)
    (IsPreFibered.pullbackMap (fiberSelf p y).2 ((d ≫ p.map ρ) ≫ X.base))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  -- The left-hand side, read in `𝒳`: the restriction map of `ρ`, followed by the morphism the
  -- datum attaches to `d ≫ p.map ρ`, which is the one it attaches to `p.map ρ` restricted.
  have hL : Fiber.fiberInclusion.map (((DescentPairData.ofHom ρ).comp X).hom.map d hd hk h) ≫
        IsPreFibered.pullbackMap (fiberSelf p y).2 ((d ≫ p.map ρ) ≫ X.base) =
      Fiber.fiberInclusion.map (pullbackFiberOfHom ρ d (d ≫ p.map ρ) rfl) ≫
        (pullbackFiberRestrictHom p x (p.map ρ) d ≫ X.totalMap (p.map ρ) hρmem) := by
    have hstep : ((DescentPairData.ofHom ρ).comp X).hom.map d hd hk h =
        pullbackFiberOfHom ρ d (d ≫ p.map ρ) rfl ≫ X.hom.map (d ≫ p.map ρ) hd₂ hk rfl :=
      DescentPairData.comp_hom_map (DescentPairData.ofHom ρ) X d hd.1 hd₂ hk rfl hd h
    rw [← DescentPairData.totalMap_restrict X hρmem d hd₂, hstep, Functor.map_comp, assoc]
    exact congrArg
      (fun s ↦ Fiber.fiberInclusion.map (pullbackFiberOfHom ρ d (d ≫ p.map ρ) rfl) ≫ s)
      (DescentPairData.totalMap_eq X (d ≫ p.map ρ) hd₂ hk rfl)
  -- The right-hand side, read in `𝒳`.
  have hR : Fiber.fiberInclusion.map (pullbackFiberOfHom (ρ' ≫ X.totalMap (p.map ρ) hρmem) d
        ((d ≫ p.map ρ) ≫ X.base) h') ≫
        IsPreFibered.pullbackMap (fiberSelf p y).2 ((d ≫ p.map ρ) ≫ X.base) =
      IsPreFibered.pullbackMap (fiberSelf p w).2 d ≫ ρ' ≫ X.totalMap (p.map ρ) hρmem :=
    pullbackFiberOfHom_fac _ _ _ _
  rw [hL]
  refine Eq.trans ?_ hR.symm
  rw [← assoc, ← assoc]
  refine congrArg (fun s ↦ s ≫ X.totalMap (p.map ρ) hρmem) ?_
  have hlL : p.IsHomLift d (Fiber.fiberInclusion.map
      (pullbackFiberOfHom ρ d (d ≫ p.map ρ) rfl) ≫ pullbackFiberRestrictHom p x (p.map ρ) d) := by
    have hA : p.IsHomLift (𝟙 V')
        (Fiber.fiberInclusion.map (pullbackFiberOfHom ρ d (d ≫ p.map ρ) rfl)) :=
      (pullbackFiberOfHom ρ d (d ≫ p.map ρ) rfl).2
    exact isHomLift_comp_of_comp_eq (id_comp _) _ _
  have hlR : p.IsHomLift d (IsPreFibered.pullbackMap (fiberSelf p w).2 d ≫ ρ') :=
    isHomLift_comp_of_comp_eq (comp_id _) _ _
  have := hlL
  have := hlR
  refine IsStronglyCartesian.ext p (p.map ρ)
    (IsPreFibered.pullbackMap (fiberSelf p x).2 (p.map ρ)) d ?_
  rw [assoc, pullbackFiberRestrictHom_fac, pullbackFiberOfHom_fac, assoc, hρfac]

end StageThree

/-! ### Clause (1) of Stacks 02ZN

The two halves are combined at the level of presheaves, by
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_comp` and the composition instances for
local injectivity and local surjectivity: the elementary statement for the second stage cannot be
composed with the one for the third directly, because the covering sieve on which a morphism of
the third stage descends to the second depends on the morphism, and the further covering on which
that descends to `𝒴` depends on it in turn.

The source and target use the common hom universe `max t₁ t₂ w vb`, which
absorbs the universes needed for descent data. The base has the independent hom universe
`vb`, so this result also applies when the base objects are in a larger universe than
its morphisms. No `UnivLE` hypothesis is needed. -/

section Clause

universe w t₁ t₂

variable {𝒞 : Type t₁} [Category.{vb} 𝒞] {𝒴 : Type t₂} [Category.{max t₁ t₂ w vb} 𝒴]
  (q : 𝒴 ⥤ 𝒞) [q.IsFibered] (J : GrothendieckTopology 𝒞)

/-- **Clause (1) of Stacks 02ZN for the composite of the three stages.** For every object `U` of
the base and all objects `x`, `y` of the fibre of `𝒴` over `U`, the map of morphism presheaves on
`𝒞/U` induced by `CategoryTheory.Functor.toStageThree` is locally injective and locally
surjective; that is, it exhibits `Mor(G x, G y)` as the sheafification of `Mor(x, y)`.

The first two stages contribute `CategoryTheory.Functor.toStageTwo_map_eq_iff` and
`CategoryTheory.Functor.exists_covering_toStageTwo_map_comp`, the third
`CategoryTheory.Functor.locallyEqual_of_toDescentPair_map_eq` and
`CategoryTheory.Functor.exists_covering_toDescentPair_map_comp`. -/
theorem isLocallyBijective_morPresheafMap_toStageThree (U : 𝒞) (x y : q.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U)
        ((isFibredOneMorphism_toStageThree q J).morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U)
        ((isFibredOneMorphism_toStageThree q J).morPresheafMap x y) := by
  have hN := isFibredOneMorphism_toStageTwo q J
  have hM := isFibredOneMorphism_toDescentPair (q.stageTwoProj J) J
  have hNinj : Presheaf.IsLocallyInjective (J.over U) (hN.morPresheafMap x y) :=
    isLocallyInjective_morPresheafMap hN (fun u v h ↦ (toStageTwo_map_eq_iff u v).mp h) U x y
  have hNsurj : Presheaf.IsLocallySurjective (J.over U) (hN.morPresheafMap x y) :=
    isLocallySurjective_morPresheafMap hN (fun G ↦ exists_covering_toStageTwo_map_comp G) U x y
  have hMinj : Presheaf.IsLocallyInjective (J.over U)
      (hM.morPresheafMap ((fiberFunctorOfCompEq hN.comp_eq U).obj x)
        ((fiberFunctorOfCompEq hN.comp_eq U).obj y)) :=
    isLocallyInjective_morPresheafMap hM
      (fun u v h ↦ locallyEqual_of_toDescentPair_map_eq u v h) U _ _
  have hMsurj : Presheaf.IsLocallySurjective (J.over U)
      (hM.morPresheafMap ((fiberFunctorOfCompEq hN.comp_eq U).obj x)
        ((fiberFunctorOfCompEq hN.comp_eq U).obj y)) :=
    isLocallySurjective_morPresheafMap hM
      (fun G ↦ exists_covering_toDescentPair_map_comp G) U _ _
  have hcomp := IsFibredOneMorphism.morPresheafMap_comp hN hM x y
  refine ⟨?_, ?_⟩
  · have h : Presheaf.IsLocallyInjective (J.over U) ((hN.comp hM).morPresheafMap x y) := by
      rw [← hcomp]; infer_instance
    exact h
  · have h : Presheaf.IsLocallySurjective (J.over U) ((hN.comp hM).morPresheafMap x y) := by
      rw [← hcomp]; infer_instance
    exact h

end Clause

end CategoryTheory.Functor
