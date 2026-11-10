module

public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# The stackification of a 2-fibre product is the 2-fibre product of the stackifications

This file proves Stacks 04Y1 for fibred categories: if `i : 𝒳 ⥤ 𝒳'`, `j : 𝒴 ⥤ 𝒴'` and
`k : 𝒵 ⥤ 𝒵'` are stackifications of the three corners of a cospan `𝒳 ⥤ 𝒴 ⟵ 𝒵` of fibred
categories over a site `(𝒞, J)`, then the canonical 1-morphism `𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'` is a
stackification of `𝒳 ×_𝒴 𝒵`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.stackifyMap`, the canonical 1-morphism
  `(U, x, z, φ) ↦ (U, i x, k z, α_x ≫ j φ ≫ β_z⁻¹)`, and
  `CategoryTheory.TwoFibreProductOver.isFibredOneMorphism_stackifyMap`, that it is a 1-morphism of
  fibred categories over `𝒞`.

## Main results

* `CategoryTheory.TwoFibreProductOver.isLocallyBijective_morPresheafMap_stackifyMap`, clause (1);
* `CategoryTheory.TwoFibreProductOver.exists_covering_stackifyMap`, clause (2);
* `CategoryTheory.TwoFibreProductOver.isStackification_stackifyMap`: Stacks 04Y1.

## Implementation notes

The 2-fibre product is the one taken in the 2-category of categories over `𝒞`,
`CategoryTheory.TwoFibreProductOver` (Stacks 0040): its objects are the quadruples `(U, x, z, φ)`
with `x` over `U`, `z` over `U` and `φ : f x ≅ g z` *vertical* over `U`. That its structure functor
is again a fibred category is Stacks 02XQ
(`CategoryTheory.TwoFibreProductOver.isFibered_structureFunctor`), which is invoked inside the
statement, for both 2-fibre products, to supply the fibredness instances the presheaves
`Mor(·, ·)` are built from; that it is a stack is Stacks 026G
(`CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`). The fibredness of `𝒳'`, `𝒴'`,
`𝒵'` is not a separate hypothesis: it is part of `CategoryTheory.Functor.IsStack`.

"`i` is a stackification" is spelled out from the two conditions of Stacks 02ZP rather than
referred to a predicate, there being none in the tree yet — Stacks 02ZN is not formalized — and the
two conditions are then repeated verbatim for the canonical 1-morphism in the conclusion, so that
hypothesis and conclusion assert one and the same notion. It is the spelling of Stacks 04Y2
(`CategoryTheory.TwoFibreProductOver.isStackification_of_isStackification`), the same statement for
categories fibred in groupoids, and of Stacks 06NS:

* Condition (1) is read through the canonical map of Stacks 042V,
  `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, between the presheaves `Mor(x, y)`
  of Stacks 02ZB on the slice `𝒞/U`. "Identifies the target with the sheafification of the source"
  is stated as: the map is locally injective and locally surjective for the induced topology
  `J.over U`, the target being a sheaf. That is the standard characterisation of a sheafification
  map (`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`), and it is used in place of an
  isomorphism from a sheafification functor because `Mor(x, y)` is valued in the hom-universe of
  the fibred category, which Mathlib's sheafification of type-valued presheaves does not
  accommodate. That the target is a sheaf is not repeated as a clause: on the hypothesis side it is
  `hs𝒳'.isMorSheaf` and on the conclusion side it is the `IsStack` conjunct.
* Condition (2) is read in sieve language and without chosen pullbacks: for every object `x'` there
  is a covering sieve `R` of `p𝒳'.obj x'` such that for each `u : V ⟶ p𝒳'.obj x'` in `R` there are
  an object `x` of `𝒳` and a morphism `i x ⟶ x'` strongly cartesian over `u`. Giving such a
  morphism is the same as giving an isomorphism `u^* x' ≅ i x` in the fibre over `V`, cartesian
  lifts being unique up to unique vertical isomorphism, so this is "`x'|_V` is in the essential
  image of `𝒳_V ⥤ 𝒳'_V`".

The source states the conclusion as an equivalence: it names `𝒲` the stackification of
`𝒳 ×_𝒴 𝒵`, obtains from the canonical 1-morphism `𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'` an induced
`h : 𝒲 ⥤ 𝒳' ×_{𝒴'} 𝒵'` by the universal property of the stackification (Stacks 0435), and shows
`h` to be an equivalence by checking that it is bijective on `Mor`-sheaves and that every object of
the target is locally in its essential image (Stacks 04WQ, Stacks 046N). Here the conclusion is
instead that the canonical 1-morphism is itself a stackification. The two assert the same thing:
`𝒳 ×_𝒴 𝒵 ⥤ 𝒲` satisfies the two conditions of Stacks 02ZP, so for the composite
`𝒳 ×_𝒴 𝒵 ⥤ 𝒲 ⥤ 𝒳' ×_{𝒴'} 𝒵'` those two conditions hold if and only if they hold for `h`, and for
a 1-morphism of stacks they hold if and only if it is an equivalence over `𝒞` (Stacks 04WQ,
Stacks 046N again). Phrasing it without `𝒲` keeps the existence of the stackification of
`𝒳 ×_𝒴 𝒵` (Stacks 02ZN) out of a statement that does not otherwise use it.

The source's route uses clause (1) of the stackification hypothesis on `j` — that
`Mor(f x, g z) ⟶ Mor(j f x, j g z)` is locally bijective, which is what makes the comparison
isomorphism of an object of `𝒳' ×_{𝒴'} 𝒵'` locally come from an isomorphism of `𝒴` — but not
clause (2) for `j`; that clause (`hobj𝒴`) is nevertheless part of the hypothesis, because it is
what makes `𝒴'` *the* stackification of `𝒴` rather than merely a stack receiving a map that
sheafifies the morphism presheaves, and Stacks 04Y1 is a statement about the stackifications.

The hom-universes of all seven categories are one and the same `v`, the universes of objects being
left independent: a map `Mor(x, y) ⟶ Mor(i x, i y)` is a map of presheaves valued in the
hom-universes of the source and of the target respectively, so the map of Stacks 042V exists
without a universe lift only when those agree, and the 2-fibre product has the hom-universe
assembled from those of `𝒞` and of the two factors.
-/

@[expose] public section

universe vb

-- The endpoints of the chosen cartesian lifts compared below are spelled through
-- `Functor.pullbackFiber`, `Functor.Fiber.fiberInclusion` and `Functor.fiberFunctorOfCompEq`, so
-- the instance arguments of `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Opposite

/-! ### Maps of fibre products of presheaves of types

A map of cospans of presheaves of types induces a map of the fibre products
`CategoryTheory.Presheaf.eqPullback`, and that map is locally injective as soon as the two outer
legs are, and locally surjective as soon as the two outer legs are locally surjective and the
middle one is locally injective: a pair of local preimages of the two components of a section
satisfies the fibre product condition after a further covering, because its image under the middle
map does and the middle map is locally injective. -/

namespace Presheaf

universe w v' u'

variable {D : Type u'} [Category.{v'} D] {A₁ A₂ CA B₁ B₂ CB : Dᵒᵖ ⥤ Type w}

/-- Application of a composite of maps of presheaves of types to a section. -/
lemma comp_app_apply {P Q R : Dᵒᵖ ⥤ Type w} (φ : P ⟶ Q) (ψ : Q ⟶ R) (d : Dᵒᵖ) (s : P.obj d) :
    (φ ≫ ψ).app d s = ψ.app d (φ.app d s) := by simp

section

/-- Two composites of maps of presheaves of types that are equal as maps agree on sections. -/
private lemma app_apply_eq_of_comp_eq {P Q R S : Dᵒᵖ ⥤ Type w} {a : P ⟶ Q} {b : Q ⟶ S}
    {c : P ⟶ R} {d : R ⟶ S} (h : a ≫ b = c ≫ d) (X : Dᵒᵖ) (s : P.obj X) :
    b.app X (a.app X s) = d.app X (c.app X s) := by
  rw [← comp_app_apply a b, h, comp_app_apply]

variable (uA : A₁ ⟶ CA) (vA : A₂ ⟶ CA) (uB : B₁ ⟶ CB) (vB : B₂ ⟶ CB)
  (l₁ : A₁ ⟶ B₁) (l₂ : A₂ ⟶ B₂) (lC : CA ⟶ CB)
  (h₁ : l₁ ≫ uB = uA ≫ lC) (h₂ : l₂ ≫ vB = vA ≫ lC)

include h₁ h₂

/-- The map of fibre products induced by a map of cospans of presheaves of types. -/
def eqPullbackMap : eqPullback uA vA ⟶ eqPullback uB vB where
  app d := ↾fun ab ↦ ⟨(l₁.app d ab.val.1, l₂.app d ab.val.2), by
    have e₁ : uB.app d (l₁.app d ab.val.1) = lC.app d (uA.app d ab.val.1) := by
      rw [← comp_app_apply l₁ uB, h₁, comp_app_apply]
    have e₂ : vB.app d (l₂.app d ab.val.2) = lC.app d (vA.app d ab.val.2) := by
      rw [← comp_app_apply l₂ vB, h₂, comp_app_apply]
    rw [e₁, e₂, ab.2]⟩
  naturality {d d'} h := by
    ext ab
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact l₁.naturality_apply h ab.val.1
    · exact l₂.naturality_apply h ab.val.2

/-- The first component of the image of a section under `eqPullbackMap` is the image of its first
component under `l₁`. -/
@[simp]
lemma eqPullbackMap_app_fst (d : Dᵒᵖ) (ab : (eqPullback uA vA).obj d) :
    ((eqPullbackMap uA vA uB vB l₁ l₂ lC h₁ h₂).app d ab).val.1 = l₁.app d ab.val.1 := rfl

/-- The second component of the image of a section under `eqPullbackMap` is the image of its second
component under `l₂`. -/
@[simp]
lemma eqPullbackMap_app_snd (d : Dᵒᵖ) (ab : (eqPullback uA vA).obj d) :
    ((eqPullbackMap uA vA uB vB l₁ l₂ lC h₁ h₂).app d ab).val.2 = l₂.app d ab.val.2 := rfl

variable (J : GrothendieckTopology D)

/-- The induced map of fibre products is locally injective as soon as the two outer legs are:
two sections agreeing after it have componentwise locally equal restrictions, and a section of a
fibre product is determined by its two components. -/
lemma isLocallyInjective_eqPullbackMap [IsLocallyInjective J l₁] [IsLocallyInjective J l₂] :
    IsLocallyInjective J (eqPullbackMap uA vA uB vB l₁ l₂ lC h₁ h₂) where
  equalizerSieve_mem {X} s t h := by
    have h1 : l₁.app X s.val.1 = l₁.app X t.val.1 := congrArg (fun w ↦ w.val.1) h
    have h2 : l₂.app X s.val.2 = l₂.app X t.val.2 := congrArg (fun w ↦ w.val.2) h
    refine J.superset_covering ?_ (J.intersection_covering
      (equalizerSieve_mem J l₁ _ _ h1) (equalizerSieve_mem J l₂ _ _ h2))
    intro Y f hf
    exact Subtype.ext (Prod.ext hf.1 hf.2)

/-- The induced map of fibre products is locally surjective as soon as the two outer legs are and
the middle leg is locally injective. Given a section of the target, its two components lift locally
along `l₁` and `l₂`; the two lifts have the same image under `lC` in `CA`, because the images of
those images in `CB` agree, so they agree after a further covering, and then the pair is a section
of the source. -/
lemma isLocallySurjective_eqPullbackMap [IsLocallySurjective J l₁] [IsLocallySurjective J l₂]
    [IsLocallyInjective J lC] :
    IsLocallySurjective J (eqPullbackMap uA vA uB vB l₁ l₂ lC h₁ h₂) where
  imageSieve_mem {X} b := by
    refine J.transitive (J.intersection_covering
      (imageSieve_mem J l₁ b.val.1) (imageSieve_mem J l₂ b.val.2)) _ ?_
    intro Y f hf
    obtain ⟨a₁, ha₁⟩ := hf.1
    obtain ⟨a₂, ha₂⟩ := hf.2
    have hb : uB.app (op X) b.val.1 = vB.app (op X) b.val.2 := b.2
    have hkey : lC.app (op Y) (uA.app (op Y) a₁) = lC.app (op Y) (vA.app (op Y) a₂) := by
      rw [← app_apply_eq_of_comp_eq h₁, ← app_apply_eq_of_comp_eq h₂, ha₁, ha₂,
        uB.naturality_apply, vB.naturality_apply, hb]
    rw [pullback_imageSieve]
    refine J.superset_covering ?_ (equalizerSieve_mem J lC _ _ hkey)
    intro Z g hg
    refine ⟨⟨(A₁.map g.op a₁, A₂.map g.op a₂), ?_⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · rw [uA.naturality_apply, vA.naturality_apply]
      exact hg
    · change l₁.app (op Z) (A₁.map g.op a₁) = B₁.map g.op (B₁.map f.op b.val.1)
      rw [l₁.naturality_apply, ha₁]
    · change l₂.app (op Z) (A₂.map g.op a₂) = B₂.map g.op (B₂.map f.op b.val.2)
      rw [l₂.naturality_apply, ha₂]

end

end Presheaf

/-! ### Composites of 1-morphisms and the maps of morphism presheaves

The comparison isomorphisms of `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`
compose, and so do the induced maps of morphism presheaves; moreover the map induced by a
1-morphism is compatible with the functoriality of `Mor(x, y)` in the two objects of the fibre, and
two 1-morphisms related by a vertical 2-isomorphism induce the same map up to the isomorphism of
morphism presheaves that the 2-isomorphism produces. These are the three formal properties of
Stacks 042V that the argument below runs on. -/

namespace Functor

universe v u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{vb} 𝒞]

/-- A morphism strongly cartesian over `f ≫ eqToHom h` is strongly cartesian over `f`.

This is `CategoryTheory.Functor.isStronglyCartesian_of_comp_eqToHom` of
`StacksFrontier.CategoryTheory.FiberedCategory.Splitting`, with the base morphism and the morphism
explicit; it is kept private here so that the two do not clash in one environment. -/
private lemma isStronglyCartesian_of_comp_eqToHom {𝒜 : Type u₂} [Category.{v} 𝒜] {q : 𝒜 ⥤ 𝒞}
    {R T T' : 𝒞} (h : T = T') {a b : 𝒜} (f : R ⟶ T) (φ : a ⟶ b)
    (hφ : q.IsStronglyCartesian (f ≫ eqToHom h) φ) : q.IsStronglyCartesian f φ := by
  subst h
  simpa using hφ

namespace IsFibredOneMorphism

variable {𝒜 : Type u₂} [Category.{v} 𝒜] {ℬ : Type u₃} [Category.{v} ℬ] {𝒟 : Type u₄}
  [Category.{v} 𝒟] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {t : 𝒟 ⥤ 𝒞}

section Comp

variable {N : 𝒜 ⥤ ℬ} {M : ℬ ⥤ 𝒟} [q.IsFibered] [r.IsFibered] [t.IsFibered]

/-- The comparison isomorphisms of two 1-morphisms compose to the comparison isomorphism of the
composite: both carry the image of the chosen cartesian lift to the chosen cartesian lift. -/
lemma mapPullbackFiberIso_comp (hN : q.IsFibredOneMorphism r N) (hM : r.IsFibredOneMorphism t M)
    {U : 𝒞} (a : q.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    ((hN.comp hM).mapPullbackFiberIso a f).hom =
      (hM.mapPullbackFiberIso ((fiberFunctorOfCompEq hN.comp_eq U).obj a) f).hom ≫
        (fiberFunctorOfCompEq hM.comp_eq V).map (hN.mapPullbackFiberIso a f).hom := by
  have hcart : r.IsStronglyCartesian f (N.map (IsPreFibered.pullbackMap a.2 f)) :=
    hN.map_isStronglyCartesian f _ inferInstance
  have hcart' : t.IsStronglyCartesian f (M.map (N.map (IsPreFibered.pullbackMap a.2 f))) :=
    hM.map_isStronglyCartesian f _ hcart
  refine fiber_hom_ext_of_cartesian f
    (M.map (N.map (IsPreFibered.pullbackMap a.2 f))) inferInstance _ _ ?_
  rw [Functor.map_comp]
  simp only [Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map]
  rw [← Functor.map_comp M, mapPullbackFiberIso_hom_fac hN a f,
    mapPullbackFiberIso_hom_fac hM _ f]
  exact mapPullbackFiberIso_hom_fac (hN.comp hM) a f

/-- The inverse form of `mapPullbackFiberIso_comp`. -/
lemma mapPullbackFiberIso_comp_inv (hN : q.IsFibredOneMorphism r N)
    (hM : r.IsFibredOneMorphism t M) {U : 𝒞} (a : q.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    ((hN.comp hM).mapPullbackFiberIso a f).inv =
      (fiberFunctorOfCompEq hM.comp_eq V).map (hN.mapPullbackFiberIso a f).inv ≫
        (hM.mapPullbackFiberIso ((fiberFunctorOfCompEq hN.comp_eq U).obj a) f).inv := by
  rw [← Iso.cancel_iso_hom_left ((hN.comp hM).mapPullbackFiberIso a f), Iso.hom_inv_id,
    mapPullbackFiberIso_comp hN hM a f]
  simp only [Category.assoc]
  rw [← Category.assoc ((fiberFunctorOfCompEq hM.comp_eq V).map
    (hN.mapPullbackFiberIso a f).hom), ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp, Iso.hom_inv_id]

omit [q.IsFibered] [r.IsFibered] [t.IsFibered] in
/-- The functor induced on fibres by a composite is the composite of the induced functors. -/
lemma fiberFunctorOfCompEq_comp_map (hN : q.IsFibredOneMorphism r N)
    (hM : r.IsFibredOneMorphism t M) {V : 𝒞} {x y : q.Fiber V} (m : x ⟶ y) :
    (fiberFunctorOfCompEq (hN.comp hM).comp_eq V).map m =
      (fiberFunctorOfCompEq hM.comp_eq V).map ((fiberFunctorOfCompEq hN.comp_eq V).map m) :=
  Fiber.hom_ext rfl

/-- **The maps of morphism presheaves of two 1-morphisms compose.** -/
lemma morPresheafMap_comp (hN : q.IsFibredOneMorphism r N) (hM : r.IsFibredOneMorphism t M)
    {U : 𝒞} (a b : q.Fiber U) :
    hN.morPresheafMap a b ≫
        hM.morPresheafMap ((fiberFunctorOfCompEq hN.comp_eq U).obj a)
          ((fiberFunctorOfCompEq hN.comp_eq U).obj b) =
      (hN.comp hM).morPresheafMap a b := by
  ext g m
  change (hM.morPresheafMap ((fiberFunctorOfCompEq hN.comp_eq U).obj a)
      ((fiberFunctorOfCompEq hN.comp_eq U).obj b)).app g
      ((hN.morPresheafMap a b).app g m) = ((hN.comp hM).morPresheafMap a b).app g m
  simp [morPresheafMap_app, mapPullbackFiberIso_comp hN hM a g.unop.hom,
    mapPullbackFiberIso_comp_inv hN hM b g.unop.hom, fiberFunctorOfCompEq_comp_map hN hM,
    Functor.map_comp, Category.assoc]

end Comp

section Conj

variable {N : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]

/-- The comparison isomorphism is natural in the morphism of the fibre. -/
@[reassoc]
lemma mapPullbackFiberIso_naturality (hN : q.IsFibredOneMorphism r N) {U : 𝒞} {a b : q.Fiber U}
    (φ : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    (fiberFunctorOfCompEq hN.comp_eq V).map (pullbackFiberHom φ f) ≫
        (hN.mapPullbackFiberIso b f).inv =
      (hN.mapPullbackFiberIso a f).inv ≫
        pullbackFiberHom ((fiberFunctorOfCompEq hN.comp_eq U).map φ) f := by
  refine fiber_hom_ext_of_cartesian f
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN.comp_eq U).obj b).2 f)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map,
    mapPullbackFiberIso_inv_fac, pullbackFiberHom_fac, mapPullbackFiberIso_inv_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, pullbackFiberHom_fac]

/-- The base change of the image of a morphism of the fibre is the conjugate, by the comparison
isomorphisms, of the image of its base change. -/
lemma pullbackFiberHom_map_eq (hN : q.IsFibredOneMorphism r N) {U : 𝒞} {a b : q.Fiber U}
    (φ : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    pullbackFiberHom ((fiberFunctorOfCompEq hN.comp_eq U).map φ) f =
      (hN.mapPullbackFiberIso a f).hom ≫
        (fiberFunctorOfCompEq hN.comp_eq V).map (pullbackFiberHom φ f) ≫
        (hN.mapPullbackFiberIso b f).inv := by
  rw [mapPullbackFiberIso_naturality hN φ f]
  simp

/-- **The map of morphism presheaves is compatible with the functoriality of `Mor(x, y)` in the two
objects of the fibre.** -/
lemma morPresheafMap_conj (hN : q.IsFibredOneMorphism r N) {U : 𝒞} {x x' y y' : q.Fiber U}
    (e : x' ⟶ x) (e' : y ⟶ y') :
    hN.morPresheafMap x y ≫ _root_.CategoryTheory.Functor.morPresheafMap r
        ((fiberFunctorOfCompEq hN.comp_eq U).map e)
        ((fiberFunctorOfCompEq hN.comp_eq U).map e') =
      _root_.CategoryTheory.Functor.morPresheafMap q e e' ≫ hN.morPresheafMap x' y' := by
  ext g m
  simp [_root_.CategoryTheory.Functor.morPresheafMap_app,
    IsFibredOneMorphism.morPresheafMap_app,
    pullbackFiberHom_map_eq hN e g.unop.hom, pullbackFiberHom_map_eq hN e' g.unop.hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

end Conj

/-- The composite of the image under `N` of a chosen cartesian lift with a morphism that is
strongly cartesian over `u` is strongly cartesian over `b ≫ u`. -/
private lemma isStronglyCartesian_map_pullbackMap_comp [q.IsFibered] {N : 𝒜 ⥤ ℬ}
    (hN : q.IsFibredOneMorphism r N) {U V W : 𝒞} (a : q.Fiber V) (b : W ⟶ V) (u : V ⟶ U) {c : ℬ}
    (φ : N.obj a.1 ⟶ c) [r.IsStronglyCartesian u φ] :
    r.IsStronglyCartesian (b ≫ u) (N.map (IsPreFibered.pullbackMap a.2 b) ≫ φ) :=
  have : r.IsStronglyCartesian b (N.map (IsPreFibered.pullbackMap a.2 b)) :=
    hN.map_isStronglyCartesian b _ inferInstance
  inferInstance

/-- The source of a morphism that is strongly cartesian over `u` is, up to equality, an object of
the fibre over the source of `u`. -/
private lemma exists_fiber_obj_eq {N : 𝒜 ⥤ ℬ} (hN : q.IsFibredOneMorphism r N) {U V : 𝒞}
    {a : 𝒜} {c : ℬ} (u : V ⟶ U) (φ : N.obj a ⟶ c) [r.IsStronglyCartesian u φ] :
    ∃ a₀ : q.Fiber V, a₀.1 = a :=
  ⟨Fiber.mk (by rw [← Functor.congr_obj hN.comp_eq a]; exact IsHomLift.domain_eq r u φ), rfl⟩

section NatIso

variable {N N' : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
  (hN : q.IsFibredOneMorphism r N) (hN' : q.IsFibredOneMorphism r N') (τ : N ≅ N')
  (hτ : ∀ a : 𝒜, r.IsHomLift (𝟙 (q.obj a)) (τ.hom.app a))

include hN hN' hτ

/-- A vertical 2-isomorphism `τ : N ≅ N'` of 1-morphisms of fibred categories over `𝒞` induces, on
the fibre over `U`, an isomorphism between the two induced functors on fibres. -/
def natIsoFiber {U : 𝒞} (a : q.Fiber U) :
    (fiberFunctorOfCompEq hN.comp_eq U).obj a ≅ (fiberFunctorOfCompEq hN'.comp_eq U).obj a :=
  Fiber.isoMk (τ.app a.1) (by
    have h := hτ a.1
    rw [a.2] at h
    exact h)

omit [q.IsFibered] [r.IsFibered] in
/-- The underlying morphism of `natIsoFiber` is the component of `τ`. -/
@[simp]
lemma fiberInclusion_map_natIsoFiber_hom {U : 𝒞} (a : q.Fiber U) :
    Fiber.fiberInclusion.map (natIsoFiber hN hN' τ hτ a).hom = τ.hom.app a.1 := rfl

omit [q.IsFibered] [r.IsFibered] in
/-- The underlying morphism of the inverse of `natIsoFiber` is the component of `τ.symm`. -/
@[simp]
lemma fiberInclusion_map_natIsoFiber_inv {U : 𝒞} (a : q.Fiber U) :
    Fiber.fiberInclusion.map (natIsoFiber hN hN' τ hτ a).inv = τ.inv.app a.1 := rfl

/-- The comparison isomorphisms of two 1-morphisms related by a vertical 2-isomorphism are
themselves related by it, after base change. -/
lemma mapPullbackFiberIso_natIso {U : 𝒞} (a : q.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    pullbackFiberHom (natIsoFiber hN hN' τ hτ a).inv f ≫ (hN.mapPullbackFiberIso a f).hom ≫
        (natIsoFiber hN hN' τ hτ (pullbackFiber q a f)).hom =
      (hN'.mapPullbackFiberIso a f).hom := by
  have hnat : τ.hom.app (pullbackFiber q a f).1 ≫ N'.map (IsPreFibered.pullbackMap a.2 f) =
      N.map (IsPreFibered.pullbackMap a.2 f) ≫ τ.hom.app a.1 := (τ.hom.naturality _).symm
  have hpb : Fiber.fiberInclusion.map (pullbackFiberHom (natIsoFiber hN hN' τ hτ a).inv f) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN.comp_eq U).obj a).2 f =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN'.comp_eq U).obj a).2 f ≫
        τ.inv.app a.1 :=
    pullbackFiberHom_fac (natIsoFiber hN hN' τ hτ a).inv f
  refine fiber_hom_ext_of_cartesian f (N'.map (IsPreFibered.pullbackMap a.2 f))
    (hN'.isCartesian_map_pullbackMap a f) _ _ ?_
  have hL : Fiber.fiberInclusion.map (pullbackFiberHom (natIsoFiber hN hN' τ hτ a).inv f ≫
          (hN.mapPullbackFiberIso a f).hom ≫
          (natIsoFiber hN hN' τ hτ (pullbackFiber q a f)).hom) ≫
        N'.map (IsPreFibered.pullbackMap a.2 f) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN'.comp_eq U).obj a).2 f := by
    simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_natIsoFiber_hom]
    rw [hnat, ← Category.assoc (Fiber.fiberInclusion.map (hN.mapPullbackFiberIso a f).hom),
      mapPullbackFiberIso_hom_fac hN a f, ← Category.assoc, hpb]
    simp
  rw [hL, mapPullbackFiberIso_hom_fac hN' a f]

/-- **Two 1-morphisms related by a vertical 2-isomorphism induce the same map of morphism
presheaves**, up to the isomorphism of morphism presheaves the 2-isomorphism produces. -/
lemma morPresheafMap_natIso {U : 𝒞} (a b : q.Fiber U) :
    hN.morPresheafMap a b ≫ _root_.CategoryTheory.Functor.morPresheafMap r
        (natIsoFiber hN hN' τ hτ a).inv (natIsoFiber hN hN' τ hτ b).hom =
      hN'.morPresheafMap a b := by
  ext g m
  change pullbackFiberHom (natIsoFiber hN hN' τ hτ a).inv g.unop.hom ≫
      ((hN.mapPullbackFiberIso a g.unop.hom).hom ≫
        (fiberFunctorOfCompEq hN.comp_eq g.unop.left).map m ≫
        (hN.mapPullbackFiberIso b g.unop.hom).inv) ≫
      pullbackFiberHom (natIsoFiber hN hN' τ hτ b).hom g.unop.hom =
    (hN'.mapPullbackFiberIso a g.unop.hom).hom ≫
      (fiberFunctorOfCompEq hN'.comp_eq g.unop.left).map m ≫
      (hN'.mapPullbackFiberIso b g.unop.hom).inv
  have hnat : τ.hom.app (pullbackFiber q a g.unop.hom).1 ≫
        N'.map (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap b.2 g.unop.hom) =
      N.map (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap b.2 g.unop.hom) ≫
        τ.hom.app b.1 := (τ.hom.naturality _).symm
  have hpbb : Fiber.fiberInclusion.map
          (pullbackFiberHom (natIsoFiber hN hN' τ hτ b).hom g.unop.hom) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN'.comp_eq U).obj b).2 g.unop.hom =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN.comp_eq U).obj b).2 g.unop.hom ≫
        τ.hom.app b.1 :=
    pullbackFiberHom_fac (natIsoFiber hN hN' τ hτ b).hom g.unop.hom
  have hιA := congrArg Fiber.fiberInclusion.map
    (mapPullbackFiberIso_natIso hN hN' τ hτ a g.unop.hom)
  simp only [Functor.map_comp, fiberInclusion_map_natIsoFiber_hom] at hιA
  refine fiber_hom_ext_of_cartesian g.unop.hom
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN'.comp_eq U).obj b).2 g.unop.hom)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  have hcommon : Fiber.fiberInclusion.map (hN'.mapPullbackFiberIso a g.unop.hom).hom ≫
      N'.map (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap b.2 g.unop.hom) =
    Fiber.fiberInclusion.map (hN'.mapPullbackFiberIso a g.unop.hom).hom ≫
      N'.map (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap b.2 g.unop.hom) := rfl
  have hL : Fiber.fiberInclusion.map (pullbackFiberHom (natIsoFiber hN hN' τ hτ a).inv g.unop.hom ≫
          ((hN.mapPullbackFiberIso a g.unop.hom).hom ≫
            (fiberFunctorOfCompEq hN.comp_eq g.unop.left).map m ≫
            (hN.mapPullbackFiberIso b g.unop.hom).inv) ≫
          pullbackFiberHom (natIsoFiber hN hN' τ hτ b).hom g.unop.hom) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN'.comp_eq U).obj b).2 g.unop.hom =
      Fiber.fiberInclusion.map (hN'.mapPullbackFiberIso a g.unop.hom).hom ≫
        N'.map (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap b.2 g.unop.hom) := by
    simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map]
    rw [hpbb, ← Category.assoc (Fiber.fiberInclusion.map
      (hN.mapPullbackFiberIso b g.unop.hom).inv), mapPullbackFiberIso_inv_fac hN b g.unop.hom,
      ← Category.assoc (N.map (Fiber.fiberInclusion.map m)), ← Functor.map_comp, ← hnat, ← hιA]
    simp [Category.assoc, Functor.map_comp]
  have hR : Fiber.fiberInclusion.map ((hN'.mapPullbackFiberIso a g.unop.hom).hom ≫
          (fiberFunctorOfCompEq hN'.comp_eq g.unop.left).map m ≫
          (hN'.mapPullbackFiberIso b g.unop.hom).inv) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hN'.comp_eq U).obj b).2 g.unop.hom =
      Fiber.fiberInclusion.map (hN'.mapPullbackFiberIso a g.unop.hom).hom ≫
        N'.map (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap b.2 g.unop.hom) := by
    simp [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map,
      mapPullbackFiberIso_inv_fac]
  rw [hL, hR]

end NatIso

/-! ### Local descent of a morphism of a fibre along a 1-morphism

If the map of morphism presheaves induced by `N` is locally surjective, a morphism `N x ⟶ N y` of a
fibre is, locally on the base, the image under `N` of a morphism between the chosen pullbacks of
`x` and `y`; if the map is also locally injective, an *isomorphism* `N x ≅ N y` descends to an
isomorphism, because the two descended morphisms are mutually inverse after a further covering. -/

section Descends

variable {N : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]

/-- **Local descent of a morphism of a fibre along a 1-morphism.** A morphism `N x ⟶ N y` of the
fibre over `V` is, locally on `V`, the image under `N` of a morphism between the chosen pullbacks
of `x` and `y`. This is local surjectivity of the map of Stacks 042V read through the chosen
cartesian lifts. -/
lemma exists_locally_descends (hN : q.IsFibredOneMorphism r N) {J : GrothendieckTopology 𝒞}
    {V : 𝒞} (x y : q.Fiber V)
    (hls : Presheaf.IsLocallySurjective (J.over V) (hN.morPresheafMap x y))
    (e : (fiberFunctorOfCompEq hN.comp_eq V).obj x ⟶ (fiberFunctorOfCompEq hN.comp_eq V).obj y) :
    ∃ R ∈ J V, ∀ ⦃W : 𝒞⦄ (b : W ⟶ V), R.arrows b →
      ∃ a : pullbackFiber q x b ⟶ pullbackFiber q y b,
        N.map (Fiber.fiberInclusion.map a) ≫ N.map (IsPreFibered.pullbackMap y.2 b) =
          N.map (IsPreFibered.pullbackMap x.2 b) ≫ Fiber.fiberInclusion.map e := by
  have := hls
  set σ := morSection r ((fiberFunctorOfCompEq hN.comp_eq V).obj x)
    ((fiberFunctorOfCompEq hN.comp_eq V).obj y) e with hσ
  have hSmem : Presheaf.imageSieve (hN.morPresheafMap x y) σ ∈ (J.over V) (Over.mk (𝟙 V)) :=
    Presheaf.imageSieve_mem (J.over V) (hN.morPresheafMap x y) σ
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) (Presheaf.imageSieve (hN.morPresheafMap x y) σ),
    ((J.mem_over_iff _).1 hSmem), ?_⟩
  intro W b hb
  have hk := (Sieve.overEquiv_iff (Presheaf.imageSieve (hN.morPresheafMap x y) σ) b).1 hb
  set κ : Over.mk (b ≫ (Over.mk (𝟙 V) : Over V).hom) ⟶ (Over.mk (𝟙 V) : Over V) :=
    Over.homMk b with hκ
  have hk' : (Presheaf.imageSieve (hN.morPresheafMap x y) σ).arrows κ := hk
  set ι₀ : (Over.mk b : Over V) ⟶ Over.mk (b ≫ (Over.mk (𝟙 V) : Over V).hom) :=
    Over.homMk (𝟙 W) (by simp) with hι₀
  obtain ⟨m, hm⟩ := (Presheaf.imageSieve (hN.morPresheafMap x y) σ).downward_closed hk' ι₀
  refine ⟨m, ?_⟩
  have hm' : (hN.morPresheafMap x y).app (Opposite.op (Over.mk b)) m =
      morRestrict r ((fiberFunctorOfCompEq hN.comp_eq V).obj x)
        ((fiberFunctorOfCompEq hN.comp_eq V).obj y) (ι₀ ≫ κ) σ := hm
  have hfac := congrArg (fun t ↦ Fiber.fiberInclusion.map t ≫
    IsPreFibered.pullbackMap
      ((fiberFunctorOfCompEq hN.comp_eq V).obj y).2 (Over.mk b : Over V).hom) hm'
  simp only [morPresheafMap_app, Functor.map_comp, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map, mapPullbackFiberIso_inv_fac,
    morRestrict_fac, hσ, morSection] at hfac
  have hidy : Fiber.fiberInclusion.map
        (pullbackFiberIdIso ((fiberFunctorOfCompEq hN.comp_eq V).obj y)).inv ≫
      IsPreFibered.pullbackMap
        ((fiberFunctorOfCompEq hN.comp_eq V).obj y).2 (Over.mk (𝟙 V) : Over V).hom =
      𝟙 _ := pullbackFiberIdIso_inv_fac _
  have hidx : pullbackFiberMap r ((fiberFunctorOfCompEq hN.comp_eq V).obj x) (ι₀ ≫ κ) ≫
        Fiber.fiberInclusion.map
        (pullbackFiberIdIso ((fiberFunctorOfCompEq hN.comp_eq V).obj x)).hom ≫
        Fiber.fiberInclusion.map e =
      IsPreFibered.pullbackMap
        ((fiberFunctorOfCompEq hN.comp_eq V).obj x).2 (Over.mk b : Over V).hom ≫
        Fiber.fiberInclusion.map e := by
    rw [← Category.assoc, pullbackFiberIdIso_hom_fac]
    congr 1
    exact pullbackFiberMap_fac r _ (ι₀ ≫ κ)
  rw [hidy, Category.comp_id, hidx] at hfac
  have hxfac := mapPullbackFiberIso_hom_fac hN x (Over.mk b : Over V).hom
  rw [← hxfac, Category.assoc] at hfac
  exact (cancel_epi _).1 hfac

/-- Restricting a morphism `a : x|_b ⟶ y|_b` that descends to `ε` along `N` to a base change
`γ ≫ b` gives a morphism that still descends to `ε`. -/
private lemma map_morRestrict_descends {V : 𝒞} (x y : q.Fiber V) {g₁ g₂ : Over V} (κ : g₁ ⟶ g₂)
    (a : pullbackFiber q x g₂.hom ⟶ pullbackFiber q y g₂.hom) (ε : N.obj x.1 ⟶ N.obj y.1)
    (h : N.map (Fiber.fiberInclusion.map a) ≫ N.map (IsPreFibered.pullbackMap y.2 g₂.hom) =
      N.map (IsPreFibered.pullbackMap x.2 g₂.hom) ≫ ε) :
    N.map (Fiber.fiberInclusion.map (morRestrict q x y κ a)) ≫
        N.map (IsPreFibered.pullbackMap y.2 g₁.hom) =
      N.map (IsPreFibered.pullbackMap x.2 g₁.hom) ≫ ε := by
  have hcomp : N.map (pullbackFiberMap q x κ) ≫ N.map (IsPreFibered.pullbackMap x.2 g₂.hom) =
      N.map (IsPreFibered.pullbackMap x.2 g₁.hom) := by
    rw [← Functor.map_comp]
    exact congrArg N.map (by simp)
  have hd := congrArg N.map (morRestrict_fac q x y κ a)
  simp only [Functor.map_comp] at hd
  rw [h, ← Category.assoc, hcomp] at hd
  exact hd

/-- **Local descent of an isomorphism of a fibre along a 1-morphism.** If the map of morphism
presheaves induced by `N` is locally bijective, an isomorphism `N x ≅ N y` of the fibre over `V`
is, locally on `V`, the image under `N` of an isomorphism between the chosen pullbacks of `x` and
`y`: the descended morphisms in the two directions are mutually inverse after `N`, hence, by local
injectivity, mutually inverse after a further covering. -/
lemma exists_locally_descends_iso (hN : q.IsFibredOneMorphism r N) {J : GrothendieckTopology 𝒞}
    {V : 𝒞} (x y : q.Fiber V)
    (hmor : ∀ (W : 𝒞) (a b : q.Fiber W),
      Presheaf.IsLocallyInjective (J.over W) (hN.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over W) (hN.morPresheafMap a b))
    (e : (fiberFunctorOfCompEq hN.comp_eq V).obj x ≅ (fiberFunctorOfCompEq hN.comp_eq V).obj y) :
    ∃ R ∈ J V, ∀ ⦃W : 𝒞⦄ (b : W ⟶ V), R.arrows b →
      ∃ t : pullbackFiber q x b ≅ pullbackFiber q y b,
        N.map (Fiber.fiberInclusion.map t.hom) ≫ N.map (IsPreFibered.pullbackMap y.2 b) =
          N.map (IsPreFibered.pullbackMap x.2 b) ≫ Fiber.fiberInclusion.map e.hom := by
  refine ⟨⟨fun {W} b ↦ ∃ t : pullbackFiber q x b ≅ pullbackFiber q y b,
      N.map (Fiber.fiberInclusion.map t.hom) ≫ N.map (IsPreFibered.pullbackMap y.2 b) =
        N.map (IsPreFibered.pullbackMap x.2 b) ≫ Fiber.fiberInclusion.map e.hom, ?_⟩, ?_,
    fun _ _ hb ↦ hb⟩
  · -- the property is stable under precomposition: restrict the isomorphism
    intro W W' b hb γ
    obtain ⟨t, ht⟩ := hb
    set κ : (Over.mk (γ ≫ b) : Over V) ⟶ Over.mk b := Over.homMk γ with hκ
    have : IsIso t.hom := inferInstance
    have := isIso_morRestrict q x y κ t.hom
    exact ⟨asIso (morRestrict q x y κ t.hom), map_morRestrict_descends x y κ t.hom _ ht⟩
  · -- the property holds on a covering sieve
    obtain ⟨R₁, hR₁, hR₁prop⟩ := exists_locally_descends hN x y (hmor V x y).2 e.hom
    obtain ⟨R₂, hR₂, hR₂prop⟩ := exists_locally_descends hN y x (hmor V y x).2 e.inv
    refine J.transitive (J.intersection_covering hR₁ hR₂) _ ?_
    intro W b hb
    obtain ⟨a₁, ha₁⟩ := hR₁prop b hb.1
    obtain ⟨a₂, ha₂⟩ := hR₂prop b hb.2
    -- the composite `a₁ ≫ a₂` is locally the identity, and likewise in the other direction
    have key : ∀ (x y : q.Fiber V) (a₁ : pullbackFiber q x b ⟶ pullbackFiber q y b)
        (a₂ : pullbackFiber q y b ⟶ pullbackFiber q x b) (ε₁ : N.obj x.1 ⟶ N.obj y.1)
        (ε₂ : N.obj y.1 ⟶ N.obj x.1),
        N.map (Fiber.fiberInclusion.map a₁) ≫ N.map (IsPreFibered.pullbackMap y.2 b) =
          N.map (IsPreFibered.pullbackMap x.2 b) ≫ ε₁ →
        N.map (Fiber.fiberInclusion.map a₂) ≫ N.map (IsPreFibered.pullbackMap x.2 b) =
          N.map (IsPreFibered.pullbackMap y.2 b) ≫ ε₂ → ε₁ ≫ ε₂ = 𝟙 _ →
        Sieve.overEquiv (Over.mk b)
          (Presheaf.equalizerSieve (F := morPresheaf q x x)
            (X := Opposite.op (Over.mk b)) (a₁ ≫ a₂) (𝟙 (pullbackFiber q x b))) ∈ J W := by
      intro x y a₁ a₂ ε₁ ε₂ ha₁ ha₂ hε
      have := (hmor V x x).1
      have hcartx : r.IsStronglyCartesian b (N.map (IsPreFibered.pullbackMap x.2 b)) :=
        hN.map_isStronglyCartesian b _ inferInstance
      have hWx : r.obj (N.obj (pullbackFiber q x b).1) = W :=
        (Functor.congr_obj hN.comp_eq (pullbackFiber q x b).1).trans (pullbackFiber q x b).2
      have hidx : r.IsHomLift (𝟙 W) (𝟙 (N.obj (pullbackFiber q x b).1)) := IsHomLift.id hWx
      have hl : r.IsHomLift (𝟙 W) (N.map (Fiber.fiberInclusion.map (a₁ ≫ a₂))) :=
        hN.map_isHomLift (𝟙 W) _
      have hcomp : N.map (Fiber.fiberInclusion.map (a₁ ≫ a₂)) =
          𝟙 (N.obj (pullbackFiber q x b).1) := by
        refine IsStronglyCartesian.ext r b (N.map (IsPreFibered.pullbackMap x.2 b)) (𝟙 W) ?_
        simp only [Functor.map_comp, Category.assoc]
        rw [ha₂, ← Category.assoc, ha₁, Category.assoc, hε, Category.comp_id]
        exact (Category.id_comp _).symm
      have happ : (hN.morPresheafMap x x).app (Opposite.op (Over.mk b)) (a₁ ≫ a₂) =
          (hN.morPresheafMap x x).app (Opposite.op (Over.mk b)) (𝟙 (pullbackFiber q x b)) := by
        have hFG : (fiberFunctorOfCompEq hN.comp_eq (Over.mk b : Over V).left).map (a₁ ≫ a₂) =
            (fiberFunctorOfCompEq hN.comp_eq (Over.mk b : Over V).left).map
              (𝟙 (pullbackFiber q x b)) := by
          refine Fiber.hom_ext ?_
          simp only [fiberInclusion_map_fiberFunctorOfCompEq_map, Functor.map_id]
          exact hcomp
        rw [morPresheafMap_app, morPresheafMap_app, hFG]
      exact (J.mem_over_iff _).1
        (Presheaf.equalizerSieve_mem (J.over V) (hN.morPresheafMap x x) _ _ happ)
    have hT12 := key x y a₁ a₂ _ _ ha₁ ha₂
      (by rw [← Functor.map_comp, e.hom_inv_id]; simp [Fiber.fiberInclusion])
    have hT21 := key y x a₂ a₁ _ _ ha₂ ha₁
      (by rw [← Functor.map_comp, e.inv_hom_id]; simp [Fiber.fiberInclusion])
    refine J.superset_covering ?_ (J.intersection_covering hT12 hT21)
    intro W' h hh
    obtain ⟨hh12, hh21⟩ := hh
    set κ : (Over.mk (h ≫ b) : Over V) ⟶ Over.mk b := Over.homMk h with hκ
    have hk12 := (Sieve.overEquiv_iff (Y := (Over.mk b : Over V)) _ h).1 hh12
    have hk21 := (Sieve.overEquiv_iff (Y := (Over.mk b : Over V)) _ h).1 hh21
    have he12 : morRestrict q x x κ (a₁ ≫ a₂) =
        morRestrict q x x κ (𝟙 (pullbackFiber q x (Over.mk b : Over V).hom)) := hk12
    have he21 : morRestrict q y y κ (a₂ ≫ a₁) =
        morRestrict q y y κ (𝟙 (pullbackFiber q y (Over.mk b : Over V).hom)) := hk21
    rw [morRestrict_comp_hom, morRestrict_id_hom] at he12 he21
    refine ⟨⟨morRestrict q x y κ a₁, morRestrict q y x κ a₂, he12, he21⟩, ?_⟩
    exact map_morRestrict_descends x y κ a₁ _ ha₁

end Descends

end IsFibredOneMorphism

end Functor

open _root_.CategoryTheory.Functor

/-! ### The canonical 1-morphism of 2-fibre products

Given 1-morphisms `i`, `j`, `k` over `𝒞` and vertical 2-isomorphisms `α : i ⋙ f' ≅ f ⋙ j`,
`β : k ⋙ g' ≅ g ⋙ j` filling the two functoriality squares, the 2-fibre product of the
stackified cospan receives a canonical 1-morphism from the 2-fibre product of the original cospan:
`(U, x, z, φ) ↦ (U, i x, k z, α_x ≫ j φ ≫ β_z⁻¹)`. It commutes with the two projections *on the
nose*, which is what makes the maps of morphism presheaves below composable. -/

namespace TwoFibreProductOver

universe v u₀ u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒞 : Type u₀} [Category.{v} 𝒞]
  {𝒳 : Type u₁} [Category.{v} 𝒳] {𝒴 : Type u₂} [Category.{v} 𝒴] {𝒵 : Type u₃} [Category.{v} 𝒵]
  {𝒳' : Type u₄} [Category.{v} 𝒳'] {𝒴' : Type u₅} [Category.{v} 𝒴']
  {𝒵' : Type u₆} [Category.{v} 𝒵']
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞}
  {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'}
  {i : 𝒳 ⥤ 𝒳'} {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'}

section Map

variable (hi : p𝒳.IsFibredOneMorphism p𝒳' i) (hj : p𝒴.IsFibredOneMorphism p𝒴' j)
  (hk : p𝒵.IsFibredOneMorphism p𝒵' k)
  (α : i ⋙ f' ≅ f ⋙ j) (hα : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x))
  (β : k ⋙ g' ≅ g ⋙ j) (hβ : ∀ z : 𝒵, p𝒴'.IsHomLift (𝟙 (p𝒵.obj z)) (β.hom.app z))

include hi hj hk hα hβ

/-- **The canonical 1-morphism of 2-fibre products.** It sends `(U, x, z, φ)` to
`(U, i x, k z, α_x ≫ j φ ≫ β_z⁻¹)` and a pair of components to their images under `i` and `k`. -/
def stackifyMap : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g' where
  obj P :=
    { base := P.base
      x := i.obj P.x
      y := k.obj P.y
      hx := by rw [← Functor.comp_obj, hi.comp_eq]; exact P.hx
      hy := by rw [← Functor.comp_obj, hk.comp_eq]; exact P.hy
      iso := α.app P.x ≪≫ j.mapIso P.iso ≪≫ (β.app P.y).symm
      vertical := by
        have h1 : p𝒴'.IsHomLift (𝟙 P.base) (α.hom.app P.x) := by
          have h := hα P.x
          rwa [P.hx] at h
        have h2 : p𝒴'.IsHomLift (𝟙 P.base) (j.map P.iso.hom) := by
          have := P.vertical
          exact isHomLift_map_of_comp_eq hj.comp_eq (𝟙 P.base) P.iso.hom
        have h3 : p𝒴'.IsHomLift (𝟙 P.base) (β.app P.y).inv := by
          have h : p𝒴'.IsHomLift (𝟙 P.base) (β.app P.y).hom := by
            have h0 := hβ P.y
            rwa [P.hy] at h0
          have := h
          infer_instance
        exact isHomLift_id_comp p𝒴' _ _ h1 (isHomLift_id_comp p𝒴' _ _ h2 h3) }
  map {P Q} Φ :=
    { hbase := Φ.hbase
      a := i.map Φ.a
      b := k.map Φ.b
      ha := by
        have := Φ.ha
        exact isHomLift_map_of_comp_eq hi.comp_eq Φ.hbase Φ.a
      hb := by
        have := Φ.hb
        exact isHomLift_map_of_comp_eq hk.comp_eq Φ.hbase Φ.b
      w := by
        have hna : f'.map (i.map Φ.a) ≫ α.hom.app Q.x = α.hom.app P.x ≫ j.map (f.map Φ.a) :=
          α.hom.naturality Φ.a
        have hnb : j.map (g.map Φ.b) ≫ β.inv.app Q.y = β.inv.app P.y ≫ g'.map (k.map Φ.b) :=
          β.inv.naturality Φ.b
        have hmid : j.map (f.map Φ.a) ≫ j.map Q.iso.hom =
            j.map P.iso.hom ≫ j.map (g.map Φ.b) := by
          rw [← Functor.map_comp, ← Functor.map_comp, Φ.w]
        change f'.map (i.map Φ.a) ≫ α.hom.app Q.x ≫ j.map Q.iso.hom ≫ β.inv.app Q.y =
          (α.hom.app P.x ≫ j.map P.iso.hom ≫ β.inv.app P.y) ≫ g'.map (k.map Φ.b)
        rw [reassoc_of% hna, reassoc_of% hmid, hnb]
        simp only [Category.assoc] }
  map_id P := by refine Hom.ext' ?_ ?_ <;> simp
  map_comp Φ Ψ := by refine Hom.ext' ?_ ?_ <;> simp

/-- The image of `P` under `stackifyMap` lies over the same object of `𝒞` as `P`. -/
@[simp]
lemma stackifyMap_obj_base (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) :
    ((stackifyMap hi hj hk α hα β hβ).obj P).base = P.base := rfl

/-- The first component of the image of `P` under `stackifyMap` is `i.obj P.x`. -/
@[simp]
lemma stackifyMap_obj_x (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) :
    ((stackifyMap hi hj hk α hα β hβ).obj P).x = i.obj P.x := rfl

/-- The second component of the image of `P` under `stackifyMap` is `k.obj P.y`. -/
@[simp]
lemma stackifyMap_obj_y (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) :
    ((stackifyMap hi hj hk α hα β hβ).obj P).y = k.obj P.y := rfl

/-- The comparison isomorphism of the image of `P` under `stackifyMap` is the image of that of
`P` under `j`, transported through `α` and `β`. -/
@[simp]
lemma stackifyMap_obj_iso_hom (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) :
    ((stackifyMap hi hj hk α hα β hβ).obj P).iso.hom =
      α.hom.app P.x ≫ j.map P.iso.hom ≫ β.inv.app P.y := rfl

/-- The first component of the image of a morphism under `stackifyMap` is its image under `i`. -/
@[simp]
lemma stackifyMap_map_a {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (Φ : P ⟶ Q) :
    ((stackifyMap hi hj hk α hα β hβ).map Φ).a = i.map Φ.a := rfl

/-- The second component of the image of a morphism under `stackifyMap` is its image under `k`. -/
@[simp]
lemma stackifyMap_map_b {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (Φ : P ⟶ Q) :
    ((stackifyMap hi hj hk α hα β hβ).map Φ).b = k.map Φ.b := rfl

/-- The image of a morphism under `stackifyMap` lies over the same morphism of `𝒞`. -/
@[simp]
lemma stackifyMap_map_hbase {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (Φ : P ⟶ Q) :
    ((stackifyMap hi hj hk α hα β hβ).map Φ).hbase = Φ.hbase := rfl

/-- The canonical 1-morphism is strictly over `𝒞`. -/
lemma stackifyMap_comp_structureFunctor :
    stackifyMap hi hj hk α hα β hβ ⋙ structureFunctor p𝒳' p𝒵' p𝒴' f' g' =
      structureFunctor p𝒳 p𝒵 p𝒴 f g := rfl

/-- The canonical 1-morphism commutes with the first projections on the nose. -/
lemma stackifyMap_comp_fst :
    stackifyMap hi hj hk α hα β hβ ⋙ fst p𝒳' p𝒵' p𝒴' f' g' = fst p𝒳 p𝒵 p𝒴 f g ⋙ i := rfl

/-- The canonical 1-morphism commutes with the second projections on the nose. -/
lemma stackifyMap_comp_snd :
    stackifyMap hi hj hk α hα β hβ ⋙ snd p𝒳' p𝒵' p𝒴' f' g' = snd p𝒳 p𝒵 p𝒴 f g ⋙ k := rfl

/-- **The canonical 1-morphism is a 1-morphism of fibred categories over `𝒞`.** A morphism of a
2-fibre product is strongly cartesian exactly when both its components are (Stacks 02XQ), and `i`
and `k` preserve strongly cartesian morphisms. -/
lemma isFibredOneMorphism_stackifyMap [p𝒳.IsFibered] [p𝒵.IsFibered] [p𝒴.IsFibered]
    [p𝒳'.IsFibered] [p𝒵'.IsFibered] [p𝒴'.IsFibered]
    (hf : p𝒳.IsFibredOneMorphism p𝒴 f) (hg : p𝒵.IsFibredOneMorphism p𝒴 g)
    (hf' : p𝒳'.IsFibredOneMorphism p𝒴' f') (hg' : p𝒵'.IsFibredOneMorphism p𝒴' g') :
    Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') (stackifyMap hi hj hk α hα β hβ) where
  comp_eq := stackifyMap_comp_structureFunctor hi hj hk α hα β hβ
  map_isStronglyCartesian := by
    intro R T u P Q Φ hΦ
    obtain ⟨ha, hb⟩ := map_isStronglyCartesian_of_isStronglyCartesian hf hg u Φ hΦ
    have hlift : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsHomLift u
        ((stackifyMap hi hj hk α hα β hβ).map Φ) := by
      have := hΦ.toIsHomLift
      exact isHomLift_map_of_comp_eq (stackifyMap_comp_structureFunctor hi hj hk α hα β hβ) u Φ
    exact isStronglyCartesian_of_components hf' hg' u _ hlift
      (hi.map_isStronglyCartesian u Φ.a ha) (hk.map_isStronglyCartesian u Φ.b hb)

end Map

/-! ### The two projections and the morphism presheaf of a 2-fibre product

The comparison isomorphism of `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` for
a projection of the 2-fibre product is the comparison
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIso` of the chosen pullbacks, so the two
components of the identification of `Mor(P, Q)` with a fibre product are the maps of morphism
presheaves induced by the two projections. -/

section Proj

variable [p𝒳.IsFibered] [p𝒵.IsFibered] [p𝒴.IsFibered]
  [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered]
  (hf : p𝒳.IsFibredOneMorphism p𝒴 f) (hg : p𝒵.IsFibredOneMorphism p𝒴 g)

/-- The comparison isomorphism of the first projection is that of the chosen pullbacks. -/
lemma mapPullbackFiberIso_fst {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (u : V ⟶ U) :
    (fst_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg).mapPullbackFiberIso P u =
      (pullbackFiberFstIso hf hg P u).symm := by
  have hc : p𝒳.IsStronglyCartesian u (IsPreFibered.pullbackMap P.2 u).a :=
    isStronglyCartesian_pullbackMap_a hf hg P u
  have := hc
  refine Iso.ext (fiber_hom_ext_of_cartesian u (IsPreFibered.pullbackMap P.2 u).a
    inferInstance _ _ ?_)
  rw [Iso.symm_hom, pullbackFiberFstIso_inv_fac hf hg P u]
  exact IsFibredOneMorphism.mapPullbackFiberIso_hom_fac
    (fst_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg) P u

/-- The comparison isomorphism of the second projection is the comparison of the chosen
pullbacks. -/
lemma mapPullbackFiberIso_snd {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (u : V ⟶ U) :
    (snd_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg).mapPullbackFiberIso P u =
      (pullbackFiberSndIso hf hg P u).symm := by
  have hc : p𝒵.IsStronglyCartesian u (IsPreFibered.pullbackMap P.2 u).b :=
    isStronglyCartesian_pullbackMap_b hf hg P u
  have := hc
  refine Iso.ext (fiber_hom_ext_of_cartesian u (IsPreFibered.pullbackMap P.2 u).b
    inferInstance _ _ ?_)
  rw [Iso.symm_hom, pullbackFiberSndIso_inv_fac hf hg P u]
  exact IsFibredOneMorphism.mapPullbackFiberIso_hom_fac
    (snd_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg) P u

/-- The `𝒳`-component of the identification of `Mor(P, Q)` with a fibre product is the map of
morphism presheaves induced by the first projection. -/
lemma morPresheafEqPullbackIso_hom_val_fst {U : 𝒞}
    (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (o : (Over U)ᵒᵖ)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj o) :
    (((morPresheafEqPullbackIso hf hg P Q).hom.app o) m).val.1 =
      ((fst_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg).morPresheafMap P Q).app o m := by
  change (pullbackFiberFstIso hf hg P o.unop.hom).homCongr
      (pullbackFiberFstIso hf hg Q o.unop.hom) (fibFstHom m) = _
  rw [IsFibredOneMorphism.morPresheafMap_app, mapPullbackFiberIso_fst hf hg,
    mapPullbackFiberIso_fst hf hg]
  simp only [Iso.homCongr_apply, Iso.symm_hom, Iso.symm_inv]
  rfl

/-- The `𝒵`-component of the identification of `Mor(P, Q)` with a fibre product is the map of
morphism presheaves induced by the second projection, followed by the identification given by the
comparison isomorphisms of `P` and `Q`. -/
lemma morPresheafEqPullbackIso_hom_val_snd {U : 𝒞}
    (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (o : (Over U)ᵒᵖ)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj o) :
    (((morPresheafEqPullbackIso hf hg P Q).hom.app o) m).val.2 =
      ((snd_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg).morPresheafMap P Q).app o m := by
  change (pullbackFiberSndIso hf hg P o.unop.hom).homCongr
      (pullbackFiberSndIso hf hg Q o.unop.hom) (fibSndHom m) = _
  rw [IsFibredOneMorphism.morPresheafMap_app, mapPullbackFiberIso_snd hf hg,
    mapPullbackFiberIso_snd hf hg]
  simp only [Iso.homCongr_apply, Iso.symm_hom, Iso.symm_inv]
  rfl

end Proj

/-! ### Clause (1) of Stacks 02ZN for the canonical 1-morphism

The morphism presheaf of a 2-fibre product is the fibre product of a cospan of morphism presheaves
(Stacks 026G, `CategoryTheory.TwoFibreProductOver.morPresheafEqPullbackIso`), and the map induced
by the canonical 1-morphism is, under that identification, the map of fibre products induced by the
maps of morphism presheaves of `i`, `k` and `j`. Local injectivity and local surjectivity therefore
follow from the corresponding statements for `i`, `k` and `j` by the two presheaf lemmas at the top
of this file — local surjectivity using that the map induced by `j` is *also* locally injective,
which is what makes a pair of local preimages satisfy the fibre product condition. -/

section Clause

variable [p𝒳.IsFibered] [p𝒵.IsFibered] [p𝒴.IsFibered]
  [p𝒳'.IsFibered] [p𝒵'.IsFibered] [p𝒴'.IsFibered]
  (hi : p𝒳.IsFibredOneMorphism p𝒳' i) (hj : p𝒴.IsFibredOneMorphism p𝒴' j)
  (hk : p𝒵.IsFibredOneMorphism p𝒵' k)
  (α : i ⋙ f' ≅ f ⋙ j) (hα : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x))
  (β : k ⋙ g' ≅ g ⋙ j) (hβ : ∀ z : 𝒵, p𝒴'.IsHomLift (𝟙 (p𝒵.obj z)) (β.hom.app z))
  (hf : p𝒳.IsFibredOneMorphism p𝒴 f) (hg : p𝒵.IsFibredOneMorphism p𝒴 g)
  (hf' : p𝒳'.IsFibredOneMorphism p𝒴' f') (hg' : p𝒵'.IsFibredOneMorphism p𝒴' g')

/-- The comparison `f'(i x) ≅ j(f x)` in the fibre over `U` produced by `α`. -/
noncomputable abbrev alphaFib {U : 𝒞} (x : p𝒳.Fiber U) :
    (fiberFunctorOfCompEq (hi.comp hf').comp_eq U).obj x ≅
      (fiberFunctorOfCompEq (hf.comp hj).comp_eq U).obj x :=
  IsFibredOneMorphism.natIsoFiber (hi.comp hf') (hf.comp hj) α hα x

/-- The comparison `g'(k z) ≅ j(g z)` in the fibre over `U` produced by `β`. -/
noncomputable abbrev betaFib {U : 𝒞} (z : p𝒵.Fiber U) :
    (fiberFunctorOfCompEq (hk.comp hg').comp_eq U).obj z ≅
      (fiberFunctorOfCompEq (hg.comp hj).comp_eq U).obj z :=
  IsFibredOneMorphism.natIsoFiber (hk.comp hg') (hg.comp hj) β hβ z

variable [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered]
  [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]

omit [p𝒳.IsFibered] [p𝒵.IsFibered] [p𝒴.IsFibered] [p𝒳'.IsFibered] [p𝒵'.IsFibered] [p𝒴'.IsFibered]
  [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered]
  [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered] in
/-- **The comparison isomorphism of the image of `P` is the image of the comparison isomorphism.**
The comparison isomorphism of `H P` is `α_x ≫ j φ ≫ β_z⁻¹` by construction, so composing it with
`β_z` gives `α_x ≫ j φ`. -/
lemma fibIso_stackifyMap {U : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (hH : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') (stackifyMap hi hj hk α hα β hβ)) :
    (fibIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)).hom ≫
        (betaFib hj hk β hβ hg hg' (fibSnd P)).hom =
      (alphaFib hi hj α hα hf hf' (fibFst P)).hom ≫
        (fiberFunctorOfCompEq hj.comp_eq U).map (fibIso hf hg P).hom :=
  Fiber.hom_ext (by simp [fibFst, fibSnd])

include hf hg hf' hg'

/-- **Clause (1) of Stacks 02ZN for the canonical 1-morphism of 2-fibre products.** -/
lemma isLocallyBijective_morPresheafMap_stackifyMap {J : GrothendieckTopology 𝒞}
    (hH : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') (stackifyMap hi hj hk α hα β hβ))
    (hmor𝒳 : ∀ (V : 𝒞) (x₁ x₂ : p𝒳.Fiber V),
      Presheaf.IsLocallyInjective (J.over V) (hi.morPresheafMap x₁ x₂) ∧
        Presheaf.IsLocallySurjective (J.over V) (hi.morPresheafMap x₁ x₂))
    (hmor𝒴 : ∀ (V : 𝒞) (y₁ y₂ : p𝒴.Fiber V),
      Presheaf.IsLocallyInjective (J.over V) (hj.morPresheafMap y₁ y₂) ∧
        Presheaf.IsLocallySurjective (J.over V) (hj.morPresheafMap y₁ y₂))
    (hmor𝒵 : ∀ (V : 𝒞) (z₁ z₂ : p𝒵.Fiber V),
      Presheaf.IsLocallyInjective (J.over V) (hk.morPresheafMap z₁ z₂) ∧
        Presheaf.IsLocallySurjective (J.over V) (hk.morPresheafMap z₁ z₂))
    (U : 𝒞) (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap P Q) ∧
      Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap P Q) := by
  have hfst := fst_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg
  have hsnd := snd_isFibredOneMorphism p𝒳 p𝒵 p𝒴 f g hf hg
  have hfst' := fst_isFibredOneMorphism p𝒳' p𝒵' p𝒴' f' g' hf' hg'
  have hsnd' := snd_isFibredOneMorphism p𝒳' p𝒵' p𝒴' f' g' hf' hg'
  -- the squares with the two projections
  have hsq1 : hH.morPresheafMap P Q ≫ hfst'.morPresheafMap
        ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q) =
      hfst.morPresheafMap P Q ≫ hi.morPresheafMap
        ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q) := by
    rw [IsFibredOneMorphism.morPresheafMap_comp, IsFibredOneMorphism.morPresheafMap_comp]
  have hsq2 : hH.morPresheafMap P Q ≫ hsnd'.morPresheafMap
        ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q) =
      hsnd.morPresheafMap P Q ≫ hk.morPresheafMap
        ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q) := by
    rw [IsFibredOneMorphism.morPresheafMap_comp, IsFibredOneMorphism.morPresheafMap_comp]
  -- the middle leg of the comparison of cospans
  have hnα := IsFibredOneMorphism.morPresheafMap_natIso (hi.comp hf') (hf.comp hj) α hα
    (fibFst P) (fibFst Q)
  have hnβ := IsFibredOneMorphism.morPresheafMap_natIso (hk.comp hg') (hg.comp hj) β hβ
    (fibSnd P) (fibSnd Q)
  -- the cospan square on the `𝒳`-leg
  have h₁ : hi.morPresheafMap ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q) ≫
      hf'.morPresheafMap (fibFst ((fiberFunctorOfCompEq hH.comp_eq U).obj P))
        (fibFst ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)) =
      hf.morPresheafMap (fibFst P) (fibFst Q) ≫
        (hj.morPresheafMap ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst P))
          ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst Q)) ≫
        (morPresheafFiberIso p𝒴' (alphaFib hi hj α hα hf hf' (fibFst P))
          (alphaFib hi hj α hα hf hf' (fibFst Q))).inv) := by
    have e1 : hi.morPresheafMap ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
          ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q) ≫
        hf'.morPresheafMap (fibFst ((fiberFunctorOfCompEq hH.comp_eq U).obj P))
          (fibFst ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)) =
        (hi.comp hf').morPresheafMap (fibFst P) (fibFst Q) :=
      IsFibredOneMorphism.morPresheafMap_comp hi hf' (fibFst P) (fibFst Q)
    have e2 : hf.morPresheafMap (fibFst P) (fibFst Q) ≫
        hj.morPresheafMap ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst P))
          ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst Q)) =
        (hf.comp hj).morPresheafMap (fibFst P) (fibFst Q) :=
      IsFibredOneMorphism.morPresheafMap_comp hf hj (fibFst P) (fibFst Q)
    rw [e1, ← Category.assoc, e2]
    exact (Iso.eq_comp_inv _).2 hnα
  -- the cospan square on the `𝒵`-leg
  have hcompat := fibIso_stackifyMap hi hj hk α hα β hβ hf hg hf' hg' P hH
  have hcompatQ := fibIso_stackifyMap hi hj hk α hα β hβ hf hg hf' hg' Q hH
  have hcompatInv : (betaFib hj hk β hβ hg hg' (fibSnd Q)).inv ≫
        (fibIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).inv =
      (fiberFunctorOfCompEq hj.comp_eq U).map (fibIso hf hg Q).inv ≫
        (alphaFib hi hj α hα hf hf' (fibFst Q)).inv := by
    have hiso : (fibIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)) ≪≫
          (betaFib hj hk β hβ hg hg' (fibSnd Q)) =
        (alphaFib hi hj α hα hf hf' (fibFst Q)) ≪≫
          (fiberFunctorOfCompEq hj.comp_eq U).mapIso (fibIso hf hg Q) := Iso.ext hcompatQ
    have h := congrArg Iso.inv hiso
    simpa using h
  have h₂ : hk.morPresheafMap ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q) ≫
      morSnd hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q) =
      morSnd hf hg P Q ≫
        (hj.morPresheafMap ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst P))
          ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst Q)) ≫
        (morPresheafFiberIso p𝒴' (alphaFib hi hj α hα hf hf' (fibFst P))
          (alphaFib hi hj α hα hf hf' (fibFst Q))).inv) := by
    have e3 : hk.morPresheafMap ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
          ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q) ≫
        hg'.morPresheafMap (fibSnd ((fiberFunctorOfCompEq hH.comp_eq U).obj P))
          (fibSnd ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)) =
        (hk.comp hg').morPresheafMap (fibSnd P) (fibSnd Q) :=
      IsFibredOneMorphism.morPresheafMap_comp hk hg' (fibSnd P) (fibSnd Q)
    have e4 : hg.morPresheafMap (fibSnd P) (fibSnd Q) ≫
        hj.morPresheafMap ((fiberFunctorOfCompEq hg.comp_eq U).obj (fibSnd P))
          ((fiberFunctorOfCompEq hg.comp_eq U).obj (fibSnd Q)) =
        (hg.comp hj).morPresheafMap (fibSnd P) (fibSnd Q) :=
      IsFibredOneMorphism.morPresheafMap_comp hg hj (fibSnd P) (fibSnd Q)
    have econj := IsFibredOneMorphism.morPresheafMap_conj hj (fibIso hf hg P).hom
      (fibIso hf hg Q).inv
    have hnβ' : (hk.comp hg').morPresheafMap (fibSnd P) (fibSnd Q) =
        (hg.comp hj).morPresheafMap (fibSnd P) (fibSnd Q) ≫
          _root_.CategoryTheory.Functor.morPresheafMap p𝒴'
            (betaFib hj hk β hβ hg hg' (fibSnd P)).hom
            (betaFib hj hk β hβ hg hg' (fibSnd Q)).inv :=
      (Iso.eq_comp_inv (morPresheafFiberIso p𝒴' (betaFib hj hk β hβ hg hg' (fibSnd P))
        (betaFib hj hk β hβ hg hg' (fibSnd Q)))).2 hnβ
    have ekey : _root_.CategoryTheory.Functor.morPresheafMap p𝒴'
            (betaFib hj hk β hβ hg hg' (fibSnd P)).hom
            (betaFib hj hk β hβ hg hg' (fibSnd Q)).inv ≫
          _root_.CategoryTheory.Functor.morPresheafMap p𝒴'
            (fibIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)).hom
            (fibIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).inv =
        _root_.CategoryTheory.Functor.morPresheafMap p𝒴'
            ((fiberFunctorOfCompEq hj.comp_eq U).map (fibIso hf hg P).hom)
            ((fiberFunctorOfCompEq hj.comp_eq U).map (fibIso hf hg Q).inv) ≫
          _root_.CategoryTheory.Functor.morPresheafMap p𝒴'
            (alphaFib hi hj α hα hf hf' (fibFst P)).hom
            (alphaFib hi hj α hα hf hf' (fibFst Q)).inv := by
      rw [_root_.CategoryTheory.Functor.morPresheafMap_comp,
        _root_.CategoryTheory.Functor.morPresheafMap_comp, hcompat, hcompatInv]
    simp only [morSnd, morPresheafFiberIso_hom, morPresheafFiberIso_inv, Iso.symm_hom,
      Iso.symm_inv, Category.assoc]
    rw [reassoc_of% e3, hnβ']
    simp only [Category.assoc]
    rw [reassoc_of% econj.symm, reassoc_of% e4, ekey]
  -- the identification of the map with a map of fibre products
  have hstar : hH.morPresheafMap P Q ≫ (morPresheafEqPullbackIso hf' hg'
        ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).hom =
      (morPresheafEqPullbackIso hf hg P Q).hom ≫
        Presheaf.eqPullbackMap (hf.morPresheafMap (fibFst P) (fibFst Q)) (morSnd hf hg P Q)
          (hf'.morPresheafMap (fibFst ((fiberFunctorOfCompEq hH.comp_eq U).obj P))
            (fibFst ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)))
          (morSnd hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hH.comp_eq U).obj Q))
          (hi.morPresheafMap ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q))
          (hk.morPresheafMap ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q))
          (hj.morPresheafMap ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst P))
            ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst Q)) ≫
            (morPresheafFiberIso p𝒴' (alphaFib hi hj α hα hf hf' (fibFst P))
              (alphaFib hi hj α hα hf hf' (fibFst Q))).inv) h₁ h₂ := by
    ext o m
    refine Subtype.ext (Prod.ext ?_ ?_)
    · have hs := ConcreteCategory.congr_hom (NatTrans.congr_app hsq1 o) m
      exact (morPresheafEqPullbackIso_hom_val_fst hf' hg'
          ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
          ((fiberFunctorOfCompEq hH.comp_eq U).obj Q) o
          ((hH.morPresheafMap P Q).app o m)).trans
        (hs.trans (congrArg (fun t ↦ (hi.morPresheafMap
            ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q)).app o t)
          (morPresheafEqPullbackIso_hom_val_fst hf hg P Q o m).symm))
    · have hs := ConcreteCategory.congr_hom (NatTrans.congr_app hsq2 o) m
      exact (morPresheafEqPullbackIso_hom_val_snd hf' hg'
          ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
          ((fiberFunctorOfCompEq hH.comp_eq U).obj Q) o
          ((hH.morPresheafMap P Q).app o m)).trans
        (hs.trans (congrArg (fun t ↦ (hk.morPresheafMap
            ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q)).app o t)
          (morPresheafEqPullbackIso_hom_val_snd hf hg P Q o m).symm))
  -- transport the two properties across the identification
  have := (hmor𝒳 U ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
    ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q)).1
  have := (hmor𝒳 U ((fiberFunctorOfCompEq hfst.comp_eq U).obj P)
    ((fiberFunctorOfCompEq hfst.comp_eq U).obj Q)).2
  have := (hmor𝒵 U ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
    ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q)).1
  have := (hmor𝒵 U ((fiberFunctorOfCompEq hsnd.comp_eq U).obj P)
    ((fiberFunctorOfCompEq hsnd.comp_eq U).obj Q)).2
  have := (hmor𝒴 U ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst P))
    ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst Q))).1
  have hlcC : Presheaf.IsLocallyInjective (J.over U)
      (hj.morPresheafMap ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst P))
          ((fiberFunctorOfCompEq hf.comp_eq U).obj (fibFst Q)) ≫
        (morPresheafFiberIso p𝒴' (alphaFib hi hj α hα hf hf' (fibFst P))
          (alphaFib hi hj α hα hf hf' (fibFst Q))).inv) := inferInstance
  have := Presheaf.isLocallyInjective_eqPullbackMap _ _ _ _ _ _ _ h₁ h₂ (J.over U)
  have := Presheaf.isLocallySurjective_eqPullbackMap _ _ _ _ _ _ _ h₁ h₂ (J.over U)
  have hcompLI : Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap P Q ≫
      (morPresheafEqPullbackIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).hom) := by
    rw [hstar]; infer_instance
  have hcompLS : Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap P Q ≫
      (morPresheafEqPullbackIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).hom) := by
    rw [hstar]; infer_instance
  have := hcompLI
  have := hcompLS
  exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective (J.over U) (hH.morPresheafMap P Q)
      (morPresheafEqPullbackIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).hom,
    Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective (J.over U)
      (hH.morPresheafMap P Q)
      (morPresheafEqPullbackIso hf' hg' ((fiberFunctorOfCompEq hH.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hH.comp_eq U).obj Q)).hom⟩

omit [p𝒳'.IsFibered] [p𝒵'.IsFibered]
  [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered] in
/-- **Clause (2) of Stacks 02ZN for the canonical 1-morphism of 2-fibre products.** Every object
`P' = (U, x', z', ψ')` of `𝒳' ×_{𝒴'} 𝒵'` receives, along a covering sieve of `U`, strongly
cartesian morphisms from objects of the form `H P`: locally `x' = i x` and `z' = k z`, and the
comparison `ψ'` transports through `α` and `β` to an isomorphism `j(f x) ≅ j(g z)` which, `j` being
a stackification, descends locally to an isomorphism `f(x|_W) ≅ g(z|_W)`. -/
lemma exists_covering_stackifyMap {J : GrothendieckTopology 𝒞}
    (hH : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') (stackifyMap hi hj hk α hα β hβ))
    (hmor𝒴 : ∀ (W : 𝒞) (y₁ y₂ : p𝒴.Fiber W),
      Presheaf.IsLocallyInjective (J.over W) (hj.morPresheafMap y₁ y₂) ∧
        Presheaf.IsLocallySurjective (J.over W) (hj.morPresheafMap y₁ y₂))
    (hobj𝒳 : ∀ x' : 𝒳', ∃ R ∈ J (p𝒳'.obj x'), ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒳'.obj x'), R.arrows u →
      ∃ (x : 𝒳) (φ : i.obj x ⟶ x'), p𝒳'.IsStronglyCartesian u φ)
    (hobj𝒵 : ∀ z' : 𝒵', ∃ R ∈ J (p𝒵'.obj z'), ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒵'.obj z'), R.arrows u →
      ∃ (z : 𝒵) (φ : k.obj z ⟶ z'), p𝒵'.IsStronglyCartesian u φ)
    (P' : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g') :
    ∃ R ∈ J P'.base, ∀ ⦃V : 𝒞⦄ (u : V ⟶ P'.base), R.arrows u →
      ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g)
        (Φ : (stackifyMap hi hj hk α hα β hβ).obj P ⟶ P'),
        (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian u Φ := by
  refine ⟨⟨fun {V} u ↦ ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g)
      (Φ : (stackifyMap hi hj hk α hα β hβ).obj P ⟶ P'),
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian u Φ, ?_⟩, ?_, fun _ _ hu ↦ hu⟩
  · -- the property is stable under precomposition: use a cartesian lift downstairs
    intro V W u hu γ
    obtain ⟨P, Φ, hΦ⟩ := hu
    have := hΦ
    have hPV : (structureFunctor p𝒳 p𝒵 p𝒴 f g).obj P = V :=
      IsHomLift.domain_eq (structureFunctor p𝒳' p𝒵' p𝒴' f' g') u Φ
    obtain ⟨P₁, Ψ, hΨ⟩ := IsPreFibered.exists_isCartesian (structureFunctor p𝒳 p𝒵 p𝒴 f g) hPV γ
    have := hΨ
    have hsc : (structureFunctor p𝒳 p𝒵 p𝒴 f g).IsStronglyCartesian γ Ψ := inferInstance
    have := hH.map_isStronglyCartesian γ Ψ hsc
    exact ⟨P₁, (stackifyMap hi hj hk α hα β hβ).map Ψ ≫ Φ, inferInstance⟩
  · -- the property holds on a covering sieve
    obtain ⟨R₀, hR₀, hR₀prop⟩ := hobj𝒳 P'.x
    obtain ⟨R₁, hR₁, hR₁prop⟩ := hobj𝒵 P'.y
    refine J.transitive (J.intersection_covering
      (J.pullback_stable (eqToHom P'.hx.symm) hR₀)
      (J.pullback_stable (eqToHom P'.hy.symm) hR₁)) _ ?_
    intro V u hu
    obtain ⟨x, φ₁, hφ₁'⟩ := hR₀prop (u ≫ eqToHom P'.hx.symm) hu.1
    obtain ⟨z, φ₂, hφ₂'⟩ := hR₁prop (u ≫ eqToHom P'.hy.symm) hu.2
    have hφ₁ : p𝒳'.IsStronglyCartesian u φ₁ :=
      isStronglyCartesian_of_comp_eqToHom P'.hx.symm u φ₁ hφ₁'
    have hφ₂ : p𝒵'.IsStronglyCartesian u φ₂ :=
      isStronglyCartesian_of_comp_eqToHom P'.hy.symm u φ₂ hφ₂'
    have := hφ₁
    have := hφ₂
    obtain ⟨x₀, rfl⟩ := hi.exists_fiber_obj_eq u φ₁
    obtain ⟨z₀, rfl⟩ := hk.exists_fiber_obj_eq u φ₂
    -- the comparison isomorphism `f'(i x) ≅ g'(k z)` of the fibre over `V`
    have := P'.vertical
    have hcart1 : p𝒴'.IsStronglyCartesian u (f'.map φ₁ ≫ P'.iso.hom) := by
      have h1 : p𝒴'.IsStronglyCartesian u (f'.map φ₁) := hf'.map_isStronglyCartesian u φ₁ hφ₁
      have h2 : p𝒴'.IsStronglyCartesian (𝟙 P'.base) P'.iso.hom :=
        Functor.IsStronglyCartesian.of_iso p𝒴' (𝟙 P'.base) P'.iso
      have := h1
      have := h2
      have h0 : p𝒴'.IsStronglyCartesian (u ≫ 𝟙 P'.base) (f'.map φ₁ ≫ P'.iso.hom) :=
        inferInstance
      rwa [Category.comp_id] at h0
    have hcart2 : p𝒴'.IsStronglyCartesian u (g'.map φ₂) := hg'.map_isStronglyCartesian u φ₂ hφ₂
    have := hcart1
    have := hcart2
    obtain ⟨θ, hθfac⟩ : ∃ θ : (fiberFunctorOfCompEq (hi.comp hf').comp_eq V).obj x₀ ≅
        (fiberFunctorOfCompEq (hk.comp hg').comp_eq V).obj z₀,
        Fiber.fiberInclusion.map θ.hom ≫ g'.map φ₂ = f'.map φ₁ ≫ P'.iso.hom :=
      ⟨fiberIsoOfCartesian u (f'.map φ₁ ≫ P'.iso.hom) (g'.map φ₂) inferInstance inferInstance,
        fiberIsoOfCartesian_hom_fac _ _ _ _ _⟩
    obtain ⟨θ', hθrel⟩ : ∃ θ' : (fiberFunctorOfCompEq (hf.comp hj).comp_eq V).obj x₀ ≅
        (fiberFunctorOfCompEq (hg.comp hj).comp_eq V).obj z₀,
        Fiber.fiberInclusion.map θ.hom =
          α.hom.app x₀.1 ≫ Fiber.fiberInclusion.map θ'.hom ≫ β.inv.app z₀.1 :=
      ⟨(alphaFib hi hj α hα hf hf' x₀).symm ≪≫ θ ≪≫ betaFib hj hk β hβ hg hg' z₀, by
        simp only [comp_obj, Iso.trans_hom, Iso.symm_hom, map_comp,
          IsFibredOneMorphism.fiberInclusion_map_natIsoFiber_inv,
          IsFibredOneMorphism.fiberInclusion_map_natIsoFiber_hom, Category.assoc,
          Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
        exact (Category.comp_id _).symm⟩
    -- the isomorphism descends locally along `j`
    obtain ⟨R₂, hR₂, hR₂prop⟩ := IsFibredOneMorphism.exists_locally_descends_iso hj
      ((fiberFunctorOfCompEq hf.comp_eq V).obj x₀)
      ((fiberFunctorOfCompEq hg.comp_eq V).obj z₀) hmor𝒴 θ'
    refine J.superset_covering ?_ hR₂
    intro W b hb
    obtain ⟨t, ht⟩ := hR₂prop b hb
    obtain ⟨A, hAhom⟩ : ∃ A : (fiberFunctorOfCompEq hf.comp_eq W).obj
          (pullbackFiber p𝒳 x₀ b) ≅
        (fiberFunctorOfCompEq hg.comp_eq W).obj (pullbackFiber p𝒵 z₀ b),
        Fiber.fiberInclusion.map A.hom =
          Fiber.fiberInclusion.map (hf.mapPullbackFiberIso x₀ b).inv ≫
            Fiber.fiberInclusion.map t.hom ≫
            Fiber.fiberInclusion.map (hg.mapPullbackFiberIso z₀ b).hom :=
      ⟨(hf.mapPullbackFiberIso x₀ b).symm ≪≫ t ≪≫ hg.mapPullbackFiberIso z₀ b, by simp⟩
    -- the descended isomorphism intertwines the two base changes
    have hinner : Fiber.fiberInclusion.map A.hom ≫ g.map (IsPreFibered.pullbackMap z₀.2 b) =
        Fiber.fiberInclusion.map (hf.mapPullbackFiberIso x₀ b).inv ≫
          Fiber.fiberInclusion.map t.hom ≫
          IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hg.comp_eq V).obj z₀).2 b := by
      rw [hAhom]
      simp only [Category.assoc]
      rw [IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hg z₀ b]
    have hd2 : j.map (Fiber.fiberInclusion.map A.hom ≫
          g.map (IsPreFibered.pullbackMap z₀.2 b)) =
        j.map (f.map (IsPreFibered.pullbackMap x₀.2 b)) ≫ Fiber.fiberInclusion.map θ'.hom := by
      rw [hinner, Functor.map_comp, Functor.map_comp, ht,
        ← IsFibredOneMorphism.mapPullbackFiberIso_inv_fac hf x₀ b,
        Functor.map_comp, Category.assoc]
    -- the two naturality squares of `α` and `β`
    have hnatα : f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b)) ≫ α.hom.app x₀.1 =
        α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
          j.map (f.map (IsPreFibered.pullbackMap x₀.2 b)) :=
      α.hom.naturality (IsPreFibered.pullbackMap x₀.2 b)
    have hnatβ : j.map (g.map (IsPreFibered.pullbackMap z₀.2 b)) ≫ β.inv.app z₀.1 =
        β.inv.app (pullbackFiber p𝒵 z₀ b).1 ≫
          g'.map (k.map (IsPreFibered.pullbackMap z₀.2 b)) :=
      β.inv.naturality (IsPreFibered.pullbackMap z₀.2 b)
    -- the comparison square, before composing with the cartesian lifts at `P'`
    have hstep : f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b)) ≫
          Fiber.fiberInclusion.map θ.hom =
        (α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫ j.map (Fiber.fiberInclusion.map A.hom) ≫
            β.inv.app (pullbackFiber p𝒵 z₀ b).1) ≫
          g'.map (k.map (IsPreFibered.pullbackMap z₀.2 b)) := by
      calc f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b)) ≫ Fiber.fiberInclusion.map θ.hom
          = (f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b)) ≫ α.hom.app x₀.1) ≫
              Fiber.fiberInclusion.map θ'.hom ≫ β.inv.app z₀.1 := by
            rw [hθrel]; simp [Category.assoc]
        _ = (α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
              j.map (f.map (IsPreFibered.pullbackMap x₀.2 b))) ≫
              Fiber.fiberInclusion.map θ'.hom ≫ β.inv.app z₀.1 := by rw [hnatα]
        _ = α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
              (j.map (f.map (IsPreFibered.pullbackMap x₀.2 b)) ≫
                Fiber.fiberInclusion.map θ'.hom) ≫ β.inv.app z₀.1 := by
            simp [Category.assoc]
        _ = α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
              j.map (Fiber.fiberInclusion.map A.hom ≫
                g.map (IsPreFibered.pullbackMap z₀.2 b)) ≫ β.inv.app z₀.1 := by rw [hd2]
        _ = α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
              j.map (Fiber.fiberInclusion.map A.hom) ≫
              (j.map (g.map (IsPreFibered.pullbackMap z₀.2 b)) ≫ β.inv.app z₀.1) := by
            rw [Functor.map_comp]; simp [Category.assoc]
        _ = α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
              j.map (Fiber.fiberInclusion.map A.hom) ≫
              (β.inv.app (pullbackFiber p𝒵 z₀ b).1 ≫
                g'.map (k.map (IsPreFibered.pullbackMap z₀.2 b))) := by rw [hnatβ]
        _ = _ := by simp [Category.assoc]
    -- the comparison square of the morphism to `P'`
    have hw : f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b) ≫ φ₁) ≫ P'.iso.hom =
        (α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫ j.map (Fiber.fiberInclusion.map A.hom) ≫
            β.inv.app (pullbackFiber p𝒵 z₀ b).1) ≫
          g'.map (k.map (IsPreFibered.pullbackMap z₀.2 b) ≫ φ₂) := by
      calc f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b) ≫ φ₁) ≫ P'.iso.hom
          = f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b)) ≫
              (f'.map φ₁ ≫ P'.iso.hom) := by rw [Functor.map_comp]; simp [Category.assoc]
        _ = (f'.map (i.map (IsPreFibered.pullbackMap x₀.2 b)) ≫
              Fiber.fiberInclusion.map θ.hom) ≫ g'.map φ₂ := by
            rw [← hθfac]; simp [Category.assoc]
        _ = ((α.hom.app (pullbackFiber p𝒳 x₀ b).1 ≫
              j.map (Fiber.fiberInclusion.map A.hom) ≫
              β.inv.app (pullbackFiber p𝒵 z₀ b).1) ≫
              g'.map (k.map (IsPreFibered.pullbackMap z₀.2 b))) ≫ g'.map φ₂ := by rw [hstep]
        _ = _ := by rw [Functor.map_comp]; simp [Category.assoc]
    -- the two components lie over, and are strongly cartesian over, `b ≫ u`
    have hasc := hi.isStronglyCartesian_map_pullbackMap_comp x₀ b u φ₁
    have hbsc := hk.isStronglyCartesian_map_pullbackMap_comp z₀ b u φ₂
    refine
      ⟨{ base := W, x := (pullbackFiber p𝒳 x₀ b).1, y := (pullbackFiber p𝒵 z₀ b).1,
          hx := (pullbackFiber p𝒳 x₀ b).2, hy := (pullbackFiber p𝒵 z₀ b).2,
          iso := Fiber.fiberInclusion.mapIso A, vertical := A.hom.2 },
        { hbase := b ≫ u, a := i.map (IsPreFibered.pullbackMap x₀.2 b) ≫ φ₁,
          b := k.map (IsPreFibered.pullbackMap z₀.2 b) ≫ φ₂,
          ha := hasc.toIsHomLift, hb := hbsc.toIsHomLift, w := hw }, ?_⟩
    refine isStronglyCartesian_of_components hf' hg' (b ≫ u) _ ?_ hasc hbsc
    refine IsHomLift.of_fac' (structureFunctor p𝒳' p𝒵' p𝒴' f' g') (b ≫ u) _ rfl rfl ?_
    simp

end Clause

/-! ### Stacks 04Y1 -/

/-- **Stacks 04Y1.** Let `(𝒞, J)` be a site, let `f : 𝒳 ⥤ 𝒴` and `g : 𝒵 ⥤ 𝒴` be 1-morphisms of
fibred categories over `𝒞`, and let `i : 𝒳 ⥤ 𝒳'`, `j : 𝒴 ⥤ 𝒴'`, `k : 𝒵 ⥤ 𝒵'` be stackifications
(Stacks 02ZP: the targets are stacks over `(𝒞, J)`, the induced maps `Mor(x, y) ⟶ Mor(i x, i y)` of
presheaves on `𝒞/U` are locally bijective, and every object of the target is locally in the
essential image), and let `f' : 𝒳' ⥤ 𝒴'`, `g' : 𝒵' ⥤ 𝒴'` be 1-morphisms of fibred categories over
`𝒞` 2-commuting with `f` and `g` along `i`, `j`, `k` via vertical 2-isomorphisms `α`, `β`. Then the
stackification of the 2-fibre product is the 2-fibre product of the stackifications: the 2-fibre
product `𝒳' ×_{𝒴'} 𝒵'` is a stack over `(𝒞, J)` — it is a fibred category by Stacks 02XQ — and the
canonical 1-morphism `𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'`,
`CategoryTheory.TwoFibreProductOver.stackifyMap`, is a 1-morphism of fibred categories over `𝒞`
which is a stackification of `𝒳 ×_𝒴 𝒵`, in the same two clauses. -/
@[stacks 04Y1]
theorem isStackification_stackifyMap {J : GrothendieckTopology 𝒞}
    (h𝒳 : p𝒳.IsFibered) (h𝒴 : p𝒴.IsFibered) (h𝒵 : p𝒵.IsFibered)
    (hs𝒳' : p𝒳'.IsStack J) (hs𝒴' : p𝒴'.IsStack J) (hs𝒵' : p𝒵'.IsStack J)
    (hf : p𝒳.IsFibredOneMorphism p𝒴 f) (hg : p𝒵.IsFibredOneMorphism p𝒴 g)
    (hf' : p𝒳'.IsFibredOneMorphism p𝒴' f') (hg' : p𝒵'.IsFibredOneMorphism p𝒴' g')
    (hi : p𝒳.IsFibredOneMorphism p𝒳' i) (hj : p𝒴.IsFibredOneMorphism p𝒴' j)
    (hk : p𝒵.IsFibredOneMorphism p𝒵' k)
    (hmor𝒳 : haveI : p𝒳.IsFibered := h𝒳
      haveI : p𝒳'.IsFibered := hs𝒳'.isFibered
      ∀ (V : 𝒞) (x₁ x₂ : p𝒳.Fiber V),
        Presheaf.IsLocallyInjective (J.over V) (hi.morPresheafMap x₁ x₂) ∧
          Presheaf.IsLocallySurjective (J.over V) (hi.morPresheafMap x₁ x₂))
    (hobj𝒳 : ∀ x' : 𝒳', ∃ R ∈ J (p𝒳'.obj x'), ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒳'.obj x'), R.arrows u →
      ∃ (x : 𝒳) (φ : i.obj x ⟶ x'), p𝒳'.IsStronglyCartesian u φ)
    (hmor𝒴 : haveI : p𝒴.IsFibered := h𝒴
      haveI : p𝒴'.IsFibered := hs𝒴'.isFibered
      ∀ (V : 𝒞) (y₁ y₂ : p𝒴.Fiber V),
        Presheaf.IsLocallyInjective (J.over V) (hj.morPresheafMap y₁ y₂) ∧
          Presheaf.IsLocallySurjective (J.over V) (hj.morPresheafMap y₁ y₂))
    (_hobj𝒴 : ∀ y' : 𝒴', ∃ R ∈ J (p𝒴'.obj y'), ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒴'.obj y'), R.arrows u →
      ∃ (y : 𝒴) (φ : j.obj y ⟶ y'), p𝒴'.IsStronglyCartesian u φ)
    (hmor𝒵 : haveI : p𝒵.IsFibered := h𝒵
      haveI : p𝒵'.IsFibered := hs𝒵'.isFibered
      ∀ (V : 𝒞) (z₁ z₂ : p𝒵.Fiber V),
        Presheaf.IsLocallyInjective (J.over V) (hk.morPresheafMap z₁ z₂) ∧
          Presheaf.IsLocallySurjective (J.over V) (hk.morPresheafMap z₁ z₂))
    (hobj𝒵 : ∀ z' : 𝒵', ∃ R ∈ J (p𝒵'.obj z'), ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒵'.obj z'), R.arrows u →
      ∃ (z : 𝒵) (φ : k.obj z ⟶ z'), p𝒵'.IsStronglyCartesian u φ)
    (α : i ⋙ f' ≅ f ⋙ j) (hα : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x))
    (β : k ⋙ g' ≅ g ⋙ j) (hβ : ∀ z : 𝒵, p𝒴'.IsHomLift (𝟙 (p𝒵.obj z)) (β.hom.app z)) :
    haveI : p𝒳.IsFibered := h𝒳
    haveI : p𝒴.IsFibered := h𝒴
    haveI : p𝒵.IsFibered := h𝒵
    haveI : p𝒳'.IsFibered := hs𝒳'.isFibered
    haveI : p𝒴'.IsFibered := hs𝒴'.isFibered
    haveI : p𝒵'.IsFibered := hs𝒵'.isFibered
    haveI : (structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered :=
      isFibered_structureFunctor p𝒳 p𝒵 p𝒴 f g hf hg
    haveI : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered :=
      isFibered_structureFunctor p𝒳' p𝒵' p𝒴' f' g' hf' hg'
    (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStack J ∧
      ∃ hH : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
          (structureFunctor p𝒳' p𝒵' p𝒴' f' g') (stackifyMap hi hj hk α hα β hβ),
        (∀ (U : 𝒞) (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U),
            Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap P Q) ∧
              Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap P Q)) ∧
          ∀ P' : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g', ∃ R ∈ J P'.base,
            ∀ ⦃V : 𝒞⦄ (u : V ⟶ P'.base), R.arrows u →
              ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g)
                (Φ : (stackifyMap hi hj hk α hα β hβ).obj P ⟶ P'),
                (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian u Φ := by
  have : p𝒳.IsFibered := h𝒳
  have : p𝒴.IsFibered := h𝒴
  have : p𝒵.IsFibered := h𝒵
  have : p𝒳'.IsFibered := hs𝒳'.isFibered
  have : p𝒴'.IsFibered := hs𝒴'.isFibered
  have : p𝒵'.IsFibered := hs𝒵'.isFibered
  have : (structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered :=
    isFibered_structureFunctor p𝒳 p𝒵 p𝒴 f g hf hg
  have : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered :=
    isFibered_structureFunctor p𝒳' p𝒵' p𝒴' f' g' hf' hg'
  have hH := isFibredOneMorphism_stackifyMap hi hj hk α hα β hβ hf hg hf' hg'
  refine ⟨isStack_structureFunctor p𝒳' p𝒵' p𝒴' f' g' J hs𝒳' hs𝒵' hs𝒴' hf' hg', hH, ?_, ?_⟩
  · exact isLocallyBijective_morPresheafMap_stackifyMap hi hj hk α hα β hβ hf hg hf' hg' hH
      hmor𝒳 hmor𝒴 hmor𝒵
  · exact exists_covering_stackifyMap hi hj hk α hα β hβ hf hg hf' hg' hH hmor𝒴 hobj𝒳 hobj𝒵

end TwoFibreProductOver

end CategoryTheory

end
