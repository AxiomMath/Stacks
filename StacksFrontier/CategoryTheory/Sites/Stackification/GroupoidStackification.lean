module

public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence

/-! # The stackification of a category fibred in groupoids is a stack in groupoids

Let `(𝒞, J)` be a site and let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids (Stacks 003S).
Stacks 02ZP asserts that there are a **stack in groupoids** `p' : 𝒮' ⥤ 𝒞` and a 1-morphism
`G : 𝒮 ⥤ 𝒮'` over `𝒞` such that

1. for every `U` and all `x`, `y` in the fibre `𝒮_U` the induced map `Mor(x, y) ⟶ Mor(G x, G y)`
   of presheaves on `𝒞/U` identifies the target with the sheafification of the source, and
2. every object of `𝒮'` is, locally on the base, in the essential image of `G`.

The source proves it by running the construction of Stacks 02ZN — which produces the
stackification of an arbitrary *fibred* category — and observing that when the input is fibred in
groupoids so is the output. This file is that observation, and only that observation: the
stackification of the underlying fibred category is **taken as a hypothesis**, spelled out as the
conclusion of Stacks 02ZN, and what is proved is that its target is fibred in groupoids, so that
the same data exhibits a stackification *in groupoids*. Once the construction of Stacks 02ZN is
assembled it supplies those hypotheses and the two results below become unconditional.

The mathematical content is that invertibility of a morphism of a fibre of `𝒮'` is a local
condition. A morphism `m : x' ⟶ y'` of the fibre of `𝒮'` over `U` restricts, along a covering
sieve, to a morphism between objects in the image of `G` (clause (2)); such a morphism is, along a
further covering sieve, the image under `G` of a morphism of a fibre of `𝒮` (local surjectivity in
clause (1)); and morphisms of the fibres of `𝒮` are invertible because `p` is fibred in groupoids.
Invertibility then propagates back up because the presheaves `Mor(·, ·)` of `𝒮'` are sheaves: the
local inverses glue (`CategoryTheory.Functor.exists_fiberIso_of_locally`) and separatedness
identifies the glued morphism with `m`.

## Main results

* `CategoryTheory.Functor.isIso_of_locally_isIso`, that a morphism of a fibre whose base changes
  along a covering sieve are invertible is itself invertible;
* `CategoryTheory.Functor.Stackification.isFiberedInGroupoids_of_isStackification`, that the
  target of a stackification of a category fibred in groupoids is fibred in groupoids, and
  `CategoryTheory.Functor.Stackification.isStackInGroupoids_of_isStackification`, that it is
  therefore a stack in groupoids. These are Stacks 02ZP, conditional on being given a
  stackification of the underlying fibred category.

The other half of Stacks 02ZP, its closing sentence that the target is *determined up to unique
2-isomorphism* by the two clauses, is not here: it is
`StacksFrontier/CategoryTheory/Sites/Stackification/Uniqueness.lean`. The results below carry the
two clauses from hypothesis to conclusion, so they cannot by themselves identify two stackifications
of one fibred category; that is what the determinacy clause does, and it is the direction a
consumer checking the two clauses for a functor of its own needs.

## Implementation notes

"Stack in groupoids" is spelled, as in
`StacksFrontier/CategoryTheory/Sites/Stackification/UniversalPropertyGroupoid.lean` (Stacks 0436)
and `StacksFrontier/CategoryTheory/Sites/Stackification/TwoFibreProductGroupoid.lean` (Stacks 04Y2),
as `CategoryTheory.Functor.IsFiberedInGroupoids` (Stacks 003S) together with
`CategoryTheory.Functor.IsStack` (Stacks 026F). That is reading (3) of Stacks 02ZJ; the other
rendering in the tree, `CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI), is not used,
only the implication 026F ⟹ 02ZI being available.

"`G` is a stackification of the underlying fibred category" is spelled out from the conclusion of
Stacks 02ZN rather than referred to a predicate, there being none in the tree: `G` is a
1-morphism of fibred categories over `𝒞`
(`CategoryTheory.Functor.IsFibredOneMorphism`, which for a functor strictly over `𝒞` between
categories fibred in groupoids is automatic by Stacks 003V, but here `𝒮'` is not yet known to be
fibred in groupoids), its target is a stack, and clauses (1) and (2) hold. The spelling of the two
clauses is the one fixed by Stacks 0435 and reused by Stacks 0436: clause (1) through the
canonical map of Stacks 042V
(`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`) between the presheaves `Mor(x, y)`
of Stacks 02ZB on the slice `𝒞/U`, asked to be locally injective and locally surjective for the
induced topology `J.over U` — the standard characterisation of a sheafification map, the target
being a sheaf because `𝒮'` is a stack — and clause (2) as: every object of a fibre of `𝒮'` is,
along a covering sieve, in the essential image of the functor `𝒮_V ⥤ 𝒮'_V` on fibres.

Faithfulness. (1) No hypothesis is dead except the local *injectivity* half of `hmor`, which is
carried because clause (1) of Stacks 02ZP is "identifies the target with the sheafification of the
source" and local injectivity is half of that; dropping it would state a strictly weaker
hypothesis than the source's, but the proof below needs only local surjectivity. `hp` is what
makes the fibres of `𝒮` groupoids, `hsp'` supplies both the fibredness of `𝒮'` and the sheaf
condition on `Mor(·, ·)` that the gluing consumes, `hG` is what makes the maps of morphism
presheaves exist, and `hobj` is clause (2), without which nothing relates a general object of `𝒮'`
to `𝒮`. (2) The site is the source's: one `(𝒞, J)` throughout, both structure functors land in
that `𝒞`, `G` is strictly over it, and the presheaves `Mor(·, ·)` are presheaves on the slice
`𝒞/U` for the induced topology `J.over U`. (3) The conclusion is the one piece of Stacks 02ZP that
is not already a hypothesis: that `𝒮'` is fibred in groupoids and hence a stack in groupoids.
(4) The hypotheses are satisfiable non-vacuously: a stack in groupoids is its own stackification,
with `𝒮' = 𝒮`, `G = 𝟭 𝒮`, `hmor` holding because the map of presheaves is then the identity and
`hobj` with the maximal sieve; and Stacks 02ZN produces them for an arbitrary category fibred in
groupoids, at which point `𝒮'` is genuinely not `𝒮`.

The object universes and the base hom universe are independent. The two total categories
share a hom universe, as required by
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`: its source and target are presheaves
valued in the hom universes of `𝒮` and of `𝒮'` respectively. No `UnivLE` hypothesis occurs.

## References

* [Stacks 02ZP](https://stacks.math.columbia.edu/tag/02ZP).
-/

@[expose] public section

universe vb

namespace CategoryTheory

open Opposite

namespace Functor

/-! ### Invertibility of a morphism of a fibre is local on the base -/

section Gluing

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- **The base changes of a morphism of a fibre form a compatible family.** Base changing
`m : x ⟶ y` along `b = γ ≫ f` is base changing it along `f` and then along `γ`, conjugated by the
canonical contractions of the iterated chosen pullbacks.

This is the compatibility hypothesis of `CategoryTheory.Functor.exists_fiberHom_of_locally` and of
`CategoryTheory.Functor.exists_fiberIso_of_locally`, and it is read off the presheaf `Mor(x, y)`:
the family is the family of restrictions of a single section, by
`CategoryTheory.Functor.morRestrict_morSection`, and the restriction maps are the conjugated base
changes, by `CategoryTheory.Functor.morRestrict_eq_pullbackFiberHom`. -/
lemma pullbackFiberHom_eq_conj (x y : p.Fiber U) (m : x ⟶ y) {V W : 𝒮} (f : V ⟶ U) (γ : W ⟶ V)
    (b : W ⟶ U) (hb : γ ≫ f = b) :
    pullbackFiberHom m b = (pullbackFiberCompIso' x f γ b hb).inv ≫
      pullbackFiberHom (pullbackFiberHom m f) γ ≫ (pullbackFiberCompIso' y f γ b hb).hom := by
  have hw : γ ≫ (Over.mk f : Over U).hom = (Over.mk b : Over U).hom := by simpa using hb
  have hcomp : (Over.homMk γ hw : (Over.mk b : Over U) ⟶ Over.mk f) ≫ overArrow (U := U) f =
      overArrow (U := U) b := by
    ext
    simpa [overArrow] using hb
  rw [← morRestrict_morSection p x y m b, ← hcomp, morRestrict_comp,
    morRestrict_morSection p x y m f,
    morRestrict_eq_pullbackFiberHom p x y (Over.homMk γ hw : (Over.mk b : Over U) ⟶ Over.mk f)]
  rfl

/-- **Invertibility of a morphism of a fibre is local on the base.** Let `p` be a fibred category
over a site `(𝒮, J)` whose presheaves `Mor(·, ·)` over `U` are sheaves — condition (2) of
Stacks 026F, which a stack satisfies. A morphism `m : x ⟶ y` of the fibre over `U` whose base
changes along the members of a covering sieve of `U` are invertible is itself invertible.

The inverses of the base changes form a compatible family, by
`CategoryTheory.Functor.pullbackFiberHom_eq_conj`, so they glue to an isomorphism `x ≅ y`
(`CategoryTheory.Functor.exists_fiberIso_of_locally`) whose base changes are those of `m`;
separatedness then identifies it with `m`. -/
theorem isIso_of_locally_isIso {J : GrothendieckTopology 𝒮} {x y : p.Fiber U}
    (hmor : ∀ (a b : p.Fiber U), IsMorSheaf p J U a b) (m : x ⟶ y) {R : Sieve U} (hR : R ∈ J U)
    (hloc : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U), R.arrows f → IsIso (pullbackFiberHom m f)) :
    IsIso m := by
  obtain ⟨e, he⟩ := exists_fiberIso_of_locally p hmor hR
    (fun {_V} f hf => have := hloc f hf; asIso (pullbackFiberHom m f))
    (fun {_V _W} f _hf γ b hb _hb' => pullbackFiberHom_eq_conj p x y m f γ b hb)
  rw [← eq_of_pullbackFiberHom_locally_eq p (hmor x y) hR (fun {_V} f hf => he f hf)]
  infer_instance

end Gluing

namespace Stackification

/-! ### Stacks 02ZP -/

section Groupoid

universe v u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {J : GrothendieckTopology 𝒞} {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}
  (hp : p.IsFiberedInGroupoids) (hsp' : p'.IsStack J) (hG : p.IsFibredOneMorphism p' G)
  (hmor : haveI : p.IsFibered := hp.isFibered
    haveI : p'.IsFibered := hsp'.isFibered
    ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
  (hobj : haveI : p'.IsFibered := hsp'.isFibered
    ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f))

include hp hsp' hG hmor in
/-- **A morphism between the images of two objects of a fibre of `𝒮` is locally invertible.** By
local surjectivity of the map of morphism presheaves — clause (1) of Stacks 02ZN — such a morphism
is, along a covering sieve of the base, the image under `G` of a morphism between the chosen
pullbacks of the two objects; that morphism is invertible because the fibres of `𝒮` are groupoids
(Stacks 003V), and `G` carries it to an invertible morphism. -/
lemma exists_locally_isIso {V : 𝒞} (a b : p.Fiber V)
    (μ : (fiberFunctorOfCompEq hG.comp_eq V).obj a ⟶
      (fiberFunctorOfCompEq hG.comp_eq V).obj b) :
    haveI : p'.IsFibered := hsp'.isFibered
    ∃ S ∈ J V, ∀ ⦃W : 𝒞⦄ (c : W ⟶ V), S.arrows c → IsIso (pullbackFiberHom μ c) := by
  have : p.IsFibered := hp.isFibered
  have : p'.IsFibered := hsp'.isFibered
  have := (hmor V a b).2
  set σ := morSection p' ((fiberFunctorOfCompEq hG.comp_eq V).obj a)
    ((fiberFunctorOfCompEq hG.comp_eq V).obj b) μ with hσ
  have hSmem : Presheaf.imageSieve (hG.morPresheafMap a b) σ ∈ (J.over V) (Over.mk (𝟙 V)) :=
    Presheaf.imageSieve_mem (J.over V) (hG.morPresheafMap a b) σ
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) (Presheaf.imageSieve (hG.morPresheafMap a b) σ),
    (J.mem_over_iff _).1 hSmem, ?_⟩
  intro W c hc
  obtain ⟨n, hn⟩ := mem_of_overEquiv hc
  have hn' : (hG.morPresheafMap a b).app (op (Over.mk c))
      (n : (morPresheaf p a b).obj (op (Over.mk c))) =
      morRestrict p' ((fiberFunctorOfCompEq hG.comp_eq V).obj a)
        ((fiberFunctorOfCompEq hG.comp_eq V).obj b) (overArrow (U := V) c) σ := hn
  rw [IsFibredOneMorphism.morPresheafMap_app, hσ, morRestrict_morSection] at hn'
  have : IsIso n := (hp.fiber_isGroupoid _).all_isIso n
  rw [← hn']
  infer_instance

include hp hsp' hG hmor hobj in
/-- **Every fibre of `𝒮'` is a groupoid.** A morphism of the fibre over `U` restricts, along a
covering sieve given by clause (2) of Stacks 02ZN, to a morphism between objects in the image of
`G`; those are locally invertible by
`CategoryTheory.Functor.Stackification.exists_locally_isIso`, hence invertible because `𝒮'` is a
stack (`CategoryTheory.Functor.isIso_of_locally_isIso`), and the same gluing over `U` makes the
original morphism invertible. -/
lemma isGroupoid_fiber (U : 𝒞) :
    haveI : p'.IsFibered := hsp'.isFibered
    IsGroupoid (p'.Fiber U) := by
  have : p.IsFibered := hp.isFibered
  have : p'.IsFibered := hsp'.isFibered
  refine ⟨@fun x' y' m => ?_⟩
  obtain ⟨R₁, hR₁, h₁⟩ := hobj U x'
  obtain ⟨R₂, hR₂, h₂⟩ := hobj U y'
  refine isIso_of_locally_isIso p' (hsp'.isMorSheaf U) m
    (J.intersection_covering hR₁ hR₂) fun V f hf => ?_
  obtain ⟨a, ⟨α⟩⟩ := h₁ hf.1
  obtain ⟨b, ⟨β⟩⟩ := h₂ hf.2
  obtain ⟨S, hS, hSiso⟩ :=
    exists_locally_isIso hp hsp' hG hmor a b (α.hom ≫ pullbackFiberHom m f ≫ β.inv)
  have : IsIso (α.hom ≫ pullbackFiberHom m f ≫ β.inv) :=
    isIso_of_locally_isIso p' (hsp'.isMorSheaf V) _ hS hSiso
  have hfac : pullbackFiberHom m f = α.inv ≫ (α.hom ≫ pullbackFiberHom m f ≫ β.inv) ≫ β.hom := by
    simp
  rw [hfac]
  infer_instance

include hp hsp' hG hmor hobj in
/-- **Stacks 02ZP.** Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids and
let `G : 𝒮 ⥤ 𝒮'` exhibit the stack `p' : 𝒮' ⥤ 𝒞` as the stackification of the fibred category
underlying `𝒮` — that is, let `G` be a 1-morphism of fibred categories over `𝒞` satisfying the two
clauses of Stacks 02ZN. Then `p'` is fibred in groupoids.

This is the whole content of Stacks 02ZP over Stacks 02ZN: the source runs the same construction
and observes that it lands in groupoid fibres. The statement is conditional on being given the
stackification, the construction of Stacks 02ZN not being assembled in the tree yet; once it is,
it supplies `hsp'`, `hG`, `hmor` and `hobj`.

By Stacks 003V it suffices that every fibre of `𝒮'` be a groupoid, which is
`CategoryTheory.Functor.Stackification.isGroupoid_fiber`. -/
@[stacks 02ZP]
theorem isFiberedInGroupoids_of_isStackification : p'.IsFiberedInGroupoids :=
  have : p'.IsFibered := hsp'.isFibered
  IsFiberedInGroupoids.mk' (isGroupoid_fiber hp hsp' hG hmor hobj)

include hp hsp' hG hmor hobj in
/-- **Stacks 02ZP, as the source states it: `𝒮'` is a stack in groupoids.** The `IsStack` half is
the hypothesis `hsp'` and the `IsFiberedInGroupoids` half is
`CategoryTheory.Functor.Stackification.isFiberedInGroupoids_of_isStackification`; together with
`hmor` and `hobj`, which are the two clauses of the source's statement carried unchanged from
hypothesis to conclusion, this says that the given `G` exhibits `𝒮'` as the stackification of `𝒮`
*in groupoids*. -/
@[stacks 02ZP]
theorem isStackInGroupoids_of_isStackification :
    p'.IsFiberedInGroupoids ∧ p'.IsStack J :=
  ⟨isFiberedInGroupoids_of_isStackification hp hsp' hG hmor hobj, hsp'⟩

end Groupoid

end Stackification

end Functor

end CategoryTheory
