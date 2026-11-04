module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ShortExact
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCechCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedFactorizations
public import StacksFrontier.CategoryTheory.Sites.VanishingOfDerivedSections

/-!
# Parasitic modules and the smooth objects (Stacks 07AR, part (1))

Let `𝒳` be an algebraic stack and let `F` be an `𝒪_𝒳`-module on `𝒳_étale`. **Stacks 07AR**
part (1) says that if `F` has the flat base change property of **Stacks 0762** then `F` is
parasitic (**Stacks 0773**) exactly when its restriction to the lisse-étale site vanishes, that
is exactly when its modules of sections vanish at every *smooth* object of `𝒳`.

Both directions are read at the sections:

* a smooth object is flat, so a parasitic module vanishes at it;
* conversely, a module vanishing at the smooth objects vanishes at an object `z` as soon as `z`
  is covered, in the étale topology, by one arrow out of an object lying over a *flat* morphism
  of schemes above a smooth object — the flat base change property then identifies the
  restriction of `F` below that object with the pullback of a vanishing restriction.

The geometric input of the second direction is
`AlgebraicGeometry.Stack.exists_covering_flat_arrow_of_flatObject`: every *flat* object of an
algebraic stack admits such a covering arrow.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.smoothObject_smallEtaleToStack_obj`: an object of `𝒳`
  named by the small étale site of the scheme below a smooth object is itself smooth.
* `AlgebraicGeometry.Stack.LisseEtale.isZero_restrictModuleToSmallEtale_of_smoothObject`: the
  restriction of such a module to the small étale site of the scheme below a smooth object is
  the zero module.
* `AlgebraicGeometry.Stack.LisseEtale.isZero_restrictModuleToSmallEtale_of_flat_arrow`: the flat
  base change property carries that vanishing along an arrow lying over a flat morphism.
* `AlgebraicGeometry.Stack.LisseEtale.subsingleton_of_isZero_restrictModuleToSmallEtale`: the
  sections at an object are the global sections of the restriction below it.
* `AlgebraicGeometry.Stack.LisseEtale.subsingleton_of_covering_flat_arrow`: the substantial half
  of part (1), from the geometric input.
* `AlgebraicGeometry.Stack.LisseEtale.subsingleton_of_isParasitic`: the easy direction.
* `AlgebraicGeometry.Stack.flatObject_schemeStack_iff`: an object of the algebraic stack of a
  scheme is flat exactly when the morphism of schemes under it is flat.
* `AlgebraicGeometry.Stack.exists_covering_flat_arrow_of_flatObject`: the geometric input — a
  flat object is covered by one arrow out of an object flat over a smooth object.
* `AlgebraicGeometry.Stack.LisseEtale.isParasitic_of_subsingleton_smoothObject`: part (1),
  (b) implies (a), at the sections.

## Implementation notes

The Stacks project proves the second direction by faithful flatness of the pullback on the small
étale sites. Here it uses only the primed 2-fibre product of **Stacks 07AK** — whose atlas has its
`𝒳`-component flat over the scheme of a smooth atlas — together with the étale refinement of a
smooth surjective morphism (**Stacks 055V**).

## References

* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w m

namespace AlgebraicGeometry.Stack

/-- A morphism of schemes over a base which is isomorphic, over that base, to an étale one is
smooth.  Composing with the isomorphism exhibits it as an isomorphism followed by an étale
morphism. -/
theorem smooth_of_iso_of_etale (B : BigFppfSite.{u}) {Y : B.Schemes} {W Z : Over Y}
    (e : W ≅ Z) (hZ : Etale (B.inclusion.map Z.hom)) :
    Smooth (B.inclusion.map W.hom) := by
  have h1 : Over.Hom.left e.hom ≫ Z.hom = W.hom := Over.w e.hom
  have hiso : IsIso (Over.Hom.left e.hom) := by
    have := (Over.forget Y).map_isIso e.hom
    simpa using this
  have hsm : Smooth (B.inclusion.map (Over.Hom.left e.hom) ≫ B.inclusion.map Z.hom) :=
    inferInstance
  exact h1 ▸ (B.inclusion.map_comp (Over.Hom.left e.hom) Z.hom ▸ hsm)

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The geometric input: a covering arrow out of an object flat over a smooth object -/

/-- **A morphism of the big fppf category of `S` is a flat morphism of algebraic spaces exactly
when the morphism of schemes underneath it is flat.**  This is the flat case of **Stacks 03MJ**
for a morphism of representable presheaves, the smooth case being
`AlgebraicGeometry.Space.isSmooth_yoneda_map_iff`. -/
theorem isFlat_yoneda_map_iff {U V : BigFppfOver B S hS} (j : U ⟶ V) :
    Space.IsFlat B S hS (yoneda.map j) ↔ Flat ((BigFppfOver.toScheme B S hS).map j) :=
  Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget j

/-- **Stacks 0787.** An object of the algebraic stack of a scheme `U` over `S` — a scheme `x`
over `U` in the big fppf category — is a *flat object* exactly when the morphism of schemes
underlying its structure morphism is flat.

This is the flat sibling of `AlgebraicGeometry.Stack.smoothObject_schemeStack_iff`, proved the
same way: **Stacks 06FM** for representable source and target identifies flatness of the
1-morphism the object names with flatness of `yoneda.map x.hom`. -/
theorem flatObject_schemeStack_iff (U : BigFppfOver B S hS) (x : Over U) :
    flatObject B S hS (schemeStack.{u, w} B S hS U).val x ↔
      Flat ((BigFppfOver.toScheme B S hS).map x.hom) := by
  have heq := representingMap_eq_yoneda_map_baseMap B S hS
    (Functor.TwoYoneda.liftBased (Over.forget U)
      (Functor.IsFiberedInGroupoids.over_forget U) x.left (Functor.Fiber.mk (a := x) rfl))
  rw [baseMapOfBasedFunctor_liftBased] at heq
  have key := hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ k => Space.IsFlat B S hS k)
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    (schemeStack.{u, w} B S hS x.left).property
    (schemeStack.{u, w} B S hS U).property
    (yoneda.obj x.left) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS x.left) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver x.left)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (objectMorphism B S hS (schemeFibredCategory B S hS U)
      (Functor.Fiber.mk (a := x) rfl))
  exact key.trans ((Iff.of_eq (congrArg (fun k => Space.IsFlat B S hS k) heq)).trans
    (isFlat_yoneda_map_iff B S hS x.hom))

/-- **The component of a 2-isomorphism of 1-morphisms of categories fibred in groupoids at an
object.**  A 2-morphism is a morphism of the underlying functors, so a 2-isomorphism has an
isomorphism for each of its components. -/
def homFunctorIsoApp
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F G : 𝒜 ⟶ ℬ} (e : F ≅ G) (x : 𝒜.val.obj) :
    (CatFiberedInGroupoids.homFunctor F).obj x ≅
      (CatFiberedInGroupoids.homFunctor G).obj x where
  hom := e.hom.hom.toNatTrans.app x
  inv := e.inv.hom.toNatTrans.app x
  hom_inv_id := congrArg (fun t : F ⟶ F => t.hom.toNatTrans.app x) e.hom_inv_id
  inv_hom_id := congrArg (fun t : G ⟶ G => t.hom.toNatTrans.app x) e.inv_hom_id

section AmbientSquare

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The first projection of the 2-fibre product `V ×_{y, 𝒴} 𝒳` is smooth when `f` is.**  It is
the base change of `f` along the 1-morphism `V ⟶ 𝒴` named by `y`, so this is **Stacks 075W**.
The sibling statement for the second projection is
`AlgebraicGeometry.Stack.LisseEtale.isSmooth_ambientSquare_snd`, which instead uses smoothness of
the object `y`. -/
theorem isSmooth_ambientSquare_fst (y : FlatFppf B S hS 𝒴)
    (hf : AlgebraicStacks.IsSmooth B S hS f) :
    AlgebraicStacks.IsSmooth B S hS (ambientSquare B S hS f y).fst :=
  AlgebraicStacks.isSmooth_baseChange B S hS f (ambientSliceMorphism B S hS y)
    (ambientSquare B S hS f y)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (ambientSliceMorphism B S hS y) f) hf

/-- **The first projection of the 2-fibre product `V ×_{y, 𝒴} 𝒳` is surjective when `f` is**,
being its base change along the 1-morphism `V ⟶ 𝒴` named by `y`. -/
theorem isSurjective_ambientSquare_fst (y : FlatFppf B S hS 𝒴)
    (hf : IsSurjective B S hS f) :
    IsSurjective B S hS (ambientSquare B S hS f y).fst :=
  isSurjective_of_isTwoFibreProduct B S hS (ambientSquare B S hS f y).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (ambientSliceMorphism B S hS y) f)) hf

end AmbientSquare

/-- **The arrow to `y` out of the `𝒳`-component of an object of the 2-fibre product
`V ×_{y, 𝒴} 𝒳` lies over the structure morphism of its `V`-component.**  That arrow is the
comparison isomorphism of the object, which is vertical, followed by the chosen cartesian lift of
`y`, which lies over the structure morphism. -/
theorem isHomLift_ambientArrow {𝒞 : Type (u + 1)} [Category.{u} 𝒞]
    {A C : Type (u + 1)} [Category.{u} A] [Category.{u} C]
    (p𝒳 : A ⥤ 𝒞) (p𝒴 : C ⥤ 𝒞) (F : A ⥤ C) (c : p𝒴.ChoiceOfPullbacks)
    {Q : ObjectProperty C} (y : Q.FullSubcategory)
    (d : SubsitePushforward.ambientTwoFibreProduct p𝒳 p𝒴 F c y) :
    p𝒴.IsHomLift d.x.hom
      (d.iso.inv ≫ c.map d.x.hom (Functor.Fiber.mk (a := y.obj) rfl)) := by
  obtain ⟨base, dx, dy, hx, hy, iso, vert⟩ := d
  subst hx
  change p𝒴.IsHomLift dx.hom (iso.inv ≫ c.map dx.hom (Functor.Fiber.mk (a := y.obj) rfl))
  have := vert
  have : p𝒴.IsHomLift (𝟙 ((Over.forget (p𝒴.obj y.obj)).obj dx)) iso.inv := inferInstance
  have h2 : p𝒴.IsHomLift dx.hom (c.map dx.hom (Functor.Fiber.mk (a := y.obj) rfl)) :=
    (c.isStronglyCartesian dx.hom (Functor.Fiber.mk (a := y.obj) rfl)).toIsHomLift
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ p𝒴 _ _ _
    ((Over.forget (p𝒴.obj y.obj)).obj dx) iso.inv inferInstance _ _ dx.hom
    (c.map dx.hom (Functor.Fiber.mk (a := y.obj) rfl)) h2

/-- **A flat object is covered by one arrow out of an object flat over a given atlas.**  For a
smooth surjective atlas `a : U ⟶ 𝒳`, a flat object `z` of `𝒳` is covered, in the étale topology,
by a single arrow `α : t ⟶ z` out of an object `t` carrying an arrow `ψ` to the object `a(𝟙_U)`
named by the atlas, lying over a *flat* morphism of schemes.  This is the proof of
`AlgebraicGeometry.Stack.exists_covering_flat_arrow_of_flatObject` run at the given atlas. -/
theorem exists_covering_flat_arrow_atlas_of_flatObject (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {U : BigFppfOver B S hS} (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a) (hasurj : IsSurjective B S hS a)
    {z : 𝒳.val.val.obj} (hz : flatObject B S hS 𝒳.val z) :
    ∃ (t : 𝒳.val.val.obj) (α : t ⟶ z)
      (ψ : t ⟶ (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U))),
      Flat (B.inclusion.map (𝒳.val.val.p.map ψ).left) ∧
      Sieve.generate (Presieve.singleton α) ∈
        associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) z := by
  let y : FlatFppf B S hS 𝒳 := ⟨z, hz⟩
  obtain ⟨U₀, a₀, h0sm, h0surj, hP⟩ := FlatFppf.exists_primed_atlas.{u, w} B S hS a y
  let d := (CatFiberedInGroupoids.homFunctor a₀.hom).obj (Over.mk (𝟙 U₀))
  have hgsm : AlgebraicStacks.IsSmooth B S hS (a₀ ≫ (ambientSquare.{u, w} B S hS a y).fst) :=
    AlgebraicStacks.isSmooth_comp.{u, w} B S hS a₀ _ h0sm
      (isSmooth_ambientSquare_fst.{u, w} B S hS a y hasm)
  have hgsurj : IsSurjective B S hS (a₀ ≫ (ambientSquare.{u, w} B S hS a y).fst) :=
    isSurjective_comp.{u, w} B S hS a₀ _ h0surj
      (isSurjective_ambientSquare_fst.{u, w} B S hS a y hasurj)
  obtain ⟨q, hqsm, hqsurj, ⟨e⟩⟩ := exists_schemeMap_of_isSurjective_isSmooth.{u, w} B S hS
    (a₀ ≫ (ambientSquare.{u, w} B S hS a y).fst) hgsurj hgsm
  have j : d.x ≅ (Over.map q).obj (Over.mk (𝟙 U₀)) :=
    homFunctorIsoApp B S hS e (Over.mk (𝟙 U₀))
  have hqsm' : Smooth (B.inclusion.map q.left) := hqsm
  have hqsurj' : Surjective (B.inclusion.map q.left) := hqsurj
  refine ⟨(CatFiberedInGroupoids.homFunctor a.hom).obj d.y,
    d.iso.inv ≫ (ambientChoiceOfPullbacks.{u, w} B S hS 𝒳).map d.x.hom
      (Functor.Fiber.mk (a := y.obj) rfl),
    (CatFiberedInGroupoids.homFunctor a.hom).map
      (Over.homMk d.y.hom (Category.comp_id _) : d.y ⟶ Over.mk (𝟙 U)), ?_, ?_⟩
  · have hfl : Flat ((BigFppfOver.toScheme B S hS).map d.y.hom) :=
      (flatObject_schemeStack_iff.{u, w} B S hS U d.y).1 hP
    have hl0 := isHomLift_map_toUnit.{u, w} (a := a) d.y
    have hl := IsHomLift.fac' 𝒳.val.val.p d.y.hom
      ((CatFiberedInGroupoids.homFunctor a.hom).map
        (Over.homMk d.y.hom (Category.comp_id _) : d.y ⟶ Over.mk (𝟙 U)))
    change Flat ((BigFppfOver.toScheme B S hS).map _)
    rw [hl]
    simp only [Functor.map_comp]
    infer_instance
  · have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    refine Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒳.val.val.p
      (BigFppfOver.baseOverTopology B S hS .etale) _
      (𝒳.val.isFiberedInGroupoids.isStronglyCartesian _) d.x.hom
      (isHomLift_ambientArrow _ 𝒳.val.val.p _ (ambientChoiceOfPullbacks.{u, w} B S hS 𝒳) y d)
      (generate_singleton_mem_baseOverTopology_etale B S hS q.left hqsm' hqsurj') ?_
    rintro W u ⟨Z, g, k, ⟨⟩, rfl⟩
    refine ⟨g ≫ Over.homMk (𝟙 U₀.left) (Over.w q).symm ≫ Over.Hom.left j.inv, ?_⟩
    rw [Category.assoc, Category.assoc, Over.w j.inv]
    congr 1

/-- **The geometric input of Stacks 07AR part (1), (b) implies (a).**  A flat object `z` of an
algebraic stack `𝒳` is covered, in the étale topology, by a single arrow `α : t ⟶ z` out of an
object `t` carrying an arrow `ψ` to a *smooth* object over a *flat* morphism of schemes.

Let `a : U ⟶ 𝒳` be a smooth surjective atlas.  The 2-fibre product `V ×_{z, 𝒳} U` has a smooth
surjective atlas `U₀` whose distinguished object `d` is *primed* (**Stacks 07AK** (2),
`AlgebraicGeometry.Stack.FlatFppf.exists_primed_atlas`): its `U`-component `d.y` is a flat object
of `(Sch/U)`, that is, lies over a flat morphism of schemes `d.y.hom`.  Take `t = a(d.y)`,
`s = a(𝟙_U)` and `ψ = a(d.y ⟶ 𝟙_U)`; then `ψ` lies over `d.y.hom`.  The arrow `α` is the
comparison isomorphism of `d` followed by the chosen cartesian lift of `z`, so it lies over the
structure morphism of the `V`-component `d.x`; and `d.x` is, by **Stacks 04SW**, the object of
`(Sch/V)` named by a smooth surjective morphism of schemes `q : U₀ ⟶ V`, whose one-member family
generates a covering sieve of the étale topology (**Stacks 055V**).  Since every morphism of a
category fibred in groupoids is strongly cartesian, that covering sieve lifts to the singleton of
`α`. -/
theorem exists_covering_flat_arrow_of_flatObject (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {z : 𝒳.val.val.obj} (hz : flatObject B S hS 𝒳.val z) :
    ∃ (t s : 𝒳.val.val.obj) (α : t ⟶ z) (ψ : t ⟶ s),
      smoothObject.{u, w} B S hS 𝒳 s ∧
      Flat (B.inclusion.map (𝒳.val.val.p.map ψ).left) ∧
      Sieve.generate (Presieve.singleton α) ∈
        associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) z := by
  obtain ⟨U, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨t, α, ψ, hψ, hα⟩ :=
    exists_covering_flat_arrow_atlas_of_flatObject B S hS 𝒳 a hasm hasurj hz
  exact ⟨t, _, α, ψ, smoothObject_atlas_obj.{u, w} B S hS a hasm, hψ, hα⟩

/-- **A sheaf vanishing at the source of a covering arrow has no sections at its target.** -/
theorem subsingleton_of_isZero_of_covering_arrow {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hsheaf : Presheaf.IsSheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    {z t : 𝒳.val.val.obj} (α : t ⟶ z) (ht : Subsingleton (F.obj (op t)))
    (hα : Sieve.generate (Presieve.singleton α) ∈
      associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) z) :
    Subsingleton (F.obj (op z)) := by
  have hzt' : IsZero (F.presheaf.obj (op t)) := @AddCommGrpCat.isZero_of_subsingleton _ ht
  have hsep : Presieve.IsSeparatedFor
      (F.presheaf ⋙ coyoneda.obj (op (F.presheaf.obj (op z)))) (Presieve.singleton α) := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact (hsheaf _ _ hα).isSeparatedFor
  have hid : 𝟙 (F.presheaf.obj (op z)) =
      (0 : F.presheaf.obj (op z) ⟶ F.presheaf.obj (op z)) := by
    refine hsep.ext fun {Y} {f} hf => ?_
    cases hf
    change (𝟙 (F.presheaf.obj (op z))) ≫ F.presheaf.map α.op
        = (0 : F.presheaf.obj (op z) ⟶ F.presheaf.obj (op z)) ≫ F.presheaf.map α.op
    rw [hzt'.eq_zero_of_tgt (F.presheaf.map α.op), comp_zero, comp_zero]
  exact AddCommGrpCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero _).2 hid)

namespace LisseEtale

/-- **An object of `𝒳` named by the small étale site of the scheme below a smooth object is
smooth.**  Such an object comes with a morphism to `x` lying over an étale — in particular
smooth — morphism of schemes, so
`AlgebraicGeometry.Stack.LisseEtale.smoothObject_of_smooth` applies.

This is the smooth sibling of `AlgebraicGeometry.Stack.flatObject_smallEtaleToStack_obj`, and it
is what makes the restriction to `U_étale` of a module see only smooth objects. -/
theorem smoothObject_smallEtaleToStack_obj {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (x : 𝒳.val.val.obj) (hx : smoothObject.{u, w} B S hS 𝒳 x)
    (V : SmallEtale E (𝒳.val.val.p.obj x).left.1
      (contains_base B E h S hS 𝒳.val.val.p x)) :
    smoothObject.{u, w} B S hS 𝒳
      ((smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x).obj V) := by
  have := isEquivalence_overPost B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
  exact smoothObject_of_smooth.{u, w} B S hS 𝒳
    ((Over.post (X := x) (𝒳.val.val.p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B E h (𝒳.val.val.p.obj x).left.1
        (contains_base B E h S hS 𝒳.val.val.p x)).obj V)).hom
    (smooth_of_iso_of_etale B
      ((Over.post (X := x) (𝒳.val.val.p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app
        ((smallEtaleInclusion B E h (𝒳.val.val.p.obj x).left.1
          (contains_base B E h S hS 𝒳.val.val.p x)).obj V))
      (smallEtaleInclusion_etale B E h _ _ V))
    hx

/-- **A module vanishing at the smooth objects restricts to zero on the small étale site of the
scheme below a smooth object.**  The restriction evaluates the module at the objects of `𝒳`
named by that site, and every one of them is a smooth object by
`AlgebraicGeometry.Stack.LisseEtale.smoothObject_smallEtaleToStack_obj`. -/
theorem isZero_restrictModuleToSmallEtale_of_smoothObject
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : ∀ y : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 y →
      Subsingleton (F.obj (op y)))
    (x : 𝒳.val.val.obj) (hx : smoothObject.{u, w} B S hS 𝒳 x) :
    IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
      (etaleTopology B) (etaleTopology_le_topology B) F) := by
  rw [PresheafOfModules.isZero_iff_forall_isZero_obj]
  intro V
  exact @ModuleCat.isZero_of_subsingleton _ _ _
    (hF ((smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x).obj V.unop)
      (smoothObject_smallEtaleToStack_obj B E h S hS x hx V.unop))

/-- **The flat base change property moves the vanishing of a restriction down a flat arrow.**
If the restriction of `F` to the small étale site below `y` is zero and `φ : x ⟶ y` lies over a
flat morphism of schemes, then the restriction below `x` is zero too: the comparison map `c_φ`
of **Stacks 06WC** is an isomorphism from a pullback of the vanishing restriction. -/
theorem isZero_restrictModuleToSmallEtale_of_flat_arrow
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F)
    {x y : 𝒳.val.val.obj} (φ : x ⟶ y)
    (hflat : Flat (B.inclusion.map (𝒳.val.val.p.map φ).left))
    (hy : IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids y (etaleTopology B) (etaleTopology_le_topology B) F)) :
    IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B) F) := by
  have hiso := hfbc φ hflat
  have : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids φ
        (etaleTopology B) (etaleTopology_le_topology B))).IsLeftAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids φ
        (etaleTopology B) (etaleTopology_le_topology B))).isLeftAdjoint
  have hzs : IsZero ((PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids φ
        (etaleTopology B) (etaleTopology_le_topology B))).obj
      (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids y
        (etaleTopology B) (etaleTopology_le_topology B) F)) :=
    Functor.map_isZero _ hy
  exact hzs.of_iso (asIso (restrictModulePullbackComparison B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids φ (etaleTopology B) (etaleTopology_le_topology B) F)).symm

/-- **Vanishing of a restriction gives vanishing of the sections at the object.**  The global
sections over the small étale site of the scheme below `x` of the restriction of `F` are the
sections of `F` at `x`, by `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso`. -/
theorem subsingleton_of_isZero_restrictModuleToSmallEtale
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (x : 𝒳.val.val.obj)
    (hx : IsZero (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids x (etaleTopology B) (etaleTopology_le_topology B) F)) :
    Subsingleton (F.obj (op x)) := by
  have : Subsingleton
      ((restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf.obj
        (op (smallEtaleFinal B E h S hS 𝒳.val.val.p x))) :=
    ModuleCat.subsingleton_of_isZero
      ((PresheafOfModules.isZero_iff_forall_isZero_obj _).1 hx
        (op (smallEtaleFinal B E h S hS 𝒳.val.val.p x)))
  exact (ConcreteCategory.bijective_of_isIso
    (restrictModuleToSmallEtaleFinalIso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
      (etaleTopology B) (etaleTopology_le_topology B) F).hom).surjective.subsingleton

/-- **The substantial half of Stacks 07AR part (1), from the geometric input.**  Let `F` be a
sheaf of `𝒪_𝒳`-modules on `𝒳_étale` with the flat base change property whose sections vanish at
every smooth object of `𝒳`.  If an object `z` is covered, in the étale topology, by a single
arrow out of an object `t` carrying an arrow to a smooth object over a *flat* morphism of
schemes, then the sections of `F` at `z` vanish.

The flat base change property makes the restriction of `F` below `t` vanish, hence its sections
at `t`; and a sheaf is separated for a covering sieve, so a section over `z` vanishing after
restriction along the covering arrow vanishes. -/
theorem subsingleton_of_covering_flat_arrow
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hsheaf : Presheaf.IsSheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F)
    (hF : ∀ y : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 y → Subsingleton (F.obj (op y)))
    {z t s : 𝒳.val.val.obj} (α : t ⟶ z) (ψ : t ⟶ s)
    (hs : smoothObject.{u, w} B S hS 𝒳 s)
    (hψ : Flat (B.inclusion.map (𝒳.val.val.p.map ψ).left))
    (hα : Sieve.generate (Presieve.singleton α) ∈
      associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) z) :
    Subsingleton (F.obj (op z)) := by
  have hzt : Subsingleton (F.obj (op t)) :=
    subsingleton_of_isZero_restrictModuleToSmallEtale B E h S hS F t
      (isZero_restrictModuleToSmallEtale_of_flat_arrow B E h S hS F hfbc ψ hψ
        (isZero_restrictModuleToSmallEtale_of_smoothObject B E h S hS F hF s hs))
  exact subsingleton_of_isZero_of_covering_arrow B S hS F hsheaf α hzt hα

/-- **The easy half of Stacks 07AR part (1).**  A parasitic module vanishes at every smooth
object, a smooth object being flat. -/
theorem subsingleton_of_isParasitic {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsParasitic.{u, w, u} B S hS 𝒳 .etale F)
    (x : 𝒳.val.val.obj) (hx : smoothObject.{u, w} B S hS 𝒳 x) :
    Subsingleton (F.obj (op x)) :=
  hF x (flatObject_of_smoothObject.{u, w} B S hS 𝒳 hx)

/-- **Stacks 07AR part (1), (b) implies (a), at the sections.**  A sheaf of `𝒪_𝒳`-modules on
`𝒳_étale` with the flat base change property whose sections vanish at every smooth object of `𝒳`
is parasitic.

Every flat object is covered by one arrow out of an object flat over a smooth object
(`AlgebraicGeometry.Stack.exists_covering_flat_arrow_of_flatObject`), and
`AlgebraicGeometry.Stack.LisseEtale.subsingleton_of_covering_flat_arrow` turns such a covering
into vanishing of the sections. -/
theorem isParasitic_of_subsingleton_smoothObject {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hsheaf : Presheaf.IsSheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F)
    (hF : ∀ y : 𝒳.val.val.obj, smoothObject.{u, w} B S hS 𝒳 y → Subsingleton (F.obj (op y))) :
    IsParasitic.{u, w, u} B S hS 𝒳 .etale F := by
  intro z hz
  obtain ⟨t, s, α, ψ, hs, hψ, hα⟩ :=
    exists_covering_flat_arrow_of_flatObject.{u, w} B S hS 𝒳 hz
  exact subsingleton_of_covering_flat_arrow B E h S hS F hsheaf hfbc hF α ψ hs hψ hα

end LisseEtale

end AlgebraicGeometry.Stack

end
