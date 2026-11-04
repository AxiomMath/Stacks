module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveSmoothEtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# Descent of quasi-coherence along a jointly surjective family (Stacks 07AZ)

Let `f j : 𝒵 j ⟶ 𝒳`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks over `S` whose
images cover the points of `𝒳`, that is `|𝒳| = ⋃ j, |f j|(|𝒵 j|)` for the points of
**Stacks 04XG**, and let `M` be a sheaf of `𝒪_𝒳`-modules.  **Stacks 07AZ** says that if every
inverse image `f j^{-1} M` is quasi-coherent, then so is `M` — in part (1) for a family of smooth
morphisms and a module on `𝒳_étale`, in part (2) for a family of flat and locally finitely
presented morphisms and a module on `𝒳_fppf`.

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the local-presentation condition of
**Stacks 03DL** (6), which for a category fibred in groupoids is the quasi-coherence of
**Stacks 06WG**; the inverse image is `AlgebraicGeometry.Stack.modulePullback`, the restriction of
**Stacks 06WE**.

Both parts are instances of one argument, `isQuasicoherentOnSite_of_familyFibreLift`.  Its two
ingredients are:

* at an object `z` of `𝒵 j`, the slice `𝒵 j/z ⥤ 𝒳/f j(z)` is an equivalence of ringed sites
  (**Stacks 06W0**) carrying the restriction of `M` to the restriction of `f j^{-1} M`, so a
  global presentation of the latter is one of the former — this is where quasi-coherence of the
  inverse images is consumed; and
* at an arbitrary object `x` of `𝒳`, joint surjectivity produces a covering of the scheme below
  `x` each member of which carries an object of some `𝒵 j` whose image maps to `x`.  Every arrow
  of a category fibred in groupoids is strongly cartesian, so each arrow of the resulting
  covering sieve of `x` factors through one of those images.

The locality is organised through `Stacks.SheafOfModules.presentedSieve M x`, the sieve of arrows
into `x` whose *source* carries a global presentation of `M`: it is a sieve because a global
presentation restricts, its pullback along any morphism is the corresponding sieve at the source,
and `M` is quasi-coherent exactly when it covers every object.  The local character of the
topology then does the combinatorics.

## Main definitions

* `Stacks.SheafOfModules.presentedSieve`: the sieve of arrows whose source carries a global
  presentation.
* `AlgebraicGeometry.Stack.familyModulePullback`: the inverse image along the `j`-th member of a
  family of 1-morphisms of algebraic stacks.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem`: a sheaf of modules is
  quasi-coherent as soon as `presentedSieve M x` covers every object `x`.
* `AlgebraicGeometry.Stack.hasGlobalPresentation_of_modulePullback`: a global presentation of the
  inverse image on the slice at `z` is one of `M` on the slice at `F z`.
* `AlgebraicGeometry.Stack.presentedSieve_image_mem`: if the inverse image along `F` is
  quasi-coherent then `presentedSieve M (F z)` covers `F z` for every object `z` of the source.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_familyFibreLift`: the common argument of the
  two parts of **Stacks 07AZ**, with the local liftability of objects as a hypothesis.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_isSmooth_jointlySurjective`: **Stacks 07AZ**,
  part (1).
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_isFlat_isLfp_jointlySurjective`:
  **Stacks 07AZ**, part (2).

## Implementation notes

The module sections live in the universe of the structure sheaf, which is what the invariance of
quasi-coherence under an equivalence of ringed sites
(`Stacks.SheafOfModules.hasGlobalPresentation_of_reindex`) requires; this is the universe in which
quasi-coherence on the site of an algebraic stack is available throughout the library, as in the
rendering of **Stacks 06WI**.

The topology is left as an arbitrary topology on the underlying category of schemes coarser than
the fppf one, so that the two parts differ only in which topology is taken and which local
lifting lemma supplies the covering: `exists_etaleCovering_family_fibre_lift` for the smooth
family and `exists_fppfCovering_family_fibre_lift` for the flat, locally finitely presented one.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 07AZ](https://stacks.math.columbia.edu/tag/07AZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.SheafOfModules

universe u v w t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The sieve on an object `x` of the site consisting of the arrows into `x` whose source
carries a global presentation of `M`.  Membership depends only on the source, and is downward
closed because a global presentation restricts along any morphism. -/
def presentedSieve (M : SheafOfModules.{t} R) (x : C) : Sieve x where
  arrows Y _ := (M.over Y).HasGlobalPresentation
  downward_closed hf g := hasGlobalPresentation_overMap M g hf

/-- The pullback of `presentedSieve M x` along any morphism `g : y ⟶ x` is `presentedSieve M y`:
membership in either sieve depends only on the source of the arrow. -/
theorem presentedSieve_pullback (M : SheafOfModules.{t} R) {x y : C} (g : y ⟶ x) :
    (presentedSieve M x).pullback g = presentedSieve M y := rfl

/-- If `presentedSieve M x` covers `x` and there is any morphism `y ⟶ x`, then
`presentedSieve M y` covers `y`. -/
theorem presentedSieve_mem_of_hom (M : SheafOfModules.{t} R) {x y : C} (g : y ⟶ x)
    (h : presentedSieve M x ∈ J x) : presentedSieve M y ∈ J y := by
  rw [← presentedSieve_pullback M g]
  exact J.pullback_stable g h

/-- **Quasi-coherence from the sieve of globally presented sources.**  A sheaf of modules is
quasi-coherent as soon as, for every object `x` of the site, the arrows into `x` whose source
carries a global presentation form a covering sieve. -/
theorem isQuasicoherentOnSite_of_presentedSieve_mem (M : SheafOfModules.{t} R)
    (h : ∀ x : C, presentedSieve M x ∈ J x) : M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation x := by
    refine ⟨Σ y : C, {g : y ⟶ x // (M.over y).HasGlobalPresentation},
      fun i => i.1, fun i => i.2.1, ?_, fun i => i.2.2⟩
    refine J.superset_covering (fun Y g hg => ?_) (h x)
    exact Sieve.ofArrows_mk _ _ (⟨Y, g, hg⟩ :
      Σ y : C, {g : y ⟶ x // (M.over y).HasGlobalPresentation})

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of categories fibred in groupoids over the big fppf category is continuous and
cocontinuous for the associated topologies. -/
private theorem isContinuous_and_isCocontinuous_associatedTopology
    {𝒵 : Type v} [Category.{w} 𝒵] {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒵 ⥤ 𝒳) (hF : F ⋙ q = p) (τ : GrothendieckTopology B.Schemes) :
    F.IsContinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) ∧
      F.IsCocontinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) :=
  have := hp.isFibered
  have := hq.isFibered
  (hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))

/-- **A global presentation of the inverse image descends to the image object.**  Let
`F : 𝒵 ⥤ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf category of
`S` and let `M` be a sheaf of modules on `𝒳`.  If the restriction of the inverse image `F^{-1}M`
to the slice at an object `z` has a global presentation, then so does the restriction of `M` to
the slice at `F z`.

The slice `𝒵/z ⥤ 𝒳/F z` of a 1-morphism is an equivalence of sites by Stacks 06W0, and the
inverse image restricted to `𝒵/z` *is* the reindexing of `M` restricted to `𝒳/F z` along it. -/
theorem hasGlobalPresentation_of_modulePullback
    {𝒵 : Type v} [Category.{w} 𝒵] {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒵 ⥤ 𝒳) (hF : F ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq τ hτ)) (z : 𝒵)
    (h : (((modulePullback B S hS p q hp hq F hF τ hτ).obj M).over z).HasGlobalPresentation) :
    (M.over (F.obj z)).HasGlobalPresentation := by
  obtain ⟨hcont, hcocont⟩ :=
    isContinuous_and_isCocontinuous_associatedTopology B S hS p q hp hq F hF τ
  subst hF
  have hsl : (Over.post (X := z) F).IsEquivalence := by
    have h1 : (Over.post (X := F.obj z) (q ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS q hq (F.obj z)
    have h3 : (Over.post (X := z) F ⋙
        Over.post (q ⋙ Over.forget (B.obj hS))).IsEquivalence := by
      rw [← Over.post_comp]
      exact isEquivalence_overPost B S hS (F ⋙ q) hp z
    exact Functor.isEquivalence_of_comp_right (Over.post (X := z) F)
      (Over.post (q ⋙ Over.forget (B.obj hS)))
  let e : Over z ≌ Over (F.obj z) := (Over.post (X := z) F).asEquivalence
  have hec : e.functor.IsContinuous ((associatedTopology B S hS (F ⋙ q) τ).over z)
      ((associatedTopology B S hS q τ).over (F.obj z)) :=
    Functor.isContinuous_overPost _ _ F z
  have hecc : e.functor.IsCocontinuous ((associatedTopology B S hS (F ⋙ q) τ).over z)
      ((associatedTopology B S hS q τ).over (F.obj z)) :=
    inferInstanceAs ((Over.post (X := z) F).IsCocontinuous
      ((associatedTopology B S hS (F ⋙ q) τ).over z)
      ((associatedTopology B S hS q τ).over (F.obj z)))
  have hei : e.inverse.IsContinuous ((associatedTopology B S hS q τ).over (F.obj z))
      ((associatedTopology B S hS (F ⋙ q) τ).over z) :=
    e.toAdjunction.isContinuous_of_isCocontinuous _ _
  exact Stacks.SheafOfModules.hasGlobalPresentation_of_reindex
    (J := (associatedTopology B S hS q τ).over (F.obj z))
    (J' := (associatedTopology B S hS (F ⋙ q) τ).over z) e
    ((ringStructureSheafCore B S hS q hq τ hτ).over (F.obj z)) (M.over (F.obj z)) h

/-- **Quasi-coherence of the inverse image covers every image object.**  If the inverse image
`F^{-1}M` of a sheaf of modules along a 1-morphism `F : 𝒵 ⥤ 𝒳` of categories fibred in groupoids
is quasi-coherent, then for every object `z` of `𝒵` the arrows into `F z` whose source carries a
global presentation of `M` form a covering sieve of `F z`.

Quasi-coherence of `F^{-1}M` supplies a covering of `z` on whose members `F^{-1}M` is globally
presented; its image under `F` covers `F z`, because `F` is continuous for the two inherited
topologies, and the restrictions of `M` at the image objects are globally presented by
`AlgebraicGeometry.Stack.hasGlobalPresentation_of_modulePullback`. -/
theorem presentedSieve_image_mem
    {𝒵 : Type v} [Category.{w} 𝒵] {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒵 ⥤ 𝒳) (hF : F ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq τ hτ))
    (hN : ((modulePullback B S hS p q hp hq F hF τ hτ).obj M).IsQuasicoherentOnSite)
    (z : 𝒵) :
    Stacks.SheafOfModules.presentedSieve M (F.obj z) ∈
      associatedTopology B S hS q τ (F.obj z) := by
  have hcont := (isContinuous_and_isCocontinuous_associatedTopology B S hS p q hp hq F hF τ).1
  obtain ⟨I, V, β, hcov, hpres⟩ := hN.locally_hasGlobalPresentation z
  refine (associatedTopology B S hS q τ).superset_covering ?_
    ((CoverPreserving.of_isContinuous F (associatedTopology B S hS p τ)
      (associatedTopology B S hS q τ)).cover_preserve hcov)
  rintro Z u ⟨A, c, g, hc, rfl⟩
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hc
  exact Stacks.SheafOfModules.hasGlobalPresentation_overMap M (g ≫ F.map b)
    (hasGlobalPresentation_of_modulePullback B S hS p q hp hq F hF τ hτ M (V i) (hpres i))

/-- A morphism of the total category of a category fibred in groupoids whose image factors
through the image of a lift factors through that lift: every lift of a base morphism is strongly
cartesian over it. -/
private theorem nonempty_hom_of_isHomLift {𝒮 : Type*} [Category 𝒮] {𝒞 : Type*} [Category 𝒞]
    (pp : 𝒮 ⥤ 𝒞) (hpp : pp.IsFiberedInGroupoids) {x zz : 𝒮} (α : zz ⟶ x)
    {V : 𝒞} (mm : V ⟶ pp.obj x) (hlift : pp.IsHomLift mm α)
    {y : 𝒮} (g : y ⟶ x) (v : pp.obj y ⟶ V) (hv : pp.map g = v ≫ mm) :
    Nonempty (y ⟶ zz) := by
  have hcart : pp.IsStronglyCartesian mm α := hpp.isStronglyCartesian_homLift mm α
  have hl2 : pp.IsHomLift (pp.map g) g := inferInstance
  rw [hv] at hl2
  obtain ⟨c, -, -⟩ :=
    Functor.IsStronglyCartesian.universal_property pp mm α v (v ≫ mm) rfl g
  exact ⟨c⟩

section Descent

variable {Jdx : Type v} {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
  (𝒵 : Jdx → Stack.AlgebraicStacks.{u, w} B S hS) (f : ∀ j, 𝒵 j ⟶ 𝒳)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The inverse image `f_j^{-1}` of sheaves of modules along the `j`-th member of a family of
1-morphisms of algebraic stacks, on the site of the indicated topology. -/
noncomputable abbrev familyModulePullback (j : Jdx) :
    SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ hτ) ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS (𝒵 j).val.val.p
        (𝒵 j).val.isFiberedInGroupoids τ hτ) :=
  modulePullback B S hS (𝒵 j).val.val.p 𝒳.val.val.p (𝒵 j).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor (f j).hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (f j).hom) τ hτ

/-- **Descent of quasi-coherence along a family of 1-morphisms with locally liftable objects.**
Let `f j : 𝒵 j ⟶ 𝒳` be a family of 1-morphisms of algebraic stacks over `S` and let `M` be a
sheaf of `𝒪_𝒳`-modules on the site of `𝒳` for the topology `τ`.  Suppose every inverse image
`f j^{-1} M` is quasi-coherent, and suppose that every object `y` of the fibre of `𝒳` over an
object `U` of the site admits a `τ`-covering family `{W i → U}` of `U` together with, for every
`i`, an object of some `𝒵 (a i)` whose image maps to `y` over `W i → U`.  Then `M` is
quasi-coherent.

This is the common argument of the two parts of **Stacks 07AZ**; the two liftability hypotheses
are supplied by `AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift` for a jointly
surjective smooth family and by
`AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift` for a jointly surjective flat and
locally finitely presented one. -/
theorem isQuasicoherentOnSite_of_familyFibreLift
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ hτ))
    (hM : ∀ j, ((familyModulePullback B S hS 𝒵 f τ hτ j).obj M).IsQuasicoherentOnSite)
    (hlift : ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber U),
      ∃ (I : Type (u + 1)) (W : I → B.Schemes) (m : ∀ i, W i ⟶ U.left) (a : I → Jdx),
        Sieve.ofArrows (fun i => (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS))
              (fun i => (Over.homMk (m i) : Over.mk (m i ≫ U.hom) ⟶ U))
            ∈ τ.over (B.obj hS) U ∧
          ∀ i, ∃ (z : (𝒵 (a i)).val.val.obj)
            (α : (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj z ⟶ y.1),
            𝒳.val.val.p.IsHomLift
              (Over.homMk (m i) rfl :
                (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α) :
    M.IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem M fun x => ?_
  have hfib : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨I, W, m, a, hR, hl⟩ := hlift (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  refine (associatedTopology B S hS 𝒳.val.val.p τ).transitive
    (Functor.functorPullback_mem_inheritedTopology 𝒳.val.val.p (τ.over (B.obj hS)) x hR) _
    fun y g hg => ?_
  rw [Stacks.SheafOfModules.presentedSieve_pullback]
  obtain ⟨i, v, hv⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  obtain ⟨z, α, hα⟩ := hl i
  obtain ⟨c⟩ := nonempty_hom_of_isHomLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids α _ hα g v hv
  exact Stacks.SheafOfModules.presentedSieve_mem_of_hom M c
    (presentedSieve_image_mem B S hS (𝒵 (a i)).val.val.p 𝒳.val.val.p
      (𝒵 (a i)).val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom)
      (CatFiberedInGroupoids.homFunctor_comp_p (f (a i)).hom) τ hτ M (hM (a i)) z)

/-- **Stacks 07AZ, part (1).**  Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of
algebraic stacks over `S` which is jointly surjective, that is `|𝒳| = ⋃ j, |f j|(|𝒵 j|)` for the
points of **Stacks 04XG**, and let `M` be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale`.  If every
inverse image `f j^{-1} M` is quasi-coherent, then so is `M`.

Joint surjectivity turns every object of `𝒳` into one covered, étale-locally, by images of
objects of the members of the family; quasi-coherence of the inverse images presents `M` globally
on a covering of each of those images, and quasi-coherence is local. -/
@[stacks 07AZ "part (1): the smooth family on the étale site"]
theorem isQuasicoherentOnSite_of_isSmooth_jointlySurjective
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale)))
    (hM : ∀ j, ((familyModulePullback B S hS 𝒵 f (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale) j).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_familyFibreLift B S hS 𝒵 f _ _ M hM fun U y => ?_
  obtain ⟨I, W, e, a, hetale, hcov, hl⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS f hsmooth hjs U y
  exact ⟨I, W, e, a, mem_etaleOverTopology_of_family B S hS W e hetale hcov, hl⟩

/-- **Stacks 07AZ, part (2).**  Let `f j : 𝒵 j ⟶ 𝒳` be a family of 1-morphisms of algebraic
stacks over `S` which are each flat and locally of finite presentation and which is jointly
surjective, that is `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `M` be a sheaf of `𝒪_𝒳`-modules on
`𝒳_fppf`.  If every inverse image `f j^{-1} M` is quasi-coherent, then so is `M`.

This is the argument of part (1) with "smooth" replaced by "flat and locally of finite
presentation" and the étale covering of **Stacks 06XH** by the fppf covering of
**Stacks 07AN**. -/
@[stacks 07AZ "part (2): the flat, locally finitely presented family on the fppf site"]
theorem isQuasicoherentOnSite_of_isFlat_isLfp_jointlySurjective
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : ∀ j, ((familyModulePullback B S hS 𝒵 f B.topology le_rfl j).obj
      M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_familyFibreLift B S hS 𝒵 f _ _ M hM fun U y => ?_
  obtain ⟨I, W, m, a, hflat', hlfp', hcov, hl⟩ :=
    exists_fppfCovering_family_fibre_lift B S hS f hflat hlfp hjs U y
  exact ⟨I, W, m, a, mem_topology_of_family B S hS W m hflat' hlfp' hcov, hl⟩

end Descent

end AlgebraicGeometry.Stack

end
