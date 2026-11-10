module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcoh
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentEtaleSheafClause
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Local quasi-coherence descends along flat, locally finitely presented families (Stacks 07AP)

Let `f j : 𝒵 j ⟶ 𝒳`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks over `S` which are
each flat (**Stacks 06PW**) and locally of finite presentation (**Stacks 06Q2**, part (1)) and
whose images cover the points of `𝒳`, `|𝒳| = ⋃ j, |f j|(|𝒵 j|)` (**Stacks 04XG**). Let `F` be a
sheaf of `𝒪_𝒳`-modules on `𝒳_fppf`. **Stacks 07AP** says that if every inverse image
`f j^{-1} F` is locally quasi-coherent (**Stacks 06WJ**) then so is `F`. This file proves it:
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isFlat_isLfp_jointlySurjective`.

## The route

Local quasi-coherence of `F` is the étale sheaf condition, which follows from the fppf one,
together with quasi-coherence of every restriction `x^*F|_{U_étale}`. On the small étale site
of a scheme, quasi-coherence is the cartesian condition between affine objects
(`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffines`, Descent,
Proposition 03DX), and the index functor of **Stacks 06W1** turns that condition for
`x^*F|_{U_étale}` into the cartesian condition for `F` itself along the arrows of `𝒳` lying
over étale morphisms of affine schemes
(`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff`).
So what has to be shown is that for every such arrow `φ : y ⟶ y'` the comparison
`𝒪(y) ⊗_{𝒪(y')} F(y') ⟶ F(y)` is bijective.

That is a descent statement, and it is proved by descending along an fppf covering of `y'`
on which the comparison is already known. The fppf-local factorisation of **Stacks 07AN**
gives a covering sieve of the scheme below `y'` over each arrow of which `y'` is the image of an
object of some `𝒵 j`; since that scheme is affine the sieve contains a *finite* family of
arrows from affine schemes which are flat, locally of finite presentation and jointly surjective,
and lifting them gives arrows `α i : w i ⟶ y'` of `𝒳` out of image objects. An object of `𝒳`
with an arrow into an image object is isomorphic to an image object, because the image of a
fibred 1-morphism is closed under pullback; so at every such object the restriction of `F` is
quasi-coherent by hypothesis, and `F` is cartesian along every arrow into it lying over an étale
morphism of affine schemes. The base changes of `φ` to the `w i` and to their pairwise fibre
products are arrows of exactly that kind. `F` satisfies the sheaf condition for the covering
`{α i}` and its base change to `y`, because it is an fppf sheaf, and fibre products of affine
schemes give pushout squares of rings of global functions. Flat descent of modules,
`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover`, assembles the comparisons.

The source argues instead through the exact sequence `0 → F → a_*a^*F → b_*b^*F` of
**Stacks 06XE** and the direct images of **Stacks 075Z**; the descent of the cartesian
condition proved here replaces both, and uses only the degree-zero, affine case of their
content.

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_isQuasicoherentOnSite_target`: a module
  whose restriction at `y'` is quasi-coherent is cartesian along every arrow into `y'` lying over
  an étale morphism of affine schemes.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_hom_image`: the
  restriction is quasi-coherent at every object with an arrow into an image object.
* `AlgebraicGeometry.Stack.exists_finite_affine_flat_family_of_mem_topology`: a covering sieve
  of an affine object contains a finite family of flat, locally finitely presented arrows with
  affine sources which is jointly surjective.
* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_isFlat_isLfp_jointlySurjective`: the
  descent step.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isFlat_isLfp_jointlySurjective`:
  **Stacks 07AP**.

## Implementation notes

The hypothesis on `F` is the source's: a sheaf of modules on `𝒳_fppf`, that is a presheaf of
modules over the structure sheaf which is a sheaf for the inherited fppf topology. The presheaf
of rings underlying the structure sheaf does not depend on the topology
(`AlgebraicGeometry.Stack.ringStructureSheafCore_obj`), so `F` is typed over the one local
quasi-coherence is stated for. The fppf sheaf condition is used: it is the sheaf condition along
the fppf covering `{α i}` that lets the cartesian condition descend.

This completes
`AlgebraicGeometry.Stack.exists_fppfCovering_isQuasicoherentOnSite_restrictModuleToSmallEtale`
of `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatDescent`, which
produces the fppf-local family of quasi-coherent restrictions but not the descent step.

The sections of `F` lie in the universe `u` of the schemes, as for the smooth statement of
**Stacks 075Y**: Descent, Proposition 03DX, through which quasi-coherence on the small étale
sites is read, is available at that universe.

## References

* [Stacks Project, Tag 07AP](https://stacks.math.columbia.edu/tag/07AP)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cartesian along arrows into an object with quasi-coherent restriction -/

/-- **A module whose restriction at `y'` is quasi-coherent is cartesian along every arrow into
`y'` lying over an étale morphism of affine schemes.** The arrow is isomorphic to the image under
the index functor of **Stacks 06W1** at `y'` of a morphism of affine objects of the small étale
site below `y'`, along which the quasi-coherent restriction is cartesian by Descent,
Proposition 03DX. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite_target
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (G : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) G.presheaf)
    {y y' : 𝒳} (f : y ⟶ y') (hf : Etale (B.inclusion.map (p.map f).left))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y')))
    (hqc : (⟨restrictModuleToSmallEtale B E h S hS p hp y' (etaleTopology B)
        (etaleTopology_le_topology B) G,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp y' G hG⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj y').left.1
        (contains_base B E h S hS p y'))).IsQuasicoherentOnSite) :
    IsIso (restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      G f.op) := by
  obtain ⟨e₁, e₂, hsq⟩ := exists_arrowIso_etaleIndex B E h S hS p hp f hf
  have hT : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleChart B E h S hS p f hf)) := hy
  have hT' : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleTop B E h S hS p y')) := hy'
  exact (ConcreteCategory.isIso_iff_bijective _).2 <|
    (bijective_restrictionBaseChange_iff_of_arrowIso
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) G
      ((etaleIndex B E h S hS p hp y').map (etaleChartToTop B E h S hS p f hf)).op
      f.op e₂.hom.op e₁.hom.op (by rw [← op_comp, ← op_comp, hsq])).1 <|
    (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS p hp G
      y' (etaleChartToTop B E h S hS p f hf)).1 <|
    SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite E _ _ _ hqc
      hT hT' (etaleChartToTop B E h S hS p f hf)

/-! ### Quasi-coherence at objects mapping to an image object -/

/-- **The restriction of `F` is quasi-coherent at every object of `𝒳` with an arrow into the
image of an object of `𝒵`**, for a 1-morphism `g : 𝒵 ⟶ 𝒳` along which the inverse image of `F`
is locally quasi-coherent. The arrow `ψ : y ⟶ g(z)` lifts to an arrow `ρ : z' ⟶ z` of `𝒵`
lying over the same morphism of schemes, and since every arrow of `𝒳` is strongly cartesian the
image `g(ρ)` factors through `ψ` by an arrow `g(z') ⟶ y` lying over an identity; quasi-coherence
at the image object `g(z')` then spreads to `y` along that arrow, which is an étale covering. -/
theorem isQuasicoherentOnSite_restrictModuleToSmallEtale_of_hom_image
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hlqc : IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F))
    {y : 𝒳.val.val.obj} {z : 𝒵.val.val.obj}
    (ψ : y ⟶ (CatFiberedInGroupoids.homFunctor g.hom).obj z) :
    (⟨restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids y
        (etaleTopology B) (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids y
        F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (𝒳.val.val.p.obj y).left.1
        (contains_base B E h S hS 𝒳.val.val.p y))).IsQuasicoherentOnSite := by
  classical
  have hp := 𝒳.val.isFiberedInGroupoids
  have hw : CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p = 𝒵.val.val.p := g.hom.hom.w
  have hzbase : 𝒵.val.val.p.obj z =
      𝒳.val.val.p.obj ((CatFiberedInGroupoids.homFunctor g.hom).obj z) :=
    (Functor.congr_obj hw z).symm
  obtain ⟨z', ρ, hρ⟩ :=
    𝒵.val.isFiberedInGroupoids.exists_lift (𝒳.val.val.p.map ψ) z hzbase
  have : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map ψ)
      ((CatFiberedInGroupoids.homFunctor g.hom).map ρ) :=
    PresheafOfCategories.isHomLift_map_of_comp hw (𝒳.val.val.p.map ψ) ρ hρ
  have := hp.isStronglyCartesian ψ
  let χ : (CatFiberedInGroupoids.homFunctor g.hom).obj z' ⟶ y :=
    Functor.IsStronglyCartesian.map 𝒳.val.val.p (𝒳.val.val.p.map ψ) ψ
      (g := 𝟙 _) (Category.id_comp _).symm ((CatFiberedInGroupoids.homFunctor g.hom).map ρ)
  have hχ : 𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj y)) χ :=
    Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  refine isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover B E h S hS
    𝒳.val.val.p hp y F hF (I := PUnit.{u + 2})
    (fun _ => (CatFiberedInGroupoids.homFunctor g.hom).obj z') (fun _ => χ) (fun _ => ?_)
    (fun t => ⟨PUnit.unit, ?_⟩) (fun _ => ?_)
  · refine morphismProperty_map_left_of_isHomLift B S hS 𝒳.val.val.p @Etale inferInstance
      (𝟙 (𝒳.val.val.p.obj y)) ?_ χ hχ
    simp only [Over.id_left]
    infer_instance
  · exact range_map_left_of_isHomLift B S hS 𝒳.val.val.p (k := 𝟙 (𝒳.val.val.p.obj y)) χ hχ
      ⟨t, by simp⟩
  · exact isQuasicoherentOnSite_restrictModuleToSmallEtale_image.{u, u + 1, u, u + 1, u, u}
      B E h S hS 𝒳.val.val.p hp (CatFiberedInGroupoids.homFunctor g.hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      (isFibredOneMorphism_homFunctor_comp B S hS g.hom) F hF hlqc z'

/-! ### A finite flat refinement over an affine object -/

/-- **A covering sieve of an affine object of the big fppf site of `S` contains a finite family
of flat, locally finitely presented arrows with affine sources which is jointly surjective.**
Through every point there passes such an arrow of the sieve, its image is open because a flat,
locally finitely presented morphism is open, and the underlying space of an affine scheme is
compact. This is `AlgebraicGeometry.Stack.exists_finite_affine_family_of_mem_topology` with the
flatness and local finite presentation of the members retained, which the sheaf condition for
the family needs. -/
theorem exists_finite_affine_flat_family_of_mem_topology {A : BigFppfOver B S hS}
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    {R : Sieve A} (hR : R ∈ BigFppfOver.topology B S hS A) :
    ∃ (I : Type u) (_ : Finite I) (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ A),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧ (∀ i, R.arrows (v i)) ∧
        (∀ i, Flat ((BigFppfOver.toScheme B S hS).map (v i))) ∧
          (∀ i, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (v i))) ∧
            ∀ x : (BigFppfOver.toScheme B S hS).obj A,
              ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base := by
  classical
  choose V v hVaff hVR hVflat hVlfp hVmem using fun x =>
    BigFppfOver.exists_affine_mem_of_mem_topology B S hS hR x
  have hopen : ∀ x, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base) := by
    intro x
    have _ := hVflat x
    have _ := hVlfp x
    exact (Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map (v x))).isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base) hopen
    (fun x _ => Set.mem_iUnion.2 ⟨x, hVmem x⟩)
  refine ⟨{x // x ∈ s}, inferInstance, fun i => V i.1, fun i => v i.1, fun i => hVaff i.1,
    fun i => hVR i.1, fun i => hVflat i.1, fun i => hVlfp i.1, fun x => ?_⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hx⟩

/-! ### The descent step -/

/-- **The descent step of Stacks 07AP.** Under the hypotheses of Stacks 07AP, `F` is cartesian
along every arrow `φ : y ⟶ y'` of `𝒳` lying over an étale morphism of affine schemes: the
comparison `𝒪(y) ⊗_{𝒪(y')} F(y') ⟶ F(y)` is bijective.

A finite family `α i : w i ⟶ y'` of arrows out of image objects, lying over a flat, locally
finitely presented and jointly surjective family of morphisms from affine schemes, is obtained
from the fppf-local factorisation of **Stacks 07AN**. It is a covering for the fppf topology,
for which `F` is a sheaf, and along the base changes of `φ` to the `w i` and to their pairwise
fibre products `F` is cartesian, since their targets map to image objects. Flat descent of
modules along the covering gives the statement. -/
theorem isIso_restrictionBaseChange_of_isFlat_isLfp_jointlySurjective {J : Type v}
    {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F))
    {y y' : 𝒳.val.val.obj} (φ : y ⟶ y')
    (hφ : Etale (B.inclusion.map (𝒳.val.val.p.map φ).left))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y'))) :
    IsIso (restrictionBaseChange
      (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj) F φ.op) := by
  classical
  have hp := 𝒳.val.isFiberedInGroupoids
  have hFet : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      F.presheaf :=
    hF.of_le (associatedTopology_mono B S hS 𝒳.val.val.p (etaleTopology_le_topology B))
  -- the fppf-local factorisation of Stacks 07AN, refined to a finite affine family
  obtain ⟨R₀, hR₀, hlift⟩ := exists_fppfCovering_fibre_lift_of_family B S hS f hflat hlfp hjs
    (𝒳.val.val.p.obj y') (Functor.Fiber.mk rfl)
  obtain ⟨I, _, V, v, hVaff, hvR, hvflat, hvlfp, hvcov⟩ :=
    exists_finite_affine_flat_family_of_mem_topology B S hS hy' hR₀
  choose jj zz α hα using fun i => hlift (hvR i)
  let W : I → 𝒳.val.val.obj := fun i =>
    (CatFiberedInGroupoids.homFunctor (f (jj i)).hom).obj (zz i)
  -- the underlying schemes
  have := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS 𝒳.val.val.p hp
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  let Φ := 𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS
  have hΦ : ∀ {P X Y Z : 𝒳.val.val.obj} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z},
      IsPullback fst snd a b → IsPullback (Φ.map fst) (Φ.map snd) (Φ.map a) (Φ.map b) :=
    fun hsq => Functor.map_isPullback (BigFppfOver.toScheme B S hS)
      (hp.map_isPullback _ _ _ _ _ hsq)
  have hWaff : ∀ i, IsAffine (Φ.obj (W i)) := fun i => by
    have := hα i
    change IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj (W i)))
    rw [IsHomLift.domain_eq 𝒳.val.val.p (v i) (α i)]
    exact hVaff i
  have : IsAffine (Φ.obj y) := hy
  have : IsAffine (Φ.obj y') := hy'
  have hunop : ∀ (X : 𝒳.val.val.obj) [IsAffine (Φ.obj X)], IsAffine (Opposite.unop
      ((BigFppfOver.toScheme B S hS).op.obj (𝒳.val.val.p.op.obj (Opposite.op X)))) :=
    fun _ h => h
  have hφ' : Etale (Φ.map φ) := hφ
  have hpbaff : ∀ {X : 𝒳.val.val.obj} (a : X ⟶ y') [IsAffine (Φ.obj X)] (i : I),
      IsAffine (Φ.obj (pullback a (α i))) := fun a _ i =>
    IsAffine.of_isPullback (hΦ (IsPullback.of_hasPullback a (α i)))
  have hWWaff : ∀ c : I × I, IsAffine (Φ.obj (pullback (α c.1) (α c.2))) := fun c =>
    hpbaff (α c.1) c.2
  -- the family covers for the fppf topology
  have hWflat : ∀ i, Flat (Φ.map (α i)) := fun i =>
    morphismProperty_map_left_of_isHomLift B S hS 𝒳.val.val.p @Flat
      (respectsIso_of_isStableUnderComposition_of_isIso @Flat
        fun g hg => by have := hg; infer_instance)
      _ (hvflat i) (α i) (hα i)
  have hWlfp : ∀ i, LocallyOfFinitePresentation (Φ.map (α i)) := fun i =>
    morphismProperty_map_left_of_isHomLift B S hS 𝒳.val.val.p @LocallyOfFinitePresentation
      (respectsIso_of_isStableUnderComposition_of_isIso @LocallyOfFinitePresentation
        fun g hg => by have := hg; infer_instance)
      _ (hvlfp i) (α i) (hα i)
  have hWcov : ∀ t : Φ.obj y', ∃ i, t ∈ Set.range (Φ.map (α i)) := fun t => by
    obtain ⟨i, hi⟩ := hvcov t
    exact ⟨i, range_map_left_of_isHomLift B S hS 𝒳.val.val.p (α i) (hα i) hi⟩
  have hcovV : Sieve.ofArrows W α ∈ associatedTopology B S hS 𝒳.val.val.p B.topology y' :=
    FibredSite.ofArrows_mem_associatedTopology B S hS 𝒳.val.val.p hp W α
      (BigFppfOver.sieve_generate_ofArrows_mem_topology _ _
        ((Scheme.ofArrows_mem_precoverage_iff _).2
          ⟨hWcov, fun i => ⟨hWflat i, hWlfp i⟩⟩))
  have hcovU : Sieve.ofArrows (fun i => pullback φ (α i)) (fun i => pullback.fst φ (α i)) ∈
      associatedTopology B S hS 𝒳.val.val.p B.topology y := by
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.pullback_stable _ φ hcovV)
    rintro Z k ⟨Y', g₁, g₂, ⟨i⟩, hgg⟩
    have hmem := (Sieve.ofArrows (fun i => pullback φ (α i))
        (fun i => pullback.fst φ (α i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback φ (α i)) (fun i => pullback.fst φ (α i)) i)
      (pullback.lift k g₁ hgg.symm)
    rwa [Limits.pullback.lift_fst k g₁ hgg.symm] at hmem
  have hsT := Stacks.SheafOfModules.ChangeOfRings.isSheafOfTypes_of_isSheaf F.presheaf hF
  have hétale : ∀ {X : 𝒳.val.val.obj} (a : X ⟶ y'),
      Etale (B.inclusion.map (𝒳.val.val.p.map (pullback.snd φ a)).left) := fun a =>
    MorphismProperty.of_isPullback (hΦ (IsPullback.of_hasPullback φ a)) hφ'
  -- `F` is cartesian along the base change of `φ` to any affine `X` mapping to some `W i`
  have hiso : ∀ {X : 𝒳.val.val.obj} (a : X ⟶ y') (i : I), (X ⟶ W i) → IsAffine (Φ.obj X) →
      IsIso (restrictionBaseChange
        (R := (structureSheaf B S hS 𝒳.val.val.p hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj) F (pullback.snd φ a).op) :=
    fun a i ψ hX => isIso_restrictionBaseChange_of_isQuasicoherentOnSite_target B E h S hS
      𝒳.val.val.p hp F hFet _ (hétale a)
      (IsAffine.of_isPullback (hΦ (IsPullback.of_hasPullback φ a))) hX
      (isQuasicoherentOnSite_restrictModuleToSmallEtale_of_hom_image B E h S hS
        (f (jj i)) F hFet (hlqc (jj i)) ψ)
  exact isIso_restrictionBaseChange_of_cover
    (R := (structureSheaf B S hS 𝒳.val.val.p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) F φ W α
    (HasRingHomProperty.appTop (P := @Flat) (Φ.map φ) inferInstance)
    ((Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcovV))
    ((Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcovU))
    (fun i => isPushout_appTop_of_isPullback (hΦ (IsPullback.of_hasPullback φ (α i))))
    (fun c => isPushout_appTop_of_isPullback (X := Φ.obj y)
      (Y := Φ.obj (pullback (α c.1) (α c.2))) (Z := Φ.obj y')
      (hΦ (IsPullback.of_hasPullback φ (pullback.fst (α c.1) (α c.2) ≫ α c.1))))
    (fun i => hiso (α i) i (𝟙 _) (hWaff i))
    (fun c => hiso (pullback.fst (α c.1) (α c.2) ≫ α c.1) c.1 (pullback.fst (α c.1) (α c.2))
      (hWWaff c))

/-! ### Stacks 07AP -/

/-- **Stacks 07AP.** Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat (**Stacks 06PW**) and locally
finitely presented (**Stacks 06Q2**) 1-morphisms of algebraic stacks over `S` with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)` (**Stacks 04XG**), and let `F` be a sheaf of `𝒪_𝒳`-modules on
`𝒳_fppf`. If every inverse image `f j^{-1} F` is locally quasi-coherent (**Stacks 06WJ**), then
so is `F`.

The étale sheaf condition follows from the fppf one. At an object `x` lying over `U`, the
restriction `x^*F|_{U_étale}` is quasi-coherent because it is cartesian between affine objects
(Descent, Proposition 03DX), which through the index functor of **Stacks 06W1** is the cartesian
condition for `F` along arrows lying over étale morphisms of affine schemes, proved by
`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_isFlat_isLfp_jointlySurjective`. -/
@[stacks 07AP]
theorem isLocallyQuasicoherent_of_isFlat_isLfp_jointlySurjective {J : Type v}
    {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F)) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F := by
  have hp := 𝒳.val.isFiberedInGroupoids
  have hFet : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      F.presheaf :=
    hF.of_le (associatedTopology_mono B S hS 𝒳.val.val.p (etaleTopology_le_topology B))
  refine ⟨hFet, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS _ hp x F hFet, ?_⟩⟩
  refine SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _
    fun {T T'} g hT hT' => ?_
  exact (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS _ hp F x g).2
    ((ConcreteCategory.isIso_iff_bijective _).1
      (isIso_restrictionBaseChange_of_isFlat_isLfp_jointlySurjective B E h S hS f hflat hlfp hjs
        F hF hlqc ((etaleIndex B E h S hS _ hp x).map g)
        (etale_etaleIndex_map B E h S hS _ hp x g)
        (isAffine_etaleIndex_obj B E h S hS _ hp x T hT)
        (isAffine_etaleIndex_obj B E h S hS _ hp x T' hT')))

end AlgebraicGeometry.Stack

end
