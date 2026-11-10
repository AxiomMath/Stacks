module

public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.Locality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# The affine objects of a category fibred in groupoids over schemes

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and give `𝒳` the topology it
inherits from the big fppf site over `S`.  Call an object `x` of `𝒳` *affine* when the scheme
`p x` underlying its image is affine.  This file proves the two facts about the affine objects
that do not depend on the module theory: they cover the final object of `𝒳`, and the slice site
of `𝒳` at any object has sheafification into abelian groups with locally bijective weak
equivalences.

Covering is obtained from an affine open cover of the scheme underlying `p x`: a Zariski cover
is an fppf cover, so after replacing it by a combinatorial representative inside the chosen
size-bounded category of schemes it is one of the site's covering families, and lifting its
members along `p` — possible because `p` is fibred in groupoids, which also makes every lift
strongly cartesian — produces a covering family of `x` for the inherited topology.

The sheafification facts hold at *every* object, not only the affine ones: the slice of `𝒳` at
`x` is equivalent to the slice of the chosen category of schemes at the scheme `p x`, by the
localization equivalence of Stacks 06W0, and that slice is essentially small.

Together with the two module-theoretic conditions of
`Stacks.SheafOfModules.PresentingCover` — that quasi-coherent modules are globally presented on
the slice site at an affine object, and that global presentations there are closed under
colimits — these assemble into a presenting cover, hence into the colimits clause of
Stacks 06WN.

## Main definitions

* `AlgebraicGeometry.FibredSite.AffineObjects` is the type of affine objects of `𝒳`, and
  `AlgebraicGeometry.FibredSite.affineObj` the corresponding family of objects of `𝒳`.

## Main results

* `AlgebraicGeometry.FibredSite.coversTop_affineObj`: the affine objects cover the final object
  of the associated fppf site.
* `AlgebraicGeometry.FibredSite.essentiallySmall_over`: every slice of `𝒳` is essentially
  small.
* `AlgebraicGeometry.FibredSite.hasWeakSheafify_over` and
  `AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_over`: the two sheafification
  conditions on the slice site at an object.
* `AlgebraicGeometry.FibredSite.presentingCoverOfAffine` assembles a presenting cover for the
  affine objects out of the above and the two module-theoretic conditions.

## Implementation notes

`AlgebraicGeometry.FibredSite.coversTop_affineObj` is stated for the fppf topology only.  The
affine open cover used in its proof is Zariski, hence a covering family for all five
topologies, but the representative supplied by Stacks 03WX inside the size-bounded category is
only known to be an fppf covering family, which is what the four coarser selected collections
of `AlgebraicGeometry.BigFppfSite.baseTopology` ask for in addition.

The characterisation `CategoryTheory.Functor.IsInheritedTopology` is what turns a covering
family of `p x` into a covering family of `x`; its strong-cartesianness hypothesis is vacuous
here because every morphism of a category fibred in groupoids is strongly cartesian over its
image (Stacks 003V).

`AlgebraicGeometry.FibredSite.essentiallySmall_over` uses only the equivalence of *categories*
of Stacks 06W0, not the accompanying identification of topologies: essential smallness is a
property of the underlying category, and the two sheafification conditions follow from it on
any site.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The affine objects of a category over the big fppf category of schemes over `S`: those
whose image has affine underlying scheme. -/
abbrev AffineObjects : Type v := {x : 𝒳 // IsAffineOver B S hS (p.obj x)}

/-- The family of affine objects of a category over the big fppf category of schemes over `S`,
indexed by itself. -/
abbrev affineObj : AffineObjects B S hS p → 𝒳 := Subtype.val

/-- An affine object has affine underlying scheme. -/
theorem isAffine_affineObj (i : AffineObjects B S hS p) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (affineObj B S hS p i))) := i.2

/-- **The affine objects cover the final object.**  For an object `x` of a category fibred in
groupoids over the big fppf category of schemes over `S`, an affine open cover of the scheme
underlying `p x` is an fppf covering family of the big site, and its members lift along `p` to
a covering family of `x` for the inherited topology whose members are affine. -/
theorem coversTop_affineObj (hp : p.IsFiberedInGroupoids) :
    (BigFppfOver.associatedTopology B S hS p .fppf).CoversTop (affineObj B S hS p) := by
  classical
  intro W
  -- An affine open cover of the scheme underlying `p W`, represented inside the site.
  obtain ⟨V, hV, hVU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B
    (p.obj W).left (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover
  obtain ⟨-, β, hβ⟩ := hVU
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := by
    intro j
    obtain ⟨e, -⟩ := hβ j
    have : IsAffine
        ((B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.X (β j)) := by
      change IsAffine
        (Spec ((B.inclusion.obj (p.obj W).left).affineOpenCover.X (β j)))
      exact isAffine_Spec _
    have hIso : IsIso e.hom := e.isIso_hom
    exact @IsAffine.of_isIso _ _ e.hom hIso inferInstance
  -- The corresponding covering family of `p W` in the big fppf category over `S`.
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .fppf (p.obj W) := by
    change Sieve.ofArrows Vobj vmap ∈ (B.topology.over (B.obj hS)) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows V.X V.f ∈ B.topology (p.obj W).left
    have hpre : V.presieve₀ ∈ B.precoverage (p.obj W).left := ⟨V, rfl, hV⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  -- Lift the family along `p`.
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => by
    have := hφ j; exact IsHomLift.domain_eq p (vmap j) (φ j)
  have hcart : ∀ j, p.IsStronglyCartesian (p.map (φ j)) (φ j) :=
    fun j => hp.isStronglyCartesian (φ j)
  -- Each member of the base family is in the sieve generated by the images of the lifts.
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    have := hφ j
    have hfac := IsHomLift.fac p (vmap j) (φ j)
    simpa using hfac
  -- The lifted family is a covering family of `W` for the inherited topology.
  have hfib : p.IsFibered := hp.isFibered
  have hcov : Sieve.ofArrows y φ ∈
      BigFppfOver.associatedTopology B S hS p .fppf W := by
    refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .fppf) y φ hcart).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .fppf).superset_covering ?_ hBcover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨j, a, rfl⟩ := hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a
  -- Its members are affine.
  have hrange : Set.range y ⊆ Set.range (affineObj B S hS p) := by
    rintro x ⟨j, rfl⟩
    refine ⟨⟨y j, ?_⟩, rfl⟩
    change IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))
    rw [hdom j]
    exact hVaff j
  exact (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering
    ((Sieve.ofArrows_le_ofObjects y φ).trans (Sieve.ofObjects_mono hrange)) hcov

/-- **Every slice of a category fibred in groupoids over schemes is essentially small.**  By the
localization equivalence of Stacks 06W0 the slice of `𝒳` at `x` is equivalent to the slice of
the chosen category of schemes at the scheme underlying `p x`, and the chosen category of
schemes is essentially small because of its size cutoff. -/
theorem essentiallySmall_over (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    EssentiallySmall.{u} (Over x) := by
  have := Stack.isEquivalence_overPost B S hS p hp x
  exact (essentiallySmall_congr
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence).2 inferInstance

/-- Sheafification into abelian groups exists on the slice at any object of the associated site
of a category fibred in groupoids over the big fppf category of schemes over `S`, because that
slice is essentially small. -/
theorem hasWeakSheafify_over (hp : p.IsFiberedInGroupoids) (τ : SiteKind) (x : 𝒳) :
    HasWeakSheafify ((BigFppfOver.associatedTopology B S hS p τ).over x) AddCommGrpCat.{u} := by
  have := essentiallySmall_over B S hS p hp x
  let _ : HasSheafify ((BigFppfOver.associatedTopology B S hS p τ).over x) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  infer_instance

/-- Weak equivalences of abelian presheaves on the slice at any object of the associated site of
a category fibred in groupoids over the big fppf category of schemes over `S` are the locally
bijective maps, because that slice is essentially small. -/
theorem wEqualsLocallyBijective_over (hp : p.IsFiberedInGroupoids) (τ : SiteKind) (x : 𝒳) :
    ((BigFppfOver.associatedTopology B S hS p τ).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} := by
  have := essentiallySmall_over B S hS p hp x
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **The affine objects as a presenting cover.**  Given that quasi-coherent modules are
globally presented on the slice site at an affine object and that global presentations there are
closed under colimits of shape `K`, the affine objects of a category fibred in groupoids over
the big fppf category of schemes over `S` form a
`Stacks.SheafOfModules.PresentingCover` for the structure sheaf of its associated fppf site. -/
def presentingCoverOfAffine (hp : p.IsFiberedInGroupoids) (K : Type u) [Category.{u} K]
    (hpres : ∀ M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf),
      M.IsQuasicoherentOnSite →
        ∀ i : AffineObjects B S hS p, (M.over (affineObj B S hS p i)).HasGlobalPresentation)
    (hcolim : ∀ (i : AffineObjects B S hS p)
      (D : K ⥤ SheafOfModules.{u}
        ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i)))
      (c : Cocone D), IsColimit c → (∀ k, (D.obj k).HasGlobalPresentation) →
        c.pt.HasGlobalPresentation) :
    Stacks.SheafOfModules.PresentingCover
      (ringStructureSheafCore B S hS p hp .fppf) K where
  I := AffineObjects B S hS p
  obj := affineObj B S hS p
  coversTop := coversTop_affineObj B S hS p hp
  hasWeakSheafify_over _ := hasWeakSheafify_over B S hS p hp .fppf _
  wEqualsLocallyBijective_over _ := wEqualsLocallyBijective_over B S hS p hp .fppf _
  hasGlobalPresentation_over := hpres
  hasGlobalPresentation_of_isColimit := hcolim

end AlgebraicGeometry.FibredSite

end
