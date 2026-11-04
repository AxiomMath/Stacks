module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackGerbe
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSieveValuationRingExtension
public import StacksFrontier.CategoryTheory.Sites.CostructuredArrowRestrictedTopology

/-!
# Points of the relative Picard functor over a valuation ring

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S`, the standing data of Stacks 0D25,
and let `R` be a valuation ring whose spectrum is a test scheme over `B`. An element of
`Pic_{X/B}(Spec R)` is, fppf locally on `Spec R`, the class of an invertible module, and two
invertible modules on `X_{Spec R}` with the same image in `Pic_{X/B}(Spec R)` are fppf locally
isomorphic (the gerbe property of Stacks 0DME). Over a valuation ring "fppf locally" may be
replaced by "after an extension of valuation rings".

## Main results

* `AlgebraicGeometry.Space.exists_valuationRing_extension_mem_of_mem_restrictedTopology`: a
  covering sieve of a valuation-ring test scheme over an algebraic space contains the spectrum
  of an extension.
* `AlgebraicGeometry.Space.PicardSituation.exists_valuationRing_extension_picardClassMap_eq`:
  an element of `Pic_{X/B}(Spec R)` is the class of an invertible module after an extension
  of `R`.
* `AlgebraicGeometry.Space.PicardSituation.exists_valuationRing_extension_picardMap_eq`: two
  Picard classes on `X_{Spec R}` with the same image in `Pic_{X/B}(Spec R)` agree after an
  extension of `R`.

## References

* [Stacks Project, Tag 0DME](https://stacks.math.columbia.edu/tag/0DME)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The test scheme over an algebraic space `Z` given by the spectrum of an extension `R'` of a
valuation-ring test scheme `Spec R ⟶ Z`, and the morphism of test schemes to `Spec R`. -/
abbrev valuationRingExtensionHom {Z : AlgebraicSpaces B S hS}
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    (ring_mem : B.Contains (Spec (.of R))) (ring_mem' : B.Contains (Spec (.of R')))
    (base : Spec (.of R) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base) ⟶ Z) :
    (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
        (specSiteObjectMap φ ring_mem ring_mem' base) ≫ h) : SchemesOver Z) ⟶
      CostructuredArrow.mk h :=
  CostructuredArrow.homMk (specSiteObjectMap φ ring_mem ring_mem' base) rfl

/-- **A covering sieve of a valuation-ring test scheme contains the spectrum of an extension.**
Let `Z` be an algebraic space over `S` and let `Spec R ⟶ Z` be a test scheme, `R` a valuation
ring. Every covering sieve of it for the fppf topology on the test schemes over `Z` contains the
morphism of test schemes `Spec R' ⟶ Spec R` of an extension of valuation rings `R ⟶ R'` whose
spectrum belongs to the site. -/
theorem exists_valuationRing_extension_mem_of_mem_restrictedTopology
    {Z : AlgebraicSpaces B S hS} (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (ring_mem : B.Contains (Spec (.of R))) (base : Spec (.of R) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base) ⟶ Z)
    {Sv : Sieve (CostructuredArrow.mk h : SchemesOver Z)}
    (hSv : Sv ∈ (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Z).restrictedTopology
      (BigFppfOver.topology B S hS) (CostructuredArrow.mk h)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (φ : R →+* R'), ValuationRing.IsExtension φ ∧
      ∃ ring_mem' : B.Contains (Spec (.of R')),
        Sv.arrows (valuationRingExtensionHom φ ring_mem ring_mem' base h) := by
  rw [CostructuredArrow.mem_restrictedTopology_proj_iff] at hSv
  obtain ⟨R', _, _, _, φ, hext, ring_mem', hmem⟩ :=
    exists_valuationRing_extension_mem_of_mem_topology R ring_mem base hSv
  exact ⟨R', inferInstance, inferInstance, inferInstance, φ, hext, ring_mem',
    (CostructuredArrow.mem_functorPushforward_proj_iff _ _ Sv
      (valuationRingExtensionHom φ ring_mem ring_mem' base h)).mp hmem⟩

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- **An element of `Pic_{X/B}(Spec R)` is the class of an invertible module after an
extension of `R`.** Let `Spec R ⟶ B` be a test scheme with `R` a valuation ring. For every
element `x` of the relative Picard functor at it there are an extension of valuation rings
`R ⟶ R'` whose spectrum belongs to the site and a Picard class of `X_{Spec R'}` whose image in
`Pic_{X/B}(Spec R')` is the restriction of `x`. -/
theorem exists_valuationRing_extension_picardClassMap_eq
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (ring_mem : B.Contains (Spec (.of R))) (base : Spec (.of R) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base) ⟶ s.base)
    (x : s.picardFunctor.obj (Opposite.op (CostructuredArrow.mk h))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (φ : R →+* R'), ValuationRing.IsExtension φ ∧
      ∃ (ring_mem' : B.Contains (Spec (.of R'))) (y : s.picardAt _),
        s.picardClassMap _ y =
          s.picardFunctor.map (valuationRingExtensionHom φ ring_mem ring_mem' base h).op x := by
  obtain ⟨R', _, _, _, φ, hext, ring_mem', ⟨y, hy⟩⟩ :=
    exists_valuationRing_extension_mem_of_mem_restrictedTopology R ring_mem base h
      (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor x)
  exact ⟨R', inferInstance, inferInstance, inferInstance, φ, hext, ring_mem', y, hy⟩

/-- **Two Picard classes with the same image in `Pic_{X/B}(Spec R)` agree after an extension
of `R`.** Let `Spec R ⟶ B` be a test scheme with `R` a valuation ring. If two elements of
`Pic(X_{Spec R})` have the same image in the relative Picard functor, then there is an
extension of valuation rings `R ⟶ R'` whose spectrum belongs to the site over which their
pullbacks to `Pic(X_{Spec R'})` agree. -/
theorem exists_valuationRing_extension_picardMap_eq
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (ring_mem : B.Contains (Spec (.of R))) (base : Spec (.of R) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base) ⟶ s.base)
    (x y : s.picardAt (CostructuredArrow.mk h))
    (hxy : s.picardClassMap _ x = s.picardClassMap _ y) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (φ : R →+* R'), ValuationRing.IsExtension φ ∧
      ∃ ring_mem' : B.Contains (Spec (.of R')),
        s.picardMap (valuationRingExtensionHom φ ring_mem ring_mem' base h) x =
          s.picardMap (valuationRingExtensionHom φ ring_mem ring_mem' base h) y :=
  exists_valuationRing_extension_mem_of_mem_restrictedTopology R ring_mem base h
    (s.isLocallyInjective_toPicardFunctor.equalizerSieve_mem
      (X := Opposite.op (CostructuredArrow.mk h)) x y hxy)

end PicardSituation

end AlgebraicGeometry.Space

end
