module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AllChartLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitsInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation

/-!
# The limit criteria of Stacks 0CP4 from limit bridges along étale charts

For a cofiltered inverse system of quasi-compact, quasi-separated algebraic spaces with affine
transition morphisms and algebraic limit, limit bridges along étale charts give limit bridges along
all charts (`AlgebraicGeometry.Space.hasAllChartLimitBridges_of_hasChartLimitBridges`), hence the
chapter's convention of Section 70.2 (`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_iff`),
under which the two halves of Stacks 0CP4 hold.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_hasChartLimitBridges`: limit bridges
  along étale charts give the chapter's convention.
* `AlgebraicGeometry.Space.exists_stage_map_of_limitBridge`: the surjectivity half of Stacks 0CP4.
* `AlgebraicGeometry.Space.exists_stage_eq_of_limitBridge`: the injectivity half of Stacks 0CP4.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Limit bridges along étale charts give the chapter's convention**, for a cofiltered inverse
system of quasi-compact, quasi-separated algebraic spaces with affine transition morphisms whose
limit is an algebraic space. -/
theorem siteContainsBaseChangeLimits_of_hasChartLimitBridges
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hbr : HasChartLimitBridges D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hc' : IsAlgebraicSpace B S hS c.pt) :
    SiteContainsBaseChangeLimits B S hS D :=
  (siteContainsBaseChangeLimits_iff D).2 fun i₀ U₀ f₀ C =>
    (hasAllChartLimitBridges_of_hasChartLimitBridges (hZ := hZ) hDalg hDaff
      (isAlgebraicSpace_of_iso B S hS (hc.conePointUniqueUpToIso (limit.isLimit D)) hc')
      hDqc hDqs hbr i₀ U₀ f₀ C).some.exists_cone

/-- **The surjectivity half of Stacks 0CP4, from limit bridges along étale charts**, for an
inverse system with algebraic limit. -/
theorem exists_stage_map_of_limitBridge
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hbr : HasChartLimitBridges D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (g : c.pt ⟶ V) (i : J) (b : D.obj i ⟶ Z) (hsq : g ≫ φ = c.π.app i ≫ b)
    (hc' : IsAlgebraicSpace B S hS c.pt) :
    ∃ (j : J) (t : D.obj j ⟶ V) (k : J) (a : k ⟶ j) (a' : k ⟶ i),
      c.π.app k ≫ D.map a ≫ t = g ∧ (D.map a ≫ t) ≫ φ = D.map a' ≫ b :=
  exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ D c hc
    (siteContainsBaseChangeLimits_of_hasChartLimitBridges B S hS hZ D c hc hbr hDalg hDqc hDqs
      hDaff hc')
    hDalg hDqc hDqs hDaff hc' hV hZ' φ hφ g i b hsq

/-- **The injectivity half of Stacks 0CP4, from limit bridges along étale charts**, for an
inverse system with algebraic limit. -/
theorem exists_stage_eq_of_limitBridge
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hbr : HasChartLimitBridges D)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hDaff : ∀ {i j : J} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    {V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hZ' : IsAlgebraicSpace B S hS Z) (φ : V ⟶ Z)
    (hφ : IsLocallyOfFinitePresentation B S hS φ)
    (i : J) (r s : D.obj i ⟶ V) (hlim : c.π.app i ≫ r = c.π.app i ≫ s)
    (hbase : r ≫ φ = s ≫ φ) (hc' : IsAlgebraicSpace B S hS c.pt) :
    ∃ (k : J) (a : k ⟶ i), D.map a ≫ r = D.map a ≫ s :=
  exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ D c hc
    (siteContainsBaseChangeLimits_of_hasChartLimitBridges B S hS hZ D c hc hbr hDalg hDqc hDqs
      hDaff hc')
    hDalg hDqc hDqs hDaff hc' hV hZ' φ hφ i r s hlim hbase

end AlgebraicGeometry.Space

end
