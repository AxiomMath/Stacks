module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Limits

/-!
# Comparing the Zariski precoverages with comap along the inclusions

The covering families of a big Zariski site, and of its slices and full subcategories, were
specified by hand. This file identifies the precoverages they present with precoverages
obtained by `Precoverage.comap` along the canonical functors:

* the precoverage of a big Zariski site is the Zariski pretopology of schemes comapped along
  its inclusion into schemes;
* the precoverage of the big Zariski slice over `S` is the site's own comapped along the slice
  forgetful functor;
* the precoverage of the small Zariski site is the slice's comapped along the full inclusion.

These identifications are what let the stability properties — closure under isomorphisms, base
change and composition — be inherited from the corresponding properties of the Zariski
precoverage on all schemes, instead of being reproved for each category.

## Main results

* `AlgebraicGeometry.bigZariskiPrecoverage_eq_comap`,
  `AlgebraicGeometry.bigZariskiOver_precoverage_eq_comap`,
  `AlgebraicGeometry.smallZariski_precoverage_eq_comap` — the three identifications.
* The instances record that the precoverages have isomorphisms and are stable under base change
  and composition.

## Implementation notes

Each identification needs that a presieve on the smaller category is determined by its image on
the larger one. For the slice forgetful functor that is `overForget_presieve_map_injective`,
which is site-agnostic and is reused from the étale development rather than restated here; for
the full inclusion of the small Zariski category it is
`AlgebraicGeometry.smallZariski_presieve_map_injective`. Both hold because the functors in
question are fully faithful. In the other direction a covering family upstairs has to be
lifted, which uses that an object of the slice over an object open in `S` is itself open in `S`.

The stability properties of the Zariski precoverage on all schemes are obtained by unfolding it
to `MorphismProperty.precoverage @IsOpenImmersion` and using that open immersions are
multiplicative, jointly-surjectivity-preserving, and stable under base change.

## References

* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020Y](https://stacks.math.columbia.edu/tag/020Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If a presieve on `X` maps to the presieve of a hypercover `E`, and `E` is the image of `E'`,
then the presieve is that of `E'`, provided `F` is injective on presieves. -/
private theorem eq_presieve₀_of_map_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X : C} {R : Presieve X} {E' : PreZeroHypercover X} {E : PreZeroHypercover (F.obj X)}
    (hinj : ∀ {R Q : Presieve X}, R.map F = Q.map F → R = Q) (hmap : E'.map F = E)
    (hR : R.map F = E.presieve₀) : R = E'.presieve₀ :=
  hinj (by rw [hR, ← hmap, PreZeroHypercover.presieve₀_map])

/-- The precoverage of a big Zariski site is the Zariski pretopology of schemes, comapped along
the site's canonical inclusion into all schemes. -/
public theorem bigZariskiPrecoverage_eq_comap (B : AlgebraicGeometry.BigZariskiSite.{u}) :
    B.precoverage = Scheme.zariskiPretopology.toPrecoverage.comap B.inclusion := by
  ext X R
  rw [Precoverage.mem_comap_iff]
  show (∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ R = E.presieve₀) ↔ _
  constructor
  · rintro ⟨E, hE, hR⟩
    rw [hR, ← PreZeroHypercover.presieve₀_map]
    exact hE.1
  · intro hR
    let E : PreZeroHypercover.{u + 1} X :=
      ⟨R.uncurry, fun i => i.1.1, fun i => i.1.2⟩
    have hE : E.presieve₀ = R := by
      funext Y g
      refine propext ⟨?_, fun hg => .mk (⟨⟨Y, g⟩, hg⟩ : R.uncurry)⟩
      rintro ⟨i⟩
      exact i.2
    have hZ : AlgebraicGeometry.IsZariskiCovering ⟨X, E⟩ := by
      show (E.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology _
      rw [PreZeroHypercover.presieve₀_map, hE]
      exact hR
    obtain ⟨E', hE', hXE, hcomb⟩ := B.covering_representative ⟨X, E⟩ hZ
    cases hXE
    exact ⟨E'.2, hE', hE.symm.trans
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb)⟩

/-- The precoverage of the big Zariski category over `S` is the site's precoverage comapped
along the slice forgetful functor. -/
public theorem bigZariskiOver_precoverage_eq_comap
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : B.Schemes) :
    BigZariskiOver.precoverage B S.obj S.property =
      B.precoverage.comap (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)) := by
  ext U R
  rw [BigZariskiOver.mem_precoverage_iff, Precoverage.mem_comap_iff]
  constructor
  · rintro ⟨E, hR, hE⟩
    refine ⟨E.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)), hE, ?_⟩
    rw [hR, ← PreZeroHypercover.presieve₀_map]
  · rintro ⟨E, hE, hR⟩
    let E' : PreZeroHypercover.{u + 1} U :=
      ⟨E.I₀, fun i => Over.mk (E.f i ≫ U.hom),
        fun i => Over.homMk (E.f i) (by simp)⟩
    have hmap : E'.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)) = E := by
      cases E
      rfl
    refine ⟨E', eq_presieve₀_of_map_eq _ overForget_presieve_map_injective hmap hR, ?_⟩
    show B.IsCovering
      ⟨(Over.forget (⟨S.obj, S.property⟩ : B.Schemes)).obj U,
        (E'.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)))⟩
    simpa [BigZariskiOver.IsCovering, hmap] using hE

/-- The precoverage of a big Zariski site has isomorphisms. -/
public instance bigZariskiPrecoverage_hasIsos (B : AlgebraicGeometry.BigZariskiSite.{u}) :
    B.precoverage.HasIsos := by
  constructor
  intro U V g hg
  change ∃ E : PreZeroHypercover V, B.IsCovering ⟨V, E⟩ ∧
      Presieve.singleton g = E.presieve₀
  refine ⟨PreZeroHypercover.singleton g, B.coverings_isSite.1 g, ?_⟩
  simp

private alias zariskiPrecoverage_isStableUnderComposition :=
  AlgebraicGeometry.Scheme.zariskiPrecoverage_isStableUnderComposition

private alias zariskiPrecoverage_isStableUnderBaseChange :=
  AlgebraicGeometry.Scheme.zariskiPrecoverage_isStableUnderBaseChange

/-- The precoverage of a big Zariski site is stable under base change. -/
public instance bigZariskiPrecoverage_stableUnderBaseChange
    (B : AlgebraicGeometry.BigZariskiSite.{u}) : B.precoverage.IsStableUnderBaseChange := by
  have : Scheme.zariskiPretopology.toPrecoverage.IsStableUnderBaseChange :=
    zariskiPrecoverage_isStableUnderBaseChange
  have : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigZariskiSiteInclusion B
  rw [bigZariskiPrecoverage_eq_comap B]
  infer_instance

/-- The precoverage of a big Zariski site is stable under composition. -/
public instance bigZariskiPrecoverage_stableUnderComposition
    (B : AlgebraicGeometry.BigZariskiSite.{u}) : B.precoverage.IsStableUnderComposition := by
  have : Scheme.zariskiPretopology.toPrecoverage.IsStableUnderComposition :=
    zariskiPrecoverage_isStableUnderComposition
  rw [bigZariskiPrecoverage_eq_comap B]
  infer_instance

/-- The precoverage of the big Zariski category over `S` has isomorphisms. -/
public instance bigZariskiOver_precoverage_hasIsos
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : B.Schemes) :
    (BigZariskiOver.precoverage B S.obj S.property).HasIsos := by
  rw [bigZariskiOver_precoverage_eq_comap B S]
  infer_instance

/-- The precoverage of the big Zariski category over `S` is stable under base change. -/
public instance bigZariskiOver_precoverage_stableUnderBaseChange
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : B.Schemes) :
    (BigZariskiOver.precoverage B S.obj S.property).IsStableUnderBaseChange := by
  have : B.precoverage.IsStableUnderBaseChange := bigZariskiPrecoverage_stableUnderBaseChange B
  rw [bigZariskiOver_precoverage_eq_comap B S]
  infer_instance

/-- The precoverage of the big Zariski category over `S` is stable under composition. -/
public instance bigZariskiOver_precoverage_stableUnderComposition
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : B.Schemes) :
    (BigZariskiOver.precoverage B S.obj S.property).IsStableUnderComposition := by
  have : B.precoverage.IsStableUnderComposition := bigZariskiPrecoverage_stableUnderComposition B
  have : Scheme.zariskiPretopology.toPrecoverage.IsStableUnderComposition :=
    zariskiPrecoverage_isStableUnderComposition
  rw [bigZariskiOver_precoverage_eq_comap B S, bigZariskiPrecoverage_eq_comap B,
    ← Precoverage.comap_comp]
  infer_instance

/-- A slice of the underlying category of a big Zariski site has equalizers. -/
public instance bigZariskiOver_hasEqualizers (B : AlgebraicGeometry.BigZariskiSite.{u})
    (X : B.Schemes) : HasEqualizers (BigZariskiOver B X.obj X.property) := by
  have : HasBinaryProducts (BigZariskiOver B X.obj X.property) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

/-- A presieve on an object of the small Zariski category is determined by its image in the big
Zariski category over `S`. -/
public theorem smallZariski_presieve_map_injective
    {B : AlgebraicGeometry.BigZariskiSite.{u}} {T : B.Schemes}
    {X : SmallZariski B T.obj T.property} {R Q : Presieve X}
    (h : R.map (SmallZariski.inclusion B T.obj T.property) =
      Q.map (SmallZariski.inclusion B T.obj T.property)) : R = Q := by
  suffices ∀ {R Q : Presieve X},
      R.map (SmallZariski.inclusion B T.obj T.property) =
        Q.map (SmallZariski.inclusion B T.obj T.property) → R ≤ Q from
    le_antisymm (this h) (this h.symm)
  intro R Q h Y g hR
  have hm : (R.map (SmallZariski.inclusion B T.obj T.property))
      ((SmallZariski.inclusion B T.obj T.property).map g) := Presieve.map_map hR
  rw [h, Presieve.map_iff] at hm
  obtain ⟨Z, hZ, a, ha, hfac⟩ := hm
  obtain rfl : Z = Y := by
    cases Z
    cases Y
    cases hZ
    rfl
  have hfac' : a = g := by
    apply (SmallZariski.inclusion B T.obj T.property).map_injective
    simpa using hfac
  simpa [hfac'] using ha

/-- The precoverage of the small Zariski category of `T` is the precoverage of the big Zariski
category over `T` comapped along the full inclusion. -/
public theorem smallZariski_precoverage_eq_comap
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (T : B.Schemes) :
    SmallZariski.precoverage B T.obj T.property =
      (BigZariskiOver.precoverage B T.obj T.property).comap
        (SmallZariski.inclusion B T.obj T.property) := by
  ext X R
  rw [SmallZariski.mem_precoverage_iff, Precoverage.mem_comap_iff,
    BigZariskiOver.mem_precoverage_iff]
  constructor
  · rintro ⟨E, rfl, hE⟩
    exact ⟨E.map (SmallZariski.inclusion B T.obj T.property),
      (PreZeroHypercover.presieve₀_map
        (F := SmallZariski.inclusion B T.obj T.property) E).symm, hE⟩
  · rintro ⟨E, hR, hE⟩
    change B.IsCovering _ at hE
    have hZ : AlgebraicGeometry.IsZariskiCovering
        ⟨(BigZariskiOver.inclusion B T.obj T.property).obj X.obj,
          E.map (BigZariskiOver.inclusion B T.obj T.property)⟩ := hE.1
    change (E.map (BigZariskiOver.toScheme B T.obj T.property)).presieve₀ ∈
      Scheme.zariskiPretopology
        ((BigZariskiOver.toScheme B T.obj T.property).obj X.obj) at hZ
    have hOpen (i : E.I₀) :
        IsOpenImmersion ((BigZariskiOver.toScheme B T.obj T.property).map (E.f i)) :=
      hZ.2 ((E.map (BigZariskiOver.toScheme B T.obj T.property)).presieve₀_f i)
    let E' : PreZeroHypercover.{u + 1} X :=
      ⟨E.I₀, fun i => ⟨E.X i, by
        show IsOpenImmersion (B.inclusion.map (E.X i).hom)
        have hcomp :
            (BigZariskiOver.toScheme B T.obj T.property).map (E.f i) ≫
              B.inclusion.map X.obj.hom = B.inclusion.map (E.X i).hom := by
          show B.inclusion.map ((E.f i).left ≫ X.obj.hom) =
            B.inclusion.map (E.X i).hom
          exact congrArg B.inclusion.map (Over.w (E.f i))
        rw [← hcomp]
        have : IsOpenImmersion
            ((BigZariskiOver.toScheme B T.obj T.property).map (E.f i)) := hOpen i
        have : IsOpenImmersion (B.inclusion.map X.obj.hom) := X.property
        infer_instance⟩,
       fun i => CategoryTheory.ObjectProperty.homMk (E.f i)⟩
    have hmap : E'.map (SmallZariski.inclusion B T.obj T.property) = E := by
      cases E
      rfl
    refine ⟨E', eq_presieve₀_of_map_eq _ smallZariski_presieve_map_injective hmap hR, ?_⟩
    show B.IsCovering
      ⟨(Over.forget (⟨T.obj, T.property⟩ : B.Schemes)).obj X.obj,
        (E'.map (SmallZariski.inclusion B T.obj T.property)).map
          (Over.forget (⟨T.obj, T.property⟩ : B.Schemes))⟩
    change B.IsCovering
      ⟨(Over.forget (⟨T.obj, T.property⟩ : B.Schemes)).obj X.obj,
        E.map (BigZariskiOver.inclusion B T.obj T.property)⟩ at hE
    simpa [hmap] using hE

/-- The precoverage of the small Zariski category of `T` is stable under base change. -/
public instance smallZariski_precoverage_stableUnderBaseChange
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (T : B.Schemes) :
    (SmallZariski.precoverage B T.obj T.property).IsStableUnderBaseChange := by
  rw [smallZariski_precoverage_eq_comap B T]
  have : PreservesLimitsOfShape WalkingCospan
      (SmallZariski.inclusion B T.obj T.property) := inferInstance
  infer_instance

end AlgebraicGeometry
