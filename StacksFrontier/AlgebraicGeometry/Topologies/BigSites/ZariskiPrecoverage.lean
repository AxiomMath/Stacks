module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits

/-!
# The Zariski covering families as a comap of the Zariski pretopology

The distinguished covering families of a big Zariski site, of its slice over a scheme `S`, and
of the small Zariski site of `S` are in each case exactly the families whose image in schemes
is a Zariski covering. Each of those precoverages is therefore the preimage — the `comap` — of
Mathlib's Zariski pretopology along the relevant functor, and the standard stability
properties of Zariski coverings transfer to them.

## Main results

* `AlgebraicGeometry.BigZariskiSite.precoverage_eq_comap`,
  `AlgebraicGeometry.BigZariskiOver.precoverage_eq_comap` and
  `AlgebraicGeometry.SmallZariski.precoverage_eq_comap` present the three precoverages as
  preimages.
* The `precoverage_hasIsos`, `precoverage_isStableUnderBaseChange` and
  `precoverage_isStableUnderComposition` instances record the resulting stability properties.
* `AlgebraicGeometry.BigZariskiOver.topology_eq_over` identifies the topology of the slice
  with the localization of the ambient topology.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The distinguished covering families of a big Zariski site are exactly those whose image in
schemes is a Zariski covering: the site's precoverage is the preimage of Mathlib's Zariski
pretopology along the inclusion. -/
public theorem BigZariskiSite.precoverage_eq_comap (B : BigZariskiSite.{u}) :
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
      exact propext ⟨fun ⟨i⟩ => i.2, fun hg => Presieve.ofArrows.mk (⟨⟨Y, g⟩, hg⟩ : R.uncurry)⟩
    have hZ : IsZariskiCovering ⟨X, E⟩ := by
      show (E.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology _
      rw [PreZeroHypercover.presieve₀_map, hE]
      exact hR
    obtain ⟨E', hE', hXE, hcomb⟩ := B.covering_representative ⟨X, E⟩ hZ
    cases hXE
    exact ⟨E'.2, hE', hE.symm.trans
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb)⟩

/-- The precoverage of the big Zariski site over `S` is the preimage of the precoverage of the
ambient site along the forgetful functor of the slice. -/
public theorem BigZariskiOver.precoverage_eq_comap
    (B : BigZariskiSite.{u}) (S : B.Schemes) :
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
    have hpresieve : R.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)) =
        E'.presieve₀.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)) := by
      rw [hR, ← hmap, ← PreZeroHypercover.presieve₀_map]
    have hR' : R = E'.presieve₀ := (Presieve.overEquiv U).injective hpresieve
    refine ⟨E', hR', ?_⟩
    show B.IsCovering
      ⟨(Over.forget (⟨S.obj, S.property⟩ : B.Schemes)).obj U,
        (E'.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)))⟩
    simpa [BigZariskiOver.IsCovering, hmap] using hE

/-- A singleton isomorphism is a distinguished covering family of a big Zariski site. -/
public instance BigZariskiSite.precoverage_hasIsos (B : BigZariskiSite.{u}) :
    B.precoverage.HasIsos := by
  constructor
  intro U V g hg
  change ∃ E : PreZeroHypercover V, B.IsCovering ⟨V, E⟩ ∧
      Presieve.singleton g = E.presieve₀
  refine ⟨PreZeroHypercover.singleton g, B.coverings_isSite.1 g, ?_⟩
  simp

/-- Zariski coverings of schemes are stable under composition. -/
public lemma Scheme.zariskiPrecoverage_isStableUnderComposition :
    (Scheme.zariskiPrecoverage : Precoverage Scheme.{u}).IsStableUnderComposition := by
  let : MorphismProperty.IsStableUnderComposition
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  unfold Scheme.zariskiPrecoverage Scheme.precoverage
  infer_instance

/-- Zariski coverings of schemes are stable under base change. -/
public lemma Scheme.zariskiPrecoverage_isStableUnderBaseChange :
    (Scheme.zariskiPrecoverage : Precoverage Scheme.{u}).IsStableUnderBaseChange := by
  let : Scheme.IsJointlySurjectivePreserving
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  let : MorphismProperty.IsStableUnderBaseChange
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) := inferInstance
  unfold Scheme.zariskiPrecoverage Scheme.precoverage
  infer_instance

/-- The distinguished covering families of a big Zariski site are stable under base change. -/
public instance BigZariskiSite.precoverage_isStableUnderBaseChange
    (B : BigZariskiSite.{u}) : B.precoverage.IsStableUnderBaseChange := by
  let : Scheme.zariskiPretopology.toPrecoverage.IsStableUnderBaseChange :=
    Scheme.zariskiPrecoverage_isStableUnderBaseChange.{u}
  let : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigZariskiSiteInclusion B
  rw [BigZariskiSite.precoverage_eq_comap B]
  infer_instance

/-- The distinguished covering families of a big Zariski site are stable under composition. -/
public instance BigZariskiSite.precoverage_isStableUnderComposition
    (B : BigZariskiSite.{u}) : B.precoverage.IsStableUnderComposition := by
  let : MorphismProperty.IsStableUnderComposition
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  let : Scheme.zariskiPretopology.toPrecoverage.IsStableUnderComposition :=
    Scheme.zariskiPrecoverage_isStableUnderComposition.{u}
  rw [BigZariskiSite.precoverage_eq_comap B]
  infer_instance

/-- A singleton isomorphism covers in the big Zariski site over `S`. -/
public instance BigZariskiOver.precoverage_hasIsos
    (B : BigZariskiSite.{u}) (S : B.Schemes) :
    (BigZariskiOver.precoverage B S.obj S.property).HasIsos := by
  rw [BigZariskiOver.precoverage_eq_comap B S]
  infer_instance

/-- Coverings of the big Zariski site over `S` are stable under base change. -/
public instance BigZariskiOver.precoverage_isStableUnderBaseChange
    (B : BigZariskiSite.{u}) (S : B.Schemes) :
    (BigZariskiOver.precoverage B S.obj S.property).IsStableUnderBaseChange := by
  let : B.precoverage.IsStableUnderBaseChange :=
    BigZariskiSite.precoverage_isStableUnderBaseChange B
  rw [BigZariskiOver.precoverage_eq_comap B S]
  infer_instance

/-- Coverings of the big Zariski site over `S` are stable under composition. -/
public instance BigZariskiOver.precoverage_isStableUnderComposition
    (B : BigZariskiSite.{u}) (S : B.Schemes) :
    (BigZariskiOver.precoverage B S.obj S.property).IsStableUnderComposition := by
  let : B.precoverage.IsStableUnderComposition :=
    BigZariskiSite.precoverage_isStableUnderComposition B
  let : Scheme.zariskiPretopology.toPrecoverage.IsStableUnderComposition :=
    Scheme.zariskiPrecoverage_isStableUnderComposition.{u}
  rw [BigZariskiOver.precoverage_eq_comap B S, BigZariskiSite.precoverage_eq_comap B,
    ← Precoverage.comap_comp]
  infer_instance

/-- The inclusion of the small Zariski site into the big Zariski site over `S` is injective on
presieves. -/
public theorem SmallZariski.presieve_map_injective
    {B : BigZariskiSite.{u}} {T : B.Schemes}
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
  have hZY : Z = Y := by
    cases Z
    cases Y
    cases hZ
    rfl
  cases hZY
  have hfac' : a = g := by
    apply (SmallZariski.inclusion B T.obj T.property).map_injective
    simpa using hfac
  simpa [hfac'] using ha

/-- The precoverage of the small Zariski site of `S` is the preimage of the precoverage of the
big Zariski site over `S` along the full inclusion. -/
public theorem SmallZariski.precoverage_eq_comap
    (B : BigZariskiSite.{u}) (T : B.Schemes) :
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
    have hZ : IsZariskiCovering
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
        let : IsOpenImmersion
            ((BigZariskiOver.toScheme B T.obj T.property).map (E.f i)) := hOpen i
        let : IsOpenImmersion (B.inclusion.map X.obj.hom) := X.property
        infer_instance⟩,
       fun i => CategoryTheory.ObjectProperty.homMk (E.f i)⟩
    have hmap : E'.map (SmallZariski.inclusion B T.obj T.property) = E := by
      cases E
      rfl
    have hpresieve :
        E'.presieve₀.map (SmallZariski.inclusion B T.obj T.property) = E.presieve₀ := by
      rw [← PreZeroHypercover.presieve₀_map, hmap]
    have hR' : R = E'.presieve₀ := SmallZariski.presieve_map_injective (hR.trans hpresieve.symm)
    refine ⟨E', hR', ?_⟩
    show B.IsCovering
      ⟨(Over.forget (⟨T.obj, T.property⟩ : B.Schemes)).obj X.obj,
        (E'.map (SmallZariski.inclusion B T.obj T.property)).map
          (Over.forget (⟨T.obj, T.property⟩ : B.Schemes))⟩
    change B.IsCovering
      ⟨(Over.forget (⟨T.obj, T.property⟩ : B.Schemes)).obj X.obj,
        E.map (BigZariskiOver.inclusion B T.obj T.property)⟩ at hE
    simpa [hmap] using hE

/-- Coverings of the small Zariski site of `S` are stable under base change. -/
public instance SmallZariski.precoverage_isStableUnderBaseChange
    (B : BigZariskiSite.{u}) (T : B.Schemes) :
    (SmallZariski.precoverage B T.obj T.property).IsStableUnderBaseChange := by
  rw [SmallZariski.precoverage_eq_comap B T]
  let : PreservesLimitsOfShape WalkingCospan
      (SmallZariski.inclusion B T.obj T.property) :=
    preservesPullbacks_smallZariskiInclusion B T.obj T.property
  infer_instance

/-- The topology of the big Zariski site over `S` is the localization at `S` of the topology
of the ambient big Zariski site. -/
public theorem BigZariskiOver.topology_eq_over (B : BigZariskiSite.{u}) (S : B.Schemes) :
    BigZariskiOver.topology B S.obj S.property = B.grothendieckTopology.over S := by
  rw [BigZariskiOver.topology, BigZariskiOver.precoverage_eq_comap B S,
    ← CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget]
  rfl

end AlgebraicGeometry
