module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringOfHom
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI

/-!
# The site axioms for the precoverage of a big ph site

The covering families of a big ph site `B` are its chosen, size-bounded ph coverings, and the
precoverage `AlgebraicGeometry.BigPHSite.precoverage` consists of the presieves they present.
This file proves that this precoverage satisfies the site axioms in the form of Mathlib's
`CategoryTheory.Precoverage` classes: it contains the isomorphisms, it is stable under base
change and under composition, and the pullbacks it needs exist.

## Main results

* `AlgebraicGeometry.BigPHSite.mem_precoverage_iff_isPHCovering` — a family of the site
  presents a covering presieve exactly when its image in all schemes is a ph covering.
* The instances `BigPHSite.precoverage_hasIsos`, `BigPHSite.precoverage_isStableUnderBaseChange`
  and `BigPHSite.precoverage_isStableUnderComposition`.

## Implementation notes

Membership in the precoverage only asks that the presieve be presented by *some* chosen
covering. The bridge `mem_precoverage_iff_isPHCovering` removes the choice in both directions:
a chosen representative exists for every ph covering of the site (`covering_representative`,
whose combinatorial equivalence preserves the presieve), and conversely two families with the
same presieve refine each other, so being a ph covering is a property of the presieve
(`AlgebraicGeometry.IsPHCovering.of_hom`). The site axioms are then those of ph coverings of
schemes, Stacks 0DBI, transported along the inclusion of the site into all schemes, which
preserves fibre products.

## References

* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0DBJ](https://stacks.math.columbia.edu/tag/0DBJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.PreZeroHypercover

variable {C : Type*} [Category* C] {S : C}

/-- If every member of the family `E` is a member of the family `F`, then `E` refines `F`: the
refinement morphisms are the transports along the equalities of sources. -/
noncomputable def homOfPresieveLE {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{v} S}
    (h : E.presieve₀ ≤ F.presieve₀) : E.Hom F :=
  have H := fun i => Presieve.ofArrows_surj F.f (E.f i) (h _ _ (Presieve.ofArrows.mk i))
  { s₀ := fun i => (H i).choose
    h₀ := fun i => eqToHom (H i).choose_spec.choose.symm
    w₀ := fun i => (H i).choose_spec.choose_spec.symm }

/-- A refinement of families is carried by a functor to a refinement of the image families. -/
def Hom.map {D : Type*} [Category* D] (G : C ⥤ D) {E : PreZeroHypercover.{w} S}
    {F : PreZeroHypercover.{v} S} (φ : E.Hom F) : (E.map G).Hom (F.map G) where
  s₀ := φ.s₀
  h₀ i := G.map (φ.h₀ i)
  w₀ i := by
    change G.map (φ.h₀ i) ≫ G.map (F.f (φ.s₀ i)) = G.map (E.f i)
    rw [← G.map_comp]
    exact congrArg G.map (φ.w₀ i)

end CategoryTheory.PreZeroHypercover

namespace AlgebraicGeometry

namespace BigPHSite

variable (B : BigPHSite.{u})

/-- **The covering presieves of a big ph site are the presieves of its ph coverings.** A family
`E` of the site presents a presieve of `B.precoverage` exactly when its image in all schemes is
a ph covering. -/
public theorem mem_precoverage_iff_isPHCovering {T : B.Schemes}
    (E : PreZeroHypercover.{u + 1} T) :
    E.presieve₀ ∈ B.precoverage T ↔
      IsPHCovering (E.map B.inclusion).X (E.map B.inclusion).f := by
  constructor
  · rintro ⟨E', hR, hE'⟩
    have hE'ph : IsPHCovering (E'.map B.inclusion).X (E'.map B.inclusion).f := hE'.1
    refine hE'ph.of_hom
      (PreZeroHypercover.Hom.map B.inclusion (PreZeroHypercover.homOfPresieveLE hR.symm.le))
      fun i => ?_
    let φ := PreZeroHypercover.homOfPresieveLE hR.le
    have hlft : LocallyOfFiniteType (B.inclusion.map (E'.f (φ.s₀ i))) := hE'ph.1 (φ.s₀ i)
    change LocallyOfFiniteType (B.inclusion.map (E.f i))
    have : IsIso (B.inclusion.map (φ.h₀ i)) := by
      dsimp [φ, PreZeroHypercover.homOfPresieveLE]
      infer_instance
    rw [← φ.w₀ i, Functor.map_comp]
    infer_instance
  · intro h
    obtain ⟨⟨Vbase, Vfam⟩, hV, hT, hcomb⟩ := B.covering_representative ⟨T, E⟩ h
    obtain rfl : T = Vbase := hT
    exact ⟨Vfam, PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb, hV⟩

/-- The underlying category of a big ph site has fibre products: it is the underlying category of
the associated big étale site. -/
public instance hasPullbacks_schemes : HasPullbacks B.Schemes :=
  hasPullbacks_bigEtaleSite (phAssociatedBigEtaleSite B)

/-- The inclusion of a big ph site into all schemes preserves fibre products. -/
public instance preservesPullbacks_inclusion :
    PreservesLimitsOfShape WalkingCospan B.inclusion :=
  preservesPullbacks_bigEtaleSiteInclusion (phAssociatedBigEtaleSite B)

/-- **Stacks 0DBI (1), on a big ph site.** The precoverage of a big ph site contains the
isomorphisms. -/
public instance precoverage_hasIsos : B.precoverage.HasIsos := by
  constructor
  intro U V g hg
  refine ⟨PreZeroHypercover.singleton g, ?_, B.coverings_isSite.1 g⟩
  simp

/-- **Stacks 0DBI (3), on a big ph site.** The precoverage of a big ph site is stable under base
change. -/
public instance precoverage_isStableUnderBaseChange : B.precoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h := by
    let E : PreZeroHypercover.{u + 1} S := ⟨ι, X, f⟩
    let F : PreZeroHypercover.{u + 1} Y := ⟨ι, P, p₁⟩
    have hE : IsPHCovering (E.map B.inclusion).X (E.map B.inclusion).f :=
      (B.mem_precoverage_iff_isPHCovering E).1 hf
    refine (B.mem_precoverage_iff_isPHCovering F).2 ?_
    have hpb := isPHCovering_pullback hE (B.inclusion.map g)
    have hsq : ∀ i, IsPullback (B.inclusion.map (p₂ i)) (B.inclusion.map (p₁ i))
        (B.inclusion.map (f i)) (B.inclusion.map g) :=
      fun i => ((h i).map B.inclusion).flip
    let φ : PreZeroHypercover.Hom
        ⟨ι, fun i => pullback (B.inclusion.map (f i)) (B.inclusion.map g),
          fun i => pullback.snd (B.inclusion.map (f i)) (B.inclusion.map g)⟩
        (F.map B.inclusion) :=
      { s₀ := id
        h₀ := fun i => (hsq i).isoPullback.inv
        w₀ := fun i => (hsq i).isoPullback_inv_snd }
    refine hpb.of_hom φ fun i => ?_
    change LocallyOfFiniteType (B.inclusion.map (p₁ i))
    exact MorphismProperty.of_isPullback (hsq i) (hE.1 i)

/-- **Stacks 0DBI (2), on a big ph site.** The precoverage of a big ph site is stable under
composition. -/
public instance precoverage_isStableUnderComposition :
    B.precoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    let E : PreZeroHypercover.{u + 1} S := ⟨ι, X, f⟩
    let F : ∀ i, PreZeroHypercover.{u + 1} (X i) := fun i => ⟨σ i, Y i, g i⟩
    have hE : IsPHCovering (E.map B.inclusion).X (E.map B.inclusion).f :=
      (B.mem_precoverage_iff_isPHCovering E).1 hf
    have hF : ∀ i, IsPHCovering ((F i).map B.inclusion).X ((F i).map B.inclusion).f :=
      fun i => (B.mem_precoverage_iff_isPHCovering (F i)).1 (hg i)
    have hbind := isPHCovering_bind (E.map B.inclusion) hE (fun i => (F i).map B.inclusion) hF
    change (E.bind F).presieve₀ ∈ B.precoverage S
    refine (B.mem_precoverage_iff_isPHCovering (E.bind F)).2 (hbind.of_hom ?_ fun p => ?_)
    · exact
        { s₀ := id
          h₀ := fun _ => 𝟙 _
          w₀ := fun p => by
            change 𝟙 _ ≫ B.inclusion.map (g p.1 p.2 ≫ f p.1) =
              B.inclusion.map (g p.1 p.2) ≫ B.inclusion.map (f p.1)
            rw [Category.id_comp, Functor.map_comp] }
    · have h₁ : LocallyOfFiniteType (B.inclusion.map (f p.1)) := hE.1 p.1
      have h₂ : LocallyOfFiniteType (B.inclusion.map (g p.1 p.2)) := (hF p.1).1 p.2
      change LocallyOfFiniteType (B.inclusion.map (g p.1 p.2 ≫ f p.1))
      rw [Functor.map_comp]
      infer_instance

end BigPHSite

end AlgebraicGeometry

end
