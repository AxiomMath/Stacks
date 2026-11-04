module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral

/-!
# The étale topos of a thickening of algebraic spaces

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, that is a closed subspace
whose inclusion is surjective on points. Base change of étale scheme charts along the inclusion
exhibits the small étale site of `X` as a *dense subsite* of the small étale site of `G`, and
therefore induces an equivalence between the two categories of sheaves. Through the comparison
of Stacks 03G1 between scheme charts and algebraic spaces étale over a given space, the same
equivalence holds for the spaces-étale sites: the sheaf topos of `X` and the sheaf topos of its
thickening `G` are canonically equivalent.

## Main definitions

* `AlgebraicGeometry.Space.thickeningChartBaseChange`: base change of étale scheme charts along
  the inclusion of a thickening.
* `AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` and
  `AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`: **Stacks 05ZM**, the induced
  equivalence of the sheaf topoi, on scheme charts and on the spaces-étale sites.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`: a sieve of the small
  étale site of a presheaf is covering exactly when every point of the scheme underlying the
  chart lies in the image of one of its arrows.
* `AlgebraicGeometry.Space.surjective_projection_of_isThickening`: the cartesian projection
  from the base change of an étale scheme chart along the inclusion of a thickening is
  surjective.
* `AlgebraicGeometry.Space.thickeningChartBaseChange_faithful`: base change of étale scheme
  charts along the inclusion of a thickening is faithful.
* `AlgebraicGeometry.Space.functorPushforward_mem_smallEtaleTopology_iff_of_isThickening`: it
  both preserves and reflects covering sieves.
* `AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`: it exhibits the small
  étale site of the ambient space as a dense subsite of the small étale site of the thickening.
* `AlgebraicGeometry.Space.thickeningChartBaseChange_isCocontinuous`: it is cocontinuous, so
  together with the previous result it is a special cocontinuous functor in the sense of
  `IsSpecialCocontinuous`, Stacks 03CG.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A pointwise criterion for the covering sieves of the small étale site -/

/-- **A sieve of the small étale site is covering exactly when its arrows are jointly
surjective on points.** For a sieve of an étale chart `A` of a presheaf `F` on the big fppf
site of `S`, being a covering sieve is equivalent to every point of the scheme underlying `A`
being in the image of the scheme morphism underlying one of the arrows of the sieve. -/
theorem SmallEtale.mem_topology_iff_exists_mem_range
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {A : SmallEtale B S hS F} (T : Sieve A) :
    T ∈ SmallEtale.topology B S hS F A ↔
      ∀ x : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj A),
        ∃ (V : SmallEtale B S hS F) (g : V ⟶ A), T.arrows g ∧
          x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS F).map g)) := by
  classical
  constructor
  · intro hT x
    obtain ⟨R, hR, hRT⟩ := (SmallEtale.mem_topology_iff B S hS F).1 hT
    obtain ⟨E, rfl, hE⟩ := (SmallEtale.mem_precoverage_iff B S hS F).1 hR
    have hEet : Presieve.ofArrows
        (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (E.X i)))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map (E.f i))) ∈
        Scheme.etalePrecoverage
          ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj A)) := by
      have h := hE.2
      rwa [IsEtaleCovering, PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀,
        Presieve.map_ofArrows] at h
    obtain ⟨i, hi⟩ := (Scheme.ofArrows_mem_etalePrecoverage_iff.1 hEet).1 x
    exact ⟨E.X i, E.f i, hRT _ _ (Presieve.ofArrows.mk i), hi⟩
  · intro hT
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      (SmallEtale.ofArrows_mem_topology B S hS F
        (fun i : Σ V : SmallEtale B S hS F, {g : V ⟶ A // T.arrows g} ↦ i.1)
        (fun i ↦ i.2.1) ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro V g ⟨i⟩
      exact i.2.2
    · rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
      refine ⟨fun x ↦ ?_, fun i ↦ etale_toScheme_toOver_map B S hS F i.2.1⟩
      obtain ⟨V, g, hg, hx⟩ := hT x
      exact ⟨⟨V, ⟨g, hg⟩⟩, hx⟩

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-! ### The inclusion of a thickening, and base change of scheme charts along it -/

/-- The inclusion of a thickening `G ⊂ X` is a closed immersion. -/
theorem isClosedImmersion_inclusion_of_isThickening (hG : IsThickening B S hS X G) :
    IsClosedImmersion B S hS (IsThickening.inclusion B S hS hG).hom :=
  hG.1.2

/-- **Base change of étale scheme charts along the inclusion of a thickening.** This is
`AlgebraicGeometry.Space.smallBaseChange`, Stacks 03G2 part (4), at the inclusion of a
thickening `G ⊂ X`, which is representable because it is a closed immersion. -/
noncomputable abbrev thickeningChartBaseChange (hG : IsThickening B S hS X G) :
    SmallEtale B S hS X.1 ⥤ SmallEtale B S hS (IsThickening.space B S hS hG).1 :=
  smallBaseChange B S hS (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep

/-- The inclusion of a thickening is surjective after every base change along a scheme
chart. -/
theorem presheafSurjective_inclusion_of_isThickening (hG : IsThickening B S hS X G) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (IsThickening.inclusion B S hS hG).hom :=
  (surjective_iff_pointsMap_surjective B S hS hG.1.1 X.property G.ι
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep).2 hG.2

/-- **The cartesian projection from a base-changed chart is surjective.** For a thickening
`G ⊂ X` and an étale scheme chart `U` of `X`, the projection from the base change of `U` along
the inclusion back to `U` is a surjective morphism of schemes. -/
theorem surjective_projection_of_isThickening (hG : IsThickening B S hS X G)
    (U : SmallEtale B S hS X.1) :
    AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd U.1.hom)) :=
  (presheafSurjective_inclusion_of_isThickening B S hS hG).property_snd U.1.hom

/-! ### Faithfulness of chart base change along a thickening -/

/-- A morphism of étale charts commutes with the projections from the base changes along the
inclusion of a thickening. -/
private theorem thickeningChartBaseChange_map_snd (hG : IsThickening B S hS X G)
    {V W : SmallEtale B S hS X.1} (k : V ⟶ W) :
    ((thickeningChartBaseChange B S hS hG).map k).hom.left ≫
        (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd W.1.hom =
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom ≫ k.hom.left :=
  smallBaseChange_map_snd B S hS (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep k

/-- **Base change of étale scheme charts along the inclusion of a thickening is faithful.** A
morphism of étale scheme charts of `X` is determined by its base change along the inclusion of
a thickening of `X`. -/
theorem thickeningChartBaseChange_faithful (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).Faithful where
  map_injective {V W} k₁ k₂ e := by
    have hW := W.property.rep
    have hetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
        (hW.snd V.1.hom)) := W.property.property_snd V.1.hom
    have hcond : ∀ k : V ⟶ W, yoneda.map k.hom.left ≫ W.1.hom =
        yoneda.map (𝟙 V.1.left) ≫ V.1.hom := fun k ↦ by simp
    have hfst : ∀ k : V ⟶ W,
        hW.lift' k.hom.left (𝟙 V.1.left) (hcond k) ≫ hW.fst' V.1.hom = k.hom.left :=
      fun k ↦ hW.lift'_fst _ _ _
    have hsnd : ∀ k : V ⟶ W,
        hW.lift' k.hom.left (𝟙 V.1.left) (hcond k) ≫ hW.snd V.1.hom = 𝟙 V.1.left :=
      fun k ↦ hW.lift'_snd _ _ _
    have he : (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom ≫
          k₁.hom.left =
        (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom ≫
          k₂.hom.left := by
      rw [← thickeningChartBaseChange_map_snd B S hS hG k₁,
        ← thickeningChartBaseChange_map_snd B S hS hG k₂, e]
    have hcomm : (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom ≫
          hW.lift' k₁.hom.left (𝟙 V.1.left) (hcond k₁) =
        (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom ≫
          hW.lift' k₂.hom.left (𝟙 V.1.left) (hcond k₂) := by
      refine hW.hom_ext' ?_ ?_
      · rw [Category.assoc, Category.assoc, hfst k₁, hfst k₂]
        exact he
      · rw [Category.assoc, Category.assoc, hsnd k₁, hsnd k₂]
    have hsection : hW.lift' k₁.hom.left (𝟙 V.1.left) (hcond k₁) =
        hW.lift' k₂.hom.left (𝟙 V.1.left) (hcond k₂) := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      refine Stacks.Etale.hom_ext_of_surjective
        ((BigFppfOver.toScheme B S hS).map
          ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom))
        (surjective_projection_of_isThickening B S hS hG V).surj
        ((BigFppfOver.toScheme B S hS).map (hW.snd V.1.hom)) _ _ ?_ ?_
      · rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp, hsnd k₁, hsnd k₂]
      · rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp]
        exact congrArg (fun t ↦ (BigFppfOver.toScheme B S hS).map t) hcomm
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    rw [← hfst k₁, ← hfst k₂]
    exact congrArg (fun t ↦ t ≫ hW.fst' V.1.hom) hsection

/-! ### The covering criterion -/

/-- **Base change along the inclusion of a thickening neither creates nor destroys coverings.**
A sieve of an étale scheme chart `U` of `X` is covering for the small étale topology of `X`
exactly when the sieve it generates on the base change of `U` is covering for the small étale
topology of the thickening `G ⊂ X`. -/
theorem functorPushforward_mem_smallEtaleTopology_iff_of_isThickening
    (hG : IsThickening B S hS X G) (U : SmallEtale B S hS X.1) (R : Sieve U) :
    R.functorPushforward (thickeningChartBaseChange B S hS hG) ∈
        SmallEtale.topology B S hS (IsThickening.space B S hS hG).1
          ((thickeningChartBaseChange B S hS hG).obj U) ↔
      R ∈ SmallEtale.topology B S hS X.1 U := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range,
    SmallEtale.mem_topology_iff_exists_mem_range]
  constructor
  · intro h u
    obtain ⟨z, hz⟩ := (surjective_projection_of_isThickening B S hS hG U).surj u
    obtain ⟨W', m, ⟨V, g, k, hgR, hm⟩, w, hw⟩ := h z
    refine ⟨V, g, hgR, (BigFppfOver.toScheme B S hS).map (k.hom.left ≫
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom) w, ?_⟩
    have hmleft : m.hom.left =
        k.hom.left ≫ ((thickeningChartBaseChange B S hS hG).map g).hom.left :=
      congrArg (fun t : W' ⟶ (thickeningChartBaseChange B S hS hG).obj U ↦ t.hom.left) hm
    have hmor : (k.hom.left ≫
          (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.1.hom) ≫
          g.hom.left =
        m.hom.left ≫
          (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd U.1.hom := by
      rw [hmleft]
      exact (Category.assoc _ _ _).trans
        ((congrArg (k.hom.left ≫ ·) (thickeningChartBaseChange_map_snd B S hS hG g).symm).trans
          (Category.assoc _ _ _).symm)
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    refine (congrArg (fun t ↦ (BigFppfOver.toScheme B S hS).map t w) hmor).trans ?_
    erw [Functor.map_comp, Scheme.Hom.comp_apply, hw, hz]
  · intro h z
    obtain ⟨V, g, hgR, v, hvz⟩ := h ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd U.1.hom) z)
    obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
      (representablePullbackMap_isPullback_scheme B S hS (IsThickening.inclusion B S hS hG)
        (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep g) z v hvz.symm
    exact ⟨(thickeningChartBaseChange B S hS hG).obj V,
      (thickeningChartBaseChange B S hS hG).map g,
      Sieve.image_mem_functorPushforward _ R hgR, w, hw⟩

/-! ### The dense subsite and the equivalence of topoi -/

/-- **The small étale site of an algebraic space is a dense subsite of the small étale site of
any thickening of it.** Base change of étale scheme charts along the inclusion of a thickening
`G ⊂ X` is cover dense and locally fully faithful, and identifies the covering sieves of the
two small étale sites. -/
theorem thickeningChartBaseChange_isDenseSubsite (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).IsDenseSubsite
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) :=
  let := smallBaseChange_isCoverDense_of_isClosedImmersion B S hS
    (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG)
  let := smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS
    (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG)
  let := thickeningChartBaseChange_faithful B S hS hG
  { functorPushforward_mem_iff := fun {U R} ↦
      functorPushforward_mem_smallEtaleTopology_iff_of_isThickening B S hS hG U R }

/-- **Base change of étale scheme charts along the inclusion of a thickening is cocontinuous**:
a covering sieve of a base-changed chart pulls back to a covering sieve of the chart. -/
instance thickeningChartBaseChange_isCocontinuous (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).IsCocontinuous
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) :=
  letI := thickeningChartBaseChange_isDenseSubsite B S hS hG
  inferInstance

/-- The sheaves of sets on the small étale site of an algebraic space `X` and on the small
étale site of a thickening `G ⊂ X` of it are equivalent, by restriction along base change of
étale scheme charts: the equivalence of the comparison lemma for the dense subsite inclusion
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`. -/
noncomputable def smallEtaleSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) (Type (u + 1)) :=
  letI := thickeningChartBaseChange_isDenseSubsite B S hS hG
  Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (thickeningChartBaseChange B S hS hG) (Type (u + 1))

/-- **The equivalence of the spaces-étale sheaf topoi of a thickening.** For a thickening
`G ⊂ X` of algebraic spaces over `S`, the sheaves of sets on the spaces-étale site of `X` and
the sheaves of sets on the spaces-étale site of `G` are canonically equivalent.

The equivalence is the chart form
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` conjugated by the two comparison
equivalences of Stacks 03G1, `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`, which
identify the sheaves on the spaces-étale site of an algebraic space with the sheaves on its
small étale site of scheme charts. -/
@[stacks 05ZM "equivalence of the spaces-étale sheaf topoi"]
noncomputable def spacesEtaleSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ≌
      Sheaf (SpacesEtale.topology B S hS (IsThickening.space B S hS hG)) (Type (u + 1)) :=
  ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).asEquivalence.trans
    ((smallEtaleSheafEquiv_of_isThickening B S hS hG).trans
      ((comparisonFunctor B S hS (IsThickening.space B S hS hG)).sheafPushforwardContinuous
          (Type (u + 1))
          (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
          (SpacesEtale.topology B S hS
            (IsThickening.space B S hS hG))).asEquivalence.symm)

end AlgebraicGeometry.Space

end
