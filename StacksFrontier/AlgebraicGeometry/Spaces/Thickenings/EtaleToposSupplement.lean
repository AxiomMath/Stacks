module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Additions to `EtaleTopos`

Further declarations about the module above, kept in their own module so that the base file is
unchanged.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

section Morphism

variable {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z')
    (hci : IsClosedImmersion B S hS i.hom)

/-- **Base change of étale scheme charts along a surjective closed immersion is faithful.**
A morphism of étale scheme charts of `Z'` is determined by its base change along a closed
immersion `i : Z ⟶ Z'` which is surjective.

This is `AlgebraicGeometry.Space.thickeningChartBaseChange_faithful` with the thickening
hypothesis replaced by the two consequences of it the argument uses: `i` is a closed
immersion, so that base change of charts along it is defined, and `i` is surjective, so that
the base change of `i` along a chart is a surjective morphism of schemes.

A morphism `k : V ⟶ W` of charts is the same datum as a section of the projection
`V ×_{Z'} W ⟶ V` of the chosen representable fibre product, and that projection is étale
because `W` is an étale chart. The base change of `i` along `V` is surjective, so two
sections which agree on it agree, by `Stacks.Etale.hom_ext_of_surjective`; and two morphisms
of charts with the same base change do agree on it, by
`AlgebraicGeometry.Space.smallBaseChange_map_snd`. -/
theorem smallBaseChange_faithful_of_surjective
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    (smallBaseChange B S hS i hci.rep).Faithful where
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
    have he : hci.rep.snd V.1.hom ≫ k₁.hom.left = hci.rep.snd V.1.hom ≫ k₂.hom.left := by
      rw [← smallBaseChange_map_snd B S hS i hci.rep k₁,
        ← smallBaseChange_map_snd B S hS i hci.rep k₂, e]
    have hcomm : hci.rep.snd V.1.hom ≫ hW.lift' k₁.hom.left (𝟙 V.1.left) (hcond k₁) =
        hci.rep.snd V.1.hom ≫ hW.lift' k₂.hom.left (𝟙 V.1.left) (hcond k₂) := by
      refine hW.hom_ext' ?_ ?_
      · rwa [Category.assoc, Category.assoc, hfst k₁, hfst k₂]
      · rw [Category.assoc, Category.assoc, hsnd k₁, hsnd k₂]
    have hsection : hW.lift' k₁.hom.left (𝟙 V.1.left) (hcond k₁) =
        hW.lift' k₂.hom.left (𝟙 V.1.left) (hcond k₂) := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      refine Stacks.Etale.hom_ext_of_surjective
        ((BigFppfOver.toScheme B S hS).map
          (hci.rep.snd V.1.hom))
        (hsurj.property_snd V.1.hom).surj
        ((BigFppfOver.toScheme B S hS).map (hW.snd V.1.hom)) _ _ ?_ ?_
      · rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp, hsnd k₁, hsnd k₂]
      · rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp, hcomm]
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    rw [← hfst k₁, ← hfst k₂]
    exact congrArg (· ≫ hW.fst' V.1.hom) hsection

/-- **Base change along a surjective closed immersion neither creates nor destroys
coverings.** A sieve of an étale scheme chart `U` of `Z'` is covering for the small étale
topology of `Z'` exactly when the sieve it generates on the base change of `U` is covering
for the small étale topology of `Z`.

This is `AlgebraicGeometry.Space.functorPushforward_mem_smallEtaleTopology_iff_of_isThickening`
at a closed immersion which is surjective, which is all its proof uses of a thickening.

Both directions are read off the pointwise criterion
`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`. Reflecting a covering
transports a point along the surjective cartesian projection at `U` and factors the arrow of
the image sieve through a base change, using
`AlgebraicGeometry.Space.smallBaseChange_map_snd`. Preserving one lifts a point along the
cartesian square `AlgebraicGeometry.Space.representablePullbackMap_isPullback_scheme` which
exhibits the base change of a morphism of charts as a fibre product.

This is the condition `CategoryTheory.Functor.IsDenseSubsite.functorPushforward_mem_iff`. -/
theorem functorPushforward_mem_smallEtaleTopology_iff_of_surjective
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    (U : SmallEtale B S hS Z'.1) (R : Sieve U) :
    R.functorPushforward (smallBaseChange B S hS i hci.rep) ∈
        SmallEtale.topology B S hS Z.1
          ((smallBaseChange B S hS i hci.rep).obj U) ↔
      R ∈ SmallEtale.topology B S hS Z'.1 U := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range,
    SmallEtale.mem_topology_iff_exists_mem_range]
  have hcomp : ∀ {A₁ A₂ A₃ : BigFppfOver B S hS} (p : A₁ ⟶ A₂) (q : A₂ ⟶ A₃)
      (y : (BigFppfOver.toScheme B S hS).obj A₁),
      (BigFppfOver.toScheme B S hS).map (p ≫ q) y =
        (BigFppfOver.toScheme B S hS).map q ((BigFppfOver.toScheme B S hS).map p y) := by
    intro A₁ A₂ A₃ p q y
    rw [(BigFppfOver.toScheme B S hS).map_comp, Scheme.Hom.comp_apply]
  constructor
  · intro h u
    obtain ⟨z, hz⟩ := (hsurj.property_snd U.1.hom).surj u
    obtain ⟨W', m, ⟨V, g, k, hgR, hm⟩, w, hw⟩ := h z
    refine ⟨V, g, hgR,
      (BigFppfOver.toScheme B S hS).map (k.hom.left ≫ hci.rep.snd V.1.hom) w, ?_⟩
    have hmleft : m.hom.left =
        k.hom.left ≫ ((smallBaseChange B S hS i hci.rep).map g).hom.left :=
      congrArg (fun t : W' ⟶ (smallBaseChange B S hS i hci.rep).obj U ↦ t.hom.left) hm
    have hmor : (k.hom.left ≫ hci.rep.snd V.1.hom) ≫ g.hom.left =
        m.hom.left ≫ hci.rep.snd U.1.hom :=
      calc (k.hom.left ≫ hci.rep.snd V.1.hom) ≫ g.hom.left
          = k.hom.left ≫ (hci.rep.snd V.1.hom ≫ g.hom.left) := Category.assoc _ _ _
        _ = k.hom.left ≫ (((smallBaseChange B S hS i hci.rep).map g).hom.left ≫
              hci.rep.snd U.1.hom) :=
            congrArg (k.hom.left ≫ ·) (smallBaseChange_map_snd B S hS i hci.rep g).symm
        _ = m.hom.left ≫ hci.rep.snd U.1.hom :=
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ hci.rep.snd U.1.hom) hmleft.symm)
    calc (BigFppfOver.toScheme B S hS).map g.hom.left
          ((BigFppfOver.toScheme B S hS).map (k.hom.left ≫ hci.rep.snd V.1.hom) w)
        = (BigFppfOver.toScheme B S hS).map (m.hom.left ≫ hci.rep.snd U.1.hom) w :=
          (hcomp _ _ w).symm.trans (congrArg (fun t ↦ (BigFppfOver.toScheme B S hS).map t w) hmor)
      _ = u := (hcomp _ _ w).trans ((congrArg (fun t ↦
          (BigFppfOver.toScheme B S hS).map (hci.rep.snd U.1.hom) t) hw).trans hz)
  · intro h z
    obtain ⟨V, g, hgR, v, hvz⟩ := h ((BigFppfOver.toScheme B S hS).map
      (hci.rep.snd U.1.hom) z)
    obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
      (representablePullbackMap_isPullback_scheme B S hS i
        hci.rep g) z v hvz.symm
    exact ⟨(smallBaseChange B S hS i hci.rep).obj V,
      (smallBaseChange B S hS i hci.rep).map g,
      Sieve.image_mem_functorPushforward _ R hgR, w, hw⟩

/-- **The small étale site of an algebraic space is a dense subsite of the small étale site
of the source of any surjective closed immersion into it.** Base change of étale scheme
charts along a closed immersion `i : Z ⟶ Z'` which is surjective is cover dense and locally
fully faithful, and identifies the covering sieves of the two small étale sites.

Cover density and local fullness are the content of Stacks 04E5 for an arbitrary closed
immersion, `AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isClosedImmersion` and
`AlgebraicGeometry.Space.smallBaseChange_isLocallyFull_of_isClosedImmersion`. Local
faithfulness follows from `AlgebraicGeometry.Space.smallBaseChange_faithful_of_surjective`,
and the covering condition is
`AlgebraicGeometry.Space.functorPushforward_mem_smallEtaleTopology_iff_of_surjective`; both
of the latter two use the surjectivity of `i`. -/
theorem smallBaseChange_isDenseSubsite_of_surjective
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    (smallBaseChange B S hS i hci.rep).IsDenseSubsite
      (SmallEtale.topology B S hS Z'.1) (SmallEtale.topology B S hS Z.1) :=
  have := smallBaseChange_isCoverDense_of_isClosedImmersion B S hS i hci
  have := smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS i hci
  have := smallBaseChange_faithful_of_surjective B S hS i hci hsurj
  { functorPushforward_mem_iff := fun {U R} ↦
      functorPushforward_mem_smallEtaleTopology_iff_of_surjective B S hS i hci hsurj U R }

end Morphism

end AlgebraicGeometry.Space

end

