module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleAbelianSheafEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules

/-!
# The étale topos of a thickening morphism of algebraic spaces

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` in the morphism form
(`AlgebraicGeometry.Space.IsThickeningHom`): an isomorphism of `X` onto a thickening subspace of
`X'`, for instance the morphism `X₀ ⟶ X_V` of base changes along `Spec k ⟶ Spec k[V]` in the
proof of Stacks 0DLL. Base change of étale scheme charts along `i`
(`AlgebraicGeometry.Space.smallBaseChange`) exhibits the small étale site of `X'` as a dense
subsite of the small étale site of `X`. This is
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite` with the inclusion of the
subspace replaced by `i` itself, so that no transport along the isomorphism of `X` with its range
is needed: the two proofs only use that `i` is a closed immersion which is surjective after every
base change along a scheme chart.

The Comparison Lemma then makes restriction of sheaves along chart base change an equivalence,
with values in abelian groups and in rings, and hence restriction of sheaves of modules over any
sheaf of rings `R` on `X` an equivalence onto sheaves of modules over the restricted ring on `X'`
(`AlgebraicGeometry.Space.thickeningHomModuleEquivalence`).

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_isDenseSubsite_of_isThickeningHom`: base change of
  étale scheme charts along a thickening is a dense subsite inclusion.
* `AlgebraicGeometry.Space.thickeningHomModuleEquivalence`: the equivalence of sheaves of modules.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}

/-- **The cartesian projection from a chart base changed along a thickening is surjective.** For
a thickening `i : X ⟶ X'` and an étale scheme chart `U` of `X'`, the projection
`U ×_{X'} X ⟶ U` is a surjective morphism of schemes, being a base change of `i`. -/
theorem surjective_projection_of_isThickeningHom (hi : IsThickeningHom B S hS i)
    (U : SmallEtale B S hS X'.1) :
    AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
      (hi.isClosedImmersion.rep.snd U.1.hom)) :=
  hi.surjective.property_snd U.1.hom

/-- **Base change of étale scheme charts along a thickening is faithful.** This is
`AlgebraicGeometry.Space.thickeningChartBaseChange_faithful` for a thickening in the morphism
form, with the same proof: a morphism of charts is a section of an étale projection, and two
sections agreeing after the surjective base change agree. -/
theorem smallBaseChange_faithful_of_isThickeningHom (hi : IsThickeningHom B S hS i) :
    (smallBaseChange B S hS i hi.isClosedImmersion.rep).Faithful where
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
    have he : hi.isClosedImmersion.rep.snd V.1.hom ≫ k₁.hom.left =
        hi.isClosedImmersion.rep.snd V.1.hom ≫ k₂.hom.left := by
      rw [← smallBaseChange_map_snd B S hS i hi.isClosedImmersion.rep k₁,
        ← smallBaseChange_map_snd B S hS i hi.isClosedImmersion.rep k₂, e]
    have hcomm : hi.isClosedImmersion.rep.snd V.1.hom ≫
          hW.lift' k₁.hom.left (𝟙 V.1.left) (hcond k₁) =
        hi.isClosedImmersion.rep.snd V.1.hom ≫
          hW.lift' k₂.hom.left (𝟙 V.1.left) (hcond k₂) := by
      refine hW.hom_ext' ?_ ?_
      · rw [Category.assoc, Category.assoc, hfst k₁, hfst k₂, he]
      · rw [Category.assoc, Category.assoc, hsnd k₁, hsnd k₂]
    have hsection : hW.lift' k₁.hom.left (𝟙 V.1.left) (hcond k₁) =
        hW.lift' k₂.hom.left (𝟙 V.1.left) (hcond k₂) := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      refine Stacks.Etale.hom_ext_of_surjective
        ((BigFppfOver.toScheme B S hS).map
          (hi.isClosedImmersion.rep.snd V.1.hom))
        (surjective_projection_of_isThickeningHom B S hS hi V).surj
        ((BigFppfOver.toScheme B S hS).map (hW.snd V.1.hom)) _ _ ?_ ?_
      · rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp, hsnd k₁, hsnd k₂]
      · rw [← (BigFppfOver.toScheme B S hS).map_comp,
          ← (BigFppfOver.toScheme B S hS).map_comp, hcomm]
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    rw [← hfst k₁, ← hfst k₂]
    exact congrArg (fun t ↦ t ≫ hW.fst' V.1.hom) hsection


/-- **Base change along a thickening neither creates nor destroys coverings.** This is
`AlgebraicGeometry.Space.functorPushforward_mem_smallEtaleTopology_iff_of_isThickening` for a
thickening in the morphism form, with the same proof. -/
theorem functorPushforward_mem_smallEtaleTopology_iff_of_isThickeningHom
    (hi : IsThickeningHom B S hS i) (U : SmallEtale B S hS X'.1) (R : Sieve U) :
    R.functorPushforward (smallBaseChange B S hS i hi.isClosedImmersion.rep) ∈
        SmallEtale.topology B S hS X.1
          ((smallBaseChange B S hS i hi.isClosedImmersion.rep).obj U) ↔
      R ∈ SmallEtale.topology B S hS X'.1 U := by
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
    obtain ⟨z, hz⟩ := (surjective_projection_of_isThickeningHom B S hS hi U).surj u
    obtain ⟨W', m, ⟨V, g, k, hgR, hm⟩, w, hw⟩ := h z
    refine ⟨V, g, hgR, (BigFppfOver.toScheme B S hS).map (k.hom.left ≫
      hi.isClosedImmersion.rep.snd V.1.hom) w, ?_⟩
    have hmleft : m.hom.left =
        k.hom.left ≫ ((smallBaseChange B S hS i hi.isClosedImmersion.rep).map g).hom.left :=
      congrArg (fun t : W' ⟶ (smallBaseChange B S hS i hi.isClosedImmersion.rep).obj U ↦
        t.hom.left) hm
    have hmor : (k.hom.left ≫ hi.isClosedImmersion.rep.snd V.1.hom) ≫ g.hom.left =
        m.hom.left ≫ hi.isClosedImmersion.rep.snd U.1.hom := by
      rw [hmleft]
      exact (Category.assoc _ _ _).trans <| (congrArg (k.hom.left ≫ ·)
        (smallBaseChange_map_snd B S hS i hi.isClosedImmersion.rep g).symm).trans
        (Category.assoc _ _ _).symm
    exact (hcomp _ _ w).symm.trans <| (congrArg (fun t ↦ (BigFppfOver.toScheme B S hS).map t w)
      hmor).trans <| (hcomp _ _ w).trans <|
      (congrArg ((BigFppfOver.toScheme B S hS).map (hi.isClosedImmersion.rep.snd U.1.hom))
        hw).trans hz
  · intro h z
    obtain ⟨V, g, hgR, v, hvz⟩ := h ((BigFppfOver.toScheme B S hS).map
      (hi.isClosedImmersion.rep.snd U.1.hom) z)
    obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
      (representablePullbackMap_isPullback_scheme B S hS i
        hi.isClosedImmersion.rep g) z v hvz.symm
    exact ⟨(smallBaseChange B S hS i hi.isClosedImmersion.rep).obj V,
      (smallBaseChange B S hS i hi.isClosedImmersion.rep).map g,
      Sieve.image_mem_functorPushforward _ R hgR, w, hw⟩


/-- **The small étale site of `X'` is a dense subsite of the small étale site of a thickening
`i : X ⟶ X'`**, through base change of étale scheme charts along `i`. Cover density and local
fullness are Stacks 04E5 for the closed immersion `i`; faithfulness and the covering condition use
that `i` is surjective after base change. -/
theorem smallBaseChange_isDenseSubsite_of_isThickeningHom (hi : IsThickeningHom B S hS i) :
    (smallBaseChange B S hS i hi.isClosedImmersion.rep).IsDenseSubsite
      (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1) :=
  let := smallBaseChange_isCoverDense_of_isClosedImmersion B S hS i hi.isClosedImmersion
  let := smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS i hi.isClosedImmersion
  let := smallBaseChange_faithful_of_isThickeningHom B S hS hi
  { functorPushforward_mem_iff := fun {U R} ↦
      functorPushforward_mem_smallEtaleTopology_iff_of_isThickeningHom B S hS hi U R }

/-- The comma categories indexing the right Kan extension along base change of étale scheme
charts along a thickening have limits in any category with limits of `u`-small shapes. -/
theorem hasLimitsOfShape_structuredArrow_smallBaseChange_of_isThickeningHom
    (hi : IsThickeningHom B S hS i) (A : Type w) [Category.{w'} A] [HasLimitsOfSize.{u, u} A]
    (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (smallBaseChange B S hS i hi.isClosedImmersion.rep).op)
      A :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (smallBaseChange B S hS i hi.isClosedImmersion.rep).op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- **The Comparison Lemma for sheaves on the small étale sites of a thickening.** Restriction
along base change of étale scheme charts along a thickening `i : X ⟶ X'` is an equivalence from
the sheaves on the small étale site of `X` to the sheaves on the small étale site of `X'`, with
values in any category with limits of `u`-small shapes. -/
theorem isEquivalence_sheafPushforward_smallBaseChange_of_isThickeningHom
    (hi : IsThickeningHom B S hS i) (A : Type w) [Category.{w'} A] [HasLimitsOfSize.{u, u} A] :
    letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
    ((smallBaseChange B S hS i hi.isClosedImmersion.rep).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1)).IsEquivalence :=
  let := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
  let := hasLimitsOfShape_structuredArrow_smallBaseChange_of_isThickeningHom B S hS hi A
  inferInstance

/-- **Sheaves of modules on a thickening and on the ambient space.** For a thickening
`i : X ⟶ X'` and a sheaf of rings `R` on the small étale site of `X`, restriction of sections
along base change of étale scheme charts is an equivalence from sheaves of `R`-modules to sheaves
of modules over the restricted ring on the small étale site of `X'`. In the proof of Stacks 0DLL,
`R` is the square-zero extension `O₀[V]` of the structure sheaf of `X₀`. -/
noncomputable def thickeningHomModuleEquivalence (hi : IsThickeningHom B S hS i)
    (R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) :
    letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
    SheafOfModules.{u} R ≌ SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
      (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1)
      (smallBaseChange B S hS i hi.isClosedImmersion.rep) R) :=
  letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
  letI := isEquivalence_sheafPushforward_smallBaseChange_of_isThickeningHom B S hS hi
    AddCommGrpCat.{u}
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence _ _ _ R

end AlgebraicGeometry.Space

end
