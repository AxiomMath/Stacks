module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolving an embedded curve by blowing up the ambient scheme at closed points

Let `Y` be a one-dimensional integral closed subscheme of a Noetherian scheme `X` satisfying the
equivalent conditions of [Stacks, Tag 0BI4]. Then a finite chain of blowups of `X` at closed
points makes the strict transform of `Y` a regular curve.

## Main definitions

* `AlgebraicGeometry.ChainTransform` relates a chain of blowups of the ambient scheme at closed
  points to the successive strict transforms of a closed subscheme along it.
* `AlgebraicGeometry.ChainTransform.pointBlowupChain`: such a chain is a chain of blowups at
  closed points.

## Main results

* `AlgebraicGeometry.exists_pointBlowupChain_chainTransform_isRegular`: [Stacks, Tag 0BI5].
* `AlgebraicGeometry.topologicalKrullDim_eq_of_pointBlowupChain`: a chain of blowups at closed
  points over a one-dimensional integral Noetherian scheme has one-dimensional source.

## Implementation notes

`AlgebraicGeometry.ChainTransform` is indexed by the composite morphism to the ambient scheme,
exactly as `Stacks.ResolutionOfSurfaces.PointBlowupChain` is, and refines it by carrying the
ideal sheaf of the strict transform; the two chains are therefore the same chain, and
`AlgebraicGeometry.ChainTransform.pointBlowupChain` is the forgetful implication. A `def`
returning the strict transform as data is not available: `PointBlowupChain` is a `Prop`.

[Stacks, Tag 0BI4] supplies a chain of blowups at closed points of `Y` with regular source, and
that chain is lifted step by step to `X` by blowing up the image of each centre; at each stage the
ambient strict transform is the blowup of the previous stage, by [Stacks, Tag 080E], since the
inverse image of a reduced closed point under a closed immersion is again a reduced closed point.
Transporting a blowup along the isomorphism produced at the previous stage uses the flat base
change of [Stacks, Tag 0805] for an isomorphism.

Dimension is not preserved by `PointBlowupChain` for formal reasons. Such a chain is proper and
birational over its one-dimensional integral Noetherian base
(`Stacks.ResolutionOfSurfaces.pointBlowupChain_properties`), hence an alteration — it is an
isomorphism over a dense open by [Stacks, Tag 0BAJ] — hence finite and surjective, and a
surjective integral morphism preserves dimension by [Stacks, Tag 0ECG].

## References

* [Stacks Project, Tag 0BI5](https://stacks.math.columbia.edu/tag/0BI5)
* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

/-! ### The successive strict transforms along a chain of point blowups -/

/-- The successive strict transforms of a closed subscheme `Y ⊆ X` along a chain of blowups of
`X` at closed points, indexed by the composite morphism to `X`: `ChainTransform Y f J` says that
`f : W ⟶ X` is such a chain and that `J` is the ideal sheaf of the strict transform of `Y` in
`W`. Each step is the one-step strict transform `AlgebraicGeometry.transformIdeal`. -/
public inductive ChainTransform {X : Scheme.{u}} (Y : X.IdealSheafData) :
    {W : Scheme.{u}} → (W ⟶ X) → W.IdealSheafData → Prop
  | refl : ChainTransform Y (𝟙 X) Y
  | step {W : Scheme.{u}} {f : W ⟶ X} {J : W.IdealSheafData} (hJ : ChainTransform Y f J)
      (w : W) (hw : IsClosed ({w} : Set W)) :
      ChainTransform Y (blowUpToBase (centerIdeal w hw) ≫ f) (transformIdeal J w hw)

/-- A chain of strict transforms lies over a chain of blowups at closed points. -/
public theorem ChainTransform.pointBlowupChain {X W : Scheme.{u}} {Y : X.IdealSheafData}
    {f : W ⟶ X} {J : W.IdealSheafData} (h : ChainTransform Y f J) :
    PointBlowupChain X Set.univ W f := by
  induction h with
  | refl => exact .refl
  | step hJ w hw ih => exact ih.step w hw (Set.mem_univ _)

/-! ### Reduced closed points and closed immersions -/

/-- A quasi-coherent ideal sheaf with reduced closed subscheme is its own radical. -/
theorem radical_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  ext1
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, ← I.ker_subschemeι, Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr
    ((RingHom.ker_isRadical_iff_reduced_of_surjective
      (I.subschemeι_app_surjective U)).mpr inferInstance)

/-- Two quasi-coherent ideal sheaves with reduced closed subschemes and the same support are
equal. -/
theorem eq_of_support_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    [IsReduced I.subscheme] [IsReduced J.subscheme] (h : I.support = J.support) : I = J := by
  rw [← radical_eq_of_isReduced I, ← radical_eq_of_isReduced J,
    ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support, h]

/-- **The inverse image of a reduced closed point under a closed immersion is the reduced closed
point above it.** Both sides are reduced with the same support, the fibre of a closed immersion
over a point of its image being a single point. -/
public theorem comap_centerIdeal_of_isClosedImmersion {C X : Scheme.{u}} (j : C ⟶ X)
    [IsClosedImmersion j] (q : C) (hq : IsClosed ({q} : Set C))
    (hjq : IsClosed ({j q} : Set X)) :
    (centerIdeal (j q) hjq).comap j = centerIdeal q hq := by
  set D := centerIdeal (j q) hjq with hD
  have hmem : j q ∈ j.ker.support := by
    change j q ∈ (j.ker.support : Set X)
    rw [j.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq]
    exact ⟨q, rfl⟩
  have hle : j.ker ≤ D := by
    refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun x hx => ?_
    change x = j q at hx
    subst hx
    exact hmem
  have hk : IsClosedImmersion.lift j D.subschemeι
      (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using hle) ≫ j = D.subschemeι :=
    IsClosedImmersion.lift_fac j D.subschemeι _
  have : IsIso (pullback.snd j D.subschemeι) := by rw [← hk]; infer_instance
  have : IsReduced D.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal ⟨{j q}, hjq⟩
  have : IsReduced (D.comap j).subscheme :=
    isReduced_of_isOpenImmersion ((D.comapIso j).hom ≫ pullback.snd j D.subschemeι)
  have : IsReduced (centerIdeal q hq).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal ⟨{q}, hq⟩
  refine eq_of_support_eq _ _ ?_
  rw [Scheme.IdealSheafData.support_comap]
  refine SetLike.coe_injective ?_
  change j ⁻¹' {j q} = {q}
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact j.isClosedEmbedding.injective.eq_iff

/-! ### Transporting a blowup along an isomorphism -/

/-- The blowup of the inverse image of an ideal sheaf under an isomorphism is the blowup of the
ideal sheaf: the inverse image is the flat base change of [Stacks, Tag 0805] along an
isomorphism. -/
public theorem nonempty_blowUp_comap_iso_of_isIso {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂) [IsIso g]
    (I : X₂.IdealSheafData) : Nonempty (blowUp (I.comap g) ≅ blowUp I) := by
  obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap g I
  have hiso : MorphismProperty.isomorphisms Scheme h :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb
      (show MorphismProperty.isomorphisms Scheme g from inferInstance)
  have : IsIso h := hiso
  exact ⟨asIso h⟩

/-! ### One step of the lift -/

/-- **The strict transform of a closed subscheme under the blowup at a closed point of its
support is the blowup of that subscheme at the point above it.** This is a case of
[Stacks, Tag 080E]. -/
@[sga "7 X 2.6" "special case"]
public theorem nonempty_transformIdeal_subscheme_iso_blowUp {X : Scheme.{u}}
    (J : X.IdealSheafData) (q : J.subscheme) (hq : IsClosed ({q} : Set J.subscheme))
    (hw : IsClosed ({J.subschemeι q} : Set X)) :
    Nonempty ((transformIdeal J (J.subschemeι q) hw).subscheme ≅ blowUp (centerIdeal q hq)) := by
  have : IsClosedImmersion (transformToBlowUp J (J.subschemeι q) hw) :=
    isClosedImmersion_transformToBlowUp J (J.subschemeι q) hw
  -- The image of the strict transform in the ambient blowup is the strict transform itself.
  have e₁ : (transformIdeal J (J.subschemeι q) hw).subscheme ≅
      transform J (J.subschemeι q) hw :=
    (asIso (transformToBlowUp J (J.subschemeι q) hw).toImage).symm
  -- Tag 080E identifies the strict transform with the blowup of the inverse image centre.
  have e₂ : transform J (J.subschemeι q) hw ≅
      blowUp ((centerIdeal (J.subschemeι q) hw).comap J.subschemeι) :=
    (Over.forget J.subscheme).mapIso
      (strictTransformBlowUpIso J.subschemeι (centerIdeal (J.subschemeι q) hw))
  rw [comap_centerIdeal_of_isClosedImmersion J.subschemeι q hq hw] at e₂
  exact ⟨e₁ ≪≫ e₂⟩

/-! ### Dimension along a chain of point blowups -/

/-- **A chain of blowups at closed points over a one-dimensional integral Noetherian scheme has
one-dimensional source.** Such a chain is an alteration, hence finite and surjective, and a
surjective integral morphism preserves dimension. -/
public theorem topologicalKrullDim_eq_of_pointBlowupChain {Y W : Scheme.{u}} [IsIntegral Y]
    [IsNoetherian Y] (hYdim : topologicalKrullDim Y = 1) {h : W ⟶ Y}
    (hc : PointBlowupChain Y Set.univ W h) : topologicalKrullDim W = 1 := by
  obtain ⟨hN, hI, hP, hB⟩ := pointBlowupChain_properties hYdim hc
  have : IsNoetherian W := hN
  have : IsIntegral W := hI
  have : IsProper h := hP
  have hdom : IsDominant h := ((tfae_isDominant_of_isIntegral h).out 1 2).mpr (by
    have := hB.bijOn.mapsTo
      (show genericPoint W ∈ genericPoints W by rw [genericPoints_eq_singleton]; rfl)
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at this)
  have : Finite (irreducibleComponents W) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := W)).to_subtype
  have : Finite (irreducibleComponents Y) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)).to_subtype
  obtain ⟨V, hVdense, hVi⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational h hB (Or.inl inferInstance)
      (Or.inl ⟨inferInstance, inferInstance⟩)
  have : IsIso (h ∣_ V) := hVi
  have hVne : Nonempty V := hVdense.nonempty.to_subtype
  have halt : IsAlteration h := ⟨hP, hdom, hI, ⟨V, hVne, inferInstance⟩⟩
  have : IsFinite h := isFinite_of_isAlteration_of_topologicalKrullDim_le_one h halt
    (le_of_eq hYdim)
  have hrange : Set.range h.base = Set.univ :=
    h.isClosedMap.isClosed_range.closure_eq.symm.trans hdom.denseRange.closure_eq
  have : Surjective h := ⟨Set.range_eq_univ.mp hrange⟩
  rw [topologicalKrullDim_eq_of_isIntegralHom_of_surjective h, hYdim]

/-! ### Lifting a chain of point blowups of the curve to the ambient scheme -/

/-- A closed map sends a closed point to a closed point. -/
private theorem isClosed_singleton_of_isClosedMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : IsClosedMap f) {a : α} (ha : IsClosed ({a} : Set α)) :
    IsClosed ({f a} : Set β) := by
  simpa using hf _ ha

/-- A chain of blowups of a closed subscheme at closed points is the chain of strict transforms
along a chain of blowups of the ambient scheme at closed points. -/
private theorem exists_chainTransform_of_pointBlowupChain {X V : Scheme.{u}}
    (Y : X.IdealSheafData) {g : V ⟶ Y.subscheme}
    (t : PointBlowupChain Y.subscheme Set.univ V g) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : W.IdealSheafData),
      ChainTransform Y f J ∧ Nonempty (V ≅ J.subscheme) := by
  induction t with
  | refl => exact ⟨X, 𝟙 X, Y, .refl, ⟨Iso.refl _⟩⟩
  | @step V g t v hv _ ih =>
      obtain ⟨W, f, J, hJ, ⟨e⟩⟩ := ih
      -- Transport the centre to the ambient scheme through the strict transform.
      have hq : IsClosed ({e.hom v} : Set J.subscheme) :=
        isClosed_singleton_of_isClosedMap (Scheme.homeoOfIso e).isClosedMap hv
      have hw : IsClosed ({J.subschemeι (e.hom v)} : Set W) :=
        isClosed_singleton_of_isClosedMap J.subschemeι.isClosedEmbedding.isClosedMap hq
      obtain ⟨d⟩ := nonempty_transformIdeal_subscheme_iso_blowUp J (e.hom v) hq hw
      -- The centre of the curve blowup is the inverse image of the ambient centre.
      have hcomap : (centerIdeal (e.hom v) hq).comap e.hom = centerIdeal v hv :=
        comap_centerIdeal_of_isClosedImmersion e.hom v hv hq
      obtain ⟨b⟩ := nonempty_blowUp_comap_iso_of_isIso e.hom (centerIdeal (e.hom v) hq)
      rw [hcomap] at b
      exact ⟨blowUp (centerIdeal (J.subschemeι (e.hom v)) hw),
        blowUpToBase (centerIdeal (J.subschemeι (e.hom v)) hw) ≫ f,
        transformIdeal J (J.subschemeι (e.hom v)) hw, hJ.step _ hw, ⟨b ≪≫ d.symm⟩⟩

/-! ### Embedded resolution of a curve -/

/-- Let `X` be a Noetherian scheme and let `Y ⊆ X` be an integral closed subscheme of dimension
one admitting an alteration by a regular scheme — one of the equivalent conditions of
[Stacks, Tag 0BI4]. Then there is a finite chain of blowups of `X` at closed points along which
the strict transform of `Y` becomes a regular curve. -/
@[stacks 0BI5]
public theorem exists_pointBlowupChain_chainTransform_isRegular {X : Scheme.{u}}
    [IsNoetherian X] (Y : X.IdealSheafData) [IsIntegral Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1)
    (hY : ∃ (Z : Scheme.{u}) (g : Z ⟶ Y.subscheme), IsAlteration g ∧ IsRegular Z) :
    ∃ (W : Scheme.{u}) (f : W ⟶ X) (J : W.IdealSheafData),
      PointBlowupChain X Set.univ W f ∧ ChainTransform Y f J ∧ IsIntegral J.subscheme ∧
        topologicalKrullDim J.subscheme = 1 ∧ IsRegular J.subscheme := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian Y.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian Y.subschemeι
  have : CompactSpace Y.subscheme := Y.subschemeι.isClosedEmbedding.compactSpace
  have : IsNoetherian Y.subscheme := IsNoetherian.mk
  obtain ⟨V, g, t, hVreg⟩ := ((resolveCurve_tfae Y.subscheme hYdim).out 1 3).mp hY
  obtain ⟨W, f, J, hJ, ⟨e⟩⟩ := exists_chainTransform_of_pointBlowupChain Y t
  obtain ⟨-, hVint, -, -⟩ := pointBlowupChain_properties hYdim t
  have : IsIntegral V := hVint
  refine ⟨W, f, J, hJ.pointBlowupChain, hJ, IsIntegral.of_isIso e.hom, ?_, fun x => ?_⟩
  · rw [← (IsHomeomorph.topologicalKrullDim_eq e.hom
      (Scheme.homeoOfIso e).isHomeomorph)]
    exact topologicalKrullDim_eq_of_pointBlowupChain hYdim t
  · obtain ⟨U, hxU, hU⟩ := hVreg (e.inv x)
    let : IsRegularRing Γ(V, U) := hU
    refine ⟨⟨e.inv ⁻¹ᵁ U.1, U.2.preimage e.inv⟩, hxU, ?_⟩
    exact IsRegularRing.of_ringEquiv (asIso (e.inv.app U.1)).commRingCatIsoToRingEquiv

end AlgebraicGeometry

end
