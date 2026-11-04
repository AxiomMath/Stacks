module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.PushoutSituation
public import StacksFrontier.AlgebraicGeometry.Pushout.IntegralFibre

/-!
# Cartesian diagrams over a pushout situation

Consider a pushout situation: a closed immersion `i : Z ⟶ X` and an integral morphism
`j : Z ⟶ Y` whose fibres map into affine opens of `X`. Let `Y' ← Z' → X'` be a second span mapping
to `Y ← Z → X` by morphisms `g, h, f` which are separated, locally of finite type and locally
quasi-finite, with both squares cartesian. Then the primed span again satisfies the fibrewise
affineness condition, and so is itself a pushout situation.

## Main definitions

* `AlgebraicGeometry.CartesianDiagram` packages the primed span together with the two cartesian
  squares and the properties of the three vertical morphisms.
* `AlgebraicGeometry.inducedSituation` is the resulting pushout situation.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_range_subset_of_isIntegral`: on a quasi-affine scheme,
  the image of an affine scheme whose ring of functions is integral over a field is contained in
  an affine open.
* `AlgebraicGeometry.primedFiber_preimage_subset_affine`: the fibrewise affineness condition for
  the primed span.

## References

* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Equal morphisms of schemes agree on every point. -/
private theorem apply_eq_apply_of_eq {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) (x : X) :
    a x = b x := by
  rw [h]

/-- Let `V` be a quasi-affine scheme, let `F` be an affine scheme whose ring of global sections is
integral over a field `k`, and let `m : F ⟶ V` be any morphism. Then the image of `m` is contained
in an affine open of `V`. -/
theorem exists_isAffineOpen_range_subset_of_isIntegral {V F : Scheme.{u}} [V.IsQuasiAffine]
    [IsAffine F] {k : Type u} [Field k] (ι : k →+* Γ(F, ⊤)) (hι : ι.IsIntegral) (m : F ⟶ V) :
    ∃ O : V.Opens, IsAffineOpen O ∧ Set.range m ⊆ (O : Set V) := by
  have hpt : ∀ x : F, V.toSpecΓ (m x) =
      PrimeSpectrum.comap (m.appTop).hom (F.toSpecΓ x) := fun x =>
    apply_eq_apply_of_eq (Scheme.toSpecΓ_naturality m) x
  have hW : IsOpen (Set.range V.toSpecΓ.base) := V.toSpecΓ.isOpenEmbedding.isOpen_range
  have hsub : Set.range (PrimeSpectrum.comap (m.appTop).hom) ⊆ Set.range V.toSpecΓ.base := by
    rintro p ⟨q, rfl⟩
    refine ⟨m (F.isoSpec.inv q), ?_⟩
    rw [hpt]
    exact congrArg (PrimeSpectrum.comap (m.appTop).hom)
      (apply_eq_apply_of_eq F.isoSpec.inv_hom_id q)
  obtain ⟨f, hf₁, hf₂⟩ := Stacks.Pushout.exists_basicOpen_range_comap ι hι (m.appTop).hom hW hsub
  refine ⟨V.basicOpen f, ?_, ?_⟩
  · rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion V.toSpecΓ,
      ← Scheme.toSpecΓ_preimage_basicOpen]
    have heq : V.toSpecΓ ''ᵁ (V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
        PrimeSpectrum.basicOpen f :=
      SetLike.coe_injective (Set.image_preimage_eq_of_subset hf₂)
    rw [heq]
    exact IsAffineOpen.Spec_basicOpen f
  · rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, ← Scheme.toSpecΓ_preimage_basicOpen]
    show V.toSpecΓ (m x) ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(V, ⊤)))
    rw [hpt]
    exact hf₁ ⟨F.toSpecΓ x, rfl⟩

/-- A span `Y' ← Z' → X'` over the span of a pushout situation, whose two squares are cartesian
and whose three vertical morphisms are separated, locally of finite type
(`AlgebraicGeometry.LocallyOfFiniteType`) and locally quasi-finite
(`AlgebraicGeometry.LocallyQuasiFinite`). -/
structure CartesianDiagram (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) where
  /-- The scheme over `X`. -/
  X' : Scheme.{u}
  /-- The scheme over `Y`. -/
  Y' : Scheme.{u}
  /-- The scheme over `Z`. -/
  Z' : Scheme.{u}
  /-- The morphism over the closed immersion `i`. -/
  i' : Z' ⟶ X'
  /-- The morphism over the integral morphism `j`. -/
  j' : Z' ⟶ Y'
  /-- The vertical morphism over `X`. -/
  f : X' ⟶ s.X
  /-- The vertical morphism over `Y`. -/
  g : Y' ⟶ s.Y
  /-- The vertical morphism over `Z`. -/
  h : Z' ⟶ s.Z
  /-- The square on the closed-immersion side is cartesian. -/
  left_isPullback : IsPullback i' h f s.i
  /-- The square on the integral side is cartesian. -/
  right_isPullback : IsPullback j' h g s.j
  /-- The vertical morphism over `X` is separated. -/
  [f_isSeparated : IsSeparated f]
  /-- The vertical morphism over `Y` is separated. -/
  [g_isSeparated : IsSeparated g]
  /-- The vertical morphism over `Z` is separated. -/
  [h_isSeparated : IsSeparated h]
  /-- The vertical morphism over `X` is locally of finite type. -/
  [f_locallyOfFiniteType : LocallyOfFiniteType f]
  /-- The vertical morphism over `Y` is locally of finite type. -/
  [g_locallyOfFiniteType : LocallyOfFiniteType g]
  /-- The vertical morphism over `Z` is locally of finite type. -/
  [h_locallyOfFiniteType : LocallyOfFiniteType h]
  /-- The vertical morphism over `X` has locally quasi-finite fibres. -/
  [f_locallyQuasiFinite : LocallyQuasiFinite f]
  /-- The vertical morphism over `Y` has locally quasi-finite fibres. -/
  [g_locallyQuasiFinite : LocallyQuasiFinite g]
  /-- The vertical morphism over `Z` has locally quasi-finite fibres. -/
  [h_locallyQuasiFinite : LocallyQuasiFinite h]

namespace CartesianDiagram

attribute [instance] f_isSeparated g_isSeparated h_isSeparated
  f_locallyOfFiniteType g_locallyOfFiniteType h_locallyOfFiniteType
  f_locallyQuasiFinite g_locallyQuasiFinite h_locallyQuasiFinite

end CartesianDiagram

/-- The primed span of a cartesian diagram satisfies the fibrewise affineness condition of a
pushout situation: every fibre of `j'` maps under `i'` into a single affine open of `X'`. -/
@[stacks 0ECK "part (1)"]
theorem primedFiber_preimage_subset_affine
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    ∀ y : d.Y', ∃ U : d.X'.Opens, IsAffineOpen U ∧
      ∀ z : d.Z', d.j' z = y → d.i' z ∈ U := by
  classical
  intro y'
  obtain ⟨U, hU, hfiber⟩ := s.fiber_preimage_subset_affine (d.g y')
  have : IsIntegralHom d.j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback d.right_isPullback.flip inferInstance
  have : IsAffine (d.j'.fiber y') := inferInstance
  set fiberMap : d.j'.fiber y' ⟶ d.X' := d.j'.fiberι y' ≫ d.i' with hfiberMap
  have hK : IsCompact (Set.range fiberMap) := isCompact_range fiberMap.continuous
  have hKU : Set.range fiberMap ⊆ (d.f ⁻¹ᵁ U : Set d.X') := by
    rintro x ⟨w, rfl⟩
    have hzj : d.j' (d.j'.fiberι y' w) = y' := by
      simpa using (d.j'.fiberHomeo y' w).2
    have hleft : d.f (d.i' (d.j'.fiberι y' w)) = s.i (d.h (d.j'.fiberι y' w)) := by
      simpa only [Scheme.Hom.comp_apply] using
        apply_eq_apply_of_eq d.left_isPullback.w (d.j'.fiberι y' w)
    have hright : s.j (d.h (d.j'.fiberι y' w)) = d.g (d.j' (d.j'.fiberι y' w)) := by
      simpa only [Scheme.Hom.comp_apply] using
        apply_eq_apply_of_eq d.right_isPullback.w.symm (d.j'.fiberι y' w)
    show d.f (d.i' (d.j'.fiberι y' w)) ∈ U
    rw [hleft]
    exact hfiber (d.h (d.j'.fiberι y' w)) (hright.trans (congrArg d.g hzj))
  obtain ⟨W, hWc, hWo, hKW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hK (d.f ⁻¹ᵁ U).2 hKU
  set U' : d.X'.Opens := ⟨W, hWo⟩ with hU'
  have hU'le : U' ≤ d.f ⁻¹ᵁ U := hWU
  have : CompactSpace U'.toScheme := isCompact_iff_compactSpace.mp hWc
  have : IsAffine U.toScheme := hU
  have : QuasiCompact (d.f.resLE U U' hU'le) := quasiCompact_of_compactSpace _
  have : U'.toScheme.IsQuasiAffine :=
    (isQuasiAffineHom_iff_isQuasiAffine (d.f.resLE U U' hU'le)).1
      (isQuasiAffineHom_of_locallyQuasiFinite (d.f.resLE U U' hU'le))
  have hRange : Set.range fiberMap ⊆ Set.range U'.ι.base := fun _ ⟨w, hw⟩ =>
    ⟨⟨fiberMap w, hKW ⟨w, rfl⟩⟩, hw⟩
  set fiberToU : d.j'.fiber y' ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι fiberMap hRange
    with hfiberToU
  have : IsIntegralHom (d.j'.fiberToSpecResidueField y') := by
    show IsIntegralHom (Limits.pullback.snd d.j' (d.Y'.fromSpecResidueField y'))
    infer_instance
  let : Field Γ(Spec (d.Y'.residueField y'), ⊤) :=
    (((Scheme.ΓSpecIso (d.Y'.residueField y')).commRingCatIsoToRingEquiv).toMulEquiv.isField
      (Field.toIsField _)).toField
  obtain ⟨O, hO, hOrange⟩ := exists_isAffineOpen_range_subset_of_isIntegral
    ((d.j'.fiberToSpecResidueField y').appTop).hom
    (IsIntegralHom.isIntegral_app (d.j'.fiberToSpecResidueField y') ⊤ (isAffineOpen_top _))
    fiberToU
  refine ⟨U'.ι ''ᵁ O, hO.image_of_isOpenImmersion U'.ι, fun z hzy => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : d.j'.fiber y', d.j'.fiberι y' w = z :=
    ⟨(d.j'.fiberHomeo y').symm ⟨z, hzy⟩, by simp⟩
  have hfac : U'.ι (fiberToU w) = fiberMap w :=
    apply_eq_apply_of_eq (IsOpenImmersion.lift_fac U'.ι fiberMap hRange) w
  have hgoal : U'.ι (fiberToU w) = d.i' z := by
    rw [hfac, hfiberMap, Scheme.Hom.comp_apply, hw]
  exact ⟨fiberToU w, hOrange ⟨w, rfl⟩, hgoal⟩

/-- The pushout situation attached to the primed span of a cartesian diagram. Its closed immersion
and integral morphism are the base changes of those of the original situation, and its fibrewise
affineness condition is `AlgebraicGeometry.primedFiber_preimage_subset_affine`. -/
noncomputable abbrev inducedSituation
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) (d : CartesianDiagram s) :
    PushoutAlongClosedImmersionAndIntegralSituation.{u} where
  S := s.S
  X := d.X'
  Y := d.Y'
  Z := d.Z'
  pX := d.f ≫ s.pX
  pY := d.g ≫ s.pY
  pZ := d.h ≫ s.pZ
  i := d.i'
  j := d.j'
  i_over := by rw [← Category.assoc, d.left_isPullback.w, Category.assoc, s.i_over]
  j_over := by rw [← Category.assoc, d.right_isPullback.w, Category.assoc, s.j_over]
  isClosedImmersion_i :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback d.left_isPullback.flip inferInstance
  isIntegralHom_j :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback d.right_isPullback.flip inferInstance
  fiber_preimage_subset_affine := primedFiber_preimage_subset_affine s d

end AlgebraicGeometry

end
