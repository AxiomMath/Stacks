module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularGerm
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.Generizations
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.CompositionAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale locus around a point and its generizations

This file assembles the pointwise étaleness statements that an induction on `dim 𝒪_{X,x}` over
the generizations of `x` consumes: from étaleness at `x` one gets quasi-finiteness there, the
equality `dim 𝒪_{X,x} = dim 𝒪_{Y,f x}` and regularity of `𝒪_{X,x}` over a regular target; from
étaleness at every proper generization of `x` one gets an affine open neighbourhood of `x` on
which `f` is étale away from the closure of `x`, étaleness at the generic points, and — once the
residue field at `x` is finite over the one at `f x` — quasi-finiteness at `x` itself.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_of_etaleAt`: étaleness at a point implies quasi-finiteness
  there.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_etaleAt` and
  `AlgebraicGeometry.isRegularLocalRing_stalk_of_etaleAt`: the local invariants at a point of
  étaleness.
* `AlgebraicGeometry.ringKrullDim_stalk_le_of_quasiFiniteAt`: quasi-finiteness bounds the local
  dimension by that of the target.
* `AlgebraicGeometry.exists_isAffineOpen_etaleAt_outside_closure`: shrinking to an affine open on
  which `f` is étale off the closure of `x`.
* `AlgebraicGeometry.quasiFiniteAt_of_finite_residueField_of_etaleAt_generizations`: a point with
  finite residue field extension all of whose proper generizations are points of étaleness is a
  point of quasi-finiteness.
* `AlgebraicGeometry.etaleAt_generization_of_ringKrullDim_stalk_eq_zero`: over a source whose
  local ring at `x` is a domain, étaleness at the one-dimensional generizations of `x` propagates
  to the generic point.
* `AlgebraicGeometry.etaleAt_pullback_fromSpecStalk_iff`: base change to `Spec 𝒪_{Y,y}` does not
  change étaleness.
* `AlgebraicGeometry.etaleAt_normalization_pullback_codimensionOne`: on the normalization of a
  closed-subscheme base change, étaleness at the one-dimensional generizations.

## Implementation notes

Several of these are the pointwise forms of statements the library has for a globally étale
morphism. The passage is uniform: étaleness at `x` gives an open `U ∋ x` with `U.ι ≫ f` étale
(`AlgebraicGeometry.etaleAt_iff_exists_open`), the global statement applies to `U.ι ≫ f`, and the
stalk of `U` at `x` is the stalk of `X` at `x` because `U.ι` is an open immersion.

Quasi-finiteness at `x` is `AlgebraicGeometry.quasiFiniteAt`, the conjunction of finite type at
`x` with Mathlib's stalkwise `Scheme.Hom.QuasiFiniteAt`; the criterion used here is the
closed-plus-no-proper-generization entry of `AlgebraicGeometry.quasiFiniteAt_tfae`, whose two
halves are supplied respectively by finiteness of the residue field extension
([Stacks, Tag 01TF]) and by étaleness at the proper generizations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Consequences of étaleness at a point -/

/-- A morphism which is étale at a point is quasi-finite there: it is unramified there, and an
unramified point is a point of quasi-finiteness. -/
theorem quasiFiniteAt_of_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hx : EtaleAt f x) :
    quasiFiniteAt f x :=
  quasiFiniteAt_of_unramifiedAt f (Stacks.Discriminant.unramifiedAt_of_etaleAt f x hx)

/-- At a point of étaleness the local rings of source and target have the same dimension. -/
theorem ringKrullDim_stalk_eq_of_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (he : EtaleAt f x) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp he
  have _ : Etale (U.ι ≫ f) := hU
  exact ((U.stalkIso (⟨x, hxU⟩ : U.toScheme)).commRingCatIsoToRingEquiv.ringKrullDim).symm.trans
    (ringKrullDim_stalk_eq_of_etale (U.ι ≫ f) (⟨x, hxU⟩ : U.toScheme))

/-- At a point of étaleness over a regular local ring the source local ring is regular. -/
theorem isRegularLocalRing_stalk_of_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (he : EtaleAt f x) (hY : IsRegularLocalRing (Y.presheaf.stalk (f x))) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp he
  have _ : Etale (U.ι ≫ f) := hU
  have hreg : IsRegularLocalRing (U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U.toScheme)) :=
    (isRegularLocalRing_stalk_iff_of_etale (U.ι ≫ f) (⟨x, hxU⟩ : U.toScheme)).mpr hY
  exact IsRegularLocalRing.of_ringEquiv
    (U.stalkIso (⟨x, hxU⟩ : U.toScheme)).commRingCatIsoToRingEquiv

/-- Quasi-finiteness at a point bounds the dimension of the local ring by that of the target:
the maximal ideal lies over the maximal ideal, and its height can only drop. -/
theorem ringKrullDim_stalk_le_of_quasiFiniteAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : f.QuasiFiniteAt x) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (Y.presheaf.stalk (f x)) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have _ : IsLocalHom (algebraMap A B) := f.prop x
  have _ : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have _ : Algebra.QuasiFinite A B := RingHom.quasiFinite_algebraMap.mp hf
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt _ _)

/-- An étale morphism over a scheme with regular local rings has a normal source: each local ring
of the source is regular, hence a normal domain. -/
@[ega "IV 6.13.1" "special case"]
theorem isNormal_of_etale_of_isRegularLocalRing_stalk {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsNormal X := by
  apply (isNormal_iff_stalk_normal X).2
  intro x
  have _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    (isRegularLocalRing_stalk_iff_of_etale f x).mpr (hY (f x))
  exact ⟨IsRegularLocalRing.isDomain (X.presheaf.stalk x),
    isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)⟩

/-! ### Composition and restriction -/

/-- Étaleness at a point is preserved by precomposition with an étale morphism. -/
theorem etaleAt_comp_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) (x : X)
    (hg : EtaleAt g (f x)) : EtaleAt (f ≫ g) x := by
  obtain ⟨V, hfV, hV⟩ := (etaleAt_iff_exists_open g (f x)).mp hg
  have _ : Etale ((f ⁻¹ᵁ V).ι ≫ (f ≫ g)) := by
    rw [← Category.assoc, ← f.resLE_comp_ι (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V from le_rfl), Category.assoc]
    infer_instance
  exact (etaleAt_iff_exists_open (f ≫ g) x).mpr ⟨f ⁻¹ᵁ V, hfV, inferInstance⟩

/-- A morphism whose restriction over an open subscheme of the target is an isomorphism is étale
at every point above that open. -/
theorem etaleAt_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)] (x : X) (hx : f x ∈ U) : EtaleAt f x := by
  have _ : Etale (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have _ : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← f.resLE_comp_ι (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U from le_rfl)]
    infer_instance
  exact etaleAt_of_open_precomp (f ⁻¹ᵁ U).ι f (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme)
    ((etale_iff_forall_etaleAt _).mp inferInstance _)

/-! ### Shrinking to an affine open -/

/-- If a morphism is étale at every proper generization of `x`, then `x` has an affine open
neighbourhood on which the morphism is étale away from the closure of `x`.

The étale locus is open, and the ambient affine open neighbourhood of `x` is a Noetherian sober
space, so `AlgebraicGeometry.exists_isOpen_subset_union_closure_singleton` applies there. -/
theorem exists_isAffineOpen_etaleAt_outside_closure {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) (x : X) (h : ∀ z : X, z ⤳ x → z ≠ x → EtaleAt f z) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∉ closure ({x} : Set X) → EtaleAt f z := by
  obtain ⟨W, hW, hxW, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top x)
  change X.Opens at W
  have _ : IsAffine W := hW
  have _ : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have _ : NoetherianSpace (W : Set X) := noetherianSpace_of_isAffineOpen W hW
  have _ : QuasiSober (W : Set X) := (inferInstance : QuasiSober W.toScheme)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isOpen_subset_union_closure_singleton
    {z : W | EtaleAt f z} ((isOpen_setOf_etaleAt f).preimage continuous_subtype_val)
    ⟨x, hxW⟩ (fun z hz hne ↦ h z (hz.map continuous_subtype_val)
      (fun heq ↦ hne (Subtype.ext heq)))
  obtain ⟨U, hU, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ Subtype.val '' V from ⟨⟨x, hxW⟩, hxV, rfl⟩)
    (W.2.isOpenMap_subtype_val V hV)
  obtain ⟨U, hU, rfl⟩ := hU
  refine ⟨U, hU, hxU, ?_⟩
  intro z hz hzcl
  obtain ⟨z, hzV, rfl⟩ := hUV hz
  rcases hVU hzV with het | hcl
  · exact het
  · exact absurd (specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hcl : (⟨x, hxW⟩ : W) ⤳ z).map continuous_subtype_val))
      hzcl

/-! ### Quasi-finiteness from the generizations -/

/-- Two points of the source related by a generization, lying over one point of the target, at
the more generic of which the morphism is quasi-finite, are equal: the fibre is discrete at a
point of quasi-finiteness. -/
theorem eq_of_specializes_of_quasiFiniteAt_of_eq_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x z : X} (h : z ⤳ x) (he : f.QuasiFiniteAt z) (hf : f z = f x) :
    z = x := by
  have hx' : f.fiberι (f z) ((f.fiberHomeo (f z)).symm ⟨x, hf.symm⟩) = x :=
    f.fiberι_fiberHomeo_symm _ _
  have hs : f.asFiber z ⤳ (f.fiberHomeo (f z)).symm ⟨x, hf.symm⟩ := by
    apply (f.fiberι (f z)).isEmbedding.specializes_iff.mp
    simpa only [Scheme.Hom.fiberι_asFiber, hx'] using h
  have heq : (f.fiberHomeo (f z)).symm ⟨x, hf.symm⟩ = f.asFiber z := by
    simpa only [he.isClopen_singleton_asFiber.1.closure_eq, Set.mem_singleton_iff] using
      specializes_iff_mem_closure.mp hs
  simpa only [hx', Scheme.Hom.fiberι_asFiber] using
    (congrArg (f.fiberι (f z)) heq).symm

/-- A point whose own point of the fibre is closed and all of whose proper generizations are
points of étaleness is a point of quasi-finiteness: the fibre has no proper generization of it,
since such a generization would be a proper generization of `x` in `X` lying over the same point
of the target, at which the morphism is quasi-finite. -/
theorem quasiFiniteAt_of_isClosed_asFiber_of_etaleAt_generizations {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (het : ∀ z : X, z ⤳ x → z ≠ x → EtaleAt f z) : quasiFiniteAt f x := by
  apply ((quasiFiniteAt_tfae f x).out 3 1).mp
  refine ⟨hclosed, ?_⟩
  rintro ⟨z, hne, hs⟩
  have hzx : f.fiberι (f x) z ⤳ x := by
    simpa only [Scheme.Hom.fiberι_asFiber] using hs.map (f.fiberι (f x)).continuous
  have hne' : f.fiberι (f x) z ≠ x := fun heq ↦
    hne ((f.fiberι (f x)).isEmbedding.injective (heq.trans (f.fiberι_asFiber x).symm))
  refine hne' (eq_of_specializes_of_quasiFiniteAt_of_eq_image f hzx
    (quasiFiniteAt_of_etaleAt f _ (het _ hzx hne')).2 ?_)
  have hm := Set.mem_range_self (f := f.fiberι (f x)) z
  rwa [f.range_fiberι] at hm

/-- A point whose residue field is finite over the residue field of its image and all of whose
proper generizations are points of étaleness is a point of quasi-finiteness. -/
theorem quasiFiniteAt_of_finite_residueField_of_etaleAt_generizations {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hfinite : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (f x)) (X.residueField x))
    (het : ∀ z : X, z ⤳ x → z ≠ x → EtaleAt f z) : quasiFiniteAt f x :=
  quasiFiniteAt_of_isClosed_asFiber_of_etaleAt_generizations f x
    ((isClosed_asFiber_iff_finite_residueField f x).mpr hfinite) het

/-! ### Étaleness at the generic point -/

/-- If the local ring at `x` is a domain and the morphism is étale at every generization of `x`
whose local ring has dimension one, then it is étale at every generization of `x` whose local
ring has dimension zero.

Both points come from `Spec 𝒪_{X,x}`; the one of dimension zero corresponds to a prime of height
zero, hence to the zero ideal, which is contained in the prime of the dimension-one point, so the
dimension-zero point is a generization of it. -/
theorem etaleAt_generization_of_ringKrullDim_stalk_eq_zero {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Y) {x x' : X}
    (hX : IsDomain (X.presheaf.stalk x))
    (hpositive : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hetale : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 → EtaleAt f z)
    (h : x' ⤳ x) (hdim : ringKrullDim (X.presheaf.stalk x') = 0) : EtaleAt f x' := by
  obtain ⟨z, hzx, hzdim⟩ := exists_specializes_ringKrullDim_stalk_eq_one x hpositive
  have hr (w : X) : w ∈ Set.range (X.fromSpecStalk x) ↔ w ⤳ x := by
    simp only [Scheme.range_fromSpecStalk, Set.mem_ofPred_eq]
  obtain ⟨p, rfl⟩ := (hr x').2 h
  obtain ⟨q, rfl⟩ := (hr z).2 hzx
  have hp : p.asIdeal.height = 0 :=
    WithBot.coe_eq_coe.mp ((ringKrullDim_stalk_fromSpecStalk X x p).symm.trans hdim)
  have hbot : p.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hp
  refine Specializes.mem_open (s := {w : X | EtaleAt f w}) ?_ (isOpen_setOf_etaleAt f)
    (hetale _ ?_ hzdim)
  · exact ((PrimeSpectrum.le_iff_specializes _ _).mp
      (show p.asIdeal ≤ q.asIdeal by simp [hbot])).map
        (X.fromSpecStalk x).continuous
  · exact (hr _).1 (Set.mem_range_self q)

/-! ### Base change to the local ring of the target -/

/-- Base change along `Spec 𝒪_{Y,y} ⟶ Y` does not change étaleness: that morphism is flat, so
the étale locus of the base change is the preimage of the étale locus. -/
theorem etaleAt_pullback_fromSpecStalk_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (y : Y) (z : (pullback f (Y.fromSpecStalk y) : Scheme.{u})) :
    EtaleAt (pullback.snd f (Y.fromSpecStalk y)) z ↔
      EtaleAt f (pullback.fst f (Y.fromSpecStalk y) z) := by
  have _ : Flat (Y.fromSpecStalk y) := flat_fromSpecStalk Y y
  exact (etaleAt_iff_of_isPullback (IsPullback.of_hasPullback f (Y.fromSpecStalk y))
    (Or.inr inferInstance) z).symm

/-! ### Étaleness on the normalization -/

/-- Over a scheme with regular local rings, étaleness at the image of a point of the
normalization lifts to étaleness of the composite with the normalization morphism: on an open
neighbourhood where the morphism is étale the source is normal, so the normalization restricts to
an isomorphism there. -/
theorem etaleAt_normalization_of_etaleAt_of_isRegularLocalRing_stalk {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X.normalizationScheme hX) (he : EtaleAt f (X.normalization hX x)) :
    EtaleAt (X.normalization hX ≫ f) x := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f (X.normalization hX x)).mp he
  have _ : Etale (U.ι ≫ f) := hU
  have _ : IsIso (X.normalization hX ∣_ U) :=
    Scheme.isIso_normalization_restrict_of_isNormal X hX U
      (isNormal_of_etale_of_isRegularLocalRing_stalk (U.ι ≫ f) hY)
  exact etaleAt_comp (X.normalization hX) f (x := x)
    (etaleAt_of_isIso_restrict (X.normalization hX) U x hxU) he

/-- On the normalization of a base change along a closed immersion into a scheme with regular
local rings, étaleness at a point of local dimension one above a point of local dimension at
least two, given étaleness of the original morphism at the proper generizations of the image
point. -/
theorem etaleAt_normalization_pullback_codimensionOne {X Y S : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [IsClosedImmersion g]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hfin : ∀ U : (pullback f g).Opens, IsCompact (U : Set (pullback f g : Scheme.{u})) →
      (irreducibleComponents U).Finite)
    [IsFinite ((pullback f g).normalization hfin)]
    (x : (pullback f g).normalizationScheme hfin)
    (hx : 2 ≤ ringKrullDim
      (((pullback f g).normalizationScheme hfin).presheaf.stalk x))
    (het : ∀ z : X, z ⤳ pullback.fst f g ((pullback f g).normalization hfin x) →
      z ≠ pullback.fst f g ((pullback f g).normalization hfin x) → EtaleAt f z)
    (z : (pullback f g).normalizationScheme hfin) (hz : z ⤳ x)
    (hdz : ringKrullDim (((pullback f g).normalizationScheme hfin).presheaf.stalk z) = 1) :
    EtaleAt ((pullback f g).normalization hfin ≫ pullback.snd f g) z := by
  have _ : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  have hne : z ≠ x := fun heq ↦ by
    rw [← heq, hdz] at hx
    exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 1) hx
  have hnne : (pullback f g).normalization hfin z ≠ (pullback f g).normalization hfin x :=
    fun heq ↦ hne (eq_of_specializes_of_quasiFiniteAt_of_eq_image
      ((pullback f g).normalization hfin) hz
      (((pullback f g).normalization hfin).quasiFiniteAt z) heq)
  refine etaleAt_normalization_of_etaleAt_of_isRegularLocalRing_stalk (pullback.snd f g) hY
    hfin z ?_
  refine etaleAt_of_isPullback (IsPullback.of_hasPullback f g)
    ((pullback f g).normalization hfin z) ?_
  refine het _ ((hz.map ((pullback f g).normalization hfin).continuous).map
    (pullback.fst f g).continuous) ?_
  exact fun heq ↦ hnne ((pullback.fst f g).isEmbedding.injective heq)

end AlgebraicGeometry

end
