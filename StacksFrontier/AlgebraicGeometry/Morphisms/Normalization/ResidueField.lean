module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# The normalization of a scheme in the spectrum of a residue field

Let `X` be a scheme, `p` a point of `X`, and `π : Y ⟶ X` the normalization of `X` in
`Spec κ(p)`, that is `(X.fromSpecResidueField p).fromNormalization`. Two facts about `π` are
proved here.

The scheme-theoretic image of `π` is the reduced closure of `{p}`: the kernel ideal sheaf of the
structural morphism out of a relative normalization agrees with that of the morphism being
normalized, and for a morphism out of a reduced scheme the kernel is the vanishing ideal of the
closure of the image. So `π` factors through the reduced closed subscheme `closure{p}`, and the
factored morphism is dominant and integral — which is what makes the dimension formula over a
universally catenary base applicable to it.

Secondly `Y` is a normal scheme: over an affine open `U` of `X` the normalization is the spectrum
of the integral closure of `Γ(X, U)` in `Γ(Spec κ(p), π⁻¹U)`, and the latter ring is either
`κ(p)` or the zero ring, so the integral closure is a subring of a field and hence a normal
domain.

## Main definitions

* `AlgebraicGeometry.Scheme.residueFieldNormalizationToPointClosure`: the factorization of `π`
  through the reduced closure of `{p}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ker_comp_of_ker_eq_bot`: a morphism with trivial kernel ideal
  sheaf can be prepended to another without changing the kernel.
* `AlgebraicGeometry.Scheme.Hom.ker_fromNormalization`: the structural morphism of a relative
  normalization has the same kernel ideal sheaf as the morphism being normalized.
* `AlgebraicGeometry.Scheme.ker_fromNormalization_fromSpecResidueField`: consequently the
  scheme-theoretic image of `π` is the reduced closure of `{p}`.
* `AlgebraicGeometry.Scheme.isDominant_residueFieldNormalizationToPointClosure`,
  `AlgebraicGeometry.Scheme.isSchemeTheoreticallyDominant_residueFieldNormalizationToPointClosure`
  and `AlgebraicGeometry.Scheme.isIntegralHom_residueFieldNormalizationToPointClosure`: that
  factorization is dominant, with trivial kernel ideal sheaf, and integral.
* `AlgebraicGeometry.isNormal_normalization_fromSpecResidueField`: `Y` is normal.
* `isNormalRing_integralClosure_of_field`: the integral closure of a ring in a field is a normal
  ring.

## Implementation notes

The point closure is spelled `Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {p})`, the
reduced induced structure on `closure{p}`, matching the form in which the dimension formula and
the coherence criteria of this library consume it.

Normality over an affine open `U` is read off `Γ(Spec κ(p), π⁻¹U)` through the property that
each of its elements is zero or a unit, which is shared by a field and the zero ring and
transports along a ring isomorphism. This avoids having to decide whether `p ∈ U`, which is what
distinguishes the two cases.

## References

* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
* [Stacks Project, Tag 056B](https://stacks.math.columbia.edu/tag/056B)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-! ### Normal integral closures -/

/-- The integral closure of a ring in a field is a normal ring: it is a domain, being a subring
of a field, and it is integrally closed in that field, hence in its own fraction field. -/
theorem isNormalRing_integralClosure_of_field (A : Type u) (K : Type u) [CommRing A] [Field K]
    [Algebra A K] : IsNormalRing (integralClosure A K) :=
  have : IsIntegrallyClosed (integralClosure A K) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
      (R := integralClosure A K) (S := K)
  IsNormalRing.of_isIntegrallyClosed _

/-- The integral closure of a ring in a ring each of whose elements is zero or a unit — a field
or the zero ring — is a normal ring. -/
theorem isNormalRing_integralClosure_of_isUnit_or_eq_zero (A K : Type u) [CommRing A]
    [CommRing K] [Algebra A K] (hK : ∀ x : K, x = 0 ∨ IsUnit x) :
    IsNormalRing (integralClosure A K) := by
  rcases subsingleton_or_nontrivial K with _ | _
  · have : Subsingleton (integralClosure A K) :=
      ⟨fun _ _ ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    refine isNormalRing_iff.mpr @fun q hq ↦ absurd (Ideal.eq_top_iff_one q |>.mpr ?_) hq.ne_top
    simp [Subsingleton.elim (1 : integralClosure A K) 0]
  · have hfield : IsField K :=
      ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx ↦ ((hK x).resolve_left hx).exists_right_inv⟩
    let := hfield.toField
    exact isNormalRing_integralClosure_of_field A K

namespace AlgebraicGeometry

/-! ### The kernel ideal sheaf of a relative normalization -/

namespace Scheme.Hom

/-- Precomposing with a morphism whose kernel ideal sheaf is trivial does not change the kernel
ideal sheaf: such a morphism is injective on sections. -/
theorem ker_comp_of_ker_eq_bot {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] (hf : f.ker = ⊥) : (f ≫ g).ker = g.ker := by
  have : IsSchemeTheoreticallyDominant f := ⟨hf⟩
  refine le_antisymm (Scheme.IdealSheafData.le_def.mpr fun U ↦ ?_) (f.le_ker_comp g)
  intro s hs
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hs ⊢
  refine f.app_injective (g ⁻¹ᵁ U.1) ?_
  rw [map_zero, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_app]
  exact hs

/-- **The scheme-theoretic image of a relative normalization.** For a qcqs morphism `f : X ⟶ Y`
the structural morphism `f.normalization ⟶ Y` has the same kernel ideal sheaf as `f`: on an
affine open the first is the inclusion of `Γ(Y, U)` into an integral closure inside
`Γ(X, f⁻¹U)`, and `X ⟶ f.normalization` is injective on sections. -/
theorem ker_fromNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] : f.fromNormalization.ker = f.ker := by
  have h := ker_comp_of_ker_eq_bot f.toNormalization f.fromNormalization f.ker_toNormalization
  rw [f.toNormalization_fromNormalization] at h
  exact h.symm

end Scheme.Hom

/-! ### The reduced closure of a point -/

/-- The reduced closure of a point is an integral scheme. -/
instance isIntegral_subscheme_vanishingIdeal_closure_singleton {X : Scheme.{u}} (p : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({p} : Set X))).subscheme :=
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({p} : Set X))).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
      rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      exact isIrreducible_singleton.closure)
  isIntegral_of_irreducibleSpace_of_isReduced _

namespace Scheme

/-- Transport of a closed subscheme along an equality of its ideal sheaf. -/
theorem eqToHom_comp_subschemeι {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst h
  simp

/-- **The scheme-theoretic image of the normalization of `X` in `Spec κ(p)` is the reduced
closure of `{p}`.** The kernel ideal sheaf of the structural morphism is that of
`Spec κ(p) ⟶ X`, whose source is reduced with image `{p}`. -/
theorem ker_fromNormalization_fromSpecResidueField {X : Scheme.{u}} (p : X) :
    (X.fromSpecResidueField p).fromNormalization.ker =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X)) := by
  rw [Scheme.Hom.ker_fromNormalization, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
    Scheme.range_fromSpecResidueField]

/-- **The factorization of the normalization of `X` in `Spec κ(p)` through the reduced closure of
`{p}`.** -/
noncomputable def residueFieldNormalizationToPointClosure (X : Scheme.{u}) (p : X) :
    (X.fromSpecResidueField p).normalization ⟶
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X))).subscheme :=
  (X.fromSpecResidueField p).fromNormalization.toImage ≫
    eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (ker_fromNormalization_fromSpecResidueField p))

/-- The factorization of the normalization of `X` in `Spec κ(p)` through the reduced closure of
`{p}`, followed by the closed immersion of that closure, is the structure morphism to `X`. -/
@[reassoc (attr := simp)]
theorem residueFieldNormalizationToPointClosure_subschemeι (X : Scheme.{u}) (p : X) :
    residueFieldNormalizationToPointClosure X p ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({p} : Set X))).subschemeι =
      (X.fromSpecResidueField p).fromNormalization := by
  rw [residueFieldNormalizationToPointClosure, Category.assoc,
    eqToHom_comp_subschemeι (ker_fromNormalization_fromSpecResidueField p),
    Scheme.Hom.toImage_imageι]

/-- The normalization of `X` in `Spec κ(p)` is dominant over the reduced closure of `{p}`. -/
instance isDominant_residueFieldNormalizationToPointClosure (X : Scheme.{u}) (p : X) :
    IsDominant (residueFieldNormalizationToPointClosure X p) := by
  rw [residueFieldNormalizationToPointClosure]
  infer_instance

/-- The normalization of `X` in `Spec κ(p)` is dominant over the reduced closure of `{p}` in the
scheme-theoretic sense: the kernel ideal sheaf of the factorization is trivial, so the
factorization is injective on sections over every open. -/
instance isSchemeTheoreticallyDominant_residueFieldNormalizationToPointClosure (X : Scheme.{u})
    (p : X) : IsSchemeTheoreticallyDominant (residueFieldNormalizationToPointClosure X p) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-- The normalization of `X` in `Spec κ(p)` is integral over the reduced closure of `{p}`. -/
instance isIntegralHom_residueFieldNormalizationToPointClosure (X : Scheme.{u}) (p : X) :
    IsIntegralHom (residueFieldNormalizationToPointClosure X p) := by
  refine MorphismProperty.of_postcomp (W := @IsIntegralHom) (W' := @IsSeparated) _
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X))).subschemeι
    inferInstance ?_
  rw [residueFieldNormalizationToPointClosure_subschemeι]
  infer_instance

/-- If the normalization of `X` in `Spec κ(p)` is finite over `X` then it is finite over the
reduced closure of `{p}`. -/
theorem isFinite_residueFieldNormalizationToPointClosure {X : Scheme.{u}} (p : X)
    (h : IsFinite (X.fromSpecResidueField p).fromNormalization) :
    IsFinite (residueFieldNormalizationToPointClosure X p) := by
  refine MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X))).subschemeι
    inferInstance ?_
  rw [residueFieldNormalizationToPointClosure_subschemeι]
  exact h

end Scheme

/-! ### Normality of the normalization in the spectrum of a residue field -/

/-- Every section of the structure sheaf of the spectrum of a field, over any open, is zero or a
unit: the space has one point, so the open is empty — in which case the sections vanish — or
everything, in which case the sections are the field. -/
private theorem isUnit_or_eq_zero_of_sections_residueField {X : Scheme.{u}} (p : X)
    (V : (Spec (X.residueField p)).Opens) (x : Γ(Spec (X.residueField p), V)) :
    x = 0 ∨ IsUnit x := by
  rcases eq_or_ne V ⊥ with rfl | hV
  · exact Or.inl (Subsingleton.elim _ _)
  · obtain ⟨z, hz⟩ : (V : Set (Spec (X.residueField p))).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h ↦ hV (Opens.coe_eq_empty.mp h)
    have hVtop : V = ⊤ :=
      Opens.ext (Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y z ▸ hz)
    subst hVtop
    let e := (Scheme.ΓSpecIso (X.residueField p)).commRingCatIsoToRingEquiv
    rcases eq_or_ne (e x) 0 with h | h
    · exact Or.inl (e.injective (by rw [h, map_zero]))
    · refine Or.inr ?_
      have hu : IsUnit (e.symm (e x)) := (isUnit_iff_ne_zero.mpr h).map e.symm.toRingHom
      rwa [e.symm_apply_apply] at hu

/-- **The normalization of a scheme in the spectrum of a residue field is normal.** Over an
affine open `U` of `X` it is the spectrum of the integral closure of `Γ(X, U)` in
`Γ(Spec κ(p), π⁻¹U)`, a ring whose elements are all zero or units, so that integral closure is a
normal ring. -/
theorem isNormal_normalization_fromSpecResidueField {X : Scheme.{u}} (p : X) :
    IsNormal (X.fromSpecResidueField p).normalization := by
  set f := X.fromSpecResidueField p with hf
  have h : IsNormal f.normalization ↔
      ∃ (I : Type u) (U : I → f.normalization.Opens),
        IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae _).out 1 4
  refine h.mpr ⟨X.affineOpens, fun U ↦ f.fromNormalization ⁻¹ᵁ U.1, IsOpenCover.mk ?_, fun U ↦ ?_⟩
  · refine top_unique fun z _ ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f.fromNormalization z)) isOpen_univ
    exact Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩
  · let : Algebra Γ(X, U.1) Γ(Spec (X.residueField p), f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    let := isNormal_spec_of_isNormalRing
      (isNormalRing_integralClosure_of_isUnit_or_eq_zero Γ(X, U.1)
        Γ(Spec (X.residueField p), f ⁻¹ᵁ U.1)
        (isUnit_or_eq_zero_of_sections_residueField p _))
    exact isNormal_of_iso (relativeNormalizationPreimageIso f U.1 U.2)

end AlgebraicGeometry

end
