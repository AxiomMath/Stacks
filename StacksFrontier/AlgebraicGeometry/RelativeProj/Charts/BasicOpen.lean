module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.ProjAway

/-!
# The chart of a relative projective spectrum over a standard open of the base

Let `s` be a relative `Proj` situation, let `W'` be an affine open of the base and let `g` be a
function on `W'`. Over the standard open `D(g) ⊆ W'` the graded ring of local sections is the
localization of the one over `W'` away from `g`, degree by degree, because the homogeneous pieces
of the algebra are quasi-coherent. Consequently the comparison morphism of charts

`Proj (s.sectionRingGrading D(g)) ⟶ Proj (s.sectionRingGrading W')`

is an open immersion onto the part of the chart over `W'` lying above `D(g)`. These are the two
topological statements of Stacks tag 01NO, for an inclusion of a standard open into an affine
open.

## Main results

* `Stacks.RelativeProj.Situation.isAwayDegreewise_basicOpen`: restriction of homogeneous sections
  to a standard open is, degree by degree, the localization away from the function cutting it out.
* `Stacks.RelativeProj.Situation.projInclusionToOpen_preimage`: the part of the chart over `W'`
  lying above `D(g)` is the standard open of the image of `g` in the section ring.
* `Stacks.RelativeProj.Situation.isOpenImmersion_projInclusionMap_basicOpen`: the comparison
  morphism is an open immersion.
* `Stacks.RelativeProj.Situation.opensRange_projInclusionMap_basicOpen`: its image is that part
  of the chart. This is the `opensRange_map` hypothesis of `Stacks.RelativeProj.Data`, for a
  standard open.

## Implementation notes

The three hypotheses of `Stacks.GradedLocalization.IsAwayDegreewise` come from
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` applied to each
homogeneous piece, together with
`Stacks.RelativeProj.Situation.sectionRingBaseMap_mul_of` to turn the module action of a function
on the base into multiplication in the section ring, and
`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen` for the invertibility of `g` on `D(g)`.

The localization statement about the homogeneous pieces is extracted through the auxiliary
lemmas `exists_pow_smul_eq_zero` and the `let`-bound `moduleOfLE` instances rather than used
directly, because the module structures on sections are stated for a
`AlgebraicGeometry.Scheme.Modules`, which is a type synonym for `SheafOfModules` that instance
search does not unfold; binding a variable of the synonym's type in a helper lemma makes them
resolve. For the same reason several steps are `Eq.trans` and `congrArg` rather than `rewrite`:
a motive mentioning a section module over `AlgebraicGeometry.Scheme.ringCatSheaf` does not
typecheck at `implicit` transparency.

The preimage computation chains `AlgebraicGeometry.Scheme.opensRange_homOfLE`,
`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι`,
`AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`,
`AlgebraicGeometry.SpecMap_preimage_basicOpen` and
`AlgebraicGeometry.Proj.toSpecZero_preimage_basicOpen`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite DirectSum
open HomogeneousLocalization HomogeneousIdeal
open Stacks.GradedLocalization Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) {W' : s.base.Opens} (g₀ : Γ(s.base, W'))

/-- The image of `g` in the section ring over `D(g)` is a unit. -/
private theorem isUnit_restrict_baseMap :
    IsUnit (gradedSectionRestriction s (s.base.basicOpen g₀) W' (s.base.basicOpen_le g₀)
      (s.sectionRingBaseMap W' g₀)) := by
  have hres := gradedSectionRestriction_baseMap s _ W' (s.base.basicOpen_le g₀) g₀
  rw [hres]
  exact RingHom.isUnit_map _ (s.base.toRingedSpace.isUnit_res_basicOpen g₀)

/-- Multiplying by a power of the image of a function acts as the module action of that power on
a homogeneous piece. -/
private theorem pow_sectionRingBaseMap_mul_of {U : s.base.Opens}
    (r : s.base.ringCatSheaf.obj.obj (op U)) (k n : ℕ) (a : s.sectionPieces U n) :
    s.sectionRingBaseMap U r ^ k * DirectSum.of (s.sectionPieces U) n a =
      DirectSum.of (s.sectionPieces U) n ((r ^ k) • a) := by
  rw [← map_pow, sectionRingBaseMap_mul_of]

/-- Every homogeneous section over `D(g)` becomes the restriction of one over `W'` after
multiplication by a power of `g`. -/
private theorem surj_restrict (hW' : IsAffineOpen W') (n : ℕ)
    (y : s.sectionRing (s.base.basicOpen g₀))
    (hy : y ∈ s.sectionRingGrading (s.base.basicOpen g₀) n) :
    ∃ (k : ℕ) (x : s.sectionRing W'), x ∈ s.sectionRingGrading W' n ∧
      gradedSectionRestriction s _ W' (s.base.basicOpen_le g₀) x =
        gradedSectionRestriction s _ W' (s.base.basicOpen_le g₀)
          (s.sectionRingBaseMap W' g₀) ^ k * y := by
  obtain ⟨a, rfl⟩ := hy
  let hle := s.base.basicOpen_le g₀
  let := moduleOfLE (s.algebra.piece (n : ℤ)) hle
  have hloc := isLocalizedModule_restrictₗ (s.algebra.piece (n : ℤ)) hW' g₀ rfl hle
  obtain ⟨⟨a', ⟨c, k, rfl⟩⟩, hac⟩ :=
    IsLocalizedModule.surj (Submonoid.powers g₀) (restrictₗ (s.algebra.piece (n : ℤ)) hle) a
  refine ⟨k, DirectSum.of (s.sectionPieces W') n a', ⟨a', rfl⟩, ?_⟩
  rw [gradedSectionRestriction_of s _ W' hle n a', gradedSectionRestriction_baseMap s _ W' hle g₀,
    pow_sectionRingBaseMap_mul_of]
  exact congrArg (DirectSum.of (s.sectionPieces (s.base.basicOpen g₀)) n) <|
    hac.symm.trans (congrArg (fun r => r • a)
      (map_pow (ConcreteCategory.hom (s.base.ringCatSheaf.obj.map (homOfLE hle).op)) g₀ k))

/-- A section of a quasi-coherent module whose restriction to a standard open vanishes is killed
by a power of the function cutting out that open. Stated for a module of the scheme rather than
for a homogeneous piece of the graded algebra, so that the module structures on sections resolve
by instance search. -/
public theorem exists_pow_smul_eq_zero {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V)) (a : Γ(M, V))
    (h0 : M.presheaf.map (homOfLE (X.basicOpen_le g)).op a = 0) :
    ∃ k : ℕ, (g ^ k) • a = 0 := by
  let hle := X.basicOpen_le g
  let := moduleOfLE M hle
  have hloc := isLocalizedModule_restrictₗ M hV g rfl hle
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) _).mp
    (show restrictₗ M hle a = 0 from h0)
  exact ⟨k, hk⟩


/-- A homogeneous section over `W'` that restricts to zero on `D(g)` is killed by a power of the
image of `g`. -/
private theorem torsion_restrict (hW' : IsAffineOpen W') (n : ℕ)
    (x : s.sectionRing W') (hx : x ∈ s.sectionRingGrading W' n)
    (hzero : gradedSectionRestriction s _ W' (s.base.basicOpen_le g₀) x = 0) :
    ∃ k : ℕ, s.sectionRingBaseMap W' g₀ ^ k * x = 0 := by
  obtain ⟨a', rfl⟩ := hx
  let hle := s.base.basicOpen_le g₀
  rw [gradedSectionRestriction_of s _ W' hle n a'] at hzero
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero (s.algebra.piece (n : ℤ)) hW' g₀ a'
    ((DFinsupp.single_eq_zero (β := s.sectionPieces (s.base.basicOpen g₀))).mp hzero)
  refine ⟨k, ?_⟩
  exact (pow_sectionRingBaseMap_mul_of s g₀ k n a').trans
    ((congrArg (DirectSum.of (s.sectionPieces W') n) hk).trans (map_zero _))

/-- **Restriction of homogeneous sections to a standard open is a degreewise localization.**
Each homogeneous piece of the algebra is quasi-coherent, so its sections over `D(g)` are the
sections over `W'` localized away from `g`. -/
public theorem isAwayDegreewise_basicOpen (hW' : IsAffineOpen W') :
    IsAwayDegreewise (gradedSectionRestriction s (s.base.basicOpen g₀) W'
        (s.base.basicOpen_le g₀)) (s.sectionRingBaseMap W' g₀) where
  isUnit_map := isUnit_restrict_baseMap s g₀
  surj := surj_restrict s g₀ hW'
  torsion n x hx hzero := torsion_restrict s g₀ hW' n x hx hzero

/-- **The part of a chart lying over a standard open of the base is a standard open.** -/
public theorem projInclusionToOpen_preimage (hW' : IsAffineOpen W') :
    projInclusionToOpen s W' hW' ⁻¹ᵁ (s.base.homOfLE (s.base.basicOpen_le g₀)).opensRange =
      Proj.basicOpen (s.sectionRingGrading W') (s.sectionRingBaseMap W' g₀) := by
  have hcomp : projInclusionToOpen s W' hW' ≫ W'.ι =
      Proj.toSpecZero (s.sectionRingGrading W') ≫ Spec.map (sectionRingZeroMap s W') ≫
        hW'.fromSpec := by
    rw [projInclusionToOpen, Category.assoc, Category.assoc, hW'.isoSpec_inv_ι]
  rw [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage, hW'.fromSpec_preimage_basicOpen, SpecMap_preimage_basicOpen,
    Proj.toSpecZero_preimage_basicOpen]
  congr 1
  exact congrArg Subtype.val (GradedRing.projZeroRingHom'_apply_coe _
    ⟨_, sectionRingBaseMap_mem_zero s W' g₀⟩)

/-- **The comparison morphism of charts over a standard open is an open immersion.** -/
public theorem isOpenImmersion_projInclusionMap_basicOpen (hW' : IsAffineOpen W')
    (hW : IsAffineOpen (s.base.basicOpen g₀)) :
    IsOpenImmersion
      (projInclusionMap s (s.base.basicOpen g₀) W' (s.base.basicOpen_le g₀) hW hW') :=
  Stacks.ProjAway.isOpenImmersion_map (isAwayDegreewise_basicOpen s g₀ hW')
    (sectionRingBaseMap_mem_zero s W' g₀) _

/-- **The image of the comparison morphism over a standard open is the part of the chart lying
over that open.** This is the `opensRange_map` hypothesis of `Stacks.RelativeProj.Data` for an
inclusion of a standard open into an affine open. -/
public theorem opensRange_projInclusionMap_basicOpen (hW' : IsAffineOpen W')
    (hW : IsAffineOpen (s.base.basicOpen g₀)) :
    letI := isOpenImmersion_projInclusionMap_basicOpen s g₀ hW' hW
    projInclusionToOpen s W' hW' ⁻¹ᵁ (s.base.homOfLE (s.base.basicOpen_le g₀)).opensRange =
      (projInclusionMap s (s.base.basicOpen g₀) W' (s.base.basicOpen_le g₀) hW hW').opensRange := by
  have := isOpenImmersion_projInclusionMap_basicOpen s g₀ hW' hW
  rw [projInclusionToOpen_preimage s g₀ hW']
  exact (Stacks.ProjAway.opensRange_map (isAwayDegreewise_basicOpen s g₀ hW')
    (sectionRingBaseMap_mem_zero s W' g₀) _).symm

end Stacks.RelativeProj.Situation

end
