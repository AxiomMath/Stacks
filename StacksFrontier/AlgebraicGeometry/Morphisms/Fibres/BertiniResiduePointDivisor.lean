module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.AffineSpaceFibreChartConstants
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFlatOpenFamily

/-!
# A point of the parameter space is the point of its residue coordinates

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and write
`q : H_univ → 𝔸^r_k` for the universal family. A point `s` of the parameter space `𝔸^r_k`
determines the tuple `a₁, …, a_r` of values of the coordinate functions in its residue field
`κ(s)`, and the `κ(s)`-point of `𝔸^r_k` classifying that tuple is the canonical morphism
`Spec κ(s) → 𝔸^r_k`. Consequently the divisor `H_a` of that tuple **is** the fibre of `q` over
`s`, by the cartesian square of
`Stacks.Bertini.FamilyDivisors.isPullback_universalFamilyMap`.

Combined with the flatness of `q` over an open `W` of the parameter space
(`Stacks.Bertini.FamilyDivisors.mem_smoothLocus_of_isPullback_of_mem_smoothLocus`), this reduces
the Jacobian criterion in the Bertini situation to a statement about the divisor `H_a` alone: `q`
is smooth at a point `w` of `q⁻¹(W)` as soon as the divisor of the residue coordinates of `q(w)`
is smooth at the point of it which `w` comes from. That is the shape in which
`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` — the Jacobian
criterion for the zero scheme of a section of an invertible module over a perfect field, of which
the algebraically closed field here is one — can be applied, and it leaves no fibre product, no
base change and no flatness in the remaining obligation.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.algebraResidueFieldParameterBase`: the residue field at a point
  of the parameter space, as an extension of `k`.
* `Stacks.Bertini.FamilyDivisors.residueCoord`: the coordinate tuple of a point of the parameter
  space, the values of the coordinate functions in its residue field.

## Main results

* `AlgebraicGeometry.Scheme.appTop_fromSpecResidueField` and
  `AlgebraicGeometry.fromSpecResidueField_comp_eq_Spec_map_algebraMap`: the canonical morphism
  `Spec κ(y) → Y` on global sections, and its composite with a morphism to an affine scheme.
* `Stacks.Bertini.FamilyDivisors.parameterPoint_residueCoord`: **a point of `𝔸^r_k` is the point
  of its residue coordinates.**
* `Stacks.Bertini.FamilyDivisors.mem_smoothLocus_of_mem_smoothLocus_residueCoordDivisor`:
  **the Jacobian criterion reduced to the divisor.** Over an open where the family is flat, `q`
  is smooth at a point of `q⁻¹(W)` as soon as the divisor of the residue coordinates of its
  image is smooth at the point it comes from.

## Implementation notes

The `k`-algebra structure on `κ(s)` is the one the structure morphism of `𝔸^r_k` induces, and is
declared as an instance so that `Stacks.Bertini.FamilyDivisors.parameterPoint` can be applied to
a tuple with entries in `κ(s)` without a `letI` in every statement.

The divisor is spelled `(D.universalDivisor.comap (D.fibreParameterMap K a)).subscheme` rather
than `(D.specializedDivisor K a).subscheme`, because that is the spelling of the cartesian square
`Stacks.Bertini.FamilyDivisors.isPullback_universalFamilyMap`; the two are identified by
`Stacks.Bertini.FamilyDivisors.specializedDivisor_eq_comap`, whose rewriting changes the type of
every morphism out of the subscheme.

No `@[stacks]` attribute is attached: these are steps inside the proof of [Stacks, Tag 0FD6].

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **The canonical morphism `Spec κ(y) → Y` on global sections** is the evaluation at `y`
followed by the comparison of `κ(y)` with the global sections of its spectrum. -/
theorem Scheme.appTop_fromSpecResidueField {Y : Scheme.{u}} (y : Y) :
    (Y.fromSpecResidueField y).appTop =
      Y.Γevaluation y ≫ (Scheme.ΓSpecIso (Y.residueField y)).inv :=
  CommRingCat.hom_ext (RingHom.ext fun u =>
    Scheme.fromSpecResidueField_appTop_apply y u)

/-- **The canonical morphism `Spec κ(y) → Y` followed by a morphism to an affine scheme** is the
spectrum of the structure map of `κ(y)` as an `R`-algebra. -/
theorem fromSpecResidueField_comp_eq_Spec_map_algebraMap (R : Type u) [CommRing R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) (y : Y) :
    letI : Algebra R ↥(Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Y.fromSpecResidueField y ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥(Y.residueField y))) := by
  let : Algebra R ↥(Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  refine AlgebraicGeometry.ext_of_isAffine ?_
  have key : (Scheme.ΓSpecIso (.of R)).inv ≫
      (g.appTop ≫ (Y.fromSpecResidueField y).appTop) =
      (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R ↥(Y.residueField y)))).appTop := by
    rw [← Scheme.ΓSpecIso_inv_naturality, RingHom.algebraMap_toAlgebra,
      Scheme.appTop_fromSpecResidueField]
    simp only [Category.assoc, CommRingCat.ofHom_hom, CommRingCat.of_carrier]
  rw [Scheme.Hom.comp_appTop]
  exact (cancel_epi _).mp key

end AlgebraicGeometry

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- **The residue field at a point of the parameter space, as an extension of `k`**, along the
structure morphism of `𝔸^r_k`. -/
instance algebraResidueFieldParameterBase (s : D.parameterBase) :
    Algebra D.k ↥(D.parameterBase.residueField s) :=
  ((Scheme.ΓSpecIso (.of D.k)).inv ≫
    (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)).appTop ≫
      D.parameterBase.Γevaluation s).hom.toAlgebra

/-- **The coordinate tuple of a point of the parameter space**: the values of the coordinate
functions of `𝔸^r_k` in the residue field at it. -/
def residueCoord (s : D.parameterBase) (i : Fin (Module.finrank D.k D.V)) :
    ↥(D.parameterBase.residueField s) :=
  D.parameterBase.Γevaluation s (AffineSpace.coord (Spec (.of D.k)) (ULift.up i))

/-- **A point of the parameter space is the point of its residue coordinates**: the
`κ(s)`-point of `𝔸^r_k` classifying the values of the coordinate functions at `s` is the
canonical morphism `Spec κ(s) → 𝔸^r_k`.

Two morphisms into `𝔸^r_k` agree when they agree over `Spec k` and on each coordinate function;
over `Spec k` both are the spectrum of the structure map of `κ(s)`
(`AlgebraicGeometry.fromSpecResidueField_comp_eq_Spec_map_algebraMap`), and on the `i`-th
coordinate both give its value at `s`
(`AlgebraicGeometry.Scheme.fromSpecResidueField_appTop_apply`), which is what
`Stacks.Bertini.FamilyDivisors.residueCoord` is. -/
theorem parameterPoint_residueCoord (s : D.parameterBase) :
    D.parameterPoint (D.residueCoord s) = D.parameterBase.fromSpecResidueField s := by
  refine AffineSpace.hom_ext ?_ fun i => ?_
  · rw [D.parameterPoint_comp_base]
    exact (fromSpecResidueField_comp_eq_Spec_map_algebraMap D.k
      (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)) s).symm
  · rw [D.parameterPoint_appTop_coord, Scheme.fromSpecResidueField_appTop_apply]
    simp only [residueCoord, CommRingCat.of_carrier]

/-- **The divisor of the residue coordinates of a point of the parameter space** — the fibre of
`q` over that point, as the closed subscheme of `X_{κ(s)}` cut out by the universal divisor. -/
abbrev residueCoordDivisor (s : D.parameterBase) : Scheme.{u} :=
  (D.universalDivisor.comap (D.fibreParameterMap
    ↥(D.parameterBase.residueField s) (D.residueCoord s))).subscheme

/-- The structure morphism of the divisor of the residue coordinates over `κ(s)`. -/
abbrev residueCoordDivisorToBase (s : D.parameterBase) :
    D.residueCoordDivisor s ⟶ Spec (.of ↥(D.parameterBase.residueField s)) :=
  (D.universalDivisor.comap (D.fibreParameterMap
      ↥(D.parameterBase.residueField s) (D.residueCoord s))).subschemeι ≫
    D.baseChangeToSpec ↥(D.parameterBase.residueField s)

/-- **The divisor of the residue coordinates is of finite presentation over `κ(s)`**, being a
base change of `q`. -/
instance locallyOfFinitePresentation_residueCoordDivisorToBase [Smooth D.toBase]
    (s : D.parameterBase) : LocallyOfFinitePresentation (D.residueCoordDivisorToBase s) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
    (D.isPullback_universalFamilyMap ↥(D.parameterBase.residueField s) (D.residueCoord s))
    (inferInstanceAs (LocallyOfFinitePresentation D.universalFamilyMap))

/-- **The Jacobian criterion reduced to the divisor.** Let `W` be an open of the parameter space
over which `q⁻¹(W) → 𝔸^r_k` is flat and let `w` be a point of `q⁻¹(W)`, lying over the point
`s = q(w)` of `W`. If the divisor of the residue coordinates of `s` — that is, the fibre of `q`
over `s` — is smooth over `κ(s)` at the point of it that `w` comes from, then `q` is smooth at
`w`.

This is the whole of the passage from the divisor to the morphism in the proof of
[Stacks, Tag 0FD6]: the fibre of `q` over `s` is the divisor `H_a` of the coordinate tuple of `s`
(`Stacks.Bertini.FamilyDivisors.parameterPoint_residueCoord` together with
`Stacks.Bertini.FamilyDivisors.isPullback_universalFamilyMap`), the point `w` is in the image of
that fibre, and smoothness of the fibre at a point propagates to smoothness of `q` there because
`q` is flat over `W`
(`Stacks.Bertini.FamilyDivisors.mem_smoothLocus_of_isPullback_of_mem_smoothLocus`). What is left
to establish for the Jacobian criterion is therefore a statement about the divisor only, with no
fibre product, no base change and no flatness in it. -/
theorem mem_smoothLocus_of_mem_smoothLocus_residueCoordDivisor [Smooth D.toBase]
    (W : D.parameterBase.Opens) (hflat : Flat (D.universalFamilyMapOver W))
    (w : (D.universalDivisorSchemeOver W).toScheme)
    (hsm : ∀ z : D.residueCoordDivisor ((D.universalFamilyMapOver W).base w),
      (D.specializedToUniversal _
          (D.residueCoord ((D.universalFamilyMapOver W).base w))).base z =
        (D.universalDivisorSchemeOver W).ι.base w →
      z ∈ (D.residueCoordDivisorToBase ((D.universalFamilyMapOver W).base w)).smoothLocus) :
    w ∈ (D.universalFamilyMapOver W).smoothLocus := by
  set s := (D.universalFamilyMapOver W).base w with hs
  set K := ↥(D.parameterBase.residueField s) with hK
  set a := D.residueCoord s with hadef
  have hpt : D.parameterPoint a = D.parameterBase.fromSpecResidueField s :=
    D.parameterPoint_residueCoord s
  have ha : ∀ p : Spec (.of K), D.parameterPoint a p ∈ W := by
    intro p
    rw [hpt, Scheme.fromSpecResidueField_apply]
    exact w.2
  have hsq := D.isPullback_universalFamilyMap K a
  have hrange : Set.range (D.specializedToUniversal K a).base =
      D.universalFamilyMap.base ⁻¹' Set.range (D.parameterPoint a).base := by
    simpa using Scheme.image_preimage_eq_of_isPullback hsq.flip Set.univ
  have hmem : (D.universalDivisorSchemeOver W).ι.base w ∈
      Set.range (D.specializedToUniversal K a).base := by
    rw [hrange, hpt]
    change D.universalFamilyMap.base _ ∈
      Set.range (D.parameterBase.fromSpecResidueField s).base
    rw [show Set.range (D.parameterBase.fromSpecResidueField s).base = {s} from
      Scheme.range_fromSpecResidueField s]
    rfl
  obtain ⟨z, hz⟩ := hmem
  have hfinal := D.mem_smoothLocus_of_isPullback_of_mem_smoothLocus W hflat a ha
    (D.specializedToUniversal K a) _ hsq z (hsm z hz)
  rw [hz] at hfinal
  rw [D.smoothLocus_universalFamilyMapOver W]
  exact hfinal

end Stacks.Bertini.FamilyDivisors

end
