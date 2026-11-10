module

public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationCharacterization.Basic
public import StacksFrontier.AlgebraicGeometry.SeminormalizationAffineInitial.Basic
public import StacksFrontier.AlgebraicGeometry.SeminormalizationIsoIff.Basic

/-!
# Characterization of the seminormalization

Let `A → B` be a map of commutative rings inducing a universal homeomorphism on spectra and
isomorphisms on all residue fields.  The canonical map from `B` to the seminormalization of `A`
is an isomorphism exactly when `B` is seminormal.

## Main results

* `AlgebraicGeometry.isSeminormalizationCandidateAlgebra_squareCubeAlgebra`: adjoining a square
  and cube root of a pair `x ^ 3 = y ^ 2` to a subintegral `A`-algebra leaves it subintegral.
* `AlgebraicGeometry.isSeminormalRing_of_isTerminal`: a terminal subintegral `A`-algebra is
  seminormal.
* `AlgebraicGeometry.isIso_lift_to_seminormalization_iff_isSeminormalRing`: the canonical map
  from `B` to the seminormalization of `A` is an isomorphism exactly when `B` is seminormal.

## Implementation notes

The canonical map is the lift from the terminal-object property of the seminormalization,
`AlgebraicGeometry.seminormalizationAlgebraObject_isTerminal`.  Expressing it in the category
of `A`-algebras retains its compatibility with the given map from `A`.

Terminality forces seminormality because the square-and-cube equation has a solution after the
explicit elementary extension `AlgebraicGeometry.SquareCubeAlgebra`, which is again a universal
homeomorphism over `A` inducing isomorphisms on all residue fields, hence again an object of the
category; the unique map back to the terminal object produces the solution and the unique map
forward makes it unique.  This is the seminormalization half of the argument whose absolute
weak normalization half is
`AlgebraicGeometry.isAbsolutelyWeaklyNormalRing_of_isTerminal`, and the four composition
lemmas it shares with that half are reused from there rather than restated.

For the converse, the canonical map is a ring map out of a seminormal ring whose spectrum map
is a universal homeomorphism inducing isomorphisms on all residue fields, so
`AlgebraicGeometry.bijective_of_universalHomeomorphism_of_residueFieldMap_isIso` — the affine,
ring-level form of the corresponding implication of Tag 0EUS — makes it
bijective, and the resulting algebra equivalence is an isomorphism of the category because the
category is full.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUR is used: `A` and `B` are arbitrary commutative rings,
with no Noetherian, affineness or reducedness assumption.

## What is not done

Nothing here is about schemes other than spectra of rings.  The corresponding statement for the
initial object of `AlgebraicGeometry.SeminormalizationCategory X` at a general scheme `X` is Tag
0EUS's `seminormalization_iso_iff` label; the implication proved there,
`AlgebraicGeometry.isIso_initialTo_iff_isSeminormal_of_isSeminormal_initial`, still carries the
seminormality of the initial object as a hypothesis, and discharging it needs the scheme-level
rather than the ring-level terminal object.

## References

* [Stacks Project, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL)
* [Stacks Project, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Adjoining a common square and cube root of a pair `x ^ 3 = y ^ 2` to a subintegral
`A`-algebra gives another subintegral `A`-algebra. -/
public theorem isSeminormalizationCandidateAlgebra_squareCubeAlgebra
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (x y : R) (hxy : x ^ 3 = y ^ 2)
    (hR : IsSeminormalizationCandidateAlgebra A (CommAlgCat.of A R)) :
    IsSeminormalizationCandidateAlgebra A
      (CommAlgCat.of A (SquareCubeAlgebra R x y)) := by
  change UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op) ∧
    (∀ z : Spec (.of R), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op).residueFieldMap z)) at hR
  exact ⟨universalHomeomorphism_composite A R _ hR.1
      (squareCubeSpecMap_universalHomeomorphism R x y hxy),
    residueFieldIsomorphisms_composite A R _ hR.2
      (isIso_residueFieldMap_squareCubeSpecMap R x y hxy)⟩

/-- A terminal subintegral `A`-algebra is seminormal. -/
public theorem isSeminormalRing_of_isTerminal
    (A : Type u) [CommRing A]
    (R : SeminormalizationAlgebraCategory A)
    (hR : IsTerminal R) :
    IsSeminormalRing R.1 := fun x y hxy =>
  terminal_squareCube_existsUnique A (IsSeminormalizationCandidateAlgebra A) R hR x y
    (isSeminormalizationCandidateAlgebra_squareCubeAlgebra A R.1 x y hxy R.property)

/-- **Stacks 0EUR.** A subintegral `A`-algebra is the seminormalization of `A` precisely when
its underlying ring is seminormal. -/
@[stacks 0EUR "sn_characterization"]
public theorem isIso_lift_to_seminormalization_iff_isSeminormalRing
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (huniv : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    IsIso ((seminormalizationAlgebraObject_isTerminal A).from
      (⟨CommAlgCat.of A B, huniv, hres⟩ : SeminormalizationAlgebraCategory A)) ↔
      IsSeminormalRing B := by
  let C := IsSeminormalizationCandidateAlgebra A
  let T : SeminormalizationAlgebraCategory A := ⟨CommAlgCat.of A B, huniv, hres⟩
  let S := seminormalizationAlgebraObject A
  let terminal := seminormalizationAlgebraObject_isTerminal A
  let f : T ⟶ S := terminal.from T
  change IsIso f ↔ IsSeminormalRing B
  have hS : IsSeminormalRing S.obj := isSeminormalRing_of_isTerminal A S terminal
  refine ⟨fun hf => ?_, fun hB => ?_⟩
  · let e : B ≃ₐ[A] S.obj := CommAlgCat.algEquivOfIso ((ObjectProperty.ι C).mapIso (asIso f))
    exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv e.symm.toRingEquiv hS
  · let phi : B →ₐ[A] S.obj := f.hom.hom
    let F : B →+* S.obj := phi.toRingHom
    let uAB := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
    let uAS := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S.obj)).op
    let uF := Scheme.Spec.map (CommRingCat.ofHom F).op
    have hring : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom F =
        CommRingCat.ofHom (algebraMap A S.obj) := by
      rw [← CommRingCat.ofHom_comp]
      ext a
      exact phi.commutes a
    have hspec : uF ≫ uAB = uAS := by
      simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp] using
        congrArg (fun q => Scheme.Spec.map q.op) hring
    have hpost : MorphismProperty.HasOfPostcompProperty
        (@UniversalHomeomorphism.{u}) (@UniversalHomeomorphism.{u}) :=
      universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty
    have hUF : UniversalHomeomorphism uF := by
      apply MorphismProperty.of_postcomp _ uF uAB huniv
      rw [hspec]
      exact seminormalization_universalHomeomorphism A
    have hresF : ∀ z : Spec (CommRingCat.of S.obj), IsIso (uF.residueFieldMap z) := fun z => by
      have hc : IsIso ((uF ≫ uAB).residueFieldMap z) := by
        rw [hspec]
        exact seminormalization_inducesResidueFieldIsomorphisms A z
      rw [Scheme.residueFieldMap_comp] at hc
      have : IsIso (uAB.residueFieldMap (uF z) ≫ uF.residueFieldMap z) := hc
      exact IsIso.of_isIso_comp_left (uAB.residueFieldMap (uF z)) (uF.residueFieldMap z)
    have : _root_.IsReduced S.obj := seminormalRing_isReduced hS
    have hbij : Function.Bijective F :=
      bijective_of_universalHomeomorphism_of_residueFieldMap_isIso F hB hUF hresF
    let e : B ≃ₐ[A] S.obj := AlgEquiv.ofBijective phi hbij
    let g : S ⟶ T := ObjectProperty.homMk (CommAlgCat.ofHom e.symm.toAlgHom)
    refine ⟨⟨g, ?_, ?_⟩⟩ <;>
      refine ObjectProperty.hom_ext C (CommAlgCat.hom_ext ?_) <;> ext z
    · exact e.left_inv z
    · exact e.right_inv z

end AlgebraicGeometry

end
