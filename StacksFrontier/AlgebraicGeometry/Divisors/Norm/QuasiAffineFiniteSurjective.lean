module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.FunctionFieldDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree

/-!
# Quasi-affineness descends along a finite surjective morphism

Let `f : X ⟶ Y` be a finite surjective morphism of schemes with `X` quasi-affine. Then `Y` is
quasi-affine as soon as either `f` is finite locally free, or `Y` is integral and normal.

In both cases the point is to produce a norm for `f`, or for a morphism close enough to `f`, and
then quote `Stacks.Divisors.isQuasiAffine_of_isFinite_of_hasNormOfDegree` (Tag 0BD1).

For a finite locally free `f` the degree need not be constant, so there is no norm on the nose;
but the target decomposes into the open and closed loci `Y_d` of constant degree
(`Stacks.Morphisms.exists_isClopenDecomposition_isFiniteLocallyFreeOfRank`, Tag 04MH), and over
each of those `f` has the determinant norm of degree `d` of Tag 0BD2. So each `Y_d` is
quasi-affine, and `Y` is covered by affine basic opens of *its own* global sections because a
section over the clopen `Y_d` extends by zero.

For an integral normal `Y` the morphism `f` need not carry a norm, because `X` need not be
integral. Replace it by one that does: pick a point `x` of `X` over the generic point of `Y` and
let `X'` be the irreducible component of `X` through `x`, with its reduced induced structure.
Then `X'` is integral, the composite `X' ⟶ X ⟶ Y` is finite, and it is surjective because the
image of the irreducible component is a closed set containing the generic point of `Y`. So
`Stacks.Divisors.exists_norm_of_finite_surjective_of_normal` (Tag 0BD3) supplies a norm of
degree `[R(X') : R(Y)]` for it, and that degree is positive because the source is nonempty.

## Main results

* `Stacks.Divisors.isQuasiAffine_of_isFiniteLocallyFree_surjective`: quasi-affineness descends
  along a finite locally free surjective morphism.
* `Stacks.Divisors.isQuasiAffine_of_isFinite_surjective_of_isNormal`: quasi-affineness descends
  along a finite surjective morphism onto an integral normal scheme.

## Implementation notes

The irreducible component is cut out as the subscheme of the vanishing ideal of its closure
(`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`), which is reduced by
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` and irreducible
because its support is the component; those two give integrality.

Extension by zero across a clopen is
`Stacks.Divisors.exists_restrict_eq_and_restrict_compl_eq_zero` below: the open and its complement
are two disjoint opens covering the scheme, so the sheaf condition glues the given section to the
zero section.

## References

* [Stacks Project, Tag 0BD5](https://stacks.math.columbia.edu/tag/0BD5)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 0BD3](https://stacks.math.columbia.edu/tag/0BD3)
* [Stacks Project, Tag 04MH](https://stacks.math.columbia.edu/tag/04MH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

/-- A section over an open subset which is also closed extends by zero to a global section:
there is a global section restricting to the given one on the open and to zero on its
complement. -/
theorem exists_restrict_eq_and_restrict_compl_eq_zero {Y : Scheme.{u}} (U : Y.Opens)
    (hU : IsClosed (U : Set Y)) (s : Γ(Y, U)) :
    ∃ t : Γ(Y, ⊤), Y.presheaf.map (homOfLE (le_top (a := U))).op t = s ∧
      Y.presheaf.map (homOfLE (le_top (a := (⟨(U : Set Y)ᶜ, hU.isOpen_compl⟩ : Y.Opens)))).op t
        = 0 := by
  set Uc : Y.Opens := ⟨(U : Set Y)ᶜ, hU.isOpen_compl⟩ with hUc
  set V : Bool → Y.Opens := fun b => if b then U else Uc with hV
  have hcover : (⨆ b, V b) = ⊤ := by
    refine le_antisymm le_top fun y _ => Opens.mem_iSup.mpr ?_
    by_cases hyU : y ∈ U
    · exact ⟨true, by simpa [hV] using hyU⟩
    · exact ⟨false, by simp [hV, hUc, hyU]⟩
  have hdisj : V false ⊓ V true = ⊥ ∧ V true ⊓ V false = ⊥ := by
    constructor <;> (apply Opens.ext; ext y; simp [hV, hUc])
  set sf : ∀ b : Bool, Γ(Y, V b) := fun b => Bool.rec 0 s b with hsf
  have hcompat : TopCat.Presheaf.IsCompatible Y.presheaf V sf := by
    intro b c
    match b, c with
    | false, false => rfl
    | true, true => rfl
    | false, true =>
        have : Subsingleton Γ(Y, V false ⊓ V true) := by rw [hdisj.1]; infer_instance
        exact Subsingleton.elim _ _
    | true, false =>
        have : Subsingleton Γ(Y, V true ⊓ V false) := by rw [hdisj.2]; infer_instance
        exact Subsingleton.elim _ _
  obtain ⟨t₀, ht₀, -⟩ := Y.IsSheaf.isSheafUniqueGluing V sf hcompat
  have key : ∀ b, Y.presheaf.map (homOfLE (le_top (a := V b))).op
      (Y.presheaf.map (eqToHom hcover.symm).op t₀) = sf b := fun b => by
    rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE (le_top (a := V b)) ≫ eqToHom hcover.symm) (Opens.leSupr V b)]
    exact ht₀ b
  exact ⟨_, key true, key false⟩

/-- The nonvanishing locus of an extension by zero across a clopen `U` is the image of the
nonvanishing locus of the original section: the extension vanishes identically off `U`, so its
nonvanishing locus lies in `U`, where it agrees with the given section. -/
theorem ι_image_basicOpen_eq_basicOpen_of_extension {Y : Scheme.{u}} (U : Y.Opens)
    (hU : IsClosed (U : Set Y)) (r : Γ(U.toScheme, ⊤)) (t : Γ(Y, ⊤))
    (ht : Y.presheaf.map (homOfLE (le_top (a := U))).op t = U.topIso.hom r)
    (htc : Y.presheaf.map
      (homOfLE (le_top (a := (⟨(U : Set Y)ᶜ, hU.isOpen_compl⟩ : Y.Opens)))).op t = 0) :
    U.ι ''ᵁ U.toScheme.basicOpen r = Y.basicOpen t := by
  have hbot : (⟨(U : Set Y)ᶜ, hU.isOpen_compl⟩ : Y.Opens) ⊓ Y.basicOpen t = ⊥ := by
    rw [← Scheme.basicOpen_res (X := Y) (f := t)
      (homOfLE (le_top (a := (⟨(U : Set Y)ᶜ, hU.isOpen_compl⟩ : Y.Opens)))).op, htc,
      Scheme.basicOpen_zero]
  have hle : Y.basicOpen t ≤ U := fun z hz => by
    by_contra hzU
    exact absurd (show z ∈ (⊥ : Y.Opens) from hbot ▸ ⟨hzU, hz⟩) (by simp)
  have hinv : U.topIso.inv (U.topIso.hom r) = r := by
    rw [← ConcreteCategory.comp_apply, U.topIso.hom_inv_id, ConcreteCategory.id_apply]
  have h1 := Scheme.Opens.ι_image_basicOpen_topIso_inv (X := Y) (U := U) (U.topIso.hom r)
  rw [hinv] at h1
  rw [h1, ← ht, Scheme.basicOpen_res, inf_eq_right.mpr hle]

/-- **Stacks Project, Tag 0BD5, case (2).** Quasi-affineness descends along a finite surjective
morphism onto an integral normal scheme. -/
@[stacks 0BD5 "integral normal target case"]
theorem isQuasiAffine_of_isFinite_surjective_of_isNormal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsIntegral Y] [IsNormal Y] [Scheme.IsQuasiAffine X] :
    Scheme.IsQuasiAffine Y := by
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  set C : Set X := irreducibleComponent x with hC
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨C, isClosed_irreducibleComponent⟩ with hI
  set X' : Scheme.{u} := I.subscheme with hX'
  set i : X' ⟶ X := I.subschemeι with hi
  have hsupport : (I.support : Set X) = C := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IrreducibleSpace X' :=
    Subtype.irreducibleSpace (hsupport.symm ▸ isIrreducible_irreducibleComponent)
  have : IsReduced X' :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsIntegral X' :=
    (isIntegral_iff_irreducibleSpace_and_isReduced X').2 ⟨inferInstance, inferInstance⟩
  have : IsFinite i := IsFinite.instOfIsClosedImmersion i
  have : IsFinite (i ≫ f) := IsFinite.instCompScheme i f
  have himage : f.base '' C = Set.univ :=
    Set.eq_univ_of_subset
      (closure_minimal (Set.singleton_subset_iff.mpr ⟨x, mem_irreducibleComponent, hx⟩)
        (f.isClosedMap C isClosed_irreducibleComponent))
      (genericPoint_closure Y)
  have : Surjective (i ≫ f) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x₀, hx₀C, rfl⟩ : y ∈ f.base '' C := himage.symm ▸ Set.mem_univ y
    obtain ⟨x₁, hx₁⟩ :=
      Set.mem_range.mp ((I.range_subschemeι).symm ▸ (hsupport.symm ▸ hx₀C))
    exact ⟨x₁, by simpa [hi] using congrArg f.base hx₁⟩
  have : Scheme.IsQuasiAffine X' := by
    have : CompactSpace X' := by
      rw [← isCompact_univ_iff]
      exact i.isClosedEmbedding.isCompact_preimage isCompact_univ
    exact Scheme.IsQuasiAffine.of_isImmersion i
  obtain ⟨φ, -, hN⟩ := exists_norm_of_finite_surjective_of_normal (i ≫ f)
  have : Algebra Y.functionField X'.functionField := φ.toAlgebra
  obtain ⟨N⟩ := hN
  exact isQuasiAffine_of_isFinite_of_hasNormOfDegree (i ≫ f)
    (pos_of_morphismNorm (i ≫ f) N (genericPoint X')) ⟨N⟩

/-- **Stacks Project, Tag 0BD5, case (1).** Quasi-affineness descends along a finite locally
free surjective morphism. -/
@[stacks 0BD5 "finite locally free case"]
theorem isQuasiAffine_of_isFiniteLocallyFree_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [Morphisms.IsFiniteLocallyFree f] [Scheme.IsQuasiAffine X] :
    Scheme.IsQuasiAffine Y := by
  have : CompactSpace Y := by
    rw [← isCompact_univ_iff, ← Set.range_eq_univ.mpr f.surjective, ← Set.image_univ]
    exact isCompact_univ.image f.continuous
  obtain ⟨U, hdec, hrank⟩ :=
    Morphisms.exists_isClopenDecomposition_isFiniteLocallyFreeOfRank f
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Y fun y => ?_
  obtain ⟨d, hyd⟩ := hdec.exists_mem y
  have : Morphisms.IsFiniteLocallyFreeOfRank (f ∣_ U d) d := hrank d
  have : Morphisms.IsFiniteLocallyFree (f ∣_ U d) :=
    Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (f ∣_ U d) d
  have : IsFinite (f ∣_ U d) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (isPullback_morphismRestrict f (U d)).flip ‹IsFinite f›
  have : Surjective (f ∣_ U d) := IsZariskiLocalAtTarget.restrict ‹Surjective f› (U d)
  -- the source of the restriction is a clopen subscheme of `X`, hence quasi-affine
  have : CompactSpace (f ⁻¹ᵁ U d).toScheme :=
    isCompact_iff_compactSpace.mp (((hdec.isClopen d).1.preimage f.continuous).isCompact)
  have : Scheme.IsQuasiAffine (f ⁻¹ᵁ U d).toScheme :=
    Scheme.IsQuasiAffine.of_isImmersion (f ⁻¹ᵁ U d).ι
  -- the degree is positive because the restriction is surjective onto a nonempty open
  obtain ⟨z, -⟩ := (f ∣_ U d).surjective (⟨y, hyd⟩ : (U d).toScheme)
  have hd : 0 < d :=
    pos_of_morphismNorm (f ∣_ U d)
      { toMorphismNormMap := (finiteLocallyFreeNorm (f ∣_ U d)).toMorphismNormMap
        app_pullback := (finiteLocallyFreeNorm (f ∣_ U d)).app_pullback d } z
  obtain ⟨N, -⟩ := finiteLocallyFreeNormOfRank (f ∣_ U d) d hd
  have : Scheme.IsQuasiAffine (U d).toScheme :=
    isQuasiAffine_of_isFinite_of_hasNormOfDegree (f ∣_ U d) hd ⟨N⟩
  -- an affine basic open of `U d` around `y`, and its extension by zero to a global section
  obtain ⟨-, ⟨r, hr, rfl⟩, hyr, -⟩ :=
    Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen (U d).toScheme)
      (show (⟨y, hyd⟩ : (U d).toScheme) ∈ (⊤ : (U d).toScheme.Opens) from trivial)
  obtain ⟨t, ht, htc⟩ := exists_restrict_eq_and_restrict_compl_eq_zero (U d)
    (hdec.isClopen d).1 ((U d).topIso.hom r)
  have himage := ι_image_basicOpen_eq_basicOpen_of_extension (U d) (hdec.isClopen d).1 r t ht htc
  refine ⟨t, ?_, ?_⟩ <;> rw [← himage]
  · exact hr.image_of_isOpenImmersion (U d).ι
  · exact ⟨⟨y, hyd⟩, hyr, rfl⟩

end Stacks.Divisors

end
