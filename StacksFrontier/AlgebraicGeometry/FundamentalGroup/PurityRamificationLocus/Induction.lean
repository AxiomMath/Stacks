module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.AnyDimension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.EtaleAtDimensionTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.ExcellentBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.ApproximationProperty.Core
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The induction of purity of the ramification locus

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes, locally of finite type, let `x` be a
point of `X` whose local ring is normal of dimension at least one and with `𝒪_{Y,f x}` regular,
and suppose `f` is étale at every generization of `x` whose local ring has dimension one.
[Stacks, Tag 0EA4] — purity of the ramification locus, attributed to Gabber — asserts that `f` is
étale at `x`. This file carries out the source's induction on `d = dim 𝒪_{X,x}`. The induction
needs two inputs: the case `d = 2` over an excellent regular local base, [Stacks, Tag 0EA3],
which is `AlgebraicGeometry.etaleAt_of_etaleAt_outside_closure_of_ringKrullDim_eq_two` in
`PurityRamification.EtaleAtDimensionTwo`, and purity of the branch locus, [Stacks, Tag 0BMB],
which is `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne` in
`PurityBranchLocus.AnyDimension`.

## Main results

* `AlgebraicGeometry.etaleAt_of_etaleAt_codimensionOne_over_excellent`: the induction over an
  excellent regular local base.
* `AlgebraicGeometry.etaleAt_of_etaleAt_codimensionOne`: [Stacks, Tag 0EA4], purity of the
  ramification locus.

## The structure of the induction

The induction is on `d = dim 𝒪_{X,x}`.

For `d = 1` the conclusion is the hypothesis on the one-dimensional generizations, applied at `x`
itself.

For `d ≥ 2` every proper generization `z` of `x` is handled first. Its local ring is a
localization of `𝒪_{X,x}`, hence normal, and its dimension is strictly smaller; if that dimension
is positive the induction hypothesis applies to `z`, and if it is zero then `z` is a generization
of a one-dimensional generization of `x`, where the standing hypothesis applies, and étaleness
spreads to generizations because it is a condition on an open set. So the morphism is étale at
every point of the source other than `x` that specializes to `x`.

Two base changes follow, neither of which changes étaleness at the point in question, both being
flat: first to `Spec 𝒪_{Y,y}`, so that the target is the spectrum of a regular local ring, and
then to the spectrum of its completion, which is again regular, and excellent because it is a
complete local ring. The source of the second base change has normal local ring at the point
above `x` by Serre's criterion along a flat map: it is regular in codimension `≤ 1`, by the
étaleness already established there, and the target local ring is normal.

Over an excellent regular local base one further flat base change puts the image of `x` at the
closed point, and then the dimension splits the argument.

For `d = 2` the conclusion is [Stacks, Tag 0EA3], after shrinking to an affine open on which the
morphism is étale away from the closure of `x`.

For `d > 2` the base is cut by a parameter `t` of the regular local ring `B` outside the square of
its maximal ideal and with nonzero image in `𝒪_{X,x}`, which is possible because `B` has positive
dimension and the structure map `B →+* 𝒪_{X,x}` is injective, that injectivity coming from
étaleness at a one-dimensional generization. Then `B ⧸ (t)` is again regular, excellent, and
Nagata, so the normalization of the cut source is finite; the local ring of the cut source at the
point above `x` has dimension `d - 1 ≥ 2`, and a point of the normalization above it has local
dimension at least two and strictly less than `d`, so the induction hypothesis applies there. The
residue field at that point is therefore finite over the residue field of the closed point of
`B ⧸ (t)`, hence the residue field at `x` is finite over that of `y`, which makes `x` a closed
point of its fibre; being also a generic point of the fibre, by the étaleness at its proper
generizations, the morphism is quasi-finite at `x`. Purity of the branch locus,
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne`, then applies: its
dimension hypothesis is the dimension formula over the excellent base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Finiteness of residue field extensions along a composite -/

/-- Finiteness of the residue field extension is transitive along a composite. -/
theorem finite_residueField_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (f x)) (X.residueField x))
    (hg : letI := (g.residueFieldMap (f x)).hom.toAlgebra
      Module.Finite (Z.residueField (g (f x))) (Y.residueField (f x))) :
    letI := ((f ≫ g).residueFieldMap x).hom.toAlgebra
    Module.Finite (Z.residueField ((f ≫ g) x)) (X.residueField x) := by
  let _ : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let _ : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      congrArg (fun φ : CommRingCat.of (Z.residueField (g (f x))) ⟶
        CommRingCat.of (X.residueField x) => φ.hom a) (Scheme.residueFieldMap_comp f g x)
  let _ : Module.Finite (Z.residueField (g (f x))) (Y.residueField (f x)) := hg
  let _ : Module.Finite (Y.residueField (f x)) (X.residueField x) := hf
  show Module.Finite (Z.residueField (g (f x))) (X.residueField x)
  exact Module.Finite.trans (Y.residueField (f x)) (X.residueField x)

/-- If the residue field extension of a composite is finite, so is that of the second factor at
the image point. -/
theorem finite_residueField_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hfinite : letI := ((f ≫ g).residueFieldMap x).hom.toAlgebra
      Module.Finite (Z.residueField ((f ≫ g) x)) (X.residueField x)) :
    letI := (g.residueFieldMap (f x)).hom.toAlgebra
    Module.Finite (Z.residueField (g (f x))) (Y.residueField (f x)) := by
  let _ : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let _ : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      congrArg (fun φ : CommRingCat.of (Z.residueField (g (f x))) ⟶
        CommRingCat.of (X.residueField x) => φ.hom a) (Scheme.residueFieldMap_comp f g x)
  let _ : Module.Finite (Z.residueField (g (f x))) (X.residueField x) := hfinite
  exact Module.Finite.left (Z.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x)

/-! ### The case of dimension two -/

/-- The case `dim 𝒪_{X,x} = 2` of the induction over an excellent regular local base: shrink to
an affine open neighbourhood of `x` on which the morphism is étale away from the closure of `x`,
and apply [Stacks, Tag 0EA3] there. -/
theorem etaleAt_of_etaleAt_generizations_of_ringKrullDim_stalk_eq_two
    {A : Type u} [CommRing A] [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x)) (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (het : ∀ z : X, z ⤳ x → z ≠ x → EtaleAt f z) : EtaleAt f x := by
  obtain ⟨U, hU, hxU, hUet⟩ := exists_isAffineOpen_etaleAt_outside_closure f x het
  have _ : IsAffine U := hU
  have hn : IsNormalRing (U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U.toScheme)) :=
    IsNormalRing.congr (U.stalkIso (⟨x, hxU⟩ : U.toScheme)).commRingCatIsoToRingEquiv.symm hX
  have hd : ringKrullDim (U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U.toScheme)) = 2 :=
    (U.stalkIso (⟨x, hxU⟩ : U.toScheme)).commRingCatIsoToRingEquiv.ringKrullDim.trans hdim
  refine etaleAt_of_open_precomp U.ι f (⟨x, hxU⟩ : U.toScheme)
    (etaleAt_of_etaleAt_outside_closure_of_ringKrullDim_eq_two hA (U.ι ≫ f)
      (⟨x, hxU⟩ : U.toScheme) hn hd ?_)
  intro z hz
  refine etaleAt_comp_of_etale U.ι f z (hUet z.1 z.2 fun hcl ↦ hz ?_)
  exact specializes_iff_mem_closure.mp (U.ι.isEmbedding.specializes_iff.mp
    (specializes_iff_mem_closure.mpr hcl))

/-! ### The induction over an excellent regular local base -/

/-- **Purity of the ramification locus over an excellent regular local base.** Let `A` be an
excellent regular local ring, let `f : X ⟶ Spec A` be locally of finite type and let `x : X` have
normal local ring of dimension at least one. If `f` is étale at every generization of `x` whose
local ring has dimension one, then `f` is étale at `x`.

This is the source's induction on `d = dim 𝒪_{X,x}`, quoting [Stacks, Tag 0EA3] from
`AlgebraicGeometry.etaleAt_of_etaleAt_outside_closure_of_ringKrullDim_eq_two` and
[Stacks, Tag 0BMB] from
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne`; see the module
docstring. -/
@[sga "1 X 3.1" "special case"]
theorem etaleAt_of_etaleAt_codimensionOne_over_excellent
    {A : Type u} [CommRing A] [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X) (hX : IsNormalRing (X.presheaf.stalk x))
    (hpositive : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hetale : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 → EtaleAt f z) :
    EtaleAt f x := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨d, hd⟩ :=
    Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk x)
  induction d using Nat.strong_induction_on generalizing A X with
  | h d ih =>
    by_cases hdim : ringKrullDim (X.presheaf.stalk x) = 1
    · exact hetale x (specializes_refl x) hdim
    have hpunctured : ∀ z : X, z ⤳ x → z ≠ x → EtaleAt f z := by
      intro z hz hne
      by_cases hzero : ringKrullDim (X.presheaf.stalk z) = 0
      · exact etaleAt_generization_of_ringKrullDim_stalk_eq_zero f hX.of_isLocalRing.1
          hpositive hetale hz hzero
      obtain ⟨e, he⟩ :=
        Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk z)
      have hlt : e < d := by
        have hh := ringKrullDim_stalk_lt_of_specializes hz hne
        rw [hd, he] at hh
        exact_mod_cast hh
      have hpos : 1 ≤ ringKrullDim (X.presheaf.stalk z) := by
        rw [he]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hh ↦ hzero (by simp only [he, hh, Nat.cast_zero]))
      exact ih e hlt hA f z (isNormalRing_stalk_of_specializes hz hX) hpos
        (fun w hw hdw ↦ hetale w (hw.trans hz) hdw) inferInstance he
    -- Base change so that the image of `x` is the closed point of the base.
    let B : Type u := (Spec (.of A)).presheaf.stalk (f x)
    have _ : IsRegularLocalRing B := isRegularLocalRing_stalk_spec A (f x)
    let _ : Algebra A B := (StructureSheaf.toStalk A (f x)).hom.toAlgebra
    have _ : (f x).asIdeal.IsPrime := (f x).isPrime
    have _ : IsLocalization.AtPrime B (f x).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A (f x)
    have _ : Algebra.EssFiniteType A B := .of_isLocalization B (f x).asIdeal.primeCompl
    have hB : IsExcellent B :=
      (isQuasiExcellent_and_isExcellent_of_essFiniteType (R := A) (S := B)).2 hA
    let g := (Spec (.of A)).fromSpecStalk (f x)
    have _ : Flat g := flat_fromSpecStalk (Spec (.of A)) (f x)
    obtain ⟨x₀, hx₀, hy₀⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g)
      x (IsLocalRing.closedPoint B) (by simp [g, B])
    let j := pullback.fst f g
    let f₀ : pullback f g ⟶ Spec (.of B) := pullback.snd f g
    change j x₀ = x at hx₀
    have hback : EtaleAt f₀ x₀ → EtaleAt f x := by
      have he := etaleAt_pullback_fromSpecStalk_iff f (f x) x₀
      change EtaleAt f₀ x₀ ↔ EtaleAt f (j x₀) at he
      rw [hx₀] at he
      exact he.mp
    apply hback
    have _ : IsLocallyNoetherian (pullback f g) := LocallyOfFiniteType.isLocallyNoetherian f₀
    have hpunctured₀ : ∀ z : (pullback f g : Scheme.{u}), z ⤳ x₀ → z ≠ x₀ → EtaleAt f₀ z := by
      intro z hz hne
      refine (etaleAt_pullback_fromSpecStalk_iff f (f x) z).mpr (hpunctured (j z) ?_ ?_)
      · simpa only [hx₀] using hz.map j.continuous
      · exact fun heq ↦ hne (j.isEmbedding.injective (heq.trans hx₀.symm))
    have _ := isIso_stalkMap_of_flat_isPreimmersion j x₀
    have hnormal₀ : IsNormalRing ((pullback f g).presheaf.stalk x₀) :=
      IsNormalRing.congr (asIso (j.stalkMap x₀)).commRingCatIsoToRingEquiv (hx₀.symm ▸ hX)
    have hd₀ : ringKrullDim ((pullback f g).presheaf.stalk x₀) = d :=
      (asIso (j.stalkMap x₀)).commRingCatIsoToRingEquiv.ringKrullDim.symm.trans
        (by rw [hx₀]; exact hd)
    have hd2 : 2 ≤ d := by
      have hp : 1 ≤ d := by exact_mod_cast (hd ▸ hpositive)
      have hn : d ≠ 1 := fun hh ↦ hdim (by simp only [hd, hh, Nat.cast_one])
      omega
    by_cases htwo : d = 2
    · exact etaleAt_of_etaleAt_generizations_of_ringKrullDim_stalk_eq_two hB f₀ x₀ hnormal₀
        (by simpa only [htwo, Nat.cast_ofNat] using hd₀) hpunctured₀
    -- `d > 2`: cut the base by a parameter and normalize.
    have hcodim₀ : ∀ z : (pullback f g : Scheme.{u}), z ⤳ x₀ →
        ringKrullDim ((pullback f g).presheaf.stalk z) = 1 → EtaleAt f₀ z := by
      intro z hz hdz
      refine hpunctured₀ z hz fun hzx ↦ ?_
      have he : (d : WithBot ℕ∞) = 1 := hd₀.symm.trans (hzx ▸ hdz)
      have hd1 : d = 1 := by exact_mod_cast he
      omega
    have hpositive₀ : 1 ≤ ringKrullDim ((pullback f g).presheaf.stalk x₀) := by
      rw [hd₀]
      exact_mod_cast (show 1 ≤ d by omega)
    obtain ⟨z, hz, hdz⟩ := exists_specializes_ringKrullDim_stalk_eq_one x₀ hpositive₀
    have hbasepos : 0 < ringKrullDim B := by
      have he := ringKrullDim_stalk_eq_of_etaleAt f₀ z (hcodim₀ z hz hdz)
      have hle := ringKrullDim_stalk_le_of_specializes (hz.map f₀.continuous)
      rw [← he, hdz, hy₀] at hle
      exact (by norm_num : (0 : WithBot ℕ∞) < 1).trans_le
        (hle.trans_eq (stalkClosedPointIso (.of B)).commRingCatIsoToRingEquiv.ringKrullDim)
    have _ : IsDomain B := IsRegularLocalRing.isDomain B
    have hφ : Function.Injective (toStalkStalkMap f₀ x₀) :=
      baseToStalk_injective_of_etaleAt_generization (A := B) f₀ hz (hcodim₀ z hz hdz)
    have _ : IsDomain ((pullback f g).presheaf.stalk x₀) := hnormal₀.of_isLocalRing.1
    obtain ⟨t, ht, ht2, htnz⟩ := exists_regular_parameter_notMem_sq_map_ne_zero (A := B)
      (toStalkStalkMap f₀ x₀) hφ hbasepos.ne'
    let C := B ⧸ Ideal.span {t}
    have _ : IsRegularLocalRing C := (quotient_isRegularLocalRing B t ht ht2).1
    have hC : IsExcellent C :=
      (isQuasiExcellent_and_isExcellent_of_essFiniteType (R := B) (S := C)).2 hB
    let q : Spec (.of C) ⟶ Spec (.of B) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t})))
    have _ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {t}) : B →+* C) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hqclosed : q (IsLocalRing.closedPoint C) = IsLocalRing.closedPoint B := Spec_closedPoint
    obtain ⟨x₂, hx₂, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f₀) (g := q)
      x₀ (IsLocalRing.closedPoint C) (hy₀.trans hqclosed.symm)
    let j₂ := pullback.fst f₀ q
    let f₂ := pullback.snd f₀ q
    change j₂ x₂ = x₀ at hx₂
    have _ : IsClosedImmersion q :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have _ : IsLocallyNoetherian (pullback f₀ q) := LocallyOfFiniteType.isLocallyNoetherian f₂
    have hslice : ringKrullDim ((pullback f₀ q).presheaf.stalk x₂) + 1 = d := by
      have hnz : toStalkStalkMap f₀ (j₂ x₂) t ∈
          nonZeroDivisors ((pullback f g).presheaf.stalk (j₂ x₂)) := by
        rw [hx₂]
        exact mem_nonZeroDivisors_iff_ne_zero.mpr htnz
      exact (ringKrullDim_stalk_pullback_quotient_add_one f₀ t x₂ hnz).trans
        ((congrArg (fun w ↦ ringKrullDim ((pullback f g).presheaf.stalk w)) hx₂).trans hd₀)
    obtain ⟨ds, hds⟩ := Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim
      ((pullback f₀ q).presheaf.stalk x₂)
    have hdsd : ds + 1 = d := by
      rw [hds] at hslice
      exact_mod_cast hslice
    have hds2 : 2 ≤ ringKrullDim ((pullback f₀ q).presheaf.stalk x₂) := by
      rw [hds]
      exact_mod_cast (show 2 ≤ ds by omega)
    have hNagataB : IsNagataScheme (Spec (.of B)) :=
      isNagataScheme_spec_of_isNagataRing B (isNagataRing_of_isQuasiExcellent hB.1)
    have hNagata : IsNagataScheme (pullback f₀ q) :=
      isNagataScheme_of_locallyOfFiniteType (j₂ ≫ f₀) hNagataB
    let hcomponents :=
      Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
        (pullback f₀ q) hNagata
    let n := Scheme.normalization (pullback f₀ q) hcomponents
    have _ : IsFinite n := Scheme.isFinite_normalization hNagata hcomponents
    have _ : IsLocallyNoetherian ((pullback f₀ q).normalizationScheme hcomponents) :=
      LocallyOfFiniteType.isLocallyNoetherian n
    obtain ⟨x₃, hx₃, hdim₃⟩ := exists_preimage_ringKrullDim_stalk_ge n n.isClosedMap
      (Scheme.surjective_normalization (pullback f₀ q) hcomponents).surj x₂ 2 hds2
    have _ : IsNormal ((pullback f₀ q).normalizationScheme hcomponents) :=
      Scheme.isNormal_normalizationScheme (pullback f₀ q) hcomponents
    have hn₃ : IsNormalRing
        (((pullback f₀ q).normalizationScheme hcomponents).presheaf.stalk x₃) :=
      (isNormal_iff_stalk_isNormalRing _).mp inferInstance x₃
    obtain ⟨dn, hdn⟩ := Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim
      (((pullback f₀ q).normalizationScheme hcomponents).presheaf.stalk x₃)
    have hdnd : dn < d := by
      have hle := ringKrullDim_stalk_le_of_quasiFiniteAt n x₃ (n.quasiFiniteAt x₃)
      rw [hx₃, hds, hdn] at hle
      have hdnds : dn ≤ ds := by exact_mod_cast hle
      omega
    have hpoint : (n ≫ j₂) x₃ = x₀ := by
      show j₂ (n x₃) = _
      rw [hx₃, hx₂]
    have he₃ : EtaleAt (n ≫ f₂) x₃ := by
      refine ih dn hdnd hC (n ≫ f₂) x₃ hn₃
        ((by norm_num : (1 : WithBot ℕ∞) ≤ 2).trans hdim₃) ?_ inferInstance hdn
      intro w hw hdw
      refine etaleAt_normalization_pullback_codimensionOne f₀ q
        (isRegularLocalRing_stalk_spec C) hcomponents x₃ hdim₃ ?_ w hw hdw
      show ∀ y : (pullback f g : Scheme.{u}), y ⤳ (n ≫ j₂) x₃ →
        y ≠ (n ≫ j₂) x₃ → EtaleAt f₀ y
      rw [hpoint]
      exact hpunctured₀
    have hfinite₃ := (isClosed_asFiber_iff_finite_residueField (n ≫ f₂) x₃).mp
      (quasiFiniteAt_of_etaleAt (n ≫ f₂) x₃ he₃).2.isClopen_singleton_asFiber.1
    have hfiniteComp := finite_residueField_comp (n ≫ f₂) q x₃ hfinite₃
      (residueField_finite_of_locallyQuasiFinite q ((n ≫ f₂) x₃))
    have heq : (n ≫ f₂) ≫ q = (n ≫ j₂) ≫ f₀ := by
      dsimp only [f₂, j₂]
      rw [Category.assoc, Category.assoc, pullback.condition]
    rw [heq] at hfiniteComp
    have hfinite₀ := finite_residueField_of_comp (n ≫ j₂) f₀ x₃ hfiniteComp
    rw [hpoint] at hfinite₀
    have hqf₀ :=
      quasiFiniteAt_of_finite_residueField_of_etaleAt_generizations f₀ x₀ hfinite₀ hpunctured₀
    exact etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne f₀ x₀ hnormal₀
      (isRegularLocalRing_stalk_spec B (f₀ x₀)) hqf₀
      (ringKrullDim_stalk_eq_of_quasiFiniteAt_over_excellent hB f₀ x₀ hy₀ hnormal₀ hφ hqf₀.2)
      hpositive₀
      (fun w hw hdw ↦ Stacks.Discriminant.unramifiedAt_of_etaleAt f₀ w (hcodim₀ w hw hdw))

/-! ### Purity of the ramification locus -/

/-- **[Stacks, Tag 0EA4], purity of the ramification locus.** Let `f : X ⟶ Y` be a morphism of
locally Noetherian schemes, let `x : X` and `y = f x`, and assume that (1) `𝒪_{X,x}` is normal of
dimension at least one, (2) `𝒪_{Y,y}` is regular, (3) `f` is locally of finite type, and (4) `f`
is étale at every specialization `x' ⤳ x` with `dim 𝒪_{X,x'} = 1`. Then `f` is étale at `x`.

The hypotheses are exactly the tag's own. "Normal" is `IsNormalRing` of the stalk (for a local
ring: a normal domain), "dimension" is `ringKrullDim`, and a specialization `x' ⤳ x` of the
source is Mathlib's `x' ⤳ x`, that is `x ∈ closure {x'}`.

The proof is the source's: the proper generizations of `x` are handled by induction on
`dim 𝒪_{X,x}`, base change to `Spec 𝒪_{Y,f x}` ([Stacks, Tag 0476]) and then to the spectrum of
its completion changes neither étaleness at the relevant point (both being flat) nor normality of
the local ring there (Serre's criterion), and over the complete — hence excellent — regular local
base the induction of `AlgebraicGeometry.etaleAt_of_etaleAt_codimensionOne_over_excellent`
applies, with [Stacks, Tag 0EA3] in dimension two and [Stacks, Tag 0BMB] above it. -/
@[stacks 0EA4 "the whole lemma: hypotheses (1) `𝒪_{X,x}` normal of dimension `≥ 1`, (2) \
`𝒪_{Y,f x}` regular, (3) `f` locally of finite type, (4) `f` étale at every `x' ⤳ x` with \
`dim 𝒪_{X,x'} = 1`; the conclusion is `EtaleAt f x`.",
  ega "IV 21.12.14" "more general",
  sga "1 X 3.1" "more general"]
theorem etaleAt_of_etaleAt_codimensionOne
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hpositive : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hetale : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → EtaleAt f x') :
    EtaleAt f x := by
  obtain ⟨d, hd⟩ :=
    Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk x)
  induction d using Nat.strong_induction_on generalizing X Y with
  | h d ih =>
    by_cases hdim : ringKrullDim (X.presheaf.stalk x) = 1
    · exact hetale x (specializes_refl x) hdim
    have hpunctured : ∀ x' : X, x' ⤳ x → x' ≠ x → EtaleAt f x' := by
      intro x' hspec hne
      by_cases hzero : ringKrullDim (X.presheaf.stalk x') = 0
      · exact etaleAt_generization_of_ringKrullDim_stalk_eq_zero f hX.of_isLocalRing.1
          hpositive hetale hspec hzero
      obtain ⟨d', hd'⟩ :=
        Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk x')
      have hlt : d' < d := by
        have hh := ringKrullDim_stalk_lt_of_specializes hspec hne
        rw [hd', hd] at hh
        exact_mod_cast hh
      have hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x') := by
        rw [hd']
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hh ↦ hzero (by simp only [hd', hh, Nat.cast_zero]))
      exact ih d' hlt f x' (isNormalRing_stalk_of_specializes hspec hX)
        (isRegularLocalRing_stalk_of_specializes (hspec.map f.continuous) hY) hpos
        (fun w hw hdw ↦ hetale w (hw.trans hspec) hdw) hd'
    -- Base change to the spectrum of the local ring of the target.
    let g := Y.fromSpecStalk (f x)
    have _ : Flat g := flat_fromSpecStalk Y (f x)
    obtain ⟨x₀, hx₀, hy₀⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g)
      x (IsLocalRing.closedPoint (Y.presheaf.stalk (f x))) (by simp [g])
    let j := pullback.fst f g
    let f₀ := pullback.snd f g
    change j x₀ = x at hx₀
    have hback : EtaleAt f₀ x₀ → EtaleAt f x := by
      have hiff := etaleAt_pullback_fromSpecStalk_iff f (f x) x₀
      change EtaleAt f₀ x₀ ↔ EtaleAt f (j x₀) at hiff
      rw [hx₀] at hiff
      exact hiff.mp
    apply hback
    have _ : IsLocallyNoetherian (pullback f g) := LocallyOfFiniteType.isLocallyNoetherian f₀
    have hpunctured₀ : ∀ z : (pullback f g : Scheme.{u}), z ⤳ x₀ → z ≠ x₀ → EtaleAt f₀ z := by
      intro z hz hne
      refine (etaleAt_pullback_fromSpecStalk_iff f (f x) z).mpr (hpunctured (j z) ?_ ?_)
      · simpa only [hx₀] using hz.map j.continuous
      · exact fun heq ↦ hne (j.isEmbedding.injective (heq.trans hx₀.symm))
    have _ := isIso_stalkMap_of_flat_isPreimmersion j x₀
    have hnormal₀ : IsNormalRing ((pullback f g).presheaf.stalk x₀) :=
      IsNormalRing.congr (asIso (j.stalkMap x₀)).commRingCatIsoToRingEquiv (hx₀.symm ▸ hX)
    have hd₀ : ringKrullDim ((pullback f g).presheaf.stalk x₀) = d :=
      (asIso (j.stalkMap x₀)).commRingCatIsoToRingEquiv.ringKrullDim.symm.trans
        (by rw [hx₀]; exact hd)
    -- Base change to the spectrum of the completion of that local ring.
    let A : Type u := Y.presheaf.stalk (f x)
    have _ : IsNoetherianRing A := inferInstance
    have _ : IsRegularLocalRing A := hY
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    have _ : IsLocalHom (algebraMap A Ahat) := inferInstance
    have _ : IsRegularLocalRing Ahat := isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp hY
    let i : Spec (.of Ahat) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    have _ : Flat i :=
      Flat.SpecMap_iff.mpr (AdicCompletion.flat_of_isNoetherian (IsLocalRing.maximalIdeal A))
    obtain ⟨x₁, hx₁, hy₁⟩ := Scheme.Pullback.exists_preimage_pullback (f := f₀) (g := i)
      x₀ (IsLocalRing.closedPoint Ahat) (by
        dsimp only [i]
        rw [Spec_closedPoint]
        exact hy₀)
    let j₁ := pullback.fst f₀ i
    let f₁ := pullback.snd f₀ i
    change j₁ x₁ = x₀ at hx₁
    have _ : IsLocallyNoetherian (pullback f₀ i) := LocallyOfFiniteType.isLocallyNoetherian f₁
    have hback₁ (z : (pullback f₀ i : Scheme.{u})) : EtaleAt f₁ z ↔ EtaleAt f₀ (j₁ z) :=
      Set.ext_iff.mp (setOf_etaleAt_eq_preimage_of_isPullback
        (IsPullback.of_hasPullback f₀ i) (Or.inr inferInstance)) z
    suffices h : EtaleAt f₁ x₁ by simpa only [hx₁] using (hback₁ x₁).mp h
    have htwo : 2 ≤ ringKrullDim ((pullback f g).presheaf.stalk x₀) := by
      rw [hd₀]
      have hp : 1 ≤ d := by exact_mod_cast (hd ▸ hpositive)
      have hn : d ≠ 1 := fun hh ↦ hdim (by simp only [hd, hh, Nat.cast_one])
      exact_mod_cast (show 2 ≤ d by omega)
    have hEt₁ : ∀ z : (pullback f₀ i : Scheme.{u}), z ⤳ x₁ →
        ringKrullDim ((pullback f g).presheaf.stalk (j₁ z)) ≤ 1 → EtaleAt f₁ z := by
      intro z hz hzdim
      refine (hback₁ z).mpr (hpunctured₀ (j₁ z) ?_ ?_)
      · simpa only [hx₁] using hz.map j₁.continuous
      · intro heq
        rw [heq] at hzdim
        exact absurd (htwo.trans hzdim) (by norm_num)
    have hnormal₁ : IsNormalRing ((pullback f₀ i).presheaf.stalk x₁) := by
      refine isNormalRing_stalk_of_flat_of_isRegularLocalRing_codimension_le_one j₁ x₁
        (hx₁.symm ▸ hnormal₀) ?_
      intro z hz hzdim
      exact isRegularLocalRing_stalk_of_etaleAt f₁ z (hEt₁ z hz hzdim)
        (isRegularLocalRing_stalk_spec Ahat (f₁ z))
    have hpositive₁ : 2 ≤ ringKrullDim ((pullback f₀ i).presheaf.stalk x₁) :=
      htwo.trans (by
        have hh := ringKrullDim_stalk_le_of_flat j₁ x₁
        rw [hx₁] at hh
        exact hh)
    refine etaleAt_of_etaleAt_codimensionOne_over_excellent
      (isExcellent_of_standard_classes_and_finiteType.{u, u}.2.1 Ahat) f₁ x₁ hnormal₁
      (((by norm_num : (1 : WithBot ℕ∞) ≤ 2)).trans hpositive₁) ?_
    intro z hz hdimz
    refine hEt₁ z hz ?_
    simpa only [hdimz] using ringKrullDim_stalk_le_of_flat j₁ z

end AlgebraicGeometry

end
