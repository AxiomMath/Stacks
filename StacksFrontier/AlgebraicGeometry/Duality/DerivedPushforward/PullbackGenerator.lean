module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.ReflectsIsomorphisms
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QcqsRightAdjoint
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.Generators
import Mathlib.Tactic.TFAE
import StacksCore.Tactic.StacksAttribute

/-!
# Detecting zero objects by `Rf_*`, and the pullback of a generator

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of quasi-compact schemes and let
`E` be a weak generator of `D_QCoh(𝒪_Y)`. [Stacks, Tag 0BQT] records that the following are
equivalent:

1. an object `K` of `D_QCoh(𝒪_X)` is zero as soon as `Rf_*K` is zero;
2. `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms;
3. `Lf^*E` is a weak generator of `D_QCoh(𝒪_X)`.

The source phrases the remark with the generator `E` given, citing [Stacks, Tag 09IS] for its
existence; the generator is therefore a hypothesis of the statement here as well, and it is the
only hypothesis beyond quasi-compactness and quasi-separatedness.

(1) ⇔ (2) is formal from exactness of `Rf_*`: a map `α` of `D_QCoh(𝒪_X)` is invertible exactly
when the third vertex of a distinguished triangle on it is zero, and `Rf_*` carries that triangle
to a distinguished triangle whose first map is `Rf_*α`, so (1) turns "`Rf_*α` invertible" into
"the cone of `α` is zero". Conversely a functor that reflects isomorphisms detects zero objects,
because a triangulated functor preserves zero morphisms and an object whose identity is zero is a
zero object.

(1) ⇔ (3) is formal from `Lf^* ⊣ Rf_*` on `D_QCoh`: the adjunction and the compatibility of
`Lf^*` with the shift identify the morphisms `(Lf^*E)⟦a⟧ ⟶ K` with the morphisms
`E⟦a⟧ ⟶ Rf_*K`, so `K` is right orthogonal to the shifts of `Lf^*E` exactly when `Rf_*K` is
right orthogonal to the shifts of `E`, which — `E` being a generator — says that `Rf_*K` is zero.

## Main results

All in the namespace `Stacks.Duality.DerivedPushforward`.

* `quasiCoherentDerivedAdjunctionQcqs` — the adjunction `Lf^* ⊣ Rf_*` on the quasi-coherent
  derived categories, with the two quasi-coherence hypotheses discharged. The functor
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` it is stated for is `qcqsRestrictedDerivedPushforward`.
* `rightOrthogonal_shiftClosure_singleton_quasiCoherentDerivedPullback_iff` — the adjunction
  step: `K` admits only the zero map from every shift of `Lf^*E` exactly when `Rf_*K` admits only
  the zero map from every shift of `E`.
* `tfae_isZero_quasiCoherentDerivedPushforward` — **[Stacks, Tag 0BQT]**, the three equivalent
  conditions.
* `reflectsIsomorphisms_qcqsRestrictedDerivedPushforward_specMap` and
  `isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_specMap` — **the remark's clause that
  the conditions hold for an affine morphism**, in the case of a morphism `Spec φ` of affine
  schemes, which is the case [Stacks, Tag 08I8] is available in
  (`AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward_specMap`): condition
  (2) holds, hence so does (3), so `L(Spec φ)^*` carries a generator to a generator.

## Implementation notes

*Where the rest of the remark lives.* The clause that the three conditions hold when `f` is
affine, when `f` is an open immersion and when `f` is a composition of such is
`Stacks.Duality.DerivedPushforward.conditions_of_multiplicativeClosure` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/GeneratorClauses.lean`, which rests on
condition (1) in the two generating cases — the two files
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/AffineConservative.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/OpenImmersionConservative.lean`. The
consequence the source draws for a quasi-affine scheme `X`, that `𝒪_X` generates `D_QCoh(𝒪_X)`,
is `isWeakTriangulatedGenerator_derivedStructureSheaf_of_isQuasiAffine` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiAffineGenerator.lean`.

*The model of the derived categories* is the locally small one, as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/Exactness.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`, because
that is the only model at which the quasi-coherent inputs — the restricted adjunction and the
exactness of the restricted `Rf_*` — are available. Part (1) of [Stacks, Tag 08D5] is therefore
taken in the form `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, which is
stated at that model and asks in addition that the target be quasi-compact; that is no extra
assumption, the source's `Y` being quasi-compact and quasi-separated. The standard-model
`qcqsQuasiCoherentDerivedPushforward` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` cannot be
used: `HasDerivedCategory` is data, and `Lf^*` exists only at the locally small model.

*Compatibility of the restricted `Lf^*` with the shift* is `Stacks.Duality`'s
`commShift_quasiCoherentDerivedPullback`, which is a definition and not an instance; it is
introduced locally where the shift isomorphism of `Lf^*` is needed, exactly as
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean` does.

## References

* [Stacks Project, Tag 0BQT](https://stacks.math.columbia.edu/tag/0BQT)
* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.DerivedPushforward

section Qcqs

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f] [CompactSpace Y]

/-! ### `Rf_*` and the adjunction `Lf^* ⊣ Rf_*` on `D_QCoh`, with both hypotheses discharged -/

/-- **The adjunction `Lf^* ⊣ Rf_*` on the quasi-coherent derived categories** of a quasi-compact
and quasi-separated morphism of schemes with quasi-compact target. This is
`Stacks.Duality.quasiCoherentDerivedAdjunction` with its two hypotheses discharged: that `Lf^*`
preserves quasi-coherence of cohomology is [Stacks, Tag 08DW] part (1),
`Stacks.Duality.isQuasicoherent_homology_derivedPullback'`, and that `Rf_*` does is
[Stacks, Tag 08D5] part (1),
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`. -/
abbrev quasiCoherentDerivedAdjunctionQcqs :
    Stacks.Duality.quasiCoherentDerivedPullback' f ⊣ qcqsRestrictedDerivedPushforward f :=
  Stacks.Duality.quasiCoherentDerivedAdjunction f
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback' f)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)

/-! ### The adjunction step -/

/-- **`Rf_*` turns orthogonality to the shifts of `E` into orthogonality to the shifts of
`Lf^*E`.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with
quasi-compact target, let `E` be an object of `D_QCoh(𝒪_Y)` and let `K` be an object of
`D_QCoh(𝒪_X)`. Then every morphism to `K` from a shift of `Lf^*E` vanishes if and only if every
morphism to `Rf_*K` from a shift of `E` vanishes.

This is the adjunction `Lf^* ⊣ Rf_*` of `quasiCoherentDerivedAdjunctionQcqs` together with the
compatibility of `Lf^*` with the shift, which identifies `Lf^*(E⟦a⟧)` with `(Lf^*E)⟦a⟧`: the
composite bijection `((Lf^*E)⟦a⟧ ⟶ K) ≃ (E⟦a⟧ ⟶ Rf_*K)` carries the zero morphism to the zero
morphism in both directions, since `Rf_*` is exact and hence preserves zero morphisms. -/
theorem rightOrthogonal_shiftClosure_singleton_quasiCoherentDerivedPullback_iff
    (E : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    ((ObjectProperty.singleton
          ((Stacks.Duality.quasiCoherentDerivedPullback' f).obj E)).shiftClosure ℤ
        ).rightOrthogonal K ↔
      ((ObjectProperty.singleton E).shiftClosure ℤ).rightOrthogonal
        ((qcqsRestrictedDerivedPushforward f).obj K) := by
  let := Stacks.Duality.commShift_quasiCoherentDerivedPullback f
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback' f)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)
  set L := Stacks.Duality.quasiCoherentDerivedPullback' f
  set R := qcqsRestrictedDerivedPushforward f
  set adj := quasiCoherentDerivedAdjunctionQcqs f
  -- the adjunction bijection and its inverse carry the zero morphism to the zero morphism
  have hz : ∀ (A : Stacks.Duality.quasiCoherentDerivedCategory Y)
      (B : Stacks.Duality.quasiCoherentDerivedCategory X),
      (adj.homEquiv A B) 0 = 0 := fun A B ↦ by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  -- transporting along the shift isomorphism and `adj` preserves and reflects the zero morphism
  have key : ∀ (a : ℤ) (g : (L.obj E)⟦a⟧ ⟶ K),
      adj.homEquiv _ _ (((L.commShiftIso a).app E).hom ≫ g) = 0 ↔ g = 0 := fun a g ↦ by
    rw [← hz (E⟦a⟧) K, (adj.homEquiv _ _).apply_eq_iff_eq,
      ← cancel_epi ((L.commShiftIso a).app E).hom, comp_zero]
  rw [rightOrthogonal_shiftClosure_ofObj_iff (fun _ : Unit ↦ L.obj E),
    rightOrthogonal_shiftClosure_ofObj_iff (fun _ : Unit ↦ E)]
  refine forall_congr' fun _ ↦ forall_congr' fun a ↦ ⟨fun H h ↦ ?_, fun H g ↦ (key a g).1 (H _)⟩
  simpa using (key a (((L.commShiftIso a).app E).inv ≫ (adj.homEquiv _ _).symm h)).2 (H _)

/-! ### The remark -/

/-- **[Stacks, Tag 0BQT].** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes with `Y` quasi-compact, and let `E` be a weak generator of `D_QCoh(𝒪_Y)` — the object
[Stacks, Tag 09IS] provides, and the one hypothesis the source's remark carries. Then the
following are equivalent:

1. every object `K` of `D_QCoh(𝒪_X)` with `Rf_*K` zero is itself zero;
2. `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms;
3. `Lf^*E` is a weak generator of `D_QCoh(𝒪_X)`.

(1) ⇒ (2): complete a morphism `α` whose image is invertible to a distinguished triangle; `Rf_*`
is exact, so it carries that triangle to a distinguished triangle whose first morphism is
`Rf_*α`, whence its third vertex `Rf_*(cone α)` is zero, whence `cone α` is zero by (1), whence
`α` is invertible. (2) ⇒ (1): if `Rf_*K` is zero then the zero endomorphism of `Rf_*K` is its
identity, so the zero endomorphism of `K` is invertible by (2) and `𝟙 K = 0`.

(1) ⇔ (3): `K` is right orthogonal to the shifts of `Lf^*E` exactly when `Rf_*K` is right
orthogonal to the shifts of `E`, by
`rightOrthogonal_shiftClosure_singleton_quasiCoherentDerivedPullback_iff`, and the latter says
exactly that `Rf_*K` is zero because `E` generates. -/
@[stacks 0BQT]
theorem tfae_isZero_quasiCoherentDerivedPushforward
    (E : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    [∀ K : Stacks.Duality.quasiCoherentDerivedCategory X,
        IsZero ((qcqsRestrictedDerivedPushforward f).obj K) → IsZero K,
      (qcqsRestrictedDerivedPushforward f).ReflectsIsomorphisms,
      (ObjectProperty.singleton
        ((Stacks.Duality.quasiCoherentDerivedPullback' f).obj E)
        ).IsWeakTriangulatedGenerator].TFAE := by
  tfae_have 1 → 2 := by
    intro h₁
    refine ⟨fun {A B} α hα ↦ ?_⟩
    obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
    exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (h₁ C ((Triangle.isZero₃_iff_isIso₁ _
      ((qcqsRestrictedDerivedPushforward f).map_distinguished _ hT)).2 hα))
  tfae_have 2 → 1 := by
    intro h₂ K hK
    have : IsIso ((qcqsRestrictedDerivedPushforward f).map (0 : K ⟶ K)) := by
      rw [Functor.map_zero, hK.eq_of_src (0 : _ ⟶ _) (𝟙 _)]
      infer_instance
    have : IsIso (0 : K ⟶ K) :=
      isIso_of_reflects_iso (0 : K ⟶ K) (qcqsRestrictedDerivedPushforward f)
    rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : K ⟶ K), comp_zero]
  tfae_have 1 → 3 := fun h₁ K hK ↦ h₁ K (hE _
    ((rightOrthogonal_shiftClosure_singleton_quasiCoherentDerivedPullback_iff f E K).1 hK))
  tfae_have 3 → 1 := fun h₃ K hK ↦
    h₃ K ((rightOrthogonal_shiftClosure_singleton_quasiCoherentDerivedPullback_iff f E K).2
      ((ObjectProperty.rightOrthogonal_iff _ _).2 fun _ z _ ↦ hK.eq_zero_of_tgt z))
  tfae_finish

end Qcqs

/-! ### The case of a morphism of affine schemes -/

section Affine

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Condition (2) of [Stacks, Tag 0BQT] for a morphism `Spec φ` of affine schemes.** The
derived direct image `R(Spec φ)_* : D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` reflects
isomorphisms.

This is [Stacks, Tag 08I8] in the form
`AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward_specMap`, read at
`qcqsRestrictedDerivedPushforward`: both functors are the restriction of the unbounded derived
direct image, at the locally small model, to the complexes with quasi-coherent cohomology. -/
theorem reflectsIsomorphisms_qcqsRestrictedDerivedPushforward_specMap :
    (qcqsRestrictedDerivedPushforward (Spec.map φ)).ReflectsIsomorphisms :=
  AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward_specMap φ

/-- **[Stacks, Tag 0BQT] for a morphism of affine schemes: `L(Spec φ)^*` carries a generator to a
generator.** Let `φ : R ⟶ S` be a map of commutative rings and let `E` be a weak generator of
`D_QCoh(𝒪_{Spec R})`. Then `L(Spec φ)^*E` is a weak generator of `D_QCoh(𝒪_{Spec S})`.

This is the implication (2) ⇒ (3) of `tfae_isZero_quasiCoherentDerivedPushforward`, whose
condition (2) holds for `Spec φ` by [Stacks, Tag 08I8]; it is the source's clause that the three
conditions of the remark hold when `f` is affine, in the case of a morphism of affine
schemes. -/
@[stacks 0BQT "the conditions hold for an affine morphism: the case of a morphism Spec φ of \
  affine schemes, where Lf^* carries a generator to a generator"]
theorem isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_specMap
    (E : Stacks.Duality.quasiCoherentDerivedCategory (Spec R))
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton
        ((Stacks.Duality.quasiCoherentDerivedPullback' (Spec.map φ)).obj E)
      ).IsWeakTriangulatedGenerator :=
  ((tfae_isZero_quasiCoherentDerivedPushforward (Spec.map φ) E hE).out 2 3).1
    (reflectsIsomorphisms_qcqsRestrictedDerivedPushforward_specMap φ)

end Affine

end Stacks.Duality.DerivedPushforward

end
