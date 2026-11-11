module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FlatBaseChange
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.PseudoCoherentMap.Locality
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfectness of a morphism of schemes is fpqc local on the base

A morphism of schemes is perfect if and only if its base change along every member of an fpqc
covering of the target is perfect (Stacks 069B).

## Main results

* `RingHom.Perfect.codescendsAlong_faithfullyFlat`: the algebra content, that perfectness of a
  ring map descends along a faithfully flat base change.
* `AlgebraicGeometry.perfect_descendsAlong_surjective_inf_flat_inf_quasiCompact`: perfectness of
  a morphism of schemes satisfies fpqc descent.
* `AlgebraicGeometry.perfect_isLocalAtTarget_fpqc`: **Stacks 069B**.

## Implementation notes

The proof is the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` (Tag 02KP for the
fpqc topology) at `P = AlgebraicGeometry.Perfect`, so it needs Zariski locality on the base,
stability under flat base change, and descent along surjective flat quasi-compact morphisms.

Zariski locality is that of an affine-local property of ring maps:
`AlgebraicGeometry.hasRingHomProperty_perfect` (in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal`) exhibits perfectness
as the affine-local property attached to `RingHom.Perfect`, which mentions no derived category.

Stability under flat base change is Tag 0688,
`AlgebraicGeometry.perfect_of_isPullback_of_flat`; only *flat* base change is available, and it
is all the criterion asks for. The descent step is what is proved here.

The ring-level descent is the recasting of hypothesis (3) of Tag 02KP given in the source: for a
faithfully flat `A → B` and an `A`-algebra `C`, perfectness of `B → B ⊗_A C` implies perfectness
of `A → C`. Finite type descends by
`Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`, which supplies a polynomial
presentation `A[x_1, …, x_n] ↠ C`; its base change `B[x_1, …, x_n] ↠ B ⊗_A C` is again surjective
and `A[x_1, …, x_n] → B[x_1, …, x_n]` is again faithfully flat, because that square is a pushout
and faithful flatness is stable under base change. Perfectness of `B ⊗_A C` as a
`B[x_1, …, x_n]`-module is Stacks 068Y at that presentation,
`Algebra.Perfect.exists_finite_projective_resolution` read through Stacks 066Q, and it then
descends to `C` over `A[x_1, …, x_n]` by Tag 068T,
`StacksDraft.Perfect.isPerfect_of_faithfullyFlat_baseChange`; Stacks 068Y as worded,
`Algebra.perfect_iff_exists_finite_projective_resolution`, turns this into perfectness of `A → C`.

The two reductions of the geometric statement to the algebra one — from a general base to an
affine one, and from a general source of the covering morphism to an affine one — are Mathlib's
`AlgebraicGeometry.of_pullback_fst_Spec_of_codescendsAlong` together with the Zariski locality of
perfectness at the source. The reduction to a covering morphism between affine schemes is
performed by hand rather than through
`AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`, which assumes
stability under arbitrary base change: a quasi-compact scheme is dominated by an affine one
through a surjective local isomorphism, which is flat, so the one base change the reduction
performs is a flat one.

## References

* [The Stacks Project, Lemma 37.61.9 (069B)](https://stacks.math.columbia.edu/tag/069B)
* [The Stacks Project, Lemma 35.22.4 (02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [The Stacks Project, Lemma 37.61.3 (0688)](https://stacks.math.columbia.edu/tag/0688)
* [The Stacks Project, Lemma 15.83.11 (068T)](https://stacks.math.columbia.edu/tag/068T)
* [The Stacks Project, Lemma 15.83.3 (068Y)](https://stacks.math.columbia.edu/tag/068Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open StacksDraft.TorAmplitude
open scoped TensorProduct

universe w u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

private theorem isPerfectModule_of_faithfullyFlat_baseChange
    {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (hf : Module.FaithfullyFlat R S)
    (e : (S ⊗[R] M) ≃ₗ[S] N)
    (hN : StacksDraft.Perfect.IsPerfectModule (R := S) N) :
    StacksDraft.Perfect.IsPerfectModule (R := R) M := by
  let f := algebraMap R S
  let F := ModuleCat.extendScalars.{u, u, u} f
  have hf' : f.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hf
  have : Limits.PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let M₀ := ModuleCat.of R M
  let N₀ := ModuleCat.of S N
  let e₀ : F.obj M₀ ≅ N₀ := LinearEquiv.toModuleIso
    ((StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv R S M₀).trans e)
  let C := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M₀
  let e₁ : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M₀) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N₀ :=
    (F.mapDerivedCategorySingleFunctor 0).app M₀ ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).mapIso e₀
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M₀)
    (StacksDraft.Perfect.isPerfect_of_faithfullyFlat_baseChange f hf' C
      (StacksDraft.Perfect.isPerfect_of_iso (F.mapDerivedCategoryFactors.app C).symm
        (StacksDraft.Perfect.isPerfect_of_iso e₁ hN)))

private theorem perfect_of_faithfullyFlat_polynomialPresentation
    (A B Q B' : Type u) [CommRing A] [CommRing B] [CommRing Q] [CommRing B']
    [Algebra A B] (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B)
    (hα : Function.Surjective α)
    [Algebra (MvPolynomial (Fin n) A) Q]
    [Module.FaithfullyFlat (MvPolynomial (Fin n) A) Q]
    [Module (MvPolynomial (Fin n) A) B] [Algebra Q B']
    (hModule : (inferInstance : Module (MvPolynomial (Fin n) A) B) =
      Module.compHom B α.toRingHom)
    (e : (Q ⊗[MvPolynomial (Fin n) A] B) ≃ₗ[Q] B')
    (hB' : StacksDraft.Perfect.IsPerfectModule (R := Q) B') :
    Algebra.Perfect A B := by
  cases hModule
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  let P := MvPolynomial (Fin n) A
  have hB : StacksDraft.Perfect.IsPerfectModule (R := P) B :=
    isPerfectModule_of_faithfullyFlat_baseChange (R := P) (S := Q) (M := B) (N := B')
      inferInstance e hB'
  exact Algebra.perfect_iff_exists_finite_projective_resolution.mpr
    ⟨n, α, hα, (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution
      B).mp hB⟩

private theorem perfect_of_faithfullyFlat_baseChange
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A B C D]
    [Module.FaithfullyFlat A B] [Algebra.Perfect B D] : Algebra.Perfect A C := by
  have : Algebra.PseudoCoherent B (B ⊗[A] C) :=
    .equiv inferInstance (Algebra.IsPushout.equiv A B C D).symm
  have : Algebra.FiniteType A C :=
    Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := C)).mp inferInstance
  obtain ⟨β, hβ, hβP⟩ : ∃ β : MvPolynomial (Fin n) B →ₐ[B] D, Function.Surjective β ∧
      ∀ p, β (MvPolynomial.map (algebraMap A B) p) = algebraMap C D (α p) := by
    let ePush : B ⊗[A] C ≃ₐ[B] D := Algebra.IsPushout.equiv A B C D
    let ePoly : B ⊗[A] MvPolynomial (Fin n) A ≃ₐ[B] MvPolynomial (Fin n) B :=
      MvPolynomial.algebraTensorAlgEquiv A B
    let mapPoly : B ⊗[A] MvPolynomial (Fin n) A →ₐ[B] B ⊗[A] C :=
      Algebra.TensorProduct.map (AlgHom.id B B) α
    refine ⟨ePush.toAlgHom.comp (mapPoly.comp ePoly.symm.toAlgHom),
      ePush.surjective.comp ((Algebra.TensorProduct.map_surjective (AlgHom.id B B) α
        (fun x => ⟨x, rfl⟩) hα).comp ePoly.symm.surjective), fun p => ?_⟩
    change ePush (mapPoly (ePoly.symm (MvPolynomial.map (algebraMap A B) p))) =
      algebraMap C D (α p)
    rw [show ePoly.symm (MvPolynomial.map (algebraMap A B) p) = 1 ⊗ₜ[A] p from
      MvPolynomial.algebraTensorAlgEquiv_symm_map A B p]
    simp [mapPoly, ePush, Algebra.IsPushout.equiv_tmul]
  let P := MvPolynomial (Fin n) A
  let Q := MvPolynomial (Fin n) B
  let : Algebra P C := α.toRingHom.toAlgebra
  have : IsScalarTower A P C :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (α.commutes x).symm)
  let : Algebra P Q := MvPolynomial.algebraMvPolynomial
  let : Algebra Q D := β.toRingHom.toAlgebra
  have : IsScalarTower B Q D :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (β.commutes x).symm)
  let : Algebra P D := (algebraMap C D).comp (algebraMap P C) |>.toAlgebra
  have : IsScalarTower P C D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A P D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq A C D, IsScalarTower.algebraMap_eq P C D, RingHom.comp_assoc,
      IsScalarTower.algebraMap_eq A P C])
  have : IsScalarTower P Q D :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun p => (hβP p).symm)
  have : IsScalarTower A Q D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq A B Q, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq B Q D, ← IsScalarTower.algebraMap_eq A B D])
  have : Algebra.IsPushout A P B Q := inferInstance
  have : Module.FaithfullyFlat P Q :=
    Module.FaithfullyFlat.of_linearEquiv P (P ⊗[A] B)
      (Algebra.IsPushout.equiv A P B Q).toLinearEquiv.symm
  have : Algebra.IsPushout P C Q D := (Algebra.IsPushout.comp_iff A P B Q (T := C) (T' := D)).mp
    ((Algebra.IsPushout.comm A B C D).mp inferInstance)
  have : Algebra.IsPushout P Q C D := .symm inferInstance
  have hBDperfect : StacksDraft.Perfect.IsPerfectModule (R := Q) D :=
    (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution D).mpr
      (Algebra.Perfect.exists_finite_projective_resolution β hβ)
  exact perfect_of_faithfullyFlat_polynomialPresentation A C Q D n α hα rfl
    (Algebra.IsPushout.equiv P Q C D).toLinearEquiv hBDperfect

/-- **The algebra content of Stacks 069B**, as a statement about `RingHom.CodescendsAlong`:
perfectness of ring maps codescends along faithfully flat ring maps. -/
public theorem _root_.RingHom.Perfect.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong @RingHom.Perfect.{u, u} @RingHom.FaithfullyFlat := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hQ hP
  have : Module.FaithfullyFlat R R' := RingHom.faithfullyFlat_algebraMap_iff.mp hQ
  have : Algebra.IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have : Algebra.Perfect R' S' := RingHom.perfect_algebraMap.mp hP
  exact RingHom.perfect_algebraMap.mpr (perfect_of_faithfullyFlat_baseChange (B := R') (D := S'))

/-- Perfectness is stable under flat base change, hypothesis (1) of Tag 02KP for the fpqc
topology. This is Tag 0688 in the shape the criterion asks for. -/
public instance perfect_isStableUnderFlatBaseChange :
    Stacks.Descent.IsStableUnderFlatBaseChange (@Perfect.{u}) where
  isStableUnderBaseChangeAlong _ :=
    { of_isPullback := fun sq hf =>
        have := hf
        perfect_of_isPullback_of_flat sq }

/-- The descent step for a covering morphism between affine schemes: perfectness of a morphism
from an affine scheme to `Spec R` follows from perfectness of its base change along a surjective
flat morphism `Spec S ⟶ Spec R`. -/
private lemma perfect_of_pullback_fst_Spec {R S T : CommRingCat.{u}}
    {f : Spec T ⟶ Spec R} {g : Spec S ⟶ Spec R}
    (hf : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) f)
    (hfst : Perfect (pullback.fst f g)) : Perfect g := by
  have := perfect_respectsIso.{u}
  refine of_pullback_fst_Spec_of_codescendsAlong (@Perfect.{u}) (@Surjective ⊓ @Flat)
    RingHom.Perfect.codescendsAlong_faithfullyFlat (fun {_ _ φ} hφ => ?_)
    (fun {_ _ _} => HasRingHomProperty.Spec_iff (P := (@Perfect.{u}))) hf hfst
  have _ : Surjective (Spec.map φ) := hφ.1
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mp hφ.2, (Spec.map φ).surjective⟩

/-- The descent step for a covering morphism out of an affine scheme, the target of the descended
morphism being arbitrary: perfectness is Zariski local at the source, so the target may be
covered by affine opens and `perfect_of_pullback_fst_Spec` applied over each. -/
private lemma perfect_of_pullback_fst_SpecMap {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ S) {g : Y ⟶ Spec R}
    (hf : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) (Spec.map φ))
    (hfst : Perfect (pullback.fst (Spec.map φ) g)) : Perfect g := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := (@Perfect.{u})) Y.affineCover]
  intro i
  let ι : pullback (Spec.map φ) (Y.affineCover.f i ≫ g) ⟶ pullback (Spec.map φ) g :=
    pullback.map _ _ _ _ (𝟙 _) (Y.affineCover.f i) (𝟙 _) (by simp) (by simp)
  have _ : IsOpenImmersion ι := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  have heq : pullback.fst (Spec.map φ) (Y.affineCover.f i ≫ g) =
      ι ≫ pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
  exact perfect_of_pullback_fst_Spec hf (heq ▸ IsZariskiLocalAtSource.comp hfst ι)

/-- **Perfectness satisfies fpqc descent**, hypothesis (3) of Tag 02KP for the fpqc topology: if
the base change of a morphism along a surjective flat quasi-compact morphism is perfect, then so
is the morphism. -/
public instance perfect_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@Perfect.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := perfect_isZariskiLocalAtTarget.{u}
  have := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have := Flat.instIsMultiplicativeScheme.{u}.toContainsIdentities
  have : MorphismProperty.ContainsIdentities (@IsLocalIso : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hflatsrc : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have : MorphismProperty.RespectsIso (@IsLocalIso : MorphismProperty Scheme.{u}) :=
    (inferInstance : IsZariskiLocalAtSource (@IsLocalIso : MorphismProperty Scheme.{u})).toRespects
  refine IsZariskiLocalAtTarget.descendsAlong (@Perfect.{u})
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) fun {R X Y} f g hf hfst => ?_
  obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := hf
  have _ : Surjective f := hsurj
  have _ : Flat f := hflat
  have _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp hqc
  obtain ⟨T, p, hp, hploc, hT⟩ :=
    X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have _ : IsAffine T := hT
  have _ : IsLocalIso p := hploc
  have _ : Surjective p := hp
  have hk : IsLocalIso (T.isoSpec.inv ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsLocalIso) T.isoSpec.inv p).mpr hploc
  have _ : Flat (T.isoSpec.inv ≫ p) :=
    IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ (T.isoSpec.inv ≫ p) hk
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((T.isoSpec.inv ≫ p) ≫ f)
  refine perfect_of_pullback_fst_SpecMap φ ?_ ?_
  · rw [hφ]
    exact ⟨inferInstance, inferInstance⟩
  · rw [hφ, ← pullbackRightPullbackFstIso_inv_fst f g (T.isoSpec.inv ≫ p),
      MorphismProperty.cancel_left_of_respectsIso (P := (@Perfect.{u}))]
    have := Stacks.Descent.IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong
      (P := (@Perfect.{u})) (T.isoSpec.inv ≫ p)
    exact MorphismProperty.pullback_fst _ _ hfst

/-- **Stacks 069B.** Perfectness of a morphism of schemes is fpqc local on the base: a morphism is
perfect if and only if its base change along every member of an fpqc covering of its target is
perfect.

Both implications are part of `CategoryTheory.MorphismProperty.IsLocalAtTarget`; they are spelled
out as a single `Iff` by `AlgebraicGeometry.perfect_iff_of_fpqcCover`. -/
@[stacks 069B, sga "6 IV 3.1.1" "special case"]
public instance perfect_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Perfect.{u}) Scheme.fpqcPrecoverage :=
  have := perfect_isZariskiLocalAtTarget.{u}
  have := perfect_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- A morphism of schemes is perfect if and only if its base change along every member of a given
fpqc covering of its target is perfect.

This spells out both directions of `AlgebraicGeometry.perfect_isLocalAtTarget_fpqc`. -/
public theorem perfect_iff_of_fpqcCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage S) :
    Perfect f ↔ ∀ i, Perfect (pullback.snd f (𝒰.f i)) :=
  have := perfect_isLocalAtTarget_fpqc.{u}
  IsLocalAtTarget.iff_of_zeroHypercover (P := (@Perfect.{u})) 𝒰

end AlgebraicGeometry

end
