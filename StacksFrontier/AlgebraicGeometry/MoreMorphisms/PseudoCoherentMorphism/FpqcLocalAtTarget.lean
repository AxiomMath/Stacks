module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence of a morphism of schemes is fpqc local on the base

A morphism of schemes is pseudo-coherent if and only if its base change along every member of an
fpqc covering of the target is pseudo-coherent (Stacks 0696).

## Main results

* `Algebra.PseudoCoherent.of_isPushout_of_faithfullyFlat`: the algebra content, that
  pseudo-coherence of a ring map descends along a faithfully flat base change.
* `RingHom.pseudoCoherent_codescendsAlong_faithfullyFlat`: the same as a statement about
  `RingHom.CodescendsAlong`.
* `AlgebraicGeometry.pseudoCoherent_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  pseudo-coherence of a morphism of schemes satisfies fpqc descent.
* `AlgebraicGeometry.pseudoCoherent_isLocalAtTarget_fpqc`: **Stacks 0696**.

## Implementation notes

The proof is the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` (Tag 02KP for the
fpqc topology) at `P = AlgebraicGeometry.PseudoCoherent`. Of its three hypotheses, Zariski
locality on the base is the instance `AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`
and stability under flat base change is Tag 0680,
`AlgebraicGeometry.pseudoCoherent_of_isPullback_of_flat`. The third, descent along surjective
flat quasi-compact morphisms, is what is proved here.

Only stability under *flat* base change is available, and it is all the criterion asks for. That
rules out two shortcuts: Mathlib's `AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat`
would turn the ring-level descent below directly into the descent instance, and
`AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact` would reduce it to the
case of a covering morphism between affine schemes, but both assume
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`. The descent instance is therefore
assembled from `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong`, which does not assume
it, with that reduction performed by hand: a quasi-compact scheme is dominated by an affine one
through a surjective local isomorphism
(`AlgebraicGeometry.Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`), a local isomorphism
is flat, and so the one base change the reduction performs is a flat one.

The ring-level descent is the recasting of hypothesis (3) of Tag 02KP given in the source: for a
faithfully flat `R → T` and an `R`-algebra `C` presented as a quotient of `R[x_1, …, x_n]`,
pseudo-coherence of `T ⊗_R C` over `T[x_1, …, x_n]` implies pseudo-coherence of `C` over
`R[x_1, …, x_n]`. Two inputs make this work. Faithful flatness is inherited by the polynomial
extension `R[x_1, …, x_n] → T[x_1, …, x_n]`, because that square is a pushout
(`Mathlib.RingTheory.TensorProduct.MvPolynomial`) and faithful flatness is stable under base
change. And `m`-pseudo-coherence of an object of a derived category of modules descends along a
faithfully flat ring map, which is Tag 068R, the declaration
`isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange` of the namespace
`StacksDraft.PseudoCoherence`. Finite type of `R → C` descends separately, by
`Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`.

The remaining two reductions of the geometric statement to the algebra one — from a general base
to an affine one and from a general source of the covering morphism to an affine one — are
Mathlib's `AlgebraicGeometry.of_pullback_fst_Spec_of_codescendsAlong`, which converts a
`RingHom.CodescendsAlong` into descent of the associated morphism property between affine
schemes, together with the Zariski locality of pseudo-coherence at the source.

## References

* [The Stacks Project, Lemma 37.60.10 (0696)](https://stacks.math.columbia.edu/tag/0696)
* [The Stacks Project, Lemma 15.66.15 (068R)](https://stacks.math.columbia.edu/tag/068R)
* [The Stacks Project, Lemma 35.22.4 (02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [The Stacks Project, Lemma 37.60.3 (0680)](https://stacks.math.columbia.edu/tag/0680)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open scoped TensorProduct

universe w v u

namespace RingHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A faithfully flat ring map stays faithfully flat after adjoining a family of variables to
both sides: that square is a pushout, and faithful flatness is stable under base change. -/
private lemma faithfullyFlat_mvPolynomialMap {R T : Type u} {σ : Type v} [CommRing R]
    [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T] :
    FaithfullyFlat (MvPolynomial.map (algebraMap R T) :
      MvPolynomial σ R →+* MvPolynomial σ T) := by
  let P := MvPolynomial σ R
  let Q := MvPolynomial σ T
  let q : P →+* Q := MvPolynomial.map (algebraMap R T)
  let : Algebra P Q := q.toAlgebra
  have : IsScalarTower P Q Q := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra T Q := inferInstance
  let : Algebra R Q := inferInstance
  have : IsScalarTower R P Q := IsScalarTower.of_algebraMap_eq fun x ↦
    (MvPolynomial.map_C (algebraMap R T) x).symm
  have : IsScalarTower R T Q := inferInstance
  -- Supplied by name: instance search does not identify the algebra structure attached to the
  -- ring map `q` with `MvPolynomial.algebraMvPolynomial`.
  have : Algebra.IsPushout R P T Q := MvPolynomial.instIsPushout_1
  have : Module.FaithfullyFlat P (TensorProduct R P T) := inferInstance
  have : Module.FaithfullyFlat P Q := Module.FaithfullyFlat.of_linearEquiv P (TensorProduct R P T)
    (Algebra.IsPushout.equiv R P T Q).toLinearEquiv.symm
  change (algebraMap P Q).FaithfullyFlat
  exact faithfullyFlat_algebraMap_iff.mpr inferInstance

open StacksDraft.PseudoCoherence in
/-- Pseudo-coherence of an object of the derived category of modules descends along a faithfully
flat ring map, in the form in which the ring-level descent below uses it: a module `M` over `R`
is pseudo-coherent as soon as some module over the faithfully flat extension `S` that its base
change is isomorphic to is pseudo-coherent.

This is Tag 068R transported along the comparison between the derived base change of a module
and the base-changed module. -/
@[sga "6 III 1.1.3" "special case", sga "6 III 1.10" "b)"]
private lemma isPseudoCoherent_of_faithfullyFlat_baseChange {R S : Type u} [CommRing R]
    [CommRing S] (q : R →+* S) (hq : q.FaithfullyFlat) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (e : (ModuleCat.extendScalars.{u, u, u} q).obj M ≅ N)
    (hN : IsPseudoCoherent ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N)) :
    IsPseudoCoherent ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  let : Algebra R S := q.toAlgebra
  let F := ModuleCat.extendScalars.{u, u, u} q
  have : F.Additive := extendScalars_additive.{u, u} q
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat'.{u, u} q
    (RingHom.flat_algebraMap_iff.mpr hq.flat)
  have : PreservesColimitsOfSize.{u, u} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} q).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let QR := DerivedCategory.Q (C := ModuleCat.{u} R)
  let QS := DerivedCategory.Q (C := ModuleCat.{u} S)
  let K := QR.objPreimage ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
  let eQ := QR.objObjPreimageIso ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
  let eDerived : QS.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N :=
    (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso eQ ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).mapIso e
  exact (pseudoCoherent_iff_all _).2 fun m ↦ IsPseudoCoherentFrom.ofIso
    ((isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange q hq K m).1
      (IsPseudoCoherentFrom.ofIso ((pseudoCoherent_iff_all _).1 hN m) eDerived.symm)) eQ

open StacksDraft.PseudoCoherence in
/-- A surjection `T[x_1, …, x_n] ⟶ B` from a polynomial ring over `T` onto a pseudo-coherent
`T`-algebra `B` makes `B` a pseudo-coherent module over the polynomial ring. -/
private lemma _root_.Algebra.PseudoCoherent.isPseudoCoherent_single {T B : Type u} [CommRing T]
    [CommRing B] [Algebra T B] [h : Algebra.PseudoCoherent T B] {n : ℕ}
    (β : MvPolynomial (Fin n) T →ₐ[T] B) (hβ : Function.Surjective β) :
    letI := β.toRingHom.toAlgebra
    IsPseudoCoherent ((DerivedCategory.singleFunctor
      (ModuleCat.{u} (MvPolynomial (Fin n) T)) 0).obj (ModuleCat.of _ B)) :=
  let := β.toRingHom.toAlgebra
  (pseudoCoherent_iff_all _).2 fun k ↦ IsPseudoCoherentFrom.ofIso
    ((Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp h).2 k n β hβ)
    (((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of B B))

open StacksDraft.PseudoCoherence in
/-- **The algebra content of Stacks 0696.** Pseudo-coherence of a ring map descends along a
faithfully flat base change: if `R → T` is faithfully flat and `B` presents the base change
`T ⊗_R C`, then `T → B` pseudo-coherent implies `R → C` pseudo-coherent.

Finite type descends by `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`. For
the relative pseudo-coherence, fix a surjection `R[x_1, …, x_n] ⟶ C`; its base change
`T[x_1, …, x_n] ⟶ B` is again surjective, the extension `R[x_1, …, x_n] → T[x_1, …, x_n]` is
again faithfully flat, and `B` is the base change of `C` along it, so Tag 068R applies. -/
theorem _root_.Algebra.PseudoCoherent.of_isPushout_of_faithfullyFlat {R C : Type u}
    (T B : Type u) [CommRing R] [CommRing T] [CommRing C] [CommRing B] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra R C] [Algebra R B] [Algebra T B] [Algebra C B]
    [IsScalarTower R T B] [IsScalarTower R C B] [Algebra.IsPushout R T C B]
    [h : Algebra.PseudoCoherent T B] :
    Algebra.PseudoCoherent R C := by
  let ePush : TensorProduct R T C ≃ₐ[T] B := Algebra.IsPushout.equiv R T C B
  have := h.equiv ePush.symm
  refine Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mpr
    ⟨Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat (R := R) (S := C) T,
      fun m n α hα ↦ ?_⟩
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin n) T
  let : Algebra P C := α.toRingHom.toAlgebra
  have : IsScalarTower R P C := IsScalarTower.of_algebraMap_eq fun r ↦ (α.commutes r).symm
  let q : P →+* Q := MvPolynomial.map (algebraMap R T)
  let : Algebra P Q := (MvPolynomial.mapAlgHom (Algebra.ofId R T)).toRingHom.toAlgebra
  let : Algebra T Q := inferInstance
  let : Algebra R Q := inferInstance
  have : IsScalarTower R P Q := IsScalarTower.of_algebraMap_eq fun r ↦
    (MvPolynomial.map_C (algebraMap R T) r).symm
  have : IsScalarTower R T Q := inferInstance
  -- Supplied by name: the algebra structure on `Q` over `P` here is the one attached to the ring
  -- map `q`, which instance search does not identify with `MvPolynomial.algebraMvPolynomial`.
  have : Algebra.IsPushout R T P Q := MvPolynomial.instIsPushout
  have hq : FaithfullyFlat q := faithfullyFlat_mvPolynomialMap (R := R) (T := T) (σ := Fin n)
  let eAlg := (Algebra.IsPushout.cancelBaseChangeAlg R T P Q C).trans ePush
  let inc : Q →ₐ[T] TensorProduct P Q C := Algebra.TensorProduct.includeLeft
  let β : Q →ₐ[T] B := eAlg.toAlgHom.comp inc
  let : Algebra Q B := β.toRingHom.toAlgebra
  have hβ : Function.Surjective β :=
    eAlg.surjective.comp (Algebra.TensorProduct.includeLeft_surjective T Q
      (show Function.Surjective (algebraMap P C) from hα))
  let M : ModuleCat.{u} P := ModuleCat.of P C
  let N : ModuleCat.{u} Q := ModuleCat.of Q B
  let F := ModuleCat.extendScalars.{u, u, u} q
  have : SMulCommClass P Q ((ModuleCat.restrictScalars.{u, u, u} q).obj (ModuleCat.of Q Q)) :=
    ModuleCat.sMulCommClass_mk q Q
  let : Algebra Q (TensorProduct P Q C) := Algebra.TensorProduct.leftAlgebra
  have hsource : F.obj M = ModuleCat.of Q (TensorProduct P Q C) := rfl
  let eQ : TensorProduct P Q C ≃ₗ[Q] B :=
    { eAlg.toEquiv with
      map_add' := eAlg.map_add
      map_smul' := fun x y ↦
        (congrArg eAlg (Algebra.smul_def x y)).trans (map_mul eAlg _ _) }
  let e : F.obj M ≅ N := hsource ▸ LinearEquiv.toModuleIso eQ
  exact IsPseudoCoherentFrom.ofIso
    ((pseudoCoherent_iff_all ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M)).1
      (isPseudoCoherent_of_faithfullyFlat_baseChange q hq M N e
        (Algebra.PseudoCoherent.isPseudoCoherent_single β hβ)) m)
    (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of C C)).symm

/-- **Stacks 0696, the algebra content**, as a statement about `RingHom.CodescendsAlong`:
pseudo-coherence of ring maps codescends along faithfully flat ring maps. -/
theorem pseudoCoherent_codescendsAlong_faithfullyFlat :
    CodescendsAlong @PseudoCoherent @FaithfullyFlat := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hQ hP
  have : Module.FaithfullyFlat R R' := faithfullyFlat_algebraMap_iff.mp hQ
  have : Algebra.IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  exact pseudoCoherent_algebraMap.mpr
    (pseudoCoherent_algebraMap.mp hP).of_isPushout_of_faithfullyFlat

end RingHom

namespace AlgebraicGeometry

/-- Pseudo-coherence of a morphism of schemes is Zariski local on the source. -/
instance pseudoCoherent_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@PseudoCoherent : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.PseudoCoherent)

/-- Pseudo-coherence of a morphism of schemes is invariant under isomorphisms of the source and
of the target.

Type class search does not derive it from `AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`
or from `AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtSource`:
`CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects` and
`CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects` do not apply to
`@AlgebraicGeometry.PseudoCoherent`, for the reason given at
`AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`. -/
instance pseudoCoherent_respectsIso :
    MorphismProperty.RespectsIso (@PseudoCoherent : MorphismProperty Scheme.{u}) :=
  pseudoCoherent_isZariskiLocalAtTarget.toRespects

/-- Pseudo-coherence is stable under flat base change, hypothesis (1) of Tag 02KP for the fpqc
topology. This is Tag 0680 in the shape the criterion asks for. -/
instance pseudoCoherent_isStableUnderFlatBaseChange :
    Stacks.Descent.IsStableUnderFlatBaseChange
      (@PseudoCoherent : MorphismProperty Scheme.{u}) where
  isStableUnderBaseChangeAlong _ :=
    { of_isPullback := fun sq hf ↦
        have := hf
        pseudoCoherent_of_isPullback_of_flat sq }

/-- The descent step for a covering morphism between affine schemes: pseudo-coherence of a
morphism from an affine scheme to `Spec R` follows from pseudo-coherence of its base change
along a surjective flat morphism `Spec S ⟶ Spec R`.

This is `RingHom.pseudoCoherent_codescendsAlong_faithfullyFlat` read geometrically, a surjective
flat morphism of affine schemes being exactly one whose map on global sections is faithfully
flat. -/
@[sga "6 III 1.1.3" "Clause (ii)", sga "6 III 1.10" "clause b), special case"]
private lemma pseudoCoherent_of_pullback_fst_Spec {R S T : CommRingCat.{u}}
    {f : Spec T ⟶ Spec R} {g : Spec S ⟶ Spec R}
    (hf : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) f)
    (hfst : PseudoCoherent (pullback.fst f g)) : PseudoCoherent g := by
  refine of_pullback_fst_Spec_of_codescendsAlong @PseudoCoherent (@Surjective ⊓ @Flat)
    RingHom.pseudoCoherent_codescendsAlong_faithfullyFlat (fun {_ _ φ} hφ ↦ ?_)
    (fun {_ _ _} ↦ HasRingHomProperty.Spec_iff (P := @PseudoCoherent)) hf hfst
  have _ : Surjective (Spec.map φ) := hφ.1
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mp hφ.2, (Spec.map φ).surjective⟩

/-- The descent step for a covering morphism out of an affine scheme, the target of the
descended morphism being arbitrary: pseudo-coherence is Zariski local at the source, so the
target may be covered by affine opens and `pseudoCoherent_of_pullback_fst_Spec` applied over
each. -/
private lemma pseudoCoherent_of_pullback_fst_SpecMap {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ S) {g : Y ⟶ Spec R}
    (hf : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) (Spec.map φ))
    (hfst : PseudoCoherent (pullback.fst (Spec.map φ) g)) : PseudoCoherent g := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @PseudoCoherent) Y.affineCover]
  intro i
  let ι : pullback (Spec.map φ) (Y.affineCover.f i ≫ g) ⟶ pullback (Spec.map φ) g :=
    pullback.map _ _ _ _ (𝟙 _) (Y.affineCover.f i) (𝟙 _) (by simp) (by simp)
  have _ : IsOpenImmersion ι := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  have heq : pullback.fst (Spec.map φ) (Y.affineCover.f i ≫ g) =
      ι ≫ pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
  exact pseudoCoherent_of_pullback_fst_Spec hf (heq ▸ IsZariskiLocalAtSource.comp hfst ι)

/-- **Pseudo-coherence satisfies fpqc descent**, hypothesis (3) of Tag 02KP for the fpqc
topology: if the base change of a morphism along a surjective flat quasi-compact morphism is
pseudo-coherent, then so is the morphism.

Zariski locality on the target reduces the claim to an affine base `Spec R`. The source `X` of
the covering morphism `f : X ⟶ Spec R` is then quasi-compact, hence dominated by an affine
scheme through a surjective local isomorphism `k`; replacing `f` by `k ≫ f` base changes the
hypothesis along `k`, which is flat, and leaves a covering morphism between affine schemes, for
which `pseudoCoherent_of_pullback_fst_SpecMap` applies. -/
instance pseudoCoherent_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@PseudoCoherent : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have := Flat.instIsMultiplicativeScheme.{u}.toContainsIdentities
  have : MorphismProperty.ContainsIdentities (@IsLocalIso : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have : MorphismProperty.RespectsIso (@IsLocalIso : MorphismProperty Scheme.{u}) :=
    (inferInstance : IsZariskiLocalAtSource (@IsLocalIso : MorphismProperty Scheme.{u})).toRespects
  refine IsZariskiLocalAtTarget.descendsAlong @PseudoCoherent
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) fun {R X Y} f g hf hfst ↦ ?_
  obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := hf
  have _ : Surjective f := hsurj
  have _ : Flat f := hflat
  have _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp hqc
  obtain ⟨T, p, hp, hploc, hT⟩ :=
    X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have _ : IsAffine T := hT
  have _ : IsLocalIso p := hploc
  have _ : Surjective p := hp
  have _ : Flat (T.isoSpec.inv ≫ p) := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ _
    ((MorphismProperty.cancel_left_of_respectsIso (P := @IsLocalIso) T.isoSpec.inv p).mpr hploc)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((T.isoSpec.inv ≫ p) ≫ f)
  refine pseudoCoherent_of_pullback_fst_SpecMap φ ?_ ?_
  · rw [hφ]
    exact ⟨inferInstance, inferInstance⟩
  · rw [hφ, ← pullbackRightPullbackFstIso_inv_fst f g (T.isoSpec.inv ≫ p),
      MorphismProperty.cancel_left_of_respectsIso (P := @PseudoCoherent)]
    have := Stacks.Descent.IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong
      (P := @PseudoCoherent) (T.isoSpec.inv ≫ p)
    exact MorphismProperty.pullback_fst _ _ hfst

/-- **Stacks 0696.** Pseudo-coherence of a morphism of schemes is fpqc local on the base: a
morphism is pseudo-coherent if and only if its base change along every member of an fpqc
covering of its target is pseudo-coherent.

Both implications are part of `CategoryTheory.MorphismProperty.IsLocalAtTarget`; they are spelled
out as a single `Iff` by `AlgebraicGeometry.pseudoCoherent_iff_of_fpqcCover`. -/
@[stacks 0696]
instance pseudoCoherent_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@PseudoCoherent : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- A morphism of schemes is pseudo-coherent if and only if its base change along every member
of a given fpqc covering of its target is pseudo-coherent.

This spells out both directions of `AlgebraicGeometry.pseudoCoherent_isLocalAtTarget_fpqc`. -/
theorem pseudoCoherent_iff_of_fpqcCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage S) :
    PseudoCoherent f ↔ ∀ i, PseudoCoherent (pullback.snd f (𝒰.f i)) :=
  IsLocalAtTarget.iff_of_zeroHypercover (P := (@PseudoCoherent : MorphismProperty Scheme.{u})) 𝒰

end AlgebraicGeometry

end
