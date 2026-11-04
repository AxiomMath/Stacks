module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisActionFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Homology.RightDerivedCollapseNaturality
public import Mathlib.Tactic.IrreducibleDef
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksCore.Tactic.StacksAttribute

/-!
# The Galois-equivariant comparison of `(R^j α_* ℱ)_{Spec K}` with `H^j(X_K, ℱ|_{X_K})`

Let `k` be a field, `K` an algebraically closed extension, `α : X ⟶ Spec k` and `ℱ` an abelian
sheaf on `X_étale`. This file builds the comparison of Étale Cohomology, Theorem 03Q9 at the
geometric point `Spec K ⟶ Spec k` in every degree `j`,

`(R^j α_* ℱ)_{Spec K} ⟶ H^j(X_K, ℱ|_{X_K})`,

and proves that it carries the Galois action of Étale Cohomology Section 03QW on the stalk to the
action `σ ↦ (Spec σ × id_X)^*` on cohomology, for every `σ ∈ Aut(K/k)` and every `j`. That it is
an isomorphism, for `α` quasi-compact and quasi-separated and `K` separable over `k`, is in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisModuleHigherDirectImageStalk.lean`, which registers Tag 03ST.

## Main definitions

* `Stacks.Frobenius.fieldGaloisStalkAction` — the action of `σ` on the stalk functor at
  `Spec K ⟶ Spec k` (Étale Cohomology Section 03QW); it is the base's
  `Stacks.Frobenius.galoisStalkAction` at `𝟙 (Spec k)` (`fieldGaloisStalkAction_eq`).
* `Stacks.Frobenius.fibreSectionsComparisonAb` — the degree-zero comparison of Stacks 0GIX through
  the strict henselization, and `Stacks.Frobenius.fibreComparisonNatTrans`, the same natural
  transformation built from the base's germwise `Stacks.Frobenius.fibreComparison`, independent of
  any big étale site (`fibreSectionsComparisonAb_eq`).
* `Stacks.Frobenius.galoisSectionsAction` — restriction of sections along `id_X × Spec σ`.
* `Stacks.Frobenius.galoisCohomologyAction` — the action `(Spec σ × id_X)^*` on
  `H^j(X_K, ℱ|_{X_K})`: pullback along `id_X × Spec σ` followed by the identification
  `(id_X × Spec σ)⁻¹ (ℱ|_{X_K}) ≅ ℱ|_{X_K}`.
* `Stacks.Frobenius.higherDirectImageFibreMap` — the comparison in degree `j`: the stalk passes
  through `R^j α_*`, the degree-zero comparison passes to right derived functors, and the right
  derived functors of `Γ(X_K, -|_{X_K})` are those of `Γ(X_K, -)` after restriction.

## Main results

* `Stacks.Frobenius.galoisStalkAction_comp_fibreComparisonNatTrans` — equivariance in degree zero,
  as an identity of natural transformations.
* `Stacks.Frobenius.galoisStalkAction_comp_higherDirectImageFibreMap` — equivariance in every
  degree.
* `Stacks.Frobenius.isIso_higherDirectImageFibreMap` — the degree-`j` comparison is an
  isomorphism when the degree-zero one is.

## Implementation notes

Equivariance in degree `j` is a consequence of equivariance in degree zero and of the naturality
of the three identifications the degree-`j` comparison is built from, which are proved in
`StacksFrontier/Homology/RightDerivedCollapseNaturality.lean`: the evaluation isomorphism is natural
in the exact functor, and the collapse `Rⁿ (G ⋙ T) ≅ Rⁿ T ∘ G` is natural in `T`, natural in `G`
and transitive in `G`. The Galois action on cohomology is pullback along `id_X × Spec σ`, which
is an automorphism, so inverse image along it is an equivalence and the collapse applies.

The two degree-zero comparisons are `irreducible_def`s: both are assembled from definitions of the
base in the vocabulary of the geometric fibre and the strict henselization, and the kernel, when
comparing the right derived functors they induce, otherwise unfolds them, which does not terminate
within the budget.

## References

* [Stacks Project, Tag 03ST](https://stacks.math.columbia.edu/tag/03ST)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03QW](https://stacks.math.columbia.edu/tag/03QW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology

universe u

namespace Stacks.Frobenius


section DegreeZero

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k))) (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of k)))

/-- The geometric point `Spec K ⟶ Spec k` of `Spec k`, its morphism being the structure morphism
`specAlgebraMap k K` on the nose. -/
abbrev fieldGeometricPoint : GeometricPoint (Spec (.of k)) where
  residueField := K
  hom := specAlgebraMap k K

/-- An automorphism `σ` of `K` over `k`, as an endomorphism of the geometric point
`Spec K ⟶ Spec k`: `Spec σ` lies over `Spec k` because `σ` fixes `k`. -/
def fieldGaloisPointHom (σ : K ≃ₐ[k] K) :
    GeometricPoint.Hom (fieldGeometricPoint (k := k) K) (fieldGeometricPoint (k := k) K) where
  hom := Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)
  comm := by
    have h : CommRingCat.ofHom (algebraMap k K) ≫
        CommRingCat.ofHom σ.toAlgHom.toRingHom = CommRingCat.ofHom (algebraMap k K) := by
      ext y
      exact σ.commutes y
    change Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp, h]

/-- **The Galois action of Étale Cohomology Section 03QW on the stalk functor at `Spec K`.** The
action of `σ ∈ G_k` on the stalk functor at the geometric point `Spec K ⟶ Spec k`, induced by
`σ` as an endomorphism of that geometric point (Tag 04FN). -/
def fieldGaloisStalkAction (σ : K ≃ₐ[k] K) :
    smallEtaleStalkAb (specAlgebraMap k K) ⟶ smallEtaleStalkAb (specAlgebraMap k K) :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (smallEtalePointHom (Spec (.of k)) (fieldGaloisPointHom K σ))

/-- It is the action `Stacks.Frobenius.galoisStalkAction` of the base, at the rational point
`𝟙 (Spec k)`. -/
theorem fieldGaloisStalkAction_eq (σ : K ≃ₐ[k] K) :
    fieldGaloisStalkAction K σ = galoisStalkAction Ab.{u + 1} K σ (𝟙 (Spec (.of k))) :=
  rfl

/-- The identity acts trivially on the stalk functor. -/
theorem fieldGaloisStalkAction_one : fieldGaloisStalkAction K (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  rw [fieldGaloisStalkAction,
    smallEtalePointHom_id (fieldGaloisPointHom K (1 : K ≃ₐ[k] K))
      (show Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom (1 : K ≃ₐ[k] K)).toRingHom) = _ by
        rw [show CommRingCat.ofHom (AlgEquiv.toAlgHom (1 : K ≃ₐ[k] K)).toRingHom =
          𝟙 (CommRingCat.of K) from rfl, Spec.map_id])]
  exact GrothendieckTopology.Point.Hom.sheafFiber_id _

/-- The Galois group acts on the left on the stalk functor. -/
theorem fieldGaloisStalkAction_mul (σ τ : K ≃ₐ[k] K) :
    fieldGaloisStalkAction K (σ * τ) = fieldGaloisStalkAction K τ ≫ fieldGaloisStalkAction K σ := by
  rw [fieldGaloisStalkAction, fieldGaloisStalkAction, fieldGaloisStalkAction,
    smallEtalePointHom_comp (fieldGaloisPointHom K σ) (fieldGaloisPointHom K τ)
      (fieldGaloisPointHom K (σ * τ)) (by
        show Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp]
        rfl)]
  exact GrothendieckTopology.Point.Hom.sheafFiber_comp _ _

/-- **The degree-zero comparison.** The map `(α_* F)_{Spec K} ⟶ Γ(X_K, F|_{X_K})` of Stacks 0GIX:
the canonical map from the stalk to sections over the base change to the strict henselization,
followed by restriction along `X_K ⟶ X ×_{Spec k} Spec 𝒪^{sh}`.

The definition is irreducible: it is stated in the vocabulary of `X_K` but built in that of the
geometric fibre and the strict henselization, and a kernel check which unfolds it while comparing
the right derived functors it induces does not terminate inside the budget. Its body is
`Stacks.Frobenius.fibreSectionsComparisonAb_def`. -/
irreducible_def fibreSectionsComparisonAb :
    smallEtalePushforwardAb X.hom ⋙ smallEtaleStalkAb (specAlgebraMap k K) ⟶
      smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1} :=
  pushforwardStalkToStrictHenselizationSectionsAb B hS X.hom (fieldGeometricPoint K) ≫
    Functor.whiskerLeft
      (smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hS X.hom (fieldGeometricPoint K)))
      (smallEtaleGlobalSectionsRestrictionAb
        (geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K))) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (geometricFibrePullbackAbCompIso B hS X.hom (fieldGeometricPoint K)).hom
      (Sheaf.Γ (smallEtaleTopology (geometricFibre X.hom (fieldGeometricPoint K))) Ab.{u + 1})

/-- The lift of `X_K` into the base change of an étale neighbourhood, through the strict
henselization, is the morphism `fibreLift`. -/
theorem geometricFibreToStrictHenselizationBaseChange_comp_etaleLift (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K) ≫
        strictHenselizationBaseChangeEtaleLift B hS X.hom (fieldGeometricPoint K) W u =
      fibreLift K X W u := by
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (geometricFibreToStrictHenselizationBaseChange B hS X.hom
      (fieldGeometricPoint K) ≫ ·) (pullback.lift_fst _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ strictHenselizationNeighborhoodLift B (Spec (.of k)) hS
      (fieldGeometricPoint K) W u) (pullback.lift_snd _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (geometricFibreToPoint X.hom (fieldGeometricPoint K) ≫ ·)
      (geometricPointToStrictHenselization_comp_neighborhoodLift B (Spec (.of k)) hS
        (fieldGeometricPoint K) W u)).trans ?_
    exact (pullback.lift_fst _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (geometricFibreToStrictHenselizationBaseChange B hS X.hom
      (fieldGeometricPoint K) ≫ ·) (pullback.lift_snd _ _ _)).trans ?_
    exact (pullback.lift_fst _ _ _).trans (pullback.lift_snd _ _ _).symm

variable (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1})

/-- **On germs the degree-zero comparison is restriction to the geometric fibre.** -/
theorem toPresheafFiber_comp_fibreSectionsComparisonAb (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber W u
          ((sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F)) ≫
        (fibreSectionsComparisonAb K X B hS).app F =
      fibreGerm K X F W u := by
  rw [fibreSectionsComparisonAb_def]
  have h1 := pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS X.hom
    (fieldGeometricPoint K) W u F
  have h2 := smallEtaleSectionsPullbackAb_comp_base
    (strictHenselizationBaseChangeToSource B hS X.hom (fieldGeometricPoint K))
    (geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K))
    ((smallEtaleBaseChange X.hom).obj W)
    (strictHenselizationBaseChangeEtaleLift B hS X.hom (fieldGeometricPoint K) W u)
    (by exact pullback.lift_snd _ _ _)
    (by rw [Category.assoc]; exact congrArg _ (pullback.lift_snd _ _ _))
  have h3 := smallEtaleSectionsPullbackAb_congr_base ((smallEtaleBaseChange X.hom).obj W)
    (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS X.hom
      (fieldGeometricPoint K))
    (geometricFibreToStrictHenselizationBaseChange_comp_etaleLift K X B hS W u)
    (by rw [Category.assoc]; exact congrArg _ (pullback.lift_snd _ _ _))
    (fibreLift_comp_hom K X W u)
  have key : Functor.whiskerLeft
        (smallEtalePullbackAb
          (strictHenselizationBaseChangeToSource B hS X.hom (fieldGeometricPoint K)))
        (smallEtaleGlobalSectionsRestrictionAb
          (geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K))) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (geometricFibrePullbackAbCompIso B hS X.hom (fieldGeometricPoint K)).hom
        (Sheaf.Γ (smallEtaleTopology (geometricFibre X.hom (fieldGeometricPoint K)))
          Ab.{u + 1}) =
      Functor.whiskerLeft
        (smallEtalePullbackAb
          (strictHenselizationBaseChangeToSource B hS X.hom (fieldGeometricPoint K)))
        (smallEtaleGlobalSectionsRestrictionAb
          (geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K))) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (smallEtalePullbackAbCompIso
          (geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K))
          (strictHenselizationBaseChangeToSource B hS X.hom (fieldGeometricPoint K))).hom
        (Sheaf.Γ (smallEtaleTopology (geometricFibre X.hom (fieldGeometricPoint K)))
          Ab.{u + 1}) ≫
      Functor.whiskerRight
        (eqToIso (congrArg (fun m : geometricFibre X.hom (fieldGeometricPoint K) ⟶ X.left =>
          smallEtalePullbackAb m)
          (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS X.hom
            (fieldGeometricPoint K)))).hom
        (Sheaf.Γ (smallEtaleTopology (geometricFibre X.hom (fieldGeometricPoint K)))
          Ab.{u + 1}) := by
    rw [geometricFibrePullbackAbCompIso_hom, Functor.whiskerRight_comp]
    rfl
  rw [h2] at h3
  simp only [Category.assoc] at h3
  rw [← key] at h3
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  exact (congrArg (fun φ => NatTrans.app φ F) h3).symm

/-- The degree-zero comparison is the comparison `fibreComparison` built germwise. -/
theorem fibreSectionsComparisonAb_app :
    (fibreSectionsComparisonAb K X B hS).app F = fibreComparison K X F :=
  (Scheme.pointSmallEtale (specAlgebraMap k K)).presheafFiber_hom_ext fun W u =>
    (toPresheafFiber_comp_fibreSectionsComparisonAb K X B hS F W u).trans
      (toPresheafFiber_comp_fibreComparison K X F W u).symm

end DegreeZero


section GaloisSections

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] (X : Over (Spec (.of k)))

/-- **The coefficient identification along the Galois action.** Since `id_X × Spec σ` lies over
`X`, inverse image along it of the restriction of a sheaf on `X_étale` to `X_K` is that
restriction again. -/
@[sga "7 XIII 1.1.2" "partial"]
def galoisPullbackAbIso (σ : K ≃ₐ[k] K) :
    smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        smallEtalePullbackAb (galoisBaseChange X K σ) ≅
      smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) :=
  smallEtalePullbackAbCompIso (galoisBaseChange X K σ)
      (pullback.fst X.hom (specAlgebraMap k K)) ≪≫
    eqToIso (congrArg (fun m : fieldBaseChange X K ⟶ X.left => smallEtalePullbackAb m)
      (galoisBaseChange_comp_fst X K σ))

/-- **The Galois action on global sections over `X_K` of a restricted sheaf.** For `σ ∈ G_k`,
restriction of global sections along `id_X × Spec σ : X_K ⟶ X_K`, followed by the identification
`(id_X × Spec σ)⁻¹ (F|_{X_K}) ≅ F|_{X_K}` which holds because `id_X × Spec σ` lies over `X`. -/
def galoisSectionsAction (σ : K ≃ₐ[k] K) :
    smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1} ⟶
      smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1} :=
  Functor.whiskerLeft (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
      (smallEtaleGlobalSectionsRestrictionAb (galoisBaseChange X K σ)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (galoisPullbackAbIso K X σ).hom
      (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})

/-- Restriction of a section along a morphism into an étale object over `X`, followed by the
Galois action on sections over `X_K`, is restriction along the morphism precomposed with
`id_X × Spec σ`. -/
theorem smallEtaleSectionsPullbackAb_comp_galoisSectionsAction (σ : K ≃ₐ[k] K)
    (W : X.left.Etale) (r : fieldBaseChange X K ⟶ W.left)
    (hr : r ≫ W.hom = pullback.fst X.hom (specAlgebraMap k K))
    (hσr : (galoisBaseChange X K σ ≫ r) ≫ W.hom = pullback.fst X.hom (specAlgebraMap k K)) :
    smallEtaleSectionsPullbackAb (pullback.fst X.hom (specAlgebraMap k K)) W r hr ≫
        galoisSectionsAction K X σ =
      smallEtaleSectionsPullbackAb (pullback.fst X.hom (specAlgebraMap k K)) W
        (galoisBaseChange X K σ ≫ r) hσr := by
  have hcomp := smallEtaleSectionsPullbackAb_comp_base
    (pullback.fst X.hom (specAlgebraMap k K)) (galoisBaseChange X K σ) W r hr
    (by rw [Category.assoc, hr])
  have hcongr := smallEtaleSectionsPullbackAb_congr_base W (galoisBaseChange_comp_fst X K σ)
    (rfl : galoisBaseChange X K σ ≫ r = galoisBaseChange X K σ ≫ r)
    (by rw [Category.assoc, hr]) hσr
  rw [hcongr, hcomp]
  simp only [galoisSectionsAction, galoisPullbackAbIso, Iso.trans_hom, Functor.whiskerRight_comp,
    Category.assoc]

end GaloisSections

section DegreeZeroEquivariance

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k))) (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of k)))

/-- **Galois equivariance in degree zero, as an identity of natural transformations.** The
comparison `(α_* F)_{Spec K} ⟶ Γ(X_K, F|_{X_K})` carries the Galois action of Étale Cohomology
Section 03QW on the stalk to the Galois action by restriction along `id_X × Spec σ`, naturally in
the sheaf `F`. -/
theorem galoisStalkAction_comp_fibreSectionsComparisonAb (σ : K ≃ₐ[k] K) :
    Functor.whiskerLeft (smallEtalePushforwardAb X.hom) (fieldGaloisStalkAction K σ) ≫
      fibreSectionsComparisonAb K X B hS =
      fibreSectionsComparisonAb K X B hS ≫ galoisSectionsAction K X σ := by
  rw [fieldGaloisStalkAction_eq]
  refine NatTrans.ext (funext fun F => ?_)
  refine (Scheme.pointSmallEtale (specAlgebraMap k K)).presheafFiber_hom_ext fun W u => ?_
  have e1 := fibreComparison_galoisStalkAction K X F σ W u
  have e2 := fibreSectionsComparisonAb_app K X B hS F
  have e3 := toPresheafFiber_comp_fibreSectionsComparisonAb K X B hS F W u
  have e4 := congrArg (fun φ => NatTrans.app φ F)
    (smallEtaleSectionsPullbackAb_comp_galoisSectionsAction K X σ
      ((smallEtaleBaseChange X.hom).obj W) (fibreLift K X W u) (fibreLift_comp_hom K X W u)
      ((congrArg (fun z => z ≫ ((smallEtaleBaseChange X.hom).obj W).hom)
            (galoisBaseChange_comp_fibreLift K X σ W u).symm).trans
          (fibreLift_comp_hom K X W (galoisLift K σ W u))))
  refine ((congrArg (fun t => (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber W u
      ((sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F)) ≫
        (galoisStalkAction Ab.{u + 1} K σ (𝟙 (Spec (.of k)))).app
          ((smallEtalePushforwardAb X.hom).obj F) ≫ t) e2).trans e1).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ (galoisSectionsAction K X σ).app F) e3).symm
  exact e4.symm

end DegreeZeroEquivariance

section ComparisonNatTrans

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k)))

/-- A big étale site containing `Spec k`. The comparison of Theorem 03Q9 is built inside a big
étale site, but does not depend on it (`Stacks.Frobenius.fibreSectionsComparisonAb_eq`). -/
noncomputable abbrev fieldBigEtaleSite : BigEtaleSite.{u} :=
  BigEtaleSite.ofSet {Spec (.of k)}

/-- The big étale site `Stacks.Frobenius.fieldBigEtaleSite` contains `Spec k`. -/
theorem fieldBigEtaleSite_contains : (fieldBigEtaleSite (k := k)).Contains (Spec (.of k)) :=
  BigEtaleSite.contains_ofSet _ rfl

/-- **The degree-zero comparison of Étale Cohomology, Theorem 03Q9, at `Spec K ⟶ Spec k`, as a
natural transformation.** Its component at `F` is the comparison
`Stacks.Frobenius.fibreComparison` `(α_* F)_{Spec K} ⟶ Γ(X_K, F|_{X_K})`, which restricts the germ
of a section over an étale neighbourhood `W` of `Spec K` along `X_K ⟶ X_W`.

It is irreducible, for the reason given at `Stacks.Frobenius.fibreSectionsComparisonAb`; its
components are `Stacks.Frobenius.fibreComparisonNatTrans_app`. -/
irreducible_def fibreComparisonNatTrans :
    smallEtalePushforwardAb X.hom ⋙ smallEtaleStalkAb (specAlgebraMap k K) ⟶
      smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1} where
  app F := fibreComparison K X F
  naturality {F F'} φ := by
    have h := (fibreSectionsComparisonAb K X fieldBigEtaleSite
      fieldBigEtaleSite_contains).naturality φ
    rwa [fibreSectionsComparisonAb_app, fibreSectionsComparisonAb_app] at h

/-- The components of the degree-zero comparison. -/
theorem fibreComparisonNatTrans_app (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    (fibreComparisonNatTrans K X).app F = fibreComparison K X F := by
  rw [fibreComparisonNatTrans_def]

/-- The comparison built through the strict henselization inside any big étale site is the
degree-zero comparison. -/
theorem fibreSectionsComparisonAb_eq (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of k))) :
    fibreSectionsComparisonAb K X B hS = fibreComparisonNatTrans K X :=
  NatTrans.ext (funext fun F =>
    (fibreSectionsComparisonAb_app K X B hS F).trans (fibreComparisonNatTrans_app K X F).symm)

/-- **Galois equivariance in degree zero.** The degree-zero comparison carries the Galois action of
Étale Cohomology Section 03QW on the stalk to the Galois action by restriction along
`id_X × Spec σ`, naturally in the sheaf. -/
theorem galoisStalkAction_comp_fibreComparisonNatTrans (σ : K ≃ₐ[k] K) :
    Functor.whiskerLeft (smallEtalePushforwardAb X.hom) (fieldGaloisStalkAction K σ) ≫
      fibreComparisonNatTrans K X =
      fibreComparisonNatTrans K X ≫ galoisSectionsAction K X σ := by
  rw [← fibreSectionsComparisonAb_eq K X fieldBigEtaleSite fieldBigEtaleSite_contains]
  exact galoisStalkAction_comp_fibreSectionsComparisonAb K X _ _ σ

end ComparisonNatTrans


section Rearrangements

variable {C : Type*} [Category C]

/-- The rearrangement behind `rightDerived_galoisSectionsAction_comp_objIsoOfAcyclicImage`, at an
abstract category. -/
theorem collapse_square_rearrange {P Q M N L : C} (x : P ⟶ Q) (y : Q ⟶ P) (cq : P ⟶ M)
    (c₁ : Q ⟶ N) (c₂ : N ⟶ L) (c₁₂ : Q ⟶ L) (m : L ⟶ M) (r : M ⟶ N)
    (hT : x ≫ c₁ = cq ≫ r) (hC : c₁ ≫ c₂ = c₁₂) (hG : y ≫ cq = c₁₂ ≫ m) :
    (x ≫ y) ≫ cq = cq ≫ r ≫ c₂ ≫ m := by
  rw [Category.assoc, hG, ← hC]
  simp only [Category.assoc]
  rw [← Category.assoc x c₁, hT, Category.assoc]

/-- The rearrangement behind `galoisStalkAction_comp_higherDirectImageFibreIso`, at an abstract
category. -/
theorem three_squares_rearrange {A B C' D : C} (s : A ⟶ A) (e : A ⟶ B) (t : B ⟶ B) (r : B ⟶ C')
    (w : C' ⟶ C') (l : C' ⟶ D) (v : D ⟶ D) (h₁ : s ≫ e = e ≫ t) (h₂ : t ≫ r = r ≫ w)
    (h₃ : w ≫ l = l ≫ v) : s ≫ e ≫ r ≫ l = (e ≫ r ≫ l) ≫ v := by
  rw [← Category.assoc s, h₁, Category.assoc, ← Category.assoc t, h₂, Category.assoc, h₃]
  simp only [Category.assoc]

end Rearrangements

section DegreeJ

open Stacks.RightDerivedComp

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] (X : Over (Spec (.of k)))

/-- `id_X × Spec σ` is an automorphism of `X_K`, with inverse `id_X × Spec σ⁻¹`. -/
instance isIso_galoisBaseChange (σ : K ≃ₐ[k] K) : IsIso (galoisBaseChange X K σ) :=
  ⟨⟨galoisBaseChange X K σ⁻¹,
    by rw [← galoisBaseChange_mul, mul_inv_cancel, galoisBaseChange_one],
    by rw [← galoisBaseChange_mul, inv_mul_cancel, galoisBaseChange_one]⟩⟩

/-- Inverse image along the automorphism `id_X × Spec σ` of `X_K` preserves injective sheaves: it
is an equivalence. -/
theorem injective_galoisPullbackAb (σ : K ≃ₐ[k] K)
    (Z : Sheaf (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}) [Injective Z] :
    Injective ((smallEtalePullbackAb (galoisBaseChange X K σ)).obj Z) := by
  have := isEquivalence_smallEtalePullbackAb_of_isIso (galoisBaseChange X K σ)
  exact (smallEtalePullbackAb (galoisBaseChange X K σ)).injective_obj Z

/-- `(id_X × Spec σ)⁻¹` carries injective sheaves to `Γ`-acyclic ones. -/
theorem acyclic_galoisPullbackAb_of_injective (σ : K ≃ₐ[k] K)
    (Z : Sheaf (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}) (hZ : Injective Z) :
    acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
      ((smallEtalePullbackAb (galoisBaseChange X K σ)).obj Z) :=
  have := hZ
  have := injective_galoisPullbackAb K X σ Z
  acyclic_of_injective _ _

/-- **The Galois action on `H^j(X_K, F|_{X_K})`.** For `σ ∈ G_k`, pullback on cohomology along the
automorphism `id_X × Spec σ` of `X_K`, `H^j(X_K, F|) ⟶ H^j(X_K, (id_X × Spec σ)⁻¹ F|)`, followed by
the identification `(id_X × Spec σ)⁻¹ (F|_{X_K}) ≅ F|_{X_K}`, which holds because `id_X × Spec σ`
lies over `X`. Pullback is the right derived functor of restriction of global sections along
`id_X × Spec σ`, read through the inverse image, which is exact and preserves injectives. -/
def galoisCohomologyAction (σ : K ≃ₐ[k] K) (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) ⟶
      ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) :=
  (NatTrans.rightDerived (smallEtaleGlobalSectionsRestrictionAb (galoisBaseChange X K σ)) j).app
      _ ≫
    (objIsoOfAcyclicImage (smallEtalePullbackAb (galoisBaseChange X K σ))
      (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
      (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn)
      (acyclic_galoisPullbackAb_of_injective K X σ) j).hom ≫
    ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).map
      ((galoisPullbackAbIso K X σ).hom.app F)

variable [IsAlgClosed K]

/-- **The comparison of Étale Cohomology, Theorem 03Q9, in degree `j`.** Given that restriction to
`X_K` carries injective sheaves to `Γ`-acyclic ones, the map `(R^j α_* F)_{Spec K} ⟶
H^j(X_K, F|_{X_K})` induced by the degree-zero comparison: the stalk is exact, so passes through
`R^j α_*`; the degree-zero comparison `(α_* -)_{Spec K} ⟶ Γ(X_K, -|_{X_K})` induces a map of right
derived functors; and the right derived functors of `Γ(X_K, -|_{X_K})` are those of `Γ(X_K, -)`
after restriction. -/
def higherDirectImageFibreMap
    (hacyc : ∀ Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}, Injective Z →
      acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj Z))
    (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    (smallEtaleStalkAb (specAlgebraMap k K)).obj
        (((smallEtalePushforwardAb X.hom).rightDerived j).obj F) ⟶
      ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) :=
  (Stacks.DerivedFunctor.rightDerivedEvaluationIso (smallEtalePushforwardAb X.hom)
      (smallEtaleStalkAb (specAlgebraMap k K)) F j).hom ≫
    (NatTrans.rightDerived (fibreComparisonNatTrans K X) j).app F ≫
    (objIsoOfAcyclicImage (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
      (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
      (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn) hacyc j).hom

/-- When the degree-zero comparison is an isomorphism, so is its degree-`j` form. -/
theorem isIso_higherDirectImageFibreMap (hc : IsIso (fibreComparisonNatTrans K X))
    (hacyc : ∀ Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}, Injective Z →
      acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj Z))
    (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    IsIso (higherDirectImageFibreMap K X hacyc j F) := by
  have : IsIso (NatTrans.rightDerived (fibreComparisonNatTrans K X) j) :=
    ⟨⟨NatTrans.rightDerived (inv (fibreComparisonNatTrans K X)) j,
      by rw [← NatTrans.rightDerived_comp, IsIso.hom_inv_id, NatTrans.rightDerived_id],
      by rw [← NatTrans.rightDerived_comp, IsIso.inv_hom_id, NatTrans.rightDerived_id]⟩⟩
  unfold higherDirectImageFibreMap
  infer_instance

omit [IsAlgClosed K] in
/-- The right derived functors of the Galois action on sections over `X_K`, after the collapse
along restriction to `X_K`, are the Galois action on `H^j(X_K, -|_{X_K})`. -/
theorem rightDerived_galoisSectionsAction_comp_objIsoOfAcyclicImage (σ : K ≃ₐ[k] K)
    (hacyc : ∀ Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}, Injective Z →
      acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj Z))
    (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    (NatTrans.rightDerived (galoisSectionsAction K X σ) j).app F ≫
        (objIsoOfAcyclicImage (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
          (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
          (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn) hacyc j).hom =
      (objIsoOfAcyclicImage (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
          (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
          (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn) hacyc j).hom ≫
        galoisCohomologyAction K X σ j F := by
  have : PreservesFiniteLimits
      (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        smallEtalePullbackAb (galoisBaseChange X K σ)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
        smallEtalePullbackAb (galoisBaseChange X K σ)) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits
      (smallEtalePullbackAb (galoisBaseChange X K σ) ⋙
        Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}) :=
    comp_preservesFiniteLimits _ _
  have hGT' : ∀ Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}, Injective Z →
      acyclic (smallEtalePullbackAb (galoisBaseChange X K σ) ⋙
          Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj Z) :=
    fun Z hZ n hn => ((hacyc Z hZ) n hn).of_iso
      ((objIsoOfAcyclicImage (smallEtalePullbackAb (galoisBaseChange X K σ))
          (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
          (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn)
          (acyclic_galoisPullbackAb_of_injective K X σ) n) ≪≫
        ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived n).mapIso
          ((galoisPullbackAbIso K X σ).app Z))
  have hGT₁₂ : ∀ Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}, Injective Z →
      acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
          smallEtalePullbackAb (galoisBaseChange X K σ)).obj Z) :=
    fun Z hZ => acyclic_of_iso _ ((galoisPullbackAbIso K X σ).app Z).symm (hacyc Z hZ)
  have hT := rightDerived_whiskerLeft_comp_objIsoOfAcyclicImage
    (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
    (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
    (smallEtaleGlobalSectionsRestrictionAb (galoisBaseChange X K σ)) (A := F)
    (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn) hacyc hGT' j
  have hC := objIsoOfAcyclicImage_trans
    (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
    (smallEtalePullbackAb (galoisBaseChange X K σ))
    (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}) (A := F)
    (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn)
    (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn)
    (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn) hGT'
    (acyclic_galoisPullbackAb_of_injective K X σ) hGT₁₂ j
  have hG := rightDerived_whiskerRight_comp_objIsoOfAcyclicImage
    (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)) ⋙
      smallEtalePullbackAb (galoisBaseChange X K σ))
    (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
    (galoisPullbackAbIso K X σ).hom (A := F)
    (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn)
    (fun n hn => isZero_rightDerived_obj_of_exact _ _ n hn) hGT₁₂ hacyc j
  have hτ : NatTrans.rightDerived (galoisSectionsAction K X σ) j =
      NatTrans.rightDerived (Functor.whiskerLeft
          (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
          (smallEtaleGlobalSectionsRestrictionAb (galoisBaseChange X K σ))) j ≫
        NatTrans.rightDerived (Functor.whiskerRight (galoisPullbackAbIso K X σ).hom
          (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})) j := by
    rw [galoisSectionsAction, NatTrans.rightDerived_comp, NatTrans.rightDerived_comp,
      show (Functor.associator (smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K)))
        (smallEtalePullbackAb (galoisBaseChange X K σ))
        (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})).inv = 𝟙 _ from rfl,
      NatTrans.rightDerived_id, Category.id_comp]
  rw [hτ, NatTrans.comp_app]
  exact collapse_square_rearrange _ _ _ _ _ _ _ _ hT hC hG


/-- **Galois equivariance of the identification of Theorem 03Q9, in every degree.** The
identification `(R^j α_* F)_{Spec K} ≅ H^j(X_K, F|_{X_K})` carries the Galois action of Étale
Cohomology Section 03QW on the stalk to the Galois action `(Spec σ × id_X)^*` on cohomology. -/
theorem galoisStalkAction_comp_higherDirectImageFibreMap (σ : K ≃ₐ[k] K)
    (hacyc : ∀ Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}, Injective Z →
      acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj Z))
    (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    (fieldGaloisStalkAction K σ).app (((smallEtalePushforwardAb X.hom).rightDerived j).obj F) ≫
        higherDirectImageFibreMap K X hacyc j F =
      higherDirectImageFibreMap K X hacyc j F ≫
        galoisCohomologyAction K X σ j F := by
  have h₁ := Stacks.DerivedFunctor.app_comp_rightDerivedEvaluationIso
    (smallEtalePushforwardAb X.hom) (fieldGaloisStalkAction K σ) F j
  have h₂ : (NatTrans.rightDerived (Functor.whiskerLeft (smallEtalePushforwardAb X.hom)
        (fieldGaloisStalkAction K σ)) j).app F ≫
      (NatTrans.rightDerived (fibreComparisonNatTrans K X) j).app F =
      (NatTrans.rightDerived (fibreComparisonNatTrans K X) j).app F ≫
        (NatTrans.rightDerived (galoisSectionsAction K X σ) j).app F := by
    rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp,
      galoisStalkAction_comp_fibreComparisonNatTrans, NatTrans.rightDerived_comp,
      NatTrans.comp_app]
  unfold higherDirectImageFibreMap
  exact three_squares_rearrange _ _ _ _ _ _ _ h₁ h₂
    (rightDerived_galoisSectionsAction_comp_objIsoOfAcyclicImage K X σ hacyc j F)
end DegreeJ

end Stacks.Frobenius

end
