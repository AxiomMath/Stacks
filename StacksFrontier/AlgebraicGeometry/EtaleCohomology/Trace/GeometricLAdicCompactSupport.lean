module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Compactly supported ℓ-adic cohomology of the geometric fibre

Let `X` be a separated scheme of finite type over a finite field `k`, let `k̄` be an extension
field of `k`, let `j : X ⟶ X̄` be a compactification of `X` over `k`, and let `F = {Fₙ}` be an
ℓ-adic sheaf on `X`.  The cohomology that Theorem B of the trace-formula chapter,
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2), is about is

`Hⁱ_c(X_k̄, F) = limₙ Hⁱ_c(X_k̄, Fₙ|_{X_k̄})`, and `Hⁱ_c(X_k̄, F ⊗ Q_ℓ) = Hⁱ_c(X_k̄, F) ⊗ Q_ℓ`,

the compactly supported cohomology of the *geometric fibre*, formed as in
[Tag 03UT](https://stacks.math.columbia.edu/tag/03UT).  Each level `Fₙ` is a sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules, hence of `ℤ_[ℓ]`-modules (`Stacks.EtaleCohomology.LAdicSheaf.padicLevel`),
and is fed, in degree zero, to the canonical
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` of
`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`, which agrees with the presentation of
Tag 0GJZ by `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIso`.

The geometric Frobenius `π_X^*` is the canonical one,
`Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusNatTrans`: the base change of the
Frobenius descent isomorphism of [Tag 03SR](https://stacks.math.columbia.edu/tag/03SR), with no
choice involved.  It passes to the limit because it is natural in the coefficient complex and
the maps of the inverse system are induced by the transition maps of `F`.

## Main definitions

* `Stacks.EtaleCohomology.geometricCompactSupportPadicCohomology`: `Hⁱ_c(X_k̄, -|_{X_k̄})` on
  sheaves of `ℤ_[ℓ]`-modules on the small étale site of Stacks 021B.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologySystem`: the inverse
  system `n ↦ Hⁱ_c(X_k̄, Fₙ)`.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomology`: its limit
  `Hⁱ_c(X_k̄, F)`.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomology`:
  `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)`.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedFrobenius` and
  `Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius`: `π_X^*` on
  them.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologyPullback` and
  `Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback`: the
  endomorphisms induced by an arbitrary natural endomorphism of `RΓ_c(X_k̄, -)`, of which the two
  above are the instance at the canonical Frobenius.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg`:
  `Hⁱ_c(X_k̄, F ⊗ Q_ℓ) = 0` for `i < 0`, the lower half of the degree bound of Tag 03V2.
* `Stacks.EtaleCohomology.isZero_compactlySupportedCohomologyGroup_single_of_neg`: the same
  vanishing for the presentation of Tag 0GJZ, for every sheaf of modules and every
  compactification.

## Implementation notes

The coefficients are `ℤ_[ℓ]` at every level, as in the statement of Tag 03UT: the levels are
restricted to
`ℤ_[ℓ]` on the sheaves, before cohomology is taken, so that the inverse system lives in one
category and its maps are induced by the transition maps of `F` with no comparison of
cohomology over different rings.

The vanishing in negative degrees holds for every ℓ-adic sheaf, every field `k̄` and every
compactification, with no finiteness, torsion or invertibility hypothesis: `RΓ_c(X_k̄, -)` is a
composite of exact functors and of right derived functors of additive functors, each of which
carries a complex concentrated in degrees `≥ 0` to one again concentrated in degrees `≥ 0`
(`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`); a limit of zero modules is zero,
and so is its extension of scalars.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 03UT](https://stacks.math.columbia.edu/tag/03UT)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### Compactly supported cohomology in negative degrees -/

section Negative

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]

/-- `RΓ_c(X, -)` carries a complex concentrated in degrees `≥ a` to one concentrated in degrees
`≥ a`: it is the composite of the right derived functors of extension by zero, of direct image
and of global sections. -/
public theorem isGE_compactlySupportedCohomology_obj
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) (a : ℤ) [K.IsGE a] :
    ((compactlySupportedCohomology.{u, r} k f j Λ).obj K).IsGE a := by
  have h₁ : ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K).IsGE a :=
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion).isGE_rightDerivedFunctorPlus_obj K a
  have h₂ : ((etaleModuleDerivedDirectImage.{u, r} Λ j.toBase).obj
      ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K)).IsGE a :=
    (etaleModuleDirectImage.{u, r} Λ j.toBase).isGE_rightDerivedFunctorPlus_obj _ a
  have : ((derivedLowerShriek.{u, r} f j Λ).obj K).IsGE a := h₂
  exact (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).isGE_rightDerivedFunctorPlus_obj
    ((derivedLowerShriek.{u, r} f j Λ).obj K) a

/-- `Hⁱ_c(X, K) = 0` for `i < a` when `K` is concentrated in degrees `≥ a`. -/
public theorem isZero_compactlySupportedCohomologyGroup_of_isGE
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) (a : ℤ) [K.IsGE a] (i : ℤ)
    (hi : i < a) :
    IsZero ((compactlySupportedCohomologyGroup.{u, r} k f j Λ i).obj K) := by
  have := isGE_compactlySupportedCohomology_obj k f j Λ K a
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ a i hi

/-- **`Hⁱ_c(X, G) = 0` for `i < 0`**, for every sheaf of `Λ`-modules `G` on the small étale site
of `X` and every compactification of `X`: the lower half of the degree bound of
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) at a single sheaf. -/
public theorem isZero_compactlySupportedCohomologyGroup_single_of_neg
    (G : EtaleModules.{u, r} Λ X) (i : ℤ) (hi : i < 0) :
    IsZero ((compactlySupportedCohomologyGroup.{u, r} k f j Λ i).obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj G)) :=
  isZero_compactlySupportedCohomologyGroup_of_isGE k f j Λ _ 0 i hi

end Negative

/-! ### The geometric fibre -/

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- A sheaf of `ℤ_[ℓ]`-modules on the small étale site of Stacks 021B, read on Mathlib's small
étale site (`AlgebraicGeometry.SmallEtale.sheafEquiv`) and placed in degree zero as a bounded
below complex. -/
public def padicCoefficientComplex :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] X.1) :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor ⋙
    ObjectProperty.lift _ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
      (fun _ => ⟨0, inferInstance⟩)

/-- **`Hⁱ_c(X_k̄, -|_{X_k̄})` with `ℤ_[ℓ]`-coefficients**, on sheaves of `ℤ_[ℓ]`-modules on the
small étale site of Stacks 021B: the `i`-th cohomology of the canonical
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` of
`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`, the complex on which the canonical
geometric Frobenius acts. -/
public def geometricCompactSupportPadicCohomology (i : ℤ) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
      ModuleCat.{u + 1} ℤ_[ℓ] :=
  padicCoefficientComplex B X ℓ ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i

/-- The inverse system `n ↦ Hⁱ_c(X_k̄, Fₙ)` of the compactly supported cohomology of the
geometric fibre with coefficients in the finite levels of an ℓ-adic sheaf. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologySystem (F : LAdicSheaf B X ℓ)
    (i : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
  Functor.ofOpSequence
    (X := fun n => (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n))
    (fun n => (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
      (LAdicSheaf.padicTransition B X ℓ F n))

/-- The `n`-th term of the inverse system is `Hⁱ_c(X_k̄, Fₙ)`. -/
@[simp]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystem_obj (F : LAdicSheaf B X ℓ)
    (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).obj (op n) =
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) :=
  rfl

/-- The map of the inverse system from level `n + 1` to level `n` is induced by the transition
map of the ℓ-adic sheaf. -/
@[simp]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ
    (F : LAdicSheaf B X ℓ) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).map
        (homOfLE (n.le_add_right 1)).op =
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
        (LAdicSheaf.padicTransition B X ℓ F n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The compactly supported ℓ-adic cohomology of the geometric fibre**,
`Hⁱ_c(X_k̄, F) = limₙ Hⁱ_c(X_k̄, Fₙ)`, as in [Tag 03UT](https://stacks.math.columbia.edu/tag/03UT)
for the restriction of `F` to `X_k̄`. -/
@[stacks 03UT "H^i_c(X_kbar, F) = lim_n H^i_c(X_kbar, F_n), on the geometric fibre"]
public def LAdicSheaf.geometricCompactlySupportedCohomology (F : LAdicSheaf B X ℓ) (i : ℤ) :
    ModuleCat.{u + 1} ℤ_[ℓ] :=
  limit (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)

/-- The projection of `Hⁱ_c(X_k̄, F)` onto `Hⁱ_c(X_k̄, Fₙ)`. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologyπ (F : LAdicSheaf B X ℓ) (i : ℤ)
    (n : ℕ) :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i ⟶
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) :=
  limit.π (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i) (op n)

/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ) = Hⁱ_c(X_k̄, F) ⊗_{ℤ_[ℓ]} ℚ_[ℓ]`**, the cohomology of the rational
ℓ-adic sheaf `F ⊗ Q_ℓ` that [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) is about. -/
@[stacks 03UT "H^i_c(X_kbar, F' ⊗ Q_ell) = H^i_c(X_kbar, F') ⊗_{Z_ell} Q_ell, on the geometric \
fibre", sga "4½ Rapport 2.10", sga "7 XXI 2.0" "more general"]
public def LAdicSheaf.rationalGeometricCompactlySupportedCohomology (F : LAdicSheaf B X ℓ)
    (i : ℤ) : ModuleCat.{u + 1} ℚ_[ℓ] :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
    (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i)

/-! ### Endomorphisms of `RΓ_c(X_k̄, -)` on the limit -/

section Pullback

variable (F : LAdicSheaf B X ℓ) (i : ℤ)
  (φ : compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⟶
    compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar)

/-- An endomorphism of `RΓ_c(X_k̄, -)`, read on `Hⁱ_c(X_k̄, -|_{X_k̄})` with
`ℤ_[ℓ]`-coefficients. -/
public def geometricCompactSupportPadicCohomologyPullback :
    geometricCompactSupportPadicCohomology B X ℓ f j kbar i ⟶
      geometricCompactSupportPadicCohomology B X ℓ f j kbar i :=
  Functor.whiskerLeft (padicCoefficientComplex B X ℓ)
    (Functor.whiskerRight φ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i))

/-- The endomorphism of the inverse system `n ↦ Hⁱ_c(X_k̄, Fₙ)` induced by `φ`: its components
commute with the maps of the system because `φ` is natural. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ⟶
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i :=
  NatTrans.ofOpSequence
    (fun n => (geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i φ).app
      (LAdicSheaf.padicLevel B X ℓ F n))
    (fun n => by
      simp only [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
      exact (geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i φ).naturality
        (LAdicSheaf.padicTransition B X ℓ F n))

/-- The endomorphism of `Hⁱ_c(X_k̄, F)` induced by an endomorphism `φ` of `RΓ_c(X_k̄, -)`; for
`φ` the geometric Frobenius this is `π_X^*`. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologyPullback :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i ⟶
      LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i :=
  limMap (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i φ)

/-- The endomorphism of the limit lies over the endomorphisms of the finite levels. -/
@[reassoc (attr := simp)]
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyPullback_π (n : ℕ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i φ ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n =
      LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n ≫
        (geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i φ).app
          (LAdicSheaf.padicLevel B X ℓ F n) :=
  limMap_π _ (op n)

/-- The endomorphism of `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` induced by `φ`. -/
public def LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ⟶
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i φ)

end Pullback

/-! ### The geometric Frobenius -/

section Frobenius

variable [Fintype k] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (F : LAdicSheaf B X ℓ) (i : ℤ)

/-- **`π_X^*` on `Hⁱ_c(X_k̄, F)`**: the endomorphism of the limit induced by the canonical
geometric Frobenius `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` of
`RΓ_c(X_k̄, -)`, which is the base change of the Frobenius descent isomorphism of Tag 03SR and
involves no choice. -/
public def LAdicSheaf.geometricCompactlySupportedFrobenius :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i ⟶
      LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i :=
  LAdicSheaf.geometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)

/-- **`π_X^*` on `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)`**, the endomorphism whose traces Tag 03V2 is about. -/
public def LAdicSheaf.rationalGeometricCompactlySupportedFrobenius :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ⟶
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i :=
  LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)

/-- At a finite level, `π_X^*` on `Hⁱ_c(X_k̄, F)` lies over the canonical
`π_X^* = canonicalCompactSupportFrobeniusGroup` on `Hⁱ_c(X_k̄, Fₙ)`. -/
@[reassoc]
public theorem LAdicSheaf.geometricCompactlySupportedFrobenius_π (n : ℕ) :
    LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n =
      LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n ≫
        canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i :=
  LAdicSheaf.geometricCompactlySupportedCohomologyPullback_π B X ℓ f j kbar F i _ n

end Frobenius

/-! ### Vanishing in negative degrees -/

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- `Hⁱ_c(X_k̄, G|_{X_k̄}) = 0` for `i < 0`. -/
public theorem isZero_geometricCompactSupportPadicCohomology_obj_of_neg
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ])) (i : ℤ)
    (hi : i < 0) :
    IsZero ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj G) := by
  have : ((padicCoefficientComplex B X ℓ).obj G).obj.IsStrictlyGE 0 := by
    change CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj G)) 0
    infer_instance
  have := isGE_compactSupportFrobeniusFunctor_obj.{u, 0} ℤ_[ℓ] f j kbar
    ((padicCoefficientComplex B X ℓ).obj G) 0
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i hi

/-- `Hⁱ_c(X_k̄, F) = 0` for `i < 0`: a limit of zero modules. -/
public theorem LAdicSheaf.isZero_geometricCompactlySupportedCohomology_of_neg
    (F : LAdicSheaf B X ℓ) (i : ℤ) (hi : i < 0) :
    IsZero (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  (IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun n =>
    (isZero_geometricCompactSupportPadicCohomology_obj_of_neg B X ℓ f j kbar
      (LAdicSheaf.padicLevel B X ℓ F n.unop) i hi).eq_of_tgt _ _)

/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ) = 0` for `i < 0`**, for every ℓ-adic sheaf `F` on a separated scheme of
finite type over a field, every extension field `k̄` and every compactification: the lower half
of the statement of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) that
`Hⁱ_c(X_k̄, F)` is nonzero for `0 ≤ i ≤ 2 dim X` only. -/
@[stacks 03V2 "the lower half of the degree bound: H^i_c(X_kbar, F) = 0 for i < 0"]
public theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg
    (F : LAdicSheaf B X ℓ) (i : ℤ) (hi : i < 0) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  Functor.map_isZero _
    (LAdicSheaf.isZero_geometricCompactlySupportedCohomology_of_neg B X ℓ f j kbar F i hi)

end EtaleCohomology

end Stacks
