module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforwardConjugation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorRightConjugate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationRankOne
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist

/-!
# Twisting the Quot functor by an invertible module (Stacks 0DP7)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `F` a quasi-coherent
`𝒪_X`-module and `L` an invertible `𝒪_X`-module, and write `G = F ⊗ L`.  Over a scheme `T` over
`B` the pullback of `G` is `G_T = F_T ⊗ L_T` (Stacks 03EL), and a quotient `F_T ⟶ Q` in
`Quot_{F/X/B}(T)` gives the quotient `G_T ⟶ Q ⊗ L_T`, which lies in `Quot_{G/X/B}(T)`.  This is
compatible with pullback and bijective, tensoring by `L_T` being an autoequivalence; so it is an
isomorphism of functors `Quot_{F/X/B} ≅ Quot_{F ⊗ L/X/B}`, which is the first assertion of
Stacks 0DP7.

For the second assertion, the fibre of `Q ⊗ L_T` at a point `t ∈ T`, twisted by `L_t^{⊗ n}`, is
the fibre of `Q` twisted by `L_t^{⊗ (n + 1)}`, so
`χ(X_t, (Q ⊗ L_T)_t ⊗ L_t^{⊗ n}) = χ(X_t, Q_t ⊗ L_t^{⊗ (n + 1)})`
(`AlgebraicGeometry.Space.CoherentObject.twistedEuler_mk_tensor`).  Hence a quotient lies in
`Quot^P_{F/X/B}` exactly when its image lies in `Quot^{P'}_{F ⊗ L/X/B}`, with `P'(t) = P(t + 1)`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.tensorInvertible`: the situation `F ⊗ L / X / B`.
* `AlgebraicGeometry.Space.QuotSituation.tensorQuotient`: the operation
  `(F_T ⟶ Q) ↦ (G_T ⟶ Q ⊗ L_T)` on quotients, recorded by kernels.
* `AlgebraicGeometry.Space.QuotSituation.quotFunctorTensorInvertibleIso`: the isomorphism
  `Quot_{F/X/B} ≅ Quot_{F ⊗ L/X/B}` of functors on the schemes over `B`.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheafTensorInvertibleIso`: the same
  isomorphism of presheaves on the schemes of the big fppf site.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.tensorQuotient_mem_iff`: the operation preserves and
  reflects the four conditions of Stacks 09TR.
* `AlgebraicGeometry.Space.QuotSituation.tensorQuotient_bijective`: it is a bijection on quotients.
* `AlgebraicGeometry.Space.QuotSituation.tensorQuotient_quotientPullback`: it commutes with
  pullback of quotients.
* `AlgebraicGeometry.Space.QuotSituation.hasHilbertPolynomial_tensorCohObject_iff`: the object
  `(T, Q ⊗ L_T)` has Hilbert polynomial `P'` exactly when `(T, Q)` has Hilbert polynomial `P`.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheafTensorInvertibleIso_spec`:
  **Stacks 0DP7.**

## Implementation notes

A quotient is recorded by its kernel, and the new quotient is the conjugate of the old one, in the
sense of `CategoryTheory.Functor.conjSubobject`, by the comparison
`f_T^*(- ⊗ L) ≅ f_T^*(-) ⊗ L_T` of Stacks 03EL.  Compatibility with pullback is the composition
law of that comparison, which is proved for morphisms of ringed topoi; it applies to the pullback
of quotients of Stacks 09TR because the composition comparison of Stacks 03LU for algebraic spaces
is the one of the morphisms of small étale ringed topoi
(`AlgebraicGeometry.Space.modulePullbackCompIso_eq_pullbackModulesCompIso`).

The four conditions of Stacks 09TR are checked on `Q ⊗ L_T` as follows.  Quasi-coherence and
finite presentation are preserved and reflected because `L_T` is locally trivial on the small
étale site; flatness over `T` and the support are read on geometric stalks, where tensoring by
`L_T` changes nothing.

Membership in `Quot^P_{F/X/B}` is read on the object of `Coh_{X/B}` a quotient gives, through the
twisted Euler characteristics `χ(X_t, Q_t ⊗ L_t^{⊗ n})` of Stacks 0DNF
(`AlgebraicGeometry.Space.CoherentObject.HasHilbertPolynomial`); this is the condition the
subfunctor `AlgebraicGeometry.Space.QuotSituation.quotCondition` cuts out of the Quot presheaf.
The statement holds for every function `P : ℤ → ℤ`, not only for numerical polynomials, and does
not use that `f` is separated.

## References

* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A coproduct of a single copy of an object is that object. -/
def isoOfIsColimitCofanFinOne {C : Type*} [Category C] {X Y : C} (ι : Fin 1 → (X ⟶ Y))
    (h : IsColimit (Cofan.mk Y ι)) : X ≅ Y where
  hom := ι 0
  inv := Cofan.IsColimit.desc h (fun _ => 𝟙 X)
  hom_inv_id := by simpa using Cofan.IsColimit.fac h (fun _ => 𝟙 X) 0
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext h
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have : ι 0 ≫ Cofan.IsColimit.desc h (fun _ => 𝟙 X) = 𝟙 X :=
      Cofan.IsColimit.fac h (fun _ => 𝟙 X) 0
    change ι 0 ≫ _ ≫ ι 0 = ι 0 ≫ 𝟙 Y
    rw [reassoc_of% this]
    simp

/-- **An invertible module on an algebraic space is locally trivial on the small étale site**:
it is finite locally free of rank one (Stacks 0B8Q). -/
theorem isLocallyTrivialOnSite_of_isInvertible (Z : AlgebraicSpaces B S hS)
    (N : Modules.{u, u} B S hS Z.1 Z.2)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Z)
      (structureRingSheaf B S hS Z).property N) :
    Stacks.SheafOfModules.TensorLocalProperties.IsLocallyTrivialOnSite
      (structureSheaf B S hS Z.1 Z.2) N := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS Z N hN U
  exact ⟨I, V, f, hf, fun i ↦ ⟨(isoOfIsColimitCofanFinOne _ (hV i).choose_spec.some).symm⟩⟩

namespace QuotSituation

variable (D : QuotSituation B S hS) (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

/-- The module `F ⊗ L` of the twisted situation. -/
abbrev tensorInvertibleModule : Modules.{u, u} B S hS D.X.1 D.X.2 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS D.X).O).obj D.F).obj L

include hL in
/-- The twisted module `F ⊗ L` is quasi-coherent, `L` being locally trivial. -/
theorem isQuasicoherentOnSite_tensorInvertibleModule :
    (D.tensorInvertibleModule L).IsQuasicoherentOnSite :=
  open Stacks.SheafOfModules.TensorLocalProperties in
  (isQuasicoherentOnSite_tensor_iff_of_isLocallyTrivialOnSite
    (structureSheaf B S hS D.X.1 D.X.2) D.F L
    (isLocallyTrivialOnSite_of_isInvertible D.X L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL))).2 D.quasicoherent

/-- **The situation `F ⊗ L / X / B`** of Stacks 0DP7: the same morphism of finite presentation,
with the quasi-coherent module `F` replaced by `F ⊗ L`. -/
def tensorInvertible : QuotSituation B S hS where
  X := D.X
  Y := D.Y
  f := D.f
  F := D.tensorInvertibleModule L
  quasicoherent := D.isQuasicoherentOnSite_tensorInvertibleModule L
  finitePresentation := D.finitePresentation

/-- The pullback `L_T` of `L` to `X_T`. -/
abbrev baseChangeInvertible (T : SchemesOver D.Y) :
    Modules.{u, u} B S hS (D.space T).1 (D.space T).2 :=
  (modulePullback B S hS (D.sourceProjection T)).obj L

/-- Tensoring by `L_T` on the modules of `X_T`. -/
abbrev tensorBaseChange (T : SchemesOver D.Y) :=
  Stacks.SheafOfModules.tensorRightFunctorOf (X := smallEtaleRingedTopos B S hS (D.space T))
    (D.baseChangeInvertible L T)

/-- The comparison `f_T^*(- ⊗ L) ≅ f_T^*(-) ⊗ L_T` of Stacks 03EL. -/
abbrev tensorComparison (T : SchemesOver D.Y) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackTensorRightIso
    (smallEtaleRingedToposModulesHom B S hS (D.sourceProjection T)) L

include hL in
/-- The pullback `L_T` is invertible. -/
theorem isInvertible_baseChangeInvertible (T : SchemesOver D.Y) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (D.space T).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).O)).property
      (D.baseChangeInvertible L T) :=
  isInvertible_modulePullback B S hS (D.sourceProjection T) L

include hL in
/-- Tensoring by `L_T` is an autoequivalence of the `𝒪_{X_T}`-modules. -/
theorem isEquivalence_tensorBaseChange (T : SchemesOver D.Y) :
    (D.tensorBaseChange L T).IsEquivalence :=
  @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible.{u, u + 1, u}
    (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).C _
    (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).J
    (structurePresheaf B S hS (D.space T).1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).O)).property
    (inferInstanceAs ((SmallEtale.topology B S hS (D.space T).1).WEqualsLocallyBijective
      AddCommGrpCat.{u}))
    (inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS (D.space T).1) AddCommGrpCat.{u}))
    (D.baseChangeInvertible L T) (D.isInvertible_baseChangeInvertible L T)

include hL in
/-- Tensoring by `L_T` preserves epimorphisms. -/
theorem preservesEpimorphisms_tensorBaseChange (T : SchemesOver D.Y) :
    (D.tensorBaseChange L T).PreservesEpimorphisms :=
  @Functor.preservesEpimorphisms_of_isLeftAdjoint _ _ _ _ _
    (@Functor.isLeftAdjoint_of_isEquivalence _ _ _ _ _ (D.isEquivalence_tensorBaseChange L T))

/-- **The twisted quotient.**  A quotient `F_T ⟶ Q`, recorded by its kernel `K`, goes to the
quotient `(F ⊗ L)_T ≅ F_T ⊗ L_T ⟶ Q ⊗ L_T`, recorded by its kernel. -/
def tensorQuotient (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Subobject ((D.tensorInvertible L).baseChangeModule T) :=
  Functor.conjSubobject (D.tensorComparison L T) (M := D.F) K

/-- The base change comparison of `F` along `h : T' ⟶ T` is the composition isomorphism of
pullbacks of modules along `X_{T'} ⟶ X_T ⟶ X`, up to the equality of the composite maps. -/
theorem baseChangeComparison_eq_pullbackModulesCompIso {T' T : SchemesOver D.Y} (h : T' ⟶ T) :
    D.baseChangeComparison h =
      eqToIso (congrArg (fun k ↦ (smallEtaleRingedToposModulesHom B S hS k).pullbackModules)
          (baseChangeMap_comp_projection D.f h).symm) ≪≫
        Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso
          (smallEtaleRingedToposModulesHom B S hS (D.relativeMap h))
          (smallEtaleRingedToposModulesHom B S hS (D.sourceProjection T))
          (smallEtaleRingedToposModulesHom B S hS (D.relativeMap h ≫ D.sourceProjection T))
          (smallEtaleCompPushforwardIso B S hS (D.relativeMap h) (D.sourceProjection T))
          (fSharpSetComp_smallEtaleCompPushforwardIso B S hS (D.relativeMap h)
            (D.sourceProjection T)) := by
  change modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f h) = _
  rw [modulePullbackTriangle_eq, modulePullbackCompIso_eq_pullbackModulesCompIso]
  rfl

include hL in
/-- **The twisted quotient commutes with pullback of quotients.** -/
theorem tensorQuotient_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    (D.tensorInvertible L).quotientPullback h (D.tensorQuotient L T K) =
      D.tensorQuotient L T' (D.quotientPullback h K) := by
  have key :=
    Stacks.Sheaves.RingedToposModules.conjSubobject_pullbackTensorRightIso_pullbackModulesCompIso
    (smallEtaleRingedToposModulesHom B S hS (D.sourceProjection T))
    (smallEtaleRingedToposModulesHom B S hS (D.relativeMap h))
    (smallEtaleRingedToposModulesHom B S hS (D.sourceProjection T'))
    (smallEtaleRingedToposModulesHom B S hS (D.relativeMap h ≫ D.sourceProjection T))
    (congrArg (smallEtaleRingedToposModulesHom B S hS) (baseChangeMap_comp_projection D.f h).symm)
    (smallEtaleCompPushforwardIso B S hS (D.relativeMap h) (D.sourceProjection T))
    (fSharpSetComp_smallEtaleCompPushforwardIso B S hS (D.relativeMap h) (D.sourceProjection T))
    D.F L K (D.preservesEpimorphisms_tensorBaseChange L T)
    (modulePullback_preservesEpimorphisms (D.relativeMap h))
  change Functor.conjSubobject (D.baseChangeComparison h) (D.tensorQuotient L T K) =
    Functor.conjSubobject (D.tensorComparison L T')
      (Functor.conjSubobject (D.baseChangeComparison h) K)
  rw [baseChangeComparison_eq_pullbackModulesCompIso]
  exact key

include hL in
/-- `L_T` is invertible in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem isInvertible_baseChangeInvertible' (T : SchemesOver D.Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS (D.space T))
      (structureRingSheaf B S hS (D.space T)).property (D.baseChangeInvertible L T) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (D.isInvertible_baseChangeInvertible L T)

include hL in
/-- **The conditions of Stacks 09TR are preserved and reflected by twisting.**  For a module `Q`
on `X_T` and a module `Q'` isomorphic to `Q ⊗ L_T`: `Q'` is quasi-coherent, flat over `T`, of
finite presentation and with support proper over `T` exactly when `Q` is. -/
theorem conditions_tensorBaseChange_iff (T : SchemesOver D.Y)
    (Q Q' : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (e : Q' ≅ (D.tensorBaseChange L T).obj Q) :
    ((Q'.IsQuasicoherentOnSite ∧ IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q') ∧
        Q'.IsFinitePresentationOnSite) ∧ D.IsProperlySupportedOver T Q' ↔
      ((Q.IsQuasicoherentOnSite ∧ IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q) ∧
        Q.IsFinitePresentationOnSite) ∧ D.IsProperlySupportedOver T Q := by
  have hN := isLocallyTrivialOnSite_of_isInvertible (D.space T) (D.baseChangeInvertible L T)
    (D.isInvertible_baseChangeInvertible' L T)
  open Stacks.SheafOfModules.TensorLocalProperties in
  have hqcT := isQuasicoherentOnSite_tensor_iff_of_isLocallyTrivialOnSite
    (structureSheaf B S hS (D.space T).1 (D.space T).2) Q _ hN
  open Stacks.SheafOfModules.TensorLocalProperties in
  have hfpT := isFinitePresentationOnSite_tensor_iff_of_isLocallyTrivialOnSite
    (structureSheaf B S hS (D.space T).1 (D.space T).2) Q _ hN
  have hqc : Q'.IsQuasicoherentOnSite ↔ Q.IsQuasicoherentOnSite :=
    ⟨fun h ↦ hqcT.1 (SheafOfModules.IsQuasicoherentOnSite.of_iso e h),
      fun h ↦ SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm (hqcT.2 h)⟩
  have hfp : Q'.IsFinitePresentationOnSite ↔ Q.IsFinitePresentationOnSite :=
    ⟨fun h ↦ hfpT.1 (SheafOfModules.IsFinitePresentationOnSite.of_iso e h),
      fun h ↦ SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm (hfpT.2 h)⟩
  have hsupp := supportOfSheaf_tensor_invertible B S hS (D.space T) Q (D.baseChangeInvertible L T)
    (D.isInvertible_baseChangeInvertible L T)
  have hsupp' : D.IsProperlySupportedOver T Q' ↔ D.IsProperlySupportedOver T Q :=
    ⟨fun h ↦ hasProperSupport_congr_support (D.space T).2 _ _ _ hsupp
        (D.isProperlySupportedOver_of_iso e h),
      fun h ↦ D.isProperlySupportedOver_of_iso e.symm
        (hasProperSupport_congr_support (D.space T).2 _ _ _ hsupp.symm h)⟩
  have hflat (h : Q.IsQuasicoherentOnSite) :
      IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q' ↔
        IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q :=
    (isFlatOver_iff_of_iso B S hS (D.space T).2 (D.projection T).hom e).trans
      (isFlatOver_tensor_invertible_iff B S hS (D.space T) (D.projection T) Q
        (D.baseChangeInvertible L T) (D.isInvertible_baseChangeInvertible L T) h (hqcT.2 h))
  constructor
  · rintro ⟨⟨⟨hq, hf⟩, hp⟩, hs⟩
    have hq' := hqc.1 hq
    exact ⟨⟨⟨hq', (hflat hq').1 hf⟩, hfp.1 hp⟩, hsupp'.1 hs⟩
  · rintro ⟨⟨⟨hq, hf⟩, hp⟩, hs⟩
    exact ⟨⟨⟨hqc.2 hq, (hflat hq).2 hf⟩, hfp.2 hp⟩, hsupp'.2 hs⟩

include hL in
/-- **The twisted quotient lies in `Quot_{F ⊗ L/X/B}(T)` exactly when the quotient lies in
`Quot_{F/X/B}(T)`.** -/
theorem tensorQuotient_mem_iff (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    D.tensorQuotient L T K ∈ (D.tensorInvertible L).properlySupportedQuotients T ↔
      K ∈ D.properlySupportedQuotients T :=
  have := D.preservesEpimorphisms_tensorBaseChange L T
  D.conditions_tensorBaseChange_iff L T (D.quotientModule T K)
    ((D.tensorInvertible L).quotientModule T (D.tensorQuotient L T K))
    (Functor.conjSubobjectCokernelIso (D.tensorComparison L T) K)

include hL in
/-- **Twisting is a bijection on quotients.**  Tensoring by `L_T` is an autoequivalence, so
conjugating by the comparison of Stacks 03EL is injective, and every quotient of `(F ⊗ L)_T` is the
twist of a quotient of `F_T`. -/
theorem tensorQuotient_bijective (T : SchemesOver D.Y) :
    Function.Bijective (D.tensorQuotient L T) := by
  have := D.isEquivalence_tensorBaseChange L T
  have := D.preservesEpimorphisms_tensorBaseChange L T
  have hff := Functor.FullyFaithful.ofFullyFaithful (D.tensorBaseChange L T)
  refine ⟨Functor.conjSubobject_injective (D.tensorComparison L T) hff D.F, fun K' ↦ ?_⟩
  obtain ⟨K, hK, -⟩ := Functor.exists_conjSubobject_eq (D.tensorComparison L T) hff (M := D.F) K'
    (@Functor.EssSurj.mem_essImage _ _ _ _ _
      (@Functor.IsEquivalence.essSurj _ _ _ _ _ (D.isEquivalence_tensorBaseChange L T)) _)
  exact ⟨K, hK⟩

/-- The twisting operation on the values of the Quot functor:
`Quot_{F/X/B}(T) ⟶ Quot_{F ⊗ L/X/B}(T)`. -/
def tensorQuotFunctorObj (T : SchemesOver D.Y) (K : D.properlySupportedQuotients T) :
    (D.tensorInvertible L).properlySupportedQuotients T :=
  ⟨D.tensorQuotient L T K.1, (D.tensorQuotient_mem_iff L T K.1).2 K.2⟩

include hL in
/-- Twisting is a bijection `Quot_{F/X/B}(T) ⟶ Quot_{F ⊗ L/X/B}(T)`. -/
theorem tensorQuotFunctorObj_bijective (T : SchemesOver D.Y) :
    Function.Bijective (D.tensorQuotFunctorObj L T) := by
  refine ⟨fun K₁ K₂ h ↦
    Subtype.ext ((D.tensorQuotient_bijective L T).1 (congrArg Subtype.val h)), fun K' ↦ ?_⟩
  obtain ⟨K, hK⟩ := (D.tensorQuotient_bijective L T).2 K'.1
  exact ⟨⟨K, (D.tensorQuotient_mem_iff L T K).1 (hK ▸ K'.2)⟩, Subtype.ext hK⟩

/-- **Stacks 0DP7, the isomorphism.**  Tensoring with an invertible module `L` is an isomorphism
of Quot functors `Quot_{F/X/B} ≅ Quot_{F ⊗ L/X/B}`: a quotient `F_T ⟶ Q` goes to
`(F ⊗ L)_T = F_T ⊗ L_T ⟶ Q ⊗ L_T`. -/
def quotFunctorTensorInvertibleIso : D.quotFunctor ≅ (D.tensorInvertible L).quotFunctor :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso (Equiv.ofBijective _ (D.tensorQuotFunctorObj_bijective L T.unop)))
    (fun {T T'} g ↦ by
      apply ConcreteCategory.hom_ext
      intro x
      exact Subtype.ext (D.tensorQuotient_quotientPullback L g.unop x.1).symm)

/-- The twisting isomorphism of Quot functors sends a quotient to its twisted quotient. -/
@[simp]
theorem quotFunctorTensorInvertibleIso_hom_app_coe (T : SchemesOver D.Y)
    (K : D.quotFunctor.obj (Opposite.op T)) :
    ((D.quotFunctorTensorInvertibleIso L).hom.app (Opposite.op T) K).1 = D.tensorQuotient L T K.1 :=
  rfl

/-- The twisting operation on quotients over a scheme of the site. -/
def tensorQuotFamily {T : BigFppfOver B S hS} (x : QuotFamilyOver D T) :
    QuotFamilyOver (D.tensorInvertible L) T where
  toBase := x.toBase
  subobject := D.tensorQuotient L _ x.subobject
  mem := (D.tensorQuotient_mem_iff L _ x.subobject).2 x.mem

include hL in
/-- Twisting is a bijection on quotients over a scheme of the site. -/
theorem tensorQuotFamily_bijective (T : BigFppfOver B S hS) :
    Function.Bijective (D.tensorQuotFamily L (T := T)) := by
  refine ⟨fun x y h ↦ ?_, fun x' ↦ ?_⟩
  · obtain ⟨xb, xK, xm⟩ := x
    obtain ⟨yb, yK, ym⟩ := y
    dsimp only [tensorQuotFamily] at h
    obtain ⟨rfl, hs⟩ := QuotFamilyOver.mk.inj h
    obtain rfl := (D.tensorQuotient_bijective L _).1 (eq_of_heq hs)
    rfl
  · obtain ⟨K, hK⟩ := (D.tensorQuotient_bijective L _).2 x'.subobject
    refine ⟨⟨x'.toBase, K, (D.tensorQuotient_mem_iff L _ K).1 (hK ▸ x'.mem)⟩, ?_⟩
    exact QuotFamilyOver.ext rfl (heq_of_eq hK)

include hL in
/-- Twisting commutes with base change of quotients along `g : T' ⟶ T`. -/
theorem tensorQuotFamily_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D T) :
    D.tensorQuotFamily L (x.baseChange g) = (D.tensorQuotFamily L x).baseChange g :=
  QuotFamilyOver.ext rfl
    (heq_of_eq (D.tensorQuotient_quotientPullback L _ x.subobject).symm)

/-- The twisting bijection on quotients over a scheme of the site. -/
def tensorQuotFamilyEquiv (T : BigFppfOver B S hS) :
    QuotFamilyOver D T ≃ QuotFamilyOver (D.tensorInvertible L) T :=
  Equiv.ofBijective (D.tensorQuotFamily L) (D.tensorQuotFamily_bijective L T)

include hL in
/-- Twisting commutes with the restriction maps of the Quot presheaves. -/
theorem tensorQuotFamily_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : QuotFamilyOver D T) :
    (D.tensorInvertible L).quotSitePresheaf.map g.op (D.tensorQuotFamily L x) =
      D.tensorQuotFamily L (D.quotSitePresheaf.map g.op x) :=
  (D.tensorQuotFamily_baseChange L g x).symm

/-- The component of the twisting isomorphism of Quot presheaves at a scheme of the site. -/
def quotSitePresheafTensorInvertibleIsoApp (T : (BigFppfOver B S hS)ᵒᵖ) :
    D.quotSitePresheaf.obj T ≅ (D.tensorInvertible L).quotSitePresheaf.obj T :=
  Equiv.toIso (D.tensorQuotFamilyEquiv L T.unop)

include hL in
/-- The components `quotSitePresheafTensorInvertibleIsoApp` are natural in the scheme of the
site. -/
theorem quotSitePresheafTensorInvertibleIsoApp_naturality {T T' : (BigFppfOver B S hS)ᵒᵖ}
    (g : T ⟶ T') :
    D.quotSitePresheaf.map g ≫ (D.quotSitePresheafTensorInvertibleIsoApp L T').hom =
      (D.quotSitePresheafTensorInvertibleIsoApp L T).hom ≫
        (D.tensorInvertible L).quotSitePresheaf.map g :=
  ConcreteCategory.hom_ext _ _ fun x ↦ (D.tensorQuotFamily_map L g.unop x).symm

/-- **Stacks 0DP7, the isomorphism, on the Quot presheaf of the site.**  Tensoring with an
invertible module `L` is an isomorphism of presheaves `Quot_{F/X/B} ≅ Quot_{F ⊗ L/X/B}` on the
schemes of the big fppf site. -/
def quotSitePresheafTensorInvertibleIso :
    D.quotSitePresheaf ≅ (D.tensorInvertible L).quotSitePresheaf :=
  NatIso.ofComponents (D.quotSitePresheafTensorInvertibleIsoApp L)
    (D.quotSitePresheafTensorInvertibleIsoApp_naturality L)

include hL in
/-- The quotient of `(F ⊗ L)_T` by the twisted quotient is the quotient of `F_T` tensored with
`L_T`. -/
def tensorQuotientModuleIso (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    (D.tensorInvertible L).quotientModule T (D.tensorQuotient L T K) ≅
      moduleTensor B S hS (D.space T) (D.quotientModule T K) (D.baseChangeInvertible L T) :=
  haveI := D.preservesEpimorphisms_tensorBaseChange L T
  Functor.conjSubobjectCokernelIso (D.tensorComparison L T) K

/-- The object of `Coh_{X/B}` attached to the twisted quotient, read as an object over the
situation of `F`: the two situations have the same morphism `X ⟶ B`. -/
def tensorCohObject {T : SchemesOver D.Y}
    (K : Subobject ((D.tensorInvertible L).baseChangeModule T))
    (hK : K ∈ (D.tensorInvertible L).properlySupportedQuotients T) :
    CoherentObject D.toCoherentSituation where
  T := T
  F := (D.tensorInvertible L).quotientModule T K
  quasicoherent := hK.1.1.1
  finitePresentation := hK.1.2
  flat := hK.1.1.2
  properSupport := ⟨D.isLocallyOfFiniteType_projection T, hK.2.1, hK.2.2⟩

/-- The object of `Coh_{X/B}` attached to a quotient of `(F ⊗ L)_T`, read over the situation of
`F`, is `tensorCohObject`. -/
theorem cohObject_tensorInvertible {T : SchemesOver D.Y}
    (K : Subobject ((D.tensorInvertible L).baseChangeModule T))
    (hK : K ∈ (D.tensorInvertible L).properlySupportedQuotients T) :
    ((D.tensorInvertible L).cohObject T K hK : CoherentObject D.toCoherentSituation) =
      D.tensorCohObject L K hK :=
  rfl

include hL in
/-- **The twist identity on the quotient of a twisted quotient.**  The twisted Euler
characteristics of the quotient `Q ⊗ L_T` of `(F ⊗ L)_T` are those of the quotient `Q` of `F_T`,
shifted by one. -/
theorem twistedEuler_tensorQuotient {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T))
    (hK : K ∈ D.properlySupportedQuotients T)
    (t : (D.cohObject T K hK).testScheme) (n : ℤ) :
    letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS D.toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
    CoherentObject.twistedEuler L
        (D.tensorCohObject L (D.tensorQuotient L T K) ((D.tensorQuotient_mem_iff L T K).2 hK)) t n =
      CoherentObject.twistedEuler L (D.cohObject T K hK) t (n + 1) :=
  let : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  CoherentObject.twistedEuler_mk_tensor (D := D.toCoherentSituation) L T
    (D.quotientModule T K) ((D.tensorInvertible L).quotientModule T (D.tensorQuotient L T K))
    _ _ _ _ _ _ _ _ (D.tensorQuotientModuleIso L T K) t n

include hL in
/-- **Stacks 0DP7, the restriction to the numerical substacks, on objects of `Coh_{X/B}`.**  The
object `(T, Q ⊗ L_T)` attached to a twisted quotient has Hilbert polynomial
`P'(n) = P(n + 1)` with respect to `L` exactly when the object `(T, Q)` attached to the quotient
has Hilbert polynomial `P`. -/
theorem hasHilbertPolynomial_tensorCohObject_iff (P : ℤ → ℤ) {T : SchemesOver D.Y}
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.properlySupportedQuotients T) :
    letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS D.toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
    CoherentObject.HasHilbertPolynomial L (fun n ↦ P (n + 1))
        (D.tensorCohObject L (D.tensorQuotient L T K) ((D.tensorQuotient_mem_iff L T K).2 hK)) ↔
      CoherentObject.HasHilbertPolynomial L P (D.cohObject T K hK) :=
  (isPrescribedTwistedEuler_iff_shift (D.twistedEuler_tensorQuotient L K hK)).symm

include hL in
/-- **Stacks 0DP7, the restriction to `Quot^P`.**  For every scheme `T` of the site and every
quotient `x ∈ Quot_{F/X/B}(T)`, the image of `x` under the isomorphism
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafTensorInvertibleIso` lies in
`Quot^{P'}_{F ⊗ L/X/B}(T)` with `P'(n) = P(n + 1)` exactly when `x` lies in `Quot^P_{F/X/B}(T)`:
the object of `Coh_{X/B}` it gives has Hilbert polynomial `P'` with respect to `L` exactly when
that of `x` has Hilbert polynomial `P`.  So the isomorphism carries `Quot^P_{F/X/B}` onto
`Quot^{P'}_{F ⊗ L/X/B}`. -/
theorem hasHilbertPolynomial_quotSitePresheafTensorInvertibleIso_iff (P : ℤ → ℤ)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : D.quotSitePresheaf.obj T) :
    letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS (D.tensorInvertible L).toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (D.tensorInvertible L).toCoherentSituation.X.1
          (D.tensorInvertible L).toCoherentSituation.X.2).O)).property L := hL
    letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS D.toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
    ((D.quotSitePresheafTensorInvertibleIso L).hom.app T x).cohObject.HasHilbertPolynomial L
        (fun n ↦ P (n + 1)) ↔
      x.cohObject.HasHilbertPolynomial L P :=
  D.hasHilbertPolynomial_tensorCohObject_iff L P x.subobject x.mem

/-- The twisting isomorphism of Quot presheaves acts on a quotient by `tensorQuotFamily`. -/
@[simp]
theorem quotSitePresheafTensorInvertibleIso_hom_app {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : D.quotSitePresheaf.obj T) :
    (D.quotSitePresheafTensorInvertibleIso L).hom.app T x = D.tensorQuotFamily L x :=
  rfl

/-- The isomorphism lies over the base: it does not change the morphism to `B` a quotient lies
over. -/
theorem quotSitePresheafTensorInvertibleIso_hom_comp_quotSitePresheafToBase :
    (D.quotSitePresheafTensorInvertibleIso L).hom ≫
        (D.tensorInvertible L).quotSitePresheafToBase = D.quotSitePresheafToBase := by
  refine NatTrans.ext (funext fun T ↦ ?_)
  apply ConcreteCategory.hom_ext
  intro x
  rfl

include hL in
/-- **Stacks 0DP7.**  Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation,
`F` a quasi-coherent `𝒪_X`-module and `L` an invertible `𝒪_X`-module.  Tensoring with `L` is an
isomorphism of Quot functors
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafTensorInvertibleIso :
Quot_{F/X/B} ≅ Quot_{F ⊗ L/X/B}`; precisely:

* it lies over `B`;
* it sends a quotient `F_T ⟶ Q` over `T` to a quotient of `(F ⊗ L)_T` with quotient module
  `Q ⊗ L_T`;
* for every `P : ℤ → ℤ` it carries `Quot^P_{F/X/B}` onto `Quot^{P'}_{F ⊗ L/X/B}`, where
  `P'(n) = P(n + 1)`: a quotient lies in `Quot^P_{F/X/B}` exactly when its image lies in
  `Quot^{P'}_{F ⊗ L/X/B}`, membership being that the object of `Coh_{X/B}` the quotient gives has
  Hilbert polynomial `P`, respectively `P'`, with respect to `L` (Stacks 0DNF). -/
@[stacks 0DP7 "the isomorphism `Quot_{F/X/B} ≅ Quot_{F ⊗ L/X/B}` given by tensoring with `L`, and
its restriction to `Quot^P ≅ Quot^{P'}` for `P'(t) = P(t + 1)`, membership read on the actual
twisted Euler characteristics `χ(X_t, Q_t ⊗ L_t^{⊗ n})`"]
theorem quotSitePresheafTensorInvertibleIso_spec :
    (D.quotSitePresheafTensorInvertibleIso L).hom ≫
        (D.tensorInvertible L).quotSitePresheafToBase = D.quotSitePresheafToBase ∧
      (∀ {T : (BigFppfOver B S hS)ᵒᵖ} (x : D.quotSitePresheaf.obj T),
        Nonempty ((D.tensorInvertible L).quotientModule _
            ((D.quotSitePresheafTensorInvertibleIso L).hom.app T x).subobject ≅
          moduleTensor B S hS (D.space _) (D.quotientModule _ x.subobject)
            (D.baseChangeInvertible L _))) ∧
      ∀ (P : ℤ → ℤ) {T : (BigFppfOver B S hS)ᵒᵖ} (x : D.quotSitePresheaf.obj T),
        letI : Stacks.SheafOfModules.IsInvertible
            (structurePresheaf B S hS (D.tensorInvertible L).toCoherentSituation.X.1)
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
              (D.tensorInvertible L).toCoherentSituation.X.1
              (D.tensorInvertible L).toCoherentSituation.X.2).O)).property L := hL
        letI : Stacks.SheafOfModules.IsInvertible
            (structurePresheaf B S hS D.toCoherentSituation.X.1)
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
              D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
        (((D.quotSitePresheafTensorInvertibleIso L).hom.app T x).cohObject.HasHilbertPolynomial L
            (fun n ↦ P (n + 1)) ↔
          x.cohObject.HasHilbertPolynomial L P) :=
  ⟨D.quotSitePresheafTensorInvertibleIso_hom_comp_quotSitePresheafToBase L,
    fun x ↦ ⟨D.tensorQuotientModuleIso L _ x.subobject⟩,
    fun P _ x ↦ D.hasHilbertPolynomial_quotSitePresheafTensorInvertibleIso_iff L P x⟩

end QuotSituation

end AlgebraicGeometry.Space

end
