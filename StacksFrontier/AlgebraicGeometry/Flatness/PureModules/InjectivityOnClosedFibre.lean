module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFibre
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Specialization
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity of a map out of a pure flat module is tested on the closed fibre

Let `f : X ⟶ S` be of finite type, let `ℱ` be a quasi-coherent `𝒪_X`-module of finite type
which is flat over `S` and pure along the fibre `X_s`, and let `φ : ℱ ⟶ 𝒢` be a map of
quasi-coherent `𝒪_X`-modules. Over a local base with closed point `s` the injectivity of `φ` is
detected by the finitely many points of `X_s` associated to the restriction `ℱ_s`: the stalk
maps `φ_x` are injective at those points if and only if `φ` is injective.

## Main results

* `AlgebraicGeometry.forall_injective_stalkLinearMap_associatedPoints_iff_mono`: **Stacks tag
  05L8**, the equivalence, both directions.

## Implementation notes

"`S` is local with closed point `s`" enters only through the specializations it provides, so it
is taken as the hypothesis that every point of `S` specializes to `s`; for `S` the spectrum of a
local ring and `s` its closed point that is the usual fact that every prime is contained in the
maximal ideal. The statement is therefore slightly more general than the source's.

"`φ` is injective" is a monomorphism of `𝒪_X`-modules, and "`φ_x` is injective" is injectivity of
`AlgebraicGeometry.stalkLinearMap`, the induced map on the stalk at `x` as a map of modules over
the local ring.

The source's proof is followed step for step. The kernel `𝒦` of `φ` is quasi-coherent, so it
vanishes exactly when it has no weakly associated point (tag 05AP), and `φ` is a monomorphism as
soon as its kernel vanishes. A weakly associated point `x'` of `𝒦` is weakly associated to `ℱ`
(tag 05AN, in the form `Module.weaklyAssociatedPrimes_subset_of_injective` applied to the
injective stalk map of the monomorphism `𝒦 ⟶ ℱ`), hence lies in `Ass_{X/S}(ℱ)` because `ℱ` is
flat over `S` — this is tag 05IJ for `𝒢 = 𝒪_S`, proved here as
`mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_flat` by instantiating the algebraic fibre
clause of tag 05IG at the module `R` itself, so that the tensor product `N ⊗_R R` of the general
statement is the stalk of `ℱ` again. Purity along `X_s` then forces `x'` to specialize into
`X_s`: were it not so, the identity base change would be an impurity. Tag 05L3 improves that to a
specialization to a point `x` of `X_s` associated to `ℱ_s`, which is where flatness is used a
second time. By hypothesis `φ_x` is injective, so `x` misses the support of `𝒦`; but the support
of a quasi-coherent module is stable under specialization and `x'` lies in it, a contradiction.

The private `notMem_supp_kernel_of_injective_stalk` repeats
`AlgebraicGeometry.Scheme.Modules.notMem_supp_kernel_of_injective_stalkLinearMap`, which is public
but sits in `StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism`, a module about the
degree of a curve rather than about purity.

## References

* [Stacks Project, Tag 05L8](https://stacks.math.columbia.edu/tag/05L8)
* [Stacks Project, Tag 05L3](https://stacks.math.columbia.edu/tag/05L3)
* [Stacks Project, Tag 05IJ](https://stacks.math.columbia.edu/tag/05IJ)
* [Stacks Project, Tag 05AN](https://stacks.math.columbia.edu/tag/05AN)
* [Stacks Project, Tag 05AP](https://stacks.math.columbia.edu/tag/05AP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.WeaklyAssociatedPrimes TensorProduct
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05IJ for `𝒢 = 𝒪_S`.** A weakly associated point of a finite type
quasi-coherent module which is flat over the base at that point lies in the relative assassin:
`WeakAss_X(ℱ) ⊆ Ass_{X/S}(ℱ)`.

This is the fibre clause of tag 05IH read at `𝒢 = 𝒪_S`, and it is obtained here the same way,
by instantiating the algebraic fibre clause of tag 05IG — which assumes nothing beyond the
tag's own hypotheses — at the module `R` itself, the tensor product `N ⊗_R R` being the stalk
of `ℱ` again. -/
theorem mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hx : Stacks.Divisors.IsWeaklyAssociatedPoint F x) :
    x ∈ Stacks.Divisors.relativeAssassin f F := by
  classical
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let ψ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := ψ.toAlgebra
  let : IsLocalHom ψ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let : Module R N := Module.compHom N ψ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have : Module.Finite B N := SheafOfModules.finite_stalk X.sheaf F x
  have : Algebra.EssFiniteType R B := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have hess : IsEssentiallyOfFiniteType R B (algebraMap R B) := by
    obtain ⟨T, T', hT, hLoc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R B).mp inferInstance
    exact ⟨T, inferInstance, (algebraMap R T).toAlgebra, hT, T',
      (algebraMap T B).toAlgebra, ⟨IsScalarTower.of_algebraMap_eq' rfl, hLoc⟩⟩
  have : IsNoetherianRing (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) := by
    have : IsLocallyNoetherian (f.fiber (f x)) := by
      have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
        show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
        infer_instance
      exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
    rw [RingHom.algebraMap_toAlgebra]
    exact isNoetherianRing_of_ringEquiv _ (quotientStalkEquivFiberStalk f x).symm
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] R) (IsLocalRing.maximalIdeal B) :=
    (LinearEquiv.isWeaklyAssociatedPrime_iff
      (TensorProduct.AlgebraTensorModule.rid R B N) _).mpr hx
  have key :=
    isAssociatedPrimeStacks_closedFibre_of_isWeaklyAssociatedPrime_tensorProduct_of_finite
      (R := R) (B := B) (N := N) (M := R) hess hT
  rw [RingHom.algebraMap_toAlgebra] at key
  rwa [Stacks.Divisors.mem_relativeAssassin_iff_isAssociatedPoint_asFiber,
    Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff]

/-- A point where the stalk map of a morphism of modules is injective misses the support of its
kernel: the stalk functor preserves monomorphisms, so the stalk of the inclusion of the kernel is
a monomorphism onto zero. -/
private theorem notMem_supp_kernel_of_injective_stalk {X : Scheme.{u}}
    {A B : X.Modules} (φ : A ⟶ B) (x : X)
    (h : Function.Injective (stalkLinearMap A B φ x)) :
    x ∉ SheafOfModules.supp (kernel φ) :=
  have hmono : Mono ((Scheme.Modules.stalkFunctor X x).map φ) :=
    (ModuleCat.mono_iff_injective _).2 h
  have hmono2 : Mono ((Scheme.Modules.stalkFunctor X x).map (kernel.ι φ)) :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.mono_stalkFunctor_map _ x
  (Scheme.Modules.notMem_supp_iff_isZero_stalk _ x).2
    (@IsZero.of_mono_eq_zero _ _ _ _ _ _ hmono2
      (Scheme.Modules.stalkFunctor_map_kernel_ι_eq_zero φ x hmono))

/-- **Stacks Project, Tag 05L8.** Let `f : X ⟶ S` be a morphism of finite type, let `ℱ` be a
quasi-coherent `𝒪_X`-module of finite type, and let `s` be a point of `S` to which every point
of `S` specializes — for instance the closed point of a local base. Assume `ℱ` is pure along the
fibre `X_s` and flat over `S`. Then a map `φ : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules is
injective if and only if the stalk map `φ_x` is injective at every point `x` of `X_s` associated
to the restriction `ℱ_s`.

One direction is immediate: the stalk maps of a monomorphism are injective at every point. For
the other, the kernel of `φ` has no weakly associated point — such a point would lie in
`Ass_{X/S}(ℱ)` by flatness, would specialize into `X_s` by purity, and the hypothesis at the
associated point of `ℱ_s` it specializes to by Tag 05L3 would put that point outside the support
of the kernel, which is stable under specialization. -/
@[stacks 05L8 "the equivalence, both directions; `S` local with closed point `s` is rendered by \
the hypothesis that every point of `S` specializes to `s`, which is what a local base supplies"]
theorem forall_injective_stalkLinearMap_associatedPoints_iff_mono
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F G : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (s : S) (hclosed : ∀ t : S, t ⤳ s)
    (hpure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (φ : F ⟶ G) :
    (∀ x : f.fiber s,
        x ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) →
          Function.Injective (stalkLinearMap F G φ (f.fiberι s x))) ↔ Mono φ := by
  refine ⟨fun hstalk => ?_, fun hmono x _ =>
    Scheme.Modules.injective_stalkLinearMap_of_mono φ hmono (f.fiberι s x)⟩
  refine Preadditive.mono_of_isZero_kernel φ ?_
  rw [isZero_iff_weaklyAssociatedPoints_eq_empty]
  refine Set.eq_empty_of_forall_notMem fun x' hx' => ?_
  -- Tag 05AN: a weakly associated point of the kernel is weakly associated to `ℱ`.
  have hxF : Stacks.Divisors.IsWeaklyAssociatedPoint F x' :=
    Module.weaklyAssociatedPrimes_subset_of_injective
      (f := stalkLinearMap (kernel φ) F (kernel.ι φ) x')
      (Scheme.Modules.injective_stalkLinearMap_of_mono (kernel.ι φ) inferInstance x') hx'
  -- Tag 05IJ at `𝒢 = 𝒪_S`, where flatness of `ℱ` over `S` is used.
  have hass : x' ∈ Stacks.Divisors.relativeAssassin f F :=
    mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_flat f F x' (hflat x') hxF
  -- Purity along `X_s` makes `x'` specialize into the closed fibre.
  obtain ⟨y, hy⟩ := exists_specializes_fiberι_of_isPureAlong
    ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) hpure hass
    (hclosed (f x'))
  -- Tag 05L3: it specializes to a point of `X_s` associated to `ℱ_s`.
  obtain ⟨x, hxspec, hxass⟩ :=
    Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre f F s
      (fun t => hflat (f.fiberι s t)) hass ⟨y, hy⟩
  -- The hypothesis at `x` keeps the kernel off `x`, while `x'` carries it there.
  exact notMem_supp_kernel_of_injective_stalk φ (f.fiberι s x) (hstalk x hxass)
    (Scheme.Modules.stableUnderSpecialization_supp X (kernel φ) hxspec
      (weaklyAssociatedPoints_subset_supp (kernel φ) hx'))

end AlgebraicGeometry

end
