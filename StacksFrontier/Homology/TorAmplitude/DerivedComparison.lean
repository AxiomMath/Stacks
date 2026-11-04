module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.Defs
public import StacksFrontier.Homology.TorAmplitude.Termwise

/-!
# Derived versus termwise Tor amplitude

Let `R` be a commutative ring, `K` a cochain complex of `R`-modules and `M` an `R`-module.
Ordinary termwise tensoring `K ⊗ M` is `((tensorModuleRight M).mapHomologicalComplex _).obj K`,
and derived Tor amplitude of `K` as an object of `D(R)` is
`StacksDraft.TorAmplitude.HasTorAmplitude` (Stacks 0652). This file connects the two, and
derives from that connection the flatness of `Coker(d_K^{a-1})` — the content of Stacks 0653.

Everything here keeps the ring universe `u` and the module universe independent: the ring is
`R : Type u` and the complexes live in `ModuleCat.{max u v} R`. That is what Stacks 0653 needs,
and it is why the file also carries the coefficient-ring bridge described below.

## Main definitions

* `StacksDraft.TorAmplitude.BoundedAbove`: a cochain complex vanishes in all large degrees.
* `StacksDraft.TorAmplitude.scalarLift`: change of coefficient ring along `ULift.ringEquiv`.

## Main results

* `StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude`: Stacks 0653 — a bounded above complex
  of flat modules with derived Tor amplitude in `[a, b]` has flat `Coker(d_K^{a-1})`.
* `StacksDraft.TorAmplitude.isSplitEpi_comparison_app`: for a certified derived tensor product,
  the comparison map at `K` is a split epimorphism as soon as *some* functor on `D(R)` maps to
  termwise tensoring by a transformation that is invertible at `K`;
  `isSplitEpi_map_comparison_app` is the same statement after applying a functor with a left
  adjoint, which is how the witness is allowed to live over the lifted coefficient ring.
* `StacksDraft.TorAmplitude.termwise_isZero_homology_of_derived`: derived Tor amplitude plus that
  split epimorphism gives the termwise vanishing `H^i(K ⊗ M) = 0` for `i ∉ [a, b]`.
* `StacksDraft.TorAmplitude.cokernel_flat_of_termwise_isZero_homology`: the flat-cokernel
  argument at independent ring and module universes.
* `StacksDraft.TorAmplitude.isIso_termwiseDerivedCounit_app_of_flat`: the counit of the total
  left derived functor of termwise tensoring is invertible at a bounded above complex of flats.
* `StacksDraft.TorAmplitude.scalarLift_map_isZero_homology_iff`: changing coefficients along
  `ULift.ringEquiv` preserves and reflects vanishing of derived cohomology.

## Implementation notes

**The coefficient-ring bridge.** `CochainComplex.KFlat` (Stacks 06XZ) and Mathlib's monoidal
structure on `ModuleCat.{w} S` are available only when the module universe agrees with the
universe of the ring. A complex in `ModuleCat.{max u v} R` with `R : Type u` therefore cannot be
fed to them directly. The way round is *not* to enlarge universes but to change the coefficient
ring by an equivalence: `scalarLift` restricts scalars along `ULift.ringEquiv`, carrying
`ModuleCat.{max u v} R` to `ModuleCat.{max u v} (ULift.{v} R)`. The module universe is unchanged
on both sides, and the target ring `ULift.{v} R` lives in `Type (max u v)`, the same universe as
its own modules. So the shared-universe K-flat theory applies on the target, instantiated at
`ULift.{v} R`, and results transport back along the equivalence. The instances here make
`scalarLift` an equivalence on modules, on cochain complexes, and on derived categories, and
`scalarLift_map_isZero_homology_iff` transports the vanishing of derived cohomology in both
directions.

**What the derived-to-termwise step needs, and what it does not.** Only a *split epimorphism* is
needed, not an isomorphism. The universal property of a total left derived functor produces one
for free: given any functor `V` on `D(R)` and any `β : Q ⋙ V ⟶ (K ↦ K ⊗ M) ⋙ Q` whose component
at `K` is invertible, `Functor.leftDerivedLift` factors `β` through the comparison map, which
therefore admits a section at `K` (`isSplitEpi_comparison_app`). Cohomology is additive, so it
carries that split epimorphism to a split epimorphism whose source vanishes by hypothesis, and a
split epimorphism out of a zero object forces its target to vanish. In particular this argument
needs neither a K-flat derivability structure nor the existence of K-flat resolutions
(Stacks 06Y4): the comparison map is *not* shown to be invertible at `K`, only split.

**The witness.** The datum `(V, β)` is taken over the lifted coefficient ring: `V` is the total
left derived functor of termwise tensoring by `scalarLift.obj M`, and `β` its counit, both from
`StacksFrontier.Homology.TorAmplitude.Comparison`, read through `scalarLift` by `liftBeta`. Its
component at `K` is invertible by `isIso_termwiseDerivedCounit_app_of_flat`, which is where the
hypotheses on `K` are spent: bounded above and termwise flat, transported to `ULift.{v} R` by
`Functor.map_isZero` and `Module.Flat.ulift_left_iff`.

**Dependencies owned by other clusters.** Nothing is duplicated here. The K-flat input is Stacks
064K, `CochainComplex.KFlat.kFlat_of_flat` of `StacksFrontier.Homology.KFlat.Flat`, used through
`CochainComplex.KFlat` at the lifted coefficient ring; Stacks 06Y0 enters through
`StacksDraft.TorAmplitude.quasiIso_tensorRight_map` of
`StacksFrontier.Homology.TorAmplitude.Comparison`, and the derived-functor input is that same module,
which stands in for Stacks 0BYI. No `@[stacks]` attribute other than 0653 is attached in this
file.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TorAmplitude

universe u v w

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

variable {R : Type u} [CommRing R]

/-! ### The coefficient-ring bridge -/

/-- Change coefficients along `ULift.ringEquiv` without changing the module carriers. Both module
categories have the same fixed universe `max u v`; this is an equivalence of coefficient rings,
not an enlargement of the module universe. Its point is that the target ring `ULift.{v} R` lives
in the universe of its own modules, so the shared-universe K-flat theory applies there. -/
public noncomputable abbrev scalarLift :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} (ULift.{v} R) :=
  ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

/-- Restricting scalars along the ring equivalence `ULift.ringEquiv` is an equivalence of module
categories. -/
public instance scalarLift_isEquivalence : (scalarLift.{u, v} (R := R)).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{v} R ≃+* R)).isEquivalence_functor

/-- An equivalence of module categories induces an equivalence on cochain complexes. -/
public instance scalarLift_mapHomologicalComplex_isEquivalence :
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
  ((scalarLift.{u, v} (R := R)).asEquivalence.mapHomologicalComplex
    (ComplexShape.up ℤ)).isEquivalence_functor

/-- The localizer morphism of the coefficient change, between the quasi-isomorphism localizers
on cochain complexes, has an underlying functor that is an equivalence. -/
public instance scalarLift_localizerMorphism_functor_isEquivalence :
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
  inferInstanceAs
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence

/-- The localizer morphism of the coefficient change is induced: a map of cochain complexes over
`R` is a quasi-isomorphism exactly when its image over `ULift.{v} R` is, because the coefficient
change preserves homology. -/
public instance scalarLift_localizerMorphism_isInduced :
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsInduced where
  inverseImage_eq := by
    ext K L f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
      (scalarLift.{u, v} (R := R))

/-- The localizer morphism of the coefficient change is a localized equivalence: an induced
localizer morphism whose functor is an equivalence is one. This is what makes
`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` applicable to the coefficient
change, and hence what lets a total left derived functor be transported across it. -/
public instance scalarLift_localizerMorphism_isLocalizedEquivalence :
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsLocalizedEquivalence :=
  LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

/-- Changing coefficients along `ULift.ringEquiv` induces an equivalence of derived
categories. -/
public instance scalarLift_mapDerivedCategory_isEquivalence :
    (scalarLift.{u, v} (R := R)).mapDerivedCategory.IsEquivalence := by
  let G := scalarLift.{u, v} (R := R)
  let : CatCommSq (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).isEquivalence
    DerivedCategory.Q DerivedCategory.Q _

/-- Ordinary tensoring commutes with the change of coefficient ring: tensoring over `R` and then
restricting scalars agrees with restricting scalars and then tensoring over `ULift.{v} R`. -/
public noncomputable def tensorScalarLiftIso (M : ModuleCat.{max u v} R) :
    tensorModuleRight M ⋙ scalarLift ≅
      scalarLift ⋙ tensorModuleRight (scalarLift.obj M) := by
  refine NatIso.ofComponents
    (fun N => (TensorProduct.equivOfCompatibleSMul (ULift.{v} R) R (ULift.{v} R)
      (N : Type (max u v)) (M : Type (max u v))).toModuleIso) ?_
  intro N N' f
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

/-- Vanishing of derived cohomology is invariant under the change of coefficient ring: it is exact
and full and faithful, and does not change the underlying abelian groups. -/
private theorem isZero_homology_scalarLift_iff (X : DerivedCategory (ModuleCat.{max u v} R))
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).obj
      ((scalarLift.{u, v} (R := R)).mapDerivedCategory.obj X)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj X) := by
  let G := scalarLift.{u, v} (R := R)
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  rw [(((DerivedCategory.homologyFunctor _ i).mapIso e.symm).isZero_iff.trans
      ((DerivedCategory.homologyFunctorFactors _ i).app K).isZero_iff),
    (((DerivedCategory.homologyFunctor _ i).mapIso
      ((G.mapDerivedCategory.mapIso e).symm ≪≫ G.mapDerivedCategoryFactors.app K)).isZero_iff.trans
      ((DerivedCategory.homologyFunctorFactors _ i).app _).isZero_iff)]
  exact ⟨fun hz => IsZero.of_full_of_faithful_of_isZero G _
    (hz.of_iso ((K.sc i).mapHomologyIso G).symm),
    fun hz => (G.map_isZero hz).of_iso ((K.sc i).mapHomologyIso G)⟩

/-- The change of coefficient ring preserves vanishing of derived cohomology. -/
public theorem scalarLift_map_isZero_homology (X : DerivedCategory (ModuleCat.{max u v} R))
    (i : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).obj
      ((scalarLift.{u, v} (R := R)).mapDerivedCategory.obj X)) :=
  (isZero_homology_scalarLift_iff X i).2 h

/-- The change of coefficient ring reflects vanishing of derived cohomology. -/
public theorem scalarLift_reflects_isZero_homology
    (X : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (ULift.{v} R)) i).obj
        ((scalarLift.{u, v} (R := R)).mapDerivedCategory.obj X))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj X) :=
  (isZero_homology_scalarLift_iff X i).1 h

/-- Changing coefficients along `ULift.ringEquiv` preserves and reflects vanishing of derived
cohomology. -/
public theorem scalarLift_map_isZero_homology_iff
    (X : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).obj
      ((scalarLift.{u, v} (R := R)).mapDerivedCategory.obj X)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj X) :=
  isZero_homology_scalarLift_iff X i

/-! ### From derived Tor amplitude to termwise vanishing -/

variable
  {derivedTensor : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R)}
  {comparison : ∀ M : ModuleCat.{max u v} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q}
  {isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
          (comparison M)
          (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))}

/-- The split epimorphism argument, after applying a functor `T` with a left adjoint. -/
private theorem isSplitEpi_map_comparison_app_aux
    (isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
          (comparison M)
          (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{max u v} R) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {H : Type*} [Category H] (T : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    [T.IsRightAdjoint]
    (V : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    (β : DerivedCategory.Q ⋙ V ⟶
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ T)
    (hβ : IsIso (β.app K)) : IsSplitEpi (T.map ((comparison M).app K)) := by
  have := isLeftDerived M
  set L := derivedTensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
  set α : DerivedCategory.Q ⋙ (L ⋙ T) ⟶
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (comparison M) T with hα
  have hfac := Functor.leftDerived_fac_app (L ⋙ T) α
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) V β K
  have happ : α.app K = T.map ((comparison M).app K) := by simp [hα]
  refine ⟨⟨inv (β.app K) ≫
    (Functor.leftDerivedLift (L ⋙ T) α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
      V β).app (DerivedCategory.Q.obj K), ?_⟩⟩
  rw [← happ, Category.assoc, hfac, IsIso.inv_hom_id]

/-- The comparison map of a certified derived tensor product is a split epimorphism at `K` as
soon as some functor `V` on `D(R)` comes with a transformation `β` to termwise tensoring whose
component at `K` is invertible.

No hypothesis is placed on `V` beyond `β`. The universal property of the total left derived
functor factors `β` as `γ ≫ comparison M` for a unique `γ`, and `inv (β.app K) ≫ γ.app (Q K)` is
then a section of `(comparison M).app K`. -/
public theorem isSplitEpi_comparison_app
    (isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
          (comparison M)
          (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{max u v} R) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (V : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (β : DerivedCategory.Q ⋙ V ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hβ : IsIso (β.app K)) : IsSplitEpi ((comparison M).app K) :=
  isSplitEpi_map_comparison_app_aux isLeftDerived M K (𝟭 _) V β hβ

/-- The same statement after applying a functor `T` with a left adjoint — in practice the
equivalence of derived categories induced by `scalarLift`, which is what allows `V` and `β` to be
built over the lifted coefficient ring `ULift.{v} R`, where the module universe agrees with the
ring's.

`L ⋙ T` is again a total left derived functor, of `(- ⊗ M) ⋙ T`, so the argument of
`isSplitEpi_comparison_app` applies verbatim to it. -/
public theorem isSplitEpi_map_comparison_app
    (isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
          (comparison M)
          (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{max u v} R) (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {H : Type*} [Category H] (T : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    [T.IsRightAdjoint]
    (V : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    (β : DerivedCategory.Q ⋙ V ⟶
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ T)
    (hβ : IsIso (β.app K)) : IsSplitEpi (T.map ((comparison M).app K)) :=
  isSplitEpi_map_comparison_app_aux isLeftDerived M K T V β hβ

/-- Derived Tor amplitude in `[a, b]` gives the termwise vanishing `H^i(K ⊗ M) = 0` for every
module `M` and every `i ∉ [a, b]`, provided the comparison map at `K` is a split epimorphism.

Cohomology is additive, so it carries the split epimorphism to a split epimorphism whose source
is zero by hypothesis; a split epimorphism out of a zero object forces its target to be zero. -/
public theorem termwise_isZero_homology_of_derived
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    (hsplit : ∀ M : ModuleCat.{max u v} R, IsSplitEpi ((comparison M).app K))
    (hamp : HasTorAmplitude derivedTensor comparison isLeftDerived
      (DerivedCategory.Q.obj K) a b)
    (M : ModuleCat.{max u v} R) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((((tensorModuleRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology i) := by
  have h := hamp M i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi)
  have := hsplit M
  exact (h.of_epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
    ((comparison M).app K))).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app _).symm

/-! ### The flat-cokernel argument at independent universes -/

/-- The flat-cokernel argument with the ring universe and the module universe independent: a
cochain complex `K` of flat `R`-modules in `ModuleCat.{max u v} R` whose termwise tensor products
have vanishing cohomology outside `[a, b]` has flat `Coker(d_K^{a-1})`.

Only the lower bound `a` is used, and only the test modules in `Type (max u v)` — which is
exactly the universe the flatness criterion needs. The two substantive steps are
`StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact` and
`StacksDraft.TorAmplitude.Termwise.flat_quotient_of_rTensor_subtype_injective`; what is restated
  here is the
categorical unfolding of the hypothesis, which the shared-universe
`StacksDraft.TorAmplitude.Termwise.cokernel_flat_of_termwise_torAmplitude` performs for the
  monoidal tensor product. -/
public theorem cokernel_flat_of_termwise_isZero_homology
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    (hflat : ∀ n : ℤ, Module.Flat R (K.X n))
    (htor : ∀ (M : ModuleCat.{max u v} R) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((((tensorModuleRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology i)) :
    Module.Flat R (cokernel (K.d (a - 1) a) : ModuleCat.{max u v} R) := by
  set g : (K.X (a - 1) : Type _) →ₗ[R] (K.X a : Type _) := (K.d (a - 1) a).hom with hg
  have hKa : Module.Flat R (K.X a : Type _) := hflat a
  have hinj : ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M (LinearMap.range g).subtype) := by
    intro M _ _
    have hexactAt : (((tensorModuleRight (ModuleCat.of R M)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt (a - 1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (htor (ModuleCat.of R M) (a - 1) (Or.inl (by omega)))
    rw [HomologicalComplex.exactAt_iff,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexactAt
    have key : Function.Exact
        (LinearMap.rTensor M (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom)
        (LinearMap.rTensor M (K.d (a - 1) ((ComplexShape.up ℤ).next (a - 1))).hom) := hexactAt
    rw [show ((ComplexShape.up ℤ).next (a - 1)) = a by simp [CochainComplex.next]] at key
    refine StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact
      (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom g ?_ M key
    rw [hg, ← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]
  have hflatQ : Module.Flat R ((K.X a : Type _) ⧸ LinearMap.range g) :=
    StacksDraft.TorAmplitude.Termwise.flat_quotient_of_rTensor_subtype_injective (LinearMap.range g)
      hinj
  exact Module.Flat.of_linearEquiv
    (ModuleCat.cokernelIsoRangeQuotient (K.d (a - 1) a)).toLinearEquiv

/-! ### Invertibility of the termwise counit at a bounded above complex of flats -/

set_option backward.isDefEq.respectTransparency false in
/-- The counit of the total left derived functor of termwise tensoring is invertible at a bounded
above complex of flat modules. This is the companion, for a bounded above complex of flats, of
`isIso_termwiseDerivedCounit_app`, which covers a K-projective complex: a bounded above complex
admits a bounded above projective resolution `π`, the counit is invertible at that resolution
since it is K-projective, and termwise tensoring carries `π` to a quasi-isomorphism because both
complexes are K-flat.

Stated for a ring and its modules in one shared universe `w`, which is what the K-flat theory
needs; the consumer reaches the independent-universe case through `scalarLift`. -/
public theorem isIso_termwiseDerivedCounit_app_of_flat {S : Type w} [CommRing S]
    (N : ModuleCat.{w} S) (P : CochainComplex (ModuleCat.{w} S) ℤ)
    (hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat S (P.X i)) :
    IsIso ((termwiseDerivedCounit N).app P) := by
  obtain ⟨d, hd⟩ := hbounded
  have hPLE : P.IsStrictlyLE d := (CochainComplex.isStrictlyLE_iff P d).2 hd
  have hPKF : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P d
  obtain ⟨P', m, π, hP'LE, hP'proj, hπ⟩ := exists_projective_resolution P d
  have : P'.IsKProjective := CochainComplex.isKProjective_of_projective P' m
  have h1 : IsIso ((termwiseDerivedCounit N).app P') := isIso_termwiseDerivedCounit_app N P'
  have h2 : QuasiIso (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map π) :=
    quasiIso_tensorModuleRight_map N π (kFlat_of_isStrictlyLE_projective P' m hP'proj) hPKF
  have h3 : IsIso (DerivedCategory.Q.map
      (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map π)) := by
    infer_instance
  have hkey : IsIso ((DerivedCategory.Q ⋙ termwiseDerived N).map π ≫
      (termwiseDerivedCounit N).app P) := by
    rw [(termwiseDerivedCounit N).naturality π]
    dsimp only [Functor.comp_map]
    infer_instance
  have h4 : IsIso ((DerivedCategory.Q ⋙ termwiseDerived N).map π) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ termwiseDerived N).map π)
    ((termwiseDerivedCounit N).app P)

/-! ### The comparison datum over the lifted coefficient ring -/

/-- Change of coefficient ring on cochain complexes. -/
private noncomputable abbrev liftCx : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤
    CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ :=
  (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The change of coefficient ring `StacksDraft.TorAmplitude.scalarLift`, read on derived
categories.  It is an equivalence, by `scalarLift_mapDerivedCategory_isEquivalence`. -/
public noncomputable abbrev scalarLiftDerived : DerivedCategory (ModuleCat.{max u v} R) ⥤
    DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) :=
  (scalarLift.{u, v} (R := R)).mapDerivedCategory

/-- Termwise tensoring commutes with the change of coefficient ring, on cochain complexes. -/
private noncomputable def liftCxTensorIso (M : ModuleCat.{max u v} R) :
    liftCx.{u, v} (R := R) ⋙
        (tensorModuleRight (scalarLift.obj M)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ liftCx.{u, v} (R := R) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (scalarLift.{u, v} (R := R) ⋙ tensorModuleRight (scalarLift.obj M)))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (tensorScalarLiftIso M) (ComplexShape.up ℤ)).symm

private noncomputable def liftBetaIsoSrc (M : ModuleCat.{max u v} R) :
    DerivedCategory.Q ⋙ (scalarLiftDerived.{u, v} (R := R) ⋙ termwiseDerived (scalarLift.obj M)) ≅
      liftCx.{u, v} (R := R) ⋙ (DerivedCategory.Q ⋙ termwiseDerived (scalarLift.obj M)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _

private noncomputable def liftBetaIsoTgt (M : ModuleCat.{max u v} R) :
    liftCx.{u, v} (R := R) ⋙
        ((tensorModuleRight (scalarLift.obj M)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) ≅
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        scalarLiftDerived.{u, v} (R := R) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (liftCxTensorIso M) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The transported comparison transformation: the counit of the total left derived functor of
termwise tensoring over `ULift.{v} R`, read through the change of coefficient ring. -/
private noncomputable def liftBeta (M : ModuleCat.{max u v} R) :
    DerivedCategory.Q ⋙ (scalarLiftDerived.{u, v} (R := R) ⋙ termwiseDerived (scalarLift.obj M)) ⟶
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        scalarLiftDerived.{u, v} (R := R) :=
  (liftBetaIsoSrc M).hom ≫
    Functor.whiskerLeft (liftCx.{u, v} (R := R))
      (termwiseDerivedCounit (scalarLift.obj M)) ≫ (liftBetaIsoTgt M).hom

private theorem isIso_liftBeta_app (M : ModuleCat.{max u v} R)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (h : IsIso ((termwiseDerivedCounit (scalarLift.obj M)).app
      ((liftCx.{u, v} (R := R)).obj K))) : IsIso ((liftBeta M).app K) := by
  dsimp only [liftBeta]
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-! ### Stacks 0653 -/

/-- **Stacks Tag 0653.** Let `R` be a ring, `a b : ℤ`, and `K` a bounded above cochain complex of
flat `R`-modules which, as an object of `D(R)`, has Tor amplitude in `[a, b]` for some certified
derived tensor product. Then `Coker(d_K^{a-1}) = K^a / Im(d_K^{a-1})` is a flat `R`-module.

The ring universe `u` and the module universe are independent: `R : Type u` and the complex lives
in `ModuleCat.{max u v} R`. Flatness of the terms is spelled out rather than written as
`StacksDraft.TorAmplitude.Termwise.IsComplexOfFlats`, which is available only when the two
  universes agree.

The derived tensor product is an arbitrary certified one, so the statement does not depend on a
construction of it. Boundedness enters through the comparison: the counit of the total left
derived functor of termwise tensoring is invertible at a bounded above complex of flat modules
(`isIso_termwiseDerivedCounit_app_of_flat`), which makes the given comparison map a split
epimorphism there, and cohomology carries that split epimorphism from a vanishing source to a
vanishing target. -/
@[stacks 0653]
public theorem cokernel_flat_of_torAmplitude
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    (hbounded : BoundedAbove K) (hflat : ∀ n : ℤ, Module.Flat R (K.X n))
    (hamp : HasTorAmplitude derivedTensor comparison isLeftDerived
      (DerivedCategory.Q.obj K) a b) :
    Module.Flat R (cokernel (K.d (a - 1) a) : ModuleCat.{max u v} R) := by
  refine cokernel_flat_of_termwise_isZero_homology K a b hflat ?_
  intro M i hi
  -- Over `ULift.{v} R` the ring and its modules share the universe `max u v`, so the lifted
  -- complex is in range of the K-flat theory.
  have hb' : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (((liftCx.{u, v} (R := R)).obj K).X j) := by
    obtain ⟨N, hN⟩ := hbounded
    exact ⟨N, fun j hj => (scalarLift.{u, v} (R := R)).map_isZero (hN j hj)⟩
  have hf' : ∀ j : ℤ, Module.Flat (ULift.{v} R) (((liftCx.{u, v} (R := R)).obj K).X j) := by
    intro j
    show Module.Flat (ULift.{v} R) (K.X j)
    rw [Module.Flat.ulift_left_iff]
    exact hflat j
  have hsplit : IsSplitEpi ((scalarLiftDerived.{u, v} (R := R)).map ((comparison M).app K)) :=
    isSplitEpi_map_comparison_app isLeftDerived M K (scalarLiftDerived.{u, v} (R := R))
      (scalarLiftDerived.{u, v} (R := R) ⋙ termwiseDerived (scalarLift.obj M)) (liftBeta M)
      (isIso_liftBeta_app M K
        (isIso_termwiseDerivedCounit_app_of_flat (scalarLift.obj M) _ hb' hf'))
  have h1 := scalarLift_map_isZero_homology
    ((derivedTensor.obj (DerivedCategory.Q.obj K)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)) i
    (hamp M i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi))
  have hz : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (ULift.{v} R)) i).obj
        ((scalarLiftDerived.{u, v} (R := R)).obj
          (((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q).obj K))) :=
    h1.of_epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).map
      ((scalarLiftDerived.{u, v} (R := R)).map ((comparison M).app K)))
  exact (scalarLift_reflects_isZero_homology
    (DerivedCategory.Q.obj (((tensorModuleRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)) i hz).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app _).symm

end

end StacksDraft.TorAmplitude
