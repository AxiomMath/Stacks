module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AlgebraPullbackHalf

/-!
# The canonical algebra-pullback module comparison is invertible

For every morphism of schemes `g : T ⟶ S` and every sheaf of commutative `𝒪_S`-algebras `E`, the
canonical comparison `Stacks.FundamentalGroup.algebraPullbackModuleComparison g E` from `g^*` of
the module underlying `E` to the module underlying `(algebraPullback g).obj E` is an isomorphism,
with no hypothesis on `g` or on `E`. Consequently the hypothesis `hpullback` of
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` holds
(`AlgebraicGeometry.algebraPullbackModuleIso_of_isQuasicoherent`), and that statement holds without
it (`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_h088F_of_hdata`).

## Main results

* `AlgebraicGeometry.isIso_algebraPullbackModuleComparison`: the canonical comparison
  `g^*(module underlying E) ⟶ module underlying ((algebraPullback g).obj E)` is an isomorphism, for
  an arbitrary morphism of schemes and an arbitrary algebra sheaf.
* `AlgebraicGeometry.algebraPullbackModuleIso_of_isQuasicoherent`: `hpullback`, in the shape
  `adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` binds it.
* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_h088F_of_hdata`: that statement with
  `hpullback` discharged; its remaining hypotheses are `h088F` and `hdata`.

## Implementation notes

The invertibility is `Stacks.AlgebraPullbackQcoh.isIso_comparison`, which proves on stalks, for an
arbitrary morphism of schemes and an arbitrary algebra sheaf, that
`Stacks.ModuleStalkTensor.comparison g E` is an isomorphism. That morphism and
`Stacks.FundamentalGroup.algebraPullbackModuleComparison g E` are the same morphism.

Both are adjoint transposes, under one and the same
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g`, of a morphism
`E ⟶ g_*((algebraPullback g).obj E)` of underlying modules, so it is enough to identify the two
transposes:

* `Stacks.ModuleStalkTensor.comparisonPushforward g E` is built from
  `Stacks.ModuleStalkTensor.adjointRingMap g E`, the transpose of
  `Stacks.AffineAlgebraEquivalence.algebraPullbackMap` across the inverse-image adjunction for
  sheaves of commutative rings, read through
  `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`;
* `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap` of the unit of
  `Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` is built from
  `Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap` of the `Under.right` component of that unit.

`Stacks.AffineAlgebraEquivalence.homEquiv_right` computes that component at the identity:
the unit's right component is the transpose of
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap`, i.e. `adjointAlgebraMap`
(`AlgebraicGeometry.algebraPullbackPushforwardAdjunction_unit_right`). Both morphisms of
underlying modules are, on sections, the map on sections of that one morphism of sheaves of
rings, so they agree by `AlgebraicGeometry.Scheme.Modules.hom_ext`.

No flatness, finiteness or quasi-compactness is needed.
`Stacks.FundamentalGroup.isIso_algebraPullbackModuleComparison_iff` settles the same
invertibility only for an algebra of the form `f_*𝒪_W` along a flat `g` with `f` quasi-compact
and quasi-separated, which does not cover the morphisms `pullback.fst f (adicThickeningι A I n)`,
base changes of closed immersions. On the stalk at `t` both sides of the comparison are the tensor
product `𝒪_{T,t} ⊗_{𝒪_{S,g t}} E_{g t}`, by `Stacks.PullbackTensorIso.pullbackStalkEquiv` for the
source and `Stacks.AlgebraPullbackQcoh.targetStalkLinearEquiv` for the target, and the comparison
is the identity between them; that argument uses no property of `g` and no property of `E`.
So the hypothesis `AlgebraSheaf.IsQuasicoherent E` carried by the type of `hpullback` is not used.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.AffineAlgebraEquivalence
open Stacks.FundamentalGroup (algebraPullbackModuleComparison)

universe u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-! ### The unit of the algebra base-change adjunction, on underlying sheaves of rings -/

/-- **The right component of the unit of the base-change adjunction for algebra sheaves is the
adjoint transpose of `Stacks.AffineAlgebraEquivalence.algebraPullbackMap`.** This is
`Stacks.AffineAlgebraEquivalence.homEquiv_right` read at the identity of
`(algebraPullback g).obj E`, where the adjunction's bijection returns the unit. -/
theorem algebraPullbackPushforwardAdjunction_unit_right (E : AlgebraSheaf S) :
    ((algebraPullbackPushforwardAdjunction g).unit.app E).right =
      Stacks.ModuleStalkTensor.adjointAlgebraMap g E := by
  have h := homEquiv_right g E ((algebraPullback g).obj E) (𝟙 _)
  rwa [Adjunction.homEquiv_id] at h

/-- The same identity for sheaves of not necessarily commutative rings, which is the category
sheaves of modules are taken over: both sides are the image of the preceding identity under
`CategoryTheory.sheafCompose` for `CategoryTheory.forget₂ CommRingCat RingCat`. -/
theorem ringSheafMap_algebraPullbackPushforwardAdjunction_unit (E : AlgebraSheaf S) :
    AlgebraSheaf.ringSheafMap ((algebraPullbackPushforwardAdjunction g).unit.app E) =
      Stacks.ModuleStalkTensor.adjointRingMap g E :=
  congrArg (CategoryTheory.sheafCompose (_root_.Opens.grothendieckTopology
      (S : TopCat.{u})) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (algebraPullbackPushforwardAdjunction_unit_right g E)

/-! ### The two comparisons are one morphism -/

/-- **The two adjoint transposes agree.** `Stacks.ModuleStalkTensor.comparisonPushforward` and
the module underlying the unit of the base-change adjunction for algebra sheaves are, on
sections over every open, the map on sections of one and the same morphism of sheaves of rings;
the two readings of that map on sections are each `rfl`. -/
theorem comparisonPushforward_eq_underlyingModuleMap_unit (E : AlgebraSheaf S) :
    Stacks.ModuleStalkTensor.comparisonPushforward g E =
      AlgebraSheaf.underlyingModuleMap ((algebraPullbackPushforwardAdjunction g).unit.app E) := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  exact congrArg
    (fun φ : AlgebraSheaf.ringSheaf E ⟶
        AlgebraSheaf.ringSheaf ((algebraPushforward g).obj ((algebraPullback g).obj E)) =>
      (φ.hom.app (op U)).hom x)
    (ringSheafMap_algebraPullbackPushforwardAdjunction_unit g E).symm

/-- **The comparison of the quasi-coherence clause of [Stacks, Tag 01SA] is the canonical
algebra-pullback module comparison.** Both are the adjoint transpose, under the one adjunction
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g`, of the morphism identified
by `comparisonPushforward_eq_underlyingModuleMap_unit`. -/
theorem moduleStalkTensorComparison_eq_algebraPullbackModuleComparison (E : AlgebraSheaf S) :
    Stacks.ModuleStalkTensor.comparison g E = algebraPullbackModuleComparison g E :=
  congrArg ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
      (AlgebraSheaf.underlyingModule E)
      (AlgebraSheaf.underlyingModule ((algebraPullback g).obj E))).symm
    (comparisonPushforward_eq_underlyingModuleMap_unit g E)

/-- **The canonical comparison `g^*(module underlying E) ⟶ module underlying (g⁻¹E ⊗ 𝒪_T)` is an
isomorphism**, for an arbitrary morphism of schemes `g : T ⟶ S` and an arbitrary sheaf of
commutative `𝒪_S`-algebras `E`.

No flatness of `g`, no quasi-compactness or quasi-separatedness, no finiteness and not even
quasi-coherence of `E` is assumed: this is
`Stacks.AlgebraPullbackQcoh.isIso_comparison`, which checks bijectivity on every stalk, carried
across the identification of the two spellings of the comparison. -/
theorem isIso_algebraPullbackModuleComparison (E : AlgebraSheaf S) :
    IsIso (algebraPullbackModuleComparison g E) :=
  cast (congrArg (fun φ : (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule E) ⟶
      AlgebraSheaf.underlyingModule ((algebraPullback g).obj E) => IsIso φ)
    (moduleStalkTensorComparison_eq_algebraPullbackModuleComparison g E))
    (Stacks.AlgebraPullbackQcoh.isIso_comparison g E)

end AlgebraicGeometry

/-! ### `hpullback`, and the chain that binds it -/

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport)

/-- **`hpullback`.** For every morphism of schemes `g : T ⟶ S` and every quasi-coherent sheaf of
commutative `𝒪_S`-algebras `E`, the `𝒪_T`-module underlying `g⁻¹E ⊗_{g⁻¹𝒪_S} 𝒪_T` is the module
pullback `g^*` of the `𝒪_S`-module underlying `E`, compatibly with the multiplication and with
the structure morphism.

This is exactly the binder `hpullback` of
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData`. The two equations are
`AlgebraicGeometry.algebraPullbackModuleIso_of_isIso_comparison`, and the isomorphism is
`AlgebraicGeometry.isIso_algebraPullbackModuleComparison` — which needs no hypothesis, so the
quasi-coherence binder is discarded. -/
def algebraPullbackModuleIso_of_isQuasicoherent :
    ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E :=
  algebraPullbackModuleIso_of_isIso_comparison
    (fun g E _ => isIso_algebraPullbackModuleComparison g E)

/-- **The chain to [Stacks, Tag 09ZT], [Stacks, Tag 0A42] and [Stacks, Tag 0899] with
`hpullback` discharged.** This is
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` with its second binder
removed; the two that remain, `h088F` and `hdata`, are untouched. -/
theorem adicFiniteAlgebraAlgebraization_of_h088F_of_hdata (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (hdata : ∀ (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
        AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
      (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
      (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
      (hBtrans : ∀ n, Nonempty
        ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
      (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
      (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
        (AlgebraSheaf.underlyingModule (B 0)))
      (P : Stacks.Algebraization.CoherentModulesProperOver f),
      ((adicThickeningCompletionFunctor A I f).obj P ≅
          adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0) →
        ∃ d : Stacks.FundamentalGroup.ModuleAlgebraData P.obj.obj, ∀ n, Nonempty
          ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj
            (Stacks.FundamentalGroup.algebraSheafOfModule P.obj.obj d) ≅ B n)) :
    AdicFiniteAlgebraAlgebraization A I f :=
  adicFiniteAlgebraAlgebraization_of_isIso_comparison A I f h088F
    (fun g E _ => isIso_algebraPullbackModuleComparison g E) hdata

end AlgebraicGeometry

end
