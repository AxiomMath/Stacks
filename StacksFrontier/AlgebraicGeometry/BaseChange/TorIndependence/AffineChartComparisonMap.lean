module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.Tor.Independence
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of Stacks 0DJ8 on a Cartesian affine-open chart

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes and let `ch` be a Cartesian affine-open chart for it, the
quadruple `U ⊆ X`, `V ⊆ S`, `V' ⊆ S'`, `U' = V' ×_V U` of `AlgebraicGeometry.BaseChangeChart`.
Given `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, this module constructs the
morphism

```
RΓ(U, K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V') ⟶ RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U', K')
```

in `D(𝒪_{S'}(V'))` whose invertibility is condition (2) of Stacks 0DJ8, and condition (3) when
it is asked only of a family of charts whose opens `U'` cover `X'`.

## Main definitions

* `AlgebraicGeometry.affineDerivedSections`: derived sections `RΓ(U, -) : D(𝒪_X) ⥤ D(𝒪_X(U))`
  over an affine open presented by an open immersion `Spec A ⟶ X`.
* `AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeMap`: the second arrow displayed above,
  the identification `RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U', L(g')^*K)`.
* `AlgebraicGeometry.BaseChangeChart.pullbackComparison`: the whole composition for `K'` the
  derived pullback of `K` and `φ` the identity.
* `AlgebraicGeometry.BaseChangeChart.comparison`: the whole composition, the morphism whose
  invertibility is conditions (2) and (3).

## Main results

* `AlgebraicGeometry.BaseChangeChart.isIso_sectionsBaseChangeMap`: the identification is an
  isomorphism whenever every cohomology sheaf of `K` is quasi-coherent.
* `AlgebraicGeometry.BaseChangeChart.comparison_comp`: the comparison is functorial in `φ`.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison`: condition (2) holds — the comparison
  map is an isomorphism on every chart — when `X` and `S'` are Tor independent over `S`, the
  cohomology sheaves of `K` are quasi-coherent, and `φ` is an isomorphism.
* `AlgebraicGeometry.exists_coveringFamily_isIso_comparison`: the step (2) ⟹ (3) for the
  comparison map itself.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Derived sections over an affine open presented by an open immersion from a spectrum.**
For `i : Spec A ⟶ X` an open immersion this is `RΓ(U, -) : D(𝒪_X) ⥤ D(A)` for `U` the image of
`i`: restrict along `i`, then take `A`-linear derived global sections. -/
public abbrev affineDerivedSections {A : CommRingCat.{u}} {X : Scheme.{u}} (i : Spec A ⟶ X) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Stacks.Duality.derivedPullback i ⋙ derivedGlobalSectionsOver (𝟙 (Spec A))

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The identification in condition (2).** On a chart, derived sections of `K` over `U` base
changed along `𝒪_X(U) ⟶ 𝒪_{X'}(U')` compare with derived sections over `U'` of the derived
pullback of `K`: `RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U', L(g')^*K)`. -/
@[stacks 0DJ8 "the second arrow of the composition in (2): the identification \
RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') = RΓ(U', L(g')^*K)"]
public def sectionsBaseChangeMap (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).functor.obj ((affineDerivedSections ch.incU).obj K) ⟶
      (affineDerivedSections ch.incU').obj ((Stacks.Duality.derivedPullback g').obj K) :=
  (derivedTildeGlobalSectionsAdjunction ch.A').val.unit.app _ ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map
      ((derivedTildeCompι ch.A').hom.app _) ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map
      ((affinePullbackComparison ch.A ch.A' ch.c).inv.app
        ((affineDerivedSections ch.incU).obj K)) ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map
      ((Stacks.Duality.derivedPullback (Spec.map ch.c)).map
        ((derivedTildeCompι ch.A).inv.app ((affineDerivedSections ch.incU).obj K))) ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map
      ((Stacks.Duality.derivedPullback (Spec.map ch.c)).map
        ((derivedTildeGlobalSectionsAdjunction ch.A).val.counit.app
          ((Stacks.Duality.derivedPullback ch.incU).obj K))) ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map
      ((Stacks.Duality.derivedPullbackCompIso (Spec.map ch.c) ch.incU).hom.app K) ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map (eqToHom (congrArg
      (fun t : Spec ch.A' ⟶ X => (Stacks.Duality.derivedPullback t).obj K) ch.wU'U.symm)) ≫
    (derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).map
      ((Stacks.Duality.derivedPullbackCompIso ch.incU' g').inv.app K)

/-- **The identification `sectionsBaseChangeMap` is an isomorphism** when every cohomology sheaf
of `K` is quasi-coherent. -/
@[stacks 0DJ8 "the second arrow of the composition in (2) is an isomorphism for K with \
quasi-coherent cohomology, so (2) tests the composition the source displays"]
public theorem isIso_sectionsBaseChangeMap (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    IsIso (ch.sectionsBaseChangeMap K) := by
  have hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec ch.A).Modules n).obj
      ((Stacks.Duality.derivedPullback ch.incU).obj K)).IsQuasicoherent := fun n =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback' ch.incU ⟨K, hK⟩ n
  have : IsIso ((derivedTildeGlobalSectionsAdjunction ch.A).val.counit.app
      ((Stacks.Duality.derivedPullback ch.incU).obj K)) :=
    isIso_derivedTildeGlobalSectionsAdjunction_counit_app ch.A
      ⟨(Stacks.Duality.derivedPullback ch.incU).obj K, hqc⟩
  have := isIso_derivedTildeGlobalSectionsAdjunction_unit ch.A'
  have : IsIso ((derivedTildeGlobalSectionsAdjunction ch.A').val.unit.app
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).functor.obj ((affineDerivedSections ch.incU).obj K))) :=
    NatIso.isIso_app_of_isIso _ _
  dsimp only [sectionsBaseChangeMap]
  infer_instance

/-- **The comparison map of Stacks 0DJ8 (2) and (3), for the derived pullback itself.** On a
chart, the composition

`RΓ(U,K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V') ⟶ RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U', L(g')^*K)`

in `D(𝒪_{S'}(V'))`: the derived base-change comparison of Stacks 065Z for the chart's pushout
square of rings, followed by the identification `sectionsBaseChangeMap`. -/
public def pullbackComparison (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).functor.obj
        ((ModuleCat.restrictScalars ch.a.hom).mapDerivedCategory.obj
          ((affineDerivedSections ch.incU).obj K)) ⟶
      (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.obj
        ((affineDerivedSections ch.incU').obj ((Stacks.Duality.derivedPullback g').obj K)) :=
  (@RingTheory.TorIndependence.derivedBaseChangeComparison _ _ _ _ _ _ _ _ _ _ _ _
      ch.a.hom ch.b.hom ch.c.hom ch.d.hom ch.isPushout_hom
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).functor
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).functor
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).comparison
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).comparison
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).isLeftDerived
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).isLeftDerived).2.1.app ((affineDerivedSections ch.incU).obj K) ≫
    (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map (ch.sectionsBaseChangeMap K)

/-- **The chart comparison map.** On a chart, the composition

`RΓ(U,K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V') ⟶ RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U',K')`

in `D(𝒪_{S'}(V'))`: `pullbackComparison` followed by `RΓ(U', -)` applied to the given morphism
`φ : L(g')^*K ⟶ K'`. -/
@[stacks 0DJ8 "the comparison map on a Cartesian affine-open chart: the morphism whose \
invertibility is condition (2), and, asked only of a family of charts whose opens U' cover X', \
condition (3)"]
public def comparison (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).functor.obj
        ((ModuleCat.restrictScalars ch.a.hom).mapDerivedCategory.obj
          ((affineDerivedSections ch.incU).obj K)) ⟶
      (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.obj
        ((affineDerivedSections ch.incU').obj K') :=
  ch.pullbackComparison K ≫ (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map
    ((affineDerivedSections ch.incU').map φ)

/-- The chart comparison is functorial in the given morphism `L(g')^*K ⟶ K'`: only its last
factor depends on that morphism. -/
public theorem comparison_comp (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' K'' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (ψ : K' ⟶ K'') :
    ch.comparison K K'' (φ ≫ ψ) =
      ch.comparison K K' φ ≫ (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map
        ((affineDerivedSections ch.incU').map ψ) := by
  dsimp only [comparison]
  rw [Functor.map_comp (affineDerivedSections ch.incU') φ ψ, Functor.map_comp, Category.assoc]

/-- **The chart comparison of Stacks 0DJ8 (2) is an isomorphism.** Let `X` and `S'` be Tor
independent over `S`, let `K ∈ D(𝒪_X)` have quasi-coherent cohomology sheaves, and let
`φ : L(g')^*K ⟶ K'` be an isomorphism. Then on every Cartesian affine-open chart the comparison

`RΓ(U,K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V') ⟶ RΓ(U',K')`

is an isomorphism. -/
public theorem isIso_comparison (hTor : TorIndependent f g) (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (hφ : IsIso φ) :
    IsIso (ch.comparison K K' φ) := by
  have := @isIso_derivedBaseChangeComparison _ _ _ _ _ _ _ _ hTor ch
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.b.hom).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.c.hom).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.b.hom).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.c.hom).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.b.hom).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.c.hom).isLeftDerived
  have := ch.isIso_sectionsBaseChangeMap K hK
  have := hφ
  dsimp only [comparison, pullbackComparison]
  infer_instance

end BaseChangeChart

/-- **The step (2) ⟹ (3).** If the comparison map of every Cartesian affine-open chart is an
isomorphism, then there is a family of charts on which it is, whose opens `U'` cover `X'`. -/
@[stacks 0DJ8 "(2) ⟹ (3) for the comparison map itself, which is the step of the three-way \
equivalence that needs no affine reduction: take the family of all charts"]
public theorem exists_coveringFamily_isIso_comparison {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (h : ∀ ch : BaseChangeChart f g f' g', IsIso (ch.comparison K K' φ)) :
    ∃ 𝒞 : Set (BaseChangeChart f g f' g'), (∀ ch ∈ 𝒞, IsIso (ch.comparison K K' φ)) ∧
      ∀ x' : X', ∃ ch ∈ 𝒞, ∃ y : Spec ch.A', ch.incU' y = x' :=
  exists_coveringFamily_of_forall_baseChangeChart sq
    (fun ch => IsIso (ch.comparison K K' φ)) h

end AlgebraicGeometry

end
