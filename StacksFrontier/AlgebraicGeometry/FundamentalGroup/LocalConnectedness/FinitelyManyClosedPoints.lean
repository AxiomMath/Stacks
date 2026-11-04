module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.BaseChangeExactSequence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpenClosedComplement

/-!
# The fundamental group of the complement of finitely many closed points

Let `X` be a scheme and let `x₁, …, xₙ ∈ X` be finitely many closed points such that the open
`U = X ∖ {x₁, …, xₙ}` is connected and retrocompact in `X`, and such that for each `i` the
punctured spectrum `Uᵢˢʰ` of the strict henselization of `𝒪_{X,xᵢ}` is connected. Then the
induced continuous homomorphism

```
π₁(U, ū) ⟶ π₁(X, ū)
```

is surjective for every geometric point `ū` of `U`.

## Main results

* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_fullyFaithful`: for a morphism
  `j : U ⟶ X` of connected schemes, if `FÉt_X ⥤ FÉt_U` is fully faithful then
  `π₁(U, ū) → π₁(X, ū)` is surjective.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_finite_isClosed_compl`: the
  surjectivity of `π₁(U, ū) → π₁(X, ū)` when `U` is the complement of a finite set of closed
  points, connected and retrocompact.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_quasiCompact_of_isClosed_compl`: the
  same conclusion for a dense retrocompact open `U` whose complement consists of closed points.
* `AlgebraicGeometry.isDominant_of_finite_isClosed_compl`: the complement of a finite set of
  closed points in a connected scheme is dense.
* `AlgebraicGeometry.connectedSpace_of_isDominant`: the target of a dominant morphism out of a
  connected scheme is connected.

## Implementation notes

The open `U` is presented as a quasi-compact open immersion `j : U ⟶ X`, and the finite set of
closed points as the complement of its image: `hfinite` says that `X ∖ U` is finite and `hclosed`
that its points are closed.

Density of `U` is not a hypothesis of the source; it follows from the finiteness of `X ∖ U` and
the connectedness of `X`. The connectedness of `X`, which the source assumes implicitly by
writing `π₁(X, ū)`, is a hypothesis of
`AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_finite_isClosed_compl`; under the
density assumption of
`AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_quasiCompact_of_isClosed_compl` it
follows from the connectedness of `U`.

## References

* [Stacks, Tag 0BSC](https://stacks.math.columbia.edu/tag/0BSC)
* [Stacks, Tag 0BSA](https://stacks.math.columbia.edu/tag/0BSA)
* [Stacks, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-- The target of a dominant morphism whose source is connected is connected. -/
theorem connectedSpace_of_isDominant {U X : Scheme.{u}} (j : U ⟶ X) [ConnectedSpace U]
    [IsDominant j] : ConnectedSpace X := by
  rw [connectedSpace_iff_univ]
  have h := (isConnected_range (f := j.base) j.base.hom.continuous).closure
  rwa [j.denseRange.closure_range] at h

/-- **The complement of a finite set of closed points of a connected scheme is dense.** Let
`j : U ⟶ X` be a morphism of schemes with `U` connected and `X` connected, and suppose that the
complement of the image of `j` is finite and consists of closed points. Then `j` is dominant. -/
theorem isDominant_of_finite_isClosed_compl {U X : Scheme.{u}} (j : U ⟶ X) [ConnectedSpace U]
    [ConnectedSpace X] (hfinite : ((Set.range j.base)ᶜ : Set X).Finite)
    (hclosed : ∀ x : X, x ∉ Set.range j.base → IsClosed ({x} : Set X)) :
    IsDominant j := by
  have hsub : (closure (Set.range j.base))ᶜ ⊆ (Set.range j.base)ᶜ :=
    Set.compl_subset_compl.mpr subset_closure
  have hcompl : IsClosed ((closure (Set.range j.base))ᶜ : Set X) := by
    rw [← Set.biUnion_of_singleton ((closure (Set.range j.base))ᶜ : Set X)]
    exact (hfinite.subset hsub).isClosed_biUnion fun x hx => hclosed x (hsub hx)
  have hclopen : IsClopen (closure (Set.range j.base) : Set X) :=
    ⟨isClosed_closure, isClosed_compl_iff.mp hcompl⟩
  exact ⟨denseRange_iff_closure_range.mpr
    (hclopen.eq_univ ⟨j.base (Classical.arbitrary U), subset_closure ⟨_, rfl⟩⟩)⟩

/-- **Full faithfulness of base change implies surjectivity on étale fundamental groups.** Let
`j : U ⟶ X` be a morphism of connected schemes and let `ū` be a geometric point of `U`. If base
change of finite étale covers `FÉt_X ⥤ FÉt_U` along `j` is fully faithful, then the induced
continuous homomorphism `π₁(U, ū) ⟶ π₁(X, ū)` is surjective. -/
@[sga "1 V 6.9" "special case"]
theorem surjective_etaleFundamentalGroupMap_of_fullyFaithful {U X : Scheme.{u}}
    [ConnectedSpace U] [ConnectedSpace X] (j : U ⟶ X) (u : GeometricPoint U)
    (hff : Nonempty (finiteEtaleBaseChange j).FullyFaithful) :
    Function.Surjective (etaleFundamentalGroupMap j u) := by
  let H := finiteEtaleBaseChange j
  let F := finiteEtaleFiberFintypeFunctor X (u.map j)
  let F' := finiteEtaleFiberFintypeFunctor U u
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso j u
  let d := galoisFunctorDataOfFiberIso F F' H t
  have _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  have _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  let star := finiteEtaleOverTerminal X
  let star' := finiteEtaleOverTerminal U
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange j u
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  have hdsurj : Function.Surjective d.hom :=
    ((surjective_inducedHom_tfae F F' H hH t d star star' hs hs' hHs).out 2 1).mp hff
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj ((autMulEquivEtaleFundamentalGroup X (u.map j)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup U u σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom j u d σ, hσ,
    MulEquiv.apply_symm_apply]

/-- **Surjectivity of `π₁(U) → π₁(X)` for a dense retrocompact open with closed complement.**
Let `j : U ⟶ X` be a dense, quasi-compact open immersion with `U` connected, and assume that
every point of `X ∖ U` is closed and that the punctured spectrum of the strict henselization of
its local ring is connected. Then for every geometric point `ū` of `U` the induced continuous
homomorphism

```
π₁(U, ū) ⟶ π₁(X, ū)
```

is surjective; equivalently, every connected finite étale cover of `X` stays connected over `U`.
Here `X` is connected because `U` is connected and dense. -/
theorem surjective_etaleFundamentalGroupMap_of_quasiCompact_of_isClosed_compl
    {U X : Scheme.{u}} (j : U ⟶ X) [ConnectedSpace U] [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j]
    (hclosed : ∀ x : X, x ∉ Set.range j.base → IsClosed ({x} : Set X))
    (hconnected : ∀ x : X, x ∉ Set.range j.base →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    (u : GeometricPoint U) :
    letI : ConnectedSpace X := connectedSpace_of_isDominant j
    Function.Surjective (etaleFundamentalGroupMap j u) := by
  have : ConnectedSpace X := connectedSpace_of_isDominant j
  exact surjective_etaleFundamentalGroupMap_of_fullyFaithful j u
    (fullyFaithful_finiteEtaleBaseChange_of_quasiCompact_of_isClosed_compl j hclosed hconnected)

/-- **Surjectivity of `π₁(U) → π₁(X)` for the complement of finitely many closed points.** Let
`X` be a connected scheme, let
`x₁, …, xₙ ∈ X` be finitely many closed points, and let `U = X ∖ {x₁, …, xₙ}`, presented as an
open immersion `j : U ⟶ X` whose image has finite complement consisting of closed points.
Assume that

1. `U` is connected and retrocompact in `X` — `[ConnectedSpace U]` and `[QuasiCompact j]`;
2. for each `i` the punctured spectrum of the strict henselization of `𝒪_{X,xᵢ}` is connected —
   `hconnected`.

Then for every geometric point `ū` of `U` the induced continuous homomorphism

```
π₁(U, ū) ⟶ π₁(X, ū)
```

is surjective; equivalently, every connected finite étale cover of `X` stays connected over `U`.
-/
@[stacks 0BSC "the surjectivity clause `π₁(U) → π₁(X)` for `U` the complement of finitely many \
closed points, under hypotheses (1) and (2); the kernel description is not proved here"]
theorem surjective_etaleFundamentalGroupMap_of_finite_isClosed_compl
    {U X : Scheme.{u}} (j : U ⟶ X) [ConnectedSpace U] [ConnectedSpace X] [IsOpenImmersion j]
    [QuasiCompact j]
    (hfinite : ((Set.range j.base)ᶜ : Set X).Finite)
    (hclosed : ∀ x : X, x ∉ Set.range j.base → IsClosed ({x} : Set X))
    (hconnected : ∀ x : X, x ∉ Set.range j.base →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    (u : GeometricPoint U) :
    Function.Surjective (etaleFundamentalGroupMap j u) := by
  have : IsDominant j := isDominant_of_finite_isClosed_compl j hfinite hclosed
  exact surjective_etaleFundamentalGroupMap_of_quasiCompact_of_isClosed_compl j hclosed
    hconnected u

end AlgebraicGeometry

end
