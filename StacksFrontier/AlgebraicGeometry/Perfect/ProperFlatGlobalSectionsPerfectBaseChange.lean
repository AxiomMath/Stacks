module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of a proper flat coherent module: perfection and base change

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism of schemes and `F` a coherent
`𝒪_X`-module flat over `Spec A`. [Stacks, Tag 07VK] asserts:

1. `RΓ(X, F)` is a perfect object of `D(A)`;
2. for every ring map `A → A'` the base change map
   `RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X_{A'}, F_{A'})` is an isomorphism.

`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isPerfect_and_isIso_baseChange` states both
clauses together, under exactly these hypotheses.

## How clause (2) is read

The base change `X_{A'}` is any cartesian square

```
X' --g--> X
|         |
f'        f
v         v
Spec A' -> Spec A
```

and `F_{A'}` is `g^* F`. Clause (2) is stated in two forms, both for every ring map `φ : A ⟶ A'`
and every such square.

* **In `D(A')`, at the Čech model.** For *every* finite affine open cover `U` of `X` whose finite
  intersections are affine, the base-change map
  `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsBaseChangeMap`,
  `RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X', g^* F)` in `D(A')`, is an isomorphism. This is the map the
  source's proof writes down: the derived extension of scalars of the alternating Čech complex of
  `U`, which computes `RΓ(X, F)`, compared with its ordinary extension of scalars, which is the
  alternating Čech complex of `g⁻¹U` and computes `RΓ(X', g^* F)`. Such covers exist for every
  proper `f` (`exists_finiteAffineCover_of_isProper`), and the statement quantifies over all of
  them.
* **On the base, at the canonical map.** The cover-free base-change map of
  [Stacks, Tag 08HY], followed by `Rf'_*` of the comparison `L(g)^* F ⟶ g^* F`,
  `L(Spec φ)^* Rf_* F ⟶ Rf'_* g^* F` in `D(𝒪_{Spec A'})`, is an isomorphism. This is the form in
  which the source states and uses the base change of derived direct images
  (Derived Categories of Schemes, Section 36.22); over the affine base `Spec A'` the derived
  category of quasi-coherent complexes is `D(A')` by [Stacks, Tag 06Z0].

## Proof

Clause (1) is `isPerfect_derivedGlobalSections`. The Čech form of clause (2) is
`isIso_derivedGlobalSectionsBaseChangeMap`: properness makes `f` separated, and coherence makes
`F` quasi-coherent. The canonical form is
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isIso_derivedBaseChangeComp_singleDegree`:
properness makes `f` quasi-compact and quasi-separated, `F` is quasi-coherent, and so is its
pullback `g^* F`.

## References

* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open AlgebraicGeometry.ProperFlatBaseChange (singleDegreeComplex)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **[Stacks, Tag 07VK].** Let `A` be a Noetherian ring, let `f : X ⟶ Spec A` be a proper
morphism of schemes and let `F` be a coherent `𝒪_X`-module flat over `Spec A`. Then

1. `RΓ(X, F)` is a perfect object of `D(A)`, and
2. for every ring map `φ : A ⟶ A'` and every cartesian square exhibiting `X'` (with
   `g : X' ⟶ X` and `f' : X' ⟶ Spec A'`) as `X_{A'} = X ×_{Spec A} Spec A'`, the base change of
   `RΓ(X, F)` to `A'` is `RΓ(X', g^* F)`:
   * the canonical base-change map `L(Spec φ)^* Rf_* F ⟶ Rf'_* g^* F` (the map of
     [Stacks, Tag 08HY] followed by `Rf'_*` of `L(g)^* F ⟶ g^* F`) is an isomorphism, and
   * for every finite affine open cover `U` of `X` with affine finite intersections, the
     base-change map `RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X', g^* F)` in `D(A')` computed on the alternating
     Čech complex of `U`, `derivedGlobalSectionsBaseChangeMap`, is an isomorphism.

The proof is the source's: the alternating Čech complex of a finite affine cover computes
`RΓ(X, F)`, is bounded and termwise flat over `A`, and has finite cohomology modules, which gives
clause (1) by [Stacks, Tag 0658] and the Čech form of clause (2) because derived and ordinary
extension of scalars agree on it ([Stacks, Tag 06XY]). -/
@[stacks 07VK]
theorem isPerfect_and_isIso_baseChange [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f F) ∧
      ∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
        {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
        (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))),
        IsIso (derivedBaseChangeComp f (Spec.map (CommRingCat.ofHom φ)) f' g hsq.w
            (DerivedCategory.Q.obj (singleDegreeComplex F))
            (DerivedCategory.Q.obj
              ((pullbackComplex g.toLRSHom.toShHom).obj (singleDegreeComplex F)))
            ((derivedPullbackNatTrans g.toLRSHom.toShHom).app (singleDegreeComplex F))) ∧
          ∀ {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens)
            (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
            (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))),
            haveI : F.IsQuasicoherent :=
              (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
            IsIso (derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff) := by
  have hFq : F.IsQuasicoherent := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  refine ⟨isPerfect_derivedGlobalSections f F hflat, fun φ X' f' g hsq => ⟨?_, ?_⟩⟩
  · exact ProperFlatFibreEulerCharacteristic.isIso_derivedBaseChangeComp_singleDegree hsq F hFq
      (@AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace
        X.toRingedSpace g.toLRSHom.toShHom F hFq) hflat
  · intro I _ _ U hU hUaff haff
    exact isIso_derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff hflat

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
