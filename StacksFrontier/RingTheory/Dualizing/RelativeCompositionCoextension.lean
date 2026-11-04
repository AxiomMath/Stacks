module

public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.RingTheory.Dualizing.RelativeComposition
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange

/-!
# Derived coextension of scalars along the base change of the diagonal

Let `R → A → B` be ring maps with `B` flat over `A` and write `D = A ⊗[R] A`, `C = B ⊗[R] B`,
`C' = B ⊗[A] B`.  The surjection `Dualizing.diagonalQuotient : C → C'` is the base change of the
diagonal `Δ : D → A` along the flat map of diagonals `δ : D → C`
(`Dualizing.diagonalQuotient_comp_diagonalBaseMap`, `Dualizing.diagonalPushoutEquiv`,
`Dualizing.flat_diagonalBaseMap`).

This file proves that **derived coextension of scalars commutes with that base change**: derived
Hom along `Dualizing.diagonalQuotient`, restricted from `C'` to `A`, is derived Hom along the
diagonal `Δ` applied to the restriction from `C` to `D`.

Both functors are right adjoints -- the first of `Ext_{A → C'} ⋙ Res_{C → C'}`, the second of
`Res_{D → A} ⋙ Ext_{D → C}` -- and those two left adjoints are identified by the derived
base-change comparison of [stacks 065Z], which is invertible here by [stacks 0661] because `C` is
flat over `D`.  So this is the comparison of right adjoints induced by an isomorphism of their
left adjoints, and it is invertible for that reason alone: no finiteness hypothesis, no
Tor-amplitude bound, no choice of representative and no projection formula enters.

## Main results

* `Dualizing.isPushout_diagonalQuotient` -- `C' = A ⊗[D] C` as a pushout of algebras, which is
  `Dualizing.diagonalPushoutEquiv` read as `Algebra.IsPushout`.
* `Dualizing.torIndependent_diagonalBaseMap` -- `A` and `C` are Tor independent over `D`, because
  `C` is flat over `D`.
* `Dualizing.nonempty_diagonalBaseChangeExtensionIso` -- **[stacks 0661] at the diagonal square**:
  the derived base-change comparison `Res_{D → A} ⋙ Ext_{D → C} ≅ Ext_{A → C'} ⋙ Res_{C → C'}`.
* `Dualizing.nonempty_diagonalBaseChangeExtensionIsoFlip` -- the same at the transposed square,
  `Res_{D → C} ⋙ Ext_{D → A} ≅ Ext_{C → C'} ⋙ Res_{A → C'}`.
* `Dualizing.nonempty_restrictDerivedHomDiagonalQuotientIso` -- **the main result**:
  `Res_{A → C'} ∘ RHom_C(C', -) ≅ RHom_D(A, -) ∘ Res_{D → C}`.
* `Dualizing.nonempty_restrictDerivedHomDiagonalQuotientObjIso` -- the main result at an object.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

section Algebraic

attribute [local instance] diagonalAlgebra diagonalAlgebraSelf diagonalQuotientAlgebra
  diagonalAlgebraQuot diagonalIsScalarTower diagonalIsScalarTowerSelf
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The structure map `A → B ⊗[A] B` is the left coprojection precomposed with `A → B`. -/
theorem algebraMap_eq_includeLeft_comp :
    (algebraMap A (B ⊗[A] B)) =
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B).comp (algebraMap A B) :=
  RingHom.ext fun _ => rfl

variable [Module.Flat A B]

/-- `C = B ⊗[R] B` is flat over the diagonal `D = A ⊗[R] A`, by
`Dualizing.flat_diagonalBaseMap`. -/
theorem flat_diagonalAlgebra : Module.Flat (A ⊗[R] A) (B ⊗[R] B) := by
  have h := flat_diagonalBaseMap R A B
  rwa [RingHom.Flat, show (diagonalBaseMap R A B).toRingHom.toAlgebra =
    diagonalAlgebra R A B from Algebra.algebra_ext _ _ fun _ => rfl] at h

omit [Module.Flat A B] in
/-- **`C' = A ⊗[D] C` as a pushout of algebras.**  This is `Dualizing.diagonalPushoutEquiv` read
through `Algebra.IsPushout.of_equiv`: the standard square of `A ⊗[D] C` is a pushout, and the
diagonal pushout equivalence identifies it with `C'` compatibly with the structure map of `C`. -/
theorem isPushout_diagonalQuotient :
    Algebra.IsPushout (A ⊗[R] A) A (B ⊗[R] B) (B ⊗[A] B) := by
  refine Algebra.IsPushout.of_equiv (R := A ⊗[R] A) (R' := A) (S := B ⊗[R] B)
    (diagonalPushoutEquiv R A B) (RingHom.ext fun x => ?_)
  show diagonalPushoutEquiv R A B ((1 : A) ⊗ₜ[A ⊗[R] A] x) = diagonalQuotient R A B x
  rw [diagonalPushoutEquiv_tmul, map_one, Algebra.TensorProduct.one_def.symm, one_mul]

/-- **`A` and `C` are Tor independent over `D`**, because `C` is flat over `D`. -/
theorem torIndependent_diagonalBaseMap :
    RingTheory.TorIndependence.TorIndependent (A ⊗[R] A) A (B ⊗[R] B) := by
  have := flat_diagonalAlgebra R A B
  exact torIndependent_of_flat_right

end Algebraic

section Derived

attribute [local instance] diagonalAlgebra diagonalAlgebraSelf diagonalQuotientAlgebra
  diagonalAlgebraQuot diagonalIsScalarTower diagonalIsScalarTowerSelf

variable [Module.Flat A B]

/-- [stacks 0661] for a pushout square with Tor independent corners: derived extension along
`R → R'` after restriction along `R → A` is restriction along `R' → A'` after derived extension
along `A → A'`. -/
private theorem nonempty_restrictExtensionIso_of_torIndependent
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra.IsPushout R A R' A']
    (hTor : RingTheory.TorIndependence.TorIndependent R A R') :
    Nonempty ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
          (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ≅
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory) := by
  let Dg := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  let Dh := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  have hiso :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u,
        u, u} R A R' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTor
      Dg.functor Dh.functor Dg.comparison Dh.comparison Dg.isLeftDerived Dh.isLeftDerived
  exact ⟨@asIso _ _ _ _ _ hiso⟩

/-- **[stacks 0661] at the diagonal square.**  Derived extension of scalars along the map of
diagonals `δ : D → C`, applied to the restriction of an object of `D(A)` along the diagonal
`Δ : D → A`, is the restriction along `Dualizing.diagonalQuotient` of its derived extension along
`A → C'`.

The square is a pushout by `Dualizing.isPushout_diagonalQuotient` and `A` and `C` are Tor
independent over `D` by `Dualizing.torIndependent_diagonalBaseMap`, so this is [stacks 0661] at
the canonical models of the two derived extensions. -/
theorem nonempty_diagonalBaseChangeExtensionIso :
    Nonempty ((ModuleCat.restrictScalars.{u}
            (algebraMap (A ⊗[R] A) A)).mapDerivedCategory ⋙
          (totalDerivedExtensionScalars.{u, u, u}
            (algebraMap (A ⊗[R] A) (B ⊗[R] B))).functor ≅
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A (B ⊗[A] B))).functor ⋙
          (ModuleCat.restrictScalars.{u}
            (algebraMap (B ⊗[R] B) (B ⊗[A] B))).mapDerivedCategory) := by
  have := isPushout_diagonalQuotient R A B
  exact nonempty_restrictExtensionIso_of_torIndependent (torIndependent_diagonalBaseMap R A B)

/-- **Derived coextension of scalars commutes with the base change of the diagonal.**  Writing
`D = A ⊗[R] A`, `C = B ⊗[R] B`, `C' = B ⊗[A] B`, `Δ : D → A` for the diagonal,
`δ : D → C` for the map of diagonals and `q : C → C'` for `Dualizing.diagonalQuotient`:

`RHom_C(C', W)|_A ≅ RHom_D(A, W|_D)`

naturally in `W` in `D(C)`.

Both sides are right adjoints -- the left-hand one of `Ext_{A → C'} ⋙ Res_q` by [stacks 0GMT]
and [stacks 0A70] composed, the right-hand one of `Res_Δ ⋙ Ext_δ` by the same two tags composed
the other way round -- and those two left adjoints are identified by
`Dualizing.nonempty_diagonalBaseChangeExtensionIso`, which is [stacks 0661] at the diagonal
square.  So this is the comparison of right adjoints induced by an isomorphism of their left
adjoints, and it is invertible for that reason alone: no finiteness hypothesis, no Tor-amplitude
bound, no choice of representative and no projection formula enters. -/
theorem nonempty_restrictDerivedHomDiagonalQuotientIso :
    Nonempty (derivedHom.{u, u, u} (algebraMap (B ⊗[R] B) (B ⊗[A] B)) ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap A (B ⊗[A] B))).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u}
            (algebraMap (A ⊗[R] A) (B ⊗[R] B))).mapDerivedCategory ⋙
          derivedHom.{u, u, u} (algebraMap (A ⊗[R] A) A)) := by
  obtain ⟨adjq⟩ := restrictScalarsDerived_adj_derivedHom.{u, u, u}
    (algebraMap (B ⊗[R] B) (B ⊗[A] B))
  obtain ⟨adjd⟩ := restrictScalarsDerived_adj_derivedHom.{u, u, u} (algebraMap (A ⊗[R] A) A)
  obtain ⟨e⟩ := nonempty_diagonalBaseChangeExtensionIso R A B
  let Dp := totalDerivedExtensionScalars.{u, u, u} (algebraMap A (B ⊗[A] B))
  let Dd := totalDerivedExtensionScalars.{u, u, u} (algebraMap (A ⊗[R] A) (B ⊗[R] B))
  have aEp : Dp.functor ⊣
      (ModuleCat.restrictScalars.{u} (algebraMap A (B ⊗[A] B))).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} A (B ⊗[A] B) _ _
      (algebraMap A (B ⊗[A] B)) _ _ Dp.functor Dp.comparison Dp.isLeftDerived
  have aEd : Dd.functor ⊣
      (ModuleCat.restrictScalars.{u}
        (algebraMap (A ⊗[R] A) (B ⊗[R] B))).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} (A ⊗[R] A) (B ⊗[R] B) _ _
      (algebraMap (A ⊗[R] A) (B ⊗[R] B)) _ _ Dd.functor Dd.comparison Dd.isLeftDerived
  exact ⟨Adjunction.rightAdjointUniq (aEp.comp adjq) ((adjd.comp aEd).ofNatIsoLeft e)⟩

/-- **[stacks 0661] at the diagonal square, read the other way round.**  Derived extension of
scalars along the diagonal `Δ : D → A`, applied to the restriction of an object of `D(C)` along
the map of diagonals `δ : D → C`, is the restriction along `A → C'` of its derived extension
along `Dualizing.diagonalQuotient`.

This is `Dualizing.nonempty_diagonalBaseChangeExtensionIso` at the transposed square, where the
Tor-independence input is flatness of `C` over `D` read on the left. -/
theorem nonempty_diagonalBaseChangeExtensionIsoFlip :
    Nonempty ((ModuleCat.restrictScalars.{u}
            (algebraMap (A ⊗[R] A) (B ⊗[R] B))).mapDerivedCategory ⋙
          (totalDerivedExtensionScalars.{u, u, u} (algebraMap (A ⊗[R] A) A)).functor ≅
        (totalDerivedExtensionScalars.{u, u, u}
            (algebraMap (B ⊗[R] B) (B ⊗[A] B))).functor ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap A (B ⊗[A] B))).mapDerivedCategory) := by
  have := (isPushout_diagonalQuotient R A B).symm
  have := flat_diagonalAlgebra R A B
  exact nonempty_restrictExtensionIso_of_torIndependent
    RingTheory.TorIndependence.torIndependent_of_flat_left

/-- **Derived coextension of scalars along the base change of the diagonal, at an object.**  The
value at `W` of `Dualizing.nonempty_restrictDerivedHomDiagonalQuotientIso`:

`RHom_C(C', W)|_A ≅ RHom_D(A, W|_D)`. -/
theorem nonempty_restrictDerivedHomDiagonalQuotientObjIso
    (W : DerivedCategory (ModuleCat.{u} (B ⊗[R] B))) :
    Nonempty ((ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} (algebraMap (B ⊗[R] B) (B ⊗[A] B))).obj W) ≅
        (derivedHom.{u, u, u} (algebraMap (A ⊗[R] A) A)).obj
          ((ModuleCat.restrictScalars.{u}
            (algebraMap (A ⊗[R] A) (B ⊗[R] B))).mapDerivedCategory.obj W)) :=
  ⟨(nonempty_restrictDerivedHomDiagonalQuotientIso R A B).some.app W⟩

end Derived

end

end Dualizing

end
