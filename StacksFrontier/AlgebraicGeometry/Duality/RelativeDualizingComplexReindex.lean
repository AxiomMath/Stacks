module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseOpen

/-!
# Changing the morphism under a diagonal open

A diagonal open `W` of `h : X ⟶ T` (Stacks 0E2T) consists of an open `W` with an open immersion
`ι : W ⟶ X ×_T X` and a closed immersion `Δ : X ⟶ W` factoring the relative diagonal. If
`h₂ : X ⟶ T₂` is a second morphism and `ι₂ : W ⟶ X ×_{T₂} X` is an open immersion with
`Δ ≫ ι₂` the relative diagonal of `h₂`, then `(W, ι₂, Δ)` is a diagonal open of `h₂`. The map
`Δ_*𝒪_X ⟶ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)` defined by a morphism `ξ` (Stacks 0E2T) only sees
`W`, `Δ` and the first projection, so it is an isomorphism for one diagonal open exactly when it
is for the other, once the first projections agree.

For `h = a ≫ j` with `j : V ⟶ T` a monomorphism, `X ×_T X ≅ X ×_V X`, so a diagonal open of `h`
is one of `a` with the same open, the same diagonal and the same first projection.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.withIota`: the diagonal open `(W, ι₂, Δ)` of `h₂`
  built from a diagonal open `(W, ι, Δ)` of `h`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.pullbackFactorIso`: the isomorphism
  `X ×_T X ≅ X ×_V X` for `h = a ≫ j` with `j` a monomorphism.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.reindex`: a diagonal open of `h = a ≫ j` as one of
  `a`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_iff_of_proj_eq`: the map
  defined by `ξ` is an isomorphism for a first projection equal to that of `D` exactly when it is
  for `D` itself.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.reindex_proj`: `D.reindex a j e` has the same first
  projection as `D`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard

variable {X T T₂ : Scheme.{u}} {h : X ⟶ T}

/-- The diagonal open `(W, ι₂, Δ)` of `h₂` built from a diagonal open `(W, ι, Δ)` of `h` and an
open immersion `ι₂ : W ⟶ X ×_{T₂} X` with `Δ ≫ ι₂` the relative diagonal of `h₂`. -/
abbrev withIota (D : DiagonalOpen h) {h₂ : X ⟶ T₂} (ι₂ : D.W ⟶ pullback h₂ h₂)
    [IsOpenImmersion ι₂] (fac₂ : D.diag ≫ ι₂ = pullback.diagonal h₂) : DiagonalOpen h₂ where
  W := D.W
  ι := ι₂
  isOpenImmersion := inferInstance
  diag := D.diag
  isClosedImmersion := D.isClosedImmersion
  fac := fac₂

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- For a first projection `p` equal to that of `D`, the map defined by `ξ` is an isomorphism
exactly when `D.diagonalAction K ξ'` is. -/
theorem isIso_diagonalAction_iff_of_proj_eq (D : DiagonalOpen h)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (p : D.W ⟶ X) (hp : p = D.proj)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackAlong p K)
    (ξ' : D.diagonalObject ⟶ D.derivedPullbackProj K) (hξ : HEq ξ ξ') :
    IsIso ((Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackAlong p K)).symm
      (Stacks.RelativeSpec.AlgebraSheaf.derivedMul D.diagonalAlgebra ≫ ξ)) ↔
      IsIso (D.diagonalAction K ξ') := by
  subst hp
  cases hξ
  unfold diagonalAction
  constructor <;> intro h' <;> convert h' using 2

variable {V : Scheme.{u}}

/-- `X ×_T X ≅ X ×_V X` for `h = a ≫ j` with `j : V ⟶ T` a monomorphism. -/
def pullbackFactorIso (a : X ⟶ V) (j : V ⟶ T) [Mono j] (e : h = a ≫ j) :
    pullback h h ≅ pullback a a where
  hom := pullback.lift (pullback.fst h h) (pullback.snd h h)
    ((cancel_mono j).1 (by rw [Category.assoc, Category.assoc, ← e, pullback.condition]))
  inv := pullback.lift (pullback.fst a a) (pullback.snd a a) (by
    rw [e, ← Category.assoc, pullback.condition, Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

/-- A diagonal open of `h` read as one of `a`, for `h = a ≫ j` with `j` a monomorphism: the same
open and the same diagonal, through `X ×_T X ≅ X ×_V X`. -/
abbrev reindex (D : DiagonalOpen h) (a : X ⟶ V) (j : V ⟶ T) [Mono j] (e : h = a ≫ j) :
    DiagonalOpen a :=
  have := D.isOpenImmersion
  D.withIota (D.ι ≫ (pullbackFactorIso a j e).hom) (by
    rw [← Category.assoc, D.fac]
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackFactorIso, pullback.lift_fst, pullback.diagonal_fst,
        pullback.diagonal_fst]
    · rw [Category.assoc, pullbackFactorIso, pullback.lift_snd, pullback.diagonal_snd,
        pullback.diagonal_snd])

/-- The first projection of `D.reindex a j e` is that of `D`. -/
theorem reindex_proj (D : DiagonalOpen h) (a : X ⟶ V) (j : V ⟶ T) [Mono j] (e : h = a ≫ j) :
    (D.reindex a j e).proj = D.proj := by
  show (D.ι ≫ (pullbackFactorIso a j e).hom) ≫ pullback.fst a a = D.ι ≫ pullback.fst h h
  rw [Category.assoc, pullbackFactorIso, pullback.lift_fst]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
