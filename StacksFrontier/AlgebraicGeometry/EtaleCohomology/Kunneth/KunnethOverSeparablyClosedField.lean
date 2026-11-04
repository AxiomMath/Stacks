module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Künneth over a separably closed field, through the projection formula and base change

Let `k` be a separably closed field, `X` and `Y` schemes of finite type over `k`, and `n ≥ 1`
invertible in `k`. [Stacks, Tag 0F1P] identifies, for `E ∈ D(X_étale, ℤ/nℤ)` and
`K ∈ D(Y_étale, ℤ/nℤ)`,

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K) = RΓ(X, E) ⊗^L RΓ(Y, K)`.

The proof of the source is two canonical maps in a row. Write `f : X ⟶ Spec k` and
`g : Y ⟶ Spec k`. [Stacks, Tag 0F1N], at the square with `S' = Spec k` and `T = Y`, is the
isomorphism `E ⊗^L f⁻¹Rg_*K ≅ Rpr₁_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)`. Then [Stacks, Tag 0F12] pulls the
constant factor `f⁻¹Rg_*K = RΓ(Y, K)` out of `RΓ(X, -)`.

This file builds that composite for an arbitrary commutative square of schemes, on the derived
categories `D(-_étale, Λ)` of `Stacks.EtaleCohomology.EtaleCoefficients`, and states the case of
the source. It is the map

`Rf_*E ⊗^L Rg_*K ⟶ Rf_*(E ⊗^L f⁻¹Rg_*K) ⟶ Rf_*Rp_*(p⁻¹E ⊗^L q⁻¹K) ≅ R(p ≫ f)_*(p⁻¹E ⊗^L q⁻¹K)`.

Its first arrow is the projection formula map (Stacks 0B56), the second is `Rf_*` of the canonical
map of Tags 0F1J and 0F1N, and the third is the composition of derived direct images.

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `pushforwardCompIsoOfAdjunction` — `Rp_* ⋙ Rf_* ≅ R(p ≫ f)_*`, the conjugate of the isomorphism
  `f⁻¹ ⋙ p⁻¹ ≅ (p ≫ f)⁻¹` of composite inverse images.
* `projectionFormulaMap` — the projection formula map `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L f⁻¹K)`.
* `kunnethMapOfBaseChange` — the composite above, for a commutative square `p ≫ f = q ≫ g`.
* `kunnethOverFieldMap` — its case for the fibre square of two schemes over `Spec k`.

## Main results

* `isIso_kunnethMapOfBaseChange` — the composite is invertible when its two non-trivial arrows
  are.
* `isIso_kunnethOverFieldMap` — the situation of [Stacks, Tag 0F1P]: the map is invertible
  given the projection formula of Tag 0F12 and the base change isomorphism of Tag 0F1N, at the
  two objects at which the source's proof uses them.

## Implementation notes

*What is not proved.* [Stacks, Tag 0F1P] is not registered here, because its proof needs two
results that are not available unconditionally.
* [Stacks, Tag 0F1N] goes through Tag 0F1J. That uses Tag 0F0G (proper base change) and
  Tag 0F1I, whose proof uses Tag 0F1H, which in turn uses the smooth base change chain
  (Tags 0F09 and 0F1C).
* [Stacks, Tag 0F12] needs `cd(X) < ∞`. That is Tag 0F10, through Tag 0F0V.

So `isIso_kunnethOverFieldMap` takes the two instances as explicit hypotheses `hprojection` and
`hbaseChange`. These are the exact maps the source's proof shows invertible: the projection
formula map at `(E, Rg_*K)`, and the canonical map of Tag 0F1N at `(E, K)`, with `S' = Spec k`
and `p = 𝟙 X`, so that `p⁻¹E` is `E`.

*Where `RΓ` lands.* The source reads both sides in `D(ℤ/nℤ)`. Here they are read in
`D((Spec k)_étale, ℤ/nℤ)`, as `Rf_*`, `Rg_*` and `R(pr₁ ≫ f)_*` with `⊗^L` on `Spec k`. For `k`
separably closed that category is `D(ℤ/nℤ)`: the equivalence is
`Stacks.EtaleCohomology.EtaleCoefficients.derivedModulesEquivOfSepClosed`, and it is compatible
with `⊗^L` (`Stacks.EtaleCohomology.EtaleCoefficients.derivedModulesEquivOfSepClosedTensorIso`).

*Relation to the Künneth map of Tag 0F1E.* The map of this file is the one the proof of
Tag 0F1P builds. It agrees with `Stacks.EtaleCohomology.EtaleCoefficients.kunnethMap`:
`Stacks.EtaleCohomology.EtaleCoefficients.kunnethMapOfBaseChange_eq_kunnethMap` and
`kunnethOverFieldMap_eq_kunnethMap`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.KunnethOverFieldMapComparison`, from the
composition law of the comparison `c⁻¹(M ⊗^L N) ≅ c⁻¹M ⊗^L c⁻¹N` (Stacks 07A4) along
`pullbackCompIso`.

*Coefficients.* `Λ` lives in `Type (u + 1)`, the universe of the small model of the étale site,
so `ℤ/nℤ` enters as `ULift.{u + 1} (ZMod n)`.

## References

* [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P)
* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

section Square

variable {W X Y S : Scheme.{u}}

/-- **The composite derived direct image**, `Rp_* ⋙ Rf_* ≅ R(p ≫ f)_*`: the conjugate, for the
adjunctions `f⁻¹ ⋙ p⁻¹ ⊣ Rp_* ⋙ Rf_*` and `(p ≫ f)⁻¹ ⊣ R(p ≫ f)_*`, of the isomorphism
`pullbackCompIso` of composite inverse images. -/
def pushforwardCompIsoOfAdjunction (p : W ⟶ X) (f : X ⟶ S) :
    pushforward Λ p ⋙ pushforward Λ f ≅ pushforward Λ (p ≫ f) :=
  conjugateIsoEquiv ((adjunction Λ f).comp (adjunction Λ p)) (adjunction Λ (p ≫ f))
    (pullbackCompIso Λ p f).symm

/-- **The projection formula map** `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` on `D(-_étale, Λ)`
(Stacks 0B56): the adjoint of the comparison `f⁻¹(Rf_*E ⊗^L K) ≅ f⁻¹Rf_*E ⊗^L f⁻¹K` of
Stacks 07A4, followed by the counit `f⁻¹Rf_*E ⟶ E` in the first factor. -/
def projectionFormulaMap (f : X ⟶ S) (E : DerivedModules Λ X) (K : DerivedModules Λ S) :
    ((tensor Λ S).obj ((pushforward Λ f).obj E)).obj K ⟶
      (pushforward Λ f).obj (((tensor Λ X).obj E).obj ((pullback Λ f).obj K)) :=
  Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap (ringedToposHom Λ f)
    (isMorphismOfSites_ringedToposHom Λ f) E K

/-- **The Künneth map through the projection formula and base change.** For a commutative
square `p ≫ f = q ≫ g` of schemes, `E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`, the composite

`Rf_*E ⊗^L Rg_*K ⟶ Rf_*(E ⊗^L f⁻¹Rg_*K) ⟶ Rf_*Rp_*(p⁻¹E ⊗^L q⁻¹K) ≅ R(p ≫ f)_*(p⁻¹E ⊗^L q⁻¹K)`

of the projection formula map, `Rf_*` of the canonical map of Tags 0F1J and 0F1N, and the
composition of direct images. This is the map the proof of [Stacks, Tag 0F1P] builds. -/
def kunnethMapOfBaseChange (p : W ⟶ X) (f : X ⟶ S) (q : W ⟶ Y) (g : Y ⟶ S) (w : p ≫ f = q ≫ g)
    (E : DerivedModules Λ X) (K : DerivedModules Λ Y) :
    ((tensor Λ S).obj ((pushforward Λ f).obj E)).obj ((pushforward Λ g).obj K) ⟶
      (pushforward Λ (p ≫ f)).obj (((tensor Λ W).obj ((pullback Λ p).obj E)).obj
        ((pullback Λ q).obj K)) :=
  projectionFormulaMap Λ f E ((pushforward Λ g).obj K) ≫
    (pushforward Λ f).map (tensorBaseChangeMap Λ f g p q w E K) ≫
      (pushforwardCompIsoOfAdjunction Λ p f).hom.app _

/-- The Künneth map through the projection formula and base change is invertible when the
projection formula map at `(E, Rg_*K)` and the canonical map of Tags 0F1J and 0F1N at `(E, K)`
are. -/
theorem isIso_kunnethMapOfBaseChange (p : W ⟶ X) (f : X ⟶ S) (q : W ⟶ Y) (g : Y ⟶ S)
    (w : p ≫ f = q ≫ g) (E : DerivedModules Λ X) (K : DerivedModules Λ Y)
    (hprojection : IsIso (projectionFormulaMap Λ f E ((pushforward Λ g).obj K)))
    (hbaseChange : IsIso (tensorBaseChangeMap Λ f g p q w E K)) :
    IsIso (kunnethMapOfBaseChange Λ p f q g w E K) := by
  unfold kunnethMapOfBaseChange
  infer_instance

end Square

section SeparablyClosedField

variable (k : Type u) [Field k] {X Y : Scheme.{u}}

/-- **The Künneth map of [Stacks, Tag 0F1P]** on `D(-_étale, Λ)`: for schemes
`f : X ⟶ Spec k` and `g : Y ⟶ Spec k`, `E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`, the map

`Rf_*E ⊗^L_Λ Rg_*K ⟶ R(pr₁ ≫ f)_*(pr₁⁻¹E ⊗^L_Λ pr₂⁻¹K)`

of `kunnethMapOfBaseChange` at the fibre square of `X ×_k Y`. Over a separably closed field `k`
its source is `RΓ(X, E) ⊗^L RΓ(Y, K)` and its target `RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K)`, both read
in `D((Spec k)_étale, Λ)`. -/
def kunnethOverFieldMap (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (E : DerivedModules Λ X)
    (K : DerivedModules Λ Y) :
    ((tensor Λ (Spec (.of k))).obj ((pushforward Λ f).obj E)).obj ((pushforward Λ g).obj K) ⟶
      (pushforward Λ (pullback.fst f g ≫ f)).obj
        (((tensor Λ (Limits.pullback f g)).obj
          ((pullback Λ (Limits.pullback.fst f g)).obj E)).obj
            ((pullback Λ (Limits.pullback.snd f g)).obj K)) :=
  kunnethMapOfBaseChange Λ (Limits.pullback.fst f g) f (Limits.pullback.snd f g) g
    Limits.pullback.condition E K

/-- **[Stacks, Tag 0F1P], given Tags 0F1N and 0F12.** Let `k` be a separably closed field, let
`X` and `Y` be schemes of finite type over `k`, and let `n ≥ 1` be invertible in `k`. For
`E ∈ D(X_étale, ℤ/nℤ)` and `K ∈ D(Y_étale, ℤ/nℤ)` the Künneth map

`RΓ(X, E) ⊗^L_{ℤ/nℤ} RΓ(Y, K) ⟶ RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_{ℤ/nℤ} pr₂⁻¹K)`

is an isomorphism, `RΓ` being read in `D((Spec k)_étale, ℤ/nℤ)`.

The hypotheses `hprojection` and `hbaseChange` are the two results the source's proof uses,
at the objects where it uses them. `hprojection` is the projection formula of [Stacks,
Tag 0F12] for `f`, at `E` and `Rg_*K`; its proof needs `cd(X) < ∞`, which is [Stacks,
Tag 0F10]. `hbaseChange` is [Stacks, Tag 0F1N] at the square with `S' = Spec k` and `T = Y`.
Neither is available unconditionally (see the implementation notes of the module). The other
hypotheses are those of the source; the composite is invertible as soon as its two arrows are. -/
theorem isIso_kunnethOverFieldMap [IsSepClosed k] (n : ℕ) [NeZero n] (_hn : IsUnit (n : k))
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X) (K : DerivedModules (ULift.{u + 1} (ZMod n)) Y)
    (hprojection : IsIso (projectionFormulaMap (ULift.{u + 1} (ZMod n)) f E
      ((pushforward (ULift.{u + 1} (ZMod n)) g).obj K)))
    (hbaseChange : IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f g
      (Limits.pullback.fst f g) (Limits.pullback.snd f g) Limits.pullback.condition E K)) :
    IsIso (kunnethOverFieldMap (ULift.{u + 1} (ZMod n)) k f g E K) :=
  isIso_kunnethMapOfBaseChange _ _ _ _ _ _ E K hprojection hbaseChange

end SeparablyClosedField

end Stacks.EtaleCohomology.EtaleCoefficients

end
