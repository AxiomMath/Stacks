module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteBaseChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriek
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmallOfModules
public import StacksFrontier.Cotangent.ResolutionTorBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Localization and the cotangent complex: `L_{B/A} = L_{B/A'}`

Let `A → A' → B` be ring maps. Extension of scalars `P ↦ A' ⊗_A P` carries a polynomial
`A`-algebra augmented to `B` to a polynomial `A'`-algebra augmented to `B`, and so defines the
functor
```
u : C_{B/A} ⟶ C_{B/A'},   (P → B) ↦ (A' ⊗_A P → B)
```
of Stacks 08QN, the one along which the comparison of Stacks 08QP is taken.

The first half of this file proves the step of Stacks 08QZ which carries all of its
differential-geometric content: the sheaf `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` on `C_{B/A}` is the
pullback along `u` of the sheaf `i^*Ω_{𝒪/A'}` on `C_{B/A'}`, which amounts to the identification
```
Ω_{P/A} ⊗_P B = Ω_{(A' ⊗_A P)/A'} ⊗_{A' ⊗_A P} B
```
natural in the augmented algebra `(P → B)`.

The second half draws the conclusion of Stacks 08QZ from it: if `B = B ⊗_A^𝐋 A'`, then
`L_{B/A}` and `L_{B/A'}` have the same cohomology in every degree, as `B`-modules. The two sides
are read on two different resolutions of `B` over `A'` — the base change `A' ⊗_A P_•` of the
standard resolution of `B` over `A`, which the hypothesis makes a resolution, and the standard
resolution of `B` over `A'` — and Tag 08PT computes the same `L_nπ_!(Ω_{𝒪/A'} ⊗_𝒪 B̲)` from
either.

The identification is Stacks 00RV, in the form
`KaehlerDifferential.tensorKaehlerEquiv : (A' ⊗_A P) ⊗_P Ω[P⁄A] ≅ Ω[(A' ⊗_A P)⁄A']`, followed by
cancellation of the base change along `P → A' ⊗_A P → B`. The source argues instead that
`Ω_{P/A}` is free because `P` is a polynomial algebra, which identifies
`Ω_{P/A} ⊗_A A' ⊗_{A' ⊗_A P} B` with `Ω_{P/A} ⊗_P B`; no freeness is needed for the form of
Stacks 00RV used here, so the comparison below holds for an arbitrary `A`-algebra augmented to
`B`, polynomial or not.

## Main definitions

* `Stacks.KaehlerDifferential.augmentationBaseChangeEquiv`: the ring-theoretic identification
  `B ⊗_{A' ⊗_A P} Ω[(A' ⊗_A P)⁄A'] ≅ B ⊗_P Ω[P⁄A]` for an `A'`-algebra `B` under `A' ⊗_A P`,
  Stacks 00RV base changed along the augmentation.
* `CommAlgCat.midAlgebra`: `B` read as an algebra over the intermediate ring `A'`.
* `CommAlgCat.midBaseChangeOver`: the functor `(P → B) ↦ (A' ⊗_A P → B)` on augmented algebras,
  i.e. `CommAlgCat.baseChangeOver` for the square of the tower `A → A' → B`.
* `CommAlgCat.midSimplicialBaseChange` and `CommAlgCat.midAugmentationBaseChange`: the base
  change `A' ⊗_A P_•` of a simplicial `A`-algebra augmented to `B`, and its augmentation
  `a' ⊗ p ↦ a' · ε(p)` (`CommAlgCat.midAugmentationBaseChange_app_tmul`).
* `CommAlgCat.midResolutionVarCardinal`: a cardinal bounding the variables of the terms of both
  resolutions of `B` over `A'` that the proof compares.

## Main results

* `Stacks.KaehlerDifferential.augmentationBaseChangeEquiv_tmul_D`: the identification sends the
  pure differential `1 ⊗ d(1 ⊗ p)` to `1 ⊗ d p`; this pins it down, since the pure differentials
  generate.
* `CommAlgCat.midBaseChangeOverDifferentialsIso`: **the step of Stacks 08QZ that the proof of
  the tag turns on**: `i^*Ω_{𝒪/A} = u^{-1}(i^*Ω_{𝒪/A'})`, as an isomorphism of functors on the
  category of `A`-algebras augmented to `B`, natural in the augmented algebra.
* `CommAlgCat.midBaseChangeOverDifferentialsIsoApp_hom_mk`: its value on a pure differential.
* `CommAlgCat.resolutionModuleLeftDerivedCotangentHomologyIso`: the module half of Tag 08PS for
  an *arbitrary* bounded resolution, at the sheaf `i^*Ω_{𝒪/A}` — the sections at the point of
  `L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the degree `n` homology of the complex of
  `Ω_{P_•/A} ⊗_{P_•} B`, as `B`-modules. Since the left-hand side does not mention the
  resolution, this is what makes two resolutions of one ring map comparable.
* `CommAlgCat.cotangentComplexHomologyMooreIso`: the cohomology of `L_{B/A}` in degree `-n` is the
  degree `n` homology of the complex of `Ω_{P_•/A} ⊗_{P_•} B` for the standard resolution.
* `CommAlgCat.midCotangentComplexHomologyIso`: **Stacks 08QZ degreewise**, the cohomology of
  `L_{B/A}` and of `L_{B/A'}` agrees in every degree as `B`-modules, under the tag's own
  hypothesis `B = B ⊗_A^𝐋 A'`. The tag's own conclusion, `L_{B/A} = L_{B/A'}` in `D(B)`, is
  `CommAlgCat.midCotangentComplexDerivedIso` of
  `StacksFrontier/Cotangent/PolynomialAlgebraSiteBaseChangeDerived.lean`.

## Implementation notes

**The shape of the tower.** The tower `A → A' → B` is presented by a `CommAlgCat.{u} A` object
`B` together with `[Algebra A' (B : Type u)]` and `[IsScalarTower A A' (B : Type u)]`, and `B`
read over `A'` is `CommAlgCat.of A' (B : Type u)`. That presentation, rather than a bare ring
with two algebra structures, is what keeps the two categories `ModuleCat (B : Type u)` and
`ModuleCat (CommAlgCat.of A' B : Type u)` definitionally equal through the *same* instances: a
bare ring would offer a second route to `Algebra A' B`, and unifying the two routes inside the
tensor-product instances is prohibitively slow.

**The hypothesis is the source's, written out.** `B = B ⊗_A^𝐋 A'` is two conditions: the higher
Tor modules `Tor_i^A(A', B)` vanish, which is
`RingTheory.TorIndependence.TorIndependent A A' (B : Type u)`, and the degree-zero part
`A' ⊗_A B → B`, `a' ⊗ x ↦ a' · x`, is bijective — the map
`CommAlgCat.baseChangeUnit (AlgHom.id A (B : Type u))`. The second is not implied by the first:
for `A → A[x] → A[x]` the middle ring is flat over `A`, so all higher Tor vanish, while
`A[x] ⊗_A A[x] → A[x]` is not injective.

Those two conditions are exactly what
`CommAlgCat.isResolution_augmentationBaseChange` of
`StacksFrontier/Cotangent/ResolutionTorBaseChange.lean` consumes, for an arbitrary commutative
square of rings: it concludes
`IsResolution A' B' (simplicialBaseChange b ε) (augmentationBaseChange b ε)`, the first half of
the proof of Stacks 08QP. For the square of the tower — `B' = B` and `b` the identity — that is
`CommAlgCat.midSimplicialBaseChange` and `CommAlgCat.midAugmentationBaseChange`, which are that
module's two constructions for the identity map of `B`, definitionally; the proof below uses the
two spellings interchangeably. Of the two fields of the resolution property the base change gets
this way, only `trivialKanFibration` needs the hypothesis: `isPolynomialAlgebra` holds
unconditionally, by `CommAlgCat.isPolynomialAlgebraBelow_midSimplicialBaseChange`.

**Degreewise here; the source's isomorphism in `D(B)` is proved elsewhere.** The source states
the conclusion as an isomorphism in `D(B)`. What this file delivers is an isomorphism of the
cohomology objects in each degree, as `B`-modules, because the comparison of the two resolutions
of `B` over `A'` it uses — the module half of Tag 08PS,
`CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso` — identifies the degree `n`
functor `(Lπ_!)_n` with `H_n` of the Moore complex, one degree at a time. That is a property of
the comparison chosen here, not of the library: a `Lπ_!` valued in `D(B)` does exist, both as the
functor `D(𝒪) ⟶ D(B)` of Tag 09CZ
(`Stacks.ChaoticSite.derivedColimitWithCoefficients`) and, in the form this argument would want,
as Tag 08PU in `D(B)` for an arbitrary bounded resolution
(`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso`).

The source's conclusion is `CommAlgCat.midCotangentComplexDerivedIso` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteBaseChangeDerived.lean`: an isomorphism
`L_{B/A} ≅ L_{B/A'}` in `D(B)` whose underlying morphism is the canonical map of Tag 08PN
attached to the square of the tower. Degreewise isomorphisms in every degree would not produce
it; that statement is reached instead from Tag 08QQ at `B' = B`, whose carried hypothesis —
Remark 08QI — is `CommAlgCat.cotangentComputedByEveryResolution`. The degreewise statement below
is kept because it is proved directly from the two resolutions and does not pass through
Tag 08QQ.

**Why Tag 08PT twice, and not Tag 08QP.** The source invokes Stacks 08QP, which identifies
`Lπ_!(g^{-1}ℱ')` with `Lπ'_!(ℱ')` for an arbitrary abelian sheaf `ℱ'` on `C_{B/A'}`. Only one
sheaf is needed, `ℱ' = i^*Ω_{𝒪/A'}`, and for that one the identification is already visible in
Tag 08PT: the base change `A' ⊗_A P_•` of the standard resolution of `B` over `A` and the
standard resolution of `B` over `A'` are two resolutions of `B` over `A'`, and Tag 08PT computes
`L_nπ'_!(i^*Ω_{𝒪/A'})` from either, while the comparison of
`CommAlgCat.midBaseChangeOverDifferentialsIso` identifies the complex it produces from the first
with the complex of `L_{B/A}`. That is the route taken below. Going through Tag 08QP instead —
`CommAlgCat.leftDerivedPointLowerShriekPolynomialBaseChangeNatIso` of
`StacksFrontier/Cotangent/PolynomialSiteBaseChangeShriek.lean` — would additionally require
identifying `g^{-1}(i^*Ω_{𝒪/A'})` with `i^*Ω_{𝒪/A}` as abelian sheaves on the small models of the
restricted sites, and would reach the degreewise conclusion with the coefficients forgotten.

## References

* [Stacks Project, Tag 08QZ](https://stacks.math.columbia.edu/tag/08QZ)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
* [Stacks Project, Tag 00RV](https://stacks.math.columbia.edu/tag/00RV)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Stacks.KaehlerDifferential

variable (A A' P B : Type u) [CommRing A] [CommRing A'] [CommRing P] [CommRing B]
  [Algebra A A'] [Algebra A P] [Algebra A' B] [Algebra P B]
  [Algebra (A' ⊗[A] P) B] [IsScalarTower A' (A' ⊗[A] P) B] [IsScalarTower P (A' ⊗[A] P) B]

/-- **Stacks 00RV along an augmentation.** Let `A → A'` and `A → P` be ring maps and let `B` be
an algebra over `A' ⊗_A P`, compatibly with both factors. Then
```
B ⊗_{A' ⊗_A P} Ω[(A' ⊗_A P)⁄A'] ≅ B ⊗_P Ω[P⁄A] .
```
This is `KaehlerDifferential.tensorKaehlerEquiv`, which identifies `Ω[(A' ⊗_A P)⁄A']` with
`(A' ⊗_A P) ⊗_P Ω[P⁄A]`, followed by cancellation of the base change along
`P → A' ⊗_A P → B`. -/
def augmentationBaseChangeEquiv :
    B ⊗[A' ⊗[A] P] Ω[(A' ⊗[A] P)⁄A'] ≃ₗ[B] B ⊗[P] Ω[P⁄A] :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (KaehlerDifferential.tensorKaehlerEquiv A A' P (A' ⊗[A] P)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange P (A' ⊗[A] P) B B Ω[P⁄A]

omit [Algebra A' B] [IsScalarTower A' (A' ⊗[A] P) B] in
/-- The identification of `Stacks.KaehlerDifferential.augmentationBaseChangeEquiv` sends the pure
differential `1 ⊗ d(1 ⊗ p)` to the pure differential `1 ⊗ d p`. Since the pure differentials
generate, this pins the identification down. -/
theorem augmentationBaseChangeEquiv_tmul_D (p : P) :
    augmentationBaseChangeEquiv A A' P B
        ((1 : B) ⊗ₜ[A' ⊗[A] P] KaehlerDifferential.D A' (A' ⊗[A] P)
          (algebraMap P (A' ⊗[A] P) p)) =
      (1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p := by
  rw [Algebra.TensorProduct.right_algebraMap_apply]
  simp only [augmentationBaseChangeEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    KaehlerDifferential.tensorKaehlerEquiv_symm_D_tmul, map_one,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

omit [Algebra A' B] [IsScalarTower A' (A' ⊗[A] P) B] in
/-- The inverse of `Stacks.KaehlerDifferential.augmentationBaseChangeEquiv` sends the pure
differential `1 ⊗ d p` to the pure differential `1 ⊗ d(1 ⊗ p)`. -/
theorem augmentationBaseChangeEquiv_symm_tmul_D (p : P) :
    (augmentationBaseChangeEquiv A A' P B).symm ((1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p) =
      (1 : B) ⊗ₜ[A' ⊗[A] P] KaehlerDifferential.D A' (A' ⊗[A] P)
        (algebraMap P (A' ⊗[A] P) p) :=
  (LinearEquiv.symm_apply_eq _).2 (augmentationBaseChangeEquiv_tmul_D A A' P B p).symm

end Stacks.KaehlerDifferential

namespace CommAlgCat

variable {A : Type u} [CommRing A]

/-- The target of the tower `A → A' → B`, read as an algebra over the intermediate ring `A'`. -/
abbrev midAlgebra (A' : Type u) [CommRing A'] (B : CommAlgCat.{u} A)
    [Algebra A' (B : Type u)] : CommAlgCat.{u} A' :=
  CommAlgCat.of A' (B : Type u)

variable (A' : Type u) [CommRing A'] [Algebra A A'] (B : CommAlgCat.{u} A)
  [Algebra A' (B : Type u)] [IsScalarTower A A' (B : Type u)]

/-- **Stacks 08QZ**, the functor `u : C_{B/A} ⟶ C_{B/A'}` of the proof, on augmented algebras:
extension of scalars `(P → B) ↦ (A' ⊗_A P → B)` for the square of the tower `A → A' → B`. -/
abbrev midBaseChangeOver : Over B ⥤ Over (midAlgebra A' B) :=
  baseChangeOver (B' := midAlgebra A' B) (AlgHom.id A (B : Type u))

variable {A' B}

/-- The augmentation of the base-changed algebra sends `a' ⊗ p` to `a'` times the augmentation
of `p`. -/
private theorem midBaseChangeOver_augmentation_tmul (X : Over B) (a' : A')
    (p : (X.left : Type u)) :
    augmentationRingHom ((midBaseChangeOver A' B).obj X) (a' ⊗ₜ[A] p) =
      algebraMap A' (B : Type u) a' * augmentationRingHom X p :=
  baseChangeAugmentation_tmul (B' := midAlgebra A' B) (AlgHom.id A (B : Type u)) X a' p

/-- The augmentation of the base-changed algebra sends `1 ⊗ p` to the augmentation of `p`. -/
theorem midBaseChangeOver_augmentation_algebraMap (X : Over B) (p : (X.left : Type u)) :
    augmentationRingHom ((midBaseChangeOver A' B).obj X)
        (algebraMap (X.left : Type u) (A' ⊗[A] (X.left : Type u)) p) =
      augmentationRingHom X p := by
  rw [Algebra.TensorProduct.right_algebraMap_apply, midBaseChangeOver_augmentation_tmul]
  simp

/-- The augmentation of the base-changed algebra extends the structure map of `A'`. -/
theorem midBaseChangeOver_augmentation_algebraMap_left (X : Over B) (a' : A') :
    augmentationRingHom ((midBaseChangeOver A' B).obj X)
        (algebraMap A' (A' ⊗[A] (X.left : Type u)) a') = algebraMap A' (B : Type u) a' := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    midBaseChangeOver_augmentation_tmul]
  simp

/-- **`Ω_{P/A} ⊗_P B = Ω_{(A' ⊗_A P)/A'} ⊗_{A' ⊗_A P} B`**, for a single `A`-algebra `P`
augmented to `B`: `Stacks.KaehlerDifferential.augmentationBaseChangeEquiv` read in
`ModuleCat B`, with the algebra structures supplied by the augmentations. -/
def midBaseChangeOverDifferentialsIsoApp (X : Over B) :
    overDifferentials X ≅
      overDifferentials (A := A') (B := midAlgebra A' B)
        ((midBaseChangeOver A' B).obj X) := by
  letI : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
  letI : Algebra (A' ⊗[A] (X.left : Type u)) (B : Type u) :=
    (augmentationRingHom ((midBaseChangeOver A' B).obj X)).toAlgebra
  haveI : IsScalarTower (X.left : Type u) (A' ⊗[A] (X.left : Type u)) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun p =>
      (midBaseChangeOver_augmentation_algebraMap (A' := A') X p).symm)
  haveI : IsScalarTower A' (A' ⊗[A] (X.left : Type u)) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a' =>
      (midBaseChangeOver_augmentation_algebraMap_left (A' := A') X a').symm)
  exact (Stacks.KaehlerDifferential.augmentationBaseChangeEquiv A A' (X.left : Type u)
    (B : Type u)).symm.toModuleIso

/-- `CommAlgCat.midBaseChangeOverDifferentialsIsoApp` sends the pure differential `1 ⊗ d p` to
the pure differential `1 ⊗ d(1 ⊗ p)`. -/
@[simp]
theorem midBaseChangeOverDifferentialsIsoApp_hom_mk (X : Over B) (p : (X.left : Type u)) :
    (midBaseChangeOverDifferentialsIsoApp (A' := A') X).hom (overDifferentialsMk X p) =
      overDifferentialsMk (A := A') (B := midAlgebra A' B) ((midBaseChangeOver A' B).obj X)
        (algebraMap (X.left : Type u) (A' ⊗[A] (X.left : Type u)) p) := by
  let _ : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
  let _ : Algebra (A' ⊗[A] (X.left : Type u)) (B : Type u) :=
    (augmentationRingHom ((midBaseChangeOver A' B).obj X)).toAlgebra
  have : IsScalarTower (X.left : Type u) (A' ⊗[A] (X.left : Type u)) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun p =>
      (midBaseChangeOver_augmentation_algebraMap (A' := A') X p).symm)
  exact Stacks.KaehlerDifferential.augmentationBaseChangeEquiv_symm_tmul_D A A'
    (X.left : Type u) (B : Type u) p

/-- **`i^*Ω_{𝒪/A} = u^{-1}(i^*Ω_{𝒪/A'})`, the step of Stacks 08QZ that the proof turns on.**
For a tower of ring maps `A → A' → B`, the functor sending an `A`-algebra `P` augmented to `B` to
`Ω_{P/A} ⊗_P B` is the composite of the base-change functor `(P → B) ↦ (A' ⊗_A P → B)` of
Stacks 08QN with the functor sending an `A'`-algebra `Q` augmented to `B` to `Ω_{Q/A'} ⊗_Q B`:
```
Ω_{P/A} ⊗_P B = Ω_{(A' ⊗_A P)/A'} ⊗_{A' ⊗_A P} B ,
```
naturally in `(P → B)`. Each component is Stacks 00RV base changed along the augmentation,
`Stacks.KaehlerDifferential.augmentationBaseChangeEquiv`, and naturality holds because both
composites send the pure differential `1 ⊗ d p` to `1 ⊗ d(1 ⊗ p)` — the pure differentials
generate, by `CommAlgCat.overDifferentials_hom_ext`.

The source's `C_{B/A}` is the full subcategory of the polynomial algebras, so the comparison of
abelian sheaves it asks for is the restriction of this isomorphism along that inclusion; nothing
below uses that `P` is a polynomial algebra. -/
@[stacks 08QZ "the step the proof turns on: the sheaf (P → B) ↦ Ω_{P/A} ⊗_P B on C_{B/A} is the \
  pullback along u : (P → B) ↦ (A' ⊗_A P → B) of the sheaf (Q → B) ↦ Ω_{Q/A'} ⊗_Q B on C_{B/A'}, \
  stated on all augmented algebras rather than only the polynomial ones. The passage from here \
  to L_{B/A} = L_{B/A'} is `CommAlgCat.midCotangentComplexHomologyIso`"]
def midBaseChangeOverDifferentialsIso :
    overDifferentialsFunctor (B := B) ≅
      midBaseChangeOver A' B ⋙ overDifferentialsFunctor (A := A') (B := midAlgebra A' B) :=
  NatIso.ofComponents (fun X => midBaseChangeOverDifferentialsIsoApp X) fun {X Y} f => by
    refine overDifferentials_hom_ext _ _ fun p => ?_
    change (midBaseChangeOverDifferentialsIsoApp (A' := A') Y).hom
        (overDifferentialsPush f.left (augmentationRingHom_comp f) (overDifferentialsMk X p)) =
      overDifferentialsPush ((midBaseChangeOver A' B).map f).left
        (augmentationRingHom_comp ((midBaseChangeOver A' B).map f))
        ((midBaseChangeOverDifferentialsIsoApp (A' := A') X).hom (overDifferentialsMk X p))
    rw [overDifferentialsPush_mk, midBaseChangeOverDifferentialsIsoApp_hom_mk,
      midBaseChangeOverDifferentialsIsoApp_hom_mk]
    refine Eq.trans ?_ (overDifferentialsPush_mk ((midBaseChangeOver A' B).map f).left
      (augmentationRingHom_comp ((midBaseChangeOver A' B).map f))
      (algebraMap (X.left : Type u) (A' ⊗[A] (X.left : Type u)) p)).symm
    congr 1

/-! ### The base change of a resolution -/

section Resolution

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- The base change `A' ⊗_A P_•` of a simplicial `A`-algebra augmented to `B`, as a simplicial
`A'`-algebra: the composite of the augmented algebras `(P_n, ε_n)` with the base-change functor
`CommAlgCat.midBaseChangeOver`, with the augmentations forgotten again. -/
abbrev midSimplicialBaseChange : SimplicialObject (CommAlgCat.{u} A') :=
  resolutionOver ε ⋙ midBaseChangeOver A' B ⋙ Over.forget _

/-- The augmentation `A' ⊗_A P_• ⟶ B` of the base change, `a' ⊗ p ↦ a' · ε(p)`. -/
def midAugmentationBaseChange :
    midSimplicialBaseChange (A' := A') ε ⟶
      (SimplicialObject.const (CommAlgCat.{u} A')).obj (midAlgebra A' B) where
  app n := ((midBaseChangeOver A' B).obj ((resolutionOver ε).obj n)).hom
  naturality _ _ f :=
    (Over.w ((midBaseChangeOver A' B).map ((resolutionOver ε).map f))).trans
      (Category.comp_id _).symm

/-- The terms of the base change are the base changes of the terms. -/
theorem midSimplicialBaseChange_obj (n : SimplexCategoryᵒᵖ) :
    (midSimplicialBaseChange (A' := A') ε).obj n = baseChangeObj (A' := A') (P.obj n) :=
  rfl

/-- The augmentation of the base change is `a' ⊗ p ↦ a' · ε(p)`. -/
theorem midAugmentationBaseChange_app_tmul (n : SimplexCategoryᵒᵖ) (a' : A')
    (p : (P.obj n : Type u)) :
    (midAugmentationBaseChange (A' := A') ε).app n (a' ⊗ₜ[A] p) =
      algebraMap A' (B : Type u) a' * ((resolutionOver ε).obj n).hom.hom p :=
  baseChangeAugmentation_tmul (B' := midAlgebra A' B) (AlgHom.id A (B : Type u))
    ((resolutionOver ε).obj n) a' p

/-- The augmented algebras of the base-changed augmentation are the base changes of the augmented
algebras: `CommAlgCat.midAugmentationBaseChange` is built from them, and reading it back as a
simplicial object of `Over B` returns them. -/
theorem resolutionOver_midAugmentationBaseChange :
    resolutionOver (midAugmentationBaseChange (A' := A') ε) =
      resolutionOver ε ⋙ midBaseChangeOver A' B :=
  rfl

/-- **The differentials of a resolution and of its base change agree.** For a simplicial
`A`-algebra `P_•` augmented to `B`, the simplicial `B`-module `Ω_{P_•/A} ⊗_{P_•} B` is
`Ω_{(A' ⊗_A P_•)/A'} ⊗_{A' ⊗_A P_•} B`: the comparison of
`CommAlgCat.midBaseChangeOverDifferentialsIso` in each simplicial degree. -/
def midBaseChangeResolutionDifferentialsIso :
    resolutionOver ε ⋙ overDifferentialsFunctor ≅
      resolutionOver (midAugmentationBaseChange (A' := A') ε) ⋙
        overDifferentialsFunctor (A := A') (B := midAlgebra A' B) :=
  Functor.isoWhiskerLeft (resolutionOver ε) (midBaseChangeOverDifferentialsIso (A' := A'))


end Resolution

/-! ### Boundedly many variables are preserved by base change -/

/-- **Base change preserves the bound on the number of variables.** If an `A`-algebra is a
polynomial algebra on at most `κ` variables then so is its base change to `A'`, on the *same* set
of variables: `A' ⊗_A A[S] = A'[S]`. This refines `CommAlgCat.isPolynomialAlgebra_baseChange`,
which forgets the bound. -/
theorem isPolynomialAlgebraBelow_baseChangeObj {κ : Cardinal.{u}} {Q : CommAlgCat.{u} A}
    (hQ : IsPolynomialAlgebraBelow A κ Q) :
    IsPolynomialAlgebraBelow A' κ (baseChangeObj (A' := A') Q) := by
  obtain ⟨ι, hι, ⟨e⟩⟩ := hQ
  refine ⟨ι, hι, ⟨?_⟩⟩
  have hf : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id A' A') e.toAlgHom) :=
    Algebra.TensorProduct.map_bijective
      (f := (AlgHom.id A' A').restrictScalars A) (g := e.toAlgHom)
      Function.bijective_id e.bijective
  exact (MvPolynomial.scalarRTensorAlgEquiv (R := A) (N := A') (σ := ι)).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id A' A') e.toAlgHom) hf)

/-- The bound on the number of variables may be enlarged. -/
theorem IsPolynomialAlgebraBelow.mono {κ κ' : Cardinal.{u}} (hκ : κ ≤ κ')
    {Q : CommAlgCat.{u} A} (hQ : IsPolynomialAlgebraBelow A κ Q) :
    IsPolynomialAlgebraBelow A κ' Q :=
  hQ.imp fun _ h => ⟨h.1.trans hκ, h.2⟩

/-! ### `Lπ_!` and the complex of an arbitrary bounded resolution -/


section Bounded

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- **`L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` computed on an arbitrary bounded resolution, as a `B`-module.**
For a resolution `ε : P_• ⟶ B` of `B` over `A` whose terms are polynomial algebras on at most
`κ` variables, the sections at the point of `L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the degree `n` homology
of the alternating face map complex of `Ω_{P_•/A} ⊗_{P_•} B`; here `π` is the point morphism of
the small model of the restricted site `C_{B/A}`, and both sides are `B`-modules.

This is the module half of Tag 08PS
(`CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso`) applied to the sheaf of
`B`-modules `i^*Ω_{𝒪/A}`, followed by the identification
`CommAlgCat.smallResolutionCotangentModuleIso` of its evaluation on the cosimplicial object of
the resolution with `Ω_{P_•/A} ⊗_{P_•} B`. Because the left-hand side does not mention the
resolution, it is what makes two resolutions of the same ring map comparable. -/
def resolutionModuleLeftDerivedCotangentHomologyIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (n : ℕ) :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} (ModuleCat.{u} (B : Type u))).obj
        (((Stacks.ChaoticSite.ModuleValued.modulePointLowerShriek
              (smallBoundedPolynomialSite A B κ) (B : Type u)).leftDerived n).obj
          (smallPolynomialCotangentModuleSheaf A B κ)) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (resolutionOver ε ⋙ overDifferentialsFunctor)).homology n :=
  (smallResolutionModuleLeftDerivedLowerShriekNatIso ε κ hPκ hε n).app
      (smallPolynomialCotangentModuleSheaf A B κ) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
        (smallResolutionCotangentModuleIso ε κ hPκ))

end Bounded

/-! ### The cotangent complex read on the standard resolution -/

/-- **The cotangent complex is the complex of `Ω_{P_•/A} ⊗_{P_•} B` for the standard
resolution.** In cohomological degree `-n` its homology is the degree `n` homology of the
alternating face map complex of `Ω_{P_•/A} ⊗_{P_•} B`. Nothing is proved here: the cotangent
complex of Tag 08PN *is* that complex, reindexed, and `Ω_{P_•/A} ⊗_{P_•} B` for the standard
resolution is the simplicial module of Tag 08PN on the nose
(`CommAlgCat.standardResolutionOverDifferentialsIso`). -/
def cotangentComplexHomologyMooreIso (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (n : ℕ) :
    (cotangentComplex.{u, u} A B).homology (-(n : ℤ)) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (resolutionOver (standardResolution.{u, u} A B).hom ⋙
          overDifferentialsFunctor)).homology n :=
  ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object).extendHomologyIso
      (ComplexShape.embeddingUpIntLE 0) (j := n) (j' := -(n : ℤ)) (by simp) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
        (standardResolutionOverDifferentialsIso A B).symm)

/-! ### `L_{B/A} = L_{B/A'}` -/

section Tower

variable (A' : Type u) [CommRing A'] [Algebra A A'] (B : CommAlgCat.{u} A)
  [Algebra A' (B : Type u)] [IsScalarTower A A' (B : Type u)]

/-- A cardinal bounding the variables of every term of the standard resolution of `B` over `A'`,
of the standard resolution of `B` over `A`, and of the base change of the latter to `A'` — base
change does not change the set of variables. Both resolutions of `B` over `A'` are read in the
small model of `C_{B/A'}` restricted by this one cardinal, which is what makes them comparable. -/
abbrev midResolutionVarCardinal : Cardinal.{u} :=
  max (standardResolutionVarCardinal A B)
    (standardResolutionVarCardinal A' (midAlgebra A' B))

variable {A' B}

/-- The base change to `A'` of the standard resolution of `B` over `A` has terms that are
polynomial algebras on at most `CommAlgCat.midResolutionVarCardinal` variables. -/
theorem isPolynomialAlgebraBelow_midSimplicialBaseChange (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A' (midResolutionVarCardinal A' B)
      ((midSimplicialBaseChange (A' := A') (B := B)
        (standardResolution.{u, u} A B).hom).obj n) :=
  (isPolynomialAlgebraBelow_baseChangeObj (A' := A')
    (standardResolution_isPolynomialAlgebraBelow A B n)).mono (le_max_left _ _)

omit [Algebra A A'] [IsScalarTower A A' (B : Type u)] in
/-- The standard resolution of `B` over `A'` has terms that are polynomial algebras on at most
`CommAlgCat.midResolutionVarCardinal` variables. -/
theorem isPolynomialAlgebraBelow_standardResolution_mid (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A' (midResolutionVarCardinal A' B)
      ((standardResolution.{u, u} A' (midAlgebra A' B)).left.obj n) :=
  (standardResolution_isPolynomialAlgebraBelow A' (midAlgebra A' B) n).mono (le_max_right _ _)

/-- **Stacks 08QZ: `L_{B/A} = L_{B/A'}`.** Let `A → A' → B` be ring maps such that
`B = B ⊗_A^𝐋 A'`, which is to say that `Tor_i^A(A', B)` vanishes for `i > 0` and the canonical
map `A' ⊗_A B → B`, `a' ⊗ x ↦ a' · x`, is bijective. Then the cotangent complexes of `B` over
`A` and of `B` over `A'` have the same cohomology in every degree, as `B`-modules.

The proof is the source's. The cohomology of `L_{B/A}` in degree `-n` is the degree `n` homology
of the complex of `Ω_{P_•/A} ⊗_{P_•} B` for the standard resolution `P_•` of `B` over `A`
(Tag 08PN, `CommAlgCat.cotangentComplexHomologyMooreIso`); that simplicial module is
`Ω_{(A' ⊗_A P_•)/A'} ⊗_{A' ⊗_A P_•} B` by the comparison of
`CommAlgCat.midBaseChangeOverDifferentialsIso`, which is the step of Stacks 08QZ that the
source's proof turns on; and `A' ⊗_A P_•` and the standard resolution of `B` over `A'` are two
resolutions of `B` over `A'`, so Tag 08PT computes the same `L_nπ_!(Ω_{𝒪/A'} ⊗_𝒪 B̲)` from both
(`CommAlgCat.resolutionModuleLeftDerivedCotangentHomologyIso`).

The hypothesis enters exactly once, and only through the first half of the proof of Stacks 08QP:
`CommAlgCat.isResolution_augmentationBaseChange` turns it into the statement that
`A' ⊗_A P_• ⟶ B` is a resolution of `B` over `A'`, which is what Tag 08PT needs of the
base-changed resolution. Both halves are used there: Tor independence makes
`s(P_•) ⊗_A A'` compute `B ⊗_A^𝐋 A'`, and bijectivity of `A' ⊗_A B → B` identifies its
degree-zero homology with `B`.

The conclusion here is degreewise, not an isomorphism in `D(B)`: the module half of Tag 08PS,
`CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso`, identifies the degree `n`
functor `(Lπ_!)_n` with the degree `n` homology of the Moore complex, so the two resolutions of
`B` over `A'` are compared one degree at a time. The source's isomorphism in `D(B)` is
`CommAlgCat.midCotangentComplexDerivedIso` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteBaseChangeDerived.lean`, which carries the same
hypotheses and is not deduced from this statement — degreewise isomorphisms do not give one in
`D(B)`. -/
@[stacks 08QZ "the cohomology of L_{B/A} and of L_{B/A'} agrees in every degree, as B-modules, \
  under the tag's own hypothesis B = B ⊗_A^𝐋 A' — Tor independence of A' and B over A, and \
  bijectivity of A' ⊗_A B → B. Degreewise rather than in D(B), because the module half of \
  Tag 08PS, which is what compares the two resolutions of B over A', is itself a statement \
  about (Lπ_!)_n and H_n. The tag's own conclusion, an isomorphism in D(B) along the canonical \
  map of Tag 08PN, is `CommAlgCat.midCotangentComplexDerivedIso`"]
def midCotangentComplexHomologyIso
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective
      (baseChangeUnit (B' := midAlgebra A' B) (AlgHom.id A (B : Type u))))
    (n : ℕ) :
    (cotangentComplex.{u, u} A B).homology (-(n : ℤ)) ≅
      (cotangentComplex.{u, u} A' (midAlgebra A' B)).homology (-(n : ℤ)) :=
  have hbc : IsResolution A' (B : Type u)
      (midSimplicialBaseChange (A' := A') (B := B) (standardResolution.{u, u} A B).hom)
      (midAugmentationBaseChange (A' := A') (B := B) (standardResolution.{u, u} A B).hom) :=
    isResolution_augmentationBaseChange (B' := midAlgebra A' B) (AlgHom.id A (B : Type u))
      (standardResolution.{u, u} A B).hom (standardResolution_isResolution.{u, u} A B) hTor hφ
  cotangentComplexHomologyMooreIso A B n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
        (midBaseChangeResolutionDifferentialsIso (A' := A') (B := B)
          (standardResolution.{u, u} A B).hom)) ≪≫
    (resolutionModuleLeftDerivedCotangentHomologyIso
        (midAugmentationBaseChange (A' := A') (B := B) (standardResolution.{u, u} A B).hom)
        (midResolutionVarCardinal A' B)
        (isPolynomialAlgebraBelow_midSimplicialBaseChange (A' := A'))
        hbc.trivialKanFibration n).symm ≪≫
    resolutionModuleLeftDerivedCotangentHomologyIso
      (standardResolution.{u, u} A' (midAlgebra A' B)).hom
      (midResolutionVarCardinal A' B)
      (isPolynomialAlgebraBelow_standardResolution_mid (A' := A'))
      (standardResolution_isResolution.{u, u} A' (midAlgebra A' B)).trivialKanFibration n ≪≫
    (cotangentComplexHomologyMooreIso A' (midAlgebra A' B) n).symm

end Tower

end CommAlgCat

end
