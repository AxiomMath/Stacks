module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.BiproductStalk
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Complex
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Exactness of the Koszul complex of the coordinates on projective space

Let `A` be a ring and `X = P^n_A = Proj A[X₀, …, Xₙ]`. For every integer `a` the Koszul complex
of the coordinates, twisted by `a`, is exact.

Exactness is a stalkwise condition. At a point `x` some coordinate `Xᵢ` lies outside the
homogeneous prime of `x`, and multiplication by `Xᵢ^(-d)` trivializes the stalk of every twist
`𝒪_X(d)` at `x`; the stalk of the `j`-th term of the complex is then the free module on the
`j`-element subsets of the coordinates over the local ring `B = 𝒪_{X,x}`, and the differential
becomes the Koszul differential of the sequence `(X₀/Xᵢ, …, Xₙ/Xᵢ)` in `B`. The `i`-th entry
of that sequence is `1`, so contraction with the `i`-th coordinate functional is a contracting
homotopy and the stalk complex is exact in every degree.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.coordRatioStalk`: the degree-zero fraction
  `X_k/Xᵢ` in the local ring at a point of the chart `D₊(Xᵢ)`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.twistStalkEquivX`: the trivialization of the stalk
  of `𝒪_X(d)` by `Xᵢ`, at the spelling of the stalk the stalk functor produces.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulStalkCoord`: the coordinate of an element of
  the stalk of the `j`-th term of the complex, read in the local ring through the trivialization
  of `𝒪_X(a+j)` by `Xᵢ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.coordRatioStalk_self`: the `i`-th ratio is `1`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulStalkCoord_injective` and
  `Stacks.AlgebraicGeometry.ProjKoszulComplex.exists_koszulStalkCoord_eq`: the coordinates
  identify the stalk of the `j`-th term with the functions on the `j`-element subsets.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulStalkCoord_stalkMap_koszulDiff`: **the stalk
  of the differential is the Koszul differential of `(X₀/Xᵢ, …, Xₙ/Xᵢ)`.**
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.acyclic_koszulComplex`: **the Koszul complex is
  acyclic.**

## Implementation notes

Only additivity of the coordinates is needed, not linearity over the local ring: the
contracting homotopy is written down in coordinates and transported back, so the three
inequivalent scalar actions on a stalk that the Euler sequence has to reconcile never enter.

Exactness is proved in the degrees of the form `j + 1` and transported to an arbitrary degree
once, at the level of the proposition, which is what keeps every `ComplexShape` index in the
proof spelled as a successor and `CategoryTheory.eqToHom` out of it.

`rw [map_sum]` on a sum indexed by the summands of a biproduct exhausts the `isDefEq` budget, so
every such step supplies `map_sum _ _ Finset.univ` as a term, as in the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjEulerSequence/Exactness.lean`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjKoszulComplex

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The local ring of `P^n_A` at a point, in the spelling the trivializations of the twisting
sheaves land in. -/
abbrev koszulStalkRing (x : ProjectiveSpectrum.top (polyGrading A n)) : Type u :=
  ToType ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n)).presheaf.stalk x)

variable (a : ℤ)

section Point

variable (x : ProjectiveSpectrum.top (polyGrading A n)) (i : Fin (n + 1))
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A) ∉ x.asHomogeneousIdeal)

/-! ### The coordinate ratios at a point of a standard chart -/

/-- **The degree-zero fraction `X_k/Xᵢ` in the local ring at `x`**, for `x` a point of the
standard chart `D₊(Xᵢ)`. These are the entries of the sequence whose Koszul complex the stalk
of the Koszul complex of the coordinates is. -/
def coordRatioStalk (k : Fin (n + 1)) : koszulStalkRing A n x :=
  (Proj.stalkIso' (polyGrading A n) x).symm
    (twistRatio (polyGrading A n) (X_mem_one A n i) hx ⟨MvPolynomial.X k, X_mem_one A n k⟩)

/-- **The `i`-th coordinate ratio is `1`.** This is why the stalk complex is contractible. -/
theorem coordRatioStalk_self : coordRatioStalk A n x i hx i = 1 := by
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A) ^ 1 ∈
      x.asHomogeneousIdeal.toIdeal.primeCompl :=
    x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx 1
  have h : twistRatio (polyGrading A n) (X_mem_one A n i) hx
      ⟨MvPolynomial.X i, X_mem_one A n i⟩ = 1 := by
    refine HomogeneousLocalization.val_injective _ ?_
    rw [val_twistRatio, HomogeneousLocalization.val_one]
    refine Eq.trans (congrArg (fun y : MvPolynomial (Fin (n + 1)) A =>
      Localization.mk y (⟨(MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A) ^ 1, hmem⟩ :
        x.asHomogeneousIdeal.toIdeal.primeCompl)) (pow_one _).symm) ?_
    exact Localization.mk_self ⟨_, hmem⟩
  rw [coordRatioStalk, h, map_one]

/-! ### Coordinates on the stalk of a term -/

/-- **The trivialization of the stalk of `𝒪_X(d)` at `x` by the coordinate `Xᵢ`**, as an
additive equivalence with the local ring, at the spelling of the stalk that the stalk functor on
sheaves of modules produces. -/
def twistStalkEquivX (d : ℤ) :
    ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading A n)) x
        (twistingSheaf (polyGrading A n) d)) ≃+ koszulStalkRing A n x :=
  (twistingSheafStalkEquiv (polyGrading A n) (X_mem_one A n i) hx d).toAddEquiv

/-- `twistStalkEquivX` agrees with the stalk trivialization `twistingSheafStalkEquiv`. -/
theorem twistStalkEquivX_apply (d : ℤ)
    (y : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (twistingSheaf (polyGrading A n) d))) :
    twistStalkEquivX A n x i hx d y =
      twistingSheafStalkEquiv (polyGrading A n) (X_mem_one A n i) hx d y :=
  rfl

/-- **The coordinate of an element of the stalk of the `j`-th term of the Koszul complex at the
index `s`**, read in the local ring at `x` through the trivialization of `𝒪_X(a+j)` by `Xᵢ`. -/
def koszulStalkCoord (j : ℤ) (s : koszulIndex (n + 1) j)
    (z : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (koszulTerm A n a j))) :
    koszulStalkRing A n x :=
  twistStalkEquivX A n x i hx (a + j)
    ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
      (biproduct.π (koszulFamily A n a j) s)).hom z)

/-- The coordinates are additive. -/
theorem koszulStalkCoord_add (j : ℤ) (s : koszulIndex (n + 1) j)
    (z z' : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (koszulTerm A n a j))) :
    koszulStalkCoord A n a x i hx j s (z + z') =
      koszulStalkCoord A n a x i hx j s z + koszulStalkCoord A n a x i hx j s z' :=
  (congrArg (twistStalkEquivX A n x i hx (a + j)) (map_add _ z z')).trans (map_add _ _ _)

/-- **An element of the stalk of the `j`-th term is determined by its coordinates.** -/
theorem koszulStalkCoord_injective (j : ℤ)
    {z z' : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (koszulTerm A n a j))}
    (h : ∀ s, koszulStalkCoord A n a x i hx j s z = koszulStalkCoord A n a x i hx j s z') :
    z = z' := by
  have hcomp : ∀ s, (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
        (projRingSheaf (polyGrading A n)) x (biproduct.π (koszulFamily A n a j) s)).hom z =
      (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
        (biproduct.π (koszulFamily A n a j) s)).hom z' := fun s =>
    (twistStalkEquivX A n x i hx (a + j)).injective (h s)
  have hz := _root_.AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
    (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) z
  have hz' := _root_.AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
    (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) z'
  rw [← hz, ← hz']
  exact congrArg _ (funext hcomp)

/-- **Every family of elements of the local ring is the coordinate family of an element of the
stalk of the `j`-th term.** -/
theorem exists_koszulStalkCoord_eq (j : ℤ) (c : koszulIndex (n + 1) j → koszulStalkRing A n x) :
    ∃ z, ∀ s, koszulStalkCoord A n a x i hx j s z = c s := by
  classical
  refine ⟨_root_.AlgebraicGeometry.SheafOfModules.stalkBiproductLift
    (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j)
    fun s => (twistStalkEquivX A n x i hx (a + j)).symm (c s), fun s => ?_⟩
  refine Eq.trans (congrArg (twistStalkEquivX A n x i hx (a + j)) ?_)
    ((twistStalkEquivX A n x i hx (a + j)).apply_symm_apply (c s))
  refine Eq.trans (map_sum (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
      (projRingSheaf (polyGrading A n)) x (biproduct.π (koszulFamily A n a j) s)).hom
    (fun t => (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
        (projRingSheaf (polyGrading A n)) x (biproduct.ι (koszulFamily A n a j) t)).hom
      ((twistStalkEquivX A n x i hx (a + j)).symm (c t)))
    Finset.univ) ?_
  refine Eq.trans (Finset.sum_eq_single_of_mem s (Finset.mem_univ s) fun t _ hts =>
    _root_.AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_ne
      (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) hts _) ?_
  exact _root_.AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_self
    (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) s _

/-! ### The stalk of the differential -/

/-- Evaluation of a morphism of modules at a fixed element, as an additive map, so that
scalar multiples and zero can be moved through it. -/
private def evalModuleHom {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (y : M) :
    (M ⟶ N) →+ N where
  toFun Φ := Φ.hom y
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The stalk of multiplication by the coordinate `X_k` is multiplication by `X_k/Xᵢ`**, once
the stalks of the twisting sheaves are trivialized by `Xᵢ`. This is the compatibility formula of
`Stacks.AlgebraicGeometry.ProjKoszulComplex.twistingSheafStalkEquiv_stalkMap_twistMulLeftInt`
with the target degree named rather than computed. -/
theorem twistStalkEquivX_stalkMap_twistMulX (d e : ℤ) (he : (1 : ℤ) + d = e)
    (k : Fin (n + 1))
    (y : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (twistingSheaf (polyGrading A n) d))) :
    twistStalkEquivX A n x i hx e
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
          (twistMulX A n k d e he)).hom y) =
      coordRatioStalk A n x i hx k * twistStalkEquivX A n x i hx d y := by
  obtain rfl : e = ((1 : ℕ) : ℤ) + d := by rw [Nat.cast_one]; exact he.symm
  exact twistingSheafStalkEquiv_stalkMap_twistMulLeftInt (polyGrading A n) (X_mem_one A n i) hx d
    ⟨MvPolynomial.X k, X_mem_one A n k⟩ y

/-- **The stalk of a matrix entry of the Koszul differential is multiplication by the
corresponding entry of the Koszul matrix of the sequence `(X₀/Xᵢ, …, Xₙ/Xᵢ)`.** -/
theorem twistStalkEquivX_stalkMap_koszulCoeff (j : ℤ) (s : koszulIndex (n + 1) j)
    (t : koszulIndex (n + 1) (j + 1))
    (y : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (twistingSheaf (polyGrading A n) (a + j)))) :
    twistStalkEquivX A n x i hx (a + (j + 1))
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
          (koszulCoeff A n a j s t)).hom y) =
      koszulRatioCoeff (coordRatioStalk A n x i hx) s t *
        twistStalkEquivX A n x i hx (a + j) y := by
  classical
  have hdeg : (1 : ℤ) + (a + j) = a + (j + 1) := by ring
  by_cases hex : ∃ k : Fin (n + 1), k ∉ s.1 ∧ t.1 = insert k s.1
  · obtain ⟨k, hk, ht⟩ := hex
    have hsm : _root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x
          (koszulSign k s.1 • twistMulX A n k (a + j) (a + (j + 1)) hdeg) =
        koszulSign k s.1 • _root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x
          (twistMulX A n k (a + j) (a + (j + 1)) hdeg) :=
      _root_.CategoryTheory.Functor.map_zsmul
        (_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading A n)) x)
    have hcoeff : koszulRatioCoeff (coordRatioStalk A n x i hx) s t =
        ((koszulSign k s.1 : ℤ) : koszulStalkRing A n x) * coordRatioStalk A n x i hx k :=
      koszulRatioCoeff_eq _ s t hk ht
    refine Eq.trans (congrArg (fun Φ =>
      twistStalkEquivX A n x i hx (a + (j + 1)) (ModuleCat.Hom.hom Φ y))
      ((congrArg (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
        (projRingSheaf (polyGrading A n)) x)
        (koszulCoeff_eq A n a j s t hk ht)).trans hsm)) ?_
    refine Eq.trans ((congrArg (twistStalkEquivX A n x i hx (a + (j + 1)))
      (map_zsmul (evalModuleHom y) (koszulSign k s.1) _)).trans
      (map_zsmul _ (koszulSign k s.1) _)) ?_
    refine Eq.trans (congrArg (fun b : koszulStalkRing A n x => koszulSign k s.1 • b)
      (twistStalkEquivX_stalkMap_twistMulX A n x i hx (a + j) (a + (j + 1)) hdeg k y)) ?_
    rw [hcoeff, zsmul_eq_mul, mul_assoc]
  · have hzero : ∀ k : Fin (n + 1), k ∉ s.1 → t.1 ≠ insert k s.1 :=
      fun k hk ht => hex ⟨k, hk, ht⟩
    have hsm : _root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x
          (0 : twistingSheaf (polyGrading A n) (a + j) ⟶
            twistingSheaf (polyGrading A n) (a + (j + 1))) = 0 :=
      _root_.CategoryTheory.Functor.map_zero
        (_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading A n)) x) _ _
    refine Eq.trans (congrArg (fun Φ =>
      twistStalkEquivX A n x i hx (a + (j + 1)) (ModuleCat.Hom.hom Φ y))
      ((congrArg (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
        (projRingSheaf (polyGrading A n)) x)
        (koszulCoeff_eq_zero A n a j s t hzero)).trans hsm)) ?_
    rw [koszulRatioCoeff_eq_zero _ s t hzero, zero_mul]
    exact (congrArg (twistStalkEquivX A n x i hx (a + (j + 1)))
      (map_zero (evalModuleHom y))).trans (map_zero _)

/-- Applying two stalk maps in turn is applying the stalk map of the composite. -/
private theorem stalkMap_comp_apply
    {M N P : SheafOfModules.{u} (projRingSheaf (polyGrading A n))} (φ : M ⟶ N) (ψ : N ⟶ P)
    (w : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x M)) :
    (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x ψ).hom
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x φ).hom w) =
      (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
        (φ ≫ ψ)).hom w :=
  congrArg (fun Φ => ModuleCat.Hom.hom Φ w)
    (((_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
      (projRingSheaf (polyGrading A n)) x).map_comp φ ψ).symm)

/-- The summand of the stalk at the index `s`, pushed through the differential and projected to
the index `t`, is the stalk of the matrix entry at `(s, t)`. -/
private theorem stalkMap_π_stalkMap_koszulDiff_stalkMap_ι (j : ℤ) (s : koszulIndex (n + 1) j)
    (t : koszulIndex (n + 1) (j + 1))
    (w : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j s))) :
    (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
          (biproduct.π (koszulFamily A n a (j + 1)) t)).hom
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
          (koszulDiff A n a j)).hom
          ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading A n)) x
            (biproduct.ι (koszulFamily A n a j) s)).hom w)) =
      (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
        (koszulCoeff A n a j s t)).hom w :=
  ((congrArg (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x
          (biproduct.π (koszulFamily A n a (j + 1)) t)).hom
        (stalkMap_comp_apply A n x (biproduct.ι (koszulFamily A n a j) s)
          (koszulDiff A n a j) w)).trans
      (stalkMap_comp_apply A n x (biproduct.ι (koszulFamily A n a j) s ≫ koszulDiff A n a j)
        (biproduct.π (koszulFamily A n a (j + 1)) t) w)).trans
    (congrArg (fun Φ : koszulFamily A n a j s ⟶ twistingSheaf (polyGrading A n) (a + (j + 1)) =>
        (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x Φ).hom w)
      ((Category.assoc _ _ _).trans (biproduct_ι_comp_koszulDiff_comp_π A n a j s t)))

/-- **The stalk of the Koszul differential is the Koszul differential of the sequence
`(X₀/Xᵢ, …, Xₙ/Xᵢ)` in the local ring at `x`**, in the coordinates given by the trivialization
of the twists by `Xᵢ`. -/
theorem koszulStalkCoord_stalkMap_koszulDiff (j : ℤ) (t : koszulIndex (n + 1) (j + 1))
    (z : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (koszulTerm A n a j))) :
    koszulStalkCoord A n a x i hx (j + 1) t
        ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
          (koszulDiff A n a j)).hom z) =
      ∑ s : koszulIndex (n + 1) j, koszulRatioCoeff (coordRatioStalk A n x i hx) s t *
        koszulStalkCoord A n a x i hx j s z := by
  classical
  have key : ∀ c : ∀ s : koszulIndex (n + 1) j,
        ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
          (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j s)),
      koszulStalkCoord A n a x i hx (j + 1) t
          ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading A n)) x (koszulDiff A n a j)).hom
            (_root_.AlgebraicGeometry.SheafOfModules.stalkBiproductLift
              (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) c)) =
        ∑ s : koszulIndex (n + 1) j, koszulRatioCoeff (coordRatioStalk A n x i hx) s t *
          twistStalkEquivX A n x i hx (a + j) (c s) := by
    intro c
    have h1 : (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading A n)) x
            (biproduct.π (koszulFamily A n a (j + 1)) t)).hom
          ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading A n)) x (koszulDiff A n a j)).hom
            (_root_.AlgebraicGeometry.SheafOfModules.stalkBiproductLift
              (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) c)) =
        ∑ s : koszulIndex (n + 1) j, (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x (koszulCoeff A n a j s t)).hom (c s) := by
      refine Eq.trans (congrArg (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
        (projRingSheaf (polyGrading A n)) x
        (biproduct.π (koszulFamily A n a (j + 1)) t)).hom
        (map_sum (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading A n)) x (koszulDiff A n a j)).hom
          (fun s => (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
              (projRingSheaf (polyGrading A n)) x
              (biproduct.ι (koszulFamily A n a j) s)).hom (c s))
          Finset.univ)) ?_
      refine Eq.trans (map_sum (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x
          (biproduct.π (koszulFamily A n a (j + 1)) t)).hom _ Finset.univ) ?_
      exact Finset.sum_congr rfl fun s _ =>
        stalkMap_π_stalkMap_koszulDiff_stalkMap_ι A n a x j s t (c s)
    refine Eq.trans (congrArg (twistStalkEquivX A n x i hx (a + (j + 1))) h1) ?_
    refine Eq.trans (map_sum (twistStalkEquivX A n x i hx (a + (j + 1))) _ Finset.univ) ?_
    exact Finset.sum_congr rfl fun s _ =>
      twistStalkEquivX_stalkMap_koszulCoeff A n a x i hx j s t (c s)
  have hz := _root_.AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
    (projRingSheaf (polyGrading A n)) x (koszulFamily A n a j) z
  exact (congrArg (fun z' => koszulStalkCoord A n a x i hx (j + 1) t
    ((_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
      (koszulDiff A n a j)).hom z')) hz.symm).trans (key _)

/-! ### Exactness -/

/-- The coordinates of the zero germ vanish. -/
theorem koszulStalkCoord_zero (j : ℤ) (s : koszulIndex (n + 1) j) :
    koszulStalkCoord A n a x i hx j s 0 = 0 :=
  (congrArg (twistStalkEquivX A n x i hx (a + j)) (map_zero _)).trans (map_zero _)

/-- The differential of the stalk complex in consecutive degrees is the stalk of the Koszul
differential, read on an element. -/
private theorem stalkComplex_d_apply (j : ℤ)
    (z : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
      (projRingSheaf (polyGrading A n)) x (koszulTerm A n a j))) :
    ModuleCat.Hom.hom ((((_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading A n)) x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (koszulComplex A n a)).d j (j + 1)) z =
      (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
        (koszulDiff A n a j)).hom z :=
  congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (congrArg (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
      (projRingSheaf (polyGrading A n)) x) (koszulComplex_d A n a j))

/-- Exactness of the stalk complex in degree `j + 1`, reduced to a statement about the stalks of
the Koszul differentials. -/
private theorem exactAt_stalk_of_exists (j : ℤ)
    (h : ∀ z : ↥(_root_.AlgebraicGeometry.SheafOfModules.stalkObj
        (projRingSheaf (polyGrading A n)) x (koszulTerm A n a (j + 1))),
      (_root_.AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading A n)) x
          (koszulDiff A n a (j + 1))).hom z = 0 →
        ∃ w, (_root_.AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading A n)) x (koszulDiff A n a j)).hom w = z) :
    (((_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
        (projRingSheaf (polyGrading A n)) x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (koszulComplex A n a)).ExactAt (j + 1) := by
  refine (HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 1 + 1)
    (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl)).mpr ?_
  refine (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr fun z hz => ?_
  obtain ⟨w, hw⟩ := h z ((stalkComplex_d_apply A n a x (j + 1) z).symm.trans hz)
  exact ⟨w, (stalkComplex_d_apply A n a x j w).trans hw⟩

include i hx in
/-- **The complex of stalks of the Koszul complex at a point of the chart `D₊(Xᵢ)` is exact in
every degree of the form `j + 1`.**

A germ killed by the differential has a coordinate family killed by the Koszul matrix of the
sequence `(X₀/Xᵢ, …, Xₙ/Xᵢ)`, whose `i`-th entry is `1`; contracting that family with the `i`-th
coordinate functional produces a coordinate family whose image under the differential is the
original one. -/
theorem exactAt_stalk_koszulComplex_succ (j : ℤ) :
    (((_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
        (projRingSheaf (polyGrading A n)) x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (koszulComplex A n a)).ExactAt (j + 1) := by
  classical
  refine exactAt_stalk_of_exists A n a x j fun z hgz => ?_
  obtain ⟨v, hv⟩ := exists_sum_koszulRatioCoeff_eq (coordRatioStalk A n x i hx)
    (coordRatioStalk_self A n x i hx) j
    (fun t => koszulStalkCoord A n a x i hx (j + 1) t z) fun u =>
      (koszulStalkCoord_stalkMap_koszulDiff A n a x i hx (j + 1) u z).symm.trans
        ((congrArg (koszulStalkCoord A n a x i hx (j + 1 + 1) u) hgz).trans
          (koszulStalkCoord_zero A n a x i hx (j + 1 + 1) u))
  obtain ⟨w, hw⟩ := exists_koszulStalkCoord_eq A n a x i hx j v
  refine ⟨w, koszulStalkCoord_injective A n a x i hx (j + 1) fun t => ?_⟩
  refine (koszulStalkCoord_stalkMap_koszulDiff A n a x i hx j t w).trans ?_
  exact (Finset.sum_congr rfl fun s _ => congrArg _ (hw s)).trans (hv t)

end Point

/-- **The complex of stalks of the Koszul complex at any point is exact in every degree.** Some
coordinate lies outside the homogeneous prime of the point, and the stalk complex is the Koszul
complex of a sequence one of whose entries is `1`. -/
theorem acyclic_stalk_koszulComplex (x : ProjectiveSpectrum.top (polyGrading A n)) :
    (((_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor
        (projRingSheaf (polyGrading A n)) x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (koszulComplex A n a)).Acyclic := by
  intro j
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, j = k + 1 := ⟨j - 1, by ring⟩
  obtain ⟨i, hx⟩ := exists_X_notMem_asHomogeneousIdeal A n x
  exact exactAt_stalk_koszulComplex_succ A n a x i hx k

/-- **The Koszul complex of the coordinates on `P^n_A`, twisted by `a`, is acyclic**: it is exact
in every degree, hence an exact complex
`0 ⟶ 𝒪_X(a) ⟶ … ⟶ 𝒪_X(a+j)^{⊕ binom(n+1, j)} ⟶ … ⟶ 𝒪_X(a+n+1) ⟶ 0`.

Acyclicity is a stalkwise condition, and at each point the complex of stalks is the Koszul
complex of the sequence `(X₀/Xᵢ, …, Xₙ/Xᵢ)` of the local ring for a coordinate `Xᵢ` outside the
homogeneous prime of the point; its `i`-th entry is `1`, so it is contractible. -/
theorem acyclic_koszulComplex : (koszulComplex A n a).Acyclic :=
  (_root_.AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic
    (projRingSheaf (polyGrading A n)) (koszulComplex A n a)).mpr
    (acyclic_stalk_koszulComplex A n a)

end Stacks.AlgebraicGeometry.ProjKoszulComplex

end
