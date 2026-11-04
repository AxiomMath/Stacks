module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom complex, and the closed structure on cochain complexes

Let `A` be a monoidal closed preadditive category whose tensor product is additive in both
variables, and which has products indexed by `ℤ`. For cochain complexes `K` and `L` in `A`
this file constructs the **internal Hom complex** `Hom•(K, L)`, whose degree-`n` term is the
product
`∏_{p : ℤ} (ihom (K.X p)).obj (L.X (p + n))`
and whose differential is the Koszul differential of a Hom complex, and shows that
`Hom•(K, -)` is right adjoint to `K ⊗ -` for Mathlib's monoidal structure on
`CochainComplex A ℤ` (the total complex of the degreewise tensor product). Consequently
`CochainComplex A ℤ` is monoidal closed.

## Main definitions

* `CochainComplex.internalHomComplex`: the complex `Hom•(K, L)`.
* `CochainComplex.internalHomEquiv`: the transposition `(K ⊗ L ⟶ M) ≃ (L ⟶ Hom•(K, M))`.
* `CochainComplex.internalHomAdjunction`: the adjunction `K ⊗ - ⊣ Hom•(K, -)`.
* `CochainComplex.monoidalClosed`: the resulting closed structure on `CochainComplex A ℤ`.

## Main results

* `CochainComplex.internalHomComplex_d_π`: the factorwise description of the differential,
  which pins it down completely.
* `CochainComplex.uncurryComp_comm`: the transposed form of the statement that a morphism
  `L ⟶ Hom•(K, M)` commutes with the differentials. This is the heart of the file: it is the
  identity that the Koszul signs of the Hom differential and of the total tensor differential
  are chosen to match.
* `CochainComplex.ι_internalHomEquiv_symm`: the transposition on the summand of bidegree
  `(p, q)` is uncurrying, up to the Koszul sign `(-1)^(p*q)`.

## Implementation notes

The product defining degree `n` is indexed by the *source* degree `p`, the factor at `p` being
`ihom (K.X p) (L.X (p + n))`. The `L`-half of the differential stays in the factor `p` and is
`ihom (K.X p)` applied to `L.d (p + n) (p + m)`, which needs no reindexing because
`HomologicalComplex.d` accepts an arbitrary pair of degrees. The `K`-half moves from the factor
`p + 1` to the factor `p`, and there the two spellings `p + 1 + n` and `p + m` of one degree of
`L` differ, so a single `HomologicalComplex.XIsoOfEq` appears in `internalHomD₂`; it is absorbed
by `XIsoOfEq_hom_comp_d` and `d_comp_XIsoOfEq_hom` in every proof. For the same reason the
transposed family attached to a morphism is indexed so that its target is `M.X (p + q)`, with
one `XIsoOfEq` relating `p + 1 + q`, `p + (q + 1)` and the degree it is inserted into.

Following the pattern of `StacksFrontier/Algebra/Homology/KoszulSymmetric.lean`, the Mathlib
fact `MonoidalClosed.pre_map` is restated here as the `@[reassoc]` lemma
`CategoryTheory.MonoidalClosed.pre_app_comp`, and `MonoidalClosed.pre_comm_ihom_map` is used
through `reassoc_of%`, so that every rewrite in a right-associated composite is syntactic: in a
general `A` the associativity of composition does not hold by `rfl`.
`CochainComplex.internalHomComplexπ` exists for the same reason: it is
`CochainComplex.internalHomπ` with its source retyped as a term of the complex, which keeps
composites with a morphism *into* `Hom•(K, L)` type-correct under the `implicit` transparency
level that `rw` works at.

The closed structure is deliberately *not* an instance, for the reason recorded in
`KoszulSymmetric.lean`: `CochainComplex A ℤ` carries several monoidal and closed structures
(`StacksFrontier/Homology/HomComplex/Currying.lean` already supplies one for `A = ModuleCat R`),
and making this one an instance would silently fix the choice of right adjoint -- which, as
Mathlib's `CategoryTheory.Closed` notes, is data and not merely a property. Consumers take the
named datum `monoidalClosed`, or the adjunction `internalHomAdjunction`.

## References

* [The Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [The Stacks Project, Tag 0A5Y](https://stacks.math.columbia.edu/tag/0A5Y)
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace CategoryTheory.MonoidalClosed

noncomputable section

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [MonoidalClosed A]

/-! ## A reassociated form of `MonoidalClosed.pre_map` -/

/-- `MonoidalClosed.pre_map`, restated componentwise with a `@[reassoc]` variant: precomposing
successively with `g` and then `f` is precomposing with `f ≫ g`. -/
@[reassoc]
lemma pre_app_comp {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (M : A) :
    (pre g).app M ≫ (pre f).app M = (pre (f ≫ g)).app M := by
  rw [pre_map]
  rfl

/-! ## Additivity of the internal hom, of currying and of uncurrying -/

variable [Preadditive A] [MonoidalPreadditive A]

/-- The internal Hom functor out of a fixed object of an additive monoidal closed category is
additive, being right adjoint to the additive functor `X ⊗ -`. -/
instance ihom_additive (X : A) : (ihom X).Additive :=
  (ihom.adjunction X).right_adjoint_additive

/-- Precomposition with the zero morphism is zero. -/
@[reassoc (attr := simp)]
lemma pre_app_zero {X Y : A} (M : A) : (pre (0 : X ⟶ Y)).app M = 0 :=
  uncurry_injective (by
    rw [uncurry_pre, MonoidalPreadditive.zero_whiskerRight, zero_comp, uncurry_eq,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp])

/-- Uncurrying is additive. -/
lemma uncurry_add {X Y Z : A} (f g : Y ⟶ (ihom X).obj Z) :
    uncurry (f + g) = uncurry f + uncurry g := by
  simp only [uncurry_eq, MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

/-- Uncurrying commutes with an integral scalar, hence with a Koszul sign. -/
lemma uncurry_units_smul {X Y Z : A} (u : ℤˣ) (f : Y ⟶ (ihom X).obj Z) :
    uncurry (u • f) = u • uncurry f := by
  rw [uncurry_eq, uncurry_eq, Units.smul_def, Units.smul_def,
    show X ◁ ((u : ℤ) • f) = (u : ℤ) • (X ◁ f) from (tensorLeft X).map_zsmul,
    Preadditive.zsmul_comp]

/-- Currying is additive. -/
lemma curry_add {X Y Z : A} (f g : X ⊗ Y ⟶ Z) : curry (f + g) = curry f + curry g := by
  simp only [curry_eq, Functor.map_add, Preadditive.comp_add]

/-- Currying commutes with an integral scalar, hence with a Koszul sign. -/
lemma curry_units_smul {X Y Z : A} (u : ℤˣ) (f : X ⊗ Y ⟶ Z) : curry (u • f) = u • curry f := by
  rw [curry_eq, curry_eq, Units.smul_def, Units.smul_def, Functor.map_zsmul,
    Preadditive.comp_zsmul]

end

end CategoryTheory.MonoidalClosed

namespace CochainComplex

noncomputable section

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [MonoidalClosed A] [Preadditive A]
  [HasProductsOfShape ℤ A]

/-! ## The internal Hom complex: the underlying graded object and the differential -/

/-- The degree-`n` term of the internal Hom complex `Hom•(K, L)`: the product over `p : ℤ` of
the internal homs `ihom (K.X p) (L.X (p + n))`. -/
abbrev internalHomX (K L : CochainComplex A ℤ) (n : ℤ) : A :=
  ∏ᶜ fun p : ℤ => (ihom (K.X p)).obj (L.X (p + n))

/-- The projection of the degree-`n` term of `Hom•(K, L)` onto its factor at `p`. -/
abbrev internalHomπ (K L : CochainComplex A ℤ) (n p : ℤ) :
    internalHomX K L n ⟶ (ihom (K.X p)).obj (L.X (p + n)) :=
  Pi.π (fun p : ℤ => (ihom (K.X p)).obj (L.X (p + n))) p

/-- The half of the Koszul differential coming from the differential of `L`: it stays in the
factor `p`, where it is `ihom (K.X p)` applied to `L.d (p + n) (p + m)`. -/
def internalHomD₁ (K L : CochainComplex A ℤ) (n m p : ℤ) :
    internalHomX K L n ⟶ (ihom (K.X p)).obj (L.X (p + m)) :=
  internalHomπ K L n p ≫ (ihom (K.X p)).map (L.d (p + n) (p + m))

/-- The half of the Koszul differential coming from the differential of `K`: it reads the factor
at `p + 1` and precomposes with `K.d p (p + 1)`, landing in the factor at `p`. -/
def internalHomD₂ (K L : CochainComplex A ℤ) (n m p : ℤ) (h : n + 1 = m) :
    internalHomX K L n ⟶ (ihom (K.X p)).obj (L.X (p + m)) :=
  internalHomπ K L n (p + 1) ≫
    (ihom (K.X (p + 1))).map (L.XIsoOfEq (show p + 1 + n = p + m by omega)).hom ≫
    (pre (K.d p (p + 1))).app (L.X (p + m))

/-- The Koszul differential of the internal Hom complex: in degree `n` it is
`f ↦ d_L ∘ f + (-1)^(n+1) f ∘ d_K`, written as a map into a product. It is zero unless the two
degrees are consecutive. -/
@[sga "4 XVII 1.1.10" "more general"]
def internalHomd (K L : CochainComplex A ℤ) (n m : ℤ) :
    internalHomX K L n ⟶ internalHomX K L m :=
  if h : n + 1 = m then
    Pi.lift fun p => internalHomD₁ K L n m p + (m.negOnePow : ℤˣ) • internalHomD₂ K L n m p h
  else 0

/-- The factorwise description of the differential of the internal Hom complex. -/
@[reassoc]
lemma internalHomd_π (K L : CochainComplex A ℤ) (n m : ℤ) (h : n + 1 = m) (p : ℤ) :
    internalHomd K L n m ≫ internalHomπ K L m p =
      internalHomD₁ K L n m p + (m.negOnePow : ℤˣ) • internalHomD₂ K L n m p h := by
  rw [internalHomd, dite_eq_left h, Pi.lift_π]

/-- The differential of the internal Hom complex vanishes between non-consecutive degrees. -/
lemma internalHomd_eq_zero (K L : CochainComplex A ℤ) (n m : ℤ) (h : ¬ n + 1 = m) :
    internalHomd K L n m = 0 := by
  rw [internalHomd, dite_eq_right h]

/-- Two morphisms into a degree of `Hom•(K, L)` agree as soon as their uncurried factors do. -/
lemma internalHomX_hom_ext {Y : A} {K L : CochainComplex A ℤ} {n : ℤ}
    (f g : Y ⟶ internalHomX K L n)
    (h : ∀ p, uncurry (f ≫ internalHomπ K L n p) = uncurry (g ≫ internalHomπ K L n p)) :
    f = g :=
  Pi.hom_ext _ _ fun p => uncurry_injective (h p)

/-! ## The differential squares to zero

Of the four composites in `d ≫ d`, two vanish -- the one that applies the differential of `L`
twice, and the one that precomposes with the differential of `K` twice -- while the remaining
two are both equal to `internalHomDD`, with opposite Koszul signs. -/

/-- The only composite surviving in `d ≫ d`: the differential of `K` precomposed after the
differential of `L`, read off the factor at `p + 1` and landing in the factor at `p`. -/
def internalHomDD (K L : CochainComplex A ℤ) (i k p : ℤ) :
    internalHomX K L i ⟶ (ihom (K.X p)).obj (L.X (p + k)) :=
  internalHomπ K L i (p + 1) ≫ (ihom (K.X (p + 1))).map (L.d (p + 1 + i) (p + k)) ≫
    (pre (K.d p (p + 1))).app (L.X (p + k))

/-- Precomposing with the differential of `K` and then applying the differential of `L` gives
`internalHomDD`. -/
lemma internalHomD₂_comp_ihom_map_d (K L : CochainComplex A ℤ) (i j k p : ℤ) (hij : i + 1 = j) :
    internalHomD₂ K L i j p hij ≫ (ihom (K.X p)).map (L.d (p + j) (p + k)) =
      internalHomDD K L i k p := by
  rw [internalHomD₂, internalHomDD]
  simp only [Category.assoc]
  rw [pre_comm_ihom_map, ← Functor.map_comp_assoc,
    HomologicalComplex.XIsoOfEq_hom_comp_d L (show p + 1 + i = p + j by omega) (p + k)]

/-- Applying the differential of `L` and then precomposing with the differential of `K` gives
the same term `internalHomDD`. -/
lemma internalHomD₁_comp_pre (K L : CochainComplex A ℤ) (i j k p : ℤ)
    (h : p + 1 + j = p + k) :
    internalHomD₁ K L i j (p + 1) ≫
        (ihom (K.X (p + 1))).map (L.XIsoOfEq h).hom ≫
        (pre (K.d p (p + 1))).app (L.X (p + k)) =
      internalHomDD K L i k p := by
  rw [internalHomD₁, internalHomDD]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, HomologicalComplex.d_comp_XIsoOfEq_hom L h (p + 1 + i)]

variable [MonoidalPreadditive A]

/-- Applying the differential of `L` twice gives zero. -/
lemma internalHomD₁_comp_ihom_map_d (K L : CochainComplex A ℤ) (i j k p : ℤ) :
    internalHomD₁ K L i j p ≫ (ihom (K.X p)).map (L.d (p + j) (p + k)) = 0 := by
  rw [internalHomD₁, Category.assoc, ← Functor.map_comp,
    HomologicalComplex.d_comp_d L (p + i) (p + j) (p + k), Functor.map_zero, comp_zero]

/-- Precomposing twice with the differential of `K` gives zero, because `pre` sends
`d ≫ d = 0` to zero. -/
lemma internalHomD₂_comp_pre (K L : CochainComplex A ℤ) (i j k p : ℤ) (hij : i + 1 = j)
    (h : p + 1 + j = p + k) :
    internalHomD₂ K L i j (p + 1) hij ≫
        (ihom (K.X (p + 1))).map (L.XIsoOfEq h).hom ≫
        (pre (K.d p (p + 1))).app (L.X (p + k)) = 0 := by
  rw [internalHomD₂]
  simp only [Category.assoc]
  rw [reassoc_of% pre_comm_ihom_map, pre_app_comp,
    HomologicalComplex.d_comp_d K p (p + 1) (p + 1 + 1), pre_app_zero, comp_zero, comp_zero,
    comp_zero]

/-- The differential followed by the `L`-half of the next differential. -/
lemma internalHomd_comp_D₁ (K L : CochainComplex A ℤ) (i j k p : ℤ) (hij : i + 1 = j) :
    internalHomd K L i j ≫ internalHomD₁ K L j k p =
      (j.negOnePow : ℤˣ) • internalHomDD K L i k p := by
  rw [internalHomD₁, internalHomd_π_assoc K L i j hij p, Preadditive.add_comp,
    Linear.units_smul_comp, internalHomD₁_comp_ihom_map_d,
    internalHomD₂_comp_ihom_map_d K L i j k p hij, zero_add]

/-- The differential followed by the `K`-half of the next differential. -/
lemma internalHomd_comp_D₂ (K L : CochainComplex A ℤ) (i j k p : ℤ) (hij : i + 1 = j)
    (hjk : j + 1 = k) :
    internalHomd K L i j ≫ internalHomD₂ K L j k p hjk = internalHomDD K L i k p := by
  rw [internalHomD₂, internalHomd_π_assoc K L i j hij (p + 1), Preadditive.add_comp,
    Linear.units_smul_comp, internalHomD₁_comp_pre K L i j k p,
    internalHomD₂_comp_pre K L i j k p hij, smul_zero, add_zero]

/-- **The internal Hom complex** `Hom•(K, L)` of two cochain complexes in a monoidal closed
additive category: its degree-`n` term is the product `∏_p ihom (K.X p) (L.X (p + n))` and its
differential is the Koszul differential `f ↦ d_L ∘ f + (-1)^(n+1) f ∘ d_K`. -/
@[sga "4 XVII 1.1.10" "(ii)"]
def internalHomComplex (K L : CochainComplex A ℤ) : CochainComplex A ℤ where
  X n := internalHomX K L n
  d n m := internalHomd K L n m
  shape _ _ h := internalHomd_eq_zero K L _ _ h
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    have hsign : (k.negOnePow : ℤˣ) = -(j.negOnePow : ℤˣ) := by
      rw [← hjk', Int.negOnePow_succ]
    refine Pi.hom_ext _ _ fun p => ?_
    rw [zero_comp, Category.assoc, internalHomd_π K L j k hjk' p, Preadditive.comp_add,
      Linear.comp_units_smul, internalHomd_comp_D₁ K L i j k p hij',
      internalHomd_comp_D₂ K L i j k p hij' hjk', hsign, Units.smul_def, Units.smul_def,
      Units.val_neg, neg_smul, add_neg_cancel]

/-- The projection of the degree-`n` term of the complex `Hom•(K, L)` onto its factor at `p`.
This is `internalHomπ` with its source retyped as a term of the complex. -/
abbrev internalHomComplexπ (K L : CochainComplex A ℤ) (n p : ℤ) :
    (internalHomComplex K L).X n ⟶ (ihom (K.X p)).obj (L.X (p + n)) :=
  internalHomπ K L n p

/-- Two morphisms into a degree of the complex `Hom•(K, L)` agree as soon as their uncurried
factors do. -/
lemma internalHomComplex_hom_ext {Y : A} {K L : CochainComplex A ℤ} {n : ℤ}
    (f g : Y ⟶ (internalHomComplex K L).X n)
    (h : ∀ p, uncurry (f ≫ internalHomComplexπ K L n p) =
      uncurry (g ≫ internalHomComplexπ K L n p)) :
    f = g :=
  internalHomX_hom_ext f g h

/-- The differential of `Hom•(K, L)`, factor by factor: on the factor at `p` it is `ihom (K.X p)`
applied to the differential of `L`, plus `(-1)^m` times precomposition with the differential of
`K` read off the factor at `p + 1`. This determines the differential, since the projections are
jointly monomorphic. -/
@[reassoc, sga "4 XVII 1.1.10" "more general"]
lemma internalHomComplex_d_π (K L : CochainComplex A ℤ) (n m : ℤ) (h : n + 1 = m) (p : ℤ) :
    (internalHomComplex K L).d n m ≫ internalHomComplexπ K L m p =
      internalHomComplexπ K L n p ≫ (ihom (K.X p)).map (L.d (p + n) (p + m)) +
        (m.negOnePow : ℤˣ) • (internalHomComplexπ K L n (p + 1) ≫
          (ihom (K.X (p + 1))).map (L.XIsoOfEq (show p + 1 + n = p + m by omega)).hom ≫
          (pre (K.d p (p + 1))).app (L.X (p + m))) :=
  internalHomd_π K L n m h p

/-! ## The transposed differential condition

A morphism `g : L ⟶ Hom•(K, M)` is the same data as a family of morphisms
`K^p ⊗ L^q ⟶ M^(p+q)`, obtained by projecting onto the factor at `p` and uncurrying. The
content of `uncurryComp_comm` is the transposed form of the condition that `g` commute with the
differentials; the Koszul signs of the Hom differential and of the total tensor differential are
exactly matched to make it equivalent to the corresponding condition on `K ⊗ L ⟶ M`. -/

/-- Uncurrying the factor at `p` of a morphism into `Hom•(K, M)` followed by the differential,
in terms of the factors of the morphism at `p` and `p + 1`. -/
private lemma uncurry_comp_d_comp_π {K M : CochainComplex A ℤ} {Y : A} {q : ℤ}
    (y : Y ⟶ (internalHomComplex K M).X q) (p : ℤ) :
    uncurry ((y ≫ (internalHomComplex K M).d q (q + 1)) ≫ internalHomComplexπ K M (q + 1) p) =
      uncurry (y ≫ internalHomComplexπ K M q p) ≫ M.d (p + q) (p + (q + 1)) +
        ((q + 1).negOnePow : ℤˣ) • (K.d p (p + 1) ▷ Y ≫
          uncurry (y ≫ internalHomComplexπ K M q (p + 1)) ≫
          (M.XIsoOfEq (show p + 1 + q = p + (q + 1) by omega)).hom) := by
  rw [Category.assoc, internalHomComplex_d_π K M q (q + 1) rfl p,
    Preadditive.comp_add, Linear.comp_units_smul, uncurry_add, uncurry_units_smul,
    ← Category.assoc y (internalHomComplexπ K M q p), uncurry_natural_right,
    ← Category.assoc y (internalHomComplexπ K M q (p + 1)),
    ← Category.assoc (y ≫ internalHomComplexπ K M q (p + 1)),
    uncurry_pre_app, uncurry_natural_right]

/-- The `(p, q)` component of the uncurrying of `g : L ⟶ Hom•(K, M)`: project the degree-`q`
component of `g` onto the factor at `p`, then uncurry. -/
def uncurryComp (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M) (p q : ℤ) :
    K.X p ⊗ L.X q ⟶ M.X (p + q) :=
  uncurry (g.f q ≫ internalHomComplexπ K M q p)

/-- The transposed form of the statement that `g : L ⟶ Hom•(K, M)` commutes with the
differentials: the degree-`q` component of the Koszul differential becomes the differential of
`M` applied after `g`, plus a sign times `g` precomposed with the differential of `K`. -/
lemma uncurryComp_comm (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M) (p q : ℤ) :
    uncurryComp K L M g p q ≫ M.d (p + q) (p + (q + 1)) +
        ((q + 1).negOnePow : ℤˣ) • (K.d p (p + 1) ▷ L.X q ≫ uncurryComp K L M g (p + 1) q ≫
          (M.XIsoOfEq (show p + 1 + q = p + (q + 1) by omega)).hom) =
      K.X p ◁ L.d q (q + 1) ≫ uncurryComp K L M g p (q + 1) := by
  have key : uncurry ((g.f q ≫ (internalHomComplex K M).d q (q + 1)) ≫
      internalHomComplexπ K M (q + 1) p) =
        uncurry ((L.d q (q + 1) ≫ g.f (q + 1)) ≫ internalHomComplexπ K M (q + 1) p) := by
    rw [g.comm q (q + 1)]
  rwa [uncurry_comp_d_comp_π, Category.assoc (L.d q (q + 1)) (g.f (q + 1)),
    uncurry_natural_left (L.d q (q + 1)) (g.f (q + 1) ≫ internalHomComplexπ K M (q + 1) p)] at key

/-! ## Two Koszul sign identities -/

/-- `(-1)^((p+1)q) = -(-1)^(pq) (-1)^(q+1)`. -/
lemma negOnePow_succ_mul (p q : ℤ) :
    (((p + 1) * q).negOnePow : ℤˣ) = -(((p * q).negOnePow : ℤˣ) * ((q + 1).negOnePow : ℤˣ)) := by
  rw [← Int.negOnePow_add, show p * q + (q + 1) = (p + 1) * q + 1 by ring, Int.negOnePow_succ,
    neg_neg]

/-- `(-1)^p (-1)^(p(q+1)) = (-1)^(pq)`. -/
lemma negOnePow_mul_succ (p q : ℤ) :
    (p.negOnePow : ℤˣ) * ((p * (q + 1)).negOnePow : ℤˣ) = ((p * q).negOnePow : ℤˣ) := by
  rw [← Int.negOnePow_add, show p + p * (q + 1) = p * q + 2 * p by ring, Int.negOnePow_add,
    Int.negOnePow_two_mul, mul_one]

/-- `(-1)^(pq) (-1)^p = (-1)^(p(q+1))`. -/
lemma negOnePow_mul_mul_succ (p q : ℤ) :
    ((p * q).negOnePow : ℤˣ) * (p.negOnePow : ℤˣ) = ((p * (q + 1)).negOnePow : ℤˣ) := by
  rw [← Int.negOnePow_add, show p * q + p = p * (q + 1) by ring]

/-- `(-1)^(q+1) (-1)^((p+1)q) = -(-1)^(pq)`. -/
lemma negOnePow_succ_mul_succ_mul (p q : ℤ) :
    ((q + 1).negOnePow : ℤˣ) * (((p + 1) * q).negOnePow : ℤˣ) = -((p * q).negOnePow : ℤˣ) := by
  rw [← Int.negOnePow_add, show q + 1 + (p + 1) * q = p * q + 1 + 2 * q by ring,
    Int.negOnePow_add, Int.negOnePow_two_mul, mul_one, Int.negOnePow_succ]

/-! ## The tensor side -/

section Tensor

variable [HasZeroObject A]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

omit [MonoidalClosed A] [HasProductsOfShape ℤ A] in
/-- On the summand `K^p ⊗ L^q` of `(K ⊗ L)^n`, the total differential is
`d_K ▷ L^q + (-1)^p (K^p ◁ d_L)`, the first term landing in the summand of bidegree
`(p + 1, q)` and the second in the summand of bidegree `(p, q + 1)`. -/
@[reassoc]
lemma ιTensorObj_comp_d (K L : CochainComplex A ℤ) (p q n n' : ℤ) (h : p + q = n)
    (hn : n + 1 = n') :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (K ⊗ L).d n n' =
      K.d p (p + 1) ▷ L.X q ≫ HomologicalComplex.ιTensorObj K L (p + 1) q n' (by omega) +
        (p.negOnePow : ℤˣ) • (K.X p ◁ L.d q (q + 1) ≫
          HomologicalComplex.ιTensorObj K L p (q + 1) n' (by omega)) := by
  change HomologicalComplex.ιMapBifunctor K L (curriedTensor A) (ComplexShape.up ℤ) p q n h ≫
    (HomologicalComplex.mapBifunctor K L (curriedTensor A) (ComplexShape.up ℤ)).d n n' = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq K L _ _
      (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q n' (by change p + 1 + q = n'; omega),
    HomologicalComplex.mapBifunctor.d₂_eq K L _ _ p
      (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) n' (by change p + (q + 1) = n'; omega)]
  simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, one_smul,
    curriedTensor_map_app, curriedTensor_obj_map]

/-! ### Uncurrying a morphism into the internal Hom complex -/

/-- The degree-`n` component of the uncurried morphism `K ⊗ L ⟶ M` attached to
`g : L ⟶ Hom•(K, M)`: on the summand of bidegree `(p, q)` it is the Koszul sign `(-1)^(pq)`
times the `(p, q)` component of `g`. -/
def uncurryHomX (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M) (n : ℤ) :
    (K ⊗ L).X n ⟶ M.X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h =>
    ((p * q).negOnePow : ℤˣ) • (uncurryComp K L M g p q ≫
      (M.XIsoOfEq (show p + q = n from h)).hom)

/-- `uncurryHomX` on the summand of bidegree `(p, q)`. -/
@[reassoc]
lemma ι_uncurryHomX (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ uncurryHomX K L M g n =
      ((p * q).negOnePow : ℤˣ) • (uncurryComp K L M g p q ≫ (M.XIsoOfEq h).hom) :=
  HomologicalComplex.ι_mapBifunctorDesc _ p q h

/-- The uncurried family of a morphism into `Hom•(K, M)` commutes with the differentials: this
is `uncurryComp_comm` read on the summands of the total tensor complex. -/
lemma uncurryHomX_comm (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M)
    (n n' : ℤ) (hn : n + 1 = n') :
    uncurryHomX K L M g n ≫ M.d n n' = (K ⊗ L).d n n' ≫ uncurryHomX K L M g n' := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hpq : p + q = n := h
  rw [ι_uncurryHomX_assoc K L M g p q n hpq, ιTensorObj_comp_d_assoc K L p q n n' hpq hn]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
  rw [ι_uncurryHomX K L M g (p + 1) q n' (by omega),
    ι_uncurryHomX K L M g p (q + 1) n' (by omega)]
  simp only [Linear.comp_units_smul]
  rw [HomologicalComplex.XIsoOfEq_hom_comp_d M hpq n']
  have h1 := congrArg (fun z => z ≫ (M.XIsoOfEq (show p + (q + 1) = n' by omega)).hom)
    (uncurryComp_comm K L M g p q)
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    HomologicalComplex.d_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom] at h1
  rw [smul_smul, negOnePow_mul_succ, negOnePow_succ_mul, ← h1, smul_add, smul_smul]
  simp only [Units.smul_def, Units.val_neg, neg_smul]
  abel

/-- The morphism `K ⊗ L ⟶ M` attached to `g : L ⟶ Hom•(K, M)` by uncurrying. -/
def uncurryHom (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M) : K ⊗ L ⟶ M where
  f n := uncurryHomX K L M g n
  comm' n n' hnn' := uncurryHomX_comm K L M g n n' hnn'

/-! ### Currying a morphism out of the tensor product -/

/-- The `(p, q)` component of a morphism `f : K ⊗ L ⟶ M`: restrict to the summand of bidegree
`(p, q)` of the degree-`(p+q)` term. -/
def curryComp (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (p q : ℤ) :
    K.X p ⊗ L.X q ⟶ M.X (p + q) :=
  HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫ f.f (p + q)

omit [MonoidalClosed A] [HasProductsOfShape ℤ A] in
/-- The restriction of `f` to the summand of bidegree `(p, q)` of any degree is its `(p, q)`
component, reindexed. -/
@[reassoc]
lemma ιTensorObj_comp_f (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ f.f n =
      curryComp K L M f p q ≫ (M.XIsoOfEq h).hom := by
  subst h
  simp [curryComp]

omit [MonoidalClosed A] [HasProductsOfShape ℤ A] in
/-- The transposed differential condition for the family attached to `f : K ⊗ L ⟶ M`, obtained
from `ιTensorObj_comp_d` by restricting `f.comm` to a summand. -/
lemma curryComp_comm (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (p q : ℤ) :
    curryComp K L M f p q ≫ M.d (p + q) (p + (q + 1)) =
      K.d p (p + 1) ▷ L.X q ≫ curryComp K L M f (p + 1) q ≫
          (M.XIsoOfEq (show p + 1 + q = p + (q + 1) by omega)).hom +
        (p.negOnePow : ℤˣ) • (K.X p ◁ L.d q (q + 1) ≫ curryComp K L M f p (q + 1)) := by
  have key := congrArg (fun z => HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫ z)
    (f.comm (p + q) (p + (q + 1)))
  rw [← Category.assoc,
    ιTensorObj_comp_d_assoc K L p q (p + q) (p + (q + 1)) rfl (by omega)] at key
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc] at key
  rw [ιTensorObj_comp_f K L M f (p + 1) q (p + (q + 1)) (by omega),
    ιTensorObj_comp_f K L M f p (q + 1) (p + (q + 1)) (by omega)] at key
  simpa [curryComp] using key

/-- The degree-`q` component of the curried morphism `L ⟶ Hom•(K, M)` attached to
`f : K ⊗ L ⟶ M`: the factor at `p` is the Koszul sign `(-1)^(pq)` times the curried `(p, q)`
component of `f`. -/
def curryHomX (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (q : ℤ) :
    L.X q ⟶ (internalHomComplex K M).X q :=
  Pi.lift fun p => ((p * q).negOnePow : ℤˣ) • curry (curryComp K L M f p q)

/-- The uncurried factors of `curryHomX` are the components of `f`, up to the Koszul sign. -/
lemma uncurry_curryHomX_π (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (p q : ℤ) :
    uncurry (curryHomX K L M f q ≫ internalHomComplexπ K M q p) =
      ((p * q).negOnePow : ℤˣ) • curryComp K L M f p q := by
  have hπ : curryHomX K L M f q ≫ internalHomComplexπ K M q p =
      ((p * q).negOnePow : ℤˣ) • curry (curryComp K L M f p q) :=
    Pi.lift_π (fun p => ((p * q).negOnePow : ℤˣ) • curry (curryComp K L M f p q)) p
  rw [hπ, uncurry_units_smul, uncurry_curry]

/-- The curried family of a morphism out of `K ⊗ L` commutes with the Koszul differential: this
is `curryComp_comm` read on the factors of the internal Hom complex. -/
lemma curryHomX_comm (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (q q' : ℤ) (hq : q + 1 = q') :
    curryHomX K L M f q ≫ (internalHomComplex K M).d q q' =
      L.d q q' ≫ curryHomX K L M f q' := by
  subst hq
  refine internalHomComplex_hom_ext _ _ fun p => ?_
  rw [uncurry_comp_d_comp_π, Category.assoc (L.d q (q + 1)) (curryHomX K L M f (q + 1)),
    uncurry_natural_left (L.d q (q + 1))
      (curryHomX K L M f (q + 1) ≫ internalHomComplexπ K M (q + 1) p),
    uncurry_curryHomX_π, uncurry_curryHomX_π, uncurry_curryHomX_π]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [curryComp_comm, smul_add, smul_smul, negOnePow_mul_mul_succ, negOnePow_succ_mul_succ_mul]
  simp only [Units.smul_def, Units.val_neg, neg_smul]
  abel

/-- The morphism `L ⟶ Hom•(K, M)` attached to `f : K ⊗ L ⟶ M` by currying. -/
def curryHom (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) : L ⟶ internalHomComplex K M where
  f q := curryHomX K L M f q
  comm' q q' hqq' := curryHomX_comm K L M f q q' hqq'

/-- The uncurried components of `curryHom f` are those of `f`, up to the Koszul sign. -/
lemma uncurryComp_curryHom (K L M : CochainComplex A ℤ) (f : K ⊗ L ⟶ M) (p q : ℤ) :
    uncurryComp K L M (curryHom K L M f) p q =
      ((p * q).negOnePow : ℤˣ) • curryComp K L M f p q :=
  uncurry_curryHomX_π K L M f p q

/-! ### The adjunction -/

/-- **The tensor-Hom transposition** `(K ⊗ L ⟶ M) ≃ (L ⟶ Hom•(K, M))`: on the summand of
bidegree `(p, q)` it is the transposition of `A`, twisted by the Koszul sign `(-1)^(pq)`. -/
def internalHomEquiv (K L M : CochainComplex A ℤ) :
    (K ⊗ L ⟶ M) ≃ (L ⟶ internalHomComplex K M) where
  toFun f := curryHom K L M f
  invFun g := uncurryHom K L M g
  left_inv f := by
    ext n
    refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
    have hpq : p + q = n := h
    rw [show (uncurryHom K L M (curryHom K L M f)).f n = uncurryHomX K L M (curryHom K L M f) n
        from rfl, ι_uncurryHomX K L M (curryHom K L M f) p q n hpq,
      ιTensorObj_comp_f K L M f p q n hpq, uncurryComp_curryHom, Linear.units_smul_comp,
      smul_smul, Int.units_mul_self, one_smul]
  right_inv g := by
    ext q
    refine internalHomComplex_hom_ext _ _ fun p => ?_
    rw [show (curryHom K L M (uncurryHom K L M g)).f q = curryHomX K L M (uncurryHom K L M g) q
        from rfl, uncurry_curryHomX_π, curryComp,
      show (uncurryHom K L M g).f (p + q) = uncurryHomX K L M g (p + q) from rfl,
      ι_uncurryHomX K L M g p q (p + q) rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id, smul_smul, Int.units_mul_self, one_smul]
    rfl

/-- The inverse transposition on the summand of bidegree `(p, q)`: it is uncurrying, up to the
Koszul sign `(-1)^(pq)`. This pins the transposition down. -/
@[reassoc]
lemma ι_internalHomEquiv_symm (K L M : CochainComplex A ℤ) (g : L ⟶ internalHomComplex K M)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ ((internalHomEquiv K L M).symm g).f n =
      ((p * q).negOnePow : ℤˣ) • (uncurryComp K L M g p q ≫ (M.XIsoOfEq h).hom) :=
  ι_uncurryHomX K L M g p q n h

/-- Currying is natural in the second variable of the tensor product. -/
lemma curryHom_naturality (K : CochainComplex A ℤ) {L L' M : CochainComplex A ℤ}
    (φ : L' ⟶ L) (g : K ⊗ L ⟶ M) :
    curryHom K L' M (K ◁ φ ≫ g) = φ ≫ curryHom K L M g := by
  ext q
  refine internalHomComplex_hom_ext _ _ fun p => ?_
  rw [show (curryHom K L' M (K ◁ φ ≫ g)).f q = curryHomX K L' M (K ◁ φ ≫ g) q from rfl,
    uncurry_curryHomX_π,
    show (φ ≫ curryHom K L M g).f q = φ.f q ≫ curryHomX K L M g q from rfl, Category.assoc,
    uncurry_natural_left, uncurry_curryHomX_π, curryComp, curryComp, HomologicalComplex.comp_f,
    ← Category.assoc, ιTensorObj_whiskerLeft K φ p q (p + q) rfl, Category.assoc,
    Linear.comp_units_smul]

/-- The transposition is natural in the second variable of the tensor product. -/
lemma internalHomEquiv_naturality (K : CochainComplex A ℤ) {L L' M : CochainComplex A ℤ}
    (φ : L' ⟶ L) (g : K ⊗ L ⟶ M) :
    internalHomEquiv K L' M (K ◁ φ ≫ g) = φ ≫ internalHomEquiv K L M g :=
  curryHom_naturality K φ g

section Closed

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- **`Hom•(K, -)` is right adjoint to `K ⊗ -`.** -/
@[instance_reducible]
def internalHomClosed (K : CochainComplex A ℤ) : Closed K where
  rightAdj := Adjunction.rightAdjointOfEquiv (F := tensorLeft K)
    (G_obj := fun M => internalHomComplex K M) (fun L M => internalHomEquiv K L M)
    (fun _ _ _ φ g => internalHomEquiv_naturality K φ g)
  adj := Adjunction.adjunctionOfEquivRight _ _

/-- The adjunction `K ⊗ - ⊣ Hom•(K, -)` on cochain complexes. -/
def internalHomAdjunction (K : CochainComplex A ℤ) :
    tensorLeft K ⊣ (internalHomClosed K).rightAdj :=
  (internalHomClosed K).adj

/-- **Cochain complexes in a monoidal closed additive category are monoidal closed**, with
internal hom the internal Hom complex `Hom•(K, -)`.

This is deliberately not an instance: see the module documentation. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed (CochainComplex A ℤ) where
  closed K := internalHomClosed K

end Closed

end Tensor

end

end CochainComplex

end
