module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.FlatLocalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulay proper intersections on a smooth scheme

Let `k` be a field, let `X` be an integral scheme smooth over `k`, and let `i : Y ⟶ X` and
`j : Z ⟶ X` be integral closed subschemes, of dimensions `dY` and `dZ`, with `dX = dim X` and
`d = dY + dZ - dX`. Assume that `dim (Y ∩ Z) ≤ d` and that `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are
Cohen–Macaulay at every point `ξ` of `Y ∩ Z` with `δ(ξ) = d`.

The source deduces `[Y] · [Z] = [Y ∩ Z]_d` from the higher-codimension Gysin formula of Stacks
0FEA, applied to the diagonal `Δ : X ⟶ X ×_k X`, its virtual normal sheaf `𝒯_{X/k}`, and the
morphism `Y ×_k Z ⟶ X ×_k X`. The work in that deduction is the verification of the hypotheses
of 0FEA, and that verification is what this file carries out: the scheme-theoretic
identification `Y ∩ Z = X ×_{Δ, X ×_k X} (Y ×_k Z)`, the dimension of `Y ×_k Z`, the resulting
bound on the dimension of the Gysin source, and the Cohen–Macaulayness of the local rings of
`Y ×_k Z` at the top-dimensional points of the intersection.

## Main definitions

* `Stacks.Chow.Intersection.intersectionToProduct`: the morphism `Y ×_X Z ⟶ Y ×_k Z`, i.e. the
  inclusion of the scheme-theoretic intersection into the product.
* `Stacks.Chow.Intersection.diagonalPullback`: the scheme `X ×_{Δ, X ×_k X} (Y ×_k Z)`, which is
  the source of the Gysin class `c(Δ ⟶ X ×_k X, 𝒯_{X/k})` evaluated on `[Y ×_k Z]`.
* `Stacks.Chow.Intersection.diagonalPullbackIso`: the identification of that scheme with the
  scheme-theoretic intersection `Y ∩ Z = Y ×_X Z`.
* `Stacks.Chow.Intersection.CohenMacaulayAtIntersection`: hypothesis (2) of Stacks 0FFD.
* `Stacks.Chow.Intersection.ProductStalkCohenMacaulay`: the scheme-level form of Stacks 045J
  used at this point of the source, proved as
  `Stacks.Chow.Intersection.productStalkCohenMacaulay`; see the implementation notes.
* `Stacks.Chow.Intersection.GysinFormulaHypotheses`: hypotheses (2), (3) and (4) of Stacks 0FEA,
  instantiated at the diagonal of `X ⟶ Spec k` and at the morphism `Y ×_k Z ⟶ X ×_k X`.

## Main results

* `Stacks.Chow.Intersection.topologicalKrullDim_diagonalPullback`: the dimension of
  `X ×_{Δ, X ×_k X} (Y ×_k Z)` is the dimension of `Y ∩ Z`.
* `Stacks.Chow.Intersection.productStalkCohenMacaulay`: `ProductStalkCohenMacaulay` holds, i.e.
  Cohen–Macaulayness of the local rings of `Y` and `Z` at the images of a point of `Y ×_k Z`
  gives Cohen–Macaulayness of the local ring of `Y ×_k Z` there.
* `Stacks.Chow.Intersection.gysinFormulaHypotheses_of_cohenMacaulayAtIntersection'`: under the
  two hypotheses of Stacks 0FFD and nothing else, the hypotheses of the Gysin formula of Stacks
  0FEA hold. `Stacks.Chow.Intersection.gysinFormulaHypotheses_of_cohenMacaulayAtIntersection` is
  the same statement with `ProductStalkCohenMacaulay` taken as a further hypothesis.

## Implementation notes

**What is not stated.** The conclusion `[Y] · [Z] = [Y ∩ Z]_d` of the source is not stated here,
because neither side of the intersection product of Stacks 0FC0 exists in this repository. As
the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin` record, the
bivariant class `Δ^!` is not constructible here: the higher-codimension Gysin class
`c(Z ⟶ X, 𝒩)` of Stacks 0FBK, the flat-pullback bivariant class of Stacks 0B78 and a
construction of the composition of bivariant classes of Stacks 0B75 are all absent. The
statement of Stacks 0FEA, which the source quotes to conclude, is absent for the same reason:
it is an identity between a cap product by `c(Z ⟶ X, 𝒩)` and a fundamental class. What remains
of the source's proof once that identity is quoted is the verification of the hypotheses of
0FEA, and that verification is complete here.

Hypothesis (1) of Stacks 0FEA, that the virtual normal sheaf is locally free of rank
`r = dim X`, is a statement about `𝒯_{X/k} = Hom(Ω_{X/k}, 𝒪_X)`; it concerns the datum
`Stacks.Chow.VirtualNormalBundle` of Stacks 0FBQ rather than the situation `(X, Y, Z)`, and the
repository has no tangent sheaf, so it is not among the clauses of
`GysinFormulaHypotheses`. The two halves it would be built from are present:
`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_relativeDifferentials` (Stacks 02G1) and
`AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt`.

**Nothing is carried.** `ProductStalkCohenMacaulay` states the step the source performs by
quoting Algebra, Lemma 10.163.3 (Stacks 045J): for a point `ζ` of `Y ×_k Z`, Cohen–Macaulayness
of `𝒪_{Y,·}` and `𝒪_{Z,·}` at the two images of `ζ` implies Cohen–Macaulayness of
`𝒪_{Y ×_k Z, ζ}`. It is proved as `productStalkCohenMacaulay`, and
`gysinFormulaHypotheses_of_cohenMacaulayAtIntersection'` therefore takes only hypotheses (1) and
(2) of the source. `gysinFormulaHypotheses_of_cohenMacaulayAtIntersection` keeps it as an
explicit hypothesis, which is how it was first stated.

The proof does not follow the source's ring-level route, and that is deliberate. The source
reads 045J on the flat local homomorphism `𝒪_{Y,ζ} ⟶ 𝒪_{Y ×_k Z, ζ}`, whose fibre is a
localization of `κ(ζ) ⊗_k 𝒪_{Z,ζ}`, and identifies that fibre's Cohen–Macaulayness with
`Algebra.TensorProduct.isMaximalCohenMacaulay_self_iff_of_essFiniteType` (Stacks 045N). Both
ring-level lemmas need the local ring of the product presented as a localization of a tensor
product *at a prime*, and the only presentation available here,
`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`, localizes at an unnamed
submonoid. The route taken instead stays at the level of morphisms, where that presentation has
already been digested: the structure morphism `Y ⟶ Spec k` is Cohen–Macaulay at the first image
of `ζ`, being flat with the source itself for its fibre
(`AlgebraicGeometry.isIso_fiberι_of_isIso_fromSpecResidueField`); Cohen–Macaulayness of a
morphism at a point survives the locally finite type base change along `Z ⟶ Spec k`
(`AlgebraicGeometry.isCohenMacaulayAt_pullback`, Stacks 045T (1)), so `Y ×_k Z ⟶ Z` is
Cohen–Macaulay at `ζ`; and Cohen–Macaulayness ascends from `𝒪_{Z, ·}` along that projection by
045J applied to its stalk map, whose fibre is the local ring of the scheme-theoretic fibre by
`AlgebraicGeometry.quotientStalkEquivFiberStalk`. That last ascent is the private
`isCohenMacaulayLocalRing_stalk_of_isCohenMacaulayAt`, the converse direction of the equivalence
that `AlgebraicGeometry.isCohenMacaulay_of_isCohenMacaulay_source` (Stacks 0C0X) uses.

**Dimensions.** The dimension of a scheme is its topological Krull dimension, with values in
`WithBot ℕ∞`; the `δ`-dimension of a point is `Stacks.Chow.relativeDimension` for the
constant-zero dimension function of `Spec k`, which is the dimension function of
`Stacks.Chow.fieldChowSituation`. The dimension `dX` of `X` enters only through the equation
`dY + dZ = dX + d` defining `d`, so the hypothesis recording `dim X = dX` is unused and
underscored.

## References

* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 045J](https://stacks.math.columbia.edu/tag/045J)
* [Stacks Project, Tag 045N](https://stacks.math.columbia.edu/tag/045N)
* [Stacks Project, Tag 045T](https://stacks.math.columbia.edu/tag/045T)
* [Stacks Project, Tag 0C0X](https://stacks.math.columbia.edu/tag/0C0X)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.Intersection

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}

/-- Applying the underlying continuous maps to a factorization of scheme morphisms. -/
private theorem base_apply_comp {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C}
    (e : f ≫ g = h) (a : A) : g.base (f.base a) = h.base a := by
  subst e
  simp


/-- Cohen–Macaulayness of a local ring of a scheme transports along an equality of points. The
`rewrite` tactic cannot do this, because the `IsNoetherianRing` instance on the stalk depends on
the point being rewritten. -/
private theorem isCohenMacaulayLocalRing_stalk_of_eq {W : Scheme.{u}} [IsLocallyNoetherian W]
    {x y : W} (h : x = y)
    (hx : IsCohenMacaulayLocalRing (W.presheaf.stalk x)) :
    IsCohenMacaulayLocalRing (W.presheaf.stalk y) := by
  subst h
  exact hx

/-- Cohen–Macaulayness of a local ring at the image of a point under a factorization `f ≫ g = h`
follows from Cohen–Macaulayness at the image under `h`. -/
private theorem isCohenMacaulayLocalRing_stalk_of_comp {A B C : Scheme.{u}}
    [IsLocallyNoetherian C] {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (e : f ≫ g = h) (a : A)
    (hx : IsCohenMacaulayLocalRing (C.presheaf.stalk (h.base a))) :
    IsCohenMacaulayLocalRing (C.presheaf.stalk (g.base (f.base a))) := by
  subst e
  exact hx

/-- The scheme-theoretic intersection `Y ∩ Z = Y ×_X Z` sits inside the product `Y ×_k Z` over
the base field. -/
def intersectionToProduct (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) :
    (pullback i j : Scheme.{u}) ⟶ (pullback (i ≫ p) (j ≫ p) : Scheme.{u}) :=
  pullback.lift (pullback.fst i j) (pullback.snd i j)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])

/-- Composing `intersectionToProduct p i j` with the first projection of `Y ×_k Z` gives the first
projection of `Y ×_X Z`. -/
@[simp]
theorem intersectionToProduct_fst (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) :
    intersectionToProduct p i j ≫ pullback.fst (i ≫ p) (j ≫ p) = pullback.fst i j :=
  pullback.lift_fst _ _ _

/-- Composing `intersectionToProduct p i j` with the second projection of `Y ×_k Z` gives the
second projection of `Y ×_X Z`. -/
@[simp]
theorem intersectionToProduct_snd (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) :
    intersectionToProduct p i j ≫ pullback.snd (i ≫ p) (j ≫ p) = pullback.snd i j :=
  pullback.lift_snd _ _ _

/-- The scheme `X ×_{Δ, X ×_k X} (Y ×_k Z)`: the source of the Gysin class of the diagonal of
`p : X ⟶ Spec k` evaluated on the product `Y ×_k Z`. -/
abbrev diagonalPullback (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) : Scheme.{u} :=
  pullback (pullback.diagonal p)
    (pullback.map (i ≫ p) (j ≫ p) p p i j (𝟙 _) (Category.comp_id _) (Category.comp_id _))

/-- **Stacks Project, Tag 0FFD.** The scheme-theoretic identification
`Y ∩ Z = X ×_{Δ, X ×_k X} (Y ×_k Z)` used by the source to recognise the source of the Gysin
class as the intersection. It is the pullback square of Stacks 01KR expressing that
`Y ×_X Z ⟶ Y ×_k Z` is the base change of the diagonal along `Y ×_k Z ⟶ X ×_k X`. -/
@[stacks 0FFD "the scheme-theoretic identification `Y ∩ Z = X ×_{Δ, X ×_k X} (Y ×_k Z)`"]
def diagonalPullbackIso (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) :
    (diagonalPullback p i j) ≅ (pullback i j : Scheme.{u}) :=
  pullbackDiagonalMapIdIso i j p

/-- The dimension of `X ×_{Δ, X ×_k X} (Y ×_k Z)` is the dimension of the scheme-theoretic
intersection `Y ∩ Z`, because the two schemes are isomorphic. -/
theorem topologicalKrullDim_diagonalPullback (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) :
    topologicalKrullDim ↑(diagonalPullback p i j) =
      topologicalKrullDim ↑(pullback i j) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (diagonalPullbackIso p i j)).isHomeomorph

/-- **Hypothesis (2) of Stacks Project, Tag 0FFD.** The local rings `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are
Cohen–Macaulay at every point `ξ` of the intersection `Y ∩ Z` whose `δ`-dimension is `d`. -/
def CohenMacaulayAtIntersection (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (i : Y ⟶ X) [IsClosedImmersion i] (j : Z ⟶ X)
    [IsClosedImmersion j] (d : ℤ) : Prop :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  ∀ ζ : ↑(pullback i j),
    relativeDimension (fieldDimensionFunction k) (pullback.fst i j ≫ i ≫ p) ζ = d →
      IsCohenMacaulayLocalRing (Y.presheaf.stalk ((pullback.fst i j).base ζ)) ∧
        IsCohenMacaulayLocalRing (Z.presheaf.stalk ((pullback.snd i j).base ζ))

/-- **The carried form of Stacks Project, Tag 045J.** At a point of the product `Y ×_k Z`,
Cohen–Macaulayness of the local rings of the two factors at the two images of that point implies
Cohen–Macaulayness of the local ring of the product. See the implementation notes. -/
def ProductStalkCohenMacaulay (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (i : Y ⟶ X) [IsClosedImmersion i] (j : Z ⟶ X)
    [IsClosedImmersion j] : Prop :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  letI : IsLocallyNoetherian ↑(pullback (i ≫ p) (j ≫ p)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ p) (j ≫ p) ≫ i ≫ p)
  ∀ ζ : ↑(pullback (i ≫ p) (j ≫ p)),
    IsCohenMacaulayLocalRing (Y.presheaf.stalk ((pullback.fst (i ≫ p) (j ≫ p)).base ζ)) →
      IsCohenMacaulayLocalRing (Z.presheaf.stalk ((pullback.snd (i ≫ p) (j ≫ p)).base ζ)) →
        IsCohenMacaulayLocalRing
          ((pullback (i ≫ p) (j ≫ p) : Scheme.{u}).presheaf.stalk ζ)

/-- **Hypotheses (2), (3) and (4) of Stacks Project, Tag 0FEA**, instantiated as the source of
Stacks 0FFD does: the closed subscheme is the diagonal `Δ ⟶ X ×_k X`, the morphism locally of
finite type is `Y ×_k Z ⟶ X ×_k X`, the integer `n` is `dY + dZ` and the rank `r` is `dim X`, so
that `n - r = d`.

The three clauses are: the product `Y ×_k Z` has dimension `dY + dZ`; the source
`X ×_{Δ, X ×_k X} (Y ×_k Z)` of the Gysin class has dimension at most `d`; and the local ring of
`Y ×_k Z` is Cohen–Macaulay at every point of the intersection of `δ`-dimension `d`. -/
def GysinFormulaHypotheses (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (i : Y ⟶ X) [IsClosedImmersion i] (j : Z ⟶ X)
    [IsClosedImmersion j] (dY dZ d : ℕ) : Prop :=
  letI : IsLocallyNoetherian ↑(pullback (i ≫ p) (j ≫ p)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ p) (j ≫ p) ≫ i ≫ p)
  topologicalKrullDim ↑(pullback (i ≫ p) (j ≫ p)) =
      (dY : WithBot ℕ∞) + (dZ : WithBot ℕ∞) ∧
    topologicalKrullDim ↑(diagonalPullback p i j) ≤ (d : WithBot ℕ∞) ∧
      ∀ ζ : ↑(pullback i j),
        relativeDimension (fieldDimensionFunction k) (pullback.fst i j ≫ i ≫ p) ζ = (d : ℤ) →
          IsCohenMacaulayLocalRing
            ((pullback (i ≫ p) (j ≫ p) : Scheme.{u}).presheaf.stalk
              ((intersectionToProduct p i j).base ζ))

/-- **Stacks Project, Tag 0FFD.** Let `k` be a field, let `X` be an integral scheme smooth over
`k` of dimension `dX`, and let `Y, Z ⊆ X` be integral closed subschemes of dimensions `dY` and
`dZ`. Put `d = dY + dZ - dX`. Assume

1. `dim (Y ∩ Z) ≤ d`, and
2. `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are Cohen–Macaulay for every `ξ ∈ Y ∩ Z` with `δ(ξ) = d`.

Then the hypotheses of the higher-codimension Gysin formula of Stacks 0FEA hold for the diagonal
`Δ : X ⟶ X ×_k X` and the morphism `Y ×_k Z ⟶ X ×_k X`, which is what the source's proof
establishes before quoting that formula to conclude `[Y] · [Z] = [Y ∩ Z]_d`.

What this theorem covers of Stacks 0FFD, and what it does not: it is the reduction of the lemma
to Stacks 0FEA, namely the identification `Y ∩ Z = X ×_{Δ, X ×_k X} (Y ×_k Z)` together with the
verification of hypotheses (2), (3) and (4) of 0FEA at the diagonal of `X ⟶ Spec k`. The
conclusion `[Y] · [Z] = [Y ∩ Z]_d` is **not** stated, and neither is Stacks 0FEA itself, for the
reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin`. Hypothesis (1) of 0FEA concerns the virtual
normal sheaf `𝒯_{X/k}` of Stacks 0FBQ rather than the situation `(X, Y, Z)`, so it is not among
the clauses verified here. The scheme-level form of Stacks 045J that the source uses at exactly
this point is taken as the hypothesis `ProductStalkCohenMacaulay`; it is proved in
`productStalkCohenMacaulay`, and
`gysinFormulaHypotheses_of_cohenMacaulayAtIntersection'` is this statement with that hypothesis
discharged. -/
@[stacks 0FFD "the reduction of the lemma to Stacks 0FEA: the identification of the intersection \
with the diagonal pullback, and hypotheses (2), (3) and (4) of 0FEA at the diagonal of \
X → Spec k. Neither the conclusion [Y]·[Z] = [Y ∩ Z]_d nor 0FEA itself is stated; carries \
ProductStalkCohenMacaulay for Stacks 045J. The docstring says what is covered in full"]
theorem gysinFormulaHypotheses_of_cohenMacaulayAtIntersection (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p] [IsIntegral X]
    (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    (j : Z ⟶ X) [IsClosedImmersion j] [IsIntegral Z]
    (dX dY dZ d : ℕ)
    (_hXdim : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (hZdim : topologicalKrullDim Z = (dZ : WithBot ℕ∞))
    (_hd : dY + dZ = dX + d)
    (hIntDim : topologicalKrullDim ↑(pullback i j) ≤ (d : WithBot ℕ∞))
    (hCM : CohenMacaulayAtIntersection k p i j (d : ℤ))
    (hAscent : ProductStalkCohenMacaulay k p i j) :
    GysinFormulaHypotheses k p i j dY dZ d := by
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  refine ⟨?_, (topologicalKrullDim_diagonalPullback p i j).trans_le hIntDim,
    fun ζ hζ => hAscent ((intersectionToProduct p i j).base ζ)
      (isCohenMacaulayLocalRing_stalk_of_comp (intersectionToProduct_fst p i j) ζ (hCM ζ hζ).1)
      (isCohenMacaulayLocalRing_stalk_of_comp (intersectionToProduct_snd p i j) ζ (hCM ζ hζ).2)⟩
  rw [AlgebraicGeometry.topologicalKrullDim_pullback k (i ≫ p) (j ≫ p), hYdim, hZdim]

/-! ### Discharging the carried ascent -/

/-- **Ascent of Cohen–Macaulayness to a source local ring.** This is Stacks 045J read on the
stalks of a morphism of schemes: for `f : X ⟶ Y` Cohen–Macaulay at `x` — flat at `x` with
Cohen–Macaulay fibre local ring there — the local ring `𝒪_{X,x}` is Cohen–Macaulay as soon as
`𝒪_{Y, f x}` is.

The stalk map `𝒪_{Y, f x} → 𝒪_{X,x}` is a flat local homomorphism, and
`AlgebraicGeometry.quotientStalkEquivFiberStalk` identifies its fibre
`𝒪_{X,x} / 𝔪_{Y, f x} 𝒪_{X,x}` with the local ring of the scheme-theoretic fibre, so
`Module.isMaximalCohenMacaulay_self_iff_of_flat` applies with both of its right-hand clauses in
hand. It is the converse direction of the same equivalence that
`AlgebraicGeometry.isCohenMacaulay_of_isCohenMacaulay_source` (Stacks 0C0X) uses. -/
@[ega "IV 6.3.3" "special case", ega "IV 6.3.5" "more general", ega "IV 7.5.3" "more general"]
private theorem isCohenMacaulayLocalRing_stalk_of_isCohenMacaulayAt {W V : Scheme.{u}}
    (f : W ⟶ V) [IsLocallyNoetherian W] [IsLocallyNoetherian V]
    (hf : ∀ v : V, IsLocallyNoetherian (f.fiber v)) (w : W)
    (hV : IsCohenMacaulayLocalRing (V.presheaf.stalk (f.base w)))
    (h : Scheme.Hom.IsCohenMacaulayAt f hf w) :
    IsCohenMacaulayLocalRing (W.presheaf.stalk w) := by
  have := hf (f.base w)
  change IsFlatAt f.toLRSHom.toShHom w ∧
    IsCohenMacaulayLocalRing ((f.fiber (f.base w)).presheaf.stalk (f.asFiber w)) at h
  let A := V.presheaf.stalk (f.base w)
  let B := W.presheaf.stalk w
  let I : Ideal B := Ideal.map (f.stalkMap w).hom (IsLocalRing.maximalIdeal A)
  let Q := B ⧸ I
  let e : Q ≃+* (f.fiber (f.base w)).presheaf.stalk (f.asFiber w) :=
    quotientStalkEquivFiberStalk f w
  let _ : Algebra A B := (f.stalkMap w).hom.toAlgebra
  have : IsLocalHom (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have _ : Module.Flat A B := RingHom.flat_algebraMap_iff.mp h.1
  have hQsurj : Function.Surjective (algebraMap B Q) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have _ : Nontrivial Q := ⟨0, 1, fun hz => by simpa using congrArg e hz⟩
  have _ : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) hQsurj
  have hQdepth : (Module.depth B (IsLocalRing.maximalIdeal B) Q : WithBot ℕ∞) =
      ringKrullDim Q := by
    rw [Module.depth_eq_depth_self_of_surjective_algebraMap (A := B) (B := Q) hQsurj]
    exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay Q).mp
      ((isCohenMacaulayLocalRing_iff_of_ringEquiv e).mpr h.2)
  exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mpr
    ((Module.isMaximalCohenMacaulay_self_iff_of_flat A B).mpr
      ⟨(isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).mp hV, hQdepth⟩)

/-- A morphism to the spectrum of a field is Cohen–Macaulay at a point exactly where the local
ring of its source is Cohen–Macaulay: such a morphism is flat, and its scheme-theoretic fibres
are the source itself, because the residue field inclusions of `Spec k` are isomorphisms. -/
private theorem isCohenMacaulayAt_of_isCohenMacaulayLocalRing_stalk_over_field
    {W : Scheme.{u}} [IsLocallyNoetherian W] (f : W ⟶ Spec (.of k)) (w : W)
    (hW : IsCohenMacaulayLocalRing (W.presheaf.stalk w)) :
    Scheme.Hom.IsCohenMacaulayAt f (isLocallyNoetherian_fiber f) w := by
  have := isLocallyNoetherian_fiber f (f.base w)
  show IsFlatAt f.toLRSHom.toShHom w ∧
    IsCohenMacaulayLocalRing ((f.fiber (f.base w)).presheaf.stalk (f.asFiber w))
  refine ⟨(Flat.iff_flat_stalkMap f).mp inferInstance w, ?_⟩
  have hiso : IsIso (f.fiberι (f.base w)) :=
    isIso_fiberι_of_isIso_fromSpecResidueField f _ (isIso_fromSpecResidueField_of_field k _)
  have : IsIso ((f.fiberι (f.base w)).stalkMap (f.asFiber w)) :=
    ((isIso_iff_isIso_stalkMap (f.fiberι (f.base w))).mp hiso).2 _
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso ((f.fiberι (f.base w)).stalkMap (f.asFiber w))).commRingCatIsoToRingEquiv).mp
    (isCohenMacaulayLocalRing_stalk_of_eq (f.fiberι_asFiber w).symm hW)

/-- **The carried form of Stacks Project, Tag 045J, discharged.** At a point `ζ` of the product
`Y ×_k Z`, Cohen–Macaulayness of the local rings of the two factors at the images of `ζ` does
imply Cohen–Macaulayness of the local ring of the product at `ζ`.

The route is the source's, through Stacks 045J, but taken at the level of morphisms rather than
of rings, which is what sidesteps the presentation of the local ring of a fibre product that the
implementation notes record as missing. The structure morphism `Y ⟶ Spec k` is Cohen–Macaulay at
the first image of `ζ`, being flat with the source for its fibre; Cohen–Macaulayness of a
morphism at a point is preserved by the locally finite type base change along `Z ⟶ Spec k`
(Stacks 045T (1)), so the second projection `Y ×_k Z ⟶ Z` is Cohen–Macaulay at `ζ`; and
Cohen–Macaulayness then ascends from `𝒪_{Z, ·}` to `𝒪_{Y ×_k Z, ζ}` along it by Stacks 045J. -/
public theorem productStalkCohenMacaulay (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (i : Y ⟶ X) [IsClosedImmersion i] (j : Z ⟶ X)
    [IsClosedImmersion j] :
    ProductStalkCohenMacaulay k p i j := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  let : IsLocallyNoetherian ↑(pullback (i ≫ p) (j ≫ p)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ p) (j ≫ p) ≫ i ≫ p)
  intro ζ hY hZ
  exact isCohenMacaulayLocalRing_stalk_of_isCohenMacaulayAt
    (pullback.snd (i ≫ p) (j ≫ p)) _ ζ hZ
    (isCohenMacaulayAt_pullback (i ≫ p) (j ≫ p) (isLocallyNoetherian_fiber (i ≫ p)) ζ
      (isCohenMacaulayAt_of_isCohenMacaulayLocalRing_stalk_over_field (i ≫ p) _ hY))

/-- **Stacks Project, Tag 0FFD.** Let `k` be a field, let `X` be an integral scheme smooth over
`k` of dimension `dX`, and let `Y, Z ⊆ X` be integral closed subschemes of dimensions `dY` and
`dZ`. Put `d = dY + dZ - dX`. Assume

1. `dim (Y ∩ Z) ≤ d`, and
2. `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are Cohen–Macaulay for every `ξ ∈ Y ∩ Z` with `δ(ξ) = d`.

Then the hypotheses of the higher-codimension Gysin formula of Stacks 0FEA hold for the diagonal
`Δ : X ⟶ X ×_k X` and the morphism `Y ×_k Z ⟶ X ×_k X`, which is what the source's proof
establishes before quoting that formula to conclude `[Y] · [Z] = [Y ∩ Z]_d`.

This is `Stacks.Chow.Intersection.gysinFormulaHypotheses_of_cohenMacaulayAtIntersection` with
its carried hypothesis `ProductStalkCohenMacaulay` discharged by
`Stacks.Chow.Intersection.productStalkCohenMacaulay`, so hypotheses (1) and (2) of the source
are the only ones it takes. It states no more than that theorem does: the conclusion
`[Y] · [Z] = [Y ∩ Z]_d` is **not** stated, and neither is Stacks 0FEA itself, for the reason
recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin`; and hypothesis (1) of 0FEA, which concerns
the virtual normal sheaf `𝒯_{X/k}` of Stacks 0FBQ rather than the situation `(X, Y, Z)`, is not
among the clauses verified here. -/
@[stacks 0FFD "the reduction of the lemma to Stacks 0FEA from hypotheses (1) and (2) alone: the \
identification of the intersection with the diagonal pullback, and hypotheses (2), (3) and (4) \
of 0FEA at the diagonal of X → Spec k. Nothing is carried. Neither the conclusion \
[Y]·[Z] = [Y ∩ Z]_d nor 0FEA itself is stated, and hypothesis (1) of 0FEA, about the virtual \
normal sheaf, is not among the clauses. The docstring says what is covered in full"]
public theorem gysinFormulaHypotheses_of_cohenMacaulayAtIntersection' (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p] [IsIntegral X]
    (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    (j : Z ⟶ X) [IsClosedImmersion j] [IsIntegral Z]
    (dX dY dZ d : ℕ)
    (hXdim : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (hZdim : topologicalKrullDim Z = (dZ : WithBot ℕ∞))
    (hd : dY + dZ = dX + d)
    (hIntDim : topologicalKrullDim ↑(pullback i j) ≤ (d : WithBot ℕ∞))
    (hCM : CohenMacaulayAtIntersection k p i j (d : ℤ)) :
    GysinFormulaHypotheses k p i j dY dZ d :=
  gysinFormulaHypotheses_of_cohenMacaulayAtIntersection k p i j dX dY dZ d hXdim hYdim hZdim hd
    hIntDim hCM (productStalkCohenMacaulay k p i j)

end Stacks.Chow.Intersection

end
