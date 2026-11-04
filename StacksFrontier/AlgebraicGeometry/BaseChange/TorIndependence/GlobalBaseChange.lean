module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived base-change map attached to a map out of a derived pullback

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes, let `K` be an object of `D(𝒪_X)` and let
`φ : L(g')^*K ⟶ K'` be a morphism in `D(𝒪_{X'})`.  The composition

`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'`

of the derived base-change map of Stacks 08HY with the derived direct image of `φ` is the
morphism whose invertibility Stacks 0DJ9 asserts, under the pointwise condition of
Stacks 0DJ8 (1) and quasi-compactness and quasi-separatedness of `f`.

## Main definitions

* `AlgebraicGeometry.derivedBaseChangeComp`: the composition
  `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'`.
* `AlgebraicGeometry.PointwiseBaseChange`: condition (1) of Stacks 0DJ8, that the pointwise
  map of Stacks 0DJ7 on stalkwise cohomology is invertible at every point of `X'` and in every
  degree.
* `AlgebraicGeometry.PointwiseBaseChangeGlobalizes`: the carried input, the conclusion of
  Stacks 0DJ9 read over all cartesian squares at once.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeComp`: **Stacks 0DJ9**, that the composition is an
  isomorphism, granted `PointwiseBaseChangeGlobalizes`.
* `AlgebraicGeometry.derivedBaseChangeComp_comp`: naturality in the target of `φ`.
* `AlgebraicGeometry.derivedBaseChangeComp_id`: at `K' = L(g')^*K` and `φ` the identity the
  composition is the derived base-change map of Stacks 08HY itself.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_globalizes`: granted the same input, the
  derived base-change map of Stacks 08HY is invertible on a complex with quasi-coherent
  cohomology whose pointwise maps are invertible.  This is the form in which Stacks 08IB
  consumes Stacks 0DJ9; the quasi-coherence of `L(g')^*K` that it asks for is Stacks 08DW
  part (1).

## Implementation notes

*Why the globalization is carried.*  The source argument reduces to `g` a morphism of affine
schemes, runs the induction principle of Stacks 08DR over the quasi-compact opens of `X`,
settles the affine case from Stacks 0DJ8 (2) through Stacks 06Z0 and Stacks 08DW, and performs
the induction step with the four-row diagram of relative Mayer–Vietoris, Stacks 08HZ.  Neither
end of that is available yet.  The relative Mayer–Vietoris triangle is now available with its
five morphisms named, as
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardTriangle_distinguished`, so the diagram of
the induction step can be written; but those morphisms are functions of a
`Stacks.Cohomology.RelativeMayerVietoris.RelativeMayerVietorisSequence` term, and Stacks 01EC
supplies that datum only as a `Nonempty`, so the triangle on `X` and the triangle on `X'`
cannot be pinned to one canonical choice and compared.  The affine case needs in addition the
identification of the chart comparison of Stacks 0DJ8 (2) with the affine form of the
base-change map, which the library does not have.  Hence `PointwiseBaseChangeGlobalizes`,
carried as a
hypothesis exactly as `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` is carried for
Stacks 08IB; `AlgebraicGeometry.DerivedBaseChangeIsoOfTorIndependent`, the Stacks 0E23 input, is
proved by `AlgebraicGeometry.derivedBaseChangeIsoOfTorIndependent`.

*The model of the derived category.*  `CategoryTheory.HasDerivedCategory.standard` is made a
local instance, as in the files that supply the base-change map and the pointwise map; the two
are then read against one model, which is what makes a single statement mentioning both
type-check.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}}

/-- Commutativity of a square of schemes, read on the underlying morphisms of ringed spaces. -/
public theorem comp_toShHom_of_comm {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (w : g' ≫ f = f' ≫ g) :
    g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : X' ⟶ S => k.toLRSHom.toShHom) w

/-- **The composition `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'`** attached to a commutative square
of schemes and a morphism `φ : L(g')^*K ⟶ K'`: the derived base-change map of Stacks 08HY
followed by the derived direct image along `f'` of `φ`. -/
public def derivedBaseChangeComp (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj K) ⟶
      (derivedPushforward f'.toLRSHom.toShHom).obj K' :=
  derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm w) K ≫
    (derivedPushforward f'.toLRSHom.toShHom).map φ

/-- The composition is natural in the target of `φ`. -/
public theorem derivedBaseChangeComp_comp (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules) (K' K'' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (ψ : K' ⟶ K'') :
    derivedBaseChangeComp f g f' g' w K K'' (φ ≫ ψ) =
      derivedBaseChangeComp f g f' g' w K K' φ ≫
        (derivedPushforward f'.toLRSHom.toShHom).map ψ := by
  simp only [derivedBaseChangeComp]
  rw [(derivedPushforward f'.toLRSHom.toShHom).map_comp φ ψ, Category.assoc]

/-- At `K' = L(g')^*K` and `φ` the identity the composition is the derived base-change map of
Stacks 08HY. -/
public theorem derivedBaseChangeComp_id (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules) :
    derivedBaseChangeComp f g f' g' w K
        ((derivedPullback g'.toLRSHom.toShHom).obj K) (𝟙 _) =
      derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm w) K := by
  simp [derivedBaseChangeComp]

/-- **Condition (1) of Stacks 0DJ8**, as a predicate on the data: the pointwise base-change map
of Stacks 0DJ7 on stalkwise cohomology is invertible at every point of `X'` and in every degree.
Stacks 0DJ8 itself is registered on the chart declarations of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart`. -/
public abbrev PointwiseBaseChange (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') : Prop :=
  ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n)

/-- **The conclusion of Stacks 0DJ9.** For a cartesian diagram of schemes with `f` quasi-compact
and quasi-separated, an object `K` of `D_QCoh(𝒪_X)` and a morphism `φ : L(g')^*K ⟶ K'` in
`D_QCoh(𝒪_{X'})` satisfying the pointwise condition of Stacks 0DJ8 (1), the composition
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism. -/
public abbrev PointwiseBaseChangeGlobalizes : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
    IsPullback g' f' f g → QuasiCompact f → QuasiSeparated f →
      ∀ (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
        (K' : DerivedCategory X'.Modules)
        (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
        (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent) →
        (∀ j : ℤ, ((DerivedCategory.homologyFunctor X'.Modules j).obj K').IsQuasicoherent) →
        PointwiseBaseChange f g f' g' w K K' φ →
        IsIso (derivedBaseChangeComp f g f' g' w K K' φ)

/-- **Stacks 0DJ9.** For a cartesian diagram of schemes

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `f` quasi-compact and quasi-separated, an object `K` of `D_QCoh(𝒪_X)` and a morphism
`φ : L(g')^*K ⟶ K'` in `D_QCoh(𝒪_{X'})` for which the pointwise maps of Stacks 0DJ7 are
invertible — condition (1) of Stacks 0DJ8 — the composition
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism. -/
-- No tag sits on this declaration: `PointwiseBaseChangeGlobalizes` is the universally
-- quantified form of the very conclusion, so the body is a single application of it. The tag
-- is registered on `isIso_derivedBaseChangeComp_of_pointwiseBaseChange` in
-- `PointwiseBaseChangeIso.lean`, which proves the conclusion outright. This declaration is
-- retained because it is the shape in which Stacks 08IB consumes Stacks 0DJ9.
public theorem isIso_derivedBaseChangeComp (h : PointwiseBaseChangeGlobalizes.{u})
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f) (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent)
    (hK' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X'.Modules j).obj K').IsQuasicoherent)
    (hp : PointwiseBaseChange f g f' g' w K K' φ) :
    IsIso (derivedBaseChangeComp f g f' g' w K K' φ) :=
  h f g f' g' sq hqc hqs w K K' φ hK hK' hp

/-- Granted the conclusion of Stacks 0DJ9, the derived base-change map of Stacks 08HY is
invertible at a complex with quasi-coherent cohomology whose pointwise maps of Stacks 0DJ7 are
invertible.  This is the shape in which Stacks 08IB consumes Stacks 0DJ9. -/
public theorem isIso_derivedBaseChangeMap_of_globalizes
    (h : PointwiseBaseChangeGlobalizes.{u}) (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S')
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent)
    (hK' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X'.Modules j).obj
      ((derivedPullback g'.toLRSHom.toShHom).obj K)).IsQuasicoherent)
    (hp : PointwiseBaseChange f g f' g' w K
      ((derivedPullback g'.toLRSHom.toShHom).obj K) (𝟙 _)) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm w) K) := by
  have hiso := h f g f' g' sq hqc hqs w K _ (𝟙 _) hK hK' hp
  rwa [derivedBaseChangeComp_id] at hiso

/-!
### Naturality of the composition in the pair, and the two inputs the induction still lacks

The Mayer–Vietoris induction of Stacks 0DJ9 compares the relative Mayer–Vietoris triangle of
Stacks 08HZ on `X`, pulled back along `g`, with the one on `X'`; its two restriction squares are
instances of `AlgebraicGeometry.derivedBaseChangeComp_naturality` below, and its five-lemma step
is `CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`.  What is still missing is a *morphism of
triangles*, that is the square on the connecting morphisms, and it needs two inputs the library
does not have.  First, shift compatibility of the base-change transformation itself,
`NatTrans.CommShift (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare ..).natTrans ℤ`:
the transformation is a mate, and neither this library nor Mathlib relates `mateEquiv` to the
shift.  Second, the connecting morphism of the absolute Mayer–Vietoris triangle of Stacks 08BV,
`Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover`, in a form with its
morphisms named, together with its compatibility with derived pullback: with
`w : Rj_{W*}(K|_W) ⟶ K⟦1⟧` on `X` and `w' : Rj_{W'*}(K'|_{W'}) ⟶ K'⟦1⟧` on `X'` and `ψ` the
comparison of the two restricted pushforwards, the equation `L(g')^* w ≫ φ⟦1⟧ = ψ ≫ w'`.  The
first reduces the connecting square of the pulled-back relative triangle to that equation; the
equation itself is irreducible, the three remaining squares of the induction being consequences
of naturality alone.
-/

/-- **Naturality of the composition in the pair `(K, K')`.**  Morphisms `u : K ⟶ L` on `X` and
`v : K' ⟶ L'` on `X'` compatible with the two maps out of the derived pullback induce a commuting
square of base-change compositions. -/
public theorem derivedBaseChangeComp_naturality (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S')
    (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) {K L : DerivedCategory X.Modules}
    {K' L' : DerivedCategory X'.Modules}
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (ψ : (derivedPullback g'.toLRSHom.toShHom).obj L ⟶ L') (u : K ⟶ L) (v : K' ⟶ L')
    (hu : (derivedPullback g'.toLRSHom.toShHom).map u ≫ ψ = φ ≫ v) :
    (derivedPullback g.toLRSHom.toShHom).map
          ((derivedPushforward f.toLRSHom.toShHom).map u) ≫
        derivedBaseChangeComp f g f' g' w L L' ψ =
      derivedBaseChangeComp f g f' g' w K K' φ ≫
        (derivedPushforward f'.toLRSHom.toShHom).map v := by
  have h2 : (derivedPushforward f'.toLRSHom.toShHom).map
          ((derivedPullback g'.toLRSHom.toShHom).map u) ≫
        (derivedPushforward f'.toLRSHom.toShHom).map ψ =
      (derivedPushforward f'.toLRSHom.toShHom).map φ ≫
        (derivedPushforward f'.toLRSHom.toShHom).map v :=
    ((derivedPushforward f'.toLRSHom.toShHom).map_comp _ _).symm.trans
      ((congrArg (fun k => (derivedPushforward f'.toLRSHom.toShHom).map k) hu).trans
        ((derivedPushforward f'.toLRSHom.toShHom).map_comp _ _))
  simp only [derivedBaseChangeComp, Category.assoc]
  exact ((reassoc_of% (derivedBaseChangeMap_naturality g'.toLRSHom.toShHom f'.toLRSHom.toShHom
        f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm w) u))
      ((derivedPushforward f'.toLRSHom.toShHom).map ψ)).trans
    (congrArg (fun k => derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm w) K ≫ k) h2)

/-- At an invertible `φ` the composition is invertible exactly when the derived base-change map
of Stacks 08HY is.  This is the passage between the two forms that Stacks 08IB uses. -/
public theorem isIso_derivedBaseChangeComp_iff (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S')
    (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') [IsIso φ] :
    IsIso (derivedBaseChangeComp f g f' g' w K K' φ) ↔
      IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm w) K) := by
  have := Functor.map_isIso (derivedPushforward f'.toLRSHom.toShHom) φ
  rw [derivedBaseChangeComp]
  exact isIso_comp_right_iff _ ((derivedPushforward f'.toLRSHom.toShHom).map φ)

/-!
### The induction of Stacks 0DJ9 over the quasi-compact opens of the source

The source proves Stacks 0DJ9 in three moves: it works locally on `S'` to reduce to a square over
an affine base, it settles an affine open of `X` from Stacks 0DJ8 (2), and it passes from two
quasi-compact opens and their intersection to their union with the relative Mayer--Vietoris
diagram.  The induction principle of Stacks 08DR joins the second and third into the affine-base
case, and that is what this section carries out.  The second and third moves are named
`BaseChangeAffineOpenCase` and `BaseChangeMayerVietorisStep`, and the affine-base case they join
into is `BaseChangeOverAffineBase`.
-/

/-- **The conclusion of Stacks 0DJ9 over an open subset of `X`**, stated invariantly: for every
open immersion `j : Y ⟶ X` with image `U` and every base change of `j ≫ f` along `g`, the
base-change composition attached to a morphism out of the derived pullback is invertible, as soon
as the pointwise maps of Stacks 0DJ7 are.  Quantifying over the representatives of `U` rather
than over its own open subscheme is what lets the induction of Stacks 08DR restrict a
representative further. -/
public abbrev BaseChangeOverOpen {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (U : X.Opens) : Prop :=
  ∀ {Y Y' : Scheme.{u}} (j : Y ⟶ X) (fY : Y ⟶ S) (fY' : Y' ⟶ S') (jY : Y' ⟶ Y),
    IsOpenImmersion j → Set.range j.base = (U : Set X) → j ≫ f = fY →
    ∀ sq : IsPullback jY fY' fY g,
      ∀ (K : DerivedCategory Y.Modules) (K' : DerivedCategory Y'.Modules)
        (φ : (derivedPullback jY.toLRSHom.toShHom).obj K ⟶ K'),
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj K).IsQuasicoherent) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor Y'.Modules n).obj K').IsQuasicoherent) →
        PointwiseBaseChange fY g fY' jY sq.w K K' φ →
        IsIso (derivedBaseChangeComp fY g fY' jY sq.w K K' φ)

/-- **The affine case of Stacks 0DJ9**, the base case of the source's induction: over a square
with affine base the conclusion holds on every affine open of `X`.  The source settles it from
Stacks 0DJ8 (2) and the translation into algebra of Stacks 06Z0 and Stacks 08DW. -/
public abbrev BaseChangeAffineOpenCase : Prop :=
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S), IsAffine S → IsAffine S' →
    QuasiCompact f → QuasiSeparated f →
    ∀ U : X.Opens, IsAffineOpen U → BaseChangeOverOpen f g U

/-- **The Mayer--Vietoris step of Stacks 0DJ9**: over a square with affine base the conclusion
passes from a quasi-compact open, an affine open and their intersection to their union.  The
source obtains it from the four-row diagram of relative Mayer--Vietoris, Stacks 08HZ, whose
second and third rows are invertible by the inductive hypothesis, closed by Stacks 014A. -/
public abbrev BaseChangeMayerVietorisStep : Prop :=
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S), IsAffine S → IsAffine S' →
    QuasiCompact f → QuasiSeparated f →
    ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
      BaseChangeOverOpen f g U → BaseChangeOverOpen f g V →
      BaseChangeOverOpen f g (U ⊓ V) → BaseChangeOverOpen f g (U ⊔ V)

/-- **Stacks 0DJ9 over an affine base**, the statement the source reaches after working locally
on `S'`: for a cartesian square whose two bases are affine and whose `f` is quasi-compact and
quasi-separated, the base-change composition is invertible. -/
public abbrev BaseChangeOverAffineBase : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
    IsAffine S → IsAffine S' → IsPullback g' f' f g → QuasiCompact f → QuasiSeparated f →
      ∀ (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
        (K' : DerivedCategory X'.Modules)
        (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K'),
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent) →
        PointwiseBaseChange f g f' g' w K K' φ →
        IsIso (derivedBaseChangeComp f g f' g' w K K' φ)

/-- **The induction of Stacks 0DJ9 over the quasi-compact opens of `X`.**  Granted the affine
case and the Mayer--Vietoris step, the conclusion holds for every cartesian square over an affine
base: an affine base makes `X` quasi-compact and quasi-separated, so the induction principle of
Stacks 08DR carries the property from the affine opens to all of `X`. -/
@[stacks 08DR "the induction of Stacks 0DJ9 from the affine opens of X to X itself"]
public theorem baseChangeOverAffineBase_of_affineOpens
    (haffine : BaseChangeAffineOpenCase.{u}) (hstep : BaseChangeMayerVietorisStep.{u}) :
    BaseChangeOverAffineBase.{u} := by
  intro X X' S S' f g f' g' hS hS' sq hqc hqs _ K K' φ hK hK' hp
  have : IsAffine S := hS
  have : CompactSpace X := @QuasiCompact.compactSpace_of_compactSpace _ _ f hqc inferInstance
  have : QuasiSeparatedSpace X :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ f inferInstance hqs
  have htop : BaseChangeOverOpen f g ⊤ :=
    Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
      (BaseChangeOverOpen f g) (haffine f g hS hS' hqc hqs)
      (hstep f g hS hS' hqc hqs) ⊤ (by simpa using isCompact_univ (X := X))
  exact htop (𝟙 X) f f' g' inferInstance (by simp) (Category.id_comp f) sq K K' φ hK hK' hp

end AlgebraicGeometry

end
