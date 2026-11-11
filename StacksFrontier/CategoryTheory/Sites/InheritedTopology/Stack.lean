module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Sites.Grothendieck

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Restriction
import StacksCore.Tactic.StacksAttribute

/-! # Stacks in groupoids over a site

Let `(𝒞, J)` be a site. A category `p : 𝒮 ⥤ 𝒞` over `𝒞` is a *stack in groupoids*
(Stacks, Definition 8.5.1) when it is fibred in groupoids, its `Isom` presheaves are
sheaves, and every descent datum relative to a `J`-covering family is effective. This
file states the three conditions and packages them.

Throughout, the double and triple overlaps of a covering family are required to be
genuine fibre products in `𝒞`: the projection data carries `IsPullback` proofs, so no
global `HasPullbacks 𝒞` is assumed and the notion of site is the one of the Stacks
project.

## Main definitions

* `CategoryTheory.Functor.IsomIsSheafFor`: the sheaf condition for `Isom(x, y)`
  relative to one covering family.
* `CategoryTheory.Functor.DescentDatum`: a descent datum relative to a covering family.
* `CategoryTheory.Functor.DescentDatum.IsEffective`: effectivity of a descent datum.
* `CategoryTheory.Functor.IsStackInGroupoids`: a stack in groupoids over a site.

## Main results

* `CategoryTheory.Functor.DescentDatum.isRestrictionOf_diagonal_id`: the pullback of the gluing
  isomorphism `φ i i` along the diagonal is the identity of `x i` (Stacks 026C (1)).
* `CategoryTheory.Functor.DescentDatum.isRestrictionOf_switch_inv`: the pullback of `φ j i`
  along the switching morphism is the inverse of `φ i j` (Stacks 026C (2)).
* `CategoryTheory.Functor.DescentDatum.diagonalPullback_eq_id`,
  `CategoryTheory.Functor.DescentDatum.gluing_comp_switchPullback_eq_id`: the same identities
  restated on the triple overlaps, used downstream.

## References

* [Stacks Project, Tag 026C](https://stacks.math.columbia.edu/tag/026C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-- The sheaf condition for `Isom(x, y)` relative to a covering family `{ f i : V i ⟶ U }`, with
double overlaps `Vij i j` that are pullbacks of `f i` and `f j`: fibre isomorphisms
`φ i : x|_{V i} ⟶ y|_{V i}` whose restrictions along `pr₁ i j` and `pr₂ i j` agree on each
overlap glue to a unique fibre isomorphism `g : x ⟶ y` with
`(xr i).hom ≫ g = φ i ≫ (yr i).hom`. -/
def IsomIsSheafFor (p : 𝒮 ⥤ 𝒞) {U : 𝒞} (x y : 𝒮)
    (hx : p.obj x = U) (hy : p.obj y = U)
    {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U)
    (Vij : I → I → 𝒞)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction p (f i) x hx) (yr : ∀ i, Restriction p (f i) y hy)
    (xrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) y hy) : Prop :=
  ∀ (φ : ∀ i, (xr i).pt ⟶ (yr i).pt),
    (∀ i, FibreHom p (xr i).pt (yr i).pt (xr i).hpt (yr i).hpt (φ i)) →
    (∀ i, IsIso (φ i)) →
    -- compatibility on overlaps: a single `γ i j` is the canonical restriction of
    -- both `φ i` (along `pr₁`) and `φ j` (along `pr₂`).
    (∀ i j, ∃ (γ : (xrij i j).pt ⟶ (yrij i j).pt),
      FibreHom p (xrij i j).pt (yrij i j).pt (xrij i j).hpt (yrij i j).hpt γ ∧
      IsRestrictionOf p (pr₁ i j) rfl rfl (xr i) (yr i) (xrij i j) (yrij i j) (φ i) γ ∧
      IsRestrictionOf p (pr₂ i j) (hVij i j).w (hVij i j).w (xr j) (yr j)
        (xrij i j) (yrij i j) (φ j) γ) →
    ∃! g : x ⟶ y,
      FibreHom p x y hx hy g ∧ IsIso g ∧
        ∀ i, (xr i).hom ≫ g = φ i ≫ (yr i).hom

/-! ## Descent data -/

/-- A descent datum relative to a covering family `{ f i : V i ⟶ U }`, whose double overlaps
`Vij i j` are pullbacks of `f i` and `f j` and whose triple overlaps `Vijk i j k` are pullbacks
of `pr₂ i j` and `pr₁ j k`: objects `x i` over `V i` with gluing isomorphisms `φ i j` on the
double overlaps, whose restrictions `αij`, `αjk`, `αik` to the triple overlaps satisfy the
cocycle condition `αik = αij ≫ αjk`. -/
@[sga "3 IV 2.1" "more general", sga "4½ Arcata 1.3.2" "more general"]
structure DescentDatum (p : 𝒮 ⥤ 𝒞) {U : 𝒞}
    {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U)
    (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → 𝒞)
    -- the triple overlap is the genuine fibre product `Vij i j ×_{V j} Vij j k`,
    -- which is canonically `V i ×_U V j ×_U V k`:
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j)
    (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    -- the three composite projections to `V i`, `V j`, `V k`:
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k) where
  /-- Objects `x i` lying over `V i`. -/
  x : I → 𝒮
  /-- `x i` lies over `V i`. -/
  hx : ∀ i, p.obj (x i) = V i
  /-- Restriction of `x i` to the overlap `V i ×_U V j`, along `pr₁ i j`. -/
  xrij : ∀ i j, Restriction p (pr₁ i j) (x i) (hx i)
  /-- Restriction of `x j` to the overlap `V i ×_U V j`, along `pr₂ i j`. -/
  xrji : ∀ i j, Restriction p (pr₂ i j) (x j) (hx j)
  /-- The gluing isomorphisms `φ i j : x i |_{ij} ⟶ x j |_{ij}`. -/
  φ : ∀ i j, (xrij i j).pt ⟶ (xrji i j).pt
  /-- Each `φ i j` is a morphism of the fibre category over the overlap. -/
  φ_fibreHom : ∀ i j,
    FibreHom p (xrij i j).pt (xrji i j).pt (xrij i j).hpt (xrji i j).hpt (φ i j)
  /-- Each `φ i j` is an isomorphism. -/
  φ_iso : ∀ i j, IsIso (φ i j)
  /-- Restriction of `x i` to the triple overlap, along the projection `q₁`. -/
  wi : ∀ i j k, Restriction p (q₁ i j k) (x i) (hx i)
  /-- Restriction of `x j` to the triple overlap, along the projection `q₂`. -/
  wj : ∀ i j k, Restriction p (q₂ i j k) (x j) (hx j)
  /-- Restriction of `x k` to the triple overlap, along the projection `q₃`. -/
  wk : ∀ i j k, Restriction p (q₃ i j k) (x k) (hx k)
  /-- The gluing isomorphism `x i |_{ijk} ⟶ x j |_{ijk}` over the triple overlap. -/
  αij : ∀ i j k, (wi i j k).pt ⟶ (wj i j k).pt
  /-- The gluing isomorphism `x j |_{ijk} ⟶ x k |_{ijk}` over the triple overlap. -/
  αjk : ∀ i j k, (wj i j k).pt ⟶ (wk i j k).pt
  /-- The gluing isomorphism `x i |_{ijk} ⟶ x k |_{ijk}` over the triple overlap. -/
  αik : ∀ i j k, (wi i j k).pt ⟶ (wk i j k).pt
  /-- `αij` is the canonical restriction of `φ i j` along `s₁₂`. -/
  αij_restr : ∀ i j k,
    IsRestrictionOf p (s₁₂ i j k) (hq₁ i j k) (hq₂ i j k) (xrij i j) (xrji i j)
      (wi i j k) (wj i j k) (φ i j) (αij i j k)
  /-- `αjk` is the canonical restriction of `φ j k` along `s₂₃` (using the pullback
  identity `q₂ = s₂₃ ≫ pr₁ j k` of `hVijk` to view `wj` as a restriction along
  `s₂₃ ≫ pr₁ j k`). -/
  αjk_restr : ∀ i j k,
    IsRestrictionOf p (s₂₃ i j k)
      ((hq₂ i j k).trans (hVijk i j k).w) (hq₃ i j k)
      (xrij j k) (xrji j k) (wj i j k) (wk i j k) (φ j k) (αjk i j k)
  /-- The canonical comparison from the triple overlap into the `(i, k)` overlap. -/
  s₁₃ : ∀ i j k, Vijk i j k ⟶ Vij i k
  /-- The comparison `s₁₃` is compatible with the projections to `V i`. -/
  hs₁₃₁ : ∀ i j k, s₁₃ i j k ≫ pr₁ i k = q₁ i j k
  /-- The comparison `s₁₃` is compatible with the projections to `V k`. -/
  hs₁₃₂ : ∀ i j k, s₁₃ i j k ≫ pr₂ i k = q₃ i j k
  /-- `αik` is the canonical restriction of `φ i k` along `s₁₃`. -/
  αik_restr : ∀ i j k,
    IsRestrictionOf p (s₁₃ i j k) (hs₁₃₁ i j k).symm (hs₁₃₂ i j k).symm
      (xrij i k) (xrji i k) (wi i j k) (wk i j k) (φ i k) (αik i j k)
  /-- The *cocycle condition* `αik = αij ≫ αjk` over the triple overlap. -/
  cocycle : ∀ i j k, αik i j k = αij i j k ≫ αjk i j k

/-- A descent datum `D` relative to a covering `{ f i : V i ⟶ U }` is effective if there is an
object `x` over `U` with restrictions `xr i` to each `V i` and fibre isomorphisms
`ψ i : x|_{V i} ⟶ D.x i` whose restrictions `ψir`, `ψjr` to each overlap satisfy
`ψir ≫ D.φ i j = ψjr`. -/
@[sga "3 IV 3.5.1" "more general"]
def DescentDatum.IsEffective {p : 𝒮 ⥤ 𝒞} {U : 𝒞}
    {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
    {Vijk : I → I → I → 𝒞}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃) : Prop :=
  ∃ (x : 𝒮) (hx : p.obj x = U) (xr : ∀ i, Restriction p (f i) x hx)
    (ψ : ∀ i, (xr i).pt ⟶ D.x i),
    (∀ i, FibreHom p (xr i).pt (D.x i) (xr i).hpt (D.hx i) (ψ i)) ∧
    (∀ i, IsIso (ψ i)) ∧
    -- compatibility on each overlap `V i ×_U V j`:
    (∀ i j,
      ∃ (xrij : Restriction p (pr₁ i j ≫ f i) x hx)
        (ψir : xrij.pt ⟶ (D.xrij i j).pt) (ψjr : xrij.pt ⟶ (D.xrji i j).pt),
        FibreHom p xrij.pt (D.xrij i j).pt xrij.hpt (D.xrij i j).hpt ψir ∧
        FibreHom p xrij.pt (D.xrji i j).pt xrij.hpt (D.xrji i j).hpt ψjr ∧
        IsIso ψir ∧ IsIso ψjr ∧
        -- `ψir` is the canonical restriction of `ψ i` along `pr₁`:
        IsRestrictionOf p (pr₁ i j) (rfl) (by simp)
          (xr i) (Restriction.id p (D.x i) (D.hx i))
          xrij (D.xrij i j) (ψ i) ψir ∧
        -- `ψjr` is the canonical restriction of `ψ j` along `pr₂`:
        IsRestrictionOf p (pr₂ i j) (hVij i j).w (by simp)
          (xr j) (Restriction.id p (D.x j) (D.hx j))
          xrij (D.xrji i j) (ψ j) ψjr ∧
        -- the descent compatibility `ψ j | = φ i j ∘ ψ i |`, i.e. `ψir ≫ φ i j = ψjr`:
        ψir ≫ D.φ i j = ψjr)

/-! ## Stacks in groupoids -/

/-- A functor `p : 𝒮 ⥤ 𝒞` is a stack in groupoids over the site `(𝒞, J)` if
1. `p` is fibred in groupoids;
2. for all `x y` over `U`, the presheaf `Isom(x, y)` satisfies the sheaf condition for every
   covering family of `J`, with overlaps given by fibre products; and
3. every descent datum relative to a covering family of `J` is effective.

A covering family `{ f i : V i ⟶ U }` is one whose generated sieve `Sieve.ofArrows V f` lies in
`J U`.

This is the covering-family form of the conditions of Stacks 02ZI, whose registered definition
is `CategoryTheory.Functor.IsStackInGroupoidsBySieves`, stated with covering sieves; that
definition implies this one at every index universe
(`CategoryTheory.Functor.IsStackInGroupoidsBySieves.isStackInGroupoids`). -/
structure IsStackInGroupoids (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop where
  /-- Condition 1: `p` is fibred in groupoids. -/
  isFiberedInGroupoids : p.IsFiberedInGroupoids
  /-- Condition 2: the `Isom` presheaves are sheaves. -/
  isom_isSheaf : ∀ {U : 𝒞} (x y : 𝒮) (hx : p.obj x = U) (hy : p.obj y = U)
    {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U →
    ∀ (Vij : I → I → 𝒞)
      (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
      (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
      (xr : ∀ i, Restriction p (f i) x hx) (yr : ∀ i, Restriction p (f i) y hy)
      (xrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) x hx)
      (yrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) y hy),
      IsomIsSheafFor p x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij
  /-- Condition 3: every descent datum is effective. -/
  effective_descent : ∀ {U : 𝒞} {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U →
    ∀ (Vij : I → I → 𝒞)
      (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
      (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
      (Vijk : I → I → I → 𝒞)
      (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
      (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
      (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
      (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
      (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
      (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
      (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
      (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
        q₁ q₂ q₃ hq₁ hq₂ hq₃),
      D.IsEffective

/-! ## Restrictions of fibre morphisms -/

/-- The identity of an object over `U` is a morphism of the fibre category over `U`. -/
protected theorem FibreHom.id (p : 𝒮 ⥤ 𝒞) {U : 𝒞} (a : 𝒮) (ha : p.obj a = U) :
    FibreHom p a a ha ha (𝟙 a) := by
  change p.IsHomLift (eqToHom ha ≫ eqToHom ha.symm) (𝟙 a)
  simp only [eqToHom_trans, eqToHom_refl]
  infer_instance

/-- A composite of two morphisms of the fibre category over `U` is one. -/
protected theorem FibreHom.comp {p : 𝒮 ⥤ 𝒞} {U : 𝒞} {a b c : 𝒮} {ha : p.obj a = U}
    {hb : p.obj b = U} {hc : p.obj c = U} {α : a ⟶ b} {β : b ⟶ c}
    (hα : FibreHom p a b ha hb α) (hβ : FibreHom p b c hb hc β) :
    FibreHom p a c ha hc (α ≫ β) := by
  have := hα
  have := hβ
  have h := CategoryTheory.IsHomLift.comp p (eqToHom ha ≫ eqToHom hb.symm)
    (eqToHom hb ≫ eqToHom hc.symm) α β
  change p.IsHomLift (eqToHom ha ≫ eqToHom hc.symm) (α ≫ β)
  simpa using h

/-- Canonical restriction along `g` is compatible with composition: if `β₁` is the canonical
restriction of `α₁` and `β₂` that of `α₂`, then `β₁ ≫ β₂` is the canonical restriction of
`α₁ ≫ α₂`. -/
theorem IsRestrictionOf.comp {p : 𝒮 ⥤ 𝒞} {W V Ux Uy Uz : 𝒞} {g : W ⟶ V}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {fz : V ⟶ Uz}
    {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy} {hz_ : W ⟶ Uz}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy} {hfz : hz_ = g ≫ fz}
    {x y z : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy} {hz : p.obj z = Uz}
    {xr : Restriction p fx x hx} {yr : Restriction p fy y hy} {zr : Restriction p fz z hz}
    {xrW : Restriction p hx_ x hx} {yrW : Restriction p hy_ y hy}
    {zrW : Restriction p hz_ z hz}
    {α₁ : xr.pt ⟶ yr.pt} {α₂ : yr.pt ⟶ zr.pt}
    {β₁ : xrW.pt ⟶ yrW.pt} {β₂ : yrW.pt ⟶ zrW.pt}
    (h₁ : IsRestrictionOf p g hfx hfy xr yr xrW yrW α₁ β₁)
    (h₂ : IsRestrictionOf p g hfy hfz yr zr yrW zrW α₂ β₂) :
    IsRestrictionOf p g hfx hfz xr zr xrW zrW (α₁ ≫ α₂) (β₁ ≫ β₂) := by
  change (β₁ ≫ β₂) ≫ Restriction.compTo p g fz hfz zr zrW
      = Restriction.compTo p g fx hfx xr xrW ≫ (α₁ ≫ α₂)
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

/-- A fibre morphism has at most one canonical restriction along `g`. -/
theorem IsRestrictionOf.unique {p : 𝒮 ⥤ 𝒞} {W V Ux Uy : 𝒞} {g : W ⟶ V}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy}
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    {xr : Restriction p fx x hx} {yr : Restriction p fy y hy}
    {xrW : Restriction p hx_ x hx} {yrW : Restriction p hy_ y hy}
    {α : xr.pt ⟶ yr.pt} {β β' : xrW.pt ⟶ yrW.pt}
    (hβ : FibreHom p xrW.pt yrW.pt xrW.hpt yrW.hpt β)
    (hβ' : FibreHom p xrW.pt yrW.pt xrW.hpt yrW.hpt β')
    (h : IsRestrictionOf p g hfx hfy xr yr xrW yrW α β)
    (h' : IsRestrictionOf p g hfx hfy xr yr xrW yrW α β') :
    β = β' := by
  have := hβ
  have := hβ'
  have e1 := Restriction.compTo_hom p g fy hfy yr yrW
  have key : β ≫ yrW.hom = β' ≫ yrW.hom := by
    rw [← e1, ← Category.assoc, ← Category.assoc, h, ← h']
  exact Functor.IsStronglyCartesian.ext p
    (eqToHom yrW.hpt ≫ hy_ ≫ eqToHom hy.symm) yrW.hom
    (eqToHom xrW.hpt ≫ eqToHom yrW.hpt.symm) key

/-- The canonical comparison `Restriction.compTo` lies over `g`. -/
theorem Restriction.compTo_isHomLift (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f) {x : 𝒮} {hx : p.obj x = U}
    (xr : Restriction p f x hx) (xrW : Restriction p h x hx) :
    p.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo p g f hh xr xrW) := by
  unfold Restriction.compTo
  infer_instance

/-- Two morphisms into a restriction `r` lying over the same base morphism agree as soon as
their composites with the cartesian morphism `r.hom` agree. -/
theorem Restriction.hom_ext {p : 𝒮 ⥤ 𝒞} {V U W : 𝒞} {f : V ⟶ U} {y : 𝒮} {hy : p.obj y = U}
    (r : Restriction p f y hy) {P : 𝒮} (hP : p.obj P = W) (k : W ⟶ V) {a b : P ⟶ r.pt}
    (ha : p.IsHomLift (eqToHom hP ≫ k ≫ eqToHom r.hpt.symm) a)
    (hb : p.IsHomLift (eqToHom hP ≫ k ≫ eqToHom r.hpt.symm) b)
    (h : a ≫ r.hom = b ≫ r.hom) : a = b :=
  Functor.IsStronglyCartesian.ext p (eqToHom r.hpt ≫ f ≫ eqToHom hy.symm) r.hom
    (eqToHom hP ≫ k ≫ eqToHom r.hpt.symm) h

/-- A fibre morphism followed by a morphism over `k` lies over `k`. -/
theorem FibreHom.fibreHom_comp_isHomLift {p : 𝒮 ⥤ 𝒞} {W V : 𝒞} {a b c : 𝒮} {ha : p.obj a = W}
    {hb : p.obj b = W} {hc : p.obj c = V} {β : a ⟶ b} {γ : b ⟶ c} {k : W ⟶ V}
    (hβ : FibreHom p a b ha hb β) (hγ : p.IsHomLift (eqToHom hb ≫ k ≫ eqToHom hc.symm) γ) :
    p.IsHomLift (eqToHom ha ≫ k ≫ eqToHom hc.symm) (β ≫ γ) := by
  have := hβ
  have := hγ
  have h := CategoryTheory.IsHomLift.comp p (eqToHom ha ≫ eqToHom hb.symm)
    (eqToHom hb ≫ k ≫ eqToHom hc.symm) β γ
  simpa using h

/-- A morphism over `k` followed by a fibre morphism lies over `k`. -/
theorem FibreHom.isHomLift_comp_fibreHom {p : 𝒮 ⥤ 𝒞} {W V : 𝒞} {a b c : 𝒮} {ha : p.obj a = W}
    {hb : p.obj b = V} {hc : p.obj c = V} {γ : a ⟶ b} {β : b ⟶ c} {k : W ⟶ V}
    (hγ : p.IsHomLift (eqToHom ha ≫ k ≫ eqToHom hb.symm) γ) (hβ : FibreHom p b c hb hc β) :
    p.IsHomLift (eqToHom ha ≫ k ≫ eqToHom hc.symm) (γ ≫ β) := by
  have := hβ
  have := hγ
  have h := CategoryTheory.IsHomLift.comp p (eqToHom ha ≫ k ≫ eqToHom hb.symm)
    (eqToHom hb ≫ eqToHom hc.symm) γ β
  simpa using h

/-- A morphism between objects over `W` whose image in the base is the identity of `W` is a
morphism of the fibre category over `W`. -/
theorem FibreHom.of_map_eq {p : 𝒮 ⥤ 𝒞} {W : 𝒞} {a b : 𝒮} {ha : p.obj a = W}
    {hb : p.obj b = W} {β : a ⟶ b} (h : eqToHom ha.symm ≫ p.map β ≫ eqToHom hb = 𝟙 W) :
    FibreHom p a b ha hb β := by
  apply CategoryTheory.IsHomLift.of_fac' p _ β rfl rfl
  have h' : p.map β = eqToHom ha ≫ (eqToHom ha.symm ≫ p.map β ≫ eqToHom hb) ≫
      eqToHom hb.symm := by simp
  rw [h', h]
  simp

/-- The canonical comparisons along `g₁` and along `g₂` compose to the canonical comparison
along `g₁ ≫ g₂`. -/
theorem Restriction.compTo_comp (p : 𝒮 ⥤ 𝒞) {W V' V U : 𝒞} (g₁ : W ⟶ V') (g₂ : V' ⟶ V)
    (f : V ⟶ U) {f' : V' ⟶ U} {h : W ⟶ U} (hf' : f' = g₂ ≫ f) (hh₁ : h = g₁ ≫ f')
    (hh : h = (g₁ ≫ g₂) ≫ f) {x : 𝒮} {hx : p.obj x = U}
    (xr : Restriction p f x hx) (xr' : Restriction p f' x hx) (xrW : Restriction p h x hx) :
    Restriction.compTo p g₁ f' hh₁ xr' xrW ≫ Restriction.compTo p g₂ f hf' xr xr' =
      Restriction.compTo p (g₁ ≫ g₂) f hh xr xrW := by
  have h₁ := Restriction.compTo_isHomLift p g₁ f' hh₁ xr' xrW
  have h₂ := Restriction.compTo_isHomLift p g₂ f hf' xr xr'
  have h₁₂ : p.IsHomLift (eqToHom xrW.hpt ≫ (g₁ ≫ g₂) ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo p g₁ f' hh₁ xr' xrW ≫ Restriction.compTo p g₂ f hf' xr xr') := by
    have := CategoryTheory.IsHomLift.comp p (eqToHom xrW.hpt ≫ g₁ ≫ eqToHom xr'.hpt.symm)
      (eqToHom xr'.hpt ≫ g₂ ≫ eqToHom xr.hpt.symm) (Restriction.compTo p g₁ f' hh₁ xr' xrW)
      (Restriction.compTo p g₂ f hf' xr xr')
    simpa using this
  refine Restriction.hom_ext xr xrW.hpt (g₁ ≫ g₂) h₁₂
    (Restriction.compTo_isHomLift p (g₁ ≫ g₂) f hh xr xrW) ?_
  rw [Category.assoc, Restriction.compTo_hom, Restriction.compTo_hom, Restriction.compTo_hom]

/-- The canonical comparison along the identity between a restriction and itself is the
identity. -/
theorem Restriction.compTo_id (p : 𝒮 ⥤ 𝒞) {V U : 𝒞} (f : V ⟶ U) (hh : f = 𝟙 V ≫ f)
    {x : 𝒮} {hx : p.obj x = U} (xr : Restriction p f x hx) :
    Restriction.compTo p (𝟙 V) f hh xr xr = 𝟙 xr.pt := by
  have h₁ : p.IsHomLift (eqToHom xr.hpt ≫ 𝟙 V ≫ eqToHom xr.hpt.symm) (𝟙 xr.pt) := by
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    infer_instance
  refine Restriction.hom_ext xr xr.hpt (𝟙 V)
    (Restriction.compTo_isHomLift p (𝟙 V) f hh xr xr) h₁ ?_
  rw [Restriction.compTo_hom, Category.id_comp]

/-- A fibre morphism is its own canonical restriction along the identity. -/
theorem IsRestrictionOf.refl (p : 𝒮 ⥤ 𝒞) {V Ux Uy : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy}
    (hfx : fx = 𝟙 V ≫ fx) (hfy : fy = 𝟙 V ≫ fy)
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy) (α : xr.pt ⟶ yr.pt) :
    IsRestrictionOf p (𝟙 V) hfx hfy xr yr xr yr α α := by
  change α ≫ Restriction.compTo p (𝟙 V) fy hfy yr yr = Restriction.compTo p (𝟙 V) fx hfx xr xr ≫ α
  rw [Restriction.compTo_id, Restriction.compTo_id, Category.comp_id, Category.id_comp]

/-- Transitivity of canonical restriction: if `α'` is the canonical restriction of `α` along
`g₂` and `β` that of `α'` along `g₁`, then `β` is the canonical restriction of `α` along
`g = g₁ ≫ g₂`. -/
theorem IsRestrictionOf.trans {p : 𝒮 ⥤ 𝒞} {W V' V Ux Uy : 𝒞} {g₁ : W ⟶ V'} {g₂ : V' ⟶ V}
    {g : W ⟶ V} (hg : g₁ ≫ g₂ = g)
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {fx' : V' ⟶ Ux} {fy' : V' ⟶ Uy}
    {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    {hfx' : fx' = g₂ ≫ fx} {hfy' : fy' = g₂ ≫ fy}
    {hfxW : hx_ = g₁ ≫ fx'} {hfyW : hy_ = g₁ ≫ fy'}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy}
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    {xr : Restriction p fx x hx} {yr : Restriction p fy y hy}
    {xr' : Restriction p fx' x hx} {yr' : Restriction p fy' y hy}
    {xrW : Restriction p hx_ x hx} {yrW : Restriction p hy_ y hy}
    {α : xr.pt ⟶ yr.pt} {α' : xr'.pt ⟶ yr'.pt} {β : xrW.pt ⟶ yrW.pt}
    (h₂ : IsRestrictionOf p g₂ hfx' hfy' xr yr xr' yr' α α')
    (h₁ : IsRestrictionOf p g₁ hfxW hfyW xr' yr' xrW yrW α' β) :
    IsRestrictionOf p g hfx hfy xr yr xrW yrW α β := by
  subst hg
  change β ≫ Restriction.compTo p (g₁ ≫ g₂) fy hfy yr yrW =
    Restriction.compTo p (g₁ ≫ g₂) fx hfx xr xrW ≫ α
  rw [← Restriction.compTo_comp p g₁ g₂ fy hfy' hfyW hfy yr yr' yrW,
    ← Restriction.compTo_comp p g₁ g₂ fx hfx' hfxW hfx xr xr' xrW, ← Category.assoc, h₁,
    Category.assoc, h₂, Category.assoc]

/-- Cancellation of canonical restriction: if `α'` is the canonical restriction of `α` along
`g₂` and the fibre morphism `β` is that of `α` along `g = g₁ ≫ g₂`, then `β` is the canonical
restriction of `α'` along `g₁`, provided `α'` is itself a fibre morphism. -/
theorem IsRestrictionOf.of_comp {p : 𝒮 ⥤ 𝒞} {W V' V Ux Uy : 𝒞} {g₁ : W ⟶ V'} {g₂ : V' ⟶ V}
    {g : W ⟶ V} (hg : g₁ ≫ g₂ = g)
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {fx' : V' ⟶ Ux} {fy' : V' ⟶ Uy}
    {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    {hfx' : fx' = g₂ ≫ fx} {hfy' : fy' = g₂ ≫ fy}
    {hfxW : hx_ = g₁ ≫ fx'} {hfyW : hy_ = g₁ ≫ fy'}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy}
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    {xr : Restriction p fx x hx} {yr : Restriction p fy y hy}
    {xr' : Restriction p fx' x hx} {yr' : Restriction p fy' y hy}
    {xrW : Restriction p hx_ x hx} {yrW : Restriction p hy_ y hy}
    {α : xr.pt ⟶ yr.pt} {α' : xr'.pt ⟶ yr'.pt} {β : xrW.pt ⟶ yrW.pt}
    (hα' : FibreHom p xr'.pt yr'.pt xr'.hpt yr'.hpt α')
    (hβ : FibreHom p xrW.pt yrW.pt xrW.hpt yrW.hpt β)
    (h₂ : IsRestrictionOf p g₂ hfx' hfy' xr yr xr' yr' α α')
    (h : IsRestrictionOf p g hfx hfy xr yr xrW yrW α β) :
    IsRestrictionOf p g₁ hfxW hfyW xr' yr' xrW yrW α' β := by
  subst hg
  change β ≫ Restriction.compTo p g₁ fy' hfyW yr' yrW =
    Restriction.compTo p g₁ fx' hfxW xr' xrW ≫ α'
  refine Restriction.hom_ext yr' xrW.hpt g₁
    (FibreHom.fibreHom_comp_isHomLift (hc := yr'.hpt) hβ
      (Restriction.compTo_isHomLift p g₁ fy' hfyW yr' yrW))
    (FibreHom.isHomLift_comp_fibreHom (ha := xrW.hpt)
      (Restriction.compTo_isHomLift p g₁ fx' hfxW xr' xrW) hα') ?_
  have h₂' : α' ≫ Restriction.compTo p g₂ fy hfy' yr yr' =
      Restriction.compTo p g₂ fx hfx' xr xr' ≫ α := h₂
  have h' : β ≫ Restriction.compTo p (g₁ ≫ g₂) fy hfy yr yrW =
      Restriction.compTo p (g₁ ≫ g₂) fx hfx xr xrW ≫ α := h
  rw [← Restriction.compTo_hom p g₂ fy hfy' yr yr', Category.assoc, ← Category.assoc _ _ yr.hom,
    Restriction.compTo_comp p g₁ g₂ fy hfy' hfyW hfy yr yr' yrW, ← Category.assoc, h',
    ← Restriction.compTo_comp p g₁ g₂ fx hfx' hfxW hfx xr xr' xrW]
  simp only [Category.assoc, reassoc_of% h₂']

/-- If `β` is the canonical restriction of a fibre morphism along `g`, then the image of `β` in
the base, an endomorphism of `W`, is a left identity for `g`. -/
theorem IsRestrictionOf.map_comp_eq {p : 𝒮 ⥤ 𝒞} {W V Ux Uy : 𝒞} {g : W ⟶ V}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy}
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    {xr : Restriction p fx x hx} {yr : Restriction p fy y hy}
    {xrW : Restriction p hx_ x hx} {yrW : Restriction p hy_ y hy}
    {α : xr.pt ⟶ yr.pt} {β : xrW.pt ⟶ yrW.pt}
    (hα : FibreHom p xr.pt yr.pt xr.hpt yr.hpt α)
    (h : IsRestrictionOf p g hfx hfy xr yr xrW yrW α β) :
    (eqToHom xrW.hpt.symm ≫ p.map β ≫ eqToHom yrW.hpt) ≫ g = g := by
  have hcx := Restriction.compTo_isHomLift p g fx hfx xr xrW
  have hcy := Restriction.compTo_isHomLift p g fy hfy yr yrW
  have := hα
  have e := congrArg p.map h
  rw [p.map_comp, p.map_comp,
    CategoryTheory.IsHomLift.fac' p (eqToHom yrW.hpt ≫ g ≫ eqToHom yr.hpt.symm)
      (Restriction.compTo p g fy hfy yr yrW),
    CategoryTheory.IsHomLift.fac' p (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo p g fx hfx xr xrW),
    CategoryTheory.IsHomLift.fac' p (eqToHom xr.hpt ≫ eqToHom yr.hpt.symm) α] at e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
    eqToHom_trans] at e
  have e' := congrArg (fun t => eqToHom xrW.hpt.symm ≫ t ≫ eqToHom yr.hpt) e
  simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id] using e'

/-- A fibre morphism `α` has a canonical restriction along `g`: there is a fibre morphism `β`
with `IsRestrictionOf p g hfx hfy xr yr xrW yrW α β`. -/
theorem IsRestrictionOf.exists_fibreHom {p : 𝒮 ⥤ 𝒞} {W V Ux Uy : 𝒞} (g : W ⟶ V)
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    (hfx : hx_ = g ≫ fx) (hfy : hy_ = g ≫ fy)
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrW : Restriction p hx_ x hx) (yrW : Restriction p hy_ y hy)
    (α : xr.pt ⟶ yr.pt) (hα : FibreHom p xr.pt yr.pt xr.hpt yr.hpt α) :
    ∃ β : xrW.pt ⟶ yrW.pt, FibreHom p xrW.pt yrW.pt xrW.hpt yrW.hpt β ∧
      IsRestrictionOf p g hfx hfy xr yr xrW yrW α β := by
  have h1 := FibreHom.isHomLift_comp_fibreHom (ha := xrW.hpt)
    (Restriction.compTo_isHomLift p g fx hfx xr xrW) hα
  have hl : p.IsHomLift ((eqToHom xrW.hpt ≫ eqToHom yrW.hpt.symm) ≫
      (eqToHom yrW.hpt ≫ hy_ ≫ eqToHom hy.symm))
      ((Restriction.compTo p g fx hfx xr xrW ≫ α) ≫ yr.hom) := by
    have := CategoryTheory.IsHomLift.comp p (eqToHom xrW.hpt ≫ g ≫ eqToHom yr.hpt.symm)
      (eqToHom yr.hpt ≫ fy ≫ eqToHom hy.symm) (Restriction.compTo p g fx hfx xr xrW ≫ α)
      yr.hom
    subst hfy
    simpa using this
  let β : xrW.pt ⟶ yrW.pt := Functor.IsStronglyCartesian.map p
    (eqToHom yrW.hpt ≫ hy_ ≫ eqToHom hy.symm) yrW.hom
    (g := eqToHom xrW.hpt ≫ eqToHom yrW.hpt.symm) rfl
    ((Restriction.compTo p g fx hfx xr xrW ≫ α) ≫ yr.hom)
  have hβ : FibreHom p xrW.pt yrW.pt xrW.hpt yrW.hpt β :=
    Functor.IsStronglyCartesian.map_isHomLift p _ yrW.hom
      (g := eqToHom xrW.hpt ≫ eqToHom yrW.hpt.symm) rfl _
  refine ⟨β, hβ, ?_⟩
  change β ≫ Restriction.compTo p g fy hfy yr yrW = Restriction.compTo p g fx hfx xr xrW ≫ α
  refine Restriction.hom_ext yr xrW.hpt g
    (FibreHom.fibreHom_comp_isHomLift (hc := yr.hpt) hβ
      (Restriction.compTo_isHomLift p g fy hfy yr yrW)) h1 ?_
  rw [Category.assoc, Restriction.compTo_hom]
  exact Functor.IsStronglyCartesian.fac p _ yrW.hom rfl _

/-! ## The diagonal and flip identities for a descent datum -/

section Identities

variable {p : 𝒮 ⥤ 𝒞} {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → 𝒞}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

/-- If the three gluing isomorphisms of a triple overlap restrict to `β₁`, `β₂`, `β₃` along a
common `Δ`, then the cocycle condition gives `β₁ ≫ β₂ = β₃`. -/
private theorem DescentDatum.comp_eq_of_restrictionOf
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    {i j k : I} {W : 𝒞} {u₁ : W ⟶ V i} {u₂ : W ⟶ V j} {u₃ : W ⟶ V k} {Δ : W ⟶ Vijk i j k}
    {hΔ₁ : u₁ = Δ ≫ q₁ i j k} {hΔ₂ : u₂ = Δ ≫ q₂ i j k} {hΔ₃ : u₃ = Δ ≫ q₃ i j k}
    {xW : Restriction p u₁ (D.x i) (D.hx i)} {yW : Restriction p u₂ (D.x j) (D.hx j)}
    {zW : Restriction p u₃ (D.x k) (D.hx k)}
    {β₁ : xW.pt ⟶ yW.pt} {β₂ : yW.pt ⟶ zW.pt} {β₃ : xW.pt ⟶ zW.pt}
    (hβ₁ : FibreHom p xW.pt yW.pt xW.hpt yW.hpt β₁)
    (hβ₂ : FibreHom p yW.pt zW.pt yW.hpt zW.hpt β₂)
    (hβ₃ : FibreHom p xW.pt zW.pt xW.hpt zW.hpt β₃)
    (h₁₂ : IsRestrictionOf p Δ hΔ₁ hΔ₂ (D.wi i j k) (D.wj i j k) xW yW (D.αij i j k) β₁)
    (h₂₃ : IsRestrictionOf p Δ hΔ₂ hΔ₃ (D.wj i j k) (D.wk i j k) yW zW (D.αjk i j k) β₂)
    (h₁₃ : IsRestrictionOf p Δ hΔ₁ hΔ₃ (D.wi i j k) (D.wk i j k) xW zW (D.αik i j k) β₃) :
    β₁ ≫ β₂ = β₃ := by
  rw [D.cocycle] at h₁₃
  exact IsRestrictionOf.unique (hβ₁.comp hβ₂) hβ₃ (h₁₂.comp h₂₃) h₁₃

/-- Let `D` be a descent datum for `p` fibred in groupoids, and `Δ : V i ⟶ Vijk i i i` the
diagonal. A fibre automorphism `e` of `x i` which is the pullback along `Δ` of each of the three
gluing isomorphisms of the triple `(i, i, i)` is the identity.

This is a restatement on the triple overlap, under the extra hypothesis that `p` is fibred in
groupoids. Stacks 026C (1) itself, for any fibred category and phrased with the pullback of
`φ i i` along the diagonal `V i ⟶ Vij i i`, is
`DescentDatum.eq_id_of_isRestrictionOf_diagonal` and
`DescentDatum.isRestrictionOf_diagonal_id`. -/
theorem DescentDatum.diagonalPullback_eq_id
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (hp : p.IsFiberedInGroupoids) (i : I) {Δ : V i ⟶ Vijk i i i}
    {hΔ₁ : 𝟙 (V i) = Δ ≫ q₁ i i i} {hΔ₂ : 𝟙 (V i) = Δ ≫ q₂ i i i}
    {hΔ₃ : 𝟙 (V i) = Δ ≫ q₃ i i i}
    {e : D.x i ⟶ D.x i}
    (he : FibreHom p (D.x i) (D.x i) (D.hx i) (D.hx i) e)
    (heij : IsRestrictionOf p Δ hΔ₁ hΔ₂ (D.wi i i i) (D.wj i i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.αij i i i) e)
    (hejk : IsRestrictionOf p Δ hΔ₂ hΔ₃ (D.wj i i i) (D.wk i i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.αjk i i i) e)
    (heik : IsRestrictionOf p Δ hΔ₁ hΔ₃ (D.wi i i i) (D.wk i i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.αik i i i) e) :
    e = 𝟙 (D.x i) := by
  have hlift : p.IsHomLift (𝟙 (p.obj (D.x i))) e := by
    simpa only [FibreHom, eqToHom_trans, eqToHom_refl] using he
  have : IsIso e := isIso_of_isHomLift_id p hp e hlift
  exact (cancel_mono e).mp
    ((D.comp_eq_of_restrictionOf he he he heij hejk heik).trans (Category.id_comp e).symm)

/-- Let `D` be a descent datum and `Δ₁₃ : Vij i j ⟶ Vijk i j i` the morphism whose composites
with the three projections are `pr₁ i j`, `pr₂ i j` and `pr₁ i j`. If `σφ` is the pullback along
`Δ₁₃` of the `(j, k)` gluing isomorphism of the triple `(i, j, i)`, then `φ i j ≫ σφ = 𝟙`.

This takes as input `hik`, the restriction of `φ i i` to the identity along `Δ₁₃`, which in
the source is derived from 026C (1). Stacks 026C (2) itself, with no such input and phrased with
the pullback of `φ j i` along the switching morphism `Vij i j ⟶ Vij j i`, is
`DescentDatum.gluing_comp_eq_id_of_isRestrictionOf_switch` and
`DescentDatum.isRestrictionOf_switch_inv`. -/
theorem DescentDatum.gluing_comp_switchPullback_eq_id
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i j : I) {Δ₁₃ : Vij i j ⟶ Vijk i j i}
    {hΔ₁ : pr₁ i j = Δ₁₃ ≫ q₁ i j i} {hΔ₂ : pr₂ i j = Δ₁₃ ≫ q₂ i j i}
    {hΔ₃ : pr₁ i j = Δ₁₃ ≫ q₃ i j i}
    {σφ : (D.xrji i j).pt ⟶ (D.xrij i j).pt}
    (hσφ : FibreHom p (D.xrji i j).pt (D.xrij i j).pt
      (D.xrji i j).hpt (D.xrij i j).hpt σφ)
    (hij : IsRestrictionOf p Δ₁₃ hΔ₁ hΔ₂ (D.wi i j i) (D.wj i j i)
      (D.xrij i j) (D.xrji i j) (D.αij i j i) (D.φ i j))
    (hji : IsRestrictionOf p Δ₁₃ hΔ₂ hΔ₃ (D.wj i j i) (D.wk i j i)
      (D.xrji i j) (D.xrij i j) (D.αjk i j i) σφ)
    (hik : IsRestrictionOf p Δ₁₃ hΔ₁ hΔ₃ (D.wi i j i) (D.wk i j i)
      (D.xrij i j) (D.xrij i j) (D.αik i j i) (𝟙 (D.xrij i j).pt)) :
    D.φ i j ≫ σφ = 𝟙 (D.xrij i j).pt := by
  exact D.comp_eq_of_restrictionOf (D.φ_fibreHom i j) hσφ
    (FibreHom.id p (D.xrij i j).pt (D.xrij i j).hpt) hij hji hik

/-- The three gluing morphisms `αij`, `αjk`, `αik` of a descent datum over a triple overlap are
morphisms of the fibre category: their images in the base are endomorphisms of the triple
overlap fixing the projections to the double overlaps, and the cocycle condition forces them
to be identities. -/
theorem DescentDatum.α_fibreHom
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i j k : I) :
    FibreHom p (D.wi i j k).pt (D.wj i j k).pt (D.wi i j k).hpt (D.wj i j k).hpt
        (D.αij i j k) ∧
      FibreHom p (D.wj i j k).pt (D.wk i j k).pt (D.wj i j k).hpt (D.wk i j k).hpt
        (D.αjk i j k) ∧
      FibreHom p (D.wi i j k).pt (D.wk i j k).pt (D.wi i j k).hpt (D.wk i j k).hpt
        (D.αik i j k) := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = eqToHom (D.wi i j k).hpt.symm ≫ p.map (D.αij i j k) ≫
      eqToHom (D.wj i j k).hpt := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = eqToHom (D.wj i j k).hpt.symm ≫ p.map (D.αjk i j k) ≫
      eqToHom (D.wk i j k).hpt := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c, c = eqToHom (D.wi i j k).hpt.symm ≫ p.map (D.αik i j k) ≫
      eqToHom (D.wk i j k).hpt := ⟨_, rfl⟩
  have ha : a ≫ s₁₂ i j k = s₁₂ i j k := by
    rw [ha_def]; exact (D.αij_restr i j k).map_comp_eq (D.φ_fibreHom i j)
  have hb : b ≫ s₂₃ i j k = s₂₃ i j k := by
    rw [hb_def]; exact (D.αjk_restr i j k).map_comp_eq (D.φ_fibreHom j k)
  have hc : c ≫ D.s₁₃ i j k = D.s₁₃ i j k := by
    rw [hc_def]; exact (D.αik_restr i j k).map_comp_eq (D.φ_fibreHom i k)
  have habc : c = a ≫ b := by
    rw [hc_def, ha_def, hb_def, D.cocycle, p.map_comp]
    simp
  have hq₃b : b ≫ q₃ i j k = q₃ i j k := by rw [hq₃, reassoc_of% hb]
  have hq₃a : a ≫ q₃ i j k = q₃ i j k := by
    have h1 : c ≫ q₃ i j k = q₃ i j k := by rw [← D.hs₁₃₂, reassoc_of% hc]
    rwa [habc, Category.assoc, hq₃b] at h1
  have ha1 : a = 𝟙 _ := by
    apply (hVijk i j k).hom_ext
    · rw [ha, Category.id_comp]
    · apply (hVij j k).hom_ext
      · simp only [Category.assoc, Category.id_comp]
        rw [← (hVijk i j k).w, reassoc_of% ha]
      · simp only [Category.assoc, Category.id_comp]
        rw [← hq₃, hq₃a]
  have hq₁b : b ≫ q₁ i j k = q₁ i j k := by
    have h1 : c ≫ q₁ i j k = q₁ i j k := by rw [← D.hs₁₃₁, reassoc_of% hc]
    rwa [habc, ha1, Category.id_comp] at h1
  have hb1 : b = 𝟙 _ := by
    apply (hVijk i j k).hom_ext
    · apply (hVij i j).hom_ext
      · simp only [Category.assoc, Category.id_comp]
        rw [← hq₁, hq₁b]
      · simp only [Category.assoc, Category.id_comp]
        rw [(hVijk i j k).w, reassoc_of% hb]
    · rw [hb, Category.id_comp]
  have hc1 : c = 𝟙 _ := by rw [habc, ha1, hb1, Category.id_comp]
  refine ⟨FibreHom.of_map_eq ?_, FibreHom.of_map_eq ?_, FibreHom.of_map_eq ?_⟩
  · rw [← ha_def, ha1]
  · rw [← hb_def, hb1]
  · rw [← hc_def, hc1]

/-- **Stacks 026C (1).** Let `D` be a descent datum for any functor `p : 𝒮 ⥤ 𝒞` (in particular
for any fibred category, not necessarily fibred in groupoids), and `Δ : V i ⟶ Vij i i` a
diagonal, i.e. `Δ ≫ pr₁ i i = 𝟙` and `Δ ≫ pr₂ i i = 𝟙`. A fibre endomorphism `e` of `x i`
which is the pullback `Δ^* φ i i` of the gluing isomorphism `φ i i` along `Δ` is the identity.

The proof is the source's: pulling back the cocycle condition for `(i, i, i)` along the
diagonal `Δ₁₂₃ : V i ⟶ Vijk i i i` gives `e ≫ e = e`, and `e` is a monomorphism. -/
@[stacks 026C "(1): `Δ^*φ_ii = id` for a general fibred category"]
theorem DescentDatum.eq_id_of_isRestrictionOf_diagonal
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i : I) {Δ : V i ⟶ Vij i i}
    (hΔ₁ : 𝟙 (V i) = Δ ≫ pr₁ i i) (hΔ₂ : 𝟙 (V i) = Δ ≫ pr₂ i i)
    {e : D.x i ⟶ D.x i}
    (he : FibreHom p (D.x i) (D.x i) (D.hx i) (D.hx i) e)
    (hr : IsRestrictionOf p Δ hΔ₁ hΔ₂ (D.xrij i i) (D.xrji i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i)) (D.φ i i) e) :
    e = 𝟙 (D.x i) := by
  let Δ₃ : V i ⟶ Vijk i i i := (hVijk i i i).lift Δ Δ (by rw [← hΔ₁, ← hΔ₂])
  have h₁₂ : Δ₃ ≫ s₁₂ i i i = Δ := (hVijk i i i).lift_fst _ _ _
  have h₂₃ : Δ₃ ≫ s₂₃ i i i = Δ := (hVijk i i i).lift_snd _ _ _
  have h₁₃ : Δ₃ ≫ D.s₁₃ i i i = Δ := by
    apply (hVij i i).hom_ext
    · rw [Category.assoc, D.hs₁₃₁, hq₁, reassoc_of% h₁₂]
    · rw [Category.assoc, D.hs₁₃₂, hq₃, reassoc_of% h₂₃]
  have hd₁ : 𝟙 (V i) = Δ₃ ≫ q₁ i i i := by rw [hq₁, reassoc_of% h₁₂]; exact hΔ₁
  have hd₂ : 𝟙 (V i) = Δ₃ ≫ q₂ i i i := by rw [hq₂, reassoc_of% h₁₂]; exact hΔ₂
  have hd₃ : 𝟙 (V i) = Δ₃ ≫ q₃ i i i := by rw [hq₃, reassoc_of% h₂₃]; exact hΔ₂
  obtain ⟨hαij, hαjk, hαik⟩ := D.α_fibreHom i i i
  have heij : IsRestrictionOf p Δ₃ hd₁ hd₂ (D.wi i i i) (D.wj i i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.αij i i i) e :=
    IsRestrictionOf.of_comp h₁₂ hαij he (D.αij_restr i i i) hr
  have hejk : IsRestrictionOf p Δ₃ hd₂ hd₃ (D.wj i i i) (D.wk i i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.αjk i i i) e :=
    IsRestrictionOf.of_comp h₂₃ hαjk he (D.αjk_restr i i i) hr
  have heik : IsRestrictionOf p Δ₃ hd₁ hd₃ (D.wi i i i) (D.wk i i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.αik i i i) e :=
    IsRestrictionOf.of_comp h₁₃ hαik he (D.αik_restr i i i) hr
  have hee : e ≫ e = e := D.comp_eq_of_restrictionOf he he he heij hejk heik
  have hc : Restriction.compTo p Δ (pr₁ i i) hΔ₁ (D.xrij i i)
      (Restriction.id p (D.x i) (D.hx i)) ≫ (D.xrij i i).hom = 𝟙 (D.x i) :=
    Restriction.compTo_hom p Δ (pr₁ i i) hΔ₁ (D.xrij i i) (Restriction.id p (D.x i) (D.hx i))
  have : IsSplitMono (Restriction.compTo p Δ (pr₁ i i) hΔ₁ (D.xrij i i)
      (Restriction.id p (D.x i) (D.hx i))) := IsSplitMono.mk' ⟨_, hc⟩
  have := D.φ_iso i i
  have hr' : e ≫ Restriction.compTo p Δ (pr₂ i i) hΔ₂ (D.xrji i i)
      (Restriction.id p (D.x i) (D.hx i)) = Restriction.compTo p Δ (pr₁ i i) hΔ₁ (D.xrij i i)
      (Restriction.id p (D.x i) (D.hx i)) ≫ D.φ i i := hr
  have : Mono (e ≫ Restriction.compTo p Δ (pr₂ i i) hΔ₂ (D.xrji i i)
      (Restriction.id p (D.x i) (D.hx i))) := by
    rw [hr']; infer_instance
  have : Mono e := mono_of_mono e (Restriction.compTo p Δ (pr₂ i i) hΔ₂ (D.xrji i i)
    (Restriction.id p (D.x i) (D.hx i)))
  exact (cancel_mono e).mp (hee.trans (Category.id_comp e).symm)

/-- **Stacks 026C (1).** For a descent datum `D` for any functor `p : 𝒮 ⥤ 𝒞` and a diagonal
`Δ : V i ⟶ Vij i i`, the identity of `x i` is the pullback `Δ^* φ i i` of the gluing
isomorphism `φ i i` along `Δ`: the pullback exists and equals the identity. -/
@[stacks 026C "(1): the pullback of `φ_ii` along the diagonal is `id_{X_i}`"]
theorem DescentDatum.isRestrictionOf_diagonal_id
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i : I) {Δ : V i ⟶ Vij i i}
    (hΔ₁ : 𝟙 (V i) = Δ ≫ pr₁ i i) (hΔ₂ : 𝟙 (V i) = Δ ≫ pr₂ i i) :
    IsRestrictionOf p Δ hΔ₁ hΔ₂ (D.xrij i i) (D.xrji i i)
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i)) (D.φ i i)
      (𝟙 (D.x i)) := by
  obtain ⟨e, he, hr⟩ := IsRestrictionOf.exists_fibreHom Δ hΔ₁ hΔ₂ (D.xrij i i) (D.xrji i i)
    (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i)) (D.φ i i)
    (D.φ_fibreHom i i)
  rwa [D.eq_id_of_isRestrictionOf_diagonal i hΔ₁ hΔ₂ he hr] at hr

/-- **Stacks 026C (2).** Let `D` be a descent datum for any functor `p : 𝒮 ⥤ 𝒞` (in particular
for any fibred category), and `σ : Vij i j ⟶ Vij j i` the switching morphism, i.e.
`σ ≫ pr₁ j i = pr₂ i j` and `σ ≫ pr₂ j i = pr₁ i j`. If the fibre morphism `σφ` is the pullback
`σ^* φ j i` of `φ j i` along `σ`, then `σφ ∘ φ i j = id`, i.e. `φ i j ≫ σφ = 𝟙`.

The proof is the source's: pull back the cocycle condition for `(i, j, i)` along
`Δ₁₃ : Vij i j ⟶ Vijk i j i`; the `(i, i)` term is the pullback of `Δ^* φ i i`, which is the
identity by part (1) (`DescentDatum.isRestrictionOf_diagonal_id`). -/
@[stacks 026C "(2): `(σ^*φ_ji) ∘ φ_ij = id` for a general fibred category"]
theorem DescentDatum.gluing_comp_eq_id_of_isRestrictionOf_switch
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i j : I) {σ : Vij i j ⟶ Vij j i}
    (hσ₁ : pr₂ i j = σ ≫ pr₁ j i) (hσ₂ : pr₁ i j = σ ≫ pr₂ j i)
    {σφ : (D.xrji i j).pt ⟶ (D.xrij i j).pt}
    (hσφ : FibreHom p (D.xrji i j).pt (D.xrij i j).pt (D.xrji i j).hpt (D.xrij i j).hpt σφ)
    (hr : IsRestrictionOf p σ hσ₁ hσ₂ (D.xrij j i) (D.xrji j i) (D.xrji i j) (D.xrij i j)
      (D.φ j i) σφ) :
    D.φ i j ≫ σφ = 𝟙 (D.xrij i j).pt := by
  let Δ₁₃ : Vij i j ⟶ Vijk i j i :=
    (hVijk i j i).lift (𝟙 _) σ ((Category.id_comp _).trans hσ₁)
  let δ : V i ⟶ Vij i i := (hVij i i).lift (𝟙 _) (𝟙 _) rfl
  have hδ₁ : 𝟙 (V i) = δ ≫ pr₁ i i := ((hVij i i).lift_fst _ _ _).symm
  have hδ₂ : 𝟙 (V i) = δ ≫ pr₂ i i := ((hVij i i).lift_snd _ _ _).symm
  have h₁₂ : Δ₁₃ ≫ s₁₂ i j i = 𝟙 _ := (hVijk i j i).lift_fst _ _ _
  have h₂₃ : Δ₁₃ ≫ s₂₃ i j i = σ := (hVijk i j i).lift_snd _ _ _
  have h₁₃ : Δ₁₃ ≫ D.s₁₃ i j i = pr₁ i j ≫ δ := by
    apply (hVij i i).hom_ext
    · simp only [Category.assoc]
      rw [D.hs₁₃₁, hq₁, reassoc_of% h₁₂, ← hδ₁, Category.comp_id]
    · simp only [Category.assoc]
      rw [D.hs₁₃₂, hq₃, reassoc_of% h₂₃, ← hσ₂, ← hδ₂, Category.comp_id]
  have hd₁ : pr₁ i j = Δ₁₃ ≫ q₁ i j i := by rw [hq₁, reassoc_of% h₁₂]
  have hd₂ : pr₂ i j = Δ₁₃ ≫ q₂ i j i := by rw [hq₂, reassoc_of% h₁₂]
  have hd₃ : pr₁ i j = Δ₁₃ ≫ q₃ i j i := by rw [hq₃, reassoc_of% h₂₃, ← hσ₂]
  obtain ⟨hαij, hαjk, hαik⟩ := D.α_fibreHom i j i
  have hij : IsRestrictionOf p Δ₁₃ hd₁ hd₂ (D.wi i j i) (D.wj i j i)
      (D.xrij i j) (D.xrji i j) (D.αij i j i) (D.φ i j) :=
    IsRestrictionOf.of_comp h₁₂ hαij (D.φ_fibreHom i j) (D.αij_restr i j i)
      (IsRestrictionOf.refl p (Category.id_comp _).symm (Category.id_comp _).symm
        (D.xrij i j) (D.xrji i j) (D.φ i j))
  have hji : IsRestrictionOf p Δ₁₃ hd₂ hd₃ (D.wj i j i) (D.wk i j i)
      (D.xrji i j) (D.xrij i j) (D.αjk i j i) σφ :=
    IsRestrictionOf.of_comp h₂₃ hαjk hσφ (D.αjk_restr i j i) hr
  have hid : IsRestrictionOf p (pr₁ i j) (Category.comp_id _).symm (Category.comp_id _).symm
      (Restriction.id p (D.x i) (D.hx i)) (Restriction.id p (D.x i) (D.hx i))
      (D.xrij i j) (D.xrij i j) (𝟙 (D.x i)) (𝟙 (D.xrij i j).pt) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hδ : IsRestrictionOf p (pr₁ i j ≫ δ)
      (by rw [Category.assoc, ← hδ₁, Category.comp_id])
      (by rw [Category.assoc, ← hδ₂, Category.comp_id])
      (D.xrij i i) (D.xrji i i) (D.xrij i j) (D.xrij i j) (D.φ i i) (𝟙 (D.xrij i j).pt) :=
    IsRestrictionOf.trans rfl (D.isRestrictionOf_diagonal_id i hδ₁ hδ₂) hid
  have hik : IsRestrictionOf p Δ₁₃ hd₁ hd₃ (D.wi i j i) (D.wk i j i)
      (D.xrij i j) (D.xrij i j) (D.αik i j i) (𝟙 (D.xrij i j).pt) :=
    IsRestrictionOf.of_comp h₁₃ hαik (FibreHom.id p (D.xrij i j).pt (D.xrij i j).hpt)
      (D.αik_restr i j i) hδ
  exact D.comp_eq_of_restrictionOf (D.φ_fibreHom i j) hσφ
    (FibreHom.id p (D.xrij i j).pt (D.xrij i j).hpt) hij hji hik

/-- **Stacks 026C (2).** For a descent datum `D` for any functor `p : 𝒮 ⥤ 𝒞` and the switching
morphism `σ : Vij i j ⟶ Vij j i`, the inverse of `φ i j` is the pullback `σ^* φ j i` of `φ j i`
along `σ`: the pullback exists and `(σ^* φ j i) ∘ φ i j = id`. -/
@[stacks 026C "(2): the pullback of `φ_ji` along the switching morphism is `φ_ij⁻¹`"]
theorem DescentDatum.isRestrictionOf_switch_inv
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i j : I) {σ : Vij i j ⟶ Vij j i}
    (hσ₁ : pr₂ i j = σ ≫ pr₁ j i) (hσ₂ : pr₁ i j = σ ≫ pr₂ j i) :
    IsRestrictionOf p σ hσ₁ hσ₂ (D.xrij j i) (D.xrji j i) (D.xrji i j) (D.xrij i j)
      (D.φ j i) (CategoryTheory.inv (I := D.φ_iso i j) (D.φ i j)) := by
  have := D.φ_iso i j
  obtain ⟨σφ, hσφ, hr⟩ := IsRestrictionOf.exists_fibreHom σ hσ₁ hσ₂ (D.xrij j i) (D.xrji j i)
    (D.xrji i j) (D.xrij i j) (D.φ j i) (D.φ_fibreHom j i)
  rwa [IsIso.eq_inv_of_hom_inv_id
    (D.gluing_comp_eq_id_of_isRestrictionOf_switch i j hσ₁ hσ₂ hσφ hr)] at hr

end Identities

end CategoryTheory.Functor
