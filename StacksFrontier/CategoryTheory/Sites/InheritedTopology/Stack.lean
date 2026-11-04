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

* `CategoryTheory.Functor.DescentDatum.diagonalPullback_eq_id`: the pullback of the gluing
  isomorphism `φ i i` along the diagonal is the identity of `x i`.
* `CategoryTheory.Functor.DescentDatum.gluing_comp_switchPullback_eq_id`: the pullback of
  `φ j i` along the switching morphism is inverse to `φ i j`.

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
`J U`. -/
@[stacks_fixed 02ZI]
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
  show p.IsHomLift (eqToHom ha ≫ eqToHom ha.symm) (𝟙 a)
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
  show p.IsHomLift (eqToHom ha ≫ eqToHom hc.symm) (α ≫ β)
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
  show (β₁ ≫ β₂) ≫ Restriction.compTo p g fz hfz zr zrW
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
gluing isomorphisms of the triple `(i, i, i)` is the identity. -/
@[stacks 026C "diagonal identity"]
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
`Δ₁₃` of the `(j, k)` gluing isomorphism of the triple `(i, j, i)`, then `φ i j ≫ σφ = 𝟙`. -/
@[stacks 026C "flip identity"]
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

end Identities

end CategoryTheory.Functor
