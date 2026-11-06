module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Adjoint functors and products of K-injective complexes

* An additive functor with an exact additive left adjoint sends K-injective complexes to
  K-injective complexes ([Stacks, Tag 08BJ]):
  `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`.
* A product of K-injective complexes is K-injective and represents the product in the derived
  category ([Stacks, Tag 0BK6]): `Stacks.Injectives.KInjectiveProduct.product_repr_derived`.
-/

section

/-! ### An adjoint criterion for K-injectivity ([Stacks, Tag 08BJ])

Let `u : A ⥤ B` be an additive functor between abelian categories with an additive left adjoint
`v : B ⥤ A`. If `v` sends acyclic cochain complexes to acyclic cochain complexes, then `u` sends
K-injective cochain complexes to K-injective cochain complexes.

## Main results

* `CategoryTheory.Adjunction.mapHomologicalComplex`: an adjunction between additive functors
  induces an adjunction between the associated functors on homological complexes.
* `HomologicalComplex.Acyclic.map`: an exact functor preserves acyclicity.
* `CochainComplex.isKInjective_mapHomologicalComplex`: the criterion, with acyclicity-preservation
  as an explicit hypothesis.
* `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`: the same criterion for a left
  adjoint that preserves finite limits and finite colimits.

## Implementation notes

The hypothesis of `CochainComplex.isKInjective_mapHomologicalComplex` is acyclicity-preservation
rather than exactness of `v`. This is what the argument uses, and it is available in situations
where `Limits.PreservesFiniteLimits v` and `Limits.PreservesFiniteColimits v` are not obtainable by
instance synthesis; `CochainComplex.isKInjective_mapHomologicalComplex_of_exact` recovers the
exactness form.

Null-homotopies are transported along `u` through `CategoryTheory.Functor.mapHomotopyCategory`,
using `HomotopyCategory.quotient_map_eq_zero_iff` to move between a vanishing morphism of homotopy
categories and a null-homotopy of chain maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]

/-- An adjunction `F ⊣ G` between additive functors induces an adjunction
`F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c` between the functors acting degreewise on
homological complexes of shape `c`. Its unit and counit are the degreewise unit and counit. -/
noncomputable def Adjunction.mapHomologicalComplex
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : F ⊣ G)
    {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c :=
  Adjunction.mkOfUnitCounit
    { unit := NatTrans.mapHomologicalComplex adj.unit c
      counit := NatTrans.mapHomologicalComplex adj.counit c
      left_triangle := by ext X i; simp
      right_triangle := by ext X i; simp }

end CategoryTheory

namespace HomologicalComplex

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]

/-- An exact functor, i.e. one preserving finite limits and finite colimits, sends acyclic
complexes to acyclic complexes. -/
theorem Acyclic.map (v : B ⥤ A) [v.Additive] [PreservesFiniteLimits v]
    [PreservesFiniteColimits v] {ι : Type*} {c : ComplexShape ι} {M : HomologicalComplex B c}
    (hM : M.Acyclic) : ((v.mapHomologicalComplex c).obj M).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff]
  exact ((HomologicalComplex.exactAt_iff _ n).1 (hM n)).map v

end HomologicalComplex

namespace CochainComplex

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]

/-- **Adjoint criterion for K-injectivity.** Let `v ⊣ u` be an adjunction of additive functors
between abelian categories. If the left adjoint `v` carries acyclic cochain complexes to acyclic
cochain complexes, then the right adjoint `u` carries K-injective cochain complexes to K-injective
cochain complexes. -/
theorem isKInjective_mapHomologicalComplex
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive] (adj : v ⊣ u)
    (hv : ∀ M : CochainComplex B ℤ, M.Acyclic →
      HomologicalComplex.Acyclic ((v.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  refine ⟨fun {M} f hM => ?_⟩
  let c := ComplexShape.up ℤ
  let adjc := adj.mapHomologicalComplex c
  -- Transpose `f : M ⟶ u(I)` across the degreewise adjunction to `g : v(M) ⟶ I`.
  let g : (v.mapHomologicalComplex c).obj M ⟶ I := (adjc.homEquiv M I).symm f
  -- `v(M)` is acyclic, so K-injectivity of `I` kills `g` in the homotopy category.
  have hg : ((HomotopyCategory.quotient A c).map g) = 0 :=
    (HomotopyCategory.quotient_map_eq_zero_iff g).2
      (CochainComplex.IsKInjective.nonempty_homotopy_zero g (hv M hM))
  have hf : f = adjc.unit.app M ≫ (u.mapHomologicalComplex c).map g := by
    have h := adjc.homEquiv_unit (X := M) (Y := I) (f := g)
    rwa [show adjc.homEquiv M I g = f from (adjc.homEquiv M I).apply_symm_apply f] at h
  -- Transport the vanishing along `u.mapHomotopyCategory c`, which is additive.
  have key : (HomotopyCategory.quotient B c).map ((u.mapHomologicalComplex c).map g) = 0 := by
    have hnat := (u.mapHomotopyCategoryFactors c).hom.naturality g
    simp only [Functor.comp_map, hg, Functor.map_zero, zero_comp] at hnat
    exact (cancel_epi ((u.mapHomotopyCategoryFactors c).hom.app _)).mp
      (hnat.symm.trans comp_zero.symm)
  rw [← HomotopyCategory.quotient_map_eq_zero_iff, hf, Functor.map_comp, key, comp_zero]

/-- **Stacks 08BJ.** Adjoint criterion for K-injectivity, exactness form: let `u : A ⥤ B` and
`v : B ⥤ A` be additive functors between abelian categories such that `u` is right adjoint to `v`
and `v` is exact. Then `u` carries K-injective cochain complexes to K-injective cochain
complexes. -/
@[stacks 08BJ]
theorem isKInjective_mapHomologicalComplex_of_exact
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive] (adj : v ⊣ u)
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  isKInjective_mapHomologicalComplex u v adj (fun _ hM => hM.map v) I

end CochainComplex

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

(Stacks Project, Tag `0BK6`, Lemma 13.31.5.)

Throughout, `A` is an abelian category. We write:
- `Comp(A)` for the category of cochain complexes in `A` (in Lean: `CochainComplex A ℤ`).
- `K(A)` for the homotopy category of complexes: same objects, with morphisms being
  chain maps up to chain homotopy (in Lean: `HomotopyCategory A (ComplexShape.up ℤ)`,
  obtained via the quotient functor `HomotopyCategory.quotient`).
- `D(A)` for the derived category, i.e. the localization of `K(A)` at the class of
  quasi-isomorphisms (in Lean: `DerivedCategory A`, with `DerivedCategory.Q` the
  localization functor `Comp(A) ⥤ D(A)`).

## Main Definitions

Definition 1 (Acyclic complex). A complex `M` is acyclic if all of its cohomology
objects vanish, i.e. `H^n(M) = 0` for all `n`. In Mathlib this is
`HomologicalComplex.Acyclic`, which unfolds to `∀ i, M.ExactAt i`.

Definition 2 (K-injective complex; Stacks Tag 070H / Definition 13.31.1).
A complex `I` is K-injective if for every acyclic complex `M` one has
`Hom_{K(A)}(M, I) = 0`. We formalize "the hom-group is `0`" as: every morphism
`(quotient).obj M ⟶ (quotient).obj I` in the homotopy category equals `0`
(the homotopy category is preadditive, so its hom-sets are abelian groups).

Definition 3 (Product in `D(A)`). Given a family `(X_t)_{t ∈ T}` in `D(A)`, an object
`P` together with morphisms `π_t : P → X_t` is a product of the family if for every `Y`
the induced map `Hom_{D(A)}(Y, P) → ∏ₜ Hom_{D(A)}(Y, X_t)`, `φ ↦ (π_t ∘ φ)`, is a
bijection. We say "`I` represents the product of the `I_t` in `D(A)`" when this map is
a bijection for `P = Q(I)` and the projections induced by the levelwise product
projections.

## Main Statements

Let `A` be an abelian category, `T` a set, and for each `t ∈ T` let `I_t` be a
K-injective complex. Assume that for every `n` the product `I^n = ∏ₜ I_t^n` exists in
`A`. Let `I` be the complex with terms `I^n` and differentials induced by the universal
property of products (in Lean: the categorical product complex `∏ᶜ I` in
`CochainComplex A ℤ`, whose degree-`n` term is `∏ₜ I_t^n` and whose projections are the
levelwise product projections). Then:

- Statement 1. `I` is a K-injective complex.
- Statement 2. `I` represents the product of the family `(I_t)` in `D(A)`; equivalently,
  for every complex `K` the natural map
  `Hom_{D(A)}(K, I) → ∏ₜ Hom_{D(A)}(K, I_t)` induced by the projections `I → I_t`
  is a bijection.
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Injectives.KInjectiveProduct

variable {C : Type*} [Category C] [Abelian C]

-- Main Definition(s)

/-! Definition 2 (K-injective complex) is Mathlib's `CochainComplex.IsKInjective`. The form used
below -- every map `Q(M) ⟶ Q(I)` out of an acyclic `M` is zero -- is the same condition, the two
being related by `HomotopyCategory.quotient_map_eq_zero_iff`, so this section uses Mathlib's. -/

/-- The natural comparison map of Definition 3 / Statement 2, in the derived category.
Given the family `X = (I_t)` whose product complex `∏ᶜ X` exists, this sends a derived
morphism `φ : Q(K) ⟶ Q(∏ᶜ X)` to the family `(φ ≫ Q(π_t))_t`, where `π_t = Pi.π X t`
are the projections of the product complex (induced by the levelwise product
projections). -/
noncomputable def derivedHomComparison [HasDerivedCategory C]
    {T : Type} (X : T → CochainComplex C ℤ) [HasProduct X] (K : CochainComplex C ℤ) :
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (∏ᶜ X)) →
      (∀ t, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (X t)) :=
  fun φ t => φ ≫ DerivedCategory.Q.map (Pi.π X t)

/-- For a family `X` of cochain complexes, the degree `n` term of the product complex `∏ᶜ X` is
isomorphic to the product `∏ᶜ (fun t => (X t).X n)` of the degree `n` terms. -/
theorem productComplex_degreewise {T : Type} (X : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasProduct fun t => (X t).X n] [HasProduct X] (n : ℤ) :
    Nonempty ((∏ᶜ X : CochainComplex C ℤ).X n ≅ ∏ᶜ (fun t => (X t).X n)) := by
  have hl : ∀ i : ℤ,
      HasLimit (Discrete.functor X ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) i) :=
    fun i => hasLimit_of_iso (F := Discrete.functor (fun t => (X t).X i))
      (Discrete.natIso (fun ⟨t⟩ => Iso.refl _))
  let c := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCone (limit.cone (Discrete.functor
      X))
  have hc : IsLimit c := isLimitOfPreserves _ (limit.isLimit (Discrete.functor X))
  exact ⟨hc.conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso (fun ⟨t⟩ => Iso.refl _))⟩

-- Auxiliary results

/-- The eval functor preserves the product, giving an `IsLimit` of the fan with apex
`(∏ᶜ X).X n` and projections `(Pi.π X t).f n`.  This is the key bridge for assembling a
homotopy on `∏ᶜ X` out of homotopies on each `X t`: a map *into* `(∏ᶜ X).X n` is
determined by its composites with the levelwise projections `(Pi.π X t).f n`. -/
noncomputable def productEvalIsLimit {T : Type} (X : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasProduct fun t => (X t).X n] [HasProduct X] (n : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ X : CochainComplex C ℤ).X n)
      (fun t => (Pi.π X t).f n)) := by
  haveI hl : ∀ i : ℤ,
      HasLimit (Discrete.functor X ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) i) :=
    fun i => hasLimit_of_iso (F := Discrete.functor (fun t => (X t).X i))
      (Discrete.natIso (fun ⟨t⟩ => Iso.refl _))
  let α : Discrete.functor X ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n
      ≅ Discrete.functor (fun t => (X t).X n) := Discrete.natIso (fun ⟨t⟩ => Iso.refl _)
  refine ((IsLimit.postcomposeHomEquiv α _).symm
    (isLimitOfPreserves _ (limit.isLimit (Discrete.functor X)))).ofIsoLimit
      (Cone.ext (Iso.refl _) ?_)
  rintro ⟨t⟩
  simp [α]

/-- **Statement 1, homotopy-assembly kernel.**  If `g : M ⟶ ∏ᶜ X` is a chain map whose
composite `g ≫ Pi.π X t` with each projection is null-homotopic, then `g` itself is
null-homotopic.  This is the heart of Statement 1: the homotopy on `∏ᶜ X` is built
levelwise from the componentwise homotopies, using `productEvalIsLimit` to lift a fan of
maps `(H t).hom i j : M.X i ⟶ (X t).X j` into a single map `M.X i ⟶ (∏ᶜ X).X j`. -/
theorem product_homotopyZero_of_componentwise {T : Type} (X : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasProduct fun t => (X t).X n] [HasProduct X]
    {M : CochainComplex C ℤ} (g : M ⟶ (∏ᶜ X : CochainComplex C ℤ))
    (H : ∀ t, Homotopy (g ≫ Pi.π X t) 0) : Nonempty (Homotopy g 0) := by
  refine ⟨
    { hom := fun i j => (productEvalIsLimit X j).lift (Fan.mk (M.X i) (fun t => (H t).hom i j))
      zero := ?_
      comm := ?_ }⟩
  · intro i j hij
    apply (productEvalIsLimit X j).hom_ext
    rintro ⟨t⟩
    rw [(productEvalIsLimit X j).fac]
    simp only [Fan.mk_pt, Fan.mk_π_app, zero_comp]
    exact (H t).zero i j hij
  · -- After projecting to each factor `(Pi.π X t).f i`, which commutes with `dNext` and
    -- `prevD`, the assembled `hom` reduces to `(H t).hom` and the identity is `(H t).comm i`.
    intro i
    apply (productEvalIsLimit X i).hom_ext
    rintro ⟨t⟩
    simp only [Fan.mk_pt, Fan.mk_π_app]
    have key : ∀ a j, (productEvalIsLimit X j).lift (Fan.mk (M.X a) (fun t => (H t).hom a j)) ≫
        (Pi.π X t).f j = (H t).hom a j := fun a j => by
      simpa using (productEvalIsLimit X j).fac (Fan.mk (M.X a) (fun t => (H t).hom a j)) ⟨t⟩
    rw [Preadditive.add_comp, Preadditive.add_comp, ← dNext_comp_right, ← prevD_comp_right]
    simp only [key, ← HomologicalComplex.comp_f, zero_comp]
    exact (H t).comm i

/-- Statement 1, in the language of Mathlib's `CochainComplex.IsKInjective` class:
a product of K-injective complexes is K-injective.  This is the same content as the
project-level `product_isKInjective` below, phrased via the Mathlib class so that the
derived-category bijection `Qh_map_bijective` can be applied in Statement 2. -/
theorem product_mathlib_isKInjective {T : Type} (X : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasProduct fun t => (X t).X n] [HasProduct X]
    (hX : ∀ t, (X t).IsKInjective) : (∏ᶜ X : CochainComplex C ℤ).IsKInjective :=
  ⟨fun f hM => product_homotopyZero_of_componentwise X f
    fun t => (hX t).homotopyZero (f ≫ Pi.π X t) hM⟩

-- Main Statement(s)

/-- Statement 1. A product of K-injective complexes is K-injective. -/
@[stacks 0BK6]
alias product_isKInjective := Stacks.Injectives.KInjectiveProduct.product_mathlib_isKInjective

/-- **Statement 2, sub-lemma [4b]: the product complex is a product in `K(A)`.**
The image `q(∏ᶜ X)` of the product complex under the homotopy quotient functor, together
with the legs `q(Pi.π X t)`, is a limit fan (i.e. the categorical product of the family
`(q(X t))` in the homotopy category `K(A)`).

INFORMAL ARGUMENT.  A fan with apex `q(K)` and legs `f_t : q(K) ⟶ q(X t)` is to be lifted
uniquely (in `K(A)`) through `q(∏ᶜ X)`.
* Existence: choose chain-map representatives `g_t : K ⟶ X t` of the `f_t`
  (`Quot.exists_rep`), form `g := Pi.lift g_t : K ⟶ ∏ᶜ X` (universal property of `∏ᶜ X` in
  `CochainComplex`), and take `q(g)`.  Then `q(g) ≫ q(Pi.π X t) = q(g ≫ Pi.π X t)
  = q(g_t) = f_t` since `g ≫ Pi.π X t = g_t` (`Pi.lift_comp_π`).
* Uniqueness: if `q(h)` also satisfies `q(h) ≫ q(Pi.π X t) = f_t` for all `t`, then for
  each `t`, `(h - g) ≫ Pi.π X t` is null-homotopic; the kernel lemma
  `product_homotopyZero_of_componentwise` (applied to `h - g`) shows `h - g` is
  null-homotopic, i.e. `q(h) = q(g)`.
STRATEGY for formal phase: build via `Fan.IsLimit`/`mkFanLimit`, using `Pi.lift` for the
lift, `Pi.lift_comp_π` + functoriality of `q` for the fac condition, and
`product_homotopyZero_of_componentwise` (on `h - g`, with
`HomotopyCategory.quotient_map_eq_zero_iff`)
for uniqueness. -/
noncomputable def productHomotopyIsLimit {T : Type} (X : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasProduct fun t => (X t).X n] [HasProduct X] :
    IsLimit (Fan.mk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (∏ᶜ X))
      (fun t => (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (Pi.π X t))) := by
  classical
  set q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  refine Fan.IsLimit.mk _
    (fun s => q.map (Pi.lift (fun t =>
      ((Quot.exists_rep (s.proj t)).choose : s.pt.as ⟶ X t)))) ?_ ?_
  · intro s t
    change q.map _ ≫ q.map (Pi.π X t) = s.proj t
    rw [← q.map_comp, Pi.lift_comp_π]
    exact (Quot.exists_rep (s.proj t)).choose_spec
  · intro s m hm
    obtain ⟨h₀, hh₀⟩ := Quot.exists_rep m
    let h : s.pt.as ⟶ (∏ᶜ X : CochainComplex C ℤ) := h₀
    have hh : q.map h = m := hh₀
    let gt : ∀ t, s.pt.as ⟶ X t := fun t => (Quot.exists_rep (s.proj t)).choose
    let g : s.pt.as ⟶ (∏ᶜ X : CochainComplex C ℤ) := Pi.lift gt
    have hcomp : ∀ t, q.map ((h - g) ≫ Pi.π X t) = 0 := by
      intro t
      rw [Preadditive.sub_comp, q.map_sub, q.map_comp, q.map_comp]
      have e2 : q.map h ≫ q.map (Pi.π X t) = s.proj t := by
        rw [hh]
        exact hm t
      have e3 : q.map g ≫ q.map (Pi.π X t) = s.proj t := by
        rw [← q.map_comp]
        change q.map (Pi.lift gt ≫ Pi.π X t) = s.proj t
        rw [Pi.lift_comp_π]
        exact (Quot.exists_rep (s.proj t)).choose_spec
      rw [e2, e3, sub_self]
    have hzero : q.map (h - g) = 0 := (HomotopyCategory.quotient_map_eq_zero_iff _).mpr
      (product_homotopyZero_of_componentwise X (h - g)
        fun t => ((HomotopyCategory.quotient_map_eq_zero_iff _).mp (hcomp t)).some)
    rw [q.map_sub, sub_eq_zero, hh] at hzero
    exact hzero

/-- Statement 2. The product complex `∏ᶜ X` represents the product of the family `(I_t)`
in the derived category `D(A)`: for every complex `K`, the natural comparison map
`Hom_{D(A)}(K, ∏ᶜ X) → ∏ₜ Hom_{D(A)}(K, I_t)` induced by the projections is a bijection
(hence an isomorphism of abelian groups). -/
@[stacks 0BK6]
theorem product_repr_derived [HasDerivedCategory C]
    {T : Type} (X : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasProduct fun t => (X t).X n] [HasProduct X]
    (hX : ∀ t, (X t).IsKInjective) (K : CochainComplex C ℤ) :
    Function.Bijective (derivedHomComparison X K) := by
  -- The comparison is a composite of bijections: the `K(A)`-level fan comparison (the
  -- universal property `productHomotopyIsLimit`), then `Qh.map` at each `X t`, against
  -- `Qh.map` at the apex `∏ᶜ X`, which is K-injective by `product_mathlib_isKInjective`.
  set q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  -- The `K(A)`-level fan comparison is bijective (universal property of the limit fan).
  have hcmpK : Function.Bijective
      (fun (g : q.obj K ⟶ q.obj (∏ᶜ X : CochainComplex C ℤ)) (t : T) =>
        g ≫ q.map (Pi.π X t)) := by
    have hl := productHomotopyIsLimit X
    constructor
    · intro g₁ g₂ h
      apply hl.hom_ext
      rintro ⟨t⟩
      simpa using congrFun h t
    · intro fam
      refine ⟨hl.lift (Fan.mk (q.obj K) fam), ?_⟩
      funext t
      simpa using hl.fac (Fan.mk (q.obj K) fam) ⟨t⟩
  -- `Qh.obj (q.obj Y)` is not definitionally `Q.obj Y`: `HomologicalComplexUpToQuasiIso.Qh` is
  -- defined in a non-exposed section. Each `Qh`-level bijection is therefore transported along
  -- Mathlib's natural isomorphism `quotientCompQhIso : q ⋙ Qh ≅ Q`.
  have hone : ∀ L : CochainComplex C ℤ, L.IsKInjective → Function.Bijective
      (fun (g : q.obj K ⟶ q.obj L) =>
        Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
          ((DerivedCategory.quotientCompQhIso C).app L) (DerivedCategory.Qh.map g)) :=
    fun L _ => (Iso.homCongr _ _).bijective.comp
      (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) L)
  have hFamQh : Function.Bijective
      (fun (G : ∀ t, q.obj K ⟶ q.obj (X t)) (t : T) =>
        Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
          ((DerivedCategory.quotientCompQhIso C).app (X t))
          (DerivedCategory.Qh.map (G t))) :=
    Function.Bijective.piMap fun t => hone (X t) (hX t)
  have hcomp : (derivedHomComparison X K) ∘
      (fun (g : q.obj K ⟶ q.obj (∏ᶜ X : CochainComplex C ℤ)) =>
        Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
          ((DerivedCategory.quotientCompQhIso C).app (∏ᶜ X : CochainComplex C ℤ))
          (DerivedCategory.Qh.map g))
      = (fun (G : ∀ t, q.obj K ⟶ q.obj (X t)) (t : T) =>
          Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
            ((DerivedCategory.quotientCompQhIso C).app (X t))
            (DerivedCategory.Qh.map (G t))) ∘
        (fun (g : q.obj K ⟶ q.obj (∏ᶜ X : CochainComplex C ℤ)) (t : T) =>
          g ≫ q.map (Pi.π X t)) := by
    funext g t
    simp only [Function.comp_apply, derivedHomComparison, Iso.homCongr_apply, Iso.app_hom,
      Iso.app_inv, Functor.map_comp, Category.assoc]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality (Pi.π X t)]
  refine (Function.Bijective.of_comp_iff (derivedHomComparison X K)
    (hone _ (product_mathlib_isKInjective X hX))).mp ?_
  rw [hcomp]
  exact hFamQh.comp hcmpK

end Stacks.Injectives.KInjectiveProduct

end

end
