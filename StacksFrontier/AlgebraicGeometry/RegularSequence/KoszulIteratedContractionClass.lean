module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.IteratedCoordinateContraction
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulContractionClass

/-!
# The composition product of the contraction classes is an iterated contraction

Let `(X, O♯)` be a ringed space, let `φ : (O♯)ʳ ⟶ O♯` be a morphism of sheaves of modules and let
`K` be a Koszul chain complex of `φ`. Read as a cochain complex, `K` is strictly perfect, and the
cohomology sheaves of its internal endomorphism complex `SheafHom^•(K, K)` carry the composition
product. Each coordinate contraction `δⱼ` is a degree-one cocycle there, with cohomology class
`Stacks.RegularSequence.KoszulChainData.contractionClass`.

This file computes the composition product of `i` of those classes. For a tuple
`j₀, …, j_{i-1}` of coordinates the ordered product

`[δ_{j₀}] [δ_{j₁}] ⋯ [δ_{j_{i-1}}]`

is the class of the degree-`i` cocycle whose component between the cochain degrees `p` and `p + i`
is the `i`-fold composite of coordinate contractions

`δ_{j_{i-1}} ≫ ⋯ ≫ δ_{j₀} : K_{-p} ⟶ K_{-p-i}`,

in which the last entry of the tuple contracts first; that is
`Stacks.RegularSequence.KoszulChainData.tupleCoordKoszulDOf` at the reversed tuple, since that
composite contracts by its own first entry first. So an ordered product of degree-one self-Ext
classes of the Koszul complex is, on cocycles, an iterated contraction.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.iteratedContractionSection`: the `i`-fold composite of
  the contraction sections, as a local section of the degree-`i` term of `SheafHom^•(K, K)`.
* `Stacks.RegularSequence.KoszulChainData.iteratedContractionCycle`: **the same, as a global
  degree-`i` cocycle** of `SheafHom^•(K, K)`, in the form of a morphism from the unit sheaf of
  modules into the degree-`i` cycles.
* `Stacks.RegularSequence.KoszulChainData.iteratedContractionClassOn`: its cohomology class, as a
  local section of `H^i(SheafHom(K, K))`.

## Main results

* `Stacks.RegularSequence.KoszulChainData.homogeneousProd_succ_right` and
  `Stacks.RegularSequence.KoszulChainData.homogeneousProd_zero`: the recursion defining the
  ordered product of degree-one local sections of a graded algebra, peeled on the right, where it
  carries no degree transport.
* `Stacks.RegularSequence.KoszulChainData.tupleCoordKoszulDOf_one` and
  `Stacks.RegularSequence.KoszulChainData.tupleCoordKoszulDOf_succ_of`: the iterated contraction
  between named degrees, split off its first factor at a named intermediate degree. These are the
  forms in which the degrees of a cochain of the internal endomorphism complex meet it.
* `Stacks.RegularSequence.KoszulChainData.applyHomSectionOver_iteratedContractionSection`:
  **evaluating the `i`-fold composite returns the `i`-fold iterated contraction** of the section
  it is applied to.
* `Stacks.RegularSequence.KoszulChainData.d_iteratedContractionSection`: the `i`-fold composite is
  a cocycle, by the Leibniz rule and the cocycle identity for a single contraction.
* `Stacks.RegularSequence.KoszulChainData.homogeneousProd_contractionClassOn`: **the ordered
  product of the classes of `i` contractions is the class of the `i`-fold composite.**

## Implementation notes

**The arity is one more than the recursion variable.** The composite is indexed by a tuple
`Fin (i + 1) → ι` and recurses on `i`, so the empty composite never arises. An empty composite
would have to be a degree-zero section of `SheafHom^•(K, K)` — the identity, or equivalently a
transport along `q + 0 = p`, which for `Int` does not reduce — and the arity-one case would then
compare a contraction followed by that transport against the bare contraction. Starting the
recursion at arity one removes the question: an ordered product of degree-one classes with no
factors is the unit of the algebra and is not an iterated contraction of anything.

**The intermediate degree of the split is a parameter.** `tupleCoordKoszulDOf` is defined with its
first factor taken out of degree `p` into degree `p - 1`, while a cochain of the endomorphism
complex meets the same factor as a map out of cochain degree `p` into cochain degree `p + 1`, that
is out of `K_{-p}` into `K_{-(p + 1)}`. The two spellings `-p - 1` and `-(p + 1)` of the
intermediate degree are equal but not syntactically so, and `K.chain.X` applied to them is
therefore not the same type. `tupleCoordKoszulDOf_succ_of` states the split with the intermediate
degree an explicit parameter, so that substituting it discharges the difference; the hypotheses of
the two contractions then agree by proof irrelevance and the identity is definitional.

**The two spellings of the ring sheaf.** The complexes here live in `StructureSheafModules Rc`,
whose ring sheaf is `Stacks.SheafOfModules.structureSheaf Rc`, written through
`CategoryTheory.sheafCompose`; the evaluation API of `AlgebraicGeometry.RingedSite` is stated
over the canonical `Stacks.SheafOfModules.Tensor.ringSheaf X.O`. The two are the same sheaf of
rings by `rfl`, but `sheafCompose` and `Tensor.ringSheaf` are both plain definitions, so a goal
written in one spelling does not match a lemma written in the other at the transparency a
rewrite uses. Both are made `implicit_reducible` locally, as in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolution`.

**The recursion peels the last factor, and the tuple of the contraction is reversed.** The
composition product multiplies on the right, `s₀ ⋯ s_n = (s₀ ⋯ s_{n-1}) · s_n`, and evaluating a
product applies the right factor first. Peeling the last factor therefore matches the recursion of
`Stacks.GradedAlgebra.homogeneousProd` on the nose, which is what makes the product formula an
induction with no reordering; the price is that the composite applies the factors in the opposite
order to the tuple, so the evaluation formula reads the tuple of `tupleCoordKoszulDOf` through
`Fin.rev`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex CochainComplex.HomComplex
open Stacks.ChainComplex Stacks.SheafOfModules

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.RegularSequence.KoszulChainData

/-! ### The ordered product of degree-one sections, peeled on the right -/

section Prod

universe v w a

/-- The ordered product of `k + 1` degree-one local sections of a graded algebra is the product of
the first `k` of them with the last one. This is the recursion defining
`Stacks.GradedAlgebra.homogeneousProd`, with no transport: the degree of the result is
`(k : ℤ) + 1`, which is definitionally `((k + 1 : ℕ) : ℤ)`. The left-handed form, which does carry
a transport, is `Stacks.GradedAlgebra.homogeneousProd_succ`. -/
theorem homogeneousProd_succ_right {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
    (B : Stacks.GradedAlgebra Pc) (Y : Cᵒᵖ) (k : ℕ) (z : Fin (k + 1) → (Pc 1).obj Y) :
    B.homogeneousProd Y (k + 1) z =
      (B.mul (k : ℤ) 1).app Y (B.homogeneousProd Y k fun l => z l.castSucc)
        (z (Fin.last k)) :=
  rfl

/-- The empty ordered product of degree-one local sections is the unit of the algebra. -/
theorem homogeneousProd_zero {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
    (B : Stacks.GradedAlgebra Pc) (Y : Cᵒᵖ) (z : Fin 0 → (Pc 1).obj Y) :
    B.homogeneousProd Y 0 z = B.one.eval Y :=
  rfl

end Prod

/-! ### The iterated contraction between named degrees -/

section Named

universe v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J
    (SheafOfModules.free (R := toRingCat J Osharp) ι)}
  {g : SheafOfModules.free (R := toRingCat J Osharp) ι ⟶
    SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A g)

/-- **The one-fold composite of coordinate contractions is a single contraction**, with no
transport: the empty composite that the recursion of `tupleCoordKoszulDOf` ends with is a
transport along an equality of a degree with itself. -/
theorem tupleCoordKoszulDOf_one (f : Fin 1 → ι) {p q : ℤ} (h : q + ((1 : ℕ) : ℤ) = p) :
    K.tupleCoordKoszulDOf 1 f h = K.coordKoszulD (f 0) (show q + 1 = p by omega) := by
  obtain rfl : q = p - 1 := by omega
  rw [K.tupleCoordKoszulDOf_succ 0 f h]
  simp only [K.tupleCoordKoszulDOf_zero, eqToHom_refl, Category.comp_id]

/-- **The `(i+1)`-fold composite of coordinate contractions splits off its first contraction at a
named intermediate degree.** The intermediate degree is a parameter rather than the expression
`p - 1` that the recursion produces, so that a consumer naming it differently — a cochain of the
internal endomorphism complex names it `-(p + 1)` — can substitute. -/
theorem tupleCoordKoszulDOf_succ_of (i : ℕ) (f : Fin (i + 1) → ι) {p m q : ℤ} (hm : m + 1 = p)
    (hq : q + ((i : ℕ) : ℤ) = m) (h : q + ((i + 1 : ℕ) : ℤ) = p) :
    K.tupleCoordKoszulDOf (i + 1) f h =
      K.coordKoszulD (f 0) hm ≫ K.tupleCoordKoszulDOf i (fun k => f k.succ) hq := by
  obtain rfl : m = p - 1 := by omega
  rfl

/-- **The composite at independently named degrees is the composite between the nonnegative
degrees of the complex**, when the two named degrees are `i` and `0`. The empty composite of
`tupleCoordKoszulDOf` is a transport along an equality of a degree with itself, which is the
identity that `tupleCoordKoszulD` begins with; the recursive steps agree once the intermediate
degree of the split is named `i`, which is what `tupleCoordKoszulDOf_succ_of` allows.

This is the bridge between the indexing a cochain of the internal endomorphism complex produces
and the indexing the stalk computation consumes. -/
theorem tupleCoordKoszulDOf_eq_tupleCoordKoszulD :
    ∀ (i : ℕ) (f : Fin i → ι) (h : ((0 : ℕ) : ℤ) + ((i : ℕ) : ℤ) = ((i : ℕ) : ℤ)),
      K.tupleCoordKoszulDOf i f (p := ((i : ℕ) : ℤ)) (q := ((0 : ℕ) : ℤ)) h =
        K.tupleCoordKoszulD i f := by
  intro i
  induction i with
  | zero =>
      intro f h
      rw [K.tupleCoordKoszulDOf_zero (p := ((0 : ℕ) : ℤ)) (q := ((0 : ℕ) : ℤ)) f h,
        K.tupleCoordKoszulD_zero]
      exact eqToHom_refl _ _
  | succ i ih =>
      intro f h
      have h0 : ((0 : ℕ) : ℤ) + ((i : ℕ) : ℤ) = ((i : ℕ) : ℤ) := by push_cast; ring
      rw [K.tupleCoordKoszulDOf_succ_of i f
          (show ((i : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring) h0,
        ih (fun k => f k.succ) h0, K.tupleCoordKoszulD_succ]
      rfl

/-- **The composite at independently named degrees, when those degrees are only propositionally
`i` and `0`.** A cochain of the internal endomorphism complex names the two degrees as `-(-i)` and
`-(i - i)`, which are `i` and `0` but not syntactically; this states the comparison with the
composite between the degrees of the complex with the two transports made explicit, so that a
consumer can discharge them by substituting the equations rather than by rewriting inside a type
index. -/
theorem tupleCoordKoszulDOf_eq_of_degrees (i : ℕ) (f : Fin i → ι) {p q : ℤ}
    (hp : p = ((i : ℕ) : ℤ)) (hq : q = ((0 : ℕ) : ℤ)) (h : q + ((i : ℕ) : ℤ) = p) :
    K.tupleCoordKoszulDOf i f h =
      eqToHom (congrArg K.chain.X hp) ≫ K.tupleCoordKoszulD i f ≫
        eqToHom (congrArg K.chain.X hq.symm) := by
  subst hp
  subst hq
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact K.tupleCoordKoszulDOf_eq_tupleCoordKoszulD i f h

end Named

/-! ### The iterated contraction as a local section of the endomorphism complex -/

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ)

/-- **The `i`-fold composite of the contraction sections**, as a degree-`i` local section of
`SheafHom^•(K, K)` over an open set. The recursion peels the last entry of the tuple, which is
therefore the innermost factor and the one applied first. -/
noncomputable def iteratedContractionSection :
    (i : ℕ) → (Fin (i + 1) → ULift.{u} (Fin r)) → (U : Opens ↥X) →
      ((endComplex Rc (cochain Rc K)).X ((i + 1 : ℕ) : ℤ)).val.obj (op U)
  | 0 => fun f U => contractionSection Rc K (f 0) U
  | i + 1 => fun f U =>
      RingedSite.compositionSection (ringedSite Rc) U ((i + 1 : ℕ) : ℤ) 1 ((i + 1 + 1 : ℕ) : ℤ)
        (by push_cast; ring) (iteratedContractionSection i (fun k => f k.castSucc) U)
        (contractionSection Rc K (f (Fin.last (i + 1))) U)

/-- The one-fold composite of the contraction sections is a single contraction section. -/
@[simp]
theorem iteratedContractionSection_zero (f : Fin 1 → ULift.{u} (Fin r)) (U : Opens ↥X) :
    iteratedContractionSection Rc K 0 f U = contractionSection Rc K (f 0) U := rfl

/-- The `(i+1)`-fold composite of the contraction sections is the `i`-fold composite of the first
`i` entries of the tuple, composed with the contraction section of the last entry. -/
@[simp]
theorem iteratedContractionSection_succ (i : ℕ) (f : Fin (i + 1 + 1) → ULift.{u} (Fin r))
    (U : Opens ↥X) :
    iteratedContractionSection Rc K (i + 1) f U =
      RingedSite.compositionSection (ringedSite Rc) U ((i + 1 : ℕ) : ℤ) 1 ((i + 1 + 1 : ℕ) : ℤ)
        (by push_cast; ring)
        (iteratedContractionSection Rc K i (fun k => f k.castSucc) U)
        (contractionSection Rc K (f (Fin.last (i + 1))) U) := rfl

/-- **Evaluating the `i`-fold composite returns the `i`-fold iterated contraction.** The component
of the composite between the cochain degrees `p` and `q = p + i` is the composite of the
contractions by the entries of the tuple, the last entry first, read on the terms `K_{-p}` and
`K_{-q}` of the Koszul chain complex. This is the only description of the section a computation
needs. -/
theorem applyHomSectionOver_iteratedContractionSection :
    ∀ (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r)) (U V : Opens ↥X) (g : V ⟶ U) (p q : ℤ)
      (hpq : p + ((i + 1 : ℕ) : ℤ) = q) (x : ((cochain Rc K).X p).val.obj (op V)),
      RingedSite.applyHomSectionOver (ringedSite Rc) (endHom Rc K) U V g ((i + 1 : ℕ) : ℤ) p q
          hpq (iteratedContractionSection Rc K i f U) x =
        (K.tupleCoordKoszulDOf (i + 1) (fun k => f k.rev)
          (show -q + ((i + 1 : ℕ) : ℤ) = -p by omega)).val.app (op V) x := by
  intro i
  induction i with
  | zero =>
      intro f U V g p q hpq x
      have hrev : ((0 : Fin 1).rev) = 0 := by decide
      refine Eq.trans
        (applyHomSectionOver_contractionSection Rc K (f 0) U V g p q (by omega) x) ?_
      refine Eq.trans ?_ (congrArg
        (fun z : K.chain.X (-p) ⟶ K.chain.X (-q) => z.val.app (op V) x)
        (K.tupleCoordKoszulDOf_one (fun k : Fin 1 => f k.rev)
          (show -q + ((1 : ℕ) : ℤ) = -p by omega)).symm)
      exact congrArg
        (fun j : ULift.{u} (Fin r) =>
          (K.coordKoszulD j (show -q + 1 = -p by omega)).val.app (op V) x)
        (congrArg f hrev.symm)
  | succ i ih =>
      intro f U V g p q hpq x
      have htuple : (fun k : Fin (i + 1) => f k.succ.rev) =
          fun k : Fin (i + 1) => f k.rev.castSucc :=
        funext fun k => congrArg f (Fin.rev_succ k)
      have hzero : f (0 : Fin (i + 1 + 1)).rev = f (Fin.last (i + 1)) :=
        congrArg f (Fin.rev_zero (i + 1))
      have h1 : p + 1 + ((i + 1 : ℕ) : ℤ) = q := by push_cast at hpq ⊢; omega
      have h2 : -(p + 1) + 1 = -p := by ring
      refine Eq.trans (RingedSite.compositionSection_applyOver (ringedSite Rc) U V g
        ((i + 1 : ℕ) : ℤ) 1 ((i + 1 + 1 : ℕ) : ℤ) p (p + 1) q (by push_cast; ring) rfl
        (by push_cast at hpq ⊢; omega)
        (iteratedContractionSection Rc K i (fun k => f k.castSucc) U)
        (contractionSection Rc K (f (Fin.last (i + 1))) U) x) ?_
      refine Eq.trans (congrArg
        (fun y : ((cochain Rc K).X (p + 1)).val.obj (op V) =>
          RingedSite.applyHomSectionOver (ringedSite Rc) (endHom Rc K) U V g
            ((i + 1 : ℕ) : ℤ) (p + 1) q h1
            (iteratedContractionSection Rc K i (fun k => f k.castSucc) U) y)
        (applyHomSectionOver_contractionSection Rc K (f (Fin.last (i + 1))) U V g p (p + 1)
          rfl x)) ?_
      refine Eq.trans (ih (fun k => f k.castSucc) U V g (p + 1) q h1
        ((K.coordKoszulD (f (Fin.last (i + 1))) h2).val.app (op V) x)) ?_
      refine Eq.trans ?_ (congrArg
        (fun z : K.chain.X (-p) ⟶ K.chain.X (-q) => z.val.app (op V) x)
        (K.tupleCoordKoszulDOf_succ_of (i + 1) (fun l : Fin (i + 1 + 1) => f l.rev) h2
          (by push_cast at hpq ⊢; omega) (by push_cast at hpq ⊢; omega)).symm)
      rw [hzero, htuple]
      rfl

/-- **The `i`-fold composite is compatible with restriction**, so the sections over all the open
sets assemble into a global section of the degree-`i` term of `SheafHom^•(K, K)`. -/
theorem iteratedContractionSection_restrict (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r))
    {U V : Opens ↥X} (g : V ⟶ U) :
    ((endComplex Rc (cochain Rc K)).X ((i + 1 : ℕ) : ℤ)).val.map g.op
        (iteratedContractionSection Rc K i f U) =
      iteratedContractionSection Rc K i f V := by
  refine RingedSite.homSection_ext (ringedSite Rc) (endHom Rc K) V ((i + 1 : ℕ) : ℤ) ?_
  intro p q hpq W j x
  rw [← RingedSite.applyHomSectionOver_restrict_comp,
    applyHomSectionOver_iteratedContractionSection,
    applyHomSectionOver_iteratedContractionSection]

/-! ### The iterated contraction as a cocycle, and its class -/

/-- Composing with the zero section on the left gives zero. -/
theorem compositionSection_zero_left (U : Opens ↥X) (p q n : ℤ) (hn : p + q = n)
    (γ : ((endComplex Rc (cochain Rc K)).X q).val.obj (op U)) :
    RingedSite.compositionSection (ringedSite Rc) U p q n hn
        (0 : ((endComplex Rc (cochain Rc K)).X p).val.obj (op U)) γ = 0 := by
  have hz := RingedSite.compositionSection_add_left (ringedSite Rc) U p q n hn
    (0 : ((endComplex Rc (cochain Rc K)).X p).val.obj (op U)) 0 γ
  rw [add_zero] at hz
  exact left_eq_add.mp hz

/-- Composing with the zero section on the right gives zero. -/
theorem compositionSection_zero_right (U : Opens ↥X) (p q n : ℤ) (hn : p + q = n)
    (β : ((endComplex Rc (cochain Rc K)).X p).val.obj (op U)) :
    RingedSite.compositionSection (ringedSite Rc) U p q n hn β
        (0 : ((endComplex Rc (cochain Rc K)).X q).val.obj (op U)) = 0 := by
  have hz := RingedSite.compositionSection_add_right (ringedSite Rc) U p q n hn β
    (0 : ((endComplex Rc (cochain Rc K)).X q).val.obj (op U)) 0
  rw [add_zero] at hz
  exact left_eq_add.mp hz

/-- **The `i`-fold composite is a cocycle.** The Leibniz rule writes the differential of a
composite as the sum of the two composites with a differentiated factor, and both factors are
cocycles: the innermost one by the cocycle identity for a single contraction, the other by
induction. -/
theorem d_iteratedContractionSection (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r))
    (U : Opens ↥X) :
    ((endComplex Rc (cochain Rc K)).d ((i + 1 : ℕ) : ℤ) (((i + 1 : ℕ) : ℤ) + 1)).val.app (op U)
        (iteratedContractionSection Rc K i f U) = 0 := by
  induction i with
  | zero => exact d_contractionSection Rc K (f 0) U
  | succ i ih =>
      refine Eq.trans (RingedSite.compositionSection_d (ringedSite Rc) U ((i + 1 : ℕ) : ℤ) 1
        ((i + 1 + 1 : ℕ) : ℤ) (((i + 1 + 1 : ℕ) : ℤ) + 1) (by push_cast; ring)
        (by push_cast; ring) (iteratedContractionSection Rc K i (fun k => f k.castSucc) U)
        (contractionSection Rc K (f (Fin.last (i + 1))) U)) ?_
      rw [ih (fun k => f k.castSucc),
        show ((endComplex Rc (cochain Rc K)).d 1 (1 + 1)).val.app (op U)
            (contractionSection Rc K (f (Fin.last (i + 1))) U) = 0 from
          d_contractionSection Rc K (f (Fin.last (i + 1))) U,
        compositionSection_zero_left, compositionSection_zero_right, smul_zero, add_zero]

/-- **The `i`-fold composite as a global section of the degree-`i` term of
`SheafHom^•(K, K)`**, assembled from its sections over all the open sets. -/
noncomputable def iteratedContractionSections (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r)) :
    ((endComplex Rc (cochain Rc K)).X ((i + 1 : ℕ) : ℤ)).sections :=
  PresheafOfModules.sectionsMk (fun U => iteratedContractionSection Rc K i f U.unop)
    (fun {_ _} j => iteratedContractionSection_restrict Rc K i f j.unop)

/-- **The `i`-fold composite as a morphism from the unit sheaf of modules into the degree-`i` term
of `SheafHom^•(K, K)`.** This is the form in which the cycle below is produced by the
morphism-level `HomologicalComplex.liftCycles`. -/
noncomputable def iteratedContractionMor (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r)) :
    _root_.SheafOfModules.unit (structureSheaf Rc) ⟶
      (endComplex Rc (cochain Rc K)).X ((i + 1 : ℕ) : ℤ) :=
  ((endComplex Rc (cochain Rc K)).X ((i + 1 : ℕ) : ℤ)).unitHomEquiv.symm
    (iteratedContractionSections Rc K i f)

/-- The morphism of the `i`-fold composite takes the unit section to the `i`-fold composite. -/
theorem iteratedContractionMor_val_app_one (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r))
    (U : (Opens ↥X)ᵒᵖ) :
    (iteratedContractionMor Rc K i f).val.app U (1 : (structureSheaf Rc).obj.obj U) =
      iteratedContractionSection Rc K i f U.unop :=
  congrFun (congrArg Subtype.val
    (((endComplex Rc (cochain Rc K)).X ((i + 1 : ℕ) : ℤ)).unitHomEquiv.apply_symm_apply
      (iteratedContractionSections Rc K i f))) U

/-- **The morphism of the `i`-fold composite is killed by the differential**, which is the cocycle
identity read on the unit section. -/
theorem iteratedContractionMor_comp_d (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r)) :
    iteratedContractionMor Rc K i f ≫
        (endComplex Rc (cochain Rc K)).d ((i + 1 : ℕ) : ℤ) (((i + 1 : ℕ) : ℤ) + 1) = 0 := by
  refine ((endComplex Rc (cochain Rc K)).X (((i + 1 : ℕ) : ℤ) + 1)).unitHomEquiv.injective ?_
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  change ((endComplex Rc (cochain Rc K)).d ((i + 1 : ℕ) : ℤ) (((i + 1 : ℕ) : ℤ) + 1)).val.app U
    ((iteratedContractionMor Rc K i f).val.app U (1 : (structureSheaf Rc).obj.obj U)) = _
  rw [iteratedContractionMor_val_app_one, d_iteratedContractionSection]
  rfl

/-- **The `i`-fold composite of the contractions as a global degree-`i` cocycle of
`SheafHom^•(K, K)`**: the morphism of the composite, lifted through the inclusion of the degree-`i`
cycles. -/
noncomputable def iteratedContractionCycle (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r)) :
    _root_.SheafOfModules.unit (structureSheaf Rc) ⟶
      (endComplex Rc (cochain Rc K)).cycles ((i + 1 : ℕ) : ℤ) :=
  (endComplex Rc (cochain Rc K)).liftCycles (iteratedContractionMor Rc K i f)
    (((i + 1 : ℕ) : ℤ) + 1) (by simp) (iteratedContractionMor_comp_d Rc K i f)

/-- The cycle of the `i`-fold composite is, inside the complex, the `i`-fold composite. -/
theorem iCycles_iteratedContractionCycle (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r))
    (U : (Opens ↥X)ᵒᵖ) :
    (((endComplex Rc (cochain Rc K)).iCycles ((i + 1 : ℕ) : ℤ)).val.app U)
        ((iteratedContractionCycle Rc K i f).val.app U
          (1 : (structureSheaf Rc).obj.obj U)) =
      iteratedContractionSection Rc K i f U.unop :=
  (congrArg (fun z => (_root_.SheafOfModules.Hom.val z).app U
      (1 : (structureSheaf Rc).obj.obj U))
    ((endComplex Rc (cochain Rc K)).liftCycles_i (iteratedContractionMor Rc K i f)
      (((i + 1 : ℕ) : ℤ) + 1) (by simp)
      (iteratedContractionMor_comp_d Rc K i f))).trans
    (iteratedContractionMor_val_app_one Rc K i f U)

/-- **The cohomology class of the `i`-fold composite of the contractions**, as a local section of
`H^i(SheafHom(K, K))` over an open set. -/
noncomputable def iteratedContractionClassOn (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r))
    (U : (Opens ↥X)ᵒᵖ) :
    ((endComplex Rc (cochain Rc K)).homology ((i + 1 : ℕ) : ℤ)).val.obj U :=
  (((endComplex Rc (cochain Rc K)).homologyπ ((i + 1 : ℕ) : ℤ)).val.app U)
    ((iteratedContractionCycle Rc K i f).val.app U (1 : (structureSheaf Rc).obj.obj U))

attribute [local instance] RingedSite.ringSheafSectionsCommRing

/-- Two cycles with the same image in the complex have the same homology class. -/
private theorem homologyπ_app_eq_of_iCycles_app_eq (n : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (x y : ((endComplex Rc (cochain Rc K)).cycles n).val.obj U)
    (h : ((endComplex Rc (cochain Rc K)).iCycles n).val.app U x =
      ((endComplex Rc (cochain Rc K)).iCycles n).val.app U y) :
    ((endComplex Rc (cochain Rc K)).homologyπ n).val.app U x =
      ((endComplex Rc (cochain Rc K)).homologyπ n).val.app U y :=
  congrArg _ (injective_app_of_mono _ U h)

/-- **The ordered product of the classes of `i` contractions is the class of their `i`-fold
composite.** Both sides peel their last factor, and a product of classes of cocycles is the class
of the cycle-level composite, so the induction compares two cycles with the same image inside the
complex; the inclusion of cycles is a monomorphism, hence injective on sections. -/
theorem homogeneousProd_contractionClassOn (i : ℕ) (f : Fin (i + 1) → ULift.{u} (Fin r))
    (U : Opens ↥X) :
    (homologyGradedAlgebra Rc (cochain Rc K)).toPresheafGradedAlgebra.homogeneousProd
        (op U) (i + 1) (fun k => contractionClassOn Rc K (f k) (op U)) =
      iteratedContractionClassOn Rc K i f (op U) := by
  induction i with
  | zero =>
      refine Eq.trans (homogeneousProd_succ_right
        (homologyGradedAlgebra Rc (cochain Rc K)).toPresheafGradedAlgebra (op U) 0
        (fun k => contractionClassOn Rc K (f k) (op U))) ?_
      refine Eq.trans (eq_of_heq
        ((homologyGradedAlgebra Rc (cochain Rc K)).toPresheafGradedAlgebra.one_mul 1 (op U)
          (contractionClassOn Rc K (f (Fin.last 0)) (op U)))) ?_
      exact homologyπ_app_eq_of_iCycles_app_eq Rc K _ (op U) _ _
        ((iCycles_contractionCycle Rc K (f (Fin.last 0)) (op U)).trans
          (iCycles_iteratedContractionCycle Rc K 0 f (op U)).symm)
  | succ i ih =>
      refine Eq.trans (homogeneousProd_succ_right
        (homologyGradedAlgebra Rc (cochain Rc K)).toPresheafGradedAlgebra (op U) (i + 1)
        (fun k => contractionClassOn Rc K (f k) (op U))) ?_
      refine Eq.trans (congrArg
        (fun y => ((homologyGradedAlgebra Rc (cochain Rc K)).mul ((i + 1 : ℕ) : ℤ) 1).app (op U) y
          (contractionClassOn Rc K (f (Fin.last (i + 1))) (op U)))
        (ih (fun k => f k.castSucc))) ?_
      refine Eq.trans (homologyMul_app_homologyπ Rc (cochain Rc K) (cochain Rc K)
        (cochain Rc K) ((i + 1 : ℕ) : ℤ) 1 U
        ((iteratedContractionCycle Rc K i (fun k => f k.castSucc)).val.app (op U)
          (1 : (structureSheaf Rc).obj.obj (op U)))
        ((contractionCycle Rc K (f (Fin.last (i + 1)))).val.app (op U)
          (1 : (structureSheaf Rc).obj.obj (op U)))) ?_
      refine homologyπ_app_eq_of_iCycles_app_eq Rc K ((i + 1 + 1 : ℕ) : ℤ) (op U) _ _ ?_
      refine Eq.trans (iCycles_cycleComposition_pureSection Rc (cochain Rc K) (cochain Rc K)
        (cochain Rc K) ((i + 1 : ℕ) : ℤ) 1 U
        ((iteratedContractionCycle Rc K i (fun k => f k.castSucc)).val.app (op U)
          (1 : (structureSheaf Rc).obj.obj (op U)))
        ((contractionCycle Rc K (f (Fin.last (i + 1)))).val.app (op U)
          (1 : (structureSheaf Rc).obj.obj (op U)))) ?_
      rw [iCycles_contractionCycle, iCycles_iteratedContractionCycle,
        iCycles_iteratedContractionCycle]
      rfl

end Stacks.RegularSequence.KoszulChainData

end
