module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.BoundaryCocycle
public import Mathlib.RingTheory.Derivation.Basic

/-!
# The boundary map of a square-zero extension of sheaves of rings is a derivation

Let `X` be a topological space, let `π : O' ⟶ O` be a surjection of sheaves of commutative
rings whose kernel `I` has square zero, and write `R = H⁰(X, O)` and `M = H¹(X, I)`.  Then `I`
is a sheaf of `O`-modules, so `M` is an `R`-module, and the boundary map `∂ : R → M` of the
short exact sequence `0 → I → O' → O → 0` is a derivation.

The `O`-action on `I` is the one the source describes: the map `O' → SheafHom(I, I)` kills `I`
because `I·I = 0`, so it factors through `O`.  Concretely, a section `a` of `O` over `V` acts on
a section `x` of `I` over `V` by multiplication by any local lift of `a` to `O'`; the result does
not depend on the lift, and the local answers glue because `I` is a sheaf.  The boundary map is
built as in Stacks 02AP: a global section `f` of `O` lifts to `O'` over the members of a covering
of `X`, the differences of the lifts form a Čech `1`-cocycle of `I`, and `∂(f)` is the class of
that cocycle, transported to `H¹(X, I)` by the comparison of Stacks 01EQ.  The cocycle used here
is the Čech coboundary of the lifts, `(i₀, i₁) ↦ f̃_{i₁} - f̃_{i₀}`, which is the negative of the
cocycle `(i₀, i₁) ↦ f̃_{i₀} - f̃_{i₁}` written in Stacks 02AP
(`Stacks.Cohomology.CechBoundary.deltaCochain_eq_neg_cechD`); so `∂` is `-δ` for the source's
`δ`.  Being a derivation is insensitive to this sign.  The Leibniz rule is then the cocycle
computation `f₀g₀ - f₁g₁ = (f₀ - f₁)g₀ + f₁(g₀ - g₁)` of the source, where the subscript `k` of
`f_k` labels the face omitting position `k`: `f₀` is the lift at `i₁` and `f₁` the lift at `i₀`.

## Main definitions

* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel` is the hypothesis of the lemma: a
  morphism of presheaves of commutative rings together with the realization of an abelian sheaf
  as its sectionwise kernel, the local surjectivity of the morphism, and the vanishing of the
  product of two sections of the kernel.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.smul` is the `O`-module structure on
  the kernel, and `…SquareZeroKernel.smulHom` is multiplication by a global section of `O`, as
  an endomorphism of the kernel.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.moduleCohomology` is the `R`-module
  structure on `M`.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.boundary` is the boundary map
  `∂ : R → M` in its Čech description, and `…SquareZeroKernel.boundaryDerivation` is it as a
  derivation.

## Main results

* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.incl_smul`: the defining equation of
  the `O`-action on the kernel, namely that over an open on which the acting section of `O`
  lifts to a section `b` of `O'`, the action is multiplication by `b`.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.smulCohomology_def`: the defining
  equation of the `R`-action on `M`.
* `Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement`: the comparison
  from first Čech cohomology of a covering to first sheaf cohomology is compatible with
  refinement of the covering.  Stacks 09V2 uses this inside its proof, where it carries no label
  of its own.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.boundary_eq`: the boundary map is
  computed by the Čech cocycle of differences of local lifts, on every covering of `X` carrying
  such lifts; this is what pins it.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.boundary_add` and
  `…SquareZeroKernel.boundary_leibniz`: additivity and the Leibniz rule.

## Implementation notes

The kernel is supplied as an abelian sheaf `I` together with a morphism `ι : I → O'` whose
sections over each open are exactly the sections killed by `π`, rather than as a categorical
kernel: that makes every statement below a statement about sections, and it is the shape in
which the source's hypothesis is used.  The same choice is made in
`Stacks.Sheaves.SquareZeroExtension.SquareZeroKernel` for Stacks 01UP.  Nothing about the
`O`-action, the `R`-action or the boundary map is assumed: each of the three is constructed, and
each is pinned by an equation (`incl_smul`, `smulCohomology_def`, `boundary_eq`).

The construction of the `O`-action and of the Čech boundary map works for presheaves `O'` and
`O` of commutative rings, since the sheaf condition is used just where sections of `I` are glued;
the surjectivity of `π` enters as local surjectivity for the topology of open covers, which is
exactly what exactness of `0 → I → O' → O → 0` at `O` gives.  The identification with the
connecting morphism of cohomology is made for sheaves `O'` and `O`, as in the source, where the
short exact sequence lives in abelian sheaves, in
`StacksFrontier.Topology.Sheaves.Cohomology.SquareZeroExtensionConnecting`.  Rings are
commutative, as everywhere in the Stacks Project.

The boundary map is taken in its Čech description, which is how Stacks 02AP defines it: the
class of the cocycle of differences of local lifts, with the opposite sign
`(i₀, i₁) ↦ f̃_{i₁} - f̃_{i₀}` (the Čech coboundary of the lifts), so that `boundary` is the
negative of the `δ` of Stacks 02AP.  That class is identified with the connecting
morphism of the long exact sequence of the right derived functors of `Γ(X, -)` by
`Stacks.Cohomology.CechOne.rightDerivedPlusδ_toRightDerivedZero`, which gives
`Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.boundary_eq_connecting`; the sign
conventions match, the cocycle there being the Čech coboundary of the lifts as well.  So the
derivation of Stacks 0B8S is the connecting morphism itself.

## References

* [Stacks Project, Tag 0B8S](https://stacks.math.columbia.edu/tag/0B8S)
* [Stacks Project, Tag 02AP](https://stacks.math.columbia.edu/tag/02AP)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 00RN](https://stacks.math.columbia.edu/tag/00RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CechCochains
open Stacks.Cohomology.CechOne Stacks.Cohomology.CechBoundary
open Stacks.Cohomology.LerayLowDegree (abelianSheafEnoughInjectives)

universe u v w w'

namespace Stacks.Cohomology.SquareZeroBoundary

variable {X : TopCat.{u}}

/-- The presheaf of abelian groups underlying a presheaf of commutative rings. -/
abbrev addPresheaf (F : TopCat.Presheaf CommRingCat.{max u v} X) :
    TopCat.Presheaf AddCommGrpCat.{max u v} X :=
  F ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The morphism of presheaves of abelian groups underlying a morphism of presheaves of
commutative rings. -/
abbrev addMap {F G : TopCat.Presheaf CommRingCat.{max u v} X} (π : F ⟶ G) :
    addPresheaf F ⟶ addPresheaf G :=
  Functor.whiskerRight π _

/-- A section of the presheaf of abelian groups underlying a presheaf of commutative rings, read
as a section of the latter.  The two types are the same; this names the ring one so that
multiplication elaborates. -/
def asRing {F : TopCat.Presheaf CommRingCat.{max u v} X} {V : Opens X}
    (y : ToType ((addPresheaf F).obj (op V))) : ToType (F.obj (op V)) := y

/-- Restriction of a section of a presheaf of commutative rings, as a ring homomorphism. -/
abbrev rres {F : TopCat.Presheaf CommRingCat.{max u v} X} {V₁ V₂ : Opens X} (h : V₂ ≤ V₁) :
    ToType (F.obj (op V₁)) →+* ToType (F.obj (op V₂)) :=
  (F.map (homOfLE h).op).hom

/-- Restriction to a smaller open is the composite of two restrictions. -/
theorem rres_rres {F : TopCat.Presheaf CommRingCat.{max u v} X} {V₁ V₂ V₃ : Opens X}
    (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (a : ToType (F.obj (op V₁))) :
    rres h₂ (rres h₁ a) = rres (h₂.trans h₁) a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Restriction along the identity is the identity. -/
theorem rres_self {F : TopCat.Presheaf CommRingCat.{max u v} X} {V₁ : Opens X} (h : V₁ ≤ V₁)
    (a : ToType (F.obj (op V₁))) : rres h a = a := by
  change ConcreteCategory.hom (F.map (homOfLE h).op) a = a
  rw [Subsingleton.elim (homOfLE h) (𝟙 V₁), op_id, F.map_id]
  rfl

/-- Restriction of a section of an abelian presheaf along the identity is the identity. -/
theorem restr_self (F : TopCat.Presheaf AddCommGrpCat.{max u v} X) {V₁ : Opens X} (h : V₁ ≤ V₁)
    (x : ToType (F.obj (op V₁))) : restr F h x = x := by
  change ConcreteCategory.hom (F.map (homOfLE h).op) x = x
  rw [Subsingleton.elim (homOfLE h) (𝟙 V₁), op_id, F.map_id]
  rfl

/-- Restriction in the underlying presheaf of abelian groups is restriction of rings. -/
theorem asRing_restr {F : TopCat.Presheaf CommRingCat.{max u v} X} {V₁ V₂ : Opens X}
    (h : V₂ ≤ V₁) (x : ToType (F.obj (op V₁))) :
    asRing (restr (addPresheaf F) h x) = rres h x := rfl

/-- Restriction of a product of sections is the product of the restrictions. -/
theorem rres_mul {F : TopCat.Presheaf CommRingCat.{max u v} X} {V₁ V₂ : Opens X} (h : V₂ ≤ V₁)
    (x y : ToType (F.obj (op V₁))) : rres h (x * y) = rres h x * rres h y :=
  map_mul (rres h) x y

/-- The Čech differential of a `0`-cochain, read on a pair of indices. -/
theorem cechD_zero_apply {Λ : Type w} (W : Λ → Opens X)
    (F : TopCat.Presheaf AddCommGrpCat.{max u v} X) (t : Cochain W F 0) (j : Fin 2 → Λ) :
    cechD W F 0 t j =
      restr F (inter_le_omit W j 0) (t (j ∘ (0 : Fin 2).succAbove)) -
        restr F (inter_le_omit W j 1) (t (j ∘ (1 : Fin 2).succAbove)) := by
  rw [cechD_apply, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, sub_eq_add_neg]

/-- **A `0`-cochain whose components agree on overlaps is a cocycle.** -/
theorem cechD_eq_zero_of_restr_eq {Λ : Type w} (W : Λ → Opens X)
    (F : TopCat.Presheaf AddCommGrpCat.{max u v} X) (c : Cochain W F 0)
    (hc : ∀ (j k : Fin 1 → Λ) {T : Opens X} (hj : T ≤ inter W j) (hk : T ≤ inter W k),
      restr F hj (c j) = restr F hk (c k)) :
    cechD W F 0 c = 0 := by
  funext j
  rw [Cochain.zero_apply, cechD_zero_apply,
    hc (j ∘ (0 : Fin 2).succAbove) (j ∘ (1 : Fin 2).succAbove) (inter_le_omit W j 0)
      (inter_le_omit W j 1), sub_self]

/-- The realization of an abelian sheaf `I` as the square-zero kernel of a surjection
`π : O' ⟶ O` of presheaves of commutative rings.  The fields say that `ι` identifies the
sections of `I` over an open with the sections of `O'` killed by `π`, that `π` is surjective
locally on `X`, and that the product of two sections of `I` vanishes. -/
structure SquareZeroKernel (O' O : TopCat.Presheaf CommRingCat.{max u v} X)
    (I : TopCat.Sheaf AddCommGrpCat.{max u v} X) where
  /-- The surjection of presheaves of commutative rings. -/
  π : O' ⟶ O
  /-- The inclusion of the kernel. -/
  ι : I.presheaf ⟶ addPresheaf O'
  /-- The inclusion is injective on sections. -/
  ι_injective : ∀ V : Opens X, Function.Injective (ι.app (op V))
  /-- Sections of the kernel are killed by `π`. -/
  π_ι : ∀ (V : Opens X) (x : ToType (I.presheaf.obj (op V))),
    π.app (op V) (asRing (ι.app (op V) x)) = 0
  /-- Sections of `O'` killed by `π` come from the kernel. -/
  exists_of_π_eq_zero : ∀ (V : Opens X) (b : ToType (O'.obj (op V))),
    π.app (op V) b = 0 → ∃ x, asRing (ι.app (op V) x) = b
  /-- `π` is surjective locally on `X`. -/
  π_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (addMap π)
  /-- The kernel has square zero. -/
  ι_mul_ι : ∀ (V : Opens X) (x y : ToType (I.presheaf.obj (op V))),
    asRing (ι.app (op V) x) * asRing (ι.app (op V) y) = 0

namespace SquareZeroKernel

variable {O' O : TopCat.Presheaf CommRingCat.{max u v} X}
  {I : TopCat.Sheaf AddCommGrpCat.{max u v} X} (E : SquareZeroKernel O' O I)

/-- A section of the kernel, read as a section of `O'`, as an additive homomorphism. -/
def inclHom (V : Opens X) :
    ToType (I.presheaf.obj (op V)) →+ ToType (O'.obj (op V)) := (E.ι.app (op V)).hom

/-- A section of the kernel, read as a section of `O'`. -/
def incl (V : Opens X) (x : ToType (I.presheaf.obj (op V))) : ToType (O'.obj (op V)) :=
  E.inclHom V x

/-- The inclusion of the kernel sends `0` to `0`. -/
@[simp] theorem incl_zero (V : Opens X) : E.incl V 0 = 0 := map_zero (E.inclHom V)

/-- The inclusion of the kernel is additive. -/
theorem incl_add (V : Opens X) (x y : ToType (I.presheaf.obj (op V))) :
    E.incl V (x + y) = E.incl V x + E.incl V y := map_add (E.inclHom V) x y

/-- The inclusion of the kernel respects differences. -/
theorem incl_sub (V : Opens X) (x y : ToType (I.presheaf.obj (op V))) :
    E.incl V (x - y) = E.incl V x - E.incl V y := map_sub (E.inclHom V) x y

/-- The inclusion of the kernel is injective on sections. -/
theorem incl_injective (V : Opens X) : Function.Injective (E.incl V) := E.ι_injective V

/-- Sections of the kernel are killed by `π`. -/
theorem π_incl (V : Opens X) (x : ToType (I.presheaf.obj (op V))) :
    E.π.app (op V) (E.incl V x) = 0 := E.π_ι V x

/-- `π` sends `0` to `0`. -/
theorem π_zero (V : Opens X) : E.π.app (op V) (0 : ToType (O'.obj (op V))) = 0 :=
  map_zero (E.π.app (op V)).hom

/-- `π` sends `1` to `1`. -/
theorem π_one (V : Opens X) : E.π.app (op V) (1 : ToType (O'.obj (op V))) = 1 :=
  map_one (E.π.app (op V)).hom

/-- The product of two sections of the kernel vanishes. -/
theorem incl_mul_incl (V : Opens X) (x y : ToType (I.presheaf.obj (op V))) :
    E.incl V x * E.incl V y = 0 := E.ι_mul_ι V x y

/-- The inclusion of the kernel commutes with restriction. -/
theorem incl_restr {V₁ V₂ : Opens X} (h : V₂ ≤ V₁) (x : ToType (I.presheaf.obj (op V₁))) :
    E.incl V₂ (restr I.presheaf h x) = rres h (E.incl V₁ x) :=
  (restr_app (P := I.presheaf) (Q := addPresheaf O') E.ι h x).symm

/-- Restriction of the inclusion of a restricted section. -/
theorem rres_incl_restr {V₁ V₂ V₃ : Opens X} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂)
    (x : ToType (I.presheaf.obj (op V₁))) :
    rres h₂ (E.incl V₂ (restr I.presheaf h₁ x)) =
      E.incl V₃ (restr I.presheaf (h₂.trans h₁) x) := by
  rw [← E.incl_restr h₂, restr_restr]

/-- `π` commutes with restriction. -/
theorem π_rres {V₁ V₂ : Opens X} (h : V₂ ≤ V₁) (b : ToType (O'.obj (op V₁))) :
    E.π.app (op V₂) (rres h b) = rres h (E.π.app (op V₁) b) := by
  have h₁ := ConcreteCategory.congr_hom (E.π.naturality (homOfLE h).op) b
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₁
  exact h₁

/-- Every section of `O'` killed by `π` comes from a unique section of the kernel. -/
theorem existsUnique_of_π_eq_zero (V : Opens X) (b : ToType (O'.obj (op V)))
    (hb : E.π.app (op V) b = 0) : ∃! x, E.incl V x = b := by
  obtain ⟨x, hx⟩ := E.exists_of_π_eq_zero V b hb
  exact ⟨x, hx, fun y hy => E.incl_injective V (hy.trans hx.symm)⟩

/-- The unique section of the kernel over `V` whose inclusion is a given section of `O'` killed
by `π`. -/
noncomputable def pre (V : Opens X) (b : ToType (O'.obj (op V)))
    (hb : E.π.app (op V) b = 0) : ToType (I.presheaf.obj (op V)) :=
  Classical.choose (E.existsUnique_of_π_eq_zero V b hb)

/-- The inclusion of `E.pre V b hb` is `b`. -/
@[simp] theorem incl_pre (V : Opens X) (b : ToType (O'.obj (op V)))
    (hb : E.π.app (op V) b = 0) : E.incl V (E.pre V b hb) = b :=
  (Classical.choose_spec (E.existsUnique_of_π_eq_zero V b hb)).1

/-- A section of the kernel is determined by its inclusion. -/
theorem eq_pre {V : Opens X} {b : ToType (O'.obj (op V))} (hb : E.π.app (op V) b = 0)
    {x : ToType (I.presheaf.obj (op V))} (hx : E.incl V x = b) : x = E.pre V b hb :=
  E.incl_injective V (hx.trans (E.incl_pre V b hb).symm)

/-- **Two lifts of the same section of `O` act in the same way.**  Their difference lies in the
kernel, and the kernel annihilates the kernel. -/
theorem mul_incl_congr (V : Opens X) (b b' : ToType (O'.obj (op V)))
    (hbb' : E.π.app (op V) b = E.π.app (op V) b') (x : ToType (I.presheaf.obj (op V))) :
    b * E.incl V x = b' * E.incl V x := by
  obtain ⟨z, hz⟩ := E.exists_of_π_eq_zero V (b - b') (by rw [map_sub, hbb', sub_self])
  have hz' : E.incl V z = b - b' := hz
  have h0 : (b - b') * E.incl V x = 0 := by rw [← hz']; exact E.incl_mul_incl V z x
  rw [sub_mul, sub_eq_zero] at h0
  exact h0

/-! ### The `O`-module structure on the square-zero kernel -/

/-- `E.IsAction V a x y` says that `y` is the section of the kernel obtained by letting
`a ∈ O(V)` act on `x ∈ I(V)`: over every open `Z ≤ V` on which `a` lifts to a section `b` of
`O'`, the inclusion of `y` restricts to `b` times the inclusion of `x`. -/
def IsAction (V : Opens X) (a : ToType (O.obj (op V)))
    (x y : ToType (I.presheaf.obj (op V))) : Prop :=
  ∀ (Z : Opens X) (hZ : Z ≤ V) (b : ToType (O'.obj (op Z))),
    E.π.app (op Z) b = rres hZ a →
      E.incl Z (restr I.presheaf hZ y) = b * E.incl Z (restr I.presheaf hZ x)

/-- The section of the kernel over `Z ≤ V` whose inclusion is `b` times the restriction of the
inclusion of `x`.  For `b` a lift of a section of `O`, this is the local action on `x`. -/
noncomputable def mulRestr {V : Opens X} (x : ToType (I.presheaf.obj (op V))) {Z : Opens X}
    (hZ : Z ≤ V) (b : ToType (O'.obj (op Z))) : ToType (I.presheaf.obj (op Z)) :=
  E.pre Z (b * E.incl Z (restr I.presheaf hZ x)) (by rw [map_mul, E.π_incl, mul_zero])

/-- The inclusion of `E.mulRestr x hZ b` is `b` times the restriction of the inclusion of `x`.
-/
@[simp] theorem incl_mulRestr {V : Opens X} (x : ToType (I.presheaf.obj (op V)))
    {Z : Opens X} (hZ : Z ≤ V) (b : ToType (O'.obj (op Z))) :
    E.incl Z (E.mulRestr x hZ b) = b * E.incl Z (restr I.presheaf hZ x) :=
  E.incl_pre _ _ _

/-- Two lifts of the same section of `O` produce the same section of the kernel. -/
theorem mulRestr_congr {V : Opens X} (a : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) {Z : Opens X} (hZ : Z ≤ V)
    {b b' : ToType (O'.obj (op Z))} (hb : E.π.app (op Z) b = rres hZ a)
    (hb' : E.π.app (op Z) b' = rres hZ a) :
    E.mulRestr x hZ b = E.mulRestr x hZ b' :=
  E.incl_injective Z (by
    rw [incl_mulRestr, incl_mulRestr]
    exact E.mul_incl_congr Z b b' (hb.trans hb'.symm) _)

/-- The local action commutes with restriction. -/
theorem restr_mulRestr {V : Opens X} (x : ToType (I.presheaf.obj (op V))) {Z T : Opens X}
    (hZ : Z ≤ V) (hT : T ≤ Z) (b : ToType (O'.obj (op Z))) :
    restr I.presheaf hT (E.mulRestr x hZ b) = E.mulRestr x (hT.trans hZ) (rres hT b) :=
  E.incl_injective T (by
    rw [E.incl_restr hT, incl_mulRestr, incl_mulRestr, map_mul, E.rres_incl_restr hZ hT])

/-- The action, read as an equality with the local action produced by any lift. -/
theorem IsAction.eq_mulRestr {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} (h : E.IsAction V a x y) {Z : Opens X} (hZ : Z ≤ V)
    {b : ToType (O'.obj (op Z))} (hb : E.π.app (op Z) b = rres hZ a) :
    restr I.presheaf hZ y = E.mulRestr x hZ b :=
  E.incl_injective Z (by rw [h Z hZ b hb, incl_mulRestr])

/-- A section of `O` that lifts over all of `V` acts by multiplication by any of its lifts. -/
theorem isAction_of_incl_eq_mul {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} (b : ToType (O'.obj (op V)))
    (hb : E.π.app (op V) b = a) (hy : E.incl V y = b * E.incl V x) : E.IsAction V a x y := by
  intro Z hZ b' hb'
  have h₁ : E.incl Z (restr I.presheaf hZ y) =
      rres hZ b * E.incl Z (restr I.presheaf hZ x) := by
    rw [E.incl_restr hZ y, hy, map_mul, E.incl_restr hZ x]
  rw [h₁]
  refine E.mul_incl_congr Z (rres hZ b) b' ?_ _
  rw [E.π_rres hZ b, hb, hb']

/-- The action is compatible with restriction. -/
theorem IsAction.restrict {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} (h : E.IsAction V a x y) {Z : Opens X} (hZ : Z ≤ V) :
    E.IsAction Z (rres hZ a) (restr I.presheaf hZ x) (restr I.presheaf hZ y) := by
  intro T hT b hb
  rw [restr_restr, restr_restr]
  refine h T (hT.trans hZ) b ?_
  rw [hb, rres_rres]

/-- A section of the kernel that restricts to the local action over an open `Z` on which the
acting section lifts, acts correctly over `Z`. -/
theorem isAction_restr_of_eq_mulRestr {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} {Z : Opens X} (hZ : Z ≤ V)
    {b : ToType (O'.obj (op Z))} (hb : E.π.app (op Z) b = rres hZ a)
    (hy : restr I.presheaf hZ y = E.mulRestr x hZ b) :
    E.IsAction Z (rres hZ a) (restr I.presheaf hZ x) (restr I.presheaf hZ y) :=
  E.isAction_of_incl_eq_mul b hb (by rw [hy, incl_mulRestr])

/-- **The action is local.**  A section of the kernel that acts correctly over each member of a
covering of `V` acts correctly over `V`. -/
theorem isAction_of_cover {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} {Λ : Type w} (W : Λ → Opens X)
    (hW : ∀ j, W j ≤ V) (hcover : V = ⨆ j, W j)
    (h : ∀ j, E.IsAction (W j) (rres (hW j) a) (restr I.presheaf (hW j) x)
      (restr I.presheaf (hW j) y)) :
    E.IsAction V a x y := by
  intro Z hZ b hb
  have hZcover : Z = ⨆ j, Z ⊓ W j := by
    refine le_antisymm (fun z hz => ?_) (iSup_le fun j => inf_le_left)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcover.le (hZ hz))
    exact Opens.mem_iSup.mpr ⟨j, hz, hj⟩
  have hkey : restr I.presheaf hZ y = E.mulRestr x hZ b := by
    refine eq_of_restr_eq (fun j => Z ⊓ W j) Z hZcover I _ _ fun j => ?_
    have hle : inter (fun j => Z ⊓ W j) j ≤ Z ⊓ W (j 0) := inter_le _ j 0
    have hleW : inter (fun j => Z ⊓ W j) j ≤ W (j 0) := hle.trans inf_le_right
    have hleZ : inter (fun j => Z ⊓ W j) j ≤ Z := hle.trans inf_le_left
    have hπ : E.π.app (op (inter (fun j => Z ⊓ W j) j)) (rres hleZ b) =
        rres hleW (rres (hW (j 0)) a) := by
      rw [E.π_rres hleZ b, hb, rres_rres, rres_rres]
    have h₂ := h (j 0) _ hleW (rres hleZ b) hπ
    rw [restr_restr, restr_restr] at h₂
    change restr I.presheaf hleZ (restr I.presheaf hZ y) =
      restr I.presheaf hleZ (E.mulRestr x hZ b)
    refine E.incl_injective _ ?_
    rw [restr_restr, E.restr_mulRestr x hZ hleZ b, incl_mulRestr]
    exact h₂
  rw [hkey, incl_mulRestr]

/-- **The action is local**, in the form that produces it from a family of lifts. -/
theorem isAction_of_restr_eq_mulRestr {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} {Λ : Type w} (W : Λ → Opens X)
    (hW : ∀ j, W j ≤ V) (hcover : V = ⨆ j, W j)
    (b : ∀ j, ToType (O'.obj (op (W j))))
    (hb : ∀ j, E.π.app (op (W j)) (b j) = rres (hW j) a)
    (hy : ∀ j, restr I.presheaf (hW j) y = E.mulRestr x (hW j) (b j)) :
    E.IsAction V a x y :=
  E.isAction_of_cover W hW hcover fun j =>
    E.isAction_restr_of_eq_mulRestr (hW j) (hb j) (hy j)

/-- The opens contained in `V` on which a given section of `O` lifts to `O'`, indexed by the
lifts themselves. -/
def LiftCover (V : Opens X) (a : ToType (O.obj (op V))) : Type (max u v) :=
  Σ Z : {Z : Opens X // Z ≤ V},
    {b : ToType (O'.obj (op Z.1)) // E.π.app (op Z.1) b = rres Z.2 a}

/-- The open attached to a member of `E.LiftCover V a`. -/
def LiftCover.cov {V : Opens X} {a : ToType (O.obj (op V))} (j : E.LiftCover V a) :
    Opens X := j.1.1

/-- The open attached to a member of the covering is contained in the ambient one. -/
theorem LiftCover.cov_le {V : Opens X} {a : ToType (O.obj (op V))} (j : E.LiftCover V a) :
    j.cov ≤ V := j.1.2

/-- The lift attached to a member of `E.LiftCover V a`. -/
def LiftCover.lift {V : Opens X} {a : ToType (O.obj (op V))} (j : E.LiftCover V a) :
    ToType (O'.obj (op j.cov)) := j.2.1

/-- The lift attached to a member of the covering lifts the given section of `O`. -/
theorem LiftCover.π_lift {V : Opens X} {a : ToType (O.obj (op V))} (j : E.LiftCover V a) :
    E.π.app (op j.cov) j.lift = rres j.cov_le a := j.2.2

/-- Restricting a lift of `a` along `h` gives a lift of the restriction of `a`. -/
private theorem π_rres_lift {V : Opens X} {a : ToType (O.obj (op V))} (j : E.LiftCover V a)
    {Z : Opens X} (h : Z ≤ j.cov) :
    E.π.app (op Z) (rres h j.lift) = rres (h.trans j.cov_le) a := by
  rw [E.π_rres, LiftCover.π_lift, rres_rres]

/-- The opens on which a section of `O` lifts cover `V`, `π` being surjective locally on `X`. -/
theorem liftCover_iSup (V : Opens X) (a : ToType (O.obj (op V))) :
    V = ⨆ j : E.LiftCover V a, j.cov := by
  have := E.π_locallySurjective
  refine le_antisymm (fun p hp => ?_) (iSup_le fun j => j.cov_le)
  obtain ⟨Z, f, ⟨b, hb⟩, hpZ⟩ :=
    CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X) (addMap E.π)
      (U := op V) a p hp
  have hb' : E.π.app (op Z) b = rres (leOfHom f) a := by
    refine hb.trans ?_
    rw [Subsingleton.elim f (homOfLE (leOfHom f))]
    rfl
  exact Opens.mem_iSup.mpr ⟨⟨⟨Z, leOfHom f⟩, ⟨b, hb'⟩⟩, hpZ⟩

/-- **Existence and uniqueness of the `O`-action on the square-zero kernel.** -/
theorem existsUnique_isAction (V : Opens X) (a : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) : ∃! y, E.IsAction V a x y := by
  classical
  have hcover : V = ⨆ j : E.LiftCover V a, j.cov := E.liftCover_iSup V a
  have hle : ∀ j : Fin 1 → E.LiftCover V a,
      inter (fun j : E.LiftCover V a => j.cov) j ≤ (j 0).cov :=
    fun j => inter_le _ j 0
  have hπ : ∀ j : Fin 1 → E.LiftCover V a,
      E.π.app (op (inter (fun j : E.LiftCover V a => j.cov) j)) (rres (hle j) (j 0).lift) =
        rres (inter_le_of_eq_iSup hcover j) a := by
    exact fun j => E.π_rres_lift (j 0) (hle j)
  have hcompat : ∀ (j k : Fin 1 → E.LiftCover V a) {T : Opens X}
      (hj : T ≤ inter (fun j : E.LiftCover V a => j.cov) j)
      (hk : T ≤ inter (fun j : E.LiftCover V a => j.cov) k),
      restr I.presheaf hj (E.mulRestr x (inter_le_of_eq_iSup hcover j)
          (rres (hle j) (j 0).lift)) =
        restr I.presheaf hk (E.mulRestr x (inter_le_of_eq_iSup hcover k)
          (rres (hle k) (k 0).lift)) := by
    intro j k T hj hk
    rw [E.restr_mulRestr x _ hj, E.restr_mulRestr x _ hk]
    refine E.mulRestr_congr a x _ ?_ ?_
    · rw [E.π_rres hj, hπ j, rres_rres]
    · rw [E.π_rres hk, hπ k, rres_rres]
  have hcd : cechD (fun j : E.LiftCover V a => j.cov) I.presheaf 0
      (fun j => E.mulRestr x (inter_le_of_eq_iSup hcover j)
        (rres (hle j) (j 0).lift)) = 0 :=
    cechD_eq_zero_of_restr_eq _ _ _ hcompat
  obtain ⟨y, hy, -⟩ :=
    existsUnique_glue (fun j : E.LiftCover V a => j.cov) V hcover I _ hcd
  have hcover' : V = ⨆ j : Fin 1 → E.LiftCover V a,
      inter (fun j : E.LiftCover V a => j.cov) j :=
    le_antisymm (le_iSup_inter hcover) (iSup_le fun j => inter_le_of_eq_iSup hcover j)
  refine ⟨y, E.isAction_of_restr_eq_mulRestr _ (fun j => inter_le_of_eq_iSup hcover j) hcover'
    (fun j => rres (hle j) (j 0).lift) hπ hy, ?_⟩
  intro y' hy'
  refine eq_of_restr_eq (fun j : E.LiftCover V a => j.cov) V hcover I y' y fun j => ?_
  rw [IsAction.eq_mulRestr E hy' (inter_le_of_eq_iSup hcover j) (hπ j), hy j]

/-- **The `O`-module structure on the square-zero kernel.**  A section `a` of `O` over `V` acts
on a section of the kernel over `V` by multiplication by any local lift of `a` to `O'`; the
result is independent of the lift because the kernel has square zero. -/
noncomputable def smul (V : Opens X) (a : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) : ToType (I.presheaf.obj (op V)) :=
  Classical.choose (E.existsUnique_isAction V a x)

/-- The action is an action: it satisfies the defining property. -/
theorem isAction_smul (V : Opens X) (a : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) : E.IsAction V a x (E.smul V a x) :=
  (Classical.choose_spec (E.existsUnique_isAction V a x)).1

/-- Anything satisfying the defining property of the action is the action. -/
theorem eq_smul {V : Opens X} {a : ToType (O.obj (op V))}
    {x y : ToType (I.presheaf.obj (op V))} (h : E.IsAction V a x y) : y = E.smul V a x :=
  (Classical.choose_spec (E.existsUnique_isAction V a x)).2 y h

/-- **The defining equation of the `O`-action on the square-zero kernel.**  Over an open `Z ≤ V`
on which `a` lifts to `b ∈ O'(Z)`, the action of `a` on `x` is multiplication by `b`. -/
theorem incl_smul {V : Opens X} (a : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) (Z : Opens X) (hZ : Z ≤ V)
    (b : ToType (O'.obj (op Z))) (hb : E.π.app (op Z) b = rres hZ a) :
    E.incl Z (restr I.presheaf hZ (E.smul V a x)) = b * E.incl Z (restr I.presheaf hZ x) :=
  E.isAction_smul V a x Z hZ b hb

/-- The action of a section of `O` that lifts over the whole open is multiplication by the
lift. -/
theorem incl_smul_of_lift {V : Opens X} {a : ToType (O.obj (op V))}
    (x : ToType (I.presheaf.obj (op V))) (b : ToType (O'.obj (op V)))
    (hb : E.π.app (op V) b = a) : E.incl V (E.smul V a x) = b * E.incl V x := by
  have h := E.incl_smul a x V le_rfl b (by rw [rres_self]; exact hb)
  rwa [restr_self, restr_self] at h

/-! ### The algebra laws of the action -/

/-- A section of `O` acts on the zero section of the kernel by zero. -/
theorem smul_zero (V : Opens X) (a : ToType (O.obj (op V))) : E.smul V a 0 = 0 :=
  (E.eq_smul (fun Z hZ b _ => by
    rw [map_zero (restr I.presheaf hZ), E.incl_zero, mul_zero])).symm

/-- The action of a section of `O` is additive in the section of the kernel. -/
theorem smul_add (V : Opens X) (a : ToType (O.obj (op V)))
    (x y : ToType (I.presheaf.obj (op V))) :
    E.smul V a (x + y) = E.smul V a x + E.smul V a y :=
  (E.eq_smul (fun Z hZ b hb => by
    rw [map_add (restr I.presheaf hZ), E.incl_add, E.incl_smul a x Z hZ b hb,
      E.incl_smul a y Z hZ b hb, map_add (restr I.presheaf hZ), E.incl_add, mul_add])).symm

/-- The zero section of `O` acts by zero. -/
theorem zero_smul (V : Opens X) (x : ToType (I.presheaf.obj (op V))) : E.smul V 0 x = 0 :=
  (E.eq_smul (E.isAction_of_incl_eq_mul 0 (E.π_zero V)
    (by rw [E.incl_zero, zero_mul]))).symm

/-- The unit section of `O` acts as the identity. -/
theorem one_smul (V : Opens X) (x : ToType (I.presheaf.obj (op V))) : E.smul V 1 x = x :=
  (E.eq_smul (E.isAction_of_incl_eq_mul 1 (E.π_one V) (one_mul _).symm)).symm

/-- The action commutes with restriction, so the kernel is a sheaf of `O`-modules. -/
theorem restr_smul {V Z : Opens X} (hZ : Z ≤ V) (a : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) :
    restr I.presheaf hZ (E.smul V a x) = E.smul Z (rres hZ a) (restr I.presheaf hZ x) :=
  E.eq_smul (IsAction.restrict E (E.isAction_smul V a x) hZ)

/-- A covering of `V` by opens over which two given sections of `O` both lift. -/
theorem iSup_liftCover_inf (V : Opens X) (a a' : ToType (O.obj (op V))) :
    V = ⨆ p : E.LiftCover V a × E.LiftCover V a', p.1.cov ⊓ p.2.cov :=
  eq_iSup_inf_of_eq_iSup (fun j : E.LiftCover V a => j.cov) (E.liftCover_iSup V a)
    (E.liftCover_iSup V a')

/-- A section of the kernel acts correctly over `V` if it does so over every open on which
both `a` and `a'` lift. -/
private theorem isAction_of_liftCover_inf {V : Opens X} (a a' : ToType (O.obj (op V)))
    {c : ToType (O.obj (op V))} {x y : ToType (I.presheaf.obj (op V))}
    (h : ∀ p : E.LiftCover V a × E.LiftCover V a',
      E.IsAction (p.1.cov ⊓ p.2.cov) (rres (inf_le_left.trans p.1.cov_le) c)
        (restr I.presheaf (inf_le_left.trans p.1.cov_le) x)
        (restr I.presheaf (inf_le_left.trans p.1.cov_le) y)) :
    E.IsAction V c x y :=
  E.isAction_of_cover _ (fun p => inf_le_left.trans p.1.cov_le) (E.iSup_liftCover_inf V a a') h

/-- The action is additive in the acting section of `O`. -/
theorem add_smul (V : Opens X) (a a' : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) :
    E.smul V (a + a') x = E.smul V a x + E.smul V a' x := by
  refine (E.eq_smul (E.isAction_of_liftCover_inf a a' fun p => ?_)).symm
  have hb₁ := E.π_rres_lift p.1 (inf_le_left : p.1.cov ⊓ p.2.cov ≤ _)
  have hb₂ := E.π_rres_lift p.2 (inf_le_right : p.1.cov ⊓ p.2.cov ≤ _)
  refine E.isAction_of_incl_eq_mul (rres inf_le_left p.1.lift + rres inf_le_right p.2.lift)
    (by rw [map_add, hb₁, hb₂, map_add]) ?_
  rw [map_add (restr I.presheaf (inf_le_left.trans p.1.cov_le)), E.incl_add,
    E.incl_smul a x _ (inf_le_left.trans p.1.cov_le) _ hb₁,
    E.incl_smul a' x _ (inf_le_left.trans p.1.cov_le) _ hb₂, add_mul]

/-- The action of a product of sections of `O` is the composite of the two actions. -/
theorem mul_smul (V : Opens X) (a a' : ToType (O.obj (op V)))
    (x : ToType (I.presheaf.obj (op V))) :
    E.smul V (a * a') x = E.smul V a (E.smul V a' x) := by
  refine (E.eq_smul (E.isAction_of_liftCover_inf a a' fun p => ?_)).symm
  have hb₁ := E.π_rres_lift p.1 (inf_le_left : p.1.cov ⊓ p.2.cov ≤ _)
  have hb₂ := E.π_rres_lift p.2 (inf_le_right : p.1.cov ⊓ p.2.cov ≤ _)
  refine E.isAction_of_incl_eq_mul (rres inf_le_left p.1.lift * rres inf_le_right p.2.lift)
    (by rw [map_mul, hb₁, hb₂, map_mul]) ?_
  rw [E.incl_smul a (E.smul V a' x) _ (inf_le_left.trans p.1.cov_le) _ hb₁,
    E.incl_smul a' x _ (inf_le_left.trans p.1.cov_le) _ hb₂, mul_assoc]

/-! ### Multiplication by a global section of `O`, as an endomorphism of the kernel -/

/-- Multiplication by a global section `r` of `O`, as an endomorphism of the kernel. -/
noncomputable def smulHom (r : ToType (O.obj (op (⊤ : Opens X)))) : I ⟶ I :=
  ObjectProperty.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun x => E.smul V.unop (rres (le_top : V.unop ≤ ⊤) r) x
          map_zero' := E.smul_zero _ _
          map_add' := fun x y => E.smul_add _ _ x y }
      naturality := by
        intro V W g
        ext x
        change E.smul W.unop (rres le_top r) (restr I.presheaf (leOfHom g.unop) x) =
          restr I.presheaf (leOfHom g.unop) (E.smul V.unop (rres le_top r) x)
        rw [E.restr_smul (leOfHom g.unop), rres_rres] }

/-- Multiplication by a global section of `O`, read on sections over an open. -/
theorem smulHom_apply (r : ToType (O.obj (op (⊤ : Opens X)))) (V : Opens X)
    (x : ToType (I.presheaf.obj (op V))) :
    (E.smulHom r).hom.app (op V) x = E.smul V (rres le_top r) x := rfl

/-- Multiplication by the unit global section is the identity. -/
theorem smulHom_one : E.smulHom 1 = 𝟙 I := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  ext x
  rw [smulHom_apply]
  change E.smul V.unop (rres le_top 1) x = x
  rw [map_one, E.one_smul]

/-- Multiplication by a product of global sections is the composite. -/
theorem smulHom_mul (r r' : ToType (O.obj (op (⊤ : Opens X)))) :
    E.smulHom (r * r') = E.smulHom r' ≫ E.smulHom r := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  ext x
  change E.smul V.unop (rres le_top (r * r')) x =
    E.smul V.unop (rres le_top r) (E.smul V.unop (rres le_top r') x)
  rw [map_mul, E.mul_smul]

/-- Multiplication by a sum of global sections is the sum of the two multiplications. -/
theorem smulHom_add (r r' : ToType (O.obj (op (⊤ : Opens X)))) :
    E.smulHom (r + r') = E.smulHom r + E.smulHom r' := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  ext x
  change E.smul V.unop (rres le_top (r + r')) x =
    E.smul V.unop (rres le_top r) x + E.smul V.unop (rres le_top r') x
  rw [map_add, E.add_smul]

/-- Multiplication by the zero global section is zero. -/
theorem smulHom_zero : E.smulHom 0 = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  ext x
  change E.smul V.unop (rres le_top 0) x = 0
  rw [map_zero, E.zero_smul]

end SquareZeroKernel



/-! ### First cohomology, and the Čech comparison under refinement -/

section Cohomology

variable {X : TopCat.{u}} [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]

/-- Abelian sheaves on a space have enough injectives. -/
local instance topCatSheafEnoughInjectives :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{max u v} X) :=
  abelianSheafEnoughInjectives X

/-- Sections over an open form an additive functor on abelian sheaves. -/
local instance sectionsAdditive (U : Opens X) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op U)).Additive := by
  change (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op U)).Additive
  infer_instance

attribute [local instance] HasDerivedCategory.standard

/-- The right derived functors of global sections are additive.  Mathlib does not record this as
an instance for `CategoryTheory.Functor.rightDerived`. -/
local instance additiveRightDerivedSections (U : Opens X) (n : ℕ) :
    ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op U)).rightDerived n)).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op U))).additive n

/-- `H¹(X, -)` on abelian sheaves: the first right derived functor of global sections. -/
noncomputable abbrev cohomologyOneFunctor (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] :
    TopCat.Sheaf AddCommGrpCat.{max u v} X ⥤ AddCommGrpCat.{max u v} :=
  ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
    (op (⊤ : Opens X))).rightDerived 1

/-- `H¹(X, -)` is additive, at the spelling the statements below use. -/
local instance additiveCohomologyOneFunctor : (cohomologyOneFunctor.{u, v} X).Additive :=
  additiveRightDerivedSections ⊤ 1

/-- `H¹(X, I)`, the first cohomology of an abelian sheaf. -/
noncomputable abbrev cohomologyOne (I : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    Type (max u v) := ToType ((cohomologyOneFunctor X).obj I)

/-- **An injective-resolution representative of a Čech cocycle represents its refinement.**
The Čech zero-cochain is refined, and the global resolution cocycle is unchanged. -/
noncomputable def refinementRepresentative {Λ : Type w} {K : Type w'}
    (U : Λ → Opens X) (V : K → Opens X) (ρ : K → Λ) (hρ : ∀ k, V k ≤ U (ρ k))
    (hU : (⊤ : Opens X) = ⨆ i, U i) (hV : (⊤ : Opens X) = ⨆ k, V k)
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (J : InjectiveResolution H)
    {c : cocycles1 U H.presheaf}
    (rep : CechOneResolutionRepresentative X ⊤ U hU H J c) :
    CechOneResolutionRepresentative X ⊤ V hV H J
      (refinementCocycles1 U V ρ hρ H.presheaf c) where
  b := refinementMap U V ρ hρ (J.cocomplex.X 0).presheaf 0 rep.b
  cycle := rep.cycle
  coboundary j := by
    have h : cechD V (J.cocomplex.X 0).presheaf 0
        (refinementMap U V ρ hρ (J.cocomplex.X 0).presheaf 0 rep.b) =
        push V (J.ι.f 0).hom 1
          ((refinementCocycles1 U V ρ hρ H.presheaf c : cocycles1 V H.presheaf) :
            Cochain V H.presheaf 1) :=
      (refinementMap_cechD U V ρ hρ (J.cocomplex.X 0).presheaf 0 rep.b).symm.trans
        ((congrArg (refinementMap U V ρ hρ (J.cocomplex.X 0).presheaf 1)
          (coboundary_eq X U H ⊤ hU J rep)).trans
          (push_refinementMap U V ρ hρ (J.ι.f 0).hom 1 (c : Cochain U H.presheaf 1)).symm)
    exact congrFun h j
  restriction j := by
    have h := congrArg (restr (J.cocomplex.X 1).presheaf (inter_le_inter_comp U V ρ hρ j))
      (restriction_eq X U H ⊤ hU J rep (ρ ∘ j))
    rw [restr_restr, map_neg, restr_app (P := (J.cocomplex.X 0).presheaf)
      (Q := (J.cocomplex.X 1).presheaf) (J.cocomplex.d 0 1).hom,
      ← refinementMap_apply] at h
    exact h

/-- **The comparison from first Čech cohomology to first sheaf cohomology is compatible with
refinement of the covering.**  The two comparison values are the homology class of one and the
same global resolution cocycle.

Stacks 09V2 uses this compatibility inside its proof, where it carries no label of its own. -/
theorem cechH1ToRightDerivedSections_refinement {Λ : Type w} {K : Type w'}
    (U : Λ → Opens X) (V : K → Opens X) (ρ : K → Λ) (hρ : ∀ k, V k ≤ U (ρ k))
    (hU : (⊤ : Opens X) = ⨆ i, U i) (hV : (⊤ : Opens X) = ⨆ k, V k)
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (z : CechH1 U H.presheaf) :
    cechH1ToRightDerivedSections X ⊤ V hV H (refinementCechH1 U V ρ hρ H.presheaf z) =
      cechH1ToRightDerivedSections X ⊤ U hU H z := by
  classical
  refine Quotient.inductionOn z ?_
  intro c
  obtain ⟨rep⟩ :=
    nonempty_cechOneResolutionRepresentative X U H ⊤ hU (InjectiveResolution.of H) c
  rw [show (Quotient.mk _ c : CechH1 U H.presheaf) = cls U H.presheaf c from rfl,
    refinementCechH1_cls,
    cechH1ToRightDerivedSections_apply X ⊤ V hV H (InjectiveResolution.of H) _
      (refinementRepresentative U V ρ hρ hU hV H (InjectiveResolution.of H) rep),
    cechH1ToRightDerivedSections_apply X ⊤ U hU H (InjectiveResolution.of H) c rep]
  rfl

/-! ### The `H⁰(X, O)`-module structure on `H¹(X, I)` -/

namespace SquareZeroKernel

variable {O' O : TopCat.Presheaf CommRingCat.{max u v} X}
  {I : TopCat.Sheaf AddCommGrpCat.{max u v} X} (E : SquareZeroKernel O' O I)

/-- The action of a global section of `O` on `H¹(X, I)`: the map induced on first cohomology by
multiplication by that section on the kernel. -/
noncomputable def smulCohomology (r : ToType (O.obj (op (⊤ : Opens X))))
    (m : cohomologyOne I) : cohomologyOne I :=
  (cohomologyOneFunctor X).map (E.smulHom r) m

/-- **The defining equation of the `H⁰(X, O)`-action on `H¹(X, I)`.** -/
theorem smulCohomology_def (r : ToType (O.obj (op (⊤ : Opens X)))) (m : cohomologyOne I) :
    E.smulCohomology r m = (cohomologyOneFunctor X).map (E.smulHom r) m := rfl

/-- **Stacks 0B8S**, first clause: `M = H¹(X, I)` is a module over `R = H⁰(X, O)`.  The kernel
is a sheaf of `O`-modules (`Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.incl_smul`),
and a global section of `O` acts on `M` through the endomorphism of the kernel it induces. -/
@[stacks 0B8S "the `H⁰(X, O)`-module structure on `H¹(X, I)`", instance_reducible]
noncomputable def moduleCohomology :
    Module (ToType (O.obj (op (⊤ : Opens X)))) (cohomologyOne I) where
  smul := E.smulCohomology
  one_smul m := by
    change (cohomologyOneFunctor X).map (E.smulHom 1) m = m
    rw [E.smulHom_one, CategoryTheory.Functor.map_id]
    rfl
  mul_smul r r' m := by
    change (cohomologyOneFunctor X).map (E.smulHom (r * r')) m =
      (cohomologyOneFunctor X).map (E.smulHom r)
        ((cohomologyOneFunctor X).map (E.smulHom r') m)
    rw [E.smulHom_mul, CategoryTheory.Functor.map_comp]
    rfl
  smul_zero r := map_zero ((cohomologyOneFunctor X).map (E.smulHom r)).hom
  smul_add r m m' := map_add ((cohomologyOneFunctor X).map (E.smulHom r)).hom m m'
  add_smul r r' m := by
    change (cohomologyOneFunctor X).map (E.smulHom (r + r')) m =
      (cohomologyOneFunctor X).map (E.smulHom r) m +
        (cohomologyOneFunctor X).map (E.smulHom r') m
    rw [E.smulHom_add, CategoryTheory.Functor.map_add]
    rfl
  zero_smul m := by
    change (cohomologyOneFunctor X).map (E.smulHom 0) m = 0
    rw [E.smulHom_zero, CategoryTheory.Functor.map_zero]
    rfl

/-! ### The boundary map -/

/-- The canonical covering of `X` attached to a global section of `O`: the opens on which the
section lifts to `O'`, indexed by the lifts. -/
abbrev boundaryCover (f : ToType (O.obj (op (⊤ : Opens X)))) :
    E.LiftCover ⊤ f → Opens X := fun j => j.cov

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The canonical covering attached to a global section of `O` covers `X`. -/
theorem boundaryCover_iSup (f : ToType (O.obj (op (⊤ : Opens X)))) :
    (⊤ : Opens X) = ⨆ j, E.boundaryCover f j := E.liftCover_iSup ⊤ f

/-- The canonical Čech `0`-cochain of local lifts of a global section of `O`. -/
noncomputable def liftCochain (f : ToType (O.obj (op (⊤ : Opens X)))) :
    Cochain (E.boundaryCover f) (addPresheaf O') 0 := fun j =>
  rres (inter_le (E.boundaryCover f) j 0) (j 0).lift

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The canonical local lifts of a global section of `O` do lift it. -/
theorem π_liftCochain (f : ToType (O.obj (op (⊤ : Opens X))))
    (j : Fin 1 → E.LiftCover ⊤ f) :
    (addMap E.π).app (op (inter (E.boundaryCover f) j)) (E.liftCochain f j) =
      restr (addPresheaf O) (inter_le_of_eq_iSup (E.boundaryCover_iSup f) j) f := by
  exact E.π_rres_lift (j 0) _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The Čech differential of the canonical local lifts is killed by `π`. -/
theorem π_cechD_liftCochain (f : ToType (O.obj (op (⊤ : Opens X))))
    (j : Fin 2 → E.LiftCover ⊤ f) :
    E.π.app (op (inter (E.boundaryCover f) j))
        (asRing (cechD (E.boundaryCover f) (addPresheaf O') 0 (E.liftCochain f) j)) = 0 := by
  have h0 : push (E.boundaryCover f) (addMap E.π) 1
      (cechD (E.boundaryCover f) (addPresheaf O') 0 (E.liftCochain f)) = 0 :=
    (push_cechD (E.boundaryCover f) (addMap E.π) 0 (E.liftCochain f)).trans
      (cechD_eq_zero_of_restr (E.boundaryCover f) f
        (inter_le_of_eq_iSup (E.boundaryCover_iSup f)) _
        fun i => (push_apply _ _ _ _ i).trans (E.π_liftCochain f i))
  have h1 := congrFun h0 j
  rw [push_apply, Cochain.zero_apply] at h1
  exact h1

/-- The canonical Čech `1`-cochain of differences of the local lifts of a global section of `O`,
as a cochain of the kernel: its image in `O'` is the Čech coboundary of the lifts,
`(i₀, i₁) ↦ f̃_{i₁} - f̃_{i₀}`, the negative of the cocycle `α` of Stacks 0B8S and 02AP. -/
noncomputable def boundaryCochain (f : ToType (O.obj (op (⊤ : Opens X)))) :
    Cochain (E.boundaryCover f) I.presheaf 1 := fun j =>
  E.pre (inter (E.boundaryCover f) j)
    (asRing (cechD (E.boundaryCover f) (addPresheaf O') 0 (E.liftCochain f) j))
    (E.π_cechD_liftCochain f j)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The cochain of differences has the Čech differential of the lifts as its image. -/
theorem push_boundaryCochain (f : ToType (O.obj (op (⊤ : Opens X)))) :
    push (E.boundaryCover f) E.ι 1 (E.boundaryCochain f) =
      cechD (E.boundaryCover f) (addPresheaf O') 0 (E.liftCochain f) :=
  funext fun j => E.incl_pre _ _ (E.π_cechD_liftCochain f j)

/-- The canonical Čech `1`-cocycle of differences of the local lifts of a global section of
`O`. -/
noncomputable def boundaryCocycle (f : ToType (O.obj (op (⊤ : Opens X)))) :
    cocycles1 (E.boundaryCover f) I.presheaf :=
  ⟨E.boundaryCochain f, by
    refine injective_push (E.boundaryCover f) E.ι E.ι_injective 2 ?_
    rw [map_zero, push_cechD, E.push_boundaryCochain f]
    exact cechD_cechD (E.boundaryCover f) (addPresheaf O') 0 (E.liftCochain f)⟩

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The cocycle of differences has the Čech differential of the lifts as its image. -/
theorem push_boundaryCocycle (f : ToType (O.obj (op (⊤ : Opens X)))) :
    push (E.boundaryCover f) E.ι 1
        ((E.boundaryCocycle f : cocycles1 (E.boundaryCover f) I.presheaf) :
          Cochain (E.boundaryCover f) I.presheaf 1) =
      cechD (E.boundaryCover f) (addPresheaf O') 0 (E.liftCochain f) :=
  E.push_boundaryCochain f

/-- **The boundary map `∂ : H⁰(X, O) → H¹(X, I)`** of the short exact sequence
`0 → I → O' → O → 0`, in the Čech description of Stacks 02AP: the class of the cocycle of
differences of local lifts, transported to `H¹(X, I)` by the comparison of Stacks 01EQ.  The
cocycle is the Čech coboundary `(i₀, i₁) ↦ f̃_{i₁} - f̃_{i₀}` of the lifts, so this is the
negative of the `δ` of Stacks 02AP, whose cocycle is `(i₀, i₁) ↦ f̃_{i₀} - f̃_{i₁}`. -/
@[stacks 0B8S "the boundary map, in the Čech description of Stacks 02AP"]
noncomputable def boundary (f : ToType (O.obj (op (⊤ : Opens X)))) : cohomologyOne I :=
  cechH1ToRightDerivedSections X ⊤ (E.boundaryCover f) (E.boundaryCover_iSup f) I
    (cls (E.boundaryCover f) I.presheaf (E.boundaryCocycle f))

/-- **The boundary map is computed by the Čech cocycle of differences of local lifts, on every
covering of `X` with such lifts.**  This is the characterization of Stacks 02AP up to sign: the
cocycle is the Čech coboundary `(i₀, i₁) ↦ f̃_{i₁} - f̃_{i₀}` of the lifts, the negative of the
cocycle of Stacks 02AP.  It pins the boundary map, and shows the canonical covering plays no
role. -/
theorem boundary_eq {Λ : Type w} (f : ToType (O.obj (op (⊤ : Opens X))))
    (W : Λ → Opens X) (hW : (⊤ : Opens X) = ⨆ j, W j)
    (lift : Cochain W (addPresheaf O') 0)
    (hlift : ∀ j, (addMap E.π).app (op (inter W j)) (lift j) =
      restr (addPresheaf O) (inter_le_of_eq_iSup hW j) f)
    (c : cocycles1 W I.presheaf)
    (hc : push W E.ι 1 (c : Cochain W I.presheaf 1) = cechD W (addPresheaf O') 0 lift) :
    E.boundary f = cechH1ToRightDerivedSections X ⊤ W hW I (cls W I.presheaf c) := by
  obtain ⟨V, ρ, hρ, ρ', hρ', hVsup, hcls⟩ :=
    exists_common_refinement_cls_eq_of_localLifts (E.boundaryCover f) E.ι (addMap E.π) W
      (E.boundaryCover_iSup f) hW E.ι_injective E.exists_of_π_eq_zero
      (E.π_liftCochain f) hlift (E.push_boundaryCocycle f) hc
  rw [boundary, ← cechH1ToRightDerivedSections_refinement (E.boundaryCover f) V ρ hρ
      (E.boundaryCover_iSup f) hVsup I, hcls,
    cechH1ToRightDerivedSections_refinement W V ρ' hρ' hW hVsup I]

/-- A covering of `X` by opens over which two given global sections of `O` both lift. -/
abbrev boundaryCoverInf (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    E.LiftCover ⊤ f × E.LiftCover ⊤ g → Opens X := fun p => p.1.cov ⊓ p.2.cov

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The common covering attached to two global sections of `O` covers `X`. -/
theorem boundaryCoverInf_iSup (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    (⊤ : Opens X) = ⨆ p, E.boundaryCoverInf f g p := E.iSup_liftCover_inf ⊤ f g


/-- Pushing a Čech `1`-cocycle along a morphism of abelian sheaves. -/
noncomputable def pushCocycles1 {Λ : Type w} (W : Λ → Opens X)
    {H G : TopCat.Sheaf AddCommGrpCat.{max u v} X} (φ : H ⟶ G)
    (c : cocycles1 W H.presheaf) : cocycles1 W G.presheaf :=
  ⟨push W φ.hom 1 (c : Cochain W H.presheaf 1),
    cechD_push W φ.hom 1 _ ((mem_cocycles1_iff W H.presheaf _).mp c.2)⟩

/-- Local lifts of a global section `τ` over the common covering of `f` and `g` give a cocycle
of the kernel whose class is the boundary of `τ`. -/
private theorem exists_boundary_eq_boundaryCoverInf (f g τ : ToType (O.obj (op (⊤ : Opens X))))
    (lift : Cochain (E.boundaryCoverInf f g) (addPresheaf O') 0)
    (hlift : ∀ p, (addMap E.π).app (op (inter (E.boundaryCoverInf f g) p)) (lift p) =
      restr (addPresheaf O) (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g) p) τ) :
    ∃ c : cocycles1 (E.boundaryCoverInf f g) I.presheaf,
      push (E.boundaryCoverInf f g) E.ι 1 (c : Cochain (E.boundaryCoverInf f g) I.presheaf 1) =
        cechD (E.boundaryCoverInf f g) (addPresheaf O') 0 lift ∧
      E.boundary τ = cechH1ToRightDerivedSections X ⊤ (E.boundaryCoverInf f g)
        (E.boundaryCoverInf_iSup f g) I (cls (E.boundaryCoverInf f g) I.presheaf c) := by
  obtain ⟨c, hc⟩ := exists_cocycle_of_localLifts (E.boundaryCoverInf f g) E.ι (addMap E.π)
    (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g)) E.ι_injective E.exists_of_π_eq_zero hlift
  exact ⟨c, hc, E.boundary_eq τ _ _ lift hlift c hc⟩

/-- The lifts of `f` over the common covering for `f` and `g`, as a Čech `0`-cochain. -/
noncomputable def liftCochainFst (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    Cochain (E.boundaryCoverInf f g) (addPresheaf O') 0 := fun p =>
  rres ((inter_le (E.boundaryCoverInf f g) p 0).trans inf_le_left) (p 0).1.lift

/-- The lifts of `g` over the common covering for `f` and `g`, as a Čech `0`-cochain. -/
noncomputable def liftCochainSnd (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    Cochain (E.boundaryCoverInf f g) (addPresheaf O') 0 := fun p =>
  rres ((inter_le (E.boundaryCoverInf f g) p 0).trans inf_le_right) (p 0).2.lift

/-- The products of the lifts of `f` and of `g`, which lift `f * g`. -/
noncomputable def liftCochainMul (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    Cochain (E.boundaryCoverInf f g) (addPresheaf O') 0 := fun p =>
  asRing (E.liftCochainFst f g p) * asRing (E.liftCochainSnd f g p)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The chosen local lifts of `f` over the common covering do lift `f`. -/
theorem π_liftCochainFst (f g : ToType (O.obj (op (⊤ : Opens X))))
    (p : Fin 1 → E.LiftCover ⊤ f × E.LiftCover ⊤ g) :
    (addMap E.π).app (op (inter (E.boundaryCoverInf f g) p)) (E.liftCochainFst f g p) =
      restr (addPresheaf O) (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g) p) f := by
  exact E.π_rres_lift (p 0).1 _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The chosen local lifts of `g` over the common covering do lift `g`. -/
theorem π_liftCochainSnd (f g : ToType (O.obj (op (⊤ : Opens X))))
    (p : Fin 1 → E.LiftCover ⊤ f × E.LiftCover ⊤ g) :
    (addMap E.π).app (op (inter (E.boundaryCoverInf f g) p)) (E.liftCochainSnd f g p) =
      restr (addPresheaf O) (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g) p) g := by
  exact E.π_rres_lift (p 0).2 _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The sums of the chosen local lifts lift `f + g`. -/
theorem π_liftCochainAdd (f g : ToType (O.obj (op (⊤ : Opens X))))
    (p : Fin 1 → E.LiftCover ⊤ f × E.LiftCover ⊤ g) :
    (addMap E.π).app (op (inter (E.boundaryCoverInf f g) p))
        ((E.liftCochainFst f g + E.liftCochainSnd f g) p) =
      restr (addPresheaf O) (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g) p) (f + g) := by
  rw [Cochain.add_apply, map_add, E.π_liftCochainFst, E.π_liftCochainSnd, map_add]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The products of the chosen local lifts lift `f * g`. -/
theorem π_liftCochainMul (f g : ToType (O.obj (op (⊤ : Opens X))))
    (p : Fin 1 → E.LiftCover ⊤ f × E.LiftCover ⊤ g) :
    (addMap E.π).app (op (inter (E.boundaryCoverInf f g) p)) (E.liftCochainMul f g p) =
      restr (addPresheaf O) (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g) p) (f * g) := by
  change E.π.app (op (inter (E.boundaryCoverInf f g) p))
      (asRing (E.liftCochainFst f g p) * asRing (E.liftCochainSnd f g p)) =
    rres (inter_le_of_eq_iSup (E.boundaryCoverInf_iSup f g) p) (f * g)
  rw [map_mul, map_mul]
  exact congrArg₂ (· * ·) (E.π_liftCochainFst f g p) (E.π_liftCochainSnd f g p)

/-- **The boundary map is additive.** -/
theorem boundary_add (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    E.boundary (f + g) = E.boundary f + E.boundary g := by
  obtain ⟨cf, hcf, ef⟩ := E.exists_boundary_eq_boundaryCoverInf f g f _ (E.π_liftCochainFst f g)
  obtain ⟨cg, hcg, eg⟩ := E.exists_boundary_eq_boundaryCoverInf f g g _ (E.π_liftCochainSnd f g)
  obtain ⟨cs, hcs, es⟩ :=
    E.exists_boundary_eq_boundaryCoverInf f g (f + g) _ (E.π_liftCochainAdd f g)
  rw [es, ef, eg, cls_add_of_localLifts (E.boundaryCoverInf f g) E.ι E.ι_injective hcf hcg hcs,
    map_add]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- **The cocycle computation of Stacks 0B8S.**  Let `a₀, a₁` be lifts of `f` and `b₀, b₁` lifts
of `g` over an open, let `α` and `β` be sections of the kernel with inclusions `a₀ - a₁` and
`b₀ - b₁`, and let `γ` have inclusion `a₀b₀ - a₁b₁`.  Then `γ = α g + f β` for the `O`-module
structure on the kernel.  This is the identity
`f₀g₀ - f₁g₁ = (f₀ - f₁)g₀ + f₁(g₀ - g₁)` of the source.  In the application `a₀, b₀` are the lifts
at the face omitting position `0` (the index `i₁`) and `a₁, b₁` those at `i₀`, so `α` is the value
at `(i₀, i₁)` of the Čech coboundary `f̃_{i₁} - f̃_{i₀}`, the negative of the 02AP cocycle. -/
theorem eq_smul_add_smul {V : Opens X} (f g : ToType (O.obj (op (⊤ : Opens X))))
    (a₀ a₁ b₀ b₁ : ToType (O'.obj (op V)))
    (hb₀ : E.π.app (op V) b₀ = rres le_top g) (ha₁ : E.π.app (op V) a₁ = rres le_top f)
    (α β γ : ToType (I.presheaf.obj (op V)))
    (hα : E.incl V α = a₀ - a₁) (hβ : E.incl V β = b₀ - b₁)
    (hγ : E.incl V γ = a₀ * b₀ - a₁ * b₁) :
    γ = E.smul V (rres le_top g) α + E.smul V (rres le_top f) β := by
  refine E.incl_injective V ?_
  rw [hγ, E.incl_add, E.incl_smul_of_lift α b₀ hb₀, E.incl_smul_of_lift β a₁ ha₁, hα, hβ]
  ring

/-- **Stacks 0B8S**, the Leibniz rule.  On a covering over which both `f` and `g` lift, the
cocycle attached to `f * g` is `α g + f β`, where `α` and `β` are the cocycles attached to `f`
and to `g` and the products are taken for the `O`-module structure on the kernel. -/
@[stacks 0B8S "the Leibniz rule for the boundary map"]
theorem boundary_leibniz (f g : ToType (O.obj (op (⊤ : Opens X)))) :
    E.boundary (f * g) =
      E.smulCohomology f (E.boundary g) + E.smulCohomology g (E.boundary f) := by
  obtain ⟨cf, hcf, ef⟩ := E.exists_boundary_eq_boundaryCoverInf f g f _ (E.π_liftCochainFst f g)
  obtain ⟨cg, hcg, eg⟩ := E.exists_boundary_eq_boundaryCoverInf f g g _ (E.π_liftCochainSnd f g)
  obtain ⟨cm, hcm, em⟩ :=
    E.exists_boundary_eq_boundaryCoverInf f g (f * g) _ (E.π_liftCochainMul f g)
  have hkey : cm = pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom g) cf +
      pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom f) cg := by
    refine Subtype.ext (funext fun j => ?_)
    have hcfj := congrFun hcf j
    have hcgj := congrFun hcg j
    have hcmj := congrFun hcm j
    rw [push_apply, cechD_zero_apply] at hcfj hcgj hcmj
    have hprod : ∀ k : Fin 2,
        restr (addPresheaf O') (inter_le_omit (E.boundaryCoverInf f g) j k)
            (E.liftCochainMul f g (j ∘ k.succAbove)) =
          rres (inter_le_omit (E.boundaryCoverInf f g) j k)
              (asRing (E.liftCochainFst f g (j ∘ k.succAbove))) *
            rres (inter_le_omit (E.boundaryCoverInf f g) j k)
              (asRing (E.liftCochainSnd f g (j ∘ k.succAbove))) :=
      fun k => rres_mul _ _ _
    rw [hprod 0, hprod 1] at hcmj
    have hb₀ : E.π.app (op (inter (E.boundaryCoverInf f g) j))
        (rres (inter_le_omit (E.boundaryCoverInf f g) j 0)
          (asRing (E.liftCochainSnd f g (j ∘ (0 : Fin 2).succAbove)))) = rres le_top g :=
      (E.π_rres _ _).trans
        ((congrArg (rres _) (E.π_liftCochainSnd f g _)).trans (rres_rres _ _ g))
    have ha₁ : E.π.app (op (inter (E.boundaryCoverInf f g) j))
        (rres (inter_le_omit (E.boundaryCoverInf f g) j 1)
          (asRing (E.liftCochainFst f g (j ∘ (1 : Fin 2).succAbove)))) = rres le_top f :=
      (E.π_rres _ _).trans
        ((congrArg (rres _) (E.π_liftCochainFst f g _)).trans (rres_rres _ _ f))
    exact E.eq_smul_add_smul f g _ _ _ _ hb₀ ha₁ _ _ _ hcfj hcgj hcmj
  rw [em, ef, eg, hkey,
    show cls (E.boundaryCoverInf f g) I.presheaf
          (pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom g) cf +
            pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom f) cg) =
        cls (E.boundaryCoverInf f g) I.presheaf
            (pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom g) cf) +
          cls (E.boundaryCoverInf f g) I.presheaf
            (pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom f) cg) from rfl,
    map_add,
    ← cechH1ToRightDerivedSections_naturality X ⊤ (E.boundaryCoverInf f g)
      (E.boundaryCoverInf_iSup f g) (E.smulHom g) cf
      (pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom g) cf) fun i => rfl,
    ← cechH1ToRightDerivedSections_naturality X ⊤ (E.boundaryCoverInf f g)
      (E.boundaryCoverInf_iSup f g) (E.smulHom f) cg
      (pushCocycles1 (E.boundaryCoverInf f g) (E.smulHom f) cg) fun i => rfl]
  exact add_comm _ _


/-- The unit global section of `O` acts on `H¹(X, I)` as the identity. -/
theorem smulCohomology_one (m : cohomologyOne I) : E.smulCohomology 1 m = m := by
  rw [smulCohomology_def, E.smulHom_one, CategoryTheory.Functor.map_id]
  rfl

/-- The boundary map kills the unit global section, as a derivation must. -/
theorem boundary_one : E.boundary (1 : ToType (O.obj (op (⊤ : Opens X)))) = 0 := by
  have h := E.boundary_leibniz 1 1
  rw [mul_one, E.smulCohomology_one] at h
  rwa [eq_comm, add_eq_right] at h

/-- **Stacks 0B8S**, in the Čech description of the boundary map.  Let `X` be a topological
space and `π : O' ⟶ O` a locally surjective morphism of presheaves of commutative rings whose
kernel `I` is a sheaf of square zero.  Then `M = H¹(X, I)` is a module over `R = O(X)`, and the
boundary map `∂ : R → M` of `0 → I → O' → O → 0` is a derivation.  For sheaves `O'` and `O` this
`∂` is the connecting morphism of cohomology
(`Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.boundary_eq_connecting`). -/
@[stacks 0B8S "the boundary map of the square-zero extension is a derivation"]
noncomputable def boundaryDerivation :
    letI := E.moduleCohomology
    Derivation ℤ (ToType (O.obj (op (⊤ : Opens X)))) (cohomologyOne I) :=
  letI := E.moduleCohomology
  { toLinearMap := (AddMonoidHom.mk' E.boundary E.boundary_add).toIntLinearMap
    map_one_eq_zero' := E.boundary_one
    leibniz' := E.boundary_leibniz }

/-- The derivation of Stacks 0B8S is the boundary map. -/
theorem boundaryDerivation_apply (f : ToType (O.obj (op (⊤ : Opens X)))) :
    letI := E.moduleCohomology
    E.boundaryDerivation f = E.boundary f := rfl

end SquareZeroKernel

end Cohomology

end Stacks.Cohomology.SquareZeroBoundary

end
