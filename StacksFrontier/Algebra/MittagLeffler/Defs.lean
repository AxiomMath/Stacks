module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

/-!
# Mittag-Leffler systems of modules
-/

@[expose] public section

universe u v w w'



/-!
# Mittag-Leffler systems of modules

Let `R` be a ring and let `(M i, f i j)` be a directed system of `R`-modules, that is a functor
`F` from an index category `J` to `ModuleCat R`, directed in the source. Dualizing into a fixed
`R`-module `N` turns it into an inverse system

  `(Hom_R(M i, N), Hom_R(f i j, N))`,

the composite of `F.op` with the functor `Hom_R(-, N)` represented by `N`. The system
`(M i, f i j)` is a *Mittag-Leffler system* if every `M i` is an `R`-module of finite presentation
and if, for every `R`-module `N`, that inverse system of dual modules satisfies the Mittag-Leffler
condition: for each `i` the images `Im(Hom_R(M j, N) → Hom_R(M i, N))`, `j ≥ i`, stabilize.

Both conditions are needed and neither follows from the other: a constant system at a module which
is not of finite presentation has identity transition maps, hence Mittag-Leffler dual systems,
while writing `ℚ` as the colimit of the directed system of its cyclic subgroups `ℤ · (1 / n !)`
gives a directed system of finite free `ℤ`-modules whose dual systems are not all Mittag-Leffler,
since `ℚ` is flat and countably generated but not projective.

Modules which are colimits of Mittag-Leffler systems are the Mittag-Leffler modules; that
characterization, and the equivalent forms of the condition above, are separate results.

## Main definitions

* `CategoryTheory.Functor.IsMittagLefflerSystem`: a diagram of `R`-modules is a Mittag-Leffler
  system if its members are of finite presentation and all of its dual inverse systems are
  Mittag-Leffler.

## Implementation notes

A directed system of `R`-modules is a functor `F : J ⥤ ModuleCat R`, and the inverse system of
dual modules is the composite `F.op ⋙ yoneda.obj N : Jᵒᵖ ⥤ Type v`, which sends `op i` to
`Hom_R(M i, N)` and a morphism `op j ⟶ op i`, that is a morphism `f i j : M i ⟶ M j`, to
precomposition with it. This pins the transition maps of the inverse system to the source's
`Hom_R(f i j, N)` rather than merely asserting that an inverse system exists.

The Mittag-Leffler condition on that system of sets is Mathlib's
`CategoryTheory.Functor.IsMittagLeffler`, which asks that for each `i` some image
`Im(Hom_R(M j, N) → Hom_R(M i, N))` be contained in all of them. For a directed index those
images decrease along `j`, so containment in all of them forces equality for `j ≥ i` large, which
is the source's stabilization condition (Definition 0595). Since a system of modules is
Mittag-Leffler exactly when its underlying system of sets is, the `Type`-valued form is the
faithful one.

Filteredness of `J` is not assumed: the definition is meaningful for an arbitrary index category,
and users add `[IsFiltered J]` where directedness is what makes the condition behave, exactly as
Mathlib's `Functor.IsMittagLeffler` assumes nothing about its index. Commutativity of `R` is
likewise unused, so `R` is an arbitrary ring, where the source's rings are commutative.

The test module `N` ranges over `ModuleCat.{v} R`, the universe of the members of the system,
rather than over all universes. This is no restriction for a `v`-small index category: the
condition for all `N` follows from the single case `N = ∏ s, M s`, which then lies in `Type v`
(Proposition 059E, (5) ⟹ (4)).

Faithfulness. (1) Neither conjunct is idle, by the two witnesses in the header: finite
presentation of the members does not follow from Mittag-Leffler dual systems, nor conversely.
(2) The scalars are the source's: one ring `R` throughout, the members are `R`-modules, the
transition maps and the dual maps are `R`-linear, `N` is an `R`-module and there is no change of
rings. (3) The dual inverse system is pinned, not merely asserted to exist: its terms are the
`R`-module homomorphisms `M i ⟶ N` and its transition maps are precomposition with the `f i j`.
(4) The instantiation is not degenerate: a constant system at a finitely presented module is a
Mittag-Leffler system, its dual systems having identity transition maps, and more substantially
so is any directed system of finite free modules with a projective colimit.

## References

* [Stacks Project, Tag 059A](https://stacks.math.columbia.edu/tag/059A)
-/

open CategoryTheory



namespace CategoryTheory.Functor

/-- **Stacks 059A.** A diagram `F : J ⥤ ModuleCat R` of `R`-modules, thought of as a directed
system `(M i, f i j)`, is a *Mittag-Leffler system* if every `M i` is an `R`-module of finite
presentation and if for every `R`-module `N` the inverse system of dual modules
`(Hom_R(M i, N), Hom_R(f i j, N))`, that is `F.op ⋙ yoneda.obj N`, satisfies the Mittag-Leffler
condition. -/
@[stacks 059A]
public def IsMittagLefflerSystem {R : Type u} [Ring R] {J : Type w} [Category.{w'} J]
    (F : J ⥤ ModuleCat.{v} R) : Prop :=
  (∀ j, Module.FinitePresentation R (F.obj j)) ∧
    ∀ N : ModuleCat.{v} R, (F.op ⋙ yoneda.obj N).IsMittagLeffler

end CategoryTheory.Functor

end

/-!
# Mittag-Leffler modules

An `R`-module `M` is *Mittag-Leffler* if the five equivalent conditions of
Stacks Proposition 10.88.6 hold. Four of them are phrased in terms of a chosen
directed system `(M_i, f_{ij})` of finitely presented `R`-modules with
`M = colim M_i`; the first is intrinsic to `M`, and is the one taken here as the
definition:

  For every finitely presented `R`-module `P` and module map `f : P → M`, there
  exists a finitely presented `R`-module `Q` and a module map `g : P → Q` such
  that `f` and `g` dominate each other, i.e. `Ker(f ⊗_R id_N) = Ker(g ⊗_R id_N)`
  for every `R`-module `N`.

The auxiliary one-way relation is Stacks Definition 10.88.2: `g : P → Q`
*dominates* `f : P → M` iff `Ker(f ⊗ id_N) ⊆ Ker(g ⊗ id_N)` for every
`R`-module `N`.

## Main definitions

* `Dominates`: the one-way domination relation between two maps out of `P`.
* `DominateEachOther`: mutual domination.
* `IsMittagLeffler`: the Mittag-Leffler condition on `M`.

The base ring `R`, the module `M`, the finitely presented modules `P` and `Q`,
and the test module `N` each carry an independent universe parameter;
`Dominates` and `DominateEachOther` take the universe of `N` explicitly, so that
at use sites it stays free and the quantification really is over every
`R`-module `N`. This is not Mathlib's `CategoryTheory.Functor.IsMittagLeffler`,
which is the Mittag-Leffler condition for inverse systems.
-/

@[expose] public section

universe uR uP uM uQ uN

/-- (Stacks 10.88.2, tag 059B.) Let `f : P → M` and `g : P → Q` be two
`R`-linear maps with common source. We say `g` *dominates* `f` if for every
`R`-module `N`, `Ker(f ⊗_R id_N) ⊆ Ker(g ⊗_R id_N)` as submodules of
`P ⊗_R N`. The test module `N` is universe-polymorphic via the explicit
universe parameter `uN`, so the predicate captures the Stacks quantification
"for every `R`-module `N`". -/
def Dominates {R : Type uR} [CommRing R]
    {P : Type uP} {M : Type uM} {Q : Type uQ}
    [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] M) (g : P →ₗ[R] Q) : Prop :=
  ∀ (N : Type uN) [AddCommGroup N] [Module R N],
    LinearMap.ker (TensorProduct.map f (LinearMap.id : N →ₗ[R] N)) ≤
      LinearMap.ker (TensorProduct.map g (LinearMap.id : N →ₗ[R] N))

/-- Two `R`-linear maps `f : P → M` and `g : P → Q` with common source
*dominate each other* if each dominates the other. Equivalently, for every
`R`-module `N` the kernels of `f ⊗_R id_N` and `g ⊗_R id_N` are equal as
submodules of `P ⊗_R N`. This is the relation used in Stacks Proposition
10.88.6 (tag 059E), condition (1). -/
def DominateEachOther {R : Type uR} [CommRing R]
    {P : Type uP} {M : Type uM} {Q : Type uQ}
    [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] M) (g : P →ₗ[R] Q) : Prop :=
  Dominates.{uR, uP, uM, uQ, uN} f g ∧ Dominates.{uR, uP, uQ, uM, uN} g f

/-- (Stacks 10.88.7, tag 059F.) An `R`-module `M` is *Mittag-Leffler* if for
every finitely presented `R`-module `P` and every `R`-linear map `f : P → M`,
there exists a finitely presented `R`-module `Q` and an `R`-linear map
`g : P → Q` such that `f` and `g` dominate each other.

This is condition (1) of Stacks Proposition 10.88.6 (tag 059E), which is
equivalent to the other four conditions in that proposition. We choose this
condition because it is intrinsic to `M` and does not depend on any auxiliary
choice of a directed system writing `M` as a colimit of finitely presented
modules.

The universe parameters `uP`, `uQ`, `uN` are independent of `uR`, `uM`, so
"for every finitely presented `R`-module `P`", "there exists ... `Q`", and
"for every test module `N`" each range over their own arbitrary universe,
matching the Stacks quantifications. -/
@[stacks 059F]
def IsMittagLeffler (R : Type uR) [CommRing R] (M : Type uM)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ (P : Type uP) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (f : P →ₗ[R] M),
    ∃ (Q : Type uQ) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : Module.FinitePresentation R Q)
      (g : P →ₗ[R] Q),
      DominateEachOther.{uR, uP, uM, uQ, uN} f g

/-- Characterization of `IsMittagLeffler` directly in terms of condition (1) of
Stacks Proposition 10.88.6 (tag 059E): for every finitely presented `R`-module
`P` and module map `f : P → M`, there exists a finitely presented `R`-module
`Q` and module map `g : P → Q` such that for every `R`-module `N` the kernels
of `f ⊗_R id_N` and `g ⊗_R id_N` coincide. -/
theorem isMittagLeffler_def_iff (R : Type uR) [CommRing R]
    (M : Type uM) [AddCommGroup M] [Module R M] :
    IsMittagLeffler.{uR, uP, uM, uQ, uN} R M ↔
      ∀ (P : Type uP) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M),
        ∃ (Q : Type uQ) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q)
          (g : P →ₗ[R] Q),
          (∀ (N : Type uN) [AddCommGroup N] [Module R N],
              LinearMap.ker
                  (TensorProduct.map f (LinearMap.id : N →ₗ[R] N)) =
                LinearMap.ker
                  (TensorProduct.map g (LinearMap.id : N →ₗ[R] N))) := by
  refine ⟨fun h P _ _ _ f ↦ ?_, fun h P _ _ _ f ↦ ?_⟩
  · obtain ⟨Q, hQa, hQm, hQfp, g, h₁, h₂⟩ := h P f
    exact ⟨Q, hQa, hQm, hQfp, g, fun N _ _ ↦ (h₁ N).antisymm (h₂ N)⟩
  · obtain ⟨Q, hQa, hQm, hQfp, g, hker⟩ := h P f
    exact ⟨Q, hQa, hQm, hQfp, g, fun N _ _ ↦ (hker N).le, fun N _ _ ↦ (hker N).ge⟩

/-- The Mittag-Leffler condition on `M` in the single-universe spelling that writes mutual
domination as equality of the kernels of `f.rTensor N` and `g.rTensor N`: for every finitely
presented `P` and every `f : P →ₗ[R] M` there is a finitely presented `Q` and a `g : P →ₗ[R] Q`
with `Ker (f ⊗ id_N) = Ker (g ⊗ id_N)` for every `R`-module `N`.

This is `IsMittagLeffler` with every quantified module in the universe of `M`, up to the
propositional identification `isMittagLeffler_def_iff`. It is an `abbrev` so that it unifies with
the condition written out, which is how the statements about Mittag-Leffler modules spell it. -/
abbrev Module.IsMittagLefflerKerEq (R : Type uR) [CommRing R] (M : Type uM) [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ (P : Type uM) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (f : P →ₗ[R] M), ∃ (Q : Type uM) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type uM) [AddCommGroup N]
        [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)

/-- The Mittag-Leffler condition transports along a linear equivalence: a witness for `e ∘ f` is
a witness for `f`, the two having the same tensored kernels. -/
public theorem Module.mittagLeffler_of_linearEquiv {R : Type uR} [CommRing R] {M N : Type uM}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (h : Module.IsMittagLefflerKerEq R N) : Module.IsMittagLefflerKerEq R M := by
  intro P _ _ _ f
  obtain ⟨Q, hQ₁, hQ₂, hQ₃, g, hg⟩ := h P ((e : M →ₗ[R] N) ∘ₗ f)
  refine ⟨Q, hQ₁, hQ₂, hQ₃, g, fun T _ _ => Eq.trans ?_ (hg T)⟩
  rw [LinearMap.rTensor_comp]
  exact (LinearEquiv.ker_comp (e.rTensor T) _).symm

/-- A map whose kernel contains the kernel of a surjection descends along that surjection. -/
public theorem LinearMap.exists_comp_eq_of_ker_le {R : Type*} [CommRing R] {X P Q : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {π : X →ₗ[R] P} (hπ : Function.Surjective π) {g' : X →ₗ[R] Q}
    (h : LinearMap.ker π ≤ LinearMap.ker g') :
    ∃ g : P →ₗ[R] Q, g ∘ₗ π = g' := by
  refine ⟨(Submodule.liftQ _ g' h) ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, ?_⟩
  ext x
  simp [LinearMap.quotKerEquivOfSurjective_symm_apply]

end
