module
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
public import StacksFrontier.CategoryTheory.Sites.Continuous
import StacksCore.Tactic.EgaSgaAttribute

namespace CategoryTheory.Functor

section

universe v₁ v₂ w w' u₁ u₂

/-!
# The pullback along a fully faithful functor of sites is fully faithful

Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be cocontinuous, continuous and fully
faithful, so that `u` gives rise to a morphism of topoi `g : Sh(C) → Sh(D)` and to the adjoint
triple `g_! ⊣ g^{-1} ⊣ g_*` (Stacks 00XO, 00XS). Then `g_!` is fully faithful.

If `C` moreover has fibre products which `u` preserves and a final object whose image under `u` is
final in `D`, then `u` is a morphism of sites `f : D → C` (Stacks 00X6) with `f_* = g^{-1}` and
`f^{-1} = g_!`, and the composition `Sh(C) --g--> Sh(D) --f--> Sh(C)` is isomorphic to the identity
morphism of `Sh(C)`: `g` presents `Sh(C)` as a subtopos of `Sh(D)`, and that embedding admits a
retraction. Unlike the neighbouring lemmas about `g_!` this has no topological counterpart; the
situation to keep in mind is the enlargement of a "partial universe" of schemes keeping the same
topology. Full faithfulness of `f^{-1}` needs none of those extra hypotheses, and the source's own
proof of it uses none: it is the chain
`Mor(g_!F, g_!G) = Mor(F, g^{-1}g_!G) = Mor(F, G)`, the first equality by adjunction and the second
because the unit of `g_! ⊣ g^{-1}` is an isomorphism (Stacks 00XT), which holds for `u` merely
cocontinuous, continuous and fully faithful.

## Main results

* `CategoryTheory.Functor.full_and_faithful_sheafPullback`: the last clause of Stacks 00XU —
  `f^{-1} = g_!` is fully faithful.

## Implementation notes

* The complete statement of Stacks 00XU, under the source's hypotheses (a)–(e), is
  `CategoryTheory.Functor.exists_isMorphismOfSites_comp_iso_id_of_isTerminal` in
  `StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismOfSitesRetraction`, which uses this
  theorem for its last clause. That `u` defines a morphism of sites `f : D → C` is
  `CategoryTheory.Functor.isMorphismOfSites_of_isTerminal` (Stacks 00X6), and that `f ∘ g` is
  isomorphic to the identity morphism of `Sh(C)` comes from the counit of `g^{-1} ⊣ g_*`,
  `CategoryTheory.Functor.isIso_sheafAdjunctionCocontinuous_counit` (Stacks 00XT). Full
  faithfulness of `f^{-1} = g_!` needs neither the fibre products nor the final objects, and is
  stated here under the hypotheses of its own proof. The identifications `f_* = g^{-1}` and
  `f^{-1} = g_!` hold by definition, the morphism of topoi attached to a morphism of sites
  (Stacks 00XC, `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`) having pushforward
  `u^s = u.sheafPushforwardContinuous` and inverse image `u_s = u.sheafPullback`; the conclusion is
  therefore stated for `u.sheafPullback` directly, as in Stacks 00XY.
* Full faithfulness is stated as the conjunction of `CategoryTheory.Functor.Full` and
  `CategoryTheory.Functor.Faithful`, which is the form `MorphismOfTopoi.IsEmbedding` takes for the
  dual condition on `f_*`; the bundled `CategoryTheory.Functor.FullyFaithful` follows by
  `CategoryTheory.Functor.FullyFaithful.ofFullyFaithful`. Equivalently the unit `𝟭 ⟶ g_! ⋙ g^{-1}`
  of `g_! ⊣ g^{-1}` is invertible (`CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit` and
  `CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful`), which is the source's second display
  `g^{-1} ∘ f^{-1} ≅ id`; that display is thus not a separate conclusion but this one.
* The two instance hypotheses are those of Stacks 00XT's half about `g_!`, and both are needed to
  write the statement or to prove it: `(u.sheafPushforwardContinuous A J K).IsRightAdjoint` is what
  makes `g_!` available at all, `g_!` being *the* chosen left adjoint of `g^{-1}`, and the
  pointwise right Kan extensions along `u.op` are what make `g_*` exist, through which the unit of
  `g_! ⊣ g^{-1}` is shown invertible. Neither `HasPullbacks C` nor preservation of `WalkingCospan`
  nor a final object is assumed.
* `g_!` is Mathlib's `CategoryTheory.Functor.sheafPullback` rather than the sheafified left Kan
  extension `(u_p)^#`; the two agree
  (`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`) and full faithfulness is
  insensitive to the choice, as any two left adjoints of `g^{-1}` are isomorphic over `g^{-1}`.
* The statement is for sheaves with values in an arbitrary category `A` and for sites in arbitrary
  universes, where the source has sheaves of sets on small sites: at that generality all three
  functors of the triple are defined in Mathlib, and the source's argument — one adjunction and
  Stacks 00XT — is unchanged.

## References

* [Stacks 00XU](https://stacks.math.columbia.edu/tag/00XU), in the section "Cocontinuous functors
  and morphisms of topoi"; the clause stated here is the last paragraph of its proof, which runs on
  Stacks 00XT alone. Morphisms of topoi are Stacks 00XA, their 2-morphisms Stacks 04IA and subtopoi
  Stacks 08LT.
-/

@[expose] public section

open CategoryTheory in
/-- **Stacks 00XU**, the clause that `f^{-1}` is fully faithful. Let `(C, J)` and `(D, K)` be sites
and let `u : C ⥤ D` be cocontinuous, continuous and fully faithful, and suppose that the inverse
image `g^{-1}` of the associated morphism of topoi `g : Sh(C) → Sh(D)` admits a left adjoint `g_!`.
Then `g_!` is fully faithful.

When `u` also satisfies the hypotheses of Stacks 00X6, so that it defines a morphism of sites
`f : D → C` with `f^{-1} = g_!`, this is the assertion that `f^{-1}` is fully faithful. -/
@[sga "4 III 2.6" "u ff ⇒ u_! ff",
  sga "4 I 5.14" "special case"]
public theorem full_and_faithful_sheafPullback
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    (A : Type w) [Category.{w'} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] [u.IsContinuous J K] [u.Full] [u.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    (u.sheafPullback A J K).Full ∧ (u.sheafPullback A J K).Faithful :=
  have h : (u.sheafPullback A J K).FullyFaithful :=
    (u.sheafAdjunctionContinuous A J K).fullyFaithfulLOfIsIsoUnit
  ⟨h.full, h.faithful⟩
end

end

end CategoryTheory.Functor
