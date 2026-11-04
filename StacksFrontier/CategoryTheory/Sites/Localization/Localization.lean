module
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
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
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `j_{U!}` commutes with connected limits

Let `(C, J)` be a site and let `U` be an object of `C`. The localization functor
`j_U = CategoryTheory.Over.forget U : C/U ⥤ C` is continuous for `J.over U` and `J`, so restriction
of sheaves along it is a functor `j_U^{-1} : Sh(C) ⥤ Sh(C/U)`, namely Mathlib's
`CategoryTheory.GrothendieckTopology.overPullback`; its left adjoint is
`j_{U!} : Sh(C/U) ⥤ Sh(C)`. A left adjoint has no reason to commute with limits, but this one
commutes with fibre products and equalizers, and more generally with every *connected* limit: for a
connected index category `K` it carries limit cones of shape `K` to limit cones. Connectedness is
the only obstruction, and it cannot be dropped: `j_{U!}` of the final sheaf is `h_U^#`, not the
final sheaf, so the empty limit is not preserved.

## Main results

* `CategoryTheory.OverShriek.preservesLimitsOfShape_of_isConnected`: Stacks 04BB, `j_{U!}`
  preserves limits of every connected shape — in particular fibre products and equalizers, and in
  particular it carries a subsheaf inclusion to a subsheaf inclusion.

## Implementation notes

* The source says *finite* connected limits, and names the two cases it uses, fibre products and
  equalizers. Finiteness is dropped, because it is not used by the source's own route: via Stacks
  00Y1 the functor `j_{U!}` is the equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` followed by
  `Over.forget h_U^#`, an equivalence commutes with limits of every size
  (`CategoryTheory.Adjunction.isEquivalencePreservesLimits`), and
  `CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected` — the forgetful functor of a
  slice category preserves connected limits of *arbitrary* shape, with no existence hypothesis on
  the limits — is unrestricted in the shape and in its universes. So the statement is per-shape,
  `Limits.PreservesLimitsOfShape K L` for `[IsConnected K]` with `K` in arbitrary universes, which
  is also the form Mathlib has an API for; there is no class of "finite connected limits" to assume
  or conclude. The source's two cases are the instances `K = Limits.WalkingCospan`
  (`CategoryTheory.widePullbackShape_connected`) and `K = Limits.WalkingParallelPair`
  (`CategoryTheory.parallel_pair_connected`).
* The source's "in particular, if `F ⊂ F'` in `Sh(C/U)` then `j_{U!}F ⊂ j_{U!}F'`" is this
  statement at `K = Limits.WalkingCospan` and nothing more: subsheaf inclusions are exactly the
  monomorphisms of `Sh(C/U)` (Stacks 00WM, 00WN; in Mathlib
  `CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono`), and
  `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape` is an instance deducing
  `L.PreservesMonomorphisms` from `Limits.PreservesLimitsOfShape Limits.WalkingCospan L`. It
  therefore gets no declaration of its own: it has no content beyond the fibre product case, and a
  named composite with no call site is a maintenance cost.
* `j_{U!}` is not pinned to a construction: it is any functor `L` equipped with an adjunction
  `L ⊣ J.overPullback (Type v) U`. This is the universal property the source uses (Stacks 00XS,
  03CD), it determines `L` up to canonical isomorphism, and `PreservesLimitsOfShape` transfers
  along such an isomorphism (`CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`), so the
  abstract form is neither weaker nor stronger than a form fixing a model. Instantiating `L` with
  `(Over.forget U).sheafPullback (Type v) (J.over U) J` and `adj` with
  `CategoryTheory.Functor.sheafAdjunctionContinuous` gives the spelling of `j_{U!}` used elsewhere
  in this repository. The hypothesis `(J.overPullback (Type v) U).IsRightAdjoint` that names a
  chosen left adjoint is implied by `adj` and so is not assumed.
* Sheaves of sets take values in `Type v`, the universe of the homs of `C`, as in the localization
  files of this repository, where Stacks 00Y1 and 03CD — the inputs of the source's proof — are
  available in that universe. Accordingly the ambient sheafification hypotheses are those of the
  source's setting: `Sh(C)` and `Sh(C/U)` admit sheafification, and a map of presheaves of sets on
  `C` becomes an isomorphism after sheafification exactly when it is locally bijective. All three
  are automatic for the standard universe choice `Type max u v`, in particular for a small site.
  They are the hypotheses of Stacks 00Y1 in this repository, binder for binder.

Faithfulness, on four points:

1. Every hypothesis is used: `adj` is what makes `L` be `j_{U!}` rather than an arbitrary functor,
   and `IsConnected K` is used, not decoration — for `K` the empty category the conclusion is false
   (`j_{U!}` of the final sheaf is `h_U^#`). The three instance hypotheses are the ambient
   existence assumptions of the source's setting, used by its proof through Stacks 00Y1 and 03CD;
   none restricts the mathematical content, and all three hold for `Type max u v`.
2. The base is the source's: sheaves of sets on the given site `(C, J)` and on its localization
   `(C/U, J.over U)` — `J.over U` is Mathlib's `@[stacks 00XZ]` topology on `Over U` — and the
   functor is the left adjoint of restriction along `j_U`, not along any other functor.
3. The functor is pinned, by its universal property: `L` is a left adjoint of
   `j_U^{-1} = J.overPullback (Type v) U`, so the statement is about `j_{U!}`; and the assertion is
   that limit cones go to limit cones, i.e. that the canonical comparison map from `j_{U!}` of a
   limit to the limit of `j_{U!}` is an isomorphism, not merely that some map exists.
4. Not degenerate: take `C : Type v` with any topology `J`, so that `Type v = Type max u v` and the
   three instances are automatic, and so is the left adjoint itself — the Kan extension
   construction `CategoryTheory.sheafPullbackConstruction` supplies
   `(J.overPullback (Type v) U).IsRightAdjoint`. Then take `L` to be
   `(Over.forget U).sheafPullback (Type v) (J.over U) J` and `adj` to be
   `(Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J`. For `J = ⊥` the
   sheaf categories are the presheaf categories and `j_{U!}G(X) = ∐_{a : X ⟶ U} G(X, a)`, where
   preservation of a fibre product is a genuine computation — the coproduct is over the same index
   `a` on both sides only because the shape is connected.

## References

Stacks Project, tag 04BB (`sites-lemma-j-shriek-commutes-equalizers-fibre-products`); Stacks 00Y1
for `Sh(C/U) ≌ Sh(C)/h_U^#`, Stacks 03CD for the description of `j_{U!}`, Stacks 00XS for the
variant hypothesis "`C` has fibre products and equalizers", and Stacks 00WM, 00WN for subsheaf
inclusions as monomorphisms.
-/

namespace CategoryTheory.OverShriek

section

universe w' w v u v₂ u₂ v₁ u₁
open CategoryTheory

namespace Stacks.Sites.ConnectedLimits

/-- An equivalence onto a slice category, followed by the forgetful functor of that slice,
preserves limits of every connected shape: an equivalence preserves limits of every shape
(`CategoryTheory.Adjunction.isEquivalencePreservesLimits`) and `Over.forget` preserves the
connected ones (`CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected`). -/
@[sga "4 IV 5.11.1" "special case", sga "4 IV 5.3" "partial"]
private lemma preservesLimitsOfShape_comp_overForget {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] {X : B} (F : A ⥤ Over X) [F.IsEquivalence]
    (K : Type w) [Category.{w'} K] [IsConnected K] :
    Limits.PreservesLimitsOfShape K (F ⋙ Over.forget X) :=
  have : Limits.PreservesLimitsOfSize.{w', w} F := Adjunction.isEquivalencePreservesLimits F
  inferInstance

end Stacks.Sites.ConnectedLimits

@[expose] public section

open Stacks.Sites.ConnectedLimits in
/-- **Stacks 04BB.** Let `C` be a site and let `U` be an object of `C`. Let `L` be a left adjoint
of the restriction functor `j_U^{-1} = J.overPullback : Sh(C) ⥤ Sh(C/U)`, i.e. let `L` be
`j_{U!}`. Then `L` commutes with limits of every connected shape `K`; in particular it commutes
with fibre products (`K = WalkingCospan`) and equalizers (`K = WalkingParallelPair`), and hence
carries subsheaf inclusions to subsheaf inclusions. -/
@[stacks 04BB "j_{U!} commutes with fibre products and equalizers, and more generally with
connected limits; in particular it preserves subsheaf inclusions.",
  sga "4 III 5.1" "fibre products clause", sga "4 III 1.9.2" "more general"]
public theorem preservesLimitsOfShape_of_isConnected {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) [HasWeakSheafify J (Type v)]
    [HasWeakSheafify (J.over U) (Type v)] [J.WEqualsLocallyBijective (Type v)]
    {L : Sheaf (J.over U) (Type v) ⥤ Sheaf J (Type v)} (adj : L ⊣ J.overPullback (Type v) U)
    {K : Type w} [Category.{w'} K] [IsConnected K] :
    Limits.PreservesLimitsOfShape K L :=
  have := preservesLimitsOfShape_comp_overForget (OverShriek.sheafFunctorToOver (U := U) J) K
  Limits.preservesLimitsOfShape_of_natIso (OverShriek.sheafFunctorToOverForgetIsoOfAdjunction J adj)
end

end

end CategoryTheory.OverShriek

namespace CategoryTheory.OverShriek

section

universe v u

/-!
# `j_{U!}` reflects injections and surjections

Let `(C, J)` be a site and let `U` be an object of `C`. The localization functor `j_U : C/U ⥤ C`
is `CategoryTheory.Over.forget U`, which is continuous for `J.over U` and `J`, so that restriction
of sheaves along it is a functor `j_U^{-1} : Sh(C) ⥤ Sh(C/U)`, namely Mathlib's
`CategoryTheory.GrothendieckTopology.overPullback`. Its left adjoint `j_{U!} : Sh(C/U) ⥤ Sh(C)`
reflects injections and surjections of sheaves of sets: if `j_{U!}φ` is injective, resp.
surjective, then so is `φ`.

## Main results

* `CategoryTheory.OverShriek.reflectsMonomorphisms_and_reflectsEpimorphisms`: Stacks 0E8E, the two
  halves of the source's statement as the two conjuncts of one statement — `j_{U!}` reflects
  monomorphisms, and `j_{U!}` reflects epimorphisms.

## Implementation notes

* Injections and surjections of sheaves of sets (Stacks 00WM: injective on sections over every
  object, resp. locally surjective) are exactly the monomorphisms, resp. the epimorphisms, of
  `Sh(C)` (Stacks 00WN); in Mathlib that dictionary is
  `CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono` together with
  `CategoryTheory.NatTrans.mono_iff_mono_app`, and
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`. The statement is therefore given in the
  categorical form, which is the form the source's own proof reduces to ("we have to show `j_{U!}`
  reflects monomorphisms and epimorphisms, see Lemma 00WN") and the form for which Mathlib has an
  API: `CategoryTheory.Functor.ReflectsMonomorphisms` and
  `CategoryTheory.Functor.ReflectsEpimorphisms`, with `CategoryTheory.Functor.mono_of_mono_map` and
  `CategoryTheory.Functor.epi_of_epi_map`. The two classes are the two conjuncts of a single
  statement because the tag is one lemma with two halves; both halves reduce to `j_{U!}` being
  faithful, by `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful` and its dual.
* `j_{U!}` is not pinned to a construction: it is any functor `L` equipped with an adjunction
  `L ⊣ J.overPullback (Type v) U`. This is the universal property the source uses (Stacks 00XS,
  03CD), it determines `L` up to canonical isomorphism, and both classes transfer along such an
  isomorphism (`CategoryTheory.Functor.ReflectsMonomorphisms.of_iso`), so the abstract form is
  neither weaker nor stronger than a form fixing a model. Instantiating `L` with
  `(Over.forget U).sheafPullback (Type v) (J.over U) J` and `adj` with
  `CategoryTheory.Functor.sheafAdjunctionContinuous` gives the spelling of `j_{U!}` used elsewhere
  in this repository; the hypothesis `(J.overPullback (Type v) U).IsRightAdjoint` that names a
  chosen left adjoint is implied by `adj` and so is not assumed.
* Sheaves of sets take values in `Type v`, the universe of the homs of `C`, as in the localization
  files of this repository, where Stacks 00Y1 and 03CD — the two inputs of the source's proof —
  are available in that universe. Accordingly the ambient sheafification hypotheses are those of
  the source's setting: `Sh(C)` and `Sh(C/U)` admit sheafification, and a map of presheaves of
  sets on `C` becomes an isomorphism after sheafification exactly when it is locally bijective.
  All three are automatic for the standard universe choice `Type max u v`, in particular for a
  small site.

Faithfulness, on four points:

1. Every hypothesis is used: `adj` is what makes `L` be `j_{U!}` rather than an arbitrary functor.
   The three instance hypotheses are the ambient existence assumptions of the source's setting,
   used by its proof through Stacks 00Y1 and 03CD; none restricts the mathematical content, and
   all three hold for `Type max u v`.
2. The base is the source's: sheaves of sets on the given site `(C, J)` and on its localization
   `(C/U, J.over U)` — `J.over U` is Mathlib's `@[stacks 00XZ]` topology on `Over U` — and the
   functor is the left adjoint of restriction along `j_U`, not along any other functor.
3. The functor is pinned, by its universal property: `L` is a left adjoint of
   `j_U^{-1} = J.overPullback (Type v) U`, so the statement is about `j_{U!}` and not about some
   functor that merely exists; and it is the reflection property, not the existence of `L`, that
   is asserted.
4. Not degenerate: take `C : Type v` with any topology `J` (so `Type v = Type max u v` and the
   three instances are automatic), `L := (Over.forget U).sheafPullback (Type v) (J.over U) J` and
   `adj := (Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J`. For `J = ⊥` and `U`
   terminal, `Over U ≌ C` and `j_{U!}` is an equivalence, so both conjuncts have content.

## References

Stacks Project, tag 0E8E (`sites-lemma-j-shriek-reflects-injections-surjections`); Stacks 00WM and
00WN for injections and surjections of sheaves of sets as monomorphisms and epimorphisms; Stacks
00Y1 and 03CD for the description of `j_{U!}` used in the proof.
-/

@[expose] public section

open CategoryTheory in
/-- **Stacks 0E8E.** Let `C` be a site and let `U` be an object of `C`. Let `L` be a left adjoint
of the restriction functor `j_U^{-1} = J.overPullback : Sh(C) ⥤ Sh(C/U)`, i.e. let `L` be
`j_{U!}`. Then `L` reflects monomorphisms and epimorphisms, that is (Stacks 00WN), if `j_{U!}φ` is
an injection of sheaves of sets then so is `φ`, and if `j_{U!}φ` is a surjection of sheaves of
sets then so is `φ`. -/
@[stacks 0E8E "j_{U!} reflects injections and surjections of sheaves of sets."]
public theorem reflectsMonomorphisms_and_reflectsEpimorphisms {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) [HasWeakSheafify J (Type v)]
    [HasWeakSheafify (J.over U) (Type v)] [J.WEqualsLocallyBijective (Type v)]
    {L : Sheaf (J.over U) (Type v) ⥤ Sheaf J (Type v)} (adj : L ⊣ J.overPullback (Type v) U) :
    L.ReflectsMonomorphisms ∧ L.ReflectsEpimorphisms :=
  have : L.Faithful := .of_iso (OverShriek.sheafFunctorToOverForgetIsoOfAdjunction J adj)
  ⟨inferInstance, inferInstance⟩
end

end

end CategoryTheory.OverShriek
