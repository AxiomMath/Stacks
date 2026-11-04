module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks tag 008I — Canonical isomorphism of pullback functor compositions

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be continuous maps of topological spaces.

(1) There is a canonical natural isomorphism of presheaf pullback functors
    `(g ∘ f)_p ≅ f_p ∘ g_p`.

(2) There is a canonical natural isomorphism of sheaf pullback functors
    `(g ∘ f)⁻¹ ≅ f⁻¹ ∘ g⁻¹`.

In both cases the isomorphism is the canonical one obtained from uniqueness
of left adjoints, given that the corresponding pushforwards `(g ∘ f)_*` and
`g_* ∘ f_*` are (definitionally) equal as functors (Stacks tag 008E).

In the categorical convention of Mathlib, `f ≫ g` is the composition
"first `f`, then `g`" (corresponding to the topological composition
`g ∘ f : X → Z`).  Hence pushforward along `f ≫ g` corresponds to `(g ∘ f)_*`,
while `pullback g ⋙ pullback f` corresponds to `f_p ∘ g_p`
(resp. `f⁻¹ ∘ g⁻¹`).
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace


variable {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks tag 008E (presheaf version), as a natural isomorphism.**
The presheaf pushforward of the composition `f ≫ g` is naturally isomorphic
to the composite `pushforward f ⋙ pushforward g`.  This is the categorical
incarnation of the identity `(g ∘ f)_* = g_* ∘ f_*` of pushforward functors on
presheaves. -/
@[ega "0 3.4.3"]
noncomputable def presheafPushforwardCompIso
    (C : Type*) [Category C] :
    TopCat.Presheaf.pushforward C (f ≫ g) ≅
      TopCat.Presheaf.pushforward C f ⋙ TopCat.Presheaf.pushforward C g :=
  NatIso.ofComponents
    (fun ℱ => TopCat.Presheaf.Pushforward.comp f g ℱ)
    (by
      intro ℱ 𝒢 α
      ext U
      simp [TopCat.Presheaf.Pushforward.comp_hom_app])

/-- **Stacks tag 008E (sheaf version), as a natural isomorphism.**
The sheaf pushforward of the composition `f ≫ g` is naturally isomorphic
to the composite `pushforward f ⋙ pushforward g`.  This is the categorical
incarnation of the identity `(g ∘ f)_* = g_* ∘ f_*` of pushforward functors on
sheaves.  In Mathlib this is in fact a definitional equality, so the
isomorphism is the identity. -/
@[sga "4 IV 4.1.1" "partial"]
noncomputable def sheafPushforwardCompIso
    (C : Type*) [Category C] :
    TopCat.Sheaf.pushforward C (f ≫ g) ≅
      TopCat.Sheaf.pushforward C f ⋙ TopCat.Sheaf.pushforward C g :=
  Iso.refl _

/-- **Stacks tag 008I, part (1): Composition of presheaf pullbacks.**

For continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z` of topological spaces, the
presheaf pullback along the composition `f ≫ g` is canonically naturally
isomorphic to the composition `pullback g ⋙ pullback f` (i.e., `f_p ∘ g_p` in
the informal notation, where `f_p` and `g_p` denote presheaf pullback).

The isomorphism is the canonical one obtained from uniqueness of left
adjoints: `pullback (f ≫ g)` is a left adjoint of `pushforward (f ≫ g)`,
while `pullback g ⋙ pullback f` is a left adjoint of
`pushforward f ⋙ pushforward g`, and these two right adjoints are equal
(Stacks tag 008E, captured by `presheafPushforwardCompIso`). -/
@[stacks 008I "(1)", sga "4 VI 7.1.3" "special case"]
noncomputable def presheafPullbackCompIso
    (C : Type*) [Category C] [Limits.HasColimits C] :
    TopCat.Presheaf.pullback C (f ≫ g) ≅
      TopCat.Presheaf.pullback C g ⋙ TopCat.Presheaf.pullback C f :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction C (f ≫ g)).leftAdjointUniq
    (((TopCat.Presheaf.pullbackPushforwardAdjunction C g).comp
      (TopCat.Presheaf.pullbackPushforwardAdjunction C f)).ofNatIsoRight
        (presheafPushforwardCompIso f g C).symm)

/-- Correctness of `presheafPullbackCompIso`: it is the natural isomorphism
induced by uniqueness of left adjoints, i.e. compatible with the adjunctions
`pullbackPushforwardAdjunction`. -/
theorem presheafPullbackCompIso_compat
    (C : Type*) [Category C] [Limits.HasColimits C] :
    presheafPullbackCompIso f g C =
      (TopCat.Presheaf.pullbackPushforwardAdjunction C (f ≫ g)).leftAdjointUniq
        (((TopCat.Presheaf.pullbackPushforwardAdjunction C g).comp
          (TopCat.Presheaf.pullbackPushforwardAdjunction C f)).ofNatIsoRight
            (presheafPushforwardCompIso f g C).symm) := rfl

/-- **Stacks tag 008I, part (2): Composition of sheaf pullbacks.**

For continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z` of topological spaces, the
sheaf pullback along the composition `f ≫ g` is canonically naturally
isomorphic to the composition `pullback g ⋙ pullback f` (i.e., `f⁻¹ ∘ g⁻¹` in
the informal notation, where `f⁻¹` and `g⁻¹` denote sheaf pullback).

The isomorphism is again the canonical one obtained from uniqueness of left
adjoints, this time using `TopCat.Sheaf.pullbackPushforwardAdjunction` and
`sheafPushforwardCompIso`. -/
@[stacks 008I "(2)", ega "0 3.5.5" "partial", sga "4 VI 7.1.3" "special case"]
noncomputable def sheafPullbackCompIso
    (A : Type*) [Category A]
    {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y : A, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA]
    [Limits.HasColimits A] [Limits.HasLimits A]
    [Limits.PreservesLimits (CategoryTheory.forget A)]
    [Limits.PreservesFilteredColimits (CategoryTheory.forget A)]
    [(CategoryTheory.forget A).ReflectsIsomorphisms] :
    TopCat.Sheaf.pullback A (f ≫ g) ≅
      TopCat.Sheaf.pullback A g ⋙ TopCat.Sheaf.pullback A f :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction A (f ≫ g)).leftAdjointUniq
    (((TopCat.Sheaf.pullbackPushforwardAdjunction A g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction A f)).ofNatIsoRight
        (sheafPushforwardCompIso f g A).symm)

/-- Correctness of `sheafPullbackCompIso`: it is the natural isomorphism
induced by uniqueness of left adjoints, compatible with the adjunctions
`pullbackPushforwardAdjunction`. -/
theorem sheafPullbackCompIso_compat
    (A : Type*) [Category A]
    {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y : A, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA]
    [Limits.HasColimits A] [Limits.HasLimits A]
    [Limits.PreservesLimits (CategoryTheory.forget A)]
    [Limits.PreservesFilteredColimits (CategoryTheory.forget A)]
    [(CategoryTheory.forget A).ReflectsIsomorphisms] :
    sheafPullbackCompIso f g A =
      (TopCat.Sheaf.pullbackPushforwardAdjunction A (f ≫ g)).leftAdjointUniq
        (((TopCat.Sheaf.pullbackPushforwardAdjunction A g).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction A f)).ofNatIsoRight
            (sheafPushforwardCompIso f g A).symm) := rfl
