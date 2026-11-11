module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Topology.Sheaves.LocalPredicate
public import StacksFrontier.Topology.Sheaves.Sheaf.ContinuousFunctions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0092 — the `f`-map of sheaves of continuous real-valued functions

For a topological space `X`, let `C⁰_X` be the sheaf `U ↦ C(U, ℝ)` of continuous
real-valued functions, viewed as a sheaf of commutative `ℝ`-algebras
(`presheafC0`). Tag 0092 is the example observing that a continuous map
`f : X → Y` induces a canonical `f`-map `f^♯ : C⁰_Y ⟶ f_*C⁰_X`, given over an open
`V ⊆ Y` by precomposition with `f|_{f^{-1}V} : f^{-1}V → V`, that is `h ↦ h ∘ f`. This is
`fSharp`, which carries the tag; `fSharp_app_apply` and `fSharp_app_eq_compRight` record
its value on sections pointwise and as an algebra map.

That `C⁰_X` really is a sheaf comes from the sheaf of continuous maps:
`presheafC0_forget_iso_presheafToTop` identifies its underlying type-valued presheaf with
Mathlib's presheaf of continuous maps to `ℝ`, and `presheafC0_forget_isSheaf` transports the
sheaf condition across that isomorphism. This is the underlying-set half of the
sheaf-of-rings example, Stacks 0091.
-/

@[expose] public section

open TopologicalSpace CategoryTheory Opposite TopCat

/-- Restriction of a continuous map `f : X ⟶ Y` to a continuous map between
preimage of `V` and `V`. -/
@[ega "I 2.2.8" "partial"]
noncomputable def restrictedContMap {X Y : TopCat.{0}} (f : X ⟶ Y) (V : Opens Y) :
    C(((Opens.map f).obj V).carrier, V) :=
  ⟨fun x => ⟨f x.1, x.2⟩, by fun_prop⟩

/-- The natural $f$-map $f^\sharp : \mathcal{C}^0_Y \to f_*\mathcal{C}^0_X$
associated to a continuous map $f : X \to Y$ between topological spaces, given on
sections over an open $V \subseteq Y$ by precomposition with $f$:
$h \mapsto h \circ f|_{f^{-1}(V)}$. This is the morphism asserted to exist in the
Stacks example. -/
@[stacks 0092 "continuous functions"]
noncomputable def fSharp {X Y : TopCat.{0}} (f : X ⟶ Y) :
    presheafC0 Y ⟶
      (TopCat.Presheaf.pushforward (CommAlgCat ℝ) f).obj
        (presheafC0 X) where
  app V := CommAlgCat.ofHom <|
    ContinuousMap.compRightAlgHom ℝ ℝ (restrictedContMap f V.unop)
  naturality := by
    intros
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro h
    rfl

/-- The action of `fSharp f` on a section, pointwise: `h ↦ h ∘ f|_{f⁻¹V}`. -/
theorem fSharp_app_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (V : (Opens Y)ᵒᵖ)
    (h : C(V.unop, ℝ))
    (x : ((Opens.map f).obj V.unop).carrier) :
    (show C(((Opens.map f).obj V.unop).carrier, ℝ) from
      ((fSharp f).app V).hom h) x = h ⟨f x.1, x.2⟩ := rfl

/-- The action of `fSharp f` on sections is precomposition with the restricted
continuous map, packaged as `ContinuousMap.compRightAlgHom`. -/
theorem fSharp_app_eq_compRight {X Y : TopCat.{0}} (f : X ⟶ Y) (V : (Opens Y)ᵒᵖ) :
    ((fSharp f).app V).hom =
      ContinuousMap.compRightAlgHom ℝ ℝ (restrictedContMap f V.unop) := rfl

