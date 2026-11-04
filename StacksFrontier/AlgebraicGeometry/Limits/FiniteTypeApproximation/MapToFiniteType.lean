module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma

/-!
# Morphisms from a limit into a scheme of finite type over the integers

Let `T = lim T_i` be the limit of an inverse system of schemes over a directed set, with affine
transition morphisms and with every stage of finite type over the integers, and let `Y` be a
scheme of finite type over the integers.  Then every morphism `T ⟶ Y` factors through some
stage, and two morphisms out of stages that induce the same morphism on `T` already agree at
some later stage.  In other words, the canonical map
`colim Hom(T_i, Y) ⟶ Hom(lim T_i, Y)` is bijective.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_terminal_from`: a scheme locally of finite type
  over the integers is locally of finite presentation over the integers.
* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_isLimit`: a morphism out of the limit
  factors through a stage.
* `AlgebraicGeometry.Scheme.exists_map_comp_eq_of_isLimit`: two morphisms out of stages inducing
  the same morphism on the limit agree at a later stage.

## Implementation notes

Both statements are the case of a terminal base of the corresponding results of
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`, namely
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` and
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`, which together
are the implication (1) ⇒ (3) of [Stacks, Tag 01ZC].  Over a terminal base the structure
morphisms carry no information, so the hypotheses expressing that the diagram and `Y` live over
the base become automatic: the transformation to the constant diagram at the terminal scheme is
the unique one, and all the required commutativities hold by `CategoryTheory.Limits.terminal`'s
universal property.

That the stages are quasi-compact and quasi-separated as schemes, which both results require, is
not an extra assumption either: a quasi-compact scheme of finite type over the integers is
Noetherian, by `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from`.  The same
Noetherianness of the terminal scheme is what upgrades finite type to finite presentation, as
required by the factorization half.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The terminal scheme `Spec (ULift ℤ)` is locally Noetherian. -/
instance isLocallyNoetherian_terminal : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).symm
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian e.hom

/-- A scheme locally of finite type over the integers is locally of finite presentation over the
integers, the integers being Noetherian. -/
lemma locallyOfFinitePresentation_terminal_from (Y : Scheme.{u})
    [LocallyOfFiniteType (terminal.from Y)] :
    LocallyOfFinitePresentation (terminal.from Y) := by
  have := isLocallyNoetherian_terminal.{u}
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

namespace Scheme

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵈ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (D.map v)]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
  [∀ i, QuasiCompact (terminal.from (D.obj i))]
  (c : Cone D) (hc : IsLimit c) (Y : Scheme.{u})

/-- The unique transformation from an inverse system of schemes to the constant system at the
terminal scheme. -/
private noncomputable def toConstTerminal :
    D ⟶ (Functor.const Iᵒᵈ).obj (⊤_ Scheme.{u}) where
  app _ := terminal.from _
  naturality _ _ _ := terminal.hom_ext _ _

include hc in
/-- **A morphism from a limit of schemes of finite type over the integers into a scheme of
finite type over the integers factors through a stage.**  The transition morphisms of the
inverse system are assumed affine. -/
theorem exists_π_app_comp_eq_of_isLimit [LocallyOfFiniteType (terminal.from Y)]
    [QuasiCompact (terminal.from Y)] (g : c.pt ⟶ Y) :
    ∃ (i : Iᵒᵈ) (h : D.obj i ⟶ Y), c.π.app i ≫ h = g := by
  have hN : ∀ i, IsNoetherian (D.obj i) := fun i ↦
    isNoetherian_of_locallyOfFiniteType_terminal_from _
  have hcpt : ∀ i, CompactSpace (D.obj i) := fun i ↦
    (compactSpace_iff_quasiCompact _).mpr inferInstance
  have hqs : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i ↦ inferInstance
  have hfp : LocallyOfFinitePresentation (terminal.from Y) :=
    locallyOfFinitePresentation_terminal_from Y
  obtain ⟨i, h, hh, -⟩ := exists_π_app_comp_eq_of_locallyOfFinitePresentation D
    (toConstTerminal D) (terminal.from Y) c hc g (by ext _; exact terminal.hom_ext _ _)
  exact ⟨i, h, hh⟩

include hc in
/-- **Two morphisms into a scheme of finite type over the integers from stages of a limit of
schemes of finite type over the integers which induce the same morphism on the limit agree at a
later stage.**  The transition morphisms of the inverse system are assumed affine. -/
theorem exists_map_comp_eq_of_isLimit [LocallyOfFiniteType (terminal.from Y)]
    {i j : Iᵒᵈ} (a : D.obj i ⟶ Y) (b : D.obj j ⟶ Y)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : Iᵒᵈ) (u : k ⟶ i) (v : k ⟶ j), D.map u ≫ a = D.map v ≫ b := by
  have hN : ∀ i, IsNoetherian (D.obj i) := fun i ↦
    isNoetherian_of_locallyOfFiniteType_terminal_from _
  have hcpt : ∀ i, CompactSpace (D.obj i) := fun i ↦
    (compactSpace_iff_quasiCompact _).mpr inferInstance
  have hqs : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i ↦ inferInstance
  exact exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType D (toConstTerminal D)
    (terminal.from Y) c hc a (terminal.hom_ext _ _) b (terminal.hom_ext _ _) hab

end Scheme

end AlgebraicGeometry

end
