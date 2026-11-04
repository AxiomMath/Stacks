module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.ModuliSpaceSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperImageAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget

/-!
# Properness of the target of a universal homeomorphism over a base (for Stacks 0DUZ)

Let `p : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and let
`f : 𝒳 ⟶ M` be a universal homeomorphism to an algebraic space through which `p` factors, by a
morphism `g : M ⟶ Y` of algebraic spaces. If `p` is proper and `g` is locally of finite type,
then `g` is proper. This is the argument of Stacks 0DUZ after its first sentence: there `f` is
the moduli space of the Keel–Mori theorem (Stacks 0DUT), which is a universal homeomorphism,
and local finite type of `g` is Stacks 0DUX.

The proof is the source's, run over `Y`.

* `g` is universally closed: `f ≫ g = p` is universally closed and `f` is surjective, so Stacks
  0CQK applies to the 1-morphism of algebraic stacks of `g`; Stacks 0512 and the bridge of
  Stacks 04XB (with Stacks 045A) read this as universal closedness of `g`.
* `g` is separated: `Δ_{𝒳/Y}` is proper, hence universally closed, and
  `Δ_{M/Y} ∘ f = (f ×_Y f) ∘ Δ_{𝒳/Y}` with `f ×_Y f` universally closed (Stacks 0515), so
  `Δ_{M/Y}` is universally closed by Stacks 0CQK, and `g` is separated by Stacks 04YS (the
  stacks form of Stacks 04Y0).
* `g` is quasi-compact, being universally closed (Stacks 04XW).

## Main results

* `AlgebraicGeometry.Stack.isProper_of_universalHomeomorphism_of_isProper_comp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of algebraic spaces under a proper 1-morphism, through a universal
homeomorphism, is proper when it is locally of finite type.** Let `f : 𝒳 ⟶ M` be a universal
homeomorphism (Stacks 0CI7) from an algebraic stack to an algebraic space, let
`p : 𝒳 ⟶ Y` be a proper 1-morphism (Stacks 0CL5) to an algebraic space, and let `g : M ⟶ Y` be a
morphism of algebraic spaces with `f ≫ g ≅ p`. If `g` is locally of finite type, then `g` is
proper (Stacks 03ZM).

This is the proof of Stacks 0DUZ after its appeal to Stacks 0DUX, which only uses of the moduli
map `f` that it is a universal homeomorphism. -/
theorem isProper_of_universalHomeomorphism_of_isProper_comp
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : IsAlgebraicSpace B S hS M) (hY : IsAlgebraicSpace B S hS Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M hM)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f)
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hp : AlgebraicStacks.IsProper B S hS p)
    (g : M ⟶ Y) (hfg : Nonempty (f.hom ≫ (associatedMap B S hS g).1 ≅ p.hom))
    (hg : Space.IsLocallyOfFiniteType B S hS g) :
    Space.IsProper B S hS g := by
  obtain ⟨e⟩ := hfg
  let G : algebraicSpaceStack.{u, w} B S hS M hM ⟶ algebraicSpaceStack.{u, w} B S hS Y hY :=
    Bicategory.InducedBicategory.mkHom (associatedMap B S hS g).1
  have hcomp : f ≫ G = p := Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.hom)
  have hrep : IsRepresentableByAlgebraicSpaces B S hS G.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, w} B S hS Y hY).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS M hM) G.hom
  have hfUC := universallyClosed_of_universalHomeomorphism B S hS f hf
  have hfsurj := isSurjective_of_universalHomeomorphism B S hS f hf
  -- `g` is universally closed (Stacks 0CQK, 0512, 045A).
  have hGUC : AlgebraicStacks.UniversallyClosed B S hS G :=
    AlgebraicStacks.universallyClosed_of_surjective_comp B S hS f G (hcomp ▸ hp.2.2) hfsurj
  have hucLT : (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fppf B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.precoverage.{u, u} .fpqc B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have key : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      HasRelativeProperty B S hS P G.hom hrep →
        P (ObjectProperty.homMk g : (⟨M, hM⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    fun P _ _ h => (representingMap_associatedMap B S hS M Y g) ▸
      (hasRelativeProperty_iff_prop_representingMap B S hS P G.hom hrep M Y hM hY
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)).1 h
  have hguc : Space.UniversallyClosed B S hS g :=
    key (Space.universallyClosedProperty B S hS)
      ((representable_universallyClosed_iff_closedMap_baseChange B S hS G hrep).2 hGUC)
  -- `g` is separated (Stacks 0515, 0CQK, 04YS).
  have hΔp := AlgebraicStacks.universallyClosed_relativeDiagonalAlgebraicStacks_of_isSeparated
    B S hS p hp.1
  rw [← hcomp] at hΔp
  have hΔG := AlgebraicStacks.universallyClosed_relativeDiagonal_of_comp B S hS f G hfUC hfsurj
    hΔp
  have h04XB : Stack.UniversallyClosed B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS (algebraicSpaceStack.{u, w} B S hS M hM).val
        (algebraicSpaceStack.{u, w} B S hS Y hY).val G.hom) :=
    (representable_universallyClosed_iff_closedMap_baseChange B S hS
      (relativeDiagonalAlgebraicStacks B S hS G)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS G)).2
      (fun 𝒵 k => hΔG 𝒵 k)
  have hsep : IsSeparated B S hS G.hom :=
    ((isSeparated_relativeDiagonal_tfae B S hS G hrep).out 4 1).1 h04XB
  have hsepLT : (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hgsep : Space.IsSeparated B S hS g := key (Space.separatedProperty B S hS) hsep
  -- `g` is quasi-compact (Stacks 04XW).
  exact ⟨hgsep, ⟨hg, Space.isQuasiCompact_of_universallyClosed B S hS hM hY g hguc⟩, hguc⟩

end AlgebraicGeometry.Stack

end
