module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineDiagonalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineSchemeStackMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The fourfold reduction of Stacks 076Z to the affine case

Let `M` be a rule satisfying hypotheses (1), (2) and (4) of **Stacks 076Z** and let
`f : 𝒲 ⟶ (Sch/X)_fppf` be a quasi-compact quasi-separated 1-morphism into the stack of an affine
scheme. The source's proof improves the source of `f` four times by the Čech step of
**Stacks 072G**, along a smooth surjective chart by an affine scheme, until the terms of the Čech
nerve are representable by affine schemes and hypothesis (4) applies. This file runs that
induction, measuring the source not by the kind of object representing it (stack, algebraic
space, scheme, separated scheme, affine scheme) but by how affine its diagonals are; that is the
same induction, one level per diagonal.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_affineChart`: **Stacks 04YC** in the form the
  Čech step consumes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineRepresentable_cechTerm`: the terms of the
  relative Čech nerve of an affine chart by an affine scheme are representable by affine schemes.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_hasAffineDiagonal`: the case of
  a quasi-compact source over an affine scheme with affine relative diagonal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **Stacks 04YC, in the form of the Čech step.** A quasi-compact algebraic stack has a
surjective smooth 1-morphism from the stack of an affine scheme, representable by algebraic
spaces. -/
theorem exists_affineChart (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : IsQuasiCompactStack.{u, t} B S hS 𝒳.val 𝒳.property) :
    ∃ (U : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (c : schemeStack.{u, t} B S hS U ⟶ 𝒳),
      IsRepresentableByAlgebraicSpaces B S hS c.hom.hom ∧ Stack.IsSurjective B S hS c ∧
        IsSmooth B S hS c := by
  obtain ⟨U, hU, c, hsurj, hrep, hsm⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, t} B S hS 𝒳).1 h𝒳
  exact ⟨U, hU, c, hrep, hsurj,
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, t, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep hsm⟩

/-- The stack of an affine scheme of the site is representable by an affine scheme. -/
theorem isAffineRepresentable_schemeStack_of_isAffine {X : BigFppfOver B S hS}
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X)) :
    IsAffineRepresentable B S hS (schemeStack.{u, t} B S hS X) :=
  ⟨X, hX, ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩

/-- Representability by an affine scheme is invariant under a 1-morphism whose functor is an
equivalence. -/
theorem isAffineRepresentable_iff_of_isEquivalence {𝒜 𝒦 : AlgebraicStacks.{u, t} B S hS}
    (e : 𝒜 ⟶ 𝒦) (he : (CatFiberedInGroupoids.homFunctor e.hom).IsEquivalence) :
    IsAffineRepresentable B S hS 𝒜 ↔ IsAffineRepresentable B S hS 𝒦 := by
  obtain ⟨E⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒜.val.isFiberedInGroupoids 𝒦.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor e.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p e.hom) he
  constructor <;> rintro ⟨A, hA, ⟨EA⟩⟩
  · exact ⟨A, hA, ⟨E.symm.trans EA⟩⟩
  · exact ⟨A, hA, ⟨E.trans EA⟩⟩

/-- **The terms of the relative Čech nerve of an affine chart by a stack representable by an
affine scheme are representable by affine schemes.** In degree `0` the term is equivalent to the
chart; in degree `n + 1` it is equivalent to `𝒰 ×_𝒳 𝒰ₙ`, whose projection to `𝒰ₙ` is a base
change of the chart, hence affine (**Stacks 0CHR**), so it is representable by an affine scheme
when `𝒰ₙ` is. -/
theorem isAffineRepresentable_cechTerm {𝒰 𝒳 : AlgebraicStacks.{u, t} B S hS} (c : 𝒰 ⟶ 𝒳)
    (h𝒰 : IsAffineRepresentable B S hS 𝒰) (hc : IsAffineHom B S hS (strictHom B S hS c))
    (n : ℕ) : IsAffineRepresentable B S hS (cechTerm B S hS c n) := by
  induction n with
  | zero =>
    exact (isAffineRepresentable_iff_of_isEquivalence B S hS (cechSingleHom B S hS c)
      (isEquivalence_cechTermSingle B S hS c)).1 h𝒰
  | succ n ih =>
    have hsnd : IsAffineHom B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS (strictHom B S hS c)
          (cechProjection B S hS c n)).snd :=
      isAffineHom_snd_of_isTwoFibreProduct B S hS _
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _) hc
    exact (isAffineRepresentable_iff_of_isEquivalence B S hS (cechPrependHom B S hS c n)
      (Stacks.RelativeCech.isEquivalence_fibreProductToNerve _ _ n)).1
      (isAffineRepresentable_of_isAffineHom B S hS ih _ hsnd)

/-- Affine diagonal passes from a 1-morphism to its strict presentation. -/
theorem hasAffineDiagonal_strictHom {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : HasAffineDiagonal B S hS f) : HasAffineDiagonal B S hS (strictHom B S hS f) :=
  hasAffineDiagonal_of_equivalence B S hS f (strictHom B S hS f)
    (strictSourceEquiv B S hS f).hom.hom
    (algStackHomHomIso B S hS (Iso.refl (strictSourceEquiv B S hS f ≫ f)))
    (inferInstanceAs (𝟭 _).IsEquivalence) hf

/-- **A chart by a stack representable by an affine scheme into a source with affine diagonal over
an affine scheme is affine**, read on the strict presentations: **Stacks 0GQE**, the composite to
the affine scheme being a 1-morphism between stacks representable by affine schemes. -/
theorem isAffineHom_strictHom_strictChart {𝒰 𝒲 : AlgebraicStacks.{u, t} B S hS}
    {X : BigFppfOver B S hS} (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (c : 𝒰 ⟶ 𝒲) (f : 𝒲 ⟶ schemeStack.{u, t} B S hS X) (h𝒰 : IsAffineRepresentable B S hS 𝒰)
    (hf : HasAffineDiagonal B S hS f) :
    IsAffineHom B S hS (strictHom B S hS (StackEtaleModuleRule.strictChart B S hS c f)) := by
  have h𝒰' : IsAffineRepresentable B S hS
      (strictSource B S hS (StackEtaleModuleRule.strictChart B S hS c f)) :=
    (isAffineRepresentable_iff_of_isEquivalence B S hS
      (strictSourceEquiv B S hS (StackEtaleModuleRule.strictChart B S hS c f))
      (inferInstanceAs (𝟭 _).IsEquivalence)).2 h𝒰
  exact isAffineHom_of_comp_of_isAffineHom_relativeDiagonal B S hS _ _ (strictHom B S hS f)
    (Iso.refl _) (isAffineHom_of_isAffineRepresentable B S hS h𝒰'
      (isAffineRepresentable_schemeStack_of_isAffine B S hS hX) _)
    (hasAffineDiagonal_strictHom B S hS f hf)

end AlgebraicStacks

namespace StackEtaleModuleRule

/-- **The last step of the reduction of Stacks 076Z.** Let `M` satisfy hypotheses (1), (2) and (4)
of **Stacks 076Z** and let `f : 𝒲 ⟶ (Sch/X)_fppf` be a 1-morphism into the stack of an affine
scheme, from a quasi-compact source, with affine relative diagonal. Then the higher direct images
along `f` carry `M` into `M`.

A smooth surjective chart `c` of `𝒲` by an affine scheme (**Stacks 04YC**) is affine
(**Stacks 0GQE**), so the terms of its relative Čech nerve are representable by affine schemes;
hypothesis (4) and
`AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_isAffineRepresentable` treat each
composite to `(Sch/X)_fppf`, and the Čech step concludes. -/
theorem preservedBy_of_hasAffineDiagonal (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (haff : PreservesHigherDirectImagesOfAffine.{u, t} B S hS M)
    {𝒲 : AlgebraicStacks.{u, t} B S hS} {X : BigFppfOver B S hS}
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (f : 𝒲 ⟶ schemeStack.{u, t} B S hS X)
    (h𝒲 : IsQuasiCompactStack.{u, t} B S hS 𝒲.val 𝒲.property)
    (hf : AlgebraicStacks.HasAffineDiagonal B S hS f) (i : ℕ) : PreservedBy B S hS M f i := by
  obtain ⟨U, hU, c, hrep, hsurj, hsm⟩ := AlgebraicStacks.exists_affineChart B S hS 𝒲 h𝒲
  have hU' := AlgebraicStacks.isAffineRepresentable_schemeStack_of_isAffine B S hS hU
  refine preservedBy_of_cechTerms B S hS c f M hserre hpull hrep hsurj hsm (fun n j => ?_) i
  exact preservedBy_of_isAffineRepresentable B S hS M hserre hpull haff
    (AlgebraicStacks.isAffineRepresentable_cechTerm B S hS _ hU'
      (AlgebraicStacks.isAffineHom_strictHom_strictChart B S hS hX c f hU' hf) n) hX _ j

end StackEtaleModuleRule

end AlgebraicGeometry.Stack

end
