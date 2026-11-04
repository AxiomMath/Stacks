module

public import StacksFrontier.Homology.CompositeCollapse

/-!
# The two forms of the Leray collapse isomorphism agree

`Stacks.RightDerivedComp.objIso` and `Stacks.RightDerivedComp.objIsoOfAcyclicImage` are two
constructions of the same comparison `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)` at a `G`-acyclic object
`A`.  They differ in what is asked of the image of an injective resolution under `G`: `objIso`
asks that `G` carry injective objects to injective ones, `objIsoOfAcyclicImage` only that it
carry them to `T`-acyclic ones.  Where both hypotheses are available — as they are for a *flat*
affine morphism of algebraic spaces — the two isomorphisms are equal.

## Main results

* `Stacks.RightDerivedComp.objIso_eq_objIsoOfAcyclicImage`: the two collapse isomorphisms agree.

## Implementation notes

`Stacks.RightDerivedComp.objIso_hom_eq` pins `objIso` down by *any* comparison `φ` of `G`
applied to the injective resolution of `A` with an injective resolution of `G.obj A` preserving
the augmentation.  The acyclic form is built out of one such comparison, namely the chosen
descent `Stacks.RightDerivedComp.descOfResolution` of the identity, whose augmentation property
is `Stacks.RightDerivedComp.comp_descOfResolution`; feeding that descent to `objIso_hom_eq`
turns the one isomorphism into the other, and no homotopy-uniqueness argument is needed.

This matters because only `objIso` carries a naturality statement in the coefficient
(`Stacks.RightDerivedComp.objIso_hom_naturality`), while the acyclic form is the one used by the
collapse along an affine morphism of algebraic spaces; a development that needs naturality of
that collapse can now have it.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.RightDerivedComp

/-- **The two forms of the collapse isomorphism agree.**  For `G` additive, left exact and
preserving injective objects, and `A` a `G`-acyclic object, the collapse
`R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)` built from the injectivity of the image of an injective
resolution is the one built from its `T`-acyclicity.

Both are the identification of `R ⁿ (G ⋙ T) (A)` with `H ⁿ (T (G (I)))` for `I` an injective
resolution of `A`, followed by the inverse of an identification of the latter with
`R ⁿ T (G A)`; `Stacks.RightDerivedComp.objIso_hom_eq` says that the first form is computed by
any augmentation-preserving comparison of `G (I)` with an injective resolution of `G.obj A`, and
the comparison the second form uses — the chosen descent of the identity — is one. -/
theorem objIso_eq_objIsoOfAcyclicImage {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C] [HasInjectiveResolutions D]
    [EnoughInjectives D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
    (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T] {A : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z)) (n : ℕ) :
    objIso G (injectiveResolution A) hA T n = objIsoOfAcyclicImage G T hA hGT n := by
  have : QuasiIso (mapι G (injectiveResolution A)) :=
    quasiIso_mapι G (injectiveResolution A) hA
  refine Iso.ext ?_
  rw [objIso_hom_eq G (injectiveResolution A) hA T n (injectiveResolution (G.obj A))
    (descOfResolution (mapι G (injectiveResolution A)) (injectiveResolution (G.obj A))) ?_]
  · rfl
  · have h := comp_descOfResolution (D := D) (mapι G (injectiveResolution A))
      (injectiveResolution (G.obj A))
    have h0 := HomologicalComplex.congr_hom h 0
    rw [HomologicalComplex.comp_f, mapι_f_zero] at h0
    exact h0

end Stacks.RightDerivedComp

end
