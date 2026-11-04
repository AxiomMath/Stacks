module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.ObjectProperty.Comma
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.CategoryTheory.Sites.Descent.SmallStack
import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness

/-!
# A set-sized stack of finite-type algebraic spaces (Stacks 04UE)

The stack of finite-type algebraic spaces over a scheme `S` of a big fppf site has a
strictly full subcategory whose inclusion is fully faithful and essentially surjective and
whose restricted projection is still a stack over the big fppf site of `S`, with all fibres
set-sized.

## Main definitions and results

* `AlgebraicGeometry.essentiallySmall_bigFppfOver`: the big fppf category over `S` is
  essentially small.
* `AlgebraicGeometry.essentiallySmall_algebraicSpaces`: so is the category of algebraic
  spaces over `S`.
* `AlgebraicGeometry.exists_small_finiteTypeSpaces_stack`: **Stacks 04UE**.

## What is assumed

The source deduces Stacks 04UE from Stacks 04UD, the statement that the projection
`finiteTypeSpacesProjection` is a stack. This library has only conditions (1) and (2) of that
tag — `AlgebraicGeometry.finiteTypeSpacesProjection_isFibered` and
`AlgebraicGeometry.finiteTypeSpacesProjection_isMorSheaf` — because condition (3), effective
descent, rests on Bootstrap, Theorem 04S6, which is not available here; see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeStack.lean`, which
records the same gap. The assembled `CategoryTheory.Functor.IsStack` therefore does not
exist, and `AlgebraicGeometry.exists_small_finiteTypeSpaces_stack` carries it as an explicit
hypothesis. Nothing else is assumed: the mathematical content of Stacks 04UE is the
unconditional `CategoryTheory.Functor.IsStack.exists_small_fullSubcategory`, and the
essential smallness of the category of finite-type algebraic spaces, which are both proved
here outright.

## Implementation notes

The essential smallness of the category of algebraic spaces over `S` is the one piece of
geometry. A scheme of size below `κ` is the colimit of its affine opens, each of which is the
spectrum of a ring of cardinality at most its size; so the size-bounded schemes lie in the
closure of the spectra of bounded rings under colimits of bounded shape, and the spectra of
bounded rings are essentially small because every such ring is a quotient of one fixed
polynomial ring. The big fppf category over `S` is then essentially small as a slice of an
essentially small category, and the functor category over it is locally small.

An algebraic space over `S` is the coequalizer, in fppf sheaves of sets, of the kernel pair
of any surjective étale atlas — that is Stacks 0262, part (3),
`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale` — and both terms of that kernel
pair are representable. So the algebraic spaces lie in the closure of the essential image of
the sheafified Yoneda embedding under coequalizers, and that closure is essentially small.

Finite-type algebraic spaces are a full subcategory of a comma category of the above, hence
essentially small too, and
`CategoryTheory.Functor.IsStack.exists_small_fullSubcategory` applies.

## References

* [Stacks Project, Tag 04UE](https://stacks.math.columbia.edu/tag/04UE)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
-/

@[expose] public section

open CategoryTheory Cardinal

namespace AlgebraicGeometry

universe u

/-- The big fppf category over `S` is essentially small, being a slice of the size-bounded
category of schemes. -/
theorem essentiallySmall_bigFppfOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : EssentiallySmall.{u} (BigFppfOver B S hS) := by
  let _ : EssentiallySmall.{u} (SchemeBelow B.cutoff) := essentiallySmall_schemeBelow B.cutoff
  exact essentiallySmall_of_fully_faithful
    (Over.post (equivSmallModel.{u} B.Schemes).functor)

/-- Presheaves on an essentially small category form a locally small category. -/
private theorem locallySmall_presheaves {C : Type*} [Category.{u} C]
    [EssentiallySmall.{u} C] : LocallySmall.{u} (Cᵒᵖ ⥤ Type u) :=
  locallySmall_of_faithful (equivSmallModel.{u} C).op.congrLeft.functor

/-- The category of algebraic spaces over `S` is essentially small: every algebraic space is
a coequalizer of representables, by Stacks 0262, part (3). -/
theorem essentiallySmall_algebraicSpaces (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    EssentiallySmall.{u} (ObjectProperty.FullSubcategory (IsAlgebraicSpace B S hS)) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let _ : EssentiallySmall.{u} C := essentiallySmall_bigFppfOver B S hS
  let _ : LocallySmall.{u} (Cᵒᵖ ⥤ Type u) := locallySmall_presheaves
  let _ : LocallySmall.{u} (Sheaf J (Type u)) :=
    locallySmall_of_faithful (sheafToPresheaf J (Type u))
  let _ : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite J (Type u)
  let G := yoneda ⋙ presheafToSheaf J (Type u)
  let Q := G.essImage.colimitsClosure (fun _ : Unit => Limits.WalkingParallelPair)
  let A : ObjectProperty (Cᵒᵖ ⥤ Type u) := IsAlgebraicSpace B S hS
  let F : A.FullSubcategory ⥤ Sheaf J (Type u) :=
    ObjectProperty.ιOfLE (show A ≤ Presheaf.IsSheaf J from fun _ h => h.isSheaf)
  have hF : ∀ X, Q (F.obj X) := by
    intro X
    obtain ⟨U, f, hsurj, hetale⟩ := X.property.exists_atlas
    let hr := hsurj.rep
    obtain ⟨hRsh, hUsh, hc⟩ := Space.isCoequalizer_of_surjectiveEtale B S hS
      f (hr.fst' f) (hr.snd f) (hr.isPullback' f) X.property hsurj hetale
    apply Q.prop_of_isColimit hc.some
    intro j
    cases j <;>
      apply G.essImage.le_colimitsClosure (fun _ : Unit => Limits.WalkingParallelPair)
    · exact ⟨hr.pullback f, ⟨(sheafificationIso
        (⟨yoneda.obj (hr.pullback f), hRsh⟩ : Sheaf J (Type u))).symm⟩⟩
    · exact ⟨U, ⟨(sheafificationIso (⟨yoneda.obj U, hUsh⟩ : Sheaf J (Type u))).symm⟩⟩
  exact essentiallySmall_of_fully_faithful (Q.lift F hF)

/-- **Stacks 04UE.** Granted that the projection from finite-type algebraic spaces over
varying base schemes is a stack over the big fppf site of `S` — Stacks 04UD, whose condition
(3) this library does not have — there is a strictly full subcategory of it with set-sized
fibres whose inclusion is essentially surjective and whose restricted projection is still a
stack. -/
@[stacks 04UE "the small stack of finite-type algebraic spaces"]
theorem exists_small_finiteTypeSpaces_stack (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (hp : (finiteTypeSpacesProjection B S hS).IsStack (BigFppfOver.topology B S hS)) :
    ∃ P : ObjectProperty (FiniteTypeSpaces B S hS),
      (∀ T : BigFppfOver B S hS,
        Small.{u} ((P.ι ⋙ finiteTypeSpacesProjection B S hS).Fiber T)) ∧
        P.ι.EssSurj ∧
        (P.ι ⋙ finiteTypeSpacesProjection B S hS).IsStack
          (BigFppfOver.topology B S hS) := by
  let _ : EssentiallySmall.{u} (FiniteTypeSpaces B S hS) :=
    have : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
    have : LocallySmall.{u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := locallySmall_presheaves
    have : EssentiallySmall.{u}
        (ObjectProperty.FullSubcategory (IsAlgebraicSpace B S hS)) :=
      essentiallySmall_algebraicSpaces B S hS
    have : ObjectProperty.EssentiallySmall.{u} (isFiniteTypeSpace B S hS) :=
      ObjectProperty.EssentiallySmall.of_le (Q := ObjectProperty.comma _ _ ⊤ ⊤)
        (fun _ _ => ⟨trivial, trivial⟩)
    inferInstance
  let _ : LocallySmall.{u} (BigFppfOver B S hS) := inferInstance
  exact Functor.IsStack.exists_small_fullSubcategory _ _ hp

end AlgebraicGeometry

end
