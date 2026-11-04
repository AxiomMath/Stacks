module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentCommaDecomposition

/-!
# The componentwise direct sum for module lower shriek, before sheafification

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `R` be a presheaf of commutative rings on its total category. Stacks 0D72
says that the restriction to simplicial degree `m` of module lower shriek from degree `n` is the
direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the module pullbacks along the transitions
`f_φ`. This file proves the presheaf-level, objectwise form of that statement.

The sections of `CategoryTheory.PresheafOfModules.pullback` over an object `U` are the colimit
of the diagram `(V, U ⟶ F V) ↦ R(U) ⊗_{R(F V)} A(V)` over the comma category
`CostructuredArrow F.op U` — this is `Stacks.PullbackColimit.pullbackObjIso`, the concrete model
for Mathlib's otherwise opaque left adjoint. For `F` the degree-`n` component inclusion and `U` a
degree-`m` object, `StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentCommaDecomposition.lean`
computes that comma category: it is the disjoint union, over the simplex maps `φ : [n] ⟶ [m]`, of
pieces each having a terminal object, namely `(u φ (V), (φ, 𝟙))`. A colimit over such a category
is the coproduct of the values at those distinguished objects, which is exactly the direct sum of
the source.

So the two inputs compose, and the composition is what is proved here. The term of the diagram at
the distinguished object attached to `φ` is `R(ι_m V) ⊗_{R(ι_n (u φ V))} A(u φ V)`, the sections
of the module pullback along `f_φ`, so the decomposition is the source's direct sum with the
source's summands, labelled as the source labels them.

## Main results

* `Stacks.Sites.ComponentModuleSumFormula.isColimitCofanPullbackDiagramComponent`: the colimit
  computing the sections of the presheaf-level module pullback along the degree-`n` component
  inclusion, evaluated at a degree-`m` object, is the coproduct over the simplex maps
  `φ : [n] ⟶ [m]` of the values of the diagram at the distinguished objects.
* `Stacks.Sites.ComponentModuleSumFormula.pullbackObjIsoCoproduct`: the same statement read as an
  isomorphism with a chosen coproduct, **the presheaf-level objectwise direct-sum formula of
  Stacks 0D72 in case (B)**.
* `Stacks.Sites.ComponentModuleSumFormula.diagramObj_componentCostructuredArrow`: the summand
  labelled `φ` is `R(ι_m V) ⊗_{R(ι_n (u φ V))} A(u φ V)`.

## Implementation notes

The comma-category decomposition is stated in
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentCommaDecomposition.lean` as the two
hypotheses of `CategoryTheory.Limits.isColimitCofanOfUniqueArrows` — a function choosing, for
each object, an index together with a morphism to the distinguished object of that index, and the
statement that such pairs are unique. Those hypotheses are stated at an arbitrary coefficient
category, so they apply verbatim to a diagram valued in `ModuleCat`; no index combinatorics is
redone here. What is new is only that the module diagram of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackColimit.lean` is indexed by that same
comma category, so the two fit together.

Everything is stated for the raw fibre inclusion `CategoryTheory.Grothendieck.ι` rather than for
`CategoryTheory.SimplicialSiteSituation.componentFunctor`, matching the spelling of the
comma-category decomposition; the two are definitionally equal.

What is **not** done here: the passage from this objectwise presheaf statement to an isomorphism
of sheaves of modules, which needs the naturality of the comparison in `V`, sheafification, and
the identification of each summand with the module pullback along the ringed transition
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom`. Case (A) of the situation is
not treated: there the comma category on the left Kan extension side does not decompose, and the
argument has to run on the right Kan extension side instead, which for modules needs a right
adjoint of module restriction that this development does not have.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ComponentModuleSumFormula

variable (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory}
  (V : C.underlying.obj (op m))
  (R : (Grothendieck C.underlying)ᵒᵖ ⥤ CommRingCat.{u})

/-- The degree-`n` object underlying the distinguished index attached to a simplex map
`φ : [n] ⟶ [m]` is `u φ (V)`. -/
theorem componentCostructuredArrow_left (φ : n ⟶ m) :
    (CocontinuousSimplicialSite.componentCostructuredArrow C V φ).left =
      op ((C.underlying.map φ.op).toFunctor.obj V) :=
  rfl

/-- The structure morphism of the distinguished index attached to a simplex map `φ : [n] ⟶ [m]`
is the cross-fibre arrow `(φ, 𝟙)`. -/
theorem componentCostructuredArrow_hom (φ : n ⟶ m) :
    (CocontinuousSimplicialSite.componentCostructuredArrow C V φ).hom =
      ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app V).op :=
  rfl

/-- The cross-fibre transition of the total presheaf of commutative rings attached to a simplex
map `φ : [n] ⟶ [m]`: the map `u_φ^* R_n ⟶ R_m` of presheaves of rings on the degree-`m`
component given by restriction along the arrows `(φ, 𝟙)`. This is the ring map
`O(φ) : f_φ^{-1}O_n ⟶ O_m` of Stacks 0D72, which in case (B) is literal whiskering because the
transition is given by a functor `C_m ⥤ C_n` and so its inverse image is restriction. -/
def ringTransition (φ : n ⟶ m) :
    (C.underlying.map φ.op).toFunctor.op ⋙ (Grothendieck.ι C.underlying (op n)).op ⋙ R ⟶
      (Grothendieck.ι C.underlying (op m)).op ⋙ R :=
  Functor.whiskerRight
    (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) R

/-- On sections over a degree-`m` object, the cross-fibre ring transition is restriction along
the arrow `(φ, 𝟙)` of the total category. -/
@[simp]
theorem ringTransition_app (φ : n ⟶ m) (W : C.underlying.obj (op m)) :
    (ringTransition C R φ).app (op W) =
      R.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app W).op :=
  rfl

variable (A : PresheafOfModules.{u}
  (((Grothendieck.ι C.underlying (op n)).op ⋙ R) ⋙ forget₂ CommRingCat RingCat))

/-- Module pullback along the transition `f_φ` of a simplex map `φ : [n] ⟶ [m]`, at the level of
presheaves of modules: restriction along the transition functor `u_φ : C_m ⥤ C_n`, followed by
extension of scalars along the cross-fibre ring transition. In case (B) the transition of topoi
has restriction for its inverse image, so this needs no Kan extension; it is
`f_φ^*G = f_φ^{-1}G ⊗_{f_φ^{-1}O_n} O_m` written out. -/
noncomputable def transitionPullbackPresheafModules (φ : n ⟶ m) :
    PresheafOfModules.{u}
        (((Grothendieck.ι C.underlying (op n)).op ⋙ R) ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u}
        (((Grothendieck.ι C.underlying (op m)).op ⋙ R) ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward₀OfCommRingCat (C.underlying.map φ.op).toFunctor
      ((Grothendieck.ι C.underlying (op n)).op ⋙ R) ⋙
    Stacks.PullbackModel.extendScalars (ringTransition C R φ)

/-- The term of the colimit diagram at the distinguished index attached to a simplex map
`φ : [n] ⟶ [m]`: the base change `R(ι_m V) ⊗_{R(ι_n (u φ V))} A(u φ V)` along the cross-fibre
arrow `(φ, 𝟙)`. These are the summands of the direct sum of Stacks 0D72. -/
theorem diagramObj_componentCostructuredArrow (φ : n ⟶ m) :
    Stacks.PullbackColimit.diagramObj (Grothendieck.ι C.underlying (op n)) R A
        (CocontinuousSimplicialSite.componentCostructuredArrow C V φ) =
      (ModuleCat.extendScalars
          (R.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app V).op).hom).obj
        (A.obj (op ((C.underlying.map φ.op).toFunctor.obj V))) :=
  rfl

/-- **The summand labelled `φ` is the module pullback along `f_φ`.** The term of the colimit
diagram at the distinguished index attached to `φ` is the value over `V` of the presheaf-level
module pullback along the transition of `φ`. This is what makes the decomposition below the
labelled direct sum of Stacks 0D72 rather than an unlabelled coproduct of base changes. -/
theorem diagramObj_componentCostructuredArrow_eq_transitionPullback (φ : n ⟶ m) :
    Stacks.PullbackColimit.diagramObj (Grothendieck.ι C.underlying (op n)) R A
        (CocontinuousSimplicialSite.componentCostructuredArrow C V φ) =
      ((transitionPullbackPresheafModules C R φ).obj A).obj (op V) :=
  rfl

/-- **Stacks 0D72, the direct-sum decomposition at the level of the colimit, in case (B).** The
colimit computing the sections over a degree-`m` object `V` of the presheaf-level module pullback
along the degree-`n` component inclusion is the coproduct, over the simplex maps `φ : [n] ⟶ [m]`,
of the values of the diagram at the distinguished indices `(u φ (V), (φ, 𝟙))`.

The injections are the colimit injections at those indices. This is
`CategoryTheory.Limits.isColimitCofanOfUniqueArrows` applied to the comma-category decomposition
of `CategoryTheory.CocontinuousSimplicialSite.componentCostructuredArrow_arrow` and
`…_subsingleton`, read at the module-valued diagram of
`Stacks.PullbackColimit.diagram` instead of at a presheaf of abelian groups. -/
noncomputable def isColimitCofanPullbackDiagramComponent :
    IsColimit (Cofan.mk
      (colimit (Stacks.PullbackColimit.diagram (Grothendieck.ι C.underlying (op n)) R A
        (op ((Grothendieck.ι C.underlying (op m)).obj V))))
      fun φ : n ⟶ m =>
        colimit.ι (Stacks.PullbackColimit.diagram (Grothendieck.ι C.underlying (op n)) R A
            (op ((Grothendieck.ι C.underlying (op m)).obj V)))
          (CocontinuousSimplicialSite.componentCostructuredArrow C V φ)) :=
  isColimitCofanOfUniqueArrows
    (Stacks.PullbackColimit.diagram (Grothendieck.ι C.underlying (op n)) R A
      (op ((Grothendieck.ι C.underlying (op m)).obj V)))
    (fun φ : n ⟶ m => CocontinuousSimplicialSite.componentCostructuredArrow C V φ)
    (CocontinuousSimplicialSite.componentCostructuredArrow_arrow C V)
    (CocontinuousSimplicialSite.componentCostructuredArrow_subsingleton C V)
    (colimit.isColimit _)

section Pullback

variable {S : (C.underlying.obj (op n))ᵒᵖ ⥤ CommRingCat.{u}}
  (α : S ⟶ (Grothendieck.ι C.underlying (op n)).op ⋙ R)
  (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))

/-- **Stacks 0D72, the objectwise direct-sum formula before sheafification, in case (B).** The
sections over a degree-`m` object `V` of the presheaf-level module pullback along the degree-`n`
component inclusion are the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the base
changes `R(ι_m V) ⊗_{R(ι_n (u φ V))} N(u φ V)` — that is, of the sections of the module pullbacks
along the transitions `f_φ`.

The left-hand side is Mathlib's `CategoryTheory.PresheafOfModules.pullback`, an abstract left
adjoint; `Stacks.PullbackColimit.pullbackObjIso` is what makes its sections accessible, and
`isColimitCofanPullbackDiagramComponent` is what decomposes them. -/
noncomputable def pullbackObjIsoCoproduct :
    ((PresheafOfModules.pullback.{u} (Stacks.PullbackColimit.toRingCatPullback α)).obj N).obj
        (op ((Grothendieck.ι C.underlying (op m)).obj V)) ≅
      ∐ fun φ : n ⟶ m =>
        Stacks.PullbackColimit.diagramObj (Grothendieck.ι C.underlying (op n)) R
          ((Stacks.PullbackModel.extendScalars α).obj N)
          (CocontinuousSimplicialSite.componentCostructuredArrow C V φ) :=
  (Stacks.PullbackColimit.pullbackObjIso α N _).trans
    ((isColimitCofanPullbackDiagramComponent C V R _).coconePointUniqueUpToIso
      (coproductIsCoproduct _))

/-- **Stacks 0D72, the objectwise direct-sum formula before sheafification, with the source's
summands, in case (B).** The sections over a degree-`m` object `V` of the presheaf-level module
pullback along the degree-`n` component inclusion are the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the sections over `V` of the module pullbacks `f_φ^*` along the transitions.

This is `pullbackObjIsoCoproduct` with each summand rewritten by
`diagramObj_componentCostructuredArrow_eq_transitionPullback`, so the summand labelled `φ` is the
one the source attaches to `φ` and the isomorphism cannot permute summands. -/
noncomputable def pullbackObjIsoCoproductTransition :
    ((PresheafOfModules.pullback.{u} (Stacks.PullbackColimit.toRingCatPullback α)).obj N).obj
        (op ((Grothendieck.ι C.underlying (op m)).obj V)) ≅
      ∐ fun φ : n ⟶ m =>
        ((transitionPullbackPresheafModules C R φ).obj
          ((Stacks.PullbackModel.extendScalars α).obj N)).obj (op V) :=
  (pullbackObjIsoCoproduct C V R α N).trans
    (Sigma.mapIso fun φ : n ⟶ m =>
      eqToIso (diagramObj_componentCostructuredArrow_eq_transitionPullback C V R
        ((Stacks.PullbackModel.extendScalars α).obj N) φ))

end Pullback

end Stacks.Sites.ComponentModuleSumFormula

end
