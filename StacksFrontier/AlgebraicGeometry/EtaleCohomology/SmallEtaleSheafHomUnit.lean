module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue

/-!
# The internal hom out of the structure sheaf on the small étale site

Let `S` be a scheme and let `𝓖` be an `𝒪`-module on the size-bounded small étale site of `S`.
The internal hom `𝓗om_𝒪(𝒪, 𝓖)` out of the structure sheaf is `𝓖` itself: a local morphism
`𝒪|_T ⟶ 𝓖|_T` is multiplication by its value on the section `1`, and that value is an arbitrary
section of `𝓖` over `T`.

**The identification is with a universe lift of `𝓖`, not with `𝓖`.**  The sections of the
internal hom over an object are the morphisms on the localization of the site there, and those
are indexed by the objects of the small étale site, which form a `Type (u + 1)`; so
`AlgebraicGeometry.SmallEtale.sheafHom` lands in `SheafOfModules.{u + 1}` while `𝓖` is in
`SheafOfModules.{u}`.  The statement below is therefore an isomorphism of abelian sheaves with
`CategoryTheory.sheafCompose` of `AddCommGrpCat.uliftFunctor` applied to `𝓖`.  Every
unit-source internal-hom isomorphism already in the tree —
`Stacks.PresheafOfModules.InternalHom.unitInternalHomIso`,
`Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso` and
`Stacks.SheafOfModules.InternalHom.ihomUnitIso` — pins the module universe to the universe of
the coefficient rings, which the small étale site does not satisfy, so none of them applies
here and this file is not a copy of any of them.

## Main results

* `AlgebraicGeometry.SmallEtale.toSheafSheafHomUnitIso`: **`𝓗om_𝒪(𝒪, 𝓖) ≅ ULift 𝓖`** as abelian
  sheaves on the small étale site of `S`.

## Implementation notes

The content is carried by two existing declarations, and no new computation is performed.  The
sections of the internal hom out of the structure sheaf over an object `V` are read off by
`Mathlib`'s `PresheafOfModules.unitHomEquiv`, which identifies the morphisms out of the free
module of rank one on the slice site over `V` with the global sections there, followed by
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`, which identifies those global
sections with the sections of `𝓖` over `V`.  Both are available because the module universe of
`𝓖` *is* the universe of the coefficient rings; it is only the internal hom that leaves that
universe.  The composite is evaluation at `1`, that is `internalHomEval` applied to `1`, which
is visibly additive, so naturality is `internalHomEval_naturality` together with
`PresheafOfModules.unit_map_one`.

`Stacks.SheafOfModules.uliftUnitOverHomEquiv`, the universe-lift form of the same bijection, is
not used: it describes the morphisms out of `SheafOfModules.uliftForPresentation` of the free
module of rank one, which would have to be compared with the free module of rank one itself,
whereas the module universe here needs no lift on the source.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- The sections of `𝓗om_𝒪(𝒪, 𝓖)` over an object `V` of the small étale site of `S` are the
sections of `𝓖` over `V`, lifted to the universe of the former: a morphism `𝒪|_V ⟶ 𝓖|_V` goes to
its value on the section `1`.  This is `PresheafOfModules.unitHomEquiv` followed by
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`, and it is additive because
evaluation on a fixed section is. -/
private def sheafHomUnitSectionsAddEquiv (V : SmallEtale B S hS) :
    ((restrFun (commStructurePresheaf B S hS) V).obj
          (SheafOfModules.unit (structureSheaf B S hS)).val ⟶
        (restrFun (commStructurePresheaf B S hS) V).obj G.val) ≃+
      ULift.{u + 1} (G.val.obj (op V)) where
  toEquiv :=
    ((PresheafOfModules.unitHomEquiv
          ((restrFun (commStructurePresheaf B S hS) V).obj G.val)).trans
        (Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv G V)).trans Equiv.ulift.symm
  map_add' _ _ := rfl

/-- Evaluation on the section `1` commutes with the restriction maps of `𝓗om_𝒪(𝒪, 𝓖)`.  This is
`internalHomEval_naturality` with the restriction of `1` recognised as `1`. -/
private theorem internalHomEval_unit_one_naturality {X Y : (SmallEtale B S hS)ᵒᵖ} (f : X ⟶ Y)
    (α : (homPresheaf B S hS
      (SheafOfModules.unit (structureSheaf B S hS)).val G.val).obj X) :
    internalHomEval (commStructurePresheaf B S hS)
        (SheafOfModules.unit (structureSheaf B S hS)).val G.val Y
        (ConcreteCategory.hom ((homPresheaf B S hS
          (SheafOfModules.unit (structureSheaf B S hS)).val G.val).map f) α)
        (1 : (structureSheaf B S hS).obj.obj Y) =
      (G.val.map f).hom (internalHomEval (commStructurePresheaf B S hS)
        (SheafOfModules.unit (structureSheaf B S hS)).val G.val X α
        (1 : (structureSheaf B S hS).obj.obj X)) := by
  rw [← PresheafOfModules.unit_map_one (structureSheaf B S hS).obj f]
  exact internalHomEval_naturality (commStructurePresheaf B S hS)
    (SheafOfModules.unit (structureSheaf B S hS)).val G.val f α
    (1 : (structureSheaf B S hS).obj.obj X)

/-- The underlying abelian presheaf of `𝓗om_𝒪(𝒪, 𝓖)` is the universe lift of that of `𝓖`:
the component at `V` is `sheafHomUnitSectionsAddEquiv` and its naturality is
`internalHomEval_unit_one_naturality`. -/
private def presheafUnitUliftIso :
    (sheafToPresheaf (topology B S hS) AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj
          (sheafHom B S hS (SheafOfModules.unit (structureSheaf B S hS)) G)) ≅
      (sheafToPresheaf (topology B S hS) AddCommGrpCat.{u + 1}).obj
        ((CategoryTheory.sheafCompose (topology B S hS)
            AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G)) :=
  NatIso.ofComponents
    (fun X => AddEquiv.toAddCommGrpIso (sheafHomUnitSectionsAddEquiv B S hS G X.unop))
    (fun {_X _Y} f => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun α =>
      ULift.ext (internalHomEval_unit_one_naturality B S hS G f α))

/-- **The internal hom out of the structure sheaf on the small étale site of `S` is the universe
lift of the target.**  A local morphism `𝒪|_T ⟶ 𝓖|_T` is multiplication by its value on the
section `1`, so the sections of `𝓗om_𝒪(𝒪, 𝓖)` over `T` are the sections of `𝓖` over `T`; the
universe lift is there because the module universe of the internal hom is one above that of
`𝓖`, see the module docstring. -/
def toSheafSheafHomUnitIso :
    (SheafOfModules.toSheaf (structureSheaf B S hS)).obj
        (sheafHom B S hS (SheafOfModules.unit (structureSheaf B S hS)) G) ≅
      (CategoryTheory.sheafCompose (topology B S hS)
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G) :=
  (fullyFaithfulSheafToPresheaf (topology B S hS) AddCommGrpCat.{u + 1}).preimageIso
    (presheafUnitUliftIso B S hS G)

end AlgebraicGeometry.SmallEtale

end
