module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKInjectives
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKRestrictDatum
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ContinuousGlobalSections

/-!
# Global sections across the restriction of the situation `U/T`

Let `(U', T', δ')` be an object of `Cris(X'/S')` and `W` an open of `T'`.  The remark
[Stacks, Tag 07MJ] attaches to `(U', T', δ')` the crystalline situation `U/T`, and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKRestrictDatum.lean` compares the
situation attached to `(U', T', δ')|_W` with `U/T` restricted to the open `g⁻¹W` of
`T = S ×_{S'} T'` and the open `V` of `U` above it:

`Cris((U/T)|_{g⁻¹W, V}) ≌ Cris(U_W/T_W)`,

the equivalence `...pullbackSituationRestrictEquivalence` being change of divided power base,
[Stacks, Tag 07IC], along the two comparison isomorphisms.  That is an equivalence of *sites*;
this file identifies the two **global sections functors** across it.

## What makes the identification canonical

Change of divided power base along a pair of isomorphisms is an equivalence, hence a right
adjoint, hence **final**, and restriction of global sections along a final continuous functor of
sites is invertible — `Stacks.Sites.globalSectionsAlongContinuousIso` of
`StacksFrontier/CategoryTheory/Sites/GlobalSections/ContinuousGlobalSections.lean`, which is
`Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal` with the map named.  Naming the map is the
point: the isomorphism below is *restriction of sections*, pinned down by
`Stacks.Sites.globalSectionsAlongContinuousApp_comp_ΓRes` — a global section of a sheaf on
`Cris(U_W/T_W)`, restricted and then evaluated at an object `B` of `Cris((U/T)|_{g⁻¹W, V})`, is
its value at the transported object.  Neither site need have a terminal object, and neither does
have one.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `pullbackSituationRestrictAbelianRestriction` — restriction of abelian sheaves along
  `...pullbackSituationRestrictEquivalence`.

## Main results

* `smallChangeBaseGlobalSectionsIso` — **change of divided power base along a pair of
  isomorphisms does not change global sections**: `Γ(Cris(X'/S'), -) ≅ g⁻¹ ⋙ Γ(Cris(X/S), -)`.
* `pullbackSituationRestrictGlobalSectionsIso` — **the two global sections functors agree across
  the restriction of `U/T`**: `Γ(Cris(U_W/T_W), -) ≅ g⁻¹ ⋙ Γ(Cris((U/T)|_{g⁻¹W, V}), -)`.  This
  is the identification that
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKBaseCase.lean` records as
  missing for the base case of the displayed equation (07MK) of [Stacks, Tag 07MJ].

## What is and is not proved

(07MK) is **not** proved and no `@[stacks]` attribute is placed.  What is proved is an
identification of two global sections functors; nothing here is an assertion of the source.

In particular the base case of (07MK) is still **not** natural in the open `W`.  This file
supplies the last *ingredient* the module documentation of `Formula07MKBaseCase.lean` names —
the two sides of that base case at `W` are now known to be the same group — but it does not
assemble the resulting family into a morphism of sheaves on the small Zariski site of `T'`: that
needs the isomorphisms above to commute with the restriction maps of `W ↦ (U', T', δ')|_W` and
`W ↦ g⁻¹W`, which is a compatibility between two *different* opens and is not stated here.  Nor
does anything here connect the global sections of `Cris((U/T)|_{g⁻¹W, V})` with the sections of
`u_{U/T, *}F_U` over `V`, which is the other half of the right-hand side at `W`; the site-level
input for that is `...smallExtendEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SituationRestrict.lean`.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open DividedPowerScheme

/-! ### Change of divided power base along a pair of isomorphisms -/

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ closedFiberMap f = g ≫ S'.toClosedFiber) [IsIso f] [IsIso g]

/-- **Change of divided power base along a pair of isomorphisms does not change global
sections**:

`Γ(Cris(X'/S'), -) ≅ g⁻¹ ⋙ Γ(Cris(X/S), -)`,

naturally in the abelian sheaf on `Cris(X'/S')`.  Change of base along a pair of isomorphisms is
an equivalence of the two small crystalline sites,
`Crystalline.GlobalCrystallineSituation.smallChangeBase_isEquivalence_of_isIso`, hence a right
adjoint, hence final; and restriction of global sections along a final continuous functor of
sites is invertible, `Stacks.Sites.globalSectionsAlongContinuousIso`.

The isomorphism is the restriction map itself, so by
`Stacks.Sites.globalSectionsAlongContinuousApp_comp_ΓRes` it carries a global section to the
family of its values at the transported objects. -/
def smallChangeBaseGlobalSectionsIso :
    globalSections S' ≅ smallChangeBaseAbelianRestriction S S' f g h ⋙ globalSections S :=
  Stacks.Sites.globalSectionsAlongContinuousIso (smallChangeBase S S' f g h) (smallTopology S)
    (smallTopology S') AddCommGrpCat.{u + 1}

/-- **The isomorphism is restriction of sections**: a global section of `G`, carried across and
then evaluated at an object `B` of `Cris(X/S)`, is the value of `G` at the object `B` is sent
to. -/
@[reassoc]
theorem smallChangeBaseGlobalSectionsIso_hom_app_comp_ΓRes
    (G : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (B : (CrystallineThickening S)ᵒᵖ) :
    (smallChangeBaseGlobalSectionsIso S S' f g h).hom.app G ≫
        ((smallChangeBaseAbelianRestriction S S' f g h).obj G).ΓRes B =
      G.ΓRes ((smallChangeBase S S' f g h).op.obj B) :=
  Stacks.Sites.globalSectionsAlongContinuousIso_hom_app_comp_ΓRes
    (smallChangeBase S S' f g h) (smallTopology S) (smallTopology S') AddCommGrpCat.{u + 1} G B

end ChangeBase

/-! ### The restriction of the situation `U/T` to an open of `T'` -/

section Restrict

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (A' : CrystallineThickening S') (W : A'.obj.thickening.target.scheme.Opens)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The comparison `(S ×_{S'} T')|_{g⁻¹W} ≅ S ×_{S'} (T'|_W)`, at the type it has as the
morphism of divided power bases between the two situations.**  As in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKRestrictDatum.lean`,
`...pullbackSituationRestrict` and `...pullbackSituation` are plain `def`s, so their fields do
not reduce at the transparency instance search runs at and `IsIso` at the type of
`...pullbackBaseRestrictOpenIso` is not found at the type change of base wants.  Naming the
morphism at that type and attaching the instance to the name is the remedy of
`...restrictSι`. -/
def pullbackSituationRestrictBaseHom :
    (pullbackSituationRestrict S S' fS fX A' W hf).S ⟶
      (pullbackSituation S S' fS fX hf (A'.restrictOpen W)).S :=
  (pullbackBaseRestrictOpenIso S S' fS A' W).hom

/-- The morphism `pullbackSituationRestrictBaseHom` is an isomorphism. -/
instance isIso_pullbackSituationRestrictBaseHom :
    IsIso (pullbackSituationRestrictBaseHom S S' fS fX A' W hf) :=
  inferInstanceAs (IsIso (pullbackBaseRestrictOpenIso S S' fS A' W).hom)

/-- **The comparison `(X ×_{X'} U')|_{q⁻¹W₀} ≅ X ×_{X'} (U'|_{W₀})`, at the type it has as the
morphism of thickened spaces between the two situations.**  See
`pullbackSituationRestrictBaseHom` for why the name is needed; here the instance the name
carries is the open immersion that change of base asks for, which an isomorphism is. -/
def pullbackSituationRestrictSourceHom :
    (pullbackSituationRestrict S S' fS fX A' W hf).X ⟶
      (pullbackSituation S S' fS fX hf (A'.restrictOpen W)).X :=
  (pullbackSourceRestrictOpenIso S S' fX A' W).hom

/-- The morphism `pullbackSituationRestrictSourceHom` is an isomorphism. -/
instance isIso_pullbackSituationRestrictSourceHom :
    IsIso (pullbackSituationRestrictSourceHom S S' fS fX A' W hf) :=
  inferInstanceAs (IsIso (pullbackSourceRestrictOpenIso S S' fX A' W).hom)

/-- **The compatibility datum of [Stacks, Tag 07IC] for the two comparisons**, at the names
above.  This is
`Crystalline.GlobalCrystallineSituation.pullbackSituationRestrict_changeBase_condition`. -/
theorem pullbackSituationRestrict_changeBase_condition' :
    (pullbackSituationRestrict S S' fS fX A' W hf).toClosedFiber ≫
        closedFiberMap (pullbackSituationRestrictBaseHom S S' fS fX A' W hf) =
      pullbackSituationRestrictSourceHom S S' fS fX A' W hf ≫
        (pullbackSituation S S' fS fX hf (A'.restrictOpen W)).toClosedFiber :=
  pullbackSituationRestrict_changeBase_condition S S' fS fX A' W hf

/-- **Restriction of abelian sheaves along `Cris((U/T)|_{g⁻¹W, V}) ⥤ Cris(U_W/T_W)`**, the
equivalence `Crystalline.GlobalCrystallineSituation.pullbackSituationRestrictEquivalence`. -/
def pullbackSituationRestrictAbelianRestriction :
    Sheaf (smallTopology (pullbackSituation S S' fS fX hf (A'.restrictOpen W)))
        AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology (pullbackSituationRestrict S S' fS fX A' W hf))
        AddCommGrpCat.{u + 1} :=
  smallChangeBaseAbelianRestriction (pullbackSituationRestrict S S' fS fX A' W hf)
    (pullbackSituation S S' fS fX hf (A'.restrictOpen W))
    (pullbackSituationRestrictBaseHom S S' fS fX A' W hf)
    (pullbackSituationRestrictSourceHom S S' fS fX A' W hf)
    (pullbackSituationRestrict_changeBase_condition' S S' fS fX A' W hf)

/-- **The functor of the equivalence is change of divided power base along the two
comparisons**, by definition; so `pullbackSituationRestrictAbelianRestriction` is restriction of
abelian sheaves along `...pullbackSituationRestrictEquivalence` and not along some other
functor. -/
theorem pullbackSituationRestrictEquivalence_functor :
    (pullbackSituationRestrictEquivalence S S' fS fX A' W hf).functor =
      smallChangeBase (pullbackSituationRestrict S S' fS fX A' W hf)
        (pullbackSituation S S' fS fX hf (A'.restrictOpen W))
        (pullbackSituationRestrictBaseHom S S' fS fX A' W hf)
        (pullbackSituationRestrictSourceHom S S' fS fX A' W hf)
        (pullbackSituationRestrict_changeBase_condition' S S' fS fX A' W hf) :=
  rfl

/-- **The global sections of the two small crystalline sites agree across the restriction of the
situation `U/T` to an open `W` of `T'`**:

`Γ(Cris(U_W/T_W), -) ≅ g⁻¹ ⋙ Γ(Cris((U/T)|_{g⁻¹W, V}), -)`,

naturally in the abelian sheaf on `Cris(U_W/T_W)`, for `g⁻¹` restriction along
`Crystalline.GlobalCrystallineSituation.pullbackSituationRestrictEquivalence`.

This is the identification the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKBaseCase.lean` records as missing:
the left-hand side of the base case of the displayed equation (07MK) of [Stacks, Tag 07MJ] read
at `W` is `Γ(Cris(U_W/T_W), F_{U_W})` by
`...crisDirectImageSectionsNatIsoRightSideTop` applied to `(U', T', δ')|_W`, and this says that
group is the global sections of `Cris(U/T)` cut down to the open `V` of `U` above `g⁻¹W`.  The
isomorphism is restriction of sections, by
`smallChangeBaseGlobalSectionsIso_hom_app_comp_ΓRes`. -/
def pullbackSituationRestrictGlobalSectionsIso :
    globalSections (pullbackSituation S S' fS fX hf (A'.restrictOpen W)) ≅
      pullbackSituationRestrictAbelianRestriction S S' fS fX A' W hf ⋙
        globalSections (pullbackSituationRestrict S S' fS fX A' W hf) :=
  smallChangeBaseGlobalSectionsIso (pullbackSituationRestrict S S' fS fX A' W hf)
    (pullbackSituation S S' fS fX hf (A'.restrictOpen W))
    (pullbackSituationRestrictBaseHom S S' fS fX A' W hf)
    (pullbackSituationRestrictSourceHom S S' fS fX A' W hf)
    (pullbackSituationRestrict_changeBase_condition' S S' fS fX A' W hf)

end Restrict

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
