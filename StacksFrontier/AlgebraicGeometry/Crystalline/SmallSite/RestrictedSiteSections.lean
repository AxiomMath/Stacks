module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKInjectives
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImageLocalVanishing
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanEvaluation
public import StacksFrontier.CategoryTheory.Sites.AbelianRestrictionExact
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The sections of `u_{X/S, *}` over an open are the global sections of the restricted site

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], an open `W` of `S`
and an open `V` of `X` whose image lies in `W`.  `Crystalline.GlobalCrystallineSituation.restrict`
is the restricted situation `(p, S|_W, V)` and `...smallExtend` is change of divided power base
`Cris(V/S|_W) ⥤ Cris(X/S)`, [Stacks, Tag 07KL], along the two open immersions.  This file proves

`Γ(V, u_{X/S, *}ℋ) ≅ Γ(Cris(V/S|_W), ℋ|)`,

naturally in the abelian sheaf `ℋ` on `Cris(X/S)`, and transfers the vanishing of right derived
functors across it. No affineness and no hypothesis on `ℋ` is needed.

This is the identification the proof of [Stacks, Tag 07LM] performs when it passes to an affine
open `V` of `X` mapping into an affine open `W` of `S` and writes
`(Ru_{X/S, *}ℋ)|_{V_Zar} = Ru_{V/S|_W, *}(ℋ|)`.

## Both sides are the same limit

`u_{X/S, *}` is the right Kan extension of [Stacks, Tag 00XK] along the cocontinuous forgetful
functor of [Stacks, Tag 07IH], so its sections over `V` are the limit of `ℋ` over
`StructuredArrow (op V) (forgetToOpens S).op` — the objects `(U, T, δ)` of `Cris(X/S)` with
`U ⊆ V`.  That the identification is natural in `ℋ` is
`CategoryTheory.Functor.ranObjNatIsoLimit`.

Global sections on `Cris(V/S|_W)` are the limit of the underlying presheaf, by
`CategoryTheory.Sheaf.ΓNatIsoLim`, and restriction along `smallExtend` is precomposition, change
of base being continuous.  The two indexing categories agree: the hom-sets of the opens of `X`
are subsingletons, so an object of the comma category is just an object of `Cris(X/S)` lying in
`V`, and `Crystalline.GlobalCrystallineSituation.smallExtend_essImage_iff` says those are exactly
the objects coming from `Cris(V/S|_W)`.  The comparison functor `smallExtendStructuredArrow` is
therefore an equivalence, hence initial, and restriction along an initial functor does not change
a limit.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `smallExtendAbelianRestriction` — restriction of abelian sheaves along `smallExtend`.
* `smallExtendStructuredArrow` — the objects of `Cris(V/S|_W)` as the index category of the limit
  computing the sections of `u_{X/S, *}` over `V`.
* `zariskiDirectImageSectionsIsoLim` — the sections over `V` as a limit over the objects of
  `Cris(X/S)` lying in `V`, naturally in the sheaf.
* `limIsoLimSmallExtend` — that limit is the limit over `Cris(V/S|_W)`.
* `zariskiDirectImageSectionsIso` — **`Γ(V, u_{X/S, *}-) ≅ Γ(Cris(V/S|_W), -|)`**.

## Main results

* `exactFunctor_smallExtendAbelianRestriction` — restriction along `smallExtend` is exact, and
  `preservesInjectiveObjects_smallExtendAbelianRestriction` that it preserves injective sheaves.
* `isZero_rightDerived_zariskiDirectImageSections_of_isZero` — **the transfer of the derived
  vanishing**: `R^p (ℋ ↦ Γ(V, u_{X/S, *}ℋ))` vanishes at `ℋ` as soon as
  `H^p(Cris(V/S|_W), ℋ|)` does.  The composite's right derived functor collapses because
  restriction is exact and preserves injectives, [Stacks, Tag 015M].

## References

* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0796](https://stacks.math.columbia.edu/tag/0796)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

namespace SmallSite

/-! ### Restriction of abelian sheaves to the restricted site -/

/-- **Restriction of abelian sheaves along `smallExtend : Cris(V/S|_W) ⥤ Cris(X/S)`.**  This is
`...SmallSite.smallChangeBaseAbelianRestriction`, [Stacks, Tag 07KL], at the pair of open
immersions `S|_W ⟶ S` and `V ⟶ X` of a restricted situation. -/
def smallExtendAbelianRestriction :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1} :=
  smallChangeBaseAbelianRestriction (restrict S W V hVW) S (restrictSι S W V hVW)
    (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)

/-- Restriction of abelian sheaves along `smallExtend` is an additive functor. -/
instance additive_smallExtendAbelianRestriction :
    (smallExtendAbelianRestriction S W V hVW).Additive :=
  inferInstanceAs ((smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW)
    (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} _ _).Additive

/-- **Restriction of abelian sheaves to the restricted site is exact.**  Change of divided power
base is continuous and cocontinuous, `...smallChangeBase_isContinuous` and
`...smallChangeBase_isCocontinuous`, and restriction of abelian sheaves along such a functor is
exact, [Stacks, Tag 0796]. -/
theorem exactFunctor_smallExtendAbelianRestriction :
    exactFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
      (Sheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1})
      (smallExtendAbelianRestriction S W V hVW) :=
  Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous _ _
    (smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW) (restrictXι S W V hVW)
      (restrict_changeBase_condition' S W V hVW))

/-- Restriction of abelian sheaves along `smallExtend` preserves finite limits. -/
instance preservesFiniteLimits_smallExtendAbelianRestriction :
    PreservesFiniteLimits (smallExtendAbelianRestriction S W V hVW) :=
  ((exactFunctor_iff _).mp (exactFunctor_smallExtendAbelianRestriction S W V hVW)).1

/-- Restriction of abelian sheaves along `smallExtend` preserves finite colimits. -/
instance preservesFiniteColimits_smallExtendAbelianRestriction :
    PreservesFiniteColimits (smallExtendAbelianRestriction S W V hVW) :=
  ((exactFunctor_iff _).mp (exactFunctor_smallExtendAbelianRestriction S W V hVW)).2

/-- Restriction of abelian sheaves along `smallExtend` carries injective sheaves to injective
sheaves. -/
instance preservesInjectiveObjects_smallExtendAbelianRestriction :
    (smallExtendAbelianRestriction S W V hVW).PreservesInjectiveObjects :=
  preservesInjectiveObjects_smallChangeBaseAbelianRestriction (restrict S W V hVW) S
    (restrictSι S W V hVW) (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)

/-! ### The objects of `Cris(X/S)` lying in `V` as an index category -/

/-- An extended object of `Cris(X/S)` has its structure morphism to `X` factoring through `V`:
it lies in the essential image of `smallExtend`, which
`Crystalline.GlobalCrystallineSituation.smallExtend_essImage_iff` identifies with that
condition. -/
theorem range_toX_subset_smallExtend_obj (A : CrystallineThickening (restrict S W V hVW)) :
    Set.range ((smallExtend S W V hVW).obj A).obj.toX.base ⊆ (V : Set S.X) :=
  (smallExtend_essImage_iff S W V hVW _).1 (Functor.obj_mem_essImage _ A)

/-- The open of `X` attached to an extended object by the forgetful functor of
[Stacks, Tag 07IH] is contained in `V`. -/
theorem forgetToOpens_smallExtend_obj_le (A : CrystallineThickening (restrict S W V hVW)) :
    (forgetToOpens S).obj ((smallExtend S W V hVW).obj A) ≤ V :=
  range_toX_subset_smallExtend_obj S W V hVW A

/-- **The objects of `Cris(V/S|_W)`, read as the index category of the limit computing the
sections of `u_{X/S, *}` over `V`.**  The sections of the direct image over `V` are a limit over
`StructuredArrow (op V) (forgetToOpens S).op`, the category of objects of `Cris(X/S)` together
with an inclusion of their open of `X` into `V`; this functor sends an object of `Cris(V/S|_W)`
to its extension, with the inclusion of `forgetToOpens_smallExtend_obj_le`. -/
def smallExtendStructuredArrow :
    (CrystallineThickening (restrict S W V hVW))ᵒᵖ ⥤
      StructuredArrow (op V) (forgetToOpens S).op where
  obj A := StructuredArrow.mk (Y := op ((smallExtend S W V hVW).obj A.unop))
    (homOfLE (forgetToOpens_smallExtend_obj_le S W V hVW A.unop)).op
  map k := StructuredArrow.homMk ((smallExtend S W V hVW).op.map k) (Subsingleton.elim _ _)

/-- The object of `Cris(X/S)` underlying the image of `A` under `smallExtendStructuredArrow` is
the extension of `A`. -/
@[simp]
theorem smallExtendStructuredArrow_obj_right (A : (CrystallineThickening (restrict S W V hVW))ᵒᵖ) :
    ((smallExtendStructuredArrow S W V hVW).obj A).right =
      op ((smallExtend S W V hVW).obj A.unop) := rfl

/-- The morphism of `Cris(X/S)` underlying the image of `k` under `smallExtendStructuredArrow` is
the extension of `k`. -/
@[simp]
theorem smallExtendStructuredArrow_map_right
    {A B : (CrystallineThickening (restrict S W V hVW))ᵒᵖ} (k : A ⟶ B) :
    ((smallExtendStructuredArrow S W V hVW).map k).right =
      (smallExtend S W V hVW).op.map k := rfl

/-- The index functor followed by the projection is change of divided power base, by
definition. -/
theorem smallExtendStructuredArrow_comp_proj :
    smallExtendStructuredArrow S W V hVW ⋙ StructuredArrow.proj (op V) (forgetToOpens S).op =
      (smallExtend S W V hVW).op := rfl

/-- The functor `smallExtendStructuredArrow` is faithful. -/
instance faithful_smallExtendStructuredArrow :
    (smallExtendStructuredArrow S W V hVW).Faithful where
  map_injective {_ _} _ _ h :=
    (smallExtend S W V hVW).op.map_injective (congrArg (fun φ ↦ φ.right) h)

/-- The functor `smallExtendStructuredArrow` is full. -/
instance full_smallExtendStructuredArrow : (smallExtendStructuredArrow S W V hVW).Full where
  map_surjective {_ _} φ := by
    obtain ⟨k, hk⟩ := (smallExtend S W V hVW).op.map_surjective φ.right
    exact ⟨k, StructuredArrow.hom_ext _ _ hk⟩

/-- Every object of `Cris(X/S)` lying in `V` is isomorphic, as an object of the comma category, to
the extension of an object of `Cris(V/S|_W)`. -/
instance essSurj_smallExtendStructuredArrow :
    (smallExtendStructuredArrow S W V hVW).EssSurj where
  mem_essImage T := by
    have hV : Set.range T.right.unop.obj.toX.base ⊆ (V : Set S.X) := leOfHom T.hom.unop
    refine ⟨op (CrystallineThickening.localObject S W V hVW T.right.unop hV),
      ⟨StructuredArrow.isoMk ?_ (Subsingleton.elim _ _)⟩⟩
    exact ((CrystallineThickening.extendLocalObjectIso S W V hVW T.right.unop hV).op).symm

/-- The functor `smallExtendStructuredArrow` is an equivalence of categories. -/
instance isEquivalence_smallExtendStructuredArrow :
    (smallExtendStructuredArrow S W V hVW).IsEquivalence where

/-! ### The sections over `V` are the global sections of the restricted site -/

/-- Restriction of abelian sheaves along `smallExtend` is precomposition on the underlying
presheaves: change of divided power base is continuous, so no sheafification intervenes.  This
holds by definition. -/
theorem smallExtendAbelianRestriction_comp_sheafToPresheaf :
    smallExtendAbelianRestriction S W V hVW ⋙
        sheafToPresheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1} =
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (smallExtend S W V hVW).op :=
  rfl

/-- **The sections of `u_{X/S, *}ℋ` over `V` are the limit of `ℋ` over the objects of
`Cris(X/S)` lying in `V`**, naturally in `ℋ`.  The direct image is the right Kan extension of
[Stacks, Tag 00XK] along the forgetful functor of [Stacks, Tag 07IH], and the sections of a right
Kan extension at an object are a limit over the comma category, naturally in the extended
functor, by `CategoryTheory.Functor.ranObjNatIsoLimit`. -/
def zariskiDirectImageSectionsIsoLim :
    zariskiDirectImageSections S V ≅
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (StructuredArrow (op V) (forgetToOpens S).op)
            ((CrystallineThickening S)ᵒᵖ) AddCommGrpCat.{u + 1}).obj
          (StructuredArrow.proj (op V) (forgetToOpens S).op) ⋙ lim :=
  Functor.isoWhiskerRight
      ((forgetToOpens S).sheafPushforwardCocontinuousCompSheafToPresheafIso
        AddCommGrpCat.{u + 1} (smallTopology S) (opensTopology S))
      ((evaluation (S.X.Opens)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.ranObjNatIsoLimit AddCommGrpCat.{u + 1} (forgetToOpens S).op (op V))

/-- **The limit over the objects of `Cris(X/S)` lying in `V` is the limit over
`Cris(V/S|_W)`.**  The index functor `smallExtendStructuredArrow` is an equivalence, hence
initial, and restriction along an initial functor does not change a limit —
`CategoryTheory.Functor.Initial.limIso`, which is natural in the diagram. -/
def limIsoLimSmallExtend :
    (Functor.whiskeringLeft (StructuredArrow (op V) (forgetToOpens S).op)
          ((CrystallineThickening S)ᵒᵖ) AddCommGrpCat.{u + 1}).obj
        (StructuredArrow.proj (op V) (forgetToOpens S).op) ⋙ lim ≅
      (Functor.whiskeringLeft ((CrystallineThickening (restrict S W V hVW))ᵒᵖ)
          ((CrystallineThickening S)ᵒᵖ) AddCommGrpCat.{u + 1}).obj
        (smallExtend S W V hVW).op ⋙ lim :=
  (Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft (StructuredArrow (op V) (forgetToOpens S).op)
        ((CrystallineThickening S)ᵒᵖ) AddCommGrpCat.{u + 1}).obj
      (StructuredArrow.proj (op V) (forgetToOpens S).op))
    (Functor.Initial.limIso (E := AddCommGrpCat.{u + 1})
      (smallExtendStructuredArrow S W V hVW))).symm

/-- **The sections of `u_{X/S, *}` over `V` are the global sections of the restricted site**:

`Γ(V, u_{X/S, *}ℋ) ≅ Γ(Cris(V/S|_W), ℋ|)`,

naturally in the abelian sheaf `ℋ` on `Cris(X/S)`, for `ℋ|` its restriction along
`smallExtend`.

Both sides are limits of the underlying presheaf of `ℋ`: the left over the objects of
`Cris(X/S)` lying in `V`, by `zariskiDirectImageSectionsIsoLim`, and the right over
`Cris(V/S|_W)`, by `CategoryTheory.Sheaf.ΓNatIsoLim`; and
`Crystalline.GlobalCrystallineSituation.smallExtendEquivalence` exhibits the second indexing
category as the first, which is `limIsoLimSmallExtend`. -/
def zariskiDirectImageSectionsIso :
    zariskiDirectImageSections S V ≅
      smallExtendAbelianRestriction S W V hVW ⋙ globalSections (restrict S W V hVW) :=
  zariskiDirectImageSectionsIsoLim S V ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
      (limIsoLimSmallExtend S W V hVW) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallExtendAbelianRestriction S W V hVW)
      (Sheaf.ΓNatIsoLim (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1}).symm

/-! ### Transfer of the derived vanishing -/

/-- **The right derived functors of `ℋ ↦ Γ(V, u_{X/S, *}ℋ)` are the cohomology of the restricted
site.**  `Γ(V, u_{X/S, *}-)` is restriction along `smallExtend` followed by global sections on
`Cris(V/S|_W)`, by `zariskiDirectImageSectionsIso`; restriction is exact, so every sheaf is
acyclic for it, and it carries injective sheaves to injective sheaves, so the right derived
functors of the composite collapse — [Stacks, Tag 015M] in the elementary case where the
comparison is an isomorphism for degreewise reasons. -/
theorem isZero_rightDerived_zariskiDirectImageSections_of_isZero
    (p : ℕ) (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : IsZero (((globalSections (restrict S W V hVW)).rightDerived p).obj
      ((smallExtendAbelianRestriction S W V hVW).obj G))) :
    IsZero (((zariskiDirectImageSections S V).rightDerived p).obj G) := by
  have := hasDerivedCategorySheaf S
  have := hasDerivedCategorySheaf (restrict S W V hVW)
  have hA : ∀ n : ℕ, 0 < n →
      IsZero (((smallExtendAbelianRestriction S W V hVW).rightDerived n).obj G) :=
    (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic
      (smallExtendAbelianRestriction S W V hVW) G).1
      (Functor.rightAcyclic_of_exact (smallExtendAbelianRestriction S W V hVW) G)
  refine IsZero.of_iso (IsZero.of_iso h
    (Stacks.RightDerivedComp.objIso (smallExtendAbelianRestriction S W V hVW)
      (injectiveResolution G) hA (globalSections (restrict S W V hVW)) p)) ?_
  exact (Functor.rightDerivedIsoOfNatIso (zariskiDirectImageSectionsIso S W V hVW) p).app G

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
