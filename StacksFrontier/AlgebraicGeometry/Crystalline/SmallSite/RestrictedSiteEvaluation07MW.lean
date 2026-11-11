module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionOpen07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictedSiteSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingZariskiRestriction

/-!
# The sections of `u_{X/S, *}` over an open, read on the restricted site, with their evaluations

Fix a global crystalline situation `(p, (S, I, γ), X)`, an open `W` of `S` and an open `V` of `X`
mapping into `W`, with restricted situation `(p, S|_W, V)`
(`Crystalline.GlobalCrystallineSituation.restrict`) and change of divided power base
`j = smallExtend : Cris(V/S|_W) ⥤ Cris(X/S)`.  For an abelian sheaf `G` on `Cris(X/S)` this file
constructs the isomorphism

`θ_G : Γ(V, u_{X/S, *}G) ≅ Γ(V, u_{V/S|_W, *}(j⁻¹G))`

(`zariskiDirectImageRestrictIso`), natural in `G`, and proves that it carries the value of a
section at `j(B)` to its value at `B` (`zariskiDirectImageRestrictIso_hom_eval`): both sides are
the limit of `G` over the objects lying over `V`, and `j` identifies the objects of
`Cris(V/S|_W)` (all of which lie over the whole of `V`) with the objects of `Cris(X/S)` lying over
`V` (`Crystalline.GlobalCrystallineSituation.smallExtend_essImage_iff`).

This is the identification through which a statement about sections over an open `V` of `X` is
reduced to the restricted situation, in the proof of part (3) of [Stacks, Tag 07MW].

## Main definitions

* `smallExtendLiesOver` — the objects of `Cris(V/S|_W)` as objects of `Cris(X/S)` lying over `V`;
  an equivalence.
* `zariskiDirectImageRestrictIso` — `θ_G`.

## Main results

* `zariskiDirectImageRestrictIso_hom_eval` — `θ_G` followed by evaluation at `B` is evaluation at
  `j(B)`.
* `zariskiDirectImageRestrictIso_hom_naturality` — `θ` is natural in `G`.
* `quasiIso_sections_zariskiDirectImageToAmbient_of_restrict` — the sections over `V` of the
  restriction `u_{X/S, *}J ⟶ h_*(J_T)` of an object `A` of `Cris(X/S)` are a quasi-isomorphism as
  soon as the same map for an object `A'` of `Cris(V/S|_W)` with `j(A') ≅ A|_{h⁻¹(V)}` is one on
  sections over the whole of `V`.

## What is and is not proved

Everything stated is proved; nothing here is specific to a crystal or to Tag 07MW.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The objects of `Cris(V/S|_W)`, all lying over `V`, as objects of `Cris(X/S)` lying over
`V`**: change of divided power base, landing in the full subcategory of the objects lying over
`V`. -/
def smallExtendLiesOver :
    (LiesOver (restrict S W V hVW) ⊤).FullSubcategory ⥤ (LiesOver S V).FullSubcategory :=
  ObjectProperty.lift _ ((LiesOver (restrict S W V hVW) ⊤).ι ⋙ smallExtend S W V hVW)
    fun B => forgetToOpens_smallExtend_obj_le S W V hVW B.obj

instance : (smallExtendLiesOver S W V hVW).Faithful where
  map_injective {B B'} f g h := by
    have : (smallExtend S W V hVW).map f.hom = (smallExtend S W V hVW).map g.hom :=
      congrArg (fun k => k.hom) h
    exact ObjectProperty.hom_ext _ ((smallExtend S W V hVW).map_injective this)

instance : (smallExtendLiesOver S W V hVW).Full where
  map_surjective {_ _} f :=
    ⟨ObjectProperty.homMk ((smallExtend S W V hVW).preimage f.hom),
      ObjectProperty.hom_ext _ ((smallExtend S W V hVW).map_preimage f.hom)⟩

instance : (smallExtendLiesOver S W V hVW).EssSurj where
  mem_essImage B := by
    obtain ⟨B', ⟨e⟩⟩ := (smallExtend_essImage_iff S W V hVW B.obj).2 B.property
    exact ⟨⟨B', le_top⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (smallExtendLiesOver S W V hVW).IsEquivalence where

/-- The opposite of `smallExtendLiesOver` is initial, being an equivalence. -/
instance : (smallExtendLiesOver S W V hVW).op.Initial :=
  Functor.initial_of_isLeftAdjoint _

/-- The diagram of `G` over the objects lying over `V`, read along `smallExtendLiesOver`, is the
diagram of the restriction of `G` over `Cris(V/S|_W)`: the identity in every component. -/
def smallExtendLiesOverDiagramIso (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (smallExtendLiesOver S W V hVW).op ⋙ (LiesOver S V).ι.op ⋙ G.obj ≅
      (LiesOver (restrict S W V hVW) ⊤).ι.op ⋙
        ((smallExtendAbelianRestriction S W V hVW).obj G).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **`θ_G : Γ(V, u_{X/S, *}G) ≅ Γ(V, u_{V/S|_W, *}(j⁻¹G))`**: both are limits of `G` over the
objects lying over `V`, and `smallExtendLiesOver` identifies the two indexing categories. -/
def zariskiDirectImageRestrictIso (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((zariskiDirectImage S).obj G).obj.obj (op V) ≅
      ((zariskiDirectImage (restrict S W V hVW)).obj
        ((smallExtendAbelianRestriction S W V hVW).obj G)).obj.obj (op ⊤) :=
  zariskiSectionsIso S V G ≪≫
    (Functor.Initial.limitIso (smallExtendLiesOver S W V hVW).op
        ((LiesOver S V).ι.op ⋙ G.obj)).symm ≪≫
    HasLimit.isoOfNatIso (smallExtendLiesOverDiagramIso S W V hVW G) ≪≫
    (zariskiSectionsIso (restrict S W V hVW) ⊤
      ((smallExtendAbelianRestriction S W V hVW).obj G)).symm

/-- **`θ_G` followed by the evaluation at an object `B` of `Cris(V/S|_W)` is the evaluation at
`j(B)`.** -/
@[reassoc]
theorem zariskiDirectImageRestrictIso_hom_eval (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (B : CrystallineThickening (restrict S W V hVW))
    (hB : (forgetToOpens (restrict S W V hVW)).obj B ≤ ⊤) :
    (zariskiDirectImageRestrictIso S W V hVW G).hom ≫
        zariskiDirectImageEval (restrict S W V hVW) hB
          ((smallExtendAbelianRestriction S W V hVW).obj G) =
      zariskiDirectImageEval S (forgetToOpens_smallExtend_obj_le S W V hVW B) G := by
  rw [← zariskiSectionsIso_hom_π, ← zariskiSectionsIso_hom_π]
  simp only [zariskiDirectImageRestrictIso, Iso.trans_hom, Iso.symm_hom,
    Functor.Initial.limitIso_inv, Category.assoc, Iso.inv_hom_id_assoc,
    Stacks.ProCech.sectionsOverπ, HasLimit.isoOfNatIso_hom_π]
  simp only [smallExtendLiesOverDiagramIso]
  exact congrArg (_ ≫ ·) (limit.pre_π _ _ _)

/-- Two maps into `Γ(V, u_{V/S|_W, *}G')` agree as soon as they agree after every evaluation at an
object of `Cris(V/S|_W)`. -/
theorem zariskiDirectImage_top_hom_ext {A : AddCommGrpCat.{u + 1}}
    {G' : Sheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1}}
    {f g : A ⟶ ((zariskiDirectImage (restrict S W V hVW)).obj G').obj.obj (op ⊤)}
    (h : ∀ B : CrystallineThickening (restrict S W V hVW),
      f ≫ zariskiDirectImageEval (restrict S W V hVW) (le_top (a := (forgetToOpens _).obj B)) G' =
        g ≫ zariskiDirectImageEval (restrict S W V hVW) le_top G') :
    f = g := by
  rw [← cancel_mono (zariskiSectionsIso (restrict S W V hVW) ⊤ G').hom]
  refine limit.hom_ext fun B => ?_
  rw [Category.assoc, Category.assoc, zariskiSectionsIso_hom_limit_π]
  exact h B.unop.obj

/-- **`θ` is natural in the sheaf.** -/
@[reassoc]
theorem zariskiDirectImageRestrictIso_hom_naturality
    {G H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : G ⟶ H) :
    ((zariskiDirectImage S).map φ).hom.app (op V) ≫
        (zariskiDirectImageRestrictIso S W V hVW H).hom =
      (zariskiDirectImageRestrictIso S W V hVW G).hom ≫
        ((zariskiDirectImage (restrict S W V hVW)).map
          ((smallExtendAbelianRestriction S W V hVW).map φ)).hom.app (op ⊤) := by
  refine zariskiDirectImage_top_hom_ext S W V hVW fun B => ?_
  have h1 := zariskiDirectImageRestrictIso_hom_eval S W V hVW H B le_top
  have h2 := zariskiDirectImageRestrictIso_hom_eval S W V hVW G B le_top
  have n1 := zariskiDirectImageEval_naturality S (forgetToOpens_smallExtend_obj_le S W V hVW B) φ
  have n2 := zariskiDirectImageEval_naturality (restrict S W V hVW)
    (le_top (a := (forgetToOpens _).obj B)) ((smallExtendAbelianRestriction S W V hVW).map φ)
  refine (Category.assoc _ _ _).trans ?_
  refine ((congrArg _ h1).trans n1).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg _ n2).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (congrArg (· ≫ ((smallExtendAbelianRestriction S W V hVW).map φ).hom.app (op B)) h2).symm

/-! ### The restriction `u_{X/S, *}J ⟶ h_*(J_T)` over `V`, read on the restricted site -/

/-- **The sections over `V` of `u_{X/S, *}J ⟶ h_*(J_T)` are those over the whole of `V` of the
same map for the restricted situation.**  Let `A` be an object of `Cris(X/S)`, `A'` an object of
`Cris(V/S|_W)` and `c : j(A'|_{T'}) ≅ A|_{h⁻¹(V)}` an isomorphism in `Cris(X/S)`, where `A'|_{T'}`
is the restriction of `A'` to the preimage of the whole of `V`.  If the restriction
`Γ(V, u_{V/S|_W, *}(j⁻¹J)) ⟶ Γ(T', (j⁻¹J)_{T'})` is a quasi-isomorphism, so is
`Γ(V, u_{X/S, *}J) ⟶ Γ(h⁻¹(V), J_T)`: the two are identified by `θ` on the sources and by
restriction along `c` on the targets. -/
theorem quasiIso_sections_zariskiDirectImageToAmbient_of_restrict
    (A : CrystallineThickening S) (A' : CrystallineThickening (restrict S W V hVW))
    (c : (smallExtend S W V hVW).obj
        (A'.restrictOpen (CrystallineThickening.ambientToXPreimage A' ⊤)) ≅
      A.restrictOpen (CrystallineThickening.ambientToXPreimage A V))
    (J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (h : QuasiIso ((((sheafSections (opensTopology (restrict S W V hVW))
      AddCommGrpCat.{u + 1}).obj (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (CrystallineThickening.zariskiDirectImageToAmbient A')
          (ComplexShape.up ℤ)).app
            (((smallExtendAbelianRestriction S W V hVW).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj J)))) :
    QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op V)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (CrystallineThickening.zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J)) := by
  refine (quasiIso_iff_of_arrow_mk_iso _ _ ?_).2 h
  refine Arrow.isoMk
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => zariskiDirectImageRestrictIso S W V hVW (J.X n))
      (fun m n _ => (zariskiDirectImageRestrictIso_hom_naturality S W V hVW (J.d m n)).symm))
    (HomologicalComplex.Hom.isoOfComponents (fun n => (J.X n).obj.mapIso c.op)
      (fun m n _ => (J.d m n).hom.naturality c.hom.op)) ?_
  ext n : 1
  refine (zariskiDirectImageRestrictIso_hom_eval S W V hVW (J.X n) _ _).trans ?_
  exact (zariskiDirectImageEval_comp S c.hom _ _ (J.X n)).symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end
