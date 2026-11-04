module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksCore.CategoryTheory.Sites.Point.StalkAsColimit
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Point.OverBijection

/-!
# The stalk of an extension by zero from a localized ringed site

Let `(C, O)` be a ringed site, `U` an object of `C` and `p` a point of `C`. For a sheaf of
modules `G` on the localized ringed site `C/U`, the stalk at `p` of the extension by zero
`j_{U!}G` is the direct sum of the stalks of `G` at the points of `C/U` lying over `p`. Those
points are indexed by the fibre `p(U)` of `p` at `U`, the point attached to `x ∈ p(U)` being
`p.over x`. This is Stacks 0710.

The proof is the one in the source, carried out on underlying presheaves of abelian groups.
Sections of the extension by zero over `V` are the direct sum, over the arrows `φ : V ⟶ U`, of
the sections of `G` over `Over.mk φ` (this is the Stacks 03DI direct-sum formula,
`extensionByZeroPresheafSectionIso`). Taking the colimit over a neighbourhood system of `p`
commutes with that direct sum, and on the `φ`-summand the colimit computes the stalk of `G` at
the point `p.over (p(φ) y)` — so the two sides are described by mutually inverse maps built
from the summand inclusions and the structure maps into the stalks.

## Main results

* `Stacks.Sites.ExtensionByZero.stalkExtensionByZeroIso`: the stalk of an extension by zero is
  the direct sum of the stalks above the point.

## Implementation notes

Everything is formed in a single universe: the statement quantifies over
`RingedSite.{u, u, u}` and over `GrothendieckTopology.Point.{u, u, u}`, which is what the
colimit description of a stalk and the fibre functor of a point are available for here.

The isomorphism is assembled out of four comparisons, in this order: the identification of the
extension by zero with the sheafification of the presheaf-level pullback
(`SheafOfModules.pullbackIso`), the identification of that sheafification's underlying
presheaf, the fact that the stalk of a sheafification is the stalk of the presheaf, and
finally the direct-sum formula proved here on the presheaf level. Keeping the presheaf-level
part separate (`stalkExtensionByZeroForward` and `stalkExtensionByZeroBackward`, with the two
composite identities) is what makes the mutual inverses provable by the universal properties
of the two colimits rather than by a computation in the sheafification.

`extensionByZeroPresheafSectionIso_inv_ι` is stated with `HEq` in Stacks 03DI, so each use
here is passed through `eq_of_heq` before being rewritten with.

## References

* [Stacks Project, Tag 0710](https://stacks.math.columbia.edu/tag/0710)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

open AlgebraicGeometry

universe u

/-- Restriction of presheaves of modules along `Over.forget U` is a right adjoint. -/
local instance ringedSitePresheafRestrictionIsRightAdjoint (X : RingedSite.{u, u, u})
    (U : X.C) :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) :
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- The presheaf-level extension by zero of `G`: the pullback along `Over.forget U` of the
underlying presheaf of modules of `G`. -/
noncomputable abbrev extensionByZeroPresheaf (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
  (PresheafOfModules.pullback.{u} (F := Over.forget U)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) :
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).hom).obj G.val

/-- The sections of `extensionByZeroPresheaf X U G` over `V` are the direct sum, over the arrows
`φ : V ⟶ U`, of the sections of `G` over `Over.mk φ`. -/
noncomputable def ringedSiteSectionIso (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) :
    (extensionByZeroPresheaf X U G).obj (op V) ≅
      ∐ extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V :=
  extensionByZeroPresheafSectionIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V

/-- The inclusion, as a map of abelian groups, of the sections of `G` over `Over.mk φ` as the
`φ`-summand of the sections of `extensionByZeroPresheaf X U G` over `V`. -/
noncomputable def extensionByZeroSectionEmbedding (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) (φ : V ⟶ U) :
    G.val.presheaf.obj (op (Over.mk φ)) ⟶
      (extensionByZeroPresheaf X U G).presheaf.obj (op V) :=
  (forget₂ _ AddCommGrpCat).map
    (Sigma.ι (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) φ ≫
      (ringedSiteSectionIso X U G V).inv)

/-- The section embedding commutes with restriction along a morphism `g : W ⟶ W'` of `Over U`. -/
private lemma extensionByZeroSectionEmbedding_over_naturality_aux (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {W W' : Over U} (g : W ⟶ W') :
    extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
        (extensionByZeroPresheaf X U G).presheaf.map g.left.op =
      G.val.presheaf.map g.op ≫
        extensionByZeroSectionEmbedding X U G W.left W.hom := by
  let adj := PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := Over.forget U) (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) :
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).hom
  have hW := congrArg (fun t => (forget₂ _ AddCommGrpCat).map t) (eq_of_heq
    (extensionByZeroPresheafSectionIso_inv_ι X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G
      W.left W.hom))
  have hW' := congrArg (fun t => (forget₂ _ AddCommGrpCat).map t) (eq_of_heq
    (extensionByZeroPresheafSectionIso_inv_ι X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G
      W'.left W'.hom))
  dsimp only [extensionByZeroSectionEmbedding, ringedSiteSectionIso,
    extensionByZeroPresheaf]
  rw [hW, hW']
  ext s
  exact (PresheafOfModules.naturality_apply (adj.unit.app G.val)
    g.op s).symm

/-- The section embedding commutes with restriction along `f : W ⟶ V`, the `φ`-summand being sent
to the `f ≫ φ`-summand. -/
lemma extensionByZeroSectionEmbedding_naturality (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {V W : X.C} (f : W ⟶ V) (φ : V ⟶ U) :
    extensionByZeroSectionEmbedding X U G V φ ≫
        (extensionByZeroPresheaf X U G).presheaf.map f.op =
      G.val.presheaf.map (Over.homMk f rfl : Over.mk (f ≫ φ) ⟶ Over.mk φ).op ≫
        extensionByZeroSectionEmbedding X U G W (f ≫ φ) :=
  extensionByZeroSectionEmbedding_over_naturality_aux X U G
    (W := Over.mk (f ≫ φ)) (W' := Over.mk φ) (Over.homMk f rfl)

/-- The section embedding commutes with restriction along a morphism `g : W ⟶ W'` of `Over U`. -/
lemma extensionByZeroSectionEmbedding_over_naturality (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {W W' : Over U} (g : W ⟶ W') :
    extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
        (extensionByZeroPresheaf X U G).presheaf.map g.left.op =
      G.val.presheaf.map g.op ≫
        extensionByZeroSectionEmbedding X U G W.left W.hom :=
  extensionByZeroSectionEmbedding_over_naturality_aux X U G g

/-- The direct sum, over `x ∈ p(U)`, of the stalks of `G` at the points `p.over x`. -/
noncomputable abbrev stalkExtensionByZeroTarget (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    AddCommGrpCat :=
  ∐ fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf

/-- For `y ∈ p(V)`, the map from the sections of `extensionByZeroPresheaf X U G` over `V` to
`stalkExtensionByZeroTarget X p U G` which sends the `φ`-summand, by the germ at `y`, to the stalk
of `G` at `p.over (p(φ) y)`. -/
noncomputable def extensionByZeroStageToStalks (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) (V : X.C)
    (y : p.fiber.obj V) :
    (extensionByZeroPresheaf X U G).presheaf.obj (op V) ⟶
      stalkExtensionByZeroTarget X p U G := by
  let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat
  let S := extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V
  let e : F.obj (∐ S) ≅ ∐ fun φ : V ⟶ U => F.obj (S φ) :=
    F.mapIso (Sigma.isoColimit (Discrete.functor S)) ≪≫
      preservesColimitIso F (Discrete.functor S) ≪≫
      HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F) ≪≫
      (Sigma.isoColimit (Discrete.functor (fun φ : V ⟶ U => F.obj (S φ)))).symm
  refine F.map (ringedSiteSectionIso X U G V).hom ≫ e.hom ≫ ?_
  refine Sigma.desc (fun φ : V ⟶ U => ?_)
  let x := p.fiber.map φ y
  have hmem : y ∈ (FunctorToTypes.fromOverSubfunctor p.fiber x).obj (Over.mk φ) :=
    (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl
  have qy : (p.over x).fiber.obj (Over.mk φ) := by
    change (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj (Over.mk φ)
    exact ⟨y, hmem⟩
  exact (p.over x).toPresheafFiber (Over.mk φ) qy G.val.presheaf ≫
    Sigma.ι (fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf) x

/-- The comparison between the underlying abelian group of the direct sum of the modules
`extensionByZeroSummands` and the direct sum of their underlying abelian groups sends the image
of the `φ`-th summand inclusion to the `φ`-th summand inclusion. -/
lemma extensionByZeroSumForgetIso_hom_ι (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C)
    (φ : V ⟶ U) :
    (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
        AddCommGrpCat).map
        (Sigma.ι (extensionByZeroSummands X.J
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) φ) ≫
      (let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
          AddCommGrpCat
       let S := extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V
       F.mapIso (Sigma.isoColimit (Discrete.functor S)) ≪≫
         preservesColimitIso F (Discrete.functor S) ≪≫
         HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F) ≪≫
         (Sigma.isoColimit (Discrete.functor (fun φ : V ⟶ U => F.obj (S φ)))).symm).hom =
      Sigma.ι (fun ψ : V ⟶ U =>
        (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
            AddCommGrpCat).obj
          (extensionByZeroSummands X.J
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V ψ)) φ := by
  let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat
  let S := extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V
  let e := F.mapIso (Sigma.isoColimit (Discrete.functor S)) ≪≫
    preservesColimitIso F (Discrete.functor S) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F) ≪≫
    (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).symm
  show F.map (Sigma.ι S φ) ≫ e.hom = _
  dsimp [e]
  calc
    _ = F.map (Sigma.ι S φ ≫ (Sigma.isoColimit (Discrete.functor S)).hom) ≫
        (preservesColimitIso F (Discrete.functor S)).hom ≫
        (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F)).hom ≫
        (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv := by
          simp only [F.map_comp, Category.assoc]
    _ = F.map (colimit.ι (Discrete.functor S) (Discrete.mk φ)) ≫
        (preservesColimitIso F (Discrete.functor S)).hom ≫
        (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F)).hom ≫
        (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv :=
          congrArg (fun g => F.map g ≫
            (preservesColimitIso F (Discrete.functor S)).hom ≫
            (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F)).hom ≫
            (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv)
              (Sigma.ι_isoColimit_hom (Discrete.functor S) φ)
    _ = colimit.ι (Discrete.functor S ⋙ F) (Discrete.mk φ) ≫
        (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F)).hom ≫
        (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv :=
          congrArg (fun g => g ≫
            (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F)).hom ≫
            (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv)
              (ι_preservesColimitIso_hom F (Discrete.functor S) (Discrete.mk φ))
    _ = (Discrete.compNatIsoDiscrete S F).hom.app (Discrete.mk φ) ≫
        colimit.ι (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ))) (Discrete.mk φ) ≫
        (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv :=
          congrArg (fun g => g ≫
            (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).inv)
              (HasColimit.isoOfNatIso_ι_hom (Discrete.compNatIsoDiscrete S F) (Discrete.mk φ))
    _ = Sigma.ι (fun ψ : V ⟶ U => F.obj (S ψ)) φ := by
          simp [Discrete.compNatIsoDiscrete]

/-- The underlying abelian group of the direct sum of the modules `extensionByZeroSummands` is
the direct sum of their underlying abelian groups. -/
noncomputable def extensionByZeroSumForgetIso (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) :
    (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
        AddCommGrpCat).obj
        (∐ extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) ≅
      ∐ fun φ : V ⟶ U =>
        (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
            AddCommGrpCat).obj
          (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V φ) := by
  let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat
  let S := extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V
  exact F.mapIso (Sigma.isoColimit (Discrete.functor S)) ≪≫
    preservesColimitIso F (Discrete.functor S) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F) ≪≫
    (Sigma.isoColimit (Discrete.functor (fun φ : V ⟶ U => F.obj (S φ)))).symm

/-- The inverse of `extensionByZeroSumForgetIso` sends the `φ`-th summand inclusion to the image
under the forgetful functor of the `φ`-th summand inclusion of modules. -/
lemma extensionByZeroSumForgetIso_inv_ι (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C)
    (φ : V ⟶ U) :
    Sigma.ι (fun ψ : V ⟶ U =>
      (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
          AddCommGrpCat).obj
        (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V ψ)) φ ≫
      (extensionByZeroSumForgetIso X U G V).inv =
    (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
        AddCommGrpCat).map
      (Sigma.ι (extensionByZeroSummands X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) φ) := by
  apply (cancel_mono (extensionByZeroSumForgetIso X U G V).hom).mp
  calc
    _ = Sigma.ι (fun ψ : V ⟶ U =>
          (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
              AddCommGrpCat).obj
            (extensionByZeroSummands X.J
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V ψ)) φ := by simp
    _ = (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
        AddCommGrpCat).map
          (Sigma.ι (extensionByZeroSummands X.J
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) φ) ≫
        (extensionByZeroSumForgetIso X U G V).hom :=
          (extensionByZeroSumForgetIso_hom_ι X U G V φ).symm

/-- The summand inclusion of the section embedding: composing the `φ`-inclusion into the direct
sum of the underlying abelian groups with the two comparison isomorphisms gives exactly
`extensionByZeroSectionEmbedding`. -/
lemma sigmaι_comp_forgetIso_inv_sectionIso_inv (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) (φ : V ⟶ U) :
    Sigma.ι (fun ψ : V ⟶ U =>
        (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
            AddCommGrpCat).obj
          (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V ψ)) φ ≫
      (extensionByZeroSumForgetIso X U G V).inv ≫
        ((forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
            AddCommGrpCat).mapIso
          (ringedSiteSectionIso X U G V)).inv =
      extensionByZeroSectionEmbedding X U G V φ := by
  rw [← Category.assoc, extensionByZeroSumForgetIso_inv_ι X U G V φ]
  exact ((forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat).map_comp
    (Sigma.ι (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) φ)
    (ringedSiteSectionIso X U G V).inv).symm

/-- Two maps out of the sections of `extensionByZeroPresheaf X U G` over `V` are equal if they
agree after composing with each section embedding. -/
private lemma hom_ext_of_sectionEmbedding (X : RingedSite.{u, u, u})
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) {T : AddCommGrpCat}
    {a b : (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat).obj ((extensionByZeroPresheaf X U G).obj (op V)) ⟶ T}
    (h : ∀ φ : V ⟶ U, extensionByZeroSectionEmbedding X U G V φ ≫ a =
      extensionByZeroSectionEmbedding X U G V φ ≫ b) : a = b := by
  let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat
  apply (cancel_epi ((extensionByZeroSumForgetIso X U G V).inv ≫
    (F.mapIso (ringedSiteSectionIso X U G V)).inv)).mp
  refine Sigma.hom_ext _ _ fun φ => ?_
  have hι := sigmaι_comp_forgetIso_inv_sectionIso_inv X U G V φ
  erw [← Category.assoc _ _ a, ← Category.assoc _ _ b, hι]
  exact h φ

/-- On the `φ`-summand, `extensionByZeroStageToStalks X p U G V y` is the germ at `y` into the
stalk of `G` at `p.over (p(φ) y)`, followed by the corresponding summand inclusion. -/
lemma extensionByZeroStageToStalks_comp_embedding (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) (V : X.C)
    (y : p.fiber.obj V) (φ : V ⟶ U) :
    extensionByZeroSectionEmbedding X U G V φ ≫
        extensionByZeroStageToStalks X p U G V y =
      (p.over (p.fiber.map φ y)).toPresheafFiber (Over.mk φ)
          (by
            change (FunctorToTypes.fromOverSubfunctor p.fiber (p.fiber.map φ y)).toFunctor.obj
              (Over.mk φ)
            exact ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl⟩)
          G.val.presheaf ≫
        Sigma.ι (fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf)
          (p.fiber.map φ y) := by
  let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat
  let S := extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V
  let e : F.obj (∐ S) ≅ ∐ fun ψ : V ⟶ U => F.obj (S ψ) :=
    F.mapIso (Sigma.isoColimit (Discrete.functor S)) ≪≫
      preservesColimitIso F (Discrete.functor S) ≪≫
      HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F) ≪≫
      (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).symm
  let st := ringedSiteSectionIso X U G V
  let component : ∀ ψ : V ⟶ U,
      F.obj (S ψ) ⟶ stalkExtensionByZeroTarget X p U G := fun ψ =>
    let xψ := p.fiber.map ψ y
    let hyψ : (p.over xψ).fiber.obj (Over.mk ψ) := by
      show (FunctorToTypes.fromOverSubfunctor p.fiber xψ).toFunctor.obj (Over.mk ψ)
      exact ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl⟩
    (p.over xψ).toPresheafFiber (Over.mk ψ) hyψ G.val.presheaf ≫
      Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) xψ
  show F.map (Sigma.ι S φ ≫ st.inv) ≫ F.map st.hom ≫ e.hom ≫
      Sigma.desc component = component φ
  calc
    _ = (F.map (Sigma.ι S φ ≫ st.inv) ≫ F.map st.hom) ≫ e.hom ≫
        Sigma.desc component := by simp [Category.assoc]
    _ = F.map ((Sigma.ι S φ ≫ st.inv) ≫ st.hom) ≫ e.hom ≫
        Sigma.desc component := congrArg (fun g => g ≫ e.hom ≫ Sigma.desc component)
          (F.map_comp (Sigma.ι S φ ≫ st.inv) st.hom).symm
    _ = F.map (Sigma.ι S φ) ≫ e.hom ≫
        Sigma.desc component := by simp [Category.assoc]
    _ = Sigma.ι (fun ψ : V ⟶ U => F.obj (S ψ)) φ ≫
        Sigma.desc component := by
          have hι : F.map (Sigma.ι S φ) ≫ e.hom =
              Sigma.ι (fun ψ : V ⟶ U => F.obj (S ψ)) φ :=
            extensionByZeroSumForgetIso_hom_ι X U G V φ
          exact congrArg (fun g => g ≫ Sigma.desc component) hι
    _ = component φ := by simp [component]

/-- For `x = p(φ) y`, on the `φ`-summand `extensionByZeroStageToStalks X p U G V y` is the germ at
`y` into the stalk of `G` at `p.over x`, followed by the `x`-th summand inclusion. -/
lemma extensionByZeroStageToStalks_comp_embedding_of_eq (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) (V : X.C)
    (y : p.fiber.obj V) (φ : V ⟶ U) (x : p.fiber.obj U)
    (h : p.fiber.map φ y = x) :
    extensionByZeroSectionEmbedding X U G V φ ≫
        extensionByZeroStageToStalks X p U G V y =
      (p.over x).toPresheafFiber (Over.mk φ)
          (by
            change (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj (Over.mk φ)
            exact ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 h⟩)
          G.val.presheaf ≫
        Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) x := by
  cases h
  exact extensionByZeroStageToStalks_comp_embedding X p U G V y φ

/-- The maps `extensionByZeroStageToStalks` are compatible with restriction along `f : W ⟶ V`. -/
lemma extensionByZeroStageToStalks_naturality (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {V W : X.C} (f : W ⟶ V) (y : p.fiber.obj W) :
    (extensionByZeroPresheaf X U G).presheaf.map f.op ≫
        extensionByZeroStageToStalks X p U G W y =
      extensionByZeroStageToStalks X p U G V (p.fiber.map f y) := by
  refine hom_ext_of_sectionEmbedding X U G V fun φ => ?_
  rw [← Category.assoc, extensionByZeroSectionEmbedding_naturality]
  generalize hx : p.fiber.map φ (p.fiber.map f y) = x at ⊢
  conv_lhs => rw [Category.assoc]
  have hW : p.fiber.map (f ≫ φ) y = x :=
    (ConcreteCategory.congr_hom (p.fiber.map_comp f φ) y).trans hx
  let q := p.over x
  let hyW : (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj
      (Over.mk (f ≫ φ)) :=
    ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 hW⟩
  let hyV : (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj
      (Over.mk φ) :=
    ⟨p.fiber.map f y,
      (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 hx⟩
  let g : Over.mk (f ≫ φ) ⟶ Over.mk φ := Over.homMk f rfl
  have hmap : q.fiber.map g hyW = hyV := Subtype.ext rfl
  rw [extensionByZeroStageToStalks_comp_embedding_of_eq X p U G W y (f ≫ φ) x hW,
    extensionByZeroStageToStalks_comp_embedding_of_eq X p U G V (p.fiber.map f y) φ x hx]
  have hsection : G.val.presheaf.map g.op ≫
      q.toPresheafFiber (Over.mk (f ≫ φ)) hyW G.val.presheaf =
    q.toPresheafFiber (Over.mk φ) hyV G.val.presheaf :=
    (q.toPresheafFiber_w g hyW G.val.presheaf).trans
      (congrArg (fun z => q.toPresheafFiber (Over.mk φ) z G.val.presheaf) hmap)
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫
    Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) x)
      hsection

/-- The map from the stalk at `p` of `extensionByZeroPresheaf X U G` to
`stalkExtensionByZeroTarget X p U G` induced by the maps `extensionByZeroStageToStalks`. -/
noncomputable def stalkExtensionByZeroForward (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf ⟶
      stalkExtensionByZeroTarget X p U G :=
  p.presheafFiberDesc
    (fun V y => extensionByZeroStageToStalks X p U G V y)
    (fun {_V _W} f y => extensionByZeroStageToStalks_naturality X p U G f y)

/-- The map from the stalk of `G` at `p.over x` to the stalk at `p` of
`extensionByZeroPresheaf X U G` induced by the section embeddings. -/
noncomputable def stalkExtensionByZeroBackwardComponent
    (X : RingedSite.{u, u, u}) (p : GrothendieckTopology.Point.{u, u, u} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (x : p.fiber.obj U) :
    (p.over x).presheafFiber.obj G.val.presheaf ⟶
      p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf := by
  let q := p.over x
  refine q.presheafFiberDesc (fun W w => ?_) ?_
  · exact extensionByZeroSectionEmbedding X U G W.left W.hom ≫
      p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf
  · intro W W' g w
    change (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj W at w
    let f := g.left
    have hval : (q.fiber.map g w).1 = p.fiber.map f w.1 := by
      change ((FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.map g w).1 = _
      rfl
    calc
      _ = (G.val.presheaf.map g.op ≫
          extensionByZeroSectionEmbedding X U G W.left W.hom) ≫
            p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf := by
              simp only [Category.assoc]
      _ = (extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
          (extensionByZeroPresheaf X U G).presheaf.map f.op) ≫
            p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf :=
              congrArg (fun k => k ≫
                p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf)
                (extensionByZeroSectionEmbedding_over_naturality X U G g).symm
      _ = extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
          p.toPresheafFiber W'.left (p.fiber.map f w.1)
            (extensionByZeroPresheaf X U G).presheaf := by
              calc
                _ = extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
                    ((extensionByZeroPresheaf X U G).presheaf.map f.op ≫
                      p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf) := by
                        simp only [Category.assoc]
                _ = _ := congrArg (fun k =>
                  extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫ k)
                    (p.toPresheafFiber_w f w.1 (extensionByZeroPresheaf X U G).presheaf)
      _ = _ := congrArg (fun z => extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
        p.toPresheafFiber W'.left z (extensionByZeroPresheaf X U G).presheaf) hval.symm

/-- The map from `stalkExtensionByZeroTarget X p U G` to the stalk at `p` of
`extensionByZeroPresheaf X U G` with components `stalkExtensionByZeroBackwardComponent`. -/
noncomputable def stalkExtensionByZeroBackward (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    stalkExtensionByZeroTarget X p U G ⟶
      p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf :=
  Sigma.desc (fun x => stalkExtensionByZeroBackwardComponent X p U G x)

/-- `stalkExtensionByZeroBackwardComponent` sends the germ at `w` of a section of `G` over `W` to
the germ at `w` of its image under the section embedding. -/
lemma stalkExtensionByZeroBackwardComponent_toPresheafFiber
    (X : RingedSite.{u, u, u}) (p : GrothendieckTopology.Point.{u, u, u} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (x : p.fiber.obj U) (W : Over U) (w : (p.over x).fiber.obj W) :
    (p.over x).toPresheafFiber W w G.val.presheaf ≫
        stalkExtensionByZeroBackwardComponent X p U G x =
      extensionByZeroSectionEmbedding X U G W.left W.hom ≫
        p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf := by
  unfold stalkExtensionByZeroBackwardComponent
  exact (p.over x).toPresheafFiber_presheafFiberDesc _ _ W w

/-- `extensionByZeroStageToStalks X p U G V y` followed by `stalkExtensionByZeroBackward` is the
germ map at `y` of `extensionByZeroPresheaf X U G`. -/
lemma stalkExtensionByZeroStageToStalks_comp_backward
    (X : RingedSite.{u, u, u}) (p : GrothendieckTopology.Point.{u, u, u} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C)
    (y : p.fiber.obj V) :
    extensionByZeroStageToStalks X p U G V y ≫
        stalkExtensionByZeroBackward X p U G =
      p.toPresheafFiber V y (extensionByZeroPresheaf X U G).presheaf := by
  refine hom_ext_of_sectionEmbedding X U G V fun φ => ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ stalkExtensionByZeroBackward X p U G)
    (extensionByZeroStageToStalks_comp_embedding X p U G V y φ)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  rw [stalkExtensionByZeroBackward, Sigma.ι_desc]
  exact stalkExtensionByZeroBackwardComponent_toPresheafFiber X p U G _ (Over.mk φ) _

/-- The germ map at `y` of `extensionByZeroPresheaf X U G` followed by
`stalkExtensionByZeroForward` is `extensionByZeroStageToStalks X p U G V y`. -/
lemma stalkExtensionByZeroForward_toPresheafFiber
    (X : RingedSite.{u, u, u}) (p : GrothendieckTopology.Point.{u, u, u} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) (y : p.fiber.obj V) :
    p.toPresheafFiber V y (extensionByZeroPresheaf X U G).presheaf ≫
        stalkExtensionByZeroForward X p U G =
      extensionByZeroStageToStalks X p U G V y := by
  unfold stalkExtensionByZeroForward
  exact p.toPresheafFiber_presheafFiberDesc _ _ V y

/-- `stalkExtensionByZeroBackward` followed by `stalkExtensionByZeroForward` is the identity. -/
lemma stalkExtensionByZeroBackward_hom (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    stalkExtensionByZeroBackward X p U G ≫ stalkExtensionByZeroForward X p U G =
      𝟙 (stalkExtensionByZeroTarget X p U G) := by
  apply Sigma.hom_ext
  intro x
  apply (p.over x).presheafFiber_hom_ext
  intro W wq
  obtain ⟨V, ⟨⟨⟩⟩, φ⟩ := W
  let w : (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj (Over.mk φ) := wq
  calc
    _ = (p.over x).toPresheafFiber (Over.mk φ) wq G.val.presheaf ≫
        (Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) x ≫
          stalkExtensionByZeroBackward X p U G) ≫ stalkExtensionByZeroForward X p U G := by
            simp only [Category.assoc]
            rfl
    _ = (p.over x).toPresheafFiber (Over.mk φ) wq G.val.presheaf ≫
        (stalkExtensionByZeroBackwardComponent X p U G x ≫
          stalkExtensionByZeroForward X p U G) := by
            rw [stalkExtensionByZeroBackward, Sigma.ι_desc]
    _ = (extensionByZeroSectionEmbedding X U G V φ ≫
        p.toPresheafFiber V w.1 (extensionByZeroPresheaf X U G).presheaf) ≫
          stalkExtensionByZeroForward X p U G := by
            rw [← Category.assoc,
              stalkExtensionByZeroBackwardComponent_toPresheafFiber X p U G x (Over.mk φ) wq]
            rfl
    _ = extensionByZeroSectionEmbedding X U G V φ ≫
        extensionByZeroStageToStalks X p U G V w.1 := by
            rw [Category.assoc, stalkExtensionByZeroForward_toPresheafFiber]
    _ = (p.over x).toPresheafFiber (Over.mk φ) wq G.val.presheaf ≫
        Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) x := by
            rw [extensionByZeroStageToStalks_comp_embedding_of_eq X p U G V w.1 φ x]
            · rfl
            · exact (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 w.2

/-- `stalkExtensionByZeroForward` followed by `stalkExtensionByZeroBackward` is the identity. -/
lemma stalkExtensionByZeroForward_hom (X : RingedSite.{u, u, u})
    (p : GrothendieckTopology.Point.{u, u, u} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    stalkExtensionByZeroForward X p U G ≫ stalkExtensionByZeroBackward X p U G =
      𝟙 (p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf) := by
  apply p.presheafFiber_hom_ext
  intro V y
  calc
    _ = extensionByZeroStageToStalks X p U G V y ≫
        stalkExtensionByZeroBackward X p U G := by
            rw [← Category.assoc, stalkExtensionByZeroForward_toPresheafFiber]
    _ = p.toPresheafFiber V y (extensionByZeroPresheaf X U G).presheaf :=
      stalkExtensionByZeroStageToStalks_comp_backward X p U G V y

/-- The stalk of extension by zero from `C/U` is the direct sum of the stalks
at the points of `C/U` above the given point. -/
@[stacks 0710]
noncomputable def stalkExtensionByZeroIso
    (X : RingedSite.{u, u, u}) (p : GrothendieckTopology.Point.{u, u, u} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (p.presheafFiber.obj (((SheafOfModules.pullback.{u}
      (F := Over.forget U)
        (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj G).val.presheaf)) ≅
      ∐ fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf := by
  letI := ringedSitePresheafRestrictionIsRightAdjoint X U
  refine p.presheafFiber.mapIso
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          PresheafOfModules.toPresheaf _).mapIso
        ((SheafOfModules.pullbackIso.{u}
          (F := Over.forget U)
            (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).app G)) ≪≫ ?_
  refine p.presheafFiber.mapIso
      ((PresheafOfModules.sheafificationCompForgetCompToPresheaf
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).app
          (extensionByZeroPresheaf X U G)) ≪≫ ?_
  refine (p.presheafToSheafCompSheafFiberIso AddCommGrpCat).app
      (extensionByZeroPresheaf X U G).presheaf ≪≫ ?_
  exact
    { hom := stalkExtensionByZeroForward X p U G
      inv := stalkExtensionByZeroBackward X p U G
      hom_inv_id := stalkExtensionByZeroForward_hom X p U G
      inv_hom_id := stalkExtensionByZeroBackward_hom X p U G }

end Stacks.Sites.ExtensionByZero
