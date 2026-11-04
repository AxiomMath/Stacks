module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksCore.CategoryTheory.Sites.Point.StalkAsColimit
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Point.OverBijection

/-!
# The stalk of an extension by zero, over a site with large objects

Let `(C, O)` be a ringed site whose objects form a type in an arbitrary universe `c` while its
morphisms, its structure rings and its module sections all live in one universe `u`, let `U` be
an object of `C` and let `p` be a point of `C`. For a sheaf of modules `G` on the localized
ringed site `C/U`, the stalk at `p` of the extension by zero `j_{U!}G` is the direct sum of the
stalks of `G` at the points of `C/U` lying over `p`. Those points are indexed by the fibre
`p(U)` of `p` at `U`, the point attached to `x ∈ p(U)` being `p.over x`. This is Stacks 0710.

## Main results

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.stalkExtensionByZeroIso`: the stalk of an
  extension by zero is the direct sum of the stalks above the point.

## Implementation notes

This restates `Stacks.Sites.ExtensionByZero.stalkExtensionByZeroIso` with the universe of the
objects of the site freed from the universe of its morphisms, everything else staying in the
single universe `u`. The reason is that the small étale ringed site of an algebraic space has
its objects one universe above its morphisms: it is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, so the single-universe statement cannot be
instantiated at it, and the module stalk available there is the "large" one,
`Stacks.moduleStalkLarge`, whose sections are raised by `ULift`.

Nothing in the proof is sensitive to the universe of the objects, and the only hypothesis the
generalization costs is essential `u`-smallness of `C`:

* the direct-sum formula for the sections of the presheaf computing `j_{U!}G` (Stacks 03DI) is
  taken from `Stacks.Sites.ExtensionByZero.OfEssentiallySmall`, which is exactly that
  restatement; the coproducts it involves are indexed by the hom-set `V ⟶ U`, which lies in
  `Type u` whatever the universe of the objects;
* the stalk itself is `CategoryTheory.GrothendieckTopology.Point.presheafFiber`, a colimit over
  the category of elements of the fibre functor. That category has large objects too, but a
  point of a site carries `CategoryTheory.GrothendieckTopology.Point.initiallySmall`, so the
  colimit is one of `u`-small shape after passing to an initial model and exists in
  `AddCommGrpCat.{u}`; this is why no universe lift is needed here;
* the index set `p.fiber.obj U` of the direct sum of stalks lies in `Type u`, so that
  coproduct, too, exists in `AddCommGrpCat.{u}`.

## References

* [Stacks Project, Tag 0710](https://stacks.math.columbia.edu/tag/0710)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

open AlgebraicGeometry

universe u c

/-- The restriction of presheaves of modules from `C` to the localized site `C/U`, the
pushforward along `Over.forget U`, is a right adjoint. -/
local instance ringedSitePresheafRestrictionIsRightAdjoint (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C] (U : X.C) :
    (PresheafOfModules.pushforward.{u} (F := Over.forget U)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) :
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).hom).IsRightAdjoint :=
  presheafRestrictionSheafIsRightAdjoint X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U

/-- The presheaf of modules whose sheafification is the extension by zero `j_{U!}G`. -/
noncomputable abbrev extensionByZeroPresheaf (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
  (PresheafOfModules.pullback.{u} (F := Over.forget U)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) :
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).hom).obj G.val

/-- The Stacks 03DI direct-sum formula for the sections of `extensionByZeroPresheaf` over an
object `V` of the site, restated for a ringed site. -/
noncomputable def ringedSiteSectionIso (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) :
    (extensionByZeroPresheaf X U G).obj (op V) ≅
      ∐ extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V :=
  extensionByZeroPresheafSectionIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V

/-- The inclusion of the summand indexed by `φ : V ⟶ U` into the sections of
`extensionByZeroPresheaf` over `V`, on underlying abelian groups. -/
noncomputable def extensionByZeroSectionEmbedding (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) (φ : V ⟶ U) :
    G.val.presheaf.obj (op (Over.mk φ)) ⟶
      (extensionByZeroPresheaf X U G).presheaf.obj (op V) :=
  (forget₂ _ AddCommGrpCat).map
    (Sigma.ι (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V) φ ≫
      (ringedSiteSectionIso X U G V).inv)

/-- The summand inclusions are compatible with restriction along `f : W ⟶ V`, where the summand
of `W` is indexed by any `ψ` equal to `f ≫ φ`. -/
private lemma extensionByZeroSectionEmbedding_naturality_of_comp_eq
    (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {V W : X.C} (f : W ⟶ V) (φ : V ⟶ U) (ψ : W ⟶ U) (h : f ≫ φ = ψ) :
    extensionByZeroSectionEmbedding X U G V φ ≫
        (extensionByZeroPresheaf X U G).presheaf.map f.op =
      G.val.presheaf.map (Over.homMk f h : Over.mk ψ ⟶ Over.mk φ).op ≫
        extensionByZeroSectionEmbedding X U G W ψ := by
  subst h
  let adj := PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := Over.forget U) (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) :
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).hom
  dsimp only [extensionByZeroSectionEmbedding, ringedSiteSectionIso,
    extensionByZeroPresheaf]
  rw [congrArg (fun t => (forget₂ _ AddCommGrpCat).map t) (eq_of_heq
      (extensionByZeroPresheafSectionIso_inv_ι X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V φ)),
    congrArg (fun t => (forget₂ _ AddCommGrpCat).map t) (eq_of_heq
      (extensionByZeroPresheafSectionIso_inv_ι X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G W (f ≫ φ)))]
  ext s
  exact (PresheafOfModules.naturality_apply (adj.unit.app G.val)
    (Over.homMk f rfl : Over.mk (f ≫ φ) ⟶ Over.mk φ).op s).symm


/-- The summand inclusions are compatible with restriction along a morphism of the site: the
summand indexed by `φ` is carried into the summand indexed by `f ≫ φ`. -/
lemma extensionByZeroSectionEmbedding_naturality (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {V W : X.C} (f : W ⟶ V) (φ : V ⟶ U) :
    extensionByZeroSectionEmbedding X U G V φ ≫
        (extensionByZeroPresheaf X U G).presheaf.map f.op =
      G.val.presheaf.map (Over.homMk f rfl : Over.mk (f ≫ φ) ⟶ Over.mk φ).op ≫
        extensionByZeroSectionEmbedding X U G W (f ≫ φ) := by
  exact extensionByZeroSectionEmbedding_naturality_of_comp_eq X U G f φ _ rfl

/-- The summand inclusions are compatible with restriction along a morphism of the localized
site, which is `extensionByZeroSectionEmbedding_naturality` read on `Over U`. -/
lemma extensionByZeroSectionEmbedding_over_naturality (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {W W' : Over U} (g : W ⟶ W') :
    extensionByZeroSectionEmbedding X U G W'.left W'.hom ≫
        (extensionByZeroPresheaf X U G).presheaf.map g.left.op =
      G.val.presheaf.map g.op ≫
        extensionByZeroSectionEmbedding X U G W.left W.hom := by
  exact extensionByZeroSectionEmbedding_naturality_of_comp_eq X U G g.left W'.hom _ (Over.w g)

/-- The direct sum, over the fibre of `p` at `U`, of the stalks of `G` at the points of the
localized site above `p`. -/
noncomputable abbrev stalkExtensionByZeroTarget (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
      AddCommGrpCat :=
  ∐ fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf

/-- The map into the direct sum of stalks attached to a neighbourhood `(V, y)` of `p`: on the
summand indexed by `φ : V ⟶ U` it is the canonical map into the stalk of `G` at
`p.over (p(φ) y)`, followed by the inclusion of that summand. -/
noncomputable def extensionByZeroStageToStalks (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
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
  have qy : (p.over x).fiber.obj (Over.mk φ) := by
    change (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj (Over.mk φ)
    exact ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl⟩
  exact (p.over x).toPresheafFiber (Over.mk φ) qy G.val.presheaf ≫
    Sigma.ι (fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf) x

/-- Forgetting the module structures carries the inclusion of the `φ`-summand to the inclusion
of the `φ`-summand. -/
lemma extensionByZeroSumForgetIso_hom_ι (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C)
    (φ : V ⟶ U) :
    (forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat).map
        (Sigma.ι (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V)
          φ) ≫
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
          (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V ψ))
        φ := by
  let F := forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
    AddCommGrpCat
  let S := extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V
  let e := F.mapIso (Sigma.isoColimit (Discrete.functor S)) ≪≫
    preservesColimitIso F (Discrete.functor S) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete S F) ≪≫
    (Sigma.isoColimit (Discrete.functor (fun ψ : V ⟶ U => F.obj (S ψ)))).symm
  change F.map (Sigma.ι S φ) ≫ e.hom = _
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

/-- Forgetting the module structures commutes with the direct sum of the summands: the
underlying abelian group of `∐ extensionByZeroSummands` is the direct sum of the underlying
abelian groups. -/
noncomputable def extensionByZeroSumForgetIso (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
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

/-- The inverse of `extensionByZeroSumForgetIso` carries the inclusion of the `φ`-summand to
the image under the forgetful functor of the inclusion of the `φ`-summand. -/
lemma extensionByZeroSumForgetIso_inv_ι (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
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
      (Sigma.ι (extensionByZeroSummands X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G V)
        φ) :=
  (Iso.comp_inv_eq _).2 (extensionByZeroSumForgetIso_hom_ι X U G V φ).symm

/-- The summand inclusion of the section embedding: composing the `φ`-inclusion into the direct
sum of the underlying abelian groups with the two comparison isomorphisms gives exactly
`extensionByZeroSectionEmbedding`. -/
lemma sigmaι_comp_forgetIso_inv_sectionIso_inv (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
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
  exact (Functor.map_comp _ _ _).symm

/-- On the summand indexed by `φ : V ⟶ U`, the map into the direct sum of stalks attached to
`(V, y)` is the canonical map into the stalk at `p.over (p(φ) y)` followed by the inclusion of
that summand. -/
lemma extensionByZeroStageToStalks_comp_embedding (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
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
  let e := extensionByZeroSumForgetIso X U G V
  let st := ringedSiteSectionIso X U G V
  let component : ∀ ψ : V ⟶ U,
      F.obj (S ψ) ⟶ stalkExtensionByZeroTarget X p U G := fun ψ =>
    let xψ := p.fiber.map ψ y
    let hyψ : (p.over xψ).fiber.obj (Over.mk ψ) := by
      change (FunctorToTypes.fromOverSubfunctor p.fiber xψ).toFunctor.obj (Over.mk ψ)
      exact ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl⟩
    (p.over xψ).toPresheafFiber (Over.mk ψ) hyψ G.val.presheaf ≫
      Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) xψ
  change F.map (Sigma.ι S φ ≫ st.inv) ≫ F.map st.hom ≫ e.hom ≫
      Sigma.desc component = component φ
  calc
    _ = F.map (Sigma.ι S φ) ≫ e.hom ≫ Sigma.desc component := by simp
    _ = Sigma.ι (fun ψ : V ⟶ U => F.obj (S ψ)) φ ≫ Sigma.desc component :=
      congrArg (fun g => g ≫ Sigma.desc component)
        (extensionByZeroSumForgetIso_hom_ι X U G V φ :
          F.map (Sigma.ι S φ) ≫ e.hom = Sigma.ι (fun ψ : V ⟶ U => F.obj (S ψ)) φ)
    _ = component φ := by simp [component]

/-- `extensionByZeroStageToStalks_comp_embedding` with the index of the summand presented as an
arbitrary element of the fibre equal to `p(φ) y`. -/
lemma extensionByZeroStageToStalks_comp_embedding_of_eq (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
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

/-- Two maps out of the sections over `V` agree if they agree on each summand inclusion. -/
private lemma extensionByZeroSectionEmbedding_hom_ext (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C] (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) (V : X.C)
    {T : AddCommGrpCat} {a b : (extensionByZeroPresheaf X U G).presheaf.obj (op V) ⟶ T}
    (h : ∀ φ : V ⟶ U, extensionByZeroSectionEmbedding X U G V φ ≫ a =
      extensionByZeroSectionEmbedding X U G V φ ≫ b) : a = b := by
  apply (cancel_epi ((extensionByZeroSumForgetIso X U G V).inv ≫
    ((forget₂ (ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)))
      AddCommGrpCat).mapIso (ringedSiteSectionIso X U G V)).inv)).mp
  refine Sigma.hom_ext _ _ fun φ => ?_
  have hι := sigmaι_comp_forgetIso_inv_sectionIso_inv X U G V φ
  exact (Category.assoc _ _ _).symm.trans <| (hι =≫ a).trans <| (h φ).trans <|
    (hι.symm =≫ b).trans (Category.assoc _ _ _)

/-- Restriction along `f : W ⟶ V` is compatible with the maps into the direct sum of stalks on
the summand of the sections indexed by `φ : V ⟶ U`. -/
private lemma extensionByZeroSectionEmbedding_comp_stageToStalks_naturality
    (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {V W : X.C} (f : W ⟶ V) (y : p.fiber.obj W) (φ : V ⟶ U) :
    extensionByZeroSectionEmbedding X U G V φ ≫
      (extensionByZeroPresheaf X U G).presheaf.map f.op ≫
        extensionByZeroStageToStalks X p U G W y =
      extensionByZeroSectionEmbedding X U G V φ ≫
        extensionByZeroStageToStalks X p U G V (p.fiber.map f y) := by
  rw [← Category.assoc, extensionByZeroSectionEmbedding_naturality]
  generalize hx : p.fiber.map φ (p.fiber.map f y) = x
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
  rw [extensionByZeroStageToStalks_comp_embedding_of_eq X p U G W y (f ≫ φ) x hW,
    extensionByZeroStageToStalks_comp_embedding_of_eq X p U G V (p.fiber.map f y) φ x hx,
    ← Category.assoc]
  exact (q.toPresheafFiber_w g hyW G.val.presheaf : G.val.presheaf.map g.op ≫
      q.toPresheafFiber (Over.mk (f ≫ φ)) hyW G.val.presheaf =
    q.toPresheafFiber (Over.mk φ) hyV G.val.presheaf) =≫ _

/-- The maps into the direct sum of stalks are compatible with restriction along a morphism of
neighbourhoods of `p`, so they form a cocone over the category of elements of the fibre
functor. -/
lemma extensionByZeroStageToStalks_naturality (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {V W : X.C} (f : W ⟶ V) (y : p.fiber.obj W) :
    (extensionByZeroPresheaf X U G).presheaf.map f.op ≫
        extensionByZeroStageToStalks X p U G W y =
      extensionByZeroStageToStalks X p U G V (p.fiber.map f y) := by
  refine extensionByZeroSectionEmbedding_hom_ext X U G V fun φ => ?_
  rw [← Category.assoc]
  exact extensionByZeroSectionEmbedding_comp_stageToStalks_naturality X p U G f y φ

/-- The map from the stalk of `extensionByZeroPresheaf` to the direct sum of the stalks of `G`
above `p`, given by `extensionByZeroStageToStalks` on each neighbourhood. -/
noncomputable def stalkExtensionByZeroForward (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf ⟶
      stalkExtensionByZeroTarget X p U G :=
  p.presheafFiberDesc
    (fun V y => extensionByZeroStageToStalks X p U G V y)
    (fun {_V _W} f y => extensionByZeroStageToStalks_naturality X p U G f y)

/-- The summand of the inverse map indexed by `x ∈ p(U)`: on a neighbourhood `(W, w)` of
`p.over x` it is the inclusion of the summand of the sections indexed by `W.hom`, followed by
the canonical map into the stalk at `p`. -/
noncomputable def stalkExtensionByZeroBackwardComponent
    (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (x : p.fiber.obj U) :
    (p.over x).presheafFiber.obj G.val.presheaf ⟶
      p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf := by
  let q := p.over x
  refine q.presheafFiberDesc (fun W w => extensionByZeroSectionEmbedding X U G W.left W.hom ≫
    p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf) ?_
  intro W W' g w
  change (FunctorToTypes.fromOverSubfunctor p.fiber x).toFunctor.obj W at w
  let f := g.left
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
      rw [Category.assoc, p.toPresheafFiber_w f w.1 (extensionByZeroPresheaf X U G).presheaf]
    _ = _ := rfl

/-- The map from the direct sum of the stalks of `G` above `p` to the stalk of
`extensionByZeroPresheaf`, given by `stalkExtensionByZeroBackwardComponent` on each
summand. -/
noncomputable def stalkExtensionByZeroBackward (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    stalkExtensionByZeroTarget X p U G ⟶
      p.presheafFiber.obj (extensionByZeroPresheaf X U G).presheaf :=
  Sigma.desc (fun x => stalkExtensionByZeroBackwardComponent X p U G x)

/-- The defining property of `stalkExtensionByZeroBackwardComponent` on a neighbourhood of
`p.over x`. -/
lemma stalkExtensionByZeroBackwardComponent_toPresheafFiber
    (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (x : p.fiber.obj U) (W : Over U) (w : (p.over x).fiber.obj W) :
    (p.over x).toPresheafFiber W w G.val.presheaf ≫
        stalkExtensionByZeroBackwardComponent X p U G x =
      extensionByZeroSectionEmbedding X U G W.left W.hom ≫
        p.toPresheafFiber W.left w.1 (extensionByZeroPresheaf X U G).presheaf := by
  unfold stalkExtensionByZeroBackwardComponent
  exact (p.over x).toPresheafFiber_presheafFiberDesc _ _ W w

/-- Composing the map attached to a neighbourhood `(V, y)` of `p` with the inverse map gives
back the canonical map from the sections over `V` into the stalk at `p`. -/
lemma stalkExtensionByZeroStageToStalks_comp_backward
    (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C)
    (y : p.fiber.obj V) :
    extensionByZeroStageToStalks X p U G V y ≫
        stalkExtensionByZeroBackward X p U G =
      p.toPresheafFiber V y (extensionByZeroPresheaf X U G).presheaf := by
  refine extensionByZeroSectionEmbedding_hom_ext X U G V fun φ => ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ stalkExtensionByZeroBackward X p U G)
    (extensionByZeroStageToStalks_comp_embedding X p U G V y φ)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  rw [stalkExtensionByZeroBackward, Sigma.ι_desc]
  exact stalkExtensionByZeroBackwardComponent_toPresheafFiber X p U G _ (Over.mk φ) _

/-- The defining property of `stalkExtensionByZeroForward` on a neighbourhood of `p`. -/
lemma stalkExtensionByZeroForward_toPresheafFiber
    (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (V : X.C) (y : p.fiber.obj V) :
    p.toPresheafFiber V y (extensionByZeroPresheaf X U G).presheaf ≫
        stalkExtensionByZeroForward X p U G =
      extensionByZeroStageToStalks X p U G V y :=
  p.toPresheafFiber_presheafFiberDesc _ _ V y

/-- The two maps compose to the identity of the direct sum of stalks. -/
lemma stalkExtensionByZeroBackward_hom (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    stalkExtensionByZeroBackward X p U G ≫ stalkExtensionByZeroForward X p U G =
      𝟙 (stalkExtensionByZeroTarget X p U G) := by
  refine Sigma.hom_ext _ _ fun x => ?_
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
            rw [← Category.assoc, stalkExtensionByZeroBackwardComponent_toPresheafFiber]
            rfl
    _ = extensionByZeroSectionEmbedding X U G V φ ≫
        extensionByZeroStageToStalks X p U G V w.1 := by
            rw [Category.assoc, stalkExtensionByZeroForward_toPresheafFiber]
    _ = (p.over x).toPresheafFiber (Over.mk φ) wq G.val.presheaf ≫
        Sigma.ι (fun z : p.fiber.obj U => (p.over z).presheafFiber.obj G.val.presheaf) x := by
            rw [extensionByZeroStageToStalks_comp_embedding_of_eq X p U G V w.1 φ x]
            · rfl
            · exact (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 w.2

/-- The two maps compose to the identity of the stalk of `extensionByZeroPresheaf`. -/
lemma stalkExtensionByZeroForward_hom (X : RingedSite.{c, u, u})
    [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J) (U : X.C)
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
at the points of `C/U` above the given point, for a ringed site whose objects may live in a
universe above its morphisms, structure rings and module sections. -/
@[stacks 0710]
noncomputable def stalkExtensionByZeroIso
    (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (p : GrothendieckTopology.Point.{u, u, c} X.J)
    (U : X.C) (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (p.presheafFiber.obj (((SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
        G).val.presheaf)) ≅
      ∐ fun x : p.fiber.obj U => (p.over x).presheafFiber.obj G.val.presheaf := by
  letI := ringedSitePresheafRestrictionIsRightAdjoint X U
  refine p.presheafFiber.mapIso
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        PresheafOfModules.toPresheaf _).mapIso
        ((SheafOfModules.pullbackIso.{u}
          (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).app G)) ≪≫
            ?_
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

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall
