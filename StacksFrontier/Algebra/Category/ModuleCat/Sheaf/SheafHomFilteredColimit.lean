module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPostcomposition
public import
  StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Internal hom out of a finitely presented module commutes with filtered colimits

Let `(X, O_X)` be a ringed space, let `F` be an `O_X`-module of finite presentation and let
`G = colim_λ G_λ` be a filtered colimit of `O_X`-modules. The canonical map

`colim_λ SheafHom_{O_X}(F, G_λ) ⟶ SheafHom_{O_X}(F, G)`

is an isomorphism: the cocone of internal homs whose legs are the postcomposition maps induced
by the colimit inclusions is itself a colimit cocone.

## Main definitions

* `Stacks.SheafOfModules.opensRingedSite`: a ringed space read as a ringed site.
* `Stacks.SheafOfModules.ihomFunctor`: internal hom out of a fixed module, as a functor in the
  target, on a ringed space.
* `Stacks.SheafOfModules.canonicalSheafHom`: the value of that functor, together with the
  identification of its sections with the module maps of the restrictions.
* `Stacks.SheafOfModules.sheafHomDiagram` and `Stacks.SheafOfModules.sheafHomCocone`: for a
  diagram of modules with a chosen internal hom for each term, the diagram of internal homs
  with the postcomposition transition maps, and its canonical cocone over the internal hom of
  the colimit.

## Main results

* `Stacks.SheafOfModules.preservesColimitsOfShape_ihomFunctor`: `SheafHom_{O_X}(F, -)` preserves
  colimits of filtered shape.
* `Stacks.SheafOfModules.isColimit_sheafHomCocone`: the canonical cocone is a colimit cocone.
* `Stacks.SheafOfModules.isIso_desc_sheafHomCocone`: equivalently, the canonical map out of any
  colimit of the diagram of internal homs is an isomorphism.

## References

* [Stacks Project, Tag 0GMV](https://stacks.math.columbia.edu/tag/0GMV)
* [Stacks Project, Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- A ringed space read as a ringed site: the site of its open subsets with the open-cover
topology, carrying the same structure sheaf. -/
abbrev opensRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := Opens ↑X
  J := Opens.grothendieckTopology ↑X
  O := Rc

/-- **Internal hom out of a fixed module on a ringed space**, as a functor in the target: it
sends `G` to `SheafHom_{O_X}(F, G)` and a map `G ⟶ G₁` to postcomposition with it. -/
noncomputable abbrev ihomFunctor (F : SheafOfModules.{u} (structureSheaf Rc)) :
    SheafOfModules.{u} (structureSheaf Rc) ⥤ SheafOfModules.{u} (structureSheaf Rc) :=
  InternalHom.internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology ↑X) Rc F

variable {Rc}

/-- `SheafHom_{O_X}(F, G)` together with the identification of its sections over an open `U`
with the `O_U`-module maps `F|_U ⟶ G|_U`: the internal hom sheaf of Stacks 03EM, read as the
characterising data of Stacks 01CO. -/
noncomputable def canonicalSheafHom (F G : SheafOfModules.{u} (structureSheaf Rc)) :
    SheafHom Rc F G where
  obj := (ihomFunctor Rc F).obj G
  sectionsEquiv U :=
    { toEquiv := ((SheafOfModules.fullyFaithfulForget ((structureSheaf Rc).over U)).homEquiv
        (X := F.over U) (Y := G.over U)).symm
      map_add' := by intros; rfl }
  restrict_natural := by intros; rfl
  smul_natural := by intros; rfl

/-- The functor `SheafHom_{O_X}(F, -)` acts on morphisms by postcomposition. -/
lemma isPostcomp_ihomFunctor_map (F : SheafOfModules.{u} (structureSheaf Rc))
    {G G₁ : SheafOfModules.{u} (structureSheaf Rc)} (u : G ⟶ G₁) :
    SheafHom.IsPostcomp Rc u (canonicalSheafHom F G) (canonicalSheafHom F G₁)
      ((ihomFunctor Rc F).map u) := by
  intro _ _; rfl

/-- The functor `SheafHom_{O_X}(F, -)` acts on morphisms as `SheafHom.postcomp`. -/
lemma ihomFunctor_map_eq_postcomp (F : SheafOfModules.{u} (structureSheaf Rc))
    {G G₁ : SheafOfModules.{u} (structureSheaf Rc)} (u : G ⟶ G₁) :
    (ihomFunctor Rc F).map u =
      SheafHom.postcomp u (canonicalSheafHom F G) (canonicalSheafHom F G₁) :=
  SheafHom.eq_postcomp_of_isPostcomp (isPostcomp_ihomFunctor_map F u)

variable {K : Type u} [Category.{u} K] (F : SheafOfModules.{u} (structureSheaf Rc))
  (D : K ⥤ SheafOfModules.{u} (structureSheaf Rc))

/-- **Internal hom out of a module of finite presentation commutes with filtered colimits**, in
functorial form: on a ringed space, `SheafHom_{O_X}(F, -)` preserves colimits of filtered shape.
This is Stacks 0GMZ read on the site of opens of the space. -/
theorem preservesColimitsOfShape_ihomFunctor [F.IsFinitePresentation] [IsFiltered K] :
    PreservesColimitsOfShape K (ihomFunctor Rc F) :=
  @InternalHom.internalHomSecondFunctor_preservesFilteredColimits (opensRingedSite Rc) F
    ‹F.IsFinitePresentation› K _ _

/-- **The diagram of internal homs.** Given a diagram `λ ↦ G_λ` of `O_X`-modules and a choice
of internal hom `SheafHom_{O_X}(F, G_λ)` for each term, the diagram `λ ↦ SheafHom_{O_X}(F, G_λ)`
whose transition maps are the canonical postcomposition maps. -/
noncomputable def sheafHomDiagram (H : ∀ j, SheafHom Rc F (D.obj j)) :
    K ⥤ SheafOfModules.{u} (structureSheaf Rc) where
  obj j := (H j).obj
  map f := SheafHom.postcomp (D.map f) (H _) (H _)
  map_id j := by
    rw [D.map_id]
    exact SheafHom.postcomp_id (H j)
  map_comp f g := by
    rw [D.map_comp]
    exact SheafHom.postcomp_comp _ _ _ _ _

/-- The transition map of `sheafHomDiagram F D H` along `f : i ⟶ j` is the postcomposition map
induced by `D.map f`. -/
@[simp]
lemma sheafHomDiagram_map (H : ∀ j, SheafHom Rc F (D.obj j)) {i j : K} (f : i ⟶ j) :
    (sheafHomDiagram F D H).map f = SheafHom.postcomp (D.map f) (H i) (H j) :=
  rfl

/-- **The canonical cocone.** The cocone on the diagram of internal homs whose point is
`SheafHom_{O_X}(F, colim G)` and whose leg at `λ` is the postcomposition map induced by the
colimit inclusion `G_λ ⟶ colim G`. Its `desc` out of a colimit is the canonical comparison map
of Stacks 0GMV. -/
noncomputable def sheafHomCocone (c : Cocone D) (H : ∀ j, SheafHom Rc F (D.obj j))
    (Hc : SheafHom Rc F c.pt) : Cocone (sheafHomDiagram F D H) where
  pt := Hc.obj
  ι :=
    { app := fun j => SheafHom.postcomp (c.ι.app j) (H j) Hc
      naturality := fun i j f => by
        refine Eq.trans ?_ (Category.comp_id _).symm
        refine Eq.trans
          (SheafHom.postcomp_comp (D.map f) (c.ι.app j) (H i) (H j) Hc).symm ?_
        exact congrArg (fun v => SheafHom.postcomp v (H i) Hc) (c.w f) }

/-- The leg of `sheafHomCocone F D c H Hc` at `j` is the postcomposition map induced by the
colimit inclusion `c.ι.app j`. -/
@[simp]
lemma sheafHomCocone_ι_app (c : Cocone D) (H : ∀ j, SheafHom Rc F (D.obj j))
    (Hc : SheafHom Rc F c.pt) (j : K) :
    (sheafHomCocone F D c H Hc).ι.app j = SheafHom.postcomp (c.ι.app j) (H j) Hc :=
  rfl

/-- The chosen internal homs of a diagram agree with the canonical ones, compatibly with the
transition maps. -/
noncomputable def sheafHomDiagramIso (H : ∀ j, SheafHom Rc F (D.obj j)) :
    sheafHomDiagram F D H ≅ D ⋙ ihomFunctor Rc F :=
  NatIso.ofComponents (fun j => SheafHom.objIso (H j) (canonicalSheafHom F (D.obj j)))
    (fun {i j} f => by
      rw [Functor.comp_map, ihomFunctor_map_eq_postcomp]
      exact (SheafHom.postcomp_comp_id (D.map f) (H i) (H j)
          (canonicalSheafHom F (D.obj j))).trans
        (SheafHom.postcomp_id_comp (D.map f) (H i) (canonicalSheafHom F (D.obj i))
          (canonicalSheafHom F (D.obj j))).symm)

/-- **Stacks Project, Tag 0GMV.** Let `F` be an `O_X`-module of finite presentation on a ringed
space and let `G = colim_λ G_λ` be a filtered colimit of `O_X`-modules. Then the canonical
cocone of internal homs over `SheafHom_{O_X}(F, G)`, whose legs are the postcomposition maps
induced by the colimit inclusions, is a colimit cocone; that is, the canonical map
`colim_λ SheafHom_{O_X}(F, G_λ) ⟶ SheafHom_{O_X}(F, G)` is an isomorphism. -/
@[stacks 0GMV]
noncomputable def isColimit_sheafHomCocone [F.IsFinitePresentation] [IsFiltered K]
    (c : Cocone D) (hc : IsColimit c)
    (H : ∀ j, SheafHom Rc F (D.obj j)) (Hc : SheafHom Rc F c.pt) :
    IsColimit (sheafHomCocone F D c H Hc) := by
  have hpres : PreservesColimitsOfShape K (ihomFunctor Rc F) :=
    preservesColimitsOfShape_ihomFunctor F
  have hmap : IsColimit ((ihomFunctor Rc F).mapCocone c) := isColimitOfPreserves _ hc
  have hpre : IsColimit ((Cocone.precompose (sheafHomDiagramIso F D H).hom).obj
      ((ihomFunctor Rc F).mapCocone c)) :=
    (IsColimit.precomposeHomEquiv (sheafHomDiagramIso F D H) _).symm hmap
  refine IsColimit.ofIsoColimit hpre (Cocone.ext
    (SheafHom.objIso (canonicalSheafHom F c.pt) Hc) (fun j => ?_))
  change (SheafHom.postcomp (𝟙 (D.obj j)) (H j) (canonicalSheafHom F (D.obj j))
        ≫ (ihomFunctor Rc F).map (c.ι.app j))
      ≫ SheafHom.postcomp (𝟙 c.pt) (canonicalSheafHom F c.pt) Hc
    = SheafHom.postcomp (c.ι.app j) (H j) Hc
  rw [ihomFunctor_map_eq_postcomp]
  refine Eq.trans (congrArg (· ≫ SheafHom.postcomp (𝟙 c.pt) (canonicalSheafHom F c.pt) Hc)
    (SheafHom.postcomp_id_comp (c.ι.app j) (H j) (canonicalSheafHom F (D.obj j))
      (canonicalSheafHom F c.pt))) ?_
  exact SheafHom.postcomp_comp_id (c.ι.app j) (H j) (canonicalSheafHom F c.pt) Hc

/-- **Stacks Project, Tag 0GMV**, in comparison-map form: for `F` of finite presentation and a
filtered diagram, the canonical map from any colimit of the internal homs
`SheafHom_{O_X}(F, G_λ)` to `SheafHom_{O_X}(F, colim_λ G_λ)` is an isomorphism. -/
@[stacks 0GMV]
theorem isIso_desc_sheafHomCocone [F.IsFinitePresentation] [IsFiltered K]
    (c : Cocone D) (hc : IsColimit c)
    (H : ∀ j, SheafHom Rc F (D.obj j)) (Hc : SheafHom Rc F c.pt)
    (t : Cocone (sheafHomDiagram F D H)) (ht : IsColimit t) :
    IsIso (ht.desc (sheafHomCocone F D c H Hc)) :=
  ht.nonempty_isColimit_iff_isIso_desc.mp ⟨isColimit_sheafHomCocone F D c hc H Hc⟩

end Stacks.SheafOfModules

end
