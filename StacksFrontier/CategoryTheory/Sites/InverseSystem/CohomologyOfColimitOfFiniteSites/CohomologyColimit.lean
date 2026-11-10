module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitsOfSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InjectiveSystemsOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites.CohomologyDiagram
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites.MorphismOfSitesAndDescent
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites.CohomologyDiagram

/-! # Cohomology of a colimit of sites with finite coverings (Stacks 09YP, weak form)

The last of the four files on the cohomology of a colimit of sites with finite coverings
(see `CohomologyOfColimitOfFiniteSites.AbelianSystemsAndSections`). Let `D` be an inverse system
of sites with finite coverings, `F` a system of abelian sheaves on it, and `C` the colimit site of
Stacks 09YL. For every index `i`, every object `X` of the site at `i` and every `p`, the cohomology
`H^p(u_i(X), G)` of `G = colim f_i^{-1}F_i` is the filtered colimit, over the arrows `a : j ⟶ i`,
of the groups `H^p(u_a(X), F_j)`. The proof computes the case `p = 0` (sections of the colimit
sheaf), shows that the colimit of a pointwise injective system is acyclic on the colimit site
(Čech vanishing and Leray's acyclicity lemma), and applies this in every degree of a pointwise
injective resolution of `F`, homology commuting with the exact colimits of `(Over i)ᵒᵖ`.

## Main results

* `Stacks.WeakSites.ColimitSiteCohomology.cohomologyCocone` and
  `Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone`: **Stacks 09YP** for an
  inverse system of sites with finite coverings.

## References

* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous

universe v u w t s

namespace Stacks.WeakSites.ColimitSiteCohomology

attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive

attribute [local instance_reducible] systemOfPushforwardMaps systemCokernel systemSyzygy

section SystemColimits

attribute [local instance_reducible] systemColimitSheaf



variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))


private theorem whiskerLeft_eqToHom_naturality
    {A B T : Type*} [Category A] [Category B] [Category T]
    {U V : A ⥤ B} (h : U = V) {P Q : B ⥤ T} (f : P ⟶ Q) :
    eqToHom (congrArg (fun W => W ⋙ P) h) ≫ Functor.whiskerLeft V f =
      Functor.whiskerLeft U f ≫ eqToHom (congrArg (fun W => W ⋙ Q) h) := by
  subst h
  simp

/-- A morphism of systems of abelian sheaves commutes with the transition maps. -/
private theorem hom_comp_transition
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) {i j : D.I} (a : j ⟶ i) :
    (f.app i).hom ≫ transition D G a =
      transition D F a ≫ Functor.whiskerLeft (D.u a).op (f.app j).hom :=
  congrArg (fun q => q.hom) (systemPushforwardMap_naturality D f a)

private theorem isCompatible_systemHom
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (P : Cᵒᵖ ⥤ Ab.{max u v w t})
    (ι : ∀ i, (G.obj i).obj ⟶ (uC i).op ⋙ P)
    (hι : IsCompatible D uC hu G P ι) :
    IsCompatible D uC hu F P (fun i => (f.app i).hom ≫ ι i) := by
  intro i j a
  dsimp only
  rw [hι a, ← Category.assoc, ← Category.assoc, hom_comp_transition D f a]
  simp only [Functor.whiskerLeft_comp, Category.assoc]

private def systemColimitMap
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) :
    systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F ⟶
      systemColimitSheaf D uC hu hobj hhom hhom_inj K hK G :=
  ((systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F).2
    (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK G)
    (fun i => (f.app i).hom ≫ systemKanUnit D uC hu G i)
    (isCompatible_systemHom D uC hu f _ _ (systemKanUnit_compatible D uC hu G))).choose

private theorem systemColimitMap_fac
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (i : D.I) :
    systemKanUnit D uC hu F i ≫ Functor.whiskerLeft (uC i).op
      (systemColimitMap D uC hu hobj hhom hhom_inj K hK f).hom =
        (f.app i).hom ≫ systemKanUnit D uC hu G i :=
  ((systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F).2
    (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK G)
    (fun i => (f.app i).hom ≫ systemKanUnit D uC hu G i)
    (isCompatible_systemHom D uC hu f _ _ (systemKanUnit_compatible D uC hu G))).choose_spec.1 i

private theorem isCompatible_post
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {G H : Cᵒᵖ ⥤ Ab.{max u v w t}}
    (ι : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ G)
    (hι : IsCompatible D uC hu F G ι) (f : G ⟶ H) :
    IsCompatible D uC hu F H (fun i => ι i ≫ Functor.whiskerLeft (uC i).op f) := by
  intro i j a
  dsimp only
  rw [hι a]
  simp only [Functor.whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_eqToHom_naturality (congrArg Functor.op (hu a))]
  rfl

private theorem isCompatible_of_epi_systemHom
    [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (hf : ∀ i, Epi (f.app i))
    (H : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ i, (G.obj i).obj ⟶ (uC i).op ⋙ H.obj)
    (hι : IsCompatible D uC hu F H.obj (fun i => (f.app i).hom ≫ ι i)) :
    IsCompatible D uC hu G H.obj ι := by
  intro i j a
  let := hf i
  suffices h : (⟨ι i⟩ : G.obj i ⟶ ((uC i).sheafPushforwardContinuous
      (Ab.{max u v w t}) (D.J i) K.toGrothendieck).obj H) =
      ⟨transition D G a ≫ Functor.whiskerLeft (D.u a).op (ι j) ≫
        eqToHom (restrict_eq.{v, u, w, t} D uC hu a H.obj)⟩ from congrArg (fun q => q.hom) h
  apply (cancel_epi (f.app i)).mp
  apply Sheaf.hom_ext
  change (f.app i).hom ≫ ι i = (f.app i).hom ≫ transition D G a ≫ _
  rw [← Category.assoc, hom_comp_transition D f a]
  simpa only [Functor.whiskerLeft_comp, Category.assoc] using hι a

private theorem colimitPresentation_hom_ext
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {G H : Sheaf K.toGrothendieck (Ab.{max u v w t})}
    (ι : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ G.obj)
    (hG : IsColimitPresentation D uC hu K F G ι)
    (f g : G ⟶ H)
    (h : ∀ i, ι i ≫ Functor.whiskerLeft (uC i).op f.hom =
      ι i ≫ Functor.whiskerLeft (uC i).op g.hom) : f = g := by
  obtain ⟨m, hm, he⟩ := hG.2 H _ (isCompatible_post D uC hu F ι hG.1 f.hom)
  exact (he f (fun _ => rfl)).trans (he g (fun i => (h i).symm)).symm

private theorem systemColimitMap_comp
    {F G H : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G)
    (g : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom G H) :
    systemColimitMap D uC hu hobj hhom hhom_inj K hK (systemHomComp f g) =
      systemColimitMap D uC hu hobj hhom hhom_inj K hK f ≫
        systemColimitMap D uC hu hobj hhom hhom_inj K hK g := by
  apply colimitPresentation_hom_ext D uC hu K F (systemKanUnit D uC hu F)
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F)
  intro i
  change _ = systemKanUnit D uC hu F i ≫ Functor.whiskerLeft (uC i).op (_ ≫ _)
  rw [Functor.whiskerLeft_comp,
    systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK (systemHomComp f g),
    ← Category.assoc, systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK f,
    Category.assoc, systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK g]
  rfl

private theorem systemColimitMap_eq_zero
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (hf : ∀ i, f.app i = 0) :
    systemColimitMap D uC hu hobj hhom hhom_inj K hK f = 0 := by
  apply colimitPresentation_hom_ext D uC hu K F (systemKanUnit D uC hu F)
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F)
  intro i
  rw [systemColimitMap_fac, hf]
  ext V
  simp

section SectionsFac

attribute [local implicit_reducible] sectionsDiagram sectionsCocone

private theorem systemColimitMap_sections_fac
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (i : D.I) (X : D.C i)
    (A : (Over i)ᵒᵖ) :
    (sectionsCocone D uC hu F _ (systemKanUnit D uC hu F)
        (systemKanUnit_compatible D uC hu F) i X).ι.app A ≫
      (systemColimitMap D uC hu hobj hhom hhom_inj K hK f).hom.app
        (op ((uC i).obj X)) =
    (sectionsDiagramMap f i X).app A ≫
      (sectionsCocone D uC hu G _ (systemKanUnit D uC hu G)
        (systemKanUnit_compatible D uC hu G) i X).ι.app A := by
  have h := congrArg (fun q => q.app (op ((D.u A.unop.hom).obj X)))
    (systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK f A.unop.left)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  change ((_ ≫ _) ≫ _) = _ ≫ (_ ≫ _)
  rw [Category.assoc, NatTrans.naturality, ← Category.assoc, h, Category.assoc]
  rfl

end SectionsFac

private theorem mono_of_isColimit
    {I T : Type*} [Category I] [Category T] [HasColimitsOfShape I T]
    [(colim : (I ⥤ T) ⥤ T).PreservesMonomorphisms]
    {F G : I ⥤ T} {c : Cocone F} {d : Cocone G}
    (hc : IsColimit c) (hd : IsColimit d) (f : F ⟶ G) [Mono f]
    (m : c.pt ⟶ d.pt) (hm : ∀ i, c.ι.app i ≫ m = f.app i ≫ d.ι.app i) :
    Mono m := by
  have heq : m = (hc.coconePointUniqueUpToIso (colimit.isColimit F)).hom ≫
      colim.map f ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom := by
    apply hc.hom_ext
    intro i
    simp only [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    change c.ι.app i ≫ m = (colimit.ι F i ≫ colim.map f) ≫ _
    rw [colimit.ι_map, Category.assoc, colimit.comp_coconePointUniqueUpToIso_hom, hm]
  rw [heq]
  infer_instance

private theorem systemColimitMap_mono
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (hf : ∀ i, Mono (f.app i)) :
    Mono (systemColimitMap D uC hu hobj hhom hhom_inj K hK f) := by
  have hmono : ∀ V, Mono ((systemColimitMap D uC hu hobj hhom hhom_inj K hK f).hom.app V) := by
    intro V
    obtain ⟨i, X, hX⟩ := hobj V.unop
    have hV : V = op ((uC i).obj X) := by rw [hX]
    subst hV
    let : PreservesFilteredColimitsOfSize.{v, max u v}
        (forget (Ab.{max u v w t})) :=
      preservesFilteredColimitsOfSize_of_univLE.{max u v w t, max u v w t} _
    let : HasExactColimitsOfShape (Over i)ᵒᵖ (Ab.{max u v w t}) := ⟨inferInstance⟩
    let : ∀ A, Mono ((sectionsDiagramMap f i X).app A) := by
      intro A
      let := hf A.unop.left
      have hm : Mono (f.app A.unop.left).hom :=
        (sheafToPresheaf (D.J A.unop.left) (Ab.{max u v w t})).map_mono _
      exact (NatTrans.mono_iff_mono_app _).mp hm _
    let : Mono (sectionsDiagramMap f i X) := NatTrans.mono_of_mono_app _
    exact mono_of_isColimit
      (isColimit_sectionsCocone_of_pointwise D uC hu hhom hhom_inj F _ _
        (systemKanUnit_compatible D uC hu F) (systemKan_isPointwise D uC hu F) i X)
      (isColimit_sectionsCocone_of_pointwise D uC hu hhom hhom_inj G _ _
        (systemKanUnit_compatible D uC hu G) (systemKan_isPointwise D uC hu G) i X)
      (sectionsDiagramMap f i X) _
      (systemColimitMap_sections_fac D uC hu hobj hhom hhom_inj K hK f i X)
  let := hmono
  have : Mono (systemColimitMap D uC hu hobj hhom hhom_inj K hK f).hom :=
    NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono K.toGrothendieck (Ab.{max u v w t})
    (systemColimitMap D uC hu hobj hhom hhom_inj K hK f)

private theorem systemColimitMap_epi
    [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) (hf : ∀ i, Epi (f.app i)) :
    Epi (systemColimitMap D uC hu hobj hhom hhom_inj K hK f) := by
  constructor
  intro H g h e
  apply colimitPresentation_hom_ext D uC hu K G (systemKanUnit D uC hu G)
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK G)
  intro i
  let := hf i
  suffices hh : (⟨systemKanUnit D uC hu G i ≫ Functor.whiskerLeft (uC i).op g.hom⟩ :
      G.obj i ⟶ ((uC i).sheafPushforwardContinuous (Ab.{max u v w t})
        (D.J i) K.toGrothendieck).obj H) =
      ⟨systemKanUnit D uC hu G i ≫ Functor.whiskerLeft (uC i).op h.hom⟩ from
    congrArg (fun q => q.hom) hh
  apply (cancel_epi (f.app i)).mp
  apply Sheaf.hom_ext
  change (f.app i).hom ≫ systemKanUnit D uC hu G i ≫ _ =
    (f.app i).hom ≫ systemKanUnit D uC hu G i ≫ _
  rw [← Category.assoc, ← Category.assoc,
    ← systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK f]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp]
  exact congrArg (fun q => systemKanUnit D uC hu F i ≫
    Functor.whiskerLeft (uC i).op q.hom) e

private theorem exists_compatible_cokernel_desc
    [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G)
    (H : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (g : ∀ i, (G.obj i).obj ⟶ (uC i).op ⋙ H.obj)
    (hg : IsCompatible D uC hu G H.obj g)
    (hfg : ∀ i, (f.app i).hom ≫ g i = 0) :
    ∃ q : ∀ i, ((systemCokernel D f).obj i).obj ⟶ (uC i).op ⋙ H.obj,
      IsCompatible D uC hu (systemCokernel D f) H.obj q ∧
      ∀ i, (cokernel.π (f.app i)).hom ≫ q i = g i := by
  let g' (i : D.I) : G.obj i ⟶ ((uC i).sheafPushforwardContinuous
      (Ab.{max u v w t}) (D.J i) K.toGrothendieck).obj H := ⟨g i⟩
  have hfg' (i : D.I) : f.app i ≫ g' i = 0 := Sheaf.hom_ext (hfg i)
  let q (i : D.I) := (cokernel.desc (f.app i) (g' i) (hfg' i)).hom
  have hq (i : D.I) : (cokernel.π (f.app i)).hom ≫ q i = g i :=
    congrArg (fun m => m.hom) (cokernel.π_desc (f.app i) (g' i) (hfg' i))
  refine ⟨q, ?_, hq⟩
  apply isCompatible_of_epi_systemHom D uC hu K (systemCokernelπ D f)
    (fun i => by change Epi (cokernel.π (f.app i)); infer_instance) H q
  change IsCompatible D uC hu G H.obj (fun i => (cokernel.π (f.app i)).hom ≫ q i)
  intro i j a
  simpa only [hq] using hg a

private theorem systemColimitMap_cokernel_condition
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) :
    systemColimitMap D uC hu hobj hhom hhom_inj K hK f ≫
      systemColimitMap D uC hu hobj hhom hhom_inj K hK (systemCokernelπ D f) = 0 := by
  rw [← systemColimitMap_comp]
  apply systemColimitMap_eq_zero
  intro i
  exact cokernel.condition (f.app i)

private def systemColimitMap_isCokernel
    [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    {F G : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F G) :
    IsColimit (CokernelCofork.ofπ
      (systemColimitMap D uC hu hobj hhom hhom_inj K hK (systemCokernelπ D f))
      (systemColimitMap_cokernel_condition D uC hu hobj hhom hhom_inj K hK f)) := by
  letI := systemColimitMap_epi D uC hu hobj hhom hhom_inj K hK
    (systemCokernelπ D f) (fun i => by change Epi (cokernel.π (f.app i)); infer_instance)
  apply CokernelCofork.IsColimit.ofπ'
  intro H m hm
  apply Classical.choice
  let g i := systemKanUnit D uC hu G i ≫ Functor.whiskerLeft (uC i).op m.hom
  have hg : IsCompatible D uC hu G H.obj g :=
    isCompatible_post D uC hu G (systemKanUnit D uC hu G)
      (systemKanUnit_compatible D uC hu G) m.hom
  have hfg (i : D.I) : (f.app i).hom ≫ g i = 0 := by
    dsimp only [g]
    rw [← Category.assoc, ← systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK f,
      Category.assoc, ← Functor.whiskerLeft_comp]
    have he := congrArg (fun q => q.hom) hm
    change (systemColimitMap D uC hu hobj hhom hhom_inj K hK f).hom ≫ m.hom = 0 at he
    rw [he]
    ext V
    simp
  obtain ⟨q, hq, hfac⟩ := exists_compatible_cokernel_desc D uC hu K f H g hg hfg
  obtain ⟨l, hl, _⟩ :=
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK
      (systemCokernel D f)).2 H q hq
  refine ⟨⟨l, ?_⟩⟩
  apply colimitPresentation_hom_ext D uC hu K G (systemKanUnit D uC hu G)
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK G)
  intro i
  change systemKanUnit D uC hu G i ≫ Functor.whiskerLeft (uC i).op (_ ≫ _) = g i
  rw [Functor.whiskerLeft_comp, ← Category.assoc,
    systemColimitMap_fac, Category.assoc, hl]
  exact hfac i

include hobj hhom hhom_inj hK in
/-- **One step of a pointwise injective resolution of a system, with its colimit.** Every system
`F` of abelian sheaves embeds into a pointwise injective system `I` (Stacks 0EXZ) with pointwise
cokernel `Q`, and the induced maps of colimit sheaves `colim F ⟶ colim I ⟶ colim Q` form a short
exact sequence compatible with the structure maps of the three colimits. This is the input of
dimension shifting for any functor of the colimit sheaf computed through the system. -/
public theorem exists_shortExact_pointwiseInjective_colimit
    [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) :
    ∃ (I Q : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
      (ι : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom F I)
      (π : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom I Q)
      (w : ∀ j, ι.app j ≫ π.app j = 0),
      (∀ j, (ShortComplex.mk _ _ (w j)).ShortExact) ∧ (∀ j, Injective (I.obj j)) ∧
      ∃ (ψ : systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F ⟶
          systemColimitSheaf D uC hu hobj hhom hhom_inj K hK I)
        (ϖ : systemColimitSheaf D uC hu hobj hhom hhom_inj K hK I ⟶
          systemColimitSheaf D uC hu hobj hhom hhom_inj K hK Q)
        (w' : ψ ≫ ϖ = 0), (ShortComplex.mk ψ ϖ w').ShortExact ∧
        (∀ j, systemKanUnit D uC hu F j ≫ Functor.whiskerLeft (uC j).op ψ.hom =
          (ι.app j).hom ≫ systemKanUnit D uC hu I j) ∧
        (∀ j, systemKanUnit D uC hu I j ≫ Functor.whiskerLeft (uC j).op ϖ.hom =
          (π.app j).hom ≫ systemKanUnit D uC hu Q j) := by
  have hmono := injectiveSystemι_mono D F
  have hepi : ∀ j, Epi ((systemCokernelπ D (injectiveSystemι D F)).app j) := fun j => by
    change Epi (cokernel.π _); infer_instance
  have w : ∀ j, (injectiveSystemι D F).app j ≫ (systemCokernelπ D (injectiveSystemι D F)).app j
      = 0 := fun j => cokernel.condition _
  refine ⟨injectiveSystem D F, systemCokernel D (injectiveSystemι D F), injectiveSystemι D F,
    systemCokernelπ D (injectiveSystemι D F), w, fun j => ?_, injectiveSystem_injective D F,
    systemColimitMap D uC hu hobj hhom hhom_inj K hK (injectiveSystemι D F),
    systemColimitMap D uC hu hobj hhom hhom_inj K hK (systemCokernelπ D (injectiveSystemι D F)),
    systemColimitMap_cokernel_condition D uC hu hobj hhom hhom_inj K hK _, ?_,
    systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK _,
    systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK _⟩
  · have := hmono j
    have := hepi j
    exact { exact := ShortComplex.exact_cokernel _ }
  · have := systemColimitMap_mono D uC hu hobj hhom hhom_inj K hK _ hmono
    have := systemColimitMap_epi D uC hu hobj hhom hhom_inj K hK _ hepi
    have hex := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk _ _ (systemColimitMap_cokernel_condition D uC hu hobj hhom hhom_inj K hK
        (injectiveSystemι D F)))
      (systemColimitMap_isCokernel D uC hu hobj hhom hhom_inj K hK (injectiveSystemι D F))
    exact ShortComplex.ShortExact.mk hex

end SystemColimits

/-- Sections of abelian sheaves over a fixed object preserve finite limits. -/
private theorem preservesFiniteLimits_sheafSections_obj
    {C : Type*} [Category* C] (J : GrothendieckTopology C) (U : Cᵒᵖ) :
    PreservesFiniteLimits ((sheafSections J Ab.{_}).obj U) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation (J := J) (A := Ab.{_})).symm

section CanonicalDiagram

variable (D : InverseSystemOfFiniteSites.{v, u, w})
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
  [htrans : ∀ {j k : D.I} (a : j ⟶ k),
    (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, w, t} D a).PreservesInjectiveObjects]

/-- Each transition functor of the system is continuous. -/
local instance transition_continuous {j k : D.I} (a : j ⟶ k) :
    (D.u a).IsContinuous (D.J k) (D.J j) := D.continuous a

/-- Pushforward along each transition functor of the system preserves injective objects. -/
local instance transition_preservesInjectives {j k : D.I} (a : j ⟶ k) :
    ((D.u a).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J k) (D.J j)).PreservesInjectiveObjects := htrans a

private def overCohomologyMap {i : D.I} (X : D.C i) (p : ℕ)
    {A B : Over i} (f : A ⟶ B) :
    ((((sheafSections (D.J B.left) (Ab.{max u v w t})).obj
      (op ((D.u B.hom).obj X))).rightDerived p).obj (F.obj B.left)) ⟶
    ((((sheafSections (D.J A.left) (Ab.{max u v w t})).obj
      (op ((D.u A.hom).obj X))).rightDerived p).obj (F.obj A.left)) :=
  cohomologyMapTo (D.u f.left) (transition D F f.left)
    ((D.u B.hom).obj X) ((D.u A.hom).obj X) (uObj_eq D f X).symm p

private theorem overCohomologyMap_id {i : D.I} (X : D.C i) (p : ℕ) (A : Over i) :
    overCohomologyMap D F (htrans := htrans) X p (𝟙 A) = 𝟙 _ := by
  let := pushforward_id_preservesInjectives.{w, max u v t} (D.J A.left)
  change cohomologyMapTo (D.u (𝟙 A.left)) (transition D F (𝟙 A.left))
    _ _ _ p = _
  calc
    _ = cohomologyMapTo (𝟭 (D.C A.left)) (𝟙 (F.obj A.left).obj)
        ((D.u A.hom).obj X) ((D.u A.hom).obj X) rfl p := by
      apply cohomologyMapTo_congr _ _ _ _ (D.id_map A.left)
      rw [transition_id_eqToHom, eqToHom_trans]
      rfl
    _ = 𝟙 _ := cohomologyMapTo_id _ _ _ _

private theorem overCohomologyMap_comp {i : D.I} (X : D.C i) (p : ℕ)
    {A B C : Over i} (f : A ⟶ B) (g : B ⟶ C) :
    overCohomologyMap D F (htrans := htrans) X p g ≫
        overCohomologyMap D F (htrans := htrans) X p f =
      overCohomologyMap D F (htrans := htrans) X p (f ≫ g) := by
  let := Functor.isContinuous_comp (D.u g.left) (D.u f.left)
    (D.J C.left) (D.J B.left) (D.J A.left)
  let := pushforward_comp_preservesInjectives (JA := D.J C.left)
    (JB := D.J B.left) (JC := D.J A.left) (D.u g.left) (D.u f.left)
  unfold overCohomologyMap
  rw [cohomologyMapTo_comp]
  apply cohomologyMapTo_congr _ _ _ _ (D.comp f.left g.left).symm
  exact (transition_comp_eqToHom D F f.left g.left).symm

private def canonicalCohomologyDiagram (i : D.I) (X : D.C i) (p : ℕ) :
    (Over i)ᵒᵖ ⥤ Ab.{max u v w t} where
  obj A := ((((sheafSections (D.J A.unop.left) (Ab.{max u v w t})).obj
    (op ((D.u A.unop.hom).obj X))).rightDerived p).obj (F.obj A.unop.left))
  map f := overCohomologyMap D F (htrans := htrans) X p f.unop
  map_id A := overCohomologyMap_id D F (htrans := htrans) X p A.unop
  map_comp f g := (overCohomologyMap_comp D F (htrans := htrans) X p g.unop f.unop).symm

section

-- the source and the target of the isomorphism below are these two diagrams, and the instance
-- `IsIso (F.toRightDerivedZero.app _)` is stated for the functors they unfold to
attribute [local instance_reducible] sectionsDiagram canonicalCohomologyDiagram

private def sectionsCohomologyDiagramZeroIso (i : D.I) (X : D.C i) :
    sectionsDiagram D F i X ≅ canonicalCohomologyDiagram D F (htrans := htrans) i X 0 := by
  refine NatIso.ofComponents (fun A => by
    letI := preservesFiniteLimits_sheafSections_obj (D.J A.unop.left)
      (op ((D.u A.unop.hom).obj X))
    exact asIso (((sheafSections (D.J A.unop.left) (Ab.{max u v w t})).obj
      (op ((D.u A.unop.hom).obj X))).toRightDerivedZero.app (F.obj A.unop.left))) ?_
  intro A B f
  exact (cohomologyMapTo_zero_comm (D.u f.unop.left) (transition D F f.unop.left)
    _ _ (uObj_eq D f.unop X).symm).symm

end

variable {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : Precoverage C)
  [hcont : ∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck]
  [hleg : ∀ j, letI := hcont j
    ((uC j).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J j) K.toGrothendieck).PreservesInjectiveObjects]
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (hι : IsCompatible D uC hu F 𝒢.obj ι)

/-- Each functor `uC j` into the colimit site is continuous. -/
local instance colimit_continuous (j : D.I) :
    (uC j).IsContinuous (D.J j) K.toGrothendieck := hcont j

/-- Pushforward along each functor `uC j` into the colimit site preserves injective objects. -/
local instance colimit_preservesInjectives (j : D.I) :
    ((uC j).sheafPushforwardContinuous (Ab.{max u v w t})
      (D.J j) K.toGrothendieck).PreservesInjectiveObjects := hleg j

private def canonicalCohomologyLeg (i : D.I) (X : D.C i) (p : ℕ) :
    canonicalCohomologyDiagram D F (htrans := htrans) i X p ⟶ (Functor.const (Over i)ᵒᵖ).obj
      ((((sheafSections K.toGrothendieck (Ab.{max u v w t})).obj
        (op ((uC i).obj X))).rightDerived p).obj 𝒢) where
  app A := cohomologyMapTo (uC A.unop.left) (ι A.unop.left)
    ((D.u A.unop.hom).obj X) ((uC i).obj X) (uLeg_eq D uC hu A.unop X).symm p
  naturality A B f := by
    let := Functor.isContinuous_comp (D.u f.unop.left) (uC B.unop.left)
      (D.J A.unop.left) (D.J B.unop.left) K.toGrothendieck
    let := pushforward_comp_preservesInjectives (JA := D.J A.unop.left)
      (JB := D.J B.unop.left) (JC := K.toGrothendieck)
      (D.u f.unop.left) (uC B.unop.left)
    change cohomologyMapTo (D.u f.unop.left) _ _ _ _ p ≫
      cohomologyMapTo (uC B.unop.left) _ _ _ _ p = _ ≫ 𝟙 _
    rw [Category.comp_id, cohomologyMapTo_comp]
    apply cohomologyMapTo_congr _ _ _ _ (hu f.unop.left)
    exact (hι f.unop.left).symm

private def canonicalCohomologyCocone (i : D.I) (X : D.C i) (p : ℕ) :
    CohomologyCocone D uC hu K F 𝒢 ι i X p where
  diagram := canonicalCohomologyDiagram D F (htrans := htrans) i X p
  objIso A := Iso.refl _
  map_eq f := by
    simp only [Iso.refl_inv, Iso.refl_hom]
    exact cohomologyMapTo_isCohomologyMap (D.u f.left) (transition D F f.left)
      _ _ (uObj_eq D f X).symm p
  leg := canonicalCohomologyLeg D F (htrans := htrans) uC hu K (hcont := hcont)
    (hleg := hleg) 𝒢 ι hι i X p
  leg_eq A := by
    simp only [Iso.refl_inv]
    exact cohomologyMapTo_isCohomologyMap (uC A.left) (ι A.left)
      _ _ (uLeg_eq D uC hu A X).symm p

end CanonicalDiagram

private def isColimitCohomologyCoconeEquiv
    {D : InverseSystemOfFiniteSites.{v, u, w}} {C : Type w} [SmallCategory C]
    {uC : ∀ i, D.C i ⥤ C}
    {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
    {K : Precoverage C} {F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    {𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})}
    {ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj} {i : D.I} {X : D.C i} {p : ℕ}
    (hf : ∀ j, (uC j).IsMorphismOfSites (D.J j) K.toGrothendieck)
    (E E' : CohomologyCocone.{v, u, w, t} D uC hu K F 𝒢 ι i X p) :
    IsColimit E.cocone ≃ IsColimit E'.cocone := by
  let ht : ∀ {j k : D.I} (a : j ⟶ k),
      (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, w, t}
        D a).PreservesInjectiveObjects :=
    fun a => restriction_preservesInjectiveObjects (D.u a) (D.isMorphismOfSites a)
  let e := cohomologyDiagramIso ht E E'
  apply IsColimit.equivOfNatIsoOfIso e
  refine Cocone.ext (Iso.refl _) (fun A => ?_)
  let := (hf A.unop.left).isContinuous
  let := restriction_preservesInjectiveObjects.{w, max u v t} (uC A.unop.left) (hf A.unop.left)
  have hm := isCohomologyMap_unique (uC A.unop.left) (ι A.unop.left)
    ((D.u A.unop.hom).obj X) p (E.leg_eq A.unop) (E'.leg_eq A.unop)
  let := cohomologyCongr_isIso K.toGrothendieck p (uLeg_eq D uC hu A.unop X) 𝒢
  have h : (E.objIso A.unop).inv ≫ E.leg.app A =
      (E'.objIso A.unop).inv ≫ E'.leg.app A := by
    apply (cancel_mono
      (cohomologyCongr K.toGrothendieck p (uLeg_eq D uC hu A.unop X) 𝒢)).mp
    simpa only [Category.assoc] using hm
  apply (cancel_epi (E'.objIso A.unop).inv).mp
  simpa only [e, cohomologyDiagramIso, Cocone.precompose_obj_ι, NatTrans.comp_app,
    CohomologyCocone.cocone, NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv, Iso.refl_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id] using h

private def isColimitCohomologyCoconeOfInjective
    {D : InverseSystemOfFiniteSites.{v, u, w}} {C : Type w} [SmallCategory C]
    {uC : ∀ i, D.C i ⥤ C}
    {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
    {K : Precoverage C} {F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
    {𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})}
    {ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj} {i : D.I} {X : D.C i} {p : ℕ}
    (hF : ∀ j, Injective (F.obj j))
    (hG : IsZero (((((sheafSections K.toGrothendieck (Ab.{max u v w t})).obj
      (op ((uC i).obj X))).rightDerived p).obj 𝒢)))
    (hp : 0 < p) (E : CohomologyCocone.{v, u, w, t} D uC hu K F 𝒢 ι i X p) :
    IsColimit E.cocone := by
  apply IsColimit.ofIsZero _ (Functor.isZero _ (fun A => ?_)) hG
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let := hF A.unop.left
  exact IsZero.of_iso
    (Functor.isZero_rightDerived_obj_injective_succ _ n (F.obj A.unop.left)) (E.objIso A.unop)

section ExactColimits

private theorem exact_of_exact_evaluation
    {I A : Type*} [Category* I] [Category* A] [Abelian A]
    (S : ShortComplex (I ⥤ A))
    (h : ∀ i, (S.map ((evaluation I A).obj i)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro i
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (h i))
    (S.mapHomologyIso ((evaluation I A).obj i)).symm

private theorem exactAt_of_isColimit
    {I A : Type*} [Category* I] [Category* A] [Abelian A]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    {ι : Type*} {c : ComplexShape ι}
    (F : I ⥤ HomologicalComplex A c) (s : Cocone F) (hs : IsColimit s)
    (n : ι) (hn : ∀ i, (F.obj i).ExactAt n) : s.pt.ExactAt n := by
  let S : ShortComplex (I ⥤ A) := ShortComplex.mk
    (Functor.whiskerLeft F (HomologicalComplex.dNatTrans A c (c.prev n) n))
    (Functor.whiskerLeft F (HomologicalComplex.dNatTrans A c n (c.next n)))
    (by ext i; exact (F.obj i).d_comp_d _ _ _)
  have hS : S.Exact := exact_of_exact_evaluation S hn
  let c₁ := (HomologicalComplex.eval A c (c.prev n)).mapCocone s
  let c₂ := (HomologicalComplex.eval A c n).mapCocone s
  let c₃ := (HomologicalComplex.eval A c (c.next n)).mapCocone s
  have h₁ : IsColimit c₁ := isColimitOfPreserves _ hs
  have h₂ : IsColimit c₂ := isColimitOfPreserves _ hs
  have h₃ : IsColimit c₃ := isColimitOfPreserves _ hs
  exact colim.exact_mapShortComplex hS h₁ h₂ h₃
    (s.pt.d (c.prev n) n) (s.pt.d n (c.next n))
    (fun j => ((s.ι.app j).comm _ _))
    (fun j => ((s.ι.app j).comm _ _))

end ExactColimits

section CechColimits


private theorem preservesColimitsOfShape_lim_of_colim
    {I J A : Type*} [Category* I] [Category* J] [Category* A]
    [HasLimitsOfShape J A] [HasColimitsOfShape I A]
    [PreservesLimitsOfShape J (colim : (I ⥤ A) ⥤ A)] :
    PreservesColimitsOfShape I (lim : (J ⥤ A) ⥤ A) where
  preservesColimit {F} := by
    let e : colimit (F ⋙ lim) ≅ limit (colimit F) :=
      (HasColimit.isoOfNatIso (limitFlipIsoCompLim F)).symm ≪≫ colimitLimitIso F.flip
    have he : e.hom = colimit.post F lim := by
      apply colimit.hom_ext
      intro i
      apply limit.hom_ext
      intro j
      simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        HasColimit.ι_isoOfNatIso_inv_assoc]
      have h := ι_colimitLimitIso_limit_π F.flip i j
      simp only [Functor.flip_flip] at h
      rw [h]
      simp [limitFlipIsoCompLim]
    have : IsIso (colimit.post F lim) := he ▸ inferInstanceAs (IsIso e.hom)
    exact preservesColimit_of_isIso_post lim F

/-- Evaluating the degreewise product of the Čech complex of `E` at a presheaf `P`, as a limit
over the discrete category of the indexing functions. -/
private def cechEvaluationIsoApp {C : Type u} [Category.{v} C]
    {A : Type*} [Category* A] [HasProducts.{w} A]
    {U : C} (E : PreZeroHypercover.{w} U)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (n : ℕ) (P : Cᵒᵖ ⥤ A) :
    (∏ᶜ fun i : Fin (n + 1) → E.I₀ =>
        P.obj (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)) ≅
      limit (Discrete.functor
        (fun i : Fin (n + 1) → E.I₀ => op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) ⋙ P) :=
  HasLimit.isoOfNatIso (Discrete.natIso (fun _ => Iso.refl _))

/-- The projections of `cechEvaluationIsoApp` are the projections of the product. -/
@[reassoc (attr := simp)]
private lemma cechEvaluationIsoApp_hom_π {C : Type u} [Category.{v} C]
    {A : Type*} [Category* A] [HasProducts.{w} A]
    {U : C} (E : PreZeroHypercover.{w} U)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (n : ℕ) (P : Cᵒᵖ ⥤ A) (i : Fin (n + 1) → E.I₀) :
    (cechEvaluationIsoApp E n P).hom ≫ limit.π (Discrete.functor
        (fun i : Fin (n + 1) → E.I₀ => op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) ⋙ P)
        ⟨i⟩ =
      Pi.π (fun i : Fin (n + 1) → E.I₀ =>
        P.obj (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)) i := by
  simp [cechEvaluationIsoApp]

private def cechEvaluationIso {C : Type u} [Category.{v} C]
    {A : Type*} [Category* A] [Preadditive A] [HasProducts.{w} A]
    {U : C} (E : PreZeroHypercover.{w} U)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (n : ℕ) :
    Stacks.CechSite.cechComplexFunctor E ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (Functor.whiskeringLeft (Discrete (Fin (n + 1) → E.I₀)) Cᵒᵖ A).obj
        (Discrete.functor (fun i => op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)) ⋙ lim := by
  refine NatIso.ofComponents (fun P => cechEvaluationIsoApp E n P) ?_
  intro P Q f
  change (Limits.Pi.map fun i : Fin (n + 1) → E.I₀ =>
      f.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)) ≫
      (cechEvaluationIsoApp E n Q).hom =
    (cechEvaluationIsoApp E n P).hom ≫ limMap (Functor.whiskerLeft _ f)
  apply limit.hom_ext
  rintro ⟨i⟩
  simp

private theorem cechComplexFunctor_preservesColimitsOfShape
    {C : Type u} [Category.{v} C]
    {A : Type*} [Category* A] [Preadditive A] [HasProducts.{w} A]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)]
    {U : C} (E : PreZeroHypercover.{w} U) [Finite E.I₀]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    PreservesColimitsOfShape I (Stacks.CechSite.cechComplexFunctor (A := A) E) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let : PreservesColimitsOfShape I
      (lim : (Discrete (Fin (n + 1) → E.I₀) ⥤ A) ⥤ A) :=
    preservesColimitsOfShape_lim_of_colim
  exact preservesColimitsOfShape_of_natIso (cechEvaluationIso E n).symm

private theorem cechCohomology_isZero_of_isColimit
    {C : Type u} [Category.{v} C]
    {A : Type*} [Category* A] [Abelian A] [HasProducts.{w} A]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)]
    [HasExactColimitsOfShape I A]
    {U : C} (E : PreZeroHypercover.{w} U) [Finite E.I₀]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : I ⥤ Cᵒᵖ ⥤ A) (s : Cocone F) (hs : IsColimit s)
    (n : ℕ) (hn : ∀ i, IsZero (Stacks.CechSite.cechCohomology E (F.obj i) n)) :
    IsZero (Stacks.CechSite.cechCohomology E s.pt n) := by
  let := cechComplexFunctor_preservesColimitsOfShape (A := A) (I := I) E
  exact (exactAt_of_isColimit (F ⋙ Stacks.CechSite.cechComplexFunctor E)
    ((Stacks.CechSite.cechComplexFunctor E).mapCocone s) (isColimitOfPreserves _ hs) n
    (fun i => (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hn i))).isZero_homology

private theorem stageCechCohomology_isZero_of_pointwise_injective
    (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
        (uC j).map g = eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Z).symm)
    (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
      (uC i).map g₁ = (uC i).map g₂ →
        ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    (hF : ∀ i, Injective (F.obj i))
    (i : D.I) {U : D.C i} (E : PreZeroHypercover.{w} U) [Finite E.I₀]
    [∀ (n : ℕ) (a : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (a b)))]
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E ((uC i).op ⋙ systemKanExtension D uC hu F) p) := by
  let : PreservesFilteredColimitsOfSize.{v, max u v}
      (forget (Ab.{max u v w t})) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w t, max u v w t} _
  let : HasExactColimitsOfShape (Over i)ᵒᵖ (Ab.{max u v w t}) :=
    ⟨inferInstance⟩
  apply cechCohomology_isZero_of_isColimit E (stageSectionsDiagram D F i)
    (stageSectionsCocone D uC hu F _ (systemKanUnit D uC hu F)
      (systemKanUnit_compatible D uC hu F) i)
    (isColimit_stageSectionsCocone_of_pointwise D uC hu hhom hhom_inj F _
      (systemKanUnit D uC hu F) (systemKanUnit_compatible D uC hu F)
      (systemKan_isPointwise D uC hu F) i) p
  intro A
  let := hF A.unop.left
  let := D.continuous A.unop.hom
  let : (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, w, t}
      D A.unop.hom).PreservesInjectiveObjects :=
    restriction_preservesInjectiveObjects (D.u A.unop.hom)
      (D.isMorphismOfSites A.unop.hom)
  exact Stacks.CechSite.injective_sheaf_cechCohomology_isZero E
    ((InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, w, t} D A.unop.hom).obj
      (F.obj A.unop.left)) p hp


end CechColimits

section ColimitPullbacks
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)

include hu hobj hhom hhom_inj in
open CategoryTheory.Sites.InverseSystem.Stacks.WeakSites.ColimitMorphismOfSites in
private theorem preservesLimit_cospan_of_mem (i : D.I) {Z : D.C i} {R : Presieve Z}
    (hR : R ∈ ((D.J i).toPrecoverage ⊓ Precoverage.finite (D.C i)) Z) {Y X : D.C i} {f : Y ⟶ Z}
    {g : X ⟶ Z} (hg : R g) : PreservesLimit (cospan f g) (uC i) := by
  have := D.hasPullbacks i
  have : R.HasPullbacks f := Precoverage.hasPullbacks_of_mem f hR
  have : HasPullback g f := Presieve.HasPullbacks.hasPullback f hg
  have : HasPullback f g := hasPullback_symmetry g f
  have key :
    ∀ (W : C) (p : W ⟶ (uC i).obj Y) (q : W ⟶ (uC i).obj X),
      p ≫ (uC i).map f = q ≫ (uC i).map g →
        ∃! h : W ⟶ (uC i).obj (pullback f g),
          h ≫ (uC i).map (pullback.fst f g) = p ∧ h ≫ (uC i).map (pullback.snd f g) = q := by
    intro W p q hpq
    obtain ⟨l, d, V, hV, p', q', hp', hq'⟩ := exists_descent₂ D uC hu hobj hhom Y X p q
    have himg : (uC l).map (p' ≫ (D.u d).map f) = (uC l).map (q' ≫ (D.u d).map g) := by
      have ef := map_transition_map D uC hu d f
      have eg := map_transition_map D uC hu d g
      rw [Functor.map_comp, Functor.map_comp, ←
        cancel_mono (f := eqToHom (Functor.congr_obj (hu d) Z))]
      simp only [Category.assoc, ef, eg]
      rw [← Category.assoc ((uC l).map p'), hp', ← Category.assoc ((uC l).map q'), hq',
        Category.assoc, Category.assoc, hpq]
    obtain ⟨k, b, hb⟩ := hhom_inj l V _ _ _ himg
    have := D.preservesPullbacks (b ≫ d) hR hg f
    have hlim := isLimitOfHasPullbackOfPreservesLimit (D.u (b ≫ d)) f g
    have heq :
      transportHom D b p' ≫ (D.u (b ≫ d)).map f = transportHom D b q' ≫ (D.u (b ≫ d)).map g := by
      rw [transportHom_comp, transportHom_comp]
      simp [transportHom, hb]
    obtain ⟨h₃, hh₁, hh₂⟩ :=
      PullbackCone.IsLimit.lift' hlim (transportHom D b p') (transportHom D b q') heq
    simp only [PullbackCone.mk_fst, PullbackCone.mk_snd] at hh₁ hh₂
    have hwp := comp_map_eq_of_transportHom_fac D uC hu hV hp' b hh₁
    have hwq := comp_map_eq_of_transportHom_fac D uC hu hV hq' b hh₂
    exact
      ⟨_, ⟨hwp, hwq⟩, fun m hm =>
        eq_of_comp_eq D uC hu hobj hhom hhom_inj i hR hg m _ (by rw [hm.1, hwp])
          (by rw [hm.2, hwq])⟩
  refine preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g) ?_
  refine
    (isLimitMapConePullbackConeEquiv (uC i) (pullback.condition (f := f) (g := g))).symm
      (PullbackCone.IsLimit.mk _ (fun s => (key s.pt s.fst s.snd s.condition).choose)
        (fun s => (key s.pt s.fst s.snd s.condition).choose_spec.1.1)
        (fun s => (key s.pt s.fst s.snd s.condition).choose_spec.1.2)
        (fun s m hm₁ hm₂ => (key s.pt s.fst s.snd s.condition).choose_spec.2 m ⟨hm₁, hm₂⟩))


end ColimitPullbacks

section CoveringProducts

attribute [local implicit_reducible] CategoryTheory.extendFan

private theorem hasProduct_fin_of_binaryProducts
    {C : Type*} [Category* C] [HasTerminal C] {α : Type*} (f : α → C)
    (h : ∀ a Y, HasBinaryProduct (f a) Y) :
    ∀ (n : ℕ) (a : Fin n → α), HasProduct (fun j => f (a j))
  | 0, a => by
    let : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    infer_instance
  | n + 1, a => by
    let := hasProduct_fin_of_binaryProducts f h n (fun j => a j.succ)
    let := h (a 0) (∏ᶜ (fun j : Fin n => f (a j.succ)))
    exact HasLimit.mk ⟨_, extendFanIsLimit (fun j => f (a j))
      (limit.isLimit _) (limit.isLimit _)⟩

private theorem preservesProduct_fin_of_binaryProducts
    {C D : Type*} [Category* C] [Category* D] [HasTerminal C]
    (F : C ⥤ D) [PreservesLimit (Functor.empty.{0} C) F]
    {α : Type*} (f : α → C) (h : ∀ a Y, HasBinaryProduct (f a) Y)
    (hF : ∀ a Y, PreservesLimit (pair (f a) Y) F) :
    ∀ (n : ℕ) (a : Fin n → α), PreservesLimit (Discrete.functor (fun j => f (a j))) F
  | 0, a => by
    let : PreservesLimitsOfShape (Discrete PEmpty) F :=
      preservesLimitsOfShape_pempty_of_preservesTerminal F
    let : PreservesLimitsOfShape (Discrete (Fin 0)) F :=
      preservesLimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1, a => by
    let := hasProduct_fin_of_binaryProducts f h n (fun j => a j.succ)
    let := h (a 0) (∏ᶜ (fun j : Fin n => f (a j.succ)))
    let := preservesProduct_fin_of_binaryProducts F f h hF n (fun j => a j.succ)
    let := hF (a 0) (∏ᶜ (fun j : Fin n => f (a j.succ)))
    apply preservesLimit_of_preserves_limit_cone
      (extendFanIsLimit (fun j => f (a j)) (limit.isLimit _) (limit.isLimit _))
    apply (isLimitMapConeFanMkEquiv _ _ _).symm.toFun
    refine IsLimit.ofIsoLimit
      (extendFanIsLimit (fun j => F.obj (f (a j)))
        (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)) ?_
    refine Cone.ext (Iso.refl _) ?_
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · exact (Category.id_comp _).symm
    · intro j _
      change F.map prod.snd ≫ F.map (Pi.π (fun i => f (a i.succ)) j) = _
      dsimp only [Iso.refl_hom, Fan.mk_π_app, Fin.cases_succ]
      rw [Category.id_comp, ← F.map_comp]
      rfl

private theorem over_hasBinaryProduct_of_hasPullback
    {C : Type*} [Category* C] {U : C} (V W : Over U) [HasPullback V.hom W.hom] :
    HasBinaryProduct V W :=
  HasLimit.mk ⟨_, (pullbackIsPullback V.hom W.hom).pullbackConeEquivBinaryFanFunctor⟩

private theorem overPost_preservesBinaryProduct
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {U : C} (V W : Over U) [HasPullback V.hom W.hom]
    [PreservesLimit (cospan V.hom W.hom) F] :
    PreservesLimit (pair V W) (Over.post F) := by
  let c := pullbackConeEquivBinaryFan.functor.obj (pullback.cone V.hom W.hom)
  apply preservesLimit_of_preserves_limit_cone
    (pullbackIsPullback V.hom W.hom).pullbackConeEquivBinaryFanFunctor
  apply (isLimitMapConeBinaryFanEquiv (Over.post F) c.fst c.snd).symm.toFun
  refine IsLimit.ofIsoLimit
    (isLimitOfHasPullbackOfPreservesLimit F V.hom W.hom).pullbackConeEquivBinaryFanFunctor ?_
  refine BinaryFan.ext (Over.isoMk (Iso.refl _) (by
    change 𝟙 (F.obj (pullback V.hom W.hom)) ≫ F.map (pullback.fst V.hom W.hom ≫ V.hom) =
      F.map (pullback.fst V.hom W.hom) ≫ F.map V.hom
    rw [Category.id_comp, F.map_comp])) ?_ ?_
  · ext
    change F.map (pullback.fst V.hom W.hom) =
      𝟙 (F.obj (pullback V.hom W.hom)) ≫ F.map (pullback.fst V.hom W.hom)
    rw [Category.id_comp]
  · ext
    change F.map (pullback.snd V.hom W.hom) =
      𝟙 (F.obj (pullback V.hom W.hom)) ≫ F.map (pullback.snd V.hom W.hom)
    rw [Category.id_comp]

private theorem overPost_preservesTerminal
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (U : C) :
    PreservesLimit (Functor.empty.{0} (Over U)) (Over.post F) := by
  apply preservesLimit_of_preserves_limit_cone (Over.mkIdTerminal (X := U))
  apply (isLimitMapConeEmptyConeEquiv (Over.post F) (Over.mk (𝟙 U))).symm.toFun
  exact IsTerminal.ofIso (Over.mkIdTerminal (X := F.obj U))
    (Over.isoMk (Iso.refl _) (by
      change 𝟙 (F.obj U) ≫ F.map (𝟙 U) = 𝟙 (F.obj U)
      rw [F.map_id, Category.comp_id]))

/-- A member of a covering `E` of `U` and any arrow over `U` have a pullback. -/
private theorem hasPullback_over_mk_of_mem
    {C : Type*} [Category* C] (K : Precoverage C) [K.HasPullbacks]
    {U : C} (E : PreZeroHypercover.{w} U) (hE : E.presieve₀ ∈ K U) (a : E.I₀) (V : Over U) :
    HasPullback (Over.mk (E.f a)).hom V.hom :=
  have : E.presieve₀.HasPullbacks V.hom := K.hasPullbacks_of_mem V.hom hE
  Presieve.HasPullbacks.hasPullback V.hom (Presieve.ofArrows.mk a)

private theorem preZeroHypercover_hasProducts
    {C : Type u} [Category.{v} C] (K : Precoverage C) [K.HasPullbacks]
    {U : C} (E : PreZeroHypercover.{w} U) (hE : E.presieve₀ ∈ K U) :
    ∀ (n : ℕ) (a : Fin (n + 1) → E.I₀),
      HasProduct (fun b ↦ Over.mk (E.f (a b))) := by
  have h (a : E.I₀) (V : Over U) : HasBinaryProduct (Over.mk (E.f a)) V := by
    have := hasPullback_over_mk_of_mem K E hE a V
    exact over_hasBinaryProduct_of_hasPullback _ _
  exact fun n a => hasProduct_fin_of_binaryProducts (fun a => Over.mk (E.f a)) h (n + 1) a

private theorem preZeroHypercover_preservesProducts
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    (K : Precoverage C) [K.HasPullbacks]
    {U : C} (E : PreZeroHypercover.{w} U) (hE : E.presieve₀ ∈ K U)
    (hF : ∀ (a : E.I₀) (V : Over U), PreservesLimit (cospan (E.f a) V.hom) F) :
    ∀ (n : ℕ) (a : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor (fun b ↦ Over.mk (E.f (a b)))) (Over.post F) := by
  let := overPost_preservesTerminal F U
  have h (a : E.I₀) (V : Over U) : HasBinaryProduct (Over.mk (E.f a)) V := by
    have := hasPullback_over_mk_of_mem K E hE a V
    exact over_hasBinaryProduct_of_hasPullback _ _
  have h' (a : E.I₀) (V : Over U) : PreservesLimit (pair (Over.mk (E.f a)) V) (Over.post F) := by
    have := hasPullback_over_mk_of_mem K E hE a V
    let : PreservesLimit (cospan (Over.mk (E.f a)).hom V.hom) F := hF a V
    exact overPost_preservesBinaryProduct F _ _
  exact fun n a => preservesProduct_fin_of_binaryProducts (Over.post F)
    (fun a => Over.mk (E.f a)) h h' (n + 1) a


end CoveringProducts

section CechMap

universe v' u' a b
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) {U : C} (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk ((E.map F).f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a)))) (Over.post F)]

attribute [local instance_reducible] CategoryTheory.PreZeroHypercover.map
attribute [local implicit_reducible]
  Stacks.CechSite.cechFormalCoproduct Stacks.CechSite.cechFormalCoproductMap

/-- The images under `Over.post F` of finitely many members of the covering `E` have a product:
they are the corresponding members of the covering `E.map F`. -/
local instance hasProduct_post (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    HasProduct (fun a ↦ (Over.post F).obj (Over.mk (E.f (i a)))) := by
  change HasProduct (fun a ↦ Over.mk ((E.map F).f (i a)))
  infer_instance

private def cechProductIso (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    F.obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ≅
      (∏ᶜ (fun a ↦ Over.mk ((E.map F).f (i a)))).left :=
  (Over.forget (F.obj U)).mapIso
    (PreservesProduct.iso (Over.post F) (fun a ↦ Over.mk (E.f (i a))))

private theorem cechProductIso_naturality {n m : ℕ}
    (g : Fin (n + 1) → Fin (m + 1)) (i : Fin (m + 1) → E.I₀) :
    F.map ((Stacks.CechSite.cechFormalCoproductMap E g).φ i).left ≫
        (cechProductIso F E n (i ∘ g)).hom =
      (cechProductIso F E m i).hom ≫
        ((Stacks.CechSite.cechFormalCoproductMap (E.map F) g).φ i).left := by
  have h₁ : (Stacks.CechSite.cechFormalCoproductMap E g).φ i =
      Pi.lift (fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (i b))) (g a)) := rfl
  have h₂ : (Stacks.CechSite.cechFormalCoproductMap (E.map F) g).φ i =
      Pi.lift (fun a ↦ Pi.π (fun b ↦ Over.mk ((E.map F).f (i b))) (g a)) := rfl
  change ((Over.post F).map ((Stacks.CechSite.cechFormalCoproductMap E g).φ i) ≫
    (PreservesProduct.iso (Over.post F) (fun a ↦ Over.mk (E.f (i (g a))))).hom).left =
    ((PreservesProduct.iso (Over.post F) (fun a ↦ Over.mk (E.f (i a)))).hom ≫
      (Stacks.CechSite.cechFormalCoproductMap (E.map F) g).φ i).left
  congr 1
  rw [h₁, h₂]
  apply Pi.hom_ext
  intro j
  simp only [PreservesProduct.iso_hom, Category.assoc, Pi.lift_comp_π,
    piComparison_comp_π, ← Functor.map_comp]
  simp [piComparison, PreZeroHypercover.map, Over.post]

variable {A : Type a} [Category.{b} A] [HasProducts.{w} A] (P : Dᵒᵖ ⥤ A)

private def cechCosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (Stacks.CechSite.cechSimplicialObject E)).obj
      ((Over.forget U).op ⋙ F.op ⋙ P) ≅
    (FormalCoproduct.cosimplicialObjectFunctor (Stacks.CechSite.cechSimplicialObject (E.map F))).obj
      ((Over.forget (F.obj U)).op ⋙ P) := by
  refine NatIso.ofComponents (fun n => Pi.mapIso (fun i =>
    P.mapIso (cechProductIso F E n.len i).symm.op)) ?_
  intro n m g
  apply Pi.hom_ext
  intro i
  dsimp [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    Stacks.CechSite.cechSimplicialObject, Stacks.CechSite.cechFormalCoproduct,
    Stacks.CechSite.cechFormalCoproductMap]
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.mapIso_hom_π_assoc, Pi.lift_comp_π,
    Pi.lift_comp_π_assoc, Functor.mapIso_inv, Iso.op_inv, Iso.symm_hom,
    ← P.map_comp, ← op_comp]
  congr 1
  apply congrArg P.map
  apply congrArg Quiver.Hom.op
  change (cechProductIso F E m.len i).inv ≫
      F.map ((Stacks.CechSite.cechFormalCoproductMap E g.toOrderHom.toFun).φ i).left =
    ((Stacks.CechSite.cechFormalCoproductMap (E.map F) g.toOrderHom.toFun).φ i).left ≫
      (cechProductIso F E n.len (i ∘ g.toOrderHom.toFun)).inv
  have h := cechProductIso_naturality F E g.toOrderHom.toFun i
  apply (cancel_mono (cechProductIso F E n.len (i ∘ g.toOrderHom.toFun)).hom).mp
  apply (cancel_epi (cechProductIso F E m.len i).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h


private def cechComplexMapIso [Preadditive A] :
    Stacks.CechSite.cechComplex E (F.op ⋙ P) ≅ Stacks.CechSite.cechComplex (E.map F) P :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso (cechCosimplicialIso F E P)

end CechMap

section ColimitAcyclicity

private theorem exists_covering_le_of_mem_toGrothendieck
    {C : Type*} [Category* C] (K : Coverage C) [K.toPrecoverage.HasIsos]
    (hbind : ∀ (X : C) (R : Presieve X) (T : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve Y),
      R ∈ K X → (∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : R f), T f hf ∈ K Y) → R.bind T ∈ K X)
    {U : C} {S : Sieve U} (hS : S ∈ K.toGrothendieck U) :
    ∃ R ∈ K U, R ≤ S := by
  change K.Saturate U S at hS
  induction hS with
  | of U R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top U =>
    exact ⟨Presieve.singleton (𝟙 U), Precoverage.mem_coverings_of_isIso (𝟙 U), by simp⟩
  | transitive U S T _ _ ihS ihT =>
    obtain ⟨R, hR, hleR⟩ := ihS
    have hex {V : C} (f : V ⟶ U) (hf : R f) := ihT (hleR _ _ hf)
    let T' : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Presieve V :=
      fun {V} f hf => (hex f hf).choose
    refine ⟨R.bind (fun _ f hf => T' f hf), ?_, ?_⟩
    · exact hbind U R T' hR (fun _ f hf => (hex f hf).choose_spec.1)
    · intro V f hf
      rcases hf with ⟨W, g, h, hg, hh, rfl⟩
      exact (hex h hg).choose_spec.2 _ g hh

private theorem cechCohomology_isZero_of_eq
    {C A : Type*} [Category* C] [Category* A] [Abelian A] [HasProducts.{w} A]
    {U : C} {E E' : PreZeroHypercover.{w} U} (h : E = E')
    [∀ (n : ℕ) (a : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (a b)))]
    [∀ (n : ℕ) (a : Fin (n + 1) → E'.I₀), HasProduct (fun b ↦ Over.mk (E'.f (a b)))]
    (P : Cᵒᵖ ⥤ A) (p : ℕ) (hP : IsZero (Stacks.CechSite.cechCohomology E P p)) :
    IsZero (Stacks.CechSite.cechCohomology E' P p) := by
  subst h
  exact hP

variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))


include hobj hhom hhom_inj hK in
private theorem colimitPrecoverage_properties :
    K.HasIsos ∧
      (∀ (Y : C) (R : Presieve Y) (T : ∀ ⦃Z : C⦄ (f : Z ⟶ Y), R f → Presieve Z),
        R ∈ K Y → (∀ ⦃Z : C⦄ (f : Z ⟶ Y) (hf : R f), T f hf ∈ K Z) → R.bind T ∈ K Y) ∧
      ∃ _ : K.HasPullbacks,
        ∀ (Y Z : C) (f : Z ⟶ Y) (R : Presieve Y) [R.HasPullbacks f],
          R ∈ K Y → R.pullbackArrows f ∈ K Z := by
  obtain ⟨K', hK', hi, ht, hp, hc⟩ :=
    CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.exists_precoverage_of_colimit
      D uC hu hobj hhom hhom_inj
  obtain rfl : K = K' :=
    Precoverage.ext (funext fun Y => Set.ext fun R => (hK Y R).trans (hK' Y R).symm)
  exact ⟨hi, ht, hp, hc⟩

include hK in
private theorem mappedCovering_mem {i : D.I} {U : D.C i}
    (E : PreZeroHypercover.{w} U)
    (hE : E.presieve₀ ∈ ((D.J i).toPrecoverage ⊓ Precoverage.finite (D.C i)) U) :
    (E.map (uC i)).presieve₀ ∈ K ((uC i).obj U) := by
  rw [PreZeroHypercover.presieve₀_map]
  exact (hK _ _).mpr ⟨i, U, rfl, E.presieve₀, hE.1, hE.2, rfl⟩

include hobj hhom hhom_inj in
private theorem colimitFunctor_preservesProducts (i : D.I) {U : D.C i}
    (E : PreZeroHypercover.{w} U)
    (hE : E.presieve₀ ∈ ((D.J i).toPrecoverage ⊓ Precoverage.finite (D.C i)) U) :
    ∀ (n : ℕ) (a : Fin (n + 1) → E.I₀),
      PreservesLimit (Discrete.functor (fun b ↦ Over.mk (E.f (a b)))) (Over.post (uC i)) := by
  let := D.hasPullbacks i
  apply preZeroHypercover_preservesProducts (uC i) _ E hE
  intro a V
  let := preservesLimit_cospan_of_mem D uC hu hobj hhom hhom_inj i hE
    (f := V.hom) (Presieve.ofArrows.mk a)
  exact preservesPullback_symmetry _ _ _

end ColimitAcyclicity

/-! ### Vanishing on the colimit site for a pointwise injective system

The Čech-vanishing criterion of Stacks 03F9 computes sheaf cohomology with coefficients in the
universe of the site, the small-site convention of the source. The two statements below are
therefore taken with the universe of the sites of the system containing the universes of the
index category and of the coefficients.
-/

section ColimitAcyclicitySiteCoefficients

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))


include hobj hhom hhom_inj hK in
/-- **The canonical colimit sheaf of a pointwise injective system is acyclic over every object of
the colimit site.** For a system `F` of abelian sheaves on the levels with every `F.obj i`
injective, the sheaf `systemColimitSheaf … F` — the sheafified Kan extension presenting
`colim fᵢ⁻¹Fᵢ` — has vanishing right derived sections over every object `U` of the colimit site
in every positive degree.

The proof is the Čech criterion of Stacks 03F9 along the coverings of the colimit site that come
from finite coverings of the levels: on such a covering the Čech complex of the colimit sheaf is
the colimit of the Čech complexes at the levels, and those are exact in positive degrees because
the `F.obj i` are injective. -/
private theorem systemColimitSheaf_cohomology_isZero_of_pointwise_injective
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    (hF : ∀ i, Injective (F.obj i)) (U : C) (p : ℕ) (hp : 0 < p) :
    IsZero (((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj (op U)).rightDerived p).obj
      (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F))) := by
  obtain ⟨hiso, hbind, hPB, hcov⟩ := colimitPrecoverage_properties D uC hu hobj hhom hhom_inj K hK
  let := hiso
  let := hPB
  let Kc : Coverage C := {
    __ := K
    pullback := by
      intro X Y f R hR
      let := K.hasPullbacks_of_mem f hR
      exact ⟨R.pullbackArrows f, hcov X Y f R hR,
        Presieve.FactorsThruAlong.pullbackArrows f R⟩ }
  let Cov : ∀ U : C,
      Set { E : PreZeroHypercover.{max u v w} U // E.sieve₀ ∈ K.toGrothendieck U } :=
    fun U => { E | ∃ (i : D.I) (X : D.C i) (Ei : PreZeroHypercover.{max u v w} X)
      (h : (uC i).obj X = U), Finite Ei.I₀ ∧
        Ei.presieve₀ ∈ ((D.J i).toPrecoverage ⊓ Precoverage.finite (D.C i)) X ∧
        E.1 = h ▸ Ei.map (uC i) }
  have hProd : ∀ {U : C}
      (E : { E : PreZeroHypercover.{max u v w} U // E.sieve₀ ∈ K.toGrothendieck U }),
      E ∈ Cov U → ∀ (n : ℕ) (a : Fin (n + 1) → E.1.I₀),
        HasProduct (fun b ↦ Over.mk (E.1.f (a b))) := by
    intro U E hE
    obtain ⟨i, X, Ei, rfl, _, hEi, he⟩ := hE
    have hmem : E.1.presieve₀ ∈ K ((uC i).obj X) := by
      rw [he]
      exact mappedCovering_mem D uC K hK Ei hEi
    exact preZeroHypercover_hasProducts K E.1 hmem
  have : HasExt.{max u v w} (Sheaf K.toGrothendieck (Ab.{max u v w})) :=
    hasExt_of_enoughInjectives _
  refine IsZero.of_iso ?_
    (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections K.toGrothendieck
      (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) p U).symm
  refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero
    K.toGrothendieck Set.univ Cov hProd (fun E hE => ?_) (fun V hV R hR => ?_)
    (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) (fun E hE q hq => ?_)
    U (Set.mem_univ U) p hp
  · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩
  · have hR' : R ∈ Kc.toGrothendieck V := by
      rwa [← Kc.toGrothendieck_toPrecoverage]
    obtain ⟨S, hS, hle⟩ := exists_covering_le_of_mem_toGrothendieck Kc hbind hR'
    obtain ⟨i, X, rfl, T, hT, hTf, rfl⟩ := (hK V S).mp hS
    let Ei : PreZeroHypercover.{max u v w} X := {
      I₀ := T.uncurry
      X a := a.1.1
      f a := a.1.2 }
    have he : Ei.presieve₀ = T := by
      funext Y f
      apply propext
      constructor
      · rintro ⟨a⟩
        exact a.2
      · intro hf
        exact Presieve.ofArrows.mk (show Ei.I₀ from ⟨⟨Y, f⟩, hf⟩)
    let : Fintype Ei.I₀ := hTf.fintype
    have hEi : Ei.presieve₀ ∈ ((D.J i).toPrecoverage ⊓ Precoverage.finite (D.C i)) X :=
      he ▸ ⟨hT, hTf⟩
    have hmap := mappedCovering_mem D uC K hK Ei hEi
    refine ⟨⟨Ei.map (uC i), K.generate_mem_toGrothendieck hmap⟩,
      ⟨i, X, Ei, rfl, inferInstance, hEi, rfl⟩, ?_⟩
    change Sieve.generate (Ei.map (uC i)).presieve₀ ≤ R
    rw [Sieve.generate_le_iff, PreZeroHypercover.presieve₀_map, he]
    exact hle
  · obtain ⟨i, X, Ei, rfl, hfin, hEi, he⟩ := hE
    let := hfin
    let := D.hasPullbacks i
    let := preZeroHypercover_hasProducts
      ((D.J i).toPrecoverage ⊓ Precoverage.finite (D.C i)) Ei hEi
    let := preZeroHypercover_hasProducts K (Ei.map (uC i))
      (mappedCovering_mem D uC K hK Ei hEi)
    -- the same instance, with its index type spelled `Ei.I₀`, as the Čech comparison needs it
    let : ∀ (n : ℕ) (a : Fin (n + 1) → Ei.I₀),
        HasProduct (fun b ↦ Over.mk ((Ei.map (uC i)).f (a b))) :=
      preZeroHypercover_hasProducts K (Ei.map (uC i))
        (mappedCovering_mem D uC K hK Ei hEi)
    let := colimitFunctor_preservesProducts D uC hu hobj hhom hhom_inj i Ei hEi
    have hz := stageCechCohomology_isZero_of_pointwise_injective
      D uC hu hhom hhom_inj F hF i Ei q hq
    have hz' := hz.of_iso ((HomologicalComplex.homologyFunctor (Ab.{max u v w})
      (ComplexShape.up ℕ) q).mapIso
      (cechComplexMapIso (uC i) Ei (systemKanExtension D uC hu F)).symm)
    let := hProd E ⟨i, X, Ei, rfl, hfin, hEi, he⟩
    exact cechCohomology_isZero_of_eq he.symm _ q hz'

include hobj hhom hhom_inj hK in
/-- **Any sheaf presenting `colim fᵢ⁻¹Fᵢ` for a pointwise injective system is acyclic over every
object of the colimit site.** This is
`systemColimitSheaf_cohomology_isZero_of_pointwise_injective` transported along the uniqueness
`colimitPresentation_uniqueIso` of a colimit presentation, so it applies to the sheaf `G` of the
given presentation `hG` rather than to the canonical model. -/
theorem cohomology_isZero_of_pointwise_injective
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    (hF : ∀ i, Injective (F.obj i))
    (G : Sheaf K.toGrothendieck (Ab.{max u v w}))
    (ι : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ G.obj)
    (hG : IsColimitPresentation D uC hu K F G ι)
    (U : C) (p : ℕ) (hp : 0 < p) :
    IsZero (((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
      (op U)).rightDerived p).obj G)) := by
  obtain ⟨e, _⟩ := colimitPresentation_uniqueIso D uC hu K F
    (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) G
    (systemKanUnit D uC hu F) ι
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F) hG
  exact (systemColimitSheaf_cohomology_isZero_of_pointwise_injective
    D uC hu hobj hhom hhom_inj K hK F hF U p hp).of_iso
      (((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
        (op U)).rightDerived p)).mapIso e.symm)



include hobj hhom hhom_inj hK in
/-- **Stacks 09YP's object-wise acyclicity in the `Ext` spelling.** For a pointwise injective
system and any sheaf `G` presenting `colim fᵢ⁻¹Fᵢ`, Mathlib's cohomology `Sheaf.H' G p U` over an
object `U` of the colimit site — the `Ext`-group out of the free abelian sheaf on `yoneda.obj U` —
vanishes in positive degrees. This is the form in which the vanishing is an input to the criterion
of Stacks 07A1 and to dimension shifting in the first variable. -/
public theorem isZero_H'_of_pointwise_injective
    [HasExt.{max u v w} (Sheaf K.toGrothendieck (Ab.{max u v w}))]
    [HasInjectiveResolutions (Sheaf K.toGrothendieck (Ab.{max u v w}))]
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    (hF : ∀ i, Injective (F.obj i))
    (G : Sheaf K.toGrothendieck (Ab.{max u v w}))
    (ι : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ G.obj)
    (hG : IsColimitPresentation D uC hu K F G ι)
    (U : C) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{max u v w, max u v w, max u v w} G p U) :=
  (cohomology_isZero_of_pointwise_injective D uC hu hobj hhom hhom_inj K hK F hF G ι hG
    U p hp).of_iso
    (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections K.toGrothendieck G p U)

end ColimitAcyclicitySiteCoefficients

/-! ### Leray's acyclicity lemma

An acyclic resolution computes the right derived functors, in Mathlib's `ℕ`-indexed
`Functor.rightDerived` form. This is the input that identifies the cohomology of the colimit
sheaf with the homology of the complex of sections of the colimit of a pointwise injective
resolution of the system.
-/

section Leray

variable {𝒜 : Type*} {ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory 𝒜] [HasDerivedCategory ℬ] [EnoughInjectives 𝒜]
  (Γ : 𝒜 ⥤ ℬ) [Γ.Additive]

omit [HasDerivedCategory 𝒜] in
/-- The right derived functor of `Γ` along the quasi-isomorphisms of `K⁺(𝒜)` exists: the
pointwise right derived functor does, by the injective derivability structure. Instance search
does not find this on its own within the default heartbeat budget, so it is produced here and
used as a local instance. -/
private lemma hasRightDerivedFunctor :
    (Γ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso 𝒜) := by
  let _ := (HomotopyCategory.Plus.localizerMorphism_derives
    (Γ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).hasPointwiseRightDerivedFunctor
  exact Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

variable [PreservesFiniteLimits Γ]

/-- An injective object is right acyclic for a left exact additive `Γ`. -/
private lemma rightAcyclic_of_injective
    [(Γ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso 𝒜)] (A : 𝒜) [Injective A] : Γ.rightAcyclic A :=
  ((Γ.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus A).2 inferInstance).2
    (fun i hi => Γ.isZero_rightDerivedPlus_obj_injective i (by omega) A)

omit [EnoughInjectives 𝒜] [PreservesFiniteLimits Γ] in
/-- The terms of the extension by zero along `ℕ ↪ ℤ` of a complex of `Γ`-acyclic objects are
`Γ`-acyclic: a degree in the image of the embedding gives back a term of the complex, and every
other degree gives a zero object. -/
private lemma rightAcyclic_extend_X
    [(Γ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso 𝒜)]
    (hI₀ : ∀ {Z : 𝒜}, IsZero Z → Γ.rightAcyclic Z) (K : CochainComplex 𝒜 ℕ)
    (hK : ∀ n, Γ.rightAcyclic (K.X n)) (i : ℤ) :
    Γ.rightAcyclic ((K.extend ComplexShape.embeddingUpNat).X i) := by
  by_cases hi : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, rfl⟩ := hi
    exact Γ.rightAcyclic.prop_of_iso (K.extendXIso _ rfl).symm (hK n)
  · exact hI₀ (K.isZero_extend_X _ i (by simpa using hi))

end Leray

/-- **Leray's acyclicity lemma, comparison form.** Let `Γ` be additive and left exact, let `Y`
be a cochain complex of `Γ`-acyclic objects with an augmentation `ε` from `X` in degree `0`
which is a quasi-isomorphism, let `J` be an injective resolution of `X`, and let `φ : Y ⟶ J`
be a map of complexes compatible with the augmentations. Then `Γ(φ)` is an isomorphism on
homology in every degree: the acyclic resolution `Y` computes `R ⁿ Γ (X)`. -/
private theorem isIso_homologyMap_map_of_rightAcyclic
    {𝒜 : Type*} {ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
    [EnoughInjectives 𝒜] (Γ : 𝒜 ⥤ ℬ) [Γ.Additive] [PreservesFiniteLimits Γ]
    {X : 𝒜} {Y : CochainComplex 𝒜 ℕ}
    (ε : (CochainComplex.single₀ 𝒜).obj X ⟶ Y) (hε : QuasiIso ε)
    (hY : ∀ (n q : ℕ), 0 < q → IsZero ((Γ.rightDerived q).obj (Y.X n)))
    (J : InjectiveResolution X) (φ : Y ⟶ J.cocomplex) (hφ : ε ≫ φ = J.ι) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) p) := by
  let _ := HasDerivedCategory.standard 𝒜
  let _ := HasDerivedCategory.standard ℬ
  let _ := hasRightDerivedFunctor Γ
  have := hε
  have : QuasiIso φ := by
    have : QuasiIso (ε ≫ φ) := by rw [hφ]; infer_instance
    exact quasiIso_of_comp_left ε φ
  have hI₁ : ∀ A : 𝒜, ∃ (B : 𝒜) (_ : Γ.rightAcyclic B) (i : A ⟶ B), Mono i := fun A =>
    ⟨Injective.under A, rightAcyclic_of_injective Γ _, Injective.ι A, inferInstance⟩
  have hI₂ : ∀ S : ShortComplex 𝒜, S.ShortExact → Γ.rightAcyclic S.X₁ →
      Γ.rightAcyclic S.X₂ → Γ.rightAcyclic S.X₃ ∧ (S.map Γ).ShortExact :=
    fun S hS h₁ h₂ => (Γ.rightAcyclic_and_shortExact_map_of_shortExact S hS).2.1 h₁ h₂
  have hI₀ : ∀ {Z : 𝒜}, IsZero Z → Γ.rightAcyclic Z :=
    Functor.RightAcyclicCriterion.zero_mem Γ Γ.rightAcyclic hI₁ hI₂
  have hYac : ∀ n, Γ.rightAcyclic (Y.X n) := fun n =>
    (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived Γ (Y.X n)).2 (hY n)
  have hJac : ∀ n, Γ.rightAcyclic (J.cocomplex.X n) := fun n => by
    have := J.injective n
    exact rightAcyclic_of_injective Γ _
  let e := ComplexShape.embeddingUpNat
  have hmain : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap φ e)) :=
    Functor.RightAcyclicCriterion.map_quasiIso Γ Γ.rightAcyclic hI₁ hI₂ _
      ⟨0, inferInstance⟩ ⟨0, inferInstance⟩
      (rightAcyclic_extend_X Γ hI₀ Y hYac) (rightAcyclic_extend_X Γ hI₀ J.cocomplex hJac)
  have hext : QuasiIso (HomologicalComplex.extendMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) e) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
      ((Stacks.DerivedIndexing.mapExtendNatIso Γ e).app Y)
      ((Stacks.DerivedIndexing.mapExtendNatIso Γ e).app J.cocomplex)
      (((Stacks.DerivedIndexing.mapExtendNatIso Γ e).hom.naturality φ).symm))).2 hmain
  have : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ e).1 hext
  exact (quasiIsoAt_iff_isIso_homologyMap _ p).1 inferInstance

/-! ### Homology commutes with exact colimits -/

section ExactColimitHomology

variable {J : Type*} [Category* J] {A : Type*} [Category* A] [Abelian A]
  [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]

/-- The colimit inclusions at an object `j : J`, assembled into a natural transformation
`(evaluation J A).obj j ⟶ colim` of functors `(J ⥤ A) ⥤ A`. -/
private def colimIota (j : J) : (evaluation J A).obj j ⟶ (colim : (J ⥤ A) ⥤ A) where
  app X := colimit.ι X j
  naturality _ _ _ := by simp

/-- The short complex of functors `J ⥤ A` attached to a diagram `G : J ⥤ ShortComplex A`;
its three terms are `G ⋙ π₁`, `G ⋙ π₂` and `G ⋙ π₃`. -/
private abbrev diagramShortComplex (G : J ⥤ ShortComplex A) : ShortComplex (J ⥤ A) :=
  (ShortComplex.FunctorEquivalence.inverse J A).obj G

/-- Homology in the functor category `J ⥤ A` is computed pointwise: the homology of
`diagramShortComplex G` is the diagram of the homologies of the `G.obj j`. -/
private def homologyDiagramIso (G : J ⥤ ShortComplex A) :
    G ⋙ ShortComplex.homologyFunctor A ≅ (diagramShortComplex G).homology :=
  NatIso.ofComponents
    (fun j => (diagramShortComplex G).mapHomologyIso ((evaluation J A).obj j)) (by
      intro j j' f
      have h := ShortComplex.homologyMap_mapNatTrans (diagramShortComplex G)
        ((evaluation J A).map f)
      have h2 : ((diagramShortComplex G).mapHomologyIso ((evaluation J A).obj j)).hom ≫
          (diagramShortComplex G).homology.map f =
            ShortComplex.homologyMap ((diagramShortComplex G).mapNatTrans
              ((evaluation J A).map f)) ≫
              ((diagramShortComplex G).mapHomologyIso ((evaluation J A).obj j')).hom := by
        rw [h]; simp
      exact h2.symm)

/-- The comparison isomorphism between the colimit of the homologies of a diagram of short
complexes and the homology of the degreewise colimit, available because `colim : (J ⥤ A) ⥤ A`
is exact and hence preserves homology. -/
private def colimitHomologyIso (G : J ⥤ ShortComplex A) :
    colimit (G ⋙ ShortComplex.homologyFunctor A) ≅
      ((diagramShortComplex G).map (colim : (J ⥤ A) ⥤ A)).homology :=
  (colim : (J ⥤ A) ⥤ A).mapIso (homologyDiagramIso G) ≪≫
    ((diagramShortComplex G).mapHomologyIso colim).symm

/-- **Homology of short complexes commutes with exact colimits.** If colimits of shape `J` in
the abelian category `A` are exact, then `ShortComplex.homologyFunctor A` preserves them. -/
instance preservesColimitsOfShape_shortComplex_homologyFunctor :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor A) where
  preservesColimit {G} :=
    preservesColimit_of_preserves_colimit_cocone (ShortComplex.isColimitColimitCocone G)
      (IsColimit.ofIsoColimit (colimit.isColimit (G ⋙ ShortComplex.homologyFunctor A))
        (Cocone.ext (colimitHomologyIso G) (fun j => by
          have h := ShortComplex.homologyMap_mapNatTrans (diagramShortComplex G) (colimIota j)
          have h2 : colimit.ι (G ⋙ ShortComplex.homologyFunctor A) j ≫
              (colimitHomologyIso G).hom =
                ShortComplex.homologyMap
                  ((diagramShortComplex G).mapNatTrans (colimIota j)) := by
            rw [h]
            simp only [colimitHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
            rw [colimit.ι_map_assoc]
            simp only [homologyDiagramIso, colimIota]
            rfl
          exact h2)))

/-- **Homology commutes with exact colimits.** If a cocone over a diagram of homological
complexes is a colimit cocone in every degree, and colimits of that shape are exact, then its
image under the degree-`p` homology functor is a colimit cocone. -/
private def isColimit_mapCocone_homologyFunctor {ι : Type*} {c : ComplexShape ι}
    (𝒦 : J ⥤ HomologicalComplex A c) (s : Cocone 𝒦)
    (hs : ∀ n : ι, IsColimit ((HomologicalComplex.eval A c n).mapCocone s)) (p : ι) :
    IsColimit ((HomologicalComplex.homologyFunctor A c p).mapCocone s) :=
  isColimitOfPreserves (ShortComplex.homologyFunctor A)
    (ShortComplex.isColimitOfIsColimitπ
      ((HomologicalComplex.shortComplexFunctor A c p).mapCocone s)
      (hs (c.prev p)) (hs p) (hs (c.next p)))

end ExactColimitHomology

/-! ### The comparison map out of a resolution

Mathlib's `InjectiveResolution.desc` lifts a morphism of objects to a morphism of injective
resolutions. Here the source complex need only be a resolution and the target complex need only
have injective terms, which is what the colimit of a pointwise injective resolution of the
system provides.
-/

section ComparisonMap

variable {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] {P : 𝒞}

/-- The degree-zero component of the comparison map: `f` extends along the monomorphism `ε`
because `T.X 0` is injective. -/
private def liftFromResolutionZero {Y : CochainComplex 𝒞 ℕ} (ε : P ⟶ Y.X 0) (hεmono : Mono ε)
    {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0) :
    Y.X 0 ⟶ T.X 0 := by
  letI : Injective (T.X 0) := hT 0
  letI : Mono ε := hεmono
  exact Injective.factorThru f ε

/-- The degree-zero component of the comparison map extends `f`. -/
private theorem liftFromResolutionZero_comm {Y : CochainComplex 𝒞 ℕ} (ε : P ⟶ Y.X 0)
    (hεmono : Mono ε) {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0) :
    ε ≫ liftFromResolutionZero ε hεmono hT f = f := by
  have : Injective (T.X 0) := hT 0
  have : Mono ε := hεmono
  exact Injective.comp_factorThru f ε

/-- The degree-one component of the comparison map, obtained from exactness at `Y.X 0`. -/
private def liftFromResolutionOne {Y : CochainComplex 𝒞 ℕ} (ε : P ⟶ Y.X 0) (hεmono : Mono ε)
    (hε : ε ≫ Y.d 0 1 = 0) (hex₀ : (ShortComplex.mk ε (Y.d 0 1) hε).Exact)
    {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) : Y.X 1 ⟶ T.X 1 := by
  letI : Injective (T.X 1) := hT 1
  refine hex₀.descToInjective (liftFromResolutionZero ε hεmono hT f ≫ T.d 0 1) ?_
  rw [show (ShortComplex.mk ε (Y.d 0 1) hε).f = ε from rfl, ← Category.assoc,
    liftFromResolutionZero_comm ε hεmono hT f]
  exact hf

/-- The degree-one component of the comparison map is a chain map in degree `0`. -/
private theorem liftFromResolutionOne_comm {Y : CochainComplex 𝒞 ℕ} (ε : P ⟶ Y.X 0)
    (hεmono : Mono ε) (hε : ε ≫ Y.d 0 1 = 0) (hex₀ : (ShortComplex.mk ε (Y.d 0 1) hε).Exact)
    {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) :
    Y.d 0 1 ≫ liftFromResolutionOne ε hεmono hε hex₀ hT f hf =
      liftFromResolutionZero ε hεmono hT f ≫ T.d 0 1 :=
  hex₀.comp_descToInjective _ _

/-- The inductive step of the comparison map, obtained from exactness at `Y.X (n + 1)`. -/
private def liftFromResolutionSucc {Y : CochainComplex 𝒞 ℕ}
    (hexs : ∀ n : ℕ, (ShortComplex.mk (Y.d n (n + 1)) (Y.d (n + 1) (n + 2))
      (Y.d_comp_d n (n + 1) (n + 2))).Exact)
    {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (n : ℕ)
    (g : Y.X n ⟶ T.X n) (g' : Y.X (n + 1) ⟶ T.X (n + 1))
    (w : Y.d n (n + 1) ≫ g' = g ≫ T.d n (n + 1)) :
    Σ' g'' : Y.X (n + 2) ⟶ T.X (n + 2),
      Y.d (n + 1) (n + 2) ≫ g'' = g' ≫ T.d (n + 1) (n + 2) := by
  letI : Injective (T.X (n + 2)) := hT (n + 2)
  exact ⟨(hexs n).descToInjective (g' ≫ T.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
    (hexs n).comp_descToInjective _ _⟩

/-- **The comparison map out of a resolution.** `ε : P ⟶ Y.X 0` exhibits the nonnegative cochain
complex `Y` as a resolution of `P`; `T` is a nonnegative cochain complex with injective terms and
`f : P ⟶ T.X 0` kills the first differential. Then `f` extends to a map of complexes `Y ⟶ T`. -/
private def liftFromResolution {Y : CochainComplex 𝒞 ℕ} (ε : P ⟶ Y.X 0) (hεmono : Mono ε)
    (hε : ε ≫ Y.d 0 1 = 0) (hex₀ : (ShortComplex.mk ε (Y.d 0 1) hε).Exact)
    (hexs : ∀ n : ℕ, (ShortComplex.mk (Y.d n (n + 1)) (Y.d (n + 1) (n + 2))
      (Y.d_comp_d n (n + 1) (n + 2))).Exact)
    {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) : Y ⟶ T :=
  CochainComplex.mkHom _ _ (liftFromResolutionZero ε hεmono hT f)
    (liftFromResolutionOne ε hεmono hε hex₀ hT f hf)
    (liftFromResolutionOne_comm ε hεmono hε hex₀ hT f hf).symm
    fun n ⟨g, g', w⟩ => ⟨(liftFromResolutionSucc hexs hT n g g' w.symm).1,
      (liftFromResolutionSucc hexs hT n g g' w.symm).2.symm⟩

/-- The comparison map extends `f`. -/
private theorem liftFromResolution_comm {Y : CochainComplex 𝒞 ℕ} (ε : P ⟶ Y.X 0)
    (hεmono : Mono ε) (hε : ε ≫ Y.d 0 1 = 0) (hex₀ : (ShortComplex.mk ε (Y.d 0 1) hε).Exact)
    (hexs : ∀ n : ℕ, (ShortComplex.mk (Y.d n (n + 1)) (Y.d (n + 1) (n + 2))
      (Y.d_comp_d n (n + 1) (n + 2))).Exact)
    {T : CochainComplex 𝒞 ℕ} (hT : ∀ n, Injective (T.X n)) (f : P ⟶ T.X 0)
    (hf : f ≫ T.d 0 1 = 0) :
    ε ≫ (liftFromResolution ε hεmono hε hex₀ hexs hT f hf).f 0 = f := by
  rw [liftFromResolution, CochainComplex.mkHom_f_0]
  exact liftFromResolutionZero_comm ε hεmono hT f

/-- The degree-zero part of an augmentation from `P` kills the first differential. -/
private theorem augmentation_f_zero_comp_d {Y : CochainComplex 𝒞 ℕ}
    (ε : (CochainComplex.single₀ 𝒞).obj P ⟶ Y) : ε.f 0 ≫ Y.d 0 1 = 0 := by
  rw [ε.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]

/-- A nonnegative cochain complex with a quasi-isomorphic augmentation from `P` in degree `0`
is exact at `P ⟶ Y⁰ ⟶ Y¹`, and the augmentation is a monomorphism in degree `0`. -/
private theorem exact₀_and_mono_of_quasiIso {Y : CochainComplex 𝒞 ℕ}
    (ε : (CochainComplex.single₀ 𝒞).obj P ⟶ Y) (h : QuasiIso ε) :
    (ShortComplex.mk (ε.f 0) (Y.d 0 1) (augmentation_f_zero_comp_d ε)).Exact ∧ Mono (ε.f 0) := by
  have := h
  have h0 : QuasiIsoAt ε 0 := inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros] at h0
  · exact h0
  · rfl
  · rfl
  · simp only [HomologicalComplex.shortComplexFunctor'_obj_f]
    exact Y.shape 0 0 (by simp)

/-- Such a complex is exact in the positive degrees. -/
private theorem exact_succ_of_quasiIso {Y : CochainComplex 𝒞 ℕ}
    (ε : (CochainComplex.single₀ 𝒞).obj P ⟶ Y) (h : QuasiIso ε) (n : ℕ) :
    (ShortComplex.mk (Y.d n (n + 1)) (Y.d (n + 1) (n + 2))
      (Y.d_comp_d n (n + 1) (n + 2))).Exact := by
  have := h
  have hex : Y.ExactAt (n + 1) := by
    rw [← quasiIsoAt_iff_exactAt ε (n + 1) (CochainComplex.exactAt_succ_single_obj _ _)]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 hex

/-- **The comparison map out of a resolution, for a quasi-isomorphic augmentation.** A nonnegative
cochain complex `Y` with a quasi-isomorphic augmentation `ε` from `P` maps to any injective
resolution `J` of `P`. -/
private def liftOfQuasiIso {Y : CochainComplex 𝒞 ℕ}
    (ε : (CochainComplex.single₀ 𝒞).obj P ⟶ Y) (h : QuasiIso ε) (J : InjectiveResolution P) :
    Y ⟶ J.cocomplex :=
  liftFromResolution (ε.f 0) (exact₀_and_mono_of_quasiIso ε h).2 (augmentation_f_zero_comp_d _)
    (exact₀_and_mono_of_quasiIso ε h).1 (exact_succ_of_quasiIso _ h) J.injective (J.ι.f 0)
    J.ι_f_zero_comp_complex_d

/-- The comparison map is compatible with the two augmentations. -/
private theorem liftOfQuasiIso_ι {Y : CochainComplex 𝒞 ℕ}
    (ε : (CochainComplex.single₀ 𝒞).obj P ⟶ Y) (h : QuasiIso ε) (J : InjectiveResolution P) :
    ε ≫ liftOfQuasiIso ε h J = J.ι := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero => exact liftFromResolution_comm _ _ _ _ _ _ _ _
  | succ n => exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).eq_of_src _ _

end ComparisonMap

/-! ### Complexes built from monomorphisms and their cokernels -/

section MonoCokernelComplex

variable {A : Type*} [Category* A] [Abelian A] (Z I : ℕ → A)
  (ι : ∀ n, Z n ⟶ I n) (π : ∀ n, I n ⟶ Z (n + 1))
  (hmono : ∀ n, Mono (ι n)) (hepi : ∀ n, Epi (π n))
  (hzero : ∀ n, ι n ≫ π n = 0)
  (hex : ∀ n, (ShortComplex.mk (ι n) (π n) (hzero n)).Exact)
  (hdd : ∀ n, (π n ≫ ι (n + 1)) ≫ (π (n + 1) ≫ ι (n + 1 + 1)) = 0)

include hmono hepi hzero hex in
/-- A cochain complex whose differentials factor as the cokernel of a monomorphism followed by
the monomorphism of the next stage is exact in the positive degrees. -/
private theorem exactAt_succ_of_monoCokernel (n : ℕ) :
    (CochainComplex.of I (fun n => π n ≫ ι (n + 1)) hdd).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [CochainComplex.of_d]
  let := hmono (n + 1 + 1)
  let := hepi n
  exact exact_comp_epi_mono (π n) (ι (n + 1)) (π (n + 1)) (ι (n + 1 + 1))
    (hzero (n + 1)) (hex (n + 1))

include hmono hepi hzero hex in
/-- Such a complex, augmented by `Z 0` along `ι 0`, is a resolution of `Z 0`. -/
private theorem quasiIso_single₀_of_monoCokernel
    (h0 : ι 0 ≫ (CochainComplex.of I (fun n => π n ≫ ι (n + 1)) hdd).d 0 1 = 0) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv
      (CochainComplex.of I (fun n => π n ≫ ι (n + 1)) hdd) (Z 0)).symm ⟨ι 0, h0⟩) := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have hd : CochainComplex.of.d I (fun m => π m ≫ ι (m + 1)) 0 1 = π 0 ≫ ι 1 :=
        CochainComplex.of_d I (fun m => π m ≫ ι (m + 1)) 0
      simp only [HomologicalComplex.shortComplexFunctor', hd]
      let := hmono 0
      let := hmono 1
      let := hepi 0
      have hexc := exact_comp_epi_mono (𝟙 _) (ι 0) (π 0) (ι 1) (hzero 0) (hex 0)
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨hexc, by dsimp; infer_instance⟩
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
          (C := CochainComplex.of I (fun m => π m ≫ ι (m + 1)) hdd) (X := Z 0) (ι 0) h0).symm
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact exactAt_succ_of_monoCokernel Z I ι π hmono hepi hzero hex hdd n
    · exact CochainComplex.exactAt_succ_single_obj _ _⟩

end MonoCokernelComplex

/-! ### The colimit of a pointwise injective resolution of the system

The system `F` has a resolution by pointwise injective systems (`systemResolutionComplex`), and
the colimit over the system is exact, so the colimit sheaves of the terms of that resolution form
a resolution of `colim fᵢ⁻¹Fᵢ`. Each of its terms is acyclic for the sections over any object of
the colimit site, by the vanishing of Tag 09YP's companion computation
(`systemColimitSheaf_cohomology_isZero_of_pointwise_injective`), so Leray's acyclicity lemma
identifies the cohomology of `colim fᵢ⁻¹Fᵢ` with the homology of its complex of sections.
-/

section ColimitResolution

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)

/-- The colimit sheaf of the `n`-th term of the pointwise injective resolution of the system. -/
private abbrev colimitResolutionObj (n : ℕ) : Sheaf K.toGrothendieck (Ab.{max u v w}) :=
  systemColimitSheaf D uC hu hobj hhom hhom_inj K hK (injectiveSystem D (systemSyzygy D F n))

/-- The colimit of the monomorphism of the `n`-th syzygy into its injective system. -/
private def colimitResolutionMono (n : ℕ) :
    systemColimitSheaf D uC hu hobj hhom hhom_inj K hK (systemSyzygy D F n) ⟶
      colimitResolutionObj D uC hu hobj hhom hhom_inj K hK F n :=
  systemColimitMap D uC hu hobj hhom hhom_inj K hK (injectiveSystemι D (systemSyzygy D F n))

/-- The colimit of the cokernel projection onto the next syzygy. -/
private def colimitResolutionCokernel (n : ℕ) :
    colimitResolutionObj D uC hu hobj hhom hhom_inj K hK F n ⟶
      systemColimitSheaf D uC hu hobj hhom hhom_inj K hK (systemSyzygy D F (n + 1)) :=
  systemColimitMap D uC hu hobj hhom hhom_inj K hK
    (systemCokernelπ D (injectiveSystemι D (systemSyzygy D F n)))

/-- The colimit of a syzygy sequence is a complex: the cokernel projection of one stage is
killed by the monomorphism of the same stage. -/
private theorem colimitResolution_mono_comp_cokernel (n : ℕ) :
    colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F n ≫
      colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F n = 0 :=
  systemColimitMap_cokernel_condition D uC hu hobj hhom hhom_inj K hK _

/-- The differentials of the colimit resolution compose to zero. -/
private theorem colimitResolution_d_comp_d (n : ℕ) :
    (colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F n ≫
        colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F (n + 1)) ≫
      (colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F (n + 1) ≫
        colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F (n + 1 + 1)) = 0 := by
  have h := colimitResolution_mono_comp_cokernel D uC hu hobj hhom hhom_inj K hK F (n + 1)
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp

/-- The complex of colimit sheaves of the pointwise injective resolution of the system. -/
private def colimitResolutionComplex :
    CochainComplex (Sheaf K.toGrothendieck (Ab.{max u v w})) ℕ :=
  CochainComplex.of (colimitResolutionObj D uC hu hobj hhom hhom_inj K hK F)
    (fun n => colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F n ≫
      colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F (n + 1))
    (colimitResolution_d_comp_d D uC hu hobj hhom hhom_inj K hK F)

/-- The differential of the colimit resolution, by definition. -/
private theorem colimitResolutionComplex_d_eq (n : ℕ) :
    (colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F).d n (n + 1) =
      colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F n ≫
        colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F (n + 1) := by
  dsimp only [colimitResolutionComplex]
  exact CochainComplex.of_d _ _ n

/-- The differential of the colimit resolution is the colimit of the differential of the
resolution of the system. -/
private theorem colimitResolutionComplex_d (n : ℕ) :
    (colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F).d n (n + 1) =
      systemColimitMap D uC hu hobj hhom hhom_inj K hK (systemResolutionDifferential D F n) :=
  (colimitResolutionComplex_d_eq D uC hu hobj hhom hhom_inj K hK F n).trans
    (systemColimitMap_comp D uC hu hobj hhom hhom_inj K hK _ _).symm

/-- The augmentation of the colimit resolution by the colimit sheaf of the system. -/
private def colimitResolutionι :
    (CochainComplex.single₀ _).obj (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) ⟶
      colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F 0, by
      have hd := colimitResolutionComplex_d_eq D uC hu hobj hhom hhom_inj K hK F 0
      have h := colimitResolution_mono_comp_cokernel D uC hu hobj hhom hhom_inj K hK F 0
      exact (congrArg
          (fun m => colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F 0 ≫ m) hd).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F 1)
            h).trans zero_comp))⟩

variable [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck]

/-- The colimit over the system of the defining short exact sequence of a syzygy is short exact:
the colimit preserves the monomorphism and the cokernel. -/
private theorem colimitSystem_cokernelSequence_exact
    {G H : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    (f : InverseSystemOfFiniteSites.AbelianSheafSystem.Hom G H) :
    (ShortComplex.mk (systemColimitMap D uC hu hobj hhom hhom_inj K hK f)
      (systemColimitMap D uC hu hobj hhom hhom_inj K hK (systemCokernelπ D f))
      (systemColimitMap_cokernel_condition D uC hu hobj hhom hhom_inj K hK f)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (systemColimitMap_isCokernel D uC hu hobj hhom hhom_inj K hK f)

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- Each colimit monomorphism of the syzygy sequence is a monomorphism. -/
private theorem mono_colimitResolutionMono (n : ℕ) :
    Mono (colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F n) :=
  systemColimitMap_mono D uC hu hobj hhom hhom_inj K hK _
    (injectiveSystemι_mono D (systemSyzygy D F n))

/-- Each colimit cokernel projection of the syzygy sequence is an epimorphism. -/
private theorem epi_colimitResolutionCokernel (n : ℕ) :
    Epi (colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F n) :=
  systemColimitMap_epi D uC hu hobj hhom hhom_inj K hK _
    (fun i => by change Epi (cokernel.π _); infer_instance)

/-- The colimit of a syzygy sequence is short exact. -/
private theorem colimitResolution_shortComplex_exact (n : ℕ) :
    (ShortComplex.mk (colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F n)
      (colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F n)
      (colimitResolution_mono_comp_cokernel D uC hu hobj hhom hhom_inj K hK F n)).Exact :=
  colimitSystem_cokernelSequence_exact D uC hu hobj hhom hhom_inj K hK _

/-- The colimit resolution is exact in the positive degrees. -/
private theorem colimitResolutionComplex_exactAt_succ (n : ℕ) :
    (colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F).ExactAt (n + 1) :=
  exactAt_succ_of_monoCokernel _ _ _ _
    (mono_colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F)
    (epi_colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolution_mono_comp_cokernel D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolution_shortComplex_exact D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolution_d_comp_d D uC hu hobj hhom hhom_inj K hK F) n

/-- The augmentation of the colimit resolution is a quasi-isomorphism: the colimit resolution
is a resolution of the colimit sheaf of the system. -/
private theorem colimitResolutionι_quasiIso :
    QuasiIso (colimitResolutionι D uC hu hobj hhom hhom_inj K hK F) :=
  quasiIso_single₀_of_monoCokernel _ _ _ _
    (mono_colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F)
    (epi_colimitResolutionCokernel D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolution_mono_comp_cokernel D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolution_shortComplex_exact D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolution_d_comp_d D uC hu hobj hhom hhom_inj K hK F) _

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- Every term of the colimit resolution is acyclic for the sections over any object of the
colimit site. -/
private theorem colimitResolutionObj_isZero_rightDerived (U : C) (n q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj (op U)).rightDerived q).obj
      (colimitResolutionObj D uC hu hobj hhom hhom_inj K hK F n)) :=
  systemColimitSheaf_cohomology_isZero_of_pointwise_injective D uC hu hobj hhom hhom_inj K hK
    (injectiveSystem D (systemSyzygy D F n))
    (injectiveSystem_injective D (systemSyzygy D F n)) U q hq

/-- A chosen injective resolution of the colimit sheaf of the system. -/
private def colimitInjectiveResolution :
    InjectiveResolution (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) :=
  InjectiveResolution.of _

/-- The comparison of the colimit resolution with the chosen injective resolution of the colimit
sheaf, extending the identity. -/
private def colimitResolutionComparison :
    colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F ⟶
      (colimitInjectiveResolution D uC hu hobj hhom hhom_inj K hK F).cocomplex :=
  liftOfQuasiIso _ (colimitResolutionι_quasiIso D uC hu hobj hhom hhom_inj K hK F) _

/-- The comparison map is compatible with the two augmentations. -/
private theorem colimitResolutionComparison_ι :
    colimitResolutionι D uC hu hobj hhom hhom_inj K hK F ≫
        colimitResolutionComparison D uC hu hobj hhom hhom_inj K hK F =
      (colimitInjectiveResolution D uC hu hobj hhom hhom_inj K hK F).ι :=
  liftOfQuasiIso_ι _ _ _

/-- **The colimit resolution computes the cohomology of the colimit sheaf.** The comparison with
the chosen injective resolution induces an isomorphism on the homology of the complexes of
sections over any object of the colimit site. -/
private theorem isIso_homologyMap_colimitResolutionComparison (U : C) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
        (op U)).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (colimitResolutionComparison D uC hu hobj hhom hhom_inj K hK F)) p) := by
  let := preservesFiniteLimits_sheafSections_obj K.toGrothendieck (op U)
  exact isIso_homologyMap_map_of_rightAcyclic _
    (colimitResolutionι D uC hu hobj hhom hhom_inj K hK F)
    (colimitResolutionι_quasiIso D uC hu hobj hhom hhom_inj K hK F)
    (fun n q hq => colimitResolutionObj_isZero_rightDerived D uC hu hobj hhom hhom_inj K hK F
      U n q hq)
    _ _ (colimitResolutionComparison_ι D uC hu hobj hhom hhom_inj K hK F) p


/-! ### The general case

For any system `G` of abelian sheaves, the sections over `u_a(X)` of the members of `G` form a
diagram over the arrows `a : j ⟶ i` whose colimit is the sections over `uᵢ(X)` of
`colim fᵢ⁻¹Gᵢ`; that is the case `p = 0`. Applying this in every degree of the pointwise injective
resolution of `F`, and using that homology commutes with the exact colimits of `(Over i)ᵒᵖ`,
identifies `Hᵖ(uᵢ(X), colim fᵢ⁻¹Fᵢ)` with the colimit of the groups `Hᵖ(u_a(X), F_j)`.
-/

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- A map on cohomology induced by a lift of `φ` to injective resolutions, read on sections and
transported along an identification of the target object, is the canonical cohomology map. -/
private theorem isCohomologyMap_of_sectionsMapTo
    {A B : Type w} [SmallCategory A] [SmallCategory B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} (G : A ⥤ B)
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P.obj ⟶ G.op ⋙ Q.obj) (I : InjectiveResolution P) (J : InjectiveResolution Q)
    (ψ : ∀ n : ℕ, (I.cocomplex.X n).obj ⟶ G.op ⋙ (J.cocomplex.X n).obj)
    (hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
      (I.cocomplex.d n n').hom ≫ ψ n' =
        ψ n ≫ Functor.whiskerLeft G.op (J.cocomplex.d n n').hom)
    (h0 : (I.ι.f 0).hom ≫ ψ 0 = φ ≫ Functor.whiskerLeft G.op (J.ι.f 0).hom)
    (V : A) (W : B) (h : G.obj V = W) (p : ℕ)
    (m : (((sheafSections JA (Ab.{max w s})).obj (op V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex ⟶
        (((sheafSections JB (Ab.{max w s})).obj (op W)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex)
    (hm : ∀ n, m.f n = sectionsMapTo G (ψ n) V W h)
    {mm : ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q)}
    (hmm : mm =
      (I.isoRightDerivedObj ((sheafSections JA (Ab.{max w s})).obj (op V)) p).hom ≫
        HomologicalComplex.homologyMap m p ≫
        (J.isoRightDerivedObj ((sheafSections JB (Ab.{max w s})).obj (op W)) p).inv ≫
        cohomologyCongr JB p h.symm Q) :
    IsCohomologyMap JA JB G φ V p mm := by
  subst hmm
  subst W
  refine ⟨I, J, ψ, hψ, h0, ?_⟩
  have hmm : m = sectionsComplexMap G I.cocomplex J.cocomplex ψ hψ V := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [hm n]
    simp [sectionsMapTo, sectionsComplexMap]
  rw [hmm]
  simp only [cohomologyCongr, eqToHom_refl, Category.comp_id]

variable (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)

variable (e : systemColimitSheaf.{v, u, max u v w, max u v w}
    D uC hu hobj hhom hhom_inj K hK F ≅ 𝒢)

variable (he : ∀ j, systemKanUnit.{v, u, max u v w, max u v w} D uC hu F j ≫
    Functor.whiskerLeft (uC j).op e.hom.hom = ι j)
  (i : D.I) (X : D.C i)

/-- The `n`-th term of the pointwise injective resolution of the system `F`. -/
private abbrev resolutionSystem (n : ℕ) :
    InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D :=
  injectiveSystem D (systemSyzygy D F n)

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- The differential of the injective resolution of `F_j` provided by the resolution of the
system, by definition. -/
private theorem systemResolutionComplex_d (j : D.I) (n : ℕ) :
    (systemResolutionComplex D F j).d n (n + 1) =
      (systemResolutionDifferential D F n).app j := by
  dsimp only [systemResolutionComplex]
  exact CochainComplex.of_d _ _ n

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- The augmentation of the injective resolution of `F_j` provided by the resolution of the
system, by definition. -/
private theorem systemResolutionι_f_zero (j : D.I) :
    (systemResolutionι D F j).f 0 = (injectiveSystemι D F).app j := rfl

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- The diagram, over the arrows `a : j ⟶ i`, of complexes of sections over `u_a(X)` of the
pointwise injective resolution of the system. -/
@[implicit_reducible]
private def resolutionSectionsDiagram :
    (Over i)ᵒᵖ ⥤ CochainComplex (Ab.{max u v w}) ℕ where
  obj A := (((sheafSections (D.J A.unop.left) (Ab.{max u v w})).obj
      (op ((D.u A.unop.hom).obj X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (systemResolutionComplex D F A.unop.left)
  map {A B} f :=
    { f n := (sectionsDiagram D (resolutionSystem D F n) i X).map f
      comm' n n' h := by
        obtain rfl : n + 1 = n' := h
        have hB := congrArg (((sheafSections (D.J B.unop.left) (Ab.{max u v w})).obj
            (op ((D.u B.unop.hom).obj X))).map) (systemResolutionComplex_d D F B.unop.left n)
        have hA := congrArg (((sheafSections (D.J A.unop.left) (Ab.{max u v w})).obj
            (op ((D.u A.unop.hom).obj X))).map) (systemResolutionComplex_d D F A.unop.left n)
        exact (congrArg (fun z => (sectionsDiagram D (resolutionSystem D F n) i X).map f ≫ z)
            hB).trans
          (((sectionsDiagramMap (systemResolutionDifferential D F n) i X).naturality f).trans
            (congrArg
              (fun z => z ≫ (sectionsDiagram D (resolutionSystem D F (n + 1)) i X).map f)
              hA).symm) }
  map_id A := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (sectionsDiagram D (resolutionSystem D F n) i X).map_id A
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (sectionsDiagram D (resolutionSystem D F n) i X).map_comp f g

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- In each degree the diagram of complexes of sections is the diagram of sections of the
corresponding term of the resolution. -/
private def resolutionSectionsDiagram_evalIso (n : ℕ) :
    resolutionSectionsDiagram D F i X ⋙
        HomologicalComplex.eval (Ab.{max u v w}) (ComplexShape.up ℕ) n ≅
      sectionsDiagram D (resolutionSystem D F n) i X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _f =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The complex of sections over `uᵢ(X)` of the colimit of the pointwise injective resolution of
the system. -/
private abbrev colimitResolutionSections : CochainComplex (Ab.{max u v w}) ℕ :=
  (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
      (op ((uC i).obj X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F)

/-- The leg at `A : Over i` of the cocone of the diagram of complexes of sections: in each degree
the structure map of the colimit of that term of the resolution. -/
private def resolutionSectionsLeg (A : Over i) :
    (resolutionSectionsDiagram D F i X).obj (op A) ⟶
      colimitResolutionSections D uC hu hobj hhom hhom_inj K hK F i X where
  f n := (sectionsCocone D uC hu (resolutionSystem D F n)
    (systemKanExtension D uC hu (resolutionSystem D F n))
    (systemKanUnit D uC hu (resolutionSystem D F n))
    (systemKanUnit_compatible D uC hu (resolutionSystem D F n)) i X).ι.app (op A)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    have hU := congrArg (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
        (op ((uC i).obj X))).map)
      (colimitResolutionComplex_d D uC hu hobj hhom hhom_inj K hK F n)
    have hA := congrArg (((sheafSections (D.J A.left) (Ab.{max u v w})).obj
        (op ((D.u A.hom).obj X))).map) (systemResolutionComplex_d D F A.left n)
    exact (congrArg (fun z => (sectionsCocone D uC hu (resolutionSystem D F n)
          (systemKanExtension D uC hu (resolutionSystem D F n))
          (systemKanUnit D uC hu (resolutionSystem D F n))
          (systemKanUnit_compatible D uC hu (resolutionSystem D F n)) i X).ι.app (op A) ≫ z)
        hU).trans
      ((systemColimitMap_sections_fac D uC hu hobj hhom hhom_inj K hK
        (systemResolutionDifferential D F n) i X (op A)).trans
      (congrArg (fun z => z ≫ (sectionsCocone D uC hu (resolutionSystem D F (n + 1))
          (systemKanExtension D uC hu (resolutionSystem D F (n + 1)))
          (systemKanUnit D uC hu (resolutionSystem D F (n + 1)))
          (systemKanUnit_compatible D uC hu (resolutionSystem D F (n + 1))) i X).ι.app (op A))
        hA).symm)

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- The legs of the cocone of complexes of sections are compatible with the diagram. -/
private theorem resolutionSectionsLeg_naturality {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (resolutionSectionsDiagram D F i X).map f ≫
        resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X B.unop =
      resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X A.unop := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (sectionsCocone D uC hu (resolutionSystem D F n)
    (systemKanExtension D uC hu (resolutionSystem D F n))
    (systemKanUnit D uC hu (resolutionSystem D F n))
    (systemKanUnit_compatible D uC hu (resolutionSystem D F n)) i X).w f

/-- The cocone of the diagram of complexes of sections, at the complex of sections over `uᵢ(X)`
of the colimit of the resolution. -/
private def resolutionSectionsCocone : Cocone (resolutionSectionsDiagram D F i X) where
  pt := colimitResolutionSections D uC hu hobj hhom hhom_inj K hK F i X
  ι :=
    { app A := resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X A.unop
      naturality _A _B f :=
        (resolutionSectionsLeg_naturality D uC hu hobj hhom hhom_inj K hK F i X f).trans
          (Category.comp_id _).symm }

/-- In each degree the cocone of complexes of sections is the cocone of sections of that term of
the resolution, which is a colimit cocone by the case `p = 0`. -/
private def isColimit_resolutionSectionsCocone_eval (n : ℕ) :
    IsColimit ((HomologicalComplex.eval (Ab.{max u v w}) (ComplexShape.up ℕ) n).mapCocone
      (resolutionSectionsCocone D uC hu hobj hhom hhom_inj K hK F i X)) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (resolutionSectionsDiagram_evalIso D F i X n) _).symm
      (isColimit_sectionsCocone_of_pointwise D uC hu hhom hhom_inj (resolutionSystem D F n)
        (systemKanExtension D uC hu (resolutionSystem D F n))
        (systemKanUnit D uC hu (resolutionSystem D F n))
        (systemKanUnit_compatible D uC hu (resolutionSystem D F n))
        (systemKan_isPointwise D uC hu (resolutionSystem D F n)) i X))
    (Cocone.ext (Iso.refl _) (fun _A =>
      (Category.comp_id _).trans (Category.id_comp _)))

/-- **The cohomology of the colimit is the colimit of the cohomologies, on complexes.** The
degree-`p` homology of the diagram of complexes of sections is a colimit cocone, because homology
commutes with the exact colimits of `(Over i)ᵒᵖ`. -/
private def isColimit_resolutionSectionsHomologyCocone (p : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor (Ab.{max u v w})
        (ComplexShape.up ℕ) p).mapCocone
      (resolutionSectionsCocone D uC hu hobj hhom hhom_inj K hK F i X)) := by
  letI : PreservesFilteredColimitsOfSize.{v, max u v} (forget (Ab.{max u v w})) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  letI : HasExactColimitsOfShape (Over i)ᵒᵖ (Ab.{max u v w}) := ⟨inferInstance⟩
  exact isColimit_mapCocone_homologyFunctor _ _
    (isColimit_resolutionSectionsCocone_eval D uC hu hobj hhom hhom_inj K hK F i X) p

/-- The augmentation of the colimit resolution by the sheaf `𝒢` presenting the colimit. -/
private def presentationResolutionι
    (ePres : systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F ≅ 𝒢) :
    (CochainComplex.single₀ _).obj 𝒢 ⟶
      colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F :=
  (CochainComplex.single₀ _).map ePres.inv ≫
    colimitResolutionι D uC hu hobj hhom hhom_inj K hK F

/-- The augmentation of the colimit resolution by `𝒢` is a quasi-isomorphism. -/
private theorem presentationResolutionι_quasiIso :
    QuasiIso (presentationResolutionι D uC hu hobj hhom hhom_inj K hK F 𝒢 e) := by
  let : QuasiIso (colimitResolutionι D uC hu hobj hhom hhom_inj K hK F) :=
    colimitResolutionι_quasiIso D uC hu hobj hhom hhom_inj K hK F
  dsimp only [presentationResolutionι]
  infer_instance

include e in
/-- The comparison of the colimit resolution with a chosen injective resolution of `𝒢`. -/
private def presentationResolutionComparison :
    colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F ⟶
      (InjectiveResolution.of 𝒢).cocomplex :=
  liftOfQuasiIso _ (presentationResolutionι_quasiIso D uC hu hobj hhom hhom_inj K hK F 𝒢 e) _

/-- The comparison map is compatible with the two augmentations by `𝒢`. -/
private theorem presentationResolutionComparison_ι :
    presentationResolutionι D uC hu hobj hhom hhom_inj K hK F 𝒢 e ≫
        presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e =
      (InjectiveResolution.of 𝒢).ι :=
  liftOfQuasiIso_ι _ _ _

/-- The colimit resolution computes the cohomology of `𝒢`: the comparison with the chosen
injective resolution is an isomorphism on the homology of the complexes of sections. -/
private theorem isIso_homologyMap_presentationResolutionComparison (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
          (op ((uC i).obj X))).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e)) p) := by
  let := preservesFiniteLimits_sheafSections_obj K.toGrothendieck (op ((uC i).obj X))
  exact isIso_homologyMap_map_of_rightAcyclic _
    (presentationResolutionι D uC hu hobj hhom hhom_inj K hK F 𝒢 e)
    (presentationResolutionι_quasiIso D uC hu hobj hhom hhom_inj K hK F 𝒢 e)
    (fun n q hq => colimitResolutionObj_isZero_rightDerived D uC hu hobj hhom hhom_inj K hK F
      ((uC i).obj X) n q hq)
    _ _ (presentationResolutionComparison_ι D uC hu hobj hhom hhom_inj K hK F 𝒢 e) p

include e in
/-- The homology of the complex of sections of the colimit resolution is the cohomology of `𝒢`
over `uᵢ(X)`. -/
private noncomputable def colimitResolutionSectionsHomologyIso (p : ℕ) :
    (HomologicalComplex.homologyFunctor (Ab.{max u v w}) (ComplexShape.up ℕ) p).obj
        (colimitResolutionSections D uC hu hobj hhom hhom_inj K hK F i X) ≅
      (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
        (op ((uC i).obj X))).rightDerived p).obj 𝒢 := by
  letI := isIso_homologyMap_presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F
    𝒢 e i X p
  exact asIso (HomologicalComplex.homologyMap
      ((((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
          (op ((uC i).obj X))).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e)) p) ≪≫
    ((InjectiveResolution.of 𝒢).isoRightDerivedObj
      ((sheafSections K.toGrothendieck (Ab.{max u v w})).obj (op ((uC i).obj X))) p).symm

include e in
/-- The sections over `uᵢ(X)` of the comparison with the chosen injective resolution of `𝒢`. -/
private abbrev presentationComparisonSections :
    colimitResolutionSections D uC hu hobj hhom hhom_inj K hK F i X ⟶
      (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
        (op ((uC i).obj X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (InjectiveResolution.of 𝒢).cocomplex :=
  (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
      (op ((uC i).obj X))).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e)

/-- The structure maps of the colimits of the terms of the resolution, assembled into a map of
complexes from the resolution of `F_j` to the pushforward along `u_j` of the colimit resolution. -/
private def colimitStructureChainMap (j : D.I) :
    systemResolutionComplex D F j ⟶
      (((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
        K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F) where
  f n := ⟨systemKanUnit D uC hu (resolutionSystem D F n) j⟩
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    change _ ≫ ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
        K.toGrothendieck).map
          ((colimitResolutionComplex D uC hu hobj hhom hhom_inj K hK F).d n (n + 1)) = _
    rw [colimitResolutionComplex_d, systemResolutionComplex_d]
    exact Sheaf.hom_ext (systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK
      (systemResolutionDifferential D F n) j)

include e in
/-- The lift of the structure map `ι_j` to the resolutions: the colimit structure maps followed by
the comparison with the chosen injective resolution of `𝒢`. -/
private def legChainMap (j : D.I) :
    systemResolutionComplex D F j ⟶
      (((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
        K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (InjectiveResolution.of 𝒢).cocomplex :=
  colimitStructureChainMap D uC hu hobj hhom hhom_inj K hK F j ≫
    (((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
      K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e)

omit [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck] in
/-- The augmentation by `𝒢` of the colimit resolution, in degree zero. -/
private theorem presentationResolutionι_f_zero :
    (presentationResolutionι D uC hu hobj hhom hhom_inj K hK F 𝒢 e).f 0 =
      e.inv ≫ colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F 0 :=
  rfl

attribute [local instance_reducible] colimitResolutionComplex systemColimitSheaf

include he in
/-- The lift of `ι_j` to the resolutions is compatible with the augmentations. -/
private theorem legChainMap_ι (j : D.I) :
    ((systemResolutionι D F j).f 0).hom ≫
        ((legChainMap D uC hu hobj hhom hhom_inj K hK F 𝒢 e j).f 0).hom =
      ι j ≫ Functor.whiskerLeft (uC j).op ((InjectiveResolution.of 𝒢).ι.f 0).hom := by
  refine Sheaf.hom_ext_iff.mp (show (systemResolutionι D F j).f 0 ≫
      (legChainMap D uC hu hobj hhom hhom_inj K hK F 𝒢 e j).f 0 =
    (⟨ι j⟩ : F.obj j ⟶ ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
        K.toGrothendieck).obj 𝒢) ≫
      ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
        K.toGrothendieck).map ((InjectiveResolution.of 𝒢).ι.f 0) from ?_)
  have hJ : (InjectiveResolution.of 𝒢).ι.f 0 =
      (e.inv ≫ colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F 0) ≫
        (presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e).f 0 := by
    rw [← presentationResolutionComparison_ι D uC hu hobj hhom hhom_inj K hK F 𝒢 e,
      HomologicalComplex.comp_f, presentationResolutionι_f_zero]
  have hι : (⟨ι j⟩ : F.obj j ⟶ ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
      K.toGrothendieck).obj 𝒢) =
      (⟨systemKanUnit D uC hu F j⟩ : F.obj j ⟶ ((uC j).sheafPushforwardContinuous
        (Ab.{max u v w}) (D.J j) K.toGrothendieck).obj
          (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F)) ≫
        ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
          K.toGrothendieck).map e.hom :=
    (Sheaf.hom_ext (he j)).symm
  have hmono : (⟨systemKanUnit D uC hu F j⟩ : F.obj j ⟶
        ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j) K.toGrothendieck).obj
          (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F)) ≫
        ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j) K.toGrothendieck).map
          (colimitResolutionMono D uC hu hobj hhom hhom_inj K hK F 0) =
      (injectiveSystemι D F).app j ≫
        ⟨systemKanUnit D uC hu (resolutionSystem D F 0) j⟩ :=
    Sheaf.hom_ext (systemColimitMap_fac D uC hu hobj hhom hhom_inj K hK
      (injectiveSystemι D F) j)
  have hcancel : ∀ {Z : Sheaf (D.J j) (Ab.{max u v w})}
      (f : ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j) K.toGrothendieck).obj
        (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) ⟶ Z),
      ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j) K.toGrothendieck).map e.hom ≫
          ((uC j).sheafPushforwardContinuous (Ab.{max u v w}) (D.J j)
            K.toGrothendieck).map e.inv ≫ f =
        f := by
    intro Z f
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hJ, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hι]
  simp only [Category.assoc]
  rw [hcancel, ← Category.assoc, hmono, systemResolutionι_f_zero, Category.assoc]
  rfl

include e he in
/-- The presentation of the cohomology diagram and cocone computed by the pointwise injective
resolution of the system: the diagram of the homologies of the complexes of sections, with the
cocone at the cohomology of `𝒢` over `uᵢ(X)`. -/
private def resolutionCohomologyCocone (p : ℕ) :
    CohomologyCocone.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι i X p where
  diagram := resolutionSectionsDiagram D F i X ⋙
    HomologicalComplex.homologyFunctor (Ab.{max u v w}) (ComplexShape.up ℕ) p
  objIso A := ((systemInjectiveResolution D F A.left).isoRightDerivedObj
    ((sheafSections (D.J A.left) (Ab.{max u v w})).obj (op ((D.u A.hom).obj X))) p).symm
  map_eq {A B} f :=
    isCohomologyMap_of_sectionsMapTo.{max u v w, w} (D.u f.left)
      (transition.{v, u, max u v w, max u v w} D F f.left)
      (systemInjectiveResolution D F B.left) (systemInjectiveResolution D F A.left)
      (fun n => transition.{v, u, max u v w, max u v w} D (resolutionSystem D F n) f.left)
      (fun n n' hn => by
        obtain rfl : n + 1 = n' := hn
        have hB : ((systemInjectiveResolution D F B.left).cocomplex.d n (n + 1)).hom =
            ((systemResolutionDifferential D F n).app B.left).hom :=
          congrArg (fun q => q.hom) (systemResolutionComplex_d D F B.left n)
        have hA : ((systemInjectiveResolution D F A.left).cocomplex.d n (n + 1)).hom =
            ((systemResolutionDifferential D F n).app A.left).hom :=
          congrArg (fun q => q.hom) (systemResolutionComplex_d D F A.left n)
        rw [hB, hA]
        exact hom_comp_transition D (systemResolutionDifferential D F n) f.left)
      (hom_comp_transition D (injectiveSystemι D F) f.left)
      ((D.u B.hom).obj X) ((D.u A.hom).obj X) (uObj_eq D f X).symm p
      ((resolutionSectionsDiagram D F i X).map f.op) (fun _ => rfl) rfl
  leg :=
    { app A := HomologicalComplex.homologyMap
        (resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X A.unop ≫
          presentationComparisonSections D uC hu hobj hhom hhom_inj K hK F 𝒢 e i X) p ≫
        ((InjectiveResolution.of 𝒢).isoRightDerivedObj
          ((sheafSections K.toGrothendieck (Ab.{max u v w})).obj (op ((uC i).obj X))) p).inv
      naturality A B f := by
        have hn : (resolutionSectionsDiagram D F i X).map f ≫
            (resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X B.unop ≫
              presentationComparisonSections D uC hu hobj hhom hhom_inj K hK F 𝒢 e i X) =
            resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X A.unop ≫
              presentationComparisonSections D uC hu hobj hhom hhom_inj K hK F 𝒢 e i X := by
          rw [← Category.assoc,
            resolutionSectionsLeg_naturality D uC hu hobj hhom hhom_inj K hK F i X f]
        simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map,
          Functor.const_obj_map, ← Category.assoc,
          ← HomologicalComplex.homologyMap_comp, hn]
        exact (Category.comp_id _).symm }
  leg_eq A := by
    refine isCohomologyMap_of_sectionsMapTo.{max u v w, w} (uC A.left) (ι A.left)
      (systemInjectiveResolution D F A.left) (InjectiveResolution.of 𝒢)
      (fun n => ((legChainMap D uC hu hobj hhom hhom_inj K hK F 𝒢 e A.left).f n).hom)
      (fun n n' _ => by
        have h := congrArg (fun q => q.hom)
          ((legChainMap D uC hu hobj hhom hhom_inj K hK F 𝒢 e A.left).comm n n')
        exact h.symm)
      (legChainMap_ι D uC hu hobj hhom hhom_inj K hK F 𝒢 ι e he A.left)
      ((D.u A.hom).obj X) ((uC i).obj X) (uLeg_eq D uC hu A X).symm p
      (resolutionSectionsLeg D uC hu hobj hhom hhom_inj K hK F i X A ≫
        presentationComparisonSections D uC hu hobj hhom hhom_inj K hK F 𝒢 e i X)
      (fun n => by
        have h := sectionsMapTo_naturality.{max u v w, w} (uC A.left)
          (systemKanUnit D uC hu (resolutionSystem D F n) A.left)
          ((legChainMap D uC hu hobj hhom hhom_inj K hK F 𝒢 e A.left).f n).hom
          (𝟙 ((resolutionSystem D F n).obj A.left).obj)
          ((presentationResolutionComparison D uC hu hobj hhom hhom_inj K hK F 𝒢 e).f n).hom
          (Category.id_comp _) ((D.u A.hom).obj X) ((uC i).obj X)
          (uLeg_eq D uC hu A X).symm
        exact h.symm.trans (Category.id_comp _)) ?_
    simp only [Iso.symm_inv, Category.assoc]
    rfl

include hobj hhom hhom_inj hK e he in
/-- **Tag 09YP for an arbitrary `p`.** The canonical cocone of the cohomology diagram over the
arrows `a : j ⟶ i` is a colimit cocone, for any presentation of that diagram: the degree-`p`
homology of the diagram of complexes of sections of the pointwise injective resolution is. -/
private theorem nonempty_isColimitCohomologyCoconeOfResolution (p : ℕ)
    (hf : ∀ j, (uC j).IsMorphismOfSites (D.J j) K.toGrothendieck)
    (E : CohomologyCocone.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι i X p) :
    Nonempty (IsColimit E.cocone) := by
  refine ⟨isColimitCohomologyCoconeEquiv hf
    (resolutionCohomologyCocone D uC hu hobj hhom hhom_inj K hK F 𝒢 ι e he i X p) E ?_⟩
  refine IsColimit.ofIsoColimit
    (isColimit_resolutionSectionsHomologyCocone D uC hu hobj hhom hhom_inj K hK F i X p)
    (Cocone.ext (colimitResolutionSectionsHomologyIso D uC hu hobj hhom hhom_inj K hK F 𝒢 e i X p)
      (fun A => ?_))
  dsimp only [CohomologyCocone.cocone, resolutionCohomologyCocone,
    colimitResolutionSectionsHomologyIso, Iso.trans_hom, asIso_hom, Iso.symm_hom]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

end ColimitResolution

/-! ### Tag 09YP -/

section Tag09YP

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (hcolim : IsColimitPresentation.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι)
  (i : D.I) (X : D.C i) (p : ℕ)

include hobj hhom hhom_inj hK in
open CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites in
/-- Each functor to the colimit site defines a morphism of sites (Stacks 0A35). The witness is
a proposition, so it is extracted from the existential statement of Stacks 0A35 directly. -/
private theorem isMorphismOfSites_colimitSite :
    ∀ j, (uC j).IsMorphismOfSites (D.J j) K.toGrothendieck :=
  (exists_isMorphismOfSites_sections_pullback_of_colimit
      D uC hu hobj hhom hhom_inj K hK).elim fun hf _ => hf

include hobj hhom hhom_inj hK hcolim in
/-- **Stacks 09YP, the canonical cohomology diagram and its cocone.** In the situation of
Stacks 0EXZ, with the functors `uC i` exhibiting `C` as the colimit of the sites of the system
(Stacks 09YL and 0A35) and with `𝒢 = colim fᵢ⁻¹Fᵢ`, the cohomology groups `Hᵖ(u_a(X), F_j)`
over the arrows `a : j ⟶ i` form a diagram whose arrows are the canonical cohomology maps,
together with the canonical cocone at `Hᵖ(uᵢ(X), 𝒢)`. -/
@[stacks 09YP "weak-system variant (Stacks 00VH finite coverings): canonical cohomology diagram \
  and cocone", no_expose]
public def cohomologyCocone : CohomologyCocone.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι i X p :=
  letI hf := isMorphismOfSites_colimitSite D uC hu hobj hhom hhom_inj K hK
  letI _htrans : ∀ {j k : D.I} (a : j ⟶ k),
      (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, max u v w, max u v w}
        D a).PreservesInjectiveObjects :=
    fun a => restriction_preservesInjectiveObjects (D.u a) (D.isMorphismOfSites a)
  letI _hcont : ∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck :=
    fun j => (hf j).isContinuous
  letI _hleg : ∀ j, ((uC j).sheafPushforwardContinuous (Ab.{max u v w})
      (D.J j) K.toGrothendieck).PreservesInjectiveObjects :=
    fun j => restriction_preservesInjectiveObjects (uC j) (hf j)
  canonicalCohomologyCocone D F uC hu K 𝒢 ι hcolim.1 i X p

include hobj hhom hhom_inj hK hcolim in
/-- **Tag 09YP in degree zero.** The canonical cocone of the diagram of degree-zero cohomology
groups is a colimit cocone; this is the sections statement of Stacks 09YN. -/
private theorem nonempty_isColimitCohomologyCoconeZero
    (E : CohomologyCocone.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι i X 0) :
    Nonempty (IsColimit E.cocone) := by
  let hf := isMorphismOfSites_colimitSite D uC hu hobj hhom hhom_inj K hK
  let htrans : ∀ {j k : D.I} (a : j ⟶ k),
      (InverseSystemOfFiniteSites.abelianSheafPushforward.{v, u, max u v w, max u v w}
        D a).PreservesInjectiveObjects :=
    fun a => restriction_preservesInjectiveObjects (D.u a) (D.isMorphismOfSites a)
  let hcont : ∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck :=
    fun j => (hf j).isContinuous
  let hleg : ∀ j, ((uC j).sheafPushforwardContinuous (Ab.{max u v w})
      (D.J j) K.toGrothendieck).PreservesInjectiveObjects :=
    fun j => restriction_preservesInjectiveObjects (uC j) (hf j)
  let E' := canonicalCohomologyCocone D F uC hu K 𝒢 ι hcolim.1 i X 0
  apply Nonempty.map (isColimitCohomologyCoconeEquiv hf E' E)
  let := preservesFiniteLimits_sheafSections_obj K.toGrothendieck (op ((uC i).obj X))
  let e := sectionsCohomologyDiagramZeroIso D F i X
  let ec : (Cocone.precompose e.hom).obj E'.cocone ≅
      sectionsCocone D uC hu F 𝒢.obj ι hcolim.1 i X :=
    Cocone.ext (asIso (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
      (op ((uC i).obj X))).toRightDerivedZero.app 𝒢)).symm (fun A => by
        change (_ ≫ cohomologyMapTo _ _ _ _ _ 0) ≫ _ = _
        exact (Iso.comp_inv_eq (asIso (((sheafSections K.toGrothendieck (Ab.{max u v w})).obj
          (op ((uC i).obj X))).toRightDerivedZero.app 𝒢))).mpr
            (cohomologyMapTo_zero_comm (uC A.unop.left) (ι A.unop.left)
              ((D.u A.unop.hom).obj X) ((uC i).obj X) (uLeg_eq D uC hu A.unop X).symm))
  exact ⟨(IsColimit.equivOfNatIsoOfIso e.symm _ _ ec).symm
    (isColimit_sectionsCocone_of_presentation D uC hu hobj hhom hhom_inj K hK F 𝒢 ι hcolim i X)⟩

include hobj hhom hhom_inj hK hcolim in
/-- **Tag 09YP for an arbitrary `p`, with no hypothesis on the system.** For any sheaf `𝒢`
presenting the colimit of the system, the canonical cocone of the cohomology diagram over the
arrows `a : j ⟶ i` is a colimit cocone: identifying `𝒢` with the colimit sheaf of the system
reduces the statement to the resolution presentation. -/
private theorem nonempty_isColimitCohomologyCoconeOfPresentation
    (E : CohomologyCocone.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι i X p) :
    Nonempty (IsColimit E.cocone) := by
  let hf := isMorphismOfSites_colimitSite D uC hu hobj hhom hhom_inj K hK
  let : ∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck := fun j => (hf j).isContinuous
  obtain ⟨g, hg⟩ := colimitPresentation_uniqueIso D uC hu K F
    (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) 𝒢 (systemKanUnit D uC hu F) ι
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F) hcolim
  exact nonempty_isColimitCohomologyCoconeOfResolution D uC hu hobj hhom hhom_inj K hK F 𝒢 ι
    g hg i X p hf E


include hobj hhom hhom_inj hK hcolim in
/-- **Tag 09YP.** The canonical cocone of the cohomology diagram over the arrows `a : j ⟶ i` is
a colimit cocone: the degree-zero case is Stacks 09YN, and the positive degrees split into the
pointwise injective case and the general one. -/
private alias nonempty_isColimitCohomologyCocone := nonempty_isColimitCohomologyCoconeOfPresentation

include hobj hhom hhom_inj hK hcolim in
/-- **Stacks 09YP.** In the situation of Stacks 0EXZ, set `𝒢 = colim fᵢ⁻¹Fᵢ`. For every index
`i`, every object `X` of the site at `i` and every `p`, the cohomology `Hᵖ(uᵢ(X), 𝒢)` is the
filtered colimit, over the arrows `a : j ⟶ i`, of the cohomology groups `Hᵖ(u_a(X), F_j)`: the
canonical cocone is a colimit cocone. The case `p = 0` is Stacks 09YN.

The colimit structure is a choice; it is unique, `CategoryTheory.Limits.IsColimit` being a
subsingleton. -/
@[stacks 09YP "weak-system variant (Stacks 00VH finite coverings): the canonical cocone is a \
  colimit cocone", no_expose]
public def isColimitCohomologyCocone
    (E : CohomologyCocone.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι i X p :=
      cohomologyCocone.{v, u, w} D uC hu hobj hhom hhom_inj K hK F 𝒢 ι hcolim
        i X p) :
    IsColimit E.cocone :=
  (nonempty_isColimitCohomologyCocone D uC hu hobj hhom hhom_inj K hK F 𝒢 ι hcolim i X p E).some

end Tag09YP

end Stacks.WeakSites.ColimitSiteCohomology

end

/-! ### Supplementary declarations -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous
universe v u w t s
namespace Stacks.WeakSites.ColimitSiteCohomology
attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive

/-- **The transition maps of a system of abelian sheaves compose, read on elements.** The
transition of `b ≫ a` is the transition of `a` followed by that of `b`, up to the transport along
the equality of functors `u_{b ≫ a} = u_a ⋙ u_b`. This is `transition_comp_eqToHom` with the
natural transformations evaluated at an object and applied to a section; it is the hypothesis
`hψ` of `Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit` for
the transitions of an abelian system. -/
public theorem transition_comp_apply
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
    {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i)
    (x : (F.obj i).obj.obj (op V)) :
    (transition D F (b ≫ a)).app (op V) x =
      (F.obj k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
        ((transition D F b).app (op ((D.u a).obj V))
          ((transition D F a).app (op V) x)) := by
  rw [transition_comp_eqToHom D F b a]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerLeft_app,
    eqToHom_app, eqToHom_map]
  rfl

end Stacks.WeakSites.ColimitSiteCohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous
universe v u w t s
namespace Stacks.WeakSites.ColimitSiteCohomology
attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive
section
open InverseSystemOfFiniteSites
attribute [local instance] systemPushforward_additive
/-- **A system of abelian sheaves from transition maps written in the direct-image
direction.** A sheaf on each level together with maps `F_j ⟶ f_{a,*} F_i` that take the identity
transition to the canonical identification and a composite transition to the composite — the
adjoint form of the data of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem` — determines
such a system, the two cocycle conditions of the structure being the transposes of the two
hypotheses here.

This is the shape in which a system is produced in practice: the direct images are restriction
functors along the transition functors of the system of sites, so a comparison of successive
direct images with the direct image along a composite transition is available concretely,
whereas the inverse images are only characterised as left adjoints. -/
public def _root_.InverseSystemOfFiniteSites.systemOfPushforwardMaps
    (D : InverseSystemOfFiniteSites.{v, u, w})
    (F : ∀ i, Sheaf (D.J i) (Ab.{max u v w t}))
    (φ : ∀ {i j} (a : i ⟶ j), F j ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (F i))
    (hid : ∀ i, φ (𝟙 i) = (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app (F i))
    (hcomp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k), φ (a ≫ b) = φ b ≫
      (abelianSheafPushforward.{v, u, w, t} D b).map (φ a) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i)) :
    AbelianSheafSystem.{v, u, w, t} D where
  obj := F
  map a := (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ |>.symm <| φ a
  map_id i := by
    have hh : (abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv (F i) (F i)
        ((abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app (F i)) = φ (𝟙 i) := by
      rw [hid]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
    rw [← hh]
    simpa only [Equiv.symm_apply_apply, Functor.id_obj] using
      (abelianSheafPullbackIdIso.{v, u, w, t} D i).inv_hom_id_app (F i)
  map_comp {i j k} a b := by
    apply (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)).homEquiv _ _ |>.injective
    dsimp only [abelianSheafPullbackCompIso]
    rw [homEquiv_leftAdjointUniq_inv_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    change ((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _)
      (((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _)
        ((abelianSheafPullback.{v, u, w, t} D a).map
          (((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _).symm (φ b)) ≫
          ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _).symm (φ a))) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i) = _
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (hcomp a b).symm

end
end Stacks.WeakSites.ColimitSiteCohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous
universe v u w t s
namespace Stacks.WeakSites.ColimitSiteCohomology
attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive
attribute [local instance_reducible] InverseSystemOfFiniteSites.systemOfPushforwardMaps
  systemCokernel systemSyzygy

/-- **A compatible family of maps out of a system of abelian sheaves, read on elements.** The map
at the level `j` is the transition of `a : k ⟶ j` followed by the map at the level `k`, transported
along the equality of objects `u_k(u_a(V)) = u_j(V)`. This is the hypothesis `hι` of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit` for the legs of
an abelian colimit presentation. -/
public theorem IsCompatible.app_apply (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w}
    [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D) (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    {g : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ H}
    (hg : IsCompatible.{v, u, w, t} D uC hu F H g) {j k : D.I} (a : k ⟶ j) (V : D.C j)
    (x : (F.obj j).obj.obj (op V)) :
    (g j).app (op V) x =
      H.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
        ((g k).app (op ((D.u a).obj V)) ((transition D F a).app (op V) x)) := by
  conv_lhs => rw [hg a]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerLeft_app,
    eqToHom_app, eqToHom_map]
  rfl

/-! ### The cohomology diagram over the arrows into a fixed index -/


end Stacks.WeakSites.ColimitSiteCohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous
universe v u w t s
namespace Stacks.WeakSites.ColimitSiteCohomology
attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive
attribute [local instance_reducible] InverseSystemOfFiniteSites.systemOfPushforwardMaps
  systemCokernel systemSyzygy
section
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
attribute [local instance_reducible] systemColimitSheaf

/-- The map of the diagram of sections over `u_a(X)` of an abelian system, written on elements:
the transition map followed by the transport along the equality of objects
`u_{f.left}(u_{B.hom}(X)) = u_{A.hom}(X)`. -/
private theorem sectionsDiagram_map_apply (i : D.I) (X : D.C i) {A B : (Over i)ᵒᵖ} (q : A ⟶ B)
    (y : (sectionsDiagram D F i X).obj A) :
    (sectionsDiagram D F i X).map q y =
      (F.obj B.unop.left).obj.map (eqToHom (congrArg op (uObj_eq D q.unop X).symm))
        ((transition D F q.unop.left).app (op ((D.u A.unop.hom).obj X)) y) := rfl


end
end Stacks.WeakSites.ColimitSiteCohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous
universe v u w t s
namespace Stacks.WeakSites.ColimitSiteCohomology
attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive
attribute [local instance_reducible] InverseSystemOfFiniteSites.systemOfPushforwardMaps
  systemCokernel systemSyzygy
section
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
attribute [local instance_reducible] systemColimitSheaf

/-- Functoriality of the diagram of sections over `u_a(X)`, written on elements. Stated with the
element a bound variable of the diagram's own value type, so that it can be applied to an element
whose type is only definitionally that. -/
private theorem sectionsDiagram_map_comp_apply (i : D.I) (X : D.C i) {A B E : (Over i)ᵒᵖ}
    (q : A ⟶ B) (r : B ⟶ E) (y : (sectionsDiagram D F i X).obj A) :
    (sectionsDiagram D F i X).map (q ≫ r) y =
      (sectionsDiagram D F i X).map r ((sectionsDiagram D F i X).map q y) := by
  rw [Functor.map_comp]
  rfl

end
end Stacks.WeakSites.ColimitSiteCohomology
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous
universe v u w t s
namespace Stacks.WeakSites.ColimitSiteCohomology
attribute [local instance] hasSheafifyAb
attribute [local instance] enoughInjectivesAbInstance
attribute [local instance] sections_additive
attribute [local instance_reducible] InverseSystemOfFiniteSites.systemOfPushforwardMaps
  systemCokernel systemSyzygy
section
variable (D : InverseSystemOfFiniteSites.{v, u, w}) {C : Type w} [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)
attribute [local instance_reducible] systemColimitSheaf
include hobj hhom hhom_inj hK in
/-- **Stacks 09YN for systems of abelian sheaves, read on elements.** Let the functors `uC i`
exhibit `C` as the colimit of the sites of the system, let `K` be the coverings of Stacks 09YL and
let `G = colim f_i^{-1}F_i` be presented by `ι` (`IsColimitPresentation`). Then, over every object
`u_i(X)` of the colimit site:

* every section of `G` over `u_i(X)` is the image under some leg `ι j` of a section of `F j` over
  `u_a(X)`, for some arrow `a : j ⟶ i`; and
* two sections of `F j` over `u_a(X)` with the same image under `ι j` are identified by the
  transition map of some further arrow `b : k ⟶ j`.

These are the two clauses of
`Stacks.WeakSites.ColimitGlobalSections.objectSections_jointlySurjective_and_separated`, which are
the object-level input of the degree-zero Cech step of Stacks 09YQ, for a system of **abelian**
sheaves rather than of sheaves of sets. They are not the forgetful image of that statement: the
forgetful functor `Sheaf K Ab ⥤ Sheaf K (Type _)` is a right adjoint, so an abelian colimit
presentation has no reason to remain a colimit presentation after it, and the universal property
of `IsColimitPresentation` quantifies only over abelian sheaves. What is used instead is that the
*object-level* conclusion of Stacks 09YN is a filtered colimit of abelian groups
(`isColimit_sectionsCocone_of_presentation`), and a filtered colimit of abelian groups is computed
on underlying sets, so its elements and its identifications are detected at a stage
(`CategoryTheory.Limits.Concrete.isColimit_exists_rep`,
`CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq`). Nothing is asked of sheafification.

The index category of that colimit is `(Over i)ᵒᵖ`, filtered because `D.I` is cofiltered
(`CategoryTheory.IsCofiltered.over`); the two arrows `Concrete.isColimit_exists_of_rep_eq` returns
are coequalized by `CategoryTheory.IsFiltered.coeqHom`, which is what turns them into the single
arrow `b` of the second clause. -/
public theorem abelianSections_jointlySurjective_and_separated
    (G : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G.obj)
    (hG : IsColimitPresentation D uC hu K F G ι) :
    (∀ (i : D.I) (X : D.C i) (s : G.obj.obj (op ((uC i).obj X))),
        ∃ (j : D.I) (a : j ⟶ i) (t : (F.obj j).obj.obj (op ((D.u a).obj X))),
          G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))
              ((ι j).app (op ((D.u a).obj X)) t) = s) ∧
      ∀ (i : D.I) (X : D.C i) (j : D.I) (a : j ⟶ i)
          (t t' : (F.obj j).obj.obj (op ((D.u a).obj X))),
        (ι j).app (op ((D.u a).obj X)) t = (ι j).app (op ((D.u a).obj X)) t' →
          ∃ (k : D.I) (b : k ⟶ j),
            (transition D F b).app (op ((D.u a).obj X)) t =
              (transition D F b).app (op ((D.u a).obj X)) t' := by
  classical
  have hforget : PreservesFilteredColimitsOfSize.{v, max u v}
      (forget (Ab.{max u v w t})) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w t, max u v w t} _
  refine ⟨fun i X s => ?_, fun i X j a t t' h => ?_⟩
  · obtain ⟨A, y, hy⟩ := Concrete.isColimit_exists_rep (sectionsDiagram D F i X)
      (isColimit_sectionsCocone_of_presentation D uC hu hobj hhom hhom_inj K hK F G ι hG i X) s
    exact ⟨A.unop.left, A.unop.hom, y, hy⟩
  · have hcol := isColimit_sectionsCocone_of_presentation D uC hu hobj hhom hhom_inj K hK F G ι
      hG i X
    have hA : (sectionsCocone D uC hu F G.obj ι hG.1 i X).ι.app (op (Over.mk a)) t =
        (sectionsCocone D uC hu F G.obj ι hG.1 i X).ι.app (op (Over.mk a)) t' :=
      congrArg (G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))) h
    obtain ⟨B, f, g, hfg⟩ :=
      Concrete.isColimit_exists_of_rep_eq (sectionsDiagram D F i X)
        (i := op (Over.mk a)) (j := op (Over.mk a)) hcol t t' hA
    have hcoeq := IsFiltered.coeq_condition f g
    have key : (sectionsDiagram D F i X).map (g ≫ IsFiltered.coeqHom f g) t =
        (sectionsDiagram D F i X).map (g ≫ IsFiltered.coeqHom f g) t' :=
      (congrArg (fun q : op (Over.mk a) ⟶ IsFiltered.coeq f g =>
          (sectionsDiagram D F i X).map q t) hcoeq).symm.trans
        ((sectionsDiagram_map_comp_apply D F i X f (IsFiltered.coeqHom f g) t).trans
          ((congrArg ((sectionsDiagram D F i X).map (IsFiltered.coeqHom f g)) hfg).trans
            (sectionsDiagram_map_comp_apply D F i X g (IsFiltered.coeqHom f g) t').symm))
    refine ⟨(IsFiltered.coeq f g).unop.left, (g ≫ IsFiltered.coeqHom f g).unop.left, ?_⟩
    have e1 := sectionsDiagram_map_apply D F i X (g ≫ IsFiltered.coeqHom f g) t
    have e2 := sectionsDiagram_map_apply D F i X (g ≫ IsFiltered.coeqHom f g) t'
    exact (ConcreteCategory.bijective_of_isIso
      ((F.obj (IsFiltered.coeq f g).unop.left).obj.map
        (eqToHom (congrArg op
          (uObj_eq D (g ≫ IsFiltered.coeqHom f g).unop X).symm)))).injective
      (e1.symm.trans (key.trans e2))

end
end Stacks.WeakSites.ColimitSiteCohomology
end
