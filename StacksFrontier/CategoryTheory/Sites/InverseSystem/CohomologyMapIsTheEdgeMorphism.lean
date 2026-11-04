module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeCalculus
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact

/-!
# The canonical cohomology map of a morphism of sites is the Leray edge morphism

`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean` pins the
canonical map on cohomology determined by a continuous functor `G` of small sites and a map of
abelian sheaves `φ : P ⟶ G_* Q` by the predicate
`Stacks.WeakSites.ColimitSiteCohomology.IsCohomologyMap`: a map `m` satisfies it when it is
computed by *some* lift of `φ` to injective resolutions. That predicate is what the cohomology
diagram of Stacks 09YP is characterised by — the field `map_eq` of
`Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone`.

This file identifies that map with the Leray edge morphism of
`StacksFrontier/Algebra/Homology/RightDerivedEdge.lean`:

`m = Rᵖ Γ_V(φ) ≫ edge(G_*, Γ_V)_Q`.

Both sides are built from lifts to injective resolutions, so the identification is the uniqueness
of such a lift up to homotopy. What it buys is the *calculus* of
`StacksFrontier/Algebra/Homology/RightDerivedEdgeCalculus.lean`: the diagram of Stacks 09YP is now
expressed in a notation that composes, that is natural in the sections functor and in the
direct-image functor, and that is invertible when the direct image is exact. None of those four
laws is available for `IsCohomologyMap`, whose only general property in this development is
uniqueness.

The restriction along a continuous functor is evaluation at the image object
(`Stacks.Cohomology.BiggerSiteGlobal.sheafSections_comp_sheafPushforwardContinuous`, an equality
of functors), which is why the target of the edge morphism is literally the right derived sections
over `G V` and no transport is needed.

## Main results

* `Stacks.WeakSites.ColimitSiteCohomology.IsCohomologyMap.eq_map_comp_edge_app` — **the canonical
  cohomology map of `(G, φ)` over `V` is the map induced by `φ` on the right derived sections over
  `V`, followed by the edge morphism of the pair `(G_*, Γ_V)` at `Q`.**

## Implementation notes

The hypotheses that the big file supplies by `local instance` — sheafification of abelian sheaves
on a small site at an enlarged coefficient universe, and hence enough injectives — are taken here
as instance arguments rather than re-derived, so that nothing is restated.

The two comparisons of resolutions are produced by
`Stacks.Cohomology.SpectralLimit.descToComplex` and `CategoryTheory.InjectiveResolution.desc`,
and identified by `Stacks.Cohomology.RightDerivedEdge.homologyMap_map_eq_of_aug`: they agree on
the augmentation, which is exactly the degree-zero clause of `IsCohomologyMap`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 09YP](https://stacks.math.columbia.edu/tag/09YP)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.RightDerivedEdge

attribute [local instance_reducible] HomologicalComplex.single HomologicalComplex.homologyFunctor
  CategoryTheory.Functor.sheafPushforwardContinuous

universe w s

namespace Stacks.WeakSites.ColimitSiteCohomology

attribute [local instance] hasSheafifyAb enoughInjectivesAbInstance sections_additive
  systemPushforward_additive

variable {A B : Type w} [SmallCategory A] [SmallCategory B]
  {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} (G : A ⥤ B)
  [G.IsContinuous JA JB]
  [HasSheafify JA (Ab.{max w s})] [HasSheafify JB (Ab.{max w s})]
  [HasInjectiveResolutions (Sheaf JA (Ab.{max w s}))]
  [HasInjectiveResolutions (Sheaf JB (Ab.{max w s}))]
  [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects]

omit [HasSheafify JA (Ab.{max w s})] [HasSheafify JB (Ab.{max w s})]
  [HasInjectiveResolutions (Sheaf JA (Ab.{max w s}))]
  [HasInjectiveResolutions (Sheaf JB (Ab.{max w s}))]
  [(G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).PreservesInjectiveObjects] in
/-- A degreewise family of maps of presheaves into the restriction along `G`, compatible with the
differentials, as a map of cochain complexes of abelian sheaves into the restriction of the target
complex: the datum `IsCohomologyMap` is phrased with, as the morphism of complexes that
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` consumes. -/
private def componentsCochainMap
    (I : CochainComplex (Sheaf JA (Ab.{max w s})) ℕ)
    (J : CochainComplex (Sheaf JB (Ab.{max w s})) ℕ)
    (ψ : ∀ n : ℕ, (I.X n).obj ⟶ G.op ⋙ (J.X n).obj)
    (hψ : ∀ n n' : ℕ, (ComplexShape.up ℕ).Rel n n' →
      (I.d n n').hom ≫ ψ n' = ψ n ≫ Functor.whiskerLeft G.op (J.d n n').hom) :
    I ⟶ ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J where
  f n := ⟨ψ n⟩
  comm' n n' h := Sheaf.hom_ext (hψ n n' h).symm

/-- **The canonical cohomology map of a morphism of sites is the Leray edge morphism.** If `m` is
the canonical map on cohomology over `V` determined by the continuous functor `G` and the map of
abelian sheaves `φ : P ⟶ G_* Q`, then

`m = Rᵖ Γ_V(φ) ≫ edge(G_*, Γ_V)_Q`.

Both sides are computed from a lift of `φ` to injective resolutions, and any two such lifts are
homotopic; the comparison used on the right is produced from the augmentations by
`Stacks.Cohomology.SpectralLimit.descToComplex` and `CategoryTheory.InjectiveResolution.desc`. -/
theorem IsCohomologyMap.eq_map_comp_edge_app
    {P : Sheaf JA (Ab.{max w s})} {Q : Sheaf JB (Ab.{max w s})}
    (φ : P ⟶ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q) (V : A) (p : ℕ)
    {m : ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).obj P) ⟶
      ((((sheafSections JB (Ab.{max w s})).obj (op (G.obj V))).rightDerived p).obj Q)}
    (hm : IsCohomologyMap JA JB G φ.hom V p m) :
    m = ((((sheafSections JA (Ab.{max w s})).obj (op V)).rightDerived p).map φ) ≫
      (edge (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB)
        ((sheafSections JA (Ab.{max w s})).obj (op V)) p).app Q := by
  obtain ⟨IP, IQ, ψ, hψ, h0, rfl⟩ := hm
  have hinj : ∀ n, Injective ((((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj IQ.cocomplex).X n) :=
    injective_mapHomologicalComplex_obj
      (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB) _ IQ.injective
  have hξ : (injectiveResolution ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)).ι.f
        0 ≫
      (Stacks.Cohomology.SpectralLimit.descToComplex
        (injectiveResolution ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)) _ hinj
        ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (IQ.ι.f 0))
        (map_ι_f_zero_comp_d (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB) IQ)).f 0 =
      (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (IQ.ι.f 0) :=
    Stacks.Cohomology.SpectralLimit.ι_comp_descToComplex _ _ _ _ _
  have hcc : IP.ι.f 0 ≫ (InjectiveResolution.desc φ
        (injectiveResolution ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q))
        IP).f 0 =
      φ ≫ (injectiveResolution
        ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)).ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  have haug : IP.ι.f 0 ≫
      (componentsCochainMap G IP.cocomplex IQ.cocomplex ψ hψ).f 0 =
        φ ≫ (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (IQ.ι.f 0) :=
    Sheaf.hom_ext h0
  have hsec : sectionsComplexMap G IP.cocomplex IQ.cocomplex ψ hψ V =
      (((sheafSections JA (Ab.{max w s})).obj (op V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (componentsCochainMap G IP.cocomplex IQ.cocomplex ψ hψ) :=
    HomologicalComplex.hom_ext _ _ fun _ => rfl
  have key : HomologicalComplex.homologyMap
        (sectionsComplexMap G IP.cocomplex IQ.cocomplex ψ hψ V) p =
      HomologicalComplex.homologyMap
        ((((sheafSections JA (Ab.{max w s})).obj (op V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc φ (injectiveResolution
              ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)) IP ≫
            Stacks.Cohomology.SpectralLimit.descToComplex
              (injectiveResolution
                ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)) _ hinj
              ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).map (IQ.ι.f 0))
              (map_ι_f_zero_comp_d
                (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB) IQ))) p := by
    rw [hsec]
    refine homologyMap_map_eq_of_aug ((sheafSections JA (Ab.{max w s})).obj (op V)) IP hinj _ _
      ?_ p
    rw [haug]
    exact (comp_comp_eq_assoc _ _ _ φ _ _ hcc hξ).symm
  rw [key, Functor.map_comp, HomologicalComplex.homologyMap_comp,
    edge_app_eq (G.sheafPushforwardContinuous (Ab.{max w s}) JA JB)
      ((sheafSections JA (Ab.{max w s})).obj (op V)) p IQ
      (injectiveResolution ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)) _ hξ,
    InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc φ IP
      (injectiveResolution ((G.sheafPushforwardContinuous (Ab.{max w s}) JA JB).obj Q)) _ hcc
      ((sheafSections JA (Ab.{max w s})).obj (op V)) p]
  simp only [Category.assoc, HomologicalComplex.homologyFunctor_map]
  rfl

/-! ### The transition maps of a system assembled from direct images -/

section System

open InverseSystemOfFiniteSites

universe v u t

/-- The direct image along a transition morphism of a system of finite sites preserves injective
abelian sheaves, in the form instance search consumes. This is
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.injective_abelianSheafPushforward`,
Stacks 0730 for abelian sheaves. -/
theorem preservesInjectiveObjects_abelianSheafPushforward
    (D : InverseSystemOfFiniteSites.{v, u, w}) {i j : D.I} (a : i ⟶ j) :
    (abelianSheafPushforward.{v, u, w, t} D a).PreservesInjectiveObjects where
  injective_obj _ := injective_abelianSheafPushforward.{v, u, w, t} D a _

end System

attribute [local instance] preservesInjectiveObjects_abelianSheafPushforward

attribute [local instance_reducible] InverseSystemOfFiniteSites.abelianSheafPushforward

/-! ### The transition maps of the cohomology diagram of Stacks 09YP -/

section Diagram

open InverseSystemOfFiniteSites

universe v u t

variable {D : InverseSystemOfFiniteSites.{v, u, w}} {Cc : Type w} [SmallCategory Cc]
  {uC : ∀ i, D.C i ⥤ Cc} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
  {K : Precoverage Cc} {F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D}
  {𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t})}
  {ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj} {i : D.I} {X : D.C i} {p : ℕ}

/-- **The transition maps of the cohomology diagram of Stacks 09YP are the Leray edge
morphisms.** Read across the identifications `objIso` of the groups of the diagram with the right
derived sections of the levels, the map of the diagram at an arrow `f : A ⟶ B` of `Over i` is the
map induced by the transition map of the system of sheaves, followed by the edge morphism of the
pair (direct image along the transition functor, sections over the chart).

This is the field `map_eq` of the structure, which pins the map by
`Stacks.WeakSites.ColimitSiteCohomology.IsCohomologyMap`, read through
`IsCohomologyMap.eq_map_comp_edge_app`. It is what makes the calculus of
`StacksFrontier/Algebra/Homology/RightDerivedEdgeCalculus.lean` available to the diagram. -/
theorem CohomologyCocone.diagram_map_eq_edge_app
    (E : CohomologyCocone.{v, u, w, t} D uC hu K F 𝒢 ι i X p) {A B : Over i} (f : A ⟶ B) :
    (E.objIso B).inv ≫ E.diagram.map f.op ≫ (E.objIso A).hom ≫
        cohomologyCongr (D.J A.left) p (uObj_eq.{v, u, w} D f X) (F.obj A.left) =
      ((((sheafSections (D.J B.left) (Ab.{max u v w t})).obj
            (op ((D.u B.hom).obj X))).rightDerived p).map
          (((abelianSheafAdjunction.{v, u, w, t} D f.left).homEquiv
            (F.obj B.left) (F.obj A.left)) (F.map f.left))) ≫
        (edge (abelianSheafPushforward.{v, u, w, t} D f.left)
            ((sheafSections (D.J B.left) (Ab.{max u v w t})).obj
              (op ((D.u B.hom).obj X))) p).app
          (F.obj A.left) := by
  have := D.continuous f.left
  have := preservesInjectiveObjects_abelianSheafPushforward D f.left
  exact IsCohomologyMap.eq_map_comp_edge_app.{w, max u v t} (D.u f.left) _ _ p (E.map_eq f)

end Diagram

end Stacks.WeakSites.ColimitSiteCohomology

end
