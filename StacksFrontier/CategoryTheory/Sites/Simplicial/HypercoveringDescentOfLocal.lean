module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocalLifts

/-!
# Descent along the total site of a hypercovering (Stacks 0D8E)

Let `C` be a site and `K` a simplicial semi-representable object with `j_total` cover dense.
If any two vertices of `K` are locally joined by an edge and any boundary of a triangle is locally
filled, then `a^{-1}` is fully faithful with essential image the cartesian sheaves, and `a_*` is a
quasi-inverse; for a hypercovering these are conditions (2) and (3) of Stacks 09VU.

## Main results

All in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

* `descent_sheaves_of_local_hypercoveringDescentOfLocal` and
  `descent_abelianSheaves_of_local_hypercoveringDescentOfLocal`: descent along the total site
  from local edges and local triangles, for sheaves of sets and of abelian groups.
* `descent_sheaves_of_isHypercovering_hypercoveringDescentOfLocal` and
  `descent_abelianSheaves_of_isHypercovering_hypercoveringDescentOfLocal`:
  **Stacks 0D8E (1) and (2)** in full.

## Implementation notes

For a cartesian sheaf `G` the counit `a^{-1} a_* G ⟶ G` is invertible
(`isIso_counit_app_of_isCartesianSheaf_totalSiteDescent`). The unit is then invertible by the
triangle identity, since restriction along the cover-dense `j_total` reflects isomorphisms; no
local fullness of `j_total` is needed.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory

namespace SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C]

variable (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{u} C))
  [J.toCoverage.HasPullbacks]

/-! ### Descent along the total site, from local edges and local triangles -/

section Local

variable (hcd : (totalForget K).IsCoverDense J) (hE : HasLocalEdgesTotalSiteDescent J K)
  (hT : HasLocalTrianglesTotalSiteDescent J K)

/-- If the counit is invertible at `L.obj F`, then `L` maps the unit at `F` to an isomorphism. -/
private theorem isIso_map_unit_app_of_isIso_counit_app {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) (F : D) [IsIso (adj.counit.app (L.obj F))] :
    IsIso (L.map (adj.unit.app F)) :=
  isIso_of_comp_hom_eq_id _ (adj.left_triangle_components F)

include hcd hE hT in
/-- The unit `F ⟶ a_* a^{-1} F` of the localization morphism of the total site is invertible when
`j_total` is cover dense and `K` has local edges and local triangles. The triangle identity makes
`a^{-1}` of the unit an inverse of the counit at the cartesian sheaf `a^{-1} F`, and restriction
along the cover-dense functor `j_total` reflects isomorphisms. -/
theorem isIso_unit_of_local_hypercoveringDescentOfLocal :
    IsIso (totalLocalizationMorphism J K).adj.unit := by
  let a := totalLocalizationMorphism J K
  suffices key : ∀ F, IsIso (a.adj.unit.app F) from NatIso.isIso_of_isIso_app _
  intro F
  have hc : IsIso (a.adj.counit.app (a.inverseImage.obj F)) :=
    isIso_counit_app_of_isCartesianSheaf_totalSiteDescent
      (isCartesianSheaf_inverseImage J K F) hE hT
  have hl : IsIso (a.inverseImage.map (a.adj.unit.app F)) :=
    isIso_map_unit_app_of_isIso_counit_app a.adj F
  have hh : IsIso ((sheafToPresheaf _ _).map (a.inverseImage.map (a.adj.unit.app F))) :=
    inferInstance
  exact @Functor.IsCoverDense.isIso_of_isIso_whiskerLeft_totalSiteDescent _ _ _ _
    (totalForget K) J hcd _ _ (a.adj.unit.app F) hh

include hE hT in
/-- The essential image of `a^{-1}` is exactly the cartesian sheaves of sets when `K` has local
edges and local triangles. -/
theorem mem_essImage_iff_isCartesianSheaf_of_local_hypercoveringDescentOfLocal
    (F : Sheaf (situation J K).totalTopology (Type u)) :
    (totalLocalizationMorphism J K).inverseImage.essImage F ↔
      (situation J K).IsCartesianSheaf F :=
  ⟨isCartesianSheaf_of_mem_essImage J K, fun hF =>
    have := isIso_counit_app_of_isCartesianSheaf_totalSiteDescent hF hE hT
    ⟨_, ⟨asIso ((totalLocalizationMorphism J K).adj.counit.app F)⟩⟩⟩

include hcd hE hT in
/-- **Descent of sheaves of sets along the total site.** When `j_total` is cover dense and `K`
has local edges and local triangles, `a^{-1}` is fully faithful with essential image the
cartesian sheaves of sets, and `a_*` is a quasi-inverse. -/
theorem descent_sheaves_of_local_hypercoveringDescentOfLocal :
    Nonempty (totalLocalizationMorphism J K).inverseImage.FullyFaithful ∧
      (∀ F : Sheaf (situation J K).totalTopology (Type u),
        (totalLocalizationMorphism J K).inverseImage.essImage F ↔
          (situation J K).IsCartesianSheaf F) ∧
      IsIso (totalLocalizationMorphism J K).adj.unit ∧
      ∀ F : Sheaf (situation J K).totalTopology (Type u), (situation J K).IsCartesianSheaf F →
        IsIso ((totalLocalizationMorphism J K).adj.counit.app F) :=
  have := isIso_unit_of_local_hypercoveringDescentOfLocal J K hcd hE hT
  ⟨⟨(totalLocalizationMorphism J K).adj.fullyFaithfulLOfIsIsoUnit⟩,
    mem_essImage_iff_isCartesianSheaf_of_local_hypercoveringDescentOfLocal J K hE hT, this,
    fun _ hF => isIso_counit_app_of_isCartesianSheaf_totalSiteDescent hF hE hT⟩

include hcd hE hT in
/-- The unit of the abelian adjunction of the total site is invertible when `j_total` is cover
dense and `K` has local edges and local triangles. -/
theorem isIso_abelianUnit_of_local_hypercoveringDescentOfLocal :
    IsIso (abelianTotalAdjunction J K).unit := by
  let adj := abelianTotalAdjunction J K
  let L := (totalForget K).sheafPushforwardContinuous Ab.{u} ((situation J K).totalTopology) J
  suffices key : ∀ F, IsIso (adj.unit.app F) from NatIso.isIso_of_isIso_app _
  intro F
  have hc : IsIso (adj.counit.app (L.obj F)) :=
    isIso_abelianCounit_app_of_isCartesianAbSheaf_totalSiteDescent _
      (isCartesianAbSheaf_of_mem_essImage J K (L.obj_mem_essImage F)) hE hT
  have hl : IsIso (L.map (adj.unit.app F)) := isIso_map_unit_app_of_isIso_counit_app adj F
  have hh : IsIso (Functor.whiskerLeft (totalForget K).op
      ((sheafCompose J (forget Ab.{u})).map (adj.unit.app F)).hom) := by
    have h₂ : IsIso ((sheafToPresheaf _ _).map (L.map (adj.unit.app F))) := inferInstance
    rw [NatTrans.isIso_iff_isIso_app] at h₂ ⊢
    intro U
    exact (forget Ab.{u}).map_isIso ((L.map (adj.unit.app F)).hom.app U)
  have hs := @Functor.IsCoverDense.isIso_of_isIso_whiskerLeft_totalSiteDescent _ _ _ _
    (totalForget K) J hcd _ _ _ hh
  have hp : IsIso ((sheafToPresheaf _ _).map (adj.unit.app F)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    have h₃ : IsIso ((sheafToPresheaf _ _).map
        ((sheafCompose J (forget Ab.{u})).map (adj.unit.app F))) := inferInstance
    rw [NatTrans.isIso_iff_isIso_app] at h₃
    have h₄ : IsIso ((forget Ab.{u}).map ((adj.unit.app F).hom.app U)) := h₃ U
    exact isIso_of_reflects_iso _ (forget Ab.{u})
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

include hE hT in
/-- The essential image of `a^{-1}` on abelian sheaves is exactly the cartesian abelian sheaves
when `K` has local edges and local triangles. -/
theorem mem_essImage_iff_isCartesianAbSheaf_of_local_hypercoveringDescentOfLocal
    (F : Sheaf (situation J K).totalTopology Ab.{u}) :
    ((totalForget K).sheafPushforwardContinuous Ab.{u}
        ((situation J K).totalTopology) J).essImage F ↔
      (situation J K).IsCartesianAbSheaf F :=
  ⟨isCartesianAbSheaf_of_mem_essImage J K, fun hF =>
    have : IsIso ((abelianTotalAdjunction J K).counit.app F) :=
      isIso_abelianCounit_app_of_isCartesianAbSheaf_totalSiteDescent F hF hE hT
    ⟨_, ⟨asIso ((abelianTotalAdjunction J K).counit.app F)⟩⟩⟩

include hcd hE hT in
/-- **Descent of abelian sheaves along the total site.** When `j_total` is cover dense and `K`
has local edges and local triangles, `a^{-1}` is fully faithful with essential image the
cartesian abelian sheaves, and `a_*` is a quasi-inverse. -/
theorem descent_abelianSheaves_of_local_hypercoveringDescentOfLocal :
    Nonempty ((totalForget K).sheafPushforwardContinuous Ab.{u}
        ((situation J K).totalTopology) J).FullyFaithful ∧
      (∀ F : Sheaf (situation J K).totalTopology Ab.{u},
        ((totalForget K).sheafPushforwardContinuous Ab.{u}
            ((situation J K).totalTopology) J).essImage F ↔
          (situation J K).IsCartesianAbSheaf F) ∧
      IsIso (abelianTotalAdjunction J K).unit ∧
      ∀ F : Sheaf (situation J K).totalTopology Ab.{u}, (situation J K).IsCartesianAbSheaf F →
        IsIso ((abelianTotalAdjunction J K).counit.app F) :=
  have := isIso_abelianUnit_of_local_hypercoveringDescentOfLocal J K hcd hE hT
  ⟨⟨(abelianTotalAdjunction J K).fullyFaithfulLOfIsIsoUnit⟩,
    mem_essImage_iff_isCartesianAbSheaf_of_local_hypercoveringDescentOfLocal J K hE hT, this,
    fun F hF => isIso_abelianCounit_app_of_isCartesianAbSheaf_totalSiteDescent F hF hE hT⟩

end Local

section Hypercovering

variable [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u, u} P)

/-! ### Descent along a hypercovering -/

/-- **Stacks 0D8E (1).** Let `C` be a site with equalizers and fibre products and `K` a
hypercovering. Then `a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` is fully faithful with essential image the
cartesian sheaves of sets, and `a_*` is a quasi-inverse: the unit `F ⟶ a_* a^{-1} F` is invertible
for every `F`, and the counit `a^{-1} a_* G ⟶ G` is invertible for every cartesian `G`. -/
theorem descent_sheaves_of_isHypercovering_hypercoveringDescentOfLocal :
    Nonempty (totalLocalizationMorphism P.toGrothendieck
        H.toSimplicialObject).inverseImage.FullyFaithful ∧
      (∀ F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u),
        (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).inverseImage.essImage F ↔
          (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf F) ∧
      IsIso (totalLocalizationMorphism P.toGrothendieck H.toSimplicialObject).adj.unit ∧
      ∀ F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology (Type u),
        (situation P.toGrothendieck H.toSimplicialObject).IsCartesianSheaf F →
          IsIso ((totalLocalizationMorphism P.toGrothendieck
            H.toSimplicialObject).adj.counit.app F) :=
  descent_sheaves_of_local_hypercoveringDescentOfLocal P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (hasLocalEdges_of_hypercovering_hypercoveringLocalLifts P H)
    (hasLocalTriangles_of_hypercovering_hypercoveringLocalLifts P H)

/-- **Stacks 0D8E (2).** Let `C` be a site with equalizers and fibre products and `K` a
hypercovering. Then `a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` is fully faithful with essential image the
cartesian sheaves of abelian groups, and `a_*` is a quasi-inverse: the unit is invertible, and the
counit is invertible at every cartesian abelian sheaf. -/
theorem descent_abelianSheaves_of_isHypercovering_hypercoveringDescentOfLocal :
    Nonempty ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
        ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
        P.toGrothendieck).FullyFaithful ∧
      (∀ F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u},
        ((totalForget H.toSimplicialObject).sheafPushforwardContinuous Ab.{u}
            ((situation P.toGrothendieck H.toSimplicialObject).totalTopology)
            P.toGrothendieck).essImage F ↔
          (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf F) ∧
      IsIso (abelianTotalAdjunction P.toGrothendieck H.toSimplicialObject).unit ∧
      ∀ F : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u},
        (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf F →
          IsIso ((abelianTotalAdjunction P.toGrothendieck H.toSimplicialObject).counit.app F) :=
  descent_abelianSheaves_of_local_hypercoveringDescentOfLocal P.toGrothendieck H.toSimplicialObject
    (isCoverDense_totalForget P H) (hasLocalEdges_of_hypercovering_hypercoveringLocalLifts P H)
    (hasLocalTriangles_of_hypercovering_hypercoveringLocalLifts P H)

end Hypercovering

end SimplicialSemiRepresentable

end CategoryTheory

end
