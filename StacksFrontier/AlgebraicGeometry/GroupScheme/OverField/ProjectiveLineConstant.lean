module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import StacksFrontier.AlgebraicGeometry.Spaces.DiscreteRepresentingSchemeSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLineFactorization
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Morphisms from the projective line to a group scheme over a field are constant

Let `k` be a field and let `G` be a group scheme over `k` which is locally of finite type. Every
morphism `f : ℙ¹_k ⟶ G` of schemes over `Spec k` is constant: it factors through the structure
morphism `ℙ¹_k ⟶ Spec k` followed by a `k`-rational point of `G`. Here `ℙ¹_k` is the model
`AlgebraicGeometry.projectiveLineProj k = Proj k[T₀, T₁]` used for exceptional curves, with its
structure morphism `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1`.

This is the scheme form of [Stacks, Tag 0AEN], which is stated for group algebraic spaces and is
`AlgebraicGeometry.Space.morphism_projectiveLine_constant`. The group scheme is carried to a group
algebraic space over `Spec k` by Stacks 043I
(`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`), on a big fppf site chosen to
contain `Spec k` and `G` (`AlgebraicGeometry.BigFppfSite.exists_containing`), and the constant
morphism it returns is read back through the Yoneda embedding. Separatedness of `G` is not a
hypothesis: a group scheme over a field is separated (Stacks 047L,
`AlgebraicGeometry.isSeparated_of_groupScheme_over_field`).

## Main definitions

* `AlgebraicGeometry.projectiveLineProjIsoProjectiveSpaceOverRing`: the isomorphism of
  `projectiveLineProj k` with the base-change model `ℙ¹_{Spec k}` of the projective line.

## Main results

* `AlgebraicGeometry.exists_section_eq_comp_of_projectiveLineProj`: a morphism over `Spec k` from
  `projectiveLineProj k` to a locally algebraic group scheme `G` over `k` is the structure
  morphism followed by a section of `G ⟶ Spec k`.
* `AlgebraicGeometry.exists_base_eq_of_projectiveLineProj`: its image is a single point.

## References

* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 047L](https://stacks.math.columbia.edu/tag/047L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The projective line `projectiveLineProj k = Proj k[T₀, T₁]` is isomorphic to the projective
line `ℙ¹_{Spec k}` of the base-change model, through the glued projective line. -/
def projectiveLineProjIsoProjectiveSpaceOverRing :
    projectiveLineProj k ≅ projectiveSpaceOverRing 1 (CommRingCat.of k) :=
  (projectiveLineIsoProj k).symm ≪≫ projectiveLineIsoProjectiveSpaceOver k

/-- The isomorphism `projectiveLineProj k ≅ ℙ¹_{Spec k}` is an isomorphism over `Spec k`: it
carries the structure morphism of `ℙ¹_{Spec k}` to `projToSpecCoeff k 1`. -/
@[reassoc]
theorem projectiveLineProjIsoProjectiveSpaceOverRing_hom_comp :
    projectiveLineProjIsoProjectiveSpaceOverRing.hom ≫
        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
      projToSpecCoeff k 1 := by
  simp only [projectiveLineProjIsoProjectiveSpaceOverRing, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, projectiveLineIsoProjectiveSpaceOver_hom_fst]
  rw [← projectiveLineIsoProj_hom_comp_projToSpecCoeff, Iso.inv_hom_id_assoc]

/-- **Morphisms from the projective line to a group scheme over a field are constant.** Let `k`
be a field and let `G` be a group scheme over `k` locally of finite type. Every morphism
`f : ℙ¹_k ⟶ G` over `Spec k` is the structure morphism `ℙ¹_k ⟶ Spec k` followed by a section
`c` of the structure morphism of `G`.

This is the scheme form of [Stacks, Tag 0AEN], deduced from the version for group algebraic
spaces, `AlgebraicGeometry.Space.morphism_projectiveLine_constant`. -/
theorem exists_section_eq_comp_of_projectiveLineProj (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] (f : projectiveLineProj k ⟶ G.left)
    (hf : f ≫ G.hom = projToSpecCoeff k 1) :
    ∃ c : Spec (CommRingCat.of k) ⟶ G.left, c ≫ G.hom = 𝟙 _ ∧ f = projToSpecCoeff k 1 ≫ c := by
  classical
  let S := Spec (CommRingCat.of k)
  -- A big fppf site containing `Spec k` and `G`.
  obtain ⟨C, hC⟩ := BigFppfSite.exists_containing ({S, G.left} : Set Scheme.{u})
  have hk : C.Contains S := hC _ (by simp)
  have hG : C.Contains G.left := hC _ (by simp)
  -- `G` as an object of the site over `Spec k`, with its group structure.
  let T : BigFppfOver C S hk := siteObject C S hk hG G.hom
  let hT : GrpObj ((Space.toSchemeOver C S hk).obj T) :=
    GrpObj.ofIso (Over.isoMk (Iso.refl _) (Category.id_comp _) :
      G ≅ (Space.toSchemeOver C S hk).obj T)
  -- The group algebraic space of Stacks 043I and its identification with `yoneda.obj T`.
  let Γ := Space.GroupAlgebraicSpace.ofGroupSchemeInSite C S hk
    (Space.terminalSpace C S hk).obj (Space.terminalSpace C S hk).property T hT
  let e : yoneda.obj T ≅ Γ.obj.X.left :=
    Space.GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda T hT
  have ht := Space.base_isTerminal k C hk
  -- Separatedness and local finite type of `Γ`.
  have hTsep : Scheme.IsSeparated ((BigFppfOver.toScheme C S hk).obj T) :=
    isSeparated_of_groupScheme_over_field (Grp.mk G)
  have hsep : Space.IsSeparatedOver C S hk Γ.obj.X.left := by
    refine (Space.isSeparatedOver_iff_isSeparated_of_isTerminal C S hk ht
      (e.inv ≫ ht.from (yoneda.obj T))).2 ?_
    exact Space.isSeparated_comp C S hk _ _ (Space.isSeparated_of_isIso C S hk e.inv)
      (Space.isSeparated_of_isSeparatedOver C S hk
        (Space.isSeparatedOver_yoneda_obj C S hk T hTsep) _)
  have hft : Space.IsLocallyOfFiniteType C S hk Γ.obj.X.hom :=
    (Space.isLocallyOfFiniteType_hom_iff_of_iso_yoneda Γ.obj.X T e).2
      (inferInstanceAs (LocallyOfFiniteType G.hom))
  -- The morphism `f`, transported to the base-change model of `ℙ¹_k` and to the site.
  let ι := projectiveLineProjIsoProjectiveSpaceOverRing (k := k)
  let g : projectiveSpaceOverRing 1 (CommRingCat.of k) ⟶ G.left := ι.inv ≫ f
  have hg : g ≫ G.hom = projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ S := by
    rw [Category.assoc, hf, ← projectiveLineProjIsoProjectiveSpaceOverRing_hom_comp,
      Iso.inv_hom_id_assoc]
  let P := Space.projectiveLineSiteObject k C hk
  let gSite : P ⟶ T := Over.homMk (ObjectProperty.homMk g) (by ext1; exact hg)
  let ρ := Space.projectiveLineRestrictedYonedaIso k C hk
  let φ : Space.projectiveLinePower k C hk (Fin 1) ⟶ Γ.obj.X.left :=
    Pi.π _ 0 ≫ ρ.hom ≫ yoneda.map gSite ≫ e.hom
  let f' : Space.projectiveLineOverBase k C hk ⟶ Γ.obj.X :=
    Over.homMk φ (ht.hom_ext _ _)
  obtain ⟨c, -, hc⟩ := Space.morphism_projectiveLine_constant k C hk Γ hsep hft f'
  -- Reading the constant morphism back as a morphism of schemes.
  let cSite : Space.baseTerminal C S hk ⟶ T := Yoneda.fullyFaithful.preimage (c ≫ e.inv)
  have hcSite : yoneda.map cSite = c ≫ e.inv := Yoneda.fullyFaithful.map_preimage _
  let σ : yoneda.obj P ⟶ Space.projectiveLinePower k C hk (Fin 1) :=
    ρ.inv ≫ Pi.lift (fun _ => 𝟙 _)
  have hgc : gSite = Space.toBaseTerminal C S hk P ≫ cSite := by
    apply yoneda.map_injective
    have h1 : σ ≫ φ ≫ e.inv = yoneda.map gSite := by simp [σ, φ]
    have h2 : σ ≫ (Space.projectiveLineOverBase k C hk).hom =
        yoneda.map (Space.toBaseTerminal C S hk P) := ht.hom_ext _ _
    rw [← h1, Functor.map_comp, hcSite, ← h2]
    have : φ = (Space.projectiveLineOverBase k C hk).hom ≫ c := hc
    rw [this]
    exact (congrArg (σ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm
  refine ⟨C.inclusion.map cSite.left, ?_, ?_⟩
  · have := congrArg C.inclusion.map (Over.w cSite)
    rw [Functor.map_comp] at this
    exact this.trans (C.inclusion.map_id _)
  · have := congrArg (fun φ => C.inclusion.map φ.left) hgc
    simp only [Over.comp_left, Functor.map_comp] at this
    have hP : C.inclusion.map (Space.toBaseTerminal C S hk P).left =
        projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ S := rfl
    rw [hP] at this
    calc f = ι.hom ≫ g := by simp [g]
      _ = projToSpecCoeff k 1 ≫ C.inclusion.map cSite.left := by
        rw [show C.inclusion.map gSite.left = g from rfl] at this
        rw [this]
        exact (Category.assoc _ _ _).symm.trans
          (projectiveLineProjIsoProjectiveSpaceOverRing_hom_comp =≫ _)

/-- **The image of a morphism from the projective line to a group scheme over a field is a
point.** Let `k` be a field and let `G` be a group scheme over `k` locally of finite type. Every
morphism `f : ℙ¹_k ⟶ G` over `Spec k` sends every point of `ℙ¹_k` to one and the same point of
`G`. -/
theorem exists_base_eq_of_projectiveLineProj (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] (f : projectiveLineProj k ⟶ G.left)
    (hf : f ≫ G.hom = projToSpecCoeff k 1) :
    ∃ g : G.left, ∀ z, f.base z = g := by
  obtain ⟨c, -, rfl⟩ := exists_section_eq_comp_of_projectiveLineProj G f hf
  refine ⟨c.base (IsLocalRing.closedPoint k), fun z => ?_⟩
  change c.base ((projToSpecCoeff k 1).base z) = _
  exact congrArg c.base (Subsingleton.elim _ _)

end AlgebraicGeometry

end
