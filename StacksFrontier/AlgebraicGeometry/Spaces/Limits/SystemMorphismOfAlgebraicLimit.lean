module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximationOfLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantChartLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageConeLimitOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemPropertiesOfAlgebraicLimit

/-!
# Stacks 0CPA with no bound on the index type

In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces over `B` with `X`
quasi-separated over `B`, and let `GX` and `GY` be diagrams as in Stacks 0CP8 for `X` and for
`Y`. Then some stage carries a morphism of the inverse systems of scheme-theoretic images
inducing `f`, and two such morphisms agree at every sufficiently late stage. Here no bound is
put on the size of the index type.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.imageSystem_hasChartLimitBridges`: the image system of a
  good diagram has limit bridges.
* `AlgebraicGeometry.Space.GoodDiagram.exists_systemMorphism_of_algebraicLimit`:
  **Stacks 0CPA, existence**.
* `AlgebraicGeometry.Space.GoodDiagram.eventually_eq_systemMorphism_of_algebraicLimit`:
  **Stacks 0CPA, eventual uniqueness**.
* `AlgebraicGeometry.Space.GoodDiagram.exists_systemMorphism_and_eventually_eq`: **Stacks 0CPA**.

## Implementation notes

The limit criterion for morphisms out of an inverse limit is applied to the image system in its
form with limit bridges, `AlgebraicGeometry.Space.exists_stage_map_of_limitBridge` and
`AlgebraicGeometry.Space.exists_stage_eq_of_limitBridge`; the image system has limit bridges
because its limit is `X` by Stacks 0CP9 and its projections are scheme-theoretically dominant.
The forms carrying the bound `#I < B.cutoff.ord.cof` are
`AlgebraicGeometry.Space.GoodDiagram.exists_systemMorphism` and
`AlgebraicGeometry.Space.GoodDiagram.eventually_eq_systemMorphism`.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

section SystemMorphisms

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    {pY : Y ⟶ D.limitCone.pt}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site over `S` is deep
/-- Limits of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
local instance hasLimits_presheaf_systemMorphismOfAlgebraicLimit :
    HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_systemMorphismOfAlgebraicLimit
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Limit bridges of the image system -/

/-- **The image system of a good diagram has limit bridges**, with no bound on the index
type. -/
theorem imageSystem_hasChartLimitBridges (GX : GoodDiagram B S hS hZ D pX)
    (hX : IsAlgebraicSpace B S hS X) : HasChartLimitBridges (imageSystem GX) := by
  let hc := isLimit_imageCone_of_algebraicLimit GX hX
  let e : X ≅ limit (imageSystem GX) := hc.conePointUniqueUpToIso (limit.isLimit _)
  have he (j : Over (op GX.index)) :
      e.inv ≫ (imageCone GX).π.app j = limit.π (imageSystem GX) j :=
    hc.conePointUniqueUpToIso_inv_comp (limit.isLimit _) j
  refine hasChartLimitBridges_of_dominant (imageSystem_isAlgebraicSpace GX)
    (fun g => imageSystem_map_isAffineHom GX g) (isAlgebraicSpace_of_iso B S hS e hX)
    fun j => ?_
  have : Epi e.inv := IsIso.epi_of_iso _
  rw [← he, schemeTheoreticImageSubfunctor_comp_of_epi]
  exact schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS (stageMap GX j)
    (isAlgebraicSpace_stageTarget GX j)

/-! ### Existence -/

/-- **Stacks 0CPA, existence.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `B` with `X` quasi-separated over `B`, and let `GX` and `GY` be diagrams as in
Stacks 0CP8 for `X` and for `Y`. Then some stage `i₀` above the indices of both diagrams
carries a morphism of the inverse systems of scheme-theoretic images on the tail above `i₀`,
over the system `(B_i)_{i ≥ i₀}`, whose limit is `f`. -/
theorem exists_systemMorphism_of_algebraicLimit (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (GX : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) :
    ∃ (i₀ : I) (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀),
      Nonempty (SystemMorphism GX GY f i₀ hiX hiY) := by
  classical
  obtain ⟨i₁, hiX₁, hiY₁⟩ := exists_ge_ge GX.index GY.index
  have hsq : (f ≫ GY.toModel) ≫ GY.modelMap =
      (imageCone GX).π.app (Over.mk (homOfLE hiX₁).op) ≫
        (stageImage GX (Over.mk (homOfLE hiX₁).op)).ι ≫
          pullback.fst _ _ ≫ D.system.map (homOfLE hiY₁).op := by
    rw [imageCone_π_ι_assoc, stageMap_fst_assoc, D.limitCone.w, Category.assoc,
      ← GY.commutes, ← Category.assoc, hf]
  obtain ⟨j, t, k, a, a', hlim, hover⟩ :=
    exists_stage_map_of_limitBridge B S hS hZ
      (imageSystem GX) (imageCone GX) (isLimit_imageCone_of_algebraicLimit GX hX)
      (imageSystem_hasChartLimitBridges GX hX)
      (imageSystem_isAlgebraicSpace GX) (imageSystem_isQuasiCompactSpace GX)
      (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit GX hX hXqs)
      (fun v => imageSystem_map_isAffineHom GX v)
      GY.model_isAlgebraicSpace (D.system_isAlgebraicSpace GY.index) GY.modelMap
      (isLocallyOfFinitePresentation_modelMap GY) (f ≫ GY.toModel)
      (Over.mk (homOfLE hiX₁).op)
      ((stageImage GX (Over.mk (homOfLE hiX₁).op)).ι ≫
        pullback.fst _ _ ≫ D.system.map (homOfLE hiY₁).op) hsq hX
  have ht : ((imageSystem GX).map a ≫ t) ≫ GY.modelMap =
      (stageImage GX k).ι ≫ pullback.fst _ _ ≫
        D.system.map (a'.left ≫ (homOfLE hiY₁).op) := by
    rw [hover, imageSystem_map_ι_assoc, stageTargetMap_fst_assoc, ← D.system.map_comp]
  exact ⟨k.left.unop, leOfHom k.hom.unop, leOfHom (a'.left ≫ (homOfLE hiY₁).op).unop,
    ⟨(exists_systemMorphism_of_stage_map GX GY f hf _ _ ((imageSystem GX).map a ≫ t) ht
      hlim).choose⟩⟩

/-! ### Eventual uniqueness -/

/-- **Stacks 0CPA, eventual uniqueness.** Two morphisms of the inverse systems of
scheme-theoretic images on the tail above a stage `i₀`, both inducing the same morphism
`f : X ⟶ Y` in the limit, have the same component at every sufficiently late stage. -/
theorem eventually_eq_systemMorphism_of_algebraicLimit (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX)
    {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {hiX : GX.index ≤ i₀} {hiY : GY.index ≤ i₀}
    (F G : SystemMorphism GX GY f i₀ hiX hiY) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ j : Over (op i₀), i₃ ≤ j.left.unop →
      F.maps.app j = G.maps.app j := by
  classical
  have hnat : ∀ (F : SystemMorphism GX GY f i₀ hiX hiY) {j k : Over (op i₀)} (a : j ⟶ k),
      (imageSystem GX).map ((Over.map (homOfLE hiX).op).map a) ≫ F.maps.app k ≫
          (stageImage GY ((Over.map (homOfLE hiY).op).obj k)).ι ≫ pullback.snd _ _ =
        F.maps.app j ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι ≫
          pullback.snd _ _ := by
    intro F j k a
    have hn : (imageSystem GX).map ((Over.map (homOfLE hiX).op).map a) ≫ F.maps.app k =
        F.maps.app j ≫ (imageSystem GY).map ((Over.map (homOfLE hiY).op).map a) :=
      F.maps.naturality a
    rw [← Category.assoc, hn, Category.assoc, imageSystem_map_ι_assoc, stageTargetMap_snd]
  let j₀ : Over (op i₀) := Over.mk (𝟙 (op i₀))
  let r : (imageSystem GX).obj ((Over.map (homOfLE hiX).op).obj j₀) ⟶ GY.model :=
    F.maps.app j₀ ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j₀)).ι ≫
      pullback.snd _ _
  let s : (imageSystem GX).obj ((Over.map (homOfLE hiX).op).obj j₀) ⟶ GY.model :=
    G.maps.app j₀ ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j₀)).ι ≫
      pullback.snd _ _
  have hind : (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j₀) ≫ F.maps.app j₀ =
      (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j₀) ≫ G.maps.app j₀ :=
    (F.induces j₀).trans (G.induces j₀).symm
  have hbas := fun j => (F.over_base j).trans (G.over_base j).symm
  have hlim : (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j₀) ≫ r =
      (imageCone GX).π.app ((Over.map (homOfLE hiX).op).obj j₀) ≫ s := by
    simp only [r, s, ← Category.assoc, hind]
  have hbase : r ≫ GY.modelMap = s ≫ GY.modelMap := by
    simp only [r, s, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using
      congrArg
        (fun z => z ≫ D.system.map ((Over.map (homOfLE hiY).op).obj j₀).hom) (hbas j₀)
  obtain ⟨kk, u, hu⟩ :=
    exists_stage_eq_of_limitBridge B S hS hZ
      (imageSystem GX) (imageCone GX) (isLimit_imageCone_of_algebraicLimit GX hX)
      (imageSystem_hasChartLimitBridges GX hX)
      (imageSystem_isAlgebraicSpace GX) (imageSystem_isQuasiCompactSpace GX)
      (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit GX hX hXqs)
      (fun v => imageSystem_map_isAffineHom GX v)
      GY.model_isAlgebraicSpace (D.system_isAlgebraicSpace GY.index) GY.modelMap
      (isLocallyOfFinitePresentation_modelMap GY)
      ((Over.map (homOfLE hiX).op).obj j₀) r s hlim hbase hX
  let j : Over (op i₀) := Over.mk u.left
  let e : (Over.map (homOfLE hiX).op).obj j ≅ kk :=
    Over.isoMk (Iso.refl _) (Subsingleton.elim _ _)
  let w : j ⟶ j₀ := Over.homMk u.left (Subsingleton.elim _ _)
  have he : e.hom ≫ u = (Over.map (homOfLE hiX).op).map w :=
    (Over.forget (op GX.index)).map_injective (Subsingleton.elim _ _)
  have hh : (imageSystem GX).map ((Over.map (homOfLE hiX).op).map w) ≫ r =
      (imageSystem GX).map ((Over.map (homOfLE hiX).op).map w) ≫ s := by
    rw [← he, Functor.map_comp, Category.assoc, Category.assoc, hu]
  have hk : F.maps.app j ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι ≫
        pullback.snd _ _ =
      G.maps.app j ≫ (stageImage GY ((Over.map (homOfLE hiY).op).obj j)).ι ≫
        pullback.snd _ _ := by
    rwa [← hnat F w, ← hnat G w]
  refine ⟨j.left.unop, leOfHom j.hom.unop, fun j' hj => ?_⟩
  have a : j' ⟶ j := Over.homMk (homOfLE hj).op (Subsingleton.elim _ _)
  refine (cancel_mono (stageImage GY ((Over.map (homOfLE hiY).op).obj j')).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · simpa only [Category.assoc] using hbas j'
  · rw [Category.assoc, Category.assoc, ← hnat F a, ← hnat G a, hk]

/-- **Stacks 0CPA.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces over
`B` with `X` quasi-separated over `B`, and let `GX` and `GY` be diagrams as in Stacks 0CP8 for
`X` and for `Y`, with the limit descriptions `X = lim X_i` and `Y = lim Y_i` of Stacks 0CP9.
Then some stage `i₀` above the indices of both diagrams carries a morphism `(f_i)_{i ≥ i₀}` of
the two inverse systems over `(B_i)_{i ≥ i₀}` with `f = lim f_i`; and any two such morphisms of
inverse systems on a common tail agree at every sufficiently late stage. -/
theorem exists_systemMorphism_and_eventually_eq (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsQuasiSeparated B S hS pX) (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (GX : GoodDiagram B S hS hZ D pX) (GY : GoodDiagram B S hS hZ D pY) :
    (∃ (i₀ : I) (hiX : GX.index ≤ i₀) (hiY : GY.index ≤ i₀),
      Nonempty (SystemMorphism GX GY f i₀ hiX hiY)) ∧
    ∀ {i₀ : I} {hiX : GX.index ≤ i₀} {hiY : GY.index ≤ i₀}
      (F G : SystemMorphism GX GY f i₀ hiX hiY),
      ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ j : Over (op i₀), i₃ ≤ j.left.unop →
        F.maps.app j = G.maps.app j :=
  ⟨exists_systemMorphism_of_algebraicLimit hX hXqs f hf GX GY,
    fun F G => eventually_eq_systemMorphism_of_algebraicLimit hX hXqs F G⟩

end SystemMorphisms

end GoodDiagram

end AlgebraicGeometry.Space

end
