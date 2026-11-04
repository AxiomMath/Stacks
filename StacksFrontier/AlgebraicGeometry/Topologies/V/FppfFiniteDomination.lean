module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfPhComparison

/-!
# Finite domination of an fppf covering

Stacks 0CP0 states that an fppf covering of a quasi-compact and quasi-separated scheme `S` is
dominated by a *finite* surjective morphism `g : S' ⟶ S` of finite presentation which, on a
Zariski covering of `S'`, factors through members of the given covering. The Stacks proof
deduces it from two inputs: the same statement with `g` merely *integral* (Stacks 0CNZ), and
the presentation of an integral morphism over a quasi-compact and quasi-separated base as a
directed inverse limit of finite morphisms of finite presentation (Stacks 09YZ). Given those,
one chooses a finite affine open cover of the integral dominating scheme, descends it and the
factorisations to a single stage of the inverse system, and takes that stage.

This file carries out that deduction, with the two inputs isolated as the hypotheses
`AlgebraicGeometry.FppfHasIntegralDomination` and
`AlgebraicGeometry.IntegralHasFinitePresentationLimit`. Nothing here is tagged: every result
is conditional on those two hypotheses, which are exactly Stacks 0CNZ and Stacks 09YZ and are
not themselves proved anywhere in the library.

## Main definitions

* `AlgebraicGeometry.IntegralLimitPresentation` is the data exhibiting a morphism as a
  directed inverse limit of finite morphisms of finite presentation to the same base.
* `AlgebraicGeometry.FppfHasIntegralDomination` is the statement of Stacks 0CNZ.
* `AlgebraicGeometry.IntegralHasFinitePresentationLimit` is the statement of Stacks 09YZ.

## Main results

* `AlgebraicGeometry.exists_finite_surjective_refinement_of_mem_fppfPrecoverage` is Stacks
  0CP0, granted the two hypotheses.
* `AlgebraicGeometry.fppfHasFiniteDomination` derives
  `AlgebraicGeometry.FppfHasFiniteDomination`, the input that
  `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` carries, from the same two
  hypotheses.

## Implementation notes

The bulk of the argument is stated as
`AlgebraicGeometry.exists_finite_surjective_refinement_of_isLimit`, whose binders carry the
inverse system itself rather than a bundled `AlgebraicGeometry.IntegralLimitPresentation`:
with the index type, its order and the diagram behind variables, every instance that the limit
lemmas of `Mathlib.AlgebraicGeometry.AffineTransitionLimit` demand is synthesised against a
variable. The order and directedness of the index type are then supplied at the call site by
`@`-application rather than by a local instance, since a local instance binding the order to a
projection of the presentation is both flagged by the style linters and liable to be found in
place of the projection appearing in the types of the other fields.

`AlgebraicGeometry.IntegralHasFinitePresentationLimit` asserts only that a presentation
*exists*, rather than producing one, so that it is a `Prop` and so that the hypothesis is as
weak as possible.

## References

* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A presentation of a morphism of schemes as the limit of a directed inverse system of
finite morphisms of finite presentation to the same base. This is the data that Stacks 09YZ
produces for an integral morphism over a quasi-compact and quasi-separated base. -/
structure IntegralLimitPresentation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The type indexing the inverse system. -/
  indexType : Type u
  /-- The order making the index type a directed preorder. -/
  [indexPreorder : Preorder indexType]
  [indexNonempty : Nonempty indexType]
  [indexDirected : IsDirected indexType (· ≤ ·)]
  /-- The inverse system of schemes. -/
  diagram : indexTypeᵒᵖ ⥤ Scheme.{u}
  /-- The compatible structure morphisms from the stages to the base. -/
  structureMap : diagram ⟶ (Functor.const indexTypeᵒᵖ).obj S
  /-- The cone from the source scheme to the inverse system. -/
  limitCone : (Functor.const indexTypeᵒᵖ).obj X ⟶ diagram
  /-- Passing from the source through any stage induces the original morphism to the base. -/
  compatible : ∀ i, f = limitCone.app i ≫ structureMap.app i
  /-- The displayed cone exhibits the source scheme as the limit. -/
  isLimit : IsLimit (Cone.mk X limitCone)
  /-- Every stage is finite over the base. -/
  stageFinite : ∀ i, IsFinite (structureMap.app i)
  /-- Every stage is of finite presentation over the base. -/
  stageFinitePresentation : ∀ i, FinitePresentation (structureMap.app i)

/-- **Stacks 0CNZ** as a hypothesis: an fppf covering of a scheme is dominated by a surjective
*integral* morphism which, on a Zariski covering of its source, factors through members of the
given covering. -/
def FppfHasIntegralDomination : Prop :=
  ∀ (I : Type v) (_ : Small.{u} I) (S : Scheme.{u}) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S),
    Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S →
      ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsIntegralHom g ∧ Surjective g ∧
        ∃ (J : Type u) (U : J → Scheme.{u}) (j : ∀ a, U a ⟶ S'),
          Presieve.ofArrows U j ∈ Scheme.zariskiPrecoverage S' ∧
            ∀ a, ∃ i, ∃ h : U a ⟶ X i, j a ≫ g = h ≫ f i

/-- **Stacks 09YZ** as a hypothesis: an integral morphism over a quasi-compact and
quasi-separated base is a directed inverse limit of finite morphisms of finite presentation to
that base. -/
def IntegralHasFinitePresentationLimit : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) (_ : IsIntegralHom f) (_ : CompactSpace S)
    (_ : QuasiSeparatedSpace S), Nonempty (IntegralLimitPresentation f)

/-- The core of Stacks 0CP0: given an integral surjective morphism `g : Y ⟶ S` dominating the
fppf covering `{f i}` Zariski locally, and a presentation of `g` as the limit of an inverse
system `D` of finite morphisms of finite presentation to `S`, one of the stages of `D` already
dominates the covering Zariski locally.

A finite affine open cover of `Y` refining the given Zariski covering descends to a cover of
one stage, and the factorisations through the members of the fppf covering descend to a
further stage, which can be chosen uniformly because the cover is finite. -/
theorem exists_finite_surjective_refinement_of_isLimit
    {I : Type v} {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S} (hfp : ∀ i, LocallyOfFinitePresentation (f i))
    {Y : Scheme.{u}} {g : Y ⟶ S} [IsIntegralHom g] [Surjective g]
    {J : Type u} {W : J → Scheme.{u}} {w : ∀ a, W a ⟶ Y}
    (hwcover : Presieve.ofArrows W w ∈ Scheme.zariskiPrecoverage Y)
    (hwfac : ∀ a, ∃ i, ∃ h : W a ⟶ X i, w a ≫ g = h ≫ f i)
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)] {D : Λᵒᵖ ⥤ Scheme.{u}}
    (t : D ⟶ (Functor.const Λᵒᵖ).obj S) (lc : (Functor.const Λᵒᵖ).obj Y ⟶ D)
    (hcompat : ∀ i, g = lc.app i ≫ t.app i) (hlim : IsLimit (Cone.mk Y lc))
    (hstageFinite : ∀ i, IsFinite (t.app i))
    (hstageFP : ∀ i, FinitePresentation (t.app i)) :
    ∃ (S' : Scheme.{u}) (g' : S' ⟶ S),
      IsFinite g' ∧ Surjective g' ∧ FinitePresentation g' ∧
        ∃ (K : Type u) (U : K → Scheme.{u}) (j : ∀ a, U a ⟶ S'),
          Presieve.ofArrows U j ∈ Scheme.zariskiPrecoverage S' ∧
            ∀ a, ∃ i, ∃ h : U a ⟶ X i, j a ≫ g' = h ≫ f i := by
  classical
  have hwdata := (Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).mp hwcover
  have hwopen : ∀ a, IsOpenImmersion (w a) := hwdata.2
  have hnat : ∀ {i j : Λᵒᵖ} (q : i ⟶ j), D.map q ≫ t.app j = t.app i := by
    intro i j q
    simp
  have haffine : ∀ {i j : Λᵒᵖ} (q : i ⟶ j), IsAffineHom (D.map q) := by
    intro i j q
    have := hstageFinite i
    have := hstageFinite j
    have : IsAffineHom (D.map q ≫ t.app j) := by
      rw [hnat q]; exact (hstageFinite i).toIsAffineHom
    exact IsAffineHom.of_comp (D.map q) (t.app j)
  have hcpt : ∀ i : Λᵒᵖ, CompactSpace (D.obj i) := by
    intro i
    have := hstageFinite i
    have : CompactSpace (((Functor.const Λᵒᵖ).obj S).obj i) := by
      dsimp
      infer_instance
    exact QuasiCompact.compactSpace_of_compactSpace (t.app i)
  have hqsep : ∀ i : Λᵒᵖ, QuasiSeparatedSpace (D.obj i) := by
    intro i
    have := hstageFinite i
    have : QuasiSeparatedSpace (((Functor.const Λᵒᵖ).obj S).obj i) := by
      dsimp
      infer_instance
    exact quasiSeparatedSpace_of_quasiSeparated (t.app i)
  have hYcompact : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  -- Refine the Zariski covering of `Y` by a finite affine open covering.
  have hW : IsOpenCover fun a : J => (w a).opensRange :=
    IsOpenCover.mk <| eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr (hwdata.1 y)
  let 𝒲 : Y.OpenCover := Y.openCoverOfIsOpenCover (fun a : J => (w a).opensRange) hW
  let C := 𝒲.affineRefinement
  let R := 𝒲.fromAffineRefinement
  let 𝒱 := C.openCover.finiteSubcover
  have : Finite 𝒱.I₀ := inferInstance
  have hVaff : ∀ a : 𝒱.I₀, IsAffineOpen (𝒱.f a).opensRange := by
    intro a
    have : IsAffine (𝒱.X a) := by
      change IsAffine (Spec _)
      infer_instance
    apply isAffineOpen_opensRange
  let c : Cone D := Cone.mk Y lc
  obtain ⟨k, V, hVcover, hVeq⟩ :=
    Scheme.exists_isOpenCover_and_isAffine_of_finite D c hlim
      (fun a : 𝒱.I₀ => (𝒱.f a).opensRange) 𝒱.isOpenCover_opensRange hVaff
  have hVrange (a : 𝒱.I₀) :
      Set.range (𝒱.f a).base = Set.range ((lc.app k ⁻¹ᵁ V a).ι).base := by
    have h := dsimp% congr($((hVeq a).2).carrier)
    simpa using h
  have hbase (a : 𝒱.I₀) {j j' : Over k} (q : j ⟶ j') :
      (opensDiagram D k (V a)).map q ≫
        ((opensDiagramι D k (V a)).app j' ≫ t.app j'.left) =
        (opensDiagramι D k (V a)).app j ≫ t.app j.left := by
    have hna := (opensDiagramι D k (V a)).naturality q
    dsimp at hna ⊢
    rw [← Category.assoc, hna, Category.assoc, hnat q.left]
  have hFactor (a : 𝒱.I₀) :
      ∃ (i : I) (j : Over k) (z : (opensDiagram D k (V a)).obj j ⟶ X i),
        z ≫ f i = ((opensDiagramι D k (V a)).app j ≫ t.app j.left) := by
    let b := C.openCover.idx a.1
    let d : J := R.s₀ b
    have hfacA' : C.openCover.f b = R.h₀ b ≫ 𝒲.f d := by
      simp [d, R, C]
    have hrange : Set.range (𝒲.f d).base = Set.range (w d).base := by
      change Set.range (Scheme.Opens.ι (Scheme.Hom.opensRange (w d))).base = _
      rw [Scheme.Opens.range_ι]
      rfl
    let e := IsOpenImmersion.isoOfRangeEq (𝒲.f d) (w d) hrange
    obtain ⟨i, h, hcomm⟩ := hwfac d
    let z₀ : 𝒱.X a ⟶ X i := by
      change C.openCover.X b ⟶ X i
      exact R.h₀ b ≫ e.hom ≫ h
    have hz₀ : z₀ ≫ f i = 𝒱.f a ≫ g := by
      change (R.h₀ b ≫ e.hom ≫ h) ≫ f i = C.openCover.f b ≫ g
      simp only [hfacA', Category.assoc, ← hcomm]
      simp [e]
    let U := lc.app k ⁻¹ᵁ V a
    let eU := IsOpenImmersion.isoOfRangeEq (𝒱.f a) U.ι (hVrange a)
    let a₀ := eU.inv ≫ z₀
    have ha₀ : a₀ ≫ f i = U.ι ≫ g := by
      simp [a₀, eU, hz₀]
    let Dₐ := opensDiagram D k (V a)
    let tₐ : Dₐ ⟶ (Functor.const (Over k)).obj S :=
      { app := fun j => (opensDiagramι D k (V a)).app j ≫ t.app j.left
        naturality j j' q := by simpa [Dₐ] using hbase a q }
    let cₐ := opensCone D c k (V a)
    have hcone (j : Over k) :
        cₐ.π.app j ≫ (opensDiagramι D k (V a)).app j = U.ι ≫ lc.app j.left := by
      simp [cₐ, U, c, opensCone, opensDiagram, opensDiagramι]
    have hleft (j : Over k) : cₐ.π.app j ≫ tₐ.app j = U.ι ≫ g := by
      change cₐ.π.app j ≫ (opensDiagramι D k (V a)).app j ≫ t.app j.left = _
      rw [← Category.assoc, hcone j, hcompat j.left]
      exact Category.assoc _ _ _
    have ha : cₐ.π ≫ tₐ = (Functor.const (Over k)).map (a₀ ≫ f i) := by
      ext j
      simpa [Functor.const_obj_map, Category.id_comp] using (hleft j).trans ha₀.symm
    have : LocallyOfFinitePresentation (f i) := hfp i
    have : ∀ j, IsAffine (Dₐ.obj j) := by
      intro j
      exact (hVeq a).1.preimage _
    obtain ⟨j, z, -, hz⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      Dₐ tₐ (f i) cₐ (isLimitOpensCone D c hlim k (V a)) a₀ ha
    exact ⟨i, j, z, hz⟩
  choose iMap jMap zMap hzMap using hFactor
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image jMap)
  have qMap (a : 𝒱.I₀) : j ⟶ jMap a := (hj (by simp)).some
  have hcommonCover : IsOpenCover fun a : 𝒱.I₀ => D.map j.hom ⁻¹ᵁ V a := by
    apply IsOpenCover.mk
    rw [← Scheme.Hom.preimage_iSup, hVcover]
    simp
  have hcommonFactor (a : 𝒱.I₀) :
      ∃ h : ↑(D.map j.hom ⁻¹ᵁ V a) ⟶ X (iMap a),
        h ≫ f (iMap a) = (D.map j.hom ⁻¹ᵁ V a).ι ≫ t.app j.left := by
    let Dₐ := opensDiagram D k (V a)
    let q := qMap a
    refine ⟨Dₐ.map q ≫ zMap a, ?_⟩
    change (Dₐ.map q ≫ zMap a) ≫ f (iMap a) =
      (D.map j.hom ⁻¹ᵁ V a).ι ≫ t.app j.left
    rw [Category.assoc, hzMap a, hbase a q]
    rfl
  have : Surjective (t.app j.left) := by
    have hs : Surjective (lc.app j.left ≫ t.app j.left) := by
      simpa [hcompat j.left] using ‹Surjective g›
    exact Surjective.of_comp (lc.app j.left) (t.app j.left)
  refine ⟨D.obj j.left, t.app j.left, hstageFinite j.left, inferInstance,
    hstageFP j.left, ?_⟩
  refine ⟨𝒱.I₀, fun a => (↑(D.map j.hom ⁻¹ᵁ V a) : Scheme), fun a => (D.map j.hom ⁻¹ᵁ V a).ι,
    ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)]
    refine ⟨fun x => ?_, fun a => inferInstance⟩
    obtain ⟨a, hx⟩ := hcommonCover.exists_mem x
    exact ⟨a, ⟨⟨x, hx⟩, rfl⟩⟩
  · intro a
    obtain ⟨h, hh⟩ := hcommonFactor a
    exact ⟨iMap a, h, hh.symm⟩

/-- **Stacks 0CP0**, granted `AlgebraicGeometry.FppfHasIntegralDomination` (Stacks 0CNZ) and
`AlgebraicGeometry.IntegralHasFinitePresentationLimit` (Stacks 09YZ): an fppf covering of a
quasi-compact and quasi-separated scheme is dominated by a finite surjective morphism of
finite presentation which, on a Zariski covering of its source, factors through members of the
given covering.

No tag is attached, since the result is conditional on the two hypotheses. -/
theorem exists_finite_surjective_refinement_of_mem_fppfPrecoverage
    (H₁ : FppfHasIntegralDomination.{u, v}) (H₂ : IntegralHasFinitePresentationLimit.{u})
    {I : Type v} [Small.{u} I] {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
        ∃ (J : Type u) (U : J → Scheme.{u}) (j : ∀ a, U a ⟶ S'),
          Presieve.ofArrows U j ∈ Scheme.zariskiPrecoverage S' ∧
            ∀ a, ∃ i, ∃ h : U a ⟶ X i, j a ≫ g = h ≫ f i := by
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := fun i =>
    (((Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hf).2 i).2
  obtain ⟨Y, g, hgint, hgsurj, J, W, w, hwcover, hwfac⟩ := H₁ I inferInstance S X f hf
  obtain ⟨p⟩ := H₂ Y S g hgint inferInstance inferInstance
  exact @exists_finite_surjective_refinement_of_isLimit I S inferInstance inferInstance X f hfp
    Y g hgint hgsurj J W w hwcover hwfac p.indexType p.indexPreorder p.indexNonempty
    p.indexDirected p.diagram p.structureMap p.limitCone p.compatible p.isLimit p.stageFinite
    p.stageFinitePresentation

/-- Granted `AlgebraicGeometry.FppfHasIntegralDomination` (Stacks 0CNZ) and
`AlgebraicGeometry.IntegralHasFinitePresentationLimit` (Stacks 09YZ), the input that
`AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` carries holds. Composing the two gives
Stacks 0DBT, and composing further with
`AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat` gives the flat case of Stacks
0ETR. -/
theorem fppfHasFiniteDomination (H₁ : FppfHasIntegralDomination.{u, v})
    (H₂ : IntegralHasFinitePresentationLimit.{u}) : FppfHasFiniteDomination.{u, v} := by
  intro I hI S hS hS' X f hf
  obtain ⟨S', g, hfin, hsurj, -, J, U, j, hj, hfac⟩ :=
    exists_finite_surjective_refinement_of_mem_fppfPrecoverage H₁ H₂ X f hf
  exact ⟨S', g, hfin, hsurj, J, U, j, hj, hfac⟩

end AlgebraicGeometry

end
