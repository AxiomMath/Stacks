module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Finiteness of the fibres of an étale chart above a point

Fix a scheme `S` and an algebraic space `X` over `S`, and let `x` be a point of `X`. The
fibre of an étale chart `φ : h_U ⟶ X` above `x` is the preimage of `x` under the induced
map on points. This file proves that finiteness of these fibres is detected by any one
jointly surjective family of étale charts: if some family of étale charts whose coproduct
map is locally surjective has finite fibres above `x`, then *every* étale chart from an
affine scheme has a finite fibre above `x`.

## Main results

* `AlgebraicGeometry.Space.exists_etaleCover_finite_fibre_iff_forall_affine_etale` is the
  equivalence of the two finiteness conditions.

The three facts about coverings that the proof turns on are stated separately, because the
same manoeuvre — pass to a cover, then pick the member through a given point — is wanted
wherever a condition at points of an algebraic space is checked on a chart:

* `AlgebraicGeometry.Space.exists_point_lift_of_sieve_mem`: a covering sieve has a member
  through which a given point of the underlying scheme factors.
* `AlgebraicGeometry.Space.exists_point_factor_of_cover`: the same for a covering family.
* `AlgebraicGeometry.Space.pullback_family_sieve_cover`: base changing a jointly locally
  surjective family along a representable map gives a covering family of the source.

## Implementation notes

An indexed family of charts is jointly surjective when the coproduct map of the represented
presheaves is locally surjective for the big fppf topology, which is how surjectivity of a
map onto an algebraic space is expressed throughout this development.

The implication from one family to all affine charts is local on the chart: an affine chart
is covered by the images of the fibre products of the chart with the members of the family,
each of which is covered by affine opens, and quasi-compactness of the affine chart cuts
the resulting cover down to a finite subfamily. The fibre over `x` of each piece is finite
because the piece maps to a member of the family with finite relative fibres, by
quasi-compactness and local quasi-finiteness of an étale morphism between affine schemes.

## References

* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Points of a representable presheaf and points of the representing scheme -/

section Points

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem pointsToScheme_symm_apply (V : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj V) :
    pointsToScheme B S hS V ((pointsEquivScheme B S hS V).symm z) = z :=
  (pointsEquivScheme B S hS V).apply_symm_apply z

private theorem injective_pointsMap_yoneda_of_injective {V W : BigFppfOver B S hS}
    (q : V ⟶ W) (hq : Function.Injective ((BigFppfOver.toScheme B S hS).map q).base) :
    Function.Injective (pointsMap B S hS (yoneda.obj V) (yoneda.map q)) := by
  intro a b hab
  refine injective_pointsToScheme B S hS V (hq ?_)
  rw [← pointsToScheme_pointsMap_yoneda, ← pointsToScheme_pointsMap_yoneda, hab]

private theorem finite_preimage_pointsMap_yoneda (V W : BigFppfOver B S hS) (q : V ⟶ W)
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    (hlqf : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map q))
    (x : points B S hS (yoneda.obj W)) :
    (pointsMap B S hS (yoneda.obj V) (yoneda.map q) ⁻¹' {x}).Finite := by
  let : QuasiCompact ((BigFppfOver.toScheme B S hS).map q) := hqc
  let : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map q) := hlqf
  have hscheme := ((BigFppfOver.toScheme B S hS).map q).finite_preimage_singleton
    (pointsToScheme B S hS W x)
  have heq : pointsMap B S hS (yoneda.obj V) (yoneda.map q) ⁻¹' {x} =
      pointsToScheme B S hS V ⁻¹'
        (((BigFppfOver.toScheme B S hS).map q).base ⁻¹' {pointsToScheme B S hS W x}) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← (injective_pointsToScheme B S hS W).eq_iff, pointsToScheme_pointsMap_yoneda]
  rw [heq]
  exact hscheme.preimage (injective_pointsToScheme B S hS V).injOn

end Points

/-! ### Set-level and site-level auxiliaries -/

private theorem finite_preimage_comp {A C D : Type*} (f : A → C) (g : C → D) (x : D)
    (hg : (g ⁻¹' {x}).Finite) (hf : ∀ y ∈ g ⁻¹' {x}, (f ⁻¹' {y}).Finite) :
    ((g ∘ f) ⁻¹' {x}).Finite := by
  simpa [Set.preimage_comp] using hg.preimage' hf

section Site

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every object of the big fppf category over `S` is covered, inside the site, by a family
of affine objects mapping to it by open immersions. -/
private theorem exists_affineOpenFamily_cover (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (q : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      Sieve.ofArrows V q ∈ BigFppfOver.topology B S hS T := by
  classical
  let T₀ : B.Schemes := T.left
  let O := B.inclusion.obj T₀
  let U := O.affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B T₀ U
  rcases hWU with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  let I := U.I₀
  let Ai : I → B.Schemes := fun i => B.obj (Scheme.size_lt_of_isOpenImmersion (U.f i) T₀.2)
  let mi : ∀ i, Ai i ⟶ T₀ := fun i =>
    B.inclusion.preimage (X := Ai i) (Y := T₀)
      (show B.inclusion.obj (Ai i) ⟶ B.inclusion.obj T₀ from U.f i)
  let V : I → BigFppfOver B S hS := fun i => Over.mk (mi i ≫ T.hom)
  let q : ∀ i, V i ⟶ T := fun i => by
    show Over.mk (mi i ≫ T.hom) ⟶ T
    exact Over.homMk (mi i)
  refine ⟨I, V, q, ?_, ?_, ?_⟩
  · intro i
    show IsAffine (U.X i)
    dsimp [U]
    exact isAffine_Spec _
  · intro i
    show _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (mi i))
    rw [show B.inclusion.map (mi i) = U.f i from
      B.inclusion.map_preimage
        (show B.inclusion.obj (Ai i) ⟶ B.inclusion.obj T₀ from U.f i)]
    exact U.map_prop i
  · have hbase : Sieve.ofArrows Ai mi ∈ B.topology T₀ := by
      have hgen : Sieve.generate W.presieve₀ ∈ B.topology T₀ :=
        Precoverage.generate_mem_toGrothendieck ⟨W, rfl, hW⟩
      apply B.topology.superset_covering ?_ hgen
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro j
      obtain ⟨e, he⟩ := hβ j
      rw [Sieve.mem_ofArrows_iff]
      refine ⟨β j, B.inclusion.preimage (X := W.X j) (Y := Ai (β j))
        (show B.inclusion.obj (W.X j) ⟶ B.inclusion.obj (Ai (β j)) from e.hom), ?_⟩
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
      show B.inclusion.map (W.f j) = e.hom ≫ U.f (β j)
      exact he.symm
    rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [V, q, T₀] using hbase

/-- A covering sieve of an object of the big fppf category over `S` has a member through
which any given point of the underlying scheme factors. -/
theorem exists_point_lift_of_sieve_mem {T : BigFppfOver B S hS} {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (V : BigFppfOver B S hS) (g : V ⟶ T) (z : (BigFppfOver.toScheme B S hS).obj V),
      R g ∧ (BigFppfOver.toScheme B S hS).map g z = y := by
  have hR' : Sieve.overEquiv T R ∈ B.topology T.left :=
    (GrothendieckTopology.mem_over_iff (J := B.topology) R).mp hR
  obtain ⟨E, hE, hER⟩ := exists_covering_refining_sieve B hR'
  let T₀ := (BigFppfOver.toScheme B S hS).obj T
  let C : Scheme.Cover Scheme.fppfPrecoverage T₀ := by
    have hfp : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage T₀ := by
      have hEfp := B.isFppfCovering_of_isCovering hE
      simpa [IsFppfCovering, Scheme.fppfPrecoverage, PreZeroHypercover.presieve₀_map, T₀]
        using hEfp
    exact ⟨E.map B.inclusion, hfp⟩
  have hcover := (Scheme.presieve₀_mem_precoverage_iff C.toPreZeroHypercover).mp C.mem₀
  obtain ⟨i, z, hz⟩ := hcover.1 y
  let V : BigFppfOver B S hS := Over.mk (E.f i ≫ T.hom)
  let g : V ⟶ T := Over.homMk (E.f i) (by simp [V])
  have hg : R g := (Sieve.overEquiv_iff R (E.f i)).mp (hER _ _ ⟨i⟩)
  exact ⟨V, g, z, hg, hz⟩

/-- A covering family of an object of the big fppf category over `S` has a member through
which any given point of the underlying scheme factors. -/
theorem exists_point_factor_of_cover {T : BigFppfOver B S hS} {I : Type u}
    (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ T)
    (hcover : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS T)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ i z, (BigFppfOver.toScheme B S hS).map (f i) z = y := by
  obtain ⟨W, g, z, hg, hz⟩ := exists_point_lift_of_sieve_mem B S hS hcover y
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
  refine ⟨i, (BigFppfOver.toScheme B S hS).map k z, ?_⟩
  show ((BigFppfOver.toScheme B S hS).map k ≫ (BigFppfOver.toScheme B S hS).map (f i)) z = y
  rw [← Functor.map_comp, hk.symm]
  exact hz

end Site

section Sieves

variable {C : Type (u + 1)} [Category.{u} C]

/-- Refining each member of a covering family by a covering family again gives a covering
family. -/
private theorem ofArrows_comp_cover (J : GrothendieckTopology C) {I : Type u} [Small.{u} I]
    {T : C} (P : I → C) (p : ∀ i, P i ⟶ T) (hP : Sieve.ofArrows P p ∈ J T)
    {K : I → Type u} [∀ i, Small.{u} (K i)] (W : ∀ i, K i → C) (q : ∀ i j, W i j ⟶ P i)
    (hW : ∀ i, Sieve.ofArrows (W i) (q i) ∈ J (P i)) :
    Sieve.ofArrows (fun ij : Σ i, K i => W ij.1 ij.2)
      (fun ij => q ij.1 ij.2 ≫ p ij.1) ∈ J T := by
  classical
  let R := Sieve.ofArrows (fun ij : Σ i, K i => W ij.1 ij.2)
    (fun ij => q ij.1 ij.2 ≫ p ij.1)
  apply J.transitive hP R
  intro Y f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff P p f).mp hf
  apply J.superset_covering ?_ (J.pullback_stable g (hW i))
  intro Z k hk
  obtain ⟨j, l, hl⟩ := (Sieve.mem_ofArrows_iff (W i) (q i) (k ≫ g)).mp hk
  show R (k ≫ (g ≫ p i))
  refine (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨⟨i, j⟩, l, ?_⟩
  simpa only [Category.assoc] using congrArg (fun f => f ≫ p i) hl

/-- A section of a coproduct of presheaves of types comes from one of the summands. -/
private theorem exists_summand_of_presheaf_sigma_section {I : Type u} [Small.{u} I]
    {F : I → Cᵒᵖ ⥤ Type u} (W : C) (s : (∐ F).obj (Opposite.op W)) :
    ∃ i t, (Sigma.ι F i).app (Opposite.op W) t = s := by
  classical
  let e := sigmaObjIso F (Opposite.op W) ≪≫
    CategoryTheory.Limits.Types.coproductIso (fun i => (F i).obj (Opposite.op W))
  let i := (e.hom s).1
  let t := (e.hom s).2
  have hz : e.hom s = ⟨i, t⟩ := Sigma.eta (e.hom s)
  refine ⟨i, t, ?_⟩
  have hι : e.hom ((Sigma.ι F i).app (Opposite.op W) t) = ⟨i, t⟩ := by
    show (((Sigma.ι F i).app (Opposite.op W) ≫ (sigmaObjIso F _).hom) ≫
      (CategoryTheory.Limits.Types.coproductIso _).hom) t = ⟨i, t⟩
    rw [ι_comp_sigmaObjIso_hom, CategoryTheory.Limits.Types.coproductIso_ι_comp_hom]
    rfl
  simpa using congrArg (fun z => e.inv z) (hι.trans hz.symm)

/-- Postcomposing a map out of a coproduct of presheaves postcomposes each component. -/
private theorem sigma_desc_comp_eq {I : Type u} [Small.{u} I] {F : I → Cᵒᵖ ⥤ Type u}
    {G H : Cᵒᵖ ⥤ Type u} (f : ∀ i, F i ⟶ G) (h : G ⟶ H) :
    Sigma.desc f ≫ h = Sigma.desc fun i => f i ≫ h :=
  Sigma.hom_ext _ _ fun i => by simp

variable [LocallySmall.{u} C]

/-- The coproduct of the represented presheaves of a covering family is locally surjective
onto the represented presheaf of the base. -/
private theorem locallySurjective_sigma_yoneda_of_cover (J : GrothendieckTopology C)
    {I : Type u} [Small.{u} I] {Y : I → C} {T : C} (f : ∀ i, Y i ⟶ T)
    (hcover : Sieve.ofArrows Y f ∈ J T) :
    Presheaf.IsLocallySurjective J (Sigma.desc (fun i => yoneda.map (f i))) := by
  have : HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ Type u) :=
    functorCategoryHasColimitsOfShape
  have hsmall : Presheaf.IsLocallySurjective J
      (Sigma.desc (fun i => shrinkYoneda.{u}.map (f i))) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map
      J f).mp hcover
  classical
  let e : (∐ fun i => shrinkYoneda.{u}.obj (Y i)) ≅ (∐ fun i => yoneda.obj (Y i)) :=
    Sigma.mapIso (fun i => shrinkYonedaIsoYoneda.app (Y i))
  have hfac : e.hom ≫ Sigma.desc (fun i => yoneda.map (f i)) =
      Sigma.desc (fun i => shrinkYoneda.map (f i)) ≫ (shrinkYonedaIsoYoneda.app T).hom := by
    apply Sigma.hom_ext
    intro i
    dsimp only [e]
    simp only [Sigma.ι_mapIso_hom_assoc, Sigma.ι_desc, Sigma.ι_desc_assoc]
    exact (shrinkYonedaIsoYoneda.hom.naturality (f i)).symm
  let : Presheaf.IsLocallySurjective J
      (Sigma.desc (fun i => shrinkYoneda.map (f i))) := hsmall
  have hcomp : Presheaf.IsLocallySurjective J
      (e.hom ≫ Sigma.desc (fun i => yoneda.map (f i))) := by
    rw [hfac]
    infer_instance
  have : Presheaf.IsLocallySurjective J e.hom := inferInstance
  exact (Presheaf.comp_isLocallySurjective_iff J e.hom
    (Sigma.desc (fun i => yoneda.map (f i)))).mp hcomp

/-- Refining each member of a jointly locally surjective family of maps from represented
presheaves by a covering family of its source leaves the family jointly locally
surjective. -/
private theorem locallySurjective_sigma_refinement (J : GrothendieckTopology C) {I : Type u}
    [Small.{u} I] (U : I → C) {X : Cᵒᵖ ⥤ Type u} (f : ∀ i, yoneda.obj (U i) ⟶ X)
    {K : I → Type u} [∀ i, Small.{u} (K i)] (V : ∀ i, K i → C) (q : ∀ i j, V i j ⟶ U i)
    (hcover : ∀ i, Sieve.ofArrows (V i) (q i) ∈ J (U i))
    (hlocal : Presheaf.IsLocallySurjective J (Sigma.desc f)) :
    Presheaf.IsLocallySurjective J
      (Sigma.desc fun ij : Σ i, K i => yoneda.map (q ij.1 ij.2) ≫ f ij.1) := by
  classical
  let F : I → Cᵒᵖ ⥤ Type u := fun i => yoneda.obj (U i)
  let G : (Σ i, K i) → Cᵒᵖ ⥤ Type u := fun ij => yoneda.obj (V ij.1 ij.2)
  let r : (∐ G) ⟶ (∐ F) := Sigma.desc fun ij =>
    yoneda.map (q ij.1 ij.2) ≫ Sigma.ι F ij.1
  have hr : Presheaf.IsLocallySurjective J r := by
    refine ⟨?_⟩
    intro T a
    obtain ⟨i, t, ht⟩ := exists_summand_of_presheaf_sigma_section (F := F) T a
    let ri : (∐ fun j => yoneda.obj (V i j)) ⟶ yoneda.obj (U i) :=
      Sigma.desc fun j => yoneda.map (q i j)
    have hri : Presheaf.IsLocallySurjective J ri :=
      locallySurjective_sigma_yoneda_of_cover J (q i) (hcover i)
    let := hri
    have himage := Presheaf.imageSieve_mem J ri t
    apply J.superset_covering ?_ himage
    intro W g hg
    obtain ⟨s, hs⟩ := hg
    obtain ⟨j, v, hv⟩ := exists_summand_of_presheaf_sigma_section
      (F := fun j => yoneda.obj (V i j)) W s
    have hriComp : Sigma.ι (fun j => yoneda.obj (V i j)) j ≫ ri = yoneda.map (q i j) := by
      simp [ri]
    have hriFun : ri.app (Opposite.op W) ∘
          (Sigma.ι (fun j => yoneda.obj (V i j)) j).app (Opposite.op W) =
        (yoneda.map (q i j)).app (Opposite.op W) := by
      funext v
      show ri.app (Opposite.op W)
          ((Sigma.ι (fun j => yoneda.obj (V i j)) j).app (Opposite.op W) v) =
        (yoneda.map (q i j)).app (Opposite.op W) v
      have hh := congrArg (fun a => a.app (Opposite.op W) v) hriComp
      simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using hh
    have hqv : (yoneda.map (q i j)).app (Opposite.op W) v =
        (yoneda.obj (U i)).map g.op t := by
      calc
        (yoneda.map (q i j)).app (Opposite.op W) v = ri.app (Opposite.op W)
            ((Sigma.ι (fun j => yoneda.obj (V i j)) j).app (Opposite.op W) v) :=
              (congrFun hriFun v).symm
        _ = ri.app (Opposite.op W) s := congrArg (ri.app (Opposite.op W)) hv
        _ = (yoneda.obj (U i)).map g.op t := hs
    have hrComp : Sigma.ι G ⟨i, j⟩ ≫ r = yoneda.map (q i j) ≫ Sigma.ι F i := by
      simp [r]
    have hrFun : r.app (Opposite.op W) ∘ (Sigma.ι G ⟨i, j⟩).app (Opposite.op W) =
        (Sigma.ι F i).app (Opposite.op W) ∘
          (yoneda.map (q i j)).app (Opposite.op W) := by
      funext v
      show r.app (Opposite.op W) ((Sigma.ι G ⟨i, j⟩).app (Opposite.op W) v) =
        (Sigma.ι F i).app (Opposite.op W) ((yoneda.map (q i j)).app (Opposite.op W) v)
      have hh := congrArg (fun a => a.app (Opposite.op W) v) hrComp
      simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using hh
    refine ⟨(Sigma.ι G ⟨i, j⟩).app (Opposite.op W) v, ?_⟩
    calc
      r.app (Opposite.op W) ((Sigma.ι G ⟨i, j⟩).app (Opposite.op W) v) =
          (Sigma.ι F i).app (Opposite.op W)
            ((yoneda.map (q i j)).app (Opposite.op W) v) := congrFun hrFun v
      _ = (∐ F).map g.op ((Sigma.ι F i).app (Opposite.op T) t) := by
            rw [hqv]
            exact NatTrans.naturality_apply (Sigma.ι F i) g.op t
      _ = (∐ F).map g.op a := by rw [← ht]
  let := hr
  let := hlocal
  have hcomp : Presheaf.IsLocallySurjective J (r ≫ Sigma.desc f) := inferInstance
  have hfactor : r ≫ Sigma.desc f =
      Sigma.desc (fun ij : Σ i, K i => yoneda.map (q ij.1 ij.2) ≫ f ij.1) := by
    rw [sigma_desc_comp_eq]
    simp
    rfl
  rwa [hfactor] at hcomp

end Sieves

section Pullbacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Base changing a jointly locally surjective family of maps into `X` along a
representable map `a : h_U ⟶ X` gives a covering family of `U`. -/
theorem pullback_family_sieve_cover {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) {I : Type u} [Small.{u} I]
    (V : I → BigFppfOver B S hS) (b : ∀ i, yoneda.obj (V i) ⟶ X)
    (hlocal : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc b))
    (hrep : yoneda.relativelyRepresentable a) :
    Sieve.ofArrows (fun i => hrep.pullback (b i)) (fun i => hrep.fst' (b i)) ∈
      BigFppfOver.topology B S hS U := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F : I → Cᵒᵖ ⥤ Type u := fun i => yoneda.obj (V i)
  let f : (∐ F) ⟶ X := Sigma.desc b
  let s : X.obj (Opposite.op U) := a.app (Opposite.op U) (𝟙 U)
  have himage : Presheaf.imageSieve f s ∈ J U := by
    let := hlocal
    exact Presheaf.imageSieve_mem J f s
  apply J.superset_covering ?_ himage
  intro W g hg
  rw [Sieve.mem_ofArrows_iff]
  obtain ⟨t, ht⟩ := hg
  obtain ⟨i, ti, hti⟩ := exists_summand_of_presheaf_sigma_section (F := F) W t
  let m : W ⟶ V i := yoneda.preimage (yonedaEquiv.symm ti)
  have hvalue : (b i).app (Opposite.op W) ti = (a.app (Opposite.op W)) g := by
    rw [← hti] at ht
    change ((Sigma.ι F i ≫ f).app (Opposite.op W) ti) = _ at ht
    rw [Sigma.ι_desc] at ht
    simpa [s] using ht.trans (NatTrans.naturality_apply a g.op (𝟙 U)).symm
  have hcompat : yoneda.map g ≫ a = yoneda.map m ≫ b i := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, m, yoneda.map_preimage,
      Equiv.apply_symm_apply] using hvalue.symm
  exact ⟨i, hrep.lift' g m hcompat, (hrep.lift'_fst g m hcompat).symm⟩

end Pullbacks

/-! ### Étale charts -/

/-- The class of morphisms of `BigFppfOver B S hS` whose underlying morphism of schemes is
étale is stable under base change. -/
instance etale_inverseImage_isStableUnderBaseChange (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun sq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale.{u})
    (sq.map (BigFppfOver.toScheme B S hS)) hg⟩


/-- Precomposing an étale map of presheaves with an open immersion of representing objects
gives an étale map of presheaves. -/
private theorem presheaf_etale_yoneda_map_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T V : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : V ⟶ T)
    (hq : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q))
    (φ : yoneda.obj T ⟶ X) (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map q ≫ φ) := by
  let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : Pe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let : (MorphismProperty.presheaf Pe).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Pe
  refine MorphismProperty.comp_mem _ _ _ ?_ hφ
  apply (MorphismProperty.relative_map_iff (P := Pe)).2
  show Etale ((BigFppfOver.toScheme B S hS).map q)
  let := hq
  infer_instance

/-! ### The equivalence -/

/-- For a point `x` of an algebraic space `X` over `S`, the following are equivalent: some
jointly locally surjective family of étale charts of `X` has finite fibres above `x`, and every
étale chart of `X` by an affine scheme has a finite fibre above `x`. -/
@[stacks 03JS]
theorem exists_etaleCover_finite_fibre_iff_forall_affine_etale (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) :
    (∃ (I : Type u) (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ X),
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) ∧
      ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) (φ i) ∧
        (pointsMap B S hS (yoneda.obj (U i)) (φ i) ⁻¹' {x}).Finite) ↔
    (∀ U : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ φ : yoneda.obj U ⟶ X, (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) φ →
        (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}).Finite) := by
  constructor
  · intro hcover U hAffine φ hφ
    classical
    obtain ⟨I₀, U₀, φ₀, hlocal₀, hrest₀⟩ := hcover
    let J := BigFppfOver.topology B S hS
    let C := BigFppfOver B S hS
    let : HasTerminal C := inferInstance
    let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
    let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    let : (MorphismProperty.presheaf Pe).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange Pe
    choose Iᵢ Uᵢ qᵢ hAffineᵢ hOpenᵢ hCoverᵢ using fun i =>
      exists_affineOpenFamily_cover B S hS (U₀ i)
    let I := Σ i, Iᵢ i
    let Ui (k : I) := Uᵢ k.1 k.2
    let oi (k : I) := qᵢ k.1 k.2
    let φi (k : I) := yoneda.map (oi k) ≫ φ₀ k.1
    have hlocal : Presheaf.IsLocallySurjective J (Sigma.desc φi) :=
      locallySurjective_sigma_refinement J U₀ φ₀ Uᵢ qᵢ hCoverᵢ hlocal₀
    have hrest (k : I) : (MorphismProperty.presheaf Pe) (φi k) ∧
        (pointsMap B S hS (yoneda.obj (Ui k)) (φi k) ⁻¹' {x}).Finite := by
      have hφi : (MorphismProperty.presheaf Pe) (φi k) :=
        presheaf_etale_yoneda_map_comp B S hS (oi k) (hOpenᵢ k.1 k.2) _ (hrest₀ k.1).1
      have hinj := injective_pointsMap_yoneda_of_injective B S hS (oi k)
        (by
          let := hOpenᵢ k.1 k.2
          exact ((BigFppfOver.toScheme B S hS).map (oi k)).isOpenEmbedding.injective)
      have heq : pointsMap B S hS (yoneda.obj (Ui k)) (φi k) ⁻¹' {x} =
          pointsMap B S hS (yoneda.obj (Ui k)) (yoneda.map (oi k)) ⁻¹'
            (pointsMap B S hS (yoneda.obj (U₀ k.1)) (φ₀ k.1) ⁻¹' {x}) := by
        rw [← Set.preimage_comp, ← pointsMap_comp]
      refine ⟨hφi, ?_⟩
      rw [heq]
      exact (hrest₀ k.1).2.preimage hinj.injOn
    have hφrep : yoneda.relativelyRepresentable φ :=
      (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).mp
        hX.diagonal_representable φ
    have hpbCover := pullback_family_sieve_cover B S hS φ Ui φi hlocal hφrep
    choose Ki Wi qi hAffineI hOpenI hCoverI using fun i =>
      exists_affineOpenFamily_cover B S hS (hφrep.pullback (φi i))
    let p (i : I) := hφrep.fst' (φi i)
    let s (i : I) := hφrep.snd (φi i)
    have hpEtale (i : I) : (MorphismProperty.presheaf Pe) (yoneda.map (p i)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (hφrep.isPullback' (φi i)).flip (hrest i).1
    have hsEtale (i : I) : (MorphismProperty.presheaf Pe) (yoneda.map (s i)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (hφrep.isPullback' (φi i)) hφ
    let K := Σ i, Ki i
    let W (k : K) := Wi k.1 k.2
    let g (k : K) : W k ⟶ U := qi k.1 k.2 ≫ p k.1
    let d (k : K) : W k ⟶ Ui k.1 := qi k.1 k.2 ≫ s k.1
    have hCoverW : Sieve.ofArrows W g ∈ J U :=
      ofArrows_comp_cover J (fun i => hφrep.pullback (φi i)) p hpbCover Wi qi hCoverI
    have hPointCover (y : (BigFppfOver.toScheme B S hS).obj U) :
        ∃ k z, (BigFppfOver.toScheme B S hS).map (g k) z = y :=
      exists_point_factor_of_cover B S hS W g hCoverW y
    have hPointOpen (k : K) :
        IsOpen (Set.range (((BigFppfOver.toScheme B S hS).map (g k)).base)) := by
      have hgEtale : Etale ((BigFppfOver.toScheme B S hS).map (g k)) :=
        (MorphismProperty.relative_map_iff (P := Pe)).1
          (presheaf_etale_yoneda_map_comp B S hS (qi k.1 k.2) (hOpenI k.1 k.2) _ (hpEtale k.1))
      exact (Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map (g k))).isOpen_range
    let images (k : K) : Set ((BigFppfOver.toScheme B S hS).obj U) :=
      Set.range (((BigFppfOver.toScheme B S hS).map (g k)).base)
    have himagesCover : Set.univ ⊆ ⋃ k, images k := by
      intro y _
      obtain ⟨k, z, hz⟩ := hPointCover y
      exact Set.mem_iUnion.mpr ⟨k, ⟨z, hz⟩⟩
    let : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hAffine
    let : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
    have hcompact : IsCompact (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj U)) :=
      isCompact_univ
    obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover images hPointOpen himagesCover
    have hEtaleD (k : K) : Etale ((BigFppfOver.toScheme B S hS).map (d k)) :=
      (MorphismProperty.relative_map_iff (P := Pe)).1
        (presheaf_etale_yoneda_map_comp B S hS (qi k.1 k.2) (hOpenI k.1 k.2) _ (hsEtale k.1))
    have hqcD (k : K) :
        QuasiCompact ((BigFppfOver.toScheme B S hS).map (d k)) := by
      let : IsAffine ((BigFppfOver.toScheme B S hS).obj (W k)) := hAffineI k.1 k.2
      let : IsAffine ((BigFppfOver.toScheme B S hS).obj (Ui k.1)) := hAffineᵢ k.1.1 k.1.2
      let : CompactSpace ((BigFppfOver.toScheme B S hS).obj (W k)) := inferInstance
      let : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (Ui k.1)) :=
        inferInstance
      infer_instance
    let pointMapU (k : K) := pointsMap B S hS (yoneda.obj (W k)) (yoneda.map (g k))
    let pointMapD (k : K) := pointsMap B S hS (yoneda.obj (W k)) (yoneda.map (d k))
    let pointMapI (k : K) := pointsMap B S hS (yoneda.obj (Ui k.1)) (φi k.1)
    have hArrow (k : K) : yoneda.map (d k) ≫ φi k.1 = yoneda.map (g k) ≫ φ := by
      have hpb := (hφrep.isPullback' (φi k.1)).w
      change yoneda.map (p k.1) ≫ φ = yoneda.map (s k.1) ≫ φi k.1 at hpb
      dsimp [d, g]
      simp only [Functor.map_comp, Category.assoc, hpb]
    let fiberW (k : K) := (pointMapI k ∘ pointMapD k) ⁻¹' {x}
    have hfiniteD (k : K) (y : points B S hS (yoneda.obj (Ui k.1))) :
        (pointMapD k ⁻¹' {y}).Finite :=
      finite_preimage_pointsMap_yoneda B S hS (W k) (Ui k.1) (d k) (hqcD k)
        (by
          let := hEtaleD k
          exact (locallyQuasiFinite_of_etale _).2) y
    have hfiniteW (k : K) : (fiberW k).Finite :=
      finite_preimage_comp (pointMapD k) (pointMapI k) x (hrest k.1).2
        (fun y _ => hfiniteD k y)
    let mappedFibers : Set (points B S hS (yoneda.obj U)) :=
      ⋃ k ∈ (t : Set K), pointMapU k '' fiberW k
    have hmappedFinite : mappedFibers.Finite := by
      dsimp [mappedFibers]
      exact t.finite_toSet.biUnion (fun k _ => (hfiniteW k).image (pointMapU k))
    have hfiberSubset : pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x} ⊆ mappedFibers := by
      intro y hy
      have hcov : pointsToScheme B S hS U y ∈ ⋃ k ∈ (t : Set K), images k :=
        ht (Set.mem_univ _)
      obtain ⟨k, hk, z, hzy⟩ := Set.mem_iUnion₂.mp hcov
      let z' := (pointsEquivScheme B S hS (W k)).symm z
      have hEq : pointMapU k z' = y := by
        refine injective_pointsToScheme B S hS U ?_
        show pointsToScheme B S hS U
            (pointsMap B S hS (yoneda.obj (W k)) (yoneda.map (g k)) z') =
          pointsToScheme B S hS U y
        rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_symm_apply]
        exact hzy
      have hzfiber : z' ∈ fiberW k := by
        change pointsMap B S hS _ (φi k.1) (pointsMap B S hS _ (yoneda.map (d k)) z') = x
        rw [← pointsMap_comp_apply, hArrow, pointsMap_comp_apply]
        exact (congrArg (pointsMap B S hS (yoneda.obj U) φ) hEq).trans hy
      exact Set.mem_iUnion₂.mpr ⟨k, hk, z', hzfiber, hEq⟩
    exact hmappedFinite.subset hfiberSubset
  · intro hfinite
    obtain ⟨T, a, haSurj, haEtale⟩ := hX.exists_atlas
    obtain ⟨I, V, q, hAffine, hOpen, hCover⟩ := exists_affineOpenFamily_cover B S hS T
    let φ : ∀ i, yoneda.obj (V i) ⟶ X := fun i => yoneda.map (q i) ≫ a
    let Pe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    have hφEtale (i : I) : (MorphismProperty.presheaf Pe) (φ i) :=
      presheaf_etale_yoneda_map_comp B S hS (q i) (hOpen i) a haEtale
    refine ⟨I, V, φ, ?_, fun i => ⟨hφEtale i, hfinite (V i) (hAffine i) (φ i) (hφEtale i)⟩⟩
    let J := BigFppfOver.topology B S hS
    have hqLocal : Presheaf.IsLocallySurjective J
        (Sigma.desc (fun i => yoneda.map (q i))) :=
      locallySurjective_sigma_yoneda_of_cover J q hCover
    have haLocal : Presheaf.IsLocallySurjective J a :=
      isLocallySurjective_of_surjective_etale B S hS a haSurj haEtale
    let : Presheaf.IsLocallySurjective J (Sigma.desc (fun i => yoneda.map (q i))) := hqLocal
    let : Presheaf.IsLocallySurjective J a := haLocal
    have hcomp : Presheaf.IsLocallySurjective J
        (Sigma.desc (fun i => yoneda.map (q i)) ≫ a) := inferInstance
    show Presheaf.IsLocallySurjective J (Sigma.desc (fun i => yoneda.map (q i) ≫ a))
    convert hcomp using 1
    apply Sigma.hom_ext
    intro i
    simp

end AlgebraicGeometry.Space

end
