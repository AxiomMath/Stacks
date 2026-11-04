module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Zariski coverings of an algebraic space by subspaces with affine étale atlases

Every algebraic space over a scheme `S` admits a Zariski covering by open subspaces, each of
which has a surjective étale atlas from an affine scheme and maps into an affine open of the
base.

Tag 03FX supplies a surjective étale atlas `U ⟶ F` whose underlying scheme is a disjoint
union of affine schemes `Y i`, each lying over an affine open of `S`. Each summand gives an
étale chart of `F`, open on points, so its image is an open subspace of `F` by Tag 03BZ; the
summands cover `|F|` because the atlas is surjective on points, and the chart factors through
its image as a surjective étale morphism by Tag 06NF.

## Main results

* `AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas` is **Stacks 03FY**.

## References

* [Stacks Project, Tag 03FY](https://stacks.math.columbia.edu/tag/03FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **Stacks 03FY.** An algebraic space over `S` has a Zariski covering by open subspaces,
each of which admits a surjective étale atlas from an affine scheme and maps into an affine
open of `S`. -/
@[stacks 03FY]
theorem exists_zariski_cover_affine_etale_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    ∃ (I : Type u) (X : I → Subfunctor F),
      IsZariskiCover B S hS I X ∧
      ∀ i, ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ (X i).toFunctor) (V : S.Opens),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f ∧
        (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f ∧
        IsAffineOpen V ∧
        ∀ (T : BigFppfOver B S hS) (_ : (X i).toFunctor.obj (Opposite.op T))
          (t : (BigFppfOver.toScheme B S hS).obj T), (B.inclusion.map T.hom) t ∈ V := by
  classical
  set G := BigFppfOver.toScheme B S hS
  obtain ⟨U, f, I, Y, e, hsurj, hetale, hYaff, hbase⟩ :=
    exists_etale_surjective_coproduct_affine_cover B S hS F hF
  -- Each summand of the atlas is an object of the site over `S`, étale over `F`.
  have hcoprod : B.Contains (∐ Y) := by
    show (∐ Y).size < B.cutoff
    rw [Scheme.size_congr e]
    exact U.left.property
  have hYsmall (i : I) : B.Contains (Y i) :=
    Scheme.size_lt_of_isOpenImmersion (Sigma.ι Y i) hcoprod
  set giMap : ∀ i, B.obj (hYsmall i) ⟶ U.left := fun i ↦
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hYsmall i)) ⟶ B.inclusion.obj U.left from
        Sigma.ι Y i ≫ e.hom)
  set Ui : I → BigFppfOver B S hS := fun i ↦ Over.mk (giMap i ≫ U.hom)
  set gi : ∀ i, Ui i ⟶ U := fun i ↦ Over.homMk (giMap i)
  have hmapgi (i : I) : G.map (gi i) = Sigma.ι Y i ≫ e.hom := B.inclusion.map_preimage _
  have hfiEtale (i : I) : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) G).presheaf (yoneda.map (gi i) ≫ f) :=
    etale_comp_of_scheme B S hS (gi i) f (by rw [hmapgi]; infer_instance) hetale
  have hfiOpen (i : I) :
      IsOpen (Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (gi i) ≫ f))) := by
    rw [← Set.image_univ]
    exact isOpenMap_pointsMap_of_etale B S hS hF (Ui i) _ (hfiEtale i) _ isOpen_univ
  -- The image of each summand is an open subspace, with that image as its point set.
  set X : I → Subfunctor F := fun i ↦ openSubspaceOfPoints B S hS F
    (Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (gi i) ≫ f)))
  have hXopen (i : I) : IsOpenSubspace B S hS (X i) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hF _ (hfiOpen i)
  have hXrange (i : I) : Set.range (pointsMap B S hS (X i).toFunctor (X i).ι) =
      Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (gi i) ≫ f)) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  refine ⟨I, X, ?_, ?_⟩
  · -- The summands cover the point space, since the atlas does and each point of the atlas
    -- lies on some summand.
    rw [isZariskiCover_iff_iUnion_points B S hS F hF I X hXopen]
    refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨p, hp⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U f).mp hsurj x
    have htop : (⨆ i : I, (Sigma.ι Y i).opensRange) = ⊤ := (sigmaOpenCover Y).iSup_opensRange
    have hmem : e.inv (pointsToScheme B S hS U p) ∈ ⨆ i : I, (Sigma.ι Y i).opensRange := by
      rw [htop]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hi
    obtain ⟨q, hq⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS (gi i) p
      ⟨y, by rw [hmapgi]; change e.hom ((Sigma.ι Y i) y) = _; rw [hy]; simp⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hXrange i]
    exact ⟨q, by rw [pointsMap_comp_apply, hq, hp]⟩
  · -- Each summand factors through its image as a surjective étale atlas of that image.
    intro i
    obtain ⟨V, hV, hmapV⟩ := hbase i
    set f' := factorThroughEtaleImage B S hS hF (Ui i) (yoneda.map (gi i) ≫ f)
      (X i) (hXopen i) (hXrange i)
    have hfactor := factorThroughEtaleImage_comp B S hS hF (Ui i) (yoneda.map (gi i) ≫ f)
      (X i) (hXopen i) (hXrange i)
    have hf'surj := surjective_factor_through_etaleImage B S hS (Ui i)
      (yoneda.map (gi i) ≫ f) (X i) (hXopen i) (hXrange i) f' hfactor
    refine ⟨Ui i, f', V, hYaff i, hf'surj,
      etale_factor_through_etaleImage B S hS (Ui i) (yoneda.map (gi i) ≫ f) (hfiEtale i)
        (X i) (hXopen i) f' hfactor, hV, ?_⟩
    -- The structure morphism of a test object of the image factors through the summand.
    intro T x t
    set g : yoneda.obj T ⟶ (X i).toFunctor := yonedaEquiv.symm x
    set W := hf'surj.rep.pullback g
    set q : W ⟶ T := hf'surj.rep.snd g
    set a : W ⟶ Ui i := yoneda.preimage (hf'surj.rep.fst g)
    have hqsurj : Surjective (G.map q) := hf'surj.property_snd g
    obtain ⟨w, hw⟩ := (G.map q).surjective t
    have hbaseOf {P Q : BigFppfOver B S hS} (m : P ⟶ Q) :
        B.inclusion.map m.left ≫ B.inclusion.map Q.hom = B.inclusion.map P.hom := by
      rw [← Functor.map_comp]
      exact congrArg B.inclusion.map (Over.w m)
    have hUibase : B.inclusion.map (Ui i).hom =
        Sigma.ι Y i ≫ e.hom ≫ B.inclusion.map U.hom := by
      show B.inclusion.map (giMap i ≫ U.hom) = _
      rw [Functor.map_comp, B.inclusion.map_preimage, Category.assoc]
    have key : (B.inclusion.map T.hom) t = (B.inclusion.map (Ui i).hom) ((G.map a) w) :=
      calc (B.inclusion.map T.hom) t
          = (B.inclusion.map T.hom) ((G.map q) w) := by rw [hw]
        _ = (B.inclusion.map W.hom) w := by rw [← hbaseOf q]; rfl
        _ = (B.inclusion.map (Ui i).hom) ((G.map a) w) := by rw [← hbaseOf a]; rfl
    rw [key, hUibase]
    exact hmapV _

end AlgebraicGeometry.Space

end
