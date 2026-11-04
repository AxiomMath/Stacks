module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Glueing a sheaf on the big fppf site from representable open subfunctors

This file carries out the glueing step of Tag 01JJ *inside* the big fppf category over a
scheme `S`, for a family of charts whose index type and whose sizes are bounded by the size
cutoff of the site.

## Main definitions

* `AlgebraicGeometry.openImmersionOver`: the property of a morphism of the big fppf category
  over `S` that the underlying morphism of schemes is an open immersion, i.e. the inverse
  image of `AlgebraicGeometry.IsOpenImmersion` along
  `AlgebraicGeometry.BigFppfOver.toScheme`.
* `AlgebraicGeometry.openChartGlueData`: the glue data, in the big fppf category over
  `S`, attached to a family of relatively representable open immersions
  `f i : yoneda.obj (X i) ⟶ F`; its `V (i, j)` is the represented fibre product
  `X i ×_F X j`.
* `AlgebraicGeometry.openChartSchemeGlueData`: the same glue data pushed to schemes,
  where the glued object is produced by `AlgebraicGeometry.Scheme.GlueData`.

## Main results

* `CategoryTheory.GlueData.oneHypercover`: glue data whose family of inclusions generates a
  covering sieve and whose `V (i, j)` really are the fibre products of the inclusions is a
  one-hypercover of the glued object.
* `AlgebraicGeometry.isRepresentable_of_openCharts`: a sheaf on the big fppf site over
  `S` covered by a family of representable open subfunctors, indexed by a type of
  cardinality below the cutoff and with sizes uniformly bounded below the cutoff, is
  representable.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

/-- Glue data in a site whose inclusions generate a covering sieve and whose `V (i, j)` are the
fibre products of the inclusions assemble into a one-hypercover of the glued object, with
`I₁ i₁ i₂` a single point and `V (i₁, i₂)` the corresponding object. -/
noncomputable def GlueData.oneHypercover {C : Type*} [Category.{v} C]
    {J : GrothendieckTopology C} [HasPullbacks C] (D : CategoryTheory.GlueData C)
    [HasMulticoequalizer D.diagram]
    (hcover : Sieve.ofArrows D.U D.ι ∈ J D.glued)
    (hlim : ∀ i j, IsLimit (D.vPullbackCone i j)) : J.OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ _ := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, CategoryTheory.GlueData.glue_condition]
  mem₀ := hcover
  mem₁ i₁ i₂ W p₁ p₂ fac := by
    refine J.superset_covering (fun T g _ ↦ ?_) (J.top_mem _)
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (hlim i₁ i₂)
      (g ≫ p₁) (g ≫ p₂) (by simpa using g ≫= fac)
    exact ⟨PUnit.unit, φ, h₁.symm, h₂.symm⟩

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property of a morphism of the big fppf category over `S` of being an open immersion of
schemes. -/
abbrev openImmersionOver : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

variable {B S hS}

/-- An open immersion of the big fppf category over `S` is a monomorphism. -/
lemma openImmersionOver_le_monomorphisms :
    openImmersionOver B S hS ≤ MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
  intro V W k hk
  have _ : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map k) := hk
  exact Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) (f := k) inferInstance

section GlueData

variable {I : Type u} {X : I → BigFppfOver B S hS}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, yoneda.obj (X i) ⟶ F}

/-- The glue data in the big fppf category over `S` attached to a family of relatively
representable open immersions into a presheaf: `U i` is `X i` and `V (i, j)` is the represented
fibre product `X i ×_F X j`. -/
noncomputable def openChartGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) :
    CategoryTheory.GlueData (BigFppfOver B S hS) where
  J := I
  U := X
  V := fun (i, j) => (hf i).rep.pullback (f j)
  f := fun i j => (hf i).rep.fst' (f j)
  f_mono := fun i j =>
    openImmersionOver_le_monomorphisms _
      ((hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip)
  f_id := fun i =>
    MorphismProperty.isIso_fst'_self openImmersionOver_le_monomorphisms (hf i)
  t := fun i j => (hf i).rep.symmetry (hf j).rep
  t_id := fun i => by
    apply (hf i).rep.hom_ext' <;>
      simp [MorphismProperty.fst'_self_eq_snd openImmersionOver_le_monomorphisms (hf i)]
  t' := fun i j k => Functor.relativelyRepresentable.lift₃ _ _ _
    (Functor.relativelyRepresentable.pullback₃.p₂ _ _ _)
    (Functor.relativelyRepresentable.pullback₃.p₃ _ _ _)
    (Functor.relativelyRepresentable.pullback₃.p₁ _ _ _)
    ((Functor.relativelyRepresentable.pullback₃.map_p₂_comp _ _ _).trans
      (Functor.relativelyRepresentable.pullback₃.map_p₃_comp _ _ _).symm)
    ((Functor.relativelyRepresentable.pullback₃.map_p₂_comp _ _ _).trans
      (Functor.relativelyRepresentable.pullback₃.map_p₁_comp _ _ _).symm)
  t_fac := fun i j k => (hf j).rep.hom_ext'
    ((Category.assoc _ _ _).trans
      ((_ ≫= Functor.relativelyRepresentable.pullback₃.snd_fst'_eq_p₁ ..).trans
        ((Functor.relativelyRepresentable.lift₃_p₁ ..).trans
          ((Category.assoc _ _ _).trans
            (_ ≫= Functor.relativelyRepresentable.symmetry_fst ..)).symm)))
    ((Category.assoc _ _ _).trans
      ((_ ≫= Functor.relativelyRepresentable.pullback₃.snd_snd_eq_p₃ ..).trans
        ((Functor.relativelyRepresentable.lift₃_p₃ ..).trans
          ((Category.assoc _ _ _).trans
            (_ ≫= Functor.relativelyRepresentable.symmetry_snd ..)).symm)))
  cocycle := fun i j k => Functor.relativelyRepresentable.pullback₃.hom_ext
    ((Category.assoc _ _ _).trans
      ((_ ≫= Category.assoc _ _ _).trans
        ((_ ≫= _ ≫= Functor.relativelyRepresentable.lift₃_p₁ ..).trans
          ((_ ≫= Functor.relativelyRepresentable.lift₃_p₂ ..).trans
            ((Functor.relativelyRepresentable.lift₃_p₃ ..).trans
              (Category.id_comp _).symm)))))
    ((Category.assoc _ _ _).trans
      ((_ ≫= Category.assoc _ _ _).trans
        ((_ ≫= _ ≫= Functor.relativelyRepresentable.lift₃_p₂ ..).trans
          ((_ ≫= Functor.relativelyRepresentable.lift₃_p₃ ..).trans
            ((Functor.relativelyRepresentable.lift₃_p₁ ..).trans
              (Category.id_comp _).symm)))))
    ((Category.assoc _ _ _).trans
      ((_ ≫= Category.assoc _ _ _).trans
        ((_ ≫= _ ≫= Functor.relativelyRepresentable.lift₃_p₃ ..).trans
          ((_ ≫= Functor.relativelyRepresentable.lift₃_p₁ ..).trans
            ((Functor.relativelyRepresentable.lift₃_p₂ ..).trans
              (Category.id_comp _).symm)))))

/-- The glue data of `AlgebraicGeometry.openChartGlueData` pushed forward to schemes. Its glued
object exists unconditionally, as a scheme. -/
noncomputable def openChartSchemeGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) : Scheme.GlueData.{u} where
  toGlueData := (openChartGlueData hf).mapGlueData (BigFppfOver.toScheme B S hS)
  f_open := fun i j => (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip

/-- The underlying glue data of `AlgebraicGeometry.openChartSchemeGlueData` is the image of
`AlgebraicGeometry.openChartGlueData` under the forgetful functor to schemes. -/
@[simp]
lemma openChartSchemeGlueData_toGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) :
    (openChartSchemeGlueData hf).toGlueData =
      (openChartGlueData hf).mapGlueData (BigFppfOver.toScheme B S hS) :=
  rfl

/-- The glue data of `AlgebraicGeometry.openChartGlueData` pushed to schemes has a glued object. -/
theorem hasMulticoequalizer_mapGlueData_toScheme
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) :
    HasColimit
      ((openChartGlueData hf).mapGlueData (BigFppfOver.toScheme B S hS)).diagram.multispan :=
  inferInstanceAs (HasMulticoequalizer (openChartSchemeGlueData hf).toGlueData.diagram)

/-- The glued scheme of `AlgebraicGeometry.openChartSchemeGlueData` has size below the cutoff of
the site, provided the index type does and the charts are uniformly bounded. -/
theorem openChartSchemeGlueData_size_lt_cutoff
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) (hI : #I < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    (openChartSchemeGlueData hf).glued.size < B.cutoff := by
  set D := openChartSchemeGlueData hf with hD
  have hJ : D.J = I := rfl
  by_cases hEmpty : IsEmpty I
  · have hpt : IsEmpty D.glued := ⟨fun x => by
      obtain ⟨i, -, -⟩ := D.ι_jointly_surjective x
      exact hEmpty.false (hJ ▸ i)⟩
    refine lt_of_le_of_lt (?_ : D.glued.size ≤ ℵ₀) B.aleph0_lt_cutoff
    unfold Scheme.size
    refine max_le le_rfl (max_le ?_ (ciSup_le' fun V => ?_))
    · have hsub : Subsingleton D.glued.affineOpens :=
        ⟨fun V W => Subtype.ext (TopologicalSpace.Opens.ext
          (Set.eq_of_subset_of_subset (fun x _ => (hpt.false x).elim)
            (fun x _ => (hpt.false x).elim)))⟩
      exact (le_one_iff_subsingleton.mpr hsub).trans one_le_aleph0
    · have hsub : Subsingleton Γ(D.glued, V.1) := inferInstance
      exact (le_one_iff_subsingleton.mpr hsub).trans one_le_aleph0
  · have hne : Nonempty I := not_isEmpty_iff.mp hEmpty
    have _ : Nonempty D.J := hJ ▸ hne
    have hsize : D.glued.size ≤ max #D.J (⨆ i : D.J, (D.U i).size) := by
      refine le_of_le_of_eq (Scheme.size_le_of_iSup_eq_top
        (fun i => (D.ι i).opensRange) D.openCover.iSup_opensRange) ?_
      congr 2
      funext i
      simpa only [Scheme.Hom.image_top_eq_opensRange] using
        (Scheme.size_congr ((D.U i).topIso.symm ≪≫ (D.ι i).isoImage ⊤)).symm
    exact hsize.trans_lt (max_lt hI ((ciSup_le' hcharts).trans_lt hμ))

/-- The multispan diagram of the glue data has a colimit after passing to schemes: it is the glued
scheme. -/
theorem hasColimit_openChartGlueData_comp
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) :
    HasColimit ((openChartGlueData hf).diagram.multispan ⋙
      BigFppfOver.toScheme B S hS) :=
  @hasColimit_of_iso _ _ _ _ _ _ (hasMulticoequalizer_mapGlueData_toScheme hf)
    ((openChartGlueData hf).diagramIso (BigFppfOver.toScheme B S hS))

/-- The forgetful functor from the big fppf category over `S` to schemes creates a colimit whose
value in schemes is contained in the site. -/
@[instance_reducible]
noncomputable def createsColimit_toScheme {K : Type*} [Category K]
    (E : K ⥤ BigFppfOver B S hS) [HasColimit (E ⋙ BigFppfOver.toScheme B S hS)]
    (h : B.Contains (colimit (E ⋙ BigFppfOver.toScheme B S hS))) :
    CreatesColimit E (BigFppfOver.toScheme B S hS) := by
  have _ : HasColimit ((E ⋙ Over.forget (B.obj hS)) ⋙ B.inclusion) :=
    hasColimit_of_iso (Functor.associator E (Over.forget (B.obj hS)) B.inclusion)
  let _ : CreatesColimit (E ⋙ Over.forget (B.obj hS)) B.inclusion :=
    createsColimitFullSubcategoryInclusion _ h
  change CreatesColimit E (Over.forget (B.obj hS) ⋙ B.inclusion)
  infer_instance

/-- Under the size hypotheses the forgetful functor to schemes creates the multicoequalizer of the
glue data, so the glued object exists in the big fppf category over `S`. -/
@[instance_reducible]
noncomputable def createsColimit_openChartGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) (hI : #I < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) := by
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  refine createsColimit_toScheme _ ?_
  change (colimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS)).size < B.cutoff
  rw [Scheme.size_congr (@HasColimit.isoOfNatIso _ _ _ _ _ _
    (hasColimit_openChartGlueData_comp hf) (hasMulticoequalizer_mapGlueData_toScheme hf)
    ((openChartGlueData hf).diagramIso (BigFppfOver.toScheme B S hS)))]
  exact openChartSchemeGlueData_size_lt_cutoff hf hI hμ hcharts

/-- The glue data has a glued object in the big fppf category over `S`. -/
theorem hasMulticoequalizer_openChartGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) (hI : #I < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    HasMulticoequalizer (openChartGlueData hf).diagram :=
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData hf hI hμ hcharts
  hasColimit_of_created _ (BigFppfOver.toScheme B S hS)

/-- The `V (i, j)` of the glue data really is the fibre product of the two inclusions into the
glued object. -/
noncomputable def isLimit_vPullbackCone_openChartGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) (hI : #I < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    [HasMulticoequalizer (openChartGlueData hf).diagram] (i j : I) :
    IsLimit ((openChartGlueData hf).vPullbackCone i j) := by
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData hf hI hμ hcharts
  have _ : PreservesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) := inferInstance
  exact (openChartGlueData hf).vPullbackConeIsLimitOfMap (BigFppfOver.toScheme B S hS) i j
    ((openChartSchemeGlueData hf).vPullbackConeIsLimit i j)

/-- The inclusions of the charts into the glued object of the big fppf category over `S` generate a
covering sieve of the fppf topology. -/
theorem ofArrows_mem_topology_openChartGlueData
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i)) (hI : #I < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    [HasMulticoequalizer (openChartGlueData hf).diagram] :
    Sieve.ofArrows (openChartGlueData hf).U (openChartGlueData hf).ι ∈
      BigFppfOver.topology B S hS (openChartGlueData hf).glued := by
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData hf hI hμ hcharts
  have _ : PreservesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) := inferInstance
  have hc : HasColimit
      ((openChartGlueData hf).mapGlueData (BigFppfOver.toScheme B S hS)).diagram.multispan :=
    hasMulticoequalizer_mapGlueData_toScheme hf
  have hcomp : ∀ i, (BigFppfOver.toScheme B S hS).map ((openChartGlueData hf).ι i) ≫
      ((openChartGlueData hf).gluedIso (BigFppfOver.toScheme B S hS)).hom =
      (openChartSchemeGlueData hf).ι i :=
    fun i => (openChartGlueData hf).ι_gluedIso_hom (BigFppfOver.toScheme B S hS) i
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS (openChartGlueData hf).ι
    (fun i => ?_) (fun x => ?_)
  · have h₁ : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ((openChartGlueData hf).ι i) ≫
        ((openChartGlueData hf).gluedIso (BigFppfOver.toScheme B S hS)).hom) := by
      rw [hcomp i]
      exact Scheme.GlueData.ι_isOpenImmersion (openChartSchemeGlueData hf) i
    exact IsOpenImmersion.of_comp _
      ((openChartGlueData hf).gluedIso (BigFppfOver.toScheme B S hS)).hom
  · obtain ⟨i, y, hy⟩ := (openChartSchemeGlueData hf).ι_jointly_surjective
      (((openChartGlueData hf).gluedIso (BigFppfOver.toScheme B S hS)).hom x)
    refine ⟨i, y, ((openChartGlueData hf).gluedIso
      (BigFppfOver.toScheme B S hS)).hom.isOpenEmbedding.injective ?_⟩
    show ((BigFppfOver.toScheme B S hS).map ((openChartGlueData hf).ι i) ≫
      ((openChartGlueData hf).gluedIso (BigFppfOver.toScheme B S hS)).hom) y = _
    rw [hcomp i]
    exact hy

/-- A sheaf `H` on the big fppf site over `S` which carries a family `p i : yoneda.obj (X i) ⟶ H`
of relatively representable open immersions, jointly locally surjective, is representable, provided
the index type has cardinality below the cutoff of the site and the charts have size uniformly
below it. -/
theorem isRepresentable_of_openCharts (H : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (X : I → BigFppfOver B S hS) (p : ∀ i, yoneda.obj (X i) ⟶ H.obj)
    (hp : ∀ i, (openImmersionOver B S hS).presheaf (p i)) (hI : #I < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    (hlocal : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc p)) :
    H.obj.IsRepresentable := by
  classical
  let D := openChartGlueData hp
  have _ : HasMulticoequalizer D.diagram := hasMulticoequalizer_openChartGlueData hp hI hμ hcharts
  have hcov : Sieve.ofArrows D.U D.ι ∈ BigFppfOver.topology B S hS D.glued :=
    ofArrows_mem_topology_openChartGlueData hp hI hμ hcharts
  let hlim : ∀ i j, IsLimit (D.vPullbackCone i j) := fun i j =>
    isLimit_vPullbackCone_openChartGlueData hp hI hμ hcharts i j
  let E := D.oneHypercover (J := BigFppfOver.topology B S hS) hcov hlim
  have hcompat : ∀ i j : I, H.obj.map (D.f i j).op (yonedaEquiv (p i)) =
      H.obj.map (D.t i j ≫ D.f j i).op (yonedaEquiv (p j)) := by
    intro i j
    refine (yonedaEquiv_naturality (p i) (D.f i j)).trans
      ((congrArg yonedaEquiv ?_).trans (yonedaEquiv_naturality (p j) (D.t i j ≫ D.f j i)).symm)
    show yoneda.map ((hp i).rep.fst' (p j)) ≫ p i =
      yoneda.map ((hp i).rep.symmetry (hp j).rep ≫ (hp j).rep.fst' (p i)) ≫ p j
    rw [Functor.relativelyRepresentable.symmetry_fst]
    exact ((hp i).rep.isPullback' (p j)).w
  let sec : (E.toPreOneHypercover.multicospanIndex H.obj).sections :=
    ⟨fun i => yonedaEquiv (p i), by rintro ⟨⟨i, j⟩, k⟩; exact hcompat i j⟩
  let η : yoneda.obj D.glued ⟶ H.obj :=
    yonedaEquiv.symm (Multifork.IsLimit.sectionsEquiv (E.isLimitMultifork H) sec)
  have hηfac : ∀ i, yoneda.map (D.ι i) ≫ η = p i := fun i => by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    show H.obj.map (D.ι i).op
      (Multifork.IsLimit.sectionsEquiv (E.isLimitMultifork H) sec) = yonedaEquiv (p i)
    exact Multifork.IsLimit.sectionsEquiv_apply_val (E.isLimitMultifork H) sec i
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) η := by
    let hmap : ∀ i, yoneda.obj (X i) ⟶ yoneda.obj D.glued := fun i => yoneda.map (D.ι i)
    have hfac : Sigma.desc hmap ≫ η = Sigma.desc p :=
      Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_desc_assoc, Sigma.ι_desc]; exact hηfac i
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac
  have hcompToGlued : ∀ {V : BigFppfOver B S hS} {i j : I} (a : V ⟶ X i) (b : V ⟶ X j),
      yoneda.map a ≫ p i = yoneda.map b ≫ p j → a ≫ D.ι i = b ≫ D.ι j := by
    intro V i j a b h
    have hstep : (hp i).rep.fst' (p j) ≫ D.ι i = (hp i).rep.snd (p j) ≫ D.ι j :=
      (D.glue_condition i j).symm.trans (by
        rw [← Category.assoc]
        exact congrArg (· ≫ D.ι j) (Functor.relativelyRepresentable.symmetry_fst _ _))
    calc a ≫ D.ι i = ((hp i).rep.lift' a b h ≫ (hp i).rep.fst' (p j)) ≫ D.ι i := by
          rw [(hp i).rep.lift'_fst]
      _ = ((hp i).rep.lift' a b h ≫ (hp i).rep.snd (p j)) ≫ D.ι j := by
          exact (Category.assoc _ _ _).trans ((_ ≫= hstep).trans (Category.assoc _ _ _).symm)
      _ = b ≫ D.ι j := by rw [(hp i).rep.lift'_snd]
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) η := by
    refine ⟨?_⟩
    rintro ⟨V⟩ (α β : V ⟶ D.glued) h
    replace h : yoneda.map α ≫ η = yoneda.map β ≫ η := by
      refine yonedaEquiv.injective ?_
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using h
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).intersection_covering
        ((BigFppfOver.topology B S hS).pullback_stable α hcov)
        ((BigFppfOver.topology B S hS).pullback_stable β hcov))
    rintro W γ ⟨⟨W₁, a, -, ⟨i⟩, fac₁⟩, ⟨W₂, b, -, ⟨j⟩, fac₂⟩⟩
    show γ ≫ α = γ ≫ β
    have h' : yoneda.map a ≫ p i = yoneda.map b ≫ p j := by
      have hh : yoneda.map (γ ≫ α) ≫ η = yoneda.map (γ ≫ β) ≫ η := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k => yoneda.map γ ≫ k) h
      rw [← fac₁, ← fac₂] at hh
      simp only [Functor.map_comp, Category.assoc] at hh
      change yoneda.map a ≫ (yoneda.map (D.ι i) ≫ η) =
        yoneda.map b ≫ (yoneda.map (D.ι j) ≫ η) at hh
      rw [hηfac i, hηfac j] at hh
      exact hh
    rw [← fac₁, ← fac₂]
    exact hcompToGlued a b h'
  let G : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj D.glued, BigFppfOver.isSheaf_yoneda_obj B S hS _⟩
  let ηS : G ⟶ H := ObjectProperty.homMk η
  have hisoS : IsIso ηS := (Sheaf.isLocallyBijective_iff_isIso ηS).mp ⟨hli, hls⟩
  have _ : IsIso η := inferInstanceAs
    (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map ηS))
  exact isRepresentable_of_natIso (yoneda.obj D.glued) (asIso η)

end GlueData

end AlgebraicGeometry

end
