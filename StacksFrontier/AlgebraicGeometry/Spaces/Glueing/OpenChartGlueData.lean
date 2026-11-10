module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.GlueDataHypercover
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Glueing a sheaf out of representable open charts

Let `F` be a sheaf of sets on the big fppf site over `S` and let `yoneda.obj (X i) ⟶ F` be a
family of open immersions of presheaves, indexed by a type of cardinality below the cutoff of
the site, whose chart schemes have size below a common bound, and whose coproduct is locally
surjective onto `F`. Then `F` is representable: the charts glue to an object of the site,
inside the size cutoff, whose representable sheaf is isomorphic to `F`.

## Main definitions

* `AlgebraicGeometry.Space.openChartGlueDataOver` is the glueing datum in the big fppf
  category over `S` formed by the charts and their pairwise fibre products over `F`;
  `AlgebraicGeometry.Space.openChartGlueData` is its image in schemes.

## Main results

* `AlgebraicGeometry.Space.openChartGlueData_size_lt_cutoff`: the glued scheme is inside the
  size cutoff of the site.
* `AlgebraicGeometry.Space.isRepresentable_of_openCharts`: `F` is representable.

## Implementation notes

The glueing datum is formed in the site, not in schemes, so that its colimit is again an
object of the site. Its multicoequalizer exists because the functor to schemes creates it:
the colimit is computed in schemes, where it is the glued scheme of the image glueing datum,
and that scheme is inside the cutoff by
`AlgebraicGeometry.Space.openChartGlueData_size_lt_cutoff`. The charts then form a
`1`-hypercover of the glued object by `AlgebraicGeometry.Space.glueDataHypercover`, so the
family of chart sections of `F` glues to a single section, which is the comparison morphism.
It is locally surjective because the coproduct of the charts is, and locally injective
because two chart points with the same image in `F` already agree in the glued object; a
locally bijective morphism of sheaves is an isomorphism.

The transition maps of the glueing datum are built from the triple fibre products
`CategoryTheory.Functor.relativelyRepresentable.pullback₃`, and are stated in that form rather
than as maps between the underlying binary fibre products, so that the three projections
`p₁`, `p₂`, `p₃` apply to them directly when the cocycle identity is checked.
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} {X : I → BigFppfOver B S hS}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, yoneda.obj (X i) ⟶ F}

section Charts

/-- The glueing datum in the big fppf category over `S` whose charts are the sources of a
family of open immersions into a presheaf and whose chart intersections are their fibre
products over that presheaf. -/
noncomputable def openChartGlueDataOver
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i)) :
    CategoryTheory.GlueData (BigFppfOver B S hS) := by
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T
  have hP : P ≤ MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
    intro V W k hk
    have _ : AlgebraicGeometry.IsOpenImmersion (T.map k) := hk
    exact Functor.mono_of_mono_map T (f := k) inferInstance
  exact
    { J := I
      U := X
      V := fun (i, j) => (hf i).rep.pullback (f j)
      f := fun i j => (hf i).rep.fst' (f j)
      f_mono := fun i j => hP _ ((hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip)
      f_id := fun i => P.isIso_fst'_self hP (hf i)
      t := fun i j => (hf i).rep.symmetry (hf j).rep
      t_id := fun i => by
        apply (hf i).rep.hom_ext' <;> simp [P.fst'_self_eq_snd hP (hf i)]
      t' := fun i j k =>
        (Functor.relativelyRepresentable.lift₃ _ _ _
          (Functor.relativelyRepresentable.pullback₃.p₂ _ _ _)
          (Functor.relativelyRepresentable.pullback₃.p₃ _ _ _)
          (Functor.relativelyRepresentable.pullback₃.p₁ _ _ _)
          ((Functor.relativelyRepresentable.pullback₃.map_p₂_comp _ _ _).trans
            (Functor.relativelyRepresentable.pullback₃.map_p₃_comp _ _ _).symm)
          ((Functor.relativelyRepresentable.pullback₃.map_p₂_comp _ _ _).trans
            (Functor.relativelyRepresentable.pullback₃.map_p₁_comp _ _ _).symm) :
          Functor.relativelyRepresentable.pullback₃ (hf i).rep (f j) (f k) ⟶
            Functor.relativelyRepresentable.pullback₃ (hf j).rep (f k) (f i))
      t_fac := fun i j k => (hf j).rep.hom_ext'
        (by
          refine (congrArg (fun q => q ≫ (hf j).rep.fst' (f i))
            (Limits.pullback.lift_snd _ _ _)).trans ?_
          refine (Functor.relativelyRepresentable.lift'_fst _ _ _ _).trans ?_
          exact ((Category.assoc _ _ _).trans (congrArg
            (fun q => Limits.pullback.fst ((hf i).rep.fst' (f j)) ((hf i).rep.fst' (f k)) ≫ q)
            (Functor.relativelyRepresentable.symmetry_fst _ _))).symm)
        (by
          refine (congrArg (fun q => q ≫ (hf j).rep.snd (f i))
            (Limits.pullback.lift_snd _ _ _)).trans ?_
          refine (Functor.relativelyRepresentable.lift'_snd _ _ _ _).trans ?_
          exact ((Category.assoc _ _ _).trans (congrArg
            (fun q => Limits.pullback.fst ((hf i).rep.fst' (f j)) ((hf i).rep.fst' (f k)) ≫ q)
            (Functor.relativelyRepresentable.symmetry_snd _ _))).symm)
      cocycle := fun i j k => by
        change (_ : Functor.relativelyRepresentable.pullback₃ (hf i).rep (f j) (f k) ⟶
              Functor.relativelyRepresentable.pullback₃ (hf j).rep (f k) (f i)) ≫
            (_ : Functor.relativelyRepresentable.pullback₃ (hf j).rep (f k) (f i) ⟶
              Functor.relativelyRepresentable.pullback₃ (hf k).rep (f i) (f j)) ≫
            (_ : Functor.relativelyRepresentable.pullback₃ (hf k).rep (f i) (f j) ⟶
              Functor.relativelyRepresentable.pullback₃ (hf i).rep (f j) (f k)) =
          𝟙 (Functor.relativelyRepresentable.pullback₃ (hf i).rep (f j) (f k))
        exact Functor.relativelyRepresentable.pullback₃.hom_ext
          (by simp) (by simp) (by simp) }

/-- The image in schemes of `AlgebraicGeometry.Space.openChartGlueDataOver`: a glueing datum
of schemes, whose chart intersections are open in the charts. -/
noncomputable def openChartGlueData
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i)) : Scheme.GlueData.{u} :=
  { (openChartGlueDataOver B S hS hf).mapGlueData (BigFppfOver.toScheme B S hS) with
    f_open := fun i j => (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip }

/-- The scheme glued from the open charts is inside the size cutoff of the big fppf site, as
soon as the index type and the chart sizes are. -/
theorem openChartGlueData_size_lt_cutoff
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hI : #I < B.cutoff) (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    (openChartGlueData B S hS hf).glued.size < B.cutoff := by
  let D := openChartGlueData B S hS hf
  rcases isEmpty_or_nonempty I with hEmpty | hne
  · have hD : IsEmpty D.glued := ⟨fun x => by
      obtain ⟨i, _, _⟩ := D.ι_jointly_surjective x
      exact hEmpty.false i⟩
    have hs : D.glued.size ≤ ℵ₀ := by
      unfold Scheme.size
      refine max_le le_rfl (max_le ?_ (ciSup_le' fun V => ?_))
      · have hsub : Subsingleton D.glued.affineOpens :=
          ⟨fun V W => by
            apply Subtype.ext
            ext x
            exact (hD.false x).elim⟩
        exact (le_one_iff_subsingleton.mpr hsub).trans one_le_aleph0
      · exact (le_one_iff_subsingleton.mpr inferInstance).trans one_le_aleph0
    exact hs.trans_lt B.aleph0_lt_cutoff
  · have : Nonempty D.J := hne
    calc
      D.glued.size ≤ max #I (⨆ i : I, (D.U i).size) := scheme_glueData_size_le D
      _ < B.cutoff := max_lt hI (lt_of_le_of_lt (ciSup_le' hcharts) hμ)

/-- The glueing diagram of the open charts has a colimit after passing to schemes: there it
is the glued scheme of the image glueing datum. -/
theorem openChart_hasColimit_comp
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i)) :
    HasColimit ((openChartGlueDataOver B S hS hf).diagram.multispan ⋙
      BigFppfOver.toScheme B S hS) := by
  let D₀ := openChartGlueDataOver B S hS hf
  let D := openChartGlueData B S hS hf
  let T := BigFppfOver.toScheme B S hS
  let hc : HasColimit D.toGlueData.diagram.multispan :=
    inferInstanceAs (HasMulticoequalizer D.toGlueData.diagram)
  let e : D₀.diagram.multispan ⋙ T ≅ D.toGlueData.diagram.multispan := D₀.diagramIso T
  exact @hasColimit_of_iso _ _ _ _ _ _ hc e

/-- The functor to schemes creates the colimit of the glueing diagram of the open charts. -/
@[instance_reducible]
noncomputable def openChart_createsColimit
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hI : #I < B.cutoff) (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    CreatesColimit (openChartGlueDataOver B S hS hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) := by
  let D₀ := openChartGlueDataOver B S hS hf
  let D := openChartGlueData B S hS hf
  let T := BigFppfOver.toScheme B S hS
  have _ : HasColimit (D₀.diagram.multispan ⋙ T) := openChart_hasColimit_comp B S hS hf
  apply AlgebraicGeometry.createsColimit_toScheme
  change (colimit (D₀.diagram.multispan ⋙ T)).size < B.cutoff
  let hc : HasColimit D.toGlueData.diagram.multispan :=
    inferInstanceAs (HasMulticoequalizer D.toGlueData.diagram)
  let e : D₀.diagram.multispan ⋙ T ≅ D.toGlueData.diagram.multispan := D₀.diagramIso T
  let e' : colimit (D₀.diagram.multispan ⋙ T) ≅ D.glued :=
    @HasColimit.isoOfNatIso _ _ _ _ _ _
      (openChart_hasColimit_comp B S hS hf) hc e
  rw [Scheme.size_congr e']
  exact openChartGlueData_size_lt_cutoff B S hS hf hI μ hμ hcharts

/-- The glueing diagram of the open charts has a multicoequalizer in the big fppf category
over `S`. -/
theorem openChart_hasColimit
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hI : #I < B.cutoff) (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    HasMulticoequalizer (openChartGlueDataOver B S hS hf).diagram := by
  have _ := openChart_hasColimit_comp B S hS hf
  have _ := openChart_createsColimit B S hS hf hI μ hμ hcharts
  exact hasColimit_of_created _ (BigFppfOver.toScheme B S hS)

/-- The chart intersections of the glueing datum of open charts are the fibre products of the
charts over the glued object. -/
noncomputable def openChart_vPullbackConeIsLimit
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hI : #I < B.cutoff) (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    [HasMulticoequalizer (openChartGlueDataOver B S hS hf).diagram]
    (i j : I) :
    IsLimit ((openChartGlueDataOver B S hS hf).vPullbackCone i j) := by
  have _ : HasColimit ((openChartGlueDataOver B S hS hf).diagram.multispan ⋙
      BigFppfOver.toScheme B S hS) := openChart_hasColimit_comp B S hS hf
  have _ : CreatesColimit (openChartGlueDataOver B S hS hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    openChart_createsColimit B S hS hf hI μ hμ hcharts
  exact (openChartGlueDataOver B S hS hf).vPullbackConeIsLimitOfMap
    (BigFppfOver.toScheme B S hS) i j ((openChartGlueData B S hS hf).vPullbackConeIsLimit i j)

/-- The open charts generate a covering sieve of the glued object. -/
theorem openChart_openCover_mem
    (hf : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hI : #I < B.cutoff) (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    letI := openChart_hasColimit B S hS hf hI μ hμ hcharts
    Sieve.generate (Presieve.ofArrows
      (openChartGlueDataOver B S hS hf).U
      (openChartGlueDataOver B S hS hf).ι) ∈
        (BigFppfOver.topology B S hS) (openChartGlueDataOver B S hS hf).glued := by
  classical
  have _ := openChart_hasColimit B S hS hf hI μ hμ hcharts
  have _ := openChart_hasColimit_comp B S hS hf
  have _ := openChart_createsColimit B S hS hf hI μ hμ hcharts
  let D₀ := openChartGlueDataOver B S hS hf
  let D := openChartGlueData B S hS hf
  let T := BigFppfOver.toScheme B S hS
  let e := D₀.gluedIso T
  have hX : B.Contains (T.obj D₀.glued) := by
    change (T.obj D₀.glued).size < B.cutoff
    rw [Scheme.size_congr e]
    exact openChartGlueData_size_lt_cutoff B S hS hf hI μ hμ hcharts
  let Y : D₀.J → B.Schemes := fun i => (D₀.U i).left
  let g : ∀ i, Y i ⟶ B.obj hX := fun i => (D₀.ι i).left
  have hcomp (i : D₀.J) : T.map (D₀.ι i) ≫ e.hom = D.ι i := by
    simpa [D, D₀, e, openChartGlueData] using D₀.ι_gluedIso_hom T i
  have hopen : ∀ i, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (g i)) := by
    intro i
    have : AlgebraicGeometry.IsOpenImmersion (T.map (D₀.ι i) ≫ e.hom) := by
      rw [hcomp i]
      exact Scheme.GlueData.ι_isOpenImmersion D i
    change AlgebraicGeometry.IsOpenImmersion (T.map (D₀.ι i))
    exact IsOpenImmersion.of_comp _ e.hom
  have hsurj' : ∀ x : B.inclusion.obj (B.obj hX),
      ∃ i y, (B.inclusion.map (g i)).base y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective (e.hom x)
    refine ⟨i, y, ?_⟩
    apply e.hom.isOpenEmbedding.injective
    change (T.map (D₀.ι i) ≫ e.hom) y = e.hom x
    rwa [hcomp i]
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact open_cover_mem_bigFppf_topology B hX Y g hopen hsurj'


end Charts

/-- A sheaf of sets on the big fppf site over `S` with a family of representable open charts
of bounded index type and bounded chart size, whose coproduct is locally surjective onto it,
is representable. -/
theorem isRepresentable_of_openCharts
    (H : Sheaf (BigFppfOver.topology B S hS) (Type u))
    {I : Type u} (X : I → BigFppfOver B S hS)
    (p : ∀ i, yoneda.obj (X i) ⟶ H.obj)
    (hp : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (p i))
    (hI : #I < B.cutoff) (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    (hlocal : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS) (Sigma.desc p)) :
    H.obj.IsRepresentable := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let D₀ := openChartGlueDataOver B S hS hp
  have _ : HasMulticoequalizer D₀.diagram :=
    openChart_hasColimit B S hS hp hI μ hμ hcharts
  let hcover := openChart_openCover_mem B S hS hp hI μ hμ hcharts
  let hlim (i j : I) := openChart_vPullbackConeIsLimit B S hS hp hI μ hμ hcharts i j
  let E := glueDataHypercover D₀ hcover hlim
  let ιX : ∀ i : I, X i ⟶ D₀.glued := D₀.ι
  let s : ∀ i : I, H.obj.obj (Opposite.op (X i)) := fun i => yonedaEquiv (p i)
  have hcompat (i j : I) :
      H.obj.map ((hp i).rep.fst' (p j)).op (s i) =
        H.obj.map ((hp i).rep.symmetry (hp j).rep ≫ (hp j).rep.fst' (p i)).op (s j) := by
    dsimp only [s]
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    congr 1
    rw [Functor.relativelyRepresentable.symmetry_fst]
    exact ((hp i).rep.isPullback' (p j)).w
  let sec : (E.toPreOneHypercover.multicospanIndex H.obj).sections :=
    ⟨s, fun ⟨⟨i, j⟩, _⟩ => hcompat i j⟩
  let gluedSection : H.obj.obj (Opposite.op D₀.glued) :=
    Multifork.IsLimit.sectionsEquiv (E.isLimitMultifork H) sec
  let η : yoneda.obj D₀.glued ⟶ H.obj := yonedaEquiv.symm gluedSection
  have hη (i : I) : yoneda.map (ιX i) ≫ η = p i := by
    apply yonedaEquiv.injective
    dsimp only [η]
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    change H.obj.map (D₀.ι i).op gluedSection = s i
    exact Multifork.IsLimit.sectionsEquiv_apply_val (E.isLimitMultifork H) sec i
  have hfactor : Sigma.desc (fun i => yoneda.map (ιX i)) ≫ η = Sigma.desc p :=
    Sigma.hom_ext _ _ fun i => by simpa only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using hη i
  have _ : Presheaf.IsLocallySurjective J η :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfactor
  have hcompToGlued {V : C} {i j : I} (a : V ⟶ X i) (b : V ⟶ X j)
      (h : yoneda.map a ≫ p i = yoneda.map b ≫ p j) :
      a ≫ ιX i = b ≫ ιX j := by
    rw [← (hp i).rep.lift'_fst a b h, Category.assoc]
    conv_rhs => rw [← (hp i).rep.lift'_snd a b h, Category.assoc]
    congr 1
    calc
      _ = (hp i).rep.symmetry (hp j).rep ≫
          ((hp j).rep.fst' (p i) ≫ ιX j) := (D₀.glue_condition i j).symm
      _ = _ := by rw [← Category.assoc, Functor.relativelyRepresentable.symmetry_fst]
  have _ : Presheaf.IsLocallyInjective J η := by
    refine ⟨?_⟩
    rintro ⟨V⟩ (α β : V ⟶ D₀.glued) h
    replace h : yoneda.map α ≫ η = yoneda.map β ≫ η := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using h
    refine J.superset_covering ?_ (J.intersection_covering
      (J.pullback_stable α hcover) (J.pullback_stable β hcover))
    rintro W γ ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change γ ≫ α = γ ≫ β
    have h' : yoneda.map a ≫ p i = yoneda.map b ≫ p j := by
      have hh : yoneda.map (γ ≫ α) ≫ η = yoneda.map (γ ≫ β) ≫ η := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k => yoneda.map γ ≫ k) h
      rw [← fac₁, ← fac₂] at hh
      simp only [Functor.map_comp, Category.assoc] at hh
      rwa [← hη i, ← hη j]
    rw [← fac₁, ← fac₂]
    exact hcompToGlued a b h'
  let XF : Sheaf J (Type u) :=
    ⟨yoneda.obj D₀.glued, (isAlgebraicSpace_yoneda B S hS D₀.glued).isSheaf⟩
  let ηS : XF ⟶ H := ⟨η⟩
  have _ : IsIso ηS := by
    rw [← Sheaf.isLocallyBijective_iff_isIso ηS]
    constructor <;> infer_instance
  have _ : IsIso η := inferInstanceAs (IsIso ((sheafToPresheaf J (Type u)).map ηS))
  exact isRepresentable_of_natIso (yoneda.obj D₀.glued) (asIso η)

end AlgebraicGeometry.Space

end
