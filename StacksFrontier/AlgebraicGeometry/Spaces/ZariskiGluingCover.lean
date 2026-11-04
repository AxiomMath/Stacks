module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Glueing which remembers the covering, and Tag 01JJ for the big fppf site

A sheaf on the big fppf site over `S` carrying a jointly locally surjective family of relatively
representable open immersions from objects of the site is represented by an object of the site,
provided the scheme glued from the charts is contained in the site; the representing object
comes with the covering of it induced by the charts. From this, the glueing step
`AlgebraicGeometry.HasZariskiGluing` of Tag 01JJ holds for the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.exists_representing_cover_of_openCharts`: the cover-remembering glueing.
  A sheaf `F` on the big fppf site over `S` carrying a jointly locally surjective family of
  relatively representable open immersions `f i : yoneda.obj (X i) ⟶ F` is represented by an
  object `Y` of the site, by an isomorphism `e : F ≅ yoneda.obj Y` which is produced together
  with the open immersions `g i : X i ⟶ Y`, the identification
  `f i ≫ e.hom = yoneda.map (g i)` of each chart with its piece of the covering of `Y`, the
  joint surjectivity of the pieces, and an identification `ε` of the scheme underlying `Y`
  with the glued scheme of `AlgebraicGeometry.openChartSchemeGlueData` under which `g i`
  becomes the `i`-th inclusion of the glue data.
* `AlgebraicGeometry.exists_representing_cover_of_openCharts_of_size_le`: the same under the
  two cardinal bounds `#I < B.cutoff` and a uniform bound `μ < B.cutoff` on the sizes of the
  charts.
* `AlgebraicGeometry.hasZariskiGluing`: `AlgebraicGeometry.HasZariskiGluing B S hS` holds for
  every big fppf site `B`, every scheme `S` contained in it and every index type, with no
  cardinal hypothesis.
* `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_lt_cof`: Tag 01JJ for the big fppf site
  of `S` under its cofinality bound alone.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section GlueData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} {X : I → BigFppfOver B S hS}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, yoneda.obj (X i) ⟶ F}

/-- If the glued scheme of the charts is contained in the site, then the forgetful functor to
schemes creates the multicoequalizer of the glue data `AlgebraicGeometry.openChartGlueData`. -/
@[instance_reducible]
noncomputable def createsColimit_openChartGlueData_of_contains
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))
    (hglued : B.Contains (openChartSchemeGlueData hf).glued) :
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
  exact hglued

/-- If the glued scheme of the charts is contained in the site, then the glue data
`AlgebraicGeometry.openChartGlueData` has a multicoequalizer. -/
theorem hasMulticoequalizer_openChartGlueData_of_contains
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))
    (hglued : B.Contains (openChartSchemeGlueData hf).glued) :
    HasMulticoequalizer (openChartGlueData hf).diagram :=
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData_of_contains hf hglued
  hasColimit_of_created _ (BigFppfOver.toScheme B S hS)

/-- If the glued scheme of the charts is contained in the site, then the `V (i, j)` of the glue
data is the fibre product of the two inclusions into the glued object. -/
noncomputable def isLimit_vPullbackCone_openChartGlueData_of_contains
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))
    (hglued : B.Contains (openChartSchemeGlueData hf).glued)
    [HasMulticoequalizer (openChartGlueData hf).diagram] (i j : I) :
    IsLimit ((openChartGlueData hf).vPullbackCone i j) := by
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData_of_contains hf hglued
  have _ : PreservesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) := inferInstance
  exact (openChartGlueData hf).vPullbackConeIsLimitOfMap (BigFppfOver.toScheme B S hS) i j
    ((openChartSchemeGlueData hf).vPullbackConeIsLimit i j)

/-- If the glued scheme of the charts is contained in the site, then the inclusions of the charts
into the glued object generate a covering sieve of the fppf topology. -/
theorem ofArrows_mem_topology_openChartGlueData_of_contains
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))
    (hglued : B.Contains (openChartSchemeGlueData hf).glued)
    [HasMulticoequalizer (openChartGlueData hf).diagram] :
    Sieve.ofArrows (openChartGlueData hf).U (openChartGlueData hf).ι ∈
      BigFppfOver.topology B S hS (openChartGlueData hf).glued := by
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData_of_contains hf hglued
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

/-- A sheaf `F` on the big fppf site over `S` which carries a family `f i : yoneda.obj (X i) ⟶ F`
of relatively representable open immersions, jointly locally surjective, is represented by an
object `Y` of the site *together with* the covering of `Y` induced by the charts, provided the
scheme glued from the charts is contained in the site.

Explicitly the conclusion provides, besides `Y`:

* an isomorphism `e : F ≅ yoneda.obj Y`;
* open immersions `g i : X i ⟶ Y`, one for each chart, with
  `f i ≫ e.hom = yoneda.map (g i)`: each chart is identified over `F` with its piece of the
  covering of `Y`;
* joint surjectivity on points of the `g i`, so that the pieces really cover `Y`;
* an isomorphism `ε` of the scheme underlying `Y` with the glued scheme
  `(openChartSchemeGlueData hf).glued` carrying `g i` to the `i`-th inclusion of the glue data.
-/
theorem exists_representing_cover_of_openCharts
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f))
    (hglued : B.Contains (openChartSchemeGlueData hf).glued) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (g : ∀ i, X i ⟶ Y)
      (ε : (BigFppfOver.toScheme B S hS).obj Y ≅ (openChartSchemeGlueData hf).glued),
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, (BigFppfOver.toScheme B S hS).map (g i) ≫ ε.hom =
        (openChartSchemeGlueData hf).ι i) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  classical
  let H : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF⟩
  let D := openChartGlueData hf
  have _ : HasMulticoequalizer D.diagram :=
    hasMulticoequalizer_openChartGlueData_of_contains hf hglued
  have hcov : Sieve.ofArrows D.U D.ι ∈ BigFppfOver.topology B S hS D.glued :=
    ofArrows_mem_topology_openChartGlueData_of_contains hf hglued
  let hlim : ∀ i j, IsLimit (D.vPullbackCone i j) := fun i j =>
    isLimit_vPullbackCone_openChartGlueData_of_contains hf hglued i j
  let E := D.oneHypercover (J := BigFppfOver.topology B S hS) hcov hlim
  have hcompat : ∀ i j : I, H.obj.map (D.f i j).op (yonedaEquiv (f i)) =
      H.obj.map (D.t i j ≫ D.f j i).op (yonedaEquiv (f j)) := by
    intro i j
    have h₁ : H.obj.map (D.f i j).op (yonedaEquiv (f i))
        = yonedaEquiv (yoneda.map (D.f i j) ≫ f i) := yonedaEquiv_naturality (f i) (D.f i j)
    have h₂ : H.obj.map (D.t i j ≫ D.f j i).op (yonedaEquiv (f j))
        = yonedaEquiv (yoneda.map (D.t i j ≫ D.f j i) ≫ f j) :=
      yonedaEquiv_naturality (f j) (D.t i j ≫ D.f j i)
    rw [h₁, h₂]
    refine congrArg yonedaEquiv ?_
    show yoneda.map ((hf i).rep.fst' (f j)) ≫ f i =
      yoneda.map ((hf i).rep.symmetry (hf j).rep ≫ (hf j).rep.fst' (f i)) ≫ f j
    rw [Functor.relativelyRepresentable.symmetry_fst]
    exact ((hf i).rep.isPullback' (f j)).w
  let sec : (E.toPreOneHypercover.multicospanIndex H.obj).sections :=
    ⟨fun i => yonedaEquiv (f i), by rintro ⟨⟨i, j⟩, k⟩; exact hcompat i j⟩
  let η : yoneda.obj D.glued ⟶ H.obj :=
    yonedaEquiv.symm (Multifork.IsLimit.sectionsEquiv (E.isLimitMultifork H) sec)
  have hηfac : ∀ i, yoneda.map (D.ι i) ≫ η = f i := fun i => by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    show H.obj.map (D.ι i).op
      (Multifork.IsLimit.sectionsEquiv (E.isLimitMultifork H) sec) = yonedaEquiv (f i)
    exact Multifork.IsLimit.sectionsEquiv_apply_val (E.isLimitMultifork H) sec i
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) η := by
    let hmap : ∀ i, yoneda.obj (X i) ⟶ yoneda.obj D.glued := fun i => yoneda.map (D.ι i)
    have hfac : Sigma.desc hmap ≫ η = Sigma.desc f := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
      exact hηfac i
    have _ := hsurj
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (BigFppfOver.topology B S hS) hfac
  have hcompToGlued : ∀ {V : BigFppfOver B S hS} {i j : I} (a : V ⟶ X i) (b : V ⟶ X j),
      yoneda.map a ≫ f i = yoneda.map b ≫ f j → a ≫ D.ι i = b ≫ D.ι j := by
    intro V i j a b h
    have hgl : (hf i).rep.symmetry (hf j).rep ≫ (hf j).rep.fst' (f i) ≫ D.ι j
        = (hf i).rep.fst' (f j) ≫ D.ι i :=
      D.glue_condition i j
    have hsym : (hf i).rep.symmetry (hf j).rep ≫ (hf j).rep.fst' (f i)
        = (hf i).rep.snd (f j) :=
      Functor.relativelyRepresentable.symmetry_fst _ _
    have hstep : (hf i).rep.fst' (f j) ≫ D.ι i = (hf i).rep.snd (f j) ≫ D.ι j :=
      calc (hf i).rep.fst' (f j) ≫ D.ι i
          = (hf i).rep.symmetry (hf j).rep ≫ (hf j).rep.fst' (f i) ≫ D.ι j := hgl.symm
        _ = ((hf i).rep.symmetry (hf j).rep ≫ (hf j).rep.fst' (f i)) ≫ D.ι j :=
            (Category.assoc _ _ _).symm
        _ = (hf i).rep.snd (f j) ≫ D.ι j := by rw [hsym]
    have h₁ : (hf i).rep.lift' a b h ≫ (hf i).rep.fst' (f j) = a :=
      (hf i).rep.lift'_fst a b h
    have h₂ : (hf i).rep.lift' a b h ≫ (hf i).rep.snd (f j) = b :=
      (hf i).rep.lift'_snd a b h
    calc a ≫ D.ι i
        = ((hf i).rep.lift' a b h ≫ (hf i).rep.fst' (f j)) ≫ D.ι i := by rw [h₁]
      _ = (hf i).rep.lift' a b h ≫ ((hf i).rep.fst' (f j) ≫ D.ι i) := Category.assoc _ _ _
      _ = (hf i).rep.lift' a b h ≫ ((hf i).rep.snd (f j) ≫ D.ι j) := by rw [hstep]
      _ = ((hf i).rep.lift' a b h ≫ (hf i).rep.snd (f j)) ≫ D.ι j :=
          (Category.assoc _ _ _).symm
      _ = b ≫ D.ι j := by rw [h₂]
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
    have h' : yoneda.map a ≫ f i = yoneda.map b ≫ f j := by
      have hh : yoneda.map (γ ≫ α) ≫ η = yoneda.map (γ ≫ β) ≫ η := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k => yoneda.map γ ≫ k) h
      rw [← fac₁, ← fac₂] at hh
      simp only [Functor.map_comp, Category.assoc] at hh
      change yoneda.map a ≫ (yoneda.map (D.ι i) ≫ η) =
        yoneda.map b ≫ (yoneda.map (D.ι j) ≫ η) at hh
      rwa [hηfac i, hηfac j] at hh
    rw [← fac₁, ← fac₂]
    exact hcompToGlued a b h'
  let G : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj D.glued, BigFppfOver.isSheaf_yoneda_obj B S hS _⟩
  let ηS : G ⟶ H := ObjectProperty.homMk η
  have hisoS : IsIso ηS := (Sheaf.isLocallyBijective_iff_isIso ηS).mp ⟨hli, hls⟩
  have _ : IsIso η := inferInstanceAs
    (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map ηS))
  have _ : HasColimit ((openChartGlueData hf).diagram.multispan ⋙
    BigFppfOver.toScheme B S hS) := hasColimit_openChartGlueData_comp hf
  have _ : CreatesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) :=
    createsColimit_openChartGlueData_of_contains hf hglued
  have _ : PreservesColimit (openChartGlueData hf).diagram.multispan
      (BigFppfOver.toScheme B S hS) := inferInstance
  have hc : HasColimit
      ((openChartGlueData hf).mapGlueData (BigFppfOver.toScheme B S hS)).diagram.multispan :=
    hasMulticoequalizer_mapGlueData_toScheme hf
  refine ⟨D.glued, (asIso η).symm, D.ι,
    D.gluedIso (BigFppfOver.toScheme B S hS), fun i => ?_,
    fun i => D.ι_gluedIso_hom (BigFppfOver.toScheme B S hS) i, fun i => ?_, fun y => ?_⟩
  · exact (Iso.comp_inv_eq (asIso η)).mpr (hηfac i).symm
  · have h₁ : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (D.ι i) ≫
        (D.gluedIso (BigFppfOver.toScheme B S hS)).hom) := by
      rw [D.ι_gluedIso_hom (BigFppfOver.toScheme B S hS) i]
      exact Scheme.GlueData.ι_isOpenImmersion (openChartSchemeGlueData hf) i
    exact IsOpenImmersion.of_comp ((BigFppfOver.toScheme B S hS).map (D.ι i))
      (D.gluedIso (BigFppfOver.toScheme B S hS)).hom
  · obtain ⟨i, z, hz⟩ := (openChartSchemeGlueData hf).ι_jointly_surjective
      ((D.gluedIso (BigFppfOver.toScheme B S hS)).hom y)
    refine ⟨i, z, (D.gluedIso (BigFppfOver.toScheme B S hS)).hom.isOpenEmbedding.injective ?_⟩
    show ((BigFppfOver.toScheme B S hS).map (D.ι i) ≫
      (D.gluedIso (BigFppfOver.toScheme B S hS)).hom) z = _
    rw [D.ι_gluedIso_hom (BigFppfOver.toScheme B S hS) i]
    exact hz

/-- A sheaf `F` on the big fppf site over `S` which carries a jointly locally surjective family
`f i : yoneda.obj (X i) ⟶ F` of relatively representable open immersions, indexed by a type of
cardinality less than `B.cutoff` and with the sizes of the charts bounded by some `μ < B.cutoff`,
is represented by an object `Y` of the site, by an isomorphism `e : F ≅ yoneda.obj Y`, together
with open immersions `g i : X i ⟶ Y` covering `Y` such that `f i ≫ e.hom = yoneda.map (g i)`. -/
theorem exists_representing_cover_of_openCharts_of_size_le
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f))
    (hI : #I < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hcharts : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (g : ∀ i, X i ⟶ Y),
      (∀ i, f i ≫ e.hom = yoneda.map (g i)) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)) := by
  obtain ⟨Y, e, g, -, hfg, -, hgopen, hgcov⟩ := exists_representing_cover_of_openCharts hF hf hsurj
    (openChartSchemeGlueData_size_lt_cutoff hf hI hμ hcharts)
  exact ⟨Y, e, g, hfg, hgopen, hgcov⟩

end GlueData

section Gluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf category over `S`, read as a morphism of schemes, commutes with
the structure morphisms to `S`. -/
theorem toScheme_map_comp_inclusion_hom {V W : BigFppfOver B S hS} (φ : V ⟶ W) :
    (BigFppfOver.toScheme B S hS).map φ ≫ B.inclusion.map W.hom = B.inclusion.map V.hom := by
  have h : (BigFppfOver.toScheme B S hS).map φ = B.inclusion.map φ.left := rfl
  rw [h, ← Functor.map_comp, Over.w]

/-- The structure morphisms to `S` of the objects of a glue data in the big fppf category over
`S` are compatible with the glueing maps of the glue data mapped to schemes. -/
theorem mapGlueData_toScheme_desc_condition
    (D : CategoryTheory.GlueData (BigFppfOver B S hS)) (a : D.J × D.J) :
    (D.mapGlueData (BigFppfOver.toScheme B S hS)).diagram.fst a ≫
        B.inclusion.map (D.U a.1).hom =
      (D.mapGlueData (BigFppfOver.toScheme B S hS)).diagram.snd a ≫
        B.inclusion.map (D.U a.2).hom := by
  obtain ⟨i, j⟩ := a
  show (BigFppfOver.toScheme B S hS).map (D.f i j) ≫ B.inclusion.map (D.U i).hom =
    (BigFppfOver.toScheme B S hS).map (D.t i j) ≫
      (BigFppfOver.toScheme B S hS).map (D.f j i) ≫ B.inclusion.map (D.U j).hom
  rw [toScheme_map_comp_inclusion_hom, toScheme_map_comp_inclusion_hom,
    toScheme_map_comp_inclusion_hom]

/-- `AlgebraicGeometry.HasZariskiGluing B S hS` holds: the glueing step of Tag 01JJ for the big
fppf category over `S` holds with no cardinal hypothesis. -/
theorem hasZariskiGluing : HasZariskiGluing B S hS := by
  intro F hF I X f hf hsurj
  have hw := mapGlueData_toScheme_desc_condition B S hS (openChartGlueData hf)
  refine ⟨(openChartSchemeGlueData hf).glued,
    Multicoequalizer.desc (openChartSchemeGlueData hf).diagram S
      (fun i => B.inclusion.map (X i).hom) hw,
    (openChartSchemeGlueData hf).ι,
    fun i => Scheme.GlueData.ι_isOpenImmersion (openChartSchemeGlueData hf) i,
    fun i => Multicoequalizer.π_desc (openChartSchemeGlueData hf).diagram S
      (fun i => B.inclusion.map (X i).hom) hw i,
    fun y => (openChartSchemeGlueData hf).ι_jointly_surjective y, fun hY => ?_⟩
  obtain ⟨W, e, g, ε, -, hgε, -, -⟩ := exists_representing_cover_of_openCharts hF hf hsurj hY
  have hpε : Multicoequalizer.desc (openChartSchemeGlueData hf).diagram S
      (fun i => B.inclusion.map (X i).hom) hw = ε.inv ≫ B.inclusion.map W.hom := by
    refine Multicoequalizer.hom_ext _ _ _ fun i => ?_
    have h₁ : (openChartSchemeGlueData hf).ι i ≫ ε.inv =
        (BigFppfOver.toScheme B S hS).map (g i) := (Iso.comp_inv_eq ε).mpr (hgε i).symm
    refine Eq.trans (Multicoequalizer.π_desc _ S _ hw i) ?_
    refine Eq.trans (toScheme_map_comp_inclusion_hom B S hS (g i)).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ B.inclusion.map W.hom) h₁.symm) ?_
    exact Category.assoc _ _ _
  have hεp : ε.hom ≫ Multicoequalizer.desc (openChartSchemeGlueData hf).diagram S
      (fun i => B.inclusion.map (X i).hom) hw = B.inclusion.map W.hom :=
    (Iso.eq_inv_comp ε).mp hpε
  refine ⟨e ≪≫ yoneda.mapIso (Over.isoMk
    (B.inclusion.preimageIso (X := W.left) (Y := B.obj hY) ε) ?_)⟩
  have hmap : B.inclusion.map
      (B.inclusion.preimage (X := W.left) (Y := B.obj hY) ε.hom) = ε.hom :=
    B.inclusion.map_preimage _
  exact B.inclusion.map_injective (Eq.trans (B.inclusion.map_comp _ _)
    (Eq.trans (congrArg (fun z => z ≫ Multicoequalizer.desc
      (openChartSchemeGlueData hf).diagram S (fun i => B.inclusion.map (X i).hom) hw) hmap) hεp))

/-- A sheaf for the fppf topology
of the big fppf category over `S` which admits a Zariski covering by representable open
subfunctors, indexed by a nonempty type smaller than the cofinality of the site's cutoff, is
representable. -/
theorem isRepresentable_of_zariskiCover_of_lt_cof
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type u} [Nonempty I] (hI : #I < B.cutoff.ord.cof)
    (X : I → BigFppfOver B S hS) (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (hf : ∀ i, Space.IsOpenImmersion B S hS (f i))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    F.IsRepresentable :=
  isRepresentable_of_zariskiCover B S hS (hasZariskiGluing B S hS) hF hI X f hf hsurj

end Gluing

end AlgebraicGeometry

end
