module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSmoothChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSmoothDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.VersalSmoothChart
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas

/-!
# Smoothness near a point of the lifting property, over a Noetherian affine source

Let `S` be a scheme contained in a big fppf site `B`, `V = Spec R` a Noetherian affine object of
the site locally of finite type over `S`, `T ⊆ |V|` closed, `W` a locally Noetherian formal
algebraic space and `g : V_{/T} ⟶ W` representable by algebraic spaces. If `g` has the lifting
property (`AlgebraicGeometry.FormalSpace.LiftsAtCompletion`) at a point `q ∈ T`, then `g` is
smooth over the completion of an open neighbourhood of `q`. This is the proof of Stacks 0GI9
for an affine `V`: an affine étale chart `Spf C₀ ⟶ W` through the image of `q` and an étale
`V' ⟶ V` over it (`exists_etale_chart_of_isLocallyNoetherian`) reduce to the affine target case
(`exists_isOpenImmersion_smooth_of_liftsAtCompletion_affine`) at a point of `V'` over `q`, and
smoothness descends to the image of the resulting open of `V'`.

## Main results

* `exists_isOpenImmersion_smooth_of_liftsAtCompletion_of_isLocallyNoetherian`: the statement
  above.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Completions along a commutative square of presheaves compose to the same morphism, up to
the identification of the two inverse images of the set of points. -/
theorem exists_iso_completionSheafMap_comp {X₁ X₂ X₂' X₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (a' : X₁ ⟶ X₂') (b' : X₂' ⟶ X₃) (hab : a ≫ b = a' ≫ b')
    (T : Set (Space.points B S hS X₃)) :
    ∃ e : Space.completionSheaf B S hS X₁ (Space.pointsMap B S hS _ a ⁻¹'
        (Space.pointsMap B S hS _ b ⁻¹' T)) ≅
      Space.completionSheaf B S hS X₁ (Space.pointsMap B S hS _ a' ⁻¹'
        (Space.pointsMap B S hS _ b' ⁻¹' T)),
      Space.completionSheafMap B S hS a (Space.pointsMap B S hS _ b ⁻¹' T) ≫
          Space.completionSheafMap B S hS b T =
        e.hom ≫ Space.completionSheafMap B S hS a' (Space.pointsMap B S hS _ b' ⁻¹' T) ≫
          Space.completionSheafMap B S hS b' T := by
  have hs : Space.pointsMap B S hS _ a ⁻¹' (Space.pointsMap B S hS _ b ⁻¹' T) =
      Space.pointsMap B S hS _ a' ⁻¹' (Space.pointsMap B S hS _ b' ⁻¹' T) := by
    rw [Space.preimage_pointsMap_preimage_pointsMap, Space.preimage_pointsMap_preimage_pointsMap,
      hab]
  refine ⟨eqToIso (congrArg (Space.completionSheaf B S hS X₁) hs), ?_⟩
  rw [Space.completionSheafMap_comp_completionSheafMap,
    Space.completionSheafMap_comp_completionSheafMap,
    ← Space.eqToHom_comp_completionSheafMap hab.symm T]
  simp only [eqToIso.hom, eqToHom_trans_assoc]

/-- The affine target case `exists_isOpenImmersion_smooth_of_liftsAtCompletion_affine`, for a set
of points given as a zero locus through an equation. -/
theorem exists_isOpenImmersion_smooth_of_liftsAtCompletion_of_eq {R : Type u} [CommRing R]
    [IsNoetherianRing R] (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType s] {C₀ : Type u} [CommRing C₀] [TopologicalSpace C₀]
    [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀] [IsNoetherianRing C₀]
    (hC₀ : TopologicalRing.IsAdic C₀) (E : QuotientSystem B S hS C₀)
    {Z : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))} (I : Ideal R)
    (hZ : Z = zeroLocusPoints B S hS hR s I)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) Z ⟶ formalSpectrum E)
    (hG : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G.hom)
    (v : PrimeSpectrum R)
    (hlift : LiftsAtCompletion B S hS (affineOver B S hS hR s) Z (formalSpectrum E) G v) :
    ∃ (U : BigFppfOver B S hS) (j : U ⟶ affineOver B S hS hR s),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map j) ∧
      ∃ hrep, Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom)
        (Space.completionSheafMap B S hS (yoneda.map j) Z ≫ G).hom hrep := by
  subst hZ
  exact exists_isOpenImmersion_smooth_of_liftsAtCompletion_affine B S hS hR s I hC₀ E G hG v
    (fun _ => hlift)

/-- An étale morphism of the big fppf site factors as an étale surjection onto an open
subobject of its target followed by the open immersion of that subobject. -/
theorem exists_isOpenImmersion_etale_surjective_comp_eq {X Y : BigFppfOver B S hS} (k : X ⟶ Y)
    [hk : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k)] :
    ∃ (U : BigFppfOver B S hS) (i : U ⟶ Y) (h : X ⟶ U),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) ∧
      AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map h) ∧ h ≫ i = k := by
  let Sch := BigFppfOver.toScheme B S hS
  let φ : Sch.obj X ⟶ Sch.obj Y := Sch.map k
  have : AlgebraicGeometry.Etale φ := hk
  let O : Y.left.obj.Opens := ⟨Set.range φ, φ.isOpenMap.isOpen_range⟩
  let i : BigFppfOver.openSubObj B S hS Y O ⟶ Y := BigFppfOver.openSubHom B S hS Y O
  let h₀ : Sch.obj X ⟶ O.toScheme := IsOpenImmersion.lift O.ι φ (Scheme.Opens.range_ι O).ge
  have hh₀ : h₀ ≫ O.ι = φ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨h, hh⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := X)
      (Y := BigFppfOver.openSubObj B S hS Y O) h₀ (by
    change h₀ ≫ O.ι ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom
    rw [← Category.assoc, hh₀]
    exact congrArg B.inclusion.map (Over.w k))
  refine ⟨_, i, h, inferInstanceAs (IsOpenImmersion O.ι), ?_, ?_, ?_⟩
  · rw [hh]
    exact MorphismProperty.of_postcomp (W := @AlgebraicGeometry.Etale)
      (W' := @AlgebraicGeometry.Etale) h₀ O.ι inferInstance (by rwa [hh₀])
  · rw [hh]
    refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := x.2
    refine ⟨y, O.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hh₀]
    exact hy.trans (Scheme.Opens.ι_apply O x).symm
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Sch.map h ≫ O.ι = φ
    rw [hh, hh₀]

/-- **Smoothness near a point of the lifting property (Noetherian affine source).** Let
`V = Spec R` be Noetherian and locally of finite type over `S`, `T ⊆ |V|` closed, `W` a locally
Noetherian formal algebraic space and `g : V_{/T} ⟶ W` representable by algebraic spaces with
the lifting property at a point `q ∈ T`. Then `g` restricted to the completion of some open
neighbourhood of `q` is smooth. -/
theorem exists_isOpenImmersion_smooth_of_liftsAtCompletion_of_isLocallyNoetherian {R : Type u}
    [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType s]
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s))))
    (hT : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hR s))) T)
    {W : FppfSheaf B S hS} (hW : IsLocallyNoetherian B S hS W)
    (g : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T ⟶ W)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (q : Space.points B S hS (yoneda.obj (affineOver B S hS hR s))) (hq : q ∈ T)
    (hlift : LiftsAtCompletion B S hS (affineOver B S hS hR s) T W g
      (Space.pointsToScheme B S hS _ q)) :
    ∃ (U : BigFppfOver B S hS) (i : U ⟶ affineOver B S hS hR s),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      Space.pointsToScheme B S hS _ q ∈ Set.range ((BigFppfOver.toScheme B S hS).map i) ∧
      ∃ hrep, Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom)
        (Space.completionSheafMap B S hS (yoneda.map i) T ≫ g).hom hrep := by
  classical
  obtain ⟨R', _, _, hR', s', _, f, hfE, v', hv', C₀, _, _, _, _, _, hC₀, E₀, ψ, hψ, G', hG'r,
    hG'⟩ := exists_etale_chart_of_isLocallyNoetherian B S hS hR s T hT hW g hg q hq
  obtain ⟨hcr, hcp⟩ := isEtale_completionSheafMap B S hS (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) (yoneda.map f) T (Space.isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ f).mpr hfE))
  have hfin : ((((Over.post B.inclusion).map f).left).residueFieldMap v').hom.Finite := by
    let fS := ((Over.post B.inclusion).map f).left
    have : AlgebraicGeometry.Etale fS := hfE
    refine finite_residueField_of_etale_fibers fS (fun y => ?_) v'
    change AlgebraicGeometry.Etale (Limits.pullback.snd fS
      ((((Over.post B.inclusion).obj (affineOver B S hS hR s)).left).fromSpecResidueField y))
    infer_instance
  have hlift' := liftsAtCompletion_of_formallyEtale B S hS f T g ψ G' hG'
    (formallyEtale_hom_of_isRepresentableEtale _ ⟨hcr, hcp⟩)
    (formallyEtale_hom_of_isRepresentableEtale ψ hψ) v' hfin (hv' ▸ hlift)
  obtain ⟨J, hJ⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hR' s' _
    (hT.preimage (Space.continuous_pointsMap B S hS _))
  obtain ⟨U', j, hj, ⟨u', hu'⟩, hrepj, hsmj⟩ :=
    exists_isOpenImmersion_smooth_of_liftsAtCompletion_of_eq B S hS hR' s' hC₀ E₀ J hJ G' hG'r
      v' hlift'
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (j ≫ f)) := by
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨U, i, h, hi, hhE, hhS, hhi⟩ :=
    exists_isOpenImmersion_etale_surjective_comp_eq B S hS (j ≫ f)
  obtain ⟨e, he⟩ := exists_iso_completionSheafMap_comp B S hS (yoneda.map h) (yoneda.map i)
    (yoneda.map j) (yoneda.map f) (by rw [← Functor.map_comp, ← Functor.map_comp, hhi]) T
  obtain ⟨hrep'', hsm''⟩ := exists_hasPropertyULift_isSmoothULift_iso_comp B S hS e _ hrepj hsmj
  obtain ⟨hrep, hsm⟩ := exists_hasPropertyULift_isSmoothULift_completionSheafMap_of_etale_cover
    B S hS i h hhE hhS T g hg ψ hψ _ hrep'' hsm'' (by
      rw [← Category.assoc (Space.completionSheafMap B S hS (yoneda.map h) _), he]
      simp only [Category.assoc, hG'])
  refine ⟨U, i, hi, ⟨(BigFppfOver.toScheme B S hS).map h u', ?_⟩, hrep, hsm⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hhi, ← hv', ← hu']
  rfl

end AlgebraicGeometry.FormalSpace
