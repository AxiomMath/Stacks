module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceEtaleSectionApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# A finite cover through a closed subspace of a finite and finitely presented space

Let `X` be an algebraic space over a scheme `S`, `q : P ⟶ X` a finite morphism, `p : h_V ⟶ X` an
étale morphism from an affine scheme and `C ⊆ P` a closed subspace such that `C ⟶ X` factors
through `p` on an open neighbourhood of every point of `C`. This file produces, around every point
of `C`, an étale chart `g : h_Γ ⟶ P` from a quasi-compact scheme, open in `P ×_X V`, over which
`C ⟶ X` factors through `p` and which is a monomorphism over `C`: two morphisms into `Γ` with the
same image in `C` agree. These are exactly the charts that
`AlgebraicGeometry.Space.exists_isFinitePresentation_isEtaleSectionClosed` needs.

The chart is the graph. If `W ⊆ C` is open and `c : W ⟶ V` is a factorization, the graph
`W ⟶ C ×_X V` is a section of an étale morphism over the open `W`, hence an open immersion. Points
of a closed subspace carry the subspace topology, so the open image of the graph is cut out on
`|C ×_X V| ⊆ |P ×_X V|` by an open set of `|P ×_X V|`, and a quasi-compact open neighbourhood of
a point of the graph inside that open set is the chart. A pair of morphisms into the chart with the
same image in `C` lands in the graph, where the projection to `C` is the inclusion of `W`.

## Main results

* `AlgebraicGeometry.Space.exists_etaleChart_mono_over_closedSubspace`.
* `AlgebraicGeometry.Space.preimage_le_range_diagonal_of_forall`: the criterion that turns the
  monomorphism property into the first property of
  `AlgebraicGeometry.Space.IsEtaleSectionClosed`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The monomorphism property over a subfunctor is the diagonal property.** If any two
morphisms into `Γ` with the same image in `P`, factoring through `T`, are equal, then the pairs of
sections of `Γ` with the same image in `T` lie on the diagonal of `Γ ×_P Γ`. -/
theorem preimage_le_range_diagonal_of_forall {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Γ : BigFppfOver B S hS} (g : yoneda.obj Γ ⟶ P) (T : Subfunctor P)
    (h : ∀ (Z : BigFppfOver B S hS) (a b : yoneda.obj Z ⟶ yoneda.obj Γ), a ≫ g = b ≫ g →
      (∃ t : yoneda.obj Z ⟶ T.toFunctor, t ≫ T.ι = a ≫ g) → a = b) :
    T.preimage (pullback.fst g g ≫ g) ≤ Subfunctor.range (pullback.diagonal g) := by
  intro Z w hw
  let l : yoneda.obj Z.unop ⟶ pullback g g := yonedaEquiv.symm w
  have hl : yonedaEquiv l = w := yonedaEquiv.apply_symm_apply w
  have hmem : yonedaEquiv (l ≫ pullback.fst g g ≫ g) ∈ T.obj (op Z.unop) := by
    rw [yonedaEquiv_comp, hl]
    exact hw
  have hab : l ≫ pullback.fst g g = l ≫ pullback.snd g g :=
    h Z.unop _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])
      ((Subfunctor.mem_obj_iff_exists T _).1 (by simpa only [Category.assoc] using hmem) |>.imp
        fun t ht => by rw [ht, Category.assoc])
  refine ⟨yonedaEquiv (l ≫ pullback.fst g g), ?_⟩
  rw [← yonedaEquiv_comp, ← hl]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hab]

/-- The lift of `γ₀ : W ⟶ h_E` to the base change `C ×_P E` is an open immersion when `W` is open
in `C`, `γ₀` lies over the inclusion of `W` and `h_E ⟶ P` is étale. -/
theorem isOpenImmersion_lift_of_comp_eq {P : AlgebraicSpaces B S hS} {E : BigFppfOver B S hS}
    {iE : yoneda.obj E ⟶ P.1} (hiE : IsEtale B S hS iE) (C : ClosedSubspaces B S hS P.1)
    {W : Subfunctor C.1.toFunctor} (hW : IsOpenSubspace B S hS W)
    {γ₀ : W.toFunctor ⟶ yoneda.obj E} (hγ₀ : γ₀ ≫ iE = W.ι ≫ C.1.ι)
    (hle : Subfunctor.range γ₀ ≤ C.1.preimage iE) :
    IsOpenImmersion B S hS (Subfunctor.lift γ₀ hle) := by
  have hEalg := isAlgebraicSpace_yoneda B S hS E
  have hCE : IsClosedSubspace B S hS (C.1.preimage iE) :=
    isClosedSubspace_preimage_yoneda B S hS P iE C
  have hγφ : Subfunctor.lift γ₀ hle ≫ C.1.fromPreimage iE = W.ι := by
    rw [← cancel_mono C.1.ι, Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
      Subfunctor.lift_ι, hγ₀]
  have hφ : IsEtale B S hS (C.1.fromPreimage iE) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS (Subfunctor.isPullback_preimage iE C.1) hCE.1
      C.2.1 hEalg P.2 hiE
  exact isOpenImmersion_of_isEtale_of_mono B S hS _ hW.1 hCE.1
    (isEtale_of_isEtale_over B S hS hW.1 hCE.1 C.2.1 _ W.ι _ (isEtale_ι_of_isOpenSubspace hW) hφ
      hγφ) (mono_of_mono_fac hγφ)

/-- Every point of an open set `O` of `|h_E|` lies in the image of an open subspace `G` with points
in `O`, represented by a quasi-compact scheme. -/
theorem exists_compactChart_of_mem_isOpen {E : BigFppfOver B S hS}
    {O : Set (points B S hS (yoneda.obj E))} (hO : IsOpen O) {e₀ : points B S hS (yoneda.obj E)}
    (he₀ : e₀ ∈ O) :
    ∃ (G : Subfunctor (yoneda.obj E)) (Γ : BigFppfOver B S hS) (eG : yoneda.obj Γ ≅ G.toFunctor),
      IsOpenSubspace B S hS G ∧ Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆ O ∧
      e₀ ∈ Set.range (pointsMap B S hS _ (eG.hom ≫ G.ι)) ∧
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Γ) := by
  have hEalg := isAlgebraicSpace_yoneda B S hS E
  obtain ⟨O', ⟨hO'o, hO'c, he₀O'⟩, hO'O⟩ :=
    (hasBasis_nhds_isOpen_isCompact B S hS _ hEalg e₀).mem_iff.1 (hO.mem_nhds he₀)
  -- The chart: the open subspace of `E` with points `O'`.
  let G : Subfunctor (yoneda.obj E) := openSubspaceOfPoints B S hS (yoneda.obj E) O'
  have hG : IsOpenSubspace B S hS G := isOpenSubspace_openSubspaceOfPoints B S hS hEalg O' hO'o
  have hGpts : Set.range (pointsMap B S hS G.toFunctor G.ι) = O' :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS O'
  have : G.toFunctor.IsRepresentable := isRepresentable_of_isOpenSubspace B S hS inferInstance G hG
  let eG : yoneda.obj G.toFunctor.reprX ≅ G.toFunctor := G.toFunctor.reprW
  have hGqc : IsQuasiCompactSpace B S hS G.toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS hEalg hG (by rwa [hGpts])
  obtain ⟨e₁, he₁⟩ : e₀ ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by rwa [hGpts]
  obtain ⟨e₂, he₂⟩ := (bijective_pointsMap_of_isIso B S hS eG.hom).2 e₁
  refine ⟨G, _, eG, hG, by rwa [hGpts], ⟨e₂, by rw [pointsMap_comp_apply, he₂, he₁]⟩, ?_⟩
  refine compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS ?_
  rw [isQuasiCompactSpace_iff_compactSpace_points B S hS _ (isAlgebraicSpace_yoneda B S hS _)]
  have := (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hG.1).1 hGqc
  exact (bijective_pointsMap_of_isIso B S hS eG.inv).2.compactSpace
    (continuous_pointsMap B S hS eG.inv)

/-- Two morphisms into `h_Γ ≅ G ⊆ h_E` with the same image in `P`, one of them factoring through
`C ⊆ P`, are equal when `G ×_E (C ×_P E)` lies in the image of a lift `γ` of `W ⊆ C`. -/
theorem eq_of_comp_eq_of_preimage_le_range {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {E Γ Z : BigFppfOver B S hS} {iE : yoneda.obj E ⟶ P} {C : Subfunctor P}
    {W : Subfunctor C.toFunctor} {γ₀ : W.toFunctor ⟶ yoneda.obj E} (hγ₀ : γ₀ ≫ iE = W.ι ≫ C.ι)
    {γ : W.toFunctor ⟶ (C.preimage iE).toFunctor} (hγι : γ ≫ (C.preimage iE).ι = γ₀)
    {G : Subfunctor (yoneda.obj E)} (hGR : G.preimage (C.preimage iE).ι ≤ Subfunctor.range γ)
    (eG : yoneda.obj Γ ≅ G.toFunctor) {a b : yoneda.obj Z ⟶ yoneda.obj Γ}
    (hab : a ≫ eG.hom ≫ G.ι ≫ iE = b ≫ eG.hom ≫ G.ι ≫ iE)
    (hat : ∃ t : yoneda.obj Z ⟶ C.toFunctor, t ≫ C.ι = a ≫ eG.hom ≫ G.ι ≫ iE) : a = b := by
  have : Mono γ₀ := mono_of_mono_fac hγ₀
  have : Mono γ := mono_of_mono_fac hγι
  -- Both morphisms factor through the graph.
  have hfac : ∀ a' : yoneda.obj Z ⟶ yoneda.obj Γ,
      (∃ t : yoneda.obj Z ⟶ C.toFunctor, t ≫ C.ι = a' ≫ eG.hom ≫ G.ι ≫ iE) →
      ∃ a'' : yoneda.obj Z ⟶ W.toFunctor, a'' ≫ γ₀ = a' ≫ eG.hom ≫ G.ι := by
    rintro a' ⟨t, ht⟩
    obtain ⟨ã, hã⟩ := (Subfunctor.mem_obj_iff_exists (C.preimage iE) (a' ≫ eG.hom ≫ G.ι)).1 (by
      show iE.app _ (yonedaEquiv (a' ≫ eG.hom ≫ G.ι)) ∈ C.obj _
      rw [← yonedaEquiv_comp]
      simp only [Category.assoc]
      rw [← ht, yonedaEquiv_comp]
      exact (yonedaEquiv t).2)
    obtain ⟨χ, hχ⟩ := (Subfunctor.mem_obj_iff_exists (Subfunctor.range γ) ã).1 (hGR _ (by
      show (C.preimage iE).ι.app _ (yonedaEquiv ã) ∈ G.obj _
      rw [← yonedaEquiv_comp, hã, ← Category.assoc, yonedaEquiv_comp]
      exact (yonedaEquiv (a' ≫ eG.hom)).2))
    refine ⟨χ ≫ inv (Subfunctor.toRange γ), ?_⟩
    have hinv : inv (Subfunctor.toRange γ) ≫ γ = (Subfunctor.range γ).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι γ).symm
    rw [← hγι, ← Category.assoc, Category.assoc χ, hinv, hχ, hã]
  obtain ⟨a'', ha''⟩ := hfac a hat
  obtain ⟨b'', hb''⟩ := hfac b (hat.imp fun _ ht => ht.trans hab)
  have key : a'' = b'' := by
    rw [← cancel_mono (W.ι ≫ C.ι), ← hγ₀, ← Category.assoc, ← Category.assoc, ha'', hb'']
    simpa only [Category.assoc] using hab
  rw [← Iso.cancel_iso_hom_right a b eG, ← cancel_mono G.ι, Category.assoc, Category.assoc, ← ha'',
    ← hb'', key]

/-- **The graph chart.** Around a point of an open subspace `W` of a closed subspace `C ⊆ P` on
which `C ⟶ X` factors through the étale `p : h_V ⟶ X`, there is an étale chart
`g : h_Γ ⟶ P` from a quasi-compact scheme, over which `P ⟶ X` factors through `p`, whose image
contains the point, and which is a monomorphism over `C`. -/
theorem exists_etaleChart_mono_over_closedSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (P : AlgebraicSpaces B S hS) (q : P.1 ⟶ X) {V : BigFppfOver B S hS}
    (p : yoneda.obj V ⟶ X) (hp : IsEtale B S hS p)
    (hE : ∃ (E : BigFppfOver B S hS) (πE : E ⟶ V) (iE : yoneda.obj E ⟶ P.1),
      IsPullback iE (yoneda.map πE) q p) (C : ClosedSubspaces B S hS P.1)
    (W : Subfunctor C.1.toFunctor) (hW : IsOpenSubspace B S hS W)
    (c : W.toFunctor ⟶ yoneda.obj V) (hc : W.ι ≫ C.1.ι ≫ q = c ≫ p)
    (w : points B S hS W.toFunctor) :
    ∃ (Γ : BigFppfOver B S hS) (g : yoneda.obj Γ ⟶ P.1) (h : yoneda.obj Γ ⟶ yoneda.obj V),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Γ) ∧ IsEtale B S hS g ∧ g ≫ q = h ≫ p ∧
      pointsMap B S hS _ (W.ι ≫ C.1.ι) w ∈ Set.range (pointsMap B S hS _ g) ∧
      ∀ (Z : BigFppfOver B S hS) (a b : yoneda.obj Z ⟶ yoneda.obj Γ), a ≫ g = b ≫ g →
        (∃ t : yoneda.obj Z ⟶ C.1.toFunctor, t ≫ C.1.ι = a ≫ g) → a = b := by
  classical
  obtain ⟨E, πE, iE, hsq⟩ := hE
  have hEalg : IsAlgebraicSpace B S hS (yoneda.obj E) := isAlgebraicSpace_yoneda B S hS E
  have hiE : IsEtale B S hS iE :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq hEalg P.2
      (isAlgebraicSpace_yoneda B S hS V) hX hp
  -- The base change of `C` to the chart `E = P ×_X V`, and the graph of `c`.
  let CE : Subfunctor (yoneda.obj E) := C.1.preimage iE
  have hCE : IsClosedSubspace B S hS CE := isClosedSubspace_preimage_yoneda B S hS P iE C
  let γ₀ : W.toFunctor ⟶ yoneda.obj E := hsq.lift (W.ι ≫ C.1.ι) c (by rw [Category.assoc, hc])
  have hγ₀ : γ₀ ≫ iE = W.ι ≫ C.1.ι := hsq.lift_fst _ _ _
  have hle : Subfunctor.range γ₀ ≤ CE := by
    rintro Z _ ⟨x, rfl⟩
    show (γ₀ ≫ iE).app Z x ∈ C.1.obj Z
    rw [hγ₀]
    exact (W.ι.app Z x).2
  let γ : W.toFunctor ⟶ CE.toFunctor := Subfunctor.lift γ₀ hle
  have hγι : γ ≫ CE.ι = γ₀ := Subfunctor.lift_ι γ₀ hle
  let R : Subfunctor CE.toFunctor := Subfunctor.range γ
  have hR : IsOpenSubspace B S hS R := isOpenSubspace_range_of_isAlgebraicSpace B S hS hW.1 γ
    (isOpenImmersion_lift_of_comp_eq B S hS hiE C hW hγ₀ hle)
  have : Mono γ₀ := mono_of_mono_fac hγ₀
  have : Mono γ := mono_of_mono_fac hγι
  have hRpts : Set.range (pointsMap B S hS R.toFunctor R.ι) =
      Set.range (pointsMap B S hS _ γ) := range_pointsMap_ι_range B S hS γ
  -- An open set of `|E|` cutting out the graph on `|C ×_P E|`.
  obtain ⟨O, hO, hOR⟩ := (isInducing_pointsMap_of_isImmersion B S hS hEalg CE.ι
    (isImmersion_of_isClosedImmersion B S hS hCE.2)).isOpen_iff.1
    (isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hCE.1 R hR)
  have he₀O : pointsMap B S hS _ γ₀ w ∈ O := by
    rw [← hγι, pointsMap_comp_apply, ← Set.mem_preimage, hOR, hRpts]
    exact ⟨w, rfl⟩
  obtain ⟨G, Γ, eG, hG, hGO, ⟨e, he⟩, hΓ⟩ := exists_compactChart_of_mem_isOpen B S hS hO he₀O
  have hGR : G.preimage CE.ι ≤ R := by
    refine le_of_range_pointsMap_ι_subset B S hS hR ?_
    rw [range_pointsMap_preimage_ι]
    intro x hx
    have : x ∈ pointsMap B S hS CE.toFunctor CE.ι ⁻¹' O := hGO hx
    rwa [hOR] at this
  refine ⟨Γ, eG.hom ≫ G.ι ≫ iE, eG.hom ≫ G.ι ≫ yoneda.map πE, hΓ, ?_,
    by simp only [Category.assoc, hsq.w], ⟨e, ?_⟩,
    fun Z a b hab hat => eq_of_comp_eq_of_preimage_le_range B S hS hγ₀ hγι hGR eG hab hat⟩
  · exact isEtale_comp B S hS
      (isEtale_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _))
      (isEtale_comp B S hS (isEtale_ι_of_isOpenSubspace hG) hiE)
  · rw [← Category.assoc, pointsMap_comp_apply B S hS _ iE, he, ← pointsMap_comp_apply, hγ₀]

/-- **A closed subspace of a finite and finitely presented space which factors locally through an
étale chart is contained in one of finite presentation which is a scheme, and factors Zariski
locally through that chart.** The closed subspace of finite presentation can in addition be asked
to satisfy a chart condition satisfied by `C`. -/
theorem exists_isFinitePresentation_factorsZariskiLocallyThrough_of_closedSubspace
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (P : AlgebraicSpaces B S hS) (hPqc : IsQuasiCompactSpace B S hS P.1)
    (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1) (q : P.1 ⟶ X) {V : BigFppfOver B S hS}
    (p : yoneda.obj V ⟶ X) (hp : IsEtale B S hS p)
    (hE : ∃ (E : BigFppfOver B S hS) (πE : E ⟶ V) (iE : yoneda.obj E ⟶ P.1),
      IsPullback iE (yoneda.map πE) q p) (C : ClosedSubspaces B S hS P.1)
    (hfac : ∀ x : points B S hS C.1.toFunctor, ∃ W : Subfunctor C.1.toFunctor,
      IsOpenSubspace B S hS W ∧ x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
      ∃ c : W.toFunctor ⟶ yoneda.obj V, W.ι ≫ C.1.ι ≫ q = c ≫ p)
    {m : ℕ} {U : Fin m → BigFppfOver B S hS}
    [∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (U i))]
    (φ : ∀ i, yoneda.obj (U i) ⟶ P.1)
    (hφ : ∀ i, MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale
      (BigFppfOver.toScheme B S hS)) (φ i))
    (J₀ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (U i)).IdealSheafData)
    (hJ₀ : ∀ i, (J₀ i).IsFiniteType) (hJ₀C : ∀ i, J₀ i ≤ chartKer B S hS P C (φ i)) :
    ∃ (T : ClosedSubspaces B S hS P.1) (Y : BigFppfOver B S hS) (e : yoneda.obj Y ≅ T.1.toFunctor),
      IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1 ∧ (∀ i, J₀ i ≤ chartKer B S hS P T (φ i)) ∧
      FactorsZariskiLocallyThrough B S hS p Y (e.hom ≫ T.1.ι ≫ q) := by
  classical
  -- A graph chart at every point of `C`.
  have hloc : ∀ x : points B S hS C.1.toFunctor, ∃ (Γ : BigFppfOver B S hS)
      (g : yoneda.obj Γ ⟶ P.1) (h : yoneda.obj Γ ⟶ yoneda.obj V),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Γ) ∧ IsEtale B S hS g ∧ g ≫ q = h ≫ p ∧
      pointsMap B S hS _ C.1.ι x ∈ Set.range (pointsMap B S hS _ g) ∧
      ∀ (Z : BigFppfOver B S hS) (a b : yoneda.obj Z ⟶ yoneda.obj Γ), a ≫ g = b ≫ g →
        (∃ t : yoneda.obj Z ⟶ C.1.toFunctor, t ≫ C.1.ι = a ≫ g) → a = b := by
    intro x
    obtain ⟨W, hW, ⟨w, rfl⟩, c, hc⟩ := hfac x
    obtain ⟨Γ, g, h, h1, h2, h3, h4, h5⟩ :=
      exists_etaleChart_mono_over_closedSubspace B S hS hX P q p hp hE C W hW c hc w
    exact ⟨Γ, g, h, h1, h2, h3, by rwa [← pointsMap_comp_apply], h5⟩
  choose Γ g h hΓ hg hgh hx hmono using hloc
  -- Finitely many of them cover `|C|`.
  have _ : CompactSpace (points B S hS P.1) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ P.2).1 hPqc
  have hCcpt : IsCompact (Set.range (pointsMap B S hS C.1.toFunctor C.1.ι)) :=
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS P.2 C.1.ι C.2.2).isCompact
  obtain ⟨t, ht⟩ := hCcpt.elim_finite_subcover
    (fun x => Set.range (pointsMap B S hS _ (g x)))
    (fun x => isOpen_range_pointsMap_of_isEtale B S hS (g x) (isAlgebraicSpace_yoneda B S hS _)
      P.2 (hg x))
    (Set.range_subset_iff.2 fun x => Set.mem_iUnion.2 ⟨x, hx x⟩)
  let σ : Fin t.card → points B S hS C.1.toFunctor := fun j => (t.equivFin.symm j).1
  have hC : IsEtaleSectionClosed B S hS (fun j => g (σ j)) C.1 := by
    refine ⟨fun j => preimage_le_range_diagonal_of_forall B S hS _ C.1 (hmono (σ j)), ?_⟩
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    have hσ : σ (t.equivFin ⟨x, hxt⟩) = x := by simp only [σ, Equiv.symm_apply_apply]
    show y ∈ Set.range (pointsMap B S hS _ (g (σ (t.equivFin ⟨x, hxt⟩))))
    rw [hσ]
    exact hyx
  obtain ⟨T, hTfp, hCT, hT, hJT⟩ := exists_isFinitePresentation_isEtaleSectionClosed B S hS hZ P
    hPqc hPqs (fun j => hΓ (σ j)) (fun j => g (σ j)) (fun j => hg (σ j)) C hC φ hφ J₀ hJ₀ hJ₀C
  obtain ⟨Y, e, hY⟩ := exists_iso_yoneda_of_isEtaleSectionClosed B S hS P (fun j => g (σ j))
    (fun j => hg (σ j)) T hT
  refine ⟨T, Y, e, hTfp, hCT, hJT, fun y => ?_⟩
  obtain ⟨j, W, hW, hWrep, hy, c, hc⟩ := hY y
  refine ⟨W, hW, hWrep, hy, c ≫ h (σ j), ?_⟩
  rw [← Category.assoc, ← Category.assoc, Category.assoc W.ι, hc, Category.assoc, hgh,
    Category.assoc]

end AlgebraicGeometry.Space

end
