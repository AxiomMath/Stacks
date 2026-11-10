module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.FlatCapture
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceSquareGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Approximating a closed subspace by closed subspaces of finite presentation

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, `C ⊆ X` a
closed subspace and `p : U ⟶ X` an étale morphism from a quasi-compact scheme of the site. For
every finite type sheaf of ideals `J₀` on `U` contained in the ideal sheaf of the base change of
`C`, there is a closed subspace `T ⊇ C` of finite presentation whose ideal sheaf on `U` still
contains `J₀`. This is the ideal-sheaf form, for the structure sheaf, of Stacks 0829, compatible
with a chart; it is an input of Stacks 0860.

## Main definitions

* `AlgebraicGeometry.Space.idealPoints`: the functor of points of the closed subscheme of an
  object of the site cut out by a sheaf of ideals.
* `AlgebraicGeometry.Space.HasFinitePresentationApproximation`: the approximation property of an
  algebraic space, which is the statement proved by induction.

## Main results

* `AlgebraicGeometry.Space.idealPoints_le_iff`, `AlgebraicGeometry.Space.idealPoints_comap`,
  `AlgebraicGeometry.Space.idealPoints_ker_rep_snd`: the dictionary between sheaves of ideals on
  a chart and subfunctors of it.
* `AlgebraicGeometry.Space.exists_closedSubspace_approx_of_isAffineSpace`: the affine case, with
  a prescription on one quasi-compact open subspace.
* `AlgebraicGeometry.Space.hasFinitePresentationApproximation_of_isElementaryDistinguishedSquare`:
  the induction step across an elementary distinguished square.
* `AlgebraicGeometry.Space.exists_isFinitePresentation_le_chartKer`: **the approximation
  theorem.**

## Implementation notes

The source reaches Stacks 0829 for algebraic spaces through Noetherian approximation, Stacks
07V9. Here it is proved by the induction principle of Stacks 08GP instead. The statement carried
through the induction needs no prescription on opens; only the affine case does, with the single
open over which the step has already approximated the closed subspace. On an affine space the
statement is `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_comap_eq_of_flat` on the
representing scheme, the chart being flat; the two approximations of a step are glued by
`AlgebraicGeometry.Space.squareGlue`.

Conditions on a chart are carried as inclusions of subfunctors of its representable presheaf,
through `AlgebraicGeometry.Space.idealPoints`, which makes them local for the fppf coverings
used in the step; the final statement is translated back to
`AlgebraicGeometry.Space.chartKer` by `AlgebraicGeometry.Space.le_chartKer_iff`.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed subschemes of a chart, read as subfunctors -/

section Dictionary

/-- The functor of points of the closed subscheme cut out by a sheaf of ideals on an object of
the site. -/
abbrev idealPoints {U : BigFppfOver B S hS}
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) : Subfunctor (yoneda.obj U) :=
  subschemePoints B S hS (Subobject.mk J.subschemeι)

variable {B S hS}

/-- The arrow of the subobject of a closed subscheme is a closed immersion. -/
theorem isClosedImmersion_arrow_mk_subschemeι {X : Scheme.{u}} (J : X.IdealSheafData) :
    _root_.AlgebraicGeometry.IsClosedImmersion (Subobject.mk J.subschemeι).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- **The functor of points reverses the order of ideal sheaves, and reflects it.** -/
theorem idealPoints_le_iff {U : BigFppfOver B S hS}
    {I J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData} :
    idealPoints B S hS J ≤ idealPoints B S hS I ↔ I ≤ J := by
  refine ⟨fun h => ?_, fun h T x hx => ?_⟩
  swap
  · rw [mem_subschemePoints_iff] at hx ⊢
    exact Subobject.factors_of_le _ (Subobject.mk_le_mk_of_comm
      (Scheme.IdealSheafData.inclusion h) (Scheme.IdealSheafData.inclusion_subschemeι h)) hx
  have hZ : _root_.AlgebraicGeometry.IsImmersion (Subobject.mk J.subschemeι).arrow :=
    have := isClosedImmersion_arrow_mk_subschemeι J
    inferInstance
  have hle : Subobject.mk J.subschemeι ≤ Subobject.mk I.subschemeι := by
    refine Subobject.le_of_factors ?_
    have h₁ : subschemeι B S hS _ hZ ∈ (idealPoints B S hS J).obj
        (op (subschemeObject B S hS _ hZ)) :=
      (mem_subschemePoints_iff B S hS _).2 (Subobject.factors_self _)
    exact (mem_subschemePoints_iff B S hS _).1 (h _ h₁)
  calc I = I.subschemeι.ker := I.ker_subschemeι.symm
    _ ≤ (Subobject.ofMkLEMk _ _ hle ≫ I.subschemeι).ker := Scheme.Hom.le_ker_comp _ _
    _ = J := by rw [Subobject.ofMkLEMk_comp, Scheme.IdealSheafData.ker_subschemeι]

/-- The functor of points of an inverse image is the preimage of the functor of points. -/
theorem idealPoints_comap {U V : BigFppfOver B S hS} (r : V ⟶ U)
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    idealPoints B S hS (J.comap ((BigFppfOver.toScheme B S hS).map r)) =
      (idealPoints B S hS J).preimage (yoneda.map r) := by
  rw [idealPoints, ← Scheme.IdealSheafData.pullback_subobject_mk_subschemeι,
    subschemePoints_pullback]

/-- Membership in the functor of points of an inverse image. -/
theorem mem_idealPoints_comap {U V W : BigFppfOver B S hS} (r : V ⟶ U)
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) (k : W ⟶ V) :
    k ∈ (idealPoints B S hS (J.comap ((BigFppfOver.toScheme B S hS).map r))).obj (op W) ↔
      k ≫ r ∈ (idealPoints B S hS J).obj (op W) := by
  rw [idealPoints_comap]
  rfl

/-- The closed subscheme cut out by the base change of a closed immersion along a chart has the
preimage of the source as its functor of points. -/
theorem idealPoints_ker_rep_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {D : Subfunctor X}
    (hD : IsClosedImmersion B S hS D.ι) {U : BigFppfOver B S hS} (ψ : yoneda.obj U ⟶ X) :
    idealPoints B S hS ((BigFppfOver.toScheme B S hS).map (hD.rep.snd ψ)).ker = D.preimage ψ := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hD.rep.snd ψ)) := hD.property_snd ψ
  rw [idealPoints, Scheme.subobject_mk_ker_subschemeι,
    subschemePoints_eq_range B S hS (hD.rep.snd ψ) (Subobject.underlyingIso _).symm
      (Subobject.underlyingIso_arrow _), range_yoneda_snd_eq_preimage B S hS ψ hD.rep]

/-- The closed subscheme cut out by a sheaf of ideals is a closed subspace. -/
theorem isClosedSubspace_idealPoints {U : BigFppfOver B S hS}
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    IsClosedSubspace B S hS (idealPoints B S hS J) := by
  have hZci := isClosedImmersion_arrow_mk_subschemeι J
  have hZimm : _root_.AlgebraicGeometry.IsImmersion (Subobject.mk J.subschemeι).arrow :=
    inferInstance
  rw [idealPoints, subschemePoints_eq_range B S hS (subschemeι B S hS _ hZimm) (Iso.refl _)
    (Category.id_comp _)]
  exact isClosedSubspace_range_yoneda_map B S hS _ hZci

/-- A closed subspace whose preimage along a chart is the closed subscheme cut out by `J` has
`J` as its chart ideal sheaf there. -/
theorem ker_rep_snd_eq_of_preimage_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {D : Subfunctor X}
    (hD : IsClosedImmersion B S hS D.ι) {U : BigFppfOver B S hS} (ψ : yoneda.obj U ⟶ X)
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (h : D.preimage ψ = idealPoints B S hS J) :
    ((BigFppfOver.toScheme B S hS).map (hD.rep.snd ψ)).ker = J := by
  rw [← idealPoints_ker_rep_snd hD ψ] at h
  exact le_antisymm (idealPoints_le_iff.1 h.ge) (idealPoints_le_iff.1 h.le)

/-- Preimages along an isomorphism reflect inclusions of subfunctors. -/
theorem le_of_preimage_le_of_iso {C : Type*} [Category C] {F G : C ⥤ Type u} (e : F ≅ G)
    {A A' : Subfunctor G} (h : A.preimage e.hom ≤ A'.preimage e.hom) : A ≤ A' := by
  have key : ∀ A : Subfunctor G, (A.preimage e.hom).preimage e.inv = A := fun A => by
    rw [← Subfunctor.preimage_comp, e.inv_hom_id, Subfunctor.preimage_id]
  rw [← key A, ← key A']
  exact fun _ x hx => h _ hx

/-- Inclusions of preimages transfer along a commuting square of morphisms. -/
private theorem preimage_preimage_le_preimage_of_comp_eq {C : Type*} [Category C]
    {X Y Y' P : C ⥤ Type u} {D : Subfunctor X} {E : Subfunctor Y} {g : Y ⟶ X} {h : Y' ⟶ X}
    {a : P ⟶ Y} {b : P ⟶ Y'} (w : a ≫ g = b ≫ h) (hDE : D.preimage g ≤ E) :
    (D.preimage h).preimage b ≤ E.preimage a := by
  rw [← Subfunctor.preimage_comp, ← w, Subfunctor.preimage_comp]
  exact fun _ x hx => hDE _ hx

end Dictionary

/-! ### The affine case -/

section Affine

variable {B S hS}

/-- The core of the affine case, with at most one open subspace on which the closed subspace is
prescribed. -/
private theorem exists_approx_of_isAffineSpace_aux {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYa : IsAffineSpace B S hS Y)
    {C : Subfunctor Y} (hC : IsClosedSubspace B S hS C)
    {ι : Type} [Finite ι] [Subsingleton ι] (Ω : ι → Subfunctor Y)
    (hΩ : ∀ i, IsOpenSubspace B S hS (Ω i))
    (hΩqc : ∀ i, IsQuasiCompactSpace B S hS (Ω i).toFunctor)
    (T₀ : ∀ i, Subfunctor (Ω i).toFunctor) (hT₀ : ∀ i, IsClosedSubspace B S hS (T₀ i))
    (hT₀f : ∀ i, IsFinitePresentation B S hS (T₀ i).ι)
    (hCT₀ : ∀ i, C.preimage (Ω i).ι ≤ T₀ i)
    {U : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (p : yoneda.obj U ⟶ Y)
    (hp : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf p)
    (J₀ : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) (hJ₀ : J₀.IsFiniteType)
    (hCp : C.preimage p ≤ idealPoints B S hS J₀)
    (hT₀p : ∀ (i : ι) (W : BigFppfOver B S hS) (k : W ⟶ U) (ω : (Ω i).toFunctor.obj (op W)),
      (Ω i).ι.app (op W) ω = p.app (op W) k → ω ∈ (T₀ i).obj (op W) →
        k ∈ (idealPoints B S hS J₀).obj (op W)) :
    ∃ T : Subfunctor Y, IsClosedSubspace B S hS T ∧ IsFinitePresentation B S hS T.ι ∧ C ≤ T ∧
      (∀ i, T.preimage (Ω i).ι = T₀ i) ∧ T.preimage p ≤ idealPoints B S hS J₀ := by
  classical
  obtain ⟨Y₀, hY₀, ⟨e⟩⟩ := hYa
  let F := BigFppfOver.toScheme B S hS
  have : IsAffine (F.obj Y₀) := hY₀
  let φ : yoneda.obj Y₀ ⟶ Y := e.inv
  have hRIe : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) F).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have hRIs : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) F).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have isoE : ∀ {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G ⟶ H) [IsIso g],
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) F).presheaf g := fun g _ =>
    presheaf_of_isIso B S hS hRIe
      (fun V => by
        change _root_.AlgebraicGeometry.Etale (F.map (𝟙 V))
        rw [F.map_id]
        infer_instance) g
  have isoS : ∀ {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G ⟶ H) [IsIso g],
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) F).presheaf g := fun g _ =>
    presheaf_of_isIso B S hS hRIs
      (fun V => by
        change _root_.AlgebraicGeometry.Surjective (F.map (𝟙 V))
        rw [F.map_id]
        infer_instance) g
  -- the closed subscheme of `Y₀` underlying `C`
  set K := (F.map (hC.2.rep.snd φ)).ker with hKdef
  have hK : idealPoints B S hS K = C.preimage φ := idealPoints_ker_rep_snd hC.2 φ
  -- the opens of `Y₀` underlying the `Ω i`
  let V₁ : ι → BigFppfOver B S hS := fun i => (hΩ i).2.rep.pullback φ
  let s₀ : ∀ i, V₁ i ⟶ Y₀ := fun i => (hΩ i).2.rep.snd φ
  let b : ∀ i, yoneda.obj (V₁ i) ⟶ (Ω i).toFunctor := fun i => (hΩ i).2.rep.fst φ
  have sq0 : ∀ i, IsPullback (b i) (yoneda.map (s₀ i)) (Ω i).ι φ := fun i =>
    (hΩ i).2.rep.isPullback φ
  have hbiso : ∀ i, IsIso (b i) := fun i => (sq0 i).isIso_fst_of_isIso
  let A : ∀ i, F.obj (V₁ i) ⟶ F.obj Y₀ := fun i => F.map (s₀ i)
  have : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (A i) := fun i =>
    (hΩ i).2.property_snd φ
  have : ∀ i, CompactSpace (F.obj (V₁ i)) := fun i =>
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS (asIso (b i)).symm (hΩqc i))
  -- the ideal sheaves on the opens underlying the `T₀ i`
  let I : ∀ i, (F.obj (V₁ i)).IdealSheafData := fun i => (F.map ((hT₀ i).2.rep.snd (b i))).ker
  have hI : ∀ i, idealPoints B S hS (I i) = (T₀ i).preimage (b i) := fun i =>
    idealPoints_ker_rep_snd (hT₀ i).2 (b i)
  have hIft : ∀ i, (I i).IsFiniteType := fun i =>
    (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (Z := ⟨(T₀ i).toFunctor, (hT₀ i).1⟩) (X := ⟨(Ω i).toFunctor, (hΩ i).1⟩)
      (ObjectProperty.homMk (T₀ i).ι) (hT₀ i).2 (isoE (b i)) (isoS (b i))).1 (hT₀f i)
  have hIK : ∀ i, I i ≤ K.comap (A i) := by
    intro i
    rw [← idealPoints_le_iff, idealPoints_comap, hK, hI]
    exact preimage_preimage_le_preimage_of_comp_eq (sq0 i).w (hCT₀ i)
  -- the chart
  set q' : U ⟶ Y₀ := yoneda.preimage (p ≫ e.hom) with hq'def
  have hq' : yoneda.map q' = p ≫ e.hom := yoneda.map_preimage _
  have hq'φ : yoneda.map q' ≫ φ = p := by rw [hq', Category.assoc, e.hom_inv_id, Category.comp_id]
  let q := F.map q'
  have : _root_.AlgebraicGeometry.Etale q := by
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q').1 ?_
    rw [hq']
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ e.hom).2 hp
  have hJ₀K : J₀ ≤ K.comap q := by
    rwa [← idealPoints_le_iff, idealPoints_comap, hK, ← Subfunctor.preimage_comp, hq'φ]
  have hIDI : ∀ i, J₀.comap (pullback.fst q (A i)) ≤ (I i).comap (pullback.snd q (A i)) := by
    intro i
    have hsr : yoneda.relativelyRepresentable (yoneda.map (s₀ i)) :=
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (s₀ i)).2 inferInstance).rep
    set r := hsr.snd (yoneda.map q') with hrdef
    set s' : hsr.pullback (yoneda.map q') ⟶ V₁ i := yoneda.preimage (hsr.fst (yoneda.map q'))
    have hs' : yoneda.map s' = hsr.fst (yoneda.map q') := yoneda.map_preimage _
    have sqY : IsPullback (yoneda.map s') (yoneda.map r) (yoneda.map (s₀ i)) (yoneda.map q') := by
      rw [hs']
      exact hsr.isPullback _
    have hw : s' ≫ s₀ i = r ≫ q' :=
      yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact sqY.w)
    have sqS := (IsPullback.of_map yoneda hw sqY).map F
    have sqS' : IsPullback (F.map r) (F.map s') q (A i) := sqS.flip
    have key : J₀.comap (F.map r) ≤ (I i).comap (F.map s') := by
      rw [← idealPoints_le_iff]
      intro W k hk
      rw [mem_idealPoints_comap] at hk ⊢
      rw [hI] at hk
      refine hT₀p i W.unop (k ≫ r) _ ?_ hk
      have h1 := congrArg (fun m => m.app W (k ≫ s')) (sq0 i).w
      have h2 := congrArg (fun m => m.app W (k ≫ r)) hq'φ
      simp only [NatTrans.comp_app_apply, yoneda_map_app] at h1 h2
      change (Ω i).ι.app W ((b i).app W (k ≫ s')) = _
      rw [h1, ← h2]
      change φ.app W ((k ≫ s') ≫ s₀ i) = φ.app W ((k ≫ r) ≫ q')
      rw [Category.assoc, hw, Category.assoc]
    have hback : ∀ M : (pullback q (A i)).IdealSheafData,
        (M.comap sqS'.isoPullback.hom).comap sqS'.isoPullback.inv = M := fun M => by
      rw [← Scheme.IdealSheafData.comap_comp, sqS'.isoPullback.inv_hom_id,
        Scheme.IdealSheafData.comap_id]
    have key' : (J₀.comap (pullback.fst q (A i))).comap sqS'.isoPullback.hom ≤
        ((I i).comap (pullback.snd q (A i))).comap sqS'.isoPullback.hom := by
      rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        sqS'.isoPullback_hom_fst, sqS'.isoPullback_hom_snd]
    have h3 : ((J₀.comap (pullback.fst q (A i))).comap sqS'.isoPullback.hom).comap
        sqS'.isoPullback.inv ≤ (((I i).comap (pullback.snd q (A i))).comap
          sqS'.isoPullback.hom).comap sqS'.isoPullback.inv :=
      Scheme.IdealSheafData.comap_mono sqS'.isoPullback.inv key'
    rwa [hback, hback] at h3
  obtain ⟨J, hJft, hJK, hJA, hJq⟩ :=
    Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_comap_eq_of_flat K A I hIft
      (fun i j => by rw [Subsingleton.elim i j]) hIK q J₀ hJ₀ hJ₀K hIDI
  -- the closed subspace
  set T : Subfunctor Y := (idealPoints B S hS J).preimage e.hom with hTdef
  have hTφ : T.preimage φ = idealPoints B S hS J := by
    rw [hTdef, ← Subfunctor.preimage_comp, e.inv_hom_id, Subfunctor.preimage_id]
  have hTc : IsClosedSubspace B S hS T :=
    isClosedSubspace_preimage B S hS e.hom _ (isAlgebraicSpace_yoneda B S hS Y₀) hY
      (isClosedSubspace_idealPoints J)
  have hTf : IsFinitePresentation B S hS T.ι := by
    refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (Z := ⟨T.toFunctor, hTc.1⟩) (X := ⟨Y, hY⟩) (ObjectProperty.homMk T.ι) hTc.2
      (isoE φ) (isoS φ)).2 fun A' => ?_
    rw [ker_rep_snd_eq_of_preimage_eq hTc.2 φ hTφ]
    exact hJft A'
  refine ⟨T, hTc, hTf, ?_, fun i => ?_, ?_⟩
  · refine le_of_preimage_le_of_iso e.symm ?_
    change C.preimage φ ≤ T.preimage φ
    rw [← hK, hTφ]
    exact idealPoints_le_iff.2 hJK
  · have hb : ∀ G G' : Subfunctor (Ω i).toFunctor, G.preimage (b i) = G'.preimage (b i) →
        G = G' := fun G G' hGG' =>
      le_antisymm (le_of_preimage_le_of_iso (asIso (b i)) hGG'.le)
        (le_of_preimage_le_of_iso (asIso (b i)) hGG'.ge)
    refine hb _ _ ?_
    rw [← Subfunctor.preimage_comp, (sq0 i).w, Subfunctor.preimage_comp, hTφ, ← hI, ← hJA i,
      idealPoints_comap]
  · rw [← hq'φ, Subfunctor.preimage_comp, hTφ, ← idealPoints_comap]
    exact idealPoints_le_iff.2 hJq

/-- **The affine case of the approximation, with a prescription on one open subspace.** Let `Y`
be an affine algebraic space, `C ⊆ Y` a closed subspace, `Ω ⊆ Y` a quasi-compact open subspace
carrying a closed subspace `T₀ ⊆ Ω` of finite presentation which contains `C ∩ Ω`, and let
`p : U ⟶ Y` be an étale chart by a quasi-compact scheme carrying a finite type sheaf of ideals
`J₀` which vanishes on the base change of `C` and, over `Ω`, on that of `T₀`. Then there is a
closed subspace `T ⊆ Y` of finite presentation containing `C`, restricting to `T₀` on `Ω`, and
on whose base change to `U` the ideal `J₀` vanishes.

On the affine scheme representing `Y` this is
`Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_comap_eq_of_flat`, the chart being flat
because it is étale. -/
theorem exists_closedSubspace_approx_of_isAffineSpace {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYa : IsAffineSpace B S hS Y)
    {C : Subfunctor Y} (hC : IsClosedSubspace B S hS C)
    {Ω : Subfunctor Y} (hΩ : IsOpenSubspace B S hS Ω)
    (hΩqc : IsQuasiCompactSpace B S hS Ω.toFunctor)
    {T₀ : Subfunctor Ω.toFunctor} (hT₀ : IsClosedSubspace B S hS T₀)
    (hT₀f : IsFinitePresentation B S hS T₀.ι) (hCT₀ : C.preimage Ω.ι ≤ T₀)
    {U : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (p : yoneda.obj U ⟶ Y)
    (hp : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf p)
    (J₀ : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) (hJ₀ : J₀.IsFiniteType)
    (hCp : C.preimage p ≤ idealPoints B S hS J₀)
    (hT₀p : ∀ (W : BigFppfOver B S hS) (k : W ⟶ U) (ω : Ω.toFunctor.obj (op W)),
      Ω.ι.app (op W) ω = p.app (op W) k → ω ∈ T₀.obj (op W) →
        k ∈ (idealPoints B S hS J₀).obj (op W)) :
    ∃ T : Subfunctor Y, IsClosedSubspace B S hS T ∧ IsFinitePresentation B S hS T.ι ∧ C ≤ T ∧
      T.preimage Ω.ι = T₀ ∧ T.preimage p ≤ idealPoints B S hS J₀ := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := exists_approx_of_isAffineSpace_aux hY hYa hC (ι := Unit)
    (fun _ => Ω) (fun _ => hΩ) (fun _ => hΩqc) (fun _ => T₀) (fun _ => hT₀) (fun _ => hT₀f)
    (fun _ => hCT₀) p hp J₀ hJ₀ hCp (fun _ => hT₀p)
  exact ⟨T, h1, h2, h3, h4 (), h5⟩

end Affine

/-! ### The induction -/

section Induction

/-- The approximation property of an algebraic space `Y`: every closed subspace is contained in a
closed subspace of finite presentation, compatibly with any finite type sheaf of ideals on a
quasi-compact étale chart which vanishes on the base change of the given closed subspace. -/
def HasFinitePresentationApproximation (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (_ : IsAlgebraicSpace B S hS Y) (C : Subfunctor Y), IsClosedSubspace B S hS C →
    ∀ (U : BigFppfOver B S hS) [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
      (p : yoneda.obj U ⟶ Y),
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf p →
      ∀ J₀ : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData, J₀.IsFiniteType →
        C.preimage p ≤ idealPoints B S hS J₀ →
        ∃ T : Subfunctor Y, IsClosedSubspace B S hS T ∧ IsFinitePresentation B S hS T.ι ∧
          C ≤ T ∧ T.preimage p ≤ idealPoints B S hS J₀

variable {B S hS}

/-- An affine algebraic space has the approximation property. -/
theorem hasFinitePresentationApproximation_of_isAffineSpace {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hYa : IsAffineSpace B S hS Y) : HasFinitePresentationApproximation B S hS Y := by
  intro hY C hC U _ p hp J₀ hJ₀ hCp
  obtain ⟨T, h1, h2, h3, -, h5⟩ := exists_approx_of_isAffineSpace_aux hY hYa hC (ι := Empty)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) p hp J₀ hJ₀ hCp (fun i => i.elim)
  exact ⟨T, h1, h2, h3, h5⟩

/-- A scheme of the site sitting in a cartesian square over a quasi-separated algebraic space,
opposite a quasi-compact space and over a quasi-compact space, is quasi-compact. -/
private theorem compactSpace_of_isPullback_aux (hZ : B.Contains (⊤_ Scheme.{u}))
    {W Ω G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W) (hΩqc : IsQuasiCompactSpace B S hS Ω)
    (ι : Ω ⟶ W) (hG : IsAlgebraicSpace B S hS G) (hGqc : IsQuasiCompactSpace B S hS G)
    (g : G ⟶ W) {U' : BigFppfOver B S hS} (a : yoneda.obj U' ⟶ Ω) (b : yoneda.obj U' ⟶ G)
    (sq : IsPullback a b ι g) : CompactSpace ((BigFppfOver.toScheme B S hS).obj U') :=
  compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (isQuasiCompactSpace_of_iso B S hS sq.flip.isoPullback.symm
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hW hWqs hΩqc ι G hG hGqc g))

/-- **The induction step.** The approximation property crosses an elementary distinguished
square `(U₀ ⊂ W, f : V ⟶ W)` with `W` quasi-separated, `U₀` quasi-compact and `V` affine.

The closed subspace is approximated on `U₀` by the induction hypothesis, with the chart restricted
over `U₀`; on the affine `V` it is approximated by
`AlgebraicGeometry.Space.exists_closedSubspace_approx_of_isAffineSpace`, prescribed on the
preimage of `U₀` by the approximation already found and with the chart pulled back to `V`; and
the two are glued by `AlgebraicGeometry.Space.squareGlue`. -/
theorem hasFinitePresentationApproximation_of_isElementaryDistinguishedSquare
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W) {U₀ : Subfunctor W} {f : V ⟶ W}
    (h : IsElementaryDistinguishedSquare B S hS hW U₀ f)
    (hU₀qc : IsQuasiCompactSpace B S hS U₀.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hP : HasFinitePresentationApproximation B S hS U₀.toFunctor) :
    HasFinitePresentationApproximation B S hS W := by
  classical
  intro _ C hC U _ p hp J₀ hJ₀ hCp
  have hV := h.isAlgebraicSpace
  have hU₀ := h.isOpenSubspace
  have hUqc := isQuasiCompact_yoneda_of_compact B S hS U inferInstance
  have hUa := isAlgebraicSpace_yoneda B S hS U
  -- the chart restricted over `U₀`, and the induction hypothesis there
  have rU := hU₀.2.rep
  set U₁ := rU.pullback p
  set i₀ := rU.snd p
  set p₀ := rU.fst p
  have sq : IsPullback p₀ (yoneda.map i₀) U₀.ι p := rU.isPullback p
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U₁) :=
    compactSpace_of_isPullback_aux hZ hW hWqs hU₀qc U₀.ι hUa hUqc p p₀ (yoneda.map i₀) sq
  have hp₀ : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf p₀ :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip hp
  have hC₀ := isClosedSubspace_preimage B S hS U₀.ι C hW hU₀.1 hC
  have hC₀p : (C.preimage U₀.ι).preimage p₀ ≤
      idealPoints B S hS (J₀.comap ((BigFppfOver.toScheme B S hS).map i₀)) := by
    rw [idealPoints_comap]
    exact preimage_preimage_le_preimage_of_comp_eq sq.w.symm hCp
  obtain ⟨T₀, hT₀, hT₀f, hCT₀, hT₀p₀⟩ := hP hU₀.1 _ hC₀ U₁ p₀ hp₀ _ (hJ₀.comap _) hC₀p
  have hT₀p : ∀ (Y : BigFppfOver B S hS) (k : Y ⟶ U) (ω : U₀.toFunctor.obj (op Y)),
      U₀.ι.app (op Y) ω = p.app (op Y) k → ω ∈ T₀.obj (op Y) →
        k ∈ (idealPoints B S hS J₀).obj (op Y) := by
    intro Y k ω hω hωT
    have hkU : p.app (op Y) k ∈ U₀.obj (op Y) := hω ▸ ω.2
    obtain ⟨k', hk'⟩ := (mem_obj_iff_exists_comp B S hS U₀ sq (op Y) k).1 hkU
    have hp₀k : p₀.app (op Y) k' = ω := by
      have h1 := congrArg (fun m => m.app (op Y) k') sq.w
      simp only [NatTrans.comp_app_apply, yoneda_map_app] at h1
      apply Subtype.ext
      change U₀.ι.app (op Y) (p₀.app (op Y) k') = U₀.ι.app (op Y) ω
      rw [h1]
      change p.app (op Y) (k' ≫ i₀) = _
      rw [hk', hω]
    have hk'm : k' ∈ (T₀.preimage p₀).obj (op Y) := by
      change p₀.app (op Y) k' ∈ T₀.obj (op Y)
      rwa [hp₀k]
    have := hT₀p₀ _ hk'm
    rwa [mem_idealPoints_comap, hk'] at this
  -- the data on the affine `V`
  obtain ⟨V', hV', ⟨e⟩⟩ := hVa
  set ψ : yoneda.obj V' ⟶ W := e.inv ≫ f with hψ
  have rp := hp.rep
  set U' := rp.pullback ψ
  set s : U' ⟶ V' := rp.snd ψ
  set prj : U' ⟶ U := yoneda.preimage (rp.fst ψ)
  have hprj : yoneda.map prj = rp.fst ψ := yoneda.map_preimage _
  have sqV : IsPullback (yoneda.map prj) (yoneda.map s) p ψ := by
    rw [hprj]
    exact rp.isPullback ψ
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U') :=
    compactSpace_of_isPullback_aux hZ hW hWqs hUqc p (isAlgebraicSpace_yoneda B S hS V')
      (IsAffineSpace.isQuasiCompactSpace (isAffineSpace_yoneda B S hS V' hV')) ψ _ _ sqV
  set pV : yoneda.obj U' ⟶ V := yoneda.map s ≫ e.inv
  have hpVf : pV ≫ f = yoneda.map prj ≫ p := by
    rw [Category.assoc, ← hψ, sqV.w]
  have hRIe : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hpV : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf pV := by
    refine (MorphismProperty.cancel_right_of_respectsIso _ _ e.inv).2 ?_
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s).2 (hp.property_snd ψ)
  set Ω := U₀.preimage f
  have hΩ : IsOpenSubspace B S hS Ω := isOpenSubspace_preimage B S hS f U₀ hW hV hU₀
  have hΩqc : IsQuasiCompactSpace B S hS Ω.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (Subfunctor.isPullback_preimage f U₀).flip.isoPullback.symm
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hW hWqs hU₀qc U₀.ι V hV
        (IsAffineSpace.isQuasiCompactSpace ⟨V', hV', ⟨e⟩⟩) f)
  set T₀' : Subfunctor Ω.toFunctor := T₀.preimage (U₀.fromPreimage f)
  have hT₀' : IsClosedSubspace B S hS T₀' :=
    isClosedSubspace_preimage B S hS _ T₀ hU₀.1 hΩ.1 hT₀
  have hT₀'f : IsFinitePresentation B S hS T₀'.ι :=
    isFinitePresentation_of_isPullback B S hS hT₀'.1 hT₀.1 hΩ.1 hU₀.1
      (Subfunctor.isPullback_preimage (U₀.fromPreimage f) T₀) hT₀f
  have hCT₀' : (C.preimage f).preimage Ω.ι ≤ T₀' := by
    exact preimage_preimage_le_preimage_of_comp_eq (Subfunctor.fromPreimage_ι U₀ f) hCT₀
  have hCpV : (C.preimage f).preimage pV ≤
      idealPoints B S hS (J₀.comap ((BigFppfOver.toScheme B S hS).map prj)) := by
    rw [idealPoints_comap]
    exact preimage_preimage_le_preimage_of_comp_eq hpVf.symm hCp
  have hT₀pV : ∀ (Y : BigFppfOver B S hS) (k : Y ⟶ U') (ω : Ω.toFunctor.obj (op Y)),
      Ω.ι.app (op Y) ω = pV.app (op Y) k → ω ∈ T₀'.obj (op Y) →
        k ∈ (idealPoints B S hS (J₀.comap ((BigFppfOver.toScheme B S hS).map prj))).obj
          (op Y) := by
    intro Y k ω hω hωT
    rw [mem_idealPoints_comap]
    refine hT₀p Y (k ≫ prj) ((U₀.fromPreimage f).app (op Y) ω) ?_ hωT
    have h1 := congrArg (fun m => m.app (op Y) ω) (Subfunctor.fromPreimage_ι U₀ f)
    have h2 := congrArg (fun m => m.app (op Y) k) hpVf
    simp only [NatTrans.comp_app_apply, yoneda_map_app] at h1 h2
    rw [h1, hω, h2]
    rfl
  obtain ⟨T₂, hT₂, hT₂f, hCT₂, hT₂Ω, hT₂p⟩ := exists_closedSubspace_approx_of_isAffineSpace hV
    ⟨V', hV', ⟨e⟩⟩ (isClosedSubspace_preimage B S hS f C hW hV hC) hΩ hΩqc hT₀' hT₀'f hCT₀' pV
    hpV _ (hJ₀.comap _) hCpV hT₀pV
  -- the two pieces agree over the square
  have hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₀.toFunctor.obj (op Y)) (b : V.obj (op Y)),
      U₀.ι.app (op Y) a = f.app (op Y) b → (a ∈ T₀.obj (op Y) ↔ b ∈ T₂.obj (op Y)) := by
    intro Y a b hab
    have hb : b ∈ Ω.obj (op Y) := by
      change f.app (op Y) b ∈ U₀.obj (op Y)
      rw [← hab]
      exact a.2
    have hfa : (U₀.fromPreimage f).app (op Y) ⟨b, hb⟩ = a := Subtype.ext hab.symm
    have h2 : b ∈ T₂.obj (op Y) ↔
        (⟨b, hb⟩ : Ω.toFunctor.obj (op Y)) ∈ (T₂.preimage Ω.ι).obj (op Y) := Iff.rfl
    rw [h2, hT₂Ω]
    change a ∈ T₀.obj (op Y) ↔ (U₀.fromPreimage f).app (op Y) ⟨b, hb⟩ ∈ T₀.obj (op Y)
    rw [hfa]
  -- `T₂` vanishes compatibly with the chart
  have hT₂J : ∀ (Y : BigFppfOver B S hS) (k : Y ⟶ U) (v : V.obj (op Y)),
      f.app (op Y) v = p.app (op Y) k → v ∈ T₂.obj (op Y) →
        k ∈ (idealPoints B S hS J₀).obj (op Y) := by
    intro Y k v hv hvT
    set v' : Y ⟶ V' := e.hom.app (op Y) v
    have hev : e.inv.app (op Y) v' = v := by simp [v']
    have hi : yoneda.map k ≫ p = yoneda.map v' ≫ ψ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map, hψ]
      change p.app (op Y) k = f.app (op Y) (e.inv.app (op Y) (e.hom.app (op Y) v))
      rw [← hv]
      exact congrArg _ hev.symm
    set k₂ := rp.lift (yoneda.map k) v' hi
    have hk₂p : k₂ ≫ prj = k :=
      yoneda.map_injective (by rw [Functor.map_comp, hprj, rp.lift_fst])
    have hk₂s : k₂ ≫ s = v' := rp.lift_snd _ _ _
    have hk₂ : k₂ ∈ (T₂.preimage pV).obj (op Y) := by
      change e.inv.app (op Y) (k₂ ≫ s) ∈ T₂.obj (op Y)
      rwa [hk₂s, hev]
    have := hT₂p _ hk₂
    rwa [mem_idealPoints_comap, hk₂p] at this
  -- glue
  set T := squareGlue B S hS U₀ f T₀ T₂ with hTdef
  have hTc := isClosedSubspace_squareGlue hW h hT₀ hT₂ hcompat
  have hTf := isFinitePresentation_squareGlue hW h hT₀ hT₂ hcompat hT₀f hT₂f
  have hpre₀ := preimage_ι_squareGlue hW h hT₂ hcompat
  have hpre₂ := preimage_squareGlue hW h hT₂ hcompat
  refine ⟨T, hTc, hTf, ?_, ?_⟩
  · refine le_of_isElementaryDistinguishedSquare hW h (𝟙 W) hW.isSheaf hTc.1.isSheaf ?_ ?_
    · intro Y y hy hyU
      have : (⟨y, hyU⟩ : U₀.toFunctor.obj (op Y)) ∈ (T.preimage U₀.ι).obj (op Y) := by
        rw [hTdef, hpre₀]
        exact hCT₀ _ hy
      exact this
    · intro Y y v hy hv
      have hvC : v ∈ (C.preimage f).obj (op Y) := by
        change f.app (op Y) v ∈ C.obj (op Y)
        rwa [hv]
      have : v ∈ (T.preimage f).obj (op Y) := by
        rw [hTdef, hpre₂]
        exact hCT₂ _ hvC
      change f.app (op Y) v ∈ T.obj (op Y) at this
      rwa [hv] at this
  · refine le_of_isElementaryDistinguishedSquare hW h p hUa.isSheaf
      (isClosedSubspace_idealPoints J₀).1.isSheaf ?_ ?_
    · intro Y k hk hkU
      have : (⟨p.app (op Y) k, hkU⟩ : U₀.toFunctor.obj (op Y)) ∈ T₀.obj (op Y) := by
        rwa [← hpre₀]
      exact hT₀p Y k _ rfl this
    · intro Y k v hk hv
      have : v ∈ (T.preimage f).obj (op Y) := by
        change f.app (op Y) v ∈ T.obj (op Y)
        rwa [hv]
      rw [hTdef, hpre₂] at this
      exact hT₂J Y k v hv this

end Induction

/-! ### The approximation theorem -/

/-- A sheaf of ideals on a chart vanishes on the base change of a closed subspace exactly when
the closed subscheme it cuts out contains that base change. -/
theorem le_chartKer_iff (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.1)
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    J ≤ chartKer B S hS X D φ ↔ D.1.preimage φ ≤ idealPoints B S hS J := by
  rw [chartKer_eq, ← idealPoints_le_iff, idealPoints_ker_rep_snd D.2.2]

/-- **A closed subspace of a quasi-compact quasi-separated algebraic space is approximated from
above by closed subspaces of finite presentation, compatibly with a quasi-compact étale chart.**
Let `C ⊆ X` be a closed subspace and `p : U ⟶ X` an étale morphism from a quasi-compact scheme of
the site, and let `J₀` be a finite type sheaf of ideals on `U` contained in the ideal sheaf of
the base change of `C` to `U`. Then there is a closed subspace `T ⊆ X` of finite presentation
containing `C` whose ideal sheaf on `U` still contains `J₀`.

This is the ideal-sheaf form of Stacks 0829 for the structure sheaf. It is proved by the
induction principle of Stacks 08GP, `AlgebraicGeometry.Space.qcqs_induction_on_self`, rather than
by Noetherian approximation: the affine case is
`AlgebraicGeometry.Space.exists_closedSubspace_approx_of_isAffineSpace` and the step across an
elementary distinguished square is
`AlgebraicGeometry.Space.hasFinitePresentationApproximation_of_isElementaryDistinguishedSquare`. -/
theorem exists_isFinitePresentation_le_chartKer (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (C : ClosedSubspaces B S hS X.1)
    {U : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (p : yoneda.obj U ⟶ X.1)
    (hp : MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale
      (BigFppfOver.toScheme B S hS)) p)
    (J₀ : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) (hJ₀ : J₀.IsFiniteType)
    (hJ₀C : J₀ ≤ chartKer B S hS X C p) :
    ∃ T : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1 ∧
      J₀ ≤ chartKer B S hS X T p := by
  have hP : HasFinitePresentationApproximation B S hS X.1 :=
    qcqs_induction_on_self B S hS hZ X hXqc hXqs
      (fun Y _ => HasFinitePresentationApproximation B S hS Y)
      (fun V hV => hasFinitePresentationApproximation_of_isAffineSpace hV)
      (fun W V U₀ f _ h _ hWqs hU₀qc hVa hU₀ _ _ =>
        hasFinitePresentationApproximation_of_isElementaryDistinguishedSquare hZ
          W.1.left.property hWqs h hU₀qc hVa
          hU₀)
  obtain ⟨T, hTc, hTf, hCT, hTp⟩ := hP X.2 C.1 C.2 U p hp J₀ hJ₀
    ((le_chartKer_iff B S hS X C p J₀).1 hJ₀C)
  exact ⟨⟨T, hTc⟩, hTf, hCT, (le_chartKer_iff B S hS X ⟨T, hTc⟩ p J₀).2 hTp⟩

end AlgebraicGeometry.Space

end
