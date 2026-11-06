module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FieldPointPreimmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fold5.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsInducingTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksCore.Tactic.StacksAttribute

/-!
# The field fibre is homeomorphic to the set-theoretic fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `y ∈ |Y|` be
represented by a field-valued point `p` whose presenting morphism `Spec(k) ⟶ Y` is a
quasi-compact monomorphism. Stacks 0AC8 says that `|X_k| → |X|` is a homeomorphism of the point
space of the field fibre `X_k = X ×_Y Spec(k)` onto the set-theoretic fibre
`f^{-1}({y}) ⊂ |X|` with its induced topology. This file proves the topological half of that
statement, which `StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreEmbedding.lean` left open: the
comparison map is topologically inducing. Together with the injectivity and the image
computation proved there, the tag is complete.

## Main definitions

* `AlgebraicGeometry.Space.homeomorphSetFibre` is the homeomorphism of Stacks 0AC8 from the
  point space of the field fibre onto the set-theoretic fibre.

## Main results

* `AlgebraicGeometry.Space.isInducing_pointsMap_yoneda_of_isPullback_fieldMorphism` is the case
  of the inducing property in which the source of `f` is a scheme: it is the geometric heart of
  the tag, and the only place quasi-compactness is used.
* `AlgebraicGeometry.Space.isInducing_pointsMap_fst_fieldFibre` is the inducing property in
  general, and `AlgebraicGeometry.Space.isEmbedding_pointsMap_fst_fieldFibre` the resulting
  topological embedding.
* `AlgebraicGeometry.Space.isPreimmersion_toScheme_map_residueFieldMap_comp` and
  `AlgebraicGeometry.BigFppfSite.residueField_spec_contains` are the two facts about
  residue-field points of objects of the site that the argument needs.

## Implementation notes

The source's proof runs as follows. Choose an étale morphism `V ⟶ Y` with `V` affine and a
point `v ∈ |V|` above `y`; quasi-compactness of `Spec(k) ⟶ Y` makes the set of points of `V`
above `y` finite (Tag 03JV,
`AlgebraicGeometry.Space.finite_setFibre_of_isQuasiCompact_fieldMorphism`), so `V` may be shrunk
so that `v` is the only one. Choose an étale atlas `U ⟶ X` by a scheme and compare
`|X_v| → |X_V| → |X|` with the fibre `U_v ⊂ U_V` of a morphism of schemes, which is a
topological embedding by Tag 01K1.

Two departures from that script are forced, and a third is a simplification.

* The shrinking step is performed by
  `AlgebraicGeometry.Space.exists_isOpen_inter_eq_singleton`, which chooses the point `v`
  rather than taking the one it is handed: a point of the fibre need not be isolated in it,
  and one maximal for the specialization order is. The argument needs only one point of the
  fibre, so this costs nothing.
* The fibre `L = V ×_Y Spec(k)` of the shrunken chart is an object of the site with at most
  one point, and `L ⟶ V` is a monomorphism, but it need not be a topological embedding after
  base change, so Tag 01K1 does not apply to it. What is used instead is the residue-field
  point `Spec(κ(L)) ⟶ L ⟶ V`, which is a monomorphism out of the spectrum of a *field* and
  therefore a preimmersion
  (`AlgebraicGeometry.isPreimmersion_of_mono_of_field`); preimmersions are stable under base
  change, which is the form in which Tag 01K1 is used here. The price is that the square
  through which the inducing property is transferred is no longer cartesian — only
  surjective onto a cartesian one — which is why
  `AlgebraicGeometry.Space.isInducing_pointsMap_of_exists_points` is stated with the
  point-lifting hypothesis rather than with a cartesian square.
* The source compares along the chart of `Y` and the atlas of `X` simultaneously. Here the two
  transfers are separate applications of the same lemma: first the statement is reduced to the
  case of a represented source by the atlas of `X`
  (`AlgebraicGeometry.Space.isInducing_pointsMap_fst_fieldFibre`), and inside that case the
  chart of `Y` is used (`...isInducing_pointsMap_yoneda_of_isPullback_fieldMorphism`). The
  reduction direction is the opposite of the source's and needs no new input.

The monomorphism hypothesis is used twice: for the finiteness of the chart fibre through Tag
03JV, and to see that the fibre `L` of the shrunken chart has at most one point. The
quasi-compactness hypothesis is used once, for that same finiteness, and it is what makes the
statement true; the counterexample without it is recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreEmbedding.lean`.

`AlgebraicGeometry.BigFppfSite.residueField_spec_contains` is imported rather than restated.

## References

* [Stacks Project, Tag 01K1](https://stacks.math.columbia.edu/tag/01K1)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_fieldFibreInducing
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Residue-field points of objects of the site -/

/-- **The residue-field point of a monomorphic chart is a preimmersion.** Let `f : L ⟶ V` be a
monomorphism of the big fppf site of `S` and let `ell` be a point of `L`. Then the composite
`Spec(κ(ell)) ⟶ L ⟶ V` is a preimmersion of schemes.

The composite is a monomorphism out of the spectrum of a field, so
`AlgebraicGeometry.isPreimmersion_of_mono_of_field` applies. This is the form in which Tag 01K1
is used in the proof of Stacks 0AC8: `L ⟶ V` itself need not be a preimmersion. -/
theorem isPreimmersion_toScheme_map_residueFieldMap_comp (L V : BigFppfOver B S hS)
    (ell : (BigFppfOver.toScheme B S hS).obj L)
    (hkap : B.Contains (Spec (.of (((BigFppfOver.toScheme B S hS).obj L).residueField ell))))
    (f : L ⟶ V) (hf : Mono f) :
    IsPreimmersion ((BigFppfOver.toScheme B S hS).map
      (residueFieldMap B S hS L ell hkap ≫ f)) := by
  have : Mono (residueFieldMap B S hS L ell hkap) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstanceAs (Mono (((BigFppfOver.toScheme B S hS).obj L).fromSpecResidueField ell)))
  exact @isPreimmersion_of_mono_of_field
    (((BigFppfOver.toScheme B S hS).obj L).residueField ell) _ _ _
    (mono_toScheme_map B S hS (residueFieldMap B S hS L ell hkap ≫ f))

/-! ### The inducing property for a represented source -/

/-- An algebraic space has, at a field-valued point presented by a quasi-compact morphism, an
étale chart whose fibre over the point it represents is a single point. -/
theorem exists_etale_chart_fibre_subsingleton {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : FieldValuedPoint B S hS Y)
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (∃ w, pointsMap B S hS _ b w = p.class B S hS Y) ∧
      ∀ w₁ w₂ : points B S hS (yoneda.obj V), pointsMap B S hS _ b w₁ = p.class B S hS Y →
        pointsMap B S hS _ b w₂ = p.class B S hS Y → w₁ = w₂ := by
  classical
  obtain ⟨V, b, hVaff, hb, v₀, hv₀⟩ :=
    exists_affine_etale_chart_at_point B S hS Y hY (p.class B S hS Y)
  have hVcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) :=
    have := hVaff
    inferInstance
  have hfin : (setFibre B S hS b p).Finite :=
    finite_setFibre_of_isQuasiCompact_fieldMorphism B S hS p hqc hVcpt
      (isEtale_of_presheaf_etale B S hS hb)
  obtain ⟨v, hvF, O₀, hO₀, hvO, hOF⟩ := exists_isOpen_inter_eq_singleton
    (hfin.image (pointsToScheme B S hS V)) ⟨_, Set.mem_image_of_mem _ hv₀⟩
  set O : ((BigFppfOver.toScheme B S hS).obj V).Opens := ⟨O₀, hO₀⟩
  set V' : BigFppfOver B S hS := openSub V O
  set ι : V' ⟶ V := openSubHom V O
  have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map ι) := by
    rw [toScheme_map_openSubHom B S hS V O]
    exact (Scheme.Hom.isEmbedding (O.ι)).injective
  have key : ∀ w : points B S hS (yoneda.obj V'),
      pointsMap B S hS _ (yoneda.map ι ≫ b) w = p.class B S hS Y →
      (BigFppfOver.toScheme B S hS).map ι (pointsToScheme B S hS V' w) = v := by
    intro w hw
    have hmemF : pointsMap B S hS (yoneda.obj V') (yoneda.map ι) w ∈
        setFibre B S hS b p := by
      change pointsMap B S hS _ b _ = _
      rw [← pointsMap_comp_apply]
      exact hw
    have hmemO : (BigFppfOver.toScheme B S hS).map ι (pointsToScheme B S hS V' w) ∈
        (O : Set _) := by
      rw [← Scheme.Opens.range_ι O, toScheme_map_openSubHom B S hS V O]
      exact Set.mem_range_self _
    exact Set.eq_of_mem_singleton
      (hOF.subset ⟨hmemO, ⟨_, hmemF, pointsToScheme_pointsMap_yoneda B S hS ι w⟩⟩)
  obtain ⟨w', hw'F, hw'v⟩ : ∃ w' ∈ setFibre B S hS b p, pointsToScheme B S hS V w' = v :=
    hOF.ge rfl |>.2
  refine ⟨V', yoneda.map ι ≫ b,
    etale_comp_of_scheme B S hS ι b (etale_toScheme_map_openSubHom B S hS V O) hb,
    ⟨(pointsEquivScheme B S hS V').symm ⟨v, hvO⟩, ?_⟩, fun w₁ w₂ h₁ h₂ ↦
      injective_pointsToScheme B S hS V' (hinj ((key w₁ h₁).trans (key w₂ h₂).symm))⟩
  have hps : pointsToScheme B S hS V' ((pointsEquivScheme B S hS V').symm ⟨v, hvO⟩) =
      ⟨v, hvO⟩ := (pointsEquivScheme B S hS V').apply_symm_apply _
  have h₁ : pointsMap B S hS (yoneda.obj V') (yoneda.map ι)
      ((pointsEquivScheme B S hS V').symm ⟨v, hvO⟩) = w' := by
    refine injective_pointsToScheme B S hS V ?_
    rw [pointsToScheme_pointsMap_yoneda B S hS ι, hw'v, toScheme_map_openSubHom B S hS V O,
      hps]
    rfl
  rw [pointsMap_comp_apply, h₁]
  exact hw'F

/-- Let `A₀ = W ×_U P` with `|P| → |U|` open and `|A₀| → |W|` surjective, and let `A₀ ⟶ P` be
a base change of `L ⟶ V`; if `L' ⟶ L ⟶ V` is a preimmersion for some `L' ⟶ L` surjective on
points, then `|W| → |U|` is topologically inducing. -/
theorem isInducing_pointsMap_yoneda_of_isPullback_of_isPreimmersion
    {U W P A₀ V L L' : BigFppfOver B S hS} {j : W ⟶ U} {u : P ⟶ U} {a₀ : A₀ ⟶ W}
    {b₀ : A₀ ⟶ P}
    (hA₀ : IsPullback (yoneda.map a₀) (yoneda.map b₀) (yoneda.map j) (yoneda.map u))
    (hu : IsOpenMap (pointsMap B S hS (yoneda.obj P) (yoneda.map u)))
    (ha₀ : Function.Surjective (pointsMap B S hS (yoneda.obj A₀) (yoneda.map a₀)))
    {fP : P ⟶ V} {fL : L ⟶ V} {c : A₀ ⟶ L}
    (htop : IsPullback (yoneda.map b₀) (yoneda.map c) (yoneda.map fP) (yoneda.map fL))
    {r : L' ⟶ L} (hr : Function.Surjective (pointsMap B S hS (yoneda.obj L') (yoneda.map r)))
    (hpre : IsPreimmersion ((BigFppfOver.toScheme B S hS).map (r ≫ fL))) :
    Topology.IsInducing (pointsMap B S hS (yoneda.obj W) (yoneda.map j)) := by
  set A : BigFppfOver B S hS := Limits.pullback r c
  set cA : A ⟶ L' := Limits.pullback.fst r c
  set bA : A ⟶ A₀ := Limits.pullback.snd r c
  have hAsq : IsPullback (yoneda.map cA) (yoneda.map bA) (yoneda.map r) (yoneda.map c) :=
    yoneda.map_isPullback (IsPullback.of_hasPullback r c)
  have hbA : Function.Surjective (pointsMap B S hS (yoneda.obj A) (yoneda.map bA)) :=
    surjective_pointsMap_of_isPullback B S hS hAsq hr
  have hβsq : IsPullback (yoneda.map cA) (yoneda.map (bA ≫ b₀))
      (yoneda.map (r ≫ fL)) (yoneda.map fP) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact (hAsq.flip.paste_horiz htop).flip
  have hrespects : MorphismProperty.RespectsIso (@IsPreimmersion) :=
    { precomp := fun i hi f hf ↦ by
        have : IsIso i := hi
        have : IsPreimmersion f := hf
        infer_instance
      postcomp := fun i hi f hf ↦ by
        have : IsIso i := hi
        have : IsPreimmersion f := hf
        infer_instance }
  have hbase : IsPreimmersion ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.snd (r ≫ fL) fP)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion)
      ((BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback (r ≫ fL) fP)) hpre
  have hβ : IsPreimmersion ((BigFppfOver.toScheme B S hS).map (bA ≫ b₀)) :=
    property_of_isPullback_of_isPullback B S hS hβsq
      (yoneda.map_isPullback (IsPullback.of_hasPullback (r ≫ fL) fP)) hbase
  have hcomp : ∀ (X : BigFppfOver B S hS) (k : A₀ ⟶ X) (w : points B S hS (yoneda.obj A)),
      pointsMap B S hS _ (yoneda.map (bA ≫ k)) w =
        pointsMap B S hS _ (yoneda.map k) (pointsMap B S hS _ (yoneda.map bA) w) := fun X k w ↦ by
    rw [Functor.map_comp, pointsMap_comp_apply]
  have hα : Function.Surjective (pointsMap B S hS (yoneda.obj A) (yoneda.map (bA ≫ a₀))) := by
    intro z
    obtain ⟨x, hx⟩ := ha₀ z
    obtain ⟨y, hy⟩ := hbA x
    exact ⟨y, by rw [hcomp, hy, hx]⟩
  have hlift : ∀ (z : points B S hS (yoneda.obj W)) (o : points B S hS (yoneda.obj P)),
      pointsMap B S hS _ (yoneda.map j) z = pointsMap B S hS _ (yoneda.map u) o →
      ∃ w : points B S hS (yoneda.obj A),
        pointsMap B S hS _ (yoneda.map (bA ≫ a₀)) w = z ∧
          pointsMap B S hS _ (yoneda.map (bA ≫ b₀)) w = o := by
    intro z o hzo
    obtain ⟨x, hx₁, hx₂⟩ := exists_points_of_isPullback B S hS hA₀ z o hzo
    obtain ⟨w, hw⟩ := hbA x
    exact ⟨w, by rw [hcomp, hw, hx₁], by rw [hcomp, hw, hx₂]⟩
  have hcomm : yoneda.map (bA ≫ a₀) ≫ yoneda.map j = yoneda.map (bA ≫ b₀) ≫ yoneda.map u := by
    simp only [Functor.map_comp, Category.assoc, hA₀.w]
  exact isInducing_pointsMap_of_exists_points B S hS hcomm hu
    (isEmbedding_pointsMap_yoneda B S hS (bA ≫ b₀)
      (Scheme.Hom.isEmbedding ((BigFppfOver.toScheme B S hS).map (bA ≫ b₀)))).isInducing
    hα hlift

/-- The base change of an étale chart `b : h_V ⟶ Y` along `g : h_T ⟶ Y` is a square of the site
whose side `P ⟶ T` is étale. -/
private theorem exists_isPullback_yoneda_map_of_presheaf_etale
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V T : BigFppfOver B S hS} {b : yoneda.obj V ⟶ Y}
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) (g : yoneda.obj T ⟶ Y) :
    ∃ (P : BigFppfOver B S hS) (fP : P ⟶ V) (u : P ⟶ T),
      IsPullback (yoneda.map fP) (yoneda.map u) b g ∧
        Etale ((BigFppfOver.toScheme B S hS).map u) :=
  ⟨hb.rep.pullback g, yoneda.preimage (hb.rep.fst g), hb.rep.snd g, by
    rw [yoneda.map_preimage]
    exact hb.rep.isPullback g, hb.property_snd g⟩

/-- Let `b : h_V ⟶ Y` be étale, `W = U ×_Y T` and `L = V ×_Y T`, with every point of `W` over a
point of the image of `b`; if `L' ⟶ L ⟶ V` is a preimmersion for some `L' ⟶ L` surjective on
points, then `|W| → |U|` is topologically inducing. -/
theorem isInducing_pointsMap_yoneda_of_isPullback_of_etale
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V T U W L L' : BigFppfOver B S hS}
    {b : yoneda.obj V ⟶ Y}
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    {m : yoneda.obj T ⟶ Y} {g : yoneda.obj U ⟶ Y} {j : W ⟶ U} {s : W ⟶ T}
    (hsq : IsPullback (yoneda.map j) (yoneda.map s) g m)
    {fL : L ⟶ V} {sL : L ⟶ T} (hLsq : IsPullback (yoneda.map fL) (yoneda.map sL) b m)
    {r : L' ⟶ L} (hr : Function.Surjective (pointsMap B S hS (yoneda.obj L') (yoneda.map r)))
    (hpre : IsPreimmersion ((BigFppfOver.toScheme B S hS).map (r ≫ fL)))
    (hpts : ∀ z : points B S hS (yoneda.obj W), ∃ w : points B S hS (yoneda.obj V),
      pointsMap B S hS _ b w = pointsMap B S hS _ g (pointsMap B S hS _ (yoneda.map j) z)) :
    Topology.IsInducing (pointsMap B S hS (yoneda.obj W) (yoneda.map j)) := by
  obtain ⟨P, fP, u, hPsq, hPet⟩ := exists_isPullback_yoneda_map_of_presheaf_etale B S hS hb g
  have hu : IsOpenMap (pointsMap B S hS (yoneda.obj P) (yoneda.map u)) := by
    refine isOpenMap_pointsMap_of_presheafEtale B S hS (yoneda.map u) ?_
    have hmul := isMultiplicative_presheaf_etale B S hS
    have hcomp := etale_comp_of_scheme B S hS u (𝟙 (yoneda.obj U))
      hPet (MorphismProperty.id_mem _ _)
    rwa [Category.comp_id] at hcomp
  set A₀ : BigFppfOver B S hS := Limits.pullback j u
  set a₀ : A₀ ⟶ W := Limits.pullback.fst j u
  set b₀ : A₀ ⟶ P := Limits.pullback.snd j u
  have hA₀ : IsPullback (yoneda.map a₀) (yoneda.map b₀) (yoneda.map j) (yoneda.map u) :=
    yoneda.map_isPullback (IsPullback.of_hasPullback j u)
  have hpaste : IsPullback (yoneda.map b₀) (yoneda.map a₀ ≫ yoneda.map s)
      (yoneda.map fP ≫ b) m := by
    rw [hPsq.w]
    exact hA₀.flip.paste_vert hsq
  set c : yoneda.obj A₀ ⟶ yoneda.obj L :=
    hLsq.lift (yoneda.map b₀ ≫ yoneda.map fP) (yoneda.map a₀ ≫ yoneda.map s)
      (by rw [Category.assoc, hpaste.w])
  have hc : yoneda.map (yoneda.preimage c) = c := yoneda.map_preimage _
  have htop : IsPullback (yoneda.map b₀) (yoneda.map (yoneda.preimage c)) (yoneda.map fP)
      (yoneda.map fL) := by
    rw [hc]
    exact hpaste.of_bot' hLsq
  refine isInducing_pointsMap_yoneda_of_isPullback_of_isPreimmersion B S hS hA₀ hu
    (fun z ↦ ?_) htop hr hpre
  obtain ⟨w, hw⟩ := hpts z
  obtain ⟨o, -, ho⟩ := exists_points_of_isPullback B S hS hPsq w _ hw
  obtain ⟨a, ha, -⟩ := exists_points_of_isPullback B S hS hA₀ z o ho.symm
  exact ⟨a, ha⟩

/-- **Stacks 0AC8 for a represented source.** Let `Y` be an algebraic space over `S`, let `p` be
a field-valued point of `Y` whose presenting morphism `Spec(k) ⟶ Y` is a quasi-compact
monomorphism, and let `g : h_U ⟶ Y` be a morphism from a represented presheaf whose fibre
`W = U ×_Y Spec(k)` is presented by a morphism `j : W ⟶ U` of the site. Then `|W| → |U|` is
topologically inducing.

This is the geometric content of the tag. An affine étale chart `V ⟶ Y` through the point
represented by `p` has finite fibre above it by Tag 03JV, so by
`AlgebraicGeometry.Space.exists_isOpen_inter_eq_singleton` it may be shrunk to one on which
some point `v` of that fibre is the only one; the fibre `L` of the shrunken chart is then a
monomorphic image of a subsingleton, and the residue-field point of `L` gives a preimmersion
into the shrunken chart. The inducing property transfers along the resulting square by
`AlgebraicGeometry.Space.isInducing_pointsMap_of_exists_points`, whose lifting hypothesis is
Tag 03H4 for `W ×_U (U ×_Y V)` composed with surjectivity of `Spec(κ(L)) ⟶ L` on points. -/
theorem isInducing_pointsMap_yoneda_of_isPullback_fieldMorphism
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p))
    {U W : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y} {j : W ⟶ U} {s : W ⟶ p.siteObject}
    (hsq : IsPullback (yoneda.map j) (yoneda.map s) g (fieldMorphism B S hS Y p)) :
    Topology.IsInducing (pointsMap B S hS (yoneda.obj W) (yoneda.map j)) := by
  obtain ⟨V, b, hb, ⟨wv, hwv⟩, hsub⟩ :=
    exists_etale_chart_fibre_subsingleton B S hS hY p hqc
  have hpall : ∀ z : points B S hS (yoneda.obj p.siteObject),
      pointsMap B S hS _ (fieldMorphism B S hS Y p) z = p.class B S hS Y := by
    intro z
    induction z using Quot.ind with | _ q =>
    exact FieldValuedPoint.pointsMap_class_eq_class B S hS p q
  obtain ⟨L, fL, sL, hLsq, -⟩ :=
    exists_isPullback_yoneda_map_of_presheaf_etale B S hS hb (fieldMorphism B S hS Y p)
  have hfLmono : Mono (yoneda.map fL) :=
    (MorphismProperty.monomorphisms _).of_isPullback hLsq.flip hmono
  have hLpts : Subsingleton (points B S hS (yoneda.obj L)) := by
    refine ⟨fun w₁ w₂ ↦ pointsMap_injective_of_mono B S hS (yoneda.map fL) (hsub _ _ ?_ ?_)⟩ <;>
      rw [← pointsMap_comp_apply, hLsq.w, pointsMap_comp_apply, hpall]
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS hLsq wv
    ((p.tautologicalPoint B S hS Y).class B S hS (yoneda.obj p.siteObject))
    (hwv.trans (hpall _).symm)
  obtain ⟨ell⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj L) := ⟨pointsToScheme B S hS L w⟩
  have hkap : B.Contains (Spec (.of (((BigFppfOver.toScheme B S hS).obj L).residueField ell))) :=
    B.residueField_spec_contains L.left.property ell
  set L' : BigFppfOver B S hS := residueFieldObject B S hS L ell hkap
  set r : L' ⟶ L := residueFieldMap B S hS L ell hkap
  have hr : Function.Surjective (pointsMap B S hS (yoneda.obj L') (yoneda.map r)) := fun _ ↦
    ⟨(pointsEquivScheme B S hS L').symm (IsLocalRing.closedPoint
      (((BigFppfOver.toScheme B S hS).obj L).residueField ell)), hLpts.elim _ _⟩
  refine isInducing_pointsMap_yoneda_of_isPullback_of_etale B S hS hb hsq hLsq hr
    (isPreimmersion_toScheme_map_residueFieldMap_comp B S hS L V ell hkap fL
      (yoneda.mono_of_mono_map hfLmono)) fun z ↦ ⟨wv, ?_⟩
  rw [hwv, ← pointsMap_comp_apply, hsq.w, pointsMap_comp_apply, hpall]

/-! ### The inducing property, the embedding, and the homeomorphism -/

/-- **Stacks 0AC8, the induced topology.** For a morphism `f : X ⟶ Y` of algebraic spaces over
`S` and a field-valued point `p` of `Y` presented by a quasi-compact monomorphism, the
comparison map `|X_k| → |X|` from the point space of the field fibre is topologically inducing.

An étale atlas `U ⟶ X` is surjective and open on points, and the base change of the comparison
map along it is the comparison map for the composite `h_U ⟶ X ⟶ Y`, which is the subject of
`AlgebraicGeometry.Space.isInducing_pointsMap_yoneda_of_isPullback_fieldMorphism`; the property
transfers by `AlgebraicGeometry.Space.isInducing_pointsMap_of_isPullback`. -/
@[stacks 0AC8 "the induced topology"]
theorem isInducing_pointsMap_fst_fieldFibre {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    Topology.IsInducing (pointsMap B S hS (fieldFibre B S hS f p)
      (pullback.fst f (fieldMorphism B S hS Y p))) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  have hpirep : yoneda.relativelyRepresentable
      (pullback.fst f (fieldMorphism B S hS Y p)) :=
    MorphismProperty.of_isPullback (P := yoneda.relativelyRepresentable)
      (IsPullback.of_hasPullback f (fieldMorphism B S hS Y p)).flip
      (Functor.relativelyRepresentable.of_diag hY.diagonal_representable _)
  have hsq := hpirep.isPullback a
  have hpaste : IsPullback (yoneda.map (hpirep.snd a))
      (hpirep.fst a ≫ pullback.snd f (fieldMorphism B S hS Y p)) (a ≫ f)
      (fieldMorphism B S hS Y p) :=
    hsq.flip.paste_vert (IsPullback.of_hasPullback f (fieldMorphism B S hS Y p))
  have hbeta : Topology.IsInducing
      (pointsMap B S hS (yoneda.obj (hpirep.pullback a)) (yoneda.map (hpirep.snd a))) := by
    refine isInducing_pointsMap_yoneda_of_isPullback_fieldMorphism B S hS hY p hmono hqc
      (g := a ≫ f) (j := hpirep.snd a)
      (s := yoneda.preimage (hpirep.fst a ≫ pullback.snd f (fieldMorphism B S hS Y p))) ?_
    rw [yoneda.map_preimage]
    exact hpaste
  exact isInducing_pointsMap_of_isPullback B S hS hsq
    (isOpenMap_pointsMap_of_presheafEtale B S hS a haEtale) hbeta
    (surjective_pointsMap_of_isPullback B S hS hsq.flip
      (isSurjective_of_presheafSurjective B S hS a haSurj))

/-- **Stacks 0AC8, the embedding.** The comparison map `|X_k| → |X|` is a topological
embedding: it is inducing and, by Tag 06RV for the monomorphism `X_k ⟶ X`, injective. -/
theorem isEmbedding_pointsMap_fst_fieldFibre {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    Topology.IsEmbedding (pointsMap B S hS (fieldFibre B S hS f p)
      (pullback.fst f (yonedaEquiv.symm p.value))) :=
  isEmbedding_pointsMap_fst_fieldFibre_of_isInducing B S hS f p hmono
    (isInducing_pointsMap_fst_fieldFibre B S hS hX hY f p hmono hqc)

/-- **Stacks 0AC8.** The point space of the field fibre `X_k` is homeomorphic to the
set-theoretic fibre `f^{-1}({y}) ⊂ |X|` with its induced topology, by the comparison map.

This is the tag: the map is an embedding by
`AlgebraicGeometry.Space.isEmbedding_pointsMap_fst_fieldFibre` and its image is the fibre by
`AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`, which is Tag 03H4. -/
@[stacks 0AC8 "homeomorphism onto the set-theoretic fibre"]
noncomputable def homeomorphSetFibre {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    points B S hS (fieldFibre B S hS f p) ≃ₜ setFibre B S hS f p :=
  (isEmbedding_pointsMap_fst_fieldFibre B S hS hX hY f p hmono hqc).toHomeomorph.trans
    (Homeomorph.setCongr (range_pointsMap_fst_fieldFibre B S hS f p))

end AlgebraicGeometry.Space

end
