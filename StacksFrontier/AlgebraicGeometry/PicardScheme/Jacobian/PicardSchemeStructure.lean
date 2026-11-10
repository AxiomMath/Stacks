module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSchemeComponents
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FieldTranslates
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.TranslatedCharts
public import
  StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# Every degree component of the Picard scheme of a curve is `Pic⁰`

For a Picard scheme `P` of a proper smooth curve `X` over a field `k` with a rational point `σ`,
and any group scheme `A` representing `Pic⁰_{X/k,σ}`, every degree component `P^d` is isomorphic
to `A` over `k`: `P⁰` represents `Pic⁰_{X/k,σ}` (`degreeLocusZeroRepresentableBy`), so `P⁰ ≅ A` by
the Yoneda lemma, and translation by a rational point of degree `d` (`d · [σ]`) is an
isomorphism `P⁰ ≅ P^d`.

## Main results

* `Stacks.RigidifiedPicard.exists_point_degree_eq` — a rational point of `P` of any degree.
* `Stacks.RigidifiedPicard.nonempty_degreeLocusOver_iso` — `P^d ≅ A` over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdimX : topologicalKrullDim X ≤ 1)
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
  (e : yonedaGrp.obj P ≅ functor f σ hσ)

/-- The element of `Pic_{X/k,σ}(T)` given by a rigidified class. -/
def mkElt {T : Over (Spec (.of k))} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0) :
    (functor f σ hσ ⋙ forget GrpCat).obj (op T) :=
  Multiplicative.ofAdd (mkGroup f σ hσ c hc)

omit [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The rigidified class underlying `mkElt f σ hσ c hc` is `c`. -/
theorem classOfElt_mkElt {T : Over (Spec (.of k))} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0) :
    classOfElt f σ hσ (mkElt f σ hσ c hc) = c :=
  smallEquiv_mkGroup f σ hσ c hc

include hdimX in
/-- **A rational point of the Picard scheme of any degree.** -/
theorem exists_point_degree_eq (d : ℤ) :
    ∃ r : Over.mk (𝟙 (Spec (.of k))) ⟶ P.X, ∀ s,
      relativeInvertibleDegreeHomAt (bcProj f (Over.mk (𝟙 (Spec (.of k)))))
        (topologicalKrullDim_fiber_bcProj_le f hdim _) s
          (classOfElt f σ hσ (homElt f σ hσ P e r)) = d := by
  obtain ⟨θ, hθ⟩ := exists_degree_eq f hdimX hdim σ hσ 1
  refine ⟨eltHom f σ hσ P e (mkElt f σ hσ (normalize f σ hσ _
      (Stacks.Picard.schemePullbackClass (pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom)
        (d • θ))) (schemePullbackClass_bcSection_normalize f σ hσ _ _)), fun s => ?_⟩
  rw [homElt_eltHom, classOfElt_mkElt, normalize, map_sub,
    relativeInvertibleDegreeHomAt_bcProj f hdim _ s, sub_zero,
    relativeInvertibleDegreeHomAt_fst f hdim (d • θ) _ s, map_zsmul, hθ, Nat.cast_one,
    smul_eq_mul, mul_one]

include hdimX in
/-- **Every degree component is isomorphic to `P⁰`.** -/
theorem nonempty_degreeLocusOver_iso_zero (d : ℤ) :
    Nonempty (degreeLocusOver f hdim σ hσ P e d ≅ degreeLocusOver f hdim σ hσ P e 0) := by
  obtain ⟨r, hr⟩ := exists_point_degree_eq f hdimX hdim σ hσ P e (-d)
  obtain ⟨i⟩ := nonempty_degreeLocus_iso f hdim σ hσ P e r hr d
  rw [add_neg_cancel] at i
  exact ⟨i⟩

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- **`P⁰` is isomorphic over `k` to every group scheme representing `Pic⁰_{X/k,σ}`.** -/
theorem nonempty_degreeLocusOver_zero_iso (A : Grp (Over (Spec (.of k))))
    (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ) :
    Nonempty (degreeLocusOver f hdim σ hσ P e 0 ≅ A.X) :=
  ⟨(degreeLocusZeroRepresentableBy f hdim σ hσ P e).uniqueUpToIso
    (Functor.representableByEquiv.symm (representingIsoOfGrp A eA))⟩

include hdimX in
/-- **Every degree component of the Picard scheme is isomorphic over `k` to every group scheme
representing `Pic⁰_{X/k,σ}`.** -/
theorem nonempty_degreeLocusOver_iso (A : Grp (Over (Spec (.of k))))
    (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ) (d : ℤ) :
    Nonempty (degreeLocusOver f hdim σ hσ P e d ≅ A.X) := by
  obtain ⟨i⟩ := nonempty_degreeLocusOver_iso_zero f hdimX hdim σ hσ P e d
  obtain ⟨j⟩ := nonempty_degreeLocusOver_zero_iso f hdim σ hσ P e A eA
  exact ⟨i ≪≫ j⟩

/-- The underlying morphism of schemes of an isomorphism over `k` is an isomorphism. -/
private theorem isIso_left_hom_of_iso {Y Z : Over (Spec (.of k))} (i : Y ≅ Z) :
    IsIso i.hom.left :=
  inferInstanceAs (IsIso ((Over.forget _).map i.hom))

/-- The base change of `X` along the identity of `Spec k` has an underlying point. -/
private theorem nonempty_left_mk_id : Nonempty (Over.mk (𝟙 (Spec (.of k)))).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum k))

/-- A proper variety structure transfers along an isomorphism over `k`. -/
theorem isProperVariety_of_iso {Y Z : Over (Spec (.of k))} (i : Y ≅ Z)
    [IsProperVariety k Z.hom] : IsProperVariety k Y.hom := by
  have hw : i.hom.left ≫ Z.hom = Y.hom := Over.w i.hom
  have := isIso_left_hom_of_iso i
  have : Nonempty Y.left := by
    have : Nonempty Z.left := IsIntegral.nonempty
    obtain ⟨z⟩ := this
    exact ⟨i.inv.left z⟩
  have : IsIntegral Y.left := isIntegral_of_isOpenImmersion i.hom.left
  rw [← hw]
  exact (isProperVariety_iff k _).2 ⟨⟨⟩, inferInstance⟩

include hdimX in
/-- **[Stacks, Tag 0BA0] (1), for one component**: given a group scheme `A` representing
`Pic⁰_{X/k,σ}` which is an abelian variety, every degree component `P^d` of the Picard scheme is a
proper variety over `k`, and it is isomorphic to `A`. -/
theorem isProperVariety_degreeLocus (A : Grp (Over (Spec (.of k))))
    (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ) [IsAbelianVariety k A.X] (d : ℤ) :
    IsProperVariety k ((degreeLocus f hdim σ hσ P e d).ι ≫ P.X.hom) := by
  obtain ⟨i⟩ := nonempty_degreeLocusOver_iso f hdimX hdim σ hσ P e A eA d
  exact isProperVariety_of_iso i

include hdimX in
/-- Every degree component of the Picard scheme has the dimension of `Pic⁰`. -/
theorem topologicalKrullDim_degreeLocus (A : Grp (Over (Spec (.of k))))
    (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ) (d : ℤ) :
    topologicalKrullDim (degreeLocus f hdim σ hσ P e d) = topologicalKrullDim A.X.left := by
  obtain ⟨i⟩ := nonempty_degreeLocusOver_iso f hdimX hdim σ hσ P e A eA d
  have := isIso_left_hom_of_iso i
  exact IsHomeomorph.topologicalKrullDim_eq _ (i.hom.left.homeomorph).isHomeomorph

include hdimX in
/-- Every degree component of the Picard scheme is nonempty. -/
theorem nonempty_degreeLocus (d : ℤ) : Nonempty (degreeLocus f hdim σ hσ P e d) := by
  obtain ⟨r, hr⟩ := exists_point_degree_eq f hdimX hdim σ hσ P e d
  obtain ⟨s⟩ := nonempty_left_mk_id (k := k)
  exact ⟨⟨r.left s, (range_subset_degreeLocus_iff f hdim σ hσ P e r d).2 hr ⟨s, rfl⟩⟩⟩

include hdimX in
/-- **Every degree component of a Picard scheme smooth of relative dimension `g` has dimension
`g`.** -/
theorem topologicalKrullDim_degreeLocus_eq {g : ℕ} [SmoothOfRelativeDimension g P.X.hom] (d : ℤ) :
    topologicalKrullDim (degreeLocus f hdim σ hσ P e d) = (g : WithBot ℕ∞) := by
  have := nonempty_degreeLocus f hdimX hdim σ hσ P e d
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : SmoothOfRelativeDimension g ((degreeLocus f hdim σ hσ P e d).ι ≫ P.X.hom) :=
    IsZariskiLocalAtSource.comp ‹_› _
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field g
    ((degreeLocus f hdim σ hσ P e d).ι ≫ P.X.hom)

/-! ### Rational points of `P^d` (Stacks 0BA0 (2)) -/

/-- The identification of `X` with its base change along the identity of `Spec k`. -/
abbrev toBcId : X ⟶ bc f (Over.mk (𝟙 (Spec (.of k)))) :=
  pullback.lift (𝟙 X) f (by simp)

omit [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- `toBcId f` is a section of the first projection of the base change onto `X`. -/
theorem toBcId_fst : toBcId f ≫ pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom = 𝟙 X :=
  pullback.lift_fst _ _ _

omit [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The identification `toBcId f` of `X` with its base change along the identity is an
isomorphism. -/
theorem isIso_toBcId : IsIso (toBcId f) := by
  refine ⟨⟨pullback.fst _ _, toBcId_fst f, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, toBcId_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
    have := pullback.condition (f := f) (g := (Over.mk (𝟙 (Spec (.of k)))).hom)
    simpa using this

/-- The class on `X` of a rational point of `P`. -/
def pointClassOf (r : Over.mk (𝟙 (Spec (.of k))) ⟶ P.X) : Stacks.Picard.ofScheme X :=
  Stacks.Picard.schemePullbackClass (toBcId f) (classOfElt f σ hσ (homElt f σ hσ P e r))

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The fibrewise degree of the class of a rational point `r` of `P` equals the degree on `X` of
`pointClassOf f σ hσ P e r`. -/
theorem degree_pointClassOf (r : Over.mk (𝟙 (Spec (.of k))) ⟶ P.X)
    (s : (Over.mk (𝟙 (Spec (.of k)))).left) :
    relativeInvertibleDegreeHomAt (bcProj f (Over.mk (𝟙 (Spec (.of k)))))
        (topologicalKrullDim_fiber_bcProj_le f hdim _) s
        (classOfElt f σ hσ (homElt f σ hσ P e r)) =
      invertibleCurveDegreeHom k f hdimX (pointClassOf f σ hσ P e r) := by
  have hiso := isIso_toBcId f
  have hc : classOfElt f σ hσ (homElt f σ hσ P e r) = Stacks.Picard.schemePullbackClass
      (pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom) (pointClassOf f σ hσ P e r) := by
    rw [pointClassOf, Stacks.Picard.schemePullbackClass_comp]
    have : pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom ≫ toBcId f = 𝟙 _ := by
      rw [← cancel_epi (toBcId f), ← Category.assoc, toBcId_fst, Category.id_comp,
        Category.comp_id]
    rw [this, Stacks.Picard.schemePullbackClass_id]
  rw [hc, relativeInvertibleDegreeHomAt_fst f hdim _ _ s, relativeInvertibleDegreeHomAt_spec f
    hdimX hdim]

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- **[Stacks, Tag 0BA0] (2): the `k`-rational points of `P^d` are the invertible modules of
degree `d` on `X`**: `r ↦ [r^*𝒫_univ]` is a bijection from the rational points of `P` landing in
`P^d` onto the Picard classes of `X` of degree `d`. -/
theorem bijOn_pointClassOf (d : ℤ) :
    Set.BijOn (pointClassOf f σ hσ P e)
      {r | Set.range r.left ⊆ (degreeLocus f hdim σ hσ P e d : Set P.X.left)}
      {c | invertibleCurveDegreeHom k f hdimX c = d} := by
  have hiso := isIso_toBcId f
  obtain ⟨s₀⟩ := nonempty_left_mk_id (k := k)
  refine ⟨fun r hr => ?_, fun r _ r' _ h => ?_, fun c hc => ?_⟩
  · rw [Set.mem_ofPred_eq, ← degree_pointClassOf f hdimX hdim σ hσ P e r s₀]
    exact (range_subset_degreeLocus_iff f hdim σ hσ P e r d).1 hr s₀
  · apply homElt_injective f σ hσ P e
    refine ext_functor f σ hσ ?_
    have h' := congrArg (Stacks.Picard.schemePullbackClass (inv (toBcId f))) h
    simp only [pointClassOf, Stacks.Picard.schemePullbackClass_comp, IsIso.inv_hom_id,
      Stacks.Picard.schemePullbackClass_id] at h'
    exact h'
  · have hT0 : ∀ n : Stacks.Picard.ofScheme (Over.mk (𝟙 (Spec (.of k)))).left, n = 0 :=
      Stacks.Picard.eq_zero_of_isField k
    set c' := Stacks.Picard.schemePullbackClass (pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom) c
    have hc' : Stacks.Picard.schemePullbackClass (bcSection f σ hσ _) c' = 0 := hT0 _
    have hpc : pointClassOf f σ hσ P e (eltHom f σ hσ P e (mkElt f σ hσ c' hc')) = c := by
      rw [pointClassOf, homElt_eltHom, classOfElt_mkElt, Stacks.Picard.schemePullbackClass_comp,
        toBcId_fst, Stacks.Picard.schemePullbackClass_id]
    refine ⟨eltHom f σ hσ P e (mkElt f σ hσ c' hc'), ?_, hpc⟩
    refine (range_subset_degreeLocus_iff f hdim σ hσ P e _ d).2 fun s => ?_
    change relativeInvertibleDegreeHomAt _ _ s (classOfElt f σ hσ (homElt f σ hσ P e
      (eltHom f σ hσ P e (mkElt f σ hσ c' hc')))) = d
    rw [degree_pointClassOf f hdimX hdim σ hσ P e _ s, hpc]
    exact hc

end Stacks.RigidifiedPicard

end
