module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FibreThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# Rigidity of closed subspaces containing every infinitesimal fibre

Let `V` be an affine object of the big fppf site of `S` with Noetherian ring of global sections
`A`, complete with respect to an ideal `I`, and let `X` be an algebraic space proper over `V`.
A closed subspace `Z ⊆ X` which contains every infinitesimal fibre `X ×_V Spec (A / Iⁿ)` is all
of `X`. This is the rigidity input of Grothendieck's algebraization of morphisms (Stacks 0A4Z):
it identifies the algebraization of the graphs with the source, and it gives the uniqueness of
the algebraized morphism.

## Main results

* `Ideal.exists_mem_forall_mul_eq_self_of_mem_iInf_pow`: Krull's intersection theorem with one
  element `r ∈ K` serving all of `⋂ₙ Kⁿ`.
* `AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_mul_eq_zero`: a closed immersion into an affine
  scheme whose ideal is killed by a function `s` is flat at the points over `D(s)`.
* `AlgebraicGeometry.Scheme.eq_empty_of_isClosed_of_disjoint_zeroLocus`: on an affine scheme a
  closed set missing the zero locus of an ideal in the Jacobson radical is empty.
* `AlgebraicGeometry.Space.isFlatAt_ι_of_forall_le_fibreThickening`: the inclusion of such a
  `Z` is flat at the points over `V(I)`.
* `AlgebraicGeometry.Space.eq_top_of_forall_fibreThickening_le`: rigidity.

## Implementation notes

The proof goes through flatness rather than through the support of the ideal sheaf: the flat
locus of a morphism locally of finite presentation is open (Stacks 05X3), its closed complement
has closed image in `|V|` (properness) which misses `V(I)`, and a nonempty closed subset of
`Spec A` meets `V(I)` because `I` lies in the Jacobson radical. A flat closed immersion is open
on points (Stacks 042S), so the same argument makes it surjective, and a surjective flat closed
immersion is an isomorphism.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

/-- **Krull's intersection theorem, uniformly.** In a Noetherian ring there is a single
`r ∈ K` with `r * a = a` for every `a` in `⋂ₙ Kⁿ`. -/
theorem Ideal.exists_mem_forall_mul_eq_self_of_mem_iInf_pow {R : Type*} [CommRing R]
    [IsNoetherianRing R] (K : Ideal R) :
    ∃ r ∈ K, ∀ a ∈ (⨅ n : ℕ, K ^ n : Ideal R), r * a = a := by
  let N : Submodule R R := ⨅ i : ℕ, K ^ i • ⊤
  have hN : ∀ k, (K.stableFiltration ⊤ ⊓ K.trivialFiltration N).N k = N :=
    fun k => inf_eq_right.mpr ((iInf_le _ k).trans <| le_of_eq <| by simp)
  obtain ⟨r, hr₁, hr₂⟩ :=
    Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul K N (IsNoetherian.noetherian N) (by
      obtain ⟨k, hk⟩ := (K.stableFiltration_stable ⊤).inter_right (K.trivialFiltration N)
      have := hk k le_rfl
      rw [hN, hN] at this
      exact this.ge)
  refine ⟨r, hr₁, fun a ha => hr₂ a ?_⟩
  rwa [show N = ⨅ n : ℕ, K ^ n by simp only [N, Ideal.smul_eq_mul, Ideal.mul_top]]

namespace AlgebraicGeometry

/-- **A closed immersion into an affine scheme is flat at the points over which its ideal is
killed by a function invertible there.** -/
theorem Scheme.Hom.flat_stalkMap_of_mul_eq_zero {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] [IsAffine X] (s : Γ(X, ⊤))
    (hs : ∀ a, f.appTop a = 0 → s * a = 0) (y : Y) (hy : f y ∈ X.basicOpen s) :
    (f.stalkMap y).hom.Flat := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  refine RingHom.Flat.of_bijective ⟨?_, f.stalkMap_surjective y⟩
  refine stalkMap_injective_of_isAffine f y fun g hg => ?_
  have key : f.stalkMap y (X.presheaf.germ ⊤ (f y) trivial g) =
      Y.presheaf.germ ⊤ y trivial (f.appTop g) := f.germ_stalkMap_apply ⊤ y trivial g
  rw [TopCat.Presheaf.Γgerm, key] at hg
  obtain ⟨W, w, hyW, hW⟩ :=
    Y.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero ⊤ (f.appTop g) ⟨y, trivial⟩ hg
  obtain ⟨_, ⟨t, rfl⟩, hyt, htW⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y) hyW
  have hsurj : Function.Surjective f.appTop := f.app_surjective ⊤ (isAffineOpen_top X)
  obtain ⟨t', rfl⟩ := hsurj t
  obtain ⟨n, hn⟩ := exists_of_res_zero_of_qcqs_of_top (X := Y) (s := f.appTop t')
    (f := f.appTop g) (by
      have hW' : Y.presheaf.map w.op (f.appTop g) = 0 := hW
      have e : (f.appTop g |_ Y.basicOpen (f.appTop t')) =
          Y.presheaf.map (homOfLE htW).op (Y.presheaf.map w.op (f.appTop g)) := by
        rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
        rfl
      rw [e, hW', map_zero])
  have hzero : s * (t' ^ n * g) = 0 := hs _ (by rwa [map_mul, map_pow])
  have hy' : f y ∈ X.basicOpen (s * t') := by
    rw [Scheme.basicOpen_mul]
    refine ⟨hy, ?_⟩
    change y ∈ f ⁻¹ᵁ X.basicOpen t'
    rwa [Scheme.preimage_basicOpen_top]
  rw [TopCat.Presheaf.Γgerm]
  refine germ_eq_zero_of_pow_mul_eq_zero (U := ⊤) ⟨f y, trivial⟩ hy' (n := n + 1) ?_
  calc (s * t') ^ (n + 1) * g = s ^ n * t' * (s * (t' ^ n * g)) := by ring
    _ = 0 := by rw [hzero, mul_zero]

/-- **A closed subset of an affine scheme missing the zero locus of an ideal inside the
Jacobson radical is empty.** On `Spec R` a closed set is `V(K)`; if `V(K) ∩ V(J) = ∅` then
`K + J = R`, so some `k ∈ K` is `1 - j` with `j ∈ J ⊆ rad(R)`, hence a unit. -/
theorem Scheme.eq_empty_of_isClosed_of_disjoint_zeroLocus {X : Scheme.{u}} [IsAffine X]
    {J : Ideal Γ(X, ⊤)} (hJ : J ≤ Ideal.jacobson ⊥) {C : Set X} (hC : IsClosed C)
    (hdisj : Disjoint C (X.zeroLocus (U := ⊤) (J : Set Γ(X, ⊤)))) : C = ∅ := by
  set C' : Set (PrimeSpectrum Γ(X, ⊤)) := X.isoSpec.hom '' C
  obtain ⟨K, hK⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal C').1 ((X.isoSpec.hom.homeomorph).isClosedMap C hC)
  have hdisj' : Disjoint C' (PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤))) := by
    rw [← X.isoSpec_image_zeroLocus]
    exact (Set.disjoint_image_iff (X.isoSpec.hom.homeomorph).injective).2 hdisj
  have hKJ : K ⊔ J = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_sup, ← hK]
    exact Set.disjoint_iff_inter_eq_empty.1 hdisj'
  obtain ⟨k, hk, j, hj, hkj⟩ :=
    Submodule.mem_sup.1 (hKJ ▸ Submodule.mem_top : (1 : Γ(X, ⊤)) ∈ K ⊔ J)
  have hunit : IsUnit k := by
    rw [show k = j * -1 + 1 by linear_combination hkj]
    exact Ideal.mem_jacobson_bot.1 (hJ hj) (-1)
  have hC'empty : C' = ∅ := by
    rw [hK, Ideal.eq_top_of_isUnit_mem K hk hunit, Submodule.top_coe,
      PrimeSpectrum.zeroLocus_univ]
  exact Set.image_eq_empty.1 hC'empty

/-- **A point mapping into the image of `j` lies in the zero locus of the pulled-back kernel.**
If `j : T ⟶ V` has `ker j^♯ = I` on global sections and `h u` lies in the image of `j`, then `u`
lies in the zero locus of the ideal generated by `h^♯ I`. -/
theorem Scheme.mem_zeroLocus_map_of_mem_range {T V W : Scheme.{u}} (j : T ⟶ V)
    {I : Ideal Γ(V, ⊤)} (hj : RingHom.ker j.appTop.hom = I) (h : W ⟶ V) {u : W}
    (hu : h u ∈ Set.range j) :
    u ∈ W.zeroLocus (U := ⊤) (Ideal.map h.appTop.hom I : Set Γ(W, ⊤)) := by
  obtain ⟨v, hv⟩ := hu
  rw [Ideal.map, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  rintro _ ⟨a, haI, rfl⟩ hmem
  have h₁ : u ∈ h ⁻¹ᵁ V.basicOpen a := by rwa [Scheme.preimage_basicOpen_top]
  have h₂ : v ∈ j ⁻¹ᵁ V.basicOpen a := by
    change j v ∈ V.basicOpen a
    rwa [hv]
  have ha : j.appTop a = 0 := (show a ∈ RingHom.ker j.appTop.hom from hj ▸ haI)
  rwa [Scheme.preimage_basicOpen_top, ha, Scheme.basicOpen_zero] at h₂

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

section Rigidity

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  {X : AlgebraicSpaces B S hS} (fX : X ⟶ schemeSpace V)

/-- **A closed subspace containing every infinitesimal fibre is flat over `X` at the points of
the closed fibre.** Let `Z ⊆ X` be a closed subspace containing `X ×_V Spec (A / Iⁿ)` for every
`n`. On an affine étale chart `Spec B` of `X` with `B` Noetherian the ideal of `Z` lies in
`⋂ₙ (I B)ⁿ`, so by Krull's intersection theorem it is killed by `1 - r` for some `r ∈ I B`; at a
point over `V(I)` the function `1 - r` is invertible, so the chart of `Z ⟶ X` is flat there. -/
theorem isFlatAt_ι_of_forall_le_fibreThickening (Z : ClosedSubspaces B S hS X.1)
    (hZ : ∀ n, (fibreThickening V I fX n).1 ≤ Z.1)
    (hN : ∀ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      IsEtaleChart B S hS X.1 (CostructuredArrow.mk b) →
      IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (z : points B S hS Z.1.toFunctor)
    (hz : pointsMap B S hS _ (Z.1.ι ≫ fX.hom) z ∈ Set.range (pointsMap B S hS _
      (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1)))) :
    IsFlatAt B S hS Z.1.ι z := by
  classical
  obtain ⟨W, b, hWaff, hb, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS X.1 X.2 (pointsMap B S hS _ Z.1.ι z)
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hb⟩
  have := hN W b hWaff hb
  have hsq := Z.2.2.rep.isPullback b
  obtain ⟨q, hqz, hqw⟩ := exists_point_of_isPullback_presheaf B S hS hsq z w hw.symm
  obtain ⟨p, rfl⟩ := Quot.exists_rep q
  have ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (Z.2.2.rep.fst b) :=
    (MorphismProperty.relative_isStableUnderBaseChange (MorphismProperty.inverseImage
      (@Etale.{u}) (BigFppfOver.toScheme B S hS))).of_isPullback hsq.flip hb
  have hiff := isFlatAt_chart_iff B S hS Z.1.ι _ W (Z.2.2.rep.fst b) b (Z.2.2.rep.snd b) ha hb
    hsq.w p (IsLocalRing.closedPoint p.carrier)
  rw [← hqz]
  refine hiff.1 ?_
  rw [isFlatAt_yoneda_iff]
  set g := (BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd b)
  have : _root_.AlgebraicGeometry.IsClosedImmersion g := Z.2.2.property_snd b
  set h := yoneda.preimage (b ≫ fX.hom)
  let φ := ((BigFppfOver.toScheme B S hS).map h).appTop.hom
  obtain ⟨r, hrK, hr⟩ := Ideal.exists_mem_forall_mul_eq_self_of_mem_iInf_pow (Ideal.map φ I)
  refine Scheme.Hom.flat_stalkMap_of_mul_eq_zero g (1 - r) (fun a ha0 => ?_) _ ?_
  · have hmem : a ∈ (⨅ n : ℕ, Ideal.map φ I ^ n) := Ideal.mem_iInf.2 fun n => by
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hWaff
      have hle := definingIdealAt_antitone B S hS X (fibreThickening V I fX n) Z (hZ n) U
        (by rwa [definingIdealAt_eq_ker])
      rwa [definingIdealAt_fibreThickening, Ideal.map_pow] at hle
    rw [sub_mul, one_mul, hr a hmem, sub_self]
  · set u := g (schemePoint B S hS _ p)
    have hu : pointsToScheme B S hS W w = u := by
      rw [← hqw, pointsToScheme_pointsMap_yoneda]
      rfl
    have hbf : b ≫ fX.hom = yoneda.map h := (Functor.map_preimage yoneda _).symm
    have hzw : pointsMap B S hS _ (Z.1.ι ≫ fX.hom) z =
        pointsMap B S hS _ (yoneda.map h) w := by
      rw [pointsMap_comp_apply, ← hw, ← pointsMap_comp_apply, hbf]
      rfl
    rw [hzw] at hz
    have hv : (BigFppfOver.toScheme B S hS).map h u ∈ Set.range
        ((BigFppfOver.toScheme B S hS).map (adicCompletionQuotientObjHom B S hS V I 1)) := by
      have hmem := (range_pointsMap_yoneda_eq_preimage B S hS
        (adicCompletionQuotientObjHom B S hS V I 1)).le hz
      rwa [Set.mem_preimage, pointsToScheme_pointsMap_yoneda, hu] at hmem
    have hzl := Scheme.mem_zeroLocus_map_of_mem_range _ (I := I)
      (by rw [ker_appTop_adicCompletionQuotientObjHom, pow_one]) _ hv
    rw [Scheme.mem_basicOpen_top, map_sub, map_one]
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun hunit => ?_
    exact (Scheme.mem_zeroLocus_iff _ _ _).1 hzl r hrK ((Scheme.mem_basicOpen_top _ _ _).2 hunit)

/-- The points of `V` lying over `Spec (A / I)`: a closed subset of `|V|` meets them as soon as
it is nonempty, when `A` is `I`-adically complete. -/
theorem eq_empty_of_isClosed_of_disjoint_range_adicCompletionQuotientObjHom
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {D : Set (points B S hS (yoneda.obj V))} (hD : IsClosed D)
    (hdisj : Disjoint D (Set.range (pointsMap B S hS _
      (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1))))) : D = ∅ := by
  have hempty := Scheme.eq_empty_of_isClosed_of_disjoint_zeroLocus
    (IsAdicComplete.le_jacobson_bot I) ((schemePointsHomeomorph B S hS V).isClosedMap D hD)
    (Set.disjoint_left.2 ?_)
  · exact Set.image_eq_empty.1 hempty
  · rintro _ ⟨d, hd, rfl⟩ hzl
    refine Set.disjoint_left.1 hdisj hd ?_
    rwa [range_pointsMap_yoneda_eq_preimage, Set.mem_preimage,
      range_eq_zeroLocus_ker_appTop _ (isAffineOpen_top _),
      ker_appTop_adicCompletionQuotientObjHom, pow_one]

/-- **A closed subspace containing every infinitesimal fibre is flat over `X`.** Its inclusion
is flat at the points over `V(I)`, and the image in `|V|` of the closed non-flat locus misses
`V(I)`, hence is empty. -/
theorem isFlat_ι_of_forall_le_fibreThickening
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hX : IsProper B S hS fX.hom) (Z : ClosedSubspaces B S hS X.1)
    (hZ : ∀ n, (fibreThickening V I fX n).1 ≤ Z.1)
    (hN : ∀ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      IsEtaleChart B S hS X.1 (CostructuredArrow.mk b) →
      IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hιlfp : IsLocallyOfFinitePresentation B S hS Z.1.ι) : IsFlat B S hS Z.1.ι := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  rw [isFlat_iff_forall_isFlatAt]
  by_contra hne
  push Not at hne
  obtain ⟨z0, hz0⟩ := hne
  have hC : IsClosed {z | ¬ IsFlatAt B S hS Z.1.ι z} :=
    (isOpen_setOf_isFlatAt B S hS Z.2.1 X.2 Z.1.ι hιlfp).isClosed_compl
  have hp : IsClosedMap (pointsMap B S hS _ (Z.1.ι ≫ fX.hom)) :=
    isClosed_of_universallyClosed B S hS hV _ (universallyClosed_comp B S hS X.2 hV _ _
      (universallyClosed_of_isClosedImmersion B S hS Z.2.1 X.2 _ Z.2.2) hX.2.2)
  have hempty := eq_empty_of_isClosed_of_disjoint_range_adicCompletionQuotientObjHom V I
    (hp _ hC) (Set.disjoint_left.2 ?_)
  · exact (Set.image_eq_empty.1 hempty).subset hz0
  · rintro _ ⟨z, hz, rfl⟩ hmem
    exact hz (isFlatAt_ι_of_forall_le_fibreThickening V I fX Z hZ hN z hmem)

/-- **A closed subspace containing every infinitesimal fibre and with open image is all of
`|X|`.** The image in `|V|` of the closed complement of its image misses `V(I)`, hence is
empty. -/
theorem isSurjective_ι_of_forall_le_fibreThickening
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hX : IsProper B S hS fX.hom) (Z : ClosedSubspaces B S hS X.1)
    (hZ : ∀ n, (fibreThickening V I fX n).1 ≤ Z.1)
    (hopen : IsOpen (Set.range (pointsMap B S hS _ Z.1.ι))) : IsSurjective B S hS Z.1.ι := by
  have hempty := eq_empty_of_isClosed_of_disjoint_range_adicCompletionQuotientObjHom V I
    ((isClosed_of_universallyClosed B S hS (isAlgebraicSpace_yoneda B S hS V) fX.hom hX.2.2) _
      hopen.isClosed_compl) (Set.disjoint_left.2 ?_)
  · rw [Set.image_eq_empty, Set.compl_empty_iff] at hempty
    exact Set.range_eq_univ.1 hempty
  · rintro _ ⟨x, hx, rfl⟩ hmem
    apply hx
    have : Mono (adicCompletionQuotientObjHom B S hS V I 1) :=
      (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
    have hx1 : x ∈ Set.range (pointsMap B S hS _ (fibreThickening V I fX 1).1.ι) := by
      rw [range_pointsMap_preimage_ι, Set.mem_preimage]
      change pointsMap B S hS X.1 fX.hom x ∈ Set.range (pointsMap B S hS
        (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1))).toFunctor
        (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1))).ι)
      rwa [range_pointsMap_ι_range]
    obtain ⟨y, rfl⟩ := hx1
    exact ⟨pointsMap B S hS _ (Subfunctor.homOfLe (hZ 1)) y, by
      rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩

/-- **Rigidity of closed subspaces.** Let `A = Γ(V, 𝒪_V)` be Noetherian and complete with
respect to an ideal `I`, and let `X` be proper over `V`. A closed subspace of `X` containing
every infinitesimal fibre `X ×_V Spec (A / Iⁿ)` is all of `X`.

Its inclusion is flat at every point over `V(I)`
(`AlgebraicGeometry.Space.isFlatAt_ι_of_forall_le_fibreThickening`); the flat locus is open
(Stacks 05X3), and the image in `|V|` of its closed complement is closed and misses `V(I)`, hence
is empty because `I` lies in the Jacobson radical of `A`. So the inclusion is flat, hence open on
points (Stacks 042S), and the same argument shows that the complement of its image is empty. A
surjective flat closed immersion is an isomorphism. -/
theorem eq_top_of_forall_fibreThickening_le
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hX : IsProper B S hS fX.hom) (Z : ClosedSubspaces B S hS X.1)
    (hZ : ∀ n, (fibreThickening V I fX n).1 ≤ Z.1) : Z.1 = ⊤ := by
  classical
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hVnoeth : HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ V (Iso.refl _) inferInstance
  have hXnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 hV fX.hom
    hX.2.1.1 hVnoeth
  have hN : ∀ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      IsEtaleChart B S hS X.1 (CostructuredArrow.mk b) →
      IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := by
    intro W b hW hb
    have := (exists_atlas_iff_forall_etale B S hS X.1 _ X.2).1 hXnoeth W b hb
    exact _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hιlfp : IsLocallyOfFinitePresentation B S hS Z.1.ι :=
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS Z.2.1 X.2 Z.1.ι hXnoeth
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS Z.1.ι Z.2.2)
  have hflat := isFlat_ι_of_forall_le_fibreThickening V I fX hX Z hZ hN hιlfp
  have hopen : IsOpen (Set.range (pointsMap B S hS _ Z.1.ι)) := by
    rw [← Set.image_univ]
    exact isOpen_of_universallyOpen B S hS X.2 Z.1.ι
      (universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS Z.2.1 X.2 Z.1.ι
        hflat hιlfp) _ isOpen_univ
  have hiso : IsIso Z.1.ι :=
    isIso_of_isClosedImmersion_of_isFlat_of_isSurjective B S hS Z.2.1 X.2 Z.1.ι Z.2.2 hflat
      (isSurjective_ι_of_forall_le_fibreThickening V I fX hX Z hZ hopen)
  refine le_antisymm le_top fun T x _ => ?_
  have hx : Z.1.ι.app T ((inv Z.1.ι).app T x) = x := by
    rw [← NatTrans.comp_app_apply, IsIso.inv_hom_id, NatTrans.id_app, types_id_apply]
  rw [← hx]
  exact ((inv Z.1.ι).app T x).2

end Rigidity

end AlgebraicGeometry.Space
