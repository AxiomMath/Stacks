module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv.IdealDescent

/-!
# The chart conditions of Stacks 083C

For a closed subspace `D` of an algebraic space `X`, the chart lemmas behind the equivalence of
conditions (2), (3) and (4) of Stacks 083C, the points of the small étale site they use, and the
bridge `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_definingIdealSheaf` from
condition (1).  The implications themselves are in
`StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart condition read on the canonical base change -/

/-- **Any closed-subscheme presentation of the inverse image computes the same kernel.** If a
morphism `j : R ⟶ U` of the site is a closed immersion of schemes whose range is the inverse
image `D ×_X U`, then its kernel is the kernel of the canonical base change.

This is `AlgebraicGeometry.Space.ker_eq_iff_exists_closedSubschemePresentation`,
applied to the ideal sheaf `j.ker` itself. -/
theorem ker_rep_snd_eq_ker_of_range_eq (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (U R : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X.1)
    (j : R ⟶ U)
    [_root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j)]
    (hj : D.1.preimage g = Subfunctor.range (yoneda.map j)) :
    ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd g)).ker =
      ((BigFppfOver.toScheme B S hS).map j).ker :=
  (ker_eq_iff_exists_closedSubschemePresentation B S hS X D U g _).2
    ⟨R, j, Stacks.Divisors.closedImmersionKerIso _,
      Stacks.Divisors.closedImmersion_eq_kerIso_comp _, hj⟩

/-- The range of the canonical base change of a closed subspace on a chart is the inverse image
of the subspace, in the orientation in which the chart conditions state it. -/
theorem preimage_eq_range_rep_snd (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X.1) :
    D.1.preimage g = Subfunctor.range (yoneda.map (D.2.2.rep.snd g)) :=
  (range_yoneda_snd_eq_preimage B S hS g D.2.2.rep).symm

/-- **The chart condition, for a presentation of the inverse image by an arbitrary closed
immersion of the site.** -/
theorem isSchemeEffectiveCartierPullback_iff_ker (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (U R : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X.1)
    (j : R ⟶ U)
    [_root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j)]
    (hj : D.1.preimage g = Subfunctor.range (yoneda.map j)) :
    IsSchemeEffectiveCartierPullback B S hS X D U g ↔
      Stacks.Divisors.IsEffectiveCartierDivisor
        ((BigFppfOver.toScheme B S hS).map j).ker := by
  rw [isSchemeEffectiveCartierPullback_iff, ker_rep_snd_eq_ker_of_range_eq B S hS X D U R g j hj]

/-- **The chart condition passes to a flat morphism of charts.** If the inverse image of `D` on
a chart `U` is an effective Cartier divisor, then so is its inverse image on any chart lying
flatly over `U`; this is Stacks 02OO applied to the base change of the ideal sheaf. -/
theorem isSchemeEffectiveCartierPullback_comp_of_flat (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) {U V : BigFppfOver B S hS} (g : yoneda.obj U ⟶ X.1)
    (k : V ⟶ U) [Flat ((BigFppfOver.toScheme B S hS).map k)]
    (h : IsSchemeEffectiveCartierPullback B S hS X D U g) :
    IsSchemeEffectiveCartierPullback B S hS X D V (yoneda.map k ≫ g) := by
  rw [isSchemeEffectiveCartierPullback_iff, schemeKer_snd_comp B S hS D g k]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    ((isSchemeEffectiveCartierPullback_iff B S hS X D U g).1 h)

/-! ### Étale charts -/

/-- A chart lying étale over an étale chart is itself an étale chart. -/
theorem isEtale_yoneda_map_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS} (g : yoneda.obj U ⟶ X) (k : V ⟶ U)
    (hk : Etale ((BigFppfOver.toScheme B S hS).map k)) (hg : IsEtale B S hS g) :
    IsEtale B S hS (yoneda.map k ≫ g) :=
  isEtale_of_presheaf_etale B S hS
    (etale_comp_of_scheme B S hS k g hk (presheaf_etale_of_isEtale B S hS hg))

/-- **Two étale charts of an algebraic space have a common refinement.** The fibre product of
two étale charts is representable, and its two projections are étale morphisms of schemes. -/
theorem exists_common_etale_chart (X : AlgebraicSpaces B S hS)
    (U V : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X.1) (h : yoneda.obj V ⟶ X.1)
    (hg : IsEtale B S hS g) (hh : IsEtale B S hS h) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U) (q : W ⟶ V),
      IsPullback (yoneda.map p) (yoneda.map q) g h ∧
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) := by
  have hg' := presheaf_etale_of_isEtale B S hS hg
  have hh' := presheaf_etale_of_isEtale B S hS hh
  have hpb : IsPullback (yoneda.map (yoneda.preimage (hg'.1.fst h)))
      (yoneda.map (hg'.1.snd h)) g h := by
    simpa only [yoneda.map_preimage] using hg'.1.isPullback h
  exact ⟨hg'.1.pullback h, yoneda.preimage (hg'.1.fst h), hg'.1.snd h, hpb,
    hh'.2 g (yoneda.map (hg'.1.snd h)) (yoneda.preimage (hg'.1.fst h)) hpb.flip,
    hg'.2 h (yoneda.map (yoneda.preimage (hg'.1.fst h))) (hg'.1.snd h) hpb⟩

/-! ### Points -/

/-- A section of a represented presheaf, restricted along `c`, maps to the restriction of its
image. -/
private theorem app_comp_eq_of_map_app_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U R R' : BigFppfOver B S hS} (g : yoneda.obj U ⟶ F) (c : R ⟶ R') (v : R' ⟶ U)
    {w : F.obj (op R)} (h : F.map c.op (g.app (op R') v) = w) : g.app (op R) (c ≫ v) = w := by
  rw [← h]
  exact congrArg (fun t => t v) (g.naturality c.op)

/-- **A matching pair of points of two charts comes from a point of their fibre product.**
Given field-valued points of `h_U` and `h_V` with the same image in `F`, and a cartesian square
exhibiting `h_W` as `h_U ×_F h_V`, there is a field-valued point of `h_W` restricting to the
classes of both.

The two representatives acquire a common extension `r` over `F`; its field spectrum maps to
both `U` and `V` compatibly, so the universal property of the fibre product, applied to the
sections over that one object, produces the required section of `h_W`. -/
theorem exists_fieldValuedPoint_of_isPullback {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V W : BigFppfOver B S hS} (a : W ⟶ U) (b : W ⟶ V)
    (g : yoneda.obj U ⟶ F) (h : yoneda.obj V ⟶ F)
    (hpb : IsPullback (yoneda.map a) (yoneda.map b) g h)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (q : FieldValuedPoint B S hS (yoneda.obj V))
    (hpq : pointsMap B S hS _ g (p.class B S hS _) =
      pointsMap B S hS _ h (q.class B S hS _)) :
    ∃ r : FieldValuedPoint B S hS (yoneda.obj W),
      pointsMap B S hS _ (yoneda.map a) (r.class B S hS _) = p.class B S hS _ ∧
      pointsMap B S hS _ (yoneda.map b) (r.class B S hS _) = q.class B S hS _ := by
  obtain ⟨r, ⟨c, hc⟩, ⟨d, hd⟩⟩ := (FieldValuedPoint.class_eq_class_iff B S hS F _ _).1 hpq
  have heq : g.app _ (c ≫ p.value) = h.app _ (d ≫ q.value) :=
    (app_comp_eq_of_map_app_eq B S hS g c _ hc).trans
      (app_comp_eq_of_map_app_eq B S hS h d _ hd).symm
  have hs := ((evaluation _ (Type u)).obj (Opposite.op r.siteObject)).map_isPullback hpb
  obtain ⟨v, hv, hv'⟩ := Types.exists_of_isPullback hs (c ≫ p.value) (d ≫ q.value) heq
  refine ⟨{ carrier := r.carrier, contained := r.contained, toBase := r.toBase, value := v },
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _ ?_,
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _ ?_⟩
  · exact ⟨_, FieldValuedPoint.dominates_refl B S hS _ _, ⟨c, hv.symm⟩⟩
  · exact ⟨_, FieldValuedPoint.dominates_refl B S hS _ _, ⟨d, hv'.symm⟩⟩

/-- **A point of a closed subspace lifts to a point of its inverse image on a surjective
chart.** For a surjective chart `g : h_U ⟶ X` and a point `x` of `D`, there is a field-valued
point of the canonical base change `D ×_X U` whose image in `X` is the image of `x`.

Surjectivity gives a representative of the image of `x` over `U` and a common extension of the
two, over which the section of `h_U` lands in the inverse image of `D`; its factorization
through `D ×_X U` is the required representative. -/
theorem exists_fieldValuedPoint_rep_pullback_of_isSurjective (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X.1)
    (hg : IsSurjective B S hS g) (x : points B S hS D.1.toFunctor) :
    ∃ p : FieldValuedPoint B S hS (yoneda.obj (D.2.2.rep.pullback g)),
      pointsMap B S hS _ (yoneda.map (D.2.2.rep.snd g) ≫ g) (p.class B S hS _) =
        pointsMap B S hS D.1.toFunctor D.1.ι x := by
  have hj : D.1.preimage g = Subfunctor.range (yoneda.map (D.2.2.rep.snd g)) :=
    preimage_eq_range_rep_snd B S hS X D U g
  obtain ⟨x, rfl⟩ := Quot.exists_rep x
  obtain ⟨v, hv⟩ := hg (pointsMap B S hS D.1.toFunctor D.1.ι (x.class B S hS _))
  obtain ⟨v, rfl⟩ := Quot.exists_rep v
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS X.1 _ _).1 hv
  change X.1.map a.op (g.app _ v.value) = r.value at ha
  change X.1.map b.op x.value.val = r.value at hb
  have hmem : r.value ∈ D.1.obj (Opposite.op r.siteObject) := by
    rw [← hb]
    exact D.1.map b.op x.value.property
  have hag : g.app (Opposite.op r.siteObject) (a ≫ v.value) = r.value :=
    app_comp_eq_of_map_app_eq B S hS g a _ ha
  have hmem' : a ≫ v.value ∈
      (Subfunctor.range (yoneda.map (D.2.2.rep.snd g))).obj (Opposite.op r.siteObject) := by
    rw [← hj]
    simpa only [Subfunctor.preimage_obj, Set.mem_preimage, hag] using hmem
  obtain ⟨q, hq⟩ := hmem'
  change q ≫ D.2.2.rep.snd g = a ≫ v.value at hq
  refine ⟨{ carrier := r.carrier, contained := r.contained, toBase := r.toBase, value := q },
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
      ⟨r, ⟨𝟙 r.siteObject, ?_⟩, ⟨b, hb⟩⟩⟩
  show X.1.map (𝟙 r.siteObject).op (g.app _ (q ≫ D.2.2.rep.snd g)) = r.value
  simpa [hq] using hag

/-- **A covering sieve of the small étale site is jointly surjective on scheme points.** Every
point of the scheme underlying an étale chart `U` is in the image of one member of a covering
family of `U`.

The point carries a geometric point of the algebraic space above it
(`AlgebraicGeometry.Space.exists_geo_lift_at_chart_point`), hence a point of the small étale
site in the sense of Stacks 04K0; joint surjectivity of the fibre functor of that point over
the covering sieve selects the member. -/
theorem exists_index_schemePoint_of_sieve_mem (X : AlgebraicSpaces B S hS)
    {U : SmallEtale B S hS X.1} {I : Type*}
    (V : I → SmallEtale B S hS X.1) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.ofArrows V f ∈ SmallEtale.topology B S hS X.1 U)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :
    ∃ i, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (f i))) := by
  obtain ⟨x, p, z', hz'⟩ := exists_geo_lift_at_chart_point B S hS X.1 U z
  obtain ⟨Z, k, hk, q, hq⟩ :=
    (etaleSitePoint B S hS X.1 x X.2).jointly_surjective (Sieve.ofArrows V f) hcov p
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨i, c, rfl⟩ := hk
  refine ⟨i, ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map c))
    (((BigFppfOver.toScheme B S hS).map q.1) z'), ?_⟩
  have hqv : q.1 ≫ (SmallEtale.toOver B S hS X.1).map (c ≫ f i) = p.1 :=
    congrArg Subtype.val hq
  rw [Functor.map_comp] at hqv
  rw [← hz', ← hqv, Functor.map_comp, Functor.map_comp]
  rfl

/-- A point of a scheme chart mapping to the scheme point of a field-valued point has its
canonical representative mapping to the class of that point. -/
private theorem pointsMap_class_schemePointRepresentative {W U : BigFppfOver B S hS} (k : W ⟶ U)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (z : (BigFppfOver.toScheme B S hS).obj W)
    (hz : (BigFppfOver.toScheme B S hS).map k z = schemePoint B S hS U p) :
    pointsMap B S hS _ (yoneda.map k) ((schemePointRepresentative B S hS W z).class B S hS _) =
      p.class B S hS _ := by
  apply injective_pointsToScheme B S hS U
  rw [pointsToScheme_pointsMap]
  change (BigFppfOver.toScheme B S hS).map k
    (schemePoint B S hS W (schemePointRepresentative B S hS W z)) = _
  rw [schemePointRepresentative_point]
  exact hz

/-! ### The chart ideal sheaf and the defining ideal -/

/-- On an affine étale chart, the ideal sheaf of `D ×_X U ⟶ U` is that of an ideal `K` of global
sections exactly when `K` is the defining ideal of `D` at that chart. -/
private theorem ker_rep_snd_eq_ofIdealTop_iff_definingIdealAt_eq (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    (haff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop K ↔ definingIdealAt B S hS X D (op V) = K := by
  have : IsAffine (unop ((SmallEtale.toOver B S hS X.1 ⋙
    BigFppfOver.toScheme B S hS).op.obj (op V))) := haff
  rw [ker_rep_snd_eq_ofIdealTop_definingIdealAt]
  exact ⟨Stacks.Divisors.ofIdealTop_injective, fun h => h ▸ rfl⟩

/-- **From the kernel on an affine chart to the defining ideal.** On an affine étale chart, if
the ideal sheaf of `D ×_X U ⟶ U` is the ideal sheaf of an ideal `K` of global sections, then `K`
is the defining ideal of `D` at that chart. -/
theorem definingIdealAt_eq_of_ker_rep_snd_eq (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    (haff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
    (h : ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop K) :
    definingIdealAt B S hS X D (op V) = K :=
  (ker_rep_snd_eq_ofIdealTop_iff_definingIdealAt_eq B S hS X D V haff K).1 h

/-- **From the defining ideal to the kernel on an affine chart.** The converse reading of
`AlgebraicGeometry.Space.definingIdealAt_eq_of_ker_rep_snd_eq`. -/
theorem ker_rep_snd_eq_ofIdealTop_of_definingIdealAt_eq (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    (haff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
    (h : definingIdealAt B S hS X D (op V) = K) :
    ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop K :=
  (ker_rep_snd_eq_ofIdealTop_iff_definingIdealAt_eq B S hS X D V haff K).2 h

/-- **An affine chart on which the defining ideal is generated by a nonzerodivisor satisfies
the chart condition.** This is the affine half of condition (4) ⟹ condition (3) of Stacks
083C, before the comparison with an arbitrary chart. -/
theorem isSchemeEffectiveCartierPullback_of_isRegular_span (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    (haff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (f : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)) (hf : IsRegular f)
    (hgen : definingIdealAt B S hS X D (op V) = Ideal.span {f}) :
    IsSchemeEffectiveCartierPullback B S hS X D V.1.left V.1.hom := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := haff
  rw [isSchemeEffectiveCartierPullback_iff,
    ker_rep_snd_eq_ofIdealTop_of_definingIdealAt_eq B S hS X D V haff _ hgen]
  exact Stacks.Divisors.isEffectiveCartierDivisor_ofIdealTop_span f hf

/-! ### Condition (4) implies condition (3) -/

/-- **Charts on which the inverse image is effective Cartier, one through every point, suffice
for condition (3).** If every point of `X` is in the image of an étale scheme chart on which
the inverse image of `D` is an effective Cartier divisor, then the inverse image of `D` is an
effective Cartier divisor on *every* étale scheme chart.

Given an arbitrary étale chart `U'`, a point `z` of its underlying scheme and a chart `V`
through its image, the common refinement `Z = V ×_X U'` is étale, hence flat and universally
open, over `U'` and its image contains `z`; and the ideal sheaf of `D ×_X Z` is the inverse
image along `Z ⟶ U'` of that of `D ×_X U'`, and is effective Cartier because `Z` lies flatly
over `V`.  So `Stacks.Divisors.isEffectiveCartierDivisor_of_flat_universallyOpen_pointwise`
applies. -/
theorem hasEffectiveCartierEtalePullbacks_of_pointwise_charts (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1)
    (h : ∀ x : points B S hS X.1,
      ∃ (V : BigFppfOver B S hS) (gV : yoneda.obj V ⟶ X.1)
        (v : points B S hS (yoneda.obj V)),
        IsEtale B S hS gV ∧ pointsMap B S hS (yoneda.obj V) gV v = x ∧
          IsSchemeEffectiveCartierPullback B S hS X D V gV) :
    HasEffectiveCartierEtalePullbacks B S hS X D := by
  intro U' g' hg'
  set T := BigFppfOver.toScheme B S hS
  rw [isSchemeEffectiveCartierPullback_iff]
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_flat_universallyOpen_pointwise _ ?_
  intro z
  set t := schemePointRepresentative B S hS U' z
  obtain ⟨V, gV, v, hgV, hv, hcart⟩ := h (pointsMap B S hS _ g' (t.class B S hS _))
  obtain ⟨v, rfl⟩ := Quot.exists_rep v
  obtain ⟨Z, a, b, hpb, ha, hb⟩ := exists_common_etale_chart B S hS X V U' gV g' hgV hg'
  have ha' : Etale (T.map a) := ha
  have hb' : Etale (T.map b) := hb
  obtain ⟨r, -, hr⟩ := exists_fieldValuedPoint_of_isPullback B S hS a b gV g' hpb v t hv
  have heq : (T.map b) (pointsToScheme B S hS Z (r.class B S hS _)) = z := by
    rw [← pointsToScheme_pointsMap B S hS b (r.class B S hS _), hr]
    exact schemePointRepresentative_point B S hS U' z
  have hZ : IsSchemeEffectiveCartierPullback B S hS X D Z (yoneda.map b ≫ g') := by
    rw [← hpb.w]
    exact isSchemeEffectiveCartierPullback_comp_of_flat B S hS X D gV a hcart
  refine ⟨T.obj Z, T.map b, inferInstance, inferInstance,
    ⟨pointsToScheme B S hS Z (r.class B S hS _), heq⟩, ?_⟩
  rw [← schemeKer_snd_comp B S hS D g' b]
  exact (isSchemeEffectiveCartierPullback_iff B S hS X D Z (yoneda.map b ≫ g')).1 hZ

/-- **An affine chart on which the defining ideal is the unit ideal, through a point off the
closed subspace.** If a point of `X` is not the image of any point of `D`, then it has an
affine étale neighbourhood on which the defining ideal of `D` is `⊤`: the inverse image of `D`
there is empty.

The point comes from a point of a surjective étale scheme chart `U`, whose image in `U` avoids
the closed set `D ×_X U`; an affine open of `U` inside the complement is the required chart. -/
theorem exists_affine_chart_definingIdealAt_eq_top (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (x : points B S hS X.1)
    (hx : ¬ ∃ d : points B S hS D.1.toFunctor,
      pointsMap B S hS D.1.toFunctor D.1.ι d = x) :
    ∃ (V : SmallEtale B S hS X.1) (v : points B S hS (yoneda.obj V.1.left)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) ∧
      pointsMap B S hS (yoneda.obj V.1.left) V.1.hom v = x ∧
      definingIdealAt B S hS X D (op V) = ⊤ := by
  obtain ⟨U, g, hsurj, hg⟩ := X.2.exists_atlas
  obtain ⟨p, hp⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U g).1 hsurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep p
  set T := BigFppfOver.toScheme B S hS
  set j := D.2.2.rep.snd g
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion (T.map j) := D.2.2.property_snd g
  have hrange : D.1.preimage g = Subfunctor.range (yoneda.map j) :=
    preimage_eq_range_rep_snd B S hS X D U g
  set y := schemePoint B S hS U p
  have hy : y ∉ Set.range (T.map j) := by
    rintro ⟨z, hz⟩
    set r := schemePointRepresentative B S hS (D.2.2.rep.pullback g) z
    have hq : (FieldValuedPoint.map B S hS _ (yoneda.map j) r).class B S hS _ =
        p.class B S hS _ :=
      pointsMap_class_schemePointRepresentative B S hS j p z hz
    have hmem : g.app _ (r.value ≫ j) ∈ D.1.obj (Opposite.op r.siteObject) := by
      show (r.value ≫ j) ∈ (D.1.preimage g).obj _
      rw [hrange]
      exact ⟨r.value, rfl⟩
    refine hx ⟨({ carrier := r.carrier
                  contained := r.contained
                  toBase := r.toBase
                  value := ⟨g.app _ (r.value ≫ j), hmem⟩ } :
        FieldValuedPoint B S hS D.1.toFunctor).class B S hS _, ?_⟩
    show pointsMap B S hS _ g ((FieldValuedPoint.map B S hS _ (yoneda.map j) r).class
      B S hS _) = _
    rw [pointsMap_class, ← pointsMap_class, hq]
    exact hp
  set O : (T.obj U).Opens :=
    ⟨(Set.range (T.map j))ᶜ, (T.map j).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨A, hA, hyA, hAO⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ O from hy)
  have hAB : B.Contains A.toScheme := (Scheme.size_coe_opens_le _ A).trans_lt U.left.property
  set U' : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (A.ι ≫ U.hom.hom) : B.obj hAB ⟶ B.obj hS)
  set k : U' ⟶ U := Over.homMk (ObjectProperty.homMk A.ι)
  have hkm : T.map k = A.ι := rfl
  have hketale : Etale (T.map k) := by
    rw [hkm]
    infer_instance
  have hgE : IsEtale B S hS g := isEtale_of_presheaf_etale B S hS hg
  have hg' : IsEtale B S hS (yoneda.map k ≫ g) :=
    isEtale_yoneda_map_comp B S hS g k hketale hgE
  set V : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map k ≫ g), presheaf_etale_of_isEtale B S hS hg'⟩
  set p' := schemePointRepresentative B S hS U' ⟨y, hyA⟩
  have hp'' : pointsMap B S hS _ (yoneda.map k) (p'.class B S hS _) = p.class B S hS _ :=
    pointsMap_class_schemePointRepresentative B S hS k p ⟨y, hyA⟩ rfl
  have haffU' : IsAffine (T.obj U') := hA
  refine ⟨V, p'.class B S hS _, hA, ?_, ?_⟩
  · show pointsMap B S hS _ g (pointsMap B S hS _ (yoneda.map k) (p'.class B S hS _)) = _
    rw [hp'']
    exact hp
  · have hpb := T.map_isPullback (IsPullback.of_hasPullback k j)
    have hci' : _root_.AlgebraicGeometry.IsClosedImmersion (T.map (pullback.fst k j)) :=
      MorphismProperty.of_isPullback hpb.flip inferInstance
    have hempty : IsEmpty (T.obj (pullback k j)) := ⟨fun z => by
      refine hAO ((T.map (pullback.fst k j) z)).property ?_
      exact ⟨T.map (pullback.snd k j) z, (congrArg (fun φ => φ z) hpb.w).symm⟩⟩
    have hrange' : D.1.preimage V.1.hom =
        Subfunctor.range (yoneda.map (pullback.fst k j)) := by
      show (D.1.preimage g).preimage (yoneda.map k) = _
      rw [hrange]
      exact (Subfunctor.range_snd_eq_preimage_range_of_isPullback
        (yoneda.map_isPullback (IsPullback.of_hasPullback k j).flip)).symm
    have haffV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hA
    refine definingIdealAt_eq_of_ker_rep_snd_eq B S hS X D V hA ⊤ ?_
    rw [ker_rep_snd_eq_ker_of_range_eq B S hS X D V.1.left _ V.1.hom _ hrange',
      Scheme.ker_eq_top_of_isEmpty]
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [Stacks.Divisors.ideal_ofIdealTop_top]
    simp

/-- **Condition (4) produces, at every point of `X`, an affine chart on which the defining
ideal is generated by a nonzerodivisor.** At a point of `|D|` this is condition (4) itself,
read through the identification of the chart ideal sheaf with the defining ideal; at a point
off `|D|` the defining ideal is the unit ideal, generated by the nonzerodivisor `1`. -/
theorem exists_affine_chart_isRegular_span_of_hasAffinePrincipal (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1)
    (h : HasAffinePrincipalEtaleNeighborhoods B S hS X D) (x : points B S hS X.1) :
    ∃ (V : SmallEtale B S hS X.1) (v : points B S hS (yoneda.obj V.1.left)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) ∧
      pointsMap B S hS (yoneda.obj V.1.left) V.1.hom v = x ∧
      ∃ f : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤),
        IsRegular f ∧ definingIdealAt B S hS X D (op V) = Ideal.span {f} := by
  by_cases hx : ∃ d : points B S hS D.1.toFunctor,
      pointsMap B S hS D.1.toFunctor D.1.ι d = x
  · obtain ⟨d, rfl⟩ := hx
    obtain ⟨U, g, v, hU, hg, hv, f, R, jj, e, hf, he, hj⟩ := h d
    have hcij : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map jj) := by
      rw [he]
      infer_instance
    refine ⟨⟨CostructuredArrow.mk g, presheaf_etale_of_isEtale B S hS hg⟩, v, hU, hv, f, hf,
      definingIdealAt_eq_of_ker_rep_snd_eq B S hS X D
        ⟨CostructuredArrow.mk g, presheaf_etale_of_isEtale B S hS hg⟩ hU _ ?_⟩
    rw [ker_rep_snd_eq_ker_of_range_eq B S hS X D U R g jj hj, he,
      Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
    rfl
  · obtain ⟨V, v, haff, hv, htop⟩ :=
      exists_affine_chart_definingIdealAt_eq_top B S hS X D x hx
    exact ⟨V, v, haff, hv, 1, isRegular_one, htop.trans Ideal.span_singleton_one.symm⟩

/-! ### Condition (1) implies the chart conditions -/

universe v₀ w₀

/-- **A trivialization of a sheaf of modules restricts along any arrow of the site.** If `M` is
isomorphic to the structure sheaf over `U` then it is so over every object lying over `U`. -/
def unitIsoRestrict (Y : RingedSite.{u, v₀, w₀})
    (M : SheafOfModules.{w₀} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {U W : Y.C} (k : W ⟶ U)
    (ε : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over U) ≅ M.over U) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ≅ M.over W :=
  (SheafOfModules.overMapUnitIso k).symm ≪≫
    (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) k).mapIso ε ≪≫
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) k).app M

/-- **A trivialization of the defining ideal sheaf on a chart exhibits a nonzerodivisor
generating the defining ideal there.** An isomorphism `𝒪_X|_V ≅ 𝓘_D|_V` carries the unit section
to a section `f` of `𝓘_D` over `V`; multiplication by `f` is then bijective from the regular
functions on `V` onto the defining ideal at `V`, so `f` is a nonzerodivisor and generates
it. -/
theorem exists_isRegular_span_definingIdealAt_of_unitIso (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (e : SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over V) ≅
      (definingIdealSheaf B S hS X D).toSheafOfModules.over V) :
    ∃ f : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤),
      IsRegular f ∧ definingIdealAt B S hS X D (op V) = Ideal.span {f} := by
  let A := Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)
  let W₀ : Over V := Over.mk (𝟙 V)
  let R₀ :=
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over V).obj.obj (op W₀)
  let φ := e.hom.val.app (op W₀)
  have hisoe : IsIso e.hom := ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩
  have hiso : IsIso φ :=
    (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op W₀)).map_isIso e.hom
  have hbij : Function.Bijective φ := (ConcreteCategory.isIso_iff_bijective φ).1 hiso
  have hone : ∀ a : R₀, (a • (1 : R₀) : R₀) = a := fun a => by rw [smul_eq_mul, mul_one]
  have hsm : ∀ a : R₀, φ a = a • φ (1 : R₀) := fun a =>
    (congrArg (fun z : R₀ => φ z) (hone a)).symm.trans
      (map_smul (ConcreteCategory.hom φ) a (1 : R₀))
  let f : A := (φ (1 : R₀)).val
  have key : ∀ a : A, ((φ a).val : A) = a * f := fun a => by rw [hsm a]; rfl
  refine ⟨f, ?_, ?_⟩
  · refine (Commute.isRegular_iff (fun _ => Commute.all _ _)).2 fun a b hab => ?_
    refine hbij.injective (Subtype.ext ?_)
    rw [key, key, mul_comm a f, mul_comm b f]
    exact hab
  · refine le_antisymm (fun x hx => ?_)
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (φ (1 : R₀)).property))
    obtain ⟨a, ha⟩ := hbij.surjective ⟨x, hx⟩
    have hv : ((φ a).val : A) = x := congrArg (fun y => (y.val : A)) ha
    rw [← hv, key a]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- **Stacks 083C, (1) ⟹ an affine principal chart at every point, through Stacks 0B8Q.** If
the defining ideal sheaf of `D` is finite locally free of rank one on the small étale site, then
every point of `X` has an affine étale chart above it on which the defining ideal of `D` is
generated by a nonzerodivisor.

Rank one on a covering family of the surjective étale chart `U₀` of an atlas gives a chart `V i`
on which `𝓘_D` is trivial and through which the chosen point of `U₀` lifts
(`exists_index_schemePoint_of_sieve_mem`); shrinking `V i` to an affine open around that lift
(`exists_affine_chart_at`) keeps the trivialization by `unitIsoRestrict`, and a trivialization
over an affine chart is a nonzerodivisor generator. -/
theorem exists_affine_chart_isRegular_span_of_isFiniteLocallyFree (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1)
    (hfree : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      (definingIdealSheaf B S hS X D).toSheafOfModules 1)
    (x : points B S hS X.1) :
    ∃ (V : SmallEtale B S hS X.1) (v : points B S hS (yoneda.obj V.1.left)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) ∧
      pointsMap B S hS (yoneda.obj V.1.left) V.1.hom v = x ∧
      ∃ f : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤),
        IsRegular f ∧ definingIdealAt B S hS X D (op V) = Ideal.span {f} := by
  set T := BigFppfOver.toScheme B S hS
  obtain ⟨U₀, g₀, hsurj, hetale⟩ := X.2.exists_atlas
  have hg₀ : IsEtale B S hS g₀ := isEtale_of_presheaf_etale B S hS hetale
  set U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk g₀, presheaf_etale_of_isEtale B S hS hg₀⟩
  obtain ⟨p, hp⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U₀ g₀).1 hsurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep p
  obtain ⟨I, V, k, hcov, hfreeV⟩ := hfree U
  obtain ⟨i, z', hz'⟩ := exists_index_schemePoint_of_sieve_mem B S hS X V k hcov
    (schemePoint B S hS U₀ p)
  obtain ⟨V', ι, haff', w₀, hw₀⟩ := exists_affine_chart_at B S hS X.1 (V i) z'
  obtain ⟨ιf, ⟨hcolim⟩⟩ := hfreeV i
  obtain ⟨f, hf, hgen⟩ := exists_isRegular_span_definingIdealAt_of_unitIso B S hS X D V'
    (unitIsoRestrict (smallEtaleRingedSite B S hS X.1 X.2) _ ι
      (@asIso _ _ _ _ (ιf default) (Limits.isIso_cofan_inj_of_unique ιf hcolim)))
  set q := schemePointRepresentative B S hS V'.1.left w₀
  have hw₀' : (T.map ι.hom.left) w₀ = z' := hw₀
  have hz : (T.map (ι.hom.left ≫ (k i).hom.left)) w₀ = schemePoint B S hS U₀ p := by
    rw [Functor.map_comp]
    show (T.map (k i).hom.left) ((T.map ι.hom.left) w₀) = _
    rw [hw₀']
    exact hz'
  have hqm : pointsMap B S hS _ (yoneda.map (ι.hom.left ≫ (k i).hom.left))
      (q.class B S hS _) = p.class B S hS _ :=
    pointsMap_class_schemePointRepresentative B S hS _ p w₀ hz
  have hm : V'.1.hom = yoneda.map (ι.hom.left ≫ (k i).hom.left) ≫ U.1.hom := by
    rw [Functor.map_comp, Category.assoc, CostructuredArrow.w (k i).hom,
      CostructuredArrow.w ι.hom]
  refine ⟨V', q.class B S hS _, haff', ?_, f, hf, hgen⟩
  have hstep : pointsMap B S hS _ V'.1.hom (q.class B S hS _) =
      pointsMap B S hS _ U.1.hom
        (pointsMap B S hS _ (yoneda.map (ι.hom.left ≫ (k i).hom.left))
          (q.class B S hS _)) :=
    congrArg (fun t => pointsMap B S hS _ t (q.class B S hS _)) hm
  rw [hstep, hqm]
  exact hp

/-- **Stacks 0B8Q for the defining ideal sheaf of an effective Cartier divisor.** On the small
étale site of an algebraic space, an invertible defining ideal sheaf is finite locally free of
rank one.

The site is locally ringed by Stacks 04KH, and the two sheafification hypotheses of
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'` hold for it at
`AddCommGrpCat.{u}`, which is the universe of the sections of `𝒪_X`. -/
theorem isFiniteLocallyFreeOfRank_one_definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : IsEffectiveCartierDivisor B S hS X D) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      (definingIdealSheaf B S hS X D).toSheafOfModules 1 := by
  have h₁ : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  have h₂ : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  have h₃ : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      (definingIdealSheaf B S hS X D).toSheafOfModules :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ h
  exact RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'
    (smallEtaleRingedSite B S hS X.1 X.2) _
    (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)

end AlgebraicGeometry.Space

end
