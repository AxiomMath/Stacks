module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCovers
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts

/-!
# Finite type quasi-coherent submodules over an étale presheaf, read on the charts of the base

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module, and let
`π : Y ⟶ X` be a morphism of presheaves, typically an algebraic space étale over `X`.  The étale
charts of `X` which factor through `Y` — pairs of an étale chart `T` of `X` and a morphism
`a : T ⟶ Y` over `X` — are the étale charts of `Y`, and the sections of the restriction of `F`
to `Y` over such a chart are the sections `F(T)`.  This file describes the finite type
quasi-coherent submodules of `F|_Y` in that language, without restricting `F` to `Y`:

* `AlgebraicGeometry.Space.ChartSubmodule F π` is a family of submodules `G(T, a)` of `F(T)`,
  one for every chart of `Y`, which is stable under restriction, whose membership is local, and
  which is *locally spanned*: every chart of `Y` is covered by affine charts on which `G` is the
  span of the restrictions of finitely many of its sections.

On the base, `π = 𝟙 X`, such a family is exactly a finite type quasi-coherent submodule of `F`
when `F` is quasi-coherent: `AlgebraicGeometry.Space.ChartSubmodule.toSubmodule` is that
submodule, and
`AlgebraicGeometry.Space.ChartSubmodule.isCartesianOnAffineCharts_toSubmodule` and
`AlgebraicGeometry.Space.ChartSubmodule.isFiniteTypeOnSite_toSubmodule` record that it is
cartesian on affine charts and of finite type.  Over a general `Y` it is the description of
Stacks 03DX(2) of a finite type quasi-coherent submodule of `F|_Y` on the affine charts of `Y`,
and that is what the étale dévissage of Stacks 0829 manipulates: restricting along a morphism
over `X` (`AlgebraicGeometry.Space.ChartSubmodule.comap`), forming suprema
(`AlgebraicGeometry.Space.ChartSubmodule.sup`), and spanning by finitely many sections over an
affine chart (`AlgebraicGeometry.Space.ChartSubmodule.spanOfChart`).

## Main results

* `AlgebraicGeometry.Space.mem_span_of_forall_mem_span_restrict`: a section over an affine chart
  which locally lies in the span of the restrictions of finitely many sections lies in their
  span.
* `AlgebraicGeometry.Space.mem_chartSpan_of_forall_pullback`: **the kernel of a map to a finite
  product of quotients commutes with flat base change of affine charts**, the computation
  underlying both the quasi-coherence of the pushforward along a quasi-compact open immersion
  into an affine chart and the cartesian property below.
* `AlgebraicGeometry.Space.ChartSubmodule.obj_eq_chartSpan` and
  `AlgebraicGeometry.Space.ChartSubmodule.fg_obj`: **a locally spanned family is cartesian on
  affine charts and finitely generated there**.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-! ### Charts over a presheaf over `X` -/

/-- A chart of `X` lying over `Y` stays over `Y` after restriction along a chart morphism. -/
theorem chartOver_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    {T T' : SmallEtale B S hS X} (g : T' ⟶ T) {a : yoneda.obj T.1.left ⟶ Y}
    (ha : a ≫ π = T.1.hom) : (yoneda.map g.hom.left ≫ a) ≫ π = T'.1.hom := by
  rw [Category.assoc, ha]
  exact CostructuredArrow.w g.hom

/-- The Yoneda image of the identity of a chart is the identity. -/
theorem yoneda_map_id_left (T : SmallEtale B S hS X) :
    yoneda.map (𝟙 T : T ⟶ T).hom.left = 𝟙 _ :=
  yoneda.map_id _

/-- Restriction along the identity of a chart is the identity. -/
theorem chartRes_id (F : Modules.{u, u} B S hS X hX) (T : SmallEtale B S hS X)
    (x : F.val.obj (op T)) : chartRes F (𝟙 T) x = x :=
  chartRestrictLinear_id F T x

variable (F : Modules.{u, u} B S hS X hX)

/-- A family of submodules of the sections of `F`, one for every chart of `X` lying over `Y`. -/
abbrev ChartSubmoduleFamily {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X) :=
  ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y), a ≫ π = T.1.hom →
    Submodule (chartRing B S hS X hX T) (F.val.obj (op T))

variable {F}

/-- The members of a chart family at two equal morphisms to `Y` agree. -/
theorem ChartSubmoduleFamily.congr {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (Q : ChartSubmoduleFamily F π) (T : SmallEtale B S hS X) {a a' : yoneda.obj T.1.left ⟶ Y}
    (h : a = a') (ha : a ≫ π = T.1.hom) (ha' : a' ≫ π = T.1.hom) :
    Q T a ha = Q T a' ha' := by
  subst h
  rfl

/-- Membership in a chart family transfers between two equal morphisms to `Y`. -/
theorem ChartSubmoduleFamily.mem_congr {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (Q : ChartSubmoduleFamily F π) (T : SmallEtale B S hS X) {a a' : yoneda.obj T.1.left ⟶ Y}
    (h : a = a') (ha : a ≫ π = T.1.hom) (ha' : a' ≫ π = T.1.hom) {x : F.val.obj (op T)}
    (hx : x ∈ Q T a ha) : x ∈ Q T a' ha' :=
  (Q.congr T h ha ha').le hx

variable (F)

/-- A chart family is *spanned* at a chart `(T₁, a₁)` of `Y` when `T₁` is affine and finitely
many sections over `T₁` span it there and, by restriction, at every affine chart over `T₁`. -/
def IsSpannedAt {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (Q : ChartSubmoduleFamily F π)
    (T₁ : SmallEtale B S hS X) (a₁ : yoneda.obj T₁.1.left ⟶ Y) (ha₁ : a₁ ≫ π = T₁.1.hom) :
    Prop :=
  IsAffine (chartScheme T₁) ∧ ∃ t : Set (F.val.obj (op T₁)), t.Finite ∧
    Q T₁ a₁ ha₁ = Submodule.span _ t ∧
    ∀ {T₂ : SmallEtale B S hS X} (h : T₂ ⟶ T₁), IsAffine (chartScheme T₂) →
      Q T₂ (yoneda.map h.hom.left ≫ a₁) (chartOver_comp h ha₁) =
        Submodule.span _ (chartRes F h '' t)

/-- **A finite type quasi-coherent submodule of `F|_Y`, read on the charts of `X` over `Y`.**
A family of submodules `obj T a` of the sections `F(T)`, for the charts `a : T ⟶ Y` over `X`,
which is stable under restriction, whose membership is local, and which is locally spanned by
finitely many sections over affine charts. -/
structure ChartSubmodule {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X) where
  /-- The submodule of the sections over a chart of `Y`. -/
  obj : ChartSubmoduleFamily F π
  /-- Stability under restriction. -/
  map {T T' : SmallEtale B S hS X} (g : T' ⟶ T) (a : yoneda.obj T.1.left ⟶ Y)
    (ha : a ≫ π = T.1.hom) {σ : F.val.obj (op T)} (hσ : σ ∈ obj T a ha) :
    chartRes F g σ ∈ obj T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha)
  /-- Membership is local. -/
  loc (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom)
    (σ : F.val.obj (op T)) {R : Sieve T} (hR : R ∈ SmallEtale.topology B S hS X T)
    (h : ∀ {T' : SmallEtale B S hS X} (g : T' ⟶ T), R g →
      chartRes F g σ ∈ obj T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha)) :
    σ ∈ obj T a ha
  /-- Local finite generation. -/
  lfg (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom) :
    Sieve.generate (fun T₁ (g₁ : T₁ ⟶ T) =>
        IsSpannedAt F obj T₁ (yoneda.map g₁.hom.left ≫ a) (chartOver_comp g₁ ha)) ∈
      SmallEtale.topology B S hS X T

variable {F}

/-! ### Spanned families -/

/-- A family spanned at a chart is spanned at every affine chart over it. -/
theorem IsSpannedAt.restrict {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    {Q : ChartSubmoduleFamily F π} {T₁ : SmallEtale B S hS X} {a₁ : yoneda.obj T₁.1.left ⟶ Y}
    {ha₁ : a₁ ≫ π = T₁.1.hom} (hQ : IsSpannedAt F Q T₁ a₁ ha₁) {T₂ : SmallEtale B S hS X}
    (h : T₂ ⟶ T₁) (hT₂ : IsAffine (chartScheme T₂)) :
    IsSpannedAt F Q T₂ (yoneda.map h.hom.left ≫ a₁) (chartOver_comp h ha₁) := by
  obtain ⟨-, t, ht, -, hspan⟩ := hQ
  refine ⟨hT₂, chartRes F h '' t, ht.image _, hspan h hT₂, fun {T₃} k hT₃ => ?_⟩
  rw [Set.image_image]
  refine (Q.congr T₃ ?_ _ _).trans ((hspan (k ≫ h) hT₃).trans ?_)
  · rw [yoneda_map_comp_left, Category.assoc]
  · congr 1
    exact Set.image_congr fun m _ => (modules_map_map F h k m).symm

/-- Spanned-ness only depends on the morphism to `Y` up to equality. -/
theorem IsSpannedAt.congr {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    {Q : ChartSubmoduleFamily F π} {T₁ : SmallEtale B S hS X} {a₁ a₁' : yoneda.obj T₁.1.left ⟶ Y}
    (e : a₁ = a₁') {ha₁ : a₁ ≫ π = T₁.1.hom} (ha₁' : a₁' ≫ π = T₁.1.hom)
    (hQ : IsSpannedAt F Q T₁ a₁ ha₁) : IsSpannedAt F Q T₁ a₁' ha₁' := by
  subst e
  exact hQ

/-- Spanned-ness transfers between two families which agree at a chart and at every affine
chart over it. -/
theorem IsSpannedAt.of_eq {Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π₁ : Y₁ ⟶ X}
    {π₂ : Y₂ ⟶ X} {Q₁ : ChartSubmoduleFamily F π₁} {Q₂ : ChartSubmoduleFamily F π₂}
    {T₁ : SmallEtale B S hS X}
    {a₁ : yoneda.obj T₁.1.left ⟶ Y₁} {ha₁ : a₁ ≫ π₁ = T₁.1.hom}
    {a₂ : yoneda.obj T₁.1.left ⟶ Y₂} {ha₂ : a₂ ≫ π₂ = T₁.1.hom}
    (hsp : IsSpannedAt F Q₁ T₁ a₁ ha₁)
    (h : ∀ {T₂ : SmallEtale B S hS X} (k : T₂ ⟶ T₁), IsAffine (chartScheme T₂) →
      Q₂ T₂ (yoneda.map k.hom.left ≫ a₂) (chartOver_comp k ha₂) =
        Q₁ T₂ (yoneda.map k.hom.left ≫ a₁) (chartOver_comp k ha₁))
    (h₀ : Q₂ T₁ a₂ ha₂ = Q₁ T₁ a₁ ha₁) : IsSpannedAt F Q₂ T₁ a₂ ha₂ := by
  obtain ⟨hA, t, ht, e0, hs⟩ := hsp
  exact ⟨hA, t, ht, h₀.trans e0, fun k hk => (h k hk).trans (hs k hk)⟩

/-! ### Descent of membership in a span -/

/-- **A section over an affine chart which locally lies in the span of the restrictions of
finitely many sections lies in their span**, `F` being cartesian on affine charts.  The covering
sieve is refined to a finite jointly faithfully flat family of affine charts and the membership
descends along it. -/
theorem mem_span_of_forall_mem_span_restrict (hF : IsCartesianOnAffineCharts F)
    {T : SmallEtale B S hS X} (hT : IsAffine (chartScheme T)) {t : Set (F.val.obj (op T))}
    (ht : t.Finite) {σ : F.val.obj (op T)} {R : Sieve T}
    (hR : R ∈ SmallEtale.topology B S hS X T)
    (h : ∀ {T' : SmallEtale B S hS X} (g : T' ⟶ T), R g → IsAffine (chartScheme T') →
      chartRes F g σ ∈ Submodule.span (chartRing B S hS X hX T') (chartRes F g '' t)) :
    σ ∈ Submodule.span (chartRing B S hS X hX T) t := by
  obtain ⟨n, z, φ, hzaff, hzR, hff⟩ := exists_finite_affine_faithfullyFlat_pi_le B S hS X hX hT hR
  have : Finite t := ht.to_subtype
  have hmem := mem_span_of_forall_restrict_mem_span F hF hT φ hzaff hff
    (fun m : t => (m : F.val.obj (op T))) (x := σ) fun i => by
      have := h (φ i) (hzR i) (hzaff i)
      rw [Set.image_eq_range] at this
      exact this
  rwa [Subtype.range_coe] at hmem

/-- The finite affine refinement of a covering sieve of an affine chart, with its covering and
faithful flatness properties together. -/
theorem exists_finite_affine_cover_le {T : SmallEtale B S hS X}
    (hT : IsAffine (chartScheme T)) {R : Sieve T} (hR : R ∈ SmallEtale.topology B S hS X T) :
    ∃ (n : ℕ) (z : Fin n → SmallEtale B S hS X) (φ : ∀ i, z i ⟶ T),
      (∀ i, IsAffine (chartScheme (z i))) ∧ (∀ i, R (φ i)) ∧
        Sieve.ofArrows z φ ∈ SmallEtale.topology B S hS X T ∧
        (RingHom.pi fun i => chartRestrict (hF := hX) (φ i)).FaithfullyFlat := by
  obtain ⟨n, z, φ, hzaff, hzT, hcov, hpre⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS X hT hR
  obtain ⟨hcov', het⟩ := Scheme.ofArrows_mem_etalePrecoverage_iff.1 hpre
  refine ⟨n, z, φ, hzaff, hzT, hcov, ?_⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj T)) := hT
  have (i : Fin n) : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X).obj (z i))) := hzaff i
  have (i : Fin n) : Flat ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X).map (φ i))) :=
    (Etale.iff_flat_and_formallyUnramified.1 (het i)).1
  exact Scheme.faithfullyFlat_pi_appTop
    (fun i => (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj (z i)))
    (fun i => (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X).map (φ i)))
    fun x => hcov' x

/-- The affine members of a covering sieve generate a covering sieve. -/
theorem generate_affine_mem {T : SmallEtale B S hS X} {R : Sieve T}
    (hR : R ∈ SmallEtale.topology B S hS X T) :
    Sieve.generate (fun T' (g : T' ⟶ T) => R g ∧ IsAffine (chartScheme T')) ∈
      SmallEtale.topology B S hS X T := by
  refine (SmallEtale.topology B S hS X).transitive hR _ fun {T'} g hg => ?_
  refine (SmallEtale.topology B S hS X).superset_covering ?_
    (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X T')
  intro T'' k hk
  obtain ⟨O, e, he⟩ := (Sieve.mem_ofArrows_iff _ _ k).1 hk
  refine ⟨openChart B S hS X T' O.down.1, e, openChartInclusion B S hS X T' O.down.1 ≫ g,
    ⟨R.downward_closed hg _, isAffine_chartScheme_openChart B S hS X T' O.down⟩, ?_⟩
  rw [he, Category.assoc]


/-! ### Sheafifying a restriction-stable family -/

/-- A chart family is stable under restriction. -/
def ChartSubmoduleFamily.IsStable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (Q : ChartSubmoduleFamily F π) : Prop :=
  ∀ {T T' : SmallEtale B S hS X} (g : T' ⟶ T) (a : yoneda.obj T.1.left ⟶ Y)
    (ha : a ≫ π = T.1.hom) {σ : F.val.obj (op T)}, σ ∈ Q T a ha →
      chartRes F g σ ∈ Q T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha)

/-- The sections which locally lie in a chart family. -/
def ChartSubmoduleFamily.sheafify {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (Q : ChartSubmoduleFamily F π) : ChartSubmoduleFamily F π := fun T a ha =>
  { carrier := {σ | ∃ R : Sieve T, R ∈ SmallEtale.topology B S hS X T ∧
      ∀ {T' : SmallEtale B S hS X} (g : T' ⟶ T), R g →
        chartRes F g σ ∈ Q T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha)}
    add_mem' := by
      rintro σ τ ⟨R₁, hR₁, h₁⟩ ⟨R₂, hR₂, h₂⟩
      refine ⟨R₁ ⊓ R₂, (SmallEtale.topology B S hS X).intersection_covering hR₁ hR₂,
        fun g hg => ?_⟩
      rw [map_add]
      exact add_mem (h₁ g hg.1) (h₂ g hg.2)
    zero_mem' := ⟨⊤, (SmallEtale.topology B S hS X).top_mem T, fun g _ => by
      rw [map_zero]
      exact zero_mem _⟩
    smul_mem' := by
      rintro r σ ⟨R, hR, h⟩
      refine ⟨R, hR, fun g hg => ?_⟩
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ (h g hg) }

/-- A section lies in the sheafification of a chart family exactly when its restrictions to the
members of some covering sieve lie in the family. -/
theorem ChartSubmoduleFamily.mem_sheafify {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (Q : ChartSubmoduleFamily F π) {T : SmallEtale B S hS X} {a : yoneda.obj T.1.left ⟶ Y}
    {ha : a ≫ π = T.1.hom} {σ : F.val.obj (op T)} :
    σ ∈ Q.sheafify T a ha ↔ ∃ R : Sieve T, R ∈ SmallEtale.topology B S hS X T ∧
      ∀ {T' : SmallEtale B S hS X} (g : T' ⟶ T), R g →
        chartRes F g σ ∈ Q T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha) :=
  Iff.rfl

/-- A restriction-stable family lies in its sheafification. -/
theorem ChartSubmoduleFamily.le_sheafify {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    {Q : ChartSubmoduleFamily F π} (hQ : Q.IsStable) (T : SmallEtale B S hS X)
    (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom) :
    Q T a ha ≤ Q.sheafify T a ha := fun _ hσ =>
  ⟨⊤, (SmallEtale.topology B S hS X).top_mem T, fun g _ => hQ g a ha hσ⟩

/-- At a chart where a restriction-stable family is spanned, its sheafification is itself. -/
theorem ChartSubmoduleFamily.sheafify_eq_of_isSpannedAt (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} {Q : ChartSubmoduleFamily F π}
    (hQ : Q.IsStable) {T : SmallEtale B S hS X} {a : yoneda.obj T.1.left ⟶ Y}
    {ha : a ≫ π = T.1.hom} (hsp : IsSpannedAt F Q T a ha) :
    Q.sheafify T a ha = Q T a ha := by
  refine le_antisymm (fun σ hσ => ?_) (Q.le_sheafify hQ T a ha)
  obtain ⟨hT, t, ht, h0, hspan⟩ := hsp
  obtain ⟨R, hR, h⟩ := hσ
  rw [h0]
  exact mem_span_of_forall_mem_span_restrict hF hT ht hR fun g hg hT' => by
    rw [← hspan g hT']
    exact h g hg

/-- Spanned-ness passes to the sheafification. -/
theorem ChartSubmoduleFamily.isSpannedAt_sheafify (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} {Q : ChartSubmoduleFamily F π}
    (hQ : Q.IsStable) {T : SmallEtale B S hS X} {a : yoneda.obj T.1.left ⟶ Y}
    {ha : a ≫ π = T.1.hom} (hsp : IsSpannedAt F Q T a ha) :
    IsSpannedAt F Q.sheafify T a ha := by
  obtain ⟨hT, t, ht, h0, hspan⟩ := id hsp
  refine ⟨hT, t, ht, (Q.sheafify_eq_of_isSpannedAt hF hQ hsp).trans h0,
    fun {T₂} h hT₂ => ?_⟩
  rw [Q.sheafify_eq_of_isSpannedAt hF hQ (hsp.restrict h hT₂)]
  exact hspan h hT₂

/-- **The chart submodule obtained by sheafifying a restriction-stable family which is locally
spanned.** -/
def ChartSubmoduleFamily.toChartSubmodule (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (Q : ChartSubmoduleFamily F π)
    (hQ : Q.IsStable)
    (hspan : ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y)
      (ha : a ≫ π = T.1.hom),
      Sieve.generate (fun T₁ (g₁ : T₁ ⟶ T) =>
          IsSpannedAt F Q T₁ (yoneda.map g₁.hom.left ≫ a) (chartOver_comp g₁ ha)) ∈
        SmallEtale.topology B S hS X T) :
    ChartSubmodule F π where
  obj := Q.sheafify
  map {T T'} g a ha σ hσ := by
    obtain ⟨R, hR, h⟩ := hσ
    refine ⟨R.pullback g, (SmallEtale.topology B S hS X).pullback_stable g hR,
      fun {T''} k hk => ?_⟩
    have h' := h (k ≫ g) hk
    rw [← modules_map_map] at h'
    exact Q.mem_congr _ (by rw [yoneda_map_comp_left, Category.assoc]) _ _ h'
  loc T a ha σ {R} hR h := by
    have h2 : ∀ (T' : SmallEtale B S hS X) (g : T' ⟶ T), R g →
        ∃ R' : Sieve T', R' ∈ SmallEtale.topology B S hS X T' ∧
          ∀ {T'' : SmallEtale B S hS X} (k : T'' ⟶ T'), R' k →
            chartRes F k (chartRes F g σ) ∈ Q T''
              (yoneda.map k.hom.left ≫ yoneda.map g.hom.left ≫ a)
              (chartOver_comp k (chartOver_comp g ha)) := fun T' g hg => h g hg
    choose R' hR' h' using h2
    refine ⟨Sieve.bind R.arrows (fun T' g hg => R' T' g hg),
      (SmallEtale.topology B S hS X).bind_covering hR (fun T' g hg => hR' T' g hg), ?_⟩
    rintro T'' x ⟨T', k, g, hg, hk, rfl⟩
    have := h' T' g hg k hk
    rw [modules_map_map] at this
    exact Q.mem_congr _ (by rw [yoneda_map_comp_left, Category.assoc]) _ _ this
  lfg T a ha := by
    refine (SmallEtale.topology B S hS X).superset_covering ?_ (hspan T a ha)
    rintro T' k ⟨T₁, l, g₁, hg₁, rfl⟩
    exact ⟨T₁, l, g₁, Q.isSpannedAt_sheafify hF hQ hg₁, rfl⟩

/-- The family of `ChartSubmoduleFamily.toChartSubmodule` is the sheafification. -/
theorem ChartSubmoduleFamily.toChartSubmodule_obj (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (Q : ChartSubmoduleFamily F π)
    (hQ : Q.IsStable) (hspan) :
    (Q.toChartSubmodule hF hQ hspan).obj = Q.sheafify :=
  rfl

/-! ### Restriction along a morphism over `X` -/

/-- **Restriction of a chart submodule along a morphism `ψ : Y' ⟶ Y` over `X`**: a chart of
`Y'` is read as a chart of `Y` through `ψ`. -/
def ChartSubmodule.comap {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (D : ChartSubmodule F π) (ψ : Y' ⟶ Y) (π' : Y' ⟶ X) (hψ : ψ ≫ π = π') :
    ChartSubmodule F π' where
  obj T a ha := D.obj T (a ≫ ψ) (by rw [Category.assoc, hψ]; exact ha)
  map g a ha σ hσ := D.obj.mem_congr _ (Category.assoc _ _ _) _ _ (D.map g (a ≫ ψ) _ hσ)
  loc T a ha σ R hR h := D.loc T (a ≫ ψ) _ σ hR fun g hg =>
    D.obj.mem_congr _ (Category.assoc _ _ _).symm _ _ (h g hg)
  lfg T a ha := by
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      (D.lfg T (a ≫ ψ) (by rw [Category.assoc, hψ]; exact ha))
    rintro T' k ⟨T₁, l, g₁, ⟨hA, t, ht, h0, hsp⟩, rfl⟩
    refine ⟨T₁, l, g₁, ⟨hA, t, ht, (D.obj.congr _ (Category.assoc _ _ _) _ _).trans h0,
      fun {T₂} h hT₂ => (D.obj.congr _ ?_ _ _).trans (hsp h hT₂)⟩, rfl⟩
    simp only [Category.assoc]

/-- The restriction of a chart submodule along `ψ`, at a chart `a` of `Y'`, is the chart
submodule at the chart `a ≫ ψ` of `Y`. -/
theorem ChartSubmodule.comap_obj {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (D : ChartSubmodule F π) (ψ : Y' ⟶ Y) (π' : Y' ⟶ X) (hψ : ψ ≫ π = π')
    (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y') (ha : a ≫ π' = T.1.hom) :
    (D.comap ψ π' hψ).obj T a ha =
      D.obj T (a ≫ ψ) (by rw [Category.assoc, hψ]; exact ha) :=
  rfl

/-- Membership in a chart submodule may be tested on the arrows of a family generating a
covering sieve. -/
theorem ChartSubmodule.mem_of_generate {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X}
    (D : ChartSubmodule F π) {T : SmallEtale B S hS X} (a : yoneda.obj T.1.left ⟶ Y)
    (ha : a ≫ π = T.1.hom) {P : Presieve T}
    (hP : Sieve.generate P ∈ SmallEtale.topology B S hS X T) {σ : F.val.obj (op T)}
    (h : ∀ {T' : SmallEtale B S hS X} (g : T' ⟶ T), P g →
      chartRes F g σ ∈ D.obj T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha)) :
    σ ∈ D.obj T a ha := by
  refine D.loc T a ha σ hP fun {T'} g hg => ?_
  obtain ⟨T'', d₁, d₂, hd₂, rfl⟩ := hg
  have := D.map d₁ _ _ (h d₂ hd₂)
  rw [modules_map_map] at this
  exact D.obj.mem_congr _ (by rw [yoneda_map_comp_left, Category.assoc]) _ _ this

/-- Comparison of two chart submodules, possibly over different presheaves, at two charts with
the same underlying chart of `X`, may be tested on affine charts. -/
theorem ChartSubmodule.le_of_forall_affine {Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π₁ : Y₁ ⟶ X} {π₂ : Y₂ ⟶ X} (D₁ : ChartSubmodule F π₁) (D₂ : ChartSubmodule F π₂)
    {T : SmallEtale B S hS X} (a₁ : yoneda.obj T.1.left ⟶ Y₁) (ha₁ : a₁ ≫ π₁ = T.1.hom)
    (a₂ : yoneda.obj T.1.left ⟶ Y₂) (ha₂ : a₂ ≫ π₂ = T.1.hom)
    (h : ∀ {T' : SmallEtale B S hS X} (g : T' ⟶ T), IsAffine (chartScheme T') →
      D₁.obj T' (yoneda.map g.hom.left ≫ a₁) (chartOver_comp g ha₁) ≤
        D₂.obj T' (yoneda.map g.hom.left ≫ a₂) (chartOver_comp g ha₂)) :
    D₁.obj T a₁ ha₁ ≤ D₂.obj T a₂ ha₂ := fun _ hσ =>
  D₂.mem_of_generate a₂ ha₂ (generate_affine_mem (R := ⊤)
    ((SmallEtale.topology B S hS X).top_mem T)) fun g hg => h g hg.2 (D₁.map g a₁ ha₁ hσ)

/-! ### Glueing along an elementary distinguished square -/

section Glue

variable {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πW : W ⟶ X} {U : Subfunctor W}
    {f : V ⟶ W}

/-- A chart of `X` over `W` restricted along `d` and factored through `U` is a chart over `U`. -/
theorem chartOver_of_subfunctor {T T' : SmallEtale B S hS X} {a : yoneda.obj T.1.left ⟶ W}
    (ha : a ≫ πW = T.1.hom) (d : T' ⟶ T) {u : yoneda.obj T'.1.left ⟶ U.toFunctor}
    (hu : u ≫ U.ι = yoneda.map d.hom.left ≫ a) : u ≫ U.ι ≫ πW = T'.1.hom := by
  rw [← Category.assoc, hu]
  exact chartOver_comp d ha

/-- A chart of `X` over `W` restricted along `d` and factored through `V` is a chart over `V`. -/
theorem chartOver_of_etale {T T' : SmallEtale B S hS X} {a : yoneda.obj T.1.left ⟶ W}
    (ha : a ≫ πW = T.1.hom) (d : T' ⟶ T) {v : yoneda.obj T'.1.left ⟶ V}
    (hv : v ≫ f = yoneda.map d.hom.left ≫ a) : v ≫ f ≫ πW = T'.1.hom := by
  rw [← Category.assoc, hv]
  exact chartOver_comp d ha

/-- The sections whose restrictions to the charts over `U` lie in `DU` and whose restrictions
to the charts over `V` lie in `DV`. -/
def glueFamily (DU : ChartSubmodule F (U.ι ≫ πW)) (DV : ChartSubmodule F (f ≫ πW)) :
    ChartSubmoduleFamily F πW := fun T a ha =>
  { carrier := {σ | (∀ (T' : SmallEtale B S hS X) (d : T' ⟶ T)
        (u : yoneda.obj T'.1.left ⟶ U.toFunctor) (hu : u ≫ U.ι = yoneda.map d.hom.left ≫ a),
        chartRes F d σ ∈ DU.obj T' u (chartOver_of_subfunctor ha d hu)) ∧
      ∀ (T' : SmallEtale B S hS X) (d : T' ⟶ T) (v : yoneda.obj T'.1.left ⟶ V)
        (hv : v ≫ f = yoneda.map d.hom.left ≫ a),
        chartRes F d σ ∈ DV.obj T' v (chartOver_of_etale ha d hv)}
    add_mem' := fun {σ τ} hσ hτ => ⟨fun T' d u hu => by
        rw [map_add]; exact add_mem (hσ.1 T' d u hu) (hτ.1 T' d u hu),
      fun T' d v hv => by rw [map_add]; exact add_mem (hσ.2 T' d v hv) (hτ.2 T' d v hv)⟩
    zero_mem' := ⟨fun T' d u hu => by rw [map_zero]; exact zero_mem _,
      fun T' d v hv => by rw [map_zero]; exact zero_mem _⟩
    smul_mem' := fun r σ hσ => ⟨fun T' d u hu => by
        rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hσ.1 T' d u hu),
      fun T' d v hv => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hσ.2 T' d v hv)⟩ }

variable (DU : ChartSubmodule F (U.ι ≫ πW)) (DV : ChartSubmodule F (f ≫ πW))

/-- The glued family is stable under restriction. -/
theorem glueFamily_isStable : (glueFamily DU DV).IsStable := by
  intro T T' g a ha σ hσ
  refine ⟨fun T'' d u hu => ?_, fun T'' d v hv => ?_⟩
  · have := hσ.1 T'' (d ≫ g) u (by rw [hu, yoneda_map_comp_left, Category.assoc])
    rw [← modules_map_map] at this
    exact this
  · have := hσ.2 T'' (d ≫ g) v (by rw [hv, yoneda_map_comp_left, Category.assoc])
    rw [← modules_map_map] at this
    exact this

/-- The two prescriptions agree on the charts over both `U` and `V`. -/
def GlueCompatible : Prop :=
  (∀ (T : SmallEtale B S hS X) (u : yoneda.obj T.1.left ⟶ U.toFunctor)
      (v : yoneda.obj T.1.left ⟶ V) (_ : v ≫ f = u ≫ U.ι) (hu : u ≫ U.ι ≫ πW = T.1.hom)
      (hv : v ≫ f ≫ πW = T.1.hom), DU.obj T u hu = DV.obj T v hv) ∧
    ∀ (T : SmallEtale B S hS X) (v₁ v₂ : yoneda.obj T.1.left ⟶ V) (_ : v₁ ≫ f = v₂ ≫ f)
      (hv₁ : v₁ ≫ f ≫ πW = T.1.hom) (hv₂ : v₂ ≫ f ≫ πW = T.1.hom),
      DV.obj T v₁ hv₁ = DV.obj T v₂ hv₂

variable {DU DV}

/-- At a chart factoring through `U`, the glued family is `DU`. -/
theorem glueFamily_subfunctor (hc : GlueCompatible DU DV) (T : SmallEtale B S hS X)
    (u : yoneda.obj T.1.left ⟶ U.toFunctor) (hu : u ≫ U.ι ≫ πW = T.1.hom)
    (hu' : (u ≫ U.ι) ≫ πW = T.1.hom) :
    glueFamily DU DV T (u ≫ U.ι) hu' = DU.obj T u hu := by
  refine le_antisymm (fun σ hσ => ?_) (fun σ hσ => ⟨fun T' d u' hu'' => ?_, fun T' d v hv => ?_⟩)
  · have := hσ.1 T (𝟙 T) u (by simp)
    rw [chartRes_id] at this
    exact this
  · have hmono : u' = yoneda.map d.hom.left ≫ u := by
      rw [← cancel_mono U.ι, hu'', Category.assoc]
    exact DU.obj.mem_congr _ hmono.symm _ _ (DU.map d u hu hσ)
  · rw [← hc.1 T' (yoneda.map d.hom.left ≫ u) v (by rw [hv, Category.assoc]) _ _]
    exact DU.map d u hu hσ

/-- At a chart factoring through `V`, the glued family is `DV`. -/
theorem glueFamily_etale (hc : GlueCompatible DU DV) (T : SmallEtale B S hS X)
    (v : yoneda.obj T.1.left ⟶ V) (hv : v ≫ f ≫ πW = T.1.hom)
    (hv' : (v ≫ f) ≫ πW = T.1.hom) :
    glueFamily DU DV T (v ≫ f) hv' = DV.obj T v hv := by
  refine le_antisymm (fun σ hσ => ?_) (fun σ hσ => ⟨fun T' d u hu => ?_, fun T' d v' hv'' => ?_⟩)
  · have := hσ.2 T (𝟙 T) v (by simp)
    rw [chartRes_id] at this
    exact this
  · rw [hc.1 T' u (yoneda.map d.hom.left ≫ v) (by rw [hu, Category.assoc]) _ _]
    exact DV.map d v hv hσ
  · rw [hc.2 T' v' (yoneda.map d.hom.left ≫ v) (by rw [hv'', Category.assoc]) _ _]
    exact DV.map d v hv hσ

/-- At a chart equal to one factoring through `U`, the glued family is `DU`. -/
theorem glueFamily_eq_of_subfunctor (hc : GlueCompatible DU DV) (T : SmallEtale B S hS X)
    (a : yoneda.obj T.1.left ⟶ W) (ha : a ≫ πW = T.1.hom)
    (u : yoneda.obj T.1.left ⟶ U.toFunctor) (hu : u ≫ U.ι ≫ πW = T.1.hom)
    (h : a = u ≫ U.ι) : glueFamily DU DV T a ha = DU.obj T u hu := by
  subst h
  exact glueFamily_subfunctor hc T u hu ha

/-- At a chart equal to one factoring through `V`, the glued family is `DV`. -/
theorem glueFamily_eq_of_etale (hc : GlueCompatible DU DV) (T : SmallEtale B S hS X)
    (a : yoneda.obj T.1.left ⟶ W) (ha : a ≫ πW = T.1.hom)
    (v : yoneda.obj T.1.left ⟶ V) (hv : v ≫ f ≫ πW = T.1.hom)
    (h : a = v ≫ f) : glueFamily DU DV T a ha = DV.obj T v hv := by
  subst h
  exact glueFamily_etale hc T v hv ha

/-- **Glueing two chart submodules along an elementary distinguished square.**  Given chart
submodules over the open subspace `U ⊂ W` and over the étale member `f : V ⟶ W`, which agree on
the charts over both and on two charts of `V` with the same image in `W`, the sections whose
restrictions lie in both form a chart submodule over `W`. -/
def ChartSubmodule.glue
    (hcov : ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ W),
      Sieve.generate (fun T' (g : T' ⟶ T) =>
          (∃ u : yoneda.obj T'.1.left ⟶ U.toFunctor, u ≫ U.ι = yoneda.map g.hom.left ≫ a) ∨
            ∃ v : yoneda.obj T'.1.left ⟶ V, v ≫ f = yoneda.map g.hom.left ≫ a) ∈
        SmallEtale.topology B S hS X T)
    (hc : GlueCompatible DU DV) : ChartSubmodule F πW where
  obj := glueFamily DU DV
  map g a ha σ hσ := glueFamily_isStable DU DV g a ha hσ
  loc T a ha σ R hR h := by
    refine ⟨fun T' d u hu => ?_, fun T' d v hv => ?_⟩
    · refine DU.loc T' u _ _ ((SmallEtale.topology B S hS X).pullback_stable d hR)
        fun {T''} k hk => ?_
      have := (h (k ≫ d) hk).1 T'' (𝟙 _) (yoneda.map k.hom.left ≫ u)
        (by rw [Category.assoc, hu, yoneda_map_comp_left, Category.assoc, yoneda_map_id_left,
          Category.id_comp])
      rw [chartRes_id, ← modules_map_map] at this
      exact this
    · refine DV.loc T' v _ _ ((SmallEtale.topology B S hS X).pullback_stable d hR)
        fun {T''} k hk => ?_
      have := (h (k ≫ d) hk).2 T'' (𝟙 _) (yoneda.map k.hom.left ≫ v)
        (by rw [Category.assoc, hv, yoneda_map_comp_left, Category.assoc, yoneda_map_id_left,
          Category.id_comp])
      rw [chartRes_id, ← modules_map_map] at this
      exact this
  lfg T a ha := by
    refine (SmallEtale.topology B S hS X).transitive (hcov T a) _ fun {T'} g hg => ?_
    obtain ⟨T'', d₁, d₂, hd₂, rfl⟩ := hg
    rcases hd₂ with ⟨u, hu⟩ | ⟨v, hv⟩
    · have hu' : (yoneda.map d₁.hom.left ≫ u) ≫ U.ι ≫ πW = T'.1.hom :=
        calc (yoneda.map d₁.hom.left ≫ u) ≫ U.ι ≫ πW
            = yoneda.map d₁.hom.left ≫ (u ≫ U.ι) ≫ πW := by simp only [Category.assoc]
          _ = (yoneda.map (d₁ ≫ d₂).hom.left ≫ a) ≫ πW := by
            rw [hu, yoneda_map_comp_left]; simp only [Category.assoc]
          _ = T'.1.hom := chartOver_comp _ ha
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (DU.lfg T' (yoneda.map d₁.hom.left ≫ u) hu')
      rintro T₁ k ⟨T₂, l, g₁, hg₁, rfl⟩
      have key : ∀ {T₃ : SmallEtale B S hS X} (m : T₃ ⟶ T₂),
          yoneda.map m.hom.left ≫ yoneda.map (g₁ ≫ d₁ ≫ d₂).hom.left ≫ a =
            (yoneda.map m.hom.left ≫ yoneda.map g₁.hom.left ≫ yoneda.map d₁.hom.left ≫ u) ≫
              U.ι := by
        intro T₃ m
        simp only [yoneda_map_comp_left, Category.assoc, hu]
      have key0 : yoneda.map (g₁ ≫ d₁ ≫ d₂).hom.left ≫ a =
          (yoneda.map g₁.hom.left ≫ yoneda.map d₁.hom.left ≫ u) ≫ U.ι := by
        simp only [yoneda_map_comp_left, Category.assoc, hu]
      refine ⟨T₂, l, g₁ ≫ d₁ ≫ d₂, hg₁.of_eq (fun {T₃} m _ =>
        glueFamily_eq_of_subfunctor hc _ _ _ _ _ (key m))
        (glueFamily_eq_of_subfunctor hc _ _ _ _ _ key0), by simp only [Category.assoc]⟩
    · have hv' : (yoneda.map d₁.hom.left ≫ v) ≫ f ≫ πW = T'.1.hom :=
        calc (yoneda.map d₁.hom.left ≫ v) ≫ f ≫ πW
            = yoneda.map d₁.hom.left ≫ (v ≫ f) ≫ πW := by simp only [Category.assoc]
          _ = (yoneda.map (d₁ ≫ d₂).hom.left ≫ a) ≫ πW := by
            rw [hv, yoneda_map_comp_left]; simp only [Category.assoc]
          _ = T'.1.hom := chartOver_comp _ ha
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (DV.lfg T' (yoneda.map d₁.hom.left ≫ v) hv')
      rintro T₁ k ⟨T₂, l, g₁, hg₁, rfl⟩
      have key : ∀ {T₃ : SmallEtale B S hS X} (m : T₃ ⟶ T₂),
          yoneda.map m.hom.left ≫ yoneda.map (g₁ ≫ d₁ ≫ d₂).hom.left ≫ a =
            (yoneda.map m.hom.left ≫ yoneda.map g₁.hom.left ≫ yoneda.map d₁.hom.left ≫ v) ≫
              f := by
        intro T₃ m
        simp only [yoneda_map_comp_left, Category.assoc, hv]
      have key0 : yoneda.map (g₁ ≫ d₁ ≫ d₂).hom.left ≫ a =
          (yoneda.map g₁.hom.left ≫ yoneda.map d₁.hom.left ≫ v) ≫ f := by
        simp only [yoneda_map_comp_left, Category.assoc, hv]
      refine ⟨T₂, l, g₁ ≫ d₁ ≫ d₂, hg₁.of_eq (fun {T₃} m _ =>
        glueFamily_eq_of_etale hc _ _ _ _ _ (key m))
        (glueFamily_eq_of_etale hc _ _ _ _ _ key0), by simp only [Category.assoc]⟩

/-- The family of `ChartSubmodule.glue` is the glued family. -/
theorem ChartSubmodule.glue_obj (hcov) (hc : GlueCompatible DU DV) :
    (ChartSubmodule.glue (DU := DU) (DV := DV) hcov hc).obj = glueFamily DU DV :=
  rfl

end Glue

/-! ### Suprema and the zero submodule -/

/-- The supremum of two chart submodules. -/
def ChartSubmodule.sup (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (D₁ D₂ : ChartSubmodule F π) :
    ChartSubmodule F π :=
  ChartSubmoduleFamily.toChartSubmodule hF (fun T a ha => D₁.obj T a ha ⊔ D₂.obj T a ha)
    (fun {T T'} g a ha σ hσ => by
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hσ
      rw [map_add]
      exact add_mem (Submodule.mem_sup_left (D₁.map g a ha hx))
        (Submodule.mem_sup_right (D₂.map g a ha hy)))
    (fun T a ha => by
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (generate_affine_mem ((SmallEtale.topology B S hS X).intersection_covering
          (D₁.lfg T a ha) (D₂.lfg T a ha)))
      rintro T' k ⟨T₁, l, g, ⟨⟨⟨A₁, l₁, g₁, h₁, e₁⟩, ⟨A₂, l₂, g₂, h₂, e₂⟩⟩, hT₁⟩, rfl⟩
      refine ⟨T₁, l, g, ?_, rfl⟩
      have s₁ := (h₁.restrict l₁ hT₁).congr (by rw [← e₁, yoneda_map_comp_left,
        Category.assoc]) (chartOver_comp g ha)
      have s₂ := (h₂.restrict l₂ hT₁).congr (by rw [← e₂, yoneda_map_comp_left,
        Category.assoc]) (chartOver_comp g ha)
      obtain ⟨-, t₁, ht₁, h0₁, hsp₁⟩ := s₁
      obtain ⟨-, t₂, ht₂, h0₂, hsp₂⟩ := s₂
      refine ⟨hT₁, t₁ ∪ t₂, ht₁.union ht₂, ?_, fun {T₂} h hT₂ => ?_⟩
      · change D₁.obj _ _ _ ⊔ D₂.obj _ _ _ = _
        rw [h0₁, h0₂, Submodule.span_union]
      · change D₁.obj _ _ _ ⊔ D₂.obj _ _ _ = _
        rw [hsp₁ h hT₂, hsp₂ h hT₂, Set.image_union, Submodule.span_union])

/-- The first chart submodule lies in the supremum. -/
theorem ChartSubmodule.le_sup_left (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (D₁ D₂ : ChartSubmodule F π)
    (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom) :
    D₁.obj T a ha ≤ (D₁.sup hF D₂).obj T a ha := fun _ hσ =>
  ⟨⊤, (SmallEtale.topology B S hS X).top_mem T, fun g _ =>
    Submodule.mem_sup_left (D₁.map g a ha hσ)⟩

/-- The second chart submodule lies in the supremum. -/
theorem ChartSubmodule.le_sup_right (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (D₁ D₂ : ChartSubmodule F π)
    (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom) :
    D₂.obj T a ha ≤ (D₁.sup hF D₂).obj T a ha := fun _ hσ =>
  ⟨⊤, (SmallEtale.topology B S hS X).top_mem T, fun g _ =>
    Submodule.mem_sup_right (D₂.map g a ha hσ)⟩

/-- The zero chart submodule. -/
def ChartSubmodule.bot (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X) : ChartSubmodule F π :=
  ChartSubmoduleFamily.toChartSubmodule hF (fun _ _ _ => ⊥)
    (fun {T T'} g a ha σ hσ => by
      rw [Submodule.mem_bot] at hσ ⊢
      rw [hσ, map_zero])
    (fun T a ha => by
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (generate_affine_mem (R := ⊤) ((SmallEtale.topology B S hS X).top_mem T))
      rintro T' k ⟨T₁, l, g, ⟨-, hT₁⟩, rfl⟩
      refine ⟨T₁, l, g, ⟨hT₁, ∅, Set.finite_empty, ?_, fun {T₂} h _ => ?_⟩, rfl⟩
      · exact Submodule.span_empty.symm
      · rw [Set.image_empty, Submodule.span_empty])

/-! ### The span of finitely many sections over a chart -/

/-- The chart morphism `T ⟶ V₀` determined by a morphism `yoneda T ⟶ yoneda V₀` over `X`. -/
def chartHomOfYoneda {V₀ T : SmallEtale B S hS X} (c : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left)
    (hc : c ≫ V₀.1.hom = T.1.hom) : T ⟶ V₀ :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage c)
    (by rw [Functor.map_preimage]; exact hc))

/-- The Yoneda image of `chartHomOfYoneda c hc` is `c`. -/
theorem yoneda_map_chartHomOfYoneda {V₀ T : SmallEtale B S hS X}
    (c : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left) (hc : c ≫ V₀.1.hom = T.1.hom) :
    yoneda.map (chartHomOfYoneda c hc).hom.left = c :=
  Functor.map_preimage _ _

/-- `chartHomOfYoneda` is compatible with restriction along a chart morphism. -/
theorem chartHomOfYoneda_comp {V₀ T T' : SmallEtale B S hS X} (g : T' ⟶ T)
    (c : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left) (hc : c ≫ V₀.1.hom = T.1.hom) :
    chartHomOfYoneda (yoneda.map g.hom.left ≫ c) (chartOver_comp g hc) =
      g ≫ chartHomOfYoneda c hc := by
  apply SmallEtale.hom_ext'
  apply yoneda.map_injective
  rw [yoneda_map_chartHomOfYoneda]
  change _ = yoneda.map (g.hom.left ≫ (chartHomOfYoneda c hc).hom.left)
  rw [Functor.map_comp, yoneda_map_chartHomOfYoneda]

/-- The family of the spans of the restrictions of a submodule `M` of the sections over a chart
`V₀`, on the presheaf represented by `V₀`. -/
def chartSpanFamily (V₀ : SmallEtale B S hS X)
    (M : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) :
    ChartSubmoduleFamily F V₀.1.hom :=
  fun _ c hc => chartSpan F (chartHomOfYoneda c hc) M

/-- The family of spans of restrictions of `M` is stable under restriction. -/
theorem chartSpanFamily_isStable (V₀ : SmallEtale B S hS X)
    (M : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) :
    (chartSpanFamily V₀ M).IsStable := fun {T T'} g c hc σ hσ => by
  refine (chartSpan_congr F (chartHomOfYoneda_comp g c hc) M).ge ?_
  exact map_mem_chartSpan F _ g M hσ

/-- The family of spans of restrictions of the span of a finite set is spanned at every affine
chart over `V₀`. -/
theorem isSpannedAt_chartSpanFamily (V₀ : SmallEtale B S hS X)
    (t : Finset (F.val.obj (op V₀))) {T : SmallEtale B S hS X} (hT : IsAffine (chartScheme T))
    (c : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left) (hc : c ≫ V₀.1.hom = T.1.hom) :
    IsSpannedAt F (chartSpanFamily V₀ (Submodule.span _ (t : Set (F.val.obj (op V₀))))) T c hc := by
  refine ⟨hT, chartRes F (chartHomOfYoneda c hc) '' t, t.finite_toSet.image _,
    chartSpan_span F _ _, fun {T₂} h _ => ?_⟩
  change chartSpan F _ _ = _
  rw [chartSpan_congr F (chartHomOfYoneda_comp h c hc), chartSpan_span, Set.image_image]
  congr 1
  exact Set.image_congr fun m _ => (modules_map_map F _ h m).symm

/-- **The chart submodule spanned by a finitely generated submodule `M` of the sections over a
chart `V₀`**, on the presheaf represented by `V₀`: over a chart `T ⟶ V₀` it consists of the
sections which locally lie in the span of the restrictions of `M`. -/
def ChartSubmodule.spanOfChart (hF : IsCartesianOnAffineCharts F) (V₀ : SmallEtale B S hS X)
    (M : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) (hM : M.FG) :
    ChartSubmodule F V₀.1.hom :=
  ChartSubmoduleFamily.toChartSubmodule hF (chartSpanFamily V₀ M) (chartSpanFamily_isStable V₀ M)
    (fun T c hc => by
      obtain ⟨t, rfl⟩ := hM
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (generate_affine_mem (R := ⊤) ((SmallEtale.topology B S hS X).top_mem T))
      rintro T' k ⟨T₁, l, g, ⟨-, hT₁⟩, rfl⟩
      exact ⟨T₁, l, g, isSpannedAt_chartSpanFamily V₀ t hT₁ _ _, rfl⟩)

/-- The span of the restrictions of `M` to a chart over `V₀` lies in `spanOfChart`. -/
theorem ChartSubmodule.chartSpan_le_spanOfChart (hF : IsCartesianOnAffineCharts F)
    (V₀ : SmallEtale B S hS X) (M : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    (hM : M.FG) (T : SmallEtale B S hS X) (c : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left)
    (hc : c ≫ V₀.1.hom = T.1.hom) :
    chartSpan F (chartHomOfYoneda c hc) M ≤ (spanOfChart hF V₀ M hM).obj T c hc :=
  ChartSubmoduleFamily.le_sheafify (chartSpanFamily_isStable V₀ M) T c hc

/-- Over an affine chart, `spanOfChart` is the span of the restrictions of `M`. -/
theorem ChartSubmodule.spanOfChart_obj_of_isAffine (hF : IsCartesianOnAffineCharts F)
    (V₀ : SmallEtale B S hS X) (M : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)))
    (hM : M.FG) {T : SmallEtale B S hS X} (hT : IsAffine (chartScheme T))
    (c : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left) (hc : c ≫ V₀.1.hom = T.1.hom) :
    (spanOfChart hF V₀ M hM).obj T c hc = chartSpan F (chartHomOfYoneda c hc) M := by
  obtain ⟨t, rfl⟩ := id hM
  exact ChartSubmoduleFamily.sheafify_eq_of_isSpannedAt hF (chartSpanFamily_isStable V₀ _)
    (isSpannedAt_chartSpanFamily V₀ t hT c hc)


/-! ### Flat base change of a finite kernel -/

/-- **The kernel of a map to a finite product of quotients commutes with flat base change of
affine charts.**  Let `g m : G m ⟶ V₀` be finitely many affine charts over an affine chart `V₀`,
let `L m` be submodules of the sections over `G m`, and let `N₀` be the submodule of the
sections over `V₀` whose restriction to every `G m` lies in `L m`.  For an affine chart
`r : R ⟶ V₀`, a section over `R` whose restriction to every fibre product `G m ×_{V₀} R` lies
in the span of the restrictions of `L m` lies in the span of the restrictions of `N₀`.

The sections over `R` are the base change of those over `V₀` because `F` is cartesian on affine
charts, the rings of the fibre products are the tensor products, and the restriction
`𝒪(V₀) ⟶ 𝒪(R)` is flat, so it carries the kernel of the map to the product of the quotients
`F(G m) / L m` to the corresponding kernel over `R`. -/
theorem mem_chartSpan_of_forall_pullback (hF : IsCartesianOnAffineCharts F)
    {V₀ R : SmallEtale B S hS X} (hV₀ : IsAffine (chartScheme V₀))
    (hR : IsAffine (chartScheme R)) (r : R ⟶ V₀) {ι : Type*} [Finite ι]
    (G : ι → SmallEtale B S hS X) (g : ∀ m, G m ⟶ V₀) (hG : ∀ m, IsAffine (chartScheme (G m)))
    (L : ∀ m, Submodule (chartRing B S hS X hX (G m)) (F.val.obj (op (G m))))
    {σ : F.val.obj (op R)}
    (hσ : ∀ m, chartRes F (pullback.snd (g m) r) σ ∈
      Submodule.span (chartRing B S hS X hX (pullback (g m) r))
        (chartRes F (pullback.fst (g m) r) '' (L m : Set (F.val.obj (op (G m)))))) :
    σ ∈ chartSpan F r (⨅ m, (L m).comap (chartRes F (g m))) := by
  classical
  have := Fintype.ofFinite ι
  let := chartAlgebra (hF := hX) r
  have hflat : Module.Flat (chartRing B S hS X hX V₀) (chartRing B S hS X hX R) :=
    flat_chartRestrict_of_isAffine r hV₀ hR
  obtain ⟨z, rfl⟩ := (hF V₀ R hV₀ hR r).2 σ
  let algP : ∀ m, Algebra (chartRing B S hS X hX V₀) (chartRing B S hS X hX (G m)) :=
    fun m => chartAlgebra (hF := hX) (g m)
  let modN : ∀ m, Module (chartRing B S hS X hX V₀) (F.val.obj (op (G m))) :=
    fun m => chartSectionsModule F (g m)
  have towN : ∀ m, IsScalarTower (chartRing B S hS X hX V₀) (chartRing B S hS X hX (G m))
      (F.val.obj (op (G m))) := fun m => chartSections_isScalarTower F (g m)
  let ρ : ∀ m, F.val.obj (op V₀) →ₗ[chartRing B S hS X hX V₀] F.val.obj (op (G m)) :=
    fun m => chartRestrictLinear F (g m)
  let ψ : ∀ m, F.val.obj (op V₀) →ₗ[chartRing B S hS X hX V₀]
      F.val.obj (op (G m)) ⧸ (L m).restrictScalars (chartRing B S hS X hX V₀) :=
    fun m => ((L m).restrictScalars (chartRing B S hS X hX V₀)).mkQ.comp (ρ m)
  have hker : LinearMap.ker (LinearMap.pi ψ) ≤ ⨅ m, (L m).comap (chartRes F (g m)) := by
    intro x hx
    refine Submodule.mem_iInf _ |>.2 fun m => ?_
    have hx' : ψ m x = 0 := congrFun (LinearMap.mem_ker.1 hx) m
    exact (Submodule.Quotient.mk_eq_zero
      ((L m).restrictScalars (chartRing B S hS X hX V₀))).1 hx'
  have hψ : ∀ m, AlgebraTensorModule.lTensor (chartRing B S hS X hX R)
      (chartRing B S hS X hX R) (ψ m) z = 0 := by
    intro m
    have hpb := IsPullback.of_hasPullback (g m) r
    set Pi := pullback (g m) r
    set pr₁ : Pi ⟶ G m := pullback.fst (g m) r
    set pr₂ : Pi ⟶ R := pullback.snd (g m) r
    have hPiaff : IsAffine (chartScheme Pi) :=
      SmallEtale.isAffine_of_isPullback_charts hpb hV₀ (hG m) hR
    let : Algebra (chartRing B S hS X hX (G m)) (chartRing B S hS X hX Pi) :=
      chartAlgebra (hF := hX) pr₁
    let : Algebra (chartRing B S hS X hX R) (chartRing B S hS X hX Pi) :=
      chartAlgebra (hF := hX) pr₂
    let : Algebra (chartRing B S hS X hX V₀) (chartRing B S hS X hX Pi) :=
      chartAlgebra (hF := hX) (pr₁ ≫ g m)
    have : IsScalarTower (chartRing B S hS X hX V₀) (chartRing B S hS X hX (G m))
        (chartRing B S hS X hX Pi) :=
      IsScalarTower.of_algebraMap_eq fun x =>
        RingHom.congr_fun (chartRestrict_comp (hF := hX) (g m) pr₁) x
    have : IsScalarTower (chartRing B S hS X hX V₀) (chartRing B S hS X hX R)
        (chartRing B S hS X hX Pi) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        change chartRestrict (hF := hX) (pr₁ ≫ g m) x =
          chartRestrict (hF := hX) pr₂ (chartRestrict (hF := hX) r x)
        rw [show pr₁ ≫ g m = pr₂ ≫ r from hpb.w]
        exact RingHom.congr_fun (chartRestrict_comp (hF := hX) r pr₂) x
    obtain ⟨e, he⟩ := SmallEtale.exists_tensorEquiv_chartRing_of_isPullback (hF := hX) hpb
      hV₀ (hG m) hR
    have : Algebra.IsPushout (chartRing B S hS X hX V₀) (chartRing B S hS X hX R)
        (chartRing B S hS X hX (G m)) (chartRing B S hS X hX Pi) :=
      Algebra.isPushout_of_linearEquiv e he
    let : Module (chartRing B S hS X hX (G m)) (F.val.obj (op Pi)) :=
      chartSectionsModule F pr₁
    have : IsScalarTower (chartRing B S hS X hX (G m)) (chartRing B S hS X hX Pi)
        (F.val.obj (op Pi)) := chartSections_isScalarTower F pr₁
    let τ : F.val.obj (op (G m)) →ₗ[chartRing B S hS X hX (G m)] F.val.obj (op Pi) :=
      chartRestrictLinear F pr₁
    have hτ : Function.Injective (τ.liftBaseChange (chartRing B S hS X hX Pi)) :=
      (hF (G m) Pi (hG m) hPiaff pr₁).1
    have hΘ : ∀ v, τ.liftBaseChange (chartRing B S hS X hX Pi)
        ((Algebra.IsPushout.cancelBaseChange (chartRing B S hS X hX V₀)
          (chartRing B S hS X hX R) (chartRing B S hS X hX (G m)) (chartRing B S hS X hX Pi)
          (F.val.obj (op (G m)))).symm
          (AlgebraTensorModule.lTensor (chartRing B S hS X hX R) (chartRing B S hS X hX R)
            (ρ m) v)) = chartRes F pr₂ (sectionsBaseChange F r v) := by
      intro v
      induction v using TensorProduct.inductionOn with
      | tmul c x =>
        rw [AlgebraTensorModule.lTensor_tmul, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, chartBaseChange_tmul, map_smulₛₗ]
        refine congrArg₂ (· • ·) rfl ?_
        change F.val.map pr₁.op (F.val.map (g m).op x) = F.val.map pr₂.op (F.val.map r.op x)
        exact (modules_map_map F (g m) pr₁ x).trans
          ((modules_map_congr F hpb.w x).trans (modules_map_map F r pr₂ x).symm)
      | add v v' hv hv' => rw [map_add, map_add, map_add, hv, hv', map_add, map_add]
    have hmem : chartRes F pr₂ (sectionsBaseChange F r z) ∈
        Submodule.span (chartRing B S hS X hX Pi) (τ '' (L m)) := hσ m
    have hw := Algebra.IsPushout.mem_range_lTensor_of_liftBaseChange_mem_span τ hτ (L m)
      (AlgebraTensorModule.lTensor (chartRing B S hS X hX R) (chartRing B S hS X hX R)
        (ρ m) z) ((hΘ z).symm ▸ hmem)
    refine lTensor_mkQ_comp_eq_zero (ρ m) _ ((L m).subtype.restrictScalars _) ?_ hw
    ext l
    exact (Submodule.Quotient.mk_eq_zero _).2 l.2
  have hz0 := lTensor_pi_eq_zero ψ hψ
  obtain ⟨v, hv⟩ := Module.Flat.mem_range_lTensor_ker (LinearMap.pi ψ) hz0
  rw [← hv]
  clear hv hz0 hψ
  induction v using TensorProduct.inductionOn with
  | tmul c k =>
    refine mem_of_eq_of_mem (chartBaseChange_tmul F r c _) ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hker k.2, rfl⟩)
  | add v w hv hw =>
    exact mem_of_eq_of_mem ((congrArg _ (map_add _ v w)).trans (map_add _ _ _)) (add_mem hv hw)

/-! ### Locally spanned families are cartesian and finitely generated on affine charts -/

/-- A finite affine refinement of an affine chart of `Y` on whose members a chart submodule is
spanned, jointly faithfully flat over the chart. -/
theorem ChartSubmodule.exists_spanned_cover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : Y ⟶ X} (D : ChartSubmodule F π) {T : SmallEtale B S hS X}
    (hT : IsAffine (chartScheme T)) (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom) :
    ∃ (n : ℕ) (E : Fin n → SmallEtale B S hS X) (φ : ∀ i, E i ⟶ T),
      (∀ i, IsAffine (chartScheme (E i))) ∧
        (∀ i, IsSpannedAt F D.obj (E i) (yoneda.map (φ i).hom.left ≫ a)
          (chartOver_comp (φ i) ha)) ∧
        Sieve.ofArrows E φ ∈ SmallEtale.topology B S hS X T ∧
        (RingHom.pi fun i => chartRestrict (hF := hX) (φ i)).FaithfullyFlat := by
  obtain ⟨n, E, φ, hE, hφ, hcov, hff⟩ := exists_finite_affine_cover_le hT (D.lfg T a ha)
  refine ⟨n, E, φ, hE, fun i => ?_, hcov, hff⟩
  obtain ⟨T₁, l, g₁, hg₁, e⟩ := hφ i
  exact (hg₁.restrict l (hE i)).congr (by rw [← e, yoneda_map_comp_left, Category.assoc]) _

/-- Membership in a chart submodule may be tested on the members of a covering family. -/
theorem ChartSubmodule.mem_of_ofArrows {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : Y ⟶ X} (D : ChartSubmodule F π) {T : SmallEtale B S hS X}
    (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom) {ι : Type*}
    (E : ι → SmallEtale B S hS X) (φ : ∀ i, E i ⟶ T)
    (hcov : Sieve.ofArrows E φ ∈ SmallEtale.topology B S hS X T) {x : F.val.obj (op T)}
    (hx : ∀ i, chartRes F (φ i) x ∈ D.obj (E i) (yoneda.map (φ i).hom.left ≫ a)
      (chartOver_comp (φ i) ha)) : x ∈ D.obj T a ha := by
  refine D.loc T a ha x hcov fun {T'} h hh => ?_
  obtain ⟨i, e, rfl⟩ := (Sieve.mem_ofArrows_iff E φ h).1 hh
  have := D.map e _ _ (hx i)
  rw [modules_map_map] at this
  exact D.obj.mem_congr _ (by rw [yoneda_map_comp_left, Category.assoc]) _ _ this

/-- **A chart submodule is cartesian on affine charts**: over a morphism `g : T' ⟶ T` of affine
charts of `Y`, its sections over `T'` are spanned by the restrictions of its sections over
`T`. -/
theorem ChartSubmodule.obj_eq_span (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (D : ChartSubmodule F π)
    {T T' : SmallEtale B S hS X} (hT : IsAffine (chartScheme T))
    (hT' : IsAffine (chartScheme T')) (g : T' ⟶ T) (a : yoneda.obj T.1.left ⟶ Y)
    (ha : a ≫ π = T.1.hom) :
    D.obj T' (yoneda.map g.hom.left ≫ a) (chartOver_comp g ha) =
      Submodule.span (chartRing B S hS X hX T')
        (chartRes F g '' (D.obj T a ha : Set (F.val.obj (op T)))) := by
  refine le_antisymm (fun σ hσ => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨n, E, φ, hE, hsp, hcov, -⟩ := D.exists_spanned_cover hT a ha
    have hσ' := mem_chartSpan_of_forall_pullback hF hT hT' g E φ hE
      (fun i => D.obj (E i) (yoneda.map (φ i).hom.left ≫ a) (chartOver_comp (φ i) ha))
      (σ := σ) fun i => by
        obtain ⟨-, t, ht, h0, hspan⟩ := hsp i
        have hP : IsAffine (chartScheme (pullback (φ i) g)) :=
          SmallEtale.isAffine_of_isPullback_charts (IsPullback.of_hasPullback (φ i) g) hT
            (hE i) hT'
        have h1 := D.map (pullback.snd (φ i) g) _ _ hσ
        have h2 := hspan (pullback.fst (φ i) g) hP
        have h3 : chartRes F (pullback.snd (φ i) g) σ ∈
            Submodule.span (chartRing B S hS X hX (pullback (φ i) g))
              (chartRes F (pullback.fst (φ i) g) '' t) := by
          rw [← h2]
          refine D.obj.mem_congr _ ?_ _ _ h1
          rw [← Category.assoc, ← yoneda_map_comp_left, ← Category.assoc, ← yoneda_map_comp_left,
            pullback.condition]
        refine Submodule.span_mono (Set.image_mono ?_) h3
        rw [h0]
        exact Submodule.subset_span
    refine chartSpan_mono F g ?_ hσ'
    intro x hx
    refine D.mem_of_ofArrows a ha E φ hcov fun i => ?_
    exact (Submodule.mem_iInf _).1 hx i
  · rintro _ ⟨x, hx, rfl⟩
    exact D.map g a ha hx

/-- **A chart submodule is finitely generated over affine charts.** -/
theorem ChartSubmodule.fg_obj (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (D : ChartSubmodule F π)
    {T : SmallEtale B S hS X} (hT : IsAffine (chartScheme T)) (a : yoneda.obj T.1.left ⟶ Y)
    (ha : a ≫ π = T.1.hom) : (D.obj T a ha).FG := by
  classical
  obtain ⟨n, E, φ, hE, hsp, hcov, hff⟩ := D.exists_spanned_cover hT a ha
  choose t ht h0 hspan using fun i => (hsp i).2
  have hgen : ∀ i (y : t i), ∃ Sg : Finset (F.val.obj (op T)),
      (↑Sg ⊆ (D.obj T a ha : Set (F.val.obj (op T)))) ∧
        (y : F.val.obj (op (E i))) ∈ Submodule.span (chartRing B S hS X hX (E i))
          (chartRes F (φ i) '' (Sg : Set (F.val.obj (op T)))) := by
    intro i y
    have hy : (y : F.val.obj (op (E i))) ∈ D.obj (E i) (yoneda.map (φ i).hom.left ≫ a)
        (chartOver_comp (φ i) ha) := by
      rw [h0 i]
      exact Submodule.subset_span y.2
    rw [D.obj_eq_span hF hT (hE i) (φ i) a ha] at hy
    obtain ⟨S0, hS0, hyS0⟩ := Submodule.mem_span_finite_of_mem_span hy
    choose x hx hxe using fun z : {w // w ∈ S0} => hS0 (Finset.mem_coe.2 z.2)
    refine ⟨Finset.univ.image x, ?_, ?_⟩
    · intro w hw
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
      exact hx z
    · refine Submodule.span_mono ?_ hyS0
      intro w hw
      exact ⟨x ⟨w, Finset.mem_coe.1 hw⟩, by simp, hxe ⟨w, Finset.mem_coe.1 hw⟩⟩
  choose Sg hS_ hyS_ using hgen
  have hfin : ∀ i, Finite (t i) := fun i => (ht i).to_subtype
  have : ∀ i, Fintype (t i) := fun i => Fintype.ofFinite _
  let Sall : Finset (F.val.obj (op T)) := Finset.univ.biUnion fun i => Finset.univ.biUnion (Sg i)
  have hSall : (↑Sall : Set (F.val.obj (op T))) ⊆ D.obj T a ha := by
    intro w hw
    simp only [Sall, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.mem_coe] at hw
    obtain ⟨i, y, hy⟩ := hw
    exact hS_ i y hy
  refine ⟨Sall, le_antisymm (Submodule.span_le.2 hSall) fun x hx => ?_⟩
  have hmem := mem_span_of_forall_restrict_mem_span F hF hT φ hE hff
    (fun w : (Sall : Set (F.val.obj (op T))) => (w : F.val.obj (op T))) (x := x) fun i => by
      have hxi := D.map (φ i) a ha hx
      rw [h0 i] at hxi
      refine Submodule.span_le.2 ?_ hxi
      intro y hy
      refine Submodule.span_mono ?_ (hyS_ i ⟨y, hy⟩)
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨⟨w, ?_⟩, rfl⟩
      simp only [Sall, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Set.mem_iUnion, Finset.mem_coe]
      exact ⟨i, ⟨y, hy⟩, hw⟩
  rwa [Subtype.range_coe] at hmem


/-! ### On the base: a finite type quasi-coherent submodule of `F` -/

/-- A submodule of `F` whose sections over an affine chart are spanned by the restrictions of its
sections over any larger affine chart is cartesian on affine charts, `F` being so. -/
theorem isCartesianOnAffineCharts_toSheafOfModules_of_le_span
    (hF : IsCartesianOnAffineCharts F) (N : F.Submodule)
    (hN : ∀ {T T' : SmallEtale B S hS X}, IsAffine (chartScheme T) →
      IsAffine (chartScheme T') → ∀ g : T' ⟶ T,
        N.obj (op T') ≤ Submodule.span (chartRing B S hS X hX T')
          (chartRes F g '' (N.obj (op T) : Set (F.val.obj (op T))))) :
    IsCartesianOnAffineCharts N.toSheafOfModules := by
  intro W W' hW hW' f
  let := chartAlgebra (hF := hX) f
  have hflat : Module.Flat (chartRing B S hS X hX W) (chartRing B S hS X hX W') :=
    flat_chartRestrict_of_isAffine f hW hW'
  set ιW := (N.obj (op W)).subtype with hιW
  set ιW' := (N.obj (op W')).subtype with hιW'
  have hcomm : ∀ u, ιW' (sectionsBaseChange N.toSheafOfModules f u) =
      sectionsBaseChange F f (AlgebraTensorModule.lTensor (chartRing B S hS X hX W')
        (chartRing B S hS X hX W') ιW u) := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul r k => rfl
    | add u v hu hv =>
      exact ((congrArg ιW' (map_add _ u v)).trans (map_add _ _ _)).trans
        ((congrArg₂ (· + ·) hu hv).trans
          (((congrArg (sectionsBaseChange F f) (map_add _ u v)).trans (map_add _ _ _)).symm))
  refine ⟨fun u v huv => ?_, fun y => ?_⟩
  · have h := congrArg ιW' huv
    rw [hcomm, hcomm] at h
    have hinj : Function.Injective (AlgebraTensorModule.lTensor (chartRing B S hS X hX W')
        (chartRing B S hS X hX W') ιW) := by
      rw [AlgebraTensorModule.coe_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact hinj ((hF W W' hW hW' f).1 h)
  · obtain ⟨y, hy⟩ := y
    have hle : Submodule.span (chartRing B S hS X hX W')
        (chartRes F f '' (N.obj (op W) : Set (F.val.obj (op W)))) ≤
          LinearMap.range ((ιW'.restrictScalars (chartRing B S hS X hX W')).comp
            (sectionsBaseChange N.toSheafOfModules f)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨TensorProduct.tmul _ (1 : chartRing B S hS X hX W') ⟨k, hk⟩, ?_⟩
      change ιW' (sectionsBaseChange N.toSheafOfModules f _) = _
      rw [hcomm]
      exact chartBaseChange_one_tmul F f k
    obtain ⟨u, hu⟩ := hle (hN hW hW' f hy)
    exact ⟨u, Subtype.ext hu⟩

variable (F) in
/-- The submodule of `F` given by a chart submodule over the identity of `X`. -/
def ChartSubmodule.toSubmodule (D : ChartSubmodule F (𝟙 X)) : F.Submodule where
  obj U := D.obj U.unop U.unop.1.hom (Category.comp_id _)
  map {U V} f σ hσ := by
    have := D.map f.unop _ _ hσ
    exact D.obj.mem_congr _ (CostructuredArrow.w f.unop.hom) _ _ this
  isSheaf U σ hσ := D.loc U.unop _ _ σ hσ fun {T'} g hg => by
    have hg' : chartRes F g σ ∈ D.obj T' T'.1.hom (Category.comp_id _) := hg
    have hw : T'.1.hom = yoneda.map g.hom.left ≫ U.unop.1.hom :=
      (CostructuredArrow.w g.hom).symm
    exact D.obj.mem_congr T' hw _ _ hg'

/-- The sections of `ChartSubmodule.toSubmodule` over a chart `T` are those of the chart
submodule at `T`. -/
theorem ChartSubmodule.mem_toSubmodule (D : ChartSubmodule F (𝟙 X)) (T : SmallEtale B S hS X)
    (σ : F.val.obj (op T)) :
    σ ∈ (D.toSubmodule F).obj (op T) ↔ σ ∈ D.obj T T.1.hom (Category.comp_id _) :=
  Iff.rfl

/-- The submodule of `F` given by a chart submodule over the identity is cartesian on affine
charts. -/
theorem ChartSubmodule.isCartesianOnAffineCharts_toSubmodule (hF : IsCartesianOnAffineCharts F)
    (D : ChartSubmodule F (𝟙 X)) :
    IsCartesianOnAffineCharts (D.toSubmodule F).toSheafOfModules := by
  refine isCartesianOnAffineCharts_toSheafOfModules_of_le_span hF _ fun {T T'} hT hT' g => ?_
  have h := D.obj_eq_span hF hT hT' g T.1.hom (Category.comp_id _)
  have hw : T'.1.hom = yoneda.map g.hom.left ≫ T.1.hom := (CostructuredArrow.w g.hom).symm
  exact le_of_eq ((D.obj.congr T' hw _ _).trans h)

/-- The submodule of `F` given by a chart submodule over the identity is of finite type on the
small étale site. -/
theorem ChartSubmodule.isFiniteTypeOnSite_toSubmodule (hF : IsCartesianOnAffineCharts F)
    (D : ChartSubmodule F (𝟙 X)) :
    SheafOfModules.IsFiniteTypeOnSite (D.toSubmodule F).toSheafOfModules :=
  isFiniteTypeOnSite_of_forall_affine_moduleFinite B S hS X hX _
    (D.isCartesianOnAffineCharts_toSubmodule hF) fun T hT =>
      Module.Finite.iff_fg.2 (D.fg_obj hF hT T.1.hom (Category.comp_id _))

end AlgebraicGeometry.Space

end
