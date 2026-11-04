module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjGradedIdealOfCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ChartClosedSubschemeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointReadingAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointReadingRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointReadingTwistKer

/-!
# The graded ideal of a closed subspace of a relative Proj, read on the étale scheme points

In Situation 0849 let `i : Z ⟶ Proj_X(𝒜)` be a closed immersion, with `π : Proj_X(𝒜) ⟶ X`
quasi-compact.  At every étale scheme point `f : T ⟶ X` the closed subscheme `Z ×_X T` of
`Proj_T(f^*𝒜)` has the graded ideal `K_{T,f} ⊆ f^*𝒜` of Stacks 0801.  This file forms, in every
degree `n`, the presheaf submodule `P_n ⊆ 𝒜_n` of the sections whose readings on every affine
chart `W ⟶ T ⟶ X` mapping to their chart lie in `K_{T,f}`, and shows that the closures of the
`P_n` form a quasi-coherent graded ideal `ℐ ⊆ 𝒜` whose restriction to every étale scheme point is
`K_{T,f}`: this is the ideal used in the proof of Stacks 085M.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.closedSubspaceReadingSubmodule`: the presheaf
  submodule `P_n ⊆ 𝒜_n`.
* `AlgebraicGeometry.Space.RelativeProjSituation.closedSubspaceGradedIdeal`: the quasi-coherent
  graded ideal `ℐ` with pieces the closures of the `P_n`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.closedSubspaceReadingSubmodule_mul_mem_left`,
  `closedSubspaceReadingSubmodule_mul_mem_right`: the family `P` is closed under multiplication
  by homogeneous sections of `𝒜` on either side.
* `AlgebraicGeometry.Space.RelativeProjSituation.closedSubspaceReadingSubmodule_le_span_restrict`:
  `P` is cartesian on affine charts.
* `AlgebraicGeometry.Space.RelativeProjSituation`
  `.mem_twistKerGradedIdeal_iff_closedSubspaceGradedIdeal`:
  at every étale scheme point `f`, a section of `f^*𝒜` lies in `K_{T,f}` exactly when the
  restriction of `𝒜 ⟶ 𝒜/ℐ` kills it.

## Implementation notes

Two facts carry the proof.  The readings of a section of `K_{T,f}` over any open `W` lie in `P_n`
(`isClosedSubspaceReading_of_mem`): a chart morphism `φ : (W' ⟶ T' ⟶ X) ⟶ (W ⟶ T ⟶ X)` is a
morphism of test objects from the chart of `W'` to `T`, along which the ideal restricts into the
ideal (`mem_pointTwistKer_restrict`), and the chart of `W'` is the open `W'` of `T'`, along whose
inclusion the restriction of the ideal is onto it (flat base change,
`pointTwistKer_le_span_restrict`, with the restriction of functions onto).  And `P_n` is
cartesian on affine charts: an affine chart `V` is a scheme point at which the chart of `⊤` is
`V` itself, and along a morphism `V ⟶ U` of affine charts the ideal at `V` is spanned by the
restrictions of the ideal at `U` (flat base change again).  Both read restrictions of
sections on charts through `etalePointReading_pointTwistKerRestrict`.  Morphisms into the chart
of a Zariski open are detected after composing into the scheme (`selfOpens_hom_ext`).

The restriction maps of `𝒜` are used through the private function `pmap`, typed in the sections
of `𝒜`, and the opens of a test object are always spelled in the site of the situation: equations
between sections typed through the restriction of scalars along two different chart morphisms, or
opens spelled through the shrunk situation, make the elaborator unfold the structure sheaf.

## References

* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {s : RelativeProjSituation.{u, u}}
  (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- The defining condition of `closedSubspaceReadingSubmodule`: a section `a` of `𝒜_n` over a
chart `V` such that, for every étale scheme point `f : T ⟶ X`, every affine open `W` of `T` and
every morphism `φ` from the chart `W ⟶ T ⟶ X` to `V`, the section of `f^*𝒜_n` over `W` that reads
as `φ^*a` lies in the graded ideal of Stacks 0801 of `Z ×_X T`. -/
def IsClosedSubspaceReading (n : ℤ) (V : SmallEtale s.site s.base s.containsBase s.space.1)
    (a : (s.algebra.piece n).val.obj (op V)) : Prop :=
  ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens), IsAffineOpen W →
    ∀ φ : s.etalePointChart f hf W ⟶ V,
      haveI := quasiCompact_relativeProj_toBase hπ T f
      (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op a) ∈
        ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W)

private theorem etalePointReading_symm_add {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (x y : (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W))) :
    (s.etalePointReading f hf n W).symm (x + y) =
      (s.etalePointReading f hf n W).symm x + (s.etalePointReading f hf n W).symm y := by
  apply (s.etalePointReading f hf n W).injective
  rw [s.etalePointReading_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem etalePointReading_symm_smul {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (c : Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T, W))
    (x : (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W))) :
    (s.etalePointReading f hf n W).symm (etalePointChartRingHom f hf W c • x) =
      c • (s.etalePointReading f hf n W).symm x := by
  apply (s.etalePointReading f hf n W).injective
  rw [s.etalePointReading_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem etalePointReading_symm_map_add_mem
    {T : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (N : Submodule Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T, W)
      Γ((s.relativeProjPoints.algebra T f).piece n, W))
    {V : SmallEtale s.site s.base s.containsBase s.space.1} (φ : s.etalePointChart f hf W ⟶ V)
    (a b : (s.algebra.piece n).val.obj (op V))
    (ha : (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op a) ∈ N)
    (hb : (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op b) ∈ N) :
    (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op (a + b)) ∈ N := by
  have e1 : (s.algebra.piece n).val.map φ.op (a + b) =
      ((s.algebra.piece n).val.map φ.op a + (s.algebra.piece n).val.map φ.op b :
        (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W))) := map_add _ a b
  have e : (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op (a + b)) =
      (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op a) +
        (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op b) :=
    (congrArg (s.etalePointReading f hf n W).symm e1).trans
      (etalePointReading_symm_add f hf n W _ _)
  rw [e]
  exact N.add_mem ha hb

private theorem etalePointReading_symm_map_zero_mem
    {T : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (N : Submodule Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T, W)
      Γ((s.relativeProjPoints.algebra T f).piece n, W))
    {V : SmallEtale s.site s.base s.containsBase s.space.1} (φ : s.etalePointChart f hf W ⟶ V) :
    (s.etalePointReading f hf n W).symm ((s.algebra.piece n).val.map φ.op 0) ∈ N := by
  have e1 : (s.algebra.piece n).val.map φ.op 0 =
      (0 : (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W))) := map_zero _
  have e2 : (s.etalePointReading f hf n W).symm
      (0 : (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W))) = 0 := by
    apply (s.etalePointReading f hf n W).injective
    rw [Equiv.apply_symm_apply, s.etalePointReading_zero]
  rw [congrArg (s.etalePointReading f hf n W).symm e1, e2]
  exact N.zero_mem

private theorem etalePointReading_symm_smul_mem {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (N : Submodule Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T, W)
      Γ((s.relativeProjPoints.algebra T f).piece n, W))
    (r : (structureRingSheaf s.site s.base s.containsBase s.space).obj.obj
      (op (s.etalePointChart f hf W)))
    (x : (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W)))
    (hx : (s.etalePointReading f hf n W).symm x ∈ N) :
    (s.etalePointReading f hf n W).symm (r • x) ∈ N := by
  obtain ⟨c, rfl⟩ := (bijective_etalePointChartRingHom f hf W).2 r
  rw [etalePointReading_symm_smul]
  exact N.smul_mem c hx

/-- The defining condition of `closedSubspaceReadingSubmodule` holds for `0`. -/
theorem isClosedSubspaceReading_zero (n : ℤ)
    (V : SmallEtale s.site s.base s.containsBase s.space.1) :
    IsClosedSubspaceReading hπ i hi n V 0 :=
  fun _ f hf W _ φ => etalePointReading_symm_map_zero_mem f hf n W _ φ

/-- The defining condition of `closedSubspaceReadingSubmodule` is stable under addition. -/
theorem IsClosedSubspaceReading.add {n : ℤ} {V : SmallEtale s.site s.base s.containsBase s.space.1}
    {a b : (s.algebra.piece n).val.obj (op V)} (ha : IsClosedSubspaceReading hπ i hi n V a)
    (hb : IsClosedSubspaceReading hπ i hi n V b) : IsClosedSubspaceReading hπ i hi n V (a + b) :=
  fun T f hf W hW φ => etalePointReading_symm_map_add_mem f hf n W _ φ a b (ha T f hf W hW φ)
    (hb T f hf W hW φ)

/-- The defining condition of `closedSubspaceReadingSubmodule` is stable under multiplication by
the functions on the chart. -/
theorem IsClosedSubspaceReading.smul {n : ℤ}
    {V : SmallEtale s.site s.base s.containsBase s.space.1}
    (r : (structureRingSheaf s.site s.base s.containsBase s.space).obj.obj (op V))
    {a : (s.algebra.piece n).val.obj (op V)} (ha : IsClosedSubspaceReading hπ i hi n V a) :
    IsClosedSubspaceReading hπ i hi n V (r • a) := by
  intro T f hf W hW φ
  rw [PresheafOfModules.map_smul]
  exact etalePointReading_symm_smul_mem f hf n W _ _ _ (ha T f hf W hW φ)

/-- The defining condition of `closedSubspaceReadingSubmodule` is stable under restriction. -/
theorem IsClosedSubspaceReading.map {n : ℤ}
    {V V' : SmallEtale s.site s.base s.containsBase s.space.1} (g : V' ⟶ V)
    {a : (s.algebra.piece n).val.obj (op V)} (ha : IsClosedSubspaceReading hπ i hi n V a) :
    IsClosedSubspaceReading hπ i hi n V' ((s.algebra.piece n).val.map g.op a) := by
  intro T f hf W hW φ
  have e : (s.algebra.piece n).val.map (φ ≫ g).op a =
      (s.algebra.piece n).val.map φ.op ((s.algebra.piece n).val.map g.op a) := by
    rw [op_comp, PresheafOfModules.map_comp_apply]
  exact e ▸ ha T f hf W hW (φ ≫ g)

/-- **The presheaf submodule `P_n ⊆ 𝒜_n`** of the sections whose readings at every étale scheme
point, on every affine chart mapping to their chart, lie in the graded ideal of Stacks 0801 of the
base change of `Z`. -/
def closedSubspaceReadingSubmodule (n : ℤ) : (s.algebra.piece n).val.Submodule where
  obj V :=
    { carrier := {a | IsClosedSubspaceReading hπ i hi n V.unop a}
      zero_mem' := isClosedSubspaceReading_zero hπ i hi n V.unop
      add_mem' := fun ha hb => ha.add hπ i hi hb
      smul_mem' := fun r _ ha => IsClosedSubspaceReading.smul hπ i hi r ha }
  map g _ ha := IsClosedSubspaceReading.map hπ i hi g.unop ha

/-- Membership in `closedSubspaceReadingSubmodule` is the defining condition. -/
theorem mem_closedSubspaceReadingSubmodule_iff (n : ℤ)
    (V : SmallEtale s.site s.base s.containsBase s.space.1)
    (a : (s.algebra.piece n).val.obj (op V)) :
    a ∈ (closedSubspaceReadingSubmodule hπ i hi n).obj (op V) ↔
      IsClosedSubspaceReading hπ i hi n V a :=
  Iff.rfl

private theorem etalePointReading_symm_mul {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (p q : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (x : (s.algebra.piece p).val.obj (op (s.etalePointChart f hf W)))
    (y : (s.algebra.piece q).val.obj (op (s.etalePointChart f hf W))) :
    (s.etalePointReading f hf (p + q) W).symm
        ((s.algebra.mul p q).app (op (s.etalePointChart f hf W)) x y) =
      ((s.relativeProjPoints.algebra T f).mul p q).app W ((s.etalePointReading f hf p W).symm x)
        ((s.etalePointReading f hf q W).symm y) := by
  apply (s.etalePointReading f hf (p + q) W).injective
  rw [s.etalePointReading_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem etalePointReading_symm_map_mul {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (p q : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    {V : SmallEtale s.site s.base s.containsBase s.space.1} (φ : s.etalePointChart f hf W ⟶ V)
    (x : (s.algebra.piece p).val.obj (op V)) (y : (s.algebra.piece q).val.obj (op V)) :
    (s.etalePointReading f hf (p + q) W).symm
        ((s.algebra.piece (p + q)).val.map φ.op ((s.algebra.mul p q).app (op V) x y)) =
      ((s.relativeProjPoints.algebra T f).mul p q).app W
        ((s.etalePointReading f hf p W).symm ((s.algebra.piece p).val.map φ.op x))
        ((s.etalePointReading f hf q W).symm ((s.algebra.piece q).val.map φ.op y)) := by
  rw [(s.algebra.mul p q).naturality φ.op x y]
  exact etalePointReading_symm_mul f hf p q W _ _

/-- The membership in a graded ideal of a homogeneous section, transported along an equation of
degrees and a heterogeneous equality of sections. -/
private theorem mem_piece_of_heq {S : Scheme.{u}}
    {A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra S}
    (K : Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedIdeal A)
    {U : S.Opens} {m m' : ℤ} (h : m = m') {x : Γ(A.piece m, U)} {y : Γ(A.piece m', U)}
    (hxy : HEq x y) (hy : y ∈ (K.piece m').toSubmodule.obj (op U)) :
    x ∈ (K.piece m).toSubmodule.obj (op U) := by
  subst h
  exact eq_of_heq hxy ▸ hy

/-- **`closedSubspaceReadingSubmodule` is closed under multiplication on the right.** -/
theorem closedSubspaceReadingSubmodule_mul_mem_right (p q : ℤ)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    {x : (s.algebra.piece p).val.obj V} (b : (s.algebra.piece q).val.obj V)
    (hx : x ∈ (closedSubspaceReadingSubmodule hπ i hi p).obj V) :
    (s.algebra.mul p q).app V x b ∈ (closedSubspaceReadingSubmodule hπ i hi (p + q)).obj V := by
  obtain ⟨V⟩ := V
  intro T f hf W hW φ
  have := quasiCompact_relativeProj_toBase hπ T f
  rw [etalePointReading_symm_map_mul]
  exact (twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
    (chartClosedSubscheme i hi T f)).mul_mem p q W (hx T f hf W hW φ) _

/-- **`closedSubspaceReadingSubmodule` is closed under multiplication on the left.** -/
theorem closedSubspaceReadingSubmodule_mul_mem_left (p q : ℤ)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (a : (s.algebra.piece p).val.obj V) {x : (s.algebra.piece q).val.obj V}
    (hx : x ∈ (closedSubspaceReadingSubmodule hπ i hi q).obj V) :
    (s.algebra.mul p q).app V a x ∈ (closedSubspaceReadingSubmodule hπ i hi (p + q)).obj V := by
  obtain ⟨V⟩ := V
  intro T f hf W hW φ
  have := quasiCompact_relativeProj_toBase hπ T f
  rw [etalePointReading_symm_map_mul]
  exact mem_piece_of_heq _ (add_comm p q)
    ((s.relativeProjPoints.algebra T f).mul_comm p q W _ _)
    ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
      (chartClosedSubscheme i hi T f)).mul_mem q p W (hx T f hf W hW φ) _)

end AlgebraicGeometry.Space.RelativeProjSituation

namespace AlgebraicGeometry.Space

section ChartHoms

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of test objects from the chart of a Zariski open `W` of `T` to `T`. -/
private noncomputable def selfOpensι (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    ((selfOpensFunctor B S hS T).obj W).1.left ⟶ T :=
  yoneda.preimage ((selfOpensFunctor B S hS T).obj W).1.hom

private theorem yoneda_map_selfOpensι (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    yoneda.map (selfOpensι T W) = ((selfOpensFunctor B S hS T).obj W).1.hom :=
  yoneda.map_preimage _

private theorem openSub_hom_ext (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) {Y : BigFppfOver B S hS}
    (g₁ g₂ : Y ⟶ openSub T W)
    (h : yoneda.map g₁ ≫ (yoneda.map (openSubHom T W) ≫ 𝟙 _) =
      yoneda.map g₂ ≫ (yoneda.map (openSubHom T W) ≫ 𝟙 _)) : g₁ = g₂ := by
  rw [Category.comp_id, ← Functor.map_comp, ← Functor.map_comp] at h
  have h2 := congrArg (BigFppfOver.toScheme B S hS).map (yoneda.map_injective h)
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_openSubHom] at h2
  exact (BigFppfOver.toScheme B S hS).map_injective ((cancel_mono W.ι).1 h2)

/-- Morphisms of test objects into the chart of a Zariski open are determined by their
composites with the structure morphism of the chart. -/
private theorem selfOpens_hom_ext (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) {Y : BigFppfOver B S hS}
    (g₁ g₂ : Y ⟶ ((selfOpensFunctor B S hS T).obj W).1.left)
    (h : yoneda.map g₁ ≫ ((selfOpensFunctor B S hS T).obj W).1.hom =
      yoneda.map g₂ ≫ ((selfOpensFunctor B S hS T).obj W).1.hom) : g₁ = g₂ := by
  have hO := selfOpensFunctor_obj B S hS T W
  generalize (selfOpensFunctor B S hS T).obj W = O at hO g₁ g₂ h
  subst hO
  exact openSub_hom_ext T W g₁ g₂ h

private theorem openSub_top_le_preimage (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) {Y : BigFppfOver B S hS} (k : Y ⟶ T)
    (g : Y ⟶ openSub T W)
    (h : yoneda.map k = yoneda.map g ≫ (yoneda.map (openSubHom T W) ≫ 𝟙 _)) :
    ⊤ ≤ (BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ W := by
  rw [Category.comp_id, ← Functor.map_comp] at h
  rw [yoneda.map_injective h, Functor.map_comp, toScheme_map_openSubHom]
  intro x _
  exact ((BigFppfOver.toScheme B S hS).map g x).2

/-- The preimage of `W` along a morphism factoring through the chart of `W` is everything. -/
private theorem selfOpens_top_le_preimage (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) {Y : BigFppfOver B S hS} (k : Y ⟶ T)
    (g : Y ⟶ ((selfOpensFunctor B S hS T).obj W).1.left)
    (h : yoneda.map k = yoneda.map g ≫ ((selfOpensFunctor B S hS T).obj W).1.hom) :
    ⊤ ≤ (BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ W := by
  have hO := selfOpensFunctor_obj B S hS T W
  generalize (selfOpensFunctor B S hS T).obj W = O at hO g h
  subst hO
  exact openSub_top_le_preimage T W k g h

private theorem isIso_openSub_top (U : BigFppfOver B S hS) (g : openSub U ⊤ ⟶ U)
    (hg : yoneda.map g = yoneda.map (openSubHom U ⊤) ≫ 𝟙 _) : IsIso g := by
  rw [Category.comp_id] at hg
  rw [yoneda.map_injective hg]
  have : IsIso ((BigFppfOver.toScheme B S hS).map (openSubHom U ⊤)) := by
    rw [toScheme_map_openSubHom]
    exact ⟨((BigFppfOver.toScheme B S hS).obj U).topIso.inv,
      ((BigFppfOver.toScheme B S hS).obj U).ι_toIso_inv,
      ((BigFppfOver.toScheme B S hS).obj U).toIso_inv_ι⟩
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

private theorem isIso_openChart_top (U : BigFppfOver B S hS) (O : SmallEtale B S hS (yoneda.obj U))
    (hO : O = (openChartFunctor B S hS (yoneda.obj U) (idEtaleChart B S hS U)).obj ⊤)
    (g : O.1.left ⟶ U) (hg : yoneda.map g = O.1.hom) : IsIso g := by
  subst hO
  exact isIso_openSub_top U g hg

/-- The chart of the open `⊤` of `U` is the identity chart: its test-object morphism to `U` is
an isomorphism. -/
private theorem isIso_selfOpensι_top (U : BigFppfOver B S hS) : IsIso (selfOpensι U ⊤) :=
  isIso_openChart_top U _ (selfOpensFunctor_obj B S hS U ⊤) _ (yoneda_map_selfOpensι U ⊤)

private theorem surjective_appLE_openSub (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) (g : openSub T W ⟶ T)
    (hg : yoneda.map g = yoneda.map (openSubHom T W) ≫ 𝟙 _)
    (h : ⊤ ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ W) :
    Function.Surjective (((BigFppfOver.toScheme B S hS).map g).appLE W ⊤ h).hom := by
  rw [Category.comp_id] at hg
  obtain rfl := yoneda.map_injective hg
  have e := toScheme_map_openSubHom B S hS T W
  generalize (BigFppfOver.toScheme B S hS).map (openSubHom T W) = φ at h e ⊢
  subst e
  exact (ConcreteCategory.bijective_of_isIso (W.ι.appLE W ⊤ W.ι_preimage_self.ge)).2

private theorem surjective_appLE_openChart (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) (O : SmallEtale B S hS (yoneda.obj T))
    (hO : O = (openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj W)
    (g : O.1.left ⟶ T) (hg : yoneda.map g = O.1.hom)
    (h : ⊤ ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ W) :
    Function.Surjective (((BigFppfOver.toScheme B S hS).map g).appLE W ⊤ h).hom := by
  subst hO
  exact surjective_appLE_openSub T W g hg h

/-- The restriction of functions from `W` to the whole chart of `W` is onto. -/
private theorem surjective_appLE_selfOpensι (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (h : ⊤ ≤ (BigFppfOver.toScheme B S hS).map (selfOpensι T W) ⁻¹ᵁ W) :
    Function.Surjective (((BigFppfOver.toScheme B S hS).map (selfOpensι T W)).appLE W ⊤ h).hom :=
  surjective_appLE_openChart T W _ (selfOpensFunctor_obj B S hS T W) _ (yoneda_map_selfOpensι T W) h

end ChartHoms

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

section ChartRestrict

variable (s : RelativeProjSituation.{u, u}) {T T' : BigFppfOver s.site s.base s.containsBase}
  (k : T' ⟶ T) (hk : IsEtale s.site s.base s.containsBase (representedSpaceMap s.site s.base
    s.containsBase k).hom)
  (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
  (hf' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)

/-- The test-object morphism of `etalePointChartRestrict`, followed into `T`, is the inclusion of
`W₁` followed by `k`. -/
private theorem yoneda_map_etalePointChartRestrict_left
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) :
    yoneda.map (s.etalePointChartRestrict k hk f hf hf' hW).hom.left ≫
        ((selfOpensFunctor s.site s.base s.containsBase T).obj W).1.hom =
      ((selfOpensFunctor s.site s.base s.containsBase T').obj W₁).1.hom ≫ yoneda.map k := by
  have h1 := CostructuredArrow.w (selfOpensPreimageChartHom k hk W).hom
  have h2 := CostructuredArrow.w
    ((selfOpensFunctor s.site s.base s.containsBase T').map (homOfLE hW)).hom
  exact ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans (Category.assoc _ _ _)).trans
    ((congrArg (yoneda.map _ ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yoneda.map k) h2)))

/-- The compatibility of `pointTwistKerRestrict` with the readings on the charts: reading the
restriction along `k` of a section is restricting its reading along the chart morphism
`etalePointChartRestrict`. -/
private def EtalePointBridge : Prop :=
  ∀ {T T' : BigFppfOver s.site s.base s.containsBase} (k : T' ⟶ T)
    (hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase k).hom)
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
    s.etalePointReading (yoneda.map k ≫ f) hf' n W₁ (pointTwistKerRestrict k f n hW a) =
      (s.algebra.piece n).val.map (s.etalePointChartRestrict k hk f hf hf' hW).op
        (s.etalePointReading f hf n W a)

end ChartRestrict

section Kernel

variable {s : RelativeProjSituation.{u, u}}
  (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- The sections over `W` of the graded ideal of Stacks 0801 of `Z ×_X T ⊆ Proj_T(f^*𝒜)`. -/
private abbrev pointKer (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :=
  haveI := quasiCompact_relativeProj_toBase hπ T f
  ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
    (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W)

/-- Membership in the graded ideal at a scheme point, transported along an equation of points
through readings on charts mapping to a common chart by the same test-object morphism. -/
private theorem mem_pointKer_of_eq {T₁ : BigFppfOver s.site s.base s.containsBase}
    (g g' : yoneda.obj T₁ ⟶ s.space.1) (e : g = g')
    (hg : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) g).hom)
    (hg' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) g').hom) (n : ℤ)
    (W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₁).Opens)
    {V : SmallEtale s.site s.base s.containsBase s.space.1} (c : (s.algebra.piece n).val.obj (op V))
    (ψ : s.etalePointChart g hg W₁ ⟶ V) (ψ' : s.etalePointChart g' hg' W₁ ⟶ V)
    (hψ : ψ.hom.left = ψ'.hom.left) (y : Γ((s.relativeProjPoints.algebra T₁ g).piece n, W₁))
    (y' : Γ((s.relativeProjPoints.algebra T₁ g').piece n, W₁))
    (hy : s.etalePointReading g hg n W₁ y = (s.algebra.piece n).val.map ψ.op c)
    (hy' : s.etalePointReading g' hg' n W₁ y' = (s.algebra.piece n).val.map ψ'.op c)
    (hK : y ∈ pointKer hπ i hi T₁ g n W₁) : y' ∈ pointKer hπ i hi T₁ g' n W₁ := by
  subst e
  obtain rfl : hg = hg' := rfl
  obtain rfl : ψ = ψ' := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hψ)
  obtain rfl : y = y' := (s.etalePointReading g hg n W₁).injective (hy.trans hy'.symm)
  exact hK

/-- Restriction of sections of a presheaf of modules along an isomorphism is injective. -/
private theorem injective_map_of_isIso {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {U V : C} (c : V ⟶ U) [IsIso c] :
    Function.Injective (M.map c.op) := by
  intro a b h
  have h' := congrArg (M.map (inv c).op) h
  rwa [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply, ← op_comp,
    IsIso.inv_hom_id, op_id, PresheafOfModules.map_id_apply, PresheafOfModules.map_id_apply] at h'

/-- A morphism of étale charts whose underlying morphism of test objects is an isomorphism is an
isomorphism. -/
private theorem isIso_of_isIso_hom_left {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (g : U ⟶ V) [IsIso g.hom.left] : IsIso g :=
  have : IsIso ((CostructuredArrow.proj yoneda s.space.1).map
      ((ObjectProperty.ι (IsEtaleChart s.site s.base s.containsBase s.space.1)).map g)) :=
    ‹IsIso g.hom.left›
  have : IsIso ((ObjectProperty.ι (IsEtaleChart s.site s.base s.containsBase s.space.1)).map g) :=
    isIso_of_reflects_iso _ (CostructuredArrow.proj yoneda s.space.1)
  isIso_of_reflects_iso _ (ObjectProperty.ι _)

private theorem pointTwistKerRestrict_zero {T T' : BigFppfOver s.site s.base s.containsBase}
    (k : T' ⟶ T) (f : yoneda.obj T ⟶ s.space.1) (n : ℤ)
    {W : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T').Opens}
    (hW : W₁ ≤
      (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ W) :
    pointTwistKerRestrict k f n hW 0 = 0 := by
  have h := pointTwistKerRestrict_add k f hW n 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

include hπ in
/-- Stacks 0801's ideal is carried into itself by the restriction along `k`
(`mem_pointTwistKer_restrict`), with the opens spelled in the site of the situation. -/
private theorem mem_pointKer_restrict {T T' : BigFppfOver s.site s.base s.containsBase}
    (k : T' ⟶ T) (f : yoneda.obj T ⟶ s.space.1) (n : ℤ)
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ((s.relativeProjPoints.algebra T f).piece n, W))
    (ha : a ∈ pointKer hπ i hi T f n W) :
    pointTwistKerRestrict k f n hW a ∈ pointKer hπ i hi T' (yoneda.map k ≫ f) n W₁ :=
  mem_pointTwistKer_restrict i hi k f hW hπ n a ha

include hπ in
/-- **The converse of the restriction of the graded ideal along a flat `k`**, when the chart
morphism of the restriction is an isomorphism: a section whose restriction lies in the ideal
at `f ∘ k` lies in the ideal at `f`. -/
private theorem mem_pointKer_of_restrict (hbridge : EtalePointBridge s)
    {T T₁ : BigFppfOver s.site s.base s.containsBase} (k : T₁ ⟶ T)
    (hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase k).hom)
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf₁ : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₁).Opens}
    (hW : W₁ ≤ preimageOpens k W) (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁)
    (hiso : IsIso (s.etalePointChartRestrict k hk f hf hf₁ hW))
    (hsurj : Function.Surjective (Scheme.Hom.appLE
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map k) W W₁ hW).hom)
    (x : Γ((s.relativeProjPoints.algebra T f).piece n, W))
    (hx : pointTwistKerRestrict k f n hW x ∈ pointKer hπ i hi T₁ (yoneda.map k ≫ f) n W₁) :
    x ∈ pointKer hπ i hi T f n W := by
  have := etale_toScheme_map_of_isEtale k f hf hf₁
  have key := hbridge k hk f hf hf₁ n hW
  have hinj := injective_map_of_isIso (s.algebra.piece n).val
    (s.etalePointChartRestrict k hk f hf hf₁ hW)
  have hspan := pointTwistKer_le_span_restrict i hi k f hW hπ n hWa hW₁a hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ pointKer hπ i hi T f n W,
      pointTwistKerRestrict k f n hW y = pointTwistKerRestrict k f n hW x := by
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ pointKer hπ i hi T f n W,
      pointTwistKerRestrict k f n hW y = z) ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, Submodule.zero_mem _, pointTwistKerRestrict_zero k f n hW⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
      exact ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, pointTwistKerRestrict_add k f hW n y₁ y₂⟩
    · rintro c₁ _ _ ⟨(y : Γ((s.relativeProjPoints.algebra T f).piece n, W)), hy, rfl⟩
      obtain ⟨c', rfl⟩ := hsurj c₁
      exact ⟨(c' • y : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
        Submodule.smul_mem _ c' hy, pointTwistKerRestrict_smul k f hW n c' y⟩
  have hRxy : s.etalePointReading f hf n W y = s.etalePointReading f hf n W x :=
    hinj ((key y).symm.trans ((congrArg _ hxy).trans (key x)))
  rw [← (s.etalePointReading f hf n W).injective hRxy]
  exact hy

include hπ in
/-- **The readings of a section of the 0801 ideal lie in `P_n`.** A section of the graded
ideal of Stacks 0801 of `Z ×_X T` over any open `W` of an étale scheme point reads, on the chart
of `W`, as a section satisfying the defining condition of `closedSubspaceReadingSubmodule`. -/
private theorem isClosedSubspaceReading_of_mem (hbridge : EtalePointBridge s)
    {T : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) (ha : a ∈ pointKer hπ i hi T f n W) :
    IsClosedSubspaceReading hπ i hi n (s.etalePointChart f hf W)
      (s.etalePointReading f hf n W a) := by
  intro T' f' hf' W' hW' φ'
  obtain ⟨κ, hκdef⟩ : ∃ κ : ((selfOpensFunctor s.site s.base s.containsBase T').obj W').1.left ⟶ T,
      κ = (φ'.hom.left ≫ selfOpensι T W : ((selfOpensFunctor s.site s.base s.containsBase T').obj
        W').1.left ⟶ T) := ⟨_, rfl⟩
  have e1 : yoneda.map κ =
      yoneda.map φ'.hom.left ≫ ((selfOpensFunctor s.site s.base s.containsBase T).obj W).1.hom :=
    (congrArg yoneda.map hκdef).trans ((yoneda.map_comp _ _).trans
      (congrArg (yoneda.map φ'.hom.left ≫ ·) (yoneda_map_selfOpensι T W)))
  have eP : yoneda.map κ ≫ f = yoneda.map (selfOpensι T' W') ≫ f' :=
    ((congrArg (· ≫ f) e1).trans (Category.assoc _ _ _)).trans ((CostructuredArrow.w φ'.hom).trans
      (congrArg (· ≫ f') (yoneda_map_selfOpensι T' W').symm))
  have hEφ : IsEtale s.site s.base s.containsBase (yoneda.map φ'.hom.left) :=
    (isEtale_iff_presheaf_of_yoneda _ _ _ _).2 (presheaf_etale_toOver_map _ _ _ _ φ')
  have hκ : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase κ).hom :=
    (congrArg (IsEtale s.site s.base s.containsBase) e1).mpr (isEtale_comp _ _ _ hEφ
      ((isEtale_iff_presheaf_of_yoneda _ _ _ _).2
        ((selfOpensFunctor s.site s.base s.containsBase T).obj W).2))
  have hι' : IsEtale s.site s.base s.containsBase (representedSpaceMap s.site s.base s.containsBase
      (selfOpensι T' W')).hom :=
    (congrArg (IsEtale s.site s.base s.containsBase) (yoneda_map_selfOpensι T' W')).mpr
      ((isEtale_iff_presheaf_of_yoneda _ _ _ _).2
        ((selfOpensFunctor s.site s.base s.containsBase T').obj W').2)
  have hfκ : IsEtale s.site s.base s.containsBase
      (pointHom (X := s.space) (yoneda.map κ ≫ f)).hom :=
    isEtale_comp _ _ _ hκ hf
  have hfι' : IsEtale s.site s.base s.containsBase
      (pointHom (X := s.space) (yoneda.map (selfOpensι T' W') ≫ f')).hom :=
    isEtale_comp _ _ _ hι' hf'
  have hWκ : ⊤ ≤ preimageOpens κ W := selfOpens_top_le_preimage T W κ φ'.hom.left e1
  have hWι' : ⊤ ≤ preimageOpens (selfOpensι T' W') W' :=
    selfOpens_top_le_preimage T' W' _ (𝟙 _)
      ((yoneda_map_selfOpensι T' W').trans ((Category.id_comp _).symm.trans
        (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _).symm)))
  have hb := mem_pointKer_restrict hπ i hi κ f n hWκ a ha
  have r1 := hbridge κ hκ f hf hfκ n hWκ a
  have r2 := (hbridge (selfOpensι T' W') hι' f' hf' hfι' n hWι'
    ((s.etalePointReading f' hf' n W').symm
      ((s.algebra.piece n).val.map φ'.op (s.etalePointReading f hf n W a)))).trans
    ((congrArg _ (Equiv.apply_symm_apply _ _)).trans
      (PresheafOfModules.map_comp_apply _ φ'.op
        (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι' hWι').op _).symm)
  have hcι : (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι' hWι').hom.left =
      selfOpensι _ ⊤ :=
    selfOpens_hom_ext T' W' _ _ ((yoneda_map_etalePointChartRestrict_left s _ hι' f' hf' hfι'
      hWι').trans ((congrArg (_ ≫ ·) (yoneda_map_selfOpensι T' W')).trans
        (congrArg (· ≫ _) (yoneda_map_selfOpensι _ ⊤).symm)))
  have h_a : yoneda.map (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι'
      hWι').hom.left = ((selfOpensFunctor s.site s.base s.containsBase
        ((selfOpensFunctor s.site s.base s.containsBase T').obj W').1.left).obj
          (⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
            ((selfOpensFunctor s.site s.base s.containsBase T').obj W').1.left).Opens)).1.hom :=
    (congrArg yoneda.map hcι).trans (yoneda_map_selfOpensι _ ⊤)
  have hL := (yoneda_map_etalePointChartRestrict_left s κ hκ f hf hfκ hWκ).trans
    (congrArg (_ ≫ ·) e1)
  have hR : yoneda.map (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι' hWι' ≫
      φ').hom.left ≫ ((selfOpensFunctor s.site s.base s.containsBase T).obj W).1.hom =
      ((selfOpensFunctor s.site s.base s.containsBase
        ((selfOpensFunctor s.site s.base s.containsBase T').obj W').1.left).obj
          (⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
            ((selfOpensFunctor s.site s.base s.containsBase T').obj W').1.left).Opens)).1.hom ≫
        (yoneda.map φ'.hom.left ≫
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W).1.hom) :=
    ((congrArg (· ≫ ((selfOpensFunctor s.site s.base s.containsBase T).obj W).1.hom)
      (yoneda.map_comp (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι'
        hWι').hom.left φ'.hom.left)).trans (Category.assoc _ _ _)).trans (congrArg (· ≫ _) h_a)
  have hψ : (s.etalePointChartRestrict κ hκ f hf hfκ hWκ).hom.left =
      (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι' hWι' ≫ φ').hom.left :=
    selfOpens_hom_ext T W _ _ (hL.trans hR.symm)
  have hy := mem_pointKer_of_eq hπ i hi (yoneda.map κ ≫ f)
    (yoneda.map (selfOpensι T' W') ≫ f') eP hfκ hfι' n ⊤ (s.etalePointReading f hf n W a)
    (s.etalePointChartRestrict κ hκ f hf hfκ hWκ)
    (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι' hWι' ≫ φ') hψ
    (pointTwistKerRestrict κ f n hWκ a)
    (pointTwistKerRestrict (selfOpensι T' W') f' n hWι'
      ((s.etalePointReading f' hf' n W').symm
        ((s.algebra.piece n).val.map φ'.op (s.etalePointReading f hf n W a)))) r1 r2 hb
  have : IsIso (s.etalePointChartRestrict (selfOpensι T' W') hι' f' hf' hfι' hWι').hom.left :=
    (congrArg IsIso hcι).mpr (isIso_selfOpensι_top _)
  have : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      ((selfOpensFunctor s.site s.base s.containsBase T').obj W').1.left) :=
    isAffine_etalePointChart s f' hf' hW'
  exact mem_pointKer_of_restrict hπ i hi hbridge (selfOpensι T' W') hι' f' hf' hfι' n hWι' hW'
    (isAffineOpen_top _) (isIso_of_isIso_hom_left _)
    (surjective_appLE_selfOpensι T' W' hWι') _ hy

include hπ in
/-- Stacks 0801's ideal along a flat `k` over affine opens is spanned by restrictions
(`pointTwistKer_le_span_restrict`), with the opens spelled in the site of the situation. -/
private theorem pointKer_le_span_restrict {T T' : BigFppfOver s.site s.base s.containsBase}
    (k : T' ⟶ T) (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁) :
    pointKer hπ i hi T' (yoneda.map k ≫ f) n W₁ ≤
      Submodule.span
        Γ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T', W₁)
        (pointTwistKerRestrict k f n hW '' SetLike.coe (pointKer hπ i hi T f n W)) := by
  have := etale_toScheme_map_of_isEtale k f hf hf'
  exact pointTwistKer_le_span_restrict i hi k f hW hπ n hWa hW₁a

include hπ in
/-- **Induction along Stacks 0801's ideal at `f ∘ k`** for `k` flat over affine opens: a property
of sections over `W₁`, stable under sums and multiplication by functions on `W₁` and true on the
restrictions of the sections of the ideal at `f` over `W`, holds on the ideal at `f ∘ k`. -/
private theorem pointKer_induction {T T' : BigFppfOver s.site s.base s.containsBase}
    (k : T' ⟶ T) (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁)
    (p : Γ((s.relativeProjPoints.algebra T' (yoneda.map k ≫ f)).piece n, W₁) → Prop)
    (hmem : ∀ w ∈ pointKer hπ i hi T f n W, p (pointTwistKerRestrict k f n hW w))
    (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hsmul : ∀ (r : Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T', W₁)) a, p a →
      p (r • a))
    (z : Γ((s.relativeProjPoints.algebra T' (yoneda.map k ≫ f)).piece n, W₁))
    (hz : z ∈ pointKer hπ i hi T' (yoneda.map k ≫ f) n W₁) : p z :=
  Submodule.span_induction (p := fun z _ => p z)
    (fun _ hx => by obtain ⟨w, hw, rfl⟩ := hx; exact hmem w hw) h0
    (fun a b _ _ => hadd a b) (fun r a _ => hsmul r a)
    (pointKer_le_span_restrict hπ i hi k f hf hf' n hW hWa hW₁a hz)

/-- The morphism from the chart of the open `⊤` of the test object of an étale chart `V`, at a
scheme point `g` equal to the structure morphism of `V`, to `V`. -/
private noncomputable def etalePointChartTopHom
    (V : SmallEtale s.site s.base s.containsBase s.space.1)
    (g : yoneda.obj V.1.left ⟶ s.space.1)
    (hg : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) g).hom) (e : g = V.1.hom) :
    s.etalePointChart g hg ⊤ ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (selfOpensι V.1.left ⊤)
    ((congrArg (· ≫ V.1.hom) (yoneda_map_selfOpensι _ ⊤)).trans (congrArg (_ ≫ ·) e.symm)))

private theorem isIso_etalePointChartTopHom (V : SmallEtale s.site s.base s.containsBase s.space.1)
    (g : yoneda.obj V.1.left ⟶ s.space.1)
    (hg : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) g).hom) (e : g = V.1.hom) :
    IsIso (etalePointChartTopHom V g hg e) := by
  have : IsIso (etalePointChartTopHom V g hg e).hom.left := isIso_selfOpensι_top _
  exact isIso_of_isIso_hom_left _

section PresheafMap

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

/-- The restriction map of a presheaf of modules, as a function into the sections of `M`. -/
private def pmap {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M.obj X) : M.obj Y := M.map g x

private theorem pmap_congr {X Y : Cᵒᵖ} (g : X ⟶ Y) {a b : M.obj X} (h : a = b) :
    pmap M g a = pmap M g b :=
  congrArg _ h

private theorem pmap_zero {X Y : Cᵒᵖ} (g : X ⟶ Y) : pmap M g 0 = 0 :=
  map_zero _

private theorem pmap_add {X Y : Cᵒᵖ} (g : X ⟶ Y) (a b : M.obj X) :
    pmap M g (a + b) = pmap M g a + pmap M g b :=
  map_add _ _ _

private theorem pmap_smul {X Y : Cᵒᵖ} (g : X ⟶ Y) (r : R.obj X) (a : M.obj X) :
    pmap M g (r • a) = R.map g r • pmap M g a :=
  PresheafOfModules.map_smul _ _ _ _

private theorem pmap_pmap_of_comp_eq {X Y Y' Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (f' : Y' ⟶ X)
    (g' : Z ⟶ Y') (h : g ≫ f = g' ≫ f') (x : M.obj (op X)) {y : M.obj (op Y')}
    (hy : pmap M f'.op x = y) : pmap M g.op (pmap M f.op x) = pmap M g'.op y := by
  rw [← hy]
  change M.map g.op (M.map f.op x) = M.map g'.op (M.map f'.op x)
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← op_comp, h]

private theorem pmap_inv_pmap {X Y : C} (c : X ⟶ Y) [IsIso c] (x : M.obj (op Y)) :
    pmap M (inv c).op (pmap M c.op x) = x := by
  change M.map (inv c).op (M.map c.op x) = x
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
    PresheafOfModules.map_id_apply]

private theorem pmap_id {X : Cᵒᵖ} (x : M.obj X) : pmap M (𝟙 X) x = x := by
  change M.map (𝟙 X) x = x
  rw [PresheafOfModules.map_id_apply]

end PresheafMap

/-- The square of chart morphisms between the charts of `⊤` at the scheme points `V` and `U` of a
morphism `φ : V ⟶ U` of étale charts. -/
private theorem inv_etalePointChartTopHom_comp
    {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (φ : V ⟶ U)
    (hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase φ.hom.left).hom)
    (hfU : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) U.1.hom).hom)
    (hfk : IsEtale s.site s.base s.containsBase
      (pointHom (X := s.space) (yoneda.map φ.hom.left ≫ U.1.hom)).hom)
    (hw : yoneda.map φ.hom.left ≫ U.1.hom = V.1.hom)
    (hW : (⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left).Opens) ≤
      preimageOpens φ.hom.left
        (⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj U.1.left).Opens))
    [IsIso (etalePointChartTopHom V _ hfk hw)] [IsIso (etalePointChartTopHom U U.1.hom hfU rfl)] :
    inv (etalePointChartTopHom V _ hfk hw) ≫
      s.etalePointChartRestrict φ.hom.left hk U.1.hom hfU hfk hW =
        φ ≫ inv (etalePointChartTopHom U U.1.hom hfU rfl) := by
  have hsq : s.etalePointChartRestrict φ.hom.left hk U.1.hom hfU hfk hW ≫
      etalePointChartTopHom U U.1.hom hfU rfl = etalePointChartTopHom V _ hfk hw ≫ φ := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (yoneda.map_injective ?_))
    exact ((yoneda.map_comp _ _).trans ((congrArg (_ ≫ ·) (yoneda_map_selfOpensι _ ⊤)).trans
      ((yoneda_map_etalePointChartRestrict_left s _ hk _ hfU hfk hW).trans
        (congrArg (· ≫ _) (yoneda_map_selfOpensι _ ⊤).symm)))).trans (yoneda.map_comp _ _).symm
  exact (IsIso.inv_comp_eq (etalePointChartTopHom V _ hfk hw)).2
    (((IsIso.eq_comp_inv (etalePointChartTopHom U U.1.hom hfU rfl)).2 hsq).trans
      (Category.assoc _ _ _))

private theorem mem_of_eq_of_mem' {R M : Type*} {_ : Semiring R} {_ : AddCommMonoid M}
    {_ : Module R M} (N : Submodule R M) {x y : M} (h : x = y) (hy : y ∈ N) : x ∈ N :=
  h ▸ hy

include hπ in
/-- The reading at `f ∘ k`, carried to a chart `V` isomorphic to the chart of `W₁`, of the
restriction of a section of the 0801 ideal at `f` is the restriction along `φ : V ⟶ U` of a
section of `P_n` over a chart `U` isomorphic to the chart of `W`. -/
private theorem pmap_reading_pointTwistKerRestrict_mem (hbridge : EtalePointBridge s)
    {T T₁ : BigFppfOver s.site s.base s.containsBase} (k : T₁ ⟶ T)
    (hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase k).hom)
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf₁ : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₁).Opens}
    (hW : W₁ ≤ preimageOpens k W) {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (φ : V ⟶ U) (cU : s.etalePointChart f hf W ⟶ U)
    (cV : s.etalePointChart (yoneda.map k ≫ f) hf₁ W₁ ⟶ V) [IsIso cU] [IsIso cV]
    (hsq : inv cV ≫ s.etalePointChartRestrict k hk f hf hf₁ hW = φ ≫ inv cU)
    (w : Γ((s.relativeProjPoints.algebra T f).piece n, W)) (hw : w ∈ pointKer hπ i hi T f n W) :
    pmap (s.algebra.piece n).val (inv cV).op
        (s.etalePointReading (yoneda.map k ≫ f) hf₁ n W₁ (pointTwistKerRestrict k f n hW w)) ∈
      chartRestrictLinear (s.algebra.piece n) φ ''
        ((closedSubspaceReadingSubmodule hπ i hi n).obj (op U) :
          Set ((s.algebra.piece n).val.obj (op U))) :=
  ⟨pmap (s.algebra.piece n).val (inv cU).op (s.etalePointReading f hf n W w),
    (mem_closedSubspaceReadingSubmodule_iff hπ i hi n U _).2 (IsClosedSubspaceReading.map hπ i hi _
      (isClosedSubspaceReading_of_mem hπ i hi hbridge f hf n W w hw)),
    pmap_pmap_of_comp_eq (s.algebra.piece n).val (inv cU) φ
      (s.etalePointChartRestrict k hk f hf hf₁ hW) (inv cV) hsq.symm
      (s.etalePointReading f hf n W w) (hbridge k hk f hf hf₁ n hW w).symm⟩

include hπ in
/-- The reading at `f ∘ k`, carried to `V`, of a section in the span of the restrictions of the
0801 ideal at `f` lies in the span of the restrictions of `P_n` along `φ`. -/
private theorem pmap_reading_mem_span (hbridge : EtalePointBridge s)
    {T T₁ : BigFppfOver s.site s.base s.containsBase} (k : T₁ ⟶ T)
    (hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase k).hom)
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf₁ : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₁).Opens}
    (hW : W₁ ≤ preimageOpens k W) {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (φ : V ⟶ U) (cU : s.etalePointChart f hf W ⟶ U)
    (cV : s.etalePointChart (yoneda.map k ≫ f) hf₁ W₁ ⟶ V) [IsIso cU] [IsIso cV]
    (hsq : inv cV ≫ s.etalePointChartRestrict k hk f hf hf₁ hW = φ ≫ inv cU)
    (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁)
    (z : Γ((s.relativeProjPoints.algebra T₁ (yoneda.map k ≫ f)).piece n, W₁))
    (hz : z ∈ pointKer hπ i hi T₁ (yoneda.map k ≫ f) n W₁) :
    pmap (s.algebra.piece n).val (inv cV).op (s.etalePointReading (yoneda.map k ≫ f) hf₁ n W₁ z) ∈
      Submodule.span (chartRing s.site s.base s.containsBase s.space.1 s.space.2 V)
        (chartRestrictLinear (s.algebra.piece n) φ ''
          ((closedSubspaceReadingSubmodule hπ i hi n).obj (op U) :
            Set ((s.algebra.piece n).val.obj (op U)))) :=
  pointKer_induction hπ i hi k f hf hf₁ n hW hWa hW₁a
    (fun z => pmap (s.algebra.piece n).val (inv cV).op
      (s.etalePointReading (yoneda.map k ≫ f) hf₁ n W₁ z) ∈
        Submodule.span (chartRing s.site s.base s.containsBase s.space.1 s.space.2 V)
          (chartRestrictLinear (s.algebra.piece n) φ ''
            ((closedSubspaceReadingSubmodule hπ i hi n).obj (op U) :
              Set ((s.algebra.piece n).val.obj (op U)))))
    (fun w hw => Submodule.subset_span
      (pmap_reading_pointTwistKerRestrict_mem hπ i hi hbridge k hk f hf hf₁ n hW φ cU cV hsq w hw))
    (mem_of_eq_of_mem' _ ((pmap_congr _ _ (s.etalePointReading_zero _ hf₁ n W₁)).trans
      (pmap_zero _ _)) (Submodule.zero_mem _))
    (fun a b ha hb => mem_of_eq_of_mem' _
      ((pmap_congr _ _ (s.etalePointReading_add _ hf₁ n W₁ a b)).trans
      (pmap_add _ _ _ _)) (Submodule.add_mem _ ha hb))
    (fun r a ha => mem_of_eq_of_mem' _
      ((pmap_congr _ _ (s.etalePointReading_smul _ hf₁ n W₁ r a)).trans
      (pmap_smul _ _ _ _)) (Submodule.smul_mem _
        ((structureRingSheaf s.site s.base s.containsBase s.space).obj.map (inv cV).op
          (etalePointChartRingHom _ hf₁ W₁ r)) ha))
    z hz

include hπ in
/-- `P_n` is cartesian along `φ : V ⟶ U`, for charts `U`, `V` isomorphic to the charts of opens
`W`, `W₁` of scheme points related by `k`, when the sections of `P_n` over `V` read into the 0801
ideal at `f ∘ k`. -/
private theorem closedSubspaceReadingSubmodule_le_span_of_iso (hbridge : EtalePointBridge s)
    {T T₁ : BigFppfOver s.site s.base s.containsBase} (k : T₁ ⟶ T)
    (hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase k).hom)
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf₁ : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)
    (n : ℤ) {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₁).Opens}
    (hW : W₁ ≤ preimageOpens k W) {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (φ : V ⟶ U) (cU : s.etalePointChart f hf W ⟶ U)
    (cV : s.etalePointChart (yoneda.map k ≫ f) hf₁ W₁ ⟶ V) [IsIso cU] [IsIso cV]
    (hsq : inv cV ≫ s.etalePointChartRestrict k hk f hf hf₁ hW = φ ≫ inv cU)
    (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁) :
    (closedSubspaceReadingSubmodule hπ i hi n).obj (op V) ≤
      Submodule.span (chartRing s.site s.base s.containsBase s.space.1 s.space.2 V)
        (chartRestrictLinear (s.algebra.piece n) φ ''
          ((closedSubspaceReadingSubmodule hπ i hi n).obj (op U) :
            Set ((s.algebra.piece n).val.obj (op U)))) := by
  intro x hx
  have e_x : pmap (s.algebra.piece n).val (inv cV).op
      (s.etalePointReading (yoneda.map k ≫ f) hf₁ n W₁
        ((s.etalePointReading (yoneda.map k ≫ f) hf₁ n W₁).symm
          ((s.algebra.piece n).val.map cV.op x))) = x :=
    (pmap_congr _ _ (Equiv.apply_symm_apply _ _)).trans (pmap_inv_pmap _ _ x)
  have hC := pmap_reading_mem_span hπ i hi hbridge k hk f hf hf₁ n hW φ cU cV hsq hWa hW₁a _
    ((mem_closedSubspaceReadingSubmodule_iff hπ i hi n V x).1 hx T₁ (yoneda.map k ≫ f) hf₁ W₁ hW₁a
      cV)
  rw [e_x] at hC
  exact hC

include hπ in
/-- **`P` is cartesian on affine charts.** Along a morphism `φ : V ⟶ U` of affine étale
charts, the sections of `P_n` over `V` are generated by the restrictions of the sections of `P_n`
over `U`: read at the scheme points `V` and `U`, this is the flat base change of the 0801 ideal
along `φ` (`pointTwistKer_le_span_restrict`). -/
private theorem closedSubspaceReadingSubmodule_le_span (hbridge : EtalePointBridge s) (n : ℤ)
    {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (φ : V ⟶ U) :
    (closedSubspaceReadingSubmodule hπ i hi n).obj (op V) ≤
      Submodule.span (chartRing s.site s.base s.containsBase s.space.1 s.space.2 V)
        (chartRestrictLinear (s.algebra.piece n) φ ''
          ((closedSubspaceReadingSubmodule hπ i hi n).obj (op U) :
            Set ((s.algebra.piece n).val.obj (op U)))) := by
  have hfU : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) U.1.hom).hom :=
    (isEtale_iff_presheaf_of_yoneda _ _ _ _).2 U.2
  have hk : IsEtale s.site s.base s.containsBase
      (representedSpaceMap s.site s.base s.containsBase φ.hom.left).hom :=
    (isEtale_iff_presheaf_of_yoneda _ _ _ _).2 (presheaf_etale_toOver_map _ _ _ _ φ)
  have hfk : IsEtale s.site s.base s.containsBase
      (pointHom (X := s.space) (yoneda.map φ.hom.left ≫ U.1.hom)).hom :=
    isEtale_comp _ _ _ hk hfU
  have hw : yoneda.map φ.hom.left ≫ U.1.hom = V.1.hom := CostructuredArrow.w φ.hom
  have hW : (⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left).Opens) ≤
      preimageOpens φ.hom.left
        (⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj U.1.left).Opens) :=
    fun _ _ => trivial
  have : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left) := hV
  have : IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj U.1.left) := hU
  have hcV : IsIso (etalePointChartTopHom V _ hfk hw) := isIso_etalePointChartTopHom V _ hfk hw
  have hcU : IsIso (etalePointChartTopHom U U.1.hom hfU rfl) :=
    isIso_etalePointChartTopHom U U.1.hom hfU rfl
  exact closedSubspaceReadingSubmodule_le_span_of_iso hπ i hi hbridge φ.hom.left hk U.1.hom hfU hfk
    n hW φ (etalePointChartTopHom U U.1.hom hfU rfl) (etalePointChartTopHom V _ hfk hw)
    (inv_etalePointChartTopHom_comp φ hk hfU hfk hw hW) (isAffineOpen_top _) (isAffineOpen_top _)

/-- Reading the restriction along `k` of a section is restricting its reading along
`etalePointChartRestrict` (`EtalePointBridge`): `etalePointReading_pointTwistKerRestrict`. -/
private theorem etalePointBridge_holds : EtalePointBridge s :=
  fun k hk f hf hf' n _ _ hW a => s.etalePointReading_pointTwistKerRestrict k hk f hf hf' n hW a

/-- **`P_n` is cartesian on affine charts.** Along a morphism `φ : V ⟶ U` of affine étale charts
of `X`, the sections of `closedSubspaceReadingSubmodule` over `V` are generated by the
restrictions of its sections over `U`. -/
theorem closedSubspaceReadingSubmodule_le_span_restrict (n : ℤ)
    {U V : SmallEtale s.site s.base s.containsBase s.space.1}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (φ : V ⟶ U) :
    (closedSubspaceReadingSubmodule hπ i hi n).obj (op V) ≤
      Submodule.span (chartRing s.site s.base s.containsBase s.space.1 s.space.2 V)
        (chartRestrictLinear (s.algebra.piece n) φ ''
          ((closedSubspaceReadingSubmodule hπ i hi n).obj (op U) :
            Set ((s.algebra.piece n).val.obj (op U)))) :=
  closedSubspaceReadingSubmodule_le_span hπ i hi etalePointBridge_holds n hU hV φ

/-- **The quasi-coherent graded ideal of a closed subspace of a relative Proj**: its degree-`n`
piece is the closure of `closedSubspaceReadingSubmodule`, the sections of `𝒜_n` whose readings at
every étale scheme point lie in the graded ideal of Stacks 0801 of the base change of `Z`. -/
def closedSubspaceGradedIdeal : s.GradedIdeal :=
  gradedIdealOfCartesian s (closedSubspaceReadingSubmodule hπ i hi)
    (closedSubspaceReadingSubmodule_mul_mem_left hπ i hi)
    (closedSubspaceReadingSubmodule_mul_mem_right hπ i hi)
    (fun n _ _ hU hV φ => closedSubspaceReadingSubmodule_le_span_restrict hπ i hi n hU hV φ)

private theorem mem_pointKer_of_reading_mem {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    {W' W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens} (h : W' ≤ W)
    (hW' : IsAffineOpen W') (a : Γ((s.relativeProjPoints.algebra T f).piece n, W))
    (ha : s.etalePointReading f hf n W a ∈
      ((closedSubspaceGradedIdeal hπ i hi).piece n).obj (op (s.etalePointChart f hf W))) :
    ((s.relativeProjPoints.algebra T f).piece n).presheaf.map (homOfLE h).op a ∈
      pointKer hπ i hi T f n W' := by
  have h1 := ((closedSubspaceGradedIdeal hπ i hi).piece n).toSubmodule.map_mem
    ((smallEtalePostcomp s.site s.base s.containsBase (pointHom f) hf).map
      ((selfOpensFunctor s.site s.base s.containsBase T).map (homOfLE h))).op ha
  have h2 := mem_of_eq_of_mem' _ (s.etalePointReading_restrict f hf n h a) h1
  have h3 := (congrArg (fun N => _ ∈ N) (gradedIdealOfCartesian_obj_of_isAffine s
    (closedSubspaceReadingSubmodule hπ i hi)
    (closedSubspaceReadingSubmodule_mul_mem_left hπ i hi)
    (closedSubspaceReadingSubmodule_mul_mem_right hπ i hi)
    (fun n _ _ hU hV φ => closedSubspaceReadingSubmodule_le_span_restrict hπ i hi n hU hV φ) n
    (isAffine_etalePointChart s f hf hW'))).mp h2
  have hmem := (mem_closedSubspaceReadingSubmodule_iff hπ i hi n _ _).1 h3 T f hf W' hW' (𝟙 _)
  have e : (s.etalePointReading f hf n W').symm ((s.algebra.piece n).val.map (𝟙 _).op
      (s.etalePointReading f hf n W'
        (((s.relativeProjPoints.algebra T f).piece n).presheaf.map (homOfLE h).op a))) =
      ((s.relativeProjPoints.algebra T f).piece n).presheaf.map (homOfLE h).op a :=
    (congrArg (s.etalePointReading f hf n W').symm (pmap_id _ _)).trans
      ((s.etalePointReading f hf n W').symm_apply_apply _)
  exact mem_of_eq_of_mem' _ e.symm hmem

private theorem mem_pointKer_iff_reading {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    a ∈ pointKer hπ i hi T f n W ↔
      s.etalePointReading f hf n W a ∈
        ((closedSubspaceGradedIdeal hπ i hi).piece n).obj (op (s.etalePointChart f hf W)) := by
  refine ⟨fun ha => (PresheafOfModules.Submodule.le_iff.1 (le_gradedIdealOfCartesian s
      (closedSubspaceReadingSubmodule hπ i hi)
      (closedSubspaceReadingSubmodule_mul_mem_left hπ i hi)
      (closedSubspaceReadingSubmodule_mul_mem_right hπ i hi)
      (fun n _ _ hU hV φ => closedSubspaceReadingSubmodule_le_span_restrict hπ i hi n hU hV φ) n)
      (op (s.etalePointChart f hf W)))
      (isClosedSubspaceReading_of_mem hπ i hi etalePointBridge_holds f hf n W a ha), fun h => ?_⟩
  have := quasiCompact_relativeProj_toBase hπ T f
  refine ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
    (chartClosedSubscheme i hi T f)).piece n).isSheaf a fun p hp => ?_
  obtain ⟨_, ⟨W', hW', rfl⟩, hpW', hW'W⟩ :=
    ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).isBasis_affineOpens
      |>.exists_subset_of_mem_open hp W.2
  exact ⟨W', homOfLE hW'W, mem_pointKer_of_reading_mem hπ i hi f hf n hW'W hW' a h, hpW'⟩

/-- **The graded ideal of the closed subspace cuts out the graded ideals of Stacks 0801 at the
étale scheme points**: at every étale scheme point `f : T ⟶ X` of the base of Situation 0849, a
homogeneous local section of `f^*𝒜` lies in the graded ideal of Stacks 0801 of
`Z ×_X T ⊆ Proj_T(f^*𝒜)` exactly when the restriction of `𝒜 ⟶ 𝒜 ⧸ ℐ` kills it, for
`ℐ = closedSubspaceGradedIdeal hπ i hi`. -/
theorem mem_twistKerGradedIdeal_iff_closedSubspaceGradedIdeal :
    ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1),
      IsEtale s.site s.base s.containsBase f → ∀ (n : ℤ)
      (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
      haveI := quasiCompact_relativeProj_toBase hπ T f
      a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W) ↔
        (((closedSubspaceGradedIdeal hπ i hi).quotientHomPoints.hom T f).app n).app W a = 0 := by
  intro T f hf n W a
  exact (mem_pointKer_iff_reading hπ i hi f hf n W a).trans
    ((closedSubspaceGradedIdeal hπ i hi).quotientHomPoints_app_eq_zero_iff f hf n W a).symm

end Kernel

end AlgebraicGeometry.Space.RelativeProjSituation

end
