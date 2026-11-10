module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSideConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteNearCodimensionOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionDenseOpenInSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Steps of the proof of Stacks 0ADD

Stacks 0ADD says that a point of codimension at most one on a locally Noetherian separated
algebraic space has an open neighbourhood which is a scheme. Its proof inducts on the degree of
an étale chart `v : h_V ⟶ Z` at the codimension-zero points, for a chart which is immersed, over
`Z`, in a proper representable morphism `q : Q ⟶ Z`. This file proves the steps of that induction;
the induction itself and Stacks 0ADD are in
`StacksFrontier/AlgebraicGeometry/Spaces/CodimensionOneSchematicLocus.lean`, and no Stacks tag is
registered here.

Write `Y` for the scheme-theoretic image of `h_V` in `Q`, `p : Y ⟶ Z` for its morphism to `Z`, and
`j : h_V ⟶ Y` for the canonical morphism, a dense open immersion by Stacks 088G.

## Main definitions

* `AlgebraicGeometry.Space.ChartRankAtCodimZeroLE`: the fibres of a chart at the field-valued
  points of codimension zero are finite locally free of rank at most `d`.

## Main results

* `AlgebraicGeometry.exists_add_one_eq_and_isFiniteLocallyFreeOfRank_of_isCompl`: if a scheme
  finite locally free of rank `r` over a field is the disjoint union of an open subscheme and a
  copy of the field's spectrum, the open subscheme has rank `r - 1`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_schemeTheoreticImage`: `Y` is finite
  over a neighbourhood of a point of codimension at most one (Stacks 0AD2).
* `AlgebraicGeometry.Space.notMem_range_pointsMap_of_chartRankAtCodimZeroLE_zero`: the base case,
  a chart of degree `0` at the codimension-zero points has empty image.
* `AlgebraicGeometry.Space.exists_chart_of_complement_graph`: the inductive step. The complement
  `W` of the graph of `j` in `h_V ×_Z Y` is an étale chart of `Y`, immersed over `Y` in the proper
  representable `Q ×_Z Y ⟶ Y`; it reaches every point of `Y` outside `h_V` above the image of `v`,
  and its degree at the codimension-zero points is one less than that of `v`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_pullback_of_isFinite`: a finite
  morphism whose fibre over `z` is covered by representable open subspaces is representable over
  a neighbourhood of `z`.

## Implementation notes

The graph of `j` is closed in `h_V ×_Z Y` by Stacks 03KO, because `p` is separated, and open
because it is an étale monomorphism. At a field-valued point `ξ` of `Y` of codimension zero, `ξ`
factors through `j` (a quasi-compact morphism reaches the codimension-zero points of its
scheme-theoretic image), so the fibre of `h_V ×_Z Y ⟶ Y` at `ξ`, which is the fibre of `v` at
`ξ ≫ p`, is the disjoint union of the fibre of `W` and a section; the degrees are compared on
global sections over the field.

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 03KO](https://stacks.math.columbia.edu/tag/03KO)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- Two open immersions into `X` have complementary images iff their ranges are complementary
sets. -/
private theorem isCompl_opensRange_iff_range_eq_compl {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsCompl f.opensRange g.opensRange ↔ Set.range f = (Set.range g)ᶜ := by
  rw [eq_compl_iff_isCompl]
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← SetLike.coe_set_eq,
    TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_sup,
    TopologicalSpace.Opens.coe_bot, TopologicalSpace.Opens.coe_top, Scheme.Hom.coe_opensRange,
    Set.bot_eq_empty, Set.top_eq_univ, Set.inf_eq_inter, Set.sup_eq_union]

/-- **Removing a rational point from a finite locally free scheme over a field lowers the
rank by one.** Let `f : X ⟶ Spec K` be finite locally free of rank `r`, and let `X` be the
disjoint union of the open subschemes `e₁ : X₁ ⟶ X` and `e₂ : T ⟶ X`, where `T` maps
isomorphically to `Spec K`. Then `X₁ ⟶ Spec K` is finite locally free of rank `s` with
`s + 1 = r`.

The sections of `X` are the product of the sections of `X₁` and of `T`, since `X` is the
coproduct of the two pieces, and the rank over a field is the dimension of the global
sections (`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq`). -/
@[ega "I 6.4.5" "6.4.5.1 with Y ≅ Spec K"]
theorem exists_add_one_eq_and_isFiniteLocallyFreeOfRank_of_isCompl {K : Type u} [Field K]
    {X X₁ T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (r : ℕ)
    (hf : IsFiniteLocallyFreeOfRank f r) (e₁ : X₁ ⟶ X) (e₂ : T ⟶ X)
    [IsOpenImmersion e₁] [IsOpenImmersion e₂] (hc : IsCompl e₁.opensRange e₂.opensRange)
    [IsIso (e₂ ≫ f)] :
    ∃ s : ℕ, s + 1 = r ∧ IsFiniteLocallyFreeOfRank (e₁ ≫ f) s := by
  classical
  have hrange := (isCompl_opensRange_iff_range_eq_compl e₁ e₂).1 hc
  have hcl : IsClosed (Set.range e₁) := by
    rw [hrange]; exact e₂.isOpenEmbedding.isOpen_range.isClosed_compl
  have : IsClosedImmersion e₁ := IsClosedImmersion.of_isPreimmersion e₁ hcl
  have : IsAffineHom f := hf.toIsAffineHom
  let a₀ : Algebra K Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  let a₁ : Algebra K Γ(X₁, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (e₁ ≫ f).appTop).hom.toAlgebra
  let a₂ : Algebra K Γ(T, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (e₂ ≫ f).appTop).hom.toAlgebra
  obtain ⟨-, hfin₀, hrank₀⟩ := (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq f r).1 hf
  -- the sections over `T` are one-dimensional
  have : IsIso (e₂ ≫ f).appTop := inferInstanceAs (IsIso ((e₂ ≫ f).app ⊤))
  have hbij₂ : Function.Bijective (algebraMap K Γ(T, ⊤)) :=
    ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (e₂ ≫ f).appTop)
  let L₂ : K ≃ₗ[K] Γ(T, ⊤) := LinearEquiv.ofBijective (Algebra.linearMap K Γ(T, ⊤)) hbij₂
  have hfin₂ : Module.Finite K Γ(T, ⊤) := Module.Finite.equiv L₂
  have hrank₂ : Module.finrank K Γ(T, ⊤) = 1 := by
    rw [← L₂.finrank_eq, Module.finrank_self]
  -- the sections over `X` split as a product
  let hcol := (nonempty_isColimit_binaryCofanMk_of_isCompl e₁ e₂ hc).some
  let c : X₁ ⨿ T ≅ X := (coprodIsCoprod X₁ T).coconePointUniqueUpToIso hcol
  have hc₁ : coprod.inl ≫ c.hom = e₁ :=
    (coprodIsCoprod X₁ T).comp_coconePointUniqueUpToIso_hom hcol ⟨WalkingPair.left⟩
  have hc₂ : coprod.inr ≫ c.hom = e₂ :=
    (coprodIsCoprod X₁ T).comp_coconePointUniqueUpToIso_hom hcol ⟨WalkingPair.right⟩
  have : IsIso c.hom.appTop := inferInstanceAs (IsIso (c.hom.app ⊤))
  let ψi : Γ(X, ⊤) ≅ CommRingCat.of (Γ(X₁, ⊤) × Γ(T, ⊤)) :=
    asIso c.hom.appTop ≪≫ Scheme.coprodPresheafObjIso ⊤ ≪≫
      limit.isoLimitCone ⟨_, CommRingCat.prodFanIsLimit _ _⟩
  let ψ : Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X₁, ⊤) × Γ(T, ⊤)) := ψi.hom
  have hψ : ∀ x, ψ x = (e₁.appTop x, e₂.appTop x) := by
    intro x
    refine Prod.ext ?_ ?_
    · change ((limit.isoLimitCone ⟨_, CommRingCat.prodFanIsLimit _ _⟩).hom ≫
          (CommRingCat.prodFan _ _).fst) ((Scheme.coprodPresheafObjIso ⊤).hom
            (c.hom.appTop x)) = _
      rw [limit.isoLimitCone_hom_π]
      change ((Scheme.coprodPresheafObjIso ⊤).hom ≫ prod.fst) (c.hom.appTop x) = _
      rw [Scheme.coprodPresheafObjIso_hom_fst, ← hc₁]
      rfl
    · change ((limit.isoLimitCone ⟨_, CommRingCat.prodFanIsLimit _ _⟩).hom ≫
          (CommRingCat.prodFan _ _).snd) ((Scheme.coprodPresheafObjIso ⊤).hom
            (c.hom.appTop x)) = _
      rw [limit.isoLimitCone_hom_π]
      change ((Scheme.coprodPresheafObjIso ⊤).hom ≫ prod.snd) (c.hom.appTop x) = _
      rw [Scheme.coprodPresheafObjIso_hom_snd, ← hc₂]
      rfl
  have hψbij : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso ψ
  let φ : Γ(X, ⊤) →ₐ[K] Γ(X₁, ⊤) × Γ(T, ⊤) :=
    { toRingHom := e₁.appTop.hom.prod e₂.appTop.hom
      commutes' := fun _ => rfl }
  have hφbij : Function.Bijective φ := by
    convert hψbij using 1
    funext x
    exact (hψ x).symm
  let Φ : Γ(X, ⊤) ≃ₗ[K] Γ(X₁, ⊤) × Γ(T, ⊤) :=
    (AlgEquiv.ofBijective φ hφbij).toLinearEquiv
  have hfinP : Module.Finite K (Γ(X₁, ⊤) × Γ(T, ⊤)) := Module.Finite.equiv Φ
  have hfin₁ : Module.Finite K Γ(X₁, ⊤) :=
    Module.Finite.of_surjective (LinearMap.fst K Γ(X₁, ⊤) Γ(T, ⊤)) Prod.fst_surjective
  refine ⟨Module.finrank K Γ(X₁, ⊤), ?_, ?_⟩
  · rw [← hrank₀, Φ.finrank_eq, Module.finrank_prod, hrank₂]
  · exact (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq (e₁ ≫ f) _).2
      ⟨inferInstance, hfin₁, rfl⟩

/-- **Removing a section from a finite locally free scheme over a field lowers the rank by
one.** If `g : X ⟶ T` is finite locally free of rank `r`, with `T ≅ Spec K`, and `X` is the
disjoint union of open subschemes `μ : X₁ ⟶ X` and `σ : T ⟶ X` with `σ` a section of `g`, then
`μ ≫ g` is finite locally free of rank `s` with `s + 1 = r`. -/
private theorem exists_add_one_eq_and_isFiniteLocallyFreeOfRank_of_isCompl_section {K : Type u}
    [Field K] {X X₁ T : Scheme.{u}} (g : X ⟶ T) (e : T ≅ Spec (CommRingCat.of K)) (r : ℕ)
    (hg : IsFiniteLocallyFreeOfRank g r) (μ : X₁ ⟶ X) (σ : T ⟶ X)
    [IsOpenImmersion μ] [IsOpenImmersion σ] (hc : IsCompl μ.opensRange σ.opensRange)
    (hσ : σ ≫ g = 𝟙 T) :
    ∃ s : ℕ, s + 1 = r ∧ IsFiniteLocallyFreeOfRank (μ ≫ g) s := by
  have : IsIso (σ ≫ g ≫ e.hom) := by
    rw [← Category.assoc, hσ, Category.id_comp]
    infer_instance
  obtain ⟨s, hs, hsflf⟩ := exists_add_one_eq_and_isFiniteLocallyFreeOfRank_of_isCompl
    (g ≫ e.hom) r (isFiniteLocallyFreeOfRank_postcomp e _ hg) μ σ hc
  refine ⟨s, hs, ?_⟩
  simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id] using
    isFiniteLocallyFreeOfRank_postcomp e.symm _ hsflf

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance hasPullbacks_presheaf_CodimensionOneChartInduction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_CodimensionOneChartInduction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rank of an étale chart at the codimension-zero field points is at most `d`.** For
every field `K`, every object `T` of the site whose scheme is `Spec K`, every morphism
`ξ : h_T ⟶ Z` whose point has a local ring of dimension `0`, and every representable
presentation `V_ξ ⟶ T` of the fibre of `v` at `ξ`, the morphism `V_ξ ⟶ T` is finite locally free
of some rank `r ≤ d`. -/
def ChartRankAtCodimZeroLE {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : BigFppfOver B S hS)
    (v : yoneda.obj V ⟶ Z) (d : ℕ) : Prop :=
  ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
    (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ Z) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
    (i : yoneda.obj Vf ⟶ yoneda.obj V),
    IsPullback i (yoneda.map q) v ξ →
    (∀ t : points B S hS (yoneda.obj T), localRingDimension B S hS (pointsMap B S hS _ ξ t) = 0) →
      ∃ r : ℕ, r ≤ d ∧ IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r

/-- **A morphism from a quasi-compact representable to a space proper over a separated algebraic
space is quasi-compact.** -/
private theorem isQuasiCompact_of_compactSpace_of_isProper {Z Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal Z) (hQ : IsAlgebraicSpace B S hS Q)
    {q : Q ⟶ Z} (hq : IsProper B S hS q) {V : BigFppfOver B S hS}
    (hVc : CompactSpace ((BigFppfOver.toScheme B S hS).obj V)) (i : yoneda.obj V ⟶ Q) :
    IsQuasiCompact B S hS i :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hQ
    (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal Q
      (isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep hq.1))
    (isQuasiCompactSpace_yoneda B S hS V hVc) i

/-- **The scheme-theoretic image of the chart in `Q` is finite over a neighbourhood of `z`.**
For an étale chart `v : h_V ⟶ Z` with quasi-compact source, immersed by `i` in a proper `Q ⟶ Z`,
and a point `z` of codimension at most one on the locally Noetherian separated `Z`, there is an
open subspace `Z₁ ∋ z` over which the scheme-theoretic image of `i` is finite. This is
Stacks 0AD2, applicable because `h_V` is open and dense in that image (Stacks 088G) and is
locally quasi-finite over `Z`. -/
theorem exists_isOpenSubspace_isFinite_schemeTheoreticImage
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal Z)
    (hnoeth : HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (z : points B S hS Z) (hdim : localRingDimension B S hS z ≤ 1)
    (V : BigFppfOver B S hS) (_ : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (v : yoneda.obj V ⟶ Z) (_ : IsEtale B S hS v)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ Z) (_ : IsProper B S hS q)
    (i : yoneda.obj V ⟶ Q) (_ : IsImmersion B S hS i) (_ : i ≫ q = v) :
    ∃ Z₁ : Subfunctor Z, IsOpenSubspace B S hS Z₁ ∧
      z ∈ Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι) ∧
      IsFinite B S hS (pullback.snd ((schemeTheoreticImageSubfunctor B S hS i).ι ≫ q) Z₁.ι) := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hiqc : IsQuasiCompact B S hS i :=
    isQuasiCompact_of_compactSpace_of_isProper B S hS hsep hQ ‹IsProper B S hS q› ‹_› i
  obtain ⟨hjopen, hiso, hrange, -, hdense⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hV hQ i ‹_›
      (Or.inl hiqc)
  set Vb := schemeTheoreticImageSubfunctor B S hS i with hVb
  have hVbcl : IsClosedSubspace B S hS Vb :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS i hQ
  have hp : IsProper B S hS (Vb.ι ≫ q) :=
    isProper_comp B S hS hVbcl.1 hQ hZ _ _
      (isProper_of_isClosedImmersion B S hS hVbcl.1 hQ _ hVbcl.2) ‹_›
  refine exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one B S hS
    hVbcl.1 hZ (Vb.ι ≫ q) hp hnoeth z hdim (Or.inr (Or.inr (Or.inr ?_)))
  refine hdense.mono ?_
  rintro _ ⟨w, rfl⟩
  set j := toSchemeTheoreticImage B S hS i
  have : IsIso (Subfunctor.toRange j) := hiso
  refine ⟨Subfunctor.range j, hrange, pointsMap B S hS _ (Subfunctor.toRange j) w, ?_, ?_⟩
  · rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
  · have heq : (Subfunctor.range j).ι ≫ Vb.ι ≫ q = inv (Subfunctor.toRange j) ≫ v := by
      have h1 : (Subfunctor.range j).ι = inv (Subfunctor.toRange j) ≫ j := by
        rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
      rw [h1, Category.assoc, ← Category.assoc j, toSchemeTheoreticImage_ι B S hS i, ‹i ≫ q = v›]
    rw [heq]
    exact isLocallyQuasiFinite_comp B S hS hrange.1 hV hZ _ _
      (isLocallyQuasiFinite_of_isEtale B S hS hV (isEtale_of_isIso B S hS _))
      (isLocallyQuasiFinite_of_isEtale B S hS hZ ‹_›)

/-- **The base case `d = 0` of the induction in the proof of Stacks 0ADD.** An étale chart
`v : h_V ⟶ Z` of an algebraic space whose fibres at the codimension-zero field points all have
rank `0` has empty image in `|Z|`.

If the image is nonempty then so is `V`, which then has a generic point `η` of an irreducible
component. Its image in `|Z|` has a local ring of dimension `0` (Stacks 0BAQ, via
`AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_exists_etale_genericPoint`), so the
fibre of `v` at a field-valued point over `η` is finite locally free of rank `0`, hence empty;
but the field-valued point itself gives a section of that fibre. -/
theorem notMem_range_pointsMap_of_chartRankAtCodimZeroLE_zero
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Z) (hv : IsEtale B S hS v)
    (h0 : ChartRankAtCodimZeroLE B S hS V v 0) (z : points B S hS Z) :
    z ∉ Set.range (pointsMap B S hS _ v) := by
  rintro ⟨x, -⟩
  obtain ⟨η, hη⟩ : ∃ η : (BigFppfOver.toScheme B S hS).obj V,
      η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj V) :=
    let c : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj V) :=
      ⟨_, irreducibleComponent_mem_irreducibleComponents (pointsToScheme B S hS V x)⟩
    ⟨(genericPoints.ofComponent c).1, (genericPoints.ofComponent c).2⟩
  obtain ⟨y, hy⟩ := surjective_pointsToScheme B S hS V η
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  have hvp := (isEtale_iff_presheaf_of_yoneda B S hS v).1 hv
  set ξ : yoneda.obj p.siteObject ⟶ Z := yoneda.map p.value ≫ v with hξ
  have hsq := hvp.rep.isPullback ξ
  have hdim : localRingDimension B S hS
      (pointsMap B S hS _ v (p.class B S hS (yoneda.obj V))) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hZ _).2
      ⟨V, v, η, hv, ⟨p, hy, rfl⟩, hη⟩
  obtain ⟨r, hr, hflf⟩ := h0 p.carrier p.field p.siteObject (Iso.refl _) ξ _
    (hvp.rep.snd ξ) (hvp.rep.fst ξ) hsq (by
      intro t
      let p₀ : FieldValuedPoint B S hS (yoneda.obj p.siteObject) :=
        { carrier := p.carrier, contained := p.contained, toBase := p.toBase,
          value := 𝟙 p.siteObject }
      have : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
        subsingleton_points_yoneda_of_isoSpec_toScheme B S hS p.siteObject (Iso.refl _)
      rw [Subsingleton.elim t (p₀.class B S hS _), hξ, pointsMap_comp_apply]
      convert hdim using 3
      change FieldValuedPoint.class B S hS _ (FieldValuedPoint.map B S hS _ _ p₀) = _
      congr 1)
  obtain rfl : r = 0 := Nat.le_zero.1 hr
  obtain ⟨s, -, hs⟩ := hsq.exists_lift (yoneda.map p.value) (𝟙 _) (by rw [Category.id_comp])
  obtain ⟨s', rfl⟩ := yoneda.map_surjective s
  exact (isEmpty_of_isFiniteLocallyFreeOfRank_zero_of_specTarget (K := p.carrier)
    ((BigFppfOver.toScheme B S hS).map (hvp.rep.snd ξ)) hflf).elim
      ((BigFppfOver.toScheme B S hS).map s' (IsLocalRing.closedPoint p.carrier))

/-- **A chart factors through `j` at a field point of codimension zero.** If `i : h_V ⟶ Q` is a
quasi-compact immersion and `ξ : h_T ⟶ Y` is a point of the scheme-theoretic image `Y` of `i`, with
`T ≅ Spec K` and `ξ` of codimension zero, then `ξ` factors through `h_V ⟶ Y`. -/
private theorem exists_yoneda_map_comp_toSchemeTheoreticImage_eq
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    {V : BigFppfOver B S hS} {i : yoneda.obj V ⟶ Q} (hi : IsImmersion B S hS i)
    (hiqc : IsQuasiCompact B S hS i) {K : Type u} [Field K] {T : BigFppfOver B S hS}
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ (schemeTheoreticImageSubfunctor B S hS i).toFunctor)
    (hcod : ∀ t, localRingDimension B S hS (pointsMap B S hS _ ξ t) = 0) :
    ∃ a : T ⟶ V, yoneda.map a ≫ toSchemeTheoreticImage B S hS i = ξ := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨-, -, hRopen, -, -⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hV hQ i hi
      (Or.inl hiqc)
  have hsub : Subsingleton (points B S hS (yoneda.obj T)) :=
    subsingleton_points_yoneda_of_isoSpec_toScheme B S hS T eT
  obtain ⟨t₀⟩ := nonempty_points_yoneda_of_isoSpec_toScheme B S hS T eT
  obtain ⟨pt, hpt⟩ :=
    exists_fieldValuedPoint_toSchemeTheoreticImage_of_localRingDimension_eq_zero B S hS i hV hQ
      hiqc _ (hcod t₀)
  have hmem : yonedaEquiv ξ ∈
      (Subfunctor.range (toSchemeTheoreticImage B S hS i)).obj (Opposite.op T) := by
    rw [eq_openSubspaceOfPoints_range_pointsMap_ι B S hS
        (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS i hQ).1 hRopen,
      mem_openSubspaceOfPoints_iff, Equiv.symm_apply_apply]
    rintro _ ⟨t, rfl⟩
    rw [hsub.elim t t₀, ← hpt]
    exact ⟨pointsMap B S hS _ (Subfunctor.toRange (toSchemeTheoreticImage B S hS i)) _, by
      rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, yonedaEquiv.injective (by rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map])⟩

/-- **Pullbacks along `θ` of two morphisms with complementary images on points have
complementary images on points.** -/
private theorem range_pointsMap_eq_compl_of_isPullback
    {X A G₁ G₂ F₁ F₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {θ : A ⟶ X} {g₁ : G₁ ⟶ X}
    {g₂ : G₂ ⟶ X} {a₁ : F₁ ⟶ G₁} {s₁ : F₁ ⟶ A} {a₂ : F₂ ⟶ G₂} {s₂ : F₂ ⟶ A}
    (h₁ : IsPullback a₁ s₁ g₁ θ) (h₂ : IsPullback a₂ s₂ g₂ θ)
    (hg : Set.range (pointsMap B S hS _ g₂) = (Set.range (pointsMap B S hS _ g₁))ᶜ) :
    Set.range (pointsMap B S hS _ s₂) = (Set.range (pointsMap B S hS _ s₁))ᶜ := by
  ext ε
  refine ⟨?_, fun hε => ?_⟩
  · rintro ⟨b, rfl⟩ ⟨c, hc⟩
    have h : pointsMap B S hS _ θ (pointsMap B S hS _ s₂ b) ∈
        Set.range (pointsMap B S hS _ g₂) :=
      ⟨pointsMap B S hS _ a₂ b, by rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, h₂.w]⟩
    rw [hg, ← hc, ← pointsMap_comp_apply, ← h₁.w, pointsMap_comp_apply] at h
    exact h ⟨_, rfl⟩
  · by_cases hε₁ : pointsMap B S hS _ θ ε ∈ Set.range (pointsMap B S hS _ g₁)
    · obtain ⟨c, hc⟩ := hε₁
      obtain ⟨ζ, -, hζ⟩ := exists_points_of_isPullback B S hS h₁ c ε hc
      exact (hε ⟨ζ, hζ⟩).elim
    · rw [← Set.mem_compl_iff, ← hg] at hε₁
      obtain ⟨c, hc⟩ := hε₁
      obtain ⟨ζ, -, hζ⟩ := exists_points_of_isPullback B S hS h₂ c ε hc
      exact ⟨ζ, hζ⟩

/-- **Removing a section from a fibre over a field lowers its rank.** Let `qV : V_f ⟶ T` be finite
locally free of rank `r ≤ d + 1`, with `T ≅ Spec K`, and let `σ : T ⟶ V_f` and `μ : W_f ⟶ V_f` be
open immersions with complementary images on points, `σ` a section of `qV`. Then `μ ≫ qV` is
finite locally free of rank at most `d`. -/
private theorem exists_le_isFiniteLocallyFreeOfRank_of_range_eq_compl {K : Type u} [Field K]
    {T Vf Wf : BigFppfOver B S hS}
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K)) {qV : Vf ⟶ T}
    {r d : ℕ} (hr : r ≤ d + 1)
    (hflf : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map qV) r)
    (σ : T ⟶ Vf) (μ : Wf ⟶ Vf)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map σ)]
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map μ)]
    {qf : Wf ⟶ T} (hσq : σ ≫ qV = 𝟙 T) (hμq : μ ≫ qV = qf)
    (hpts : Set.range (pointsMap B S hS _ (yoneda.map μ)) =
      (Set.range (pointsMap B S hS _ (yoneda.map σ)))ᶜ) :
    ∃ s : ℕ, s ≤ d ∧ IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map qf) s := by
  have hsets : Set.range ((BigFppfOver.toScheme B S hS).map μ) =
      (Set.range ((BigFppfOver.toScheme B S hS).map σ))ᶜ := by
    rw [← image_pointsToScheme_range B S hS μ, ← image_pointsToScheme_range B S hS σ, hpts,
      Set.image_compl_eq (bijective_pointsToScheme B S hS Vf)]
  have hcompl := (isCompl_opensRange_iff_range_eq_compl _ _).2 hsets
  -- the rank count
  obtain ⟨s, hs, hsflf⟩ := exists_add_one_eq_and_isFiniteLocallyFreeOfRank_of_isCompl_section
    _ eT r hflf _ _ hcompl (by rw [← Functor.map_comp, hσq, CategoryTheory.Functor.map_id])
  exact ⟨s, by omega, by rwa [← hμq, Functor.map_comp]⟩

/-- **The graph of an étale morphism over a separated morphism is open and closed.** Let
`fst : h_P ⟶ Y` and `snd : P ⟶ V` form a pullback of a separated `p : Y ⟶ Z` along `v = j ≫ p`,
with `j` étale. The graph of `j` is a section `γ : V ⟶ P` of `snd` with `γ ≫ fst = j`, which is an
open and a closed immersion. -/
private theorem exists_isOpenImmersion_isClosedImmersion_graph
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {V P : BigFppfOver B S hS} {j : yoneda.obj V ⟶ Y}
    {p : Y ⟶ Z} {v : yoneda.obj V ⟶ Z} (hjp : j ≫ p = v) (hj : IsEtale B S hS j)
    (hp : IsSeparated B S hS p) {fst : yoneda.obj P ⟶ Y} {snd : P ⟶ V}
    (hsq : IsPullback fst (yoneda.map snd) p v) (hfst : IsEtale B S hS fst) :
    ∃ γ : V ⟶ P, yoneda.map γ ≫ fst = j ∧ IsOpenImmersion B S hS (yoneda.map γ) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map γ) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map γ) := by
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hP : IsAlgebraicSpace B S hS (yoneda.obj P) := isAlgebraicSpace_yoneda B S hS P
  obtain ⟨γ, hγ⟩ := yoneda.map_surjective
    (hsq.lift j (𝟙 _) (by rw [Category.id_comp, hjp]))
  have hγfst : yoneda.map γ ≫ fst = j := by rw [hγ, IsPullback.lift_fst]
  have hγsnd : yoneda.map γ ≫ yoneda.map snd = 𝟙 _ := by rw [hγ, IsPullback.lift_snd]
  have hΓopen : IsOpenImmersion B S hS (yoneda.map γ) :=
    isOpenImmersion_of_isEtale_of_mono B S hS _ hV hP
      (isEtale_of_isEtale_over B S hS hV hP hY (yoneda.map γ) j fst hj hfst hγfst)
      (mono_of_mono_fac hγsnd)
  have hsq' : IsPullback (yoneda.map snd) fst (j ≫ p) p := by
    rw [hjp]
    exact hsq.flip
  have hgraph : graph B S hS j p ≫ hsq'.isoPullback.inv = yoneda.map γ := by
    rw [Iso.comp_inv_eq]
    refine pullback.hom_ext ?_ ?_
    · rw [graph_comp_fst, Category.assoc, IsPullback.isoPullback_hom_fst, hγsnd]
    · rw [graph_comp_snd, Category.assoc, IsPullback.isoPullback_hom_snd, hγfst]
  have hΓcl : IsClosedImmersion B S hS (yoneda.map γ) := by
    rw [← hgraph]
    exact MorphismProperty.RespectsIso.postcomp _ _ _
      (isClosedImmersion_graph_of_isSeparated B S hS j p hp)
  exact ⟨γ, hγfst, hΓopen, (presheaf_yoneda_map_iff B S hS inferInstance γ).1 hΓopen,
    (presheaf_yoneda_map_iff B S hS inferInstance γ).1 hΓcl⟩

/-- **The complement of an open and closed subscheme of a quasi-compact scheme.** If
`γ : V ⟶ P` is an open and closed immersion of schemes with `P` quasi-compact, there is an open
immersion `ιW : W ⟶ P` with `W` quasi-compact whose image on points is the complement of that of
`γ`. -/
private theorem exists_isOpenImmersion_range_eq_compl {V P : BigFppfOver B S hS}
    (hPc : CompactSpace ((BigFppfOver.toScheme B S hS).obj P)) (γ : V ⟶ P)
    (hγo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map γ))
    (hγc : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map γ)) :
    ∃ (W : BigFppfOver B S hS) (ιW : W ⟶ P),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
      IsOpenImmersion B S hS (yoneda.map ιW) ∧
      Set.range (pointsMap B S hS _ (yoneda.map ιW)) =
        (Set.range (pointsMap B S hS _ (yoneda.map γ)))ᶜ := by
  let Wo : ((BigFppfOver.toScheme B S hS).obj P).Opens :=
    ⟨(Set.range ((BigFppfOver.toScheme B S hS).map γ))ᶜ,
      ((BigFppfOver.toScheme B S hS).map γ).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hιWs : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (BigFppfOver.openSubHom B S hS P Wo)) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion Wo.ι)
  have hcl : IsClosed (Wo : Set ((BigFppfOver.toScheme B S hS).obj P)) :=
    isClosed_compl_iff.2 hγo.base_open.isOpen_range
  refine ⟨BigFppfOver.openSubObj B S hS P Wo, BigFppfOver.openSubHom B S hS P Wo,
    isCompact_iff_compactSpace.1 hcl.isCompact,
    (presheaf_yoneda_map_iff B S hS inferInstance _).2 hιWs, ?_⟩
  -- the points of `P` off the graph are the points of `W`
  have hrng : ∀ {U : BigFppfOver B S hS} (h : U ⟶ P),
      Set.range (pointsMap B S hS _ (yoneda.map h)) =
        pointsToScheme B S hS P ⁻¹' Set.range ((BigFppfOver.toScheme B S hS).map h) := fun h => by
    rw [← image_pointsToScheme_range B S hS h,
      Set.preimage_image_eq _ (injective_pointsToScheme B S hS P)]
  rw [hrng, hrng, ← Set.preimage_compl]
  congr 1
  exact Scheme.Opens.range_ι Wo

/-- **The base change of an immersion `i : h_V ⟶ Q` along a pullback square over `V` is an
immersion.** If `fst, snd` form a pullback of `p : Y ⟶ Z` along `v = i ≫ q`, the induced
morphism `h_P ⟶ Y ×_Z Q` is an immersion. -/
private theorem isImmersion_pullback_lift_of_isPullback
    {Y Z Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V P : BigFppfOver B S hS} {p : Y ⟶ Z}
    {q : Q ⟶ Z} {v : yoneda.obj V ⟶ Z} {i : yoneda.obj V ⟶ Q} (hi : IsImmersion B S hS i)
    (hiq : i ≫ q = v) {fst : yoneda.obj P ⟶ Y} {snd : P ⟶ V}
    (hsq : IsPullback fst (yoneda.map snd) p v) :
    IsImmersion B S hS
      (pullback.lift (f := p) (g := q) fst (yoneda.map snd ≫ i)
        (by rw [Category.assoc, hiq, hsq.w])) := by
  have hnsq : IsPullback (pullback.lift (f := p) (g := q) fst (yoneda.map snd ≫ i)
      (by rw [Category.assoc, hiq, hsq.w])) (yoneda.map snd) (pullback.snd p q) i := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p q)
    rwa [pullback.lift_fst, hiq]
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hnsq.flip hi

/-- **Removing the graph from the fibre lowers its rank.** Let `θ, qV` form a pullback of
`fst : h_P ⟶ Y` along a point `ξ : h_T ⟶ Y` with `T ≅ Spec K`, the fibre `qV` finite locally free
of rank `r ≤ d + 1`. Suppose `ξ` factors as `a ≫ j` through a monomorphism `j = γ ≫ fst`, with
`γ` an open immersion, and `ιW` is an open immersion whose image on points is the complement of
that of `γ`. Then the fibre of `ιW ≫ fst` at `ξ` is finite locally free of rank at most `d`. -/
private theorem exists_le_isFiniteLocallyFreeOfRank_of_isPullback_compl
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {K : Type u} [Field K]
    {V P W T Vf Wf : BigFppfOver B S hS}
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    {fst : yoneda.obj P ⟶ Y} {j : yoneda.obj V ⟶ Y} [Mono j] {γ : V ⟶ P}
    (hγfst : yoneda.map γ ≫ fst = j) (hΓopen : IsOpenImmersion B S hS (yoneda.map γ))
    {ιW : W ⟶ P} (hιWo : IsOpenImmersion B S hS (yoneda.map ιW))
    (hWrange : Set.range (pointsMap B S hS _ (yoneda.map ιW)) =
      (Set.range (pointsMap B S hS _ (yoneda.map γ)))ᶜ)
    {ξ : yoneda.obj T ⟶ Y} {a : T ⟶ V} (hξ : yoneda.map a ≫ j = ξ)
    {θ : yoneda.obj Vf ⟶ yoneda.obj P} {qV : Vf ⟶ T} (hlow : IsPullback θ (yoneda.map qV) fst ξ)
    {r d : ℕ} (hr : r ≤ d + 1)
    (hflf : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map qV) r)
    {iW : yoneda.obj Wf ⟶ yoneda.obj W} {qf : Wf ⟶ T}
    (hsqW : IsPullback iW (yoneda.map qf) (yoneda.map ιW ≫ fst) ξ) :
    ∃ s : ℕ, s ≤ d ∧ IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map qf) s := by
  -- an open immersion into `P` whose pullback to the fibre `V_f` is open over `T`
  have key : ∀ {U A : BigFppfOver B S hS} (o : A ⟶ P) (ho : IsOpenImmersion B S hS (yoneda.map o))
      (c : yoneda.obj U ⟶ yoneda.obj A) (g : U ⟶ T),
      IsPullback c (yoneda.map g) (yoneda.map o ≫ fst) ξ →
      ∃ m : U ⟶ Vf, m ≫ qV = g ∧ IsPullback c (yoneda.map m) (yoneda.map o) θ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map m) := by
    intro U A o ho c g hc
    obtain ⟨m, hm⟩ := yoneda.map_surjective (hlow.lift (c ≫ yoneda.map o) (yoneda.map g)
      (by rw [Category.assoc, hc.w]))
    have hup : IsPullback c (yoneda.map m) (yoneda.map o) θ :=
      IsPullback.of_bot (by rwa [hm, IsPullback.lift_snd]) (by rw [hm, IsPullback.lift_fst]) hlow
    exact ⟨m, yoneda.map_injective (by rw [Functor.map_comp, hm, IsPullback.lift_snd]), hup,
      (presheaf_yoneda_map_iff B S hS inferInstance m).1
        ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hup ho)⟩
  -- the graph contributes a section of that fibre, and `W` the rest of it
  obtain ⟨σ, hσq, hupΓ, hσo⟩ := key γ hΓopen (yoneda.map a) (𝟙 T) (by
    rw [CategoryTheory.Functor.map_id, hγfst, ← hξ]
    exact IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]⟩)
  obtain ⟨μ, hμq, hupW, hμo⟩ := key ιW hιWo iW qf hsqW
  -- on points, the two pieces are complementary
  exact exists_le_isFiniteLocallyFreeOfRank_of_range_eq_compl B S hS eT hr hflf σ μ hσq hμq
    (range_pointsMap_eq_compl_of_isPullback B S hS hupΓ hupW hWrange)

/-- **The complement of the graph lowers the rank at the codimension-zero points.** Let
`i : h_V ⟶ Q` be a quasi-compact immersion, `j : h_V ⟶ Y` the open immersion into its
scheme-theoretic image `Y`, and `fst, snd` a pullback of `p : Y ⟶ Z` along the étale
`v = j ≫ p`. If `γ` is the graph of `j` and `ιW` is an open immersion whose image on points is the
complement of that of `γ`, then rank at most `d + 1` for `v` at the codimension-zero field points
gives rank at most `d` for `ιW ≫ fst`. -/
private theorem chartRankAtCodimZeroLE_of_range_eq_compl_graph
    {Z Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hQ : IsAlgebraicSpace B S hS Q) {V P W : BigFppfOver B S hS} {i : yoneda.obj V ⟶ Q}
    (hi : IsImmersion B S hS i) (hiqc : IsQuasiCompact B S hS i)
    {v : yoneda.obj V ⟶ Z} (hv : IsEtale B S hS v)
    {p : (schemeTheoreticImageSubfunctor B S hS i).toFunctor ⟶ Z}
    (hjp : toSchemeTheoreticImage B S hS i ≫ p = v)
    {fst : yoneda.obj P ⟶ (schemeTheoreticImageSubfunctor B S hS i).toFunctor} {snd : P ⟶ V}
    (hsq : IsPullback fst (yoneda.map snd) p v) {γ : V ⟶ P}
    (hγfst : yoneda.map γ ≫ fst = toSchemeTheoreticImage B S hS i)
    (hΓopen : IsOpenImmersion B S hS (yoneda.map γ)) {ιW : W ⟶ P}
    (hιWo : IsOpenImmersion B S hS (yoneda.map ιW))
    (hWrange : Set.range (pointsMap B S hS _ (yoneda.map ιW)) =
      (Set.range (pointsMap B S hS _ (yoneda.map γ)))ᶜ)
    (d : ℕ) (hd : ChartRankAtCodimZeroLE B S hS V v (d + 1)) :
    ChartRankAtCodimZeroLE B S hS W (yoneda.map ιW ≫ fst) d := by
  intro K hK T eT ξ Wf qf iW hsqW hcod
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨hjopen, -, -, -, -⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hV hQ i hi
      (Or.inl hiqc)
  have : Mono (toSchemeTheoreticImage B S hS i) := mono_of_isOpenImmersion B S hS _ hjopen
  -- `ξ` lands in the image of `j`, and so factors through it
  obtain ⟨a, hξ⟩ := exists_yoneda_map_comp_toSchemeTheoreticImage_eq B S hS hQ hi hiqc eT ξ hcod
  -- the fibre of `v` over `ξ ≫ p`, of rank at most `d + 1`
  have hvr := ((isEtale_iff_presheaf_of_yoneda B S hS v).1 hv).rep
  set Vf := hvr.pullback (ξ ≫ p)
  set qV : Vf ⟶ T := hvr.snd (ξ ≫ p)
  set iV : yoneda.obj Vf ⟶ yoneda.obj V := hvr.fst (ξ ≫ p)
  have hsqV : IsPullback iV (yoneda.map qV) v (ξ ≫ p) := hvr.isPullback (ξ ≫ p)
  obtain ⟨r, hr, hflf⟩ := hd K hK T eT (ξ ≫ p) Vf qV iV hsqV (by
    intro t
    rw [← hξ, Category.assoc, hjp, pointsMap_comp_apply,
      localRingDimension_pointsMap_of_etale B S hS hV hZ v hv,
      ← localRingDimension_pointsMap_of_etale B S hS hV
        (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS i hQ).1 _
        (isEtale_of_isOpenImmersion B S hS hjopen), ← pointsMap_comp_apply, hξ]
    exact hcod t)
  -- the fibre of `P ⟶ Y` over `ξ` is that fibre of `v`
  set θ : yoneda.obj Vf ⟶ yoneda.obj P := hsq.lift (yoneda.map qV ≫ ξ) iV
    (by rw [Category.assoc, ← hsqV.w]) with hθ
  have hlow : IsPullback θ (yoneda.map qV) fst ξ :=
    IsPullback.of_right (by rwa [hθ, IsPullback.lift_snd])
      (IsPullback.lift_fst _ _ _ _) hsq.flip
  exact exists_le_isFiniteLocallyFreeOfRank_of_isPullback_compl B S hS eT hγfst hΓopen hιWo
    hWrange hξ hlow hr hflf hsqW

/-- **The inductive step of the proof of Stacks 0ADD.** Let `v : h_V ⟶ Z` be an étale chart of
a separated algebraic space with quasi-compact source, immersed by `i` over `Z` in a proper
representable morphism `q : Q ⟶ Z`. Write `Y` for the scheme-theoretic image of `i`,
`p : Y ⟶ Z` for its morphism to `Z` and `j : h_V ⟶ Y` for the canonical open immersion. There
is an étale chart `w : h_W ⟶ Y` with quasi-compact source, immersed over `Y` in a proper
representable morphism `q' : Q' ⟶ Y`, such that

* every point of `Y` outside the image of `j` lying over the image of `v` is in the image of `w`;
* if `v` has rank at most `d + 1` at the codimension-zero field points, then `w` has rank at
  most `d` there.

`W` is the complement of the graph of `j` in the scheme `h_V ×_Z Y`, which is open and closed
(closed by Stacks 03KO since `p` is separated, open since it is an étale monomorphism), `w` is the
restriction of the projection to `Y`, and `Q' = Y ×_Z Q` with `W` immersed by the base change
of `i`. At a codimension-zero field point `ξ` of `Y`, `ξ` factors through `j`, so the fibre of
`h_V ×_Z Y` is the disjoint union of the fibre of `W` and a section coming from the graph, and
`AlgebraicGeometry.exists_add_one_eq_and_isFiniteLocallyFreeOfRank_of_isCompl` compares the
ranks. -/
theorem exists_chart_of_complement_graph
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal Z)
    (V : BigFppfOver B S hS) (hVc : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (v : yoneda.obj V ⟶ Z) (hv : IsEtale B S hS v)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ Z) (hq : IsProper B S hS q) (hqr : yoneda.relativelyRepresentable q)
    (i : yoneda.obj V ⟶ Q) (hi : IsImmersion B S hS i) (hiq : i ≫ q = v) :
    ∃ (W : BigFppfOver B S hS) (_ : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
      (w : yoneda.obj W ⟶ (schemeTheoreticImageSubfunctor B S hS i).toFunctor)
      (Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Q')
      (q' : Q' ⟶ (schemeTheoreticImageSubfunctor B S hS i).toFunctor)
      (i' : yoneda.obj W ⟶ Q'),
      IsEtale B S hS w ∧ IsProper B S hS q' ∧ yoneda.relativelyRepresentable q' ∧
      IsImmersion B S hS i' ∧ i' ≫ q' = w ∧
      (∀ y : points B S hS (schemeTheoreticImageSubfunctor B S hS i).toFunctor,
        y ∉ Set.range (pointsMap B S hS _ (toSchemeTheoreticImage B S hS i)) →
        pointsMap B S hS _ ((schemeTheoreticImageSubfunctor B S hS i).ι ≫ q) y ∈
          Set.range (pointsMap B S hS _ v) →
        y ∈ Set.range (pointsMap B S hS _ w)) ∧
      (∀ d : ℕ, ChartRankAtCodimZeroLE B S hS V v (d + 1) →
        ChartRankAtCodimZeroLE B S hS W w d) := by
  classical
  -- the scheme-theoretic image `Y` of the chart in `Q`, and the chart's open immersion into it
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hiqc : IsQuasiCompact B S hS i :=
    isQuasiCompact_of_compactSpace_of_isProper B S hS hsep hQ hq hVc i
  obtain ⟨hjopen, -, -, -, -⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hV hQ i hi
      (Or.inl hiqc)
  set Vb := schemeTheoreticImageSubfunctor B S hS i
  set j := toSchemeTheoreticImage B S hS i with hj
  have hVbcl : IsClosedSubspace B S hS Vb :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS i hQ
  set p := Vb.ι ≫ q with hpdef
  have hjp : j ≫ p = v := by
    rw [hpdef, ← Category.assoc, hj, toSchemeTheoreticImage_ι B S hS i, hiq]
  have hp : IsProper B S hS p :=
    isProper_comp B S hS hVbcl.1 hQ hZ _ _ (isProper_of_isClosedImmersion B S hS hVbcl.1 hQ _
      hVbcl.2) hq
  have hpr : yoneda.relativelyRepresentable p :=
    MorphismProperty.comp_mem _ _ _ hVbcl.2.rep hqr
  -- the fibre product `P = Y ×_Z V`, represented by a scheme
  set P := hpr.pullback v
  set fst : yoneda.obj P ⟶ Vb.toFunctor := hpr.fst v
  set snd : P ⟶ V := hpr.snd v
  have hsq : IsPullback fst (yoneda.map snd) p v := hpr.isPullback v
  have hfst_et : IsEtale B S hS fst := isEtale_of_isPullback_yoneda B S hS hsq.flip hv
  -- the graph of `j`, a section of `P ⟶ V` which is open and closed
  obtain ⟨γ, hγfst, hΓopen, hγo, hγc⟩ := exists_isOpenImmersion_isClosedImmersion_graph B S hS
    hVbcl.1 hjp (isEtale_of_isOpenImmersion B S hS hjopen) hp.1 hsq hfst_et
  have hPc : CompactSpace ((BigFppfOver.toScheme B S hS).obj P) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS hsq.flip.isoPullback.symm
        (hp.2.1.2 (yoneda.obj V) hV (isQuasiCompactSpace_yoneda B S hS V hVc) v))
  -- its complement `W`, which is quasi-compact
  obtain ⟨W, ιW, hWc, hιWo, hWrange⟩ := exists_isOpenImmersion_range_eq_compl B S hS hPc γ hγo hγc
  -- the proper representable morphism `Q' ⟶ Y` and the immersion of `W` into it
  refine ⟨W, hWc, yoneda.map ιW ≫ fst, pullback p q,
    isAlgebraicSpace_pullback B S hS p q hVbcl.1 hQ hZ, pullback.fst p q,
    yoneda.map ιW ≫ pullback.lift fst (yoneda.map snd ≫ i) (by rw [Category.assoc, hiq, hsq.w]),
    isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hιWo) hfst_et,
    isProper_pullback_fst B S hS hQ hZ hVbcl.1 q p hq, MorphismProperty.pullback_fst _ _ hqr,
    isImmersion_comp B S hS _ _ (isImmersion_of_isOpenImmersion B S hS hιWo)
      (isImmersion_pullback_lift_of_isPullback B S hS hi hiq hsq),
    by rw [Category.assoc, pullback.lift_fst], ?_,
    chartRankAtCodimZeroLE_of_range_eq_compl_graph B S hS hZ hQ hi hiqc hv hjp hsq hγfst hΓopen
      hιWo hWrange⟩
  -- (a)
  intro y hyj ⟨x, hx⟩
  obtain ⟨π, hπ₁, -⟩ := exists_points_of_isPullback B S hS hsq y x hx.symm
  have hπ : π ∈ Set.range (pointsMap B S hS _ (yoneda.map ιW)) := by
    rw [hWrange]
    rintro ⟨a, rfl⟩
    exact hyj ⟨a, by rw [← hπ₁, ← pointsMap_comp_apply, hγfst]⟩
  obtain ⟨b, rfl⟩ := hπ
  exact ⟨b, by rw [pointsMap_comp_apply, hπ₁]⟩

/-- **A finite morphism whose fibre over `z` is covered by representable opens is
representable over a neighbourhood of `z`.** This is a step of the proof of Stacks 0ADD.

Let `p : Y ⟶ Z` be a finite morphism of algebraic spaces and `z ∈ |Z|` a point such that every
point of `|Y|` over `z` lies in a representable open subspace of `Y`. Then there is an open
subspace `Z₂ ⊆ Z` containing `z` such that `Y ×_Z Z₂` is representable.

All those open subspaces lie in the schematic locus `L` of `Y` (Stacks 03JH, unconditional as
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`).
The complement `C` of `|L|` is closed, so `p(C)` is closed because a finite morphism is
universally closed, and `z ∉ p(C)`. The open subspace `Z₂` with point set `|Z| ∖ p(C)` (Stacks
03BZ) has inverse image in `Y` an open subspace contained in `L`, hence representable as an
open subspace of a scheme. -/
theorem exists_isOpenSubspace_isRepresentable_pullback_of_isFinite
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (p : Y ⟶ Z) (hp : IsFinite B S hS p)
    (z : points B S hS Z)
    (hfib : ∀ y : points B S hS Y, pointsMap B S hS Y p y = z →
      ∃ G : Subfunctor Y, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
        y ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    ∃ Z₂ : Subfunctor Z, IsOpenSubspace B S hS Z₂ ∧
      z ∈ Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι) ∧
      (pullback p Z₂.ι).IsRepresentable := by
  obtain ⟨hLopen, hLrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hY
  set L := schematicLocus B S hS Y
  set C : Set (points B S hS Y) := (Set.range (pointsMap B S hS L.toFunctor L.ι))ᶜ
  have hCcl : IsClosed C :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS L.ι hLopen.2).isClosed_compl
  have hpC : IsClosed (pointsMap B S hS Y p '' C) :=
    isClosed_of_universallyClosed B S hS hZ p (universallyClosed_of_isFinite B S hS hY hZ hp) C
      hCcl
  set W : Set (points B S hS Z) := (pointsMap B S hS Y p '' C)ᶜ
  have hzW : z ∈ W := by
    rintro ⟨y, hyC, hyz⟩
    obtain ⟨G, hG, hGrep, hyG⟩ := hfib y hyz
    have hGL : G ≤ L := le_schematicLocus B S hS Y G hG hGrep
    refine hyC ?_
    obtain ⟨g, rfl⟩ := hyG
    refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe hGL) g, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  set Z₂ := openSubspaceOfPoints B S hS Z W
  have hZ₂open : IsOpenSubspace B S hS Z₂ :=
    isOpenSubspace_openSubspaceOfPoints B S hS hZ W hpC.isOpen_compl
  have hZ₂range : Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  set G := Z₂.preimage p
  have hGopen : IsOpenSubspace B S hS G := isOpenSubspace_preimage B S hS p Z₂ hZ hY hZ₂open
  have hGL : G ≤ L := by
    refine le_of_range_pointsMap_ι_subset B S hS hLopen ?_
    rw [pointsRange_preimage, hZ₂range]
    intro y hy
    by_contra hyL
    exact hy ⟨y, hyL, rfl⟩
  set N := G.preimage L.ι
  have hNopen : IsOpenSubspace B S hS N :=
    isOpenSubspace_preimage B S hS L.ι G hY hLopen.1 hGopen
  have hNrep : N.toFunctor.IsRepresentable :=
    isRepresentable_of_isOpenSubspace B S hS hLrep N hNopen
  have hsq₁ : IsPullback (G.fromPreimage L.ι) N.ι G.ι L.ι := Subfunctor.isPullback_preimage L.ι G
  have hsq₂ : IsPullback (𝟙 G.toFunctor) (Subfunctor.homOfLe hGL) G.ι L.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, Subfunctor.homOfLe_ι]⟩
  have e₁ : N.toFunctor ≅ G.toFunctor := hsq₁.isoIsPullback _ _ hsq₂
  have e₂ : G.toFunctor ≅ pullback p Z₂.ι := (Subfunctor.isPullback_preimage p Z₂).flip.isoPullback
  refine ⟨Z₂, hZ₂open, hZ₂range ▸ hzW, ?_⟩
  exact isRepresentable_of_natIso _ (e₁ ≪≫ e₂)

end AlgebraicGeometry.Space
