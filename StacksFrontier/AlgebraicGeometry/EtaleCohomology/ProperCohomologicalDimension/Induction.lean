module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.LerayVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Dimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.GeometricFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Morphisms.GraphClosure
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.FiniteFibres
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of torsion sheaves along proper morphisms: the induction

This file proves, by induction on the dimension, the absolute form of [Stacks, Tag 095U]: for a
proper scheme `X` of dimension at most `N` over an algebraically closed field and a torsion
abelian sheaf `G` on `X_étale`, `H^q(X, G) = 0` for `q > 2N`. The proper base change theorem
([Stacks, Tag 095T]) and the cohomology of curves ([Stacks, Tag 03SC]) enter as the hypotheses
`h095T` and `h03SC`.

## Main results

* `isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiber_le_zero`: the case of fibres
  of dimension `0`: higher direct images along a proper morphism with zero-dimensional fibres
  vanish.
* `subsingleton_sheafH_of_topologicalKrullDim_le_one`: the case of curves, from
  [Stacks, Tag 03SC].
* `subsingleton_sheafH_of_isIntegral_of_induction`: the induction step for integral schemes.
* `subsingleton_sheafH_of_isProper_of_induction`: the induction step in general.
* `subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve`: the absolute form of
  [Stacks, Tag 095U], granted the case of curves.
* `subsingleton_sheafH_of_isProper_of_isAlgClosed`: the absolute form of [Stacks, Tag 095U].

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 0EW3](https://stacks.math.columbia.edu/tag/0EW3)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- **The case of fibres of dimension zero** of [Stacks, Tag 095U]. The higher direct images
along a proper morphism all of whose fibres have dimension at most `0` vanish. -/
@[sga "4½ Th_finitude 1.3" "special case"]
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiber_le_zero
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p]
    (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ (0 : ℕ))
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) (hq : 2 * 0 < q) :
    IsZero (((etaleAbelianDirectImage.{u, v} p).rightDerived q).obj F) := by
  have hfin : ∀ t : T, ((p : S → T) ⁻¹' {t}).Finite := by
    intro t
    have : IsLocallyNoetherian (p.fiber t) :=
      LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField t)
    have : AlgebraicGeometry.IsNoetherian (p.fiber t) := ⟨⟩
    have h0 : topologicalKrullDim (p.fiber t) ≤ 0 := by simpa using hN t
    have hf : (Set.univ : Set (p.fiber t)).Finite :=
      Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero h0
    have : Finite (p.fiber t) := Set.finite_univ_iff.1 hf
    exact Set.finite_coe_iff.1 (Finite.of_equiv _ (p.fiberHomeo t).toEquiv)
  have : IsFinite p :=
    ((IsFinite.tfae_isProper_finite_preimage_singleton p).out 1 2).2
      (⟨inferInstance, hfin⟩ : IsProper p ∧ ∀ s, ((p : S → T) ⁻¹' {s}).Finite)
  exact isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom.{u, v} p F q (by omega)

/-- Étale cohomology of a sheaf on the empty scheme vanishes: every abelian sheaf on its small
étale site is zero. -/
theorem subsingleton_sheafH_of_isEmpty_sheafUniverse {X : Scheme.{u}} [IsEmpty X]
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) :=
  Sheaf.subsingleton_H_of_isZero (isZero_of_forall_isZero_sections.{u, v} G fun V ↦
    isZero_sections_of_isEmpty.{u, v} G V ⟨fun x ↦ isEmptyElim (show X from V.hom x)⟩) q

/-- **The case of curves** of [Stacks, Tag 095U], from [Stacks, Tag 03SC] (`h03SC`): for `X`
proper over an algebraically closed field with `dim X ≤ 1`, `H^q(X, G) = 0` for every torsion
abelian sheaf `G` and every `q > 2`. -/
theorem subsingleton_sheafH_of_topologicalKrullDim_le_one
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h03SC : CurveTorsionCohomologyStatement.{u, v}) (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (π : X ⟶ Spec (.of k)) [IsProper π]
    (hX : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ) (hq : 2 * 1 < q) :
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) :=
  (h03SC π (by exact_mod_cast hX) G hG).1 q (by omega)

/-- A scheme proper over a field is Noetherian. -/
private theorem isNoetherian_of_isProper_over_field {k : Type u} [Field k] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of k)) [IsProper π] : AlgebraicGeometry.IsNoetherian Y :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace π
  ⟨⟩

/-- If `a + 1 ≤ N` and `1 ≤ N`, then `a ≤ N - 1` in `WithBot ℕ∞`. -/
private theorem le_natCast_pred_of_add_one_le {a : WithBot ℕ∞} {N : ℕ} (hN : 1 ≤ N)
    (h : a + 1 ≤ (N : WithBot ℕ∞)) : a ≤ ((N - 1 : ℕ) : WithBot ℕ∞) :=
  le_natCast_of_add_one_le (by rwa [show N - 1 + 1 = N by omega])

/-- A closed subscheme of an irreducible Noetherian scheme of dimension at most `N`, which is not
everything, has dimension at most `N - 1`. -/
private theorem topologicalKrullDim_le_pred_of_not_surjective {E W : Scheme.{u}} (e : E ⟶ W)
    [IsClosedImmersion e] [IrreducibleSpace W] [NoetherianSpace W] {N : ℕ} (hN : 1 ≤ N)
    (hW : topologicalKrullDim W ≤ N) (he : ¬ Function.Surjective e) :
    topologicalKrullDim E ≤ ((N - 1 : ℕ) : WithBot ℕ∞) :=
  le_natCast_pred_of_add_one_le hN
    ((topologicalKrullDim_add_one_le_of_isClosedImmersion e he).trans hW)

/-- **The integral case of the induction step** of [Stacks, Tag 095U]. Let `N ≥ 2` and suppose
the vanishing `H^q(Y, G) = 0` for `q > 2M` is known for every proper scheme `Y` of dimension at
most `M` over an algebraically closed field, for every `1 ≤ M < N`. Let `X` be an integral proper
scheme of dimension at most `N` over an algebraically closed field `k`. Then `H^q(X, G) = 0` for
every torsion abelian sheaf `G` and every `q > 2N`. -/
theorem subsingleton_sheafH_of_isIntegral_of_induction
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, v} p)
    (N : ℕ) (hN : 2 ≤ N)
    (IH : ∀ M : ℕ, 1 ≤ M → M < N → ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
      (π : Y ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim Y ≤ M →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G →
        ∀ q : ℕ, 2 * M < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q))
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (π : X ⟶ Spec (.of k)) [IsProper π]
    [IsIntegral X] (hX : topologicalKrullDim X ≤ N)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ) (hq : 2 * N < q) :
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
  have hN1 : 1 ≤ N - 1 := by omega
  have hNN : N - 1 < N := by omega
  by_cases hlow : topologicalKrullDim X ≤ ((N - 1 : ℕ) : WithBot ℕ∞)
  · exact IH (N - 1) hN1 hNN k X π hlow G hG q (by omega)
  have hdim1 : 1 ≤ topologicalKrullDim X :=
    ((show ((1 : ℕ) : WithBot ℕ∞) ≤ ((N - 1 : ℕ) : WithBot ℕ∞) by exact_mod_cast hN1).trans_lt
      (lt_of_not_ge hlow)).le
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = p + 1 := ⟨q - 1, by omega⟩
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProper_over_field π
  obtain ⟨U, ψ, hU, hψ, hψover⟩ :=
    Stacks.Chow.exists_isDominant_partialMap_to_projectiveLine π hdim1
  have : IsDominant ψ := hψ
  let qP : projectiveLine k ⟶ Spec (.of k) := projectiveLine k ↘ Spec (.of k)
  let X' := OpenGraphClosure.closure π qP U ψ hψover
  let b : X' ⟶ X := OpenGraphClosure.projection π qP U ψ hψover
  let f : X' ⟶ projectiveLine k := OpenGraphClosure.secondProjection π qP U ψ hψover
  have : IsProper b := OpenGraphClosure.isProper_projection π qP U ψ hψover
  have : IsProper f := OpenGraphClosure.isProper_secondProjection π qP U ψ hψover
  have : IsIntegral X' := OpenGraphClosure.isIntegral_closure π qP U ψ hψover hU
  have : IsDominant f := OpenGraphClosure.isDominant_secondProjection π qP U ψ hψover
  have hbU : IsIso (pullback.snd b U.ι) :=
    OpenGraphClosure.isIso_projection_restrict π qP U ψ hψover
  have : IsProper (b ≫ π) := inferInstance
  have : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isProper_over_field (b ≫ π)
  obtain ⟨u₀, hu₀⟩ := hU.nonempty
  have hX' : topologicalKrullDim X' ≤ N := by
    have hopen := (pullback.fst b U.ι).isOpenEmbedding
    have hne : (Set.range (pullback.fst b U.ι)).Nonempty :=
      ⟨_, ⟨inv (pullback.snd b U.ι) ⟨u₀, hu₀⟩, rfl⟩⟩
    rw [topologicalKrullDim_eq_of_isOpen k X' (b ≫ π) _ hopen.isOpen_range hne,
      ← hopen.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
      (Scheme.homeoOfIso (asIso (pullback.snd b U.ι))).isHomeomorph.topologicalKrullDim_eq]
    exact (U.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hX
  let Zc : Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  let i : I.subscheme ⟶ X := I.subschemeι
  have hrange : Set.range i = (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hio : Set.range U.ι.base = (Set.range i.base)ᶜ := by
    rw [hrange, compl_compl, Scheme.Opens.range_ι]
  refine subsingleton_sheafH_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, v} i b
    (pullback.fst b i) (pullback.snd b i) U.ι hio (IsPullback.of_hasPullback b i)
    (pullback.fst b U.ι) (pullback.snd b U.ι) (IsPullback.of_hasPullback b U.ι) (h095T b) G hG p
    ?_ ?_ ?_
  · have hnsurj : ¬ Function.Surjective (pullback.fst b i) := by
      intro hs
      obtain ⟨e, he⟩ := hs (OpenGraphClosure.inclusion π qP U ψ hψover ⟨u₀, hu₀⟩)
      have h1 : b (pullback.fst b i e) = i (pullback.snd b i e) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have h2 : b (OpenGraphClosure.inclusion π qP U ψ hψover ⟨u₀, hu₀⟩) = u₀ := by
        change (OpenGraphClosure.inclusion π qP U ψ hψover ≫
          OpenGraphClosure.projection π qP U ψ hψover) ⟨u₀, hu₀⟩ = u₀
        rw [OpenGraphClosure.inclusion_comp_projection]
        rfl
      have : u₀ ∈ Set.range i := ⟨pullback.snd b i e, by rw [← h1, he, h2]⟩
      rw [hrange] at this
      exact this hu₀
    have hEle := topologicalKrullDim_le_pred_of_not_surjective (pullback.fst b i) (by omega) hX'
      hnsurj
    have : IsProper (pullback.fst b i ≫ b ≫ π) := inferInstance
    exact IH (N - 1) hN1 hNN k _ (pullback.fst b i ≫ b ≫ π) hEle _
      (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) p (by omega)
  · have hG' := torsionSheafProperty_etaleAbelianInverseImage.{u, v} b G hG
    have : JacobsonSpace (projectiveLine k) := LocallyOfFiniteType.jacobsonSpace qP
    have hPdim : topologicalKrullDim (projectiveLine k) = 1 := topologicalKrullDim_projectiveLine k
    have hPns : ¬ Subsingleton (projectiveLine k) := by
      intro hs
      have h0 : topologicalKrullDim (projectiveLine k) ≤ 0 :=
        topologicalKrullDim_zero_of_discreteTopology _
      rw [hPdim] at h0
      exact absurd h0 (by norm_num)
    have hfib : ∀ t : projectiveLine k,
        topologicalKrullDim (f.fiber t) ≤ ((N - 1 : ℕ) : WithBot ℕ∞) := fun t ↦
      le_natCast_pred_of_add_one_le (by omega)
        ((topologicalKrullDim_fiber_add_one_le_of_isDominant f hPns t).trans hX')
    refine LerayVanishing.subsingleton_sheafH_of_forall_rightDerived_etaleAbelianDirectImage.{u, v}
      f _ (p + 1) fun r hr ↦ ?_
    by_cases hr' : 2 * (N - 1) < r
    · exact Sheaf.subsingleton_H_of_isZero
        (isZero_rightDerived_etaleAbelianDirectImage_of_geometricFibres.{u, v} f (h095T f)
          (N - 1) hfib (subsingleton_sheafH_of_isSepClosed_of_isAlgClosed.{u, v} (N - 1)
            (IH (N - 1) hN1 hNN)) _ hG' r hr') _
    · have hT := torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{v} f r _ hG'
      exact IH 1 le_rfl (by omega) k (projectiveLine k) qP (by rw [hPdim]; norm_num) _ hT
        (p + 1 - r) (by omega)
  · have hnsurj : ¬ Function.Surjective i := by
      intro hs
      have : u₀ ∈ Set.range i := hs u₀
      rw [hrange] at this
      exact this hu₀
    have hZle := topologicalKrullDim_le_pred_of_not_surjective i (by omega) hX hnsurj
    have : IsProper (i ≫ π) := inferInstance
    exact IH (N - 1) hN1 hNN k _ (i ≫ π) hZle _
      (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) (p + 1) (by omega)

/-- A surjective closed immersion into a reduced scheme is an isomorphism. -/
@[sga "3 X 8.9" "special case"]
theorem isIso_of_isClosedImmersion_of_surjective {E W : Scheme.{u}} (e : E ⟶ W)
    [IsClosedImmersion e] [IsReduced W] (he : Function.Surjective e) : IsIso e := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← Scheme.IdealSheafData.support_eq_top_iff]
  refine Closeds.ext ?_
  rw [Scheme.Hom.support_ker, he.range_eq, closure_univ]
  rfl

/-- The reduced closed subscheme on a closed subset `B` has underlying set `B`. -/
private theorem range_subschemeι_vanishingIdeal_eq_closeds {X : Scheme.{u}} (B : Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal B).subschemeι = (B : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The reduced closed subscheme on a closed subset has dimension at most that of the scheme. -/
private theorem topologicalKrullDim_subscheme_vanishingIdeal_le {X : Scheme.{u}} (B : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal B).subscheme ≤
      topologicalKrullDim X :=
  (Scheme.IdealSheafData.vanishingIdeal B).subschemeι.isClosedEmbedding.isInducing
    |>.topologicalKrullDim_le

/-- The inclusion of closed subschemes `J.subscheme ⟶ I.subscheme` for `I ≤ J` is a closed
immersion. -/
private theorem isClosedImmersion_idealSheafData_inclusion_of_le {X : Scheme.{u}}
    {I J : X.IdealSheafData} (h : I ≤ J) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp _ I.subschemeι

/-- A point of `I.subscheme` lies in the image of a morphism over `X` from the reduced closed
subscheme on `D` if and only if its image in `X` lies in `D`. -/
private theorem mem_range_iff_of_comp_subschemeι {X : Scheme.{u}} {I : X.IdealSheafData}
    (D : Closeds X)
    (f : (Scheme.IdealSheafData.vanishingIdeal D).subscheme ⟶ I.subscheme)
    (hf : f ≫ I.subschemeι = (Scheme.IdealSheafData.vanishingIdeal D).subschemeι)
    (y : I.subscheme) : y ∈ Set.range f ↔ I.subschemeι y ∈ (D : Set X) := by
  rw [← range_subschemeι_vanishingIdeal_eq_closeds D, ← hf, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, I.subschemeι.isClosedEmbedding.injective.mem_set_image]

/-- The reduced closed subscheme on an irreducible closed subset is integral. -/
private theorem isIntegral_vanishingIdeal_subscheme_of_isIrreducible {X : Scheme.{u}}
    (C : Closeds X) (hC : IsIrreducible (C : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
  have hrange := range_subschemeι_vanishingIdeal_eq_closeds C
  have : Nonempty (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    obtain ⟨-, y, -⟩ : (Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι).Nonempty :=
      hrange ▸ hC.nonempty
    exact ⟨y⟩
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι) :=
      Subtype.irreducibleSpace (hrange ▸ hC)
    exact (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.isClosedEmbedding.isEmbedding
      |>.toHomeomorph.isOpenEmbedding.irreducibleSpace
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- If `C ⊄ A`, the intersection of the closed subschemes on `C` and on `A` of a common closed
subscheme `I.subscheme` is not all of the one on `C`. -/
private theorem not_surjective_pullback_fst_of_not_le {X : Scheme.{u}} {I : X.IdealSheafData}
    {C A : Closeds X} (hCA : ¬ C ≤ A)
    (iC : (Scheme.IdealSheafData.vanishingIdeal C).subscheme ⟶ I.subscheme)
    (iA : (Scheme.IdealSheafData.vanishingIdeal A).subscheme ⟶ I.subscheme)
    (hiC : iC ≫ I.subschemeι = (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)
    (hiA : iA ≫ I.subschemeι = (Scheme.IdealSheafData.vanishingIdeal A).subschemeι) :
    ¬ Function.Surjective (pullback.fst iC iA) := by
  intro hs
  obtain ⟨x, hxC, hxA⟩ := Set.not_subset.1 hCA
  rw [← range_subschemeι_vanishingIdeal_eq_closeds C] at hxC
  obtain ⟨c, rfl⟩ := hxC
  obtain ⟨e, he⟩ := hs c
  apply hxA
  have h1 : iC (pullback.fst iC iA e) = iA (pullback.snd iC iA e) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rw [he] at h1
  have h2 := (mem_range_iff_of_comp_subschemeι A iA hiA (iC c)).1 ⟨_, h1.symm⟩
  rwa [← Scheme.Hom.comp_apply, hiC] at h2

/-- A Noetherian space is the union of finitely many irreducible closed subsets. -/
private theorem exists_finset_closeds_isIrreducible_sup_eq_top (X : Type*) [TopologicalSpace X]
    [NoetherianSpace X] :
    ∃ T : Finset (Closeds X), (∀ C ∈ T, IsIrreducible (C : Set X)) ∧ T.sup id = ⊤ := by
  classical
  obtain ⟨S, hSfin, hScl, hSirr, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := X))
  let T : Finset (Closeds X) :=
    hSfin.toFinset.attach.image fun t ↦ ⟨t.1, hScl t.1 (hSfin.mem_toFinset.1 t.2)⟩
  refine ⟨T, Finset.forall_mem_image.2 fun t _ ↦ hSirr t.1 (hSfin.mem_toFinset.1 t.2),
    top_unique fun x _ ↦ ?_⟩
  obtain ⟨t, htS, hxt⟩ := Set.mem_sUnion.1 (hSU ▸ Set.mem_univ x : x ∈ ⋃₀ S)
  exact Finset.le_sup (f := id) (s := T)
    (Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨t, hSfin.mem_toFinset.2 htS⟩)) hxt

/-- **The step over the irreducible components** in [Stacks, Tag 095U]. Under the induction
hypothesis `IH`, if the vanishing for `q > 2N` holds on the reduced closed subscheme on `A`, and
`C ⊄ A` is an irreducible closed subset, then it holds on the reduced closed subscheme on
`C ∪ A`. -/
private theorem subsingleton_sheafH_subscheme_sup_of_induction
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, v} p)
    (N : ℕ) (hN : 2 ≤ N)
    (IH : ∀ M : ℕ, 1 ≤ M → M < N → ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
      (π : Y ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim Y ≤ M →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G →
        ∀ q : ℕ, 2 * M < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q))
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (π : X ⟶ Spec (.of k)) [IsProper π]
    (hX : topologicalKrullDim X ≤ N) (C A : Closeds X) (hC : IsIrreducible (C : Set X))
    (hCA : ¬ C ≤ A)
    (hA : ∀ G : Sheaf (Scheme.IdealSheafData.vanishingIdeal A).subscheme.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}, Stacks.Torsion.torsionSheafProperty _ G →
        ∀ q : ℕ, 2 * N < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q))
    (G : Sheaf (Scheme.IdealSheafData.vanishingIdeal (C ⊔ A)).subscheme.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) (q : ℕ) (hq : 2 * N < q) :
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = p + 1 := ⟨q - 1, by omega⟩
  let IA := Scheme.IdealSheafData.vanishingIdeal A
  let IB := Scheme.IdealSheafData.vanishingIdeal (C ⊔ A)
  let IC := Scheme.IdealSheafData.vanishingIdeal C
  have hAB : IB ≤ IA := Scheme.IdealSheafData.vanishingIdeal_antimono le_sup_right
  have hCB : IB ≤ IC := Scheme.IdealSheafData.vanishingIdeal_antimono le_sup_left
  let iA : IA.subscheme ⟶ IB.subscheme := Scheme.IdealSheafData.inclusion hAB
  let iC : IC.subscheme ⟶ IB.subscheme := Scheme.IdealSheafData.inclusion hCB
  have hiA : iA ≫ IB.subschemeι = IA.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hAB
  have hiC : iC ≫ IB.subschemeι = IC.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hCB
  have : IsClosedImmersion iA := isClosedImmersion_idealSheafData_inclusion_of_le hAB
  have : IsClosedImmersion iC := isClosedImmersion_idealSheafData_inclusion_of_le hCB
  have hcover : ∀ y : IB.subscheme, IB.subschemeι y ∈ (C : Set X) ∨
      IB.subschemeι y ∈ (A : Set X) := fun y ↦ by
    have : IB.subschemeι y ∈ ((C ⊔ A : Closeds X) : Set X) :=
      range_subschemeι_vanishingIdeal_eq_closeds (C ⊔ A) ▸ Set.mem_range_self y
    rwa [Closeds.coe_sup] at this
  let Uo : IB.subscheme.Opens :=
    ⟨(Set.range iA)ᶜ, iA.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hio : Set.range Uo.ι.base = (Set.range iA.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    rfl
  have : IsReduced Uo.toScheme := isReduced_of_isOpenImmersion Uo.ι
  have hbU : IsIso (pullback.snd iC Uo.ι) := by
    refine isIso_of_isClosedImmersion_of_surjective _ ?_
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y ↦ (mem_range_iff_of_comp_subschemeι C iC hiC _).2
      ((hcover _).resolve_right fun h ↦ y.2 ((mem_range_iff_of_comp_subschemeι A iA hiA _).2 h))
  have : IsProper (IC.subschemeι ≫ π) := inferInstance
  have : AlgebraicGeometry.IsNoetherian IC.subscheme :=
    isNoetherian_of_isProper_over_field (IC.subschemeι ≫ π)
  have : IsIntegral IC.subscheme := isIntegral_vanishingIdeal_subscheme_of_isIrreducible C hC
  have hCdim : topologicalKrullDim IC.subscheme ≤ N :=
    (topologicalKrullDim_subscheme_vanishingIdeal_le C).trans hX
  refine subsingleton_sheafH_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, v} iA iC
    (pullback.fst iC iA) (pullback.snd iC iA) Uo.ι hio (IsPullback.of_hasPullback iC iA)
    (pullback.fst iC Uo.ι) (pullback.snd iC Uo.ι) (IsPullback.of_hasPullback iC Uo.ι)
    (h095T iC) G hG p ?_ ?_ ?_
  · have hEle := topologicalKrullDim_le_pred_of_not_surjective (pullback.fst iC iA) (by omega)
      hCdim (not_surjective_pullback_fst_of_not_le hCA iC iA hiC hiA)
    have : IsProper (pullback.fst iC iA ≫ IC.subschemeι ≫ π) := inferInstance
    exact IH (N - 1) (by omega) (by omega) k _ (pullback.fst iC iA ≫ IC.subschemeι ≫ π) hEle _
      (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) p (by omega)
  · exact subsingleton_sheafH_of_isIntegral_of_induction.{u, v} h095T N hN IH k
      IC.subscheme (IC.subschemeι ≫ π) hCdim _
      (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) (p + 1) hq
  · exact hA _ (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) (p + 1) hq

/-- **The induction step** of [Stacks, Tag 095U]. Let `N ≥ 2` and suppose the vanishing
`H^q(Y, G) = 0` for `q > 2M` is known for every proper scheme `Y` of dimension at most `M` over an
algebraically closed field, for every `1 ≤ M < N`. Then it holds for `M = N`. -/
theorem subsingleton_sheafH_of_isProper_of_induction
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, v} p)
    (N : ℕ) (hN : 2 ≤ N)
    (IH : ∀ M : ℕ, 1 ≤ M → M < N → ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
      (π : Y ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim Y ≤ M →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G →
        ∀ q : ℕ, 2 * M < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q))
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (π : X ⟶ Spec (.of k)) [IsProper π]
    (hX : topologicalKrullDim X ≤ N)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ) (hq : 2 * N < q) :
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
  classical
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProper_over_field π
  have claim : ∀ T : Finset (Closeds X), (∀ C ∈ T, IsIrreducible (C : Set X)) →
      ∀ B : Closeds X, B = T.sup id →
      ∀ G : Sheaf (Scheme.IdealSheafData.vanishingIdeal B).subscheme.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty _ G →
        ∀ q : ℕ, 2 * N < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ B hB G _ q _
      have : IsEmpty (Scheme.IdealSheafData.vanishingIdeal B).subscheme := by
        refine ⟨fun y ↦ ?_⟩
        have hy := (range_subschemeι_vanishingIdeal_eq_closeds B).subset (Set.mem_range_self y)
        rw [show (B : Set X) = ∅ by rw [hB]; rfl] at hy
        exact hy
      exact subsingleton_sheafH_of_isEmpty_sheafUniverse.{u, v} G q
    | insert C T hCT ih =>
      intro hirr B hB G hG q hq
      have hirrT : ∀ D ∈ T, IsIrreducible (D : Set X) := fun D hD ↦
        hirr D (Finset.mem_insert_of_mem hD)
      have hBCA : B = C ⊔ T.sup id := by rw [hB, Finset.sup_insert]; rfl
      by_cases hCA : C ≤ T.sup id
      · exact ih hirrT B (by rw [hBCA, sup_eq_right.2 hCA]) G hG q hq
      subst hBCA
      exact subsingleton_sheafH_subscheme_sup_of_induction.{u, v} h095T N hN IH k X π hX C _
        (hirr C (Finset.mem_insert_self C T)) hCA (ih hirrT _ rfl) G hG q hq
  obtain ⟨T, hTirr, hTtop⟩ := exists_finset_closeds_isIrreducible_sup_eq_top X
  let ι := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι
  have : UniversalHomeomorphism ι :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective ι
      (Set.range_eq_univ.1 (range_subschemeι_vanishingIdeal_eq_closeds ⊤))
  have hsubY := claim T hTirr ⊤ hTtop.symm ((etaleAbelianInverseImage.{u, v} ι).obj G)
    (torsionSheafProperty_etaleAbelianInverseImage.{u, v} _ G hG) q hq
  exact (Equiv.ofBijective _
    (etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, v, max (u + 1) v}
      ι G q)).subsingleton

/-- **The absolute form of [Stacks, Tag 095U], from the case of curves.** Granted the proper base
change theorem (`h095T`, [Stacks, Tag 095T]) and the vanishing `H^q(C, G) = 0` for `q > 2` on
every proper scheme `C` of dimension at most one over an algebraically closed field (`hcurve`,
part (1) of [Stacks, Tag 03SC] for proper curves): for `N ≥ 1`, every proper scheme `Y` of
dimension at most `N` over an algebraically closed field and every torsion abelian sheaf `G` on
`Y_étale`, `H^q(Y, G) = 0` for `q > 2N`. -/
theorem subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, v} p)
    (hcurve : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q)) :
    ∀ N : ℕ, 1 ≤ N → ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
      (π : Y ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim Y ≤ N →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G →
        ∀ q : ℕ, 2 * N < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN1
    rcases Nat.lt_or_ge N 2 with hN | hN
    · obtain rfl : N = 1 := by omega
      exact hcurve
    · exact subsingleton_sheafH_of_isProper_of_induction.{u, v} h095T N hN
        fun M hM1 hMN ↦ ih M hMN hM1

/-- **The absolute form of [Stacks, Tag 095U].** Granted the proper base change theorem
(`h095T`, [Stacks, Tag 095T]) and [Stacks, Tag 03SC] (`h03SC`): for `N ≥ 1`, every proper scheme
`Y` of dimension at most `N` over an algebraically closed field and every torsion abelian sheaf
`G` on `Y_étale`, `H^q(Y, G) = 0` for `q > 2N`. -/
theorem subsingleton_sheafH_of_isProper_of_isAlgClosed
    [∀ S : Scheme.{u},
      HasExt.{max (u + 1) v} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, v} p)
    (h03SC : CurveTorsionCohomologyStatement.{u, v}) :
    ∀ N : ℕ, 1 ≤ N → ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
      (π : Y ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim Y ≤ N →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G →
        ∀ q : ℕ, 2 * N < q → Subsingleton (Sheaf.H.{max (u + 1) v} G q) :=
  subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve.{u, v} h095T
    (subsingleton_sheafH_of_topologicalKrullDim_le_one.{u, v} h03SC)

end Stacks.EtaleCohomology

end
