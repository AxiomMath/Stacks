module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.ComponentTwist
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.ChainDescent

/-!
# An invertible module on the model restricting to a pullback of an ample module

In the situation of [Stacks, Tag 0C61] suppose every component of the special fibre `X_k` has
multiplicity one and `X_k` is a proper nodal curve over `k` with `H⁰(X_k, 𝒪) = k`, and let
`c₀ : X_k ⟶ Y₀` be the composite of a chain of contractions of rational bridges which is a stable
contraction ([Stacks, Tag 0E7Q]). The components of `X_k` mapped to a point by `c₀` form a proper
subset (`Y₀` has dimension one), so there is an invertible `ℳ` on `X` of degree zero on exactly
these components; its restriction to `X_k` descends along the chain to an invertible `ℒ₀` on `Y₀`,
which is ample since its pullback has positive degree on every component of `X_k` not contracted
by `c₀`.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_isAmple_pullback_iso_specialFiberι`.
* `Stacks.Models.RegularProperModelSituation`'s
  `invertibleCurveDegree_reducedComponent_eq_specialFiberComponentDegree`: the degree on the
  reduced component through a generic point of `X_k` is the component degree `deg(ℳ|_{C_Z})` of
  the corresponding component.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open Stacks.AlgebraicGeometry.ComponentDegrees

namespace Stacks.Topology.Dimension

/-- **A quasi-sober space of Krull dimension one has a non-closed point.** Otherwise every
irreducible closed subset, being the closure of its generic point, is a single point, so there is
no strict inclusion of irreducible closed subsets. -/
theorem exists_not_isClosed_singleton_of_topologicalKrullDim_eq_one {X : Type*}
    [TopologicalSpace X] [QuasiSober X] (h : topologicalKrullDim X = 1) :
    ∃ x : X, ¬ IsClosed ({x} : Set X) := by
  by_contra hcon
  push Not at hcon
  have h1 : (1 : WithBot ℕ∞) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds X) := by
    rw [← topologicalKrullDim, h]
  obtain ⟨s, t, hst⟩ := Order.one_le_krullDim_iff.1 h1
  obtain ⟨η, hη⟩ := QuasiSober.sober t.isIrreducible t.isClosed
  have ht : (t : Set X) = {η} := by
    rw [← hη.def, (hcon _).closure_eq]
  have hs : (s : Set X) = (t : Set X) := by
    refine Set.Subset.antisymm hst.le ?_
    obtain ⟨y, hy⟩ := s.2.nonempty
    have hy' : y ∈ (t : Set X) := hst.le hy
    rw [ht] at hy' ⊢
    rw [Set.mem_singleton_iff.1 hy'] at hy
    exact Set.singleton_subset_iff.2 hy
  exact hst.ne (TopologicalSpace.IrreducibleCloseds.ext hs)

end Stacks.Topology.Dimension

namespace AlgebraicGeometry

/-- The degree of an invertible module on a proper curve over `k` depends only on the structure
morphism (up to equality) and on the module up to isomorphism. -/
theorem invertibleCurveDegree_congr (k : Type u) [Field k] {X : Scheme.{u}}
    {f f' : X ⟶ Spec (.of k)} [IsProper f] [IsProper f'] (h : f = f')
    (hdim : topologicalKrullDim X ≤ 1) {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    invertibleCurveDegree k f hdim L = invertibleCurveDegree k f' hdim L' := by
  subst h
  exact invertibleCurveDegree_eq_of_iso k f hdim e

/-- **The degree on a closed subscheme only depends on its ideal.** For a closed immersion
`i : C ⟶ X` with kernel `J` and a proper `f : X ⟶ Spec k`, the degree over `k` of the
restriction of an invertible module to `C` along `i` equals that of its restriction to the
closed subscheme cut out by `J`: the two are isomorphic over `X`. -/
theorem invertibleCurveDegree_pullback_subschemeι_eq_of_ker_eq (k : Type u) [Field k]
    {X C : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : C ⟶ X) [IsClosedImmersion i]
    (J : X.IdealSheafData) (hJ : i.ker = J)
    (hJdim : topologicalKrullDim J.subscheme ≤ 1) (hCdim : topologicalKrullDim C ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    @invertibleCurveDegree k _ J.subscheme (J.subschemeι ≫ f) inferInstance hJdim
        ((Scheme.Modules.pullback J.subschemeι).obj L)
        (SheafOfModules.isInvertible_pullback J.subschemeι L) =
      @invertibleCurveDegree k _ C (i ≫ f) inferInstance hCdim
        ((Scheme.Modules.pullback i).obj L) (SheafOfModules.isInvertible_pullback i L) := by
  subst hJ
  let e : C ≅ i.ker.subscheme := asIso i.toImage
  have he : e.hom ≫ i.ker.subschemeι = i := i.toImage_imageι
  rw [← invertibleCurveDegree_pullback_of_isIso e.hom (i.ker.subschemeι ≫ f) hCdim hJdim
    ((Scheme.Modules.pullback i.ker.subschemeι).obj L)]
  exact invertibleCurveDegree_congr k (by rw [← Category.assoc, he]) hCdim
    ((Scheme.Modules.pullbackComp e.hom i.ker.subschemeι).app L ≪≫
      (Scheme.Modules.pullbackCongr he).app L)

end AlgebraicGeometry

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **Translation between the two indexings of the components of the special fibre.** For the
generic point `ζ` of a one-dimensional irreducible component `Z = closure {ζ}` of `X_k`, the
degree over `k` of `(ℳ|_{X_k})|_{closure {ζ}}` (with its reduced induced structure) is the
component degree `deg(ℳ|_{C_Z})`: both closed subschemes are the reduced induced structure on the
same closed subset of `X_k`. -/
theorem invertibleCurveDegree_reducedComponent_eq_specialFiberComponentDegree
    (hdim : topologicalKrullDim S.specialFiber ≤ 1) (M : S.X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property M)
    (ζ : genericPointsOne S.specialFiber) (Z : irreducibleComponents S.specialFiber)
    (hZ : (Z.1 : Set S.specialFiber) = closure {ζ.1}) :
    letI : SheafOfModules.IsInvertible S.specialFiber.presheaf S.specialFiber.ringCatSheaf.2
        ((Scheme.Modules.pullback S.specialFiberι).obj M) :=
      SheafOfModules.isInvertible_pullback S.specialFiberι M
        (hL := hM.toAlgebraicGeometry)
    @invertibleCurveDegree S.k _ (reducedComponent S.specialFiber ζ)
        (reducedComponentι S.specialFiber ζ ≫ S.specialFiberToSpec)
        (isProper_reducedComponentι_comp S.k S.specialFiberToSpec ζ)
        (topologicalKrullDim_reducedComponent_le S.specialFiber hdim ζ)
        ((Scheme.Modules.pullback (reducedComponentι S.specialFiber ζ)).obj
          ((Scheme.Modules.pullback S.specialFiberι).obj M))
        (SheafOfModules.isInvertible_pullback (reducedComponentι S.specialFiber ζ)
          ((Scheme.Modules.pullback S.specialFiberι).obj M)) =
      S.specialFiberComponentDegree Z M hM := by
  let : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 M := hM.toAlgebraicGeometry
  have hrange : Set.range (S.specialFiberComponentι Z) = Z.1 := by
    have h1 : S.specialFiberι.base '' Set.range (S.specialFiberComponentι Z) =
        S.specialFiberι.base '' Z.1 := by
      rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
        S.specialFiberComponentι_specialFiberι Z, Scheme.IdealSheafData.range_subschemeι]
      exact S.coe_support_specialFiberComponentIdeal Z
    exact S.specialFiberι.isClosedEmbedding.injective.image_injective h1
  have hker : (S.specialFiberComponentι Z).ker =
      Scheme.IdealSheafData.vanishingIdeal ⟨closure ({ζ.1} : Set S.specialFiber),
        isClosed_closure⟩ := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    simp only [TopologicalSpace.Closeds.coe_closure, hrange, hZ, closure_closure]
    rfl
  refine (invertibleCurveDegree_pullback_subschemeι_eq_of_ker_eq S.k S.specialFiberToSpec
    (S.specialFiberComponentι Z) _ hker
    (topologicalKrullDim_reducedComponent_le S.specialFiber hdim ζ)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    ((Scheme.Modules.pullback S.specialFiberι).obj M)).trans ?_
  unfold specialFiberComponentDegree componentDegree
  exact invertibleCurveDegree_congr S.k rfl _ ((Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr (S.specialFiberComponentι_specialFiberι Z)).app M)

/-- **An invertible module on the model whose restriction to the special fibre is the pullback
of an ample module along the stable contraction.** -/
theorem exists_isAmple_pullback_iso_specialFiberι
    (hm : ∀ Z, S.specialFiberMultiplicity Z = 1)
    (hdim : topologicalKrullDim S.specialFiber = 1)
    (hglobal : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop))
    (hnodal : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩;
      Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber)
    {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}
    (hseq : IsIteratedContractionOfRationalBridges S.k S.specialFiberToSpec g₀ c₀)
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀) :
    ∃ (M : S.X.Modules) (_ : SheafOfModules.IsInvertible S.X.toRingedSpace.presheaf
        (structureSheafRing S.X.toRingedSpace).property M)
      (L₀ : Y₀.Modules) (_ : SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
        (structureSheafRing Y₀.toRingedSpace).property L₀),
      Scheme.Modules.IsAmple Y₀ L₀ ∧
        Nonempty ((Scheme.Modules.pullback c₀).obj L₀ ≅
          (Scheme.Modules.pullback S.specialFiberι).obj M) := by
  classical
  have hcomp : c₀ ≫ g₀ = S.specialFiberToSpec := hc₀.comp_eq
  have : IsProper g₀ := hc₀.isProper
  have : IsProper c₀ := by
    have : IsProper (c₀ ≫ g₀) := by rw [hcomp]; infer_instance
    exact IsProper.of_comp c₀ g₀
  have hsurj : Function.Surjective c₀ :=
    (c₀.surjective_of_isIso_app fun U =>
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₀
        hc₀.isIso_unitToPushforwardObjUnit U).surj
  -- the components contracted to a point by `c₀`
  let T : Set (irreducibleComponents S.specialFiber) :=
    {Z | ∃ y : Y₀, ∀ x ∈ (Z.1 : Set S.specialFiber), c₀ x = y}
  have hT : ∃ Z, Z ∉ T := by
    obtain ⟨y, hy⟩ :=
      Stacks.Topology.Dimension.exists_not_isClosed_singleton_of_topologicalKrullDim_eq_one
        hc₀.topologicalKrullDim_eq
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      fun ⟨y', hy'⟩ => hy ?_⟩
    have himage : c₀ '' irreducibleComponent x = {c₀ x} := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        rw [hy' z hz, hy' x mem_irreducibleComponent]
        rfl
      · rintro _ rfl
        exact ⟨x, mem_irreducibleComponent, rfl⟩
    rw [← himage]
    exact c₀.isClosedMap _ isClosed_irreducibleComponent
  obtain ⟨M, hM, hdeg⟩ := S.exists_isInvertible_specialFiberComponentDegree hm T hT
  let hMag : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 M :=
    hM.toAlgebraicGeometry
  let : SheafOfModules.IsInvertible S.specialFiber.presheaf S.specialFiber.ringCatSheaf.2
      ((Scheme.Modules.pullback S.specialFiberι).obj M) :=
    SheafOfModules.isInvertible_pullback S.specialFiberι M
  -- the degree on the reduced component through a generic point is the component degree
  have hdegζ := fun ζ : genericPointsOne S.specialFiber =>
    S.invertibleCurveDegree_reducedComponent_eq_specialFiberComponentDegree hdim.le M hM ζ
      ⟨closure {ζ.1}, (mem_genericPointsOne_iff.1 ζ.2).1⟩ rfl
  obtain ⟨L₀, hL₀, ⟨e⟩⟩ :=
    hseq.exists_pullback_iso_of_invertibleCurveDegree_eq_zero hdim hglobal hnodal
      ((Scheme.Modules.pullback S.specialFiberι).obj M) fun ζ hζ => by
        rw [hdegζ]
        exact (hdeg _).1 hζ
  refine ⟨M, hMag, L₀, hL₀, ?_, ⟨e⟩⟩
  refine isAmple_of_invertibleCurveDegree_pullback_pos S.specialFiberToSpec g₀ c₀ hcomp hsurj
    hdim.le hc₀.topologicalKrullDim_eq.le L₀ fun ζ hζ => ?_
  rw [invertibleCurveDegree_eq_of_iso S.k _ _
    ((Scheme.Modules.pullback (reducedComponentι S.specialFiber ζ)).mapIso e), hdegζ]
  exact (hdeg _).2 hζ

end Stacks.Models.RegularProperModelSituation

end
