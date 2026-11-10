module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.DualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.GeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility

/-!
# The degree of the dualizing sheaf on subcurves of a nodal curve

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities. Then `X` is Gorenstein ([Stacks, Tag 0E37]), so its dualizing sheaf
`ω_X` is invertible, and for a reduced connected one-dimensional closed subscheme `Y ⊊ X` the exact
sequence `0 ⟶ ω_Y ⟶ ω_X|_Y ⟶ 𝒪_{Y ∩ X'} ⟶ 0` of [Stacks, Tag 0E34] computes
`deg(ω_X|_Y) = deg(Y ∩ X') - 2 χ(Y, 𝒪_Y)`.

## Main results

* `AlgebraicGeometry.equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one`: a connected
  one-dimensional space is equidimensional.
* `AlgebraicGeometry.isGorenstein_of_connectedSpace_of_hasAtWorstNodalSingularities` and
  `AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities`: a
  connected one-dimensional nodal curve is Gorenstein, and its dualizing sheaf is invertible.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail`:
  [Stacks, Tag 0E63], `deg(ω_X|_C) < 0` on a rational tail `C`.
* `finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail`:
  [Stacks, Tag 0E3J], `deg(ω_X|_Y) ≥ dim_k H¹(Y, 𝒪_Y)` for every reduced connected
  one-dimensional closed subscheme `Y ≠ X`, when `X` has no rational tail.

## References

* [Stacks Project, Tag 0E3J](https://stacks.math.columbia.edu/tag/0E3J)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E34](https://stacks.math.columbia.edu/tag/0E34)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry


/-- **A connected one-dimensional space is equidimensional.** In a connected Noetherian sober `T₀`
space of dimension one, an irreducible component of dimension zero would be a closed generic point,
hence its own component and open (the other components are finitely many closed sets), so by
connectedness the whole space, which would then have dimension zero; so every component has
dimension one. -/
theorem equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one {T : Type*}
    [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T] [T0Space T]
    [ConnectedSpace T]
    (hdim : topologicalKrullDim T = 1) : TopologicalSpace.Equidimensional T := by
  suffices h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W = 1 from
    fun _ hA _ hB => (h _ hA).trans (h _ hB).symm
  intro W hW
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  let W' : TopologicalSpace.IrreducibleCloseds T := ⟨W, hW.1, hWc⟩
  change topologicalKrullDim (W' : Set T) = 1
  rw [topologicalKrullDim_coe_eq_height W']
  have hle : (Order.height W' : WithBot ℕ∞) ≤ 1 := hdim ▸ Order.height_le_krullDim W'
  have hne : Order.height W' ≠ 0 := by
    intro h0
    have hmin : IsMin W' := Order.height_eq_zero.mp h0
    let η := hW.1.genericPoint
    have hη : closure ({η} : Set T) = W := by
      have := hW.1.isGenericPoint_genericPoint_closure
      rwa [hWc.closure_eq] at this
    have hWη : W = {η} := by
      ext z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · let Z' : TopologicalSpace.IrreducibleCloseds T :=
          ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
        have hZW : Z' ≤ W' := closure_minimal (Set.singleton_subset_iff.mpr hz) hWc
        have hWZ : W' ≤ Z' := hmin hZW
        have hZW' : closure ({z} : Set T) ⊆ W := hZW
        have hWZ' : W ⊆ closure ({z} : Set T) := hWZ
        have hcl : closure ({z} : Set T) = closure {η} := by
          rw [hη]
          exact le_antisymm hZW' hWZ'
        exact (inseparable_iff_closure_eq.mpr hcl).eq
      · rw [Set.mem_singleton_iff.mp hz, ← hη]
        exact subset_closure rfl
    have hηc : IsClosed ({η} : Set T) := hWη ▸ hWc
    have hgen : η ∈ genericPoints T := by
      change closure {η} ∈ irreducibleComponents T
      rw [hη]
      exact hW
    have huniv := eq_univ_of_isClosed_of_mem_genericPoints hηc hgen
    have : Subsingleton T := ⟨fun a b => by
      have ha : a ∈ ({η} : Set T) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({η} : Set T) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have : Nonempty T := ⟨η⟩
    have : DiscreteTopology T := inferInstance
    have h0 := topologicalKrullDim_zero_of_discreteTopology (X := T)
    rw [hdim] at h0
    exact absurd h0 (by decide)
  exact le_antisymm hle (by exact_mod_cast Order.one_le_iff_ne_zero.mpr hne)

/-- A scheme with a quasi-compact morphism locally of finite type to `Spec k` is Noetherian. -/
private theorem isNoetherian_of_morphismProperty {k : Type u} [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] : IsNoetherian Z :=
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := QuasiCompact.compactSpace_of_compactSpace g
  ⟨⟩

/-- The canonical map to `Spec Γ(Z, ⊤)` is a morphism over `Spec k`. -/
private theorem toSpecΓ_comp_spec_map_ΓSpecIso_inv_comp_appTop {k : Type u} [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) :
    Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

/-- The map `Γ(Z, ⊤) ⟶ Γ(Spec Γ(Z, ⊤), ⊤)` induced by `toSpecΓ` is an isomorphism. -/
private theorem isIso_ΓSpecIso_inv_toSpecΓ_appTop (Z : Scheme.{u}) :
    IsIso ((Scheme.ΓSpecIso (.of Γ(Z, ⊤))).inv ≫ Z.toSpecΓ.appTop) := by
  rw [Scheme.toSpecΓ_appTop]
  infer_instance

/-- **A connected one-dimensional nodal curve is Gorenstein.** It is equidimensional, being
connected of dimension one, so [Stacks, Tag 0E37] applies. -/
theorem isGorenstein_of_connectedSpace_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X) :
    IsGorenstein X := by
  have := isNoetherian_of_morphismProperty (X ↘ Spec (.of k))
  exact Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k X
    (equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hdim) hdim hnodal

/-- **The dualizing sheaf of a connected proper one-dimensional nodal curve is invertible.** The
curve is Gorenstein
(`AlgebraicGeometry.isGorenstein_of_connectedSpace_of_hasAtWorstNodalSingularities`), so
`AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_connectedSpace` applies. -/
theorem isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities (k : Type u)
    [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) :=
  have := isGorenstein_of_connectedSpace_of_hasAtWorstNodalSingularities k X hdim hnodal
  isInvertible_dualizingSheafOverField_of_connectedSpace k (X ↘ Spec (.of k)) hdim

/-- **A reduced closed subscheme of a reduced scheme which is not the whole scheme has support
different from the whole space**: a reduced closed subscheme is cut out by the vanishing ideal of
its support, and the vanishing ideal of the whole space is the nilradical, which is zero. -/
theorem IdealSheafData.support_ne_univ_of_ne_bot {Y : Scheme.{u}} [IsReduced Y]
    (C : Y.IdealSheafData) [IsReduced C.subscheme] (hC : C ≠ ⊥) :
    (C.support : Set Y) ≠ Set.univ := by
  intro h
  apply hC
  have hker := Stacks.Chow.ker_eq_vanishingIdeal_support_of_isReduced C.subschemeι
  rw [Scheme.IdealSheafData.ker_subschemeι] at hker
  have htop : C.support = ⊤ := Closeds.ext h
  rw [hker, htop, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **A subcurve on which `ω_X` has degree less than `dim_k H¹(Y, 𝒪_Y)` has negative degree, and
is a rational tail if irreducible.** Let `X` be proper of dimension one over `k` with
`H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and let `Y ⊆ X` be a reduced connected
one-dimensional closed subscheme whose support is not all of `X`. With `k' = Γ(Y, 𝒪_Y)`, a field,
the sequence `0 ⟶ ω_Y ⟶ ω_X|_Y ⟶ 𝒪_{Y ∩ X'} ⟶ 0` of [Stacks, Tag 0E34] and the divisibility by
`[k' : k]` force `Y ∩ X'` to be one `k'`-rational point and `H¹(Y, 𝒪_Y) = 0`. This is the core of
the proof of [Stacks, Tag 0E3J]. -/
theorem invertibleCurveDegree_neg_and_isRationalTail_of_lt_finrank_cohomologyOverField_one
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
    (hY : topologicalKrullDim Y.subscheme = 1) (hYX : (Y.support : Set X) ≠ Set.univ) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
      hnodal
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hω
    invertibleCurveDegree k (Y.subschemeι ≫ (X ↘ Spec (.of k))) hY.le
        ((Scheme.Modules.pullback Y.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) <
      (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ (X ↘ Spec (.of k)))
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) →
    invertibleCurveDegree k (Y.subschemeι ≫ (X ↘ Spec (.of k))) hY.le
        ((Scheme.Modules.pullback Y.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0 ∧
      (IrreducibleSpace Y.subscheme → IsRationalTail k X Y) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
    hnodal
  intro hlt
  let f := X ↘ Spec (.of k)
  let fY := Y.subschemeι ≫ f
  have := isNoetherian_of_morphismProperty f
  have := isNoetherian_of_morphismProperty fY
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hXeq : Equidimensional X := equidimensional_of_isIso_globalSections_of_dimension_one k f hdim
  have hYeq : Equidimensional Y.subscheme :=
    equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hY
  -- `k' = Γ(Y, 𝒪_Y)` is a field and `ω_Y` is invertible over it
  let : Field Γ(Y.subscheme, ⊤) :=
    (isField_globalSections_of_isReduced_of_connectedSpace k fY).toField
  let : Algebra k Γ(Y.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop).hom.toAlgebra
  have : IsProper Y.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fY
  have := isIso_ΓSpecIso_inv_toSpecΓ_appTop Y.subscheme
  have hf : Y.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y.subscheme, ⊤))) =
      fY := toSpecΓ_comp_spec_map_ΓSpecIso_inv_comp_appTop fY
  let : Y.subscheme.Over (Spec (.of k)) := ⟨fY⟩
  have : LocallyOfFiniteType (Y.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType fY)
  have hYnodal := Stacks.Curves.hasAtWorstNodalSingularities_subscheme hXeq hdim hnodal Y hYeq hY
  have : IsGorenstein Y.subscheme :=
    Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k Y.subscheme hYeq hY hYnodal
  have := isInvertible_dualizingSheafOverField_of_connectedSpace Γ(Y.subscheme, ⊤)
    Y.subscheme.toSpecΓ hY
  -- the sequence `0 ⟶ ω_Y ⟶ ω_X|_Y ⟶ 𝒪_{Y ∩ X'} ⟶ 0`
  obtain ⟨a, b, w, hS⟩ := (Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible
    f hXeq hdim Y hYeq hY).2.2.2.2.2.2.2.2.1
  let : SheafOfModules.IsInvertible Y.subscheme.presheaf Y.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Y.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι _ hω
  -- `Y` meets the closure of its complement
  have hYne : (Y.support : Set X).Nonempty := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y.subscheme)
    rw [← Y.range_subschemeι]
    exact ⟨_, y, rfl⟩
  have hne : Nonempty (intersectionWithComplementaryCurveIdeal Y).subscheme :=
    nonempty_intersectionWithComplementaryCurve_of_connectedSpace Y hYne hYX
  obtain ⟨h1, hg⟩ := finrank_globalSections_intersection_eq_one_of_invertibleCurveDegree_lt Y hY.le
    Γ(Y.subscheme, ⊤) Y.subscheme.toSpecΓ hf hS (Iso.refl _) (Iso.refl _) hdim.le hne hlt
  have hh1 := finrank_cohomologyOverField_one_unit_eq_mul_genus Γ(Y.subscheme, ⊤) fY
    Y.subscheme.toSpecΓ hf
  rw [hg, mul_zero] at hh1
  refine ⟨?_, fun hirr => ?_⟩
  · rw [hh1] at hlt
    exact_mod_cast hlt
  · have : IsIntegral Y.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
    exact isRationalTail_of_finrank_globalSections_intersection_eq_one hdim.le Y hY
      (nonempty_complementaryCurve_of_support_ne_univ Y hYX) Γ(Y.subscheme, ⊤)
      Y.subscheme.toSpecΓ h1 hg

/-- **Stacks Project, Tag 0E3J.** Let `X` be a proper scheme of dimension one over a field `k`
with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities. If `X` has no rational tail, then for
every reduced connected closed subscheme `Y ⊆ X`, `Y ≠ X`, of dimension one,
`deg(ω_X|_Y) ≥ dim_k H¹(Y, 𝒪_Y)`.

Here `ω_X` is invertible
(`AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities`). If
the inequality failed, then `deg(ω_X|_Y) < 0`; for `Y` irreducible this makes `Y` a rational
tail, and otherwise some one-dimensional component `C` of `Y` has `deg(ω_X|_C) < 0`
([Stacks, Tag 0AYW]) and is a rational tail by the same analysis. -/
@[stacks 0E3J]
theorem finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
    (hY : topologicalKrullDim Y.subscheme = 1) (hYX : Y ≠ ⊥) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
      hnodal
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hω
    (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ (X ↘ Spec (.of k)))
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) ≤
      invertibleCurveDegree k (Y.subschemeι ≫ (X ↘ Spec (.of k))) hY.le
        ((Scheme.Modules.pullback Y.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
    hnodal
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hYX' := IdealSheafData.support_ne_univ_of_ne_bot Y hYX
  by_contra! hcon
  obtain ⟨hneg, hirr⟩ :=
    invertibleCurveDegree_neg_and_isRationalTail_of_lt_finrank_cohomologyOverField_one hdim hnodal
      Y hY hYX' hcon
  by_cases hirred : IrreducibleSpace Y.subscheme
  · exact htail Y (hirr hirred)
  -- a component `C` of `Y` with `deg(ω_X|_C) < 0`
  let := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι
    (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hω
  obtain ⟨ξ, hξ⟩ := exists_componentDegree_neg_of_invertibleCurveDegree_neg
    (Y.subschemeι ≫ (X ↘ Spec (.of k))) hY.le _ hneg
  obtain ⟨C, hCint, hCdim, hCY, hCdeg⟩ := exists_idealSheafData_componentDegree (k := k) Y hY.le
    (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) ξ
  have hCX : (C.support : Set X) ≠ Set.univ := fun h => hYX' (Set.eq_univ_of_univ_subset (h ▸ hCY))
  have hClt : invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le
      ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) <
      (Module.finrank k (cohomologyOverField k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (SheafOfModules.unit C.subscheme.ringCatSheaf) 1) : ℤ) := by
    rw [hCdeg]
    exact hξ.trans_le (Nat.cast_nonneg _)
  exact htail C ((invertibleCurveDegree_neg_and_isRationalTail_of_lt_finrank_cohomologyOverField_one
    hdim hnodal C hCdim hCX hClt).2 inferInstance)

/-- **Stacks Project, Tag 0E63.** Let `X` be a proper scheme of dimension one over a field `k`
with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and let `C ⊆ X` be a rational tail. Then
`deg(ω_X|_C) < 0`.

Here `ω_X` is invertible
(`AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities`). The
sequence `0 ⟶ ω_C ⟶ ω_X|_C ⟶ 𝒪_{C ∩ X'} ⟶ 0` of [Stacks, Tag 0E34] gives
`deg(ω_X|_C) = -[k' : k]` with `k' = Γ(C, 𝒪_C)`
(`AlgebraicGeometry.invertibleCurveDegree_eq_neg_of_isRationalTail`). -/
@[stacks 0E63]
theorem invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
      hnodal
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hω
    invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC).le
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0 := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
    hnodal
  let f := X ↘ Spec (.of k)
  let fC := C.subschemeι ≫ f
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC
  have hXeq : Equidimensional X := equidimensional_of_isIso_globalSections_of_dimension_one k f hdim
  have hCeq : Equidimensional C.subscheme := Equidimensional.of_preirreducibleSpace C.subscheme
  obtain ⟨a, b, w, hS⟩ := (Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible
    f hXeq hdim C hCeq hCdim).2.2.2.2.2.2.2.2.1
  let : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι _ hω
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  let : Algebra k Γ(C.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop).hom.toAlgebra
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fC
  have := isIso_ΓSpecIso_inv_toSpecΓ_appTop C.subscheme
  have hf : C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.subscheme, ⊤))) =
      fC := toSpecΓ_comp_spec_map_ΓSpecIso_inv_comp_appTop fC
  -- `ω_C` is invertible over `Γ(C, 𝒪_C)`
  let : C.subscheme.Over (Spec (.of k)) := ⟨fC⟩
  have : LocallyOfFiniteType (C.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType fC)
  have : IsGorenstein C.subscheme :=
    Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k C.subscheme hCeq hCdim
      (Stacks.Curves.hasAtWorstNodalSingularities_subscheme hXeq hdim hnodal C hCeq hCdim)
  have := isInvertible_dualizingSheafOverField_of_connectedSpace Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ hCdim
  have hneg := invertibleCurveDegree_eq_neg_of_isRationalTail hdim hC Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ hf hS (Iso.refl _) (Iso.refl _)
  change invertibleCurveDegree k fC _ (ShortComplex.mk a b w).X₂ < 0
  rw [hneg]
  have : 0 < Module.finrank k Γ(C.subscheme, ⊤) := by
    have := (isField_and_finite_globalSections k fC).2
    exact Module.finrank_pos
  omega

end AlgebraicGeometry

end
