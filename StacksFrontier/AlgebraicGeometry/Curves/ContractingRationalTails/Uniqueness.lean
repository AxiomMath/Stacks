module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Terminal
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.ContractedTail

/-!
# Uniqueness of the contraction of all rational tails

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, with
at-worst-nodal singularities and of genus at least one. Contracting rational tails until none
are left gives a morphism `X ⟶ X'` which does not depend on the choices made: two such chains
are related by a unique isomorphism of their targets under `X`. This is the uniqueness
statement of [Stacks, Tag 0E3L].

## Main results

All in the namespace `AlgebraicGeometry`:

* `subsingleton_range_of_isRationalTail_of_forall_not_isRationalTail`: a
  morphism `c : X ⟶ Y` over `k` with `𝒪_Y = c_*𝒪_X`, onto a nodal curve of positive genus without
  rational tails, maps every rational tail of `X` to a point.
* `IsIteratedContractionOfRationalTails.exists_comp_eq_of_forall_not_isRationalTail`:
  such a morphism factors through every chain of contractions of rational tails.
* `IsIteratedContractionOfRationalTails.existsUnique_iso`: [Stacks, Tag 0E3L],
  independence of choices.

## Implementation notes

The source shows that `c` contracts a rational tail `C` using sections of `ω_{X'}^{⊗ 2}` and
[Stacks, Tag 0E63]. Here the argument is the Euler characteristic computation of
`Stacks.Curves.StableModel.subsingleton_range_of_isRationalTail`: if `c(C) = D` is a curve, then
`χ(𝒪_D) ≥ χ(𝒪_{D ∩ Y'})` with `Y'` the closure of `Y ∖ D`, which forces `D` to be a rational tail
of `Y` (`AlgebraicGeometry.isRationalTail_of_finrank_globalSections_intersection_eq_one`), or
`D = Y` and `χ(𝒪_Y) > 0`, against `g ≥ 1`.

## References

* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3J](https://stacks.math.columbia.edu/tag/0E3J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Curves.StableModel

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- A nonempty scheme proper over `k` has nonzero finite-dimensional global functions. -/
theorem finrank_globalSections_pos {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
    [Nonempty S] :
    letI : Algebra k Γ(S, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    0 < Module.finrank k Γ(S, ⊤) := by
  let : Algebra k Γ(S, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have := Stacks.EmptyLimitCounterexample.nontrivial_Γ_of_nonempty S (Classical.arbitrary S)
  have := forall_finiteDimensional_cohomologyOverField_unit k f 0
  have : FiniteDimensional k Γ(S, ⊤) := Module.Finite.equiv
    (cohomologyOverFieldZeroIsoSections k f (SheafOfModules.unit S.ringCatSheaf)).toLinearEquiv
  exact Module.finrank_pos

/-- If `c ≫ g = f`, where `c` is an isomorphism on global functions and `f` identifies `k` with
the global functions of its source, then so does `g`. -/
theorem isIso_globalSections_of_comp {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} (c : X ⟶ Y)
    (g : Y ⟶ Spec (.of k)) (hcomp : c ≫ g = f)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hc : IsIso c.appTop) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := by
  have h1 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (c ≫ g).appTop) := by
    rw [hcomp]
    infer_instance
  rw [Scheme.Hom.comp_appTop, ← Category.assoc] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (c.appTop) _ h1

/-- A closed subscheme whose support is at most a point is a subsingleton. -/
theorem subsingleton_subscheme_of_support_subset_singleton {Y : Scheme.{u}}
    {I : Y.IdealSheafData} {y : Y} (h : (I.support : Set Y) ⊆ {y}) : Subsingleton I.subscheme := by
  refine ⟨fun a b => I.subschemeι.isClosedEmbedding.injective ?_⟩
  have hmem (w : I.subscheme) : I.subschemeι w = y :=
    h (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩)
  rw [hmem a, hmem b]

/-- Under a surjective morphism, the images of a closed subscheme and of the closure of its
complement cover the target. -/
theorem range_union_range_complementaryCurveIdeal {X Y : Scheme.{u}} (C : X.IdealSheafData)
    (c : X ⟶ Y) [Surjective c] (y : Y) :
    y ∈ Set.range (C.subschemeι ≫ c) ∨
      y ∈ Set.range ((complementaryCurveIdeal C).subschemeι ≫ c) := by
  obtain ⟨p, rfl⟩ := c.surjective y
  rcases (support_union_support_complementaryCurveIdeal C ▸ Set.mem_univ p :
    p ∈ (C.support : Set X) ∪ (complementaryCurveIdeal C).support) with hp | hp
  · obtain ⟨q, rfl⟩ := (Scheme.IdealSheafData.range_subschemeι _ ▸ hp : _ ∈ Set.range _)
    exact Or.inl ⟨q, rfl⟩
  · obtain ⟨q, rfl⟩ := (Scheme.IdealSheafData.range_subschemeι _ ▸ hp : _ ∈ Set.range _)
    exact Or.inr ⟨q, rfl⟩

/-- The support of the kernel of a proper morphism is its range. -/
private theorem support_ker_eq_range {W Y : Scheme.{u}} (f : W ⟶ Y) [IsProper f] :
    (f.ker.support : Set Y) = Set.range f := by
  rw [Scheme.Hom.support_ker]
  exact f.isClosedMap.isClosed_range.closure_eq

/-- The scheme-theoretic image of an integral scheme under a proper morphism to a scheme of
dimension at most one is an integral curve, unless the image is a point. -/
theorem isIntegral_ker_and_topologicalKrullDim_eq_one {T Y : Scheme.{u}} [IsIntegral T]
    (h : T ⟶ Y) [IsProper h] (hYdim : topologicalKrullDim Y ≤ 1)
    (hns : ¬ (Set.range h).Subsingleton) :
    IsIntegral h.ker.subscheme ∧ topologicalKrullDim h.ker.subscheme = 1 := by
  have hsupp := support_ker_eq_range h
  have : IsReduced h.ker.subscheme := Scheme.Hom.isReduced_image h
  have : IrreducibleSpace h.ker.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme Y h.ker (by
      rw [Scheme.IdealSheafData.range_subschemeι, hsupp, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ T).image h h.continuous.continuousOn)
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, le_antisymm
    (h.ker.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hYdim)
    (one_le_topologicalKrullDim_of_not_subsingleton _ fun hsub => hns ?_)⟩
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  have hmem (x : T) : h x ∈ Set.range h.ker.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
    exact ⟨x, rfl⟩
  obtain ⟨a', ha'⟩ := hmem a
  obtain ⟨b', hb'⟩ := hmem b
  rw [← ha', ← hb', Subsingleton.elim a' b']

/-- **A curve with the Euler characteristic of a nonempty finite scheme has genus zero.** If
`H⁰(Y, 𝒪_Y) = k` and `χ(𝒪_Y) = χ(𝒪_Z)` for a nonempty closed subscheme `Z` of dimension zero,
then `Y` has genus zero. -/
theorem genus_eq_zero_of_finsum_finrank_unit_eq {Y : Scheme.{u}} (gY : Y ⟶ Spec (.of k))
    [IsProper gY] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop)]
    (hYdim : topologicalKrullDim Y ≤ 1) (Z : Y.IdealSheafData) [Nonempty Z.subscheme]
    (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hYZ : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k gY
        (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (Z.subschemeι ≫ gY) (SheafOfModules.unit Z.subscheme.ringCatSheaf) n) : ℤ)) :
    genus gY = 0 := by
  let : Algebra k Γ(Z.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ gY).appTop).hom.toAlgebra
  have hZχ := finsum_alternating_finrank_unit_eq_finrank_of_topologicalKrullDim_le_zero
    (Z.subschemeι ≫ gY) hZ
  have hpos : 0 < Module.finrank k Γ(Z.subscheme, ⊤) :=
    finrank_globalSections_pos k (Z.subschemeι ≫ gY)
  have hYχ := finsum_finrank_unit_eq_mul_one_sub_genus k gY hYdim gY (by simp)
  rw [Module.finrank_self, Nat.cast_one, one_mul] at hYχ
  have hpos' : (0 : ℤ) < Module.finrank k Γ(Z.subscheme, ⊤) := by exact_mod_cast hpos
  have : (genus gY : ℤ) < 1 := by linarith
  omega

/-- **`χ(𝒪_{D ∩ Y'}) ≤ χ(𝒪_D)`.** Let `D` and `Z` be closed subschemes covering a scheme `Y` of
dimension at most one, proper over `k`, such that `D ∩ Z` has dimension zero and
`χ(𝒪_Y) = χ(𝒪_Z)`. Then `χ(𝒪_{D ∩ Y'}) ≤ χ(𝒪_D)`, where `Y'` is the closure of `Y ∖ D`. -/
theorem finsum_finrank_unit_intersection_le {Y : Scheme.{u}} (gY : Y ⟶ Spec (.of k))
    [IsProper gY] [IsReduced Y] (hYdim : topologicalKrullDim Y ≤ 1) {D Z : Y.IdealSheafData}
    (hcov : ∀ y : Y, y ∈ (D.support : Set Y) ∨ y ∈ (Z.support : Set Y))
    (hdim : topologicalKrullDim (D ⊔ Z).subscheme ≤ 0)
    (hYZ : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k gY
        (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (Z.subschemeι ≫ gY) (SheafOfModules.unit Z.subscheme.ringCatSheaf) n) : ℤ)) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        ((D ⊔ complementaryCurveIdeal D).subschemeι ≫ gY)
        (SheafOfModules.unit (D ⊔ complementaryCurveIdeal D).subscheme.ringCatSheaf) n) : ℤ) ≤
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (D.subschemeι ≫ gY) (SheafOfModules.unit D.subscheme.ringCatSheaf) n) : ℤ) := by
  have hDZ : D ⊓ Z = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine le_antisymm le_top fun y _ => ?_
    rcases hcov y with hy | hy
    · exact Scheme.IdealSheafData.support_antitone inf_le_left hy
    · exact Scheme.IdealSheafData.support_antitone inf_le_right hy
  have hZY' : Z ≤ complementaryCurveIdeal D := by
    change Z ≤ (Scheme.Opens.ι D.support.compl).ker
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    refine closure_minimal (fun y hy => ?_) Z.support.isClosed
    rw [Scheme.Opens.range_ι] at hy
    exact (hcov y).resolve_left hy
  have hun := finsum_finrank_unit_add_of_inf_eq_bot k gY hYdim hDZ
  have hle := finsum_finrank_unit_le_of_le k gY (sup_le_sup_left hZY' D) hdim
  linarith

private theorem eq_one_and_eq_zero_of_mul_le_mul_one_sub {d a g : ℕ} (hpos : 0 < d * a)
    (h : ((d * a : ℕ) : ℤ) ≤ d * (1 - g)) : a = 1 ∧ g = 0 := by
  have hd : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have ha : 0 < a := Nat.pos_of_mul_pos_left hpos
  push_cast at h
  have hsum : (a : ℤ) + g ≤ 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  omega

/-- **A curve `D ≠ Y` with `χ(𝒪_{D ∩ Y'}) ≤ χ(𝒪_D)` is a rational tail.** Let `Y` be proper of
dimension at most one over `k` with `H⁰(Y, 𝒪_Y) = k`, and `D ≠ Y` a one-dimensional integral
closed subscheme with `χ(𝒪_{D ∩ Y'}) ≤ χ(𝒪_D)`, where `Y'` is the closure of `Y ∖ D`. Writing
`k' = Γ(D, 𝒪_D)`, this reads `[k' : k] dim_{k'} Γ(D ∩ Y', 𝒪) ≤ [k' : k](1 - g')`, so `D ∩ Y'` is
one `k'`-point and `D` has genus zero. -/
theorem isRationalTail_of_finsum_finrank_unit_le {Y : Scheme.{u}} (gY : Y ⟶ Spec (.of k))
    [IsProper gY] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop)]
    (hYdim : topologicalKrullDim Y ≤ 1) (D : Y.IdealSheafData) [IsIntegral D.subscheme]
    (hDdim : topologicalKrullDim D.subscheme = 1) (hDY : (D.support : Set Y) ≠ Set.univ)
    (hχ : ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        ((D ⊔ complementaryCurveIdeal D).subschemeι ≫ gY)
        (SheafOfModules.unit (D ⊔ complementaryCurveIdeal D).subscheme.ringCatSheaf) n) : ℤ) ≤
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (D.subschemeι ≫ gY) (SheafOfModules.unit D.subscheme.ringCatSheaf) n) : ℤ)) :
    @IsRationalTail k _ Y ⟨gY⟩ D := by
  let : Y.Over (Spec (.of k)) := ⟨gY⟩
  have : IsProper (Y ↘ Spec (.of k)) := inferInstanceAs (IsProper gY)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian gY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace gY
  have : IsNoetherian Y := ⟨⟩
  have : ConnectedSpace Y := connectedSpace_of_isIso_globalSections k gY
  set fD := D.subschemeι ≫ gY
  let : Field Γ(D.subscheme, ⊤) := (isField_of_universallyClosed k fD).toField
  let : Algebra k Γ(D.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fD.appTop).hom.toAlgebra
  have : IsProper D.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fD
  have : IsIso ((Scheme.ΓSpecIso (.of Γ(D.subscheme, ⊤))).inv ≫
      D.subscheme.toSpecΓ.appTop) := by rw [Scheme.toSpecΓ_appTop]; infer_instance
  have hf : D.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(D.subscheme, ⊤))) =
      D.subschemeι ≫ (Y ↘ Spec (.of k)) := by
    change D.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ fD.appTop) = fD
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have hDχ := finsum_finrank_unit_eq_mul_one_sub_genus Γ(D.subscheme, ⊤) fD hDdim.le
    D.subscheme.toSpecΓ hf
  let I := intersectionWithComplementaryCurveIdeal D
  let : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (Y ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra Γ(D.subscheme, ⊤) Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of Γ(D.subscheme, ⊤))).inv ≫ (Scheme.IdealSheafData.inclusion
      (le_sup_left : D ≤ I) ≫ D.subscheme.toSpecΓ).appTop).hom.toAlgebra
  have : Nonempty I.subscheme := nonempty_intersectionWithComplementaryCurve_of_connectedSpace D
    ⟨D.subschemeι (Classical.arbitrary _), D.range_subschemeι ▸ ⟨_, rfl⟩⟩ hDY
  have hIχ := finsum_alternating_finrank_unit_eq_finrank_of_topologicalKrullDim_le_zero
    (I.subschemeι ≫ (Y ↘ Spec (.of k)))
    (topologicalKrullDim_intersectionWithComplementaryCurve_le_zero hYdim D)
  have hmul := finrank_globalSections_intersection_eq_mul D Γ(D.subscheme, ⊤)
    D.subscheme.toSpecΓ hf
  have hpos : 0 < Module.finrank k Γ(I.subscheme, ⊤) :=
    finrank_globalSections_pos k (I.subschemeι ≫ (Y ↘ Spec (.of k)))
  have hineq : (Module.finrank k Γ(I.subscheme, ⊤) : ℤ) ≤
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) * (1 - genus D.subscheme.toSpecΓ) := by
    rw [← hDχ]
    change _ ≤ ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
      (D.subschemeι ≫ gY) (SheafOfModules.unit D.subscheme.ringCatSheaf) n) : ℤ)
    rw [← hIχ]
    change ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
      ((D ⊔ complementaryCurveIdeal D).subschemeι ≫ gY)
      (SheafOfModules.unit (D ⊔ complementaryCurveIdeal D).subscheme.ringCatSheaf) n) : ℤ) ≤ _
    linarith
  rw [hmul] at hpos hineq
  obtain ⟨h1, h2⟩ := eq_one_and_eq_zero_of_mul_le_mul_one_sub hpos hineq
  exact isRationalTail_of_finrank_globalSections_intersection_eq_one hYdim D hDdim
    (nonempty_complementaryCurve_of_support_ne_univ D hDY) Γ(D.subscheme, ⊤)
    D.subscheme.toSpecΓ h1 h2

/-- **A morphism onto a curve of positive genus without rational tails contracts every rational
tail.** Let `X` be a proper nodal curve over `k` with `H⁰(X, 𝒪_X) = k`, `C` a rational tail of
`X`, and `c : X ⟶ Y` a morphism over `k` with `𝒪_Y = c_*𝒪_X`, where `Y` is proper of dimension
one over `k`, at worst nodal, of genus at least one and without rational tails. Then `c(C)` is
a point.

Otherwise `D = c(C)` is an integral curve. With `Z` the image of the closure `X'` of `X ∖ C`, the
ideal of `Z` has `χ = 0` and `D ∩ Z` is at most a point, so `χ(𝒪_D) = χ(𝒪_{D ∩ Z}) ≥ χ(𝒪_{D ∩ Y'})`
where `Y'` is the closure of `Y ∖ D`. If `D ≠ Y`, writing `k' = Γ(D, 𝒪_D)` this reads
`[k' : k](1 - g') ≥ [k' : k] dim_{k'} Γ(D ∩ Y', 𝒪) ≥ [k' : k]`, so `D` is a rational tail of `Y`.
If `D = Y`, then `Z` is a nonempty finite scheme and `1 - g = χ(𝒪_Y) = χ(𝒪_Z) > 0`. -/
theorem subsingleton_range_of_isRationalTail_of_forall_not_isRationalTail {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) {gY : Y ⟶ Spec (.of k)} [IsProper gY]
    {c : X ⟶ Y} (hcomp : c ≫ gY = X ↘ Spec (.of k))
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hYdim : topologicalKrullDim Y = 1)
    (hYnodal : letI : Y.Over (Spec (.of k)) := ⟨gY⟩
      Stacks.Curves.HasAtWorstNodalSingularities k Y)
    (hYtail : ∀ D : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨gY⟩ D)
    (hgenus : 1 ≤ genus gY) :
    (Set.range (C.subschemeι ≫ c)).Subsingleton := by
  by_contra hns
  have : IsProper (c ≫ gY) := hcomp ▸ inferInstance
  have : IsProper c := IsProper.of_comp c gY
  have hiso : ∀ U : Y.Opens, IsIso (c.app U) :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO
  have : Surjective c := c.surjective_of_isIso_app hiso
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim := Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC
  have : IsLocallyNoetherian C.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.subschemeι ≫ (X ↘ Spec (.of k)))
  have : CompactSpace C.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (C.subschemeι ≫ (X ↘ Spec (.of k)))
  have : IsNoetherian C.subscheme := ⟨⟩
  set h := C.subschemeι ≫ c
  have : IsFinite h := h.isFinite_of_not_subsingleton_range hCdim.le hns
  let : Y.Over (Spec (.of k)) := ⟨gY⟩
  have : IsProper (Y ↘ Spec (.of k)) := inferInstanceAs (IsProper gY)
  have : IsReduced Y := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k Y hYnodal
  have := isIso_globalSections_of_comp k c gY hcomp (hiso ⊤)
  obtain ⟨_, hDdim⟩ := isIntegral_ker_and_topologicalKrullDim_eq_one h hYdim.le hns
  set Z := ((complementaryCurveIdeal C).subschemeι ≫ c).ker
  set D := h.ker
  have hYZ := finsum_finrank_unit_eq_add_idealPowerMultiple k gY hYdim.le Z
  rw [finsum_idealPowerMultiple_ker_comp_eq_zero k hdim hnodal hC gY c hcomp hO, zero_add] at hYZ
  have hsuppD : (D.support : Set Y) = Set.range h := support_ker_eq_range h
  have hsuppZ : (Z.support : Set Y) = Set.range ((complementaryCurveIdeal C).subschemeι ≫ c) :=
    support_ker_eq_range _
  have hcov (y : Y) : y ∈ (D.support : Set Y) ∨ y ∈ (Z.support : Set Y) :=
    hsuppD ▸ hsuppZ ▸ range_union_range_complementaryCurveIdeal C c y
  have hint := range_inter_range_subset_singleton hC c hiso hCdim.le hns
  by_cases hDY : (D.support : Set Y) = Set.univ
  · obtain ⟨p⟩ := hC.complementaryCurve_nonempty
    obtain ⟨w, -⟩ : ((complementaryCurveIdeal C).subschemeι ≫ c) p ∈ Set.range Z.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hsuppZ]
      exact ⟨p, rfl⟩
    have : Nonempty Z.subscheme := ⟨w⟩
    have : Subsingleton Z.subscheme := subsingleton_subscheme_of_support_subset_singleton
      fun y hy => hint ⟨hsuppD ▸ (hDY ▸ Set.mem_univ y : y ∈ (D.support : Set Y)), hsuppZ ▸ hy⟩
    have := genus_eq_zero_of_finsum_finrank_unit_eq k gY hYdim.le Z
      (topologicalKrullDim_le_zero_of_subsingleton Z.subscheme) hYZ
    omega
  · have : Subsingleton (D ⊔ Z).subscheme := subsingleton_subscheme_of_support_subset_singleton
      fun y hy => by
        rw [Scheme.IdealSheafData.support_sup] at hy
        exact hint ⟨hsuppD ▸ hy.1, hsuppZ ▸ hy.2⟩
    exact hYtail D (isRationalTail_of_finsum_finrank_unit_le k gY hYdim.le D hDdim hDY
      (finsum_finrank_unit_intersection_le k gY hYdim.le hcov
        (topologicalKrullDim_le_zero_of_subsingleton _) hYZ))

namespace IsIteratedContractionOfRationalTails

variable {k}

/-- **A morphism onto a curve of positive genus without rational tails factors through every
chain of contractions of rational tails.** Let `t : X ⟶ X₁` be a chain of contractions of rational
tails of a proper nodal curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, and `c : X ⟶ Y` a morphism over
`k` with `𝒪_Y = c_*𝒪_X`, where `Y` is a proper nodal curve over `k` of genus at least one without
rational tails. Then `c = t ≫ c'` with `c'` over `k` and `𝒪_Y = c'_*𝒪_{X₁}`: each contracted tail
goes to a point under `c`
(`AlgebraicGeometry.subsingleton_range_of_isRationalTail_of_forall_not_isRationalTail`), so `c`
factors through the contraction (`Stacks.Curves.StableModel.contraction_comp_eq_of_factors`). -/
theorem exists_comp_eq_of_forall_not_isRationalTail {X X₁ Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {f₁ : X₁ ⟶ Spec (.of k)} {t : X ⟶ X₁}
    (hseq : IsIteratedContractionOfRationalTails k fX f₁ t) (hproper : IsProper fX)
    (hdim : topologicalKrullDim X = 1) (hglob : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    {gY : Y ⟶ Spec (.of k)} [IsProper gY] (hYdim : topologicalKrullDim Y = 1)
    (hYnodal : letI : Y.Over (Spec (.of k)) := ⟨gY⟩
      Stacks.Curves.HasAtWorstNodalSingularities k Y)
    (hYtail : ∀ D : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨gY⟩ D)
    (hgenus : 1 ≤ genus gY) {c : X ⟶ Y} (hcomp : c ≫ gY = fX)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    ∃ c' : X₁ ⟶ Y, t ≫ c' = c ∧ c' ≫ gY = f₁ ∧
      IsIso (SheafOfModules.unitToPushforwardObjUnit c'.toRingCatSheafHom) := by
  induction hseq with
  | identity X fX => exact ⟨c, Category.id_comp c, hcomp, hO⟩
  | @step X X₁ X₂ fX f₁ f₂ c₁ d C hC e hc hbase hd ih =>
    let : X.Over (Spec (.of k)) := ⟨fX⟩
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglob
    -- the one-step chain
    have h1 : IsIteratedContractionOfRationalTails k fX f₁ (c₁ ≫ 𝟙 X₁) :=
      .step C hC e hc hbase (.identity X₁ f₁)
    have : IsProper fX := hproper
    have := hglob
    have hO₁ := h1.isIso_unitToPushforwardObjUnit hdim hnodal
    rw [Category.comp_id] at hO₁
    -- `c` contracts `C`, hence factors through `c₁`
    have hsub := subsingleton_range_of_isRationalTail_of_forall_not_isRationalTail k hdim hnodal
      hC hcomp hO hYdim hYnodal hYtail hgenus
    have hfac := exists_comp_eq_canonicalMapToAttachingPoint k X hC c hsub
    have hcomp' := contraction_comp_eq_of_factors k X hdim hnodal hC hc c hfac
    set c₂ := e.inv ≫ complementaryCurveι C ≫ c
    have hc₂ : c₁ ≫ c₂ = c := by
      rw [← hcomp']
      simp only [c₂, Category.assoc]
    have hc₂O : IsIso (SheafOfModules.unitToPushforwardObjUnit c₂.toRingCatSheafHom) :=
      isIso_unitToPushforwardObjUnit_of_comp c₁ c₂ hO₁ (hc₂ ▸ hO)
    have hc₂g : c₂ ≫ gY = f₁ := by
      have hiso : IsIso c₁.appTop :=
        Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₁ hO₁ ⊤
      refine ext_of_isAffine ((cancel_mono c₁.appTop).1 ?_)
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Category.assoc, hc₂, hcomp,
        hbase]
    obtain ⟨c', hc', hc'g, hc'O⟩ := ih (h1.isProper_target hdim hnodal)
      (h1.topologicalKrullDim_target hdim hnodal) (h1.isIso_globalSections_target hdim hnodal)
      (h1.hasAtWorstNodalSingularities_target hdim hnodal) hc₂g hc₂O
    exact ⟨c', by rw [Category.assoc, hc', hc₂], hc'g, hc'O⟩

/-- Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`,
at-worst-nodal singularities and genus at least one. For two chains `c₁ : X ⟶ Y₁` and
`c₂ : X ⟶ Y₂` of contractions of rational tails after which none are left, there is a unique
isomorphism `e : Y₁ ≅ Y₂` with `c₁ ≫ e = c₂`. -/
@[stacks 0E3L "independence of choices"]
theorem existsUnique_iso {X Y₁ Y₂ : Scheme.{u}} {fX : X ⟶ Spec (.of k)}
    {fY₁ : Y₁ ⟶ Spec (.of k)} {fY₂ : Y₂ ⟶ Spec (.of k)} {c₁ : X ⟶ Y₁} {c₂ : X ⟶ Y₂}
    [IsProper fX] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hgenus : 1 ≤ genus fX)
    (hseq₁ : IsIteratedContractionOfRationalTails k fX fY₁ c₁)
    (hterminal₁ : ∀ C : Y₁.IdealSheafData, ¬ @IsRationalTail k _ Y₁ ⟨fY₁⟩ C)
    (hseq₂ : IsIteratedContractionOfRationalTails k fX fY₂ c₂)
    (hterminal₂ : ∀ C : Y₂.IdealSheafData, ¬ @IsRationalTail k _ Y₂ ⟨fY₂⟩ C) :
    ∃! e : Y₁ ≅ Y₂, c₁ ≫ e.hom = c₂ := by
  have : IsProper fY₁ := hseq₁.isProper_target hdim hnodal
  have : IsProper fY₂ := hseq₂.isProper_target hdim hnodal
  obtain ⟨d, hd, -, -⟩ := hseq₁.exists_comp_eq_of_forall_not_isRationalTail inferInstance hdim
    inferInstance hnodal (hseq₂.topologicalKrullDim_target hdim hnodal)
    (hseq₂.hasAtWorstNodalSingularities_target hdim hnodal) hterminal₂
    (hgenus.trans_eq (hseq₂.genus_target hdim hnodal).symm) hseq₂.comp_structureMap
    (hseq₂.isIso_unitToPushforwardObjUnit hdim hnodal)
  obtain ⟨d', hd', -, -⟩ := hseq₂.exists_comp_eq_of_forall_not_isRationalTail inferInstance hdim
    inferInstance hnodal (hseq₁.topologicalKrullDim_target hdim hnodal)
    (hseq₁.hasAtWorstNodalSingularities_target hdim hnodal) hterminal₁
    (hgenus.trans_eq (hseq₁.genus_target hdim hnodal).symm) hseq₁.comp_structureMap
    (hseq₁.isIso_unitToPushforwardObjUnit hdim hnodal)
  -- morphisms out of `Yᵢ` are determined after composing with `cᵢ`
  have hext : ∀ {Y Y' : Scheme.{u}} {fY : Y ⟶ Spec (.of k)} {fY' : Y' ⟶ Spec (.of k)}
      {c : X ⟶ Y}, IsIteratedContractionOfRationalTails k fX fY c → IsProper fY' →
      ∀ {a b : Y ⟶ Y'}, c ≫ a = c ≫ b → a = b := by
    intro Y Y' fY fY' c hseq _ a b hab
    let : Y.Over (Spec (.of k)) := ⟨fY⟩
    have : IsProper (Y ↘ Spec (.of k)) := hseq.isProper_target hdim hnodal
    have : IsReduced Y := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k Y
      (hseq.hasAtWorstNodalSingularities_target hdim hnodal)
    have : IsDominant c := c.isDominant_of_isIso_unitToPushforwardObjUnit
      (hseq.isIso_unitToPushforwardObjUnit hdim hnodal)
    exact ext_of_isDominant_of_isSeparated fY'
      (ext_of_isDominant c (by rw [← Category.assoc, ← Category.assoc, hab])) c hab
  have h12 : d ≫ d' = 𝟙 Y₁ := hext hseq₁ (inferInstance : IsProper fY₁)
    (by rw [← Category.assoc, hd, hd', Category.comp_id])
  have h21 : d' ≫ d = 𝟙 Y₂ := hext hseq₂ (inferInstance : IsProper fY₂)
    (by rw [← Category.assoc, hd', hd, Category.comp_id])
  exact ⟨⟨d, d', h12, h21⟩, hd, fun e he =>
    Iso.ext (hext hseq₁ (inferInstance : IsProper fY₂) (he.trans hd.symm))⟩

end IsIteratedContractionOfRationalTails

end AlgebraicGeometry

end
