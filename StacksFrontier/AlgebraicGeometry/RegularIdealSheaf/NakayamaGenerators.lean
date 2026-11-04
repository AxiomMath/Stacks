module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ImmersionStalk
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange

/-!
# Nakayama generators for the defining ideal sheaf of an immersion

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes.  This file collects the facts about
defining ideal sheaves and their stalks that compare the ideal of `i ≫ j` with that of `j`:
the inclusion between the two ideal sheaves, a common open over which both immersions are
closed, Nakayama's lemma for the stalk of an ideal sheaf in the form that lifts a basis of the
cotangent fibre `J_x / 𝔪_x J_x`, the passage from such a lift to generators on a neighbourhood,
and the linear algebra of extending a basis through an injective map.

## Main results

* `definingIdealOfHom_le_comp`: the defining ideal sheaf of `j` is contained in that of the
  composite `i ≫ j`.
* `exists_isClosedImmersion_resLE_comp`: an open of `X` around `j (i z)` over which `j` and,
  inside its preimage, `i` both restrict to closed immersions, together with the stability of
  both conditions under shrinking that open.
* `stalkIdeal_eq_span_of_span_idealCotangentFiber`: **Nakayama for the stalk of an ideal
  sheaf.**  Elements of a finitely generated stalk `J_x` whose classes span the cotangent fibre
  `J_x / 𝔪_x J_x` generate `J_x`.
* `exists_isGeneratedByOn_definingIdealOfHom`: sections of the defining ideal sheaf of an
  immersion locally of finite presentation whose germs generate one stalk generate the ideal
  sheaf on a neighbourhood of that point.
* `exists_basis_sum_of_injective`: a basis of a subspace extends to a basis of the ambient
  finite-dimensional space, indexed by a sum type.

## Implementation notes

`exists_isGeneratedByOn_definingIdealOfHom` assumes the immersion quasi-compact in addition to
being locally of finite presentation.  The finite generating family on a neighbourhood that the
shrinking argument consumes is produced from Stacks tag 01TV: over an affine open inside the
coborder of the range the immersion restricts to a closed immersion, so that tag makes the
kernel of the map on sections finitely generated, and quasi-compactness identifies that kernel
with the sections of the defining ideal sheaf.

## References

* [Stacks Project, Lemma 29.21.7 (Tag 01TV)](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Lemma 10.20.1 (Tag 00DV)](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

section Composite

/-- **The defining ideal sheaf grows along a composite.**  A section of `𝒪_X` killed by
`𝒪_X ⟶ j_* 𝒪_Y` is killed by `𝒪_X ⟶ (i ≫ j)_* 𝒪_Z`, since the latter factors through the
former. -/
theorem definingIdealOfHom_le_comp {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) :
    definingIdealOfHom j ≤ definingIdealOfHom (i ≫ j) := by
  refine SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr ?_)
  intro V s hs
  have hs0 : (j.app V.unop).hom s = 0 := hs
  show (i.app (j ⁻¹ᵁ V.unop)).hom ((j.app V.unop).hom s) = 0
  rw [hs0, map_zero]

end Composite

section ClosedRestriction

/-- Alias of `AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange`. -/
private alias isClosedImmersion_resLE :=
  AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange

/-- **A common open over which two composable immersions are both closed.**  For immersions
`i : Z ⟶ Y` and `j : Y ⟶ X` and a point `z` of `Z` there is an open `U` of `X` containing
`j (i z)` such that over every open `U' ≤ U` the morphism `j` restricts to a closed immersion
into `U'` and `i` restricts to a closed immersion into `j ⁻¹ U'`. -/
theorem exists_isClosedImmersion_resLE_comp {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (z : Z) :
    ∃ U : X.Opens, j.base (i.base z) ∈ U ∧ ∀ U' : X.Opens, U' ≤ U →
      IsClosedImmersion (j.resLE U' (j ⁻¹ᵁ U') le_rfl) ∧
        IsClosedImmersion (i.resLE (j ⁻¹ᵁ U') (i ⁻¹ᵁ (j ⁻¹ᵁ U')) le_rfl) := by
  obtain ⟨A, hA, hpre⟩ := j.isEmbedding.isInducing.isOpen_iff.mp i.coborderRange.isOpen
  have hiz : i.base z ∈ i.coborderRange := subset_coborder ⟨z, rfl⟩
  refine ⟨(⟨A, hA⟩ : X.Opens) ⊓ j.coborderRange,
    ⟨hpre.superset hiz, subset_coborder ⟨i.base z, rfl⟩⟩, fun U' hU' => ⟨?_, ?_⟩⟩
  · exact isClosedImmersion_resLE j U' (le_trans hU' inf_le_right)
  · refine isClosedImmersion_resLE i (j ⁻¹ᵁ U') fun y hy => hpre.subset (hU' hy).1

end ClosedRestriction

section Nakayama

variable {X : LocallyRingedSpace.{u}}
  (J : (structureSheafModule X.toRingedSpace).Submodule)

/-- **Nakayama's lemma for the stalk of an ideal sheaf.**  Elements of a finitely generated
stalk `J_x` whose classes span the cotangent fibre `J_x / 𝔪_x J_x` over the residue field
generate `J_x`. -/
theorem stalkIdeal_eq_span_of_span_idealCotangentFiber {x : X} (hfg : (stalkIdeal J x).FG)
    {n : ℕ} (f : Fin n → stalkIdeal J x)
    (hspan : Submodule.span (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Set.range fun a => (Submodule.Quotient.mk (f a) : idealCotangentFiber J x)) = ⊤) :
    stalkIdeal J x = Ideal.span (Set.range fun a => (f a : X.presheaf.stalk x)) := by
  classical
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)) hfg
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal
        (⊥ : Ideal (X.presheaf.stalk x)) bot_ne_top).symm) fun a ha => ?_
    have hmem : (Submodule.Quotient.mk (⟨a, ha⟩ : stalkIdeal J x) : idealCotangentFiber J x)
        ∈ Submodule.span (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (Set.range fun b => (Submodule.Quotient.mk (f b) : idealCotangentFiber J x)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
    choose lam hlam using fun b => Ideal.Quotient.mk_surjective
      (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (c b)
    have hq : (Submodule.Quotient.mk
        ((⟨a, ha⟩ : stalkIdeal J x) - ∑ b, lam b • f b) : idealCotangentFiber J x) = 0 := by
      rw [← Submodule.mkQ_apply, map_sub, map_sum, sub_eq_zero]
      simp only [Submodule.mkQ_apply]
      rw [← hc]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hlam b, Module.Quotient.mk_smul_mk]
    have hsmul := (Submodule.Quotient.mk_eq_zero _).mp hq
    rw [Submodule.mem_smul_top_iff] at hsmul
    have hcoe : (((⟨a, ha⟩ : stalkIdeal J x) - ∑ b, lam b • f b : stalkIdeal J x) :
        X.presheaf.stalk x) = a - ∑ b, lam b • (f b : X.presheaf.stalk x) := by
      rw [Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [hcoe] at hsmul
    refine Submodule.mem_sup.mpr ⟨∑ b, lam b • (f b : X.presheaf.stalk x),
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Ideal.subset_span ⟨b, rfl⟩),
      a - ∑ b, lam b • (f b : X.presheaf.stalk x), hsmul, by ring⟩
  · rintro _ ⟨b, rfl⟩
    exact (f b).2

end Nakayama

section Generation

/-- The kernel of the map on sections over an affine open inside the coborder of the range of an
immersion locally of finite presentation is generated by finitely many sections. -/
private theorem exists_span_ker_app {Y X : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j]
    [LocallyOfFinitePresentation j] {V : X.Opens} (hV : IsAffineOpen V)
    (hVc : V ≤ j.coborderRange) :
    ∃ (r : ℕ) (g : Fin r → Γ(X, V)), RingHom.ker (j.app V).hom = Ideal.span (Set.range g) := by
  have _ : IsAffine V.toScheme := hV
  have hCI : IsClosedImmersion (j.resLE V (j ⁻¹ᵁ V) le_rfl) := isClosedImmersion_resLE j V hVc
  have hfg := (locallyOfFinitePresentation_iff_fg_ker (j.resLE V (j ⁻¹ᵁ V) le_rfl)).mp
    inferInstance ⟨⊤, isAffineOpen_top V.toScheme⟩
  rw [Scheme.Hom.ker_apply] at hfg
  -- the map on global sections of the restriction is the map on sections over `V`, read through
  -- the identifications of the sections of an open subscheme
  have hinj : Function.Injective ((j ⁻¹ᵁ V).topIso.inv.hom) :=
    ((j ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv).injective
  have hsurj : Function.Surjective (V.topIso.hom.hom) :=
    (V.topIso.commRingCatIsoToRingEquiv).surjective
  have happ : ∀ s : Γ(V.toScheme, ⊤),
      ((j.resLE V (j ⁻¹ᵁ V) le_rfl).app ⊤).hom s
        = (j ⁻¹ᵁ V).topIso.inv.hom ((j.app V).hom (V.topIso.hom.hom s)) := fun s => by
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
    rfl
  have hker : RingHom.ker ((j.resLE V (j ⁻¹ᵁ V) le_rfl).app ⊤).hom
      = Ideal.comap V.topIso.hom.hom (RingHom.ker (j.app V).hom) := by
    refine Submodule.ext fun s => ?_
    simp only [RingHom.mem_ker, Ideal.mem_comap, happ s]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h]; exact map_zero _⟩
  rw [hker] at hfg
  obtain ⟨t, ht⟩ := hfg
  have hker2 : RingHom.ker (j.app V).hom
      = Ideal.span (V.topIso.hom.hom '' (t : Set (Γ(V.toScheme, ⊤)))) := by
    rw [← Ideal.map_span, ht, Ideal.map_comap_of_surjective _ hsurj]
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hker2 ▸ Submodule.fg_span (t.finite_toSet.image _) :
      (RingHom.ker (j.app V).hom).FG)
  exact ⟨r, g, hg.symm⟩

/-- **Sections generating one stalk of the defining ideal sheaf generate it near that point.**
Let `j : Y ⟶ X` be a quasi-compact immersion locally of finite presentation, let `x` be a point
of `X` lying in the coborder of the range of `j`, and let `f₁, …, f_n` be sections of the
defining ideal sheaf of `j` over an open `U ∋ x` whose germs generate the stalk at `x`.  Then
the `f_i` generate the defining ideal sheaf on a neighbourhood of `x` inside `U`. -/
theorem exists_isGeneratedByOn_definingIdealOfHom {Y X : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j]
    [QuasiCompact j] [LocallyOfFinitePresentation j] {x : X} (hx : x ∈ j.coborderRange)
    {U : X.Opens} (hxU : x ∈ U) {n : ℕ} (f : Fin n → Γ(X, U))
    (hf : ∀ a, f a ∈ (definingIdealOfHom j).obj (op U))
    (hgen : stalkIdeal (X := X.toLocallyRingedSpace) (definingIdealOfHom j) x
      = Jid (germFamily X.toRingedSpace U f x hxU)) :
    ∃ (U' : X.Opens) (_ : x ∈ U') (hU' : U' ≤ U),
      IsGeneratedByOn X.toRingedSpace (definingIdealOfHom j) U'
        (fun a => X.presheaf.map (homOfLE hU').op (f a)) := by
  obtain ⟨V, hV, hxV, hVc⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) hx
  obtain ⟨r, g, hg⟩ := exists_span_ker_app j hV hVc
  exact exists_isGeneratedByOn_of_stalkIdeal_eq (X := X.toLocallyRingedSpace)
    (definingIdealOfHom j) hxV g
    (Stacks.AlgebraicGeometry.isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span j hV g hg)
    hxU f hf hgen

end Generation

section BasisExtension

/-- **Extending a basis through an injective map.**  If `φ : V →ₗ[k] W` is injective and `W` is
finite dimensional, a basis of `V` indexed by `Fin n` is the `Fin n` part of a basis of `W`
indexed by `Fin n ⊕ Fin m`. -/
theorem exists_basis_sum_of_injective {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {n : ℕ} (φ : V →ₗ[k] W)
    (hφ : Function.Injective φ) (bV : Module.Basis (Fin n) k V) :
    ∃ (m : ℕ) (bW : Module.Basis (Fin n ⊕ Fin m) k W), ∀ a, bW (Sum.inl a) = φ (bV a) := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range φ)
  refine ⟨Module.finrank k C,
    ((bV.map (LinearEquiv.ofInjective φ hφ)).prod (Module.finBasis k C)).map
      (Submodule.prodEquivOfIsCompl _ _ hC), fun a => ?_⟩
  rw [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl',
    Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd]
  simp

end BasisExtension

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
