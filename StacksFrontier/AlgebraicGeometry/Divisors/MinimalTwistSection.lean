module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.AlgebraicGeometry.Divisors.MultiplePointCartier

/-!
# The minimality step of [Stacks, Tag 0A27]

Let `X` be a proper curve over a field `k` and `x` a closed point at which `𝒪_{X,x}` is a
discrete valuation ring. If `s` is a global section of `𝒪_X(n·x)` which is not a section of
`𝒪_X`, with `n` minimal with this property, then the germ of `s` at `x` generates the stalk
`(𝒪_X(n·x))_x`. Together with the canonical section `1_{n·x}`, which is nonvanishing exactly off
`x`, it gives a cover of `X` by two charts, and hence `X ∖ {x}` is affine.

## Main definitions

* `Stacks.Divisors.unitToInvertibleSheaf`: the inclusion `𝒪_X ⟶ 𝒪_X(D)`, multiplication by the
  canonical section `1_D`.
* `Stacks.Divisors.invertibleSheafMap`: the inclusion `𝒪_X(D) ⟶ 𝒪_X(D')` induced by a morphism
  `ℐ_{D'} ⟶ ℐ_D` of ideal sheaves.

## Main results

* `Stacks.Divisors.canonicalSections_mem_range_unitToInvertibleSheaf`: `1_D` is a section of
  `𝒪_X`.
* `Stacks.Divisors.unitToInvertibleSheaf_comp_invertibleSheafMap`: the inclusion
  `𝒪_X(D) ⟶ 𝒪_X(D')` lies over the inclusion of `𝒪_X`, as soon as the ideal-sheaf morphism lies
  over the two inclusions `ℐ ⟶ 𝒪_X`.
* `Stacks.Divisors.mem_nonvanishingChart_of_minimal`: the minimality step. If every section
  of `𝒪_X(D)` is a section of `𝒪_X`, if a non-generating germ at `x` forces a section of
  `𝒪_X(D')` to come from `𝒪_X(D)`, and if `s` is a section of `𝒪_X(D')` that is not a section of
  `𝒪_X`, then the germ of `s` at `x` generates `(𝒪_X(D'))_x`.
* `Stacks.Divisors.sup_nonvanishingChart_pair_eq_top`: `1_D` together with any section
  nonvanishing on the support of `D` covers `X`.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_nonvanishingChart`: the inner claim of
  [Stacks, Tag 0A27] from one section whose germ at `x` generates the stalk.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_minimal`: the inner claim of
  [Stacks, Tag 0A27] from a minimal twist.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveSpaceSections

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

section UnitInclusion

variable (D : X.IdealSheafData)

/-- **The inclusion `𝒪_X ⟶ 𝒪_X(D)`**: the unique `𝒪_X`-linear map carrying `1` to the canonical
section `1_D`, i.e. multiplication by `1_D`. -/
noncomputable def unitToInvertibleSheaf :
    _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace) ⟶ invertibleSheaf D :=
  (invertibleSheaf D).unitHomEquiv.symm (canonicalSections D)

/-- **The inclusion `𝒪_X ⟶ 𝒪_X(D)` carries `1` to `1_D`.** -/
theorem unitHomEquiv_unitToInvertibleSheaf :
    (invertibleSheaf D).unitHomEquiv (unitToInvertibleSheaf D) = canonicalSections D :=
  (invertibleSheaf D).unitHomEquiv.apply_symm_apply _

/-- **The canonical section `1_D` is a section of `𝒪_X`**: it is the image of the unit section
under `𝒪_X ⟶ 𝒪_X(D)`. -/
theorem canonicalSections_mem_range_unitToInvertibleSheaf :
    canonicalSections D ∈
      Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf D)) :=
  ⟨(_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)).unitHomEquiv (𝟙 _), by
    rw [← _root_.SheafOfModules.unitHomEquiv_comp_apply, Category.id_comp,
      unitHomEquiv_unitToInvertibleSheaf]⟩

end UnitInclusion

section Monotone

variable {I J : X.IdealSheafData} (g : negativeTwist J ⟶ negativeTwist I)

/-- **The monotone inclusion `𝒪_X(D) ⟶ 𝒪_X(D')`** induced by a morphism `ℐ_{D'} ⟶ ℐ_D` of ideal
sheaves, given by precomposition on `𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)`. -/
noncomputable def invertibleSheafMap : invertibleSheaf I ⟶ invertibleSheaf J :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft X.sheaf.obj g.val⟩

private theorem canonicalSections_eq_sectionsOfTop (K : X.IdealSheafData) :
    canonicalSections K
      = Stacks.SheafOfModules.sectionsOfTopOfRingSheaf (invertibleSheaf K)
          ((restrFun X.sheaf.obj ⊤).map (idealInclusion K).val) := rfl

private theorem sectionsMap_invertibleSheafMap_aux :
    _root_.SheafOfModules.sectionsMap (invertibleSheafMap g) (canonicalSections I)
      = Stacks.SheafOfModules.sectionsOfTopOfRingSheaf (invertibleSheaf J)
          ((restrFun X.sheaf.obj ⊤).map (g ≫ idealInclusion I).val) := by
  have h : (canonicalSections I).eval (op ⊤)
      = (restrFun X.sheaf.obj ⊤).map (idealInclusion I).val :=
    Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top (invertibleSheaf I) _
  refine Stacks.SheafOfModules.sections_ext_of_eval_top (invertibleSheaf J) ?_
  refine Eq.trans (congrArg (fun z => (invertibleSheafMap g).val.app (op ⊤) z) h) ?_
  refine Eq.trans ((restrFun X.sheaf.obj ⊤).map_comp g.val (idealInclusion I).val).symm ?_
  exact (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top (invertibleSheaf J) _).symm

/-- **The monotone inclusion carries `1_D` to `1_{D'}`**, provided the ideal-sheaf morphism `g`
lies over the two inclusions `ℐ ⟶ 𝒪_X`. -/
theorem sectionsMap_invertibleSheafMap_canonicalSections
    (hg : g ≫ idealInclusion I = idealInclusion J) :
    _root_.SheafOfModules.sectionsMap (invertibleSheafMap g) (canonicalSections I)
      = canonicalSections J :=
  (sectionsMap_invertibleSheafMap_aux g).trans
    ((congrArg
      (fun φ : negativeTwist J ⟶ _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace) =>
        Stacks.SheafOfModules.sectionsOfTopOfRingSheaf (invertibleSheaf J)
          ((restrFun X.sheaf.obj ⊤).map φ.val)) hg).trans
      (canonicalSections_eq_sectionsOfTop J).symm)

/-- **The monotone inclusion lies over the inclusion of `𝒪_X`**, provided the ideal-sheaf morphism
`g` lies over the two inclusions `ℐ ⟶ 𝒪_X`. -/
theorem unitToInvertibleSheaf_comp_invertibleSheafMap
    (hg : g ≫ idealInclusion I = idealInclusion J) :
    unitToInvertibleSheaf I ≫ invertibleSheafMap g = unitToInvertibleSheaf J :=
  (_root_.SheafOfModules.unitHomEquiv_symm_comp (canonicalSections I)
      (invertibleSheafMap g)).trans
    (congrArg (invertibleSheaf J).unitHomEquiv.symm
      (sectionsMap_invertibleSheafMap_canonicalSections g hg))

end Monotone

/-- **The minimality step of [Stacks, Tag 0A27].** Let `𝒪_X(D) ⟶ 𝒪_X(D')` be an inclusion lying
over the inclusion of `𝒪_X`, let `x` be a point, and suppose

* `hlocal`: a section of `𝒪_X(D')` whose germ at `x` does not generate `(𝒪_X(D'))_x` comes from
  `𝒪_X(D)`;
* `hmin`: every section of `𝒪_X(D)` is a section of `𝒪_X`;
* `hs`: `s` is a section of `𝒪_X(D')` that is **not** a section of `𝒪_X`.

Then the germ of `s` at `x` generates `(𝒪_X(D'))_x`, which is the membership
`x ∈ nonvanishingChart (𝒪_X(D')) s`. -/
theorem mem_nonvanishingChart_of_minimal {I J : X.IdealSheafData}
    [IsEffectiveCartierDivisor J]
    (incl : invertibleSheaf I ⟶ invertibleSheaf J)
    (hincl : unitToInvertibleSheaf I ≫ incl = unitToInvertibleSheaf J)
    (x : X)
    (hlocal : ∀ t : (invertibleSheaf J).sections,
      x ∉ nonvanishingChart (invertibleSheaf J) t →
        t ∈ Set.range (_root_.SheafOfModules.sectionsMap incl))
    (hmin : ∀ t : (invertibleSheaf I).sections,
      t ∈ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf I)))
    (s : (invertibleSheaf J).sections)
    (hs : s ∉ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf J))) :
    x ∈ nonvanishingChart (invertibleSheaf J) s := by
  by_contra h
  obtain ⟨t, ht⟩ := hlocal s h
  obtain ⟨b, hb⟩ := hmin t
  refine hs ⟨b, ?_⟩
  rw [← hincl, _root_.SheafOfModules.sectionsMap_comp, hb, ht]

/-- **The canonical section and one section nonvanishing on the support of `D` cover `X`.** -/
theorem sup_nonvanishingChart_pair_eq_top (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (s₁ : (invertibleSheaf D).sections)
    (hs₁ : D.supportSet ⊆ (nonvanishingChart (invertibleSheaf D) s₁ : Set X)) :
    (⨆ i : Fin 2, nonvanishingChart (invertibleSheaf D)
      (if i = 0 then canonicalSections D else s₁)) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  rw [Opens.mem_iSup]
  by_cases hy : y ∈ D.supportSet
  · exact ⟨1, hs₁ hy⟩
  · refine ⟨0, ?_⟩
    show y ∈ (nonvanishingChart (invertibleSheaf D) (canonicalSections D) : Set X)
    rw [nonvanishingChart_canonicalSections]
    exact hy

section Engine

variable {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}

/-- **The inner claim of [Stacks, Tag 0A27] from one nonvanishing germ.** Let `X` be a proper
curve over `k`, locally Noetherian and integral, let `x` be a closed point at which `𝒪_{X,x}` is
a discrete valuation ring, and let `s₁` be a global section of `𝒪_X(n·x)` whose germ at `x`
generates the stalk. Then `X ∖ {x}` is affine. -/
theorem isAffineOpen_compl_singleton_of_mem_nonvanishingChart
    [IsLocallyNoetherian X] [IsIntegral X]
    (hf : IsProper f) (hc : IsCurve k f) {x : X} (hx : IsClosed ({x} : Set X))
    {n : ℕ} (hn : 0 < n) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (s₁ : (invertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)).sections)
    (hs₁ : x ∈ nonvanishingChart
      (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) s₁) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) := by
  classical
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n).supportSet
      = ({x} : Set X) := by
    rw [supportSet_pow _ hn]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  refine isAffineOpen_compl_singleton_of_canonicalSections_of_isDiscreteValuationRing
    hf hc hx hn (m := 1)
    (fun i => if i = 0 then
      canonicalSections (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)
      else s₁)
    (sup_nonvanishingChart_pair_eq_top _ s₁ ?_) 0 rfl
  rw [hsupp]
  exact Set.singleton_subset_iff.mpr hs₁

/-- **The inner claim of [Stacks, Tag 0A27] from a minimal twist.** Let `X` be a proper curve
over `k`, locally Noetherian and integral, and let `x` be a closed point at which `𝒪_{X,x}` is a
discrete valuation ring. Given a morphism `g : ℐ_{(p+1)x} ⟶ ℐ_{p·x}` of ideal sheaves lying over
the two inclusions into `𝒪_X`, the local statement that a non-generating germ comes from
`𝒪_X(p·x)`, the statement that every global section of `𝒪_X(p·x)` is a section of `𝒪_X`, and a
global section of `𝒪_X((p+1)x)` that is not a section of `𝒪_X`, the open `X ∖ {x}` is
affine. -/
theorem isAffineOpen_compl_singleton_of_minimal
    [IsLocallyNoetherian X] [IsIntegral X]
    (hf : IsProper f) (hc : IsCurve k f) {x : X} (hx : IsClosed ({x} : Set X))
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {p : ℕ}
    (g : negativeTwist
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)) ⟶
      negativeTwist (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p))
    (hg : g ≫ idealInclusion
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p)
      = idealInclusion
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)))
    (hlocal : ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))).sections,
      x ∉ nonvanishingChart (invertibleSheaf
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))) t →
        t ∈ Set.range (_root_.SheafOfModules.sectionsMap (invertibleSheafMap g)))
    (hmin : ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p)).sections,
      t ∈ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p))))
    (s : (invertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))).sections)
    (hs : s ∉ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))))) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
  isAffineOpen_compl_singleton_of_mem_nonvanishingChart hf hc hx (Nat.succ_pos p) s
    (mem_nonvanishingChart_of_minimal (invertibleSheafMap g)
      (unitToInvertibleSheaf_comp_invertibleSheafMap g hg) x hlocal hmin s hs)

end Engine

end Stacks.Divisors

end
