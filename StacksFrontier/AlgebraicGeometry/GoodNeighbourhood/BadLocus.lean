module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.SmoothAtRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.ZeroSchemeStalkRegular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The singular locus of a normal variety has codimension at least two

Let `X` be an integral normal scheme locally of finite type over an algebraically closed field
`k`, containing a nonempty open `W` smooth of relative dimension `d`. Every point `z` of `X` at
which `X` is not smooth of relative dimension `d` has dimension `δ(z) ≤ d - 2`. Indeed a point of
dimension `d - 1` has a one-dimensional normal local ring, which is a discrete valuation ring,
hence regular, so `X` is smooth there (`k` is perfect), of relative dimension `d` because `X` is
irreducible of dimension `d`. This is the input `R₁` of the Bertini argument of SGA 4, Exposé XI,
3.3: the curve `C` cut out by `d - 1` general sections misses the singular locus.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.relativeDimension_genericPoint_eq_of_opens`: the
  dimension of `X` is `d`.
* `AlgebraicGeometry.GoodNeighbourhood.relativeDimension_add_two_le_of_not_subschemeSmoothAt_bot`:
  the singular locus has dimension at most `d - 2`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Stacks.Chow IsLocalRing

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- A point whose closure is an irreducible component of an irreducible scheme is its generic
point. -/
private theorem eq_genericPoint_of_closure_mem_irreducibleComponents {Y : Scheme.{u}}
    [IrreducibleSpace Y] {x : Y} (h : closure {x} ∈ irreducibleComponents Y) :
    x = genericPoint Y := by
  rw [irreducibleComponents_eq_singleton] at h
  have hx : IsGenericPoint x Set.univ := h
  exact hx.eq (genericPoint_spec Y)

/-- **The dimension of an integral scheme containing a nonempty open smooth of relative dimension
`d` is `d`**, read at its generic point. -/
theorem relativeDimension_genericPoint_eq_of_opens [LocallyOfFiniteType p] [IsIntegral X]
    (W : X.Opens) [Nonempty W] (d : ℕ) [SmoothOfRelativeDimension d (W.ι ≫ p)] :
    relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint X) = d := by
  have h1 := relativeDimension_genericPoint_of_smoothOfRelativeDimension d (W.ι ≫ p)
  rw [relativeDimension_opensι_comp] at h1
  have hc := closure_singleton_mem_irreducibleComponents_of_isOpenImmersion W.ι
  rw [← eq_genericPoint_of_closure_mem_irreducibleComponents hc]
  exact h1

/-- **A normal integral scheme over an algebraically closed field is smooth of the right
relative dimension away from a closed set of dimension at most `d - 2`.** -/
theorem relativeDimension_add_two_le_of_not_subschemeSmoothAt_bot [IsAlgClosed k]
    [LocallyOfFiniteType p] [IsIntegral X] [IsNormal X] (W : X.Opens) [Nonempty W] (d : ℕ)
    [SmoothOfRelativeDimension d (W.ι ≫ p)] (z : X)
    (hz : ¬ SubschemeSmoothAt p (⊥ : X.IdealSheafData) d z) :
    relativeDimension (fieldChowSituation k).dimensionFunction p z + 2 ≤ d := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hgen := relativeDimension_genericPoint_eq_of_opens p W d
  have hgenW : genericPoint X ∈ W := by
    obtain ⟨w⟩ := ‹Nonempty W›
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨w.1, Set.mem_univ _, w.2⟩
  have : Smooth (W.ι ≫ p) := SmoothOfRelativeDimension.smooth d _
  by_contra hlt
  push Not at hlt
  apply hz
  -- the local ring at `z` is regular
  have hreg : IsRegularLocalRing (X.presheaf.stalk z) := by
    by_cases hzW : z ∈ W
    · have hsmz : InfinitesimalLifting.SmoothAt p z := by
        refine ⟨W, hzW, ?_⟩
        have h := Scheme.Hom.resLE_comp_ι p (U := ⊤) (V := W) le_top
        have h' : Smooth (p.resLE ⊤ W le_top ≫ (⊤ : (Spec (.of k)).Opens).ι) := by
          rw [h]; infer_instance
        have : IsIso (⊤ : (Spec (.of k)).Opens).ι :=
          inferInstanceAs (IsIso (Scheme.topIso (Spec (.of k))).hom)
        have he : p.resLE ⊤ W le_top = (p.resLE ⊤ W le_top ≫ (⊤ : (Spec (.of k)).Opens).ι) ≫
            inv (⊤ : (Spec (.of k)).Opens).ι := by simp
        rw [he]
        exact MorphismProperty.comp_mem @Smooth _ _ h' inferInstance
      have hz' : z ∈ {x : X | InfinitesimalLifting.SmoothAt p x} := hsmz
      rw [smoothAt_locus_eq_regular_locus k p] at hz'
      exact hz'
    · have hne : z ≠ genericPoint X := fun h => hzW (h ▸ hgenW)
      have hmem : z ∈ closure ({genericPoint X} : Set X) := by
        rw [(genericPoint_spec X).def]; trivial
      have hlt' : relativeDimension (fieldChowSituation k).dimensionFunction p z <
          relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint X) :=
        relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) p hmem hne
      have hcomp : ∀ W' : irreducibleComponents X,
          relativeDimension (fieldChowSituation k).dimensionFunction p W'.2.1.genericPoint =
            (d : ℤ) := by
        intro W'
        have hg := W'.2.1.isGenericPoint_genericPoint
          (isClosed_of_mem_irreducibleComponents _ W'.2)
        have hmem : closure {W'.2.1.genericPoint} ∈ irreducibleComponents X := by
          rw [hg.def]; exact W'.2
        rw [eq_genericPoint_of_closure_mem_irreducibleComponents hmem, hgen]
      have hdim := ringKrullDim_stalk_eq_toNat_sub_relativeDimension (fieldChowSituation k) p
        hcomp z
      have hδ : (d : ℤ) - relativeDimension (fieldChowSituation k).dimensionFunction p z = 1 := by
        omega
      rw [hδ] at hdim
      set R := X.presheaf.stalk z
      have : IsIntegrallyClosed R := IsNormal.stalk_normal z
      have hdim1 : ringKrullDim R = 1 := by rw [hdim]; rfl
      have hnf : ¬ IsField R := fun hf => by
        have := ringKrullDim_eq_zero_of_isField hf
        rw [hdim1] at this
        exact absurd this (by norm_num)
      have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by rw [hdim1]; rfl)
      have hm : maximalIdeal R ≠ ⊥ := fun h => hnf ((isField_iff_maximalIdeal_eq).mpr h)
      have htfae : IsDiscreteValuationRing R ↔
          (IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime) :=
        (IsDiscreteValuationRing.TFAE R hnf).out 1 4
      have hdvr : IsDiscreteValuationRing R :=
        htfae.mpr ⟨inferInstance, maximalIdeal R,
          ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
            (hP.2.isMaximal_of_ne_bot hP.1)⟩
      infer_instance
  -- transport to the closed subscheme `⊥`, which is `X`
  have : IsIso (⊥ : X.IdealSheafData).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr rfl
  set e := asIso (⊥ : X.IdealSheafData).subschemeι
  set s := e.inv z
  have hsz : (⊥ : X.IdealSheafData).subschemeι s = z := by
    show (e.inv ≫ e.hom) z = z
    rw [Iso.inv_hom_id]
    rfl
  have hregS : IsRegularLocalRing ((⊥ : X.IdealSheafData).subscheme.presheaf.stalk s) :=
    isRegularLocalRing_stalk_of_iso e.symm z
  have hsmS : InfinitesimalLifting.SmoothAt ((⊥ : X.IdealSheafData).subschemeι ≫ p) s := by
    have hs : s ∈ {x : (⊥ : X.IdealSheafData).subscheme |
        IsRegularLocalRing ((⊥ : X.IdealSheafData).subscheme.presheaf.stalk x)} := hregS
    rw [← smoothAt_locus_eq_regular_locus k ((⊥ : X.IdealSheafData).subschemeι ≫ p)] at hs
    exact hs
  have hirr : IrreducibleSpace (⊥ : X.IdealSheafData).subscheme :=
    (Scheme.homeoOfIso e).irreducibleSpace_iff.mpr inferInstance
  have he : ∀ η : (⊥ : X.IdealSheafData).subscheme, η ⤳ s →
      closure ({η} : Set (⊥ : X.IdealSheafData).subscheme) ∈
        irreducibleComponents (⊥ : X.IdealSheafData).subscheme →
      relativeDimension (fieldChowSituation k).dimensionFunction p
        ((⊥ : X.IdealSheafData).subschemeι η) = d := by
    intro η _ hη
    rw [irreducibleComponents_eq_singleton] at hη
    have hcl : closure ({η} : Set (⊥ : X.IdealSheafData).subscheme) = Set.univ := hη
    have hgη : IsGenericPoint ((⊥ : X.IdealSheafData).subschemeι η) Set.univ := by
      show closure {(Scheme.homeoOfIso e) η} = Set.univ
      rw [← Set.image_singleton, ← (Scheme.homeoOfIso e).image_closure, hcl, Set.image_univ,
        (Scheme.homeoOfIso e).range_coe]
    rw [hgη.eq (genericPoint_spec X), hgen]
  have := subschemeSmoothAt_of_smoothAt p ⊥ s hsmS d he
  rwa [hsz] at this

end AlgebraicGeometry.GoodNeighbourhood

end
