/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.BouquetRing
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FundamentalSystemOfIdealsOfDefinitionExistence
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionColimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpaceDisjointGlue
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpaceDouble
public import StacksFrontier.AlgebraicGeometry.FormalScheme.PowerSeriesFormalSpectrum

/-!
# A twisted double of `Spf R⟦X⟧` over the bouquet ring

For the local ring `R` of `AlgebraicGeometry.BouquetRing`, whose spectrum is a closed point and the
points `q n` with `D(y n) = {q n}`, let `Y = Spf R⟦X⟧` with the `X`-adic topology. Its points are
those of `Spec R`. The basic opens `pt n = D(y n)` of `Y` are pairwise disjoint single points. Over
`pt n` the substitution `X ↦ X - ε n` is an automorphism `σ n` of `Y`; glued over the disjoint
union `W = ⨆ pt n`, these give an automorphism `φ` of `Y|_W`, the identity on points.

The twisted double `𝔛` is two copies of `Y` glued along `W` by `φ`. It is a quasi-compact formal
scheme à la EGA. Its points are the two closed points `o b` of the copies and the points `η n` of
`W`. Each point has a smallest open neighbourhood: a copy of `Y` for `o b`, and the point itself
for `η n`.

## Main definitions

* `AlgebraicGeometry.TwistedDouble.Y`: the formal spectrum of `R⟦X⟧`.
* `AlgebraicGeometry.TwistedDouble.pt`: the basic open `D(y n)` of `Y`, the single point `q n`.
* `AlgebraicGeometry.TwistedDouble.φ`: the automorphism of `Y|_W` that is `X ↦ X - ε n` over
  `pt n`.
* `AlgebraicGeometry.TwistedDouble.𝔛`: the twisted double, as a formal scheme à la EGA.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.TwistedDouble

open LocallyTopologicallyRingedSpace PowerSeriesFormalSpectrum

open PowerSeries (X C)

/-- The topological ring `R⟦X⟧`, `X`-adically, over the bouquet ring `R`. -/
noncomputable abbrev A : TopCommRingCat.{0} := ring BouquetRing.R

/-- The formal spectrum `Y = Spf R⟦X⟧` over the bouquet ring `R`. -/
noncomputable abbrev Y : LTRS.{0} := spfLTRS A.α (isPreAdmissible BouquetRing.R)

/-- The basic open `D(y n)` of `Y`, the single point `q n`. -/
noncomputable def pt (n : ℕ) : Opens Y := spfBasicOpen A.α (C (BouquetRing.y n))

/-- A point of `Y` lies in `pt n` exactly when it corresponds to the point `q n` of `Spec R`. -/
theorem mem_pt_iff (n : ℕ) (p : Y) : p ∈ pt n ↔ pointsEquiv p = BouquetRing.q n :=
  (pointsEquiv_mem_spfBasicOpen_C (BouquetRing.y n) p).trans (BouquetRing.mem_basicOpen_y_iff n _)

/-- The opens `pt n` are pairwise disjoint. -/
theorem pt_disjoint : Pairwise fun i j => pt i ⊓ pt j = ⊥ := by
  intro i j hij
  refine eq_bot_iff.mpr fun p hp => ?_
  have hi := (mem_pt_iff i p).mp hp.1
  have hj := (mem_pt_iff j p).mp hp.2
  exact (hij (BouquetRing.q_injective (hi.symm.trans hj))).elim

/-- The open `W = ⨆ pt n` of `Y`, along which the two copies are glued. -/
noncomputable abbrev W : Opens Y := iSup pt

/-- The nilpotent `ε n` of the bouquet ring. -/
theorem isNilpotent_ε (n : ℕ) : IsNilpotent (BouquetRing.ε n) :=
  ⟨n + 1, BouquetRing.ε_pow_succ n⟩

/-- The automorphism `σ n` of `Y` given by the substitution `X ↦ X - ε n`. -/
noncomputable def σ (n : ℕ) : Y ≅ Y := aut (BouquetRing.ε n) (isNilpotent_ε n)

/-- The automorphism `σ n` is the identity on points. -/
theorem σ_base (n : ℕ) (p : Y) : (σ n).hom.toHom.base p = p :=
  aut_base _ _ p

/-- The automorphism `φ` of `Y|_W`, which is `σ n` over `pt n`. -/
noncomputable def φ : Y.restrict W ≅ Y.restrict W :=
  disjointGlueIso pt pt_disjoint σ σ_base

/-- The automorphism `φ` is the identity on points. -/
theorem φ_base (p : Y.restrict W) : φ.hom.toHom.base p = p :=
  disjointGlue_base pt _ σ_base pt_disjoint p

/-- The twisted double of `Y` along `W`, an object of `LTRS`. -/
noncomputable def D : LTRS.{0} := double Y W φ φ_base

/-- `Y = Spf R⟦X⟧` is quasi-compact. -/
instance : CompactSpace Y := compactSpace_spfSpace A.α (isPreAdmissible BouquetRing.R)

/-- The twisted double `D` is quasi-compact, being covered by two copies of `Y`. -/
instance : CompactSpace D := compactSpace_double Y W φ φ_base

/-- The twisted double is a formal scheme à la EGA. -/
theorem isFormalScheme_D : IsFormalScheme D :=
  isFormalScheme_double Y W φ φ_base (isFormalScheme_spfLTRS A.α (isAdmissible BouquetRing.R))

/-- **The twisted double `𝔛`**, a quasi-compact formal scheme à la EGA. -/
noncomputable def 𝔛 : FormalScheme.{0} := ⟨D, isFormalScheme_D⟩

/-- The underlying space of `𝔛` is quasi-compact. -/
instance : CompactSpace 𝔛.obj := inferInstanceAs (CompactSpace D)

/-! ### The two charts and the points of `W` -/

/-- The open of `D` which is the `b`-th copy of `Y`. -/
noncomputable def U (b : Bool) : Opens D := doubleOpen Y W φ φ_base b

/-- The chart of `D` over `U b`: the restriction of `D` to `U b` is `Spf R⟦X⟧`. -/
noncomputable def e (b : Bool) :
    D.toPresheafedSpace.restrict (f := (U b).inclusion') (U b).isOpenEmbedding' ≅ Spf A.α :=
  doubleChartIso Y W φ φ_base b

/-- The inclusion `Y ⟶ D` of the `b`-th copy, through the chart `e b`. -/
noncomputable def h (b : Bool) : Y ⟶ D := spfChartHom (isPreAdmissible BouquetRing.R) (e b)

/-- The inclusion through the chart is the inclusion of the `b`-th copy of `Y` into the double. -/
theorem h_eq (b : Bool) : h b = doubleι Y W φ φ_base b :=
  Hom.ext' (doubleChartIso_inv_comp_ofRestrict Y W φ φ_base b)

/-- The inclusion `h b` of the `b`-th copy of `Y` is an open immersion. -/
instance (b : Bool) : PresheafedSpace.IsOpenImmersion (h b).toHom := by
  rw [h_eq]; exact isOpenImmersion_doubleι Y W φ φ_base b

/-- Two points of the two copies of `Y` agree in `D` exactly when they are the same point of `Y`,
lying in `W` unless the copies are the same. -/
theorem h_base_eq_iff {b b' : Bool} {x x' : Y} :
    (h b).toHom.base x = (h b').toHom.base x' ↔ x = x' ∧ (b = b' ∨ x ∈ W) := by
  rw [h_eq, h_eq]; exact doubleι_base_eq_iff Y W φ φ_base

/-- Every point of `D` lies in one of the two copies of `Y`. -/
theorem exists_h_base_eq (z : D) : ∃ b x, (h b).toHom.base x = z := by
  simp only [h_eq]; exact exists_doubleι_base_eq Y W φ φ_base z

/-- A point of `D` lies in `U b` exactly when it lies in the `b`-th copy of `Y`. -/
theorem mem_U_iff (b : Bool) (z : D) : z ∈ U b ↔ ∃ x, (h b).toHom.base x = z := by
  rw [h_eq]; exact Iff.rfl

/-- The open `U b` is an affine formal open of `D`. -/
theorem isAffineFormalOpen_U (b : Bool) : IsAffineFormalOpen D (U b) :=
  ⟨A, inferInstance, isAdmissible BouquetRing.R, ⟨e b⟩⟩

/-- The open `U b` is quasi-compact. -/
theorem isCompact_U (b : Bool) : IsCompact (U b : Set D) :=
  isCompact_of_spfChart (isPreAdmissible BouquetRing.R) (e b)

/-- The open `pt n` lies in `W`. -/
theorem pt_le_W (n : ℕ) : pt n ≤ W := le_iSup pt n

/-- The point `η n` of `D`: the image of `pt n` in either copy of `Y`. -/
noncomputable def η (n : ℕ) : Opens D :=
  ⟨(h false).toHom.base '' (pt n : Set Y),
    (PresheafedSpace.IsOpenImmersion.base_open (f := (h false).toHom)).isOpenMap _ (pt n).2⟩

/-- A point of the `b`-th copy of `Y` lies in `η n` exactly when it lies in `pt n`. -/
theorem h_base_mem_η_iff (b : Bool) (n : ℕ) (x : Y) : (h b).toHom.base x ∈ η n ↔ x ∈ pt n := by
  constructor
  · rintro ⟨x', hx', hx'x⟩
    obtain ⟨rfl, -⟩ := h_base_eq_iff.mp hx'x
    exact hx'
  · exact fun hx => ⟨x, hx, h_base_eq_iff.mpr ⟨rfl, Or.inr (pt_le_W n hx)⟩⟩

/-- The preimage of `η n` in either copy of `Y` is `pt n`. -/
theorem map_h_η (b : Bool) (n : ℕ) : (Opens.map (h b).toHom.base).obj (η n) = pt n :=
  Opens.ext (Set.ext fun x => h_base_mem_η_iff b n x)

/-- The point `η n` lies in both copies of `Y`. -/
theorem η_le_U (b : Bool) (n : ℕ) : η n ≤ U b := by
  rintro z ⟨x, hx, rfl⟩
  exact (mem_U_iff b _).mpr ⟨x, h_base_eq_iff.mpr ⟨rfl, Or.inr (pt_le_W n hx)⟩⟩

/-! ### The twist over `pt n` -/

/-- The inclusion of `pt n` into `Y`, through `Y|_W`. -/
noncomputable def k (n : ℕ) : (Y.restrict W).restrict (disjointGlueCover pt n) ⟶ Y :=
  (Y.restrict W).ofRestrict (disjointGlueCover pt n) ≫ Y.ofRestrict W

/-- The inclusion `k n` of `pt n` into `Y` is an open immersion. -/
instance (n : ℕ) : PresheafedSpace.IsOpenImmersion (k n).toHom := by
  change PresheafedSpace.IsOpenImmersion
    ((Y.restrict W).toPresheafedSpace.ofRestrict (disjointGlueCover pt n).isOpenEmbedding ≫
      Y.toPresheafedSpace.ofRestrict W.isOpenEmbedding)
  exact PresheafedSpace.IsOpenImmersion.comp
    (H := PresheafedSpace.IsOpenImmersion.ofRestrict (Y.restrict W).toPresheafedSpace
      (disjointGlueCover pt n).isOpenEmbedding) _
    (hg := PresheafedSpace.IsOpenImmersion.ofRestrict Y.toPresheafedSpace W.isOpenEmbedding)

/-- The range of the inclusion `k n` is `pt n`. -/
theorem range_k (n : ℕ) : Set.range (k n).toHom.base = (pt n : Set Y) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · exact fun hx => ⟨⟨⟨x, pt_le_W n hx⟩, hx⟩, rfl⟩

/-- **The twist over `pt n`.** On `pt n` the two inclusions of `Y` into `D` differ by `σ n`. -/
theorem k_comp_h_true (n : ℕ) : k n ≫ h true = k n ≫ (σ n).hom ≫ h false := by
  rw [h_eq, h_eq, k]
  calc ((Y.restrict W).ofRestrict (disjointGlueCover pt n) ≫ Y.ofRestrict W) ≫
        doubleι Y W φ φ_base true
      = (Y.restrict W).ofRestrict (disjointGlueCover pt n) ≫ φ.hom ≫ Y.ofRestrict W ≫
          doubleι Y W φ φ_base false := by
        rw [Category.assoc, ofRestrict_comp_doubleι_true]
    _ = ((Y.restrict W).ofRestrict (disjointGlueCover pt n) ≫ φ.hom ≫ Y.ofRestrict W) ≫
          doubleι Y W φ φ_base false := by simp only [Category.assoc]
    _ = ((Y.restrict W).ofRestrict (disjointGlueCover pt n) ≫ Y.ofRestrict W ≫ (σ n).hom) ≫
          doubleι Y W φ φ_base false := by
        rw [show (Y.restrict W).ofRestrict (disjointGlueCover pt n) ≫ φ.hom ≫ Y.ofRestrict W =
          _ from ofRestrict_comp_disjointGlue_comp_ofRestrict pt (fun i => (σ i).hom) σ_base
            pt_disjoint n]
    _ = _ := by simp only [Category.assoc]; rfl

end AlgebraicGeometry.TwistedDouble

end
