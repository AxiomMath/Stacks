module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Examples.Schemes.LocalQuotientDegreeM.Ring
public import StacksFrontier.Examples.Schemes.LocalQuotientDegreeM.Values

/-!
# The glued module on the affine plane

This file builds the `𝒪_X`-module `F` on `X = Spec ℚ[x, y]` which is locally a quotient of
`𝒪_X` but is not globally generated.

Write `L` for the line `x = 0`, `Q = i_* i^{-1} 𝒪_X` for the pushforward of the *ordinary*
inverse image of `𝒪_X` along `i : L → X`, and `g = x - y(y-1)` for the equation of the
irreducible curve through `p0 = (0,0)` and `p1 = (0,1)`. The module `F` is obtained by gluing
`Q|_U` and `Q|_V` along multiplication by `g`, for `U = X ∖ {p0}` and `V = X ∖ {p1}`; it is
presented here in the `U`-chart, where a section of `Q` over `W` is a rational function regular
at every point of `W ∩ L`, and the gluing condition is divisibility by `g` at `p0`.

## Main definitions

* `Stacks.Examples.LocalQuotientDegreeM.Fgrp`: the sections of `F` over an open, as a subgroup of
  the function field.
* `Stacks.Examples.LocalQuotientDegreeM.Fpre`: those sections as a presheaf of abelian groups.
* `Stacks.Examples.LocalQuotientDegreeM.Fsheaf`: `F` as a sheaf of `𝒪_X`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Stacks.FractionValue
open PrimeSpectrum (basicOpen)

namespace Stacks.Examples.LocalQuotientDegreeM

attribute [local instance] Classical.propDecidable

/-- The affine plane `X = Spec ℚ[x, y]`. -/
public abbrev Plane : Scheme := Spec (CommRingCat.of Poly)

/-- The generic point of the line `L : x = 0`. -/
public def ptL : PrimeSpectrum Poly := ⟨pL, prime_pL⟩

/-- The point `p0 = (0, 0)`. -/
public def pt0 : PrimeSpectrum Poly := ⟨p0, prime_p0⟩

/-- The point `p1 = (0, 1)`. -/
public def pt1 : PrimeSpectrum Poly := ⟨p1, prime_p1⟩

/-- An open containing a point of the line contains the generic point of the line. -/
public lemma ptL_mem_of_mem {W : Opens (PrimeSpectrum.Top Poly)} {q : PrimeSpectrum Poly}
    (hq : q ∈ W) (hqL : pL ≤ q.asIdeal) : ptL ∈ W :=
  mem_of_le_of_mem hq hqL

/-- An open containing the generic point of the line contains the generic point of the plane.
-/
public lemma genericPt_mem_of_ptL_mem {W : Opens (PrimeSpectrum.Top Poly)} (h : ptL ∈ W) :
    genericPt Poly ∈ W :=
  genericPt_mem h

/-- The condition a section of `F` satisfies at a point of the line: regularity, strengthened to
divisibility by `g` at the points where `y` vanishes. -/
public def Cond (q : PrimeSpectrum Poly) (h : Frac) : Prop :=
  (yv ∉ q.asIdeal → h ∈ Op q.asIdeal) ∧
    (yv ∈ q.asIdeal → ∃ u ∈ Op q.asIdeal, h = algebraMap Poly Frac gpoly * u)

/-- The zero function satisfies the condition `Cond q`. -/
public lemma cond_zero (q : PrimeSpectrum Poly) : Cond q 0 :=
  ⟨fun _ => zero_mem _, fun _ => ⟨0, zero_mem _, by simp⟩⟩

/-- The condition `Cond q` is closed under addition. -/
public lemma cond_add {q : PrimeSpectrum Poly} {h h' : Frac} (hh : Cond q h) (hh' : Cond q h') :
    Cond q (h + h') := by
  refine ⟨fun hy => add_mem (hh.1 hy) (hh'.1 hy), fun hy => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hh.2 hy
  obtain ⟨u', hu', rfl⟩ := hh'.2 hy
  exact ⟨u + u', add_mem hu hu', by ring⟩

/-- The condition `Cond q` is closed under negation. -/
public lemma cond_neg {q : PrimeSpectrum Poly} {h : Frac} (hh : Cond q h) : Cond q (-h) := by
  refine ⟨fun hy => neg_mem (hh.1 hy), fun hy => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hh.2 hy
  exact ⟨-u, neg_mem hu, by ring⟩

/-- The condition `Cond q` is closed under multiplication by elements of `Op q`. -/
public lemma cond_smul {q : PrimeSpectrum Poly} {c h : Frac} (hc : c ∈ Op q.asIdeal)
    (hh : Cond q h) : Cond q (c * h) := by
  refine ⟨fun hy => mul_mem hc (hh.1 hy), fun hy => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hh.2 hy
  exact ⟨c * u, mul_mem hc hu, by ring⟩

/-- The sections of `F` over an open `W`, as a subgroup of the function field. -/
public def Fgrp (W : Opens (PrimeSpectrum.Top Poly)) : AddSubgroup Frac where
  carrier := {h | (∀ q ∈ W, pL ≤ q.asIdeal → Cond q h) ∧ (ptL ∉ W → h = 0)}
  zero_mem' := ⟨fun q _ _ => cond_zero q, fun _ => rfl⟩
  add_mem' hh hh' :=
    ⟨fun q hq hqL => cond_add (hh.1 q hq hqL) (hh'.1 q hq hqL), fun h0 => by
      rw [hh.2 h0, hh'.2 h0, add_zero]⟩
  neg_mem' hh := ⟨fun q hq hqL => cond_neg (hh.1 q hq hqL), fun h0 => by rw [hh.2 h0, neg_zero]⟩

/-- Membership in `Fgrp W`, unfolded. -/
public lemma mem_Fgrp_iff {W : Opens (PrimeSpectrum.Top Poly)} {h : Frac} :
    h ∈ Fgrp W ↔ (∀ q ∈ W, pL ≤ q.asIdeal → Cond q h) ∧ (ptL ∉ W → h = 0) :=
  Iff.rfl

/-- Two sections agreeing as rational functions are equal. -/
public lemma Fgrp_ext {W : Opens (PrimeSpectrum.Top Poly)} {h h' : Fgrp W}
    (e : (h : Frac) = (h' : Frac)) : h = h' := Subtype.ext e

/-- A section over an open missing the line is zero. -/
public lemma Fgrp_eq_zero {W : Opens (PrimeSpectrum.Top Poly)} (hW : ptL ∉ W) (h : Fgrp W) :
    (h : Frac) = 0 :=
  h.2.2 hW

/-- The restriction of a section: the inclusion if the smaller open still meets the line, and
zero otherwise. -/
public def Fres {W W' : Opens (PrimeSpectrum.Top Poly)} (hle : W' ≤ W) : Fgrp W →+ Fgrp W' where
  toFun h := ⟨if ptL ∈ W' then (h : Frac) else 0, by
    refine ⟨fun q hq hqL => ?_, fun h0 => ite_eq_right h0⟩
    by_cases hL : ptL ∈ W'
    · rw [ite_eq_left hL]
      exact h.2.1 q (hle hq) hqL
    · rw [ite_eq_right hL]
      exact cond_zero q⟩
  map_zero' := by
    refine Subtype.ext ?_
    by_cases hL : ptL ∈ W' <;> simp [hL]
  map_add' a b := by
    refine Subtype.ext ?_
    by_cases hL : ptL ∈ W' <;> simp [hL]

/-- Restriction to an open meeting the line is the identity on rational functions. -/
@[simp] public lemma Fres_coe {W W' : Opens (PrimeSpectrum.Top Poly)} (hle : W' ≤ W)
    (hW' : ptL ∈ W') (h : Fgrp W) : ((Fres hle h : Fgrp W') : Frac) = (h : Frac) :=
  ite_eq_left hW'

/-- Restriction to an open missing the line is zero. -/
public lemma Fres_coe_of_notMem {W W' : Opens (PrimeSpectrum.Top Poly)} (hle : W' ≤ W)
    (hW' : ptL ∉ W') (h : Fgrp W) : ((Fres hle h : Fgrp W') : Frac) = 0 :=
  ite_eq_right hW'

/-- The sections of `F` as a presheaf of abelian groups on `X`. -/
public def Fpre : (Opens (PrimeSpectrum.Top Poly))ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (Fgrp W.unop)
  map i := AddCommGrpCat.ofHom (Fres (leOfHom i.unop))
  map_id W := by
    ext h
    change ((Fres le_rfl h : Fgrp W.unop) : Frac) = ((h : Fgrp W.unop) : Frac)
    by_cases hL : ptL ∈ W.unop
    · exact Fres_coe le_rfl hL h
    · rw [Fres_coe_of_notMem _ hL, Fgrp_eq_zero hL h]
  map_comp {W W' W''} i j := by
    ext h
    change ((Fres (leOfHom (i ≫ j).unop) h : Fgrp W''.unop) : Frac) =
      ((Fres (leOfHom j.unop) (Fres (leOfHom i.unop) h) : Fgrp W''.unop) : Frac)
    by_cases hL : ptL ∈ W''.unop
    · rw [Fres_coe _ hL, Fres_coe _ hL, Fres_coe _ (leOfHom j.unop hL)]
    · rw [Fres_coe_of_notMem _ hL, Fres_coe_of_notMem _ hL]

/-- The value of a section of the structure sheaf is regular at every point of its open. -/
public lemma genericValue_mem_Op {W : Opens (PrimeSpectrum.Top Poly)} (s : Sect Poly W)
    {q : PrimeSpectrum Poly} (hq : q ∈ W) : genericValue s ∈ Op q.asIdeal := by
  obtain ⟨a, b, hb, hab⟩ := exists_fraction_genericValue s hq
  exact (mem_Op_iff q.isPrime).2 ⟨a, b, hb, hab⟩

/-- The action of a section of `𝒪_X` on a section of `F`: multiplication in the function field.
-/
public instance smulSect (W : Opens (PrimeSpectrum.Top Poly)) : SMul (Sect Poly W) (Fgrp W) where
  smul s h := ⟨genericValue s * (h : Frac), by
    refine ⟨fun q hq hqL => cond_smul (genericValue_mem_Op s hq) (h.2.1 q hq hqL), fun h0 => ?_⟩
    rw [h.2.2 h0, mul_zero]⟩

/-- The action of a section of `𝒪_X` on a section of `F` is multiplication by its value. -/
@[simp] public lemma smul_coe {W : Opens (PrimeSpectrum.Top Poly)} (s : Sect Poly W)
    (h : Fgrp W) : ((s • h : Fgrp W) : Frac) = genericValue s * (h : Frac) := rfl

/-- The sections of `F` over `W` form a module over the sections of `𝒪_X` over `W`. -/
public instance moduleSect (W : Opens (PrimeSpectrum.Top Poly)) :
    Module (Sect Poly W) (Fgrp W) where
  one_smul h := by
    refine Fgrp_ext ?_
    by_cases hW : genericPt Poly ∈ W
    · rw [smul_coe, genericValue_one hW, one_mul]
    · have hz : (h : Frac) = 0 := Fgrp_eq_zero (fun hL => hW (genericPt_mem_of_ptL_mem hL)) h
      rw [smul_coe, hz, mul_zero]
  mul_smul s t h := by
    refine Fgrp_ext ?_
    by_cases hW : genericPt Poly ∈ W
    · rw [smul_coe, smul_coe, smul_coe, genericValue_mul hW, mul_assoc]
    · have hz : (h : Frac) = 0 := Fgrp_eq_zero (fun hL => hW (genericPt_mem_of_ptL_mem hL)) h
      rw [smul_coe, smul_coe, smul_coe, hz, mul_zero, mul_zero, mul_zero]
  smul_zero s := by
    refine Fgrp_ext ?_
    rw [smul_coe, show ((0 : Fgrp W) : Frac) = 0 from rfl, mul_zero]
  smul_add s h h' := by
    refine Fgrp_ext ?_
    rw [smul_coe, show ((h + h' : Fgrp W) : Frac) = (h : Frac) + (h' : Frac) from rfl,
      show ((s • h + s • h' : Fgrp W) : Frac) = ((s • h : Fgrp W) : Frac) +
        ((s • h' : Fgrp W) : Frac) from rfl, smul_coe, smul_coe, mul_add]
  add_smul s t h := by
    refine Fgrp_ext ?_
    rw [smul_coe, show ((s • h + t • h : Fgrp W) : Frac) = ((s • h : Fgrp W) : Frac) +
      ((t • h : Fgrp W) : Frac) from rfl, smul_coe, smul_coe]
    by_cases hW : genericPt Poly ∈ W
    · rw [genericValue_add hW, add_mul]
    · have hz : (h : Frac) = 0 := Fgrp_eq_zero (fun hL => hW (genericPt_mem_of_ptL_mem hL)) h
      rw [hz, mul_zero, mul_zero, mul_zero, add_zero]
  zero_smul h := by
    refine Fgrp_ext ?_
    rw [smul_coe, genericValue_zero, zero_mul, show ((0 : Fgrp W) : Frac) = 0 from rfl]

/-- The presheaf `Fpre` is a sheaf. -/
public lemma Fpre_isSheaf : TopCat.Presheaf.IsSheaf Fpre := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  by_cases hL : ∃ i, ptL ∈ U i
  · obtain ⟨i₀, hi₀⟩ := hL
    have key : ∀ i, ptL ∈ U i → (sf i).1 = (sf i₀).1 := by
      intro i hi
      have hinf : ptL ∈ U i ⊓ U i₀ := Opens.mem_inf.mpr ⟨hi, hi₀⟩
      calc (sf i).1
          = ((Fres (inf_le_left : U i ⊓ U i₀ ≤ U i) (sf i) : Fgrp (U i ⊓ U i₀)) : Frac) :=
            (Fres_coe _ hinf _).symm
        _ = ((Fres (inf_le_right : U i ⊓ U i₀ ≤ U i₀) (sf i₀) : Fgrp (U i ⊓ U i₀)) : Frac) :=
            Subtype.ext_iff.mp (hsf i i₀)
        _ = (sf i₀).1 := Fres_coe _ hinf _
    have hmem : (sf i₀).1 ∈ Fgrp (iSup U) := by
      refine ⟨fun q hq hqL => ?_, fun h0 => absurd (le_iSup U i₀ hi₀) h0⟩
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hq
      rw [← key i (ptL_mem_of_mem hi hqL)]
      exact (sf i).2.1 q hi hqL
    refine ⟨⟨_, hmem⟩, fun i => Fgrp_ext ?_, fun s' hs' => Fgrp_ext ?_⟩
    · by_cases hi : ptL ∈ U i
      · exact (Fres_coe (le_iSup U i) hi (⟨_, hmem⟩ : Fgrp (iSup U))).trans (key i hi).symm
      · exact (Fres_coe_of_notMem (le_iSup U i) hi (⟨_, hmem⟩ : Fgrp (iSup U))).trans
          (Fgrp_eq_zero hi (sf i)).symm
    · exact (Fres_coe (le_iSup U i₀) hi₀ s').symm.trans (Subtype.ext_iff.mp (hs' i₀))
  · have hsup : ptL ∉ iSup U := fun h => hL (Opens.mem_iSup.mp h)
    have hzero : ∀ i, (sf i).1 = 0 := fun i => Fgrp_eq_zero (fun h => hL ⟨i, h⟩) (sf i)
    refine ⟨0, fun i => Fgrp_ext ?_, fun s' _ => Fgrp_ext ?_⟩
    · exact (congrArg Subtype.val (map_zero (Fres (le_iSup U i)))).trans (hzero i).symm
    · exact Fgrp_eq_zero hsup s'

/-- Restriction of sections of `F` is compatible with the action of sections of `𝒪_X`. -/
public lemma Fpre_smul_res {W W' : Opens (PrimeSpectrum.Top Poly)} (hle : W' ≤ W)
    (r : Sect Poly W) (m : Fgrp W) :
    Fres hle (r • m) =
      ((Spec.structureSheaf Poly).presheaf.map (homOfLE hle).op r) • Fres hle m := by
  refine Fgrp_ext ?_
  by_cases hL : ptL ∈ W'
  · rw [Fres_coe _ hL, smul_coe, smul_coe, Fres_coe _ hL,
      genericValue_res hle (genericPt_mem_of_ptL_mem hL) r]
  · rw [Fres_coe_of_notMem _ hL, smul_coe, Fres_coe_of_notMem _ hL, mul_zero]

/-- The module `F`, as a sheaf of `𝒪_X`-modules on `X = Spec ℚ[x, y]`. -/
public def Fsheaf : SheafOfModules Plane.ringCatSheaf where
  val := @PresheafOfModules.ofPresheaf _ _ Plane.ringCatSheaf.obj Fpre
    (fun W => moduleSect W.unop) (fun {_ _} i r m => Fpre_smul_res (leOfHom i.unop) r m)
  isSheaf := Fpre_isSheaf

end Stacks.Examples.LocalQuotientDegreeM

end
