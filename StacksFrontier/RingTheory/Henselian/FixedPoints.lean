module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.RingTheory.Henselian.Criteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fixed points of a henselian local ring under a group acting trivially on the residue field

Let `S` be a local ring and let a group `G` act on `S` by ring automorphisms. The subring `S ^ G`
of fixed points is again local, with maximal ideal `𝔪_S ∩ S ^ G`, because the inverse of a fixed
unit is fixed.

Assume moreover that `G` acts trivially on the residue field of `S`, i.e. that `σ x - x ∈ 𝔪_S`
for every `σ ∈ G` and `x ∈ S` — in the language of `Ideal.inertia` this says that `G` is its own
inertia subgroup at `𝔪_S`. Then a simple root in `S` of a monic polynomial with coefficients in
`S ^ G` is automatically fixed by `G`, because `σ` carries it to a root in the same residue class
and the henselian root is unique there. Consequently `S ^ G` inherits henselianness from `S`, and
its residue field inherits separable closedness.

## Main results

* `Stacks.FixedPoints.isLocalRing`: the fixed subring of a local ring is local.
* `Stacks.FixedPoints.maximalIdeal_eq`: its maximal ideal is the contraction of `𝔪_S`.
* `Stacks.FixedPoints.exists_isRoot_of_isUnit_derivative`: a simple root in `S` of a monic
  polynomial over `S ^ G` lies in `S ^ G`.
* `Stacks.FixedPoints.henselianLocalRing`: the fixed subring of a henselian local ring is
  henselian.
* `Stacks.FixedPoints.isSepClosed_residueField`: its residue field is separably closed when that
  of `S` is.
* `Subring.mulSemiringActionOfStable`: a subring stable under the action carries the restricted
  action, with `Stacks.FixedPoints.mem_fixedPoints_subring_of_stable` identifying its fixed
  points. This is how the results above are applied to a localization sitting inside a field on
  which the group acts.

## Implementation notes

The inertia hypothesis is written out as `∀ (σ : G) (x : S), σ • x - x ∈ maximalIdeal S` rather
than as `(maximalIdeal S).inertia G = ⊤`, so that it can be supplied without first producing a
`Subgroup` equality; `Ideal.mem_inertia` turns one into the other.

Uniqueness of the henselian root is `hensel_uniqueness` (Stacks 06RR), which holds in any local
ring. Only existence uses `HenselianLocalRing S`.

## References

* [Stacks Project, Tag 06RR](https://stacks.math.columbia.edu/tag/06RR)
* [Stacks Project, Tag 04GE](https://stacks.math.columbia.edu/tag/04GE)

## Tags

fixed points, invariants, henselian local ring, inertia, residue field, separably closed
-/

@[expose] public section

universe u v

open IsLocalRing Polynomial

namespace Stacks.FixedPoints

variable (S : Type u) [CommRing S] (G : Type v) [Group G] [MulSemiringAction G S]

/-- The inclusion of the fixed subring into `S`. -/
abbrev subtypeHom : _root_.FixedPoints.subring S G →+* S :=
  (_root_.FixedPoints.subring S G).subtype

variable {S G}

/-- A fixed element which is a unit of `S` is a unit of the fixed subring: the inverse of a
fixed element is fixed, by uniqueness of inverses. -/
theorem isUnit_of_isUnit_val {a : _root_.FixedPoints.subring S G} (ha : IsUnit (a : S)) :
    IsUnit a := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hbmem : b ∈ _root_.FixedPoints.subring S G := by
    intro σ
    calc σ • b = σ • b * ((a : S) * b) := by rw [hb, mul_one]
      _ = σ • ((a : S) * b) * b := by rw [smul_mul', a.2 σ]; ring
      _ = b := by rw [hb, smul_one, one_mul]
  exact isUnit_iff_exists_inv.mpr ⟨⟨b, hbmem⟩, Subtype.ext hb⟩

/-- An element of the fixed subring is a unit there exactly when it is a unit of `S`. -/
theorem isUnit_val_iff {a : _root_.FixedPoints.subring S G} :
    IsUnit (a : S) ↔ IsUnit a :=
  ⟨isUnit_of_isUnit_val, fun h => h.map (subtypeHom S G)⟩

variable (S G)

/-- **The fixed subring of a local ring is local.** An element outside the maximal ideal of `S`
is a unit of `S`, and if it is fixed then so is its inverse. -/
theorem isLocalRing [IsLocalRing S] : IsLocalRing (_root_.FixedPoints.subring S G) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a : S) with h | h
  · exact Or.inl (isUnit_of_isUnit_val h)
  · exact Or.inr (isUnit_of_isUnit_val (by simpa using h))

/-- The maximal ideal of the fixed subring of a local ring is the contraction of `𝔪_S`. -/
theorem maximalIdeal_eq [IsLocalRing S]
    (h : IsLocalRing (_root_.FixedPoints.subring S G) := isLocalRing S G) :
    maximalIdeal (_root_.FixedPoints.subring S G)
      = (maximalIdeal S).comap (subtypeHom S G) := by
  ext a
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr isUnit_val_iff.symm

/-- The inclusion of the fixed subring of a local ring is a local ring map. -/
theorem isLocalHom_subtypeHom [IsLocalRing S]
    (_h : IsLocalRing (_root_.FixedPoints.subring S G) := isLocalRing S G) :
    IsLocalHom (subtypeHom S G) :=
  ⟨fun _ => isUnit_of_isUnit_val⟩

variable {S G}

variable (S G) in
/-- Evaluating the image in `S[X]` of a polynomial over the fixed subring at the image of a
point of the fixed subring. -/
theorem eval_map_subtypeHom (p : (_root_.FixedPoints.subring S G)[X])
    (x : _root_.FixedPoints.subring S G) :
    (p.map (subtypeHom S G)).eval (x : S)
      = ((p.eval x : _root_.FixedPoints.subring S G) : S) := by
  exact eval_map_apply (subtypeHom S G) x

/-- A polynomial with coefficients in the fixed subring is unchanged by the action of `G` on its
coefficients. -/
theorem map_toRingHom_map_subtypeHom (f : (_root_.FixedPoints.subring S G)[X]) (σ : G) :
    (f.map (subtypeHom S G)).map (MulSemiringAction.toRingHom G S σ)
      = f.map (subtypeHom S G) := by
  ext n
  simp only [coeff_map]
  exact (f.coeff n).2 σ

/-- The image under `σ` of a root of a polynomial with coefficients in the fixed subring is
again a root. -/
theorem isRoot_smul {f : (_root_.FixedPoints.subring S G)[X]} {a : S}
    (ha : (f.map (subtypeHom S G)).IsRoot a) (σ : G) :
    (f.map (subtypeHom S G)).IsRoot (σ • a) := by
  have h := congrArg (fun p : S[X] => p.eval (MulSemiringAction.toRingHom G S σ a))
    (map_toRingHom_map_subtypeHom f σ)
  simp only [eval_map, eval₂_at_apply] at h
  have ha' : eval₂ (subtypeHom S G) a f = 0 := by rwa [← eval_map]
  change eval (σ • a) (f.map (subtypeHom S G)) = 0
  rw [eval_map]
  change eval₂ (subtypeHom S G) (MulSemiringAction.toRingHom G S σ a) f = 0
  rw [← h, ha', map_zero]

variable (S G) in
/-- **A simple root of a monic polynomial over the fixed subring is fixed.** If `G` acts
trivially on the residue field of the local ring `S`, then a root `a` of `f.map (S ^ G → S)` at
which the derivative is a unit is fixed by `G`, because `σ a` is another root in the same
residue class and the henselian root is unique there. -/
theorem mem_fixedPoints_of_isRoot [IsLocalRing S]
    (hG : ∀ (σ : G) (x : S), σ • x - x ∈ maximalIdeal S)
    {f : (_root_.FixedPoints.subring S G)[X]} {a : S}
    (ha : (f.map (subtypeHom S G)).IsRoot a)
    (hd : (f.map (subtypeHom S G)).derivative.eval a ∉ maximalIdeal S) :
    a ∈ _root_.FixedPoints.subring S G := by
  intro σ
  refine (hensel_uniqueness (f.map (subtypeHom S G)) a (σ • a) ha (isRoot_smul ha σ) ?_ hd).symm
  simpa using (maximalIdeal S).neg_mem (hG σ a)

/-- **Henselian lifting inside the fixed subring.** Let `S` be henselian local and let `G` act
trivially on its residue field. A monic polynomial `f` over `S ^ G` with a simple root modulo
`𝔪_S` has a root in `S ^ G` in that residue class. -/
theorem exists_isRoot_of_isUnit_derivative [HenselianLocalRing S]
    (hG : ∀ (σ : G) (x : S), σ • x - x ∈ maximalIdeal S)
    {f : (_root_.FixedPoints.subring S G)[X]} (hf : f.Monic) (a₀ : S)
    (h0 : (f.map (subtypeHom S G)).eval a₀ ∈ maximalIdeal S)
    (hd : IsUnit ((f.map (subtypeHom S G)).derivative.eval a₀)) :
    ∃ a : _root_.FixedPoints.subring S G, f.IsRoot a ∧ (a : S) - a₀ ∈ maximalIdeal S := by
  obtain ⟨a, haroot, hacong⟩ :=
    HenselianLocalRing.is_henselian (f.map (subtypeHom S G)) (hf.map _) a₀ h0 hd
  have hunit : (f.map (subtypeHom S G)).derivative.eval a ∉ maximalIdeal S := by
    obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub a a₀ (f.map (subtypeHom S G)).derivative
    rw [← IsLocalRing.notMem_maximalIdeal] at hd
    intro hmem
    refine hd ?_
    have : (f.map (subtypeHom S G)).derivative.eval a₀
        = (f.map (subtypeHom S G)).derivative.eval a - (a - a₀) * c := by
      linear_combination -hc
    rw [this]
    exact (maximalIdeal S).sub_mem hmem ((maximalIdeal S).mul_mem_right c hacong)
  have ha := mem_fixedPoints_of_isRoot S G hG haroot hunit
  refine ⟨⟨a, ha⟩, Subtype.ext ?_, hacong⟩
  rw [← eval_map_subtypeHom S G f ⟨a, ha⟩]
  exact haroot

variable (S G)

/-- **The fixed subring of a henselian local ring is henselian**, provided `G` acts trivially on
the residue field. -/
theorem henselianLocalRing [HenselianLocalRing S]
    (hG : ∀ (σ : G) (x : S), σ • x - x ∈ maximalIdeal S) :
    HenselianLocalRing (_root_.FixedPoints.subring S G) := by
  have hloc := isLocalRing S G
  have hmax := maximalIdeal_eq S G hloc
  refine { __ := hloc, is_henselian := fun f hf a₀ h0 hd => ?_ }
  have h0' : (f.map (subtypeHom S G)).eval (a₀ : S) ∈ maximalIdeal S := by
    rw [eval_map_subtypeHom S G f a₀]
    rwa [hmax] at h0
  have hd' : IsUnit ((f.map (subtypeHom S G)).derivative.eval (a₀ : S)) := by
    rw [derivative_map, eval_map_subtypeHom S G f.derivative a₀]
    exact hd.map (subtypeHom S G)
  obtain ⟨a, haroot, hacong⟩ := exists_isRoot_of_isUnit_derivative hG hf (a₀ : S) h0' hd'
  exact ⟨a, haroot, by rwa [hmax]⟩

variable {S G}

variable (S G)

/-- **The residue field of the fixed subring is separably closed** when that of `S` is, provided
`S` is henselian local and `G` acts trivially on its residue field. A monic separable polynomial
over `κ(S ^ G)` has a simple root in `κ(S)`, which lifts by henselianness to a root in `S` of a
monic lift; that root is fixed by `G`, so its residue is a root in `κ(S ^ G)`. -/
theorem isSepClosed_residueField [HenselianLocalRing S] [IsSepClosed (ResidueField S)]
    (hG : ∀ (σ : G) (x : S), σ • x - x ∈ maximalIdeal S) :
    letI := isLocalRing S G
    IsSepClosed (ResidueField (_root_.FixedPoints.subring S G)) := by
  let := isLocalRing S G
  have : IsLocalHom (subtypeHom S G) := isLocalHom_subtypeHom S G
  set ι : ResidueField (_root_.FixedPoints.subring S G) →+* ResidueField S :=
    ResidueField.map (subtypeHom S G)
  have hcomp : (residue S).comp (subtypeHom S G)
      = ι.comp (residue (_root_.FixedPoints.subring S G)) := by
    ext x
    exact (ResidueField.map_residue (subtypeHom S G) x).symm
  refine IsSepClosed.of_exists_root _ fun g hgm hgi hgs => ?_
  -- Lift `g` to a monic polynomial `f` over the fixed subring.
  have hlift : g ∈ Polynomial.lifts (residue (_root_.FixedPoints.subring S G)) :=
    Polynomial.map_surjective _ (residue_surjective (R := _root_.FixedPoints.subring S G)) g
  obtain ⟨f, hfmap, -, hfm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hgm
  -- A simple root of `g` in the residue field of `S`.
  obtain ⟨α, hα⟩ : ∃ α, (g.map ι).IsRoot α := by
    refine IsSepClosed.exists_root _ ?_ (hgs.map (f := ι))
    rw [hgm.degree_map ι]
    exact (degree_pos_of_irreducible hgi).ne'
  have hα' : g.eval₂ ι α = 0 := by rwa [← eval_map]
  have hαd : (derivative g).eval₂ ι α ≠ 0 := hgs.eval₂_derivative_ne_zero ι hα'
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := S) α
  -- The reduction of the lift of `f` to `S[X]` is `g` pushed into `κ(S)`.
  have hmapP : (f.map (subtypeHom S G)).map (residue S) = g.map ι := by
    rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hfmap]
  have h0 : (f.map (subtypeHom S G)).eval a₀ ∈ maximalIdeal S := by
    rwa [← IsLocalRing.residue_eq_zero_iff, ← eval_map_apply, hmapP, ha₀]
  have hd : IsUnit ((f.map (subtypeHom S G)).derivative.eval a₀) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      ← eval_map_apply, ← derivative_map, hmapP, ha₀, derivative_map, eval_map]
    exact hαd
  obtain ⟨a, haroot, -⟩ := exists_isRoot_of_isUnit_derivative hG hfm a₀ h0 hd
  refine ⟨residue _ a, ?_⟩
  rw [← hfmap, eval_map_apply, haroot, map_zero]

section Stable

variable {M : Type*} [Monoid M] {T : Type*} [Ring T] [MulSemiringAction M T]

/-- A subring stable under a `MulSemiringAction` carries the restricted action. -/
@[instance_reducible, sga "3 IV 3.2.2" "special case"]
def _root_.Subring.mulSemiringActionOfStable (U : Subring T)
    (h : ∀ (σ : M) (x : T), x ∈ U → σ • x ∈ U) : MulSemiringAction M U where
  smul σ x := ⟨σ • (x : T), h σ x x.2⟩
  one_smul x := Subtype.ext (one_smul M (x : T))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : T))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ (x : T) (y : T))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : T) (y : T))

/-- The restricted action on a stable subring is the ambient one. -/
theorem coe_smul_of_stable (U : Subring T) (h : ∀ (σ : M) (x : T), x ∈ U → σ • x ∈ U)
    (σ : M) (x : U) :
    letI := U.mulSemiringActionOfStable h
    ((σ • x : U) : T) = σ • (x : T) := rfl

/-- The fixed points of the restricted action on a stable subring are the elements of the
subring fixed in the ambient ring. -/
theorem mem_fixedPoints_subring_of_stable (U : Subring T)
    (h : ∀ (σ : M) (x : T), x ∈ U → σ • x ∈ U) (x : U) :
    letI := U.mulSemiringActionOfStable h
    x ∈ _root_.FixedPoints.subring U M ↔ ∀ σ : M, σ • (x : T) = (x : T) :=
  ⟨fun hx σ => congrArg Subtype.val (hx σ), fun hx σ => Subtype.ext (hx σ)⟩

end Stable

end Stacks.FixedPoints
