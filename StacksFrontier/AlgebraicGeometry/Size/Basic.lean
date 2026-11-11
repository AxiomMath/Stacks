module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# The size of a scheme (Stacks Section 000H)

The *size* of a scheme `S` is the cardinal
`max ℵ₀ (max #S.affineOpens (⨆ U : S.affineOpens, #Γ(S, U)))`, together with the three
inequalities `ℵ₀ ≤ size S`, `#S.affineOpens ≤ size S` and `#Γ(S, U) ≤ size S` that it
satisfies by construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry

/-- **The size of a scheme**, as defined in the opening text of Stacks Section 000H
(Section 3.9, before Lemma 3.9.1, Tag 000I).

The *size* of a scheme `S` is the maximum of `ℵ₀`, the cardinality of the set of
affine opens of `S`, and the supremum over affine opens `U ⊆ S` of the
cardinality of the ring of sections `Γ(S, U)`.

Every Section 3.9 size bound is stated in terms of this one cardinal, so the bounds
compose. -/
noncomputable def Scheme.size (S : Scheme.{u}) : Cardinal.{u} :=
  max Cardinal.aleph0
    (max (Cardinal.mk S.affineOpens)
      (⨆ U : S.affineOpens, Cardinal.mk Γ(S, U.1)))

/-- `ℵ₀ ≤ size S`. -/
theorem Scheme.aleph0_le_size (S : Scheme.{u}) : ℵ₀ ≤ S.size :=
  le_max_left _ _

/-- The number of affine opens of `S` is bounded by `size S`. -/
theorem Scheme.mk_affineOpens_le_size (S : Scheme.{u}) : #S.affineOpens ≤ S.size :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- The cardinality of the sections over any affine open is bounded by `size S`. -/
theorem Scheme.mk_sections_le_size (S : Scheme.{u}) (U : S.affineOpens) :
    #Γ(S, U.1) ≤ S.size :=
  (le_ciSup bddAbove_of_small U).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The cardinality of a stalk of `S` is bounded by `size S`: the stalk is covered by the
sections over the affine opens through the point, and both the affine opens and their sections
are bounded by the size. -/
theorem Scheme.mk_stalk_le_size (S : Scheme.{u}) (x : S) :
    Cardinal.mk (S.presheaf.stalk x) ≤ S.size := by
  let I : Type u := {V : S.affineOpens // x ∈ V.1}
  let g : (i : I) × S.presheaf.obj (Opposite.op i.1.1) → S.presheaf.stalk x :=
    fun i => (ConcreteCategory.hom (S.presheaf.germ i.1.1 x i.1.2)) i.2
  have hg : Function.Surjective g := by
    intro r
    obtain ⟨V, hxV, hV, s, hs⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis S.isBasis_affineOpens S.presheaf x r
    exact ⟨⟨⟨⟨V, hV⟩, hxV⟩, s⟩, hs⟩
  calc
    Cardinal.mk (S.presheaf.stalk x) ≤
        Cardinal.mk ((i : I) × S.presheaf.obj (Opposite.op i.1.1)) :=
      Cardinal.mk_le_of_surjective hg
    _ = Cardinal.sum (fun i : I => Cardinal.mk (S.presheaf.obj (Opposite.op i.1.1))) :=
      Cardinal.mk_sigma _
    _ ≤ Cardinal.mk I * ⨆ i : I, Cardinal.mk (S.presheaf.obj (Opposite.op i.1.1)) :=
      Cardinal.sum_le_mk_mul_iSup _
    _ ≤ S.size * S.size :=
      mul_le_mul' ((Cardinal.mk_subtype_le _).trans S.mk_affineOpens_le_size)
        (ciSup_le' fun i => S.mk_sections_le_size i.1)
    _ = S.size := Cardinal.mul_eq_self S.aleph0_le_size

/-- The cardinality of a residue field of `S` is bounded by `size S`: the residue field is a
quotient of the stalk at that point, whose cardinality is bounded by the size. -/
theorem Scheme.residueField_size_le (S : Scheme.{u}) (x : S) :
    Cardinal.mk (S.residueField x) ≤ S.size :=
  (Cardinal.mk_le_of_surjective (S.residue_surjective x)).trans (S.mk_stalk_le_size x)

end AlgebraicGeometry
