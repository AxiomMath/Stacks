module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.SupportChange

/-!
# The extended alternating Čech complex of equations on an open, read on the ambient scheme

Let `X` be a scheme, `W ⊆ X` an open subscheme and `f₁, …, f_c ∈ Γ(W, 𝒪_W)`.  The extended
alternating Čech complex of Stacks 0G7I of `ℱ|_W` and `f₁, …, f_c` is a complex on `W`; its
splice is the complex of `𝒪_X`-modules

`ℱ ⟶ ι_* ⨁ (ℱ|_W)_{i₀} ⟶ ⋯`

whose cohomology sheaves are supported on the complement of the union of the principal opens of
the `fᵢ` in `W`.  This file builds that complex, its support, and the fraction cocycle
`s ↦ s / (f₁ ⋯ f_c)` in its top degree.

## Main definitions

* `Stacks.Perfect.ConormalClass.chartSplice`: the splice of the extended alternating Čech complex
  of equations on an open.
* `Stacks.Perfect.ConormalClass.chartSupport`: the closed subset of `X` outside of which the
  splice is acyclic.
* `Stacks.Perfect.ConormalClass.chartFraction`: the fraction cocycle.

## Main results

* `Stacks.Perfect.ConormalClass.cohomologySupportedOn_chartSplice`: the cohomology sheaves of the
  splice are supported on `chartSupport`.
* `Stacks.Perfect.ConormalClass.chartFraction_comp_d`: the fraction cocycle is a cocycle.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction (fractionHom fractionHom_secIso fractionCochain_apply
  secIso_smul secIso_restrict)
open Stacks.AlgebraicGeometry.ModuleLimits (homOfSections homOfSections_app)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The splice of the Čech complex of equations on an open -/

section Chart

variable (W : X.Opens) {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) (F : X.Modules)

/-- **The extended alternating Čech complex of equations on an open, read on `X`.** -/
def chartSplice : CochainComplex X.Modules ℕ :=
  splice W F (cplx f ((res W).obj F)) (Iso.refl _)

/-- In degrees `n + 1 → n + 2` the differential of `chartSplice` is the pushforward of the
differential of the Čech complex on `W`. -/
theorem chartSplice_d_succ (n : ℕ) :
    (chartSplice W f F).d (n + 1) (n + 1 + 1) =
      (push W).map ((cplx f ((res W).obj F)).d (n + 1) (n + 1 + 1)) :=
  splice_d_succ W F (cplx f ((res W).obj F)) (Iso.refl _) n

/-- The differential of `chartSplice` in degrees `0 → 1` is the unit `ℱ ⟶ ι_* (ℱ|_W)` followed
by the pushforward of the degree-`0` differential of the Čech complex on `W`. -/
theorem chartSplice_d_zero :
    (chartSplice W f F).d 0 1 = unitW W F ≫ (push W).map ((cplx f ((res W).obj F)).d 0 1) := by
  refine (splice_d_zero W F (cplx f ((res W).obj F)) (Iso.refl _)).trans ?_
  exact congrArg (fun g => unitW W F ≫ (push W).map g) (Category.id_comp _)

/-- The closed subset of `X` outside of which the splice is acyclic: the complement of the
image of the union of the principal opens of the equations. -/
def chartSupport : Set X := ((W.ι ''ᵁ ⨆ i, W.toScheme.basicOpen (f i) : X.Opens) : Set X)ᶜ

/-- The subset `chartSupport W f` of `X` is closed. -/
theorem isClosed_chartSupport : IsClosed (chartSupport W f) :=
  (W.ι ''ᵁ ⨆ i, W.toScheme.basicOpen (f i)).isOpen.isClosed_compl

/-- **The splice is supported on `chartSupport`**, the Čech complex being supported on the zero
locus of the equations (Stacks 0G7K). -/
theorem cohomologySupportedOn_chartSplice :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace)
      (chartSupport W f)
      (DerivedCategory.Q.obj ((chartSplice W f F).extend ComplexShape.embeddingUpNat)) := by
  have hK := Stacks.Perfect.SupportedFraction.cohomologySupportedOn_cech f ((res W).obj F)
  refine cohomologySupportedOn_splice (W := W) F (cplx f ((res W).obj F)) (Iso.refl _)
    (T' := Stacks.Perfect.CechDerivedSupport.equationsClosedSet f) hK ?_
  intro x hx
  rw [chartSupport, Set.mem_compl_iff, not_not] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, rfl, fun h => h hy⟩

end Chart

/-! ### The fraction cocycle -/

section Fraction

variable (W : X.Opens) {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤)) (F : X.Modules)

/-- **The fraction cocycle** `s ↦ s / (f₁ ⋯ f_c)` in the top degree of the splice. -/
def chartFraction : F ⟶ (chartSplice W f F).X (d + 1) :=
  unitW W F ≫ (push W).map (fractionHom f ((res W).obj F) d)

/-- The fraction cocycle is a cocycle: the splice vanishes above its top degree. -/
theorem chartFraction_comp_d :
    chartFraction W f F ≫ (chartSplice W f F).d (d + 1) (d + 1 + 1) = 0 := by
  rw [chartSplice_d_succ, chartFraction]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun g => unitW W F ≫ g) ((push W).map_comp _ _).symm).trans ?_
  refine (congrArg (fun g => unitW W F ≫ (push W).map (fractionHom f ((res W).obj F) d ≫ g))
    (Stacks.Perfect.SupportedFraction.cplx_d_top_eq_zero f ((res W).obj F))).trans ?_
  exact (congrArg (fun g => unitW W F ≫ (push W).map g) comp_zero).trans
    ((congrArg (fun g => unitW W F ≫ g) ((push W).map_zero _ _)).trans comp_zero)

end Fraction

end Stacks.Perfect.ConormalClass
