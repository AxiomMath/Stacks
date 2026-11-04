module

public import StacksFrontier.Topology.Sheaves.Basis.ModuleFMap
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

/-!
# Supports of sections of a sheaf of modules

Let `X` be a ringed space and `F` a sheaf of `O_X`-modules. The support of a section `s : F(U)`
over an open `U` is the set of points `x ∈ U` at which the germ `s_x` is nonzero in the stalk
`F_x`, and the support of `F` is the set of points at which the stalk `F_x` is nonzero.

Stalks and germs of `F` are taken on its underlying `Ab`-valued presheaf `F.toPresheaf.presheaf`,
and those of `O_X` on the `RingCat`-valued presheaf `X.presheafRing`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection`: the support of a section of `F`.
* `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp`: the support of `F`.
* `AlgebraicGeometry.RingedSpace.suppRingSection`: the support of a section of `O_X`.

## Main results

* `AlgebraicGeometry.RingedSpace.ModuleSheaf.isClosed_suppSection`: the support of a section
  `s : F(U)` is closed in `U`.
* `AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection_smul_subset`:
  `Supp(f • s) ⊆ Supp(f) ∩ Supp(s)`.
* `AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection_add_subset`:
  `Supp(s + s') ⊆ Supp(s) ∪ Supp(s')`.
* `AlgebraicGeometry.RingedSpace.ModuleSheaf.mem_supp_iff`: `Supp(F)` is the union of the supports
  of all sections of `F`.
* `AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection_map_subset`: a morphism `φ : F ⟶ G`
  satisfies `Supp(φ(s)) ⊆ Supp(s)`.

## References

* [Stacks Project, Tag 01AT](https://stacks.math.columbia.edu/tag/01AT)
* [Stacks Project, Tag 01AU](https://stacks.math.columbia.edu/tag/01AU)
-/

open TopCat CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The underlying `Ab`-valued presheaf of a sheaf of `O_X`-modules. -/
noncomputable abbrev abPresheaf (F : ModuleSheaf X) : TopCat.Presheaf Ab X.carrier :=
  F.toPresheaf.presheaf

/-- The germ at `x ∈ U` of a section `s : F(U)`, as an element of the stalk `F_x`. -/
noncomputable def sectionGerm (F : ModuleSheaf X) (U : Opens X.carrier) (x : X.carrier)
    (hx : x ∈ U) (s : F.toPresheaf.obj (Opposite.op U)) : F.abPresheaf.stalk x :=
  (F.abPresheaf.germ U x hx) s

/-- The support of a section `s : F(U)`: the set of points `x ∈ U` at which the germ `s_x` is
nonzero in the stalk `F_x`. -/
noncomputable def suppSection (F : ModuleSheaf X) (U : Opens X.carrier)
    (s : F.toPresheaf.obj (Opposite.op U)) : Set X.carrier :=
  {x | ∃ hx : x ∈ U, F.sectionGerm U x hx s ≠ 0}

/-- The support of `F`: the set of points `x` at which the stalk `F_x` has a nonzero element. -/
@[ega "0 3.1.6" "Supp(F)"]
noncomputable def supp (F : ModuleSheaf X) : Set X.carrier :=
  {x | ∃ a : F.abPresheaf.stalk x, a ≠ 0}

end AlgebraicGeometry.RingedSpace.ModuleSheaf

namespace AlgebraicGeometry.RingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The germ at `x ∈ U` of a section `f : O_X(U)` of the sheaf of rings, as an element of
the ring stalk `O_{X,x}`. -/
noncomputable def ringSectionGerm (U : Opens X.carrier) (x : X.carrier) (hx : x ∈ U)
    (f : (X.presheafRing).obj (Opposite.op U)) : (X.presheafRing).stalk x :=
  ((X.presheafRing).germ U x hx) f

/-- The support of a section `f : O_X(U)` of the sheaf of rings, the set of points `x ∈ U`
at which the germ `f_x` is nonzero in `O_{X,x}`. -/
noncomputable def suppRingSection (U : Opens X.carrier)
    (f : (X.presheafRing).obj (Opposite.op U)) : Set X.carrier :=
  {x | ∃ hx : x ∈ U, X.ringSectionGerm U x hx f ≠ 0}

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The support of a section `s : F(U)` is closed in `U`, for the subspace topology on `U`. -/
@[stacks 01AU "(1)"]
theorem isClosed_suppSection (F : ModuleSheaf X) (U : Opens X.carrier)
    (s : F.toPresheaf.obj (Opposite.op U)) :
    IsClosed {x : U | (x : X.carrier) ∈ F.suppSection U s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨x, hxU⟩ hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, suppSection, sectionGerm, not_exists,
    not_not] at hx
  have h0 : (F.abPresheaf.germ U x hxU) s = 0 := hx hxU
  have hg : (F.abPresheaf.germ U x hxU) s = (F.abPresheaf.germ U x hxU) 0 := by rw [h0, map_zero]
  obtain ⟨W, hxW, iU, iV, hres⟩ := F.abPresheaf.germ_eq x hxU hxU s 0 hg
  refine ⟨Subtype.val ⁻¹' (W : Set X.carrier), ?_, ?_, ?_⟩
  · rintro ⟨y, hyU⟩ hyW
    simp only [Set.mem_preimage] at hyW
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, suppSection, sectionGerm, not_exists,
      not_not]
    intro hyU'
    have e1 : (F.abPresheaf.germ U y hyU') s
        = (F.abPresheaf.germ W y hyW) ((F.abPresheaf.map iU.op) s) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [e1, hres, TopCat.Presheaf.germ_res_apply, map_zero]
  · exact (W.isOpen).preimage continuous_subtype_val
  · exact hxW

/-- For `f : O_X(U)` and `s : F(U)`, `Supp(f • s) ⊆ Supp(f) ∩ Supp(s)`. -/
@[stacks 01AU "(2)"]
theorem suppSection_smul_subset (F : ModuleSheaf X) (U : Opens X.carrier)
    (f : (X.presheafRing).obj (Opposite.op U)) (s : F.toPresheaf.obj (Opposite.op U)) :
    F.suppSection U (f • s) ⊆ X.suppRingSection U f ∩ F.suppSection U s := by
  intro x ⟨hxU, hne⟩
  simp only [sectionGerm, PresheafOfModules.germ_ringCat_smul] at hne
  refine ⟨⟨hxU, ?_⟩, ⟨hxU, ?_⟩⟩
  · intro hf
    apply hne
    rw [AlgebraicGeometry.RingedSpace.ringSectionGerm] at hf
    rw [hf, zero_smul]
  · intro hs
    apply hne
    rw [sectionGerm] at hs
    rw [hs, smul_zero]

/-- For `s s' : F(U)`, `Supp(s + s') ⊆ Supp(s) ∪ Supp(s')`. -/
@[stacks 01AU "(3)"]
theorem suppSection_add_subset (F : ModuleSheaf X) (U : Opens X.carrier)
    (s s' : F.toPresheaf.obj (Opposite.op U)) :
    F.suppSection U (s + s') ⊆ F.suppSection U s ∪ F.suppSection U s' := by
  intro x ⟨hxU, hne⟩
  simp only [sectionGerm, map_add] at hne
  rw [Set.mem_union]
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.mp h
  simp only [suppSection, sectionGerm, Set.mem_ofPred_eq, not_exists, not_not] at h1 h2
  exact hne (by rw [h1 hxU, h2 hxU, add_zero])

/-- A point `x` lies in `Supp(F)` if and only if there exist an open set `U` with `x ∈ U` and a
section `s : F(U)` with `x ∈ Supp(s)`. Equivalently, `Supp(F)` is the union over all `(U, s)` of
`Supp(s)`. -/
@[stacks 01AU "(4)"]
theorem mem_supp_iff (F : ModuleSheaf X) (x : X.carrier) :
    x ∈ F.supp ↔ ∃ (U : Opens X.carrier) (s : F.toPresheaf.obj (Opposite.op U)),
      x ∈ F.suppSection U s := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨U, hx, s, hs⟩ := F.abPresheaf.exists_germ_eq a
    refine ⟨U, s, hx, ?_⟩
    rwa [sectionGerm, hs]
  · rintro ⟨U, s, hx, hne⟩
    exact ⟨F.sectionGerm U x hx s, hne⟩

/-- For a morphism `φ : F ⟶ G` of `O_X`-modules and `s : F(U)`, `Supp(φ(s)) ⊆ Supp(s)`. -/
@[stacks 01AU "(5)"]
theorem suppSection_map_subset (F G : ModuleSheaf X)
    (φ : PresheafOfModules.Hom F.toPresheaf G.toPresheaf) (U : Opens X.carrier)
    (s : F.toPresheaf.obj (Opposite.op U)) :
    G.suppSection U ((φ.app (Opposite.op U)) s) ⊆ F.suppSection U s := by
  intro x ⟨hxU, hne⟩
  refine ⟨hxU, ?_⟩
  intro hs
  apply hne
  rw [sectionGerm] at hs ⊢
  have key := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := Ab) U x hxU
    ((PresheafOfModules.toPresheaf X.presheafRing).map φ) s
  have hz : (TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf X.presheafRing).map φ)
        ((TopCat.Presheaf.germ ((PresheafOfModules.toPresheaf X.presheafRing).obj F.toPresheaf)
          U x hxU) s) = 0 := by
    rw [show (TopCat.Presheaf.germ ((PresheafOfModules.toPresheaf X.presheafRing).obj F.toPresheaf)
        U x hxU) s = (F.abPresheaf.germ U x hxU) s from rfl, hs, map_zero]
  exact key.symm.trans hz

end AlgebraicGeometry.RingedSpace.ModuleSheaf
