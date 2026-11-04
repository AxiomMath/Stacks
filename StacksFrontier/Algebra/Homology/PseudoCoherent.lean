module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# `m`-pseudo-coherence in the derived category of a ring

Let `R` be a ring and let `D(R)` be the derived category of the category of
`R`-modules. For `m : ℤ`, an object `K` of `D(R)` is `m`-pseudo-coherent when it can be
approximated in degrees `≥ m` by a bounded complex of finite free `R`-modules: there is such
a complex `E` and a morphism `α : Q(E) ⟶ K` in `D(R)` with `Hⁱ(α)` an isomorphism for `i > m`
and `Hᵐ(α)` surjective.

## Main definitions

* `StacksDraft.PseudoCoherence.IsFiniteFree`: an `R`-module object is finite and free.
* `StacksDraft.PseudoCoherence.IsBoundedFiniteFree`: a cochain complex of `R`-modules is
  bounded with finite free terms.
* `StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree`: a cochain complex of `R`-modules is
  bounded above with finite free terms.
* `StacksDraft.PseudoCoherence.IsPseudoCoherentFrom`: `m`-pseudo-coherence of an object of
  `D(R)`, Stacks 064Q (1).
* `StacksDraft.PseudoCoherence.IsPseudoCoherent`: pseudo-coherence of an object of `D(R)`,
  Stacks 064Q (2).
* `StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom`: `m`-pseudo-coherence of a module,
  Stacks 064Q (3).
* `StacksDraft.PseudoCoherence.IsModulePseudoCoherent`: pseudo-coherence of a module,
  Stacks 064Q (4).

## Main results

* `StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.shift`: `m`-pseudo-coherence of `K`
  gives `(m - n)`-pseudo-coherence of `K⟦n⟧`.
* `StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso`: `m`-pseudo-coherence only
  depends on the isomorphism class of `K` in `D(R)`.
* `StacksDraft.PseudoCoherence.bridgeIso`: the homology of `Q(E)` computed in `D(R)` agrees
  with the homology of the cochain complex `E`.
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.PseudoCoherence

universe v u

variable {R : Type u} [Ring R]

/-- An object of `ModuleCat R` is *finite free* when it is finite and free as an
`R`-module. -/
def IsFiniteFree (M : ModuleCat.{v} R) : Prop :=
  Module.Finite R M ∧ Module.Free R M

/-- A cochain complex of `R`-modules is a *bounded complex of finite free `R`-modules* when it
vanishes outside a finite range of degrees and each of its terms is finite free. Boundedness is
recorded through the strict bounds `IsStrictlyGE`/`IsStrictlyLE`. -/
structure IsBoundedFiniteFree (E : CochainComplex (ModuleCat.{v} R) ℤ) : Prop where
  /-- Some degree below which `E` vanishes. -/
  lowerBound : ∃ a : ℤ, E.IsStrictlyGE a
  /-- Some degree above which `E` vanishes. -/
  upperBound : ∃ b : ℤ, E.IsStrictlyLE b
  /-- Every term of `E` is a finite free `R`-module. -/
  finiteFree : ∀ i : ℤ, IsFiniteFree (E.X i)

/-- Shifting reindexes the terms of a complex and translates its bounds, so a bounded complex of
finite free modules stays one. -/
theorem IsBoundedFiniteFree.shift {E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hE : IsBoundedFiniteFree E) (n : ℤ) :
    IsBoundedFiniteFree (E⟦n⟧) := by
  obtain ⟨a, ha⟩ := hE.lowerBound
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨⟨a - n, ?_⟩, ⟨b - n, ?_⟩, ?_⟩
  · exact CochainComplex.isStrictlyGE_shift E a n (a - n) (by ring)
  · exact CochainComplex.isStrictlyLE_shift E b n (b - n) (by ring)
  · intro i
    -- `(E⟦n⟧).X i` is `E.X (i + n)` by definition.
    rw [show ((shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n).obj E).X i
        = E.X (i + n) from rfl]
    exact hE.finiteFree (i + n)

/-- Boundedness and finite freeness of `E` can equivalently be phrased by exhibiting a window
`[a, b]` outside of which `E` vanishes. -/
theorem isBoundedFiniteFree_iff_exists_window (E : CochainComplex (ModuleCat.{v} R) ℤ) :
    IsBoundedFiniteFree E ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) → IsZero (E.X i)) ∧
        (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) := by
  refine ⟨?_, fun ⟨⟨a, b, hw⟩, hff⟩ =>
    ⟨⟨a, (CochainComplex.isStrictlyGE_iff E a).2 fun i hi => hw i (Or.inl hi)⟩,
      ⟨b, (CochainComplex.isStrictlyLE_iff E b).2 fun i hi => hw i (Or.inr hi)⟩,
      fun i => (hff i).symm⟩⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hff⟩
  exact ⟨⟨a, b, fun i hi => hi.elim (fun h => E.isZero_of_isStrictlyGE a i h)
    fun h => E.isZero_of_isStrictlyLE b i h⟩, fun i => (hff i).symm⟩

/-- A cochain complex of `R`-modules is a *bounded-above complex of finite free `R`-modules*
when it vanishes in all sufficiently large degrees and each of its terms is finite free. Only
the upper bound is imposed, so such a complex may be unbounded below. -/
structure IsBoundedAboveFiniteFree (E : CochainComplex (ModuleCat.{v} R) ℤ) : Prop where
  /-- Some degree above which `E` vanishes. -/
  upperBound : ∃ b : ℤ, E.IsStrictlyLE b
  /-- Every term of `E` is a finite free `R`-module. -/
  finiteFree : ∀ i : ℤ, IsFiniteFree (E.X i)

/-- A bounded complex of finite free modules is in particular bounded above. -/
theorem IsBoundedFiniteFree.isBoundedAboveFiniteFree
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hE : IsBoundedFiniteFree E) :
    IsBoundedAboveFiniteFree E :=
  ⟨hE.upperBound, hE.finiteFree⟩

variable [HasDerivedCategory (ModuleCat.{v} R)]

/-- An object `K` of `D(R)` is *`m`-pseudo-coherent* when there is a bounded complex `E` of
finite free `R`-modules and a morphism `α : Q(E) ⟶ K` in `D(R)`, where `Q` sends a complex to its
image in the derived category, such that `Hⁱ(α)` is an isomorphism for every `i > m` and `Hᵐ(α)`
is surjective. -/
@[stacks 064Q "(1)", sga "6 II 2.3.2"]
def IsPseudoCoherentFrom (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{v} R) ℤ,
    IsBoundedFiniteFree E ∧ ∃ α : (DerivedCategory.Q).obj E ⟶ K,
      (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map α)

/-- An object `K` of `D(R)` is *pseudo-coherent* when it is represented by a bounded-above
complex of finite free `R`-modules. -/
@[stacks 064Q "(2)"]
def IsPseudoCoherent (K : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{v} R) ℤ,
    IsBoundedAboveFiniteFree E ∧ Nonempty ((DerivedCategory.Q).obj E ≅ K)

/-- An `R`-module `M` is *`m`-pseudo-coherent* when the object of `D(R)` concentrated in
degree `0` with value `M` is `m`-pseudo-coherent. -/
@[stacks 064Q "(3)"]
def IsModulePseudoCoherentFrom (M : Type v) [AddCommGroup M] [Module R M] (m : ℤ) : Prop :=
  IsPseudoCoherentFrom
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R M)) m

/-- An `R`-module `M` is *pseudo-coherent* when the object of `D(R)` concentrated in degree `0`
with value `M` is pseudo-coherent. -/
@[stacks 064Q "(4)"]
def IsModulePseudoCoherent (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  IsPseudoCoherent
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R M))

/-- The comparison `Hⁱ(Q(E)) ≅ Hⁱ(E)` between the homology of `E` computed in `D(R)` and the
homology of the cochain complex `E`. -/
noncomputable def bridgeIso (E : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj ((DerivedCategory.Q).obj E) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).obj E :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app E

/-- Precomposing an epimorphism with an isomorphism gives an epimorphism. The isomorphism factor
is handled by `IsIso.epi_of_iso` rather than by instance search, which in this environment can
reach `Epi` through a chain that depends on an unproved result. -/
private theorem epi_comp_of_isIso_left {C : Type*} [Category C] {X Y Z : C} (e : X ⟶ Y)
    [IsIso e] (f : Y ⟶ Z) [Epi f] : Epi (e ≫ f) := by
  have : Epi e := IsIso.epi_of_iso _
  exact epi_comp _ _

/-- Postcomposing an epimorphism with an isomorphism gives an epimorphism. -/
private theorem epi_comp_of_isIso_right {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    [Epi f] (e : Y ⟶ Z) [IsIso e] : Epi (f ≫ e) := by
  have : Epi e := IsIso.epi_of_iso _
  exact epi_comp _ _

/-- Naturally isomorphic functors detect the same epimorphisms. -/
theorem epi_map_iff_of_natIso {C : Type*} [Category C] {D : Type*} [Category D]
    {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
    Epi (F₁.map f) ↔ Epi (F₂.map f) := by
  have key : ∀ {G₁ G₂ : C ⥤ D} (_ : G₁ ≅ G₂), Epi (G₁.map f) → Epi (G₂.map f) :=
    fun {G₁ G₂} e h => by
    rw [show G₂.map f = e.inv.app X ≫ G₁.map f ≫ e.hom.app Y by simp]
    have := epi_comp_of_isIso_right (G₁.map f) (e.hom.app Y)
    exact epi_comp_of_isIso_left _ _
  exact ⟨key e, key e.symm⟩

/-- The natural isomorphism `Hⁱ(-⟦n⟧) ≅ Hⁿ⁺ⁱ(-)` on `D(R)`, coming from the shift sequence on the
homology functors. -/
noncomputable def homologyFunctorShiftIso (n i : ℤ) :
    shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} R) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{v} R) (n + i) :=
  Functor.ShiftSequence.shiftIso
    (F := DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0) n i (n + i) rfl

/-- `Hⁱ` of a shifted morphism is an isomorphism exactly when `Hⁿ⁺ⁱ` of the morphism is. -/
theorem isIso_homologyFunctor_map_shift_iff
    {X Y : DerivedCategory (ModuleCat.{v} R)} (φ : X ⟶ Y) (n i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (φ⟦n⟧')) ↔
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (n + i)).map φ) := by
  exact NatIso.isIso_map_iff (homologyFunctorShiftIso n i) φ

/-- `Hⁱ` of a shifted morphism is an epimorphism exactly when `Hⁿ⁺ⁱ` of the morphism is. -/
theorem epi_homologyFunctor_map_shift_iff
    {X Y : DerivedCategory (ModuleCat.{v} R)} (φ : X ⟶ Y) (n i : ℤ) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (φ⟦n⟧')) ↔
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (n + i)).map φ) := by
  exact epi_map_iff_of_natIso (homologyFunctorShiftIso n i) φ

/-- If `K` is `m`-pseudo-coherent then `K⟦n⟧` is `(m - n)`-pseudo-coherent: shift the
approximating complex along `Q`'s shift compatibility. -/
@[sga "6 I 2.5" "a), bounded clause"]
theorem IsPseudoCoherentFrom.shift {K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) (n : ℤ) :
    IsPseudoCoherentFrom (K⟦n⟧) (m - n) := by
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  refine ⟨E⟦n⟧, hE.shift n, ((DerivedCategory.Q).commShiftIso n).hom.app E ≫ (α⟦n⟧'), ?_, ?_⟩
  · intro i hi
    have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (α⟦n⟧')) := by
      rw [isIso_homologyFunctor_map_shift_iff]
      exact hiso (n + i) (by omega)
    rw [Functor.map_comp]
    exact IsIso.comp_isIso
  · have hsub : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m - n)).map (α⟦n⟧')) := by
      rw [epi_homologyFunctor_map_shift_iff, show n + (m - n) = m from by ring]
      exact hepi
    rw [Functor.map_comp]
    exact epi_comp_of_isIso_left _ _

/-- `m`-pseudo-coherence depends only on the isomorphism class of the object in `D(R)`. -/
theorem IsPseudoCoherentFrom.ofIso {K K' : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) (e : K ≅ K') :
    IsPseudoCoherentFrom K' m := by
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  refine ⟨E, hE, α ≫ e.hom, ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp]
    have := hiso i hi
    exact IsIso.comp_isIso
  · rw [Functor.map_comp]
    have := hepi
    exact epi_comp_of_isIso_right _ _

end StacksDraft.PseudoCoherence
