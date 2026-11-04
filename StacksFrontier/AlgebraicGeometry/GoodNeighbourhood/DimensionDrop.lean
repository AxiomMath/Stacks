module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.BertiniCut

/-!
# Cutting a closed set by a general section lowers its dimension

Let `X` be locally of finite type over a field `k`, with `δ` the dimension of the closure of a
point (`Stacks.Chow.fieldChowSituation`). If every point of a closed subscheme `T` has `δ ≤ e` and
a section `s` vanishes at no generic point of `T`, then every point of `T ∩ Z(s)` has
`δ ≤ e - 1`. For the linear system `V_n` of sections vanishing on `Z = V(I)` and `T` off `Z`, not
vanishing at the finitely many generic points is a general condition.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.relativeDimension_le_sub_one_of_mem_zeroScheme`: every
  point of `T` in a closed set avoiding the generic points of `T` has `δ ≤ e - 1`.
* `AlgebraicGeometry.GoodNeighbourhood.generalIn_notMem_support_genericPoints`: nonvanishing at
  the generic points of `T` off `Z` holds for a general member of `V_n`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.SectionsVanishingOnSubscheme Stacks.Chow

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- If every point of the closed subscheme `T` has `δ ≤ e` and the closed set `Z` contains no
generic point of `T`, then every point of `T ∩ Z` has `δ ≤ e - 1`. -/
theorem relativeDimension_le_sub_one_of_mem_zeroScheme [LocallyOfFiniteType p]
    (T : X.IdealSheafData) (e : ℤ)
    (hdim : ∀ y ∈ T.support, relativeDimension (fieldChowSituation k).dimensionFunction p y ≤ e)
    (Z : X.IdealSheafData) (hZ : ∀ η ∈ genericPoints T.subscheme, T.subschemeι η ∉ Z.support)
    (y : X) (hyT : y ∈ T.support) (hyZ : y ∈ Z.support) :
    relativeDimension (fieldChowSituation k).dimensionFunction p y ≤ e - 1 := by
  have : LocallyOfFiniteType (show X ⟶ (fieldChowSituation k).S from p) := ‹_›
  obtain ⟨w, rfl⟩ : y ∈ Set.range T.subschemeι := by rwa [Scheme.IdealSheafData.range_subschemeι]
  set η := (genericPoints.ofComponent ⟨irreducibleComponent w,
    irreducibleComponent_mem_irreducibleComponents w⟩).1
  have hηgen : η ∈ genericPoints T.subscheme := (genericPoints.ofComponent _).2
  have hsp : η ⤳ w := (genericPoints.isGenericPoint_ofComponent _).specializes
    mem_irreducibleComponent
  have hsp' : T.subschemeι η ⤳ T.subschemeι w := hsp.map T.subschemeι.continuous
  have hne : T.subschemeι w ≠ T.subschemeι η := fun he => hZ η hηgen (he ▸ hyZ)
  have hηT : T.subschemeι η ∈ T.support := by
    show T.subschemeι η ∈ (T.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨η, rfl⟩
  have h1 := hdim _ hηT
  have h2 : relativeDimension (fieldChowSituation k).dimensionFunction p (T.subschemeι w) <
      relativeDimension (fieldChowSituation k).dimensionFunction p (T.subschemeι η) :=
    relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) p
      (specializes_iff_mem_closure.1 hsp') hne
  omega

/-- A member of `V_n` not lying in the subspace of sections vanishing at `y` has `y` outside its
zero scheme. -/
theorem notMem_support_of_notMem_vanishingAtSubmodule {L : X.Modules} [IsInvertibleModule X L]
    (I : X.IdealSheafData) (n : ℤ) {y : X} {v : vanishingSections k p I L n}
    (hv : v ∉ Stacks.Chow.BertiniChain.vanishingAtSubmodule k p I L n y) :
    y ∉ (zeroScheme X (tensorPowModule X L n) (vsec p n v)).support := fun hy =>
  AlgebraicGeometry.notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen _ _
    (not_not.mp hv) (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hy)

/-- Finitely many general properties, indexed by a finite type, hold together. -/
theorem GeneralIn.forall_of_finite {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {ι : Type*} [Finite ι] {P : ι → V → Prop}
    (h : ∀ i, GeneralIn k V (P i)) : GeneralIn k V (fun v => ∀ i, P i v) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine (GeneralIn.forall_fin (P := fun j => P (e.symm j)) fun j => h _).mono fun v hv i => ?_
  simpa using hv (e i)

/-- A general member of `V_n` vanishes at no generic point of `T` off `Z`. -/
theorem generalIn_notMem_support_genericPoints [IsProper p] {L : X.Modules}
    [IsInvertibleModule X L] (I : X.IdealSheafData) (n : ℤ)
    (hgen : GeneratesOffSupport k p I L n) (T : X.IdealSheafData) :
    GeneralIn k (vanishingSections k p I L n) (fun v => ∀ η ∈ genericPoints T.subscheme,
      T.subschemeι η ∉ I.support →
        T.subschemeι η ∉ (zeroScheme X (tensorPowModule X L n) (vsec p n v)).support) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace T.subscheme := QuasiCompact.compactSpace_of_compactSpace T.subschemeι
  have : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.subschemeι ≫ p)
  have : IsNoetherian T.subscheme := {}
  let E : Set T.subscheme := {η | η ∈ genericPoints T.subscheme ∧ T.subschemeι η ∉ I.support}
  have : Finite E := ((genericPoints.finite
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset
      fun η hη => hη.1).to_subtype
  refine (GeneralIn.forall_of_finite (ι := E) (P := fun η v =>
      T.subschemeι η.1 ∉ (zeroScheme X (tensorPowModule X L n) (vsec p n v)).support)
    fun η => (GeneralIn.of_notMem _ (Stacks.Chow.BertiniChain.vanishingAtSubmodule_ne_top k p I L
      n hgen η.2.2)).mono fun v hv => notMem_support_of_notMem_vanishingAtSubmodule p I n hv).mono
    fun v hv η hη hηI => hv ⟨η, hη, hηI⟩

end AlgebraicGeometry.GoodNeighbourhood

end
