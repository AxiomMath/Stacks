module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMapQuasiIso
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Homology.CyclesShortComplex
public import StacksFrontier.Homology.KFlat.Bifunctor

/-!
# Left exact functors and quasi-isomorphisms of complexes of acyclic objects

Let `T : D ⥤ E` be an additive, left exact functor between abelian categories, `D` having enough
injectives, and call an object `X` of `D` `T`-acyclic when `RⁿT(X) = 0` for every `n > 0`
(`Stacks.RightDerivedComp.acyclic`).  This file proves the classical facts:

* an acyclic cochain complex `L` indexed by `ℤ`, bounded below and with `T`-acyclic terms, is
  carried by `T` to an acyclic complex;
* consequently a quasi-isomorphism `φ : K ⟶ J` of `ℕ`-indexed cochain complexes with `T`-acyclic
  terms is carried by `T` to a quasi-isomorphism.

The first is dimension shifting along the short exact sequences `0 → Zʲ → Lʲ → Zʲ⁺¹ → 0` of the
cycles: starting below the bound, where the cycles vanish, the two-out-of-three property
`Stacks.RightDerivedComp.acyclic_shortExact` makes every `Zʲ` acyclic and keeps every one of these
sequences short exact after applying `T`, and
`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact` splices them.  The second
applies the first to the mapping cone of `φ`, extended by zero to `ℤ`; its terms
`K^{n+1} ⊕ J^n` are `T`-acyclic.

Both statements are proved; nothing is assumed.  The criterion
`quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone` is stated for an arbitrary additive
functor, so that it also serves functors (such as a limit of sections along a tower) whose
acyclicity on the cone is obtained by other means.

## Main results

* `Stacks.RightDerivedComp.acyclic_cycles_of_acyclic`: the cycles of a bounded below acyclic
  complex with `T`-acyclic terms are `T`-acyclic.
* `Stacks.RightDerivedComp.acyclic_mapHomologicalComplex_of_acyclic`: such a complex is carried
  by `T` to an acyclic complex.
* `HomologicalComplex.quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone`: an additive
  functor `F` carries `φ` to a quasi-isomorphism as soon as it carries the mapping cone of the
  extension of `φ` to an acyclic complex.
* `Stacks.RightDerivedComp.acyclic_map_mappingCone_extendMap`: for a quasi-isomorphism `φ`
  between `ℕ`-indexed complexes with `T`-acyclic terms, `T` carries the mapping cone of the
  extension of `φ` to an acyclic complex.
* `Stacks.RightDerivedComp.quasiIso_mapHomologicalComplex_map_of_acyclic`: `T` carries `φ` to a
  quasi-isomorphism.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C]

/-- **A property of objects holding on the terms of a complex and on zero objects holds on the
terms of its extension** along an embedding of complex shapes, provided it is invariant under
isomorphism: those terms are the terms of the complex and zero objects. -/
theorem prop_extend_X (P : C → Prop) (hiso : ∀ {X Y : C}, (X ≅ Y) → P X → P Y)
    (hzero : ∀ X : C, IsZero X → P X) (K : HomologicalComplex C c) (hK : ∀ i, P (K.X i))
    (e : c.Embedding c') (i' : ι') : P ((K.extend e).X i') := by
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    exact hiso (K.extendXIso e hi).symm (hK i)
  · exact hzero _ (K.isZero_extend_X e i' fun i hi => h ⟨i, hi⟩)

end HomologicalComplex

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- **A property of objects holding on the terms of two complexes, invariant under isomorphism
and stable under binary biproducts, holds on the terms of the mapping cone** of a morphism
between them, the term in degree `n` being `K^{n+1} ⊞ J^n`. -/
theorem prop_X (P : C → Prop) (hiso : ∀ {X Y : C}, (X ≅ Y) → P X → P Y)
    (hbiprod : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) {K J : CochainComplex C ℤ} (φ : K ⟶ J)
    (hK : ∀ n, P (K.X n)) (hJ : ∀ n, P (J.X n)) (n : ℤ) : P ((mappingCone φ).X n) :=
  hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
    (hbiprod _ _ (hK (n + 1)) (hJ n))

end CochainComplex.mappingCone

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- **An additive functor carries a morphism `φ` of `ℕ`-indexed cochain complexes to a
quasi-isomorphism as soon as it carries the mapping cone of the extension of `φ` by zero to `ℤ`
to an acyclic complex.**  The functor commutes with mapping cones
(`CochainComplex.mappingCone.mapHomologicalComplexIso`), a morphism is a quasi-isomorphism exactly
when its mapping cone is acyclic, and extension by zero neither creates nor destroys
quasi-isomorphisms (`quasiIso_mapHomologicalComplex_map_extendMap_iff`). -/
theorem quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone
    {K J : CochainComplex C ℕ} (φ : K ⟶ J)
    (h : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone (extendMap φ ComplexShape.embeddingUpNat))).Acyclic) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) := by
  rw [← quasiIso_mapHomologicalComplex_map_extendMap_iff F ComplexShape.embeddingUpNat,
    CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  exact fun n => (h n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso _ F)

end HomologicalComplex

namespace Stacks.RightDerivedComp

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
  [EnoughInjectives D] (T : D ⥤ E) [T.Additive]

/-- A zero object is `T`-acyclic, being injective. -/
theorem acyclic_of_isZero {X : D} (h : IsZero X) : acyclic T X :=
  fun n hn => ((acyclic_of_injective T 0) n hn).of_iso ((T.rightDerived n).mapIso h.isoZero)

/-- **A binary biproduct of `T`-acyclic objects is `T`-acyclic**, by the long exact sequence of
the split short exact sequence `0 → X → X ⊞ Y → Y → 0`. -/
theorem acyclic_biprod (X Y : D) (hX : acyclic T X) (hY : acyclic T Y) :
    acyclic T (X ⊞ Y) := fun n hn =>
  Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
    (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact T n (hX n hn) (hY n hn)

variable [PreservesFiniteLimits T]

/-- **The cycles of a bounded below acyclic complex with `T`-acyclic terms are `T`-acyclic.**
Below the bound the cycles vanish; above it, `0 → Zʲ → Lʲ → Zʲ⁺¹ → 0` is short exact and the
two-out-of-three property of `T`-acyclic objects passes acyclicity from `Zʲ` to `Zʲ⁺¹`. -/
theorem acyclic_cycles_of_acyclic {L : CochainComplex D ℤ} (hL : L.Acyclic) (m : ℤ)
    (hm : ∀ j, j < m → IsZero (L.X j)) (hX : ∀ j, acyclic T (L.X j)) (j : ℤ) :
    acyclic T (L.cycles j) := by
  have hbase : ∀ i, i < m → acyclic T (L.cycles i) := fun i hi =>
    acyclic_of_isZero T (IsZero.of_mono (L.iCycles i) (hm i hi))
  have key : ∀ k : ℕ, acyclic T (L.cycles (m - 1 + k)) := by
    intro k
    induction k with
    | zero => exact hbase _ (by omega)
    | succ k ih =>
      have h := (acyclic_shortExact T _
        (L.cyclesShortComplex_shortExact (i := m - 1 + k) (j := m - 1 + k + 1) rfl
          (hL _)) ih (hX _)).1
      have hk : m - 1 + ((k + 1 : ℕ) : ℤ) = m - 1 + k + 1 := by push_cast; ring
      rw [hk]
      exact h
  by_cases hj : j < m
  · exact hbase j hj
  · have hk : m - 1 + (((j - (m - 1)).toNat : ℕ) : ℤ) = j := by omega
    rw [← hk]
    exact key _

/-- **A left exact functor carries a bounded below acyclic complex with `T`-acyclic terms to an
acyclic complex**: the cycles are `T`-acyclic (`acyclic_cycles_of_acyclic`), so `T` keeps each
of the sequences `0 → Zʲ → Lʲ → Zʲ⁺¹ → 0` short exact, and these splice to the image complex. -/
theorem acyclic_mapHomologicalComplex_of_acyclic {L : CochainComplex D ℤ} (hL : L.Acyclic)
    (m : ℤ) (hm : ∀ j, j < m → IsZero (L.X j)) (hX : ∀ j, acyclic T (L.X j)) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact T L fun i j hij =>
    (acyclic_shortExact T _ (L.cyclesShortComplex_shortExact hij (hL j))
      (acyclic_cycles_of_acyclic T hL m hm hX i) (hX i)).2

/-- **For a quasi-isomorphism `φ` of `ℕ`-indexed cochain complexes with `T`-acyclic terms, `T`
carries the mapping cone of the extension of `φ` by zero to `ℤ` to an acyclic complex.**  The
cone is acyclic because the extension of `φ` is a quasi-isomorphism, it vanishes below degree
`-1`, and its terms `K^{n+1} ⊞ J^n` are `T`-acyclic. -/
theorem acyclic_map_mappingCone_extendMap {K J : CochainComplex D ℕ} (φ : K ⟶ J) [QuasiIso φ]
    (hK : ∀ a, acyclic T (K.X a)) (hJ : ∀ a, acyclic T (J.X a)) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))).Acyclic := by
  refine acyclic_mapHomologicalComplex_of_acyclic T
    ((CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).1 inferInstance) (-1)
    (fun j hj => ?_) (CochainComplex.mappingCone.prop_X (acyclic T)
      (fun e h n hn => (h n hn).of_iso ((T.rightDerived n).mapIso e.symm)) (acyclic_biprod T) _
      (HomologicalComplex.prop_extend_X (acyclic T)
        (fun e h n hn => (h n hn).of_iso ((T.rightDerived n).mapIso e.symm))
        (fun _ h => acyclic_of_isZero T h) K hK _)
      (HomologicalComplex.prop_extend_X (acyclic T)
        (fun e h n hn => (h n hn).of_iso ((T.rightDerived n).mapIso e.symm))
        (fun _ h => acyclic_of_isZero T h) J hJ _))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact K.isZero_extend_X _ _ fun a ha => by
      rw [ComplexShape.embeddingUpNat_f] at ha
      omega
  · exact J.isZero_extend_X _ _ fun a ha => by
      rw [ComplexShape.embeddingUpNat_f] at ha
      omega

/-- **A left exact functor carries a quasi-isomorphism of `ℕ`-indexed cochain complexes with
`T`-acyclic terms to a quasi-isomorphism.**  This is
`acyclic_map_mappingCone_extendMap` read through
`HomologicalComplex.quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone`. -/
theorem quasiIso_mapHomologicalComplex_map_of_acyclic {K J : CochainComplex D ℕ} (φ : K ⟶ J)
    [QuasiIso φ] (hK : ∀ a, acyclic T (K.X a)) (hJ : ∀ a, acyclic T (J.X a)) :
    QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) :=
  HomologicalComplex.quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone T φ
    (acyclic_map_mappingCone_extendMap T φ hK hJ)

end Stacks.RightDerivedComp
