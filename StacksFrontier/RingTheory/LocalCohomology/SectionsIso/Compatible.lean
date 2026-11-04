module

public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Localizations

/-!
# Compatible families of sections, in the Čech model

Let `R` be a commutative ring, `f : Fin r → R` a finite family, `I = (f₁, …, f_r)` and `M` an
`R`-module whose universe is independent of the ring's. The sheaf axiom of
`StacksFrontier/RingTheory/LocalCohomology/BasicOpenSections/Glue.lean` describes the sections of `M̃`
on `U = Spec R \ V(I)` as the families of sections on the standard opens `D(f_i)` agreeing at every
common point. This file translates that condition into the language of the Čech complex: a family
`(m_i)` of elements of the localizations `M_{f_i}` is *Čech compatible* when the images of `m_a`
and `m_b` in `M_{∏ i ∈ t, f i}` agree for every finite set `t` of indices containing both `a`
and `b`.

That the two conditions match is the content of the file, and it is the statement that restriction
of sections is the transition map of the Čech complex
(`Stacks.LocalCohomology.cechSectionsEquiv_restrict`) together with the observation that
`D(∏ i ∈ t, f i)` is the set of primes missing every `f i`, `i ∈ t`: agreeing at every point of
`D(f_a) ∩ D(f_b)` is agreeing after restriction to `D(f_a f_b)`, and a section of `M̃` on the
latter is an element of `M_{f_a f_b}`.

Quantifying over all finite `t ∋ a, b` rather than only over `t = {a, b}` costs nothing — the
condition for a larger `t` follows from the one for `{a, b}` by composing transition maps — and it
removes the need to transport a localization along `{a, b} = {b, a}`.

## Main definitions

* `Stacks.LocalCohomology.cechCompatible` — the Čech compatible families, as an `R`-submodule of
  `∏ i, M_{f_i}`.
* `Stacks.LocalCohomology.cechFamilyEquiv` — the family of identifications
  `Γ(D(f_i), M̃) ≅ M_{f_i}`, assembled.
* `Stacks.LocalCohomology.compatibleSectionsEquivCechCompatible` — **the two compatibility
  conditions agree**.
* `Stacks.LocalCohomology.moduleSectionsComplementEquivCechCompatible` —
  `Γ(Spec R \ V(I), M̃) ≅ { Čech compatible families }`.

## Main results

* `Stacks.LocalCohomology.mem_cechCompatible_iff` — a family of local sections is compatible in the
  sense of the sheaf axiom exactly when the corresponding family of fractions is Čech compatible.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat.{v} R)

/-- The **Čech compatible families**: the families `(m_i)` of elements of the localizations
`M_{f_i}` whose images in `M_{∏ i ∈ t, f i}` agree, for every finite set `t` of indices containing
the two indices compared. These are the families that glue to a section of `M̃` on
`Spec R \ V(I)`. -/
def cechCompatible : Submodule R (∀ i : Fin r, Cech.cechMod f (M : Type _) {i}) where
  carrier := {x | ∀ (a b : Fin r) (t : Finset (Fin r)) (ha : a ∈ t) (hb : b ∈ t),
    Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2 ha) (x a) =
      Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2 hb) (x b)}
  add_mem' hx hy a b t ha hb := by
    simp only [Pi.add_apply, map_add]
    rw [hx a b t ha hb, hy a b t ha hb]
  zero_mem' a b t ha hb := by simp only [Pi.zero_apply, map_zero]
  smul_mem' c {_x} hx a b t ha hb := by
    simp only [Pi.smul_apply, map_smul]
    rw [hx a b t ha hb]

/-- The identifications `Γ(D(f_i), M̃) ≅ M_{f_i}` of
`Stacks.LocalCohomology.cechSectionsEquiv`, assembled into a single equivalence of the product
modules. -/
def cechFamilyEquiv :
    (∀ i : Fin r, moduleSections M (cechBasicOpen f {i})) ≃ₗ[R]
      (∀ i : Fin r, Cech.cechMod f (M : Type _) {i}) :=
  LinearEquiv.piCongrRight fun i => cechSectionsEquiv f M {i}

/-- The `i`-th component of `cechFamilyEquiv f M x` is the fraction
`cechSectionsEquiv f M {i} (x i)` corresponding to the `i`-th section. -/
@[simp]
theorem cechFamilyEquiv_apply (x : ∀ i : Fin r, moduleSections M (cechBasicOpen f {i}))
    (i : Fin r) : cechFamilyEquiv f M x i = cechSectionsEquiv f M {i} (x i) :=
  rfl

/-- A prime missing `f a` and `f b` misses `∏ i ∈ {a, b}, f i`. -/
theorem mem_cechBasicOpen_pair {a b : Fin r} {p : PrimeSpectrum R}
    (hpa : p ∈ cechBasicOpen f {a}) (hpb : p ∈ cechBasicOpen f {b}) :
    p ∈ cechBasicOpen f {a, b} := by
  refine (mem_cechBasicOpen_iff f _ p).2 fun i hi => ?_
  rcases Finset.mem_insert.1 hi with rfl | hi
  · exact (mem_cechBasicOpen_iff f _ p).1 hpa _ (Finset.mem_singleton_self _)
  · obtain rfl := Finset.mem_singleton.1 hi
    exact (mem_cechBasicOpen_iff f _ p).1 hpb _ (Finset.mem_singleton_self _)

/-- Two local sections whose fractions have the same image in `M_{∏ i ∈ t, f i}` have the same
restrictions to `D(∏ i ∈ t, f i)`, and conversely: the identification of sections with fractions
is injective. -/
theorem restrict_eq_iff_cechι_eq {a b : Fin r} {t : Finset (Fin r)} (ha : a ∈ t) (hb : b ∈ t)
    (xa : moduleSections M (cechBasicOpen f {a})) (xb : moduleSections M (cechBasicOpen f {b})) :
    moduleSectionsRestrict M
          (cechBasicOpen_le_of_subset f (Finset.singleton_subset_iff.2 ha)) xa =
        moduleSectionsRestrict M
          (cechBasicOpen_le_of_subset f (Finset.singleton_subset_iff.2 hb)) xb ↔
      Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2 ha)
          (cechSectionsEquiv f M {a} xa) =
        Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2 hb)
          (cechSectionsEquiv f M {b} xb) := by
  rw [← cechSectionsEquiv_restrict_apply, ← cechSectionsEquiv_restrict_apply]
  exact ⟨fun h => congrArg _ h, fun h => (cechSectionsEquiv f M t).injective h⟩

/-- **The two compatibility conditions agree.** A family of sections of `M̃` on the standard opens
`D(f_i)` agrees at every common point of two of them exactly when the corresponding family of
fractions is Čech compatible. -/
theorem mem_cechCompatible_iff (x : ∀ i : Fin r, moduleSections M (cechBasicOpen f {i})) :
    cechFamilyEquiv f M x ∈ cechCompatible f M ↔
      x ∈ compatibleModuleSections M (fun i => cechBasicOpen f {i}) := by
  refine ⟨fun hy a b p hpa hpb => ?_, fun hx a b t ha hb =>
    (restrict_eq_iff_cechι_eq f M ha hb (x a) (x b)).1
      (Subtype.ext (funext fun q => hx a b q.1 _ _))⟩
  have h := (restrict_eq_iff_cechι_eq f M (t := {a, b}) (by simp) (by simp) (x a) (x b)).2
    (hy a b {a, b} (by simp) (by simp))
  exact congrFun (congrArg Subtype.val h) ⟨p, mem_cechBasicOpen_pair f hpa hpb⟩

/-- **`Γ(⋃ i, D(f_i), M̃) ≅ { Čech compatible families }`.** The sheaf axiom, with the compatible
families written in the Čech model. -/
def compatibleSectionsEquivCechCompatible :
    compatibleModuleSections M (fun i => cechBasicOpen f {i}) ≃ₗ[R] cechCompatible f M where
  toFun x := ⟨cechFamilyEquiv f M x.1, (mem_cechCompatible_iff f M x.1).2 x.2⟩
  map_add' x y := Subtype.ext (map_add (cechFamilyEquiv f M) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (cechFamilyEquiv f M) c x.1)
  invFun y := ⟨(cechFamilyEquiv f M).symm y.1,
    (mem_cechCompatible_iff f M _).1
      (by simpa only [LinearEquiv.apply_symm_apply] using y.2)⟩
  left_inv x := Subtype.ext ((cechFamilyEquiv f M).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((cechFamilyEquiv f M).apply_symm_apply y.1)

variable (I : Ideal R)

/-- **`Γ(Spec R \ V(I), M̃) ≅ { Čech compatible families }`.** The sections of the quasi-coherent
module generated by `M` on the complement of the zero locus of `I = (f₁, …, f_r)` are the families
of fractions `m_i ∈ M_{f_i}` whose images agree in every further localization. -/
def moduleSectionsComplementEquivCechCompatible (hIf : Ideal.span (Set.range f) = I) :
    moduleSections M (complementZeroLocus R I) ≃ₗ[R] cechCompatible f M :=
  ((moduleSectionsCongr M (complementZeroLocus_eq_iSup_cechBasicOpen f I hIf)).trans
    (moduleSectionsCoverEquiv M _)).trans (compatibleSectionsEquivCechCompatible f M)

end Stacks.LocalCohomology

end
