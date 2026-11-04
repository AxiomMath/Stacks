module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support

/-!
# A quasi-coherent sheaf of ideals on an integral scheme has empty or full support

On an integral scheme the support of a quasi-coherent submodule of the structure sheaf is either
empty or the whole space (`supp_eq_empty_or_eq_univ`). In particular a nonzero quasi-coherent
sheaf of ideals on an integral scheme has full support. No Noetherian, finite type or coherence
hypothesis is needed.

## Main results

* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.support_eq_univ_of_injective_smul`: a module
  admitting an injective multiplicative map to a domain, with a nonzero element, has full support.
* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.support_sections_eq_univ`: over a nonempty open
  of an integral scheme, the sections of a submodule of the structure sheaf have full support as
  a module over the ring of sections.
* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.mem_supp_of_ne_zero_sections`: a nonzero section
  over an affine open puts every point of that open in the support.
* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_nonempty`: if the support is
  nonempty it is everything.
* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_empty_or_eq_univ`: the same, as a
  dichotomy.
* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_not_isZero`: a submodule of the
  structure sheaf that is not the zero sheaf has full support.
* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.genericPoint_mem_supp_of_not_isZero`: the generic
  point lies in the support of any such submodule.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory SheafOfModules TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.Tag01YHFullSupport

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### The module-theoretic core -/

/-- **A module with a nonzero element that injects multiplicatively into a domain has full
support.** -/
theorem support_eq_univ_of_injective_smul {A : Type u} [CommRing A] [IsDomain A]
    {M : Type u} [AddCommGroup M] [Module A M] (f : M → A)
    (hinj : ∀ x : M, f x = 0 → x = 0) (hsmul : ∀ (r : A) (x : M), f (r • x) = r * f x)
    {m : M} (hm : m ≠ 0) : Module.support A M = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  rw [Module.mem_support_iff']
  refine ⟨m, fun r hr hrm => ?_⟩
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hfm : f m ≠ 0 := fun h => hm (hinj m h)
  have hf0 : f 0 = 0 := by simpa using hsmul 0 0
  have hzero : r * f m = 0 := by rw [← hsmul, hrm, hf0]
  exact mul_ne_zero hr0 hfm hzero

/-- **A module whose support is nonempty is nonzero.** -/
theorem exists_ne_zero_of_mem_support {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] {p : PrimeSpectrum A} (hp : p ∈ Module.support A M) : ∃ m : M, m ≠ 0 := by
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  have h1 : (1 : A) ∉ p.asIdeal := fun h =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  exact ⟨m, by simpa using hm 1 h1⟩

/-! ### Sections of a submodule of the structure sheaf -/

variable {Z : Scheme.{u}}

/-- **Over a nonempty open of an integral scheme, the sections of a submodule of the structure
sheaf have full support as soon as one of them is nonzero.** -/
theorem support_sections_eq_univ [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule) (V : Z.Opens) [Nonempty V]
    (m : Γ(N.toSheafOfModules, V)) (hm : m ≠ 0) :
    Module.support Γ(Z, V) Γ(N.toSheafOfModules, V) = Set.univ :=
  support_eq_univ_of_injective_smul (fun x : Γ(N.toSheafOfModules, V) => (x.val : Γ(Z, V)))
    (fun _ h => Subtype.ext h) (fun _ _ => rfl) hm

/-- **A nonzero section over an affine open puts every point of that open in the support.** -/
theorem mem_supp_of_ne_zero_sections [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent)
    (V : Z.affineOpens) {y : Z} (hy : y ∈ V.1)
    (m : Γ(N.toSheafOfModules, V.1)) (hm : m ≠ 0) :
    y ∈ SheafOfModules.supp N.toSheafOfModules := by
  have := hq
  have : Nonempty V.1 := ⟨⟨y, hy⟩⟩
  refine (Scheme.Modules.mem_support_sections_iff_mem_supp
    (N.toSheafOfModules : Z.Modules) V y hy).mp ?_
  rw [support_sections_eq_univ N V.1 m hm]
  trivial

/-- **An affine open that meets the support is contained in it.** -/
theorem mem_supp_of_mem_affineOpen [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent)
    (V : Z.affineOpens) {x y : Z} (hx : x ∈ V.1) (hy : y ∈ V.1)
    (hxs : x ∈ SheafOfModules.supp N.toSheafOfModules) :
    y ∈ SheafOfModules.supp N.toSheafOfModules := by
  have := hq
  have : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := exists_ne_zero_of_mem_support
    ((Scheme.Modules.mem_support_sections_iff_mem_supp
      (N.toSheafOfModules : Z.Modules) V x hx).mpr hxs)
  exact mem_supp_of_ne_zero_sections N hq V hy m hm

/-! ### The dichotomy -/

/-- Every point of a scheme lies in some affine open. -/
theorem exists_affineOpen_mem (x : Z) : ∃ V : Z.affineOpens, x ∈ V.1 := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨V, hV⟩, hxV⟩

/-- The generic point lies in every affine open of an integral scheme that contains a point. -/
private theorem genericPoint_mem_of_mem [IsIntegral Z] {V : Z.affineOpens} {x : Z} (hx : x ∈ V.1) :
    genericPoint Z ∈ V.1 :=
  ((genericPoint_spec Z).mem_open_set_iff V.1.isOpen).mpr ⟨x, Set.mem_univ x, hx⟩

/-- **The generic point lies in the support as soon as the support is nonempty.** -/
theorem genericPoint_mem_supp_of_nonempty [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent)
    (hne : (SheafOfModules.supp N.toSheafOfModules).Nonempty) :
    genericPoint Z ∈ SheafOfModules.supp N.toSheafOfModules := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hxV⟩ := exists_affineOpen_mem x
  exact mem_supp_of_mem_affineOpen N hq V hxV (genericPoint_mem_of_mem hxV) hx

/-- **A quasi-coherent submodule of the structure sheaf of an integral scheme with nonempty
support has full support.** -/
theorem supp_eq_univ_of_nonempty [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent)
    (hne : (SheafOfModules.supp N.toSheafOfModules).Nonempty) :
    SheafOfModules.supp N.toSheafOfModules = Set.univ := by
  have hg := genericPoint_mem_supp_of_nonempty N hq hne
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨V, hyV⟩ := exists_affineOpen_mem y
  exact mem_supp_of_mem_affineOpen N hq V (genericPoint_mem_of_mem hyV) hyV hg

/-- **On an integral scheme the support of a quasi-coherent submodule of the structure sheaf is
empty or everything.** -/
theorem supp_eq_empty_or_eq_univ [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent) :
    SheafOfModules.supp N.toSheafOfModules = ∅ ∨
      SheafOfModules.supp N.toSheafOfModules = Set.univ :=
  (SheafOfModules.supp N.toSheafOfModules).eq_empty_or_nonempty.imp id
    (supp_eq_univ_of_nonempty N hq)

/-- **A nonzero quasi-coherent sheaf of ideals on an integral scheme has full support**: if the
associated sheaf of modules is not a zero object, its support is the whole space. -/
theorem supp_eq_univ_of_not_isZero [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent)
    (hN : ¬ Limits.IsZero (N.toSheafOfModules : Z.Modules)) :
    SheafOfModules.supp N.toSheafOfModules = Set.univ := by
  refine supp_eq_univ_of_nonempty N hq (Set.nonempty_iff_ne_empty.mpr fun h => hN ?_)
  exact DevissageNoetherian.isZero_of_supp_eq_empty (N.toSheafOfModules : Z.Modules) h

/-- **The generic point lies in the support of a nonzero quasi-coherent sheaf of ideals on an
integral scheme.** -/
theorem genericPoint_mem_supp_of_not_isZero [IsIntegral Z]
    (N : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hq : (N.toSheafOfModules : Z.Modules).IsQuasicoherent)
    (hN : ¬ Limits.IsZero (N.toSheafOfModules : Z.Modules)) :
    genericPoint Z ∈ SheafOfModules.supp N.toSheafOfModules := by
  rw [supp_eq_univ_of_not_isZero N hq hN]
  trivial

end Stacks.AlgebraicGeometry.Tag01YHFullSupport

end
