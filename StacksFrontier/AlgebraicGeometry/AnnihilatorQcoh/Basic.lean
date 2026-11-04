module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Exactness
public import StacksFrontier.AlgebraicGeometry.Properties.IdealPowerAnnihilator
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# The subsheaf of sections annihilated by an ideal sheaf, and its affine sections

Let `X` be a scheme, `I` an ideal subsheaf of `𝒪_X` and `F` an `𝒪_X`-module.  The subsheaf of
`F` of sections annihilated by `I` is the *ideal transporter*: a section over `U` belongs to it
when **every** restriction of it is annihilated by the sections of `I` there.  This file
introduces that condition as a predicate `IsAnnihilatorSubsheaf I F N` on a submodule sheaf `N`
of `F`, so that the results below apply to every construction of the object, and proves the
affine description of its sections.

The predicate is a characterization, not a construction: three constructions of this subsheaf
already exist in the library and no fourth is introduced.  Existence is therefore a theorem
(`isAnnihilatorSubsheaf_annihilatorSubmodule`), uniqueness is another
(`IsAnnihilatorSubsheaf.unique`), and the supremum description the Stacks project uses is a
third (`isAnnihilatorSubsheaf_sSup`).

## Main definitions

* `IsAnnihilatorSubsheaf I F N`: the sections of `N` over every open `U` are exactly the
  sections of `F` over `U` all of whose restrictions are annihilated by the sections of `I`.

## Main results

* `isAnnihilatorSubsheaf_annihilatorSubmodule`: `Stacks.SheafOfModules.annihilatorSubmodule`
  satisfies the predicate, so such a subsheaf exists.
* `IsAnnihilatorSubsheaf.unique`: at most one submodule sheaf satisfies it.
* `isAnnihilatorSubsheaf_sSup`: the supremum of the submodule sheaves of `F` that `I`
  annihilates satisfies it; this is the description used in [Stacks, Tag 01PO].
* `IsAnnihilatorSubsheaf.smul_eq_zero`: `I` annihilates the sections of `N`, with no restriction
  taken.  This is the property a consumer of the subsheaf needs.
* `exists_pow_smul_mem_image`: for `U` affine and `f : Γ(X, U)`, a section of a quasi-coherent
  `I` over `X.basicOpen f` becomes a restriction from `U` after multiplication by a power of
  `f`.
* `smul_map_eq_zero_of_isAffineOpen`: **the engine.**  Over an affine open, annihilation by the
  sections of `I` on that open alone already implies annihilation after every restriction.
* `IsAnnihilatorSubsheaf.mem_iff_of_isAffineOpen`: **part (2) of [Stacks, Tag 01PO]** — over an
  affine open the sections of `N` are `{s | I(U) • s = 0}`.
* `isAnnihilatorSubsheaf_idealPowerAnnihilator`: the library's scheme-level
  `AlgebraicGeometry.idealPowerAnnihilator` also satisfies the predicate, for the ideal power.

## Implementation notes

Only quasi-coherence of `I` is used here; neither `F` nor `I` needs to be of finite type, and
`F` needs no hypothesis at all beyond being a sheaf.  Finite generation of the sections of `I`
enters only in the quasi-coherence and stalk assertions, in the sibling files.

The engine is a localization argument rather than a sheaf-theoretic one.  Over an affine `U`,
every open `V ≤ U` is covered by basic opens `X.basicOpen f` with `f : Γ(X, U)`, and over such a
basic open the sections of a quasi-coherent `I` are the localization of `Γ(I, U)` away from `f`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`).  So a section
`a` of `I` over `X.basicOpen f` satisfies `f ^ n * a = r|` for some `r : Γ(I, U)`, and `f` is a
unit there, which turns the hypothesis `r • s = 0` into `a • s| = 0`.  Being zero is a local
condition on a sheaf, so the conclusion follows on all of `V`.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.AnnihilatorQcoh

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The characterizing property -/

/-- **The subsheaf of sections annihilated by an ideal sheaf, as a property.** A submodule sheaf
`N` of `F` is *the* annihilator of the ideal subsheaf `I` when its sections over every open `U`
are exactly the sections of `F` over `U` all of whose restrictions are annihilated by the
sections of `I`.

Stating the property instead of constructing the object lets every result below be used with any
of the existing constructions of this subsheaf, and makes the construction a theorem
(`isAnnihilatorSubsheaf_annihilatorSubmodule`) rather than a definition. -/
def IsAnnihilatorSubsheaf (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    (F : X.Modules) (N : F.Submodule) : Prop :=
  ∀ (U : X.Opens) (s : Γ(F, U)),
    s ∈ N.toSubmodule.obj (op U) ↔
      ∀ (V : X.Opens) (h : V ≤ U) (a : Γ(X, V)), a ∈ I.toSubmodule.obj (op V) →
        a • F.presheaf.map (homOfLE h).op s = 0

variable {I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule} {F : X.Modules}

/-- A section restricted along the identity is unchanged, in the spelling the annihilator
condition produces. -/
theorem map_homOfLE_refl (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE (le_refl U)).op s = s := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, F.presheaf.map_id]
  rfl

/-- **At most one submodule sheaf is the annihilator of `I` in `F`.** -/
theorem IsAnnihilatorSubsheaf.unique {N₁ N₂ : F.Submodule}
    (h₁ : IsAnnihilatorSubsheaf I F N₁) (h₂ : IsAnnihilatorSubsheaf I F N₂) : N₁ = N₂ := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W ↦ ?_)
  obtain ⟨U⟩ := W
  exact Submodule.ext fun s ↦ (h₁ U s).trans (h₂ U s).symm

/-- **`I` annihilates the sections of its annihilator subsheaf.** This is the form a consumer
needs: no restriction is taken. -/
theorem IsAnnihilatorSubsheaf.smul_eq_zero {N : F.Submodule} (hN : IsAnnihilatorSubsheaf I F N)
    (U : X.Opens) (a : Γ(X, U)) (ha : a ∈ I.toSubmodule.obj (op U))
    (s : Γ(N.toSheafOfModules, U)) : a • s = 0 := by
  refine Subtype.ext ?_
  have h := (hN U (s.val : Γ(F, U))).mp s.property U (le_refl U) a ha
  rwa [map_homOfLE_refl F U (s.val : Γ(F, U))] at h

/-- The sections of `F` over `U` that `I` annihilates, with no restriction taken, in the form the
supremum description below quantifies over. -/
theorem IsAnnihilatorSubsheaf.smul_section_eq_zero {N : F.Submodule}
    (hN : IsAnnihilatorSubsheaf I F N) (U : X.Opens) {s : Γ(F, U)}
    (hs : s ∈ N.toSubmodule.obj (op U)) (a : Γ(X, U))
    (ha : a ∈ I.toSubmodule.obj (op U)) : a • s = 0 := by
  have h := (hN U s).mp hs U (le_refl U) a ha
  rwa [map_homOfLE_refl F U s] at h

/-! ### Existence: the ideal transporter -/

/-- The sections of the structure sheaf of a scheme commute, in the shape the general-site
annihilator construction takes as a hypothesis. The sections are a `RingCat`, so commutativity is
not an instance there; it is transported from the `CommRingCat` structure of `X.presheaf`. -/
theorem mul_comm_ringCatSheaf (X : Scheme.{u}) :
    ∀ (U : (X.Opens)ᵒᵖ) (a b : X.ringCatSheaf.obj.obj U), a * b = b * a := by
  intro U a b
  let _ : CommRing (X.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing (X.presheaf.obj U))
  exact mul_comm a b

/-- **The annihilator subsheaf exists**: the general-site ideal transporter
`Stacks.SheafOfModules.annihilatorSubmodule`, read on the site of opens of a scheme, satisfies
the characterizing property.

Only the indexing differs: the construction quantifies over morphisms `op U ⟶ Y` of the
opposite category of opens, and every such morphism is `(homOfLE h).op` for the inclusion of
`Y.unop`. Its membership lemma `mem_annihilatorSubmodule_obj` is `Iff.rfl`, so nothing else is
needed. -/
theorem isAnnihilatorSubsheaf_annihilatorSubmodule
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) :
    IsAnnihilatorSubsheaf I F
      (Stacks.SheafOfModules.annihilatorSubmodule F (mul_comm_ringCatSheaf X) I) :=
  fun _ _ ↦ ⟨fun h V hVU a ha ↦ h (op V) (homOfLE hVU).op a ha,
    fun h Y g a ha ↦ h Y.unop g.unop.le a ha⟩

/-- **The subsheaf of [Stacks, Tag 01PO]: the largest submodule sheaf of `F` that `I`
annihilates, and its sections.** The supremum is taken in the complete lattice of submodule
sheaves of `F`, and the conclusion unfolds to the statement that a section over `U` belongs to
it exactly when every restriction of it is annihilated by the sections of `I` there.

That this supremum is the *only* submodule sheaf with those sections is
`IsAnnihilatorSubsheaf.unique`, and `isAnnihilatorSubsheaf_annihilatorSubmodule` exhibits a
second, explicit model of it. Neither quasi-coherence nor finiteness is used. -/
@[stacks 01PO "the subsheaf"]
theorem isAnnihilatorSubsheaf_sSup
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) :
    IsAnnihilatorSubsheaf I F
      (sSup {N : F.Submodule | ∀ (U : X.Opens) (s : Γ(F, U)),
        s ∈ N.toSubmodule.obj (op U) →
          ∀ a : Γ(X, U), a ∈ I.toSubmodule.obj (op U) → a • s = 0}) := by
  set S := {N : F.Submodule | ∀ (U : X.Opens) (s : Γ(F, U)),
    s ∈ N.toSubmodule.obj (op U) →
      ∀ a : Γ(X, U), a ∈ I.toSubmodule.obj (op U) → a • s = 0}
  set A := Stacks.SheafOfModules.annihilatorSubmodule F (mul_comm_ringCatSheaf X) I
  have hAann : IsAnnihilatorSubsheaf I F A := isAnnihilatorSubsheaf_annihilatorSubmodule I F
  have hAmem : A ∈ S := fun U _ hs a ha ↦ hAann.smul_section_eq_zero U hs a ha
  have hle : sSup S ≤ A := by
    refine sSup_le fun N hN ↦ SheafOfModules.Submodule.le_iff.mpr
      (PresheafOfModules.Submodule.le_iff.mpr fun W ↦ ?_)
    obtain ⟨U⟩ := W
    intro s hs
    exact (hAann U s).mpr fun V hVU a ha ↦
      hN V _ (N.toSubmodule.map_mem (homOfLE hVU).op hs) a ha
  rw [le_antisymm hle (le_sSup hAmem)]
  exact hAann

/-! ### Localizing the ideal on a basic open -/

/-- **The sections of a quasi-coherent ideal sheaf over a basic open become restrictions after
multiplication by a power of the defining function.** This is
`IsLocalizedModule.Away.surj` for `I`, with the subtype bookkeeping of
`SheafOfModules.Submodule` discharged, so that it reads as a statement about elements of
`Γ(X, X.basicOpen f)`. -/
theorem exists_pow_smul_mem_image (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (b : Γ(X, X.basicOpen f)) (hb : b ∈ I.toSubmodule.obj (op (X.basicOpen f))) :
    ∃ (n : ℕ) (r : Γ(X, U)), r ∈ I.toSubmodule.obj (op U) ∧
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) * b =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op r := by
  let := moduleOfLE I.toSheafOfModules (X.basicOpen_le f)
  have hloc : IsLocalizedModule.Away f (restrictₗ I.toSheafOfModules (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ I.toSheafOfModules hU f rfl (X.basicOpen_le f)
  obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj
    (restrictₗ I.toSheafOfModules (X.basicOpen_le f)) f
    (show Γ(I.toSheafOfModules, X.basicOpen f) from ⟨b, hb⟩)
  exact ⟨n, y.val, y.property, congrArg Subtype.val hy⟩

/-- Restriction of a section of `X` whose basic open contains the target is a unit. -/
theorem isUnit_map_of_le_basicOpen {U V : X.Opens} (a : Γ(X, U)) (h : V ≤ X.basicOpen a) :
    IsUnit (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le a))).op a) := by
  have h2 : X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) =
      X.presheaf.map (homOfLE (h.trans (X.basicOpen_le a))).op a := by
    rw [← X.presheaf.map_comp_apply]
    rfl
  rw [← h2]
  exact (X.presheaf.map (homOfLE h).op).hom.isUnit_map (X.toRingedSpace.isUnit_res_basicOpen a)

/-- A unit scalar does not annihilate: if `r` is a unit and `r • m = 0`, then `m = 0`. -/
theorem eq_zero_of_isUnit_smul_eq_zero {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {r : R} (hr : IsUnit r) {m : M} (h : r • m = 0) : m = 0 := by
  obtain ⟨u, rfl⟩ := hr
  simpa using congrArg (fun z ↦ (↑u⁻¹ : R) • z) h

/-! ### Naming the sections of a submodule sheaf -/

/-- The underlying section of `F` of a section of a submodule sheaf of `F`. The sections of
`N.toSheafOfModules` are a subtype of `F.val.obj (op U)`, which is the same type as `Γ(F, U)` but
not the same expression, so the plain projection does not carry the module instances that
`Γ(F, U)` does; naming it once fixes the spelling. -/
def subVal (N : F.Submodule) {U : X.Opens} (z : Γ(N.toSheafOfModules, U)) : Γ(F, U) := z.1

/-- A section of `N` lies in `N`. -/
theorem subVal_mem (N : F.Submodule) {U : X.Opens} (z : Γ(N.toSheafOfModules, U)) :
    subVal N z ∈ N.toSubmodule.obj (op U) := z.2

/-- Every section of `F` lying in `N` is `subVal` of a section of `N`. -/
theorem subVal_mk (N : F.Submodule) {U : X.Opens} (s : Γ(F, U))
    (hs : s ∈ N.toSubmodule.obj (op U)) :
    subVal N (show Γ(N.toSheafOfModules, U) from ⟨s, hs⟩) = s := rfl

/-- Sections of `N` are determined by their underlying sections of `F`. -/
theorem subVal_injective (N : F.Submodule) {U : X.Opens} :
    Function.Injective (subVal N (U := U)) := fun _ _ h ↦ Subtype.ext h

/-! ### Finite generation of the sections of the ideal -/

/-- The underlying function of a section of an ideal subsheaf, at the spelling `Γ(X, U)`. The
sections of `I.toSheafOfModules` are a subtype of the sections of the unit, whose carrier is the
same type as `Γ(X, U)` but not the same expression; naming the coercion once keeps the ascription
out of every statement below. -/
def idealVal (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) {U : X.Opens}
    (z : Γ(I.toSheafOfModules, U)) : Γ(X, U) := z.1

/-- A section of `I` lies in `I`. -/
theorem idealVal_mem (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) {U : X.Opens}
    (z : Γ(I.toSheafOfModules, U)) : idealVal I z ∈ I.toSubmodule.obj (op U) := z.2

/-- Every element of `I` over `U` is `idealVal` of a section. -/
theorem idealVal_mk (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) {U : X.Opens}
    (a : Γ(X, U)) (ha : a ∈ I.toSubmodule.obj (op U)) :
    idealVal I (show Γ(I.toSheafOfModules, U) from ⟨a, ha⟩) = a := rfl

/-- `idealVal` is `Γ(X, U)`-linear. -/
theorem idealVal_smul (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) {U : X.Opens}
    (c : Γ(X, U)) (z : Γ(I.toSheafOfModules, U)) :
    idealVal I (c • z) = c * idealVal I z := rfl

/-- `idealVal` is additive. -/
theorem idealVal_add (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) {U : X.Opens}
    (z w : Γ(I.toSheafOfModules, U)) :
    idealVal I (z + w) = idealVal I z + idealVal I w := rfl

/-- **The sections of a quasi-coherent ideal sheaf of finite type over an affine open are a
finitely generated module.** This is `moduleFinite_sections_on_affine` with the generating set
produced. -/
theorem exists_finset_span_eq_top (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] [I.toSheafOfModules.IsFiniteType] {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ T : Finset Γ(I.toSheafOfModules, U),
      Submodule.span Γ(X, U) (T : Set Γ(I.toSheafOfModules, U)) = ⊤ := by
  have : Module.Finite Γ(X, U) Γ(I.toSheafOfModules, U) :=
    AlgebraicGeometry.moduleFinite_sections_on_affine I.toSheafOfModules U hU
  exact Module.Finite.fg_top

/-- **Annihilation by a generating family of `Γ(I, U)` is annihilation by all of `Γ(I, U)`.**
The target is an arbitrary `Γ(X, U)`-module, so that this serves both the sections of `F` over
`U` itself and its sections over a smaller open, where the module structure is restriction of
scalars. -/
theorem smul_eq_zero_of_span_eq_top (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    {U : X.Opens} {M : Type*} [AddCommGroup M] [Module Γ(X, U) M]
    (G : Set Γ(I.toSheafOfModules, U)) (hG : Submodule.span Γ(X, U) G = ⊤) (m : M)
    (h : ∀ z ∈ G, idealVal I z • m = 0) (r : Γ(X, U))
    (hr : r ∈ I.toSubmodule.obj (op U)) : r • m = 0 := by
  let φ : Γ(I.toSheafOfModules, U) →ₗ[Γ(X, U)] M :=
    { toFun := fun z ↦ idealVal I z • m
      map_add' := fun z w ↦ by simp [idealVal_add, add_smul]
      map_smul' := fun c z ↦ by simp [idealVal_smul, mul_smul] }
  have hker : (⊤ : Submodule Γ(X, U) Γ(I.toSheafOfModules, U)) ≤ LinearMap.ker φ := by
    rw [← hG, Submodule.span_le]
    exact h
  have := hker (Submodule.mem_top (x := show Γ(I.toSheafOfModules, U) from ⟨r, hr⟩))
  rw [LinearMap.mem_ker] at this
  simpa [φ, idealVal_mk] using this

/-! ### The engine: affine annihilation is already local annihilation -/

/-- **Over an affine open, annihilation by the sections of `I` there implies annihilation after
every restriction.** This is the content of part (2) of [Stacks, Tag 01PO], and it is what makes
the affine description of the annihilator subsheaf possible at all. Quasi-coherence of `I` is
used; nothing is assumed of `F` beyond being a sheaf, and no finiteness is used. -/
theorem smul_map_eq_zero_of_isAffineOpen (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(F, U))
    (hs : ∀ a : Γ(X, U), a ∈ I.toSubmodule.obj (op U) → a • s = 0)
    {V : X.Opens} (hVU : V ≤ U) (a : Γ(X, V)) (ha : a ∈ I.toSubmodule.obj (op V)) :
    a • F.presheaf.map (homOfLE hVU).op s = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
  intro x hx
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le (⟨x, hx⟩ : V) (hVU hx)
  refine ⟨X.basicOpen f, hfV, hxf, ?_⟩
  rw [map_zero, Scheme.Modules.map_smul, ← F.presheaf.map_comp_apply]
  -- Everything now lives over `W = X.basicOpen f`.
  set W : X.Opens := X.basicOpen f
  set aW : Γ(X, W) := X.presheaf.map (homOfLE hfV).op a
  obtain ⟨n, r, hrmem, hr⟩ :=
    exists_pow_smul_mem_image I hU f aW (I.toSubmodule.map_mem _ ha)
  have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n)) := by
    simpa using (isUnit_map_of_le_basicOpen f (le_refl (X.basicOpen f))).pow n
  refine eq_zero_of_isUnit_smul_eq_zero hunit ?_
  rw [smul_smul, hr]
  have := congrArg (F.presheaf.map (homOfLE (X.basicOpen_le f)).op) (hs r hrmem)
  rw [Scheme.Modules.map_smul, map_zero] at this
  convert this using 2
  rfl

/-! ### Part (2): the sections over an affine open -/

/-- **Part (2) of [Stacks, Tag 01PO].** Over an affine open `U`, the sections of the annihilator
subsheaf are exactly the sections of `F` annihilated by `Γ(I, U)`; no restriction has to be
tested. -/
@[stacks 01PO "part (2)"]
theorem IsAnnihilatorSubsheaf.mem_iff_of_isAffineOpen {N : F.Submodule}
    (hN : IsAnnihilatorSubsheaf I F N) [I.toSheafOfModules.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(F, U)) :
    s ∈ N.toSubmodule.obj (op U) ↔
      ∀ a : Γ(X, U), a ∈ I.toSubmodule.obj (op U) → a • s = 0 := by
  rw [hN U s]
  refine ⟨fun h a ha ↦ ?_, fun h V hVU a ha ↦ ?_⟩
  · have hU' := h U (le_refl U) a ha
    rwa [map_homOfLE_refl F U s] at hU'
  · exact smul_map_eq_zero_of_isAffineOpen I F hU s h hVU a ha

/-- **The scheme-level ideal-power annihilator is the annihilator subsheaf of the ideal
power.** Its membership lemma `AlgebraicGeometry.mem_idealPowerAnnihilator` is `Iff.rfl`, so this
is again only a reindexing, and it lets the three results of [Stacks, Tag 01PO] be read off for
the object [Stacks, Tag 01PQ] is stated about. -/
theorem isAnnihilatorSubsheaf_idealPowerAnnihilator
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ) :
    IsAnnihilatorSubsheaf (AlgebraicGeometry.idealPower I n) F
      (AlgebraicGeometry.idealPowerAnnihilator I F n) :=
  fun _ _ ↦ ⟨fun h V hVU a ha ↦ h (op V) (homOfLE hVU).op a ha,
    fun h Y g a ha ↦ h Y.unop g.unop.le a ha⟩

end Stacks.AlgebraicGeometry.AnnihilatorQcoh

end
