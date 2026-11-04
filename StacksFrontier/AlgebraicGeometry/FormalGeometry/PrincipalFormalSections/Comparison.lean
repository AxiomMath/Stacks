module

public import Mathlib.Algebra.Colimit.Module
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Limit

/-!
# The comparison map at a principal formal locus

Let `A` be a commutative ring, `f ∈ A`, `𝔞 ⊆ A` an ideal, `U = Spec A ∖ V(𝔞)` and `M` an
`A`-module. The *formal locus* of `f` in `U` is `U ∩ V(f)`, and this file constructs the canonical
map

`colim_V Γ(V, M̃) ⟶ lim_n Γ(U, (M/fⁿM)~)`

of [Stacks, Tag 0EIH], the colimit being over the opens `V ⊆ U` containing `U ∩ V(f)`.

The map at a single neighbourhood `V` reduces a section of `M̃` on `V` modulo `fⁿ` and then extends
the result from `V` back to `U`. The extension is canonical and has nothing to do with `M`: the
module `M/fⁿM` is annihilated by `fⁿ`, so the sheaf `(M/fⁿM)~` vanishes on the open locus `D(f)`
where `f` is invertible, which contains `U ∖ V`; so restriction from `U` to `V` is bijective on
sections of `(M/fⁿM)~`.

## Main definitions

* `Stacks.Algebraization.FormalSections.OpenNearVanishing` — the opens `V` with
  `U ∩ V(f) ⊆ V ⊆ U`, ordered by reverse inclusion.
* `Stacks.Algebraization.FormalSections.colimNear` — the colimit `colim_V Γ(V, M̃)`.
* `Stacks.Algebraization.FormalSections.extendQuot` — the canonical extension of sections of
  `(M/fⁿM)~` from `V` to `U`.
* `Stacks.Algebraization.FormalSections.formalComparison` — the comparison map.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)
open Stacks.LocalCohomology

universe u v

namespace Stacks.Algebraization.FormalSections

/-- `U = Spec A ∖ V(𝔞)`, as an open subset of `Spec A`. -/
abbrev complOpen (A : Type u) [CommRing A] (a : Ideal A) : Opens (PrimeSpectrum.Top A) :=
  complementZeroLocus A a

variable (A : Type u) [CommRing A] (a : Ideal A) (f : A)

/-- An open neighbourhood of the formal locus `U ∩ V(f)` inside `U = Spec A ∖ V(𝔞)`: an open
`V ⊆ U` containing every point of `U` at which `f` vanishes. -/
structure OpenNearVanishing where
  /-- The underlying open subset of `Spec A`. -/
  carrier : Opens (PrimeSpectrum.Top A)
  /-- It is contained in `U`. -/
  le_complement : carrier ≤ complOpen A a
  /-- It contains the formal locus. -/
  vanishing_le : ∀ p : PrimeSpectrum A, p ∈ complOpen A a → f ∈ p.asIdeal → p ∈ carrier

namespace OpenNearVanishing

variable {A a f}

/-- Neighbourhoods of the formal locus are ordered by reverse inclusion. -/
instance : Preorder (OpenNearVanishing A a f) where
  le V W := W.carrier ≤ V.carrier
  le_refl _ := le_refl _
  le_trans _ _ _ h₁ h₂ := le_trans h₂ h₁

/-- `V ≤ W` exactly when the open `W` is contained in the open `V`. -/
theorem le_iff {V W : OpenNearVanishing A a f} : V ≤ W ↔ W.carrier ≤ V.carrier := Iff.rfl

/-- `U` itself is a neighbourhood of the formal locus. -/
instance : Nonempty (OpenNearVanishing A a f) :=
  ⟨⟨complOpen A a, le_refl _, fun _ hp _ ↦ hp⟩⟩

/-- Any two neighbourhoods of the formal locus have a common refinement, their intersection. -/
instance : IsDirectedOrder (OpenNearVanishing A a f) :=
  ⟨fun V W ↦ ⟨⟨V.carrier ⊓ W.carrier, inf_le_left.trans V.le_complement,
    fun p hp hpf ↦ ⟨V.vanishing_le p hp hpf, W.vanishing_le p hp hpf⟩⟩,
    (inf_le_left : V.carrier ⊓ W.carrier ≤ V.carrier),
    (inf_le_right : V.carrier ⊓ W.carrier ≤ W.carrier)⟩⟩

/-- Equality of neighbourhoods of the formal locus is decided classically. -/
instance : DecidableEq (OpenNearVanishing A a f) := Classical.decEq _

end OpenNearVanishing

variable (M : ModuleCat.{v} A)

/-- The sections of `M̃` on a neighbourhood of the formal locus. -/
abbrev nearSections (V : OpenNearVanishing A a f) : Type (max u v) :=
  moduleSections M V.carrier

/-- The directed system of sections on the neighbourhoods of the formal locus: restriction to a
smaller neighbourhood. -/
def nearRestrict : ∀ V W : OpenNearVanishing A a f, V ≤ W →
    nearSections A a f M V →ₗ[A] nearSections A a f M W :=
  fun _ _ h ↦ moduleSectionsRestrict M h

/-- The sections of `M̃` on the neighbourhoods of the formal locus, with the restriction maps, form
a directed system. -/
instance : DirectedSystem (fun V : OpenNearVanishing A a f ↦ nearSections A a f M V)
    (fun _ _ h ↦ (nearRestrict A a f M _ _ h : _ → _)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- **`colim_V Γ(V, M̃)`**: the colimit of the sections of `M̃` over the opens `V` with
`U ∩ V(f) ⊆ V ⊆ U`, ordered by reverse inclusion. -/
abbrev colimNear : Type (max u v) :=
  Module.DirectLimit (fun V : OpenNearVanishing A a f ↦ nearSections A a f M V)
    (nearRestrict A a f M)

/-! ### Canonical extension of the quotient sections -/

/-- Restriction of sections of `(M/fⁿM)~` from `U` to a neighbourhood of the formal locus is
bijective. -/
theorem bijective_restrict_quot (V : OpenNearVanishing A a f) (n : ℕ) :
    Function.Bijective (moduleSectionsRestrict (Quot f M n) V.le_complement) :=
  bijective_moduleSectionsRestrict_of_smul_eq_zero (pow_smul_quot_eq_zero f M n)
    V.le_complement fun q hq hqV hmem ↦
      hqV (V.vanishing_le q hq (q.2.mem_of_pow_mem n hmem))

/-- The canonical extension of a section of `(M/fⁿM)~` from a neighbourhood of the formal locus to
all of `U`. -/
def extendQuot (V : OpenNearVanishing A a f) (n : ℕ) :
    moduleSections (Quot f M n) V.carrier →ₗ[A]
      moduleSections (Quot f M n) (complOpen A a) :=
  (LinearEquiv.ofBijective _ (bijective_restrict_quot A a f M V n)).symm.toLinearMap

/-- Restricting the extension `extendQuot` of a section back to the neighbourhood recovers the
section. -/
@[simp]
theorem restrict_extendQuot (V : OpenNearVanishing A a f) (n : ℕ)
    (t : moduleSections (Quot f M n) V.carrier) :
    moduleSectionsRestrict (Quot f M n) V.le_complement (extendQuot A a f M V n t) = t :=
  (LinearEquiv.ofBijective _ (bijective_restrict_quot A a f M V n)).apply_symm_apply t

/-- Sections of `(M/fⁿM)~` on `U` that agree on a neighbourhood of the formal locus are equal. -/
theorem extendQuot_injective_aux (V : OpenNearVanishing A a f) (n : ℕ)
    {s t : moduleSections (Quot f M n) (complOpen A a)}
    (h : moduleSectionsRestrict (Quot f M n) V.le_complement s =
      moduleSectionsRestrict (Quot f M n) V.le_complement t) : s = t :=
  (bijective_restrict_quot A a f M V n).1 h

/-! ### The comparison map -/

/-- The extended reductions of a section of `M̃` modulo `fⁿ⁺¹` and modulo `fⁿ` are compatible under
the transition map `M/fⁿ⁺¹M → M/fⁿM`. -/
theorem nbhdComparison_compat (V : OpenNearVanishing A a f) (s : nearSections A a f M V) (n : ℕ) :
    moduleSectionsMap (quotLe f M (Nat.le_succ n)) (complOpen A a)
        (extendQuot A a f M V (n + 1)
          (moduleSectionsMap (quotMk f M (n + 1)) V.carrier s)) =
      extendQuot A a f M V n (moduleSectionsMap (quotMk f M n) V.carrier s) := by
  refine extendQuot_injective_aux A a f M V n ?_
  rw [restrict_extendQuot, ← moduleSectionsMap_restrict, restrict_extendQuot,
    ← moduleSectionsMap_comp_apply, quotMk_comp_quotLe]

/-- The comparison at a single neighbourhood: reduce a section of `M̃` modulo every power of `f`
and extend the results from the neighbourhood back to `U`. -/
def nbhdComparison (V : OpenNearVanishing A a f) :
    nearSections A a f M V →ₗ[A] formalLimit f M (complOpen A a) where
  toFun s := ⟨fun n ↦ extendQuot A a f M V n (moduleSectionsMap (quotMk f M n) V.carrier s),
    nbhdComparison_compat A a f M V s⟩
  map_add' s t := Subtype.ext (funext fun n ↦ by simp only [map_add]; rfl)
  map_smul' c s := Subtype.ext (funext fun n ↦ by
    simp only [map_smul, RingHom.id_apply]; rfl)

/-- The `n`-th component of `nbhdComparison` extends to `U` the reduction modulo `fⁿ`. -/
@[simp]
theorem nbhdComparison_apply (V : OpenNearVanishing A a f) (s : nearSections A a f M V) (n : ℕ) :
    (nbhdComparison A a f M V s).1 n =
      extendQuot A a f M V n (moduleSectionsMap (quotMk f M n) V.carrier s) := rfl

/-- The comparison maps at the neighbourhoods are compatible with restriction to a smaller
neighbourhood. -/
theorem nbhdComparison_restrict {V W : OpenNearVanishing A a f} (h : V ≤ W)
    (s : nearSections A a f M V) :
    nbhdComparison A a f M W (nearRestrict A a f M V W h s) = nbhdComparison A a f M V s := by
  refine Subtype.ext (funext fun n ↦ extendQuot_injective_aux A a f M W n ?_)
  rw [nbhdComparison_apply, nbhdComparison_apply, restrict_extendQuot]
  exact (congrArg (moduleSectionsRestrict (Quot f M n) h)
    (restrict_extendQuot A a f M V n (moduleSectionsMap (quotMk f M n) V.carrier s))).symm

/-- **The comparison map of [Stacks, Tag 0EIH]**: from the colimit of the sections of `M̃` over the
opens `V` with `U ∩ V(f) ⊆ V ⊆ U` to the inverse limit of the sections of `(M/fⁿM)~` on `U`. -/
def formalComparison : colimNear A a f M →ₗ[A] formalLimit f M (complOpen A a) :=
  Module.DirectLimit.lift A (OpenNearVanishing A a f) _ (nearRestrict A a f M)
    (nbhdComparison A a f M) fun _ _ h s ↦ nbhdComparison_restrict A a f M h s

/-- On the image of the sections over a neighbourhood `V`, `formalComparison` is `nbhdComparison`
at `V`. -/
@[simp]
theorem formalComparison_of (V : OpenNearVanishing A a f) (s : nearSections A a f M V) :
    formalComparison A a f M
        (Module.DirectLimit.of A (OpenNearVanishing A a f) _ (nearRestrict A a f M) V s) =
      nbhdComparison A a f M V s :=
  Module.DirectLimit.lift_of _ _ _

end Stacks.Algebraization.FormalSections

end
