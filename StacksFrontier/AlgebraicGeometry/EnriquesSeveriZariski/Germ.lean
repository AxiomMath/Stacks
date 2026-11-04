module

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity

/-!
# Two facts about germs of sections of a coherent module

The *support* of a global section of an `𝒪_X`-module is the set of points at which its germ is
nonzero; it is a closed subset of `X`. And on a locally Noetherian scheme, a germ of a coherent
module lying in every power of the maximal ideal times the stalk is zero — the Krull
intersection theorem at a stalk.

## Main results

* `Stacks.EnriquesSeveriZariski.isClosed_germSupport`: the support of a global section is closed.
* `Stacks.EnriquesSeveriZariski.eq_zero_of_forall_mem_maximalIdeal_pow_smul`: a germ of a
  coherent module in every power of the maximal ideal times the stalk vanishes.

## Implementation notes

The support of a section is read off `AlgebraicGeometry.isOpen_germ_eq_zero`, which gives
openness of the vanishing locus of a section over an arbitrary open; over `⊤` the membership
side conditions are vacuous and the two sets are complementary.

The Krull statement is `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` at the stalk, whose three
hypotheses are: the stalk of the structure sheaf is a local ring (true on any scheme), it is
Noetherian (locally Noetherian scheme), and the stalk of the module is a finite module over it
(`SheafOfModules.finite_stalk`, for a coherent, hence finite type, module).

## References

* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.EnriquesSeveriZariski

variable {X : Scheme.{u}}

/-- **The support of a global section.** The points at which the germ of `t` is nonzero. -/
def germSupport (F : X.Modules) (t : Γ(F, ⊤)) : Set X :=
  {y : X | F.presheaf.germ ⊤ y (Opens.mem_top y) t ≠ 0}

/-- **The support of a global section is closed.** -/
theorem isClosed_germSupport (F : X.Modules) (t : Γ(F, ⊤)) : IsClosed (germSupport F t) := by
  rw [← isOpen_compl_iff]
  have hset : (germSupport F t)ᶜ =
      {x : X | x ∈ (⊤ : X.Opens) ∧ ∀ hx : x ∈ (⊤ : X.Opens),
        (ConcreteCategory.hom (F.presheaf.germ ⊤ x hx)) t = 0} := by
    ext y
    simp only [Set.mem_compl_iff, germSupport, Set.mem_setOf_eq, not_not]
    exact ⟨fun h => ⟨Opens.mem_top y, fun _ => h⟩, fun h => h.2 (Opens.mem_top y)⟩
  rw [hset]
  exact isOpen_germ_eq_zero F ⊤ t

/-- A point outside the support of a section has vanishing germ there. -/
theorem germ_eq_zero_of_notMem_germSupport (F : X.Modules) (t : Γ(F, ⊤)) {y : X}
    (hy : y ∉ germSupport F t) : F.presheaf.germ ⊤ y (Opens.mem_top y) t = 0 :=
  not_not.1 hy

/-- **The Krull intersection theorem at a stalk.** On a locally Noetherian scheme, an element of
the stalk of a coherent module lying in every power of the maximal ideal times the stalk is
zero. -/
theorem eq_zero_of_forall_mem_maximalIdeal_pow_smul [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (y : X) (m : F.presheaf.stalk y)
    (hm : ∀ j : ℕ, m ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ j) •
      (⊤ : Submodule (X.presheaf.stalk y) (F.presheaf.stalk y))) :
    m = 0 := by
  have : F.IsFiniteType := Stacks.Chow.isFiniteType_of_isCoherent F
  have hfin : Module.Finite (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F y
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
    (M := (F.presheaf.stalk y : Type u)) (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hmem : m ∈ (⨅ j : ℕ, (IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ j) •
      (⊤ : Submodule (X.presheaf.stalk y) (F.presheaf.stalk y))) :=
    Submodule.mem_iInf _ |>.2 hm
  rw [hbot] at hmem
  simpa using hmem

end Stacks.EnriquesSeveriZariski

end
