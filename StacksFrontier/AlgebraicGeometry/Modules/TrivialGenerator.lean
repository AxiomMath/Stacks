module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne

/-!
# Generators of a trivial module

A global section `g` of an `𝒪_X`-module `G` *generates* `G` when, over every open `O`, every
section of `G` is `f • g|_O` for exactly one function `f` on `O`
(`Stacks.TrivialGenerator.IsGen`). A trivial module has a generator, namely the image of `1`
under an isomorphism with `𝒪_X` (`Stacks.TrivialGenerator.exists_isGen_of_iso`). Division by a
generator, `Stacks.TrivialGenerator.divGen`, turns sections of `G` into functions; it is additive,
linear over functions, and commutes with restriction.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.TrivialGenerator

variable {X : Scheme.{u}} (G : X.Modules)

/-- The structure sheaf as a module over itself. -/
noncomputable abbrev unitMod (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The restriction of a global section to an open. -/
noncomputable abbrev resTop (g : Γ(G, ⊤)) (O : X.Opens) : Γ(G, O) :=
  G.presheaf.map (homOfLE le_top).op g

/-- **`g` generates `G`**: over every open, multiplication of `g` by functions is bijective. -/
def IsGen (g : Γ(G, ⊤)) : Prop :=
  ∀ O : X.Opens, Function.Bijective (fun f : Γ(X, O) => f • resTop G g O)

variable {G}

/-- Division by a generator. -/
noncomputable def divGen {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) : Γ(G, O) → Γ(X, O) :=
  (Equiv.ofBijective _ (hg O)).symm

/-- Multiplying the generator by the quotient of a section recovers the section. -/
theorem divGen_smul_resTop {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) (m : Γ(G, O)) :
    divGen hg O m • resTop G g O = m :=
  (Equiv.ofBijective _ (hg O)).apply_symm_apply m

/-- A function is the quotient of `m` by the generator exactly when it carries the generator
to `m`. -/
theorem divGen_eq_iff {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) (m : Γ(G, O))
    (f : Γ(X, O)) : divGen hg O m = f ↔ f • resTop G g O = m := by
  constructor
  · rintro rfl; exact divGen_smul_resTop hg O m
  · rintro rfl; exact (Equiv.ofBijective _ (hg O)).symm_apply_apply f

/-- Division by a generator is linear over the functions on the open. -/
theorem divGen_smul {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) (f : Γ(X, O)) (m : Γ(G, O)) :
    divGen hg O (f • m) = f * divGen hg O m := by
  rw [divGen_eq_iff, mul_smul, divGen_smul_resTop]

/-- Division by a generator is additive. -/
theorem divGen_add {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) (m m' : Γ(G, O)) :
    divGen hg O (m + m') = divGen hg O m + divGen hg O m' := by
  rw [divGen_eq_iff, add_smul, divGen_smul_resTop, divGen_smul_resTop]

/-- The zero section divides to the zero function. -/
theorem divGen_zero {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) :
    divGen hg O 0 = 0 := by
  rw [divGen_eq_iff, zero_smul]

/-- Division by a generator commutes with restriction to a smaller open. -/
theorem divGen_map {g : Γ(G, ⊤)} (hg : IsGen G g) {O O' : X.Opens} (h : O ≤ O')
    (m : Γ(G, O')) :
    divGen hg O (G.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (divGen hg O' m) := by
  rw [divGen_eq_iff]
  conv_rhs => rw [← divGen_smul_resTop hg O' m]
  rw [Scheme.Modules.map_smul]
  congr 1
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- A generator divides itself to the unit function. -/
theorem divGen_resTop {g : Γ(G, ⊤)} (hg : IsGen G g) (O : X.Opens) :
    divGen hg O (resTop G g O) = 1 := by
  rw [divGen_eq_iff, one_smul]

/-- **A module isomorphic to `𝒪_X` has a generator**: the image of `1`. -/
theorem exists_isGen_of_iso (e : unitMod X ≅ G) :
    ∃ g : Γ(G, ⊤), IsGen G g := by
  let one : ∀ O : X.Opens, Γ(unitMod X, O) := fun O => (1 : Γ(X, O))
  refine ⟨Scheme.Modules.Hom.app e.hom ⊤ (one ⊤), fun O => ?_⟩
  have h1 : (unitMod X).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (one ⊤) = one O :=
    map_one (X.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
  have hnat : resTop G (Scheme.Modules.Hom.app e.hom ⊤ (one ⊤)) O =
      Scheme.Modules.Hom.app e.hom O (one O) := by
    have := congr($(e.hom.mapPresheaf.naturality (homOfLE (le_top : O ≤ ⊤)).op) (one ⊤))
    simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply, h1] at this
    exact this.symm
  have hlin : (fun f : Γ(X, O) => f • resTop G (Scheme.Modules.Hom.app e.hom ⊤ (one ⊤)) O) =
      Scheme.Modules.Hom.app e.hom O := by
    funext f
    rw [hnat]
    refine (Scheme.Modules.Hom.app_smul e.hom f (one O)).symm.trans ?_
    congr 1
    exact mul_one f
  rw [hlin]
  exact ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom O)

end Stacks.TrivialGenerator

end
