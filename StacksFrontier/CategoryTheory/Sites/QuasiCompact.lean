module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact objects of a site and of a topos

There are two notions, for the two categories in play: quasi-compact objects of a site, and
quasi-compact objects of the topos of sheaves of sets on a site.

## Main definitions

* `CategoryTheory.GrothendieckTopology.IsQuasiCompactObject`: an object `U` of a site is
  quasi-compact when every covering of `U` is refined by a covering whose morphism to it has
  finite index image.
* `CategoryTheory.Sheaf.IsQuasiCompact`: a sheaf of sets is quasi-compact when every locally
  surjective map onto it from a coproduct restricts to a locally surjective map from a coproduct
  over a finite subset of the index set.
* `CategoryTheory.GrothendieckTopology.IsQuasiCompactTopos`: the topos of sheaves of sets on a
  site is quasi-compact when its final object is.

## Main results

* `CategoryTheory.GrothendieckTopology.isQuasiCompactObject_bot`: for the trivial topology every
  object is quasi-compact.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

universe v u

variable {C : Type u} [Category.{v} C]

/-- An object `U` of a site `C` is *quasi-compact* if every covering `𝒰 = {U i ⟶ U}` of `U`,
given as a `PreZeroHypercover` whose generated sieve `sieve₀` belongs to `J`, admits a covering
`𝒱 = {V j ⟶ U}` together with a morphism `φ : 𝒱 ⟶ 𝒰` over `𝟙 U` whose index map `φ.s₀` has
finite image. -/
@[stacks 090H "A quasi-compact object of a site: every covering is refined by one that
  factors through only finitely many of its members.", sga "4 VI 1.1", sga "6 II 2.1.1"]
def IsQuasiCompactObject (J : GrothendieckTopology C) (U : C) : Prop :=
  ∀ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J U →
    ∃ (𝒱 : PreZeroHypercover.{max u v} U) (φ : 𝒱.Hom 𝒰),
      𝒱.sieve₀ ∈ J U ∧ (Set.range φ.s₀).Finite

/-- For the trivial topology `⊥`, where the only covering sieve of `U` is the maximal one, every
object is quasi-compact. -/
theorem isQuasiCompactObject_bot (U : C) :
    IsQuasiCompactObject (⊥ : GrothendieckTopology C) U := by
  intro 𝒰 h𝒰
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1
    (show 𝒰.sieve₀ (𝟙 U) by rw [bot_covering.1 h𝒰]; trivial)
  exact ⟨{ I₀ := PUnit, X := fun _ => U, f := fun _ => 𝟙 U },
    { s₀ := fun _ => i, h₀ := fun _ => a, w₀ := fun _ => ha.symm },
    bot_covering.2 (Sieve.id_mem_iff_eq_top.1 (Sieve.ofArrows_mk _ _ PUnit.unit)),
    Set.finite_range _⟩

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An object `F` of the topos `Sh(C)` of sheaves of sets on a site is *quasi-compact* if for
every locally surjective map `∐_{i ∈ I} G i ⟶ F` of sheaves there is a finite subset `T ⊆ I` for
which `∐_{i ∈ T} G i ⟶ F` is still locally surjective. -/
@[stacks 0D07 "A quasi-compact object of the topos of sheaves of sets on a site.",
  sga "4 IV 8.7" "more general", sga "4 IX 1.2"]
def IsQuasiCompact (F : Sheaf J (Type max v u)) : Prop :=
  ∀ (I : Type max v u) (G : I → Sheaf J (Type max v u)) (f : ∀ i, G i ⟶ F),
    Sheaf.IsLocallySurjective (Sigma.desc f) →
      ∃ T : Set I, T.Finite ∧ Sheaf.IsLocallySurjective (Sigma.desc fun j : T => f j.1)

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology

universe v u

variable {C : Type u} [Category.{v} C]

/-- The topos `Sh(C)` of sheaves of sets on a site is *quasi-compact* if its final object is a
quasi-compact object. -/
@[stacks 0D07 "A quasi-compact topos: its final object is a quasi-compact object.",
  sga "4 IV 8.7"]
def IsQuasiCompactTopos (J : GrothendieckTopology C) : Prop :=
  Sheaf.IsQuasiCompact (⊤_ (Sheaf J (Type max v u)))

end CategoryTheory.GrothendieckTopology
