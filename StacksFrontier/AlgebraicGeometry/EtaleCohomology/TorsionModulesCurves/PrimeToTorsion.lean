module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology

/-!
# Sheaves of `Λ`-modules which are torsion prime to an integer

A sheaf of `Λ`-modules `ℱ` on the small étale site of a scheme is *torsion prime to `p`* when
every local section is, on the members of some covering sieve, annihilated by a positive integer
prime to `p`. For `p` the exponential characteristic of a base field `k` this is the condition
"torsion prime to `char(k)`" of Stacks 0GJI part (1); for `p = 1` it is plain torsion,
`Stacks.EtaleCohomology.IsTorsionEtaleModule`.

## Main definitions

* `Stacks.EtaleCohomology.IsTorsionPrimeToEtaleModule` — the condition above.

## Main results

* `Stacks.EtaleCohomology.isTorsionPrimeToEtaleModule_one_iff` — torsion prime to `1` is torsion.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- A sheaf of `Λ`-modules on the small étale site of `X` is **torsion prime to `p`** when every
section over an object of the site is, on the members of some covering sieve, annihilated by a
positive integer prime to `p`. -/
def IsTorsionPrimeToEtaleModule (p : ℕ) (X : Scheme.{u}) (F : EtaleModules.{u, r} Λ X) : Prop :=
  ∀ (V : X.Etale) (x : F.obj.obj (Opposite.op V)), ∃ R : Sieve V, R ∈ X.smallEtaleTopology V ∧
    ∀ (W : X.Etale) (g : W ⟶ V), R g →
      ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • F.obj.map g.op x = 0

/-- Torsion prime to `1` is torsion: every positive integer is prime to `1`. -/
theorem isTorsionPrimeToEtaleModule_one_iff (X : Scheme.{u}) (F : EtaleModules.{u, r} Λ X) :
    IsTorsionPrimeToEtaleModule Λ 1 X F ↔ IsTorsionEtaleModule Λ X F := by
  refine ⟨fun h V x => ?_, fun h V x => ?_⟩
  · obtain ⟨R, hR, hx⟩ := h V x
    exact ⟨R, hR, fun W g hg => (hx W g hg).imp fun n hn => ⟨hn.1, hn.2.2⟩⟩
  · obtain ⟨R, hR, hx⟩ := h V x
    exact ⟨R, hR, fun W g hg => (hx W g hg).imp fun n hn => ⟨hn.1, Nat.coprime_one_right n,
      hn.2⟩⟩

/-- A sheaf which is torsion prime to some `p` is torsion. -/
theorem IsTorsionPrimeToEtaleModule.isTorsionEtaleModule {p : ℕ} {X : Scheme.{u}}
    {F : EtaleModules.{u, r} Λ X} (h : IsTorsionPrimeToEtaleModule Λ p X F) :
    IsTorsionEtaleModule Λ X F := fun V x =>
  (h V x).imp fun _ hR => ⟨hR.1, fun W g hg => (hR.2 W g hg).imp fun _ hn => ⟨hn.1, hn.2.2⟩⟩

end Stacks.EtaleCohomology

end
