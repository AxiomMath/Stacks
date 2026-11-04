module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ColimitClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.AssertionsExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleBoundedTorsion

/-!
# Reduction of the assertions of Stacks Tag 03SC to sheaves killed by a prime

A torsion abelian sheaf `F` on the small étale site of a Noetherian scheme is the filtered union of
its subsheaves `F[n!]`, each killed by `n!`. Since the eight assertions of Tag 03SC pass to
filtered colimits (`Stacks.EtaleCohomology.TorsionCurveAssertions.of_isColimit`), and from the
outer terms of a short exact sequence to the middle one (Tag 0A5C), they hold for every torsion
sheaf as soon as they hold for every sheaf killed by a prime number.

## Main results

* `Stacks.Torsion.LocallyKilledBy.of_mono`: a subsheaf inherits a torsion condition.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_torsion`: the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A subsheaf inherits the condition of being locally killed by integers with a given
property. -/
theorem LocallyKilledBy.of_mono {P : ℕ → Prop} {F G : Sheaf J AddCommGrpCat.{w}} (i : G ⟶ F)
    [Mono i] (hF : LocallyKilledBy J P F) : LocallyKilledBy J P G := by
  have hinj : ∀ U, Function.Injective (i.hom.app U) := fun U => by
    have : Mono ((sheafToPresheaf J AddCommGrpCat.{w}).map i) := inferInstance
    have : Mono (((sheafToPresheaf J AddCommGrpCat.{w}).map i).app U) := inferInstance
    exact (AddCommGrpCat.mono_iff_injective _).mp this
  intro U x
  obtain ⟨R, hR, h⟩ := hF U (i.hom.app _ x)
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨n, hn, hx⟩ := h V f hf
  refine ⟨n, hn, hinj _ ?_⟩
  rw [map_nsmul, map_zero, NatTrans.naturality_apply]
  exact hx

/-- A subsheaf of an `l`-power torsion abelian sheaf is `l`-power torsion. -/
theorem isPrimePowerTorsion_of_mono {F G : Sheaf J AddCommGrpCat.{w}} (i : G ⟶ F) [Mono i]
    (l : ℕ) (hF : IsPrimePowerTorsion J l F) : IsPrimePowerTorsion J l G :=
  (isPrimePowerTorsion_iff_locallyKilledBy J l G).mpr
    (LocallyKilledBy.of_mono J i ((isPrimePowerTorsion_iff_locallyKilledBy J l F).mp hF))

/-- A subsheaf of an abelian sheaf that is torsion prime to `p` is torsion prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_of_mono {F G : Sheaf J AddCommGrpCat.{w}} (i : G ⟶ F)
    [Mono i] (p : ℕ) (hF : IsPrimeToCharacteristicTorsion J p F) :
    IsPrimeToCharacteristicTorsion J p G :=
  (isPrimeToCharacteristicTorsion_iff_locallyKilledBy J p G).mpr
    (LocallyKilledBy.of_mono J i ((isPrimeToCharacteristicTorsion_iff_locallyKilledBy J p F).mp hF))

end Stacks.Torsion

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsNoetherian X] [QuasiCompact f] [QuasiSeparated f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Reduction of Stacks Tag 03SC to sheaves killed by a prime.** On a Noetherian scheme `X` with
a quasi-compact quasi-separated morphism to `Spec k`, if the eight assertions hold for every
abelian sheaf killed by a prime number, they hold for every torsion abelian sheaf. -/
theorem of_torsion
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      ℓ • 𝟙 G = 0 → TorsionCurveAssertions f G)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F := by
  have hkilled : ∀ (m : ℕ), m ≠ 0 → ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      m • 𝟙 G = 0 → TorsionCurveAssertions f G := fun m hm G hG =>
    of_nsmul_id_eq_zero f (fun _ => True) (fun _ _ _ => ⟨trivial, trivial⟩)
      (fun ℓ hℓ G _ hG => h ℓ hℓ G hG) m hm G trivial hG
  let D := Stacks.Torsion.torsionFiltration X.smallEtaleTopology F
  have hd := Stacks.Torsion.isIso_torsionFiltrationDesc X.smallEtaleTopology F hF
  have hcol : IsColimit (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F)) :=
    have : IsIso ((colimit.isColimit D).desc
        (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F))) := hd
    IsColimit.ofPointIso (colimit.isColimit D)
  have hmono : ∀ n, Mono ((Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F).app n) :=
    fun n => (inferInstance : Mono (kernel.ι ((Nat.factorial n.down) • 𝟙 F)))
  refine of_isColimit f hcol (fun n => hkilled _ (Nat.factorial_ne_zero _) _
      (nsmul_id_kernel_eq_zero F _))
    (fun p hp n => Stacks.Torsion.isPrimePowerTorsion_of_mono _
      ((Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F).app n) p hp)
    (fun hp n => Stacks.Torsion.isPrimeToCharacteristicTorsion_of_mono _
      ((Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F).app n) _ hp) ?_
  intro hc
  obtain ⟨m, hm, hmF⟩ := exists_nsmul_id_eq_zero_of_isConstructibleEtaleSheaf hc hF
  exact hkilled m hm.ne' F hmF

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
