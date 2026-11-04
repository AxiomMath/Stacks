module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Abelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Stalk
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.BoundedTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `ℚ_ℓ`-sheaves on a Noetherian scheme

The abelian category of `ℚ_ℓ`-sheaves is the quotient of the abelian category of `ℤ_ℓ`-sheaves
(Tag 03UO) by the Serre subcategory of torsion sheaves. Everything needed for that quotient is
general: the objects annihilated by a power of `ℓ` in any abelian category form a Serre class, and
Mathlib localizes an abelian category at a Serre class. So the work here is to identify the
project's `LAdicSheaf.IsTorsion` with that general property, and then to read off the three things
Tag 03UR asserts about the quotient.

The hom-group formula of the tag,
`Hom_{ℚ_ℓ}(F, G) = Hom_{ℤ_ℓ}(F, G) ⊗_{ℤ_ℓ} ℚ_ℓ`, is a theorem about the quotient and not part of
its construction; the general instance `Stacks.CategoryTheory.isLocalizedModule_mapIntLinearMap`,
at the quotient functor `rationalization`, proves it in the form that does not presuppose a
`ℤ_ℓ`-module structure on the hom-group: the quotient's hom-group *is* the hom-group of `ℤ_ℓ`-
sheaves with the powers of `ℓ` inverted. Since every integer prime to `ℓ` is already invertible in
`ℤ_ℓ`, inverting `ℓ` is exactly `- ⊗_{ℤ_ℓ} ℚ_ℓ`.

## Main definitions

* `Stacks.EtaleCohomology.torsionSheaves`: the torsion `ℤ_ℓ`-sheaves, as a Serre subcategory.
* `Stacks.EtaleCohomology.RationalSheaf`: the category of `ℚ_ℓ`-sheaves on `X`.
* `Stacks.EtaleCohomology.rationalization`: the quotient functor `F ↦ F ⊗ ℚ_ℓ`.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalk`: the stalk of `F' ⊗ ℚ_ℓ` at a geometric
  point.

## Main results

* `Stacks.EtaleCohomology.RationalSheaf.abelian`: `ℚ_ℓ`-sheaves form an abelian category.

## Implementation notes

The quotient is realized by Mathlib's localization of the morphisms which are isomorphisms modulo
the Serre class, so the objects of `RationalSheaf` are literally the `ℤ_ℓ`-sheaves on `X`, as the
tag says. In particular every `ℚ_ℓ`-sheaf is of the form `F ⊗ ℚ_ℓ`, which is what makes the stalk
of a `ℚ_ℓ`-sheaf well defined by the recipe `F ⊗ ℚ_ℓ ↦ F_x̄ ⊗ ℚ_ℓ`.

Nothing here provides an adjunction for the quotient functor. The construction is a calculus of
fractions, which produces no functor back to `ℤ_ℓ`-sheaves; and for a localizing subcategory of a
Grothendieck abelian category the adjunction which does exist runs the other way, the section
functor being right adjoint to the quotient functor.

## References

* [Stacks Project, Tag 03UR](https://stacks.math.columbia.edu/tag/03UR)
* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [Fact ℓ.Prime] [IsNoetherian X.1]

/-- A torsion ℓ-adic sheaf, written as a single power of `ℓ` annihilating the identity of the
whole system rather than each of its levels separately. -/
public theorem LAdicSheaf.isTorsion_iff_nsmul_id_eq_zero (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.IsTorsion B X ℓ F ↔ ∃ k : ℕ, (ℓ ^ k) • 𝟙 F = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, LAdicSheaf.Hom.ext _ _ _ (fun n => hk n)⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, fun n => congrArg (fun g : F ⟶ F => g.app n) hk⟩

/-- **Stacks 03UR.** The torsion `ℤ_ℓ`-sheaves, as a property of objects of the abelian category
of `ℤ_ℓ`-sheaves. -/
@[stacks 03UR "the subcategory of torsion sheaves"]
public abbrev torsionSheaves : ObjectProperty (LAdicSheaf.{u, u + 1} B X ℓ) :=
  Stacks.CategoryTheory.isTorsionObject ℓ

/-- The subcategory `torsionSheaves` is exactly the torsion `ℤ_ℓ`-sheaves of Tag 03UR. -/
public theorem LAdicSheaf.isTorsion_iff_mem_torsionSheaves (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.IsTorsion B X ℓ F ↔ torsionSheaves B X ℓ F :=
  (LAdicSheaf.isTorsion_iff_nsmul_id_eq_zero B X ℓ F).trans
    (Stacks.CategoryTheory.isTorsionObject_iff ℓ F).symm

/-- **Stacks 03UR.** The abelian category of `ℚ_ℓ`-sheaves on `X`: the quotient of the abelian
category of `ℤ_ℓ`-sheaves by the Serre subcategory of torsion sheaves. Its objects are the
`ℤ_ℓ`-sheaves on `X`. -/
@[stacks 03UR "the category of Q_ℓ-sheaves as the quotient by the torsion sheaves",
  sga "4½ Rapport 2.9"]
public abbrev RationalSheaf := (torsionSheaves B X ℓ).isoModSerre.Localization

/-- **Stacks 03UR.** The quotient functor `F ↦ F ⊗ ℚ_ℓ` from `ℤ_ℓ`-sheaves to `ℚ_ℓ`-sheaves. -/
@[stacks 03UR "the quotient functor F ↦ F ⊗ Q_ℓ"]
public abbrev rationalization : LAdicSheaf.{u, u + 1} B X ℓ ⥤ RationalSheaf B X ℓ :=
  (torsionSheaves B X ℓ).isoModSerre.Q

/-- **Stacks 03UR.** The category of `ℚ_ℓ`-sheaves on `X` is abelian. -/
@[stacks 03UR "Q_ℓ-sheaves form an abelian category"]
public instance RationalSheaf.abelian : Abelian (RationalSheaf B X ℓ) :=
  ObjectProperty.SerreClassLocalization.abelian (rationalization B X ℓ) (torsionSheaves B X ℓ)

/-- **Stacks 03UR.** The stalk at a geometric point `x` of the `ℚ_ℓ`-sheaf `F ⊗ ℚ_ℓ`, for `F` a
`ℤ_ℓ`-sheaf: the `ℤ_ℓ`-module stalk of `F` (Tag 03UQ) tensored up to `ℚ_ℓ`. Every `ℚ_ℓ`-sheaf is
of this shape, the objects of the quotient category being the `ℤ_ℓ`-sheaves themselves. -/
@[stacks 03UR "the stalk of F ⊗ Q_l is the stalk of F tensored with Q_l"]
public abbrev LAdicSheaf.rationalStalk (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (x : GeometricPoint X.1) : Type (u + 1) :=
  TensorProduct (PadicInt ℓ) (LAdicSheaf.stalk B X ℓ F x) (Padic ℓ)

end Stacks.EtaleCohomology

end
