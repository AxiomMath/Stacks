module

public import StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.Absolute

/-!
# Descending an obstruction from the absolute integral closure

This file collects two general facts used to deduce, from an obstruction over a henselian local
ring, that the absolute integral closure `A⁺` of a domain `A` is not a filtered colimit of
finitely presented flat `A`-algebras.

* Every domain `Γ₀` which is an integral extension of `A` embeds into `A⁺` over `A`. Moreover
  `A⁺` is faithfully flat over `A` as soon as it is flat, being an integral extension: this is
  Mathlib's instance `Module.FaithfullyFlat.of_isIntegral_of_isDomain`.
* Let `B` be a faithfully flat `A`-algebra receiving a finitely presented `A`-algebra `Γ₀`, and
  let `R` be a henselian local `A`-algebra. If `R ⊗_A Γ₀` admits no `R`-algebra map to a nonzero
  finite free `R`-algebra, then `B` is the colimit of no filtered diagram of finitely presented
  flat `A`-algebras. Indeed `Γ₀ → B` would factor through a stage `C`, which is finitely
  presented and faithfully flat over `A`; then `R ⊗_A C` is finitely presented and faithfully
  flat over the henselian local ring `R`, so it maps to a nonzero finite free `R`-algebra
  (**Stacks 04GJ**), and so would `R ⊗_A Γ₀`.

## Main results

* `absoluteIntegralClosure.exists_injective_algHom`: an integral domain extension of `A` embeds
  into `A⁺`.
* `absoluteIntegralClosure.faithfulSMul`: the structure map `A → A⁺` is injective, which is what
  Mathlib's instance `Module.FaithfullyFlat.of_isIntegral_of_isDomain` needs, beyond integrality,
  to make `A⁺` faithfully flat over `A` once it is flat.
* `Stacks.Examples.isEmpty_isColimit_of_isEmpty_hom_tensor_finite_free`: the descent of the
  obstruction from `R ⊗_A Γ₀` to `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v w

namespace absoluteIntegralClosure

variable (A : Type u) [CommRing A] [IsDomain A]

/-- The structure map `A → A⁺` is injective. -/
instance faithfulSMul : FaithfulSMul A (absoluteIntegralClosure A) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_injective A)

/-- Every domain which is an integral extension of `A` embeds into `A⁺` over `A`: its fraction
field is algebraic over that of `A`, hence embeds into the algebraic closure, and the image of an
integral element is integral. -/
theorem exists_injective_algHom (Γ₀ : Type w) [CommRing Γ₀] [IsDomain Γ₀] [Algebra A Γ₀]
    [FaithfulSMul A Γ₀] [Algebra.IsIntegral A Γ₀] :
    ∃ f : Γ₀ →ₐ[A] absoluteIntegralClosure A, Function.Injective f := by
  have : FaithfulSMul A (AlgebraicClosure (FractionRing A)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr <| by
      rw [IsScalarTower.algebraMap_eq A (FractionRing A) (AlgebraicClosure (FractionRing A))]
      exact (algebraMap (FractionRing A) _).injective.comp
        (IsFractionRing.injective A (FractionRing A))
  let g : Γ₀ →ₐ[A] AlgebraicClosure (FractionRing A) := IsAlgClosed.lift
  have hg : Function.Injective g := (RingHom.injective_iff_ker_eq_bot g.toRingHom).mpr <|
    Ideal.eq_bot_of_comap_eq_bot (R := A) <| by
      rw [RingHom.comap_ker, show g.toRingHom.comp (algebraMap A Γ₀) =
          algebraMap A (AlgebraicClosure (FractionRing A)) from RingHom.ext g.commutes]
      exact (RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective A (AlgebraicClosure (FractionRing A)))
  exact ⟨g.codRestrict (absoluteIntegralClosure A) fun x =>
    (Algebra.IsIntegral.isIntegral (R := A) x).map g,
    fun x y hxy => hg (congrArg Subtype.val hxy)⟩

end absoluteIntegralClosure

namespace Stacks.Examples

open FlatAlgebraNotFilteredColimit

/-- Let `B` be a faithfully flat `A`-algebra receiving a finitely presented `A`-algebra `Γ₀`,
and let `R` be a henselian local `A`-algebra such that `R ⊗_A Γ₀` admits no `R`-algebra map to
a nonzero finite free `R`-algebra. Then `B` is the colimit of no filtered diagram of finitely
presented flat `A`-algebras: `Γ₀` would map to a stage `C`, and the finitely presented faithfully
flat `R`-algebra `R ⊗_A C` maps to a nonzero finite free `R`-algebra by **Stacks 04GJ**. -/
theorem isEmpty_isColimit_of_isEmpty_hom_tensor_finite_free
    {A : Type max u v} [CommRing A] {B : CommAlgCat.{max u v} A} [Module.FaithfullyFlat A B]
    {Γ₀ : Type max u v} [CommRing Γ₀] [Algebra A Γ₀] [Algebra.FinitePresentation A Γ₀]
    (g : Γ₀ →ₐ[A] B) (R : Type max u v) [CommRing R] [Algebra A R] [HenselianLocalRing R]
    (hR : ∀ (T : Type max u v) [CommRing T] [Algebra R T], Module.Free R T → Module.Finite R T →
      Nontrivial T → IsEmpty (R ⊗[A] Γ₀ →ₐ[R] T)) :
    ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommAlgCat.{max u v} A),
      (∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j)) →
        ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c) := by
  intro J _ _ F hF c hpt
  subst hpt
  refine ⟨fun hc => ?_⟩
  let : PreservesColimitsOfShape J (forget CommRingCat.{max u v}) :=
    preservesColimitsOfShape_forget_commRingCat.{max u v, v} J
  let S : CommAlgCat.{max u v} A := CommAlgCat.of A Γ₀
  have : Algebra.FinitePresentation A S := inferInstanceAs (Algebra.FinitePresentation A Γ₀)
  obtain ⟨i, ⟨h⟩⟩ := exists_stage_hom_of_finitePresentation F hc S (CommAlgCat.ofHom g)
  let : Algebra.FinitePresentation A (F.obj i) := (hF i).1
  let : Module.Flat A (F.obj i) := (hF i).2
  let : Module.FaithfullyFlat A (F.obj i) :=
    faithfullyFlat_stage_of_faithfullyFlat_cocone F c c.pt rfl i
  obtain ⟨T, hfree, hfin, hne, ⟨k⟩⟩ :=
    exists_finite_free_factor_of_faithfullyFlat_finitePresentation (R := R)
      (S := R ⊗[A] F.obj i)
  exact (hR T hfree hfin hne).false
    (k.hom.comp (Algebra.TensorProduct.map (AlgHom.id R R) h.hom))

end Stacks.Examples

end
