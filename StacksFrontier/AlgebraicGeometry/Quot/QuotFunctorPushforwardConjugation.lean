module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforwardSupplement

/-!
# The direct image of quotients along a fully faithful pushforward

Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine quasi-finite morphism of algebraic
spaces which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module.  Over a test scheme `T` of `B` the morphism of Quot functors of Stacks 0DP1 sends a
quotient of `F_T`, recorded by its kernel `K`, to the quotient `G_T ⟶ π_{T,*}(F_T/K)` of
`G_T = (π_*F)_T`, recorded by its kernel; this is `CategoryTheory.Functor.conjSubobject` for the
comparison `G_T ≅ π_{T,*}F_T`.

Collected here is what that construction does when the direct image `π_{T,*}` is *fully
faithful*: it is then injective on quotients, and a quotient of `G_T` is in its image as soon as
the quotient module is a direct image.  Both facts are proved for the conjugation construction in
the generality in which it is defined, and both are used with a hypothesis on `π` which makes
`π_{T,*}` fully faithful — a closed immersion by Stacks 04CJ, an open immersion by Stacks 03LV.

## Main results

* `CategoryTheory.Functor.conjSubobject_injective`: conjugating quotients by a comparison
  `e : P₂ ≅ P₁ ⋙ L` whose further functor `L` is fully faithful is injective.
* `CategoryTheory.Functor.exists_conjSubobject_eq`: a quotient of `P₂ M` whose quotient object
  lies in the essential image of `L` is the conjugate of a quotient of `P₁ M`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotient_injective_of_fullyFaithful`
  states that the direct image of quotients of `F_T` is injective when `π_{T,*}` is fully faithful.

## Implementation notes

Neither result needs `L` to be exact.  A quotient is recorded by its kernel, and a kernel
subobject is unchanged when the projection it is the kernel of is composed with a monomorphism
(`CategoryTheory.Limits.kernelSubobject_eq_of_comp_mono`); that is what carries both proofs, the
first comparing the two projections onto the conjugate quotients by an isomorphism of their
common target and the second comparing a projection with the image under `L` of a surjection.
Full faithfulness enters twice: it descends an isomorphism of the images of the two quotients to
an isomorphism of the quotients, and it produces the surjection out of `P₁ M` whose image is a
given projection out of `P₂ M` — faithfulness alone makes that preimage an epimorphism, since a
faithful functor reflects epimorphisms.

## References

* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-! ### Conjugating quotients by a fully faithful comparison -/

section Conjugation

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
  [Abelian D₁] [Abelian D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- Equal subobjects have the same projection onto the quotient, read through the identification
of the two quotients. -/
theorem cokernel_π_comp_eqToHom {A : D₂} {K K' : Subobject A} (hK : K = K')
    (hcok : cokernel K.arrow = cokernel K'.arrow) :
    cokernel.π K.arrow ≫ eqToHom hcok = cokernel.π K'.arrow := by
  subst hK
  simp

/-- **Conjugating quotients by a comparison whose further functor is fully faithful is
injective.**

Two quotients of `P₁ M` with the same conjugate have isomorphic images under `L`, compatibly with
the projections from `P₂ M`; the isomorphism descends to an isomorphism of the two quotients
compatible with the projections from `P₁ M`, and a quotient is determined by its kernel. -/
theorem Functor.conjSubobject_injective (e : P₂ ≅ P₁ ⋙ L) [L.PreservesEpimorphisms]
    (hff : L.FullyFaithful) (M : C) :
    Function.Injective (Functor.conjSubobject e (M := M)) := by
  intro K₁ K₂ hK
  have hcok : cokernel (Functor.conjSubobject e K₁).arrow =
      cokernel (Functor.conjSubobject e K₂).arrow := by rw [hK]
  set θ : L.obj (cokernel K₁.arrow) ≅ L.obj (cokernel K₂.arrow) :=
    (Functor.conjSubobjectCokernelIso e K₁).symm ≪≫ eqToIso hcok ≪≫
      Functor.conjSubobjectCokernelIso e K₂ with hθ
  have key : L.map (cokernel.π K₁.arrow) ≫ θ.hom = L.map (cokernel.π K₂.arrow) := by
    refine (cancel_epi (e.hom.app M)).1 ?_
    have e₁ : e.hom.app M ≫ L.map (cokernel.π K₁.arrow) =
        Functor.conjQuotientProjection e K₁ := rfl
    have e₂ : e.hom.app M ≫ L.map (cokernel.π K₂.arrow) =
        Functor.conjQuotientProjection e K₂ := rfl
    rw [← Category.assoc, e₁, e₂,
      ← Functor.cokernel_π_comp_conjSubobjectCokernelIso_hom e K₁,
      ← Functor.cokernel_π_comp_conjSubobjectCokernelIso_hom e K₂, hθ]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, cokernel_π_comp_eqToHom hK hcok]
  have hpre : cokernel.π K₁.arrow ≫ (hff.preimageIso θ).hom = cokernel.π K₂.arrow :=
    hff.map_injective (by rwa [L.map_comp, Functor.FullyFaithful.preimageIso_hom, hff.map_preimage])
  calc K₁ = kernelSubobject (cokernel.π K₁.arrow) := (kernelSubobject_cokernel_π K₁).symm
    _ = kernelSubobject (cokernel.π K₂.arrow) :=
        (kernelSubobject_eq_of_comp_mono _ _ _ hpre).symm
    _ = K₂ := kernelSubobject_cokernel_π K₂

/-- **A quotient of `P₂ M` whose quotient object is an image under `L` is a conjugate.**

The projection of `P₂ M` onto the quotient, read through the comparison `e` and through the
identification of the quotient object with `L Q`, is the image under `L` of a surjection
`P₁ M ⟶ Q`, because `L` is fully faithful and a faithful functor reflects epimorphisms; the
kernel of that surjection is the quotient of `P₁ M` sought, and the two quotients of `P₂ M` have
the same kernel because their projections differ by an isomorphism of the target. -/
theorem Functor.exists_conjSubobject_eq (e : P₂ ≅ P₁ ⋙ L) (hff : L.FullyFaithful) {M : C}
    (K' : Subobject (P₂.obj M)) (hK' : L.essImage (cokernel K'.arrow)) :
    ∃ K : Subobject (P₁.obj M), Functor.conjSubobject e K = K' ∧
      Nonempty (L.obj (cokernel K.arrow) ≅ cokernel K'.arrow) := by
  have _ := hff.faithful
  obtain ⟨Q, ⟨ψ⟩⟩ := hK'
  set r : P₁.obj M ⟶ Q := hff.preimage (e.inv.app M ≫ cokernel.π K'.arrow ≫ ψ.inv)
  have hmap : L.map r = e.inv.app M ≫ cokernel.π K'.arrow ≫ ψ.inv := hff.map_preimage _
  have hepiL : Epi (L.map r) := by
    rw [hmap]
    infer_instance
  have _ : Epi r := L.epi_of_epi_map hepiL
  have hc : cokernel.π (kernelSubobject r).arrow ≫
      (Abelian.cokernelKernelSubobjectIso r).hom = r := by
    rw [← Abelian.cokernelKernelSubobjectIso_inv_comp r, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hkey : Functor.conjQuotientProjection e (kernelSubobject r) ≫
      (L.map (Abelian.cokernelKernelSubobjectIso r).hom ≫ ψ.hom) = cokernel.π K'.arrow := by
    rw [Functor.conjQuotientProjection, Category.assoc,
      ← Category.assoc (L.map (cokernel.π (kernelSubobject r).arrow)), ← L.map_comp, hc, hmap]
    simp
  refine ⟨kernelSubobject r, ?_,
    ⟨L.mapIso (Abelian.cokernelKernelSubobjectIso r) ≪≫ ψ⟩⟩
  show kernelSubobject (Functor.conjQuotientProjection e (kernelSubobject r)) = K'
  exact (kernelSubobject_eq_of_comp_mono _ _ _ hkey).symm.trans (kernelSubobject_cokernel_π K')

end Conjugation

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-! ### The direct image of quotients along a fully faithful pushforward -/

/-- **The direct image of quotients is injective when the direct image of modules is fully
faithful.**  Two quotients of `F_T` with the same direct image agree: the direct image of
quotients is `CategoryTheory.Functor.conjSubobject` for the comparison `G_T ≅ π_{T,*}F_T`. -/
theorem pushforwardQuotient_injective_of_fullyFaithful
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS) (c : PushforwardComparison D)
    (T : SchemesOver D.base)
    (hff : (modulePushforward B S hS (D.baseChangeOfMap T)).FullyFaithful) :
    Function.Injective (D.pushforwardQuotient h c T) := by
  have := c.preservesEpimorphisms T
  exact Functor.conjSubobject_injective (c.iso T) hff D.F

/-- **The direct image of quotients is injective when the direct image of modules is fully
faithful.**  Two quotients of `F_T` with the same direct image agree: the direct image of
quotients is `CategoryTheory.Functor.conjSubobject` for the comparison `G_T ≅ π_{T,*}F_T`. -/
theorem pushforwardQuotient_injective_of_fullyFaithful' (c : PushforwardComparison D)
    (T : SchemesOver D.base)
    (hff : (modulePushforward B S hS (D.baseChangeOfMap T)).FullyFaithful) :
    Function.Injective (D.pushforwardQuotient' c T) := by
  have := c.preservesEpimorphisms T
  exact Functor.conjSubobject_injective (c.iso T) hff D.F

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
