module

public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# Moving closed-fibre data across an isomorphism of the closed-fibre ring

`AlgebraicGeometry.FlatLocalKoszulDeformationSituation` asks for its regular sequence and its
Koszul identification in the ring `A ⧸ 𝔪_R A`, the closed fibre of the algebra map written as a
quotient of `A`. The geometry of [Stacks, Tag 0G0R] delivers them in the local ring of the fibre
scheme instead — a ring isomorphic to that quotient, but not equal to it. This file moves the two
pieces of data across such an isomorphism.

## Main results

* `RingTheory.Sequence.isRegular_of_ringEquiv`: a sequence whose image under a ring isomorphism
  is regular is regular.
* `StacksDraft.DerivedRingIso.restrictScalarsMapDerivedCategoryIso`: derived extension of scalars
  along the inverse of a ring isomorphism is restriction of scalars along the isomorphism.
* `StacksDraft.DerivedRingIso.quotientRestrictScalarsIso`: the restriction along `E` of
  `B ⧸ E(J)` is `C ⧸ J`.
* `StacksDraft.DerivedRingIso.nonempty_iso_single_of_ringEquiv`: if derived extension of scalars
  along `E ∘ mk` carries `K` to a module in degree zero, then so does derived extension of
  scalars along `mk`, the module being the same one with scalars restricted along `E`.

## Implementation notes

*The regularity transport.* `E` is an additive isomorphism `C ≃+ B` carrying `c * x` to
`E c * E x`, which is exactly the compatibility `AddEquiv.isRegular_congr` asks of the sequences
`rs` over `C` and `rs.map E` over `B`.

*The derived transport without inverting a functor.* Derived extension of scalars along a ring
isomorphism is an equivalence, but rather than inverting it the statement composes with derived
extension of scalars along the inverse isomorphism: `E⁻¹ ∘ (E ∘ mk) = mk`, so
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` already carries the
identification along `E ∘ mk` to one along `mk`. Derived extension of scalars along `E⁻¹` is then
identified with restriction of scalars along `E` by
`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso` at the identity homomorphism,
whose derived extension of scalars is the identity functor
(`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId`). Restriction of scalars
is exact, so it commutes with placing a module in degree zero
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`).

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.Sequence

/-- **A sequence whose image under a ring isomorphism is regular is regular.** -/
theorem isRegular_of_ringEquiv {C B : Type u} [CommRing C] [CommRing B] (E : C ≃+* B)
    (rs : List C) (h : IsRegular B (rs.map E)) : IsRegular C rs :=
  (E.toAddEquiv.isRegular_congr
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ => map_mul E r))).mpr h

end RingTheory.Sequence

namespace StacksDraft.DerivedRingIso

attribute [local instance] HasDerivedCategory.standard

variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]

/-- **Derived extension of scalars along the inverse of a ring isomorphism is restriction of
scalars along the isomorphism.** -/
def restrictScalarsMapDerivedCategoryIso (E : C ≃+* B) :
    (ModuleCat.restrictScalars.{u, u, u} (E : C →+* B)).mapDerivedCategory ≅
      (totalDerivedExtensionScalars.{u, u, u} (E.symm : B →+* C)).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (totalDerivedExtensionScalarsId C) ≪≫
    derivedExtensionScalarsRestrictIso (E.symm : B →+* C) (E : C →+* B)
      (fun x => E.apply_symm_apply x) (fun y => E.symm_apply_apply y) (RingHom.id C) ≪≫
    eqToIso (congrArg (fun f => (totalDerivedExtensionScalars.{u, u, u} f).functor)
      (RingHom.id_comp (E.symm : B →+* C)))

/-- **Restricting a cyclic module along a ring isomorphism.** The `C`-module obtained from
`B ⧸ E(J)` by restricting scalars along `E` is `C ⧸ J`. -/
def quotientRestrictScalarsIso (E : C ≃+* B) (J : Ideal C) :
    ModuleCat.of C (C ⧸ J) ≅
      (ModuleCat.restrictScalars.{u, u, u} (E : C →+* B)).obj
        (ModuleCat.of B (B ⧸ J.map (E : C →+* B))) :=
  letI inst : Module C (B ⧸ J.map (E : C →+* B)) :=
    Module.compHom (B ⧸ J.map (E : C →+* B)) (E : C →+* B)
  @LinearEquiv.toModuleIso C _ (C ⧸ J) (B ⧸ J.map (E : C →+* B)) _ _ _ inst
    { Ideal.quotientEquiv J (J.map (E : C →+* B)) E rfl with
      map_smul' := fun c x => by
        induction x using Quotient.inductionOn with
        | h a =>
          change Ideal.quotientEquiv J (J.map (E : C →+* B)) E rfl (Ideal.Quotient.mk J (c * a)) =
            Ideal.Quotient.mk (J.map (E : C →+* B)) ((E : C →+* B) c) *
              Ideal.quotientEquiv J (J.map (E : C →+* B)) E rfl (Ideal.Quotient.mk J a)
          simp [Ideal.quotientEquiv_apply, Ideal.quotientMap_mk, ← map_mul] }

/-- **Moving a degree-zero identification across the closed-fibre isomorphism.** If derived
extension of scalars along `E ∘ mk` carries `K` to the module `M` placed in degree zero, then
derived extension of scalars along `mk` carries `K` to `M` with scalars restricted along `E`,
placed in degree zero. -/
theorem nonempty_iso_single_of_ringEquiv
    (E : C ≃+* B) (mk : A →+* C) (K : DerivedCategory (ModuleCat.{u} A)) (M : ModuleCat.{u} B)
    (h : Nonempty ((totalDerivedExtensionScalars.{u, u, u} ((E : C →+* B).comp mk)).functor.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, u} mk).functor.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj
        ((ModuleCat.restrictScalars.{u, u, u} (E : C →+* B)).obj M)) := by
  obtain ⟨e⟩ := h
  have hθψ : (E.symm : B →+* C).comp ((E : C →+* B).comp mk) = mk := by
    ext x
    exact E.symm_apply_apply (mk x)
  exact ⟨eqToIso (congrArg (fun f => (totalDerivedExtensionScalars.{u, u, u} f).functor.obj K)
      hθψ.symm) ≪≫
    ((totalDerivedExtensionScalarsComp ((E : C →+* B).comp mk) (E.symm : B →+* C)).app K).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u} (E.symm : B →+* C)).functor.mapIso e ≪≫
    ((restrictScalarsMapDerivedCategoryIso E).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).symm ≪≫
    ((ModuleCat.restrictScalars.{u, u, u} (E : C →+* B)).mapDerivedCategorySingleFunctor 0).app M⟩

end StacksDraft.DerivedRingIso

end
