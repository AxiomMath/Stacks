module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality

/-!
# Divided power differential forms transported along an isomorphism of divided power rings

`Crystalline.differentialsEquivOfAlgEquiv` of `ModuleDifferentials/Functoriality.lean` carries
the module of divided power differentials along an isomorphism of divided power rings.  This
file does the same in every degree, for
`Crystalline.dividedPowerDifferentialForms`.

The map in one direction is `Crystalline.mapDifferentialFormsOfDPMorphism`, which is semilinear
and not linear — the two exterior powers are taken over two different rings — so the result is
an *additive* equivalence pinned by the statement that it is that map.  The inverse is the same
construction for the inverse isomorphism, whose divided power compatibility is recovered exactly
as in degree one, and the two round trips are
`Crystalline.mapDifferentialFormsOfDPMorphism_comp` against
`Crystalline.mapDifferentialFormsOfDPMorphism_id`.

## Main definitions

* `Crystalline.differentialFormsEquivOfAlgEquiv` — the equivalence
  `Ωⁱ_{B/A,δ} ≃+ Ωⁱ_{C/A,ε}` induced by an isomorphism of divided power rings, bundled with the
  proof that it is `Crystalline.mapDifferentialFormsOfDPMorphism`.

## What is and is not proved

**No tag attribute is placed, and [Stacks, Tag 07LF] is not proved here.**  This is one of the
crossings the isomorphism `ε` of that tag has to make — the section ring of a level object of
the system of [Stacks, Tag 07JN] is identified with a finite level of `D(n)` by a ring
isomorphism, and the forms have to be carried along it — and nothing else here is about that
tag.  No hypothesis is carried beyond the isomorphism, its divided power compatibility and the
image of the divided power ideal.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

universe u v

namespace Crystalline

section FormsAlgEquiv

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (delta : DividedPowers J)
variable {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C}

/-- **An isomorphism of divided power rings carries the divided power differential forms of one
to those of the other, in every degree.**

The equivalence is additive and not linear: the exterior powers are taken over the two different
rings `B` and `C`, so the comparison is semilinear over the isomorphism, which is what
`Crystalline.mapDifferentialFormsOfDPMorphism` is.  The bundled equation says the equivalence
*is* that comparison, so every computation lemma for it applies.

The divided power compatibility of the inverse isomorphism is recovered from that of the
isomorphism exactly as in degree one, by
`DividedPowers.IsDPMorphism.of_comp` against the image of the divided power ideal. -/
public noncomputable def differentialFormsEquivOfAlgEquiv
    (epsilon : DividedPowers K) (f : B ≃ₐ[A] C)
    (hf : delta.IsDPMorphism epsilon f.toAlgHom.toRingHom)
    (hJ : J.map f.toAlgHom.toRingHom = K) (i : ℕ) :
    { E : dividedPowerDifferentialForms (A := A) delta i ≃+
        dividedPowerDifferentialForms (A := A) epsilon i //
      ∀ x, E x = mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon
        f.toAlgHom hf i x } := by
  have hg : epsilon.IsDPMorphism delta f.symm.toAlgHom.toRingHom := by
    refine DividedPowers.IsDPMorphism.of_comp delta epsilon delta
      f.toAlgHom.toRingHom f.symm.toAlgHom.toRingHom hJ.symm hf ?_
    have heq : f.symm.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom = RingHom.id B := by
      ext x
      exact f.symm_apply_apply x
    exact Eq.subst (motive := fun φ ↦ DividedPowers.IsDPMorphism delta delta φ) heq.symm
      (DividedPowers.DPMorphism.id delta).isDPMorphism
  have hGF : (mapDifferentialsOfDPMorphism (A := A) (J := K) (delta := epsilon) delta
        f.symm.toAlgHom hg).comp
      (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon
        f.toAlgHom hf) = AddMonoidHom.id _ := by
    rw [mapDifferentialsOfDPMorphism_comp]
    have he : f.symm.toAlgHom.comp f.toAlgHom = AlgHom.id A B := by ext x; simp
    simpa only [he] using mapDifferentialsOfDPMorphism_id (A := A) (J := _) (delta := delta)
  have hFG : (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon
        f.toAlgHom hf).comp
      (mapDifferentialsOfDPMorphism (A := A) (J := K) (delta := epsilon) delta
        f.symm.toAlgHom hg) = AddMonoidHom.id _ := by
    rw [mapDifferentialsOfDPMorphism_comp]
    have he : f.toAlgHom.comp f.symm.toAlgHom = AlgHom.id A C := by ext x; simp
    simpa only [he] using mapDifferentialsOfDPMorphism_id (A := A) (J := _) (delta := epsilon)
  refine ⟨{ toFun := mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon
              f.toAlgHom hf i
            invFun := mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := epsilon) delta
              f.symm.toAlgHom hg i
            left_inv := fun x ↦ ?_
            right_inv := fun x ↦ ?_
            map_add' := map_add _ }, fun _ ↦ rfl⟩
  · exact (ExteriorAlgebra.powMapₛₗ_eq_comp i
      (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := J) (delta := delta) epsilon f.toAlgHom hf)
      (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := K) (delta := epsilon) delta
        f.symm.toAlgHom hg)
      (LinearMap.id (R := B) (M := dividedPowerDifferentials (A := A) delta))
      (fun r ↦ (f.symm_apply_apply r).symm)
      (fun m ↦ (DFunLike.congr_fun hGF m).symm) x).symm.trans
      (ExteriorAlgebra.powMapₛₗ_eq_self i
        (LinearMap.id (R := B) (M := dividedPowerDifferentials (A := A) delta))
        (fun _ ↦ rfl) (fun _ ↦ rfl) x)
  · exact (ExteriorAlgebra.powMapₛₗ_eq_comp i
      (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := K) (delta := epsilon) delta
        f.symm.toAlgHom hg)
      (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := J) (delta := delta) epsilon f.toAlgHom hf)
      (LinearMap.id (R := C) (M := dividedPowerDifferentials (A := A) epsilon))
      (fun r ↦ (f.apply_symm_apply r).symm)
      (fun m ↦ (DFunLike.congr_fun hFG m).symm) x).symm.trans
      (ExteriorAlgebra.powMapₛₗ_eq_self i
        (LinearMap.id (R := C) (M := dividedPowerDifferentials (A := A) epsilon))
        (fun _ ↦ rfl) (fun _ ↦ rfl) x)

end FormsAlgEquiv

end Crystalline

end
