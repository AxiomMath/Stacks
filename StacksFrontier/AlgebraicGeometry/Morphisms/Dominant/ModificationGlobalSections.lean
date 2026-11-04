module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions on a modification of the spectrum of a normal domain

A modification `f : X ⟶ Spec A` of the spectrum of a normal domain satisfies `f_*𝒪_X = 𝒪_{Spec A}`,
so the canonical map `A ⟶ Γ(X, 𝒪_X)` is an isomorphism. The fibre of a birational morphism over
the generic point of the target is the spectrum of the function field, which is the input that
the Stein-factorization criterion for `f_*𝒪_X = 𝒪_S` requires.

## Main results

* `AlgebraicGeometry.isIso_fiberToSpecResidueField_genericPoint_of_isBirational`: the fibre of a
  birational morphism from an irreducible scheme over the generic point of an integral target is
  the spectrum of the residue field there.
* `AlgebraicGeometry.IsModification.isIso_c`: the structure sheaf of the spectrum of a normal
  domain is the direct image of the structure sheaf along a modification.
* `AlgebraicGeometry.IsModification.isIso_appTop`: consequently `A ⟶ Γ(X, 𝒪_X)` is an
  isomorphism.

## Implementation notes

The fibre over a point is the pullback along the morphism from the spectrum of the residue field
there, and that morphism factors through the spectrum of the local ring by the residue map, which
at a generic point of an integral scheme is an isomorphism. Base change of a birational morphism
along the spectrum of the local ring at a generic point is an isomorphism, and replacing the right
leg of a pullback square by its composite with an isomorphism preserves this.

## References

* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 0BAB](https://stacks.math.columbia.edu/tag/0BAB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

private theorem finite_irreducibleComponents_univ_of_irreducibleSpace (X : Scheme.{u})
    [IrreducibleSpace X] : Finite (irreducibleComponents X) := by
  have h : irreducibleComponents (X : Type u) = {(Set.univ : Set X)} :=
    irreducibleComponents_eq_singleton
  rw [h]
  infer_instance

/-- Precomposing the right leg of a pullback square with an isomorphism does not change whether
the projection to that leg is an isomorphism. -/
private theorem isIso_pullback_snd_of_eq_comp {X Y Z W : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (i : W ⟶ Y) [IsIso i] (k : W ⟶ Z) (hk : k = i ≫ g)
    (h : IsIso (pullback.snd f g)) : IsIso (pullback.snd f k) := by
  subst hk
  let e : pullback f (i ≫ g) ⟶ pullback f g :=
    pullback.lift (pullback.fst f (i ≫ g)) (pullback.snd f (i ≫ g) ≫ i)
      (by rw [pullback.condition, Category.assoc])
  let e' : pullback f g ⟶ pullback f (i ≫ g) :=
    pullback.lift (pullback.fst f g) (pullback.snd f g ≫ inv i)
      (by rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.condition])
  have h1 : e ≫ e' = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp only [e, e', Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, IsIso.hom_inv_id, Category.comp_id]
  have h2 : e' ≫ e = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp only [e, e', Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, IsIso.inv_hom_id, Category.comp_id]
  have he : IsIso e := ⟨e', h1, h2⟩
  have hsnd : pullback.snd f (i ≫ g) = e ≫ pullback.snd f g ≫ inv i := by
    simp only [e, pullback.lift_snd_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hsnd]
  infer_instance

/-- The fibre of a birational morphism from an irreducible scheme over the generic point of an
integral target is the spectrum of the residue field at that point. -/
@[ega "IV 6.15.4" "special case"]
theorem isIso_fiberToSpecResidueField_genericPoint_of_isBirational {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IrreducibleSpace X] [IsIntegral Y] (hf : IsBirational f) :
    IsIso (f.fiberToSpecResidueField (genericPoint Y)) := by
  have := finite_irreducibleComponents_univ_of_irreducibleSpace X
  have := finite_irreducibleComponents_univ_of_irreducibleSpace Y
  have hstalk : IsIso (pullback.snd f (Y.fromSpecStalk (genericPoint Y))) :=
    isIso_pullback_snd_fromSpecStalk_of_isBirational f hf (genericPoint Y)
      (by rw [genericPoints_eq_singleton]; rfl)
  have hres := AlgebraicGeometry.isIso_residue_genericPoint Y
  have hi : IsIso (Spec.map (Y.residue (genericPoint Y))) := by
    have := hres; infer_instance
  exact isIso_pullback_snd_of_eq_comp f (Y.fromSpecStalk (genericPoint Y))
    (Spec.map (Y.residue (genericPoint Y))) (Y.fromSpecResidueField (genericPoint Y))
    (Scheme.Hom.ext' rfl) hstalk

namespace IsModification

/-- For a modification of the spectrum of a normal domain the direct image of the structure sheaf
of the source is the structure sheaf of the target. -/
theorem isIso_c {A : Type u} [CommRing A] [IsNormalDomain A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} (hf : IsModification f) : IsIso f.c := by
  have hX : IsIntegral X := hf.source_isIntegral
  have hP : IsProper f := hf.isProper
  have hN : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hfib : IsIso (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational f hf.isBirational
  have hfibΓ : IsIso (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).appTop := by
    have := hfib
    have hc0 : IsIso (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).c :=
      PresheafedSpace.c_isIso_of_iso
        (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).toPshHom
    have := hc0
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have hΓ : IsIso ((Scheme.ΓSpecIso
      ((Spec (.of A)).residueField (genericPoint (Spec (.of A))))).inv ≫
      (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).appTop) := by
    have := hfibΓ
    infer_instance
  have hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint (Spec (.of A)) := by
    intro x hx
    have hmem := hf.isBirational.bijOn.mapsTo hx
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
  exact Stacks.SteinFactorization.isIso_c_of_isNormal f hgen hΓ

/-- The canonical map from a normal domain to the global functions on a modification of its
spectrum is an isomorphism. -/
theorem isIso_appTop {A : Type u} [CommRing A] [IsNormalDomain A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} (hf : IsModification f) : IsIso f.appTop := by
  have := hf.isIso_c
  exact NatIso.isIso_app_of_isIso f.c (Opposite.op ⊤)

end IsModification

end AlgebraicGeometry

end
