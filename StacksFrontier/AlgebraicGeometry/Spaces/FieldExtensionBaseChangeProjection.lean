module

public import StacksFrontier.AlgebraicGeometry.Spaces.PurelyInseparableBaseChangeScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The projection from the base change of a space to a finite field extension

Let `k` be a field, `L/k` a field extension and `X` a presheaf on the big fppf site of
`Spec k`. Write `X_L = h_{Spec L} × X` for the base change of `X` to `L`
(`AlgebraicGeometry.Space.extensionBaseChange`) and `π : X_L ⟶ X` for the projection
(`AlgebraicGeometry.Space.extensionBaseChangeProj`). This file records three properties of `π`:

* `π` is surjective after every represented base change;
* `π` is finite locally free when `L/k` is finite;
* the fibre of `π` over a point represented by a field-valued point `Spec κ ⟶ X` has at most
  one element when `κ ⊗_k L` is a field.

## Main results

* `AlgebraicGeometry.Space.presheaf_surjective_extensionBaseChangeProj`
* `AlgebraicGeometry.Space.presheaf_isFiniteLocallyFree_extensionBaseChangeProj`
* `AlgebraicGeometry.Space.subsingleton_setFibre_extensionBaseChangeProj`

## Implementation notes

The first two are inherited from `Spec L ⟶ Spec k` along the cartesian square
`AlgebraicGeometry.Space.isPullback_extensionBaseChangeProj`. For the third, write `P` for the
site object `Spec κ` of the field-valued point and `R = κ ⊗_k L`. The square of spectra of
`k ⟶ κ, L ⟶ R` is cartesian in the site, so `h_{Spec R}` is the pullback of `π` along
`h_P ⟶ X`; every point of the fibre therefore comes from a point of `h_{Spec R}`, of which
there is only one because `R` is a field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (k L : Type u) [Field k] [Field L] [Algebra k L] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k))) (hL : B.Contains (Spec (.of L)))

/-- The projection `X_L ⟶ X` has every base-change stable property of `Spec L ⟶ Spec k`. -/
theorem presheaf_extensionBaseChangeProj {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) (hPL : P (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    (P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (extensionBaseChangeProj k L B hk hL X) := by
  have hι : Over.mkIdTerminal.from (specExtension k L B hk hL) =
      specExtensionToBase k L B hk hL := Over.mkIdTerminal.hom_ext _ _
  exact presheaf_prod_snd hP (specExtension k L B hk hL) X (by rwa [hι])

/-- **The projection `X_L ⟶ X` is surjective after every represented base change:** the
spectrum of a field is a point, so `Spec L ⟶ Spec k` is surjective. -/
theorem presheaf_surjective_extensionBaseChangeProj
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (extensionBaseChangeProj k L B hk hL X) :=
  presheaf_extensionBaseChangeProj k L B hk hL inferInstance
    ((AlgebraicGeometry.surjective_iff _).2 (Function.surjective_to_subsingleton _)) X

/-- **The projection `X_L ⟶ X` is finite locally free when `L/k` is finite:** `Spec L ⟶ Spec k`
is finite, flat and of finite presentation, and each of these is stable under base change. -/
theorem presheaf_isFiniteLocallyFree_extensionBaseChangeProj [FiniteDimensional k L]
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (extensionBaseChangeProj k L B hk hL X) := by
  have hfin := presheaf_extensionBaseChangeProj k L B hk hL
    (P := @_root_.AlgebraicGeometry.IsFinite.{u}) inferInstance
    ((_root_.AlgebraicGeometry.IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap k L))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)) X
  have hflat := presheaf_extensionBaseChangeProj k L B hk hL (P := @Flat.{u}) inferInstance
    (inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap k L))))) X
  have hlfp := presheaf_extensionBaseChangeProj k L B hk hL
    (P := @LocallyOfFinitePresentation.{u}) inferInstance
    ((LocallyOfFinitePresentation.SpecMap_iff (CommRingCat.ofHom (algebraMap k L))).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance))) X
  exact ⟨hfin.1, fun U V g p q hpb =>
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨hfin.2 g p q hpb, hflat.2 g p q hpb, hlfp.2 g p q hpb⟩⟩

/-- **A point with residue field linearly disjoint from `L` has at most one preimage in
`X_L`.** Let `p : Spec κ ⟶ X` be a field-valued point whose structure morphism to `Spec k` is
`Spec` of a `k`-algebra structure on `κ`. If `κ ⊗_k L` is a field, the fibre of
`X_L ⟶ X` over the point of `p` has at most one element. -/
theorem subsingleton_setFibre_extensionBaseChangeProj
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B (Spec (.of k)) hk X) [Algebra k p.carrier]
    [FiniteDimensional k p.carrier] [FiniteDimensional k L]
    (hp : Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) = p.toBase)
    (hfield : IsField (p.carrier ⊗[k] L)) :
    (setFibre B (Spec (.of k)) hk (extensionBaseChangeProj k L B hk hL X) p).Subsingleton := by
  classical
  let R := p.carrier ⊗[k] L
  let : Field R := hfield.toField
  have hR : B.Contains (Spec (.of R)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k R hk
  let Z : BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let Q : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k R))) :
      B.obj hR ⟶ B.obj hk)
  let E := specExtension k L B hk hL
  let a : Q ⟶ p.siteObject := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap p.carrier R)))) (by
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (algebraMap p.carrier R)) ≫ p.toBase = _
    rw [← hp, ← Spec.map_comp]
    congr 1)
  let b : Q ⟶ E := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : L →+* R))))
    (by
      apply ObjectProperty.hom_ext
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp)
  let a₀ : p.siteObject ⟶ Z := Over.homMk p.siteObject.hom
  let b₀ : E ⟶ Z := specExtensionToBase k L B hk hL
  have hab : IsPullback a b a₀ b₀ := by
    apply IsPullback.of_map_of_faithful (Over.forget (B.obj hk))
    apply IsPullback.of_map_of_faithful B.inclusion
    show IsPullback (Spec.map (CommRingCat.ofHom (algebraMap p.carrier R)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : L →+* R)))
      p.toBase (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    rw [← hp]
    exact ((CommRingCat.isPushout_tensorProduct k p.carrier L).op.map Scheme.Spec).flip
  let s : yoneda.obj p.siteObject ⟶ X := yonedaEquiv.symm p.value
  let π := extensionBaseChangeProj k L B hk hL X
  have hright := isPullback_extensionBaseChangeProj k L B hk hL X
  have hbot : s ≫ (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X = yoneda.map a₀ :=
    (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _
  let q : yoneda.obj Q ⟶ extensionBaseChange k L B hk hL X :=
    hright.lift (yoneda.map b) (yoneda.map a ≫ s) (by
      rw [Category.assoc, hbot, ← Functor.map_comp, ← Functor.map_comp, hab.w])
  have hleft : IsPullback q (yoneda.map a) π s := by
    refine IsPullback.of_right ?_ (hright.lift_snd _ _ _) hright
    rw [hright.lift_fst, hbot]
    exact (hab.map yoneda).flip
  have : Subsingleton (points B (Spec (.of k)) hk (yoneda.obj Q)) :=
    (pointsEquivScheme B (Spec (.of k)) hk Q).subsingleton_congr.mpr
      (inferInstanceAs (Subsingleton (PrimeSpectrum R)))
  have hpt : ∀ x ∈ setFibre B (Spec (.of k)) hk π p, ∃ w : points B (Spec (.of k)) hk
      (yoneda.obj Q), pointsMap B (Spec (.of k)) hk _ q w = x := fun x hx =>
    (exists_points_of_isPullback B (Spec (.of k)) hk hleft x
      ((FieldValuedPoint.tautological B (Spec (.of k)) hk p).class B (Spec (.of k)) hk _)
      (hx.trans (FieldValuedPoint.pointsMap_class_tautological B (Spec (.of k)) hk p).symm)).imp
      fun _ h => h.1
  intro x hx y hy
  obtain ⟨w, rfl⟩ := hpt x hx
  obtain ⟨w', rfl⟩ := hpt y hy
  rw [Subsingleton.elim w w']

end AlgebraicGeometry.Space

end
