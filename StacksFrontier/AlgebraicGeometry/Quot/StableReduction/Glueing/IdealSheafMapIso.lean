module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleIrreducibleCover0551
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SubbundleZeroSchemeCartier

/-!
# Direct image of ideal sheaves along an isomorphism of schemes

Along an isomorphism of schemes `f : X ⟶ Y`, the direct image `I ↦ I.map f` of ideal sheaves is
the inverse image along `inv f`. It therefore commutes with suprema, its support is the image of
the support, and the closed subscheme it cuts out is isomorphic to the one cut out by `I`,
compatibly with the closed immersions into `X` and `Y`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMapIso`: the isomorphism
  `I.subscheme ≅ (I.map f).subscheme`.

## Main results

The identity `I.map f = I.comap (inv f)` is the base's
`AlgebraicGeometry.Scheme.IdealSheafData.map_eq_comap_inv`.

* `AlgebraicGeometry.Scheme.IdealSheafData.map_sup_of_isIso`: the direct image commutes with
  suprema.
* `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_map_of_isIso`: the support of the direct
  image is the image of the support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- Along an isomorphism, the direct image of ideal sheaves commutes with binary suprema. -/
theorem map_sup_of_isIso (I J : X.IdealSheafData) : (I ⊔ J).map f = I.map f ⊔ J.map f := by
  simp only [map_eq_comap_inv _ f, comap_sup]

/-- Along an isomorphism, the support of the direct image of an ideal sheaf is the image of its
support. -/
theorem coe_support_map_of_isIso (I : X.IdealSheafData) :
    ((I.map f).support : Set Y) = f '' I.support := by
  rw [map_eq_comap_inv _ f, support_comap, TopologicalSpace.Closeds.coe_preimage]
  refine (congrFun (Set.image_eq_preimage_of_inverse (f := f) (g := inv f) (fun x => ?_)
    (fun y => ?_)) _).symm <;> simp [← Scheme.Hom.comp_apply]

/-- Along an isomorphism `f`, the closed subscheme cut out by an ideal sheaf `I` is isomorphic to
the one cut out by its direct image. -/
def subschemeMapIso (I : X.IdealSheafData) : I.subscheme ≅ (I.map f).subscheme :=
  have : IsClosedImmersion (I.subschemeι ≫ f) := inferInstance
  have h : IsIso (I.subschemeι ≫ f).toImage := inferInstance
  @asIso _ _ _ _ (I.subschemeι ≫ f).toImage h

/-- The isomorphism `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMapIso` is compatible with
the closed immersions. -/
@[reassoc (attr := simp)]
theorem subschemeMapIso_hom_subschemeι (I : X.IdealSheafData) :
    (I.subschemeMapIso f).hom ≫ (I.map f).subschemeι = I.subschemeι ≫ f :=
  show (I.subschemeι ≫ f).toImage ≫ (I.subschemeι ≫ f).imageι = _ from
    (I.subschemeι ≫ f).toImage_imageι

/-- The isomorphism `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMapIso` is compatible with
the closed immersions, pointwise. -/
theorem subschemeι_subschemeMapIso_hom_apply (I : X.IdealSheafData) (x : I.subscheme) :
    (I.map f).subschemeι ((I.subschemeMapIso f).hom x) = f (I.subschemeι x) := by
  rw [← Scheme.Hom.comp_apply, subschemeMapIso_hom_subschemeι, Scheme.Hom.comp_apply]

end AlgebraicGeometry.Scheme.IdealSheafData

end
