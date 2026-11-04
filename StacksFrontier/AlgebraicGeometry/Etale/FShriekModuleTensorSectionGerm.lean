module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorStalkGenerator

/-!
# The germ of the tensor product of two sections

Let `B` be a big étale site containing a scheme `X`, let `Λ` be a commutative ring and let `F`,
`H` be sheaves of `Λ`-modules on the small étale site of `X`. The tensor product `F ⊗_Λ H` is a
sheafification, so a pair of sections over an object of the site gives a section of `F ⊗_Λ H`
only through the comparison `Stacks.ModuleSheafTensorSection.moduleToTensorSection`. This file
records what the fibre at a geometric point does to that comparison: it inverts it, and on germs
it is the naturality of germs.

## Main results

* `AlgebraicGeometry.SmallEtale.toPresheafFiber_moduleToTensorSection` — **the germ of a section
  of the pointwise tensor product is the germ of its image in `F ⊗_Λ H`.**
* `AlgebraicGeometry.SmallEtale.toPresheafFiber_tensorSupportedSectionsHom_val` — **the germ of
  a supported section tensored with a fixed section** is the image of the germ of the
  corresponding pure tensor.
* `AlgebraicGeometry.SmallEtale.isIso_presheafFiber_map_moduleToTensorSection` — **the fibre of
  the comparison is an isomorphism.**

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] (X : B.Scheme)

attribute [local instance] moduleSheafMonoidal

/-- `Λ`-modules in the coefficient universe of the small étale site have limits indexed by the
universe of the schemes. -/
@[instance_reducible]
public def hasLimitsOfSizeModuleCatSmall : HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) v} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) v, max (u + 1) v}

attribute [local instance] hasLimitsOfSizeModuleCatSmall

/-- **The germ of a section of the pointwise tensor product is the germ of its image in
`F ⊗_Λ H`.** -/
public theorem toPresheafFiber_moduleToTensorSection
    (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (x : GeometricPoint X.obj)
    (W : SmallEtale B X.obj X.property)
    (w : (geometricPointFiber B X.obj X.property x).obj W) :
    (geometricPointSitePoint B X.obj X.property x).toPresheafFiber W w (F.obj ⊗ H.obj) ≫
        (geometricPointSitePoint B X.obj X.property x).presheafFiber.map
          (Stacks.ModuleSheafTensorSection.moduleToTensorSection
            (SmallEtale.topology B X.obj X.property) Λ F H) =
      (Stacks.ModuleSheafTensorSection.moduleToTensorSection
          (SmallEtale.topology B X.obj X.property) Λ F H).app (op W) ≫
        (geometricPointSitePoint B X.obj X.property x).toPresheafFiber W w (F ⊗ H).obj :=
  (geometricPointSitePoint B X.obj X.property x).toPresheafFiber_naturality
    (Stacks.ModuleSheafTensorSection.moduleToTensorSection
      (SmallEtale.topology B X.obj X.property) Λ F H) W w

/-- **The fibre of the comparison of the pointwise tensor product with the tensor product of
sheaves is an isomorphism.** -/
public instance isIso_presheafFiber_map_moduleToTensorSection
    (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (x : GeometricPoint X.obj) :
    IsIso ((geometricPointSitePoint B X.obj X.property x).presheafFiber.map
      (Stacks.ModuleSheafTensorSection.moduleToTensorSection
        (SmallEtale.topology B X.obj X.property) Λ F H)) := by
  have : IsIso ((Functor.Monoidal.μIso (presheafToSheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) v} Λ)) F.obj H.obj).inv ≫
      ((sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
        (sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app H)) := by
    have : IsIso ((sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
        (sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app H) :=
      (tensorIso (asIso ((sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app F))
        (asIso ((sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app H))).isIso_hom
    infer_instance
  change IsIso ((geometricPointSitePoint B X.obj X.property x).presheafFiber.map
    (toSheafify (SmallEtale.topology B X.obj X.property) (F.obj ⊗ H.obj) ≫
      (sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) v} Λ)).map
        ((Functor.Monoidal.μIso (presheafToSheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) v} Λ)) F.obj H.obj).inv ≫
          ((sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
              (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
            (sheafificationAdjunction (SmallEtale.topology B X.obj X.property)
              (ModuleCat.{max (u + 1) v} Λ)).counit.app H))))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- **The germ of a supported section tensored with a fixed section.** The germ at a lift of a
geometric point `x̄` of the supported section `a ⊗ h` of `F ⊗_Λ H` is the image, under the fibre
of the comparison of the pointwise tensor product with the tensor product of sheaves, of the
germ of the pure tensor of `a` with the restriction of `h`. -/
public theorem toPresheafFiber_tensorSupportedSectionsHom_val
    (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (x : GeometricPoint X.obj)
    (W : SmallEtale B X.obj X.property) (h : H.obj.obj (op W))
    (Z : Set ((SmallEtale.toScheme B X.obj X.property).obj W)) (hZ : IsLocallyClosed Z)
    (a : supportedSections B X.obj X.property
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) W Z hZ)
    (w : (geometricPointFiber B X.obj X.property x).obj
      (openObject B X.obj X.property W (supportOpen B X.obj X.property W Z hZ))) :
    (geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        (openObject B X.obj X.property W (supportOpen B X.obj X.property W Z hZ)) w (F ⊗ H).obj
        ((tensorSupportedSectionsHom B Λ F H W h Z hZ a).val) =
      (geometricPointSitePoint B X.obj X.property x).presheafFiber.map
        (Stacks.ModuleSheafTensorSection.moduleToTensorSection
          (SmallEtale.topology B X.obj X.property) Λ F H)
        ((geometricPointSitePoint B X.obj X.property x).toPresheafFiber
          (openObject B X.obj X.property W (supportOpen B X.obj X.property W Z hZ)) w
          (F.obj ⊗ H.obj)
          ((show ↥(F.obj.obj
              (op (openObject B X.obj X.property W (supportOpen B X.obj X.property W Z hZ))))
              from a.val) ⊗ₜ[Λ] H.obj.map
            (openObjectι B X.obj X.property W
              (supportOpen B X.obj X.property W Z hZ)).op h)) :=
  (ConcreteCategory.congr_hom
    (toPresheafFiber_moduleToTensorSection B Λ X F H x
      (openObject B X.obj X.property W (supportOpen B X.obj X.property W Z hZ)) w) _).symm

end AlgebraicGeometry.SmallEtale

end
