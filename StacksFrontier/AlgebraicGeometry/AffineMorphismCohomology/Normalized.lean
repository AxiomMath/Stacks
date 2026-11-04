module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Collapse
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology under affine morphisms, pinned by resolutions

Let `f : X ⟶ S` be an affine morphism of schemes. Then `H ⁱ(X, ℱ) ≅ H ⁱ(S, f_* ℱ)` for every
quasi-coherent `𝒪_X`-module `ℱ`, naturally in `ℱ`, and the isomorphism is *characterized*:

* it is computed, at every quasi-coherent `ℱ`, by **any** injective resolution `I` of `ℱ`, **any**
  injective resolution `J` of `f_* ℱ` and **any** cochain map `f_* I ⟶ J` preserving the
  augmentation; and
* in degree zero it is the ordinary identification of global sections, read through the canonical
  maps `Γ ⟶ R ⁰Γ` on both sides.

This is [Stacks, Tag 089W] together with the two normalizations listed above.

**The shape of the argument.** `Γ(X, -) = f_* ⋙ Γ(S, -)` *on the nose*
(`Stacks.SchemeCohomology.pushforward_comp_secF`), so `H ⁱ(X, -)` is the `i`-th right derived
functor of a composite and the statement is the collapse of that composite at an `f_*`-acyclic
object. The collapse is `Stacks.AcyclicCollapse`, whose hypotheses hold here by

* `Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj`, [Stacks, Tag 01EX] part (2):
  the pushforward of an *injective* module sheaf has `Γ(S, -)`-acyclic sections. This is strictly
  weaker than the pushforward preserving injective objects, which is false, and it is the reason
  `Stacks.RightDerivedComp` cannot be used directly; and
* `Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward`, [Stacks, Tag 01XC]: the
  higher direct images of a quasi-coherent module along an affine morphism vanish.

## Main definitions

* `Stacks.AffineCohomologyResolution.sectionsPushforwardIso`: global sections on the source are
  global sections of the pushforward on the target, by `Iso.refl`.
* `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso`: **[Stacks, Tag 089W]**, the
  natural isomorphism `H ⁱ(X, -) ≅ H ⁱ(S, f_*(-))` on quasi-coherent modules.

## Main results

* `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso_hom_eq`: the comparison-of-
  resolutions clause.
* `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso_zero_hom`: the degree-zero
  normalization clause.

## Implementation notes

**Why every instance argument is written out.** `AlgebraicGeometry.Scheme.Modules` is a `def`
carrying its *own* `CategoryTheory.Category` instance, distinct from — though definitionally
equal to — the one on `SheafOfModules _`. The statements below mix the two spellings, because
`Scheme.Modules.pushforward f` is stated in the first and `Tag01E3.secF`, hence
`Tag01E3.Hfunctor`, in the second. Instance search then resolves the category of the middle
term to one of the two and fails to find `HasDerivedCategory`, `Functor.Additive` or
`PreservesFiniteLimits` for the other, with an error naming an instance that is present. The
cure is to apply `Stacks.AcyclicCollapse` with all of its instance arguments supplied as terms:
checking a given term against its expected type unfolds both spellings, while instance *search*
does not. Nothing is assumed that is not available; the terms below are exactly what search
finds when the spelling is unambiguous.

**A second construction of the same isomorphism.**
`Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso` has the same type and is built by
a different route — the Leray collapse in the bounded below derived category — and no lemma
identifies the two. The isomorphism built here is the one the two normalizations are proved
about, so all three clauses of the tag speak about a single object.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AffineCohomologyResolution

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Global sections on the source are definitionally global sections of the
pushforward on the target. -/
public noncomputable def sectionsPushforwardIso :
    secF X.ringCatSheaf ⊤ ≅ Scheme.Modules.pushforward f ⋙ secF S.ringCatSheaf ⊤ :=
  Iso.refl _

/-- The hypothesis [Stacks, Tag 01XC] supplies: the higher direct images of a quasi-coherent
module along an affine morphism vanish. -/
theorem isZero_rightDerived_pushforward_obj [IsAffineHom f]
    (F : SheafOfModules.{u} X.ringCatSheaf)
    (hF : SheafOfModules.isQuasicoherent X.ringCatSheaf F) (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) :=
  have : F.IsQuasicoherent := hF
  Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward f F n hn

/-- **[Stacks, Tag 089W].** For an affine morphism, cohomology of a quasi-coherent module
is canonically isomorphic to cohomology of its pushforward. The isomorphism is a
natural isomorphism on the category of quasi-coherent modules, rather than an
unrelated choice of an isomorphism for each module. -/
@[stacks 089W "the natural isomorphism",
  ega "II 5.2.3",
  ega "III 1.3.4" "g to a point",
  ega "III 1.3.3"]
public noncomputable def cohomologyPushforwardIso [IsAffineHom f] (i : ℕ) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
          Hfunctor X.ringCatSheaf ⊤ i ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
          Scheme.Modules.pushforward f ⋙ Hfunctor S.ringCatSheaf ⊤ i :=
  @Stacks.AcyclicCollapse.natIso (SheafOfModules.{u} X.ringCatSheaf)
    (SheafOfModules.{u} S.ringCatSheaf) AddCommGrpCat.{u}
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    IsGrothendieckAbelian.enoughInjectives IsGrothendieckAbelian.enoughInjectives
    (Scheme.Modules.pushforward f)
    (Stacks.SchemeCohomology.pushforward_additive f)
    (Stacks.SchemeCohomology.pushforward_preservesFiniteLimits f)
    (secF S.ringCatSheaf ⊤) inferInstance inferInstance
    (fun I hI => Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj f ⊤ I hI)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (isZero_rightDerived_pushforward_obj f) i

/-- The affine cohomology isomorphism is computed by any map from the pushforward
of an injective resolution to an injective resolution of the pushforward that
preserves the augmentation. Global sections of the pushed-forward complex are
definitionally global sections of the original complex. -/
@[stacks 089W "comparison of resolutions"]
public theorem cohomologyPushforwardIso_hom_eq [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] (i : ℕ)
    (I : InjectiveResolution (C := SheafOfModules X.ringCatSheaf) F)
    (J : InjectiveResolution (C := SheafOfModules S.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj F))
    (φ : ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex ⟶ J.cocomplex)
    (hφ : (Scheme.Modules.pushforward f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (cohomologyPushforwardIso f i).hom.app ⟨F, inferInstance⟩ =
      (I.isoRightDerivedObj (secF X.ringCatSheaf ⊤) i).hom ≫
        HomologicalComplex.homologyMap
          (((secF S.ringCatSheaf ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i ≫
        (J.isoRightDerivedObj (secF S.ringCatSheaf ⊤) i).inv :=
  @Stacks.AcyclicCollapse.objIso_hom_eq (SheafOfModules.{u} X.ringCatSheaf)
    (SheafOfModules.{u} S.ringCatSheaf) AddCommGrpCat.{u}
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    IsGrothendieckAbelian.enoughInjectives IsGrothendieckAbelian.enoughInjectives
    (Scheme.Modules.pushforward f)
    (Stacks.SchemeCohomology.pushforward_additive f)
    (Stacks.SchemeCohomology.pushforward_preservesFiniteLimits f)
    (secF S.ringCatSheaf ⊤) inferInstance inferInstance
    (fun I hI => Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj f ⊤ I hI) F
    (isZero_rightDerived_pushforward_obj f F inferInstance) i I J φ hφ

/-- In degree zero, the affine cohomology isomorphism agrees with the ordinary
identification of global sections through the canonical maps to zeroth right
derived functors. -/
@[stacks 089W "degree-zero normalization"]
public theorem cohomologyPushforwardIso_zero_hom [IsAffineHom f] :
    Functor.whiskerLeft
          (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
          (secF X.ringCatSheaf ⊤).toRightDerivedZero ≫
        (cohomologyPushforwardIso f 0).hom =
      Functor.whiskerLeft
          (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
          (sectionsPushforwardIso f).hom ≫
        Functor.whiskerLeft
          (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
            Scheme.Modules.pushforward f)
          (secF S.ringCatSheaf ⊤).toRightDerivedZero := by
  refine NatTrans.ext (funext fun F => ?_)
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact @Stacks.AcyclicCollapse.toRightDerivedZero_comp_objIso_hom
    (SheafOfModules.{u} X.ringCatSheaf) (SheafOfModules.{u} S.ringCatSheaf) AddCommGrpCat.{u}
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    IsGrothendieckAbelian.enoughInjectives IsGrothendieckAbelian.enoughInjectives
    (Scheme.Modules.pushforward f)
    (Stacks.SchemeCohomology.pushforward_additive f)
    (Stacks.SchemeCohomology.pushforward_preservesFiniteLimits f)
    (secF S.ringCatSheaf ⊤) inferInstance inferInstance
    (fun I hI => Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj f ⊤ I hI) F.obj
    (isZero_rightDerived_pushforward_obj f F.obj F.property)

end Stacks.AffineCohomologyResolution

end
