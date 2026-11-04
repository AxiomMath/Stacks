module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.IdealCompatibility

/-!
# The first-order extension of a deformation induces the prescribed map on the base ideal

Let `Z ⊆ Y'` and `Z₂ ⊆ X'` be closed subspaces which are first order thickenings, `g : X' ⟶ Y'`
and `e₀ : Z₂ ⟶ Z` with `ι₂ ≫ g = e₀ ≫ ι`, and suppose the conormal map
`e₀^*𝒞_{Z/Y'} ⟶ 𝒞_{Z₂/X'}` is an isomorphism (by Stacks 06BH this is the case when `g` is
flat and the square is cartesian). Then the extension `0 → 𝒞_{Z₂/X'} → ι₂⁻¹𝒪_{X'} → 𝒪_{Z₂} → 0`,
with its kernel identified with `e₀^*𝒞_{Z/Y'}` along the conormal map, induces the prescribed
map `c : e₀⁻¹𝒞_{Z/Y'} ⟶ e₀^*𝒞_{Z/Y'}` of the extension problem
`AlgebraicGeometry.Space.FlatThickeningDeformation.problem` of `e₀`: it is a solution of that
problem (`isCompatible_transportKernel`). This is the commutative diagram displayed in the proof
of [Stacks Project, Tag 0D17].

## Main results

* `isCompatible_transportKernel_of_factorization`: an extension of algebras whose ideal image
  factors through `c`, an isomorphism of modules and the inclusion of its kernel induces `c`.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.isCompatible_transportKernel`.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u v w



section GenericCompatibility

open Deformation Deformation.ToposThickening AlgebraicGeometry

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {D : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})] [D.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  (f : RingedToposHom X D) {A : Sheaf D.J CommRingCat.{w₂}} {a : A ⟶ D.O}
  {M : SheafOfModules.{w₂} ((sheafCompose D.J (forget₂ CommRingCat.{w₂} RingCat.{w₂})).obj D.O)}
  (E : AlgebraExtension a M)
  (G : SheafOfModules.{w₁} ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj X.O))
  (c : inverseImageExtensionIdeal f (M := M) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).map
          f.fSharpInverseImage)).obj G)
  {A₁ : Sheaf X.J CommRingCat.{w₁}} {a₁ : A₁ ⟶ X.O}
  (θ : A₁ ≅ (inverseImageCommRingFunctor f.toToposHom).obj E.extension)
  {N : SheafOfModules.{w₁} ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj X.O)}
  (Q : AlgebraExtension a₁ N)


/-- **Compatibility from a factorisation through the kernel.** If the ideal image map
`f⁻¹𝒥 ⟶ 𝒜 ⟶ 𝒪'` factors, on underlying sheaves of sets, as `c` followed by an isomorphism
`φ : 𝒢 ≅ 𝒩` and the inclusion of the kernel `𝒩` of `𝒪'`, then `𝒪'` with its kernel identified
with `𝒢` along `φ` induces `c`. -/
theorem isCompatible_transportKernel_of_factorization (Q₀ : AlgebraExtension a₁ N) (φ : G ⟶ N)
    [hφi : IsIso φ]
    (cS : f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)
        ((SheafOfModules.restrictScalars ((sheafCompose D.J
          (forget₂ CommRingCat.{w₂} RingCat.{w₂})).map E.reduction)).obj M)) ⟶
      (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
          X.O)).obj G)
    (φS : (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
        X.O)).obj G ⟶
      (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
          X.O)).obj N)
    (ιS : (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
        X.O)).obj N ⟶ X.forgetRing.obj Q₀.extension)
    (h : f.toToposHom.inverseImage.map E.inclSheafSets ≫ X.forgetRing.map (θ.inv ≫ Q₀.algebraMap) =
      cS ≫ φS ≫ ιS)
    (hc : ∀ (U : X.Cᵒᵖ) (x : (inverseImageExtensionIdeal f (M := M)).val.obj U),
      (Sheaf.sectionsFunctor X.J U).map cS x = c.val.app U x)
    (hφ : ∀ (U : X.Cᵒᵖ) (m : G.val.obj U), (Sheaf.sectionsFunctor X.J U).map φS m = φ.val.app U m)
    (hι : ∀ (U : X.Cᵒᵖ) (m : N.val.obj U), (Sheaf.sectionsFunctor X.J U).map ιS m = Q₀.incl m) :
    (RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c).IsCompatible θ c
      (Q₀.transportKernel (asIso φ).symm) :=
  isCompatible_transportKernel_of_sheaf_eq f E G c θ Q₀ (asIso φ).symm h fun U x ↦
    (congrArg (fun y ↦ (Sheaf.sectionsFunctor X.J U).map ιS y)
      ((hφ U _).trans (congrArg (φ.val.app U) (hc U x)))).trans (hι U _)

end GenericCompatibility

namespace AlgebraicGeometry.Space.FlatThickeningDeformation


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)
  {X' : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X'.1)
  (hZ₂ : IsFirstOrderThickening B S hS X' Z₂.1) (g : X' ⟶ Y') (e₀ : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
      AlgebraicSpaces B S hS) ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X' Z₂ ≫ g = e₀ ≫ (subspaceInclusion B S hS Y' Z))


omit hZ in
/-- On sections over `U`, the inclusion of the conormal sheaf `𝒞_{Z₂/X'}` into
`ι₂⁻¹𝒪_{X'}` is the kernel inclusion of the first-order algebra extension of `Z₂ ⊂ X'`. -/
theorem sections_conormalSetInclusion (U : (SmallEtale B S hS Z₂.1.toFunctor)ᵒᵖ)
    (m : (conormalModule B S hS X' Z₂).val.obj U) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z₂.1.toFunctor) U).map
        (conormalSetInclusion B S hS Z₂ hZ₂) m =
      (firstOrderAlgebraExtension B S hS Z₂ hZ₂ g).incl m :=
  (congrArg (fun φ ↦ (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z₂.1.toFunctor) U).map φ m)
    (moduleSheafFunctor_map_conormalInverseImageι B S hS Z₂ hZ₂).symm).trans
    (firstOrderAlgebraExtension_incl Z₂ hZ₂ g m).symm

omit hZ₂ in
/-- On sections over `U`, `problemCSets` is the prescribed map `c` of the extension problem
`problem e₀ hZ`. -/
theorem problemCSets_sections (U : (SmallEtale B S hS Z₂.1.toFunctor)ᵒᵖ)
    (x : (problem e₀ hZ).I.val.obj U) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z₂.1.toFunctor) U).map (problemCSets hZ Z₂
        e₀) x =
      (problem e₀ hZ).c.val.app U x :=
  rfl

/-- On sections over `U`, the map of underlying sheaves of sets of the conormal map
`e₀^*𝒞_{Z/Y'} ⟶ 𝒞_{Z₂/X'}` is the conormal map itself. -/
theorem sections_conormalMap (U : (SmallEtale B S hS Z₂.1.toFunctor)ᵒᵖ)
    (m : ((modulePullback B S hS e₀).obj (conormalModule B S hS Y' Z)).val.obj U) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z₂.1.toFunctor) U).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS))).map
          (conormalMap B S hS Z₂ Z g e₀ hsq)) m =
      (conormalMap B S hS Z₂ Z g e₀ hsq).val.app U m :=
  rfl

/-- `isCompatible_transportKernel`, for the problem written as `ofBaseAlgebraExtension`. -/
theorem isCompatible_transportKernel_ofBase [IsIso (conormalMap B S hS Z₂ Z g e₀ hsq)] :
    (Deformation.ToposThickening.RingedToposExtensionProblem.ofBaseAlgebraExtension
      (smallEtaleRingedToposHom B S hS e₀) (baseExtension hZ) (pulledBackConormal e₀)
      (problem e₀ hZ).c).IsCompatible (squareBaseIso hZ Z₂ g e₀ hsq) (problem e₀ hZ).c
      ((firstOrderAlgebraExtension B S hS Z₂ hZ₂ g).transportKernel
        (asIso (conormalMap B S hS Z₂ Z g e₀ hsq)).symm) :=
  isCompatible_transportKernel_of_factorization (smallEtaleRingedToposHom B S hS e₀)
    (baseExtension hZ) (pulledBackConormal e₀) (problem e₀ hZ).c (squareBaseIso hZ Z₂ g e₀ hsq)
    (firstOrderAlgebraExtension B S hS Z₂ hZ₂ g) (conormalMap B S hS Z₂ Z g e₀ hsq)
    (problemCSets hZ Z₂ e₀) _ (conormalSetInclusion B S hS Z₂ hZ₂)
    (idealImageSets_eq_firstOrderAlgebraMap hZ Z₂ hZ₂ g e₀ hsq)
    (problemCSets_sections hZ Z₂ e₀) (sections_conormalMap Z₂ g e₀ hsq)
    (sections_conormalSetInclusion Z₂ hZ₂ g) (hφi := by assumption)

/-- **The ideal map of a morphism of first-order thickenings is the conormal map**: the
first-order algebra extension of `Z₂ ⊂ X'`, with its kernel identified with `e₀^*𝒞_{Z/Y'}` along
the conormal map, induces the prescribed map `c` of the problem on the base ideal. -/
theorem isCompatible_transportKernel [IsIso (conormalMap B S hS Z₂ Z g e₀ hsq)] :
    (problem e₀ hZ).IsCompatible (squareBaseIso hZ Z₂ g e₀ hsq) (problem e₀ hZ).c
      ((firstOrderAlgebraExtension B S hS Z₂ hZ₂ g).transportKernel
        (asIso (conormalMap B S hS Z₂ Z g e₀ hsq)).symm) :=
  isCompatible_transportKernel_ofBase hZ Z₂ hZ₂ g e₀ hsq

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
