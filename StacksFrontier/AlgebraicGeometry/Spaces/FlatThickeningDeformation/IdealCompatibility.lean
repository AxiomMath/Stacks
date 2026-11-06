module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInclusionRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInclusionSections

/-!
# The ideal map of a morphism of first-order thickenings is the conormal map

Let `Z ⊆ Y'` and `Z₂ ⊆ X'` be closed subspaces which are first order thickenings, `g : X' ⟶ Y'`
and `e₀ : Z₂ ⟶ Z` with `ι₂ ≫ g = e₀ ≫ ι`. On the small étale site of `Z₂` the extension
`0 → 𝒞_{Z₂/X'} → ι₂⁻¹𝒪_{X'} → 𝒪_{Z₂} → 0` is an extension of `e₀⁻¹ι⁻¹𝒪_{Y'}`-algebras, and the
ideal `e₀⁻¹𝒞_{Z/Y'}` of the base maps into its middle term. This file proves, as an equality of
morphisms of sheaves of sets (`idealImageSets_eq`), that this map is the canonical map
`e₀⁻¹𝒞_{Z/Y'} ⟶ e₀^*𝒞_{Z/Y'}` followed by the conormal map `e₀^*𝒞_{Z/Y'} ⟶ 𝒞_{Z₂/X'}` and the
inclusion of the conormal sheaf. Both sides are compared after transposing
along the adjunction `e₀⁻¹ ⊣ e₀_*`, where the statement becomes
`AlgebraicGeometry.Space.conormalSetInclusion_restriction_conormalModule`.

This is the step of the proof of [Stacks Project, Tag 0D17] identifying the ideal sheaf of
`X ⊆ X'` with `f^*𝒞_{Y/Y'}` compatibly with the diagram of the extension problem.

## Main results

* `AlgebraicGeometry.Space.FlatThickeningDeformation.idealImageSets_eq`: the ideal image is the
  canonical map followed by the conormal map.
* `isCompatible_transportKernel_of_sheaf_eq`: a criterion for an extension of algebras to
  induce the prescribed map of a problem posed by `ofBaseAlgebraExtension`.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u v w

section GenericIdealImage

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

/-- The ideal image of a section `x` of `f⁻¹I` in the problem posed by `ofBaseAlgebraExtension`
is the image of `x` under the inverse image of the kernel inclusion of `E`, followed by `θ⁻¹` and
the algebra map of `Q`. -/
theorem idealImage_ofBaseAlgebraExtension (U : X.Cᵒᵖ)
    (x : (inverseImageExtensionIdeal f (M := M)).val.obj U) :
    (RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c).idealImage θ Q x =
      Q.algebraMap.hom.app U (θ.inv.hom.app U
        ((Sheaf.sectionsFunctor X.J U).map (f.toToposHom.inverseImage.map E.inclSheafSets) x)) :=
  congrArg (fun y ↦ Q.algebraMap.hom.app U (θ.inv.hom.app U y))
    (inverseImageExtensionIdealIncl_val_app f E U x)

/-- If the image of the base ideal under `θ⁻¹` and the algebra map of `Q₀` is a morphism `ψ`
whose value on each section `x` is the kernel inclusion of `e⁻¹(c(x))`, then the transport of
`Q₀` along `e : N ≅ G` is compatible with `c` in the problem posed by `ofBaseAlgebraExtension`. -/
theorem isCompatible_transportKernel_of_sheaf_eq (Q₀ : AlgebraExtension a₁ N) (e : N ≅ G)
    {ψ : f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)
        ((SheafOfModules.restrictScalars ((sheafCompose D.J
          (forget₂ CommRingCat.{w₂} RingCat.{w₂})).map E.reduction)).obj M)) ⟶
      X.forgetRing.obj Q₀.extension}
    (h : f.toToposHom.inverseImage.map E.inclSheafSets ≫ X.forgetRing.map (θ.inv ≫ Q₀.algebraMap) =
      ψ)
    (h' : ∀ (U : X.Cᵒᵖ) (x : (inverseImageExtensionIdeal f (M := M)).val.obj U),
      (Sheaf.sectionsFunctor X.J U).map ψ x = Q₀.incl (e.inv.val.app U (c.val.app U x))) :
    (RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c).IsCompatible θ c
      (Q₀.transportKernel e) := fun U x ↦
  (idealImage_ofBaseAlgebraExtension f E G c θ (Q₀.transportKernel e) U x).trans
    ((congrArg (fun φ ↦ (Sheaf.sectionsFunctor X.J U).map φ x) h).trans (h' U x))

end GenericIdealImage

section GenericSections

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- On sections over `U`, a morphism `p` into the underlying sheaf of sets of `R₁` followed by
the underlying map of `a ≫ b` sends `x` to `b (a (p x))`. -/
theorem sections_comp_forget_map_comp {T : Sheaf J (Type w)} {R₁ R₂ R₃ : Sheaf J CommRingCat.{w}}
    (p : T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R₁) (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₃)
    (U : Cᵒᵖ) (x : T.obj.obj U) :
    (Sheaf.sectionsFunctor J U).map (p ≫ (sheafCompose J (forget CommRingCat.{w})).map (a ≫ b)) x =
      b.hom.app U (a.hom.app U ((Sheaf.sectionsFunctor J U).map p x)) :=
  rfl

/-- On sections over `U`, the composite `p ≫ q ≫ r` of morphisms of sheaves of sets sends `x` to
`r (q (p x))`. -/
theorem sections_comp_comp {T₁ T₂ T₃ T₄ : Sheaf J (Type w)} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (r : T₃ ⟶ T₄) (U : Cᵒᵖ) (x : T₁.obj.obj U) :
    (Sheaf.sectionsFunctor J U).map (p ≫ q ≫ r) x =
      (Sheaf.sectionsFunctor J U).map r ((Sheaf.sectionsFunctor J U).map q
        ((Sheaf.sectionsFunctor J U).map p x)) :=
  rfl

end GenericSections

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

section Restriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  {X' : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X'.1) (g : X' ⟶ Y')
  (e₀ : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X' Z₂ ≫ g = e₀ ≫ subspaceInclusion B S hS Y' Z)
  (hZ₂ : IsFirstOrderThickening B S hS X' Z₂.1) (hZ : IsFirstOrderThickening B S hS Y' Z.1)

/-- `AlgebraicGeometry.Space.conormalSetInclusion_restriction_conormalModule`, with the direct
image written as that of the morphism of small étale ringed topoi. -/
theorem conormalSetInclusion_restriction_conormalModule_smallEtale :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
        ((modulePullbackAdjunction B S hS e₀).homEquiv (conormalModule B S hS Y' Z)
          (conormalModule B S hS X' Z₂) (conormalMap B S hS Z₂ Z g e₀ hsq)) ≫
      (smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map
        (conormalSetInclusion B S hS Z₂ hZ₂) =
    conormalSetInclusion B S hS Z hZ ≫
      (sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor) (forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z₂ Z g e₀ hsq) :=
  conormalSetInclusion_restriction_conormalModule B S hS Z₂ Z g e₀ hsq hZ₂ hZ

end Restriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)
  {X' : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X'.1)
  (hZ₂ : IsFirstOrderThickening B S hS X' Z₂.1) (g : X' ⟶ Y') (e₀ : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
      AlgebraicSpaces B S hS) ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X' Z₂ ≫ g = e₀ ≫ (subspaceInclusion B S hS Y' Z))

/-- The inclusion of the kernel of `Deformation.AlgebraExtension.ofKernelInclusion` is the given
inclusion, on sections. -/
theorem _root_.Deformation.AlgebraExtension.ofKernelInclusion_incl {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
    {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    (E : Sheaf J CommRingCat.{u}) (r : E ⟶ O)
    (hr : Presheaf.IsLocallySurjective J r.hom) (α : A ⟶ E) (hα : α ≫ r = a)
    (r' : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj E ⟶
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
    (hr' : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map r = r')
    (ι : (SheafOfModules.restrictScalars r').obj M ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj E))
    (hzero : ∀ (U : Cᵒᵖ) (m : M.val.obj U), r'.hom.app U (ι.val.app U m) = 0)
    (hexists : ∀ (U : Cᵒᵖ) (x : E.obj.obj U), r.hom.app U x = 0 →
      ∃ m : M.val.obj U, (ι.val.app U m : E.obj.obj U) = x)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (ι.val.app U))
    (hsq : ∀ (U : Cᵒᵖ) (x y : E.obj.obj U), r.hom.app U x = 0 → r.hom.app U y = 0 →
      x * y = 0) {U : Cᵒᵖ} (m : M.val.obj U) :
    (Deformation.AlgebraExtension.ofKernelInclusion (a := a) E r hr α hα r' hr' ι hzero hexists
      hinj hsq).incl m = (ι.val.app U m : E.obj.obj U) := by
  subst hr'
  rfl

/-- The kernel inclusion of an extension transported along `e : ℳ ≅ 𝒩` is the original one
after `e⁻¹`, on sections. -/
theorem _root_.Deformation.AlgebraExtension.transportKernel_incl {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    (P : Deformation.AlgebraExtension a M) (e : M ≅ N) {U : Cᵒᵖ} (n : N.val.obj U) :
    (P.transportKernel e).incl n = P.incl (e.inv.val.app U n) :=
  rfl

omit hZ in
/-- The kernel inclusion of the extension of a first-order thickening is the conormal inclusion
`𝒞_{Z/X} ⟶ i⁻¹𝒪_X`, on sections. -/
theorem firstOrderAlgebraExtension_incl {U : (SmallEtale B S hS Z₂.1.toFunctor)ᵒᵖ}
    (m : (conormalModule B S hS X' Z₂).val.obj U) :
    (firstOrderAlgebraExtension B S hS Z₂ hZ₂ g).incl m =
      (conormalInverseImageι B S hS Z₂ hZ₂).val.app U m :=
  Deformation.AlgebraExtension.ofKernelInclusion_incl.{u, u + 1, u}
    (J := SmallEtale.topology B S hS Z₂.1.toFunctor)
    (A := inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂ ≫ g))
    (O := (smallEtaleRingedTopos B S hS ⟨Z₂.1.toFunctor, Z₂.2.1⟩).O)
    (M := conormalModule B S hS X' Z₂)
    (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂))
    (structureSharpInverseImage B S hS (subspaceInclusion B S hS X' Z₂))
    (isLocallySurjective_structureSharpInverseImage B S hS (subspaceInclusion B S hS X' Z₂) Z₂.2.2)
    (inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g)
    (inverseImageStructureSheafMap_comp_structureSharpInverseImage B S hS _ g)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X' Z₂))
    (forget₂_map_structureSharpInverseImage B S hS _)
    (conormalInverseImageι B S hS Z₂ hZ₂) _ _ _ _ m

/-- `(i₂ ≫ g)⁻¹𝒪_{Y'} ≅ e₀⁻¹t⁻¹𝒪_{Y'}`: the square followed by the composition law for inverse
images. -/
def squareBaseIso :
    inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂ ≫ g) ≅
      (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS e₀).toToposHom).obj
        (baseExtension hZ).extension :=
  eqToIso (congrArg (inverseImageStructureSheaf B S hS) hsq) ≪≫
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS e₀ (subspaceInclusion B S hS Y'
        Z)).app
      (smallEtaleRingedTopos B S hS Y').O).symm

/-- `squareBaseIso` followed by the inverse image of the base reduction and the comorphism of
`e₀` is the comorphism `(i₂ ≫ g)⁻¹𝒪_{Y'} ⟶ 𝒪_{Z₂}`. -/
theorem squareBaseIso_hom_comp :
    (squareBaseIso hZ Z₂ g e₀ hsq).hom ≫
        (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS e₀).toToposHom).map
          (problem e₀ hZ).baseReduction ≫ (problem e₀ hZ).f.fSharpInverseImage =
      structureSharpInverseImage B S hS (subspaceInclusion B S hS X' Z₂ ≫ g) := by
  have h := smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS e₀
    (subspaceInclusion B S hS Y' Z)
  have h' : ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS e₀ (subspaceInclusion B S hS
      Y' Z)).app
      (smallEtaleRingedTopos B S hS Y').O).inv ≫
        (smallEtaleInverseImageRing B S hS e₀).map
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y' Z)).fSharpInverseImage ≫
        (smallEtaleRingedToposHom B S hS e₀).fSharpInverseImage =
      (smallEtaleRingedToposHom B S hS (e₀ ≫ (subspaceInclusion B S hS Y'
          Z))).fSharpInverseImage :=
    (Iso.inv_comp_eq _).2 h.symm
  show (eqToHom (congrArg (inverseImageStructureSheaf B S hS) hsq) ≫
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS e₀ (subspaceInclusion B S hS Y'
          Z)).app
        (smallEtaleRingedTopos B S hS Y').O).inv) ≫
      (smallEtaleInverseImageRing B S hS e₀).map
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y' Z)).fSharpInverseImage ≫
      (smallEtaleRingedToposHom B S hS e₀).fSharpInverseImage = _
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h').trans
    (structureSharpInverseImage_eqToHom B S hS hsq))


omit hZ₂ in
/-- The target of the prescribed map, on underlying sheaves of sets, written over `𝒪_{Z₂}`. -/
theorem problemCSets_target_eq :
    (Sheaf.moduleSheafFunctor ((sheafCompose (SmallEtale.topology B S hS Z₂.1.toFunctor)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (inverseImageStructureSheaf B S hS e₀))).obj
        ((SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS
          Z₂.1.toFunctor) (forget₂ CommRingCat.{u} RingCat.{u})).map
            (problem e₀ hZ).f.fSharpInverseImage)).obj (problem e₀ hZ).G) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
          AlgebraicSpaces B S hS))).obj
          ((modulePullback B S hS e₀).obj (conormalModule B S hS Y' Z)) := rfl

omit hZ₂ in
/-- The prescribed map `c : e₀⁻¹𝒞_{Z/Y'} ⟶ e₀^*𝒞_{Z/Y'}` of the problem, on underlying sheaves of
sets. -/
def problemCSets :
    (Sheaf.moduleSheafFunctor ((sheafCompose (SmallEtale.topology B S hS Z₂.1.toFunctor)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (inverseImageStructureSheaf B S hS e₀))).obj (problem e₀ hZ).I ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
          AlgebraicSpaces B S hS))).obj
          ((modulePullback B S hS e₀).obj (conormalModule B S hS Y' Z)) :=
  (Sheaf.moduleSheafFunctor ((sheafCompose (SmallEtale.topology B S hS Z₂.1.toFunctor)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (inverseImageStructureSheaf B S hS e₀))).map (problem e₀ hZ).c ≫
    eqToHom (problemCSets_target_eq hZ Z₂ e₀)

omit hZ in
/-- Reassociation of four composable morphisms: `a ≫ (b ≫ c) ≫ r = ((a ≫ b) ≫ c) ≫ r`. -/
theorem comp_comp_comp_eq_comp_comp_comp {𝒞 : Type*} [Category 𝒞] {A₁ A₂ A₃ A₄ A₅ : 𝒞}
    (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄) (r : A₄ ⟶ A₅) :
    a ≫ (b ≫ c) ≫ r = ((a ≫ b) ≫ c) ≫ r := by
  simp only [Category.assoc]

section Generic

variable {P₁ Q₁ : AlgebraicSpaces B S hS}

/-- The transpose along `e^* ⊣ e_*`, on underlying sheaves of sets: the unit followed by the
direct image. -/
theorem moduleSheafFunctor_map_homEquiv_modulePullbackAdjunction_generic (e : P₁ ⟶ Q₁)
    (M : Modules.{u, u} B S hS Q₁.1 Q₁.2) (N : Modules.{u, u} B S hS P₁.1 P₁.2)
    (φ : (modulePullback B S hS e).obj M ⟶ N) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Q₁)).map
        ((modulePullbackAdjunction B S hS e).homEquiv M N φ) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Q₁)).map
          ((modulePullbackAdjunction B S hS e).unit.app M) ≫
        (smallEtaleRingedToposHom B S hS e).toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS P₁)).map φ) := by
  rw [Adjunction.homEquiv_unit]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Generic

section Mate

variable {U₁ X₁ Y₁ : AlgebraicSpaces B S hS}

omit hZ in
/-- **The composition law for inverse images is the mate of that for direct images**, on
transposes: transposing along `f⁻¹ ⊣ f_*` and `p⁻¹ ⊣ p_*` a map out of `p⁻¹f⁻¹A` read through
`p⁻¹f⁻¹ ≅ (p ≫ f)⁻¹` is transposing along `(p ≫ f)⁻¹ ⊣ (p ≫ f)_*` and comparing the direct
images. -/
theorem homEquiv_homEquiv_compInverseImageIso_hom_app (p : U₁ ⟶ X₁) (f : X₁ ⟶ Y₁)
    {A : Sheaf (SmallEtale.topology B S hS Y₁.1) (Type u)}
    {T : Sheaf (SmallEtale.topology B S hS U₁.1) (Type u)}
    (φ : (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.inverseImage.obj A ⟶ T) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom B S hS p).toToposHom.adj.homEquiv _ _
          ((smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom.app A ≫ φ)) =
      (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.adj.homEquiv _ _ φ ≫
        (smallToposMorphismTypeU_comp B S hS p f).inv.app T := by
  have h1 := ((((smallEtaleRingedToposHom B S hS f).toToposHom.comp
      (smallEtaleRingedToposHom B S hS p).toToposHom).adj.ofNatIsoRight
        (smallToposMorphismTypeU_comp B S hS p f)).homEquiv_naturality_right
      ((smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom.app A) φ).trans
    (congrArg (· ≫ _) (Adjunction.homEquiv_leftAdjointUniq_hom_app _
      (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.adj A))
  have h2 := Adjunction.homEquiv_ofNatIsoRight_apply (((smallEtaleRingedToposHom B S hS
      f).toToposHom.comp
      (smallEtaleRingedToposHom B S hS p).toToposHom).adj)
    (smallToposMorphismTypeU_comp B S hS p f)
    ((smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom.app A ≫ φ)
  have h3 := h2.symm.trans (h1.trans (Adjunction.homEquiv_unit _ _ _ _).symm)
  simp only [MorphismOfTopoi.comp, Adjunction.comp_homEquiv, Equiv.trans_apply] at h3
  exact (Iso.eq_comp_inv ((smallToposMorphismTypeU_comp B S hS p f).app T)).2 h3

omit hZ in
/-- The inverse form of `homEquiv_homEquiv_compInverseImageIso_hom_app`: transposing a map out of
`(p ≫ f)⁻¹A` read through `(p ≫ f)⁻¹ ≅ p⁻¹f⁻¹`. -/
theorem homEquiv_compInverseImageIso_inv_app (p : U₁ ⟶ X₁) (f : X₁ ⟶ Y₁)
    {A : Sheaf (SmallEtale.topology B S hS Y₁.1) (Type u)}
    {T : Sheaf (SmallEtale.topology B S hS U₁.1) (Type u)}
    (ψ : (smallEtaleRingedToposHom B S hS p).toToposHom.inverseImage.obj
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj A) ⟶ T) :
    (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom_compInverseImageIso B S hS p f).inv.app A ≫ ψ) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
          ((smallEtaleRingedToposHom B S hS p).toToposHom.adj.homEquiv _ _ ψ) ≫
        (smallToposMorphismTypeU_comp B S hS p f).hom.app T :=
  (Iso.comp_inv_eq ((smallToposMorphismTypeU_comp B S hS p f).app T)).1
    ((homEquiv_homEquiv_compInverseImageIso_hom_app p f
      ((smallEtaleRingedToposHom_compInverseImageIso B S hS p f).inv.app A ≫ ψ)).symm.trans
      (congrArg (fun x ↦ (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom B S hS p).toToposHom.adj.homEquiv _ _ x))
        (Iso.hom_inv_id_app_assoc (smallEtaleRingedToposHom_compInverseImageIso B S hS p f) A ψ)))

omit hZ in
/-- Transposing along `m₂⁻¹ ⊣ m₂_*` a map out of `m₂⁻¹𝒪` read through `m₁ = m₂`. -/
theorem homEquiv_forgetRing_eqToIso_inv {m₁ m₂ : U₁ ⟶ X₁} (h : m₁ = m₂)
    {T : Sheaf (SmallEtale.topology B S hS U₁.1) (Type u)}
    (ψ : (smallEtaleRingedTopos B S hS U₁).forgetRing.obj
      (inverseImageStructureSheaf B S hS m₁) ⟶ T) :
    (smallEtaleRingedToposHom B S hS m₂).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedTopos B S hS U₁).forgetRing.map
          (eqToIso (congrArg (inverseImageStructureSheaf B S hS) h)).inv ≫ ψ) =
      (smallEtaleRingedToposHom B S hS m₁).toToposHom.adj.homEquiv _ _ ψ ≫
        eqToHom (congrArg (fun m ↦ (smallToposMorphismTypeU B S hS m).pushforward.obj T) h) := by
  subst h
  simp only [eqToIso_refl, Iso.refl_inv, CategoryTheory.Functor.map_id, eqToHom_refl,
    Category.comp_id]
  exact congrArg _ (Category.id_comp ψ)

omit hZ in
/-- Transposing the inverse image of a map is following it by the unit. -/
theorem homEquiv_inverseImage_map (p : U₁ ⟶ X₁)
    {A A' : Sheaf (SmallEtale.topology B S hS X₁.1) (Type u)} (a : A ⟶ A') :
    (smallEtaleRingedToposHom B S hS p).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom B S hS p).toToposHom.inverseImage.map a) =
      a ≫ (smallEtaleRingedToposHom B S hS p).toToposHom.adj.unit.app A' := by
  rw [Adjunction.homEquiv_unit]
  exact ((smallEtaleRingedToposHom B S hS p).toToposHom.adj.unit.naturality a).symm

end Mate

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_IdealCompatibility
    (W : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS W).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of sheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_sheaf_IdealCompatibility
    (W : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) (Sheaf (smallEtaleRingedTopos B S hS W).J (Type u)) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (smallEtaleRingedTopos B S hS W).J (Type u))

omit hZ₂ in
/-- The `𝒜`-algebra structure read through `θ`, on underlying sheaves of sets: the composition
law for `e₀ ≫ t`, the square, and the composition law for `i₂ ≫ g` followed by the inverse image
along `i₂` of `g^♯`. -/
theorem forgetRing_map_squareBaseIso_inv_comp :
    (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
        hS)).forgetRing.map
        ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
          inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS e₀ (subspaceInclusion B S hS Y'
          Z)).hom.app
          ((smallEtaleRingedTopos B S hS Y').forgetRing.obj (smallEtaleRingedTopos B S hS Y').O) ≫
        (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
            hS)).forgetRing.map
          (eqToIso (congrArg (inverseImageStructureSheaf B S hS) hsq)).inv ≫
        (smallEtaleRingedToposHom_compInverseImageIso B S hS
            (subspaceInclusion B S hS X' Z₂) g).inv.app
          ((smallEtaleRingedTopos B S hS Y').forgetRing.obj (smallEtaleRingedTopos B S hS Y').O) ≫
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X'
            Z₂)).toToposHom.inverseImage.map
          ((smallEtaleRingedTopos B S hS X').forgetRing.map
            (smallEtaleRingedToposHom B S hS g).fSharpInverseImage) := by
  refine ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
      hS)).forgetRing.map_comp _ _).trans ?_
  refine (congrArg₂ (· ≫ ·)
    (((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
        hS)).forgetRing.map_comp
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS e₀ (subspaceInclusion B S hS Y'
          Z)).hom.app
        (smallEtaleRingedTopos B S hS Y').O)
      (eqToIso (congrArg (inverseImageStructureSheaf B S hS) hsq)).inv).trans
      (congrArg (· ≫ _) (forget_map_compInverseImageRingIso_hom B S hS e₀ (subspaceInclusion B S hS
          Y' Z))))
    (((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
        hS)).forgetRing.map_comp _ _).trans
      (congrArg₂ (· ≫ ·)
        (forget_map_compInverseImageRingIso_inv B S hS (subspaceInclusion B S hS X' Z₂) g)
        (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
          (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS)).J
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X' Z₂)).toToposHom.inverseImage
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage)))).trans ?_
  exact Category.assoc _ _ _

omit hZ₂ in
/-- **The double transpose of the `𝒜`-algebra structure read through `θ`**, along `e₀⁻¹ ⊣ e₀_*`
and `t⁻¹ ⊣ t_*`: it is `g^♯ : 𝒪_{Y'} ⟶ g_*𝒪_{X'}` followed by the direct image of the unit of
`i₂⁻¹ ⊣ i₂_*` and the comparisons of iterated direct images along the square. -/
theorem homEquiv_homEquiv_forgetRing_squareBaseIso_inv_comp :
    (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y' Z)).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.map
            ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
              inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g))) =
      ((((sheafCompose (SmallEtale.topology B S hS Y'.1) (forget CommRingCat.{u})).map
          (smallEtaleRingedToposHom B S hS g).fSharp ≫
        (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
          ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X'
              Z₂)).toToposHom.adj.unit.app
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
                X').O).ringSheaf)) ≫
        (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X' Z₂) g).hom.app
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))) ≫
        eqToHom (congrArg (fun m ↦ (smallToposMorphismTypeU B S hS m).pushforward.obj
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))) hsq)) ≫
        (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS Y' Z)).inv.app _ := by
  refine (congrArg (fun x ↦ (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y'
      Z)).toToposHom.adj.homEquiv _ _
    ((smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _ x))
    (forgetRing_map_squareBaseIso_inv_comp hZ Z₂ g e₀ hsq)).trans ?_
  refine (homEquiv_homEquiv_compInverseImageIso_hom_app e₀ (subspaceInclusion B S hS Y' Z)
      _).trans ?_
  refine (congrArg (· ≫ _) (homEquiv_forgetRing_eqToIso_inv hsq _)).trans ?_
  refine (congrArg (fun x ↦ (x ≫ _) ≫ _)
    (homEquiv_compInverseImageIso_inv_app (subspaceInclusion B S hS X' Z₂) g _)).trans ?_
  refine (congrArg (fun x ↦ (((smallEtaleRingedToposHom B S hS g).toToposHom.adj.homEquiv _ _ x ≫
    _) ≫ _) ≫ _) (homEquiv_inverseImage_map (subspaceInclusion B S hS X' Z₂) _)).trans ?_
  refine (congrArg (fun x ↦ ((x ≫ _) ≫ _) ≫ _)
    ((smallEtaleRingedToposHom B S hS g).toToposHom.adj.homEquiv_naturality_right _ _)).trans ?_
  refine (congrArg (fun x ↦ (((x ≫ _) ≫ _) ≫ _) ≫ _)
    ((congrArg _ (MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget
      (smallEtaleRingedToposHom B S hS g).toToposHom _ _
      (smallEtaleRingedToposHom B S hS g).fSharp)).trans (Equiv.apply_symm_apply _ _))).trans ?_
  rfl

omit hZ in
/-- The transpose along `t⁻¹ ⊣ t_*` of the restricted comorphism of the square, on underlying
sheaves of sets: the comorphism of `g` read in the direct image along `e₀ ≫ t`, compared with
the iterated direct image. -/
theorem homEquiv_forget_map_restrictedSharpThroughThickening :
    (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y' Z)).toToposHom.adj.homEquiv _ _
        ((sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor) (forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z g e₀ hsq)) =
      (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (structureSharpThroughThickeningAt B S hS Z₂ g (e₀ ≫ (subspaceInclusion B S hS Y' Z)) hsq ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS Y' Z)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))) :=
  (Stacks.Sheaves.ToposPushforward.ringSheafMap_ringImageAdjunction_homEquiv _ _ _ _).symm.trans
    (congrArg _ (Equiv.apply_symm_apply _ _))

omit hZ in
/-- `homEquiv_forget_map_restrictedSharpThroughThickening` with the objects of the adjunction
written as the underlying sheaves of sets of the ringed topoi. -/
theorem homEquiv_forget_map_restrictedSharpThroughThickening_forgetRing :
    (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y' Z)).toToposHom.adj.homEquiv
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y').O).ringSheaf
        ((smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.obj
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂))))
        ((sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor) (forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z g e₀ hsq)) =
      (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (structureSharpThroughThickeningAt B S hS Z₂ g (e₀ ≫ (subspaceInclusion B S hS Y' Z)) hsq ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS Y' Z)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))) :=
  homEquiv_forget_map_restrictedSharpThroughThickening Z₂ g e₀ hsq

omit hZ in
/-- The comorphism of `g`, on underlying sheaves of sets. -/
theorem forget_map_structureSharp_eq :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (structureSharp B S hS g) =
      (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS g).fSharp := by
  rw [← map_structureSharpCommRing]
  rfl

omit hZ in
/-- The direct image of the unit of `i₂⁻¹ ⊣ i₂_*` read in `(i₂ ≫ g)_*`, on underlying sheaves of
sets. -/
theorem forget_map_pushforward_ringUnit_comp :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS g)).map
            (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' Z₂))
              (structureRingSheaf B S hS X')) ≫
          (Stacks.Sheaves.ToposPullback.pullbackRingSheafComp (SmallEtale.topology B S hS X'.1)
              (SmallEtale.topology B S hS Y'.1)
              (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' Z₂)).pushforward
              (smallToposMorphismTypeU B S hS g).pushforward
              (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))).hom ≫
          Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans
            (SmallEtale.topology B S hS Y'.1)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))
            (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X' Z₂) g).hom) =
      (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
          ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X'
              Z₂)).toToposHom.adj.unit.app
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
                X').O).ringSheaf) ≫
        (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X' Z₂) g).hom.app
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂))) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit hZ in
/-- The comparison `(e₀ ≫ t)_* ⟶ t_*e₀_*` of iterated direct images of rings, on underlying
sheaves of sets. -/
theorem forget_map_pushforwardRingSheafCompInv_eq :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans
            (SmallEtale.topology B S hS Y'.obj)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))
            (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS Y' Z)).inv ≫
          (Stacks.Sheaves.ToposPullback.pullbackRingSheafComp
            (SmallEtale.topology B S hS Z.1.toFunctor)
            (SmallEtale.topology B S hS Y'.obj) (smallToposMorphismTypeU B S hS e₀).pushforward
            (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS Y' Z)).pushforward
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))).inv) =
      (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS Y' Z)).inv.app
        ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
            hS)).forgetRing.obj
          (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂))) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit hZ in
/-- The comorphism of `g` read in the direct image along `e₀ ≫ t`, compared with the iterated
direct image, on underlying sheaves of sets. -/
theorem forget_map_structureSharpThroughThickeningAt_comp :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (structureSharpThroughThickeningAt B S hS Z₂ g (e₀ ≫ (subspaceInclusion B S hS Y' Z)) hsq ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS Y' Z)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' Z₂))) =
      ((((sheafCompose (SmallEtale.topology B S hS Y'.1) (forget CommRingCat.{u})).map
          (smallEtaleRingedToposHom B S hS g).fSharp ≫
        (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
          ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X'
              Z₂)).toToposHom.adj.unit.app
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
                X').O).ringSheaf)) ≫
        (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X' Z₂) g).hom.app
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))) ≫
        eqToHom (congrArg (fun m ↦ (smallToposMorphismTypeU B S hS m).pushforward.obj
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))) hsq)) ≫
        (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS Y' Z)).inv.app _ := by
  simp only [structureSharpThroughThickeningAt, structureSharpThroughThickening_eq,
    pushforwardRingSheafCompInv, Functor.map_comp,
    Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans,
    Stacks.Sheaves.ToposPullback.sheafCompose_map_pullbackRingSheafComp_hom,
    Stacks.Sheaves.ToposPullback.sheafCompose_map_pullbackRingSheafComp_inv, eqToHom_map,
    Category.id_comp, Category.comp_id, Category.assoc]
  refine (congrArg₂ (· ≫ ·) (forget_map_structureSharp_eq g)
    (congrArg₂ (· ≫ ·) (forget_map_pushforward_ringUnit_comp Z₂ g)
      (congrArg (_ ≫ ·) (forget_map_pushforwardRingSheafCompInv_eq Z₂ e₀)))).trans ?_
  simp only [Category.assoc]
  exact comp_comp_comp_eq_comp_comp_comp _ _ _ _

omit hZ₂ in
/-- **The transpose of the `𝒜`-algebra structure read through `θ` is the restricted comorphism of
the square**, on underlying sheaves of sets: transposing
`e₀⁻¹t⁻¹𝒪_{Y'} ≅ (i₂ ≫ g)⁻¹𝒪_{Y'} ⟶ i₂⁻¹𝒪_{X'}` along `e₀⁻¹ ⊣ e₀_*` gives the comorphism
`t⁻¹𝒪_{Y'} ⟶ e₀_*(i₂⁻¹𝒪_{X'})` of `AlgebraicGeometry.Space.restrictedSharpThroughThickening`. -/
theorem homEquiv_forgetRing_squareBaseIso_inv_comp :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
            hS)).forgetRing.map
          ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
            inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g)) =
      (sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor) (forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z₂ Z g e₀ hsq) :=
  ((smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS Y' Z)).toToposHom.adj.homEquiv _
      _).injective
    ((homEquiv_homEquiv_forgetRing_squareBaseIso_inv_comp hZ Z₂ g e₀ hsq).trans
      ((forget_map_structureSharpThroughThickeningAt_comp Z₂ g e₀ hsq).symm.trans
        (homEquiv_forget_map_restrictedSharpThroughThickening_forgetRing Z₂ g e₀ hsq).symm))

/-- The kernel inclusion of the extension of the thickening `Z ⊂ Y'`, on underlying sheaves of
sets, is the conormal inclusion `𝒞_{Z/Y'} ⟶ t⁻¹𝒪_{Y'}`. -/
theorem inclSheafSets_baseExtension :
    (baseExtension hZ).inclSheafSets = conormalSetInclusion B S hS Z hZ := by
  rw [← moduleSheafFunctor_map_conormalInverseImageι B S hS Z hZ]
  exact Sheaf.hom_ext_sections fun _ m ↦ firstOrderAlgebraExtension_incl Z hZ (𝟙 Y') m

omit hZ₂ in
/-- The prescribed map of the problem is the change-of-rings half of the unit of the pullback
adjunction, on underlying sheaves of sets. -/
theorem problemCSets_eq_pullbackScalarUnit :
    problemCSets hZ Z₂ e₀ =
      Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit
        (smallEtaleRingedToposHom B S hS e₀) (conormalModule B S hS Y' Z) := by
  refine Sheaf.hom_ext_sections fun _ _ ↦ ?_
  rfl

omit hZ₂ in
/-- `homEquiv_forgetRing_squareBaseIso_inv_comp` with the objects of the adjunction written as
the target of the kernel inclusion of the base extension. -/
theorem homEquiv_forgetRing_squareBaseIso_inv_comp_baseExtension :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (baseExtension hZ).extension))
        ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
            hS)).forgetRing.obj
          (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))
        ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
            hS)).forgetRing.map
          ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
            inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g)) =
      (sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor) (forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z₂ Z g e₀ hsq) :=
  homEquiv_forgetRing_squareBaseIso_inv_comp hZ Z₂ g e₀ hsq

omit hZ₂ in
/-- Naturality of the transpose along `e₀⁻¹ ⊣ e₀_*` at the kernel inclusion of the base
extension. -/
theorem homEquiv_idealImageSets_naturality :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom B S hS e₀).toToposHom.inverseImage.map
            (baseExtension hZ).inclSheafSets ≫
          (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.map
            ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
              inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g)) =
      (baseExtension hZ).inclSheafSets ≫
        (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (baseExtension hZ).extension))
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.obj
            (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))
          ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.map
            ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
              inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g)) :=
  (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv_naturality_left _ _

omit hZ₂ in
/-- **The transpose of the ideal-image map**: the image `x ↦ (θ⁻¹ ≫ alg)(x)` of the base ideal
`e₀⁻¹𝒞_{Z/Y'}` in `i₂⁻¹𝒪_{X'}`, transposed along `e₀⁻¹ ⊣ e₀_*`, is the conormal inclusion of
`Z ⊂ Y'` followed by the restricted comorphism of the square. -/
theorem homEquiv_idealImageSets :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _
        ((smallEtaleRingedToposHom B S hS e₀).toToposHom.inverseImage.map
            (baseExtension hZ).inclSheafSets ≫
          (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
              hS)).forgetRing.map
            ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
              inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g)) =
      conormalSetInclusion B S hS Z hZ ≫
        (sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor) (forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z g e₀ hsq) :=
  (homEquiv_idealImageSets_naturality hZ Z₂ g e₀ hsq).trans
    ((congrArg (_ ≫ ·) (homEquiv_forgetRing_squareBaseIso_inv_comp_baseExtension hZ Z₂ g e₀
      hsq)).trans (congrArg (· ≫ _) (inclSheafSets_baseExtension hZ)))

omit hZ in
/-- The direct image along `e₀` of a morphism of `𝒪_{Z₂}`-modules, on underlying sheaves of
sets. -/
theorem moduleSheafFunctor_map_modulePushforward_map
    {N N' : Modules.{u, u} B S hS Z₂.1.toFunctor Z₂.2.1} (φ : N ⟶ N') :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B
        S hS))).map
        ((modulePushforward B S hS e₀).map φ) =
      (smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
            AlgebraicSpaces B S hS))).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit hZ₂ in
/-- Naturality of the transpose along `e₀⁻¹ ⊣ e₀_*` at the target of the prescribed map. -/
theorem homEquiv_problemCSets_comp
    {T : Sheaf (SmallEtale.topology B S hS Z₂.1.toFunctor) (Type u)}
    (ν : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
        AlgebraicSpaces B S hS))).obj
      ((modulePullback B S hS e₀).obj (conormalModule B S hS Y' Z)) ⟶ T) :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _ (problemCSets hZ Z₂ e₀ ≫ ν) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces
          B S hS))).map
          ((modulePullbackAdjunction B S hS e₀).unit.app (conormalModule B S hS Y' Z)) ≫
        (smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map ν :=
  ((smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv_naturality_right
      (problemCSets hZ Z₂ e₀) ν).trans
    (congrArg (· ≫ _) ((congrArg ((smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _)
      (problemCSets_eq_pullbackScalarUnit hZ Z₂ e₀)).trans
      (moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_homEquiv B S hS e₀
        (conormalModule B S hS Y' Z)).symm))

omit hZ in
/-- The transpose along `e₀^* ⊣ e₀_*`, on underlying sheaves of sets: the unit followed by the
direct image. -/
theorem moduleSheafFunctor_map_homEquiv_modulePullbackAdjunction
    (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1) (N : Modules.{u, u} B S hS Z₂.1.toFunctor
        Z₂.2.1)
    (φ : (modulePullback B S hS e₀).obj M ⟶ N) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B
        S hS))).map
        ((modulePullbackAdjunction B S hS e₀).homEquiv M N φ) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces
          B S hS))).map
          ((modulePullbackAdjunction B S hS e₀).unit.app M) ≫
        (smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
              AlgebraicSpaces B S hS))).map φ) :=
  moduleSheafFunctor_map_homEquiv_modulePullbackAdjunction_generic e₀ M N φ

/-- **The transpose of the conormal-map side**: `c` followed by the conormal map and the conormal
inclusion of `Z₂ ⊂ X'`, transposed along `e₀⁻¹ ⊣ e₀_*`, is the transpose of the conormal map
followed by the direct image of the conormal inclusion. -/
theorem homEquiv_conormalSideSets :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv _ _
        (problemCSets hZ Z₂ e₀ ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
              AlgebraicSpaces B S hS))).map
            (conormalMap B S hS Z₂ Z g e₀ hsq) ≫ conormalSetInclusion B S hS Z₂ hZ₂) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces
          B S hS))).map
          ((modulePullbackAdjunction B S hS e₀).homEquiv _ _ (conormalMap B S hS Z₂ Z g e₀ hsq)) ≫
        (smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map
          (conormalSetInclusion B S hS Z₂ hZ₂) := by
  refine (homEquiv_problemCSets_comp hZ Z₂ e₀
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
        AlgebraicSpaces B S hS))).map
      (conormalMap B S hS Z₂ Z g e₀ hsq) ≫ conormalSetInclusion B S hS Z₂ hZ₂)).trans ?_
  exact (congrArg (_ ≫ ·) ((smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map_comp
      _ _)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (moduleSheafFunctor_map_homEquiv_modulePullbackAdjunction Z₂ e₀ _ _
          (conormalMap B S hS Z₂ Z g e₀ hsq)).symm))

/-- `homEquiv_conormalSideSets` with the objects of the adjunction written as those of the
ideal-image side. -/
theorem homEquiv_conormalSideSets_baseExtension :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv
        ((Stacks.SheafOfModules.Tensor.ringSheaf (baseExtension hZ).extension).moduleSheaf
          ((SheafOfModules.restrictScalars
            ((sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor)
              (forget₂ CommRingCat.{u} RingCat.{u})).map (baseExtension hZ).reduction)).obj
            (conormalModule B S hS Y' Z)))
        ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
            hS)).forgetRing.obj
          (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))
        (problemCSets hZ Z₂ e₀ ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
              AlgebraicSpaces B S hS))).map
            (conormalMap B S hS Z₂ Z g e₀ hsq) ≫ conormalSetInclusion B S hS Z₂ hZ₂) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces
          B S hS))).map
          ((modulePullbackAdjunction B S hS e₀).homEquiv (conormalModule B S hS Y' Z)
            (conormalModule B S hS X' Z₂) (conormalMap B S hS Z₂ Z g e₀ hsq)) ≫
        (smallEtaleRingedToposHom B S hS e₀).toToposHom.pushforward.map
          (conormalSetInclusion B S hS Z₂ hZ₂) :=
  homEquiv_conormalSideSets hZ Z₂ hZ₂ g e₀ hsq


/-- **The ideal image is `c` followed by the conormal map**, as morphisms of sheaves of sets on
the small étale site of `Z₂`: the image `(θ⁻¹ ≫ alg)(x)` in `i₂⁻¹𝒪_{X'}` of a section `x` of the
base ideal `e₀⁻¹𝒞_{Z/Y'}` is the conormal inclusion of the image of `c(x)` under the conormal map.
Both sides are compared after transposing along `e₀⁻¹ ⊣ e₀_*`, where this is
`AlgebraicGeometry.Space.conormalSetInclusion_restriction_conormalModule`. -/
theorem idealImageSets_eq :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.inverseImage.map
        (baseExtension hZ).inclSheafSets ≫
      (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
          hS)).forgetRing.map
        ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
          inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X' Z₂) g) =
    problemCSets hZ Z₂ e₀ ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
          AlgebraicSpaces B S hS))).map
        (conormalMap B S hS Z₂ Z g e₀ hsq) ≫ conormalSetInclusion B S hS Z₂ hZ₂ :=
  ((smallEtaleRingedToposHom B S hS e₀).toToposHom.adj.homEquiv
      ((Stacks.SheafOfModules.Tensor.ringSheaf (baseExtension hZ).extension).moduleSheaf
        ((SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS Z.1.toFunctor)
            (forget₂ CommRingCat.{u} RingCat.{u})).map (baseExtension hZ).reduction)).obj
          (conormalModule B S hS Y' Z)))
      ((smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
          hS)).forgetRing.obj
        (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X' Z₂)))).injective
    ((homEquiv_idealImageSets hZ Z₂ g e₀ hsq).trans
      ((conormalSetInclusion_restriction_conormalModule_smallEtale Z₂ g e₀ hsq hZ₂ hZ).symm.trans
        (homEquiv_conormalSideSets_baseExtension hZ Z₂ hZ₂ g e₀ hsq).symm))

/-- `idealImageSets_eq` with the algebra map written as that of the first-order algebra
extension of `Z₂ ⊂ X'`. -/
theorem idealImageSets_eq_firstOrderAlgebraMap :
    (smallEtaleRingedToposHom B S hS e₀).toToposHom.inverseImage.map
        (baseExtension hZ).inclSheafSets ≫
      (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
          hS)).forgetRing.map
        ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫
          (firstOrderAlgebraExtension B S hS Z₂ hZ₂ g).algebraMap) =
    problemCSets hZ Z₂ e₀ ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ :
          AlgebraicSpaces B S hS))).map
        (conormalMap B S hS Z₂ Z g e₀ hsq) ≫ conormalSetInclusion B S hS Z₂ hZ₂ :=
  (congrArg (fun φ ↦ (smallEtaleRingedToposHom B S hS e₀).toToposHom.inverseImage.map
        (baseExtension hZ).inclSheafSets ≫
      (smallEtaleRingedTopos B S hS (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S
          hS)).forgetRing.map
        ((squareBaseIso hZ Z₂ g e₀ hsq).inv ≫ φ))
    (firstOrderAlgebraExtension_algebraMap B S hS Z₂ hZ₂ g)).trans
    (idealImageSets_eq hZ Z₂ hZ₂ g e₀ hsq)

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
