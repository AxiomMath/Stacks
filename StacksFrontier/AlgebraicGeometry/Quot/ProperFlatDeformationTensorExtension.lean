module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationIdealSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePreimageSections

/-!
# The extension of a deformation with ideal `𝒪_Z ⊗_{R} I`

Let `X' ⟶ Spec A` be a deformation of `x₀ = (X₀ ⟶ Spec k)` over an algebra `A` of `𝒞_Λ` whose
residue kernel `I = 𝔪_A` squares to zero, and let `Z = X' ×_{Spec A} Spec k ⊆ X'` be its closed
fibre. By flatness of `X' ⟶ Spec A`, the conormal module of `Z ⊆ X'` is `𝒪_Z ⊗_R I`,
`R = Γ(Spec k)` (`AlgebraicGeometry.Space.conormalModulePreimageSquareZeroIso`), and its sections
`1 ⊗ a` are the classes of the functions `a ∈ I` pulled back to `X'`. This file reads the
extension `𝒪_{X'}|_Z` of `𝒪_Z` with its ideal so identified, restricts it to `X₀ ≅ Z`, and
identifies the ideal there with `𝒪_{X₀} ⊗_k 𝔪_A`: the extension whose class is the class of the
deformation in the proof of [Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.deformationTensorIdealIso`: `𝒞_{Z/X'} ≅ 𝒪_Z ⊗_R I`.
* `AlgebraicGeometry.Space.deformationTensorAlgebraExtension`: the extension of `𝒪_Z` by
  `𝒪_Z ⊗_R I`.
* `AlgebraicGeometry.Space.deformationTensorBaseExtension`: its restriction to `X₀`.
* `AlgebraicGeometry.Space.deformationTensorLinearIdealIso`: the ideal of the restriction is
  `𝒪_{X₀} ⊗_k 𝔪_A`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory

/-- A morphism read through the inverse of a composite of five isomorphisms, one isomorphism at
a time. Stated for abstract isomorphisms so that concrete instances are checked factor by
factor. -/
theorem comp_trans_trans_trans_trans_inv {C : Type*} [Category C] {U P₀ P₁ P₂ P₃ P₄ P₅ : C}
    (a : P₀ ≅ P₁) (b : P₁ ≅ P₂) (c : P₂ ≅ P₃) (d : P₃ ≅ P₄) (e : P₄ ≅ P₅) (σ₅ : U ⟶ P₅)
    (σ₄ : U ⟶ P₄) (σ₃ : U ⟶ P₃) (σ₂ : U ⟶ P₂) (σ₁ : U ⟶ P₁) (σ₀ : U ⟶ P₀)
    (h₅ : σ₅ ≫ e.inv = σ₄) (h₄ : σ₄ ≫ d.inv = σ₃) (h₃ : σ₃ ≫ c.inv = σ₂) (h₂ : σ₂ ≫ b.inv = σ₁)
    (h₁ : σ₁ ≫ a.inv = σ₀) (E : P₀ ≅ P₅) (hE : E = a ≪≫ b ≪≫ c ≪≫ d ≪≫ e) :
    σ₅ ≫ E.inv = σ₀ := by
  subst h₅ h₄ h₃ h₂ h₁ hE
  simp

end CategoryTheory

namespace Deformation.AlgebraExtension

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **The inclusion of the kernel of an extension built from an inclusion `ι`** is `ι`, on
sections. -/
theorem incl_ofKernelInclusion (E : Sheaf J CommRingCat.{u}) (r : E ⟶ O)
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
    (ofKernelInclusion E r hr α hα r' hr' ι hzero hexists hinj hsq).incl m =
      (ι.val.app U m : E.obj.obj U) := by
  subst hr'
  rfl

/-- The inclusion of the kernel of a transported extension is the original inclusion, on the
transported section. -/
theorem incl_transportKernel {N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
    (P : AlgebraExtension a M) (e : M ≅ N) {U : Cᵒᵖ} (n : N.val.obj U) :
    (P.transportKernel e).incl n = P.incl (e.inv.val.app U n) :=
  rfl

end Deformation.AlgebraExtension

namespace AlgebraicGeometry.Space

/-- **The inclusion of the kernel of the extension of a first-order thickening** is the inclusion
`𝒞_{Z/X} ⟶ i⁻¹𝒪_X` of `AlgebraicGeometry.Space.conormalInverseImageι`, on sections. -/
theorem firstOrderAlgebraExtension_incl (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (g : X ⟶ Y)
    {U : (SmallEtale B S hS Z.1.toFunctor)ᵒᵖ}
    (m : (conormalModule B S hS X Z).val.obj U) :
    (firstOrderAlgebraExtension B S hS Z hZ g).incl m =
      (show ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z)).obj.obj U) from
        (conormalInverseImageι B S hS Z hZ).val.app U m) := by
  unfold firstOrderAlgebraExtension
  exact Deformation.AlgebraExtension.incl_ofKernelInclusion.{u, u + 1, u}
    (J := SmallEtale.topology B S hS Z.1.toFunctor) _ _ _ _ _ _ _ _ _ _ _ _ _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

/-- The closed fibre `Z = X' ×_{Spec A} Spec k` of a deformation, as an algebraic space. -/
abbrev deformationFibreSpace : AlgebraicSpaces B S hS :=
  ⟨(deformationThickening B S hS x hsq).1.toFunctor, (deformationThickening B S hS x hsq).2.1⟩

/-- The projection `Z ⟶ Spec k` of the closed fibre of a deformation, read on the base of `x₀`. -/
abbrev deformationFibreBaseProjection :
    deformationFibreSpace B S hS x hsq ⟶
      schemeSpace ((cartesianProperFlatProjection B S hS).obj y₀) :=
  preimageRangeProjection B S hS (deformationStructureMap B S hS x)
    (deformationBaseImmersion B S hS x) (isClosedImmersion_deformationBaseImmersion B S hS x hsq)

/-- The `Γ(Spec k)`-module `I = Ker(Γ(Spec A) ⟶ Γ(Spec k))` of a deformation, `I² = 0`. -/
abbrev deformationBaseKernel :
    ModuleCat.{u} (baseRing B S hS ((cartesianProperFlatProjection B S hS).obj y₀)) :=
  RingHom.squareZeroKer _ (deformationBaseImmersion_Γ_surjective B S hS x)
    (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)

/-- **The conormal module of the closed fibre of a deformation is `𝒪_Z ⊗_R I`**, `R = Γ(Spec k)`,
`I = Ker(Γ(Spec A) ⟶ R)`, by flatness of `X' ⟶ Spec A` (the flat clause of Stacks 04CQ). -/
def deformationTensorIdealIso :
    conormalModule B S hS (deformationSpace B S hS x) (deformationThickening B S hS x hsq) ≅
      (baseRingTensorModule B S hS (deformationFibreSpace B S hS x hsq)
        (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))).obj
        (deformationBaseKernel B S hS x hsq) :=
  conormalModulePreimageSquareZeroIso B S hS (deformationStructureMap B S hS x)
    (deformationBaseImmersion B S hS x) (isClosedImmersion_deformationBaseImmersion B S hS x hsq)
    (isFlat_deformationStructureMap B S hS x) (isAffine_deformationBase B S hS x)
    (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)

/-- **The extension of a deformation, with ideal `𝒪_Z ⊗_R I`.** The extension of the first-order
thickening `Z ⊆ X'` (`AlgebraicGeometry.Space.firstOrderAlgebraExtension`), for any `g : X' ⟶ Y`,
with its ideal read through `AlgebraicGeometry.Space.deformationTensorIdealIso`. -/
def deformationTensorAlgebraExtension {Y : AlgebraicSpaces B S hS}
    (g : deformationSpace B S hS x ⟶ Y) :
    Deformation.AlgebraExtension
      (J := SmallEtale.topology B S hS (deformationThickening B S hS x hsq).1.toFunctor)
      (structureSharpInverseImage B S hS
        (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq) ≫ g))
      ((baseRingTensorModule B S hS (deformationFibreSpace B S hS x hsq)
        (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))).obj
        (deformationBaseKernel B S hS x hsq)) :=
  (firstOrderAlgebraExtension B S hS (deformationThickening B S hS x hsq)
      (isFirstOrderThickening_deformationThickening B S hS x hsq) g).transportKernel
    (deformationTensorIdealIso B S hS x hsq)

/-- **The sections `1 ⊗ a` of `𝒪_Z ⊗_R I` are the classes of the functions `a`**: read through
`AlgebraicGeometry.Space.deformationTensorIdealIso`, the section `1 ⊗ a` is the pullback to the
closed fibre `Z` of the section `g^♯a` of the ideal of `Z ⊆ X'`, `g : X' ⟶ Spec A` the structure
morphism. -/
theorem baseRingTensorSection_deformationTensorIdealIso_inv
    (a : deformationBaseKernel B S hS x hsq) :
    baseRingTensorSection B S hS (deformationFibreSpace B S hS x hsq)
        (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))
        (deformationBaseKernel B S hS x hsq) a ≫
        (deformationTensorIdealIso B S hS x hsq).inv =
      modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS (deformationSpace B S hS x) (deformationThickening B S hS x hsq))
        (preimageIdealSection B S hS (deformationStructureMap B S hS x)
          (rangeSubspace B S hS (deformationBaseImmersion B S hS x)
            (isClosedImmersion_deformationBaseImmersion B S hS x hsq))
          ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B S hS (deformationBaseImmersion B S hS x)
            (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).symm ▸ a.2⟩) :=
  baseRingTensorSection_conormalModulePreimageSquareZeroIso_inv B S hS
    (deformationStructureMap B S hS x) (deformationBaseImmersion B S hS x)
    (isClosedImmersion_deformationBaseImmersion B S hS x hsq)
    (isFlat_deformationStructureMap B S hS x) (isAffine_deformationBase B S hS x)
    (deformationBaseImmersion_Γ_ker_sq B S hS x hsq) a

/-- The kernel inclusion of `AlgebraicGeometry.Space.deformationTensorAlgebraExtension` is that of
the first-order thickening, read through `AlgebraicGeometry.Space.deformationTensorIdealIso`. -/
theorem deformationTensorAlgebraExtension_kernelInclusion {Y : AlgebraicSpaces B S hS}
    (g : deformationSpace B S hS x ⟶ Y) :
    (deformationTensorAlgebraExtension B S hS x hsq g).kernelInclusion =
      (SheafOfModules.restrictScalars
        ((sheafCompose (SmallEtale.topology B S hS (deformationThickening B S hS x hsq).1.toFunctor)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
          (firstOrderAlgebraExtension B S hS (deformationThickening B S hS x hsq)
            (isFirstOrderThickening_deformationThickening B S hS x hsq) g).reduction)).map
          (deformationTensorIdealIso B S hS x hsq).inv ≫
        (firstOrderAlgebraExtension B S hS (deformationThickening B S hS x hsq)
          (isFirstOrderThickening_deformationThickening B S hS x hsq) g).kernelInclusion :=
  rfl

/-- **The kernel inclusion on the sections `1 ⊗ a`.** In the extension
`AlgebraicGeometry.Space.deformationTensorAlgebraExtension`, the section `1 ⊗ a` of the ideal
`𝒪_Z ⊗_R I` is included into `i⁻¹𝒪_{X'}` as the class of the function `g^♯a` of `X'`
(`g : X' ⟶ Spec A` the structure morphism), carried by the inclusion
`AlgebraicGeometry.Space.conormalInverseImageι` of the first-order thickening `Z ⊆ X'`. -/
theorem deformationTensorAlgebraExtension_incl_baseRingTensorSection
    {Y : AlgebraicSpaces B S hS} (g : deformationSpace B S hS x ⟶ Y)
    (a : deformationBaseKernel B S hS x hsq)
    {U : (SmallEtale B S hS (deformationThickening B S hS x hsq).1.toFunctor)ᵒᵖ} :
    (deformationTensorAlgebraExtension B S hS x hsq g).incl
        ((baseRingTensorSection B S hS (deformationFibreSpace B S hS x hsq)
          (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))
          (deformationBaseKernel B S hS x hsq) a).val.app U
          (1 : (structureRingSheaf B S hS (deformationFibreSpace B S hS x hsq)).obj.obj U)) =
      (conormalInverseImageι B S hS (deformationThickening B S hS x hsq)
          (isFirstOrderThickening_deformationThickening B S hS x hsq)).val.app U
        ((modulePullbackGlobalSection B S hS
          (subspaceInclusion B S hS (deformationSpace B S hS x)
            (deformationThickening B S hS x hsq))
          (preimageIdealSection B S hS (deformationStructureMap B S hS x)
            (rangeSubspace B S hS (deformationBaseImmersion B S hS x)
              (isClosedImmersion_deformationBaseImmersion B S hS x hsq))
            ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B S hS (deformationBaseImmersion B S hS x)
              (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).symm ▸ a.2⟩)).val.app U
          (1 : (structureRingSheaf B S hS (deformationFibreSpace B S hS x hsq)).obj.obj U)) := by
  have h := congrArg (fun t => t.val.app U
      (1 : (structureRingSheaf B S hS (deformationFibreSpace B S hS x hsq)).obj.obj U))
    (baseRingTensorSection_deformationTensorIdealIso_inv B S hS x hsq a)
  refine (firstOrderAlgebraExtension_incl B S hS (deformationThickening B S hS x hsq)
    (isFirstOrderThickening_deformationThickening B S hS x hsq) g _).trans ?_
  exact congrArg (fun m => (conormalInverseImageι B S hS (deformationThickening B S hS x hsq)
    (isFirstOrderThickening_deformationThickening B S hS x hsq)).val.app U m)
    ((SheafOfModules.comp_val_app_apply _ _ _ _).symm.trans h)

variable {x} (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr : (cartesianProperFlatProjection B S hS).map x.arrow ≫ r = 𝟙 _)

/-- **The extension of a deformation on the space it deforms, with ideal `𝒪_{X₀} ⊗_R I`.** The
restriction of `AlgebraicGeometry.Space.deformationTensorAlgebraExtension` (for the retracted
structure morphism `X' ⟶ Spec A ⟶ Spec k`) along `X₀ ≅ Z`, as an extension of
`f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}`. -/
def deformationTensorBaseExtension :
    Deformation.AlgebraExtension (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (structureSharpInverseImage B S hS (baseStructureMap B S hS (y₀ := y₀)))
      ((etaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS _)).obj
        ((baseRingTensorModule B S hS (deformationFibreSpace B S hS x hsq)
          (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))).obj
          (deformationBaseKernel B S hS x hsq))) :=
  castBase B S hS (deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq r hr)
    ((etaleRestrictionFunctor B S hS (deformationThickeningIso B S hS x hsq).hom
      (isEtale_hom_of_iso B S hS _) _ _).obj
      (deformationTensorAlgebraExtension B S hS x hsq (deformationRetractedStructureMap B S hS r)))

variable (x) in
/-- Through `X₀ ≅ Z`, the projection of the closed fibre to `Spec k` is the structure morphism
of `x₀`. -/
theorem deformationThickeningIso_hom_comp_fibreBaseProjection :
    (deformationThickeningIso B S hS x hsq).hom ≫ deformationFibreBaseProjection B S hS x hsq =
      baseStructureMap B S hS (y₀ := y₀) :=
  deformationThickeningIso_hom_comp_preimageProjection B S hS x hsq

variable (x) in
/-- **The ideal of the extension of a deformation on `X₀` is `𝒪_{X₀} ⊗_k 𝔪_A`**: the restriction
to `X₀ ≅ Z` of `𝒪_Z ⊗_R I` is `𝒪_{X₀} ⊗_R I` (pullback commutes with `𝒪 ⊗_R -`, Stacks 03LW for
the étale restriction), and `R ≅ k`, `I ≅ 𝔪_A`. -/
def deformationTensorLinearIdealIso :
    (etaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS _)).obj
        ((baseRingTensorModule B S hS (deformationFibreSpace B S hS x hsq)
          (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))).obj
          (deformationBaseKernel B S hS x hsq)) ≅
      (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).obj
        (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq) :=
  ((modulePullbackIsoEtaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
      (isEtale_hom_of_iso B S hS _)).app _).symm ≪≫
    (baseRingTensorModulePullbackCompIso B S hS (deformationThickeningIso B S hS x hsq).hom
      (deformationFibreBaseProjection B S hS x hsq)).app (deformationBaseKernel B S hS x hsq) ≪≫
    eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS y₀.obj.obj.left φ).obj
      (deformationBaseKernel B S hS x hsq))
      (congrArg baseRingHomOfMap
        (deformationThickeningIso_hom_comp_fibreBaseProjection B S hS x hsq))) ≪≫
    ((baseRingTensorModuleRestrictScalarsIso B S hS y₀.obj.obj.left
      (baseResidueFieldEquiv B S hS hy₀).toRingHom
      (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
      (baseResidueFieldEquiv B S hS hy₀).surjective).app _).symm ≪≫
    (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).mapIso
      (RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
        (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x) _ _
        (residueMap_surjective' x.algebra) hsq)

variable (x) in
/-- **The sections `1 ⊗ v` of `𝒪_{X₀} ⊗_k 𝔪_A`**, read through
`AlgebraicGeometry.Space.deformationTensorLinearIdealIso`: the restriction to `X₀ ≅ Z` of the
section `1 ⊗ v` of `𝒪_Z ⊗_R I`. -/
theorem baseRingTensorSection_deformationTensorLinearIdealIso_inv
    (v : RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq) :
    baseRingTensorSection B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
        (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq) v ≫
        (deformationTensorLinearIdealIso B S hS x hsq).inv =
      modulePullbackGlobalSection B S hS (deformationThickeningIso B S hS x hsq).hom
          (baseRingTensorSection B S hS (deformationFibreSpace B S hS x hsq)
            (baseRingHomOfMap (deformationFibreBaseProjection B S hS x hsq))
            (deformationBaseKernel B S hS x hsq)
            ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
              (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
              (deformationBaseImmersion_Γ_surjective B S hS x)
              (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
              (residueMap_surjective' x.algebra) hsq).inv.hom v)) ≫
        ((modulePullbackIsoEtaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
          (isEtale_hom_of_iso B S hS _)).app _).hom :=
  by
  have h₅ := baseRingTensorSection_map B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))
    (RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
      (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
      (deformationBaseImmersion_Γ_surjective B S hS x)
      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
      (residueMap_surjective' x.algebra) hsq).inv v
  have h₄ := baseRingTensorSection_restrictScalarsIso_hom B S hS y₀.obj.obj.left
    (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
    (baseResidueFieldEquiv B S hS hy₀).surjective (deformationBaseKernel B S hS x hsq)
    ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
      (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
      (deformationBaseImmersion_Γ_surjective B S hS x)
      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
      (residueMap_surjective' x.algebra) hsq).inv.hom v)
  have h₃ := baseRingTensorSection_eqToIso_inv B S hS y₀.obj.obj.left
    (φ := baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
    (φ' := baseRingHomOfMap ((deformationThickeningIso B S hS x hsq).hom ≫
      deformationFibreBaseProjection B S hS x hsq))
    (congrArg baseRingHomOfMap
      (deformationThickeningIso_hom_comp_fibreBaseProjection B S hS x hsq))
    (deformationBaseKernel B S hS x hsq)
    ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
      (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
      (deformationBaseImmersion_Γ_surjective B S hS x)
      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
      (residueMap_surjective' x.algebra) hsq).inv.hom v)
  have h₂ := baseRingTensorSection_comp_pullbackCompIso_inv B S hS
    (deformationThickeningIso B S hS x hsq).hom (deformationFibreBaseProjection B S hS x hsq)
    (deformationBaseKernel B S hS x hsq)
    ((RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
      (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x)
      (deformationBaseImmersion_Γ_surjective B S hS x)
      (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)
      (residueMap_surjective' x.algebra) hsq).inv.hom v)
  refine CategoryTheory.comp_trans_trans_trans_trans_inv
    ((modulePullbackIsoEtaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
      (isEtale_hom_of_iso B S hS _)).app _).symm
    ((baseRingTensorModulePullbackCompIso B S hS (deformationThickeningIso B S hS x hsq).hom
      (deformationFibreBaseProjection B S hS x hsq)).app (deformationBaseKernel B S hS x hsq))
    (eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS y₀.obj.obj.left φ).obj
      (deformationBaseKernel B S hS x hsq))
      (congrArg baseRingHomOfMap
        (deformationThickeningIso_hom_comp_fibreBaseProjection B S hS x hsq))))
    ((baseRingTensorModuleRestrictScalarsIso B S hS y₀.obj.obj.left
      (baseResidueFieldEquiv B S hS hy₀).toRingHom
      (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
      (baseResidueFieldEquiv B S hS hy₀).surjective).app _).symm
    ((baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).mapIso
      (RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
        (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x) _ _
        (residueMap_surjective' x.algebra) hsq))
    _ ?s4 ?s3 ?s2 ?s1 _ ?h5 ?h4 ?h3 ?h2 ?h1 (deformationTensorLinearIdealIso B S hS x hsq) rfl
  case h5 => exact h₅
  case h4 => exact h₄
  case h3 => exact h₃
  case h2 => exact h₂
  case h1 => rfl

end AlgebraicGeometry.Space

end
