module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationClass
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLift
public import StacksFrontier.Deformation.Examples.Geometric.SchemesDeformationCategory

/-!
# The extension of a deformation of an algebraic space over an algebra with square-zero ideal

In the situation of Stacks 0E3Z, let `X` be an algebraic space over the field `k` and let `y` be
an object of the deformation category of `X` over an object `A` of `𝒞_Λ` whose maximal ideal
`𝔪_A` squares to zero: a flat family `X' ⟶ Spec A` together with a cartesian arrow from `X`
over `Spec k ⟶ Spec A`. The closed fibre `Z = X' ×_{Spec A} Spec k ⊆ X'` is a first order
thickening, identified with `X` by the cartesian arrow, and for a retraction `r` of
`Spec k ⟶ Spec A` the structure sheaf of `X'` read on `X` is an extension

`0 ⟶ 𝒪_X ⊗_k 𝔪_A ⟶ 𝒪_{X'}|_X ⟶ 𝒪_X ⟶ 0`

of `f⁻¹𝒪_{Spec k}`-algebras, `f : X ⟶ Spec k` the structure morphism: its ideal is the
conormal module of `Z ⊆ X'`, which is `𝒪_Z ⊗ 𝔪_A` by flatness (the flat clause of Stacks 04CQ).
This is the identification of first-order deformations with extensions used in the proof of
[Stacks Project, Tag 0D17], which the second display of [Stacks Project, Tag 0E41] rests on.

The construction is the one for proper flat families
(`AlgebraicGeometry.Space.deformationKernelExtension`), carried out for the category of
Stacks 0E3Z: no properness is used.

## Main definitions

* `Deformation.Examples.spaceDefoThickening`: the closed fibre `Z ⊆ X'`.
* `Deformation.Examples.spaceDefoThickeningIso`: `X ≅ Z`.
* `Deformation.Examples.spaceDefoKernelExtension`: the extension of `𝒪_X` by `𝒪_X ⊗_k 𝔪_A`.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-! ### Residue maps -/

/-- **A morphism of `𝒞_Λ` to the residue field is the residue map.** -/
theorem hom_residueFieldBase_eq_residueMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) : f.hom.toRingHom = residueMap A := by
  have h := residueMap_comp f
  rwa [residueMap_residueFieldBase] at h

/-! ### The base `Spec k ⊆ Spec A` -/

/-- The closed immersion `Spec k ⟶ Spec A` underlying the structure arrow of a point. -/
abbrev spaceDefoBaseImmersion (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    spaceBaseOver B hΛ hSpec (residueFieldBase Λ k) ⟶ spaceBaseOver B hΛ hSpec y.left.base :=
  spaceBaseOverMap B hΛ hSpec y.hom.base

variable (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
  (hA : IsLocalRing.maximalIdeal y.left.base ^ 2 = ⊥)

include hA in
/-- The base immersion of a point over an algebra with square-zero maximal ideal is a
square-zero closed immersion. -/
theorem isSquareZeroClosedImmersion_spaceDefoBaseImmersion :
    IsSquareZeroClosedImmersion B (Spec (.of Λ)) hΛ
      (spaceDefoBaseImmersion B hΛ hSpec X hX toK y) :=
  isSquareZeroClosedImmersion_spaceBaseOverMap B hΛ hSpec y.hom.base hA

include hA in
/-- The base immersion is a closed immersion. -/
theorem isClosedImmersion_spaceDefoBaseImmersion :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceDefoBaseImmersion B hΛ hSpec X hX toK y)) :=
  (isSquareZeroClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK y hA).1

/-- The base `Spec A` of a point is affine. -/
theorem isAffine_spaceDefoBase :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
      (spaceBaseOver B hΛ hSpec y.left.base)) :=
  isAffine_toScheme_spaceBaseOver B hΛ hSpec y.left.base

/-! ### Functions on the base -/

variable {B hΛ hSpec} in
/-- **`A ≃ Γ(Spec A)`** for an object `A` of `𝒞_Λ`, read on the big fppf site. -/
abbrev spaceDefoAlgebraEquiv (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    A ≃+* baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec A) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv

/-- **Pullback of functions along `Spec k ⟶ Spec A` is the residue map**, through
`A ≃ Γ(Spec A)` and `k ≃ Γ(Spec k)`. -/
theorem spaceDefoBaseImmersion_Γ_comp :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceDefoBaseImmersion B hΛ hSpec X hX toK y)).op).hom.comp
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) y.left.base).toRingHom =
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
        (residueFieldBase Λ k)).toRingHom.comp (residueMap y.left.base) := by
  have hm : (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceDefoBaseImmersion B hΛ hSpec X hX toK y) =
      Spec.map (CommRingCat.ofHom y.hom.base.hom.toRingHom) := B.inclusion.map_preimage _
  rw [hm, ← hom_residueFieldBase_eq_residueMap y.hom.base]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y.hom.base.hom.toRingHom)
  ext a
  exact (congrArg (fun g => g.hom a) h).symm

/-- The ring map `Γ(Spec A) ⟶ Γ(Spec k)` of the base immersion is surjective. -/
theorem spaceDefoBaseImmersion_Γ_surjective :
    Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceDefoBaseImmersion B hΛ hSpec X hX toK y)).op).hom :=
  RingHom.surjective_of_ringEquiv _ _ _ _ (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK y)
    (residueMap_surjective' y.left.base)

/-- The kernel of the residue map of an object of `𝒞_Λ` is its maximal ideal. -/
theorem ker_residueMap_eq_maximalIdeal (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    RingHom.ker (residueMap A) = IsLocalRing.maximalIdeal A := by
  rw [← hom_residueFieldBase_eq_residueMap (isTerminal_residueFieldBase.from A)]
  exact ker_eq_maximalIdeal_of_hom_residueFieldBase _

/-- The residue map of an object with square-zero maximal ideal has square-zero kernel. -/
theorem ker_residueMap_sq_of_maximalIdeal_sq {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : IsLocalRing.maximalIdeal A ^ 2 = ⊥) : RingHom.ker (residueMap A) ^ 2 = ⊥ := by
  rwa [ker_residueMap_eq_maximalIdeal]

include hA in
/-- The kernel of `Γ(Spec A) ⟶ Γ(Spec k)` squares to zero when `𝔪_A² = 0`. -/
theorem spaceDefoBaseImmersion_Γ_ker_sq :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceDefoBaseImmersion B hΛ hSpec X hX toK y)).op).hom ^ 2 = ⊥ :=
  RingHom.ker_sq_eq_bot_of_ringEquiv _ _ _ _ (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK y)
    (ker_residueMap_sq_of_maximalIdeal_sq hA)

/-! ### The closed fibre -/

/-- **The closed fibre `Z = X' ×_{Spec A} Spec k ⊆ X'`** of a point over an algebra with
square-zero maximal ideal. -/
abbrev spaceDefoThickening : ClosedSubspaces B (Spec (.of Λ)) hΛ
    (spaceTotalSpace B hΛ hSpec y.left).1 :=
  preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec y.left)
    (squareZeroSubspace B (Spec (.of Λ)) hΛ _
      (isSquareZeroClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK y hA))

/-- The closed fibre is a first order thickening of the total space. -/
theorem isFirstOrderThickening_spaceDefoThickening :
    IsFirstOrderThickening B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)
      (spaceDefoThickening B hΛ hSpec X hX toK y hA).1 :=
  isFirstOrderThickening_preimage_squareZeroSubspace B (Spec (.of Λ)) hΛ _
    (isSquareZeroClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK y hA)
    (spaceTotalToBase B hΛ hSpec y.left)

/-- The closed fibre, as an algebraic space. -/
abbrev spaceDefoFibreSpace : AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
  ⟨(spaceDefoThickening B hΛ hSpec X hX toK y hA).1.toFunctor,
    (spaceDefoThickening B hΛ hSpec X hX toK y hA).2.1⟩

/-- **The closed fibre is `X`**: the structure arrow of the point and the inverse-image square of
the closed fibre are both fibre products of `X' ⟶ Spec A` and `Spec k ⟶ Spec A`. -/
def spaceDefoThickeningIsoPresheaf :
    X ≅ (spaceDefoThickening B hΛ hSpec X hX toK y hA).1.toFunctor := by
  let i := spaceDefoBaseImmersion B hΛ hSpec X hX toK y
  have hi := isSquareZeroClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK y hA
  have hAp : IsPullback y.hom.map toK y.left.toBase (yoneda.map i) := y.hom.cartesian
  have hB := isPullback_preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec y.left)
    (squareZeroSubspace B (Spec (.of Λ)) hΛ i hi)
  have key : (rangeIsoPresheaf B (Spec (.of Λ)) hΛ i hi.1).inv ≫ yoneda.map i =
      (Subfunctor.range (yoneda.map i)).ι := by
    rw [Iso.inv_comp_eq, rangeIsoPresheaf_hom, Subfunctor.toRange_ι]
  have hB' : IsPullback (spaceDefoThickening B hΛ hSpec X hX toK y hA).1.ι
      ((preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec y.left)
        (squareZeroSubspace B (Spec (.of Λ)) hΛ i hi)).hom ≫
          (rangeIsoPresheaf B (Spec (.of Λ)) hΛ i hi.1).inv)
      y.left.toBase (yoneda.map i) :=
    hB.of_iso (Iso.refl _) (Iso.refl _) (rangeIsoPresheaf B (Spec (.of Λ)) hΛ i hi.1).symm
      (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
      (by simp only [Iso.refl_hom, Category.id_comp]; exact Category.comp_id _)
      (by simp only [Iso.symm_hom, Iso.refl_hom]; exact key.symm)
  exact hAp.isoIsPullback _ _ hB'

/-- The identification of `X` with the closed fibre is compatible with the maps into `X'`. -/
theorem spaceDefoThickeningIsoPresheaf_hom_ι :
    (spaceDefoThickeningIsoPresheaf B hΛ hSpec X hX toK y hA).hom ≫
        (spaceDefoThickening B hΛ hSpec X hX toK y hA).1.ι = y.hom.map :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The closed fibre is `X`**, as an isomorphism of algebraic spaces. -/
def spaceDefoThickeningIso :
    spaceOf B hΛ X hX ≅ spaceDefoFibreSpace B hΛ hSpec X hX toK y hA :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (spaceDefoThickeningIsoPresheaf B hΛ hSpec X hX toK y hA)

/-- The structure arrow `X ⟶ X'` of a point, as a morphism of algebraic spaces. -/
abbrev spaceDefoArrow : spaceOf B hΛ X hX ⟶ spaceTotalSpace B hΛ hSpec y.left :=
  ObjectProperty.homMk (spaceSpecialMap B hΛ hSpec X hX toK y)

/-- The identification of `X` with the closed fibre, followed by the inclusion of the closed
fibre, is the structure arrow of the point. -/
theorem spaceDefoThickeningIso_hom_comp_subspaceInclusion :
    (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hA) =
      spaceDefoArrow B hΛ hSpec X hX toK y := by
  apply ObjectProperty.hom_ext
  exact spaceDefoThickeningIsoPresheaf_hom_ι B hΛ hSpec X hX toK y hA

/-- The projection `Z ⟶ Spec k` of the closed fibre. -/
abbrev spaceDefoFibreBaseProjection :
    spaceDefoFibreSpace B hΛ hSpec X hX toK y hA ⟶
      schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) :=
  preimageRangeProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec y.left)
    (spaceDefoBaseImmersion B hΛ hSpec X hX toK y)
    (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK y hA)

/-- **Through `X ≅ Z`, the projection of the closed fibre to `Spec k` is the structure morphism
of `X`.** -/
theorem spaceDefoThickeningIso_hom_comp_fibreBaseProjection :
    (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom ≫
        spaceDefoFibreBaseProjection B hΛ hSpec X hX toK y hA =
      spaceStructureMap B hΛ hSpec X hX toK := by
  apply ObjectProperty.hom_ext
  exact IsPullback.isoIsPullback_hom_snd _ _ _ _

/-! ### The ideal of the closed fibre -/

/-- The `Γ(Spec k)`-module `I = Ker(Γ(Spec A) ⟶ Γ(Spec k))`, `I² = 0`. -/
abbrev spaceDefoBaseKernel :
    ModuleCat.{u}
      (baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :=
  RingHom.squareZeroKer _ (spaceDefoBaseImmersion_Γ_surjective B hΛ hSpec X hX toK y)
    (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK y hA)


/-- **The conormal module of the closed fibre is `𝒪_Z ⊗_R I`**, `R = Γ(Spec k)`,
`I = Ker(Γ(Spec A) ⟶ R)`, by flatness of `X' ⟶ Spec A` (the flat clause of Stacks 04CQ). -/
def spaceDefoTensorIdealIso :
    conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left)
        (spaceDefoThickening B hΛ hSpec X hX toK y hA) ≅
      (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hA)
        (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK y hA))).obj
        (spaceDefoBaseKernel B hΛ hSpec X hX toK y hA) :=
  conormalModulePreimageSquareZeroIso B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec y.left)
    (spaceDefoBaseImmersion B hΛ hSpec X hX toK y)
    (isClosedImmersion_spaceDefoBaseImmersion B hΛ hSpec X hX toK y hA) y.left.flat
    (isAffine_spaceDefoBase B hΛ hSpec X hX toK y)
    (spaceDefoBaseImmersion_Γ_ker_sq B hΛ hSpec X hX toK y hA)

/-- **The extension of the closed fibre, with ideal `𝒪_Z ⊗_R I`.** The extension of the first
order thickening `Z ⊆ X'` (`AlgebraicGeometry.Space.firstOrderAlgebraExtension`), for any
`g : X' ⟶ Y`, with its ideal read through `Deformation.Examples.spaceDefoTensorIdealIso`. -/
def spaceDefoTensorAlgebraExtension {Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ}
    (g : spaceTotalSpace B hΛ hSpec y.left ⟶ Y) :
    AlgebraExtension
      (J := SmallEtale.topology B (Spec (.of Λ)) hΛ
        (spaceDefoThickening B hΛ hSpec X hX toK y hA).1.toFunctor)
      (structureSharpInverseImage B (Spec (.of Λ)) hΛ
        (subspaceInclusion B (Spec (.of Λ)) hΛ _
          (spaceDefoThickening B hΛ hSpec X hX toK y hA) ≫ g))
      ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hA)
        (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK y hA))).obj
        (spaceDefoBaseKernel B hΛ hSpec X hX toK y hA)) :=
  (firstOrderAlgebraExtension B (Spec (.of Λ)) hΛ (spaceDefoThickening B hΛ hSpec X hX toK y hA)
      (isFirstOrderThickening_spaceDefoThickening B hΛ hSpec X hX toK y hA) g).transportKernel
    (spaceDefoTensorIdealIso B hΛ hSpec X hX toK y hA)

/-! ### The extension on `X` -/

variable {y} (r : spaceBaseOver B hΛ hSpec y.left.base ⟶
    spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
  (hr : spaceDefoBaseImmersion B hΛ hSpec X hX toK y ≫ r = 𝟙 _)

/-- The composite `X' ⟶ Spec A ⟶ Spec k` of the structure morphism of a point with a retraction
`r` of `Spec k ⟶ Spec A`. -/
abbrev spaceDefoRetractedStructureMap :
    spaceTotalSpace B hΛ hSpec y.left ⟶
      schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) :=
  spaceTotalToBase B hΛ hSpec y.left ≫ schemeSpaceMap r

include hr in
/-- Restricted to `X` through the closed fibre, the retracted structure morphism of a point is
the structure morphism of `X`. -/
theorem spaceDefoThickeningIso_hom_comp_retractedStructureMap :
    (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom ≫
        (subspaceInclusion B (Spec (.of Λ)) hΛ _ (spaceDefoThickening B hΛ hSpec X hX toK y hA) ≫
          spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r) =
      spaceStructureMap B hΛ hSpec X hX toK := by
  rw [← Category.assoc, spaceDefoThickeningIso_hom_comp_subspaceInclusion]
  apply ObjectProperty.hom_ext
  change y.hom.map ≫ y.left.toBase ≫ yoneda.map r = toK
  have hr' : yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base) ≫ yoneda.map r = 𝟙 _ := by
    rw [← yoneda.map_comp]
    exact (congrArg yoneda.map hr).trans (yoneda.map_id _)
  rw [← Category.assoc, y.hom.cartesian.w, Category.assoc, hr']
  exact Category.comp_id _

/-- **The extension of a point, on `X`, with ideal the restriction of `𝒪_Z ⊗_R I`.** The
restriction along `X ≅ Z` of `Deformation.Examples.spaceDefoTensorAlgebraExtension` for the
retracted structure morphism, as an extension of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X`. -/
def spaceDefoTensorBaseExtension :
    AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (structureSharpInverseImage B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      ((etaleRestrictionModule B (Spec (.of Λ)) hΛ
          (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom
          (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _)).obj
        ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hA)
          (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK y hA))).obj
          (spaceDefoBaseKernel B hΛ hSpec X hX toK y hA))) :=
  castBase B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso_hom_comp_retractedStructureMap B hΛ hSpec X hX toK hA r hr)
    ((etaleRestrictionFunctor B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom
        (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _) _ _).obj
      (spaceDefoTensorAlgebraExtension B hΛ hSpec X hX toK y hA
        (spaceDefoRetractedStructureMap B hΛ hSpec X hX toK r)))

/-- The base-ring datum `k ⟶ Γ(X, 𝒪_X)` (on the model of the small étale site) of the structure
morphism of `X`. -/
abbrev spaceDefoFieldHom : k →+* modelGlobalFunctions B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX) :=
  (baseRingHomOfMap (spaceStructureMap B hΛ hSpec X hX toK)).comp
    (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)).toRingHom

variable (y) in
/-- **The ideal of the extension of a point on `X` is `𝒪_X ⊗_k 𝔪_A`**: the restriction to
`X ≅ Z` of `𝒪_Z ⊗_R I` is `𝒪_X ⊗_R I` (pullback commutes with `𝒪 ⊗_R -`, and étale restriction
is pullback, Stacks 03LW), and `R ≅ k`, `I ≅ 𝔪_A`. -/
def spaceDefoTensorLinearIdealIso :
    (etaleRestrictionModule B (Spec (.of Λ)) hΛ
        (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom
        (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _)).obj
        ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hA)
          (baseRingHomOfMap (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK y hA))).obj
          (spaceDefoBaseKernel B hΛ hSpec X hX toK y hA)) ≅
      (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
        (RingHom.squareZeroKer (residueMap y.left.base) (residueMap_surjective' y.left.base)
          (ker_residueMap_sq_of_maximalIdeal_sq hA)) :=
  ((modulePullbackIsoEtaleRestrictionModule B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom
      (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ _)).app _).symm ≪≫
    (baseRingTensorModulePullbackCompIso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hA).hom
      (spaceDefoFibreBaseProjection B hΛ hSpec X hX toK y hA)).app
      (spaceDefoBaseKernel B hΛ hSpec X hX toK y hA) ≪≫
    eqToIso (congrArg (fun φ => (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX) φ).obj
      (spaceDefoBaseKernel B hΛ hSpec X hX toK y hA))
      (congrArg baseRingHomOfMap
        (spaceDefoThickeningIso_hom_comp_fibreBaseProjection B hΛ hSpec X hX toK y hA))) ≪≫
    ((baseRingTensorModuleRestrictScalarsIso B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)).toRingHom
      (baseRingHomOfMap (spaceStructureMap B hΛ hSpec X hX toK))
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
        (residueFieldBase Λ k)).surjective).app _).symm ≪≫
    (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
      (spaceDefoFieldHom B hΛ hSpec X hX toK)).mapIso
      (RingHom.squareZeroKerRingEquivIso _ _
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) y.left.base)
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k))
        (spaceDefoBaseImmersion_Γ_comp B hΛ hSpec X hX toK y) _ _
        (residueMap_surjective' y.left.base) (ker_residueMap_sq_of_maximalIdeal_sq hA))

include hr in
/-- **The extension of a point, with ideal `𝒪_X ⊗_k 𝔪_A`.** -/
def spaceDefoKernelExtension :
    AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
        (RingHom.squareZeroKer (residueMap y.left.base) (residueMap_surjective' y.left.base)
          (ker_residueMap_sq_of_maximalIdeal_sq hA))) :=
  (spaceDefoTensorBaseExtension B hΛ hSpec X hX toK hA r hr).transportKernel
    (spaceDefoTensorLinearIdealIso B hΛ hSpec X hX toK y hA)

end Deformation.Examples

end
