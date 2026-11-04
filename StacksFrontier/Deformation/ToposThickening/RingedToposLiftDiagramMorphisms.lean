module

public import StacksFrontier.Deformation.ToposThickening.RingedToposLiftDiagram
import StacksCore.Tactic.StacksAttribute

/-!
# The morphisms fitting into the diagram of Stacks 08UG

For the general diagram `Deformation.ToposThickening.RingedToposLiftDiagram` of
[Stacks Project, Tag 08UG], the lifting problem asks for a morphism of ringed topoi
`g' : (Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` fitting into (08UH) compatibly with `ν`. This file
defines those morphisms, `RingedToposLiftDiagram.CompatibleLift`, and proves that they are exactly
the lifts of the one-site diagram `RingedToposLiftDiagram.toFirstOrderLiftDiagram` on `𝒞₂` of the
source's reduction: a morphism of ringed topoi inducing `g` on the topoi is its comorphism
`g⁻¹𝒪'₁ ⟶ 𝒪'₂`, and each face of (08UH) it has to close becomes one condition on the comorphism.

## Main definitions

* `Deformation.ToposThickening.RingedToposLiftDiagram.thickenedSource₁` and siblings: the four
  thickened ringed topoi `(Sh(𝒞'ⱼ), 𝒪'ⱼ)` and `(Sh(ℬ'ⱼ), 𝒪_{ℬ'ⱼ})`, on the sites of their
  reductions.
* `RingedToposLiftDiagram.thickenedHom₁`, `thickenedHom₂` and `thickenedBaseMorphism`: the
  morphisms `f'₁`, `f'₂` and `h'` of (08UH).
* `RingedToposLiftDiagram.liftHom`: the morphism `(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` inducing `g`
  on the topoi with a given structure map.
* `RingedToposLiftDiagram.CompatibleLift`: a morphism fitting into (08UH) compatibly with `ν`.
* `RingedToposLiftDiagram.compatibleLiftEquiv`: those morphisms are the lifts of the one-site
  diagram.

## Implementation notes

`CompatibleLift` follows `Deformation.ToposThickening.InverseImageExtension.CompatibleMorphism`
(Stacks 0GQ7): the morphism `g'` is `liftHom ψ` for its structure map `ψ`, so it induces `g` on
the topoi as the identification of the underlying topoi of the thickenings forces. The face
`f'₁ ∘ g' = h' ∘ f'₂` is an equality of morphisms of ringed topoi; the face `g' ∘ i₂ = i₁ ∘ g`,
the thickenings `iⱼ` being the identity on the topoi, is the equality of the two maps
`g⁻¹𝒪'₁ ⟶ 𝒪₂`; compatibility with `ν` is read after the two inclusions `g⁻¹𝒢₁ ⊂ g⁻¹𝒪'₁` and
`𝒢₂ ⊂ 𝒪'₂`.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UH](https://stacks.math.columbia.edu/tag/08UH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor
  commRingImageAdjunction)
open Deformation.ToposThickening.InverseImageExtension (invImage invIdealOf invKernelInclOf
  comp_fSharpInverseImage_eq)

universe u

namespace Deformation.ToposThickening

/-- Two morphisms of ringed topoi with equal underlying morphisms of topoi are equal exactly when
their structure maps, in inverse-image form, agree through that equality. -/
theorem RingedToposHom.eq_iff_fSharpInverseImage {X B : RingedTopos.{u, u, u}}
    [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (a b : RingedToposHom X B) (ht : a.toToposHom = b.toToposHom) :
    a = b ↔ a.fSharpInverseImage =
      eqToHom (congrArg (fun T => (inverseImageCommRingFunctor T).obj B.O) ht) ≫
        b.fSharpInverseImage := by
  obtain ⟨Ta, fa⟩ := a
  obtain ⟨Tb, fb⟩ := b
  dsimp only at ht
  subst ht
  simp only [eqToHom_refl, Category.id_comp]
  constructor
  · intro h
    cases h
    rfl
  · intro h
    congr 1
    exact ((commRingImageAdjunction Ta).homEquiv _ _).symm.injective h

/-- The comorphism of a morphism of ringed topoi with structure map the adjunct of `φ` is `φ`. -/
private theorem fSharpInverseImage_mk_homEquiv {X B : RingedTopos.{u, u, u}}
    [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (T : MorphismOfTopoi X.Topos B.Topos) (φ : (inverseImageCommRingFunctor T).obj B.O ⟶ X.O) :
    (RingedToposHom.mk T ((commRingImageAdjunction T).homEquiv _ _ φ)).fSharpInverseImage = φ :=
  ((commRingImageAdjunction T).homEquiv _ _).symm_apply_apply φ

namespace RingedToposLiftDiagram

variable {X₁ X₂ B₁ B₂ : RingedTopos.{u, u, u}}
  [X₁.J.HasSheafCompose (forget RingCat.{u})] [X₂.J.HasSheafCompose (forget RingCat.{u})]
  [B₁.J.HasSheafCompose (forget RingCat.{u})] [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{u})] [X₂.J.HasSheafCompose (forget CommRingCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X₂.J AddCommGrpCat.{u}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : RingedToposLiftDiagram X₁ X₂ B₁ B₂)

/-! ### The thickened ringed topoi and the thickened morphisms of (08UH) -/

/-- The thickened ringed topos `(Sh(𝒞'₁), 𝒪'₁)`, on the site of `𝒞₁`. -/
abbrev thickenedSource₁ : RingedTopos.{u, u, u} := { C := X₁.C, J := X₁.J, O := D.Q₁.extension }

/-- The thickened ringed topos `(Sh(𝒞'₂), 𝒪'₂)`, on the site of `𝒞₂`. -/
abbrev thickenedSource₂ : RingedTopos.{u, u, u} := { C := X₂.C, J := X₂.J, O := D.Q₂.extension }

/-- The thickened ringed topos `(Sh(ℬ'₁), 𝒪_{ℬ'₁})`, on the site of `ℬ₁`. -/
abbrev thickenedBase₁ : RingedTopos.{u, u, u} :=
  { C := B₁.C, J := B₁.J, O := D.S₁.baseExtension }

/-- The thickened ringed topos `(Sh(ℬ'₂), 𝒪_{ℬ'₂})`, on the site of `ℬ₂`. -/
abbrev thickenedBase₂ : RingedTopos.{u, u, u} :=
  { C := B₂.C, J := B₂.J, O := D.S₂.baseExtension }

/-- The morphism `f'₁ : (Sh(𝒞'₁), 𝒪'₁) ⟶ (Sh(ℬ'₁), 𝒪_{ℬ'₁})`: it induces `f₁` on the topoi and its
comorphism is the structure map `f₁⁻¹𝒪_{ℬ'₁} ⟶ 𝒪'₁` of the front row. -/
def thickenedHom₁ : RingedToposHom (thickenedSource₁ D) (thickenedBase₁ D) where
  toToposHom := D.S₁.f.toToposHom
  fSharp := (commRingImageAdjunction D.S₁.f.toToposHom).homEquiv _ _ D.Q₁.baseMap

/-- The morphism `f'₂ : (Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(ℬ'₂), 𝒪_{ℬ'₂})`. -/
def thickenedHom₂ : RingedToposHom (thickenedSource₂ D) (thickenedBase₂ D) where
  toToposHom := D.S₂.f.toToposHom
  fSharp := (commRingImageAdjunction D.S₂.f.toToposHom).homEquiv _ _ D.Q₂.baseMap

/-- The morphism `h' : (Sh(ℬ'₂), 𝒪_{ℬ'₂}) ⟶ (Sh(ℬ'₁), 𝒪_{ℬ'₁})`. -/
def thickenedBaseMorphism : RingedToposHom (thickenedBase₂ D) (thickenedBase₁ D) where
  toToposHom := D.h.toToposHom
  fSharp := (commRingImageAdjunction D.h.toToposHom).homEquiv _ _ D.hB'

/-- The morphism `(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` inducing `g` on the topoi with structure map
`ψ : 𝒪'₁ ⟶ g_*𝒪'₂`. -/
def liftHom (ψ : D.Q₁.extension ⟶ (pushforwardCommRingFunctor D.g.toToposHom).obj D.Q₂.extension) :
    RingedToposHom (thickenedSource₂ D) (thickenedSource₁ D) where
  toToposHom := D.g.toToposHom
  fSharp := ψ

omit [X₁.J.HasSheafCompose (forget CommRingCat)] [X₂.J.HasSheafCompose (forget CommRingCat)]
  [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comorphism `f₁⁻¹𝒪_{ℬ'₁} ⟶ 𝒪'₁` of `f'₁` is the structure map `D.Q₁.baseMap`. -/
theorem thickenedHom₁_fSharpInverseImage :
    (thickenedHom₁ D).fSharpInverseImage = D.Q₁.baseMap :=
  fSharpInverseImage_mk_homEquiv _ _

omit [X₁.J.HasSheafCompose (forget CommRingCat)] [X₂.J.HasSheafCompose (forget CommRingCat)]
  [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comorphism `f₂⁻¹𝒪_{ℬ'₂} ⟶ 𝒪'₂` of `f'₂` is the structure map `D.Q₂.baseMap`. -/
theorem thickenedHom₂_fSharpInverseImage :
    (thickenedHom₂ D).fSharpInverseImage = D.Q₂.baseMap :=
  fSharpInverseImage_mk_homEquiv _ _

omit [X₁.J.HasSheafCompose (forget CommRingCat)] [X₂.J.HasSheafCompose (forget CommRingCat)]
  [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comorphism `h⁻¹𝒪_{ℬ'₁} ⟶ 𝒪_{ℬ'₂}` of `h'` is the given map `D.hB'`. -/
theorem thickenedBaseMorphism_fSharpInverseImage :
    (thickenedBaseMorphism D).fSharpInverseImage = D.hB' :=
  fSharpInverseImage_mk_homEquiv _ _

/-- **The face `f'₁ ∘ g' = h' ∘ f'₂` of (08UH)**, for `g'` inducing `g` on the topoi, is the
equality `g⁻¹f'₁ ≫ g'^♯ = h' ≫ f'₂` of the two maps `g⁻¹f₁⁻¹𝒪_{ℬ'₁} ⟶ 𝒪'₂`, the source and
`f₂⁻¹h⁻¹𝒪_{ℬ'₁}` compared by `f₁ ∘ g = h ∘ f₂`. -/
theorem comp_liftHom_eq_iff
    (ψ : D.Q₁.extension ⟶ (pushforwardCommRingFunctor D.g.toToposHom).obj D.Q₂.extension) :
    (thickenedHom₁ D).comp (liftHom D ψ) = (thickenedBaseMorphism D).comp (thickenedHom₂ D) ↔
      (invImage D.g).map D.Q₁.baseMap ≫ (liftHom D ψ).fSharpInverseImage =
        thickBaseHom D ≫ D.Q₂.baseMap := by
  have ht₀ := congrArg RingedToposHom.toToposHom D.comm
  have ht : ((thickenedHom₁ D).comp (liftHom D ψ)).toToposHom =
      ((thickenedBaseMorphism D).comp (thickenedHom₂ D)).toToposHom := ht₀
  rw [RingedToposHom.eq_iff_fSharpInverseImage _ _ ht,
    comp_fSharpInverseImage_eq, comp_fSharpInverseImage_eq, thickenedHom₁_fSharpInverseImage,
    thickenedHom₂_fSharpInverseImage, thickenedBaseMorphism_fSharpInverseImage, Iso.inv_comp_eq]
  simp only [thickBaseHom, baseComparison, Iso.trans_hom, Iso.symm_hom]
  exact Iff.rfl

omit [X₁.J.HasSheafCompose (forget CommRingCat)] [X₂.J.HasSheafCompose (forget CommRingCat)]
  [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comorphism of `liftHom ψ` is the adjunct of `ψ`. -/
theorem liftHom_fSharpInverseImage
    (ψ : D.Q₁.extension ⟶ (pushforwardCommRingFunctor D.g.toToposHom).obj D.Q₂.extension) :
    (liftHom D ψ).fSharpInverseImage =
      ((commRingImageAdjunction D.g.toToposHom).homEquiv _ _).symm ψ :=
  rfl

omit [X₁.J.HasSheafCompose (forget CommRingCat)] [X₂.J.HasSheafCompose (forget CommRingCat)]
  [HasWeakSheafify X₂.J AddCommGrpCat] [X₂.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The comorphism of the morphism attached to the adjunct of a comorphism is that comorphism. -/
theorem liftHom_homEquiv (φ : (invImage D.g).obj D.Q₁.extension ⟶ D.Q₂.extension) :
    (liftHom D ((commRingImageAdjunction D.g.toToposHom).homEquiv _ _ φ)).fSharpInverseImage =
      φ :=
  fSharpInverseImage_mk_homEquiv _ _

/-! ### The morphisms fitting into (08UH) compatibly with `ν` -/

/-- **A morphism `g' : (Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` of ringed topoi fitting into the diagram
(08UH) of Stacks 08UG compatibly with `ν`.** It induces `g` on the topoi (it is `liftHom ψ` for
its structure map `ψ : 𝒪'₁ ⟶ g_*𝒪'₂`), closes the face `f'₁ ∘ g' = h' ∘ f'₂`, closes the face
`g' ∘ i₂ = i₁ ∘ g` (its comorphism followed by `𝒪'₂ ⟶ 𝒪₂` is `g⁻¹`(reduction) followed by `g^♯`),
and its comorphism carries `g⁻¹𝒢₁ ⊂ g⁻¹𝒪'₁` into `𝒢₂ ⊂ 𝒪'₂` by `ν`. -/
@[ext]
structure CompatibleLift where
  /-- The structure map `𝒪'₁ ⟶ g_*𝒪'₂` of `g'`. -/
  fSharp : D.Q₁.extension ⟶ (pushforwardCommRingFunctor D.g.toToposHom).obj D.Q₂.extension
  /-- The face `f'₁ ∘ g' = h' ∘ f'₂`. -/
  over_base :
    (thickenedHom₁ D).comp (liftHom D fSharp) = (thickenedBaseMorphism D).comp (thickenedHom₂ D)
  /-- The face `g' ∘ i₂ = i₁ ∘ g`. -/
  over_g : (liftHom D fSharp).fSharpInverseImage ≫ D.Q₂.reduction =
    (invImage D.g).map D.Q₁.reduction ≫ D.g.fSharpInverseImage
  /-- `g'` induces `ν` on the ideals. -/
  compatible_nu : ∀ (U : X₂.Cᵒᵖ) (m : (invIdealOf D.g D.S₁.G).val.obj U),
    (liftHom D fSharp).fSharpInverseImage.hom.app U
        (show ((invImage D.g).obj D.Q₁.extension).obj.obj U from
          (frontKernelIncl D).val.app U m) =
      (show D.Q₂.extension.obj.obj U from
        D.Q₂.kernelInclusion.val.app U (show D.S₂.G.val.obj U from D.nu.val.app U m))

/-- **The morphisms fitting into (08UH) compatibly with `ν` are the lifts of the one-site
diagram** of the source's reduction: a morphism inducing `g` on the topoi is its comorphism
`g⁻¹𝒪'₁ ⟶ 𝒪'₂`, and the three conditions are those of
`Deformation.ToposThickening.FirstOrderLiftDiagram.Lift`. -/
def compatibleLiftEquiv : CompatibleLift D ≃ (toFirstOrderLiftDiagram D).Lift where
  toFun p :=
    { hom := (liftHom D p.fSharp).fSharpInverseImage
      reduction_app := fun U a => congrArg (fun k => k.hom.app U a) p.over_g
      base_app := fun U a => congrArg (fun k => k.hom.app U a)
        ((comp_liftHom_eq_iff D p.fSharp).1 p.over_base)
      kernel_comm := p.compatible_nu }
  invFun q :=
    { fSharp := (commRingImageAdjunction D.g.toToposHom).homEquiv _ _ q.hom
      over_base := (comp_liftHom_eq_iff D _).2
        ((congrArg (fun k => (invImage D.g).map D.Q₁.baseMap ≫ k)
          (liftHom_homEquiv D q.hom)).trans q.base_comm)
      over_g := (congrArg (fun k => k ≫ D.Q₂.reduction) (liftHom_homEquiv D q.hom)).trans
        q.reduction_comm
      compatible_nu := fun U m =>
        (congrArg (fun k => k.hom.app U
          (show ((invImage D.g).obj D.Q₁.extension).obj.obj U from
            (frontKernelIncl D).val.app U m)) (liftHom_homEquiv D q.hom)).trans
          (q.kernel_comm U m) }
  left_inv p := CompatibleLift.ext
    (((commRingImageAdjunction D.g.toToposHom).homEquiv _ _).apply_symm_apply p.fSharp)
  right_inv q := FirstOrderLiftDiagram.Lift.ext (liftHom_homEquiv D q.hom)

end RingedToposLiftDiagram

end Deformation.ToposThickening

end
