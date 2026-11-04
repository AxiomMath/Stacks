module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.FunctorialityTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.IsoOfAlgebraIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.AffineBaseChange

/-!
# Polarized isomorphisms over an affine base are isomorphisms of section algebras

Let `(f : X ⟶ S, ℒ)` and `(g : Y ⟶ S, ℳ)` be polarized families (proper, flat, of finite
presentation, with invertible relatively ample polarizations) over an affine scheme `S`, and let
`d₀ > 0`. Pulling sections back along an isomorphism `φ : X ≅ Y` over `S` and reading them through
`φ^* ℳ ≅ ℒ` gives an isomorphism of the global sections data of the truncated section algebras
`𝒜(g) = 𝒪_S ⊕ ⨁_{d ≥ d₀} g_* ℳ^{⊗ d}` and `𝒜(f)`. This file proves that this is a bijection
(`Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection`).

The inverse is the construction of [Stacks, Tag 0D4F]: an isomorphism of data is an isomorphism
of graded algebras `𝒜(g) ⟶ 𝒜(f)` (the base being affine), hence an isomorphism of relative `Proj`
compatible with the Serre twists ([Stacks, Tag 07ZJ]); through the isomorphisms `r'` and `θ'` of
conclusions (4) and (5) of [Stacks, Tag 0D4F], which hold at every cut, it gives an isomorphism of
polarized families. One composite is the identity by the functoriality of `r'` and `θ'`; the other
by [Stacks, Tag 01O9]: a multiplicative family of maps out of the Serre twists is determined by its
degree-one member.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver.sectionsIso`: the isomorphism
  of global sections data attached to an isomorphism of polarized families.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver.ofSectionsIso`: the
  isomorphism of polarized families attached to an isomorphism of data.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoOver.sectionsEquiv`: the bijection.
* `PolarizedFamily.deformationOfIsoOver`, `PolarizedFamily.homOfIsoOver` (in the namespace
  `Stacks.AlgebraicGeometry.ProjectiveDeformation`): an isomorphism of polarized families over `S`
  as a morphism from the trivial deformation to a deformation over `𝟙 S`, so that the
  functoriality of [Stacks, Tag 0D4F] applies to it.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.polarizedIsoSectionBijection`.
* `…PolarizedIsoOver.ofSectionsIso_sectionsIso`, `…PolarizedIsoOver.sectionsIso_ofSectionsIso`:
  the two composites.
* `…ProjectiveDeformation.algebraPullbackSheafHom_app_unitApp_eq`: for a morphism of deformations
  whose polarization is the one transported along an algebra map `γ`, `γ` agrees with
  `algebraPullbackSheafHom` in degrees `≥ d₀`.

## Implementation notes

The construction of `ofSectionsIso` (`projHomOfSectionsIso`, `totalIsoOfSectionsIso`,
`polarizationOfSectionsIso`) is the two-family form of the assembly `projHomOfAlgebraIso`,
`totalIsoOfAlgebraIso`, `polarizationIsoOfAlgebraIso` of
`StacksFrontier/AlgebraicGeometry/ProjectiveDeformation/IsoOfAlgebraIso.lean`, which is stated for
two deformations of one family at the cut `P.degreeBound`; here the two families differ and the
cut is arbitrary, and the general results of that file (`isPullback_projBaseChangeOfAlgebraHom`,
`isIso_baseChangeTwistHom_app`) are applied directly.

An isomorphism `φ` of polarized families is a morphism from the trivial deformation of `(f, ℒ)` to
the deformation `deformationOfIsoOver φ`, whose `r'` and `θ'` are those of `(g, ℳ)`. These agree
only definitionally, and comparing composites of morphisms of modules that agree only after
unfolding is very expensive for the elaborator and the kernel. All such comparisons are therefore
routed through lemmas stated for free variables and proved by `subst`
(`heq_polarizationOfFactorization`, `heq_baseChangeTwistHom_app_of_heq`, …), in the manner of
`StacksFrontier/AlgebraicGeometry/ProjectiveDeformation/HomExtOfAlgebraPullback.lean`, and the
polarization is built by the generic `polarizationOfFactorization` so that its defining equation is
an instance of a lemma about free variables.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.GradedIsomScheme
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU Otw twD
  preimage_toBase_le_of_comp)
open MonoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation
open SectionRingBaseChange PolarizedFamily PolarizedFamily.AdmissibleDeformation

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- The polarized family `(f, ℒ)` over a quasi-compact base, assembled from its hypotheses. -/
abbrev PolarizedFamily.ofMorphism {S X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsProper f]
    [Flat f] [Stacks.Ample.IsInvertibleModule X L] [CompactSpace S]
    (hfp : _root_.AlgebraicGeometry.FinitePresentation f)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : PolarizedFamily.{u} where
  X := X
  S := S
  f := f
  L := L
  isProper := inferInstance
  flat := inferInstance
  finitePresentation := hfp
  invertible := inferInstance
  isRelativelyAmple := hL
  compactSpace := inferInstance

namespace PolarizedIsoOver

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules}

/-- The identity isomorphism of a polarized family over its base. -/
def refl (f : X ⟶ S) (L : X.Modules) : PolarizedIsoOver f f L L where
  iso := Iso.refl X
  comm := Category.id_comp f
  pol := (Scheme.Modules.pullbackId X).app L

/-- The square of an isomorphism of polarized families over `𝟙 S` is cartesian. -/
theorem isPullback (φ : PolarizedIsoOver f g L M) : IsPullback φ.iso.hom f g (𝟙 S) :=
  IsPullback.of_horiz_isIso ⟨by rw [φ.comm, Category.comp_id]⟩

/-- An isomorphism of polarized families lies over `𝟙 S`. -/
theorem hom_comp_eq (φ : PolarizedIsoOver f g L M) : φ.iso.hom ≫ g = f ≫ 𝟙 S := by
  rw [φ.comm, Category.comp_id]

end PolarizedIsoOver

/-- **The deformation of `P` along an isomorphism over its base.** For a family `g : Y ⟶ S` and
an isomorphism `φ` of polarized families from `(P.f, P.L)` to `(g, ℳ)` over `S`, the trivial
thickening `𝟙 S` together with the cartesian square of `φ` and the lifted polarization `ℳ`. -/
abbrev PolarizedFamily.deformationOfIsoOver (P : PolarizedFamily.{u}) {Y : Scheme.{u}}
    {g : Y ⟶ P.S} [IsProper g] [Flat g] (hfp : _root_.AlgebraicGeometry.FinitePresentation g)
    {M : Y.Modules} [Stacks.Ample.IsInvertibleModule Y M] (φ : PolarizedIsoOver P.f g P.L M) :
    P.AdmissibleDeformation where
  S' := P.S
  X' := Y
  i := 𝟙 P.S
  i' := φ.iso.hom
  f' := g
  isThickening := ⟨inferInstance, Function.surjective_id⟩
  isPullback := φ.isPullback
  isProper := inferInstance
  flat := inferInstance
  finitePresentation := hfp
  L' := M
  invertible := inferInstance
  polarization := φ.pol.symm

/-- The trivial deformation of a polarized family: the deformation along the identity. -/
abbrev PolarizedFamily.trivialDeformation (P : PolarizedFamily.{u}) : P.AdmissibleDeformation :=
  P.deformationOfIsoOver P.finitePresentation (PolarizedIsoOver.refl P.f P.L)

/-- **An isomorphism of polarized families over `S` as a morphism of deformations** from the
trivial deformation of `P` to the deformation along it, over `𝟙 S`. -/
abbrev PolarizedFamily.homOfIsoOver (P : PolarizedFamily.{u}) {Y : Scheme.{u}} {g : Y ⟶ P.S}
    [IsProper g] [Flat g] (hfp : _root_.AlgebraicGeometry.FinitePresentation g) {M : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y M] (φ : PolarizedIsoOver P.f g P.L M) :
    Hom P.trivialDeformation (P.deformationOfIsoOver hfp φ) where
  base := 𝟙 P.S
  total := φ.iso.hom
  isPullback := φ.isPullback
  base_comm := Category.comp_id _
  total_comm := Category.id_comp _
  polarization := φ.pol

section Bijective

variable {Y' Y : Scheme.{u}} (q : Y' ⟶ Y) [IsIso q] (M : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y M] (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M')

open Stacks.RingedSpace Stacks.SheafOfModules.TensorPower Stacks.TensorPowerPullback
  RingedSpaceModuleAdjunction in
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory in
/-- **Along an isomorphism, pulling back sections of the tensor powers is bijective**, for any
comparison `ε : q^*ℳ ≅ ℳ'` and an open whose inverse image is the target open. -/
theorem bijective_sectionPull_of_isIso (n : ℤ) (W : Y.Opens) (V' : Y'.Opens)
    (h : V' ≤ q ⁻¹ᵁ W) (h' : q ⁻¹ᵁ W ≤ V') :
    Function.Bijective (sectionPull q M M' ε n W V' h) := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y M
  have := isInvertible_tensorPower_of_isInvertibleModule Y' M'
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  have := isEquivalence_tensorRightFunctor Y.toRingedSpace.presheaf
    (isSheafStructure Y.toRingedSpace) M
  have hW : q ''ᵁ (q ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have h1 := bijective_pullbackUnit_of_isOpenImmersion q
    (tensorPower Y.toRingedSpace.presheaf (isSheafStructure Y.toRingedSpace) M n) W hW
  have h2 := bijective_iso_hom_app (pullbackIntPowIso q.toLRSHom.toShHom M n)
    ((opensMap q.toLRSHom.toShHom).op.obj (op W))
  have h3 := bijective_map_homOfLE_of_eq (tensorPower Y'.toRingedSpace.presheaf
    (isSheafStructure Y'.toRingedSpace) ((pullbackFunctor q.toLRSHom.toShHom).obj M) n) h h'
  have h4 := bijective_iso_hom_app
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n) (op V')
  exact h4.comp (h3.comp (h2.comp h1))

end Bijective

/-- The identity of a scheme acts as the identity on global functions. -/
theorem appLE_id_top (S : Scheme.{u}) :
    Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top = 𝟙 Γ(S, ⊤) :=
  (Scheme.Hom.appLE_eq_app (𝟙 S) (U := ⊤)).trans (Scheme.Hom.id_app ⊤)

/-- The identity of a scheme acts as the identity on global functions, elementwise. -/
theorem appLE_id_top_apply (S : Scheme.{u}) (r : Γ(S, ⊤)) :
    Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top r = r := by
  rw [appLE_id_top]
  rfl

namespace PolarizedIsoOver

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M]
    (d₀ : ℕ) (hd₀ : 0 < d₀) (φ : PolarizedIsoOver f g L M)

/-- The pullback of global sections along an isomorphism of polarized families over `𝟙 S` is
`Γ(S, 𝒪_S)`-linear. -/
theorem tailMapApp_smul_top (n : ℕ) (r : Γ(S, ⊤))
    (x : Γ((tailAlgebra g M d₀ hd₀).piece (n : ℤ), ⊤)) :
    tailMapApp _ _ d₀ d₀ hd₀ hd₀ le_rfl ⊤ ⊤ (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom
        (squarePieceMap φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top) n (r • x) =
      r • (show Γ((tailAlgebra f L d₀ hd₀).piece (n : ℤ), ⊤) from
        tailMapApp _ _ d₀ d₀ hd₀ hd₀ le_rfl ⊤ ⊤ (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom
        (squarePieceMap φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top) n x) := by
  have h := tailMapApp_smul φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol d₀ hd₀ ⊤ le_top n r x
  rw [appLE_id_top_apply] at h
  exact h

/-- **Pulling global sections back along an isomorphism of polarized families**, as a homomorphism
of the global sections data of the truncated section algebras: `tailMapApp` of `squarePieceMap`
for the square of `φ` over `𝟙 S`. -/
def sectionsHom : GradedMulDatum.Hom (tailAlgebra g M d₀ hd₀).globalDatum
    (tailAlgebra f L d₀ hd₀).globalDatum where
  app n :=
    { toFun := tailMapApp _ _ d₀ d₀ hd₀ hd₀ le_rfl ⊤ ⊤ (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom
        (squarePieceMap φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top) n
      map_add' := map_add _
      map_smul' := φ.tailMapApp_smul_top d₀ hd₀ n }
  app_mul i j a b := tailMapApp_mul
    (fun n r x => squarePieceMap_smul φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top n r x)
    (fun n m _ _ x y => squarePieceMap_mul φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top
      n m x y) (i : ℤ) (j : ℤ) a b
  app_one := by
    change tailMapApp _ _ d₀ d₀ hd₀ hd₀ le_rfl ⊤ ⊤ (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom
      (squarePieceMap φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top) 0
        ((tailAlgebra g M d₀ hd₀).one ⊤) = (tailAlgebra f L d₀ hd₀).one ⊤
    exact tailMapApp_one

/-- The value of `sectionsHom` on a global section of degree `n`. -/
theorem sectionsHom_app (n : ℕ) (s : Γ((tailAlgebra g M d₀ hd₀).piece (n : ℤ), ⊤)) :
    (φ.sectionsHom d₀ hd₀).app n s =
      tailMapApp _ _ d₀ d₀ hd₀ hd₀ le_rfl ⊤ ⊤ (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom
        (squarePieceMap φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol ⊤ ⊤ le_top) n s := rfl

/-- Pulling back global sections along an isomorphism of polarized families is bijective in every
degree. -/
theorem bijective_sectionsHom_app (n : ℕ) : Function.Bijective ((φ.sectionsHom d₀ hd₀).app n) := by
  refine bijective_tailMapApp rfl ?_ (fun m _ => ?_) (n : ℤ)
  · have h : (Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_top).hom = RingHom.id _ :=
      RingHom.ext (appLE_id_top_apply S)
    rw [h]
    exact Function.bijective_id
  · exact bijective_sectionPull_of_isIso φ.iso.hom M L φ.pol m _ _ _ le_top

/-- **The isomorphism of global sections data attached to an isomorphism of polarized
families.** -/
def sectionsIso : GradedMulDatum.Iso (tailAlgebra g M d₀ hd₀).globalDatum
    (tailAlgebra f L d₀ hd₀).globalDatum :=
  GradedMulDatum.Iso.ofBijective (φ.sectionsHom d₀ hd₀) (φ.bijective_sectionsHom_app d₀ hd₀)

end PolarizedIsoOver


section PullbackId

variable {S : Scheme.{u}}

/-- The pullback of a global section of `A_n` along the identity, as a global section of the
inverse image `A.pullback (𝟙 S)`. -/
def pullbackSectionTop (A : SheafGradedAlgebra S) (n : ℤ) (a : Γ(A.piece n, ⊤)) :
    Γ((A.pullback (𝟙 S)).piece n, ⊤) :=
  Scheme.Modules.pullbackSection (𝟙 S) (A.piece n) ⊤ ⊤ le_top a

/-- `pullbackIdHom` undoes the pullback of global sections along the identity. -/
theorem pullbackIdHom_app_pullbackSectionTop (A : SheafGradedAlgebra S) (n : ℤ)
    (a : Γ(A.piece n, ⊤)) :
    ((SheafGradedAlgebraHom.pullbackIdHom A).app n).app ⊤ (pullbackSectionTop A n a) = a := by
  have h := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection (𝟙 S) (A.piece n) ⊤ ⊤
    le_top le_top a
  change (Scheme.Modules.restrictFunctorId.hom.app (A.piece n)).app ⊤
    (((Scheme.Modules.restrictFunctorIsoPullback (𝟙 S)).inv.app (A.piece n)).val.app (op ⊤)
      (Scheme.Modules.pullbackSection (𝟙 S) (A.piece n) ⊤ ⊤ le_top a)) = a
  rw [h, Scheme.Modules.restrictFunctorId_hom_app_app]
  change ((A.piece n).presheaf.map (homOfLE le_top).op ≫ (A.piece n).presheaf.map _) a = a
  rw [← Functor.map_comp]
  rw [show (homOfLE (le_top : (𝟙 S) ''ᵁ ⊤ ≤ ⊤)).op ≫
      (eqToHom (show (⊤ : S.Opens) = (𝟙 S) ''ᵁ ⊤ by simp)).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- The pullback of global sections along the identity is bijective. -/
theorem bijective_pullbackSectionTop (A : SheafGradedAlgebra S) (n : ℤ) :
    Function.Bijective (pullbackSectionTop A n) := by
  have hb : Function.Bijective (((SheafGradedAlgebraHom.pullbackIdHom A).app n).app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  refine (Function.Bijective.of_comp_iff' hb _).1 ?_
  have : ((((SheafGradedAlgebraHom.pullbackIdHom A).app n).app ⊤) ∘ pullbackSectionTop A n) = id :=
    funext (pullbackIdHom_app_pullbackSectionTop A n)
  rw [this]
  exact Function.bijective_id

end PullbackId

section Family

variable {S X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsProper f] [Flat f] [QuasiCompact f]
  [QuasiSeparated f] [Stacks.Ample.IsInvertibleModule X L] [CompactSpace S]
  (hf : _root_.AlgebraicGeometry.FinitePresentation f)
  (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- `r'` of [Stacks, Tag 0D4F] for the polarized family `(f, ℒ)` itself (its trivial deformation),
with target the relative `Proj` of `tailAlgebra f ℒ d₀`. -/
def canonicalProjHomOfMorphism : X ⟶ (relativeProj (tailAlgebra f L d₀ hd₀)).scheme :=
  (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.canonicalProjHom d₀ hd₀

/-- `r'` of `(f, ℒ)` is an isomorphism. -/
instance isIso_canonicalProjHomOfMorphism : IsIso (canonicalProjHomOfMorphism f L hf hL d₀ hd₀) :=
  (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.isIso_canonicalProjHom d₀ hd₀

/-- `r'` of `(f, ℒ)` lies over `S`. -/
theorem canonicalProjHomOfMorphism_comp_toBase :
    canonicalProjHomOfMorphism f L hf hL d₀ hd₀ ≫ (relativeProj (tailAlgebra f L d₀ hd₀)).toBase =
      f :=
  (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.canonicalProjHom_comp_toBase d₀ hd₀

/-- `θ'` of [Stacks, Tag 0D4F] for the polarized family `(f, ℒ)` itself. -/
def canonicalTwistMapOfMorphism :
    (Scheme.Modules.pullback (canonicalProjHomOfMorphism f L hf hL d₀ hd₀)).obj
      (relativeTwist (tailAlgebra f L d₀ hd₀) 1) ⟶ L :=
  (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.canonicalTwistMap d₀ hd₀

/-- `θ'` of `(f, ℒ)` is an isomorphism. -/
instance isIso_canonicalTwistMapOfMorphism :
    IsIso (canonicalTwistMapOfMorphism f L hf hL d₀ hd₀) :=
  (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.isIso_canonicalTwistMap d₀ hd₀

end Family

/-- Composites of heterogeneously equal morphisms between equal objects are heterogeneously
equal. -/
theorem heq_comp_of_heq {C : Type*} [Category C] {A A' B B' Z Z' : C} (hA : A = A')
    (hB : B = B') (hZ : Z = Z') {a : A ⟶ B} {a' : A' ⟶ B'} {k : B ⟶ Z} {k' : B' ⟶ Z'}
    (ha : HEq a a') (hk : HEq k k') : HEq (a ≫ k) (a' ≫ k') := by
  subst hA hB hZ
  cases eq_of_heq ha
  cases eq_of_heq hk
  rfl

section Factorization

variable {X₁ X₂ P₁ P₂ : Scheme.{u}} (t : X₁ ⟶ X₂) (r₁ : X₁ ⟶ P₁) (r₂ : X₂ ⟶ P₂)
  {O₂ : P₂.Modules} {O₁ : P₁.Modules} {L₂ : X₂.Modules} {L₁ : X₁.Modules}
  (θ₂ : (Scheme.Modules.pullback r₂).obj O₂ ⟶ L₂) (iθ₂ : IsIso θ₂)
  (θ₁ : (Scheme.Modules.pullback r₁).obj O₁ ⟶ L₁) (iθ₁ : IsIso θ₁) (N : P₁ ⟶ P₂)
  (τ : (Scheme.Modules.pullback N).obj O₂ ⟶ O₁) (iτ : IsIso τ) (e : t ≫ r₂ = r₁ ≫ N)

/-- The composite `t^* r₂^* O₂ ≅ (t ≫ r₂)^* O₂ ≅ (r₁ ≫ N)^* O₂ ≅ r₁^* N^* O₂ ⟶ r₁^* O₁ ⟶ L₁` read
off a factorization `t ≫ r₂ = r₁ ≫ N` and a map `τ : N^* O₂ ⟶ O₁`. -/
def factorizationTail :
    (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback r₂).obj O₂) ⟶ L₁ :=
  (Scheme.Modules.pullbackComp t r₂).hom.app O₂ ≫ (Scheme.Modules.pullbackCongr e).hom.app O₂ ≫
    (Scheme.Modules.pullbackComp r₁ N).inv.app O₂ ≫ (Scheme.Modules.pullback r₁).map τ ≫ θ₁

include iθ₁ iτ in
/-- `factorizationTail` is an isomorphism when `τ` and `θ₁` are. -/
theorem isIso_factorizationTail : IsIso (factorizationTail t r₁ r₂ θ₁ N τ e) := by
  unfold factorizationTail
  infer_instance

/-- **The polarization transported along a factorization**: `t^* L₂ ≅ t^* r₂^* O₂ ≅ L₁`, through
`θ₂⁻¹` and `factorizationTail`. This is the shape of `polarizationIsoOfAlgebraIso`. -/
def polarizationOfFactorization : (Scheme.Modules.pullback t).obj L₂ ≅ L₁ :=
  (Scheme.Modules.pullback t).mapIso (asIso θ₂).symm ≪≫
    @asIso _ _ _ _ (factorizationTail t r₁ r₂ θ₁ N τ e)
      (isIso_factorizationTail t r₁ r₂ θ₁ iθ₁ N τ iτ e)

/-- **The defining equation of `polarizationOfFactorization`**, in the shape of
`canonicalTwistMap_comp_polarization`. -/
theorem pullback_map_comp_polarizationOfFactorization_hom :
    (Scheme.Modules.pullback t).map θ₂ ≫
        (polarizationOfFactorization t r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N τ iτ e).hom =
      (Scheme.Modules.pullbackComp t r₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr e).hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁ N).inv.app O₂ ≫
        (Scheme.Modules.pullback r₁).map τ ≫ θ₁ := by
  rw [polarizationOfFactorization, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, ← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- **An isomorphism `t^* L₂ ≅ L₁` satisfying the defining equation of a
`polarizationOfFactorization` is that polarization**, all data being allowed to differ up to
equalities: the two-sided form of `heq_of_pullback_map_comp_hom_eq`. -/
theorem heq_polarizationOfFactorization {X₁ X₂ P₁ P₂ : Scheme.{u}} {t₁ t₂ : X₁ ⟶ X₂}
    (ht : t₁ = t₂) {r₁ r₁' : X₁ ⟶ P₁} (hr₁ : r₁ = r₁') {r₂ r₂' : X₂ ⟶ P₂} (hr : r₂ = r₂')
    {O₂ : P₂.Modules} {O₁ : P₁.Modules} {L₂ : X₂.Modules} {L₁ : X₁.Modules}
    (θ₂ : (Scheme.Modules.pullback r₂).obj O₂ ⟶ L₂) (iθ₂ : IsIso θ₂)
    (θ₂' : (Scheme.Modules.pullback r₂').obj O₂ ⟶ L₂) (hθ : HEq θ₂ θ₂')
    (θ₁ : (Scheme.Modules.pullback r₁).obj O₁ ⟶ L₁) (iθ₁ : IsIso θ₁)
    (θ₁' : (Scheme.Modules.pullback r₁').obj O₁ ⟶ L₁) (hθ₁ : HEq θ₁ θ₁') {N₁ N₂ : P₁ ⟶ P₂}
    (hN : N₁ = N₂) {τ₁ : (Scheme.Modules.pullback N₁).obj O₂ ⟶ O₁} (iτ₁ : IsIso τ₁)
    {τ₂ : (Scheme.Modules.pullback N₂).obj O₂ ⟶ O₁} (hτ : HEq τ₁ τ₂)
    (e₁ : t₁ ≫ r₂ = r₁ ≫ N₁) (e₂ : t₂ ≫ r₂' = r₁' ≫ N₂)
    (pol₂ : (Scheme.Modules.pullback t₂).obj L₂ ≅ L₁)
    (h₂ : (Scheme.Modules.pullback t₂).map θ₂' ≫ pol₂.hom =
      (Scheme.Modules.pullbackComp t₂ r₂').hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr e₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁' N₂).inv.app O₂ ≫
        (Scheme.Modules.pullback r₁').map τ₂ ≫ θ₁') :
    HEq (polarizationOfFactorization t₁ r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N₁ τ₁ iτ₁ e₁) pol₂ := by
  subst ht hr hN hr₁
  cases eq_of_heq hθ
  cases eq_of_heq hτ
  cases eq_of_heq hθ₁
  refine heq_of_eq (Iso.ext ?_)
  rw [← cancel_epi ((Scheme.Modules.pullback t₁).map θ₂),
    pullback_map_comp_polarizationOfFactorization_hom t₁ r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N₁ τ₁ iτ₁ e₁, h₂]

end Factorization

/-- The map of Serre twists along a base change depends only on the algebra map, up to equalities
of the bases and of the algebras. -/
theorem heq_baseChangeTwistHom_app_of_heq {S₁ S₂ T₁ T₂ : Scheme.{u}} (hS : S₁ = S₂)
    (hT : T₁ = T₂) {A₁ : SheafGradedAlgebra S₁} {A₂ : SheafGradedAlgebra S₂} (hA : HEq A₁ A₂)
    {g₁ : T₁ ⟶ S₁} {g₂ : T₂ ⟶ S₂} (hg : HEq g₁ g₂) {B₁ : SheafGradedAlgebra T₁}
    {B₂ : SheafGradedAlgebra T₂} (hB : HEq B₁ B₂)
    {ψ₁ : SheafGradedAlgebraHom (A₁.pullback g₁) B₁}
    {ψ₂ : SheafGradedAlgebraHom (A₂.pullback g₂) B₂}
    (hψ : HEq ψ₁ ψ₂) (h₁ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₁.app (d : ℤ)))
    (h₂ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₂.app (d : ℤ))) (n : ℤ) :
    HEq ((baseChangeTwistHom ψ₁ h₁).app n) ((baseChangeTwistHom ψ₂ h₂).app n) := by
  subst hS hT
  cases eq_of_heq hA
  cases eq_of_heq hg
  cases eq_of_heq hB
  cases eq_of_heq hψ
  rfl

/-- The morphism `Proj(B) ⟶ Proj(g^*A) ⟶ Proj(A)` depends only on the algebra map, up to equalities
of the bases and of the algebras. -/
theorem projMapOfEventuallyIso_comp_baseChangeHom_of_heq {S₁ S₂ T₁ T₂ : Scheme.{u}}
    (hS : S₁ = S₂) (hT : T₁ = T₂) {A₁ : SheafGradedAlgebra S₁} {A₂ : SheafGradedAlgebra S₂}
    (hA : HEq A₁ A₂) {g₁ : T₁ ⟶ S₁} {g₂ : T₂ ⟶ S₂} (hg : HEq g₁ g₂) {B₁ : SheafGradedAlgebra T₁}
    {B₂ : SheafGradedAlgebra T₂} (hB : HEq B₁ B₂)
    {ψ₁ : SheafGradedAlgebraHom (A₁.pullback g₁) B₁}
    {ψ₂ : SheafGradedAlgebraHom (A₂.pullback g₂) B₂}
    (hψ : HEq ψ₁ ψ₂) (h₁ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₁.app (d : ℤ)))
    (h₂ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₂.app (d : ℤ))) :
    HEq (projMapOfEventuallyIso ψ₁ h₁ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A₁ g₁)
      (projMapOfEventuallyIso ψ₂ h₂ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A₂ g₂) := by
  subst hS hT
  cases eq_of_heq hA
  cases eq_of_heq hg
  cases eq_of_heq hB
  cases eq_of_heq hψ
  rfl

/-- **The polarization of a morphism of deformations is the polarization transported along the
factorization `r'₁ ≫ M = φ.total ≫ r'₂`**, by `canonicalTwistMap_comp_polarization`, all data being
allowed to differ from the canonical ones up to equalities. -/
theorem heq_polarizationOfFactorization_polarization {P : PolarizedFamily.{u}}
    {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ) (hd₀ : 0 < d₀)
    (hiso : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n))
    {t : D₁.X' ⟶ D₂.X'} (ht : t = φ.total)
    {r₁ : D₁.X' ⟶ (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).scheme}
    (hr₁ : r₁ = D₁.canonicalProjHom d₀ hd₀)
    {r₂ : D₂.X' ⟶ (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).scheme}
    (hr₂ : r₂ = D₂.canonicalProjHom d₀ hd₀)
    (θ₂ : (Scheme.Modules.pullback r₂).obj (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      D₂.L') (iθ₂ : IsIso θ₂) (hθ₂ : HEq θ₂ (D₂.canonicalTwistMap d₀ hd₀))
    (θ₁ : (Scheme.Modules.pullback r₁).obj (relativeTwist (D₁.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      D₁.L') (iθ₁ : IsIso θ₁) (hθ₁ : HEq θ₁ (D₁.canonicalTwistMap d₀ hd₀))
    {N : (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).scheme ⟶
      (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).scheme}
    (hN : N = projBaseChangeHom φ d₀ hd₀ hiso)
    {τ : (Scheme.Modules.pullback N).obj (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      relativeTwist (D₁.truncatedSectionAlgebra d₀ hd₀) 1} (iτ : IsIso τ)
    (hτ : HEq τ (projBaseChangeTwistMap φ d₀ hd₀ hiso)) (e : t ≫ r₂ = r₁ ≫ N) :
    HEq (polarizationOfFactorization t r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N τ iτ e) φ.polarization := by
  subst ht hr₁ hr₂ hN
  exact heq_polarizationOfFactorization rfl rfl rfl θ₂ iθ₂ _ hθ₂ θ₁ iθ₁ _ hθ₁ rfl iτ hτ e
    (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hiso).symm φ.polarization
    (canonicalTwistMap_comp_polarization φ d₀ hd₀ hiso)

/-- The defining equation of `polarizationOfFactorization` transported along equalities of its
data. -/
theorem pullback_map_comp_eq_of_heq_polarizationOfFactorization {X₁ X₂ P₁ P₂ : Scheme.{u}}
    {t t' : X₁ ⟶ X₂} (ht : t = t') {r₁ r₁' : X₁ ⟶ P₁} (hr₁ : r₁ = r₁') {r₂ r₂' : X₂ ⟶ P₂}
    (hr₂ : r₂ = r₂') {O₂ : P₂.Modules} {O₁ : P₁.Modules} {L₂ : X₂.Modules} {L₁ : X₁.Modules}
    (θ₂ : (Scheme.Modules.pullback r₂).obj O₂ ⟶ L₂) (iθ₂ : IsIso θ₂)
    {θ₂' : (Scheme.Modules.pullback r₂').obj O₂ ⟶ L₂} (hθ₂ : HEq θ₂ θ₂')
    (θ₁ : (Scheme.Modules.pullback r₁).obj O₁ ⟶ L₁) (iθ₁ : IsIso θ₁)
    {θ₁' : (Scheme.Modules.pullback r₁').obj O₁ ⟶ L₁} (hθ₁ : HEq θ₁ θ₁') {N N' : P₁ ⟶ P₂}
    (hN : N = N') (τ : (Scheme.Modules.pullback N).obj O₂ ⟶ O₁) (iτ : IsIso τ)
    {τ' : (Scheme.Modules.pullback N').obj O₂ ⟶ O₁} (hτ : HEq τ τ')
    (e : t ≫ r₂ = r₁ ≫ N) (e' : t' ≫ r₂' = r₁' ≫ N')
    (pol' : (Scheme.Modules.pullback t').obj L₂ ≅ L₁)
    (hpol : HEq (polarizationOfFactorization t r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N τ iτ e) pol') :
    (Scheme.Modules.pullback t').map θ₂' ≫ pol'.hom =
      (Scheme.Modules.pullbackComp t' r₂').hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr e').hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁' N').inv.app O₂ ≫
        (Scheme.Modules.pullback r₁').map τ' ≫ θ₁' := by
  subst ht hr₁ hr₂ hN
  cases eq_of_heq hθ₂
  cases eq_of_heq hθ₁
  cases eq_of_heq hτ
  cases eq_of_heq hpol
  exact pullback_map_comp_polarizationOfFactorization_hom t r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N τ iτ e

/-- **If the polarization of a morphism of deformations is a `polarizationOfFactorization` along an
algebra map `γ`, it satisfies the equation of `canonicalTwistMap_comp_polarization` for `γ`.** -/
theorem pullback_map_comp_polarization_of_heq_polarizationOfFactorization
    {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ)
    (hd₀ : 0 < d₀)
    (γ : SheafGradedAlgebraHom ((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base)
      (D₁.truncatedSectionAlgebra d₀ hd₀))
    (hγ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (γ.app (d : ℤ)))
    {t : D₁.X' ⟶ D₂.X'} (ht : t = φ.total)
    {r₁ : D₁.X' ⟶ (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).scheme}
    (hr₁ : r₁ = D₁.canonicalProjHom d₀ hd₀)
    {r₂ : D₂.X' ⟶ (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).scheme}
    (hr₂ : r₂ = D₂.canonicalProjHom d₀ hd₀)
    (θ₂ : (Scheme.Modules.pullback r₂).obj (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      D₂.L') (iθ₂ : IsIso θ₂) (hθ₂ : HEq θ₂ (D₂.canonicalTwistMap d₀ hd₀))
    (θ₁ : (Scheme.Modules.pullback r₁).obj (relativeTwist (D₁.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      D₁.L') (iθ₁ : IsIso θ₁) (hθ₁ : HEq θ₁ (D₁.canonicalTwistMap d₀ hd₀))
    {N : (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).scheme ⟶
      (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).scheme}
    (hN : N = projMapOfEventuallyIso γ hγ ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)
    {τ : (Scheme.Modules.pullback N).obj (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      relativeTwist (D₁.truncatedSectionAlgebra d₀ hd₀) 1} (iτ : IsIso τ)
    (hτ : HEq τ ((baseChangeTwistHom γ hγ).app 1)) (e : t ≫ r₂ = r₁ ≫ N)
    (e₀ : φ.total ≫ D₂.canonicalProjHom d₀ hd₀ = D₁.canonicalProjHom d₀ hd₀ ≫
      (projMapOfEventuallyIso γ hγ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base))
    (hpol : HEq (polarizationOfFactorization t r₁ r₂ θ₂ iθ₂ θ₁ iθ₁ N τ iτ e) φ.polarization) :
    (Scheme.Modules.pullback φ.total).map (D₂.canonicalTwistMap d₀ hd₀) ≫
        φ.polarization.hom =
      (Scheme.Modules.pullbackComp φ.total (D₂.canonicalProjHom d₀ hd₀)).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullbackCongr e₀).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullbackComp (D₁.canonicalProjHom d₀ hd₀)
          (projMapOfEventuallyIso γ hγ ≫
            Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
            (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)).inv.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullback (D₁.canonicalProjHom d₀ hd₀)).map
          ((baseChangeTwistHom γ hγ).app 1) ≫
        D₁.canonicalTwistMap d₀ hd₀ := by
  subst ht hr₁ hr₂ hN
  exact pullback_map_comp_eq_of_heq_polarizationOfFactorization rfl rfl rfl θ₂ iθ₂ hθ₂ θ₁ iθ₁ hθ₁
    rfl τ iτ hτ e e₀ φ.polarization hpol

/-- `(a⁻¹ ≫ b) ≫ (b⁻¹ ≫ a) = 𝟙`. -/
theorem inv_comp_hom_comp_inv_comp_hom {C : Type*} [Category C] {A B Z : C} (a : A ≅ B)
    (b : A ≅ Z) : (a.inv ≫ b.hom) ≫ b.inv ≫ a.hom = 𝟙 B := by
  simp

/-- **The converse of `final_square`**: the equation of a polarization in degree one, read back in
the families of `TwistSections`. -/
theorem eq_of_final_square {X₁ X₂ P₁ P₂ : Scheme.{u}} (q : X₁ ⟶ X₂) (r₁ r₁' : X₁ ⟶ P₁)
    (h₁ : r₁ = r₁') (r₂ r₂' : X₂ ⟶ P₂) (h₂ : r₂ = r₂') (N N' : P₁ ⟶ P₂) (hN : N = N')
    (hsq : q ≫ r₂ = r₁ ≫ N) (hsq' : q ≫ r₂' = r₁' ≫ N')
    {O₂ : P₂.Modules} {O₁ : P₁.Modules} {L₂ T₂ : X₂.Modules} {L₁ T₁ : X₁.Modules}
    (θ₂ : (Scheme.Modules.pullback r₂).obj O₂ ⟶ L₂) (t₂ : (Scheme.Modules.pullback r₂').obj O₂ ⟶ T₂)
    (κ₂ : T₂ ⟶ L₂) (e₂ : θ₂ = (Scheme.Modules.pullbackCongr h₂).hom.app O₂ ≫ t₂ ≫ κ₂)
    (θ₁ : (Scheme.Modules.pullback r₁).obj O₁ ⟶ L₁) (t₁ : (Scheme.Modules.pullback r₁').obj O₁ ⟶ T₁)
    (κ₁ : T₁ ⟶ L₁) (κ₁' : L₁ ⟶ T₁) (hκ₁ : κ₁ ≫ κ₁' = 𝟙 T₁)
    (e₁ : θ₁ = (Scheme.Modules.pullbackCongr h₁).hom.app O₁ ≫ t₁ ≫ κ₁)
    (τ : (Scheme.Modules.pullback N).obj O₂ ⟶ O₁) (τ' : (Scheme.Modules.pullback N').obj O₂ ⟶ O₁)
    (eτ : τ = (Scheme.Modules.pullbackCongr hN).hom.app O₂ ≫ τ')
    (pol : (Scheme.Modules.pullback q).obj L₂ ⟶ L₁) (pp : (Scheme.Modules.pullback q).obj T₂ ⟶ T₁)
    (hk : (Scheme.Modules.pullback q).map κ₂ ≫ pol = pp ≫ κ₁)
    (hpol : (Scheme.Modules.pullback q).map θ₂ ≫ pol =
      (Scheme.Modules.pullbackComp q r₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr hsq).hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁ N).inv.app O₂ ≫
        (Scheme.Modules.pullback r₁).map τ ≫ θ₁) :
    (Scheme.Modules.pullbackComp q r₂').inv.app O₂ ≫ (Scheme.Modules.pullback q).map t₂ ≫ pp =
      (Scheme.Modules.pullbackCongr hsq').hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁' N').inv.app O₂ ≫
        (Scheme.Modules.pullback r₁').map τ' ≫ t₁ := by
  subst h₁ h₂ hN e₂ e₁ eτ
  simp only [pullbackCongr_rfl_hom_app, Category.id_comp] at hpol ⊢
  have : IsSplitMono κ₁ := IsSplitMono.mk' ⟨κ₁', hκ₁⟩
  rw [← cancel_mono κ₁]
  simp only [Category.assoc]
  rw [← hk, ← Functor.map_comp_assoc, hpol, Iso.inv_hom_id_app_assoc]

/-- `a⁻¹ ≫ b` is an isomorphism. -/
theorem isIso_inv_comp_hom {C : Type*} [Category C] {A B Z : C} (a : A ≅ B) (b : A ≅ Z) :
    IsIso (a.inv ≫ b.hom) :=
  ⟨⟨b.inv ≫ a.hom, by simp, by simp⟩⟩

/-- `θ'` in degree one, `canonicalTwistPow 1`, is an isomorphism. -/
theorem isIso_canonicalTwistPow_one {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation)
    (d₀ : ℕ) (hd₀ : 0 < d₀) : IsIso (D.canonicalTwistPow d₀ hd₀ 1) := by
  have hcomp : IsIso (D.canonicalTwistPow d₀ hd₀ 1 ≫
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D.L' 1).inv ≫ (λ_ D.L').hom) := by
    rw [← D.canonicalTwistMap_eq d₀ hd₀]
    exact D.isIso_canonicalTwistMap d₀ hd₀
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_inv_comp_hom _ _) hcomp

section RoundTrip

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ)
  (hd₀ : 0 < d₀)
  (γ : SheafGradedAlgebraHom ((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base)
    (D₁.truncatedSectionAlgebra d₀ hd₀))
  (hγ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (γ.app (d : ℤ)))
  (e : φ.total ≫ canonicalProjHom' d₀ hd₀ D₂ = canonicalProjHom' d₀ hd₀ D₁ ≫
    (projMapOfEventuallyIso γ hγ ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base))

/-- **The second family of `TwistSections` for an algebra map `γ : g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`**: the map
of Serre twists along `Proj(𝒜'(D₁)) ⟶ Proj(𝒜'(D₂))` attached to `γ`, pulled back along `r'₁`,
followed by `θ'₁`. For `γ = algebraPullbackSheafHom φ` this is `twistFamily₂`. -/
def algebraTwistFamily (n : ℤ) :
    (Scheme.Modules.pullback (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)).obj
        (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ⟶ tensorPowerModule D₁.X' D₁.L' n :=
  TwistSections.congrFamily D₁.L' e
    (TwistSections.comp₂ D₁.L' (canonicalProjHom' d₀ hd₀ D₁)
      (projMapOfEventuallyIso γ hγ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)
      (baseChangeTwistHom γ hγ) (D₁.canonicalTwistPow d₀ hd₀)) n

/-- `algebraTwistFamily` is multiplicative on inverse images of sections. -/
theorem algebraTwistFamily_unitMul :
    TwistSections.UnitMul D₁.L' (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
      (twistAlgebra (D₂.truncatedSectionAlgebra d₀ hd₀)) (algebraTwistFamily φ d₀ hd₀ γ hγ e) :=
  TwistSections.congrFamily_unitMul D₁.L' _ _
    (TwistSections.comp₂_unitMul D₁.L' _ _ _ _ (D₁.canonicalTwistPow_unitMul d₀ hd₀))

/-- `algebraTwistFamily` as the composite it is defined to be. -/
theorem algebraTwistFamily_eq_def (n : ℤ) :
    algebraTwistFamily φ d₀ hd₀ γ hγ e n =
      (Scheme.Modules.pullbackCongr e).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ≫
        (Scheme.Modules.pullbackComp (canonicalProjHom' d₀ hd₀ D₁)
          (projMapOfEventuallyIso γ hγ ≫
            Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
            (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)).inv.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ≫
        (Scheme.Modules.pullback (canonicalProjHom' d₀ hd₀ D₁)).map
          ((baseChangeTwistHom γ hγ).app n) ≫
        D₁.canonicalTwistPow d₀ hd₀ n :=
  by unfold algebraTwistFamily TwistSections.congrFamily TwistSections.comp₂; rfl

/-- **In degree one the two families agree** as soon as the polarization of `φ` satisfies the
equation of `canonicalTwistMap_comp_polarization` for `γ`. -/
theorem twistFamily₁_one_eq_algebraTwistFamily
    (e₀ : φ.total ≫ D₂.canonicalProjHom d₀ hd₀ = D₁.canonicalProjHom d₀ hd₀ ≫
      (projMapOfEventuallyIso γ hγ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base))
    (hpol : (Scheme.Modules.pullback φ.total).map (D₂.canonicalTwistMap d₀ hd₀) ≫
        φ.polarization.hom =
      (Scheme.Modules.pullbackComp φ.total (D₂.canonicalProjHom d₀ hd₀)).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullbackCongr e₀).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullbackComp (D₁.canonicalProjHom d₀ hd₀)
          (projMapOfEventuallyIso γ hγ ≫
            Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
            (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)).inv.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullback (D₁.canonicalProjHom d₀ hd₀)).map
          ((baseChangeTwistHom γ hγ).app 1) ≫
        D₁.canonicalTwistMap d₀ hd₀) :
    twistFamily₁ φ d₀ hd₀ 1 = algebraTwistFamily φ d₀ hd₀ γ hγ e 1 := by
  rw [twistFamily₁_eq_def, algebraTwistFamily_eq_def]
  have hk := TwistSections.pullback_kappa_comp φ.total D₂.L' D₁.L' φ.polarization
  have e₂ : D₂.canonicalTwistMap d₀ hd₀ =
      (Scheme.Modules.pullbackCongr (rfl : D₂.canonicalProjHom d₀ hd₀ =
        canonicalProjHom' d₀ hd₀ D₂)).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        D₂.canonicalTwistPow d₀ hd₀ 1 ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₂.L' 1).inv ≫ (λ_ D₂.L').hom := by
    rw [pullbackCongr_rfl_hom_app, Category.id_comp]
    exact D₂.canonicalTwistMap_eq d₀ hd₀
  have e₁ : D₁.canonicalTwistMap d₀ hd₀ =
      (Scheme.Modules.pullbackCongr (rfl : D₁.canonicalProjHom d₀ hd₀ =
        canonicalProjHom' d₀ hd₀ D₁)).hom.app
          (relativeTwist (D₁.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        D₁.canonicalTwistPow d₀ hd₀ 1 ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' 1).inv ≫ (λ_ D₁.L').hom := by
    rw [pullbackCongr_rfl_hom_app, Category.id_comp]
    exact D₁.canonicalTwistMap_eq d₀ hd₀
  have eτ : (baseChangeTwistHom γ hγ).app 1 =
      (Scheme.Modules.pullbackCongr (rfl : (projMapOfEventuallyIso γ hγ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
          (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base) = _)).hom.app
        (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
          (baseChangeTwistHom γ hγ).app 1 := by
    rw [pullbackCongr_rfl_hom_app]
    exact (Category.id_comp _).symm
  exact eq_of_final_square φ.total (D₁.canonicalProjHom d₀ hd₀) (canonicalProjHom' d₀ hd₀ D₁) rfl
    (D₂.canonicalProjHom d₀ hd₀) (canonicalProjHom' d₀ hd₀ D₂) rfl _ _ rfl e₀ e
    (D₂.canonicalTwistMap d₀ hd₀) (D₂.canonicalTwistPow d₀ hd₀ 1) _ e₂
    (D₁.canonicalTwistMap d₀ hd₀) (D₁.canonicalTwistPow d₀ hd₀ 1) _
    ((λ_ D₁.L').inv ≫ (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' 1).hom)
    (inv_comp_hom_comp_inv_comp_hom _ _) e₁
    ((baseChangeTwistHom γ hγ).app 1) _ eτ φ.polarization.hom
    (TwistSections.polPow D₂.L' φ.total D₁.L' φ.polarization 1) hk hpol

/-- **`algebraTwistFamily` on the sections attached to homogeneous elements**: the inverse image of
`ψ(a)` goes to `γ(g^* a)` read in `(ℒ'₁)^{⊗ d}`. -/
theorem algebraTwistFamily_app_unitApp_psiU (V : D₂.S'.Opens) (d : ℕ)
    (a : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ), V)) :
    (algebraTwistFamily φ d₀ hd₀ γ hγ e d).app ((φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) ⁻¹ᵁ
        ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V))
        (unitApp (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) d)
          ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
          (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)) =
      (tensorPowerModule D₁.X' D₁.L' d).presheaf.map
        (homOfLE (((TwistSections.preimage_le_of_eq e
          ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)).trans
          ((canonicalProjHom' d₀ hd₀ D₁).preimage_mono (baseChangeTwist_preimage_le γ hγ V))).trans
          (D₁.canonicalProjHom_preimage_le d₀ hd₀ (φ.base ⁻¹ᵁ V)))).op
        (show Γ(tensorPowerModule D₁.X' D₁.L' d, D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) from
          ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
            ((γ.app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
              (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))) := by
  have e1 := TwistSections.congrFamily_app D₁.L' e
    (TwistSections.comp₂ D₁.L' (canonicalProjHom' d₀ hd₀ D₁)
      (projMapOfEventuallyIso γ hγ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)
      (baseChangeTwistHom γ hγ) (D₁.canonicalTwistPow d₀ hd₀)) d
    ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
    (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)
  have e2 := TwistSections.comp₂_app_eq D₁.L' (canonicalProjHom' d₀ hd₀ D₁)
    (projMapOfEventuallyIso γ hγ ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)
    (baseChangeTwistHom γ hγ) (D₁.canonicalTwistPow d₀ hd₀) d
    ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
    (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)
    (psiU (D₁.truncatedSectionAlgebra d₀ hd₀) d (φ.base ⁻¹ᵁ V)
      ((γ.app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
        (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a)))
    (baseChangeTwist_preimage_le _ _ V) (baseChangeTwistHom_app_unitApp_psiU _ _ d V a)
  have e3 := D₁.canonicalTwistPow_app_unitApp_psiU d₀ hd₀ d (φ.base ⁻¹ᵁ V)
    ((γ.app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
      (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))
  have t1 : algebraTwistFamily φ d₀ hd₀ γ hγ e d = TwistSections.congrFamily D₁.L' e
      (TwistSections.comp₂ D₁.L' (canonicalProjHom' d₀ hd₀ D₁)
        (projMapOfEventuallyIso γ hγ ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
          (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)
        (baseChangeTwistHom γ hγ) (D₁.canonicalTwistPow d₀ hd₀)) d := rfl
  rw [t1]
  rw [e1]
  rw [e2, e3]
  exact (congrArg _ (map_map_homOfLE _
    ((canonicalProjHom' d₀ hd₀ D₁).preimage_mono (baseChangeTwist_preimage_le γ hγ V))
    (D₁.canonicalProjHom_preimage_le d₀ hd₀ (φ.base ⁻¹ᵁ V))
    (((canonicalProjHom' d₀ hd₀ D₁).preimage_mono (baseChangeTwist_preimage_le γ hγ V)).trans
      (D₁.canonicalProjHom_preimage_le d₀ hd₀ (φ.base ⁻¹ᵁ V))) _)).trans
    (map_map_homOfLE _ _ _ _ _)

/-- `algebraTwistFamily` is an isomorphism in degree one. -/
theorem isIso_algebraTwistFamily_one : IsIso (algebraTwistFamily φ d₀ hd₀ γ hγ e 1) := by
  have := isIso_canonicalTwistPow_one D₁ d₀ hd₀
  have := isIso_baseChangeTwistHom_app γ hγ 1
  rw [algebraTwistFamily_eq_def]
  exact IsIso.comp_isIso' ((Scheme.Modules.pullbackCongr e).app _).isIso_hom
    (IsIso.comp_isIso' ((Scheme.Modules.pullbackComp _ _).app _).isIso_inv
      (IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_baseChangeTwistHom_app γ hγ 1))
        (isIso_canonicalTwistPow_one D₁ d₀ hd₀)))

include e in
/-- **The round trip.** If the polarization of a morphism of deformations `φ` satisfies the
equation of `canonicalTwistMap_comp_polarization` for an algebra map `γ`, then `γ` agrees with
`algebraPullbackSheafHom φ` on the pullbacks of homogeneous sections of degree `d ≥ d₀` over an
affine open: by [Stacks, Tag 01O9] the two families agree in all degrees
(`TwistDegreeOne.eq_of_unitMul_of_app_one`), and the comparison `𝒜'_d ⟶ (f'_1)_*(ℒ'_1)^{⊗ d}` is
injective. -/
theorem algebraPullbackSheafHom_app_unitApp_eq
    (e₀ : φ.total ≫ D₂.canonicalProjHom d₀ hd₀ = D₁.canonicalProjHom d₀ hd₀ ≫
      (projMapOfEventuallyIso γ hγ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base))
    (hpol : (Scheme.Modules.pullback φ.total).map (D₂.canonicalTwistMap d₀ hd₀) ≫
        φ.polarization.hom =
      (Scheme.Modules.pullbackComp φ.total (D₂.canonicalProjHom d₀ hd₀)).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullbackCongr e₀).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullbackComp (D₁.canonicalProjHom d₀ hd₀)
          (projMapOfEventuallyIso γ hγ ≫
            Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
            (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base)).inv.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (Scheme.Modules.pullback (D₁.canonicalProjHom d₀ hd₀)).map
          ((baseChangeTwistHom γ hγ).app 1) ≫
        D₁.canonicalTwistMap d₀ hd₀)
    (V : D₂.S'.Opens) (hV : IsAffineOpen V) (d : ℕ) (hd : d₀ ≤ d)
    (a : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ), V)) :
    ((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
        (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a) =
      (γ.app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
        (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a) := by
  have h1 := twistFamily₁_one_eq_algebraTwistFamily φ d₀ hd₀ γ hγ e e₀ hpol
  have := isIso_algebraTwistFamily_one φ d₀ hd₀ γ hγ e
  have hfam := TwistDegreeOne.eq_of_unitMul_of_app_one (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
    D₁.L' (algebraTwistFamily φ d₀ hd₀ γ hγ e) (twistFamily₁ φ d₀ hd₀)
    (algebraTwistFamily_unitMul φ d₀ hd₀ γ hγ e) (twistFamily₁_unitMul φ d₀ hd₀) h1.symm (d : ℤ)
  have L := twistFamily₁_app_unitApp_psiU φ d₀ hd₀ V d a
  rw [← hfam, algebraTwistFamily_app_unitApp_psiU, basePowerMap_value] at L
  have hinv := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' d) ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
    (sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V)
      ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V)
      (show Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V) from
        ((D₂.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a))
  have hT := preimage_toBase_le_of_comp
    (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) V
  have L' := L.trans (congrArg (fun z => (tensorPowerModule D₁.X' D₁.L' d).presheaf.map
    (homOfLE hT).op z) hinv)
  have hc := comparison_algebraPullbackSheafHom_pullbackSection φ d₀ hd₀
    (le_refl (φ.base ⁻¹ᵁ V)) d hd a
  have e5 : Scheme.Modules.pullbackSection φ.base
      ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V (φ.base ⁻¹ᵁ V) le_rfl a =
      unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a :=
    Stacks.Conormal.pullbackSection_self φ.base _ V a
  have hc' : (show Γ(tensorPowerModule D₁.X' D₁.L' d, D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) from
      ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
        (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
        (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))) =
      sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V)
        (D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) (preimage_comp_le_preimage_total φ V)
        (show Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V) from
          ((D₂.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a) :=
    (congrArg (fun z => ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
      (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V) z)) e5).symm.trans hc
  have hXc : (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) ⁻¹ᵁ
      ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V) ≤
      D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V) :=
    ((TwistSections.preimage_le_of_eq e
      ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)).trans
      ((canonicalProjHom' d₀ hd₀ D₁).preimage_mono (baseChangeTwist_preimage_le γ hγ V))).trans
      (D₁.canonicalProjHom_preimage_le d₀ hd₀ (φ.base ⁻¹ᵁ V))
  have hX' : D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V) ≤ (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) ⁻¹ᵁ
      ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V) := by
    refine le_of_eq ?_
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      total_comp_canonicalProjHom'_toBase]
  have key : (tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE hXc).op
      (show Γ(tensorPowerModule D₁.X' D₁.L' d, D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) from
        ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
          (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
            (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))) =
      (tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE hXc).op
      (show Γ(tensorPowerModule D₁.X' D₁.L' d, D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) from
        ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
          ((γ.app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
            (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))) :=
    (congrArg (fun z => (tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE hXc).op z)
      hc').trans L'.symm
  have := D₁.isIso_sectionAlgebraComparison_app d₀ hd₀ d hd
  exact (ConcreteCategory.bijective_of_isIso
    (((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V))).1
    ((bijective_map_homOfLE_of_eq (tensorPowerModule D₁.X' D₁.L' d) hXc hX').1 key)

end RoundTrip


section Bridge

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules}
    [IsProper f] [Flat f] [QuasiCompact f] [QuasiSeparated f]
    [IsProper g] [Flat g] [QuasiCompact g] [QuasiSeparated g]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M] [CompactSpace S]
    (hf : _root_.AlgebraicGeometry.FinitePresentation f)
    (hg : _root_.AlgebraicGeometry.FinitePresentation g)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M)
    (d₀ : ℕ) (hd₀ : 0 < d₀) (φ : PolarizedIsoOver f g L M)

/-- `r'` of the deformation along `φ` is `r'` of the target family. -/
theorem canonicalProjHom_deformationOfIsoOver :
    ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).canonicalProjHom d₀ hd₀ =
      canonicalProjHomOfMorphism g M hg hM d₀ hd₀ := rfl

/-- `θ'` of the deformation along `φ` is `θ'` of the target family. -/
theorem heq_canonicalTwistMap_deformationOfIsoOver :
    HEq (((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).canonicalTwistMap d₀
      hd₀) (canonicalTwistMapOfMorphism g M hg hM d₀ hd₀) := by
  unfold canonicalTwistMapOfMorphism
  rw [canonicalTwistMap_eq, canonicalTwistMap_eq]
  exact heq_comp_of_heq rfl rfl rfl HEq.rfl (heq_comp_of_heq rfl rfl rfl HEq.rfl HEq.rfl)

end Bridge

namespace PolarizedIsoOver

section Low

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {M : Y.Modules} [QuasiCompact g] [QuasiSeparated g]
    [Stacks.Ample.IsInvertibleModule Y M] (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- Two homomorphisms out of the global sections datum of a truncated section algebra agree in
degree zero: the degree-zero piece is `𝒪_S`, generated by the unit. -/
theorem app_zero_eq_of_tailAlgebra {N : GradedMulDatum Γ(S, ⊤)}
    (F G : GradedMulDatum.Hom (tailAlgebra g M d₀ hd₀).globalDatum N) : F.app 0 = G.app 0 := by
  refine LinearMap.ext fun s => ?_
  obtain ⟨r, hr⟩ := (SectionRingBaseChange.bijective_smul_one_tail
    (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
      (Stacks.RelativeAmple.laurentPowers M)) d₀ hd₀
    (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.isCommutative_pushforwardGradedAlgebra _ _
      (Stacks.RelativeAmple.isCommutative_laurentPowers M))
    (Stacks.RelativeAmple.isQuasicoherent_pushforward_laurentPowers g M) ⊤).2 s
  rw [← hr]
  have hF : F.app 0 ((tailAlgebra g M d₀ hd₀).one ⊤) = N.one := F.app_one
  have hG : G.app 0 ((tailAlgebra g M d₀ hd₀).one ⊤) = N.one := G.app_one
  exact ((F.app 0).map_smul r _).trans
    ((congrArg (r • ·) (hF.trans hG.symm)).trans ((G.app 0).map_smul r _).symm)

/-- Two homomorphisms out of the global sections datum of a truncated section algebra agree in the
degrees strictly between `0` and the cut, where the piece vanishes. -/
theorem app_eq_of_tailAlgebra_of_lt {N : GradedMulDatum Γ(S, ⊤)}
    (F G : GradedMulDatum.Hom (tailAlgebra g M d₀ hd₀).globalDatum N) (n : ℕ) (h0 : 0 < n)
    (hn : n < d₀) : F.app n = G.app n := by
  refine LinearMap.ext fun s => ?_
  have hs : s = 0 := Stacks.AlgebraicGeometry.SectionAlgebra.eq_zero_of_tailPiece
    (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
      (Stacks.RelativeAmple.laurentPowers M)) d₀ (show (n : ℤ) ≠ 0 by omega)
    (show ¬ (d₀ : ℤ) ≤ (n : ℤ) by omega) (op ⊤) s
  rw [hs, map_zero, map_zero]

end Low

section Standing

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules}
    [IsProper f] [Flat f] [QuasiCompact f] [QuasiSeparated f]
    [IsProper g] [Flat g] [QuasiCompact g] [QuasiSeparated g]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M] [IsAffine S]
    (hf : _root_.AlgebraicGeometry.FinitePresentation f)
    (hg : _root_.AlgebraicGeometry.FinitePresentation g)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M)
    (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- **`algebraPullbackSheafHom` of an isomorphism of polarized families on global sections** is
`sectionsHom`. -/
theorem algebraPullbackSheafHom_app_pullbackSectionTop (φ : PolarizedIsoOver f g L M) (n : ℕ)
    (a : Γ((tailAlgebra g M d₀ hd₀).piece (n : ℤ), ⊤)) :
    ((algebraPullbackSheafHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀
        hd₀).app n).app ⊤ (pullbackSectionTop _ (n : ℤ) a) = (φ.sectionsHom d₀ hd₀).app n a :=
  tailPullbackHom_app_pullbackSection φ.iso.hom g f (𝟙 S) φ.hom_comp_eq M L φ.pol d₀ hd₀ (n : ℤ)
    le_top a

/-- **For an isomorphism of polarized families over an affine base, `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` is an
isomorphism in every degree**: it is bijective on global sections. -/
theorem isIso_algebraPullbackHom_homOfIsoOver_app (φ : PolarizedIsoOver f g L M) (n : ℤ) :
    IsIso ((algebraPullbackHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀
      hd₀).app n) := by
  refine (SheafGradedAlgebraHom.forall_isIso_app_iff (algebraPullbackSheafHom
    ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀ hd₀)).2 (fun m => ?_) n
  rw [SheafGradedAlgebraHom.globalSectionsEquiv_apply_coe]
  refine (Function.Bijective.of_comp_iff _
    (bijective_pullbackSectionTop (tailAlgebra g M d₀ hd₀) (m : ℤ))).1 ?_
  have : (⇑((algebraPullbackSheafHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ)
      d₀ hd₀).globalSectionsMap m) ∘ pullbackSectionTop (tailAlgebra g M d₀ hd₀) (m : ℤ)) =
        (φ.sectionsHom d₀ hd₀).app m :=
    funext (algebraPullbackSheafHom_app_pullbackSectionTop hf hg hL d₀ hd₀ φ m)
  have hb := φ.bijective_sectionsHom_app d₀ hd₀ m
  rw [← this] at hb
  exact hb

variable (I : GradedMulDatum.Iso (tailAlgebra g M d₀ hd₀).globalDatum
    (tailAlgebra f L d₀ hd₀).globalDatum)

/-- **The homomorphism of graded algebras attached to an isomorphism of global sections data**,
precomposed with `pullbackIdHom`. -/
abbrev algebraHomOfSectionsIso :
    SheafGradedAlgebraHom ((tailAlgebra g M d₀ hd₀).pullback (𝟙 S)) (tailAlgebra f L d₀ hd₀) :=
  (SheafGradedAlgebraHom.globalDatumIsoEquiv.symm I).1.comp
    (SheafGradedAlgebraHom.pullbackIdHom _)

/-- `algebraHomOfSectionsIso` is an isomorphism in every degree. -/
instance isIso_algebraHomOfSectionsIso_app (n : ℤ) :
    IsIso ((algebraHomOfSectionsIso d₀ hd₀ I).app n) := by
  have := (SheafGradedAlgebraHom.globalDatumIsoEquiv.symm I).2 n
  change IsIso ((SheafGradedAlgebraHom.pullbackIdHom _).app n ≫
    (SheafGradedAlgebraHom.globalDatumIsoEquiv.symm I).1.app n)
  infer_instance

/-- `algebraHomOfSectionsIso` is an isomorphism in all large degrees. -/
theorem eventually_isIso_algebraHomOfSectionsIso :
    ∀ᶠ d : ℕ in Filter.atTop, IsIso ((algebraHomOfSectionsIso d₀ hd₀ I).app (d : ℤ)) :=
  Filter.Eventually.of_forall fun _ => inferInstance

/-- `algebraHomOfSectionsIso` acts on global sections by the given isomorphism of data. -/
theorem algebraHomOfSectionsIso_app_pullbackSectionTop (n : ℕ)
    (a : Γ((tailAlgebra g M d₀ hd₀).piece (n : ℤ), ⊤)) :
    ((algebraHomOfSectionsIso d₀ hd₀ I).app n).app ⊤ (pullbackSectionTop _ (n : ℤ) a) =
      I.hom.app n a :=
  (congrArg (fun z => ((SheafGradedAlgebraHom.globalDatumIsoEquiv.symm I).1.app n).app ⊤ z)
    (pullbackIdHom_app_pullbackSectionTop (tailAlgebra g M d₀ hd₀) (n : ℤ) a)).trans
    (SheafGradedAlgebraHom.ofGlobalSections_app_app_top I.hom.app I.hom.app_mul I.hom.app_one n a)

/-- **The isomorphism `Proj_S(𝒜(f)) ⟶ Proj_S(𝒜(g))` attached to an isomorphism of data**: the
morphism of [Stacks, Tag 07ZJ] followed by the base change morphism along `𝟙 S`. -/
abbrev projHomOfSectionsIso :
    (relativeProj (tailAlgebra f L d₀ hd₀)).scheme ⟶
      (relativeProj (tailAlgebra g M d₀ hd₀)).scheme :=
  projMapOfEventuallyIso (algebraHomOfSectionsIso d₀ hd₀ I)
      (eventually_isIso_algebraHomOfSectionsIso d₀ hd₀ I) ≫
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom (tailAlgebra g M d₀ hd₀)
      (𝟙 S)

/-- The square of `projHomOfSectionsIso` over `𝟙 S` is cartesian. -/
theorem isPullback_projHomOfSectionsIso :
    IsPullback (projHomOfSectionsIso d₀ hd₀ I) (relativeProj (tailAlgebra f L d₀ hd₀)).toBase
      (relativeProj (tailAlgebra g M d₀ hd₀)).toBase (𝟙 S) :=
  isPullback_projBaseChangeOfAlgebraHom (algebraHomOfSectionsIso d₀ hd₀ I)
    (eventually_isIso_algebraHomOfSectionsIso d₀ hd₀ I)

/-- `projHomOfSectionsIso` is an isomorphism. -/
instance isIso_projHomOfSectionsIso : IsIso (projHomOfSectionsIso d₀ hd₀ I) :=
  (isPullback_projHomOfSectionsIso d₀ hd₀ I).isIso_fst_of_isIso

/-- The map of Serre twists in degree one along `projHomOfSectionsIso`. -/
abbrev twistHomOfSectionsIso :
    (Scheme.Modules.pullback (projHomOfSectionsIso d₀ hd₀ I)).obj
        (relativeTwist (tailAlgebra g M d₀ hd₀) 1) ⟶ relativeTwist (tailAlgebra f L d₀ hd₀) 1 :=
  (baseChangeTwistHom (algebraHomOfSectionsIso d₀ hd₀ I)
    (eventually_isIso_algebraHomOfSectionsIso d₀ hd₀ I)).app 1

/-- `twistHomOfSectionsIso` is an isomorphism. -/
instance isIso_twistHomOfSectionsIso : IsIso (twistHomOfSectionsIso d₀ hd₀ I) :=
  isIso_baseChangeTwistHom_app _ _ 1

/-- **The isomorphism `X ≅ Y` attached to an isomorphism of data**: `r'_f ≫ M ≫ (r'_g)⁻¹`. -/
def totalIsoOfSectionsIso : X ≅ Y :=
  asIso (canonicalProjHomOfMorphism f L hf hL d₀ hd₀) ≪≫ asIso (projHomOfSectionsIso d₀ hd₀ I) ≪≫
    (asIso (canonicalProjHomOfMorphism g M hg hM d₀ hd₀)).symm

/-- `totalIsoOfSectionsIso` as a composite. -/
theorem totalIsoOfSectionsIso_hom :
    (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I).hom =
      canonicalProjHomOfMorphism f L hf hL d₀ hd₀ ≫ projHomOfSectionsIso d₀ hd₀ I ≫
        inv (canonicalProjHomOfMorphism g M hg hM d₀ hd₀) := rfl

/-- `totalIsoOfSectionsIso` is compatible with `r'`. -/
theorem totalIsoOfSectionsIso_hom_comp_canonicalProjHom :
    (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I).hom ≫ canonicalProjHomOfMorphism g M hg hM d₀ hd₀ =
      canonicalProjHomOfMorphism f L hf hL d₀ hd₀ ≫ projHomOfSectionsIso d₀ hd₀ I := by
  rw [totalIsoOfSectionsIso_hom, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- `totalIsoOfSectionsIso` lies over `S`. -/
theorem totalIsoOfSectionsIso_hom_comp :
    (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I).hom ≫ g = f := by
  have h₂' : inv (canonicalProjHomOfMorphism g M hg hM d₀ hd₀) ≫ g =
      (relativeProj (tailAlgebra g M d₀ hd₀)).toBase := by
    rw [IsIso.inv_comp_eq, canonicalProjHomOfMorphism_comp_toBase]
  rw [totalIsoOfSectionsIso_hom, Category.assoc, Category.assoc, h₂',
    (isPullback_projHomOfSectionsIso d₀ hd₀ I).w, Category.comp_id,
    canonicalProjHomOfMorphism_comp_toBase]

/-- **The comparison of polarizations attached to an isomorphism of data**, through `θ'_g⁻¹`, the
map of Serre twists along `projHomOfSectionsIso` and `θ'_f`. -/
def polarizationOfSectionsIso :
    (Scheme.Modules.pullback (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I).hom).obj M ≅ L :=
  polarizationOfFactorization (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I).hom
    (canonicalProjHomOfMorphism f L hf hL d₀ hd₀) (canonicalProjHomOfMorphism g M hg hM d₀ hd₀)
    (canonicalTwistMapOfMorphism g M hg hM d₀ hd₀) inferInstance
    (canonicalTwistMapOfMorphism f L hf hL d₀ hd₀) inferInstance
    (projHomOfSectionsIso d₀ hd₀ I) (twistHomOfSectionsIso d₀ hd₀ I) inferInstance
    (totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀ I)

/-- **The isomorphism of polarized families attached to an isomorphism of global sections
data.** -/
abbrev ofSectionsIso : PolarizedIsoOver f g L M where
  iso := totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I
  comm := totalIsoOfSectionsIso_hom_comp hf hg hL hM d₀ hd₀ I
  pol := polarizationOfSectionsIso hf hg hL hM d₀ hd₀ I

/-- The polarization of `homOfIsoOver φ` is the comparison of polarizations of `φ`. -/
theorem heq_polarization_homOfIsoOver (φ : PolarizedIsoOver f g L M) :
    HEq φ.pol ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ).polarization := HEq.rfl

/-- For the data of an isomorphism of polarized families, `algebraHomOfSectionsIso` is
`algebraPullbackSheafHom`. -/
theorem algebraHomOfSectionsIso_sectionsIso (φ : PolarizedIsoOver f g L M) :
    algebraHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀) =
      algebraPullbackSheafHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀
        hd₀ := by
  refine SheafGradedAlgebraHom.ext_of_isAffine fun n a => ?_
  obtain ⟨b, rfl⟩ := (bijective_pullbackSectionTop (tailAlgebra g M d₀ hd₀) (n : ℤ)).2 a
  exact (algebraHomOfSectionsIso_app_pullbackSectionTop d₀ hd₀ _ n b).trans
    (algebraPullbackSheafHom_app_pullbackSectionTop hf hg hL d₀ hd₀ φ n b).symm

/-- The polarization of `ofSectionsIso I` is a `polarizationOfFactorization`, written in the
spelling of the deformations `trivialDeformation` and `deformationOfIsoOver φ`. -/
private theorem heq_pol_ofSectionsIso_polarizationOfFactorization (φ : PolarizedIsoOver f g L M) :
    HEq (ofSectionsIso hf hg hL hM d₀ hd₀ I).pol
      (polarizationOfFactorization
        (X₁ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.X')
        (X₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).X')
        (P₁ := (relativeProj
          ((PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra d₀
            hd₀)).scheme)
        (P₂ := (relativeProj
          (((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
            φ).truncatedSectionAlgebra d₀ hd₀)).scheme)
        (O₂ := relativeTwist
          (((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
            φ).truncatedSectionAlgebra d₀ hd₀) 1)
        (O₁ := relativeTwist
          ((PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra
            d₀ hd₀) 1)
        (L₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).L')
        (L₁ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.L')
        (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ I).hom
        (canonicalProjHomOfMorphism f L hf hL d₀ hd₀)
        (canonicalProjHomOfMorphism g M hg hM d₀ hd₀)
        (canonicalTwistMapOfMorphism g M hg hM d₀ hd₀)
        (isIso_canonicalTwistMapOfMorphism g M hg hM d₀ hd₀)
        (canonicalTwistMapOfMorphism f L hf hL d₀ hd₀)
        (isIso_canonicalTwistMapOfMorphism f L hf hL d₀ hd₀)
        (projHomOfSectionsIso d₀ hd₀ I) (twistHomOfSectionsIso d₀ hd₀ I)
        (isIso_twistHomOfSectionsIso d₀ hd₀ I)
        (totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀ I)) :=
  (HEq.rfl : HEq _ (polarizationOfSectionsIso hf hg hL hM d₀ hd₀ I)).trans HEq.rfl

/-- **Every isomorphism of polarized families is recovered from its global sections data**, by the
functoriality of `r'` and `θ'` (`canonicalProjHom_comp_projBaseChangeHom`,
`canonicalTwistMap_comp_polarization`). -/
theorem ofSectionsIso_sectionsIso (φ : PolarizedIsoOver f g L M) :
    ofSectionsIso hf hg hL hM d₀ hd₀ (φ.sectionsIso d₀ hd₀) = φ := by
  have hiso := isIso_algebraPullbackHom_homOfIsoOver_app hf hg hL d₀ hd₀ φ
  have hψ := heq_of_eq (algebraHomOfSectionsIso_sectionsIso hf hg hL d₀ hd₀ φ)
  have hN' : projHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀) =
      projBaseChangeHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀ hd₀
        hiso :=
    eq_of_heq (projMapOfEventuallyIso_comp_baseChangeHom_of_heq
      (S₁ := S) (T₁ := S)
      (S₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).S')
      (T₂ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.S')
      (A₁ := tailAlgebra g M d₀ hd₀) (g₁ := 𝟙 S) (B₁ := tailAlgebra f L d₀ hd₀)
      (A₂ :=
        ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).truncatedSectionAlgebra
        d₀ hd₀) (g₂ := ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ).base)
      (B₂ :=
        (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra d₀ hd₀)
      (ψ₁ := algebraHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀))
      (ψ₂ := algebraPullbackSheafHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀
        hd₀) rfl rfl HEq.rfl HEq.rfl HEq.rfl hψ
        (eventually_isIso_algebraHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀))
      (eventually_isIso_algebraPullbackSheafHom _ d₀ hd₀ hiso))
  have hτ' : HEq (twistHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀))
      (projBaseChangeTwistMap ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀ hd₀
        hiso) :=
    heq_baseChangeTwistHom_app_of_heq
      (S₁ := S) (T₁ := S)
      (S₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).S')
      (T₂ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.S')
      (A₁ := tailAlgebra g M d₀ hd₀) (g₁ := 𝟙 S) (B₁ := tailAlgebra f L d₀ hd₀)
      (A₂ :=
        ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg φ).truncatedSectionAlgebra
        d₀ hd₀) (g₂ := ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ).base)
      (B₂ :=
        (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra d₀ hd₀)
      (ψ₁ := algebraHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀))
      (ψ₂ := algebraPullbackSheafHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀
        hd₀) rfl rfl HEq.rfl HEq.rfl HEq.rfl hψ
        (eventually_isIso_algebraHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀))
      (eventually_isIso_algebraPullbackSheafHom _ d₀ hd₀ hiso) 1
  have key : canonicalProjHomOfMorphism f L hf hL d₀ hd₀ ≫
      projBaseChangeHom ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀ hd₀ hiso =
      φ.iso.hom ≫ canonicalProjHomOfMorphism g M hg hM d₀ hd₀ :=
    canonicalProjHom_comp_projBaseChangeHom _ d₀ hd₀ hiso
  have ht : (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ (φ.sectionsIso d₀ hd₀)).hom = φ.iso.hom := by
    refine (cancel_mono (canonicalProjHomOfMorphism g M hg hM d₀ hd₀)).1 ?_
    exact (totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀
      (φ.sectionsIso d₀ hd₀)).trans
      ((congrArg (fun N => canonicalProjHomOfMorphism f L hf hL d₀ hd₀ ≫ N) hN').trans key)
  refine PolarizedIsoOver.ext ht ?_
  have ht' : (totalIsoOfSectionsIso hf hg hL hM d₀ hd₀ (φ.sectionsIso d₀ hd₀)).hom =
      ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ).total := ht
  have hpol := heq_polarizationOfFactorization_polarization
    ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg φ) d₀ hd₀ hiso ht'
    (rfl : canonicalProjHomOfMorphism f L hf hL d₀ hd₀ =
      (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.canonicalProjHom d₀ hd₀)
    (canonicalProjHom_deformationOfIsoOver hf hg hL hM d₀ hd₀ φ).symm
    (canonicalTwistMapOfMorphism g M hg hM d₀ hd₀)
    (isIso_canonicalTwistMapOfMorphism g M hg hM d₀ hd₀)
    (heq_canonicalTwistMap_deformationOfIsoOver hf hg hL hM d₀ hd₀ φ).symm
    (canonicalTwistMapOfMorphism f L hf hL d₀ hd₀)
    (isIso_canonicalTwistMapOfMorphism f L hf hL d₀ hd₀) HEq.rfl hN'
    (isIso_twistHomOfSectionsIso d₀ hd₀ (φ.sectionsIso d₀ hd₀)) hτ'
    (totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀ (φ.sectionsIso d₀ hd₀))
  exact (heq_pol_ofSectionsIso_polarizationOfFactorization hf hg hL hM d₀ hd₀
    (φ.sectionsIso d₀ hd₀) φ).trans (hpol.trans (heq_polarization_homOfIsoOver hf hg hL φ).symm)

/-- **In degrees `≥ d₀`, the data of `ofSectionsIso I` is `I`**, by
`algebraPullbackSheafHom_app_unitApp_eq`. -/
theorem sectionsHom_ofSectionsIso_app (n : ℕ) (hn : d₀ ≤ n)
    (a : Γ((tailAlgebra g M d₀ hd₀).piece (n : ℤ), ⊤)) :
    ((ofSectionsIso hf hg hL hM d₀ hd₀ I).sectionsHom d₀ hd₀).app n a = I.hom.app n a := by
  have hγ' := eventually_isIso_algebraHomOfSectionsIso d₀ hd₀ I
  have core := algebraPullbackSheafHom_app_unitApp_eq
    ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg (ofSectionsIso hf hg hL hM d₀ hd₀ I))
    d₀ hd₀ (algebraHomOfSectionsIso d₀ hd₀ I) hγ' ?_ ?_ ?_ ⊤ (isAffineOpen_top S) n hn a
  · have hu : pullbackSectionTop (tailAlgebra g M d₀ hd₀) (n : ℤ) a =
        unitApp ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).base
          ((((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
            (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀).piece (n : ℤ))
          ⊤ a :=
      Stacks.Conormal.pullbackSection_self _ _ ⊤ a
    refine (algebraPullbackSheafHom_app_pullbackSectionTop hf hg hL d₀ hd₀ _ n a).symm.trans ?_
    refine Eq.trans ?_ (algebraHomOfSectionsIso_app_pullbackSectionTop d₀ hd₀ I n a)
    have hu' : pullbackSectionTop (((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀) (n : ℤ) a =
        unitApp ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).base
          ((((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
            (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀).piece (n : ℤ))
          ⊤ a :=
      Stacks.Conormal.pullbackSection_self _ _ ⊤ a
    rw [hu, hu']
    exact core
  · exact totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀ I
  · exact totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀ I
  · have hN : projHomOfSectionsIso d₀ hd₀ I = projMapOfEventuallyIso
        (algebraHomOfSectionsIso d₀ hd₀ I : SheafGradedAlgebraHom
          ((((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
            (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀).pullback
            ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg
              (ofSectionsIso hf hg hL hM d₀ hd₀ I)).base)
          ((PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra
            d₀ hd₀))
          hγ' ≫ Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
            (((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
              (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀)
            ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg
              (ofSectionsIso hf hg hL hM d₀ hd₀ I)).base :=
      eq_of_heq (projMapOfEventuallyIso_comp_baseChangeHom_of_heq
        (S₁ := S) (T₁ := S)
        (S₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).S')
        (T₂ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.S')
        (A₁ := tailAlgebra g M d₀ hd₀) (g₁ := 𝟙 S) (B₁ := tailAlgebra f L d₀ hd₀)
        (A₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀)
        (g₂ := ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).base)
        (B₂ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra d₀
          hd₀)
        (ψ₁ := algebraHomOfSectionsIso d₀ hd₀ I) (ψ₂ := algebraHomOfSectionsIso d₀ hd₀ I)
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl hγ' hγ')
    have hτ := heq_baseChangeTwistHom_app_of_heq
        (S₁ := S) (T₁ := S)
        (S₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).S')
        (T₂ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.S')
        (A₁ := tailAlgebra g M d₀ hd₀) (g₁ := 𝟙 S) (B₁ := tailAlgebra f L d₀ hd₀)
        (A₂ := ((PolarizedFamily.ofMorphism f L hf hL).deformationOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).truncatedSectionAlgebra d₀ hd₀)
        (g₂ := ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg
          (ofSectionsIso hf hg hL hM d₀ hd₀ I)).base)
        (B₂ := (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.truncatedSectionAlgebra d₀
          hd₀)
        (ψ₁ := algebraHomOfSectionsIso d₀ hd₀ I) (ψ₂ := algebraHomOfSectionsIso d₀ hd₀ I)
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl hγ' hγ' 1
    exact pullback_map_comp_polarization_of_heq_polarizationOfFactorization
      ((PolarizedFamily.ofMorphism f L hf hL).homOfIsoOver hg (ofSectionsIso hf hg hL hM d₀ hd₀ I))
      d₀ hd₀ (algebraHomOfSectionsIso d₀ hd₀ I) hγ' rfl
      (rfl : canonicalProjHomOfMorphism f L hf hL d₀ hd₀ =
        (PolarizedFamily.ofMorphism f L hf hL).trivialDeformation.canonicalProjHom d₀ hd₀)
      (canonicalProjHom_deformationOfIsoOver hf hg hL hM d₀ hd₀
        (ofSectionsIso hf hg hL hM d₀ hd₀ I)).symm
      (canonicalTwistMapOfMorphism g M hg hM d₀ hd₀)
      (isIso_canonicalTwistMapOfMorphism g M hg hM d₀ hd₀)
      (heq_canonicalTwistMap_deformationOfIsoOver hf hg hL hM d₀ hd₀
        (ofSectionsIso hf hg hL hM d₀ hd₀ I)).symm
      (canonicalTwistMapOfMorphism f L hf hL d₀ hd₀)
      (isIso_canonicalTwistMapOfMorphism f L hf hL d₀ hd₀) HEq.rfl hN
      (isIso_twistHomOfSectionsIso d₀ hd₀ I) hτ
      (totalIsoOfSectionsIso_hom_comp_canonicalProjHom hf hg hL hM d₀ hd₀ I) _
      ((heq_pol_ofSectionsIso_polarizationOfFactorization hf hg hL hM d₀ hd₀ I
        (ofSectionsIso hf hg hL hM d₀ hd₀ I)).symm.trans
        (heq_polarization_homOfIsoOver hf hg hL _))

/-- **Every isomorphism of global sections data comes from an isomorphism of polarized
families.** -/
theorem sectionsIso_ofSectionsIso :
    (ofSectionsIso hf hg hL hM d₀ hd₀ I).sectionsIso d₀ hd₀ = I := by
  refine GradedMulDatum.Iso.ext (GradedMulDatum.Hom.ext (funext fun n => ?_))
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact app_zero_eq_of_tailAlgebra d₀ hd₀ _ _
  by_cases hn : d₀ ≤ n
  · exact LinearMap.ext fun a => sectionsHom_ofSectionsIso_app hf hg hL hM d₀ hd₀ I n hn a
  · exact app_eq_of_tailAlgebra_of_lt d₀ hd₀ _ _ n hn0 (by omega)

end Standing

/-- **The section-algebra bijection.** -/
def sectionsEquiv {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {L : X.Modules} {M : Y.Modules}
    [IsProper f] [Flat f] [QuasiCompact f] [QuasiSeparated f]
    [IsProper g] [Flat g] [QuasiCompact g] [QuasiSeparated g]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M] [IsAffine S]
    (hf : _root_.AlgebraicGeometry.FinitePresentation f)
    (hg : _root_.AlgebraicGeometry.FinitePresentation g)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) (d₀ : ℕ) (hd₀ : 0 < d₀) :
    PolarizedIsoOver f g L M ≃ GradedMulDatum.Iso (tailAlgebra g M d₀ hd₀).globalDatum
      (tailAlgebra f L d₀ hd₀).globalDatum where
  toFun φ := φ.sectionsIso d₀ hd₀
  invFun := ofSectionsIso hf hg hL hM d₀ hd₀
  left_inv := ofSectionsIso_sectionsIso hf hg hL hM d₀ hd₀
  right_inv := sectionsIso_ofSectionsIso hf hg hL hM d₀ hd₀

end PolarizedIsoOver

/-- **Polarized isomorphisms over an affine base are isomorphisms of section algebras**:
`Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedIsoSectionBijection`. -/
theorem polarizedIsoSectionBijection : PolarizedIsoSectionBijection.{u} := by
  intro S X Y f g L M _ _ _ _ _ _ _ _ _ _ _ hf hg hL hM d₀ hd₀
  exact ⟨PolarizedIsoOver.sectionsEquiv hf hg hL hM d₀ hd₀, fun φ n s => rfl⟩

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
