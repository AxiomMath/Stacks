module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientInverseImage

/-!
# Realizations of square-zero extensions

A realization of a square-zero extension of the structure sheaf of an algebraic space `X` over
`f : X ⟶ Y` is a first-order thickening `X ⊂ X'` over `Y` whose structure sheaf is the given
extension. Given a charted presentation of `f`, the ambient space `X'` comes with an immersion
`X ⟶ X'` and a structure morphism `X' ⟶ Y` whose composite is `f`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.Realization`: A realization of a square-zero
  extension.
* `AlgebraicGeometry.Space.SquareZeroExtension.ambientImmersion`: The immersion `X ⟶ X'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.ambientToBase`: The structure morphism `X' ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.ambientImmersion_comp_toBase`: The composite
  `X ⟶ X' ⟶ Y` is `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v' u' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical comparison `f⁻¹𝒪_Y ≅ i⁻¹g⁻¹𝒪_Y` of inverse images for `i ≫ g = f`: the
composition law of [Stacks Project, Tag 03G8] in inverse-image form, the mate of the cartesian
composition comparison of direct images. -/
def canonicalBaseComparison {X Y Z : AlgebraicSpaces B S hS}
    (i : X ⟶ Z) (g : Z ⟶ Y) (f : X ⟶ Y) (h : i ≫ g = f) :
    (smallEtaleInverseImageRing B S hS f).obj
        (smallEtaleRingedTopos B S hS Y).O ≅
      (smallEtaleInverseImageRing B S hS i).obj
        ((smallEtaleInverseImageRing B S hS g).obj
          (smallEtaleRingedTopos B S hS Y).O) := by
  subst h
  exact ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i g).app
    (smallEtaleRingedTopos B S hS Y).O).symm

/-- **A realization of a square-zero extension** ([Stacks Project, Tag 05ZT]): a first-order
thickening `X ⊂ X'` over the base whose structure sheaf, read on the small étale site of `X`,
is the extension, compatibly with the surjections to `𝒪_X` and with the algebra structures over
the base. -/
structure SquareZeroExtension.Realization {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) where
  /-- The ambient space `X'`. -/
  ambient : AlgebraicSpaces B S hS
  /-- The closed subspace of `X'` identified with `X`. -/
  closed : Subfunctor ambient.1
  /-- It is a first-order thickening. -/
  firstOrder : IsFirstOrderThickening B S hS ambient closed
  /-- The identification of `X` with the closed subspace. -/
  closedIso : X.1 ≅ closed.toFunctor
  /-- The immersion `X ⟶ X'`. -/
  immersion : X ⟶ ambient
  /-- It is the inclusion of the closed subspace. -/
  immersion_eq : immersion.hom = closedIso.hom ≫ closed.ι
  /-- The structure morphism `X' ⟶ Y`. -/
  toBase : ambient ⟶ Y
  /-- It extends `f`. -/
  over_base : immersion ≫ toBase = f
  /-- The identification `i⁻¹𝒪_{X'} ≅ 𝒜`. -/
  sheafIso :
    (smallEtaleInverseImageRing B S hS immersion).obj
      (smallEtaleRingedTopos B S hS ambient).O ≅ E.A
  /-- It is compatible with the surjections to `𝒪_X`. -/
  quotient_compatibility :
    sheafIso.hom ≫ E.π = (smallEtaleRingedToposHom B S hS immersion).fSharpInverseImage
  /-- The comparison of inverse images of the structure sheaf of the base. -/
  baseComparison :
    (smallEtaleInverseImageRing B S hS f).obj
        (smallEtaleRingedTopos B S hS Y).O ≅
      (smallEtaleInverseImageRing B S hS immersion).obj
        ((smallEtaleInverseImageRing B S hS toBase).obj
          (smallEtaleRingedTopos B S hS Y).O)
  /-- It is the canonical one. -/
  baseComparison_canonical :
    baseComparison = canonicalBaseComparison B S hS immersion toBase f over_base
  /-- The identification is one of algebras over the base. -/
  algebra_compatibility :
    E.toBase = baseComparison.hom ≫
      (smallEtaleInverseImageRing B S hS immersion).map
        (smallEtaleRingedToposHom B S hS toBase).fSharpInverseImage ≫
      sheafIso.hom


/-- The comparison of left adjoints attached to an isomorphism of a composite right adjoint with
a third one, applied to an adjunct of a composite: pure adjunction calculus. -/
theorem leftAdjointUniq_comp_homEquiv_symm {Cy Cx' Cx : Type*} [Category Cy] [Category Cx']
    [Category Cx] {LP : Cy ⥤ Cx'} {RP : Cx' ⥤ Cy} {LI : Cx' ⥤ Cx} {RI : Cx ⥤ Cx'}
    {LF : Cy ⥤ Cx} {RF : Cx ⥤ Cy} (adjP : LP ⊣ RP) (adjI : LI ⊣ RI) (adjF : LF ⊣ RF)
    (ν : RI ⋙ RP ≅ RF) {O : Cy} {O' : Cx'} {A : Cx} (p' : O ⟶ RP.obj O') (ψ : O' ⟶ RI.obj A) :
    (((adjP.comp adjI).ofNatIsoRight ν).leftAdjointUniq adjF).hom.app O ≫
        (adjF.homEquiv O A).symm (p' ≫ RP.map ψ ≫ ν.hom.app A) =
      LI.map ((adjP.homEquiv O O').symm p') ≫ (adjI.homEquiv O' A).symm ψ := by
  rw [Adjunction.leftAdjointUniq_ofNatIsoRight_hom_app_comp_homEquiv_symm, Category.assoc,
    Category.assoc, Iso.hom_inv_id_app]
  rw [show RP.map ψ ≫ 𝟙 ((RI ⋙ RP).obj A) = RP.map ψ from Category.comp_id _]
  rw [Adjunction.comp_homEquiv,
    Equiv.symm_trans_apply, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]

/-- **The algebra compatibility, abstractly.** For morphisms of topoi `Ti`, `Tp`, `Tf` with an
isomorphism `ν` of `Tf_*` with the composite direct image and a comparison `κ` of inverse images
of sheaves of rings lying over the induced comparison of left adjoints, a map
`τ : Tf⁻¹𝒪 ⟶ 𝒜` whose adjunct is, on underlying sheaves of sets, `p'` followed by `Tp_*ψ'` and
`ν`, factors through `κ` as the inverse image of the adjunct of `p'` followed by that of `ψ'`.
Stated for abstract morphisms of topoi, where the terms are small. -/
theorem MorphismOfTopoi.comp_eq_of_forget {C : Type u'} [Category.{v'} C] {D : Type u'}
    [Category.{v'} D] {E : Type u'} [Category.{v'} E] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    (Ti : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
    (Tp : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf L (Type w)))
    (Tf : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf L (Type w)))
    (ν : (Tp.comp Ti).pushforward ≅ Tf.pushforward)
    (κ : Tp.inverseImageRing ⋙ Ti.inverseImageRing ≅ Tf.inverseImageRing)
    (hκ : ∀ O, (sheafCompose J (forget CommRingCat.{w})).map (κ.hom.app O) =
      (((Tp.comp Ti).adj.ofNatIsoRight ν).leftAdjointUniq Tf.adj).hom.app
        ((sheafCompose L (forget CommRingCat.{w})).obj O))
    (OY : Sheaf L CommRingCat.{w}) (OX' : Sheaf K CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (p' : OY ⟶ Tp.pushforwardRing.obj OX') (ψ' : OX' ⟶ Ti.pushforwardRing.obj A)
    (τ : Tf.inverseImageRing.obj OY ⟶ A)
    (hτ : (sheafCompose J (forget CommRingCat.{w})).map τ =
      (Tf.adj.homEquiv _ _).symm ((sheafCompose L (forget CommRingCat.{w})).map p' ≫
        Tp.pushforward.map ((sheafCompose K (forget CommRingCat.{w})).map ψ') ≫
        ν.hom.app ((sheafCompose J (forget CommRingCat.{w})).obj A))) :
    κ.hom.app OY ≫ τ = Ti.inverseImageRing.map ((Tp.ringAdjunction.homEquiv _ _).symm p') ≫
      (Ti.ringAdjunction.homEquiv _ _).symm ψ' := by
  refine (sheafCompose J (forget CommRingCat.{w})).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, hκ, hτ, MorphismOfTopoi.inverseImageRing_map_forget,
    MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget,
    MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget]
  exact leftAdjointUniq_comp_homEquiv_symm Tp.adj Ti.adj Tf.adj ν _ _



/-- `AlgebraicGeometry.Space.MorphismOfTopoi.comp_eq_of_forget`, spelled with the image functors of
sheaves of commutative rings. -/
theorem MorphismOfTopoi.comp_eq_of_forget' {C : Type u'} [Category.{v'} C] {D : Type u'}
    [Category.{v'} D] {E : Type u'} [Category.{v'} E] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    (Ti : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
    (Tp : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf L (Type w)))
    (Tf : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf L (Type w)))
    (ν : (Tp.comp Ti).pushforward ≅ Tf.pushforward)
    (κ : inverseImageCommRingFunctor.{w, w, v', u', v', u'} Tp ⋙
        inverseImageCommRingFunctor.{w, w, v', u', v', u'} Ti ≅
      inverseImageCommRingFunctor.{w, w, v', u', v', u'} Tf)
    (hκ : ∀ O, (sheafCompose J (forget CommRingCat.{w})).map (κ.hom.app O) =
      (((Tp.comp Ti).adj.ofNatIsoRight ν).leftAdjointUniq Tf.adj).hom.app
        ((sheafCompose L (forget CommRingCat.{w})).obj O))
    (OY : Sheaf L CommRingCat.{w}) (OX' : Sheaf K CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (p' : OY ⟶ (pushforwardCommRingFunctor.{w, w, v', u', v', u'} Tp).obj OX')
    (ψ' : OX' ⟶ (pushforwardCommRingFunctor.{w, w, v', u', v', u'} Ti).obj A)
    (τ : (inverseImageCommRingFunctor.{w, w, v', u', v', u'} Tf).obj OY ⟶ A)
    (hτ : (sheafCompose J (forget CommRingCat.{w})).map τ =
      (Tf.adj.homEquiv _ _).symm ((sheafCompose L (forget CommRingCat.{w})).map p' ≫
        Tp.pushforward.map ((sheafCompose K (forget CommRingCat.{w})).map ψ') ≫
        ν.hom.app ((sheafCompose J (forget CommRingCat.{w})).obj A))) :
    κ.hom.app OY ≫ τ = (inverseImageCommRingFunctor.{w, w, v', u', v', u'} Ti).map
        (((commRingImageAdjunction.{w, w, v', u', v', u'} Tp).homEquiv _ _).symm p') ≫
      ((commRingImageAdjunction.{w, w, v', u', v', u'} Ti).homEquiv _ _).symm ψ' :=
  MorphismOfTopoi.comp_eq_of_forget Ti Tp Tf ν κ hκ OY OX' A p' ψ' τ hτ

namespace SquareZeroExtension

attribute [local instance] hasSheafify_bigFppfOver

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)
  (hcU : B.Contains (chartThickening B S hS E (presentationChart C.P)))
  (hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P)))

/-- The immersion `X ⟶ X'` into the ambient space. -/
def ambientImmersion : X ⟶ ambient E C hcU hcR :=
  ObjectProperty.homMk (exists_ambientMap E C hcU hcR).choose

/-- On the presenting chart `U` of `X`, the immersion `X ⟶ X'` is the inclusion of `U` into its
thickening followed by the quotient map onto `X'`. -/
theorem ambientImmersion_fac :
    C.P.toSpace ≫ (ambientImmersion E C hcU hcR).hom =
      yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR :=
  (exists_ambientMap E C hcU hcR).choose_spec

/-- The structure morphism `X' ⟶ Y` of the ambient space. -/
def ambientToBase : ambient E C hcU hcR ⟶ Y :=
  ObjectProperty.homMk (exists_ambientToBase E C hcU hcR).choose

/-- On the thickened presenting chart, the structure morphism `X' ⟶ Y` is the map to the
presenting scheme of `Y` followed by its quotient map onto `Y`. -/
theorem ambientToBase_fac :
    ambQuot E C hcU hcR ≫ (ambientToBase E C hcU hcR).hom =
      yoneda.map (ambUToBase E C hcU) ≫ C.Q.toSpace :=
  (exists_ambientToBase E C hcU hcR).choose_spec

/-- The composite of the immersion `X ⟶ X'` and the structure morphism `X' ⟶ Y` is `f`. -/
theorem ambientImmersion_comp_toBase :
    ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR = f :=
  ambientMap_comp_toBase _ (ambientImmersion_fac E C hcU hcR) _ (ambientToBase_fac E C hcU hcR)

end SquareZeroExtension

end AlgebraicGeometry.Space

end

