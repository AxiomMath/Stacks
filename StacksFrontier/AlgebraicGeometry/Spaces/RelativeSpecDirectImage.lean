module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The canonical factorization through the relative spectrum of the direct image

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces. This file
constructs the canonical factorization

`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`.

The construction takes as hypotheses an anti-equivalence `E` between algebraic spaces affine over
a base and quasi-coherent algebras on it, its base-change compatibility `C`, the quasi-coherence
`hqc` of `f_* 𝒪_Y`, and an identification `hid` of the direct image of `𝒪_Y` along the identity
of `Y` with `𝒪_Y`. The canonical `𝒪_Y`-algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` corresponds under `E`
and `C` to a section `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` over `Y`, and composing that
section with the projection gives the factorization.

## Main definitions

* `AlgebraicGeometry.Space.idAffineOver` is `Y` itself, as an algebraic space affine over `Y`,
  and `AlgebraicGeometry.Space.unitAlgebra` is `𝒪_Y` as an `𝒪_Y`-algebra.
* `AlgebraicGeometry.Space.relativeSpec` is the relative spectrum `\underline{Spec}_X(A)` of a
  quasi-coherent `𝒪_X`-algebra `A` on an algebraic space `X`, together with its structure
  morphism, as an algebraic space affine over `X`: the algebraic space affine over `X`
  corresponding to `A` under the anti-equivalence `E`.
* `AlgebraicGeometry.Space.directImageAlgebra` is `f_* 𝒪_Y` as a quasi-coherent algebra and
  `AlgebraicGeometry.Space.relativeSpecDirectImage` is its relative spectrum.
* `AlgebraicGeometry.Space.qcAlgebraPullback` is base change of quasi-coherent algebras.
* `AlgebraicGeometry.Space.pullbackPushforwardCounit` is the canonical `𝒪_Y`-algebra map
  `f^* f_* 𝒪_Y ⟶ 𝒪_Y`, and `AlgebraicGeometry.Space.pullbackPushforwardCounitAlgebraHom` is
  that map read as a morphism of algebra sheaves into `𝒪_Y`.
* `AlgebraicGeometry.Space.relativeSpecDirectImageSection` is the resulting section
  `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` over `Y`, and
  `AlgebraicGeometry.Space.relativeSpecDirectImageMap` is the canonical morphism
  `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`.

## Main results

* `AlgebraicGeometry.Space.relativeSpecPushforwardIso`: the direct image of the structure sheaf
  of `\underline{Spec}_X(A)` is `A`, and `AlgebraicGeometry.Space.relativeSpecBaseChangeIso`:
  `Y ×_X \underline{Spec}_X(A) = \underline{Spec}_Y(g^* A)`, both read off the anti-equivalence.
* `AlgebraicGeometry.Space.pullbackPushforwardCounit_structure`: the canonical map
  `f^* f_* 𝒪_Y ⟶ 𝒪_Y` is a map of `𝒪_Y`-algebras.
* `AlgebraicGeometry.Space.relativeSpecDirectImageMap_factorization`: the canonical morphism
  composed with the structure morphism of the relative spectrum is `f`.
* `AlgebraicGeometry.Space.functor_map_relativeSpecDirectImageSection` and
  `AlgebraicGeometry.Space.relativeSpecDirectImageSection_unique`: the section is the unique
  morphism over `Y` whose image under the anti-equivalence is the canonical algebra map.

## References

* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `Y` over itself, and `𝒪_Y` as an `𝒪_Y`-algebra -/

/-- An algebraic space is affine over itself, through its identity morphism. -/
def idAffineOver (Y : AlgebraicSpaces B S hS) : AffineOver B S hS Y :=
  ⟨Over.mk (𝟙 Y), isAffineHom_id Y.1⟩

/-- The structure sheaf of an algebraic space, read as an algebra over itself through the
identity morphism of sheaves of rings. -/
def unitAlgebra (Y : AlgebraicSpaces B S hS) : AlgebraSheaf.{u, u} B S hS Y.1 Y.2 :=
  AlgebraSheaf.ofHom (𝟙 (structureSheaf B S hS Y.1 Y.2))

/-- `𝒪_Y` is quasi-coherent as an `𝒪_Y`-algebra. -/
theorem isQuasicoherent_unitAlgebra (Y : AlgebraicSpaces B S hS) :
    (unitAlgebra B S hS Y).IsQuasicoherent :=
  SheafOfModules.isQuasicoherentOnSite_unit _

/-- `𝒪_Y` as an object of the category of quasi-coherent `𝒪_Y`-algebras. -/
def unitQuasicoherentAlgebra (Y : AlgebraicSpaces B S hS) : QuasicoherentAlgebra B S hS Y :=
  ⟨unitAlgebra B S hS Y, isQuasicoherent_unitAlgebra B S hS Y⟩

/-! ### The relative spectrum over an algebraic space -/

variable (E : AffineAlgebraAntiEquivalence B S hS)

/-- The relative spectrum `\underline{Spec}_X(A)` of a quasi-coherent `𝒪_X`-algebra on an
algebraic space `X`, as an algebraic space affine over `X`: the value on `A` of the inverse of
the anti-equivalence `E`. -/
@[stacks 081W "the relative spectrum, for a given anti-equivalence of Stacks 081V"]
def relativeSpec {X : AlgebraicSpaces B S hS} (A : QuasicoherentAlgebra B S hS X) :
    AffineOver B S hS X :=
  ((E.equivalence X).inverse.obj A).unop

/-- The direct image of the structure sheaf of `\underline{Spec}_X(A)` is `A`: the counit of the
anti-equivalence, read through its identification with direct image. -/
def relativeSpecPushforwardIso {X : AlgebraicSpaces B S hS}
    (A : QuasicoherentAlgebra B S hS X) :
    pushforwardAlgebra B S hS (relativeSpec B S hS E A).obj ≅ A.obj :=
  (E.pushforward_obj X (relativeSpec B S hS E A)).symm ≪≫
    (quasicoherentAlgebraInclusion B S hS X).mapIso
      (((E.pushforwardIso X).app (op (relativeSpec B S hS E A))).symm ≪≫
        (E.equivalence X).counitIso.app A)

/-! ### The direct-image algebra and its relative spectrum -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The quasi-coherent algebra `f_* 𝒪_Y` of a morphism `f : Y ⟶ X`, given the quasi-coherence
`hqc` of `AlgebraicGeometry.Space.pushforwardAlgebra`. -/
def directImageAlgebra (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    QuasicoherentAlgebra B S hS X :=
  ⟨pushforwardAlgebra B S hS (Over.mk f), hqc⟩

/-- The relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)`, as an algebraic space affine
over `X`. -/
def relativeSpecDirectImage (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) : AffineOver B S hS X :=
  relativeSpec B S hS E (directImageAlgebra B S hS f hqc)

/-- The direct image of the structure sheaf of `\underline{Spec}_X(f_* 𝒪_Y)` is `f_* 𝒪_Y`. -/
def relativeSpecDirectImagePushforwardIso (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    pushforwardAlgebra B S hS (relativeSpecDirectImage B S hS E f hqc).obj ≅
      pushforwardAlgebra B S hS (Over.mk f) :=
  relativeSpecPushforwardIso B S hS E (directImageAlgebra B S hS f hqc)

/-! ### Base change -/

variable (C : BaseChangeCompatibility B S hS E)

/-- Base change of quasi-coherent algebras along a morphism of algebraic spaces: the algebra
pullback of `C`, restricted to the quasi-coherent algebras. -/
def qcAlgebraPullback (g : Y ⟶ X) :
    QuasicoherentAlgebra B S hS X ⥤ QuasicoherentAlgebra B S hS Y :=
  ObjectProperty.lift _ (quasicoherentAlgebraInclusion B S hS X ⋙ C.algebraPullback g)
    (C.algebraPullback_isQuasicoherent g)

/-- `Y ×_X \underline{Spec}_X(A) = \underline{Spec}_Y(g^* A)`: the base-change compatibility
`C` at the relative spectrum of `A`. -/
def relativeSpecBaseChangeIso (g : Y ⟶ X) (A : QuasicoherentAlgebra B S hS X) :
    (qcAlgebraPullback B S hS E C g).obj A ≅
      (E.equivalence Y).functor.obj
        (op ((C.affineBaseChange g).obj (relativeSpec B S hS E A))) :=
  ((qcAlgebraPullback B S hS E C g).mapIso ((E.equivalence X).counitIso.app A)).symm ≪≫
    (C.baseChangeIso g).app (op (relativeSpec B S hS E A))

/-! ### The canonical algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` -/

/-- The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` of sheaves of commutative rings, induced on the
pushout `f^* f_* 𝒪_Y` of `𝒪_Y` and `f⁻¹ f_* 𝒪_Y` over `f⁻¹ 𝒪_X` by the counit
`f⁻¹ f_* 𝒪_Y ⟶ 𝒪_Y` of the inverse-image/direct-image adjunction and the identity of `𝒪_Y`. -/
def pullbackPushforwardCounit (f : Y ⟶ X) :
    ((C.algebraPullback f).obj (pushforwardAlgebra B S hS (Over.mk f))).right ⟶
      (smallEtaleRingedTopos B S hS Y).O :=
  (C.algebraPullback_isPushout f (pushforwardAlgebra B S hS (Over.mk f))).desc
    ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
      (smallEtaleRingedTopos B S hS Y).O)
    (𝟙 (smallEtaleRingedTopos B S hS Y).O)
    ((Adjunction.homEquiv_counit
        (commRingImageAdjunction (smallEtaleRingedToposHom B S hS f).toToposHom)
        (smallEtaleRingedTopos B S hS X).O (smallEtaleRingedTopos B S hS Y).O
        (smallEtaleRingedToposHom B S hS f).fSharp).symm.trans
      (Category.comp_id _).symm)

/-- The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` is a map of `𝒪_Y`-algebras: precomposing it with the
algebra structure map of `f^* f_* 𝒪_Y` gives the identity of `𝒪_Y`. -/
theorem pullbackPushforwardCounit_structure (f : Y ⟶ X) :
    ((C.algebraPullback f).obj (pushforwardAlgebra B S hS (Over.mk f))).hom ≫
        pullbackPushforwardCounit B S hS E C f =
      𝟙 (structureSheaf B S hS Y.1 Y.2) :=
  IsPushout.inr_desc _ _ _ _

/-- The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` as a morphism of algebra sheaves into
`AlgebraicGeometry.Space.unitAlgebra`. -/
def pullbackPushforwardCounitAlgebraHom (f : Y ⟶ X) :
    (C.algebraPullback f).obj (pushforwardAlgebra B S hS (Over.mk f)) ⟶
      unitAlgebra B S hS Y where
  right := pullbackPushforwardCounit B S hS E C f
  comm U r := by
    have h : ((((C.algebraPullback f).obj (pushforwardAlgebra B S hS (Over.mk f))).hom ≫
        pullbackPushforwardCounit B S hS E C f).hom.app U).hom r = r := by
      rw [pullbackPushforwardCounit_structure]; rfl
    rw [ObjectProperty.FullSubcategory.comp_hom] at h
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h

/-- The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` as a morphism of quasi-coherent `𝒪_Y`-algebras. -/
def directImageCounitHom (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    (qcAlgebraPullback B S hS E C f).obj (directImageAlgebra B S hS f hqc) ⟶
      unitQuasicoherentAlgebra B S hS Y :=
  ObjectProperty.homMk (pullbackPushforwardCounitAlgebraHom B S hS E C f)

/-! ### The canonical factorization -/

/-- The image of `AlgebraicGeometry.Space.idAffineOver` under the anti-equivalence is `𝒪_Y`,
given the identification `hid` of the direct image of `𝒪_Y` along the identity with `𝒪_Y`. -/
def unitQuasicoherentAlgebraIdIso
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    unitQuasicoherentAlgebra B S hS Y ≅
      (E.equivalence Y).functor.obj (op (idAffineOver B S hS Y)) :=
  ObjectProperty.isoMk
      (P := (AlgebraSheaf.IsQuasicoherent :
        ObjectProperty (AlgebraSheaf.{u, u} B S hS Y.1 Y.2)))
      (hid.symm ≪≫ (E.pushforward_obj Y (idAffineOver B S hS Y)).symm) ≪≫
    ((E.pushforwardIso Y).app (op (idAffineOver B S hS Y))).symm

/-- The canonical section `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` over `Y`: the morphism which
the anti-equivalence over `Y` matches with the canonical algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y`, read
through the base-change identification
`Y ×_X \underline{Spec}_X(f_* 𝒪_Y) = \underline{Spec}_Y(f^* f_* 𝒪_Y)`. -/
def relativeSpecDirectImageSection (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    idAffineOver B S hS Y ⟶
      (C.affineBaseChange f).obj (relativeSpecDirectImage B S hS E f hqc) :=
  ((E.equivalence Y).functor.preimage
    ((relativeSpecBaseChangeIso B S hS E C f (directImageAlgebra B S hS f hqc)).inv ≫
      directImageCounitHom B S hS E C f hqc ≫
      (unitQuasicoherentAlgebraIdIso B S hS E hid).hom)).unop

/-- The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`: the canonical section
over `Y`, composed with the projection of the base change. -/
def relativeSpecDirectImageMap (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    Over.mk f ⟶ (relativeSpecDirectImage B S hS E f hqc).obj :=
  Over.homMk
    ((relativeSpecDirectImageSection B S hS E C f hqc hid).hom.left ≫
      C.affineBaseChange_projection f (relativeSpecDirectImage B S hS E f hqc))
    (((Category.assoc _ _ _).trans
        (congrArg
          (fun k ↦ (relativeSpecDirectImageSection B S hS E C f hqc hid).hom.left ≫ k)
          (C.affineBaseChange_isPullback f
            (relativeSpecDirectImage B S hS E f hqc)).w)).trans
      (((Category.assoc _ _ _).symm.trans
          (congrArg (fun k ↦ k ≫ f)
            (Over.w (relativeSpecDirectImageSection B S hS E C f hqc hid).hom))).trans
        (Category.id_comp f)))

/-- The canonical morphism `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` is a section of the
projection to `Y`. -/
theorem relativeSpecDirectImageSection_section (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    (relativeSpecDirectImageSection B S hS E C f hqc hid).hom.left ≫
        ((C.affineBaseChange f).obj (relativeSpecDirectImage B S hS E f hqc)).obj.hom =
      𝟙 Y :=
  Over.w _

/-- The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)`, composed with the structure
morphism of the relative spectrum, is `f`. -/
theorem relativeSpecDirectImageMap_factorization (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    (relativeSpecDirectImageMap B S hS E C f hqc hid).left ≫
        (relativeSpecDirectImage B S hS E f hqc).obj.hom = f :=
  Over.w _

/-- The canonical section corresponds, under the anti-equivalence over `Y`, to the canonical
algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y`. -/
theorem functor_map_relativeSpecDirectImageSection (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y) :
    (E.equivalence Y).functor.map
        (op (relativeSpecDirectImageSection B S hS E C f hqc hid)) =
      (relativeSpecBaseChangeIso B S hS E C f (directImageAlgebra B S hS f hqc)).inv ≫
        directImageCounitHom B S hS E C f hqc ≫
        (unitQuasicoherentAlgebraIdIso B S hS E hid).hom :=
  (E.equivalence Y).functor.map_preimage _

/-- The canonical section is the *only* morphism `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` over
`Y` which the anti-equivalence matches with the canonical algebra map. -/
theorem relativeSpecDirectImageSection_unique (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y)
    (s : idAffineOver B S hS Y ⟶
      (C.affineBaseChange f).obj (relativeSpecDirectImage B S hS E f hqc))
    (hs : (E.equivalence Y).functor.map (op s) =
      (relativeSpecBaseChangeIso B S hS E C f (directImageAlgebra B S hS f hqc)).inv ≫
        directImageCounitHom B S hS E C f hqc ≫
        (unitQuasicoherentAlgebraIdIso B S hS E hid).hom) :
    s = relativeSpecDirectImageSection B S hS E C f hqc hid :=
  Quiver.Hom.op_inj
    ((E.equivalence Y).functor.map_injective
      (hs.trans
        (functor_map_relativeSpecDirectImageSection B S hS E C f hqc hid).symm))

end AlgebraicGeometry.Space

end
