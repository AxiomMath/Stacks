module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.DirectImageAlongAnIsomorphism
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Nested restriction of modules on a ringed space

Restricting a ringed space to an open `U` and then restricting the result to an open `V` of
`X.restrict U` gives a space isomorphic to the restriction of `X` to the image of `V` in `X`,
and the two resulting restriction functors on modules agree under that isomorphism.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.siteRestrictAdjunction`: restriction to an open
  subspace is left adjoint to the
  direct image along the inclusion.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso`: the isomorphism of ringed spaces
  between the twice-restricted
  space and the restriction to the image.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionModulesIso` and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionComplexIso`: the
  comparison of the two restriction functors, on modules and on complexes.

## Implementation notes

The space, ring and module universes all coincide, as they already must for the results of Tag
08C6 onwards that this file serves.

The comparison is obtained from uniqueness of left adjoints. On the right-adjoint side
everything is a direct image along a morphism of ringed spaces, so the three of them compose to
the direct image of a composite, and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso_hom_fac` identifies that
composite with the inclusion of the image of `V`; since
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.directImage` is a plain
function of the morphism, that identification transports by `congrArg`.

`AlgebraicGeometry.RingedSpace.PseudoCoherence.leftAdjointIsoOfRightIso` is stated over abstract
  categories on purpose: the same
term elaborated against the ringed-space vocabulary exhausts many times the default heartbeat
budget, because the unifier unfolds the restricted spaces.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

/-- **Restriction to an open subspace is left adjoint to the direct image.** -/
def siteRestrictAdjunction (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    restrictModules.{u} X U ⊣ directImage (X.ofRestrict U.isOpenEmbedding) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  let G := Opens.map j.hom.base
  let adj : F ⊣ G := h.isOpenMap.adjunction
  have : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := h.functor_isContinuous
  have : G.IsContinuous
      (Opens.grothendieckTopology (X : TopCat))
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat)) := inferInstance
  let R := structureSheafOfRings X
  let S := structureSheafOfRings (X.restrict U.isOpenEmbedding)
  let φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} _ _).obj R := 𝟙 _
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} _ _).obj S := directImageRingHom j
  have h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext V x
    rfl
  have h2 : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change (R.obj.map (adj.counit.app (F.obj V.unop)).op ≫
      R.obj.map (F.map (adj.unit.app V.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components V.unop]
    exact Functor.map_id_apply R.obj (Opposite.op (F.obj V.unop)) x
  change SheafOfModules.pushforward φ ⊣ SheafOfModules.pushforward ψ
  exact SheafOfModules.pushforwardPushforwardAdj adj φ ψ h1 h2

/-- The image of `V` under the two successive inclusions is the image of `V` in `X`. -/
theorem range_ofRestrict_comp_ofRestrict (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    Set.range (ConcreteCategory.hom
        ((X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
          X.ofRestrict U.isOpenEmbedding).hom.base) =
      Set.range (ConcreteCategory.hom
        (X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).hom.base) := by
  refine Eq.trans ?_ (Opens.set_range_inclusion' _).symm
  ext y
  simp only [Set.mem_range, SetLike.mem_coe]
  refine ⟨?_, fun hy => ⟨⟨⟨y, mem_of_mem_image ⟨y, hy⟩⟩, mem_of_mem_image' ⟨y, hy⟩⟩, rfl⟩⟩
  rintro ⟨p, rfl⟩
  exact dblIncl_mem p

/-- **An open of an open restriction is an open of the space.** Restricting `X` to `U` and then
to `V` gives a ringed space isomorphic to the restriction of `X` to the image of `V`. -/
def nestedOpenIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding ≅
      X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding :=
  SheafedSpace.isoMk (PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    ((X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
      X.ofRestrict U.isOpenEmbedding).hom
    (X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).hom
    (range_ofRestrict_comp_ofRestrict X U V))

/-- The comparison isomorphism of `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso` is
  compatible with the two
inclusions into `X`. -/
theorem nestedOpenIso_hom_fac (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (nestedOpenIso X U V).hom ≫
        X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding =
      (X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
        X.ofRestrict U.isOpenEmbedding := by
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := (X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding
  let f := jV ≫ jU
  let W : Opens X.carrier := U.isOpenEmbedding.functor.obj V
  let g := X.ofRestrict W.isOpenEmbedding
  let F := SheafedSpace.forgetToPresheafedSpace (C := CommRingCat.{u})
  apply F.map_injective
  show F.map ((nestedOpenIso X U V).hom) ≫ F.map g = F.map f
  dsimp [nestedOpenIso]
  simp only [SheafedSpace.isoMk_hom]
  exact PresheafedSpace.IsOpenImmersion.lift_fac (F.map g) (F.map f)
    (range_ofRestrict_comp_ofRestrict X U V).le

/-- **Two left adjoints of isomorphic right adjoints are isomorphic.** Stated over abstract
categories: elaborated against the ringed-space vocabulary the same term exhausts many times the
default heartbeat budget. -/
def leftAdjointIsoOfRightIso {A : Type*} [Category A] {B : Type*} [Category B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    L₁ ≅ L₂ :=
  adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e.symm)

/-- The right adjoints of the two sides of
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionModulesIso`. The three
direct images compose to the direct image of the composite, and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso_hom_fac` says that composite is the
  inclusion of the image of `V`. -/
def nestedRestrictionRightIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    directImage (nestedOpenIso X U V).inv ⋙
        directImage ((X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding) ⋙
          directImage (X.ofRestrict U.isOpenEmbedding) ≅
      directImage (X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) :=
  let e := nestedOpenIso X U V
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := (X.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding
  let jW := X.ofRestrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding
  have hcomp : e.inv ≫ (jV ≫ jU) = jW := by
    rw [← nestedOpenIso_hom_fac X U V, Iso.inv_hom_id_assoc]
  Functor.isoWhiskerLeft (directImage e.inv) (directImageComp jV jU) ≪≫
    directImageComp e.inv (jV ≫ jU) ≪≫
    eqToIso (congrArg (directImage
      (X := X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) (Y := X)) hcomp)

/-- **Nested restriction is restriction to the image.** Restricting modules to `U`, then to `V`,
then transporting along `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso` is
  restriction to the image of `V` in `X`.
Both sides are left adjoints, and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionRightIso` identifies their right
adjoints. -/
def nestedRestrictionModulesIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    restrictModules.{u} X U ⋙
        restrictModules.{u} (X.restrict U.isOpenEmbedding) V ⋙
          (moduleEquivOfIso (nestedOpenIso X U V)).functor ≅
      restrictModules.{u} X (U.isOpenEmbedding.functor.obj V) :=
  leftAdjointIsoOfRightIso
    (((siteRestrictAdjunction X U).comp
        (siteRestrictAdjunction (X.restrict U.isOpenEmbedding) V)).comp
      (moduleEquivOfIso (nestedOpenIso X U V)).toAdjunction)
    (siteRestrictAdjunction X (U.isOpenEmbedding.functor.obj V))
    (nestedRestrictionRightIso X U V)

/-- The complex form of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionModulesIso`.
-/
def nestedRestrictionComplexIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) (K : CochainComplex (OXMod.{u} X) ℤ) :
    (((moduleEquivOfIso (nestedOpenIso X U V)).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (restrictComplex (restrictComplex K U) V)) ≅
      restrictComplex K (U.isOpenEmbedding.functor.obj V) := by
  have : ((restrictModules.{u} X U) ⋙
      restrictModules.{u} (X.restrict U.isOpenEmbedding) V ⋙
        (moduleEquivOfIso (nestedOpenIso X U V)).functor).PreservesZeroMorphisms := by
    constructor
    intro A B
    ext T x
    rfl
  exact (NatIso.mapHomologicalComplex (nestedRestrictionModulesIso X U V)
    (ComplexShape.up ℤ)).app K

end AlgebraicGeometry.RingedSpace.PseudoCoherence

end
