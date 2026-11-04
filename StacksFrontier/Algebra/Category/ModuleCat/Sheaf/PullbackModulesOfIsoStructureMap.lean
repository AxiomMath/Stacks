module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of sheaves of modules along a morphism of ringed topoi with invertible structure map

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose structure map in
inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` is an *isomorphism* — the situation of Stacks 08PA, where
`O_C` is by construction an inverse image of the structure sheaf of a common base. The pullback
of sheaves of modules `f^*G = O_C ⊗_{f⁻¹O_D} f⁻¹G` of Stacks 03D6 then performs no genuine
extension of scalars: its second factor is an equivalence. In particular extension of scalars
along `f♯` *has a left adjoint*.

Extension of scalars is always a left adjoint, of restriction of scalars along the same map; when
`f♯` is invertible it is a right adjoint as well, so the pullback of modules has a left adjoint as
soon as its geometric factor does.

## Main results

* `AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage`: the two
  inverse-image forms of the structure map agree — the one taken through the adjunction for
  sheaves of *commutative* rings, and the one taken through the adjunction for sheaves of rings
  along which scalars are actually extended.
* `AlgebraicGeometry.RingedToposHom`'s
  `isIso_fSharpInverseImageRing_of_hasSheafCompose_forgetCommRingCat`: consequently, if the
  commutative-ring form is an isomorphism then so is the ring form.
* `Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso`:
  extension of scalars along an invertible structure map is restriction of scalars along its
  inverse.
* `Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharp_isRightAdjoint`:
  extension of scalars along an invertible structure map has a left adjoint.

## Implementation notes

A `AlgebraicGeometry.RingedToposHom` carries only the direct-image form `f♯ : O_D ⟶ f_*O_C` of
the structure map, and the inverse-image form is *derived* from it — twice over, through two
different adjunctions. `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is the adjunct for
sheaves of commutative rings, which is the form in which Stacks 08PA's identification
`g⁻¹O_C ≅ O_{C'}` is available and is invertible, and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing` is the adjunct for sheaves of rings,
which is the form the change-of-rings adjunction of Stacks 03CZ uses.
`forgetCommRingSheaf_map_fSharpInverseImage` identifies the two.

The identification is proved on underlying sheaves of **sets**, where both forms are the adjunct
of one and the same map under `f⁻¹ ⊣ f_*` for sheaves of sets
(`Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv` and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing_adjunct`), and then transported back
along the faithfulness of `sheafCompose _ (forget RingCat)`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w'})]

/-- The inverse-image form of the structure map of a morphism of ringed topoi taken through the
adjunction for sheaves of *commutative* rings has, as its underlying morphism of sheaves of
rings, the inverse-image form taken through the adjunction for sheaves of rings. Both are the
adjunct of the same morphism of sheaves of sets under `f⁻¹ ⊣ f_*`. -/
theorem forgetCommRingSheaf_map_fSharpInverseImage (f : RingedToposHom X Y) :
    (Stacks.forgetCommRingSheaf X.J).map f.fSharpInverseImage = f.fSharpInverseImageRing := by
  refine (sheafCompose X.J (forget RingCat.{w})).map_injective
    (((f.toToposHom.adj.homEquiv _ _).eq_symm_apply.2 (Eq.symm ?_)).trans
      ((f.toToposHom.adj.homEquiv _ _).eq_symm_apply.2
        f.fSharpInverseImageRing_adjunct.symm).symm)
  refine Eq.trans ?_ (forget_map_commRingImageAdjunction_homEquiv f.toToposHom Y.O X.O
    f.fSharpInverseImage)
  exact congrArg (sheafCompose Y.J (forget CommRingCat.{w'})).map
    (((commRingImageAdjunction f.toToposHom).homEquiv Y.O X.O).apply_symm_apply f.fSharp).symm

/-- If the structure map of a morphism of ringed topoi is an isomorphism of sheaves of
commutative rings, then the morphism of sheaves of *rings* along which scalars are extended to
form the pullback of modules is an isomorphism too. -/
instance isIso_fSharpInverseImageRing_of_hasSheafCompose_forgetCommRingCat
    (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage] :
    IsIso f.fSharpInverseImageRing :=
  f.forgetCommRingSheaf_map_fSharpInverseImage ▸
    ((Stacks.forgetCommRingSheaf X.J).mapIso (asIso f.fSharpInverseImage)).isIso_hom

end AlgebraicGeometry.RingedToposHom

namespace Stacks.Sheaves.RingedToposModules.RingedToposHom

universe v u w v' u' w'

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

/-- **Extension of scalars along an invertible structure map is restriction of scalars along its
inverse.** Both are left adjoint to restriction of scalars along the structure map itself — the
first by the change-of-rings adjunction of Stacks 03CZ, the second because restriction of scalars
along an isomorphism is an equivalence — so they agree by uniqueness of left adjoints. -/
def extendScalarsFSharpIsoRestrictScalarsOfIsIso : extendScalarsFSharp f ≅
    SheafOfModules.restrictScalars (asIso f.fSharpInverseImage).inv := by
  have adj : SheafOfModules.restrictScalars (asIso f.fSharpInverseImage).inv ⊣
      SheafOfModules.restrictScalars (commRingSheafMap X.J (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) := by
    rw [commRingSheafMap_fSharpCommRing]
    exact (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (asIso f.fSharpInverseImage)).toAdjunction
  exact (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).leftAdjointUniq adj

/-- **Extension of scalars along an invertible structure map has a left adjoint**, being
restriction of scalars along the inverse, which is an equivalence. -/
instance extendScalarsFSharp_isRightAdjoint : (extendScalarsFSharp f).IsRightAdjoint :=
  have : (SheafOfModules.restrictScalars (asIso f.fSharpInverseImage).inv).IsRightAdjoint :=
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (asIso f.fSharpInverseImage)).symm.isRightAdjoint_inverse
  Functor.isRightAdjoint_of_iso
    (F := SheafOfModules.restrictScalars (asIso f.fSharpInverseImage).inv)
    f.extendScalarsFSharpIsoRestrictScalarsOfIsIso.symm

end Stacks.Sheaves.RingedToposModules.RingedToposHom

/-! ## The inverse image of modules along a continuous functor of sites has a left adjoint -/

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{ww})
  [UnivLE.{vv, ww}] [UnivLE.{vv', ww}] [UnivLE.{uu, ww}]
  [HasWeakSheafify K AddCommGrpCat.{ww}] [K.WEqualsLocallyBijective AddCommGrpCat.{ww}]

/-- Restriction of scalars along the comparison of the inverse image of a sheaf of rings with its
restriction has a left adjoint, that comparison being an isomorphism. -/
instance restrictScalars_restrictionRingIso_isRightAdjoint :
    (SheafOfModules.restrictScalars.{ww} (restrictionRingIso J K G O).hom).IsRightAdjoint :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (restrictionRingIso J K G O)).isRightAdjoint_inverse

/-- **The inverse image of sheaves of modules along the restriction functor induced by a
continuous functor of sites has a left adjoint.** It is restriction of sheaves of modules along
`G` followed by restriction of scalars along an isomorphism
(`Stacks.Sheaves.ToposPullback.restrictionModuleIso`), the first of which has the left adjoint
`SheafOfModules.pullback` of Stacks 03D7 and the second of which is an equivalence. The two
sites, their morphisms and the module sections live in independent universes, the sections
being required only to dominate the two sites' object and morphism universes. -/
instance pullbackModuleFunctor_restriction_isRightAdjoint :
    (pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) O).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (restrictionModuleIso J K G O).symm

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- `pullbackModuleFunctor_restriction_isRightAdjoint` for a functor that is only *equal* to the
restriction functor rather than spelled as it. -/
lemma pullbackModuleFunctor_isRightAdjoint_of_eq
    {Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ]
    (hΦ : Φ = G.sheafPushforwardContinuous (Type ww) J K) :
    (pullbackModuleFunctor J Φ O).IsRightAdjoint := by
  subst hΦ
  infer_instance

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- **The inverse image of sheaves of modules of Stacks 03D2 along a morphism of topoi whose
inverse image is restriction along a continuous functor of sites has a left adjoint.** -/
lemma inverseImageModules_isRightAdjoint_of_eq
    (f : _root_.MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))
    (hf : f.inverseImage = G.sheafPushforwardContinuous (Type ww) J K) :
    (Stacks.Sheaves.RingedToposModules.inverseImageModules f O).IsRightAdjoint :=
  pullbackModuleFunctor_isRightAdjoint_of_eq J K G O hf

end Stacks.Sheaves.ToposPullback

/-! ## The pullback of modules along a morphism of ringed topoi with invertible structure map -/

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

/-- The structure map along which the pullback of modules extends scalars is an isomorphism,
stated for the morphism `AlgebraicGeometry.RingedToposHom.toModulesHom` of ringed topoi of the
modules development. -/
instance isIso_toModulesHom_fSharpInverseImage :
    IsIso f.toModulesHom.fSharpInverseImage :=
  inferInstanceAs (IsIso f.fSharpInverseImageRing)

/-- **The pullback of sheaves of modules along a morphism of ringed topoi whose structure map is
invertible has a left adjoint as soon as its geometric factor does.** The pullback is the inverse
image of Stacks 03D2 followed by extension of scalars along the structure map, and an invertible
structure map makes the second factor an equivalence. -/
instance pullbackModules_isRightAdjoint
    [(Stacks.Sheaves.RingedToposModules.inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).IsRightAdjoint] :
    (f.toModulesHom.pullbackModules).IsRightAdjoint :=
  have a₁ := Adjunction.ofIsRightAdjoint
    (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp f.toModulesHom)
  have a₂ := Adjunction.ofIsRightAdjoint
    (Stacks.Sheaves.RingedToposModules.inverseImageModules f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
  (a₁.comp a₂).isRightAdjoint

end AlgebraicGeometry.RingedToposHom

end
