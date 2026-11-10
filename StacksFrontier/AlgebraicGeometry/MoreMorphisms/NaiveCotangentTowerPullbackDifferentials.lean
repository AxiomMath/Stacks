module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentImmersionDegreeZero
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep

/-!
# The middle term of the conormal sequence of a tower is a geometric pullback

For morphisms of schemes `i : X ⟶ P` and `g : P ⟶ Y` the conormal sequence of the tower of
sheaves of commutative rings

`i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X`

on the Zariski site of `X` has middle term `𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y]`.  This file
identifies that term with the geometric pullback `i^*Ω_{P/Y}` taken along `i`, which is the
coordinate the conormal sequence of [Stacks Project, Tag 01UZ] is written in.  The structural
homomorphism `i⁻¹𝒪_P ⟶ 𝒪_X` has to be locally surjective for the conormal sequence to be
formed at all, so `i` is assumed surjective on stalks; an immersion qualifies.

The identification is a composite of three known comparisons.  The middle term is the
extension of scalars to `𝒪_X` of the corepresenting sheaf `Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y]`
(`Stacks.Sites.Conormal.tensorDifferentialsIso`); that sheaf is the inverse image `i⁻¹Ω_{P/Y}`
by the inverse-image theorem for differentials of [Stacks Project, Tag 08RR]
(`AlgebraicGeometry.SheafOfModules.pullbackDifferentialsIso`); and inverse image followed by
extension of scalars is the pullback of sheaves of modules of [Stacks Project, Tag 0096].

## Main definitions

* `Stacks.NaiveCotangentTower.twoStepFunctor`, `twoStepRightFunctor`, `compAdjunction` and
  `twoStepAdjunction`: the two-step model of `i^*` — the inverse image of sheaves of modules
  followed by extension of scalars along the structural homomorphism — and its adjunction
  with `i_*`.
* `Stacks.NaiveCotangentTower.pullbackIsoComp`: the identification of `i^*` with the two-step
  model, by uniqueness of left adjoints.
* `Stacks.NaiveCotangentTower.crossingStepOne`, `crossingStepTwo`, `crossingStepThree` and
  `crossingAux`: the three factors of the comparison and their composite.
* `Stacks.NaiveCotangentTower.tensorDifferentialsCrossing`: **the comparison**
  `𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y] ≅ i^*Ω_{P/Y}`.

## Main results

* `Stacks.NaiveCotangentTower.tensorDifferentialsCrossing_hom_tensorDifferential`: **the
  comparison on local sections.**  For a section `t` of `𝒪_P` over an open `U`, the local
  section `1 ⊗ d(i⁻¹t)` of the middle term is carried to the image of `d_{P/Y}t` under the
  unit of the module pullback/pushforward adjunction of `i`.  Since two morphisms out of the
  middle term agreeing on those sections are equal, this pins the comparison down, and it is
  the form in which the conormal differential of Stacks 01UZ is stated.
* `Stacks.NaiveCotangentTower.pullbackIsoComp_inv_app_compAdjunction_unit` and
  `crossingStepTwo_hom_apply`: the last two factors on local sections, which is what the
  previous statement is assembled from.

## Implementation notes

`RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` already identifies `i^*` with the
two-step model, but its second adjunction is built by rewriting along
`RingedSpaceModuleAdjunction.modulePushforward_eq`, so its unit is behind a transport and the
formula on local sections cannot be read off it.  `twoStepAdjunction` therefore rebuilds that
adjunction from `CategoryTheory.Adjunction.comp` and
`CategoryTheory.Adjunction.ofNatIsoRight`, both of which have an explicit unit, and
`pullbackIsoComp` is the resulting comparison.  The transport that remains is an `eqToIso`
attached to `modulePushforward_eq`, and `eqToIso_hom_app_val_app_apply` discharges it: the
direct image of sheaves of modules does not change the underlying sections, so that
comparison is the identity on them.

`crossingAux` carries no type ascription and `tensorDifferentialsCrossing` is its one-line
restatement at the spelling the conormal sequence and `AlgebraicGeometry.Scheme.Modules` use.
This is deliberate: the composite crosses the `TopCat.Sheaf` and
`CategoryTheory.Sheaf (Opens.grothendieckTopology _)` spellings of the structure sheaf, and
elaborating it directly under the expected type exhausts the heartbeat budget.

Every proof below is a chain of `Eq.trans` and `congrArg` rather than `rw`.  This is forced:
goals mixing the two spellings of the site are not type-correct at `implicit` transparency,
which is the transparency `rw` builds its motive at.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence
  of an immersion, whose middle term is `i^*Ω_{P/Y}`.
* [Stacks Project, Tag 08TF](https://stacks.math.columbia.edu/tag/08TF), the conormal sequence
  of a tower of sheaves of rings on a site.
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR), the inverse image of
  the sheaf of relative differentials.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), the pullback of
  sheaves of modules along a morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (inverseImageDerivation inverseImageRingHom
  moduleOfDifferentialsOfSite pullbackDifferentialsIso pullbackDifferentialsIso_compatible
  universalDerivation universalDerivationOfSite)
open RingedSpaceModuleAdjunction (modulePullback modulePushforward
  modulePullbackPushforwardAdjunction modulePushforward_eq)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.SheafOfModules (inverseImageBaseRing inverseImageFirstRingMap
  inverseImageMiddleRing ringedSpaceStructureMap)

universe w v₁ u₁ v₂ u₂ u

noncomputable section

namespace Stacks.NaiveCotangentTower

section EqToIso

variable {D₀ : Type u₁} [Category.{v₁} D₀] {C₀ : Type u₂} [Category.{v₂} C₀]
  {J₀ : GrothendieckTopology C₀} {R₀ : CategoryTheory.Sheaf J₀ RingCat.{w}}

/-- The comparison attached to an equality of functors into a category of sheaves of modules
acts as the identity on local sections. -/
theorem eqToIso_hom_app_val_app_apply {F G : D₀ ⥤ _root_.SheafOfModules.{w} R₀} (h : F = G)
    (T : D₀) (U : C₀ᵒᵖ) (x : (F.obj T).val.obj U) (y : (G.obj T).val.obj U) (hxy : HEq x y) :
    (((eqToIso h).hom.app T).val.app U) x = y := by
  subst h
  exact eq_of_heq hxy

end EqToIso

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y)

/-- If `i` is surjective on stalks, the structural homomorphism `i⁻¹𝒪_P ⟶ 𝒪_X` is locally
surjective. -/
instance isLocallySurjective_ringedSpaceStructureMap [SurjectiveOnStalks i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (ringedSpaceStructureMap (ringedSpaceHom i)).hom :=
  Stacks.NaiveCotangentDegreeZero.isLocallySurjective_inverseImageStructureMap i

section Tower

variable [SurjectiveOnStalks i]

/-- The structural homomorphism `i⁻¹𝒪_P ⟶ 𝒪_X`, as the datum that the pullback of sheaves of
modules along a morphism of sheaves of rings over the identity site takes. -/
abbrev ringHom :=
  Stacks.Sites.Conormal.underlyingRingHomForPullback
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (ringedSpaceStructureMap (ringedSpaceHom i))

/-- The unit `𝒪_P ⟶ i_*i⁻¹𝒪_P`, as the datum that the inverse image of sheaves of modules
takes. -/
abbrev invRingHom :=
  inverseImageRingHom ((ringedSpaceHom i).hom.base) P.toRingedSpace.sheaf

/-- Restriction of scalars of sheaves of modules along `ringHom i` is a right adjoint. -/
instance pushforwardRingHom_isRightAdjoint :
    (_root_.SheafOfModules.pushforward.{u} (ringHom i)).IsRightAdjoint :=
  Stacks.Sites.Conormal.differentialPushforwardIsRightAdjoint.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (ringedSpaceStructureMap (ringedSpaceHom i))

/-- The direct image of sheaves of modules along `invRingHom i` is a right adjoint. -/
instance pushforwardInvRingHom_isRightAdjoint :
    (_root_.SheafOfModules.pushforward.{u} (invRingHom i)).IsRightAdjoint :=
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_pushforward_inverseImageRingHom
    ((ringedSpaceHom i).hom.base) P.toRingedSpace.sheaf

/-! ### The two-step model of the pullback -/

/-- The two-step model of `i^*`: the inverse image of sheaves of modules along `i`, followed by
extension of scalars along the structural homomorphism `i⁻¹𝒪_P ⟶ 𝒪_X`. -/
def twoStepFunctor :=
  _root_.SheafOfModules.pullback.{u} (invRingHom i) ⋙
    (_root_.SheafOfModules.pullback.{u} (ringHom i) : _root_.SheafOfModules _ ⥤ _)

/-- The right adjoint of the two-step model: restriction of scalars along the structural
homomorphism, followed by the direct image along the inverse-image unit. -/
def twoStepRightFunctor :=
  _root_.SheafOfModules.pushforward.{u} (ringHom i) ⋙
    _root_.SheafOfModules.pushforward.{u} (invRingHom i)

/-- The two-step model is left adjoint to the composite of the two right adjoints. -/
def compAdjunction : twoStepFunctor i ⊣ twoStepRightFunctor i :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction (invRingHom i)).comp
    (_root_.SheafOfModules.pullbackPushforwardAdjunction (ringHom i))

/-- The two-step model is left adjoint to `i_*`, by
`RingedSpaceModuleAdjunction.modulePushforward_eq`. -/
def twoStepAdjunction : twoStepFunctor i ⊣ modulePushforward (ringedSpaceHom i) :=
  Adjunction.ofNatIsoRight (compAdjunction i)
    (eqToIso (X := twoStepRightFunctor i) (Y := modulePushforward (ringedSpaceHom i))
      (modulePushforward_eq (ringedSpaceHom i)).symm)

/-- **Stacks 0096, the two-step description of `i^*`.**  The pullback of sheaves of modules
along `i` is the inverse image followed by extension of scalars along the structural
homomorphism: both are left adjoint to `i_*`. -/
def pullbackIsoComp : modulePullback (ringedSpaceHom i) ≅ twoStepFunctor i :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (ringedSpaceHom i))
    (twoStepAdjunction i)

omit [SurjectiveOnStalks i] in
/-- **The last factor on local sections.**  The comparison of `i^*` with the two-step model
carries the two-step unit of a local section of `Ω_{P/Y}` back to its image under the unit of
the pullback/pushforward adjunction of `i`. -/
theorem pullbackIsoComp_inv_app_compAdjunction_unit (U : P.Opens)
    (ω : (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g).val.obj (op U)) :
    (((pullbackIsoComp i).inv.app
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
        ((((compAdjunction i).unit.app
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app (op U)) ω)
      = (((modulePullbackPushforwardAdjunction (ringedSpaceHom i)).unit.app
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app (op U)) ω := by
  have key : (modulePullbackPushforwardAdjunction (ringedSpaceHom i)).unit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g) ≫
      (modulePushforward (ringedSpaceHom i)).map ((pullbackIsoComp i).hom.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)) =
      (twoStepAdjunction i).unit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  have key2 : (twoStepAdjunction i).unit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g) =
      (compAdjunction i).unit.app (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g) ≫
        (eqToIso (X := twoStepRightFunctor i) (Y := modulePushforward (ringedSpaceHom i))
          (modulePushforward_eq (ringedSpaceHom i)).symm).hom.app
          ((twoStepFunctor i).obj (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)) :=
    rfl
  have h3 := ConcreteCategory.congr_hom
    (congrArg (fun m => m.val.app (op U)) (key.trans key2)) ω
  have h4 : (((pullbackIsoComp i).hom.app
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
        ((((modulePullbackPushforwardAdjunction (ringedSpaceHom i)).unit.app
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app (op U)) ω) =
      (((compAdjunction i).unit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app (op U)) ω :=
    h3.trans (eqToIso_hom_app_val_app_apply _ _ _ _ _ (HEq.refl _))
  have hcmp : ∀ y, (((pullbackIsoComp i).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
      ((((pullbackIsoComp i).hom.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) y) = y := fun y =>
    ConcreteCategory.congr_hom (congrArg (fun m => m.val.app
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
      ((pullbackIsoComp i).hom_inv_id_app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g))) y
  exact (congrArg (((pullbackIsoComp i).inv.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app
    (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) h4).symm.trans (hcmp _)

/-! ### The three factors of the comparison -/

/-- The first factor: the middle term of the conormal sequence is the extension of scalars of
`Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y]`. -/
def crossingStepOne :=
  Stacks.Sites.Conormal.tensorDifferentialsIso.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i))

/-- The second factor: `Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y]` is the inverse image of `Ω_{P/Y}`. -/
def crossingStepTwo :=
  (_root_.SheafOfModules.pullback.{u} (ringHom i)).mapIso
    (pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
      (AlgebraicGeometry.inverseImageStructureMap g)).symm

/-- The third factor: the two-step model of `i^*Ω_{P/Y}` is `i^*Ω_{P/Y}`. -/
def crossingStepThree :=
  ((pullbackIsoComp i).app (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).symm

omit [SurjectiveOnStalks i] in
/-- **The second factor on local sections.**  The inverse-image comparison of differentials,
extended to `𝒪_X`, carries `1 ⊗ d(i⁻¹t)` to the two-step unit image of `d_{P/Y} t`. -/
theorem crossingStepTwo_hom_apply (U : P.Opens)
    (t : (P.toRingedSpace.sheaf).obj.obj (op U)) :
    (((crossingStepTwo i g).hom.val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
      ((((_root_.SheafOfModules.pullbackPushforwardAdjunction (ringHom i)).unit.app
            (moduleOfDifferentialsOfSite.{u, u, u, u}
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
              (inverseImageMiddleRing (ringedSpaceHom i))
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g)))).val.app
          (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
        ((universalDerivationOfSite.{u, u, u, u}
            (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
            (inverseImageMiddleRing (ringedSpaceHom i))
            (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))).d
          (((invRingHom i).hom.app (op U)) t))))
      = (((compAdjunction i).unit.app
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app (op U))
        ((AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation g).d t) := by
  have hcompat := PresheafOfModulesOfCommRing.Derivation.congr_d
    (pullbackDifferentialsIso_compatible ((ringedSpaceHom i).hom.base)
      (AlgebraicGeometry.inverseImageStructureMap g))
    (((invRingHom i).hom.app (op U)) t)
  have hiso : ∀ y, ((pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
        (AlgebraicGeometry.inverseImageStructureMap g)).inv.val.app
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
      (((pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
        (AlgebraicGeometry.inverseImageStructureMap g)).hom.val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) y) = y := fun y =>
    ConcreteCategory.congr_hom (congrArg (fun m => m.val.app
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
      (Iso.hom_inv_id (pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
        (AlgebraicGeometry.inverseImageStructureMap g)))) y
  have hinv : ((pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
          (AlgebraicGeometry.inverseImageStructureMap g)).inv.val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
        ((universalDerivationOfSite.{u, u, u, u}
            (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
            (inverseImageMiddleRing (ringedSpaceHom i))
            (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))).d
          (((invRingHom i).hom.app (op U)) t))
      = (inverseImageDerivation ((ringedSpaceHom i).hom.base)
          (universalDerivation (AlgebraicGeometry.inverseImageStructureMap g))).val.d
        (((invRingHom i).hom.app (op U)) t) :=
    (congrArg ((pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
      (AlgebraicGeometry.inverseImageStructureMap g)).inv.val.app
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) hcompat).symm.trans (hiso _)
  have hspec := (inverseImageDerivation ((ringedSpaceHom i).hom.base)
    (universalDerivation (AlgebraicGeometry.inverseImageStructureMap g))).2 (op U) t
  have hnat := (_root_.SheafOfModules.pullbackPushforwardAdjunction (ringHom i)).unit.naturality
    (pullbackDifferentialsIso ((ringedSpaceHom i).hom.base)
      (AlgebraicGeometry.inverseImageStructureMap g)).inv
  have hnatel := ConcreteCategory.congr_hom
    (congrArg (fun m => m.val.app (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) hnat)
    ((universalDerivationOfSite.{u, u, u, u}
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i))
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))).d
      (((invRingHom i).hom.app (op U)) t))
  have hcomp := Adjunction.comp_unit_app
    (_root_.SheafOfModules.pullbackPushforwardAdjunction (invRingHom i))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction (ringHom i))
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)
  refine hnatel.symm.trans ?_
  refine Eq.trans (congrArg (((_root_.SheafOfModules.pullbackPushforwardAdjunction
    (ringHom i)).unit.app ((_root_.SheafOfModules.pullback.{u} (invRingHom i)).obj
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g))).val.app
    (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) (hinv.trans hspec)) ?_
  exact (ConcreteCategory.congr_hom
    (congrArg (fun m => m.val.app (op U)) hcomp)
    ((AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation g).d t)).symm

/-! ### The comparison -/

/-- The three-step comparison, with no expected type imposed on it. -/
def crossingAux :=
  crossingStepOne i g ≪≫ crossingStepTwo i g ≪≫ crossingStepThree i g

/-- **The middle term of the conormal sequence of the tower is the geometric pullback.** -/
def tensorDifferentialsCrossing :
    (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))).X₂ ≅
      (AlgebraicGeometry.Scheme.Modules.pullback i).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g) :=
  crossingAux i g

/-- **The comparison on local sections.**  For an open `U` of `P` and a section `t` of `𝒪_P`
over `U`, write `i⁻¹t` for the section of `i⁻¹𝒪_P` over `i ⁻¹ᵁ U` obtained from `t` by the unit
of the inverse-image/direct-image adjunction on sheaves of commutative rings — the section that
`Stacks.Conormal.Sites.coborderUnit` is built from.  The comparison carries the local section
`1 ⊗ d(i⁻¹t)` of the middle term to the image of `d_{P/Y}t` under the unit of the module
pullback/pushforward adjunction of `i`, read over `U`.

This pins the comparison down: two morphisms out of the middle term agreeing on the local
sections `Stacks.Sites.Conormal.tensorDifferential` are equal
(`Stacks.Sites.Conormal.tensorSheaf_hom_ext`). -/
theorem tensorDifferentialsCrossing_hom_tensorDifferential (U : P.Opens)
    (t : P.presheaf.obj (op U)) :
    (((tensorDifferentialsCrossing i g).hom.val.app (op (i ⁻¹ᵁ U)))
      (Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
        (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
        (ringedSpaceStructureMap (ringedSpaceHom i))
        (op (i ⁻¹ᵁ U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
          P.sheaf).hom.app (op U)).hom t)))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).val.app (op U))
        ((AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation g).d t) := by
  have hsplit : ∀ x, (((tensorDifferentialsCrossing i g).hom.val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) x)
      = (((crossingStepThree i g).hom.val.app
          (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
        (((crossingStepTwo i g).hom.val.app
            (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
          (((crossingStepOne i g).hom.val.app
              (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) x))) := fun _ => rfl
  refine (hsplit _).trans ?_
  refine Eq.trans (congrArg (fun y => (((crossingStepThree i g).hom.val.app
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U)))
    ((((crossingStepTwo i g).hom.val.app
        (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))) y))))
    (Stacks.Sites.Conormal.tensorDifferentialsIso_d.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
      (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
      (ringedSpaceStructureMap (ringedSpaceHom i))
      (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))
      (((invRingHom i).hom.app (op U)) t))) ?_
  refine Eq.trans (congrArg (((crossingStepThree i g).hom.val.app
    (op ((Opens.map ((ringedSpaceHom i).hom.base)).obj U))))
    (crossingStepTwo_hom_apply i g U t)) ?_
  exact pullbackIsoComp_inv_app_compAdjunction_unit i g U _

end Tower

end Stacks.NaiveCotangentTower

end

end
