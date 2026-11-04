module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitDescriptionEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperModelSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidOfSliceObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemPropertiesOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SystemMorphismOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesianOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmoothOfAlgebraicLimit

/-!
# Descending a groupoid in algebraic spaces along a Noetherian limit

Let `Y = lim Y_i` be the limit of a Noetherian limit system (Situation 0CP6) and let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `Y` whose object and arrow spaces are
quasi-separated and of finite type over `Y`. This file carries out the part of the proof of
Stacks 0CQ1 which, using the limit descriptions of Stacks 0CP9 and the morphisms of inverse
systems of Stacks 0CPA, produces inverse systems `(U_i)` and `(R_i)` over `(Y_i)` and morphisms
of systems `(s_i)`, `(t_i)`, `(c_i)`, `(e_i)`, `(i_i)` which, at every sufficiently late stage,
form a groupoid in algebraic spaces over `Y_i`.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianLimitSystem.limitSpace`,
  `AlgebraicGeometry.Space.NoetherianLimitSystem.stageSpace`: the limit and the stages of a
  Noetherian limit system as algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.PreDescent`: diagrams as in Stacks 0CP8 for the
  spaces of objects, arrows, composable pairs and triples of a groupoid over `Y`, with morphisms
  of their image systems on a common tail inducing all the structure maps of the groupoid.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent`: such data satisfying, at every
  stage of the tail, the laws of a groupoid, with smooth source and target and with
  `R = U ×_{U_i} R_i` along `s` and `t`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.stageGroupoid`: the groupoid
  `(U_i, R_i, s_i, t_i, c_i)` in algebraic spaces over `Y_i` at a stage `i` of the tail.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.eventually_eq`,
  `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.eventually_comp_eq`,
  `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.eventually_comp_eq_comp`,
  `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.eventually_comp_eq_id`: the eventual
  uniqueness of Stacks 0CPA applied to composites of morphisms of image systems, possibly
  defined on different tails.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.PreDescent.nonempty`: limit descriptions exist
  for any diagrams of the four spaces (Stacks 0CPA).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.nonempty`: the groupoid laws,
  smoothness and the cartesian squares hold on a late tail, by Stacks 0CPC, 0CPD and 0CPF.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.stageGroupoid_isSmooth` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.isClosedImmersion_objects`: the stage
  groupoid is smooth and `U ⟶ Y ×_{Y_i} U_i` is a closed immersion.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent.nonempty_of_noetherianApproximation`:
  the descent, from the inputs of the staged Stacks 0CP7.

## Implementation notes

The source assumes the laws of the stage groupoid to follow from "the uniqueness of Stacks 0CPA";
here every law is an equation between composites of morphisms of image systems, and
`AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.eventually_comp_eq_comp` and its variants
carry it to a late stage. Associativity is checked on the image system of the space of
composable triples, which Stacks 0CPF identifies with `T_i ×_{R_i} T_i` at late stages. No bound
on the size of the index set is assumed anywhere.

## References

* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace NoetherianLimitSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  (D : NoetherianLimitSystem B S hS hZ I)

/-- The limit `Y` of a Noetherian limit system, as an algebraic space. -/
abbrev limitSpace : AlgebraicSpaces B S hS := ⟨D.limitCone.pt, D.limit_isAlgebraicSpace⟩

/-- The stage `Y_i` of a Noetherian limit system, as an algebraic space. -/
abbrev stageSpace (i : I) : AlgebraicSpaces B S hS :=
  ⟨D.system.obj (op i), D.system_isAlgebraicSpace i⟩

/-- The projection `Y ⟶ Y_i`, as a morphism of algebraic spaces. -/
noncomputable abbrev limitProjection (i : I) : D.limitSpace ⟶ D.stageSpace i :=
  ObjectProperty.homMk (D.limitCone.π.app (op i))

end NoetherianLimitSystem

namespace GoodDiagram.SystemMorphism

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  {D : NoetherianLimitSystem B S hS hZ I}
  {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
  {pY : Y ⟶ D.limitCone.pt} {pZ : Z ⟶ D.limitCone.pt}
  {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY}
  {GZ : GoodDiagram B S hS hZ D pZ}

/-- The composite of two morphisms of image systems, on a common later tail. -/
theorem exists_comp {f : X ⟶ Y} {g : Y ⟶ Z} {i₁ i₂ : I} {h₁X : GX.index ≤ i₁}
    {h₁Y : GY.index ≤ i₁} {h₂Y : GY.index ≤ i₂} {h₂Z : GZ.index ≤ i₂}
    (F : SystemMorphism GX GY f i₁ h₁X h₁Y) (G : SystemMorphism GY GZ g i₂ h₂Y h₂Z) {n : I}
    (h₁ : i₁ ≤ n) (h₂ : i₂ ≤ n) :
    ∃ C : SystemMorphism GX GZ (f ≫ g) n (h₁X.trans h₁) (h₂Z.trans h₂),
      ∀ j : Over (op n), C.maps.app j = F.maps.app ((Over.map (homOfLE h₁).op).obj j) ≫
        G.maps.app ((Over.map (homOfLE h₂).op).obj j) :=
  ⟨{ maps :=
      { app := fun j => F.maps.app ((Over.map (homOfLE h₁).op).obj j) ≫
          G.maps.app ((Over.map (homOfLE h₂).op).obj j)
        naturality := fun _ _ v =>
          (Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) (F.maps.naturality ((Over.map (homOfLE h₁).op).map v))).trans
            ((Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) (G.maps.naturality ((Over.map (homOfLE h₂).op).map v))).trans
              (Category.assoc _ _ _).symm))) }
     over_base := fun j =>
       (Category.assoc _ _ _).trans
         ((congrArg (_ ≫ ·) (G.over_base ((Over.map (homOfLE h₂).op).obj j))).trans
           (F.over_base ((Over.map (homOfLE h₁).op).obj j)))
     induces := fun j =>
       (Category.assoc _ _ _).symm.trans
         ((congrArg (· ≫ _) (F.induces ((Over.map (homOfLE h₁).op).obj j))).trans
           ((Category.assoc _ _ _).trans
             ((congrArg (f ≫ ·) (G.induces ((Over.map (homOfLE h₂).op).obj j))).trans
               (Category.assoc _ _ _).symm))) }, fun _ => rfl⟩

/-- The identity morphism of an image system, on a tail. -/
theorem exists_id {n : I} (h : GX.index ≤ n) :
    ∃ C : SystemMorphism GX GX (𝟙 X) n h h, ∀ j : Over (op n), C.maps.app j = 𝟙 _ :=
  ⟨{ maps := 𝟙 _
     over_base := fun _ => Category.id_comp _
     induces := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm }, fun _ => rfl⟩

variable (hX : IsAlgebraicSpace B S hS X) (hXqs : IsQuasiSeparated B S hS pX)
include hX hXqs

/-- **Eventual uniqueness of Stacks 0CPA, on two tails.** Two morphisms of image systems inducing
the same morphism `f : X ⟶ Y`, defined on possibly different tails, have the same component at
every sufficiently late stage. -/
theorem eventually_eq {f : X ⟶ Y} {i₁ i₂ : I} {h₁X : GX.index ≤ i₁} {h₁Y : GY.index ≤ i₁}
    {h₂X : GX.index ≤ i₂} {h₂Y : GY.index ≤ i₂} (F : SystemMorphism GX GY f i₁ h₁X h₁Y)
    (G : SystemMorphism GX GY f i₂ h₂X h₂Y) :
    ∀ᶠ i in Filter.atTop, ∀ (h₁ : i₁ ≤ i) (h₂ : i₂ ≤ i),
      F.maps.app (Over.mk (homOfLE h₁).op) = G.maps.app (Over.mk (homOfLE h₂).op) := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_ge_ge i₁ i₂
  obtain ⟨m, hnm, hm⟩ :=
    eventually_eq_systemMorphism_of_algebraicLimit hX hXqs (F.restrict hn₁) (G.restrict hn₂)
  exact Filter.eventually_atTop.2 ⟨m, fun i hi _ _ => hm (Over.mk (homOfLE (hnm.trans hi)).op) hi⟩

/-- **Morphisms of image systems inducing a given morphism exist on every late tail.** -/
theorem eventually_nonempty {f : X ⟶ Y} (hf : f ≫ pY = pX) (GX : GoodDiagram B S hS hZ D pX)
    (GY : GoodDiagram B S hS hZ D pY) :
    ∀ᶠ n in Filter.atTop, ∃ (hnX : GX.index ≤ n) (hnY : GY.index ≤ n),
      Nonempty (SystemMorphism GX GY f n hnX hnY) := by
  obtain ⟨i₀, hiX, hiY, ⟨F⟩⟩ := exists_systemMorphism_of_algebraicLimit hX hXqs f hf GX GY
  exact Filter.eventually_atTop.2 ⟨i₀, fun n hn => ⟨hiX.trans hn, hiY.trans hn, ⟨F.restrict hn⟩⟩⟩

/-- **A composite of morphisms of image systems is eventually the given morphism** inducing the
composite in the limit. -/
theorem eventually_comp_eq {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    {i₁ i₂ i₃ : I} {h₁X : GX.index ≤ i₁} {h₁Y : GY.index ≤ i₁} {h₂Y : GY.index ≤ i₂}
    {h₂Z : GZ.index ≤ i₂} {h₃X : GX.index ≤ i₃} {h₃Z : GZ.index ≤ i₃}
    (F : SystemMorphism GX GY f i₁ h₁X h₁Y) (G : SystemMorphism GY GZ g i₂ h₂Y h₂Z)
    (H : SystemMorphism GX GZ h i₃ h₃X h₃Z) :
    ∀ᶠ i in Filter.atTop, ∀ (h₁ : i₁ ≤ i) (h₂ : i₂ ≤ i) (h₃ : i₃ ≤ i),
      F.maps.app (Over.mk (homOfLE h₁).op) ≫ G.maps.app (Over.mk (homOfLE h₂).op) =
        H.maps.app (Over.mk (homOfLE h₃).op) := by
  subst hfg
  obtain ⟨n, hn₁, hn₂⟩ := exists_ge_ge i₁ i₂
  obtain ⟨C, hC⟩ := exists_comp F G hn₁ hn₂
  filter_upwards [eventually_eq hX hXqs C H, Filter.eventually_ge_atTop n] with i hi hni
  intro h₁ h₂ h₃
  have := hi hni h₃
  rw [hC] at this
  exact this

/-- **Two composites of morphisms of image systems inducing the same morphism agree
eventually.** -/
theorem eventually_comp_eq_comp {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z} {pY' : Y' ⟶ D.limitCone.pt} {GY' : GoodDiagram B S hS hZ D pY'}
    (hfg : f ≫ g = f' ≫ g')
    {i₁ i₂ i₃ i₄ : I} {h₁X : GX.index ≤ i₁} {h₁Y : GY.index ≤ i₁} {h₂Y : GY.index ≤ i₂}
    {h₂Z : GZ.index ≤ i₂} {h₃X : GX.index ≤ i₃} {h₃Y : GY'.index ≤ i₃}
    {h₄Y : GY'.index ≤ i₄} {h₄Z : GZ.index ≤ i₄}
    (F : SystemMorphism GX GY f i₁ h₁X h₁Y) (G : SystemMorphism GY GZ g i₂ h₂Y h₂Z)
    (F' : SystemMorphism GX GY' f' i₃ h₃X h₃Y) (G' : SystemMorphism GY' GZ g' i₄ h₄Y h₄Z) :
    ∀ᶠ i in Filter.atTop, ∀ (h₁ : i₁ ≤ i) (h₂ : i₂ ≤ i) (h₃ : i₃ ≤ i) (h₄ : i₄ ≤ i),
      F.maps.app (Over.mk (homOfLE h₁).op) ≫ G.maps.app (Over.mk (homOfLE h₂).op) =
        F'.maps.app (Over.mk (homOfLE h₃).op) ≫ G'.maps.app (Over.mk (homOfLE h₄).op) := by
  obtain ⟨n, hn₃, hn₄⟩ := exists_ge_ge i₃ i₄
  obtain ⟨C, hC⟩ := exists_comp F' G' hn₃ hn₄
  filter_upwards [eventually_comp_eq hX hXqs hfg F G C, Filter.eventually_ge_atTop n]
    with i hi hni
  intro h₁ h₂ h₃ h₄
  have := hi h₁ h₂ hni
  rw [hC] at this
  exact this

/-- **A composite of morphisms of image systems inducing the identity is eventually the
identity.** -/
theorem eventually_comp_eq_id {f : X ⟶ Y} {g : Y ⟶ X} (hfg : f ≫ g = 𝟙 X)
    {i₁ i₂ : I} {h₁X : GX.index ≤ i₁} {h₁Y : GY.index ≤ i₁} {h₂Y : GY.index ≤ i₂}
    {h₂X : GX.index ≤ i₂}
    (F : SystemMorphism GX GY f i₁ h₁X h₁Y) (G : SystemMorphism GY GX g i₂ h₂Y h₂X) :
    ∀ᶠ i in Filter.atTop, ∀ (h₁ : i₁ ≤ i) (h₂ : i₂ ≤ i),
      F.maps.app (Over.mk (homOfLE h₁).op) ≫ G.maps.app (Over.mk (homOfLE h₂).op) = 𝟙 _ := by
  obtain ⟨C, hC⟩ := exists_id (GX := GX) le_rfl
  filter_upwards [eventually_comp_eq hX hXqs hfg F G C,
    Filter.eventually_ge_atTop GX.index] with i hi hni
  intro h₁ h₂
  have := hi h₁ h₂ hni
  rw [hC] at this
  exact this

end GoodDiagram.SystemMorphism

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  {D : NoetherianLimitSystem B S hS hZ I} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {pX : X ⟶ D.limitCone.pt}

/-- **The members of the image system are of finite presentation over their stages** when `X`
is quasi-separated over `B`: `X_{i'} ⟶ B_{i'}` is of finite type, being a closed immersion
followed by a base change of the model, and quasi-separated, its source being absolutely
quasi-separated; the stage is Noetherian (Stacks 06G4). -/
theorem isFinitePresentation_stageImage_ι_fst (G : GoodDiagram B S hS hZ D pX)
    (hX : IsAlgebraicSpace B S hS X) (hqs : IsQuasiSeparated B S hS pX) (j : Over (op G.index)) :
    IsFinitePresentation B S hS
      ((stageImage G j).ι ≫ pullback.fst (D.system.map j.hom) G.modelMap) :=
  isFinitePresentation_of_isFiniteType B S hS (imageSystem_isAlgebraicSpace G j)
    (D.system_isAlgebraicSpace j.left.unop) _ (D.noetherian j.left.unop).2.2
    ⟨isLocallyOfFiniteType_comp B S hS (imageSystem_isAlgebraicSpace G j)
      (isAlgebraicSpace_stageTarget G j) (D.system_isAlgebraicSpace j.left.unop) _ _
      (isLocallyOfFiniteType_of_isImmersion B S hS _
        (isImmersion_of_isClosedImmersion B S hS (isClosedSubspace_stageImage G j).2))
      (isLocallyOfFiniteType_stageTarget_fst G j),
     isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (D.system_isAlgebraicSpace j.left.unop)
      (D.noetherian j.left.unop).2.1 (imageSystem_isQuasiCompactSpace G j) _⟩
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ
      (imageSystem_isAlgebraicSpace G j)
      (imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit G hX hqs j) _)

end GoodDiagram

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z Z' : AlgebraicSpaces B S hS}

/-- A map `a : R ⟶ U` over the base whose base change commutes with the projections is a base
change of `a`, as in `isPullback_baseChange_source` and `isPullback_baseChange_target`. -/
private theorem isPullback_baseChange_of_comp (G : GroupoidInAlgebraicSpaces B S hS Z)
    (f : Z' ⟶ Z) {a : G.arrows.obj ⟶ G.objects.obj}
    {a' : (baseChange G f).groupoid.arrows.obj ⟶ (baseChange G f).groupoid.objects.obj}
    (ha : a ≫ G.objectsToBase.hom = G.arrowsToBase.hom)
    (h₁ : a' ≫ pullback.fst f.hom G.objectsToBase.hom = pullback.fst f.hom G.arrowsToBase.hom)
    (h₂ : a' ≫ pullback.snd f.hom G.objectsToBase.hom =
      pullback.snd f.hom G.arrowsToBase.hom ≫ a) :
    IsPullback (pullback.snd f.hom G.arrowsToBase.hom) a' a
      (pullback.snd f.hom G.objectsToBase.hom) := by
  refine IsPullback.of_bot ?_ h₂.symm
    (IsPullback.of_hasPullback f.hom G.objectsToBase.hom).flip
  exact (IsPullback.of_hasPullback f.hom G.arrowsToBase.hom).flip.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) ((Category.id_comp _).trans h₁.symm |>.trans
      (Category.comp_id _).symm)
    ((Category.id_comp _).trans ha.symm |>.trans (Category.comp_id _).symm) (by simp)

/-- **The source map of a base-changed groupoid is a base change of the source map**: for a
groupoid `(U, R, s, t, c)` over `Z` and `f : Z' ⟶ Z`, the square formed by `Z' ×_Z R ⟶ R`,
the source map of `Z' ×_Z (U, R, s, t, c)`, `s` and `Z' ×_Z U ⟶ U` is cartesian. -/
theorem isPullback_baseChange_source (G : GroupoidInAlgebraicSpaces B S hS Z) (f : Z' ⟶ Z) :
    IsPullback (pullback.snd f.hom G.arrowsToBase.hom) (baseChange G f).groupoid.source.hom
      G.source.hom (pullback.snd f.hom G.objectsToBase.hom) :=
  isPullback_baseChange_of_comp G f (congrArg (fun k => k.hom) G.source_over)
    (baseChange_source_comp_fst G f) (baseChange_source_comp_snd G f)

/-- **The target map of a base-changed groupoid is a base change of the target map.** -/
theorem isPullback_baseChange_target (G : GroupoidInAlgebraicSpaces B S hS Z) (f : Z' ⟶ Z) :
    IsPullback (pullback.snd f.hom G.arrowsToBase.hom) (baseChange G f).groupoid.target.hom
      G.target.hom (pullback.snd f.hom G.objectsToBase.hom) :=
  isPullback_baseChange_of_comp G f (congrArg (fun k => k.hom) G.target_over)
    (baseChange_target_comp_fst G f) (baseChange_target_comp_snd G f)

/-- **The base change of a smooth groupoid is smooth**, by Stacks 03ZE applied to the two
cartesian squares `isPullback_baseChange_source` and `isPullback_baseChange_target`. -/
theorem isSmooth_baseChange (G : GroupoidInAlgebraicSpaces B S hS Z) (f : Z' ⟶ Z)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    GroupoidInAlgebraicSpaces.IsSmooth B S hS (baseChange G f).groupoid :=
  ⟨(isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS G.arrows.property (baseChange G f).groupoid.objects.property
        G.objects.property (baseChange G f).groupoid.arrows.property
        (isPullback_baseChange_source G f)) hG.1,
    (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS G.arrows.property (baseChange G f).groupoid.objects.property
        G.objects.property (baseChange G f).groupoid.arrows.property
        (isPullback_baseChange_target G f)) hG.2⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open Space Space.GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  {D : NoetherianLimitSystem B S hS hZ I}

section Pairs

variable {Y : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Y)

/-- The structure morphism `R ×_{s, U, t} R ⟶ Y` of the space of composable pairs. -/
noncomputable abbrev pairsToBase : (groupoidPresheafObject G).pairs ⟶ Y.obj :=
  (groupoidPresheafObject G).fst ≫ G.arrowsToBase.hom

/-- The structure morphism of the space of composable triples to the base. -/
noncomputable abbrev triplesToBase : (groupoidPresheafObject G).triples ⟶ Y.obj :=
  (groupoidPresheafObject G).fst₃ ≫ pairsToBase G

/-- The space `R ×_{s, U, t} R` of composable pairs is an algebraic space. -/
theorem isAlgebraicSpace_pairs : IsAlgebraicSpace B S hS (groupoidPresheafObject G).pairs :=
  (groupoidObject G).pairs.property

/-- The space of composable triples is an algebraic space. -/
theorem isAlgebraicSpace_triples : IsAlgebraicSpace B S hS (groupoidPresheafObject G).triples :=
  (groupoidObject G).triples.property

/-- The source map `s : R ⟶ U` commutes with the structure morphisms to the base. -/
theorem source_comp_objectsToBase :
    G.source.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
  congrArg (fun k => k.hom) G.source_over

/-- The target map `t : R ⟶ U` commutes with the structure morphisms to the base. -/
theorem target_comp_objectsToBase :
    G.target.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
  congrArg (fun k => k.hom) G.target_over

/-- The second projection `R ×_{s, U, t} R ⟶ R` followed by the structure morphism of `R` is
the structure morphism `pairsToBase` of the composable pairs. -/
theorem snd_comp_arrowsToBase :
    (groupoidPresheafObject G).snd ≫ G.arrowsToBase.hom = pairsToBase G :=
  calc (groupoidPresheafObject G).snd ≫ G.arrowsToBase.hom
      = (groupoidPresheafObject G).snd ≫ (groupoidPresheafObject G).target ≫
          G.objectsToBase.hom := congrArg (_ ≫ ·) (target_comp_objectsToBase G).symm
    _ = ((groupoidPresheafObject G).snd ≫ (groupoidPresheafObject G).target) ≫
          G.objectsToBase.hom := (Category.assoc _ _ _).symm
    _ = ((groupoidPresheafObject G).fst ≫ (groupoidPresheafObject G).source) ≫
          G.objectsToBase.hom :=
        congrArg (· ≫ G.objectsToBase.hom) (groupoidPresheafObject G).isPullback_pairs.w.symm
    _ = (groupoidPresheafObject G).fst ≫ (groupoidPresheafObject G).source ≫
          G.objectsToBase.hom := Category.assoc _ _ _
    _ = pairsToBase G := congrArg (_ ≫ ·) (source_comp_objectsToBase G)

/-- The composition `c : R ×_{s, U, t} R ⟶ R` commutes with the structure morphisms to the
base. -/
theorem comp_comp_arrowsToBase :
    (groupoidPresheafObject G).comp ≫ G.arrowsToBase.hom = pairsToBase G :=
  congrArg (fun k => k.hom) G.comp_over

/-- The identity `e : U ⟶ R` commutes with the structure morphisms to the base. -/
theorem identity_comp_arrowsToBase :
    (groupoidPresheafObject G).identity ≫ G.arrowsToBase.hom = G.objectsToBase.hom :=
  (congrArg ((groupoidPresheafObject G).identity ≫ ·) (source_comp_objectsToBase G).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.objectsToBase.hom) (groupoidPresheafObject G).identity_source).trans
        (Category.id_comp _)))

/-- The inverse `i : R ⟶ R` commutes with the structure morphism of `R` to the base. -/
theorem inverse_comp_arrowsToBase :
    (groupoidPresheafObject G).inverse ≫ G.arrowsToBase.hom = G.arrowsToBase.hom :=
  (congrArg ((groupoidPresheafObject G).inverse ≫ ·) (source_comp_objectsToBase G).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.objectsToBase.hom) (groupoidPresheafObject G).inverse_source).trans
        (target_comp_objectsToBase G)))

/-- The projection `snd₃` from composable triples to composable pairs commutes with the
structure morphisms to the base. -/
theorem snd₃_comp_pairsToBase :
    (groupoidPresheafObject G).snd₃ ≫ pairsToBase G = triplesToBase G :=
  calc (groupoidPresheafObject G).snd₃ ≫ pairsToBase G
      = ((groupoidPresheafObject G).snd₃ ≫ (groupoidPresheafObject G).fst) ≫
          G.arrowsToBase.hom := (Category.assoc _ _ _).symm
    _ = ((groupoidPresheafObject G).fst₃ ≫ (groupoidPresheafObject G).snd) ≫
          G.arrowsToBase.hom :=
        congrArg (· ≫ G.arrowsToBase.hom) (groupoidPresheafObject G).isPullback_triples.w.symm
    _ = (groupoidPresheafObject G).fst₃ ≫ (groupoidPresheafObject G).snd ≫
          G.arrowsToBase.hom := Category.assoc _ _ _
    _ = triplesToBase G := congrArg (_ ≫ ·) (snd_comp_arrowsToBase G)

/-- If `a` lies over `pT`, then the pair `(a, b)` lifted to `R ×_{s, U, t} R` lies over `pT`. -/
theorem liftPair_comp_pairsToBase {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : T ⟶ (groupoidPresheafObject G).arrows} {pT : T ⟶ Y.obj}
    (w : a ≫ (groupoidPresheafObject G).source = b ≫ (groupoidPresheafObject G).target)
    (ha : a ≫ G.arrowsToBase.hom = pT) :
    (groupoidPresheafObject G).liftPair a b w ≫ pairsToBase G = pT :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ G.arrowsToBase.hom)
      (Deformation.GroupoidObject.liftPair_fst _ a b w)).trans ha)

end Pairs

section Descent

variable (G : GroupoidInAlgebraicSpaces B S hS D.limitSpace)

/-- **The limit descriptions of a groupoid over a Noetherian limit.** Diagrams as in Stacks 0CP8
for the spaces of objects, arrows, composable pairs and composable triples of a groupoid
`(U, R, s, t, c)` in algebraic spaces over `Y = lim Y_i`, and morphisms of their inverse systems
of scheme-theoretic images (Stacks 0CPA) on a common tail inducing the structure morphisms of the
groupoid: source, target, identity, inverse, composition, the two projections of a composable
pair, the four composable pairs of the unit and inverse laws, the two bracketings of a composable
triple and its two projections. -/
structure PreDescent where
  /-- A diagram for the object space `U`. -/
  objects : GoodDiagram B S hS hZ D G.objectsToBase.hom
  /-- A diagram for the arrow space `R`. -/
  arrows : GoodDiagram B S hS hZ D G.arrowsToBase.hom
  /-- A diagram for the space `R ×_{s, U, t} R` of composable pairs. -/
  pairs : GoodDiagram B S hS hZ D (pairsToBase G)
  /-- A diagram for the space of composable triples. -/
  triples : GoodDiagram B S hS hZ D (triplesToBase G)
  /-- The common tail of the morphisms of systems. -/
  index : I
  le_objects : objects.index ≤ index
  le_arrows : arrows.index ≤ index
  le_pairs : pairs.index ≤ index
  le_triples : triples.index ≤ index
  /-- The source maps `s_i : R_i ⟶ U_i`. -/
  source : SystemMorphism arrows objects (groupoidPresheafObject G).source index le_arrows
    le_objects
  /-- The target maps `t_i : R_i ⟶ U_i`. -/
  target : SystemMorphism arrows objects (groupoidPresheafObject G).target index le_arrows
    le_objects
  /-- The identities `e_i : U_i ⟶ R_i`. -/
  identity : SystemMorphism objects arrows (groupoidPresheafObject G).identity index le_objects
    le_arrows
  /-- The inverses `i_i : R_i ⟶ R_i`. -/
  inverse : SystemMorphism arrows arrows (groupoidPresheafObject G).inverse index le_arrows
    le_arrows
  /-- The compositions `c_i : T_i ⟶ R_i`. -/
  comp : SystemMorphism pairs arrows (groupoidPresheafObject G).comp index le_pairs le_arrows
  /-- The first projections `p_i : T_i ⟶ R_i`. -/
  fst : SystemMorphism pairs arrows (groupoidPresheafObject G).fst index le_pairs le_arrows
  /-- The second projections `q_i : T_i ⟶ R_i`. -/
  snd : SystemMorphism pairs arrows (groupoidPresheafObject G).snd index le_pairs le_arrows
  /-- The pairs `(e(t(a)), a)`. -/
  unitLeft : SystemMorphism arrows pairs ((groupoidPresheafObject G).liftPair
    ((groupoidPresheafObject G).target ≫ (groupoidPresheafObject G).identity) (𝟙 _)
    (groupoidPresheafObject G).identity_target_comp_source) index le_arrows le_pairs
  /-- The pairs `(a, e(s(a)))`. -/
  unitRight : SystemMorphism arrows pairs ((groupoidPresheafObject G).liftPair (𝟙 _)
    ((groupoidPresheafObject G).source ≫ (groupoidPresheafObject G).identity)
    (groupoidPresheafObject G).identity_source_comp_target) index le_arrows le_pairs
  /-- The pairs `(a⁻¹, a)`. -/
  inverseLeft : SystemMorphism arrows pairs ((groupoidPresheafObject G).liftPair
    (groupoidPresheafObject G).inverse (𝟙 _) (groupoidPresheafObject G).inverse_comp_source)
    index le_arrows le_pairs
  /-- The pairs `(a, a⁻¹)`. -/
  inverseRight : SystemMorphism arrows pairs ((groupoidPresheafObject G).liftPair (𝟙 _)
    (groupoidPresheafObject G).inverse (groupoidPresheafObject G).inverse_comp_target)
    index le_arrows le_pairs
  /-- The first bracketing of a composable triple. -/
  assocLeft : SystemMorphism triples pairs (groupoidPresheafObject G).assocLeft index le_triples
    le_pairs
  /-- The second bracketing of a composable triple. -/
  assocRight : SystemMorphism triples pairs (groupoidPresheafObject G).assocRight index le_triples
    le_pairs
  /-- The first pair of a composable triple. -/
  fst₃ : SystemMorphism triples pairs (groupoidPresheafObject G).fst₃ index le_triples le_pairs
  /-- The second pair of a composable triple. -/
  snd₃ : SystemMorphism triples pairs (groupoidPresheafObject G).snd₃ index le_triples le_pairs

/-- **The descent of a groupoid over a Noetherian limit to every late stage.** Limit descriptions
of the groupoid (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.PreDescent`) whose morphisms of
systems satisfy, at every stage `i` of the tail, the laws of a groupoid object
`(U_i, R_i, s_i, t_i, c_i, e_i, i_i)` with `T_i = R_i ×_{s_i, U_i, t_i} R_i`, have smooth `s_i`
and `t_i` when the groupoid is smooth, and present `R` as `U ×_{U_i} R_i` along both `s` and
`t`. -/
structure LimitDescent extends PreDescent G where
  identity_source : ∀ (i : I) (h : index ≤ i), identity.maps.app (Over.mk (homOfLE h).op) ≫
    source.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  identity_target : ∀ (i : I) (h : index ≤ i), identity.maps.app (Over.mk (homOfLE h).op) ≫
    target.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  inverse_source : ∀ (i : I) (h : index ≤ i), inverse.maps.app (Over.mk (homOfLE h).op) ≫
    source.maps.app (Over.mk (homOfLE h).op) = target.maps.app (Over.mk (homOfLE h).op)
  inverse_target : ∀ (i : I) (h : index ≤ i), inverse.maps.app (Over.mk (homOfLE h).op) ≫
    target.maps.app (Over.mk (homOfLE h).op) = source.maps.app (Over.mk (homOfLE h).op)
  comp_source : ∀ (i : I) (h : index ≤ i), comp.maps.app (Over.mk (homOfLE h).op) ≫
    source.maps.app (Over.mk (homOfLE h).op) =
      snd.maps.app (Over.mk (homOfLE h).op) ≫ source.maps.app (Over.mk (homOfLE h).op)
  comp_target : ∀ (i : I) (h : index ≤ i), comp.maps.app (Over.mk (homOfLE h).op) ≫
    target.maps.app (Over.mk (homOfLE h).op) =
      fst.maps.app (Over.mk (homOfLE h).op) ≫ target.maps.app (Over.mk (homOfLE h).op)
  unitLeft_fst : ∀ (i : I) (h : index ≤ i), unitLeft.maps.app (Over.mk (homOfLE h).op) ≫
    fst.maps.app (Over.mk (homOfLE h).op) =
      target.maps.app (Over.mk (homOfLE h).op) ≫ identity.maps.app (Over.mk (homOfLE h).op)
  unitLeft_snd : ∀ (i : I) (h : index ≤ i), unitLeft.maps.app (Over.mk (homOfLE h).op) ≫
    snd.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  unitLeft_comp : ∀ (i : I) (h : index ≤ i), unitLeft.maps.app (Over.mk (homOfLE h).op) ≫
    comp.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  unitRight_fst : ∀ (i : I) (h : index ≤ i), unitRight.maps.app (Over.mk (homOfLE h).op) ≫
    fst.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  unitRight_snd : ∀ (i : I) (h : index ≤ i), unitRight.maps.app (Over.mk (homOfLE h).op) ≫
    snd.maps.app (Over.mk (homOfLE h).op) =
      source.maps.app (Over.mk (homOfLE h).op) ≫ identity.maps.app (Over.mk (homOfLE h).op)
  unitRight_comp : ∀ (i : I) (h : index ≤ i), unitRight.maps.app (Over.mk (homOfLE h).op) ≫
    comp.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  inverseLeft_fst : ∀ (i : I) (h : index ≤ i), inverseLeft.maps.app (Over.mk (homOfLE h).op) ≫
    fst.maps.app (Over.mk (homOfLE h).op) = inverse.maps.app (Over.mk (homOfLE h).op)
  inverseLeft_snd : ∀ (i : I) (h : index ≤ i), inverseLeft.maps.app (Over.mk (homOfLE h).op) ≫
    snd.maps.app (Over.mk (homOfLE h).op) = 𝟙 _
  inverseLeft_comp : ∀ (i : I) (h : index ≤ i), inverseLeft.maps.app (Over.mk (homOfLE h).op) ≫
    comp.maps.app (Over.mk (homOfLE h).op) =
      source.maps.app (Over.mk (homOfLE h).op) ≫ identity.maps.app (Over.mk (homOfLE h).op)
  inverseRight_fst : ∀ (i : I) (h : index ≤ i),
    inverseRight.maps.app (Over.mk (homOfLE h).op) ≫ fst.maps.app (Over.mk (homOfLE h).op) =
      𝟙 _
  inverseRight_snd : ∀ (i : I) (h : index ≤ i),
    inverseRight.maps.app (Over.mk (homOfLE h).op) ≫ snd.maps.app (Over.mk (homOfLE h).op) =
      inverse.maps.app (Over.mk (homOfLE h).op)
  inverseRight_comp : ∀ (i : I) (h : index ≤ i),
    inverseRight.maps.app (Over.mk (homOfLE h).op) ≫ comp.maps.app (Over.mk (homOfLE h).op) =
      target.maps.app (Over.mk (homOfLE h).op) ≫ identity.maps.app (Over.mk (homOfLE h).op)
  assocLeft_fst : ∀ (i : I) (h : index ≤ i), assocLeft.maps.app (Over.mk (homOfLE h).op) ≫
    fst.maps.app (Over.mk (homOfLE h).op) =
      fst₃.maps.app (Over.mk (homOfLE h).op) ≫ comp.maps.app (Over.mk (homOfLE h).op)
  assocLeft_snd : ∀ (i : I) (h : index ≤ i), assocLeft.maps.app (Over.mk (homOfLE h).op) ≫
    snd.maps.app (Over.mk (homOfLE h).op) =
      snd₃.maps.app (Over.mk (homOfLE h).op) ≫ snd.maps.app (Over.mk (homOfLE h).op)
  assocRight_fst : ∀ (i : I) (h : index ≤ i), assocRight.maps.app (Over.mk (homOfLE h).op) ≫
    fst.maps.app (Over.mk (homOfLE h).op) =
      fst₃.maps.app (Over.mk (homOfLE h).op) ≫ fst.maps.app (Over.mk (homOfLE h).op)
  assocRight_snd : ∀ (i : I) (h : index ≤ i), assocRight.maps.app (Over.mk (homOfLE h).op) ≫
    snd.maps.app (Over.mk (homOfLE h).op) =
      snd₃.maps.app (Over.mk (homOfLE h).op) ≫ comp.maps.app (Over.mk (homOfLE h).op)
  assoc : ∀ (i : I) (h : index ≤ i), assocLeft.maps.app (Over.mk (homOfLE h).op) ≫
    comp.maps.app (Over.mk (homOfLE h).op) =
      assocRight.maps.app (Over.mk (homOfLE h).op) ≫ comp.maps.app (Over.mk (homOfLE h).op)
  isPullback_pairs : ∀ (i : I) (h : index ≤ i),
    IsPullback (fst.maps.app (Over.mk (homOfLE h).op)) (snd.maps.app (Over.mk (homOfLE h).op))
      (source.maps.app (Over.mk (homOfLE h).op)) (target.maps.app (Over.mk (homOfLE h).op))
  isPullback_triples : ∀ (i : I) (h : index ≤ i),
    IsPullback (fst₃.maps.app (Over.mk (homOfLE h).op))
      (snd₃.maps.app (Over.mk (homOfLE h).op))
      (snd.maps.app (Over.mk (homOfLE h).op)) (fst.maps.app (Over.mk (homOfLE h).op))
  source_isSmooth : ∀ (i : I) (h : index ≤ i),
    Space.IsSmooth B S hS (source.maps.app (Over.mk (homOfLE h).op))
  target_isSmooth : ∀ (i : I) (h : index ≤ i),
    Space.IsSmooth B S hS (target.maps.app (Over.mk (homOfLE h).op))
  source_isPullback : ∀ (i : I) (h : index ≤ i),
    IsPullback ((imageCone arrows).π.app ((Over.map (homOfLE le_arrows).op).obj
        (Over.mk (homOfLE h).op))) G.source.hom (source.maps.app (Over.mk (homOfLE h).op))
      ((imageCone objects).π.app ((Over.map (homOfLE le_objects).op).obj
        (Over.mk (homOfLE h).op)))
  target_isPullback : ∀ (i : I) (h : index ≤ i),
    IsPullback ((imageCone arrows).π.app ((Over.map (homOfLE le_arrows).op).obj
        (Over.mk (homOfLE h).op))) G.target.hom (target.maps.app (Over.mk (homOfLE h).op))
      ((imageCone objects).π.app ((Over.map (homOfLE le_objects).op).obj
        (Over.mk (homOfLE h).op)))

variable {G}

/-- A map `a : R ⟶ U` over the base is quasi-separated and quasi-compact when `U` and `R` are
quasi-separated over the base and `R` is of finite type. -/
private theorem isQuasiSeparated_isQuasiCompact_of_comp_objectsToBase
    {a : G.arrows.obj ⟶ G.objects.obj} (ha : a ≫ G.objectsToBase.hom = G.arrowsToBase.hom)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom) :
    Space.IsQuasiSeparated B S hS a ∧ Space.IsQuasiCompact B S hS a :=
  ⟨isQuasiSeparated_of_comp B S hS _ G.objectsToBase.hom (ha ▸ hRqs),
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ G.objectsToBase.hom G.arrows.property
      D.limitSpace.property (ha ▸ hRft.2) hUqs⟩

/-- The first projection `R ×_{s, U, t} R ⟶ R` of a smooth groupoid whose arrow space is
quasi-separated and of finite type over a base over which the object space is quasi-separated
is quasi-separated and of finite type, being a base change of the target map. -/
theorem fst_isQuasiSeparated_isFiniteType (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom) :
    Space.IsQuasiSeparated B S hS (groupoidPresheafObject G).fst ∧
      Space.IsFiniteType B S hS (groupoidPresheafObject G).fst := by
  obtain ⟨htqs, htqc⟩ := isQuasiSeparated_isQuasiCompact_of_comp_objectsToBase
    (target_comp_objectsToBase G) hUqs hRqs hRft
  have htlft : Space.IsLocallyOfFiniteType B S hS G.target.hom :=
    isLocallyOfFiniteType_of_isSmooth B S hS hG.2
  have sq := (groupoidPresheafObject G).isPullback_pairs
  have sq' := (groupoidObject G).isPullback_pairs
  refine ⟨isQuasiSeparated_of_isPullback B S hS sq.flip htqs, ?_, ?_⟩
  · exact (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq'.flip htlft
  · exact isQuasiCompact_of_isPullback B S hS sq.flip htqc

/-- The spaces of composable pairs and triples of such a groupoid are quasi-separated over the
base. -/
theorem pairs_triples_isQuasiSeparated (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom) :
    Space.IsQuasiSeparated B S hS (pairsToBase G) ∧
      Space.IsQuasiSeparated B S hS (triplesToBase G) := by
  have hfst := (fst_isQuasiSeparated_isFiniteType hG hUqs hRqs hRft).1
  have hP : Space.IsQuasiSeparated B S hS (pairsToBase G) :=
    isQuasiSeparated_comp B S hS (isAlgebraicSpace_pairs G) G.arrows.property _ _ hfst hRqs
  refine ⟨hP, isQuasiSeparated_comp B S hS (isAlgebraicSpace_triples G)
    (isAlgebraicSpace_pairs G) _ _ ?_ hP⟩
  exact isQuasiSeparated_of_isPullback B S hS
    (groupoidPresheafObject G).isPullback_triples.flip hfst

/-- The spaces of composable pairs and triples of such a groupoid are of finite type over the
base. -/
theorem pairs_triples_isFiniteType (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom) :
    Space.IsFiniteType B S hS (pairsToBase G) ∧
      Space.IsFiniteType B S hS (triplesToBase G) := by
  obtain ⟨-, hfst⟩ := fst_isQuasiSeparated_isFiniteType hG hUqs hRqs hRft
  have hP : Space.IsFiniteType B S hS (pairsToBase G) :=
    isFiniteType_comp B S hS (isAlgebraicSpace_pairs G) G.arrows.property
      D.limitSpace.property _ _ hfst hRft
  refine ⟨hP, isFiniteType_comp B S hS (isAlgebraicSpace_triples G) (isAlgebraicSpace_pairs G)
    D.limitSpace.property _ _ ⟨?_, ?_⟩ hP⟩
  · exact (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (groupoidObject G).isPullback_triples.flip hfst.1
  · exact isQuasiCompact_of_isPullback B S hS
      (groupoidPresheafObject G).isPullback_triples.flip hfst.2

/-- **Limit descriptions of a groupoid exist** for any diagrams of its four spaces: the morphisms
of systems are those of Stacks 0CPA, on a common tail. -/
theorem PreDescent.nonempty (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom)
    (GU : GoodDiagram B S hS hZ D G.objectsToBase.hom)
    (GR : GoodDiagram B S hS hZ D G.arrowsToBase.hom)
    (GP : GoodDiagram B S hS hZ D (pairsToBase G))
    (GT : GoodDiagram B S hS hZ D (triplesToBase G)) : Nonempty (PreDescent G) := by
  obtain ⟨hPqs, hTqs⟩ := pairs_triples_isQuasiSeparated hG hUqs hRqs hRft
  have hU := G.objects.property
  have hR := G.arrows.property
  have hP := isAlgebraicSpace_pairs G
  have hT := isAlgebraicSpace_triples G
  have e1 := SystemMorphism.eventually_nonempty hR hRqs (source_comp_objectsToBase G) GR GU
  have e2 := SystemMorphism.eventually_nonempty hR hRqs (target_comp_objectsToBase G) GR GU
  have e3 := SystemMorphism.eventually_nonempty hU hUqs (identity_comp_arrowsToBase G) GU GR
  have e4 := SystemMorphism.eventually_nonempty hR hRqs (inverse_comp_arrowsToBase G) GR GR
  have e5 := SystemMorphism.eventually_nonempty hP hPqs (comp_comp_arrowsToBase G) GP GR
  have e6 := SystemMorphism.eventually_nonempty (f := (groupoidPresheafObject G).fst) hP hPqs
    rfl GP GR
  have e7 := SystemMorphism.eventually_nonempty hP hPqs (snd_comp_arrowsToBase G) GP GR
  have e8 := SystemMorphism.eventually_nonempty hR hRqs (liftPair_comp_pairsToBase G
    (groupoidPresheafObject G).identity_target_comp_source
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (identity_comp_arrowsToBase G)).trans
      (target_comp_objectsToBase G)))) GR GP
  have e9 := SystemMorphism.eventually_nonempty hR hRqs (liftPair_comp_pairsToBase G
    (groupoidPresheafObject G).identity_source_comp_target (Category.id_comp _)) GR GP
  have e10 := SystemMorphism.eventually_nonempty hR hRqs (liftPair_comp_pairsToBase G
    (groupoidPresheafObject G).inverse_comp_source (inverse_comp_arrowsToBase G)) GR GP
  have e11 := SystemMorphism.eventually_nonempty hR hRqs (liftPair_comp_pairsToBase G
    (groupoidPresheafObject G).inverse_comp_target (Category.id_comp _)) GR GP
  have e12 := SystemMorphism.eventually_nonempty (f := (groupoidPresheafObject G).assocLeft) hT
    hTqs (liftPair_comp_pairsToBase G _
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (comp_comp_arrowsToBase G)))) GT GP
  have e13 := SystemMorphism.eventually_nonempty (f := (groupoidPresheafObject G).assocRight) hT
    hTqs (liftPair_comp_pairsToBase G _ (Category.assoc _ _ _)) GT GP
  have e14 := SystemMorphism.eventually_nonempty (f := (groupoidPresheafObject G).fst₃) hT hTqs
    rfl GT GP
  have e15 := SystemMorphism.eventually_nonempty hT hTqs (snd₃_comp_pairsToBase G) GT GP
  have key : ∀ᶠ n : I in Filter.atTop, Nonempty (PreDescent G) := by
    filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
      with n ⟨hRn, hUn, ⟨F1⟩⟩ ⟨_, _, ⟨F2⟩⟩ ⟨_, _, ⟨F3⟩⟩ ⟨_, _, ⟨F4⟩⟩ ⟨hPn, _, ⟨F5⟩⟩
        ⟨_, _, ⟨F6⟩⟩ ⟨_, _, ⟨F7⟩⟩ ⟨_, _, ⟨F8⟩⟩ ⟨_, _, ⟨F9⟩⟩ ⟨_, _, ⟨F10⟩⟩ ⟨_, _, ⟨F11⟩⟩
        ⟨hTn, _, ⟨F12⟩⟩ ⟨_, _, ⟨F13⟩⟩ ⟨_, _, ⟨F14⟩⟩ ⟨_, _, ⟨F15⟩⟩
    exact ⟨{ objects := GU, arrows := GR, pairs := GP, triples := GT, index := n
             le_objects := hUn, le_arrows := hRn, le_pairs := hPn, le_triples := hTn
             source := F1, target := F2, identity := F3, inverse := F4, comp := F5, fst := F6
             snd := F7, unitLeft := F8, unitRight := F9, inverseLeft := F10
             inverseRight := F11, assocLeft := F12, assocRight := F13, fst₃ := F14
             snd₃ := F15 }⟩
  exact key.exists.elim fun _ h => h

/-- The source map of such a groupoid, and the second projection of its composable pairs, are
flat and of finite presentation; the latter is a base change of the former. -/
theorem source_snd_isFlat_isFinitePresentation (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom) :
    (Space.IsFlat B S hS G.source.hom ∧ Space.IsFinitePresentation B S hS G.source.hom) ∧
      (Space.IsFlat B S hS (groupoidPresheafObject G).snd ∧
        Space.IsFinitePresentation B S hS (groupoidPresheafObject G).snd) := by
  obtain ⟨hsqs, hsqc⟩ := isQuasiSeparated_isQuasiCompact_of_comp_objectsToBase
    (source_comp_objectsToBase G) hUqs hRqs hRft
  have hslfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom :=
    isLocallyOfFinitePresentation_of_isSmooth B S hS hG.1
  have hsfl : Space.IsFlat B S hS G.source.hom := isFlat_of_isSmooth B S hS _ hG.1
  have sq := (groupoidPresheafObject G).isPullback_pairs
  have sq' := (groupoidObject G).isPullback_pairs
  refine ⟨⟨hsfl, hslfp, hsqc, hsqs⟩, ?_, ?_, ?_, ?_⟩
  · exact (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq' hsfl
  · exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq' hslfp
  · exact isQuasiCompact_of_isPullback B S hS sq hsqc
  · exact isQuasiSeparated_of_isPullback B S hS sq hsqs

/-- **The groupoid laws hold at every late stage**, with no bound on the size of the index set.
The laws are equations between composites of morphisms of image systems which hold in
the limit, so they hold eventually by the uniqueness of Stacks 0CPA; the source and target maps
are smooth at late stages by Stacks 0CPD and present `R` as `U ×_{U_i} R_i` by Stacks 0CPC; and
`T_i = R_i ×_{s_i, U_i, t_i} R_i` at late stages, as well as the analogous statement for
triples, by Stacks 0CPF. -/
theorem LimitDescent.nonempty (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom) (P : PreDescent G) :
    Nonempty (LimitDescent G) := by
  classical
  obtain ⟨hPqs, hTqs⟩ := pairs_triples_isQuasiSeparated hG hUqs hRqs hRft
  obtain ⟨⟨hsfl, hsfp⟩, hqfl, hqfp⟩ := source_snd_isFlat_isFinitePresentation hG hUqs hRqs hRft
  have htfl : Space.IsFlat B S hS G.target.hom := isFlat_of_isSmooth B S hS _ hG.2
  obtain ⟨htqs, htqc⟩ := isQuasiSeparated_isQuasiCompact_of_comp_objectsToBase
    (target_comp_objectsToBase G) hUqs hRqs hRft
  have htfp : Space.IsFinitePresentation B S hS G.target.hom :=
    ⟨isLocallyOfFinitePresentation_of_isSmooth B S hS hG.2, htqc, htqs⟩
  have hU := G.objects.property
  have hR := G.arrows.property
  have hP := isAlgebraicSpace_pairs G
  have hT := isAlgebraicSpace_triples G
  let Γ := groupoidPresheafObject G
  -- the laws, from the uniqueness of Stacks 0CPA
  have l1 := SystemMorphism.eventually_comp_eq_id hU hUqs Γ.identity_source P.identity P.source
  have l2 := SystemMorphism.eventually_comp_eq_id hU hUqs Γ.identity_target P.identity P.target
  have l3 := SystemMorphism.eventually_comp_eq hR hRqs Γ.inverse_source P.inverse P.source
    P.target
  have l4 := SystemMorphism.eventually_comp_eq hR hRqs Γ.inverse_target P.inverse P.target
    P.source
  have l5 := SystemMorphism.eventually_comp_eq_comp hP hPqs Γ.comp_source P.comp P.source
    P.snd P.source
  have l6 := SystemMorphism.eventually_comp_eq_comp hP hPqs Γ.comp_target P.comp P.target
    P.fst P.target
  have l7 := SystemMorphism.eventually_comp_eq_comp hR hRqs (Γ.liftPair_fst _ _ _) P.unitLeft
    P.fst P.target P.identity
  have l8 := SystemMorphism.eventually_comp_eq_id hR hRqs (Γ.liftPair_snd _ _ _) P.unitLeft P.snd
  have l9 := SystemMorphism.eventually_comp_eq_id hR hRqs Γ.compUnitLeft_comp P.unitLeft P.comp
  have l10 := SystemMorphism.eventually_comp_eq_id hR hRqs (Γ.liftPair_fst _ _ _) P.unitRight
    P.fst
  have l11 := SystemMorphism.eventually_comp_eq_comp hR hRqs (Γ.liftPair_snd _ _ _) P.unitRight
    P.snd P.source P.identity
  have l12 := SystemMorphism.eventually_comp_eq_id hR hRqs Γ.compUnitRight_comp P.unitRight
    P.comp
  have l13 := SystemMorphism.eventually_comp_eq hR hRqs (Γ.liftPair_fst _ _ _) P.inverseLeft
    P.fst P.inverse
  have l14 := SystemMorphism.eventually_comp_eq_id hR hRqs (Γ.liftPair_snd _ _ _) P.inverseLeft
    P.snd
  have l15 := SystemMorphism.eventually_comp_eq_comp hR hRqs Γ.compInverseLeft_comp
    P.inverseLeft P.comp P.source P.identity
  have l16 := SystemMorphism.eventually_comp_eq_id hR hRqs (Γ.liftPair_fst _ _ _) P.inverseRight
    P.fst
  have l17 := SystemMorphism.eventually_comp_eq hR hRqs (Γ.liftPair_snd _ _ _) P.inverseRight
    P.snd P.inverse
  have l18 := SystemMorphism.eventually_comp_eq_comp hR hRqs Γ.compInverseRight_comp
    P.inverseRight P.comp P.target P.identity
  have l19 := SystemMorphism.eventually_comp_eq_comp hT hTqs Γ.assocLeft_fst P.assocLeft P.fst
    P.fst₃ P.comp
  have l20 := SystemMorphism.eventually_comp_eq_comp hT hTqs Γ.assocLeft_snd P.assocLeft P.snd
    P.snd₃ P.snd
  have l21 := SystemMorphism.eventually_comp_eq_comp hT hTqs Γ.assocRight_fst P.assocRight P.fst
    P.fst₃ P.fst
  have l22 := SystemMorphism.eventually_comp_eq_comp hT hTqs Γ.assocRight_snd P.assocRight
    P.snd P.snd₃ P.comp
  have l23 := SystemMorphism.eventually_comp_eq_comp hT hTqs Γ.assocLeft_comp P.assocLeft
    P.comp P.assocRight P.comp
  -- smoothness, from Stacks 0CPD
  have smooth_tail : ∀ {f} (F : SystemMorphism P.arrows P.objects f P.index P.le_arrows
      P.le_objects), Space.IsSmooth B S hS f → ∀ᶠ i in Filter.atTop, ∀ h : P.index ≤ i,
        Space.IsSmooth B S hS (F.maps.app (Over.mk (homOfLE h).op)) := fun F hF => by
    obtain ⟨i₃, -, hi₃⟩ :=
      SystemMorphism.exists_isSmooth_of_algebraicLimit hR hU hRqs hUqs F hF
    exact Filter.eventually_atTop.2 ⟨i₃, fun i hi _ => hi₃ _ hi⟩
  have s1 := smooth_tail P.source hG.1
  have s2 := smooth_tail P.target hG.2
  -- `R = U ×_{U_i} R_i` along `s` and along `t`, from Stacks 0CPC
  have pullback_tail : ∀ {f} (F : SystemMorphism P.arrows P.objects f P.index P.le_arrows
      P.le_objects), Space.IsFlat B S hS f → Space.IsFinitePresentation B S hS f →
        ∀ᶠ i in Filter.atTop, ∀ h : P.index ≤ i,
          IsPullback ((imageCone P.arrows).π.app ((Over.map (homOfLE P.le_arrows).op).obj
              (Over.mk (homOfLE h).op))) f (F.maps.app (Over.mk (homOfLE h).op))
            ((imageCone P.objects).π.app ((Over.map (homOfLE P.le_objects).op).obj
              (Over.mk (homOfLE h).op))) := fun F hfl hfp => by
    obtain ⟨i₃, -, hi₃⟩ :=
      SystemMorphism.exists_isFlat_isPullback_of_algebraicLimit hR hU hRqs hUqs F hfl hfp
    exact Filter.eventually_atTop.2 ⟨i₃, fun i hi _ => (hi₃ _ hi).2.1⟩
  have c1 := pullback_tail P.source hsfl hsfp
  have c2 := pullback_tail P.target htfl htfp
  -- the stage squares of pairs and triples are cartesian, from Stacks 0CPF
  have pb1 : ∀ᶠ i in Filter.atTop, ∀ h : P.index ≤ i,
      IsPullback (P.fst.maps.app (Over.mk (homOfLE h).op)) (P.snd.maps.app (Over.mk (homOfLE h).op))
        (P.source.maps.app (Over.mk (homOfLE h).op))
        (P.target.maps.app (Over.mk (homOfLE h).op)) := by
    obtain ⟨i₉, le₅, le₆, le₇, le₈, comm, -, hiso⟩ :=
      exists_isClosedImmersion_lift_and_isIso_of_algebraicLimit hP hR hR hU hPqs hRqs hUqs
        Γ.isPullback_pairs (source_comp_objectsToBase G) (target_comp_objectsToBase G)
        (snd_comp_arrowsToBase G) P.source P.target P.fst P.snd
    obtain ⟨i₁₀, le₁₀, h10⟩ := hiso hsfl hsfp
    refine Filter.eventually_atTop.2 ⟨i₁₀, fun i hi _ => ?_⟩
    have := h10 i hi
    exact (IsPullback.of_iso_pullback ⟨(comm i (le₁₀.trans hi)).symm⟩
      (asIso (pullback.lift _ _ (comm i (le₁₀.trans hi)).symm))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).flip
  have pb2 : ∀ᶠ i in Filter.atTop, ∀ h : P.index ≤ i,
      IsPullback (P.fst₃.maps.app (Over.mk (homOfLE h).op))
        (P.snd₃.maps.app (Over.mk (homOfLE h).op))
        (P.snd.maps.app (Over.mk (homOfLE h).op)) (P.fst.maps.app (Over.mk (homOfLE h).op)) := by
    obtain ⟨i₉, le₅, le₆, le₇, le₈, comm, -, hiso⟩ :=
      exists_isClosedImmersion_lift_and_isIso_of_algebraicLimit hT hP hP hR hTqs hPqs hRqs
        Γ.isPullback_triples (snd_comp_arrowsToBase G) rfl (snd₃_comp_pairsToBase G)
        P.snd P.fst P.fst₃ P.snd₃
    obtain ⟨i₁₀, le₁₀, h10⟩ := hiso hqfl hqfp
    refine Filter.eventually_atTop.2 ⟨i₁₀, fun i hi _ => ?_⟩
    have := h10 i hi
    exact (IsPullback.of_iso_pullback ⟨(comm i (le₁₀.trans hi)).symm⟩
      (asIso (pullback.lift _ _ (comm i (le₁₀.trans hi)).symm))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).flip
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1
    (l1.and (l2.and (l3.and (l4.and (l5.and (l6.and (l7.and (l8.and (l9.and (l10.and (l11.and
      (l12.and (l13.and (l14.and (l15.and (l16.and (l17.and (l18.and (l19.and (l20.and (l21.and
      (l22.and (l23.and (pb1.and (pb2.and (s1.and (s2.and (c1.and (c2.and
      (Filter.eventually_ge_atTop P.index))))))))))))))))))))))))))))))
  have ge : ∀ i, n ≤ i → P.index ≤ i := fun i h =>
    (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hle : P.index ≤ n := ge n le_rfl
  exact ⟨{ objects := P.objects, arrows := P.arrows, pairs := P.pairs, triples := P.triples
           index := n
           le_objects := P.le_objects.trans hle, le_arrows := P.le_arrows.trans hle
           le_pairs := P.le_pairs.trans hle, le_triples := P.le_triples.trans hle
           source := P.source.restrict hle, target := P.target.restrict hle
           identity := P.identity.restrict hle, inverse := P.inverse.restrict hle
           comp := P.comp.restrict hle, fst := P.fst.restrict hle, snd := P.snd.restrict hle
           unitLeft := P.unitLeft.restrict hle, unitRight := P.unitRight.restrict hle
           inverseLeft := P.inverseLeft.restrict hle, inverseRight := P.inverseRight.restrict hle
           assocLeft := P.assocLeft.restrict hle, assocRight := P.assocRight.restrict hle
           fst₃ := P.fst₃.restrict hle, snd₃ := P.snd₃.restrict hle
           identity_source := fun i h => (hn i h).1 (ge i h) (ge i h)
           identity_target := fun i h => (hn i h).2.1 (ge i h) (ge i h)
           inverse_source := fun i h => (hn i h).2.2.1 (ge i h) (ge i h) (ge i h)
           inverse_target := fun i h => (hn i h).2.2.2.1 (ge i h) (ge i h) (ge i h)
           comp_source := fun i h => (hn i h).2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           comp_target := fun i h => (hn i h).2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           unitLeft_fst := fun i h => (hn i h).2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           unitLeft_snd := fun i h => (hn i h).2.2.2.2.2.2.2.1 (ge i h) (ge i h)
           unitLeft_comp := fun i h => (hn i h).2.2.2.2.2.2.2.2.1 (ge i h) (ge i h)
           unitRight_fst := fun i h => (hn i h).2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h)
           unitRight_snd := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           unitRight_comp := fun i h => (hn i h).2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h)
           inverseLeft_fst := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h)
           inverseLeft_snd := fun i h => (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h)
           inverseLeft_comp := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           inverseRight_fst := fun i h => (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h)
           inverseRight_snd := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h)
           inverseRight_comp := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           assocLeft_fst := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           assocLeft_snd := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           assocRight_fst := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h) (ge i h)
           assocRight_snd := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h)
               (ge i h)
           assoc := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h) (ge i h) (ge i h)
               (ge i h)
           isPullback_pairs := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h)
           isPullback_triples := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h)
           source_isSmooth := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h)
           target_isSmooth := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h)
           source_isPullback := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h)
           target_isPullback := fun i h =>
             (hn i h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (ge i h)}⟩

namespace LimitDescent

variable (Δ : LimitDescent G) (i : I) (h : Δ.index ≤ i)

/-- The member `X_i` of the image system of a diagram, as an object over the stage `Y_i`. -/
noncomputable abbrev stageOver {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    (GX : GoodDiagram B S hS hZ D pX) (le : GX.index ≤ Δ.index) : Over (D.system.obj (op i)) :=
  Over.mk ((stageImage GX ((Over.map (homOfLE le).op).obj (Over.mk (homOfLE h).op))).ι ≫
    pullback.fst _ _)

/-- The component `f_i` of a morphism of image systems on the tail of `Δ`, as a morphism over the
stage `Y_i`. -/
noncomputable abbrev stageHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
    {pY : Y ⟶ D.limitCone.pt} {GX : GoodDiagram B S hS hZ D pX}
    {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y} {leX : GX.index ≤ Δ.index}
    {leY : GY.index ≤ Δ.index} (F : SystemMorphism GX GY f Δ.index leX leY) :
    stageOver Δ i h GX leX ⟶ stageOver Δ i h GY leY :=
  Over.homMk (F.maps.app (Over.mk (homOfLE h).op)) (F.over_base _)

/-- **The groupoid object `(U_i, R_i, s_i, t_i, c_i, e_i, i_i)` of the slice over `Y_i`.** -/
noncomputable def stageGroupoidObject :
    Deformation.GroupoidObject (Over (D.system.obj (op i))) :=
  Deformation.GroupoidObject.ofUniversalLaws
    (stageOver Δ i h Δ.objects Δ.le_objects) (stageOver Δ i h Δ.arrows Δ.le_arrows)
    (stageOver Δ i h Δ.pairs Δ.le_pairs) (stageOver Δ i h Δ.triples Δ.le_triples)
    (stageHom Δ i h Δ.source) (stageHom Δ i h Δ.target) (stageHom Δ i h Δ.identity)
    (stageHom Δ i h Δ.inverse) (stageHom Δ i h Δ.fst) (stageHom Δ i h Δ.snd)
    (IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (Δ.isPullback_pairs i h).w)
      (Δ.isPullback_pairs i h))
    (stageHom Δ i h Δ.comp) (stageHom Δ i h Δ.fst₃) (stageHom Δ i h Δ.snd₃)
    (IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (Δ.isPullback_triples i h).w)
      (Δ.isPullback_triples i h))
    (Over.OverMorphism.ext (Δ.identity_source i h)) (Over.OverMorphism.ext (Δ.identity_target i h))
    (Over.OverMorphism.ext (Δ.inverse_source i h)) (Over.OverMorphism.ext (Δ.inverse_target i h))
    (Over.OverMorphism.ext (Δ.comp_source i h)) (Over.OverMorphism.ext (Δ.comp_target i h))
    (stageHom Δ i h Δ.unitLeft) (Over.OverMorphism.ext (Δ.unitLeft_fst i h))
    (Over.OverMorphism.ext (Δ.unitLeft_snd i h)) (Over.OverMorphism.ext (Δ.unitLeft_comp i h))
    (stageHom Δ i h Δ.unitRight) (Over.OverMorphism.ext (Δ.unitRight_fst i h))
    (Over.OverMorphism.ext (Δ.unitRight_snd i h)) (Over.OverMorphism.ext (Δ.unitRight_comp i h))
    (stageHom Δ i h Δ.inverseLeft) (Over.OverMorphism.ext (Δ.inverseLeft_fst i h))
    (Over.OverMorphism.ext (Δ.inverseLeft_snd i h))
    (Over.OverMorphism.ext (Δ.inverseLeft_comp i h))
    (stageHom Δ i h Δ.inverseRight) (Over.OverMorphism.ext (Δ.inverseRight_fst i h))
    (Over.OverMorphism.ext (Δ.inverseRight_snd i h))
    (Over.OverMorphism.ext (Δ.inverseRight_comp i h))
    (stageHom Δ i h Δ.assocLeft) (stageHom Δ i h Δ.assocRight)
    (Over.OverMorphism.ext (Δ.assocLeft_fst i h)) (Over.OverMorphism.ext (Δ.assocLeft_snd i h))
    (Over.OverMorphism.ext (Δ.assocRight_fst i h)) (Over.OverMorphism.ext (Δ.assocRight_snd i h))
    (Over.OverMorphism.ext (Δ.assoc i h))

/-- **The groupoid `(U_i, R_i, s_i, t_i, c_i)` in algebraic spaces over the stage `Y_i`.** -/
noncomputable def stageGroupoid : GroupoidInAlgebraicSpaces B S hS (D.stageSpace i) :=
  ofOverGroupoidObject (D.stageSpace i) (Δ.stageGroupoidObject i h)
    (imageSystem_isAlgebraicSpace Δ.objects _) (imageSystem_isAlgebraicSpace Δ.arrows _)

/-- The object space of the stage groupoid is the member `U_i` of the image system of `U`. -/
theorem stageGroupoid_objects_obj :
    (Δ.stageGroupoid i h).objects.obj = (imageSystem Δ.objects).obj
      ((Over.map (homOfLE Δ.le_objects).op).obj (Over.mk (homOfLE h).op)) := rfl

/-- The arrow space of the stage groupoid is the member `R_i` of the image system of `R`. -/
theorem stageGroupoid_arrows_obj :
    (Δ.stageGroupoid i h).arrows.obj = (imageSystem Δ.arrows).obj
      ((Over.map (homOfLE Δ.le_arrows).op).obj (Over.mk (homOfLE h).op)) := rfl

/-- The source map `s_i` of the stage groupoid is the component of the image system of `s`. -/
theorem stageGroupoid_source_hom :
    (Δ.stageGroupoid i h).source.hom = Δ.source.maps.app (Over.mk (homOfLE h).op) := rfl

/-- The target map `t_i` of the stage groupoid is the component of the image system of `t`. -/
theorem stageGroupoid_target_hom :
    (Δ.stageGroupoid i h).target.hom = Δ.target.maps.app (Over.mk (homOfLE h).op) := rfl

/-- The stage groupoid is smooth when the source and target maps are, which they are at every
stage of the tail of `Δ`. -/
theorem stageGroupoid_isSmooth : IsSmooth B S hS (Δ.stageGroupoid i h) :=
  ⟨Δ.source_isSmooth i h, Δ.target_isSmooth i h⟩

/-- The structure morphism `U_i ⟶ Y_i` of the stage groupoid. -/
theorem stageGroupoid_objectsToBase_hom : (Δ.stageGroupoid i h).objectsToBase.hom =
    (stageImage Δ.objects ((Over.map (homOfLE Δ.le_objects).op).obj
      (Over.mk (homOfLE h).op))).ι ≫ pullback.fst _ _ := rfl

/-- **`U ⟶ Y ×_{Y_i} U_i` is a closed immersion**, by the construction of the image system of `U`
(Stacks 0CP9). -/
theorem isClosedImmersion_objects :
    Space.IsClosedImmersion B S hS (pullback.lift G.objectsToBase.hom
      ((imageCone Δ.objects).π.app ((Over.map (homOfLE Δ.le_objects).op).obj
        (Over.mk (homOfLE h).op)))
      (by rw [imageCone_π_ι_assoc, stageMap_fst]; rfl) :
        G.objects.obj ⟶ pullback (D.limitCone.π.app (op i))
          ((stageImage Δ.objects ((Over.map (homOfLE Δ.le_objects).op).obj
            (Over.mk (homOfLE h).op))).ι ≫ pullback.fst _ _)) :=
  isClosedImmersion_lift_imageCone_π Δ.objects (Δ.le_objects.trans h)

variable {Δ i h} in
/-- The object space `U_i` of the stage groupoid is of finite presentation over `Y_i`. -/
theorem stageGroupoid_objects_isFinitePresentation
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom) :
    Space.IsFinitePresentation B S hS (Δ.stageGroupoid i h).objectsToBase.hom :=
  isFinitePresentation_stageImage_ι_fst Δ.objects G.objects.property hUqs _

variable {Δ i h} in
/-- The arrow space `R_i` of the stage groupoid is of finite presentation over `Y_i`. -/
theorem stageGroupoid_arrows_isFinitePresentation
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom) :
    Space.IsFinitePresentation B S hS (Δ.stageGroupoid i h).arrowsToBase.hom :=
  isFinitePresentation_stageImage_ι_fst Δ.arrows G.arrows.property hRqs _

/-! #### The morphism to the base change of the stage groupoid -/

/-- The base change `Y ×_{Y_i} (U_i, R_i, s_i, t_i, c_i)` of the stage groupoid to `Y`. -/
noncomputable abbrev baseChangeGroupoid : GroupoidInAlgebraicSpaces B S hS D.limitSpace :=
  (Space.baseChange (Δ.stageGroupoid i h) (D.limitProjection i)).groupoid

/-- The map `U ⟶ Y ×_{Y_i} U_i`. -/
noncomputable abbrev mapObjects : G.objects.obj ⟶ (Δ.baseChangeGroupoid i h).objects.obj :=
  pullback.lift (f := D.limitCone.π.app (op i))
    (g := (stageImage Δ.objects ((Over.map (homOfLE Δ.le_objects).op).obj
      (Over.mk (homOfLE h).op))).ι ≫ pullback.fst _ _) G.objectsToBase.hom
    ((imageCone Δ.objects).π.app ((Over.map (homOfLE Δ.le_objects).op).obj
      (Over.mk (homOfLE h).op)))
    ((imageCone_π_ι_assoc Δ.objects
      ((Over.map (homOfLE Δ.le_objects).op).obj (Over.mk (homOfLE h).op)) _).trans
      (stageMap_fst Δ.objects _)).symm

/-- The map `R ⟶ Y ×_{Y_i} R_i`. -/
noncomputable abbrev mapArrows : G.arrows.obj ⟶ (Δ.baseChangeGroupoid i h).arrows.obj :=
  pullback.lift (f := D.limitCone.π.app (op i))
    (g := (stageImage Δ.arrows ((Over.map (homOfLE Δ.le_arrows).op).obj
      (Over.mk (homOfLE h).op))).ι ≫ pullback.fst _ _) G.arrowsToBase.hom
    ((imageCone Δ.arrows).π.app ((Over.map (homOfLE Δ.le_arrows).op).obj
      (Over.mk (homOfLE h).op)))
    ((imageCone_π_ι_assoc Δ.arrows
      ((Over.map (homOfLE Δ.le_arrows).op).obj (Over.mk (homOfLE h).op)) _).trans
      (stageMap_fst Δ.arrows _)).symm

/-- The first component of `U ⟶ Y ×_{Y_i} U_i` is the structure morphism `U ⟶ Y`. -/
theorem mapObjects_fst : Δ.mapObjects i h ≫
    pullback.fst (D.limitProjection i).hom (Δ.stageGroupoid i h).objectsToBase.hom =
      G.objectsToBase.hom := pullback.lift_fst _ _ _

/-- The second component of `U ⟶ Y ×_{Y_i} U_i` is the projection `U ⟶ U_i`. -/
theorem mapObjects_snd : Δ.mapObjects i h ≫
    pullback.snd (D.limitProjection i).hom (Δ.stageGroupoid i h).objectsToBase.hom =
      (imageCone Δ.objects).π.app ((Over.map (homOfLE Δ.le_objects).op).obj
        (Over.mk (homOfLE h).op)) := pullback.lift_snd _ _ _

/-- The first component of `R ⟶ Y ×_{Y_i} R_i` is the structure morphism `R ⟶ Y`. -/
theorem mapArrows_fst : Δ.mapArrows i h ≫
    pullback.fst (D.limitProjection i).hom (Δ.stageGroupoid i h).arrowsToBase.hom =
      G.arrowsToBase.hom := pullback.lift_fst _ _ _

/-- The second component of `R ⟶ Y ×_{Y_i} R_i` is the projection `R ⟶ R_i`. -/
theorem mapArrows_snd : Δ.mapArrows i h ≫
    pullback.snd (D.limitProjection i).hom (Δ.stageGroupoid i h).arrowsToBase.hom =
      (imageCone Δ.arrows).π.app ((Over.map (homOfLE Δ.le_arrows).op).obj
        (Over.mk (homOfLE h).op)) := pullback.lift_snd _ _ _

/-- The maps `mapArrows` and `mapObjects` commute with the source maps. -/
theorem mapArrows_source : Δ.mapArrows i h ≫ (Δ.baseChangeGroupoid i h).source.hom =
    G.source.hom ≫ Δ.mapObjects i h := by
  refine pullback.hom_ext ?_ ?_
  · exact ((Category.assoc _ _ _).trans ((congrArg (Δ.mapArrows i h ≫ ·)
      (Space.baseChange_source_comp_fst _ _)).trans (Δ.mapArrows_fst i h))).trans
      (((Category.assoc _ _ _).trans ((congrArg (G.source.hom ≫ ·) (Δ.mapObjects_fst i h)).trans
        (source_comp_objectsToBase G))).symm)
  · exact ((Category.assoc _ _ _).trans ((congrArg (Δ.mapArrows i h ≫ ·)
      (Space.baseChange_source_comp_snd _ _)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Δ.stageGroupoid i h).source.hom) (Δ.mapArrows_snd i h)).trans
          (Δ.source.induces (Over.mk (homOfLE h).op)))))).trans
      (((Category.assoc _ _ _).trans
        (congrArg (G.source.hom ≫ ·) (Δ.mapObjects_snd i h))).symm)

/-- The maps `mapArrows` and `mapObjects` commute with the target maps. -/
theorem mapArrows_target : Δ.mapArrows i h ≫ (Δ.baseChangeGroupoid i h).target.hom =
    G.target.hom ≫ Δ.mapObjects i h := by
  refine pullback.hom_ext ?_ ?_
  · exact ((Category.assoc _ _ _).trans ((congrArg (Δ.mapArrows i h ≫ ·)
      (Space.baseChange_target_comp_fst _ _)).trans (Δ.mapArrows_fst i h))).trans
      (((Category.assoc _ _ _).trans ((congrArg (G.target.hom ≫ ·) (Δ.mapObjects_fst i h)).trans
        (target_comp_objectsToBase G))).symm)
  · exact ((Category.assoc _ _ _).trans ((congrArg (Δ.mapArrows i h ≫ ·)
      (Space.baseChange_target_comp_snd _ _)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Δ.stageGroupoid i h).target.hom) (Δ.mapArrows_snd i h)).trans
          (Δ.target.induces (Over.mk (homOfLE h).op)))))).trans
      (((Category.assoc _ _ _).trans
        (congrArg (G.target.hom ≫ ·) (Δ.mapObjects_snd i h))).symm)

/-- The map on composable pairs. -/
noncomputable abbrev mapPairs := pullback.map G.source.hom G.target.hom
  (Δ.baseChangeGroupoid i h).source.hom (Δ.baseChangeGroupoid i h).target.hom
  (Δ.mapArrows i h) (Δ.mapArrows i h) (Δ.mapObjects i h) (Δ.mapArrows_source i h).symm
  (Δ.mapArrows_target i h).symm

/-- On composable pairs, the map to the base change followed by the comparison with the
stage is the projection `R ×_U R ⟶ T_i` of the image system of the pairs. -/
theorem mapPairs_comparison : Δ.mapPairs i h ≫
    (Space.baseChangeComposableToOld (Δ.stageGroupoid i h) (D.limitProjection i)).hom ≫
      overPairsComparison (D.stageSpace i) (Δ.stageGroupoidObject i h) =
    (imageCone Δ.pairs).π.app ((Over.map (homOfLE Δ.le_pairs).op).obj
      (Over.mk (homOfLE h).op)) := by
  refine (overGroupoidPresheafObject (D.stageSpace i)
    (Δ.stageGroupoidObject i h)).isPullback_pairs.hom_ext ?_ ?_
  · have h₂ := Space.baseChangeComposableToOld_comp_fst (Δ.stageGroupoid i h)
      (D.limitProjection i)
    have h₃ := overPairsComparison_fst (D.stageSpace i) (Δ.stageGroupoidObject i h)
    have e₁ : Δ.mapPairs i h ≫ pullback.fst (Δ.baseChangeGroupoid i h).source.hom
        (Δ.baseChangeGroupoid i h).target.hom =
          pullback.fst G.source.hom G.target.hom ≫ Δ.mapArrows i h := pullback.lift_fst _ _ _
    refine ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)).trans
      (Δ.fst.induces (Over.mk (homOfLE h).op)).symm
    exact (congrArg (fun k => Δ.mapPairs i h ≫ (Space.baseChangeComposableToOld
        (Δ.stageGroupoid i h) (D.limitProjection i)).hom ≫ k) h₃).trans
      ((congrArg (Δ.mapPairs i h ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd _ _) e₁).trans ((Category.assoc _ _ _).trans
          (congrArg (pullback.fst _ _ ≫ ·) (Δ.mapArrows_snd i h))))))
  · have h₂ := Space.baseChangeComposableToOld_comp_snd (Δ.stageGroupoid i h)
      (D.limitProjection i)
    have h₃ := overPairsComparison_snd (D.stageSpace i) (Δ.stageGroupoidObject i h)
    have e₁ : Δ.mapPairs i h ≫ pullback.snd (Δ.baseChangeGroupoid i h).source.hom
        (Δ.baseChangeGroupoid i h).target.hom =
          pullback.snd G.source.hom G.target.hom ≫ Δ.mapArrows i h := pullback.lift_snd _ _ _
    refine ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)).trans
      (Δ.snd.induces (Over.mk (homOfLE h).op)).symm
    exact (congrArg (fun k => Δ.mapPairs i h ≫ (Space.baseChangeComposableToOld
        (Δ.stageGroupoid i h) (D.limitProjection i)).hom ≫ k) h₃).trans
      ((congrArg (Δ.mapPairs i h ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd _ _) e₁).trans ((Category.assoc _ _ _).trans
          (congrArg (pullback.snd _ _ ≫ ·) (Δ.mapArrows_snd i h))))))

/-- The maps `mapPairs` and `mapArrows` commute with the compositions. -/
theorem mapPairs_comp : Δ.mapPairs i h ≫ (Δ.baseChangeGroupoid i h).comp.hom =
    G.comp.hom ≫ Δ.mapArrows i h := by
  have e₁ : Δ.mapPairs i h ≫ pullback.fst (Δ.baseChangeGroupoid i h).source.hom
      (Δ.baseChangeGroupoid i h).target.hom =
        pullback.fst G.source.hom G.target.hom ≫ Δ.mapArrows i h := pullback.lift_fst _ _ _
  refine pullback.hom_ext ?_ ?_
  · exact ((Category.assoc _ _ _).trans
      (congrArg (Δ.mapPairs i h ≫ ·) (Space.baseChange_comp_comp_fst _ _))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst _ _) e₁).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (pullback.fst G.source.hom G.target.hom ≫ ·) (Δ.mapArrows_fst i h)).trans
            (((Category.assoc _ _ _).trans ((congrArg (G.comp.hom ≫ ·) (Δ.mapArrows_fst i h)).trans
              (congrArg (fun k => k.hom) G.comp_over))).symm)))))
  · exact ((Category.assoc _ _ _).trans
      (congrArg (Δ.mapPairs i h ≫ ·) (Space.baseChange_comp_comp_snd _ _))).trans
      (((congrArg (Δ.mapPairs i h ≫ ·) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ Δ.comp.maps.app (Over.mk (homOfLE h).op)) (Δ.mapPairs_comparison i h)).trans
          ((Δ.comp.induces (Over.mk (homOfLE h).op)).trans
            ((congrArg (G.comp.hom ≫ ·) (Δ.mapArrows_snd i h)).symm.trans
              (Category.assoc _ _ _).symm))))

/-- **The morphism of groupoids `(U, R, s, t, c) ⟶ Y ×_{Y_i} (U_i, R_i, s_i, t_i, c_i)`** over
`Y`, whose components are the projections of the image systems. -/
noncomputable def toBaseChangeHom : Hom G (Δ.baseChangeGroupoid i h) :=
  Hom.mkOfComp (Δ.mapObjects i h) (Δ.mapArrows i h) (Δ.mapArrows_source i h)
    (Δ.mapArrows_target i h) (Δ.mapPairs_comp i h) (Δ.mapObjects_fst i h) (Δ.mapArrows_fst i h)

/-- **The source square of that morphism is cartesian**: `R = U ×_{U'} R'` with
`U' = Y ×_{Y_i} U_i` and `R' = Y ×_{Y_i} R_i`, by `R = U ×_{U_i} R_i` (Stacks 0CPC). -/
theorem isPullback_mapArrows_source : IsPullback (Δ.mapArrows i h) G.source.hom
    (Δ.baseChangeGroupoid i h).source.hom (Δ.mapObjects i h) := by
  have hright := Space.isPullback_baseChange_source (Δ.stageGroupoid i h) (D.limitProjection i)
  refine IsPullback.of_right ?_ ((Δ.mapArrows_source i h)) hright
  rw [Δ.mapArrows_snd i h, Δ.mapObjects_snd i h]
  exact Δ.source_isPullback i h

end LimitDescent

/-- **The groupoid descent in the proof of Stacks 0CQ1**, granted the inputs of the staged Stacks
0CP7 (`h07SU`), with no bound on the size of the index set. In Situation
0CP6, a smooth groupoid `(U, R, s, t, c)` in algebraic spaces over `Y = lim Y_i` whose object and
arrow spaces are quasi-separated and of finite type over `Y` has limit descriptions whose
morphisms of systems form, at every stage of a tail, a smooth groupoid `(U_i, R_i, s_i, t_i, c_i)`
over `Y_i` with `R = U ×_{U_i} R_i` along `s` and along `t`
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.LimitDescent`). -/
theorem LimitDescent.nonempty_of_noetherianApproximation
    {D : NoetherianLimitSystem B S hS B.contains_terminal I}
    {G : GroupoidInAlgebraicSpaces B S hS D.limitSpace} (hG : IsSmooth B S hS G)
    (hUqs : Space.IsQuasiSeparated B S hS G.objectsToBase.hom)
    (hUft : Space.IsFiniteType B S hS G.objectsToBase.hom)
    (hRqs : Space.IsQuasiSeparated B S hS G.arrowsToBase.hom)
    (hRft : Space.IsFiniteType B S hS G.arrowsToBase.hom)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    Nonempty (LimitDescent G) := by
  obtain ⟨hPqs, hTqs⟩ := pairs_triples_isQuasiSeparated hG hUqs hRqs hRft
  obtain ⟨hPft, hTft⟩ := pairs_triples_isFiniteType hG hUqs hRqs hRft
  obtain ⟨GU⟩ := nonempty_goodDiagram_of_noetherianApproximation D _ G.objects.property hUqs
    hUft h07SU
  obtain ⟨GR⟩ := nonempty_goodDiagram_of_noetherianApproximation D _ G.arrows.property hRqs
    hRft h07SU
  obtain ⟨GP⟩ := nonempty_goodDiagram_of_noetherianApproximation D _ (isAlgebraicSpace_pairs G)
    hPqs hPft h07SU
  obtain ⟨GT⟩ := nonempty_goodDiagram_of_noetherianApproximation D _
    (isAlgebraicSpace_triples G) hTqs hTft h07SU
  obtain ⟨P⟩ := PreDescent.nonempty hG hUqs hRqs hRft GU GR GP GT
  exact LimitDescent.nonempty hG hUqs hRqs hRft P

end Descent

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
