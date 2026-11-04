module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOver
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOverTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectBaseChangeStableProof
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of relatively perfect objects of algebraic spaces

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S`, locally of finite
presentation, let `g : Y' ⟶ Y` be a morphism, `X' = Y' ×_Y X` and `g' : X' ⟶ X` the projection.
Stacks 0DKT says that `L(g')^*` carries `Y`-perfect objects of `D(𝒪_X)` to `Y'`-perfect objects
of `D(𝒪_{X'})`.

## Main results

* `AlgebraicGeometry.RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff`
  states that on a ringed site, the derived stalk of a restriction to a slice at a lifted point
  `Φ.over x` has Tor amplitude in `[a, b]` exactly when the derived stalk at `Φ` does.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback`:
  the stalk form of Stacks 0DKD (1) at one geometric point, with no boundedness assumption.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback`:
  **Stacks 0DKT**.

## Implementation notes

The source reduces to schemes. Here the two clauses are treated directly. Pseudo-coherence is
Stacks 08H4 for algebraic spaces. Locally finite Tor dimension over `f'⁻¹𝒪_{Y'}` is read at the
geometric points: on a slice `V'` of the small étale site of `X'` lying over a slice `V` of the
small étale site of `X` on which `E` has Tor amplitude in `[a, b]` over `f⁻¹𝒪_Y`, every lift of
a geometric point to `V'` maps to a lift of its image to `V`; the derived stalk of `E` there has
Tor amplitude in `[a, b]` (Stacks 0DJJ (1) on the slice, with Stacks 04H2 to pass to the stalk
on `X`), so the derived stalk of `L(g')^*E` at the point of `X'` does (Stacks 0DKD (1) at the
stalk, through the computation of the geometric stalk of a derived pullback by a K-flat
resolution, Stacks 0DKE), and Stacks 0DJJ (2) on the slice `V'` concludes. Such slices `V'`
cover every object of the small étale site of `X'`, by the base change of charts used for
Stacks 08H4. Tor independence of `X` and `Y'` over `Y` is flatness of `f`.

## References

* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0DKE](https://stacks.math.columbia.edu/tag/0DKE)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.TorAmplitude

universe u v w d

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-! ### Tor amplitude of a stalk at a lifted point -/

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, v, w}) [LocallySmall.{w} X.C]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
  sliceRestrictionPreservesFiniteLimits sliceRestrictionPreservesFiniteColimits

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Tor amplitude of a stalk at a lifted point.** For a point `Φ` of a ringed site, an object
`V` and `x ∈ Φ.fiber V`, the derived stalk of `E|_V` at the lifted point `Φ.over x` has Tor
amplitude in `[a, b]` over `(𝒪|_V)_{Φ.over x}` exactly when the derived stalk `E_Φ` has Tor
amplitude in `[a, b]` over `𝒪_Φ`: by Stacks 04H2 the first is the second with its scalars
restricted along a ring isomorphism. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff
    (Φ : X.J.Point.{w}) {V : X.C} (x : Φ.fiber.obj V)
    (E : RingedSite.DerivedModules X) (a b : ℤ) :
    HasTorAmplitudeCanonical (((Φ.over x).presheafFiber (A := CommRingCat.{w})).obj
        (X.over V).O.obj)
      ((Stacks.derivedModuleFiber (Φ.over x) (X.over V).O).obj
        ((derivedRestriction X V).obj E)) a b ↔
      HasTorAmplitudeCanonical ((Φ.presheafFiber (A := CommRingCat.{w})).obj X.O.obj)
        ((Stacks.derivedModuleFiber Φ X.O).obj E) a b := by
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let Fib := Stacks.sheafModuleFiberOfCommRing Φ X.O
  let Fib' := Stacks.sheafModuleFiberOfCommRing (Φ.over x) (X.over V).O
  let Res := SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) V
  let e₁ : (Stacks.derivedModuleFiber (Φ.over x) (X.over V).O).obj
        ((derivedRestriction X V).obj E) ≅
      DerivedCategory.Q.obj ((Fib'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Res.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (Stacks.derivedModuleFiber (Φ.over x) (X.over V).O).mapIso
        ((derivedRestriction X V).mapIso eK.symm ≪≫
          Res.mapDerivedCategoryFactors.app K) ≪≫
      Fib'.mapDerivedCategoryFactors.app _
  let e₂ : (Stacks.derivedModuleFiber Φ X.O).obj E ≅
      DerivedCategory.Q.obj ((Fib.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (Stacks.derivedModuleFiber Φ X.O).mapIso eK.symm ≪≫ Fib.mapDerivedCategoryFactors.app K
  have key := Stacks.hasTorAmplitudeCanonical_sheafModuleFiber_over_iff Φ x X.O K a b
  exact ((hasTorAmplitudeCanonical_iff_of_iso e₁ a b).trans
    (key.trans (hasTorAmplitudeCanonical_iff_of_iso e₂ a b).symm))

end AlgebraicGeometry.RingedSite

/-! ### Stacks 0DKD (1) at one geometric point -/

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Stalk

open AlgebraicGeometry.BaseChangeTorAmplitude (hasTorAmplitudeCanonical_of_iso)

variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)

include hpb in
/-- **Stacks 0DKD (1) at a geometric point.** In a cartesian square with `X` and `Y'` Tor
independent over `Y`, if the derived stalk of `E ∈ D(𝒪_X)` at `g'(x̄')`, read over
`(f⁻¹𝒪_Y)_{g'(x̄')}`, has Tor amplitude in `[a, b]`, then so does the derived stalk of
`L(g')^*E` at `x̄'`, read over `(f'⁻¹𝒪_{Y'})_{x̄'}`. No boundedness of `E` is assumed: `E` is
represented by a K-flat complex with flat terms and K-flat geometric stalks, which computes
`L(g')^*`. -/
theorem hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) (x' : GeometricPoint B S hS X'.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ)
    (hE : HasTorAmplitudeCanonical (relativeStalkRing f (geometricPointMap g'.hom x'))
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
      a b) :
    HasTorAmplitudeCanonical (relativeStalkRing f' x')
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).obj ((derivedScalarRestriction B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E))) a b := by
  let x := geometricPointMap g'.hom x'
  obtain ⟨P, s, hs, hP, hst⟩ :=
    exists_kFlat_resolution_kFlat_geometricStalks X (DerivedCategory.Q.objPreimage E)
  let eP : DerivedCategory.Q.obj P ≅ E :=
    @asIso _ _ _ _ (DerivedCategory.Q.map s)
        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs) ≪≫
      DerivedCategory.Q.objObjPreimageIso E
  have hx' := hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapIso
        ((derivedScalarRestriction B S hS f).mapIso eP.symm) ≪≫
      derivedRelativeStalkIso f x P ≪≫
      ((ModuleCat.restrictScalars (relativeStalkMap f x)).mapDerivedCategoryFactors.app
        (stalkComplex x P)).symm) a b hE
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g' _ hP
  let eL : (smallEtaleDerivedModulePullback B S hS g').obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
    (smallEtaleDerivedModulePullback B S hS g').mapIso
        ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
        ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  exact hasTorAmplitudeCanonical_of_iso
    (DerivedCategory.Q.mapIso
        (((ModuleCat.restrictScalars (relativeStalkMap f' x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (pullbackStalkComplexIso g' x' P)).symm ≪≫
      (derivedRelativeStalkIso f' x' _).symm ≪≫
      (Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).mapIso
        ((derivedScalarRestriction B S hS f').mapIso
          (eL.symm ≪≫ (smallEtaleDerivedModulePullback B S hS g').mapIso eP))) a b
    (hasTorAmplitudeCanonical_relativeStalk_pullback g' f' f g hpb htor x' P (hst x) a b hx')

end Stalk

/-! ### Stacks 0DKT -/

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

section BaseChange

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom)
  (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)

/-- The Tor clause of relative perfectness, read at the geometric points: every object of the
small étale site of `X` is covered by objects `V` over which the derived stalks of `E` at all
geometric points lifting to `V` have Tor amplitude in one interval `[a, b]` over `f⁻¹𝒪_Y`. -/
theorem exists_cover_hasTorAmplitudeCanonical_relativeStalk
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E)
    (U : (inverseImageRingedSite B S hS f).C) :
    ∃ R : Presieve U, Sieve.generate R ∈ (inverseImageRingedSite B S hS f).J U ∧
      ∀ ⦃V : (inverseImageRingedSite B S hS f).C⦄ (k : V ⟶ U), R k → ∃ a b : ℤ,
        ∀ (x : GeometricPoint B S hS X.1) (_ : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V),
          HasTorAmplitudeCanonical (relativeStalkRing f x)
            ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
              (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
            a b := by
  obtain ⟨R, hR, h⟩ := hE.2 U
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨a, b, hab⟩ := h k hk
  exact ⟨a, b, fun x p =>
    (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff
      (inverseImageRingedSite B S hS f) (etaleSitePoint B S hS X.1 x X.2) p _ a b).1
      (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
        _ _ a b hab ((etaleSitePoint B S hS X.1 x X.2).over p))⟩

variable {X' Y' : AlgebraicSpaces B S hS} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g)

/-- **Stacks 0DKT.** Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S`, locally of
finite presentation, let `g : Y' ⟶ Y` be a morphism, `X' = Y' ×_Y X` and `g' : X' ⟶ X` the
projection. If `K ∈ D(𝒪_X)` is `Y`-perfect, then `L(g')^*K` is `Y'`-perfect. -/
theorem isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hlfp)
      ((smallEtaleDerivedModulePullback B S hS g').obj K) := by
  refine ⟨isPseudoCoherent_smallEtaleDerivedModulePullback g' K hK.1, fun U' => ?_⟩
  let P : SmallEtale B S hS X.1 → Prop := fun W => ∃ a b : ℤ,
    ∀ (x : GeometricPoint B S hS X.1) (_ : (etaleSitePoint B S hS X.1 x X.2).fiber.obj W),
      HasTorAmplitudeCanonical (relativeStalkRing f x)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
          (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj K))
        a b
  let R : Presieve U' := fun V' _ => ∃ (W : SmallEtale B S hS X.1) (q : V'.1.left ⟶ W.1.left),
    yoneda.map q ≫ W.1.hom = V'.1.hom ≫ g'.hom ∧ P W
  refine ⟨R, ?_, fun V' k ⟨W, q, hq, a, b, hW⟩ => ⟨a, b, ?_⟩⟩
  · exact generate_mem_topology_chartsOver_of_cover g' P
      (fun W => (exists_cover_hasTorAmplitudeCanonical_relativeStalk f hfl hlfp K hK W).imp
        fun R hR => ⟨hR.1, fun V k hk => hR.2 k hk⟩)
      (fun m ⟨a, b, hab⟩ =>
        ⟨a, b, fun x p => hab x ((etaleSitePoint B S hS X.1 x X.2).fiber.map m p)⟩)
      U'
  · refine
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family
        _ _ a b
        (fun ψ : Σ x' : GeometricPoint B S hS X'.1,
            (etaleSitePoint B S hS X'.1 x' X'.2).fiber.obj V' =>
          (etaleSitePoint B S hS X'.1 ψ.1 X'.2).over ψ.2)
        (isConservativeFamilyOfPoints_etaleSitePointOver B S hS X'.2 V') (fun ψ => ?_)
    refine (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff
      (inverseImageRingedSite B S hS f') (etaleSitePoint B S hS X'.1 ψ.1 X'.2) ψ.2 _ a b).2 ?_
    refine hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback g' f' f g sq
      (torIndependent_of_isFlat_left f g hfl) ψ.1 K a b (hW _ ⟨ψ.2.1 ≫ q, ?_⟩)
    exact (congrArg (fun α => α.app (op ψ.1.val.siteObject) ψ.2.1) hq).trans
      (congrArg (g'.hom.app (op ψ.1.val.siteObject)) ψ.2.2)

end BaseChange

end AlgebraicGeometry.Space

end
