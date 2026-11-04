module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.Homology.RelativelyPerfect.Criterion
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.KoszulLiftSheaf
import all StacksFrontier.Homology.RelativelyPerfect.Criterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The amplitude of derived pullback along a Tor-independent base change

Consider a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Spec R' --> Spec R
```

with `X` and `Spec R'` Tor independent over `Spec R`, and suppose `R'` has Tor amplitude in
`[a, b]` over `R`. Then `L(g')^*` lowers lower bounds on cohomology by at most `-a`. At a point
`x'` of `X'` the stalk of `L(g')^*N` is `𝒪_{X',x'} ⊗^𝐋_{𝒪_{X,g'(x')}} N_{g'(x')}`, and the
local ring `𝒪_{X',x'}` has Tor amplitude in `[a, b]` over `𝒪_{X,g'(x')}`: this is
Stacks 0C0V applied to the transposed square and to `𝒪_{Spec R'}`, whose Tor amplitude over
`Spec R` is that of `R'` over `R` (Stacks 0DHY).

## Main results

* `AlgebraicGeometry.DerivedPullbackAmplitude.isGE_totalDerivedExtensionScalars`: derived
  extension of scalars along a ring map `A → C`, with `C` of Tor amplitude in `[e, b]` over `A`,
  carries an object of `D(A)` vanishing below `n` to an object vanishing below `n + e`.
* `AlgebraicGeometry.DerivedPullbackAmplitude.isGE_of_forall_derivedStalkFunctor`: lower bounds
  on cohomology on a scheme are detected on the derived stalks.
* `AlgebraicGeometry.DerivedPullbackAmplitude.hasTorAmplitudeCanonical_stalk`: the local rings
  upstairs have Tor amplitude in `[a, b]` over the local rings of `X`.
* `AlgebraicGeometry.DerivedPullbackAmplitude.hasDerivedPullbackAmplitude`: the amplitude bound
  for `L(g')^*`.

## References

* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 0AA7](https://stacks.math.columbia.edu/tag/0AA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.DerivedPullbackAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

section Ring

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- **Extension of scalars along a ring map of bounded Tor amplitude shifts lower bounds.**  If
`C`, as an `A`-module, has Tor amplitude in `[e, b]`, then for a K-flat complex `P` of
`A`-modules whose cohomology vanishes below `n`, the complex `C ⊗_A P` of `C`-modules has
cohomology vanishing below `n + e`. -/
theorem isGE_Q_extendScalars (e b : ℤ)
    (hC : HasTorAmplitudeCanonical A ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))) e b)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (n : ℤ)
    (hPn : (DerivedCategory.Q.obj P).IsGE n) :
    (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).IsGE
        (n + e) := by
  let N := (ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)
  obtain ⟨F, hFflat, hFge, hFle, ⟨eF⟩⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative A _ e b).1 hC
  have hFk : F.KFlat := CochainComplex.KFlat.kFlat_of_flat.{u, u} F b
  obtain ⟨G, hG, ⟨eG⟩⟩ := (DerivedCategory.Q.obj P).exists_iso_Q_obj_of_isGE n
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N
  obtain ⟨c₁⟩ := CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat T P L hP
  obtain ⟨c₂⟩ := CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat T F G hFk
  let eN : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj F :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app N).symm ≪≫ eF
  let e₁ : DerivedCategory.Q.obj (P ⊗ L) ≅ DerivedCategory.Q.obj (F ⊗ G) :=
    c₁.symm ≪≫ (T.tensor.obj _).mapIso eN ≪≫
      CochainComplex.DerivedTensor.derivedTensorProductCommIso _ _ ≪≫
      (T.tensor.obj _).mapIso eG ≪≫ c₂
  have hFG : (F ⊗ G).IsStrictlyGE (e + n) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hz : IsZero (F.X p ⊗ G.X q) := by
      by_cases hp : p < e
      · exact (tensorRight (G.X q)).map_isZero (F.isZero_of_isStrictlyGE e p hp)
      · have hq : q < n := by
          change p + q = i at hpq
          omega
        exact (tensorLeft (F.X p)).map_isZero (G.isZero_of_isStrictlyGE n q hq)
    exact hz.eq_of_src _ _
  let e₃ : tensorLeft N ≅ ModuleCat.extendScalars φ ⋙ ModuleCat.restrictScalars φ :=
    NatIso.ofComponents (fun M => Iso.refl _) fun _ => rfl
  let e₂ : ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      P ⊗ L :=
    (NatIso.mapHomologicalComplex e₃ (ComplexShape.up ℤ)).symm.app P ≪≫
      (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight N)
        (ComplexShape.up ℤ)).app P ≪≫
      @asIso _ _ _ _ (AdicCompletionTor.tensorSingleInclusion N P)
        (AdicCompletionTor.tensorSingleInclusion_isIso N P)
  rw [← PseudoCoherence.isGE_restrictScalars_iff φ, add_comm]
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (e₁.symm ≪≫ DerivedCategory.Q.mapIso e₂.symm ≪≫
      ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app _).symm) (e + n)

/-- **Derived extension of scalars along a ring map of bounded Tor amplitude shifts lower
bounds.**  If `C`, as an `A`-module, has Tor amplitude in `[e, b]`, then `C ⊗^𝐋_A -` carries an
object of `D(A)` whose cohomology vanishes below `n` to an object of `D(C)` whose cohomology
vanishes below `n + e`. -/
theorem isGE_totalDerivedExtensionScalars (e b : ℤ)
    (hC : HasTorAmplitudeCanonical A ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))) e b)
    (E : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (hE : E.IsGE n) :
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ).functor.obj E).IsGE (n + e) := by
  obtain ⟨P, p, hPlarge, -, hp, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage E)
  have hP : P.KFlat := hPlarge
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  have := isGE_Q_extendScalars φ e b hC P hP n (DerivedCategory.TStructure.t.isGE_of_iso eP.symm n)
  let c : DerivedCategory.Q.obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        D.functor.obj E :=
    (asIso (D.comparison.app P)).symm ≪≫ D.functor.mapIso eP
  exact DerivedCategory.TStructure.t.isGE_of_iso c (n + e)

end Ring

section Stalks

open Stacks.ModuleSkyscraper

/-- **Lower bounds on cohomology are detected on the derived stalks.** -/
theorem isGE_of_forall_derivedStalkFunctor {Z : Scheme.{u}} (E : DerivedCategory Z.Modules)
    (m : ℤ) (h : ∀ z : Z, ((derivedStalkFunctor z).obj E).IsGE m) : E.IsGE m := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  refine isZero_of_forall_modulesStalk _ fun z => ?_
  exact ((DerivedCategory.isGE_iff _ _).1 (h z) i hi).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (modulesStalkFunctor Z z) i).app E).symm

/-- **Derived stalks preserve lower bounds on cohomology**: the stalk functor is exact. -/
theorem isGE_derivedStalkFunctor {Z : Scheme.{u}} (E : DerivedCategory Z.Modules) (m : ℤ)
    (hE : E.IsGE m) (z : Z) : ((derivedStalkFunctor z).obj E).IsGE m := by
  rw [DerivedCategory.isGE_iff] at hE ⊢
  intro i hi
  exact ((modulesStalkFunctor Z z).map_isZero (hE i hi)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (modulesStalkFunctor Z z) i).app E)

/-- The stalk of `𝒪_Z`, regarded as a module over itself, at a point `z` is the local ring
`𝒪_{Z,z}` regarded as a module over itself. -/
def modulesStalkUnitIso (Z : Scheme.{u}) (z : Z) :
    (modulesStalkFunctor Z z).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      ModuleCat.of (Z.presheaf.stalk z) (Z.presheaf.stalk z) :=
  (Stacks.Ample.unitStalkEquiv Z z).toModuleIso

end Stalks

section BaseChange

open Stacks.ModuleSkyscraper

variable {R R' : CommRingCat.{u}} (φ : R ⟶ R') {X X' : Scheme.{u}} (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g' : X' ⟶ X)

/-- `𝒪_{X'}` placed in degree zero, as the derived pullback along `f' : X' ⟶ Spec R'` of the
sheaf associated with `R'`. -/
def derivedPullbackTildeSelfIso :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f'.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')))) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor X'.Modules 0).obj
        (SheafOfModules.unit X'.ringCatSheaf)) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f'.toLRSHom.toShHom).mapIso
    (DerivedCategory.Q.mapIso (Stacks.AffineTilde.tildeSingleSelfIso R') ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm) ≪≫
    Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f'.toLRSHom.toShHom ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _

/-- The stalk at `x'` of `𝒪_{X'}` placed in degree zero, read over the local ring of `X` at
`g'(x')`, is the local ring `𝒪_{X',x'}` regarded as an `𝒪_{X,g'(x')}`-module, placed in degree
zero. -/
def relativeStalkComplexUnitIso (x' : X') :
    DerivedCategory.Q.obj (relativeStalkComplex g'
        ((CochainComplex.singleFunctor X'.Modules 0).obj (SheafOfModules.unit X'.ringCatSheaf))
        x') ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk (g'.base x'))) 0).obj
        ((ModuleCat.restrictScalars (g'.stalkMap x').hom).obj
          (ModuleCat.of (X'.presheaf.stalk x') (X'.presheaf.stalk x'))) :=
  DerivedCategory.Q.mapIso
      (((ModuleCat.restrictScalars (g'.stalkMap x').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (modulesStalkFunctor X' x')
          (ComplexShape.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.restrictScalars (g'.stalkMap x').hom) (ComplexShape.up ℤ) 0).app _ ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso
          ((ModuleCat.restrictScalars (g'.stalkMap x').hom).mapIso
            (modulesStalkUnitIso X' x'))) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- **The local rings of a Tor-independent base change have bounded Tor amplitude.**  Let
`X' --g'--> X`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'` be a cartesian square over
`Spec φ : Spec R' ⟶ Spec R` with `X` and `Spec R'` Tor independent over `Spec R`.  If `R'` has Tor
amplitude in `[a, b]` over `R`, then at every point `x'` of `X'` the local ring `𝒪_{X',x'}` has
Tor amplitude in `[a, b]` over `𝒪_{X,g'(x')}`. -/
theorem hasTorAmplitudeCanonical_stalk (hsq : IsPullback g' f' f (Spec.map φ))
    (hTor : TorIndependent f (Spec.map φ)) (a b : ℤ)
    (hR' : HasTorAmplitudeCanonical R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (letI : Algebra R R' := φ.hom.toAlgebra; ModuleCat.of R R')) a b) (x' : X') :
    HasTorAmplitudeCanonical (X.presheaf.stalk (g'.base x'))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk (g'.base x'))) 0).obj
        ((ModuleCat.restrictScalars (g'.stalkMap x').hom).obj
          (ModuleCat.of (X'.presheaf.stalk x') (X'.presheaf.stalk x')))) a b := by
  let : Algebra R R' := φ.hom.toAlgebra
  let M := (CochainComplex.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')
  have h₁ : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) a b :=
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
        DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R R')) (ComplexShape.up ℤ) 0).app
            (ModuleCat.of R' R')).symm) a b hR'
  have h₂ : HasTorAmplitudeOver (Spec.map φ)
      (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) a b :=
    (AffineRelativeTorAmplitude.hasTorAmplitudeOver_tildeComplex_iff R R' M a b).2 h₁
  obtain ⟨K₀, ⟨e₀⟩, hK₀⟩ := derivedPullback_hasTorAmplitudeOver f' g' (Spec.map φ) f hsq.flip
    hTor.symm _ a b h₂
  exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    (relativeStalkComplexUnitIso g' x') a b
    (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_moduleLift _ a b
      (relativeStalkAmplitude_of_derivedIso g' a b (e₀ ≪≫ derivedPullbackTildeSelfIso f') hK₀ x'))

/-- **Derived pullback along a Tor-independent base change of a morphism of finite Tor
dimension has bounded amplitude.**  In the situation of `hasTorAmplitudeCanonical_stalk`, if `R'`
has Tor amplitude in `[a, b]` over `R`, then `L(g')^*` carries an object of `D(𝒪_X)` whose
cohomology vanishes below `n` to an object of `D(𝒪_{X'})` whose cohomology vanishes below
`n + a`: at a point `x'` the stalk of `L(g')^*N` is `𝒪_{X',x'} ⊗^𝐋_{𝒪_{X,g'(x')}} N_{g'(x')}`. -/
@[sga "6 IV 3.1.1" "special case"]
theorem hasDerivedPullbackAmplitude (hsq : IsPullback g' f' f (Spec.map φ))
    (hTor : TorIndependent f (Spec.map φ)) (a b : ℤ)
    (hR' : HasTorAmplitudeCanonical R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (letI : Algebra R R' := φ.hom.toAlgebra; ModuleCat.of R R')) a b) :
    Stacks.Cohomology.DerivedInternalHomPullback.HasDerivedPullbackAmplitude
      g'.toLRSHom.toShHom (-a) := by
  intro N n hN
  refine isGE_of_forall_derivedStalkFunctor _ _ fun x' => ?_
  have h₂ := isGE_totalDerivedExtensionScalars (g'.stalkMap x').hom a b
    (hasTorAmplitudeCanonical_stalk φ f f' g' hsq hTor a b hR' x') _ n
    (isGE_derivedStalkFunctor N n hN (g'.base x'))
  rw [sub_neg_eq_add]
  rw [DerivedCategory.isGE_iff] at h₂ ⊢
  intro i hi
  exact (h₂ i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((derivedPullbackStalkIso g' x').app N))

end BaseChange

end AlgebraicGeometry.DerivedPullbackAmplitude

end
