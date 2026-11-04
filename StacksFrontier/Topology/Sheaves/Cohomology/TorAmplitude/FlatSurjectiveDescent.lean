module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Tor amplitude descends along a surjective flat morphism

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a surjective flat morphism of locally ringed spaces and let
`E` be an object of `D(𝒪_Y)`.  Then `E` has Tor amplitude in `[a, b]` if and only if `Lf^*E`
does.

## Main results

* `Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_derivedPullback_iff`: for a
  surjective flat morphism `f` of locally ringed spaces, `E` has Tor amplitude in `[a, b]` if and
  only if `Lf^*E` does.
* `Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_iff_forall_derivedPullback`: the
  same for a jointly surjective *family* of flat morphisms, indexed in an arbitrary universe.
* `Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_iff_forall_fpqc`: the same for a
  family of morphisms of schemes in `AlgebraicGeometry.Scheme.fpqcPrecoverage`, which is the
  Tor-amplitude half of Tag 09UG.

## Implementation notes

The forward implication is Tag 09U8. For the converse, `f^*` is exact (Tag 02N4), so `Lf^*` is
`Functor.mapDerivedCategory` of `f^*` and commutes with the cohomology functors; `Lf^*` is
monoidal (Tag 079U); and `f^*` reflects zero objects, because on stalks it is base change along
the germ maps `𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}` (Tag 0098), which are flat local homomorphisms of local
rings and hence faithfully flat (Tag 00HR).

Tor amplitude is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, the predicate of Tag 08CG
read at the canonical derived tensor product of Tag 06YU on the site of opens, and the derived
pullback is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`.

## References

* [Stacks Project, Tag 09UD](https://stacks.math.columbia.edu/tag/09UD)
* [Stacks Project, Tag 09U8](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00HR](https://stacks.math.columbia.edu/tag/00HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.TorAmplitude.FlatDescent

universe u v

/-! ### Faithful flatness of the germ maps -/

/-- **Faithful flatness transfers across a square of ring isomorphisms.**  If
`eA ∘ φ = ψ ∘ eB` with `eB : B ≃+* B'` and `eA : A ≃+* A'` ring isomorphisms and
`ψ : B' →+* A'` faithfully flat, then `φ : B →+* A` is faithfully flat. -/
private theorem faithfullyFlat_of_ringEquiv_square {B B' A A' : Type v} [CommRing B]
    [CommRing B'] [CommRing A] [CommRing A'] {φ : B →+* A} {ψ : B' →+* A'} (eB : B ≃+* B')
    (eA : A ≃+* A') (hsq : eA.toRingHom.comp φ = ψ.comp eB.toRingHom)
    (hψ : ψ.FaithfullyFlat) : φ.FaithfullyFlat := by
  have hφ : φ = eA.symm.toRingHom.comp (ψ.comp eB.toRingHom) := by
    rw [← hsq]
    ext b
    simp
  rw [hφ]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective eB.bijective) hψ)
    (RingHom.FaithfullyFlat.of_bijective eA.symm.bijective)

/-- **Base change along a flat germ map between local rings reflects zero objects.**  Let
`f : X ⟶ Y` be a morphism of ringed spaces which is flat at `x`, with `𝒪_{Y, f(x)}` and
`𝒪_{X, x}` local and the stalk map a local homomorphism. Then a module `M` over `𝒪_{Y, f(x)}`
whose base change `Stacks.RingedSpace.stalkBaseChange f x` along the germ map is zero is
itself zero. -/
theorem isZero_of_isZero_stalkBaseChange {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : X ⟶ Y) (x : X.carrier) (hflat : AlgebraicGeometry.IsFlatAt f x)
    (hloc : IsLocalHom (f.hom.stalkMap x).hom)
    (hY : IsLocalRing (Y.presheaf.stalk (f.hom.base x)))
    (hX : IsLocalRing (X.presheaf.stalk x))
    (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing Y).obj (f.hom.base x)))
    (hM : IsZero ((Stacks.RingedSpace.stalkBaseChange f x).obj M)) : IsZero M := by
  let := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X x
  let := hloc
  let := hY
  let := hX
  have hff : (Stacks.RingedSpace.stalkRingMap f x).hom.FaithfullyFlat := by
    refine faithfullyFlat_of_ringEquiv_square (ψ := (f.hom.stalkMap x).hom)
      (Stacks.RingedSpace.ringStalkCommIso Y (f.hom.base x)).ringCatIsoToRingEquiv
      (Stacks.RingedSpace.ringStalkCommIso X x).ringCatIsoToRingEquiv ?_
      (faithfullyFlat_of_flat_of_isLocalHom _ hflat)
    exact RingHom.ext fun r => congrArg (fun g => (ConcreteCategory.hom g) r)
      (Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso f x)
  exact (Stacks.ProjectiveCohomology.isZero_extendScalars_iff
    (Stacks.RingedSpace.stalkRingMap f x).hom hff M).mp hM

/-! ### Degreewise pullback reflects zero objects -/

/-- If base change along the germ map at `x` reflects zero objects and `f^*G` is zero, then the
stalk of `G` at `f(x)` is zero. -/
private theorem isZero_stalk_of_isZero_modulePullback {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : X ⟶ Y) (x : X.carrier)
    (hff : ∀ M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing Y).obj (f.hom.base x)),
      IsZero ((Stacks.RingedSpace.stalkBaseChange f x).obj M) → IsZero M)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (hG : IsZero ((modulePullback f).obj G)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
      (f.hom.base x)).obj G) :=
  hff _ (IsZero.of_iso (Functor.map_isZero
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x) hG)
    ((Stacks.RingedSpace.stalkModulePullbackFunctorIso f x).app G).symm)

/-- **A surjective morphism whose germ base changes reflect zero objects has a pullback that
reflects zero objects.**  If `f` is surjective and base change along each of its germ maps
reflects zero objects, then a sheaf of `𝒪_Y`-modules `G` with `f^*G` zero is zero. -/
theorem isZero_of_isZero_modulePullback {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : X ⟶ Y) (hsurj : Function.Surjective f.hom.base)
    (hff : ∀ (x : X.carrier) (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing Y).obj (f.hom.base x))),
      IsZero ((Stacks.RingedSpace.stalkBaseChange f x).obj M) → IsZero M)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (hG : IsZero ((modulePullback f).obj G)) : IsZero G := by
  rw [AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj]
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact isZero_stalk_of_isZero_modulePullback f x (hff x) G hG

/-! ### The derived pullback along a flat morphism -/

section Flat

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

section

variable [PreservesFiniteLimits (modulePullback f)]
  [PreservesFiniteColimits (modulePullback f)]

/-- **Along a flat morphism the derived pullback is the degreewise pullback.**  For an exact
`f^*`, the functor `Functor.mapDerivedCategory` of `f^*` is isomorphic to `Lf^*`. -/
private def mapDerivedCategoryIsoDerivedPullback :
    (modulePullback f).mapDerivedCategory ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f :=
  @Functor.leftDerivedUnique _ _ _ _ _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (modulePullback f).mapDerivedCategory _ _
    (modulePullback f).mapDerivedCategoryFactorsh.hom
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ))
    inferInstance
    (Functor.isLeftDerivedFunctor_of_inverts _ _ (modulePullback f).mapDerivedCategoryFactorsh)
    inferInstance

/-- **Along a flat morphism the derived pullback commutes with the cohomology functors**:
`H^i(Lf^*K) ≅ f^*H^i(K)`. -/
private def derivedPullbackHomologyIso (i : ℤ)
    (K : DerivedCategory (OXMod.{u, u} Y)) :
    (modulePullback f).obj ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).obj K) ≅
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K) :=
  ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (modulePullback f) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso
      ((mapDerivedCategoryIsoDerivedPullback f).app K)

/-- **Along a flat morphism the derived pullback of a module placed in degree `0` is its
pullback placed in degree `0`.** -/
private def derivedPullbackSingleIso (F : OXMod.{u, u} Y) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj F) ≅
      (DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj ((modulePullback f).obj F) :=
  ((mapDerivedCategoryIsoDerivedPullback f).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj F)).symm ≪≫
    ((modulePullback f).mapDerivedCategorySingleFunctor 0).app F

end

/-- For a flat morphism `f`, an `𝒪_Y`-module `F` and a degree `i`, the pullback of
`H^i(E ⊗^L_{𝒪_Y} F[0])` is `H^i(Lf^*E ⊗^L_{𝒪_X} (f^*F)[0])`. -/
private def pullbackHomologyTensorIso (hflat : AlgebraicGeometry.IsFlat f)
    (E : DerivedCategory (OXMod.{u, u} Y)) (F : OXMod.{u, u} Y) (i : ℤ) :
    (modulePullback f).obj ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).obj
        (((derTensor Y).tensor.obj E).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj F))) ≅
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
        (((derTensor X).tensor.obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E)).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
            ((modulePullback f).obj F))) := by
  letI : PreservesFiniteLimits (modulePullback f) :=
    preservesFiniteLimits_modulePullback_of_isFlat f hflat
  letI : PreservesFiniteColimits (modulePullback f) :=
    preservesFiniteColimits_modulePullback f
  refine derivedPullbackHomologyIso f i _ ≪≫
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso ?_
  exact (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).app
      (E, (DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj F) ≪≫
    ((derTensor X).tensor.obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E)).mapIso
      (derivedPullbackSingleIso f F)

end Flat

/-! ### Tag 09UD -/

attribute [local instance] HasDerivedCategory.standard

/-- Let `f : X ⟶ Y` be a surjective flat morphism of locally ringed spaces, let `E` be an
object of `D(𝒪_Y)` and let `a, b` be integers.  Then `E` has Tor amplitude in `[a, b]` if and
only if `Lf^*E` has Tor amplitude in `[a, b]`. -/
@[stacks 09UD]
theorem hasTorAmplitude_derivedPullback_iff {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hsurj : Function.Surjective f.base) (hflat : AlgebraicGeometry.IsFlat f.toShHom)
    (E : DerivedCategory (OXMod.{u, u} Y.toRingedSpace)) (a b : ℤ) :
    HasTorAmplitude Y.toRingedSpace E a b ↔
      HasTorAmplitude X.toRingedSpace
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toShHom).obj E)
        a b := by
  refine ⟨Pullback.hasTorAmplitude_derivedPullback f.toShHom E a b, fun hE F i hi => ?_⟩
  refine isZero_of_isZero_modulePullback f.toShHom hsurj
    (fun x => isZero_of_isZero_stalkBaseChange f.toShHom x (hflat x)
      (LocallyRingedSpace.isLocalHomStalkMap f x) (Y.isLocalRing _) (X.isLocalRing x)) _ ?_
  exact IsZero.of_iso (hE ((modulePullback f.toShHom).obj F) i hi)
    (pullbackHomologyTensorIso f.toShHom hflat E F i)

/-! ### A jointly surjective family in place of a single surjection -/

/-- **A sheaf of modules whose pullback along every member of a jointly surjective family
vanishes is zero**, provided base change along each germ map of the family reflects vanishing. -/
theorem isZero_of_forall_isZero_modulePullback {Y : AlgebraicGeometry.RingedSpace.{u, u}}
    {I : Type v} {X : I → AlgebraicGeometry.RingedSpace.{u, u}} (f : ∀ i, X i ⟶ Y)
    (hsurj : ∀ y : Y.carrier, ∃ i, ∃ x : (X i).carrier, (f i).hom.base x = y)
    (hff : ∀ (i : I) (x : (X i).carrier)
        (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafRing Y).obj ((f i).hom.base x))),
      IsZero ((Stacks.RingedSpace.stalkBaseChange (f i) x).obj M) → IsZero M)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (hG : ∀ i, IsZero ((modulePullback (f i)).obj G)) : IsZero G := by
  rw [AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj]
  intro y
  obtain ⟨i, x, rfl⟩ := hsurj y
  exact isZero_stalk_of_isZero_modulePullback (f i) x (hff i x) G (hG i)

/-- **Tor amplitude descends along a jointly surjective family of flat morphisms of locally
ringed spaces.** Let `{f_i : X_i ⟶ Y}` be a family of flat morphisms of locally ringed spaces
whose images cover `Y`, let `E` be an object of `D(𝒪_Y)` and let `a, b` be integers.  Then `E`
has Tor amplitude in `[a, b]` if and only if every derived pullback `Lf_i^*E` does. -/
@[sga "6 I 5.5" "special case", sga "6 I 5.7" "a), special case"]
theorem hasTorAmplitude_iff_forall_derivedPullback {Y : LocallyRingedSpace.{u}} {I : Type v}
    {X : I → LocallyRingedSpace.{u}} (f : ∀ i, X i ⟶ Y)
    (hsurj : ∀ y : Y, ∃ i, ∃ x : (X i), (f i).base x = y)
    (hflat : ∀ i, AlgebraicGeometry.IsFlat (f i).toShHom)
    (E : DerivedCategory (OXMod.{u, u} Y.toRingedSpace)) (a b : ℤ) :
    HasTorAmplitude Y.toRingedSpace E a b ↔
      ∀ i, HasTorAmplitude (X i).toRingedSpace
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (f i).toShHom).obj E) a b := by
  refine ⟨fun hE i => Pullback.hasTorAmplitude_derivedPullback (f i).toShHom E a b hE,
    fun hE F i hi => ?_⟩
  refine isZero_of_forall_isZero_modulePullback (fun j => (f j).toShHom) hsurj
    (fun j x => isZero_of_isZero_stalkBaseChange (f j).toShHom x (hflat j x)
      (LocallyRingedSpace.isLocalHomStalkMap (f j) x) (Y.isLocalRing _) ((X j).isLocalRing x))
    _ fun j => IsZero.of_iso (hE j ((modulePullback (f j).toShHom).obj F) i hi)
      (pullbackHomologyTensorIso (f j).toShHom (hflat j) E F i)

/-- **Tor amplitude descends along an fpqc covering of schemes.**  Let `{f_i : Y_i ⟶ X}` be a
family of morphisms of schemes lying in `AlgebraicGeometry.Scheme.fpqcPrecoverage X`, let `E` be
an object of `D(𝒪_X)` and let `a, b` be integers.  Then `E` has Tor amplitude in `[a, b]` if and
only if every derived pullback `Lf_i^*E` does.

This is the Tor-amplitude half of Tag 09UG. -/
theorem hasTorAmplitude_iff_forall_fpqc {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ) :
    HasTorAmplitude X.toRingedSpace E a b ↔
      ∀ i, HasTorAmplitude (Y i).toRingedSpace
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (f i).toLRSHom.toShHom).obj E) a b := by
  obtain ⟨hsurj, hflat⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hf.2
  exact hasTorAmplitude_iff_forall_derivedPullback (fun i => (f i).toLRSHom) hsurj
    (fun i x => have := hflat i; Flat.stalkMap (f i) x) E a b

end Stacks.Cohomology.TorAmplitude.FlatDescent

end
