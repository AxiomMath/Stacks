module

public import StacksFrontier.AlgebraicGeometry.Bridge.SchemeBridge
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteMorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedTildePushforward
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Derived sheaf Hom with exact support on quasi-coherent complexes

Let `i : Z ⟶ X` be a pseudo-coherent closed immersion of schemes. This file proves the two
parts of [Stacks, Tag 0A78]:

1. the right derived functor `R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` of sheaf Hom with exact
   support carries `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(𝒪_Z)`;
2. for `X = Spec A` and `Z = Spec B` the square

   `D⁺(A) ⥤ D⁺_QCoh(𝒪_X)`,  `D⁺(B) ⥤ D⁺_QCoh(𝒪_Z)`

   whose horizontal arrows are derived sheafification, whose left vertical arrow is
   `R Hom_A(B, -)` and whose right vertical arrow is `R ℰom(𝒪_Z, -)`, commutes.

By [Stacks, Tag 0684] every closed immersion into a locally Noetherian scheme is pseudo-coherent,
which is the parenthetical assertion of the tag; each part therefore comes with a locally
Noetherian variant.

## Part (1)

*Boundedness below* is left t-exactness of an unbounded right derived functor: a bounded-below
object has a bounded-below injective resolution, which is K-injective and therefore computes the
derived functor degreewise, and an additive functor sends zero objects to zero objects. No
hypothesis on `i` enters.

*Quasi-coherence* is checked after `i_*`, which is exact and whose essential image consists of
the modules annihilated by the kernel ideal of `i^♯` ([Stacks, Tag 08KS]); on quasi-coherent
modules that essential image is described by [Stacks, Tag 01QY], and together these say that an
`𝒪_Z`-module is quasi-coherent as soon as its pushforward is. After `i_*` the derived sheaf Hom
with exact support becomes the derived internal Hom out of `Ri_* 𝒪_Z` by [Stacks, Tag 0A77], and
`Ri_* 𝒪_Z` is a pseudo-coherent object of `D(𝒪_X)` precisely because `i` is pseudo-coherent
([Stacks, Tag 0AVX]). Part (1) of [Stacks, Tag 0A6H] then gives the quasi-coherence of the
cohomology sheaves of that derived internal Hom.

## Part (2)

The commutativity is realized by a comparison map, natural in the object of `D(A)`: the map

`(R Hom_A(B, L))^~ ⟶ R ℰom(𝒪_Z, L^~)`

adjoint under [Stacks, Tag 0A76] to the sheafified counit of [Stacks, Tag 0A70] read through
[Stacks, Tag 01I9] on derived categories. It is invertible at every bounded-below `L`. Both of
its sides then have quasi-coherent cohomology sheaves — the target by part (1) — so both are
derived sheafifications and the comparison is the sheafification of a map of `D(B)`; that map
induces, on morphisms out of any object, the composite of the adjunction bijection of
[Stacks, Tag 0A70], full faithfulness of derived sheafification, composition with an isomorphism
and the adjunction bijection of [Stacks, Tag 0A76], so it is an isomorphism by Yoneda.

## Main definitions

* `AlgebraicGeometry.Scheme.pushforwardDerivedStructureSheafIso` identifies `Ri_* 𝒪_Z` with the
  degree-zero complex on `i_* 𝒪_Z`.
* `AlgebraicGeometry.affineDerivedPushforwardTildeIso` is [Stacks, Tag 01I9] on derived
  categories: `Ri_* ∘ (-)^~ ≅ (-)^~ ∘` restriction of scalars.
* `AlgebraicGeometry.affineDerivedSheafHomComparison` is the comparison map of part (2).

## Main results

* `AlgebraicGeometry.Scheme.isQuasicoherent_of_pushforward`: an `𝒪_Z`-module whose pushforward
  along a closed immersion is quasi-coherent is quasi-coherent.
* `AlgebraicGeometry.Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf`: for a
  pseudo-coherent closed immersion, `Ri_* 𝒪_Z` is pseudo-coherent.
* `isBoundedBelow_derivedSheafHomExactSupport_obj`, in the namespace
  `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`: derived sheaf Hom with
  exact support preserves cohomological boundedness below.
* `AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus` is part (1) of
  [Stacks, Tag 0A78] and
  `AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus_of_noetherian`
  its locally Noetherian case.
* `AlgebraicGeometry.affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus` is the case of
  part (1) for a pseudo-coherent closed immersion of affine schemes and a sheafified argument,
  proved directly with the lower bound on degrees made explicit; it is what part (2) consumes,
  and it carries no tag of its own since part (1) covers it.
* `AlgebraicGeometry.map_comp_affineDerivedSheafHomComparison_app` computes the comparison map of
  part (2) against a sheafified morphism, which is what makes it invertible.
* `AlgebraicGeometry.isIso_affineDerivedSheafHomComparison_app` is part (2) of
  [Stacks, Tag 0A78] and
  `AlgebraicGeometry.isIso_affineDerivedSheafHomComparison_app_of_noetherian` its locally
  Noetherian case.

## Implementation notes

**Where part (1) of [Stacks, Tag 0A6H] comes from.** That the derived internal Hom out of a
pseudo-coherent object into an object of `D⁺_QCoh` has quasi-coherent cohomology is
`AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`, proved for an
arbitrary scheme. The affine statements below do not go through it: on `Spec R` the tag is
available for a sheafified second argument, as
`AlgebraicGeometry.derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent`.

**Where [Stacks, Tag 06Z0] comes from.** That derived sheafification is an equivalence
onto `D_QCoh` on an affine scheme is used at the standard model of the derived category, which is
the model this file selects, through
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful` and
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`. Importing that
file brings `StacksFrontier.Homology.DerivedCategory.LocallySmall` into the closure, whose
`HasDerivedCategory` instances are *global*; the priority `10000` on the local attribute below is
what keeps them from being selected, so every statement in this file still reads at the standard
model and none of their types moved when the import was added.

**Membership in `D⁺_QCoh`** is `DerivedCategoryB.derivedCategoryBPlus` applied to the object
property `SheafOfModules.isQuasicoherent`: cohomological boundedness below together with
quasi-coherence of every cohomology sheaf. So "maps `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(𝒪_Z)`" is
expressed as a property of the object `R ℰom(𝒪_Z, K)` for `K` in `D⁺_QCoh(𝒪_X)`, not as a
lifted functor; and the commuting square of part (2) is expressed by a natural transformation
defined on all of `D(A)` together with its invertibility on the bounded-below objects, rather
than by a natural isomorphism of functors restricted to a subcategory.

**The adjunction of [Stacks, Tag 0A70] is chosen, not assumed.** The library proves it as
`Dualizing.restrictScalarsDerived_adj_derivedHom`, a `Nonempty`; the comparison map is built from
`Classical.choice` of it. Part (2) holds for whichever adjunction is chosen — the Yoneda argument
uses only that it is one — so nothing about the choice enters the statement.

**Three spellings of `𝒪_X`-modules** meet here: sheaf Hom with exact support is stated over
`structureSheafRing`, pseudo-coherence over
`Stacks.StrictlyPerfect.OXMod`, and sheafification and quasi-coherence over
`AlgebraicGeometry.Scheme.Modules`. They unfold to the same category, but their instances are
found by different paths, so a goal that mixes two of them is not type-correct at the
transparency at which `rewrite` builds its motive. Hence
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent.of_iso` is applied with its source object given
explicitly; `affineDerivedPushforwardTildeIso` passes through the ascription `e` to move between
`AlgebraicGeometry.Scheme.Modules.pushforward`, in which [Stacks, Tag 01I9] is stated, and
`RingedSpaceModuleAdjunction.modulePushforward`, in which the exact-support adjunction is; and
the proofs about the comparison map are written as composites of `congrArg` rather than as
rewrites.

## References

* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0AVX](https://stacks.math.columbia.edu/tag/0AVX)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

/-- **Boundedness below is preserved by `R ℰom(𝒪_Z, -)`.** For a closed quotient morphism of
ringed spaces, the right derived functor of sheaf Hom with exact support is left t-exact: it
carries an object with no cohomology below degree `n` to an object with no cohomology below
degree `n`, because a bounded-below injective resolution is K-injective and therefore computes
the derived functor degreewise, and an additive functor preserves zero objects. -/
theorem isBoundedBelow_derivedSheafHomExactSupport_obj
    (S : ClosedQuotientMorphismOfRingedSpaces.{u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow (S.derivedSheafHomExactSupport.obj K) := by
  obtain ⟨n, hn⟩ := hK
  have hGE : K.IsGE n := (DerivedCategory.isGE_iff K n).2 hn
  have h := Stacks.DerivedFunctor.isGE_totalRightDerived_obj S.sheafHomExactSupport K n
  exact ⟨n, (DerivedCategory.isGE_iff _ n).1 h⟩

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace AlgebraicGeometry

namespace Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **[Stacks, Tag 01QY] in the form a descent argument consumes.** An `𝒪_Z`-module whose
pushforward along a closed immersion `i : Z ⟶ X` is quasi-coherent is itself quasi-coherent.

Pushforward along a closed immersion is fully faithful, and by [Stacks, Tag 08KS] its essential
image consists of the `𝒪_X`-modules annihilated by the kernel ideal of `i^♯`. By
[Stacks, Tag 01QY] the pushforward of quasi-coherent modules has the same essential image inside
the quasi-coherent modules, so a quasi-coherent `i_* M` is the pushforward of a quasi-coherent
module, which full faithfulness identifies with `M`. -/
theorem isQuasicoherent_of_pushforward (M : Z.Modules)
    (hM : ((modulePushforward
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  set S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i with hS
  set F := modulePushforward S.i with hF
  have hAnn := (Stacks.Tag08KS.ClosedQuotient.modulePushforward_essImage_iff S
    (F.obj M)).1 ⟨M, ⟨Iso.refl _⟩⟩
  have hG : (Stacks.Modules.pushforwardQcoh i).essImage ⟨F.obj M, hM⟩ :=
    (Stacks.ClosedImmersion.pushforwardQcoh_essImage_iff i (F.obj M) hM).2 hAnn
  obtain ⟨N, ⟨e⟩⟩ := hG
  have e' : F.obj N.obj ≅ F.obj M :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapIso e
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
    (F.preimageIso e') N.property

/-- Quasi-coherence of the cohomology sheaves of `R ℰom(𝒪_Z, K)` follows from that of an object
identified with `Ri_* R ℰom(𝒪_Z, K)`, since `i_*` is exact and `isQuasicoherent_of_pushforward`. -/
private theorem derivedCategoryBPlus_derivedSheafHomExactSupport_of_pushforward
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : DerivedCategoryB.IsBoundedBelow K) {Y : DerivedCategory X.Modules}
    (e : (modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
        ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport.obj
          K) ≅ Y)
    (hY : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) Y) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        i).derivedSheafHomExactSupport.obj K) := by
  set S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i with hS
  refine ⟨S.isBoundedBelow_derivedSheafHomExactSupport_obj K hK, fun n => ?_⟩
  refine isQuasicoherent_of_pushforward i _ ?_
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor _ n).mapIso e).symm ≪≫
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (modulePushforward S.i) n).app (S.derivedSheafHomExactSupport.obj K)) (hY n)

/-- Derived pushforward of the structure sheaf of a closed subscheme is the degree-zero complex
on `i_* 𝒪_Z`: pushforward along a closed immersion is exact, so it commutes with the degree-zero
single-object functor. -/
def pushforwardDerivedStructureSheafIso :
    (DerivedCategory.singleFunctor X.Modules 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf)) :=
  (((modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          i).i).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit Z.ringCatSheaf)).symm ≪≫
    (modulePushforward
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.mapIso
        (eqToIso (RingedSite.derivedStructureSheaf_eq_singleFunctor_obj
          (Stacks.SheafOfModules.ringedSite Z.sheaf)).symm)

/-- **[Stacks, Tag 0AVX] for a closed immersion.** If a closed immersion `i : Z ⟶ X` is
pseudo-coherent then `Ri_* 𝒪_Z` is a pseudo-coherent object of `D(𝒪_X)`.

A closed immersion is finite, so [Stacks, Tag 0AVX] applies and makes the pseudo-coherence of `i`
equivalent to that of the `𝒪_X`-module `i_* 𝒪_Z` in degree zero; that degree-zero complex is
`Ri_* 𝒪_Z` by `pushforwardDerivedStructureSheafIso`. -/
theorem isPseudoCoherent_pushforward_derivedStructureSheaf (hi : PseudoCoherent i) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      ((modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf))) :=
  RingedSpace.IsPseudoCoherent.of_iso
    (X := X.toRingedSpace)
    (E := (DerivedCategory.singleFunctor X.Modules 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    ((pseudoCoherent_iff_isPseudoCoherent_pushforward_unit i).1 hi)
    (pushforwardDerivedStructureSheafIso i)

/-- **Stacks Project, Tag 0A78, part (1).** Let `i : Z ⟶ X` be a pseudo-coherent closed
immersion of schemes. Then `R ℰom(𝒪_Z, -)` maps `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(𝒪_Z)`.

Boundedness below is `isBoundedBelow_derivedSheafHomExactSupport_obj`. For quasi-coherence, the
pushforward `Ri_* R ℰom(𝒪_Z, K)` is the derived internal Hom `R ℰom_{𝒪_X}(Ri_* 𝒪_Z, K)` by
[Stacks, Tag 0A77], and `Ri_* 𝒪_Z` is pseudo-coherent by [Stacks, Tag 0AVX]; part (1) of
[Stacks, Tag 0A6H] makes the cohomology sheaves of that
derived internal Hom quasi-coherent. Since `i_*` is exact it commutes with taking cohomology, so
each cohomology sheaf of `R ℰom(𝒪_Z, K)` has quasi-coherent pushforward, and
`isQuasicoherent_of_pushforward` descends quasi-coherence to `Z`. -/
@[stacks 0A78 "part (1)"]
theorem derivedSheafHomExactSupport_mem_derivedCategoryBPlus (hi : PseudoCoherent i)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        i).derivedSheafHomExactSupport.obj K) :=
  derivedCategoryBPlus_derivedSheafHomExactSupport_of_pushforward i K hK.1
    ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
      i).derivedSheafHomExactSupportPushforwardNatIso.app K)
    (derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X _ K
      (isPseudoCoherent_pushforward_derivedStructureSheaf i hi) hK)

/-- **Stacks Project, Tag 0A78, part (1), the locally Noetherian case.** For *every* closed
immersion `i : Z ⟶ X` into a locally Noetherian scheme, `R ℰom(𝒪_Z, -)` maps `D⁺_QCoh(𝒪_X)` into
`D⁺_QCoh(𝒪_Z)`: a closed immersion is locally of finite type, hence pseudo-coherent over a
locally Noetherian target by [Stacks, Tag 0684]. -/
@[stacks 0A78 "part (1) for a locally Noetherian target"]
theorem derivedSheafHomExactSupport_mem_derivedCategoryBPlus_of_noetherian
    [IsLocallyNoetherian X]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        i).derivedSheafHomExactSupport.obj K) :=
  derivedSheafHomExactSupport_mem_derivedCategoryBPlus i
    ((pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance) K hK

end Scheme

/-! ### Part (2): the affine comparison -/

variable (A B : CommRingCat.{u}) (φ : A ⟶ B)

/-- Derived sheafification preserves cohomological boundedness below, being exact. -/
theorem isBoundedBelow_tilde_mapDerivedCategory_obj (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : DerivedCategoryB.IsBoundedBelow M) :
    DerivedCategoryB.IsBoundedBelow ((tilde.functor R).mapDerivedCategory.obj M) := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, fun m hm => ?_⟩
  exact ((tilde.functor R).map_isZero (hn m hm)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (tilde.functor R) m).app M)

/-- Derived sheafification carries `D⁺(R)` into `D⁺_QCoh(𝒪_{Spec R})`. -/
theorem derivedCategoryBPlus_tilde_mapDerivedCategory_obj (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : DerivedCategoryB.IsBoundedBelow M) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      ((tilde.functor R).mapDerivedCategory.obj M) :=
  ⟨isBoundedBelow_tilde_mapDerivedCategory_obj R M hM,
    affineTilde_isQuasicoherent R M⟩

/-- **The affine case of part (1) of [Stacks, Tag 0A78], with a sheafified argument.** Let
`φ : A ⟶ B` be a ring map whose spectrum is a pseudo-coherent closed immersion
`i : Z = Spec B ⟶ X = Spec A`, and let `L` be a bounded-below object of `D(A)`. Then
`R ℰom(𝒪_Z, L^~)` lies in `D⁺_QCoh(𝒪_Z)`. -/
theorem affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus
    [IsClosedImmersion (Spec.map φ)] (hφ : PseudoCoherent (Spec.map φ))
    (L : DerivedCategory (ModuleCat.{u} A)) (hL : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf)
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        (Spec.map φ)).derivedSheafHomExactSupport.obj
          ((tilde.functor A).mapDerivedCategory.obj L)) :=
  Scheme.derivedCategoryBPlus_derivedSheafHomExactSupport_of_pushforward (Spec.map φ) _
    (isBoundedBelow_tilde_mapDerivedCategory_obj A L hL)
    ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
      (Spec.map φ)).derivedSheafHomExactSupportPushforwardNatIso.app _)
    (derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent A _
      (Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf (Spec.map φ) hφ) L hL).2

/-- **[Stacks, Tag 01I9] on derived categories.** Derived sheafification on `Spec B` followed by
derived pushforward along `Spec φ` is restriction of scalars along `φ` followed by derived
sheafification on `Spec A`.

Pushforward along a closed immersion and both sheafification functors are exact, so the
underived identification `AlgebraicGeometry.pushforwardTildeIso` of [Stacks, Tag 01I9] descends
through the localizations defining the derived categories. The two spellings of pushforward of
sheaves of modules — the scheme-level `AlgebraicGeometry.Scheme.Modules.pushforward`, in which
[Stacks, Tag 01I9] is stated, and the ringed-space level
`RingedSpaceModuleAdjunction.modulePushforward`, in which the exact-support adjunction is — are
the same functor; the statement uses the second, and `e` below is where they meet. -/
def affineDerivedPushforwardTildeIso [IsClosedImmersion (Spec.map φ)] :
    (tilde.functor B).mapDerivedCategory ⋙
        (modulePushforward (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).i).mapDerivedCategory ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙
        (tilde.functor A).mapDerivedCategory :=
  let e : (tilde.functor B).mapDerivedCategory ⋙
      (Scheme.Modules.pushforward (Spec.map φ)).mapDerivedCategory ≅
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙
          (tilde.functor A).mapDerivedCategory :=
    CategoryTheory.Functor.mapDerivedCategoryCompIso (pushforwardTildeIso A B φ) ≪≫
      (CategoryTheory.Functor.mapDerivedCategoryCompIso
        (Iso.refl (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor A))).symm
  e

/-- **The comparison map of part (2) of [Stacks, Tag 0A78].** For a closed immersion
`i : Spec B ⟶ Spec A`, the natural transformation

`(R Hom_A(B, L))^~  ⟶  R ℰom(𝒪_{Spec B}, L^~)`

adjoint, under the adjunction `Ri_* ⊣ R ℰom(𝒪_{Spec B}, -)` of [Stacks, Tag 0A76], to the
composite

`Ri_*((R Hom_A(B, L))^~)  ≅  (R Hom_A(B, L))^~  ⟶  L^~`

whose first map is [Stacks, Tag 01I9] on derived categories and whose second is the
sheafification of the counit of the adjunction of [Stacks, Tag 0A70]. It is assembled from the
unit of the first adjunction, that identification and the counit of the second, so its
naturality is theirs.

The adjunction of [Stacks, Tag 0A70] is `Classical.choice` of
`Dualizing.restrictScalarsDerived_adj_derivedHom`, which proves that one exists. -/
def affineDerivedSheafHomComparison [IsClosedImmersion (Spec.map φ)] :
    _root_.Dualizing.derivedHom.{u, u, u} φ.hom ⋙ (tilde.functor B).mapDerivedCategory ⟶
      (tilde.functor A).mapDerivedCategory ⋙
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).derivedSheafHomExactSupport :=
  CategoryTheory.Functor.whiskerLeft
      (_root_.Dualizing.derivedHom.{u, u, u} φ.hom ⋙ (tilde.functor B).mapDerivedCategory)
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction.unit ≫
    CategoryTheory.Functor.whiskerLeft (_root_.Dualizing.derivedHom.{u, u, u} φ.hom)
      (CategoryTheory.Functor.whiskerRight (affineDerivedPushforwardTildeIso A B φ).hom
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).derivedSheafHomExactSupport) ≫
    CategoryTheory.Functor.whiskerRight
      (Classical.choice
        (_root_.Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} φ.hom)).counit
      ((tilde.functor A).mapDerivedCategory ⋙
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).derivedSheafHomExactSupport)

/-- The components of the comparison map of part (2) of [Stacks, Tag 0A78]: at `L` it is the map
adjoint to [Stacks, Tag 01I9] followed by the sheafified counit of [Stacks, Tag 0A70]. -/
theorem affineDerivedSheafHomComparison_app [IsClosedImmersion (Spec.map φ)]
    (L : DerivedCategory (ModuleCat.{u} A)) :
    (affineDerivedSheafHomComparison A B φ).app L =
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _)
        ((affineDerivedPushforwardTildeIso A B φ).hom.app
            ((_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L) ≫
          (tilde.functor A).mapDerivedCategory.map ((Classical.choice
            (_root_.Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} φ.hom)).counit.app
              L)) := by
  let adj := Classical.choice
    (_root_.Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} φ.hom)
  refine Eq.trans ?_ (Adjunction.homEquiv_unit
    (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
      (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction _ _ _).symm
  exact (congrArg (fun z => (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction.unit.app
          ((tilde.functor B).mapDerivedCategory.obj
            ((_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L)) ≫ z)
    (CategoryTheory.Functor.map_comp
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        (Spec.map φ)).derivedSheafHomExactSupport
      ((affineDerivedPushforwardTildeIso A B φ).hom.app
        ((_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L))
      ((tilde.functor A).mapDerivedCategory.map (adj.counit.app L)))).symm

/-- **The comparison map, tested against a sheafified object.** Composing the comparison of
part (2) of [Stacks, Tag 0A78] with the sheafification of a map `g : T ⟶ R Hom_A(B, L)` of `D(B)`
gives the map adjoint to the image of `g` under [Stacks, Tag 0A70] and [Stacks, Tag 01I9].

This is what makes the comparison an isomorphism: the right-hand side is a composite of
bijections in `g`. -/
theorem map_comp_affineDerivedSheafHomComparison_app [IsClosedImmersion (Spec.map φ)]
    (L : DerivedCategory (ModuleCat.{u} A)) (T : DerivedCategory (ModuleCat.{u} B))
    (g : T ⟶ (_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L) :
    (tilde.functor B).mapDerivedCategory.map g ≫
        (affineDerivedSheafHomComparison A B φ).app L =
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _)
        ((affineDerivedPushforwardTildeIso A B φ).hom.app T ≫
          (tilde.functor A).mapDerivedCategory.map (((Classical.choice
            (_root_.Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} φ.hom)).homEquiv
              T L).symm g)) := by
  let adj := Classical.choice
    (_root_.Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} φ.hom)
  have hnat : (modulePushforward (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).i).mapDerivedCategory.map
        ((tilde.functor B).mapDerivedCategory.map g) ≫
      (affineDerivedPushforwardTildeIso A B φ).hom.app
        ((_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L) =
      (affineDerivedPushforwardTildeIso A B φ).hom.app T ≫
        (tilde.functor A).mapDerivedCategory.map
          ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map g) :=
    (affineDerivedPushforwardTildeIso A B φ).hom.naturality g
  have h : (modulePushforward (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
          (Spec.map φ)).i).mapDerivedCategory.map
        ((tilde.functor B).mapDerivedCategory.map g) ≫
      ((affineDerivedPushforwardTildeIso A B φ).hom.app
          ((_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L) ≫
        (tilde.functor A).mapDerivedCategory.map (adj.counit.app L)) =
      (affineDerivedPushforwardTildeIso A B φ).hom.app T ≫
        (tilde.functor A).mapDerivedCategory.map ((adj.homEquiv T L).symm g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (tilde.functor A).mapDerivedCategory.map
            (adj.counit.app L)) hnat).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (affineDerivedPushforwardTildeIso A B φ).hom.app T ≫ z)
              (CategoryTheory.Functor.map_comp (tilde.functor A).mapDerivedCategory
                ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map g)
                (adj.counit.app L)).symm).trans
            (congrArg (fun z => (affineDerivedPushforwardTildeIso A B φ).hom.app T ≫
                (tilde.functor A).mapDerivedCategory.map z)
              (Adjunction.homEquiv_counit adj T L g).symm))))
  refine Eq.trans (congrArg (fun z => (tilde.functor B).mapDerivedCategory.map g ≫ z)
    (affineDerivedSheafHomComparison_app A B φ L)) ?_
  exact Eq.trans
    (Adjunction.homEquiv_naturality_left
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction
      ((tilde.functor B).mapDerivedCategory.map g) _).symm
    (congrArg _ h)

/-- **Stacks Project, Tag 0A78, part (2).** Let `φ : A ⟶ B` be a ring map whose spectrum is a
pseudo-coherent closed immersion `i : Z = Spec B ⟶ X = Spec A`, and let `L` be a bounded-below
object of `D(A)`. Then the comparison map of `affineDerivedSheafHomComparison` is invertible at
`L`:

`(R Hom_A(B, L))^~  ≅  R ℰom(𝒪_Z, L^~)`.

This is the commutativity of the square of part (2): the derived sheafification functors
`D⁺(A) ⥤ D⁺_QCoh(𝒪_X)` and `D⁺(B) ⥤ D⁺_QCoh(𝒪_Z)` intertwine `R Hom_A(B, -)` with
`R ℰom(𝒪_Z, -)`.

By the affine case of part (1), `affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus`, the
target has quasi-coherent cohomology sheaves, so it is the derived sheafification of an object
`N` of `D(B)`, and the comparison is the sheafification of a map `ψ` into `N`. For every `T` in
`D(B)`, composition with `ψ` is, by `map_comp_affineDerivedSheafHomComparison_app`, the composite
of the adjunction bijection of [Stacks, Tag 0A70], full faithfulness of derived sheafification on
`Spec A`, composition with an isomorphism, and the adjunction bijection of [Stacks, Tag 0A76]. So
`ψ` is an isomorphism by Yoneda, and hence so is the comparison. -/
@[stacks 0A78 "part (2)"]
theorem isIso_affineDerivedSheafHomComparison_app [IsClosedImmersion (Spec.map φ)]
    (hφ : PseudoCoherent (Spec.map φ))
    (L : DerivedCategory (ModuleCat.{u} A)) (hL : DerivedCategoryB.IsBoundedBelow L) :
    IsIso ((affineDerivedSheafHomComparison A B φ).app L) := by
  let adj := Classical.choice
    (_root_.Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} φ.hom)
  obtain ⟨hA⟩ : Nonempty ((tilde.functor A).mapDerivedCategory.FullyFaithful) :=
    ⟨StandardModel.mapDerivedCategoryFullyFaithful A⟩
  obtain ⟨hB⟩ : Nonempty ((tilde.functor B).mapDerivedCategory.FullyFaithful) :=
    ⟨StandardModel.mapDerivedCategoryFullyFaithful B⟩
  obtain ⟨N, ⟨eN⟩⟩ := StandardModel.exists_iso_mapDerivedCategory B
    ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
      (Spec.map φ)).derivedSheafHomExactSupport.obj
        ((tilde.functor A).mapDerivedCategory.obj L))
    (affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus A B φ hφ L hL).2
  have hmap := hB.map_preimage
    ((affineDerivedSheafHomComparison A B φ).app L ≫ eN.inv)
  have hψ : IsIso (hB.preimage
      ((affineDerivedSheafHomComparison A B φ).app L ≫ eN.inv)) := by
    refine isIso_of_yoneda_map_bijective _ (fun T => ?_)
    let e₃ : ((tilde.functor A).mapDerivedCategory.obj
          ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj T) ⟶
            (tilde.functor A).mapDerivedCategory.obj L) ≃
        ((modulePushforward (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
            (Spec.map φ)).i).mapDerivedCategory.obj
              ((tilde.functor B).mapDerivedCategory.obj T) ⟶
            (tilde.functor A).mapDerivedCategory.obj L) :=
      { toFun := fun v => ((affineDerivedPushforwardTildeIso A B φ).app T).hom ≫ v
        invFun := fun w => ((affineDerivedPushforwardTildeIso A B φ).app T).inv ≫ w
        left_inv := fun v => Iso.inv_hom_id_assoc _ v
        right_inv := fun w => Iso.hom_inv_id_assoc _ w }
    let e₂ : ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj T ⟶ L) ≃
        ((tilde.functor A).mapDerivedCategory.obj
            ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj T) ⟶
          (tilde.functor A).mapDerivedCategory.obj L) :=
      { toFun := fun u => (tilde.functor A).mapDerivedCategory.map u
        invFun := fun v => hA.preimage v
        left_inv := fun u => hA.preimage_map u
        right_inv := fun v => hA.map_preimage v }
    let e₆ : ((tilde.functor B).mapDerivedCategory.obj T ⟶
          (tilde.functor B).mapDerivedCategory.obj N) ≃ (T ⟶ N) :=
      { toFun := fun w => hB.preimage w
        invFun := fun v => (tilde.functor B).mapDerivedCategory.map v
        left_inv := fun w => hB.map_preimage w
        right_inv := fun v => hB.preimage_map v }
    let e₅ : ((tilde.functor B).mapDerivedCategory.obj T ⟶
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
            (Spec.map φ)).derivedSheafHomExactSupport.obj
              ((tilde.functor A).mapDerivedCategory.obj L)) ≃
        ((tilde.functor B).mapDerivedCategory.obj T ⟶
          (tilde.functor B).mapDerivedCategory.obj N) :=
      { toFun := fun w => w ≫ eN.inv
        invFun := fun w => w ≫ eN.hom
        left_inv := fun w => (Category.assoc w eN.inv eN.hom).trans
          ((congrArg (fun z => w ≫ z) eN.inv_hom_id).trans (Category.comp_id w))
        right_inv := fun w => (Category.assoc w eN.hom eN.inv).trans
          ((congrArg (fun z => w ≫ z) eN.hom_inv_id).trans (Category.comp_id w)) }
    have hfun : (fun (x : T ⟶ (_root_.Dualizing.derivedHom.{u, u, u} φ.hom).obj L) =>
          x ≫ hB.preimage
            ((affineDerivedSheafHomComparison A B φ).app L ≫ eN.inv)) =
        (adj.homEquiv T L).symm.trans (e₂.trans (e₃.trans
          (((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
            (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
              ((tilde.functor B).mapDerivedCategory.obj T)
              ((tilde.functor A).mapDerivedCategory.obj L)).trans
            (e₅.trans e₆)))) := by
      funext g
      refine hB.map_injective ?_
      refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _) ?_
      refine Eq.trans
        (congrArg (fun z => (tilde.functor B).mapDerivedCategory.map g ≫ z) hmap) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun z => z ≫ eN.inv)
        (map_comp_affineDerivedSheafHomComparison_app A B φ L T g)) ?_
      exact (hB.map_preimage (((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
            (Spec.map φ)).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
              ((tilde.functor B).mapDerivedCategory.obj T)
              ((tilde.functor A).mapDerivedCategory.obj L))
          ((affineDerivedPushforwardTildeIso A B φ).hom.app T ≫
            (tilde.functor A).mapDerivedCategory.map ((adj.homEquiv T L).symm g)) ≫
        eN.inv)).symm
    rw [hfun]
    exact Equiv.bijective _
  have hfac : (affineDerivedSheafHomComparison A B φ).app L =
      (tilde.functor B).mapDerivedCategory.map (hB.preimage
        ((affineDerivedSheafHomComparison A B φ).app L ≫ eN.inv)) ≫ eN.hom :=
    ((Category.assoc _ eN.inv eN.hom).trans
        ((congrArg (fun z => (affineDerivedSheafHomComparison A B φ).app L ≫ z)
            eN.inv_hom_id).trans
          (Category.comp_id ((affineDerivedSheafHomComparison A B φ).app L)))).symm.trans
      (congrArg (fun z => z ≫ eN.hom) hmap).symm
  rw [hfac]
  infer_instance

/-- **Stacks Project, Tag 0A78, part (2), the locally Noetherian case.** For *every* closed
immersion `Spec B ⟶ Spec A` with `Spec A` locally Noetherian, the comparison map of
`affineDerivedSheafHomComparison` is invertible at every bounded-below object of `D(A)`: a closed
immersion is locally of finite type, hence pseudo-coherent over a locally Noetherian target by
[Stacks, Tag 0684]. -/
@[stacks 0A78 "part (2) for a locally Noetherian target"]
theorem isIso_affineDerivedSheafHomComparison_app_of_noetherian
    [IsLocallyNoetherian (Spec A)] [IsClosedImmersion (Spec.map φ)]
    (L : DerivedCategory (ModuleCat.{u} A)) (hL : DerivedCategoryB.IsBoundedBelow L) :
    IsIso ((affineDerivedSheafHomComparison A B φ).app L) :=
  isIso_affineDerivedSheafHomComparison_app A B φ
    ((pseudoCoherent_iff_locallyOfFiniteType (Spec.map φ)).2 inferInstance) L hL

end AlgebraicGeometry

end
