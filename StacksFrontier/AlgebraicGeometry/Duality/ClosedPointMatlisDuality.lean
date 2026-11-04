module

public import StacksFrontier.RingTheory.Dualizing.RegularLocalFiniteLengthDuality
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentSitePerfect
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.RingCatStalkFiniteLength
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityAtAPerfectObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.SupportFromRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedIsomorphismTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk
public import StacksFrontier.Topology.Sheaves.Modules.UnitStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectDerivedHomStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroStrictModel
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge

/-!
# Duality for a coherent module supported at a closed point of a regular scheme

Let `k` be a field, `X` a scheme of finite type over `k` which is regular, `x ∈ X` a closed
point, `F` a coherent `𝒪_X`-module supported at `x` and `F'` a coherent `𝒪_X`-module supported
at `x` whose stalk at `x` is a Matlis dual of `F_x`. Then, with `d_x = dim 𝒪_{X,x}`,

`Hom_X(F, M) = H⁰(X, M ⊗^𝐋_{𝒪_X} F'[-d_x])`

functorially in `M`. This is [stacks 0G02].

## Main definitions

* `Dualizing.IsMatlisDualPair` — "`N'` is a Matlis dual of `N`" as a relation between two modules
  over a local ring, rather than as the four pieces of data an injective hull carries.

## Main results

* `Dualizing.exists_ringKrullDim_eq_and_nonempty_derivedHom_single_self_iso_matlisDual` — the
  local input: `RHom_A(N, A) ≅ N'[-d]` over a regular local ring `A`, with the shift `d` pinned to
  the dimension of `A`.
* `AlgebraicGeometry.nonempty_derivedStalk_derivedSheafHom_unit_iso_of_nearModel` — the stalk of
  the derived dual, `R𝓗om_{𝒪_X}(F, 𝒪_X)_x ≅ RHom_{𝒪_{X,x}}(F_x, 𝒪_{X,x})`, from a complex
  representing `F` which is strictly perfect on one neighbourhood of `x`.
* `AlgebraicGeometry.exists_ringKrullDim_eq_and_nonempty_derivedSheafHom_unit_iso` — the derived
  dual itself: `R𝓗om_{𝒪_X}(F, 𝒪_X) ≅ F'[-d_x]` in `D(𝒪_X)`.
* `AlgebraicGeometry.exists_ringKrullDim_eq_and_homAddEquiv_homologyDerivedTensor` —
  **[stacks 0G02]**, the duality and its functoriality in `M`.

## Implementation notes

**The shape of the proof.** `F` placed in degree zero is a perfect object of `D(𝒪_X)`
([stacks 0FDC] at the ringed site of opens,
`AlgebraicGeometry.isPerfect_singleFunctor_of_isCoherent_of_isRegular`), so the sheaf-theoretic
duality `AlgebraicGeometry.RingedSite.homAddEquivHomologyDerivedTensorOfDual` — which is
[stacks 08JJ] (3) at a perfect object followed by [stacks 08JA] — delivers the conclusion and
its functoriality from a *single* isomorphism `R𝓗om_{𝒪_X}(F, 𝒪_X) ≅ F'[-d_x]`, with no
naturality asked of it. That one isomorphism is where all the geometry goes, and it is produced
stalkwise: both sides have their cohomology supported on the closed point `{x}`
(`Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleton_derivedSheafHom_single`
and `AlgebraicGeometry.cohomologySupportedOn_shift`), and on objects so supported an isomorphism
of derived stalks at `x` is an isomorphism
(`Stacks.Cohomology.SupportedComplexes.isoOfRingCatDerivedStalkIsoOfSupported`). At the stalk the
isomorphism is [stacks 0GM8] case (1)
(`Stacks.SheafOfModules.DerivedHomStalk.derivedStalkDerivedSheafHomIsoNearPoint`) composed with
the local Matlis duality of `StacksFrontier.RingTheory.Dualizing.RegularLocalFiniteLengthDuality`,
which is the reduction target of the source's own proof.

**Two readings of the local ring.** The stalk functor on sheaves of modules takes its values in
modules over the `RingCat`-valued stalk of the sheaf of rings,
`Stacks.Cohomology.DerivedInternalHomStalk.stalkRing`, and that is the ring the derived internal
hom on stalks and `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` are written over; the
`CommRingCat`-valued stalk `𝒪_{X,x} = X.presheaf.stalk x` is the ring "dimension of the local
ring at `x`" is about. The two are isomorphic and not equal, by
`AlgebraicGeometry.ringCatStalkRingEquiv`; the local data of the statement below is therefore
phrased over the first and the dimension clause over the second, the single crossing being
`ringKrullDim_eq_of_ringEquiv`. Writing the local data over the second instead would require
crossing the derived internal hom itself, which is a change-of-rings statement
([stacks 0E1W]) rather than a transport of one object.

**Why the Matlis dual is a relation.** `Dualizing.IsMatlisDualPair` packages the injective hull
and the identification `N' ≅ Hom_A(N, E)` into one `Prop` with `A` a variable. At the stalk
ring, elaborating `IsLocalRing.ResidueField` and the module structure on `Hom_A(N, E)` afresh
fails — the `CommRing` instance on the `RingCat`-valued stalk is a transported one, so instance
search has two `Ring` paths on the carrier — whereas *applying* an already-elaborated predicate
only substitutes.

**The universe of the derived hom.** `derivedHomAdjunctionOverRing.{u, v, w}` is written with
`v = 0` throughout, as the local duality is. The abbreviation
`Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedHom` leaves `v` undetermined — the
constraint `max u v = u` has several solutions — and the instance it picks does not unify with
the one the local duality is stated at, so it is avoided here.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08Y2](https://stacks.math.columbia.edu/tag/08Y2)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (ringedSite)
open Stacks.Cohomology.DerivedInternalHomStalk (stalkRing derivedStalk stalkDerivedHom)
open Stacks.DerivedTensor.RingedSite (unitObject)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.DerivedInternalHomStalk.stalkCommRing

namespace Dualizing

/-! ### Matlis duality as a relation between two modules -/

/-- **`N'` is a Matlis dual of `N` over a local ring `A`**: there is an injective hull `E` of the
residue field of `A` with `N' ≅ Hom_A(N, E)`.

This is the relation the source asks of the two stalks: "choose a coherent module `F'` supported
at `x` such that `F_x` and `F'_x` are Matlis dual". It is stated as a relation, rather than as
the four separate pieces of data `(E, i, hi, hdual)`, so that it can be *applied* at a stalk
ring: the residue field and the module structure on `Hom_A(N, E)` are elaborated once here, with
`A` a variable, and the application only substitutes. At the two spellings of the stalk of a
structure sheaf, elaborating them afresh fails -- see the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk` on the two readings
of the stalk ring.

The injective hull is `Module.IsInjectiveHull` of [stacks 08Y2], and the residue field is lifted
to the module universe by `ModuleCat.uliftFunctor`, as in
`Dualizing.derivedHomFiniteLengthIsoMatlisDual`. -/
def IsMatlisDualPair (A : Type u) [CommRing A] [IsLocalRing A] (N N' : ModuleCat.{u} A) : Prop :=
  ∃ (E : ModuleCat.{u} A) (i : (ModuleCat.uliftFunctor.{0} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) (_ : Mono i),
    Module.IsInjectiveHull i ∧ Nonempty (N' ≅ ModuleCat.of A (N ⟶ E))

/-! ### The local input -/

/-- **The derived dual of a finite-length module over a regular local ring, with the shift
pinned to the dimension.** For `A` regular local, `N` of finite length and `N'` a Matlis dual of
`N`,

`RHom_A(N, A) ≅ N'[-d]`, `d = dim A`.

This is `Dualizing.nonempty_derivedHom_single_iso_matlisDual_shift` at the regular module,
together with
`Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift`, which
produces the normalizing shift of the regular module and identifies it with the dimension.
`Dualizing.exists_shift_derivedHom_single_self_iso_matlisDual` is the same statement with the
shift left unidentified and the Matlis dual given as data rather than as a relation. -/
theorem exists_ringKrullDim_eq_and_nonempty_derivedHom_single_self_iso_matlisDual
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (N N' : ModuleCat.{u} A) (hN : IsFiniteLength A N) (hdual : IsMatlisDualPair A N N') :
    ∃ d : ℕ, ringKrullDim A = (d : ℕ∞) ∧
      Nonempty
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1} A).hom.obj
            (op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N),
              (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N')⟦-(d : ℤ)⟧) := by
  obtain ⟨E, i, hmono, hi, hNN'⟩ := hdual
  obtain ⟨d, hdim, hω⟩ :=
    exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift A
  exact ⟨d, hdim, nonempty_derivedHom_single_iso_matlisDual_shift.{u, 0} A _ (d : ℤ)
    hω E i hi N N' hN hNN'⟩

end Dualizing

namespace AlgebraicGeometry

/-! ### The local ring at a point, in the spelling the stalk functor produces -/

/-- The stalk of the structure sheaf of a scheme, in the `RingCat` spelling, is a local ring:
it is isomorphic to `𝒪_{X,x}` by `AlgebraicGeometry.ringCatStalkRingEquiv`. -/
local instance isLocalRing_stalkRing (X : Scheme.{u}) (x : X) :
    IsLocalRing (stalkRing X.toRingedSpace x) :=
  (ringCatStalkRingEquiv (X := X) x).symm.isLocalRing

/-! ### The stalk of the derived dual, from a model strictly perfect near the point -/

/-- **The stalk at `x` of `R𝓗om_{𝒪_X}(F, 𝒪_X)` is `RHom_{𝒪_{X,x}}(F_x, 𝒪_{X,x})`**, given a
complex `E` representing `F` in degree zero which is bounded and whose terms are direct summands
of finite free modules on one open neighbourhood `V` of `x`.

This is Tag 0GM8 case (1), `Stacks.SheafOfModules.DerivedHomStalk`
`.derivedStalkDerivedSheafHomIsoNearPoint`, transported along the two identifications of
representatives: `qE` for the first variable, and
`CategoryTheory.DerivedCategory.singleFunctorIsoCompQ` for the structure sheaf in degree
zero. -/
theorem nonempty_derivedStalk_derivedSheafHom_unit_iso_of_nearModel
    (X : Scheme.{u}) (x : X) (V : Opens X) (hxV : x ∈ V) (F : X.Modules)
    (E : CochainComplex (Stacks.SheafOfModules.StructureSheafModules X.sheaf) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, ∃ r : ℕ, Nonempty (Retract ((E.X i).over V)
      (_root_.SheafOfModules.free (R := (_root_.structureSheaf X.sheaf).over V)
        (ULift.{u} (Fin r)))))
    (qE : DerivedCategory.Q.obj E ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F) :
    Nonempty
      ((derivedStalk X.toRingedSpace x).obj
          (((RingedSite.derivedSheafHomBifunctor (ringedSite X.sheaf)).obj
              (op ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj
            (unitObject (ringedSite X.sheaf))) ≅
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1}
            (stalkRing X.toRingedSpace x)).hom.obj
          (op ((derivedStalk X.toRingedSpace x).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F)),
            (derivedStalk X.toRingedSpace x).obj (unitObject (ringedSite X.sheaf)))) := by
  set G := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) with hG
  have qG : DerivedCategory.Q.obj G ≅ unitObject (ringedSite X.sheaf) :=
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).symm
  have key := Stacks.SheafOfModules.DerivedHomStalk.derivedStalkDerivedSheafHomIsoNearPoint
    X.sheaf E G hE x V hxV hterm
  have hbi : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op (DerivedCategory.Q.obj E))).obj (DerivedCategory.Q.obj G) ≅
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj
        (unitObject (ringedSite X.sheaf)) :=
    ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso qE.op).symm.app
        (DerivedCategory.Q.obj G) ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj F))).mapIso qG
  exact ⟨((derivedStalk X.toRingedSpace x).mapIso hbi).symm ≪≫ key ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1}
        (stalkRing X.toRingedSpace x)).hom.mapIso
      (Iso.prod ((derivedStalk X.toRingedSpace x).mapIso qE).op.symm
        ((derivedStalk X.toRingedSpace x).mapIso qG))⟩

/-! ### The derived dual of the module -/

/-- **The derived dual of a coherent module supported at a closed point of a regular scheme is
the shifted Matlis dual**: `R𝓗om_{𝒪_X}(F, 𝒪_X) ≅ F'[-d]` in `D(𝒪_X)`, with `d = dim 𝒪_{X,x}`.

Both sides have their cohomology supported on `{x}`, so it is enough to produce the isomorphism
of derived stalks at `x`. There it is Tag 0GM8 case (1) — available through the model of `F`
which `Stacks.Cohomology.ExtensionByZeroStrictModel.exists_boundedStrictModel_nearPoint`
produces, bounded and strictly perfect on one neighbourhood of `x` — composed with the local
Matlis duality over the regular local ring `𝒪_{X,x}`. -/
theorem exists_ringKrullDim_eq_and_nonempty_derivedSheafHom_unit_iso
    (X : Scheme.{u}) (hX : IsRegular X) (x : X) (hx : IsClosed ({x} : Set X))
    (F F' : X.Modules) [F.IsCoherent]
    (hFsupp : SheafOfModules.supp (R := X.ringCatSheaf) F ⊆ {x})
    (hF'supp : SheafOfModules.supp (R := X.ringCatSheaf) F' ⊆ {x})
    (hN : IsFiniteLength (stalkRing X.toRingedSpace x) (SheafOfModules.stalkObjStalkRing x F))
    (hdual : Dualizing.IsMatlisDualPair (stalkRing X.toRingedSpace x)
      (SheafOfModules.stalkObjStalkRing x F) (SheafOfModules.stalkObjStalkRing x F')) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = (d : ℕ∞) ∧
      Nonempty
        ((((RingedSite.derivedSheafHomBifunctor (ringedSite X.sheaf)).obj
              (op ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj
            (unitObject (ringedSite X.sheaf))) ≅
          ((DerivedCategory.singleFunctor X.Modules 0).obj F')⟦-(d : ℤ)⟧) := by
  let : IsRegularLocalRing (X.presheaf.stalk x : Type u) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
  let : IsRegularLocalRing (stalkRing X.toRingedSpace x) :=
    IsRegularLocalRing.of_ringEquiv (R := (X.presheaf.stalk x : Type u))
      (e := (ringCatStalkRingEquiv (X := X) x).symm)
  obtain ⟨V, hxV, E, hEb, hterm, ⟨qE⟩⟩ :=
    Stacks.Cohomology.ExtensionByZeroStrictModel.exists_boundedStrictModel_nearPoint x F hX hFsupp
  obtain ⟨d, hdim, ⟨μ⟩⟩ :=
    Dualizing.exists_ringKrullDim_eq_and_nonempty_derivedHom_single_self_iso_matlisDual
      (stalkRing X.toRingedSpace x) _ _ hN hdual
  obtain ⟨st⟩ := nonempty_derivedStalk_derivedSheafHom_unit_iso_of_nearModel X x V hxV F E
    hEb hterm qE
  refine ⟨d, ?_, ?_⟩
  · exact (ringKrullDim_eq_of_ringEquiv (ringCatStalkRingEquiv (X := X) x)).symm.trans hdim
  · have σ1 : (derivedStalk X.toRingedSpace x).obj (unitObject (ringedSite X.sheaf)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (stalkRing X.toRingedSpace x)) 0).obj
          (ModuleCat.of (stalkRing X.toRingedSpace x) (stalkRing X.toRingedSpace x)) :=
      SheafOfModules.derivedUnitStalkIso X.sheaf x
    have σ : ∀ G : X.Modules, (derivedStalk X.toRingedSpace x).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (stalkRing X.toRingedSpace x)) 0).obj
          (SheafOfModules.stalkObjStalkRing x G) := fun G =>
      ((SheafOfModules.stalkFunctor
        (structureSheafRing X.toRingedSpace) x).mapDerivedCategorySingleFunctor 0).app G
    have hz : ∀ G : X.Modules, SheafOfModules.supp (R := X.ringCatSheaf) G ⊆ {x} →
        ∀ y : X, y ∉ ({x} : Set X) → IsZero (TopCat.Presheaf.stalk (X := X) G.val.presheaf y) :=
      fun G hG y hy =>
      Stacks.Cohomology.ExtensionByZeroStrictModel.isZero_stalk_of_notMem_supp G
        (fun h => hy (hG h))
    have hsh : (derivedStalk X.toRingedSpace x).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj F')⟦-(d : ℤ)⟧) ≅
        ((derivedStalk X.toRingedSpace x).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F'))⟦-(d : ℤ)⟧ :=
      ((SheafOfModules.stalkFunctor
        (structureSheafRing X.toRingedSpace) x).mapDerivedCategory.commShiftIso (-(d : ℤ))).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj F')
    have ψ := st ≪≫ (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, 0, u + 1}
          (stalkRing X.toRingedSpace x)).hom.mapIso (Iso.prod (σ F).op.symm σ1) ≪≫ μ ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} (stalkRing X.toRingedSpace x)))
        (-(d : ℤ))).mapIso (σ F').symm ≪≫ hsh.symm
    refine ⟨Stacks.Cohomology.SupportedComplexes.isoOfRingCatDerivedStalkIsoOfSupported
      X.toRingedSpace x hx _ _ ?_ ?_ ψ⟩
    · exact
        Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleton_derivedSheafHom_single
          X.sheaf x hx F (hz F hFsupp) _
    · exact cohomologySupportedOn_shift _ _ (-(d : ℤ)) _
        (Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleFunctor_obj
          (_root_.structureSheaf X.sheaf) ({x} : Set X) 0 F' (hz F' hF'supp))

/-! ### Stacks 0G02 -/

/-- **Stacks 0G02.** Let `k` be a field, `X` a scheme of finite type over `k` which is regular,
`x ∈ X` a closed point, `F` a coherent `𝒪_X`-module supported at `x`, and `F'` a coherent
`𝒪_X`-module supported at `x` whose stalk at `x` is a Matlis dual of `F_x`. Then with
`d_x = dim 𝒪_{X,x}`,

`Hom_X(F, M) = H⁰(X, M ⊗^𝐋_{𝒪_X} F'[-d_x])`

functorially in `M`. -/
@[stacks 0G02 "the scheme-level statement: k a field, X a scheme of finite type over k which \
is regular, x a closed point of X, F a coherent 𝒪_X-module supported at x and F' a coherent \
𝒪_X-module supported at x whose stalk at x is a Matlis dual of F_x; then Hom_X(F, M) is \
identified additively with H⁰(X, M ⊗^L_{𝒪_X} F'[-d_x]), d_x = dim 𝒪_{X,x}, functorially in M.  \
The identification is produced for every M in D(𝒪_X), which generalizes the source's clause for \
M in D_perf(𝒪_X).  The local ring is read as the RingCat-valued stalk of the sheaf of rings, \
which is the local ring 𝒪_{X,x} by AlgebraicGeometry.ringCatStalkRingEquiv and is where the \
Matlis-duality hypothesis is stated; the dimension clause d_x = dim 𝒪_{X,x} is stated at the \
CommRingCat-valued stalk X.presheaf.stalk x.  The duality at the point to which the source's \
proof reduces this -- for A a regular local ring of dimension d, Hom_{D(A)}(N, K) is H⁰(K ⊗^L_A \
N'[-d]) functorially in K -- is registered separately, on \
Dualizing.exists_addEquiv_hom_homology_derivedTensor_matlisDual"]
theorem exists_ringKrullDim_eq_and_homAddEquiv_homologyDerivedTensor
    (k : Type u) [Field k] (X : Scheme.{u}) (sX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hX : IsRegular X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (F F' : X.Modules) [F.IsCoherent] [F'.IsCoherent]
    (hFsupp : SheafOfModules.supp (R := X.ringCatSheaf) F ⊆ {x})
    (hF'supp : SheafOfModules.supp (R := X.ringCatSheaf) F' ⊆ {x})
    (hdual : Dualizing.IsMatlisDualPair (stalkRing X.toRingedSpace x)
      (SheafOfModules.stalkObjStalkRing x F) (SheafOfModules.stalkObjStalkRing x F')) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = (d : ℕ∞) ∧
      ∃ e : ∀ M : DerivedCategory X.Modules,
          ((DerivedCategory.singleFunctor X.Modules 0).obj F ⟶ M) ≃+
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
              ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
                  (ringedSite X.sheaf)).obj
                (((Stacks.SheafOfModules.derivedTensorProductFunctor
                    (ringedSite X.sheaf)).obj M).obj
                  (((DerivedCategory.singleFunctor X.Modules 0).obj F')⟦-(d : ℤ)⟧))) : Type u),
        ∀ (M N : DerivedCategory X.Modules) (g : M ⟶ N)
            (a : (DerivedCategory.singleFunctor X.Modules 0).obj F ⟶ M),
          e N (a ≫ g) =
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
                  (ringedSite X.sheaf)).map
                (((Stacks.SheafOfModules.derivedTensorProductFunctor
                    (ringedSite X.sheaf)).map g).app
                  (((DerivedCategory.singleFunctor X.Modules 0).obj F')⟦-(d : ℤ)⟧)))
              (e M a) := by
  let : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  have hN : IsFiniteLength (stalkRing X.toRingedSpace x)
      (SheafOfModules.stalkObjStalkRing x F) :=
    Stacks.Chow.isFiniteLength_stalkRing_of_supp_subset_singleton x F hFsupp
  have key := exists_ringKrullDim_eq_and_nonempty_derivedSheafHom_unit_iso X hX x hx F F'
    hFsupp hF'supp hN hdual
  obtain ⟨d, hdim, he⟩ := key
  obtain ⟨e⟩ := he
  have hperf : (ringedSite X.sheaf).IsPerfect
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
    isPerfect_singleFunctor_of_isCoherent_of_isRegular hX F
  refine ⟨d, hdim,
    RingedSite.homAddEquivHomologyDerivedTensorOfDual (ringedSite X.sheaf)
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)
      (((DerivedCategory.singleFunctor X.Modules 0).obj F')⟦-(d : ℤ)⟧) hperf e, ?_⟩
  intro M N g a
  exact RingedSite.homAddEquivHomologyDerivedTensorOfDual_naturality (ringedSite X.sheaf)
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)
    (((DerivedCategory.singleFunctor X.Modules 0).obj F')⟦-(d : ℤ)⟧) hperf e g a

end AlgebraicGeometry

end
