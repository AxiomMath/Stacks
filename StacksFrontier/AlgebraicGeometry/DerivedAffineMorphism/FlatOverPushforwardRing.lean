module

public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Flat
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.QuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.RingedSpaceOverPushforwardRing
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `g` is flat, and `Lg^*` is the quasi-inverse candidate of [Stacks, Tag 0AVW]

Let `f : X ⟶ S` be an affine morphism of schemes and let
`g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)` be the morphism of ringed spaces of
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/RingedSpaceOverPushforwardRing.lean`, whose
derived pushforward `Rg_*` **is** the functor `Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)` of [Stacks, Tag 0AVW].
This file carries out the first half of the source's proof of that tag:

* `g` is a **flat** morphism of ringed spaces;
* hence `g^*` is **exact**, and the derived pullback `Lg^*` exists with no resolving datum left
  over and is computed degreewise;
* `Lg^* ⊣ Φ`;
* `H^i(Lg^* M) ≅ g^*(H^i M)`, so `Lg^*` carries `D_QCoh(f_* 𝒪_X)` into `D_QCoh(𝒪_X)`.

Those are exactly the source's sentences "*Then `g` is a flat morphism of ringed spaces … and
`Φ` is the restriction of `Rg_*`. We claim that `Lg^*` is a quasi-inverse. First, observe that
`Lg^*` sends `D_QCoh(f_*𝒪_X)` into `D_QCoh(𝒪_X)` because `g^*` transforms quasi-coherent modules
into quasi-coherent modules … Hence `g^*` is exact and `H^i(Lg^*M) = g^*H^i(M)`*".

## Main definitions

All in the namespace `Stacks.AlgebraicGeometry.DerivedAffinePushforward`.

* `derivedPullbackOverRing` — `Lg^* : D(f_* 𝒪_X) ⥤ D(𝒪_X)`.
* `derivedPullbackPushforwardAdjunctionOverRing` — the adjunction `Lg^* ⊣ Φ`.

## Main results

* `stalkMap_toPushforwardStructureSpace` — the stalk map of `g` **is**
  `TopCat.Presheaf.stalkPushforward`, the structure map of `g` being the identity.
* `isFlat_toPushforwardStructureSpace` — **`g` is flat**, by
  `AlgebraicGeometry.flat_stalkPushforward_of_isAffineHom`.
* `modulePullback_toPushforwardStructureSpace` — `g^*` **is**
  `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules f`, the quasi-inverse
  `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of [Stacks, Tag 01SB]; the two are equal, not merely isomorphic.
* `preservesFiniteLimits_modulePullback_toPushforwardStructureSpace` and
  `preservesFiniteColimits_modulePullback_toPushforwardStructureSpace` — **`g^*` is exact**.
* `derivedPullbackOverRingIsoMapDerivedCategory` — `Lg^*` is the functor `g^*` induces on derived
  categories, so it is computed degreewise.
* `homologyDerivedPullbackOverRingIso` — `H^i(Lg^* M) ≅ g^*(H^i M)`.
* `isQuasicoherent_homologyFunctor_derivedPullbackOverRing_of_isAffineHom` — **`Lg^*` carries
  `D_QCoh(f_* 𝒪_X)` into `D_QCoh(𝒪_X)`**.

## Implementation notes

*What this file removes from the library's own account of [Stacks, Tag 0AVW].* The module
docstrings of `DerivedPushforwardOverPushforwardRing.lean` and of
`RingedSpaceOverPushforwardRing.lean` named three inputs for the tag's equivalence clause as
unavailable: the flatness of `g`, i.e. the stalks of `f_* 𝒪_X`; a resolving datum for `Lg^*`;
and [Stacks, Tag 01BG], that `g^*` preserves quasi-coherence. The first is
`isFlat_toPushforwardStructureSpace` below. The second is not needed at all once the first is
available — `derivedPullbackPushforwardAdjunctionOfExact` consumes exactness of `g^*` and leaves
no datum — and the third was already in the library as
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`, which is a
statement about `pullbackModules f`, equal to `g^*` by
`modulePullback_toPushforwardStructureSpace`.

*What is still owed for the tag.* The unit `M ⟶ Φ(Lg^* M)` and the counit `Lg^* Φ(K) ⟶ K` are
not shown here to be invertible on the quasi-coherent derived categories. Their abelian
counterparts are available and unconditional —
`Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent` and
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_of_isQuasicoherent` — and the
adjunction whose unit and counit those are is `pullbackPushforwardAdjunction f`, which is the
abelian adjunction `g^* ⊣ g_*` underlying the derived one. What is between the two is the
identification of `H^i` of the derived unit with the abelian unit at `H^i`, for which the
natural isomorphism `H^i ∘ Φ ≅ g_* ∘ H^i` on `D_QCoh(𝒪_X)` is needed; the library has its
`Rf_*` form objectwise and at a pinned model
(`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso`) but not
over `f_* 𝒪_X` and not naturally.

*The stalk map is compared germ by germ.* `AlgebraicGeometry.PresheafedSpace.Hom.stalkMap` is
`(stalkFunctor _).map g.c ≫ stalkPushforward`, and with `g.c = 𝟙` the first factor is an
identity — but rewriting `g.c` to `𝟙` inside the `stalkFunctor` leaves a term the elaborator
rejects, the identity being typed at `(S, f_* 𝒪_X)`'s sheaf of rings and the target at `S`'s.
`TopCat.Presheaf.stalk_hom_ext` avoids the question: both maps are determined by their germs,
and on germs `AlgebraicGeometry.PresheafedSpace.stalkMap_germ` and
`TopCat.Presheaf.stalkPushforward_germ` give the same answer.

*The exactness statements are instances* because the statement of
`derivedPullbackOverRingIsoMapDerivedCategory` mentions
`CategoryTheory.Functor.mapDerivedCategory`, whose type requires them.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.AffineQcohPushforward

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### `g` is flat -/

/-- **The stalk map of `g` is `TopCat.Presheaf.stalkPushforward`.**  The structure map of
`g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)` is the identity, so nothing is left of the first factor of
`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`.  Compared germ by germ, where the two sides
are `AlgebraicGeometry.PresheafedSpace.stalkMap_germ` and
`TopCat.Presheaf.stalkPushforward_germ`. -/
theorem stalkMap_toPushforwardStructureSpace (x : X) :
    (toPushforwardStructureSpace f).hom.stalkMap x =
      X.presheaf.stalkPushforward CommRingCat f.base x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [AlgebraicGeometry.PresheafedSpace.stalkMap_germ]
  exact (Category.id_comp _).trans
    (TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base X.presheaf U x hU).symm

/-- **`g` is a flat morphism of ringed spaces**, for `f` affine.  This is the flatness asserted
in the proof of [Stacks, Tag 0AVW]: at a point `x` of `X` over `s = f x`, the stalk `𝒪_{X, x}`
is a further localization of `(f_* 𝒪_X)_s` and so flat over it. -/
theorem isFlat_toPushforwardStructureSpace [IsAffineHom f] :
    AlgebraicGeometry.IsFlat (toPushforwardStructureSpace f) := fun x => by
  rw [AlgebraicGeometry.IsFlatAt, stalkMap_toPushforwardStructureSpace f x]
  exact AlgebraicGeometry.flat_stalkPushforward_of_isAffineHom f x

/-! ### `g^*` and its exactness -/

/-- **`g^*` is the quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of [Stacks, Tag 01SB].**  Both are
`CategoryTheory.SheafOfModules.pullback` of the identity of `f_* 𝒪_X`, so the two functors
`Mod(f_* 𝒪_X) ⥤ Mod(𝒪_X)` are equal and not merely isomorphic.  This is the counterpart for
inverse image of `modulePushforward_toPushforwardStructureSpace`. -/
theorem modulePullback_toPushforwardStructureSpace :
    RingedSpaceModuleAdjunction.modulePullback (toPushforwardStructureSpace f) =
      Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules f :=
  rfl

/-- **`g^*` is left exact**, for `f` affine: `g` is flat, and inverse image of sheaves of modules
along a flat morphism of ringed spaces preserves finite limits. -/
@[sga "6 VI 2.3.1" "more general"]
instance preservesFiniteLimits_modulePullback_toPushforwardStructureSpace [IsAffineHom f] :
    PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)) :=
  RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
    (isFlat_toPushforwardStructureSpace f)

/-- **`g^*` is right exact**, unconditionally: it is a left adjoint. -/
instance preservesFiniteColimits_modulePullback_toPushforwardStructureSpace :
    PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)) :=
  haveI := RingedSpaceModuleAdjunction.preservesColimits_modulePullback
    (toPushforwardStructureSpace f)
  inferInstance

/-! ### `Lg^*`, and the adjunction `Lg^* ⊣ Φ` -/

section Derived

open scoped Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable [IsAffineHom f]
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]

/-- **The derived pullback along `g` exists with no resolving datum left over**: `g^*` is exact,
so the class of all objects of the homotopy category is a resolving datum for it. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_toPushforwardStructureSpace :
    (pullbackOnHomotopy (toPushforwardStructureSpace f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing (pushforwardStructureSpace f))) (ComplexShape.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact (toPushforwardStructureSpace f)

/-- **`Lg^* : D(f_* 𝒪_X) ⥤ D(𝒪_X)`**, the derived pullback along
`g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`.  This is the functor the source of [Stacks, Tag 0AVW] offers as
the quasi-inverse of `Φ`. -/
abbrev derivedPullbackOverRing :
    DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) ⥤
      DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  derivedPullback (toPushforwardStructureSpace f)

/-- **The adjunction `Lg^* ⊣ Φ`.**  `Φ` *is* `Rg_*` by
`derivedPushforwardOverRing_eq_derivedPushforward`, and the derived adjunction of
[Stacks, Tag 079W] for a morphism of ringed spaces along which degreewise pullback is exact
takes no resolving datum. -/
def derivedPullbackPushforwardAdjunctionOverRing :
    derivedPullbackOverRing.{w} f ⊣ derivedPushforwardOverRing.{w} f :=
  derivedPullbackPushforwardAdjunctionOfExact (toPushforwardStructureSpace f)

/-- **`Lg^*` is computed degreewise**: it is the functor `g^*` induces on derived categories,
`g^*` being exact.  Both are left derived functors of degreewise pullback, so they agree by the
uniqueness of left derived functors. -/
def derivedPullbackOverRingIsoMapDerivedCategory :
    (RingedSpaceModuleAdjunction.modulePullback
        (toPushforwardStructureSpace f)).mapDerivedCategory ≅
      derivedPullbackOverRing.{w} f :=
  let P := RingedSpaceModuleAdjunction.modulePullback (toPushforwardStructureSpace f)
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u}
    (structureSheafRing (pushforwardStructureSpace f))) (ComplexShape.up ℤ)
  haveI : P.mapDerivedCategory.IsLeftDerivedFunctor P.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W P.mapDerivedCategory P.mapDerivedCategoryFactorsh
  Functor.leftDerivedUnique
    ((pullbackOnHomotopy (toPushforwardStructureSpace f)).totalLeftDerived DerivedCategory.Qh W)
    P.mapDerivedCategory P.mapDerivedCategoryFactorsh.hom
    ((pullbackOnHomotopy (toPushforwardStructureSpace f)).totalLeftDerivedCounit
      DerivedCategory.Qh W) W

/-- **`H^i(Lg^* M) ≅ g^*(H^i M)`.**  `Lg^*` is computed degreewise by
`derivedPullbackOverRingIsoMapDerivedCategory`, and an exact functor's induced functor on
derived categories commutes with cohomology. -/
def homologyDerivedPullbackOverRingIso (i : ℤ)
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
        ((derivedPullbackOverRing.{w} f).obj M) ≅
      (Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules f).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M) :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).mapIso
      ((derivedPullbackOverRingIsoMapDerivedCategory.{w} f).app M).symm ≪≫
    ((RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).mapDerivedCategoryCompHomologyFunctorIso i).app M

/-- **`Lg^*` carries `D_QCoh(f_* 𝒪_X)` into `D_QCoh(𝒪_X)`.**  Let `f` be affine and let `M` have
quasi-coherent cohomology sheaves over `f_* 𝒪_X`.  Then the cohomology sheaves of `Lg^* M` are
quasi-coherent `𝒪_X`-modules.

They are `g^*` of the cohomology sheaves of `M` by `homologyDerivedPullbackOverRingIso`, and
`g^*` preserves quasi-coherence by [Stacks, Tag 01BG] in the form
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`. -/
theorem isQuasicoherent_homologyFunctor_derivedPullbackOverRing_of_isAffineHom
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
      ((derivedPullbackOverRing.{w} f).obj M)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (homologyDerivedPullbackOverRingIso.{w} f i M).symm
    (Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules f _ (hcoh i))

end Derived

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
