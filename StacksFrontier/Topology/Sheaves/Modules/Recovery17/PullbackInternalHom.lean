module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Homology.PseudoCoherent.HomFlat
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of internal Hom

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` and `G` be
modules on `Y`. If `F` is finitely presented and `f` is flat, then pullback
commutes with the internal Hom from `F` to `G`.

## Main definitions

* `Stacks.SheafHomPullback.PullbackSheafHomComparison` specifies the comparison by its action
  on local homomorphisms and pulled-back local sections.
* `Stacks.SheafHomPullback.pullbackSheafHomComparison` is the underlying morphism of this
  canonical comparison data.

## Main results

* `Stacks.SheafHomPullback.pullbackSheafHomComparison_isIso` says that this comparison is an
  isomorphism when its first argument is finitely presented and the morphism
  of ringed spaces is flat.

## Implementation notes

Internal Homs are represented by `SheafHom` packages. The comparison is stated
for arbitrary such packages, so it does not depend on a choice of model for
the internal Hom. Pullback is the canonical left adjoint
`RingedSpaceModuleAdjunction.modulePullback`. The comparison data includes the
equation `f^*φ(f^*t) = f^*(φ(t))` on every pair of nested opens. In particular,
the comparison is not an arbitrary morphism between the two Hom objects.

## References

* [Stacks Project, Tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafHomPullback

open RingedSpaceModuleAdjunction

private theorem finitePresentation_of_finite_linearPresentation
    {R M ι σ : Type u} [Ring R] [AddCommGroup M] [Module R M]
    [Finite ι] [Finite σ]
    (l : (ι →₀ R) →ₗ[R] M) (r : (σ →₀ R) →ₗ[R] LinearMap.ker l)
    (hl : Function.Surjective l) (hr : Function.Surjective r) :
    Module.FinitePresentation R M := by
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  exact Module.finitePresentation_of_free_of_surjective l hl
    (Module.Finite.iff_fg.mp (Module.Finite.of_surjective r hr))

private theorem finitePresentation_of_ringEquiv_linearPresentation
    {R S M N ι σ : Type u} [Ring R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Finite ι] [Finite σ]
    (e : R ≃+* S) (eM : M ≃+ N)
    (heM : ∀ (r : R) (m : M), eM (r • m) = e r • eM m)
    (l : (ι →₀ R) →ₗ[R] M)
    (r : (σ →₀ R) →ₗ[R] LinearMap.ker l)
    (hl : Function.Surjective l) (hr : Function.Surjective r) :
    Module.FinitePresentation S N := by
  classical
  let eι : (ι →₀ R) ≃+ (ι →₀ S) := Finsupp.mapRange.addEquiv e.toAddEquiv
  let eσ : (σ →₀ R) ≃+ (σ →₀ S) := Finsupp.mapRange.addEquiv e.toAddEquiv
  let lS : (ι →₀ S) →ₗ[S] N := {
    toFun := fun z => eM (l (eι.symm z))
    map_add' := by
      intro z w
      simp [eι, map_add]
    map_smul' := by
      intro a z
      have hc : eι.symm (a • z) = e.symm a • eι.symm z := by
        ext i
        simp [eι, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply,
          map_mul]
      show eM (l (eι.symm (a • z))) = a • eM (l (eι.symm z))
      rw [hc, map_smul, heM, e.apply_symm_apply] }
  let eKer : LinearMap.ker l ≃+ LinearMap.ker lS := {
    toFun := fun z => ⟨eι z.1, by
      show eM (l (eι.symm (eι z.1))) = 0
      rw [eι.symm_apply_apply]
      simp⟩
    invFun := fun z => ⟨eι.symm z.1,
      eM.injective ((show eM (l (eι.symm z.1)) = 0 from z.2).trans eM.map_zero.symm)⟩
    left_inv := fun z => Subtype.ext (eι.symm_apply_apply z.1)
    right_inv := fun z => Subtype.ext (eι.apply_symm_apply z.1)
    map_add' := fun z w => Subtype.ext (eι.map_add z.1 w.1) }
  let rS : (σ →₀ S) →ₗ[S] LinearMap.ker lS := {
    toFun := fun z => eKer (r (eσ.symm z))
    map_add' := by
      intro z w
      apply Subtype.ext
      show eι (r (eσ.symm (z + w))).1 =
        eι (r (eσ.symm z)).1 + eι (r (eσ.symm w)).1
      rw [eσ.symm.map_add, r.map_add]
      exact eι.map_add _ _
    map_smul' := by
      intro a z
      have hc : eσ.symm (a • z) = e.symm a • eσ.symm z := by
        ext i
        simp [eσ, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply,
          map_mul]
      apply Subtype.ext
      show eι ((r (eσ.symm (a • z))).1) = a • eι ((r (eσ.symm z)).1)
      rw [hc, r.map_smul]
      ext i
      simp [eσ, eι, Finsupp.mapRange.addEquiv_apply,
        Finsupp.mapRange_apply, map_mul] }
  have hlS : Function.Surjective lS := by
    intro n
    obtain ⟨m, hm⟩ := eM.surjective n
    obtain ⟨z, hz⟩ := hl m
    refine ⟨eι z, ?_⟩
    show eM (l (eι.symm (eι z))) = n
    simpa [hz] using hm
  have hrS : Function.Surjective rS := by
    intro z
    obtain ⟨w, hw⟩ := hr (eKer.symm z)
    refine ⟨eσ w, ?_⟩
    show eKer (r (eσ.symm (eσ w))) = z
    rw [eσ.symm_apply_apply, hw, eKer.apply_symm_apply]
  exact finitePresentation_of_finite_linearPresentation lS rS hlS hrS

private theorem moduleStalkFunctor_preservesFiniteLimits
    {X : TopCat.{u}}
    (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Limits.PreservesFiniteLimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor O x) := by
  let F := AlgebraicGeometry.SheafOfModules.stalkFunctor O x
  let G := forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x))
    AddCommGrpCat.{u}
  have hFG : Limits.PreservesFiniteLimits (F ⋙ G) := by
    let A := SheafOfModules.toSheaf O
    let B := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    show Limits.PreservesFiniteLimits (A ⋙ B)
    exact @Limits.comp_preservesFiniteLimits _ _ _ _ _ _ A B ⟨fun _ _ _ => inferInstance⟩
      (TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor
        (C := AddCommGrpCat.{u}) (FC := fun A B => A →+ B) (CC := fun A => A) x)
  exact Limits.preservesFiniteLimits_of_reflects_of_preserves F G

/-- Transport an identification with a finitely supported function space along a ring
isomorphism of the scalars. If `M` carries both an `R`- and an `S`-module structure whose
actions correspond under `e : R ≃+* S`, an `S`-linear identification `M ≃ₗ[S] (I →₀ S)`
becomes an `R`-linear identification `M ≃ₗ[R] (I →₀ R)`.

Mathlib's `Finsupp.mapRange.linearEquiv` transports the *value* module and leaves the scalars
alone, so it does not apply; the scalars are what move here. -/
private noncomputable def finsuppCongrScalars {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M]
    (hsmul : ∀ (a : R) (m : M), a • m = e a • m)
    {I : Type u} (f : M ≃ₗ[S] (I →₀ S)) :
    M ≃ₗ[R] (I →₀ R) where
  toFun z := Finsupp.mapRange.addEquiv e.symm.toAddEquiv (f z)
  invFun z := f.symm (Finsupp.mapRange.addEquiv e.toAddEquiv z)
  left_inv z := by
    apply f.injective
    ext j
    simp [Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply]
  right_inv z := by
    ext j
    simp [Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply]
  map_add' z w :=
    (congrArg (Finsupp.mapRange.addEquiv e.symm.toAddEquiv) (f.map_add z w)).trans
      ((Finsupp.mapRange.addEquiv e.symm.toAddEquiv).map_add _ _)
  map_smul' a z := by
    change Finsupp.mapRange.addEquiv e.symm.toAddEquiv (f (a • z)) =
      a • Finsupp.mapRange.addEquiv e.symm.toAddEquiv (f z)
    rw [hsmul a z, f.map_smul]
    ext j
    simp [Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply, map_mul]

/-- Compatibility of an additive equivalence with scalar actions transported along ring
isomorphisms. If `M` carries `R`- and `K`-actions identified by `e : R ≃+* K`, and `N` carries
`T`- and `K`-actions identified by `eT : K ≃+* T`, then a `K`-linear equivalence `M ≃ₗ[K] N` is
additive and `e.trans eT`-semilinear.

Stated over variable rings and a variable equivalence rather than at the concrete stalk types:
the identical argument at those types costs the elaborator two thirds of a heartbeat budget. -/
private theorem addEquiv_smul_of_compHom {R K T : Type u} [Ring R] [Ring K] [Ring T]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module K M] [Module T N] [Module K N]
    (e : R ≃+* K) (eT : K ≃+* T)
    (hM : ∀ (a : R) (m : M), a • m = e a • m)
    (hN : ∀ (c : K) (n : N), c • n = eT c • n)
    (eL : M ≃ₗ[K] N) (a : R) (m : M) :
    eL.toAddEquiv (a • m) = (e.trans eT) a • eL.toAddEquiv m := by
  show eL (a • m) = (e.trans eT) a • eL m
  rw [hM a m, eL.map_smul, hN (e a) (eL m)]
  rfl

/-- Finite presentation from surjections out of two free modules of finite rank, transported
along a ring isomorphism of the scalars. If `g : A →ₗ[K] B` is surjective, `ρ : C →ₗ[K] ker g`
is surjective, `A` and `C` are identified with `ι →₀ K` and `σ →₀ K` for finite `ι` and `σ`,
and `eB : B ≃+ N` is `e`-semilinear for a ring isomorphism `e : K ≃+* T`, then `N` is of finite
presentation over `T`.

This is the entire abstract content of the stalk computation below. Stating it over variable
modules rather than at the concrete stalk types is what keeps both declarations inside the
default heartbeat budget: the identical reasoning performed in place costs roughly twice the
budget. -/
private theorem finitePresentation_of_surjections_ringEquiv
    {K T A B C N ι σ : Type u} [Ring K] [CommRing T]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup N]
    [Module K A] [Module K B] [Module K C] [Module T N] [Finite ι] [Finite σ]
    (eA : A ≃ₗ[K] (ι →₀ K)) (eC : C ≃ₗ[K] (σ →₀ K))
    (g : A →ₗ[K] B) (hg : Function.Surjective g)
    (ρ : C →ₗ[K] LinearMap.ker g) (hρ : Function.Surjective ρ)
    (e : K ≃+* T) (eB : B ≃+ N)
    (heB : ∀ (a : K) (b : B), eB (a • b) = e a • eB b) :
    Module.FinitePresentation T N := by
  classical
  have hl : Function.Surjective (g.comp eA.symm.toLinearMap) := by
    intro b
    obtain ⟨a, ha⟩ := hg b
    exact ⟨eA a, by simpa using ha⟩
  let eKer : LinearMap.ker g ≃ₗ[K] LinearMap.ker (g.comp eA.symm.toLinearMap) :=
    { toFun := fun z => ⟨eA z.1, by simp⟩
      invFun := fun z => ⟨eA.symm z.1, z.2⟩
      left_inv := fun z => Subtype.ext (eA.symm_apply_apply z.1)
      right_inv := fun z => Subtype.ext (eA.apply_symm_apply z.1)
      map_add' := fun z w => Subtype.ext (eA.map_add z.1 w.1)
      map_smul' := fun a z => Subtype.ext (eA.map_smul a z.1) }
  exact finitePresentation_of_ringEquiv_linearPresentation e eB heB
    (g.comp eA.symm.toLinearMap) (eKer.toLinearMap.comp (ρ.comp eC.symm.toLinearMap)) hl
    (eKer.surjective.comp (hρ.comp eC.symm.surjective))

/-- The restricted ring stalk `(𝒪_Y|_U)_{⟨y,·⟩}` written two ways: as the stalk of the sheaf
`U.sheafRestrict.obj (structureSheafRing Y)` used by the stalk functor, and as
`LocallyFreeRank.restrictStalkRing`, the spelling the trivialization lemmas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank` state their conclusions over. The
two are definitionally the
same ring; naming the identification once keeps it out of the two consumers below. -/
private noncomputable def restrictStalkRingCast (Y : RingedSpace.{u, u}) (y : Y.carrier)
    (U : Opens Y.carrier) (hyU : y ∈ U) :
    ↑(TopCat.Presheaf.stalk (C := RingCat.{u}) (X := TopCat.of U.carrier)
        (U.sheafRestrict.obj (structureSheafRing Y)).obj (⟨y, hyU⟩ : TopCat.of U.carrier))
      ≃+* LocallyFreeRank.restrictStalkRing (TopCat.of Y.carrier) Y.sheaf y U hyU :=
  RingEquiv.cast (congrArg
    (fun P : TopCat.Presheaf RingCat (TopCat.of U.carrier) =>
      P.stalk (⟨y, hyU⟩ : TopCat.of U.carrier))
    (show ((TopCat.Sheaf.forget RingCat (TopCat.of U.carrier)).obj
          (U.sheafRestrict.obj (structureSheafRing Y))) =
        ((TopCat.Sheaf.forget RingCat (TopCat.of U.carrier)).obj
          (LocallyFreeRank.restrictRing (TopCat.of Y.carrier) U
            (LocallyFreeRank.toRingSheaf (TopCat.of Y.carrier) Y.sheaf))) from by congr 1))

/-- The stalk of `M` at `y` computed through the restricted site over a neighbourhood `U`, and
its stalk computed on `Y`, are identified by an additive equivalence semilinear over the ring
isomorphism `(𝒪_Y|_U)_{⟨y,·⟩} ≃+* 𝒪_{Y,y}`.

This is `LocallyFreeRank.Trivialization.stalk_restrictMod_linearEquiv` with its scalars moved
onto the stalk functor's own base ring. It is a separate declaration because the type ascription
that identifies the two spellings of the stalk compares two `Module` structures on those stalks,
and performed inside `sheafFinitePresentation_stalk` that single step costs half of the default
heartbeat budget on its own. -/
private theorem exists_restrictStalk_semilinearEquiv (Y : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureSheafRing Y)) (y : Y.carrier)
    (U : Opens Y.carrier) (hyU : y ∈ U) :
    letI : Module (ToType (TopCat.Presheaf.stalk Y.sheaf.obj y))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) :=
      LocallyFreeRank.instModuleStalkF (TopCat.of Y.carrier) Y.sheaf M y
    ∃ (e : ↑(TopCat.Presheaf.stalk (C := RingCat.{u}) (X := TopCat.of U.carrier)
            (U.sheafRestrict.obj (structureSheafRing Y)).obj (⟨y, hyU⟩ : TopCat.of U.carrier))
          ≃+* ToType (TopCat.Presheaf.stalk Y.sheaf.obj y))
        (eA : ↑((@AlgebraicGeometry.SheafOfModules.stalkFunctor (TopCat.of U.carrier)
              (U.sheafRestrict.obj (structureSheafRing Y)) (⟨y, hyU⟩ : TopCat.of U.carrier)).obj
                ((U.sheafOfModulesEquivOver (structureSheafRing Y)).functor.obj (M.over U)))
            ≃+ ToType (TopCat.Presheaf.stalk M.val.presheaf y)),
      ∀ a m, eA (a • m) = e a • eA m := by
  classical
  let xU : TopCat.of U.carrier := ⟨y, hyU⟩
  let Stalk := @AlgebraicGeometry.SheafOfModules.stalkFunctor (TopCat.of U.carrier)
    (U.sheafRestrict.obj (structureSheafRing Y)) xU
  let MU := (U.sheafOfModulesEquivOver (structureSheafRing Y)).functor.obj (M.over U)
  let kU := LocallyFreeRank.restrictStalkRing (TopCat.of Y.carrier) Y.sheaf y U hyU
  let eRing := restrictStalkRingCast Y y U hyU
  let eTag := LocallyFreeRank.restrictStalkRingEquiv
    (TopCat.of Y.carrier) Y.sheaf y hyU
  let : Module kU ↑(Stalk.obj MU) :=
    Module.compHom ↑(Stalk.obj MU) eRing.symm.toRingHom
  let : Module (ToType (TopCat.Presheaf.stalk Y.sheaf.obj y))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) :=
    LocallyFreeRank.instModuleStalkF (TopCat.of Y.carrier) Y.sheaf M y
  let : Module kU (ToType (TopCat.Presheaf.stalk
      (X := TopCat.of (U : Type u))
      ((LocallyFreeRank.restrictMod (TopCat.of Y.carrier) U
        (LocallyFreeRank.toRingSheaf (TopCat.of Y.carrier) Y.sheaf) M).val.presheaf)
      (⟨y, hyU⟩ : (U : Type u)))) :=
    LocallyFreeRank.instModuleStalkRestrictMod
      (TopCat.of Y.carrier) Y.sheaf M y U hyU
  let : Module kU (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) :=
    Module.compHom (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) eTag.toRingHom
  obtain ⟨eLocalGlobal₀⟩ :=
    LocallyFreeRank.Trivialization.stalk_restrictMod_linearEquiv
      (TopCat.of Y.carrier) Y.sheaf M y hyU
  let eLocalGlobal :
      ↑(Stalk.obj MU) ≃ₗ[kU]
        ↑(TopCat.Presheaf.stalk M.val.presheaf y) := eLocalGlobal₀
  exact ⟨eRing.trans eTag, eLocalGlobal.toAddEquiv, fun a m =>
    addEquiv_smul_of_compHom eRing eTag
      (fun a m => by
        show a • m = (eRing.symm (eRing a)) • m
        rw [eRing.symm_apply_apply])
      (fun _ _ => rfl) eLocalGlobal a m⟩

private theorem sheafFinitePresentation_stalk
    {Y : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing Y))
    [M.IsFinitePresentation] (y : Y.carrier) :
    let M' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
    Module.FinitePresentation (TopCat.Presheaf.stalk (C := CommRingCat.{u}) Y.presheaf y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M'.presheaf y) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let : q.IsFinitePresentation := hq
  have hycover : y ∈ iSup q.X := by
    rw [(Opens.coversTop_iff Y.carrier q.X).1 q.coversTop]
    simp
  obtain ⟨i, hyi⟩ := (Opens.mem_iSup).mp hycover
  let U : Opens Y.carrier := q.X i
  let E := U.sheafOfModulesEquivOver (structureSheafRing Y)
  let MU := E.functor.obj (M.over U)
  let P := q.presentation i
  let P' := P.map E.functor (U.sheafOfModulesEquivOverUnit (structureSheafRing Y)).symm
  let xU : TopCat.of U.carrier := ⟨y, hyi⟩
  let Stalk := AlgebraicGeometry.SheafOfModules.stalkFunctor
    (U.sheafRestrict.obj (structureSheafRing Y)) xU
  have hcol : Limits.PreservesColimitsOfSize.{u, u} Stalk :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits _ _
  have hP' : P'.IsFinite := by
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · simpa [P', SheafOfModules.Presentation.map,
        SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.generatorsOfIsCokernelFree] using
          (inferInstance : Finite P.generators.I)
    · simpa [P', SheafOfModules.Presentation.map,
        SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.relationsOfIsCokernelFree] using
          (inferInstance : Finite P.relations.I)
  let Rst := TopCat.Presheaf.stalk (C := RingCat.{u}) (X := TopCat.of U.carrier)
    (U.sheafRestrict.obj (structureSheafRing Y)).obj xU
  let kU := LocallyFreeRank.restrictStalkRing (TopCat.of Y.carrier) Y.sheaf y U hyi
  let eRing : ↑Rst ≃+* kU := restrictStalkRingCast Y y U hyi
  let sGen := ↑(Stalk.obj (SheafOfModules.free P'.generators.I))
  let : Module (↑Rst) sGen := inferInstance
  let : Module kU sGen := Module.compHom sGen eRing.symm.toRingHom
  let eGenData := LocallyFreeRank.Trivialization.stalk_free_linearEquiv
    (TopCat.of Y.carrier) Y.sheaf y (U := U) hyi P'.generators.I
  let sRel := ↑(Stalk.obj (SheafOfModules.free P'.relations.I))
  let : Module (↑Rst) sRel := inferInstance
  let : Module kU sRel := Module.compHom sRel eRing.symm.toRingHom
  let eRelData := LocallyFreeRank.Trivialization.stalk_free_linearEquiv
    (TopCat.of Y.carrier) Y.sheaf y (U := U) hyi P'.relations.I
  have hcol' : Limits.PreservesFiniteLimits Stalk :=
    moduleStalkFunctor_preservesFiniteLimits
      (U.sheafRestrict.obj (structureSheafRing Y)) xU
  let eGenRst : sGen ≃ₗ[↑Rst] (P'.generators.I →₀ ↑Rst) :=
    finsuppCongrScalars eRing (fun _ _ => rfl) eGenData.some
  let eRelRst : sRel ≃ₗ[↑Rst] (P'.relations.I →₀ ↑Rst) :=
    finsuppCongrScalars eRing (fun _ _ => rfl) eRelData.some
  let gMor := Stalk.map P'.generators.π
  let g : ↑(Stalk.obj (SheafOfModules.free P'.generators.I)) →ₗ[
      ↑Rst]
      ↑(Stalk.obj MU) := gMor.hom
  let kIso : Stalk.obj (Limits.kernel P'.generators.π) ≅
      ModuleCat.of (↑Rst) (LinearMap.ker g) :=
    (Limits.PreservesKernel.iso Stalk P'.generators.π) ≪≫
      ModuleCat.kernelIsoKer gMor
  let relMor := Stalk.map P'.relations.π
  have : Limits.PreservesFiniteColimits Stalk := inferInstance
  have hgenSurj : Function.Surjective g :=
    (ModuleCat.epi_iff_surjective gMor).mp inferInstance
  have hrelSurj : Function.Surjective relMor.hom :=
    (ModuleCat.epi_iff_surjective relMor).mp inferInstance
  have hkIsoSurj : Function.Surjective kIso.hom.hom :=
    (ModuleCat.epi_iff_surjective kIso.hom).mp inferInstance
  let : Module (ToType (TopCat.Presheaf.stalk Y.sheaf.obj y))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) :=
    LocallyFreeRank.instModuleStalkF (TopCat.of Y.carrier) Y.sheaf M y
  obtain ⟨eBase, eAdd, heAdd⟩ := exists_restrictStalk_semilinearEquiv Y M y U hyi
  exact finitePresentation_of_surjections_ringEquiv
    (K := ↑Rst) (T := ToType (TopCat.Presheaf.stalk Y.sheaf.obj y))
    (B := ↑(Stalk.obj MU)) (N := ↑(TopCat.Presheaf.stalk M.val.presheaf y))
    (ι := P'.generators.I) (σ := P'.relations.I)
    eGenRst eRelRst g hgenSurj (kIso.hom.hom.comp relMor.hom)
    (hkIsoSurj.comp hrelSurj) eBase eAdd heAdd

/-- The stalk map of a morphism of presheaves of modules sends the germ of `s` to the germ of
its image. -/
private theorem stalkFunctor_map_germ_toPresheaf
    {Z : TopCat.{u}} {R : Z.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (φ : M ⟶ N) (x : Z) (U : Opens Z) (hx : x ∈ U) (s : M.obj (Opposite.op U)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ)).hom
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hx
        ((φ.app (Opposite.op U)).hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ) s

private noncomputable def stalkMapLinear
    {Z : TopCat.{u}} {R : Z.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (φ : M ⟶ N) (x : Z) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) →ₗ[R.stalk x]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) := by
  let φp : M.presheaf ⟶ N.presheaf :=
    (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ
  let ψ := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φp).hom
  refine { toFun := ψ, map_add' := ψ.map_add, map_smul' := ?_ }
  intro r m
  obtain ⟨Ur, hUr, sr, hsr⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) R r
  obtain ⟨Um, hUm, sm, hsm⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) M.presheaf m
  let U : TopologicalSpace.Opens Z := Ur ⊓ Um
  let hU : x ∈ U := ⟨hUr, hUm⟩
  let iUr : U ⟶ Ur := homOfLE inf_le_left
  let iUm : U ⟶ Um := homOfLE inf_le_right
  let rU : R.obj (Opposite.op U) := (R.map iUr.op).hom sr
  let mU : M.obj (Opposite.op U) := (M.map iUm.op).hom sm
  have hgr : (R.germ U x hU).hom rU = r := by
    dsimp [rU]
    rw [TopCat.Presheaf.germ_res_apply R iUr x hU sr, hsr]
  have hgm : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hU).hom mU = m := by
    change (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hU).hom
      ((M.presheaf.map iUm.op).hom sm) = m
    rw [TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.presheaf iUm x hU sm, hsm]
  rw [← hgr, ← hgm, ← PresheafOfModules.germ_smul M x U hU rU mU]
  have hnat (s : M.obj (Opposite.op U)) :
      ψ ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hU).hom s) =
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hU).hom
          ((φ.app (Opposite.op U)).hom s) :=
    stalkFunctor_map_germ_toPresheaf M N φ x U hU s
  rw [hnat (rU • mU), hnat mU, (φ.app (Opposite.op U)).hom.map_smul rU mU,
    PresheafOfModules.germ_smul N x U hU rU ((φ.app (Opposite.op U)).hom mU), hgr]
  simp

private theorem stalkMapLinear_germ
    {Z : TopCat.{u}} {R : Z.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (φ : M ⟶ N) (x : Z) (U : Opens Z) (hx : x ∈ U)
    (s : M.obj (Opposite.op U)) :
    stalkMapLinear (R := R) M N φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hx
        ((φ.app (Opposite.op U)).hom s) := by
  dsimp [stalkMapLinear]
  exact stalkFunctor_map_germ_toPresheaf M N φ x U hx s

private abbrev ringedSpaceModulePresheaf
    {X : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing X)) :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val

private abbrev ringedSpaceModuleMap
    {X : RingedSpace.{u, u}} {M N : SheafOfModules.{u} (structureSheafRing X)}
    (φ : M ⟶ N) : ringedSpaceModulePresheaf M ⟶ ringedSpaceModulePresheaf N := φ.val

private lemma isIso_of_stalkMapLinear_bijective
    {X : RingedSpace.{u, u}} {M N : SheafOfModules.{u} (structureSheafRing X)}
    (φ : M ⟶ N)
    (hφ : ∀ x, Function.Bijective
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((ExtensionByZeroModules.toAb (structureSheafRing X)).map φ)).hom)) : IsIso φ :=
  ExtensionByZeroModules.isIso_of_stalk_isIso (X := TopCat.of X.carrier)
    (O := structureSheafRing X) φ fun x => (ConcreteCategory.isIso_iff_bijective _).mpr (hφ x)

private theorem ringedSpace_sheaf_obj_eq {Z : RingedSpace.{u, u}} :
    (SheafedSpace.sheaf Z).obj = Z.presheaf := rfl

/-- The canonical comparison, specified by pullback of local homomorphisms.

Write `η` for the unit of `f^* ⊣ f_*`. For `s ∈ H(V)`, let `φ` be the local
homomorphism represented by `s`. The adjoint transpose of `hom` sends `s` to
the local homomorphism on `f⁻¹(V)` which, on every `f⁻¹(U)` with `U ⊆ V`, sends
`η_F(t)` to `η_G(φ(t))`.

These equations characterize pullback of `φ`: sections in the image of the
unit locally generate the pullback as an `𝒪_X`-module. The quantification over
all nested opens makes the characterization compatible with restriction.
Thus the extra data specifies the canonical map, without imposing an extra
condition on the ringed spaces or on `F` and `G`. -/
structure PullbackSheafHomComparison
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F G : SheafOfModules.{u} (structureSheafRing Y))
    (H : SheafHom Y.sheaf F G)
    (H' : SheafHom X.sheaf ((modulePullback f).obj F)
      ((modulePullback f).obj G)) where
  /-- The comparison morphism. -/
  hom : (modulePullback f).obj H.obj ⟶ H'.obj
  /-- A pulled-back local homomorphism acts on a pulled-back section by
  pulling back its value. -/
  map_sections (V U : Opens Y) (i : U ⟶ V) (s : H.obj.val.obj (op V))
      (t : F.val.obj (op U)) :
    (H'.sectionsEquiv ((opensMap f).obj V)
      (((modulePullbackPushforwardAdjunction f).homEquiv H.obj H'.obj hom).val.app
        (op V) s)).val.app (op (Over.mk ((opensMap f).map i)))
          (((modulePullbackPushforwardAdjunction f).unit.app F).val.app (op U) t) =
      ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op U)
        ((H.sectionsEquiv V s).val.app (op (Over.mk i)) t)

/-- The canonical map
`f^* SheafHom(F, G) ⟶ SheafHom(f^*F, f^*G)`, with its sectionwise
characterization supplied by `PullbackSheafHomComparison`. -/
def pullbackSheafHomComparison
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F G : SheafOfModules.{u} (structureSheafRing Y))
    (H : SheafHom Y.sheaf F G)
    (H' : SheafHom X.sheaf ((modulePullback f).obj F)
      ((modulePullback f).obj G))
    (comparison : PullbackSheafHomComparison f F G H H') :
    (modulePullback f).obj H.obj ⟶ H'.obj :=
  comparison.hom

private theorem pullbackSheafHomComparison_stalk_bijective
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (hf : AlgebraicGeometry.IsFlat f)
    (F G : SheafOfModules.{u} (structureSheafRing Y)) [F.IsFinitePresentation]
    (H : SheafHom Y.sheaf F G)
    (H' : SheafHom X.sheaf ((modulePullback f).obj F) ((modulePullback f).obj G))
    (comparison : PullbackSheafHomComparison f F G H H') (x : X) :
    Function.Bijective (stalkMapLinear (R := X.presheaf)
      (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj))
      (ringedSpaceModulePresheaf H'.obj) (ringedSpaceModuleMap comparison.hom) x) := by
  classical
  let y := f.hom.base x
  let R := TopCat.Presheaf.stalk (C := CommRingCat.{u}) Y.sheaf.obj y
  let S := X.presheaf.stalk x
  let F' := (modulePullback f).obj F
  let G' := (modulePullback f).obj G
  let Htgt := Stacks.SheafOfModules.SheafHomStalk.commVal
    (Rc := X.sheaf) H'.obj
  let Fsrc := Stacks.SheafOfModules.SheafHomStalk.commVal
    (Rc := Y.sheaf) F
  let Gsrc := Stacks.SheafOfModules.SheafHomStalk.commVal
    (Rc := Y.sheaf) G
  let Hsrc := Stacks.SheafOfModules.SheafHomStalk.commVal
    (Rc := Y.sheaf) H.obj
  let Ftgt := Stacks.SheafOfModules.SheafHomStalk.commVal
    (Rc := X.sheaf) F'
  let Gtgt := Stacks.SheafOfModules.SheafHomStalk.commVal
    (Rc := X.sheaf) G'
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Fsrc.presheaf y
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Gsrc.presheaf y
  let P := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Hsrc.presheaf y
  let M' := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Ftgt.presheaf x
  let N' := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Gtgt.presheaf x
  let P' := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Htgt.presheaf x
  let : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.sheaf.obj) F.val y
  let : Module R N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.sheaf.obj) G.val y
  let : Module (↑R) (↑(TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.SheafOfModules.SheafHomStalk.commVal
        (Rc := Y.sheaf) F).presheaf y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.sheaf.obj) F.val y
  let : Module (↑R) (↑(TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.SheafOfModules.SheafHomStalk.commVal
        (Rc := Y.sheaf) G).presheaf y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.sheaf.obj) G.val y
  let : Module R P :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.sheaf.obj) H.obj.val y
  let : Module (↑R) (TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.SheafOfModules.SheafHomStalk.commVal
        (Rc := Y.sheaf) H.obj).presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.sheaf.obj) H.obj.val y
  let : Module S M' :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.obj) F'.val x
  let : Module S N' :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.obj) G'.val x
  let : Module S P' :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.obj) H'.obj.val x
  let : Module (↑(X.presheaf.stalk x)) (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (Stacks.SheafOfModules.SheafHomStalk.commVal
        (Rc := X.sheaf) H'.obj).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.obj) H'.obj.val x
  let instPullbackHomStalk : Module (↑(X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((modulePullback f).obj H.obj).val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.obj) ((modulePullback f).obj H.obj).val x
  -- The same module structure again, with the structure presheaf spelled `X.presheaf` rather
  -- than `X.sheaf.obj`.  `exists_modulePullbackStalkLinearEquiv` states its conclusion over the
  -- former, and instance search does not identify the two: both are plain definitions, so they
  -- are equal only at default transparency.
  let : Module (↑(X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj)) x
  let : Module (↑(X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (ringedSpaceModulePresheaf ((modulePullback f).obj F)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (ringedSpaceModulePresheaf ((modulePullback f).obj F)) x
  let : Module (↑(X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (ringedSpaceModulePresheaf ((modulePullback f).obj G)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (ringedSpaceModulePresheaf ((modulePullback f).obj G)) x
  let instTargetHomStalk : Module (↑(X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) H'.obj.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.sheaf.obj) H'.obj.val x
  let : Algebra R S := (f.hom.stalkMap x).hom.toAlgebra
  let : Module.Flat R S := hf x
  let : Module.FinitePresentation R M := sheafFinitePresentation_stalk F y
  have : ((modulePullback f).obj F).IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation f F
  obtain ⟨EF, hEF⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f F x
  obtain ⟨EG, hEG⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f G x
  obtain ⟨EH, hEH⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f H.obj x
  let eH := @Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearEquivOfFinitePresentation.{u}
    (TopCat.of Y.carrier) Y.sheaf F G H y (inferInstance : F.IsFinitePresentation)
  let eH' := @Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearEquivOfFinitePresentation.{u}
    (TopCat.of X.carrier) X.sheaf F' G' H' x (inferInstance : F'.IsFinitePresentation)
  let eH'linear : P' ≃ₗ[S] (M' →ₗ[S] N') :=
    { toFun := eH'.equiv
      invFun := eH'.equiv.symm
      left_inv := eH'.equiv.left_inv
      right_inv := eH'.equiv.right_inv
      map_add' := eH'.equiv.map_add
      map_smul' := eH'.equiv.map_smul }
  let b := stalkMapLinear (R := X.presheaf)
    (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj))
    (ringedSpaceModulePresheaf H'.obj) (ringedSpaceModuleMap comparison.hom) x
  let eHb : TensorProduct R S P ≃ₗ[S]
      TensorProduct R S (M →ₗ[R] N) := eH.equiv.baseChange R S
  let eH'fun : (M' →ₗ[S] N') ≃ₗ[S]
      (TensorProduct R S M →ₗ[S] TensorProduct R S N) :=
    LinearEquiv.arrowCongr EF EG
  let EHinv : TensorProduct R S P →ₗ[S]
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj)).presheaf x) :=
    EH.symm.toLinearMap
  let bBase : TensorProduct R S (M →ₗ[R] N) →ₗ[S] P' :=
    (b.comp EHinv).comp eHb.symm.toLinearMap
  let lhs : TensorProduct R S (M →ₗ[R] N) →ₗ[S]
      (TensorProduct R S M →ₗ[S] TensorProduct R S N) :=
    eH'fun.toLinearMap.comp (eH'linear.toLinearMap.comp bBase)
  let hbc := Module.FinitePresentation.isBaseChange_map R M N S
  let bc := hbc.equiv
  have hbBase : ∀ t, bBase t = b (EH.symm (eHb.symm t)) := fun _ => rfl
  have hlhs : ∀ t, lhs t = eH'fun (eH'linear (bBase t)) := fun _ => rfl
  have hgen1 (p : M →ₗ[R] N) (m : M) :
      lhs ((1 : S) ⊗ₜ[R] p) ((1 : S) ⊗ₜ[R] m) =
        bc ((1 : S) ⊗ₜ[R] p) ((1 : S) ⊗ₜ[R] m) := by
    obtain ⟨V, hyV, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) Hsrc.presheaf
        (eH.equiv.symm p)
    obtain ⟨W, hyW, t, ht⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) Fsrc.presheaf m
    let U : Opens Y.carrier := V ⊓ W
    let hyU : y ∈ U := ⟨hyV, hyW⟩
    let iV : U ⟶ V := homOfLE inf_le_left
    let iW : U ⟶ W := homOfLE inf_le_right
    let sU := (Hsrc.presheaf.map iV.op).hom s
    let tU := (Fsrc.presheaf.map iW.op).hom t
    have hsU : TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        Hsrc.presheaf U y hyU sU = eH.equiv.symm p := by
      rw [TopCat.Presheaf.germ_res_apply, hs]
    have htU : TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        Fsrc.presheaf U y hyU tU = m := by
      rw [TopCat.Presheaf.germ_res_apply, ht]
    let fU := (opensMap f).obj U
    have hxU : x ∈ fU := hyU
    let adj := modulePullbackPushforwardAdjunction f
    let uH := (adj.unit.app H.obj).val.app (op U) sU
    let uF := (adj.unit.app F).val.app (op U) tU
    let uG := (adj.unit.app G).val.app (op U)
      ((H.sectionsEquiv U sU).val.app (op (Over.mk (𝟙 U))) tU)
    let zH := TopCat.Presheaf.germ
      (C := AddCommGrpCat.{u}) ((modulePullback f).obj H.obj).val.presheaf fU x hxU uH
    let qsec := ((adj.homEquiv H.obj H'.obj comparison.hom).val.app (op U)).hom sU
    let zH' := TopCat.Presheaf.germ
      (C := AddCommGrpCat.{u}) Htgt.presheaf fU x hxU qsec
    let zF := TopCat.Presheaf.germ
      (C := AddCommGrpCat.{u}) Ftgt.presheaf fU x hxU uF
    let zG := TopCat.Presheaf.germ
      (C := AddCommGrpCat.{u}) Gtgt.presheaf fU x hxU uG
    have hEH' : EH zH = (1 : S) ⊗ₜ[R]
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Hsrc.presheaf U y hyU sU :=
      hEH U hyU sU
    have hEF' : EF zF = (1 : S) ⊗ₜ[R]
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Fsrc.presheaf U y hyU tU :=
      hEF U hyU tU
    have hEG' : EG zG = (1 : S) ⊗ₜ[R]
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Gsrc.presheaf U y hyU
          ((H.sectionsEquiv U sU).val.app (op (Over.mk (𝟙 U))) tU) :=
      hEG U hyU ((H.sectionsEquiv U sU).val.app (op (Over.mk (𝟙 U))) tU)
    have hsTrans : qsec =
        ((ringedSpaceModuleMap comparison.hom).app (op fU)).hom uH := by
      show ((adj.homEquiv H.obj H'.obj comparison.hom).val.app (op U)).hom sU = _
      exact congrArg (fun m => (m.val.app (op U)).hom sU)
        (adj.homEquiv_unit (f := comparison.hom))
    let b' := stalkMapLinear (R := X.presheaf)
      (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj))
      (ringedSpaceModulePresheaf H'.obj) (ringedSpaceModuleMap comparison.hom) x
    have hbz : b' zH = zH' := by
      show stalkMapLinear (R := X.presheaf)
          (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj))
          (ringedSpaceModulePresheaf H'.obj) (ringedSpaceModuleMap comparison.hom) x
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj)).presheaf
            fU x hxU uH) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (ringedSpaceModulePresheaf H'.obj).presheaf fU x hxU qsec
      rw [stalkMapLinear_germ (R := X.presheaf)
        (ringedSpaceModulePresheaf ((modulePullback f).obj H.obj))
        (ringedSpaceModulePresheaf H'.obj) (ringedSpaceModuleMap comparison.hom)
        x fU hxU uH, ← hsTrans]
    have hmap' := comparison.map_sections U U (𝟙 U) sU tU
    rw [show (opensMap f).map (𝟙 U) = 𝟙 fU from Subsingleton.elim _ _] at hmap'
    have hEval : eH'linear zH' zF =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Gtgt.presheaf fU x hxU
          ((H'.sectionsEquiv fU qsec).val.app (op (Over.mk (𝟙 fU))) uF) :=
      eH'.germ_apply fU hxU qsec uF
    rw [hmap'] at hEval
    have hq : eH.equiv
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Hsrc.presheaf U y hyU sU) = p := by
      rw [hsU, LinearEquiv.apply_symm_apply]
    have hsource : eHb.symm ((1 : S) ⊗ₜ[R] p) =
        (1 : S) ⊗ₜ[R]
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Hsrc.presheaf U y hyU sU := by
      show (eH.equiv.baseChange R S).symm ((1 : S) ⊗ₜ[R] p) = _
      rw [LinearEquiv.baseChange_symm_tmul]
      exact congrArg (fun m => (1 : S) ⊗ₜ[R] m) hsU.symm
    have hsource' : EH.symm (eHb.symm ((1 : S) ⊗ₜ[R] p)) = zH := by
      rw [hsource]
      exact EH.injective ((EH.apply_symm_apply _).trans hEH'.symm)
    rw [hlhs ((1 : S) ⊗ₜ[R] p), hbBase ((1 : S) ⊗ₜ[R] p), hsource', hbz, ← htU, ← hEF']
    show (LinearEquiv.arrowCongr EF EG (eH'linear zH')) (EF zF) = _
    refine Eq.trans
      ((LinearEquiv.arrowCongr_apply EF EG (eH'linear zH') (EF zF)).trans
        (congrArg (fun t => EG ((eH'linear zH') t)) (EF.symm_apply_apply zF))) ?_
    calc
      EG ((eH'linear zH') zF) = EG zG := congrArg EG hEval
      _ = _ := by
        have heHval' :
            eH.equiv
                (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Hsrc.presheaf U y hyU sU)
                (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Fsrc.presheaf U y hyU tU) =
              TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Gsrc.presheaf U y hyU
                ((H.sectionsEquiv U sU).val.app (op (Over.mk (𝟙 U))) tU) :=
          eH.germ_apply U hyU sU tU
        rw [hEG', ← heHval', hq, htU, hEF', htU]
        simp [bc, IsBaseChange.equiv_tmul, LinearMap.baseChangeHom_apply]
        rfl
  have hgen (p : M →ₗ[R] N) :
      lhs ((1 : S) ⊗ₜ[R] p) = bc ((1 : S) ⊗ₜ[R] p) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul s m =>
        rw [TensorProduct.tmul_eq_smul_one_tmul (R := R) s m, map_smul, hgen1 p m, map_smul]
  have hEq : lhs = bc.toLinearMap := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp [lhs, bc]
    | add z w hz hw => simp [hz, hw]
    | tmul s p =>
        rw [TensorProduct.tmul_eq_smul_one_tmul (R := R) s p, map_smul, hgen p, map_smul]
        rfl
  have hbij : Function.Bijective lhs := by
    rw [hEq]
    exact bc.bijective
  have hcomp : ⇑lhs = ⇑(eH'linear.toEquiv.trans eH'fun.toEquiv) ∘ ⇑b ∘
      ⇑(eHb.symm.toEquiv.trans EH.symm.toEquiv) := rfl
  rw [hcomp, EquivLike.comp_bijective] at hbij
  exact (EquivLike.bijective_comp _ _).1 hbij

/-- **Stacks Project, Tag 0C6I.** Let `f : X ⟶ Y` be a flat morphism of
ringed spaces. If `F` is a finitely presented `𝒪_Y`-module, then the canonical
map
`f^* SheafHom(F, G) ⟶ SheafHom(f^*F, f^*G)` is an isomorphism. -/
@[stacks 0C6I]
theorem pullbackSheafHomComparison_isIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.IsFlat f)
    (F G : SheafOfModules.{u} (structureSheafRing Y)) [F.IsFinitePresentation]
    (H : SheafHom Y.sheaf F G)
    (H' : SheafHom X.sheaf ((modulePullback f).obj F)
      ((modulePullback f).obj G))
    (comparison : PullbackSheafHomComparison f F G H H') :
    IsIso (pullbackSheafHomComparison f F G H H' comparison) :=
  isIso_of_stalkMapLinear_bijective _ fun x =>
    pullbackSheafHomComparison_stalk_bijective f hf F G H H' comparison x

end Stacks.SheafHomPullback
