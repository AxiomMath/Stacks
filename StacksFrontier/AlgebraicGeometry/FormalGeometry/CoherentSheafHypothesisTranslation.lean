module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NearVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealFiniteness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SchemeOpenSectionsDerived
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyFiniteness
public import StacksFrontier.RingTheory.Depth.AlgebraMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0DXQ for an arbitrary coherent sheaf on the punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring, `X = Spec(A)`, `U = X ∖ {𝔪}` its punctured spectrum and
`I ⊆ A` a proper ideal with `Y = V(I)`.  Stacks 0DXQ is stated for an **arbitrary coherent
`𝒪_U`-module `ℱ`**, with its depth and dimension hypotheses read on the stalks `ℱ_x`.  The
formalization of that theorem in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodCohomologyFiniteness` is
stated instead for `ℱ = M̃|_U` with `M` a finite `A`-module, its hypotheses being read on the
localizations `M_𝔭`.  This file is the reduction of the first form to the second.

Two things are needed, and both are proved here.

*The hypotheses.*  Every coherent module on `U` is `M̃|_U` for a finite `A`-module `M`
(Stacks 0BK0 (1), `Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde`), and the stalk
of `M̃|_U` at a point `𝔭` of `U` is the localization `M_𝔭`, as a module over `𝒪_{U, 𝔭} ≅ A_𝔭`.
So `depth(ℱ_𝔭) = depth_{A_𝔭}(M_𝔭)`, and the source's hypotheses on the stalks of `ℱ` become
exactly the field `depthOrDimensionBound` of
`Stacks.Algebraization.PuncturedNeighbourhood.Hypotheses` and the predicate
`Stacks.Algebraization.DepthAddDimGtAtMaximalIdeal`.

*The cohomology.*  For an open `V = X ∖ V(J)` the source's `Hⁱ(V, ℱ)` is the cohomology of the
restriction of `ℱ` to `V`, whereas the `A`-module the finiteness statement is about is
`Stacks.LocalCohomologySequence.complementCohomologyBase J M i`, the right derived functor on
sheaves on the **ambient** `X` of the sections over that open.  The two are identified here, as
`A`-modules, by Stacks 01E1 (2).

## Main results

* `Stacks.Algebraization.depth_eq_of_semilinearAddEquiv` — depth is carried along a ring
  isomorphism together with a semilinear additive bijection of modules.
* `Stacks.Algebraization.stalkDepth` — the depth of the stalk of a sheaf of modules on a scheme
  at a point, over the local ring there.
* `Stacks.Algebraization.stalkDepth_congr`, `Stacks.Algebraization.stalkDepth_restrict` and
  `Stacks.Algebraization.stalkDepth_tilde` — the stalk depth is an isomorphism invariant, is
  unchanged by restriction along an open immersion, and for `M̃` at a prime `𝔭` equals
  `depth_{A_𝔭}(M_𝔭)`.
* `Stacks.Algebraization.mem_complementZeroLocus_maximalIdeal_of_notMem_zeroLocus` — for a proper
  ideal `I` every point of `X ∖ V(I)` lies on the punctured spectrum, which is what lets the
  source evaluate `ℱ` at the points of `X ∖ V(I)`.
* `Stacks.Algebraization.stalkDepth_eq_depth_localizedModule` — for `ℱ ≅ M̃|_U` the stalk depth of
  `ℱ` at `𝔭` is `depth_{A_𝔭}(M_𝔭)`.
* `Stacks.Algebraization.StalkDepthOrDimensionBound` and
  `Stacks.Algebraization.StalkDepthAddDimGt` — assumption (2) of Stacks 0DXQ and its extra
  finiteness assumption, stated on the stalks of `ℱ` as the source states them.
* `Stacks.Algebraization.hypotheses_of_stalkDepthOrDimensionBound` and
  `Stacks.Algebraization.depthAddDimGtAtMaximalIdeal_of_stalkDepthAddDimGt` — the two translation
  theorems.
* `Stacks.Algebraization.exists_finiteModule_hypotheses_of_isCoherent` — for a coherent `ℱ` the
  finite module and the translated hypotheses together, which is the source's reduction step.
* `Stacks.Algebraization.openCohomologyBase` and
  `Stacks.Algebraization.openCohomologyBaseIsoComplementCohomologyBase` — `Hⁱ(X ∖ V(J), ℱ|)` as
  an `A`-module, and its identification with
  `Stacks.LocalCohomologySequence.complementCohomologyBase`.
* `Stacks.Algebraization.openCohomologyBaseRestrictIso` — the same identification with the
  restriction of a module on `U` to `X ∖ V(J)` for `J ⊆ 𝔪`.

## Implementation notes

*The depth of a stalk needs a semilinear transport.*  The two stalks being compared are modules
over two *different* local rings, isomorphic but not equal: `𝒪_{U, x}` against `𝒪_{X, j(x)}` for
the open immersion `j`, and `𝒪_{X, 𝔭}` against `A_𝔭`.  So the invariance statements cannot be
`Module.depth_eq_depth_of_linearEquiv` alone; `depth_eq_of_semilinearAddEquiv` packages the
transport, and is proved from `Module.depth_eq_depth_of_linearEquiv` together with
`Module.depth_eq_depth_map_algebraMap` at the surjection given by the ring isomorphism.  The
same fact exists as a `private` declaration `depth_eq_of_semilinearEquiv` in
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapCompletion.lean`, stated for a
`≃ₛₗ`; being private it is unreachable, and the form taken here — an `AddEquiv` plus the
semilinearity equation — is the form in which the three stalk comparisons below supply it, since
the stalk functor used by `Stacks.Divisors.IsAssociatedPoint` and by `stalkDepth` lands in
abelian groups.

*The semilinearity of the two stalk identifications.*  For an isomorphism of `𝒪_X`-modules and
for restriction along an open immersion the semilinearity has to be checked on germs, by writing
a scalar and a vector as germs on a common open — `PresheafOfModules.germ_smul` together with
`Scheme.Modules.Hom.app_smul` in the first case, and with
`Scheme.Modules.germ_restrictStalkNatIso_hom_app` and
`Scheme.Modules.smul_restrictAppIso_hom_apply` in the second.  These are the same computations
that `Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr` and
`isAssociatedPoint_restrict_iff` perform for associated points; there they are internal to the
proofs, so they are redone here.

*The stalk of `M̃`.*  Mathlib's `Module R ((tilde M).presheaf.stalk x)` instance and its
`IsLocalizedModule` instance for `AlgebraicGeometry.tilde.toStalk` are found only when the point
is spelled as an element of `PrimeSpectrum ↑R`, not as a point of the scheme `Spec R`, which is
why `stalkDepth_tilde` is stated at that spelling; and the `A`-action on the stalk is the
restriction of the `𝒪_{X, 𝔭}`-action on the nose, so the scalar tower is `rfl`.  The `A_𝔭`-linear
identification `M_𝔭 ≅ M̃_𝔭` is obtained from the `A`-linear `IsLocalizedModule.iso` by
`LinearEquiv.extendScalarsOfIsLocalization`.

*Points of `X ∖ V(I)` are points of `U`.*  Assumption (2) of the source ranges over the points of
`X ∖ V(I)`, which would include `𝔪` if `𝔪 ∉ V(I)`; but `I` is proper, so `𝔪 ∈ V(I)` and every
such point lies in `U`, where `ℱ` is defined.  That is
`mem_complementZeroLocus_maximalIdeal_of_notMem_zeroLocus`, and it is what makes the stalkwise
condition of this file — quantified over the points of `U` outside `V(I)` — the source's
condition and not a restriction of it.

*Which of the named pieces of the cohomology comparison generalise.*  Of the three pieces the
implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCohomologyMittagLeffler` name for
the punctured spectrum, only `Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso` is
needed here, and it is already stated for an arbitrary scheme and an arbitrary open, so it
generalises verbatim.
`Stacks.Cohomology.ModuleComparison.homologyDerivedSectionsOverIsoRightDerived` is not
punctured-spectrum-specific either — it holds for any ringed space — but it is only needed when the
left-hand side is the *total* derived sections functor `RΓ`, which is the model Tag 0DXI uses and
not the one Tag 0DXQ's finiteness clause uses; the comparison below is between two classical right
derived functors and does not meet it.
`Stacks.LocalCohomology.hgroupRestrictIso` is general as well, for any scheme and open, but
compares the *abelian-group-valued* cohomology of Stacks 01E3 on the two sides and so loses the
`A`-module structure the statement is about; it is therefore not usable here.  The remaining
identifications, that the sections over the complement of `V(J)` are the sections over
`X ∖ V(J)` and that `complementCohomologyBase` is the result of reading those over `A`, hold by
`rfl`.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0DXN](https://stacks.math.columbia.edu/tag/0DXN)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)

## Tags

local cohomology, depth, coherent sheaf, punctured spectrum, algebraization, stalk
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing

universe u

namespace Stacks.Algebraization

/-- **Depth is carried along a ring isomorphism together with a semilinear bijection of
modules.**  If `e : R ≃+* S` and `f : M ≃+ N` satisfy `f (r • m) = e r • f m` for an `R`-module
`M` and an `S`-module `N`, then `depth_I(M) = depth_{I·S}(N)`.

The `S`-module `N` is read as an `R`-module along `e`, which makes `f` linear, and then
`Module.depth_eq_depth_map_algebraMap` at the surjection `e` moves the scalars back. -/
public theorem depth_eq_of_semilinearAddEquiv {R S : Type*} [CommRing R] [CommRing S]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : R ≃+* S) (f : M ≃+ N) (hf : ∀ (r : R) (m : M), f (r • m) = e r • f m)
    (I : Ideal R) :
    Module.depth R I M = Module.depth S (I.map (e : R →+* S)) N := by
  let : Algebra R S := (e : R →+* S).toAlgebra
  let : Module R N := Module.compHom N (e : R →+* S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (Module.depth_eq_depth_of_linearEquiv I
      ({ __ := f, map_smul' := hf } : M ≃ₗ[R] N)).trans
    (Module.depth_eq_depth_map_algebraMap e.surjective I N)

/-- `Stacks.Algebraization.depth_eq_of_semilinearAddEquiv` for local rings and their maximal
ideals, which `e` carries onto each other. -/
private theorem depth_maximalIdeal_eq_of_semilinearAddEquiv {R S : Type*} [CommRing R]
    [IsLocalRing R] [CommRing S] [IsLocalRing S] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = e r • f m) :
    Module.depth R (maximalIdeal R) M = Module.depth S (maximalIdeal S) N := by
  have hmap : Ideal.map (e : R →+* S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [depth_eq_of_semilinearAddEquiv e f hf, hmap]

/-- Scalar and vector in a stalk of a sheaf of modules are germs on a common open, and their
product is the germ of the product. -/
private theorem exists_germ_smul_eq {X : Scheme.{u}} (F : X.Modules) (x : X)
    (r : X.presheaf.stalk x) (m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (t : Γ(F, U)),
      X.presheaf.germ U x hx a = r ∧ TopCat.Presheaf.germ F.val.presheaf U x hx t = m ∧
        r • m = TopCat.Presheaf.germ F.val.presheaf U x hx (a • t) := by
  obtain ⟨U₁, hx₁, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨U₂, hx₂, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  have hx : x ∈ U₁ ⊓ U₂ := ⟨hx₁, hx₂⟩
  have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hx a
  have ht := TopCat.Presheaf.germ_res_apply F.val.presheaf
    (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hx t
  exact ⟨U₁ ⊓ U₂, hx, _, _, ha, ht, by
    rw [← ha, ← ht]; exact (PresheafOfModules.germ_smul F.val x _ hx _ _).symm⟩

/-- **The depth of the stalk of a sheaf of modules on a scheme at a point.**  The stalk `ℱ_x` is
a module over the local ring `𝒪_{X, x}`, and this is its depth along the maximal ideal there.
It is the quantity the hypotheses of Stacks 0DXQ are phrased with. -/
@[ega "IV 5.7.1"]
public def stalkDepth {X : Scheme.{u}} (F : X.Modules) (x : X) : ℕ∞ :=
  Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)

/-- **Isomorphic `𝒪_X`-modules have the same stalk depth at every point.**  An isomorphism
induces an isomorphism of stalks over the same local ring, linear for the action by
`Scheme.Modules.Hom.app_smul` on germs. -/
public theorem stalkDepth_congr {X : Scheme.{u}} {F G : X.Modules} (ee : F ≅ G) (x : X) :
    stalkDepth F x = stalkDepth G x := by
  let f : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x ≃+
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x :=
    ((TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      ((Scheme.Modules.toPresheaf X).mapIso ee)).addCommGroupIsoToAddEquiv
  have hfm : ∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)),
      f (TopCat.Presheaf.germ F.val.presheaf U x hx s)
        = TopCat.Presheaf.germ G.val.presheaf U x hx (ee.hom.app U s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx _ s
  have hf : ∀ r m, f (r • m) = (RingEquiv.refl (X.presheaf.stalk x)) r • f m := by
    intro r m
    obtain ⟨U, hx, a, t, rfl, rfl, hs⟩ := exists_germ_smul_eq F x r m
    rw [hs, hfm, hfm, Scheme.Modules.Hom.app_smul ee.hom a t]
    exact PresheafOfModules.germ_smul G.val x U hx a (ee.hom.app U t)
  exact depth_maximalIdeal_eq_of_semilinearAddEquiv (RingEquiv.refl _) f hf

/-- **The stalk depth is unchanged by restriction along an open immersion.**  For an open
immersion `j : X ⟶ Y` the stalk of `G|_X` at `x` is the stalk of `G` at `j x`
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), semilinearly over the stalk map of
`j`, which is an isomorphism of local rings carrying the maximal ideal onto the maximal
ideal. -/
public theorem stalkDepth_restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (G : Y.Modules) (x : X) :
    stalkDepth (Scheme.Modules.restrict G j) x = stalkDepth G (j.base x) := by
  let e : (X.presheaf.stalk x) ≃+* (Y.presheaf.stalk (j.base x)) :=
    (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
  let f : TopCat.Presheaf.stalk (C := Ab.{u}) (Scheme.Modules.restrict G j).val.presheaf x ≃+
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (j.base x) :=
    ((Scheme.Modules.restrictStalkNatIso j x).app G).addCommGroupIsoToAddEquiv
  have he (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
      e (X.presheaf.germ U x hx a) =
        Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a) := by
    apply e.symm.injective
    simp only [e.symm_apply_apply]
    show X.presheaf.germ U x hx a =
      j.stalkMap x (Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a))
    rw [j.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
    exact (X.presheaf.germ_res_apply _ _ _ _).symm
  have hf : ∀ r m, f (r • m) = e r • f m := by
    intro r m
    obtain ⟨U, hx, a, t, rfl, rfl, hs⟩ := exists_germ_smul_eq (Scheme.Modules.restrict G j) x r m
    have hfm (s : Γ(Scheme.Modules.restrict G j, U)) :
        f (TopCat.Presheaf.germ (Scheme.Modules.restrict G j).val.presheaf U x hx s) =
          G.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) s :=
      ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x G hx) s
    rw [hs]
    refine (hfm (a • t)).trans ?_
    rw [he, hfm]
    have hs := Scheme.Modules.smul_restrictAppIso_hom_apply j G U a t
    change a • t = (G.smul ((j.appIso U).inv a)).hom t at hs
    rw [hs]
    let z : Γ(G, j ''ᵁ U) := t
    show G.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa)
      ((G.smul ((j.appIso U).inv a)).hom z) = _
    rw [G.smul_apply ((j.appIso U).inv a) z]
    show TopCat.Presheaf.germ G.val.presheaf (j ''ᵁ U) (j.base x) (by simpa)
      (((j.appIso U).inv a) • z) = _
    exact PresheafOfModules.germ_smul G.val (j.base x) (j ''ᵁ U) (by simpa)
      ((j.appIso U).inv a) z
  exact depth_maximalIdeal_eq_of_semilinearAddEquiv e f hf

/-- `Stacks.Algebraization.stalkDepth_restrict` at the inclusion of an open subscheme: the stalk
depth of `G|_U` at a point of `U` is the stalk depth of `G` at that point of `X`. -/
public theorem stalkDepth_restrict_opens {X : Scheme.{u}} (U : X.Opens) (G : X.Modules)
    (x : U.toScheme) :
    stalkDepth (Scheme.Modules.restrict G U.ι) x = stalkDepth G x.1 :=
  stalkDepth_restrict U.ι G x

/-- **The depth of the stalk of `M̃` at a prime is the depth of the localization `M_𝔭`.** The
stalk of `M̃` at `𝔭` is the localization `M_𝔭` and the stalk of the structure sheaf is `A_𝔭`
(Stacks 01HV), compatibly with the actions, so `depth_{𝒪_𝔭}(M̃_𝔭) = depth_{A_𝔭}(M_𝔭)` by
`Stacks.Algebraization.depth_eq_of_semilinearAddEquiv`. -/
public theorem stalkDepth_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (p : PrimeSpectrum (ToType R)) :
    stalkDepth ((tilde.functor R).obj M) p =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := by
  let algInst : Algebra (ToType R) ((Spec R).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra (ToType R) p
  have locInst : IsLocalization.AtPrime
      (((Spec R).presheaf.stalk p : CommRingCat) : Type u) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (ToType R) p
  have localInst : IsLocalRing (((Spec R).presheaf.stalk p : CommRingCat) : Type u) :=
    IsLocalization.AtPrime.isLocalRing _ p.asIdeal
  let modStalk : Module ((Spec R).presheaf.stalk p)
      ((tilde M).presheaf.stalk p : Type u) :=
    Scheme.Modules.moduleStalk ((tilde.functor R).obj M) p
  have tower : IsScalarTower (ToType R) ((Spec R).presheaf.stalk p)
      ((tilde M).presheaf.stalk p : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ : Localization.AtPrime p.asIdeal ≃ₐ[ToType R] ((Spec R).presheaf.stalk p) :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  let modAp : Module (Localization.AtPrime p.asIdeal) ((tilde M).presheaf.stalk p : Type u) :=
    Module.compHom _ (e₀ : Localization.AtPrime p.asIdeal →+* ((Spec R).presheaf.stalk p))
  have towerAp : IsScalarTower (ToType R) (Localization.AtPrime p.asIdeal)
      ((tilde M).presheaf.stalk p : Type u) :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      show (e₀ (algebraMap (ToType R) (Localization.AtPrime p.asIdeal) a)) • n = a • n
      rw [e₀.commutes]
      exact algebraMap_smul ((Spec R).presheaf.stalk p) a n
  have g : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[ToType R]
      ((tilde M).presheaf.stalk p : Type u) :=
    IsLocalizedModule.iso p.asIdeal.primeCompl (tilde.toStalk M p).hom
  have g' : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      ((tilde M).presheaf.stalk p : Type u) :=
    g.extendScalarsOfIsLocalization p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  exact (depth_maximalIdeal_eq_of_semilinearAddEquiv e₀.toRingEquiv g'.toAddEquiv
    (fun y m => g'.map_smul y m)).symm


/-! ### Every point of `X ∖ V(I)` lies on the punctured spectrum -/

section Punctured

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A prime lies on the punctured spectrum `U = Spec(A) ∖ {𝔪}` exactly when it is not the
closed point: the zero locus of the maximal ideal is the closed point. -/
public theorem mem_complementZeroLocus_maximalIdeal_iff (p : PrimeSpectrum A) :
    p ∈ complementZeroLocus A (maximalIdeal A) ↔ p ≠ closedPoint A := by
  show p ∉ PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ↔ _
  rw [zeroLocus_maximalIdeal]
  exact not_congr Set.mem_singleton_iff

/-- **A point of `X ∖ V(I)` lies on the punctured spectrum, for every proper ideal `I`.** This is
the step the source leaves silent when it states assumption (2) of Stacks 0DXQ at the points of
`X ∖ V(I)` and evaluates the stalk of a module `ℱ` that is only defined on `U = X ∖ {𝔪}`: since
`I` is proper the closed point lies in `V(I)`, so a point outside `V(I)` is not the closed
point. -/
public theorem mem_complementZeroLocus_maximalIdeal_of_notMem_zeroLocus {I : Ideal A}
    (hI : I ≠ ⊤) {p : PrimeSpectrum A} (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    p ∈ complementZeroLocus A (maximalIdeal A) :=
  (mem_complementZeroLocus_maximalIdeal_iff p).2 fun h =>
    hp (h ▸ closedPoint_mem_zeroLocus hI)

end Punctured

/-! ### The stalks of a coherent module on `U` are the localizations of a finite module -/

section Stalks

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {b : Ideal A} {M : ModuleCat.{u} A}
  {F : (complementZeroLocus A b : Scheme).Modules}

/-- **The depth of the stalk of a coherent module on `U = Spec(A) ∖ V(𝔟)` is the depth of a
localization.** If `ℱ ≅ M̃|_U` then the stalk of `ℱ` at a point `𝔭` of `U` is `M_𝔭`, as a module
over `𝒪_{U, 𝔭} ≅ A_𝔭`: restriction along an open immersion does not change the stalk
(`Stacks.Algebraization.stalkDepth_restrict`), and the stalk of `M̃` at `𝔭` is `M_𝔭`
(`Stacks.Algebraization.stalkDepth_tilde`).

This is the depth-theoretic counterpart of
`Stacks.Algebraization.mem_associatedPoints_complementTilde_iff`. -/
public theorem stalkDepth_eq_depth_localizedModule
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A b).ι)
    (p : PrimeSpectrum A) (hp : p ∈ complementZeroLocus A b) :
    stalkDepth F ⟨p, hp⟩ =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := by
  have h1 : stalkDepth F ⟨p, hp⟩ =
      stalkDepth (Scheme.Modules.restrict ((tilde.functor (CommRingCat.of A)).obj M)
        (complementZeroLocus A b).ι) ⟨p, hp⟩ := stalkDepth_congr e ⟨p, hp⟩
  have h2 : stalkDepth (Scheme.Modules.restrict ((tilde.functor (CommRingCat.of A)).obj M)
        (complementZeroLocus A b).ι) ⟨p, hp⟩ =
      stalkDepth ((tilde.functor (CommRingCat.of A)).obj M) p :=
    stalkDepth_restrict_opens (complementZeroLocus A b)
      ((tilde.functor (CommRingCat.of A)).obj M) ⟨p, hp⟩
  rw [h1, h2]
  exact stalkDepth_tilde (R := CommRingCat.of A) M p

end Stalks


/-! ### The hypotheses of Stacks 0DXQ, stated on the stalks of `ℱ` -/

section Conditions

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **Assumption (2) of Stacks 0DXQ, stated on the stalks of a module `ℱ` on the punctured
spectrum.** At a point `x` of `U = Spec(A) ∖ {𝔪}` lying outside `V(I)` whose closure in
`Spec(A)` meets `V(I)` in more than the closed point, either `depth(ℱ_x) ≥ s` or
`depth(ℱ_x) + dim(closure {x}) > d + s`.

The source quantifies over the points of `X ∖ V(I)`; by
`Stacks.Algebraization.mem_complementZeroLocus_maximalIdeal_of_notMem_zeroLocus` those all lie
in `U`, where `ℱ` is defined, so the two quantifications agree. -/
public def StalkDepthOrDimensionBound (I : Ideal A)
    (F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules) (s d : ℤ) : Prop :=
  ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
    x.1 ∉ PrimeSpectrum.zeroLocus (I : Set A) →
    PrimeSpectrum.zeroLocus (x.1.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ≠
      {closedPoint A} →
    ((enatToEInt (stalkDepth F x) ≥ (s : EInt)) ∨
      (enatToEInt (stalkDepth F x) + krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal)) >
        ((d + s : ℤ) : EInt)))

/-- **The extra finiteness assumption of Stacks 0DXQ, stated on the stalks of a module `ℱ` on the
punctured spectrum.** At every point `x` of `U ∩ V(I)` the sum `depth(ℱ_x) + dim(closure {x})`
exceeds `s`. -/
public def StalkDepthAddDimGt (I : Ideal A)
    (F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules) (s : ℤ) : Prop :=
  ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
    x.1 ∈ PrimeSpectrum.zeroLocus (I : Set A) →
    enatToEInt (stalkDepth F x) + krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal)) > (s : EInt)

variable {M : ModuleCat.{u} A} [Module.Finite A M]
  {F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules}

omit [Module.Finite A M] in
/-- **The hypotheses of Stacks 0DXQ for an arbitrary coherent `ℱ` are the hypotheses for
`ℱ = M̃|_U`.** Given a finite `A`-module `M` and an isomorphism `ℱ ≅ M̃|_U`, assumption (2) of
the source — stated on the stalks of `ℱ` — is the field `depthOrDimensionBound` of
`Stacks.Algebraization.PuncturedNeighbourhood.Hypotheses`, because the stalk of `ℱ` at a point
`𝔭` of `U` is `M_𝔭` by `Stacks.Algebraization.stalkDepth_eq_depth_localizedModule`.

The remaining fields of `Hypotheses` are conditions on `A` and `I` alone — properness of `I`,
`I`-adic completeness, the existence of a dualizing complex and assumption (1),
`cd(A, I) ≤ d` — and are carried unchanged. -/
public theorem hypotheses_of_stalkDepthOrDimensionBound (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hI : I ≠ ⊤) (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I
      (Ideal.fg_of_isNoetherianRing I) ≤ d)
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι)
    (h : StalkDepthOrDimensionBound I F s d) :
    PuncturedNeighbourhood.Hypotheses (M := (M : Type u)) I s d omega where
  ne_top := hI
  adicComplete := hcomplete
  dualizing := hdualizing
  cohomologicalDimension_le := hcd
  depthOrDimensionBound p hp hinter := by
    have hmem := mem_complementZeroLocus_maximalIdeal_of_notMem_zeroLocus hI hp
    have := h ⟨p, hmem⟩ hp hinter
    rwa [stalkDepth_eq_depth_localizedModule e p hmem] at this

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- **The extra finiteness assumption of Stacks 0DXQ for an arbitrary coherent `ℱ` is the
assumption for `ℱ = M̃|_U`.** Given a finite `A`-module `M` and an isomorphism `ℱ ≅ M̃|_U`, the
source's assumption `depth(ℱ_x) + dim(closure {x}) > s` at the points of `U ∩ V(I)` is
`Stacks.Algebraization.DepthAddDimGtAtMaximalIdeal`: a prime of `V(I)` other than `𝔪` is a point
of `U`, and there the stalk of `ℱ` is `M_𝔭`. -/
public theorem depthAddDimGtAtMaximalIdeal_of_stalkDepthAddDimGt (I : Ideal A) (s : ℤ)
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι)
    (h : StalkDepthAddDimGt I F s) :
    DepthAddDimGtAtMaximalIdeal (M := (M : Type u)) I s := by
  intro p hp hpne
  have hmem : p ∈ complementZeroLocus A (maximalIdeal A) :=
    (mem_complementZeroLocus_maximalIdeal_iff p).2 hpne
  have := h ⟨p, hmem⟩ hp
  rwa [stalkDepth_eq_depth_localizedModule e p hmem] at this


/-- **The reduction of Stacks 0DXQ to a finite module.** Let `(A, 𝔪)` be a Noetherian local ring
which has a dualizing complex and is `I`-adically complete for a proper ideal `I` with
`cd(A, I) ≤ d`, and let `ℱ` be a *coherent* module on the punctured spectrum
`U = Spec(A) ∖ {𝔪}` satisfying assumption (2) of the source and its extra finiteness
assumption, both read on the stalks of `ℱ`. Then there is a finite `A`-module `M` with
`ℱ ≅ M̃|_U` for which the hypotheses of
`Stacks.Algebraization.PuncturedNeighbourhood.Hypotheses` and
`Stacks.Algebraization.DepthAddDimGtAtMaximalIdeal` hold.

Stacks 0BK0 (1), in the form `Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde`,
produces `M`; the two translation theorems above then transport the stalkwise conditions. This
is the step of the source proof reading "we may assume `ℱ = M̃|_U` for a finite `A`-module `M`
by Lemma 0BK0". -/
public theorem exists_finiteModule_hypotheses_of_isCoherent (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hI : I ≠ ⊤) (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I
      (Ideal.fg_of_isNoetherianRing I) ≤ d)
    (G : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules) [G.IsCoherent]
    (h : StalkDepthOrDimensionBound I G s d) (hfin : StalkDepthAddDimGt I G s) :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      Nonempty (G ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
        (complementZeroLocus A (maximalIdeal A)).ι) ∧
      PuncturedNeighbourhood.Hypotheses (M := (M : Type u)) I s d omega ∧
      DepthAddDimGtAtMaximalIdeal (M := (M : Type u)) I s := by
  obtain ⟨M, hMfin, ⟨e⟩⟩ :=
    Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde A (maximalIdeal A) G
  have := hMfin
  exact ⟨M, hMfin, ⟨e⟩,
    hypotheses_of_stalkDepthOrDimensionBound I s d omega hI hcomplete hdualizing hcd e h,
    depthAddDimGtAtMaximalIdeal_of_stalkDepthAddDimGt I s e hfin⟩

end Conditions

/-! ### The two models of `Hⁱ(X ∖ V(J), ℱ)`, reconciled -/

section Cohomology

open Stacks.LocalCohomology
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.Cohomology.SchemeOpenSections (derivedSectionsOnOpenIso)

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- **`Hⁱ(W, 𝒢)` for an open subscheme `W` of `Spec(A)`, read as an `A`-module.**  The classical
`i`-th right derived functor of global sections on the open subscheme `W`, with scalars restricted
along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(W, 𝒪_W)`.

This is the left-hand side of the source's `Hⁱ(V, ℱ)`: the cohomology of a module *on `W`*, as
opposed to the cohomology on the ambient `Spec(A)` of the sections over `W`, which is
`Stacks.LocalCohomologySequence.complementCohomologyBase`. -/
public noncomputable abbrev openCohomologyBase (A : Type u) [CommRing A]
    (W : (Spec (CommRingCat.of A)).Opens) (G : W.toScheme.Modules) (i : ℕ) : ModuleCat.{u} A :=
  (Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)).obj
    ((ModuleCat.restrictScalars W.ι.appTop.hom).obj
      (((moduleGlobalSections W.toScheme).rightDerived i).obj G))

/-- **Stacks 01E1 (2) in `A`-module form.**  For a module `𝒢` on the open `W = Spec(A) ∖ V(J)`
isomorphic to `M̃|_W`, the `A`-module `Hⁱ(W, 𝒢)` is
`Stacks.LocalCohomologySequence.complementCohomologyBase J M i`, the degree-`i` right derived
functor on sheaves on the ambient `Spec(A)` of the sections over `W`.

`Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso` is the comparison, for an
arbitrary scheme and an arbitrary open; the two remaining identifications — that the sections on
the complement of `V(J)` are the sections over `Spec(A) ∖ V(J)`
(`Stacks.Cohomology.ModuleComparison.sectionsOnComplement_eq` and
`Stacks.LocalCohomologySequence.openComplement_zeroLocusSubset`) and that
`complementCohomologyBase` reads the result over `A` — hold by `rfl`. -/
public noncomputable def openCohomologyBaseIsoComplementCohomologyBase (J : Ideal A)
    (M : ModuleCat.{u} A) {G : (complementZeroLocus A J : Scheme).Modules}
    (e : G ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A J).ι)
    (i : ℕ) :
    openCohomologyBase A (complementZeroLocus A J) G i ≅
      Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of A) J M i :=
  (Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)).mapIso
      ((ModuleCat.restrictScalars (complementZeroLocus A J).ι.appTop.hom).mapIso
        (((moduleGlobalSections (complementZeroLocus A J).toScheme).rightDerived i).mapIso e)) ≪≫
    (Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)).mapIso
      ((derivedSectionsOnOpenIso (Spec (CommRingCat.of A)) (complementZeroLocus A J) i).app
        ((tilde.functor (CommRingCat.of A)).obj M)).symm

variable [IsLocalRing A]

/-- For `J ⊆ 𝔪` the open `Spec(A) ∖ V(J)` is contained in the punctured spectrum. -/
public theorem le_complementZeroLocus_maximalIdeal {J : Ideal A} (hJ : J ≤ maximalIdeal A) :
    complementZeroLocus A J ≤ complementZeroLocus A (maximalIdeal A) :=
  (complementZeroLocus_le_complementZeroLocus_iff (maximalIdeal A) J).2
    (hJ.trans Ideal.le_radical)

/-- **The restriction to `Spec(A) ∖ V(J)` of a module on `U` isomorphic to `M̃|_U`.**  For
`J ⊆ 𝔪` the open `V = Spec(A) ∖ V(J)` sits inside `U`, and the restriction of `ℱ` to it is
`M̃|_V`: restricting twice along `V ⟶ U ⟶ Spec(A)` is restricting once along `V ⟶ Spec(A)`, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.homOfLE_ι`. -/
public noncomputable def restrictSmallerIso {J : Ideal A} (hJ : J ≤ maximalIdeal A)
    (M : ModuleCat.{u} A)
    {F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules}
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι) :
    (Scheme.Modules.restrictFunctor
          ((Spec (CommRingCat.of A)).homOfLE (le_complementZeroLocus_maximalIdeal hJ))).obj F ≅
      ((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A J).ι :=
  (Scheme.Modules.restrictFunctor
        ((Spec (CommRingCat.of A)).homOfLE (le_complementZeroLocus_maximalIdeal hJ))).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp
        ((Spec (CommRingCat.of A)).homOfLE (le_complementZeroLocus_maximalIdeal hJ))
        (complementZeroLocus A (maximalIdeal A)).ι).symm.app
      ((tilde.functor (CommRingCat.of A)).obj M)) ≪≫
    (Scheme.Modules.restrictFunctorCongr
      ((Spec (CommRingCat.of A)).homOfLE_ι
        (le_complementZeroLocus_maximalIdeal hJ))).app
      ((tilde.functor (CommRingCat.of A)).obj M)

/-- **The cohomology comparison at a neighbourhood of the formal locus.**  Let `ℱ` be a module on
the punctured spectrum `U` with `ℱ ≅ M̃|_U` for an `A`-module `M`, and let `J ⊆ 𝔪`.  Then the
`A`-module `Hⁱ(Spec(A) ∖ V(J), ℱ|)` — the cohomology of the restriction of `ℱ` to that open, which
is what the source writes `Hⁱ(V, ℱ)` — is
`Stacks.LocalCohomologySequence.complementCohomologyBase J M i`, the `A`-module the finiteness
clause of Stacks 0DXQ is stated about in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodCohomologyFiniteness`.

This is Stacks 01E1 (2), through
`Stacks.Algebraization.openCohomologyBaseIsoComplementCohomologyBase`. -/
public noncomputable def openCohomologyBaseRestrictIso {J : Ideal A} (hJ : J ≤ maximalIdeal A)
    (M : ModuleCat.{u} A)
    {F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules}
    (e : F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι)
    (i : ℕ) :
    openCohomologyBase A (complementZeroLocus A J)
        ((Scheme.Modules.restrictFunctor
          ((Spec (CommRingCat.of A)).homOfLE
            (le_complementZeroLocus_maximalIdeal hJ))).obj F) i ≅
      Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of A) J M i :=
  openCohomologyBaseIsoComplementCohomologyBase J M (restrictSmallerIso hJ M e) i

end Cohomology

end Stacks.Algebraization

end
