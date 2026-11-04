module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GlobalProperOverCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelKernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelNontrivial
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicInvertible
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.RingCatStalk
public import StacksFrontier.RingTheory.Module.Free.RankOneOfQuotient

/-!
# An algebraizing coherent module is locally invertible, and `(𝓛ₙ)` is not algebraizable

The last two steps of the proof sketch of [Stacks, Tag 0EHE] are: an algebraizing coherent module
`𝓛` on the punctured spectrum `U` would have invertible stalks along `U ∩ Y`, hence would be
invertible — so trivial, `A = k[x,y][[t]]` being a UFD — on an open `V` with `U ∩ Y ⊆ V ⊆ U`,
"which would imply `𝓛ₙ ≅ 𝒪_U/Iⁿ𝒪_U`. Since `𝓛₂ ≇ 𝒪_U/I²𝒪_U` by construction we get a
contradiction as desired." This file proves both, and closes the second clause of the tag.

**Local invertibility.** The first half is general, and is stated for an arbitrary locally
Noetherian scheme `X` and quasi-coherent ideal sheaf `𝓘`. If the completion of a coherent
`𝒪_X`-module `𝓛` along `𝓘` is isomorphic to an invertible object of `Coh(X, 𝓘)`, then `𝓛` is
invertible on an open neighbourhood of the support of `𝓘`
(`Stacks.Algebraization.exists_isInvertibleModule_restrict_of_isInvertibleAdic_completionIso`).
At a point `y` of that support the stalk `𝓛_y` is free, by the closing remark of
[Stacks, Tag 0EL6] in the form `Stacks.Algebraization.free_stalk_of_forall_pushforward_iso`, and
it is free *of rank one*, because the first adic quotient `𝓛_y / 𝓘_y 𝓛_y` is the stalk of an
invertible module and hence cyclic: a free module whose quotient by a proper ideal is cyclic free
is cyclic (`Stacks.FreeOfAdicQuotients.nonempty_linearEquiv_self_of_quotient_linearEquiv`). The
trivializing germ then spreads out to a neighbourhood by [Stacks, Tag 0B8J], and the union of all
trivializing opens is the `V` wanted.

**The level comparison.** The second half is the identification of the terms of the completion
with direct images of pullbacks. The closed immersion `Spec(A/tⁿA) ∩ U ⟶ U` has kernel ideal sheaf
`(I𝒪_U)ⁿ` (`Stacks.Algebraization.NonAlgebraizableExample.ker_levelStructureMap`), which is
exactly the hypothesis of [Stacks, Tag 0EL1] in the form
`Stacks.Algebraization.idealQuotientPushforwardIso`, so `𝓛/Iⁿ𝓛` is the direct image of the
pullback of `𝓛`; factoring the structure map through `V` — which is possible because the image of
`Spec(A/tⁿA) ∩ U` is `U ∩ Y` — writes it as the direct image of the pullback of `𝓛|_V`.

**The conclusion.** On `V` the module `𝓛` is trivial, `Pic` of every open of `Spec(A)` vanishing
(`Stacks.Algebraization.NonAlgebraizableExample.isTrivial_of_isInvertible_ambientOpen`), so the
level-two term of the completion is the direct image of `𝒪`; direct image along a closed immersion
is fully faithful ([Stacks, Tag 08KS]), so `𝓛₂ ≅ 𝒪`, which
`Stacks.Algebraization.NonAlgebraizableExample.not_isTrivial_levelModule_two` forbids.

## Main results

* `Stacks.Algebraization.nonempty_linearEquiv_stalk_of_isInvertibleAdic_completionIso` — the
  stalk of an algebraizing coherent module at a point of the support of `𝓘` is free of rank one.
* `Stacks.Algebraization.exists_isInvertibleModule_restrict_of_isInvertibleAdic_completionIso` —
  **local invertibility of an algebraizing module.**
* `Stacks.Algebraization.NonAlgebraizableExample.idealPowerQuotientIsoPushforwardPullbackOnOpen` —
  **the level comparison**: `𝓛/Iⁿ𝓛` is the direct image along `levelStructureMap k n` of the
  pullback of `𝓛|_V`.
* `Algebraization.NonAlgebraizableExample.not_isCompletionOfCoherent_levelCoherentAdicSystem` —
  **`(𝓛ₙ)` is not the completion of a coherent `𝒪_U`-module**, for every choice of `a` and `φ`.

## Implementation notes

The two coherent-module spellings have to be kept apart. `AlgebraicGeometry.Scheme.Modules` is a
`def`, not an abbreviation, so the projection `L.obj` of an object of
`AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf` has type
`SheafOfModules X.ringCatSheaf` and instance search does not find the module structure on its
stalks, which is stated at the `X.Modules` spelling. Every statement about a stalk of `L.obj`
below therefore writes `show X.Modules from L.obj`; without it the `Module` instance on
`TopCat.Presheaf.stalk L.obj.val.presheaf y` is not synthesized.

`Stacks.Algebraization.exists_isInvertibleModule_restrict_of_forall_mem_isoUnit` takes the
supremum of *all* opens trivializing the module rather than a chosen family: the local
trivializations are only given at the points of the subset, and a chosen family indexed by those
points would not cover the supremum, whose points need not lie in the subset.

The factorization of `levelStructureMap k 2` through `V` is
`AlgebraicGeometry.IsOpenImmersion.lift`, which needs the image to be contained in `V`;
`Stacks.Algebraization.NonAlgebraizableExample.range_levelStructureMap` computes that image from
`exists_subschemeIso_levelOpen`, the range of a morphism being unchanged by precomposition with
an isomorphism.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EL6](https://stacks.math.columbia.edu/tag/0EL6)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-- An invertible module on a scheme is finite locally free, in the pointwise spelling. -/
public theorem isFiniteLocallyFree_of_isInvertibleModule {X : Scheme.{u}} (M : X.Modules)
    (hM : Stacks.Ample.IsInvertibleModule X M) :
    AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree M := by
  have h1 : M.IsFiniteLocallyFreeOfRank 1 :=
    (Stacks.Modules.isFiniteLocallyFreeOfRank_iff_localGenerators M 1).mpr
      (Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X M)
  intro x
  obtain ⟨U, hxU, he⟩ := h1 x
  exact ⟨U, hxU, ULift (Fin 1), inferInstance, he⟩

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (L : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (F : Stacks.Coherent.CoherentAdicSystems I)

/-- The underlying module of a coherent module is quasi-coherent. -/
private theorem isQuasicoherent_obj_of_coherent {X : Scheme.{u}}
    (L : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (show X.Modules from L.obj).IsQuasicoherent := by
  have : L.obj.IsCoherent := L.property
  exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L.obj).1

/-- The `n`-th adic quotient of `L` is the `n`-th term of its completion, which is isomorphic to
the `n`-th term of `F` by `e`. -/
private def idealPowerQuotientIsoOfCompletionIso
    (e : ((completionFunctor X I).obj L).obj ≅ F.obj) (n : ℕ) :
    idealPowerQuotient I (n + 1) L.obj ≅ F.obj.obj (op n) :=
  eqToIso (completionFunctor_obj X I L n).symm ≪≫ e.app (op n)

/-- Each term of the completion of `L` is the direct image of a finite locally free module on the
corresponding infinitesimal neighbourhood, when that completion is isomorphic to an invertible
coherent adic system. -/
public theorem exists_isFiniteLocallyFree_pushforward_iso_of_isInvertibleAdic
    (hF : Stacks.Coherent.IsInvertibleAdic I F)
    (e : ((completionFunctor X I).obj L).obj ≅ F.obj) (n : ℕ) :
    ∃ N : (I ^ (n + 1)).subscheme.Modules,
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree N ∧
        Nonempty (idealPowerQuotient I (n + 1) L.obj ≅
          (Scheme.Modules.pushforward (I ^ (n + 1)).subschemeι).obj N) := by
  obtain ⟨N, hN, ⟨f⟩⟩ := hF n
  refine ⟨N, isFiniteLocallyFree_of_isInvertibleModule N hN, ⟨?_⟩⟩
  exact idealPowerQuotientIsoOfCompletionIso I L F e n ≪≫ f.symm

/-- The stalk of an algebraizing coherent module at a point of the support is free. -/
public theorem free_stalk_of_isInvertibleAdic_completionIso
    (hF : Stacks.Coherent.IsInvertibleAdic I F)
    (e : ((completionFunctor X I).obj L).obj ≅ F.obj) {y : X} (hy : y ∈ I.support) :
    Module.Free (ToType (X.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk (show X.Modules from L.obj).val.presheaf y)) :=
  have : L.obj.IsCoherent := L.property
  have := isQuasicoherent_obj_of_coherent L
  have : L.obj.IsFinitePresentation := isFinitePresentation_of_isCoherent L.obj
  free_stalk_of_forall_pushforward_iso I L.obj hy
    (exists_isFiniteLocallyFree_pushforward_iso_of_isInvertibleAdic I L F hF e)

omit [IsLocallyNoetherian X] in
/-- If the `t`-th adic quotient of a quasi-coherent module is the direct image of an **invertible**
module on the closed subscheme cut out by `𝓘 ^ t`, then at a point `y` of the support of `𝓘` the
quotient `𝒢_y / 𝓘_y ^ t 𝒢_y` is isomorphic to `𝒪_{X,y} / 𝓘_y ^ t`. -/
public theorem nonempty_quotient_stalk_linearEquiv_of_pushforward_iso (J : X.IdealSheafData)
    (G : X.Modules) [G.IsQuasicoherent] {t : ℕ} (ht : t ≠ 0) {y : X} (hy : y ∈ J.support)
    (N : (J ^ t).subscheme.Modules)
    (hN : Stacks.Ample.IsInvertibleModule (J ^ t).subscheme N)
    (e : idealPowerQuotient J t G ≅
      (Scheme.Modules.pushforward (J ^ t).subschemeι).obj N) :
    Nonempty (((modulesStalkFunctor X y).obj G ⧸
        (IdealSheafData.stalk J y ^ t •
          (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj G))))
      ≃ₗ[X.presheaf.stalk y] (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t)) := by
  classical
  have hind : Topology.IsInducing (ConcreteCategory.hom ((J ^ t).subschemeι).base) :=
    (IsClosedImmersion.isClosedEmbedding ((J ^ t).subschemeι)).isInducing
  set z : (J ^ t).subscheme := idealPowSubschemePoint J ht y hy
  let _ : Module (X.presheaf.stalk y) (N.presheaf.stalk z) :=
    Module.compHom _ (((J ^ t).subschemeι).stalkMap z).hom
  let _ : Module (X.presheaf.stalk y) ((J ^ t).subscheme.presheaf.stalk z) :=
    Module.compHom _ (((J ^ t).subschemeι).stalkMap z).hom
  have f₃ : ((Scheme.Modules.pushforward ((J ^ t).subschemeι)).obj N).presheaf.stalk y
      ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk z :=
    stalkPushforwardModuleLinearEquiv ((J ^ t).subschemeι) N z hind
  have fL : ((modulesStalkFunctor X y).obj G ⧸
        (IdealSheafData.stalk J y ^ t •
          (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj G))))
      ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk z :=
    ((idealPowerQuotientStalkLinearEquiv J t G y).trans
      ((modulesStalkFunctor X y).mapIso e).toLinearEquiv).trans f₃
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (J ^ t).subscheme.presheaf
      (J ^ t).subscheme.ringCatSheaf.2 N := hN
  obtain ⟨p⟩ := Stacks.InvertibleStalk.nonempty_linearEquiv_stalk N z
  have p' : N.presheaf.stalk z ≃ₗ[X.presheaf.stalk y] (J ^ t).subscheme.presheaf.stalk z :=
    { toFun := p
      map_add' := fun a b => p.map_add a b
      map_smul' := fun r a => p.map_smul ((((J ^ t).subschemeι).stalkMap z).hom r) a
      invFun := p.symm
      left_inv := p.left_inv
      right_inv := p.right_inv }
  have q : (X.presheaf.stalk y ⧸ IdealSheafData.stalk (J ^ t) y)
      ≃ₗ[X.presheaf.stalk y] (J ^ t).subscheme.presheaf.stalk z :=
    IdealSheafData.subschemeStalkQuotLinearEquiv (J ^ t) z
  exact ⟨(fL.trans (p'.trans q.symm)).trans
    (Submodule.quotEquivOfEq _ _ (IdealSheafData.stalk_pow J t y))⟩

/-- **The stalk of an algebraizing coherent module at a point of `U ∩ Y` is free of rank one.** -/
public theorem nonempty_linearEquiv_stalk_of_isInvertibleAdic_completionIso
    (hF : Stacks.Coherent.IsInvertibleAdic I F)
    (e : ((completionFunctor X I).obj L).obj ≅ F.obj) {y : X} (hy : y ∈ I.support) :
    Nonempty ((modulesStalkFunctor X y).obj L.obj
      ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y) := by
  have : L.obj.IsCoherent := L.property
  have := isQuasicoherent_obj_of_coherent L
  have hfree : Module.Free (ToType (X.presheaf.stalk y))
      (ToType ((modulesStalkFunctor X y).obj L.obj)) :=
    free_stalk_of_isInvertibleAdic_completionIso I L F hF e hy
  obtain ⟨N, hN, ⟨f⟩⟩ := hF 0
  have hmain : Nonempty (((modulesStalkFunctor X y).obj L.obj ⧸
        (IdealSheafData.stalk I y ^ 1 •
          (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj L.obj))))
      ≃ₗ[X.presheaf.stalk y] (X.presheaf.stalk y ⧸ IdealSheafData.stalk I y ^ 1)) := by
    refine nonempty_quotient_stalk_linearEquiv_of_pushforward_iso I L.obj one_ne_zero hy N hN ?_
    exact idealPowerQuotientIsoOfCompletionIso I L F e 0 ≪≫ f.symm
  have htop : IdealSheafData.stalk I y ^ 1 ≠ ⊤ := by
    rw [pow_one]
    exact fun hc => (IdealSheafData.stalk_eq_top_iff_notMem_support I y).mp hc hy
  exact Stacks.FreeOfAdicQuotients.nonempty_linearEquiv_self_of_quotient_linearEquiv htop hmain

/-! ### Spreading a trivialized stalk out to a neighbourhood -/

section Spread

variable {Y : Scheme.{u}}

/-- A trivialization of `M` over an open `U`, read as a trivialization of its restriction to the
open subscheme `U`. -/
public def restrictUnitIsoOfOverIso (U : Y.Opens) {M : Y.Modules}
    (e : M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    U.sheafOfModulesEquivOverUnit Y.ringCatSheaf

/-- A trivialization of the restriction of `M` to an open subscheme `U`, read as a trivialization
of `M` over `U`. -/
public def overUnitIsoOfRestrictIso (U : Y.Opens) {M : Y.Modules}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm)

/-- **Local trivializations along a subset combine to one open on which the module is
invertible.** -/
public theorem exists_isInvertibleModule_restrict_of_forall_mem_isoUnit (M : Y.Modules)
    (Z : Set Y) (h : ∀ x ∈ Z, ∃ V : Y.Opens, x ∈ V ∧
      Nonempty (M.over V ≅ SheafOfModules.unit (Y.ringCatSheaf.over V))) :
    ∃ V : Y.Opens, Z ⊆ V ∧
      Stacks.Ample.IsInvertibleModule V.toScheme (M.restrict V.ι) := by
  classical
  set T := {U : Y.Opens // Nonempty (M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U))}
  set V : Y.Opens := ⨆ U : T, U.1
  refine ⟨V, ?_,
    Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over
      V.toScheme (M.restrict V.ι) fun x => ?_⟩
  · intro x hx
    obtain ⟨U, hxU, he⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, he⟩, hxU⟩
  · obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    set W : V.toScheme.Opens := V.ι ⁻¹ᵁ U.1
    set f := V.ι ∣_ U.1
    have he : (M.restrict V.ι).restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
      ((Scheme.Modules.restrictFunctorComp W.ι V.ι).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι V.ι U.1).symm).app M ≪≫
        (Scheme.Modules.restrictFunctorComp f U.1.ι).app M ≪≫
        (Scheme.Modules.restrictFunctor f).mapIso
          (restrictUnitIsoOfOverIso U.1 U.2.some) ≪≫
        Scheme.Modules.restrictUnitIso f
    exact ⟨W, hxU, ⟨overUnitIsoOfRestrictIso W he⟩⟩

end Spread

/-! ### Local invertibility of an algebraizing module -/

/-- **Local invertibility of an algebraizing module.** If the completion of a coherent module `L`
on a locally Noetherian scheme is isomorphic to an invertible object of `Coh(X, 𝓘)`, then there is
an open `V` containing the support of `𝓘` on which `L` is invertible. -/
public theorem exists_isInvertibleModule_restrict_of_isInvertibleAdic_completionIso
    (hF : Stacks.Coherent.IsInvertibleAdic I F)
    (e : ((completionFunctor X I).obj L).obj ≅ F.obj) :
    ∃ V : X.Opens, (I.support : Set X) ⊆ V ∧
      Stacks.Ample.IsInvertibleModule V.toScheme ((show X.Modules from L.obj).restrict V.ι) := by
  have : L.obj.IsCoherent := L.property
  have : (show X.Modules from L.obj).IsFinitePresentation :=
    isFinitePresentation_of_isCoherent L.obj
  refine exists_isInvertibleModule_restrict_of_forall_mem_isoUnit L.obj _ fun y hy => ?_
  obtain ⟨p⟩ := nonempty_linearEquiv_stalk_of_isInvertibleAdic_completionIso I L F hF e hy
  obtain ⟨U, hyU, ⟨iso⟩⟩ := Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis
    (ρ := ULift.{u} (Fin 1)) (show X.Modules from L.obj) y
    ((Module.Basis.singleton (ULift.{u} (Fin 1)) (ToType (X.presheaf.stalk y))).map p.symm)
  exact ⟨U, hyU, ⟨iso ≪≫ CategoryTheory.Limits.coproductUniqueIso _⟩⟩

end Stacks.Algebraization

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-! ### The level-`n` comparison -/

/-- **Stacks Project, Tag 0EHE (the level comparison).** For a quasi-coherent `𝒪_U`-module `𝓛`
the term `𝓛 / Iⁿ𝓛` is the direct image along `levelStructureMap k n` of the pullback of `𝓛`: the
closed immersion `Spec(A/tⁿA) ∩ U ⟶ U` has kernel ideal sheaf `(I𝒪_U)ⁿ`
(`ker_levelStructureMap`), which is exactly the hypothesis of [Stacks, Tag 0EL1]. -/
@[stacks 0EHE "L/I^n L is the direct image along Spec(A/t^n A) ∩ U → U of the pullback of L"]
public def idealPowerQuotientIsoPushforwardPullback (n : ℕ)
    (M : (situation k).U.toScheme.Modules) [M.IsQuasicoherent] :
    idealPowerQuotient (idealOnOpen (situation k)) n M ≅
      (Scheme.Modules.pushforward (levelStructureMap k n)).obj
        ((Scheme.Modules.pullback (levelStructureMap k n)).obj M) :=
  idealQuotientPushforwardIso (idealOnOpen (situation k)) n M (levelStructureMap k n)
    (ker_levelStructureMap k n)

/-- **Stacks Project, Tag 0EHE (the level comparison through an intermediate open).** The same
identification, with the pullback taken in two steps through an open `V ⊆ U` that
`levelStructureMap k n` factors through: `𝓛 / Iⁿ𝓛` is the direct image of the pullback of
`𝓛|_V`. -/
@[stacks 0EHE "L/I^n L is the direct image of the pullback of L restricted to a smaller open"]
public def idealPowerQuotientIsoPushforwardPullbackOnOpen (n : ℕ)
    (M : (situation k).U.toScheme.Modules) [M.IsQuasicoherent]
    (V : (situation k).U.toScheme.Opens) (f : (levelOpen k n).toScheme ⟶ V.toScheme)
    (hf : f ≫ V.ι = levelStructureMap k n) :
    idealPowerQuotient (idealOnOpen (situation k)) n M ≅
      (Scheme.Modules.pushforward (levelStructureMap k n)).obj
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback V.ι).obj M)) :=
  idealPowerQuotientIsoPushforwardPullback k n M ≪≫
    (Scheme.Modules.pushforward (levelStructureMap k n)).mapIso
      (((Scheme.Modules.pullbackComp f V.ι).app M ≪≫
        (Scheme.Modules.pullbackCongr hf).app M).symm)

/-- The image of `Spec(A/tⁿA) ∩ U ⟶ U` is the punctured closed fibre `U ∩ Y`, for `n ≥ 1`. -/
public theorem range_levelStructureMap {n : ℕ} (hn : n ≠ 0) :
    Set.range (levelStructureMap k n) =
      ((idealOnOpen (situation k)).support : Set (situation k).U.toScheme) := by
  obtain ⟨ee, hee⟩ := exists_subschemeIso_levelOpen k n
  have hcomp : ee.inv ≫ (idealOnOpen (situation k) ^ n).subschemeι = levelStructureMap k n := by
    rw [← hee, ← Category.assoc, ee.inv_hom_id, Category.id_comp]
  have hpt1 : ∀ w, levelStructureMap k n (ee.hom w) =
      (idealOnOpen (situation k) ^ n).subschemeι w := fun w => by rw [← hee]; rfl
  have hpt2 : ∀ z, (idealOnOpen (situation k) ^ n).subschemeι (ee.inv z) =
      levelStructureMap k n z := fun z => by rw [← hcomp]; rfl
  have h1 : Set.range (levelStructureMap k n) =
      Set.range (idealOnOpen (situation k) ^ n).subschemeι := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro _ ⟨z, rfl⟩; exact ⟨ee.inv z, hpt2 z⟩
    · rintro _ ⟨w, rfl⟩; exact ⟨ee.hom w, hpt1 w⟩
  rw [h1, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.support_pow (idealOnOpen (situation k)) n hn]

/-! ### The conclusion -/

/-- **Stacks Project, Tag 0EHE (the family is not algebraizable).** The object `(𝓛ₙ)` of
`Coh(U, I𝒪_U)` is not the completion of any coherent `𝒪_U`-module, for every choice of the
coefficients `aₘ` and the exponents `φ(m)`.

This is the source's first proof. An algebraizing coherent module `𝓛` has invertible stalks along
`U ∩ Y`, so it is invertible on an open `V` with `U ∩ Y ⊆ V ⊆ U`
(`exists_isInvertibleModule_restrict_of_isInvertibleAdic_completionIso`); there it is trivial,
`A = k[x,y][[t]]` being a unique factorization domain
(`isTrivial_of_isInvertible_ambientOpen`); the level-two term of its completion is the direct
image along the closed immersion of the punctured spectrum of `A/t²A` of the pullback of `𝓛|_V`
(`idealPowerQuotientIsoPushforwardPullbackOnOpen`), hence of the structure sheaf, and direct
image along a closed immersion is fully faithful, so `𝓛₂ ≅ 𝒪`; and
`not_isTrivial_levelModule_two` forbids that. -/
@[stacks 0EHE "the family (L_n) is not the completion of a coherent O_U-module"]
public theorem not_isCompletionOfCoherent_levelCoherentAdicSystem (a : ℕ → PlaneRing k)
    (φ : ℕ → ℕ) :
    ¬ IsCompletionOfCoherent (idealOnOpen (situation k)) (levelCoherentAdicSystem k a φ) := by
  rintro ⟨L, ⟨e⟩⟩
  have : L.obj.IsCoherent := L.property
  have := Stacks.Algebraization.isQuasicoherent_obj_of_coherent L
  obtain ⟨V, hV, hLV⟩ := exists_isInvertibleModule_restrict_of_isInvertibleAdic_completionIso
    (idealOnOpen (situation k)) L (levelCoherentAdicSystem k a φ)
    (isInvertibleAdic_levelCoherentAdicSystem k a φ) e
  obtain ⟨triv⟩ := Stacks.PicardTrivialOpenUFD.hasTrivialPicard_of_iso
    ((situation k).U.ι.isoImage V).symm
    (fun M hM => isTrivial_of_isInvertible_ambientOpen k M hM) _ hLV
  have hrange : Set.range (levelStructureMap k 2) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, range_levelStructureMap k (two_ne_zero)]
    exact hV
  have hf : IsOpenImmersion.lift V.ι (levelStructureMap k 2) hrange ≫ V.ι =
      levelStructureMap k 2 := IsOpenImmersion.lift_fac _ _ _
  have c2 : idealPowerQuotient (idealOnOpen (situation k)) 2 L.obj ≅
      (Scheme.Modules.pushforward (levelStructureMap k 2)).obj (levelModule k a φ 2) :=
    Stacks.Algebraization.idealPowerQuotientIsoOfCompletionIso _ L _ e 1
  refine not_isTrivial_levelModule_two k a φ ⟨?_⟩
  refine ((Stacks.ClosedImmersion.fullyFaithfulPushforward
      (levelStructureMap k 2)).preimageIso
      ((idealPowerQuotientIsoPushforwardPullbackOnOpen k 2 L.obj V _ hf).symm ≪≫ c2)).symm ≪≫ ?_
  exact (Scheme.Modules.pullback (IsOpenImmersion.lift V.ι (levelStructureMap k 2) hrange)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.obj).symm ≪≫ triv) ≪≫
    Stacks.PicardTrivialOpenUFD.pullbackUnitIso _

end Stacks.Algebraization.NonAlgebraizableExample

end
