module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.SliceAffineDualAmplitude

/-!
# The duality amplitude on the slice sites over the basic opens of one affine open

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and
`V ⊆ X` an affine open. `Stacks.Duality.exists_forall_isLE_derivedSheafHomSlice` and its companion
give, for each affine open `W`, an interval `[a', b']` with

`A ∈ D^{≥q}  ⟹  R𝓗om_{𝒪_X|_W}(A, K|_W) ∈ D^{≤b'-q}`,
`A ∈ D^{≤q}  ⟹  R𝓗om_{𝒪_X|_W}(A, K|_W) ∈ D^{≥a'-q}`

on the slice site `Opens(X)/W`, the interval depending on `W`. A dévissage over a covering of `X`
has to fix a truncation level and a pseudo-coherence level *before* choosing the member of the
covering it works over, and both levels are governed by `b' - a'`; so a bound depending on the
member is of no use to it. This file supplies one interval good for **every basic open of a fixed
affine open at once**:

`Stacks.Duality.exists_forall_basicOpen_isLE_derivedSheafHomSlice` and
`Stacks.Duality.exists_forall_basicOpen_isGE_derivedSheafHomSlice`.

Since the basic opens of the sections over `V` form a basis of `V`, and the affine opens of `X`
cover it, that is enough to choose the two levels first.

## The proof

Over `V` the complex `K` has a dualizing model `ω` over `Γ(X, V)`
(`Stacks.Duality.HasDualizingModelOn`), and `ω` has an injective amplitude interval `[a, b]`
depending only on `ω`. Over the basic open `D(f)` of a section `f` of `𝒪_X` over `V` the model is
the extension of scalars of `ω` along `Γ(X, V) ⟶ Γ(X, D(f))`
(`Stacks.Duality.nonempty_iso_extendScalars_basicOpen`), and that map is a localization
(`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`), along which the *same* interval
`[a, b]` remains an injective amplitude interval: a bounded complex of injective `Γ(X, V)`-modules
is carried degreewise, and in the same degrees, to a bounded complex of injective
`Γ(X, D(f))`-modules, by [Stacks, Tag 0A6I]. That is
`Stacks.Duality.hasInjectiveAmplitude_extendScalars_of_isLocalization`, the form of
`AlgebraicGeometry.AffineExt.hasInjectiveAmplitude_extD_locMap` that an abstract localization
rather than a localization away from one element gives.

With the interval in hand the two bounds are
`Stacks.Duality.isLE_derivedSheafHomSlice_of_hasInjectiveAmplitude` and its companion, which are
`Stacks.Duality.exists_forall_isLE_derivedSheafHomSlice` and
`Stacks.Duality.exists_forall_isGE_derivedSheafHomSlice` with the dualizing model and its
amplitude interval supplied rather than chosen: the quantifier over the interval has to be moved
outside the quantifier over the open, and a bound obtained from a model chosen inside the proof
cannot be compared with one obtained from another.

## Main results

* `Stacks.Duality.hasInjectiveAmplitude_extendScalars_of_isLocalization`: extension of scalars
  along a localization of a Noetherian ring keeps an injective amplitude interval.
* `Stacks.Duality.isLE_derivedSheafHomSlice_of_hasInjectiveAmplitude` and
  `Stacks.Duality.isGE_derivedSheafHomSlice_of_hasInjectiveAmplitude`: the two slice bounds at a
  given dualizing model and a given injective amplitude interval for it.
* `Stacks.Duality.exists_forall_basicOpen_isLE_derivedSheafHomSlice` and
  `Stacks.Duality.exists_forall_basicOpen_isGE_derivedSheafHomSlice`: **the two bounds with one
  interval for all the basic opens of a fixed affine open.**

## References

* [Stacks Project, Tag 0A5S](https://stacks.math.columbia.edu/tag/0A5S)
* [Stacks Project, Tag 0A6I](https://stacks.math.columbia.edu/tag/0A6I)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHom`,
--   `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-! ### Injective amplitude along a localization -/

/-- **Extension of scalars along a localization keeps an injective amplitude interval.** For `A`
Noetherian, `B` a localization of `A` and `L` an object of `D(A)` with injective amplitude in
`[a, b]`, the object `L ⊗_A B` of `D(B)` has injective amplitude in the same `[a, b]`.

A bounded complex of injective `A`-modules representing `L` is carried degreewise, and in the
same degrees, to a bounded complex of injective `B`-modules representing `L ⊗_A B`: the terms
stay injective by [Stacks, Tag 0A6I], the bounds survive because an additive functor carries
zero objects to zero objects, and the image complex still represents the extension because
extension of scalars along a localization is exact.

This is `AlgebraicGeometry.AffineExt.hasInjectiveAmplitude_extD_locMap` with the localization
abstract instead of a localization away from a single element, which is the form the basic opens
of an affine open of a scheme present. -/
theorem hasInjectiveAmplitude_extendScalars_of_isLocalization {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] (S : Submonoid A) [IsLocalization S B]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))]
    (L : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hL : StacksDraft.InjectiveDimension.HasInjectiveAmplitude L a b) :
    StacksDraft.InjectiveDimension.HasInjectiveAmplitude
      ((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory.obj L) a b := by
  obtain ⟨I, hge, hle, hinj, ⟨eI⟩⟩ := hL
  refine ⟨((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I,
    Dualizing.isStrictlyGE_mapHomologicalComplex _ I a hge,
    Dualizing.isStrictlyLE_mapHomologicalComplex _ I b hle, fun i => ?_, ⟨?_⟩⟩
  · have := hinj i
    exact Dualizing.injective_extendScalars.{u, u} S (I.X i)
  · exact (ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory.mapIso eI ≪≫
      (Functor.mapDerivedCategoryFactors
        (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))).app I

/-! ### The slice bounds at a given model and a given interval -/

variable {X : Scheme.{u}}

section Given

variable [IsLocallyNoetherian X] (W : X.Opens) (hW : IsAffineOpen W)

/-- **The transport of `K|_W` is the derived sheafification of a given model.** This is
`Stacks.Duality.exists_isDualizingComplex_iso_sliceSpecFunctor_restrict` with the model and the
isomorphism of `Stacks.Duality.HasDualizingModelOn` supplied rather than chosen. -/
def sliceSpecFunctorRestrictTildeIso {K : DerivedCategory X.Modules}
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, W)))
    (e : (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, W) ⋙
        Scheme.Modules.restrictFunctor hW.isoSpec.hom).mapDerivedCategory.obj ω) :
    (sliceSpecFunctor W hW).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(X, W)).mapDerivedCategory.obj ω :=
  sliceSpecFunctorRestrictIso W hW K ≪≫
    (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapDerivedCategory.mapIso e ≪≫
      (Stacks.AffineTilde.tildeIsoSpecCancelIso hW).app ω

/-- The transport of `R𝓗om(A, K|_W)` is `R𝓗om(M~, ω~)` once `K|_W` and `A` are transported. -/
private def sliceDerivedSheafHomTildeIso {K : DerivedCategory X.Modules}
    {ω M : DerivedCategory (ModuleCat.{u} Γ(X, W))}
    {A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))}
    (e : (sliceSpecFunctor W hW).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(X, W)).mapDerivedCategory.obj ω)
    (eA : (tilde.functor Γ(X, W)).mapDerivedCategory.obj M ≅ (sliceSpecFunctor W hW).obj A) :=
  sliceSpecDerivedSheafHomIso W hW A _ ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).obj
      (op ((sliceSpecFunctor W hW).obj A))).mapIso e ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).mapIso (Iso.op eA)).app
      ((tilde.functor Γ(X, W)).mapDerivedCategory.obj ω)

/-- **The bound above, at a given injective amplitude interval.** Let `X` be locally Noetherian,
`W ⊆ X` affine, and let the transport of `K|_W` to `Spec Γ(X, W)` be the derived sheafification of
an object `ω` of `D(Γ(X, W))` with injective amplitude in `[a, b]`. Then for every object `A` of
the derived category of `𝒪_X|_W`-modules on `Opens(X)/W` whose transport has coherent cohomology
sheaves and which has no cohomology below `q`, the object `R𝓗om_{𝒪_X|_W}(A, K|_W)` has no
cohomology above `b - q`.

This is `Stacks.Duality.exists_forall_isLE_derivedSheafHomSlice` with the interval given, which
is what lets one interval serve a family of opens. Over `Spec Γ(X, W)` the bound is
`AlgebraicGeometry.AffineExt.isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude`, the
`Ext`-presheaf bound of [Stacks, Tag 0A88]; it is read back on the slice site by
`Stacks.Duality.isLE_of_isLE_sliceSpecFunctor_obj`. -/
theorem isLE_derivedSheafHomSlice_of_hasInjectiveAmplitude {K : DerivedCategory X.Modules}
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, W))) (a b : ℤ)
    (hab : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b)
    (e : (sliceSpecFunctor W hW).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(X, W)).mapDerivedCategory.obj ω)
    (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) (q : ℤ)
    (hAcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
      ((sliceSpecFunctor W hW).obj A)).IsCoherent)
    (hAq : A.IsGE q) :
    ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
      W).derivedSheafHomBifunctor.obj (op A)).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
          K)).IsLE (b - q) := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨M, hM, ⟨eA⟩⟩ :=
    exists_iso_tilde_of_isCoherent_homology Γ(X, W) ((sliceSpecFunctor W hW).obj A) hAcoh
  have hΦA : ((sliceSpecFunctor W hW).obj A).IsGE q :=
    CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ _ q
      (CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ A q hAq)
  have hMq : M.IsGE q := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    refine (StandardModel.isZero_homology_mapDerivedCategory_obj_iff _ M i).1 ?_
    exact IsZero.of_iso ((DerivedCategory.isGE_iff _ q).1 hΦA i hi)
      ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).mapIso eA)
  have h :=
    AlgebraicGeometry.AffineExt.isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude
      Γ(X, W) M ω q a b hMq hab
  refine isLE_of_isLE_sliceSpecFunctor_obj W hW _ (b - q) ?_
  refine DerivedCategory.TStructure.t.isLE_of_iso
    (sliceDerivedSheafHomTildeIso W hW e eA).symm (b - q)

/-- **The bound below, at a given injective amplitude interval.** The companion of
`Stacks.Duality.isLE_derivedSheafHomSlice_of_hasInjectiveAmplitude`, with the lower end of the
interval; over `Spec Γ(X, W)` the bound is read on the module side,
`StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude`, and carried across the
comparison of [Stacks, Tag 0A88], which is invertible because the cohomology modules of the
model are finite and `ω` has finite injective dimension. -/
theorem isGE_derivedSheafHomSlice_of_hasInjectiveAmplitude {K : DerivedCategory X.Modules}
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, W))) (a b : ℤ)
    (hab : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b)
    (e : (sliceSpecFunctor W hW).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(X, W)).mapDerivedCategory.obj ω)
    (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over W))) (q : ℤ)
    (hAcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).obj
      ((sliceSpecFunctor W hW).obj A)).IsCoherent)
    (hAq : A.IsLE q) :
    ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
      W).derivedSheafHomBifunctor.obj (op A)).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
          K)).IsGE (a - q) := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨M, hM, ⟨eA⟩⟩ :=
    exists_iso_tilde_of_isCoherent_homology Γ(X, W) ((sliceSpecFunctor W hW).obj A) hAcoh
  have hΦA : ((sliceSpecFunctor W hW).obj A).IsLE q :=
    have h1 : (((Scheme.Modules.overEquiv W).functor.mapDerivedCategory).obj A).IsLE q :=
      Stacks.Homology.isLE_mapDerivedCategory_obj _ A q
    Stacks.Homology.isLE_mapDerivedCategory_obj _ _ q
  have hMq : M.IsLE q := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    refine (StandardModel.isZero_homology_mapDerivedCategory_obj_iff _ M i).1 ?_
    exact IsZero.of_iso (DerivedCategory.isZero_of_isLE _ q i hi)
      ((DerivedCategory.homologyFunctor (Spec Γ(X, W)).Modules i).mapIso eA)
  have hRHom : ((StacksDraft.DerivedHom.derivedHomAdjunction
      (R := (Γ(X, W) : Type u))).hom.obj (op M, ω)).IsGE (a - q) :=
    StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude _ M ω q a b hMq hab
  have hiso : IsIso (affineDerivedTildeHomComparison Γ(X, W) M ω) :=
    isIso_affineDerivedTildeHomComparison_of_finite_homology Γ(X, W) M ω hM ⟨a, b, hab⟩
  have hspec := CategoryTheory.Functor.isGE_obj_mapDerivedCategory
    (tilde.functor Γ(X, W)) _ (a - q) hRHom
  have h : (((Stacks.SheafOfModules.derivedSheafHom (Spec Γ(X, W)).sheaf).obj
      (op ((tilde.functor Γ(X, W)).mapDerivedCategory.obj M))).obj
        ((tilde.functor Γ(X, W)).mapDerivedCategory.obj ω)).IsGE (a - q) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (asIso (affineDerivedTildeHomComparison Γ(X, W) M ω)) (a - q)
  refine isGE_of_isGE_sliceSpecFunctor_obj W hW _ (a - q) ?_
  refine DerivedCategory.TStructure.t.isGE_of_iso
    (sliceDerivedSheafHomTildeIso W hW e eA).symm (a - q)

end Given

/-! ### One interval for all the basic opens of an affine open -/

section BasicOpen

variable [IsLocallyNoetherian X]

/-- **Duality against a dualizing complex carries `D^{≥q}` into `D^{≤b-q}` on the slice site over
every basic open of a fixed affine open, with one `b`.** Let `X` be a locally Noetherian scheme,
`K` a dualizing complex on it and `V ⊆ X` an affine open. There is an integer `b`, depending only
on `K` and `V`, such that for every section `f` of `𝒪_X` over `V` and every object `A` of the
derived category of `𝒪_X|_{D(f)}`-modules on `Opens(X)/D(f)` whose transport to
`Spec Γ(X, D(f))` has coherent cohomology sheaves and which has no cohomology below `q`, the
object `R𝓗om_{𝒪_X|_{D(f)}}(A, K|_{D(f)})` has no cohomology above `b - q`.

`b` is the upper end of an injective amplitude interval for the dualizing model of `K` over
`Γ(X, V)`; over `D(f)` the model is the extension of scalars of that one along a localization,
which keeps the interval
(`Stacks.Duality.hasInjectiveAmplitude_extendScalars_of_isLocalization`). The basic opens of `V`
being a basis of `V`, this is the form in which a dévissage can fix its truncation and
pseudo-coherence levels before choosing the open it works over. -/
theorem exists_forall_basicOpen_isLE_derivedSheafHomSlice (V : X.affineOpens)
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    ∃ b : ℤ, ∀ (f : Γ(X, V.1))
      (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over (X.basicOpen f)))) (q : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, X.basicOpen f)).Modules i).obj
        ((sliceSpecFunctor (X.basicOpen f) (V.2.basicOpen f)).obj A)).IsCoherent) →
      A.IsGE q →
      ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        (X.basicOpen f)).derivedSheafHomBifunctor.obj (op A)).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf
            (X.basicOpen f)).mapDerivedCategory.obj K)).IsLE (b - q) := by
  let : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨ω, hω, ⟨e⟩⟩ := hK V.1 V.2
  obtain ⟨a, b, hab⟩ := hω.finiteInjectiveDimension
  refine ⟨b, fun f A q hAcoh hAq => ?_⟩
  let := preservesFiniteLimits_extendScalars_basicOpen V f
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  exact isLE_derivedSheafHomSlice_of_hasInjectiveAmplitude (X.basicOpen f) (V.2.basicOpen f) _ a b
    (hasInjectiveAmplitude_extendScalars_of_isLocalization (Submonoid.powers f) ω a b hab)
    (sliceSpecFunctorRestrictTildeIso (X.basicOpen f) (V.2.basicOpen f) _
      (nonempty_iso_extendScalars_basicOpen V f ω e).some) A q hAcoh hAq

/-- **Duality against a dualizing complex carries `D^{≤q}` into `D^{≥a-q}` on the slice site over
every basic open of a fixed affine open, with one `a`.** The companion of
`Stacks.Duality.exists_forall_basicOpen_isLE_derivedSheafHomSlice`, with the lower end of the
amplitude interval of the dualizing model over `Γ(X, V)`. -/
theorem exists_forall_basicOpen_isGE_derivedSheafHomSlice (V : X.affineOpens)
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    ∃ a : ℤ, ∀ (f : Γ(X, V.1))
      (A : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over (X.basicOpen f)))) (q : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(X, X.basicOpen f)).Modules i).obj
        ((sliceSpecFunctor (X.basicOpen f) (V.2.basicOpen f)).obj A)).IsCoherent) →
      A.IsLE q →
      ((((Stacks.SheafOfModules.ringedSite X.sheaf).over
        (X.basicOpen f)).derivedSheafHomBifunctor.obj (op A)).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf
            (X.basicOpen f)).mapDerivedCategory.obj K)).IsGE (a - q) := by
  let : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨ω, hω, ⟨e⟩⟩ := hK V.1 V.2
  obtain ⟨a, b, hab⟩ := hω.finiteInjectiveDimension
  refine ⟨a, fun f A q hAcoh hAq => ?_⟩
  let := preservesFiniteLimits_extendScalars_basicOpen V f
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  exact isGE_derivedSheafHomSlice_of_hasInjectiveAmplitude (X.basicOpen f) (V.2.basicOpen f) _ a b
    (hasInjectiveAmplitude_extendScalars_of_isLocalization (Submonoid.powers f) ω a b hab)
    (sliceSpecFunctorRestrictTildeIso (X.basicOpen f) (V.2.basicOpen f) _
      (nonempty_iso_extendScalars_basicOpen V f ω e).some) A q hAcoh hAq

/-- **The restriction of a dualizing complex to an affine open is bounded below.** For `X`
locally Noetherian, `K` a dualizing complex on `X` and `W ⊆ X` affine, there is an integer `b`
with `K|_W` in `D^{≥b}` on the slice site `Opens(X)/W`.

The transport of `K|_W` to `Spec Γ(X, W)` is the derived sheafification of a dualizing model `ω`
over `Γ(X, W)` (`Stacks.Duality.exists_isDualizingComplex_iso_sliceSpecFunctor_restrict`), and a
dualizing complex has finite injective dimension: it is represented by a complex of injectives
concentrated in degrees `[a, b]`, hence lies in `D^{≥a}`. Sheafification is exact and the
transport reflects the bound (`Stacks.Duality.isGE_of_isGE_sliceSpecFunctor_obj`).

This is the lower cohomological bound on the intermediate object that the dévissage of
`AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHomEvaluation_of_approximation_of_isLE`
asks for; it may depend on the open, and does. -/
theorem exists_isGE_overFunctor_of_isDualizingComplex (W : X.Opens) (hW : IsAffineOpen W)
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    ∃ b : ℤ, ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj
      K).IsGE b := by
  let : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ := exists_isDualizingComplex_iso_sliceSpecFunctor_restrict W hW hK
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hω.finiteInjectiveDimension
  refine ⟨a, isGE_of_isGE_sliceSpecFunctor_obj W hW _ a ?_⟩
  have h0 : (DerivedCategory.Q.obj I).IsGE a := by
    have := hge
    infer_instance
  have h1 : ω.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have h2 : ((tilde.functor Γ(X, W)).mapDerivedCategory.obj ω).IsGE a :=
    CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ ω a h1
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

end BasicOpen

end Stacks.Duality

end
