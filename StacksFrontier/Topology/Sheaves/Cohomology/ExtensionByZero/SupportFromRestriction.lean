module

public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# Cohomological support read off a vanishing restriction

Let `(X, 𝒪)` be a ringed space, `V ⊆ X` an open and `E` an object of the unbounded derived
category `D(𝒪)`. Restriction to `V` is exact, so it commutes with the cohomology sheaves, and
restriction of modules to an open subspace leaves the stalks at the points of that subspace
alone. Consequently

```
E|_V = 0   ⟹   every cohomology sheaf of E has vanishing stalks on V,
```

that is, `E` has its cohomology supported on the complement of `V`. This is the converse of
`Stacks.Cohomology.PushforwardRestriction.isZero_derived_restrict_compl_of_supported`, which goes
from a closed support to the vanishing of the restriction to the complement.

The statement is used across *two* models of restriction to an open, and the second half of this
file identifies them. `ExtensionByZeroModules.jStar` restricts to the open *subspace* `V`, that
is to `SheafOfModules (resRing V 𝒪)`; `Stacks.SheafOfModules.derivedRestrict`, the restriction
that [Stacks, Tag 08DL] is stated with, restricts to the *slice site* of the opens contained in
`V`, that is to `SheafOfModules ((structureSheaf Rc).over V)`. The two are reconciled by
`Stacks.SheafOfModules.overFunctor_comp_sliceToSubspaceFunctor`, an equality of functors holding
on the nose, together with the faithfulness of the comparison of the two models; so an object
vanishes after one restriction exactly when it vanishes after the other, degree by degree on
cohomology.

With that in hand, [Stacks, Tag 08DL] gives the support of a derived internal Hom: for `K` with
cohomology supported on a closed `T` and *arbitrary* `L`, the derived internal Hom
`R𝓗om_𝒪(K, L)` again has its cohomology supported on `T`. The derived dual of a complex
supported at a closed point is the case `T = {x}`; the case `L = 𝒪_X` of that is the derived
dual proper.

## Main results

* `Stacks.Cohomology.RestrictionSupport.isZero_stalk_homology_of_isZero_jStar`: **the bridge.**
  If `E` restricts to zero on the open subspace `V`, the stalk at every point of `V` of every
  cohomology sheaf of `E` vanishes.
* `Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_of_isZero_jStar`: hence `E` has
  its cohomology supported on any set whose complement is contained in `V`.
* `Stacks.Cohomology.RestrictionSupport.isZero_jStar_mapDerivedCategory_of_cohomologySupportedOn`:
  the converse, for an open disjoint from the support.
* `Stacks.Cohomology.RestrictionSupport.isZero_derivedRestrict_iff_isZero_jStar`: **the two
  models of restriction to an open detect the zero object together.**
* `Stacks.Cohomology.RestrictionSupport.isZero_derivedSheafHom_of_isZero`: a derived internal
  Hom out of a zero object is zero.
* `Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_derivedSheafHom`: **the support of
  a derived internal Hom**, `R𝓗om_𝒪(K, L)` is supported on a closed `T` whenever `K` is.
* `Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleton_derivedSheafHom`: the
  same at a closed point, which is the derived-dual statement.
* `Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleFunctor_obj`: a module
  placed in a single degree is supported wherever its stalks are.
* `Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleton_derivedSheafHom_single`:
  the two previous results combined — the derived dual of a *module* whose stalks vanish away
  from a closed point is supported at that point.

## Implementation notes

The stalk comparison is assembled from
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` in the spelling
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso` — restriction is exact, so
it commutes with the cohomology of the derived category — and from
`TopCat.Presheaf.stalkRestrictIso`, the statement that the naive restriction of a presheaf to an
open has the same stalks at the points of that open. These are the two halves the scheme-level
argument of `StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDerivedModules.lean` uses in its
private `stalkDerivedRestrictIso`; the content here is the same, stated for a bare sheaf of
rings on a space and for the two restriction models of the internal-Hom development, where it is
needed.

Reflecting the zero object across the two models is done at the level of *modules*, not of
derived categories: `Stacks.SheafOfModules.sliceToSubspaceFunctor` is half of an equivalence,
hence faithful, and a faithful additive functor reflects zero objects
(`Stacks.Cohomology.RestrictionSupport.isZero_of_isZero_map`). Lifting that to derived
categories directly would need the faithfulness of the induced functor on derived categories,
which is not available; going through cohomology avoids the question, since an object of a
derived category with no cohomology is zero.

## References

* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules
open Stacks.Cohomology.SupportedComplexes (exactFunctorDerivedHomologyIso)
open Stacks.Cohomology.PushforwardRestriction (isZero_derived_of_homology_isZero
  isZero_jStar_obj_of_stalk_isZero)

universe u

namespace Stacks.Cohomology.RestrictionSupport

attribute [local instance] HasDerivedCategory.standard

-- Restriction of modules to the opens contained in an open is exact: left exactness and right
-- exactness are lemmas in
-- `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CokernelFinitePresentation.lean`, registered as
-- instances here so that `Stacks.SheafOfModules.derivedRestrict` elaborates without the
-- exactness of the restriction being carried as a hypothesis.
attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-! ### A faithful additive functor reflects zero objects -/

/-- A faithful functor preserving zero morphisms reflects zero objects: an object is zero
exactly when its identity is zero, and both conditions are detected on the image. -/
theorem isZero_of_isZero_map {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [G.Faithful] {N : C} (h : IsZero (G.obj N)) : IsZero N :=
  (IsZero.iff_id_eq_zero _).2 (G.map_injective (h.eq_of_src _ _))

/-! ### The stalk of a cohomology sheaf of a restriction to an open subspace -/

section Space

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- A sheaf of modules which is a zero object has all its stalks zero. -/
theorem isZero_stalk_of_isZero {M : SheafOfModules.{u} O} (hM : IsZero M) (y : X) :
    IsZero (TopCat.Presheaf.stalk (X := X) M.val.presheaf y) :=
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero ((SheafOfModules.toSheaf O).obj M)).1
    (Functor.map_isZero (SheafOfModules.toSheaf O) hM) y

/-- **The stalks of a cohomology sheaf of a restriction.** At a point `y` of an open `V`, the
stalk of the `n`-th cohomology sheaf of the restriction of `E` to the open subspace `V` is the
stalk at `y` of the `n`-th cohomology sheaf of `E`.

Restriction is exact, so it commutes with the cohomology sheaves, and restriction of modules to
an open subspace does not change the stalks at the points of that subspace. -/
def stalkJStarHomologyIso (V : Opens X) (n : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} O)) (y : Usp V) :
    TopCat.Presheaf.stalk (X := Usp V)
        (((DerivedCategory.homologyFunctor (SheafOfModules.{u} (resRing V O)) n).obj
          ((jStar V O).mapDerivedCategory.obj E)).val.presheaf) y ≅
      TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).obj E).val.presheaf) y.1 :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((toAb (resRing V O)).mapIso ((exactFunctorDerivedHomologyIso (jStar V O) n).app E)) ≪≫
    TopCat.Presheaf.stalkRestrictIso V
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).obj E).val.presheaf) y

/-- **The bridge.** If `E` restricts to zero on the open subspace `V`, then at every point of
`V` every cohomology sheaf of `E` has vanishing stalk.

The only hypotheses are that `V` be open and that the restriction of `E` to `V` vanish. -/
theorem isZero_stalk_homology_of_isZero_jStar (V : Opens X)
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : IsZero ((jStar V O).mapDerivedCategory.obj E)) (n : ℤ) {y : X} (hy : y ∈ V) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).obj E).val.presheaf) y) :=
  IsZero.of_iso
    (isZero_stalk_of_isZero (resRing V O)
      (Functor.map_isZero (DerivedCategory.homologyFunctor _ n) hE) ⟨y, hy⟩)
    (stalkJStarHomologyIso O V n E ⟨y, hy⟩).symm

/-- **An object restricting to zero on an open is supported on the complement.** -/
theorem cohomologySupportedOn_compl_of_isZero_jStar (V : Opens X)
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : IsZero ((jStar V O).mapDerivedCategory.obj E)) :
    CohomologySupportedOn O ((V : Set X)ᶜ) E := fun n _ hy =>
  isZero_stalk_homology_of_isZero_jStar O V E hE n (by simpa using hy)

/-- An object restricting to zero on an open `V` is supported on every set whose complement is
contained in `V`. -/
theorem cohomologySupportedOn_of_isZero_jStar (T : Set X) (V : Opens X)
    (hTV : Tᶜ ⊆ (V : Set X)) (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : IsZero ((jStar V O).mapDerivedCategory.obj E)) :
    CohomologySupportedOn O T E := fun n _ hy =>
  isZero_stalk_homology_of_isZero_jStar O V E hE n (hTV hy)

/-- **The converse.** An object supported on `T` restricts to zero on every open disjoint from
`T`. This is `Stacks.Cohomology.PushforwardRestriction.isZero_derived_restrict_compl_of_supported`
without the requirement that the open be the complement of a closed `T`. -/
theorem isZero_jStar_mapDerivedCategory_of_cohomologySupportedOn (T : Set X) (V : Opens X)
    (hVT : (V : Set X) ⊆ Tᶜ) (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn O T E) :
    IsZero ((jStar V O).mapDerivedCategory.obj E) := by
  refine isZero_derived_of_homology_isZero _ fun n => ?_
  refine IsZero.of_iso ?_ ((exactFunctorDerivedHomologyIso (jStar V O) n).app E)
  exact isZero_jStar_obj_of_stalk_isZero O V _ fun x hx => hE n x (hVT hx)

/-- **A module placed in a single degree.** If the stalks of `M` vanish outside `T`, then the
object of `D(𝒪)` given by `M` in degree `n` has its cohomology supported on `T`: its only
non-vanishing cohomology sheaf is `M` itself, in degree `n`. -/
theorem cohomologySupportedOn_singleFunctor_obj (T : Set X) (n : ℤ) (M : SheafOfModules.{u} O)
    (hM : ∀ y : X, y ∉ T → IsZero (TopCat.Presheaf.stalk (X := X) M.val.presheaf y)) :
    CohomologySupportedOn O T
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) n).obj M) := by
  intro i y hy
  rcases lt_trichotomy i n with h | h | h
  · exact isZero_stalk_of_isZero O (DerivedCategory.isZero_of_isGE _ n i h) y
  · subst h
    exact (hM y hy).of_iso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((toAb O).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} O) i).app M)))
  · exact isZero_stalk_of_isZero O (DerivedCategory.isZero_of_isLE _ n i h) y

end Space

/-! ### The two models of restriction to an open -/

section TwoModels

open Stacks.SheafOfModules

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (V : Opens X)

/-- The comparison of the slice-site and the open-subspace model of `𝒪_V`-modules is faithful,
being one half of an equivalence of categories. -/
instance sliceToSubspaceFunctor_faithful : (sliceToSubspaceFunctor Rc V).Faithful :=
  inferInstanceAs (V.sheafOfModulesEquivOver (structureSheaf Rc)).functor.Faithful

/-- **The two models of restriction of a module to an open detect the zero object together.**
Restriction to the opens contained in `V` kills a module exactly when restriction to the open
subspace `V` does: the first followed by the comparison of the two models *is* the second, and
the comparison is faithful. -/
theorem isZero_overFunctor_obj_iff (M : SheafOfModules.{u} (structureSheaf Rc)) :
    IsZero ((SheafOfModules.overFunctor.{u} (structureSheaf Rc) V).obj M) ↔
      IsZero ((jStar V (structureSheaf Rc)).obj M) :=
  ⟨fun h => Functor.map_isZero (sliceToSubspaceFunctor Rc V) h,
    fun h => isZero_of_isZero_map (sliceToSubspaceFunctor Rc V) h⟩

/-- Degreewise form of `isZero_derivedRestrict_iff_isZero_jStar`: in each cohomological degree,
the two models of derived restriction to `V` vanish together. -/
theorem isZero_homology_derivedRestrict_iff (E : DerivedCategory (StructureSheafModules Rc))
    (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj ((derivedRestrict Rc V).obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((jStar V (structureSheaf Rc)).mapDerivedCategory.obj E)) :=
  ((exactFunctorDerivedHomologyIso
      (SheafOfModules.overFunctor.{u} (structureSheaf Rc) V) n).app E).isZero_iff.trans
    ((isZero_overFunctor_obj_iff Rc V _).trans
      ((exactFunctorDerivedHomologyIso (jStar V (structureSheaf Rc)) n).app E).isZero_iff.symm)

/-- **The two models of derived restriction to an open detect the zero object together.**

`Stacks.SheafOfModules.derivedRestrict` restricts to the slice site of the opens contained in
`V` and `ExtensionByZeroModules.jStar` to the open subspace `V`; an object of `D(𝒪)` vanishes
after the one exactly when it vanishes after the other. -/
theorem isZero_derivedRestrict_iff_isZero_jStar
    (E : DerivedCategory (StructureSheafModules Rc)) :
    IsZero ((derivedRestrict Rc V).obj E) ↔
      IsZero ((jStar V (structureSheaf Rc)).mapDerivedCategory.obj E) :=
  ⟨fun h => isZero_derived_of_homology_isZero _ fun n =>
      (isZero_homology_derivedRestrict_iff Rc V E n).1 (Functor.map_isZero _ h),
    fun h => isZero_derived_of_homology_isZero _ fun n =>
      (isZero_homology_derivedRestrict_iff Rc V E n).2 (Functor.map_isZero _ h)⟩

/-- **The bridge in the slice-site model.** An object of `D(𝒪)` whose restriction to the opens
contained in `V` vanishes has its cohomology supported on the complement of `V`. -/
theorem cohomologySupportedOn_compl_of_isZero_derivedRestrict
    (E : DerivedCategory (StructureSheafModules Rc))
    (hE : IsZero ((derivedRestrict Rc V).obj E)) :
    CohomologySupportedOn (structureSheaf Rc) ((V : Set X)ᶜ) E :=
  cohomologySupportedOn_compl_of_isZero_jStar (structureSheaf Rc) V E
    ((isZero_derivedRestrict_iff_isZero_jStar Rc V E).1 hE)

/-- **The converse in the slice-site model.** An object supported on `T` restricts to zero on
the opens contained in an open disjoint from `T`. -/
theorem isZero_derivedRestrict_of_cohomologySupportedOn (T : Set X)
    (hVT : (V : Set X) ⊆ Tᶜ) (E : DerivedCategory (StructureSheafModules Rc))
    (hE : CohomologySupportedOn (structureSheaf Rc) T E) :
    IsZero ((derivedRestrict Rc V).obj E) :=
  (isZero_derivedRestrict_iff_isZero_jStar Rc V E).2
    (isZero_jStar_mapDerivedCategory_of_cohomologySupportedOn (structureSheaf Rc) T V hVT E hE)

end TwoModels

/-! ### The support of a derived internal Hom -/

section InternalHom

open Stacks.SheafOfModules

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

/-- **A derived internal Hom out of a zero object is zero.** `R𝓗om_𝒪(-, L)` is an additive
functor, and an additive functor carries a zero object to a zero object.

The modules are named `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf S.O)`, which is the
spelling `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` declares its domain at.  A
ringed site has fields `C`, `J` and `O` only -- there is no `ringSheaf` getter, and
`StacksFrontier/CategoryTheory/Sites/Modules/RingedSite.lean` records that none is wanted: "No
ringed-site getter or alternative underlying-ring construction is needed." -/
theorem isZero_derivedSheafHom_of_isZero (S : RingedSite.{u, u, u})
    {K : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf S.O))}
    (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf S.O))) (hK : IsZero K) :
    IsZero (((RingedSite.derivedSheafHomBifunctor S).obj (op K)).obj L) :=
  Functor.map_isZero ((RingedSite.derivedSheafHomBifunctor S).flip.obj L) hK.op

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (V : Opens X)

/-- **The derived internal Hom out of an object vanishing on `V` is supported off `V`.**

[Stacks, Tag 08DL] identifies the restriction of `R𝓗om_𝒪(K, L)` to the opens contained in `V`
with `R𝓗om_{𝒪|_V}(K|_V, L|_V)`; the first argument vanishes, so that object is zero, and the
bridge then puts the support of `R𝓗om_𝒪(K, L)` outside `V`. No hypothesis is placed on `L`. -/
theorem cohomologySupportedOn_compl_derivedSheafHom
    (K L : DerivedCategory (StructureSheafModules Rc))
    (hK : IsZero ((derivedRestrict Rc V).obj K)) :
    CohomologySupportedOn (structureSheaf Rc) ((V : Set X)ᶜ)
      (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj L) :=
  cohomologySupportedOn_compl_of_isZero_derivedRestrict Rc V _
    ((isZero_derivedSheafHom_of_isZero ((ringedSite Rc).over V)
      ((derivedRestrict Rc V).obj L) hK).of_iso (derivedSheafHomRestrictionIso Rc V K L))

end InternalHom

section InternalHomClosed

open Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The support of a derived internal Hom.** Let `(X, 𝒪)` be a ringed space, let `T ⊆ X` be
closed and let `K` be an object of `D(𝒪)` whose cohomology sheaves are supported on `T`. Then
for *every* `L` in `D(𝒪)` the cohomology sheaves of `R𝓗om_𝒪(K, L)` are supported on `T`.

The hypotheses are exactly: `T` is closed (so that its complement is an open to restrict to),
and `K` is supported on `T`. Nothing is assumed about `L`, about `K` beyond its support, or
about the space.

On the complement `V = X \ T` the restriction of `K` vanishes, so [Stacks, Tag 08DL] makes the
restriction of `R𝓗om_𝒪(K, L)` to `V` a derived internal Hom out of a zero object, hence zero;
and an object restricting to zero on `V` is supported on `T`. -/
theorem cohomologySupportedOn_derivedSheafHom (T : Set X) (hT : IsClosed T)
    (K L : DerivedCategory (StructureSheafModules Rc))
    (hK : CohomologySupportedOn (structureSheaf Rc) T K) :
    CohomologySupportedOn (structureSheaf Rc) T
      (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj L) :=
  fun n y hy => cohomologySupportedOn_compl_derivedSheafHom Rc ⟨Tᶜ, hT.isOpen_compl⟩ K L
    (isZero_derivedRestrict_of_cohomologySupportedOn Rc _ T le_rfl K hK) n y (by simpa using hy)

/-- **The derived internal Hom out of a complex supported at a closed point is supported at that
point.** This is the derived-dual statement at a closed point: taking `L = 𝒪_X` reads
`R𝓗om_𝒪(K, 𝒪_X)`, the derived dual of `K`.

The hypotheses are: `{x}` is closed in `X`, and the cohomology sheaves of `K` are supported on
`{x}`. No coherence, Noetherianness, regularity or finite-type hypothesis is used, and `L` is
arbitrary. -/
theorem cohomologySupportedOn_singleton_derivedSheafHom (x : X)
    (hx : IsClosed ({x} : Set X)) (K L : DerivedCategory (StructureSheafModules Rc))
    (hK : CohomologySupportedOn (structureSheaf Rc) ({x} : Set X) K) :
    CohomologySupportedOn (structureSheaf Rc) ({x} : Set X)
      (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj L) :=
  cohomologySupportedOn_derivedSheafHom Rc ({x} : Set X) hx K L hK

/-- **The derived dual of a module supported at a closed point is supported at that point.**

Let `(X, 𝒪)` be a ringed space, let `x ∈ X` be a point with `{x}` closed, and let `F` be an
`𝒪`-module whose stalks vanish away from `x`. Then for every `L` in `D(𝒪)` — in particular for
`L = 𝒪_X` in degree zero, where the conclusion is about the derived dual
`R𝓗om_𝒪(F, 𝒪_X)` — the cohomology sheaves of `R𝓗om_𝒪(F, L)` are supported on `{x}`.

The hypotheses are exactly: `{x}` is closed, and the stalks of `F` vanish off `x`. Coherence of
`F`, local Noetherianness, regularity and finite type over a field are *not* used. -/
theorem cohomologySupportedOn_singleton_derivedSheafHom_single (x : X)
    (hx : IsClosed ({x} : Set X)) (F : SheafOfModules.{u} (structureSheaf Rc))
    (hF : ∀ y : X, y ∉ ({x} : Set X) →
      IsZero (TopCat.Presheaf.stalk (X := X) F.val.presheaf y))
    (L : DerivedCategory (StructureSheafModules Rc)) :
    CohomologySupportedOn (structureSheaf Rc) ({x} : Set X)
      (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
        (op ((DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj F))).obj L) :=
  cohomologySupportedOn_singleton_derivedSheafHom Rc x hx _ L
    (cohomologySupportedOn_singleFunctor_obj (structureSheaf Rc) ({x} : Set X) 0 F hF)

end InternalHomClosed

end Stacks.Cohomology.RestrictionSupport

end

