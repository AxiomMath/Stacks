module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.RankLocalGenerators
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Local freeness: trivialising restrictions versus local generators

There are two ways to say that a sheaf of modules on a scheme `X` is locally free, and the
library contains both.

* `AlgebraicGeometry.Scheme.Modules.IsLocallyFree` and its finite and fixed-rank refinements ask
  that every point have an open neighbourhood `U` on which the *restriction*
  `F.restrict U.ι : U.toScheme.Modules` is isomorphic to a free sheaf.
* `CategoryTheory.SheafOfModules.IsLocallyFree` and
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, which are the definitions of Stacks Tag
  01C6, ask for a `CategoryTheory.SheafOfModules.LocalGeneratorsData`: a family of opens covering
  the terminal object of the Zariski site together with generating sections of each `F.over U`, a
  sheaf of modules on the *slice site* `Over U`, whose evaluation maps are isomorphisms.

This file proves the two agree. The comparison is
`AlgebraicGeometry.Scheme.Modules.overEquiv`, which identifies sheaves of modules on the slice
site `Over U` with sheaves of modules on the open subscheme `U`; it carries `F.over U` to
`F.restrict U.ι` by `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` and it carries free
sheaves to free sheaves of the same index because it is an equivalence, hence preserves the
coproducts that define them.

## Main definitions

* `Stacks.Modules.freeOverEquivIso` is the identification of free sheaves across `overEquiv`.
* `Stacks.Modules.restrictIsoFree` and `Stacks.Modules.freeIsoOver` convert a trivialisation of
  `F.over U` into one of `F.restrict U.ι` and back.
* `Stacks.Modules.localGeneratorsDataOfFreeIsoFamily` packages a trivialising cover whose index
  types vary from member to member as `LocalGeneratorsData`.

## Main results

* `Stacks.Modules.isLocallyFree_of_free_iso_family` and
  `Stacks.Modules.isFiniteLocallyFree_of_free_iso_family` recognise local freeness from such a
  cover.
* `Stacks.Modules.isLocallyFree_iff_localGenerators`,
  `Stacks.Modules.isFiniteLocallyFree_iff_localGenerators` and
  `Stacks.Modules.isFiniteLocallyFreeOfRank_iff_localGenerators` are the three comparisons.
* `Stacks.Modules.tilde_isLocallyFree_iff_module`,
  `Stacks.Modules.tilde_isFiniteLocallyFree_iff_module` and
  `Stacks.Modules.tilde_isFiniteLocallyFreeOfRank_iff_module` are Stacks Tag 05JM stated with the
  Tag 01C6 definition of local freeness.

## Implementation notes

The family versions of the recognition lemmas generalise
`Stacks.SheafOfModules.localGeneratorsDataOfFreeIso` and
`Stacks.SheafOfModules.isFiniteLocallyFree_of_free_iso`, which fix one index type `A` for the
whole cover, to covers whose index type varies from point to point. They are term proofs: the
field `LocalGeneratorsData.IsLocallyFreeData.isIso` binds its index at the type
`(localGeneratorsDataOfFreeIsoFamily Y hY h).I`, so the application of
`Stacks.SheafOfModules.isIso_generatingSections_ofEpi` has to be checked at default
transparency.

Those recognition lemmas are stated on a bare site, with binders literally of the form
`SheafOfModules.{u} R`, and only then applied at `X.Modules`. This is not a stylistic choice.
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules.{u} X.ringCatSheaf` and is not
reducible, so elaborating `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F` for
`F : X.Modules` cannot read the universe parameters off `F` and silently defaults them to `0`.
At the scheme level the universe arguments therefore have to be written out --- both on the
predicates, as `.{u, u, u}`, and on each application of a recognition lemma --- and the
recognition lemmas themselves have to live where no such annotation is needed.

For the same reason `freeOverEquivIso` supplies the hypothesis of
`CategoryTheory.SheafOfModules.mapFreeIso` by explicit application rather than by instance
search: `(Scheme.Modules.overEquiv U).functor` is a left adjoint, so it preserves the relevant
coproducts, but the instance is about `SheafOfModules` while the functor's codomain is
`Scheme.Modules`, and typeclass resolution unfolds at reducible transparency only. Mathlib's own
`TopologicalSpace.Opens.sheafOfModulesEquivOver` is proved with
`backward.isDefEq.respectTransparency` disabled for this reason; no such option is needed here,
because the only place it bites is this one instance argument, and `Iso.refl` already identifies
the slice site's unit module with that of `U` at default transparency.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v u₁

namespace Stacks.Modules

section Site

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The local generators data of a sheaf of modules trivialised over a cover of the terminal
object by free sheaves whose index types are allowed to depend on the member of the cover. -/
noncomputable def localGeneratorsDataOfFreeIsoFamily {M : SheafOfModules.{u} R} {I : Type u₁}
    {A : I → Type u} (Y : I → C) (hY : J.CoversTop Y)
    (h : ∀ i, SheafOfModules.free.{u} (A i) ≅ M.over (Y i)) :
    SheafOfModules.LocalGeneratorsData.{u₁} M where
  I := I
  X := Y
  coversTop := hY
  generators i :=
    (SheafOfModules.free.generatingSections (R := R.over (Y i)) (A i)).ofEpi (h i).hom

/-- A sheaf of modules trivialised over a cover of the terminal object by free sheaves, with the
index type allowed to vary over the cover, is locally free. -/
theorem isLocallyFree_of_free_iso_family {M : SheafOfModules.{u} R} {I : Type u₁}
    {A : I → Type u} (Y : I → C) (hY : J.CoversTop Y)
    (h : ∀ i, SheafOfModules.free.{u} (A i) ≅ M.over (Y i)) : M.IsLocallyFree :=
  ⟨localGeneratorsDataOfFreeIsoFamily Y hY h,
    ⟨fun i ↦ Stacks.SheafOfModules.isIso_generatingSections_ofEpi (h i)⟩⟩

/-- A sheaf of modules trivialised over a cover of the terminal object by free sheaves on finite
index types, allowed to vary over the cover, is finite locally free. -/
theorem isFiniteLocallyFree_of_free_iso_family {M : SheafOfModules.{u} R} {I : Type u₁}
    {A : I → Type u} (hA : ∀ i, Finite (A i)) (Y : I → C) (hY : J.CoversTop Y)
    (h : ∀ i, SheafOfModules.free.{u} (A i) ≅ M.over (Y i)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M :=
  ⟨localGeneratorsDataOfFreeIsoFamily Y hY h,
    ⟨fun i ↦ Stacks.SheafOfModules.isIso_generatingSections_ofEpi (h i)⟩,
    ⟨fun i ↦ ⟨hA i⟩⟩⟩

end Site

section Scheme

variable {X : Scheme.{u}}

/-- `AlgebraicGeometry.Scheme.Modules.overEquiv U` carries the free sheaf of modules on the slice
site `Over U` to the free sheaf of modules on the open subscheme `U`, with the same index
type. -/
noncomputable def freeOverEquivIso (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) :=
  letI F := (Scheme.Modules.overEquiv U).functor
  letI h : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I h (Iso.refl _)

/-- A trivialisation of `F.over U`, the module `F` seen on the slice site over an open `U`, as a
trivialisation of the restriction `F.restrict U.ι` to the open subscheme `U`. -/
noncomputable def restrictIsoFree (U : X.Opens) (F : X.Modules) (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ F.over U) :
    F.restrict (Scheme.Opens.ι U) ≅ SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I :=
  (freeOverEquivIso U I ≪≫ (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv U).app F).symm

/-- A trivialisation of the restriction `F.restrict U.ι` to an open subscheme `U`, as a
trivialisation of `F.over U` on the slice site over `U`. The two are related by the fully
faithful functor of `AlgebraicGeometry.Scheme.Modules.overEquiv U`. -/
noncomputable def freeIsoOver (U : X.Opens) (F : X.Modules) (I : Type u)
    (e : F.restrict (Scheme.Opens.ι U) ≅
      SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ F.over U :=
  (Scheme.Modules.overEquiv U).functor.preimageIso
    ((freeOverEquivIso U I).symm ≪≫ e.symm ≪≫ ((Scheme.Modules.overFunctorEquiv U).app F).symm)

/-- A family of opens of `X` containing their own index point covers the terminal object of the
Zariski site of `X`. -/
theorem coversTop_of_mem {U : ↥X → X.Opens} (hU : ∀ x, x ∈ U x) :
    (Opens.grothendieckTopology ↥X).CoversTop U := by
  rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
  intro x _
  simp only [Opens.mem_iSup]
  exact ⟨x, hU x⟩

/-- For local generators data with invertible evaluation maps, every point lies in a member
`q.X i` of the cover on which the restriction of the module is isomorphic to the free sheaf on
the index type of the generators. -/
theorem exists_restrict_iso_free (F : X.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{u} F) (hq : q.IsLocallyFreeData) (x : ↥X) :
    ∃ i : q.I, x ∈ q.X i ∧ Nonempty (F.restrict (Scheme.Opens.ι (q.X i)) ≅
      SheafOfModules.free (R := ((q.X i : Scheme.{u})).ringCatSheaf) (q.generators i).I) := by
  have hc := q.coversTop
  rw [Opens.coversTop_iff] at hc
  have hx : x ∈ ⨆ i, q.X i := by rw [hc]; trivial
  rw [Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, hi, ⟨restrictIsoFree (q.X i) F (q.generators i).I
    (@asIso _ _ _ _ (q.generators i).π (hq.isIso i))⟩⟩

/-- The two notions of local freeness of a sheaf of modules on a scheme agree: having locally
free restrictions to open subschemes is the same as having local generators data with invertible
evaluation maps. -/
theorem isLocallyFree_iff_localGenerators (F : X.Modules) :
    F.IsLocallyFree ↔ SheafOfModules.IsLocallyFree.{u, u, u} F := by
  constructor
  · intro h
    choose U hU I e using h
    exact isLocallyFree_of_free_iso_family.{u, u, u} (I := ↥X) U (coversTop_of_mem hU)
      fun x ↦ freeIsoOver (U x) F (I x) (e x).some
  · rintro ⟨q, hfree⟩ x
    obtain ⟨i, hi, he⟩ := exists_restrict_iso_free F q hfree x
    exact ⟨q.X i, hi, (q.generators i).I, he⟩

/-- The two notions of finite local freeness of a sheaf of modules on a scheme agree. -/
theorem isFiniteLocallyFree_iff_localGenerators (F : X.Modules) :
    F.IsFiniteLocallyFree ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  constructor
  · intro h
    choose U hU I hIfin e using h
    exact isFiniteLocallyFree_of_free_iso_family.{u, u, u} (I := ↥X) hIfin U
      (coversTop_of_mem hU) fun x ↦ freeIsoOver (U x) F (I x) (e x).some
  · rintro ⟨q, hfree, hfin⟩ x
    obtain ⟨i, hi, he⟩ := exists_restrict_iso_free F q hfree x
    exact ⟨q.X i, hi, (q.generators i).I, (hfin.isFiniteType i).finite, he⟩

/-- The two notions of finite local freeness of rank `r` of a sheaf of modules on a scheme
agree. -/
theorem isFiniteLocallyFreeOfRank_iff_localGenerators (F : X.Modules) (r : ℕ) :
    F.IsFiniteLocallyFreeOfRank r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r := by
  constructor
  · intro h
    choose U hU e using h
    exact Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso.{u, u, u} r U
      (coversTop_of_mem hU) fun x ↦ freeIsoOver (U x) F (ULift.{u} (Fin r)) (e x).some
  · rintro ⟨q, hfree, hr⟩ x
    obtain ⟨i, hi, he⟩ := exists_restrict_iso_free F q hfree x
    refine ⟨q.X i, hi, ⟨he.some ≪≫ ?_⟩⟩
    exact (SheafOfModules.freeFunctor (R := ((q.X i : Scheme.{u})).ringCatSheaf)).mapIso
      ((hr i).some.trans Equiv.ulift.symm).toIso

end Scheme

section Tilde

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The sheaf `M̃` associated to an `R`-module `M` is a locally free `𝒪_X`-module on
`X = Spec R`, in the sense of Stacks Tag 01C6, if and only if `M` is a locally free
`R`-module. -/
@[stacks 05JM "locally free"]
theorem tilde_isLocallyFree_iff_module :
    SheafOfModules.IsLocallyFree.{u, u, u}
        (tilde (R := CommRingCat.of R) (ModuleCat.of R M)) ↔ Module.IsLocallyFree R M :=
  (isLocallyFree_iff_localGenerators _).symm.trans (_root_.tilde_isLocallyFree_iff R M)

/-- The sheaf `M̃` associated to an `R`-module `M` is a finite locally free `𝒪_X`-module on
`X = Spec R`, in the sense of Stacks Tag 01C6, if and only if `M` is a finite locally free
`R`-module. -/
@[stacks 05JM "finite locally free"]
theorem tilde_isFiniteLocallyFree_iff_module :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (tilde (R := CommRingCat.of R) (ModuleCat.of R M)) ↔ Module.IsFiniteLocallyFree R M :=
  (isFiniteLocallyFree_iff_localGenerators _).symm.trans
    (_root_.tilde_isFiniteLocallyFree_iff R M)

/-- The sheaf `M̃` associated to an `R`-module `M` is a finite locally free `𝒪_X`-module of rank
`r` on `X = Spec R`, in the sense of Stacks Tag 01C6, if and only if `M` is a finite locally free
`R`-module of rank `r`. -/
@[stacks 05JM "finite locally free of rank r"]
theorem tilde_isFiniteLocallyFreeOfRank_iff_module (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (tilde (R := CommRingCat.of R) (ModuleCat.of R M)) r ↔
      Module.IsFiniteLocallyFreeOfRank R M r :=
  (isFiniteLocallyFreeOfRank_iff_localGenerators _ r).symm.trans
    (_root_.tilde_isFiniteLocallyFreeOfRank_iff R M r)

end Tilde

end Stacks.Modules

/-! ### Transport along an isomorphism -/

namespace AlgebraicGeometry

/-- Finite local freeness of rank `r` transports along an isomorphism of sheaves of modules on
a scheme. -/
theorem scheme_rank_transport_iso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (r : ℕ)
    (hM : M.IsFiniteLocallyFreeOfRank r) : N.IsFiniteLocallyFreeOfRank r := by
  intro x
  obtain ⟨U, hxU, ⟨hU⟩⟩ := hM x
  exact ⟨U, hxU, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ hU⟩⟩

end AlgebraicGeometry

end
