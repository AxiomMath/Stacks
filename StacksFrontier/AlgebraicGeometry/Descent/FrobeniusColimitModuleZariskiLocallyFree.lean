module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiSeparated
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullbackTransport
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# Finite local freeness of a Frobenius-colimit module is Zariski local

Condition (1) of Stacks 0EX9 for Stacks Tag 0EXE was reduced in
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundleGroupoidZariski.lean` to two
inputs per Zariski family of the big h category over `S`. This file discharges the second of
them: that finite local freeness of a sheaf of `colim_F 𝒪_U`-modules is **detected** by its
scalar extensions along the family.

The statement is false for a general family of the big h site — a non-flat morphism can make a
module look locally free after extension of scalars when it is not — so it is proved exactly
where it is true, for a family whose members are open immersions whose images cover.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitPullbackFreeOfFactor`: a trivialisation of the transition
  functor of a morphism factoring isomorphically through an open is one of the transition functor
  of that open's inclusion.
* `AlgebraicGeometry.frobeniusColimitFreeIsoOverOfPullbackObjFree`: **a trivialisation of the
  transition functor of an open immersion `V.ι` is a trivialisation of the slice restriction
  `M.over V`** — the converse of
  `AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso`, and the one step that was missing.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_of_frobeniusColimitPullback_of_openImmersion`:
  **a sheaf of `colim_F 𝒪_X`-modules whose transition along each member of a family of open
  immersions covering `X` is finite locally free is finite locally free.**
* `AlgebraicGeometry.isFiniteLocallyFree_of_bigHFrobeniusColimitPullback`: the same statement for
  a Zariski family of the big h category over `S` — **the hypothesis `hP` of
  `AlgebraicGeometry.isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_families`,
  discharged.**

## Implementation notes

**Why the argument runs through free modules rather than through finite local freeness.** The
transition functor of an open immersion is slice restriction followed by the open-subscheme
equivalence `AlgebraicGeometry.frobeniusColimitModuleOpenEquiv`
(`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`), so what the hypothesis gives is
finite local freeness of `E.functor.obj (M.over V)` and what the conclusion consumes is finite
local freeness of `M.over V`. Transporting finite local freeness *backwards* along `E` is not a
formality: `E` changes both the site — from the slice site `Opens(X)/V` to the site `Opens V` of
the open subscheme — and the sheaf of rings, so the covering family and the iterated slices of a
`CategoryTheory.SheafOfModules.LocalGeneratorsData` would both have to be carried across.

Being *free* has no covering family in it, and so crosses `E` in one line: `E` sends free to free
(`AlgebraicGeometry.frobeniusColimitModuleOpenEquivObjFree`), hence so does its inverse, by the
unit isomorphism. The argument therefore refines the given data to free trivialisations first —
`AlgebraicGeometry.exists_cover_free_frobeniusColimitPullback` does that, member by member — and
only reassembles finite local freeness at the very end, through
`Stacks.Modules.isFiniteLocallyFree_of_free_iso_family`.

**The index universe.** `Stacks.Modules.isFiniteLocallyFree_of_free_iso_family` indexes its cover
by a type of the site's own object universe, which for `Opens X` is `Type u`, while the families
of the big h category over `S` are indexed by a type of `Type (u + 1)`
(`AlgebraicGeometry.BigHOver.zariskiPrecoverage` is stated there, and the two sides would not
meet with a smaller one). The shrink is performed by indexing the cover by the *opens that
trivialise `M`* — a subtype of `X.Opens`, hence of `Type u` — rather than by the family; the
family is then used only to show that those opens cover, which is a statement about points.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe t u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-! ### Free trivialisations across the open-subscheme bridge -/

/-- **A trivialisation of the transition functor of `V.ι` is a trivialisation of the slice
restriction `M.over V`.**

This is the converse of `AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso`, and it is the
step that makes finite local freeness descend along an open cover: the transition functor of
`V.ι` is slice restriction followed by `AlgebraicGeometry.frobeniusColimitModuleOpenEquiv`, so
what has to be undone is that equivalence, and a free module crosses it in both directions
because `AlgebraicGeometry.frobeniusColimitModuleOpenEquivObjFree` sends free to free and the
unit isomorphism turns that into the same statement for the inverse. -/
noncomputable def frobeniusColimitFreeIsoOverOfPullbackObjFree (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (V : X.Opens) (hV : IsInCharacteristic V.toScheme p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (I : Type u)
    (e : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M ≅
      _root_.SheafOfModules.free I) :
    _root_.SheafOfModules.free (R := (frobeniusColimitRingSheaf X p hX).over V) I ≅ M.over V :=
  letI E := frobeniusColimitModuleOpenEquiv X p hX V hV
  letI a : E.functor.obj (M.over V) ≅ _root_.SheafOfModules.free I :=
    ((frobeniusColimitModuleRestrictIsoPullback X p hX V hV).app M).trans e
  (E.unitIso.app _).trans
    ((E.inverse.mapIso
      ((frobeniusColimitModuleOpenEquivObjFree X p hX V hV I).trans a.symm)).trans
        (E.unitIso.app _).symm)

/-- **A trivialisation of the transition functor of a morphism factoring isomorphically through
an open is a trivialisation of the transition functor of that open's inclusion.**

The transition functor of the isomorphism `θ` is an equivalence
(`AlgebraicGeometry.frobeniusColimitPullbackEquivOfIso`), so the trivialisation can be moved
across it; its inverse is again a transition functor, and the transition of a free module is free
by Mathlib's `CategoryTheory.SheafOfModules.pullbackObjFreeIso`. -/
noncomputable def frobeniusColimitPullbackFreeOfFactor (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (V : X.Opens) (hV : IsInCharacteristic V.toScheme p)
    {Y : Scheme.{u}} (j : Y ⟶ X) (hY : IsInCharacteristic Y p)
    (θ : Y ⟶ V.toScheme) [IsIso θ] (hθ : θ ≫ V.ι = j)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (I : Type u)
    (e : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p j hY hX)).obj M ≅ _root_.SheafOfModules.free I) :
    (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M ≅
      _root_.SheafOfModules.free I :=
  letI E := frobeniusColimitPullbackEquivOfIso p (asIso θ) hY hV
  (E.unitIso.app _).trans
    ((E.inverse.mapIso
        (((frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ).app M).trans e)).trans
      (_root_.SheafOfModules.pullbackObjFreeIso
        (frobeniusColimitStructureSheafHom p (asIso θ).inv hV hY) I))

/-! ### Finite local freeness along a family of open immersions -/

/-- **Finite local freeness of a `colim_F 𝒪_X`-module is detected by the transition functors of a
family of open immersions whose images cover `X`.**

This is the locality statement that condition (1) of Stacks 0EX9 asks of Stacks Tag 0EXE, at the
level of schemes. The hypothesis is read member by member: finite local freeness of the
transition of `M` along `j i` gives, by
`AlgebraicGeometry.exists_cover_free_frobeniusColimitPullback`, a cover of `Y i` over whose
members that transition is *free*, and composing with `j i` turns each such member into an open
immersion into `X` along which `M` is trivialised. Those opens cover `X`, and
`AlgebraicGeometry.frobeniusColimitFreeIsoOverOfPullbackObjFree` reads each trivialisation on the
slice restriction, which is the form
`Stacks.Modules.isFiniteLocallyFree_of_free_iso_family` consumes. -/
theorem isFiniteLocallyFree_of_frobeniusColimitPullback_of_openImmersion (X : Scheme.{u})
    (hX : IsInCharacteristic X p) {ι : Type t} {Y : ι → Scheme.{u}} (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hY : ∀ i, IsInCharacteristic (Y i) p)
    (hcov : ⨆ i, (j i).opensRange = ⊤)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    (h : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p (j i) (hY i) hX)).obj M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  -- the opens of `X` over which `M` becomes free on a finite index type
  set P : X.Opens → Prop := fun W => ∃ K : Type u, Finite K ∧
    Nonempty (_root_.SheafOfModules.free (R := (frobeniusColimitRingSheaf X p hX).over W) K ≅
      M.over W) with hPdef
  have key : ∀ x : (X : TopCat), ∃ W : X.Opens, P W ∧ x ∈ W := by
    intro x
    have hx : x ∈ ⨆ i, (j i).opensRange := by rw [hcov]; trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, z, hz⟩ := hx
    obtain ⟨I₀, W, K, hWcov, hKfin, hWfree⟩ :=
      exists_cover_free_frobeniusColimitPullback (Y i) p (hY i)
        ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (j i) (hY i) hX)).obj M) (h i)
    have hzW : z ∈ ⨆ m, W m := by rw [hWcov]; trivial
    rw [Opens.mem_iSup] at hzW
    obtain ⟨m, hm⟩ := hzW
    -- the open immersion `(W m).ι ≫ j i` into `X`, along which `M` is free
    have hWm : IsInCharacteristic (W m).toScheme p := isInCharacteristic_toScheme (hY i) (W m)
    have hfac : (W m).ι ≫ j i = (W m).ι ≫ j i := rfl
    have e₁ : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p ((W m).ι ≫ j i) hWm hX)).obj M ≅
          _root_.SheafOfModules.free (K m) :=
      ((frobeniusColimitPullbackTriangleIso p (W m).ι (j i) ((W m).ι ≫ j i) hWm (hY i) hX
        hfac).app M).symm.trans (hWfree m).some
    refine ⟨((W m).ι ≫ j i).opensRange, ⟨K m, hKfin m, ⟨?_⟩⟩, ?_⟩
    · refine frobeniusColimitFreeIsoOverOfPullbackObjFree p X hX _
        (isInCharacteristic_toScheme hX _) M (K m) ?_
      exact frobeniusColimitPullbackFreeOfFactor p X hX _
        (isInCharacteristic_toScheme hX _) ((W m).ι ≫ j i) hWm
        (IsOpenImmersion.isoOfRangeEq ((W m).ι ≫ j i)
          ((W m).ι ≫ j i).opensRange.ι (by simp)).hom
        (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) M (K m) e₁
    · exact ⟨⟨z, hm⟩, hz⟩
  refine Stacks.Modules.isFiniteLocallyFree_of_free_iso_family.{u, u, u}
    (I := { W : X.Opens // P W }) (A := fun W => W.2.choose)
    (fun W => W.2.choose_spec.1) (fun W => W.1) ?_ (fun W => W.2.choose_spec.2.some)
  rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
  intro x _
  simp only [Opens.mem_iSup]
  obtain ⟨W, hW, hxW⟩ := key x
  exact ⟨⟨W, hW⟩, hxW⟩

/-! ### The big h site -/

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (hpS : IsInCharacteristic S p)

include hpS

/-- **Finite local freeness of a sheaf of `colim_F 𝒪_U`-modules is detected by its scalar
extensions along a Zariski family of the big h category over `S`.**

This is the hypothesis `hP` of
`AlgebraicGeometry.isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_families`,
discharged. The two geometric inputs are
`AlgebraicGeometry.isOpenImmersion_of_mem_bigHOver_zariskiPrecoverage` and
`AlgebraicGeometry.iSup_opensRange_eq_top_of_mem_bigHOver_zariskiPrecoverage`, and the content is
`AlgebraicGeometry.isFiniteLocallyFree_of_frobeniusColimitPullback_of_openImmersion` on the
underlying family of morphisms of schemes. -/
theorem isFiniteLocallyFree_of_bigHFrobeniusColimitPullback {ι : Type t}
    {U : BigHOver B S hS} {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ U)
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U)
    (M : _root_.SheafOfModules.{u} (bigHFrobeniusColimitRingSheaf B S hS p hpS U))
    (h : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((bigHFrobeniusColimitPullback B S hS p hpS (f i).op).obj M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  have hoi : ∀ i, IsOpenImmersion ((BigHOver.toScheme B S hS).map (f i)) :=
    isOpenImmersion_of_mem_bigHOver_zariskiPrecoverage B S hS hf
  exact isFiniteLocallyFree_of_frobeniusColimitPullback_of_openImmersion p
    ((BigHOver.toScheme B S hS).obj U) (isInCharacteristic_bigHOver B S hS p hpS U)
    (fun i => (BigHOver.toScheme B S hS).map (f i))
    (fun i => isInCharacteristic_bigHOver B S hS p hpS (X i))
    (iSup_opensRange_eq_top_of_mem_bigHOver_zariskiPrecoverage B S hS hf) M h

end AlgebraicGeometry

end
