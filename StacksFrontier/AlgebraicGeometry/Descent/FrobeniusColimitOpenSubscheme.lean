module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.PullbackUnitAut

/-!
# `colim_F 𝒪_X` restricted to an open is `colim_F 𝒪` of the open subscheme

Let `p` be a prime and let `X` be a scheme in characteristic `p`. For an open `U` of `X`,
`AlgebraicGeometry.frobeniusColimitRingSheafOverIso` identifies the restriction
`(colim_F 𝒪_X)|_U` with the colimit along the restricted Frobenius — but on the **slice site**
`Opens(X)/U`, not on the site `Opens U` of the open subscheme `U`. This file crosses that last
gap:

`(colim_F 𝒪_X)|_U ≅ colim_F 𝒪_{U}` under `TopologicalSpace.Opens.sheafEquivOver`,

so that the sheaf of rings of Stacks Tag 0EXB formed on an open subscheme is the restriction of
the one formed on the ambient scheme. This is what lets a statement about `colim_F 𝒪` over a
scheme be applied to an open of another scheme — in particular it is what identifies the almost
blowup square of Stacks Example 0EVH over a localisation `A_g` with the restriction to the basic
open `D(g)` of the square over `A`.

## Main definitions

* `CategoryTheory.Limits.ringSheafEndoColimitEquivIso`: an equivalence of categories of sheaves
  of rings carries the colimit of a sheaf of rings along an endomorphism to the colimit along the
  image endomorphism.
* `AlgebraicGeometry.frobeniusColimitRingSheafOpenIso`: **`colim_F 𝒪_X` restricted to `U` is
  `colim_F 𝒪_U`.**
* `AlgebraicGeometry.frobeniusColimitRingSheafOpenSectionsIso`: the same identification read on
  sections over an open of `U`.

## Main results

* `AlgebraicGeometry.sheafEquivOver_functor_map_frobeniusRingSheafOnOpensHom`: **the endomorphism
  the identification carries Frobenius to is Frobenius.** Transporting the restriction of the
  `p`-th power map on `𝒪_X` to the site of the open subscheme gives the `p`-th power map on
  `𝒪_U`; both act on a section by raising it to the `p`-th power.
* `TopologicalSpace.Opens.overEquivalence_inverse_obj_top_left`: the object of the slice site
  that the top open of `U` corresponds to is `U` itself, which is what instantiates the sections
  identification at global sections of the open subscheme.
* `AlgebraicGeometry.exists_cover_free_frobeniusColimitModuleRestrict`: **a finite locally free
  `colim_F 𝒪_X`-module is free on each member of an open cover, as a `colim_F 𝒪_U`-module on the
  open subscheme.** This is the form in which the trivialising-cover argument for
  [Stacks, Tag 0EXD] consumes finite local freeness: the trivialisation given by the definition
  lives over the slice sheaves of rings `(colim_F 𝒪_X)|_U`, and what the cover argument needs is
  a free module over `colim_F 𝒪_U`, the sheaf of rings the square of Example 0EVH over a
  localisation carries.

## Implementation notes

**Everything here is Mathlib plus one four-line lemma.** The slice-site-to-open-subspace
equivalence of sheaf categories is `TopologicalSpace.Opens.sheafEquivOver`
(`Mathlib/Topology/Sheaves/Over.lean`), at an arbitrary target category and with no hypotheses,
and the two identifications of ring sheaves it has to be compatible with hold by `rfl`:
`U.toScheme.ringSheafOnOpens` **is** the transport of `X.ringSheafOnOpens.over U`, because
Mathlib's `TopologicalSpace.Opens.overPullbackSheafEquivOver` is `Iso.refl`. So the only content
is `AlgebraicGeometry.sheafEquivOver_functor_map_frobeniusRingSheafOnOpensHom`, which says the
transported Frobenius is Frobenius, and that is a computation on sections.

**The characteristic of the open subscheme is a parameter, not derived.** `IsInCharacteristic` is
a proposition, so any two witnesses agree; taking it in rather than producing it with
`AlgebraicGeometry.isInCharacteristic_of_hom` keeps this module independent of the Frobenius
twist development and lets a consumer hand in whichever witness it already has.

**Why the colimit transports.** The functor of an equivalence is a left adjoint, so it preserves
all colimits, and `CategoryTheory.Limits.endoColimitCompIso` — stated for an arbitrary
colimit-preserving functor and an arbitrary endomorphism — applies with no further work. Nothing
of the sequential colimit is ever unfolded.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Frobenius

universe u

namespace CategoryTheory.Limits

/-- **An equivalence of categories of sheaves of rings transports the colimit along an
endomorphism.** The functor of an equivalence preserves colimits, so
`CategoryTheory.Limits.endoColimitCompIso` applies to it. -/
noncomputable def ringSheafEndoColimitEquivIso {C : Type u} [Category.{u} C] {D : Type u}
    [Category.{u} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {S : Sheaf J RingCat.{u}} (ψ : S ⟶ S) (E : Sheaf J RingCat.{u} ≌ Sheaf K RingCat.{u}) :
    E.functor.obj (ringSheafEndoColimit ψ) ≅ ringSheafEndoColimit (E.functor.map ψ) :=
  letI : PreservesColimitsOfSize.{0, 0} E.functor :=
    Adjunction.leftAdjoint_preservesColimits E.toAdjunction
  endoColimitCompIso ψ E.functor

end CategoryTheory.Limits

namespace TopologicalSpace.Opens

/-- The object of the slice site `Opens(X)/U` which the top open of the subspace `U` corresponds
to is `U` itself. -/
@[simp]
lemma overEquivalence_inverse_obj_top_left {X : Type u} [TopologicalSpace X] (U : Opens X) :
    ((Opens.overEquivalence U).inverse.obj ⊤).left = U := by
  ext x
  simp

end TopologicalSpace.Opens

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) (U : X.Opens)
  (hU : IsInCharacteristic U.toScheme p)

/-- **The Frobenius endomorphism of `𝒪_X`, restricted to the slice site at `U` and transported to
the site of the open subscheme `U`, is the Frobenius endomorphism of `𝒪_U`.** Both are the `p`-th
power map on sections: the transport reindexes the sections of `𝒪_X` along the opens of `U`, and
restriction to the slice site acts on sections by the original morphism
(`AlgebraicGeometry.overPullback_frobeniusRingSheafOnOpensHom_app`). -/
lemma sheafEquivOver_functor_map_frobeniusRingSheafOnOpensHom :
    (Opens.sheafEquivOver U (A := RingCat.{u})).functor.map
        (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} U).map
          (frobeniusRingSheafOnOpensHom X p hX)) =
      frobeniusRingSheafOnOpensHom U.toScheme p hU := by
  apply Sheaf.hom_ext
  ext W g
  exact (overPullback_frobeniusRingSheafOnOpensHom_app X p hX U
    (op ((Opens.overEquivalence U).inverse.obj W.unop)) g).trans
      (frobeniusPresheafHom_app_apply U.toScheme p hU W.unop g).symm

/-- **`colim_F 𝒪_X` restricted to an open `U` is `colim_F 𝒪_U`.** Under the equivalence
`TopologicalSpace.Opens.sheafEquivOver` between sheaves on the slice site `Opens(X)/U` and sheaves
on the open subscheme `U`, the restriction of the Frobenius colimit of the structure sheaf of `X`
is the Frobenius colimit of the structure sheaf of `U`.

This is the compatibility of the sheaf of rings of Stacks Tag 0EXB with passing to an open
subscheme. `AlgebraicGeometry.frobeniusColimitRingSheafOverIso` supplies the same statement on the
slice site; the content here is crossing to the site of the open subscheme, so that a theorem
about `colim_F 𝒪` of a scheme can be read on an open of another one. -/
noncomputable def frobeniusColimitRingSheafOpenIso :
    (Opens.sheafEquivOver U (A := RingCat.{u})).functor.obj
        ((frobeniusColimitRingSheaf X p hX).over U) ≅
      frobeniusColimitRingSheaf U.toScheme p hU :=
  (Opens.sheafEquivOver U (A := RingCat.{u})).functor.mapIso
      (frobeniusColimitRingSheafOverIso X p hX U) ≪≫
    ringSheafEndoColimitEquivIso _ (Opens.sheafEquivOver U (A := RingCat.{u})) ≪≫
    eqToIso (congrArg ringSheafEndoColimit
      (sheafEquivOver_functor_map_frobeniusRingSheafOnOpensHom X p hX U hU))

/-- **The sections form of the identification.** Over an open `W` of `U`, the sections of
`colim_F 𝒪_U` are the sections of `colim_F 𝒪_X` over the corresponding open of `X`. At `W = ⊤`
that open is `U` itself, by
`TopologicalSpace.Opens.overEquivalence_inverse_obj_top_left`. -/
noncomputable def frobeniusColimitRingSheafOpenSectionsIso (W : Opens ↥U) :
    (frobeniusColimitRingSheaf X p hX).obj.obj
        (op ((Opens.overEquivalence U).inverse.obj W).left) ≅
      (frobeniusColimitRingSheaf U.toScheme p hU).obj.obj (op W) :=
  ((sheafToPresheaf (Opens.grothendieckTopology ↥U) RingCat.{u}).mapIso
    (frobeniusColimitRingSheafOpenIso X p hX U hU)).app (op W)

/-- **Sections of `colim_F 𝒪_X` over `U` are the global sections of `colim_F 𝒪_U`.** This is
`AlgebraicGeometry.frobeniusColimitRingSheafOpenSectionsIso` at the top open of `U`, which
corresponds to `U` itself. It is the form in which a statement about the global sections of
`colim_F 𝒪` of a scheme is read as a statement about the sections of `colim_F 𝒪` of an ambient
scheme over an open — in particular the form in which the cartesian square of global sections at
Example 0EVH over a localisation is read over a basic open. -/
noncomputable def frobeniusColimitRingSheafOpenTopSectionsIso :
    (frobeniusColimitRingSheaf X p hX).obj.obj (op U) ≅
      (frobeniusColimitRingSheaf U.toScheme p hU).obj.obj (op ⊤) :=
  eqToIso (congrArg (fun V : X.Opens => (frobeniusColimitRingSheaf X p hX).obj.obj (op V))
      (Opens.overEquivalence_inverse_obj_top_left U).symm) ≪≫
    frobeniusColimitRingSheafOpenSectionsIso X p hX U hU ⊤

/-- **The identification of `colim_F 𝒪_X` restricted to `U` with `colim_F 𝒪_U`, read on the
restriction functor `TopologicalSpace.Opens.sheafRestrict` rather than on the composite of
`overPullback` with `TopologicalSpace.Opens.sheafEquivOver`.**

The two presentations of the restriction agree by `overPullbackSheafEquivOver`, which Mathlib
supplies as `Iso.refl`; naming this form matters only because it is the one
`TopologicalSpace.Opens.sheafOfModulesEquivOver` is stated against, and so the one a module-level
statement can be transported along. -/
noncomputable def frobeniusColimitRingSheafRestrictIso :
    U.sheafRestrict.obj (frobeniusColimitRingSheaf X p hX) ≅
      frobeniusColimitRingSheaf U.toScheme p hU :=
  ((Opens.overPullbackSheafEquivOver (A := RingCat.{u}) U).app
      (frobeniusColimitRingSheaf X p hX)).symm ≪≫
    frobeniusColimitRingSheafOpenIso X p hX U hU

/-- **The module-level half of the open-subscheme bridge**: sheaves of modules over the
restriction of `colim_F 𝒪_X` to the slice site at `U` are the same thing as sheaves of modules
over `colim_F 𝒪_U`.

It is the composition of two identifications, neither of which is about the Frobenius colimit:
`TopologicalSpace.Opens.sheafOfModulesEquivOver` crosses from the slice site `Opens(X)/U` to the
site `Opens U` of the open subscheme, and
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso` transports modules along the
identification `frobeniusColimitRingSheafRestrictIso` of the two sheaves of rings on that site.
The Frobenius colimit enters only through that one isomorphism. -/
noncomputable def frobeniusColimitModuleOpenEquiv :
    _root_.SheafOfModules.{u} ((frobeniusColimitRingSheaf X p hX).over U) ≌
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf U.toScheme p hU) :=
  (Opens.sheafOfModulesEquivOver U (frobeniusColimitRingSheaf X p hX)).trans
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (frobeniusColimitRingSheafRestrictIso X p hX U hU))

/-- **Restriction of a sheaf of modules over `colim_F 𝒪_X` to an open subscheme `U`**, as a
functor to sheaves of modules over `colim_F 𝒪_U`.

This is the functor whose absence blocked the trivialising-cover argument for [Stacks, Tag 0EXD]:
Mathlib's `SheafOfModules.overFunctor` restricts to the *slice site* at `U`, where no statement
about `colim_F 𝒪` of a scheme can be read, and
`AlgebraicGeometry.frobeniusColimitModuleOpenEquiv` carries that restriction to the site of the
open subscheme, where it can. -/
noncomputable def frobeniusColimitModuleRestrict :
    _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX) ⥤
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf U.toScheme p hU) :=
  _root_.SheafOfModules.overFunctor (frobeniusColimitRingSheaf X p hX) U ⋙
    (frobeniusColimitModuleOpenEquiv X p hX U hU).functor

/-! ### Freeness across the open-subscheme bridge -/

/-- **Restriction of scalars along `AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso`**,
named with its type ascribed.

The ascription is load-bearing, not cosmetic. Written inline, as
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
(frobeniusColimitRingSheafRestrictIso X p hX U hU)`, the module universe of the two categories
of sheaves of modules is left as a metavariable, and the `CategoryTheory.Category` instance
cannot be synthesised: the instance's hom universe is a `max` of the module universe with the
site's two universes, and Lean cannot solve a `max` equation for the unknown. With the universe
pinned by the ascribed type the same term elaborates. Every use below goes through this name
rather than through the inline form for that reason. -/
def frobeniusColimitRestrictScalarsEquiv :
    _root_.SheafOfModules.{u} ((Opens.sheafRestrict U).obj (frobeniusColimitRingSheaf X p hX)) ≌
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf U.toScheme p hU) :=
  Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (frobeniusColimitRingSheafRestrictIso X p hX U hU)

/-- **The open-subscheme bridge carries the structure sheaf to the structure sheaf.** The two
halves of `AlgebraicGeometry.frobeniusColimitModuleOpenEquiv` each do: the site change by
Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOverUnit`, which is the identity, and the
change of the sheaf of rings by
`Stacks.Sheaves.RingedPoint.restrictScalarsObjUnitIso`. -/
def frobeniusColimitModuleOpenEquivUnitIso :
    (frobeniusColimitModuleOpenEquiv X p hX U hU).functor.obj
        (_root_.SheafOfModules.unit ((frobeniusColimitRingSheaf X p hX).over U)) ≅
      _root_.SheafOfModules.unit (frobeniusColimitRingSheaf U.toScheme p hU) :=
  (frobeniusColimitRestrictScalarsEquiv X p hX U hU).functor.mapIso
      (Opens.sheafOfModulesEquivOverUnit U (frobeniusColimitRingSheaf X p hX)) ≪≫
    Stacks.Sheaves.RingedPoint.restrictScalarsObjUnitIso
      (frobeniusColimitRingSheafRestrictIso X p hX U hU)

/-- **The open-subscheme bridge carries free sheaves of modules to free sheaves of modules.**
A free sheaf of modules is a coproduct of copies of the structure sheaf, the bridge is an
equivalence and so preserves coproducts, and it fixes the structure sheaf by
`AlgebraicGeometry.frobeniusColimitModuleOpenEquivUnitIso`. -/
def frobeniusColimitModuleOpenEquivObjFree (I : Type u) :
    (frobeniusColimitModuleOpenEquiv X p hX U hU).functor.obj
        (_root_.SheafOfModules.free I) ≅
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf U.toScheme p hU) I :=
  _root_.SheafOfModules.freeIsoOfUnitIso
    (frobeniusColimitModuleOpenEquiv X p hX U hU).functor
    (frobeniusColimitModuleOpenEquivUnitIso X p hX U hU) I
    (inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      (frobeniusColimitModuleOpenEquiv X p hX U hU).functor))

/-- **A module trivialised over `U` on the slice site restricts to a free module on the open
subscheme `U`.** -/
def frobeniusColimitModuleRestrictObjFreeOfIso
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (I : Type u)
    (e : M.over U ≅ _root_.SheafOfModules.free I) :
    (frobeniusColimitModuleRestrict X p hX U hU).obj M ≅
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf U.toScheme p hU) I :=
  (frobeniusColimitModuleOpenEquiv X p hX U hU).functor.mapIso e ≪≫
    frobeniusColimitModuleOpenEquivObjFree X p hX U hU I

/-- **A finite locally free `colim_F 𝒪_X`-module is free on each member of an open cover, as a
`colim_F 𝒪_U`-module on the open subscheme.**

Finite local freeness of a sheaf of modules is *defined* as a cover of the space together with,
over each member, a finite generating family which is a basis — but the family lives over the
slice sheaf of rings `(colim_F 𝒪_X)|_U` on the slice site `Opens(X)/U`, which is not where a
statement about `colim_F 𝒪` of a *scheme* can be read. This theorem moves the trivialisation to
the site of the open subscheme and to the sheaf of rings `colim_F 𝒪_U` that the almost blowup
square of Stacks Example 0EVH over a localisation carries, which is the form the
trivialising-cover argument for [Stacks, Tag 0EXD] consumes.

The characteristic of each member is supplied by
`AlgebraicGeometry.isInCharacteristic_toScheme`, so no hypothesis beyond that of `X` is
needed. -/
theorem exists_cover_free_frobeniusColimitModuleRestrict
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    ∃ (I : Type u) (V : I → X.Opens) (K : I → Type u), (⨆ i, V i = ⊤) ∧
      (∀ i, Finite (K i)) ∧ ∀ i, Nonempty
        ((frobeniusColimitModuleRestrict X p hX (V i)
            (isInCharacteristic_toScheme hX (V i))).obj M ≅
          _root_.SheafOfModules.free (K i)) := by
  obtain ⟨q, hfree, hfin⟩ := h.exists_isFiniteLocallyFreeData
  refine ⟨q.I, q.X, fun i => (q.generators i).I,
    (Opens.coversTop_iff _ q.X).mp q.coversTop, fun i => (hfin.isFiniteType i).finite,
    fun i => ⟨?_⟩⟩
  have : IsIso (q.generators i).π := hfree.isIso i
  exact frobeniusColimitModuleRestrictObjFreeOfIso X p hX (q.X i)
    (isInCharacteristic_toScheme hX (q.X i)) M _ (asIso (q.generators i).π).symm

end AlgebraicGeometry

end
