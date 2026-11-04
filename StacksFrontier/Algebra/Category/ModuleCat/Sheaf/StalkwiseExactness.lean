module

public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Exactness, monomorphy and epimorphy of sheaves of modules are stalkwise

Let `X` be a topological space and `O` a sheaf of rings on `X`. This file proves that the
stalk functor `AlgebraicGeometry.SheafOfModules.stalkFunctor O x`, which takes a sheaf of
`O`-modules to its stalk at `x` as a module over the stalk `O_x`, is **exact**, and that it
**detects** exactness, monomorphy, epimorphy and isomorphy: a short complex of sheaves of
`O`-modules is exact if and only if its complex of stalk modules is exact at every point of
`X`, and a morphism is a monomorphism (respectively an epimorphism, respectively an
isomorphism) if and only if it is injective (respectively surjective, respectively bijective)
on every stalk.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.toTopSheaf` : the forgetful functor
  `SheafOfModules.toSheaf`, with its target spelled `TopCat.Sheaf AddCommGrpCat X` rather than
  `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`. The two are definitionally equal types
  carrying different `Category` instances; see the implementation notes.
* `AlgebraicGeometry.SheafOfModules.stalkFunctorCompForget₂` : the underlying abelian group of the
  stalk module is Mathlib's abelian-group stalk of the underlying sheaf of abelian groups, *on the
  nose* (it is `Iso.refl`).

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` : the stalk functor on
  sheaves of modules over a space preserves finite limits. With
  `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits` this says the stalk functor is
  exact.
* `AlgebraicGeometry.SheafOfModules.stalkMap_germ` : the stalk map sends the germ of a section to
  the germ of its image.
* `AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact` : a short complex of
  sheaves of modules is exact iff all of its complexes of stalk *modules* are exact.
* `AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap`,
  `AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap` and
  `AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap` : monomorphy, epimorphy and
  isomorphy are stalkwise.
* `AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact` : short
  exactness is stalkwise.

## Implementation notes

**Spaces, not general sites.** Everything here is for sheaves of modules on the site
`Opens.grothendieckTopology X` of a topological space `X`. The two inputs are Mathlib's
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` (exactness of a complex of sheaves of abelian
groups on a space is stalkwise) and Mathlib's `Module (R.stalk x)` instance on the abelian-group
stalk, both stated for `TopCat`/`Opens` only.

**Universes.** The single universe `u` carries the space, the sheaf of rings and the modules:
Mathlib's module structure on the stalk of a presheaf of modules
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) is stated only for `X : TopCat.{u}`,
`R : X.Presheaf RingCat.{u}` and `M : PresheafOfModules.{u} R`.

**`TopCat.Sheaf` versus `Sheaf (Opens.grothendieckTopology X)`.** These are definitionally equal
types with *different* `Category` instances (`TopCat.instCategorySheaf` and
`CategoryTheory.Sheaf.instCategory`), so an instance found for one spelling is not found for the
other: `ShortComplex.map F` needs `F.PreservesZeroMorphisms` at whichever spelling `F`'s source and
target are written, and Mathlib's stalkwise exactness theorem is stated at the `TopCat.Sheaf` one.
`toTopSheaf` pins that spelling, and the four instances after it transport `Faithful`, `Additive`,
`PreservesFiniteLimits` and `PreservesFiniteColimits` across.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 007T](https://stacks.math.columbia.edu/tag/007T)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ZeroObject

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-! ### The stalk map on germs -/

/-- The stalk map of a morphism of sheaves of modules sends the germ at `x` of a section to
the germ at `x` of its image. This formula determines `stalkMap`, since every element of a
stalk is a germ (`TopCat.Presheaf.exists_germ_eq`). -/
@[simp]
theorem stalkMap_germ {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) (U : Opens X)
    (hx : x ∈ U) (s : M.val.obj (op U)) :
    (stalkMap O x f).hom ((TopCat.Presheaf.germ M.val.presheaf U x hx).hom s) =
      (TopCat.Presheaf.germ N.val.presheaf U x hx).hom (f.val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf O.obj).map f.val) s

/-! ### The underlying sheaf of abelian groups, at the `TopCat.Sheaf` spelling -/

/-- The forgetful functor from sheaves of `O`-modules to sheaves of abelian groups, with its
target spelled `TopCat.Sheaf AddCommGrpCat X`. This is `SheafOfModules.toSheaf O` itself; only
the spelling of the target category differs, and that spelling is what decides which
instances typeclass search finds. -/
noncomputable def toTopSheaf :
    _root_.SheafOfModules.{u} O ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  _root_.SheafOfModules.toSheaf O

/-- The forgetful functor `toTopSheaf O` is faithful. -/
instance instFaithfulToTopSheaf : (toTopSheaf O).Faithful :=
  inferInstanceAs (_root_.SheafOfModules.toSheaf.{u} O).Faithful

/-- The functor `toTopSheaf O` is additive. -/
instance instAdditiveToTopSheaf : (toTopSheaf O).Additive :=
  inferInstanceAs (_root_.SheafOfModules.toSheaf.{u} O).Additive

/-- The functor `toTopSheaf O` preserves finite limits. -/
noncomputable instance instPreservesFiniteLimitsToTopSheaf :
    PreservesFiniteLimits (toTopSheaf O) :=
  inferInstanceAs (PreservesFiniteLimits (_root_.SheafOfModules.toSheaf.{u} O))

/-- The functor `toTopSheaf O` preserves finite colimits. -/
noncomputable instance instPreservesFiniteColimitsToTopSheaf :
    PreservesFiniteColimits (toTopSheaf O) :=
  inferInstanceAs (PreservesFiniteColimits (_root_.SheafOfModules.toSheaf.{u} O))

/-! ### The stalk functor is exact -/

/-- The underlying abelian group of the stalk module of a sheaf of modules is the
abelian-group stalk of the underlying sheaf of abelian groups, on the nose. -/
noncomputable def stalkFunctorCompForget₂ :
    stalkFunctor O x ⋙
        forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
          AddCommGrpCat.{u} ≅
      toTopSheaf O ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
  Iso.refl _

/-- The stalk functor on sheaves of modules over a topological space preserves finite limits.
Together with `stalkFunctor_preservesColimits` this says it is an exact functor. -/
noncomputable instance stalkFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (stalkFunctor O x) :=
  haveI : PreservesFiniteLimits (stalkFunctor O x ⋙
      forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
        AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (stalkFunctorCompForget₂ O x).symm
  preservesFiniteLimits_of_reflects_of_preserves (stalkFunctor O x)
    (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
      AddCommGrpCat.{u})

/-! ### Stalkwise criteria -/

variable {O x}

/-- **Exactness is stalkwise.** A short complex of sheaves of modules on a topological space is
exact if and only if, for every point, the induced short complex of stalk modules is exact. The
form with abelian-group stalks is
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`. -/
theorem exact_iff_stalkFunctor_map_exact (S : ShortComplex (_root_.SheafOfModules.{u} O)) :
    S.Exact ↔ ∀ x : X, (S.map (stalkFunctor O x)).Exact := by
  refine ((S.exact_map_iff_of_faithful (toTopSheaf O)).symm.trans
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map (toTopSheaf O)))).trans
    (forall_congr' fun x => ?_)
  rw [(S.map (stalkFunctor O x)).exact_iff_exact_map_forget₂]
  exact ShortComplex.exact_iff_of_iso (ShortComplex.mapNatIso S (stalkFunctorCompForget₂ O x))

/-- **Monomorphy is stalkwise.** A morphism of sheaves of modules is a monomorphism exactly
when it is injective on every stalk. -/
theorem mono_iff_injective_stalkMap {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) :
    Mono f ↔ ∀ x : X, Function.Injective (stalkMap O x f).hom := by
  rw [← ShortComplex.exact_iff_mono (S := ShortComplex.mk (0 : 0 ⟶ M) f (by simp)) (by simp),
    exact_iff_stalkFunctor_map_exact]
  refine forall_congr' fun x => ?_
  rw [← ModuleCat.mono_iff_injective]
  exact ShortComplex.exact_iff_mono _ (by simp)

/-- **Epimorphy is stalkwise.** A morphism of sheaves of modules is an epimorphism exactly
when it is surjective on every stalk. -/
theorem epi_iff_surjective_stalkMap {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) :
    Epi f ↔ ∀ x : X, Function.Surjective (stalkMap O x f).hom := by
  rw [← ShortComplex.exact_iff_epi (S := ShortComplex.mk f (0 : N ⟶ 0) (by simp)) (by simp),
    exact_iff_stalkFunctor_map_exact]
  refine forall_congr' fun x => ?_
  rw [← ModuleCat.epi_iff_surjective]
  exact ShortComplex.exact_iff_epi _ (by simp)

/-- **Isomorphy is stalkwise.** A morphism of sheaves of modules is an isomorphism exactly
when it is bijective on every stalk. -/
theorem isIso_iff_bijective_stalkMap {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, Function.Bijective (stalkMap O x f).hom := by
  constructor
  · intro hf x
    exact ⟨(mono_iff_injective_stalkMap f).1 inferInstance x,
      (epi_iff_surjective_stalkMap f).1 inferInstance x⟩
  · intro hf
    have := (mono_iff_injective_stalkMap f).2 fun x => (hf x).1
    have := (epi_iff_surjective_stalkMap f).2 fun x => (hf x).2
    exact isIso_of_mono_of_epi f

/-- **Short exactness is stalkwise.** A short complex of sheaves of modules is short exact
exactly when all of its complexes of stalk modules are short exact. -/
theorem shortExact_iff_stalkFunctor_map_shortExact
    (S : ShortComplex (_root_.SheafOfModules.{u} O)) :
    S.ShortExact ↔ ∀ x : X, (S.map (stalkFunctor O x)).ShortExact := by
  constructor
  · intro hS x
    have := hS.mono_f
    have := hS.epi_g
    refine ShortComplex.ShortExact.mk' (hS.exact.map _) ?_ ?_
    · exact Functor.map_mono (stalkFunctor O x) S.f
    · exact Functor.map_epi (stalkFunctor O x) S.g
  · intro hS
    have h₁ : Mono S.f := (mono_iff_injective_stalkMap S.f).2 fun x =>
      (ModuleCat.mono_iff_injective _).1 (hS x).mono_f
    have h₂ : Epi S.g := (epi_iff_surjective_stalkMap S.g).2 fun x =>
      (ModuleCat.epi_iff_surjective _).1 (hS x).epi_g
    exact ShortComplex.ShortExact.mk'
      ((exact_iff_stalkFunctor_map_exact S).2 fun x => (hS x).exact) h₁ h₂

end AlgebraicGeometry.SheafOfModules

end
