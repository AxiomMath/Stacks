module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules for a coarser topology

Let `C` be a category carrying two Grothendieck topologies `J' ≤ J`, and let `R` be a sheaf of
rings for `J`. Then `R` is also a sheaf of rings for `J'`, and the identity functor on `C` is a
morphism of sites `C_J ⟶ C_{J'}` whose direct image `ε_*` is the identity on underlying
presheaves and whose inverse image `ε^*` is `J`-sheafification. This file builds that pair for
sheaves of modules, proves it adjoint, and deduces that `ε_*` preserves K-injective complexes.

## Main definitions

* `Stacks.Sites.CoarserTopology.ringSheafOfLe`: a sheaf of rings for `J`, regarded as a sheaf of
  rings for the coarser topology `J'`.
* `AlgebraicGeometry.RingedSite.ofLe`: a ringed site, regarded as a ringed site for a coarser
  topology.
* `Stacks.Sites.CoarserTopology.modulePushforward`: `ε_*`, a sheaf of modules for `J` regarded as
  a sheaf of modules for `J'`, with the same underlying presheaf of modules.
* `Stacks.Sites.CoarserTopology.modulePullback`: `ε^*`, the `J`-sheafification of the underlying
  presheaf of modules of a sheaf of modules for `J'`.

## Main results

* `Stacks.Sites.CoarserTopology.modulePullbackAdjPushforward`: `ε^* ⊣ ε_*`.
* `Stacks.Sites.CoarserTopology.isKInjective_modulePushforward`: **Stacks 093Y for `ε`**, that
  `ε_*` carries a K-injective complex of `J`-sheaves of modules to a K-injective complex of
  `J'`-sheaves of modules, because `ε^*` is an exact left adjoint of it.

## Implementation notes

`ε_*` is *defined* to be the identity on underlying presheaves of modules, rather than obtained
from `SheafOfModules.pushforward` along the identity functor of `C`. Both are the direct image
of the same morphism of sites, but the latter inserts `Functor.op (𝟭 C)` and a restriction of
scalars along `𝟙 R` into every object, so that sections of `ε_* M` over `U` are no longer the
*same term* as sections of `M` over `U`. That identity of terms is what makes the comparison
maps of a complex over the two sites literally equal.

`ε^*` is exact. Left exactness is `PreservesFiniteLimits`, a composite of the forgetful functor
to presheaves of modules, which is a right adjoint, with `J`-sheafification, which is left exact.
Right exactness needs no separate argument: `ε^*` is a left adjoint.

Exhibiting the adjunction `ε^* ⊣ ε_*` is a restriction of Mathlib's
`PresheafOfModules.sheafificationAdjunction` along the fully faithful forgetful functor
`SheafOfModules.{v} (ringSheafOfLe h R) ⥤ PresheafOfModules.{v} R.obj`, by
`CategoryTheory.Adjunction.restrictFullyFaithful`. Both commutation isomorphisms it asks for are
the identity: `ε^*` is by definition the composite of that forgetful functor with
sheafification, and `ε_*` followed by the forgetful functor is the forgetful functor of the
finer site, since `ε_*` does not change the underlying presheaf of modules.

## References

* [Stacks Project, Tag 0F17](https://stacks.math.columbia.edu/tag/0F17)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace Stacks.Sites.CoarserTopology

variable {C : Type u} [Category.{w} C] {J J' : GrothendieckTopology C} (h : J' ≤ J)

section RingSheaf

variable (R : Sheaf J RingCat.{r})

/-- A sheaf of rings for a topology `J`, regarded as a sheaf of rings for a coarser topology
`J'`: a `J'`-covering is a `J`-covering, so the descent conditions for `J'` are among those for
`J`. -/
abbrev ringSheafOfLe : Sheaf J' RingCat.{r} := ⟨R.obj, R.property.of_le h⟩

end RingSheaf

section Pushforward

variable (R : Sheaf J RingCat.{r})

/-- **The direct image `ε_*` of the comparison of two topologies, on sheaves of modules.** A
sheaf of modules for the finer topology `J` is a sheaf of modules for the coarser topology `J'`,
with the same underlying presheaf of modules. -/
def modulePushforward :
    SheafOfModules.{v} R ⥤ SheafOfModules.{v} (ringSheafOfLe h R) where
  obj M := { val := M.val, isSheaf := M.isSheaf.of_le h }
  map φ := { val := φ.val }

/-- `ε_*` is the identity on underlying presheaves of modules. -/
@[simp]
lemma modulePushforward_obj_val (M : SheafOfModules.{v} R) :
    ((modulePushforward.{u, v, w, r} h R).obj M).val = M.val := rfl

/-- `ε_*` is the identity on morphisms of underlying presheaves of modules. -/
@[simp]
lemma modulePushforward_map_val {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    ((modulePushforward.{u, v, w, r} h R).map φ).val = φ.val := rfl

/-- `ε_*` is fully faithful: a morphism of sheaves of modules is a morphism of the underlying
presheaves of modules, and `ε_*` does not change those. -/
def fullyFaithfulModulePushforward : (modulePushforward.{u, v, w, r} h R).FullyFaithful where
  preimage φ := ⟨φ.val⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- `ε_*` is full. -/
instance : (modulePushforward.{u, v, w, r} h R).Full :=
  (fullyFaithfulModulePushforward.{u, v, w, r} h R).full

/-- `ε_*` is faithful. -/
instance : (modulePushforward.{u, v, w, r} h R).Faithful :=
  (fullyFaithfulModulePushforward.{u, v, w, r} h R).faithful

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- `ε_*` is additive. -/
instance modulePushforward_additive : (modulePushforward.{u, v, w, r} h R).Additive where
  map_add := rfl

end Pushforward

section Pullback

variable (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The inverse image `ε^*` of the comparison of two topologies, on sheaves of modules.** A
sheaf of modules for the coarser topology `J'` is `J`-sheafified: its underlying presheaf of
modules is taken, and the associated sheaf of modules for `J` is formed. -/
noncomputable def modulePullback :
    SheafOfModules.{v} (ringSheafOfLe h R) ⥤ SheafOfModules.{v} R :=
  SheafOfModules.forget (ringSheafOfLe h R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

/-- **`ε^* ⊣ ε_*`.** A morphism from the `J`-sheafification of a `J'`-sheaf of modules `M` to a
`J`-sheaf of modules `N` is a morphism of presheaves of modules `M ⟶ N`, which is the same thing
as a morphism `M ⟶ ε_* N` of `J'`-sheaves of modules. -/
noncomputable def modulePullbackAdjPushforward :
    modulePullback.{u, v, w, r} h R ⊣ modulePushforward.{u, v, w, r} h R :=
  Adjunction.restrictFullyFaithful
    (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj))
    (SheafOfModules.fullyFaithfulForget.{v} (ringSheafOfLe h R))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- `ε^*` is left exact: it preserves finite limits. -/
noncomputable instance modulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (modulePullback.{u, v, w, r} h R) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.forget (ringSheafOfLe h R) ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)))

/-- `ε^*` is right exact: it preserves finite colimits. -/
noncomputable instance modulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (modulePullback.{u, v, w, r} h R) :=
  letI : PreservesColimitsOfSize.{0, 0} (modulePullback.{u, v, w, r} h R) :=
    (modulePullbackAdjPushforward.{u, v, w, r} h R).leftAdjoint_preservesColimits
  inferInstance

/-- `ε^*` is additive. -/
noncomputable instance modulePullback_additive :
    (modulePullback.{u, v, w, r} h R).Additive :=
  (modulePullbackAdjPushforward.{u, v, w, r} h R).left_adjoint_additive

/-- **Stacks 093Y for the comparison of two topologies.** `ε_*` carries a K-injective complex of
`J`-sheaves of modules to a K-injective complex of `J'`-sheaves of modules, since it is the
right adjoint of the exact functor `ε^*`. -/
theorem isKInjective_modulePushforward
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((modulePushforward.{u, v, w, r} h R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
    (modulePullback.{u, v, w, r} h R) (modulePullbackAdjPushforward.{u, v, w, r} h R) I

end Pullback

end Stacks.Sites.CoarserTopology

namespace AlgebraicGeometry.RingedSite

/-- A ringed site, regarded as a ringed site for a coarser topology: the structure sheaf for the
finer topology is a sheaf for the coarser one. -/
abbrev ofLe (S : RingedSite.{u, w, r}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J) :
    RingedSite.{u, w, r} where
  C := S.C
  J := J'
  O := ⟨S.O.obj, S.O.property.of_le h⟩

end AlgebraicGeometry.RingedSite

end
