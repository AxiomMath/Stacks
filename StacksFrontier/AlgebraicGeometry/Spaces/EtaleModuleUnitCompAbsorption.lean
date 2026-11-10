module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackCompUnit

/-!
# The absorption of the fourth factor, and the inner unit on a section

Let `h : D ⟶ A` and `g : A ⟶ C` be étale morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B`.  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackCompUnit.lean`
decomposes the unit of `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` into four factors
and reads three of them; what its "What is not done" section records as owed is the **absorption of
the fourth factor** and the join of the two halves of the reading on a section.  Both are proved
here.

## Main results

* `AlgebraicGeometry.Space.modulesHom_comp_comp_val_app_apply`: a threefold composite of
  morphisms of modules acts on a local section as the three actions in turn.  Stated on
  variables, which is what makes it able to decompose the inner unit in **one** step; the two-step
  decomposition through the middle object is what exhausts the heartbeat budget.
* `AlgebraicGeometry.Space.modulesHom_ext`: two morphisms of modules that agree on every local
  section are equal.  Stated on variables, so that the extensionality of sheaves of modules is
  elaborated once at a variable site.
* `AlgebraicGeometry.Space.innerUnit_comp_modulePushforward_map_eq_self`: **the absorption of the
  fourth factor** — the inner unit followed by the direct image along the composite of the
  comparison of iterated restrictions is the inner unit itself.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app_eq_inner`: consequently the
  unit of `etaleModulePullbackCompAdjunction` at a module **is** the inner unit at that module.
* `AlgebraicGeometry.Space.innerUnitVal`: **the inner unit on a section is the unit of étale
  restriction along `h ≫ g` on that section.**  This is the join of `innerUnitVal₁₂` with
  `innerUnitVal₃₄` and `innerUnitVal₅₆`, the join that the predecessor file records as
  unavailable.
* `AlgebraicGeometry.Space.innerUnit_target_eq_unit_target`: the two spellings of the target of
  the unit agree, as objects.  This is the measurement that the implementation notes below turn
  on.

## Implementation notes

The spelling discipline is the one recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackCompUnit.lean`: never write a statement
that mixes two spellings of one object, let `congrArg` and `Eq.trans` determine the type, and
where a term must be named, ascribe it the way the consuming lemma spells it.  Two further
measurements are recorded here, and they are what the proofs are shaped by.

**The absorption.**  The two halves of it that the predecessor file supplies —
`innerUnit_comp_modulePushforward_map_id_nested` and `innerUnit_comp_map_id` — cannot be joined,
because the `CategoryTheory.CategoryStruct.comp` of the first has its target object spelled as the
direct image of the *composite* restriction and the `CategoryTheory.CategoryStruct.comp` of the
second has it spelled as the direct image of the *iterated* restriction, so the join asks the
unifier to cross the two inside a `Quiver.Hom`.  The route taken here removes the mismatch at its
source instead of crossing it: `modulePushforward_map_etaleModulePullbackComp_hom_app_atEndo`
reads the folded map-identity equation at the **endomorphism** hom type of the iterated spelling,
after which `Stacks.comp_congr_right` builds a composite whose target is that spelling and
`CategoryTheory.Category.comp_id` matches it syntactically.  No crossing is left to do.

**Which crossings are affordable.**  The decisive fact is
`innerUnit_target_eq_unit_target`: the two spellings
`(etaleModulePullback g ⋙ etaleModulePullback h) ⋙ modulePushforward (h ≫ g)` and
`etaleModulePullback (h ≫ g) ⋙ modulePushforward (h ≫ g)` agree *at an object* by `rfl`, and
cheaply, while they do **not** agree affordably as functors — `etaleModulePullback (h ≫ g)` against
`etaleModulePullback g ⋙ etaleModulePullback h` exhausts the budget on its own.  So a unification
that reaches the two spellings through `CategoryTheory.Functor.obj` congruence, which compares the
two *functors*, is fatal, while one that reduces the `CategoryTheory.Functor.comp` projection
first is not.  Concretely: a crossing inside a `Quiver.Hom` is affordable (which is why
`etaleModulePullbackCompAdjunction_unit_app_eq_inner` elaborates at all), and a crossing inside a
`SheafOfModules.Hom.val` applied to a section is not.

The reason the last one is not is sharper than the spelling: `val` is a
projection, so two applications of it are not compared argument by argument — `whnf` is asked for
the morphism in constructor form first.  For a *composite* of morphisms that reduces, and the
crossing costs nothing, which is why the two spellings of the target meet freely in
`innerUnitVal₁₂₃`; for the unit of one of these adjunctions it does not terminate inside the
budget, whatever the two spellings are.  So the rule is not "do not cross inside
`SheafOfModules.Hom.val`" but "where two readings of a *unit* on a section meet, their `val` must
already be at one spelling", and the spelling is chosen by giving
`modulesHom_val_app_congr` its target module explicitly.

## What this leaves

`hu`, the comparison of the units

```
(etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
  (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit
```

— and with it `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`
— is **proved**, in `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompJoin.lean`, as
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit` and
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`.  What this file owed it is the
pair above: `etaleModulePullbackCompAdjunction_unit_app_eq_inner` and `innerUnitVal`.  The one
step left over — lifting `innerUnitVal` from sections to the component through
`modulesHom_ext` — is carried out there, and the measurement that closes it is recorded there
too: the lift must leave the target module of `modulesHom_ext` to be read off the hypothesis,
where it comes out as the written-out
`(modulePushforward (h ≫ g)).obj ((etaleModulePullback h).obj ((etaleModulePullback g).obj M))`,
and each retyping around it must be its own declaration.  Pinning that target at either spelling
of the unit's target, and three other shapes of the same join, exhaust the heartbeat budget.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

/-! ### Sections of a morphism of modules, on variables -/

section Sections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}

/-- A threefold composite of morphisms of `𝒪_Y`-modules acts on a local section as the three
actions in turn.  Stated on variables, so that no spelling of either middle object has to be
matched against a concrete term: the two-step decomposition through them does not elaborate. -/
theorem modulesHom_comp_comp_val_app_apply {M N P Q : Modules.{u, u} B S hS Y hY} (f : M ⟶ N)
    (f₁ : N ⟶ P) (f₂ : P ⟶ Q) (W : (SmallEtale B S hS Y)ᵒᵖ) (x : M.val.obj W) :
    (f ≫ f₁ ≫ f₂).val.app W x = f₂.val.app W (f₁.val.app W (f.val.app W x)) :=
  rfl

/-- Two morphisms of `𝒪_Y`-modules that agree on every local section are equal.  Stated on
variables, so that the extensionality of sheaves of modules is elaborated once at a variable site
and every use is substitution. -/
theorem modulesHom_ext {M N : Modules.{u, u} B S hS Y hY} {f g : M ⟶ N}
    (hfg : ∀ (W : (SmallEtale B S hS Y)ᵒᵖ) (x : M.val.obj W), f.val.app W x = g.val.app W x) :
    f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun x => hfg W x))

end Sections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D : AlgebraicSpaces B S hS}
variable (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
variable (M : Modules.{u, u} B S hS C.1 C.2)

/-! ### The absorption of the fourth factor -/

/-- The two spellings of the target of the unit of étale restriction along a composite agree as
objects: the iterated restriction followed by the direct image, and the restriction along the
composite followed by the direct image.  The same identity **between the two functors** is not
affordable, which is the measurement the implementation notes turn on. -/
theorem innerUnit_target_eq_unit_target :
    ((etaleModulePullback.{u, u} B S hS g hg ⋙ etaleModulePullback.{u, u} B S hS h hh) ⋙
        modulePushforward B S hS (h ≫ g)).obj M =
      (etaleModulePullback.{u, u} B S hS (h ≫ g) hhg ⋙
        modulePushforward B S hS (h ≫ g)).obj M :=
  rfl

set_option maxHeartbeats 400000 in
-- The statement is the type of the proof term (`type_of%`), so the term is elaborated twice,
-- once in the statement and once as the proof, which exceeds the default limit.
/-- The direct image along `h ≫ g` of the comparison of iterated restrictions is the identity,
read at the **endomorphism** hom type of the iterated spelling.  Reading it there is what lets
the absorption be a syntactic match rather than a crossing of two spellings. -/
theorem modulePushforward_map_etaleModulePullbackComp_hom_app_atEndo :
    type_of% (Stacks.eq_atType
      (α := ((modulePushforward B S hS (h ≫ g)).obj
            ((etaleModulePullback.{u, u} B S hS h hh).obj
              ((etaleModulePullback.{u, u} B S hS g hg).obj M)) ⟶
          (modulePushforward B S hS (h ≫ g)).obj
            ((etaleModulePullback.{u, u} B S hS h hh).obj
              ((etaleModulePullback.{u, u} B S hS g hg).obj M))))
      (modulePushforward_map_etaleModulePullbackComp_hom_app B S hS h g hh hg hhg M)) :=
  (Stacks.eq_atType
     (α := ((modulePushforward B S hS (h ≫ g)).obj
           ((etaleModulePullback.{u, u} B S hS h hh).obj
             ((etaleModulePullback.{u, u} B S hS g hg).obj M)) ⟶
         (modulePushforward B S hS (h ≫ g)).obj
           ((etaleModulePullback.{u, u} B S hS h hh).obj
             ((etaleModulePullback.{u, u} B S hS g hg).obj M))))
     (modulePushforward_map_etaleModulePullbackComp_hom_app B S hS h g hh hg hhg M) :)

set_option maxHeartbeats 400000 in
-- The statement is the type of the proof term (`type_of%`), so the term is elaborated twice,
-- once in the statement and once as the proof, which exceeds the default limit.
/-- The inner unit followed by the direct image of the comparison of iterated restrictions, with
that factor rewritten to the identity of the iterated spelling. -/
theorem innerUnit_comp_modulePushforward_map_atEndo :
    type_of% (Stacks.comp_congr_right
      ((((etaleModulePullbackAdjunction B S hS g hg).comp
          (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
            (modulePushforwardCompIso B S hS h g)).unit.app M)
      (modulePushforward_map_etaleModulePullbackComp_hom_app_atEndo B S hS h g hh hg hhg M)) :=
  (Stacks.comp_congr_right
     ((((etaleModulePullbackAdjunction B S hS g hg).comp
         (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
           (modulePushforwardCompIso B S hS h g)).unit.app M)
     (modulePushforward_map_etaleModulePullbackComp_hom_app_atEndo B S hS h g hh hg hhg M) :)

set_option maxHeartbeats 400000 in
-- The statement is the type of the proof term (`type_of%`), so the term is elaborated twice,
-- once in the statement and once as the proof, which exceeds the default limit.
/-- **The absorption of the fourth factor.**  The inner unit of the composite adjunction,
followed by the direct image along `h ≫ g` of the comparison of iterated restrictions, is the
inner unit itself. -/
theorem innerUnit_comp_modulePushforward_map_eq_self :
    type_of% ((innerUnit_comp_modulePushforward_map_atEndo B S hS h g hh hg hhg M).trans
      (CategoryTheory.Category.comp_id
        ((((etaleModulePullbackAdjunction B S hS g hg).comp
            (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
              (modulePushforwardCompIso B S hS h g)).unit.app M))) :=
  ((innerUnit_comp_modulePushforward_map_atEndo B S hS h g hh hg hhg M).trans
     (CategoryTheory.Category.comp_id
       ((((etaleModulePullbackAdjunction B S hS g hg).comp
           (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
             (modulePushforwardCompIso B S hS h g)).unit.app M)) :)

set_option maxHeartbeats 400000 in
-- The statement is the type of the proof term (`type_of%`), so the term is elaborated twice,
-- once in the statement and once as the proof, which exceeds the default limit.
/-- **The unit of `etaleModulePullbackCompAdjunction` at a module is the inner unit at that
module.**  The four-factor decomposition of the composite unit, with the fourth factor
absorbed. -/
theorem etaleModulePullbackCompAdjunction_unit_app_eq_inner :
    type_of% ((etaleModulePullbackCompAdjunction_unit_app B S hS h g hh hg hhg M).trans
      (innerUnit_comp_modulePushforward_map_eq_self B S hS h g hh hg hhg M)) :=
  ((etaleModulePullbackCompAdjunction_unit_app B S hS h g hh hg hhg M).trans
     (innerUnit_comp_modulePushforward_map_eq_self B S hS h g hh hg hhg M) :)

/-! ### The inner unit on a section -/

variable (W : (SmallEtale B S hS C.1)ᵒᵖ)

/-- The inner unit on a section, decomposed into its three factors in one step.  This is the join
of `innerUnitVal₁₂` with `innerUnitVal₃₄` that the predecessor file records as unavailable: the
threefold decomposition on variables replaces the two-step one through the middle object. -/
theorem innerUnitVal₁₂₃ (s : M.val.obj W) :
    type_of% ((innerUnitStep₁ B S hS h g hh hg M W s).trans
      (modulesHom_comp_comp_val_app_apply
        ((etaleModulePullbackAdjunction B S hS g hg).unit.app M)
        ((modulePushforward B S hS g).map
          ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)))
        ((modulePushforwardCompIso B S hS h g).hom.app
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W s)) :=
  ((innerUnitStep₁ B S hS h g hh hg M W s).trans
     (modulesHom_comp_comp_val_app_apply
       ((etaleModulePullbackAdjunction B S hS g hg).unit.app M)
       ((modulePushforward B S hS g).map
         ((etaleModulePullbackAdjunction B S hS h hh).unit.app
           ((etaleModulePullback.{u, u} B S hS g hg).obj M)))
       ((modulePushforwardCompIso B S hS h g).hom.app
         ((etaleModulePullback.{u, u} B S hS h hh).obj
           ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W s) :)

set_option maxHeartbeats 400000 in
-- The statement is the type of the proof term (`type_of%`), so the term is elaborated twice,
-- once in the statement and once as the proof, which exceeds the default limit.
/-- **The inner unit on a section is the unit of étale restriction along `h ≫ g` on that
section.**  The threefold decomposition, then the comparison of the two direct images read as an
iterated restriction of sheaves of sets, then the composition law of Stacks 03LQ. -/
theorem innerUnitVal (s : M.val.obj W) :
    type_of% ((innerUnitVal₁₂₃ B S hS h g hh hg M W s).trans
      ((modulePushforwardCompIso_hom_app_val_app_setRestriction B S hS h g hh hg M W _).trans
        (innerUnitVal₅₆ B S hS h g hh hg hhg M W s))) :=
  ((innerUnitVal₁₂₃ B S hS h g hh hg M W s).trans
     ((modulePushforwardCompIso_hom_app_val_app_setRestriction B S hS h g hh hg M W _).trans
       (innerUnitVal₅₆ B S hS h g hh hg hhg M W s)) :)

/-- The unit of étale restriction along `h ≫ g`, read at the hom type whose target is spelled as
the iterated restriction followed by the direct image.  Ascribing it this way is affordable; the
corresponding crossing inside a `SheafOfModules.Hom.val` at a section is not, which is what the
"What is not done" section of this file records. -/
def unitAtInner :
    M ⟶ ((etaleModulePullback.{u, u} B S hS g hg ⋙ etaleModulePullback.{u, u} B S hS h hh) ⋙
      modulePushforward B S hS (h ≫ g)).obj M :=
  (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit.app M

end AlgebraicGeometry.Space

end
