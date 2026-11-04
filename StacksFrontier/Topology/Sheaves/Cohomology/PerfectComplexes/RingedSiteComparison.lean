module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.IteratedRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness on a ringed space and on its ringed site of opens

A ringed space `(X, O_X)` *is* a ringed site: its site of opens with the open-cover topology,
with the same structure sheaf (`Stacks.SheafOfModules.ringedSite`). Perfectness of a complex of
`O_X`-modules is therefore defined twice over, once for each reading:

* `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex` ([Stacks, Tag 08CM]) asks for *one* open
  cover of `X` over each member of which the complex is quasi-isomorphic to a strictly perfect
  complex, the restriction being taken to the *restricted ringed space*;
* `AlgebraicGeometry.RingedSite.IsPerfectComplex` ([Stacks, Tag 08G5]) asks for a covering of
  *every* object of the site, the restriction being `SheafOfModules.overFunctor` into modules
  over the *slice* sheaf of rings.

This file proves that the two agree, and likewise for the derived-category predicates
`Stacks.Cohomology.PerfectComplexes.IsPerfect` and `AlgebraicGeometry.RingedSite.IsPerfect`.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff_ringedSite` and
  `Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite`: the two readings of
  [Stacks, Tags 08CM and 08G5] agree on a ringed space.
* `Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_iff_ringSheaf`: the ringed-space notion
  of a strictly perfect complex is the ringed-site notion at the structure sheaf of rings.
* `Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_restrictComplexEquiv` and
  `Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_restrictComplexEquiv_inverse`: strict
  perfectness of a complex of modules over the slice sheaf of rings on `Over U` is strict
  perfectness of its transport to the restricted ringed space, and conversely.
* `Stacks.Cohomology.PerfectComplexes.exists_strictlyPerfect_restrictComplex` and
  `Stacks.Cohomology.PerfectComplexes.exists_strictlyPerfect_restrictComplex_ringedSite`: a
  local strictly perfect model over an open in one reading is one in the other.

## Implementation notes

**Why there is anything to prove.** The ring sheaves and the categories of modules agree on the
nose: `Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O`
and
`StrictlyPerfect.structureSheafOfRings X` are the same sheaf of rings, and so are their slices
over an open. What differs is the *target of restriction* — the slice sheaf of rings on `Over U`
against the structure sheaf of `X.restrict U` — and the *shape of the locality condition*.

The first difference is `AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`
(Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOver`), under which the site's
`restrictComplex` *is* the space's `restrictComplex`, definitionally. That equivalence carries
the unit to the unit, again definitionally, so it transports strict perfectness in both
directions by `SheafOfModules.isStrictlyPerfect_map`.

The second difference is bridged by a sieve. Being quasi-isomorphic to a strictly perfect
complex over an object of the site is inherited by every arrow into that object, because
restriction along an arrow is exact and preserves the unit; so the arrows with that property
form a sieve, `quasiStrictlyPerfectSieve`. A single open cover of `X` makes that sieve covering
at `⊤`, and pulling back along the unique arrow `V ⟶ ⊤` makes it covering at every `V`. In the
other direction the covering sieve at `⊤` is itself an open cover of `X`, so the single cover
asked for by [Stacks, Tag 08CM] is read off the site condition at the final object.

**Strict perfectness has two spellings on a ringed space.** `StrictlyPerfect.IsStrictlyPerfect`
is stated for `StrictlyPerfect.OXMod` with the termwise condition at a module universe
independent of the ring universe, and `IsStrictlyPerfect` for a sheaf of rings on a site with
its own. At the common universe both are the plain condition that each term be a retract of
`O_X^{⊕n}`, the two spellings of that module being identified by
`StrictlyPerfect.finiteFreeIsoFree`; `isStrictlyPerfect_iff_ringSheaf` is that comparison.

**Quasi-isomorphisms and instance synthesis.** Every transport of a quasi-isomorphism below is
routed through a lemma whose complexes are abstract — `quasiIso_restrictComplexEquiv_map`,
`quasiIso_restrictComplexEquiv_inverse_map`, `quasiIso_overMap_map`, `quasiIso_comp_iso_hom`,
`quasiIso_comp_iso_inv` — rather than left to instance synthesis at the concrete restriction.
`QuasiIso` carries the two `HasHomology` families as instance arguments, and synthesizing them
at a term containing `RingedSite.restrictComplex` unfolds the slice restriction functor; done
inline that exhausts the heartbeat budget, whereas at an abstract pair of complexes the same
instances are immediate from `Abelian`.

**Composing with [Stacks, Tag 08JJ].** The comparison below is at an arbitrary `u`, and
[Stacks, Tag 08JJ], `AlgebraicGeometry.RingedSite.isPerfect_derivedDual`, now matches it: the
derived-internal-Hom and perfectness clusters were generalized in the module universe, so
`Stacks.SheafOfModules.isPerfect_derivedDual`
(`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/PerfectDual.lean`) is stated at a
`universe u` rather than at `RingedSite.{0, 0, 0}` with modules in `SheafOfModules.{0}`. The two
therefore compose on `Scheme.{u}`, which is what
`Stacks.DerivedQCoh.isPerfect_derivedDual` of
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.DualOfAPerfectComplex` uses.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.PseudoCoherence
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u d

namespace Stacks.Cohomology.PerfectComplexes

variable (X : RingedSpace.{u, u})

/-! ### Two bookkeeping lemmas about quasi-isomorphisms -/

/-- A quasi-isomorphism followed by an isomorphism is a quasi-isomorphism. Stated for abstract
complexes so that no instance has to be synthesized at the concrete restrictions below. -/
theorem quasiIso_comp_iso_hom {A : Type*} [Category* A] [Abelian A]
    {P Q R : CochainComplex A ℤ} (f : P ⟶ Q) (hf : QuasiIso f) (e : Q ≅ R) :
    QuasiIso (f ≫ e.hom) := by
  have := hf
  infer_instance

/-- A quasi-isomorphism followed by the inverse of an isomorphism is a quasi-isomorphism. -/
theorem quasiIso_comp_iso_inv {A : Type*} [Category* A] [Abelian A]
    {P Q R : CochainComplex A ℤ} (f : P ⟶ Q) (hf : QuasiIso f) (e : R ≅ Q) :
    QuasiIso (f ≫ e.inv) := by
  have := hf
  infer_instance

/-! ### The two spellings of strict perfectness on a ringed space -/

/-- **The two spellings of "direct summand of a finite free module" on a ringed space agree.**
`StrictlyPerfect.IsDirectSummandOfFiniteFree` asks for a retract of
`StrictlyPerfect.finiteFree X n`, the `n`-fold biproduct of the structure sheaf, and
`IsDirectSummandOfFiniteFree` for a retract of `SheafOfModules.free (ULift (Fin n))`, the
coproduct of `n` copies of the unit; the two modules are identified by
`StrictlyPerfect.finiteFreeIsoFree`. -/
theorem isDirectSummandOfFiniteFree_iff_ringSheaf (M : StrictlyPerfect.OXMod.{u, u} X) :
    StrictlyPerfect.IsDirectSummandOfFiniteFree M ↔
      _root_.IsDirectSummandOfFiniteFree (StrictlyPerfect.structureSheafOfRings X) M := by
  rw [StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract,
    isDirectSummandOfFiniteFree_iff_free]
  constructor
  · rintro ⟨n, ⟨r⟩⟩
    refine ⟨n, r.i ≫ (StrictlyPerfect.finiteFreeIsoFree X n).hom,
      (StrictlyPerfect.finiteFreeIsoFree X n).inv ≫ r.r, ?_⟩
    rw [Category.assoc, Iso.hom_inv_id_assoc, r.retract]
  · rintro ⟨n, i, r, hir⟩
    exact ⟨n, ⟨⟨i ≫ (StrictlyPerfect.finiteFreeIsoFree X n).inv,
      (StrictlyPerfect.finiteFreeIsoFree X n).hom ≫ r, by
        rw [Category.assoc, Iso.inv_hom_id_assoc, hir]⟩⟩⟩

/-- **The two spellings of strict perfectness on a ringed space agree.** Both ask that only
finitely many terms be nonzero and that every term be a direct summand of a finite free module;
the termwise conditions agree by `isDirectSummandOfFiniteFree_iff_ringSheaf`. -/
theorem isStrictlyPerfect_iff_ringSheaf
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) :
    StrictlyPerfect.IsStrictlyPerfect E ↔
      _root_.IsStrictlyPerfect (StrictlyPerfect.structureSheafOfRings X) E :=
  ⟨fun hE => ⟨hE.bounded, fun i =>
      (isDirectSummandOfFiniteFree_iff_ringSheaf X _).1 (hE.directSummand i)⟩,
    fun hE => ⟨hE.bounded, fun i =>
      (isDirectSummandOfFiniteFree_iff_ringSheaf X _).2 (hE.termDirectSummand i)⟩⟩

/-! ### Transport across the slice-versus-subspace equivalence -/

section Restrict

variable (U : Opens X.carrier)

/-- The functor of `sheafOfModulesEquivRestrict X U` is additive. -/
instance restrictEquivFunctorAdditive :
    (sheafOfModulesEquivRestrict.{u} X U).functor.Additive := ⟨by intros; ext W x; rfl⟩

/-- The inverse functor of `sheafOfModulesEquivRestrict X U` is additive. -/
instance restrictEquivInverseAdditive :
    (sheafOfModulesEquivRestrict.{u} X U).inverse.Additive := ⟨by intros; ext W x; rfl⟩

/-- The functor of `sheafOfModulesEquivRestrict X U` preserves homology. -/
instance restrictEquivFunctorPreservesHomology :
    (sheafOfModulesEquivRestrict.{u} X U).functor.PreservesHomology := inferInstance

/-- The inverse functor of `sheafOfModulesEquivRestrict X U` preserves homology. -/
instance restrictEquivInversePreservesHomology :
    (sheafOfModulesEquivRestrict.{u} X U).inverse.PreservesHomology := inferInstance

/-- The transport equivalence of complexes: restriction to the slice sheaf of rings on `Over U`
against restriction to the open subspace `U`. -/
abbrev restrictComplexEquiv :
    CochainComplex
        (SheafOfModules.{u} ((StrictlyPerfect.structureSheafOfRings X).over U)) ℤ ≌
      CochainComplex (StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ :=
  (sheafOfModulesEquivRestrict.{u} X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The transport equivalence carries the unit of the slice sheaf of rings to the structure
sheaf of the restricted space. The two are the same module, so this is the identity. -/
def restrictEquivUnitIso :
    (sheafOfModulesEquivRestrict.{u} X U).functor.obj
        (SheafOfModules.unit ((StrictlyPerfect.structureSheafOfRings X).over U)) ≅
      SheafOfModules.unit
        (StrictlyPerfect.structureSheafOfRings (X.restrict U.isOpenEmbedding)) :=
  Iso.refl _

/-- The transport equivalence carries the structure sheaf of the restricted space to the unit of
the slice sheaf of rings; the comparison inverse to `restrictEquivUnitIso`. -/
def restrictEquivInverseUnitIso :
    (sheafOfModulesEquivRestrict.{u} X U).inverse.obj
        (SheafOfModules.unit
          (StrictlyPerfect.structureSheafOfRings (X.restrict U.isOpenEmbedding))) ≅
      SheafOfModules.unit ((StrictlyPerfect.structureSheafOfRings X).over U) :=
  (sheafOfModulesEquivRestrict.{u} X U).inverse.mapIso (restrictEquivUnitIso X U).symm ≪≫
    ((sheafOfModulesEquivRestrict.{u} X U).unitIso.app _).symm

/-- **Strict perfectness over the slice sheaf of rings becomes strict perfectness on the
restricted space.** The transport equivalence is exact and carries the unit to the unit. -/
theorem isStrictlyPerfect_restrictComplexEquiv
    {P : CochainComplex
      (SheafOfModules.{u} ((StrictlyPerfect.structureSheafOfRings X).over U)) ℤ}
    (hP : _root_.IsStrictlyPerfect ((StrictlyPerfect.structureSheafOfRings X).over U) P) :
    StrictlyPerfect.IsStrictlyPerfect ((restrictComplexEquiv X U).functor.obj P) :=
  (isStrictlyPerfect_iff_ringSheaf _ _).2
    (SheafOfModules.isStrictlyPerfect_map _ (restrictEquivUnitIso X U) hP)

/-- **Strict perfectness on the restricted space becomes strict perfectness over the slice sheaf
of rings.** The inverse of the transport equivalence is exact and carries the unit to the
unit. -/
theorem isStrictlyPerfect_restrictComplexEquiv_inverse
    {P : CochainComplex (StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : StrictlyPerfect.IsStrictlyPerfect P) :
    _root_.IsStrictlyPerfect ((StrictlyPerfect.structureSheafOfRings X).over U)
      ((restrictComplexEquiv X U).inverse.obj P) :=
  SheafOfModules.isStrictlyPerfect_map _ (restrictEquivInverseUnitIso X U)
    ((isStrictlyPerfect_iff_ringSheaf _ _).1 hP)

end Restrict

/-! ### From the ringed site to the ringed space -/

section Compare

/-- **The site's restriction to the slice over `U` is the space's restriction to `U`.** Under the
transport equivalence the two restriction functors are the same functor, so this holds on the
nose. -/
theorem restrictComplexEquiv_obj_restrictComplex (U : Opens X.carrier)
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) :
    ((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      ((Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E U) =
      restrictComplex E U :=
  rfl

/-- A quasi-isomorphism of complexes over the slice sheaf of rings stays one after transport to
the restricted space: the transport equivalence preserves homology. -/
theorem quasiIso_restrictComplexEquiv_map (U : Opens X.carrier)
    {A B : CochainComplex
      (SheafOfModules.{u} ((StrictlyPerfect.structureSheafOfRings X).over U)) ℤ}
    (q : A ⟶ B) (hq : QuasiIso q) :
    QuasiIso (((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  have := hq
  infer_instance

/-- **A site-level strictly perfect model over an open becomes a space-level one.** The site's
restriction of `E` to the slice over `U` is, under the transport equivalence, the space's
restriction of `E` to `U`; so the transported model is a model in the sense of
[Stacks, Tag 08CM]. -/
theorem exists_strictlyPerfect_restrictComplex (U : Opens X.carrier)
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (P : CochainComplex
      (SheafOfModules.{u} ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over U)) ℤ)
    (hP : _root_.IsStrictlyPerfect
      ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over U) P)
    (q : P ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E U) (hq : QuasiIso q) :
    ∃ P' : CochainComplex (StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
      StrictlyPerfect.IsStrictlyPerfect P' ∧
        ∃ f : P' ⟶ restrictComplex E U, QuasiIso f :=
  ⟨_, isStrictlyPerfect_restrictComplexEquiv X U hP, _,
    quasiIso_restrictComplexEquiv_map X U q hq⟩

/-! ### From the ringed space to the ringed site -/

/-- The unit of the transport equivalence at the level of complexes: a complex of modules over
the slice sheaf of rings is recovered from its transport to the restricted space. -/
def restrictComplexUnitIso (U : Opens X.carrier)
    (A : CochainComplex
      (SheafOfModules.{u} ((StrictlyPerfect.structureSheafOfRings X).over U)) ℤ) :
    A ≅ ((sheafOfModulesEquivRestrict.{u} X U).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A) :=
  (NatIso.mapHomologicalComplex (sheafOfModulesEquivRestrict.{u} X U).unitIso
    (ComplexShape.up ℤ)).app A

/-- A quasi-isomorphism of complexes on the restricted space stays one after transport back to
the slice sheaf of rings. -/
theorem quasiIso_restrictComplexEquiv_inverse_map (U : Opens X.carrier)
    {A B : CochainComplex (StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (q : A ⟶ B) (hq : QuasiIso q) :
    QuasiIso (((sheafOfModulesEquivRestrict.{u} X U).inverse.mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  have := hq
  infer_instance

/-- **A space-level strictly perfect model over an open becomes a site-level one.** The inverse
of the transport equivalence carries the space's restriction of `E` to `U` back to the site's
restriction of `E` to the slice over `U`. -/
theorem exists_strictlyPerfect_restrictComplex_ringedSite (U : Opens X.carrier)
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect P)
    (q : P ⟶ restrictComplex E U) (hq : QuasiIso q) :
    ∃ P' : CochainComplex
        (SheafOfModules.{u} ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over U)) ℤ,
      _root_.IsStrictlyPerfect
          ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over U) P' ∧
        ∃ f : P' ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E U, QuasiIso f :=
  ⟨_, isStrictlyPerfect_restrictComplexEquiv_inverse X U hP, _,
    quasiIso_comp_iso_inv _ (quasiIso_restrictComplexEquiv_inverse_map X U q hq)
      (restrictComplexUnitIso X U
        ((Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E U))⟩

/-- A quasi-isomorphism of complexes over the slice sheaf of rings on `Over V` stays one after
restriction along an arrow `g : W ⟶ V` of the site: restriction along an arrow is exact. -/
theorem quasiIso_overMap_map {V W : Opens X.carrier} (g : W ⟶ V)
    {A B : CochainComplex
      (SheafOfModules.{u} ((StrictlyPerfect.structureSheafOfRings X).over V)) ℤ}
    (q : A ⟶ B) (hq : QuasiIso q) :
    QuasiIso (((SheafOfModules.overMap.{u} (StrictlyPerfect.structureSheafOfRings X) g
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  have := hq
  let : PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (StrictlyPerfect.structureSheafOfRings X) g) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g
  let : PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (StrictlyPerfect.structureSheafOfRings X) g) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g
  infer_instance

/-- **A site-level strictly perfect model over an object of the site restricts along any arrow
into that object.** Restriction along an arrow of the site is exact and carries the unit to the
unit, so it carries a model to a model. -/
theorem exists_strictlyPerfect_restrictComplex_of_hom {V W : Opens X.carrier} (g : W ⟶ V)
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (P : CochainComplex
      (SheafOfModules.{u} ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over V)) ℤ)
    (hP : _root_.IsStrictlyPerfect
      ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over V) P)
    (q : P ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E V) (hq : QuasiIso q) :
    ∃ P' : CochainComplex
        (SheafOfModules.{u} ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over W)) ℤ,
      _root_.IsStrictlyPerfect
          ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over W) P' ∧
        ∃ f : P' ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E W, QuasiIso f := by
  let : PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (StrictlyPerfect.structureSheafOfRings X) g) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g
  exact ⟨_, SheafOfModules.isStrictlyPerfect_map _ (SheafOfModules.overMapUnitIso g) hP, _,
    quasiIso_comp_iso_hom _ (quasiIso_overMap_map X g q hq)
      ((Functor.mapHomologicalComplexCompIso
        (SheafOfModules.overFunctorMap.{u} (StrictlyPerfect.structureSheafOfRings X) g)
        (ComplexShape.up ℤ)).app E)⟩

/-- The arrows of the site of opens over whose source a complex of `O_X`-modules becomes
quasi-isomorphic to a strictly perfect complex. It is a sieve by
`exists_strictlyPerfect_restrictComplex_of_hom`. -/
def quasiStrictlyPerfectSieve
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) (V : Opens X.carrier) :
    Sieve V where
  arrows W _ := ∃ P : CochainComplex
      (SheafOfModules.{u} ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over W)) ℤ,
    _root_.IsStrictlyPerfect
        ((ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).over W) P ∧
      ∃ q : P ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E W, QuasiIso q
  downward_closed := by
    rintro W W' f ⟨P, hP, q, hq⟩ g
    exact exists_strictlyPerfect_restrictComplex_of_hom X g E P hP q hq

/-- **The ringed-space reading of perfectness implies the ringed-site one.** The single open
cover supplied by [Stacks, Tag 08CM] makes `quasiStrictlyPerfectSieve` covering at the final
open `⊤`, and that sieve is its own pullback along any arrow, so it is covering at every open. -/
theorem isPerfectComplex_ringedSite_of_isPerfectComplex
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) (hE : IsPerfectComplex E) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfectComplex E := by
  obtain ⟨I, U, hU, hmodels⟩ := hE
  have htop : quasiStrictlyPerfectSieve X E ⊤ ∈ (Opens.grothendieckTopology X.carrier) ⊤ := by
    refine (Opens.mem_grothendieckTopology (T := (X.carrier : Type u))).2 fun x _ => ?_
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 (hU ▸ (by trivial : x ∈ (⊤ : Opens X.carrier)))
    obtain ⟨P, hP, q, hq⟩ := hmodels i
    exact ⟨U i, homOfLE le_top,
      exists_strictlyPerfect_restrictComplex_ringedSite X (U i) E P hP q hq, hxi⟩
  intro V
  refine ⟨(quasiStrictlyPerfectSieve X E V).arrows, ?_, fun W f hf => hf⟩
  rw [Sieve.generate_sieve]
  exact (Opens.grothendieckTopology X.carrier).pullback_stable
    (homOfLE le_top : V ⟶ (⊤ : Opens X.carrier)) htop

/-- **The two readings of perfectness of a complex on a ringed space agree**:
[Stacks, Tag 08CM] on the space and [Stacks, Tag 08G5] on its ringed site of opens. -/
theorem isPerfectComplex_iff_ringedSite
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) :
    IsPerfectComplex E ↔ (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfectComplex E :=
  ⟨isPerfectComplex_ringedSite_of_isPerfectComplex X E, isPerfectComplex_of_ringedSite X E⟩

section Derived

variable [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]

/-- The derived category of `O_X`-modules read at the ringed site's spelling of the structure
sheaf of rings. The two spellings are the same category, but an instance at one does not fire at
the other. -/
local instance hasDerivedCategoryRingedSite : HasDerivedCategory.{d}
    (SheafOfModules.{u} (ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X))

/-- **The two readings of perfectness of an object of `D(O_X)` agree**: [Stacks, Tag 08CM] on
the ringed space and [Stacks, Tag 08G5] on its ringed site of opens. Both ask for a
representative satisfying the respective complex-level condition, and those agree by
`isPerfectComplex_iff_ringedSite`. -/
theorem isPerfect_iff_ringedSite (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) :
    IsPerfect K ↔ (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect K :=
  ⟨fun ⟨E, hE, he⟩ => ⟨E, (isPerfectComplex_iff_ringedSite X E).1 hE, he⟩,
    isPerfect_of_ringedSite X K⟩

end Derived

end Compare

end Stacks.Cohomology.PerfectComplexes

end
