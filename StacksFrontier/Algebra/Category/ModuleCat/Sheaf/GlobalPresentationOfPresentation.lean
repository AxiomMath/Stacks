module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure

/-!
# A global presentation from a presentation

`SheafOfModules.HasGlobalPresentation`, the global condition of Stacks 03DE(6) underlying
quasi-coherence on an arbitrary site, asks for a presentation of a sheaf of modules *after*
raising the universe of its sections to one containing the site, by
`SheafOfModules.uliftForPresentation`.  Mathlib's `SheafOfModules.Presentation` is a
presentation of the sheaf itself.  This file produces the first from the second.

The content is that the universe lift carries the two colimits a presentation consists of — a
coproduct of copies of the structure sheaf, and a cokernel — to colimits of the same shape.
That is not formal: a colimit of sheaves of modules is the sheafification of the colimit of the
underlying presheaves, and the lift is only defined objectwise, so it has to be shown to commute
with sheafification.  The module doc of
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels` lists the cokernel half as one
of the three things that are "not formal consequences of the two presentations", and
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` takes it as a
hypothesis; `SheafOfModules.uliftForPresentationFunctor_preservesColimits` discharges it.

## Main definitions

* `SheafOfModules.uliftForPresentationFunctor` bundles `SheafOfModules.uliftForPresentation`
  and `SheafOfModules.uliftForPresentationMap` into a functor.

## Main results

* `SheafOfModules.uliftForPresentationFunctor_preservesColimits`: raising the universe of the
  sections of a sheaf of modules preserves colimits.
* `SheafOfModules.HasGlobalPresentation.of_presentation'`: a sheaf of modules with a presentation
  has a global presentation, in an arbitrary module universe.
* `SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent`: a quasi-coherent sheaf of modules
  in the sense of Mathlib is quasi-coherent on the site.

## Implementation notes

Colimit preservation is proved as in
`AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits`: the forgetful functor to abelian
sheaves reflects isomorphisms, hence reflects the colimits it preserves, and after composing
with it the universe lift of sheaves of modules *is* the universe lift of abelian sheaves, by
`Iso.refl`, which preserves colimits by
`Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits`.  The two
`CategoryTheory.Limits.preservesColimitsOfSize_of_univLE` steps shrink the diagram size from the
one at which the forgetful functors are known to preserve colimits — the module universe, with
the site universes adjoined for the morphisms — down to the module universe of the source, which
is where the diagrams of a presentation live; the universe arguments are written out because the
`max` equations they solve have no most general solution.

The index types of a global presentation lie in the presentation universe, so the index type of
a presentation is lifted with `ULift`; that is a reindexing of a coproduct along an equivalence
of index types and carries no further content.

Nothing here carries a Stacks attribute: these are the inputs for the quasi-coherence clauses of
Stacks 03DL and 03L6, not statements of them.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Raising the universe of the sections of a sheaf of modules preserves colimits.** -/
theorem uliftForPresentationFunctor_preservesColimits
    [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{max t m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}] :
    PreservesColimitsOfSize.{m, m} (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)) := by
  let F := uliftForPresentationFunctor.{u, v, r, m, t} (R := R)
  let G := SheafOfModules.toSheaf.{max t m} R
  have h1 : PreservesColimitsOfSize.{m, m} (SheafOfModules.toSheaf.{m} R) :=
    preservesColimitsOfSize_shrink _
  have h2 : PreservesColimitsOfSize.{m, m} G :=
    preservesColimitsOfSize_of_univLE.{max m u t, max m t, m, m, _, _, _, _} _
  have h3 : PreservesColimitsOfSize.{m, m}
      (sheafCompose J AddCommGrpCat.uliftFunctor.{t, m}) :=
    Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits
  have e : F ⋙ G ≅
      SheafOfModules.toSheaf.{m} R ⋙ sheafCompose J AddCommGrpCat.uliftFunctor.{t, m} :=
    Iso.refl _
  have := h1
  have := h2
  have := h3
  let : PreservesColimitsOfSize.{m, m} (F ⋙ G) := preservesColimits_of_natIso e.symm
  let : ReflectsColimitsOfSize.{m, m} G := reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves F G

/-- A coproduct of copies of one object, reindexed along the universe lift of its index type. -/
private noncomputable def isColimitCofanULift.{d', d, b, bb} {D : Type d} [Category.{d'} D]
    {B : Type b} {O P : D} (ι : B → (O ⟶ P)) (h : IsColimit (Cofan.mk P ι)) :
    IsColimit (Cofan.mk (f := fun _ : ULift.{bb} B ↦ O) P fun i ↦ ι i.down) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ Cofan.IsColimit.desc h fun b ↦ s.inj (ULift.up b)) ?_ ?_
  · intro s i
    exact Cofan.IsColimit.fac h (fun b ↦ s.inj (ULift.up b)) i.down
  · intro s n hn
    refine Cofan.IsColimit.hom_ext h _ _ fun b ↦ ?_
    rw [Cofan.IsColimit.fac h (fun b ↦ s.inj (ULift.up b)) b]
    exact hn (ULift.up b)

section Bridge

variable {S : Sheaf J RingCat.{m}} [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **A global presentation from a presentation, in an arbitrary module universe.**  A sheaf of
modules presented as the cokernel of a map between coproducts of copies of the structure sheaf
has a global presentation in the sense of Stacks 03DE(6): the universe lift carries both
colimits to colimits of the same shape, and the index types are lifted along `ULift`.

`SheafOfModules.HasGlobalPresentation.of_presentation` is the same statement under the standing
assumption that the module universe already contains the site universes, where the universe lift
is an isomorphism and no colimit preservation is needed.  Here the module universe `m` is
arbitrary and only `CategoryTheory.HasWeakSheafify` is asked of it, so neither statement is an
instance of the other and both are kept. -/
theorem HasGlobalPresentation.of_presentation' {M : SheafOfModules.{m} S} (p : M.Presentation) :
    M.HasGlobalPresentation := by
  let : HasSheafify J AddCommGrpCat.{m} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify J AddCommGrpCat.{max u v m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v m, v, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v m, u, v} J
  let U := uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := S)
  have hU : PreservesColimitsOfSize.{m, m} U :=
    uliftForPresentationFunctor_preservesColimits.{u, v, m, m, max u v m} (R := S)
  have := hU
  have : PreservesColimitsOfSize.{0, 0} U := preservesColimitsOfSize_shrink U
  have : U.PreservesZeroMorphisms :=
    preservesZeroMorphisms_uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := S)
  have hcok := isColimitCoforkMapOfIsColimit' U _ p.isColimit
  have hfree := fun I : Type m ↦ isColimitCofanULift.{_, _, _, max u v}
    (fun i ↦ U.map ((freeCofan I).inj i))
    ((Cofan.isColimitMapCoconeEquiv U _ (freeCofan I))
      (isColimitOfPreserves U (isColimitFreeCofan I)))
  exact ⟨ULift.{max u v} p.generators.I, ULift.{max u v} p.relations.I,
    U.obj (freeCofan p.generators.I).pt, U.obj (freeCofan p.relations.I).pt,
    (fun i ↦ U.map ((freeCofan p.generators.I).inj i.down)),
    (fun i ↦ U.map ((freeCofan p.relations.I).inj i.down)),
    ⟨hfree p.generators.I⟩, ⟨hfree p.relations.I⟩, U.map _, U.map p.generators.π, _, ⟨hcok⟩⟩

omit [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- **Quasi-coherence in the sense of Mathlib implies quasi-coherence on the site.**  A
quasi-coherent sheaf of modules has a presentation on each member of a family covering the final
object, hence a global presentation there, which is the criterion of Stacks 03DN. -/
theorem IsQuasicoherentOnSite.of_isQuasicoherent
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{m}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{m}]
    (M : SheafOfModules.{m} S) [hM : M.IsQuasicoherent] : M.IsQuasicoherentOnSite := by
  obtain ⟨q⟩ := hM.nonempty_quasicoherentData
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
    M).2 ⟨q.I, q.X, q.coversTop, fun i ↦ ?_⟩
  exact HasGlobalPresentation.of_presentation' (q.presentation i)

end Bridge

end SheafOfModules

end
