module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# Mathlib-sense quasi-coherence and quasi-coherence in the sense of Stacks 03DL(6)

`SheafOfModules.HasGlobalPresentation.of_presentation_of_preservesColimits` turns Mathlib's
`SheafOfModules.Presentation` of a sheaf of modules into the global presentation of
Stacks 03DL(6), which is stated in the fixed universe `max u v r` through
`SheafOfModules.uliftForPresentation`.  It does so under a hypothesis: that the universe lift
preserves colimits of the shapes in which the presentation is a colimit, namely those indexed by
a category whose objects *and* morphisms lie in the universe `r` of the sections.

This file discharges that hypothesis, on every site and with no size assumption.  The supply of
colimit preservation for `SheafOfModules.toSheaf` is
`AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits`, which gives the shapes whose
objects lie in `Type r` but whose morphisms lie in `max u r`; a functor preserving colimits of
larger shapes preserves colimits of smaller ones, which is
`CategoryTheory.Limits.preservesColimitsOfSize_of_univLE`, and `r ≤ max u r` needs nothing.
(`CategoryTheory.Limits.preservesColimitsOfSize_shrink` would also do, but it states the two
supplied levels as `max w w₂` and `max w' w₂'`, so it only elaborates when those four universes
are written out; left to unification it is stuck on `max r ?w₂ =?= max u r`.)  The
sheafification data at the raised universe `max u v r` is then automatic as well, by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`, since a site always
lies below `max u v r`.

Consequently a `SheafOfModules.Presentation` yields a `SheafOfModules.HasGlobalPresentation`
outright, and Mathlib's `SheafOfModules.IsQuasicoherent` — local presentations on a family
covering the final object — implies `SheafOfModules.IsQuasicoherentOnSite`, the predicate of
Stacks 03DL(6).

## Main results

* `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'`: the universe lift of
  sheaves of modules preserves colimits of every shape whose objects and morphisms lie in the
  universe of the sections.  It is
  `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor` at the lift amount
  `max u v r`, with that lemma's sheafification hypotheses at the raised universe discharged.
* `SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor` and
  `SheafOfModules.uliftForPresentationKernelIso`: the universe lift is also left exact, so the
  lift of a kernel is the kernel of the lift.
* `SheafOfModules.Presentation.hasGlobalPresentation`: a presentation gives a global
  presentation, with no hypothesis beyond sheafification at the universe of the sections.
* `SheafOfModules.QuasicoherentData.isQuasicoherentOnSite` and
  `SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent`: Mathlib's quasi-coherence implies
  the quasi-coherence of Stacks 03DL(6).
* `SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`: the converse at
  the level of a single module — a global presentation yields a `SheafOfModules.Presentation` — on
  a site whose sheaves of modules have global sections small relative to the universe of the
  sections.  Unlike `SheafOfModules.HasGlobalPresentation.nonempty_presentation`, which asks the
  sections to lie in the presentation universe `max u v r` itself, the universe of the sections
  here is arbitrary.
* `SheafOfModules.small_sections_of_univLE`: that smallness holds in particular when the site
  itself is small relative to the universe of the sections.
* `SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent` and
  `SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`: on a site small relative to the
  universe of the sections the two predicates agree.
* `not_univLE_succ`: that smallness of the site fails on a big site, so those last two results
  do not apply there; the hypothesis of
  `SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections` does.

## Implementation notes

Nothing here carries a `stacks` attribute.  The comparison of Mathlib's `IsQuasicoherent` with
`IsQuasicoherentOnSite` is a statement about two definitions of one notion, not a result of the
source; Stacks 03DN, which *is* the locality statement, is
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation` and is used
below.

The converse direction needs a size hypothesis and *only* a size hypothesis, but not one on the
site.  A global presentation indexes its coproducts by types in `Type (max u v r)`, while
`SheafOfModules.free` is indexed by `Type r`, and on the big fppf site of a scheme over
`S : Scheme.{u}` — objects in `Type (u + 1)`, sections in `Type u` — the index types cannot be
shrunk at all, since `UnivLE.{u + 1, u}` is false.  What can be shrunk is the *image* of an
index type in the global sections, and that suffices: the universe lift
`SheafOfModules.uliftForPresentation` is not merely colimit-preserving but full and faithful, so
the components of a global presentation are lifts of global sections, and replacing an index
type by the set of sections it names makes the comparison map onto a free module a *split*
epimorphism, along which the cokernel diagram transports.  The tools are
`SheafOfModules.uliftForPresentationMapDown` together with
`SheafOfModules.full_uliftForPresentationFunctor` and
`SheafOfModules.faithful_uliftForPresentationFunctor`.  So the hypothesis is smallness of the
global sections, which a site with a final object has
(`SheafOfModules.small_sections_of_isTerminal`), rather than smallness of the site.

Exactness of the universe lift is *not* what makes that work, although it is true and is proved
here.  The relations of the presentation are generating sections of the kernel of a map between
free modules formed at the universe of the sections, so no kernel at the raised universe is ever
compared with a kernel below it, and
`SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor` goes unused by
`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe r v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **The universe lift of sheaves of modules preserves colimits of small shapes.**  Colimits of
sheaves of modules are detected by the underlying abelian sheaves, where the lift is composition
with the universe lift of abelian groups;
`AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits` supplies the shapes whose morphisms
lie in `max u r`, and preservation descends from a larger shape universe to a smaller one.

The primed name distinguishes this from
`SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor`, which raises the universe
of the sections by an arbitrary amount and therefore has to assume the sheafification data at
the raised universe.  Here the amount is the fixed `max u v r` in which
`SheafOfModules.HasGlobalPresentation` is stated, where that data is automatic, so the only
hypotheses are the ones at the universe of the sections. -/
public theorem preservesColimitsOfSize_uliftForPresentationFunctor' (R : Sheaf J RingCat.{r})
    [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] :
    PreservesColimitsOfSize.{r, r}
      (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) := by
  have : HasSheafify J AddCommGrpCat.{max u v r} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r} _
  have : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r} _
  refine ⟨fun {K} _ => ?_⟩
  have : PreservesColimitsOfShape K (toSheaf.{r} R) :=
    (preservesColimitsOfSize_of_univLE.{max u r, r, r, r} _).preservesColimitsOfShape
  have : PreservesColimitsOfShape K (toSheaf.{max u v r} R) :=
    (preservesColimitsOfSize_of_univLE.{max u v r, max u v r, r, r} _).preservesColimitsOfShape
  exact preservesColimitsOfShape_uliftForPresentationFunctor.{r, r, max u v r, r, r, v, u} R K

/-- **A presentation gives a global presentation, unconditionally.**  This is
`SheafOfModules.HasGlobalPresentation.of_presentation_of_preservesColimits` with its
colimit-preservation hypothesis discharged by
`SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'`. -/
public theorem Presentation.hasGlobalPresentation {R : Sheaf J RingCat.{r}}
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {M : SheafOfModules.{r} R} (P : M.Presentation) : M.HasGlobalPresentation :=
  HasGlobalPresentation.of_presentation_of_preservesColimits
    (preservesColimitsOfSize_uliftForPresentationFunctor' R) P

section Quasicoherent

variable {R : Sheaf J RingCat.{r}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{r}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Presentations of a sheaf of modules on a family covering the final object make it
quasi-coherent in the sense of Stacks 03DL(6): each presentation becomes a global presentation
on its slice, and quasi-coherence is local on a covering family by Stacks 03DN. -/
public theorem QuasicoherentData.isQuasicoherentOnSite {M : SheafOfModules.{r} R}
    (q : M.QuasicoherentData.{u}) : M.IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation M).2
    ⟨q.I, q.X, q.coversTop, fun i => (q.presentation i).hasGlobalPresentation⟩

/-- **Mathlib's quasi-coherence implies the quasi-coherence of Stacks 03DL(6).** -/
public theorem isQuasicoherentOnSite_of_isQuasicoherent (M : SheafOfModules.{r} R)
    [M.IsQuasicoherent] : M.IsQuasicoherentOnSite :=
  QuasicoherentData.isQuasicoherentOnSite
    (IsQuasicoherent.nonempty_quasicoherentData (M := M)).some

end Quasicoherent

universe t m

section Exactness

/-- **`CategoryTheory.sheafCompose` along the universe lift of abelian groups preserves finite
limits.**  Limits of sheaves are computed in presheaves, where composing with the lift is
postcomposition, and `AddCommGrpCat.uliftFunctor` preserves finite limits.  This is the limit
counterpart of `CategoryTheory.preservesColimitsOfShape_sheafCompose`, which is harder: a
colimit of sheaves is *not* computed in presheaves. -/
public theorem preservesLimitsOfShape_sheafCompose_uliftFunctor
    [HasWeakSheafify J AddCommGrpCat.{max t m}]
    (K : Type) [SmallCategory K] [FinCategory K] :
    PreservesLimitsOfShape K (sheafCompose J AddCommGrpCat.uliftFunctor.{t, m}) := by
  have e : sheafCompose J AddCommGrpCat.uliftFunctor.{t, m} ⋙
      sheafToPresheaf J AddCommGrpCat.{max t m} ≅
      sheafToPresheaf J AddCommGrpCat.{m} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{m} AddCommGrpCat.{max t m}).obj
          AddCommGrpCat.uliftFunctor.{t, m} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)
  have h : PreservesLimitsOfShape K
      (sheafCompose J AddCommGrpCat.uliftFunctor.{t, m} ⋙
        sheafToPresheaf J AddCommGrpCat.{max t m}) :=
    preservesLimitsOfShape_of_natIso e.symm
  have : ReflectsLimitsOfShape K (sheafToPresheaf J AddCommGrpCat.{max t m}) := inferInstance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J AddCommGrpCat.{max t m})

/-- **The universe lift of sheaves of modules is left exact.**  Finite limits of sheaves of
modules are detected and created by the underlying abelian sheaves, where the lift is
composition with the universe lift of abelian groups, and that composition preserves finite
limits by `SheafOfModules.preservesLimitsOfShape_sheafCompose_uliftFunctor`.

Together with `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'` this makes
the lift exact. -/
public theorem preservesFiniteLimits_uliftForPresentationFunctor (R : Sheaf J RingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] :
    PreservesFiniteLimits (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) := by
  have : HasSheafify J AddCommGrpCat.{max u v r} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r} _
  have : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r} _
  constructor
  intro K _ _
  have hc : PreservesLimitsOfShape K
      (sheafCompose J AddCommGrpCat.uliftFunctor.{max u v r, r}) :=
    preservesLimitsOfShape_sheafCompose_uliftFunctor K
  have h2 : PreservesLimitsOfShape K
      ((uliftForPresentationFunctor (R := R) :
          SheafOfModules.{r} R ⥤ SheafOfModules.{max u v r} R) ⋙ toSheaf.{max u v r} R) :=
    preservesLimitsOfShape_of_natIso
      (uliftForPresentationFunctorCompToSheafIso R :
        (uliftForPresentationFunctor (R := R) :
            SheafOfModules.{r} R ⥤ SheafOfModules.{max u v r} R) ⋙
          toSheaf.{max u v r} R ≅ _).symm
  have : ReflectsLimitsOfShape K (toSheaf.{max u v r} R) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (toSheaf.{max u v r} R)

/-- **The universe lift of a kernel is the kernel of the universe lift**, a kernel being a
finite limit and the lift preserving those by
`SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor`. -/
public noncomputable def uliftForPresentationKernelIso {R : Sheaf J RingCat.{r}}
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {M N : SheafOfModules.{r} R} (f : M ⟶ N) :
    uliftForPresentation.{u, v, r, r, max u v r} (kernel f) ≅
      kernel (uliftForPresentationMap.{u, v, r, r, max u v r} f) :=
  have := preservesFiniteLimits_uliftForPresentationFunctor.{r, v, u} R
  PreservesKernel.iso (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) f

end Exactness

section Descend

variable {R : Sheaf J RingCat.{r}}

/-- **The universe lift of a sheaf of modules is full**: a morphism between the lifts is
`ULift.up` of a morphism between the modules, namely the one obtained by reading it on sections
inside the lift. -/
public noncomputable def uliftForPresentationMapDown {M N : SheafOfModules.{m} R}
    (g : uliftForPresentation.{u, v, r, m, t} M ⟶ uliftForPresentation.{u, v, r, m, t} N) :
    M ⟶ N where
  val :=
    { app := fun X ↦ ModuleCat.ofHom
        { toFun := fun x ↦ (g.val.app X (ULift.up x)).down
          map_add' := fun x y ↦ congrArg ULift.down
            (map_add (g.val.app X).hom (ULift.up x) (ULift.up y))
          map_smul' := fun a x ↦ congrArg ULift.down
            (map_smul (g.val.app X).hom a (ULift.up x)) }
      naturality := fun {X Y} f ↦ by
        ext x
        exact congrArg ULift.down
          (PresheafOfModules.naturality_apply g.val f (ULift.up x)) }

/-- `SheafOfModules.uliftForPresentationMapDown` is a section of the universe lift on
morphisms. -/
public theorem uliftForPresentationMap_down {M N : SheafOfModules.{m} R}
    (g : uliftForPresentation.{u, v, r, m, t} M ⟶ uliftForPresentation.{u, v, r, m, t} N) :
    uliftForPresentationMap.{u, v, r, m, t} (uliftForPresentationMapDown g) = g := by
  ext X x
  exact ULift.ext _ _ rfl

/-- The universe lift is injective on morphisms. -/
public theorem uliftForPresentationMap_injective {M N : SheafOfModules.{m} R} {f g : M ⟶ N}
    (h : uliftForPresentationMap.{u, v, r, m, t} f =
      uliftForPresentationMap.{u, v, r, m, t} g) : f = g := by
  ext X x
  exact congrArg ULift.down
    (congrArg (fun k : uliftForPresentation.{u, v, r, m, t} M ⟶ _ ↦ k.val.app X (ULift.up x)) h)

/-- The universe lift sends the zero morphism to the zero morphism. -/
public theorem uliftForPresentationMap_zero (M N : SheafOfModules.{m} R) :
    uliftForPresentationMap.{u, v, r, m, t} (0 : M ⟶ N) = 0 := by
  ext X x
  exact ULift.ext _ _ rfl

/-- The universe lift of sheaves of modules is full. -/
public instance full_uliftForPresentationFunctor (R : Sheaf J RingCat.{r}) :
    (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)).Full where
  map_surjective g := ⟨uliftForPresentationMapDown g, uliftForPresentationMap_down g⟩

/-- The universe lift of sheaves of modules is faithful. -/
public instance faithful_uliftForPresentationFunctor (R : Sheaf J RingCat.{r}) :
    (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)).Faithful where
  map_injective h := uliftForPresentationMap_injective h

/-- **`UnivLE.{max u v r, r}` makes the global sections of every sheaf of modules small.**  The
sections of `N : SheafOfModules.{r} R` form a type in `Type (max u r)`, which is `Type r`-small
as soon as every type in `Type (max u v r)` is. -/
public theorem small_sections_of_univLE [UnivLE.{max u v r, r}] (N : SheafOfModules.{r} R) :
    Small.{r} N.sections :=
  Small.trans_univLE.{max u v r, r} _

variable [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Any family of global sections of `M` is hit by a map out of a free module on a type in
`Type r`, the generators being indexed by (a type in `Type r` receiving) the family surjectively. -/
private theorem exists_free_hom_of_sections (M : SheafOfModules.{r} R) [Small.{r} M.sections]
    {ι : Type*} (g : ι → (unit R ⟶ M)) :
    ∃ (A : Type r) (idx : ι → A) (π : free (R := R) A ⟶ M),
      Function.Surjective idx ∧ ∀ i, ιFree (idx i) ≫ π = g i := by
  set idx : ι → Shrink.{r} M.sections := fun i ↦ equivShrink _ (M.unitHomEquiv (g i)) with hidx
  refine ⟨Set.range idx, fun i ↦ ⟨idx i, i, rfl⟩,
    M.freeHomEquiv.symm fun s ↦ (equivShrink M.sections).symm s.1, ?_, fun i ↦ ?_⟩
  · rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩
  · rw [← unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
    simp [hidx]

/-- **A global presentation gives a `SheafOfModules.Presentation`**, the converse of
`SheafOfModules.Presentation.hasGlobalPresentation`, on a site whose sheaves of modules have
`Type r`-small global sections.  That holds on every site with a final object, by
`SheafOfModules.small_sections_of_isTerminal`, hence on a big site, where the stronger
hypothesis `UnivLE.{max u v r, r}` — enough for this by
`SheafOfModules.small_sections_of_univLE` — is false by `not_univLE_succ`.

The index types `I` and `K` of a global presentation lie in `Type (max u v r)` and are not
themselves shrinkable; what is shrinkable is their *image* in the global sections.  Write `L` for
the universe lift, `b : P ⟶ L M` for the epimorphism out of the first coproduct and `ι` for its
cofan.  Each `ι i ≫ b` is `L` of a global section of `M`, the lift being full, and the global
sections are `Type r`-small, so those sections are enumerated by a set `A` of them indexed by a
type in `Type r`.  Restricting to that image — rather than to all sections — is what makes the
comparison map `d : P ⟶ L (free A)` a *split* epimorphism: a splitting picks for each member of
`A` one index of `I` that produced it.

Splitness moves the cokernel across the factorisation `b = d ≫ L π`: given `k` with
`L α ≫ k = 0`, the composite `d ≫ k` kills `a`, so it factors as `b ≫ m`, and the splitting
`j` turns that into `k = L π ≫ m`.  The relations are shrunk the same way: each `κ k ≫ a ≫ d`
is `L` of a global section of `free A` annihilated by `π`, hence of `kernel π`, whose sections
are small as well, so `a ≫ d` factors through `L α` for a map `α : free T ⟶ free A` with
`T : Type r`.  Fullness and faithfulness carry the resulting cokernel diagram back down, and
`SheafOfModules.presentationOfIsCokernelFree` reads off the presentation. -/
public theorem HasGlobalPresentation.nonempty_presentation_of_small_sections
    [∀ N : SheafOfModules.{r} R, Small.{r} N.sections]
    {M : SheafOfModules.{r} R} (h : M.HasGlobalPresentation) : Nonempty M.Presentation := by
  classical
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  have hU : PreservesColimitsOfSize.{r, r}
      (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) :=
    preservesColimitsOfSize_uliftForPresentationFunctor' R
  -- The generators: the *image* in the sections of the big index type of the presentation.
  obtain ⟨A, idx, π, hidx, hfac⟩ :=
    exists_free_hom_of_sections M fun i ↦ uliftForPresentationMapDown (ι i ≫ b)
  -- The comparison map out of the big coproduct, and the splitting its index set affords.
  set d : P ⟶ uliftForPresentation.{u, v, r, r, max u v r} (free (R := R) A) :=
    Cofan.IsColimit.desc hP
      (fun i ↦ uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (idx i))) with hd
  have hdfac : ∀ i, ι i ≫ d =
      uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (R := R) (idx i)) :=
    fun i ↦ Cofan.IsColimit.fac hP _ i
  have hdb : d ≫ uliftForPresentationMap.{u, v, r, r, max u v r} π = b := by
    refine Cofan.IsColimit.hom_ext hP _ _ fun i ↦ ?_
    rw [Limits.cofan_mk_inj, ← Category.assoc, hdfac i, ← uliftForPresentationMap_comp, hfac i]
    exact uliftForPresentationMap_down _
  have hfreeA : IsColimit (Cofan.mk
      (uliftForPresentation.{u, v, r, r, max u v r} (free (R := R) A))
      fun s : A ↦ uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree s)) :=
    (Cofan.isColimitMapCoconeEquiv
        (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) _
        (Cofan.mk (free (R := R) A) ιFree)).toFun
      (isColimitOfPreserves _ (isColimitFreeCofan A))
  set j : uliftForPresentation.{u, v, r, r, max u v r} (free (R := R) A) ⟶ P :=
    Cofan.IsColimit.desc hfreeA (fun s ↦ ι (Function.surjInv hidx s)) with hj
  have hjfac : ∀ s : A, uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree s) ≫ j =
      ι (Function.surjInv hidx s) :=
    fun s ↦ Cofan.IsColimit.fac hfreeA _ s
  have hjd : j ≫ d = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hfreeA _ _ fun s ↦ ?_
    rw [Limits.cofan_mk_inj, ← Category.assoc, hjfac s, hdfac, Function.surjInv_eq hidx]
    exact (Category.comp_id _).symm
  -- Both the lift of `π` and `π` itself are epimorphisms, because `b` is.
  have hbepi : Epi b := Cofork.IsColimit.epi hb
  have hLπepi : Epi (uliftForPresentationMap.{u, v, r, r, max u v r} π) := by
    have : Epi (d ≫ uliftForPresentationMap.{u, v, r, r, max u v r} π) := by
      rw [hdb]; exact hbepi
    exact epi_of_epi d _
  have hπepi : Epi π := ⟨fun {_} p q hpq ↦ uliftForPresentationMap_injective
    ((cancel_epi (uliftForPresentationMap.{u, v, r, r, max u v r} π)).mp (by
      rw [← uliftForPresentationMap_comp, ← uliftForPresentationMap_comp, hpq]))⟩
  -- The relations: the global sections of `kernel π` named by the second coproduct.
  set sk : K → (unit R ⟶ free (R := R) A) :=
    fun k ↦ uliftForPresentationMapDown (κ k ≫ a ≫ d) with hsk
  have hskL : ∀ k, uliftForPresentationMap.{u, v, r, r, max u v r} (sk k) = κ k ≫ a ≫ d :=
    fun k ↦ uliftForPresentationMap_down _
  have hskπ : ∀ k, sk k ≫ π = 0 := by
    intro k
    refine uliftForPresentationMap_injective ?_
    rw [uliftForPresentationMap_comp, hskL, uliftForPresentationMap_zero]
    simp only [Category.assoc]
    rw [hdb, hab, comp_zero]
  obtain ⟨T, idx', π₁, -, hfac'⟩ := exists_free_hom_of_sections (kernel π)
    fun k ↦ kernel.lift π (sk k) (hskπ k)
  set α : free (R := R) T ⟶ free (R := R) A := π₁ ≫ kernel.ι π with hα
  have hαπ : α ≫ π = 0 := by rw [hα, Category.assoc, kernel.condition, comp_zero]
  set ε : Q ⟶ uliftForPresentation.{u, v, r, r, max u v r} (free (R := R) T) :=
    Cofan.IsColimit.desc hQ
      (fun k ↦ uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (idx' k))) with hε
  have hεfac : ∀ k, κ k ≫ ε =
      uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (R := R) (idx' k)) :=
    fun k ↦ Cofan.IsColimit.fac hQ _ k
  have hεα : ε ≫ uliftForPresentationMap.{u, v, r, r, max u v r} α = a ≫ d := by
    refine Cofan.IsColimit.hom_ext hQ _ _ fun k ↦ ?_
    simp only [Limits.cofan_mk_inj, ← Category.assoc]
    rw [hεfac k, ← uliftForPresentationMap_comp, hα, ← Category.assoc, hfac' k, kernel.lift_ι,
      hskL k]
    simp
  -- The lift of `π` is a cokernel of the lift of `α`, because `d` is a split epimorphism.
  have hLα : uliftForPresentationMap.{u, v, r, r, max u v r} α ≫
      uliftForPresentationMap.{u, v, r, r, max u v r} π = 0 := by
    rw [← uliftForPresentationMap_comp, hαπ, uliftForPresentationMap_zero]
  have hLcol : IsColimit (CokernelCofork.ofπ
      (uliftForPresentationMap.{u, v, r, r, max u v r} π) hLα) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} k hk ↦ ?_
    have h0 : a ≫ d ≫ k = 0 := by
      rw [← Category.assoc, ← hεα, Category.assoc, hk, comp_zero]
    obtain ⟨m, hm⟩ := CokernelCofork.IsColimit.desc' hb (d ≫ k) h0
    have hm' : b ≫ m = d ≫ k := hm
    refine ⟨m, ?_⟩
    have e1 : uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m =
        j ≫ d ≫ uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m := by
      rw [← Category.assoc j, hjd, Category.id_comp]
    have e2 : j ≫ d ≫ uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m = j ≫ d ≫ k := by
      rw [← Category.assoc d, hdb, hm']
    have e3 : j ≫ d ≫ k = k := by rw [← Category.assoc, hjd, Category.id_comp]
    rw [e1, e2, e3]
  -- The universe lift is full and faithful, so that cokernel diagram descends.
  have hcol : IsColimit (CokernelCofork.ofπ π hαπ) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} k hk ↦ ?_
    have hk' : uliftForPresentationMap.{u, v, r, r, max u v r} α ≫
        uliftForPresentationMap.{u, v, r, r, max u v r} k = 0 := by
      rw [← uliftForPresentationMap_comp, hk, uliftForPresentationMap_zero]
    obtain ⟨m, hm⟩ := CokernelCofork.IsColimit.desc' hLcol
      (uliftForPresentationMap.{u, v, r, r, max u v r} k) hk'
    have hm' : uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m =
      uliftForPresentationMap.{u, v, r, r, max u v r} k := hm
    refine ⟨uliftForPresentationMapDown m, uliftForPresentationMap_injective ?_⟩
    rw [uliftForPresentationMap_comp, uliftForPresentationMap_down]
    exact hm'
  exact ⟨presentationOfIsCokernelFree α π hαπ hcol⟩

end Descend

section Equivalence

variable {R : Sheaf J RingCat.{r}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{r}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Quasi-coherence in the sense of Stacks 03DL(6) gives Mathlib's quasi-coherent data: by
Stacks 03DN the global presentations may be taken on a family covering the final object, and on
a site small relative to the universe of the sections each of them is a
`SheafOfModules.Presentation`. -/
public theorem IsQuasicoherentOnSite.nonempty_quasicoherentData [UnivLE.{max u v r, r}]
    {M : SheafOfModules.{r} R} (h : M.IsQuasicoherentOnSite) :
    Nonempty M.QuasicoherentData.{u} := by
  obtain ⟨I, X, hX, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation M).1 h
  refine ⟨{ I := I, X := X, coversTop := hX, presentation := fun i => ?_ }⟩
  have : ∀ N : SheafOfModules.{r} (R.over (X i)), Small.{r} N.sections :=
    fun N => small_sections_of_univLE N
  exact (hP i).nonempty_presentation_of_small_sections.some

/-- **The quasi-coherence of Stacks 03DL(6) implies Mathlib's**, on a site whose objects and
morphisms are small relative to the universe of the sections. -/
public theorem IsQuasicoherentOnSite.isQuasicoherent [UnivLE.{max u v r, r}]
    {M : SheafOfModules.{r} R} (h : M.IsQuasicoherentOnSite) : M.IsQuasicoherent :=
  (IsQuasicoherentOnSite.nonempty_quasicoherentData h).some.isQuasicoherent

/-- **Mathlib's quasi-coherence and the quasi-coherence of Stacks 03DL(6) agree** on a site
whose objects and morphisms are small relative to the universe of the sections.  The hypothesis
is not removable: on the big fppf site over `S : Scheme.{u}` the site lives in `Type (u + 1)`
and the sections in `Type u`, where it fails by `not_univLE_succ`. -/
public theorem isQuasicoherent_iff_isQuasicoherentOnSite [UnivLE.{max u v r, r}]
    (M : SheafOfModules.{r} R) : M.IsQuasicoherent ↔ M.IsQuasicoherentOnSite :=
  ⟨fun _ => isQuasicoherentOnSite_of_isQuasicoherent M, fun h => h.isQuasicoherent⟩

end Equivalence

end SheafOfModules

/-- **The size hypothesis of `SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite` is not
vacuous.**  On a big site the objects live one universe above the sections, so the hypothesis
reads `UnivLE.{u + 1, u}`, and that is false: `Type u` is not `Small.{u}`.  Mathlib proves this
as an anonymous `example`; it is named here because it is the concrete obstruction to
identifying the two quasi-coherence predicates on the big fppf site. -/
public theorem not_univLE_succ : ¬ UnivLE.{u + 1, u} := by
  rw [univLE_iff]
  exact fun h => not_small_type.{u} (h (Type u))

end
