module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# A finite presentation from a finite global presentation, in an arbitrary module universe

Stacks 03DE(7), `SheafOfModules.HasFiniteGlobalPresentation`, presents a sheaf of modules as the
cokernel of a map between coproducts of *finitely many* copies of the structure sheaf, after
raising the universe of the sections to the universe `max u v w` containing the site.  Mathlib's
`SheafOfModules.Presentation` presents the sheaf itself, by free sheaves of modules indexed in
the universe `w` of the sections.  This file turns the first into the second, with its finiteness
intact, and with no relation between `w` and the universes of the site.

`AlgebraicGeometry.SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation`
already does this when `w = max u v`, where the universe lift is an isomorphism; that hypothesis
is what forces the comparison of the two renderings of Stacks 03DL(7) to be stated at that single
universe, and it fails on a big site, whose objects lie one universe above its sections.  The
unrestricted statement for the *infinite* notion is
`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`, under the
hypothesis — not a hypothesis on the site — that the global sections of every sheaf of modules be
small relative to `w`.  A site with a final object satisfies it, by
`SheafOfModules.small_sections_of_isTerminal`.

What is proved here is the finite analogue, at the same hypothesis.  The argument is the one of
the infinite case and is repeated rather than deduced, because the infinite statement returns a
bare `Nonempty` and so discards exactly the index types whose finiteness is the point.  Both
index types are replaced by the *image* in the global sections of the finite index type the
global presentation supplies, and the image of a finite type is finite: for the generators that
is already what the infinite argument does, since restricting to the image is what makes the
comparison map a split epimorphism; for the relations the infinite argument takes all sections of
the kernel, and taking instead the image of the second finite index type is the one change.

## Main results

* `Stacks.SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation_of_small`:
  a finite global presentation in the sense of Stacks 03DE(7) yields a finite
  `SheafOfModules.Presentation`, on a site whose sheaves of modules have small global sections.
* `Stacks.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite_of_small`: hence
  Stacks 03DL(7) in the rendering by universal properties implies Mathlib's
  `SheafOfModules.IsFinitePresentation`, with no restriction on the module universe.

## Implementation notes

No tag attribute is placed.  Stacks 03DL(7) is carried by
`SheafOfModules.IsFinitePresentationOnSite` and by Mathlib's
`SheafOfModules.IsFinitePresentation`, and what is proved here is the comparison of those two
renderings of it, not a further part of the source's content.  This follows
`StacksFrontier/AlgebraicGeometry/Topologies/FinitePresentationOnSiteBridge.lean`, which says the
same of its universe-restricted version.

The covering family required of Mathlib's `SheafOfModules.IsFinitePresentation` is the family of
all objects over which the module has a finite global presentation; it covers the final object
because, by Stacks 03DL(7), every object of the site is covered by such objects.  This is the
assembly of `AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite`
run again at an arbitrary module universe.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules

universe r v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- A finite family of global sections of a sheaf of modules `N` is hit by the generators of a free
module on a finite index type `A` (the image of the family), through one map `free A ⟶ N`. -/
private theorem exists_finite_free_hom_of_unit_homs
    [∀ N : _root_.SheafOfModules.{r} R, Small.{r} N.sections] {n : ℕ}
    (N : _root_.SheafOfModules.{r} R) (s : Fin n → (unit R ⟶ N)) :
    ∃ (A : Type r) (_ : Finite A) (idx : Fin n → A) (π : free (R := R) A ⟶ N),
      Function.Surjective idx ∧ ∀ i, ιFree (idx i) ≫ π = s i := by
  set idx : Fin n → Shrink.{r} N.sections :=
    fun i ↦ equivShrink N.sections (N.unitHomEquiv (s i)) with hidx
  refine ⟨Set.range idx, Set.finite_coe_iff.2 (Set.finite_range idx),
    fun i ↦ ⟨idx i, i, rfl⟩,
    N.freeHomEquiv.symm fun c ↦ (equivShrink N.sections).symm c.1, ?_, fun i ↦ ?_⟩
  · rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩
  · rw [← unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
    simp [hidx]

/-- **A finite global presentation gives a finite `SheafOfModules.Presentation`**, on a site
whose sheaves of modules have `Type r`-small global sections, and with no relation between the
universe `r` of the sections and the universes of the site.

Write `L` for the universe lift, `b : P ⟶ L M` for the epimorphism out of the first coproduct,
`ι` for its cofan over `Fin n`, and `a : Q ⟶ P` for the relation map with cofan `κ` over
`Fin k`.  Each `ι i ≫ b` is `L` of a global section of `M`, the lift being full, so the `n`
generators name a finite set `A` of global sections, and the comparison map `d : P ⟶ L (free A)`
is a *split* epimorphism — a splitting picks for each member of `A` one of the `n` indices that
produced it.  Splitness moves the cokernel across the factorisation `b = d ≫ L π`.  The same
device applies to the relations: each `κ j ≫ a ≫ d` is `L` of a global section of `free A`
killed by `π`, hence of `kernel π`, and those `k` sections name a finite set `T`, through whose
free module `a ≫ d` factors.  Fullness and faithfulness of the lift carry the resulting cokernel
diagram back down, and `SheafOfModules.presentationOfIsCokernelFree` reads off the presentation,
whose two index types are the finite sets `A` and `T`. -/
theorem exists_isFinite_presentation_of_hasFiniteGlobalPresentation_of_small
    [∀ N : _root_.SheafOfModules.{r} R, Small.{r} N.sections]
    {M : _root_.SheafOfModules.{r} R} (h : M.HasFiniteGlobalPresentation) :
    ∃ P : M.Presentation, P.IsFinite := by
  classical
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  have hU : PreservesColimitsOfSize.{r, r}
      (uliftForPresentationFunctor.{u, v, r, r, max u v r} (R := R)) :=
    preservesColimitsOfSize_uliftForPresentationFunctor' R
  -- The generators: the image in the global sections of the finite index type `Fin n`.
  obtain ⟨A, hAfin, idx, π, hidxs, hfac⟩ := exists_finite_free_hom_of_unit_homs M
    fun i ↦ uliftForPresentationMapDown (ι i ≫ b)
  -- The comparison map out of the coproduct, and the splitting its index set affords.
  set d : P ⟶ uliftForPresentation.{u, v, r, r, max u v r} (free (R := R) A) :=
    Cofan.IsColimit.desc hP
      (fun i ↦ uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (idx i))) with hd
  have hdfac : ∀ i, ι i ≫ d =
      uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (R := R) (idx i)) := by
    intro i
    rw [hd]
    exact Cofan.IsColimit.fac hP _ i
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
    Cofan.IsColimit.desc hfreeA (fun s ↦ ι (Function.surjInv hidxs s)) with hj
  have hjfac : ∀ s : A, uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree s) ≫ j =
      ι (Function.surjInv hidxs s) := by
    intro s
    rw [hj]
    exact Cofan.IsColimit.fac hfreeA _ s
  have hjd : j ≫ d = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hfreeA _ _ fun s ↦ ?_
    rw [Limits.cofan_mk_inj, ← Category.assoc, hjfac s, hdfac, Function.surjInv_eq hidxs s]
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
  -- The relations: the image in the sections of `kernel π` of the finite index type `Fin k`.
  set sk : Fin k → (unit R ⟶ free (R := R) A) :=
    fun l ↦ uliftForPresentationMapDown (κ l ≫ a ≫ d) with hsk
  have hskL : ∀ l, uliftForPresentationMap.{u, v, r, r, max u v r} (sk l) = κ l ≫ a ≫ d :=
    fun l ↦ uliftForPresentationMap_down _
  have hskπ : ∀ l, sk l ≫ π = 0 := by
    intro l
    refine uliftForPresentationMap_injective ?_
    rw [uliftForPresentationMap_comp, hskL, uliftForPresentationMap_zero]
    simp only [Category.assoc]
    rw [hdb, hab, comp_zero]
  obtain ⟨T, hTfin, idx', π₁, -, hfac'⟩ := exists_finite_free_hom_of_unit_homs (kernel π)
    fun l ↦ kernel.lift π (sk l) (hskπ l)
  set α : free (R := R) T ⟶ free (R := R) A := π₁ ≫ kernel.ι π with hα
  have hαπ : α ≫ π = 0 := by rw [hα, Category.assoc, kernel.condition, comp_zero]
  set ε : Q ⟶ uliftForPresentation.{u, v, r, r, max u v r} (free (R := R) T) :=
    Cofan.IsColimit.desc hQ
      (fun l ↦ uliftForPresentationMap.{u, v, r, r, max u v r} (ιFree (idx' l))) with hε
  have hεfac : ∀ l, κ l ≫ ε =
      uliftForPresentationMap.{u, v, r, r, max u v r}
        (ιFree (R := R) (idx' l)) := by
    intro l
    rw [hε]
    exact Cofan.IsColimit.fac hQ _ l
  have hεα : ε ≫ uliftForPresentationMap.{u, v, r, r, max u v r} α = a ≫ d := by
    refine Cofan.IsColimit.hom_ext hQ _ _ fun l ↦ ?_
    simp only [Limits.cofan_mk_inj, ← Category.assoc]
    rw [hεfac l, ← uliftForPresentationMap_comp, hα, ← Category.assoc, hfac' l,
      kernel.lift_ι, hskL l]
    simp
  -- The lift of `π` is a cokernel of the lift of `α`, because `d` is a split epimorphism.
  have hLα : uliftForPresentationMap.{u, v, r, r, max u v r} α ≫
      uliftForPresentationMap.{u, v, r, r, max u v r} π = 0 := by
    rw [← uliftForPresentationMap_comp, hαπ, uliftForPresentationMap_zero]
  have hLcol : IsColimit (CokernelCofork.ofπ
      (uliftForPresentationMap.{u, v, r, r, max u v r} π) hLα) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} z hz ↦ ?_
    have h0 : a ≫ d ≫ z = 0 := by
      rw [← Category.assoc, ← hεα, Category.assoc, hz, comp_zero]
    obtain ⟨m, hm⟩ := CokernelCofork.IsColimit.desc' hb (d ≫ z) h0
    have hm' : b ≫ m = d ≫ z := hm
    refine ⟨m, ?_⟩
    have e1 : uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m =
        j ≫ d ≫ uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m := by
      rw [← Category.assoc j, hjd, Category.id_comp]
    have e2 : j ≫ d ≫ uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m = j ≫ d ≫ z := by
      rw [← Category.assoc d, hdb, hm']
    have e3 : j ≫ d ≫ z = z := by rw [← Category.assoc, hjd, Category.id_comp]
    rw [e1, e2, e3]
  -- The universe lift is full and faithful, so that cokernel diagram descends.
  have hcol : IsColimit (CokernelCofork.ofπ π hαπ) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {Z} z hz ↦ ?_
    have hz' : uliftForPresentationMap.{u, v, r, r, max u v r} α ≫
        uliftForPresentationMap.{u, v, r, r, max u v r} z = 0 := by
      rw [← uliftForPresentationMap_comp, hz, uliftForPresentationMap_zero]
    obtain ⟨m, hm⟩ := CokernelCofork.IsColimit.desc' hLcol
      (uliftForPresentationMap.{u, v, r, r, max u v r} z) hz'
    have hm' : uliftForPresentationMap.{u, v, r, r, max u v r} π ≫ m =
      uliftForPresentationMap.{u, v, r, r, max u v r} z := hm
    refine ⟨uliftForPresentationMapDown m, uliftForPresentationMap_injective ?_⟩
    rw [uliftForPresentationMap_comp, uliftForPresentationMap_down]
    exact hm'
  exact ⟨presentationOfIsCokernelFree α π hαπ hcol,
    ⟨⟨inferInstanceAs (Finite A)⟩, ⟨inferInstanceAs (Finite T)⟩⟩⟩

omit [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
/-- **The two renderings of Stacks 03DL(7) compared, at an arbitrary module universe.**  A sheaf
of modules of finite presentation in the covering-family sense of
`SheafOfModules.IsFinitePresentationOnSite` is of finite presentation in Mathlib's sense, on a
site whose sheaves of modules have `Type r`-small global sections.

This is
`AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite` with its
restriction to the module universe `max u v` removed; the covering family is the family of all
objects over which the module has a finite global presentation. -/
theorem isFinitePresentation_of_isFinitePresentationOnSite_of_small
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{r}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [∀ (X : C) (N : _root_.SheafOfModules.{r} (R.over X)), Small.{r} N.sections]
    (M : _root_.SheafOfModules.{r} R) [M.IsFinitePresentationOnSite] :
    M.IsFinitePresentation := by
  rw [Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations]
  refine ⟨{ X : C // (M.over X).HasFiniteGlobalPresentation }, Subtype.val, ?_, ?_⟩
  · intro X
    obtain ⟨I, V, f, hf, hV⟩ :=
      _root_.SheafOfModules.IsFinitePresentationOnSite.locally_hasFiniteGlobalPresentation
        (F := M) X
    refine J.superset_covering ?_ hf
    refine (Sieve.generate_le_iff _ _).mpr ?_
    intro W g hg
    obtain ⟨i⟩ := hg
    exact ⟨⟨V i, hV i⟩, ⟨𝟙 _⟩⟩
  · intro i
    exact exists_isFinite_presentation_of_hasFiniteGlobalPresentation_of_small i.property

end Stacks.SheafOfModules

end
