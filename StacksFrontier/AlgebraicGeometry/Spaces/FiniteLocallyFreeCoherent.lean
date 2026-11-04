module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure

/-!
# Finite locally free modules on a locally Noetherian algebraic space are coherent

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `M` be
an `𝒪_F`-module on the small étale site of `F` which is **finite locally free**
(`SheafOfModules.IsFiniteLocallyFreeOnSite`, Stacks 03DL(2)): every étale chart of `F` has a
covering on whose members the restriction of `M` is a finite coproduct of copies of the
structure sheaf.  If `F` is locally Noetherian then `M` is coherent.  This is the last assertion
of Stacks 07UB.

The proof does **not** go through Descent, Proposition 03DX(2), and that is the point of this
file.  `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` — the base change criterion that the
chart-sections files of this tree carry as a hypothesis, and which for a general quasi-coherent
module is 03DX(2) — quantifies over *all* morphisms of affine étale charts, whereas a local
trivialization of `M` gives the base change property only between charts lying over one
trivializing chart.  Three things bridge that gap, and none of them is 03DX:

* the relations clause of `StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules` uses the base
  change property **once**, between two `Good` charts, so it is enough to supply the property
  there and not everywhere.  The general forms in that file now carry exactly that localized
  hypothesis;
* the discharge of the base change property for a free module
  (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan`) transports to the
  slice site at a chart, by `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv`
  below; and
* a chart can be covered by charts which are simultaneously affine, Noetherian and
  trivializing, because finite freeness on a slice is inherited by every smaller slice.

## Main results

* `Stacks.SheafOfModules.exists_piEquiv_of_isColimit_cofan`: **the sections of a finite
  coproduct of copies of one sheaf of modules over any object of any site are the families of
  sections of that sheaf, naturally in the object**, and
  `Stacks.SheafOfModules.exists_finsuppEquiv_of_isColimit_cofan`, its case of a coproduct of
  copies of the structure sheaf.  Finiteness of the index is what makes these free of
  quasi-compactness hypotheses: a finite coproduct in a preadditive category is a biproduct, so
  the coprojections admit retractions which compute the sections elementwise.
* `Stacks.SheafOfModules.isFiniteFree_over_of_le`: finite freeness of the restriction of a
  sheaf of modules to a slice site is inherited by every smaller slice site, at an arbitrary
  module universe.
* `SheafOfModules.hasGlobalPresentation_of_isFiniteFree`: **a finite free sheaf of modules on
  any site has a global presentation**, at an arbitrary module universe, and
  `SheafOfModules.isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite`: **a finite locally free
  sheaf of modules is quasi-coherent**, which is Stacks 03DL(2) ⇒ Stacks 03DL(6).
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isFiniteFree_over`: **the base
  change comparison of `M` over any morphism of charts lying over a chart `A` on which `M` is
  finite free is bijective.**  No affineness and no cohomological input.
* `AlgebraicGeometry.Space.exists_generates_of_isFiniteFree_over` and
  `AlgebraicGeometry.Space.isFiniteType_of_isFiniteLocallyFreeOnSite`: a finite locally free
  module is of finite type in the sectionwise sense of Stacks 03DL(5).
* `AlgebraicGeometry.Space.exists_covering_through_noetherianAffineFree`: every étale chart of a
  locally Noetherian algebraic space is covered by charts which are affine, have Noetherian ring
  of sections, and trivialize `M`.
* `AlgebraicGeometry.Space.isCoherentOnSite_of_isFiniteLocallyFreeOnSite`: **a finite locally
  free module on a locally Noetherian algebraic space is coherent on the small étale ringed
  site**, at an arbitrary module universe.
* `AlgebraicGeometry.Space.isCoherent_of_isFiniteLocallyFreeOnSite` and
  `AlgebraicGeometry.Space.isCoherent_of_fact_isFiniteLocallyFreeOnSite`: **such a module is
  coherent**, at an arbitrary module universe, as a theorem and as an instance.

## Implementation notes

**The module universe is free throughout, as it is in the source.**  Nothing here pins it.  In
particular quasi-coherence is *not* obtained from coherence on the site:
`SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite` is available only when the module
universe equals the coefficient universe, because it builds a presentation out of Mathlib's
`SheafOfModules.free`, which exists only there.  It is obtained instead from finite local
freeness directly, by `SheafOfModules.hasGlobalPresentation_of_isFiniteFree`, where the
universe crossing is absorbed by `SheafOfModules.uliftForPresentation`: the predicate
`SheafOfModules.HasGlobalPresentation` takes its coproducts and its cokernel in the single
universe `max u v r m`, both the finite free model and the module are raised there, and the
natural linear equivalences of `SheafOfModules.IsFiniteFree` — which relate the coefficient
universe to the module universe — become an isomorphism of the two lifts through
`ULift.moduleEquiv`.  A finite free module is then a presentation with no relations: the
coproduct is the module itself and the identity is a cokernel of the zero map.

**Why the sections of the free model are computed by hand.**  The comparison
`Stacks.Sites.freeSectionsMap` of `StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections` is
bijective only over a *quasi-compact* object of the site, because `SheafOfModules.free` on an
arbitrary index type is a sheafification.  For a *finite* index no such hypothesis is needed,
and here it must not be assumed: the base change property is needed over the charts lying over
a trivializing chart, and those are not affine in general.  The elementary argument replacing it
is `Stacks.SheafOfModules.exists_piEquiv_of_isColimit_cofan`: the colimit property of the
cofan produces retractions `π i` of its legs with `∑ i, π i ≫ ι i = 𝟙`, and evaluating that
identity at an object of the site inverts the map `x ↦ (π i x)` on sections.

That argument is the abstract-cofan form of `Stacks.SheafOfModules.id_free_eq_sum`,
`Stacks.SheafOfModules.freeCoord_map` and `Stacks.SheafOfModules.freeCoord_bijective`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkFreeCover.lean:163`, `:197`, `:231`), which
run the same three steps for Mathlib's `SheafOfModules.free` on a finite index under
`[HasWeakSheafify]`.  Those could be re-derived from the general form through
`SheafOfModules.isColimitFreeCofan`; they are not, because they live upstream of this file.
`Stacks.SheafOfModules.app_sum` of the same file is reused rather than restated.

**The slice site is definitionally transparent here, and that is used throughout.**  For a chart
`A` and an object `V` of `Over A`, `(M.over A).val.obj (op V)` is `M.val.obj (op V.left)` and
`((ringSheaf X).over A).obj.obj (op V)` is `(ringSheaf X).obj.obj (op V.left)`, both by `rfl`,
because restriction to a slice is pushforward along `Over.forget` followed by restriction of
scalars along an identity.  Restriction maps agree in the same way.  The two spellings
nevertheless produce *different instance terms* for the scalar action on the sections, so a
`rw [map_smul]` or `rw [map_sum]` whose instances are synthesized from the chart spelling will
not fire on a goal phrased in the slice spelling; the proofs below either phrase a whole
statement in one spelling or apply the lemma in term mode, where unification is up to
definitional equality.

`AlgebraicGeometry.Space.IsNoetherianAffineFreeChart` exists only so that the
`Good` predicate of the general results of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules` is written once.  It reuses
`AlgebraicGeometry.Space.IsAffineChart` and spells its Noetherian component as
`AlgebraicGeometry.Space.exists_covering_through_noetherianAffine` does, so that the covering
produced there is accepted with no transport.

Stacks 07UB has five numbered equivalent conditions and three further assertions, of which this
file proves one: the final one, for a finite locally free module.  So the part-string
`@[stacks 07UB "finite locally free modules"]` sits on
`AlgebraicGeometry.Space.isCoherent_of_fact_isFiniteLocallyFreeOnSite`, beside the pre-existing
`@[stacks 07UB "structure sheaf"]` of `AlgebraicGeometry.Space.isCoherent_structureSheaf`, and
the bare tag is not claimed: the five numbered conditions are not proved here.

**Placement still owed.**  Seven of the results below mention no chart and no algebraic space:
the four in `Stacks.SheafOfModules`, the two in `SheafOfModules`, and
`AlgebraicGeometry.Space.exists_generates_of_isFiniteFree_over` together with
`AlgebraicGeometry.Space.isFiniteType_of_isFiniteLocallyFreeOnSite`, whose proofs touch only
`.J`, `.C`, `SheafOfModules.over` and sieves.  The last two are Stacks 03DL(2) ⇒ Stacks 03DL(5)
in the sectionwise form and belong beside 03DL itself in
`StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite`, the two `SheafOfModules` ones
likewise, and the four cofan and slice results belong in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree` beside
`Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`, whose docstring already advertises the
coefficient-universe form of `Stacks.SheafOfModules.isFiniteFree_over_of_le`.  They are gathered
here because moving declarations between modules is a repository-wide change and this file is
one landing; the risk of leaving them is that a second copy of 03DL(2) ⇒ 03DL(5) gets written
against a different predicate stack, as already happened once — compare
`Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree` and
`...isQuasicoherent_of_isFiniteLocallyFree`, which prove the same two implications for *Mathlib's*
`SheafOfModules.IsFiniteLocallyFree`.

**Two upstream lemmas are special cases of
`SheafOfModules.hasFiniteGlobalPresentation_of_isFiniteFree` and are not re-derived from it.**
`SheafOfModules.hasGlobalPresentation_unit` is the case `n = 1` with the module universe equal to
the coefficient universe, and `SheafOfModules.hasGlobalPresentation_of_isZero` is the case
`n = 0`; both live upstream of this file, so collapsing them is a separate change.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **The sections of a module exhibited as a finite coproduct.**  If a cofan with point `N` and
`n` legs out of a module `E` is a colimit, then the sections of `N` over every object of the site
are the `Fin n`-indexed families of sections of `E`, naturally in the object.

No quasi-compactness of the object is needed, in contrast with
`Stacks.Sites.bijective_freeSectionsMap`, and this is what finiteness of the index buys: a
finite coproduct in a preadditive category is a biproduct, so each leg `ι i` has a retraction
`π i` obtained from the colimit property, these satisfy `∑ i, π i ≫ ι i = 𝟙 N`, and evaluating
that identity on sections inverts `x ↦ (π i x)`. -/
theorem exists_piEquiv_of_isColimit_cofan {n : ℕ} {E N : SheafOfModules.{w} R}
    (ι : ∀ _ : Fin n, E ⟶ N) (hN : IsColimit (Cofan.mk N ι)) :
    ∃ θ : ∀ X : Cᵒᵖ, (N.val.obj X) ≃ₗ[R.obj.obj X] (Fin n → E.val.obj X),
      ∀ ⦃X Y : Cᵒᵖ⦄ (g : X ⟶ Y) (x : N.val.obj X) (i : Fin n),
        θ Y (N.val.map g x) i = E.val.map g (θ X x i) := by
  classical
  set π : Fin n → (N ⟶ E) := fun i =>
    Cofan.IsColimit.desc hN (fun j => if j = i then 𝟙 E else 0)
  have hfac : ∀ i j, ι j ≫ π i = if j = i then 𝟙 E else 0 := fun i j => by
    have h := Cofan.IsColimit.fac hN (fun j => if j = i then 𝟙 E else 0) j
    rwa [cofan_mk_inj] at h
  have hfac1 : ∀ i, ι i ≫ π i = 𝟙 E := fun i => by simpa using hfac i i
  have hfac0 : ∀ i j, j ≠ i → ι j ≫ π i = 0 := fun i j h => by simpa [h] using hfac i j
  have htot : ∑ i, π i ≫ ι i = 𝟙 N := by
    refine Cofan.IsColimit.hom_ext hN _ _ (fun j => ?_)
    simp only [cofan_mk_inj, Preadditive.comp_sum]
    rw [Finset.sum_eq_single j]
    · rw [← Category.assoc, hfac1 j, Category.id_comp]
      exact (Category.comp_id (ι j)).symm
    · intro i _ hij
      rw [← Category.assoc, hfac0 i j (Ne.symm hij), Limits.zero_comp]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hΨΘ : ∀ (X : Cᵒᵖ) (x : N.val.obj X),
      ∑ i, (ι i).val.app X ((π i).val.app X x) = x := by
    intro X x
    have h := app_sum Finset.univ (fun i => π i ≫ ι i) X x
    rw [htot] at h
    exact h.symm
  have hΘΨ : ∀ (X : Cᵒᵖ) (y : Fin n → E.val.obj X) (i : Fin n),
      (π i).val.app X (∑ j, (ι j).val.app X (y j)) = y i := by
    intro X y i
    rw [map_sum, Finset.sum_eq_single i]
    · exact congrFun (congrArg (fun φ : E ⟶ E => fun z => (φ.val.app X) z) (hfac1 i)) (y i)
    · intro j _ hji
      exact congrFun (congrArg (fun φ : E ⟶ E => fun z => (φ.val.app X) z) (hfac0 i j hji)) (y j)
    · intro h; exact absurd (Finset.mem_univ i) h
  refine ⟨fun X => LinearEquiv.ofBijective (LinearMap.pi fun i => ((π i).val.app X).hom)
    (Function.bijective_iff_has_inverse.2
      ⟨fun y => ∑ i, (ι i).val.app X (y i), hΨΘ X, fun y => funext (hΘΨ X y)⟩), ?_⟩
  intro X Y g x i
  exact PresheafOfModules.naturality_apply (π i).val g x

/-- **The sections of a finite coproduct of copies of the structure sheaf over any object of any
site are the finitely supported families of sections of the structure sheaf**, naturally in the
object.  This is the case `E = SheafOfModules.unit R` of
`Stacks.SheafOfModules.exists_piEquiv_of_isColimit_cofan`, with the finitely supported families
substituted for the functions by `Finsupp.linearEquivFunOnFinite`. -/
theorem exists_finsuppEquiv_of_isColimit_cofan {n : ℕ} {N : SheafOfModules.{w} R}
    (ι : ∀ _ : Fin n, SheafOfModules.unit R ⟶ N)
    (hN : IsColimit (Cofan.mk N ι)) :
    ∃ θ : ∀ X : Cᵒᵖ, (N.val.obj X) ≃ₗ[R.obj.obj X] (Fin n →₀ R.obj.obj X),
      ∀ ⦃X Y : Cᵒᵖ⦄ (g : X ⟶ Y) (x : N.val.obj X) (i : Fin n),
        θ Y (N.val.map g x) i = R.obj.map g (θ X x i) := by
  obtain ⟨θ, hθ⟩ := exists_piEquiv_of_isColimit_cofan ι hN
  exact ⟨fun X => (θ X).trans
    (Finsupp.linearEquivFunOnFinite (R.obj.obj X) (R.obj.obj X) (Fin n)).symm, hθ⟩

/-- **The sections of a finite free sheaf of modules are the finitely supported families of
sections of the structure sheaf**, naturally in the object of the site.

This is `SheafOfModules.IsFiniteFree` read on sections: the finite free model's sections are
computed by `Stacks.SheafOfModules.exists_finsuppEquiv_of_isColimit_cofan` and transported along
the natural linear equivalences of the predicate, which cross module universes harmlessly
because only the module's own sections appear in the conclusion.  It is the
`SheafOfModules.IsFiniteFree` analogue of
`SheafOfModules.isFiniteFree_iff_exists_isColimit`, which collapses the model only when the
module and coefficient universes agree. -/
theorem exists_finsuppEquiv_of_isFiniteFree {M : SheafOfModules.{m} R}
    (h : SheafOfModules.IsFiniteFree R M) :
    ∃ (n : ℕ) (ψ : ∀ X : Cᵒᵖ, (M.val.obj X) ≃ₗ[R.obj.obj X] (Fin n →₀ R.obj.obj X)),
      ∀ ⦃X Y : Cᵒᵖ⦄ (g : X ⟶ Y) (x : M.val.obj X) (i : Fin n),
        ψ Y (M.val.map g x) i = R.obj.map g (ψ X x i) := by
  obtain ⟨n, N, ι, ⟨hcol⟩, e, he⟩ := h
  obtain ⟨θ, hθ⟩ := exists_finsuppEquiv_of_isColimit_cofan ι hcol
  refine ⟨n, fun X => (e X).symm.trans (θ X), ?_⟩
  have ht : ∀ (X : Cᵒᵖ) (z : M.val.obj X),
      ((e X).symm.trans (θ X)) z = θ X ((e X).symm z) := fun _ _ => rfl
  intro X Y g x i
  obtain ⟨y, rfl⟩ : ∃ y, x = e X y := ⟨(e X).symm x, ((e X).apply_symm_apply x).symm⟩
  simp only [ht, ← he g y, LinearEquiv.symm_apply_apply]
  exact Eq.trans (congrArg (fun z => (θ Y z) i) ((e Y).symm_apply_apply _)) (hθ g y i)

/-- **Finite freeness on a slice site is inherited by every smaller slice site**, at an
arbitrary module universe.

This is the `SheafOfModules.IsFiniteFree` form of
`Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`, which is stated for a module in the
coefficient universe.  The finite free model is carried along by
`SheafOfModules.overMap`, which preserves finite coproducts because it is additive, and the
natural linear equivalences are reindexed along `CategoryTheory.Over.map`: the sections of a
module restricted to a slice are the sections over the underlying object, so no transport of
them is needed. -/
theorem isFiniteFree_over_of_le {M : SheafOfModules.{m} R} {Z Y : C} (h : Z ⟶ Y)
    (hM : SheafOfModules.IsFiniteFree (R.over Y) (M.over Y)) :
    SheafOfModules.IsFiniteFree (R.over Z) (M.over Z) := by
  obtain ⟨n, N, ι, ⟨hc⟩, e, he⟩ := hM
  have hp : PreservesColimit
      (Discrete.functor (fun _ : Fin n => SheafOfModules.unit (R.over Y)))
      (SheafOfModules.overMap.{w} R h) :=
    preservesCoproduct_of_preservesBiproduct _
  refine ⟨n, (SheafOfModules.overMap.{w} R h).obj N,
    fun i => (SheafOfModules.overMap.{w} R h).map (ι i), ⟨?_⟩,
    fun W => e (op ((Over.map h).obj W.unop)), ?_⟩
  · exact Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk N ι) (isColimitOfPreserves _ hc)
  · intro W W' g x
    exact he ((Over.map h).op.map g) x

end Stacks.SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite free sheaf of modules has a finite global presentation**, at an arbitrary module
universe: the presentation is the module itself, with no relations.

`SheafOfModules.HasFiniteGlobalPresentation` takes its coproducts and its cokernel in the single
universe `max u v w m` of the site objects, the site morphisms, the coefficient rings and the
module sections, so the finite free model — which lives in the coefficient universe — and the
module — which lives in the module universe — must first be raised there.  Both are raised by
`SheafOfModules.uliftForPresentation`, which lifts the sections objectwise, and the natural
linear equivalences of `SheafOfModules.IsFiniteFree` become an isomorphism of the two lifts
because `ULift.moduleEquiv` identifies each lifted module with the module itself.  The lift
carries the cofan to a cofan because it preserves zero morphisms and finite limits, hence finite
biproducts, hence finite coproducts; and the identity is a cokernel of the zero map, so the
isomorphism is the cokernel projection.

This is the *finite* presentation predicate and not `SheafOfModules.HasGlobalPresentation`,
which it implies by `SheafOfModules.HasFiniteGlobalPresentation.hasGlobalPresentation`: the
index of the coproduct is `Fin n` on the nose, so no reindexing into the presentation universe is
needed, and the finite-type and finite-presentation consequences of Stacks 03DL come out as
well.  It subsumes `SheafOfModules.hasGlobalPresentation_unit`, which is the case `n = 1` at
`m = w`, and `SheafOfModules.hasGlobalPresentation_of_isZero`, which is the case `n = 0`;
neither is re-derived from it here, since both live upstream. -/
theorem hasFiniteGlobalPresentation_of_isFiniteFree {M : SheafOfModules.{m} R}
    (h : SheafOfModules.IsFiniteFree R M) : M.HasFiniteGlobalPresentation := by
  obtain ⟨n, N, ι, ⟨hc⟩, e, he⟩ := h
  let L : SheafOfModules.{w} R ⥤ SheafOfModules.{max u v w m} R :=
    SheafOfModules.uliftForPresentationFunctor.{u, v, w, w, max u v m} (R := R)
  have hpb : PreservesBiproduct (fun _ : Fin n => SheafOfModules.unit R) L :=
    preservesBiproduct_of_preservesProduct L
  have hpc : PreservesColimit
      (Discrete.functor (fun _ : Fin n => SheafOfModules.unit R)) L :=
    preservesCoproduct_of_preservesBiproduct L
  have hcol : IsColimit (Cofan.mk (L.obj N) (fun i => L.map (ι i))) :=
    Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk N ι) (isColimitOfPreserves _ hc)
  let Mup : SheafOfModules.{max u v w m} R :=
    SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w} M
  have bIso : L.obj N ≅ Mup := by
    refine (SheafOfModules.fullyFaithfulForget R).preimageIso (PresheafOfModules.isoMk ?_ ?_)
    · exact fun X => (ULift.moduleEquiv.trans ((e X).trans ULift.moduleEquiv.symm)).toModuleIso
    · intro X Y g
      ext x
      exact congrArg ULift.up (he g x.down)
  exact ⟨n, n, L.obj N, L.obj N, fun i => L.map (ι i), fun i => L.map (ι i), ⟨hcol⟩, ⟨hcol⟩,
    0, bIso.hom, by rw [zero_comp],
    ⟨(CokernelCofork.IsColimit.ofId (0 : L.obj N ⟶ L.obj N) rfl).ofIsoColimit
      (Cofork.ext bIso (Category.id_comp _))⟩⟩

/-- **A finite locally free sheaf of modules on a site is of finite presentation**, at an
arbitrary module universe.  This is Stacks 03DL(2) ⇒ Stacks 03DL(7): the covering witnessing
finite local freeness is already a covering on whose members the module has a finite global
presentation, by `SheafOfModules.hasFiniteGlobalPresentation_of_isFiniteFree`.

Quasi-coherence (Stacks 03DL(6)) and finite type (Stacks 03DL(5)) then follow through the
existing instances `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite` and
`SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite`. -/
theorem isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite {M : SheafOfModules.{m} R}
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite M) : M.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation U := by
    obtain ⟨I, V, f, hf, hfree⟩ := h U
    exact ⟨I, V, f, hf, fun i => hasFiniteGlobalPresentation_of_isFiniteFree (hfree i)⟩

end SheafOfModules

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The base change comparison of a module trivialized on a slice -/

/-- **The base change comparison of a module is bijective over every morphism of charts lying
over a chart on which the module is finite free.**

This is the transport to the slice site at `A` of
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan`, and it is what replaces
Descent, Proposition 03DX(2) for a finite locally free module: no affineness of either chart is
needed and no cohomological input is used.  The sections of the finite free model over the two
charts, read as objects of the slice over `A`, are computed by
`Stacks.SheafOfModules.exists_finsuppEquiv_of_isColimit_cofan`, and the resulting
identifications are fed to
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv`. -/
theorem bijective_sectionsBaseChange_of_isFiniteFree_over {M : Modules.{u, m} B S hS F hF}
    {A A' : (smallEtaleRingedSite B S hS F hF).C}
    (hA : SheafOfModules.IsFiniteFree
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over A)
        (M.over A))
    (f : A' ⟶ A) :
    Function.Bijective (sectionsBaseChange M f) := by
  obtain ⟨n, ψ, hnat⟩ := Stacks.SheafOfModules.exists_finsuppEquiv_of_isFiniteFree hA
  refine bijective_sectionsBaseChange_of_finsuppEquiv f (ψ (op (Over.mk (𝟙 A))))
    (ψ (op (Over.mk f))) (fun x i => ?_)
  exact hnat ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 A)).op) x i

/-! ### Finite type of a finite locally free module -/

/-- **A module which is finite free over a chart is generated by finitely many of its sections
over that chart**, in the sectionwise sense of Stacks 03DL(5).

The generators are the preimages under the trivialization of the tautological finitely supported
families, and the covering sieve witnessing generation over any chart is the maximal one: the
coefficients of a section are read off by the trivialization at that chart. -/
theorem exists_generates_of_isFiniteFree_over {M : Modules.{u, m} B S hS F hF}
    {A : (smallEtaleRingedSite B S hS F hF).C}
    (hA : SheafOfModules.IsFiniteFree
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over A)
        (M.over A)) :
    ∃ (n : ℕ) (s : Fin n → M.val.obj (op A)),
      PresheafOfModules.Generates (smallEtaleRingedSite B S hS F hF).J M.val s := by
  classical
  obtain ⟨n, ψ, hnat⟩ := Stacks.SheafOfModules.exists_finsuppEquiv_of_isFiniteFree hA
  have hmap : ∀ (W₁ W₂ : (Over A)ᵒᵖ) (gg : W₁ ⟶ W₂) (z : (M.over A).val.obj W₁),
      ψ W₂ ((M.over A).val.map gg z)
        = Finsupp.mapRange
            ((((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS F hF).O)).over A).obj.map gg)
            (map_zero _) (ψ W₁ z) :=
    fun _ _ gg z => Finsupp.ext fun j =>
      (hnat gg z j).trans Finsupp.mapRange_apply.symm
  refine ⟨n, fun i => (ψ (op (Over.mk (𝟙 A)))).symm (Finsupp.single i 1), ?_⟩
  intro V f t
  refine ⟨⊤, (smallEtaleRingedSite B S hS F hF).J.top_mem V, fun W g _ => ?_⟩
  set A' : (Over A)ᵒᵖ := op (Over.mk (𝟙 A))
  set W' : (Over A)ᵒᵖ := op (Over.mk (g ≫ f))
  set u₁ : A' ⟶ W' :=
    (Over.homMk (g ≫ f) (by simp) : Over.mk (g ≫ f) ⟶ Over.mk (𝟙 A)).op
  set u₂ : (op (Over.mk f) : (Over A)ᵒᵖ) ⟶ W' :=
    (Over.homMk g (by simp) : Over.mk (g ≫ f) ⟶ Over.mk f).op
  have hcoef : ∀ i : Fin n,
      ψ W' ((M.over A).val.map u₁ ((ψ A').symm (Finsupp.single i 1)))
        = Finsupp.single i 1 := by
    intro i
    have h := hmap A' W' u₁ ((ψ A').symm (Finsupp.single i 1))
    rw [(ψ A').apply_symm_apply, Finsupp.mapRange_single] at h
    exact h.trans (congrArg (Finsupp.single i) (map_one _))
  have key : ∑ i, (ψ W' ((M.over A).val.map u₂ t) i) •
        (M.over A).val.map u₁ ((ψ A').symm (Finsupp.single i 1))
      = (M.over A).val.map u₂ t := by
    refine (ψ W').injective ?_
    refine Eq.trans (map_sum (ψ W') _ Finset.univ) ?_
    refine Eq.trans (Finset.sum_congr rfl (fun i _ => Eq.trans ((ψ W').map_smul _ _)
      (congrArg (fun p => (ψ W' ((M.over A).val.map u₂ t) i) • p) (hcoef i)))) ?_
    refine Finsupp.ext fun j => ?_
    refine Eq.trans (Finsupp.finsetSum_apply _ _ j) ?_
    refine Eq.trans (Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => ?_)) ?_
    · rw [Finsupp.smul_single_one, Finsupp.single_eq_of_ne (Ne.symm hij)]
    · exact absurd (Finset.mem_univ j) h
    · rw [Finsupp.smul_single_one, Finsupp.single_eq_same]
  exact ⟨fun i => ψ W' ((M.over A).val.map u₂ t) i, key⟩

/-- **A finite locally free module on an algebraic space is of finite type**, in the sectionwise
sense of Stacks 03DL(5).  The covering family is the family of all charts trivializing the
module, which covers because the trivializing charts of any chart do.  No Noetherian hypothesis
is used. -/
theorem isFiniteType_of_isFiniteLocallyFreeOnSite (M : Modules.{u, m} B S hS F hF)
    (hflf : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J M.val := by
  refine ⟨{A : (smallEtaleRingedSite B S hS F hF).C //
      SheafOfModules.IsFiniteFree
        (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over A)
          (M.over A)},
    Subtype.val, ?_, fun A => exists_generates_of_isFiniteFree_over A.2⟩
  intro Z
  obtain ⟨I, V, f, hcov, hfree⟩ := hflf Z
  refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_ hcov
  refine le_trans (Sieve.ofArrows_le_ofObjects V f) (Sieve.ofObjects_mono ?_)
  rintro X ⟨i, rfl⟩
  exact ⟨⟨V i, hfree i⟩, rfl⟩

/-! ### Coherence -/

/-- An étale chart of `F` is a *Noetherian affine free chart* for `M` when the scheme underlying
it is affine with Noetherian ring of global sections and the restriction of `M` to the slice at
it is finite free.

This is the `Good` predicate with which the general coherence results of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules` are instantiated below.  Its affine and
Noetherian components are `AlgebraicGeometry.Space.IsNoetherianAffineChart`, the predicate
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian` already uses for the same purpose and
which `AlgebraicGeometry.Space.exists_covering_through_noetherianAffine` produces, rather than a
second spelling of the conjunction; they discharge two of the hypotheses by a projection each; the
third component discharges the localized base change hypothesis through
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isFiniteFree_over`. -/
abbrev IsNoetherianAffineFreeChart (M : Modules.{u, m} B S hS F hF)
    (A : (smallEtaleRingedSite B S hS F hF).C) : Prop :=
  IsNoetherianAffineChart B S hS F A ∧
    SheafOfModules.IsFiniteFree
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over A)
        (M.over A)

/-- **Every étale chart of a locally Noetherian algebraic space is covered by charts which are
affine, have Noetherian ring of sections, and trivialize a given finite locally free module.**

The chart is first covered by trivializing charts, which is finite local freeness, and each of
those is then covered by Noetherian affine charts, which is
`AlgebraicGeometry.Space.exists_covering_through_noetherianAffine`; a Noetherian affine chart
over a trivializing chart is itself trivializing, by
`Stacks.SheafOfModules.isFiniteFree_over_of_le`.  The two steps are combined by transitivity of
the topology. -/
theorem exists_covering_through_noetherianAffineFree
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF) (hflf : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (W : (smallEtaleRingedSite B S hS F hF).C) :
    ∃ Sv : Sieve W, Sv ∈ (smallEtaleRingedSite B S hS F hF).J W ∧
      ∀ ⦃Y : (smallEtaleRingedSite B S hS F hF).C⦄ (h : Y ⟶ W), Sv h →
        ∃ (A : (smallEtaleRingedSite B S hS F hF).C) (l : Y ⟶ A) (mm : A ⟶ W),
          IsNoetherianAffineFreeChart M A ∧ h = l ≫ mm := by
  classical
  let Sv : Sieve W :=
    { arrows := fun Y h => ∃ (A : (smallEtaleRingedSite B S hS F hF).C) (l : Y ⟶ A) (mm : A ⟶ W),
        IsNoetherianAffineFreeChart M A ∧ h = l ≫ mm
      downward_closed := by
        rintro Y Z h ⟨A, l, mm, hA, rfl⟩ gg
        exact ⟨A, gg ≫ l, mm, hA, by simp⟩ }
  refine ⟨Sv, ?_, fun Y h hh => hh⟩
  obtain ⟨I, V, f, hcov, hfree⟩ := hflf W
  refine (smallEtaleRingedSite B S hS F hF).J.transitive hcov Sv ?_
  intro Z gz hgz
  obtain ⟨i, az, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hgz
  obtain ⟨Sz, hSz, hfac⟩ := exists_covering_through_noetherianAffine B S hS F hF Fact.out Z
  refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_ hSz
  intro Y k hk
  obtain ⟨A, l, mm, hA, hleft⟩ := hfac k hk
  refine ⟨A, l, mm ≫ (az ≫ f i),
    ⟨hA, Stacks.SheafOfModules.isFiniteFree_over_of_le (mm ≫ az) (hfree i)⟩, ?_⟩
  rw [hleft]
  exact Category.assoc _ _ _

/-- **A finite locally free module on a locally Noetherian algebraic space is coherent on the
small étale ringed site.**  This is the coherence-on-the-site half of the last assertion of
Stacks 07UB, at an arbitrary module universe and with no hypothesis beyond the two the source
makes.

Descent, Proposition 03DX(2) is *not* used: the relations clause
`AlgebraicGeometry.Space.isCoherentOnSite_of_isCartesian` needs the base change property of the
sections only between the charts of the covering, and the covering produced by
`AlgebraicGeometry.Space.exists_covering_through_noetherianAffineFree` consists of charts
trivializing `M`, where
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isFiniteFree_over` supplies it. -/
theorem isCoherentOnSite_of_isFiniteLocallyFreeOnSite
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF) (hflf : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    SheafOfModules.IsCoherentOnSite M :=
  isCoherentOnSite_of_isCartesian B S hS F hF M (IsNoetherianAffineFreeChart M)
    (exists_covering_through_noetherianAffineFree M hflf)
    (fun _ hA => hA.1.1) (fun _ hA => hA.1.2)
    (fun _ _ hA _ ff => bijective_sectionsBaseChange_of_isFiniteFree_over hA.2 ff)
    (isFiniteType_of_isFiniteLocallyFreeOnSite M hflf)

/-- **A finite locally free module on a locally Noetherian algebraic space is coherent.**  This
is the last assertion of Stacks 07UB for a finite locally free module, at an arbitrary module
universe, as the source has it.

`AlgebraicGeometry.Space.IsCoherent` is quasi-coherence together with coherence on the site.
Quasi-coherence is `SheafOfModules.isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite` and does
not use local Noetherianity; coherence on the site is
`AlgebraicGeometry.Space.isCoherentOnSite_of_isFiniteLocallyFreeOnSite`, and that is where local
Noetherianity enters. -/
theorem isCoherent_of_isFiniteLocallyFreeOnSite
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF) (hflf : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    IsCoherent B S hS F hF M :=
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hflf
  { __ := SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite M
    __ := isCoherentOnSite_of_isFiniteLocallyFreeOnSite M hflf }

/-- **Stacks 07UB, finite locally free modules.**  A finite locally free module on a locally
Noetherian algebraic space is coherent, as an instance.

This is `AlgebraicGeometry.Space.isCoherent_of_isFiniteLocallyFreeOnSite` with finite local
freeness supplied by instance search through `Fact`, which is how the predicate — an `abbrev`
and not a class — can be an instance hypothesis.  The same wrapping is used by the locally
Noetherian hypothesis of `AlgebraicGeometry.Space.isCoherent_structureSheaf`. -/
@[stacks 07UB "finite locally free modules"]
instance isCoherent_of_fact_isFiniteLocallyFreeOnSite
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF)
    [Fact (SheafOfModules.IsFiniteLocallyFreeOnSite M)] :
    IsCoherent B S hS F hF M :=
  isCoherent_of_isFiniteLocallyFreeOnSite M Fact.out

end AlgebraicGeometry.Space

end
