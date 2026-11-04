module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# A biproduct of finite locally free modules on a site is finite locally free

Let `R` be a sheaf of rings on a site `C`.  If two sheaves of `R`-modules are finite locally
free in the sense of Stacks 03DL (2), then so is their biproduct: on an object of the site,
refine a trivializing covering family for the first module by trivializing covering families for
the second, and over a member of the refinement take the disjoint union of the two free bases.

## Main results

* `CategoryTheory.Sieve.ofArrows_sigma_comp_mem`: covering families compose — a family of
  covering families of the members of a covering family generates, after composing the arrows, a
  covering family.
* `Stacks.SheafOfModules.isColimitCofanBiprod`: a biproduct of two finite coproducts of copies
  of one object is a finite coproduct of copies of it, of the sum of the two ranks.
* `Stacks.SheafOfModules.isFiniteFree_biprod`: a biproduct of two finite free sheaves of modules
  is finite free, which is Stacks 03DE (2) for a biproduct.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biprod`: **a biproduct of two finite locally
  free sheaves of modules on a site is finite locally free**, which is Stacks 03DL (2) for a
  biproduct.

## Implementation notes

`SheafOfModules.IsFiniteLocallyFreeOnSite` and `SheafOfModules.IsFiniteFree` are phrased by
colimiting cofans of copies of the structure sheaf, so nothing here needs a sheafification
instance, and the refinement of covering families is carried out on sieves rather than on slice
sites.

The module universe is the universe of the coefficient ring.  That is the shape in which
`SheafOfModules.isFiniteFree_iff_exists_isColimit` collapses the finite free model of Stacks
03DE (2) onto the module itself, which is what turns the statement about biproducts into one
about colimiting cofans and keeps the argument categorical: no sections of a biproduct are
computed anywhere.  At a module universe independent of the ring universe the finite free model
of the biproduct would have to be compared with the biproduct sectionwise, which is a different
argument.

The restriction of the biproduct to a slice is the biproduct of the restrictions because
`SheafOfModules.overFunctor` is additive (`SheafOfModules.overFunctor_additive`), hence preserves
binary biproducts.  That comparison is formed inline rather than named:
`Stacks.SheafOfModules.overBiprodIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryBiprod` already names
it, under sheafification hypotheses that this file does not need.

Existence of the biproduct is an instance hypothesis, as it is for
`Stacks.SheafOfModules.isFinitePresentation_biprod`; existence of the biproducts of the
restrictions is then supplied by the preservation instance.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Sieve

/-- **Covering families compose.**  If `V i ⟶ U` is a covering family of `U` and, for each `i`,
`W i j ⟶ V i` is a covering family of `V i`, then the composites `W i j ⟶ V i ⟶ U` form a
covering family of `U`. -/
theorem ofArrows_sigma_comp_mem {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {U : C} {I : Type*} {V : I → C} {f : ∀ i, V i ⟶ U} (hf : Sieve.ofArrows V f ∈ J U)
    {I' : I → Type*} {W : ∀ i, I' i → C} {g : ∀ i j, W i j ⟶ V i}
    (hg : ∀ i, Sieve.ofArrows (W i) (g i) ∈ J (V i)) :
    Sieve.ofArrows (fun p : Σ i, I' i => W p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1) ∈ J U := by
  refine J.transitive hf _ ?_
  rintro Z h ⟨T, a, b, ⟨i⟩, rfl⟩
  refine J.superset_covering ?_ (J.pullback_stable a (hg i))
  rintro Y c ⟨T', d, e, ⟨j⟩, hde⟩
  exact ⟨W i j, d, g i j ≫ f i,
    ⟨(⟨i, j⟩ : Σ i, I' i)⟩, by rw [← Category.assoc, hde, Category.assoc]⟩

end CategoryTheory.Sieve

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A biproduct of two finite coproducts of copies of one object is again one**, of the sum of
the two ranks: the legs are the legs of the two cofans followed by the two inclusions of the
biproduct, reindexed along `Fin.addCases`. -/
noncomputable def isColimitCofanBiprod {D : Type*} [Category D] [Preadditive D] {E A B : D}
    [HasBinaryBiproduct A B] {n m : ℕ} (ι : ∀ _ : Fin n, E ⟶ A) (κ : ∀ _ : Fin m, E ⟶ B)
    (hA : IsColimit (Cofan.mk A ι)) (hB : IsColimit (Cofan.mk B κ)) :
    IsColimit (Cofan.mk (f := fun _ : Fin (n + m) => E) (A ⊞ B)
      (Fin.addCases (motive := fun _ => E ⟶ A ⊞ B)
        (fun i => ι i ≫ biprod.inl) (fun j => κ j ≫ biprod.inr))) := by
  refine Cofan.IsColimit.mk _
    (fun t => biprod.desc (Cofan.IsColimit.desc hA fun i => t.inj (Fin.castAdd m i))
      (Cofan.IsColimit.desc hB fun j => t.inj (Fin.natAdd n j))) (fun t k => ?_) (fun t p hp => ?_)
  · induction k using Fin.addCases with
    | left i =>
      simp only [cofan_mk_inj, Fin.addCases_left, Category.assoc, biprod.inl_desc]
      exact Cofan.IsColimit.fac hA _ i
    | right j =>
      simp only [cofan_mk_inj, Fin.addCases_right, Category.assoc, biprod.inr_desc]
      exact Cofan.IsColimit.fac hB _ j
  · refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc]
      refine Cofan.IsColimit.hom_ext hA _ _ fun i => ?_
      have hfac := Cofan.IsColimit.fac hA (fun i => t.inj (Fin.castAdd m i)) i
      have hleg := hp (Fin.castAdd m i)
      simp only [cofan_mk_inj, Fin.addCases_left] at hleg hfac
      rw [← Category.assoc]
      simp only [cofan_mk_inj]
      rw [hleg, hfac]
    · rw [biprod.inr_desc]
      refine Cofan.IsColimit.hom_ext hB _ _ fun j => ?_
      have hfac := Cofan.IsColimit.fac hB (fun j => t.inj (Fin.natAdd n j)) j
      have hleg := hp (Fin.natAdd n j)
      simp only [cofan_mk_inj, Fin.addCases_right] at hleg hfac
      rw [← Category.assoc]
      simp only [cofan_mk_inj]
      rw [hleg, hfac]

/-- **A biproduct of two finite free sheaves of modules is finite free.**  This is Stacks
03DE (2) for a biproduct; the rank of the biproduct is the sum of the two ranks. -/
theorem isFiniteFree_biprod {R : Sheaf J RingCat.{w}} (A B : _root_.SheafOfModules.{w} R)
    [HasBinaryBiproduct A B]
    (hA : _root_.SheafOfModules.IsFiniteFree R A)
    (hB : _root_.SheafOfModules.IsFiniteFree R B) :
    _root_.SheafOfModules.IsFiniteFree R (A ⊞ B) := by
  rw [_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit] at hA hB ⊢
  obtain ⟨n, ι, ⟨hcA⟩⟩ := hA
  obtain ⟨m, κ, ⟨hcB⟩⟩ := hB
  exact ⟨n + m, _, ⟨isColimitCofanBiprod ι κ hcA hcB⟩⟩

/-- **Stacks 03DL (2) for a biproduct.**  A biproduct of two finite locally free sheaves of
modules on a site is finite locally free.

On an object `U` of the site, a trivializing covering family `V i ⟶ U` for `A` is refined by
trivializing covering families `W i j ⟶ V i` for `B`; the composites cover `U` by
`CategoryTheory.Sieve.ofArrows_sigma_comp_mem`, over each of them both restrictions are finite
free — that of `A` by `Stacks.SheafOfModules.exists_isColimitCofan_over_of_le` — their biproduct
is finite free by `Stacks.SheafOfModules.isFiniteFree_biprod`, and it is the restriction of the
biproduct because restriction to a slice is additive. -/
theorem isFiniteLocallyFreeOnSite_biprod {R : Sheaf J RingCat.{w}}
    (A B : _root_.SheafOfModules.{w} R) [HasBinaryBiproduct A B]
    (hA : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite A)
    (hB : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite B) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (A ⊞ B) := fun U => by
  obtain ⟨I, V, f, hf, hAV⟩ := hA U
  choose I' W g hg hBW using fun i => hB (V i)
  refine ⟨Σ i, I' i, fun p => W p.1 p.2, fun p => g p.1 p.2 ≫ f p.1,
    Sieve.ofArrows_sigma_comp_mem J hf hg, fun p => ?_⟩
  have hAW : _root_.SheafOfModules.IsFiniteFree (R.over (W p.1 p.2)) (A.over (W p.1 p.2)) :=
    (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).mpr
      (exists_isColimitCofan_over_of_le A (g p.1 p.2)
        ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).mp (hAV p.1)))
  have := preservesBinaryBiproduct_of_preservesBiproduct
    (_root_.SheafOfModules.overFunctor R (W p.1 p.2)) A B
  exact Intrinsic.isFiniteFree_of_iso
    ((_root_.SheafOfModules.overFunctor R (W p.1 p.2)).mapBiprod A B).symm
    (isFiniteFree_biprod _ _ hAW (hBW p.1 p.2))

end Stacks.SheafOfModules

end
