module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.Algebraization

/-!
# Shrinking an open to the finite free locus of an algebraizing module

Fix an algebraization situation, so that `U` is an open of the affine Noetherian scheme
`X = Spec A`, and let `(F_n)` be a coherent `I`-adic system on `U`. Suppose a coherent module `G`
on an open `V ⊆ U` has `(F_n)|_V` as its adic completion, and suppose `G` is free at every point
of a subset `T ⊆ V`. This file shows that `V` may be shrunk to an open `V'` with `T ⊆ V' ⊆ V` on
which the restriction of `G` is finite locally free and still has `(F_n)|_{V'}` as its completion.

Nothing new happens at the level of mathematics: on a locally Noetherian scheme a coherent module
with a free stalk at a point is finite free on a neighbourhood of that point, so the union of
those neighbourhoods over the points of `T` is an open on which the module is finite locally free,
and both the finite local freeness and the identification of the completion are inherited by any
further restriction. The only content is the bookkeeping of the restrictions: finite local
freeness is a pointwise condition, so no global cover is needed, and the completion is carried
along by the fact that it commutes with restriction to a smaller open.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteLocallyFree_restrict_of_free_stalks` — a
  coherent module on a locally Noetherian scheme which is free at every point of a set is finite
  locally free after restriction to some open neighbourhood of that set.
* `Stacks.Algebraization.exists_isFiniteLocallyFree_completion_of_free_stalks` — a coherent module
  whose completion is a given coherent adic system, and which is free at every point of a subset
  of its domain, may be restricted to a smaller open containing that subset on which it becomes
  finite locally free and still computes the same completion.

## References

* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0EIK](https://stacks.math.columbia.edu/tag/0EIK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A coherent module free at every point of a set is finite locally free on an open
neighbourhood of that set.** Over a locally Noetherian scheme a free stalk spreads out to a
finite free trivialisation on an open neighbourhood of the point, by
`AlgebraicGeometry.Scheme.Modules.exists_free_restrict_of_free_stalk`; the union of those
neighbourhoods over the points of the set is the required open, and the trivialisations restrict
to it because finite local freeness is a pointwise condition. -/
theorem exists_isFiniteLocallyFree_restrict_of_free_stalks {X : Scheme.{u}}
    [IsLocallyNoetherian X] (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M)
    (T : Set X)
    (hfree : ∀ x ∈ T, Module.Free (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M)) :
    ∃ W : X.Opens, T ⊆ (W : Set X) ∧ IsFiniteLocallyFree (M.restrict W.ι) := by
  classical
  choose W hmemW r hfreeW using fun x : T =>
    exists_free_restrict_of_free_stalk M hM x.1 (hfree x.1 x.2)
  have key : ∀ Wsup : X.Opens, (∀ z : Wsup.toScheme, ∃ x : T, z.1 ∈ W x) →
      IsFiniteLocallyFree (M.restrict Wsup.ι) := by
    intro Wsup hcov z
    obtain ⟨x, hx⟩ := hcov z
    refine ⟨Wsup.ι ⁻¹ᵁ W x, hx, ULift.{u} (Fin (r x)), inferInstance, ⟨?_⟩⟩
    exact ((restrictFunctorComp (Wsup.ι ⁻¹ᵁ W x).ι Wsup.ι).app M).symm ≪≫
      ((restrictFunctorCongr (morphismRestrict_ι Wsup.ι (W x))).app M).symm ≪≫
      (restrictFunctorComp (Wsup.ι ∣_ W x) (W x).ι).app M ≪≫
      (restrictFunctor (Wsup.ι ∣_ W x)).mapIso (hfreeW x).some ≪≫
      (restrictFreeIso (Wsup.ι ∣_ W x) _).symm
  exact ⟨⨆ x : T, W x, fun t ht => Opens.mem_iSup.mpr ⟨⟨t, ht⟩, hmemW ⟨t, ht⟩⟩,
    key _ fun z => Opens.mem_iSup.mp z.2⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Algebraization

/-- **The open on which a coherent module algebraizes a coherent adic system may be shrunk to the
finite free locus.** Let `(F_n)` be a coherent `I 𝒪_U`-adic system on the open `U` of an
algebraization situation, let `G` be a coherent module on an open `V ⊆ U` whose adic completion is
`(F_n)|_V`, and suppose `G` is free at every point of a subset `T ⊆ V`. Then there is an open `V'`
with `T ⊆ V' ⊆ V` such that the restriction of `G` to `V'` is finite locally free and its adic
completion is `(F_n)|_{V'}`.

The open `V'` is the image in `U` of the open neighbourhood of `T` produced by
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteLocallyFree_restrict_of_free_stalks`, and the
completion is transported along the inclusion `V' ⟶ V` by
`Stacks.Algebraization.completionRestrictOpenIso`. -/
theorem exists_isFiniteLocallyFree_completion_of_free_stalks
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (V : S.U.toScheme.Opens)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf)
    (e : ((completionFunctor V.toScheme ((idealOnOpen S).comap V.ι)).obj G).obj ≅
          F.obj ⋙ AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι)
    (T : Set S.U.toScheme) (hTV : T ⊆ (V : Set S.U.toScheme))
    (hfreeT : ∀ y : V.toScheme, V.ι.base y ∈ T →
      Module.Free (V.toScheme.presheaf.stalk y)
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor V.toScheme y).obj G.obj)) :
    ∃ V' : S.U.toScheme.Opens, T ⊆ (V' : Set S.U.toScheme) ∧ V' ≤ V ∧
      ∃ G' : AlgebraicGeometry.SheafOfModules.CoherentModules V'.toScheme.ringCatSheaf,
        AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G'.obj ∧
        Nonempty (((completionFunctor V'.toScheme ((idealOnOpen S).comap V'.ι)).obj G').obj ≅
          F.obj ⋙ AlgebraicGeometry.Scheme.Modules.restrictFunctor V'.ι) := by
  obtain ⟨W, hTW, hWflf⟩ :=
    Scheme.Modules.exists_isFiniteLocallyFree_restrict_of_free_stalks G.obj G.property
      (V.ι.base ⁻¹' T) hfreeT
  have hV'V : V.ι ''ᵁ W ≤ V := by
    have h1 : V.ι ''ᵁ W ≤ V.ι ''ᵁ (⊤ : V.toScheme.Opens) := V.ι.image_mono le_top
    rwa [V.ι_image_top] at h1
  have hρι : S.U.toScheme.homOfLE hV'V ≫ V.ι = (V.ι ''ᵁ W).ι :=
    S.U.toScheme.homOfLE_ι hV'V
  have hψ : (V.ι.isoImage W).inv ≫ W.ι = S.U.toScheme.homOfLE hV'V := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.isoImage_inv_ι, hρι]
  have hideal : ((idealOnOpen S).comap V.ι).comap (S.U.toScheme.homOfLE hV'V) =
      (idealOnOpen S).comap (V.ι ''ᵁ W).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hρι]
  refine ⟨V.ι ''ᵁ W, ?_, hV'V,
    restrictCoherentModules (S.U.toScheme.homOfLE hV'V) G, ?_, ⟨?_⟩⟩
  · exact fun t ht => ⟨⟨t, hTV ht⟩, hTW ht, rfl⟩
  · refine Scheme.Modules.IsFiniteLocallyFree.of_iso ?_
      (hWflf.restrict (V.ι.isoImage W).inv)
    exact ((Scheme.Modules.restrictFunctorComp (V.ι.isoImage W).inv W.ι).app G.obj).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hψ).app G.obj
  · rw [← hideal]
    exact (completionRestrictOpenIso (S.U.toScheme.homOfLE hV'V)
        ((idealOnOpen S).comap V.ι) G).symm ≪≫
      Functor.isoWhiskerRight e
        (Scheme.Modules.restrictFunctor (S.U.toScheme.homOfLE hV'V)) ≪≫
      Functor.isoWhiskerLeft F.obj
        ((Scheme.Modules.restrictFunctorComp (S.U.toScheme.homOfLE hV'V) V.ι).symm ≪≫
          Scheme.Modules.restrictFunctorCongr hρι)

end Stacks.Algebraization

end
