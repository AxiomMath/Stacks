module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictPullback
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTrivialisedHom
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycle
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycleOfOverlap

/-!
# Glueing a finite locally free `colim_F 𝒪_X`-module from transition matrices

The last step of the essential surjectivity half of [Stacks, Tag 0EXD] is a Zariski glueing: the
local solutions produced over the members of a cover of the base — each of them a *free* module,
since the local case of the tag is `ℱ = 𝒪_Z^{⊕r}` and `𝒢` is free over the preimage of a
neighbourhood of the centre — have to be assembled into one finite locally free module over
`colim_F 𝒪_X`.

`Stacks.SheafOfModules.MatrixCocycle` glues exactly such data, and it is stated over an
*arbitrary* sheaf of rings on a topological space, so it applies verbatim to
`AlgebraicGeometry.frobeniusColimitRingSheaf`: no new glueing machine is needed. What this file
adds is the output in the two forms the comparison functor of the tag speaks — an object of
`AlgebraicGeometry.frobeniusColimitVectorBundles`, and the identification of each chart with a
free module **in the transition-functor spelling**, which is the spelling in which the square of
[Stacks, Example 0EVH] over a localisation `A_g` presents the restriction to `D(g)`.

## Main results

* `Stacks.SheafOfModules.nonempty_over_iso_free_of_combSections_bijective`: **a sheaf of modules
  trivialised by a finite family of sections over `U` is free over `U`**, as a sheaf of modules on
  the slice site and not merely sectionwise. This is
  `Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj` with its two hypotheses read off
  from bijectivity of the combination map.
* `AlgebraicGeometry.exists_frobeniusColimitVectorBundle_of_matrixCocycle`: **a matrix cocycle
  over a cover of `X` glues to a finite locally free `colim_F 𝒪_X`-module whose transition to
  each member of the cover is free** of the prescribed rank.
* `AlgebraicGeometry.exists_frobeniusColimitVectorBundle_of_overlap`: the same, with the glueing
  data given as **isomorphisms of the free charts over the overlaps** rather than as matrices,
  which is the form fullness of the comparison functor of [Stacks, Tag 0EXD] over an overlap
  produces.

## Implementation notes

The chart identification is given in the transition-functor spelling rather than as an
isomorphism over the slice site, because that is what the comparison functor consumes and because
the crossing between the two is already available as
`AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso`. Going the other way would require a
chart isomorphism of `Stacks.SheafOfModules.OModuleGlueData` as a morphism of sheaves of modules
over the slice site, which that development only has sectionwise
(`Stacks.SheafOfModules.OModuleGlueData.chartIso`); with free charts the sectionwise form suffices,
since a trivialisation by sections already produces the slice-level isomorphism.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius Stacks.SheafOfModules

universe u

namespace Stacks.SheafOfModules

/-- **A sheaf of modules trivialised by a finite family of sections over `U` is free over `U`.**
The combination map being bijective over every smaller open gives both hypotheses of
`Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj`: injectivity directly, and local
surjectivity at the open itself. -/
theorem nonempty_over_iso_free_of_combSections_bijective {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
    (M : _root_.SheafOfModules.{u} R) {U : Opens X} {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U)))
    (hbij : ∀ ⦃V : Opens X⦄ (f : V ⟶ U), Function.Bijective (combSections M s f)) :
    Nonempty (M.over U ≅ _root_.SheafOfModules.free (R := R.over U) ι) := by
  refine nonempty_over_iso_free_of_inj_of_surj M s (fun V f => (hbij f).1) fun V f t y hy => ?_
  obtain ⟨c, hc⟩ := (hbij f).2 t
  refine ⟨V, 𝟙 V, hy, c, ?_⟩
  rw [res_id, Category.id_comp]
  exact hc.symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **A matrix cocycle over a cover of `X` glues to a finite locally free `colim_F 𝒪_X`-module
whose transition to each member of the cover is free** of the prescribed rank.

The module is `Stacks.SheafOfModules.MatrixCocycle.glued`, finite locally free by
`Stacks.SheafOfModules.MatrixCocycle.isFiniteLocallyFree_glued`; its basis sections over a member
of the cover trivialise it there
(`Stacks.SheafOfModules.MatrixCocycle.bijective_combSections_basis`), which makes it free over
that member on the slice site, and
`AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso` carries that to the transition-functor
spelling. -/
theorem exists_frobeniusColimitVectorBundle_of_matrixCocycle {K : Type u} (V : K → X.Opens)
    (hV : ⨆ k, V k = ⊤) (m : K → ℕ)
    (D : MatrixCocycle (frobeniusColimitRingSheaf X p hX) V m) :
    ∃ N : frobeniusColimitVectorBundles X p hX, ∀ k : K,
      Nonempty ((frobeniusColimitVectorBundlesPullback p (V k).ι
            (isInCharacteristic_toScheme hX (V k)) hX).obj N ≅
          ⟨_root_.SheafOfModules.free (ULift.{u} (Fin (m k))),
            isFiniteLocallyFreeFrobeniusColimitFree p (isInCharacteristic_toScheme hX (V k))
              (ULift.{u} (Fin (m k)))⟩) := by
  refine ⟨⟨D.glued, D.isFiniteLocallyFree_glued hV⟩, fun k => ?_⟩
  have hfree : Nonempty (D.glued.over (V k) ≅
      _root_.SheafOfModules.free (R := (frobeniusColimitRingSheaf X p hX).over (V k))
        (ULift.{u} (Fin (m k)))) :=
    nonempty_over_iso_free_of_combSections_bijective D.glued (D.basis k) fun W f => by
      rw [combSections_hom_eq D.glued (D.basis k) f (homOfLE (leOfHom f))]
      exact D.bijective_combSections_basis k (leOfHom f)
  exact ⟨ObjectProperty.isoMk _ (frobeniusColimitPullbackObjFreeOfIso X p hX (V k)
    (isInCharacteristic_toScheme hX (V k)) D.glued (ULift.{u} (Fin (m k))) hfree.some)⟩

/-- **A family of comparisons of the free charts over the overlaps glues to a finite locally free
`colim_F 𝒪_X`-module whose transition to each member of the cover is free** of the prescribed
rank.

This is `AlgebraicGeometry.exists_frobeniusColimitVectorBundle_of_matrixCocycle` fed the matrix
cocycle `Stacks.SheafOfModules.matrixCocycleOfOverlap` of the family, and it is the form the
Zariski glueing of [Stacks, Tag 0EXD] produces its data in: fullness of the comparison functor
over the overlap of two members of the cover gives an isomorphism of the two local free
solutions, not a matrix. -/
theorem exists_frobeniusColimitVectorBundle_of_overlap {K : Type u} (V : K → X.Opens)
    (hV : ⨆ k, V k = ⊤) (m : K → ℕ)
    (φ : ∀ k l : K,
      (MatrixCocycle.chart (O := frobeniusColimitRingSheaf X p hX) (m := m) k).over
          (V k ⊓ V l) ⟶
        (MatrixCocycle.chart (O := frobeniusColimitRingSheaf X p hX) (m := m) l).over
          (V k ⊓ V l))
    (hid : ∀ k : K, φ k k = 𝟙 _)
    (hcomp : ∀ (k l j : K) ⦃W : X.Opens⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j)
      (x : ToType ((MatrixCocycle.chart (O := frobeniusColimitRingSheaf X p hX)
        (m := m) k).val.obj (op W))),
      overlapApp V m φ l j hl hj (overlapApp V m φ k l hk hl x)
        = overlapApp V m φ k j hk hj x) :
    ∃ N : frobeniusColimitVectorBundles X p hX, ∀ k : K,
      Nonempty ((frobeniusColimitVectorBundlesPullback p (V k).ι
            (isInCharacteristic_toScheme hX (V k)) hX).obj N ≅
          ⟨_root_.SheafOfModules.free (ULift.{u} (Fin (m k))),
            isFiniteLocallyFreeFrobeniusColimitFree p (isInCharacteristic_toScheme hX (V k))
              (ULift.{u} (Fin (m k)))⟩) :=
  exists_frobeniusColimitVectorBundle_of_matrixCocycle X p hX V hV m
    (matrixCocycleOfOverlap V m φ hid hcomp)

end AlgebraicGeometry

end
