module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeEdge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineHigherDirectImageSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.LerayVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DenseOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSupportRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale cohomology of a scheme of finite type over a field vanishes above twice its dimension

Let `K` be a field and `X` a quasi-compact scheme locally of finite type over `K`, of dimension at
most `n`. Then `H^b_ét(X, 𝓕) = 0` for every abelian torsion sheaf `𝓕` on `X_ét` and every
`b > 2n + cd(K)`, so `cd(X) ≤ 2 dim(X) + cd(K)`. No separatedness is assumed.

For affine `X` the sharper bound `cd(X) ≤ dim(X) + cd(K)` is Stacks 0F0V; this file deduces the
general bound from it by induction on `n`, with the results of the source on the supports of
higher direct images (Stacks 0F0X) as the inductive engine.

## The proof

Choose an affine open `U ⊆ X` containing every generic point of `X` whose inclusion `j : U ⟶ X`
is an affine morphism (`AlgebraicGeometry.exists_isAffineOpen_isAffineHom_genericPoints`: inside
each irreducible component take an affine open avoiding the other components and contained in
every member of a finite affine cover of `X` through the generic point; the union is affine, and
its intersection with each member of the cover is a union of some of the pieces). Every point
outside `U` is a proper specialization of a generic point, so its residue field has transcendence
degree at most `n - 1` over `K`.

Write `G = j⁻¹𝓕` and `c : 𝓕 ⟶ j_*G` for the unit. Its kernel and the cokernel of its coimage
factorization vanish on `U`, so they are supported in transcendence degree `≤ n - 1`; by the
induction hypothesis (through the reduction of Stacks 0F0W to closed subschemes,
`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_finiteTypeBound`) their
cohomology vanishes above `2(n - 1) + cd(K)`. It remains to see `H^b(X, j_*G) = 0`. The bottom
edge of the Leray spectral sequence of `j`
(`Stacks.EtaleCohomology.LerayVanishing.subsingleton_sheafH_directImage_of_forall`) reduces this
to `H^b(U, G) = 0`, which is Stacks 0F0V for the affine `U`, and to
`H^{b-1-q}(X, R^qj_*G) = 0` for `q ≥ 1`. Since `j` is affine, Stacks 0F0X places the support of
`R^qj_*G` in transcendence degree `≤ n - q`, and the induction hypothesis applies once more.

## Main results

* `Stacks.EtaleCohomology.LerayVanishing.subsingleton_sheafH_directImage_of_forall`: the bottom
  edge of the Leray spectral sequence, as a vanishing criterion for `H^n(Y, f_*𝓕)`.
* `AlgebraicGeometry.exists_isAffineOpen_isAffineHom_genericPoints`: a Noetherian scheme has an
  affine open containing all its generic points whose inclusion is an affine morphism.
* `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_finiteTypeBound`: the
  reduction of Stacks 0F0W, for an arbitrary quasi-compact `X` and an arbitrary bound.
* `AlgebraicGeometry.subsingleton_H_of_topologicalKrullDim_le`: `H^b(X, 𝓕) = 0` for
  `b > 2n + cd(K)`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_two_mul_add`:
  `cd(X) ≤ 2n + cd(K)`.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [SGA 4, Exposé X, Corollaire 4.3]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

/-! ### The bottom edge of the Leray spectral sequence -/

namespace Stacks.EtaleCohomology.LerayVanishing

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

variable {X Y : Scheme.{u}}

/-- **The bottom edge of the Leray spectral sequence, as a vanishing criterion** (Stacks 0732).
For `f : X ⟶ Y` and an abelian sheaf `𝓕` on `X_étale`, `H^n(Y, f_*𝓕) = 0` as soon as
`H^n(X, 𝓕) = 0` and `H^{n-1-q}(Y, R^qf_*𝓕) = 0` for every `q` with `1 ≤ q ≤ n - 1`. -/
public theorem subsingleton_sheafH_directImage_of_forall (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (hX : Subsingleton (Sheaf.H.{u + 1, u + 1} F n))
    (h : ∀ q : ℕ, 1 ≤ q → q + 1 ≤ n → Subsingleton (Sheaf.H.{u + 1, u + 1}
      (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F) (n - 1 - q))) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, 0} f).obj F) n) := by
  have : (etaleAbelianDirectImage.{u, 0} f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
  have : (etaleAbelianDirectImage.{u, 0} f).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).isRightAdjoint
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}]
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}] at hX
  refine Stacks.CompositeDegreeVanishing.isZero_rightDerived_obj_map_of_isZero
    (etaleAbelianDirectImage.{u, 0} f) (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}) F n
    (hX.of_iso ((Functor.rightDerivedIsoOfNatIso
      (etaleAbelianDirectImageCompΓIso.{u, 0} f) n).app F)) fun q hq hqn => ?_
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    _ _ _).1 (h q hq hqn)

end Stacks.EtaleCohomology.LerayVanishing

/-! ### An affine open through the generic points with affine inclusion -/

namespace AlgebraicGeometry

/-- Every point of a quasi-sober space lies in the closure of a generic point of an irreducible
component. -/
theorem exists_mem_genericPoints_mem_closure {α : Type*} [TopologicalSpace α] [QuasiSober α]
    (x : α) : ∃ η ∈ genericPoints α, x ∈ closure {η} := by
  let c : irreducibleComponents α :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨(genericPoints.ofComponent c).1, (genericPoints.ofComponent c).2, ?_⟩
  rw [(genericPoints.isGenericPoint_ofComponent c).def]
  exact mem_irreducibleComponent

open scoped Function in
/-- **An affine open through all generic points, with affine inclusion.** A Noetherian scheme `X`
has an affine open `U` containing every generic point of `X` such that the inclusion
`U ⟶ X` is an affine morphism.

Inside the irreducible component of each generic point `η` choose an affine open neighbourhood
`A_η` of `η` avoiding the other irreducible components and contained in every member through `η`
of a finite affine open cover of `X`. The `A_η` are pairwise disjoint, so their union `U` is
affine; and the intersection of `U` with a member `W` of the cover is the union of the `A_η`
with `η ∈ W`, the others being disjoint from `W`, so it is affine too. -/
theorem exists_isAffineOpen_isAffineHom_genericPoints (X : Scheme.{u}) [IsNoetherian X] :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoints X ⊆ U ∧ IsAffineHom U.ι := by
  classical
  have hG : (genericPoints X).Finite :=
    genericPoints.finite (finite_irreducibleComponents_of_isNoetherian (X := X))
  -- a finite affine open cover
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => (V : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
      exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩)
  -- the open set `O_η` in which `A_η` is chosen
  let N : X → Set X := fun η => (⋃ η' ∈ hG.toFinset.erase η, closure {η'})ᶜ
  let O : X → Set X := fun η => N η ∩ ⋂ V ∈ s.filter (fun V : X.affineOpens => η ∈ (V : X.Opens)),
    ((V : X.Opens) : Set X)
  have hO : ∀ η, IsOpen (O η) := fun η =>
    (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl.inter
      (isOpen_biInter_finset fun V _ => (V : X.Opens).isOpen)
  have hηO : ∀ η ∈ genericPoints X, η ∈ O η := by
    intro η hη
    refine ⟨?_, Set.mem_iInter₂.2 fun V hV => (Finset.mem_filter.1 hV).2⟩
    simp only [N, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_erase, Set.Finite.mem_toFinset,
      not_exists]
    intro η' ⟨hne, hη'⟩ hcl
    -- `η ∈ closure {η'}` forces the components to agree
    have h1 : closure {η} ⊆ closure {η'} :=
      closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure
    have h2 : closure {η} = closure {η'} :=
      le_antisymm h1 (hη.2 isIrreducible_singleton.closure h1)
    exact hne (inseparable_iff_closure_eq.mpr h2).eq.symm
  choose! A hA hηA hAO using fun η (hη : η ∈ genericPoints X) =>
    exists_isAffineOpen_mem_and_subset (U := ⟨O η, hO η⟩) (hηO η hη)
  -- every point of `A_η` lies in the closure of `η`
  have hAcl : ∀ η ∈ genericPoints X, ∀ y ∈ A η, y ∈ closure {η} := by
    intro η hη y hy
    obtain ⟨ξ, hξ, hyξ⟩ := exists_mem_genericPoints_mem_closure y
    by_cases hξη : ξ = η
    · exact hξη ▸ hyξ
    · exfalso
      have := (hAO η hη hy).1
      simp only [N, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_erase,
        Set.Finite.mem_toFinset] at this
      exact this ⟨ξ, ⟨hξη, hξ⟩, hyξ⟩
  have hdisj : (genericPoints X).Pairwise (Disjoint on A) := by
    intro η hη η' hη' hne
    change Disjoint (A η) (A η')
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    ext y
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hy hy'
    have h2 := hAcl η' hη' y hy'
    have hη'A : η' ∈ A η := (specializes_iff_mem_closure.2 h2).mem_open (A η).isOpen hy
    have := (hAO η hη hη'A).1
    simp only [N, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_erase,
      Set.Finite.mem_toFinset] at this
    exact this ⟨η', ⟨hne.symm, hη'⟩, subset_closure rfl⟩
  refine ⟨⨆ η ∈ genericPoints X, A η, IsAffineOpen.biSup_of_disjoint hG hA hdisj, ?_, ?_⟩
  · exact fun η hη =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨η, TopologicalSpace.Opens.mem_iSup.2 ⟨hη, hηA η hη⟩⟩
  · refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨V, hVs, hxV⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    refine ⟨V, hxV, V.2, ?_⟩
    rw [← (Scheme.Opens.ι _).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    -- `U ⊓ V` is the union of the `A_η` with `η ∈ V`
    have hUV : (⨆ η ∈ genericPoints X, A η) ⊓ (V : X.Opens) =
        ⨆ η ∈ {η | η ∈ genericPoints X ∧ η ∈ (V : X.Opens)}, A η := by
      apply le_antisymm
      · rintro y ⟨hyU, hyV⟩
        obtain ⟨η, hη, hyη⟩ : ∃ η ∈ genericPoints X, y ∈ A η := by
          have hyU' : y ∈ (⨆ η ∈ genericPoints X, A η) := hyU
          simp only [TopologicalSpace.Opens.mem_iSup] at hyU'
          obtain ⟨η, hη, hyη⟩ := hyU'
          exact ⟨η, hη, hyη⟩
        have hηV : η ∈ (V : X.Opens) :=
          (specializes_iff_mem_closure.2 (hAcl η hη y hyη)).mem_open (V : X.Opens).isOpen hyV
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨η, TopologicalSpace.Opens.mem_iSup.2
          ⟨⟨hη, hηV⟩, hyη⟩⟩
      · refine iSup₂_le fun η hη => le_inf (le_iSup₂_of_le η hη.1 le_rfl) ?_
        exact fun y hy => Set.mem_iInter₂.1 (hAO η hη.1 hy).2 V (Finset.mem_filter.2 ⟨hVs, hη.2⟩)
    rw [hUV]
    exact IsAffineOpen.biSup_of_disjoint (hG.subset fun η hη => hη.1)
      (fun η hη => hA η hη.1) (hdisj.mono fun η hη => hη.1)

/-! ### Sheaves supported in bounded transcendence degree -/

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

/-- **Stacks 0F0W, for a quasi-compact scheme and an arbitrary bound.** Let `K` be a field, `X` a
quasi-compact scheme locally of finite type over `K`, `a` a natural number and `B ∈ ℕ∞` such that
every torsion abelian sheaf on every quasi-compact scheme `Z` locally of finite type over `K`
with `dim Z ≤ a` has vanishing cohomology above `B` (`hV`). Then every torsion abelian sheaf `𝓕`
on `X_ét` whose support is contained in the set `E_a` of points `x` with `trdeg_K κ(x) ≤ a` has
`H^b(X, 𝓕) = 0` for `b > B`.

The proof is that of `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_cdBound`,
which is the case of an affine `X` with `B = a + cd(K)`: `𝓕` is a filtered colimit of torsion
subsheaves supported on closed subsets of `E_a` (Stacks 0F0N), each of which is the direct image
from a reduced closed subscheme of dimension at most `a` (Stacks 04CA, 0A21), and cohomology
commutes with filtered colimits on the quasi-compact and quasi-separated scheme `X` (Stacks
03Q5). -/
theorem subsingleton_H_of_smallEtaleSupport_subset_of_finiteTypeBound (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [CompactSpace X] [LocallyOfFiniteType f] (a : ℕ)
    (B : ℕ∞)
    (hV : ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of K)) [CompactSpace Z] [LocallyOfFiniteType g],
      topologicalKrullDim Z ≤ a →
        ∀ G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1},
          Stacks.Torsion.torsionSheafProperty Z.smallEtaleTopology G →
            ∀ b : ℕ, B < b → Subsingleton (Sheaf.H.{u + 1, u + 1} G b))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : Stacks.EtaleCohomology.smallEtaleSupport F ⊆ Scheme.trdegLESet K f a)
    (b : ℕ) (hb : B < b) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F b) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  let E : Set X := Scheme.trdegLESet K f a
  have hE : StableUnderSpecialization E := Scheme.stableUnderSpecialization_trdegLESet K f a
  have hG := (smallEtaleSupport_subset_iff F E).1 hsupp
  obtain ⟨I, _, _, D, ι, ⟨hcolim⟩, hmonos, hD⟩ :=
    exists_isFilteredColimit_isClosed_support_smallEtale E hE F hG
  -- the cohomology of each term vanishes
  have hterm : ∀ i, IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      b).obj (D.obj i)) := by
    intro i
    obtain ⟨W, hW, hWE, hWsupp⟩ := hD i
    have hmono : Mono (ι.app i) := hmonos i
    let J := Scheme.IdealSheafData.vanishingIdeal (⟨W, hW⟩ : TopologicalSpace.Closeds X)
    let i₀ : J.subscheme ⟶ X := J.subschemeι
    have hrange : Set.range i₀ = W := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hunit := isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk i₀ (D.obj i)
      (fun s hs => hWsupp s (by rwa [hrange] at hs))
    let H := (smallEtalePullbackAb i₀).obj (D.obj i)
    have hH : Stacks.Torsion.torsionSheafProperty J.subscheme.smallEtaleTopology H :=
      Stacks.Torsion.torsionSheafProperty_of_iso _
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage i₀).app (D.obj i)).symm
        (torsionSheafProperty_etaleAbelianInverseImage.{u, u + 1} i₀ (D.obj i)
          ((Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).prop_of_mono (ι.app i) hF))
    have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace i₀
    -- the closed subscheme has dimension at most `a`
    have hdim : topologicalKrullDim J.subscheme ≤ a := by
      rw [topologicalKrullDim_eq_iSup_trdeg_residueField K J.subscheme (i₀ ≫ f)]
      refine iSup_le fun z => ?_
      have htr := trdeg_residueField_of_surjectiveOnStalks K f i₀ z.1
      have hz : i₀ z.1 ∈ E := hWE (hrange ▸ ⟨z.1, rfl⟩)
      simp only [E, Scheme.trdegLESet, Set.mem_ofPred_eq] at hz
      rw [htr] at hz
      exact_mod_cast Cardinal.toENat_le_natCast.2 hz
    have h2 : Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePushforwardAb i₀).obj H) b) :=
      (Equiv.ofBijective _ (etaleCohomologyDirectImageMap_bijective.{u, 0, u + 1} i₀ H b)
        ).subsingleton_congr.2 (hV J.subscheme (i₀ ≫ f) hdim H hH b hb)
    exact ((Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
      _ _ _).1 h2).of_iso (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
        b).mapIso (asIso ((smallEtaleAdjunctionAb i₀).unit.app (D.obj i))))
  -- cohomology commutes with filtered colimits (Stacks 03Q5)
  have h03Q5 := Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale.{0, u} X b D
  have hzero : IsZero (colimit (D ⋙ (Sheaf.Γ X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerived b)) :=
    (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext fun i => (hterm i).eq_of_src _ _)
  have hF' : IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b).obj
      F) :=
    (hzero.of_iso (asIso (colimit.post D
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b))).symm).of_iso
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b).mapIso
        (hcolim.coconePointUniqueUpToIso (colimit.isColimit D)))
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    _ _ _).2 hF'

/-! ### Supports and the open `U` -/

/-- `Ext` into a zero object vanishes. -/
theorem _root_.CategoryTheory.Abelian.Ext.subsingleton_of_isZero {C : Type*} [Category* C]
    [Abelian C] [HasExt.{w} C] (X : C) {Y : C} (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Abelian.Ext X Y n) := by
  refine ⟨fun a b => ?_⟩
  rw [← a.comp_mk₀_id, ← b.comp_mk₀_id, hY.eq_of_src (𝟙 Y) 0, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]

/-- If `Ext^{b+1}(X, -)` vanishes on `ker u` and on `B`, and `Ext^b(X, -)` vanishes on the
cokernel of the coimage factorization of `u : A ⟶ B`, then `Ext^{b+1}(X, A) = 0`. -/
private theorem
    _root_.CategoryTheory.Abelian.Ext.subsingleton_of_kernel_of_cokernel_factorThruCoimage
    {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] (X : C) {A B : C} (u : A ⟶ B) (b : ℕ)
    (hK : Subsingleton (Abelian.Ext X (kernel u) (b + 1)))
    (hC : Subsingleton (Abelian.Ext X (cokernel (Abelian.factorThruCoimage u)) b))
    (hB : Subsingleton (Abelian.Ext X B (b + 1))) :
    Subsingleton (Abelian.Ext X A (b + 1)) := by
  -- the two short exact sequences cut out by `u`
  let S₁ := ShortComplex.mk (kernel.ι u) (Abelian.coimage.π u) (cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel (kernel.ι u)
      mono_f := equalizer.ι_mono
      epi_g := coequalizer.π_epi }
  let S₂ := ShortComplex.mk (Abelian.factorThruCoimage u)
    (cokernel.π (Abelian.factorThruCoimage u)) (cokernel.condition _)
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_cokernel (Abelian.factorThruCoimage u)
      mono_f := Abelian.instMonoFactorThruCoimage u
      epi_g := coequalizer.π_epi }
  have : Subsingleton (Abelian.Ext X S₂.X₃ b) := hC
  have : Subsingleton (Abelian.Ext X S₂.X₂ (b + 1)) := hB
  have : Subsingleton (Abelian.Ext X S₁.X₃ (b + 1)) :=
    subsingleton_ext_X₁_of_shortExact hS₂ _ b (b + 1) rfl
  have : Subsingleton (Abelian.Ext X S₁.X₁ (b + 1)) := hK
  exact subsingleton_ext_X₂_of_shortExact hS₁ _ (b + 1)

/-- **A sheaf vanishing on an open is supported on the complement.** If the inverse image of an
abelian sheaf `𝓚` on `X_ét` along an open immersion `j : U ⟶ X` vanishes, then the support of `𝓚`
is contained in the complement of `U`: a geometric point lying over `U` factors through `j`, and
the stalk there is a stalk of `j⁻¹𝓚`. -/
theorem smallEtaleSupport_subset_compl_range_of_isZero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : IsZero ((etaleAbelianInverseImage.{u, u + 1} j).obj H)) :
    smallEtaleSupport H ⊆ (Set.range j.base)ᶜ := by
  rintro x ⟨s, hs, hnz⟩ ⟨y, rfl⟩
  apply hnz
  have hsub : Set.range s.hom.base ⊆ Set.range j.base := by
    rintro _ ⟨p, rfl⟩
    exact ⟨y, by rw [← hs]; exact congrArg s.hom.base (Subsingleton.elim _ _) |>.symm⟩
  let s' : Spec (.of s.residueField) ⟶ U := IsOpenImmersion.lift j s.hom hsub
  have hs' : s' ≫ j = s.hom := IsOpenImmersion.lift_fac j s.hom hsub
  have h0 : IsZero ((smallEtaleStalkAb s').obj ((smallEtalePullbackAb j).obj H)) :=
    Functor.map_isZero _ (hH.of_iso ((smallEtalePullbackAbIsoEtaleAbelianInverseImage j).app H))
  have e := (smallEtaleStalkPullbackAbIso j s').app H
  rw [hs'] at e
  exact h0.of_iso e.symm

/-- **Points off an open through the generic points have smaller transcendence degree.** Let `X`
be locally of finite type over a field `K`, of dimension at most `n`, and `U` an open containing
every generic point of `X`. A point `x ∉ U` is a proper specialization of a generic point, so
`n = m + 1` and `trdeg_K κ(x) ≤ m`. -/
theorem exists_mem_trdegLESet_of_notMem (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {n : ℕ} (hX : topologicalKrullDim X ≤ n)
    (U : Set X) (hU : genericPoints X ⊆ U) (x : X) (hx : x ∉ U) :
    ∃ m : ℕ, n = m + 1 ∧ x ∈ Scheme.trdegLESet K f m := by
  obtain ⟨ξ, hξ, hxξ⟩ := exists_mem_genericPoints_mem_closure x
  have hne : ξ ≠ x := fun h => hx (h ▸ hU hξ)
  have hlt := trdeg_residueField_lt_of_specialization K X f (specializes_iff_mem_closure.2 hxξ)
    hne
  have hξn : let : Algebra K (X.residueField ξ) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.Γevaluation ξ).hom.toAlgebra
      Algebra.trdeg K (X.residueField ξ) ≤ n :=
    Cardinal.toENat_le_natCast.1 (toENat_trdeg_residueField_le_of_topologicalKrullDim_le K X f hX ξ)
  have hxn := lt_of_lt_of_le hlt hξn
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (hxn.trans (Cardinal.natCast_lt_aleph0))
  rw [ht] at hxn
  have htn : t < n := by exact_mod_cast hxn
  refine ⟨n - 1, by omega, ?_⟩
  simp only [Scheme.trdegLESet, Set.mem_ofPred_eq]
  rw [ht]
  exact_mod_cast (by omega : t ≤ n - 1)

/-! ### The vanishing theorem -/

/-- **Sheaves vanishing on an open through the generic points.** Let `X` be locally of finite type
over a field `K` with `dim X ≤ n`, and `U` an open containing every generic point of `X`. If
torsion sheaves supported in transcendence degree `≤ m` have vanishing cohomology above `2m + c₀`
for every `m < n`, then a torsion sheaf `𝓗` with `𝓗|_U = 0` has `H^b(X, 𝓗) = 0` for
`2n + c₀ < b + 1`. -/
private theorem subsingleton_H_of_isZero_inverseImage_ι (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {n c₀ : ℕ} (hX : topologicalKrullDim X ≤ n)
    (U : X.Opens) (hU : genericPoints X ⊆ U)
    (hsupp : ∀ m < n, ∀ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology H →
        smallEtaleSupport H ⊆ Scheme.trdegLESet K f m → ∀ b : ℕ, 2 * m + c₀ < b →
          Subsingleton (Sheaf.H.{u + 1, u + 1} H b))
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology H)
    (hH0 : IsZero ((etaleAbelianInverseImage.{u, u + 1} U.ι).obj H)) (b : ℕ)
    (hb : 2 * n + c₀ < b + 1) : Subsingleton (Sheaf.H.{u + 1, u + 1} H b) := by
  have hrange : Set.range U.ι.base = (U : Set X) := Scheme.Opens.range_ι U
  have hHs := smallEtaleSupport_subset_compl_range_of_isZero U.ι H hH0
  rw [hrange] at hHs
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- in dimension zero `U` is everything, so `H` is zero
    refine Abelian.Ext.subsingleton_of_isZero _ (isZero_of_forall_isZero_smallEtaleStalkAb H
      fun s => ?_) _
    by_contra hs
    obtain ⟨m, hm, -⟩ := exists_mem_trdegLESet_of_notMem K f hX U hU _ (hHs ⟨s, rfl, hs⟩)
    omega
  · refine hsupp (n - 1) (by omega) H hH (fun x hx => ?_) b (by omega)
    obtain ⟨m, hm, hxm⟩ := exists_mem_trdegLESet_of_notMem K f hX U hU x (hHs hx)
    rwa [show n - 1 = m by omega]

/-- **The direct image from an affine open, via Leray and Stacks 0F0X.** Let `X` be locally of
finite type over a field `K`, `U ⊆ X` an open with affine inclusion, and `𝓖` a torsion sheaf on `U`
supported in transcendence degree `≤ n`. If torsion sheaves on `X` supported in transcendence
degree `≤ m` have vanishing cohomology above `2m + c₀` for every `m < n`, and `H^b(U, 𝓖) = 0` with
`2n + c₀ < b`, then `H^b(X, j_*𝓖) = 0`. -/
private theorem subsingleton_H_directImage_ι_of_forall_lt (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [CompactSpace X] [LocallyOfFiniteType f] (U : X.Opens)
    [IsAffineHom U.ι] {n c₀ : ℕ}
    (hsupp : ∀ m < n, ∀ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology H →
        smallEtaleSupport H ⊆ Scheme.trdegLESet K f m → ∀ b : ℕ, 2 * m + c₀ < b →
          Subsingleton (Sheaf.H.{u + 1, u + 1} H b))
    (G : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty U.toScheme.smallEtaleTopology G)
    (hsuppG : smallEtaleSupport G ⊆ Scheme.trdegLESet K (U.ι ≫ f) n) {b : ℕ}
    (hb : 2 * n + c₀ < b) (hUb : Subsingleton (Sheaf.H.{u + 1, u + 1} G b)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, 0} U.ι).obj G) b) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  let j : U.toScheme ⟶ X := U.ι
  refine LerayVanishing.subsingleton_sheafH_directImage_of_forall j G b hUb fun q hq hqb => ?_
  by_cases hqn : n < q
  · exact Abelian.Ext.subsingleton_of_isZero _
      (isZero_rightDerived_etaleAbelianDirectImage_of_lt K (j ≫ f) f j rfl n G hG hsuppG q
        hqn) _
  · refine hsupp (n - q) (by omega) _
      (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{0} j q G hG) ?_ (b - 1 - q)
      (by omega)
    intro y hy
    have h := smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset K (j ≫ f) f j rfl
      n G hG hsuppG q hy
    simp only [Set.mem_ofPred_eq] at h
    simp only [Scheme.trdegLESet, Set.mem_ofPred_eq]
    have hle := le_trans le_self_add h
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (hle.trans_lt Cardinal.natCast_lt_aleph0)
    rw [ht] at h ⊢
    have : t + q ≤ n := by exact_mod_cast h
    exact_mod_cast (by omega : t ≤ n - q)

/-- **The inductive step.** Let `X` be a quasi-compact scheme locally of finite type over a field
`K` with `dim X ≤ n` and `cd(K) = c₀`. If torsion sheaves on `X` supported in transcendence degree
`≤ m` have vanishing cohomology above `2m + c₀` for every `m < n`, then every torsion sheaf `𝓕` on
`X_ét` has `H^b(X, 𝓕) = 0` for `b > 2n + c₀`. -/
private theorem subsingleton_H_of_forall_lt_trdegLESet (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [CompactSpace X] [LocallyOfFiniteType f] {n c₀ : ℕ}
    (hX : topologicalKrullDim X ≤ n)
    (hc₀ : Scheme.etaleCohomologicalDimension (Spec (.of K)) = c₀)
    (hsupp : ∀ m < n, ∀ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology H →
        smallEtaleSupport H ⊆ Scheme.trdegLESet K f m → ∀ b : ℕ, 2 * m + c₀ < b →
          Subsingleton (Sheaf.H.{u + 1, u + 1} H b))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (b : ℕ)
    (hb : 2 * n + c₀ < b) : Subsingleton (Sheaf.H.{u + 1, u + 1} F b) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  obtain ⟨U, hU, hgen, hj⟩ := exists_isAffineOpen_isAffineHom_genericPoints X
  let j : U.toScheme ⟶ X := U.ι
  -- the inverse image to `U` and the unit `𝓕 ⟶ j_*j⁻¹𝓕`
  have : IsAffine U.toScheme := hU
  have hdimU : topologicalKrullDim U.toScheme ≤ n :=
    j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hX
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} j
  let L := etaleAbelianInverseImage.{u, 0} j
  let G := L.obj F
  have hG : Stacks.Torsion.torsionSheafProperty U.toScheme.smallEtaleTopology G :=
    torsionSheafProperty_etaleAbelianInverseImage.{u, 0} j F hF
  let cu := adj.unit.app F
  have hLc : IsIso (L.map cu) := by
    let ff := etaleAbelianDirectImageFullyFaithfulOfIsOpenImmersion.{u, 0} j
    let _ := ff.full
    let _ := ff.faithful
    infer_instance
  have hK0 : IsZero (L.obj (kernel cu)) := isZero_inverseImage_kernel_unit adj F
  have hC0 : IsZero (L.obj (cokernel (Abelian.factorThruCoimage cu))) :=
    (isZero_map_kernel_and_cokernel_factorThruCoimage_of_isIso_map L cu).2
  let T : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
  have hKt : T (kernel cu) := T.prop_of_mono (kernel.ι cu) hF
  have hjG : T ((etaleAbelianDirectImage.{u, 0} j).obj G) :=
    torsionSheafProperty_smallEtaleDirectImageAb.{0} j G hG
  have hCt : T (cokernel (Abelian.factorThruCoimage cu)) :=
    T.prop_of_epi (cokernel.π (Abelian.factorThruCoimage cu)) hjG
  -- `H^b(U, j⁻¹𝓕) = 0` by Stacks 0F0V
  have hUb : Subsingleton (Sheaf.H.{u + 1, u + 1} G b) := by
    refine Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension U.toScheme G hG b
      (lt_of_le_of_lt (Scheme.etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le K
        U.toScheme (j ≫ f) n hdimU) ?_)
    rw [hc₀]
    exact_mod_cast (by omega : n + c₀ < b)
  -- `H^b(X, j_*j⁻¹𝓕) = 0` by the bottom edge of the Leray spectral sequence and Stacks 0F0X
  have hsuppG : smallEtaleSupport G ⊆ Scheme.trdegLESet K (j ≫ f) n := by
    rw [Scheme.trdegLESet_eq_univ_of_topologicalKrullDim_le K (j ≫ f) hdimU]
    exact Set.subset_univ _
  have hjb := subsingleton_H_directImage_ι_of_forall_lt K f U hsupp G hG hsuppG hb hUb
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  -- sheaves vanishing on `U` have vanishing cohomology from degree `2n + cd(K)` on
  exact Abelian.Ext.subsingleton_of_kernel_of_cokernel_factorThruCoimage _ cu b'
    (subsingleton_H_of_isZero_inverseImage_ι K f hX U hgen hsupp _ hKt hK0 (b' + 1) (by omega))
    (subsingleton_H_of_isZero_inverseImage_ι K f hX U hgen hsupp _ hCt hC0 b' (by omega)) hjb

/-- **Étale cohomology of a scheme of finite type over a field vanishes above twice its
dimension.** Let `K` be a field and `X` a quasi-compact scheme locally of finite type over `K` with
`dim X ≤ n`. Then `H^b_ét(X, 𝓕) = 0` for every abelian torsion sheaf `𝓕` on `X_ét` and every
`b > 2n + cd(K)`.

The proof is by induction on `n`; see the module documentation. -/
theorem subsingleton_H_of_topologicalKrullDim_le (K : Type u) [Field K] (n : ℕ) :
    ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [CompactSpace X] [LocallyOfFiniteType f],
      topologicalKrullDim X ≤ n →
        ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
            ∀ b : ℕ, ((2 * n : ℕ) : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of K)) < b →
              Subsingleton (Sheaf.H.{u + 1, u + 1} F b) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X f _ _ hX F hF b hb
  set c := Scheme.etaleCohomologicalDimension (Spec (.of K))
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, c = c₀ := by
    have hne : c ≠ ⊤ := fun htop => by
      rw [htop, add_top] at hb
      exact not_top_lt hb
    obtain ⟨c₀, h⟩ := ENat.ne_top_iff_exists.1 hne
    exact ⟨c₀, h.symm⟩
  rw [hc₀] at hb
  -- the induction hypothesis, for sheaves supported in smaller transcendence degree
  refine subsingleton_H_of_forall_lt_trdegLESet K f hX hc₀ (fun m hm H hH hHs b' hb' => ?_) F hF b
    (by exact_mod_cast hb)
  refine subsingleton_H_of_smallEtaleSupport_subset_of_finiteTypeBound K f m
    (((2 * m : ℕ) : ℕ∞) + c) (fun Z g _ _ hZ G hG b'' hb'' => ih m hm Z g hZ G hG b'' hb'')
    H hH hHs b' ?_
  rw [hc₀]
  exact_mod_cast hb'

/-- **`cd(X) ≤ 2 dim(X) + cd(K)`.** A quasi-compact scheme `X` locally of finite type over a field
`K` with `dim X ≤ n` has cohomological dimension at most `2n + cd(K)`. -/
@[sga "5 I 1.5.2" "more general"]
theorem Scheme.etaleCohomologicalDimension_le_two_mul_add (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType f]
    (n : ℕ) (hX : topologicalKrullDim X ≤ n) :
    Scheme.etaleCohomologicalDimension X ≤
      ((2 * n : ℕ) : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of K)) :=
  Scheme.etaleCohomologicalDimension_le X _ fun F hF q hq =>
    subsingleton_H_of_topologicalKrullDim_le K n X f hX F hF q hq

end AlgebraicGeometry

end
