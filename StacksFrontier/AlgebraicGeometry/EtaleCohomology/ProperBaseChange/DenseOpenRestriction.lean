module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteClosedComplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FilteredColimitClasses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSupportRestriction

/-!
# Restriction to a scalar extension and an open through the generic points of a curve

Let `X` be a Noetherian scheme of dimension at most one, locally of finite type over a separably
closed field `k`, and `W` an open of `X` containing every generic point. Then the complement of `W`
is a closed subscheme finite over `k`
(`AlgebraicGeometry.exists_isClosedImmersion_isFinite_range_eq_compl`), so the passage from `F` to
`j_* j^{-1} F` along `j : W ⟶ X`
(`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_unit_directImage`) applies
with no closed subscheme to choose. This is the reduction to a dense open in the dévissage of
Stacks 03SC (7).

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_genericPoints_subset`
* `Stacks.EtaleCohomology.isIso_etaleAbelianInverseImageDirectImageAdj_counit_of_mono` — for an
  étale monomorphism `j` (for instance an open immersion) the counit `j^{-1} j_* ⟶ 𝟭` is an
  isomorphism: the direct image is fully faithful, being isomorphic to the right adjoint of
  restriction whose counit is invertible
  (`Stacks.EtaleCohomology.etaleDirectImageAdj_counit_app_isIso`).
* `Stacks.EtaleCohomology.isZero_map_kernel_and_cokernel_factorThruCoimage_of_isIso_map` — an exact
  functor inverting `c` kills the kernel of `c` and the cokernel of its coimage factorisation, the
  two sheaves on which `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_target`
  asks for information beyond injectivity.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_directImage_constant` — for an
  open immersion `t : V ⟶ Y` through every generic point of a curve `Y`, restriction is surjective
  in degree `q` on `t_* M_V` as soon as it is on `M_Y` and injective in degree `q + 1`: the
  comparison `M_Y ⟶ t_* M_V` becomes an isomorphism over `V`, so its kernel and cokernel are
  supported on the finite complement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- A closed subscheme finite over `k` whose complement is the image of an open immersion through
every generic point of a curve. -/
private theorem exists_isClosedImmersion_isFinite_range_eq_compl_range {k : Type u} [Field k]
    {Y V : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    [TopologicalSpace.NoetherianSpace Y] (hdim : topologicalKrullDim Y ≤ 1) (t : V ⟶ Y)
    [IsOpenImmersion t] (ht : genericPoints Y ⊆ Set.range t.base) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ Y), IsClosedImmersion i ∧ IsFinite (i ≫ π) ∧
      Set.range t.base = (Set.range i.base)ᶜ := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ :=
    exists_isClosedImmersion_isFinite_range_eq_compl k π hdim t.opensRange
      (by rw [Scheme.Hom.coe_opensRange]; exact ht)
  exact ⟨Z, i, hi, hfin, by rw [hrange, compl_compl, Scheme.Hom.coe_opensRange]⟩

/-- **Passage from `j_* j^{-1} F` to `F` across an open through the generic points.** -/
theorem surjective_etaleCohomologyRestrictionMap_of_genericPoints_subset
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k] [IsSepClosed k']
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    [TopologicalSpace.NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) (W : X.Opens)
    (hW : genericPoints X ⊆ W) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hP : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' π) ((etaleAbelianDirectImage.{u, 0} W.ι).obj
        ((etaleAbelianInverseImage.{u, 0} W.ι).obj F)) q))
    (hC : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' π) (cokernel (Abelian.factorThruCoimage
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} W.ι).unit.app F))) q))
    (hC' : ∀ m, q = m + 1 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' π) (cokernel (Abelian.factorThruCoimage
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} W.ι).unit.app F))) m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) := by
  obtain ⟨Z, i, hi, hfin, hij⟩ := exists_isClosedImmersion_isFinite_range_eq_compl_range π hdim W.ι
    (by rw [Scheme.Opens.range_ι]; exact hW)
  exact surjective_etaleCohomologyRestrictionMap_of_unit_directImage.{u, u + 1} k k' π i W.ι hij
    F q hP hC hC'

/-- **For an étale monomorphism the counit `j^{-1} j_* ⟶ 𝟭` is an isomorphism.** -/
theorem isIso_etaleAbelianInverseImageDirectImageAdj_counit_of_mono {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] [Mono j] :
    IsIso (etaleAbelianInverseImageDirectImageAdj.{u, 0} j).counit := by
  have : IsIso (etaleDirectImageAdj.{u, 0} j).counit := NatIso.isIso_of_isIso_app _
  let ff := ((etaleDirectImageAdj.{u, 0} j).fullyFaithfulROfIsIsoCounit).ofIso
    ((etaleDirectImageAdj.{u, 0} j).rightAdjointUniq
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} j))
  have := ff.full
  have := ff.faithful
  infer_instance

/-- **An exact functor inverting `c` kills its kernel and the cokernel of its coimage
factorisation.** -/
theorem isZero_map_kernel_and_cokernel_factorThruCoimage_of_isIso_map {C D : Type*} [Category* C]
    [Category* D] [Abelian C] [Abelian D] (L : C ⥤ D) [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] {A B : C} (c : A ⟶ B) [IsIso (L.map c)] :
    IsZero (L.obj (kernel c)) ∧ IsZero (L.obj (cokernel (Abelian.factorThruCoimage c))) := by
  refine ⟨IsZero.of_iso (isZero_kernel_of_mono _) (PreservesKernel.iso L c), ?_⟩
  have : Epi (L.map (Abelian.factorThruCoimage c)) :=
    epi_of_epi_fac (f := L.map (Abelian.coimage.π c)) (by rw [← L.map_comp, Abelian.coimage.fac])
  have : IsIso (L.map (Abelian.factorThruCoimage c)) := isIso_of_mono_of_epi _
  exact IsZero.of_iso (isZero_cokernel_of_epi _) (PreservesCokernel.iso L _)

/-- **From the constant sheaf on a curve to its direct image from an open through the generic
points.** -/
theorem surjective_etaleCohomologyRestrictionMap_directImage_constant
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k] [IsSepClosed k']
    {Y V : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    [TopologicalSpace.NoetherianSpace Y] (hdim : topologicalKrullDim Y ≤ 1) (t : V ⟶ Y)
    [IsOpenImmersion t] (ht : genericPoints Y ⊆ Set.range t.base) (M : AddCommGrpCat.{u + 1})
    (q : ℕ)
    (hM : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (scalarExtensionFst k k' π) ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
        q))
    (hinj : ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}, Function.Injective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π) G (q + 1))) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      ((etaleAbelianDirectImage.{u, 0} t).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) q) := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} t
  let L := etaleAbelianInverseImage.{u, 0} t
  let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let e := (etaleAbelianInverseImageConstantIso.{u, 0} t).app M
  let c : A ⟶ (etaleAbelianDirectImage.{u, 0} t).obj
      ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) :=
    adj.unit.app A ≫ (etaleAbelianDirectImage.{u, 0} t).map e.hom
  have : IsIso adj.counit := isIso_etaleAbelianInverseImageDirectImageAdj_counit_of_mono t
  have hu : IsIso (L.map (adj.unit.app A)) :=
    IsIso.of_isIso_fac_right (h := 𝟙 _) (adj.left_triangle_components A)
  have : IsIso (L.map c) := by
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨hK, hC⟩ := isZero_map_kernel_and_cokernel_factorThruCoimage_of_isIso_map L c
  obtain ⟨Z, i, hi, hfin, hij⟩ := exists_isClosedImmersion_isFinite_range_eq_compl_range π hdim t ht
  have hb := fun G hG n =>
    (bijective_etaleCohomologyRestrictionMap_of_isZero_inverseImage.{u, u + 1} k k' π i t hij
      G hG n).2
  exact surjective_etaleCohomologyRestrictionMap_target.{u, 0, u + 1} _ c q hM (hinj A)
    (hb _ hK (q + 1)) (hinj _) (hb _ hC q)

end Stacks.EtaleCohomology

end
