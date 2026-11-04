module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.CompactSupportVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.LowestDegreeDerivedDual
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality
public import StacksFrontier.AlgebraicGeometry.Divisors.TorsionFree.DenseOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.TorsionFree.IntegralNoetherian
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated

/-!
# Top-degree compactly supported cohomology of the dual of a coherent sheaf

Let `X` be an integral scheme proper over a field `k` of dimension `d`, with dualizing complex
`ω_X^•` ([Stacks, Section 0FVU], here `AlgebraicGeometry.standardRelativeDualizingComplex`), let
`G` be a coherent `𝒪_X`-module and let `U ⊆ X` be an open with `U ≠ X`. This file proves that

`H^{-d}_c(U, R𝓗om(G, ω_X^•)|_U) = H^0_c(U, R𝓗om(G, ω_X^•)[-d]|_U) = 0`,

the vanishing at the heart of the proof of [Stacks, Tag 0G5E].

## Main results

* `Stacks.Duality.Lichtenbaum.isTorsionFree_relativeDualizingModule`: `ω_X` is torsion free
  ([Stacks, Tag 0FVV] part (2) and [Stacks, Tag 0AXY]).
* `Stacks.Duality.Lichtenbaum.isZero_homology_standardRelativeDualizingComplex`: `ω_X^•` has no
  cohomology below degree `-d` ([Stacks, Tag 0FVV] part (1)).
* `Stacks.Duality.Lichtenbaum.standardRelativeDualizingComplex_homology_section_eq_zero`: a section
  of `H^{-d}(ω_X^•) = ω_X` vanishing on a nonempty open is zero.
* `Stacks.Duality.Lichtenbaum.subsingleton_degreeZeroCompactSupport_shift_boundedCoherentDuality`:
  the vanishing of `H^0_c(U, R𝓗om(G, ω_X^•)[-d]|_U)`.

## Implementation notes

The source writes `H^{-d}(R𝓗om(G, ω_X^•)) = 𝓗om(G, ω_X)` and quotes [Stacks, Tag 0AXZ] for the
torsion freeness of the right-hand side, which then has no nonzero section vanishing on a
nonempty open. Only that last property is used, and it is proved directly from the torsion
freeness of `ω_X` (`Stacks.Duality.Lichtenbaum.homology_derivedDualInto_section_eq_zero`): a
section of `H^{-d}(R𝓗om(G, ω_X^•))` is a morphism `G ⟶ ω_X`, and it vanishes as soon as each of its
values does.

`R𝓗om(-, ω_X^•)` is `Stacks.Duality.boundedCoherentDuality`, and `H^0_c` is
`AlgebraicGeometry.degreeZeroCompactSupport`, both at the standard model of the derived category.

## References

* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0AXY](https://stacks.math.columbia.edu/tag/0AXY)
* [Stacks Project, Tag 0G5C](https://stacks.math.columbia.edu/tag/0G5C)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Duality.Lichtenbaum

open _root_.AlgebraicGeometry Stacks.AlgebraicGeometry.ReflexiveModules

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- **The dualizing module of a proper variety is torsion free.** By [Stacks, Tag 0FVV] part (2),
`ω_X` is coherent with property `(S₂)` and its support is the union of the irreducible components
of maximal dimension, which for `X` integral is `X`; so it is torsion free by
[Stacks, Tag 0AXY]. -/
theorem isTorsionFree_relativeDualizingModule [IsIntegral X] :
    IsTorsionFree (relativeDualizingModule p
      (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) := by
  let := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨hcoh, hS2, hsupp⟩ := relativeDualizingModule_of_isProper p
  have := hcoh
  have hComp : (Set.univ : Set X) ∈ irreducibleComponents X := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have hUniv : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph
  have hmem : ∀ x : X, x ∈ _root_.SheafOfModules.supp (relativeDualizingModule p
      (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) := fun x => by
    rw [hsupp]
    exact Set.mem_sUnion.mpr ⟨Set.univ, ⟨hComp, hUniv⟩, Set.mem_univ x⟩
  have h := isTorsionFree_tfae X _ ⟨genericPoint X, hmem _⟩
  have h3 : genericPoint X ∈ _root_.SheafOfModules.supp (relativeDualizingModule p
        (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ∧
      SheafHasPropertySk X (relativeDualizingModule p
        (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) 1 :=
    ⟨hmem _, fun x => (min_le_min (by norm_num) le_rfl).trans (hS2 x)⟩
  exact (h.out 1 3).2 h3

/-- If a section of `B` over `W` is zero as soon as it restricts to zero on `V`, then so is a
section of an isomorphic module `A` whose image under the isomorphism restricts to zero. -/
private theorem eq_zero_of_iso_of_map_eq_zero {A B : X.Modules} (e : A ≅ B) {V W : X.Opens}
    (h : V ≤ W) (hB : ∀ y : Γ(B, W), B.presheaf.map (homOfLE h).op y = 0 → y = 0)
    (z : Γ(A, W)) (hz : A.presheaf.map (homOfLE h).op z = 0) : z = 0 := by
  have h0 : e.hom.app W z = 0 := hB _ <|
    (NatTrans.naturality_apply e.hom.mapPresheaf (homOfLE h).op z).symm.trans
      ((congrArg _ hz).trans (map_zero _))
  have h1 := congrArg (fun t => t.app W z) e.hom_inv_id
  exact h1.symm.trans ((congrArg (e.inv.app W) h0).trans (map_zero _))

/-- **A section of `ω_X = H^{-d}(ω_X^•)` vanishing on a nonempty open is zero.** For `X` an
integral scheme proper over `k` of dimension `d`, a section of the `(-d)`-th cohomology sheaf of
`ω_X^•` (at the standard model) over `W` which vanishes on `W ∩ V`, for `V` nonempty, is zero:
that sheaf is `ω_X`, which is quasi-coherent and torsion free
(`Stacks.Duality.Lichtenbaum.isTorsionFree_relativeDualizingModule`), and `W ∩ V` is nonempty
as soon as `W` is. -/
theorem standardRelativeDualizingComplex_homology_section_eq_zero [IsIntegral X] (d : ℕ)
    (hd : topologicalKrullDim X = d) (V : X.Opens) (hV : (V : Set X).Nonempty) (W : X.Opens)
    (z : Γ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) (-(d : ℤ))).obj
        (standardRelativeDualizingComplex p), W))
    (hz : ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) (-(d : ℤ))).obj
        (standardRelativeDualizingComplex p)).presheaf.map
          (homOfLE (inf_le_left : W ⊓ V ≤ W)).op z = 0) :
    z = 0 := by
  have hdn : ENat.toNat ((topologicalKrullDim X).getD 0) = d := by rw [hd]; rfl
  let e : (@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) (-(d : ℤ))).obj
        (standardRelativeDualizingComplex p) ≅
      relativeDualizingModule p (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) :=
    (StacksDraft.DerivedModel.modelHomologyFunctorIso (Scheme.Modules.hasDerivedCategory X)
      (HasDerivedCategory.standard X.Modules) (-(d : ℤ))).app _ ≪≫
      eqToIso (by rw [relativeDualizingModule, hdn])
  have := isQuasicoherent_relativeDualizingModule p
    (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))
  by_cases hW : (W : Set X).Nonempty
  · have hWV : ((W ⊓ V : X.Opens) : Set X).Nonempty := by
      have hW' : (Set.univ ∩ (W : Set X)).Nonempty := by simpa using hW
      have hV' : (Set.univ ∩ (V : Set X)).Nonempty := by simpa using hV
      simpa using (IrreducibleSpace.isIrreducible_univ X).2 _ _ W.isOpen V.isOpen hW' hV'
    exact eq_zero_of_iso_of_map_eq_zero e inf_le_left
      (fun y => (isTorsionFree_relativeDualizingModule p).eq_zero_of_map_eq_zero inf_le_left hWV y)
      z hz
  · refine TopCat.Presheaf.section_ext ⟨_, Scheme.Modules.isSheaf _⟩ W _ 0 fun x hx => ?_
    exact absurd ⟨x, hx⟩ hW

/-- The cohomology sheaves of `ω_X^•` (at the standard model) vanish below degree `-dim X`
([Stacks, Tag 0FVV] part (1)). -/
theorem isZero_homology_standardRelativeDualizingComplex (d : ℕ)
    (hd : topologicalKrullDim X = d) (j : ℤ) (hj : j < -(d : ℤ)) :
    IsZero ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) j).obj (standardRelativeDualizingComplex p)) := by
  have hdn : ENat.toNat ((topologicalKrullDim X).getD 0) = d := by rw [hd]; rfl
  exact (isZero_homology_of_lt_of_isProper p j (by rw [hdn]; exact hj)).of_iso
    ((StacksDraft.DerivedModel.modelHomologyFunctorIso (Scheme.Modules.hasDerivedCategory X)
      (HasDerivedCategory.standard X.Modules) j).app _)

/-- **`H^{-d}_c(U, R𝓗om(G, ω_X^•)|_U) = 0` on a proper variety of dimension `d`, for `U ≠ X`.**
Let `X` be an integral scheme proper over a field `k` with `dim X = d`, let `G` be a coherent
`𝒪_X`-module, and let `U ⊆ X` be an open whose complement is nonempty. Then the degree-zero
compactly supported cohomology of `U` with coefficients in `R𝓗om(G, ω_X^•)[-d]|_U` vanishes.

This is the heart of the proof of [Stacks, Tag 0G5E]: `ω_X^•` has no cohomology below degree
`-d` and `H^{-d}(ω_X^•) = ω_X` is torsion free ([Stacks, Tag 0FVV], [Stacks, Tag 0AXY]), so
`K = R𝓗om(G, ω_X^•)[-d]` has no cohomology in negative degrees and `H^0(K) = 𝓗om(G, ω_X)` has no
nonzero global section vanishing on a nonempty open
(`Stacks.Duality.Lichtenbaum.homology_derivedDualInto_section_eq_zero`); [Stacks, Tag 0G5C] then
gives `H^0_c(U, K|_U) = 0`
(`Stacks.Duality.Lichtenbaum.subsingleton_degreeZeroCompactSupport_of_forall_eq_zero`). -/
theorem subsingleton_degreeZeroCompactSupport_shift_boundedCoherentDuality [IsIntegral X]
    (d : ℕ) (hd : topologicalKrullDim X = d) (G : X.Modules) (hG : G.IsCoherent)
    (U : X.Opens) (hU : ((U : Set X)ᶜ).Nonempty) :
    letI := LocallyOfFiniteType.isLocallyNoetherian p
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsNoetherian X := ⟨⟩
    Subsingleton (degreeZeroCompactSupport p U ((restrictBoundedCoherentLift U.ι).obj
      ((((boundedCoherentDuality X (isDualizingComplex_standardRelativeDualizingComplex p)).obj
        (op ⟨(@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) 0).obj G,
            derivedCategoryBBounded_singleFunctor_obj X G hG⟩) :
              BoundedCoherentDerived X))⟦-(d : ℤ)⟧))) := by
  let := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  let := HasDerivedCategory.standard X.Modules
  let : HasDerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) :=
    HasDerivedCategory.standard _
  let ω := standardRelativeDualizingComplex p
  let D : DerivedCategory X.Modules := RingedSite.derivedDualInto
    (Stacks.SheafOfModules.ringedSite X.sheaf) ω ((DerivedCategory.singleFunctor X.Modules 0).obj G)
  have hωGE : (show DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) from
      ω).IsGE (-(d : ℤ)) :=
    (DerivedCategory.isGE_iff _ _).2 fun j hj =>
      isZero_homology_standardRelativeDualizingComplex p d hd j hj
  have hGLE : (show DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) from
      (DerivedCategory.singleFunctor X.Modules 0).obj G).IsLE 0 :=
    (DerivedCategory.isLE_iff _ _).2 fun j hj =>
      DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules 0).obj G) 0 j hj
  have hDGE := Stacks.SheafOfModules.isGE_derivedSheafHom X.sheaf _ _ 0 (-(d : ℤ)) hGLE hωGE
  let K : BoundedCoherentDerived X :=
    (boundedCoherentDuality X (isDualizingComplex_standardRelativeDualizingComplex p)).obj
      (op ⟨(DerivedCategory.singleFunctor X.Modules 0).obj G,
        derivedCategoryBBounded_singleFunctor_obj X G hG⟩)
  let eH : ∀ i : ℤ, (DerivedCategory.homologyFunctor X.Modules i).obj
      (K⟦-(d : ℤ)⟧).obj ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ) + i)).obj D :=
    fun i => (DerivedCategory.homologyFunctor X.Modules i).mapIso
      (((boundedCoherentDerived X).ι.commShiftIso (-(d : ℤ))).app K) ≪≫
        ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso
          (-(d : ℤ)) i (-(d : ℤ) + i) rfl).app D
  refine subsingleton_degreeZeroCompactSupport_of_forall_eq_zero p (K⟦-(d : ℤ)⟧)
    (fun i hi => ?_) U hU ?_
  · refine IsZero.of_iso ?_ (eH i)
    exact DerivedCategory.isZero_of_isGE _ (-(d : ℤ) - 0) (-(d : ℤ) + i) (by omega) (hX := hDGE)
  · intro V hV σ hσ
    let e := eH 0 ≪≫ eqToIso (by rw [add_zero])
    exact eq_zero_of_iso_of_map_eq_zero e (le_top : V ≤ ⊤)
      (fun y => homology_derivedDualInto_section_eq_zero G ω (-(d : ℤ))
        (fun j hj => isZero_homology_standardRelativeDualizingComplex p d hd j hj) V
        (fun W z hz =>
          standardRelativeDualizingComplex_homology_section_eq_zero p d hd V hV W z hz) y)
      σ hσ

end Stacks.Duality.Lichtenbaum

end
