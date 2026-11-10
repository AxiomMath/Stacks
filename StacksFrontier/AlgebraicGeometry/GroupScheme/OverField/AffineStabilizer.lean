module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerSubgroup
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AffineSectionsTensorZeroDivisors
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GeometricallyIrreducibleOfConnected
public import StacksFrontier.AlgebraicGeometry.Morphisms.ClosedSubschemesDirectedAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.RingTheory.HopfAlgebra.ReducedCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ReducedOfStalkUnit
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# An affine closed subgroup scheme of finite presentation

Let `G` be a connected, quasi-compact group scheme over a field `k` of characteristic zero.  This
file proves Perrin's step C1 (thesis I §2, IV §1): **there is an affine closed subgroup scheme
`H ⊆ G` whose inclusion is locally of finite presentation**
(`AlgebraicGeometry.exists_closedSubgroupScheme_isAffine_locallyOfFinitePresentation`).  Being an
affine group scheme in characteristic zero, `H` is reduced
(`AlgebraicGeometry.isReduced_of_groupScheme_of_charZero_of_isAffine`), so it lies in every
closed subgroup scheme `L` of `G` with surjective inclusion, for instance the reduction `G_red`
(`AlgebraicGeometry.exists_affineStabilizer_lift`).

## Proof

Fix a nonempty affine open `U` of `G`.  For every finite set `F ⊆ Γ(U)` the right stabiliser of
`F` is a closed subscheme `Z_F = V(K_F)` with ideal sheaf of finite type
(`AlgebraicGeometry.exists_idealSheafData_forall_rightStabilises`; Perrin's content hypothesis is
`AlgebraicGeometry.zeroDivisorsNilpotent_tensor_of_isAffineOpen` in characteristic zero), and a
closed subgroup scheme (`AlgebraicGeometry.exists_closedSubgroupScheme_of_rightStabilises`).  The
`Z_F` form a directed family, and a point `x` lying on every `Z_F` is the unit: the point
`Spec κ(x) ⟶ G` stabilises every function on `U`, hence is `1` (Perrin IV 1.3,
`AlgebraicGeometry.eq_one_of_forall_rightStabilises`).  So `⋂ Z_F` lies in an affine open
neighbourhood of the unit, and on the quasi-compact `G` some `Z_F` is affine
(`AlgebraicGeometry.Scheme.exists_isAffine_of_directed`).

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, I §2 and IV §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

namespace AlgebraicGeometry

universe u

/-- In characteristic zero every affine open of a geometrically irreducible group scheme satisfies
Perrin's content hypothesis: every zero divisor of every `Γ(U) ⊗[k] κ` is nilpotent. -/
theorem zeroDivisors_isNilpotent_tensor_of_charZero (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (.of k)))) [GeometricallyIrreducible G.X.hom] (U : G.X.left.Opens)
    (hU : IsAffineOpen U) :
    letI := sectionsAlgebra G.X.hom U
    ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.X.left, U) ⊗[k] κ),
      z ∉ nonZeroDivisors (Γ(G.X.left, U) ⊗[k] κ) → IsNilpotent z :=
  let := sectionsAlgebra G.X.hom U
  fun κ _ _ ↦ zeroDivisorsNilpotent_tensor_of_isAffineOpen k G hU rfl κ

/-- **Perrin, thesis I §2 and IV §1 (step C1): an affine closed subgroup scheme of finite
presentation.**  Let `G` be a connected, quasi-compact group scheme over a field `k` of
characteristic zero.  There is a closed subgroup scheme `H` of `G` which is affine and whose
inclusion `H ⟶ G` is locally of finite presentation (its ideal sheaf is of finite type); `H` is
moreover reduced, being an affine group scheme in characteristic zero.

`H` is the right stabiliser of a finite set of functions on a nonempty affine open `U` of `G`:
these stabilisers are closed subgroup schemes with ideal sheaves of finite type, they form a
directed family whose intersection is the unit point (Perrin IV 1.3), so one of them lies in an
affine open neighbourhood of the unit and is affine. -/
theorem exists_closedSubgroupScheme_isAffine_locallyOfFinitePresentation (k : Type u) [Field k]
    [CharZero k] (G : Grp (Over (Spec (.of k)))) [ConnectedSpace G.X.left]
    [CompactSpace G.X.left] :
    ∃ H : ClosedSubgroupScheme G, IsAffine H.carrier.X.left ∧
      LocallyOfFinitePresentation H.ι.hom.hom.left ∧ IsReduced H.carrier.X.left := by
  classical
  have : GeometricallyIrreducible G.X.hom := geometricallyIrreducible_of_connectedSpace G.X
  have hC := zeroDivisors_isNilpotent_tensor_of_charZero k G
  obtain ⟨x₀⟩ := (inferInstance : Nonempty G.X.left)
  obtain ⟨U, hU, hx₀U, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x₀)
  have hne : (U : Set G.X.left).Nonempty := ⟨x₀, hx₀U⟩
  -- the stabiliser ideal sheaves of the finite subsets of `Γ(U)`
  have hKex : ∀ F : Finset Γ(G.X.left, U), ∃ K : G.X.left.IdealSheafData,
      (∀ W : G.X.left.affineOpens, (K.ideal W).FG) ∧
      ∀ (T : Over (Spec (.of k))) (h : T ⟶ G.X),
        (∀ i : F, RightStabilises h U i.1) ↔ K ≤ h.left.ker :=
    fun F ↦ exists_idealSheafData_forall_rightStabilises hU (hC U hU) hne (fun i : F ↦ i.1)
  choose K hKfg hK using hKex
  -- the stabilisers form a directed family
  have hmono : ∀ {F F' : Finset Γ(G.X.left, U)}, F ⊆ F' → K F ≤ K F' := by
    intro F F' hFF'
    let j : Over.mk ((K F').subschemeι ≫ G.X.hom) ⟶ G.X := Over.homMk (K F').subschemeι rfl
    have hj := (hK F' _ j).mpr (Scheme.IdealSheafData.ker_subschemeι (K F')).ge
    exact ((hK F _ j).mp fun i ↦ hj ⟨i.1, hFF' i.2⟩).trans
      (Scheme.IdealSheafData.ker_subschemeι (K F')).le
  have hsub : ∀ {F F' : Finset Γ(G.X.left, U)}, F ⊆ F' →
      Set.range (K F').subschemeι.base ⊆ Set.range (K F).subschemeι.base := by
    intro F F' hFF'
    rintro _ ⟨y, rfl⟩
    refine ⟨IsClosedImmersion.lift (K F).subschemeι (K F').subschemeι ?_ y, ?_⟩
    · rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
      exact hmono hFF'
    · rw [← Scheme.Hom.comp_apply, IsClosedImmersion.lift_fac]
  have hdir : Directed (· ⊇ ·) fun F ↦ Set.range (K F).subschemeι.base :=
    fun F F' ↦ ⟨F ∪ F', hsub Finset.subset_union_left, hsub Finset.subset_union_right⟩
  -- the intersection of the stabilisers is the unit point
  obtain ⟨pt⟩ : Nonempty (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨U', hU', hU'e, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top ((η[G.X] : 𝟙_ _ ⟶ G.X).left pt))
  have hint : ⋂ F, Set.range (K F).subschemeι.base ⊆ U' := by
    intro x hx
    let Y : Over (Spec (.of k)) := Over.mk (G.X.left.fromSpecResidueField x ≫ G.X.hom)
    let p : Y ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField x) rfl
    have : IsReduced Y.left := inferInstanceAs (IsReduced (Spec (G.X.left.residueField x)))
    have hp : ∀ f, RightStabilises p U f := by
      intro f
      obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
        (K {f}) p.left).2 (by
          rintro _ ⟨q, rfl⟩
          rw [← Scheme.IdealSheafData.range_subschemeι]
          change G.X.left.fromSpecResidueField x q ∈ _
          rw [Scheme.fromSpecResidueField_apply]
          exact Set.mem_iInter.mp hx {f})
      have hle : K {f} ≤ p.left.ker := by
        rw [← hg]
        exact (Scheme.IdealSheafData.ker_subschemeι (K {f})).symm.le.trans
          (Scheme.Hom.le_ker_comp _ _)
      exact (hK {f} Y p).mpr hle ⟨f, Finset.mem_singleton_self f⟩
    have h1 := eq_one_of_forall_rightStabilises p hU hne hp
    let q : Spec (G.X.left.residueField x) := default
    have hq : p.left q = x := Scheme.fromSpecResidueField_apply _ _
    have hpl : p.left = (toUnit Y).left ≫ (η[G.X] : 𝟙_ _ ⟶ G.X).left := by
      rw [h1]
      rfl
    rw [← hq, hpl, Scheme.Hom.comp_apply, Subsingleton.elim ((toUnit Y).left q) pt]
    exact hU'e
  obtain ⟨F, hF⟩ := Scheme.exists_isAffine_of_directed G.X.left (fun F ↦ (K F).subschemeι)
    hdir hU' hint
  -- the stabiliser of `F` is the required subgroup
  obtain ⟨H, e, heq⟩ := exists_closedSubgroupScheme_of_rightStabilises G hU (hC U hU) hne
    (fun i : F ↦ i.1) (K F) (hK F)
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsAffine (Over.mk ((K F).subschemeι ≫ G.X.hom)).left := hF
  have : IsAffine H.carrier.X.left := IsAffine.of_isIso e.inv.left
  have hι : H.ι.hom.hom.left = e.inv.left ≫ (K F).subschemeι := by
    have := congrArg Over.Hom.left heq
    rw [Over.comp_left] at this
    change (K F).subschemeι = _ at this
    refine Eq.trans ?_ (congrArg (e.inv.left ≫ ·) this).symm
    rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have : LocallyOfFinitePresentation (K F).subschemeι :=
    (Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff _).mpr (hKfg F)
  refine ⟨H, inferInstance, ?_, ?_⟩
  · rw [hι]
    infer_instance
  · have : GrpObj (Over.mk H.carrier.X.hom) := inferInstanceAs (GrpObj H.carrier.X)
    exact isReduced_of_groupScheme_of_charZero_of_isAffine k H.carrier.X.left H.carrier.X.hom

/-- **The affine stabiliser inside the reduction.**  Let `G` be a connected, quasi-compact group
scheme over a field `k` of characteristic zero and `L` a closed subgroup scheme of `G` whose
inclusion is surjective (for instance the reduction `G_red`, Stacks 047R).  Then there is an
affine closed subscheme `Z` of `L` through which the unit factors, with `Z ⟶ L` a closed
immersion locally of finite presentation and the composite `Z ⟶ L ⟶ G` locally of finite
presentation: the affine reduced stabiliser of
`AlgebraicGeometry.exists_closedSubgroupScheme_isAffine_locallyOfFinitePresentation`, lifted
through `L`. -/
theorem exists_affineStabilizer_lift (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (.of k)))) [ConnectedSpace G.X.left] [CompactSpace G.X.left]
    (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left] :
    ∃ (Z : Scheme.{u}) (iZ : Z ⟶ L.carrier.X.left), IsClosedImmersion iZ ∧
      LocallyOfFinitePresentation iZ ∧ LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left) ∧
      IsAffine Z ∧ ∃ e : (𝟙_ (Over (Spec (.of k)))).left ⟶ Z,
        e ≫ iZ = (η[L.carrier.X] : 𝟙_ _ ⟶ L.carrier.X).left := by
  obtain ⟨H, hA, hP, hR⟩ := exists_closedSubgroupScheme_isAffine_locallyOfFinitePresentation k G
  have := L.isClosedImmersion
  have := H.isClosedImmersion
  obtain ⟨iZ, hiZ⟩ := exists_lift_of_isClosedImmersion L.ι.hom.hom.left H.ι.hom.hom.left
    fun x _ ↦ ‹Surjective L.ι.hom.hom.left›.surj x
  have : IsClosedImmersion (iZ ≫ L.ι.hom.hom.left) := by
    rw [hiZ]
    infer_instance
  have : IsClosedImmersion iZ := IsClosedImmersion.of_comp_isClosedImmersion iZ L.ι.hom.hom.left
  have : LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left) := hiZ ▸ hP
  have : LocallyOfFinitePresentation iZ := locallyOfFinitePresentation_of_comp iZ L.ι.hom.hom.left
  refine ⟨_, iZ, inferInstance, inferInstance, inferInstance, hA,
    (η[H.carrier.X] : 𝟙_ _ ⟶ H.carrier.X).left, ?_⟩
  rw [← cancel_mono L.ι.hom.hom.left, Category.assoc, hiZ, ← Over.comp_left, ← Over.comp_left,
    IsMonHom.one_hom, IsMonHom.one_hom]

end AlgebraicGeometry

end
