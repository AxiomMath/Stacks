module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseOneToTwo
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThree
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThreeToTwo
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections.DualBasisOne

/-!
# Invertible objects of the derived category of a connected ringed space

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings, and suppose `X` is
connected. Then an invertible object `M` of `D(𝒪_X)` is an invertible `𝒪_X`-module placed in a
single degree: there are `m ∈ ℤ` and an invertible `𝒪_X`-module `ℒ` with `M ≅ ℒ[-m]`.

This is the special case of [Stacks, Tag 0FPG] that the source invokes whenever it says that an
invertible object of `D(𝒪_X)` on a connected space "is" a shifted invertible module. By clause (3)
of that tag `M` is represented by a complex `E` which on each member `U_i` of an open covering is
quasi-isomorphic to an invertible module placed in a degree `n_i`; members with distinct degrees
are disjoint (`Stacks.Cohomology.InvertibleDerived.not_mem_of_degree_ne`), so on a connected `X`
every member meeting a given point carries one and the same degree `m`. Then `H^k(E)` vanishes
for `k ≠ m`, because it vanishes on every member of the covering, so `E` is isomorphic in
`D(𝒪_X)` to `H^m(E)[-m]`; and `H^m(E)` is locally generated freely by one section, hence an
invertible module.

## Main results

* `Stacks.Cohomology.InvertibleDerived.exists_isInvertibleModule_iso_singleFunctor` — the
  statement above.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- **On a connected space the degrees of clause (3) of [Stacks, Tag 0FPG] are one degree.** Given
an open covering `U` of a connected space and degrees `deg i` such that members with distinct
degrees are disjoint, there is a single `m` with `deg i = m` for every member containing a
point. -/
theorem exists_deg_eq_of_connected [ConnectedSpace X.carrier] {I : Type*}
    (U : I → Opens X.carrier) (hU : ∀ x : X.carrier, ∃ i, x ∈ U i) (deg : I → ℤ)
    (hdisj : ∀ i j, deg i ≠ deg j → ∀ x, x ∈ U i → x ∉ U j) :
    ∃ m : ℤ, ∀ (i : I) (x : X.carrier), x ∈ U i → deg i = m := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X.carrier)
  obtain ⟨i₀, hi₀⟩ := hU x₀
  refine ⟨deg i₀, ?_⟩
  let S : Set X.carrier := ⋃ (i : I) (_ : deg i = deg i₀), (U i : Set X.carrier)
  let T : Set X.carrier := ⋃ (i : I) (_ : deg i ≠ deg i₀), (U i : Set X.carrier)
  have hSo : IsOpen S := isOpen_biUnion fun i _ => (U i).isOpen
  have hTo : IsOpen T := isOpen_biUnion fun i _ => (U i).isOpen
  have hST : S ∪ T = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := hU x
    by_cases h : deg i = deg i₀
    · exact Or.inl (Set.mem_biUnion (x := i) h hi)
    · exact Or.inr (Set.mem_biUnion (x := i) h hi)
  have hdj : Disjoint S T := by
    refine Set.disjoint_left.mpr fun x hS hT => ?_
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hS
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hT
    exact hdisj i j (hi.trans_ne hj.symm) x hxi hxj
  have hSc : IsClopen S := by
    refine ⟨?_, hSo⟩
    have : S = Tᶜ := by
      ext x
      constructor
      · exact fun hS hT => Set.disjoint_left.mp hdj hS hT
      · exact fun hT => Or.resolve_right ((Set.ext_iff.mp hST x).mpr trivial) hT
    rw [this]
    exact hTo.isClosed_compl
  have hSu : S = Set.univ := hSc.eq_univ ⟨x₀, Set.mem_biUnion (x := i₀) rfl hi₀⟩
  intro i x hx
  by_contra hne
  have hxS : x ∈ S := hSu ▸ Set.mem_univ x
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxS
  exact hdisj i j (fun h => hne (h.trans hj)) x hx hxj

/-- A cochain complex whose cohomology vanishes off the degree `m` is isomorphic in the derived
category to its `m`-th cohomology placed in degree `m`. -/
private theorem nonempty_Q_obj_iso_singleFunctor_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (E : CochainComplex C ℤ) (m : ℤ)
    (hz : ∀ k, k ≠ m →
      IsZero ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) k).obj E)) :
    Nonempty (DerivedCategory.Q.obj E ≅ (DerivedCategory.singleFunctor C m).obj
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) m).obj E)) := by
  have hQ : ∀ k, k ≠ m → IsZero ((DerivedCategory.homologyFunctor C k).obj
      (DerivedCategory.Q.obj E)) := fun k hk =>
    (hz k hk).of_iso ((DerivedCategory.homologyFunctorFactors C k).app E)
  have : (DerivedCategory.Q.obj E).IsGE m :=
    (DerivedCategory.isGE_iff _ m).mpr fun k hk => hQ k (by omega)
  have : (DerivedCategory.Q.obj E).IsLE m :=
    (DerivedCategory.isLE_iff _ m).mpr fun k hk => hQ k (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj E) m
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C m).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso C m).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor C m).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors C m).app E)⟩

/-- **An invertible object of `D(𝒪_X)` on a connected space with local stalks is a shifted
invertible module**: `M ≅ ℒ[-m]` for an integer `m` and an invertible `𝒪_X`-module `ℒ`. -/
theorem exists_isInvertibleModule_iso_singleFunctor [ConnectedSpace X.carrier]
    (hloc : ∀ x : X.carrier, IsLocalRing (X.presheaf.stalk x))
    [HasDerivedCategory.{d} (Mod X.sheaf)] (M : DerivedModules X.sheaf)
    (hM : IsInvertibleObject M) :
    ∃ (m : ℤ) (ℒ : Mod X.sheaf), Stacks.SheafOfModules.Tensor.IsInvertibleModule X.sheaf ℒ ∧
      Nonempty (M ≅ (DerivedCategory.singleFunctor (Mod X.sheaf) m).obj ℒ) := by
  classical
  obtain ⟨E, ⟨I, U, hU, hdata⟩, ⟨eM⟩⟩ :=
    hasLocalInvertibleDegree_of_hasInvertibleModuleDecomposition M
      (hasInvertibleModuleDecomposition_of_isInvertibleObject X M hM) hloc
  choose deg L hL f hf using hdata
  have hdisj : ∀ i j, deg i ≠ deg j → ∀ x, x ∈ U i → x ∉ U j := fun i j hij x hx =>
    @not_mem_of_degree_ne X hloc E (U i) (U j) (deg i) (deg j) (L i) (L j) (hL i) (f i) (hf i)
      (f j) (hf j) hij x hx
  have hcov : ∀ x : X.carrier, ∃ i, x ∈ U i := exists_mem_of_iSup_eq_top U hU
  obtain ⟨m, hm⟩ := exists_deg_eq_of_connected U hcov deg hdisj
  choose ι hι using hcov
  have hz : ∀ k, k ≠ m →
      IsZero ((HomologicalComplex.homologyFunctor (Mod X.sheaf) (ComplexShape.up ℤ) k).obj E) :=
    fun k hk => AlgebraicGeometry.RingedSpace.isZero_of_restrictModules X _ (fun x => U (ι x))
      (fun x => ⟨x, hι x⟩) fun x =>
        @isZero_restrictModules_homology_of_ne X E (U (ι x)) (deg (ι x)) (L (ι x)) (f (ι x))
          (hf (ι x)) k (by rwa [hm (ι x) x (hι x)])
  have hinv : Stacks.SheafOfModules.Tensor.IsInvertibleModule X.sheaf
      ((HomologicalComplex.homologyFunctor (Mod X.sheaf) (ComplexShape.up ℤ) m).obj E) := by
    have key : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
        ∃ s : ((HomologicalComplex.homologyFunctor (Mod X.sheaf) (ComplexShape.up ℤ) m).obj
          E).val.obj (op W), ∀ (W' : Opens X.carrier) (h : W' ≤ W),
          Function.Bijective fun c : X.presheaf.obj (op W') =>
            ringSec (U := op W') c • ((HomologicalComplex.homologyFunctor (Mod X.sheaf)
              (ComplexShape.up ℤ) m).obj E).val.map (homOfLE h).op s := by
      intro x
      have hφ := @nonempty_restrictModules_homology_iso X E (U (ι x)) (deg (ι x)) (L (ι x))
        (f (ι x)) (hf (ι x))
      rw [hm (ι x) x (hι x)] at hφ
      obtain ⟨φ⟩ := hφ
      obtain ⟨W, hxW, -, s, hs⟩ := exists_smul_bijective_of_iso_restrict hloc _ (hL (ι x)) φ (hι x)
      exact ⟨W, hxW, s, hs⟩
    choose W hxW s hs using key
    have hcovW : (Opens.grothendieckTopology X.carrier).CoversTop W :=
      (Opens.coversTop_iff _ _).mpr (IsOpenCover.mk (top_le_iff.mp fun x _ =>
        Opens.mem_iSup.mpr ⟨x, hxW x⟩))
    exact Stacks.SheafOfModules.isInvertible_of_dualBasisOne _ _ hcovW fun x =>
      Stacks.SheafOfModules.DualBasisOne.ofSmulBijective (W x) (s x) fun V =>
        hs x V.unop.left (leOfHom V.unop.hom)
  obtain ⟨e⟩ := nonempty_Q_obj_iso_singleFunctor_homology E m hz
  exact ⟨m, _, hinv, ⟨eM.symm ≪≫ e⟩⟩

end Stacks.Cohomology.InvertibleDerived

end
