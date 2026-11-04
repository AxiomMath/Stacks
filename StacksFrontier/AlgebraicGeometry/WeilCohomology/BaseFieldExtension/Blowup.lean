module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Divisor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Axiom (A7) descends along a field extension

Let `k'/k` be a field extension and `i : Z ⟶ X` a closed immersion of smooth projective schemes
over `k` with `Z` nowhere dense in `X`. The base change `i_{k'} : Z_{k'} ⟶ X_{k'}` is again a
closed immersion with nowhere dense image (the projection `X_{k'} ⟶ X` is flat, so it lifts
generalizations, and a nowhere dense closed subset of the Noetherian space `X` contains no
generic point of an irreducible component). Blowing up commutes with flat base change
(Tag 0805), so the blowing up of `X_{k'}` in `Z_{k'}` maps to the base change of the blowing up
of `X` in `Z`, over `X_{k'}`. Hence injectivity of the pullback along the blowing up for
`(H')^*` gives injectivity of its base change to `F'` for `H^*`, and so injectivity for `H^*`
(the linear algebra fact of the proof of Lemma 0FVT).

## Main results

* `IsNowhereDense.preimage_of_generalizingMap`: the preimage of a nowhere dense closed subset of
  a Noetherian sober space under a continuous generalizing map is nowhere dense.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.exists_blowup_baseChange`: the blowing up of
  `X_{k'}` in `Z_{k'}` maps to `(Bl_Z X)_{k'}` over `X_{k'}`.
* `Stacks.WeilCohomology.FieldExtensionComparison.blowupAxiom`: **(A7) descends**.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function Topology
  TopologicalSpace

universe u w w'

/-- **The preimage of a nowhere dense closed set under a generalizing map is nowhere dense**, the
target being Noetherian and sober. An interior point `x'` of the preimage maps into `S`; the
generic point `η` of an irreducible component through `f x'` is not in `S` (Noetherian: a
component inside the closed nowhere dense `S` would give `S` interior), and lifts to a
generalization of `x'`, which lies in the open interior, hence maps into `S`. -/
theorem IsNowhereDense.preimage_of_generalizingMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [NoetherianSpace Y] [QuasiSober Y] {f : X → Y} (hf : Continuous f)
    (hg : GeneralizingMap f) {S : Set Y} (hS : IsClosed S) (hnd : IsNowhereDense S) :
    IsNowhereDense (f ⁻¹' S) := by
  rw [IsNowhereDense, (hS.preimage hf).closure_eq, Set.eq_empty_iff_forall_notMem]
  intro x' hx'
  have hZ := irreducibleComponent_mem_irreducibleComponents (f x')
  have hgen := (isIrreducible_irreducibleComponent (x := f x')).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ hZ)
  obtain ⟨η', hη', hfη'⟩ := hg (hgen.specializes (mem_irreducibleComponent (x := f x')))
  have hηS : (isIrreducible_irreducibleComponent (x := f x')).genericPoint ∈ S := by
    rw [← hfη']
    exact interior_subset (s := f ⁻¹' S) (hη'.mem_open isOpen_interior hx')
  refine (hS.isNowhereDense_iff_forall_irreducibleComponents_not_subset.mp hnd) _ hZ ?_
  rw [← hgen.def]
  exact hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηS)

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]

/-- The base change of a closed immersion is a closed immersion. -/
theorem isClosedImmersion_baseChange_map :
    IsClosedImmersion ((baseChange k k').map i).hom.left := by
  have h : IsClosedImmersion ((toScheme k).map i) := ‹IsClosedImmersion i.hom.left›
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_baseChange_map (k' := k') i).flip h

/-- The ideal sheaf of `i_{k'}` is the inverse image of the ideal sheaf of `i`. -/
theorem ker_baseChange_map :
    ((baseChange k k').map i).hom.left.ker = i.hom.left.ker.comap (baseChangeProj X) := by
  have sq := isPullback_baseChange_map (k' := k') i
  have : IsClosedImmersion ((toScheme k).map i) := ‹IsClosedImmersion i.hom.left›
  show ((toScheme k').map ((baseChange k k').map i)).ker = _
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

omit [IsClosedImmersion i.hom.left] in
/-- The image of `i_{k'}` is the inverse image of the image of `i`. -/
theorem range_baseChange_map :
    Set.range ((baseChange k k').map i).hom.left.base =
      (baseChangeProj X).base ⁻¹' Set.range i.hom.left.base := by
  have sq := isPullback_baseChange_map (k' := k') i
  show Set.range ((toScheme k').map ((baseChange k k').map i)).base =
    (baseChangeProj X).base ⁻¹' Set.range ((toScheme k).map i).base
  rw [← Scheme.Pullback.range_fst]
  apply Set.Subset.antisymm
  · rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · rw [← sq.isoPullback_inv_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _

/-- **The centre stays nowhere dense** after base change along `k'/k`. -/
theorem isNowhereDense_range_baseChange_map
    (hnd : IsNowhereDense (Set.range i.hom.left.base)) :
    IsNowhereDense (Set.range ((baseChange k k').map i).hom.left.base) := by
  have : CompactSpace ((toScheme k).obj X) := SmoothProjectiveScheme.compactSpace X
  have : IsNoetherian ((toScheme k).obj X) :=
    { toIsLocallyNoetherian := SmoothProjectiveScheme.isLocallyNoetherian X
      toCompactSpace := inferInstance }
  rw [range_baseChange_map]
  exact IsNowhereDense.preimage_of_generalizingMap (baseChangeProj X).continuous
    (Flat.generalizingMap (baseChangeProj X)) i.hom.left.isClosedEmbedding.isClosed_range hnd

/-- **The blowing up of `X_{k'}` in `Z_{k'}` maps to `(Bl_Z X)_{k'}` over `X_{k'}`** (Tag 0805:
blowing up commutes with the flat base change `X_{k'} ⟶ X`). -/
theorem exists_blowup_baseChange :
    haveI := isClosedImmersion_baseChange_map (k' := k') i
    ∃ φ : SmoothProjectiveScheme.blowupObj ((baseChange k k').map i) ⟶
        (baseChange k k').obj (SmoothProjectiveScheme.blowupObj i),
      φ ≫ (baseChange k k').map (SmoothProjectiveScheme.blowupHom i) =
        SmoothProjectiveScheme.blowupHom ((baseChange k k').map i) := by
  have := isClosedImmersion_baseChange_map (k' := k') i
  obtain ⟨h, hsq⟩ := Stacks.Blowup.exists_isPullback_blowUpToBase_of_eq_comap
    (ε := baseChangeProj (k' := k') X) i.hom.left.ker _ (ker_baseChange_map (k' := k') i).symm
  have hw := hsq.flip.w
  let l : (toScheme k').obj (SmoothProjectiveScheme.blowupObj ((baseChange k k').map i)) ⟶
      (toScheme k').obj ((baseChange k k').obj (SmoothProjectiveScheme.blowupObj i)) :=
    pullback.lift (h : (toScheme k').obj (SmoothProjectiveScheme.blowupObj
        ((baseChange k k').map i)) ⟶ (toScheme k).obj (SmoothProjectiveScheme.blowupObj i))
      (SmoothProjectiveScheme.blowupObj ((baseChange k k').map i)).obj.hom (by
        show h ≫ Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom =
          (Stacks.Blowup.blowUpToBase ((baseChange k k').map i).hom.left.ker ≫
            ((baseChange k k').obj X).obj.hom) ≫ ArtinSchreier.specExt k k'
        rw [← Category.assoc, ← hw, Category.assoc, (isPullback_baseChangeProj (k' := k') X).w]
        exact (Category.assoc _ _ _).symm)
  have hl0 : l ≫ ((baseChange k k').obj (SmoothProjectiveScheme.blowupObj i)).obj.hom =
      (SmoothProjectiveScheme.blowupObj ((baseChange k k').map i)).obj.hom :=
    pullback.lift_snd _ _ _
  have hl1 : l ≫ baseChangeProj (SmoothProjectiveScheme.blowupObj i) = h :=
    pullback.lift_fst _ _ _
  refine ⟨homMk l hl0, ?_⟩
  apply hom_ext'
  rw [Functor.map_comp]
  show l ≫ _ = _
  apply (isPullback_baseChangeProj X).hom_ext
  · rw [Category.assoc, baseChangeProj_naturality, ← Category.assoc, hl1]
    exact hw.symm
  · rw [Category.assoc, w, hl0, w]

end SmoothProjectiveScheme

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

include Φ in
/-- **Axiom (A7) descends**: if pullback along the blowing up in a smooth nowhere dense centre is
injective for `(H')^*`, it is injective for `H^*`. -/
theorem blowupAxiom (h : 𝔇'.BlowupAxiom) : 𝔇.BlowupAxiom := by
  intro Z X i _ hnd
  have := isClosedImmersion_baseChange_map (k' := k') i
  have h1 := h _ _ ((baseChange k k').map i) (isNowhereDense_range_baseChange_map i hnd)
  obtain ⟨φ, hφ⟩ := exists_blowup_baseChange (k' := k') i
  have h2 : Injective (𝔇'.pull ((baseChange k k').map
      (SmoothProjectiveScheme.blowupHom i))) := by
    rw [← hφ, 𝔇'.pull_comp, AlgHom.coe_comp] at h1
    exact h1.of_comp
  apply injective_of_injective_baseChange F'
    (𝔇.pull (SmoothProjectiveScheme.blowupHom i)).toLinearMap
  have h4 : Injective ((Φ.iso _).toLinearMap ∘ₗ
      (𝔇.pull (SmoothProjectiveScheme.blowupHom i)).toLinearMap.baseChange F') := by
    rw [Φ.iso_comp_baseChange_pull (SmoothProjectiveScheme.blowupHom i), LinearMap.coe_comp]
    exact h2.comp (Φ.iso X).injective
  rw [LinearMap.coe_comp] at h4
  exact h4.of_comp

end FieldExtensionComparison

end Stacks.WeilCohomology
