module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ReducedInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratumPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.LocallyConstantReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothReduction
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.Topology.Irreducible.LocallyClosedCoverParts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Theorem 03SC for constructible sheaves killed by a prime

In Situation 0A52 with `X` reduced, a constructible abelian sheaf `F` killed by a prime `ℓ`
satisfies statements (1) -- (8), granted Lemma 0A5B for `Z/ℓ` on smooth curves.
This is the stratification step of the proof of Theorem 03SC.

## Main results

* `AlgebraicGeometry.Scheme.exists_comp_eq_of_isImmersion_of_isReduced`: a morphism from a
  reduced scheme whose image lies in the image of an immersion factors through it.
* `Stacks.EtaleCohomology.isFiniteLocallyConstant_etaleAbelianInverseImage_of_range_subset`: a
  sheaf which is finite locally constant on the strata of a constructible stratification is finite
  locally constant on every reduced open contained in one stratum, read on Mathlib's site.
* `Stacks.EtaleCohomology.curveStatements_of_isConstructible_of_nsmul_eq_zero`: **the
  constructible `ℓ`-torsion case of Theorem 03SC**, for `X` reduced, granted Lemma 0A5B.
* `Stacks.EtaleCohomology.IsConstructibleOnEveryBigSite.exists_nsmul_id_eq_zero`: a constructible
  sheaf is killed by a positive integer (it is torsion and compact, Tag 09Z4).
* `Stacks.EtaleCohomology.curveStatements_of_isConstructible_of_isReduced`: **Theorem 03SC for
  constructible sheaves**, for `X` reduced, by induction on an integer killing the sheaf.

## Implementation notes

The proof is the one of the source. By Tag 095E the sheaf `F` is finite locally constant on the
strata of one finite partition of `X` into locally closed subschemes. Inside the stratum through
the generic point of each irreducible component one finds an irreducible open, and these opens
can be taken pairwise disjoint with dense union `W`
(`Stacks.Topology.Irreducible.exists_isIrreducible_opens_of_isLocallyClosed_cover`). On each of
them `F` is finite locally constant, so Lemma 03SD applies to the extension by zero of its
restriction; the short exact sequences of extension by zero along a disjoint union of two opens
(`Stacks.EtaleCohomology.exists_shortExact_extensionByZero_of_isCompl`) and Lemma 0A5C give the
statements for `j_! j^{-1} F`, `j : W ⟶ X`, and the backward direction of Tag 0GJA gives them for
`F`.

**No `@[stacks]` attribute**: Lemma 0A5B enters as a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.Scheme

/-- **Lifting through an immersion.** A morphism `j : V ⟶ X` from a reduced scheme whose image
lies in the image of an immersion `i : P ⟶ X` factors through `i`: the base change of `i` along
`j` is a surjective immersion onto the reduced scheme `V`, hence an isomorphism. -/
@[ega "I 5.1.5" "more general"]
theorem exists_comp_eq_of_isImmersion_of_isReduced {P V X : Scheme.{u}} (i : P ⟶ X)
    [IsImmersion i] (j : V ⟶ X) [IsReduced V] (h : Set.range j.base ⊆ Set.range i.base) :
    ∃ g : V ⟶ P, g ≫ i = j := by
  have hsurj : Set.range (pullback.snd i j).base = Set.univ := by
    rwa [Scheme.Pullback.range_snd, Set.preimage_eq_univ_iff]
  have : Surjective (pullback.snd i j) := ⟨Set.range_eq_univ.1 hsurj⟩
  have : IsClosedImmersion (pullback.snd i j) :=
    .of_isPreimmersion _ (by simp [hsurj])
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i j)
  exact ⟨inv (pullback.snd i j) ≫ pullback.fst i j, by simp [pullback.condition]⟩

end AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- **Finite local constancy on a reduced open inside a stratum.** Let `s` be a constructible
stratification of `X` on whose strata the abelian sheaf `F` (read on the site of Tag 021B) is
finite locally constant. For an open immersion `j : V ⟶ X` from a reduced scheme with image
inside one stratum, `j^{-1} F` is finite locally constant on Mathlib's small étale site of `V`. -/
theorem isFiniteLocallyConstant_etaleAbelianInverseImage_of_range_subset (B : BigEtaleSite.{u})
    (X : B.Scheme) {V : Scheme.{u}} (F : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : ConstructibleStratification B X ⊤)
    (hs : ∀ i, ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((AlgebraicGeometry.smallEtaleBaseChange B (s.inclusion i)).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj
          ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj F)))
    (j : V ⟶ X.obj) [IsOpenImmersion j] [IsReduced V] (t : Fin s.n)
    (ht : Set.range j.base ⊆ Set.range (B.inclusion.map (s.inclusion t)).base) :
    ConstantSheaf.IsFiniteLocallyConstant V.smallEtaleTopology
      ((etaleAbelianInverseImage.{u, 0} j).obj F) := by
  have hV : B.Contains V := (Scheme.size_le_of_isOpenImmersion j).trans_lt X.property
  have := s.isImmersion t
  obtain ⟨g, hg⟩ := Scheme.exists_comp_eq_of_isImmersion_of_isReduced
    (B.inclusion.map (s.inclusion t)) j ht
  let gB : B.obj V hV ⟶ s.piece t := ObjectProperty.homMk g
  let jB : B.obj V hV ⟶ X := ObjectProperty.homMk j
  have hgB : gB ≫ s.inclusion t = jB := by
    ext1
    exact hg
  have hB := isFiniteLocallyConstant_smallEtaleSheafPullback_comp B AddCommGrpCat.{u + 1}
    (s.inclusion t) gB _ (hs t)
  rw [hgB] at hB
  rw [SmallEtale.isFiniteLocallyConstant_abelian_iff_toEtaleSite B V hV]
  exact ConstantSheaf.isFiniteLocallyConstant_congr _
    ((SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{u + 1} jB
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map jB))
      (Functor.sheafAdjunctionContinuous _ _ _ _)).app F) (hF := hB)

/-- **Lemma 0A5C along a disjoint union of two opens.** For an open immersion `j : V ⟶ X` and a
decomposition of `V` into complementary opens `A` and `B`, if statements (1) -- (8) hold for the
extensions by zero of the restrictions of `F` to `A` and to `B`, they hold for `j_! j^{-1} F`. -/
theorem CurveStatements.extensionByZero_etaleAbelianInverseImage_of_isCompl {k : Type u}
    [Field k] {X V : Scheme.{u}} [IsNoetherian X] (π : X ⟶ Spec (.of k)) (j : V ⟶ X)
    [IsOpenImmersion j] [IsNoetherian V] {A B : V.Opens} (hAB : IsCompl A B)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} (A.ι ≫ j)).obj
      ((etaleAbelianInverseImage.{u, 0} (A.ι ≫ j)).obj F)))
    (hB : CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} (B.ι ≫ j)).obj
      ((etaleAbelianInverseImage.{u, 0} (B.ι ≫ j)).obj F))) :
    CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj
      ((etaleAbelianInverseImage.{u, 0} j).obj F)) := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_shortExact_extensionByZero_of_isCompl j hAB ((etaleAbelianInverseImage.{u, 0} j).obj F)
  refine (CurveStatements.of_shortExact hT (hA.of_iso ?_) (hB.of_iso ?_)).of_iso e₂
  · exact (extensionByZero.{u, 0} (A.ι ≫ j)).mapIso
      ((etaleAbelianInverseImageCompIso.{u, 0} A.ι j).app F ≪≫
        (etaleAbelianInverseImageRestrictionIso.{u, 0} A.ι).app _) ≪≫ e₁.symm
  · exact (extensionByZero.{u, 0} (B.ι ≫ j)).mapIso
      ((etaleAbelianInverseImageCompIso.{u, 0} B.ι j).app F) ≪≫ e₃.symm

/-- **Lemma 0A5C along a finite disjoint union of opens.** Let `W` be a family of pairwise
disjoint opens of `X` such that statements (1) -- (8) hold for `j_! j^{-1} F` for every open
immersion `j` onto one `W i`. Then they hold for `j_! j^{-1} F` for every open immersion `j` onto
a finite union of the `W i`. -/
theorem CurveStatements.extensionByZero_etaleAbelianInverseImage_of_range_eq_biUnion
    {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X] (π : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {ι : Type*} [DecidableEq ι]
    {W : ι → Set X} (hWo : ∀ i, IsOpen (W i)) (hWdisj : Pairwise (Function.onFun Disjoint W))
    (hW : ∀ (i : ι) (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j], Set.range j.base = W i →
      CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj
        ((etaleAbelianInverseImage.{u, 0} j).obj F)))
    (S : Finset ι) :
    ∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j], Set.range j.base = ⋃ i ∈ S, W i →
      CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj
        ((etaleAbelianInverseImage.{u, 0} j).obj F)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro V j _ hj
    have : IsEmpty V := by simpa using hj
    exact CurveStatements.of_isZero π (isZero_extensionByZero_of_isEmpty j _)
  | insert a S ha ih =>
    intro V j _ hj
    have : CompactSpace V := ⟨(j.isOpenEmbedding.isInducing.isCompact_iff).2
      (by rw [Set.image_univ]; exact TopologicalSpace.NoetherianSpace.isCompact _)⟩
    have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion j
    have : IsNoetherian V := ⟨⟩
    let A : V.Opens := j ⁻¹ᵁ ⟨W a, hWo a⟩
    let Bo : V.Opens := j ⁻¹ᵁ ⟨⋃ i ∈ S, W i, isOpen_biUnion fun i _ ↦ hWo i⟩
    have hrange : ∀ x : V, j.base x ∈ W a ∪ ⋃ i ∈ S, W i := fun x ↦ by
      have : j.base x ∈ Set.range j.base := ⟨x, rfl⟩
      rw [hj] at this
      simpa using this
    have hAB : IsCompl A Bo := by
      refine ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
      · ext x
        simp only [A, Bo, TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage,
          TopologicalSpace.Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
          TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and,
          Set.mem_iUnion, not_exists]
        intro hxa i hi hxi
        exact Set.disjoint_left.1 (hWdisj (fun h : a = i ↦ ha (h ▸ hi))) hxa hxi
      · ext x
        simp only [A, Bo, TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_preimage,
          TopologicalSpace.Opens.coe_mk, Set.mem_union, Set.mem_preimage,
          TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
        simpa using hrange x
    refine CurveStatements.extensionByZero_etaleAbelianInverseImage_of_isCompl π j hAB F
      (hW a _ _ ?_) (ih _ _ ?_) <;>
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_mk, Set.image_preimage_eq_inter_range,
        hj]
    · exact Set.inter_eq_left.2 fun x hx ↦ by simp [hx]
    · exact Set.inter_eq_left.2 fun x hx ↦ by
        simp only [Finset.set_biUnion_insert]
        exact Or.inr hx

/-- A scheme quasi-compact and locally of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_of_quasiCompact {k : Type u} [Field k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π] :
    IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian π
  have := QuasiCompact.compactSpace_of_compactSpace π
  ⟨⟩

/-- **Theorem 03SC for a constructible sheaf killed by a prime, `X` reduced, granted Lemma 0A5B
for `Z/ℓ`.** Let `X` be a reduced separated scheme of finite type and dimension at
most one over an algebraically closed field `k`, `ℓ` a prime and `F` a constructible abelian sheaf
on `X_étale` killed by `ℓ`. If statements (1) -- (8) hold for `Z/ℓ` on every smooth curve over `k`,
they hold for `F`. -/
theorem curveStatements_of_isConstructible_of_nsmul_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] {ℓ : ℕ} (hℓ : ℓ.Prime) {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) (hℓF : ℓ • 𝟙 F = 0)
    (hbase : CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) :
    CurveStatements.{u, 0, u + 1} π F := by
  classical
  have := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  obtain ⟨s, hs⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B (B.obj X hX) _).1
    (hF B hX)
  have hlc : ∀ t, IsLocallyClosed (Set.range (B.inclusion.map (s.inclusion t)).base) :=
    fun t ↦ by
      have := s.isImmersion t
      exact (B.inclusion.map (s.inclusion t)).isLocallyClosed_range
  have : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  have := Fintype.ofFinite (irreducibleComponents X)
  obtain ⟨W, hWo, hWirr, hWdisj, hWdense, hWsub⟩ :=
    Stacks.Topology.Irreducible.exists_isIrreducible_opens_of_isLocallyClosed_cover (X := X)
      (fun t ↦ Set.range (B.inclusion.map (s.inclusion t)).base) hlc s.covers.symm
  have hpiece : ∀ (Z : irreducibleComponents X) (V : Scheme.{u}) (j : V ⟶ X)
      [IsOpenImmersion j], Set.range j.base = W Z →
      CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj
        ((etaleAbelianInverseImage.{u, 0} j).obj F)) := by
    intro Z V j _ hj
    obtain ⟨t, ht⟩ := hWsub Z
    have : IsReduced V := isReduced_of_isOpenImmersion j
    have : ConnectedSpace V := by
      rw [connectedSpace_iff_univ]
      have h := (hWirr Z).isConnected
      rw [← hj, ← Set.image_univ] at h
      exact ⟨Set.image_nonempty.1 h.1, j.isOpenEmbedding.isInducing.isPreconnected_image.1 h.2⟩
    have := isFiniteLocallyConstant_etaleAbelianInverseImage_of_range_subset B (B.obj X hX) F s
      hs j t (hj ▸ ht)
    exact curveStatements_extensionByZero_of_isFiniteLocallyConstant hℓ π hdim j _
      (nsmul_id_eq_zero_map _ hℓF) hbase
  let U : X.Opens := ⟨⋃ Z, W Z, isOpen_iUnion hWo⟩
  have hU := CurveStatements.extensionByZero_etaleAbelianInverseImage_of_range_eq_biUnion π F
    hWo hWdisj hpiece Finset.univ U.toScheme U.ι (by
      rw [Scheme.Opens.range_ι]
      simp only [Finset.mem_univ, Set.iUnion_true]
      rfl)
  exact curveStatements_of_curveStatements_extensionByZero_of_dense π hdim U.ι
    (by rwa [Scheme.Opens.range_ι]) F
    (hU.of_iso ((extensionByZero.{u, 0} U.ι).mapIso
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} U.ι).app F)))

/-- An object which is a retract of the kernel of `n • 𝟙` on it, compatibly with the kernel
inclusion, is killed by `n`. -/
theorem nsmul_id_eq_zero_of_comp_kernel_ι_eq_id {C : Type*} [Category C] [Preadditive C]
    {F : C} {n : ℕ} [HasKernel (n • 𝟙 F)] (g : F ⟶ kernel (n • 𝟙 F))
    (hg : g ≫ kernel.ι (n • 𝟙 F) = 𝟙 F) : n • 𝟙 F = 0 :=
  calc n • 𝟙 F = n • (g ≫ kernel.ι (n • 𝟙 F)) := by rw [hg]
    _ = g ≫ (kernel.ι (n • 𝟙 F) ≫ (n • 𝟙 F)) := by
      rw [Preadditive.comp_nsmul, Preadditive.comp_nsmul, Category.comp_id]
    _ = 0 := by rw [kernel.condition, comp_zero]

/-- **A constructible abelian sheaf is killed by a positive integer.** On a quasi-compact
quasi-separated scheme, a constructible abelian sheaf is torsion, hence the union of its
subsheaves `F[n!]`; being a compact object (Tag 09Z4), it equals one of them. -/
theorem exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf (B : BigEtaleSite.{u})
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) : ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  have := SmallEtale.isGrothendieckAbelian_sheaf_succ B X.obj X.property
  have : ∀ (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} ℤ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
    fun S T g => Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence
      (AlgebraicGeometry.smallEtaleBaseChange B g) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
    fun T V => Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ
      (SmallEtale.topology B T.obj T.property) V
  have hFP : IsFinitelyPresentable.{u + 1} F := isFinitelyPresentable_of_isConstructibleAbelianSheaf
    B X (hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B X) F hF
  have : IsIso (Stacks.Torsion.torsionFiltrationDesc
      (SmallEtale.topology B X.obj X.property) F) :=
    Stacks.Torsion.isIso_torsionFiltrationDesc _ F
      (torsionSheafProperty_of_isConstructibleAbelianSheaf B X F hF)
  have hc : IsColimit (Cocone.mk F (Stacks.Torsion.torsionFiltrationι
      (SmallEtale.topology B X.obj X.property) F)) :=
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (Stacks.Torsion.torsionFiltrationDesc
        (SmallEtale.topology B X.obj X.property) F))
        (fun j => Stacks.Torsion.ι_torsionFiltrationDesc _ F j))
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have : IsCardinalFiltered (ULift.{u + 1} ℕ) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff _).2 inferInstance
  obtain ⟨m, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit Cardinal.aleph0 hc (𝟙 F)
  exact ⟨m.down.factorial, Nat.factorial_pos _, nsmul_id_eq_zero_of_comp_kernel_ι_eq_id f hf⟩

/-- **A sheaf constructible on every big étale site is killed by a positive integer.** -/
theorem IsConstructibleOnEveryBigSite.exists_nsmul_id_eq_zero {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleOnEveryBigSite F) : ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨n, hn, h⟩ := exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B (B.obj X hX)
    (e.inverse.obj F) (hF B hX)
  exact ⟨n, hn, nsmul_id_eq_zero_of_iso (e.counitIso.app F) (nsmul_id_eq_zero_map e.functor h)⟩

/-- **Reduction of the constructible case to sheaves killed by a prime.** On a Noetherian scheme
over a field, if statements (1) -- (8) hold for every constructible sheaf killed by a prime, they
hold for every constructible sheaf.

`F` is killed by some `n > 0`; by induction on `n`, with `ℓ` a prime factor of `n`, the sequence
`0 → F[ℓ] → F → ℓF → 0` and Lemma 0A5C reduce to `F[ℓ]`, killed by `ℓ`, and `ℓF`, killed by
`n / ℓ`, both constructible as subsheaves of `F`. -/
theorem CurveStatements.of_isConstructible_of_forall_prime {k : Type u} [Field k]
    {X : Scheme.{u}} [IsNoetherian X] (π : X ⟶ Spec (.of k))
    (hprime : ∀ ℓ : ℕ, ℓ.Prime → ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsConstructibleOnEveryBigSite G → ℓ • 𝟙 G = 0 → CurveStatements.{u, 0, u + 1} π G)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) :
    CurveStatements.{u, 0, u + 1} π F := by
  obtain ⟨n, hn, hnF⟩ := hF.exists_nsmul_id_eq_zero
  induction n using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact CurveStatements.of_isZero π
        ((IsZero.iff_id_eq_zero F).2 (by simpa using hnF))
    · set ℓ := n.minFac
      have hℓ : ℓ.Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hmn : m < n := by
        rw [hm]
        exact lt_mul_left hm0 hℓ.one_lt
      let f : F ⟶ F := ℓ • 𝟙 F
      let S := ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (cokernel.condition _)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
      have hK : ℓ • 𝟙 (kernel f) = 0 := by
        rw [← cancel_mono (kernel.ι f)]
        simp only [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
        rw [← Category.comp_id (kernel.ι f), ← Preadditive.comp_nsmul]
        exact kernel.condition f
      have hQ : m • 𝟙 (Abelian.coimage f) = 0 := by
        rw [← cancel_mono (Abelian.factorThruCoimage f), ← cancel_epi (Abelian.coimage.π f)]
        simp only [Preadditive.nsmul_comp, Category.id_comp, zero_comp, comp_zero,
          Preadditive.comp_nsmul, Abelian.coimage.fac]
        rw [show m • f = n • 𝟙 F by rw [smul_smul, hm, mul_comm], hnF]
      have h₁ : CurveStatements.{u, 0, u + 1} π S.X₁ :=
        hprime ℓ hℓ _ (hF.of_mono (kernel.ι f)) hK
      have h₃ : CurveStatements.{u, 0, u + 1} π S.X₃ :=
        ih m hmn _ (hF.of_mono (Abelian.factorThruCoimage f)) hm0 hQ
      exact CurveStatements.of_shortExact hS h₁ h₃

/-- **Theorem 03SC for constructible sheaves on a reduced `X`, granted Lemma 0A5B for `Z/ℓ`
for every prime `ℓ`.** Let `X` be a reduced separated scheme of finite type and
dimension at most one over an algebraically closed field `k` and `F` a constructible abelian sheaf
on `X_étale`. Then statements (1) -- (8) hold for `F`. -/
theorem curveStatements_of_isConstructible_of_isReduced {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] [IsReduced X] (hdim : topologicalKrullDim X ≤ 1)
    (hbase : ∀ ℓ : ℕ, ℓ.Prime →
      CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) :
    CurveStatements.{u, 0, u + 1} π F :=
  have := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  CurveStatements.of_isConstructible_of_forall_prime π (fun ℓ hℓ G hG hℓG ↦
    curveStatements_of_isConstructible_of_nsmul_eq_zero hℓ π hdim G hG hℓG (hbase ℓ hℓ)) F hF

/-- **Theorem 03SC for constructible sheaves, granted Lemma 0A5B for `Z/ℓ` for every prime
`ℓ`.** Let `X` be a separated scheme of finite type and dimension at most one over an
algebraically closed field `k` and `F` a constructible abelian sheaf on `X_étale`. Then statements
(1) -- (8) hold for `F`.

For `F` killed by a prime this is reduced to the reduction `X_red` (Tag 03SI): `F` is
`i_* i^{-1} F` for the universal homeomorphism `i : X_red ⟶ X`, and Lemma 0A5D for the finite
morphism `i` carries the statements for `i^{-1} F` to `i_* i^{-1} F`. -/
theorem curveStatements_of_isConstructible {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    (hbase : ∀ ℓ : ℕ, ℓ.Prime →
      CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) :
    CurveStatements.{u, 0, u + 1} π F := by
  have := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  refine CurveStatements.of_isConstructible_of_forall_prime π (fun ℓ hℓ G hG hℓG ↦ ?_) F hF
  let i := X.reductionι
  have hdim' : topologicalKrullDim X.reduction ≤ 1 := by
    rwa [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.isHomeomorph_reductionι X)]
  have hGi : IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} i).obj G) :=
    hG.etaleAbelianInverseImage i
  have hℓGi : ℓ • 𝟙 ((etaleAbelianInverseImage.{u, 0} i).obj G) = 0 :=
    nsmul_id_eq_zero_map _ hℓG
  have hpush := CurveStatements.directImage_of_nsmul_eq_zero π i hℓ hℓGi
    (fun B hX _ _ ↦ hGi B hX)
    (curveStatements_of_isConstructible_of_nsmul_eq_zero hℓ (i ≫ π) hdim' _ hGi hℓGi
      (hbase ℓ hℓ))
  have := etaleAbelianInverseImage_isEquivalence_of_universalHomeomorphism.{u, 0} i
  exact hpush.of_iso (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app G)).symm

end Stacks.EtaleCohomology
