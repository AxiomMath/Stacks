module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.EtaleModuleFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex

/-!
# Constructibility by Noetherian induction, and in distinguished triangles

Two devices used by the inductions of Stacks 0GKX and 0GKZ.

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isClosedImmersion`: on a scheme
  with Noetherian underlying space, a sheaf of `Λ`-modules is constructible as soon as its inverse
  image to a nonempty open of every nonempty reduced closed subscheme is constructible. This is
  the step "it suffices to find a dense open `U ⊆ S` such that the restriction to `U` is
  constructible; the restriction to `S ∖ U` is constructible by induction" of the source, as a
  Noetherian induction: the strata it produces are opens of closed subschemes, and they are
  assembled by Stacks 09YR.
* `Stacks.EtaleCohomology.prop_homology_obj₂_of_distTriang_plus`: a weak Serre class containing
  all cohomology objects of the outer vertices of a distinguished triangle of `D⁺` contains
  those of the middle vertex, by the five term exact sequence
  `H^{n-1}(T₃) → H^n(T₁) → H^n(T₂) → H^n(T₃) → H^{n+1}(T₁)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

universe u r

namespace Stacks.EtaleCohomology

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The middle vertex of a distinguished triangle of `D⁺`.** A weak Serre class containing all
cohomology objects of the first and third vertices of a distinguished triangle of `D⁺(C)`
contains those of the second. -/
theorem prop_homology_obj₂_of_distTriang_plus (P : ObjectProperty C) [P.IsWeakSerreClass]
    (T : Pretriangulated.Triangle (DerivedCategory.Plus C)) (hT : T ∈ distTriang _)
    (h₁ : ∀ i : ℤ, P ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₁))
    (h₃ : ∀ i : ℤ, P ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₃)) (n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor C n).obj T.obj₂) := by
  let T' := DerivedCategory.Plus.ι.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := DerivedCategory.Plus.ι.map_distinguished T hT
  have h₁' : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj T'.obj₁) := h₁
  have h₃' : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj T'.obj₃) := h₃
  change P ((DerivedCategory.homologyFunctor C n).obj T'.obj₂)
  exact ObjectProperty.prop_mid_of_exact₄
    (fun S hS a b c d => P.prop_obj₂_of_exact S hS a b c d)
    (f₀ := DerivedCategory.HomologySequence.δ T' (n - 1) n (by omega))
    (f₁ := (DerivedCategory.homologyFunctor C n).map T'.mor₁)
    (f₂ := (DerivedCategory.homologyFunctor C n).map T'.mor₂)
    (f₃ := DerivedCategory.HomologySequence.δ T' n (n + 1) rfl)
    (DerivedCategory.HomologySequence.δ_comp T' hT' (n - 1) n (by omega))
    (by rw [← Functor.map_comp, Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT',
      Functor.map_zero])
    (DerivedCategory.HomologySequence.comp_δ T' hT' n (n + 1) rfl)
    (DerivedCategory.HomologySequence.exact₁ T' hT' (n - 1) n (by omega))
    (DerivedCategory.HomologySequence.exact₂ T' hT' n)
    (DerivedCategory.HomologySequence.exact₃ T' hT' n (n + 1) rfl)
    (h₃' (n - 1)) (h₁' n) (h₃' n) (h₁' (n + 1))

end Triangle

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

section NoetherianInduction

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- **Constructibility by Noetherian induction.** Let `S` be a scheme of `B` whose underlying space
is Noetherian and `G` a sheaf of `Λ`-modules on `S`. Suppose that for every nonempty reduced closed
subscheme `i : Z ⟶ S` of `B` there is a nonempty open `v : V ⟶ Z` of `B` on which the inverse image
of `G` is constructible. Then `G` is constructible. -/
theorem isConstructibleEtaleModule_of_forall_isClosedImmersion (S : B.Scheme)
    [NoetherianSpace S.obj] (G : EtaleModules.{u, r} Λ S.obj)
    (h : ∀ (Z : B.Scheme) (i : Z ⟶ S), IsClosedImmersion (B.inclusion.map i) → IsReduced Z.obj →
      Nonempty Z.obj → ∃ (V : B.Scheme) (v : V ⟶ Z), IsOpenImmersion (B.inclusion.map v) ∧
        Nonempty V.obj ∧ IsBigSiteConstructibleEtaleModule B V Λ
          ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map (v ≫ i))).obj G)) :
    IsBigSiteConstructibleEtaleModule B S Λ G := by
  have : CompactSpace S.obj := NoetherianSpace.compactSpace S.obj
  have : QuasiSeparatedSpace S.obj := inferInstance
  let P : Set S.obj → Prop := fun A => ∃ (T : B.Scheme) (t : T ⟶ S),
    IsImmersion (B.inclusion.map t) ∧ Set.range (B.inclusion.map t).base = A ∧
      IsBigSiteConstructibleEtaleModule B T Λ
        ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map t)).obj G)
  have hP : ∀ Z : Set S.obj, IsClosed Z → (Set.univ ∩ Z).Nonempty →
      ∃ V : Set S.obj, IsOpen V ∧ (V ∩ Set.univ ∩ Z).Nonempty ∧ P (V ∩ Set.univ ∩ Z) := by
    intro Z hZ hne
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : TopologicalSpace.Closeds S.obj)
    have hZB : B.Contains I.subscheme :=
      Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact I.subschemeι S.property
    let ZB : B.Scheme := B.obj I.subscheme hZB
    let iB : ZB ⟶ S := ObjectProperty.homMk I.subschemeι
    have hrange : Set.range I.subschemeι.base = Z :=
      Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
    have hred : IsReduced ZB.obj := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    obtain ⟨z, hz⟩ := hne
    obtain ⟨z', hz'⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz.2
    obtain ⟨V, v, hv, hVne, hV⟩ := h ZB iB (inferInstanceAs (IsClosedImmersion I.subschemeι)) hred
      ⟨z'⟩
    have hopen : IsOpen (Set.range (B.inclusion.map v).base) :=
      (B.inclusion.map v).isOpenEmbedding.isOpen_range
    obtain ⟨V₀, hV₀, hpre⟩ :=
      (I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff).1 hopen
    refine ⟨V₀, hV₀, ?_, ⟨V, v ≫ iB, ?_, ?_, hV⟩⟩
    · obtain ⟨y⟩ := hVne
      refine ⟨I.subschemeι.base ((B.inclusion.map v).base y), ⟨⟨?_, trivial⟩, ?_⟩⟩
      · have : (B.inclusion.map v).base y ∈ I.subschemeι.base ⁻¹' V₀ := hpre ▸ ⟨y, rfl⟩
        exact this
      · exact hrange ▸ ⟨_, rfl⟩
    · have : IsOpenImmersion (B.inclusion.map v) := hv
      have : IsClosedImmersion (B.inclusion.map iB) :=
        inferInstanceAs (IsClosedImmersion I.subschemeι)
      change IsImmersion (B.inclusion.map v ≫ B.inclusion.map iB)
      infer_instance
    · change Set.range (B.inclusion.map v ≫ I.subschemeι).base = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hpre,
        Set.image_preimage_eq_inter_range, hrange, Set.inter_univ]
  have : NoetherianSpace (B.inclusion.obj S) := inferInstanceAs (NoetherianSpace S.obj)
  obtain ⟨n, A, hlc, -, hPA, -, hcov⟩ :=
    exists_locallyClosed_partition_of_noetherianSpace (Set.univ : Set S.obj) isOpen_univ P hP
  choose T t ht hrng hcon using hPA
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B S Λ _ T t ht
    (fun k => (hrng k) ▸ isConstructible_of_isLocallyClosed (hlc k)) ?_
    (fun k => isConstructibleModuleSheaf_congr B Λ (T k)
      (etaleModulesToSmallEtalePullbackIso B Λ (t k) G) (hcon k))
  rw [hcov]
  exact Set.iUnion_congr fun k => (hrng k).symm

end NoetherianInduction

end Stacks.EtaleCohomology

end
