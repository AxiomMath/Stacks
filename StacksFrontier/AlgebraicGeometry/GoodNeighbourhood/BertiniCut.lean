module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodLocus
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GeneralMember
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniRationalMember
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisorOpenGlue
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniVanishingJet
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneralPosition
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniCutStep
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisorsOnX
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemFiniteness
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.Topology.Irreducible.SingletonComponent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One Bertini cut of the locus where a closed subscheme is smooth

Let `X` be proper over an algebraically closed field `k`, `ℒ` invertible, and `V_n ⊆ Γ(X, ℒ^{⊗ n})`
the sections vanishing on a closed subscheme `Z = V(I)` supported in one closed point `c` (or
empty), with the two conclusions of [Stacks, Tag 0FD5]: `V_n` generates `ℒ^{⊗ n}` off `Z` and
embeds `X ∖ Z`. Let `T ⊆ X` be any closed subscheme and `G ⊆ T` the open where `T` is smooth of
relative dimension `r + 1`. Then a general member `v ∈ V_n` cuts `G` in a scheme smooth of
relative dimension `r`: at every point `z` of `X` where `T` is smooth of relative dimension `r + 1`
and `v` vanishes, `T ∩ Z(v)` is smooth of relative dimension `r`. "General" means: for the
`k`-points of a nonempty open of the parameter space of `V_n`, off finitely many hyperplanes.

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.CutGood`: the property that a section cuts the locus where
  `T` is smooth of relative dimension `r + 1` in a scheme smooth of relative dimension `r`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.exists_cutGood`: the general member is good.

## References

* SGA 4, Exposé XI, 3.3.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.SectionsVanishingOnSubscheme

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) {L : X.Modules}
  [IsInvertibleModule X L] (n : ℤ)

/-- **The cut of the good locus by one section.** At every point where `T` is smooth of relative
dimension `r + 1` and `v` vanishes, `T ∩ Z(v)` is smooth of relative dimension `r`. -/
def CutGood (T : X.IdealSheafData) (r : ℕ) (v : Γ(tensorPowModule X L n, ⊤)) : Prop :=
  ∀ z : X, SubschemeSmoothAt p T (r + 1) z →
    z ∈ (zeroScheme X (tensorPowModule X L n) v).support →
    SubschemeSmoothAt p (T ⊔ zeroScheme X (tensorPowModule X L n) v) r z

/-- The global section underlying a member of the linear system `V_n`. -/
abbrev vsec {I : X.IdealSheafData} (v : vanishingSections k p I L n) :
    Γ(tensorPowModule X L n, ⊤) :=
  ((v : Stacks.Bertini.globalSections k p (tensorPowModule X L n)) : Γ(tensorPowModule X L n, ⊤))

/-- In a scheme smooth of positive relative dimension over a field, with noetherian underlying
space, the generic point of an irreducible component is not a closed point. -/
theorem not_isClosed_singleton_of_mem_genericPoints {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    (r : ℕ) [SmoothOfRelativeDimension (r + 1) f] [TopologicalSpace.NoetherianSpace G] (η : G)
    (hη : closure ({η} : Set G) ∈ irreducibleComponents G) : ¬ IsClosed ({η} : Set G) := by
  intro hcl
  rw [hcl.closure_eq] at hη
  have hopen := Stacks.Topology.Irreducible.isOpen_singleton_of_mem_irreducibleComponents
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents η hη
  have hdim := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field (r + 1) f η
  have hemb : Topology.IsOpenEmbedding (Subtype.val : ({η} : Set G) → G) :=
    hopen.isOpenEmbedding_subtypeVal
  have h1 := hemb.topologicalKrullDimAt_eq ⟨η, rfl⟩
  have h2 : topologicalKrullDimAt ({η} : Set G) ⟨η, rfl⟩ ≤ 0 := by
    have : DiscreteTopology ({η} : Set G) := by
      have : Subsingleton ({η} : Set G) := (Set.subsingleton_singleton).coe_sort
      infer_instance
    calc topologicalKrullDimAt ({η} : Set G) ⟨η, rfl⟩ ≤ topologicalKrullDim ({η} : Set G) :=
          topologicalKrullDimAt_le_topologicalKrullDim _
      _ = 0 := topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
  rw [← h1, hdim] at h2
  exact absurd h2 (by norm_cast)

/-- **The `1`-jet condition at a closed point is a hyperplane condition on a subsystem of
codimension at most the local dimension.** For a family of divisors `D`, smooth over an
algebraically closed field, with hypothesis (3) of [Stacks, Tag 0FD6], a closed point `x` of local
dimension `m`, and a linear map `T : V → M` with `dim M ≤ m`, the members of `ker T` whose germ at
`x` lies in `𝔪_x²ℒ_x` lie in a proper subspace. -/
theorem exists_ne_top_germ_notMem_maximalSqSmul (D : Stacks.Bertini.FamilyDivisors.{u, u})
    [IsAlgClosed D.k] [Smooth D.toBase] {q : ℕ} {b : Module.Basis (Fin (q + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    {m : ℕ} (hdim : topologicalKrullDimAt D.X x = (m : WithBot ℕ∞))
    {M : Type u} [AddCommGroup M] [Module D.k M] [Module.Finite D.k M]
    (T : D.V →ₗ[D.k] M) (hM : Module.finrank D.k M ≤ m) :
    ∃ P : Submodule D.k (LinearMap.ker T), P ≠ ⊤ ∧ ∀ v : LinearMap.ker T, v ∉ P →
      (D.L.presheaf.Γgerm x).hom (D.sectionOf (v : D.V)) ∉
        Stacks.ImmersionEvaluationSurjective.maximalSqSmul D.L x := by
  have hev := D.evalVector_ne_zero_restrictSystem_ker himm hx hdim T hM
  refine ⟨LinearMap.ker ((D.restrictSystem (LinearMap.ker T)).evalVector x), fun htop => hev
    (LinearMap.ker_eq_top.mp htop), fun v hv => ?_⟩
  exact ((D.restrictSystem (LinearMap.ker T)).notMem_maximalSqSmul_iff_evalVector_ne_zero x v).mpr
    hv

/-- `AlgebraicGeometry.GoodNeighbourhood.exists_ne_top_germ_notMem_maximalSqSmul` for a system
restricted along an immersion `g : Y ⟶ X` with `Y` smooth over the base. -/
theorem exists_ne_top_germ_notMem_maximalSqSmul_pullbackAlong
    (D : Stacks.Bertini.FamilyDivisors.{u, u}) [IsAlgClosed D.k] {Y : Scheme.{u}} (g : Y ⟶ D.X)
    [IsImmersion g] [Smooth (g ≫ D.toBase)] {q : ℕ} {b : Module.Basis (Fin (q + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb) {x : Y} (hx : IsClosed ({x} : Set Y))
    {m : ℕ} (hdim : topologicalKrullDimAt Y x = (m : WithBot ℕ∞))
    {M : Type u} [AddCommGroup M] [Module D.k M] [Module.Finite D.k M]
    (T : D.V →ₗ[D.k] M) (hM : Module.finrank D.k M ≤ m) :
    ∃ P : Submodule D.k (LinearMap.ker T), P ≠ ⊤ ∧ ∀ v : LinearMap.ker T, v ∉ P →
      (((Scheme.Modules.pullback g).obj D.L).presheaf.Γgerm x).hom
          (pullbackGlobalSections g D.L (D.sectionOf (v : D.V))) ∉
        Stacks.ImmersionEvaluationSurjective.maximalSqSmul ((Scheme.Modules.pullback g).obj D.L)
          x := by
  have : Smooth (D.pullbackAlong g).toBase := ‹Smooth (g ≫ D.toBase)›
  have : IsAlgClosed (D.pullbackAlong g).k := ‹IsAlgClosed D.k›
  let : Module (D.pullbackAlong g).k M := ‹Module D.k M›
  have : Module.Finite (D.pullbackAlong g).k M := ‹Module.Finite D.k M›
  exact exists_ne_top_germ_notMem_maximalSqSmul (D.pullbackAlong g)
    (Stacks.Bertini.FamilyDivisors.isImmersive_pullbackAlong g himm) hx hdim T hM

/-- **One Bertini cut of the good locus.** Let `X` be proper over an algebraically closed field,
`V_n` the sections of `ℒ^{⊗ n}` vanishing on `Z = V(I)` with `|Z| ⊆ {c}` for a closed point `c`,
generating off `Z` and embedding `X ∖ Z`, and let the complete linear system be immersive. Let
`T` be a closed subscheme and `r : ℕ`, with `dim_k Γ(Z, ℒ^{⊗ n}|_Z) ≤ r + 1` in case `c ∈ Z`.
Then there are a nonempty open `U` of the parameter space of `V_n` and finitely many nonzero
linear forms `ℓ` on `V_n` such that every member `v = Σ aⱼ bⱼ` with `a` a `k`-point of `U` and
`ℓ(v) ≠ 0` for all `ℓ` cuts the locus where `T` is smooth of relative dimension `r + 1` in a scheme
smooth of relative dimension `r`. -/
@[sga "4 XI 2.1" "special case"]
theorem exists_cutGood [IsAlgClosed k] [IsProper p] (I : X.IdealSheafData) (c : X)
    (hc : IsClosed ({c} : Set X)) (hI : ∀ y ∈ I.support, y = c)
    (hgen : GeneratesOffSupport k p I L n)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k p I L n)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k p b hgen))
    {q : ℕ} {b' : Module.Basis (Fin (q + 1)) k
      (Stacks.Bertini.globalSections k p (tensorPowModule X L n))}
    {hb' : (ambientFamilyDivisors k p (L := L) n).GeneratesBy b'}
    (himm' : (ambientFamilyDivisors k p (L := L) n).IsImmersive b' hb')
    (T : X.IdealSheafData) (r : ℕ)
    (hfin : c ∈ I.support → Module.finrank k (subschemeSections k p I (L := L) n) ≤ r + 1) :
    GeneralIn k (vanishingSections k p I L n) (fun v => CutGood p n T r (vsec p n v)) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace T.subscheme := QuasiCompact.compactSpace_of_compactSpace T.subschemeι
  have : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.subschemeι ≫ p)
  have : IsNoetherian T.subscheme := {}
  set M := tensorPowModule X L n
  set G := goodLocus p T (r + 1)
  set ιG : G.toScheme ⟶ X := G.ι ≫ T.subschemeι
  set fG : G.toScheme ⟶ Spec (.of k) := ιG ≫ p
  have hGsm : SmoothOfRelativeDimension (r + 1) fG := by
    simpa only [fG, ιG, Category.assoc] using smoothOfRelativeDimension_goodLocus p T (r + 1)
  have : Smooth fG := SmoothOfRelativeDimension.smooth (r + 1) fG
  have hιGinj : Function.Injective ιG.base := fun a b h =>
    G.ι.isOpenEmbedding.injective (T.subschemeι.isClosedEmbedding.injective h)
  have : IsImmersion ιG := AlgebraicGeometry.IsImmersion.comp G.ι T.subschemeι
  have : TopologicalSpace.NoetherianSpace G.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (G : Set T.subscheme))
  set O := openComplement I
  set Wo : G.toScheme.Opens := ιG ⁻¹ᵁ O
  have hrng : Set.range (Wo.ι ≫ ιG).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact y.2
  set g₁ : Wo.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (Wo.ι ≫ ιG) hrng
  have hg₁ : g₁ ≫ O.ι = Wo.ι ≫ ιG := IsOpenImmersion.lift_fac _ _ _
  have : IsImmersion g₁ := by
    have : IsImmersion (g₁ ≫ O.ι) := by
      rw [hg₁]; exact AlgebraicGeometry.IsImmersion.comp Wo.ι ιG
    exact (AlgebraicGeometry.IsImmersion.comp_iff g₁ O.ι).mp this
  set D₁ := cutFamily k p I L n g₁
  have hD₁base : D₁.toBase = Wo.ι ≫ fG := by
    show g₁ ≫ O.ι ≫ p = Wo.ι ≫ ιG ≫ p
    rw [← Category.assoc, hg₁, Category.assoc]
  have : Smooth D₁.toBase := by
    rw [hD₁base]
    exact MorphismProperty.comp_mem @Smooth _ _ (inferInstance : Smooth Wo.ι) ‹Smooth fG›
  obtain ⟨U, hUne, hU⟩ := D₁.forGeneral_smooth_specializedDivisor (generates_cutFamily g₁ hgen)
    (fun N b => isImmersive_cutFamily g₁ hgen himm N b)
  let E : Set G.toScheme := {η | η ∈ genericPoints G.toScheme ∧ ιG η ∉ I.support}
  have : Finite E := ((genericPoints.finite
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset
      fun η hη => hη.1).to_subtype
  let C : Type u := {y : G.toScheme // ιG y = c ∧ c ∈ I.support}
  have : Subsingleton C := ⟨fun a b => Subtype.ext (hιGinj (a.2.1.trans b.2.1.symm))⟩
  have : Finite C := Finite.of_subsingleton
  have hclosed : ∀ w : G.toScheme, ιG w = c → IsClosed ({w} : Set G.toScheme) := by
    intro w hw
    have : ({w} : Set G.toScheme) = ιG.base ⁻¹' {c} := by
      ext w'
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hw, fun h => hιGinj (h.trans hw.symm)⟩
    rw [this]; exact hc.preimage ιG.continuous
  have hD₂ : ∀ y : C, ∃ P : Submodule k (vanishingSections k p I L n), P ≠ ⊤ ∧
      ∀ v ∉ P, ((((Scheme.Modules.pullback ιG).obj (tensorPowModule X L n))).presheaf.Γgerm
        y.1).hom (pullbackGlobalSections ιG (tensorPowModule X L n) (vsec p n v)) ∉
          Stacks.ImmersionEvaluationSurjective.maximalSqSmul
            ((Scheme.Modules.pullback ιG).obj (tensorPowModule X L n)) y.1 := by
    intro y
    have hcl := hclosed y.1 y.2.1
    have : Smooth (ιG ≫ (ambientFamilyDivisors k p (L := L) n).toBase) := ‹Smooth fG›
    obtain ⟨P, hP, hPg⟩ := exists_ne_top_germ_notMem_maximalSqSmul_pullbackAlong
      (ambientFamilyDivisors k p (L := L) n) ιG himm' hcl
      (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field (r + 1) fG _)
      (restrictionMap k p I (tensorPowModule X L n)) (hfin y.2.2)
    exact ⟨P, hP, hPg⟩
  choose Pc hPc hPcgerm using hD₂
  let Q : E ⊕ C → Submodule k (vanishingSections k p I L n) :=
    Sum.elim (fun η => Stacks.Chow.BertiniChain.vanishingAtSubmodule k p I L n (ιG η.1)) Pc
  have hQ : ∀ i, Q i ≠ ⊤ := by
    rintro (η | y)
    · exact Stacks.Chow.BertiniChain.vanishingAtSubmodule_ne_top k p I L n hgen η.2.2
    · exact hPc y
  choose ℓ hℓ hQℓ using fun i => (Q i).exists_le_ker_of_lt_top (hQ i).lt_top
  refine ⟨U, hUne, _, inferInstance, ℓ, hℓ, fun a ha hℓa => ?_⟩
  set v : vanishingSections k p I L n :=
    ∑ j, a j • Module.finBasis k (vanishingSections k p I L n) j
  have hvQ : ∀ i, v ∉ Q i := fun i hi => hℓa i (LinearMap.mem_ker.1 (hQℓ i hi))
  set M := tensorPowModule X L n
  set s := vsec p n v
  have h₁ : Smooth ((zeroScheme D₁.X D₁.L (D₁.sectionOf v)).subschemeι ≫ D₁.toBase) :=
    D₁.smooth_zeroScheme_of_smooth_specializedDivisor a (hU D₁.k a ha a rfl)
  set M' := (Scheme.Modules.pullback ιG).obj M
  set t := pullbackGlobalSections ιG M s
  set ZG := zeroScheme G.toScheme M' t
  have hZG : ZG = (zeroScheme X M s).comap ιG := zeroScheme_pullback_eq_comap ιG M s
  have hZ1 : zeroScheme D₁.X D₁.L (D₁.sectionOf v) = ZG.comap Wo.ι := by
    show zeroScheme _ _ (pullbackGlobalSections g₁ _ (pullbackGlobalSections O.ι M s)) = _
    rw [zeroScheme_pullback_eq_comap, zeroScheme_pullback_eq_comap,
      ← Scheme.IdealSheafData.comap_comp, hg₁, Scheme.IdealSheafData.comap_comp, hZG]
  have hsmW : Smooth ((ZG.comap Wo.ι).subschemeι ≫ Wo.ι ≫ fG) := by
    rw [← hZ1, ← hD₁base]; exact h₁
  have hreg : ∀ y : G.toScheme, IsRegularLocalRing (G.toScheme.presheaf.stalk y) :=
    fun y => isRegularLocalRing_stalk_of_smooth_over_field fG y
  have hgerm : ∀ y : G.toScheme, y ∈ ZG.support → y ∉ Set.range Wo.ι.base →
      (M'.presheaf.Γgerm y).hom t ∉ Stacks.ImmersionEvaluationSurjective.maximalSqSmul M' y := by
    intro y _ hyW
    have hyI : ιG y ∈ I.support := by
      by_contra h
      exact hyW ⟨⟨y, h⟩, rfl⟩
    have hyc := hI _ hyI
    exact hPcgerm ⟨y, hyc, hyc ▸ hyI⟩ v (hvQ (Sum.inr ⟨y, hyc, hyc ▸ hyI⟩))
  have hsmG : Smooth (ZG.subschemeι ≫ fG) :=
    smooth_zeroScheme_of_smooth_comap_of_forall_notMem_maximalSqSmul M' t fG Wo.ι rfl hsmW hreg
      hgerm
  have hgenpts : ∀ η : G.toScheme, closure ({η} : Set G.toScheme) ∈
      irreducibleComponents G.toScheme → η ∉ ZG.support := by
    intro η hη hηZ
    by_cases hηI : ιG η ∈ I.support
    · have hηc := hI _ hηI
      exact not_isClosed_singleton_of_mem_genericPoints fG r η hη (hclosed η hηc)
    · have hnv := hvQ (Sum.inl ⟨η, hη, hηI⟩)
      have hmem : ιG η ∈ nvOpen M s := not_not.mp hnv
      have hmem' : η ∈ nvOpen M' t := by
        rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
        exact hmem
      exact AlgebraicGeometry.notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen M' t hmem'
        (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hηZ)
  have hrel : SmoothOfRelativeDimension r (ZG.subschemeι ≫ fG) :=
    smoothOfRelativeDimension_zeroScheme fG r M' t hgenpts hsmG
  intro z hz hzZ
  obtain ⟨y, rfl⟩ := exists_mem_goodLocus_of_subschemeSmoothAt p T (r + 1) hz
  refine subschemeSmoothAt_sup_of_comap p T r (zeroScheme X M s) G ?_ y hzZ
  have hc' : ((zeroScheme X M s).comap T.subschemeι).comap G.ι = ZG := by
    rw [hZG, ← Scheme.IdealSheafData.comap_comp]
  rw [hc']
  simpa only [fG, ιG, Category.assoc] using hrel

end AlgebraicGeometry.GoodNeighbourhood

end
