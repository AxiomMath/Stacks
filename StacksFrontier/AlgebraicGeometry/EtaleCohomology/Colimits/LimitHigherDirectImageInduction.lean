module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageInductionStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import StacksFrontier.CategoryTheory.Limits.SystemColimitMono
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Higher direct images along a limit: the induction on the degree

The first proof of [Stacks, Tag 0EYM] is an induction on the degree `p`. Every system of abelian
sheaves `ℱ_•` on the inverse system `(X_i)` embeds into a system of injective sheaves `𝒢_•`
(`Stacks.EtaleCohomology.InjectiveSheafSystem.system`, [Stacks, Tag 0EXZ]) with cokernel system
`𝒬_•`. The colimits on the limit `X` of the inverse images of the three systems form a short
exact sequence `0 ⟶ ℱ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0`: the colimits exist, abelian sheaves on the small étale
site having coproducts and coequalizers; the cokernel of `ℱ ⟶ 𝒢` presents the colimit of `𝒬_•`
because cokernels commute with colimits of systems; and `ℱ ⟶ 𝒢` is a monomorphism because
filtered colimits of abelian sheaves are exact. The dimension shift
`Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_succ` then passes from
degree `p` to degree `p + 1`, given that `R^{p+1}g_*𝒢 = 0`.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackCocone` — the compatibility of a
  family `f_i^{-1}ℱ_i ⟶ 𝓕` with the transition maps of a system.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.exists_isPullbackColimitPresentation` — every
  system has a colimit presentation on the limit.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.mono_of_isPullbackColimitPresentation` — the
  colimits on the limit of two systems related by a levelwise monomorphism are related by a
  monomorphism.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_succ_of_forall` —
  the inductive step for all systems at once.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_of_zero` — **the
  induction**: the colimit assertion in degree zero, together with the vanishing of the higher
  direct images on colimits of systems of injective sheaves, gives the assertion in every
  degree.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)

/-- The compatibility of a family of maps `f_i^{-1}ℱ_i ⟶ 𝓕` with the transition maps of a system
`ℱ_•`: the hypothesis under which a family presents `𝓕` as a colimit. -/
abbrev IsPullbackCocone (F : EtaleSheafSystem DX Ab.{u + 1})
    {𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (conePullbackComp cX a).inv.app (F.obj j) ≫
    (smallEtalePullbackAb (cX.π.app i)).map (F.map a) ≫ ι i = ι j

section Construction

variable {cX} (F : EtaleSheafSystem DX Ab.{u + 1})

/-- **Filtered colimits of abelian sheaves on the small étale site are exact**, for the filtered
shape `CategoryTheory.Limits.SystemLift I` of systems over a directed set `I : Type u`. -/
theorem hasExactColimitsOfShape_systemLift_sheaf (X : Scheme.{u}) [IsDirected I (· ≤ ·)]
    [Nonempty I] :
    HasExactColimitsOfShape (SystemLift I) (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} AddCommGrpCat.{u + 1}
  have : HasColimitsOfShape (SystemLift I) AddCommGrpCat.{u + 1} := inferInstance
  Sheaf.hasExactColimitsOfShape _

/-- **Every system has a colimit presentation on the limit**: the inverse images to the limit of
the sheaves of a system, with the comparisons of inverse images along the transitions, have a
colimit, abelian sheaves on the small étale site having coproducts and coequalizers. -/
theorem exists_isPullbackColimitPresentation (F : EtaleSheafSystem DX Ab.{u + 1}) :
    ∃ (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕),
      IsPullbackCocone cX F ι ∧ IsPullbackColimitPresentation cX 𝓕 F ι := by
  have : HasCoproductsOfShape Iᵒᵖ (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) :=
    hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} cX.pt _
  have : HasCoproductsOfShape (Σ i j : Iᵒᵖ, i ⟶ j) (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) :=
    hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} cX.pt _
  let A : Iᵒᵖ → Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1} :=
    fun i => (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i)
  let T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i) := fun {i j} a =>
    (conePullbackComp cX a).inv.app (F.obj j) ≫ (smallEtalePullbackAb (cX.π.app i)).map (F.map a)
  exact ⟨systemColimit A T, systemColimitι A T,
    fun a => (Category.assoc _ _ _).symm.trans (systemColimitι_compatible A T a),
    .of_isSystemColimit (isSystemColimit_systemColimit A T)⟩

variable {F G : EtaleSheafSystem DX Ab.{u + 1}} (α : ∀ i, F.obj i ⟶ G.obj i)
  (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)

/-- A pullback cocone is compatible with the maps of the diagram of inverse images. -/
private theorem pullbackDiagramMap_comp_ι {𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕}
    (hι : IsPullbackCocone cX F ι) {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.pullbackDiagramMap cX (i := i) (j := j) a ≫ ι i = ι j :=
  (Category.assoc _ _ _).trans (hι a)

include hα in
/-- The maps of the diagrams of inverse images of two systems commute with a map of systems. -/
theorem pullbackDiagramMap_comp_map {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.pullbackDiagramMap cX (i := i) (j := j) a ≫ (smallEtalePullbackAb (cX.π.app i)).map (α i) =
      (smallEtalePullbackAb (cX.π.app j)).map (α j) ≫
        G.pullbackDiagramMap cX (i := i) (j := j) a := by
  have hn := (conePullbackComp cX a).inv.naturality (α j)
  simp only [Functor.comp_map] at hn
  rw [EtaleSheafSystem.pullbackDiagramMap, EtaleSheafSystem.pullbackDiagramMap, Category.assoc,
    ← Functor.map_comp, ← hα a, Functor.map_comp, ← reassoc_of% hn]
  rfl

include hα in
/-- **The colimits on the limit of two systems are related by a monomorphism** as soon as the
systems are, filtered colimits of abelian sheaves being exact. -/
theorem mono_of_isPullbackColimitPresentation [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ i, Mono (α i)] {𝓕 𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    {ιF : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕}
    {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖}
    (hιF : IsPullbackCocone cX F ιF) (hιG : IsPullbackCocone cX G ιG)
    (hF : IsPullbackColimitPresentation cX 𝓕 F ιF)
    (hG : IsPullbackColimitPresentation cX 𝓖 G ιG) (u : 𝓕 ⟶ 𝓖)
    (hu : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i = ιF i ≫ u) : Mono u := by
  have : HasExactColimitsOfShape (SystemLift I) (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) :=
    hasExactColimitsOfShape_systemLift_sheaf cX.pt
  have : HasColimitsOfShape (SystemLift I) (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) :=
    hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} cX.pt (SystemLift I)
  have : ∀ i, Mono ((smallEtalePullbackAb (cX.π.app i)).map (α i)) := fun i => inferInstance
  exact IsSystemColimit.mono_of_isSystemColimit (F.pullbackDiagramMap_comp cX)
    (G.pullbackDiagramMap_comp cX) (fun i => (smallEtalePullbackAb (cX.π.app i)).map (α i))
    (pullbackDiagramMap_comp_map α hα) (pullbackDiagramMap_comp_ι hιF)
    (pullbackDiagramMap_comp_ι hιG) hF.isSystemColimit hG.isSystemColimit u
    (fun i => (hu i).symm)

end Construction

/-! ### The induction -/

section Induction

variable [IsDirected I (· ≤ ·)] [Nonempty I]

/-- **A system with a colimit presentation embeds into a system of injective sheaves, compatibly
with colimit presentations.** For a system `F` with a colimit presentation `𝓕` on the limit there
are a system `G` of injective sheaves, a short exact sequence of systems `0 ⟶ F ⟶ G ⟶ Q ⟶ 0`,
colimit presentations `𝓖`, `𝓠` of `G`, `Q`, and a short exact sequence `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓠 ⟶ 0`
on the limit compatible with the presentations. -/
theorem exists_injective_shortExact_presentation (F : EtaleSheafSystem DX Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : IsPullbackCocone cX F ι) (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    ∃ (G : EtaleSheafSystem DX Ab.{u + 1}) (_ : ∀ i, Injective (G.obj i))
      (Q : EtaleSheafSystem DX Ab.{u + 1}) (α : ∀ i, F.obj i ⟶ G.obj i)
      (β : ∀ i, G.obj i ⟶ Q.obj i) (hαβ : ∀ i, α i ≫ β i = 0)
      (𝓖 𝓠 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖)
      (ιQ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (Q.obj i) ⟶ 𝓠)
      (u : 𝓕 ⟶ 𝓖) (v : 𝓖 ⟶ 𝓠) (huv : u ≫ v = 0),
      (∀ i, (ShortComplex.mk (α i) (β i) (hαβ i)).ShortExact) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
        (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
        (systemPullback DX Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i) ∧
      IsPullbackCocone cX G ιG ∧ IsPullbackColimitPresentation cX 𝓖 G ιG ∧
      IsPullbackCocone cX Q ιQ ∧ IsPullbackColimitPresentation cX 𝓠 Q ιQ ∧
      (ShortComplex.mk u v huv).ShortExact ∧
      (∀ i, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i = ι i ≫ u) ∧
      (∀ i, (smallEtalePullbackAb (cX.π.app i)).map (β i) ≫ ιQ i = ιG i ≫ v) := by
  -- the system of injective sheaves containing `F`, and the quotient
  let G := InjectiveSheafSystem.system DX F
  let α : ∀ i, F.obj i ⟶ G.obj i := InjectiveSheafSystem.ι DX F
  have hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i :=
    InjectiveSheafSystem.ι_comm DX F
  have : ∀ i, Mono (α i) := InjectiveSheafSystem.mono_ι DX F
  have : ∀ i, Injective (G.obj i) := InjectiveSheafSystem.injective DX F
  let Q := EtaleSheafSystem.cokernel α hα
  let β : ∀ i, G.obj i ⟶ Q.obj i := fun i => cokernel.π (α i)
  have hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i :=
    EtaleSheafSystem.cokernel_π_comm α hα
  have hαβ : ∀ i, α i ≫ β i = 0 := fun i => cokernel.condition (α i)
  have : ∀ i, Epi (β i) := fun i => coequalizer.π_epi
  have hE : ∀ i, (ShortComplex.mk (α i) (β i) (hαβ i)).ShortExact := fun i =>
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (α i)) }
  -- the colimit presentation of `G` and the map `u : 𝓕 ⟶ 𝓖`
  obtain ⟨𝓖, ιG, hιG, hG⟩ := exists_isPullbackColimitPresentation (cX := cX) G
  have hcompat : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      F.pullbackDiagramMap cX (i := i) (j := j) a ≫
          ((smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i) =
        (smallEtalePullbackAb (cX.π.app j)).map (α j) ≫ ιG j := fun {i j} a => by
    rw [← Category.assoc, pullbackDiagramMap_comp_map α hα a, Category.assoc,
      pullbackDiagramMap_comp_ι hιG a]
  let u : 𝓕 ⟶ 𝓖 :=
    hpres.isSystemColimit.desc (fun i => (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i)
      hcompat
  have hu : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i = ι i ≫ u := fun i =>
    (hpres.isSystemColimit.fac (fun i => (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i)
      hcompat i).symm
  have : Mono u := mono_of_isPullbackColimitPresentation α hα hι hιG hpres hG u hu
  -- the quotient on the limit
  let 𝓠 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1} := cokernel u
  let v : 𝓖 ⟶ 𝓠 := cokernel.π u
  have huv : u ≫ v = 0 := cokernel.condition u
  have hlim : (ShortComplex.mk u v huv).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u) }
  have hz : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i ≫ v = 0 := fun i => by
    rw [reassoc_of% (hu i), huv, comp_zero]
  let ιQ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (Q.obj i) ⟶ 𝓠 :=
    fun i => (PreservesCokernel.iso (smallEtalePullbackAb (cX.π.app i)) (α i)).hom ≫
      cokernel.desc _ (ιG i ≫ v) (hz i)
  have hv : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (β i) ≫ ιQ i = ιG i ≫ v := fun i => by
    have h : (smallEtalePullbackAb (cX.π.app i)).map (cokernel.π (α i)) ≫
        (PreservesCokernel.iso (smallEtalePullbackAb (cX.π.app i)) (α i)).hom =
          cokernel.π ((smallEtalePullbackAb (cX.π.app i)).map (α i)) := by
      rw [← Iso.eq_comp_inv, PreservesCokernel.iso_inv, π_comp_cokernelComparison]
    exact ((reassoc_of% h) _).trans (cokernel.π_desc _ _ _)
  have hιQ : IsPullbackCocone cX Q ιQ := fun {i j} a => by
    change Q.pullbackDiagramMap cX (i := i) (j := j) a ≫ ιQ i = ιQ j
    rw [← cancel_epi ((smallEtalePullbackAb (cX.π.app j)).map (β j)),
      ← reassoc_of% pullbackDiagramMap_comp_map β hβ a, hv i,
      reassoc_of% pullbackDiagramMap_comp_ι hιG a, hv j]
  have hQ : IsPullbackColimitPresentation cX 𝓠 Q ιQ :=
    .of_isSystemColimit <| IsSystemColimit.of_cokernel
      (A := fun i => (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i))
      (B := fun i => (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i))
      (C := fun i => (smallEtalePullbackAb (cX.π.app i)).obj (Q.obj i))
      (TA := fun a => F.pullbackDiagramMap cX a) (TB := fun a => G.pullbackDiagramMap cX a)
      (TC := fun a => Q.pullbackDiagramMap cX a) (α := ι) (β := ιG) (hUV := huv)
      (fun i => (smallEtalePullbackAb (cX.π.app i)).map (α i))
      (fun i => (smallEtalePullbackAb (cX.π.app i)).map (β i))
      (fun i => ((smallEtalePullbackAb (cX.π.app i)).map_comp _ _).symm.trans
        ((congrArg _ (hαβ i)).trans (Functor.map_zero _ _ _)))
      (fun i => Functor.map_epi _ _) (pullbackDiagramMap_comp_map β hβ) ιQ
      hpres.isSystemColimit hG.isSystemColimit
      (pullbackDiagramMap_comp_ι hι) u v (fun i => (hu i).symm)
      (fun i => (hv i).symm) (cokernelIsCokernel u)
  exact ⟨G, inferInstance, Q, α, β, hαβ, 𝓖, 𝓠, ιG, ιQ, u, v, huv, hE, hα, hβ, hιG, hG, hιQ, hQ,
    hlim, hu, hv⟩

/-- **The inductive step of the first proof of [Stacks, Tag 0EYM], for every system at once.** If
the colimit assertion holds in degree `p` for every system with a colimit presentation, and
`R^{p+1}g_*` vanishes on the colimit of every system of injective sheaves, then the colimit
assertion holds in degree `p + 1` for every system with a colimit presentation. The system is
embedded into the system of injective sheaves of
`Stacks.EtaleCohomology.InjectiveSheafSystem.system`, the quotient is the cokernel system, and the
colimits on the limit of the three systems form a short exact sequence. -/
theorem isHigherDirectImageColimit_succ_of_forall (p : ℕ)
    (hvan : ∀ (G : EtaleSheafSystem DX Ab.{u + 1}) [∀ i, Injective (G.obj i)]
      (𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖),
      IsPullbackCocone cX G ιG → IsPullbackColimitPresentation cX 𝓖 G ιG →
      IsZero (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived (p + 1)).obj 𝓖))
    (ih : ∀ (F : EtaleSheafSystem DX Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕),
      IsPullbackCocone cX F ι → IsPullbackColimitPresentation cX 𝓕 F ι →
      IsHigherDirectImageColimit γ p cX cS hcS 𝓕 F ι)
    (F : EtaleSheafSystem DX Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : IsPullbackCocone cX F ι) (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    IsHigherDirectImageColimit γ (p + 1) cX cS hcS 𝓕 F ι := by
  obtain ⟨G, _, Q, α, β, hαβ, 𝓖, 𝓠, ιG, ιQ, u, v, huv, hE, hα, hβ, hιG, hG, hιQ, hQ, hlim, hu,
    hv⟩ := exists_injective_shortExact_presentation cX F 𝓕 ι hι hpres
  exact isHigherDirectImageColimit_succ γ p cX cS hcS (α := α) (β := β) hαβ hE ι ιG ιQ u v huv
    hlim hu hv hα hβ (fun a => by rw [← hιG a, Iso.hom_inv_id_app_assoc])
    (hvan G 𝓖 ιG hιG hG) (ih G 𝓖 ιG hιG hG) (ih Q 𝓠 ιQ hιQ hQ)

/-- **The induction on the degree of the first proof of [Stacks, Tag 0EYM].** If the colimit
assertion holds in degree zero for every system with a colimit presentation, and the higher
direct images in positive degrees vanish on the colimit of every system of injective sheaves,
then the colimit assertion holds in every degree. -/
theorem isHigherDirectImageColimit_of_zero
    (h0 : ∀ (F : EtaleSheafSystem DX Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕),
      IsPullbackCocone cX F ι → IsPullbackColimitPresentation cX 𝓕 F ι →
      IsHigherDirectImageColimit γ 0 cX cS hcS 𝓕 F ι)
    (hvan : ∀ (q : ℕ) (G : EtaleSheafSystem DX Ab.{u + 1}) [∀ i, Injective (G.obj i)]
      (𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖),
      IsPullbackCocone cX G ιG → IsPullbackColimitPresentation cX 𝓖 G ιG →
      IsZero (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived (q + 1)).obj 𝓖))
    (p : ℕ) (F : EtaleSheafSystem DX Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : IsPullbackCocone cX F ι) (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    IsHigherDirectImageColimit γ p cX cS hcS 𝓕 F ι := by
  induction p generalizing F 𝓕 ι with
  | zero => exact h0 F 𝓕 ι hι hpres
  | succ p ih =>
    exact isHigherDirectImageColimit_succ_of_forall γ cX cS hcS p (hvan p)
      ih F 𝓕 ι hι hpres

end Induction

end Stacks.EtaleCohomology.LimitHigherDirectImage
