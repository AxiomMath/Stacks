module

public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Stability
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtalePrecoverage

/-!
# Cohomology of a parasitic module over a flat scheme

A sheaf of modules on one of the five standard big sites of a scheme `S` whose sections vanish
on every object flat over `S` has vanishing cohomology at every object flat over `S`.

## Main results

* `AlgebraicGeometry.bigZariskiCohomology_isZero_of_isParasitic`
* `AlgebraicGeometry.bigEtaleCohomology_isZero_of_isParasitic`
* `AlgebraicGeometry.bigSmoothCohomology_isZero_of_isParasitic`
* `AlgebraicGeometry.bigSyntomicCohomology_isZero_of_isParasitic`
* `AlgebraicGeometry.bigFppfCohomology_isZero_of_isParasitic`

## Implementation notes

Cohomology is that of the underlying abelian sheaf and vanishing is categorical `IsZero`. The
parasitic hypothesis is the pointwise expansion of `AlgebraicGeometry.IsParasitic`: taking it
pointwise keeps the ring sheaf of the module out of the hypothesis, so it need not be
transported along a structure-sheaf equation.

**The ring sheaf is a free variable.** Each statement takes an arbitrary sheaf of rings `𝒪` on
the site and a sheaf of `𝒪`-modules, rather than fixing `𝒪` to be the site's structure sheaf.
Nothing in any of the five proofs touches the ring sheaf — they all factor through
`SheafOfModules.toSheaf` and the underlying abelian sheaf — so this costs nothing and is
strictly more general: instantiating `𝒪` at the structure sheaf of the site recovers the
statement about `𝒪`-modules.

All five reduce to one criterion,
`Stacks.CechSite.cohomology_isZero_of_isZero_on_covering_fiberProducts`, applied to the family
of objects flat over `S`. What each case has to supply is that the family is stable under the
objects and iterated fibre products of its coverings, which is where the topology enters: the
covering morphisms of each site are flat (open immersions, étale, smooth, syntomic, and flat
respectively), and flatness is stable under composition and base change.

## References

* [Stacks Project, Tag 0755](https://stacks.math.columbia.edu/tag/0755)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u v s w

namespace AlgebraicGeometry

private lemma flat_binaryProduct_over {C : Type u} [Category.{v} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{s}) {U : C} [HasBinaryProducts (Over U)] (A B : Over U)
    (hA : Flat (G.map A.hom)) (hB : Flat (G.map B.hom))
    [PreservesLimitsOfShape WalkingCospan G] :
    Flat (G.map (prod A B).hom) := by
  let : HasBinaryProducts (Over U) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let e := Over.prodLeftIsoPullback A B
  have hfst : Flat (G.map (pullback.fst A.hom B.hom)) := by
    have hcomp : Flat ((PreservesPullback.iso G A.hom B.hom).hom ≫
        pullback.fst (G.map A.hom) (G.map B.hom)) := by infer_instance
    rwa [PreservesPullback.iso_hom_fst] at hcomp
  have : IsIso (G.map e.hom) := Functor.map_isIso G e.hom
  have heq : (prod A B).hom = e.hom ≫ pullback.fst A.hom B.hom ≫ A.hom := by
    calc
      (prod A B).hom = (prod.fst (X := A)).left ≫ A.hom :=
        (Over.w (prod.fst (X := A))).symm
      _ = e.hom ≫ pullback.fst A.hom B.hom ≫ A.hom := by
        rw [← Category.assoc, ← Over.prodLeftIsoPullback_hom_fst]
  rw [heq]
  have hcomp : Flat ((G.map e.hom ≫ G.map (pullback.fst A.hom B.hom)) ≫
      G.map A.hom) := by infer_instance
  simpa only [Functor.map_comp, Category.assoc] using hcomp

private theorem flat_piObj_fin_succ {C : Type u} [Category.{v} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{s}) [PreservesLimitsOfShape WalkingCospan G]
    {n : ℕ} {U : C} [HasFiniteProducts (Over U)] (f : Fin (n + 1) → Over U)
    (hf : ∀ i, Flat (G.map (f i).hom)) :
    Flat (G.map (piObj f).hom) := by
  let : HasBinaryProducts (Over U) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let : HasFiniteProducts (Over U) := hasFiniteProducts_of_has_binary_and_terminal
  induction n with
  | zero =>
      change Flat (G.map (piObj f).hom)
      let : Unique (Fin 1) := inferInstance
      let e : piObj f ≅ f 0 := productUniqueIso f
      have : IsIso (e.hom.left) :=
        Functor.map_isIso (Over.forget U) e.hom
      have : IsIso (G.map e.hom.left) := Functor.map_isIso G e.hom.left
      have heq : (piObj f).hom = e.hom.left ≫ (f 0).hom := (Over.w e.hom).symm
      rw [heq, Functor.map_comp]
      have := hf 0
      infer_instance
  | succ n ih =>
      change Flat (G.map (piObj f).hom)
      have htail : Flat (G.map (piObj (fun i : Fin (n + 1) ↦ f i.succ)).hom) :=
        ih (fun i : Fin (n + 1) ↦ f i.succ) (fun i ↦ hf i.succ)
      let c₁ : Fan (fun i : Fin (n + 1) ↦ f i.succ) := limit.cone _
      let t₁ : IsLimit c₁ := limit.isLimit _
      let c₂ : BinaryFan (f 0) c₁.pt :=
        BinaryFan.mk (prod.fst (X := f 0)) (prod.snd (X := f 0))
      let t₂ : IsLimit c₂ := prodIsProd _ _
      let c : Fan f := CategoryTheory.extendFan c₁ c₂
      let hc : IsLimit c := CategoryTheory.extendFanIsLimit f t₁ t₂
      let e := IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc
      have hbin : Flat (G.map c.pt.hom) := by
        change Flat (G.map (prod (f 0) c₁.pt).hom)
        exact flat_binaryProduct_over G (f 0) c₁.pt (hf 0)
          (by simpa [c₁] using htail)
      have : IsIso e.hom.left := Functor.map_isIso (Over.forget U) e.hom
      have : IsIso (G.map e.hom.left) := Functor.map_isIso G e.hom.left
      have heq : (piObj f).hom = e.hom.left ≫ c.pt.hom := (Over.w e.hom).symm
      rw [heq, Functor.map_comp]
      infer_instance

private theorem flat_iteratedFiberProduct {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S : Scheme.{s}} (toOver : C ⥤ Over S)
    [PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S)]
    {U : C} (hU : Flat (toOver.obj U).hom)
    (E : PreZeroHypercover.{max u v} U)
    {p : ℕ} (s : Fin (p + 1) → E.I₀)
    (hE : ∀ i, Flat ((toOver ⋙ Over.forget S).map (E.f (s i)))) :
    Flat (toOver.obj (Stacks.CechSite.iteratedFiberProduct E s)).hom := by
  let : HasBinaryProducts (Over U) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let : HasFiniteProducts (Over U) := hasFiniteProducts_of_has_binary_and_terminal
  let P := piObj (fun i ↦ Over.mk (E.f (s i)))
  have hP : Flat ((toOver ⋙ Over.forget S).map P.hom) :=
    flat_piObj_fin_succ (toOver ⋙ Over.forget S) _ (fun i ↦ hE i)
  have hw := (toOver.map P.hom).w
  unfold Stacks.CechSite.iteratedFiberProduct
  change Flat (toOver.obj P.left).hom
  rw [← hw]
  exact (inferInstance : Flat (((toOver ⋙ Over.forget S).map P.hom) ≫ (toOver.obj U).hom))

private theorem cohomology_isZero_of_flat_covering_data_transport
    {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C]
    [HasPullbacks C] {J : GrothendieckTopology C} (K : Pretopology C)
    (hK : K.toGrothendieck = J)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    {S : Scheme.{s}} (toOver : C ⥤ Over S)
    [PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S)]
    (F : Sheaf J AddCommGrpCat.{v})
    (hCover : ∀ {X : C} (E : PreZeroHypercover.{max u v} X), E.presieve₀ ∈ K X →
      ∀ i, Flat ((toOver ⋙ Over.forget S).map (E.f i)))
    (hF : ∀ X : C, Flat (toOver.obj X).hom →
      Subsingleton (F.obj.obj (Opposite.op X)))
    (U : C) (hU : Flat (toOver.obj U).hom) (p : ℕ) :
    IsZero (F.H' p U) := by
  subst J
  let B : Set C := {X | Flat (toOver.obj X).hom}
  have hB : ∀ (V : C), V ∈ B →
      ∀ (E : PreZeroHypercover.{max u v} V), E.presieve₀ ∈ K V →
        (∀ i, E.X i ∈ B) ∧
          ∀ (q : ℕ) (s : Fin (q + 1) → E.I₀),
            Stacks.CechSite.iteratedFiberProduct E s ∈ B := by
    intro V hV E hE
    change Flat (toOver.obj V).hom at hV
    refine ⟨fun i ↦ ?_, fun q s ↦
      flat_iteratedFiberProduct toOver hV E s (fun i ↦ hCover E hE (s i))⟩
    have := hCover E hE i
    have hw : (toOver.obj (E.X i)).hom =
        ((toOver ⋙ Over.forget S).map (E.f i) ≫ (toOver.obj V).hom) :=
      (toOver.map (E.f i)).w.symm
    change Flat (toOver.obj (E.X i)).hom
    rw [hw]
    infer_instance
  have hFzero (V : C) (hV : V ∈ B) :
      IsZero (F.obj.obj (Opposite.op V)) := by
    have : Subsingleton (F.obj.obj (Opposite.op V)) :=
      hF V (by simpa only [B, Set.mem_ofPred_eq] using hV)
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact Stacks.CechSite.cohomology_isZero_of_isZero_on_covering_fiberProducts
    K B F hFzero hB U (by simpa only [B, Set.mem_ofPred_eq] using hU) p

/-- The precoverage of a big fppf site is the fppf precoverage of schemes pulled back along the
inclusion of the site into all schemes. -/
lemma bigFppf_precoverage_eq (B : AlgebraicGeometry.BigFppfSite.{u}) :
    B.precoverage = Scheme.fppfPrecoverage.comap B.inclusion := by
  ext X R
  refine ⟨fun ⟨E, h, hE⟩ ↦ h ▸ hE.1, fun hR ↦ ?_⟩
  rw [Precoverage.mem_comap_iff] at hR
  let E := R.preZeroHypercover
  have hE : E.presieve₀ = R := R.presieve₀_preZeroHypercover
  have hCov : AlgebraicGeometry.IsFppfCovering ⟨X, E⟩ := by
    unfold AlgebraicGeometry.IsFppfCovering
    change Presieve.map B.inclusion E.presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)
    rwa [hE]
  obtain ⟨E', hE', hComb⟩ := B.fppf_has_representative ⟨X, E⟩ hCov
  obtain ⟨hXE, hComb⟩ := hComb
  cases hXE
  have hE'cov : B.IsCovering E' := by
    simpa [AlgebraicGeometry.BigFppfSite.IsCovering] using hE'
  exact ⟨E'.2, hE.symm.trans
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb),
    hE'cov⟩

private instance schemeEtalePrecoverage_stableUnderBaseChange :
    Scheme.etalePrecoverage.{u}.IsStableUnderBaseChange := by
  dsimp only [Scheme.etalePrecoverage]
  exact schemePrecoverage_stableUnderBaseChange (@Etale : MorphismProperty Scheme.{u})

private instance schemeEtalePrecoverage_stableUnderComposition :
    Scheme.etalePrecoverage.{u}.IsStableUnderComposition := by
  dsimp only [Scheme.etalePrecoverage]
  let : MorphismProperty.IsStableUnderComposition
      (@Etale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  exact schemePrecoverage_stableUnderComposition (@Etale : MorphismProperty Scheme.{u})

/-- The precoverage of a big smooth site is the smooth precoverage of schemes pulled back along
the inclusion of the site into all schemes. -/
lemma bigSmoothPrecoverage_eq_comap (B : AlgebraicGeometry.BigSmoothSite.{u}) :
    B.precoverage = (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).comap
      (ObjectProperty.ι _) := by
  ext X R
  rw [Precoverage.mem_comap_iff]
  change (∃ E : PreZeroHypercover.{u + 1} X,
      B.IsCovering ⟨X, E⟩ ∧ R = E.presieve₀) ↔ _
  refine ⟨?_, fun hR ↦ ?_⟩
  · rintro ⟨E, hE, rfl⟩
    rw [← PreZeroHypercover.presieve₀_map]
    exact hE.1
  let E := R.preZeroHypercover
  have hE : E.presieve₀ = R := R.presieve₀_preZeroHypercover
  have hmem : (E.map (ObjectProperty.ι _)).presieve₀ ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) _ := by
    rwa [PreZeroHypercover.presieve₀_map, hE]
  have hSmooth : AlgebraicGeometry.SmoothCovering B.cutoff ⟨X, E⟩ := hmem
  obtain ⟨E', hE', hComb⟩ := B.has_coveringRepresentative ⟨X, E⟩ hSmooth
  obtain ⟨hXE, hComb⟩ := hComb
  cases hXE
  exact ⟨E'.2, hE', hE.symm.trans
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb)⟩

/-- The precoverage of a big syntomic site is the syntomic precoverage of schemes pulled back
along the inclusion of the site into all schemes. -/
lemma bigSyntomicPrecoverage_eq_comap (B : AlgebraicGeometry.BigSyntomicSite.{u}) :
    B.precoverage = (Scheme.precoverage (@Syntomic
      : MorphismProperty Scheme.{u})).comap B.inclusion := by
  ext X R
  rw [Precoverage.mem_comap_iff]
  change (∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ B.IsCovering ⟨X, E⟩) ↔ _
  refine ⟨?_, fun hR ↦ ?_⟩
  · rintro ⟨E, rfl, hE⟩
    have hSyntomic : AlgebraicGeometry.SyntomicCovering B.cutoff ⟨X, E⟩ := hE.1
    have hmem : (E.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (@Syntomic
        : MorphismProperty Scheme.{u}) _ := by
      refine (Scheme.ofArrows_mem_precoverage_iff (@Syntomic)).2 ⟨fun x ↦ ?_, hSyntomic.1⟩
      have hx := Set.eq_univ_iff_forall.mp hSyntomic.2 x
      change x ∈ ⋃ i, Set.range ((E.map B.inclusion).f i) at hx
      simpa only [Set.mem_iUnion, Set.mem_range] using hx
    simpa only [PreZeroHypercover.presieve₀_map] using hmem
  · let E := R.preZeroHypercover
    have hE : E.presieve₀ = R := R.presieve₀_preZeroHypercover
    have hSyntomic : AlgebraicGeometry.SyntomicCovering B.cutoff ⟨X, E⟩ := by
      have hmem : (E.map B.inclusion).presieve₀ ∈
          Scheme.precoverage (@Syntomic
            : MorphismProperty Scheme.{u}) _ := by
        rwa [PreZeroHypercover.presieve₀_map, hE]
      have hparts := (Scheme.ofArrows_mem_precoverage_iff
        (@Syntomic)).mp hmem
      change AlgebraicGeometry.IsSyntomicCovering
        (fun i ↦ (E.map B.inclusion).X i) (fun i ↦ (E.map B.inclusion).f i)
      refine ⟨hparts.2, Set.eq_univ_iff_forall.mpr fun x ↦ ?_⟩
      obtain ⟨i, hi⟩ := hparts.1 x
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr hi⟩
    obtain ⟨E', hE', hComb⟩ := B.has_coveringRepresentative ⟨X, E⟩ hSyntomic
    obtain ⟨hXE, hComb⟩ := hComb
    cases hXE
    exact ⟨E'.2, hE.symm.trans
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb), hE'⟩

private instance schemeZariskiPrecoverage_hasIsos :
    (Scheme.zariskiPretopology.toPrecoverage).HasIsos := by
  constructor
  intro X Y f hf
  exact Scheme.zariskiPretopology.has_isos f

/-- The precoverage of jointly surjective families in a class of morphisms containing the
isomorphisms has isomorphisms as coverings. -/
private lemma scheme_precoverage_hasIsos_of_isIso (W : MorphismProperty Scheme.{u})
    (hW : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f], W f) :
    (Scheme.precoverage W).HasIsos := by
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  have : IsIso f.base := Functor.map_isIso Scheme.forgetToTop f
  exact (Scheme.singleton_mem_precoverage_iff W f).mpr
    ⟨(ConcreteCategory.bijective_of_isIso f.base).surjective, have := hf; hW f⟩

/-- A parasitic module on the big Zariski site has no cohomology at a flat object. -/
@[stacks 0755 "flat_parasitic_vanishing"]
public theorem bigZariskiCohomology_isZero_of_isParasitic
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigZariskiOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) RingCat.{u}}
    (F : SheafOfModules.{u} 𝒪)
    (hF : ∀ X : AlgebraicGeometry.BigZariskiOver B S hS,
      Flat ((Over.post B.inclusion).obj X).hom → Subsingleton (F.val.obj (Opposite.op X)))
    (U : AlgebraicGeometry.BigZariskiOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj F).H' p U) := by
  let P := Scheme.zariskiPretopology.toPrecoverage
  let G := AlgebraicGeometry.BigZariskiOver.toScheme B S hS
  let : P.HasIsos := schemeZariskiPrecoverage_hasIsos
  let : P.IsStableUnderBaseChange := Scheme.zariskiPrecoverage_isStableUnderBaseChange
  let : P.IsStableUnderComposition := Scheme.zariskiPrecoverage_isStableUnderComposition
  let K : Pretopology (AlgebraicGeometry.BigZariskiOver B S hS) :=
    (P.comap G).toPretopology
  have hK : K.toGrothendieck = AlgebraicGeometry.BigZariskiOver.topology B S hS := by
    have hpre : P.comap G = AlgebraicGeometry.BigZariskiOver.precoverage B S hS := by
      calc
        P.comap G = (P.comap B.inclusion).comap (Over.forget (⟨S, hS⟩ : B.Schemes)) := by
          rw [Precoverage.comap_comp]
        _ = B.precoverage.comap (Over.forget (⟨S, hS⟩ : B.Schemes)) :=
          congrArg (fun J : Precoverage B.Schemes ↦
            J.comap (Over.forget (⟨S, hS⟩ : B.Schemes)))
              (AlgebraicGeometry.BigZariskiSite.precoverage_eq_comap B).symm
        _ = AlgebraicGeometry.BigZariskiOver.precoverage B S hS :=
          (AlgebraicGeometry.BigZariskiOver.precoverage_eq_comap B ⟨S, hS⟩).symm
    calc
      K.toGrothendieck = (P.comap G).toGrothendieck := by
        dsimp [K]
        exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck
      _ = AlgebraicGeometry.BigZariskiOver.topology B S hS := by
        rw [hpre, AlgebraicGeometry.BigZariskiOver.topology]
  let : PreservesLimitsOfShape WalkingCospan
      (Over.post B.inclusion ⋙ Over.forget (B.inclusion.obj (⟨S, hS⟩ : B.Schemes))) := by
    change PreservesLimitsOfShape WalkingCospan G
    infer_instance
  have hCover : ∀ {X : AlgebraicGeometry.BigZariskiOver B S hS}
      (E : PreZeroHypercover X), E.presieve₀ ∈ K X →
      ∀ i, Flat (G.map (E.f i)) := by
    intro X E hE
    have hmapped : (E.map G).presieve₀ ∈ P (G.obj X) := by
      change E.presieve₀ ∈ (P.comap G) X at hE
      rw [Precoverage.mem_comap_iff] at hE
      simpa only [PreZeroHypercover.presieve₀_map] using hE
    have hprops := (Scheme.ofArrows_mem_precoverage_iff (@IsOpenImmersion)).mp <| by
      simpa [P, Scheme.zariskiPretopology, Scheme.pretopology] using hmapped
    intro i
    have : IsOpenImmersion (G.map (E.f i)) := hprops.2 i
    infer_instance
  let : EssentiallySmall.{u} B.Schemes := by
    change EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow B.schemeCardinal)
    exact AlgebraicGeometry.essentiallySmall_schemeBelow B.schemeCardinal
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigZariskiOver B S hS) :=
    CategoryTheory.essentiallySmall_over (⟨S, hS⟩ : B.Schemes)
  exact cohomology_isZero_of_flat_covering_data_transport K hK (Over.post B.inclusion)
    ((SheafOfModules.toSheaf _).obj F) hCover hF U hU p

/-- A parasitic module on the big étale site has no cohomology at a flat object. -/
@[stacks 0755 "flat_parasitic_vanishing"]
public theorem bigEtaleCohomology_isZero_of_isParasitic
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigEtaleOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) RingCat.{u}}
    (F : SheafOfModules.{u} 𝒪)
    (hF : ∀ X : AlgebraicGeometry.BigEtaleOver B S hS,
      Flat ((Over.post B.inclusion).obj X).hom → Subsingleton (F.val.obj (Opposite.op X)))
    (U : AlgebraicGeometry.BigEtaleOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj F).H' p U) := by
  let P := Scheme.etalePrecoverage
  let G := AlgebraicGeometry.BigEtaleOver.toScheme B S hS
  let : P.HasIsos := schemeEtalePrecoverage_hasIsos
  let : P.IsStableUnderBaseChange := schemeEtalePrecoverage_stableUnderBaseChange
  let : P.IsStableUnderComposition := schemeEtalePrecoverage_stableUnderComposition
  let K : Pretopology (AlgebraicGeometry.BigEtaleOver B S hS) :=
    (P.comap G).toPretopology
  have hK : K.toGrothendieck = AlgebraicGeometry.BigEtaleOver.topology B S hS := by
    have hpre : P.comap G = AlgebraicGeometry.BigEtaleOver.precoverage B S hS := by
      calc
        P.comap G = (P.comap B.inclusion).comap
            (AlgebraicGeometry.BigEtaleOver.forget B S hS) := by
          rw [Precoverage.comap_comp]
        _ = B.precoverage.comap (AlgebraicGeometry.BigEtaleOver.forget B S hS) :=
          congrArg (fun J : Precoverage B.Scheme ↦
            J.comap (AlgebraicGeometry.BigEtaleOver.forget B S hS))
            (bigEtalePrecoverage_eq_comap B).symm
        _ = AlgebraicGeometry.BigEtaleOver.precoverage B S hS :=
          (bigEtaleOver_precoverage_eq_comap B S hS).symm
    calc
      K.toGrothendieck = (P.comap G).toGrothendieck := by
        dsimp [K]
        exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck
      _ = AlgebraicGeometry.BigEtaleOver.topology B S hS := by
        rw [hpre, AlgebraicGeometry.BigEtaleOver.topology]
  let : PreservesLimitsOfShape WalkingCospan
      (Over.post B.inclusion ⋙ Over.forget (B.inclusion.obj (B.obj S hS))) := by
    change PreservesLimitsOfShape WalkingCospan G
    infer_instance
  have hCover : ∀ {X : AlgebraicGeometry.BigEtaleOver B S hS}
      (E : PreZeroHypercover X), E.presieve₀ ∈ K X →
      ∀ i, Flat (G.map (E.f i)) := by
    intro X E hE
    change E.presieve₀ ∈ (P.comap G) X at hE
    rw [Precoverage.mem_comap_iff] at hE
    have hcover' : (E.map G).presieve₀ ∈ Scheme.precoverage (@Etale) _ := by
      simpa only [P, Scheme.etalePrecoverage, PreZeroHypercover.presieve₀_map] using hE
    have hEtale := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp hcover'
    intro i
    have : Etale (G.map (E.f i)) := hEtale.2 i
    infer_instance
  let : EssentiallySmall.{u} B.Scheme := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigEtaleOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj S hS)
  exact cohomology_isZero_of_flat_covering_data_transport K hK (Over.post B.inclusion)
    ((SheafOfModules.toSheaf _).obj F) hCover hF U hU p

/-- A parasitic module on the big smooth site has no cohomology at a flat object. -/
@[stacks 0755 "flat_parasitic_vanishing"]
public theorem bigSmoothCohomology_isZero_of_isParasitic
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    [HasSheafify (AlgebraicGeometry.BigSmoothOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) RingCat.{u}}
    (F : SheafOfModules.{u} 𝒪)
    (hF : ∀ X : AlgebraicGeometry.BigSmoothOver B S hS,
      Flat ((Over.post (ObjectProperty.ι _)).obj X).hom →
        Subsingleton (F.val.obj (Opposite.op X)))
    (U : AlgebraicGeometry.BigSmoothOver B S hS)
    (hU : Flat ((Over.post (ObjectProperty.ι _)).obj U).hom) (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj F).H' p U) := by
  let P := Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})
  let I := ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < B.cutoff)
  let toOver : AlgebraicGeometry.BigSmoothOver B S hS ⥤ Over S := Over.post I
  let G := AlgebraicGeometry.BigSmoothOver.toScheme B S hS
  let base := AlgebraicGeometry.BigSmoothSite.base B S hS
  let : HasPullbacks B.category :=
    AlgebraicGeometry.schemeCutoff_hasPullbacks B
  let : Scheme.IsJointlySurjectivePreserving (@Smooth : MorphismProperty Scheme.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  let : P.HasIsos := scheme_precoverage_hasIsos_of_isIso (@Smooth : MorphismProperty Scheme.{u})
    fun _ ↦ inferInstance
  let : P.IsStableUnderBaseChange :=
    schemePrecoverage_stableUnderBaseChange (@Smooth : MorphismProperty Scheme.{u})
  let : P.IsStableUnderComposition :=
    schemePrecoverage_stableUnderComposition (@Smooth : MorphismProperty Scheme.{u})
  let : B.precoverage.IsStableUnderBaseChange := by
    rw [bigSmoothPrecoverage_eq_comap B]
    infer_instance
  let K : Pretopology (AlgebraicGeometry.BigSmoothOver B S hS) := (P.comap G).toPretopology
  have hpre : P.comap G = B.precoverage.comap (Over.forget base) := by
    calc
      P.comap G = (P.comap I).comap (Over.forget base) := by
        rw [Precoverage.comap_comp]
      _ = B.precoverage.comap (Over.forget base) :=
        congrArg (fun J : Precoverage B.category ↦ J.comap (Over.forget base))
          (bigSmoothPrecoverage_eq_comap B).symm
  have hK : K.toGrothendieck = AlgebraicGeometry.BigSmoothOver.topology B S hS := by
    calc
      K.toGrothendieck = (P.comap G).toGrothendieck := by
        dsimp [K]
        exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck
      _ = (B.precoverage.comap (Over.forget base)).toGrothendieck := by rw [hpre]
      _ = B.grothendieckTopology.over base := by
        rw [← CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget]
      _ = AlgebraicGeometry.BigSmoothOver.topology B S hS := rfl
  let : PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S) := by
    change PreservesLimitsOfShape WalkingCospan G
    infer_instance
  have hCover : ∀ {X : AlgebraicGeometry.BigSmoothOver B S hS}
      (E : PreZeroHypercover X), E.presieve₀ ∈ K X →
      ∀ i, Flat (G.map (E.f i)) := by
    intro X E hE
    change E.presieve₀ ∈ (P.comap G) X at hE
    rw [Precoverage.mem_comap_iff] at hE
    have hmem : (E.map G).presieve₀ ∈ P (G.obj X) := by
      simpa only [PreZeroHypercover.presieve₀_map] using hE
    have hparts := (Scheme.ofArrows_mem_precoverage_iff (@Smooth)).mp hmem
    intro i
    have : Smooth (G.map (E.f i)) := hparts.2 i
    infer_instance
  let : EssentiallySmall.{u} B.category := by
    change EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow B.cutoff)
    exact AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigSmoothOver B S hS) :=
    CategoryTheory.essentiallySmall_over (AlgebraicGeometry.BigSmoothSite.base B S hS)
  exact cohomology_isZero_of_flat_covering_data_transport K hK toOver
    ((SheafOfModules.toSheaf _).obj F) hCover hF U hU p

/-- A parasitic module on the big syntomic site has no cohomology at a flat object. -/
@[stacks 0755 "flat_parasitic_vanishing"]
public theorem bigSyntomicCohomology_isZero_of_isParasitic
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigSyntomicOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) RingCat.{u}}
    (F : SheafOfModules.{u} 𝒪)
    (hF : ∀ X : AlgebraicGeometry.BigSyntomicOver B S hS,
      Flat ((Over.post B.inclusion).obj X).hom → Subsingleton (F.val.obj (Opposite.op X)))
    (U : AlgebraicGeometry.BigSyntomicOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj F).H' p U) := by
  let P := Scheme.precoverage (@Syntomic
    : MorphismProperty Scheme.{u})
  let toOver : AlgebraicGeometry.BigSyntomicOver B S hS ⥤ Over S := Over.post B.inclusion
  let G := AlgebraicGeometry.BigSyntomicOver.toScheme B S hS
  let : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) WalkingCospan :=
    AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan
      B.cutoff
  let : HasPullbacks B.category :=
    hasLimitsOfShape_of_closedUnderLimits WalkingCospan
      (fun X : Scheme.{u} ↦ X.size < B.cutoff)
  let : MorphismProperty.IsStableUnderBaseChange
      (@Syntomic.{u}) := syntomic_isStableUnderBaseChange
  let : MorphismProperty.IsStableUnderComposition
      (@Syntomic.{u}) := syntomic_isStableUnderComposition
  let : MorphismProperty.ContainsIdentities (@Syntomic.{u}) :=
    ⟨fun X ↦ (AlgebraicGeometry.isSyntomicCovering_singleton_of_isIso (𝟙 X)).1 ()⟩
  let : Scheme.IsJointlySurjectivePreserving
      (@Syntomic.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  let : P.HasIsos := scheme_precoverage_hasIsos_of_isIso (@Syntomic.{u}) fun f _ ↦
    (AlgebraicGeometry.isSyntomicCovering_singleton_of_isIso f).1 ()
  let : P.IsStableUnderBaseChange := schemePrecoverage_stableUnderBaseChange (@Syntomic.{u})
  let : P.IsStableUnderComposition := schemePrecoverage_stableUnderComposition (@Syntomic.{u})
  let : B.precoverage.IsStableUnderBaseChange := by
    rw [bigSyntomicPrecoverage_eq_comap B]
    infer_instance
  let K : Pretopology (AlgebraicGeometry.BigSyntomicOver B S hS) := (P.comap G).toPretopology
  have hpre : P.comap G =
      B.precoverage.comap (AlgebraicGeometry.BigSyntomicOver.forget B S hS) := by
    calc
      P.comap G = (P.comap B.inclusion).comap
          (AlgebraicGeometry.BigSyntomicOver.forget B S hS) := by
        rw [Precoverage.comap_comp]
      _ = B.precoverage.comap (AlgebraicGeometry.BigSyntomicOver.forget B S hS) :=
        congrArg (fun J : Precoverage B.category ↦
          J.comap (AlgebraicGeometry.BigSyntomicOver.forget B S hS))
          (bigSyntomicPrecoverage_eq_comap B).symm
  have hK : K.toGrothendieck = AlgebraicGeometry.BigSyntomicOver.topology B S hS := by
    calc
      K.toGrothendieck = (P.comap G).toGrothendieck := by
        dsimp [K]
        exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck
      _ = (B.precoverage.comap
          (AlgebraicGeometry.BigSyntomicOver.forget B S hS)).toGrothendieck := by rw [hpre]
      _ = B.topology.over (B.obj S hS) := by
        rw [← CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget]
      _ = AlgebraicGeometry.BigSyntomicOver.topology B S hS := rfl
  let : PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S) := by
    change PreservesLimitsOfShape WalkingCospan G
    infer_instance
  have hCover : ∀ {X : AlgebraicGeometry.BigSyntomicOver B S hS}
      (E : PreZeroHypercover X), E.presieve₀ ∈ K X →
      ∀ i, Flat (G.map (E.f i)) := by
    intro X E hE
    change E.presieve₀ ∈ (P.comap G) X at hE
    rw [Precoverage.mem_comap_iff] at hE
    have hmem : (E.map G).presieve₀ ∈ P (G.obj X) := by
      simpa only [PreZeroHypercover.presieve₀_map] using hE
    have hparts := (Scheme.ofArrows_mem_precoverage_iff
      (@Syntomic)).mp hmem
    intro i
    exact AlgebraicGeometry.flat (hparts.2 i)
  let : EssentiallySmall.{u} B.category := by
    change EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow B.cutoff)
    exact AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigSyntomicOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj S hS)
  exact cohomology_isZero_of_flat_covering_data_transport K hK toOver
    ((SheafOfModules.toSheaf _).obj F) hCover hF U hU p

/-- A parasitic module on the big fppf site has no cohomology at a flat object. -/
@[stacks 0755 "flat_parasitic_vanishing"]
public theorem bigFppfCohomology_isZero_of_isParasitic
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}}
    (F : SheafOfModules.{u} 𝒪)
    (hF : ∀ X : AlgebraicGeometry.BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj X).hom → Subsingleton (F.val.obj (Opposite.op X)))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj F).H' p U) := by
  let P := Scheme.fppfPrecoverage
  let toOver : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) WalkingCospan :=
    AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan
      B.cutoff
  let : HasPullbacks B.Schemes :=
    hasLimitsOfShape_of_closedUnderLimits WalkingCospan
      (fun X : Scheme.{u} ↦ X.size < B.cutoff)
  let : P.HasIsos := by
    change Scheme.fppfPrecoverage.HasIsos
    refine ⟨?_⟩
    intro X Y f hf
    have : IsIso f.base := Functor.map_isIso Scheme.forgetToTop f
    have : Surjective f := ⟨(ConcreteCategory.bijective_of_isIso f.base).surjective⟩
    exact f.singleton_mem_fppfPrecoverage
  let : P.IsStableUnderBaseChange := by infer_instance
  let : P.IsStableUnderComposition := by infer_instance
  let : B.precoverage.IsStableUnderBaseChange := by
    rw [bigFppf_precoverage_eq B]
    infer_instance
  let K : Pretopology (AlgebraicGeometry.BigFppfOver B S hS) := (P.comap G).toPretopology
  have hpre : P.comap G =
      (B.precoverage.comap (AlgebraicGeometry.BigFppfOver.forget B S hS)) := by
    calc
      P.comap G = (P.comap B.inclusion).comap
          (AlgebraicGeometry.BigFppfOver.forget B S hS) := by
        rw [Precoverage.comap_comp]
      _ = B.precoverage.comap (AlgebraicGeometry.BigFppfOver.forget B S hS) :=
        congrArg (fun J : Precoverage B.Schemes ↦
          J.comap (AlgebraicGeometry.BigFppfOver.forget B S hS))
          (bigFppf_precoverage_eq B).symm
  have hK : K.toGrothendieck = AlgebraicGeometry.BigFppfOver.topology B S hS := by
    calc
      K.toGrothendieck = (P.comap G).toGrothendieck := by
        dsimp [K]
        exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck
      _ = (B.precoverage.comap
          (AlgebraicGeometry.BigFppfOver.forget B S hS)).toGrothendieck := by rw [hpre]
      _ = B.topology.over (B.obj hS) := by
        rw [← CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget]
      _ = AlgebraicGeometry.BigFppfOver.topology B S hS := rfl
  let : PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S) := by
    change PreservesLimitsOfShape WalkingCospan G
    infer_instance
  have hCover : ∀ {X : AlgebraicGeometry.BigFppfOver B S hS}
      (E : PreZeroHypercover X), E.presieve₀ ∈ K X →
      ∀ i, Flat (G.map (E.f i)) := by
    intro X E hE
    change E.presieve₀ ∈ (P.comap G) X at hE
    rw [Precoverage.mem_comap_iff] at hE
    have hmem : (E.map G).presieve₀ ∈ Scheme.fppfPrecoverage (G.obj X) := by
      simpa only [PreZeroHypercover.presieve₀_map] using hE
    rw [Scheme.fppfPrecoverage_eq_inf] at hmem
    exact ((Scheme.ofArrows_mem_precoverage_iff (@Flat)).mp hmem.1).2
  let : EssentiallySmall.{u} B.Schemes := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj hS)
  exact cohomology_isZero_of_flat_covering_data_transport K hK toOver
    ((SheafOfModules.toSheaf _).obj F) hCover hF U hU p

end AlgebraicGeometry

end
