module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Comparing the étale precoverages with comap along the inclusions

The covering families of a big étale site, and of its slices and full subcategories, were
specified by hand. This file identifies the precoverages they present with precoverages
obtained by `Precoverage.comap` along the canonical functors:

* the precoverage of a big étale site is the étale precoverage of schemes comapped along its
  inclusion into schemes;
* the precoverage of the big étale slice over `S` is the site's own comapped along the slice
  forgetful functor;
* the precoverage of the small étale site is the slice's comapped along the full inclusion.

These identifications are what let the stability properties — closure under isomorphisms, base
change and composition — be inherited from the corresponding properties of the étale
precoverage on all schemes, instead of being reproved for each category. They also identify the
slice topology with Mathlib's localized topology, which is what makes the general slice
machinery applicable.

## Main results

* `AlgebraicGeometry.bigEtalePrecoverage_eq_comap`,
  `AlgebraicGeometry.bigEtaleOver_precoverage_eq_comap`,
  `AlgebraicGeometry.smallEtale_precoverage_eq_comap` — the three identifications.
* `AlgebraicGeometry.bigEtaleOver_topology_eq` — the slice topology is the localized topology.
* The instances record that the precoverages have isomorphisms and are stable under base change
  and composition.

## Implementation notes

Each identification needs that a presieve on the smaller category is determined by its image
on the larger one, which is the content of `overForget_presieve_map_injective` and
`smallEtale_presieve_map_injective`; both hold because the functors in question are fully
faithful. In the other direction a covering family upstairs has to be lifted, which uses that
an object of the slice over an object étale over `S` is itself étale over `S`.

`overForget_presieve_map_injective` is stated for an arbitrary slice category, since nothing
about schemes enters it.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Lemma 34.4.5 (Tag 021H)](https://stacks.math.columbia.edu/tag/021H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The precoverage of a big étale site is the étale precoverage of schemes, comapped along
the site's canonical inclusion into all schemes. -/
public theorem bigEtalePrecoverage_eq_comap
    (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    B.precoverage = Scheme.etalePrecoverage.comap B.inclusion := by
  ext X R
  rw [AlgebraicGeometry.BigEtaleSite.mem_precoverage_iff, Precoverage.mem_comap_iff]
  refine ⟨fun ⟨E, hR, hE⟩ => hR ▸ E.presieve₀_map (F := B.inclusion) ▸ hE.1, fun hR => ?_⟩
  let E : PreZeroHypercover.{u + 1} X :=
    ⟨R.uncurry, fun i => i.1.1, fun i => i.1.2⟩
  have hE : E.presieve₀ = R := by
    funext Y g
    exact propext ⟨fun ⟨i⟩ => i.2, fun hg => Presieve.ofArrows.mk (⟨⟨Y, g⟩, hg⟩ : R.uncurry)⟩
  have hEt : AlgebraicGeometry.IsEtaleCovering ⟨X, E⟩ := by
    change (E.map B.inclusion).presieve₀ ∈ _
    rw [PreZeroHypercover.presieve₀_map, hE]
    exact hR
  obtain ⟨V, hV, hXV, hcomb⟩ := B.exists_covering_rep ⟨X, E⟩ hEt
  cases hXV
  exact ⟨V.2, hE.symm.trans
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb), hV⟩

/-- Two presieves with the same image under `F` are equal, provided that an arrow whose image
is, up to an `eqToHom`, the image of `g` is `g` itself. -/
private theorem presieve_eq_of_map_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {X : C} {R Q : Presieve X}
    (key : ∀ {Y Z : C} (g : Y ⟶ X) (a : Z ⟶ X) (P : Presieve X), P a →
      ∀ hZ : F.obj Z = F.obj Y, F.map a = eqToHom hZ ≫ F.map g → P g)
    (h : R.map F = Q.map F) : R = Q := by
  have this (P Q : Presieve X) (hmap : P.map F = Q.map F) {Y : C} (g : Y ⟶ X) (hp : P g) : Q g := by
    obtain ⟨Z, hZ, a, ha, hfac⟩ := Presieve.map_iff.1 (hmap ▸ Presieve.map_map hp)
    exact key g a Q ha hZ hfac
  funext Y g
  exact propext ⟨this R Q h g, this Q R h.symm g⟩

/-- A presieve on an object of a slice category is determined by its image under the slice
forgetful functor. -/
public theorem overForget_presieve_map_injective {C : Type*} [Category C]
    {X : C} {U : Over X} {R Q : Presieve U}
    (h : R.map (Over.forget X) = Q.map (Over.forget X)) : R = Q := by
  refine presieve_eq_of_map_eq (fun {V W} g a P ha hW hfac => ?_) h
  change a.left = eqToHom hW ≫ g.left at hfac
  have hWV : W = V := CostructuredArrow.obj_ext W V hW <| by
    simpa only [Functor.id_map, ← Over.w g, Category.assoc, ← Over.w a]
      using congrArg (· ≫ U.hom) hfac.symm
  cases hWV
  have hag : a = g := Over.OverMorphism.ext (by simpa using hfac)
  simpa [hag] using ha

/-- The precoverage of the big étale category over `S` is the site's precoverage comapped
along the slice forgetful functor. -/
public theorem bigEtaleOver_precoverage_eq_comap
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    BigEtaleOver.precoverage B S hS =
      B.precoverage.comap (Over.forget (B.obj S hS)) := by
  ext U R
  rw [BigEtaleOver.mem_precoverage_iff, Precoverage.mem_comap_iff,
    AlgebraicGeometry.BigEtaleSite.mem_precoverage_iff]
  refine ⟨fun ⟨E, hR, hE⟩ =>
    ⟨E.map (Over.forget (B.obj S hS)), hR ▸ (E.presieve₀_map (F := Over.forget _)).symm, hE⟩,
    fun ⟨E, hR, hE⟩ => ?_⟩
  let E' : PreZeroHypercover.{u + 1} U :=
    ⟨E.I₀, fun i => Over.mk (E.f i ≫ U.hom),
      fun i => Over.homMk (E.f i) (by simp)⟩
  have hE' : (E'.map (Over.forget (B.obj S hS))) = E := by
    cases E
    rfl
  have hmap : R.map (Over.forget (B.obj S hS)) = E'.presieve₀.map
      (Over.forget (B.obj S hS)) := by
    rw [hR, ← hE', ← PreZeroHypercover.presieve₀_map]
  exact ⟨E', overForget_presieve_map_injective hmap, by
    simpa [BigEtaleOver.IsCovering, hE'] using hE⟩

/-- The precoverage of a big étale site has isomorphisms. -/
public instance bigEtalePrecoverage_hasIsos
    (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    B.precoverage.HasIsos := by
  constructor
  intro U V g hg
  rw [AlgebraicGeometry.BigEtaleSite.mem_precoverage_iff]
  refine ⟨PreZeroHypercover.singleton g, ?_, B.coverings_isSite.1 g⟩
  simp

/-- The precoverage of the big étale category over `S` has isomorphisms. -/
public instance bigEtaleOver_precoverage_hasIsos
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigEtaleOver.precoverage B S hS).HasIsos := by
  rw [bigEtaleOver_precoverage_eq_comap B S hS]
  infer_instance

/-- The étale precoverage on all schemes is stable under base change. -/
public instance etalePrecoverage_isStableUnderBaseChange :
    Scheme.etalePrecoverage.IsStableUnderBaseChange := by
  unfold Scheme.etalePrecoverage
  refine ⟨?_⟩
  intro ι X Y f hf Z g P p₁ p₂ h
  change Presieve.ofArrows Y f ∈ Scheme.jointlySurjectivePrecoverage X ∧
    Presieve.ofArrows Y f ∈ (MorphismProperty.precoverage @Etale) X at hf
  change Presieve.ofArrows P p₁ ∈ Scheme.jointlySurjectivePrecoverage Z ∧
    Presieve.ofArrows P p₁ ∈ (MorphismProperty.precoverage @Etale) Z
  refine ⟨?_, ?_⟩
  · exact Precoverage.mem_coverings_of_isPullback f hf.1 g p₁ p₂ h
  · intro W k hk
    obtain ⟨i⟩ := hk
    exact MorphismProperty.of_isPullback (h i).flip (hf.2 ⟨i⟩)

/-- The precoverage of a big étale site is stable under base change. -/
public instance bigEtalePrecoverage_stableUnderBaseChange
    (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    B.precoverage.IsStableUnderBaseChange := by
  have : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigEtaleSiteInclusion B
  rw [bigEtalePrecoverage_eq_comap B]
  infer_instance

/-- The precoverage of the big étale category over `S` is stable under base change. -/
public instance bigEtaleOver_precoverage_stableUnderBaseChange
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigEtaleOver.precoverage B S hS).IsStableUnderBaseChange := by
  have : B.precoverage.IsStableUnderBaseChange := bigEtalePrecoverage_stableUnderBaseChange B
  rw [bigEtaleOver_precoverage_eq_comap B S hS]
  infer_instance

/-- The precoverage of the big étale category over `S` is stable under composition. -/
public instance bigEtaleOver_precoverage_stableUnderComposition
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigEtaleOver.precoverage B S hS).IsStableUnderComposition := by
  have : MorphismProperty.IsStableUnderComposition (@Etale) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale)).toIsStableUnderComposition
  have : Scheme.etalePrecoverage.IsStableUnderComposition := by
    unfold Scheme.etalePrecoverage
    refine ⟨?_⟩
    intro ι S X f hf σ Y g hg
    have hf' := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp hf
    have hg' i := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp (hg i)
    refine (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mpr ⟨fun z => ?_, fun ⟨i, j⟩ =>
      MorphismProperty.comp_mem @Etale (g i j) (f i) ((hg' i).2 j) (hf'.2 i)⟩
    obtain ⟨i, y, rfl⟩ := hf'.1 z
    obtain ⟨j, x, rfl⟩ := (hg' i).1 y
    exact ⟨⟨i, j⟩, x, rfl⟩
  rw [bigEtaleOver_precoverage_eq_comap B S hS, bigEtalePrecoverage_eq_comap B,
    ← Precoverage.comap_comp]
  infer_instance

/-- The topology of the big étale category over `S` is the localization of the site's
topology at `S`. -/
public theorem bigEtaleOver_topology_eq (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    BigEtaleOver.topology B S hS = B.topology.over (B.obj S hS) := by
  have : B.precoverage.IsStableUnderBaseChange := bigEtalePrecoverage_stableUnderBaseChange B
  rw [BigEtaleOver.topology, bigEtaleOver_precoverage_eq_comap B S hS]
  exact (over_toGrothendieck_eq_toGrothendieck_comap_forget
    B.precoverage (B.obj S hS)).symm

/-- A slice of the underlying category of a big étale site has equalizers. -/
public instance bigEtaleOver_hasEqualizers (B : AlgebraicGeometry.BigEtaleSite.{u})
    (X : B.Scheme) : HasEqualizers (Over X) := by
  have : HasPullbacks (Over X) := inferInstance
  have : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

/-- A presieve on an object of the small étale category is determined by its image in the big
étale category over `S`. -/
public theorem smallEtale_presieve_map_injective
    {B : AlgebraicGeometry.BigEtaleSite.{u}} {T : AlgebraicGeometry.Scheme.{u}}
    {hT : B.Contains T} {X : SmallEtale B T hT} {R Q : Presieve X}
    (h : R.map (SmallEtale.inclusion B T hT) =
      Q.map (SmallEtale.inclusion B T hT)) : R = Q := by
  refine presieve_eq_of_map_eq (fun {Y Z} g a P ha hZ hfac => ?_) h
  have hZY : Z = Y := by
    cases Z
    cases Y
    cases hZ
    rfl
  cases hZY
  have hfac' : a = g := (SmallEtale.inclusion B T hT).map_injective (by simpa using hfac)
  simpa [hfac'] using ha

/-- The precoverage of the small étale category of `T` is the precoverage of the big étale
category over `T` comapped along the full inclusion. -/
public theorem smallEtale_precoverage_eq_comap
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme) :
    SmallEtale.precoverage B T.obj T.property =
      (BigEtaleOver.precoverage B T.obj T.property).comap
        (SmallEtale.inclusion B T.obj T.property) := by
  ext X R
  rw [SmallEtale.mem_precoverage_iff, Precoverage.mem_comap_iff,
    BigEtaleOver.mem_precoverage_iff]
  refine ⟨fun ⟨E, hR, hE⟩ => ⟨E.map (SmallEtale.inclusion B T.obj T.property),
    hR ▸ (E.presieve₀_map (F := SmallEtale.inclusion B T.obj T.property)).symm, hE⟩,
    fun ⟨E, hR, hE⟩ => ?_⟩
  change B.IsCovering _ at hE
  have hcover := AlgebraicGeometry.BigEtaleSite.IsCovering.etale hE
  change (E.map (BigEtaleOver.toScheme B T.obj T.property)).presieve₀ ∈
    Scheme.jointlySurjectivePrecoverage _ ∧
      (E.map (BigEtaleOver.toScheme B T.obj T.property)).presieve₀ ∈
        (MorphismProperty.precoverage @Etale) _ at hcover
  have hEtale (i : E.I₀) :
      Etale ((BigEtaleOver.toScheme B T.obj T.property).map (E.f i)) :=
    (MorphismProperty.ofArrows_mem_precoverage.mp hcover.2) i
  let E' : PreZeroHypercover.{u + 1} X :=
    ⟨E.I₀, fun i => ⟨E.X i, by
      change Etale (B.inclusion.map (E.X i).hom)
      have hcomp :
          (BigEtaleOver.toScheme B T.obj T.property).map (E.f i) ≫
            B.inclusion.map X.obj.hom = B.inclusion.map (E.X i).hom := by
        change B.inclusion.map ((E.f i).left ≫ X.obj.hom) =
          B.inclusion.map (E.X i).hom
        exact congrArg B.inclusion.map (Over.w (E.f i))
      rw [← hcomp]
      have : Etale ((BigEtaleOver.toScheme B T.obj T.property).map (E.f i)) := hEtale i
      have : Etale (B.inclusion.map X.obj.hom) := X.property
      infer_instance⟩,
     fun i => CategoryTheory.ObjectProperty.homMk (E.f i)⟩
  have hmap : E'.map (SmallEtale.inclusion B T.obj T.property) = E := by
    cases E
    rfl
  have hpresieve :
      E'.presieve₀.map (SmallEtale.inclusion B T.obj T.property) = E.presieve₀ := by
    rw [← PreZeroHypercover.presieve₀_map, hmap]
  refine ⟨E', smallEtale_presieve_map_injective (hR.trans hpresieve.symm), ?_⟩
  change B.IsCovering
    ⟨(Over.forget (B.obj T.obj T.property)).obj X.obj,
      (E'.map (SmallEtale.inclusion B T.obj T.property)).map
        (Over.forget (B.obj T.obj T.property))⟩
  change B.IsCovering
    ⟨(Over.forget (B.obj T.obj T.property)).obj X.obj, E.map _⟩ at hE
  simpa [hmap] using hE

/-- The precoverage of the small étale category of `S` has isomorphisms. -/
public instance smallEtale_precoverage_hasIsos (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S) :
    (SmallEtale.precoverage B S hS).HasIsos := by
  rw [smallEtale_precoverage_eq_comap B ⟨S, hS⟩]
  infer_instance

/-- The precoverage of the small étale category of `S` is stable under base change. -/
public instance smallEtale_precoverage_stableUnderBaseChange
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    (SmallEtale.precoverage B S hS).IsStableUnderBaseChange := by
  rw [smallEtale_precoverage_eq_comap B ⟨S, hS⟩]
  have : PreservesLimitsOfShape WalkingCospan (SmallEtale.inclusion B S hS) := inferInstance
  infer_instance

/-- The precoverage of the small étale category of `S` is stable under composition. -/
public instance smallEtale_precoverage_stableUnderComposition
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    (SmallEtale.precoverage B S hS).IsStableUnderComposition := by
  rw [smallEtale_precoverage_eq_comap B ⟨S, hS⟩]
  infer_instance

end AlgebraicGeometry
