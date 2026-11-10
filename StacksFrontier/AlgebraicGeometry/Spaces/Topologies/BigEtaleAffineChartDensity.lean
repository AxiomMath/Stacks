module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedProperPushforward

/-!
# Detecting isomorphisms on the big étale site on affine charts through étale charts

Let `X` be an algebraic space of a big étale site `T`. Call an object `w : W ⟶ X` of the big
étale site of `X` an *affine chart through an étale chart* when `W` is the algebraic space
represented by an affine scheme and `w` factors as `a ≫ v` with `v : V ⟶ X` étale and `V` the
algebraic space represented by an affine scheme. These objects generate a covering sieve of every
object of the big étale site of `X`: an object `U ⟶ X` is covered by the base changes of an
affine étale atlas of `X`, and each of those by affine étale charts (Stacks 041F). So a morphism
of abelian sheaves, or of the derived category, on the big étale site of `X` is an isomorphism as
soon as its restrictions to the spaces-étale sites of all such objects are.

This is the form in which a base-change statement for algebraic spaces is reduced to an affine
base and an affine base change.

## Main definitions

In the namespace `AlgebraicGeometry.BigEtaleSpaceSite`:

* `IsAffineThroughEtaleChart`: the objects described above.

## Main results

* `generate_affineThroughEtaleChartPresieve_mem`: they generate a covering sieve of every object.
* `isIso_of_isIso_smallEtaleRestriction_map_of_affineThroughEtaleChart` and
  `isIso_of_isIso_mapDerivedCategory_affineThroughEtaleChart`: detection of isomorphisms of
  abelian sheaves and of the derived category of the big étale site.

## References

* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard

/-- The objects `w : W ⟶ X` of the big étale site of `X` with `W` represented by an affine scheme
and `w = a ≫ v` for an étale `v : V ⟶ X` with `V` represented by an affine scheme. -/
def IsAffineThroughEtaleChart (X : T.Spaces) : ObjectProperty (Over X) :=
  fun Y ↦ ∃ (W₀ V₀ : BigFppfOver T.fppfSite S T.fppf_mem),
    IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj W₀) ∧
    IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj V₀) ∧
    ∃ (v : Space.yonedaSpace T.fppfSite S T.fppf_mem V₀ ⟶ X)
      (a : Space.yonedaSpace T.fppfSite S T.fppf_mem W₀ ⟶
        Space.yonedaSpace T.fppfSite S T.fppf_mem V₀),
      Space.IsEtale T.fppfSite S T.fppf_mem v.hom ∧ Y = Over.mk (a ≫ v)

/-- The presieve of arrows out of affine charts through étale charts. -/
def affineThroughEtaleChartPresieve {X : T.Spaces} (Y : Over X) : Presieve Y :=
  fun {Z} _ ↦ IsAffineThroughEtaleChart T X Z

/-- **Affine charts through étale charts generate a covering sieve of every object of the big
étale site of `X`.** -/
theorem generate_affineThroughEtaleChartPresieve_mem {X : T.Spaces} (Y : Over X) :
    Sieve.generate (affineThroughEtaleChartPresieve T Y) ∈ T.bigEtaleTopology X Y := by
  set g₀ : Y.left.1 ⟶ X.1 := Y.hom.hom
  obtain ⟨W, b, hWaff, hbEt, -, hcov⟩ := Space.exists_isEtaleCovering_affine
    T.fppfSite S T.fppf_mem X.1 X.2
  have hpb := Space.isEtaleCovering_pullback T.fppfSite S T.fppf_mem g₀ Y.left.2 _ b hcov
  choose W' b' hW'aff hb'Et hb'pt hcov' using fun x ↦ Space.exists_isEtaleCovering_affine
    T.fppfSite S T.fppf_mem (pullback g₀ (b x)) (hpb.source_isAlgebraicSpace x)
  have hcomp := Space.isEtaleCovering_comp T.fppfSite S T.fppf_mem _ _ _ _ _ hpb hcov'
  let E : PreZeroHypercover.{u + 2} Y.left :=
    { I₀ := ULift.{u + 2} ((x : Space.points T.fppfSite S T.fppf_mem X.1) ×
        Space.points T.fppfSite S T.fppf_mem (pullback g₀ (b x)))
      X := fun i ↦ Space.yonedaSpace T.fppfSite S T.fppf_mem (W' i.down.1 i.down.2)
      f := fun i ↦ ObjectProperty.homMk (b' i.down.1 i.down.2 ≫ pullback.fst g₀ (b i.down.1)) }
  have hE : Space.IsEtaleCoveringFamily T.fppfSite S T.fppf_mem ⟨Y.left, E⟩ :=
    Space.IsEtaleCovering.reindex T.fppfSite S T.fppf_mem hcomp
      (σ := ULift.down) fun x ↦ ⟨ULift.up x, rfl⟩
  have hgen : Sieve.generate E.presieve₀ ∈ T.topology Y.left := by
    obtain ⟨⟨V, F⟩, hF, hleft, hcomb⟩ := T.covering_representative ⟨Y.left, E⟩ hE
    cases hleft
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb,
      T.mem_precoverage_iff]
    exact ⟨F, rfl, hF⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro Z g ⟨i⟩
  rw [Sieve.overEquiv_iff]
  refine Sieve.le_generate _ _ _ ⟨W' i.down.1 i.down.2, W i.down.1, hW'aff _ _, hWaff _,
    ObjectProperty.homMk (b i.down.1),
    ObjectProperty.homMk (b' i.down.1 i.down.2 ≫ pullback.snd g₀ (b i.down.1)),
    hbEt i.down.1, ?_⟩
  congr 1
  refine ObjectProperty.hom_ext _ ?_
  change (b' i.down.1 i.down.2 ≫ pullback.fst g₀ (b i.down.1)) ≫ g₀ =
    (b' i.down.1 i.down.2 ≫ pullback.snd g₀ (b i.down.1)) ≫ b i.down.1
  rw [Category.assoc, pullback.condition, Category.assoc]

/-- The affine charts through étale charts are cover-dense in the big étale site of `X`. -/
instance isCoverDense_affineThroughEtaleChart (X : T.Spaces) :
    (IsAffineThroughEtaleChart T X).ι.IsCoverDense (T.bigEtaleTopology X) where
  is_cover U := by
    refine GrothendieckTopology.superset_covering _ ?_
      (generate_affineThroughEtaleChartPresieve_mem T U)
    rw [Sieve.generate_le_iff]
    rintro Z f hZ
    exact @Presieve.in_coverByImage _ _ _ _ (IsAffineThroughEtaleChart T X).ι U ⟨Z, hZ⟩ f

/-- The value at `V` of a morphism of abelian sheaves on the big étale site of `X` is invertible
as soon as its restriction to the spaces-étale site of `V` is: the value at `V` is the value of
that restriction at the final object. -/
theorem isIso_app_of_isIso_smallEtaleRestriction_map {X : T.Spaces}
    {M N : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}} (ψ : M ⟶ N) (V : Over X)
    (h : IsIso ((smallEtaleRestriction T V.hom).map ψ)) : IsIso (ψ.hom.app (op V)) := by
  have h₂ : IsIso (((smallEtaleRestriction T V.hom).map ψ).hom.app
      (op (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.left))) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) _ h) _
  let e : (Over.map V.hom).obj ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem
      V.left).obj (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.left)) ≅ V :=
    Over.isoMk (Iso.refl _) (by simp [Space.SpacesEtale.final])
  exact (NatTrans.isIso_app_iff_of_iso ψ.hom e.op).mp h₂

/-- **Isomorphisms of abelian sheaves on the big étale site of `X` are detected on the
spaces-étale sites of the affine charts through étale charts.** -/
theorem isIso_of_isIso_smallEtaleRestriction_map_of_affineThroughEtaleChart {X : T.Spaces}
    {M N : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}} (ψ : M ⟶ N)
    (h : ∀ V : Over X, IsAffineThroughEtaleChart T X V →
      IsIso ((smallEtaleRestriction T V.hom).map ψ)) : IsIso ψ := by
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := (IsAffineThroughEtaleChart T X).ι) ψ ?_
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun V ↦ ?_
  exact isIso_app_of_isIso_smallEtaleRestriction_map T ψ V.unop.obj (h V.unop.obj V.unop.property)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search over the derived category of abelian sheaves on the big étale site
/-- **Isomorphisms of the derived category of the big étale site of `X` are detected on the
spaces-étale sites of the affine charts through étale charts.** -/
theorem isIso_of_isIso_mapDerivedCategory_affineThroughEtaleChart {X : T.Spaces}
    {P Q : DerivedCategory (Sheaf (T.bigEtaleTopology X) Ab.{u + 1})} (φ : P ⟶ Q)
    (h : ∀ V : Over X, IsAffineThroughEtaleChart T X V →
      IsIso ((smallEtaleRestriction T V.hom).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_smallEtaleRestriction_map_of_affineThroughEtaleChart T _ fun V hV ↦ ?_
  exact ((smallEtaleRestriction T V.hom).isIso_mapDerivedCategory_map_iff φ).mp (h V hV) n

end AlgebraicGeometry.BigEtaleSpaceSite

end
