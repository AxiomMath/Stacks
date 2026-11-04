module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Point.Map
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the small affine étale site

The small affine étale site of a scheme has enough points.

## Main results

* `AlgebraicGeometry.smallAffineEtale_hasConservativeFamily` states that the small affine étale
  site has enough points.

## Implementation notes

The site is relative to a chosen big étale site containing the base scheme. It is essentially
small, so it may be replaced by a small model; on the small model the localizations at its
objects cover the final object and have finite covering refinements, which is the criterion for
the existence of points. The conservative family is then transported back along the equivalence.

The two auxiliary functors into the étale objects over `S` and into the affine objects over `S`
are recorded explicitly because the essential smallness is deduced from the essential smallness
of affine schemes étale over `S`.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u u₁ v₁ w₁ u₂ v₂

namespace AlgebraicGeometry

private abbrev affineEtaleObjects (S : Scheme.{u}) : ObjectProperty S.Etale :=
  fun X => IsAffine X.left

private def smallAffineEtaleToEtale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicGeometry.SmallAffineEtale B S hS ⥤ S.Etale where
  obj X := MorphismProperty.Over.mk (P := @Etale) (Q := ⊤)
    (B.inclusion.map X.obj.obj.hom) X.obj.property
  map := fun {X Y} f => MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤)
    ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map f) (by
      change B.inclusion.map f.hom.hom.left ≫ B.inclusion.map Y.obj.obj.hom =
        B.inclusion.map X.obj.obj.hom
      rw [← B.inclusion.map_comp]
      exact congrArg B.inclusion.map f.hom.hom.w)
  map_id X := by apply MorphismProperty.Over.Hom.ext; rfl
  map_comp f g := by apply MorphismProperty.Over.Hom.ext; rfl

private def smallAffineEtaleToAffineEtale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicGeometry.SmallAffineEtale B S hS ⥤
      (affineEtaleObjects S).FullSubcategory :=
  (affineEtaleObjects S).lift (smallAffineEtaleToEtale B S hS) fun X => X.property

private instance smallAffineEtaleToEtale_full
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallAffineEtaleToEtale B S hS).Full where
  map_surjective := by
    intro X Y f
    let g : X.obj.obj.left ⟶ Y.obj.obj.left := B.inclusion.preimage f.left
    have hg : B.inclusion.map (g ≫ Y.obj.obj.hom) = B.inclusion.map X.obj.obj.hom := by
      rw [Functor.map_comp,
        show B.inclusion.map g = f.left from B.inclusion.map_preimage f.left]
      exact MorphismProperty.Over.w f
    exact ⟨ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk g
      (B.inclusion.map_injective hg))),
      MorphismProperty.Over.Hom.ext (B.inclusion.map_preimage f.left)⟩

private instance smallAffineEtaleToEtale_faithful
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallAffineEtaleToEtale B S hS).Faithful where
  map_injective h := (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map_injective
    (congrArg (·.left) h)

private instance smallAffineEtaleToAffineEtale_full
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallAffineEtaleToAffineEtale B S hS).Full :=
  Functor.Full.of_comp_faithful_iso
    ((affineEtaleObjects S).liftCompιIso (smallAffineEtaleToEtale B S hS) fun X => X.property)

private instance smallAffineEtaleToAffineEtale_faithful
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallAffineEtaleToAffineEtale B S hS).Faithful :=
  Functor.Faithful.of_comp_iso
    ((affineEtaleObjects S).liftCompιIso (smallAffineEtaleToEtale B S hS) fun X => X.property)

private theorem essentiallySmall_smallAffineEtale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EssentiallySmall.{u} (AlgebraicGeometry.SmallAffineEtale B S hS) := by
  let P := affineEtaleObjects S
  have hP : ObjectProperty.EssentiallySmall.{u} P := by
    let F := Scheme.AffineEtale.Spec S
    let Q := F.essImage.isoClosure
    have : ObjectProperty.EssentiallySmall.{u} Q := inferInstance
    apply ObjectProperty.EssentiallySmall.of_le (Q := Q)
    intro X hX
    let : IsAffine X.left := hX
    let A : Scheme.AffineEtale S :=
      MorphismProperty.CostructuredArrow.mk (P := @Etale.{u}) (Q := ⊤)
        (X.left.isoSpec.inv ≫ X.hom) (by infer_instance)
    refine ⟨F.obj A, ⟨A, ⟨Iso.refl _⟩⟩, ⟨MorphismProperty.Over.isoMk
      X.left.isoSpec (by
        show X.left.isoSpec.hom ≫ (X.left.isoSpec.inv ≫ X.hom) = X.hom
        simp)⟩⟩
  have : LocallySmall.{u} S.Etale := inferInstance
  have : EssentiallySmall.{u} P.FullSubcategory := inferInstance
  exact essentiallySmall_of_fully_faithful (smallAffineEtaleToAffineEtale B S hS)

/-- Every covering sieve of the small affine étale site contains a covering sieve generated by
a pre-`0`-hypercover with finitely many components. -/
public theorem finite_refinement_smallAffineEtale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicGeometry.SmallAffineEtale B S hS} {R : Sieve X}
    (hR : R ∈ AlgebraicGeometry.SmallAffineEtale.topology B S hS X) :
    ∃ E : PreZeroHypercover.{u + 1} X, Finite E.I₀ ∧ E.sieve₀ ≤ R ∧
      E.sieve₀ ∈ AlgebraicGeometry.SmallAffineEtale.topology B S hS X := by
  let K := AlgebraicGeometry.SmallAffineEtale.precoverage B S hS
  let := AlgebraicGeometry.hasPullbacks_smallAffineEtale B S hS
  exact finite_refinement_saturate K (by
    intro X R hR
    obtain ⟨E, hEq, hCov⟩ := (AlgebraicGeometry.SmallAffineEtale.mem_precoverage_iff B S hS).mp hR
    exact ⟨E, hCov.2, hEq⟩) ((K.mem_toGrothendieck_iff).mp hR)

/-- If every covering sieve for `J` contains a covering sieve generated by a pre-`0`-hypercover
with finitely many components, then every covering sieve of `X` for the topology induced on `D`
along `e.inverse` contains a covering sieve generated by finitely many arrows `Y i ⟶ X`. -/
public theorem finite_refinement_equiv
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [HasPullbacks C] (e : C ≌ D) (J : GrothendieckTopology C)
    {X : D} {R : Sieve X} (hR : R ∈ e.inverse.inducedTopology J X)
    (hfinite : ∀ {X : C} {R : Sieve X}, R ∈ J X →
      ∃ E : PreZeroHypercover.{u₁} X, Finite E.I₀ ∧ E.sieve₀ ≤ R ∧ E.sieve₀ ∈ J X) :
    ∃ (ι : Type) (_ : Finite ι) (Y : ι → D) (f : ∀ i, Y i ⟶ X),
      Sieve.ofArrows Y f ≤ R ∧ Sieve.ofArrows Y f ∈ e.inverse.inducedTopology J X := by
  let F := e.functor
  let G := e.inverse
  have hR' : R.functorPushforward G ∈ J (G.obj X) := by
    simpa [Functor.mem_inducedTopology_iff_of_isCoverDense] using hR
  obtain ⟨E, hFin, hLe, hCov⟩ := hfinite hR'
  let : Fintype E.I₀ := Fintype.ofFinite E.I₀
  let r : Fin (Fintype.card E.I₀) ≃ E.I₀ := (Fintype.equivFin E.I₀).symm
  let E' := E.reindex r
  have hReindex : E'.sieve₀ = E.sieve₀ := congrArg Sieve.generate (E.presieve₀_reindex r)
  let Y (k : Fin (Fintype.card E.I₀)) : D := F.obj (E'.X k)
  let f (k : Fin (Fintype.card E.I₀)) : Y k ⟶ X :=
    F.map (E'.f k) ≫ e.counit.app X
  let H : Sieve X := Sieve.ofArrows Y f
  have hFactorR : ∀ k, R (f k) := by
    intro k
    obtain ⟨Z, g, h, hg, hEq⟩ := (hReindex ▸ hLe) _ (E'.sieve₀_f k)
    have hfactor : f k = (F.map h ≫ e.counit.app Z) ≫ g := by
      dsimp [f]
      rw [hEq, Functor.map_comp, e.fun_inv_map]
      simp [Category.assoc]
    rw [hfactor]
    exact R.downward_closed hg _
  have hUnitFactor : ∀ k, E'.f k = e.unit.app (E'.X k) ≫ G.map (f k) := by
    intro k
    calc
      E'.f k = (E'.f k ≫ e.unit.app (G.obj X)) ≫ G.map (e.counit.app X) := by simp [G]
      _ = (e.unit.app (E'.X k) ≫ (F ⋙ G).map (E'.f k)) ≫ G.map (e.counit.app X) := by
        rw [← e.unit.naturality (E'.f k)]
        simp
      _ = e.unit.app (E'.X k) ≫ G.map (f k) := by simp [f]
  have hPushCover : E'.sieve₀ ≤ H.functorPushforward G := by
    rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro k
    show (H.arrows.functorPushforward G) (E'.f k)
    exact ⟨Y k, f k, e.unit.app (E'.X k),
      (Sieve.ofArrows_mk (Y := Y) (f := f) k), hUnitFactor k⟩
  have hHcover : H.functorPushforward G ∈ J (G.obj X) :=
    J.superset_covering hPushCover (by simpa [hReindex] using hCov)
  refine ⟨Fin (Fintype.card E.I₀), inferInstance, Y, f, ?_, ?_⟩
  · rwa [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  · simpa [H, Functor.mem_inducedTopology_iff_of_isCoverDense] using hHcover

/-- **Stacks 06VX, small affine étale case.** The small affine étale site of a
scheme has enough points. -/
@[stacks 06VX "small_affine_etale"]
public theorem smallAffineEtale_hasConservativeFamily
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    GrothendieckTopology.HasConservativeFamily.{u}
      (AlgebraicGeometry.SmallAffineEtale.topology B S hS) := by
  let C := AlgebraicGeometry.SmallAffineEtale B S hS
  let J := AlgebraicGeometry.SmallAffineEtale.topology B S hS
  have : HasPullbacks C := AlgebraicGeometry.hasPullbacks_smallAffineEtale B S hS
  have : EssentiallySmall.{u} C := essentiallySmall_smallAffineEtale B S hS
  have : LocallySmall.{u} C := inferInstance
  let e := equivSmallModel.{u} C
  let C₀ := SmallModel.{u} C
  let G := e.inverse
  let K := G.inducedTopology J
  have : HasLimitsOfShape WalkingCospan C₀ :=
    Adjunction.hasLimitsOfShape_of_equivalence G
  have : ∀ i : C₀, HasPullbacks (Over i) := fun _ => inferInstance
  have : ∀ i : C₀, Small.{u} (Over i) := fun _ => inferInstance
  have hTop : K.CoversTop (fun X : C₀ => X) := fun X =>
    K.superset_covering (fun Y _ _ => ⟨Y, ⟨𝟙 Y⟩⟩) (K.top_mem X)
  have hRefine : ∀ (i : C₀) ⦃X : Over i⦄ (R : Sieve X),
      R ∈ (K.over i) X →
        ∃ (ι : Type) (_ : Finite ι) (Y : ι → Over i) (g : ∀ k, Y k ⟶ X),
          Sieve.ofArrows Y g ≤ R ∧ Sieve.ofArrows Y g ∈ (K.over i) X := by
    intro i X R hR
    have hR' : Sieve.overEquiv X R ∈ K X.left := (K.mem_over_iff R).mp hR
    obtain ⟨ι, hFin, Z, f, hLe, hCov⟩ :=
      finite_refinement_equiv e J hR' (finite_refinement_smallAffineEtale B S hS)
    let Y (k : ι) : Over i := Over.mk (f k ≫ X.hom)
    let g (k : ι) : Y k ⟶ X := Over.homMk (f k) (by simp [Y])
    have hEq : (Sieve.overEquiv X) (Sieve.ofArrows Y g) = Sieve.ofArrows Z f := by
      show Sieve.functorPushforward (Over.forget i)
          (Sieve.generate (Presieve.ofArrows Y g)) =
        Sieve.generate (Presieve.ofArrows Z f)
      rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows]
      rfl
    refine ⟨ι, hFin, Y, g, ?_, ?_⟩
    · exact (Sieve.overEquiv X).le_iff_le.mp (by rwa [hEq])
    · rwa [K.mem_over_iff, hEq]
  have : GrothendieckTopology.HasEnoughPoints.{u} K :=
    GrothendieckTopology.hasEnoughPoints_of_coversTop_of_exists_finite_refinement
      (J := K) (U := fun X : C₀ => X) hTop hRefine
  exact hasConservativeFamily_of_denseSubsite K J G
    (GrothendieckTopology.HasConservativeFamily.of_hasEnoughPoints K)

end AlgebraicGeometry
