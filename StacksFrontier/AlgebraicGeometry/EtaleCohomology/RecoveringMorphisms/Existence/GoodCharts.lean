module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.ComparisonPresentations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale

/-!
# Affine étale charts over affine opens are dense in the small étale site

The *good charts* of the small étale site of `S` are its affine objects whose image lies in an
affine open of `S` (`AlgebraicGeometry.SmallEtale.IsGoodChart`).  They form a full subcategory
which is cover-dense (`AlgebraicGeometry.SmallEtale.goodChartInclusion_isCoverDense`): every
object is covered by affine opens of itself lying over affine opens of `S`.  This is the
variant of Stacks 04HR along which the global argument of Stacks 04I7 identifies two direct
images, since on a good chart a comparison of representables is available.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-- Every point of `T` has an affine open neighbourhood mapping into an affine open of `S`. -/
lemma exists_affineOpens_mem_le_preimage {T S : Scheme.{u}} (f : T ⟶ S) (x : T) :
    ∃ (V : S.affineOpens) (W : T.affineOpens), x ∈ (W : T.Opens) ∧
      (W : T.Opens) ≤ f ⁻¹ᵁ (V : S.Opens) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  exact ⟨⟨V, hV⟩, ⟨W, hW⟩, hxW, hWV⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the small étale site is a *good chart* when it is affine and lies over an affine
open of `S`. -/
def IsGoodChart : ObjectProperty (SmallEtale B S hS) := fun U =>
  AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B S hS).obj U) ∧
    ∃ V : S.affineOpens, Nonempty (U ⟶ openObj B S hS (V : S.Opens))

/-- The full subcategory of good charts. -/
abbrev GoodChart := (IsGoodChart B S hS).FullSubcategory

/-- The inclusion of the good charts. -/
abbrev goodChartInclusion : GoodChart B S hS ⥤ SmallEtale B S hS := (IsGoodChart B S hS).ι

/-- Every object of the small étale site has a covering family by good charts. -/
theorem exists_isCovering_isGoodChart (X : SmallEtale B S hS) :
    ∃ E : PreZeroHypercover X, SmallEtale.IsCovering B S hS ⟨X, E⟩ ∧
      ∀ i, IsGoodChart B S hS (E.X i) := by
  let T := B.inclusion.obj X.obj.left
  let pX : T ⟶ S := B.inclusion.map X.obj.hom
  choose Vx Wx hxW hWV using exists_affineOpens_mem_le_preimage pX
  let U : T.OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} T
    X i := (Wx i.down : T.Opens).toScheme
    f i := (Wx i.down : T.Opens).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨ULift.up x, ⟨x, hxW x⟩, rfl⟩,
        fun i ↦ inferInstanceAs (IsOpenImmersion (Wx i.down : T.Opens).ι)⟩ }
  obtain ⟨V, hV, hEq⟩ :=
    AlgebraicGeometry.BigEtaleSite.exists_isCovering_tautologicallyEquivalent_openCover
      B X.obj.left U
  choose β e he using hEq.2
  have hfac (i : V.I₀) :
      (e i).hom ≫ (Wx (β i).down : T.Opens).ι = B.inclusion.map (V.f i) := by
    simpa [PreZeroHypercover.map] using he i
  have hEt (i : V.I₀) : Etale (B.inclusion.map (V.f i)) := by
    rw [← hfac i]
    let : IsIso (e i).hom := (e i).isIso_hom
    exact Etale.etale_comp (e i).hom (Wx (β i).down : T.Opens).ι
  let E : PreZeroHypercover X := {
    I₀ := V.I₀
    X i := by
      let : Etale (B.inclusion.map X.obj.hom) := X.property
      have := hEt i
      exact ⟨Over.mk (V.f i ≫ X.obj.hom), by
        show Etale (B.inclusion.map (V.f i) ≫ B.inclusion.map X.obj.hom)
        exact Etale.etale_comp (B.inclusion.map (V.f i)) (B.inclusion.map X.obj.hom)⟩
    f i := ObjectProperty.homMk (Over.homMk (V.f i) (by simp)) }
  have hmap : E.map (SmallEtale.inclusion B S hS ⋙ BigEtaleOver.forget B S hS) = V := by
    ext <;> rfl
  have hE : SmallEtale.IsCovering B S hS ⟨X, E⟩ := by
    show B.IsCovering ⟨X.obj.left, E.map
      (SmallEtale.inclusion B S hS ⋙ BigEtaleOver.forget B S hS)⟩
    rwa [hmap]
  refine ⟨E, hE, fun i ↦ ⟨?_, Vx (β i).down, ?_⟩⟩
  · show AlgebraicGeometry.IsAffine ((V.map B.inclusion).X i)
    exact IsAffine.of_isIso (e i).hom
  rw [nonempty_hom_opensToBoundedEtale_iff]
  rintro _ ⟨z, rfl⟩
  show pX (B.inclusion.map (V.f i) z) ∈ (Vx (β i).down : S.Opens)
  rw [← hfac i]
  refine hWV (β i).down ?_
  rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
  exact ⟨(e i).hom z, rfl⟩

/-- **Good charts are cover-dense.** -/
theorem goodChartInclusion_isCoverDense :
    (goodChartInclusion B S hS).IsCoverDense (SmallEtale.topology B S hS) := by
  refine ⟨fun X ↦ ?_⟩
  obtain ⟨E, hE, hgood⟩ := exists_isCovering_isGoodChart B S hS X
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS X := by
    rw [SmallEtale.mem_precoverage_iff]
    exact ⟨E, rfl, hE⟩
  have hgen : Sieve.generate E.presieve₀ ∈ SmallEtale.topology B S hS X := by
    show Sieve.generate E.presieve₀ ∈ (SmallEtale.precoverage B S hS).toGrothendieck X
    rw [Precoverage.mem_toGrothendieck_iff]
    exact Precoverage.Saturate.of X E.presieve₀ hpre
  refine (SmallEtale.topology B S hS).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro Y f ⟨i⟩
  exact ⟨⟨⟨E.X i, hgood i⟩, 𝟙 _, E.f i, by simp⟩⟩

end AlgebraicGeometry.SmallEtale

end
