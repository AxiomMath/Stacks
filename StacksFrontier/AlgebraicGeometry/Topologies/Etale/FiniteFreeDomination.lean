module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteFreeDominationAffine
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Finite locally free morphisms locally dominate étale coverings

This file proves [Stacks, Tag 02LI]: an étale covering `{U_i → S}` is refined by a family
built in two Zariski steps out of surjective finite locally free morphisms. There is a Zariski
open covering `S = ⋃ V_j`, for each `j` a surjective finite locally free `W_j → V_j`, and for
each `j` a Zariski open covering `W_j = ⋃_k W_{j,k}`, such that every `W_{j,k} → S` factors
through one of the `U_i → S`.

The proof is local on `S`: around each point one shrinks the étale covering to a *surjective*
étale morphism of affine schemes and applies [Stacks, Tag 02LH].

## Main results

* `Stacks.Topologies.Etale.exists_zariski_finiteLocallyFree_refinement` is [Stacks, Tag 02LI].

## Implementation notes

Covering families and their refinements are represented by
`CategoryTheory.PreZeroHypercover` and its morphisms; the two Zariski coverings are
`AlgebraicGeometry.Scheme.OpenCover`s, and the composite family is Mathlib's
`CategoryTheory.PreZeroHypercover.bind` of the inner coverings pushed forward along the finite
locally free morphisms. The refining morphism records, for every member of the composite
family, a member of the original étale covering through which it factors.

The local data produced around a point is bundled into the structure
`Stacks.Topologies.Etale.LocalRefinementAt`, and is chosen at each point of `S` by a single
`Classical.choice`.

## References

* [Stacks Project, Tag 02LI](https://stacks.math.columbia.edu/tag/02LI)
* [Stacks Project, Tag 02LH](https://stacks.math.columbia.edu/tag/02LH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Topologies.Etale

/-- Around any point in the image of an étale morphism `f : X ⟶ S` there is an affine open
`V ⊆ S` and a *surjective* étale morphism `U ⟶ V` of affine schemes factoring through `f`. -/
private lemma exists_affine_etale_neighborhood
    {S X : Scheme.{u}} {s : S} (f : X ⟶ S) [Etale f] (x : X) (hx : f x = s) :
    ∃ (V : S.affineOpens) (_ : s ∈ V.1)
      (U : Scheme.{u}) (_ : IsAffine U) (q : U ⟶ V.1.toScheme)
      (_ : Etale q) (_ : Surjective q) (g : U ⟶ X),
        g ≫ f = q ≫ V.1.ι := by
  classical
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hs₀, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let V₀ : S.affineOpens := ⟨V₀, hV₀⟩
  let P : X.Opens := f ⁻¹ᵁ V₀.1
  have hxP : x ∈ P := by
    show f x ∈ V₀.1
    rwa [hx]
  let xP : P.toScheme := ⟨x, hxP⟩
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
    P.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ xP) isOpen_univ
  let U₀ : P.toScheme.affineOpens := ⟨U₀, hU₀⟩
  let f₀ := f.resLE V₀.1 P le_rfl
  let f₁ : U₀.1.toScheme ⟶ V₀.1.toScheme := U₀.1.ι ≫ f₀
  let b₀ : V₀.1.toScheme := ⟨s, hs₀⟩
  let a₀ : U₀.1.toScheme := ⟨xP, hxU₀⟩
  have : IsAffine U₀.1.toScheme := U₀.2
  have : IsAffine V₀.1.toScheme := V₀.2
  have hf₁a₀ : f₁ a₀ = b₀ := by
    apply Subtype.ext
    show (f₀ xP).1 = s
    rwa [Scheme.Hom.coe_resLE_apply]
  have hopen : IsOpen (Set.range f₁) := by
    simpa only [Set.image_univ] using Scheme.Hom.isOpenMap f₁ _ isOpen_univ
  have hb₀ : b₀ ∈ Set.range f₁ := ⟨a₀, hf₁a₀⟩
  let O : V₀.1.toScheme.Opens := ⟨Set.range f₁, hopen⟩
  obtain ⟨r, hrO, hrb₀⟩ := (isAffineOpen_top V₀.1.toScheme).exists_basicOpen_le
    (V := O) ⟨b₀, hb₀⟩ (by trivial)
  let B₁ : V₀.1.toScheme.Opens := V₀.1.toScheme.basicOpen r
  let U₁ : U₀.1.toScheme.Opens := U₀.1.toScheme.basicOpen (f₁.appTop r)
  have hpre : f₁ ⁻¹ᵁ B₁ = U₁ := Scheme.Hom.preimage_basicOpen_top f₁ r
  have hB₁ : IsAffineOpen B₁ := (isAffineOpen_top V₀.1.toScheme).basicOpen r
  let V : S.affineOpens := ⟨V₀.1.ι ''ᵁ B₁, hB₁.image_of_isOpenImmersion V₀.1.ι⟩
  have hs : s ∈ V.1 := ⟨b₀, (by simpa using hrb₀), rfl⟩
  let inc : B₁.toScheme ⟶ S := B₁.ι ≫ V₀.1.ι
  let e : B₁.toScheme ≅ V.1.toScheme :=
    IsOpenImmersion.isoOfRangeEq inc V.1.ι (by simp [inc, V, Set.range_comp])
  let f₂ : U₁.toScheme ⟶ B₁.toScheme := f₁.resLE B₁ U₁ (by rw [hpre])
  have hf₂ : Surjective f₂ := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨a, ha⟩ : (z.1 : V₀.1.toScheme) ∈ Set.range f₁ := hrO z.2
    have haU : a ∈ U₁ := by
      rw [← hpre]
      show f₁ a ∈ B₁
      simpa [ha] using z.2
    refine ⟨⟨a, haU⟩, Subtype.ext ?_⟩
    simpa [f₂, Scheme.Hom.coe_resLE_apply] using ha
  have hfactor : (U₁.ι ≫ U₀.1.ι ≫ P.ι) ≫ f = (f₂ ≫ e.hom) ≫ V.1.ι := by
    have hleft : (U₁.ι ≫ U₀.1.ι ≫ P.ι) ≫ f = U₁.ι ≫ f₁ ≫ V₀.1.ι := by
      simp [f₁, f₀, Scheme.Hom.resLE_comp_ι, Category.assoc]
    have hrestrict : f₂ ≫ B₁.ι = U₁.ι ≫ f₁ := by simp [f₂, Scheme.Hom.resLE_comp_ι]
    have hefac : e.hom ≫ V.1.ι = B₁.ι ≫ V₀.1.ι :=
      IsOpenImmersion.isoOfRangeEq_hom_fac inc V.1.ι (by simp [inc, V, Set.range_comp])
    calc
      (U₁.ι ≫ U₀.1.ι ≫ P.ι) ≫ f = U₁.ι ≫ f₁ ≫ V₀.1.ι := hleft
      _ = f₂ ≫ e.hom ≫ V.1.ι := by
        rw [← Category.assoc, ← hrestrict, Category.assoc, ← hefac]
      _ = (f₂ ≫ e.hom) ≫ V.1.ι := by rw [Category.assoc]
  exact ⟨V, hs, U₁.toScheme, (by dsimp only [U₁]; infer_instance), f₂ ≫ e.hom,
    inferInstance, inferInstance, U₁.ι ≫ U₀.1.ι ≫ P.ι, hfactor⟩

/-- The local data produced around a point `s` of `S` by [Stacks, Tag 02LH]: an affine open
neighbourhood `V` of `s`, a surjective finite locally free `W ⟶ V`, an open covering of `W`,
and a member `i` of the given family through which every piece of that covering factors. -/
private structure LocalRefinementAt {S : Scheme.{u}} (E : PreZeroHypercover.{w} S) (s : S) where
  /-- An affine open neighbourhood of `s` in `S`. -/
  V : S.affineOpens
  /-- The neighbourhood contains `s`. -/
  contains : s ∈ V.1
  /-- A scheme finite locally free over `V`. -/
  W : Scheme.{u}
  /-- The finite locally free morphism to `V`. -/
  p : W ⟶ V.1.toScheme
  /-- `p` is finite locally free. -/
  finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFree p
  /-- `p` is surjective. -/
  surjective : Surjective p
  /-- A Zariski open covering of `W`. -/
  U : W.OpenCover.{u}
  /-- The index of a member of `E` through which the covering factors. -/
  i : E.I₀
  /-- The factorizations through that member. -/
  lift : ∀ k, U.X k ⟶ E.X i
  /-- The factorizations commute with the structure morphisms. -/
  comm : ∀ k, U.f k ≫ p ≫ V.1.ι = lift k ≫ E.f i

private lemma localRefinementAt_nonempty {S : Scheme.{u}} (E : PreZeroHypercover.{w} S)
    (hE : E.presieve₀ ∈ Scheme.etalePrecoverage S) (s : S) :
    Nonempty (LocalRefinementAt E s) := by
  classical
  have hdata := (Scheme.presieve₀_mem_precoverage_iff E).mp hE
  obtain ⟨i, x, hx⟩ := hdata.1 s
  have : Etale (E.f i) := hdata.2 i
  obtain ⟨V, hs, U, hU, q, hq, hqsurj, g, hfactor⟩ :=
    exists_affine_etale_neighborhood (E.f i) x hx
  have : IsAffine V.1.toScheme := V.2
  obtain ⟨T, p, hflf, hpsurj, 𝒯, -, g', hlift⟩ :=
    exists_isFiniteLocallyFree_surjective_finite_openCover_lift q
  exact ⟨⟨V, hs, T, p, hflf, hpsurj, 𝒯, i, fun k ↦ g' k ≫ g, fun k ↦ by
    simpa only [Category.assoc, hfactor] using congrArg (fun h ↦ h ≫ V.1.ι) (hlift k)⟩⟩

private noncomputable def localRefinementAt {S : Scheme.{u}} (E : PreZeroHypercover.{w} S)
    (hE : E.presieve₀ ∈ Scheme.etalePrecoverage S) (s : S) : LocalRefinementAt E s :=
  Classical.choice (localRefinementAt_nonempty E hE s)

/-- An étale covering is refined, after a Zariski covering of the base, by Zariski coverings of
schemes which are finite locally free and surjective over the corresponding members of the base
covering. -/
@[stacks 02LI]
theorem exists_zariski_finiteLocallyFree_refinement {S : Scheme.{u}}
    (E : PreZeroHypercover.{w} S) (hE : E.presieve₀ ∈ Scheme.etalePrecoverage S) :
    ∃ (V : S.OpenCover.{u}) (W : V.I₀ → Scheme.{u}) (p : ∀ j, W j ⟶ V.X j),
      (∀ j, Stacks.Morphisms.IsFiniteLocallyFree (p j)) ∧
        (∀ j, Surjective (p j)) ∧
          ∃ U : ∀ j, (W j).OpenCover.{u},
            Nonempty
              ((V.toPreZeroHypercover.bind fun j ↦
                (U j).toPreZeroHypercover.pushforward (p j)).Hom E) := by
  classical
  let D := localRefinementAt E hE
  let V : S.OpenCover.{u} :=
    { I₀ := S
      X := fun s ↦ (D s).V.1.toScheme
      f := fun s ↦ (D s).V.1.ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun s ↦ ⟨s, ⟨s, (D s).contains⟩, rfl⟩, fun s ↦ inferInstance⟩ }
  refine ⟨V, fun j ↦ (D j).W, fun j ↦ (D j).p, fun j ↦ (D j).finiteLocallyFree,
    fun j ↦ (D j).surjective, fun j ↦ (D j).U,
    ⟨{ s₀ := fun k ↦ (D k.1).i
       h₀ := fun k ↦ (D k.1).lift k.2
       w₀ := fun k ↦ ?_ }⟩⟩
  show (D k.1).lift k.2 ≫ E.f (D k.1).i = ((D k.1).U.f k.2 ≫ (D k.1).p) ≫ V.f k.1
  simpa [Category.assoc] using ((D k.1).comm k.2).symm

end Stacks.Topologies.Etale

end
