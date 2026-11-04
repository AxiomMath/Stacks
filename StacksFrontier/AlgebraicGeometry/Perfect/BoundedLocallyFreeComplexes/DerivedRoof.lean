module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.QcohPresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal

/-!
# Derived morphisms between bounded complexes of finite locally free modules

Let `X` be a quasi-compact and quasi-separated scheme with the resolution property and let
`ℰ^•`, `ℱ^•` be finite complexes of finite locally free `𝒪_X`-modules.  Every morphism
`α : ℰ^• ⟶ ℱ^•` of `D(𝒪_X)` is then represented by a diagram `ℰ^• ← 𝒢^• → ℱ^•` in which `𝒢^•`
is again a bounded complex of finite locally free `𝒪_X`-modules and `𝒢^• → ℰ^•` is a
quasi-isomorphism.  This is [Stacks, Tag 0F8G].

## Main results

* `exists_boundedFiniteLocallyFree_roof_of_hasResolutionProperty`, in the namespace
  `Stacks.Perfect.BoundedLocallyFreeComplexes`, is [Stacks, Tag 0F8G];
  `exists_boundedFiniteLocallyFree_roof` is the same statement with an additional assumption
  `hstage` that it does not use; the variant
  `exists_boundedFiniteLocallyFree_roof_of_affineDiagonal` in the same namespace is the statement
  for a scheme that is moreover assumed to have affine diagonal.

The classes of schemes on which that affine diagonal is itself discharged, so that the roof is
available with nothing assumed beyond the scheme — separated, Noetherian, carrying an ample
invertible module, affine, and `ℙⁿ` over an affine base — are in
`StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/DerivedRoofUnconditional.lean`,
together with two instances of the conclusion in which every binder is filled in.

## Implementation notes

The proof is the source's.  On a scheme with affine diagonal the derived inclusion
`D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` is full by [Stacks, Tag 08DB], so `α` comes from a morphism of
`D(QCoh(𝒪_X))` between the two complexes read in the quasi-coherent modules; the calculus of
fractions there writes that morphism as a diagram of bounded complexes of quasi-coherent
modules, and the finite locally free replacement of [Stacks, Tag 0F8E] applied to the middle
term finishes the argument.

Affineness of the diagonal is supplied by [Stacks, Tag 0F8C],
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`: `X` is affine over a Noetherian
scheme with the resolution property, through the converse of [Stacks, Tag 0F8B] at Noetherian
stages (`AlgebraicGeometry.hasResolutionProperty_stage`).

The derived morphism is said to be represented by the diagram in the form
`inv (Q p) ≫ Q q = α`, which is an equality of morphisms of `D(𝒪_X)` and pins the diagram to
`α` rather than merely asserting that some diagram exists.

## References

* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F8E](https://stacks.math.columbia.edu/tag/0F8E)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- Transport of a diagram presentation of a morphism along isomorphisms identifying the image
of a diagram under a functor with a second diagram. -/
private lemma inv_comp_eq_of_natural_isos {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {A B H : C} {A' B' H' : D} (eA : J.obj A ≅ A') (eB : J.obj B ≅ B') (eH : J.obj H ≅ H')
    (p : H ⟶ A) (q : H ⟶ B) (p' : H' ⟶ A') [hp' : IsIso p'] (q' : H' ⟶ B') (β : A ⟶ B) (α : A' ⟶ B')
    (hp : J.map p ≫ eA.hom = eH.hom ≫ p') (hq : J.map q ≫ eB.hom = eH.hom ≫ q')
    (hβ : J.map β = eA.hom ≫ α ≫ eB.inv) (hfac : p ≫ β = q) :
    inv p' ≫ q' = α := by
  have h : p' ≫ α = q' := by
    refine (cancel_epi eH.hom).1 ?_
    calc
      eH.hom ≫ p' ≫ α = J.map p ≫ eA.hom ≫ α := by
        rw [← Category.assoc, ← hp, Category.assoc]
      _ = J.map p ≫ J.map β ≫ eB.hom := by
        rw [hβ]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = eH.hom ≫ q' := by rw [← Category.assoc, ← J.map_comp, hfac, hq]
  rw [← h]
  simp

/-- **A derived morphism between complexes of quasi-coherent modules is represented by a diagram
of complexes of quasi-coherent modules.**  On a quasi-compact scheme with affine diagonal the
derived inclusion of the quasi-coherent modules is full, so the morphism comes from
`D(QCoh(𝒪_X))`, where the calculus of fractions produces the diagram; boundedness of the source
and boundedness below of the target bound the middle term. -/
private theorem exists_quasicoherent_roof (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E F : CochainComplex X.Modules ℤ)
    (hEqc : ∀ i : ℤ, (E.X i).IsQuasicoherent) (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent)
    (hEplus : CochainComplex.plus X.Modules E) (hEminus : CochainComplex.minus X.Modules E)
    (hFplus : CochainComplex.plus X.Modules F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (H : CochainComplex X.Modules ℤ) (p : H ⟶ E) (_ : QuasiIso p) (q : H ⟶ F),
      (CochainComplex.plus X.Modules H ∧ CochainComplex.minus X.Modules H) ∧
        (∀ i : ℤ, (H.X i).IsQuasicoherent) ∧
          inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let I := P.ι
  have : PreservesFiniteLimits I := inferInstance
  have : PreservesFiniteColimits I := inferInstance
  have : I.Additive := I.additive_of_preserves_binary_products
  let E₀ : CochainComplex P.FullSubcategory ℤ := HomologicalComplex.liftObjectProperty P E hEqc
  let F₀ : CochainComplex P.FullSubcategory ℤ := HomologicalComplex.liftObjectProperty P F hFqc
  let J := I.mapDerivedCategory
  have : J.Full := full_mapDerivedCategory_isQuasicoherent_ι X
  let eta := I.mapDerivedCategoryFactors
  let α₀ : DerivedCategory.Q.obj E₀ ⟶ DerivedCategory.Q.obj F₀ :=
    J.preimage (eta.hom.app E₀ ≫ α ≫ eta.inv.app F₀)
  have hα₀ : J.map α₀ = eta.hom.app E₀ ≫ α ≫ eta.inv.app F₀ := J.map_preimage _
  obtain ⟨aE, haE⟩ := (CochainComplex.plus_iff X.Modules E).mp hEplus
  obtain ⟨aF, haF⟩ := (CochainComplex.plus_iff X.Modules F).mp hFplus
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff E).mp hEminus
  let M := I.mapHomologicalComplex (ComplexShape.up ℤ)
  have hGE := fun (K₀ : CochainComplex P.FullSubcategory ℤ) n =>
    CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff K₀ I n
  have hLE := fun (K₀ : CochainComplex P.FullSubcategory ℤ) n =>
    CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K₀ I n
  have : E₀.IsStrictlyGE (min aE aF) := (hGE E₀ _).1 (E.isStrictlyGE_of_ge _ aE (min_le_left _ _))
  have : F₀.IsStrictlyGE (min aE aF) := (hGE F₀ _).1 (F.isStrictlyGE_of_ge _ aF (min_le_right _ _))
  have : E₀.IsStrictlyLE b := (hLE E₀ b).1 ‹_›
  obtain ⟨H₀, hH₀GE, hH₀LE, p₀, hp₀, q₀, hfrac⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE (min aE aF) b α₀
  let H : CochainComplex X.Modules ℤ := M.obj H₀
  let p : H ⟶ E := M.map p₀
  let q : H ⟶ F := M.map q₀
  have hp : QuasiIso p :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology p₀ I).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso P.FullSubcategory p₀).1 hp₀)
  have hpIso : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules p).2 hp
  refine ⟨H, p, hp, q, ⟨(CochainComplex.plus_iff X.Modules H).2 ⟨min aE aF,
      (hGE H₀ _).2 hH₀GE⟩,
    (CochainComplex.minus_iff H).2 ⟨b, (hLE H₀ b).2 hH₀LE⟩⟩,
    fun i => (H₀.X i).property, ?_⟩
  refine inv_comp_eq_of_natural_isos (hp' := hpIso) J (eta.app E₀) (eta.app F₀) (eta.app H₀)
    (DerivedCategory.Q.map p₀) (DerivedCategory.Q.map q₀) (DerivedCategory.Q.map p)
    (DerivedCategory.Q.map q) α₀ α (eta.hom.naturality p₀) (eta.hom.naturality q₀) hα₀ ?_
  rw [hfrac]
  simp

/-- **[Stacks, Tag 0F8G] for a scheme with affine diagonal.**  On a quasi-compact and
quasi-separated scheme with the resolution property and affine diagonal, a morphism of `D(𝒪_X)`
between bounded complexes of finite locally free `𝒪_X`-modules is represented by a diagram
`ℰ^• ← 𝒢^• → ℱ^•` with `𝒢^•` again a bounded complex of finite locally free modules and
`𝒢^• → ℰ^•` a quasi-isomorphism. -/
theorem exists_boundedFiniteLocallyFree_roof_of_affineDiagonal (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α := by
  obtain ⟨H, p, hp, q, hHbound, hHqc, hroof⟩ := exists_quasicoherent_roof X E F
    (isQuasicoherent_X_of_boundedFiniteLocallyFree X E hE)
    (isQuasicoherent_X_of_boundedFiniteLocallyFree X F hF) hE.1.1 hE.1.2 hF.1.1 α
  have hpIso : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules p).2 hp
  obtain ⟨G, r, hG, hr⟩ := exists_boundedFiniteLocallyFree_quasiIso X H hHbound.1 hHqc
    (isPerfect_of_iso (asIso (DerivedCategory.Q.map p)).symm
      (isPerfect_of_boundedFiniteLocallyFree X E hE))
  have hrIso : IsIso (DerivedCategory.Q.map r) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules r).2 hr
  refine ⟨G, r ≫ p, inferInstance, r ≫ q, hG, ?_⟩
  simpa only [Functor.map_comp, IsIso.inv_comp, Category.assoc, IsIso.inv_hom_id_assoc] using hroof

/-- **[Stacks, Tag 0F8G].**  Let `X` be a quasi-compact and quasi-separated scheme with the
resolution property and let `ℰ^•`, `ℱ^•` be finite complexes of finite locally free
`𝒪_X`-modules.  Every morphism `α : ℰ^• ⟶ ℱ^•` of `D(𝒪_X)` is represented by a diagram
`ℰ^• ← 𝒢^• → ℱ^•` with `𝒢^•` a bounded complex of finite locally free `𝒪_X`-modules and
`𝒢^• → ℰ^•` a quasi-isomorphism.

The assumptions on `X` are exactly the source's.  The affine diagonal used in the proof comes
from [Stacks, Tag 0F8C], `AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`. -/
@[stacks 0F8G]
theorem exists_boundedFiniteLocallyFree_roof_of_hasResolutionProperty (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α :=
  have := HasResolutionProperty.isAffineHom_diagonal X
  exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X E F hE hF α

/-- **[Stacks, Tag 0F8G], with an additional assumption `hstage`.**  Let
`X` be a quasi-compact and quasi-separated scheme with the resolution property and let `ℰ^•`,
`ℱ^•` be finite complexes of finite locally free `𝒪_X`-modules.  Every morphism
`α : ℰ^• ⟶ ℱ^•` of `D(𝒪_X)` is represented by a diagram `ℰ^• ← 𝒢^• → ℱ^•` with `𝒢^•` a
bounded complex of finite locally free `𝒪_X`-modules and `𝒢^• → ℰ^•` a quasi-isomorphism.  The
assumption `hstage`, the converse of [Stacks, Tag 0F8B], is not needed:
`exists_boundedFiniteLocallyFree_roof_of_hasResolutionProperty`
states the conclusion without it. -/
theorem exists_boundedFiniteLocallyFree_roof (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hstage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
      (∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g)) →
      (∀ i, CompactSpace (D.obj i)) → (∀ i, QuasiSeparatedSpace (D.obj i)) →
      HasResolutionProperty c.pt → ∃ i, HasResolutionProperty (D.obj i))
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
      boundedFiniteLocallyFreeComplex X G ∧
        inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α :=
  have := isAffineHom_diagonal_of_hasResolutionProperty X hstage
  exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X E F hE hF α

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
