module

public import Mathlib.Algebra.Homology.HomotopyFiber
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.QcohPresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal
public import StacksFrontier.CategoryTheory.Localization.RightFraction.Equality

/-!
# Derived-equal maps of bounded complexes of finite locally free modules

Let `X` be a quasi-compact and quasi-separated scheme with the resolution property and let
`ℰ^•`, `ℱ^•` be finite complexes of finite locally free `𝒪_X`-modules.  Two maps of complexes
`α^•, β^• : ℰ^• ⟶ ℱ^•` defining the same morphism of `D(𝒪_X)` then become homotopic after
precomposition with a quasi-isomorphism `γ^• : 𝒢^• ⟶ ℰ^•` whose source is again a bounded
complex of finite locally free `𝒪_X`-modules.

## Main results

* `exists_boundedFiniteLocallyFree_homotopy_of_hasResolutionProperty`: the statement above, for
  `X` quasi-compact and quasi-separated with the resolution property.
* `exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal`: the same statement for `X` with
  affine diagonal.
* the same statement when `X` admits an affine morphism to a Noetherian scheme with the
  resolution property:
`exists_boundedFiniteLocallyFree_homotopy_of_exists_isAffineHom_isNoetherian_hasResolutionProperty`
* `exists_boundedFiniteLocallyFree_homotopy`: the same statement with an additional hypothesis
  `hstage`, the converse of [Stacks, Tag 0F8B].

## References

* [Stacks Project, Tag 0F8H](https://stacks.math.columbia.edu/tag/0F8H)
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

/-- On a quasi-compact scheme with affine diagonal, two maps of bounded below complexes of
quasi-coherent modules that agree in `D(𝒪_X)` become homotopic after precomposition with a
quasi-isomorphism from a bounded below complex of quasi-coherent modules. -/
private theorem exists_quasicoherent_homotopy (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E F : CochainComplex X.Modules ℤ)
    (hEqc : ∀ i : ℤ, (E.X i).IsQuasicoherent) (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent)
    (hEplus : CochainComplex.plus X.Modules E) (hFplus : CochainComplex.plus X.Modules F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      CochainComplex.plus X.Modules G ∧ (∀ i : ℤ, (G.X i).IsQuasicoherent) ∧
        Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let A := P.FullSubcategory
  let I := P.ι
  have : PreservesFiniteLimits I := inferInstance
  have : PreservesFiniteColimits I := inferInstance
  have : I.Additive := I.additive_of_preserves_binary_products
  let E₀ : CochainComplex A ℤ := HomologicalComplex.liftObjectProperty P E hEqc
  let F₀ : CochainComplex A ℤ := HomologicalComplex.liftObjectProperty P F hFqc
  let M := I.mapHomologicalComplex (ComplexShape.up ℤ)
  let lift (f : E ⟶ F) : E₀ ⟶ F₀ :=
    { f i := ObjectProperty.homMk (f.f i)
      comm' i j _ := I.map_injective (f.comm i j) }
  have hinc : ∀ f : E ⟶ F, M.map (lift f) = f := fun f => by ext i; rfl
  let α₀ := lift α
  let β₀ := lift β
  have hαinc : M.map α₀ = α := hinc α
  have hβinc : M.map β₀ = β := hinc β
  let J := I.mapDerivedCategory
  have : J.Faithful := faithful_mapDerivedCategory_isQuasicoherent_ι X
  let eta := I.mapDerivedCategoryFactors
  have hqc : DerivedCategory.Q.map α₀ = DerivedCategory.Q.map β₀ := by
    refine J.map_injective ((cancel_mono (eta.hom.app F₀)).1 ?_)
    have hn : ∀ f : E₀ ⟶ F₀, J.map (DerivedCategory.Q.map f) ≫ eta.hom.app F₀ =
        eta.hom.app E₀ ≫ DerivedCategory.Q.map (M.map f) := fun f => by
      simpa only [Functor.comp_map] using eta.hom.naturality f
    rw [hn α₀, hn β₀, hαinc, hβinc]
    exact congrArg (eta.hom.app E₀ ≫ ·) h
  have hQh : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α₀) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map β₀) := by
    refine (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app F₀)).1 ?_
    rw [DerivedCategory.quotientCompQhIso_hom_naturality α₀,
      DerivedCategory.quotientCompQhIso_hom_naturality β₀, hqc]
  obtain ⟨Zbar, sbar, hsbar, hfac⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α₀)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map β₀)).1 hQh
  obtain ⟨Zc, rfl⟩ := HomotopyCategory.quotient_obj_surjective Zbar
  obtain ⟨γc, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective sbar
  have hγc : QuasiIso γc := (HomotopyCategory.quotient_map_mem_quasiIso_iff γc).1 hsbar
  have hhC : Homotopy (γc ≫ α₀) (γc ≫ β₀) :=
    HomotopyCategory.homotopyOfEq _ _ (by simpa only [Functor.map_comp] using hfac)
  obtain ⟨nE, hnE⟩ := (CochainComplex.plus_iff X.Modules E).mp hEplus
  obtain ⟨nF, hnF⟩ := (CochainComplex.plus_iff X.Modules F).mp hFplus
  obtain ⟨n, hnEn, hnFn⟩ : ∃ n : ℤ, n < nE ∧ n < nF :=
    ⟨min nE nF - 1, by omega, by omega⟩
  have : E₀.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact IsZero.of_full_of_faithful_of_isZero I (E₀.X i)
      (E.isZero_of_isStrictlyGE nE i (by omega))
  have : F₀.IsStrictlyGE nF := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact IsZero.of_full_of_faithful_of_isZero I (F₀.X i) (F.isZero_of_isStrictlyGE nF i hi)
  let Zt : CochainComplex A ℤ := CochainComplex.truncGE Zc n
  let δ : Zt ⟶ E₀ := CochainComplex.truncGEMap γc n ≫ inv (CochainComplex.πTruncGE E₀ n)
  have hTγ : QuasiIso (CochainComplex.truncGEMap γc n) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    intro i _
    exact (quasiIso_iff γc).1 hγc i
  have hδ : QuasiIso δ := inferInstanceAs
    (QuasiIso (CochainComplex.truncGEMap γc n ≫ inv (CochainComplex.πTruncGE E₀ n)))
  let path : CochainComplex A ℤ := F₀.pathObject
  have : path.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    refine HomologicalComplex.pathObject.isZero_X _ _
      (F₀.isZero_of_isStrictlyGE nF i (by omega)) fun j hj => ?_
    change j + 1 = i at hj
    exact F₀.isZero_of_isStrictlyGE nF j (by omega)
  let lifted : Zc ⟶ path := HomologicalComplex.pathObject.lift (γc ≫ α₀) (γc ≫ β₀) hhC
  let liftedTrunc : Zt ⟶ path :=
    CochainComplex.truncGEMap lifted n ≫ inv (CochainComplex.πTruncGE path n)
  have hπ : ∀ {C D : CochainComplex A ℤ} [D.IsStrictlyGE n] (f : C ⟶ D),
      CochainComplex.πTruncGE C n ≫
        (CochainComplex.truncGEMap f n ≫ inv (CochainComplex.πTruncGE D n)) = f := by
    intro C D _ f
    rw [← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hπlift : CochainComplex.πTruncGE Zc n ≫ liftedTrunc = lifted := hπ lifted
  have hπδ : CochainComplex.πTruncGE Zc n ≫ δ = γc := hπ γc
  have : Epi (CochainComplex.πTruncGE Zc n) :=
    HomologicalComplex.instEpiπTruncGE Zc (ComplexShape.embeddingUpIntGE n)
  have hlift : ∀ (p : path ⟶ F₀) (q : E₀ ⟶ F₀), lifted ≫ p = γc ≫ q → liftedTrunc ≫ p = δ ≫ q := by
    intro p q hpq
    refine (cancel_epi (CochainComplex.πTruncGE Zc n)).1 ?_
    rw [← Category.assoc, hπlift, ← Category.assoc, hπδ]
    exact hpq
  have hhom : Homotopy (δ ≫ α₀) (δ ≫ β₀) := by
    rw [← hlift _ _ (HomologicalComplex.pathObject.lift_π₀ _ _ _),
      ← hlift _ _ (HomologicalComplex.pathObject.lift_π₁ _ _ _)]
    exact (HomologicalComplex.pathObject.homotopy₀₁ F₀ fun i => ⟨i + 1, rfl⟩).compLeft liftedTrunc
  have hδ' : QuasiIso (M.map δ) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology δ I).2 hδ
  have hmap : Homotopy (M.map (δ ≫ α₀)) (M.map (δ ≫ β₀)) := I.mapHomotopy hhom
  rw [M.map_comp δ α₀, M.map_comp δ β₀, hαinc, hβinc] at hmap
  exact ⟨M.obj Zt, M.map δ, hδ', (CochainComplex.plus_iff X.Modules _).2
    ⟨n, (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi => I.map_isZero
      (Zt.isZero_of_isStrictlyGE n i hi)⟩, fun i => (Zt.X i).property, ⟨hmap⟩⟩

/-- On a quasi-compact and quasi-separated scheme with the resolution property and affine
diagonal, two maps of bounded complexes of finite locally free `𝒪_X`-modules defining the same
morphism of `D(𝒪_X)` become homotopic after a quasi-isomorphism from a bounded complex of finite
locally free modules. -/
theorem exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) := by
  obtain ⟨Z, δ, hδ, hZplus, hZqc, ⟨hhom⟩⟩ := exists_quasicoherent_homotopy X E F
    (isQuasicoherent_X_of_boundedFiniteLocallyFree X E hE)
    (isQuasicoherent_X_of_boundedFiniteLocallyFree X F hF) hE.1.1 hF.1.1 α β h
  have hδIso : IsIso (DerivedCategory.Q.map δ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules δ).2 hδ
  obtain ⟨G, γ, hG, hγ⟩ := exists_boundedFiniteLocallyFree_quasiIso X Z hZplus hZqc
    (isPerfect_of_iso (asIso (DerivedCategory.Q.map δ)).symm
      (isPerfect_of_boundedFiniteLocallyFree X E hE))
  exact ⟨G, γ ≫ δ, inferInstance, hG,
    ⟨by simpa only [Category.assoc] using hhom.compLeft γ⟩⟩

/-- Let `X` be a quasi-compact and quasi-separated scheme with the resolution property that
admits an affine morphism to a Noetherian scheme with the resolution property, and let `ℰ^•`,
`ℱ^•` be finite complexes of finite locally free `𝒪_X`-modules.  If two maps of complexes
`α^•, β^• : ℰ^• ⟶ ℱ^•` define the same morphism of `D(𝒪_X)`, then there is a
quasi-isomorphism `γ^• : 𝒢^• ⟶ ℰ^•` with `𝒢^•` a bounded complex of finite locally free
`𝒪_X`-modules such that `α^• ∘ γ^•` and `β^• ∘ γ^•` are homotopic maps of complexes. -/
theorem
  exists_boundedFiniteLocallyFree_homotopy_of_exists_isAffineHom_isNoetherian_hasResolutionProperty
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hmodel : ∃ (Y : Scheme.{u}) (f : X ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y)
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  have := isAffineHom_diagonal_of_exists_isAffineHom_isNoetherian_hasResolutionProperty X hmodel
  exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal X E F hE hF α β h

/-- Let `X` be a quasi-compact and quasi-separated scheme with the resolution property and let
`ℰ^•`, `ℱ^•` be finite complexes of finite locally free `𝒪_X`-modules.  If two maps of complexes
`α^•, β^• : ℰ^• ⟶ ℱ^•` define the same morphism of `D(𝒪_X)`, then there is a
quasi-isomorphism `γ^• : 𝒢^• ⟶ ℰ^•` with `𝒢^•` a bounded complex of finite locally free
`𝒪_X`-modules such that `α^• ∘ γ^•` and `β^• ∘ γ^•` are homotopic. -/
@[stacks 0F8H]
theorem exists_boundedFiniteLocallyFree_homotopy_of_hasResolutionProperty (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  have := HasResolutionProperty.isAffineHom_diagonal X
  exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal X E F hE hF α β h

/-- Let `X` be a quasi-compact and quasi-separated scheme with the resolution property and let
`ℰ^•`, `ℱ^•` be finite complexes of finite locally free `𝒪_X`-modules, and assume `hstage`, the
converse of [Stacks, Tag 0F8B].  If two maps of complexes `α^•, β^• : ℰ^• ⟶ ℱ^•` define the
same morphism of `D(𝒪_X)`, then there is a quasi-isomorphism `γ^• : 𝒢^• ⟶ ℰ^•` with `𝒢^•` a
bounded complex of finite locally free `𝒪_X`-modules such that `α^• ∘ γ^•` and `β^• ∘ γ^•` are
homotopic. -/
theorem exists_boundedFiniteLocallyFree_homotopy (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    (hstage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
      (∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g)) →
      (∀ i, CompactSpace (D.obj i)) → (∀ i, QuasiSeparatedSpace (D.obj i)) →
      HasResolutionProperty c.pt → ∃ i, HasResolutionProperty (D.obj i))
    (E F : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E) (hF : boundedFiniteLocallyFreeComplex X F)
    (α β : E ⟶ F) (h : DerivedCategory.Q.map α = DerivedCategory.Q.map β) :
    ∃ (G : CochainComplex X.Modules ℤ) (γ : G ⟶ E) (_ : QuasiIso γ),
      boundedFiniteLocallyFreeComplex X G ∧ Nonempty (Homotopy (γ ≫ α) (γ ≫ β)) :=
  have := isAffineHom_diagonal_of_hasResolutionProperty X hstage
  exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal X E F hE hF α β h

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
