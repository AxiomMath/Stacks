module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionQuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RationalGaloisQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Radicial
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocalRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.FieldTheory.AlgClosedFiniteExtension
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The base change of the Galois quotient of `Spec ℚ̄` to `ℚ̄`

Let `X = Spec ℚ̄ / Gal(ℚ̄/ℚ)` be the algebraic space of Stacks 0483, with its universally
injective structure morphism `X ⟶ Spec ℚ`. Remark 049E asserts that its base change
`X_ℚ̄ = X ×_{Spec ℚ} Spec ℚ̄ ⟶ Spec ℚ̄` is weakly radicial but not radicial. Both halves are
proved here.

## Main definitions

* `AlgebraicGeometry.RationalGaloisQuotient.galoisQuotientBaseChange` is `X_ℚ̄`, and
  `AlgebraicGeometry.RationalGaloisQuotient.galoisQuotientBaseChangeToCover` is its projection
  to `Spec ℚ̄`.

## Main results

* `AlgebraicGeometry.RationalGaloisQuotient.isAlgebraicSpace_galoisQuotient`: the quotient `X`
  is an algebraic space, by Stacks 02Z2; hence so is `X_ℚ̄`
  (`AlgebraicGeometry.RationalGaloisQuotient.isAlgebraicSpace_galoisQuotientBaseChange`).
* `AlgebraicGeometry.RationalGaloisQuotient.isWeaklyRadicial_galoisQuotientBaseChangeToCover`:
  **Stacks 049E**, `X_ℚ̄ ⟶ Spec ℚ̄` is weakly radicial.
* `AlgebraicGeometry.RationalGaloisQuotient.not_isRadicial_galoisQuotientBaseChangeToCover`:
  **Stacks 049E**, `X_ℚ̄ ⟶ Spec ℚ̄` is not radicial.
* `AlgebraicGeometry.RationalGaloisQuotient.infinite_galoisGroup`: the absolute Galois group of
  `ℚ` is infinite.
* `AlgebraicGeometry.RationalGaloisQuotient.isReduced_algebraicClosure_tensorProduct_rat`:
  `ℚ̄ ⊗_ℚ ℚ̄` is reduced.

## Implementation notes

Weak radiciality is witnessed fibrewise by sections: over a field-valued point
`Spec(K) ⟶ Spec ℚ̄` the fibre `Spec(K) ×_ℚ X` receives the section through the projection of
`Spec ℚ̄` onto `X`, a section is a monomorphism, and the extension it exhibits is `K ⊂ K`.

The failure of radiciality is detected on the reduced test scheme `Spec(ℚ̄ ⊗_ℚ ℚ̄)`. Over the
identity point of `Spec ℚ̄` the fibre of `X_ℚ̄ ⟶ Spec ℚ̄` is `X_ℚ̄` itself, and radiciality would
identify its reduction with `Spec ℚ̄`; morphisms from a reduced scheme into the fibre factor
through the reduction, so the two projections `Spec(ℚ̄ ⊗_ℚ ℚ̄) ⟶ Spec ℚ̄` would have the same
image in `X`. Since the graph `∐_{g} Spec ℚ̄` of the Galois action is the kernel pair of the
projection onto `X` (`AlgebraicGeometry.Space.isPullback_toQuotientSheaf_bigFppf`), they would
then be related by a morphism `Spec(ℚ̄ ⊗_ℚ ℚ̄) ⟶ ∐_{g} Spec ℚ̄`. Such a morphism meets only
finitely many summands, `Spec(ℚ̄ ⊗_ℚ ℚ̄)` being quasi-compact, while the graph of every Galois
element `σ` is a point of `Spec(ℚ̄ ⊗_ℚ ℚ̄)` at which only the summand of `σ⁻¹` can relate the two
projections. So the Galois group would be finite, and it is not.

The source says no more than "weakly radicial, but not radicial"; the argument above is the
standard one that `X_ℚ̄` is not a scheme near its unique point.

## References

* [Stacks Project, Tag 0483](https://stacks.math.columbia.edu/tag/0483)
* [Stacks Project, Tag 049E](https://stacks.math.columbia.edu/tag/049E)
* [Stacks Project, Tag 02Z6](https://stacks.math.columbia.edu/tag/02Z6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.RationalGaloisQuotient

variable (B : BigFppfSite.{0}) (hS : B.Contains base) (hU : B.Contains cover.left)

/-- The object `Spec ℚ` of the big fppf site over itself, a terminal object. -/
abbrev siteBase : BigFppfOver B base hS := Over.mk (𝟙 (B.obj hS))

/-- Any two morphisms of presheaves into the presheaf represented by `Spec ℚ` agree: it is
represented by a terminal object. -/
theorem hom_ext_yoneda_siteBase {F : (BigFppfOver B base hS)ᵒᵖ ⥤ Type}
    (a b : F ⟶ yoneda.obj (siteBase B hS)) : a = b := by
  ext T x
  exact (Over.mkIdTerminal : IsTerminal (siteBase B hS)).hom_ext _ _

/-- The structure morphism `Spec ℚ̄ ⟶ Spec ℚ`, on represented presheaves. -/
def coverToBase : yoneda.obj (siteCover B hS hU) ⟶ yoneda.obj (siteBase B hS) :=
  yoneda.map (Over.homMk (siteCover B hS hU).hom)


/-! ### The absolute Galois group of `ℚ` is infinite -/

/-- `ℚ̄` is Galois over `ℚ`. -/
theorem isGalois_algebraicClosure_rat : IsGalois ℚ (AlgebraicClosure ℚ) := by
  have : Normal ℚ (AlgebraicClosure ℚ) :=
    { toIsAlgebraic := AlgebraicClosure.isAlgebraic ℚ
      splits' := fun x ↦ (AlgebraicClosure.isAlgClosed ℚ).splits
        ((minpoly ℚ x).map (algebraMap ℚ (AlgebraicClosure ℚ))) }
  exact isGalois_iff.mpr ⟨inferInstance, this⟩

/-- `ℚ̄` is not finite-dimensional over `ℚ`: a primitive fifth root of unity has degree four
over `ℚ`, while a finite algebraically closed extension of `ℚ` has degree at most two. -/
theorem not_finiteDimensional_algebraicClosure_rat :
    ¬ FiniteDimensional ℚ (AlgebraicClosure ℚ) := by
  intro hfin
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root
    ((Polynomial.cyclotomic 5 ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)))
    (by
      rw [Polynomial.degree_map]
      exact (Polynomial.degree_cyclotomic_pos 5 ℚ (by norm_num)).ne')
  have hroot : Polynomial.aeval μ (Polynomial.cyclotomic 5 ℚ) = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hμ
  have hmin : minpoly ℚ μ = Polynomial.cyclotomic 5 ℚ :=
    (minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat (by norm_num))
      hroot (Polynomial.cyclotomic.monic 5 ℚ)).symm
  have hdeg : (minpoly ℚ μ).natDegree ≤ Module.finrank ℚ (AlgebraicClosure ℚ) :=
    minpoly.natDegree_le μ
  rw [hmin, Polynomial.natDegree_cyclotomic, Nat.totient_prime (by norm_num)] at hdeg
  rcases IsAlgClosed.finrank_eq_one_or_two ℚ (AlgebraicClosure ℚ) with h | h <;> omega

/-- The absolute Galois group of `ℚ` is infinite: by Artin's theorem a finite group of
automorphisms of `ℚ̄` would make `ℚ̄` finite over its fixed field, which is `ℚ` because `ℚ̄`
is Galois over `ℚ`. -/
theorem infinite_galoisGroup : Infinite galoisGroup := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have := isGalois_algebraicClosure_rat
  let K₀ := FixedPoints.subfield galoisGroup (AlgebraicClosure ℚ)
  have hsurj : Function.Surjective (algebraMap ℚ K₀) := by
    intro x
    obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (x : AlgebraicClosure ℚ)).2
      (fun f ↦ x.2 f)
    exact ⟨q, Subtype.ext (by simpa using hq)⟩
  have : Module.Finite ℚ K₀ :=
    Module.Finite.of_surjective (Algebra.linearMap ℚ K₀) hsurj
  have : IsScalarTower ℚ K₀ (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun _ ↦ by simp
  exact not_finiteDimensional_algebraicClosure_rat (Module.Finite.trans K₀ _)


/-! ### `ℚ̄ ⊗_ℚ ℚ̄` is reduced -/

/-- `ℚ̄ ⊗_ℚ ℚ̄` is reduced. It suffices to check `ℚ̄ ⊗_ℚ B` for a finitely generated subalgebra
`B` of `ℚ̄`, which is a finite separable field extension of `ℚ`, hence unramified; so is its
base change to `ℚ̄`, a finite algebra over a field, which is therefore reduced. -/
theorem isReduced_algebraicClosure_tensorProduct_rat :
    _root_.IsReduced (AlgebraicClosure ℚ ⊗[ℚ] AlgebraicClosure ℚ) := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    B.toIntermediateField' (Subalgebra.isField_of_algebraic B)
  let e : B ≃ₐ[ℚ] E.toSubalgebra := Subalgebra.equivOfEq B E.toSubalgebra (by simp [E])
  have : Algebra.FiniteType ℚ E :=
    Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType B).mp hB) e
  have : Algebra.IsAlgebraic ℚ E := IntermediateField.isAlgebraic_tower_bot
  have : Algebra.IsSeparable ℚ E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  have : _root_.IsReduced (AlgebraicClosure ℚ ⊗[ℚ] E) :=
    Algebra.FormallyUnramified.isReduced_of_field (AlgebraicClosure ℚ) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.congr AlgEquiv.refl e : _ ≃ₐ[ℚ] AlgebraicClosure ℚ ⊗[ℚ] E).toRingHom
    (AlgEquiv.injective _)


/-! ### The two projections of `Spec ℚ̄ ×_ℚ Spec ℚ̄` are not related by the Galois action

Every Galois element `σ` relates the two projections at the point of `Spec(ℚ̄ ⊗_ℚ ℚ̄)` given by
the graph of `σ`, and only the element `σ` does so there. A morphism from the quasi-compact
scheme `Spec(ℚ̄ ⊗_ℚ ℚ̄)` to `∐_{g} Spec ℚ̄` meets only finitely many summands, so it cannot
relate the two projections everywhere: the absolute Galois group of `ℚ` is infinite. -/

/-- The underlying scheme of `Spec ℚ̄ ×_ℚ Spec ℚ̄` is `Spec(ℚ̄ ⊗_ℚ ℚ̄)`. -/
def galoisCoverOverProdIsoSpec :
    (galoisCover B hS hU ⨯ galoisCover B hS hU).left ≅
      Spec (.of (AlgebraicClosure ℚ ⊗[ℚ] AlgebraicClosure ℚ)) :=
  Over.prodLeftIsoPullback (galoisCover B hS hU) (galoisCover B hS hU) ≪≫
    pullbackSpecIso ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)

/-- `Spec ℚ̄ ×_ℚ Spec ℚ̄` is affine. -/
instance isAffine_galoisCoverOverProd :
    IsAffine (galoisCover B hS hU ⨯ galoisCover B hS hU).left :=
  IsAffine.of_isIso (galoisCoverOverProdIsoSpec B hS hU).hom

/-- `Spec ℚ̄ ×_ℚ Spec ℚ̄` is reduced. -/
instance isReduced_galoisCoverOverProd :
    IsReduced (galoisCover B hS hU ⨯ galoisCover B hS hU).left := by
  have := isReduced_algebraicClosure_tensorProduct_rat
  exact isReduced_of_isOpenImmersion (galoisCoverOverProdIsoSpec B hS hU).hom

/-- A morphism from the spectrum of a field to `Spec ℚ̄` which is fixed by a Galois element
forces that element to be the identity. -/
theorem eq_one_of_comp_galoisAction {K : Type} [Field K]
    (β : Spec (.of K) ⟶ Spec (.of (AlgebraicClosure ℚ))) (g : galoisGroup)
    (h : β ≫ (galoisAction B hS hU g).hom.left = β) : g = 1 := by
  have h' : Spec.map (CommRingCat.ofHom (g⁻¹).toRingEquiv.toRingHom ≫ Spec.preimage β) =
      Spec.map (Spec.preimage β) := by
    rwa [Spec.map_comp, Spec.map_preimage]
  have h'' := congrArg (fun φ ↦ (CommRingCat.Hom.hom φ)) (Spec.map_injective h')
  rw [← inv_eq_one]
  ext x
  exact (Spec.preimage β).hom.injective (congrArg (fun φ : AlgebraicClosure ℚ →+* K ↦ φ x) h'')

/-- The underlying morphism of schemes of the inclusion of the summand indexed by `σ` into the
relation scheme of the Galois action. -/
abbrev relationSummand (σ : galoisGroup) :
    (galoisCover B hS hU).left ⟶
      (Space.actionRelationScheme (galoisCover B hS hU) galoisGroup).left :=
  (Over.forget base).map (Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ)

/-- Each summand of the relation scheme of the Galois action is an open subscheme. -/
instance isOpenImmersion_relationSummand (σ : galoisGroup) :
    IsOpenImmersion (relationSummand B hS hU σ) := by
  have key : IsOpenImmersion
      (Sigma.ι (fun _ : galoisGroup ↦ (galoisCover B hS hU).left) σ ≫
        (Space.actionRelationUnderlyingIso (galoisCover B hS hU) galoisGroup).inv) :=
    inferInstance
  rwa [Space.actionRelationUnderlyingIso_inv_ι] at key

/-- Every point of the relation scheme of the Galois action lies on one of its summands. -/
theorem exists_mem_range_relationSummand
    (z : (Space.actionRelationScheme (galoisCover B hS hU) galoisGroup).left) :
    ∃ σ : galoisGroup, z ∈ Set.range (relationSummand B hS hU σ) := by
  obtain ⟨σ, x, hx⟩ := (AlgebraicGeometry.sigmaOpenCover
    (fun _ : galoisGroup ↦ (galoisCover B hS hU).left)).exists_eq
      ((Space.actionRelationUnderlyingIso (galoisCover B hS hU) galoisGroup).hom z)
  refine ⟨σ, x, ?_⟩
  have hx' : (Sigma.ι (fun _ : galoisGroup ↦ (galoisCover B hS hU).left) σ ≫
      (Space.actionRelationUnderlyingIso (galoisCover B hS hU) galoisGroup).inv) x = z := by
    show (Space.actionRelationUnderlyingIso (galoisCover B hS hU) galoisGroup).inv
      (((AlgebraicGeometry.sigmaOpenCover
        (fun _ : galoisGroup ↦ (galoisCover B hS hU).left)).f σ) x) = z
    rw [hx]
    simp
  rwa [Space.actionRelationUnderlyingIso_inv_ι (galoisCover B hS hU) galoisGroup σ] at hx'

/-- On the summand indexed by `σ`, the target map of the graph relation is the action of `σ`. -/
theorem relationSummand_target (σ : galoisGroup) :
    relationSummand B hS hU σ ≫ (galoisRelation B hS hU).target.left =
      (galoisAction B hS hU σ).hom.left := by
  have ht : (galoisRelation B hS hU).target =
      Space.actionRelationTarget (galoisCover B hS hU) galoisGroup (galoisAction B hS hU) :=
    prod.lift_fst _ _
  rw [ht]
  show (Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ ≫
    Sigma.desc (fun h : galoisGroup ↦ (galoisAction B hS hU h).hom)).left = _
  rw [Sigma.ι_desc]

/-- On every summand, the source map of the graph relation is the identity. -/
theorem relationSummand_source (σ : galoisGroup) :
    relationSummand B hS hU σ ≫ (galoisRelation B hS hU).source.left = 𝟙 _ := by
  have hs : (galoisRelation B hS hU).source =
      Space.actionRelationSource (galoisCover B hS hU) galoisGroup :=
    prod.lift_snd _ _
  rw [hs]
  show (Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ ≫
    Sigma.desc (fun _ : galoisGroup ↦ 𝟙 (galoisCover B hS hU))).left = _
  rw [Sigma.ι_desc, Over.id_left]

/-- The graph of the action of the Galois element `σ`, a morphism
`Spec ℚ̄ ⟶ Spec ℚ̄ ×_ℚ Spec ℚ̄`. -/
abbrev galoisGraph (σ : galoisGroup) :
    galoisCover B hS hU ⟶ galoisCover B hS hU ⨯ galoisCover B hS hU :=
  prod.lift (𝟙 _) (galoisAction B hS hU σ).hom

/-- If the two projections of `Spec ℚ̄ ×_ℚ Spec ℚ̄` are related by the Galois action, then the
absolute Galois group of `ℚ` is finite.

The preimages of the summands of `∐_{g} Spec ℚ̄` form an open cover of the quasi-compact scheme
`Spec(ℚ̄ ⊗_ℚ ℚ̄)`, so finitely many summands suffice; and the graph of each Galois element `σ`
lies in the preimage of the summand indexed by `σ⁻¹` only. -/
theorem finite_galoisGroup_of_rel
    (r : galoisCover B hS hU ⨯ galoisCover B hS hU ⟶
      Space.actionRelationScheme (galoisCover B hS hU) galoisGroup)
    (hrt : r ≫ (galoisRelation B hS hU).target = prod.fst)
    (hrs : r ≫ (galoisRelation B hS hU).source = prod.snd) :
    Finite galoisGroup := by
  classical
  let pt : (Spec (.of (AlgebraicClosure ℚ)) : Scheme) := IsLocalRing.closedPoint _
  let O : galoisGroup → Set (galoisCover B hS hU ⨯ galoisCover B hS hU).left :=
    fun τ ↦ r.left ⁻¹' Set.range (relationSummand B hS hU τ)
  have hO (τ : galoisGroup) : IsOpen (O τ) :=
    (relationSummand B hS hU τ).isOpenEmbedding.isOpen_range.preimage r.left.continuous
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO fun w _ ↦
    Set.mem_iUnion.2 (exists_mem_range_relationSummand B hS hU (r.left w))
  have hrt' := congrArg Over.Hom.left hrt
  have hrs' := congrArg Over.Hom.left hrs
  rw [Over.comp_left] at hrt' hrs'
  have : Subsingleton (galoisCover B hS hU).left := by
    show Subsingleton (PrimeSpectrum (AlgebraicClosure ℚ))
    infer_instance
  have hkey (σ τ : galoisGroup) (hmem : (galoisGraph B hS hU σ).left pt ∈ O τ) :
      σ = τ⁻¹ := by
    have hrange : Set.range ((galoisGraph B hS hU σ).left ≫ r.left) ⊆
        Set.range (relationSummand B hS hU τ) := by
      rintro _ ⟨s, rfl⟩
      rw [show s = pt from Subsingleton.elim _ _]
      exact hmem
    let ρ := IsOpenImmersion.lift (relationSummand B hS hU τ) _ hrange
    have hρ : ρ ≫ relationSummand B hS hU τ = (galoisGraph B hS hU σ).left ≫ r.left :=
      IsOpenImmersion.lift_fac _ _ _
    have h₁ : ρ ≫ (galoisAction B hS hU τ).hom.left = 𝟙 _ := by
      rw [← relationSummand_target, ← Category.assoc, hρ, Category.assoc, hrt',
        ← Over.comp_left, prod.lift_fst, Over.id_left]
    have h₂ : ρ = (galoisAction B hS hU σ).hom.left := by
      rw [← Category.comp_id ρ, ← relationSummand_source B hS hU τ, ← Category.assoc, hρ,
        Category.assoc, hrs', ← Over.comp_left, prod.lift_snd]
    have hmul : (galoisAction B hS hU (τ * σ)).hom.left =
        (galoisAction B hS hU σ).hom.left ≫ (galoisAction B hS hU τ).hom.left := by
      rw [map_mul]
      rfl
    have hone : 𝟙 _ ≫ (galoisAction B hS hU (τ * σ)).hom.left = 𝟙 _ := by
      rw [Category.id_comp, hmul, ← h₂, h₁]
    exact eq_inv_of_mul_eq_one_right (eq_one_of_comp_galoisAction B hS hU _ _ hone)
  have hpick (σ : galoisGroup) : ∃ τ : t, (galoisGraph B hS hU σ).left pt ∈ O τ := by
    obtain ⟨τ, hτ, hmem⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((galoisGraph B hS hU σ).left pt)))
    exact ⟨⟨τ, hτ⟩, hmem⟩
  choose φ hφ using hpick
  refine Finite.of_injective φ fun σ σ' he ↦ ?_
  rw [hkey σ _ (hφ σ), hkey σ' _ (he ▸ hφ σ')]


/-! ### The site object `Spec ℚ̄ ×_ℚ Spec ℚ̄` -/

/-- The big fppf site contains `Spec ℚ̄ ×_ℚ Spec ℚ̄`. -/
theorem contains_galoisCoverOver_prod :
    B.Contains (galoisCover B hS hU ⨯ galoisCover B hS hU).left :=
  BigFppfSite.contains_prod_left B _ _ hU hU

/-- `Spec ℚ̄ ×_ℚ Spec ℚ̄`, as an object of the big fppf site over `Spec ℚ`. -/
def siteCoverProd : BigFppfOver B base hS :=
  Over.mk (ObjectProperty.homMk (galoisCover B hS hU ⨯ galoisCover B hS hU).hom :
    B.obj (contains_galoisCoverOver_prod B hS hU) ⟶ B.obj hS)

/-- The first projection `Spec ℚ̄ ×_ℚ Spec ℚ̄ ⟶ Spec ℚ̄`, in the big fppf site. -/
def siteCoverProdFst : siteCoverProd B hS hU ⟶ siteCover B hS hU :=
  Over.homMk (ObjectProperty.homMk (prod.fst : galoisCover B hS hU ⨯ _ ⟶ _).left) (by
    apply ObjectProperty.hom_ext
    exact Over.w (prod.fst : galoisCover B hS hU ⨯ galoisCover B hS hU ⟶ _))

/-- The second projection `Spec ℚ̄ ×_ℚ Spec ℚ̄ ⟶ Spec ℚ̄`, in the big fppf site. -/
def siteCoverProdSnd : siteCoverProd B hS hU ⟶ siteCover B hS hU :=
  Over.homMk (ObjectProperty.homMk (prod.snd : galoisCover B hS hU ⨯ _ ⟶ _).left) (by
    apply ObjectProperty.hom_ext
    exact Over.w (prod.snd : galoisCover B hS hU ⨯ galoisCover B hS hU ⟶ _))

/-- The first projection in the site is the first projection of the product over `Spec ℚ`. -/
theorem post_map_siteCoverProdFst :
    (Over.post B.inclusion).map (siteCoverProdFst B hS hU) =
      (prod.fst : galoisCover B hS hU ⨯ galoisCover B hS hU ⟶ _) :=
  Over.OverMorphism.ext rfl

/-- The second projection in the site is the second projection of the product over `Spec ℚ`. -/
theorem post_map_siteCoverProdSnd :
    (Over.post B.inclusion).map (siteCoverProdSnd B hS hU) =
      (prod.snd : galoisCover B hS hU ⨯ galoisCover B hS hU ⟶ _) :=
  Over.OverMorphism.ext rfl

/-- The underlying scheme of the site object `Spec ℚ̄ ×_ℚ Spec ℚ̄` is reduced. -/
instance isReduced_siteCoverProd :
    IsReduced ((BigFppfOver.toScheme B base hS).obj (siteCoverProd B hS hU)) :=
  isReduced_galoisCoverOverProd B hS hU


/-- A presheaf represented by an object of the site whose underlying scheme is reduced has the
étale-local property of being reduced. -/
private theorem hasEtaleLocalProperty_isReduced_yoneda (T : BigFppfOver B base hS)
    (hT : IsReduced ((BigFppfOver.toScheme B base hS).obj T)) :
    Space.HasEtaleLocalProperty B base hS (yoneda.obj T) (fun V : Scheme ↦ IsReduced V) :=
  (Space.exists_atlas_iff_of_representable B base hS (yoneda.obj T)
    (fun V : Scheme ↦ IsReduced V) T (Iso.refl _)).2 hT

section Quotient

variable [HasSheafify (BigFppfOver.topology B base hS) (Type 0)]

/-- The Galois quotient of `Spec ℚ̄` is an algebraic space over `Spec ℚ`, as asserted by
Stacks 02Z6: the action is free in the sense of condition `(*)` of Stacks 02Z2. -/
theorem isAlgebraicSpace_galoisQuotient :
    IsAlgebraicSpace B base hS (galoisQuotient B hS hU) :=
  Space.isAlgebraicSpace_actionQuotient_unconditional galoisGroup B hS (siteCover B hS hU)
    (galoisAction B hS hU) (galoisAction_nontrivialOnFixedResidueFields B hS hU)

/-- The base change `X_ℚ̄ = X ×_{Spec ℚ} Spec ℚ̄` of the Galois quotient `X` of `Spec ℚ̄`. -/
abbrev galoisQuotientBaseChange : (BigFppfOver B base hS)ᵒᵖ ⥤ Type :=
  pullback (coverToBase B hS hU) (galoisQuotientToBase B hS hU)

/-- The base change `X_ℚ̄ ⟶ Spec ℚ̄` of the structure morphism of the Galois quotient. -/
def galoisQuotientBaseChangeToCover :
    galoisQuotientBaseChange B hS hU ⟶ yoneda.obj (siteCover B hS hU) :=
  pullback.fst _ _

/-- The base change of the Galois quotient of `Spec ℚ̄` to `ℚ̄` is an algebraic space. -/
theorem isAlgebraicSpace_galoisQuotientBaseChange :
    IsAlgebraicSpace B base hS (galoisQuotientBaseChange B hS hU) :=
  isAlgebraicSpace_pullback B base hS _ _
    (isAlgebraicSpace_yoneda B base hS _) (isAlgebraicSpace_galoisQuotient B hS hU)
    (isAlgebraicSpace_yoneda B base hS _)

/-- The projection of `Spec ℚ̄` onto its Galois quotient. -/
abbrev galoisChart : yoneda.obj (siteCover B hS hU) ⟶ galoisQuotient B hS hU :=
  Stacks.Groupoids.quotientChart (BigFppfOver.topology B base hS) (Over.post B.inclusion)
    (siteCover B hS hU)
    (Space.actionRelation (Space.underlyingOver B hS (siteCover B hS hU)) galoisGroup
      (galoisAction B hS hU))

/-- A morphism of presheaves to `Spec ℚ̄` lifts to the base change `X_ℚ̄`, through the
projection of `Spec ℚ̄` onto the Galois quotient. -/
def liftToBaseChange {F : (BigFppfOver B base hS)ᵒᵖ ⥤ Type}
    (a : F ⟶ yoneda.obj (siteCover B hS hU)) : F ⟶ galoisQuotientBaseChange B hS hU :=
  pullback.lift a (a ≫ galoisChart B hS hU) (hom_ext_yoneda_siteBase B hS _ _)

/-- The lift of a morphism to `Spec ℚ̄` recovers it under the projection `X_ℚ̄ ⟶ Spec ℚ̄`. -/
@[reassoc (attr := simp)]
theorem liftToBaseChange_toCover {F : (BigFppfOver B base hS)ᵒᵖ ⥤ Type}
    (a : F ⟶ yoneda.obj (siteCover B hS hU)) :
    liftToBaseChange B hS hU a ≫ galoisQuotientBaseChangeToCover B hS hU = a :=
  pullback.lift_fst _ _ _

/-- **Stacks 049E.** The base change `X_ℚ̄ ⟶ Spec ℚ̄` of the morphism of Stacks 0483 is weakly
radicial.

Over a field-valued point `Spec(K) ⟶ Spec ℚ̄` the fibre has a section, through the projection
of `Spec ℚ̄` onto the Galois quotient; a section is a monomorphism, and it exhibits the trivial,
purely inseparable, extension `K ⊂ K`. The point set of the fibre is a singleton because it
receives the point of the section and because the base change of the universally injective
morphism of Stacks 0483 is universally injective. -/
@[stacks 049E "the base change of Example 0483 to ℚ̄ is weakly radicial"]
theorem isWeaklyRadicial_galoisQuotientBaseChangeToCover :
    Space.IsWeaklyRadicial B base hS (isAlgebraicSpace_galoisQuotientBaseChange B hS hU)
      (isAlgebraicSpace_yoneda B base hS _) (galoisQuotientBaseChangeToCover B hS hU) := by
  intro K _ T eT g
  let f := galoisQuotientBaseChangeToCover B hS hU
  let s : yoneda.obj T ⟶ pullback g f :=
    pullback.lift (𝟙 _) (liftToBaseChange B hS hU g) (by simp [f])
  have hs : s ≫ pullback.fst g f = 𝟙 _ := pullback.lift_fst _ _ _
  have : Mono s := SplitMono.mono ⟨_, hs⟩
  have hTsub := Space.subsingleton_points_yoneda_of_isoSpec_toScheme B base hS T eT
  have hinj : Space.UniversallyInjective B base hS f :=
    Space.universallyInjective_pullback B base hS _ _
      (universallyInjective_galoisQuotientToBase B hS hU)
  refine ⟨⟨⟨Space.pointsMap B base hS _ s
      ((Space.pointsEquivScheme B base hS T).symm (eT.inv (IsLocalRing.closedPoint K)))⟩,
    ⟨fun x y => hinj (yoneda.obj T) (isAlgebraicSpace_yoneda B base hS T) g
      (hTsub.elim _ _)⟩⟩, K, inferInstance, Algebra.id K, inferInstance, T, 𝟙 T, eT, s, this,
    by rw [hs, CategoryTheory.Functor.map_id], by simp⟩


/-- If the base change `X_ℚ̄ ⟶ Spec ℚ̄` were radicial, any two morphisms from a reduced object
of the site to `Spec ℚ̄` would have the same image in the Galois quotient.

Radiciality over the identity point of `Spec ℚ̄` identifies the reduction of the fibre with the
spectrum of a purely inseparable, hence trivial, extension of `ℚ̄`, over `Spec ℚ̄`. A morphism
from a reduced object to the fibre factors through its reduction, so it is determined by its
composite with the projection to `Spec ℚ̄`; and the two morphisms in question give two
morphisms to the fibre with the same such composite. -/
theorem galoisChart_eq_of_isRadicial
    (hrad : Space.IsRadicial B base hS (isAlgebraicSpace_galoisQuotientBaseChange B hS hU)
      (isAlgebraicSpace_yoneda B base hS _) (galoisQuotientBaseChangeToCover B hS hU))
    {T : BigFppfOver B base hS} (hT : IsReduced ((BigFppfOver.toScheme B base hS).obj T))
    (p q₁ q₂ : T ⟶ siteCover B hS hU) :
    yoneda.map q₁ ≫ galoisChart B hS hU = yoneda.map q₂ ≫ galoisChart B hS hU := by
  classical
  let f := galoisQuotientBaseChangeToCover B hS hU
  let U := siteCover B hS hU
  have eT : (BigFppfOver.toScheme B base hS).obj U ≅ Spec (.of (AlgebraicClosure ℚ)) :=
    Iso.refl _
  let P := pullback (𝟙 (yoneda.obj U)) f
  let hP : IsAlgebraicSpace B base hS P :=
    isAlgebraicSpace_pullback B base hS (𝟙 _) f (isAlgebraicSpace_yoneda B base hS U)
      (isAlgebraicSpace_galoisQuotientBaseChange B hS hU) (isAlgebraicSpace_yoneda B base hS U)
  let _ : TopologicalSpace (Space.points B base hS P) := Space.pointTopology B base hS P
  let Z := Space.reducedClosedSubspace B base hS P hP Set.univ isClosed_univ
  have liftZ {T' : BigFppfOver B base hS}
      (hT' : IsReduced ((BigFppfOver.toScheme B base hS).obj T')) (π : yoneda.obj T' ⟶ P) :
      ∃ ρ : yoneda.obj T' ⟶ Z.toFunctor, ρ ≫ Z.ι = π :=
    (Space.exists_lift_closedSubspace_iff_pointsMap_range_subset B base hS hP
      (isAlgebraicSpace_yoneda B base hS T') Z
      (Space.isClosedSubspace_reducedClosedSubspace B base hS P hP Set.univ isClosed_univ)
      (hasEtaleLocalProperty_isReduced_yoneda B hS T' hT') π).2 (by
        intro z _
        rw [Space.range_pointsMap_ι_reducedClosedSubspace B base hS P hP Set.univ isClosed_univ]
        exact Set.mem_univ _)
  rcases hrad (AlgebraicClosure ℚ) U eT (𝟙 _) with
    hempty | ⟨L, hL, hAlg, hPI, M, m, eM, e, hproj, hstruct⟩
  · let σ₀ : yoneda.obj U ⟶ P :=
      pullback.lift (𝟙 _) (liftToBaseChange B hS hU (𝟙 _)) (by simp [f])
    obtain ⟨ρ, -⟩ := liftZ (inferInstanceAs (IsReduced (Spec (.of (AlgebraicClosure ℚ))))) σ₀
    exact (hempty.false (Space.pointsMap B base hS _ ρ
      ((Space.pointsEquivScheme B base hS U).symm
        (eT.inv (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))))).elim
  · let _ : Field L := hL
    let _ : Algebra (AlgebraicClosure ℚ) L := hAlg
    have : IsPurelyInseparable (AlgebraicClosure ℚ) L := hPI
    have : IsIso (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) L)) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso ((BigFppfOver.toScheme B base hS).map m) := by
      rw [hstruct]
      infer_instance
    have : IsIso m := isIso_of_reflects_iso m (BigFppfOver.toScheme B base hS)
    let π (q : T ⟶ U) : yoneda.obj T ⟶ P :=
      pullback.lift (yoneda.map p)
        (pullback.lift (yoneda.map p) (yoneda.map q ≫ galoisChart B hS hU)
          (hom_ext_yoneda_siteBase B hS _ _))
        ((Category.comp_id _).trans (pullback.lift_fst _ _ _).symm)
    obtain ⟨ρ₁, hρ₁⟩ := liftZ hT (π q₁)
    obtain ⟨ρ₂, hρ₂⟩ := liftZ hT (π q₂)
    have hfst (q : T ⟶ U) : π q ≫ pullback.fst (𝟙 (yoneda.obj U)) f = yoneda.map p :=
      pullback.lift_fst _ _ _
    have hZ : e.hom ≫ yoneda.map m = Z.ι ≫ pullback.fst (𝟙 (yoneda.obj U)) f := by
      rw [← hproj, Iso.hom_inv_id_assoc]
    have h₁ : (ρ₁ ≫ e.hom) ≫ yoneda.map m = (ρ₂ ≫ e.hom) ≫ yoneda.map m := by
      rw [Category.assoc, Category.assoc, hZ, ← Category.assoc, ← Category.assoc, hρ₁, hρ₂,
        hfst, hfst]
    have hπ : π q₁ = π q₂ := by
      rw [← hρ₁, ← hρ₂, (cancel_mono e.hom).1 ((cancel_mono (yoneda.map m)).1 h₁)]
    have hsnd (q : T ⟶ U) : π q ≫ pullback.snd (𝟙 (yoneda.obj U)) f ≫
        pullback.snd (coverToBase B hS hU) (galoisQuotientToBase B hS hU) =
          yoneda.map q ≫ galoisChart B hS hU :=
      (pullback.lift_snd_assoc ..).trans (pullback.lift_snd ..)
    rw [← hsnd q₁, ← hsnd q₂, hπ]

/-- **Stacks 049E.** The base change `X_ℚ̄ ⟶ Spec ℚ̄` of the morphism of Stacks 0483 is not
radicial.

Were it radicial, the two projections `Spec ℚ̄ ×_ℚ Spec ℚ̄ ⟶ Spec ℚ̄`, which are morphisms from
the reduced scheme `Spec(ℚ̄ ⊗_ℚ ℚ̄)`, would have the same image in the Galois quotient
(`AlgebraicGeometry.RationalGaloisQuotient.galoisChart_eq_of_isRadicial`). The graph of the
Galois action is the kernel pair of the projection of `Spec ℚ̄` onto its quotient, so the two
projections would be related by a morphism `Spec(ℚ̄ ⊗_ℚ ℚ̄) ⟶ ∐_{g} Spec ℚ̄`, which by
quasi-compactness forces the absolute Galois group of `ℚ` to be finite
(`AlgebraicGeometry.RationalGaloisQuotient.finite_galoisGroup_of_rel`); it is not
(`AlgebraicGeometry.RationalGaloisQuotient.infinite_galoisGroup`). -/
@[stacks 049E "the base change of Example 0483 to ℚ̄ is not radicial"]
theorem not_isRadicial_galoisQuotientBaseChangeToCover :
    ¬ Space.IsRadicial B base hS (isAlgebraicSpace_galoisQuotientBaseChange B hS hU)
      (isAlgebraicSpace_yoneda B base hS _) (galoisQuotientBaseChangeToCover B hS hU) := by
  intro hrad
  let W := siteCoverProd B hS hU
  let F := Over.post (X := B.obj hS) B.inclusion
  let J := BigFppfOver.topology B base hS
  let j := galoisRelation B hS hU
  have heq := galoisChart_eq_of_isRadicial B hS hU hrad (isReduced_siteCoverProd B hS hU)
    (siteCoverProdFst B hS hU) (siteCoverProdFst B hS hU) (siteCoverProdSnd B hS hU)
  have happ := congrArg (fun k ↦ k.app (op W) (𝟙 W)) heq
  simp only [galoisChart, NatTrans.comp_app_apply, yoneda_map_app,
    Stacks.Groupoids.quotientChart_app] at happ
  have := Space.actionRelation_isEtaleEquivalenceRelation (galoisCover B hS hU) galoisGroup
    (galoisAction B hS hU) (galoisAction_nontrivialOnFixedResidueFields B hS hU)
  have hpb := Space.isPullback_toQuotientSheaf_bigFppf B base hS j
  let a : (Stacks.Groupoids.points F (galoisCover B hS hU)).obj (op W) :=
    F.map (siteCoverProdFst B hS hU)
  let b : (Stacks.Groupoids.points F (galoisCover B hS hU)).obj (op W) :=
    F.map (siteCoverProdSnd B hS hU)
  have hab : yonedaEquiv.symm a ≫ Stacks.Groupoids.toQuotientSheaf J F j =
      yonedaEquiv.symm b ≫ Stacks.Groupoids.toQuotientSheaf J F j := by
    apply yonedaEquiv.injective
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let r : F.obj W ⟶ Space.actionRelationScheme (galoisCover B hS hU) galoisGroup :=
    yonedaEquiv (hpb.lift _ _ hab)
  have hrt : r ≫ j.target = a :=
    (congrArg yonedaEquiv (hpb.lift_fst _ _ hab)).trans (Equiv.apply_symm_apply _ _)
  have hrs : r ≫ j.source = b :=
    (congrArg yonedaEquiv (hpb.lift_snd _ _ hab)).trans (Equiv.apply_symm_apply _ _)
  exact not_finite_iff_infinite.2 infinite_galoisGroup
    (finite_galoisGroup_of_rel B hS hU r (hrt.trans (post_map_siteCoverProdFst B hS hU))
      (hrs.trans (post_map_siteCoverProdSnd B hS hU)))

end Quotient

end AlgebraicGeometry.RationalGaloisQuotient

end
