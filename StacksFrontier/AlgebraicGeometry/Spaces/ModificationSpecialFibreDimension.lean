module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTower
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalDenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationNormalPuncturedSurface
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecialFibreDimension

/-!
# The special fibre of a modification of a local domain

Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at least one and `f : X → Spec A` a
modification (Stacks 0AD8). **Stacks 0AYJ, case (1)**, says `dim X_κ ≤ dim A - 1`.

## Main results

* `AlgebraicGeometry.Space.IsIntegralModification.existsUnique_pointsToScheme_eq_genericPoint`:
  exactly one point of `|X|` lies over the generic point of `Spec A`.
* `AlgebraicGeometry.Space.dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralModification`:
  **Stacks 0AYJ, case (1)**.
* `AlgebraicGeometry.Space.dimension_adicFibre_zero_le_one_of_isIntegralModification`: for
  `dim A = 2`, the fibre `X ×_{Spec A} Spec(A/𝔪)` has dimension at most one. This is the input
  the source's proof of Stacks 0AGN feeds to Stacks 0AE7, stated for the adic fibre of index
  `0` that the algebraization results of `FormalAlgebraization.lean` use.

## The proof

The source reduces cases (1)-(3) to case (4); here case (1) is reduced to case (3), which is
on the base (`dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace`). A
modification has integral source, so only the uniqueness of the point over the generic point
`η` of `Spec A` is to be shown. By Stacks 0BBE the morphism is an isomorphism between dense
open subspaces, so it is locally quasi-finite at the generic point `ξ` of `|X|`, and Stacks
0AD5 (`isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq`) says that `ξ` is then the only point
over the generic point of `|Spec A|`, which is `η` under the identification of the points of
the represented space `Spec A` with those of the scheme.

The fibre over the residue field point and the adic fibre of index `0` are base changes along
`Spec(A/𝔪) → Spec A` and `Spec(A/𝔪¹) → Spec A`, which are isomorphic over `Spec A`.

## References

* [Stacks Project, Tag 0AYJ](https://stacks.math.columbia.edu/tag/0AYJ)
* [Stacks Project, Tag 0AGN](https://stacks.math.columbia.edu/tag/0AGN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A)))

/-- A modification `f : X → Spec A` of the spectrum of a local domain has exactly one point
of `|X|` over the generic point of `Spec A`. -/
theorem IsIntegralModification.existsUnique_pointsToScheme_eq_genericPoint [IsDomain A]
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B (Spec (.of A)) hS X}
    {f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hS)}
    (hf : IsIntegralModification B (Spec (.of A)) hS hX
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _)
      (isIntegralSpace_yoneda_baseTerminal A B hS) f) :
    ∃! x : points B (Spec (.of A)) hS X,
      pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)
        (pointsMap B (Spec (.of A)) hS X f x) = genericPoint (Spec (.of A)) := by
  have hY : IsAlgebraicSpace B (Spec (.of A)) hS
      (yoneda.obj (baseTerminal B (Spec (.of A)) hS)) :=
    isAlgebraicSpace_yoneda B (Spec (.of A)) hS _
  have hYint : IsIntegralSpace B (Spec (.of A)) hS
      (yoneda.obj (baseTerminal B (Spec (.of A)) hS)) :=
    isIntegralSpace_yoneda_baseTerminal A B hS
  have hXint : IsIntegralSpace B (Spec (.of A)) hS X := hf.isIntegralSpace B (Spec (.of A)) hS
  have hbir := hf.isBirational B (Spec (.of A)) hS
  have hlft : IsLocallyOfFiniteType B (Spec (.of A)) hS f :=
    (hf.isProper B (Spec (.of A)) hS).isFiniteType.1
  have hdom : IsDominant B (Spec (.of A)) hS f :=
    isDominant_of_isBirational B (Spec (.of A)) hS hX hY hXint.isDecentSpace hYint.isDecentSpace
      (hXint.finite_irreducibleComponents B (Spec (.of A)) hS X)
      (hYint.finite_irreducibleComponents B (Spec (.of A)) hS _) hbir
  -- The two generic points.
  have gen : ∀ {Z : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
      (hZ : IsAlgebraicSpace B (Spec (.of A)) hS Z), IsIntegralSpace B (Spec (.of A)) hS Z →
      ∃ ξ : points B (Spec (.of A)) hS Z, IsGenericPoint ξ Set.univ := fun {Z} hZ hZint => by
    have := quasiSober_points_of_isDecentSpace B (Spec (.of A)) hS hZ hZint.isDecentSpace
    have := hZint.irreducibleSpace B (Spec (.of A)) hS Z
    exact QuasiSober.sober (IrreducibleSpace.isIrreducible_univ _) isClosed_univ
  have _ : IrreducibleSpace (points B (Spec (.of A)) hS X) :=
    hXint.irreducibleSpace B (Spec (.of A)) hS X
  obtain ⟨ξ, hξ⟩ := gen hX hXint
  obtain ⟨η, hη⟩ := gen hY hYint
  -- Stacks 0BBE: an isomorphism between dense open subspaces.
  obtain ⟨U₁, V₁, ψ, hU₁, hV₁, hU₁dense, -, hψ, hψiso⟩ :=
    exists_dense_isOpenSubspace_isIso_of_isBirational B (Spec (.of A)) hS hX hY
      hXint.isDecentSpace hYint.isDecentSpace
      (hXint.finite_irreducibleComponents B (Spec (.of A)) hS X)
      (hYint.finite_irreducibleComponents B (Spec (.of A)) hS _) f hbir
      (Or.inl ⟨hlft, hYint.hasEtaleLocalProperty_isReduced B (Spec (.of A)) hS _⟩)
  have _ := hψiso
  -- The generic point of the source lies in `U₁`, where `f` is locally quasi-finite.
  obtain ⟨u, hu⟩ : ξ ∈ Set.range (pointsMap B (Spec (.of A)) hS U₁.toFunctor U₁.ι) :=
    (hξ.mem_open_set_iff
      (isOpen_range_pointsMap_of_isOpenImmersion B (Spec (.of A)) hS U₁.ι hU₁.2)).2
      (by simpa using Set.range_nonempty_iff_nonempty.2 hU₁dense.nonempty)
  have hqf : IsQuasiFiniteAt B (Spec (.of A)) hS f ξ := by
    refine ⟨U₁, hU₁, u, hu, ?_⟩
    rw [← hψ]
    exact isLocallyQuasiFinite_comp B (Spec (.of A)) hS hU₁.1 hV₁.1 hY ψ V₁.ι
      (isLocallyQuasiFinite_of_isEtale B (Spec (.of A)) hS hV₁.1
        (isEtale_of_isIso B (Spec (.of A)) hS ψ))
      (isLocallyQuasiFinite_of_isEtale B (Spec (.of A)) hS hY (isEtale_ι_of_isOpenSubspace hV₁))
  have huniq := (isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq B (Spec (.of A)) hS hX hY hYint f
    hlft hdom hξ hη).1 hqf
  have hξη : pointsMap B (Spec (.of A)) hS X f ξ = η :=
    pointsMap_eq_of_isGenericPoint B (Spec (.of A)) hS hY hYint.isDecentSpace f hdom hξ hη
  -- The generic point of `|Spec A|` is the generic point of the scheme.
  have hηgen : pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS) η =
      genericPoint (Spec (.of A)) := by
    have h := hη.image
      (schemePointsHomeomorph B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)).continuous
    rw [Set.image_univ, (schemePointsHomeomorph B (Spec (.of A)) hS _).surjective.range_eq,
      closure_univ] at h
    exact h.eq (genericPoint_spec (Spec (.of A)))
  refine ⟨ξ, by beta_reduce; rw [hξη, hηgen], fun z hz => huniq z ?_⟩
  exact (bijective_pointsToScheme B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)).1
    (hz.trans hηgen.symm)

/-- **Stacks 0AYJ, case (1).** Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at
least one and let `f : X → Spec A` be a modification. Then the special fibre `X_κ` has
dimension at most `dim(A) - 1`. -/
@[stacks 0AYJ "case (1), f a modification"]
theorem dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralModification [IsDomain A]
    [IsNoetherianRing A] (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hS))
    (hf : IsIntegralModification B (Spec (.of A)) hS hX
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _)
      (isIntegralSpace_yoneda_baseTerminal A B hS) f) :
    dimension B (Spec (.of A)) hS
        (fieldFibre B (Spec (.of A)) hS f (residueFieldPoint A B hS))
        (isAlgebraicSpace_fieldFibre hX (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _) f
          (residueFieldPoint A B hS)) + 1
      ≤ ringKrullDim A :=
  dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace A B hS hdim hX f
    (hf.isProper B _ hS).isFiniteType.1 (hf.isIntegralSpace B _ hS)
    (hf.existsUnique_pointsToScheme_eq_genericPoint A B hS) _

/-- The spectrum of the residue field and the adic thickening of index `0` are isomorphic
objects of the big fppf site over `Spec A`. -/
def residueSpecOverIsoAdicThickeningObject :
    (residueFieldPoint A B hS).siteObject ≅
      adicThickeningObject A (IsLocalRing.maximalIdeal A) B hS
        (contains_adicThickening A _ B hS) 0 := by
  let e : A ⧸ IsLocalRing.maximalIdeal A ^ (0 + 1) ≃+* A ⧸ IsLocalRing.maximalIdeal A :=
    Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
  let eS : B.inclusion.obj (B.obj (residueFieldPoint A B hS).contained) ≅
      B.inclusion.obj (B.obj (contains_adicThickening A (IsLocalRing.maximalIdeal A) B hS 0)) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let iS : B.obj (residueFieldPoint A B hS).contained ≅
      B.obj (contains_adicThickening A (IsLocalRing.maximalIdeal A) B hS 0) :=
    B.inclusion.preimageIso eS
  refine Over.isoMk iS ?_
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp]
  have key : B.inclusion.map iS.hom = eS.hom := B.inclusion.map_preimage _
  refine (congrArg (fun φ => φ ≫ B.inclusion.map (adicThickeningObject A
    (IsLocalRing.maximalIdeal A) B hS (contains_adicThickening A _ B hS) 0).hom) key).trans ?_
  change eS.hom ≫ adicThickeningι A (IsLocalRing.maximalIdeal A) 0 =
    B.inclusion.map (residueSpecHom A B hS)
  rw [residueSpecHom, Functor.map_preimage]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = _
  rw [← Spec.map_comp]
  congr 1

/-- The fibre of a morphism to `Spec A` over the residue field point is isomorphic to its adic
fibre of index `0` along the maximal ideal. -/
def fieldFibreResidueFieldPointIsoAdicFibreZero
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hS)) :
    fieldFibre B (Spec (.of A)) hS f (residueFieldPoint A B hS) ≅
      adicFibre A (IsLocalRing.maximalIdeal A) B hS (contains_adicThickening A _ B hS) f 0 :=
  have hw : yonedaEquiv.symm (residueFieldPoint A B hS).value =
      yoneda.map (residueSpecOverIsoAdicThickeningObject A B hS).hom ≫
        yoneda.map (adicThickeningMap A (IsLocalRing.maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) 0) := by
    rw [← Functor.map_comp]
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    exact (Over.mkIdTerminal (X := B.obj hS)).hom_ext _ _
  asIso (pullback.map f _ f _ (𝟙 X)
    (yoneda.map (residueSpecOverIsoAdicThickeningObject A B hS).hom) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hw]))

/-- For a modification `f : X → Spec A` of a two-dimensional Noetherian local domain, the
fibre `X ×_{Spec A} Spec(A/𝔪)` has dimension at most one. -/
theorem dimension_adicFibre_zero_le_one_of_isIntegralModification [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (f : X ⟶ yoneda.obj (baseObject A B hS))
    (hf : IsIntegralModification B (Spec (.of A)) hS hX
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _)
      (isIntegralSpace_yoneda_baseTerminal A B hS) f) :
    dimension B (Spec (.of A)) hS
      (adicFibre A (IsLocalRing.maximalIdeal A) B hS (contains_adicThickening A _ B hS) f 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX f 0) ≤ 1 := by
  have h := dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralModification A B hS
    (by rw [hdim]; exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hX f hf
  rw [dimension_eq_of_iso B _ hS _
    (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX f 0)
    (fieldFibreResidueFieldPointIsoAdicFibreZero A B hS f), hdim] at h
  generalize dimension B (Spec (.of A)) hS _ _ = d at h ⊢
  cases d with
  | bot => exact bot_le
  | coe d =>
    have h' : ((d + 1 : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
      simpa only [WithBot.coe_add, WithBot.coe_one] using h
    have h'' : d + 1 ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp h'
    cases d with
    | top => simp at h''
    | coe n =>
      have : n + 1 ≤ 2 := by exact_mod_cast h''
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))

end AlgebraicGeometry.Space

end
