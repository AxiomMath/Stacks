module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointIndivisibility
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints0FH7
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CompositeCommuting

/-!
# Cycle classes of points and the degree (Stacks 0FHV)

Assume given data (D0)–(D3) satisfying (A), (B), (C) over the actual category of smooth
projective schemes over `k` (`Stacks.WeilCohomology.WeilData`). Let `k'/k` be a finite separable
extension and `X` a geometrically irreducible smooth projective scheme over `k'` of dimension `d`.
Stacks 0FHV says that `γ : CH_0(X) → H^{2d}(X)(d)` factors through `deg : CH_0(X) → 𝐙`.

The proof is the source's.

* *Rational points* (`WeilData.cycleClass_rationalPointClass_eq`): for `k'`-rational points
  `x, x'`, Stacks 0FH7 gives a finite separable `K/k'` over which `[x] - [x']` is divisible by an
  integer `n > 1`; by Stacks 0FHU the two `K`-rational points of `X_K` over them have the same
  cycle class, and by (C)(b) along the projection `X_K ⟶ X` so do `x` and `x'`.
* *Closed points* (`WeilData.residueDegree_smul_cycleClass_closedPointClass`): for closed points
  `x, x'` with separable residue fields, `deg(x') γ([x]) = deg(x) γ([x'])`, by the rational-point
  step over a finite separable `K/k'` into which `κ(x)` and `κ(x')` embed, and (C)(b) along
  `X_K ⟶ X`.
* *The factorisation* (`WeilData.exists_cycleClass_comp_eq_comp_chowDegree`): Stacks 0FH5
  generates `CH_0(X)` by the classes of such points.

Along `X_K ⟶ X` the class of a closed point `s` is carried to `[κ(s) : κ(f(s))]` times the class
of its image (`equidimensionalPushforward_closedSubschemeClass_specField`, Stacks 02R4).

## Main definitions

* `Stacks.WeilCohomology.closedPointClass`: the class `[x] ∈ CH^i(X)` of a closed point.

## Main results

* `Stacks.WeilCohomology.WeilData.exists_cycleClass_comp_eq_comp_chowDegree`: **Stacks 0FHV**.
* `Stacks.WeilCohomology.WeilData.cycleClass_rationalPointClass_eq`: the rational-point step.
* `Stacks.WeilCohomology.WeilData.residueDegree_smul_cycleClass_closedPointClass`: the
  closed-point step.
* `Stacks.WeilCohomology.equidimensionalPushforward_closedSubschemeClass_specField`: proper
  pushforward of the class of a closed point.

## References

* [Stacks Project, Tag 0FHV](https://stacks.math.columbia.edu/tag/0FHV)
* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0FHU](https://stacks.math.columbia.edu/tag/0FHU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

section Pushforward

open Classical in
/-- The cycle of a closed point `Spec L ⟶ T` of relative dimension zero, in a degree `n` that is
zero, is the prime cycle of its image. -/
theorem cycleAssociatedToClosedSubscheme_specField_val_of_eq_zero {T : Scheme.{u}}
    (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ T) [IsClosedImmersion i]
    (h : relativeDimension (fieldChowSituation k).dimensionFunction sT
      (i (genericPoint (Spec (.of L)))) = 0) {n : ℤ} (hn : n = 0) (t : T) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sT i n).1 t =
      if t = i (genericPoint (Spec (.of L))) then 1 else 0 := by
  subst hn
  rw [cycleAssociatedToClosedSubscheme_specField_val sT i h,
    Function.locallyFinsuppWithin.single_apply]

/-- **Proper pushforward of the class of a closed point.** Let `f : S ⟶ T` be a morphism of
smooth projective schemes over `k`, both equidimensional of dimension `d`, and let
`i : Spec L ⟶ S`, `j : Spec L' ⟶ T` be closed points with `f (i(*)) = j(*)`. Then
`f_*[i] = [κ(i(*)) : κ(j(*))] [j]` in `CH^d(T)`. -/
theorem equidimensionalPushforward_closedSubschemeClass_specField
    {S T : (SmoothProjectiveScheme k).FullSubcategory} (f : S ⟶ T) {d : ℕ}
    (hS : RelativeDimension S.obj.hom d) (hT : RelativeDimension T.obj.hom d)
    {L L' : Type u} [Field L] [Field L'] (i : Spec (.of L) ⟶ S.obj.left) [IsClosedImmersion i]
    (j : Spec (.of L') ⟶ T.obj.left) [IsClosedImmersion j]
    (hi : relativeDimension (fieldChowSituation k).dimensionFunction S.obj.hom
      (i (genericPoint (Spec (.of L)))) = 0)
    (hj : relativeDimension (fieldChowSituation k).dimensionFunction T.obj.hom
      (j (genericPoint (Spec (.of L')))) = 0)
    (hij : f.hom.left (i (genericPoint (Spec (.of L)))) = j (genericPoint (Spec (.of L')))) :
    equidimensionalPushforward f d d d d (by ring) (closedSubschemeClass S.obj.hom i d) =
      (f.hom.left.residueDegree (i (genericPoint (Spec (.of L)))) : ℤ) •
        closedSubschemeClass T.obj.hom j d := by
  classical
  funext e
  by_cases he : e = d
  · subst he
    have : IsProper f.hom.left := by
      have : IsProper (f.hom.left ≫ T.obj.hom) := by rw [Over.w f.hom]; infer_instance
      exact IsProper.of_comp f.hom.left T.obj.hom
    have := (isClopenDecomposition_dimPart S.obj.hom).isProper_ι e
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, dite_true,
      AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
      AddEquiv.coe_toAddMonoidHom, Pi.smul_apply, closedSubschemeClass_apply]
    rw [chowGroupDegreeEquiv_self]
    have hn : (e : ℤ) - e = 0 := sub_self _
    have hmem : i (genericPoint (Spec (.of L))) ∈ Set.range (dimPart S.obj.hom e).ι := by
      rw [Scheme.Opens.range_ι, dimPart_self_eq_top S.obj.hom hS]
      trivial
    obtain ⟨u0, hu0⟩ := hmem
    have hc : (cycleGroupRestrict (fieldChowSituation k) S.obj.hom (partBase S.obj.hom e)
        (dimPart S.obj.hom e).ι rfl ((e : ℤ) - e)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) S.obj.hom i ((e : ℤ) - e))).1 =
        @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _ u0 1 := by
      refine Function.locallyFinsuppWithin.ext fun u ↦ ?_
      rw [cycleGroupRestrict_apply,
        cycleAssociatedToClosedSubscheme_specField_val_of_eq_zero S.obj.hom i hi hn,
        Function.locallyFinsuppWithin.single_apply]
      exact if_congr ⟨fun h ↦ (dimPart S.obj.hom e).ι.isOpenEmbedding.injective (h.trans hu0.symm),
        fun h ↦ h ▸ hu0⟩ rfl rfl
    have hg : ((dimPart S.obj.hom e).ι ≫ f.hom.left).base u0 =
        j (genericPoint (Spec (.of L'))) := by
      rw [Scheme.Hom.comp_apply, hu0, hij]
    have hpush := properPushforward_single (fieldChowSituation k) (partBase S.obj.hom e) T.obj.hom
      ((dimPart S.obj.hom e).ι ≫ f.hom.left) (by rw [Category.assoc, Over.w f.hom]) ((e : ℤ) - e)
      u0 _ hc
    rw [hg, ite_eq_left (by rw [hj, hn]), Chow.residueDegree_comp,
      residueDegree_eq_one_of_isOpenImmersion (dimPart S.obj.hom e).ι,
      mul_one, hu0] at hpush
    have hcyc : properPushforward (fieldChowSituation k) (partBase S.obj.hom e) T.obj.hom
        ((dimPart S.obj.hom e).ι ≫ f.hom.left) (by rw [Category.assoc, Over.w f.hom]) ((e : ℤ) - e)
        (cycleGroupRestrict (fieldChowSituation k) S.obj.hom (partBase S.obj.hom e)
          (dimPart S.obj.hom e).ι rfl ((e : ℤ) - e)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) S.obj.hom i ((e : ℤ) - e))) =
        (f.hom.left.residueDegree (i (genericPoint (Spec (.of L)))) : ℤ) •
          cycleAssociatedToClosedSubscheme (fieldChowSituation k) T.obj.hom j ((e : ℤ) - e) := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun t ↦ ?_)
      rw [hpush, AddSubgroup.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
        cycleAssociatedToClosedSubscheme_specField_val_of_eq_zero T.obj.hom j hj hn,
        Function.locallyFinsuppWithin.single_apply]
      split_ifs <;> simp
    calc _ = chowGroupRestrict (fieldChowSituation k) T.obj.hom (partBase T.obj.hom e)
          (dimPart T.obj.hom e).ι rfl ((e : ℤ) - e)
          (QuotientAddGroup.mk (properPushforward (fieldChowSituation k) (partBase S.obj.hom e)
            T.obj.hom ((dimPart S.obj.hom e).ι ≫ f.hom.left)
            (by rw [Category.assoc, Over.w f.hom]) ((e : ℤ) - e)
            (cycleGroupRestrict (fieldChowSituation k) S.obj.hom (partBase S.obj.hom e)
              (dimPart S.obj.hom e).ι rfl ((e : ℤ) - e)
              (cycleAssociatedToClosedSubscheme (fieldChowSituation k) S.obj.hom i
                ((e : ℤ) - e))))) := rfl
      _ = _ := by rw [hcyc, QuotientAddGroup.mk_zsmul, map_zsmul]
  · have := isEmpty_dimPart_of_ne T.obj.hom hT he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end Pushforward

/-- **An irreducible scheme smooth over `S` has a relative dimension**: it is one of its parts of
constant dimension, which are open and closed (Stacks 02NM). -/
theorem exists_relativeDimension_of_irreducibleSpace {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX]
    [IrreducibleSpace X] : ∃ d : ℕ, RelativeDimension sX d := by
  obtain ⟨x⟩ := (IrreducibleSpace.toNonempty : Nonempty X)
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart sX).exists_mem x
  refine ⟨d, (relativeDimension_iff_forall_mem_dimPart sX d).2 fun y ↦ ?_⟩
  have := PreirreducibleSpace.preconnectedSpace X
  have h := ((isClopenDecomposition_dimPart sX).isClopen d).eq_univ ⟨x, hd⟩
  exact (Set.ext_iff.mp h y).2 trivial

section OverExtension

variable {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k'] {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k').S) [Smooth p]
  (hp : IsProjectiveMorphism p)

/-- A scheme of relative dimension `d` over `k'` has relative dimension `d` over `k`. -/
theorem isNonemptyEquidimensional_ofOverField [Nonempty X] {d : ℕ} (hd : RelativeDimension p d) :
    IsNonemptyEquidimensional (ofOverField (k := k) p hp) d where
  nonempty := ‹_›
  relativeDimension := by
    have := etale_of_isSeparable (k := k) k'
    have h0 := (isNonemptyEquidimensional_specField (k := k) k').relativeDimension
    have h := hd.comp_of_flat p (SmoothProjectiveScheme.specStructure k k') h0
    rwa [add_zero] at h

/-- A `k'`-rational point of `X` has relative dimension zero over `k`. -/
theorem relativeDimension_ofOverField_rationalPoint (z : (fieldChowSituation k').S ⟶ X)
    (hz : z ≫ p = 𝟙 _) :
    relativeDimension (fieldChowSituation k).dimensionFunction (ofOverField (k := k) p hp).obj.hom
      (z (genericPoint (Spec (.of k')))) = 0 :=
  have := isClosedImmersion_of_comp_eq_id p z hz
  (relativeDimension_comp_closedImmersion _ z _ _).symm.trans
    (relativeDimension_rationalPoint p hp z hz _)

/-- **The class `[x] ∈ CH^i(X)` of a closed point** `x` of `X`, `X` viewed over `k`: the class of
the closed subscheme `Spec κ(x) ⟶ X` (`Stacks.WeilCohomology.closedSubschemeClass`). -/
def closedPointClass {x₀ : X} (h₀ : IsClosed ({x₀} : Set X)) (i : ℤ) :
    codimensionChowGroup k (ofOverField (k := k) p hp).obj.hom i :=
  @closedSubschemeClass k _ (ofOverField (k := k) p hp).obj.left _ (ofOverField p hp).obj.hom _
    (X.fromSpecResidueField x₀) (isClosed_singleton_iff_isClosedImmersion.mp h₀) i

end OverExtension

/-- **Two finite separable extensions embed into a third.** For finite separable extensions
`L₁/K₀`, `L₂/K₀` there is a finite separable extension `K/K₀` receiving `K₀`-embeddings of both:
the compositum of their images in an algebraic closure. -/
theorem exists_finiteSeparable_algHom_algHom (K₀ L₁ L₂ : Type u) [Field K₀] [Field L₁] [Field L₂]
    [Algebra K₀ L₁] [Algebra K₀ L₂] [FiniteDimensional K₀ L₁] [FiniteDimensional K₀ L₂]
    [Algebra.IsSeparable K₀ L₁] [Algebra.IsSeparable K₀ L₂] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra K₀ K) (_ : FiniteDimensional K₀ K)
      (_ : Algebra.IsSeparable K₀ K), Nonempty (L₁ →ₐ[K₀] K) ∧ Nonempty (L₂ →ₐ[K₀] K) := by
  let σ₁ : L₁ →ₐ[K₀] AlgebraicClosure K₀ := IsAlgClosed.lift
  let σ₂ : L₂ →ₐ[K₀] AlgebraicClosure K₀ := IsAlgClosed.lift
  have : FiniteDimensional K₀ σ₁.fieldRange := σ₁.toLinearMap.finiteDimensional_range
  have : FiniteDimensional K₀ σ₂.fieldRange := σ₂.toLinearMap.finiteDimensional_range
  have : Algebra.IsSeparable K₀ σ₁.fieldRange := AlgEquiv.Algebra.isSeparable σ₁.equivFieldRange
  have : Algebra.IsSeparable K₀ σ₂.fieldRange := AlgEquiv.Algebra.isSeparable σ₂.equivFieldRange
  exact ⟨↥(σ₁.fieldRange ⊔ σ₂.fieldRange : IntermediateField K₀ (AlgebraicClosure K₀)),
    inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(IntermediateField.inclusion le_sup_left).comp σ₁.equivFieldRange.toAlgHom⟩,
    ⟨(IntermediateField.inclusion le_sup_right).comp σ₂.equivFieldRange.toAlgHom⟩⟩

/-- A `k'`-embedding `κ(z) ⟶ K` of the residue field at a point `z` of a scheme over `k'` gives a
`K`-valued point `Spec K ⟶ Spec κ(z) ⟶ X` lying over `Spec K ⟶ Spec k'`. -/
theorem specMap_comp_fromSpecResidueField_comp {k' : Type u} [Field k'] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k')) [Smooth p] (hp : IsProjectiveMorphism p) (z : X) {K : Type u}
    [Field K] [Algebra k' K] (σ : X.residueField z →+* K)
    (hσ : σ.comp ((Scheme.ΓSpecIso (.of k')).inv ≫ p.appTop ≫ X.Γevaluation z).hom =
      algebraMap k' K) :
    Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecResidueField z ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k' K)) := by
  have h := fromSpecResidueField_comp_hom
    (Y := (⟨Over.mk p, ‹Smooth p›, hp.isProjective⟩ :
      (SmoothProjectiveScheme k').FullSubcategory)) z
  refine (congrArg (Spec.map (CommRingCat.ofHom σ) ≫ ·) h).trans ?_
  rw [← Spec.map_comp, ← hσ]
  rfl

/-- A morphism of finite type from the spectrum of a field `K` to that of a field `k'` has nonzero
residue degree at the generic point. -/
private theorem residueDegree_genericPoint_ne_zero {k' K : Type u} [Field k'] [Field K]
    (g : Spec (.of K) ⟶ Spec (.of k')) [LocallyOfFiniteType g] :
    g.residueDegree (genericPoint (Spec (.of K))) ≠ 0 := by
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hcl : IsClosed ({genericPoint (Spec (.of K))} : Set (Spec (.of K))) := by
    rw [show ({genericPoint (Spec (.of K))} : Set (Spec (.of K))) = Set.univ from
      Set.eq_univ_of_forall fun z ↦ Subsingleton.elim z _]
    exact isClosed_univ
  exact residueDegree_ne_zero_of_finite k' g _ (residueField_finite_of_closed_point k' g _ hcl)

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)
variable {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k']

/-- **The rational-point step of Stacks 0FHV, in the dimension of `X`.** -/
theorem cycleClass_rationalPointClass_eq_of_relativeDimension [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k').S) [Smooth p] [GeometricallyIrreducible p]
    (hp : IsProjectiveMorphism p) {d : ℕ} (hd : RelativeDimension p d)
    (x x' : (fieldChowSituation k').S ⟶ X) (hx : x ≫ p = 𝟙 _) (hx' : x' ≫ p = 𝟙 _) :
    W.cycleClass (ofOverField p hp) d (rationalPointClass p hp x hx d) =
      W.cycleClass (ofOverField p hp) d (rationalPointClass p hp x' hx' d) := by
  -- an integer `n > 1` invertible in `k'`
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℤ, 1 < n ∧ IsUnit ((n : ℤ) : k') := by
    by_cases h2 : IsUnit ((2 : ℤ) : k')
    · exact ⟨2, by norm_num, h2⟩
    · refine ⟨3, by norm_num, ?_⟩
      have h20 : ((2 : ℤ) : k') = 0 := by simpa using h2
      have : ((3 : ℤ) : k') = 1 := by
        rw [show (3 : ℤ) = 2 + 1 by norm_num, Int.cast_add, h20, zero_add, Int.cast_one]
      rw [this]
      exact isUnit_one
  -- Stacks 0FH7
  obtain ⟨K, _, _, _, _, δ, hδ⟩ :=
    exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_isProjectiveMorphism k' p hp n hn
      x x' hx hx'
  let : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional k K := Module.Finite.trans k' K
  have : Algebra.IsSeparable k K := Algebra.IsSeparable.trans k k' K
  have := etale_of_isSeparable (k := k) k'
  have := etale_of_isSeparable (k := k) K
  let g := (fieldExtensionBaseChangeSituation k' K).g
  let pK := pullback.snd p g
  have hpKproj : IsProjectiveMorphism pK := hp.baseChange _
  let y : (fieldChowSituation K).S ⟶ Limits.pullback p g :=
    pullback.lift (g ≫ x) (𝟙 _) (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  let y' : (fieldChowSituation K).S ⟶ Limits.pullback p g :=
    pullback.lift (g ≫ x') (𝟙 _) (by rw [Category.assoc, hx', Category.comp_id, Category.id_comp])
  have hy : y ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  have hy' : y' ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  have hxy : y ≫ pullback.fst p g = g ≫ x := pullback.lift_fst _ _ _
  have hxy' : y' ≫ pullback.fst p g = g ≫ x' := pullback.lift_fst _ _ _
  have hsub := baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub k' K p
    (IsPullback.of_hasPullback p g) x hx x' hx' y hy hxy y' hy' hxy'
  -- Stacks 0FHU on `X_K`
  have h0FHU : (fun i : ℤ ↦ W.cycleClass (ofOverField pK hpKproj) i
        (rationalPointClass pK hpKproj y hy i)) =
      fun i : ℤ ↦ W.cycleClass (ofOverField pK hpKproj) i
        (rationalPointClass pK hpKproj y' hy' i) := by
    by_contra hne
    exact W.rationalPointChowClass_sub_ne_zsmul hA hB hC pK hpKproj y y' hy hy' hne n hn1 δ
      (hsub.symm.trans hδ)
  -- the pushforward along `X_K ⟶ X`
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  have : Nonempty X := ⟨x (genericPoint (Spec (.of k')))⟩
  have : Nonempty (Limits.pullback p g : Scheme.{u}) := ⟨y (genericPoint (Spec (.of K)))⟩
  have hX := isNonemptyEquidimensional_ofOverField (k := k) p hp hd
  have hXK := isNonemptyEquidimensional_ofOverField (k := k) pK hpKproj
    (hd.of_isPullback (IsPullback.of_hasPullback p g))
  let q : ofOverField (k := k) pK hpKproj ⟶ ofOverField (k := k) p hp :=
    SmoothProjectiveScheme.baseChangeFst k p hp (k'' := K)
  have := isClosedImmersion_of_comp_eq_id p x hx
  have := isClosedImmersion_of_comp_eq_id p x' hx'
  have := isClosedImmersion_of_comp_eq_id pK y hy
  have := isClosedImmersion_of_comp_eq_id pK y' hy'
  have himg : ∀ (z : (fieldChowSituation K).S ⟶ Limits.pullback p g)
      (z0 : (fieldChowSituation k').S ⟶ X), z ≫ pullback.fst p g = g ≫ z0 →
      q.hom.left (z (genericPoint (Spec (.of K)))) = z0 (genericPoint (Spec (.of k'))) := by
    intro z z0 hzz
    refine (Scheme.Hom.comp_apply z (pullback.fst p g) _).symm.trans ?_
    rw [hzz, Scheme.Hom.comp_apply]
    exact congrArg z0.base (Subsingleton.elim _ _)
  have hdeg : ∀ (z : (fieldChowSituation K).S ⟶ Limits.pullback p g) (hz : z ≫ pK = 𝟙 _)
      (z0 : (fieldChowSituation k').S ⟶ X) (hz0 : z0 ≫ p = 𝟙 _), z ≫ pullback.fst p g = g ≫ z0 →
      q.hom.left.residueDegree (z (genericPoint (Spec (.of K)))) =
        g.residueDegree (genericPoint (Spec (.of K))) := by
    intro z hz z0 hz0 hzz
    have h1 := Chow.residueDegree_comp z (pullback.fst p g) (genericPoint (Spec (.of K)))
    rw [hzz, Chow.residueDegree_comp g z0, (residueDegree_eq_one_of_section pK z hz _).2,
      (residueDegree_eq_one_of_section p z0 hz0 _).2, one_mul, mul_one] at h1
    exact h1.symm
  have hpush : ∀ (z : (fieldChowSituation K).S ⟶ Limits.pullback p g) (hz : z ≫ pK = 𝟙 _)
      (z0 : (fieldChowSituation k').S ⟶ X) (hz0 : z0 ≫ p = 𝟙 _), z ≫ pullback.fst p g = g ≫ z0 →
      (q.hom.left.residueDegree (z (genericPoint (Spec (.of K)))) : ℤ) •
          W.cycleClass (ofOverField p hp) d (rationalPointClass p hp z0 hz0 d) =
        W.pushforward hA.perfectPairing q hXK hX (2 * d) d (2 * d) d (by ring) (by ring)
          (W.cycleClass (ofOverField pK hpKproj) d (rationalPointClass pK hpKproj z hz d)) := by
    intro z hz z0 hz0 hzz
    have : IsClosedImmersion (X := Spec (.of K)) (Y := (ofOverField (k := k) pK hpKproj).obj.left)
      z := isClosedImmersion_of_comp_eq_id pK z hz
    have : IsClosedImmersion (X := Spec (.of k')) (Y := (ofOverField (k := k) p hp).obj.left)
      z0 := isClosedImmersion_of_comp_eq_id p z0 hz0
    have hQ := equidimensionalPushforward_closedSubschemeClass_specField q hXK.relativeDimension
      hX.relativeDimension z z0 (relativeDimension_ofOverField_rationalPoint pK hpKproj z hz)
      (relativeDimension_ofOverField_rationalPoint p hp z0 hz0) (himg z z0 hzz)
    rw [← map_zsmul, ← hC.pushforward q d d hXK hX d d (by ring)]
    exact congrArg (W.cycleClass (ofOverField p hp) d) hQ.symm
  have hm := residueDegree_genericPoint_ne_zero g
  have h := (hpush y hy x hx hxy).trans
    ((congrArg _ (congrFun h0FHU (d : ℤ))).trans (hpush y' hy' x' hx' hxy').symm)
  rw [hdeg y hy x hx hxy, hdeg y' hy' x' hx' hxy', ← Int.cast_smul_eq_zsmul F,
    ← Int.cast_smul_eq_zsmul F] at h
  exact smul_right_injective _ (by exact_mod_cast hm) h

/-- **The rational-point step of Stacks 0FHV.** Assume given (D0)–(D3) satisfying (A), (B), (C).
Let `k'/k` be a finite separable extension, `X` a geometrically irreducible smooth projective
scheme over `k'` and `x, x'` two `k'`-rational points of `X`. Then `γ(x) = γ(x')`: the classes
`γ([x]), γ([x']) ∈ H^{2i}(X)(i)` agree in every codimension `i`.

This is the second paragraph of the source's proof of Stacks 0FHV. By Stacks 0FH7 there is a
finite separable `K/k'` over which `[x] - [x']` becomes divisible by an integer `n > 1`
invertible in `k'`; by Stacks 0FHU the two rational points of `X_K` over `x, x'` then have the
same cycle class; by (C)(b) along the projection `X_K ⟶ X`, which carries the class of either
point to `[K : k']` times the class of its image, `γ(x) = γ(x')`. -/
theorem cycleClass_rationalPointClass_eq [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k').S) [Smooth p] [GeometricallyIrreducible p]
    (hp : IsProjectiveMorphism p) (x x' : (fieldChowSituation k').S ⟶ X) (hx : x ≫ p = 𝟙 _)
    (hx' : x' ≫ p = 𝟙 _) :
    (fun i : ℤ ↦ W.cycleClass (ofOverField p hp) i (rationalPointClass p hp x hx i)) =
      fun i : ℤ ↦ W.cycleClass (ofOverField p hp) i (rationalPointClass p hp x' hx' i) := by
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton p
  obtain ⟨d, hd⟩ := exists_relativeDimension_of_irreducibleSpace p
  have : Nonempty X := ⟨x (genericPoint (Spec (.of k')))⟩
  have hX := isNonemptyEquidimensional_ofOverField (k := k) p hp hd
  funext i
  by_cases hi : i = d
  · subst hi
    exact W.cycleClass_rationalPointClass_eq_of_relativeDimension hA hB hC p hp hd x x' hx hx'
  · have hzero : ∀ (z : (fieldChowSituation k').S ⟶ X) (hz : z ≫ p = 𝟙 _),
        rationalPointClass (k := k) p hp z hz i = 0 := by
      intro z hz
      have : IsClosedImmersion (X := Spec (.of k')) (Y := (ofOverField (k := k) p hp).obj.left)
        z := isClosedImmersion_of_comp_eq_id p z hz
      refine closedSubschemeClass_specField_eq_zero (ofOverField (k := k) p hp).obj.hom z
        (relativeDimension_rationalPoint (k := k) p hp z hz) (d := d) ?_ hi
      rw [dimPart_self_eq_top _ hX.relativeDimension]
      trivial
    rw [hzero x hx, hzero x' hx']

/-- **The closed-point step of Stacks 0FHV.** Let `X` be a geometrically irreducible smooth
projective scheme over `k'` of relative dimension `d`, and `x₀, x₁` closed points of `X` with
residue fields separable over `k'`. Then `deg(x₁) γ([x₀]) = deg(x₀) γ([x₁])` in `H^{2d}(X)(d)`,
`deg(x) = [κ(x) : k']`.

This is the first paragraph of the source's proof of Stacks 0FHV: over a finite separable `K/k'`
into which `κ(x₀)` and `κ(x₁)` embed, `X_K` has `K`-rational points `y₀, y₁` over `x₀, x₁`; their
classes agree by the rational-point step, and the projection `X_K ⟶ X` carries `[yᵢ]` to
`[K : κ(xᵢ)] [xᵢ]`, so (C)(b) gives `[K : κ(x₀)] γ([x₀]) = [K : κ(x₁)] γ([x₁])`. -/
theorem residueDegree_smul_cycleClass_closedPointClass [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k').S) [Smooth p] [GeometricallyIrreducible p]
    (hp : IsProjectiveMorphism p) {d : ℕ} (hd : RelativeDimension p d) {x₀ x₁ : X}
    (h₀ : IsClosed ({x₀} : Set X)) (h₁ : IsClosed ({x₁} : Set X))
    (hs₀ : HasSeparableResidueField k' p x₀) (hs₁ : HasSeparableResidueField k' p x₁) :
    (p.residueDegree x₁ : ℤ) • W.cycleClass (ofOverField p hp) d (closedPointClass p hp h₀ d) =
      (p.residueDegree x₀ : ℤ) •
        W.cycleClass (ofOverField p hp) d (closedPointClass p hp h₁ d) := by
  let : Algebra k' (X.residueField x₀) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ p.appTop ≫ X.Γevaluation x₀).hom.toAlgebra
  let : Algebra k' (X.residueField x₁) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ p.appTop ≫ X.Γevaluation x₁).hom.toAlgebra
  have : Module.Finite k' (X.residueField x₀) := residueField_finite_of_closed_point k' p x₀ h₀
  have : Module.Finite k' (X.residueField x₁) := residueField_finite_of_closed_point k' p x₁ h₁
  have : Algebra.IsSeparable k' (X.residueField x₀) := hs₀
  have : Algebra.IsSeparable k' (X.residueField x₁) := hs₁
  obtain ⟨K, _, _, _, _, ⟨σ₀⟩, ⟨σ₁⟩⟩ :=
    exists_finiteSeparable_algHom_algHom k' (X.residueField x₀) (X.residueField x₁)
  let : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional k K := Module.Finite.trans k' K
  have : Algebra.IsSeparable k K := Algebra.IsSeparable.trans k k' K
  have := etale_of_isSeparable (k := k) k'
  have := etale_of_isSeparable (k := k) K
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let g := (fieldExtensionBaseChangeSituation k' K).g
  let pK := pullback.snd p g
  have hpKproj : IsProjectiveMorphism pK := hp.baseChange _
  have hdK : RelativeDimension pK d := hd.of_isPullback (IsPullback.of_hasPullback p g)
  -- the `K`-rational points over `x₀` and `x₁`
  have hlift : ∀ (z : X) (σ : X.residueField z →+* K),
      σ.comp ((Scheme.ΓSpecIso (.of k')).inv ≫ p.appTop ≫ X.Γevaluation z).hom = algebraMap k' K →
      (Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecResidueField z) ≫ p = 𝟙 _ ≫ g := fun z σ hσ ↦ by
    rw [Category.assoc, specMap_comp_fromSpecResidueField_comp p hp z σ hσ, Category.id_comp]
  let y₀ : (fieldChowSituation K).S ⟶ Limits.pullback p g :=
    pullback.lift _ (𝟙 _) (hlift x₀ σ₀.toRingHom σ₀.comp_algebraMap)
  let y₁ : (fieldChowSituation K).S ⟶ Limits.pullback p g :=
    pullback.lift _ (𝟙 _) (hlift x₁ σ₁.toRingHom σ₁.comp_algebraMap)
  have hy₀ : y₀ ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  have hy₁ : y₁ ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  have hxy₀ : y₀ ≫ pullback.fst p g =
      Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ X.fromSpecResidueField x₀ :=
    pullback.lift_fst _ _ _
  have hxy₁ : y₁ ≫ pullback.fst p g =
      Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ X.fromSpecResidueField x₁ :=
    pullback.lift_fst _ _ _
  -- the rational-point step on `X_K`
  have hrat := W.cycleClass_rationalPointClass_eq_of_relativeDimension (k' := K) hA hB hC pK
    hpKproj hdK y₀ y₁ hy₀ hy₁
  -- the pushforward along `X_K ⟶ X`
  have : Nonempty X := ⟨x₀⟩
  have : Nonempty (Limits.pullback p g : Scheme.{u}) := ⟨y₀ (genericPoint (Spec (.of K)))⟩
  have hX := isNonemptyEquidimensional_ofOverField (k := k) p hp hd
  have hXK := isNonemptyEquidimensional_ofOverField (k := k) pK hpKproj hdK
  let q : ofOverField (k := k) pK hpKproj ⟶ ofOverField (k := k) p hp :=
    SmoothProjectiveScheme.baseChangeFst k p hp (k'' := K)
  have himg : ∀ (z : (fieldChowSituation K).S ⟶ Limits.pullback p g) (x : X)
      (σ : X.residueField x →+* K),
      z ≫ pullback.fst p g = Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecResidueField x →
      (z ≫ pullback.fst p g) (genericPoint (Spec (.of K))) = x := by
    intro z x σ hzx
    rw [hzx, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hpush : ∀ (z : (fieldChowSituation K).S ⟶ Limits.pullback p g) (hz : z ≫ pK = 𝟙 _)
      (x : X) (hx : IsClosed ({x} : Set X)) (σ : X.residueField x →+* K),
      z ≫ pullback.fst p g = Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecResidueField x →
      (q.hom.left.residueDegree (z (genericPoint (Spec (.of K)))) : ℤ) •
          W.cycleClass (ofOverField p hp) d (closedPointClass p hp hx d) =
        W.pushforward hA.perfectPairing q hXK hX (2 * d) d (2 * d) d (by ring) (by ring)
          (W.cycleClass (ofOverField pK hpKproj) d (rationalPointClass pK hpKproj z hz d)) := by
    intro z hz x hx σ hzx
    have : IsClosedImmersion (X := Spec (.of K)) (Y := (ofOverField (k := k) pK hpKproj).obj.left)
      z := isClosedImmersion_of_comp_eq_id pK z hz
    have hjx : relativeDimension (fieldChowSituation k).dimensionFunction
        (ofOverField (k := k) p hp).obj.hom
        (X.fromSpecResidueField x (genericPoint (Spec (.of (X.residueField x))))) = 0 := by
      rw [Scheme.fromSpecResidueField_apply]
      exact relativeDimension_eq_zero_of_isClosed (fieldChowSituation k) (fun _ _ ↦ rfl)
        (ofOverField (k := k) p hp).obj.hom x hx
    have hQ := @equidimensionalPushforward_closedSubschemeClass_specField _ _ _ _ q d
      hXK.relativeDimension hX.relativeDimension K (X.residueField x) _ _ z _
      (X.fromSpecResidueField x) (isClosed_singleton_iff_isClosedImmersion.mp hx)
      (relativeDimension_ofOverField_rationalPoint pK hpKproj z hz) hjx
      (((Scheme.Hom.comp_apply _ _ _).symm.trans (himg z x σ hzx)).trans
        (Scheme.fromSpecResidueField_apply x _).symm)
    rw [← map_zsmul, ← hC.pushforward q d d hXK hX d d (by ring)]
    exact congrArg (W.cycleClass (ofOverField p hp) d) hQ.symm
  -- the degrees: `[K : k'] = [κ(x) : k'] [K : κ(x)]`
  have hdeg : ∀ (z : (fieldChowSituation K).S ⟶ Limits.pullback p g) (hz : z ≫ pK = 𝟙 _)
      (x : X) (σ : X.residueField x →+* K),
      z ≫ pullback.fst p g = Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecResidueField x →
      g.residueDegree (genericPoint (Spec (.of K))) =
        p.residueDegree x * q.hom.left.residueDegree (z (genericPoint (Spec (.of K)))) := by
    intro z hz x σ hzx
    have h1 := Chow.residueDegree_comp (z ≫ pullback.fst p g) p (genericPoint (Spec (.of K)))
    have h3 : (z ≫ pullback.fst p g) ≫ p = g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz, Category.id_comp]
    rwa [h3, himg z x σ hzx, Chow.residueDegree_comp z (pullback.fst p g),
      (residueDegree_eq_one_of_section pK z hz _).2, mul_one] at h1
  have hN := residueDegree_genericPoint_ne_zero g
  have e := (hpush y₀ hy₀ x₀ h₀ σ₀.toRingHom hxy₀).trans
    ((congrArg _ hrat).trans (hpush y₁ hy₁ x₁ h₁ σ₁.toRingHom hxy₁).symm)
  have d₀ := hdeg y₀ hy₀ x₀ σ₀.toRingHom hxy₀
  have d₁ := hdeg y₁ hy₁ x₁ σ₁.toRingHom hxy₁
  set m₀ := q.hom.left.residueDegree (y₀ (genericPoint (Spec (.of K))))
  set m₁ := q.hom.left.residueDegree (y₁ (genericPoint (Spec (.of K))))
  set a₀ := p.residueDegree x₀
  set a₁ := p.residueDegree x₁
  set γ₀ := W.cycleClass (ofOverField p hp) d (closedPointClass p hp h₀ d)
  set γ₁ := W.cycleClass (ofOverField p hp) d (closedPointClass p hp h₁ d)
  have hm₀ : (m₀ : F) ≠ 0 := Nat.cast_ne_zero.mpr fun h ↦ hN (by rw [d₀, h, mul_zero])
  simp only [← Int.cast_smul_eq_zsmul F, Int.cast_natCast] at e ⊢
  refine smul_right_injective _ hm₀ ?_
  calc (m₀ : F) • (a₁ : F) • γ₀ = (a₁ : F) • (m₀ : F) • γ₀ := smul_comm _ _ _
    _ = (a₁ : F) • (m₁ : F) • γ₁ := by rw [e]
    _ = ((a₁ * m₁ : ℕ) : F) • γ₁ := by rw [smul_smul, Nat.cast_mul]
    _ = ((a₀ * m₀ : ℕ) : F) • γ₁ := by rw [← d₁, ← d₀]
    _ = (m₀ : F) • (a₀ : F) • γ₁ := by rw [Nat.cast_mul, mul_comm (a₀ : F), smul_smul]

/-- **Stacks Project, Tag 0FHV.** Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and
(C). Let `k'/k` be a finite separable extension and let `X` be a geometrically irreducible smooth
projective scheme over `k'` of dimension `d`. Then `γ : CH_0(X) → H^{2d}(X)(d)` factors through
`deg : CH_0(X) → 𝐙`.

Here `X` is a scheme with a smooth projective, geometrically irreducible structure morphism
`p : X ⟶ Spec k'`, viewed over `k` through `Spec k' ⟶ Spec k` (`ofOverField p hp`), which is how
the data over `k` apply to it; "of dimension `d`" is `topologicalKrullDim X = d`. `CH_0(X)` is
the Chow group of zero cycles of `X` over `k'` and `deg` its degree (Stacks 0AZ1,
`Stacks.Chow.chowDegree`, read at the point `s` of `Spec k'`); `γ` is the cycle class map
`CH^d(X) → H^{2d}(X)(d)` of (D2) composed with `CH_0(X) = CH^d(X)`
(`zeroCycleToCodimensionOfExtension`).

The proof is the source's. By Stacks 0FH5 `CH_0(X)` is generated by the classes of closed points
with separable residue field, and for two such points
`deg(x') γ([x]) = deg(x) γ([x'])` (`WeilData.residueDegree_smul_cycleClass_closedPointClass`):
over a finite separable extension into which both residue fields embed this comes from the
rational-point step (Stacks 0FH7, Stacks 0FHU, (C)(b)) and (C)(b) along `X_K ⟶ X`. -/
@[stacks 0FHV "for X smooth projective and geometrically irreducible over a finite separable \
  k'/k, viewed over k, with the actual CH_0(X) over k' and its degree, the data (D0)-(D3) and \
  axioms (A), (B), (C) over the actual category of smooth projective k-schemes"]
theorem exists_cycleClass_comp_eq_comp_chowDegree [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k').S) [Smooth p] [GeometricallyIrreducible p]
    (hp : IsProjectiveMorphism p) {d : ℕ} (hd : topologicalKrullDim X = d)
    (s : (fieldChowSituation k').S) :
    haveI := isProper_of_isProjectiveMorphism p hp
    haveI : LocallyOfFiniteType
        (show (ofOverField (k := k) p hp).obj.left ⟶ (fieldChowSituation k').S from p) :=
      inferInstanceAs (LocallyOfFiniteType p)
    ∃ φ : ℤ →+ W.Tw (ofOverField p hp) (2 * d) d,
      (W.cycleClass (ofOverField p hp) d).comp
          (zeroCycleToCodimensionOfExtension (ofOverField p hp) p rfl d) =
        φ.comp (chowDegree (fieldChowSituation k') (fieldChowSituation_dimensionFunction k') p
          s) := by
  have := isProper_of_isProjectiveMorphism p hp
  have : LocallyOfFiniteType
      (show (ofOverField (k := k) p hp).obj.left ⟶ (fieldChowSituation k').S from p) :=
    inferInstanceAs (LocallyOfFiniteType p)
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton p
  have : Nonempty X := IrreducibleSpace.toNonempty
  obtain ⟨r, hr⟩ := exists_relativeDimension_of_irreducibleSpace p
  obtain rfl : d = r := by
    have h := topologicalKrullDim_eq_of_relativeDimension (d := r) p hr
    rw [hd] at h
    exact_mod_cast h
  -- the class and the degree of a closed point
  have hcyc : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      cycleAssociatedToClosedSubscheme (fieldChowSituation k') p
          (integralComponentAt x).subschemeι 0 =
        @cycleAssociatedToClosedSubscheme (fieldChowSituation k') _ _ p _ (X.fromSpecResidueField x)
          (isClosed_singleton_iff_isClosedImmersion.mp hx) 0 := by
    intro x hx
    have := isIntegral_integralComponentAt x
    have := isClosed_singleton_iff_isClosedImmersion.mp hx
    refine cycleAssociatedToClosedSubscheme_eq_of_genericPoint_eq (fieldChowSituation k') p
      (integralComponentAt x).subschemeι (X.fromSpecResidueField x) ?_ 0
    rw [Scheme.fromSpecResidueField_apply]
    exact genericPointOf_integralComponentAt x
  have hgen : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      zeroCycleToCodimensionOfExtension (ofOverField p hp) p rfl d
          (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k') p 0)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k') p
              (integralComponentAt x).subschemeι 0)) = closedPointClass (k := k) p hp hx d := by
    intro x hx
    rw [hcyc x hx]
    have := SmoothProjectiveScheme.isFinite_specStructure k k'
    refine @zeroCycleToCodimensionOfExtension_mk k _ k' _ _ _ (ofOverField p hp) p _ rfl _
      (X.fromSpecResidueField x) (isClosed_singleton_iff_isClosedImmersion.mp hx)
      (fun z ↦ (@relativeDimension_comp_closedImmersion _ _ _
        (fieldChowSituation k).dimensionFunction
        (X.fromSpecResidueField x) (isClosed_singleton_iff_isClosedImmersion.mp hx)
        (p ≫ SmoothProjectiveScheme.specStructure k k') z).trans ?_) d
    rw [Scheme.fromSpecResidueField_apply]
    exact relativeDimension_eq_zero_of_isClosed (fieldChowSituation k) (fun _ _ ↦ rfl)
      (p ≫ SmoothProjectiveScheme.specStructure k k') x hx
  have hdegx : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      chowDegree (fieldChowSituation k') (fieldChowSituation_dimensionFunction k') p s
          (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k') p 0)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k') p
              (integralComponentAt x).subschemeι 0)) = (p.residueDegree x : ℤ) := by
    intro x hx
    rw [hcyc x hx]
    refine (chowDegree_mk (fieldChowSituation k') (fieldChowSituation_dimensionFunction k') p s
      _).trans ?_
    rw [Subsingleton.elim s (p.base x)]
    refine cycleDegree_single (fieldChowSituation k') (fieldChowSituation_dimensionFunction k') p
      x _ ?_
    have h := @cycleAssociatedToClosedSubscheme_specField_val k' _ X p (X.residueField x) _ _
      (X.fromSpecResidueField x) (isClosed_singleton_iff_isClosedImmersion.mp hx)
      (by rw [Scheme.fromSpecResidueField_apply]
          exact relativeDimension_eq_zero_of_isClosed (fieldChowSituation k') (fun _ _ ↦ rfl) p x
            hx)
    rwa [Scheme.fromSpecResidueField_apply] at h
  -- `γ` is `deg · v` as soon as it is on the generators of Stacks 0FH5
  have hfac : ∀ v : W.Tw (ofOverField p hp) (2 * d) d,
      (∀ (x : X) (hx : IsClosed ({x} : Set X)), HasSeparableResidueField k' p x →
        W.cycleClass (ofOverField p hp) d (closedPointClass p hp hx d) =
          (p.residueDegree x : ℤ) • v) →
      (W.cycleClass (ofOverField p hp) d).comp
          (zeroCycleToCodimensionOfExtension (ofOverField p hp) p rfl d) =
        (zmultiplesHom _ v).comp
          (chowDegree (fieldChowSituation k') (fieldChowSituation_dimensionFunction k') p s) := by
    intro v hv
    refine AddMonoidHom.ext fun α ↦ ?_
    refine AddSubgroup.closure_induction (p := fun α _ ↦ W.cycleClass (ofOverField p hp) d
        (zeroCycleToCodimensionOfExtension (ofOverField p hp) p rfl d α) =
      chowDegree (fieldChowSituation k') (fieldChowSituation_dimensionFunction k') p s α • v)
      ?_ ?_ ?_ ?_
      (mem_closure_separablePointClasses_of_isProjectiveMorphism k' p hp α)
    · rintro _ ⟨x, hx, hsx, rfl⟩
      rw [hgen x hx, hdegx x hx]
      exact hv x hx hsx
    · rw [map_zero, map_zero]
      exact ((congrArg (· • v) (map_zero (chowDegree (fieldChowSituation k')
        (fieldChowSituation_dimensionFunction k') p s))).trans (zero_smul ℤ v)).symm
    · intro a b _ _ ha hb
      rw [map_add, map_add, ha, hb, ← add_smul]
      exact congrArg (· • v) (map_add _ a b).symm
    · intro a _ ha
      rw [map_neg, map_neg, ha, ← neg_smul]
      exact congrArg (· • v) (map_neg _ a).symm
  by_cases hex : ∃ x : X, IsClosed ({x} : Set X) ∧ HasSeparableResidueField k' p x
  · obtain ⟨x₁, h₁, hs₁⟩ := hex
    have ha₁ : (p.residueDegree x₁ : F) ≠ 0 := Nat.cast_ne_zero.mpr
      (residueDegree_ne_zero_of_finite k' p x₁ (residueField_finite_of_closed_point k' p x₁ h₁))
    refine ⟨zmultiplesHom _ ((p.residueDegree x₁ : F)⁻¹ •
      W.cycleClass (ofOverField p hp) d (closedPointClass p hp h₁ d)), hfac _ ?_⟩
    intro x hx hsx
    have h := W.residueDegree_smul_cycleClass_closedPointClass hA hB hC p hp hr hx h₁ hsx hs₁
    simp only [← Int.cast_smul_eq_zsmul F, Int.cast_natCast] at h ⊢
    rw [smul_comm, ← h, inv_smul_smul₀ ha₁]
  · exact ⟨zmultiplesHom _ 0, hfac 0 fun x hx hsx ↦ (hex ⟨x, hx, hsx⟩).elim⟩

end WeilData

end Stacks.WeilCohomology
