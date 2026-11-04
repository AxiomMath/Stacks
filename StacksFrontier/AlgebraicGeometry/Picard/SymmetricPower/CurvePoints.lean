module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Geometry.HilbertSchemeGeometry
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents

/-!
# The Hilbert schemes of points of a smooth curve: affine opens and rational points

Let `X` be a smooth curve over a field `k`.

* Every finite family of points of `X` lies in an affine open (Stacks Tag 09NN); this is the
  hypothesis of Stacks Tag 0B9A for `X ⟶ Spec k`, in every degree.
* For a scheme `H` representing `Hilb^d_{X/k}`, the `k`-rational points of `H` are the effective
  Cartier divisors `D ⊆ X` which are finite locally free of rank `d` over `k`, that is, of
  degree `d` (Stacks Tag 0AYY reads the degree of an effective Cartier divisor on a proper curve
  as its degree over the base field). This is item 2 of the description of `Hilb^d` in the
  proof of Stacks Tag 0B9I.

## Main results

* `Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_isCurve`: finitely many points of a curve
  lie in a common affine open.
* `Stacks.Hilbert.hilbertHypothesis_of_isCurve`: the hypothesis of Tag 0B9A for a curve.
* `Stacks.Hilbert.rationalPointsEquivDivisors`: the `k`-points of a representing scheme are the
  effective Cartier divisors of degree `d` on `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Hilbert

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Finitely many points of a curve lie in a common affine open** (Stacks Tag 09NN). This is
the hypothesis of Stacks Tag 0B9A for a curve, in every degree. -/
theorem exists_isAffineOpen_forall_mem_of_isCurve [IsCurve k f] {ι : Type*} [Finite ι]
    (x : ι → X) : ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components X
    (fun U _ => ?_) x (fun _ => inferInstance) (fun i => ?_)
  · rcases isEmpty_or_nonempty U with hU | hU
    · exact Set.toFinite _
    · have : IrreducibleSpace U :=
        Subtype.irreducibleSpace (s := (U : Set X)) ⟨⟨hU.some.1, hU.some.2⟩,
          (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.isOpen
            (Set.subset_univ _)⟩
      rw [irreducibleComponents_eq_singleton]
      exact Set.finite_singleton _
  · rw [Ring.krullDimLE_iff]
    calc ringKrullDim (X.presheaf.stalk (x i)) ≤ topologicalKrullDim X := by
          rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
          exact le_iSup_of_le (x i) le_rfl
      _ = 1 := IsCurve.topologicalKrullDim_eq_one (f := f)

/-- **The hypothesis of Stacks Tag 0B9A holds for a curve**, in every degree. -/
theorem hilbertHypothesis_of_isCurve [IsCurve k f] (d : ℕ) :
    ∀ (s : Spec (.of k)) (x : Fin d → (Over.mk f).left), (∀ i, (Over.mk f).hom (x i) = s) →
      ∃ U : (Over.mk f).left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U :=
  fun _ x _ => exists_isAffineOpen_forall_mem_of_isCurve f x

/-- A curve is separated over its base field. -/
instance isSeparated_over_mk_of_isCurve [IsCurve k f] : IsSeparated (Over.mk f).hom :=
  inferInstanceAs (IsSeparated f)

/-! ### Rational points -/

/-- The isomorphism `X ≅ X ×_k k`, the inverse of the first projection. -/
def selfBaseChange : X ⟶ pullback f (𝟙 (Spec (.of k))) :=
  pullback.lift (𝟙 X) f (by simp)

/-- The morphism `selfBaseChange f : X ⟶ X ×_k k` is an isomorphism, whose inverse is the first
projection. -/
instance : IsIso (selfBaseChange f) := by
  refine ⟨⟨pullback.fst _ _, pullback.lift_fst _ _ _, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, selfBaseChange, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, selfBaseChange, pullback.lift_snd, Category.id_comp,
      ← Category.comp_id (pullback.snd f _), ← pullback.condition]

/-- Composing `selfBaseChange f` with the second projection `X ×_k k ⟶ Spec k` gives `f`. -/
theorem selfBaseChange_snd : selfBaseChange f ≫ pullback.snd f (𝟙 _) = f :=
  pullback.lift_snd _ _ _

/-- Finite local freeness of rank `d` of a closed subscheme transported along an isomorphism
of the ambient schemes over the base. -/
theorem isFiniteLocallyFreeOfRank_comap_iff {Y Y' B : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e]
    (p : Y ⟶ B) (I : Y.IdealSheafData) (d : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I.comap e).subschemeι ≫ e ≫ p) d ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ p) d := by
  have hsq := (AlgebraicGeometry.isPullback_of_isClosedImmersion (I.comap e).subschemeι
    I.subschemeι _ e (by rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc,
      Category.assoc, pullback.condition]) (by simp [Scheme.IdealSheafData.ker_subschemeι]))
  have : IsIso ((I.comapIso e).hom ≫ pullback.snd e I.subschemeι) := by
    have : IsIso (pullback.snd e I.subschemeι) := inferInstance
    infer_instance
  have hcomm : ((I.comapIso e).hom ≫ pullback.snd e I.subschemeι) ≫ I.subschemeι ≫ p =
      (I.comap e).subschemeι ≫ e ≫ p := by
    rw [Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
      ← Category.assoc, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc]
  rw [← hcomm]
  exact (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d).cancel_left_of_respectsIso _ _

/-- **The `k`-rational points of a scheme representing `Hilb^d_{X/k}`, for a smooth curve `X`,
are the effective Cartier divisors of `X` of degree `d`**, that is, finite locally free of rank
`d` over `k`. -/
def rationalPointsEquivDivisors [IsCurve k f] [Smooth f] {d : ℕ} {H : Over (Spec (.of k))}
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ H) ≃
      {D : X.IdealSheafData // Stacks.Divisors.IsEffectiveCartierDivisor D ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) d} :=
  hH.family.trans
    { toFun := fun Z =>
        ⟨Z.ideal.comap (selfBaseChange f), by
          have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve _ f
          have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
              ((Z.ideal.comap (selfBaseChange f)).subschemeι ≫ f) d := by
            have := (isFiniteLocallyFreeOfRank_comap_iff (selfBaseChange f) (pullback.snd f _)
              Z.ideal d).mpr Z.isFiniteLocallyFreeOfRank
            rwa [selfBaseChange_snd] at this
          have : Stacks.Morphisms.IsFiniteLocallyFree
              ((Z.ideal.comap (selfBaseChange f)).subschemeι ≫ f) :=
            @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d hrank
          exact ⟨(isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f _).1, hrank⟩⟩
      invFun := fun D =>
        ⟨D.1.comap (inv (selfBaseChange f)), by
          have := (isFiniteLocallyFreeOfRank_comap_iff (inv (selfBaseChange f)) f D.1 d).mpr D.2.2
          have e : inv (selfBaseChange f) ≫ f = pullback.snd f (𝟙 _) := by
            rw [IsIso.inv_comp_eq, selfBaseChange_snd]
          rw [e] at this
          exact this⟩
      left_inv := fun Z => HilbertFamily.ext (by
        change (Z.ideal.comap (selfBaseChange f)).comap (inv (selfBaseChange f)) = Z.ideal
        rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
          Scheme.IdealSheafData.comap_id])
      right_inv := fun D => Subtype.ext (by
        change (D.1.comap (inv (selfBaseChange f))).comap (selfBaseChange f) = D.1
        rw [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id,
          Scheme.IdealSheafData.comap_id]) }

end Stacks.Hilbert

end
