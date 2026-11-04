module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CofilteredLimit
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Descent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EqualityLocus
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HDescent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescent
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.BaseChange
public import StacksFrontier.RingTheory.FormallySmooth.Field

/-!
# Descending a family of cycles along a completely decomposed cover at a finite stage

Let `S = lim_{i ∈ I} S_i` be the limit of a cofiltered system of Noetherian schemes with affine
transition morphisms, let `X₀ ⟶ S_{i₀}` be of finite type and `X = X₀ ×_{S_{i₀}} S`, and let `α`
be a family of `r`-cycles on the fibres of `X/S`. Suppose that at a stage `i ≥ i₀` there are a
proper, completely decomposed `gᵢ : T ⟶ S_i` and a relative `r`-cycle `α'` on
`X_i ×_{S_i} T / T` whose base change to `S' = S ×_{S_i} T` is the base change `g^*α` of `α` along
`g : S' ⟶ S`. This file proves the last two paragraphs of the proofs of
[Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D) and
[Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W): at some later stage `j`, `α` is the base
change of a relative `r`-cycle `αⱼ` on `X_j/S_j`.

## Main results

* `AlgebraicGeometry.IsCompletelyDecomposed.hasSeparableResidueFieldPoints` — a completely
  decomposed morphism satisfies the hypothesis of Tag 0H4X (2).
* `AlgebraicGeometry.exists_forall_pullback_snd_mem_of_isLimit` — Limits, Lemma 05F4, for the
  base change of the system to a scheme over a stage and a closed subset with quasi-compact
  complement.
* `Stacks.Chow.baseChangeFamilyOfIsPullback_overlap_apply_eq` — the two pullbacks of `α'` to the
  overlap `T ×_{S_i} T` agree over the image of `S ×_{S_i} (T ×_{S_i} T)`, because
  `pr₁^*g^*α = pr₂^*g^*α`.
* `Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_stageLift` — if they agree over the
  image of a later stage, the base change of `α'` descends there (Lemmas 0H4X and 0H52).
* `Stacks.Chow.baseChangeFamily_eq_fiberCycleRestrict_of_stage` — the descended family base
  changes to `α`, by injectivity of base change along the completely decomposed `S' ⟶ S`.
* `Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_of_stage` — the assembled statement.

## Implementation notes

The overlap condition is a condition on the closed subset of `T ×_{S_i} T` where the two pullbacks
agree (Lemma 0H5C); it holds over the image of the limit, hence over the image of a later stage
by Limits, Lemma 05F4, applied to the base changed system `(S_j ×_{S_i} (T ×_{S_i} T))_{j ≥ i}`
of `AlgebraicGeometry.pullbackDiagram`.

Every family in the argument is a base change of `α`, of `α'` or of the descended family through
a cartesian square, and is handled with `Stacks.Chow.baseChangeFamilyOfIsPullback`: pasting
squares composes base changes (Tag 0H4P, part (1)), and two base changes through squares over the
same bottom edge agree as soon as the top edges agree, which is checked on components.

## References

* [Stacks Project, Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
* [Stacks Project, Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W)
* [Stacks Project, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Tag 0H52](https://stacks.math.columbia.edu/tag/0H52)
* [Stacks Project, Tag 0H5C](https://stacks.math.columbia.edu/tag/0H5C)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A completely decomposed morphism has a point with separable residue field extension over
every point of the target: an isomorphism of fields is a separable extension, being formally
smooth. -/
theorem IsCompletelyDecomposed.hasSeparableResidueFieldPoints {X Y : Scheme.{u}} {g : X ⟶ Y}
    (hg : IsCompletelyDecomposed g) : Stacks.Chow.HasSeparableResidueFieldPoints g := by
  intro y
  obtain ⟨x, hx, hiso⟩ := hg y
  refine ⟨x, hx, ?_⟩
  let : Algebra (Y.residueField (g x)) (X.residueField x) := (g.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (g x)) (X.residueField x)) :=
    (ConcreteCategory.isIso_iff_bijective (g.residueFieldMap x)).mp hiso
  let e := AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (g x)) (X.residueField x)) hbij
  have : Algebra.FormallySmooth (Y.residueField (g x)) (X.residueField x) :=
    Algebra.FormallySmooth.of_equiv e
  exact Algebra.FormallySmooth.isSeparableExtension _ _

/-- If a closed subset of a stage of a cofiltered system with affine transition morphisms, base
changed to a scheme `T` over that stage, contains the image of `(lim S_j) ×_{S_i} T`, then it
contains the image of `S_j ×_{S_i} T` for some later stage `j`, as soon as its complement is
quasi-compact. -/
theorem exists_forall_pullback_snd_mem_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] (c : Cone D)
    (hc : IsLimit c) {i : I} {T : Scheme.{u}} (h : T ⟶ D.obj i) (E : Set T) (hE : IsClosed E)
    (hEc : IsCompact Eᶜ) (H : ∀ y : (pullback (c.π.app i) h : Scheme.{u}),
      pullback.snd (c.π.app i) h y ∈ E) :
    ∃ (j : I) (v : j ⟶ i), ∀ y : (pullback (D.map v) h : Scheme.{u}),
      pullback.snd (D.map v) h y ∈ E := by
  let D' := pullbackDiagram D i h
  let c' := pullbackCone D c i h
  have : ∀ {j k : Over i} (q : j ⟶ k), IsAffineHom (D'.map q) := by
    intro j k q
    have hq : IsAffineHom ((Over.post D).map q).left := by
      change IsAffineHom (D.map q.left)
      infer_instance
    exact MorphismProperty.overPullbackMap (P := @IsAffineHom.{u}) h ((Over.post D).map q) hq
  let k₀ : Over i := Over.mk (𝟙 i)
  let U : (D'.obj k₀).Opens := (pullback.snd (D.map (𝟙 i)) h) ⁻¹ᵁ ⟨Eᶜ, hE.isOpen_compl⟩
  have hU : IsCompact (U : Set (D'.obj k₀)) :=
    QuasiCompact.isCompact_preimage (f := pullback.snd (D.map (𝟙 i)) h) _
      hE.isOpen_compl hEc
  obtain ⟨j, fj, hj⟩ := exists_map_preimage_le_map_preimage D' c' (isLimitPullbackCone D c hc i h)
    (V := ⊥) hU (by
    intro y hy
    exfalso
    have hmap : c'.π.app k₀ ≫ pullback.snd (D.map (𝟙 i)) h = pullback.snd (c.π.app i) h :=
      pullback.lift_snd _ _ _
    change (c'.π.app k₀ ≫ pullback.snd (D.map (𝟙 i)) h) y ∈ Eᶜ at hy
    rw [hmap] at hy
    exact hy (H y))
  refine ⟨j.left, j.hom, fun y => ?_⟩
  by_contra hy
  have hmap : D'.map fj ≫ pullback.snd (D.map (𝟙 i)) h = pullback.snd (D.map j.hom) h :=
    pullback.lift_snd _ _ _
  have : y ∈ D'.map fj ⁻¹ᵁ U := by
    change (D'.map fj ≫ pullback.snd (D.map (𝟙 i)) h) y ∈ Eᶜ
    rw [hmap]
    exact hy
  exact (hj this : y ∈ (⊥ : (D'.obj j).Opens))

end AlgebraicGeometry

namespace Stacks.Chow

/-- Base change through a square only depends on the top edge and the bottom edge as morphisms. -/
theorem baseChangeFamilyOfIsPullback_congr {X S T P : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {g g' : T ⟶ S} {a a' : P ⟶ X} {p : P ⟶ T}
    (sq : IsPullback a p f g) (sq' : IsPullback a' p f g') [LocallyOfFiniteType p] (ha : a = a')
    (hg : g = g') (r : ℕ)
    (α : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback f sq r α = baseChangeFamilyOfIsPullback f sq' r α := by
  subst ha hg
  rfl

/-- A cartesian square stays cartesian after precomposing its top and left edges with an
isomorphism. -/
theorem _root_.CategoryTheory.IsPullback.of_isIso_comp {X S T P P' : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T} (sq : IsPullback a p f g) (ψ : P' ⟶ P) [IsIso ψ]
    {p' : P' ⟶ T} (hψ : ψ ≫ p = p') : IsPullback (ψ ≫ a) p' f g :=
  IsPullback.of_iso sq (asIso ψ).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simp [← hψ]) (by simp) (by simp)

/-- The isomorphism of fibres `Stacks.Chow.overlapFiberComparison` is the restriction to the
fibres of `Stacks.Chow.overlapComparison`. -/
theorem overlapFiberComparison_hom_eq_fiberRestrict {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (t : (pullback g g : Scheme.{u})) :
    (overlapFiberComparison f g t).hom =
      fiberRestrict (pullback.snd (pullback.snd f g) (pullback.snd g g))
        (pullback.snd (pullback.snd f g) (pullback.fst g g)) (overlapComparison f g).hom
        (overlapComparison_hom_snd f g) t := by
  refine pullback.hom_ext
    (?_ : _ ≫ (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberι t =
      _ ≫ (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberι t)
    (?_ : _ ≫ (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberToSpecResidueField t =
      _ ≫ (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberToSpecResidueField t)
  · rw [overlapFiberComparison_hom_fiberι, fiberRestrict_fiberι]
  · rw [overlapFiberComparison_hom_snd, fiberRestrict_fiberToSpecResidueField]

/-- Pasting the pullback of `b` along `ρ` onto a cartesian square over `q`, then factoring the
bottom edge through a second cartesian square over the same right edge `f`, gives a cartesian
square over `σ`. -/
private theorem isPullback_lift_paste {P P' X Y Y' Z R : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {q : Y ⟶ Z} {a' : P' ⟶ X} {b' : P' ⟶ Y'} {g' : Y' ⟶ Z} (sq : IsPullback a b f q)
    (t : IsPullback a' b' f g') (ρ : R ⟶ Y) (σ : R ⟶ Y') (h : ρ ≫ q = σ ≫ g') :
    IsPullback (t.lift (pullback.fst b ρ ≫ a) (pullback.snd b ρ ≫ σ) (by
      rw [Category.assoc, sq.w, ← Category.assoc, pullback.condition, Category.assoc, h,
        Category.assoc])) (pullback.snd b ρ) b' σ := by
  have big := (IsPullback.of_hasPullback b ρ).paste_horiz sq
  rw [h] at big
  exact IsPullback.of_right' big t

/-- Two successive base changes through `sq` and the pullback of its left edge along `ρ` are the
base change through `t` followed by the base change through the pasted square over `σ`. -/
private theorem baseChangeFamilyOfIsPullback_lift_paste {P P' X Y Y' Z R : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {q : Y ⟶ Z} {a' : P' ⟶ X} {b' : P' ⟶ Y'} {g' : Y' ⟶ Z}
    [LocallyOfFiniteType f] [LocallyOfFiniteType b] [LocallyOfFiniteType b']
    (sq : IsPullback a b f q) (t : IsPullback a' b' f g') (ρ : R ⟶ Y) (σ : R ⟶ Y')
    (h : ρ ≫ q = σ ≫ g') (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamilyOfIsPullback b (IsPullback.of_hasPullback b ρ) r
        (baseChangeFamilyOfIsPullback f sq r α) =
      baseChangeFamilyOfIsPullback b' (isPullback_lift_paste sq t ρ σ h) r
        (baseChangeFamilyOfIsPullback f t r α) := by
  rw [baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback,
    baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
  exact baseChangeFamilyOfIsPullback_congr f _ _ (t.lift_fst _ _ _).symm h r α

/-- The pullback of `f` along the composite `g₁ ≫ g₂ = s` maps to the pullback of `f` along `g₂`,
cartesianly over `g₁`. -/
private theorem exists_isPullback_pullback_snd_comp {X B C A : Scheme.{u}} (f : X ⟶ C) (g₂ : B ⟶ C)
    (g₁ : A ⟶ B) (s : A ⟶ C) (hs : g₁ ≫ g₂ = s) :
    ∃ θ : pullback f s ⟶ pullback f g₂, IsPullback θ (pullback.snd f s) (pullback.snd f g₂) g₁ ∧
      θ ≫ pullback.fst f g₂ = pullback.fst f s := by
  subst hs
  refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g₁) (by
    rw [pullback.condition, Category.assoc]), ?_, pullback.lift_fst _ _ _⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback _ _

/-! ### The overlap condition over the limit -/

section Overlap

variable {S₁ T X₁ S X : Scheme.{u}} (fi : X₁ ⟶ S₁) [LocallyOfFiniteType fi] (gᵢ : T ⟶ S₁)
  (π : S ⟶ S₁) (fX : X ⟶ S) [LocallyOfFiniteType fX] (θ : X ⟶ X₁) (r : ℕ)
  (α : FamilyOfCycles fX r) (α' : FamilyOfCycles (pullback.snd fi gᵢ) r)
  (Φ : pullback (pullback.snd fi gᵢ) (pullback.snd π gᵢ) ⟶ pullback fX (pullback.fst π gᵢ))
  [IsIso Φ] (hΦ₂ : Φ ≫ pullback.snd fX (pullback.fst π gᵢ) =
    pullback.snd (pullback.snd fi gᵢ) (pullback.snd π gᵢ))
  (hΦθ : Φ ≫ pullback.fst fX (pullback.fst π gᵢ) ≫ θ =
    pullback.fst (pullback.snd fi gᵢ) (pullback.snd π gᵢ) ≫ pullback.fst fi gᵢ)
  (h : baseChangeFamily (pullback.snd fi gᵢ) (pullback.snd π gᵢ) r α' =
    baseChangeFamilyOfIsPullback fX ((IsPullback.of_hasPullback fX _).of_isIso_comp Φ hΦ₂) r α)

include hΦθ h in
/-- One of the two pullbacks of `α'` to the overlap `T ×_{S₁} T`, given through a square `sq`
over a morphism `q : T ×_{S₁} T ⟶ T` with `q ≫ gᵢ = pr₁ ≫ gᵢ`, base changed to
`S ×_{S₁} (T ×_{S₁} T)`, is the base change of `α` through a square whose top edge is
determined by its composite with `θ`. -/
theorem exists_baseChangeFamilyOfIsPullback_overlap_eq
    {a : pullback (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ) ⟶ pullback fi gᵢ}
    {q : pullback gᵢ gᵢ ⟶ T}
    (sq : IsPullback a (pullback.snd (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ))
      (pullback.snd fi gᵢ) q) (hq : q ≫ gᵢ = pullback.fst gᵢ gᵢ ≫ gᵢ) :
    ∃ (A : pullback (pullback.snd (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ))
          (pullback.snd π (pullback.fst gᵢ gᵢ ≫ gᵢ)) ⟶ X)
      (sqA : IsPullback A (pullback.snd _ (pullback.snd π (pullback.fst gᵢ gᵢ ≫ gᵢ))) fX
        (pullback.fst π (pullback.fst gᵢ gᵢ ≫ gᵢ))),
      A ≫ θ = pullback.fst _ _ ≫ a ≫ pullback.fst fi gᵢ ∧
      baseChangeFamilyOfIsPullback (pullback.snd (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ))
          (IsPullback.of_hasPullback _ (pullback.snd π (pullback.fst gᵢ gᵢ ≫ gᵢ))) r
          (baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ) sq r α') =
        baseChangeFamilyOfIsPullback fX sqA r α := by
  let ρ := pullback.snd π (pullback.fst gᵢ gᵢ ≫ gᵢ)
  let σ : pullback π (pullback.fst gᵢ gᵢ ≫ gᵢ) ⟶ pullback π gᵢ :=
    pullback.lift (pullback.fst _ _) (ρ ≫ q) (by
      rw [Category.assoc, hq]
      exact pullback.condition)
  have hσρ : ρ ≫ q = σ ≫ pullback.snd π gᵢ := (pullback.lift_snd _ _ _).symm
  have sqτ := IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.snd π gᵢ)
  have sqσ := isPullback_lift_paste sq sqτ ρ σ hσρ
  let sqΦ := (IsPullback.of_hasPullback fX (pullback.fst π gᵢ)).of_isIso_comp Φ hΦ₂
  have hσg : σ ≫ pullback.fst π gᵢ = pullback.fst π (pullback.fst gᵢ gᵢ ≫ gᵢ) :=
    pullback.lift_fst _ _ _
  have sqA := sqσ.paste_horiz sqΦ
  rw [hσg] at sqA
  refine ⟨_, sqA, ?_, ?_⟩
  · simp only [Category.assoc, hΦθ, IsPullback.lift_fst_assoc]
    rfl
  · rw [baseChangeFamilyOfIsPullback_lift_paste sq sqτ ρ σ hσρ r α',
      baseChangeFamilyOfIsPullback_of_hasPullback, h,
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
    exact baseChangeFamilyOfIsPullback_congr fX (sqσ.paste_horiz sqΦ) sqA rfl hσg r α

include hΦθ h in
/-- **The overlap condition holds over the limit.** The two pullbacks of `α'` to the overlap
`T ×_{S₁} T`, compared through `Stacks.Chow.overlapComparison`, agree at every point in the image
of `S ×_{S₁} (T ×_{S₁} T)`: both base change to that scheme as base changes of `α`, through two
squares with the same top edge. -/
theorem baseChangeFamilyOfIsPullback_overlap_apply_eq (sqθ : IsPullback θ fX fi π)
    (z : (pullback π (pullback.fst gᵢ gᵢ ≫ gᵢ) : Scheme.{u})) :
    baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
        (IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ)) r α'
        (pullback.snd π (pullback.fst gᵢ gᵢ ≫ gᵢ) z) =
      baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
        ((IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.snd gᵢ gᵢ)).of_isIso_comp
          (overlapComparison fi gᵢ).hom (overlapComparison_hom_snd fi gᵢ)) r α'
        (pullback.snd π (pullback.fst gᵢ gᵢ ≫ gᵢ) z) := by
  obtain ⟨A₁, sqA₁, hA₁, e₁⟩ := exists_baseChangeFamilyOfIsPullback_overlap_eq fi gᵢ π fX θ r α α'
    Φ hΦ₂ hΦθ h (IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ)) rfl
  obtain ⟨A₂, sqA₂, hA₂, e₂⟩ := exists_baseChangeFamilyOfIsPullback_overlap_eq fi gᵢ π fX θ r α α'
    Φ hΦ₂ hΦθ h ((IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.snd gᵢ gᵢ)).of_isIso_comp
      (overlapComparison fi gᵢ).hom (overlapComparison_hom_snd fi gᵢ))
    pullback.condition.symm
  have hA : A₁ = A₂ := by
    refine sqθ.hom_ext ?_ ?_
    · rw [hA₁, hA₂, Category.assoc, overlapComparison_hom_fst_fst]
    · rw [sqA₁.w, sqA₂.w]
  have heq := e₁.trans ((baseChangeFamilyOfIsPullback_congr fX sqA₁ sqA₂ hA rfl r α).trans e₂.symm)
  exact (baseChangeFamilyOfIsPullback_eq_iff _ _ r _ _).mp heq z

end Overlap

/-! ### Descent to a later stage -/

section Stage

variable {S₁ T X₁ S₂ X₂ T₂ : Scheme.{u}} (fi : X₁ ⟶ S₁) (gᵢ : T ⟶ S₁) (w : S₂ ⟶ S₁)
  (fj : X₂ ⟶ S₂) (ψ : X₂ ⟶ X₁) (κ : T₂ ⟶ T) (g₂ : T₂ ⟶ S₂)

/-- The morphism `X₂ ×_{S₂} T₂ ⟶ X₁ ×_{S₁} T` induced by `ψ : X₂ ⟶ X₁` and `κ : T₂ ⟶ T` over
`w : S₂ ⟶ S₁`. -/
def stageLift (hT : κ ≫ gᵢ = g₂ ≫ w) (hψ : ψ ≫ fi = fj ≫ w) :
    pullback fj g₂ ⟶ pullback fi gᵢ :=
  pullback.lift (pullback.fst _ _ ≫ ψ) (pullback.snd _ _ ≫ κ) (by
    rw [Category.assoc, hψ, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, hT])

/-- The composite of `stageLift` with the projection to `X₁` is the projection to `X₂` followed
by `ψ`. -/
@[reassoc (attr := simp)]
theorem stageLift_fst (hT : κ ≫ gᵢ = g₂ ≫ w) (hψ : ψ ≫ fi = fj ≫ w) :
    stageLift fi gᵢ w fj ψ κ g₂ hT hψ ≫ pullback.fst fi gᵢ = pullback.fst _ _ ≫ ψ :=
  pullback.lift_fst _ _ _

/-- The composite of `stageLift` with the projection to `T` is the projection to `T₂` followed
by `κ`. -/
@[reassoc (attr := simp)]
theorem stageLift_snd (hT : κ ≫ gᵢ = g₂ ≫ w) (hψ : ψ ≫ fi = fj ≫ w) :
    stageLift fi gᵢ w fj ψ κ g₂ hT hψ ≫ pullback.snd fi gᵢ = pullback.snd _ _ ≫ κ :=
  pullback.lift_snd _ _ _

/-- If `X₂ = X₁ ×_{S₁} S₂` and `T₂ = T ×_{S₁} S₂`, then `X₂ ×_{S₂} T₂ = (X₁ ×_{S₁} T) ×_T T₂`. -/
theorem isPullback_stageLift (sqT : IsPullback κ g₂ gᵢ w) (sqψ : IsPullback ψ fj fi w) :
    IsPullback (stageLift fi gᵢ w fj ψ κ g₂ sqT.w sqψ.w) (pullback.snd fj g₂)
      (pullback.snd fi gᵢ) κ := by
  refine IsPullback.of_right ?_ (stageLift_snd fi gᵢ w fj ψ κ g₂ sqT.w sqψ.w)
    (IsPullback.of_hasPullback fi gᵢ)
  rw [stageLift_fst, sqT.w]
  exact (IsPullback.of_hasPullback fj g₂).paste_horiz sqψ

/-- **Descent along the base change of the cover to a later stage.** Let `S₁` be locally
Noetherian, `fi : X₁ ⟶ S₁` locally of finite type, `gᵢ : T ⟶ S₁` proper and completely decomposed,
and `α' ∈ z(X₁ ×_{S₁} T / T, r)`. Let `w : S₂ ⟶ S₁` with `S₂` locally Noetherian and
`X₂ = X₁ ×_{S₁} S₂`. If the two pullbacks of `α'` to `T ×_{S₁} T` agree over the image of
`S₂ ×_{S₁} (T ×_{S₁} T)`, then the base change of `α'` to `T₂ = T ×_{S₁} S₂` descends to a
relative `r`-cycle on `X₂/S₂` (Lemmas 0H4X and 0H52). -/
theorem exists_relativeCycles_baseChangeFamily_eq_stageLift [IsLocallyNoetherian T]
    [IsLocallyNoetherian S₂] [LocallyOfFiniteType fi] [LocallyOfFiniteType fj] [IsProper gᵢ]
    (hgᵢ : IsCompletelyDecomposed gᵢ) (sqT : IsPullback κ g₂ gᵢ w) (sqψ : IsPullback ψ fj fi w)
    (r : ℕ)
    (α' : FamilyOfCycles (pullback.snd fi gᵢ) r)
    (hα' : α' ∈ relativeCycles (pullback.snd fi gᵢ) r)
    (himg : ∀ y : (pullback w (pullback.fst gᵢ gᵢ ≫ gᵢ) : Scheme.{u}),
      baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
          (IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ)) r α'
          (pullback.snd w (pullback.fst gᵢ gᵢ ≫ gᵢ) y) =
        baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
          ((IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.snd gᵢ gᵢ)).of_isIso_comp
            (overlapComparison fi gᵢ).hom (overlapComparison_hom_snd fi gᵢ)) r α'
          (pullback.snd w (pullback.fst gᵢ gᵢ ≫ gᵢ) y)) :
    ∃ α₂ : FamilyOfCycles fj r, α₂ ∈ relativeCycles fj r ∧
      baseChangeFamily fj g₂ r α₂ =
        baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
          (isPullback_stageLift fi gᵢ w fj ψ κ g₂ sqT sqψ) r α' := by
  have : IsProper g₂ := MorphismProperty.of_isPullback sqT ‹IsProper gᵢ›
  have : IsLocallyNoetherian T₂ := LocallyOfFiniteType.isLocallyNoetherian g₂
  have : IsLocallyNoetherian (pullback gᵢ gᵢ : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst gᵢ gᵢ)
  have hg₂ : IsCompletelyDecomposed g₂ := IsCompletelyDecomposed.of_isPullback sqT hgᵢ
  have : Surjective g₂ := hg₂.toSurjective
  let sqj := isPullback_stageLift fi gᵢ w fj ψ κ g₂ sqT sqψ
  let α'₂ := baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ) sqj r α'
  have hα'₂ : IsRelativeCycle (pullback.snd fj g₂) r α'₂ :=
    isRelativeCycle_baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ) sqj r hα'
  -- The comparison of the overlap of `T₂` with the overlap of `T`.
  let ρ₂ : pullback g₂ g₂ ⟶ pullback gᵢ gᵢ :=
    pullback.map g₂ g₂ gᵢ gᵢ κ κ w sqT.w.symm sqT.w.symm
  have hρ₁ : pullback.fst g₂ g₂ ≫ κ = ρ₂ ≫ pullback.fst gᵢ gᵢ := (pullback.lift_fst _ _ _).symm
  have hρ₂ : pullback.snd g₂ g₂ ≫ κ = ρ₂ ≫ pullback.snd gᵢ gᵢ := (pullback.lift_snd _ _ _).symm
  let sq₁ := IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ)
  let sq₂ := (IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.snd gᵢ gᵢ)).of_isIso_comp
    (overlapComparison fi gᵢ).hom (overlapComparison_hom_snd fi gᵢ)
  have sqρ := isPullback_lift_paste sqj sq₁ (pullback.fst g₂ g₂) ρ₂ hρ₁
  -- The first pullback of `α'₂` to the overlap.
  have e₁ : baseChangeFamily (pullback.snd fj g₂) (pullback.fst g₂ g₂) r α'₂ =
      baseChangeFamilyOfIsPullback (pullback.snd (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ)) sqρ r
        (baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ) sq₁ r α') := by
    rw [← baseChangeFamilyOfIsPullback_of_hasPullback (pullback.snd fj g₂) r α'₂,
      baseChangeFamilyOfIsPullback_lift_paste sqj sq₁ _ ρ₂ hρ₁]
  -- The second pullback, read through the overlap comparison.
  let Ω₂ := (overlapComparison fj g₂).hom
  let sqΩ₂ := (IsPullback.of_hasPullback (pullback.snd fj g₂) (pullback.snd g₂ g₂)).of_isIso_comp
    Ω₂ (overlapComparison_hom_snd fj g₂)
  have e₂ : (fun t => fiberCycleRestrict (pullback.snd (pullback.snd fj g₂) (pullback.snd g₂ g₂))
        (pullback.snd (pullback.snd fj g₂) (pullback.fst g₂ g₂)) Ω₂
        (overlapComparison_hom_snd fj g₂) t r
        (baseChangeFamily (pullback.snd fj g₂) (pullback.snd g₂ g₂) r α'₂ t)) =
      baseChangeFamilyOfIsPullback (pullback.snd (pullback.snd fi gᵢ) (pullback.fst gᵢ gᵢ)) sqρ r
        (baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ) sq₂ r α') := by
    rw [← baseChangeFamilyOfIsPullback_eq (pullback.snd fj g₂) sqΩ₂ r Ω₂ rfl
        (overlapComparison_hom_snd fj g₂) α'₂,
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback,
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
    refine baseChangeFamilyOfIsPullback_congr _ _ _ ?_ hρ₂ r α'
    have h₁ := reassoc_of% (overlapComparison_hom_fst_fst fj g₂)
    have h₂ := reassoc_of% (overlapComparison_hom_fst_fst fi gᵢ)
    have h₃ := reassoc_of% (overlapComparison_hom_snd fj g₂)
    have h₄ := reassoc_of% (overlapComparison_hom_snd fi gᵢ)
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, stageLift_fst, Ω₂, h₁, overlapComparison_hom_fst_fst,
        IsPullback.lift_fst_assoc]
    · simp only [Category.assoc, stageLift_snd, Ω₂]
      rw [pullback.condition_assoc (f := pullback.snd fj g₂) (g := pullback.snd g₂ g₂), h₃, hρ₂,
        pullback.condition (f := pullback.snd fi gᵢ) (g := pullback.snd gᵢ gᵢ), h₄,
        IsPullback.lift_snd_assoc]
      simp only [Category.assoc]
  -- The descent condition of Tag 0H4X (2).
  have hcond : ∀ (t : (pullback g₂ g₂ : Scheme.{u}))
      (x : (pullback.snd (pullback.snd fj g₂) (pullback.fst g₂ g₂)).fiber t),
      (baseChangeFamily (pullback.snd fj g₂) (pullback.fst g₂ g₂) r α'₂ t :
          AlgebraicCycle ((pullback.snd (pullback.snd fj g₂) (pullback.fst g₂ g₂)).fiber t) ℤ) x =
        (baseChangeFamily (pullback.snd fj g₂) (pullback.snd g₂ g₂) r α'₂ t :
            AlgebraicCycle ((pullback.snd (pullback.snd fj g₂) (pullback.snd g₂ g₂)).fiber t) ℤ)
          ((overlapFiberComparison fj g₂ t).hom x) := by
    intro t x
    have hfam : baseChangeFamily (pullback.snd fj g₂) (pullback.fst g₂ g₂) r α'₂ = _ :=
      e₁.trans (((baseChangeFamilyOfIsPullback_eq_iff _ sqρ r _ _).mpr fun t' => by
        have := himg (pullback.lift (pullback.fst g₂ g₂ ≫ g₂) ρ₂ (by
          rw [Category.assoc, ← sqT.w, ← Category.assoc, hρ₁,
            Category.assoc]) t')
        have hpt : pullback.snd w (pullback.fst gᵢ gᵢ ≫ gᵢ) (pullback.lift
            (pullback.fst g₂ g₂ ≫ g₂) ρ₂ (by
              rw [Category.assoc, ← sqT.w, ← Category.assoc, hρ₁,
                Category.assoc]) t') = ρ₂ t' := by
          rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
        rwa [hpt] at this).trans e₂.symm)
    have := congrArg (fun F : FamilyOfCycles _ r =>
      (F t : AlgebraicCycle ((pullback.snd (pullback.snd fj g₂) (pullback.fst g₂ g₂)).fiber t) ℤ)
        x) hfam
    simp only at this
    rw [this, fiberCycleRestrict_apply, overlapFiberComparison_hom_eq_fiberRestrict]
  obtain ⟨α₂, hα₂, -⟩ := existsUnique_familyOfCycles_baseChangeFamily_eq fj g₂
    hg₂.hasSeparableResidueFieldPoints r α'₂ hcond
  exact ⟨α₂, isRelativeCycle_of_isRelativeCycle_baseChangeFamily_of_isProper fj g₂ r α₂
    (by rwa [hα₂]), hα₂⟩

end Stage

section OverlapStage

variable {S₁ T X₁ S X : Scheme.{u}} (fi : X₁ ⟶ S₁) [LocallyOfFiniteType fi] (gᵢ : T ⟶ S₁)
  (π : S ⟶ S₁) (fX : X ⟶ S) [LocallyOfFiniteType fX] (θ : X ⟶ X₁) (r : ℕ)
  (α : FamilyOfCycles fX r) (α' : FamilyOfCycles (pullback.snd fi gᵢ) r)
  (Φ : pullback (pullback.snd fi gᵢ) (pullback.snd π gᵢ) ⟶ pullback fX (pullback.fst π gᵢ))
  [IsIso Φ] (hΦ₂ : Φ ≫ pullback.snd fX (pullback.fst π gᵢ) =
    pullback.snd (pullback.snd fi gᵢ) (pullback.snd π gᵢ))
  (hΦθ : Φ ≫ pullback.fst fX (pullback.fst π gᵢ) ≫ θ =
    pullback.fst (pullback.snd fi gᵢ) (pullback.snd π gᵢ) ≫ pullback.fst fi gᵢ)
  (h : baseChangeFamily (pullback.snd fi gᵢ) (pullback.snd π gᵢ) r α' =
    baseChangeFamilyOfIsPullback fX ((IsPullback.of_hasPullback fX _).of_isIso_comp Φ hΦ₂) r α)

include hΦθ h in
/-- **The descended family base changes to the given one.** In the situation of
`Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_stageLift`, let moreover `S ⟶ S₁` factor
as `π₂ ≫ w` and let `X = X₁ ×_{S₁} S` (through `θ`) be identified with `X₂ ×_{S₂} S` through an
isomorphism `LC` over `S` and `X₁`. If `α₂` on `X₂/S₂` pulls back to the base change of `α'` along
`T₂ ⟶ T`, then its base change to `S` is `α`, read through `LC`: both have the same base change
to `S' = S ×_{S₁} T`, along which base change is injective because `S' ⟶ S` is completely
decomposed. -/
theorem baseChangeFamily_eq_fiberCycleRestrict_of_stage (sqθ : IsPullback θ fX fi π) [IsProper gᵢ]
    (hgᵢ : IsCompletelyDecomposed gᵢ) {S₂ X₂ : Scheme.{u}} (w : S₂ ⟶ S₁) (fj : X₂ ⟶ S₂)
    [LocallyOfFiniteType fj] (ψ : X₂ ⟶ X₁) (sqψ : IsPullback ψ fj fi w) {T₂ : Scheme.{u}}
    (κ : T₂ ⟶ T) (g₂ : T₂ ⟶ S₂) (sqT : IsPullback κ g₂ gᵢ w) (π₂ : S ⟶ S₂)
    (hπ : π₂ ≫ w = π) (LC : pullback fj π₂ ⟶ X) [IsIso LC] (hLC₁ : LC ≫ fX = pullback.snd fj π₂)
    (hLC₂ : LC ≫ θ = pullback.fst fj π₂ ≫ ψ) (α₂ : FamilyOfCycles fj r)
    (hα₂ : baseChangeFamily fj g₂ r α₂ =
      baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
        (isPullback_stageLift fi gᵢ w fj ψ κ g₂ sqT sqψ) r α') :
    baseChangeFamily fj π₂ r α₂ = fun s => fiberCycleRestrict fX (pullback.snd fj π₂) LC hLC₁ s r
      (α s) := by
  have : Surjective (pullback.fst π gᵢ) :=
    (isCompletelyDecomposed_pullback_fst π gᵢ hgᵢ).toSurjective
  refine baseChangeFamily_injective (pullback.snd fj π₂) (pullback.fst π gᵢ) r _ _ ?_
  -- The left-hand side.
  let μ : pullback π gᵢ ⟶ T₂ :=
    sqT.lift (pullback.snd π gᵢ) (pullback.fst π gᵢ ≫ π₂) (by
      rw [Category.assoc, hπ, pullback.condition])
  have hμ₁ : μ ≫ κ = pullback.snd π gᵢ := sqT.lift_fst _ _ _
  have hμ₂ : pullback.fst π gᵢ ≫ π₂ = μ ≫ g₂ := (sqT.lift_snd _ _ _).symm
  have sqμ := isPullback_lift_paste (IsPullback.of_hasPullback fj π₂)
    (IsPullback.of_hasPullback fj g₂) (pullback.fst π gᵢ) μ hμ₂
  have big₂ := sqμ.paste_horiz (isPullback_stageLift fi gᵢ w fj ψ κ g₂ sqT sqψ)
  rw [hμ₁] at big₂
  let ψ' := big₂.isoPullback.hom
  have hψ' : ψ' ≫ pullback.snd (pullback.snd fi gᵢ) (pullback.snd π gᵢ) =
      pullback.snd (pullback.snd fj π₂) (pullback.fst π gᵢ) := big₂.isoPullback_hom_snd
  let sqΦ := (IsPullback.of_hasPullback fX (pullback.fst π gᵢ)).of_isIso_comp Φ hΦ₂
  have eL : baseChangeFamily (pullback.snd fj π₂) (pullback.fst π gᵢ) r
        (baseChangeFamily fj π₂ r α₂) =
      baseChangeFamilyOfIsPullback fX (sqΦ.of_isIso_comp ψ' hψ') r α := by
    rw [← baseChangeFamilyOfIsPullback_of_hasPullback fj r α₂,
      ← baseChangeFamilyOfIsPullback_of_hasPullback (pullback.snd fj π₂) r,
      baseChangeFamilyOfIsPullback_lift_paste (IsPullback.of_hasPullback fj π₂)
        (IsPullback.of_hasPullback fj g₂) _ μ hμ₂,
      baseChangeFamilyOfIsPullback_of_hasPullback fj r α₂, hα₂,
      baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback,
      baseChangeFamilyOfIsPullback_congr (pullback.snd fi gᵢ) _
        ((IsPullback.of_hasPullback (pullback.snd fi gᵢ) (pullback.snd π gᵢ)).of_isIso_comp ψ' hψ')
        big₂.isoPullback_hom_fst.symm hμ₁,
      ← fiberCycleRestrict_baseChangeFamilyOfIsPullback (pullback.snd fi gᵢ)
        (IsPullback.of_hasPullback _ _) r ψ' hψ',
      baseChangeFamilyOfIsPullback_of_hasPullback, h,
      fiberCycleRestrict_baseChangeFamilyOfIsPullback fX sqΦ r ψ' hψ']
  -- The right-hand side.
  let pR := pullbackRestrict fX (pullback.snd fj π₂) LC hLC₁ (pullback.fst π gᵢ)
  have hpR : pR ≫ pullback.snd fX (pullback.fst π gᵢ) =
      pullback.snd (pullback.snd fj π₂) (pullback.fst π gᵢ) :=
    pullbackRestrict_snd fX _ LC hLC₁ _
  have : IsIso pR := by
    dsimp only [pR, pullbackRestrict]
    infer_instance
  let sqR := (IsPullback.of_hasPullback fX (pullback.fst π gᵢ)).of_isIso_comp pR hpR
  have eR : baseChangeFamily (pullback.snd fj π₂) (pullback.fst π gᵢ) r
        (fun s => fiberCycleRestrict fX (pullback.snd fj π₂) LC hLC₁ s r (α s)) =
      baseChangeFamilyOfIsPullback fX sqR r α := by
    rw [baseChangeFamilyOfIsPullback_eq fX sqR r pR rfl hpR α]
    funext t
    exact baseChangeFamily_fiberCycleRestrict fX (pullback.snd fj π₂) LC hLC₁ _ r α t
  rw [eL, eR]
  refine baseChangeFamilyOfIsPullback_congr fX _ _ ?_ rfl r α
  refine sqθ.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hΦθ, ← Category.assoc ψ',
      big₂.isoPullback_hom_fst, Category.assoc, stageLift_fst, IsPullback.lift_fst_assoc]
    simp only [pR, Category.assoc, pullbackRestrict_fst_assoc, hLC₂]
  · rw [(sqΦ.of_isIso_comp ψ' hψ').w, sqR.w]

end OverlapStage


/-! ### The descent at a finite stage -/

/-- **Descending a family of cycles to a finite stage.** Let `S = lim S_i` be the limit of a
cofiltered system of Noetherian schemes with affine transition morphisms, let `f₀ : X₀ ⟶ S_{i₀}`
be of finite type and let `α` be a family of `r`-cycles on the fibres of `X = X₀ ×_{S_{i₀}} S`
over `S`. Let `u : i ⟶ i₀`, let `gᵢ : T ⟶ S_i` be proper and completely decomposed with `T`
Noetherian, and let `α'` be a relative `r`-cycle on `X_i ×_{S_i} T / T` whose base change to
`S' = S ×_{S_i} T` is `g^*α`, read through the canonical isomorphism `Φ` (pinned down by `hΦ₁` and
`hΦ₂`). Then for some `v : j ⟶ i` there is a relative `r`-cycle `αⱼ` on `X_j/S_j` whose base
change to `S` is `α`, read through `AlgebraicGeometry.limitComparison`. -/
theorem exists_relativeCycles_baseChangeFamily_eq_of_stage {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, IsNoetherian (D.obj i)] (c : Cone D) (hc : IsLimit c) {i₀ : I} {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ D.obj i₀) [LocallyOfFiniteType f₀] [QuasiCompact f₀] (r : ℕ)
    (α : FamilyOfCycles (pullback.snd f₀ (c.π.app i₀)) r) {i : I} (u : i ⟶ i₀) {T : Scheme.{u}}
    (gᵢ : T ⟶ D.obj i) [IsProper gᵢ] (hgᵢ : IsCompletelyDecomposed gᵢ) [IsNoetherian T]
    (α' : FamilyOfCycles (pullback.snd (pullback.snd f₀ (D.map u)) gᵢ) r)
    (hα' : α' ∈ relativeCycles (pullback.snd (pullback.snd f₀ (D.map u)) gᵢ) r)
    (Φ : pullback (pullback.snd (pullback.snd f₀ (D.map u)) gᵢ) (pullback.snd (c.π.app i) gᵢ) ⟶
      pullback (pullback.snd f₀ (c.π.app i₀)) (pullback.fst (c.π.app i) gᵢ)) [IsIso Φ]
    (hΦ₁ : Φ ≫ pullback.fst _ _ ≫ pullback.fst f₀ (c.π.app i₀) =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst f₀ (D.map u))
    (hΦ₂ : Φ ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : baseChangeFamily (pullback.snd (pullback.snd f₀ (D.map u)) gᵢ)
        (pullback.snd (c.π.app i) gᵢ) r α' = fun t =>
      fiberCycleRestrict (pullback.snd (pullback.snd f₀ (c.π.app i₀)) (pullback.fst (c.π.app i) gᵢ))
        (pullback.snd (pullback.snd (pullback.snd f₀ (D.map u)) gᵢ) (pullback.snd (c.π.app i) gᵢ))
        Φ hΦ₂ t r (baseChangeFamily (pullback.snd f₀ (c.π.app i₀)) (pullback.fst (c.π.app i) gᵢ)
          r α t)) :
    ∃ (j : I) (v : j ⟶ i) (αⱼ : FamilyOfCycles (pullback.snd f₀ (D.map (v ≫ u))) r),
      αⱼ ∈ relativeCycles (pullback.snd f₀ (D.map (v ≫ u))) r ∧
      baseChangeFamily (pullback.snd f₀ (D.map (v ≫ u))) (c.π.app j) r αⱼ = fun s =>
        fiberCycleRestrict (pullback.snd f₀ (c.π.app i₀))
          (pullback.snd (pullback.snd f₀ (D.map (v ≫ u))) (c.π.app j))
          (limitComparison D c (v ≫ u) f₀) (limitComparison_snd D c (v ≫ u) f₀) s r (α s) := by
  -- `X = X_i ×_{S_i} S`.
  obtain ⟨θ, sqθ, hθ⟩ := exists_isPullback_pullback_snd_comp f₀ (D.map u) (c.π.app i)
    (c.π.app i₀) (c.w u)
  have hΦθ : Φ ≫ pullback.fst _ _ ≫ θ = pullback.fst _ _ ≫ pullback.fst _ gᵢ := by
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, hθ] using hΦ₁
    · simp only [Category.assoc, sqθ.w]
      rw [pullback.condition_assoc, reassoc_of% hΦ₂,
        pullback.condition (f := pullback.snd f₀ (D.map u)) (g := gᵢ),
        pullback.condition_assoc (f := pullback.snd (pullback.snd f₀ (D.map u)) gᵢ)
          (g := pullback.snd (c.π.app i) gᵢ),
        ← pullback.condition (f := c.π.app i) (g := gᵢ)]
  have h' : baseChangeFamily (pullback.snd (pullback.snd f₀ (D.map u)) gᵢ)
      (pullback.snd (c.π.app i) gᵢ) r α' =
      baseChangeFamilyOfIsPullback (pullback.snd f₀ (c.π.app i₀))
        ((IsPullback.of_hasPullback _ _).of_isIso_comp Φ hΦ₂) r α := by
    rw [h, baseChangeFamilyOfIsPullback_eq _ _ r Φ rfl hΦ₂]
  -- The overlap condition holds over the limit, hence over a later stage.
  have : IsNoetherian (pullback gᵢ gᵢ : Scheme.{u}) :=
    isNoetherian_of_locallyOfFiniteType (pullback.fst gᵢ gᵢ)
  have hγ₁ := isRelativeCycle_baseChangeFamilyOfIsPullback (pullback.snd (pullback.snd f₀
    (D.map u)) gᵢ) (IsPullback.of_hasPullback _ (pullback.fst gᵢ gᵢ)) r hα'
  have hγ₂ := isRelativeCycle_baseChangeFamilyOfIsPullback (pullback.snd (pullback.snd f₀
    (D.map u)) gᵢ) ((IsPullback.of_hasPullback _ (pullback.snd gᵢ gᵢ)).of_isIso_comp
      (overlapComparison _ gᵢ).hom (overlapComparison_hom_snd _ gᵢ)) r hα'
  have hE := isClosed_setOf_fiberCycle_eq _ ⟨_, hγ₁⟩ ⟨_, hγ₂⟩
  obtain ⟨j, v, hj⟩ := exists_forall_pullback_snd_mem_of_isLimit D c hc
    (pullback.fst gᵢ gᵢ ≫ gᵢ) _ hE (TopologicalSpace.NoetherianSpace.isCompact _)
    (baseChangeFamilyOfIsPullback_overlap_apply_eq _ gᵢ (c.π.app i) _ θ r α α' Φ hΦ₂ hΦθ h' sqθ)
  -- The stage `j`.
  obtain ⟨ψ, sqψ, hψ⟩ := exists_isPullback_pullback_snd_comp f₀ (D.map u) (D.map v)
    (D.map (v ≫ u)) (D.map_comp v u).symm
  obtain ⟨αⱼ, hαⱼ, hbase⟩ := exists_relativeCycles_baseChangeFamily_eq_stageLift
    (pullback.snd f₀ (D.map u)) gᵢ (D.map v) (pullback.snd f₀ (D.map (v ≫ u))) ψ
    (pullback.fst gᵢ (D.map v)) (pullback.snd gᵢ (D.map v)) hgᵢ
    (IsPullback.of_hasPullback gᵢ (D.map v)) sqψ r α' hα' hj
  refine ⟨j, v, αⱼ, hαⱼ, ?_⟩
  refine baseChangeFamily_eq_fiberCycleRestrict_of_stage _ gᵢ (c.π.app i) _ θ r α α' Φ hΦ₂ hΦθ
    h' sqθ hgᵢ (D.map v) _ ψ sqψ (pullback.fst gᵢ (D.map v)) (pullback.snd gᵢ (D.map v))
    (IsPullback.of_hasPullback gᵢ (D.map v)) (c.π.app j) (c.w v)
    (limitComparison D c (v ≫ u) f₀) _ ?_ αⱼ hbase
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, hθ, hψ, limitComparison_fst]
  · simp only [Category.assoc, sqθ.w, sqψ.w, limitComparison_snd_assoc]
    rw [pullback.condition_assoc, c.w v]

end Stacks.Chow

end
