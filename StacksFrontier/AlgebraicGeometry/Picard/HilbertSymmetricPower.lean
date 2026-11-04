module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.FibrePowerPermutation
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormGroupProductHint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.RankComp
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The morphism `π : Xⁿ ⟶ Sⁿ(X)` of Stacks 0FH9

Let `X ⟶ S` be separated and smooth of relative dimension one, and let `H d` represent the
Hilbert functor of points `Hilb^d_{X/S}` for every `d`. Stacks 0FH9 writes
`Sⁿ(X) = Hilb^n_{X/S}` and uses the canonical morphism

  `π : Xⁿ ⟶ Sⁿ(X)`,   `(x₁, …, xₙ) ↦ [x₁] + ⋯ + [xₙ]`,

asserting that it is `Sₙ`-invariant and finite flat of degree `n!`, and that `Sₙ` acts faithfully
on `Xⁿ`. This file constructs `π` and proves those properties, together with the integrality of
`Xⁿ` that the norm computation of the source needs, and assembles them into the computation
`π^*(Norm_π ℒ₁) = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}` for this `π`.

## Main definitions

* `Stacks.Hilbert.familyOfPoints` — the family `[x₁] + ⋯ + [xₙ]` of `n` relative points.
* `Stacks.Hilbert.symmetricPowerMap` — the morphism `π : Xⁿ ⟶ H n` classifying
  `Σᵢ Γ_{prᵢ}`.
* `Stacks.Scheme.fibrePowerSuccIso` — `X^{n+1} ≅ Xⁿ ×_S X`.

## Main results

* `Stacks.Hilbert.family_comp_symmetricPowerMap` — the family classified by `g ≫ π` is
  `Σᵢ Γ_{g ≫ prᵢ}`, i.e. `π` sends `(x₁, …, xₙ)` to `[x₁] + ⋯ + [xₙ]`.
* `Stacks.Hilbert.symmetricPowerMap_succ` — `π_{n+1}` is `π_n × id` followed by point addition.
* `Stacks.Hilbert.isFiniteLocallyFreeOfRank_symmetricPowerMap` — `π` is finite locally free of
  rank `n!`, and `Stacks.Hilbert.isFinite_symmetricPowerMap` — `π` is finite.
* `Stacks.Hilbert.fibrePowerPerm_comp_symmetricPowerMap` — `π` is `Sₙ`-invariant.
* `Stacks.Scheme.isIntegral_fibrePower` — `Xⁿ` is integral for `X` smooth and geometrically
  irreducible over a field.
* `Stacks.Scheme.exists_ne_sections_of_isAlgClosed` and
  `Stacks.Scheme.fibrePowerPerm_left_injective_of_isAlgClosed` — a nonempty smooth curve over
  an algebraically closed field has two distinct rational points, so `Sₙ` acts faithfully.
* `Stacks.SheafOfModules.pullbackPicardClass_normInvertible_symmetricPowerMap` — the formula
  `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]` in `Pic(Xⁿ)` for this `π`, with no hypothesis left
  on `π`.

## Implementation notes

*The representing schemes are parameters.* As in Stacks 0B9H, the statements take
`H : ℕ → Over S` together with `RepresentsHilbertFunctorOfRank X (H d) d` for every `d`; nothing
is chosen, and the results hold for every such family.

*How `π` is defined.* `π` is the morphism classifying `familyOfPoints` of the projections, so its
characterization is a computation with the naturality of the universal family. The degree is
proved by induction from Stacks 0B9G: `π_{n+1}` factors as the isomorphism
`X^{n+1} ≅ Xⁿ ×_S X`, the base change `π_n × id` of `π_n` (degree `n!`), and point addition
`H n ×_S X ⟶ H (n+1)` (degree `n + 1`), and ranks multiply in a composition.

*Geometric integrality.* For integrality of `Xⁿ` the curve is assumed smooth and geometrically
irreducible; geometric reducedness comes from smoothness. Then `Xⁿ ⟶ S` is smooth, hence `Xⁿ`
is reduced, and `Xⁿ` is irreducible by induction since `X ⟶ Spec k` is geometrically
irreducible and universally open.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
* [Stacks Project, Tag 0B9H](https://stacks.math.columbia.edu/tag/0B9H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Scheme Nat

universe u

namespace Stacks.IdealSheaf

/-- **The inverse image of ideal sheaves commutes with finite products**, the empty product being
the unit ideal. -/
theorem comap_prod {Y Z : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → Z.IdealSheafData) (f : Y ⟶ Z) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f :=
  map_prod ({ toFun := fun J : Z.IdealSheafData => J.comap f
              map_one' := Scheme.IdealSheafData.comap_top f
              map_mul' := fun J K => comap_mul J K f } :
    Z.IdealSheafData →* Y.IdealSheafData) I s

end Stacks.IdealSheaf

namespace Stacks.Scheme

variable {S : Scheme.{u}} (X : Over S)

/-- **Splitting off a factor of the fibre power.** `X^{n+1} ≅ Xⁿ ×_S X`, the first component
being the last `n` coordinates and the second component the coordinate `0`. -/
def fibrePowerSuccIso (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => X) ≅ (∏ᶜ fun _ : Fin n => X) ⨯ X where
  hom := prod.lift (Pi.lift fun i => Pi.π (fun _ : Fin (n + 1) => X) i.succ)
    (Pi.π (fun _ : Fin (n + 1) => X) 0)
  inv := Pi.lift (Fin.cases prod.snd fun i => prod.fst ≫ Pi.π (fun _ : Fin n => X) i)
  hom_inv_id := Pi.hom_ext _ _ fun i => by
    cases i using Fin.cases <;> simp
  inv_hom_id := by
    refine prod.hom_ext (Pi.hom_ext _ _ fun i => ?_) ?_ <;> simp

/-- The empty fibre power is `S`: its structure morphism is an isomorphism. -/
theorem isIso_fibrePower_zero_hom : IsIso (∏ᶜ fun _ : Fin 0 => X).hom := by
  let r : (∏ᶜ fun _ : Fin 0 => X) ⟶ Over.mk (𝟙 S) := Over.homMk (∏ᶜ fun _ : Fin 0 => X).hom
  have : IsIso r := ⟨Pi.lift fun i => Fin.elim0 i, Pi.hom_ext _ _ fun i => Fin.elim0 i,
    Over.mkIdTerminal.hom_ext _ _⟩
  exact (Over.forget S).map_isIso r

/-- The structure morphism of `A ×_S X`, through the canonical fibre product. -/
theorem prod_hom_eq (A : Over S) :
    (A ⨯ X).hom = (Over.prodLeftIsoPullback A X).hom ≫ pullback.fst A.hom X.hom ≫ A.hom := by
  rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]

/-- `f × id : A ×_S X ⟶ B ×_S X` is the base change of `f : A ⟶ B` along the first projection,
on underlying schemes. -/
theorem isPullback_prod_fst_prodMap_left {A B : Over S} (f : A ⟶ B) :
    IsPullback (prod.fst : A ⨯ X ⟶ A).left (prod.map f (𝟙 X)).left f.left
      (prod.fst : B ⨯ X ⟶ B).left := by
  have h : IsPullback (prod.fst : A ⨯ X ⟶ A) (prod.map f (𝟙 X)) f prod.fst :=
    IsPullback.of_iso_pullback ⟨by simp⟩ (pullbackProdFstIsoProd f X).symm (by simp)
      (by rw [pullbackProdFstIsoProd, Iso.symm_hom, pullback.lift_snd])
  exact h.map (Over.forget S)

/-- The fibre power of a smooth `S`-scheme is smooth over `S`. -/
instance smooth_fibrePower_hom [Smooth X.hom] (n : ℕ) :
    Smooth (∏ᶜ fun _ : Fin n => X).hom := by
  induction n with
  | zero => have := isIso_fibrePower_zero_hom X; infer_instance
  | succ n ih =>
    have h : (∏ᶜ fun _ : Fin (n + 1) => X).hom = (fibrePowerSuccIso X n).hom.left ≫
        ((∏ᶜ fun _ : Fin n => X) ⨯ X).hom := (Over.w _).symm
    have : IsIso (fibrePowerSuccIso X n).hom.left := (Over.forget S).map_isIso _
    rw [h, prod_hom_eq]
    infer_instance

/-- The fibre power of a geometrically irreducible, universally open `S`-scheme over an
irreducible base is irreducible. -/
theorem irreducibleSpace_fibrePower [GeometricallyIrreducible X.hom] [UniversallyOpen X.hom]
    [IrreducibleSpace S] (n : ℕ) : IrreducibleSpace (∏ᶜ fun _ : Fin n => X).left := by
  induction n with
  | zero =>
    have := isIso_fibrePower_zero_hom X
    let e := (asIso (∏ᶜ fun _ : Fin 0 => X).hom).symm
    exact e.hom.surjective.irreducibleSpace e.hom.continuous
  | succ n ih =>
    have : IrreducibleSpace
        (Limits.pullback (∏ᶜ fun _ : Fin n => X).hom X.hom : Scheme.{u}) := inferInstance
    let e := ((Over.forget S).mapIso (fibrePowerSuccIso X n) ≪≫
      Over.prodLeftIsoPullback _ X).inv
    exact e.surjective.irreducibleSpace e.continuous

/-- **The fibre power of a smooth, geometrically irreducible scheme over a field is integral.**
It is reduced because it is smooth over a field, and irreducible because each factor is
geometrically irreducible. -/
theorem isIntegral_fibrePower {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom] (n : ℕ) :
    IsIntegral (∏ᶜ fun _ : Fin n => X).left := by
  have := irreducibleSpace_fibrePower X n
  have := geometricallyReduced_of_smooth (∏ᶜ fun _ : Fin n => X).hom
  have : IsReduced (∏ᶜ fun _ : Fin n => X).left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (∏ᶜ fun _ : Fin n => X).hom
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨‹_›, ‹_›⟩

/-- A scheme smooth of relative dimension one over a field has, besides any given point `x`, a
closed point different from `x`. Closed points are dense, the scheme being Jacobson; if `x`
were the only one, the scheme would be the single point `x`, of dimension zero, whereas it has
dimension one at every point. -/
theorem exists_isClosed_singleton_ne {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] (x : Y) :
    ∃ y : Y, IsClosed {y} ∧ y ≠ x := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have := LocallyOfFiniteType.jacobsonSpace f
  by_contra! h
  have hsub : Subsingleton Y := by
    have huniv : (Set.univ : Set Y) ⊆ closure {x} := by
      rw [← closure_closedPoints]
      exact closure_mono fun y hy => h y hy
    refine ⟨fun a b => ?_⟩
    obtain ⟨c, hc⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨x, trivial⟩
      isClosed_univ.isLocallyClosed
    have hx : IsClosed {x} := h c hc.2 ▸ hc.2
    rw [hx.closure_eq] at huniv
    exact (huniv (Set.mem_univ a)).trans (huniv (Set.mem_univ b)).symm
  have : DiscreteTopology Y := ⟨Subsingleton.elim _ _⟩
  have : Nonempty Y := ⟨x⟩
  have hdim := topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one f x
  have hle := topologicalKrullDimAt_le_topologicalKrullDim (X := Y) x
  rw [hdim, topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] at hle
  exact absurd hle (by decide)

/-- **A curve over an algebraically closed field has two distinct rational points.** If
`X ⟶ Spec k` is smooth of relative dimension one, `k` is algebraically closed and `X` is
nonempty, the structure morphism has two distinct sections. They come from two distinct closed
points, whose residue fields are `k` by the Nullstellensatz. -/
theorem exists_ne_sections_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 X.hom] [Nonempty X.left] :
    ∃ s t : Over.mk (𝟙 (Spec (.of k))) ⟶ X, s ≠ t := by
  have := SmoothOfRelativeDimension.smooth 1 X.hom
  have := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X.left))
    Set.univ_nonempty isClosed_univ.isLocallyClosed
  obtain ⟨y, hy, hyx⟩ := exists_isClosed_singleton_ne X.hom x
  refine ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp _ _ _),
    Over.homMk (pointOfClosedPoint X.hom y hy) (pointOfClosedPoint_comp _ _ _), fun h => ?_⟩
  have h' := congrArg (fun g => g.left (IsLocalRing.closedPoint k)) h
  exact hyx ((pointOfClosedPoint_apply X.hom y hy _).symm.trans
    (h'.symm.trans (pointOfClosedPoint_apply X.hom x hx _)))

/-- **The permutation action on the fibre power of a curve is faithful.** For `X` nonempty and
smooth of relative dimension one over an algebraically closed field, the action of `Sₙ` on `Xⁿ`
by permuting the factors is faithful. -/
theorem fibrePowerPerm_left_injective_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 X.hom] [Nonempty X.left] (n : ℕ) :
    Function.Injective fun σ : Equiv.Perm (Fin n) => (fibrePowerPerm X n σ).left := by
  obtain ⟨s, t, hst⟩ := exists_ne_sections_of_isAlgClosed X
  exact fibrePowerPerm_left_injective X n hst

end Stacks.Scheme

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- **The family `[x₁] + ⋯ + [xₙ]`.** On a separated smooth relative curve, the sum of the graphs
of `n` relative points `xᵢ : T ⟶ X` is a degree-`n` family over `T`. It is built by adding the
points one at a time, starting from the empty family; its ideal is computed in
`Stacks.Hilbert.familyOfPoints_ideal`. -/
def familyOfPoints (X T : Over S) [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom] :
    {n : ℕ} → (Fin n → (T ⟶ X)) → HilbertFamily X T n
  | 0, _ => familyZero X T
  | _ + 1, x => familyAddPoint X T (familyOfPoints X T fun i => x i.succ) (x 0)
      (isClosedImmersion_pointGraph_of_isSeparated X T (x 0))

/-- The ideal of `[x₁] + ⋯ + [xₙ]` is the product of the ideals of the graphs. -/
theorem familyOfPoints_ideal (X T : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom] {n : ℕ} (x : Fin n → (T ⟶ X)) :
    (familyOfPoints X T x).ideal = ∏ i, pointIdeal X T (x i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [familyOfPoints, familyAddPoint_ideal, ih, Fin.prod_univ_succ, mul_comm]

/-- The family `[x₁] + ⋯ + [xₙ]` does not depend on the order of the points. -/
theorem familyOfPoints_perm (X T : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom] {n : ℕ} (x : Fin n → (T ⟶ X)) (σ : Equiv.Perm (Fin n)) :
    familyOfPoints X T (fun i => x (σ i)) = familyOfPoints X T x :=
  HilbertFamily.ext (by
    rw [familyOfPoints_ideal, familyOfPoints_ideal]
    exact Equiv.prod_comp σ fun i => pointIdeal X T (x i))

variable {X : Over S} [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
  {H : ℕ → Over S} (hH : ∀ d, RepresentsHilbertFunctorOfRank X (H d) d)

/-- **The morphism `π : Xⁿ ⟶ Sⁿ(X) = Hilb^n_{X/S}` of Stacks 0FH9.** For a separated smooth
relative curve `X ⟶ S` and representing schemes `H d` of `Hilb^d_{X/S}`, the morphism
`Xⁿ ⟶ H n` classifying the family `Σᵢ Γ_{prᵢ}`, so that `(x₁, …, xₙ) ↦ [x₁] + ⋯ + [xₙ]`
(`Stacks.Hilbert.family_comp_symmetricPowerMap`). -/
def symmetricPowerMap (n : ℕ) : (∏ᶜ fun _ : Fin n => X) ⟶ H n :=
  (hH n).family.symm (familyOfPoints X _ fun i => Pi.π (fun _ : Fin n => X) i)

/-- The ideal of the family classified by `g ≫ π`, for `g = (x₁, …, xₙ) : T ⟶ Xⁿ`, is the product
of the ideals of the graphs of the `xᵢ`. -/
theorem family_comp_symmetricPowerMap_ideal (n : ℕ) {T : Over S}
    (g : T ⟶ ∏ᶜ fun _ : Fin n => X) :
    ((hH n).family (g ≫ symmetricPowerMap hH n)).ideal =
      ∏ i, pointIdeal X T (g ≫ Pi.π (fun _ : Fin n => X) i) := by
  rw [(hH n).naturality, symmetricPowerMap, Equiv.apply_symm_apply, familyOfPoints_ideal,
    Stacks.IdealSheaf.comap_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := isClosedImmersion_pointGraph_of_isSeparated X _ (Pi.π (fun _ : Fin n => X) i)
  exact pointIdeal_comap_familyBaseChangeMap X g _

/-- **The characterization of `π`.** The morphism `g ≫ π`, for `g = (x₁, …, xₙ) : T ⟶ Xⁿ`,
classifies the family `[x₁] + ⋯ + [xₙ]`. -/
theorem family_comp_symmetricPowerMap (n : ℕ) {T : Over S} (g : T ⟶ ∏ᶜ fun _ : Fin n => X) :
    (hH n).family (g ≫ symmetricPowerMap hH n) =
      familyOfPoints X T fun i => g ≫ Pi.π (fun _ : Fin n => X) i :=
  HilbertFamily.ext (by rw [family_comp_symmetricPowerMap_ideal, familyOfPoints_ideal])

/-- `π` classifies the family `Σᵢ Γ_{prᵢ}`: its ideal is the product over all `i` of the ideals
of the graphs of the projections. -/
theorem symmetricPowerMap_family_ideal (n : ℕ) :
    ((hH n).family (symmetricPowerMap hH n)).ideal =
      ∏ i, pointIdeal X _ (Pi.π (fun _ : Fin n => X) i) := by
  simpa using family_comp_symmetricPowerMap_ideal hH n (𝟙 _)

/-- **`π` is `Sₙ`-invariant**: permuting the factors does not change the sum of the points. -/
theorem fibrePowerPerm_comp_symmetricPowerMap (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    fibrePowerPerm X n σ ≫ symmetricPowerMap hH n = symmetricPowerMap hH n := by
  refine (hH n).family.injective ?_
  have h := family_comp_symmetricPowerMap hH n (𝟙 _)
  simp only [Category.id_comp] at h
  rw [family_comp_symmetricPowerMap, h]
  simp_rw [fibrePowerPerm_comp_π]
  exact familyOfPoints_perm X _ _ σ

/-- `Sₙ`-invariance of `π`, on the underlying morphism of schemes. -/
theorem fibrePowerPerm_left_comp_symmetricPowerMap_left (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (fibrePowerPerm X n σ).left ≫ (symmetricPowerMap hH n).left =
      (symmetricPowerMap hH n).left := by
  rw [← Over.comp_left, fibrePowerPerm_comp_symmetricPowerMap]

/-- **`π_{n+1}` through point addition.** `π_{n+1}` is the isomorphism `X^{n+1} ≅ Xⁿ ×_S X`,
followed by `π_n × id`, followed by the point-addition morphism `H n ×_S X ⟶ H (n + 1)` of
Stacks 0B9G. -/
theorem symmetricPowerMap_succ (n : ℕ) :
    symmetricPowerMap hH (n + 1) = (fibrePowerSuccIso X n).hom ≫
      prod.map (symmetricPowerMap hH n) (𝟙 X) ≫ addPoint (hH n) (hH (n + 1)) := by
  refine (hH (n + 1)).family.injective (HilbertFamily.ext ?_)
  have e1 : ((fibrePowerSuccIso X n).hom ≫ prod.map (symmetricPowerMap hH n) (𝟙 X)) ≫
      prod.fst = (Pi.lift fun i => Pi.π (fun _ : Fin (n + 1) => X) i.succ) ≫
        symmetricPowerMap hH n := by
    simp [fibrePowerSuccIso]
  have e2 : ((fibrePowerSuccIso X n).hom ≫ prod.map (symmetricPowerMap hH n) (𝟙 X)) ≫
      prod.snd = Pi.π (fun _ : Fin (n + 1) => X) 0 := by
    simp [fibrePowerSuccIso]
  rw [symmetricPowerMap_family_ideal, ← Category.assoc,
    isPointAddition_addPoint (hH n) (hH (n + 1)) _ _, e1, e2,
    family_comp_symmetricPowerMap_ideal, Fin.prod_univ_succ, mul_comm]
  simp

/-- `π_0` is an isomorphism: both `X⁰` and `H 0` are `S`. -/
theorem isIso_symmetricPowerMap_zero : IsIso (symmetricPowerMap hH 0) := by
  refine ⟨Pi.lift fun i => Fin.elim0 i, Pi.hom_ext _ _ fun i => Fin.elim0 i, ?_⟩
  refine (hH 0).family.injective (HilbertFamily.ext ?_)
  rw [HilbertFamily.ideal_eq_top, HilbertFamily.ideal_eq_top]

/-- **`π : Xⁿ ⟶ Sⁿ(X)` is finite locally free of degree `n!`.** By induction on `n`, through
`Stacks.Hilbert.symmetricPowerMap_succ`: `π_n × id` is a base change of `π_n`, point addition
has degree `n + 1` (Stacks 0B9G), and degrees multiply in a composition. -/
instance isFiniteLocallyFreeOfRank_symmetricPowerMap (n : ℕ) :
    Morphisms.IsFiniteLocallyFreeOfRank (symmetricPowerMap hH n).left n ! := by
  induction n with
  | zero =>
    have := isIso_symmetricPowerMap_zero hH
    have : IsIso (symmetricPowerMap hH 0).left := (Over.forget S).map_isIso _
    exact Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso _
  | succ n ih =>
    have h1 : Morphisms.IsFiniteLocallyFreeOfRank
        (prod.map (symmetricPowerMap hH n) (𝟙 X)).left n ! :=
      Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback (isPullback_prod_fst_prodMap_left X _)
    have h2 : Morphisms.IsFiniteLocallyFreeOfRank (addPoint (hH n) (hH (n + 1))).left (n + 1) :=
      (isPointAddition_addPoint _ _).isFiniteLocallyFreeOfRank_left
    have h3 := Morphisms.IsFiniteLocallyFreeOfRank.comp
      (prod.map (symmetricPowerMap hH n) (𝟙 X)).left (addPoint (hH n) (hH (n + 1))).left
      (n !) (n + 1)
    have h4 := Morphisms.isFiniteLocallyFreeOfRank_precomp
      ((Over.forget S).mapIso (fibrePowerSuccIso X n)) _ h3
    rw [symmetricPowerMap_succ, Over.comp_left, Over.comp_left, Nat.factorial_succ, mul_comm]
    exact h4

/-- **`π : Xⁿ ⟶ Sⁿ(X)` is finite.** -/
instance isFinite_symmetricPowerMap (n : ℕ) : IsFinite (symmetricPowerMap hH n).left :=
  Morphisms.isFinite_of_isFiniteLocallyFreeOfRank _ n !

end Stacks.Hilbert

namespace Stacks.SheafOfModules

open Stacks.Hilbert RingedSpaceModuleAdjunction

/-- **The computation `π^*𝒩 = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}` of Stacks 0FH9 for the actual
`π : Xⁿ ⟶ Sⁿ(X)`.** Let `k` be algebraically closed and `X` a separated, geometrically
irreducible scheme, smooth of relative dimension one over `k`, whose Hilbert functors of points
are represented by `H d`. For `π = symmetricPowerMap hH n`, a family `ℒᵢ` with
`[ℒᵢ] = prᵢ^*[ℳ]` and the canonical norm of Tag 0BD2,

  `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]`   in   `Pic(Xⁿ)`.

Every hypothesis on `π` and `Xⁿ` of the general form of this computation on a fibre power,
`pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_faithful`, is
discharged here: the degree, finiteness and invariance of `π`, the
integrality of `Xⁿ`, and the faithfulness of the permutation action. -/
theorem pullbackPicardClass_normInvertible_symmetricPowerMap {k : Type u} [Field k]
    [IsAlgClosed k] {X : Over (Spec (.of k))} [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom] [GeometricallyIrreducible X.hom] {H : ℕ → Over (Spec (.of k))}
    (hH : ∀ d, RepresentsHilbertFunctorOfRank X (H d) d) (n : ℕ) (i₀ : Fin n)
    (M : SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace))
    (hM : IsInvertible X.left.presheaf X.left.ringCatIsSheaf M)
    (L : Fin n → SheafOfModules.{u}
      (structureSheafRing (∏ᶜ fun _ : Fin n => X).left.toRingedSpace))
    (hL : ∀ i, IsInvertible (∏ᶜ fun _ : Fin n => X).left.presheaf
      (∏ᶜ fun _ : Fin n => X).left.ringCatIsSheaf (L i))
    (hpull : ∀ i, pullbackPicardClass (Pi.π (fun _ : Fin n => X) i).left M hM =
      picardClass (∏ᶜ fun _ : Fin n => X).left.presheaf
        (∏ᶜ fun _ : Fin n => X).left.ringCatIsSheaf (L i) (hL i)) :
    pullbackPicardClass (symmetricPowerMap hH n).left
        (Stacks.Divisors.normInvertible (symmetricPowerMap hH n).left
          (Stacks.Divisors.finiteLocallyFreeNormOfRank (symmetricPowerMap hH n).left n !
            (factorial_pos n)).1.toMorphismNormMap
          (L i₀))
        (Stacks.Divisors.isInvertible_normInvertible (symmetricPowerMap hH n).left _ (L i₀)
          (Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible
            (symmetricPowerMap hH n).left (L i₀) (hL i₀))) =
      (n - 1)! • ∑ i, picardClass (∏ᶜ fun _ : Fin n => X).left.presheaf
        (∏ᶜ fun _ : Fin n => X).left.ringCatIsSheaf (L i) (hL i) := by
  have := SmoothOfRelativeDimension.smooth 1 X.hom
  have := Stacks.Scheme.isIntegral_fibrePower X n
  have : Nonempty X.left := X.hom.surjective.nonempty
  exact pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_faithful X
    (symmetricPowerMap hH n).left (fibrePowerPerm_left_comp_symmetricPowerMap_left hH n)
    (Stacks.Scheme.fibrePowerPerm_left_injective_of_isAlgClosed X n) i₀ M hM L hL hpull

end Stacks.SheafOfModules

end
