module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SeparableExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.GaloisSelfProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace of the unit class of the spectrum of a Galois extension (Stacks 0FVR)

Let `𝔚` be data (D0), (D1), (D2') satisfying axioms (A1)–(A7) of Section 45.14
(`Stacks.WeilCohomology.WeilChernData`), `γ` the cycle class map of Tag 0FIF, and `k'/k` a finite
Galois extension. Then `X = Spec(k')` is nonempty, smooth, projective and equidimensional of
dimension `0` over `k`, and Stacks 0FVR says that the map `λ = ∫_X : H^0(X)(0) ⟶ F` of axiom (A6),
characterised by `(id ⊗ λ) γ([Δ]) = 1`, takes the unit class to the degree:

`∫_{Spec(k')} 1 = [k' : k]`.

## The proof

The proof is the source's, on the actual data. Write `A = H^*(X)`, `G = Gal(k'/k)` and
`a_σ = Spec(σ) : X ⟶ X`.

* `X × X = ∐_{τ ∈ G} X`, the `τ`-th copy embedded by `c_τ = (id, a_τ)`
  (`Stacks.WeilCohomology.isColimitSpecGaloisCofan`); the diagonal is `c_1`. By (A1) the
  restrictions `c_τ^*` are jointly injective on `H^*(X × X)`.
* `c_ρ^* γ([Δ]) = γ(c_ρ^![Δ])` by compatibility of `γ` with the Gysin maps, and the Gysin map of
  the open immersion `c_ρ` is restriction of cycles. So `c_1^* γ([Δ]) = γ([X]) = 1`, and
  `c_ρ^* γ([Δ]) = 0` for `ρ ≠ 1`, the copies being disjoint.
* With `f_σ = a_σ × id`, `c_τ ≫ f_σ = a_σ ≫ c_{σ⁻¹τ}`, so `c_τ^* ∑_σ f_σ^* γ([Δ]) = 1` for every
  `τ`: this is the source's `1 = ∑_σ (Spec(σ) × id)^* γ([Δ])`.
* Through the Künneth isomorphism of (A5), `f_σ^*` is `a_σ^* ⊗ id`, which commutes with the
  contraction `id ⊗ λ`. Applying `id ⊗ λ` gives `λ(1) · 1 = ∑_σ a_σ^*(1) = |G| · 1` in `H^0(X)`
  (`FirstChernClassData.IsCohomologicalChernCharacter.untwistTrace_one_smul_spec_galois`); no
  nonvanishing is used up to here.
* `|G| = [k' : k]` (`IsGalois.card_aut_eq_finrank`), and `H^*(X) ≠ 0` by (A3), (A4) and (A5)
  (`FirstChernClassData.nontrivial_H_spec`: `Spec(k')` is a point of degree `[k' : k]` of
  `𝐏¹_k`), so the unit can be cancelled: `λ(1) = [k' : k]`.

## The statement

`λ` is any `F`-linear map `H^0(X)(0) ⟶ F` with `(id ⊗ λ) γ([Δ]) = 1`, the normalisation of (A6);
by Remark 0FIK such a map is unique, and it is the one written `∫_X`
(`WeilChernData.toWeilData`, whose trace map is a choice of it, gives
`WeilChernData.toWeilData_trace_one_spec_galois`). The value `λ(1)` is read through
`FirstChernClassData.untwistTrace`, which identifies `H^0(X)(0)` with `H^0(X)` by the canonical
identification `V(0) = V` (`tateTwistCoordinates_zero`).

## Main results

* `WeilChernData.untwistTrace_one_spec_galois`: **Stacks 0FVR**, `∫_{Spec(k')} 1 = [k' : k]` for
  a finite Galois extension `k'/k`.
* `WeilChernData.toWeilData_trace_one_spec_galois`: the same for the trace map `∫_X` of the data
  of Section 0FHA defined by `𝔚`.
* `FirstChernClassData.IsCohomologicalChernCharacter.untwistTrace_one_smul_spec_galois`:
  `λ(1) · 1 = [k' : k] · 1` in `H^0(Spec(k'))`, from (A1), (A5) and the normalisation alone.

Supporting facts:

* `codimensionGysin_closedSubschemeClass_of_isOpenImmersion_self`: for an open and closed
  immersion `g : V ⟶ Z`, `g^![V] = [V]` in `CH^0(V)`.
* `codimensionGysin_closedSubschemeClass_of_disjoint_range`: for an open immersion `j : Y ⟶ Z`
  and a closed subscheme `A` of `Z` disjoint from its image, `j^![A] = 0`.

## References

* [Stacks Project, Tag 0FVR](https://stacks.math.columbia.edu/tag/0FVR)
* [Stacks Project, Tag 0FIK](https://stacks.math.columbia.edu/tag/0FIK)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-! ### Gysin maps of open immersions on classes of closed subschemes -/

section Chow

variable {V Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- Restricted along an open and closed immersion `g : V ⟶ Z`, the cycle of the closed subscheme
`V` of `Z` is the fundamental cycle of `V`. -/
theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme_of_isOpenImmersion_self (g : V ⟶ Z)
    [IsOpenImmersion g.hom.left] [IsClosedImmersion g.hom.left] (n : ℤ) :
    cycleGroupRestrict (fieldChowSituation k) Z.obj.hom V.obj.hom g.hom.left (Over.w g.hom) n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom g.hom.left n) =
      fundamentalCycle (fieldChowSituation k) V.obj.hom n := by
  rw [← cycleGroupRestrict_fundamentalCycle (fieldChowSituation k) Z.obj.hom V.obj.hom
    g.hom.left (Over.w g.hom) n]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  rw [cycleGroupRestrict_apply, cycleGroupRestrict_apply]
  show (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom g.hom.left n).1
      ((𝟙 Z.obj.left : Z.obj.left ⟶ Z.obj.left) (g.hom.left x)) =
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom (𝟙 _) n).1
      ((𝟙 Z.obj.left : Z.obj.left ⟶ Z.obj.left) (g.hom.left x))
  by_cases hA : ∃ ξ : genericPoints Z.obj.left, (𝟙 Z.obj.left : Z.obj.left ⟶ Z.obj.left) ξ.1 =
      (𝟙 Z.obj.left : Z.obj.left ⟶ Z.obj.left) (g.hom.left x) ∧
      relativeDimension (fieldChowSituation k).dimensionFunction Z.obj.hom
        ((𝟙 Z.obj.left : Z.obj.left ⟶ Z.obj.left) (g.hom.left x)) = n
  · obtain ⟨ξ, hξ, hd⟩ := hA
    rw [← hξ]
    exact cycleAssociatedToClosedSubscheme_apply_of_mem_range_of_isOpenImmersion
      (fieldChowSituation k) Z.obj.hom (𝟙 _) g.hom.left g.hom.left (Category.comp_id _) n ξ
      (hξ ▸ hd) x (by simpa using hξ.symm)
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_isOpenImmersion (fieldChowSituation k)
      Z.obj.hom (𝟙 _) g.hom.left g.hom.left (Category.comp_id _) n _ hA,
      cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation k) Z.obj.hom (𝟙 _) n _ hA]

/-- **`g^![V] = [V]`** for an open and closed immersion `g : V ⟶ Z`: the Gysin map of `g` carries
the class `[V] ∈ CH^0(Z)` of the closed subscheme `V` to the fundamental class of `V`. -/
theorem codimensionGysin_closedSubschemeClass_of_isOpenImmersion_self (g : V ⟶ Z)
    [IsOpenImmersion g.hom.left] [IsClosedImmersion g.hom.left] :
    codimensionGysin V.obj.hom Z.obj.hom (Over.w g.hom) 0
        (closedSubschemeClass Z.obj.hom g.hom.left 0) = fundamentalClass V := by
  funext d
  rw [codimensionGysin_closedSubschemeClass_apply,
    cycleGroupRestrict_cycleAssociatedToClosedSubscheme_of_isOpenImmersion_self g,
    ← fundamentalChowClass, chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  exact eq_of_heq ((fundamentalChowClass_heq _ _ (by ring)).trans
    (chowGroupDegreeEquiv_heq _ _ _ _).symm)

/-- **`j^![A] = 0`** for an open immersion `j : Y ⟶ Z` and a closed subscheme `A` of `Z` disjoint
from the image of `j`. -/
theorem codimensionGysin_closedSubschemeClass_of_disjoint_range
    {Y : (SmoothProjectiveScheme k).FullSubcategory} (j : Y ⟶ Z) [IsOpenImmersion j.hom.left]
    {A : Scheme.{u}} (ι : A ⟶ Z.obj.left)
    [IsClosedImmersion ι] (hdisj : Disjoint (Set.range j.hom.left.base) (Set.range ι.base)) :
    codimensionGysin Y.obj.hom Z.obj.hom (Over.w j.hom) 0 (closedSubschemeClass Z.obj.hom ι 0) =
      0 := by
  funext d
  rw [codimensionGysin_closedSubschemeClass_apply]
  have h0 : cycleGroupRestrict (fieldChowSituation k) Z.obj.hom Y.obj.hom j.hom.left
      (Over.w j.hom) ((d : ℤ) - 0)
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom ι ((d : ℤ) - 0)) = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    rw [cycleGroupRestrict_apply]
    exact cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation k) Z.obj.hom ι _ _
      (fun ⟨ξ, hξ, _⟩ ↦ hdisj.le_bot ⟨⟨y, rfl⟩, ⟨ξ.1, hξ⟩⟩)
  rw [h0, map_zero, map_zero]
  rfl

end Chow

/-! ### The copies of `Spec(k')` in the self-product -/

namespace GaloisTrace

variable (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k']

/-- `X = Spec(k')` as a smooth projective scheme over `k`. -/
abbrev X : (SmoothProjectiveScheme k).FullSubcategory := spec k k'

variable {k'}

/-- `a_σ = Spec(σ) : Spec(k') ⟶ Spec(k')`. -/
abbrev aut (σ : k' ≃ₐ[k] k') : X (k := k) k' ⟶ X k' := specMap (σ : k' →ₐ[k] k')

/-- The underlying morphism of schemes of `a_σ` is `Spec(σ)`. -/
theorem aut_hom_left (σ : k' ≃ₐ[k] k') : (aut σ).hom.left = specAut σ := rfl

/-- `Spec` of the identity automorphism is the identity. -/
theorem aut_one : aut (1 : k' ≃ₐ[k] k') = 𝟙 _ :=
  hom_ext_left (specAut_one (k := k) (k' := k'))

/-- `a_{στ} = a_σ ≫ a_τ`. -/
theorem aut_mul (σ τ : k' ≃ₐ[k] k') : aut (σ * τ) = aut σ ≫ aut τ :=
  hom_ext_left (specAut_mul σ τ)

/-- The `τ`-th copy `c_τ = (id, Spec(τ)) : Spec(k') ⟶ Spec(k') × Spec(k')`. -/
def copy (τ : k' ≃ₐ[k] k') : X (k := k) k' ⟶ prod (X k') (X k') :=
  ObjectProperty.homMk (Over.homMk (U := (X (k := k) k').obj) (V := (prod (X k') (X k')).obj)
    (specGaloisCoprojection τ) (by
      change specGaloisCoprojection τ ≫ pullback.fst _ _ ≫ _ = _
      rw [specGaloisCoprojection_fst_assoc]))

/-- The underlying morphism of schemes of `c_τ` is the `τ`-th coprojection
`specGaloisCoprojection τ`. -/
theorem copy_hom_left (τ : k' ≃ₐ[k] k') : (copy τ).hom.left = specGaloisCoprojection τ := rfl

/-- The copy `c_τ` is an open immersion. -/
instance (τ : k' ≃ₐ[k] k') : IsOpenImmersion (copy τ).hom.left :=
  isOpenImmersion_specGaloisCoprojection τ

/-- The first projection of `c_τ` is the identity. -/
@[reassoc (attr := simp)]
theorem copy_fst (τ : k' ≃ₐ[k] k') : copy τ ≫ fst (X k') (X k') = 𝟙 _ :=
  hom_ext_left (specGaloisCoprojection_fst τ)

/-- The second projection of `c_τ` is `a_τ`. -/
@[reassoc (attr := simp)]
theorem copy_snd (τ : k' ≃ₐ[k] k') : copy τ ≫ snd (X k') (X k') = aut τ :=
  hom_ext_left (specGaloisCoprojection_snd τ)

/-- The diagonal is the copy `c_1`. -/
theorem diag_eq_copy_one : diag (X (k := k) k') = copy 1 :=
  prod_hom_ext (by rw [diag_fst, copy_fst]) (by rw [diag_snd, copy_snd, aut_one])

/-- `f_σ = Spec(σ) × id`. -/
def autProd (σ : k' ≃ₐ[k] k') : prod (X (k := k) k') (X k') ⟶ prod (X k') (X k') :=
  prodLift (fst (X k') (X k') ≫ aut σ) (snd (X k') (X k'))

/-- The first projection of `f_σ` is the first projection followed by `a_σ`. -/
@[reassoc (attr := simp)]
theorem autProd_fst (σ : k' ≃ₐ[k] k') :
    autProd σ ≫ fst (X (k := k) k') (X k') = fst (X k') (X k') ≫ aut σ :=
  prodLift_fst _ _

/-- The second projection of `f_σ` is the second projection. -/
@[reassoc (attr := simp)]
theorem autProd_snd (σ : k' ≃ₐ[k] k') :
    autProd σ ≫ snd (X (k := k) k') (X k') = snd (X k') (X k') :=
  prodLift_snd _ _

/-- `c_τ ≫ (Spec(σ) × id) = Spec(σ) ≫ c_{σ⁻¹τ}`. -/
theorem copy_comp_autProd (σ τ : k' ≃ₐ[k] k') :
    copy τ ≫ autProd σ = aut σ ≫ copy (σ⁻¹ * τ) :=
  prod_hom_ext (by simp) (by simp [← aut_mul])

/-- The copies are the coprojections of a coproduct of schemes. -/
def isColimitCopy :
    IsColimit (Cofan.mk (prod (X (k := k) k') (X k')).obj.left fun τ ↦ (copy τ).hom.left) :=
  isColimitSpecGaloisCofan k k'

/-- Distinct copies have disjoint images. -/
theorem disjoint_range_copy {σ τ : k' ≃ₐ[k] k'} (h : σ ≠ τ) :
    Disjoint (Set.range (copy (k := k) σ).hom.left.base) (Set.range (copy τ).hom.left.base) := by
  have := disjoint_opensRange_specGaloisCoprojection h
  rwa [← TopologicalSpace.Opens.coe_disjoint, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange] at this

end GaloisTrace

/-! ### The trace of the unit class -/

namespace FirstChernClassData.IsCohomologicalChernCharacter

open GaloisTrace

variable {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch)
  {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k']

/-- The untwisted class `κ(γ([Δ])) ∈ H^0(X × X)` of the diagonal of `X = Spec(k')`. -/
abbrev diagonalUntwist (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsGalois k k'] : 𝔇.H (prod (X (k := k) k') (X k')) :=
  𝔇.κ _ ((0 : ℕ) : ℤ)
    (h.codimensionCycleClass (prod (X k') (X k')) 0 (diagonalClass (X k') 0))

open Classical in
/-- **`c_ρ^* γ([Δ])` is `1` for `ρ = 1` and `0` otherwise.** -/
theorem pull_copy_diagonalUntwist (ρ : k' ≃ₐ[k] k') :
    𝔇.pull (copy ρ) (h.diagonalUntwist k') = if ρ = 1 then 1 else 0 := by
  rw [diagonalUntwist, ← κ_pullTw, ← h.codimensionCycleClass_codimensionGysin]
  split_ifs with hρ
  · subst hρ
    have : IsOpenImmersion (diag (X (k := k) k')).hom.left := by
      rw [diag_eq_copy_one]; infer_instance
    rw [← diag_eq_copy_one]
    have h0 : codimensionGysin (X (k := k) k').obj.hom (prod (X k') (X k')).obj.hom
        (Over.w (diag (X k')).hom) ((0 : ℕ) : ℤ) (diagonalClass (X k') 0) =
          fundamentalClass (X k') :=
      codimensionGysin_closedSubschemeClass_of_isOpenImmersion_self (diag (X k'))
    rw [h0, h.codimensionCycleClass_fundamentalClass]
    exact 𝔇.κ_unitTw _
  · have hd : Disjoint (Set.range (copy ρ).hom.left.base)
        (Set.range (diag (X (k := k) k')).hom.left.base) := by
      rw [diag_eq_copy_one]; exact disjoint_range_copy hρ
    have h0 : codimensionGysin (X (k := k) k').obj.hom (prod (X k') (X k')).obj.hom
        (Over.w (copy ρ).hom) ((0 : ℕ) : ℤ) (diagonalClass (X k') 0) = 0 :=
      codimensionGysin_closedSubschemeClass_of_disjoint_range (copy ρ) _ hd
    rw [h0, map_zero, map_zero]

/-- **The source's `1 = ∑_σ (Spec(σ) × id)^* γ([Δ])`**, checked on the copies by (A1). -/
theorem sum_pull_autProd_diagonalUntwist (hA1 : 𝔇.CoproductAxiom) :
    ∑ σ : k' ≃ₐ[k] k', 𝔇.pull (autProd σ) (h.diagonalUntwist k') = 1 := by
  classical
  refine (𝔇.bijective_pull_of_isColimit_cofan hA1 copy isColimitCopy).1 (funext fun τ ↦ ?_)
  simp only [map_sum, map_one]
  have hτ : ∀ σ : k' ≃ₐ[k] k', 𝔇.pull (copy τ) (𝔇.pull (autProd σ) (h.diagonalUntwist k')) =
      if σ = τ then 1 else 0 := by
    intro σ
    rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, copy_comp_autProd, 𝔇.pull_comp, AlgHom.comp_apply,
      pull_copy_diagonalUntwist]
    have : σ⁻¹ * τ = 1 ↔ σ = τ := by rw [inv_mul_eq_one]
    by_cases hστ : σ = τ
    · rw [if_pos (this.mpr hστ), if_pos hστ, map_one]
    · rw [if_neg (fun h' ↦ hστ (this.mp h')), if_neg hστ, map_zero]
  rw [Finset.sum_congr rfl fun σ _ ↦ hτ σ, Finset.sum_ite_eq' Finset.univ τ, if_pos
    (Finset.mem_univ _)]

omit [CharZero F] in
/-- Through the Künneth map, `(Spec(σ) × id)^*` is `Spec(σ)^* ⊗ id`. -/
theorem pull_autProd_kunnethMap (σ : k' ≃ₐ[k] k') (t : 𝔇.H (X (k := k) k') ⊗[F] 𝔇.H (X k')) :
    𝔇.pull (autProd σ) (𝔇.kunnethMap (X k') (X k') t) =
      𝔇.kunnethMap (X k') (X k')
        (TensorProduct.map (𝔇.pull (aut σ)).toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [kunnethMap_tmul, TensorProduct.map_tmul, kunnethMap_tmul, map_mul, ← AlgHom.comp_apply,
      ← AlgHom.comp_apply, ← 𝔇.pull_comp, ← 𝔇.pull_comp, autProd_fst, autProd_snd, 𝔇.pull_comp]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [CharZero F] in
/-- The contraction `x ⊗ y ↦ λ(y) x` commutes with `g ⊗ id`. -/
theorem contractRight_map_id {A : Type*} [Ring A] [Algebra F A] (lam : A →ₗ[F] F)
    (g : A →ₗ[F] A) (t : A ⊗[F] A) :
    DiagonalExpansion.contractRight lam (TensorProduct.map g LinearMap.id t) =
      g (DiagonalExpansion.contractRight lam t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **`λ(1) · 1 = [k' : k] · 1` in `H^0(Spec(k'))`** for a finite Galois extension `k'/k` and
every `λ` normalised as in axiom (A6), `(id ⊗ λ) γ([Δ]) = 1`. This uses only (A1) and (A5), and no
nonvanishing of `H^*(Spec(k'))`. -/
theorem untwistTrace_one_smul_spec_galois (hA1 : 𝔇.CoproductAxiom) (hA5 : 𝔇.KunnethAxiom)
    (lam : tateTwist F 𝔇.tate (𝔇.grade (spec k k') (2 * ((0 : ℕ) : ℤ))) (0 : ℕ) →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 (spec k k') 0 lam
      (h.codimensionCycleClass (prod (spec k k') (spec k k')) 0
        (diagonalClass (spec k k') 0)) = 1) :
    𝔇.untwistTrace (spec k k') 0 lam 1 • (1 : 𝔇.H (spec k k')) =
      (Module.finrank k k' : F) • (1 : 𝔇.H (spec k k')) := by
  classical
  set μ := 𝔇.untwistTrace (spec k k') 0 lam
  set t := (𝔇.kunnethEquiv hA5 (X (k := k) k') (X k')).symm (h.diagonalUntwist k')
  have ht : 𝔇.kunnethMap (X (k := k) k') (X k') t = h.diagonalUntwist k' :=
    (𝔇.kunnethEquiv hA5 _ _).apply_symm_apply _
  have hμ : DiagonalExpansion.contractRight μ t = 1 := hlam
  have hsum : ∑ σ : k' ≃ₐ[k] k', TensorProduct.map (𝔇.pull (aut σ)).toLinearMap LinearMap.id t =
      (1 : 𝔇.H (X (k := k) k')) ⊗ₜ[F] (1 : 𝔇.H (X k')) := by
    refine (hA5.2 (X k') (X k')).1 ?_
    rw [map_sum, kunnethMap_tmul, map_one, map_one, one_mul]
    simp_rw [← pull_autProd_kunnethMap, ht]
    exact h.sum_pull_autProd_diagonalUntwist hA1
  have := congrArg (DiagonalExpansion.contractRight μ) hsum
  rw [map_sum, DiagonalExpansion.contractRight_tmul] at this
  simp_rw [contractRight_map_id, hμ] at this
  simp only [AlgHom.toLinearMap_apply, map_one, Finset.sum_const, Finset.card_univ] at this
  rw [← this, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank k k', Nat.cast_smul_eq_nsmul]

end FirstChernClassData.IsCohomologicalChernCharacter

namespace WeilChernData

variable {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)
  (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k']

/-- **Stacks Project, Tag 0FVR.** Assume given data (D0), (D1), (D2') satisfying axioms
(A1)–(A7), and let `k'/k` be a finite Galois extension. Then `∫_{Spec(k')} 1 = [k' : k]`: every
`F`-linear map `λ : H^0(Spec(k'))(0) ⟶ F` with `(id ⊗ λ) γ([Δ]) = 1` (axiom (A6), `γ` the cycle
class map of Tag 0FIF; such a `λ` is unique by Remark 0FIK and is `∫_{Spec(k')}`) takes the unit
class to `[k' : k]`. -/
@[stacks 0FVR "the source's statement on the actual data (D0), (D1), (D2') satisfying (A1)-(A7) \
(WeilChernData, with γ of 0FIF): every λ normalised as in (A6) at Spec(k'), i.e. ∫_{Spec(k')} \
(unique by 0FIK), takes the unit class to [k' : k]; the nonvanishing of H^*(Spec(k')) needed to \
cancel the unit is derived from (A3), (A4), (A5)"]
theorem untwistTrace_one_spec_galois
    (lam : tateTwist F 𝔚.tate (𝔚.grade (spec k k') (2 * ((0 : ℕ) : ℤ))) (0 : ℕ) →ₗ[F] F)
    (hlam : 𝔚.traceContract 𝔚.kunneth (spec k k') 0 lam
      (𝔚.γ (prod (spec k k') (spec k k')) 0 (diagonalClass (spec k k') 0)) = 1) :
    𝔚.untwistTrace (spec k k') 0 lam 1 = (Module.finrank k k' : F) := by
  have := 𝔚.nontrivial_H_spec 𝔚.projectiveBundle 𝔚.divisor 𝔚.kunneth k'
  have h := 𝔚.isCohomologicalChernCharacter.untwistTrace_one_smul_spec_galois 𝔚.coproduct
    𝔚.kunneth lam hlam
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  exact (algebraMap F (𝔚.H (spec k k'))).injective h

/-- **Stacks 0FVR for the trace map `∫_X` of the data of Section 0FHA defined by `𝔚`**:
`∫_{Spec(k')} 1 = [k' : k]`. -/
@[stacks 0FVR "the same for the trace map ∫ of 𝔚.toWeilData, the λ of (A6)"]
theorem toWeilData_trace_one_spec_galois :
    𝔚.untwistTrace (spec k k') 0 (𝔚.toWeilData.trace (spec k k') 0
      (isNonemptyEquidimensional_of_dimension_zero
        (FirstChernClassData.topologicalKrullDim_spec_field (k := k) (K' := k')))) 1 =
      (Module.finrank k k' : F) :=
  𝔚.untwistTrace_one_spec_galois k' _
    (𝔚.isCohomologicalChernCharacter.traceContract_toWeilData_trace 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace _ 0 _)

end WeilChernData

end Stacks.WeilCohomology

end
