module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindCapCommuteGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductDedekind
public import StacksFrontier.AlgebraicGeometry.Chow.TripleIntersectionProductExterior
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart

/-!
# Associativity of the intersection product over a Dedekind base

Let `(S, δ)` be as in section 42.63 of the Stacks Project: `S` is locally Noetherian with an open
covering by spectra of Dedekind domains, `δ = 0` at closed points and `δ = 1` elsewhere. Let `X`
be smooth over `S` and let `Y`, `Z`, `W` be locally of finite type over `X`. Section 42.64 defines
the product `α · β = Δ^!(α × β) ∈ CH_*(Y ×_X Z)` of `α ∈ CH_*(Y)` and `β ∈ CH_*(Z)`, where `×` is
the exterior product of Stacks 0FC4 and `Δ^!` the Gysin class of the diagonal of Stacks 0FBR.
**Stacks 0FCA** asserts that it is associative:

  `(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`.

## Main results

* `Stacks.Chow.IsDedekindChowBase.chowPushforwardOfIso_pullbackSymmetry_exteriorProductChow_tmul`
  — the exterior product over a Dedekind base is symmetric on Chow groups.
* `Stacks.Chow.exteriorProductDedekindChow_chowPushforwardOfIso_snd` — it commutes with
  pushforward along an isomorphism in its second variable.
* `Stacks.Chow.IsDedekindChowBase.exteriorProductChow_tmul_cap`,
  `Stacks.Chow.IsDedekindChowBase.exteriorProductChow_cap_tmul` — Stacks 0FC7 at a test morphism,
  in the second and in the first variable, read on a scheme isomorphic to the base change.
* `Stacks.Chow.IsDedekindChowBase.exteriorProductChow_assoc_tmul` — Stacks 0FC8 on Chow classes.
* `Stacks.Chow.IsDedekindChowBase.exteriorProductChow_tmul_diagonalCap`,
  `Stacks.Chow.IsDedekindChowBase.exteriorProductChow_diagonalCap_tmul` —
  `Δ₂₃^!(α × η) = α × Δ^!(η)` and `Δ^!(ξ) × γ = Δ₁₂^!(ξ × γ)`, for every bivariant class of the
  diagonal.
* `Stacks.Chow.IsDedekindChowBase.intersectionProduct_assoc_of_commutesWithEveryClass` —
  associativity for a class of the diagonal whose restriction along `Δ₁₂` commutes with every
  class.
* `Stacks.Chow.IsDedekindChowBase.intersectionProduct_assoc_of_relativeDimension` — Stacks 0FCA
  for `X` of constant relative dimension.
* `Stacks.Chow.IsDedekindChowBase.intersectionProduct_assoc` — **Stacks 0FCA**, for `X` of
  arbitrary relative dimension.

## Implementation notes

The two sides of the equation do not live in the same group on the nose: the left-hand side lies
over `(Y ×_X Z) ×_X W` in degree `(n + m - 1 - d) + l - 1 - d` and the right-hand side over
`Y ×_X (Z ×_X W)` in degree `n + (m + l - 1 - d) - 1 - d`, `d` being the relative dimension of
`X` over `S`. The equation is read after the associator of the triple fibre product and the
matching of the two degrees, as for Stacks 0FC1 in
`Stacks.Chow.IsAssociativeIntersectionProduct`. For `X` of varying relative dimension the product
is formed over each open and closed part `X_e` of constant relative dimension `e`, on the parts
`Y_e = a⁻¹(X_e)`, `Z_e`, `W_e` of `Y`, `Z`, `W` over it.

The cap products `Δ₁₂^! ∩ -` and `Δ₂₃^! ∩ -` are the cap operations of `Δ^!` itself against the
two test morphisms of the triple product `(Y ×_S Z) ×_S W ⟶ X ×_S X`. Bivariant classes are those
of the Gysin system `Stacks.Chow.gysinSystemOfInvertible`.

## References

* [Stacks Project, Tag 0FCA](https://stacks.math.columbia.edu/tag/0FCA)
* [Stacks Project, Section 42.64 (Tag 0FC9)](https://stacks.math.columbia.edu/tag/0FC9)
* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 0FC8](https://stacks.math.columbia.edu/tag/0FC8)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The base change of an isomorphism of test schemes -/

/-- The base change `1 × v : X ×_S T' ⟶ X ×_S T` of an isomorphism `v : T' ⟶ T` is an
isomorphism. -/
instance isIso_testBaseChangeMapOfEq {Y Z T T' : Scheme.{u}} (w : Y ⟶ Z) (g : T ⟶ Z)
    (v : T' ⟶ T) [IsIso v] (m : T' ⟶ Z) (hm : v ≫ g = m) :
    IsIso (testBaseChangeMapOfEq w g v m hm) :=
  (isPullback_testBaseChangeMapOfEq w g v m hm).isIso_snd_of_isIso

/-! ### The exterior product over a Dedekind base: symmetry and isomorphisms -/

section Symmetry

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-- **The exterior product over a Dedekind base is symmetric, on Chow groups.** For
`α ∈ CH_n(X)` and `β ∈ CH_m(Y)` the pushforward of `α × β` along the isomorphism
`X ×_S Y ≅ Y ×_S X` exchanging the two factors is `β × α`, read in degree `n + m - 1`. -/
theorem IsDedekindChowBase.chowPushforwardOfIso_pullbackSymmetry_exteriorProductChow_tmul
    (hS : IsDedekindChowBase C) (α : chowGroup C f n) (β : chowGroup C g m) :
    chowPushforwardOfIso C (pullback.fst f g ≫ f) (pullback.fst g f ≫ g)
        (pullbackSymmetry f g).hom (Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base f g)
        (n + m - 1) (hS.exteriorProductChow f g n m (α ⊗ₜ[ℤ] β)) =
      chowGroupDegreeEquiv C (pullback.fst g f ≫ g) (by ring : m + n - 1 = n + m - 1)
        (hS.exteriorProductChow g f m n (β ⊗ₜ[ℤ] α)) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C f n) α
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C g m) β
  refine (chowPushforwardOfIso_mk C _ _ _ _ _ (exteriorProductDedekindCycles C f g n m a b)).trans
    ?_
  refine (chowGroupDegreeEquiv_mk_eq_mk_of_val C _ _ _ _ ?_).symm
  refine DFunLike.ext _ _ fun z ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, (pullbackSymmetry f g).hom.base w = z :=
    ⟨(pullbackSymmetry f g).inv.base z, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
  rw [properPushforward_apply_image_of_isClosedImmersion,
    ← exteriorProductDedekindCycles_pullbackSymmetry C f g n m a b, ← Scheme.Hom.comp_apply,
    Iso.hom_inv_id]
  rfl

end Symmetry

section SecondFactor

variable {C : ChowSituation.{u}} {X T T' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : T ⟶ C.S) [LocallyOfFiniteType g] (v : T' ⟶ T) [IsIso v] (m' : T' ⟶ C.S)
  [LocallyOfFiniteType m'] (hm : v ≫ g = m') (n k : ℤ)

/-- **The exterior product over a Dedekind base commutes with pushforward along an isomorphism in
its second variable**: `α × v_*β = (1 × v)_*(α × β)` for an isomorphism `v : T' ⟶ T`. -/
theorem exteriorProductDedekindChow_chowPushforwardOfIso_snd
    (hfac : ExteriorProductFactorsThroughRationalEquivalence C f g n k)
    (hfac' : ExteriorProductFactorsThroughRationalEquivalence C f m' n k)
    (α : chowGroup C f n) (β : chowGroup C m' k) :
    exteriorProductDedekindChow C f g n k hfac α (chowPushforwardOfIso C m' g v hm k β) =
      chowPushforwardOfIso C (pullback.fst f m' ≫ f) (pullback.fst f g ≫ f)
        (testBaseChangeMapOfEq f g v m' hm) (by rw [testBaseChangeMapOfEq_fst_assoc]) (n + k - 1)
        (exteriorProductDedekindChow C f m' n k hfac' α β) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C f n) α
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C m' k) β
  rw [chowPushforwardOfIso_mk, exteriorProductDedekindChow_mk_mk,
    exteriorProductDedekindChow_mk_mk, chowPushforwardOfIso_mk,
    properPushforward_exteriorProductDedekindCycles_of_isClosedImmersion]

end SecondFactor

/-! ### Stacks 0FC7 at a test morphism, read on an isomorphic scheme -/

section AtTest

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X Y Z T V : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z) [LocallyOfFiniteType u]
  (hu : u ≫ sZ = sY) (p : ℤ) (c : BivariantClass C (gysinSystemOfInvertible C) sY sZ u hu p)
  (h : T ⟶ Z) [LocallyOfFiniteType h] (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
  (hT : h ≫ sZ = sT) (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (v : V ⟶ T)
  [LocallyOfFiniteType v] (hV : v ≫ sT = sV) (θ : (pullback u h : Scheme.{u}) ≅ V)
  (hθ : θ.hom ≫ v = pullback.snd u h)

omit [LocallyOfFiniteType v] in
/-- **Stacks 0FC7 at a test morphism, in the second variable.** Over a base as in section 42.63,
let `c ∈ A^p(Y ⟶ Z)`, `h : T ⟶ Z`, and `V ≅ Y ×_Z T` over `T`. Then for `α ∈ CH_n(X)` and
`η ∈ CH_m(T)`

  `α × (c ∩ η) = c ∩ (α × η)`   in   `CH_{n + (m - p) - 1}(X ×_S V)`,

where on the left `c ∩ η` is the cap at the test morphism `h`, read on `V`, and on the right the
cap is taken at the test morphism `X ×_S T ⟶ T ⟶ Z` and read on `X ×_S V`. The structure
morphisms of `T` and `V` are arbitrary presentations `sT`, `sV` of the composites. -/
theorem IsDedekindChowBase.exteriorProductChow_tmul_cap (n m : ℤ) (α : chowGroup C sX n)
    (η : chowGroup C sT m) :
    hS.exteriorProductChow sX sV n (m - p)
        (α ⊗ₜ[ℤ] chowPushforwardOfIso C (pullback.fst u h ≫ sY) sV θ.hom
          (pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ) (m - p)
          (c.cap h m (chowGroupCongr C hT.symm m η))) =
      chowPushforwardOfIso C (pullback.fst u (pullback.snd sX sT ≫ h) ≫ sY)
        (pullback.fst sX sV ≫ sX)
        ((pullbackLeftPullbackSndIso u h (pullback.snd sX sT)).inv ≫
          (transportPullbackIso (pullback.snd u h) v θ hθ (pullback.snd sX sT)).hom ≫
            (exteriorCapIso sX sT v hV).hom)
        (by rw [Category.assoc, Category.assoc, exteriorCapIso_hom_comp_structureMorphism]
            simp [pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ])
        (n + (m - p) - 1)
        (chowGroupDegreeEquiv C (pullback.fst u (pullback.snd sX sT ≫ h) ≫ sY)
          (by ring : n + m - 1 - p = n + (m - p) - 1)
          (c.cap (pullback.snd sX sT ≫ h) (n + m - 1)
            (chowGroupCongr C (by rw [Category.assoc, hT, pullback.condition]) (n + m - 1)
              (hS.exteriorProductChow sX sT n m (α ⊗ₜ[ℤ] η))))) := by
  subst hT hV hu
  have key := exteriorProductDedekindChow_cap_comm_of_isDedekindChowBase hS sX sZ u n p α c h m η
  have hθ' := pullbackIso_hom_comp_structureMorphism (u ≫ sZ) sZ u rfl h (h ≫ sZ) rfl
    (v ≫ h ≫ sZ) v rfl θ hθ
  have hMB : inv (mixedCommuteHom sX sZ u h) ≫
      testBaseChangeMapOfEq sX (v ≫ h ≫ sZ) θ.hom (pullback.fst u h ≫ u ≫ sZ) hθ' ≫
        (pullback.fst sX (v ≫ h ≫ sZ) ≫ sX) =
      pullback.fst u (pullback.snd sX (h ≫ sZ) ≫ h) ≫ (u ≫ sZ) := by
    rw [testBaseChangeMapOfEq_fst_assoc, IsIso.inv_comp_eq,
      mixedCommuteHom_comp_structureMorphism]
  have k2 := congrArg (chowPushforwardOfIso C _ (pullback.fst sX (v ≫ h ≫ sZ) ≫ sX)
    (inv (mixedCommuteHom sX sZ u h) ≫
      testBaseChangeMapOfEq sX (v ≫ h ≫ sZ) θ.hom (pullback.fst u h ≫ u ≫ sZ) hθ')
    (by rw [Category.assoc]; exact hMB) (n + (m - p) - 1)) key
  rw [chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _
      (testBaseChangeMapOfEq sX (v ≫ h ≫ sZ) θ.hom (pullback.fst u h ≫ u ≫ sZ) hθ')
      (IsIso.hom_inv_id_assoc _ _) _ (by rw [testBaseChangeMapOfEq_fst_assoc])] at k2
  refine (exteriorProductDedekindChow_chowPushforwardOfIso_snd sX (v ≫ h ≫ sZ) θ.hom
    (pullback.fst u h ≫ u ≫ sZ) hθ' n (m - p) _
    (hS.exteriorProductFactorsThroughRationalEquivalence _ _ _ _) α (c.cap h m η)).trans ?_
  refine k2.trans (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  rw [IsIso.inv_comp_eq]
  have hsnd : pullback.snd sX (pullback.fst u h ≫ u ≫ sZ) = mixedCommuteHom sX sZ u h ≫
      (pullbackLeftPullbackSndIso u h (pullback.snd sX (h ≫ sZ))).inv ≫
        pullback.fst (pullback.snd u h) (pullback.snd sX (h ≫ sZ)) := by
    apply pullback.hom_ext <;> simp
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, testBaseChangeMapOfEq_snd, exteriorCapIso_hom_snd,
      transportPullbackIso_hom_fst]
    rw [hsnd, Category.assoc, Category.assoc]

omit [LocallyOfFiniteType v] in
/-- **Stacks 0FC7 at a test morphism, in the first variable.** With the notation of
`Stacks.Chow.IsDedekindChowBase.exteriorProductChow_tmul_cap`, for `ξ ∈ CH_m(T)` and
`γ ∈ CH_n(X)`

  `(c ∩ ξ) × γ = c ∩ (ξ × γ)`   in   `CH_{(m - p) + n - 1}(V ×_S X)`,

the cap on the right being taken at the test morphism `T ×_S X ⟶ T ⟶ Z`. -/
theorem IsDedekindChowBase.exteriorProductChow_cap_tmul (m n : ℤ) (ξ : chowGroup C sT m)
    (γ : chowGroup C sX n) :
    hS.exteriorProductChow sV sX (m - p) n
        (chowPushforwardOfIso C (pullback.fst u h ≫ sY) sV θ.hom
          (pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ) (m - p)
          (c.cap h m (chowGroupCongr C hT.symm m ξ)) ⊗ₜ[ℤ] γ) =
      chowPushforwardOfIso C (pullback.fst u (pullback.fst sT sX ≫ h) ≫ sY)
        (pullback.fst sV sX ≫ sV)
        ((pullbackLeftPullbackSndIso u h (pullback.fst sT sX)).inv ≫
          (transportPullbackIso (pullback.snd u h) v θ hθ (pullback.fst sT sX)).hom ≫
            (exteriorCapFstIso sX sT v hV).hom)
        (by rw [Category.assoc, Category.assoc, exteriorCapFstIso_hom_comp_structureMorphism]
            simp [pullbackIso_hom_comp_structureMorphism sY sZ u hu h sT hT sV v hV θ hθ])
        ((m - p) + n - 1)
        (chowGroupDegreeEquiv C (pullback.fst u (pullback.fst sT sX ≫ h) ≫ sY)
          (by ring : m + n - 1 - p = (m - p) + n - 1)
          (c.cap (pullback.fst sT sX ≫ h) (m + n - 1)
            (chowGroupCongr C (by rw [Category.assoc, hT]) (m + n - 1)
              (hS.exteriorProductChow sT sX m n (ξ ⊗ₜ[ℤ] γ))))) := by
  subst hT hV hu
  have hsymV := hS.chowPushforwardOfIso_pullbackSymmetry_exteriorProductChow_tmul sX
    (v ≫ h ≫ sZ) n (m - p) γ
    (chowPushforwardOfIso C (pullback.fst u h ≫ (u ≫ sZ)) (v ≫ h ≫ sZ) θ.hom
      (pullbackIso_hom_comp_structureMorphism (u ≫ sZ) sZ u rfl h (h ≫ sZ) rfl (v ≫ h ≫ sZ) v
        rfl θ hθ) (m - p) (c.cap h m ξ))
  have h2 := hS.exteriorProductChow_tmul_cap sX (u ≫ sZ) sZ u rfl p c h (h ≫ sZ) rfl
    (v ≫ h ≫ sZ) v rfl θ hθ n m γ ξ
  have hsymT := hS.chowPushforwardOfIso_pullbackSymmetry_exteriorProductChow_tmul (h ≫ sZ) sX
    m n ξ γ
  have hι : (pullbackSymmetry (h ≫ sZ) sX).hom ≫ (pullback.snd sX (h ≫ sZ) ≫ h) =
      pullback.fst (h ≫ sZ) sX ≫ h := by
    rw [pullbackSymmetry_hom_comp_snd_assoc]
  have hcap := BivariantClass.cap_chowPushforwardOfTestIso C (gysinSystemOfInvertible C)
    (u ≫ sZ) sZ u rfl p c (pullback.snd sX (h ≫ sZ) ≫ h)
    (pullbackSymmetry (h ≫ sZ) sX).hom hι (m + n - 1)
    (chowGroupCongr C (Category.assoc _ _ _).symm (m + n - 1)
      (hS.exteriorProductChow (h ≫ sZ) sX m n (ξ ⊗ₜ[ℤ] γ)))
  have hD : c.cap (pullback.snd sX (h ≫ sZ) ≫ h) (n + m - 1)
      (chowGroupCongr C (by rw [Category.assoc, pullback.condition]) (n + m - 1)
        (hS.exteriorProductChow sX (h ≫ sZ) n m (γ ⊗ₜ[ℤ] ξ))) ≍
      chowPushforwardOfIso C (pullback.fst u (pullback.fst (h ≫ sZ) sX ≫ h) ≫ (u ≫ sZ))
        (pullback.fst u (pullback.snd sX (h ≫ sZ) ≫ h) ≫ (u ≫ sZ))
        (pullbackBaseChangeOfTestIso u (pullbackSymmetry (h ≫ sZ) sX).hom hι).hom
        (pullbackBaseChangeOfTestIso_hom_comp u _ hι (u ≫ sZ)) (m + n - 1 - p)
        (c.cap (pullback.fst (h ≫ sZ) sX ≫ h) (m + n - 1)
          (chowGroupCongr C (Category.assoc _ _ _).symm (m + n - 1)
            (hS.exteriorProductChow (h ≫ sZ) sX m n (ξ ⊗ₜ[ℤ] γ)))) := by
    rw [← hcap]
    refine BivariantClass.cap_heq c _ (by ring) ?_
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    refine ((heq_of_eq hsymT).trans (chowGroupDegreeEquiv_heq C _ _ _)).symm.trans ?_
    exact chowPushforwardOfIso_heq _ _ _ (by rw [Category.assoc])
      (by rw [Category.assoc, pullback.condition]) rfl (chowGroupCongr_heq C _ _ _).symm
  have hmor : (pullbackBaseChangeOfTestIso u (pullbackSymmetry (h ≫ sZ) sX).hom hι).hom ≫
      ((pullbackLeftPullbackSndIso u h (pullback.snd sX (h ≫ sZ))).inv ≫
        (transportPullbackIso (pullback.snd u h) v θ hθ (pullback.snd sX (h ≫ sZ))).hom ≫
          (exteriorCapIso sX (h ≫ sZ) v rfl).hom) ≫ (pullbackSymmetry sX (v ≫ h ≫ sZ)).hom =
      (pullbackLeftPullbackSndIso u h (pullback.fst (h ≫ sZ) sX)).inv ≫
        (transportPullbackIso (pullback.snd u h) v θ hθ (pullback.fst (h ≫ sZ) sX)).hom ≫
          (exteriorCapFstIso sX (h ≫ sZ) v rfl).hom := by
    have hfst : (pullbackBaseChangeOfTestIso u (pullbackSymmetry (h ≫ sZ) sX).hom hι).hom ≫
        (pullbackLeftPullbackSndIso u h (pullback.snd sX (h ≫ sZ))).inv ≫
          pullback.fst (pullback.snd u h) (pullback.snd sX (h ≫ sZ)) =
        (pullbackLeftPullbackSndIso u h (pullback.fst (h ≫ sZ) sX)).inv ≫
          pullback.fst (pullback.snd u h) (pullback.fst (h ≫ sZ) sX) := by
      apply pullback.hom_ext <;> simp
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, exteriorCapIso_hom_snd,
        exteriorCapFstIso_hom_fst, transportPullbackIso_hom_fst]
      rw [reassoc_of% hfst]
    · simp
  have hξ : chowGroupCongr C (rfl : h ≫ sZ = h ≫ sZ) m ξ = ξ := rfl
  rw [hξ] at h2
  refine eq_of_heq (((heq_of_eq hsymV).trans (chowGroupDegreeEquiv_heq C _ _ _)).symm.trans ?_)
  rw [h2, chowPushforwardOfIso_comp_apply]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    ((chowGroupDegreeEquiv_heq C _ _ _).trans hD)).trans ?_
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_congr_apply C _ _ _ _ hmor]
  exact chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    (chowGroupDegreeEquiv_heq C _ _ _).symm

end AtTest

/-! ### Associativity of the exterior product, on Chow groups -/

section Assoc

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X Y Z : Scheme.{u}}
  (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g]
  (h : Z ⟶ C.S) [LocallyOfFiniteType h] (n m l : ℤ)

/-- **Stacks 0FC8, on Chow classes.** Over a base as in section 42.63, for `α ∈ CH_n(X)`,
`β ∈ CH_m(Y)` and `γ ∈ CH_l(Z)`, the pushforward of `(α × β) × γ` along the associator
`(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)` is `α × (β × γ)`, the two degrees `(n + m - 1) + l - 1` and
`n + (m + l - 1) - 1` being matched. -/
theorem IsDedekindChowBase.exteriorProductChow_assoc_tmul (α : chowGroup C f n)
    (β : chowGroup C g m) (γ : chowGroup C h l) :
    chowGroupDegreeEquiv C (pullback.fst f (pullback.fst g h ≫ g) ≫ f)
        (exteriorProductDedekind_degree_assoc n m l)
        (chowPushforwardOfIso C (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
          (tripleProductAssoc_hom_comp_base f g h) (n + m - 1 + l - 1)
          (hS.exteriorProductChow (pullback.fst f g ≫ f) h (n + m - 1) l
            (hS.exteriorProductChow f g n m (α ⊗ₜ[ℤ] β) ⊗ₜ[ℤ] γ))) =
      hS.exteriorProductChow f (pullback.fst g h ≫ g) n (m + l - 1)
        (α ⊗ₜ[ℤ] hS.exteriorProductChow g h m l (β ⊗ₜ[ℤ] γ)) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C f n) α
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C g m) β
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C h l) γ
  have key := exteriorProductDedekindChow_assoc_of_isDedekindChowBase C f g h n m l hS
    (QuotientAddGroup.mk' (rationalEquivalences C f n) a)
    (QuotientAddGroup.mk' (rationalEquivalences C g m) b)
    (QuotientAddGroup.mk' (rationalEquivalences C h l) c)
  exact eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans
    ((eqRec_heq _ _).symm.trans (heq_of_eq key)))

end Assoc

/-! ### Exterior products and capping with the diagonal -/

/-- The comparison `Y ×_X Z ⟶ Y ×_S Z` lies over the structure morphism of `Y ×_X Z ⟶ X`. -/
private theorem fibreProductToExteriorProduct_comp_fst_comp
    {C : ChowSituation.{u}} {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) (a : Y ⟶ X)
    (b : Z ⟶ X) :
    fibreProductToExteriorProduct sX a b ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) =
      (pullback.fst a b ≫ a) ≫ sX := by
  rw [fibreProductToExteriorProduct_comp_structure, Category.assoc]

section Chain

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X Y Z W : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (a : Y ⟶ X) [LocallyOfFiniteType a]
  (b : Z ⟶ X) [LocallyOfFiniteType b] (g : W ⟶ X) [LocallyOfFiniteType g] (d : ℤ)
  (Dc : BivariantClass C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
    (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) d)

/-- **Capping with the diagonal in the second variable, `Δ₂₃^!(α × η) = α × Δ^!(η)`**, over a
base as in section 42.63 and for every bivariant class `Δ^!` of the diagonal of `X`. The class
`Δ^!(η)` lives on `Z ×_X W` and `Δ₂₃^!` is the cap of `Δ^!` against the test morphism
`Y ×_S (Z ×_S W) ⟶ Z ×_S W ⟶ X ×_S X`, read through
`Stacks.Chow.secondPartialDiagonalPullbackIso`. -/
theorem IsDedekindChowBase.exteriorProductChow_tmul_diagonalCap (n k : ℤ)
    (α : chowGroup C (a ≫ sX) n)
    (η : chowGroup C (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) k) :
    hS.exteriorProductChow (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) n (k - d)
        (α ⊗ₜ[ℤ] chowGroupCongr C (Category.assoc (pullback.fst b g) b sX).symm (k - d)
          (properChowPushforward C
            (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX b g) ≫ sX)
            (pullback.fst b g ≫ (b ≫ sX)) (pullbackDiagonalMapIdIso b g sX).hom
            (pullbackDiagonalMapIdIso_hom_comp_structure C sX b g) (k - d)
            (properPushforwardDescends C _ _ _ _ _)
            (Dc.cap (exteriorToSelfProduct C sX b g) k
              (chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX b g).symm
                k η)))) =
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫ sX)
        (pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ (a ≫ sX))
        (secondPartialDiagonalPullbackIso sX a b g).hom
        (secondPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + (k - d) - 1)
        (chowGroupDegreeEquiv C
          (pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫ sX)
          (by ring : n + k - 1 - d = n + (k - d) - 1)
          (Dc.cap (secondPartialDiagonalTest sX a b g) (n + k - 1)
            (chowGroupCongr C (secondPartialDiagonalTest_comp_base sX a b g).symm (n + k - 1)
              (hS.exteriorProductChow (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) n k
                (α ⊗ₜ[ℤ] η))))) := by
  have key := hS.exteriorProductChow_tmul_cap (a ≫ sX) sX (selfProductStructure C sX)
    (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) d Dc
    (exteriorToSelfProduct C sX b g) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX))
    (exteriorToSelfProduct_comp_selfProductStructure C sX b g) ((pullback.fst b g ≫ b) ≫ sX)
    (fibreProductToExteriorProduct sX b g)
    (fibreProductToExteriorProduct_comp_fst_comp sX b g) (pullbackDiagonalMapIdIso b g sX)
    (pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct sX b g) n k α η
  rw [properChowPushforward_eq_chowPushforwardOfIso, chowGroupCongr_chowPushforwardOfIso_target]
  refine key.trans (chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _)
  apply pullback.hom_ext
  · rw [secondPartialDiagonalPullbackIso_hom_fst]
    simp
  · rw [← cancel_mono (fibreProductToExteriorProduct sX b g)]
    simp only [Category.assoc, secondPartialDiagonalPullbackIso_hom_snd,
      exteriorCapIso_hom_snd_assoc]
    rw [pullback.condition (f := fibreProductToExteriorProduct sX b g)
      (g := pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)))]
    simp

/-- **Capping with the diagonal in the first variable, `Δ^!(ξ) × γ = Δ₁₂^!(ξ × γ)`**, over a
base as in section 42.63 and for every bivariant class `Δ^!` of the diagonal of `X`, read on
`Y ×_X Z` through `Stacks.Chow.firstPartialDiagonalPullbackIso`. -/
theorem IsDedekindChowBase.exteriorProductChow_diagonalCap_tmul (k l : ℤ)
    (ξ : chowGroup C (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) k)
    (γ : chowGroup C (g ≫ sX) l) :
    hS.exteriorProductChow ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) (k - d) l
        (chowGroupCongr C (Category.assoc (pullback.fst a b) a sX).symm (k - d)
          (properChowPushforward C
            (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX)
            (pullback.fst a b ≫ (a ≫ sX)) (pullbackDiagonalMapIdIso a b sX).hom
            (pullbackDiagonalMapIdIso_hom_comp_structure C sX a b) (k - d)
            (properPushforwardDescends C _ _ _ _ _)
            (Dc.cap (exteriorToSelfProduct C sX a b) k
              (chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm
                k ξ))) ⊗ₜ[ℤ] γ) =
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX)
        (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫ ((pullback.fst a b ≫ a) ≫ sX))
        (firstPartialDiagonalPullbackIso sX a b g).hom
        (firstPartialDiagonalPullbackIso_hom_comp_base sX a b g) (k - d + l - 1)
        (chowGroupDegreeEquiv C
          (pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX)
          (by ring : k + l - 1 - d = k - d + l - 1)
          (Dc.cap (firstPartialDiagonalTest sX a b g) (k + l - 1)
            (chowGroupCongr C (firstPartialDiagonalTest_comp_base sX a b g).symm (k + l - 1)
              (hS.exteriorProductChow (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) k l
                (ξ ⊗ₜ[ℤ] γ))))) := by
  have key := hS.exteriorProductChow_cap_tmul (g ≫ sX) sX (selfProductStructure C sX)
    (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) d Dc
    (exteriorToSelfProduct C sX a b) (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
    (exteriorToSelfProduct_comp_selfProductStructure C sX a b) ((pullback.fst a b ≫ a) ≫ sX)
    (fibreProductToExteriorProduct sX a b)
    (fibreProductToExteriorProduct_comp_fst_comp sX a b) (pullbackDiagonalMapIdIso a b sX)
    (pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct sX a b) k l ξ γ
  rw [properChowPushforward_eq_chowPushforwardOfIso, chowGroupCongr_chowPushforwardOfIso_target]
  refine key.trans (chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _)
  apply pullback.hom_ext
  · rw [← cancel_mono (fibreProductToExteriorProduct sX a b)]
    simp only [Category.assoc, firstPartialDiagonalPullbackIso_hom_fst,
      exteriorCapFstIso_hom_fst_assoc]
    rw [pullback.condition (f := fibreProductToExteriorProduct sX a b)
      (g := pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX))]
    simp
  · rw [firstPartialDiagonalPullbackIso_hom_snd]
    simp

end Chain

/-- Transport along an equality of structure morphisms preserves heterogeneous equality. -/
private theorem chowGroupCongr_heq_congr (C : ChowSituation.{u}) {X : Scheme.{u}}
    {q₁ q₂ q₃ q₄ : X ⟶ C.S} [LocallyOfFiniteType q₁] [LocallyOfFiniteType q₂]
    [LocallyOfFiniteType q₃] [LocallyOfFiniteType q₄] (h₁ : q₁ = q₂) (h₂ : q₃ = q₄) {k k' : ℤ}
    {α : chowGroup C q₁ k} {α' : chowGroup C q₃ k'} (h : α ≍ α') :
    chowGroupCongr C h₁ k α ≍ chowGroupCongr C h₂ k' α' :=
  (chowGroupCongr_heq C _ _ _).trans (h.trans (chowGroupCongr_heq C _ _ _).symm)

/-- Transport along an equality of degrees preserves heterogeneous equality. -/
private theorem chowGroupDegreeEquiv_heq_congr (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {k₁ k₂ k₃ k₄ : ℤ} (h₁ : k₁ = k₂) (h₂ : k₃ = k₄)
    {α : chowGroup C sX k₁} {α' : chowGroup C sX k₃} (h : α ≍ α') :
    chowGroupDegreeEquiv C sX h₁ α ≍ chowGroupDegreeEquiv C sX h₂ α' :=
  (chowGroupDegreeEquiv_heq C _ _ _).trans (h.trans (chowGroupDegreeEquiv_heq C _ _ _).symm)

/-! ### Associativity -/

section Main

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X Y Z W : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (a : Y ⟶ X) [LocallyOfFiniteType a]
  (b : Z ⟶ X) [LocallyOfFiniteType b] (g : W ⟶ X) [LocallyOfFiniteType g]

/-- **Associativity of the intersection product over a Dedekind base, for a class of the diagonal
whose restriction along `Δ₁₂` commutes with every class.** Let `(S, δ)` be as in section 42.63,
`X` locally of finite type over `S` with a bivariant class `Δ^! ∈ A^d(X ⟶ X ×_S X)`, and `Y`, `Z`,
`W` locally of finite type over `X`. If the restriction (Stacks 0F9Z) of `Δ^!` along the test
morphism `Δ₁₂ : (Y ×_S Z) ×_S W ⟶ X ×_S X` commutes with every bivariant class over it, then for
`α ∈ CH_n(Y)`, `β ∈ CH_m(Z)` and `γ ∈ CH_l(W)`

  `(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

the left-hand side pushed forward along the associator of the triple fibre product over `X` and
the two degrees `(n + m - 1 - d) + l - 1 - d` and `n + (m + l - 1 - d) - 1 - d` matched. -/
theorem IsDedekindChowBase.intersectionProduct_assoc_of_commutesWithEveryClass (d : ℤ)
    (Dc : BivariantClass C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) d)
    (hres : (bivariantRestriction C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX)
      (firstPartialDiagonalTest sX a b g) d
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) Dc).CommutesWithEveryClass)
    (n m l : ℤ) (α : chowGroup C (a ≫ sX) n) (β : chowGroup C (b ≫ sX) m)
    (γ : chowGroup C (g ≫ sX) l) :
    chowGroupDegreeEquiv C (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
        (by ring : n + m - 1 - d + l - 1 - d = n + (m + l - 1 - d) - 1 - d)
        (properChowPushforward C
          (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX)) (tripleProductAssoc a b g).hom
          (tripleProductAssoc_hom_comp_structureMorphism C sX a b g) (n + m - 1 - d + l - 1 - d)
          (properPushforwardDescends C _ _ _ _ _)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX (pullback.fst a b ≫ a) g d Dc
            (n + m - 1 - d) l
            (chowGroupCongr C (Category.assoc (pullback.fst a b) a sX).symm (n + m - 1 - d)
              (hS.intersectionProduct (gysinSystemOfInvertible C) sX a b d Dc n m (α ⊗ₜ[ℤ] β))
              ⊗ₜ[ℤ] γ))) =
      hS.intersectionProduct (gysinSystemOfInvertible C) sX a (pullback.fst b g ≫ b) d Dc n
        (m + l - 1 - d)
        (α ⊗ₜ[ℤ] chowGroupCongr C (Category.assoc (pullback.fst b g) b sX).symm (m + l - 1 - d)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX b g d Dc m l (β ⊗ₜ[ℤ] γ))) := by
  have hcomm := diagonalGysinCommuteOnTripleProduct_of_commutesWithEveryClass C
    (properPushforwardDescends C) sX a b g d Dc n (m - 1) (l - 1) hres
  simp only [IsDedekindChowBase.intersectionProduct_apply]
  rw [hS.exteriorProductChow_diagonalCap_tmul sX a b g d Dc (n + m - 1) l,
    hS.exteriorProductChow_tmul_diagonalCap sX a b g d Dc n (m + l - 1),
    ← hS.exteriorProductChow_assoc_tmul (a ≫ sX) (b ≫ sX) (g ≫ sX) n m l]
  generalize hS.exteriorProductChow (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX)
    (n + m - 1) l (hS.exteriorProductChow (a ≫ sX) (b ≫ sX) n m (α ⊗ₜ[ℤ] β) ⊗ₜ[ℤ] γ) = x
  have H := hcomm (chowGroupDegreeEquiv C _ (by ring : n + m - 1 + l - 1 = n + (m - 1) + (l - 1)) x)
  simp only [properChowPushforward_eq_chowPushforwardOfIso, AddEquiv.coe_toAddMonoidHom] at H ⊢
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq H).trans ?_))
  · refine chowGroupDegreeEquiv_heq_congr C _ _ _ ?_
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    refine BivariantClass.cap_heq Dc _ (by ring) ?_
    refine chowGroupCongr_heq_congr C _ _ ?_
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    refine chowGroupDegreeEquiv_heq_congr C _ _ _ ?_
    refine BivariantClass.cap_heq Dc _ (by ring) ?_
    refine chowGroupCongr_heq_congr C _ _ ?_
    exact (chowGroupDegreeEquiv_heq C _ _ _).symm
  · refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    refine BivariantClass.cap_heq Dc _ (by ring) ?_
    refine chowGroupCongr_heq_congr C _ _ ?_
    refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
    refine chowGroupDegreeEquiv_heq_congr C _ _ _ ?_
    refine BivariantClass.cap_heq Dc _ (by ring) ?_
    refine chowGroupCongr_heq_congr C _ _ ?_
    refine chowGroupDegreeEquiv_heq_congr C _ _ _ ?_
    exact chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ (chowGroupDegreeEquiv_heq C _ _ _)

/-- **Stacks 0FCA for `X` of constant relative dimension.** Let `(S, δ)` be as in section 42.63:
`S` locally Noetherian with an open covering by spectra of Dedekind domains, `δ = 0` at closed
points and `δ = 1` elsewhere. Let `X` be smooth over `S` of constant relative dimension `d`, and
let `Y`, `Z`, `W` be locally of finite type over `X`. Form the intersection product
`α · β = Δ^!(α × β)` of section 42.64, `Stacks.Chow.IsDedekindChowBase.intersectionProduct`,
with the Gysin class `Δ^! ∈ A^d(X ⟶ X ×_S X)` of the diagonal of Stacks 0FBR,
`Stacks.Chow.diagonalGysinClass`, read with its source over `S` through `s_X`. Then for
`α ∈ CH_n(Y)`, `β ∈ CH_m(Z)` and `γ ∈ CH_l(W)`

  `(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

read through the associator `(Y ×_X Z) ×_X W ≅ Y ×_X (Z ×_X W)` and the matching of the degrees
`(n + m - 1 - d) + l - 1 - d` and `n + (m + l - 1 - d) - 1 - d`. -/
theorem IsDedekindChowBase.intersectionProduct_assoc_of_relativeDimension [Smooth sX] {d : ℕ}
    (hd : RelativeDimension sX d) (n m l : ℤ) (α : chowGroup C (a ≫ sX) n)
    (β : chowGroup C (b ≫ sX) m) (γ : chowGroup C (g ≫ sX) l) :
    chowGroupDegreeEquiv C (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
        (by ring : n + m - 1 - d + l - 1 - d = n + (m + l - 1 - d) - 1 - d)
        (properChowPushforward C
          (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX)) (tripleProductAssoc a b g).hom
          (tripleProductAssoc_hom_comp_structureMorphism C sX a b g) (n + m - 1 - d + l - 1 - d)
          (properPushforwardDescends C _ _ _ _ _)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX (pullback.fst a b ≫ a) g d
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure C sX) rfl (d : ℤ)
              (diagonalGysinClass C sX sX hd))
            (n + m - 1 - d) l
            (chowGroupCongr C (Category.assoc (pullback.fst a b) a sX).symm (n + m - 1 - d)
              (hS.intersectionProduct (gysinSystemOfInvertible C) sX a b d
                (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
                  (diagonal_comp_selfProductStructure C sX) rfl (d : ℤ)
                  (diagonalGysinClass C sX sX hd)) n m (α ⊗ₜ[ℤ] β))
              ⊗ₜ[ℤ] γ))) =
      hS.intersectionProduct (gysinSystemOfInvertible C) sX a (pullback.fst b g ≫ b) d
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
          (diagonal_comp_selfProductStructure C sX) rfl (d : ℤ) (diagonalGysinClass C sX sX hd))
        n (m + l - 1 - d)
        (α ⊗ₜ[ℤ] chowGroupCongr C (Category.assoc (pullback.fst b g) b sX).symm (m + l - 1 - d)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX b g d
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure C sX) rfl (d : ℤ)
              (diagonalGysinClass C sX sX hd)) m l (β ⊗ₜ[ℤ] γ))) :=
  hS.intersectionProduct_assoc_of_commutesWithEveryClass sX a b g d _
    ((commutesWithEveryClass_bivariantRestriction_bivariantClassCongrBase_iff _ _ _ _ _).2
      (diagonalGysinClass_bivariantRestriction_commutesWithEveryClass _ sX sX hd _)) n m l α β γ

open Stacks.WeilCohomology (partBase relativeDimension_partBase)

/-- The part `X_e` of `X` of relative dimension `e`, over `S`. -/
local notation "X[" e "]" => partBase sX e

/-- The restriction `a_e : Y_e ⟶ X_e` of a morphism `a : Y ⟶ X` to the parts over `X_e`. -/
local notation "π[" a ", " e "]" => dimPartOverHom sX a e

/-- The Gysin class `Δ^! ∈ A^e(X_e ⟶ X_e ×_S X_e)` of the diagonal of the part `X_e`. -/
local notation "Δ[" e "]" => bivariantClassCongrBase _ (gysinSystemOfInvertible _)
  (pullback.diagonal (partBase sX e)) (diagonal_comp_selfProductStructure _ (partBase sX e)) rfl
  ((e : ℕ) : ℤ) (diagonalGysinClass _ (partBase sX e) (partBase sX e)
    (relativeDimension_partBase sX e))

/-- The restriction of a class `α ∈ CH_n(Y)` to the part `Y_e` of `Y` over `X_e`. -/
local notation "res[" a ", " e ", " n ", " α "]" => chowGroupDimPartOver _ sX a e n α

/-- **Stacks 0FCA.** Let `(S, δ)` be as in section 42.63: `S` locally Noetherian with an open
covering by spectra of Dedekind domains, `δ = 0` at closed points and `δ = 1` elsewhere. Let `X`
be smooth over `S`, of arbitrary and not necessarily constant relative dimension, and let `Y`,
`Z`, `W` be locally of finite type over `X`. As section 42.64 prescribes, the intersection product
`α · β = Δ^!(α × β)` is formed over the open and closed parts `X_e` of `X` where `X ⟶ S` has
relative dimension `e` (`Stacks.WeilCohomology.dimPart`), with the Gysin class
`Δ^! ∈ A^e(X_e ⟶ X_e ×_S X_e)` of the diagonal of Stacks 0FBR: for `α ∈ CH_n(Y)` and
`β ∈ CH_m(Z)` its component over `X_e` is `α|_{Y_e} · β|_{Z_e} ∈ CH_{n+m-1-e}(Y_e ×_{X_e} Z_e)`,
where `Y_e = a⁻¹(X_e)` and `Z_e = b⁻¹(X_e)` are the parts of `Y` and `Z` over `X_e`
(`Stacks.Chow.chowGroupDimPartOver`). Then for `γ ∈ CH_l(W)`

  `(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

component by component, read through the associator of the triple fibre product over `X_e` and
the matching of the degrees `(n + m - 1 - e) + l - 1 - e` and `n + (m + l - 1 - e) - 1 - e`. -/
@[stacks 0FCA "the whole statement (α·β)·γ = α·(β·γ) in CH_*(Y ×_X Z ×_X W) for X smooth over a \
base as in section 42.63 (zero-dimensional components allowed), of arbitrary relative dimension, \
Y, Z, W locally of finite type over X and arbitrary α, β, γ; the product is Δ^!(α × β) with Δ^! \
the Gysin class of the diagonal of Stacks 0FBR and × the exterior product of Stacks 0FC4, formed \
on the open and closed parts of X of constant relative dimension as in section 42.64, bivariant \
classes those of `Stacks.Chow.gysinSystemOfInvertible`"]
theorem IsDedekindChowBase.intersectionProduct_assoc [Smooth sX] (n m l : ℤ)
    (α : chowGroup C (a ≫ sX) n) (β : chowGroup C (b ≫ sX) m) (γ : chowGroup C (g ≫ sX) l)
    (e : ℕ) :
    chowGroupDegreeEquiv C
        (pullback.fst π[a, e] (pullback.fst π[b, e] π[g, e] ≫ π[b, e]) ≫ (π[a, e] ≫ X[e]))
        (by ring : n + m - 1 - e + l - 1 - e = n + (m + l - 1 - e) - 1 - e)
        (properChowPushforward C
          (pullback.fst (pullback.fst π[a, e] π[b, e] ≫ π[a, e]) π[g, e] ≫
            ((pullback.fst π[a, e] π[b, e] ≫ π[a, e]) ≫ X[e]))
          (pullback.fst π[a, e] (pullback.fst π[b, e] π[g, e] ≫ π[b, e]) ≫ (π[a, e] ≫ X[e]))
          (tripleProductAssoc π[a, e] π[b, e] π[g, e]).hom
          (tripleProductAssoc_hom_comp_structureMorphism C X[e] π[a, e] π[b, e] π[g, e])
          (n + m - 1 - e + l - 1 - e) (properPushforwardDescends C _ _ _ _ _)
          (hS.intersectionProduct (gysinSystemOfInvertible C) X[e]
            (pullback.fst π[a, e] π[b, e] ≫ π[a, e]) π[g, e] e Δ[e] (n + m - 1 - e) l
            (chowGroupCongr C (Category.assoc (pullback.fst π[a, e] π[b, e]) π[a, e] X[e]).symm
              (n + m - 1 - e)
              (hS.intersectionProduct (gysinSystemOfInvertible C) X[e] π[a, e] π[b, e] e Δ[e] n m
                (res[a, e, n, α] ⊗ₜ[ℤ] res[b, e, m, β])) ⊗ₜ[ℤ] res[g, e, l, γ]))) =
      hS.intersectionProduct (gysinSystemOfInvertible C) X[e] π[a, e]
        (pullback.fst π[b, e] π[g, e] ≫ π[b, e]) e Δ[e] n (m + l - 1 - e)
        (res[a, e, n, α] ⊗ₜ[ℤ]
          chowGroupCongr C (Category.assoc (pullback.fst π[b, e] π[g, e]) π[b, e] X[e]).symm
            (m + l - 1 - e)
            (hS.intersectionProduct (gysinSystemOfInvertible C) X[e] π[b, e] π[g, e] e Δ[e] m l
              (res[b, e, m, β] ⊗ₜ[ℤ] res[g, e, l, γ]))) :=
  hS.intersectionProduct_assoc_of_relativeDimension (partBase sX e) (dimPartOverHom sX a e)
    (dimPartOverHom sX b e) (dimPartOverHom sX g e) (relativeDimension_partBase sX e) n m l _ _ _

end Main

end Stacks.Chow

end
