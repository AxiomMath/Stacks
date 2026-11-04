module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveGaloisCoverKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveTorsorDescent

/-!
# Killing a cohomology class of a curve over a field extension ([Stacks, Tag 0EYT])

Let `K/k` be a field extension, `X` a smooth affine curve over `k` with a rational point `x`,
`F` an abelian sheaf on `Spec(K)_étale` annihilated by an integer `n` invertible in `k`, and
`ξ ∈ H^q(X_K, F)` with `q > 0`. Then there are finite extensions `K'/K` and `k'/k` with
`k' ⊆ K'` and a finite étale Galois cover `Z ⟶ X_{k'}`, whose group has order dividing a power of
`n` and which is split over `x_{k'}`, such that `ξ` dies in `H^q(Z_{K'}, F)`.

The case `q > 1` is `Stacks.EtaleCohomology.exists_galoisCover_of_one_lt`. For `q = 1`, let `Ω`
be an algebraic closure of `K` and `\bar k ⊆ Ω` the algebraic closure of `k`. The restriction of
`ξ` to `X_Ω` comes from a class `ζ ∈ H^1(X_{\bar k}, S)` with `S` finite and annihilated by `n`
(`Stacks.EtaleCohomology.exists_kbar_class`), which comes from a class `ζ_E ∈ H^1(X_E, S)` for a
finite subextension `E` (`Stacks.EtaleCohomology.exists_finite_stage_class`). A Galois cover
`Z ⟶ X_{k'}` split over `x_{k'}` kills `ζ_E`
(`Stacks.EtaleCohomology.exists_galoisCover_restriction_eq_zero`), hence `ξ` dies on `Z_Ω`. With
`L₀ ⊆ Ω` a finite extension of `K` containing `k'`, the class `ξ|_{Z_{L₀}}` dies on `Z_Ω`, hence
on `Z_{K'}` for a finite extension `K'/L₀` ([Stacks, Tag 03Q6]).

## Main results

* `Stacks.EtaleCohomology.exists_galoisCover_killing_class` — [Stacks, Tag 0EYT].

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

section MapTo

variable {X₁ X₂ X₃ X₄ : Scheme.{u}}

/-- The cohomology map of a morphism factoring through `h` kills the classes whose restriction
along `h` vanishes. -/
theorem etaleCohomologyMapTo_eq_zero_of_restriction_eq_zero (k₁ : X₃ ⟶ X₂) (h : X₂ ⟶ X₁)
    (k : X₃ ⟶ X₁) (hk : k = k₁ ≫ h) {A : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {C : Sheaf X₃.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ C) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p)
    (hx : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} h A p x = 0) :
    etaleCohomologyMapTo k w p x = 0 := by
  rw [etaleCohomologyMapTo_eq_comp_restriction k₁ h k hk, hx, map_zero]

/-- A cohomology map, after a restriction, after a cohomology map, is the cohomology map of the
composite. -/
theorem exists_etaleCohomologyMapTo_restriction_etaleCohomologyMapTo (k₁ : X₄ ⟶ X₃)
    (h : X₃ ⟶ X₂) (k₂ : X₂ ⟶ X₁) {A : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {C : Sheaf X₄.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w₂ : (etaleAbelianInverseImage.{u, u + 1} k₂).obj A ⟶ B)
    (W : (etaleAbelianInverseImage.{u, u + 1} k₁).obj
      ((etaleAbelianInverseImage.{u, u + 1} h).obj B) ⟶ C) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    ∃ W' : (etaleAbelianInverseImage.{u, u + 1} (k₁ ≫ h ≫ k₂)).obj A ⟶ C,
      etaleCohomologyMapTo k₁ W p
          (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} h B p (etaleCohomologyMapTo k₂ w₂ p x)) =
        etaleCohomologyMapTo (k₁ ≫ h ≫ k₂) W' p x := by
  let w' := (etaleAbelianInverseImageCompIso'.{u, u + 1} h k₂ (h ≫ k₂) rfl).hom.app A ≫
    (etaleAbelianInverseImage.{u, u + 1} h).map w₂ ≫ 𝟙 _
  refine ⟨(etaleAbelianInverseImageCompIso'.{u, u + 1} k₁ (h ≫ k₂) (k₁ ≫ h ≫ k₂) rfl).hom.app A ≫
    (etaleAbelianInverseImage.{u, u + 1} k₁).map w' ≫ W, ?_⟩
  rw [← etaleCohomologyMapTo_id h B p, etaleCohomologyMapTo_comp h k₂ (h ≫ k₂) rfl w₂ (𝟙 _) w' rfl,
    etaleCohomologyMapTo_comp k₁ (h ≫ k₂) (k₁ ≫ h ≫ k₂) rfl w' W _ rfl]

/-- A class whose image under an invertible cohomology map dies after restriction along `h` is
killed by the cohomology map of every morphism factoring through `h`. -/
theorem etaleCohomologyMapTo_eq_zero_of_isIso (k₁ : X₄ ⟶ X₃) (h : X₃ ⟶ X₂) (k₂ : X₂ ⟶ X₁)
    (k : X₄ ⟶ X₁) (hk : k = k₁ ≫ h ≫ k₂) {A : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {C : Sheaf X₄.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w₂ : (etaleAbelianInverseImage.{u, u + 1} k₂).obj A ⟶ B) [IsIso w₂]
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ C) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p)
    (hx : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} h B p (etaleCohomologyMapTo k₂ w₂ p x)
      = 0) :
    etaleCohomologyMapTo k w p x = 0 := by
  have hk' : k = (k₁ ≫ h) ≫ k₂ := by rw [hk, Category.assoc]
  rw [← etaleCohomologyMapTo_comp (k₁ ≫ h) k₂ k hk' w₂
    ((etaleAbelianInverseImage.{u, u + 1} (k₁ ≫ h)).map (inv w₂) ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (k₁ ≫ h) k₂ k hk').inv.app A ≫ w) w
    (by simp)]
  exact etaleCohomologyMapTo_eq_zero_of_restriction_eq_zero k₁ h (k₁ ≫ h) rfl _ p _ hx

/-- **The diagram chase of the case `q = 1` of Tag 0EYT.** Let `ξ` be a class on `X_K` whose
restriction to `X_Ω` is the image under a map of sheaves `ψ` of the restriction of a class `ζ`
on `X_{\bar k}`, itself the image of a class `ζ_E` on `X_E` which dies on `Z`. If `Y_Ω ⟶ Y ⟶ X_K`
factors through `X_Ω` and the composite `Y_Ω ⟶ X_Ω ⟶ X_{\bar k} ⟶ X_E` through `Z`, then the
image of `ξ` on `Y` dies on `Y_Ω`. -/
theorem restriction_etaleCohomologyMapTo_eq_zero_of_factor
    {YΩ Y XK XΩ Xkb XE Z : Scheme.{u}} (sΩ : YΩ ⟶ Y) (c : Y ⟶ XK) (v : YΩ ⟶ XΩ) (o : XΩ ⟶ XK)
    (hv₁ : v ≫ o = sΩ ≫ c) (t : XΩ ⟶ Xkb) (π : Xkb ⟶ XE) (j : YΩ ⟶ Z) (h : Z ⟶ XE)
    (hv₂ : v ≫ t ≫ π = j ≫ h) {G : Sheaf XK.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {SE : Sheaf XE.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {Skb : Sheaf Xkb.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w₀ : (etaleAbelianInverseImage.{u, u + 1} c).obj G ⟶ B)
    (ψ : (etaleAbelianInverseImage.{u, u + 1} t).obj Skb ⟶
      (etaleAbelianInverseImage.{u, u + 1} o).obj G)
    (w : (etaleAbelianInverseImage.{u, u + 1} π).obj SE ⟶ Skb) (p : ℕ)
    (ξ : Sheaf.H.{u + 1, u + 1} G p) (ζ : Sheaf.H.{u + 1, u + 1} Skb p)
    (ζE : Sheaf.H.{u + 1, u + 1} SE p)
    (hψ : Sheaf.H.map ψ p (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} t Skb p ζ) =
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} o G p ξ)
    (hw : etaleCohomologyMapTo π w p ζE = ζ)
    (hdie : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} h SE p ζE = 0) :
    etaleCohomologyRestrictionMap.{u, u + 1, u + 1} sΩ B p (etaleCohomologyMapTo c w₀ p ξ) = 0 := by
  rw [← etaleCohomologyMapTo_id sΩ B p, etaleCohomologyMapTo_comp sΩ c (v ≫ o) hv₁ w₀ (𝟙 _) _ rfl,
    etaleCohomologyMapTo_eq_comp_restriction v o _ rfl, ← hψ, etaleCohomologyMapTo_sheafH_map,
    ← hw]
  obtain ⟨W, hW⟩ := exists_etaleCohomologyMapTo_restriction_etaleCohomologyMapTo v t π w
    ((etaleAbelianInverseImage.{u, u + 1} v).map ψ ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} v o (v ≫ o) rfl).inv.app G ≫
        (etaleAbelianInverseImageCompIso'.{u, u + 1} sΩ c (v ≫ o) hv₁).hom.app G ≫
          (etaleAbelianInverseImage.{u, u + 1} sΩ).map w₀ ≫ 𝟙 _) p ζE
  rw [hW]
  exact etaleCohomologyMapTo_eq_zero_of_restriction_eq_zero j h _ hv₂ _ p ζE hdie

end MapTo

/-- A finite extension of `k` mapping into an algebraic extension `Ω` of `K ⊇ k` lands in a
subextension of `Ω/K` of finite degree. -/
theorem exists_finiteDimensional_intermediateField_range_le {k : Type u} (K : Type u)
    {Ω E : Type u} [Field k] [Field K] [Field Ω] [Field E] [Algebra k K] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω] [Algebra.IsIntegral K Ω] [Algebra k E]
    [FiniteDimensional k E] (ι : E →ₐ[k] Ω) :
    ∃ L₀ : IntermediateField K Ω, FiniteDimensional K L₀ ∧ ∀ e : E, ι e ∈ L₀ := by
  let b := Module.finBasis k E
  refine ⟨IntermediateField.adjoin K (Set.range fun i => ι (b i)),
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y,
    fun e => ?_⟩
  rw [← b.sum_repr e, map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply k K Ω]
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The projection of `X_L` onto `X_E` for a finite subextension `E` of `L/k`, followed by
`X_E ⟶ Spec E`, is `X_L ⟶ Spec L ⟶ Spec E`. -/
theorem fextPullbackCone_π_app_fst {L : Type u} [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (E : FExt k L) :
    (fextPullbackCone (k := k) (K := L) X f).π.app (op E) ≫ pullback.fst (spectrumMap k E.1) f =
      pullback.fst (spectrumMap k L) f ≫ spectrumMap E.1 L :=
  pullback.lift_fst _ _ _

/-- The projection of `X_L` onto `X_E` for a finite subextension `E` of `L/k`, followed by
`X_E ⟶ X`, is the projection `X_L ⟶ X`. -/
theorem fextPullbackCone_π_app_snd {L : Type u} [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (E : FExt k L) :
    (fextPullbackCone (k := k) (K := L) X f).π.app (op E) ≫ pullback.snd (spectrumMap k E.1) f =
      pullback.snd (spectrumMap k L) f :=
  pullback.lift_snd _ _ _

/-- The second component of `coverBaseChangeMap` is `Z_{K'} ⟶ Z ⟶ X_{k'} ⟶ X`. -/
theorem coverBaseChangeMap_snd (k' K' : Type u) [Field k'] [Field K'] [Algebra k k']
    [Algebra K K'] [Algebra k' K'] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    {Z : Scheme.{u}} (p : Z ⟶ pullback (spectrumMap k k') f) :
    coverBaseChangeMap f K k' K' p ≫ pullback.snd (spectrumMap k K) f =
      pullback.snd _ _ ≫ p ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- `coverBaseChangeClass` is the restriction along `coverBaseChangeMap` composed with the
identification of the two inverse images of `F`. -/
theorem coverBaseChangeClass_apply (k' K' : Type u) [Field k'] [Field K'] [Algebra k k']
    [Algebra K K'] [Algebra k' K'] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    {Z : Scheme.{u}} (p : Z ⟶ pullback (spectrumMap k k') f)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q) :
    coverBaseChangeClass f K k' K' p F q ξ =
      etaleCohomologyMapTo (coverBaseChangeMap f K k' K' p)
        ((etaleAbelianInverseImageCompIso'.{u, u + 1} (coverBaseChangeMap f K k' K' p)
          (pullback.fst (spectrumMap k K) f) _ (coverBaseChangeMap_fst f K k' K' p).symm).inv.app F)
        q ξ :=
  rfl

/-- **The last step of the case `q = 1` of Tag 0EYT.** Let `p : Z ⟶ X_{k'}` be a cover with `Z`
affine, and `L₀ ⊆ Ω` a finite extension of `K` containing `k'`. If the restriction of `ξ` to
`Z_{L₀}` dies on `Z_Ω`, then it dies on `Z_{K'}` for a finite extension `K'/K` containing `L₀`
([Stacks, Tag 03Q6]), and the data `(k', K', Z, p)` satisfy the conclusion of Tag 0EYT as soon
as `p` is a Galois cover of the required kind. -/
theorem exists_galoisCover_of_restriction_algebraicClosure_eq_zero [IsAffine X]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (L₀ : IntermediateField K (Ωbar K)) [FiniteDimensional K L₀]
    [Algebra k' L₀] [IsScalarTower k k' L₀] {Z : Scheme.{u}} [IsAffine Z]
    (p : Z ⟶ pullback (spectrumMap k k') f)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) {n q : ℕ}
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q)
    (hgal : IsGaloisCover p) (hcard : ∃ m : ℕ, Nat.card (Aut (Over.mk p)) ∣ n ^ m)
    (hsplit : IsSplitOver p (basePoint f k' x hx))
    (hξ : etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (pullback.snd (spectrumMap L₀ (Ωbar K))
        (pullback.fst (spectrumMap k' L₀) (p ≫ pullback.fst (spectrumMap k k') f))) _ q
        (etaleCohomologyMapTo (coverBaseChangeMap f K k' L₀ p)
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (coverBaseChangeMap f K k' L₀ p)
            (pullback.fst (spectrumMap k K) f) _
              (coverBaseChangeMap_fst f K k' L₀ p).symm).inv.app F) q ξ) = 0) :
    ∃ (k' K' : Type u) (_ : Field k') (_ : Field K') (_ : Algebra k k') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : Algebra k K') (_ : IsScalarTower k k' K')
      (_ : IsScalarTower k K K') (_ : FiniteDimensional k k') (_ : FiniteDimensional K K')
      (Z : Scheme.{u}) (p : Z ⟶ pullback (spectrumMap k k') f),
      IsGaloisCover p ∧ (∃ m : ℕ, Nat.card (Aut (Over.mk p)) ∣ n ^ m) ∧
        IsSplitOver p (basePoint f k' x hx) ∧ coverBaseChangeClass f K k' K' p F q ξ = 0 := by
  let fY := pullback.fst (spectrumMap k' L₀) (p ≫ pullback.fst (spectrumMap k k') f)
  let gY := pullback.snd (spectrumMap k' L₀) (p ≫ pullback.fst (spectrumMap k k') f)
  have : Algebra.IsAlgebraic L₀ (Ωbar K) := Algebra.IsAlgebraic.tower_top (K := K) L₀
  obtain ⟨E₂, hE₂⟩ := exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic
    (L := L₀) (Ω := Ωbar K) fY _ q _ hξ
  have : FiniteDimensional L₀ E₂ := hE₂.1
  let : Algebra k' E₂ := ((algebraMap L₀ E₂).comp (algebraMap k' L₀)).toAlgebra
  have : IsScalarTower k' L₀ E₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra k E₂ := ((algebraMap K E₂).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K E₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k k' E₂ := IsScalarTower.of_algebraMap_eq fun c => Subtype.ext <| by
    show algebraMap K (Ωbar K) (algebraMap k K c) =
      ((algebraMap k' L₀ (algebraMap k k' c) : L₀) : Ωbar K)
    rw [← IsScalarTower.algebraMap_apply k k' L₀]
    exact (IsScalarTower.algebraMap_apply k K (Ωbar K) c).symm
  have : FiniteDimensional K E₂ := Module.Finite.trans L₀ E₂
  refine ⟨k', E₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Z, p, hgal, hcard,
    hsplit, ?_⟩
  let u : pullback (spectrumMap k' E₂) (p ≫ pullback.fst (spectrumMap k k') f) ⟶
      pullback (spectrumMap L₀ E₂) fY :=
    pullback.lift (pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ spectrumMap L₀ E₂) (pullback.snd _ _) (by
        rw [Category.assoc, spectrumMap_comp_spectrumMap k' L₀ E₂]
        exact pullback.condition))
      (pullback.lift_fst _ _ _).symm
  have hufst : u ≫ pullback.fst (spectrumMap L₀ E₂) fY = pullback.fst _ _ :=
    pullback.lift_fst _ _ _
  have hu₁ : u ≫ pullback.snd _ _ ≫ gY = pullback.snd _ _ := by
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hu : coverBaseChangeMap f K k' E₂ p =
      u ≫ pullback.snd _ _ ≫ coverBaseChangeMap f K k' L₀ p := by
    apply pullback.hom_ext
    · simp only [Category.assoc, coverBaseChangeMap_fst]
      rw [← pullback.condition_assoc, reassoc_of% hufst, spectrumMap_comp_spectrumMap K L₀ E₂]
    · simp only [Category.assoc, coverBaseChangeMap_snd]
      rw [reassoc_of% hu₁]
  exact (coverBaseChangeClass_apply f k' E₂ p F q ξ).trans
    (etaleCohomologyMapTo_eq_zero_of_isIso u (pullback.snd _ _) _ _ hu _ _ q ξ hE₂.2)

/-- **The geometric factorization of the case `q = 1` of Tag 0EYT.** For a tower
`k ⊆ E ⊆ E' ⊆ \bar k` and a finite extension `L₀ ⊆ Ω` of `K` containing `E'`, with `Y = Z_{L₀}`,
the map `Y_Ω ⟶ Y ⟶ X_K` factors through `X_Ω` by a map `v` such that
`Y_Ω ⟶ X_Ω ⟶ X_{\bar k} ⟶ X_E` factors through `Z ⟶ X_{E'} ⟶ X_E`. -/
private theorem exists_XOmega_lift_coverBaseChangeMap (E : FExt k (kbar k K)) {E' : Type u}
    [Field E'] [Algebra E.1 E'] [Algebra k E'] [IsScalarTower k E.1 E'] (ιE' : E' →ₐ[E.1] kbar k K)
    (L₀ : IntermediateField K (Ωbar K)) [Algebra E' L₀] [IsScalarTower k E' L₀]
    (hL : ∀ e : E', ((algebraMap E' L₀ e : L₀) : Ωbar K) = algebraMap (kbar k K) (Ωbar K) (ιE' e))
    {Z : Scheme.{u}} (p : Z ⟶ pullback (spectrumMap k E') f) :
    ∃ v : pullback (spectrumMap L₀ (Ωbar K))
        (pullback.fst (spectrumMap E' L₀) (p ≫ pullback.fst (spectrumMap k E') f)) ⟶
        XOmega (K := K) f,
      v ≫ XOmegaSnd f = pullback.snd _ _ ≫ coverBaseChangeMap f K E' L₀ p ∧
      v ≫ XOmegaToXkbar f ≫ (fextPullbackCone (k := k) (K := kbar k K) X f).π.app (op E) =
        (pullback.snd _ _ ≫ pullback.snd (spectrumMap E' L₀)
          (p ≫ pullback.fst (spectrumMap k E') f)) ≫ p ≫ pullbackSpectrumMap f E.1 E' := by
  let fY := pullback.fst (spectrumMap E' L₀) (p ≫ pullback.fst (spectrumMap k E') f)
  let gY := pullback.snd (spectrumMap E' L₀) (p ≫ pullback.fst (spectrumMap k E') f)
  let πE := (fextPullbackCone (k := k) (K := kbar k K) X f).π.app (op E)
  have hYΩ : pullback.snd (spectrumMap L₀ (Ωbar K)) fY ≫ fY =
      pullback.fst _ _ ≫ spectrumMap L₀ (Ωbar K) := pullback.condition.symm
  have hvc : pullback.fst (spectrumMap L₀ (Ωbar K)) fY ≫ spectrumMap K (Ωbar K) =
      (pullback.snd (spectrumMap L₀ (Ωbar K)) fY ≫ coverBaseChangeMap f K E' L₀ p) ≫
        pullback.fst (spectrumMap k K) f := by
    rw [Category.assoc, coverBaseChangeMap_fst, reassoc_of% hYΩ,
      spectrumMap_comp_spectrumMap K L₀ (Ωbar K)]
  let v : pullback (spectrumMap L₀ (Ωbar K)) fY ⟶ XOmega (K := K) f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ coverBaseChangeMap f K E' L₀ p) hvc
  have hv₁ : v ≫ XOmegaSnd f = pullback.snd _ _ ≫ coverBaseChangeMap f K E' L₀ p :=
    pullback.lift_snd _ _ _
  have hvfst : v ≫ XOmegaFst f = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hY : gY ≫ p ≫ pullback.fst (spectrumMap k E') f = fY ≫ spectrumMap E' L₀ :=
    pullback.condition.symm
  have hring : spectrumMap (kbar k K) (Ωbar K) ≫ spectrumMap E.1 (kbar k K) =
      spectrumMap L₀ (Ωbar K) ≫ spectrumMap E' L₀ ≫ spectrumMap E.1 E' := by
    simp only [spectrumMap, ← Spec.map_comp]
    congr 1
    ext e
    exact (congrArg (algebraMap (kbar k K) (Ωbar K)) (ιE'.commutes e).symm).trans (hL _).symm
  have hv₂ : v ≫ XOmegaToXkbar f ≫ πE =
      (pullback.snd _ _ ≫ gY) ≫ p ≫ pullbackSpectrumMap f E.1 E' := by
    refine pullback.hom_ext (f := spectrumMap k E.1) (g := f) ?_ ?_
    · erw [Category.assoc, Category.assoc, fextPullbackCone_π_app_fst f E]
      simp only [Category.assoc, pullbackSpectrumMap_fst, reassoc_of% XOmegaToXkbar_fst,
        reassoc_of% hvfst, reassoc_of% hY, reassoc_of% hYΩ, hring]
    · erw [Category.assoc, Category.assoc, fextPullbackCone_π_app_snd f E]
      rw [XOmegaToXkbar_snd (K := K) f, reassoc_of% hv₁]
      simp only [Category.assoc, pullbackSpectrumMap_snd, coverBaseChangeMap_snd]
      rfl
  exact ⟨v, hv₁, hv₂⟩

/-- **[Stacks, Tag 0EYT], the case `q = 1`.** -/
theorem exists_galoisCover_of_eq_one [IsCurve k f] [IsAffine X] (x : Spec (.of k) ⟶ X)
    (hx : x ≫ f = 𝟙 _) (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {n : ℕ} (hn0 : 0 < n) (hn : IsUnit (n : k)) (hF : n • 𝟙 F = 0)
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) 1) :
    ∃ (k' K' : Type u) (_ : Field k') (_ : Field K') (_ : Algebra k k') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : Algebra k K') (_ : IsScalarTower k k' K')
      (_ : IsScalarTower k K K') (_ : FiniteDimensional k k') (_ : FiniteDimensional K K')
      (Z : Scheme.{u}) (p : Z ⟶ pullback (spectrumMap k k') f),
      IsGaloisCover p ∧ (∃ m : ℕ, Nat.card (Aut (Over.mk p)) ∣ n ^ m) ∧
        IsSplitOver p (basePoint f k' x hx) ∧ coverBaseChangeClass f K k' K' p F 1 ξ = 0 := by
  have : ConnectedSpace X :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ X).isConnected
  have : GeometricallyConnected f := geometricallyConnected_of_connectedSpace_of_section f x hx
  obtain ⟨S, hSfin, hSn, ζ, ψ, hψ⟩ := exists_kbar_class f F hn0 hn hF ξ
  obtain ⟨E, ζE, w, hw⟩ := exists_finite_stage_class f (kbar k K) S ζ
  have hS : ∀ s : S, n • s = 0 := fun s => by simpa using ConcreteCategory.congr_hom hSn s
  obtain ⟨E', _, _, _, _, hE', ιE', Z, p, hgal, hcard, hsplit, hdie⟩ :=
    exists_galoisCover_restriction_eq_zero f x hx (E := E.1) (L := kbar k K) S hS ζE
  have : FiniteDimensional k E.1 := E.2
  have : FiniteDimensional k E' := Module.Finite.trans E.1 E'
  let ιE : E' →+* Ωbar K := (algebraMap (kbar k K) (Ωbar K)).comp ιE'.toRingHom
  have hιE : ∀ c : k, ιE (algebraMap k E' c) = algebraMap k (Ωbar K) c := fun c => by
    show algebraMap (kbar k K) (Ωbar K) (ιE' (algebraMap k E' c)) = _
    rw [IsScalarTower.algebraMap_apply k E.1 E', ιE'.commutes]
    rfl
  obtain ⟨L₀, hL₀, hmem⟩ := exists_finiteDimensional_intermediateField_range_le K
    ({ ιE with commutes' := hιE } : E' →ₐ[k] Ωbar K)
  let : Algebra E' L₀ := (ιE.codRestrict L₀ hmem).toAlgebra
  have : IsScalarTower k E' L₀ := IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (hιE c).symm
  let fY := pullback.fst (spectrumMap E' L₀) (p ≫ pullback.fst (spectrumMap k E') f)
  have : IsFinite p := hgal.1
  have : IsAffine Z := isAffine_of_isAffineHom p
  have : Algebra.IsAlgebraic L₀ (Ωbar K) := Algebra.IsAlgebraic.tower_top (K := K) L₀
  obtain ⟨v, hv₁, hv₂⟩ := exists_XOmega_lift_coverBaseChangeMap f E ιE' L₀ (fun _ => rfl) p
  exact exists_galoisCover_of_restriction_algebraicClosure_eq_zero f x hx E' L₀ p F ξ hgal hcard
    hsplit (restriction_etaleCohomologyMapTo_eq_zero_of_factor
      (pullback.snd (spectrumMap L₀ (Ωbar K)) fY) (coverBaseChangeMap f K E' L₀ p) v
      (XOmegaSnd f) hv₁ (XOmegaToXkbar f)
      ((fextPullbackCone (k := k) (K := kbar k K) X f).π.app (op E)) _
      (p ≫ pullbackSpectrumMap f E.1 E') hv₂
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (coverBaseChangeMap f K E' L₀ p)
        (pullback.fst (spectrumMap k K) f) _ (coverBaseChangeMap_fst f K E' L₀ p).symm).inv.app F)
      ψ w 1 ξ ζ ζE hψ hw hdie)

/-- **Stacks Project, Tag 0EYT.** Let `K/k` be a field extension, `X` a smooth affine curve over
`k` with a rational point `x`, `F` an abelian sheaf on `Spec(K)_étale` annihilated by an integer
`n` invertible in `k`, `q > 0` and `ξ ∈ H^q(X_K, F)`. There are finite extensions `K'/K` and
`k'/k` with `k' ⊆ K'` and a finite étale Galois cover `Z ⟶ X_{k'}`, whose group has order
dividing a power of `n` and which is split over `x_{k'}`, such that `ξ` dies in
`H^q(Z_{K'}, F)`. -/
@[stacks 0EYT]
theorem exists_galoisCover_killing_class [IsCurve k f] [Smooth f] [IsAffine X]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ}
    (hn : IsUnit (n : k)) (hF : n • 𝟙 F = 0) {q : ℕ} (hq : 0 < q)
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q) :
    ∃ (k' K' : Type u) (_ : Field k') (_ : Field K') (_ : Algebra k k') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : Algebra k K') (_ : IsScalarTower k k' K')
      (_ : IsScalarTower k K K') (_ : FiniteDimensional k k') (_ : FiniteDimensional K K')
      (Z : Scheme.{u}) (p : Z ⟶ pullback (spectrumMap k k') f),
      IsGaloisCover p ∧ (∃ m : ℕ, Nat.card (Aut (Over.mk p)) ∣ n ^ m) ∧
        IsSplitOver p (basePoint f k' x hx) ∧ coverBaseChangeClass f K k' K' p F q ξ = 0 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  obtain h | rfl : 1 < q ∨ q = 1 := by omega
  · exact exists_galoisCover_of_one_lt f x hx F hn0 hF h ξ
  · exact exists_galoisCover_of_eq_one f x hx F hn0 hn hF ξ

end Stacks.EtaleCohomology

end
