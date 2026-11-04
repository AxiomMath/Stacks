module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# Algebraization of a cartesian tower of closed subspaces of the adic fibres

Let `A` be a Noetherian ring complete with respect to an ideal `I`, `S = Spec A`,
`S_n = Spec(A / I^{n+1})`, and `X ⟶ S` separated and of finite type with adic fibres
`X_n = X ×_S S_n`.  A tower `Z_0 ⟶ Z_1 ⟶ ⋯` of algebraic spaces over the `X_n` with cartesian
squares, `Z_0 ⟶ X_0` a closed immersion and `Z_0` proper over `S_0`, is the tower of adic fibres
of a closed subspace `Z ⊆ X` proper over `S` (Stacks 08BG).

## Main results

* `AlgebraicGeometry.Space.exists_isClosedImmersion_adicFibre_iso`: **Stacks 08BG**.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 08B2](https://stacks.math.columbia.edu/tag/08B2)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- **Stacks 08BG.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, write
`S = Spec A` and `S_n = Spec(A / I^{n+1})`, and let `X ⟶ S` be a separated morphism of finite
type of algebraic spaces, with adic fibres `X_n = X ×_S S_n`.  Let `Z_n` be algebraic spaces with
morphisms `j_n : Z_n ⟶ X_n` and `t_n : Z_n ⟶ Z_{n+1}` making every square
`Z_n ⟶ Z_{n+1}` over `X_n ⟶ X_{n+1}` cartesian.  If `Z_0 ⟶ X_0` is a closed immersion and
`Z_0 ⟶ S_0` is proper, then there is a closed immersion `i : Z ⟶ X` of algebraic spaces with
`Z ⟶ S` proper and isomorphisms `Z_n ≅ Z ×_S S_n` over `X_n`, compatible with the transition
maps.

The index `n` stands for the source's `n + 1`: `Z 0 = Z_1`, `X 0 = X_1`, `S 0 = S_1`. -/
@[stacks 08BG]
theorem exists_isClosedImmersion_adicFibre_iso [IsNoetherianRing A] [IsAdicComplete I A]
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (hft : IsFiniteType B (Spec (.of A)) hS fX)
    (hsep : IsSeparated B (Spec (.of A)) hS fX)
    (Z : ℕ → (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
    (hZ : ∀ n, IsAlgebraicSpace B (Spec (.of A)) hS (Z n))
    (j : ∀ n, Z n ⟶ adicFibre A I B hS hSn fX n) (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicFibreSucc A I B hS hSn fX n))
    (hj : IsClosedImmersion B (Spec (.of A)) hS (j 0))
    (hprop : IsProper B (Spec (.of A)) hS
      (j 0 ≫ pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn 0)))) :
    ∃ (W : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (Spec (.of A)) hS W) (i : W ⟶ X),
      IsClosedImmersion B (Spec (.of A)) hS i ∧ IsProper B (Spec (.of A)) hS (i ≫ fX) ∧
      ∃ e : ∀ n, Z n ≅ adicFibre A I B hS hSn (i ≫ fX) n,
        (∀ n, (e n).hom ≫ adicFibreMap A I B hS hSn i rfl n = j n) ∧
        (∀ n, t n ≫ (e (n + 1)).hom = (e n).hom ≫ adicFibreSucc A I B hS hSn (i ≫ fX) n) := by
  let Xs : AlgebraicSpaces B (Spec (.of A)) hS := ⟨X, hX⟩
  let f : Xs ⟶ schemeSpace (baseObject A B hS) := ObjectProperty.homMk fX
  have hjn : ∀ n, IsClosedImmersion B (Spec (.of A)) hS (j n) :=
    isClosedImmersion_of_isPullback_adicFibreSucc_tower A I B hS hSn hX fX Z hZ j t hcart hj
  let p : ∀ n, adicFibre A I B hS hSn fX n ⟶ X := fun n =>
    pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))
  have hth : ∀ n, IsClosedImmersion B (Spec (.of A)) hS
      (yoneda.map (adicThickeningMap A I B hS hSn n)) := fun n =>
    (presheaf_yoneda_map_iff B (Spec (.of A)) hS inferInstance _).2
      (isClosedImmersion_toScheme_map_adicThickeningMap A I B hS hSn n)
  have hp : ∀ n, IsClosedImmersion B (Spec (.of A)) hS (p n) := fun n => by
    have := isClosedImmersion_isStableUnderBaseChange B (Spec (.of A)) hS
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback fX _).flip (hth n)
  have hpm : ∀ n, Mono (p n) := fun n => mono_of_isClosedImmersion B (Spec (.of A)) hS _ (hp n)
  have hjm : ∀ n, Mono (j n) := fun n => mono_of_isClosedImmersion B (Spec (.of A)) hS _ (hjn n)
  have hps : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ p (n + 1) = p n := fun n =>
    adicFibreSucc_fst A I B hS hSn fX n
  have hkk : ∀ n, IsClosedImmersion B (Spec (.of A)) hS (j n ≫ p n) := fun n =>
    isClosedImmersion_comp B (Spec (.of A)) hS _ _ (hjn n) (hp n)
  let C : ℕ → ClosedSubspaces B (Spec (.of A)) hS X := fun n =>
    ⟨Subfunctor.range (j n ≫ p n),
      isClosedSubspace_range_of_isClosedImmersion B (Spec (.of A)) hS _ (hZ n) (hkk n)⟩
  have hD : ∀ n, (adicFibreSubspace A I B hS hSn Xs fX n).1 = Subfunctor.range (p n) := fun n =>
    (range_adicFibre_fst A I B hS hSn fX n).symm
  have hinj : ∀ {F G : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) [Mono g] T,
      Function.Injective (g.app T) := fun g _ T =>
    (mono_iff_injective (g.app T)).1 ((NatTrans.mono_iff_mono_app g).1 inferInstance T)
  have hCD : ∀ n, (C n).1 = (C (n + 1)).1 ⊓ Subfunctor.range (p n) := by
    intro n
    refine le_antisymm (le_inf ?_ ?_) ?_
    · rintro T _ ⟨z, rfl⟩
      refine ⟨(t n).app T z, ?_⟩
      simpa only [Category.assoc, hps n, NatTrans.comp_app_apply] using
        congrArg (fun m => m.app T z) (congrArg (· ≫ p (n + 1)) (hcart n).w)
    · rintro T _ ⟨z, rfl⟩
      exact ⟨(j n).app T z, rfl⟩
    · rintro T x ⟨⟨z', hz'⟩, ⟨y, hy⟩⟩
      have h1 : (p (n + 1)).app T ((j (n + 1)).app T z') =
          (p (n + 1)).app T ((adicFibreSucc A I B hS hSn fX n).app T y) :=
        hz'.trans (hy.symm.trans (congrArg (fun m => m.app T y) (hps n).symm))
      obtain ⟨z, -, hz2⟩ := Types.exists_of_isPullback
        ((hcart n).map ((evaluation _ (Type u)).obj T)) z' y (hinj (p (n + 1)) T h1)
      refine ⟨z, ?_⟩
      change (p n).app T ((j n).app T z) = x
      rw [show (j n).app T z = y from hz2]
      exact hy
  have hC0 : IsProper B (Spec (.of A)) hS ((C 0).1.ι ≫ f.hom) := by
    have : Mono (j 0 ≫ p 0) := mono_of_isClosedImmersion B (Spec (.of A)) hS _ (hkk 0)
    have heq : (C 0).1.ι ≫ f.hom = (rangeIsoOfMono B (Spec (.of A)) hS (j 0 ≫ p 0)).inv ≫
        ((j 0 ≫ pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn 0))) ≫
          yoneda.map (adicThickeningMap A I B hS hSn 0)) := by
      rw [← rangeIsoOfMono_inv_comp B (Spec (.of A)) hS (j 0 ≫ p 0)]
      simp only [Category.assoc]
      exact congrArg (fun m => (rangeIsoOfMono B (Spec (.of A)) hS (j 0 ≫ p 0)).inv ≫ j 0 ≫ m)
        pullback.condition
    rw [heq]
    refine isProper_comp' B (Spec (.of A)) hS _ _ (hZ 0) (schemeSpace (baseObject A B hS)).2
      (isProper_of_isIso B (Spec (.of A)) hS _) ?_
    exact isProper_comp' B (Spec (.of A)) hS _ _
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _) (schemeSpace (baseObject A B hS)).2 hprop
      (isProper_of_isClosedImmersion B (Spec (.of A)) hS
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _) (schemeSpace (baseObject A B hS)).2 _
        (hth 0))
  obtain ⟨W, hWC, hWp⟩ := exists_closedSubspace_inf_adicFibreSubspace_eq A I B hS hSn Xs f hft
    hsep C (fun n => (hCD n).trans (congrArg ((C (n + 1)).1 ⊓ ·) (hD n).symm)) hC0
  have hCW : ∀ n, (C n).1 = W.1 ⊓ Subfunctor.range (p n) := fun n =>
    (hWC n).symm.trans (congrArg (W.1 ⊓ ·) (hD n))
  let i : W.1.toFunctor ⟶ X := W.1.ι
  have : Mono i := mono_of_isClosedImmersion B (Spec (.of A)) hS _ W.2.2
  have hle : ∀ n, Subfunctor.range (j n ≫ p n) ≤ W.1 := fun n =>
    (hCW n).le.trans inf_le_left
  let ℓ : ∀ n, Z n ⟶ W.1.toFunctor := fun n => Subfunctor.lift (j n ≫ p n) (hle n)
  have hℓ : ∀ n, ℓ n ≫ i = j n ≫ p n := fun n => Subfunctor.lift_ι _ _
  let u : ∀ n, Z n ⟶ adicFibre A I B hS hSn (i ≫ fX) n := fun n =>
    pullback.lift (ℓ n) (j n ≫ pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (by rw [← Category.assoc, hℓ n, Category.assoc, Category.assoc, pullback.condition])
  let w : ∀ n, adicFibre A I B hS hSn (i ≫ fX) n ⟶ adicFibre A I B hS hSn fX n := fun n =>
    adicFibreMap A I B hS hSn i rfl n
  have hwm : ∀ n, Mono (w n) := by
    intro n
    constructor
    intro Q g h hgh
    apply pullback.hom_ext
    · refine (cancel_mono i).1 ?_
      simpa [w] using
        congrArg (· ≫ pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))) hgh
    · simpa [w] using
        congrArg (· ≫ pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n))) hgh
  have huw : ∀ n, u n ≫ w n = j n := by
    intro n
    apply pullback.hom_ext
    · dsimp only [w, u]
      rw [Category.assoc, adicFibreMap_fst, ← Category.assoc, pullback.lift_fst, hℓ n]
    · dsimp only [w, u]
      rw [Category.assoc, adicFibreMap_snd, pullback.lift_snd]
  have hrange : ∀ n, Subfunctor.range (w n) ≤ Subfunctor.range (j n) := by
    intro n T _ ⟨y, hy⟩
    subst hy
    have hmem : (p n).app T ((w n).app T y) ∈ (C n).1.obj T := by
      rw [hCW n]
      refine ⟨?_, ⟨(w n).app T y, rfl⟩⟩
      have h := congrArg (fun m => m.app T y)
        (adicFibreMap_fst A I B hS hSn i (rfl : i ≫ fX = i ≫ fX) n)
      simp only [NatTrans.comp_app_apply] at h
      change (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app T
        ((w n).app T y) ∈ W.1.obj T
      rw [h]
      exact ((pullback.fst (i ≫ fX) (yoneda.map (adicThickeningMap A I B hS hSn n))).app T y).2
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, hinj (p n) T hz⟩
  let v : ∀ n, adicFibre A I B hS hSn (i ≫ fX) n ⟶ Z n := fun n =>
    Subfunctor.lift (w n) (hrange n) ≫ (rangeIsoOfMono B (Spec (.of A)) hS (j n)).inv
  have hvj : ∀ n, v n ≫ j n = w n := fun n => by
    dsimp only [v]
    rw [Category.assoc, rangeIsoOfMono_inv_comp, Subfunctor.lift_ι]
  let e : ∀ n, Z n ≅ adicFibre A I B hS hSn (i ≫ fX) n := fun n =>
    { hom := u n
      inv := v n
      hom_inv_id := (cancel_mono (j n)).1 (by rw [Category.assoc, hvj n, huw n, Category.id_comp])
      inv_hom_id := by
        have := hwm n
        exact (cancel_mono (w n)).1 (by rw [Category.assoc, huw n, hvj n, Category.id_comp]) }
  refine ⟨W.1.toFunctor, W.2.1, i, W.2.2, hWp, e, huw, fun n => ?_⟩
  have := hwm (n + 1)
  refine (cancel_mono (w (n + 1))).1 ?_
  change t n ≫ u (n + 1) ≫ w (n + 1) = (u n ≫ adicFibreSucc A I B hS hSn (i ≫ fX) n) ≫ w (n + 1)
  rw [huw (n + 1), (hcart n).w, Category.assoc]
  dsimp only [w]
  rw [adicFibreSucc_adicFibreMap, ← Category.assoc]
  exact congrArg (· ≫ adicFibreSucc A I B hS hSn fX n) (huw n).symm

end AlgebraicGeometry.Space

end
