module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Theorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquare

/-!
# Base change maps at torsion sheaves, from sheaves annihilated by one integer

The proofs of [Stacks, Tag 0F1H] and [Stacks, Tag 0F1I] begin: *"Write `𝓕 = colim 𝓕[n]` where the
colimit is over the multiplicative system of integers invertible in `K`. Since cohomology commutes
with filtered colimits in our situation, it suffices to prove the lemma for `𝓕[n]`."* This file
proves that reduction for the base change map on higher direct images of any commutative square
of schemes whose horizontal sides are quasi-compact and quasi-separated, and states it for the
product square of an open immersion with a scheme over a field.

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_forall_annihilated` — in a commutative
  square
  ```
  X  ←-h-  Y
  |f       |e
  S' ←-g-  T
  ```
  with `g` and `h` quasi-compact and quasi-separated, if the base change map
  `f⁻¹ R^q g_* G ⟶ R^q h_* e⁻¹ G` is an isomorphism at every abelian sheaf `G` annihilated by an
  integer `n > 0` invertible on a scheme `S`, then it is one at every abelian sheaf whose stalks
  are torsion of orders invertible on `S`.
* `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_forall_annihilated` — its case
  for the product square `Y ×_K X ← Y ×_K U` of an open immersion `j : U ⟶ X` over a field `K`,
  with the integers invertible in `K`.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **The base change map at a torsion sheaf, from sheaves annihilated by one integer.** In a
commutative square `h ≫ f = e ≫ g` of schemes with `g` and `h` quasi-compact and
quasi-separated, if the base change map `f⁻¹ R^q g_* G ⟶ R^q h_* e⁻¹ G` is an isomorphism at
every abelian sheaf `G` on `T_étale` annihilated by an integer `n > 0` invertible on `S`, then it
is an isomorphism at every abelian sheaf `F` whose stalks are torsion of orders invertible on
`S`. The sheaf `F` is the filtered colimit of its subsheaves `F[n]`, `n` invertible on `S`;
inverse images commute with colimits and higher direct images along quasi-compact
quasi-separated morphisms commute with filtered colimits. -/
theorem isIso_higherBaseChangeMapAb_of_forall_annihilated (S : Scheme.{u})
    {X Y S' T : Scheme.{u}} (f : X ⟶ S') (g : T ⟶ S') (h : Y ⟶ X) (e : Y ⟶ T)
    (w : h ≫ f = e ≫ g) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact h] [QuasiSeparated h]
    (q : ℕ)
    (H : ∀ n : ℕ, 0 < n → IsUnit ((n : ℤ) : Γ(S, ⊤)) →
      ∀ G : Sheaf (smallEtaleTopology T) Ab.{u + 1},
        (∀ (V : T.Etale) (x : G.obj.obj (op V)), (n : ℤ) • x = 0) →
          IsIso ((higherBaseChangeMapAb f g h e w q).app G))
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (t : GeometricPoint T) (a : (smallEtaleStalkAb t.hom).obj F),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0) :
    IsIso ((higherBaseChangeMapAb f g h e w q).app F) := by
  let D := SmoothBaseChange.torsionDiagram F S
  have : PreservesColimit D ((smallEtalePushforwardAb g).rightDerived q) :=
    SmoothBaseChange.preservesColimit_rightDerived_smallEtalePushforwardAb g q D
  have : PreservesColimit (D ⋙ smallEtalePullbackAb e)
      ((smallEtalePushforwardAb h).rightDerived q) :=
    SmoothBaseChange.preservesColimit_rightDerived_smallEtalePushforwardAb h q _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (smallEtalePullbackAb f) :=
    (smallEtaleAdjunctionAb f).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u + 1, u + 1} (smallEtalePullbackAb e) :=
    (smallEtaleAdjunctionAb e).leftAdjoint_preservesColimits
  refine SmoothBaseChange.isIso_app_of_isColimit (SmoothBaseChange.isColimitTorsionCocone S F hF)
    (higherBaseChangeMapAb f g h e w q) fun k => ?_
  exact H _ (SmoothBaseChange.invertibleIndex_pos S k.down)
    (SmoothBaseChange.isUnit_invertibleIndex S k.down) (D.obj k)
    (fun V x => SmoothBaseChange.zsmul_kernel_eq_zero F _ (op V) x)

/-- An integer is invertible on `Spec K` exactly when it is invertible in the field `K`. -/
theorem isUnit_intCast_Γ_Spec_iff {K : Type u} [Field K] {n : ℤ} :
    IsUnit (n : Γ(Spec (.of K), ⊤)) ↔ IsUnit (n : K) :=
  (MulEquiv.isUnit_map (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv).symm.trans
    (by simp)

namespace OpenImmersionProductSquare

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU)

/-- **The first reduction of [Stacks, Tag 0F1H]**: for the product square
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
of a quasi-compact quasi-separated morphism `j` of schemes over a field `K`, if the base change
map `q⁻¹ R^i j_* G ⟶ R^i h_* p⁻¹ G` is an isomorphism at every abelian sheaf `G` on `U_étale`
annihilated by an integer `n > 0` invertible in `K`, then it is one at every abelian sheaf `𝓕`
whose stalks are torsion of orders invertible in `K`. -/
theorem isIso_higherBaseChangeMapAb_of_forall_annihilated [QuasiCompact j] [QuasiSeparated j]
    (i : ℕ)
    (H : ∀ n : ℕ, 0 < n → IsUnit ((n : ℤ) : K) →
      ∀ G : Sheaf (smallEtaleTopology U) Ab.{u + 1},
        (∀ (V : U.Etale) (x : G.obj.obj (op V)), (n : ℤ) • x = 0) →
          IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
            (h_comp_q sX sU sY j hj) i).app G))
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (t : GeometricPoint U) (a : (smallEtaleStalkAb t.hom).obj 𝓕),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : K) ∧ n • a = 0) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  have : QuasiCompact (h sX sU sY j hj) :=
    MorphismProperty.of_isPullback (isPullback sX sU sY j hj).flip ‹_›
  have : QuasiSeparated (h sX sU sY j hj) :=
    MorphismProperty.of_isPullback (isPullback sX sU sY j hj).flip ‹_›
  refine Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_forall_annihilated
    (Spec (.of K)) _ _ _ _ _ i (fun n hn hu G hG => ?_) 𝓕 (fun t a => ?_)
  · exact H n hn (isUnit_intCast_Γ_Spec_iff.1 hu) G hG
  · obtain ⟨n, hn, hu, ha⟩ := h𝓕 t a
    exact ⟨n, hn, isUnit_intCast_Γ_Spec_iff.2 hu, ha⟩

end OpenImmersionProductSquare

end Stacks.EtaleCohomology

end
