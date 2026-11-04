module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMapComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicPointTrace

/-!
# Changing the geometric point of the stalk of an ℓ-adic sheaf

A morphism `θ : s ⟶ t` of geometric points of `X` induces isomorphisms of the finite-level stalks
of an ℓ-adic sheaf `F` at `t` and at `s` ([Stacks, Tag 04FN]).  If `θ` carries an endomorphism `a`
of `s` to an endomorphism `b` of `t`, these isomorphisms intertwine their actions, so `a` and `b`
have the same trace at every finite level of the torsion-free model of `F`, hence the same trace
on the rational stalks.  The actions of endomorphisms of a geometric point compose, so
the action of an iterate is the iterate of the action.

These are the two facts about stalks used in the proof of [Stacks, Tag 03V0] to compare the
geometric Frobenius at a point of `X ×_k k'` of degree one over `k'` with a power of the geometric
Frobenius at the point of `X` below it.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.Hom.iterate`: the iterates `a, a ≫ a, …` of an endomorphism.
* `Stacks.EtaleCohomology.finiteLevelStalkPointIso`: the level-`n` stalks at `t` and `s` along
  `θ : s ⟶ t`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkEnd_eq_of_comm`: endomorphisms related by
  a morphism of geometric points have the same trace on the rational stalks.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkEnd_iterate`: the action of an iterate.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

/-- The iterates `a, a ≫ a, a ≫ a ≫ a, …` of an endomorphism of a geometric point:
`a.iterate e` is the `(e + 1)`-fold composite. -/
def GeometricPoint.Hom.iterate {S : Scheme.{u}} {s : GeometricPoint S}
    (a : GeometricPoint.Hom s s) : ℕ → GeometricPoint.Hom s s
  | 0 => a
  | e + 1 => (a.iterate e).comp a

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-! ### Composites of endomorphisms -/

/-- The level-`n` action of a composite is the composite of the actions. -/
theorem finiteLevelStalkEnd_comp (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a b : GeometricPoint.Hom s s) (n : ℕ) :
    finiteLevelStalkEnd B X ℓ F (a.comp b) n =
      finiteLevelStalkEnd B X ℓ F b n ≫ finiteLevelStalkEnd B X ℓ F a n :=
  congrArg (fun α => NatTrans.app α (F.level n).obj)
    (geometricPointStalkMap_comp B X.1 X.property a b (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))

/-- The action of a composite on the rational stalk is the composite of the actions. -/
theorem LAdicSheaf.rationalStalkEnd_comp (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a b : GeometricPoint.Hom s s) :
    LAdicSheaf.rationalStalkEnd B X ℓ F (a.comp b) =
      LAdicSheaf.rationalStalkEnd B X ℓ F a ∘ₗ LAdicSheaf.rationalStalkEnd B X ℓ F b := by
  have h : LAdicSheaf.stalkEnd B X ℓ F (a.comp b) =
      LAdicSheaf.stalkEnd B X ℓ F a ∘ₗ LAdicSheaf.stalkEnd B X ℓ F b := by
    refine LinearMap.ext fun v => Subtype.ext (funext fun n => ?_)
    exact congrArg (fun g => g.hom (v.1 n)) (finiteLevelStalkEnd_comp B X ℓ F a b n)
  rw [LAdicSheaf.rationalStalkEnd, h, LinearMap.baseChange_comp]
  rfl

/-- **The action of an iterate on the rational stalk is the iterate of the action.** -/
theorem LAdicSheaf.rationalStalkEnd_iterate (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (e : ℕ) :
    LAdicSheaf.rationalStalkEnd B X ℓ F (a.iterate e) =
      LAdicSheaf.rationalStalkEnd B X ℓ F a ^ (e + 1) := by
  induction e with
  | zero => exact (pow_one _).symm
  | succ e ih =>
      rw [GeometricPoint.Hom.iterate, LAdicSheaf.rationalStalkEnd_comp, ih, pow_succ]
      rfl

/-! ### Changing the geometric point -/

section PointChange

variable (F : LAdicSheaf B X ℓ) {s t : GeometricPoint X.1} (θ : GeometricPoint.Hom s t)

/-- The level-`n` stalk map `F_t ⟶ F_s` along a morphism `θ : s ⟶ t` of geometric points, an
isomorphism ([Stacks, Tag 04FN]). -/
def finiteLevelStalkPointIso (n : ℕ) :
    finiteLevelStalk B X ℓ F t n ≅ finiteLevelStalk B X ℓ F s n :=
  @asIso _ _ _ _ ((geometricPointStalkMap B X.1 X.property θ
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).app (F.level n).obj)
    (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ (geometricPointStalkMap B X.1 X.property θ
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (geometricPointStalkMap_isIso B X.1 X.property θ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (F.level n).obj)

/-- If `θ : s ⟶ t` carries `a : s ⟶ s` to `b : t ⟶ t`, the level-`n` stalk isomorphism
intertwines their actions. -/
theorem finiteLevelStalkEnd_comp_finiteLevelStalkPointIso (a : GeometricPoint.Hom s s)
    (b : GeometricPoint.Hom t t) (h : θ.comp b = a.comp θ) (n : ℕ) :
    finiteLevelStalkEnd B X ℓ F b n ≫ (finiteLevelStalkPointIso B X ℓ F θ n).hom =
      (finiteLevelStalkPointIso B X ℓ F θ n).hom ≫ finiteLevelStalkEnd B X ℓ F a n :=
  (congrArg (fun α => NatTrans.app α (F.level n).obj)
    (geometricPointStalkMap_comp B X.1 X.property θ b
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))).symm.trans
    ((congrArg (fun c => NatTrans.app (geometricPointStalkMap B X.1 X.property c
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))) (F.level n).obj) h).trans
      (congrArg (fun α => NatTrans.app α (F.level n).obj)
        (geometricPointStalkMap_comp B X.1 X.property a θ
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))))

/-- **Endomorphisms related by a morphism of geometric points have the same trace on the rational
stalks.**  If `θ : s ⟶ t` carries `a : s ⟶ s` to `b : t ⟶ t`, that is `θ ∘ b = a ∘ θ`, then
`Tr(a | F_s ⊗ ℚ_ℓ) = Tr(b | F_t ⊗ ℚ_ℓ)`: both are the ℓ-adic limits of the traces at the finite
levels of the torsion-free model of `F`, where the stalk isomorphisms along `θ` intertwine the two
actions. -/
theorem LAdicSheaf.trace_rationalStalkEnd_eq_of_comm (a : GeometricPoint.Hom s s)
    (b : GeometricPoint.Hom t t) (h : θ.comp b = a.comp θ) :
    LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ F a) =
      LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ F b) := by
  obtain ⟨ta, hta, htan⟩ := LAdicSheaf.exists_trace_rationalStalkEnd_torsionFreeModel F a
  obtain ⟨tb, htb, htbn⟩ := LAdicSheaf.exists_trace_rationalStalkEnd_torsionFreeModel F b
  rw [hta, htb]
  congr 1
  refine eq_of_toZModPow_succ_eq (ℓ := ℓ) fun n => ?_
  rw [htan, htbn]
  exact (trace_hom_eq_of_comm (finiteLevelStalkPointIso B X ℓ
    (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) θ n) _ _
    (finiteLevelStalkEnd_comp_finiteLevelStalkPointIso B X ℓ _ θ a b h n)).symm

end PointChange

end Stacks.EtaleCohomology

end
