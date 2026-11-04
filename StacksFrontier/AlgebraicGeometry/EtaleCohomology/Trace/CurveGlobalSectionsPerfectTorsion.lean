module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectStalkExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ProjectiveCurveBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem

/-!
# The twist complex is torsion

Let `Λ` be a finite ring, not necessarily commutative. Every twist `N ⊗[Λ] J` of a sheaf of
`Λ`-modules by a right `Λ`-module is killed by `|Λ|`, because `|Λ| = 0` in `Λ`; so are the terms
of the twist complex `R ⊠ I` and its sheaves of cycles. On the base change `X_{k̄}` of a curve
`X` over `k` to an algebraically closed field such a torsion sheaf has no cohomology above degree
two, by Tag 0A53. This is the vanishing input of the dimension shifting in the proof of
[Stacks, Tag 03TV]; the vanishing itself is
`Stacks.SheafTwist.subsingleton_ext_twistComplex_cycles`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTorVanishing`.

## Main results

* `Stacks.SheafTwist.nsmul_id_twistComplex_X`: `|Λ|` kills the terms of `R ⊠ I`.
* `Stacks.SheafTwist.torsionSheafProperty_twistComplex_cycles`: the cycles of `R ⊠ I` are torsion.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Abelian HomologicalComplex
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe w u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ] [Finite Λ]

/-- Multiples of a morphism of abelian sheaves act sectionwise as multiples. -/
lemma nsmul_hom_app_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ) (x : F.obj.obj U) :
    (n • f).hom.app U x = n • f.hom.app U x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul, Sheaf.Hom.add_app, AddCommGrpCat.hom_add_apply, ih]

omit [Finite Λ] in
/-- **A twist is killed by `|Λ|`**: on a pure tensor, `|Λ| • (n ⊗ m) = n ⊗ (|Λ| : Λ) • m = 0`. -/
lemma card_nsmul_tensor (D : BalancedDerivedTensoring.{r, w} Λ) (N : ModuleCat.{w} (MulOpposite Λ))
    (M : ModuleCat.{w} Λ) (x : (D.ordinary.obj N).obj M) : Nat.card Λ • x = 0 := by
  have h := tensor_ext D (Nat.card Λ • 𝟙 ((D.ordinary.obj N).obj M)) 0 (fun n m => by
    show Nat.card Λ • D.pure N M n m = 0
    have hc : (Nat.card Λ : Λ) = 0 := by rw [← nsmul_one, card_nsmul_eq_zero']
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul Λ, hc, zero_smul, map_zero])
  exact congrArg (fun f : (D.ordinary.obj N).obj M ⟶ _ => f x) h

variable (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ) (Y : Scheme.{u})

omit [Finite Λ] in
/-- **The twist of a sheaf by a finite free module is killed by `|Λ|`.** -/
lemma nsmul_id_twist (N : FiniteFree.{max (u + 1) r} Λ)
    (J : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    Nat.card Λ • 𝟙 (((twist.{u, r} D Y).obj N).obj J) = 0 := by
  apply Sheaf.hom_ext
  ext U x
  rw [nsmul_hom_app_apply]
  exact card_nsmul_tensor D N.obj (J.obj.obj U) x

omit [Finite Λ] in
/-- **The terms of the twist complex are killed by `|Λ|`.** -/
lemma nsmul_id_twistComplex_X (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    [HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)] (n : ℤ) :
    Nat.card Λ • 𝟙 ((twistComplex D Y R I).X n) = 0 := by
  let K := ((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj R |>.obj I
  show Nat.card Λ • 𝟙 ((K.total (ComplexShape.up ℤ)).X n) = 0
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have h : Nat.card Λ • 𝟙 ((K.X p).X q) = 0 := nsmul_id_twist.{u, r} D Y (R.X p) (I.X q)
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp
    (K.ιTotal (ComplexShape.up ℤ) p q n hpq), ← Preadditive.nsmul_comp, h, zero_comp]

/-- **The cycles of the twist complex are torsion**: they are killed by `|Λ|`. -/
lemma torsionSheafProperty_twistComplex_cycles
    (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    [HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)] (n : ℤ) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology ((twistComplex D Y R I).cycles n) := by
  have hz : Nat.card Λ • 𝟙 ((twistComplex D Y R I).cycles n) = 0 := by
    rw [← cancel_mono ((twistComplex D Y R I).iCycles n), Preadditive.nsmul_comp, Category.id_comp,
      zero_comp, ← Category.comp_id ((twistComplex D Y R I).iCycles n), ← Preadditive.comp_nsmul,
      nsmul_id_twistComplex_X, comp_zero]
  intro U x
  refine ⟨⊤, Y.smallEtaleTopology.top_mem U, fun V f _ => ⟨Nat.card Λ, Nat.card_pos, ?_⟩⟩
  exact (nsmul_hom_app_apply (𝟙 _) _ (op V) _).symm.trans (by rw [hz]; rfl)

end Stacks.SheafTwist

end
