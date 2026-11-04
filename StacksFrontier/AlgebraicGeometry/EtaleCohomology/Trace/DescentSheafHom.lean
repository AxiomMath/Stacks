module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DualRepresentationHomFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentSheaf

/-!
# A locally constant sheaf as `Hom_{A[H]}(N^∨, D(A[H]))`

Let `G : V ⟶ U` be a Galois covering with finite group `H`, `A = ℤ/n`, `Λ` an `A`-algebra and `N`
a finite `Λ`-module with an action `ρ` of `H`. The descent sheaf `F = D(N)` of `N` along `G`
(sections over `W`: the `H`-equivariant locally constant maps `W ×_U V → N`) is
`Hom_{A[H]}(N^∨, D(A[H]))`, where `D(A[H])` is the descent sheaf of the regular representation:
a section `t` of `F` goes to `φ ↦ (z ↦ ψ_{t(z)}(φ))`, with `ψ_y(φ) = ∑_g φ(g y) g`. This is
Steps 4 to 6 of the proof of [Stacks, Tag 03UG], in the form `F = Hom_{A[H]}(N^∨, f_* A)`.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.descentSheafHomIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Finset MonoidAlgebra

universe u

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {H : Type} [Group H] [Fintype H] {n : ℕ} [NeZero n] {Λ : Type} [Ring Λ]
  [Algebra (ZMod n) Λ] {N : Type (u + 1)} [AddCommGroup N] [Module Λ N] [Module (ZMod n) N]
  [IsScalarTower (ZMod n) Λ N] (ρ : H →* Module.End Λ N)

omit [NeZero n] in
/-- `ψ_{h y} = ψ_y · h⁻¹`. -/
lemma dualRepHom_act (h : H) (y : N) (φ : DualRep (restrictRep (A := ZMod n) ρ)) :
    dualRepHom (restrictRep (A := ZMod n) ρ) (ρ h y) φ =
      dualRepHom (restrictRep (A := ZMod n) ρ) y φ * single h⁻¹ 1 := by
  show ∑ g : H, single g (DualRep.equiv _ φ (ρ g (ρ h y))) =
    (∑ g : H, single g (DualRep.equiv _ φ (ρ g y))) * single h⁻¹ 1
  rw [sum_mul]
  simp only [single_mul_single, mul_one]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  simp [← Module.End.mul_apply, ← map_mul]

variable {U : Scheme.{u}} (G : EtaleGaloisCovering U H)

local notation "R" => MonoidAlgebra (ZMod n) H

/-- The section `z ↦ ψ_{t(z)}(φ)` of `D(A[H])` attached to a section `t` of `D(N)` and
`φ ∈ N^∨`. -/
def homSection {W : U.Etale} (t : G.equivariantMaps Λ N ρ W)
    (φ : DualRep (restrictRep (A := ZMod n) ρ)) :
    G.equivariantMaps R (ULift.{u + 1} R) (rightRegularRepULift.{u} (ZMod n) H) W :=
  ⟨t.1.map fun y => ULift.up (dualRepHom (restrictRep (A := ZMod n) ρ) y φ), fun h z => by
    change ULift.up (dualRepHom _ (t.1 ((G.pullbackAct W h).base z)) φ) =
      ULift.up (dualRepHom _ (t.1 z) φ * single h⁻¹ 1)
    rw [t.2 h z, dualRepHom_act]⟩

omit [NeZero n] in
/-- The value of `G.homSection ρ t φ` at `z` is `ψ_{t(z)}(φ)`. -/
@[simp]
lemma homSection_apply {W : U.Etale} (t : G.equivariantMaps Λ N ρ W)
    (φ : DualRep (restrictRep (A := ZMod n) ρ)) (z : G.fiberProd W) :
    (G.homSection ρ t φ).1 z = ULift.up (dualRepHom (restrictRep (A := ZMod n) ρ) (t.1 z) φ) :=
  rfl

/-- `φ ↦ (z ↦ ψ_{t(z)}(φ))`, an `A[H]`-linear map `N^∨ → D(A[H])(W)`. -/
def homSectionHom {W : U.Etale} (t : G.equivariantMaps Λ N ρ W) :
    dualRepModule (A := ZMod n) ρ ⟶
      ModuleCat.of R
        (G.equivariantMaps R (ULift.{u + 1} R) (rightRegularRepULift.{u} (ZMod n) H) W) :=
  ModuleCat.ofHom
    { toFun := G.homSection ρ t
      map_add' := fun φ φ' => Subtype.ext (LocallyConstant.ext fun z => ULift.ext _ _ (by
        change dualRepHom _ (t.1 z) (φ + φ') = dualRepHom _ (t.1 z) φ + dualRepHom _ (t.1 z) φ'
        exact map_add _ _ _))
      map_smul' := fun r φ => Subtype.ext (LocallyConstant.ext fun z => ULift.ext _ _ (by
        change dualRepHom _ (t.1 z) (r • φ) = r * dualRepHom _ (t.1 z) φ
        exact (dualRepHom _ (t.1 z)).map_smul r φ)) }

/-- `t ↦ (φ ↦ (z ↦ ψ_{t(z)}(φ)))`, the comparison `D(N)(W) → Hom_{A[H]}(N^∨, D(A[H])(W))`. -/
def homSectionLinear (W : U.Etale) :
    G.equivariantMaps Λ N ρ W →ₗ[Λ]
      (Stacks.EtaleCohomology.homFunctor (dualRepModule (A := ZMod n) ρ)
        (dualRepRightAction (A := ZMod n) ρ)).obj
          (ModuleCat.of R (G.equivariantMaps R (ULift.{u + 1} R)
            (rightRegularRepULift.{u} (ZMod n) H) W)) where
  toFun t := G.homSectionHom ρ t
  map_add' t t' := ModuleCat.hom_ext (LinearMap.ext fun φ =>
    Subtype.ext (LocallyConstant.ext fun z => ULift.ext _ _ (by
      change ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) (t.1 z + t'.1 z))) =
        ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) (t.1 z))) +
          ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) (t'.1 z)))
      simp only [map_add, single_add, sum_add_distrib])))
  map_smul' l t := ModuleCat.hom_ext (LinearMap.ext fun φ =>
    Subtype.ext (LocallyConstant.ext fun z => ULift.ext _ _ (by
      change ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) (l • t.1 z))) =
        ∑ g : H, single g (DualRep.equiv _ (dualRepRightMul (A := ZMod n) ρ l φ) ((ρ g) (t.1 z)))
      simp only [map_smul]
      rfl)))

/-- **The comparison is bijective on sections**, for `N` finite. -/
theorem bijective_homSectionLinear [Finite N] (W : U.Etale) :
    Function.Bijective (G.homSectionLinear (n := n) ρ W) := by
  classical
  have hb := bijective_dualRepHom (restrictRep (A := ZMod n) ρ)
    (Stacks.LAdic.bijective_dual_eval_zmod N)
  let ψ := dualRepHom (restrictRep (A := ZMod n) ρ)
  have : Finite (DualRep (restrictRep (A := ZMod n) ρ)) :=
    Finite.of_injective
      (fun φ : DualRep (restrictRep (A := ZMod n) ρ) =>
        ((DualRep.equiv _ φ : Module.Dual (ZMod n) N) : N → ZMod n))
      (fun φ φ' h => (DualRep.equiv _).injective (DFunLike.coe_injective h))
  refine ⟨fun t t' htt =>
    Subtype.ext (LocallyConstant.ext fun z => hb.1 (LinearMap.ext fun φ => ?_)), fun Φ => ?_⟩
  · exact congrArg (fun F : dualRepModule (A := ZMod n) ρ ⟶ ModuleCat.of R
      (G.equivariantMaps R (ULift.{u + 1} R) (rightRegularRepULift.{u} (ZMod n) H) W) =>
        ((ModuleCat.Hom.hom F φ).1 z).down) htt
  have : Finite (dualRepModule (A := ZMod n) ρ) :=
    inferInstanceAs (Finite (DualRep (restrictRep (A := ZMod n) ρ)))
  let Φ' : dualRepModule (A := ZMod n) ρ ⟶ ModuleCat.of R
      (G.equivariantMaps R (ULift.{u + 1} R) (rightRegularRepULift.{u} (ZMod n) H) W) := Φ
  let L : G.fiberProd W → (DualRep (restrictRep (A := ZMod n) ρ) →ₗ[R] R) := fun z =>
    { toFun := fun φ => ((Φ'.hom φ).1 z).down
      map_add' := fun φ φ' => congrArg (fun s => (s.1 z).down) (Φ'.hom.map_add φ φ')
      map_smul' := fun r φ => congrArg (fun s => (s.1 z).down) (Φ'.hom.map_smul r φ) }
  let ψinv := Function.surjInv hb.2
  have hψ : ∀ f, ψ (ψinv f) = f := Function.surjInv_eq hb.2
  have hL : IsLocallyConstant L := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro f₀
    have : L ⁻¹' {f₀} = ⋂ φ, {z | (Φ'.hom φ).1 z = ULift.up (f₀ φ)} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      refine ⟨fun h φ => ULift.ext _ _ (by rw [← h]; rfl), fun h => LinearMap.ext fun φ => ?_⟩
      exact congrArg ULift.down (h φ)
    rw [this]
    exact isOpen_iInter_of_finite fun φ => (Φ'.hom φ).1.isLocallyConstant.isOpen_fiber _
  let t₀ : LocallyConstant (G.fiberProd W) N := ⟨fun z => ψinv (L z), (hL.comp ψinv)⟩
  have ht₀ : t₀ ∈ G.equivariantMaps Λ N ρ W := by
    intro h z
    apply hb.1
    show ψ (ψinv (L ((G.pullbackAct W h).base z))) = ψ (ρ h (ψinv (L z)))
    refine LinearMap.ext fun φ => ?_
    rw [hψ]
    show ((Φ'.hom φ).1 ((G.pullbackAct W h).base z)).down = ψ (ρ h (ψinv (L z))) φ
    have h2 : dualRepHom (restrictRep (A := ZMod n) ρ) (ψinv (L z)) = L z := hψ (L z)
    rw [(Φ'.hom φ).2 h z, dualRepHom_act, h2]
    rfl
  refine ⟨⟨t₀, ht₀⟩, ModuleCat.hom_ext (LinearMap.ext fun φ =>
    Subtype.ext (LocallyConstant.ext fun z => ULift.ext _ _ ?_))⟩
  show ψ (ψinv (L z)) φ = ((Φ'.hom φ).1 z).down
  rw [hψ]
  rfl

/-- **Steps 4 to 6 of [Stacks, Tag 03UG]: `D(N) ≅ Hom_{A[H]}(N^∨, D(A[H]))`**, for `A = ℤ/n` and
`N` a finite `Λ`-module with an action of `H`. -/
def descentSheafHomIso [Finite N] :
    G.descentSheaf.{u, 0, 0, u + 1} Λ N ρ ≅
      (Stacks.EtaleCohomology.etaleModuleHom (dualRepModule (A := ZMod n) ρ)
        (dualRepRightAction (A := ZMod n) ρ) U).obj (G.regularDescentSheaf (A := ZMod n)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun W => (LinearEquiv.ofBijective (G.homSectionLinear (n := n) ρ W.unop)
        (G.bijective_homSectionLinear (n := n) ρ W.unop)).toModuleIso)
      (fun {W W'} g => by
        ext t
        exact ModuleCat.hom_ext (LinearMap.ext fun φ =>
          Subtype.ext (LocallyConstant.ext fun z => rfl))))

end AlgebraicGeometry.EtaleGaloisCovering

end
