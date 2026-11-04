module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleDomination
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory

/-!
# Base changes of finite étale covers are cofinal under domination

Let `g : X' ⟶ X` be a morphism of connected schemes which dominates finite étale covers
(`AlgebraicGeometry.DominatesFiniteEtale`): every finite étale cover of `X'` embeds into the base
change of a finite étale cover of `X`. This file upgrades the embedding to a map the other way:
every nonempty finite étale cover `V` of `X'` receives a morphism over `X'` from the base change
`W ×_X X'` of a nonempty finite étale cover `W` of `X`.

For `g : X_k̄ ⟶ X` this is the cofinality used in the proof of Tag 03VM: a cohomology class on
`X_k̄` which dies on some finite étale cover of `X_k̄` already dies on the base change of a finite
étale cover of `X`.

## The argument

Let `V ↪ U ×_X X'` be the embedding, `Γ = π₁(X, x)`, `G = π₁(X', x')` with `x = g ∘ x'`, and `S`
the geometric fibre of `U`. The finite `Γ`-set `Q = Perm S` of frames of `S`, with `Γ` acting by
postcomposition, has every stabilizer equal to the kernel of `Γ` acting on `S`. By Tag 0BND it is
the fibre of a finite étale cover `W` of `X`. The fibre of `W ×_X X'` is `Q`, with `G` acting
through `G → Γ`; so an element of `G` fixing a point of it acts trivially on `S`, hence on the
fibre of `U ×_X X'`, hence on that of `V`. A `G`-set all of whose stabilizers act trivially on a
nonempty `G`-set `T` maps equivariantly to `T`
(`MulAction.exists_smul_equivariant_of_forall_smul_eq`), and Tag 0BND for `X'` turns that
equivariant map into a morphism `W ×_X X' ⟶ V`.

## Main results

* `MulAction.exists_smul_equivariant_of_forall_smul_eq` — the orbit-representative construction.
* `AlgebraicGeometry.nonempty_finiteEtaleFiber_of_nonempty_left` — a nonempty finite étale cover
  of a connected scheme has a nonempty geometric fibre.
* `AlgebraicGeometry.exists_hom_finiteEtaleBaseChange_of_dominatesFiniteEtale` — cofinality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup
open scoped FintypeCatDiscrete

universe u

namespace MulAction

/-- **Equivariant maps out of a `G`-set whose stabilizers act trivially.** Let `G` act on `A` and
on a nonempty `Y`, and suppose every element of `G` fixing some point of `A` fixes every point of
`Y`. Then there is a `G`-equivariant map `A → Y`: send `c • r` to `c • y₀`, for `r` a chosen
representative of each orbit. -/
theorem exists_smul_equivariant_of_forall_smul_eq {G A Y : Type*} [Group G] [MulAction G A]
    [MulAction G Y] (y₀ : Y) (h : ∀ (g : G) (a : A), g • a = a → ∀ y : Y, g • y = y) :
    ∃ t : A → Y, ∀ (g : G) (a : A), t (g • a) = g • t a := by
  classical
  let r : A → A := fun a ↦ (Quotient.mk (orbitRel G A) a).out
  have hr : ∀ a, ∃ c : G, c • a = r a := fun a ↦
    (orbitRel_apply).1 (Quotient.mk_out (s := orbitRel G A) a)
  choose c hc using hr
  refine ⟨fun a ↦ (c a)⁻¹ • y₀, fun g a ↦ ?_⟩
  have hra : r (g • a) = r a :=
    congrArg Quotient.out (Quotient.sound ((orbitRel_apply).2 ⟨g, rfl⟩))
  have hfix : ((c a)⁻¹ * c (g • a) * g) • a = a := by
    rw [mul_smul, mul_smul, hc, hra, ← hc a, inv_smul_smul]
  calc (c (g • a))⁻¹ • y₀
      = (c (g • a))⁻¹ • (c a • ((c a)⁻¹ * c (g • a) * g) • (c a)⁻¹ • y₀) := by
        rw [h _ a hfix ((c a)⁻¹ • y₀), smul_inv_smul]
    _ = g • (c a)⁻¹ • y₀ := by
        simp only [← mul_smul]
        congr 1
        group

end MulAction

namespace AlgebraicGeometry

section Fibre

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-- **A nonempty finite étale cover of a connected scheme has a nonempty geometric fibre**: a cover
with empty fibre is initial in the Galois category of finite étale covers, hence has empty
source. -/
theorem nonempty_finiteEtaleFiber_of_nonempty_left (V : FiniteEtaleOver X) [Nonempty V.left] :
    Nonempty ((finiteEtaleFiberFunctor x).obj V) := by
  let : CategoryTheory.GaloisCategory (FiniteEtaleOver X) :=
    IsGaloisCategory.toGaloisCategory (finiteEtaleFiberFunctor x)
  let : IsGaloisCategory (finiteEtaleFiberFintypeFunctor X x ⋙ FintypeCat.incl) :=
    isGaloisCategory_finiteEtaleFiberFunctor x
  let : PreGaloisCategory.FiberFunctor (finiteEtaleFiberFintypeFunctor X x) :=
    IsGaloisCategory.fiberFunctor (finiteEtaleFiberFintypeFunctor X x)
  exact (PreGaloisCategory.not_initial_iff_fiber_nonempty
    (finiteEtaleFiberFintypeFunctor X x) V).1
      fun h ↦ (isEmpty_left_of_isInitial_finiteEtaleOver V h).false (Classical.arbitrary _)

/-- On the equivalence `AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory`, an element of
the fundamental group acts on the fibre of a cover by its `MulAction`. -/
theorem finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply (Y : FiniteEtaleOver X)
    (σ : EtaleFundamentalGroup X x) (y : (finiteEtaleFiberFunctor x).obj Y) :
    (ConcreteCategory.hom
      (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.ρ σ) y :
        (finiteEtaleFiberFunctor x).obj Y) = σ • y :=
  finiteEtaleEquivalenceOfIsGaloisCategory_action X x Y σ y

end Fibre

section Frames

variable {Γ S : Type*} [Group Γ] [MulAction Γ S]

/-- The action of `Γ` on the frames `S ≃ S` of a `Γ`-set, by postcomposition. -/
@[reducible] def frameMulAction : MulAction Γ (S ≃ S) where
  smul σ e := e.trans (MulAction.toPerm σ)
  one_smul e := Equiv.ext fun s ↦ one_smul Γ (e s)
  mul_smul σ τ e := Equiv.ext fun s ↦ mul_smul σ τ (e s)

/-- An element fixing a frame fixes every point. -/
theorem smul_eq_of_frame_smul_eq {σ : Γ} {e : S ≃ S}
    (h : @HSMul.hSMul Γ (S ≃ S) (S ≃ S) (@instHSMul _ _ (frameMulAction).toSMul) σ e = e)
    (s : S) : σ • s = s := by
  have := congrArg (fun e' : S ≃ S ↦ e' (e.symm s)) h
  change (MulAction.toPerm σ) (e (e.symm s)) = e (e.symm s) at this
  simpa using this

end Frames

/-- **Cofinality of base changes under domination.** Let `g : X' ⟶ X` be a morphism of connected
schemes dominating finite étale covers, and `x'` a geometric point of `X'`. Every nonempty finite
étale cover `V` of `X'` receives a morphism of covers from the base change of a nonempty finite
étale cover `W` of `X`. -/
theorem exists_hom_finiteEtaleBaseChange_of_dominatesFiniteEtale {X' X : Scheme.{u}}
    [ConnectedSpace X'] [ConnectedSpace X] (g : X' ⟶ X) (hg : DominatesFiniteEtale g)
    (x' : GeometricPoint X') (V : FiniteEtaleOver X') [Nonempty V.left] :
    ∃ W : FiniteEtaleOver X, Nonempty W.left ∧ Nonempty ((finiteEtaleBaseChange g).obj W ⟶ V) := by
  classical
  obtain ⟨U, j, hj⟩ := hg V
  let x : GeometricPoint X := x'.map g
  let S := (finiteEtaleFiberFunctor x).obj U
  have : Finite S := finite_finiteEtaleFiber x U
  have : Fintype S := Fintype.ofFinite S
  let : MulAction (EtaleFundamentalGroup X x) (S ≃ S) := frameMulAction
  -- the frames of `S` as a finite continuous `π₁(X, x)`-set
  let Q : Action FintypeCat.{u} (EtaleFundamentalGroup X x) :=
    Action.FintypeCat.ofMulAction (EtaleFundamentalGroup X x) (FintypeCat.of (S ≃ S))
  have hQ : Q.IsContinuous := by
    have : DiscreteTopology ((forget₂ _ TopCat).obj Q) := ⟨rfl⟩
    refine continuousSMul_iff_stabilizer_isOpen.2 fun e ↦ ?_
    have hset : (MulAction.stabilizer (EtaleFundamentalGroup X x) e : Set _) =
        ⋂ s : S, {σ : EtaleFundamentalGroup X x | σ • s = s} := by
      ext σ
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h s ↦ smul_eq_of_frame_smul_eq (e := (e : S ≃ S)) h s, fun h ↦ ?_⟩
      exact Equiv.ext fun s ↦ h ((show S ≃ S from e) s)
    rw [hset]
    refine isOpen_iInter_of_finite fun s ↦ ?_
    let : TopologicalSpace S := ⊥
    have : DiscreteTopology S := ⟨rfl⟩
    exact @Continuous.isOpen_preimage _ _ (functorAutomorphismTopology _) ⊥ _
      (continuous_componentEmbedding_apply (finiteEtaleFiberFunctor x) U s) {s} trivial
  let E := finiteEtaleEquivalenceOfIsGaloisCategory X x
  let Qc : ContAction FintypeCat.{u} (EtaleFundamentalGroup X x) := ⟨Q, hQ⟩
  let W := E.inverse.obj Qc
  let c := E.counitIso.app Qc
  let ψ : (finiteEtaleFiberFunctor x).obj W → (S ≃ S) := fun w ↦
    ConcreteCategory.hom c.hom.hom.hom w
  have hψ : ∀ (σ : EtaleFundamentalGroup X x) (w : (finiteEtaleFiberFunctor x).obj W),
      ψ (σ • w) = σ • ψ w := by
    intro σ w
    have h : ConcreteCategory.hom c.hom.hom.hom
        (ConcreteCategory.hom ((E.functor.obj W).obj.ρ σ) w) =
          ConcreteCategory.hom (Qc.obj.ρ σ) (ConcreteCategory.hom c.hom.hom.hom w) :=
      ConcreteCategory.congr_hom (c.hom.hom.comm σ) w
    rwa [finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply] at h
  -- `W` is nonempty: its fibre contains the preimage of the identity frame
  have hWne : Nonempty W.left := by
    let w₀ : (finiteEtaleFiberFunctor x).obj W :=
      ConcreteCategory.hom c.inv.hom.hom (Equiv.refl S)
    exact ⟨w₀.1.base (Classical.arbitrary _)⟩
  -- an element of `π₁(X', x')` fixing a point of the fibre of `W ×_X X'` fixes the fibre of `V`
  have hstab : ∀ (τ : EtaleFundamentalGroup X' x')
      (w : (finiteEtaleFiberFunctor x').obj ((finiteEtaleBaseChange g).obj W)), τ • w = w →
        ∀ v : (finiteEtaleFiberFunctor x').obj V, τ • v = v := by
    intro τ w hw v
    let pW : (finiteEtaleFiberFunctor x').obj ((finiteEtaleBaseChange g).obj W) →
        (finiteEtaleFiberFunctor x).obj W := finiteEtaleFiberProjection g x' W
    have h1 : etaleFundamentalGroupMap g x' τ • pW w = pW w := by
      change ((etaleFundamentalGroupMap g x' τ).app W).hom _ = _
      rw [← etaleFundamentalGroupMap_finiteEtaleFiberProjection]
      exact congrArg _ hw
    have h2 : etaleFundamentalGroupMap g x' τ • ψ (pW w) = ψ (pW w) := by
      rw [← hψ, h1]
    have h4 : ∀ y : (finiteEtaleFiberFunctor x').obj ((finiteEtaleBaseChange g).obj U),
        τ • y = y := by
      intro y
      apply (finiteEtaleFiberProjectionEquiv g x' U).injective
      change finiteEtaleFiberProjection g x' U ((τ.app _).hom y) =
        finiteEtaleFiberProjection g x' U y
      rw [etaleFundamentalGroupMap_finiteEtaleFiberProjection]
      exact smul_eq_of_frame_smul_eq h2 _
    have hinj : Function.Injective (ConcreteCategory.hom ((finiteEtaleFiberFunctor x').map j)) :=
      fun _ _ hab ↦ Subtype.ext ((cancel_mono j.left).1 (congrArg Subtype.val hab))
    apply hinj
    change ConcreteCategory.hom ((finiteEtaleFiberFunctor x').map j) ((τ.app V).hom v) =
      ConcreteCategory.hom ((finiteEtaleFiberFunctor x').map j) v
    exact (ConcreteCategory.congr_hom (τ.hom.naturality j) v).symm.trans (h4 _)
  obtain ⟨y₀⟩ := nonempty_finiteEtaleFiber_of_nonempty_left x' V
  obtain ⟨t, ht⟩ := MulAction.exists_smul_equivariant_of_forall_smul_eq y₀ hstab
  let E' := finiteEtaleEquivalenceOfIsGaloisCategory X' x'
  let hAct : (E'.functor.obj ((finiteEtaleBaseChange g).obj W)).obj ⟶ (E'.functor.obj V).obj :=
    { hom := FintypeCat.homMk t
      comm := fun τ ↦ by
        ext w
        change t (ConcreteCategory.hom
            ((E'.functor.obj ((finiteEtaleBaseChange g).obj W)).obj.ρ τ) w) =
          ConcreteCategory.hom ((E'.functor.obj V).obj.ρ τ) (t w)
        exact (congrArg t (finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply x' _ τ w)).trans
          ((ht τ w).trans (finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply x' V τ (t w)).symm) }
  exact ⟨W, hWne, ⟨E'.functor.preimage (ObjectProperty.homMk hAct)⟩⟩

end AlgebraicGeometry

end
