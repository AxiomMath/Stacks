module

public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Right acyclicity of a finite product of functors

`Stacks.RightAcyclicProduct.rightAcyclic_pi` closes right acyclicity under finite products of the
**object**, for a fixed functor.  This file does the other variable:  a functor which is a finite
product of functors is right acyclic at `M` as soon as every factor is.

No induction over the index type is needed, and no transport along an equivalence with `Fin n`.
The assignment `α ↦ NatTrans.rightDerived α n` is additive and functorial
(`CategoryTheory.NatTrans.rightDerived_zero`, `_add`, `_comp`, `_id`), so applying it to the
identity `∑ i, pᵢ ≫ qᵢ = 𝟙 W` of a finite product presentation writes the identity of
`Rⁿ W` as a finite sum of maps each factoring through `Rⁿ (F i)`.  At an object where every
factor vanishes, every summand is zero, so the identity is zero.  That is the whole proof, and it
is why the index type may live in any universe:  Mathlib's `Limits.biproduct` API, and with it
`Limits.biproduct.total`, is indexed by `Type 0`, while the index type of a simplicial degree of a
hypercovering lives in `Type u`.

## Main results

* `CategoryTheory.NatTrans.rightDerived_sum`:  `NatTrans.rightDerived · n` commutes with finite
  sums.
* `CategoryTheory.Functor.rightDerivedIsoOfIso`:  an isomorphism of functors induces one of their
  right derived functors.
* `CategoryTheory.Limits.sum_pi_π_comp_single_eq_id`:  the finite product presentation
  `∑ i, πᵢ ≫ ⟨δᵢⱼ⟩ = 𝟙`, for a product over a finite index in any universe.
* `CategoryTheory.Functor.isZero_rightDerived_obj_of_sum_comp_id` and
  `CategoryTheory.Functor.rightAcyclic_of_sum_comp_id`:  the statement above, with the product
  presented by that identity.
* `CategoryTheory.Functor.rightAcyclic_of_iso`:  right acyclicity transported along an
  isomorphism of functors.
* `CategoryTheory.Functor.rightAcyclic_of_isoPi`:  **the finite-product step** — a functor
  isomorphic to `∏ᶜ F` is right acyclic at `M` when every `F i` is.

## Implementation notes

The product form takes the functor `W` and an isomorphism `W ≅ ∏ᶜ F` rather than being stated
about `∏ᶜ F` itself.  That is not a convenience:  `rightAcyclic` needs its functor to be additive
and the `ℕ`-indexed criterion needs it left exact, and neither is available for `∏ᶜ F` by
synthesis, whereas the functor one actually has in hand — a degree of a relative Čech complex,
say — carries both.  Composing the projections with the isomorphism moves the product
presentation onto `W` and the two instances are never needed for `∏ᶜ F`.

`sum_pi_π_comp_single_eq_id` uses a single `eqToHom (congrArg X h)` for the diagonal entry of the
splitting, which is unavoidable in a family indexed by a type with no definitional case analysis;
it is one `eqToHom`, discharged immediately by `Pi.lift_π`, and not a chain.

## References

* [Stacks, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe vE uE

variable {E : Type uE} [Category.{vE} E] [Preadditive E]

/-- **A finite product is split by the family of "diagonal" lifts.**  The sum over the index of
the projection to a factor followed by the lift whose components are the identity at that factor
and zero elsewhere is the identity of the product.

This is `Limits.biproduct.total` without the restriction to a `Type 0` index:  the biproduct API
is indexed by `Type 0`, and the index type of a simplicial degree of a hypercovering is not. -/
theorem sum_pi_π_comp_single_eq_id {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → E) [HasProduct X] :
    ∑ i, Pi.π X i ≫ Pi.lift (fun j ↦ if h : i = j then eqToHom (congrArg X h) else 0) =
      𝟙 (∏ᶜ X) := by
  refine Pi.hom_ext _ _ (fun j ↦ ?_)
  rw [Category.id_comp, Preadditive.sum_comp]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro i _ hij
    rw [Category.assoc, Pi.lift_π, dif_neg hij, comp_zero]

end CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- **`NatTrans.rightDerived · n` commutes with finite sums.**  It takes zero to zero and
addition to addition, so it commutes with a `Finset` sum by induction on the `Finset`. -/
theorem NatTrans.rightDerived_sum {ι : Type*} (s : Finset ι) {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : ι → (F ⟶ G)) (n : ℕ) :
    NatTrans.rightDerived (∑ i ∈ s, α i) n = ∑ i ∈ s, NatTrans.rightDerived (α i) n := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using NatTrans.rightDerived_zero (F := F) (G := G) n
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, NatTrans.rightDerived_add, ih]

/-- **An isomorphism of additive functors induces an isomorphism of their right derived
functors.**  `NatTrans.rightDerived · n` is functorial, so it carries the two triangles of the
isomorphism to the two triangles of the image. -/
def Functor.rightDerivedIsoOfIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- **The higher right derived functors of a finite product of functors vanish where those of
every factor do.**  Applying the additive, functorial assignment `NatTrans.rightDerived · n` to
the splitting identity `∑ i, pᵢ ≫ qᵢ = 𝟙 W` writes `𝟙 (Rⁿ W)` as a finite sum of maps factoring
through `Rⁿ (F i)`; evaluated at `M` each summand factors through a zero object. -/
theorem Functor.isZero_rightDerived_obj_of_sum_comp_id {ι : Type*} (s : Finset ι)
    (W : C ⥤ D) [W.Additive] (F : ι → (C ⥤ D)) [∀ i, (F i).Additive]
    (p : ∀ i, W ⟶ F i) (q : ∀ i, F i ⟶ W)
    (htot : ∑ i ∈ s, p i ≫ q i = 𝟙 W)
    (M : C) (n : ℕ) (h : ∀ i ∈ s, IsZero (((F i).rightDerived n).obj M)) :
    IsZero ((W.rightDerived n).obj M) := by
  classical
  rw [IsZero.iff_id_eq_zero]
  have hsum : (𝟙 (W.rightDerived n) : W.rightDerived n ⟶ W.rightDerived n) =
      ∑ i ∈ s, NatTrans.rightDerived (p i) n ≫ NatTrans.rightDerived (q i) n := by
    rw [← NatTrans.rightDerived_id W n, ← htot, NatTrans.rightDerived_sum]
    exact Finset.sum_congr rfl fun i _ ↦ NatTrans.rightDerived_comp (p i) (q i) n
  have happ := congrArg (fun η : W.rightDerived n ⟶ W.rightDerived n ↦ η.app M) hsum
  simp only [NatTrans.id_app, NatTrans.app_sum, NatTrans.comp_app] at happ
  rw [happ]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [(h i hi).eq_of_tgt ((NatTrans.rightDerived (p i) n).app M) 0, zero_comp]

section Acyclic

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **Right acyclicity transported along an isomorphism of functors.** -/
theorem Functor.rightAcyclic_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] (e : F ≅ G) (M : C) (hF : F.rightAcyclic M) :
    G.rightAcyclic M := by
  have : PreservesFiniteLimits G := preservesFiniteLimits_of_natIso e
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  exact IsZero.of_iso ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat F M).1 hF n hn)
    ((Functor.rightDerivedIsoOfIso e n).app M).symm

/-- **A functor presented as a finite product by a splitting identity is right acyclic where
every factor is.** -/
theorem Functor.rightAcyclic_of_sum_comp_id {ι : Type*} (s : Finset ι)
    (W : C ⥤ D) [W.Additive] [PreservesFiniteLimits W]
    (F : ι → (C ⥤ D)) [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    (p : ∀ i, W ⟶ F i) (q : ∀ i, F i ⟶ W)
    (htot : ∑ i ∈ s, p i ≫ q i = 𝟙 W)
    (M : C) (h : ∀ i ∈ s, (F i).rightAcyclic M) :
    W.rightAcyclic M := by
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  exact Functor.isZero_rightDerived_obj_of_sum_comp_id s W F p q htot M n
    (fun i hi ↦ (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (F i) M).1 (h i hi) n hn)

/-- **The finite-product step:  a functor isomorphic to a finite product of functors is right
acyclic at `M` as soon as every factor is.**  The splitting identity of the product is moved onto
`W` by composing the projections and the diagonal lifts with the isomorphism, which is what keeps
`∏ᶜ F` from having to be additive or left exact itself. -/
theorem Functor.rightAcyclic_of_isoPi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : C ⥤ D) [W.Additive] [PreservesFiniteLimits W]
    (F : ι → (C ⥤ D)) [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [HasProduct F] (e : W ≅ ∏ᶜ F) (M : C) (h : ∀ i, (F i).rightAcyclic M) :
    W.rightAcyclic M := by
  classical
  refine Functor.rightAcyclic_of_sum_comp_id Finset.univ W F
    (fun i ↦ e.hom ≫ Pi.π F i)
    (fun i ↦ Pi.lift (fun j ↦ if hij : i = j then eqToHom (congrArg F hij) else 0) ≫ e.inv)
    ?_ M (fun i _ ↦ h i)
  have hstep : ∀ i : ι, (e.hom ≫ Pi.π F i) ≫
      (Pi.lift (fun j ↦ if hij : i = j then eqToHom (congrArg F hij) else 0) ≫ e.inv) =
      e.hom ≫ (Pi.π F i ≫
        Pi.lift (fun j ↦ if hij : i = j then eqToHom (congrArg F hij) else 0)) ≫ e.inv := by
    intro i
    simp only [Category.assoc]
  rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    Limits.sum_pi_π_comp_single_eq_id, Category.id_comp, e.hom_inv_id]

end Acyclic

end CategoryTheory

end
