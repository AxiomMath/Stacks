module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Regular functions on `Spec 𝒪_{X,x}` come from a neighbourhood of `x`

Let `X` be a scheme and `x ∈ X`. Every global regular function on `Spec 𝒪_{X,x}` is the pullback,
along `Spec 𝒪_{X,x} ⟶ V`, of a regular function on some open neighbourhood `V` of `x`, and `V`
may be chosen inside any given neighbourhood of `x`. For finitely many functions one `V` serves
all of them. This is the statement that `𝒪_{X,x}` is the colimit of the rings `𝒪_X(V)`, read
on the canonical morphisms `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem`.

## Main results

* `AlgebraicGeometry.Scheme.exists_le_fromSpecStalkOfMem_appTop_eq`: a regular function on
  `Spec 𝒪_{X,x}` is the pullback of a regular function on a neighbourhood of `x` inside `W`.
* `AlgebraicGeometry.Scheme.exists_le_forall_fromSpecStalkOfMem_appTop_eq`: the same for finitely
  many functions, with one neighbourhood for all of them.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (x : X)

/-- Restricting a regular function from `V` to a smaller neighbourhood `V'` of `x` does not change
its pullback to `Spec 𝒪_{X,x}`. -/
theorem fromSpecStalkOfMem_appTop_homOfLE {V V' : X.Opens} (h : V' ≤ V) (hx : x ∈ V')
    (a : Γ(V, ⊤)) :
    (V'.fromSpecStalkOfMem x hx).appTop ((X.homOfLE h).appTop a) =
      (V.fromSpecStalkOfMem x (h hx)).appTop a := by
  have e : V'.fromSpecStalkOfMem x hx ≫ X.homOfLE h = V.fromSpecStalkOfMem x (h hx) := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, Opens.fromSpecStalkOfMem_ι,
      Opens.fromSpecStalkOfMem_ι]
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

/-- **A regular function on `Spec 𝒪_{X,x}` comes from a neighbourhood of `x` inside `W`.** -/
theorem exists_le_fromSpecStalkOfMem_appTop_eq {W : X.Opens} (hW : x ∈ W)
    (c : Γ(Spec (X.presheaf.stalk x), ⊤)) :
    ∃ (V : X.Opens) (_ : V ≤ W) (hx : x ∈ V) (a : Γ(V, ⊤)),
      (V.fromSpecStalkOfMem x hx).appTop a = c := by
  obtain ⟨V, hVW, hx, s, hs⟩ := X.presheaf.exists_le_germ_eq
    ((ΓSpecIso (X.presheaf.stalk x)).hom c) hW
  change X.Opens at V
  refine ⟨V, hVW, hx, (Scheme.Opens.toSpecΓ V).appTop ((ΓSpecIso Γ(X, V)).inv s), ?_⟩
  have h₁ := congrArg (fun φ => (Hom.appTop φ).hom ((ΓSpecIso Γ(X, V)).inv s))
    (Opens.fromSpecStalkOfMem_toSpecΓ V x hx)
  have h₂ := congrArg (fun φ => φ.hom s)
    (ΓSpecIso_inv_naturality (X.presheaf.germ V x hx))
  simp only [Hom.comp_appTop, CommRingCat.comp_apply] at h₁ h₂
  refine h₁.trans (h₂.symm.trans ?_)
  rw [hs]
  exact (ΓSpecIso (X.presheaf.stalk x)).hom_inv_id_apply c

/-- **Finitely many regular functions on `Spec 𝒪_{X,x}` come from one neighbourhood of `x`
inside `W`.** -/
theorem exists_le_forall_fromSpecStalkOfMem_appTop_eq {W : X.Opens} (hW : x ∈ W) {ι : Type*}
    (s : Finset ι) (c : ι → Γ(Spec (X.presheaf.stalk x), ⊤)) :
    ∃ (V : X.Opens) (_ : V ≤ W) (hx : x ∈ V) (a : ι → Γ(V, ⊤)),
      ∀ i ∈ s, (V.fromSpecStalkOfMem x hx).appTop (a i) = c i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨W, le_rfl, hW, fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s hj ih =>
    obtain ⟨V₀, hV₀W, hx₀, a₀, ha₀⟩ := ih
    obtain ⟨V, hVV₀, hx, b, hb⟩ := exists_le_fromSpecStalkOfMem_appTop_eq x hx₀ (c j)
    refine ⟨V, hVV₀.trans hV₀W, hx,
      fun i => if i = j then b else (X.homOfLE hVV₀).appTop (a₀ i), fun i hi => ?_⟩
    by_cases hij : i = j
    · subst hij
      simpa using hb
    · simp only [if_neg hij, fromSpecStalkOfMem_appTop_homOfLE x hVV₀ hx]
      exact ha₀ i ((Finset.mem_insert.1 hi).resolve_left hij)

end AlgebraicGeometry.Scheme

end
