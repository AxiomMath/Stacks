module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.CategoryTheory.Inertia

/-!
# The inertia of a category fibred in groupoids (Stacks 042I)

Let `p : S ⥤ C` be a category fibred in groupoids. Its inertia `I_S` (the absolute inertia
`AbsoluteInertia p` of `StacksCore.CategoryTheory.Inertia`, whose objects are pairs `(x, α)` with
`α` an automorphism of `x` lying over the identity) is again fibred in groupoids over `C`.

Both clauses of `Functor.IsFiberedInGroupoids` for the inertia structure functor come from the
corresponding clauses for `p`, the point in each case being that the *automorphism* datum is
forced rather than chosen:

* a lift `ψ : y ⟶ x` of a base morphism carries the automorphism `α` of `x` back to a unique
  vertical endomorphism `β` of `y` with `β ≫ ψ = ψ ≫ α`, and `β` is invertible because it lies
  over an identity (`Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift` together with
  `Functor.IsStronglyCartesian.isIso_of_base_isIso`);
* the fill-in supplied by `p` automatically commutes with the two automorphisms, because both
  `χ ≫ β` and `β' ≫ χ` solve one and the same fill-in problem for `p`.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.exists_aut_of_lift`: the transport of an inertia
  automorphism along a lift.
* `CategoryTheory.Functor.IsFiberedInGroupoids.absoluteInertia`: **Stacks 042I**.
-/

@[expose] public section

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S] {p : S ⥤ C}

/-- **Transport of an inertia automorphism along a lift.** If `p` is fibred in groupoids,
`ψ : y ⟶ x` is any morphism of `S` and `α` is an automorphism of `x` lying over the identity,
then there is an automorphism `β` of `y` lying over the identity with `β ≫ ψ = ψ ≫ α`.

The fill-in clause of `Functor.IsFiberedInGroupoids` produces `β` as a vertical *endomorphism*;
it is invertible because a morphism lying over an identity is strongly cartesian over it, and a
strongly cartesian morphism over an isomorphism is an isomorphism. -/
theorem exists_aut_of_lift (hp : p.IsFiberedInGroupoids) {x y : S} (ψ : y ⟶ x) (α : Aut x)
    (hα : p.map α.hom = 𝟙 (p.obj x)) :
    ∃ β : Aut y, p.map β.hom = 𝟙 (p.obj y) ∧ β.hom ≫ ψ = ψ ≫ α.hom := by
  obtain ⟨χ, ⟨hχmap, hχfac⟩, -⟩ :=
    hp.unique_lift ψ (ψ ≫ α.hom) (𝟙 (p.obj y)) (by simp [hα])
  have : p.IsHomLift (𝟙 (p.obj y)) χ := hχmap ▸ (inferInstance : p.IsHomLift (p.map χ) χ)
  have := hp.isStronglyCartesian_homLift (𝟙 (p.obj y)) χ
  have : IsIso χ := IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 (p.obj y)) χ
  exact ⟨asIso χ, hχmap, hχfac⟩

/-- **Stacks 042I.** If `p : S ⥤ C` is fibred in groupoids, then so is the inertia fibred
category `I_S ⥤ C`. -/
@[stacks 042I]
theorem absoluteInertia (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) :
    (relativeInertiaStruct p p).IsFiberedInGroupoids := by
  constructor
  · -- Existence of lifts: lift the base morphism in `S`, then transport the automorphism.
    rintro V U f X rfl
    obtain ⟨y, ψ, hψ⟩ := hp.exists_lift f X.obj rfl
    obtain ⟨β, hβ, hβcomm⟩ := exists_aut_of_lift hp ψ X.auto X.cond
    refine ⟨⟨y, β, hβ⟩, ⟨ψ, hβcomm.symm⟩,
      IsHomLift.of_fac' _ f _ (IsHomLift.domain_eq p f ψ) rfl (IsHomLift.fac' p f ψ)⟩
  · -- Fill-ins: the fill-in for `p` automatically commutes with the two automorphisms.
    intro X Y Z Φ Ψ g hcomm
    obtain ⟨χ, ⟨hχmap, hχfac⟩, huniq⟩ := hp.unique_lift Φ.hom Ψ.hom g hcomm
    have hcomm' : g ≫ p.map Φ.hom = p.map (Ψ.hom ≫ X.auto.hom) := by
      rwa [p.map_comp, X.cond, Category.comp_id]
    have hχcomm : χ ≫ Y.auto.hom = Z.auto.hom ≫ χ :=
      (hp.unique_lift Φ.hom (Ψ.hom ≫ X.auto.hom) g hcomm').unique
        ⟨by rw [p.map_comp, Y.cond, Category.comp_id, hχmap],
          by rw [Category.assoc, ← Φ.comm, ← Category.assoc, hχfac]⟩
        ⟨by rw [p.map_comp, Z.cond, Category.id_comp, hχmap],
          by rw [Category.assoc, hχfac, Ψ.comm]⟩
    exact ⟨⟨χ, hχcomm⟩, ⟨hχmap, RelativeInertiaHom.ext hχfac⟩, fun χ' ⟨h₁, h₂⟩ ↦
      RelativeInertiaHom.ext (huniq χ'.hom ⟨h₁, congrArg RelativeInertiaHom.hom h₂⟩)⟩

end CategoryTheory.Functor.IsFiberedInGroupoids
