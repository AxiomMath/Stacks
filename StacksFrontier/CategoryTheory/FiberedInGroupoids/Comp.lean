module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of categories fibred in groupoids (Stacks 09WW)

Stacks Tag `09WW` (Lemma 4.35.13): if `p : 𝒜 ⥤ ℬ` and `q : ℬ ⥤ 𝒞` are fibred in
groupoids, then so is `p ⋙ q`.

The proof verifies the two primitive axioms of the canonical predicate
`CategoryTheory.Functor.IsFiberedInGroupoids` (Stacks `003S`) directly, rather than
going through the characterization "fibred category with groupoid fibres"
(Stacks `003V`): lifts for `p ⋙ q` are obtained by lifting along `q` and then along
`p`, and a fill-in for `p ⋙ q` is obtained by first factoring the base morphism
through `q`'s uniqueness clause and then lifting the resulting `ℬ`-morphism through
`p`'s. Verticality of the composed lift is packaged as `IsHomLift.comp_functor`,
which composes a lift along two *functors*; Mathlib's `IsHomLift.comp` composes two
*morphisms* along a single functor and does not cover this.
-/

@[expose] public section

namespace CategoryTheory

variable {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]

/-- Vertical composition of lifts along two functors: if `φ` lies over `ψ` for `p` and
`ψ` lies over `f` for `q`, then `φ` lies over `f` for `p ⋙ q`. -/
lemma IsHomLift.comp_functor (p : 𝒜 ⥤ ℬ) (q : ℬ ⥤ 𝒞)
    {U V : 𝒞} {a b : ℬ} {x y : 𝒜} (f : U ⟶ V) (ψ : a ⟶ b) (φ : x ⟶ y)
    [p.IsHomLift ψ φ] [q.IsHomLift f ψ] :
    (p ⋙ q).IsHomLift f φ := by
  have hxa : p.obj x = a := IsHomLift.domain_eq p ψ φ
  have hyb : p.obj y = b := IsHomLift.codomain_eq p ψ φ
  have haU : q.obj a = U := IsHomLift.domain_eq q f ψ
  have hbV : q.obj b = V := IsHomLift.codomain_eq q f ψ
  refine IsHomLift.of_fac' (p ⋙ q) f φ (by simp [hxa, haU]) (by simp [hyb, hbV]) ?_
  simp only [Functor.comp_map]
  rw [IsHomLift.fac' p ψ φ, q.map_comp, q.map_comp, eqToHom_map, eqToHom_map,
    IsHomLift.fac' q f ψ]
  simp [Category.assoc]

namespace Functor

/-- **Stacks 09WW.** The composition of two functors that are fibred in groupoids is
fibred in groupoids. -/
@[stacks 09WW]
theorem IsFiberedInGroupoids.comp (p : 𝒜 ⥤ ℬ) (q : ℬ ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) :
    (p ⋙ q).IsFiberedInGroupoids := by
  refine ⟨fun f x hx ↦ ?_, fun φ ψ f hf ↦ ?_⟩
  · -- Lift `f` along `q` to some `ψ`, then lift `ψ` along `p` to get `φ`.
    obtain ⟨b, ψ, _⟩ := hq.exists_lift f (p.obj x) hx
    obtain ⟨y, φ, _⟩ := hp.exists_lift ψ x rfl
    exact ⟨y, φ, IsHomLift.comp_functor p q f ψ φ⟩
  · -- Factor `f` through `p.map φ` using `q`-uniqueness, then lift along `p`.
    obtain ⟨g, ⟨hg1, hg2⟩, hguniq⟩ := hq.unique_lift (p.map φ) (p.map ψ) f hf
    obtain ⟨χ, ⟨hχ1, hχ2⟩, hχuniq⟩ := hp.unique_lift φ ψ g hg2
    refine ⟨χ, ⟨by simpa [hχ1] using hg1, hχ2⟩, fun χ' hχ' ↦ ?_⟩
    refine hχuniq χ' ⟨hguniq (p.map χ') ⟨hχ'.1, ?_⟩, hχ'.2⟩
    simpa [Functor.map_comp] using congrArg p.map hχ'.2

end Functor

end CategoryTheory
