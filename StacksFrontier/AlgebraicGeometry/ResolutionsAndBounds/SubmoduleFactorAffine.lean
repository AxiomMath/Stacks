module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.Injectivity

/-!
# Factoring a morphism through a subsheaf by an affine-local check

Let `X` be a scheme, `f : P ⟶ M` a morphism of `𝒪_X`-modules and `Q` a subsheaf of `M`. To
factor `f` through `Q` one has to know that every value of `f`, over every open of `X`, lies in
`Q`. This file reduces that to the affine opens: if the values of `f` over the affine opens lie
in `Q`, then `f` factors through `Q`.

## Main definitions

* `AlgebraicGeometry.factorThruOfLocalMem`: the factorization of `f` through `Q` obtained from
  the hypothesis that every value of `f` lies in `Q` near each point.
* `AlgebraicGeometry.factorThruOfForallAffineOpens`: the factorization of `f` through `Q`
  obtained from the affine-local hypothesis.

## Main results

* `AlgebraicGeometry.factorThruOfLocalMem_ι` and
  `AlgebraicGeometry.factorThruOfForallAffineOpens_ι`: the factorization composed with the
  inclusion of `Q` is `f`.
* `AlgebraicGeometry.val_factorThruOfForallAffineOpens_app`: the factorization does not change
  the value of a section.

## Implementation notes

Both hypotheses are weaker than the one `SheafOfModules.Submodule.factorThru` asks for because
membership in a subsheaf is a local condition: for `factorThruOfLocalMem` this is the sheaf
axiom of `Q` applied to the covering sieve of neighbourhoods supplied by the hypothesis, and for
`factorThruOfForallAffineOpens` it is
`Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens`, which uses that the affine opens
form a basis. In both cases the restriction of a value of `f` is the value of `f` on the
restricted section, which is `Stacks.AlgebraicGeometry.IdealPowerColimit.app_naturality`.

This is the form in which a submodule cut out by an infimum over affine opens can be factored
through: for such a submodule the containment of the image is the hard direction of the lattice,
and the only description available is of the sections over an affine open. The local form is the
one to use when the neighbourhoods on which the values can be recognised are constrained — for
instance when they have to be small enough for a sheafified tensor product to be presented by a
sum of pure tensors.

## References

* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Factoring through a subsheaf, checked locally.** A morphism of `𝒪_X`-modules factors
through a subsheaf `Q` of its target as soon as every value of the morphism lies in `Q` after
restriction to some neighbourhood of each point of the open it lives on. -/
noncomputable def factorThruOfLocalMem {P M : X.Modules} (Q : M.Submodule) (f : P ⟶ M)
    (hf : ∀ (W : X.Opens) (x : Γ(P, W)) (p : X), p ∈ W →
      ∃ (V : X.Opens) (hV : V ≤ W), p ∈ V ∧
        f.app V (P.presheaf.map (homOfLE hV).op x) ∈ Q.toSubmodule.obj (op V)) :
    P ⟶ subMod Q :=
  Q.factorThru f (by
    intro W x
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = W := ⟨W.unop, rfl⟩
    refine Q.isSheaf (X := op W) (f.app W x) fun p hp ↦ ?_
    obtain ⟨V, hVW, hpV, hmem⟩ := hf W x p hp
    have hres : M.presheaf.map (homOfLE hVW).op (f.app W x) ∈ Q.toSubmodule.obj (op V) := by
      rw [app_naturality f hVW x]
      exact hmem
    exact ⟨V, homOfLE hVW, hres, hpV⟩)

/-- The factorization obtained from the local hypothesis, composed with the inclusion of `Q`
into the ambient sheaf, is the original morphism. -/
@[reassoc (attr := simp)]
theorem factorThruOfLocalMem_ι {P M : X.Modules} (Q : M.Submodule) (f : P ⟶ M)
    (hf : ∀ (W : X.Opens) (x : Γ(P, W)) (p : X), p ∈ W →
      ∃ (V : X.Opens) (hV : V ≤ W), p ∈ V ∧
        f.app V (P.presheaf.map (homOfLE hV).op x) ∈ Q.toSubmodule.obj (op V)) :
    factorThruOfLocalMem Q f hf ≫ Q.ι = f :=
  Q.factorThru_ι f _

/-- **Factoring through a subsheaf, checked on the affine opens.** A morphism of `𝒪_X`-modules
whose values over the affine opens of `X` lie in a subsheaf `Q` of its target factors through
`Q`. -/
noncomputable def factorThruOfForallAffineOpens {P M : X.Modules} (Q : M.Submodule)
    (f : P ⟶ M)
    (hf : ∀ (V : X.affineOpens) (x : Γ(P, V.1)),
      f.app V.1 x ∈ Q.toSubmodule.obj (op V.1)) :
    P ⟶ subMod Q :=
  Q.factorThru f (by
    intro W x
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = W := ⟨W.unop, rfl⟩
    exact mem_of_forall_affineOpens Q (f.app W x) fun V hV ↦
      (app_naturality f hV x).symm ▸ hf V _)

/-- The factorization through `Q` composed with the inclusion of `Q` into the ambient sheaf is
the original morphism. -/
@[reassoc (attr := simp)]
theorem factorThruOfForallAffineOpens_ι {P M : X.Modules} (Q : M.Submodule) (f : P ⟶ M)
    (hf : ∀ (V : X.affineOpens) (x : Γ(P, V.1)),
      f.app V.1 x ∈ Q.toSubmodule.obj (op V.1)) :
    factorThruOfForallAffineOpens Q f hf ≫ Q.ι = f :=
  Q.factorThru_ι f _

/-- The factorization through `Q` does not change the value of a section. -/
theorem val_factorThruOfForallAffineOpens_app {P M : X.Modules} (Q : M.Submodule) (f : P ⟶ M)
    (hf : ∀ (V : X.affineOpens) (x : Γ(P, V.1)),
      f.app V.1 x ∈ Q.toSubmodule.obj (op V.1))
    (W : X.Opens) (x : Γ(P, W)) :
    (((factorThruOfForallAffineOpens Q f hf).app W x).1 : Γ(M, W)) = f.app W x := rfl

end AlgebraicGeometry

end
