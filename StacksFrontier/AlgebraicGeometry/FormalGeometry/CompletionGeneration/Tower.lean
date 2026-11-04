module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction

/-!
# Generating a coherent adic system by lifting a single level through the transition maps

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf on `X`, `G` a coherent
`𝒪_X`-module and `(F_n)` a coherent adic system along `ℐ`. This file proves that a *single*
epimorphism `G ⟶ F_0` already exhibits `(F_n)` as a quotient of the completion `G^∧`, provided the
transition maps are surjective on morphisms out of `G`:

  if `Hom(G, F_{n+1}) ⟶ Hom(G, F_n)` is surjective for every `n`, and some `G ⟶ F_0` is an
  epimorphism, then there is an epimorphism `G^∧ ⟶ (F_n)` in `Coh(X, ℐ)`.

This is the last paragraph of the proof of Stacks 0885 with its two geometric inputs removed. In
the source `G` is a finite direct sum `(L ^⊗ (-d))^{⊕ t}` of negative twists of an `f`-ample
invertible sheaf, the epimorphism `G ⟶ F_0` comes from Serre's global generation of
`F_0 ⊗ L ^⊗ d`, and the surjectivity of the transition maps on `Hom(G, -)` comes from the uniform
vanishing of `H¹(X, Ker(F_{n+1} ⟶ F_n) ⊗ L ^⊗ d)` of Stacks 0884 through the long exact
cohomology sequence. None of that is used here: the content of this file is the *bookkeeping*,
which is pure category theory over `ℕᵒᵖ` together with the adjunction of Stacks 0880.

The route is the adjunction `Hom(G^∧, (F_n)) ≃ Hom(G, lim F_n)` of
`Stacks.Algebraization.completionHomLimitEquiv`. Surjectivity of the transition maps lets one lift
a given `s : G ⟶ F_0` step by step to a compatible family `ψ_n : G ⟶ F_n` with `ψ_0 = s`; such a
family is a cone, hence a morphism `G ⟶ lim F_n`, hence a morphism of systems `G^∧ ⟶ (F_n)` whose
level-`0` component composed with the projection `G ⟶ (G^∧)_0` is `s`. Since that projection is an
epimorphism and `s` is one, the level-`0` component is an epimorphism, and Stacks 087Y upgrades
that to an epimorphism of systems.

## Main definitions

* `Stacks.Algebraization.coneOfSucc` — a cone on a functor out of `ℕᵒᵖ` built from
  successor-level data.
* `Stacks.Algebraization.homToLimitOfSucc` — the morphism into the limit that cone determines.

## Main results

* `Stacks.Algebraization.hom_naturality_le_of_succ` — successor compatibility of a family of
  morphisms into an inverse system over `ℕᵒᵖ` propagates to every pair `m ≤ n`.
* `Stacks.Algebraization.exists_hom_tower_of_surjective` — a morphism into the lowest term of an
  inverse system over `ℕᵒᵖ` whose transition maps are surjective on morphisms out of a fixed
  object lifts to a compatible family of morphisms into every term.
* `Stacks.Algebraization.epi_app_zero_homToAdicSystem` — the level-`0` component of the morphism
  of systems attached to `f : G ⟶ lim F_n` is an epimorphism as soon as `f` followed by the
  lowest limit projection is one.
* `Stacks.Algebraization.exists_epi_completionFunctor_of_epi_comp_limit_π` — the epimorphism of
  systems attached to such an `f`.
* `Stacks.Algebraization.exists_epi_completionFunctor_of_surjective_transitionHom` — **the main
  result**: an epimorphism `G ⟶ F_0` and surjectivity of the transition maps on `Hom(G, -)` make
  `(F_n)` a quotient of `G^∧`.

## Implementation notes

The naturality of the cone is reduced to the successor case exactly as
`Stacks.Algebraization.completionProjection_naturality_le` does it: `Nat.le_induction` on the
upper index, and `Subsingleton.elim` to recognise an arbitrary arrow of `ℕᵒᵖ` as the opposite of
the `homOfLE` of its underlying inequality — the hom-types of a preorder category are
subsingletons.

The lifting step is a `Nat.rec` over the chosen sections of the surjections, so the family it
produces is literally `s` at level `0` and its compatibility is the defining equation of the
choice at each successor. Nothing finer is needed: the source's "lift a generating family through
the surjections" is this recursion applied to each member of the family at once, which here is
the single morphism out of the direct sum.

The abstract statements are given for an arbitrary functor `ℕᵒᵖ ⥤ C` into an arbitrary category,
since no property of modules enters them.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe v₁ u₁ u

namespace Stacks.Algebraization

/-! ### Compatible families of morphisms into an inverse system over `ℕᵒᵖ` -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] (F : ℕᵒᵖ ⥤ C) (M : C)

/-- A family of morphisms into the terms of an inverse system over `ℕᵒᵖ` which is compatible with
the transition maps between consecutive levels is compatible with all of them.

The induction is on the upper index, and the identity transition is recognised through
`Subsingleton.elim`, the hom-types of a preorder category being subsingletons. -/
public theorem hom_naturality_le_of_succ (ψ : ∀ n : ℕ, M ⟶ F.obj (op n))
    (hψ : ∀ n : ℕ, ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = ψ n) {m n : ℕ} (h : m ≤ n) :
    ψ n ≫ F.map (homOfLE h).op = ψ m := by
  induction n, h using Nat.le_induction with
  | base =>
    have h0 : F.map (homOfLE (le_refl m)).op = 𝟙 _ :=
      (congrArg F.map (Subsingleton.elim (homOfLE (le_refl m)).op (𝟙 (op m)))).trans
        (F.map_id (op m))
    rw [h0]
    exact Category.comp_id _
  | succ n hn ih =>
    have heq : (homOfLE (Nat.le_succ_of_le hn)).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op := Subsingleton.elim _ _
    rw [heq, Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ F.map (homOfLE hn).op) (hψ n)).trans ih)

/-- **A compatible family of morphisms into an inverse system over `ℕᵒᵖ` is a cone.** The
compatibility is required only between consecutive levels; `hom_naturality_le_of_succ`
propagates it. -/
public def coneOfSucc (ψ : ∀ n : ℕ, M ⟶ F.obj (op n))
    (hψ : ∀ n : ℕ, ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = ψ n) : Cone F where
  pt := M
  π :=
    { app := fun n => ψ n.unop
      naturality := fun i j a => (Category.id_comp _).trans (by
        refine Eq.symm ?_
        simpa only [show (homOfLE (leOfHom a.unop)).op = a from Subsingleton.elim _ _] using
          hom_naturality_le_of_succ F M ψ hψ (leOfHom a.unop)) }

/-- The components of `Stacks.Algebraization.coneOfSucc` are the given morphisms. -/
public theorem coneOfSucc_π_app (ψ : ∀ n : ℕ, M ⟶ F.obj (op n))
    (hψ : ∀ n : ℕ, ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = ψ n) (n : ℕᵒᵖ) :
    (coneOfSucc F M ψ hψ).π.app n = ψ n.unop :=
  rfl

/-- The morphism into the limit determined by a compatible family, with its source pinned to `M`.

`(Stacks.Algebraization.coneOfSucc F M ψ hψ).pt` is `M` by definition, but not syntactically, and
a rewrite along `CategoryTheory.Limits.limit.lift_π` inside an `Epi` would have to build its
motive at the unpinned spelling. -/
public def homToLimitOfSucc [HasLimit F] (ψ : ∀ n : ℕ, M ⟶ F.obj (op n))
    (hψ : ∀ n : ℕ, ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = ψ n) : M ⟶ limit F :=
  limit.lift F (coneOfSucc F M ψ hψ)

/-- The composite of `Stacks.Algebraization.homToLimitOfSucc` with a limit projection is the
corresponding member of the family. -/
public theorem homToLimitOfSucc_π [HasLimit F] (ψ : ∀ n : ℕ, M ⟶ F.obj (op n))
    (hψ : ∀ n : ℕ, ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = ψ n) (n : ℕᵒᵖ) :
    homToLimitOfSucc F M ψ hψ ≫ limit.π F n = ψ n.unop :=
  limit.lift_π (coneOfSucc F M ψ hψ) n

/-- **Lifting a morphism through a tower of surjections.** If every transition map of an inverse
system over `ℕᵒᵖ` is surjective on morphisms out of `M`, then every morphism `M ⟶ F_0` extends to
a family of morphisms `M ⟶ F_n` compatible with the transition maps.

The family is built by recursion on the level out of chosen preimages, so it is the given
morphism at level `0` on the nose. -/
public theorem exists_hom_tower_of_surjective
    (hsurj : ∀ n : ℕ, Function.Surjective
      (fun g : M ⟶ F.obj (op (n + 1)) => g ≫ F.map (homOfLE (Nat.le_succ n)).op))
    (s : M ⟶ F.obj (op 0)) :
    ∃ ψ : ∀ n : ℕ, M ⟶ F.obj (op n),
      ψ 0 = s ∧ ∀ n : ℕ, ψ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = ψ n := by
  choose lift hlift using fun (n : ℕ) (g : M ⟶ F.obj (op n)) => hsurj n g
  exact ⟨fun n => Nat.rec (motive := fun k : ℕ => M ⟶ F.obj (op k)) s (fun k x => lift k x) n,
    rfl, fun n => hlift n _⟩

end Abstract

/-! ### Generation of a coherent adic system -/

section Completion

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (F : Stacks.Coherent.CoherentAdicSystems I)

/-- **The level-`0` component of a morphism out of a completion is an epimorphism as soon as the
corresponding morphism into the limit is.** The projection `G ⟶ (G^∧)_0` composed with the
level-`0` component of `Stacks.Algebraization.homToAdicSystem` is `f` followed by the lowest limit
projection, so if the latter is an epimorphism so is the component. -/
public theorem epi_app_zero_homToAdicSystem (f : coherentObj G ⟶ limit F.obj)
    (hf : Epi (f ≫ limit.π F.obj (op 0))) :
    Epi ((homToAdicSystem G F f).hom.app (op 0)) := by
  have hc : Epi (completionProjection X I G 0 ≫ (homToAdicSystem G F f).hom.app (op 0)) := by
    rw [completionProjection_homToAdicSystem G F f (op 0)]
    exact hf
  exact epi_of_epi (completionProjection X I G 0) _

/-- **A morphism into the limit which is surjective at the lowest level generates the system.**
Given `f : G ⟶ lim F_n` whose composite with the lowest limit projection is an epimorphism, the
morphism of coherent adic systems `G^∧ ⟶ (F_n)` attached to `f` by the adjunction of Stacks 0880
is an epimorphism, by Stacks 087Y. -/
public theorem exists_epi_completionFunctor_of_epi_comp_limit_π (f : coherentObj G ⟶ limit F.obj)
    (hf : Epi (f ≫ limit.π F.obj (op 0))) :
    ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (p : (completionFunctor X I).obj P ⟶ F), Epi p :=
  ⟨G, homToAdicSystem G F f,
    (Stacks.Coherent.epi_iff_epi_app_zero I (homToAdicSystem G F f)).mpr
      (epi_app_zero_homToAdicSystem I G F f hf)⟩

/-- **The last paragraph of the proof of Stacks 0885, with its geometric inputs removed.** Let `G`
be a coherent `𝒪_X`-module and `(F_n)` a coherent adic system along `ℐ`. Suppose

* every transition map `F_{n+1} ⟶ F_n` is surjective on morphisms out of `G`, and
* some morphism `s : G ⟶ F_0` is an epimorphism.

Then `(F_n)` receives an epimorphism from the completion `G^∧`, so it is a quotient of an object
in the image of the completion functor of Stacks 0880.

In the source `G` is `(L ^⊗ (-d))^{⊕ t}` for an `f`-ample invertible `L`, the epimorphism `s` is
Serre's global generation of `F_0 ⊗ L ^⊗ d`, and the surjectivity hypothesis is the long exact
cohomology sequence applied to the vanishing of `H¹(X, Ker(F_{n+1} ⟶ F_n) ⊗ L ^⊗ d)` of Stacks
0884. -/
public theorem exists_epi_completionFunctor_of_surjective_transitionHom
    (hsurj : ∀ n : ℕ, Function.Surjective
      (fun g : coherentObj G ⟶ F.obj.obj (op (n + 1)) =>
        g ≫ F.obj.map (homOfLE (Nat.le_succ n)).op))
    (s : coherentObj G ⟶ F.obj.obj (op 0)) (hs : Epi s) :
    ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (p : (completionFunctor X I).obj P ⟶ F), Epi p := by
  obtain ⟨ψ, hψ0, hψ⟩ := exists_hom_tower_of_surjective F.obj (coherentObj G) hsurj s
  refine exists_epi_completionFunctor_of_epi_comp_limit_π I G F
    (homToLimitOfSucc F.obj (coherentObj G) ψ hψ) ?_
  rw [homToLimitOfSucc_π F.obj (coherentObj G) ψ hψ (op 0), hψ0]
  exact hs

end Completion

end Stacks.Algebraization

end
