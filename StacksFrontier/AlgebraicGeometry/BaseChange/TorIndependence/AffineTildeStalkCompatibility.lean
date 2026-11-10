module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkGerm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkRings
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TildeStalkGerm
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.MilnorPatching.Relative
import all StacksFrontier.RingTheory.MilnorPatching.ModuleProperties

/-!
# Stacks 01HV, 01I9 and 0098 agree at a module

Let `c : A ⟶ A'` be a homomorphism of commutative rings, `y` a point of `Spec A'` and
`x = Spec(c)(y)` its image. For an `A`-module `M` the stalk at `y` of `(Spec c)^*(M̃)` can be
computed in two ways.

* Along `Spec A'`: the affine pullback isomorphism of Stacks 01I9 identifies `(Spec c)^*(M̃)`
  with `(A' ⊗_A M)~`, and the stalk formula of Stacks 01HV at `A'` identifies the stalk of that
  with `𝒪_{Spec A',y} ⊗_{A'} (A' ⊗_A M)`.
* Along `Spec A`: the stalk formula for a pullback of Stacks 0098 identifies the stalk with
  `𝒪_{Spec A',y} ⊗_{𝒪_{Spec A,x}} (M̃)_x`, and Stacks 01HV at `A` identifies the inner factor
  with `𝒪_{Spec A,x} ⊗_A M`.

**They agree**, under the composition isomorphism for extension of scalars along the two
factorizations `A ⟶ 𝒪_{Spec A,x} ⟶ 𝒪_{Spec A',y}` and `A ⟶ A' ⟶ 𝒪_{Spec A',y}` of one and the
same ring homomorphism — the two factorizations being equal is
`AlgebraicGeometry.specGermRingHom_stalkMap`.

This is, for `Spec` of a ring map against sheafification, the analogue of what
`Stacks.ModuleSkyscraper.pullbackStalkIso_comp_app` is for a composite of morphisms. It is the
underived content of the affine case of the coherence
between the derived stalk formula of Stacks 0098 and the affine comparison square of Stacks 08DW.

## The route

Both sides are morphisms out of `𝒪_{Spec A',y} ⊗_{𝒪_{Spec A,x}} (𝒪_{Spec A,x} ⊗_A M)`, which is
the value at `M` of a composite of two left adjoints. A morphism out of a left adjoint is
determined by its composite with the unit, so it suffices to evaluate both sides at
`1 ⊗ (1 ⊗ m)`; no generation argument about tensor products is needed, and nothing has to be said
about the stalk of a pullback on arbitrary elements.

The evaluation of the first side is a four-step chase through
`AlgebraicGeometry.tildeModulesStalkIso_inv_app_one_tmul`,
`Stacks.ModuleSkyscraper.pullbackStalkIso_hom_app_one_tmul_germ`,
`AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen` and
`AlgebraicGeometry.tildeModulesStalkIso_hom_app_germ_toOpen`. Those four computations fit
together exactly: the germ of the global section attached to `m` is carried to the germ of the
section that the unit of `(Spec c)^* ⊣ (Spec c)_*` attaches to it, and that is the section 01I9
is normalised against. The second side is `ModuleCat.extendScalarsComp` twice and the transport
along the equality of ring homomorphisms.

## Main results

* `ModuleCat.extendScalars2_comp4_eq_comp3`: the chase, with every object and morphism a variable.
  Its two `hom_ext` inputs are not new: `MilnorPatching.extendScalars_twice_hom_ext` is the
  determination of a morphism out of an iterated extension of scalars by its values on
  `1 ⊗ (1 ⊗ m)`, and `ModuleCat.ExtendScalars.map_tmul` the computation of one factor.
* `AlgebraicGeometry.tildeModulesStalkIso_inv_app_one_tmul`: Stacks 01HV read backwards on
  `1 ⊗ m`.
* `AlgebraicGeometry.affineTildeStalkCompatibility`: **the compatibility.**

## Implementation notes

Both chases are run inside `ModuleCat.extendScalars2_comp4_eq_comp3`, where every object and
every morphism is a variable and the seven step values arrive as hypotheses. Assembling the chase
outside it and matching the result against the goal does not work: the objects here are stalks of
sheafifications, every one of them a colimit, and the single `isDefEq` that compares the assembled
composite with the one in the goal exhausts the elaborator's recursion depth — not because any
step is hard, but because the terms are deep. Split one factor per hypothesis, each comparison is
shallow.

For the same reason every tensor that has to be *written* is written inside a helper whose rings
and modules are variables, and the step lemma for the first factor,
`ModuleCat.extendScalars_map_one_tmul_one_tmul_of_eq`, takes both ring homomorphisms rather than
one: its conclusion then spells the element exactly as `ModuleCat.extendScalars2_comp4_eq_comp3`
asks for it, rather than definitionally. Written in place, against an expected type that still
mentions the identity functor of an adjunction's unit, the `Module` instance for the tensor
product is not even found.

None of Stacks 01HV, 01I9 and 0098 asserts this coherence: it is a statement about how the three
fit together, not a clause of any of them.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u uR uS uT w

namespace ModuleCat

/-- **Extension of scalars applied to a morphism, on a doubly unital tensor, with the inner value
named.** The three rings and both ring homomorphisms are binders, in the order
`MilnorPatching.extendScalars_twice_hom_ext` has them, so that the element this produces is the
one that lemma asks for — spelled identically, not merely definitionally.

*Why not `ModuleCat.ExtendScalars.map_tmul`.* That lemma states the same computation with only
the first two rings as binders, the third arriving through the instance the module carries. Read
that way the element this produces is the right one only up to definitional unfolding, and
`MilnorPatching.extendScalars_twice_hom_ext` — which is what
`ModuleCat.extendScalars2_comp4_eq_comp3` applies — demands the element
`(1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)` syntactically. At the concrete instance below, where
every object is a stalk of a sheafification, the comparison the one-binder form leaves to the
elaborator exhausts `maxRecDepth`, so the two-binder form is load-bearing, not stylistic. -/
public theorem extendScalars_map_one_tmul_one_tmul_of_eq {R S T : Type u} [CommRing R]
    [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) {M : ModuleCat.{u} R}
    {P : ModuleCat.{u} S} (w : (ModuleCat.extendScalars.{u, u, u} f).obj M ⟶ P)
    (m : M) (a : P) (h : w.hom ((1 : S) ⊗ₜ[R,f] m) = a) :
    ((ModuleCat.extendScalars.{u, u, u} g).map w).hom
        ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)) = (1 : T) ⊗ₜ[S, g] a := by
  rw [← h]; rfl

/-- **A four-factor composite out of an iterated extension of scalars equals a three-factor one,
step by step.** The two composites agree as soon as the seven displayed computations hold: each
names the value of one factor on the value of the previous one, starting from `1 ⊗ (1 ⊗ m)` on
both sides and ending at a common value `w m`.

Every object and every morphism is a variable, and that is the point. The concrete instance — the
compatibility of Stacks 01HV with Stacks 01I9 and Stacks 0098 — has objects that are stalks of
sheafifications, and matching a chase assembled against those objects with the composite in the
goal exhausts the elaborator's recursion depth even though no step is individually hard. Here each
`isDefEq` the caller triggers compares one factor against one lemma.

The three rings live in independent universes and the modules at
`max w uR uS uT`, which is the generality of `MilnorPatching.extendScalars_twice_hom_ext`, the
only input of the proof. -/
public theorem extendScalars2_comp4_eq_comp3 {R : Type uR} {S : Type uS} {T : Type uT}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    {M : ModuleCat.{max w uR uS uT} R}
    {N₁ N₂ N₃ P₁ P₂ N : ModuleCat.{max w uR uS uT} T}
    (f₁ : (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M) ⟶ N₁)
    (f₂ : N₁ ⟶ N₂) (f₃ : N₂ ⟶ N₃) (f₄ : N₃ ⟶ N)
    (g₁ : (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M) ⟶ P₁)
    (g₂ : P₁ ⟶ P₂) (g₃ : P₂ ⟶ N)
    (a₁ : M → N₁) (a₂ : M → N₂) (a₃ : M → N₃) (b₁ : M → P₁) (b₂ : M → P₂) (w : M → N)
    (h₁ : ∀ m : M, f₁.hom ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)) = a₁ m)
    (h₂ : ∀ m : M, f₂.hom (a₁ m) = a₂ m) (h₃ : ∀ m : M, f₃.hom (a₂ m) = a₃ m)
    (h₄ : ∀ m : M, f₄.hom (a₃ m) = w m)
    (k₁ : ∀ m : M, g₁.hom ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)) = b₁ m)
    (k₂ : ∀ m : M, g₂.hom (b₁ m) = b₂ m) (k₃ : ∀ m : M, g₃.hom (b₂ m) = w m) :
    f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂ ≫ g₃ := by
  refine MilnorPatching.extendScalars_twice_hom_ext.{uR, uS, uT, w} f g M _ _ fun m => ?_
  have e₁ : (f₁ ≫ f₂ ≫ f₃ ≫ f₄).hom ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)) =
      f₄.hom (f₃.hom (f₂.hom (f₁.hom ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m))))) := rfl
  have e₂ : (g₁ ≫ g₂ ≫ g₃).hom ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)) =
      g₃.hom (g₂.hom (g₁.hom ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)))) := rfl
  rw [e₁, e₂, h₁ m, h₂ m, h₃ m, h₄ m, k₁ m, k₂ m, k₃ m]

end ModuleCat

namespace AlgebraicGeometry

open Stacks.ModuleSkyscraper

variable (A : CommRingCat.{u}) (y : (Spec A).carrier) (M : ModuleCat.{u} A)

/-- **Stacks 01HV read backwards on a unital tensor.** The inverse of
`AlgebraicGeometry.tildeModulesStalkIso` carries `1 ⊗ m` to the germ at `y` of the global section
of `M̃` attached to `m`. -/
public theorem tildeModulesStalkIso_inv_app_one_tmul (m : M) :
    ((tildeModulesStalkIso A y).inv.app M).hom
        ((1 : ToType ((Spec A).presheaf.stalk y)) ⊗ₜ[A, specGermRingHom A y] m) =
      (TopCat.Presheaf.germ ((tilde.functor A).obj M).val.presheaf ⊤ y trivial).hom
        ((tilde.toOpen M ⊤).hom m) :=
  Eq.trans
    (congrArg (((tildeModulesStalkIso A y).inv.app M).hom)
      (tildeModulesStalkIso_hom_app_germ_toOpen A y M m).symm)
    (congr($((tildeModulesStalkIso A y).hom_inv_id_app M).hom
      ((TopCat.Presheaf.germ ((tilde.functor A).obj M).val.presheaf ⊤ y trivial).hom
        ((tilde.toOpen M ⊤).hom m))))

/-- **Stacks 01HV, 01I9 and 0098 agree at a module.** For a ring homomorphism `c : A ⟶ A'`, a
point `y` of `Spec A'` with image `x` in `Spec A` and an `A`-module `M`, the identification

`𝒪_{Spec A',y} ⊗_{𝒪_{Spec A,x}} (𝒪_{Spec A,x} ⊗_A M) ≅ 𝒪_{Spec A',y} ⊗_{A'} (A' ⊗_A M)`

obtained by going up through the stalk of `(Spec c)^*(M̃)` — Stacks 01HV at `A` backwards, then
the stalk formula of Stacks 0098, then the affine pullback isomorphism of Stacks 01I9 on stalks,
then Stacks 01HV at `A'` — is the one obtained by merging the two extensions of scalars on each
side and transporting along `AlgebraicGeometry.specGermRingHom_stalkMap`.

Both sides are morphisms out of the value of a composite of two extension-of-scalars functors, so
they are determined by their value on `1 ⊗ (1 ⊗ m)`; `ModuleCat.extendScalars2_comp4_eq_comp3`
chases each side there, one factor at a time. -/
public theorem affineTildeStalkCompatibility {A A' : CommRingCat.{u}} (c : A ⟶ A')
    (y : (Spec A').carrier) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).map
          ((tildeModulesStalkIso A ((Spec.map c).base y)).inv.app M) ≫
        (pullbackStalkIso (Spec.map c) y).hom.app ((tilde.functor A).obj M) ≫
        (modulesStalkFunctor (Spec A') y).map ((pullbackTildeIso A A' c).hom.app M) ≫
        (tildeModulesStalkIso A' y).hom.app ((ModuleCat.extendScalars.{u, u, u} c.hom).obj M) =
      (ModuleCat.extendScalarsComp.{u, u} (specGermRingHom A ((Spec.map c).base y))
            ((Spec.map c).stalkMap y).hom).inv.app M ≫
        (ModuleCat.extendScalarsFunctorCongr.{u} (specGermRingHom_stalkMap c y)).hom.app M ≫
        (ModuleCat.extendScalarsComp.{u, u} c.hom (specGermRingHom A' y)).hom.app M :=
  ModuleCat.extendScalars2_comp4_eq_comp3 (specGermRingHom A ((Spec.map c).base y))
    ((Spec.map c).stalkMap y).hom _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun m => ModuleCat.extendScalars_map_one_tmul_one_tmul_of_eq
      (specGermRingHom A ((Spec.map c).base y)) ((Spec.map c).stalkMap y).hom
      ((tildeModulesStalkIso A ((Spec.map c).base y)).inv.app M) m _
      (tildeModulesStalkIso_inv_app_one_tmul A ((Spec.map c).base y) M m))
    (fun m => pullbackStalkIso_hom_app_one_tmul_germ (Spec.map c) y ((tilde.functor A).obj M) ⊤
      trivial ((tilde.toOpen M ⊤).hom m))
    (fun m => Eq.trans
      (Stacks.Algebraization.modulesStalkFunctor_map_germ ((pullbackTildeIso A A' c).hom.app M) y
        ((Spec.map c) ⁻¹ᵁ ⊤) trivial
        ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map c)).unit.app
          ((tilde.functor A).obj M)).val.app (op ⊤)).hom ((tilde.toOpen M ⊤).hom m)))
      (congrArg
        (fun t => (((tilde.functor A').obj
            ((ModuleCat.extendScalars.{u, u, u} c.hom).obj M)).presheaf.germ ⊤ y trivial).hom t)
        (pullbackTildeIso_hom_app_unit_toOpen A A' c M m)))
    (fun m => tildeModulesStalkIso_hom_app_germ_toOpen A' y
      ((ModuleCat.extendScalars.{u, u, u} c.hom).obj M) ((1 : A') ⊗ₜ[A, c.hom] m))
    (fun m => by
      have h := MilnorPatching.comp_inv_tmul (specGermRingHom A ((Spec.map c).base y))
        ((Spec.map c).stalkMap y).hom M 1 1 m
      simp only [map_one, one_mul] at h
      exact h)
    (fun m => ModuleCat.extendScalarsFunctorCongr_hom_app_one_tmul
      (specGermRingHom_stalkMap c y) M m)
    (fun m => ModuleCat.extendScalarsComp_hom_app_one_tmul c.hom (specGermRingHom A' y) M m)

end AlgebraicGeometry

end
