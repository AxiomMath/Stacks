module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineComparisonCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineModuleBridge
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Galois

/-!
# The cocycle condition for the one-element family `Spec B ⟶ Spec R`, over the tensor powers

For a `ModuleCat.DescentData` for `R → B`, the transition morphism of the descent datum
`Stacks.Descent.specSingletonDescentData'` of `Stacks.Descent.qcohPseudofunctor` satisfies the
cocycle condition `Stacks.Descent.SpecSingletonCocycle` over the threefold wide pullback
`Spec (B ⊗[R] (B ⊗[R] B))` (`Stacks.Descent.specSingletonCocycle`), so the descent datum
`Stacks.Descent.specSingletonDescentData` needs no hypothesis.  The identity is first proved in
terms of `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`
(`Stacks.Descent.pullbackComp_specTransition_cocycle`), and is then read in terms of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`.

## Main definitions

* `Stacks.Descent.tildeTransition`: a morphism between the two extensions of scalars of an
  `R`-module along two ring maps `R ⟶ S`, read as a morphism between the two pullbacks of the
  associated quasi-coherent module on `Spec R`.
* `Stacks.Descent.specSingletonDescentData` and
  `Stacks.Descent.specSingletonDescentDataOfModule`: **the descent datum of
  `Stacks.Descent.qcohPseudofunctor` for the one-element family `Spec B ⟶ Spec R` attached to a
  module descent datum**, over the chosen tensor pullbacks and in the unindexed form
  respectively.

## Main results

* `Stacks.Descent.pullHom_eq_pullbackComp`: `pullHom` for
  `AlgebraicGeometry.modulePullbackPseudofunctor` written with
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`, and `Stacks.Descent.galoisMapComp'_hom_app`,
  the forward direction of `Stacks.Descent.galoisMapComp'_inv_app`.
* `Stacks.Descent.extendScalarsCompTildeIso_app_comp_pullbackComp` and
  `Stacks.Descent.extendScalarsCompTildeIso_inv_app_comp_pullbackComp`:
  `Stacks.Descent.extendScalarsCompTildeIso_app_comp_of_eq` with the geometric factor written
  with `AlgebraicGeometry.Scheme.Modules.pullbackComp`, in both directions.
* `Stacks.Descent.pullbackComp_tildeTransition`: the base change of
  `Stacks.Descent.tildeTransition` along a further ring map is `Stacks.Descent.tildeTransition`
  of the base change of the algebraic morphism, cancelled by `ModuleCat.cancelExtendScalars` at
  both ends.
* `Stacks.Descent.specTransitionIsoOfDescentData_hom_hom`: the geometric transition morphism of
  a module descent datum, after forgetting quasi-coherence, is `Stacks.Descent.tildeTransition`
  of the algebraic one.
* `Stacks.Descent.pullbackComp_specTransition_cocycle`: **the cocycle identity**, as an identity
  of morphisms of sheaves of modules on `Spec (B ⊗[R] (B ⊗[R] B))`.  Its three terms are the
  three base changes of the geometric transition morphism along `Stacks.Descent.tensorMap₀₁`,
  `Stacks.Descent.tensorMap₁₂` and `Stacks.Descent.tensorMap₀₂`.
* `Stacks.Descent.pullHom_specTransitionIsoOfDescentData`: one base change of the geometric
  transition morphism, read as a
  `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`.
* `Stacks.Descent.pullHom_comp_qcoh` and `Stacks.Descent.pullHom'_comp_of_pullHom_comp`: a
  cocycle identity for `pullHom` at `Stacks.Descent.qcohPseudofunctor` from the identity of the
  underlying morphisms, and the cocycle condition of `CategoryTheory.Pseudofunctor.DescentData'`
  from the identity for `pullHom` at the three projections.
* `Stacks.Descent.specSingletonCocycle`: `Stacks.Descent.SpecSingletonCocycle` holds.
* `Stacks.Descent.tildeTransition_injective` and `Stacks.Descent.tildeTransition_comp_iff`: a
  cocycle identity between geometric transition morphisms is equivalent to the algebraic
  identity it comes from.

## Implementation notes

Every lemma here that crosses between `AlgebraicGeometry.modulePullbackPseudofunctor` and
`AlgebraicGeometry.Scheme.Modules` keeps the schemes and the morphisms of schemes as variables.
With a *concrete* `AlgebraicGeometry.Spec.map` in a `CategoryTheory.Pseudofunctor.mapComp'`
position the kernel has to unfold `AlgebraicGeometry.modulePullbackPseudofunctor`, which is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor.comp CategoryTheory.Bicategory.Adj.forget₁`, and
it does not terminate: `Stacks.Descent.galoisMapComp'_inv_app` instantiated at `r := Spec.map χ`
times out in the kernel, while the same instantiation at a variable `r : Spec U ⟶ Spec R` is
free.

Two further kernel facts are responsible for the shape of this file.

First, `AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso` of an
equality of *functors*, so `(Scheme.Modules.pullbackCongr h).inv.app Ω` is a stuck
`Eq.rec` in a data position.  The kernel cannot compare two such terms whose objects `Ω` are
definitionally but not syntactically equal, even when the objects compare in isolation for free:
`(pullbackCongr h).inv.app (tildeQcoh B N).obj = (pullbackCongr h).inv.app
((tilde.functor (CommRingCat.of B)).obj N)` times out in the kernel by `rfl`, while
`(tildeQcoh B N).obj = (tilde.functor (CommRingCat.of B)).obj N` is free by `rfl`
(`Stacks.Descent.tildeQcoh_obj`).  Consequently **every statement in the second half of this
file spells that object the same way**, as `(tilde.functor (CommRingCat.of B)).obj D.module`,
and the two `Stacks.Descent.pullbackCongr_hom_app_comp`-style lemmas take the target proof as a
parameter rather than forming `Eq.trans` of the two given ones, for the same reason.

Second, and for the same reason, `CategoryTheory.Iso.app` must not be applied to
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`: `Stacks.Descent.inv_comp4_of_comp4` therefore
takes its last factor as a pair of mutually inverse morphisms together with one of the two
triangle identities, rather than as a `CategoryTheory.Iso`.

### Where the two spellings of the object are allowed to meet

The pseudofunctor spells the quasi-coherent module on `Spec B` as
`(Stacks.Descent.tildeQcoh B D.module).obj`, and the affine comparison spells it as
`(AlgebraicGeometry.tilde.functor (CommRingCat.of B)).obj D.module`.  As above, the two cannot be
identified under `AlgebraicGeometry.Scheme.Modules.pullbackCongr`.  They can be identified, for
free, in an *argument* of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`: there the comparison is made
argument by argument and reduces to `Stacks.Descent.tildeQcoh_obj`.  That is why
`Stacks.Descent.pullHom_specTransitionIsoOfDescentData` pins every implicit argument of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` — `F`, the two schemes, the two
objects and the two morphisms — at the spelling the affine comparison uses, and is proved as a
*term*: `AlgebraicGeometry.Spec` unfolds to a structure instance if the schemes are left to be
inferred from the objects, and `rw` refuses the goal at `implicit` transparency because
`(Spec R).Modules` and `↑(modulePullbackPseudofunctor.obj _)` are not interchangeable there.

For the same reason `Stacks.Descent.specSingletonCocycle` never states the threefold composite:
it hands `Stacks.Descent.pullHom_comp_qcoh` three instances of
`Stacks.Descent.pullHom_specTransitionIsoOfDescentData` against a goal left to be solved from
`Stacks.Descent.SpecSingletonCocycle`; writing the composite out as a statement of its own and
closing it by `exact` is far more expensive.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite
  TensorProduct
open Pseudofunctor.LocallyDiscreteOpToCat

universe t v' v u' u

namespace Stacks.Descent

/-! ### Formal rearrangements -/

section Formal

variable {C : Type*} [Category C]

/-- Two composites of three factors agree as soon as the factors do. -/
theorem comp3_congr {X Y Z W : C} {a a' : X ⟶ Y} {u u' : Y ⟶ Z} {b b' : Z ⟶ W} (ha : a = a')
    (hu : u = u') (hb : b = b') : a ≫ u ≫ b = a' ≫ u' ≫ b' := by rw [ha, hu, hb]

/-- A composition identity transported along identifications of its three terms. -/
theorem comp_eq_of_eq_of_eq_of_eq {X Y Z : C} {u u' : X ⟶ Y} {v v' : Y ⟶ Z} {w w' : X ⟶ Z}
    (hu : u = u') (hv : v = v') (hw : w = w') (h : u' ≫ v' = w') : u ≫ v = w := by
  rwa [hu, hv, hw]

/-- **An identity between composites of isomorphisms, read backwards.**  The last factor is
supplied as a pair of morphisms `dh`, `di` with `dh ≫ di = 𝟙`. -/
theorem inv_comp4_of_comp4 {X₀ X₁ X₂ X₃ X₄ Y : C} (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    {dh : X₃ ⟶ X₄} {di : X₄ ⟶ X₃} (hd : dh ≫ di = 𝟙 X₃) (e : X₀ ≅ Y) (g : Y ≅ X₄)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ dh = e.hom ≫ g.hom) :
    di ≫ c.inv ≫ b.inv ≫ a.inv = g.inv ≫ e.inv := by
  have hd' : ∀ {Z : C} (x : X₃ ⟶ Z), dh ≫ di ≫ x = x := fun x => by
    rw [← Category.assoc, hd, Category.id_comp]
  refine (Iso.cancel_iso_hom_left (e ≪≫ g) _ _).1 ?_
  conv_lhs => rw [show (e ≪≫ g).hom = a.hom ≫ b.hom ≫ c.hom ≫ dh from h.symm]
  simp [hd']

/-- Cancelling an isomorphism off the end of a four-fold composite. -/
theorem comp3_eq_of_comp4_eq {X₀ X₁ X₂ X₃ X₄ Z : C} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃}
    (e : X₄ ≅ X₃) {d : X₀ ⟶ Z} {g : Z ⟶ X₄} (h : a ≫ b ≫ c ≫ e.inv = d ≫ g) :
    a ≫ b ≫ c = d ≫ g ≫ e.hom := by
  simpa using h =≫ e.hom

end Formal

/-! ### `pullHom` in the vocabulary of `AlgebraicGeometry.Scheme.Modules.pullbackComp` -/

section PullHomExpansion

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` spelled out. -/
theorem pullHom_eq_mapComp'_comp {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} {X₁ X₂ : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by simp [← hgf₁])).hom.toNatTrans.app M₁ ≫
        (F.map g.op.toLoc).toFunctor.map φ ≫
        (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (by simp [← hgf₂])).inv.toNatTrans.app M₂ :=
  rfl

/-- The forward direction of the composition comparison of
`AlgebraicGeometry.modulePullbackPseudofunctor`, as in `Stacks.Descent.galoisMapComp'_inv_app`. -/
theorem galoisMapComp'_hom_app {X₁ X₂ X₃ : Scheme.{u}} (p : X₂ ⟶ X₃) (q : X₁ ⟶ X₂)
    (r : X₁ ⟶ X₃) (h : q ≫ p = r)
    (M : modulePullbackPseudofunctor.{u}.obj (.mk (op X₃))) :
    (modulePullbackPseudofunctor.mapComp' p.op.toLoc q.op.toLoc r.op.toLoc
        (by simp [← h])).hom.toNatTrans.app M =
      ((Scheme.Modules.pullbackCongr h).inv ≫ (Scheme.Modules.pullbackComp q p).inv).app M := by
  subst h; rfl

/-- **`pullHom` for `AlgebraicGeometry.modulePullbackPseudofunctor`, written with
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.** -/
theorem pullHom_eq_pullbackComp {X Y Z : Scheme.{u}} {f₁ f₂ : Y ⟶ X} {g : Z ⟶ Y}
    {gf₁ gf₂ : Z ⟶ X} {M : modulePullbackPseudofunctor.{u}.obj (.mk (op X))}
    (φ : (modulePullbackPseudofunctor.map f₁.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map f₂.op.toLoc).toFunctor.obj M)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      (Scheme.Modules.pullbackCongr hgf₁).inv.app M ≫
        (Scheme.Modules.pullbackComp g f₁).inv.app M ≫
        (Scheme.Modules.pullback g).map φ ≫
        (Scheme.Modules.pullbackComp g f₂).hom.app M ≫
        (Scheme.Modules.pullbackCongr hgf₂).hom.app M := by
  rw [pullHom_eq_mapComp'_comp, galoisMapComp'_hom_app f₁ g gf₁ hgf₁,
    galoisMapComp'_inv_app f₂ g gf₂ hgf₂]
  rfl

end PullHomExpansion

/-! ### The affine comparison over a composite, in the `pullbackComp` vocabulary -/

section Coherence

variable {R S U : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ U)

/-- Composing the comparisons of pullbacks along `f = g` and along `g = h` gives the comparison
along `f = h`. -/
theorem pullbackCongr_hom_app_comp {X Y : Scheme.{u}} {f g h : X ⟶ Y} (p : f = g) (q : g = h)
    (r : f = h) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app M ≫ (Scheme.Modules.pullbackCongr q).hom.app M =
      (Scheme.Modules.pullbackCongr r).hom.app M := by
  subst q p
  simp [Scheme.Modules.pullbackCongr]

/-- `Stacks.Descent.extendScalarsCompTildeIso_app_comp_of_eq` with the geometric factor written
as `AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by a single transport. -/
theorem extendScalarsCompTildeIso_app_comp_pullbackComp {χ : R ⟶ U} (hχ : φ ≫ ψ = χ)
    (hh : ψ.hom.comp φ.hom = χ.hom) (hc : Spec.map ψ ≫ Spec.map φ = Spec.map χ)
    (M : ModuleCat.{u} R) :
    (extendScalarsCompTildeIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map ((extendScalarsCompTildeIso φ).hom.app M) ≫
        (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).hom.app
          ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullbackCongr hc).hom.app ((tilde.functor R).obj M) =
      (tilde.functor U).map (ModuleCat.cancelExtendScalars φ.hom ψ.hom hh M).hom ≫
        (extendScalarsCompTildeIso χ).hom.app M := by
  refine Eq.trans ?_ (extendScalarsCompTildeIso_app_comp_of_eq φ ψ hχ hh M)
  rw [specPullbackComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    pullbackCongr_hom_app_comp _ _ hc]

/-- `Stacks.Descent.extendScalarsCompTildeIso_app_comp_pullbackComp` read backwards, with every
factor inverted. -/
theorem extendScalarsCompTildeIso_inv_app_comp_pullbackComp {χ : R ⟶ U} (hχ : φ ≫ ψ = χ)
    (hh : ψ.hom.comp φ.hom = χ.hom) (hc : Spec.map ψ ≫ Spec.map φ = Spec.map χ)
    (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullbackCongr hc).inv.app ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app
          ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map ((extendScalarsCompTildeIso φ).inv.app M) ≫
        (extendScalarsCompTildeIso ψ).inv.app ((ModuleCat.extendScalars φ.hom).obj M) =
      (extendScalarsCompTildeIso χ).inv.app M ≫
        (tilde.functor U).map (ModuleCat.cancelExtendScalars φ.hom ψ.hom hh M).inv :=
  inv_comp4_of_comp4
    ((extendScalarsCompTildeIso ψ).app ((ModuleCat.extendScalars φ.hom).obj M))
    ((Scheme.Modules.pullback (Spec.map ψ)).mapIso ((extendScalarsCompTildeIso φ).app M))
    ((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app ((tilde.functor R).obj M))
    (Iso.hom_inv_id_app (Scheme.Modules.pullbackCongr hc) ((tilde.functor R).obj M))
    ((tilde.functor U).mapIso (ModuleCat.cancelExtendScalars φ.hom ψ.hom hh M))
    ((extendScalarsCompTildeIso χ).app M)
    (extendScalarsCompTildeIso_app_comp_pullbackComp φ ψ hχ hh hc M)

end Coherence

/-! ### The geometric reading of a morphism of extensions of scalars -/

section TildeTransition

/-- **A morphism between two extensions of scalars of a module, read as a morphism between the
two pullbacks of the associated quasi-coherent module.**  This is the geometric transition
morphism attached to an algebraic one, through
`Stacks.Descent.extendScalarsCompTildeIso` at the two ring maps. -/
def tildeTransition {R S : CommRingCat.{u}} (φ₁ φ₂ : R ⟶ S) (N : ModuleCat.{u} R)
    (α : (ModuleCat.extendScalars φ₁.hom).obj N ⟶ (ModuleCat.extendScalars φ₂.hom).obj N) :
    (Scheme.Modules.pullback (Spec.map φ₁)).obj ((tilde.functor R).obj N) ⟶
      (Scheme.Modules.pullback (Spec.map φ₂)).obj ((tilde.functor R).obj N) :=
  (extendScalarsCompTildeIso φ₁).inv.app N ≫ (tilde.functor S).map α ≫
    (extendScalarsCompTildeIso φ₂).hom.app N

/-- `Stacks.Descent.tildeTransition` is multiplicative. -/
theorem tildeTransition_comp {R S : CommRingCat.{u}} (φ₁ φ₂ φ₃ : R ⟶ S) (N : ModuleCat.{u} R)
    (α : (ModuleCat.extendScalars φ₁.hom).obj N ⟶ (ModuleCat.extendScalars φ₂.hom).obj N)
    (β : (ModuleCat.extendScalars φ₂.hom).obj N ⟶ (ModuleCat.extendScalars φ₃.hom).obj N) :
    tildeTransition φ₁ φ₂ N α ≫ tildeTransition φ₂ φ₃ N β = tildeTransition φ₁ φ₃ N (α ≫ β) := by
  simp only [tildeTransition, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- `Stacks.Descent.tildeTransition` as a conjugate, with the two comparison isomorphisms
written as `CategoryTheory.Iso.app`. -/
theorem tildeTransition_eq_comp {R S : CommRingCat.{u}} (φ₁ φ₂ : R ⟶ S) (N : ModuleCat.{u} R)
    (α : (ModuleCat.extendScalars φ₁.hom).obj N ⟶ (ModuleCat.extendScalars φ₂.hom).obj N) :
    tildeTransition φ₁ φ₂ N α =
      ((extendScalarsCompTildeIso φ₁).app N).inv ≫ (tilde.functor S).map α ≫
        ((extendScalarsCompTildeIso φ₂).app N).hom :=
  rfl

/-- **`Stacks.Descent.tildeTransition` is injective.** -/
theorem tildeTransition_injective {R S : CommRingCat.{u}} (φ₁ φ₂ : R ⟶ S) (N : ModuleCat.{u} R) :
    Function.Injective (tildeTransition φ₁ φ₂ N) := by
  intro α β h
  rw [tildeTransition_eq_comp, tildeTransition_eq_comp] at h
  exact (tilde.functor S).map_injective
    ((Iso.cancel_iso_hom_right _ _ _).1 ((Iso.cancel_iso_inv_left _ _ _).1 h))

/-- **A cocycle identity between geometric transition morphisms says exactly as much as the
algebraic identity it comes from.** -/
theorem tildeTransition_comp_iff {R S : CommRingCat.{u}} (φ₁ φ₂ φ₃ : R ⟶ S) (N : ModuleCat.{u} R)
    (α : (ModuleCat.extendScalars φ₁.hom).obj N ⟶ (ModuleCat.extendScalars φ₂.hom).obj N)
    (β : (ModuleCat.extendScalars φ₂.hom).obj N ⟶ (ModuleCat.extendScalars φ₃.hom).obj N)
    (γ : (ModuleCat.extendScalars φ₁.hom).obj N ⟶ (ModuleCat.extendScalars φ₃.hom).obj N) :
    tildeTransition φ₁ φ₂ N α ≫ tildeTransition φ₂ φ₃ N β = tildeTransition φ₁ φ₃ N γ ↔
      α ≫ β = γ :=
  ⟨fun h ↦ tildeTransition_injective φ₁ φ₃ N ((tildeTransition_comp φ₁ φ₂ φ₃ N α β).symm.trans h),
    fun h ↦ (tildeTransition_comp φ₁ φ₂ φ₃ N α β).trans
      (congrArg (tildeTransition φ₁ φ₃ N) h)⟩

/-- **The base change of a geometric transition morphism along a further ring map.**  Pulling
`Stacks.Descent.tildeTransition` back along `Spec ψ` and reading the result over the two
composites `φᵢ ≫ ψ` gives `Stacks.Descent.tildeTransition` of the base change of the algebraic
morphism, cancelled by `ModuleCat.cancelExtendScalars` at both ends. -/
theorem pullbackComp_tildeTransition {R S T : CommRingCat.{u}} (φ₁ φ₂ : R ⟶ S) (ψ : S ⟶ T)
    {χ₁ χ₂ : R ⟶ T} (hχ₁ : φ₁ ≫ ψ = χ₁) (hχ₂ : φ₂ ≫ ψ = χ₂)
    (hh₁ : ψ.hom.comp φ₁.hom = χ₁.hom) (hh₂ : ψ.hom.comp φ₂.hom = χ₂.hom)
    (hc₁ : Spec.map ψ ≫ Spec.map φ₁ = Spec.map χ₁)
    (hc₂ : Spec.map ψ ≫ Spec.map φ₂ = Spec.map χ₂) (N : ModuleCat.{u} R)
    (α : (ModuleCat.extendScalars φ₁.hom).obj N ⟶ (ModuleCat.extendScalars φ₂.hom).obj N) :
    (Scheme.Modules.pullbackCongr hc₁).inv.app ((tilde.functor R).obj N) ≫
        (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ₁)).inv.app
          ((tilde.functor R).obj N) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map (tildeTransition φ₁ φ₂ N α) ≫
        (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ₂)).hom.app
          ((tilde.functor R).obj N) ≫
        (Scheme.Modules.pullbackCongr hc₂).hom.app ((tilde.functor R).obj N) =
      tildeTransition χ₁ χ₂ N
        ((ModuleCat.cancelExtendScalars φ₁.hom ψ.hom hh₁ N).inv ≫
          (ModuleCat.extendScalars ψ.hom).map α ≫
          (ModuleCat.cancelExtendScalars φ₂.hom ψ.hom hh₂ N).hom) := by
  have hnat : (extendScalarsCompTildeIso ψ).hom.app ((ModuleCat.extendScalars φ₁.hom).obj N) ≫
      (Scheme.Modules.pullback (Spec.map ψ)).map ((tilde.functor S).map α) =
      (tilde.functor T).map ((ModuleCat.extendScalars ψ.hom).map α) ≫
        (extendScalarsCompTildeIso ψ).hom.app ((ModuleCat.extendScalars φ₂.hom).obj N) :=
    ((extendScalarsCompTildeIso ψ).hom.naturality α).symm
  have K₁ := comp3_eq_of_comp4_eq
    ((extendScalarsCompTildeIso ψ).app ((ModuleCat.extendScalars φ₁.hom).obj N))
    (extendScalarsCompTildeIso_inv_app_comp_pullbackComp φ₁ ψ hχ₁ hh₁ hc₁ N)
  have K₂ := extendScalarsCompTildeIso_app_comp_pullbackComp φ₂ ψ hχ₂ hh₂ hc₂ N
  simp only [tildeTransition, Functor.map_comp, Category.assoc]
  rw [reassoc_of% K₁]
  simp only [Iso.app_hom]
  rw [reassoc_of% hnat, K₂]

end TildeTransition

/-! ### Forgetting quasi-coherence -/

section QcohReduction

/-- The components of a composite of morphisms of quasi-coherent modules. -/
theorem qcoh_comp_hom {b : LocallyDiscrete Scheme.{u}ᵒᵖ}
    {M N P : quasicoherentProperty.{u}.Obj b} (u : M ⟶ N) (v : N ⟶ P) :
    (u ≫ v).hom = u.hom ≫ v.hom :=
  rfl

/-- **The cocycle identity for `pullHom` at `Stacks.Descent.qcohPseudofunctor` follows from the
identity between the underlying morphisms of sheaves of modules.** -/
theorem pullHom_comp_qcoh {X Y Z : Scheme.{u}} {f₁ f₂ : Y ⟶ X} {g₀₁ g₁₂ g₀₂ : Z ⟶ Y}
    {c₀ c₁ c₂ : Z ⟶ X} {M : quasicoherentProperty.{u}.Obj (.mk (op X))}
    (φ : (qcohPseudofunctor.map f₁.op.toLoc).toFunctor.obj M ⟶
      (qcohPseudofunctor.map f₂.op.toLoc).toFunctor.obj M)
    (h₀ : g₀₁ ≫ f₁ = c₀) (h₁ : g₀₁ ≫ f₂ = c₁) (h₂ : g₁₂ ≫ f₁ = c₁) (h₃ : g₁₂ ≫ f₂ = c₂)
    (h₄ : g₀₂ ≫ f₁ = c₀) (h₅ : g₀₂ ≫ f₂ = c₂)
    (hcomp : pullHom φ.hom g₀₁ c₀ c₁ h₀ h₁ ≫ pullHom φ.hom g₁₂ c₁ c₂ h₂ h₃ =
      pullHom φ.hom g₀₂ c₀ c₂ h₄ h₅) :
    pullHom φ g₀₁ c₀ c₁ h₀ h₁ ≫ pullHom φ g₁₂ c₁ c₂ h₂ h₃ = pullHom φ g₀₂ c₀ c₂ h₄ h₅ :=
  ObjectProperty.hom_ext _
    ((qcoh_comp_hom _ _).trans
      (comp_eq_of_eq_of_eq_of_eq (hom_pullHom M M φ g₀₁ c₀ c₁ h₀ h₁)
        (hom_pullHom M M φ g₁₂ c₁ c₂ h₂ h₃) (hom_pullHom M M φ g₀₂ c₀ c₂ h₄ h₅) hcomp))

end QcohReduction

/-! ### The cocycle condition from the identity at the three projections -/

section PullHomPrime

open Pseudofunctor.DescentData'

/-- **The cocycle condition of `CategoryTheory.Pseudofunctor.DescentData'` from the
corresponding identity for `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` at the
three projections of the threefold wide pullback.** -/
theorem pullHom'_comp_of_pullHom_comp {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} {ι : Type t} {S : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S} {sq : ∀ i j, ChosenPullback (f i) (f j)}
    (sq₃ : ∀ i₁ i₂ i₃ : ι, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    {obj : ∀ i, F.obj (.mk (op (X i)))}
    (hom : ∀ i j : ι, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) (i₁ i₂ i₃ : ι)
    (h : pullHom (hom i₁ i₂) (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom (hom i₂ i₃) (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  rwa [pullHom'₁₂_eq_pullHom_of_chosenPullback₃ sq₃,
    pullHom'₂₃_eq_pullHom_of_chosenPullback₃ sq₃, pullHom'₁₃_eq_pullHom_of_chosenPullback₃ sq₃]

end PullHomPrime

/-! ### The transition morphism of a module descent datum, read over the tensor powers -/

section SpecTransition

/-- Two equal morphisms of quasi-coherent modules have equal underlying morphisms of sheaves of
modules. -/
theorem qcoh_hom_congr {b : LocallyDiscrete Scheme.{u}ᵒᵖ}
    {M N : quasicoherentProperty.{u}.Obj b} {u v : M ⟶ N} (h : u = v) : u.hom = v.hom :=
  congrArg _ h

/-- The underlying morphism of sheaves of modules of a component of
`Stacks.Descent.extendScalarsCompTildeEquivIso` is the corresponding component of
`Stacks.Descent.extendScalarsCompTildeIso`. -/
theorem extendScalarsCompTildeEquivIso_app_hom_hom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (N : ModuleCat.{u} R) :
    ((extendScalarsCompTildeEquivIso φ).app N).hom.hom =
      (extendScalarsCompTildeIso φ).hom.app N :=
  (ObjectProperty.ι _).map_preimage _

/-- The inverse form of `Stacks.Descent.extendScalarsCompTildeEquivIso_app_hom_hom`. -/
theorem extendScalarsCompTildeEquivIso_app_inv_hom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (N : ModuleCat.{u} R) :
    ((extendScalarsCompTildeEquivIso φ).app N).inv.hom =
      (extendScalarsCompTildeIso φ).inv.app N :=
  (ObjectProperty.ι _).map_preimage _

/-- `AlgebraicGeometry.tildeEquiv` is `AlgebraicGeometry.tilde.functor` after forgetting
quasi-coherence. -/
theorem tildeEquiv_functor_map_hom {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((tildeEquiv (R := R)).functor.map f).hom = (tilde.functor R).map f :=
  rfl

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The sheaf of modules underlying `Stacks.Descent.tildeQcoh`. -/
theorem tildeQcoh_obj (N : ModuleCat.{u} B) :
    (tildeQcoh B N).obj = (tilde.functor (CommRingCat.of B)).obj N :=
  rfl

/-- `Stacks.Descent.specTransitionIsoOfDescentData`, unfolded in the category of
quasi-coherent modules. -/
theorem specTransitionIsoOfDescentData_hom_eq (D : ModuleCat.DescentData.{u, u, u} R B) :
    (specTransitionIsoOfDescentData R B D).hom =
      ((extendScalarsCompTildeEquivIso (tensorInl R B)).app D.module).inv ≫
        (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).functor.map
          (extendScalarsTransitionOfDescentData R B D).hom ≫
        ((extendScalarsCompTildeEquivIso (tensorInr R B)).app D.module).hom :=
  rfl

/-- **The geometric transition morphism of a module descent datum, after forgetting
quasi-coherence, is `Stacks.Descent.tildeTransition` of the algebraic one.** -/
theorem specTransitionIsoOfDescentData_hom_hom (D : ModuleCat.DescentData.{u, u, u} R B) :
    ((specTransitionIsoOfDescentData R B D).hom).hom =
      tildeTransition (tensorInl R B) (tensorInr R B) D.module
        (extendScalarsTransitionOfDescentData R B D).hom :=
  (qcoh_hom_congr (specTransitionIsoOfDescentData_hom_eq R B D)).trans
    (comp3_congr (extendScalarsCompTildeEquivIso_app_inv_hom _ _)
      (tildeEquiv_functor_map_hom _) (extendScalarsCompTildeEquivIso_app_hom_hom _ _))

/-- **The base change of the geometric transition morphism of a module descent datum along a
ring map out of `B ⊗[R] B`** is `Stacks.Descent.tildeTransition` of
`Stacks.Descent.extendScalarsTripleTransition`. -/
theorem pullbackComp_specTransitionIsoOfDescentData (D : ModuleCat.DescentData.{u, u, u} R B)
    {T : CommRingCat.{u}} (ψ : CommRingCat.of (B ⊗[R] B) ⟶ T) {χ₁ χ₂ : CommRingCat.of B ⟶ T}
    (hχ₁ : tensorInl R B ≫ ψ = χ₁) (hχ₂ : tensorInr R B ≫ ψ = χ₂)
    (hh₁ : ψ.hom.comp (tensorInl R B).hom = χ₁.hom)
    (hh₂ : ψ.hom.comp (tensorInr R B).hom = χ₂.hom)
    (hc₁ : Spec.map ψ ≫ Spec.map (tensorInl R B) = Spec.map χ₁)
    (hc₂ : Spec.map ψ ≫ Spec.map (tensorInr R B) = Spec.map χ₂) :
    (Scheme.Modules.pullbackCongr hc₁).inv.app ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
        (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map (tensorInl R B))).inv.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map
          ((specTransitionIsoOfDescentData R B D).hom).hom ≫
        (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map (tensorInr R B))).hom.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
        (Scheme.Modules.pullbackCongr hc₂).hom.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) =
      tildeTransition χ₁ χ₂ D.module (extendScalarsTripleTransition R B D ψ.hom hh₁ hh₂) := by
  rw [specTransitionIsoOfDescentData_hom_hom]
  exact pullbackComp_tildeTransition (tensorInl R B) (tensorInr R B) ψ hχ₁ hχ₂ hh₁ hh₂ hc₁ hc₂
    D.module (extendScalarsTransitionOfDescentData R B D).hom

/-- **`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` of the geometric transition
morphism of a module descent datum, along a ring map out of `B ⊗[R] B`, is
`Stacks.Descent.tildeTransition` of `Stacks.Descent.extendScalarsTripleTransition`.** -/
theorem pullHom_specTransitionIsoOfDescentData (D : ModuleCat.DescentData.{u, u, u} R B)
    {T : CommRingCat.{u}} (ψ : CommRingCat.of (B ⊗[R] B) ⟶ T) {χ₁ χ₂ : CommRingCat.of B ⟶ T}
    (hχ₁ : tensorInl R B ≫ ψ = χ₁) (hχ₂ : tensorInr R B ≫ ψ = χ₂)
    (hh₁ : ψ.hom.comp (tensorInl R B).hom = χ₁.hom)
    (hh₂ : ψ.hom.comp (tensorInr R B).hom = χ₂.hom)
    (hc₁ : Spec.map ψ ≫ Spec.map (tensorInl R B) = Spec.map χ₁)
    (hc₂ : Spec.map ψ ≫ Spec.map (tensorInr R B) = Spec.map χ₂) :
    pullHom (F := modulePullbackPseudofunctor.{u})
        (X₁ := Spec (CommRingCat.of B)) (X₂ := Spec (CommRingCat.of B))
        (M₁ := (tilde.functor (CommRingCat.of B)).obj D.module)
        (M₂ := (tilde.functor (CommRingCat.of B)).obj D.module)
        (f₁ := Spec.map (tensorInl R B)) (f₂ := Spec.map (tensorInr R B))
        ((specTransitionIsoOfDescentData R B D).hom).hom
        (Spec.map ψ) (Spec.map χ₁) (Spec.map χ₂) hc₁ hc₂ =
      tildeTransition χ₁ χ₂ D.module (extendScalarsTripleTransition R B D ψ.hom hh₁ hh₂) :=
  (pullHom_eq_pullbackComp (X := Spec (CommRingCat.of B))
      (M := (tilde.functor (CommRingCat.of B)).obj D.module)
      ((specTransitionIsoOfDescentData R B D).hom).hom hc₁ hc₂).trans
    (pullbackComp_specTransitionIsoOfDescentData R B D ψ hχ₁ hχ₂ hh₁ hh₂ hc₁ hc₂)

end SpecTransition

/-! ### The cocycle condition -/

section Cocycle

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- On spectra, `Stacks.Descent.tensorInl` followed by `Stacks.Descent.tensorMap₀₁` is
`Stacks.Descent.tensorIncl₀`. -/
theorem specMap_tensorMap₀₁_comp_tensorInl :
    Spec.map (tensorMap₀₁ R B) ≫ Spec.map (tensorInl R B) = Spec.map (tensorIncl₀ R B) := by
  rw [← Spec.map_comp, tensorInl_comp_tensorMap₀₁]

/-- On spectra, `Stacks.Descent.tensorInr` followed by `Stacks.Descent.tensorMap₀₁` is
`Stacks.Descent.tensorIncl₁`. -/
theorem specMap_tensorMap₀₁_comp_tensorInr :
    Spec.map (tensorMap₀₁ R B) ≫ Spec.map (tensorInr R B) = Spec.map (tensorIncl₁ R B) := by
  rw [← Spec.map_comp, tensorInr_comp_tensorMap₀₁]

/-- On spectra, `Stacks.Descent.tensorInl` followed by `Stacks.Descent.tensorMap₁₂` is
`Stacks.Descent.tensorIncl₁`. -/
theorem specMap_tensorMap₁₂_comp_tensorInl :
    Spec.map (tensorMap₁₂ R B) ≫ Spec.map (tensorInl R B) = Spec.map (tensorIncl₁ R B) := by
  rw [← Spec.map_comp, tensorInl_comp_tensorMap₁₂]

/-- On spectra, `Stacks.Descent.tensorInr` followed by `Stacks.Descent.tensorMap₁₂` is
`Stacks.Descent.tensorIncl₂`. -/
theorem specMap_tensorMap₁₂_comp_tensorInr :
    Spec.map (tensorMap₁₂ R B) ≫ Spec.map (tensorInr R B) = Spec.map (tensorIncl₂ R B) := by
  rw [← Spec.map_comp, tensorInr_comp_tensorMap₁₂]

/-- On spectra, `Stacks.Descent.tensorInl` followed by `Stacks.Descent.tensorMap₀₂` is
`Stacks.Descent.tensorIncl₀`. -/
theorem specMap_tensorMap₀₂_comp_tensorInl :
    Spec.map (tensorMap₀₂ R B) ≫ Spec.map (tensorInl R B) = Spec.map (tensorIncl₀ R B) := by
  rw [← Spec.map_comp, tensorInl_comp_tensorMap₀₂]

/-- On spectra, `Stacks.Descent.tensorInr` followed by `Stacks.Descent.tensorMap₀₂` is
`Stacks.Descent.tensorIncl₂`. -/
theorem specMap_tensorMap₀₂_comp_tensorInr :
    Spec.map (tensorMap₀₂ R B) ≫ Spec.map (tensorInr R B) = Spec.map (tensorIncl₂ R B) := by
  rw [← Spec.map_comp, tensorInr_comp_tensorMap₀₂]

/-- **The three base changes of the geometric transition morphism of a module descent datum along
the three projections of `Stacks.Descent.specTensorChosenPullback₃` satisfy the cocycle
identity.**  This is `Stacks.Descent.SpecSingletonCocycle` written with
`AlgebraicGeometry.Scheme.Modules.pullbackComp` in place of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`. -/
theorem pullbackComp_specTransition_cocycle (D : ModuleCat.DescentData.{u, u, u} R B) :
    ((Scheme.Modules.pullbackCongr (specMap_tensorMap₀₁_comp_tensorInl R B)).inv.app
            ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
          (Scheme.Modules.pullbackComp (Spec.map (tensorMap₀₁ R B))
              (Spec.map (tensorInl R B))).inv.app
            ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
          (Scheme.Modules.pullback (Spec.map (tensorMap₀₁ R B))).map
            ((specTransitionIsoOfDescentData R B D).hom).hom ≫
          (Scheme.Modules.pullbackComp (Spec.map (tensorMap₀₁ R B))
              (Spec.map (tensorInr R B))).hom.app
            ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
          (Scheme.Modules.pullbackCongr (specMap_tensorMap₀₁_comp_tensorInr R B)).hom.app
            ((tilde.functor (CommRingCat.of B)).obj D.module)) ≫
        ((Scheme.Modules.pullbackCongr (specMap_tensorMap₁₂_comp_tensorInl R B)).inv.app
            ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
          (Scheme.Modules.pullbackComp (Spec.map (tensorMap₁₂ R B))
              (Spec.map (tensorInl R B))).inv.app
            ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
          (Scheme.Modules.pullback (Spec.map (tensorMap₁₂ R B))).map
            ((specTransitionIsoOfDescentData R B D).hom).hom ≫
          (Scheme.Modules.pullbackComp (Spec.map (tensorMap₁₂ R B))
              (Spec.map (tensorInr R B))).hom.app
            ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
          (Scheme.Modules.pullbackCongr (specMap_tensorMap₁₂_comp_tensorInr R B)).hom.app
            ((tilde.functor (CommRingCat.of B)).obj D.module)) =
      (Scheme.Modules.pullbackCongr (specMap_tensorMap₀₂_comp_tensorInl R B)).inv.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
        (Scheme.Modules.pullbackComp (Spec.map (tensorMap₀₂ R B))
            (Spec.map (tensorInl R B))).inv.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
        (Scheme.Modules.pullback (Spec.map (tensorMap₀₂ R B))).map
          ((specTransitionIsoOfDescentData R B D).hom).hom ≫
        (Scheme.Modules.pullbackComp (Spec.map (tensorMap₀₂ R B))
            (Spec.map (tensorInr R B))).hom.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) ≫
        (Scheme.Modules.pullbackCongr (specMap_tensorMap₀₂_comp_tensorInr R B)).hom.app
          ((tilde.functor (CommRingCat.of B)).obj D.module) :=
  comp_eq_of_eq_of_eq_of_eq
    (pullbackComp_specTransitionIsoOfDescentData R B D (tensorMap₀₁ R B)
      (tensorInl_comp_tensorMap₀₁ R B) (tensorInr_comp_tensorMap₀₁ R B)
      (tensorMap₀₁_comp_tensorInl R B) (tensorMap₀₁_comp_tensorInr R B)
      (specMap_tensorMap₀₁_comp_tensorInl R B) (specMap_tensorMap₀₁_comp_tensorInr R B))
    (pullbackComp_specTransitionIsoOfDescentData R B D (tensorMap₁₂ R B)
      (tensorInl_comp_tensorMap₁₂ R B) (tensorInr_comp_tensorMap₁₂ R B)
      (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B)
      (specMap_tensorMap₁₂_comp_tensorInl R B) (specMap_tensorMap₁₂_comp_tensorInr R B))
    (pullbackComp_specTransitionIsoOfDescentData R B D (tensorMap₀₂ R B)
      (tensorInl_comp_tensorMap₀₂ R B) (tensorInr_comp_tensorMap₀₂ R B)
      (tensorMap₀₂_comp_tensorInl R B) (tensorMap₀₂_comp_tensorInr R B)
      (specMap_tensorMap₀₂_comp_tensorInl R B) (specMap_tensorMap₀₂_comp_tensorInr R B))
    ((tildeTransition_comp_iff _ _ _ _ _ _ _).2 (extendScalarsTripleTransition_comp R B D))

/-- **The cocycle condition `Stacks.Descent.SpecSingletonCocycle` holds for the transition
morphism that a module descent datum supplies.** -/
theorem specSingletonCocycle (D : ModuleCat.DescentData.{u, u, u} R B) :
    SpecSingletonCocycle R B D := by
  intro i₁ i₂ i₃
  refine pullHom'_comp_of_pullHom_comp (specSingletonSq₃ R B)
    (specSingletonHomOfDescentData R B D) i₁ i₂ i₃ ?_
  refine pullHom_comp_qcoh _ _ _ _ _ _ _ ?_
  exact comp_eq_of_eq_of_eq_of_eq
    (pullHom_specTransitionIsoOfDescentData R B D (tensorMap₀₁ R B)
      (tensorInl_comp_tensorMap₀₁ R B) (tensorInr_comp_tensorMap₀₁ R B)
      (tensorMap₀₁_comp_tensorInl R B) (tensorMap₀₁_comp_tensorInr R B)
      (specMap_tensorMap₀₁_comp_tensorInl R B) (specMap_tensorMap₀₁_comp_tensorInr R B))
    (pullHom_specTransitionIsoOfDescentData R B D (tensorMap₁₂ R B)
      (tensorInl_comp_tensorMap₁₂ R B) (tensorInr_comp_tensorMap₁₂ R B)
      (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B)
      (specMap_tensorMap₁₂_comp_tensorInl R B) (specMap_tensorMap₁₂_comp_tensorInr R B))
    (pullHom_specTransitionIsoOfDescentData R B D (tensorMap₀₂ R B)
      (tensorInl_comp_tensorMap₀₂ R B) (tensorInr_comp_tensorMap₀₂ R B)
      (tensorMap₀₂_comp_tensorInl R B) (tensorMap₀₂_comp_tensorInr R B)
      (specMap_tensorMap₀₂_comp_tensorInl R B) (specMap_tensorMap₀₂_comp_tensorInr R B))
    ((tildeTransition_comp_iff _ _ _ _ _ _ _).2 (extendScalarsTripleTransition_comp R B D))

/-- **The descent datum of `Stacks.Descent.qcohPseudofunctor` for the one-element family
`Spec B ⟶ Spec R` attached to a module descent datum.**  Its object is `(D.module)^~`, and its
transition morphism is the image of `ModuleCat.DescentData.transition` under
`Stacks.Descent.extendScalarsTransitionEquiv`. -/
def specSingletonDescentData (D : ModuleCat.DescentData.{u, u, u} R B) :
    qcohPseudofunctor.DescentData' (specSingletonSq R B) (specSingletonSq₃ R B) :=
  specSingletonDescentData' R B D (specSingletonCocycle R B D)

/-- **A module descent datum for `R → B` gives a descent datum of
`Stacks.Descent.qcohPseudofunctor` for the one-element family `Spec B ⟶ Spec R`**, in the
unindexed form `CategoryTheory.Pseudofunctor.DescentData`: the image of
`Stacks.Descent.specSingletonDescentData` under
`Stacks.Descent.specTensorDescentDataEquivalence`. -/
def specSingletonDescentDataOfModule (D : ModuleCat.DescentData.{u, u, u} R B) :
    qcohPseudofunctor.DescentData (specSingleton R B) :=
  (specTensorDescentDataEquivalence R B).functor.obj (specSingletonDescentData R B D)

end Cocycle

end Stacks.Descent

end

end
