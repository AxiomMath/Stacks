module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.PushforwardCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningUnitDescent

/-!
# The unit compatibility, asked for in the thickening picture

`AlgebraicGeometry.exists_unit_of_adicThickeningPushforwardFamily`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicThickeningUnitDescent.lean`)
descends a family of units `u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` on the adic thickenings to a morphism
`𝒪_X ⟶ G` on `X`, but it asks for the compatibility of the family in the form `hu`: the direct
images on `X` must commute with `AlgebraicGeometry.adicThickeningPushforwardTransition`, the
transition of the *first* picture conjugated by the unwinding. A caller has the compatibility in
the thickening picture instead — commuting with
`AlgebraicGeometry.adicThickeningCompletionTransition` — because that is the shape the transitions
`hBtrans` of a cartesian system of algebra sheaves give, through
`AlgebraicGeometry.unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso`. **This file derives
`hu` from that form**, which is what the module docstring of `AdicThickeningUnitDescent.lean`
records as still owed.

## The identification, and the shape that gets it through

The two forms differ by the identification of `adicThickeningPushforwardTransition` with the
direct image along `vₙ` of `adicThickeningCompletionTransition`, which is the unit cocycle
`Stacks.Descent.unit_pullbackPushforwardAdjunction_comp` read at `iₙ ≫ vₙ₊₁ = vₙ`. Two cocycles
are needed, both proved here over **variable** schemes with the composite named by an equation
binder, so that no fibre product is ever reduced:

* `AlgebraicGeometry.unit_comp_pushUnit_comp_map_pullbackCompHom` — the unit cocycle with the two
  comparisons of the factorisation collected into `Stacks.Descent.pushUnit` and
  `Stacks.Descent.pullbackCompHom`.
* `AlgebraicGeometry.structureUnitHom_comp_pushUnit_comp_map_pullbackUnitIso` — the companion for
  the structure morphisms, from
  `Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_comp`.

`AlgebraicGeometry.structureUnitHom_comp_map_comp_of_unit_comp` is where they are applied, and its
shape is the whole point: **the pushed-forward transition `T` and the comparison `Θ` are binders,
named by equations**, and its conclusion mentions neither `pushUnit` nor `pullbackCompHom` nor
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`. A consumer discharges the two binders with
statements already written at the adic morphisms —
`AlgebraicGeometry.unit_comp_adicThickeningPushforwardTransition` and
`AlgebraicGeometry.pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition` — so the
only thing instantiated at `vₙ` is a conclusion in the vocabulary that is already used there.

### Why the binders are not optional: four measurements

Writing the identification out and proving it by instantiating the cocycle directly, which is the
obvious route, does not compile, and the budget is exhausted in a way that is worth recording
because it is *not* the statement and *not* the instantiation:

* the cocycle instantiated at `iₙ`, `vₙ₊₁` and `adicBaseChangeSucc_fst` with **no expected type**
  elaborates, and its inferred type is exactly the wanted statement; and the wanted statement
  **written out** elaborates too (as a `Prop`-valued definition, and so do the three factors of
  its left-hand side separately);
* but the term checked **against** that written statement is a `whnf` timeout at 200,000
  heartbeats, and with every subterm spelled as the cocycle spells it, an `isDefEq` timeout;
* closing the same goal with `apply` instead gets through the elaborator and is then a **kernel**
  deterministic timeout;
* and so is the same statement proved by instantiating a form of the cocycle in which `vₙ` is
  already a binder — the elaborator accepts it, the kernel does not.

What *is* affordable: the raw cocycle
`Stacks.Descent.unit_pullbackPushforwardAdjunction_comp` instantiated at `iₙ` and `vₙ₊₁` with the
composite left as `iₙ ≫ vₙ₊₁`; the collected cocycle at `k := iₙ ≫ vₙ₊₁` with `hk := rfl`; and the
collected cocycle with `k` and `hk` kept as binders. So the step that overruns is exactly the
substitution of the concrete `vₙ` for the composite — the transport along
`AlgebraicGeometry.adicBaseChangeSucc_fst` on the *direct image* side, which cannot be discharged
by `subst` because `vₙ = pullback.fst f (adicThickeningι A I n)` is not a variable. Keeping the
morphisms it compares as binders, as `structureUnitHom_comp_map_comp_of_unit_comp` does, is what
removes that transport from everything the kernel has to check.

## Main results

* `AlgebraicGeometry.structureUnitHom_comp_map_comp_adicThickeningPushforwardTransition` — the
  hypothesis `hu` of `AlgebraicGeometry.adicThickeningUnitSystemHom`, derived from the
  compatibility in the thickening picture.
* `AlgebraicGeometry.exists_unit_of_adicThickeningTransitionFamily` — the descent of the unit with
  that compatibility as its only hypothesis on the family.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Descent (pushUnit pushUnit_app pullbackCompHom
  unit_pullbackPushforwardAdjunction_comp pushforwardCongr_rfl_hom pullbackCongr_rfl_hom)
open Stacks.AlgebraicGeometry.AffineBaseChange (unitObj pullbackUnitIso structureUnitHom
  unit_comp_map_pullbackUnitIso structureUnitHom_comp)

/-! ### The composition law of the direct image at the level of components -/

section Generic

variable {Z Z' Z'' : Scheme.{u}}

/-- The comparison `AlgebraicGeometry.Scheme.Modules.pushforwardComp`, which is the identity on
components by
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id`, cancelled at the end
of a composite. -/
private theorem comp_comp_pushforwardComp_hom_app (c : Z'' ⟶ Z') (h : Z' ⟶ Z) (M : Z''.Modules)
    {W V : Z.Modules} (a : W ⟶ V)
    (b : V ⟶ (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pushforward c).obj M)) :
    a ≫ b ≫ (Scheme.Modules.pushforwardComp c h).hom.app M = a ≫ b :=
  (congrArg (fun z => a ≫ b ≫ z)
      (Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id c h M)).trans
    (congrArg (fun z => a ≫ z) (Category.comp_id b))

/-! ### The two cocycles -/

/-- **The unit cocycle, read on the pushed-forward unit.** For `c ≫ h = k` the unit of
`h^* ⊣ h_*`, followed by the direct image along `h` of the unit of `c^* ⊣ c_*` — which is
`Stacks.Descent.pushUnit` — and by the direct image along `k` of the comparison
`Stacks.Descent.pullbackCompHom`, is the unit of `k^* ⊣ k_*`.

This is `Stacks.Descent.unit_pullbackPushforwardAdjunction_comp` with the two comparisons of the
factorisation `k = c ≫ h` collected into the two named morphisms. The morphism `k` and the
equation naming it are binders, and the proof begins by substituting them: the schemes stay
variables, so no concrete fibre product is ever reduced. -/
public theorem unit_comp_pushUnit_comp_map_pullbackCompHom (h : Z' ⟶ Z) (c : Z'' ⟶ Z')
    {k : Z'' ⟶ Z} (hk : c ≫ h = k) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M ≫
        (pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj M) ≫
          (Scheme.Modules.pushforward k).map (pullbackCompHom c h k hk M) =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M := by
  subst hk
  rw [pushUnit_app, pullbackCompHom, unit_pullbackPushforwardAdjunction_comp]
  simp only [pushforwardCongr_rfl_hom, pullbackCongr_rfl_hom, NatTrans.id_app, Category.comp_id,
    Category.assoc]

/-- **The structure morphism cocycle, read on the pushed-forward unit.** For `c ≫ h = k` the
structure morphism of `h`, followed by `Stacks.Descent.pushUnit` at the structure sheaf and by the
direct image along `k` of the identification `c^* 𝒪_{Z'} ≅ 𝒪_{Z''}`, is the structure morphism of
`k`.

The inputs are `Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso`, which
turns the unit at the structure sheaf into the structure morphism, and
`Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_comp`, the multiplicativity of the
structure morphism. As above, `k` and the equation naming it are binders. -/
public theorem structureUnitHom_comp_pushUnit_comp_map_pullbackUnitIso (h : Z' ⟶ Z) (c : Z'' ⟶ Z')
    {k : Z'' ⟶ Z} (hk : c ≫ h = k) :
    structureUnitHom h ≫ (pushUnit h c k hk).app (unitObj Z') ≫
        (Scheme.Modules.pushforward k).map (pullbackUnitIso c).hom =
      structureUnitHom k := by
  subst hk
  rw [pushUnit_app]
  simp only [pushforwardCongr_rfl_hom, NatTrans.id_app, Category.comp_id, Category.assoc]
  rw [← NatTrans.naturality (Scheme.Modules.pushforwardComp c h).hom (pullbackUnitIso c).hom]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, unit_comp_map_pullbackUnitIso]
  exact (comp_comp_pushforwardComp_hom_app c h (unitObj Z'') _ _).trans
    (structureUnitHom_comp c h).symm

/-! ### Rearranging the composite the derivation below runs through -/

/-- **The shape of the derivation below.** A composite `s₁ ≫ p₁ ≫ t` in which `t` splits as
`q ≫ r`, the second factor commutes with `q` past a naturality square, the tail `m ≫ r`
factors as `w ≫ p₀`, and the resulting head `s₁ ≫ q₀ ≫ w` is `s₀`. Stated and proved in an
abstract category, and applied as a term: the goal it is applied to mixes the two presentations of
the category of sheaves of modules, where associativity rewriting fails for the reason recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicThickeningUnwinding.lean`. -/
private theorem comp_comp_eq_comp_of_split {C : Type*} [Category C]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ : C} {s₁ : O₁ ⟶ O₂} {p₁ : O₂ ⟶ O₃} {t : O₃ ⟶ O₄} {q : O₃ ⟶ O₅}
    {r : O₅ ⟶ O₄} {q₀ : O₂ ⟶ O₆} {m : O₆ ⟶ O₅} {w : O₆ ⟶ O₇} {p₀ : O₇ ⟶ O₄} {s₀ : O₁ ⟶ O₇}
    (ht : t = q ≫ r) (hnat : p₁ ≫ q = q₀ ≫ m) (hmr : m ≫ r = w ≫ p₀)
    (hs : s₁ ≫ q₀ ≫ w = s₀) :
    s₁ ≫ p₁ ≫ t = s₀ ≫ p₀ := by
  subst ht hs
  simp [reassoc_of% hnat, hmr]

/-! ### The square, with every comparison map a binder -/

/-- **The compatibility of a family of units with a pushed-forward transition, from its
compatibility downstairs.** Let `c ≫ h = k` be a factorisation, let `G` be a module on the base,
and suppose given

* a morphism `T : h_*(h^* G) ⟶ k_*(k^* G)` — the pushed-forward transition — characterized by
  carrying the unit of `h^* ⊣ h_*` to the unit of `k^* ⊣ k_*`, the unit at `h` being an
  epimorphism, so that `T` is the only such morphism;
* a morphism `Θ : c^*(h^* G) ⟶ k^* G` named as the comparison `Stacks.Descent.pullbackCompHom`
  of the factorisation;
* units `u₁ : 𝒪_{Z'} ⟶ h^* G` and `u₀ : 𝒪_{Z''} ⟶ k^* G` whose compatibility is the one visible
  *downstairs*: `u₁` pulled back along `c`, read through `c^* 𝒪_{Z'} ≅ 𝒪_{Z''}` and `Θ`, is `u₀`.

Then the two units are compatible on the base, through the structure morphisms and `T`.

**`T` and `Θ` are binders, and so is the composite `k`.** That is what makes this usable at the
adic morphisms, where `k = vₙ` is a projection out of a fibre product and the equation
`iₙ ≫ vₙ₊₁ = vₙ` cannot be substituted: a consumer supplies `T`, `Θ` and the two equations naming
them from statements that are already written at those morphisms, and nothing in the conclusion
mentions `Stacks.Descent.pushUnit`, `pullbackCompHom` or
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`. The two cocycles above, where those do appear,
are applied here — over variable schemes.

The proof is four steps: the characterization of `T` identifies it with
`Stacks.Descent.pushUnit` followed by the direct image of the comparison, by the unit cocycle and
the epimorphism; the naturality of `pushUnit` moves the direct image of `u₁` across it; the
hypothesis downstairs rewrites the tail; and the structure morphism cocycle collapses the
head. -/
public theorem structureUnitHom_comp_map_comp_of_unit_comp (h : Z' ⟶ Z) (c : Z'' ⟶ Z')
    {k : Z'' ⟶ Z} (hk : c ≫ h = k) (G : Z.Modules)
    (hepi : Epi ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app G))
    {T : (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj G) ⟶
      (Scheme.Modules.pushforward k).obj ((Scheme.Modules.pullback k).obj G)}
    (hT : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app G ≫ T =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app G)
    {u₁ : unitObj Z' ⟶ (Scheme.Modules.pullback h).obj G}
    {u₀ : unitObj Z'' ⟶ (Scheme.Modules.pullback k).obj G}
    {Θ : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback h).obj G) ⟶
      (Scheme.Modules.pullback k).obj G}
    (hΘ : Θ = pullbackCompHom c h k hk G)
    (hu : (pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map u₁ ≫ Θ = u₀) :
    structureUnitHom h ≫ (Scheme.Modules.pushforward h).map u₁ ≫ T =
      structureUnitHom k ≫ (Scheme.Modules.pushforward k).map u₀ := by
  have hT' : T = (pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj G) ≫
      (Scheme.Modules.pushforward k).map (pullbackCompHom c h k hk G) :=
    (@cancel_epi _ _ _ _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app G) hepi _ _).mp
      (hT.trans (unit_comp_pushUnit_comp_map_pullbackCompHom h c hk G).symm)
  have key : (Scheme.Modules.pullback c).map u₁ ≫ pullbackCompHom c h k hk G =
      (pullbackUnitIso c).hom ≫ u₀ :=
    (congrArg (fun z => (Scheme.Modules.pullback c).map u₁ ≫ z) hΘ).symm.trans
      ((Iso.inv_comp_eq (pullbackUnitIso c)).mp hu)
  refine comp_comp_eq_comp_of_split hT' ((pushUnit h c k hk).naturality u₁) ?_
    (structureUnitHom_comp_pushUnit_comp_map_pullbackUnitIso h c hk)
  exact (((Scheme.Modules.pushforward k).map_comp _ _).symm.trans
    (congrArg (Scheme.Modules.pushforward k).map key)).trans
      ((Scheme.Modules.pushforward k).map_comp _ _)

end Generic

/-! ### The pushed-forward transition is the direct image of the thickening transition -/

section Adic

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsLocallyNoetherian X] [LocallyOfFiniteType f]

omit [IsLocallyNoetherian X] [LocallyOfFiniteType f] in
/-- The comparison `Stacks.Descent.pullbackCompHom` at `iₙ ≫ vₙ₊₁ = vₙ` is the canonical
transition of a completion. This is
`AlgebraicGeometry.pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition`, whose
right-hand side is the transition and whose left-hand side is the composite that
`pullbackCompHom` is a `def` for. -/
private theorem pullbackCompHom_eq_adicThickeningCompletionTransition (n : ℕ) (G : X.Modules) :
    pullbackCompHom (adicBaseChangeSucc A I f n)
        (pullback.fst f (adicThickeningι A I (n + 1)))
        (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n) G =
      (adicThickeningCompletionTransition A I f G n).hom :=
  pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition A I f n G

omit [LocallyOfFiniteType f] in
/-- **The compatibility `hu` of `AlgebraicGeometry.adicThickeningUnitSystemHom`, from the
compatibility in the thickening picture.** Let `u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` be a family of units on
the adic thickenings which is compatible with the canonical transitions
`AlgebraicGeometry.adicThickeningCompletionTransition` of the thickening picture — the form in
which a caller has it, since that is the shape of
`AlgebraicGeometry.unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso`, the compatibility
the transitions `hBtrans` of a cartesian system of algebra sheaves give. Then the family satisfies
the hypothesis `hu` of `AlgebraicGeometry.adicThickeningUnitSystemHom`: its direct images on `X`
are compatible with `AlgebraicGeometry.adicThickeningPushforwardTransition`.

This is `AlgebraicGeometry.structureUnitHom_comp_map_comp_of_unit_comp` at `iₙ ≫ vₙ₊₁ = vₙ`, with
its two binders discharged by statements already written at the adic morphisms:
`AlgebraicGeometry.unit_comp_adicThickeningPushforwardTransition` names the pushed-forward
transition, and
`AlgebraicGeometry.pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition` names the
comparison of the factorisation as the transition of the thickening picture. The epimorphism is
`AlgebraicGeometry.epi_unit_app_adicThickeningCompletion`. -/
public theorem structureUnitHom_comp_map_comp_adicThickeningPushforwardTransition
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (u : ∀ n : ℕ, unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n)
    (hu : ∀ n : ℕ, (pullbackUnitIso (adicBaseChangeSucc A I f n)).inv ≫
        (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (u (n + 1)) ≫
          (adicThickeningCompletionTransition A I f G.obj n).hom = u n)
    (n : ℕ) :
    structureUnitHom (pullback.fst f (adicThickeningι A I (n + 1))) ≫
        (Scheme.Modules.pushforward
            (pullback.fst f (adicThickeningι A I (n + 1)))).map (u (n + 1)) ≫
          adicThickeningPushforwardTransition A I f G n =
      structureUnitHom (pullback.fst f (adicThickeningι A I n)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map (u n) :=
  structureUnitHom_comp_map_comp_of_unit_comp
    (pullback.fst f (adicThickeningι A I (n + 1))) (adicBaseChangeSucc A I f n)
    (adicBaseChangeSucc_fst A I f n) G.obj
    (epi_unit_app_adicThickeningCompletion A I f G (n + 1))
    (unit_comp_adicThickeningPushforwardTransition A I f G n)
    (pullbackCompHom_eq_adicThickeningCompletionTransition A I f n G.obj).symm (hu n)

/-- **The unit side of `hdata`, with the compatibility asked for in the thickening picture.** Let
`G` be a coherent `𝒪_X`-module whose support is proper over an `I`-adically complete Noetherian
base and let `u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` be a family of morphisms on the adic thickenings compatible
with the canonical transitions of the thickening picture. Then there is a morphism `μ : 𝒪_X ⟶ G`
on `X` restricting to `u n` for every `n`.

This is `AlgebraicGeometry.exists_unit_of_adicThickeningPushforwardFamily` with its hypothesis
`hu` discharged, so that the compatibility a caller must supply is the one it has: the hypothesis
here is literally the statement of
`AlgebraicGeometry.unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso` at the module system
of a cartesian system of algebra sheaves, read along an isomorphism of systems. No hypothesis on
the theorem on formal functions is carried, and no tensor product or multiplication enters. -/
public theorem exists_unit_of_adicThickeningTransitionFamily [IsNoetherianRing A]
    [IsAdicComplete I A]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : Stacks.Algebraization.HasProperSupport f G.obj)
    (u : ∀ n : ℕ, unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n)
    (hu : ∀ n : ℕ, (pullbackUnitIso (adicBaseChangeSucc A I f n)).inv ≫
        (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (u (n + 1)) ≫
          (adicThickeningCompletionTransition A I f G.obj n).hom = u n) :
    ∃ μ : SheafOfModules.unit X.ringCatSheaf ⟶ G.obj, ∀ n : ℕ,
      (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).inv ≫
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ = u n :=
  exists_unit_of_adicThickeningPushforwardFamily A I f G u hG
    (structureUnitHom_comp_map_comp_adicThickeningPushforwardTransition A I f G u hu)

end Adic

end AlgebraicGeometry

end
