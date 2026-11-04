module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsObstructionMap
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonTransitivity
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyPullbackAdjoint

/-!
# The identity case of the map of obstruction modules of Stacks 07YH

`map_id` and `map_local` of clause (2) of an obstruction theory (Stacks 07YG) ask what
`Deformation.Artin.SectionsSheaf.obstructionMap` is at an identity morphism of affine objects.
`Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id` contracts its two cohomology factors
there to `Hⁿ(X, η_𝒢 ≫ k)` for `η` the unit of the pullback–pushforward adjunction, and what is
left to do is (i) cancel the four spelling comparisons the construction is wrapped in and
(ii) compute `η ≫ k` at the coefficient map of Stacks 07YH. This file does (i) — in the abstract,
at the spelling comparisons themselves, and **assembled**: `obstructionMapGen` at `g = 𝟙 X` is
`Hⁿ` of the coefficient map as soon as (ii) holds. (ii) is stated exactly here and is now proved,
in `StacksFrontier/Deformation/Artin/Obstruction/SectionsFirstFactorIdentity.lean` (its first
tensor factor), below (its second) and
`StacksFrontier/Deformation/Artin/Obstruction/SectionsCoefficientIdentity.lean` (their assembly),
so `obstructionMapGen_id` holds unconditionally as
`Deformation.Artin.SectionsSheaf.obstructionMapGen_id_of_semilinear`.

## Main results

* `Deformation.Artin.SectionsSheaf.rightDerivedCompIso_id_hom_app` and `..._id_inv_app` —
  **the composite right-derived comparison of an exact functor is the identity when that functor
  is the identity.** This is the one of the four spelling comparisons of
  `obstructionMap` that does not cancel against another, namely
  `Deformation.Artin.SectionsSheaf.rightDerivedRestrictScalarsIso` at the ring map
  `Γ(X, 𝒪_X) → Γ(X, 𝒪_X)` induced by `𝟙 X`; `..._identity_hom_app` and `..._identity_inv_app`
  are that instance.
* `Deformation.Artin.SectionsSheaf.conjugate_map_eq` — the other three cancel: a map conjugated
  by `Functor.isoWhiskerRight σ R ≪≫ ρ` on the left and `ρ` on the right is the map itself.
* `Deformation.Artin.SectionsSheaf.obstructionAssemble` — **the whole cancellation**, in the
  abstract shape the identity case of `obstructionMapGen` has: with the two cohomology factors
  contracted and the two degenerate comparisons identities, the composite is `Hⁿ` of the
  coefficient map.
* `Deformation.Artin.SectionsSheaf.moduleCohomologyAlongIso_id`,
  `..alongIso_hom_app_comp_id` and `..alongIso_comp_restrict_inv_id` — the two degenerate
  comparisons contracted at an identity morphism of schemes: cohomology read over the target of
  `𝟙 X` is cohomology of `X`, and the comparison of the two restriction-of-scalars spellings is
  an identity, so their composite is the single comparison of the two indexings of cohomology.
* `Deformation.Artin.SectionsSheaf.obstructionInner_id` — the inner composite of
  `obstructionMapGen` at `g = 𝟙 X`: `Hⁿ` of the coefficient map followed by that one
  comparison.
* `Deformation.Artin.SectionsSheaf.obstructionMapGen_id` — **the identity case, assembled**:
  granted the coefficient identity (ii) below, `obstructionMapGen` at `g = 𝟙 X` is `Hⁿ` of the
  coefficient map, which is what `map_id` and `map_local` of clause (2) ask for.
* `Deformation.Artin.SectionsSheaf.unit_comp_pullbackId_hom_app` — the unit of the
  pullback–pushforward adjunction at `𝟙 X` followed by the identity law `(𝟙 X)^* ≅ 𝟭` is the
  identity. This is the adjoint equation for Mathlib's
  `AlgebraicGeometry.Scheme.Modules.pullbackId`.
* `Deformation.Artin.SectionsSheaf.baseChangeSheafIsoGen_id_hom` and
  `..unit_comp_baseChangeSheafIsoGen_id` — **the second of the two tensor factors of the
  coefficient map degenerates at an identity**: `g^* 𝓕_A ≅ 𝓕_{A₁}` at `g = 𝟙 X` *is* the
  identity law for pullback, so composed with the unit it is `𝟙 𝓕_A`. This is one of the two
  factor-wise statements (ii) reduces to; the other is
  `Deformation.Artin.SectionsSheaf.unit_comp_tildeFirstFactorMapGen_id`, in
  `StacksFrontier/Deformation/Artin/Obstruction/SectionsFirstFactorIdentity.lean`, and both are
  now proved.

## Main definitions

* `Deformation.Artin.SectionsSheaf.pullbackIdUnit` — the unit `𝒢 ⟶ (𝟙 X)^* 𝒢` of the
  pullback–pushforward adjunction at an identity morphism of schemes, read in the
  `AlgebraicGeometry.Scheme.Modules` spelling. This is the arrow that does **not** disappear at
  an identity: `(𝟙 X)^*` is an abstract left adjoint and is not `𝟭`.

## What is done, and what is not

`map_id` and `map_local` are **proved**, in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`. They rest on three
ingredients: the coefficient identity (ii), its *assembly* out of its two tensor factors, and
the two transports between `obstructionMapGen` and `affineObstructionMap`. The identity (ii)
alone does not give `map_id` and `map_local`; item 3 below says why.
`map_comp` is not proved.

1. **The mathematics, and where each part of it is.** The identity in question is
```
pullbackIdUnit X ((tensorSheafFunctor π 𝓕_X).obj M) ≫
    tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd (ofSemilinear (𝟙 A) f) =
  (tensorSheafFunctor π 𝓕_X).map f,
```
   the coefficient half of the map of obstruction modules composed with the unit. The
   comparison of [Stacks, Tag 01CD] composed with the unit is the tensor product of the two
   units, which is `Stacks.RingedSpace.unit_comp_comparisonIso_id` in
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparisonIdentity.lean`, and
   that splits the obligation into the two tensor factors. **Both factors are now proved:**
   * `η_{π^* M̃} ≫ tildeFirstFactorMapGen (𝟙 A) π π (𝟙 X) hfst (ofSemilinear (𝟙 A) f) =
     (Scheme.Modules.pullback π).map ((tilde.functor A).map f)` — **done**, as
     `Deformation.Artin.SectionsSheaf.unit_comp_tildeFirstFactorMapGen_id` in
     `StacksFrontier/Deformation/Artin/Obstruction/SectionsFirstFactorIdentity.lean`;
   * `η_{𝓕_X} ≫ (baseChangeSheafIsoGen s s 𝓕 (𝟙 X) hsnd).hom = 𝟙 𝓕_X` — **done**, as
     `unit_comp_baseChangeSheafIsoGen_id` below.

   The second went through as follows. `baseChangeSheafIsoGen` at `g = 𝟙 X` is
   `Scheme.Modules.pullbackComp` followed by a transport, and that composite is the right
   unitality law `AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality` of Mathlib's
   pullback pseudofunctor read at a component — `baseChangeSheafIsoGen_id_hom`; the transport it
   produces is an `eqToHom` of an equality of functors and `Scheme.Modules.pullbackCongr` is
   the `eqToIso` of the same equality, so they agree by proof irrelevance. What is then left is
   the adjoint equation for `Scheme.Modules.pullbackId`, which is
   `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom` read through
   `CategoryTheory.unit_conjugateEquiv` — `unit_comp_pullbackId_hom_app`. Both passages between
   the ringed-space and `Scheme.Modules` spellings of the unit are `rfl` and cost 4 heartbeats.

   The first factor needed three things the second did not, and all three are in
   `SectionsFirstFactorIdentity.lean`. (a) `hfst` is `𝟙 X ≫ π = π ≫ Spec.map (𝟙 A)` and not
   `𝟙 X ≫ π = π`, so `pullbackCongr hfst` is split as the transport along `𝟙 X ≫ π = π` —
   which right unitality supplies — followed by the transport along `π = π ≫ Spec.map (𝟙 A)`;
   the split is free, because `pullbackCongr` is `eqToIso` of an equality of *functors* and
   equality of functors is a `Prop`, so `pullbackCongr_hom_app_comp` composes two of them. (b)
   The remaining factor is a *left* unitality statement at `Spec.map (𝟙 A)` while
   `AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality` is stated at `𝟙 (Spec A)`;
   the cure is not a congruence lemma for `pullbackComp` but to carry the morphism as a
   variable `u` with `hu : u = 𝟙 Y` and `subst` it — which is also the only way to *state*
   `unit_comp_pullbackSpecIdIso`, since before the substitution `(pushforward u).obj Z` and `Z`
   are different objects. (a) and (b) together are `pullbackComp_congr_comp_inv_app`. (c)
   `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` at the identity ring map is a
   development of its own, not a step, and it is `tildePullbackIso_id_hom_app`: the comparison
   is the identity law for pullback followed by the associated sheaf of the unit `m ↦ 1 ⊗ m` of
   extension of scalars. Its handle is
   `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` for
   `..tildePullbackAdjunction` and `..extendScalarsTildeAdjunction`, exactly as
   `..tildePullbackIso_unit` uses it, and the computation it reduces to is made on sections over
   the whole space, where the identity law for the *direct* image is the identity map.

   The assembly of the two factors is
   `Deformation.Artin.SectionsSheaf.unit_comp_tensorSheafPullbackMapGen_id`, in
   `StacksFrontier/Deformation/Artin/Obstruction/SectionsCoefficientIdentity.lean`:
   `tensorSheafPullbackMapGen` is the Tag 01CD comparison wrapped in the two `eqToHom`s of
   `tensorSheafFunctor_obj_eq` and followed by `Stacks.RingedSpace.tensorSheaf` applied to a
   `×ₘ` of the two factors, and carrying the unit past those `eqToHom`s and that product
   morphism is `..tensorAssemble` there, with every arrow a variable and the two `eqToHom`s
   constrained by `e = 𝟙` rather than inspected. The product morphism itself is taken apart by
   `CategoryTheory.Prod.hom_ext`, composition in a product category being componentwise by
   `rfl`.

2. **The assembly is done, and the definitional-equality cost it was blocked by is paid by
   splitting.** `obstructionMapGen_id` applies `obstructionAssemble` to the unfolding of
   `obstructionMapGen` at `g = 𝟙 X`. Doing it in one declaration does not work and does not
   fail for a mathematical reason: the term is correct, and it costs 1.7 · 10⁶ heartbeats
   against a budget of 2 · 10⁵. `rw` and `simp only` are not available on this goal either —
   they report it "not type-correct under the `implicit` transparency level", because
   `AlgebraicGeometry.Scheme.ringCatSheaf X` is a `TopCat.Sheaf RingCat ↑X.toPresheafedSpace`
   where `Sheaf (Opens.grothendieckTopology ↥X) RingCat` is expected and `TopCat.Sheaf` is a
   plain `def`.

   What makes it fit is that the cost is in comparing the two spellings of cohomology —
   `Stacks.Cohomology.moduleCohomologyAlong (𝟙 X).toLRSHom.toShHom n` against
   `Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace n`, and
   `(Γ ⋙ restrictGlobalScalars (𝟙 X)).rightDerived n` against `Γ.rightDerived n` — and that
   those comparisons are **not uniformly expensive**: the comparison of the two
   *functors* costs 8 · 10³ heartbeats, of the two functors *applied to an object*
   6.8 · 10⁴, and of two morphism components whose codomains differ by it 3.5 · 10⁶. So the
   declarations below are arranged to make each comparison at the cheapest level available:
   `moduleCohomologyAlongIso_id` at the level of the two isomorphisms, `obstructionAssemble`
   with the inner composite a *single* variable rather than its four arrows (which would ask
   for one comparison per arrow), and `alongIso_hom_app_comp_id` split off from
   `alongIso_comp_restrict_inv_id` so that each carries one. Every declaration then comes in
   under budget — 1.5 · 10⁵ for the worst of them. **Do not raise the heartbeats**; if another
   factor has to be added here, split again.

3. **`map_id` and `map_local` do not follow from `obstructionMapGen_id` alone**, and the two
   transports that stand between them are built in
   `StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`. That lemma is
   about `obstructionMapGen` at `g = 𝟙 X`; `map_id` and `map_local` are about
   `Deformation.Artin.SectionsSheaf.affineObstructionMap`. `obstructionMap` instantiates `g` at
   `baseChangeMap q (quotHom ψ t)`, which `baseChangeMap_quotHom_affineHom_id` evaluates at an
   identity morphism of affine objects as `eqToHom h'` — a transport between two *equal* fibre
   products, not `𝟙` — and that is what `..obstructionMapGen_eqToHom` gets past; and
   `affineObstructionMap` goes through `obstructionMapOf`, whose `match`
   on `Spec.map (𝟙 A) ≫ t = t` does not reduce, because neither side of that equality is a
   variable, and what the map is instead is `..obstructionMapOf_eq_comp_eqToHom`. The two
   transports are inverse and cancel, by `..obstructionMapOf_id_eq`. The full account is in the
   "what is not done" of
   `StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMap.lean`.

The restatement of `obstructionMap` with the base-change morphism of schemes as a parameter —
the first of the three obligations the previous record left — **is** done, in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMap.lean`: it is
`Deformation.Artin.SectionsSheaf.obstructionMapGen`, and `obstructionMap` is now its
instantiation at the base-change immersion, with its type unchanged. The transport law for
`moduleCohomologyMap` along an equality of ringed spaces, the alternative that record offered,
is therefore not needed.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleComparison Stacks.Cohomology.DerivedCompTransport

universe u

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Three of the four spelling comparisons cancel -/

/-- **A map conjugated by two compatible comparisons is the map itself.** For `σ : Cf ≅ Df` and
`ρ : Df ⋙ R ≅ Φ`, conjugating `Cf.map x` by `Functor.isoWhiskerRight σ R ≪≫ ρ` on the left and
by `ρ` on the right gives `Φ.map x`: the naturality of `σ` cancels it against itself and the
naturality of `ρ` cancels `ρ` against itself.

At `Cf = Hⁿ(X, -)` in the bounded-below spelling, `Df = Hⁿ(X, -)` in the `Functor.rightDerived`
spelling, `R` restriction of scalars to the base ring and `Φ` the degree-`n` part of
`cohomologyDeltaFunctor`, this is the cancellation of three of the four spelling comparisons
`Deformation.Artin.SectionsSheaf.obstructionMapGen` is wrapped in. -/
theorem conjugate_map_eq {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {Cf Df : C₁ ⥤ C₂} {R : C₂ ⥤ C₃} {Φ : C₁ ⥤ C₃} (σ : Cf ≅ Df) (ρ : Df ⋙ R ≅ Φ)
    {P Q : C₁} (x : P ⟶ Q) :
    ((Functor.isoWhiskerRight σ R ≪≫ ρ).app P).inv ≫
        R.map (Cf.map x ≫ σ.hom.app Q) ≫ ρ.hom.app Q = Φ.map x := by
  have hσ : (σ.inv.app P) ≫ Cf.map x ≫ σ.hom.app Q = Df.map x := by
    rw [σ.hom.naturality x, ← Category.assoc]
    simp
  have hρ := ρ.hom.naturality x
  simp only [Iso.trans_inv, Iso.app_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.assoc]
  rw [← Category.assoc (R.map (σ.inv.app P)), ← Functor.map_comp, hσ]
  rw [show R.map (Df.map x) = (Df ⋙ R).map x from rfl, hρ]
  simp

/-! ### The fourth is the identity -/

/-- **The composite right-derived comparison for the identity functor is the identity.** For an
additive `F`, the comparison `F.rightDerived n ⋙ 𝟭 ≅ (F ⋙ 𝟭).rightDerived n` of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` attached to the identity comparison is
the identity. The proof is its own composition law at `G = G' = 𝟭`, which gives
`x ≫ x = x` for `x` the component, and `x` is invertible. -/
theorem rightDerivedCompIso_id_hom_app {A B : Type*} [Category A] [Category B] [Abelian A]
    [HasInjectiveResolutions A] [Abelian B] (F : A ⥤ B) [F.Additive] (n : ℕ) (Z : A) :
    (rightDerivedCompIso F (𝟭 B) (F ⋙ 𝟭 B) (Iso.refl _) n).hom.app Z = 𝟙 _ := by
  have h2 := rightDerivedCompIso_hom_app_comp F (𝟭 B) (F ⋙ 𝟭 B) (𝟭 B) ((F ⋙ 𝟭 B) ⋙ 𝟭 B)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (fun _ => by simp) n Z
  exact (cancel_epi ((rightDerivedCompIso F (𝟭 B) (F ⋙ 𝟭 B) (Iso.refl _) n).app Z).hom).1
    (h2.trans (Category.comp_id _).symm)

/-- The inverse half of `rightDerivedCompIso_id_hom_app`. -/
theorem rightDerivedCompIso_id_inv_app {A B : Type*} [Category A] [Category B] [Abelian A]
    [HasInjectiveResolutions A] [Abelian B] (F : A ⥤ B) [F.Additive] (n : ℕ) (Z : A) :
    (rightDerivedCompIso F (𝟭 B) (F ⋙ 𝟭 B) (Iso.refl _) n).inv.app Z = 𝟙 _ := by
  have h := (rightDerivedCompIso F (𝟭 B) (F ⋙ 𝟭 B) (Iso.refl _) n).inv_hom_id_app Z
  rwa [rightDerivedCompIso_id_hom_app F n Z, Category.comp_id] at h

/-- **`rightDerivedRestrictScalarsIso` at an identity morphism of schemes is the identity.**
The ring map on global sections induced by `𝟙 X` is the identity, so restriction of scalars
along it is `𝟭` on the nose and the comparison degenerates. This is the one of the four spelling
comparisons of `Deformation.Artin.SectionsSheaf.obstructionMapGen` that has nothing to cancel
against. -/
theorem rightDerivedRestrictScalarsIso_identity_hom_app (X : Scheme.{u}) (n : ℕ)
    (Z : Modules X.toRingedSpace) :
    (rightDerivedRestrictScalarsIso
        (Stacks.Cohomology.globalSectionsRingHom (𝟙 X : X ⟶ X).toLRSHom.toShHom).hom
        (Stacks.Cohomology.moduleGlobalSections X.toRingedSpace)
        (Stacks.Cohomology.moduleGlobalSections_additive _) n).hom.app Z = 𝟙 _ :=
  rightDerivedCompIso_id_hom_app _ n Z

/-- The inverse half of `rightDerivedRestrictScalarsIso_identity_hom_app`. -/
theorem rightDerivedRestrictScalarsIso_identity_inv_app (X : Scheme.{u}) (n : ℕ)
    (Z : Modules X.toRingedSpace) :
    (rightDerivedRestrictScalarsIso
        (Stacks.Cohomology.globalSectionsRingHom (𝟙 X : X ⟶ X).toLRSHom.toShHom).hom
        (Stacks.Cohomology.moduleGlobalSections X.toRingedSpace)
        (Stacks.Cohomology.moduleGlobalSections_additive _) n).inv.app Z = 𝟙 _ :=
  rightDerivedCompIso_id_inv_app _ n Z

/-! ### The whole cancellation, in the shape the identity case has -/

/-- **The four spelling comparisons of the map of obstruction modules cancel at an identity.**
This is the abstract shape of the identity case of
`Deformation.Artin.SectionsSheaf.obstructionMapGen`: with the inner composite `w` of the two
cohomology factors and the two degenerate comparisons already contracted to `Cf.map x ≫ σ x`,
and with the transport `E` an identity, the whole composite is `Φ.map x`.

Every arrow is a variable constrained by an equation rather than written out, and the outer
comparison `I` in particular: the unifier then matches the conclusion against a goal
first-order, and the one definitional comparison per arrow is made where this is applied. With
`I` written as `Functor.isoWhiskerRight σ R ≪≫ ρ` in the conclusion instead, matching a goal
asks for the `inv` field of a `CategoryTheory.NatIso.ofComponents` built by a tactic proof, and
that exhausts the heartbeat budget in `whnf`.

The inner composite is **one** variable `w` and not the four arrows it is made of, and that is
forced by the heartbeat budget rather than by taste: the four arrows of
`obstructionMapGen` are typed in the `Stacks.Cohomology.moduleCohomologyAlong` spelling of
cohomology and `Cf`, `Df` here in the `Functor.rightDerived` one, so a signature naming all
four asks for one definitional comparison of the two spellings per arrow, each of them
~10⁵ heartbeats, and the application of the assembled lemma then costs 1.7 · 10⁶. With the
composite a single variable the comparisons are made once each, in
`obstructionInner_id` and in `alongIso_comp_restrict_inv_id`, and each
declaration comes in under budget. -/
theorem obstructionAssemble {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {Cf Df : C₁ ⥤ C₂} {R : C₂ ⥤ C₃} {Φ : C₁ ⥤ C₃} (σ : Cf ≅ Df) (ρ : Df ⋙ R ≅ Φ)
    (I : Cf ⋙ R ≅ Φ) {P Q : C₁} (x : P ⟶ Q) (w : Cf.obj P ⟶ Df.obj Q)
    (E : R.obj (Df.obj Q) ⟶ R.obj (Df.obj Q)) (H : R.obj (Df.obj Q) ⟶ Φ.obj Q)
    (hI : I = Functor.isoWhiskerRight σ R ≪≫ ρ) (hw : w = Cf.map x ≫ σ.hom.app Q)
    (hE : E = 𝟙 _) (hH : H = ρ.hom.app Q) :
    (I.app P).inv ≫ R.map w ≫ E ≫ H = Φ.map x := by
  subst hI; subst hw; subst hE; subst hH
  rw [Category.id_comp]
  exact conjugate_map_eq σ ρ x

/-! ### The two degenerate comparisons, contracted -/

/-- **At an identity morphism of schemes the two cohomology comparisons are the same iso.**
`moduleCohomologyAlongIso` reads cohomology over the target of a morphism; at `𝟙 X` the target
is `X` itself and the iso is `spaceModuleCohomologyIso`, on the nose. The comparison is made
here, between the two isomorphisms themselves, because at that level it is a comparison of
functors and cheap; between their components at an object it costs 3.5 · 10⁶ heartbeats. -/
theorem moduleCohomologyAlongIso_id (X : Scheme.{u}) (n : ℕ) :
    moduleCohomologyAlongIso (𝟙 X : X ⟶ X) n = spaceModuleCohomologyIso X n := rfl

/-- `moduleCohomologyAlongIso_id` read at a component and composed with the identity that
`rightDerivedRestrictScalarsIso_identity_inv_app` produces. This is the
right-unit half of `alongIso_comp_restrict_inv_id`, split off from it so that each of the two
carries only one comparison of the two spellings of cohomology. -/
theorem alongIso_hom_app_comp_id (X : Scheme.{u}) (n : ℕ) (Z : Modules X.toRingedSpace) :
    (moduleCohomologyAlongIso (𝟙 X : X ⟶ X) n).hom.app Z ≫
        𝟙 (((Stacks.Cohomology.moduleGlobalSections X.toRingedSpace ⋙
          ModuleCat.restrictScalars (Stacks.Cohomology.globalSectionsRingHom
            (𝟙 X : X ⟶ X).toLRSHom.toShHom).hom).rightDerived n).obj Z) =
      (spaceModuleCohomologyIso X n).hom.app Z :=
  (Category.comp_id ((moduleCohomologyAlongIso (𝟙 X : X ⟶ X) n).hom.app Z)).trans
    (congrArg (fun τ => τ.hom.app Z) (moduleCohomologyAlongIso_id X n))

/-- **The last two of the four spelling comparisons contract to the first one.** At an identity
morphism of schemes, the comparison of the two indexings of cohomology followed by the
comparison of the two restriction-of-scalars spellings is the comparison of the two indexings
read on `X` itself: the second factor is an identity, by
`rightDerivedRestrictScalarsIso_identity_inv_app`. -/
theorem alongIso_comp_restrict_inv_id (X : Scheme.{u}) (n : ℕ) (Z : Modules X.toRingedSpace) :
    (moduleCohomologyAlongIso (𝟙 X : X ⟶ X) n).hom.app Z ≫
        (rightDerivedRestrictScalarsIso
            (Stacks.Cohomology.globalSectionsRingHom
              (𝟙 X : X ⟶ X).toLRSHom.toShHom).hom
          (Stacks.Cohomology.moduleGlobalSections X.toRingedSpace)
          (Stacks.Cohomology.moduleGlobalSections_additive _) n).inv.app Z =
      (spaceModuleCohomologyIso X n).hom.app Z :=
  (congrArg (fun z => (moduleCohomologyAlongIso (𝟙 X : X ⟶ X) n).hom.app Z ≫ z)
      (rightDerivedRestrictScalarsIso_identity_inv_app X n Z)).trans
    (alongIso_hom_app_comp_id X n Z)

/-! ### The arrow that does not degenerate at an identity -/

/-- **The unit `𝒢 ⟶ (𝟙 X)^* 𝒢` of the pullback–pushforward adjunction at an identity morphism
of schemes**, read in the `AlgebraicGeometry.Scheme.Modules` spelling: the pushforward along an
identity is the identity functor on the nose, so the unit's target is the pullback itself and no
transport is involved.

This arrow is **not** an identity: `(𝟙 X)^*` is an abstract left adjoint and is not equal to
`𝟭`. It is what survives of the arrow of [Stacks, Tag 01FA] in the identity case of the map of
obstruction modules, by `Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id`.

Naming it is not cosmetic: the composite of the ringed-space unit with
`Deformation.Artin.SectionsSheaf.tensorSheafPullbackMapGen`, written out, asks the elaborator to
solve `(𝟙 X)^*` in the `Scheme.Modules` spelling against the ringed-space one with the middle
object of the composition a metavariable, and that exhausts the heartbeat budget in `whnf`. -/
def pullbackIdUnit (X : Scheme.{u}) (G : SheafOfModules.{u} X.ringCatSheaf) :
    G ⟶ (Scheme.Modules.pullback (𝟙 X)).obj G :=
  (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    (𝟙 X.toRingedSpace)).unit.app G

/-- **The unit followed by the identity law for pullback is the identity.** This is the adjoint
equation for `AlgebraicGeometry.Scheme.Modules.pullbackId` — its mate under the two adjunctions
`𝟭 ⊣ 𝟭` and `(𝟙 X)^* ⊣ (𝟙 X)_*` is the identity law for pushforward, which is
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom` — read through
`CategoryTheory.unit_conjugateEquiv`.

The two passages between spellings it needs are both `rfl` and cheap:
`pullbackIdUnit X G` is the unit of Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)`, and
`(AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app G` is `𝟙 G`, the pushforward along
an identity being the identity functor on the nose. -/
theorem unit_comp_pullbackId_hom_app (X : Scheme.{u}) (G : X.Modules) :
    pullbackIdUnit X G ≫ (Scheme.Modules.pullbackId X).hom.app G = 𝟙 G := by
  have h := CategoryTheory.unit_conjugateEquiv (Adjunction.id (C := X.Modules))
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom G
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  refine h.symm.trans ?_
  exact (Category.id_comp _).trans rfl

/-! ### The second tensor factor at an identity -/

section SecondFactor

variable {W X : Scheme.{u}} (s : X ⟶ W) (𝓕 : W.Modules)

/-- **`g^* 𝓕_A ≅ 𝓕_{A₁}` at `g = 𝟙 X` is the identity law for pullback.** The isomorphism is
`Scheme.Modules.pullbackComp` followed by the transport along `𝟙 X ≫ s = s`, and that composite
is the right unitality law of Mathlib's pullback pseudofunctor,
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality`, read at the component `𝓕`.

The transport the unitality law produces is an `eqToHom` of an equality of *functors*, and
`Scheme.Modules.pullbackCongr` is the `eqToIso` of the same equality, so the two agree by
proof irrelevance with no `eqToHom_app` step. -/
theorem baseChangeSheafIsoGen_id_hom (hsnd : (𝟙 X : X ⟶ X) ≫ s = s) :
    (baseChangeSheafIsoGen s s 𝓕 (𝟙 X) hsnd).hom =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback s).obj 𝓕) := by
  have h := congrArg (fun τ => NatTrans.app τ 𝓕)
    (Scheme.Modules.pseudofunctor_right_unitality s)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  have key : (Scheme.Modules.pullbackComp (𝟙 X) s).inv.app 𝓕 ≫
        (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback s).obj 𝓕) =
      (Scheme.Modules.pullbackCongr hsnd).hom.app 𝓕 := h
  have hd : (baseChangeSheafIsoGen s s 𝓕 (𝟙 X) hsnd).hom =
      (Scheme.Modules.pullbackComp (𝟙 X) s).hom.app 𝓕 ≫
        (Scheme.Modules.pullbackCongr hsnd).hom.app 𝓕 := rfl
  rw [hd, ← key, ← Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app,
    Category.id_comp]

/-- **The second of the two tensor factors of the coefficient map degenerates at an identity**:
the unit of the pullback–pushforward adjunction at `𝟙 X` followed by `g^* 𝓕_A ≅ 𝓕_{A₁}` is the
identity of `𝓕_A`.

This is the second of the two factor-wise obligations the identity case of clause (2) of
Stacks 07YG reduces to, by `Stacks.RingedSpace.unit_comp_comparisonIso_id`. The first — the
same statement for `tildeFirstFactorMapGen` — is
`Deformation.Artin.SectionsSheaf.unit_comp_tildeFirstFactorMapGen_id`, and their assembly is
`..unit_comp_tensorSheafPullbackMapGen_id`. -/
theorem unit_comp_baseChangeSheafIsoGen_id (hsnd : (𝟙 X : X ⟶ X) ≫ s = s) :
    pullbackIdUnit X ((Scheme.Modules.pullback s).obj 𝓕) ≫
        (baseChangeSheafIsoGen s s 𝓕 (𝟙 X) hsnd).hom = 𝟙 _ := by
  rw [baseChangeSheafIsoGen_id_hom]
  exact unit_comp_pullbackId_hom_app X _

end SecondFactor

/-! ### What the identity case reduces to -/

section Identity

variable {A : CommRingCat.{u}} {W X : Scheme.{u}} (π : X ⟶ Spec A) (s : X ⟶ W)
  (𝓕 : W.Modules)

/-- **The two cohomology factors of the map of obstruction modules, contracted at an identity.**
At `g = 𝟙 X` the pullback map on cohomology followed by `Hⁿ` of the coefficient map is `Hⁿ` of
the coefficient map composed with the unit of the pullback–pushforward adjunction: both arrows
of [Stacks, Tag 01F9] degenerate, by `Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id`.

This is the first half of the identity case; what the second half needs is recorded in this
module's "what is not done". -/
theorem moduleCohomologyPullbackMap_comp_tensorSheafPullbackMapGen_id (n : ℕ)
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map (𝟙 A)) (hsnd : (𝟙 X : X ⟶ X) ≫ s = s)
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (α : (ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M ⟶ N)
    (hα : pullbackIdUnit X ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α =
      (tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) :
    Stacks.Cohomology.moduleCohomologyPullbackMap (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        (Stacks.Cohomology.moduleCohomologyAlong (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)).map
          (tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α) =
      (Stacks.Cohomology.moduleCohomologyAlong (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)).map
        ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) :=
  (Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id (X := X.toRingedSpace) (n : ℤ)
      ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M)
      (tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α)).trans
    (congrArg (fun z => (Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace (n : ℤ)).map z)
      hα)

/-- **The inner composite of the map of obstruction modules at an identity.** The two cohomology
factors and the two degenerate spelling comparisons of
`Deformation.Artin.SectionsSheaf.obstructionMapGen` contract, at `g = 𝟙 X`, to `Hⁿ` of the
coefficient map followed by the single comparison of the two indexings of cohomology: the first
two factors by `moduleCohomologyPullbackMap_comp_tensorSheafPullbackMapGen_id` and the last two by
`alongIso_comp_restrict_inv_id`.

This is the hypothesis `hw` that `obstructionAssemble` asks for, at the identity. -/
theorem obstructionInner_id (n : ℕ)
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map (𝟙 A)) (hsnd : (𝟙 X : X ⟶ X) ≫ s = s)
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (α : (ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M ⟶ N)
    (hα : pullbackIdUnit X ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α =
      (tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) :
    Stacks.Cohomology.moduleCohomologyPullbackMap (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        (Stacks.Cohomology.moduleCohomologyAlong
            (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)).map
          (tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α) ≫
        (moduleCohomologyAlongIso (𝟙 X : X ⟶ X) n).hom.app
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N) ≫
        (rightDerivedRestrictScalarsIso
            (Stacks.Cohomology.globalSectionsRingHom
              (𝟙 X : X ⟶ X).toLRSHom.toShHom).hom
          (Stacks.Cohomology.moduleGlobalSections X.toRingedSpace)
          (Stacks.Cohomology.moduleGlobalSections_additive _) n).inv.app
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N) =
      (Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace (n : ℤ)).map
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) ≫
        (spaceModuleCohomologyIso X n).hom.app
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N) :=
  (congrArg (fun z =>
        Stacks.Cohomology.moduleCohomologyPullbackMap (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)
            ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
          (Stacks.Cohomology.moduleCohomologyAlong
              (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)).map
            (tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α) ≫ z)
      (alongIso_comp_restrict_inv_id X n
        ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N))).trans
    ((Category.assoc
        (Stacks.Cohomology.moduleCohomologyPullbackMap (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M))
        ((Stacks.Cohomology.moduleCohomologyAlong
            (𝟙 X : X ⟶ X).toLRSHom.toShHom (n : ℤ)).map
          (tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α))
        ((spaceModuleCohomologyIso X n).hom.app
          ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N))).symm.trans
      (congrArg (fun z => z ≫ (spaceModuleCohomologyIso X n).hom.app
            ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N))
        (moduleCohomologyPullbackMap_comp_tensorSheafPullbackMapGen_id π s 𝓕 n hfst hsnd f α hα)))

/-- **The map of obstruction modules at an identity is `Hⁿ` of the coefficient map**, granted
the one coefficient-level identity the construction still owes.

This is the identity case of clause (2) of Stacks 07YG for the example of Stacks 07YH,
assembled: the two cohomology factors degenerate by
`Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id`, the four spelling comparisons cancel by
`obstructionAssemble`, and what is left is the hypothesis `hα` — that the coefficient half of
the map, composed with the unit of the pullback–pushforward adjunction at `𝟙 X`, is
`𝓕_A ⊗_A f`.

That hypothesis is now discharged by
`Deformation.Artin.SectionsSheaf.unit_comp_tensorSheafPullbackMapGen_id`, and this lemma with it
is `..obstructionMapGen_id_of_semilinear`. `map_id` and `map_local` do **not** follow from this
lemma alone — one record claimed they did — because they are statements about
`affineObstructionMap`, and two transports stand between the two; those transports are built in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`, where the two
conditions are proved. -/
theorem obstructionMapGen_id (n : ℕ)
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map (𝟙 A)) (hsnd : (𝟙 X : X ⟶ X) ≫ s = s)
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (α : (ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M ⟶ N)
    (hα : pullbackIdUnit X ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd α =
      (tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) :
    obstructionMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd n α =
      ((cohomologyDeltaFunctor π).functor n).map
        ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) :=
  obstructionAssemble (spaceModuleCohomologyIso X n) (cohomologyRestrictIso π n)
    (cohomologyPlusDeltaIso π n)
    ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) _ _ _
    rfl (obstructionInner_id π s 𝓕 n hfst hsnd f α hα) (eqToHom_refl _ _) rfl

end Identity

end Deformation.Artin.SectionsSheaf

end
