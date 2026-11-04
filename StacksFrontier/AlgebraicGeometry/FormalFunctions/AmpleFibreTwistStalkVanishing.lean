module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistBaseChange
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# The vanishing clause of Tag 0D2M at the stalk

[Stacks, Tag 0D2M] concerns a proper morphism `f : X ⟶ Y` with `Y` Noetherian, an invertible
`𝒪_X`-module `ℒ`, a coherent `𝒪_X`-module `ℱ` and a point `y ∈ Y` at which `ℒ_y` is ample on
the fibre `X_y`; its first conclusion is that for all large `d` the stalk
`R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)_y` vanishes for every `p > 0`.

`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistBaseChange.lean` proves both
clauses of the tag on the base change `X' = X ×_Y Spec 𝒪_{Y,y}`, where they are statements about
`H ᵖ(X', ℱ' ⊗ ℒ' ^⊗ d)`. What this file supplies is the passage from that cohomology to the
stalk — degree-`p` flat base change along `Spec 𝒪_{Y,y} ⟶ Y`, in the one shape the tag needs.

## Main results

* `Stacks.FormalFunctions.isPullback_stalkBaseChangeRes` — the base change `X'` is also the
  base change of `f ∣_ V` along `Spec 𝒪_{Y,y} ⟶ V`, for any open `V ∋ y`. This is the square the
  affine-base theorems are applied to, and giving `X'` itself as its corner is what avoids
  transporting cohomology along an isomorphism of schemes.
* `Stacks.FormalFunctions.isZero_stalk_rightDerived_of_subsingleton_stalkBaseChange` — **the
  bridge**: if `H ᵖ(X', q^* ℳ)` vanishes, where `q : X' ⟶ X` is the projection, then the stalk
  `R ᵖ f_*(ℳ)_y` vanishes. No hypothesis on `Y`, and `f` only separated and quasi-compact.
* `Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_twistModule` — **the vanishing clause
  of [Stacks, Tag 0D2M]**, at the tag's own hypotheses: a single `d₀` such that for `d ≥ d₀` and
  every `p > 0` the stalk `R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)_y` is zero.

## Implementation notes

The chain of the bridge runs through one affine open `V ∋ y`, chosen inside the proof, and is a
chain of *isomorphisms of modules of sections*; nothing is ever transported along a mere
bijection of cohomology groups, so each step is a single library comparison applied once.

Read from the stalk end, with `T = Spec 𝒪_{Y,y}`, `g : T ⟶ Y` the canonical morphism, `q` its
factorization through `V`, `𝒜 = R ᵖ f_* ℳ` and `ℬ = 𝒜|_V`:

1. `AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv` identifies the stalk `𝒜_y`
   with `Γ(T, g^* 𝒜)`, which is where quasi-coherence of the higher direct image
   ([Stacks, Tag 01XK]'s companion `isQuasicoherent_rightDerived`) is used.
2. `g = q ≫ V.ι`, so `g^* 𝒜 ≅ q^* ℬ` by the composition law for module pullbacks.
3. `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` computes `Γ(T, q^* ℬ)` as
   `Γ(T, ⊤) ⊗_{Γ(V, ⊤)} Γ(ℬ, ⊤)` — both `V` and `T` being affine. This is the step that
   replaces the localization-of-the-stalk bookkeeping: no prime ideal and no `IsLocalization`
   hypothesis enters.
4. [Stacks, Tag 01E5] for schemes (`higherDirectImageRestrictIso`) and [Stacks, Tag 01XK] over
   the affine base `V` (`baseSectionsRightDerivedPushforwardIso`) rewrite `Γ(ℬ, ⊤)` as
   `H ᵖ(f ⁻¹ V, ℳ|_{f ⁻¹ V})`.
5. `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso` — flat base change for the cohomology of
   a quasi-coherent module over affine bases, in every degree — identifies the resulting tensor
   product with `H ᵖ(X', q^* ℳ)`. It is applied at the square of
   `isPullback_stalkBaseChangeRes`, whose corner is `X'` itself.

Only the vanishing is claimed, and that is what makes step 5 usable: the isomorphism it produces
is not identified with the canonical base-change map, and `Subsingleton` transports along any
isomorphism. The other clause of the tag is a surjectivity of a *named* map and cannot be routed
this way.

Flatness of `q` is cancelled off flatness of `g` by
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms`,
`V.ι` being a monomorphism.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

open Stacks.AlgebraicGeometry.ModuleBaseChange (baseSectionsRightDerivedPushforwardIso)
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (higherDirectImageRestrictIso)
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars
  le_preimage_top)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Ample (IsAmple IsInvertibleModule tensorPowModule)
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.FormalFunctions

variable {X Y : Scheme.{u}}

/-! ### Transporting subsingletons -/

/-- **A subsingleton transports backwards along an isomorphism of a concrete category.** The
objects compared below live in `ModuleCat` over five different rings, and the only thing asked of
each comparison is that it is a bijection of underlying sets. -/
public theorem subsingleton_of_iso {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [inst : ∀ A B : C, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    {A B : C} (e : A ≅ B) (h : Subsingleton (CC B)) : Subsingleton (CC A) :=
  Function.Injective.subsingleton (ConcreteCategory.bijective_of_isIso e.hom).1

/-! ### The base change as a base change over an open of the target -/

variable (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] (y : Y) {V : Y.Opens} (hy : y ∈ V)

/-- **The projection `X' ⟶ X` lands in `f ⁻¹ V` when `y ∈ V`**, and this is the resulting
morphism `X' ⟶ f ⁻¹ V`. It is obtained as a lift through the cartesian square of
`AlgebraicGeometry.isPullback_morphismRestrict`, so that its two compatibilities come for
free. -/
public def stalkBaseChangeRes : stalkBaseChange f y ⟶ (f ⁻¹ᵁ V : Scheme.{u}) :=
  (isPullback_morphismRestrict f V).flip.lift (stalkBaseChangeι f y)
    (stalkBaseChangeStructure f y ≫ V.fromSpecStalkOfMem y hy)
    (by rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]; exact pullback.condition)

omit [IsSeparated f] [QuasiCompact f] in
/-- `Stacks.FormalFunctions.stalkBaseChangeRes` is the projection `X' ⟶ X` read into
`f ⁻¹ V`. -/
public theorem stalkBaseChangeRes_comp_ι :
    stalkBaseChangeRes f y hy ≫ (f ⁻¹ᵁ V).ι = stalkBaseChangeι f y :=
  (isPullback_morphismRestrict f V).flip.lift_fst _ _ _

omit [IsSeparated f] [QuasiCompact f] in
/-- **`X' = X ×_Y Spec 𝒪_{Y,y}` is the base change of `f ∣_ V` along `Spec 𝒪_{Y,y} ⟶ V`** for
any open `V ∋ y`. The square of `X'` over `Y` is cartesian and so is the square of `f ∣_ V` over
`V.ι`, and `Spec 𝒪_{Y,y} ⟶ Y` factors through `V`; the claim is the right-cancellation of the
second out of the first. -/
public theorem isPullback_stalkBaseChangeRes :
    IsPullback (stalkBaseChangeRes f y hy) (stalkBaseChangeStructure f y) (f ∣_ V)
      (V.fromSpecStalkOfMem y hy) := by
  refine IsPullback.of_right (h₁₂ := (f ⁻¹ᵁ V).ι) (h₂₂ := V.ι) ?_ ?_
    (isPullback_morphismRestrict f V).flip
  · rw [stalkBaseChangeRes_comp_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact IsPullback.of_hasPullback f (Y.fromSpecStalk y)
  · exact (isPullback_morphismRestrict f V).flip.lift_snd _ _ _

/-- **`Spec 𝒪_{Y,y} ⟶ V` is flat.** `Spec 𝒪_{Y,y} ⟶ Y` is flat,
`AlgebraicGeometry.flat_fromSpecStalk`, and flatness may be cancelled against the
monomorphism `V.ι`. -/
public theorem flat_fromSpecStalkOfMem : Flat (V.fromSpecStalkOfMem y hy) := by
  have h1 : Flat (V.fromSpecStalkOfMem y hy ≫ V.ι) := by
    rw [Scheme.Opens.fromSpecStalkOfMem_ι V y hy]
    exact AlgebraicGeometry.flat_fromSpecStalk Y y
  have h2 : MorphismProperty.HasOfPostcompProperty (@Flat)
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  exact h2.of_postcomp _ V.ι (inferInstanceAs (Mono V.ι)) h1

/-- **The module `H ᵖ(X', ·)` is computed on is the pullback of `ℳ` to `X'`.** Pulling `ℳ` back
to `f ⁻¹ V` and then to `X'` is pulling it back along the projection `X' ⟶ X`: restriction to an
open is the pullback along its inclusion, and pullbacks compose. -/
public def pullbackRestrictStalkBaseChangeIso (M : X.Modules) :
    (Scheme.Modules.pullback (stalkBaseChangeRes f y hy)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M) ≅
      (Scheme.Modules.pullback (stalkBaseChangeι f y)).obj M :=
  (Scheme.Modules.pullback (stalkBaseChangeRes f y hy)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app M) ≪≫
    (Scheme.Modules.pullbackComp (stalkBaseChangeRes f y hy) (f ⁻¹ᵁ V).ι).app M ≪≫
      eqToIso (congrArg (fun φ : stalkBaseChange f y ⟶ X =>
        (Scheme.Modules.pullback φ).obj M) (stalkBaseChangeRes_comp_ι f y hy))

/-! ### Flat base change at a stalk, in the vanishing direction -/

/-- A subsingleton transports backwards along an isomorphism of modules, through the global
sections `H ᵖ` of a scheme. -/
private theorem subsingleton_rightDerived_evaluation_of_iso {Z : Scheme.{u}} {M N : Z.Modules}
    (e : M ≅ N) (p : ℕ)
    (h : Subsingleton (((_root_.SheafOfModules.evaluation.{u} Z.ringCatSheaf
      (op (⊤ : Z.Opens))).rightDerived p).obj N)) :
    Subsingleton (((_root_.SheafOfModules.evaluation.{u} Z.ringCatSheaf
      (op (⊤ : Z.Opens))).rightDerived p).obj M) :=
  subsingleton_of_iso (((_root_.SheafOfModules.evaluation.{u} Z.ringCatSheaf
    (op (⊤ : Z.Opens))).rightDerived p).mapIso e) h

/-- **The stalk of a higher direct image vanishes as soon as the cohomology of the base change
`X' = X ×_Y Spec 𝒪_{Y,y}` does.** For `f : X ⟶ Y` separated and quasi-compact and `ℳ` a
quasi-coherent `𝒪_X`-module, if `H ᵖ(X', q^* ℳ)` is zero — `q : X' ⟶ X` being the projection —
then so is the stalk `R ᵖ f_*(ℳ)_y`.

This is the vanishing half of [Stacks, Tag 02KH] part (1) along the flat morphism
`Spec 𝒪_{Y,y} ⟶ Y`, in degree `p`, which is the shape [Stacks, Tag 0D2M] consumes. The proof is
the chain of comparisons described in this file's implementation notes. Nothing here is asked of
`Y`: the affine open `V ∋ y` the chain runs through is produced inside the proof. -/
public theorem isZero_stalk_rightDerived_of_subsingleton_stalkBaseChange
    (M : X.Modules) [M.IsQuasicoherent] (p : ℕ)
    (h : Subsingleton (((_root_.SheafOfModules.evaluation.{u} (stalkBaseChange f y).ringCatSheaf
        (op (⊤ : (stalkBaseChange f y).Opens))).rightDerived p).obj
      ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj M))) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerived p).obj M).presheaf.stalk y) := by
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := y) (U := ⊤) (TopologicalSpace.Opens.mem_top y)
  have : IsAffine (V : Scheme.{u}) := hV
  have := flat_fromSpecStalkOfMem y hy
  set A := ((Scheme.Modules.pushforward f).rightDerived p).obj M with hA
  set q := V.fromSpecStalkOfMem y hy with hq
  set M' := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M with hM'
  set B := (Scheme.Modules.restrictFunctor V.ι).obj A with hB
  -- the module whose cohomology the hypothesis is about, read on `f ⁻¹ V`
  have s1 := subsingleton_rightDerived_evaluation_of_iso
      (pullbackRestrictStalkBaseChangeIso f y hy M) p h
  -- flat base change over the affine base `V`, at the cartesian square whose corner is `X'`
  obtain ⟨bc⟩ := AlgebraicGeometry.nonempty_cohomologyBaseChangeIso
    (q := q) (iX := f ∣_ V) (p := stalkBaseChangeRes f y hy)
    (kY := stalkBaseChangeStructure f y) (isPullback_stalkBaseChangeRes f y hy) M' p
  have s2 : Subsingleton ((baseRestrictScalars (f ∣_ V) ⋙ baseExtendScalars q).obj
      (((_root_.SheafOfModules.evaluation.{u} (f ⁻¹ᵁ V : Scheme.{u}).ringCatSheaf
        (op (⊤ : (f ⁻¹ᵁ V : Scheme.{u}).Opens))).rightDerived p).obj M')) :=
    subsingleton_of_iso bc s1
  -- [Stacks, Tag 01XK] over the affine base `V`, then [Stacks, Tag 01E5]
  have : A.IsQuasicoherent := by rw [hA]; infer_instance
  have s3 : Subsingleton ((baseExtendScalars q).obj ((moduleGlobalSections
      (V : Scheme.{u})).obj B)) :=
    subsingleton_of_iso ((baseExtendScalars q).mapIso
      (baseSectionsRightDerivedPushforwardIso (f ∣_ V) M' p ≪≫
        (moduleGlobalSections (V : Scheme.{u})).mapIso
          ((higherDirectImageRestrictIso f V p).app M))).symm s2
  -- the sections of the pullback over the affine pair `(V, Spec 𝒪_{Y,y})`
  have s4 : Subsingleton (ModuleCat.of Γ(Spec (Y.presheaf.stalk y), ⊤)
      Γ((Scheme.Modules.pullback q).obj B, ⊤)) :=
    subsingleton_of_iso (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso q B
      (isAffineOpen_top (V : Scheme.{u})) (isAffineOpen_top (Spec (Y.presheaf.stalk y)))
      (le_preimage_top q ⊤)).symm s3
  -- `Spec 𝒪_{Y,y} ⟶ Y` factors through `V`
  have s5 : Subsingleton ((moduleGlobalSections (Spec (Y.presheaf.stalk y))).obj
      ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj A)) :=
    subsingleton_of_iso ((moduleGlobalSections (Spec (Y.presheaf.stalk y))).mapIso
      ((Scheme.Modules.pullback q).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app A) ≪≫
        (Scheme.Modules.pullbackComp q V.ι).app A ≪≫
          eqToIso (congrArg (fun φ : Spec (Y.presheaf.stalk y) ⟶ Y =>
            (Scheme.Modules.pullback φ).obj A)
            (Scheme.Opens.fromSpecStalkOfMem_ι V y hy)))).symm s4
  -- the sections of the pullback to `Spec 𝒪_{Y,y}` are the stalk
  have s6 : Subsingleton Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj A,
      (⊤ : (Spec (Y.presheaf.stalk y)).Opens)) := s5
  obtain ⟨e, -⟩ := AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv A y hV hy
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr e.symm.injective.subsingleton

/-! ### The vanishing clause of Tag 0D2M -/

/-- **The vanishing clause of [Stacks, Tag 0D2M].**

Let `f : X ⟶ Y` be proper with `Y` locally Noetherian, let `ℒ` be an invertible `𝒪_X`-module and
`ℱ` a coherent `𝒪_X`-module, and let `y ∈ Y` be a point at which `ℒ_y` is ample on the fibre
`X_y`. Then there is a `d₀` such that for every `d ≥ d₀` and every `p > 0` the stalk

  `R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)_y`

is zero.

This is the first of the tag's two displays. It is
`Stacks.FormalFunctions.exists_subsingleton_and_surjective_twistModule_stalkBaseChange` — both
clauses on the base change `X' = X ×_Y Spec 𝒪_{Y,y}`, under this very ampleness hypothesis —
followed by `isZero_stalk_rightDerived_of_subsingleton_stalkBaseChange`, the twist on `X'` being
identified with the pullback of the twist by [Stacks, Tag 0EGK]'s
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistModuleIso`.

The tag's other clause is a surjectivity of a named comparison map and is not proved here; it is
`Stacks.FormalFunctions.surjective_fiberSectionsStalkHom` of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistStalkSurjective.lean`, where the two
are put together as
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`. -/
public theorem exists_isZero_stalk_rightDerived_twistModule (f : X ⟶ Y) [IsProper f]
    [AlgebraicGeometry.IsLocallyNoetherian Y] (y : Y) (F L : X.Modules)
    [IsInvertibleModule X L] [F.IsCoherent]
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      IsZero ((((Scheme.Modules.pushforward f).rightDerived p).obj
        (twistModule X L F d)).presheaf.stalk y) := by
  obtain ⟨d₀, hd₀⟩ := exists_subsingleton_and_surjective_twistModule_stalkBaseChange f y F L hL
  refine ⟨d₀, fun d hd p hp => ?_⟩
  have : (twistModule X L F d).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
      (tensorPowModule X L d)
  have : (twistModule X L F d).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent (twistModule X L F d)
  refine isZero_stalk_rightDerived_of_subsingleton_stalkBaseChange f y
    (twistModule X L F d) p ?_
  exact subsingleton_rightDerived_evaluation_of_iso
    (pullbackTwistModuleIso (stalkBaseChangeι f y) L F d) p ((hd₀ d hd).1 p hp)

end Stacks.FormalFunctions

end
