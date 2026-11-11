module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionCoordinateDual
public import StacksFrontier.AlgebraicGeometry.Crystalline.PairFormsTransportCoordinateDual
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerPairForms

/-!
# [Stacks, Remark 60.17.6, Tag 07L6]: crystals and the pairs over a strong lifting presentation

In the situation of [Stacks, Section 60.17, Tag 07J7] — `X = Spec(C)` and `S = Spec(A)` affine,
`p` nilpotent on `C` — [Stacks, Remark 60.17.6, Tag 07L6] says:

> The equivalence of Proposition 60.17.4 holds if we start with a surjection `P → C` where `P/A`
> satisfies the strong lifting property of Algebra, Lemma 10.137.17.  To prove this we can argue
> as in the proof of Lemma 60.17.5.

This module carries that argument out.  Let `f : P ↠ C` be a surjection of `A`-algebras with `P/A`
having the strong lifting property of [Stacks, Tag 07K4] (`Algebra.HasStrongLiftingProperty`), and
let `D_P` be the `p`-adic completion of `D_{P, γ}(ker f)`.

* As in the proof of [Stacks, Tag 07L5], choose a polynomial algebra mapping onto `P`, here
  `A[x_t : t ∈ P] → P`, `x_t ↦ t`, and present the system of thickenings of [Stacks, Tag 07JN] by
  the composite `A[x_t] → P → C`; call `D` its completed envelope.  Since `P` need not be of finite
  type, there are in general infinitely many variables.
* The lifting argument of the proof of [Stacks, Tag 07L5] uses only the strong lifting property
  of `P/A`: it gives divided power `A`-algebra maps `a : D → D_P`, `b : D_P → D` compatible with
  the augmentations to `C`, with `a ∘ b = id_{D_P}`
  (`Crystalline.exists_retract_of_comp_eq_of_hasStrongLiftingProperty`).
* The pairs over `D` are those of [Stacks, Tag 07JH] (`...SmallSite.crystalPairFunctor`, whose
  equivalence is `...SmallSite.crystalPairFunctor_isEquivalence`), read in the completed one-forms
  of `D` (`...SmallSite.tensorPowerPairsDualEquivalence`); the pairs over `D_P` satisfying
  (07JB)–(07JE) are `Crystalline.CoordinateDualRetractPair`, the condition (07JE) being read on the
  base change along `b`, as the proof of [Stacks, Tag 07L5] defines it over a ring with no
  coordinates of its own; and the base changes along `a` and `b` are quasi-inverse equivalences
  between them (`Crystalline.CoordinateDual.retractPairEquivalence`), for any family of
  coordinates.
* Consequently the functor from crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the
  pairs over `D_P` — the functor of [Stacks, Tag 07JG] followed by the base change along `a` — is an
  equivalence:
  `...SmallSite.exists_presentation_retract_crystalPairEquivalence_of_hasStrongLiftingProperty`.

## References

* [Stacks Project, Remark 60.17.6, Tag 07L6](https://stacks.math.columbia.edu/tag/07L6)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The ring `D` of the system**: the `p`-adically completed divided power envelope of the
presentation `A[x_{(0,i)}] → C` of the system, for any family of variables. -/
abbrev wholeSpaceEnvelopeCompletion : DividedPowerRing.{u} :=
  envelopeCompletion (presentationEnvelope (affineSituation S hp)
      (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0))
    (affineSituation S hp).p
    (tensorPowerPresentationEnvelope_prime_nilpotent (affineSituation S hp)
      (wholeSpacePresentation S hp))

variable [DecidableEq (wholeSpaceIndex S hp)]

/-- **The topological coordinates of `D`**: its completed forms, the coordinates `x_{(0,i)}` and
the coordinate functionals dual to their differentials. -/
abbrev wholeSpaceCoordinateDualData :
    CompletedCoordinateDualData (affineSituation S hp).p (wholeSpaceEnvelopeCompletion hp) :=
  envelopeCompletionCoordinateDualData _ (affineSituation S hp).p _

/-- **The pairs of [Stacks, Tag 07JG] are pairs over the completed envelope**: the identity,
reading a pair of `...SmallSite.crystalPairFunctor` with the spelling of
`Crystalline.tensorPowerOneFormsEquivForms`. -/
def pairCatToEnvelopePairs : PairCat hp ⥤ Pair.{u, u, u, u} (affineSituation S hp).p
    (wholeSpaceEnvelopeCompletion hp)
    (completedTensorPowerDifferentials (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp))
    (fun x ↦ tensorPowerDerivation (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0 x) where
  obj P := P
  map f := f

/-- The inverse of `...SmallSite.pairCatToEnvelopePairs`, also the identity. -/
def envelopePairsToPairCat : Pair.{u, u, u, u} (affineSituation S hp).p
    (wholeSpaceEnvelopeCompletion hp)
    (completedTensorPowerDifferentials (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp))
    (fun x ↦ tensorPowerDerivation (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0 x) ⥤ PairCat hp where
  obj P := P
  map f := f

/-- The identity is an equivalence between the two spellings of the pairs over `D`. -/
def pairCatEnvelopePairsEquivalence := CategoryTheory.Equivalence.mk
  (pairCatToEnvelopePairs hp) (envelopePairsToPairCat hp) (Iso.refl _) (Iso.refl _)

/-- The coordinate functionals of `Ω̂_{E/A,δ}` read off those of `Ω̂¹_D`, reindexed. -/
def tensorPowerFormsCoordFun (i : wholeSpaceIndex S hp) :
    completedTensorPowerDifferentials (affineSituation S hp) (wholeSpacePresentation S hp) 0 →ₗ[
      (wholeSpaceEnvelopeCompletion hp : Type u)] (wholeSpaceEnvelopeCompletion hp : Type u) :=
  ((wholeSpaceCoordinateDualData hp).coordFun
      ((Equiv.uniqueProd (wholeSpaceIndex S hp) (Fin 1)).symm i)).comp
    (tensorPowerOneFormsEquivForms (affineSituation S hp) (wholeSpacePresentation S hp)).toLinearMap

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The coordinate functionals of `Ω̂_{E/A,δ}` are dual to the `d x_i`. -/
theorem isCoordinateDual_tensorPowerFormsCoordFun :
    IsCoordinateDual (tensorPowerVariableDifferential (affineSituation S hp)
      (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp))
      (tensorPowerFormsCoordFun hp) := by
  have hc := (wholeSpaceCoordinateDualData hp).isCoordinateDual
  have hv := tensorPowerOneFormsEquivForms_variableDifferential (affineSituation S hp)
    (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp)
  refine ⟨fun i ↦ ?_, fun {i j} hij ↦ ?_⟩
  · change (wholeSpaceCoordinateDualData hp).coordFun
      ((Equiv.uniqueProd (wholeSpaceIndex S hp) (Fin 1)).symm i)
      (tensorPowerOneFormsEquivForms (affineSituation S hp) (wholeSpacePresentation S hp)
        (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) i)) = 1
    rw [hv]
    exact hc.self _
  · change (wholeSpaceCoordinateDualData hp).coordFun
      ((Equiv.uniqueProd (wholeSpaceIndex S hp) (Fin 1)).symm j)
      (tensorPowerOneFormsEquivForms (affineSituation S hp) (wholeSpacePresentation S hp)
        (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) i)) = 0
    rw [hv]
    exact hc.of_ne fun h ↦ hij ((Equiv.uniqueProd (wholeSpaceIndex S hp) (Fin 1)).symm.injective h)

/-- **The pairs over `D` for the two spellings of `Ω_D` are the same**, for any family of
variables: the pairs of [Stacks, Tag 07JG], with values in `M ⊗̂ Ω̂_{E/A,δ}` and coordinates the
`d x_i`, and the pairs with values in `M ⊗̂ Ω̂¹_{D/A,γ̂}` and coordinates the `d x_{(0,i)}`. -/
def tensorPowerPairsDualEquivalence :
    Pair.{u, u, u, u} (affineSituation S hp).p (wholeSpaceEnvelopeCompletion hp)
        (completedTensorPowerDifferentials (affineSituation S hp) (wholeSpacePresentation S hp) 0)
        (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp))
        (fun x ↦ tensorPowerDerivation (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) 0 x) ≌
      Pair.{u, u, u, u} (affineSituation S hp).p (wholeSpaceEnvelopeCompletion hp)
        (wholeSpaceCoordinateDualData hp).forms (wholeSpaceCoordinateDualData hp).dx
        (wholeSpaceCoordinateDualData hp).diff :=
  Pair.formsTransportEquivalenceOfDual (affineSituation S hp).p
    (tensorPowerOneFormsEquivForms (affineSituation S hp) (wholeSpacePresentation S hp))
    (tensorPowerOneFormsEquivForms_derivation (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp))
    (Equiv.uniqueProd (wholeSpaceIndex S hp) (Fin 1)).symm
    (tensorPowerOneFormsEquivForms_variableDifferential (affineSituation S hp)
      (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp))
    (wholeSpaceCoordinateDualData hp).isCoordinateDual
    (fun x ↦ (LinearEquiv.symm_apply_eq _).mpr
      (tensorPowerOneFormsEquivForms_derivation (affineSituation S hp)
        (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) x).symm)
    (fun j ↦ (LinearEquiv.symm_apply_eq _).mpr
      ((tensorPowerOneFormsEquivForms_variableDifferential (affineSituation S hp)
        (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) _).trans
        (by rw [Equiv.apply_symm_apply]; rfl)).symm)
    (isCoordinateDual_tensorPowerFormsCoordFun hp)

variable (D' : DividedPowerRing.{u}) [Algebra ((affineSituation S hp).A : Type u) (D' : Type u)]
  (a : DPMorphism (wholeSpaceEnvelopeCompletion hp).dividedPowers D'.dividedPowers)
  (b : DPMorphism D'.dividedPowers (wholeSpaceEnvelopeCompletion hp).dividedPowers)
  (ha : ∀ c : ((affineSituation S hp).A : Type u),
    a (algebraMap ((affineSituation S hp).A : Type u) (wholeSpaceEnvelopeCompletion hp) c) =
      algebraMap ((affineSituation S hp).A : Type u) (D' : Type u) c)
  (hb : ∀ c : ((affineSituation S hp).A : Type u),
    b (algebraMap ((affineSituation S hp).A : Type u) (D' : Type u) c) =
      algebraMap ((affineSituation S hp).A : Type u) (wholeSpaceEnvelopeCompletion hp) c)
  (hab : ∀ x : (D' : Type u), a (b x) = x)
  (hρ : ∀ y : wholeSpaceEnvelopeCompletion hp,
    b (a y) - y ∈ (wholeSpaceEnvelopeCompletion hp).ideal)

/-- **The retract data of `a : D → D'`, `b : D' → D`** over the topological coordinates of the
completed envelope `D` of the system. -/
abbrev wholeSpaceDualRetractData :
    CoordinateDualRetractData (affineSituation S hp).p (wholeSpaceEnvelopeCompletion hp)
      (wholeSpaceCoordinateDualData hp) :=
  envelopeCompletionDualRetractData _ (affineSituation S hp).p _ D' a b ha hb hab hρ

/-- **The functor from crystals to the pairs over `D'`**: the functor of [Stacks, Tag 07JG]
(`...SmallSite.crystalPairFunctor`), read in the completed one-forms of `D`, followed by the
base change `F` along `a : D → D'` (`Crystalline.CoordinateDual.retractForwardFunctor`). -/
def crystalDualRetractPairFunctor : QuasiCoherentCrystal S ⥤
    CoordinateDualRetractPair (wholeSpaceCoordinateDualData hp)
      (wholeSpaceDualRetractData hp D' a b ha hb hab hρ) :=
  crystalPairFunctor hp ⋙ pairCatToEnvelopePairs hp ⋙ (tensorPowerPairsDualEquivalence hp).functor ⋙
    CoordinateDual.retractForwardFunctor _ (wholeSpaceDualRetractData hp D' a b ha hb hab hρ)

/-- **The functor from crystals to the pairs over `D'` is an equivalence**, from
[Stacks, Tag 07JH] and the equivalence of pairs along the retract, for any family of
variables. -/
theorem crystalDualRetractPairFunctor_isEquivalence :
    (crystalDualRetractPairFunctor hp D' a b ha hb hab hρ).IsEquivalence := by
  have := crystalPairFunctor_isEquivalence hp
  let E := (pairCatEnvelopePairsEquivalence hp).trans
    ((tensorPowerPairsDualEquivalence hp).trans (CoordinateDual.retractPairEquivalence _
      (wholeSpaceDualRetractData hp D' a b ha hb hab hρ)))
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  exact Functor.isEquivalence_trans (crystalPairFunctor hp) E.functor

end Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **[Stacks, Remark 60.17.6, Tag 07L6]: the equivalence of [Stacks, Proposition 60.17.4,
Tag 07JH] holds if we start with a surjection `P → C` where `P/A` satisfies the strong lifting
property of [Stacks, Tag 07K4].**  In the situation of [Stacks, Section 60.17, Tag 07J7],
`X = Spec(C)` and `S = Spec(A)` affine with `p` nilpotent on `C`, let `f : P ↠ C` be a surjection of
`A`-algebras such that `P/A` has the strong lifting property (`Algebra.HasStrongLiftingProperty`),
and let `D_P` be the `p`-adic completion of `D_{P, γ}(ker f)`
(`Crystalline.completedEnvelopeOfPresentation`).  The source only indicates the proof ("argue as
in the proof of Lemma 07L5"; details are not written out there); this theorem carries it out.
Arguing as in the proof of [Stacks, Tag 07L5]:

* there are a polynomial algebra `A[x_i]` with a surjection `q : A[x_i] ↠ P`, the system of
  [Stacks, Tag 07JN] being presented by `A[x_{(0,i)}] → P → C` (`WholeSpacePresentation S hp`), and
  homomorphisms of divided power `A`-algebras `a : D → D_P`, `b : D_P → D` compatible with the
  augmentations to `C`, with `a ∘ b = id_{D_P}`, `D` being the completed envelope of the system;
* the base changes along `a` and `b` are quasi-inverse equivalences between the pairs `(M, ∇)` over
  `D` and the pairs `(M', ∇')` over `D_P` satisfying (07JB)–(07JE)
  (`Crystalline.CoordinateDualRetractPair`: `p`-adically complete, a completed connection with
  values in the completed one-forms of `D_P` whose curvature vanishes, and (07JE) read on the base
  change along `b`, as the proof of [Stacks, Tag 07L5] defines it);
* and the functor from the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the
  pairs over `D_P` — the functor of [Stacks, Tag 07JG] followed by the base change along `a`
  (`...SmallSite.crystalDualRetractPairFunctor`) — is an equivalence of categories. -/
@[stacks 07L6 "in the situation of 07J7 (X = Spec C, S = Spec A affine, p nilpotent on C), for a \
surjection f : P ->> C with P/A having the strong lifting property of 07K4 (Algebra.\
HasStrongLiftingProperty) and D_P the p-adic completion of the divided power envelope of ker f: \
arguing as in 07L5, there are a polynomial presentation q : A[x_i] ->> P (in general in infinitely \
many variables), the system of 07JN being presented by A[x_(0,i)] -> P -> C, and divided power \
A-algebra maps a : D -> D_P, b : D_P -> D compatible with the augmentations, with a . b = id; the \
base changes along a and b are inverse equivalences between the pairs over D and the pairs over \
D_P satisfying 07JB-07JE (CoordinateDualRetractPair: p-adically complete, a completed connection \
over the completed forms of D_P with vanishing curvature, and 07JE read on the base change along \
b, as the proof of 07L5 defines it); and the functor from the crystals in quasi-coherent \
O_{X/S}-modules on Cris(X/S) to the pairs over D_P, the functor of 07JG followed by the base \
change along a (crystalDualRetractPairFunctor), is an equivalence of categories"]
theorem exists_presentation_retract_crystalPairEquivalence_of_hasStrongLiftingProperty
    (P : Type u) [CommRing P] [Algebra ((affineSituation S hp).A : Type u) P]
    (hP : Algebra.HasStrongLiftingProperty ((affineSituation S hp).A : Type u) P)
    (f : P →ₐ[(affineSituation S hp).A] (affineSituation S hp).C) (hf : Function.Surjective f) :
    ∃ (ι : Type u) (_ : DecidableEq ι)
      (q : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A] P)
      (hq : Function.Surjective q),
      letI : WholeSpacePresentation S hp := ⟨ι, f.comp q, hf.comp hq⟩
      ∃ (a : DPMorphism (wholeSpaceEnvelopeCompletion hp).dividedPowers
          (completedEnvelopeOfPresentation (affineSituation S hp) f hf).dividedPowers)
        (b : DPMorphism
          (completedEnvelopeOfPresentation (affineSituation S hp) f hf).dividedPowers
          (wholeSpaceEnvelopeCompletion hp).dividedPowers)
        (ha : ∀ c : ((affineSituation S hp).A : Type u),
          a (algebraMap ((affineSituation S hp).A : Type u) (wholeSpaceEnvelopeCompletion hp) c) =
            algebraMap ((affineSituation S hp).A : Type u)
              (completedEnvelopeOfPresentation (affineSituation S hp) f hf : Type u) c)
        (hb : ∀ c : ((affineSituation S hp).A : Type u),
          b (algebraMap ((affineSituation S hp).A : Type u)
              (completedEnvelopeOfPresentation (affineSituation S hp) f hf : Type u) c) =
            algebraMap ((affineSituation S hp).A : Type u) (wholeSpaceEnvelopeCompletion hp) c)
        (hab : ∀ x, a (b x) = x)
        (hρ : ∀ y, b (a y) - y ∈ (wholeSpaceEnvelopeCompletion hp).ideal),
        a.comp b = DPMorphism.id _ ∧
        (completedEnvelopeAugmentation (affineSituation S hp) f hf).comp a.toRingHom =
          completedEnvelopeAugmentation (affineSituation S hp)
            (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
            (tensorPowerPresentation_surjective (affineSituation S hp)
              (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) 0) ∧
        (completedEnvelopeAugmentation (affineSituation S hp)
            (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
            (tensorPowerPresentation_surjective (affineSituation S hp)
              (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) 0)).comp
            b.toRingHom =
          completedEnvelopeAugmentation (affineSituation S hp) f hf ∧
        ∃ e : Pair.{u, u, u, u} (affineSituation S hp).p (wholeSpaceEnvelopeCompletion hp)
            (wholeSpaceCoordinateDualData hp).forms (wholeSpaceCoordinateDualData hp).dx
            (wholeSpaceCoordinateDualData hp).diff ≌
          CoordinateDualRetractPair (wholeSpaceCoordinateDualData hp)
            (wholeSpaceDualRetractData hp
              (completedEnvelopeOfPresentation (affineSituation S hp) f hf) a b ha hb hab hρ),
          e.functor = CoordinateDual.retractForwardFunctor _ (wholeSpaceDualRetractData hp
            (completedEnvelopeOfPresentation (affineSituation S hp) f hf) a b ha hb hab hρ) ∧
          e.inverse = CoordinateDual.retractBackFunctor _ (wholeSpaceDualRetractData hp
            (completedEnvelopeOfPresentation (affineSituation S hp) f hf) a b ha hb hab hρ) ∧
          crystalDualRetractPairFunctor hp _ a b ha hb hab hρ =
            crystalPairFunctor hp ⋙ pairCatToEnvelopePairs hp ⋙
              (tensorPowerPairsDualEquivalence hp).functor ⋙ e.functor ∧
          (crystalDualRetractPairFunctor hp _ a b ha hb hab hρ).IsEquivalence := by
  classical
  let q : MvPolynomial P (affineSituation S hp).A →ₐ[(affineSituation S hp).A] P :=
    MvPolynomial.aeval id
  have hq : Function.Surjective q := fun x ↦ ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ _⟩
  refine ⟨P, inferInstance, q, hq, ?_⟩
  have hq' : Function.Surjective (q.comp (MvPolynomial.rename
      (Prod.snd : Fin 1 × P → P))) :=
    hq.comp (MvPolynomial.rename_surjective _ Prod.snd_surjective)
  let : WholeSpacePresentation S hp := ⟨_, f.comp q, hf.comp hq⟩
  let : DecidableEq (wholeSpaceIndex S hp) := inferInstanceAs (DecidableEq P)
  have hret := exists_retract_of_comp_eq_of_hasStrongLiftingProperty (affineSituation S hp) P hP
    f hf _ hq' (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (MvPolynomial.algHom_ext fun _ ↦ rfl)
    (tensorPowerPresentation_surjective (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0)
  refine hret.elim fun a h ↦ h.elim fun b ⟨ha, hb, hab, haug, hbaug⟩ ↦ ?_
  have hab' : ∀ x, a (b x) = x := fun x ↦ congrArg (fun r : DPMorphism _ _ ↦ r x) hab
  have hρ : ∀ y, b (a y) - y ∈ (wholeSpaceEnvelopeCompletion hp).ideal := fun y ↦
    sub_mem_completionIdeal_of_augmentation_eq _ _ _
      ((DFunLike.congr_fun hbaug (a y)).trans (DFunLike.congr_fun haug y))
  exact ⟨a, b, ha, hb, hab', hρ, hab, haug, hbaug, CoordinateDual.retractPairEquivalence _ _, rfl,
    rfl, rfl, crystalDualRetractPairFunctor_isEquivalence hp _ a b ha hb hab' hρ⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
