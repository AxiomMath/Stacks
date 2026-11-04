module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerPairForms

/-!
# The crystals clause of [Stacks, Lemma 60.17.5, Tag 07L5]

In the situation of [Stacks, Section 60.17, Tag 07J7] — `X = Spec(C)` and `S = Spec(A)` affine,
`p` nilpotent on `C` — let `A → P' → C` be ring maps with `A → P'` smooth and `P' → C`
surjective, and `D'` the `p`-adic completion of `D_{P', γ}(J')`.  [Stacks, Lemma 60.17.5,
Tag 07L5] chooses a polynomial presentation `P = A[x_i] → P' → C`, divided power maps
`a : D → D'`, `b : D' → D` with `a ∘ b = id`, deduces an equivalence between the pairs over `D`
and over `D'`, and ends:

> In particular, the equivalence of Proposition 60.17.4 also holds for the corresponding functor
> towards pairs over `D'`.

The functor of [Stacks, Proposition 60.17.4, Tag 07JH] is `...SmallSite.crystalPairFunctor`, for
the presentation of the system of thickenings of [Stacks, Tag 07JN] given by the instance
`...SmallSite.WholeSpacePresentation S hp`; its pairs take their connections in
`Ω̂_{E/A,δ}`, those of the lemma in the completed one-forms of `D`, and
`Crystalline.tensorPowerPairFormsEquivalence` identifies the two.

## Main results

* `...SmallSite.crystalRetractPairFunctor` — **the functor towards the pairs over `D'`**: the
  functor of [Stacks, Tag 07JG] followed by the base change `F` along `a`.  On a crystal `ℱ` its
  module is `D' ⊗̂_D M`, `M = lim_e Γ((X, T_e, δ̄), ℱ)`
  (`...SmallSite.crystalRetractPairFunctor_obj_carrier`), with the base-changed connection
  (`...SmallSite.crystalRetractPairFunctor_obj_nabla`).
* `...SmallSite.crystalRetractPairFunctor_isEquivalence` — it is an equivalence, from
  [Stacks, Tag 07JH] and the second assertion of [Stacks, Tag 07L5].
* `...SmallSite.exists_presentation_retract_crystalPairEquivalence` — **[Stacks, Lemma 60.17.5,
  Tag 07L5]** in this situation: both assertions, for a presentation of the system, and the last
  sentence.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]
  [Fintype (wholeSpaceIndex S hp)] [DecidableEq (wholeSpaceIndex S hp)]

/-- **The pairs of [Stacks, Tag 07JG] are pairs over the completed envelope**: the identity,
reading a pair of `...SmallSite.crystalPairFunctor` with the spelling of
`Crystalline.tensorPowerPairFormsEquivalence`. -/
def pairCatToTensorPowerPairs : PairCat hp ⥤ Pair.{u, u, u, u} (affineSituation S hp).p
    (envelopeCompletion (presentationEnvelope (affineSituation S hp)
      (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0))
      (affineSituation S hp).p
      (tensorPowerPresentationEnvelope_prime_nilpotent (affineSituation S hp)
        (wholeSpacePresentation S hp)))
    (completedTensorPowerDifferentials (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp))
    (fun x ↦ tensorPowerDerivation (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0 x) where
  obj P := P
  map f := f

/-- The inverse of `...SmallSite.pairCatToTensorPowerPairs`, also the identity. -/
def tensorPowerPairsToPairCat : Pair.{u, u, u, u} (affineSituation S hp).p
    (envelopeCompletion (presentationEnvelope (affineSituation S hp)
      (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0))
      (affineSituation S hp).p
      (tensorPowerPresentationEnvelope_prime_nilpotent (affineSituation S hp)
        (wholeSpacePresentation S hp)))
    (completedTensorPowerDifferentials (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (tensorPowerVariableDifferential (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp))
    (fun x ↦ tensorPowerDerivation (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0 x) ⥤ PairCat hp where
  obj P := P
  map f := f

/-- The identity is an equivalence between the two spellings of the pairs over `D`. -/
def pairCatTensorPowerPairsEquivalence := CategoryTheory.Equivalence.mk
  (pairCatToTensorPowerPairs hp) (tensorPowerPairsToPairCat hp) (Iso.refl _) (Iso.refl _)

/-- **The ring `D`**: the `p`-adically completed divided power envelope of the presentation
`A[x_{(0,i)}] → C` of the system. -/
abbrev systemEnvelopeCompletion : DividedPowerRing.{u} :=
  envelopeCompletion (presentationEnvelope (affineSituation S hp)
      (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0))
    (affineSituation S hp).p
    (tensorPowerPresentationEnvelope_prime_nilpotent (affineSituation S hp)
      (wholeSpacePresentation S hp))

/-- The coordinates of the completed envelope `D` of the presentation of the system. -/
abbrev systemEnvelopeCoordinates :=
  polynomialEnvelopeCoordinates (affineSituation S hp)
    (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (tensorPowerPresentation_surjective (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0)

variable (D' : DividedPowerRing.{u}) [Algebra ((affineSituation S hp).A : Type u) (D' : Type u)]
  (a : DPMorphism (systemEnvelopeCompletion hp).dividedPowers D'.dividedPowers)
  (b : DPMorphism D'.dividedPowers (systemEnvelopeCompletion hp).dividedPowers)
  (ha : ∀ c : ((affineSituation S hp).A : Type u),
    a (algebraMap ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp) c) =
      algebraMap ((affineSituation S hp).A : Type u) (D' : Type u) c)
  (hb : ∀ c : ((affineSituation S hp).A : Type u),
    b (algebraMap ((affineSituation S hp).A : Type u) (D' : Type u) c) =
      algebraMap ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp) c)
  (hab : ∀ x : (D' : Type u), a (b x) = x)
  (hρ : ∀ y : systemEnvelopeCompletion hp, b (a y) - y ∈ (systemEnvelopeCompletion hp).ideal)

/-- **The functor towards the pairs over `D'`** of the last sentence of
[Stacks, Lemma 60.17.5, Tag 07L5]: the functor of [Stacks, Tag 07JG]
(`...SmallSite.crystalPairFunctor`), read in the completed one-forms of `D`
(`Crystalline.tensorPowerPairFormsEquivalence`), followed by the base change `F` along
`a : D → D'` (`Crystalline.retractForwardFunctor`). -/
def crystalRetractPairFunctor : QuasiCoherentCrystal S ⥤
    RetractPair (systemEnvelopeCoordinates hp)
      (envelopeRetractData _ (affineSituation S hp).p _ D' a b ha hb hab hρ) :=
  crystalPairFunctor hp ⋙ pairCatToTensorPowerPairs hp ⋙
    (tensorPowerPairFormsEquivalence (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp)).functor ⋙
    retractForwardFunctor _ (envelopeRetractData _ (affineSituation S hp).p _ D' a b ha hb hab hρ)

/-- **[Stacks, Lemma 60.17.5, Tag 07L5], last sentence**: the equivalence of
[Stacks, Proposition 60.17.4, Tag 07JH] also holds for the corresponding functor towards the
pairs over `D'`. -/
theorem crystalRetractPairFunctor_isEquivalence :
    (crystalRetractPairFunctor hp D' a b ha hb hab hρ).IsEquivalence := by
  have := crystalPairFunctor_isEquivalence hp
  let E := (pairCatTensorPowerPairsEquivalence hp).trans
    ((tensorPowerPairFormsEquivalence (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp)).trans (retractPairEquivalence _
        (envelopeRetractData _ (affineSituation S hp).p _ D' a b ha hb hab hρ)))
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  exact Functor.isEquivalence_trans (crystalPairFunctor hp) E.functor

/-- **The pair over `D'` attached to a crystal**: the module of
`...SmallSite.crystalRetractPairFunctor` at `ℱ` is the completed base change `D' ⊗̂_D M` along
`a` of the module `M = lim_e Γ((X, T_e, δ̄), ℱ)` of the pair of [Stacks, Tag 07JG]. -/
theorem crystalRetractPairFunctor_obj_carrier (Fc : QuasiCoherentCrystal S) :
    letI : Algebra (systemEnvelopeCompletion hp : Type u) (D' : Type u) := a.toRingHom.toAlgebra
    ((crystalRetractPairFunctor hp D' a b ha hb hab hρ).obj Fc).carrier =
      CompletedConnection.baseChangeCarrier (affineSituation S hp).p
        (systemEnvelopeCompletion hp) (D' : Type u)
        ((pairCatToTensorPowerPairs hp).obj (crystalPair hp Fc)).carrier :=
  rfl

/-- **The connection of the pair over `D'` attached to a crystal** is the base change along `a`
of the connection of the pair of [Stacks, Tag 07JG], read in the completed one-forms of `D` by
`Crystalline.tensorPowerOneFormsEquiv`. -/
theorem crystalRetractPairFunctor_obj_nabla (Fc : QuasiCoherentCrystal S) :
    ((crystalRetractPairFunctor hp D' a b ha hb hab hρ).obj Fc).nabla =
      (retractForward _ (envelopeRetractData _ (affineSituation S hp).p _ D' a b ha hb hab hρ)
        ((tensorPowerPairFormsEquivalence (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp)).functor.obj
          ((pairCatToTensorPowerPairs hp).obj (crystalPair hp Fc)))).nabla :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **[Stacks, Lemma 60.17.5, Tag 07L5], for the crystals of [Stacks, Tag 07JH].**  In the
situation of [Stacks, Section 60.17, Tag 07J7], `X = Spec(C)` and `S = Spec(A)` affine with `p`
nilpotent on `C`, let `A → P' → C` be ring maps with `A → P'` smooth and `P' → C` surjective,
and let `D'` be the `p`-adic completion of `D_{P', γ}(J')`.  Then

* **(first assertion)** there are a choice of the data `A → P → C` — a polynomial algebra
  `P = A[x_i]` in finitely many variables with a surjection `q : P ↠ P'`, the presentation of the
  system of [Stacks, Tag 07JN] being the composite `P → P' → C` — and homomorphisms of divided
  power `A`-algebras `a : D → D'`, `b : D' → D` compatible with the augmentations to `C`, with
  `a ∘ b = id_{D'}`;
* **(second assertion)** these maps induce an equivalence of categories `e` between the pairs over
  `D` and the pairs over `D'` satisfying (07JB)–(07JE), with functor the base change `F` along `a`
  and quasi-inverse the base change `G` along `b`;
* **(last sentence)** the equivalence of [Stacks, Proposition 60.17.4, Tag 07JH] also holds for
  the corresponding functor towards the pairs over `D'`: the functor
  `...SmallSite.crystalRetractPairFunctor` from the crystals in quasi-coherent
  `𝒪_{X/S}`-modules on `Cris(X/S)`, which is the functor of [Stacks, Tag 07JG]
  (`...SmallSite.crystalPairFunctor`, for the presentation `P → C`) followed by `F`, is an
  equivalence of categories. -/
@[stacks 07L5 "all three parts in the situation of 07J7 (X = Spec C, S = Spec A affine, p \
nilpotent on C), for A -> P' smooth and P' -> C surjective: a polynomial presentation \
q : A[x_i] ->> P' in finitely many variables, the system of 07JN being presented by \
A[x_(0,i)] -> P' -> C (WholeSpacePresentation S hp), and divided power A-algebra maps a : D -> D', \
b : D' -> D compatible with the augmentations, with a . b = id; an equivalence between the pairs \
over D and the pairs over D' satisfying 07JB-07JE whose functor is the base change along a and \
whose inverse is the base change along b; and the last sentence: the functor of 07JG for that \
presentation, from the crystals in quasi-coherent O_{X/S}-modules on Cris(X/S), followed by the \
base change along a towards the pairs over D' (crystalRetractPairFunctor), is an equivalence"]
theorem exists_presentation_retract_crystalPairEquivalence (P' : Type u) [CommRing P']
    [Algebra ((affineSituation S hp).A : Type u) P']
    [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
    (f' : P' →ₐ[(affineSituation S hp).A] (affineSituation S hp).C)
    (hf' : Function.Surjective f') :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (q : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A] P')
      (hq : Function.Surjective q),
      letI : WholeSpacePresentation S hp := ⟨ι, f'.comp q, hf'.comp hq⟩
      ∃ (a : DPMorphism (systemEnvelopeCompletion hp).dividedPowers
          (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers)
        (b : DPMorphism
          (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
          (systemEnvelopeCompletion hp).dividedPowers)
        (ha : ∀ c : ((affineSituation S hp).A : Type u),
          a (algebraMap ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp) c) =
            algebraMap ((affineSituation S hp).A : Type u)
              (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u) c)
        (hb : ∀ c : ((affineSituation S hp).A : Type u),
          b (algebraMap ((affineSituation S hp).A : Type u)
              (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u) c) =
            algebraMap ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp) c)
        (hab : ∀ x, a (b x) = x)
        (hρ : ∀ y, b (a y) - y ∈ (systemEnvelopeCompletion hp).ideal),
        a.comp b = DPMorphism.id _ ∧
        (completedEnvelopeAugmentation (affineSituation S hp) f' hf').comp a.toRingHom =
          completedEnvelopeAugmentation (affineSituation S hp)
            (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
            (tensorPowerPresentation_surjective (affineSituation S hp)
              (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) 0) ∧
        (completedEnvelopeAugmentation (affineSituation S hp)
            (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
            (tensorPowerPresentation_surjective (affineSituation S hp)
              (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp) 0)).comp
            b.toRingHom =
          completedEnvelopeAugmentation (affineSituation S hp) f' hf' ∧
        ∃ e : Pair.{u, u, u, u} (affineSituation S hp).p _ (systemEnvelopeCoordinates hp).forms
            (systemEnvelopeCoordinates hp).dx (systemEnvelopeCoordinates hp).diff ≌
          RetractPair (systemEnvelopeCoordinates hp)
            (envelopeRetractData _ (affineSituation S hp).p _
              (completedEnvelopeOfPresentation (affineSituation S hp) f' hf') a b ha hb hab hρ),
          e.functor = retractForwardFunctor _ (envelopeRetractData _ (affineSituation S hp).p _
            (completedEnvelopeOfPresentation (affineSituation S hp) f' hf') a b ha hb hab hρ) ∧
          e.inverse = retractBackFunctor _ (envelopeRetractData _ (affineSituation S hp).p _
            (completedEnvelopeOfPresentation (affineSituation S hp) f' hf') a b ha hb hab hρ) ∧
          crystalRetractPairFunctor hp _ a b ha hb hab hρ =
            crystalPairFunctor hp ⋙ pairCatToTensorPowerPairs hp ⋙
              (tensorPowerPairFormsEquivalence (affineSituation S hp)
                (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp)).functor ⋙
              e.functor ∧
          (crystalRetractPairFunctor hp _ a b ha hb hab hρ).IsEquivalence := by
  have hex := @exists_mvPolynomial_surjection_of_smooth
    ((affineSituation S hp).A : Type u) _ P' _ _ ‹_›
  refine hex.elim fun m hm ↦ hm.elim fun q₀ hq₀ ↦ ?_
  let q : MvPolynomial (ULift.{u} (Fin m)) (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
      P' := q₀.comp (MvPolynomial.rename ULift.down)
  have hq : Function.Surjective q :=
    hq₀.comp (MvPolynomial.rename_surjective _ ULift.down_surjective)
  refine ⟨ULift.{u} (Fin m), inferInstance, inferInstance, q, hq, ?_⟩
  have hq' : Function.Surjective (q.comp (MvPolynomial.rename
      (Prod.snd : Fin 1 × ULift.{u} (Fin m) → ULift.{u} (Fin m)))) :=
    hq.comp (MvPolynomial.rename_surjective _ Prod.snd_surjective)
  let : WholeSpacePresentation S hp := ⟨_, f'.comp q, hf'.comp hq⟩
  let : Fintype (wholeSpaceIndex S hp) := inferInstanceAs (Fintype (ULift.{u} (Fin m)))
  let : DecidableEq (wholeSpaceIndex S hp) := inferInstanceAs (DecidableEq (ULift.{u} (Fin m)))
  have hret := exists_retract_of_comp_eq (affineSituation S hp) P' f' hf' _ hq'
    (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
    (MvPolynomial.algHom_ext fun _ ↦ rfl)
    (tensorPowerPresentation_surjective (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0)
  refine hret.elim fun a h ↦ h.elim fun b ⟨ha, hb, hab, haug, hbaug⟩ ↦ ?_
  have hab' : ∀ x, a (b x) = x := fun x ↦ congrArg (fun r : DPMorphism _ _ ↦ r x) hab
  have hρ : ∀ y, b (a y) - y ∈ (systemEnvelopeCompletion hp).ideal := fun y ↦
    sub_mem_completionIdeal_of_augmentation_eq _ _ _
      ((DFunLike.congr_fun hbaug (a y)).trans (DFunLike.congr_fun haug y))
  exact ⟨a, b, ha, hb, hab', hρ, hab, haug, hbaug, retractPairEquivalence _ _, rfl, rfl, rfl,
    crystalRetractPairFunctor_isEquivalence hp _ a b ha hb hab' hρ⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
