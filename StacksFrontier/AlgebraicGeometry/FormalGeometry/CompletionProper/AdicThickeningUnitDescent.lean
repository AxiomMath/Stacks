module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges

/-!
# Descending the unit of a system of algebra sheaves

`AlgebraicGeometry.exists_unit_of_adicThickeningFamily` descends a family of morphisms
`u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` on the adic thickenings to a morphism `𝒪_X ⟶ G` on `X`, but it carries
a binder `α`: the family has to be *handed to it* already assembled into a morphism

  `α : ⌃(𝒪_X) ⟶ ⌃(G)`

of inverse systems in the picture of `Stacks.Algebraization.completionFunctor`, where the terms are
the quotients `G / 𝓘 ⁿ⁺¹ G` on `X` and the transitions are the quotient projections. That binder
is what this file discharges. Nothing here touches a tensor product or a multiplication: the unit
of an algebra sheaf is a morphism of modules, and so is everything below.

## The translation

The assembly has a degreewise half and a compatibility half. The degreewise half is
`AlgebraicGeometry.adicThickeningCompletionUnitHomEquiv`, which is available: it identifies the
hom-set `⌃(𝒪_X)ₙ ⟶ ⌃(G)ₙ` of the first picture with `𝒪_{Xₙ} ⟶ G|_{Xₙ}`. The compatibility half is
the naturality of `α`, and translating it is what
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso_projection` — the normalization of the
unwinding, which says that the projection `G ⟶ ⌃(G)ₙ` followed by the identification
`⌃(G)ₙ ≅ (vₙ)_* (G|_{Xₙ})` is the unit of `vₙ^* ⊣ (vₙ)_*` — is for. Two steps:

* `AlgebraicGeometry.adicThickeningPushforwardTransition` — the transition of the second picture
  *pushed forward to `X`*, `(vₙ₊₁)_* (G|_{Xₙ₊₁}) ⟶ (vₙ)_* (G|_{Xₙ})`. It is defined as the
  transition of the first picture conjugated by the unwinding, and
  `AlgebraicGeometry.unit_comp_adicThickeningPushforwardTransition` is the normalization that
  pins it down: it carries the adjunction unit at `n + 1` to the adjunction unit at `n`. Since the
  unit at `n + 1` is an epimorphism
  (`AlgebraicGeometry.epi_unit_app_adicThickeningCompletion`), it is the **only** morphism that
  does, so the hypothesis stated with it is a condition on the family and not on a choice.
* `AlgebraicGeometry.completionProjection_comp_adicThickeningCompletionUnitHomEquiv_symm` — the
  translation itself. The degreewise identification, read backwards and tested against the
  projection `𝒪_X ⟶ ⌃(𝒪_X)ₙ`, is the structure morphism `vₙ^♯ : 𝒪_X ⟶ (vₙ)_* 𝒪_{Xₙ}` followed by
  the direct image of `u n`. The projection lemma supplies the unit and
  `Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso` turns the unit at the
  structure sheaf into `vₙ^♯`.

So the compatibility a caller must supply is the one visible on `X`:

  `vₙ₊₁^♯ ≫ (vₙ₊₁)_* (u (n+1)) ≫ T n = vₙ^♯ ≫ (vₙ)_* (u n)`,

the family being a morphism out of the structure morphisms into the pushed-forward second picture.
`AlgebraicGeometry.adicThickeningUnitSystemHom` assembles it into `α` and
`AlgebraicGeometry.exists_unit_of_adicThickeningPushforwardFamily` is
`exists_unit_of_adicThickeningFamily` with `α` and `hα` discharged.

Some compatibility is indispensable, and this is not an artefact of the route: the module
docstring of `FiniteAlgebraAlgebraization.lean` refutes the form of the descent in which the
degreewise data at `n` and at `n + 1` are unrelated, by a rank-two family over `k⟦t⟧`. The
hypothesis above is exactly the tie between consecutive degrees that refutation shows is needed.

## What this does **not** do

It does not close `hdata`, the third binder of
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData`. `hdata` asks for a
multiplication, a unit and three algebra laws; this is the unit alone. The multiplication is the
descent of a map out of a tensor product and is not reachable from here.

Neither does it identify `adicThickeningPushforwardTransition` with the direct image of
`AlgebraicGeometry.adicThickeningCompletionTransition` along `vₙ`. That identification — which
would state the compatibility purely in the thickening picture, as the caller's `hBtrans` gives
it — is the unit cocycle `Stacks.Descent.unit_pullbackPushforwardAdjunction_comp` read at
`iₙ ≫ vₙ₊₁ = vₙ`, and it goes through the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp` at the adic morphisms, which the module docstring
of `AdicPictureBridges.lean` records as overrunning the deterministic budget in four
ways. It is left to a caller that can afford it; the normalization above is what makes it a
well-posed question with a unique answer.

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

open Stacks.Algebraization (completionFunctor completionProjection completionProjection_transition
  epi_completionProjection unitCoherentModule HasProperSupport)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.AlgebraicGeometry.AffineBaseChange (unitObj pullbackUnitIso structureUnitHom
  unit_comp_map_pullbackUnitIso)

/-! ### Rearranging composites that mix the two presentations

Plain category theory. These are applied as terms rather than rewritten, for the reason recorded
in the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicThickeningUnwinding.lean`: a composite mixing
the coherent modules with `AlgebraicGeometry.Scheme.Modules` is not type-correct at `implicit`
transparency, and associativity rewriting on it fails. -/

section Rearrange

variable {C : Type*} [Category C]

/-- **Cancelling a retraction pair in the middle of a composite.** -/
private theorem comp_comp_cancel_mid {W Y Y' V : C} (a : W ⟶ Y) {m : Y ⟶ Y'} {n : Y' ⟶ Y}
    (hm : m ≫ n = 𝟙 Y) (p : Y ⟶ V) : (a ≫ m) ≫ n ≫ p = a ≫ p := by
  rw [Category.assoc, ← Category.assoc m, hm, Category.id_comp]

/-- **Normalizing the first two factors of a composite.** -/
private theorem comp_comp_congr_left {W Y Z V : C} {a : W ⟶ Y} {b : Y ⟶ Z} {c : W ⟶ Z}
    (h : a ≫ b = c) (m : Z ⟶ V) : a ≫ b ≫ m = c ≫ m := by
  rw [← Category.assoc, h]

/-- **Reading a compatibility stated through a conjugated transition back on the terms it
conjugates.** The shape of the naturality step below: `hu` is the compatibility of the family
with the transition `i₁ ≫ m ≫ h₀`, and the conclusion is the naturality square it becomes once
the normalization `h₀` is cancelled against `i₀`. -/
private theorem comp_comp_comp_eq_of_comp_comp_eq {W Y₁ Z₁ T₁ T₀ Z₀ Y₀ : C} {s₁ : W ⟶ Y₁}
    {q₁ : Y₁ ⟶ Z₁} {i₁ : Z₁ ⟶ T₁} {m : T₁ ⟶ T₀} {h₀ : T₀ ⟶ Z₀} {i₀ : Z₀ ⟶ T₀} {s₀ : W ⟶ Y₀}
    {q₀ : Y₀ ⟶ Z₀} (hh : h₀ ≫ i₀ = 𝟙 T₀) (hu : s₁ ≫ q₁ ≫ i₁ ≫ m ≫ h₀ = s₀ ≫ q₀) :
    s₀ ≫ q₀ ≫ i₀ = (s₁ ≫ q₁ ≫ i₁) ≫ m := by
  rw [← Category.assoc, ← hu]
  simp [hh]

end Rearrange

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsLocallyNoetherian X]

/-! ### The transition of the thickening picture, pushed forward -/

/-- **The transition of the second picture, read on `X`.** The transition of the first picture,
conjugated by the unwinding `AlgebraicGeometry.adicThickeningCompletionPushforwardIso`, is a
morphism `(vₙ₊₁)_* (ℱ|_{Xₙ₊₁}) ⟶ (vₙ)_* (ℱ|_{Xₙ})` between the direct images of the terms of the
thickening picture.

It is defined by conjugation rather than built from `iₙ : Xₙ ⟶ Xₙ₊₁`, and
`AlgebraicGeometry.unit_comp_adicThickeningPushforwardTransition` is what makes that harmless:
the normalization determines it uniquely, so a hypothesis stated with it is a condition on the
data and not a reference to this construction. -/
public def adicThickeningPushforwardTransition
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I (n + 1)))).obj
        (adicThickeningCompletion A I f F.obj (n + 1)) ⟶
      (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).obj
        (adicThickeningCompletion A I f F.obj n) :=
  (adicThickeningCompletionPushforwardIso A I f F (n + 1)).inv ≫
    ((completionFunctor X (baseIdealSheaf A I f)).obj F).obj.map (homOfLE (Nat.le_succ n)).op ≫
      (adicThickeningCompletionPushforwardIso A I f F n).hom

/-- The definition of `AlgebraicGeometry.adicThickeningPushforwardTransition`, named so that the
proofs below can normalize its first factor without unfolding it by unification. -/
private theorem adicThickeningPushforwardTransition_eq
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    adicThickeningPushforwardTransition A I f F n =
      (adicThickeningCompletionPushforwardIso A I f F (n + 1)).inv ≫
        ((completionFunctor X (baseIdealSheaf A I f)).obj F).obj.map
            (homOfLE (Nat.le_succ n)).op ≫
          (adicThickeningCompletionPushforwardIso A I f F n).hom :=
  rfl

/-- **The normalization of the pushed-forward transition.** It carries the unit of
`vₙ₊₁^* ⊣ (vₙ₊₁)_*` at `ℱ` to the unit of `vₙ^* ⊣ (vₙ)_*` at `ℱ`.

This is the compatibility of the unwinding with the transitions of a completion: the unit at `n`
is the projection `ℱ ⟶ ℱ / 𝓘 ⁿ⁺¹ ℱ` read through the unwinding
(`AlgebraicGeometry.adicThickeningCompletionPushforwardIso_projection`), and the projections are
compatible with the quotient transitions
(`Stacks.Algebraization.completionProjection_transition`). -/
public theorem unit_comp_adicThickeningPushforwardTransition
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst f (adicThickeningι A I (n + 1)))).unit.app F.obj ≫
        adicThickeningPushforwardTransition A I f F n =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst f (adicThickeningι A I n))).unit.app F.obj := by
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst f (adicThickeningι A I (n + 1)))).unit.app F.obj ≫ z)
    (adicThickeningPushforwardTransition_eq A I f F n)) ?_
  refine Eq.trans (congrArg (fun k => k ≫
      (adicThickeningCompletionPushforwardIso A I f F (n + 1)).inv ≫
        ((completionFunctor X (baseIdealSheaf A I f)).obj F).obj.map
            (homOfLE (Nat.le_succ n)).op ≫
          (adicThickeningCompletionPushforwardIso A I f F n).hom)
    (adicThickeningCompletionPushforwardIso_projection A I f F (n + 1)).symm) ?_
  refine Eq.trans (comp_comp_cancel_mid
    (completionProjection X (baseIdealSheaf A I f) F (n + 1))
    (adicThickeningCompletionPushforwardIso A I f F (n + 1)).hom_inv_id _) ?_
  refine Eq.trans (comp_comp_congr_left
    (completionProjection_transition X (baseIdealSheaf A I f) F n) _) ?_
  exact adicThickeningCompletionPushforwardIso_projection A I f F n

/-- **The unit of `vₙ^* ⊣ (vₙ)_*` at a coherent module is an epimorphism.** It is the projection
onto a term of the completion, which is an epimorphism
(`Stacks.Algebraization.epi_completionProjection`), followed by an isomorphism.

This is what makes `AlgebraicGeometry.unit_comp_adicThickeningPushforwardTransition` a
characterization: at most one morphism satisfies it.

The category is ascribed, here and in the two epimorphism facts the proof uses: the projection is
typed at `AlgebraicGeometry.Scheme.Modules` and instance search does not cross from there to
`SheafOfModules X.ringCatSheaf`, as the docstring of
`Stacks.Algebraization.epi_completionProjection` records. -/
public theorem epi_unit_app_adicThickeningCompletion
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    Epi (C := X.Modules) ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst f (adicThickeningι A I n))).unit.app F.obj) := by
  have h2 : Epi (C := X.Modules)
      (adicThickeningCompletionPushforwardIso A I f F n).hom := inferInstance
  exact Eq.mp (congrArg (fun k => Epi (C := X.Modules) k)
      (adicThickeningCompletionPushforwardIso_projection A I f F n))
    (@epi_comp _ _ _ _ _ _ (epi_completionProjection X (baseIdealSheaf A I f) F n) _ h2)

/-! ### The degreewise identification, tested against the projection -/

/-- The inverse of `AlgebraicGeometry.adicThickeningCompletionUnitHomEquiv` written out. Both
`CategoryTheory.Iso.homCongr` and `CategoryTheory.Functor.FullyFaithful.homEquiv` are `Equiv`s
with an explicit inverse, so this is reflexivity up to the identity that
`CategoryTheory.Iso.refl` contributes. -/
private theorem adicThickeningCompletionUnitHomEquiv_symm_apply
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (w : unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n) :
    (adicThickeningCompletionUnitHomEquiv A I f n G).symm w =
      (adicThickeningCompletionPushforwardIso A I f (unitCoherentModule X) n).hom ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
            ((pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).hom ≫ w) ≫
          (adicThickeningCompletionPushforwardIso A I f G n).inv :=
  congrArg (fun z =>
      (adicThickeningCompletionPushforwardIso A I f (unitCoherentModule X) n).hom ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
            ((pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).hom ≫ z) ≫
          (adicThickeningCompletionPushforwardIso A I f G n).inv)
    (Category.comp_id w)

/-- **The translation of the compatibility, degreewise.** A morphism `u : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` of
the thickening picture, read backwards through
`AlgebraicGeometry.adicThickeningCompletionUnitHomEquiv` and tested against the projection
`𝒪_X ⟶ ⌃(𝒪_X)ₙ`, is the structure morphism `vₙ^♯` followed by the direct image of `u` and the
unwinding.

This is the whole use of
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso_projection` here: it replaces the
projection followed by the unwinding with the unit of `vₙ^* ⊣ (vₙ)_*`, and
`Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso` identifies that unit at
the structure sheaf, followed by the direct image of `vₙ^* 𝒪_X ≅ 𝒪_{Xₙ}`, with `vₙ^♯`. -/
public theorem completionProjection_comp_adicThickeningCompletionUnitHomEquiv_symm
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (w : unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n) :
    completionProjection X (baseIdealSheaf A I f) (unitCoherentModule X) n ≫
        (adicThickeningCompletionUnitHomEquiv A I f n G).symm w =
      structureUnitHom (pullback.fst f (adicThickeningι A I n)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map w ≫
          (adicThickeningCompletionPushforwardIso A I f G n).inv := by
  refine Eq.trans (congrArg (fun z =>
      completionProjection X (baseIdealSheaf A I f) (unitCoherentModule X) n ≫ z)
    (adicThickeningCompletionUnitHomEquiv_symm_apply A I f G n w)) ?_
  refine Eq.trans (comp_comp_congr_left
    (adicThickeningCompletionPushforwardIso_projection A I f (unitCoherentModule X) n) _) ?_
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction
            (pullback.fst f (adicThickeningι A I n))).unit.app (unitCoherentModule X).obj ≫
        z ≫ (adicThickeningCompletionPushforwardIso A I f G n).inv)
    ((Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map_comp
      (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).hom w)) ?_
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction
            (pullback.fst f (adicThickeningι A I n))).unit.app (unitCoherentModule X).obj ≫ z)
    (Category.assoc
      ((Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
        (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).hom)
      ((Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map w)
      (adicThickeningCompletionPushforwardIso A I f G n).inv)) ?_
  exact comp_comp_congr_left
    (unit_comp_map_pullbackUnitIso (pullback.fst f (adicThickeningι A I n))) _

/-! ### Assembling the family into a morphism of systems -/

section Assembly

variable (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (u : ∀ n : ℕ, unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n)

/-- **The naturality of the assembled morphism.** The degreewise identifications of
`AlgebraicGeometry.adicThickeningCompletionUnitHomEquiv`, read backwards, commute with the
quotient transitions of the first picture as soon as the pushed-forward family commutes with
`AlgebraicGeometry.adicThickeningPushforwardTransition`.

The projections onto the terms of the completion of `𝒪_X` are epimorphisms, so it is enough to
test the square against the one at `n + 1`; against it both sides are translated by
`AlgebraicGeometry.completionProjection_comp_adicThickeningCompletionUnitHomEquiv_symm`, and what
remains is the hypothesis with the normalization of the unwinding cancelled.

Public because the assembled morphism below is a `def` in an exposed section, so its body may not
name a private declaration. -/
public theorem adicThickeningUnitSystemHom_naturality
    (hu : ∀ n : ℕ, structureUnitHom (pullback.fst f (adicThickeningι A I (n + 1))) ≫
        (Scheme.Modules.pushforward
            (pullback.fst f (adicThickeningι A I (n + 1)))).map (u (n + 1)) ≫
          adicThickeningPushforwardTransition A I f G n =
      structureUnitHom (pullback.fst f (adicThickeningι A I n)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map (u n))
    (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj (unitCoherentModule X)).obj.map
          (homOfLE (Nat.le_succ n)).op ≫
        (adicThickeningCompletionUnitHomEquiv A I f n G).symm (u n) =
      (adicThickeningCompletionUnitHomEquiv A I f (n + 1) G).symm (u (n + 1)) ≫
        ((completionFunctor X (baseIdealSheaf A I f)).obj G).obj.map
          (homOfLE (Nat.le_succ n)).op := by
  refine (@cancel_epi _ _ _ _ _ (completionProjection X (baseIdealSheaf A I f)
    (unitCoherentModule X) (n + 1))
    (epi_completionProjection X (baseIdealSheaf A I f) (unitCoherentModule X) (n + 1)) _ _).mp ?_
  refine Eq.trans (comp_comp_congr_left (completionProjection_transition X
    (baseIdealSheaf A I f) (unitCoherentModule X) n) _) ?_
  refine Eq.trans
    (completionProjection_comp_adicThickeningCompletionUnitHomEquiv_symm A I f G n (u n)) ?_
  refine Eq.trans ?_ (Category.assoc
    (completionProjection X (baseIdealSheaf A I f) (unitCoherentModule X) (n + 1))
    ((adicThickeningCompletionUnitHomEquiv A I f (n + 1) G).symm (u (n + 1)))
    (((completionFunctor X (baseIdealSheaf A I f)).obj G).obj.map (homOfLE (Nat.le_succ n)).op))
  refine Eq.trans ?_ (congrArg (fun z => z ≫
      ((completionFunctor X (baseIdealSheaf A I f)).obj G).obj.map (homOfLE (Nat.le_succ n)).op)
    (completionProjection_comp_adicThickeningCompletionUnitHomEquiv_symm A I f G (n + 1)
      (u (n + 1))).symm)
  exact comp_comp_comp_eq_of_comp_comp_eq
    (adicThickeningCompletionPushforwardIso A I f G n).hom_inv_id
    (Eq.trans (congrArg (fun z =>
        structureUnitHom (pullback.fst f (adicThickeningι A I (n + 1))) ≫
          (Scheme.Modules.pushforward
            (pullback.fst f (adicThickeningι A I (n + 1)))).map (u (n + 1)) ≫ z)
      (adicThickeningPushforwardTransition_eq A I f G n).symm) (hu n))

/-- **The binder `α` of `AlgebraicGeometry.exists_unit_of_adicThickeningFamily`, constructed.**
A family `u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` whose direct images are compatible with the pushed-forward
transitions assembles into a morphism of the inverse systems of
`Stacks.Algebraization.completionFunctor`.

The terms come from `AlgebraicGeometry.adicThickeningCompletionUnitHomEquiv` read backwards; the
naturality is supplied at the successor steps only, by `CategoryTheory.NatTrans.ofOpSequence`,
and the systems are a full subcategory of `ℕᵒᵖ ⥤ X.Modules`, so the morphism is
`CategoryTheory.ObjectProperty.homMk` of that natural transformation. -/
public def adicThickeningUnitSystemHom
    (hu : ∀ n : ℕ, structureUnitHom (pullback.fst f (adicThickeningι A I (n + 1))) ≫
        (Scheme.Modules.pushforward
            (pullback.fst f (adicThickeningι A I (n + 1)))).map (u (n + 1)) ≫
          adicThickeningPushforwardTransition A I f G n =
      structureUnitHom (pullback.fst f (adicThickeningι A I n)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map (u n)) :
    (completionFunctor X (baseIdealSheaf A I f)).obj (unitCoherentModule X) ⟶
      (completionFunctor X (baseIdealSheaf A I f)).obj G :=
  ObjectProperty.homMk (NatTrans.ofOpSequence
    (fun n => (adicThickeningCompletionUnitHomEquiv A I f n G).symm (u n))
    (adicThickeningUnitSystemHom_naturality A I f G u hu))

/-- **The unit side of `hdata`, with no binder left.** Let `G` be a coherent `𝒪_X`-module whose
support is proper over an `I`-adically complete Noetherian base and let
`u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` be a family of morphisms on the adic thickenings whose direct images on
`X` are compatible with the pushed-forward transitions. Then there is a morphism `μ : 𝒪_X ⟶ G` on
`X` restricting to `u n` for every `n`.

This is `AlgebraicGeometry.exists_unit_of_adicThickeningFamily` with its binder `α` discharged by
`AlgebraicGeometry.adicThickeningUnitSystemHom` and its `hα` by
`Equiv.apply_symm_apply`, the components of that morphism being the degreewise identifications
read backwards. No hypothesis on the theorem on formal functions is carried, and no tensor
product or multiplication enters: the descent used is
`Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete`, which
is unconditional over such a base. -/
public theorem exists_unit_of_adicThickeningPushforwardFamily [IsNoetherianRing A]
    [IsAdicComplete I A] [LocallyOfFiniteType f] (hG : HasProperSupport f G.obj)
    (hu : ∀ n : ℕ, structureUnitHom (pullback.fst f (adicThickeningι A I (n + 1))) ≫
        (Scheme.Modules.pushforward
            (pullback.fst f (adicThickeningι A I (n + 1)))).map (u (n + 1)) ≫
          adicThickeningPushforwardTransition A I f G n =
      structureUnitHom (pullback.fst f (adicThickeningι A I n)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map (u n)) :
    ∃ μ : SheafOfModules.unit X.ringCatSheaf ⟶ G.obj, ∀ n : ℕ,
      (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).inv ≫
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ = u n :=
  exists_unit_of_adicThickeningFamily A I f G hG u
    (adicThickeningUnitSystemHom A I f G u hu)
    (fun n => Equiv.apply_symm_apply (adicThickeningCompletionUnitHomEquiv A I f n G) (u n))

end Assembly

end AlgebraicGeometry

end
