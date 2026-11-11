module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods

/-!
# Completion along the zero scheme of a section of an ample module

Let `k` be a field, `X` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_X`-module and
`s ∈ Γ(X, 𝓛)`. Write `Y = Z(s)` for the zero scheme of `s`, let `𝓘 ⊆ 𝒪_X` be its sheaf of ideals,
and let `𝓥` be the open subschemes of `X` containing `Y`, ordered by reverse inclusion. Stacks
0EL7 says that if

`depth(𝒪_{X,x}) + dim({x}‾) > 2`

for every `x ∈ X ∖ Y`, then the completion functor `colim_𝓥 Coh(𝒪_V) ⟶ Coh(X, 𝓘)` is an
equivalence on the full subcategories of finite locally free objects.

The source proves the two halves separately, and they are separate here as well. Full
faithfulness is reduced to the sections comparison `colim_𝓥 Γ(V, 𝓛^{⊗ m}) → lim Γ(Y_n,
𝓛^{⊗ m}|_{Y_n})` being bijective for all `m`, which is condition (2) of Stacks 0EK2. Essential
surjectivity uses the depth hypothesis: a finite locally free object `(𝓕_n)` has finite free
completed stalks along `Y`, the depth identity

`depth((𝒪_{X,y}^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) = depth(𝒪_{X,x}) + dim({x}‾) - dim({y}‾)`

at a specialization `x ⤳ y` with `x ∉ Y` turns the hypothesis into the criterion of Stacks 0EL5,
and the coherent module it produces has finite free stalks along `Y`, hence is finite locally
free on an open `V ∈ 𝓥`.

## Main definitions

* `Stacks.Algebraization.IsCompletionEquivalenceOnFiniteLocallyFree` — a weaker form of
  the conclusion of Stacks 0EL7: full faithfulness of completion on finite locally free coherent
  `𝒪_X`-modules (not over the colimit) together with essential surjectivity refined by a
  neighbourhood of the subscheme.

## Main results

* `Stacks.Algebraization.isCompletionEquivalence_of_two_lt_depth_add_dimClosure` — the conclusion
  from full faithfulness and a pointwise algebraization, both taken as hypotheses. The
  unconditional Stacks 0EL7 is
  `Stacks.Algebraization.completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure`
  (`StacksFrontier/AlgebraicGeometry/Algebraization/LefschetzFiniteLocallyFreeEquivalence.lean`).

## Implementation notes

The theorem of this file is an assembly step, not Stacks 0EL7: both halves of its conclusion are
hypotheses. `hff` is full faithfulness of completion on finite locally free coherent
`𝒪_X`-modules, which is only the `V = X` member of the full faithfulness over
`colim_𝓥 Coh(𝒪_V)`; `halgebraize` is the conclusion of Stacks 0EL5 fed by the depth identity, for
the given `X`, `𝓛` and `s`. What is proved is that the local freeness `halgebraize` returns along
`Y` is turned into a single open neighbourhood by
`Stacks.Algebraization.exists_isOpen_isFiniteLocallyFree_of_forall_mem`.

Stacks 0EL7 itself, unconditional and with full faithfulness over the colimit (condition (4) of
Stacks 0EK2, `Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`), is
`Stacks.Algebraization.completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure`.

The zero scheme is `AlgebraicGeometry.Scheme.zeroScheme`, which is directly the sheaf of ideals
`𝓘`, so `Y` itself never has to be named; `𝓥` is the opens containing its support, and
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι` identifies that support with the image
of the closed immersion `Y ⟶ X` used by the Stacks 0EK2 vocabulary.

## References

* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5), the criterion.
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2), the sections comparison.
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2), the four conditions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- **A weaker form of the conclusion of Stacks 0EL7.** Completion along `𝓘` is fully faithful on
finite locally free coherent `𝒪_X`-modules, and every finite locally free object of `Coh(X, 𝓘)`
is the completion of a coherent `𝒪_X`-module which is finite locally free on an open
neighbourhood of the closed subscheme cut out by `𝓘`. -/
public def IsCompletionEquivalenceOnFiniteLocallyFree (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : Prop :=
  CompletionFullyFaithfulOnFiniteLocallyFree X I ∧
    ∀ F : Stacks.Coherent.CoherentAdicSystems I,
      (∀ n : ℕ, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (F.obj.obj (op n))) →
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        Nonempty (((completionFunctor X I).obj G).obj ≅ F.obj) ∧
          ∃ V : X.Opens, (I.support : Set X) ⊆ (V : Set X) ∧ ∀ x : X, x ∈ V →
            ∃ (U : X.Opens) (_ : x ∈ U) (_ : U ≤ V) (ρ : Type u) (_ : Finite ρ),
              Nonempty (Scheme.Modules.restrict G.obj U.ι ≅ SheafOfModules.free.{u} ρ)

/-- **A conditional assembly for [Stacks, Tag 0EL7]; not Tag 0EL7 itself.** Let `X` be a proper
scheme over a field, `𝓛` an ample invertible `𝒪_X`-module, `s ∈ Γ(X, 𝓛)` and `Y = Z(s)` with
sheaf of ideals `𝓘`. Given full faithfulness of completion on finite locally free coherent
`𝒪_X`-modules (`hff`) and, for every finite locally free object of `Coh(X, 𝓘)`, a coherent
`𝒪_X`-module with that completion which is free near each point of `Y` (`halgebraize`), the
conclusion `IsCompletionEquivalenceOnFiniteLocallyFree` follows: the pointwise neighbourhoods are
glued into one open containing `Y`.

Both halves of the conclusion are thus hypotheses, and properness, ampleness and the depth
inequality play no role in the proof. The unconditional statement of [Stacks, Tag 0EL7], with full
faithfulness over the colimit `colim_𝓥 Coh(𝒪_V)`, is
`Stacks.Algebraization.completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure`. -/
public theorem isCompletionEquivalence_of_two_lt_depth_add_dimClosure (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (_hample : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x)
    (hff : CompletionFullyFaithfulOnFiniteLocallyFree X (zeroScheme X L s))
    (halgebraize : ∀ F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s),
      (∀ n : ℕ, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (F.obj.obj (op n))) →
      (∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
        ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x) →
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        Nonempty (((completionFunctor X (zeroScheme X L s)).obj G).obj ≅ F.obj) ∧
          ∀ y ∈ ((zeroScheme X L s).support : Set X),
            ∃ (U : X.Opens) (_ : y ∈ U) (ρ : Type u) (_ : Finite ρ),
              Nonempty (Scheme.Modules.restrict G.obj U.ι ≅ SheafOfModules.free.{u} ρ)) :
    IsCompletionEquivalenceOnFiniteLocallyFree X (zeroScheme X L s) := by
  refine ⟨hff, fun F hF => ?_⟩
  obtain ⟨G, hG, hstalk⟩ := halgebraize F hF hdepth
  obtain ⟨V, hV, hfreeV⟩ :=
    exists_isOpen_isFiniteLocallyFree_of_forall_mem G.obj
      ((zeroScheme X L s).support : Set X) hstalk
  exact ⟨G, hG, V, hV, hfreeV⟩

end Stacks.Algebraization

end
