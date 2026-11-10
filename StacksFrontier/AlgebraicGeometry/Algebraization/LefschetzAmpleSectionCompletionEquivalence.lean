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

* `Stacks.Algebraization.IsCompletionEquivalenceOnFiniteLocallyFree` — the conclusion in the
  vocabulary available here: full faithfulness of completion on finite locally free coherent
  modules together with essential surjectivity refined by a neighbourhood of the subscheme.

## Main results

* `Stacks.Algebraization.isCompletionEquivalence_of_two_lt_depth_add_dimClosure` — Stacks 0EL7.

## Implementation notes

The colimit `colim_𝓥 Coh(𝒪_V)` is not a category in this library, and cannot be assembled from
what is here: as the Stacks 0EK2 file records in its own "remaining implications" section, the
comparison of `Coh(X, 𝓘)` with `Coh(V, 𝓘|_V)` for a neighbourhood `V` is missing, and that
comparison is what is needed even to write down the functor out of the colimit. The two halves of
the conclusion are therefore stated as follows.

* Essential surjectivity is stated with the neighbourhood: every finite locally free object of
  `Coh(X, 𝓘)` is the completion of a coherent `𝒪_X`-module that is finite locally free on an open
  containing `Y`. That is the object-level content of the equivalence, and it is what the source's
  proof produces.
* Full faithfulness is stated at the ambient scheme, as
  `Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree`
  (`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/Basic.lean`, line 361),
  which is the `V = X` member of the colimit. It is not the colimit statement, which quantifies
  over pairs of modules living on possibly different neighbourhoods.

Two inputs are hypotheses rather than invocations, each with a reason.

* `hff`, full faithfulness. The source gets it from Lemma 52.15.2 and the sections comparison of
  Stacks 0EL2; in this library the Stacks 0EK2 carrier
  `Stacks.Algebraization.quasiAffine_neighbourhoodSectionsComplete_implies_amplePower`
  (`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/Neighbourhoods.lean`,
  line 288) proves only (1) ⇒ (2), and its
  module documentation records that (2) ⇒ (3) ⇒ (4), which is what would turn the sections
  comparison into full faithfulness, needs inputs that are absent.
* `halgebraize`, the conclusion of Stacks 0EL5 together with the depth identity that feeds it.
  The Stacks 0EL5 carrier `Stacks.Algebraization.satisfiesDepthInequalities_one_two_iff`
(`StacksFrontier/AlgebraicGeometry/Algebraization/DepthInequalitiesCohomologicalDimensionOne.lean`)
  proves only the opening step of that proposition, in the affine situation of Stacks 0EHC, and
  its attribute says so; the depth identity rests on Local Cohomology, Lemma 51.11.3, which is
  not available either.

What is proved is the assembly: the depth hypothesis is handed to `halgebraize` unchanged, and the
local freeness it returns along `Y` is turned into a single open neighbourhood by
`Stacks.Algebraization.exists_isOpen_isFiniteLocallyFree_of_forall_mem`.

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

/-- **The conclusion of Stacks 0EL7, spelled out.** Completion along `𝓘` is fully faithful on
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

/-- **Stacks Project, Tag 0EL7.** Let `X` be a proper scheme over a field, `𝓛` an ample invertible
`𝒪_X`-module, `s ∈ Γ(X, 𝓛)` and `Y = Z(s)` with sheaf of ideals `𝓘`. If
`depth(𝒪_{X,x}) + dim({x}‾) > 2` at every point off `Y`, then completion along `𝓘` is fully
faithful on finite locally free coherent modules, and every finite locally free object of
`Coh(X, 𝓘)` is the completion of a coherent module finite locally free near `Y`. -/
@[stacks 0EL7 "essential surjectivity up to V; full faithfulness over X; 0EL5, 0EL2 assumed"]
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
