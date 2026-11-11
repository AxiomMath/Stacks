module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAdicCompletion
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence

/-!
# The short exact sequence of cohomology at the formal completion

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a Noetherian scheme over `A`
and `ℱ` a coherent `𝒪_X`-module all of whose cohomology modules `H^p(X, ℱ)` are finite over `A`.
Write `𝓘 = I · 𝒪_X`. The ingredients used in
`Completion/CohomologyAdicCompletion.lean` — [Stacks, Tag 0A0K], [Stacks, Tag 08U1],
[Stacks, Tag 07KZ] and [Stacks, Tag 0A06] — already give, with nothing assumed, the short exact
sequence
`0 ⟶ R¹lim H^{p-1}(X, ℱ/𝓘ⁿℱ) ⟶ H^p(X, lim ℱ/𝓘ⁿℱ) ⟶ lim H^p(X, ℱ/𝓘ⁿℱ) ⟶ 0`
— the second displayed sequence of the source's proof, whose outer terms are the tag's own — and
the identification `H^p(RΓ(X, ℱ)^∧) = H^p(X, ℱ)^∧` of the cohomology of the derived `I`-adic
completion of `RΓ(X, ℱ)` with the `I`-adic completion of `H^p(X, ℱ)`. Both are proved under the
tag's own hypotheses in `exists_shortExact_cohomology_limit_adicQuotients`, a step of the
source's proof.

What separates that from the source's conclusion is a single isomorphism of `D(A)`: the
identification of `RΓ(X, lim ℱ/𝓘ⁿℱ)` with the derived `I`-adic completion of `RΓ(X, ℱ)`, which is
[Stacks, Tag 0BLX]. Composing the sequence with it moves the middle term onto `H^p(X, ℱ)^∧` and
so gives the source's statement; at a chosen reflector that transport is
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology` of
`Completion/CohomologyAdicCompletion.lean`, and with no reflector supplied it is
`exists_shortExact_adicCompletion_cohomology_of_forall_reflector` below, which takes the
isomorphism as the hypothesis `hBLX` and therefore carries no tag. The derived completion functor
is never assumed there: it is produced from [Stacks, Tag 0920].

`hBLX` is discharged for an **arbitrary** ideal `I` in
`Completion/GeneralCohomologyAdicCompletion.lean`, by
`Stacks.Algebraization.hBLX_baseIdealSheaf`, and the source's whole statement — the sequence with
`H^p(X, ℱ)^∧` in the middle **and** the vanishing of the `R¹lim` term for a proper `f` — is
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_whole` there. At a *principal*
ideal `I = (a)` the transport is also carried out, by a different route, in
`Completion/PrincipalCohomologyAdicCompletion.lean`. The vanishing of the `R¹lim` term for a
proper `f` rests on the Mittag-Leffler condition for the tower `n ↦ H^{p-1}(X, ℱ/𝓘ⁿℱ)`, which is
[Stacks, Tag 02OB], and is proved — unconditionally, from [Stacks, Tag 02O8] — in
`Completion/CohomologyAdicCompletionWhole.lean` as
`Stacks.Algebraization.isZero_firstDerivedLimit_cohomology_adicQuotients_of_isProper`.

## Main results

* `Stacks.Algebraization.exists_shortExact_cohomology_limit_adicQuotients`: the short exact
  sequence relating `H^p(X, lim ℱ/𝓘ⁿℱ)` to the inverse limit and the first derived inverse limit
  of the cohomology modules of the adic quotients, together with the identification of the
  cohomology of the derived `I`-adic completion of `RΓ(X, ℱ)` with the `I`-adic completion of
  `H^p(X, ℱ)`.
* `Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_of_forall_reflector`: the
  same sequence with the `I`-adic completion of `H^p(X, ℱ)` in the middle, with no reflector
  supplied and [Stacks, Tag 0BLX] assumed at every reflector.

## Implementation notes

Derived `I`-adic completion is a left adjoint to the inclusion of the full subcategory of
derived-complete objects of `D(A)`, as in [Stacks, Tag 0A06]. It is *not* assumed as data: `A`
being Noetherian, `I` is of finite type, and
`AdicCompletionTor.derivedCompletion_homology_shortExact` ([Stacks, Tag 0EET], which reads the
adjunction off [Stacks, Tag 0920]) produces a reflector inside the proof. The library fixes no
choice of one, so every statement about derived completion here is quantified over every
reflector: in the registered theorem that quantifier is in the conclusion, where by uniqueness of
left adjoints it is no weaker than naming one, and in the hypothesis `hBLX` of the transport it is
no stronger than naming one.

As in `Completion/CohomologyAdicCompletion.lean`, `Stacks.Algebraization.modulesHasDerivedCategory`
is reinstated as a local instance of high priority, so that `D(𝒪_X)` is the standard model.

## References

* [Stacks Project, Tag 0A0M](https://stacks.math.columbia.edu/tag/0A0M)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0EET](https://stacks.math.columbia.edu/tag/0EET)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped AlgebraicGeometry

attribute [local instance 10000] Stacks.Algebraization.modulesHasDerivedCategory

universe u

namespace Stacks.Algebraization

/-- **The second displayed sequence of the proof of [Stacks, Tag 0A0M]**, the exact sequence at
the formal completion.

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a Noetherian scheme over `A` and
`ℱ` a coherent `𝒪_X`-module whose cohomology modules `H^p(X, ℱ)` are finite over `A` — the
hypotheses of the source, and nothing else. Write `𝓘 = I · 𝒪_X`. Then for every `p`:

* there is a short exact sequence of `A`-modules
  `0 ⟶ R¹lim H^{p-1}(X, ℱ/𝓘ⁿℱ) ⟶ H^p(X, lim ℱ/𝓘ⁿℱ) ⟶ lim H^p(X, ℱ/𝓘ⁿℱ) ⟶ 0`,
  whose left term is the cokernel of `1 - shift` on the product of the degree-`(p-1)` cohomology
  tower and whose right term is the inverse limit of the degree-`p` cohomology tower — the two
  outer terms of the source's conclusion, related exactly as the source relates them; and
* for every reflector `C` onto the derived-complete objects of `D(A)`, the `p`-th cohomology of
  the derived `I`-adic completion `C(RΓ(X, ℱ))` is the `I`-adic completion of `H^p(X, ℱ)`. This
  is [Stacks, Tag 0A06] and is the step at which the source uses the finiteness of `H^p(X, ℱ)`
  over `A`.

Derived `I`-adic completion is not assumed: `A` is Noetherian, so a reflector exists by
[Stacks, Tag 0920], and the second part is stated for every one of them.

The middle term of this sequence is `H^p(X, lim ℱ/𝓘ⁿℱ)` rather than `H^p(X, ℱ)^∧`; identifying
the two is the composite of the second part above with the isomorphism
`RΓ(X, lim ℱ/𝓘ⁿℱ) ≅ C(RΓ(X, ℱ))` of [Stacks, Tag 0BLX], along which
`exists_shortExact_adicCompletion_cohomology` below transports the sequence. That isomorphism is
proved for an arbitrary ideal `I` in
`Completion/GeneralCohomologyAdicCompletion.lean`, as
`Stacks.Algebraization.hBLX_baseIdealSheaf`, and the source's whole statement — the sequence with
`H^p(X, ℱ)^∧` in the middle, and the vanishing of the `R¹lim` term for a proper `f` — is
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_whole` there. -/
public theorem exists_shortExact_cohomology_limit_adicQuotients
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ p : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))))
    (p : ℤ) :
    let T : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      adicQuotientSystem (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F ⋙
        DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f
    let H : ℤ → DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A := fun q ↦
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
    (∃ (i : CompletionSequences.firstDerivedLimit A (T ⋙ H (p - 1)) ⟶
        (H p).obj ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (limit (adicQuotientSystem
              (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F)))))
      (q : (H p).obj ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (limit (adicQuotientSystem
              (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F)))) ⟶
        limit (T ⋙ H p))
      (w : i ≫ q = 0),
      (ShortComplex.mk i q w).ShortExact) ∧
    ∀ (C : DerivedCategory (ModuleCat.{u} A) ⥤
        (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
          fun L ↦ IsDerivedComplete I L).FullSubcategory)
        (_ : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
          fun L ↦ IsDerivedComplete I L).ι),
      Nonempty
        ((H p).obj ((C.obj ((derivedGlobalSectionsOver f).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj) ≅
          ModuleCat.of A (AdicCompletion I
            ((H p).obj ((derivedGlobalSectionsOver f).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F))))) := by
  intro T H
  set single := DerivedCategory.singleFunctor X.Modules 0
  set D := derivedGlobalSectionsOver f
  set S := adicQuotientSystem (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F
  refine ⟨?_, ?_⟩
  · -- [Stacks, Tag 0A0K]: the ordinary limit of the adic quotient tower is its derived limit.
    obtain ⟨hprodSheaf, hlimSheaf⟩ :=
      isDerivedLimit_single_limit_powerQuotients
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F
    -- [Stacks, Tag 08U1]: derived global sections carry that to a derived limit in `D(A)`.
    obtain ⟨hprod, hlim⟩ :=
      isDerivedLimit_map_derivedGlobalSectionsOver f (S ⋙ single) (single.obj (limit S)) hlimSheaf
    have hprod' : HasProduct fun n : ℕ ↦ T.obj ⟨n⟩ := hprod
    have hlim' : IsDerivedLimit T (D.obj (single.obj (limit S))) := hlim
    -- [Stacks, Tag 07KZ]: the Milnor short exact sequence of that derived limit.
    obtain ⟨-, hmilnor⟩ :=
      ModuleDerivedLimitTriangle.derivedLimit_iso_and_homology_shortExact.{u, u} A T
    obtain ⟨a, b, -, hdegree⟩ := hmilnor _ hlim'
    obtain ⟨-, i, q, w, -, -, -, hse⟩ := hdegree p
    exact ⟨i, q, w, hse⟩
  · -- [Stacks, Tag 0A06]: all cohomology modules being finite, the derived completion computes
    -- the `I`-adic completion of each of them.
    intro C adj
    exact AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion A I
      (D.obj (single.obj F)) hfinite C adj p

/-- The short exact sequence of [Stacks, Tag 0A0M] with the `I`-adic completion of `H^p(X, ℱ)` in
the middle, given the identification `hBLX` of [Stacks, Tag 0BLX].

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a Noetherian scheme over `A`
and `ℱ` a coherent `𝒪_X`-module whose cohomology modules `H^p(X, ℱ)` are finite over `A`. Write
`𝓘 = I · 𝒪_X`. Then for every `p` the `I`-adic completion of `H^p(X, ℱ)` sits in a short exact
sequence of `A`-modules
`0 ⟶ R¹lim H^{p-1}(X, ℱ/𝓘ⁿℱ) ⟶ H^p(X, ℱ)^∧ ⟶ lim H^p(X, ℱ/𝓘ⁿℱ) ⟶ 0`
whose left term is the cokernel of `1 - shift` on the product of the degree-`(p-1)` cohomology
tower and whose right term is the inverse limit of the degree-`p` cohomology tower.

Derived `I`-adic completion is not assumed: `A` is Noetherian, so a left adjoint `C` to the
inclusion of the derived-complete objects of `D(A)` exists by [Stacks, Tag 0920] and is produced
in the proof. The single assumed result is `hBLX`, which is [Stacks, Tag 0BLX] for `f`: the
derived global sections of the formal completion `lim ℱ/𝓘ⁿℱ` are the derived `I`-adic completion
of the derived global sections of `ℱ`. It is quantified over the reflector because the library
fixes no choice of one; by uniqueness of left adjoints that is equivalent to its instance at any
single reflector.

Because `hBLX` is a result the source's proof *derives* rather than one of its hypotheses, this
theorem carries no tag; it is exactly the transport along `hBLX` of
`exists_shortExact_cohomology_limit_adicQuotients` above, which proves the same sequence with
`H^p(X, lim ℱ/𝓘ⁿℱ)` in the middle and assumes nothing. `hBLX` is proved at an arbitrary ideal by
`Stacks.Algebraization.hBLX_baseIdealSheaf`, and the tag is carried by
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_whole` of
`Completion/GeneralCohomologyAdicCompletion.lean`. -/
public theorem exists_shortExact_adicCompletion_cohomology_of_forall_reflector
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ p : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))))
    (hBLX : ∀ (C : DerivedCategory (ModuleCat.{u} A) ⥤
        (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
          fun L ↦ IsDerivedComplete I L).FullSubcategory)
        (_ : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
          fun L ↦ IsDerivedComplete I L).ι),
      Nonempty
        ((C.obj ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj ≅
          (derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (limit (adicQuotientSystem
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F)))))
    (p : ℤ) :
    let T : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      adicQuotientSystem (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F ⋙
        DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f
    let H : ℤ → DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A := fun q ↦
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
    ∃ (i : CompletionSequences.firstDerivedLimit A (T ⋙ H (p - 1)) ⟶
        ModuleCat.of A (AdicCompletion I
          ((H p).obj ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)))))
      (q : ModuleCat.of A (AdicCompletion I
          ((H p).obj ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)))) ⟶
        limit (T ⋙ H p))
      (w : i ≫ q = 0),
      (ShortComplex.mk i q w).ShortExact := by
  -- [Stacks, Tag 0920] in the shape of [Stacks, Tag 0EET]: derived `I`-adic completion on `D(A)`
  -- exists, `A` being Noetherian, so no reflector has to be assumed.
  have : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨C, ⟨adj⟩, -, -, -⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A I
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A)
  exact exists_shortExact_adicCompletion_cohomology A I f F hfinite C adj (hBLX C adj) p

end Stacks.Algebraization

end
