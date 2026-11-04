module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QA

/-!
# The bounds of [Stacks, Tag 07QA] from the statement of [Stacks, Tag 07Q9]

[Stacks, Tag 07QA] reads: *with notations and assumptions as in [Stacks, Lemma 60.25.4, Tag 07Q9],
the map `f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` has kernel and cokernel annihilated by
`q^{i + 1}`.*  The tag is registered on
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
`SmallSite/CrisCohomologyBound07QAMain.lean`, under exactly those assumptions.  This file
records the deduction for an arbitrary abelian sheaf `ℱ` on `Cris(X/S)` and the abelian inverse
image, from the library's rendering `...SmallSite.Statement07Q9` of [Stacks, Tag 07Q9] taken as
the binder `h07Q9`; it carries no tag.

## The two clauses, and what each costs

The kernel clause is the source's argument: the kernel of `f^*` is a quotient of
`H^{i - 1}(X_Zar, E)` for `E` the third term of the triangle of [Stacks, Tag 07Q9], the
filtration of that group runs over the `i + 1` degrees `-1, 0, …, i - 1`, and `E` is
concentrated in degrees `≥ -1` because `Ru_{X/S, *}ℱ` and `Rf_{Zar, *}Ru_{X'/S, *}ℱ'` are
concentrated in degrees `≥ 0`.

The cokernel injects into `H^i(X_Zar, E)`, whose filtration runs over the `i + 2` degrees
`-1, 0, …, i`; from the annihilation alone one therefore obtains `q^{i + 2}`.  The two exponents
differ by the degree `-1` step: `ℋ^{-1}(E)` is the kernel of
`ℋ^0(Ru_{X/S, *}ℱ) ⟶ ℋ^0(Rf_{Zar, *}Ru_{X'/S, *}ℱ')`, which
`...SmallSite.mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` identifies with
`u_{X/S, *}` of the crystalline adjunction unit, taken here as the binder `hmono`.  For a crystal
in quasi-coherent modules and the module pullback that injectivity is proved, as
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.

## The degenerate cover

`Mono (u_{X/S, *}(crisUnit ℱ))` fails for `X' = ∅` and `ℱ ≠ 0`, since then `f_cris^{-1}` is the
zero functor.  An `α_p`-cover is `Spec` of `C ⟶ C[z]/(z^p - c)`, which is free of rank `p ≥ 1`,
so its source is empty only when its target is: `AlgebraicGeometry.isEmpty_of_isAlphaPCover`,
`AlgebraicGeometry.isEmpty_of_isAlphaPCoverComposite` and
`AlgebraicGeometry.isEmpty_of_isIteratedAlphaPCover` below.

## Main results

* `pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA_of_statement07Q9` — the kernel bound for
  an abelian sheaf, from `Statement07Q9`.
* `exists_crisCohomologyMap_eq_pow_smul_07QA_of_statement07Q9` — the cokernel bound for an
  abelian sheaf, from `Statement07Q9` and `hmono`.
* `exists_comp_mor₁_eq_pow_smul_07QA_of_isGE_neg_one`,
  `exists_hypercohomologyMap_eq_pow_smul_07QA_pow_add_two`,
  `exists_crisCohomologyMap_eq_pow_smul_07QA_pow_add_two` and
  `exists_crisCohomologyMap_eq_pow_smul_07QA_of_statement07Q9_pow_add_two` — the cokernel bound
  with exponent `q^{i + 2}`, which is what the conclusion of [Stacks, Tag 07Q9] gives on its own,
  with no hypothesis on `ℋ^0` of the comparison map.  These measure the one step `hmono` buys.
* `AlgebraicGeometry.injective_C_mk_alphaPAlgebra` — `C ⟶ C[z]/(z^p - c)` is injective for
  `p ≠ 0`.
* `AlgebraicGeometry.isEmpty_of_isAlphaPCover`,
  `AlgebraicGeometry.isEmpty_of_isAlphaPCoverComposite`,
  `AlgebraicGeometry.isEmpty_of_isIteratedAlphaPCover` — the source of an `α_p`-cover, of a
  composition of `α_p`-covers, or of an iterated `α_p`-cover is empty only if its target is.

## References

* [Stacks Project, Lemma 60.25.5, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe w w' u

noncomputable section

/-! ### The degenerate cover `X' = ∅` is excluded -/

namespace AlgebraicGeometry

/-- **`C ⟶ C[z]/(z^p - c)` is injective for `p ≠ 0`.**  The relation is monic of degree `p ≥ 1`,
so no nonzero constant polynomial is divisible by it: division by a monic polynomial leaves a
constant unchanged.

This is the ring-level form of the statement that the local model
`Spec(C[z]/(z^p - c)) ⟶ Spec(C)` of an `α_p`-cover has empty source only if it has empty
target. -/
theorem injective_C_mk_alphaPAlgebra {p : ℕ} (hp : p ≠ 0) (C : Type u) [CommRing C] (c : C) :
    Function.Injective (fun r : C =>
      Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ p - Polynomial.C c : Polynomial C)})
        (Polynomial.C r)) := by
  cases subsingleton_or_nontrivial C with
  | inl h => exact fun r s _ => Subsingleton.elim r s
  | inr h =>
    have hg : (Polynomial.X ^ p - Polynomial.C c : Polynomial C).Monic :=
      Polynomial.monic_X_pow_sub_C c hp
    intro r s hrs
    have hrs' : Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X ^ p - Polynomial.C c : Polynomial C)}) (Polynomial.C r) =
        Ideal.Quotient.mk
          (Ideal.span {(Polynomial.X ^ p - Polynomial.C c : Polynomial C)}) (Polynomial.C s) :=
      hrs
    have h0 : Polynomial.C (r - s) ∈
        Ideal.span {(Polynomial.X ^ p - Polynomial.C c : Polynomial C)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, hrs', sub_self]
    have hmod :
        Polynomial.C (r - s) %ₘ (Polynomial.X ^ p - Polynomial.C c : Polynomial C) = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hg).2 (Ideal.mem_span_singleton.mp h0)
    have hself :
        Polynomial.C (r - s) %ₘ (Polynomial.X ^ p - Polynomial.C c : Polynomial C) =
          Polynomial.C (r - s) := by
      rw [Polynomial.modByMonic_eq_self_iff hg,
        Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp) c]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.pos_of_ne_zero hp)
    exact sub_eq_zero.mp (Polynomial.C_eq_zero.mp (hself.symm.trans hmod))

/-- **The source of an `α_p`-cover is empty only if its target is.**  The local model is
`Spec(C[z]/(z^p - c)) ⟶ Spec(C)`, and `injective_C_mk_alphaPAlgebra` makes `C[z]/(z^p - c)` the
zero ring only when `C` is.

This is what removes the degenerate cover from the hypotheses of
[Stacks, Lemma 60.25.4, Tag 07Q9]: for `X' = ∅` and `X ≠ ∅` the crystalline inverse image along
`f` is the zero functor, so the injectivity of the crystalline adjunction unit that the cokernel
clause of [Stacks, Lemma 60.25.5, Tag 07QA] rests on would fail. -/
theorem isEmpty_of_isAlphaPCover {p : ℕ} (hp : p ≠ 0) {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsAlphaPCover p f) (h : IsEmpty X') : IsEmpty X := by
  obtain ⟨C, hC, hpC, c, e, e', he⟩ := hf
  let := hC
  have hA : IsEmpty (Spec (CommRingCat.of (alphaPAlgebra p C c))) :=
    Function.isEmpty (Scheme.homeoOfIso e').symm
  have hsub : Subsingleton (alphaPAlgebra p C c) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mp hA
  have : Subsingleton C :=
    ⟨fun r s => injective_C_mk_alphaPAlgebra hp C c (Subsingleton.elim _ _)⟩
  have : IsEmpty (Spec (CommRingCat.of C)) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr inferInstance
  exact Function.isEmpty (Scheme.homeoOfIso e)

/-- **The source of a composition of `α_p`-covers is empty only if its target is.**  Induction
along the composition, the base case being an isomorphism and the inductive step
`isEmpty_of_isAlphaPCover`. -/
theorem isEmpty_of_isAlphaPCoverComposite {p : ℕ} (hp : p ≠ 0) {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsAlphaPCoverComposite p f) (h : IsEmpty X') : IsEmpty X := by
  induction hf with
  | of_isIso g hg =>
    have := hg
    exact Function.isEmpty (Scheme.homeoOfIso (asIso g)).symm
  | comp hg hh ih => exact ih (isEmpty_of_isAlphaPCover hp hg h)

/-- **The source of an iterated `α_p`-cover is empty only if its target is**, which is the form
the hypothesis of [Stacks, Lemma 60.25.4, Tag 07Q9] takes.  Around a point of the target the
cover restricts to a composition of `α_p`-covers, so `isEmpty_of_isAlphaPCoverComposite` empties
the neighbourhood the point lies in. -/
theorem isEmpty_of_isIteratedAlphaPCover {p : ℕ} (hp : p ≠ 0) {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsIteratedAlphaPCover p f) (h : IsEmpty X') : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, hcomp⟩ := hf.2 x
  have hpre : IsEmpty ((f ⁻¹ᵁ U).toScheme) :=
    Function.isEmpty (Scheme.Opens.ι (f ⁻¹ᵁ U)).base
  exact (isEmpty_of_isAlphaPCoverComposite hp hcomp hpre).elim ⟨x, hxU⟩

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### What the conclusion of [Stacks, Tag 07Q9] gives for the cokernel on its own -/

section Abstract

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- **The cokernel bound with the exponent the concentration of `E` in degrees `≥ -1` buys, and
nothing beyond it.**  For a distinguished triangle `A ⟶ B ⟶ E ⟶ A⟦1⟧` in `D(𝒜)` with `A` and `B`
concentrated in degrees `≥ 0` — which is all the triangle of [Stacks, Lemma 60.25.4, Tag 07Q9]
offers for free — and with every cohomology object of `E` in degree `≤ i` annihilated by `q`,
the scalar `q^{i + 2}` times any morphism `P ⟶ B` out of an object concentrated in degrees `≤ i`
factors through `A ⟶ B`.

This is `...SmallSite.exists_comp_mor₁_eq_pow_smul_07QA` with its concentration hypothesis
`E` in degrees `≥ 0` replaced by the automatic `≥ -1` of
`Stacks.Triangulated.isGE_obj₃_sub_one`, and the exponent accordingly one larger: the filtration
runs over the `i + 2` degrees `-1, 0, …, i`.  Compare
`...SmallSite.exists_comp_mor₁_eq_pow_smul_07QA_of_mono`, which recovers the source's `q^{i + 1}`
from the injectivity of `ℋ^0(A) ⟶ ℋ^0(B)`; the two differ by exactly one power of `q`, and that
is the whole arithmetic weight of that injectivity. -/
theorem exists_comp_mor₁_eq_pow_smul_07QA_of_isGE_neg_one (q i : ℕ)
    (T : Triangle (DerivedCategory 𝒜)) (hT : T ∈ distTriang (DerivedCategory 𝒜))
    [T.obj₁.IsGE 0] [T.obj₂.IsGE 0]
    (hE : ∀ j : ℤ, j ≤ (i : ℤ) →
      (q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₃) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE (i : ℤ)] (g : P ⟶ T.obj₂) :
    ∃ h : P ⟶ T.obj₁, ((q : ℤ) ^ (i + 2)) • g = h ≫ T.mor₁ := by
  have : T.obj₃.IsGE (-1) := by
    have h := Stacks.Triangulated.isGE_obj₃_sub_one T hT 0
    rwa [zero_sub] at h
  obtain ⟨h, hh⟩ := Stacks.Triangulated.exists_comp_mor₁_eq_pow_smul
    (𝒜 := 𝒜) (q : ℤ) (-1) (i : ℤ) T hT hE P g
  refine ⟨h, ?_⟩
  have hexp : ((i : ℤ) - (-1)).toNat + 1 = i + 2 := by omega
  rw [← hh, hexp]

end Abstract

section Registered

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

/-- **The kernel bound of [Stacks, Tag 07QA] for an abelian sheaf, from `Statement07Q9`.**
For `f : X' ⟶ X` an iterated `α_p`-cover of constant degree `q` over the closed fibre of a
divided power base, and for any abelian sheaf `ℱ` on `Cris(X/S)`, the kernel of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`

is annihilated by `q^{i + 1}`.

The source's own proof is used: the third term `E` of the distinguished triangle of
[Stacks, Lemma 60.25.4, Tag 07Q9] has cohomology sheaves annihilated by `q` and is concentrated
in degrees `≥ -1`, the kernel is a quotient of `H^{i - 1}(X_Zar, E)`, and the filtration of that
group runs over the `i + 1` degrees `-1, 0, …, i - 1`.  `h07Q9` is
[Stacks, Lemma 60.25.4, Tag 07Q9] itself, in the library's rendering `...SmallSite.Statement07Q9`
of it, and `hcover` and `hdeg` are the two geometric hypotheses it is applied to; the prime, its
primality, the `ℤ_(p)`-structure of the base and the local nilpotence of `p` are part of
`Crystalline.GlobalCrystallineSituation`.

Everything between the abstract bound and `f^*` is a theorem of this library: the commutation
`...SmallSite.crisZariskiSquare` of the square of topoi, the coherence
`...SmallSite.crisZariskiLerayCoherence` of the two Leray factorizations across it, and the
corepresentation `...SmallSite.derivedZariskiGlobalSectionsHomologyShiftAddEquiv` of Zariski
hypercohomology with its naturality. -/
theorem pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA_of_statement07Q9 (q i : ℕ)
    (h07Q9 : Statement07Q9 S S' fS fX hf q)
    (hcover : IsIteratedAlphaPCover S'.p fX) (hdeg : HasConstantDegree fX q)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (x : (cohomologyFunctor S' i).obj F)
    (hx : crisCohomologyMap S S' fS fX hf F i x = 0) :
    ((q : ℤ) ^ (i + 1)) • x = 0 :=
  pow_smul_eq_zero_of_crisCohomologyMap_eq_zero_07QA S S' fS fX hf q i F
    (h07Q9 hcover hdeg (crisZariskiSquare S S' fS fX hf) F) x hx

/-- **The cokernel bound of [Stacks, Tag 07QA] for an abelian sheaf, from `Statement07Q9`.**
In the same situation, `q^{i + 1}` times any class in `H^i(Cris(X'/S), ℱ')` is in the image of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`.

The cokernel injects into `H^i(X_Zar, E)` for `E` the third term of the triangle of
[Stacks, Lemma 60.25.4, Tag 07Q9]; the filtration of that group runs over the degrees
`-1, 0, …, i`, and the source's exponent `q^{i + 1}` rather than `q^{i + 2}` is the statement
that the degree `-1` step is absent.  `ℋ^{-1}(E)` is the kernel of
`ℋ^0(Ru_{X/S, *}ℱ) ⟶ ℋ^0(Rf_{Zar, *}Ru_{X'/S, *}ℱ')`, which
`...SmallSite.mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` identifies with
`u_{X/S, *}` of the crystalline unit `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ`, so `hmono` is exactly that
absence.  For a crystal in quasi-coherent modules and the module pullback the corresponding
injectivity is the theorem
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`, from the
splitness of `D ⟶ D'` of [Stacks, Lemma 60.25.3, Tag 07N1]; for an arbitrary abelian sheaf it is
carried here as `hmono`. -/
theorem exists_crisCohomologyMap_eq_pow_smul_07QA_of_statement07Q9 (q i : ℕ)
    (h07Q9 : Statement07Q9 S S' fS fX hf q)
    (hcover : IsIteratedAlphaPCover S'.p fX) (hdeg : HasConstantDegree fX q)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hmono : Mono ((zariskiDirectImage S').map (crisUnit S S' fS fX hf F)))
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y = crisCohomologyMap S S' fS fX hf F i x :=
  exists_crisCohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit S S' fS fX hf q i F
    (h07Q9 hcover hdeg (crisZariskiSquare S S' fS fX hf) F) hmono y

/-! ### The cokernel bound with the exponent `q^{i + 2}`, with no hypothesis on `ℋ^0` -/

/-- **The cokernel bound on Zariski hypercohomology groups with exponent `q^{i + 2}`.**  Granting
the conclusion of [Stacks, Lemma 60.25.4, Tag 07Q9] and nothing else, `q^{i + 2}` times any class
in `H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')` is in the image of

`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`.

This is `...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA` with its monomorphism
hypothesis removed and the exponent raised by one, through
`exists_comp_mor₁_eq_pow_smul_07QA_of_isGE_neg_one`.  Together the two say that the injectivity
of `ℋ^0` of the comparison map is worth exactly one power of `q` in the cokernel bound, and
nothing else. -/
theorem exists_hypercohomologyMap_eq_pow_smul_07QA_pow_add_two (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (y : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj
        ((derivedZariskiPushforwardFunctor S S' fX).obj
          ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))))) :
    ∃ x, ((q : ℤ) ^ (i + 2)) • y =
      zariskiHypercohomologyComparisonMap S S' fS fX hf F i x := by
  set α := derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F
  obtain ⟨E, v, wE, hT⟩ := distinguished_cocone_triangle α
  set T := (DerivedCategory.Plus.ι
    (C := Sheaf (opensTopology S') AddCommGrpCat.{u + 1})).mapTriangle.obj
      (Triangle.mk α v wE)
  have hT₀ : T ∈ distTriang (DerivedCategory (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})) :=
    DerivedCategory.Plus.ι.map_distinguished _ hT
  have : ((derivedZariskiDirectImage S').obj F).IsGE 0 :=
    isGE_derivedZariskiDirectImage_obj S' F
  have : ((derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))).IsGE 0 :=
    isGE_derivedZariskiPushforward_obj S S' fX (crisPullback S S' fS fX hf F)
  have : T.obj₁.IsGE 0 := inferInstanceAs
    ((DerivedCategory.Plus.ι.obj ((derivedZariskiDirectImage S').obj F)).IsGE 0)
  have : T.obj₂.IsGE 0 := inferInstanceAs
    ((DerivedCategory.Plus.ι.obj ((derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F)))).IsGE 0)
  have hE : ∀ j : ℤ, j ≤ (i : ℤ) →
      ((q : ℤ) • 𝟙 ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj T.obj₃) = 0) := fun j _ =>
    smul_id_homologyFunctor_ι_obj₃_eq_zero S' q hann v wE hT j
  obtain ⟨h, hh⟩ := exists_comp_mor₁_eq_pow_smul_07QA_of_isGE_neg_one q i T hT₀ hE
    (zariskiUnitShift S' (i : ℤ))
    ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
      ((derivedZariskiPushforwardFunctor S S' fX).obj
        ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))) (i : ℤ)) y)
  refine ⟨(derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
    ((derivedZariskiDirectImage S').obj F) (i : ℤ)).symm h, ?_⟩
  apply (derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
    ((derivedZariskiPushforwardFunctor S S' fX).obj
      ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))) (i : ℤ)).injective
  have e2 := derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality S' α (i : ℤ)
    ((derivedZariskiGlobalSectionsHomologyShiftAddEquiv S'
      ((derivedZariskiDirectImage S').obj F) (i : ℤ)).symm h)
  refine (map_zsmul _ _ _).trans (hh.trans (Eq.trans ?_ e2.symm))
  exact congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map α)
    (AddEquiv.apply_symm_apply _ h).symm

/-- **The cokernel bound on the crystalline cohomology groups with exponent `q^{i + 2}`.**
Granting the conclusion of [Stacks, Lemma 60.25.4, Tag 07Q9] and nothing else, `q^{i + 2}` times
any class in `H^i(Cris(X'/S), ℱ')` is in the image of

`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')`.

`exists_hypercohomologyMap_eq_pow_smul_07QA_pow_add_two` transported along the two Leray
isomorphisms of `SmallSite/CrisCohomologyBound07QA.lean`, which carry nothing. -/
theorem exists_crisCohomologyMap_eq_pow_smul_07QA_pow_add_two (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    ∃ x, ((q : ℤ) ^ (i + 2)) • y = crisCohomologyMap S S' fS fX hf F i x := by
  obtain ⟨z, hz⟩ := exists_hypercohomologyMap_eq_pow_smul_07QA_pow_add_two S S' fS fX hf q i F
    hann (crisCohomologyZariskiHypercohomologyPushforwardAddEquiv S S' fS fX hf F i y)
  refine ⟨(crisCohomologyZariskiHypercohomologyAddEquiv S' F i).symm z, ?_⟩
  apply (crisCohomologyZariskiHypercohomologyPushforwardAddEquiv S S' fS fX hf F i).injective
  rwa [map_zsmul,
    ← zariskiHypercohomologyComparisonMap_crisCohomologyZariskiHypercohomologyAddEquiv,
    AddEquiv.apply_symm_apply]

/-- **The cokernel bound with exponent `q^{i + 2}` under the source's hypotheses.**  The same
statement as `exists_crisCohomologyMap_eq_pow_smul_07QA_of_statement07Q9` but with the exponent
raised by one and `hmono` dropped: this is what [Stacks, Lemma 60.25.4, Tag 07Q9] yields for the
cokernel on its own, and the comparison of the two exponents is what pins down what `hmono`
contributes. -/
theorem exists_crisCohomologyMap_eq_pow_smul_07QA_of_statement07Q9_pow_add_two (q i : ℕ)
    (h07Q9 : Statement07Q9 S S' fS fX hf q)
    (hcover : IsIteratedAlphaPCover S'.p fX) (hdeg : HasConstantDegree fX q)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (y : (cohomologyFunctor S i).obj (crisPullback S S' fS fX hf F)) :
    ∃ x, ((q : ℤ) ^ (i + 2)) • y = crisCohomologyMap S S' fS fX hf F i x :=
  exists_crisCohomologyMap_eq_pow_smul_07QA_pow_add_two S S' fS fX hf q i F
    (h07Q9 hcover hdeg (crisZariskiSquare S S' fS fX hf) F) y

end Registered

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
