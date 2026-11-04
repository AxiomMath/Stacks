module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessResolution.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.DifferenceSequences
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmbeddedPointStep
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# The inductive step of Tag 0BEM, assembled on the scheme-theoretic support

[Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) is reduced by
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hasNoEmbeddedAssociatedPointsStep` to
[Stacks, Tag 02O6] and one geometric input: the first-difference identity
`AlgebraicGeometry.IsTwistDifferenceStep` for a coherent sheaf **without embedded associated
points**. This file supplies that input, and therefore reduces the tag to Tag 02O6 alone.

The identity is produced where [Stacks, Tag 02P2] applies — on a scheme without embedded points,
for a coherent sheaf of full support — and carried to an arbitrary coherent sheaf by the source's
own two moves:

* [Stacks, Tag 02OM]: replace `X` by the closed subscheme `Z` cut out by the annihilator of `𝒢`.
  There `𝒢` becomes a coherent sheaf `𝒢'` of *full* support with `i_*𝒢' ≅ 𝒢`, and `Z` has no
  embedded points, so [Stacks, Tag 02OZ] case (3) supplies the regular meromorphic section of
  `i^*𝓛_j` that Tag 02P2 needs.
* [Stacks, Tag 02OL], applied **on `Z`**: `𝒢'` itself is not known to have no embedded associated
  points — that is clause (b) of Tag 02OM, which the library does not have, being blocked on
  [Stacks, Tag 05EY] — so the embedded associated points are removed downstairs instead, by
  `AlgebraicGeometry.isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints` at the side condition
  *full support*. That side condition passes through the reduction because the Tag 02OL quotient
  has the same support as the sheaf it replaces, which is exactly what that theorem's
  support-invariance hypothesis asks.

The passage back to `X` is the content of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/PushforwardTwist.lean`: the twisted Euler
characteristic, the support, its dimension and relative nowhere density are all unchanged by
`i_*` along a closed immersion.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `isNowhereDense_preimage_val_of_eq_univ`: inside a *full* support, relative nowhere density is
  nowhere density in the scheme.
* `isTwistDifferenceStep_of_supp_eq_univ_of_hasNoEmbeddedAssociatedPoints`: the first-difference
  identity on a scheme without embedded points, for a coherent sheaf of full support without
  embedded associated points — [Stacks, Tag 02P2] read as a difference of Euler characteristics.
* `isTwistDifferenceStep_of_supp_eq_univ`: the same with the embedded associated points removed by
  [Stacks, Tag 02OL].
* `isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints`: **the first-difference identity for a
  coherent sheaf without embedded associated points on an arbitrary proper scheme over a field**,
  given [Stacks, Tag 02O6]. This is the remaining hypothesis of
  `exists_eulerPolynomial_twistedSheaf_of_hasNoEmbeddedAssociatedPointsStep`.
* `exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology`: **[Stacks, Tag 0BEM]
  from [Stacks, Tag 02O6] alone.**

## What Tag 0BEM owes after this file

`hfin`, which is [Stacks, Tag 02O6]: finite-dimensionality over `k` of the cohomology of a
coherent sheaf on a proper scheme over a field. It is carried as a hypothesis by every statement
below and by every statement they are built from, and nothing else is outstanding: `hfin` is the
only hypothesis of `exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` beyond
properness and the invertibility of the twisting sheaves, which are part of the tag's own
statement.

Tag 02O6 is **proved** in this library, as
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, and over a field it is
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, which is exactly
`hfin`. So Tag 0BEM is settled outright; the unconditional statement, with the attribute, is
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper` in
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/EulerPolynomialProper.lean`. The statements here are
left with `hfin` so that their consumers can continue to supply it from whichever form of
Tag 02O6 is at hand.

## Implementation notes

**Why the side condition of the Tag 02OL reduction is `Supp 𝒢 = univ` and not `True`.** On `Z`
the difference sequences exist only for a sheaf of full support, because that is what Tag 02P2
needs; so the step available on `Z` is not the unconditional one, and the unconditional form of
`isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints` cannot be fed. The predicate-indexed
form can, and the only property of the predicate it uses is that it is determined by the support.

**Why `Supp 𝒢' ≠ ∅` is not needed.** `AlgebraicGeometry.natDimSupp` has a junk value on empty
support, and the step's hypothesis is `natDimSupp 𝒢 ≠ 0`; it transports to `Z` because
`natDimSupp` is a function of the support alone and the support is carried by
`natDimSupp_pushforward_of_isClosedImmersion` together with `SheafOfModules.supp_eq_of_iso`.

**Why the coherence arguments are written out with `@`.** `AlgebraicGeometry.eulerCharacteristic`
takes the coherence of its sheaf as an instance argument, and
`AlgebraicGeometry.IsTwistDifferenceStep` fixes which *term* appears there. The bridge lemmas
`eulerCharacteristic_twistedSheaf_eq_of_iso` and
`eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion` take those terms explicitly,
so each bridge can be made to match the goal syntactically and the identity closes by `rw`; the
alternative, relying on the proof irrelevance of `SheafOfModules.IsCoherent` to make `linarith`
identify the atoms, is not something `rw` motives respect.

**No attribute is attached here, and the declaration that carries it is named.** Tag 0BEM's
statement is unconditional, while
`exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` carries `hfin` — Tag 02O6 —
as a hypothesis. By the covering-set rule the attribute is therefore
withheld here: the statement has a hypothesis the tag does not. It sits instead on
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`, which is that statement with
`hfin` discharged from Tag 02O6 — the single declaration whose conclusion is the whole of the
tag's statement. Tags 02OL, 02OM, 02OZ, 02O6 and 02P2 are attached where they are proved; nothing
here states a clause of any of them.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### An invariance lemma -/

/-- **Inside a full support, relative nowhere density is nowhere density in the scheme.** The
inclusion of `Set.univ` is a homeomorphism, and nowhere density is a homeomorphism invariant
(`Homeomorph.isNowhereDense_image_iff`).

The ambient subset is a free variable so that the hypothesis `S = Set.univ` is discharged by
`subst` here rather than by a rewrite in a *type* position at the use site, which is the same
device as `AlgebraicGeometry.isNowhereDense_preimage_val_congr`. -/
theorem isNowhereDense_preimage_val_of_eq_univ {Y : Type*} [TopologicalSpace Y] {S T : Set Y}
    (hS : S = Set.univ) (hT : IsNowhereDense T) :
    IsNowhereDense ((Subtype.val : ↥S → Y) ⁻¹' T) := by
  subst hS
  have himage : (Subtype.val : ↥(Set.univ : Set Y) → Y) ⁻¹' T =
      (Homeomorph.Set.univ Y).symm '' T :=
    Set.ext fun a => ⟨fun ha => ⟨(a : Y), ha, rfl⟩, fun ⟨_, hb, hba⟩ => hba ▸ hb⟩
  rw [himage, Homeomorph.isNowhereDense_image_iff]
  exact hT

/-! ### The step on a scheme without embedded points -/

section SuppUniv

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **The first-difference identity of [Stacks, Tag 0BEM] on a scheme without embedded points,
for a coherent sheaf of full support without embedded associated points.**

[Stacks, Tag 02OZ] case (3) supplies a regular meromorphic section of `𝓛ᵢ`,
`AlgebraicGeometry.exists_differenceSequences_of_supp_eq_univ` turns it into the two difference
sequences of [Stacks, Tag 02P2], and
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_update_sub_eq_of_differenceSequences` reads
those as the first difference. The two support-dimension drops are carried in the nowhere-dense
form `AlgebraicGeometry.IsTwistDifferenceStep` asks for: Tag 02P2's exceptional subset is nowhere
dense in the scheme, and for a sheaf of full support that is nowhere density inside the
support. -/
theorem isTwistDifferenceStep_of_supp_eq_univ_of_hasNoEmbeddedAssociatedPoints [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (hX : HasNoEmbeddedPoints X) :
    IsTwistDifferenceStep k f L (fun G => _root_.SheafOfModules.supp G = Set.univ ∧
      HasNoEmbeddedAssociatedPoints G) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro G hG hP hG0 i
  obtain ⟨hsupp, hemb⟩ := hP
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints X hX (L i)
  obtain ⟨S, T, hS, hT, cS1, cS2, cS3, cT1, cT2, cT3, ⟨eS⟩, ⟨eT⟩, ⟨e01⟩, ndS, ndT, -, -⟩ :=
    exists_differenceSequences_of_supp_eq_univ k f (L i) G hG hG0 hemb hsupp s hs
  refine ⟨T.X₃, S.X₃, cT3, cS3, ?_, ?_, ?_, ?_, fun n =>
    eulerCharacteristic_twistedSheaf_update_sub_eq_of_differenceSequences k f L hfin G hG i
      hS hT cS1 cS2 cS3 cT1 cT2 cT3 eS eT e01 n⟩
  · exact hsupp ▸ Set.subset_univ _
  · exact isNowhereDense_preimage_val_of_eq_univ hsupp ndT
  · exact hsupp ▸ Set.subset_univ _
  · exact isNowhereDense_preimage_val_of_eq_univ hsupp ndS

/-- **The first-difference identity of [Stacks, Tag 0BEM] on a scheme without embedded points,
for a coherent sheaf of full support.** The embedded associated points are removed by
[Stacks, Tag 02OL], through
`AlgebraicGeometry.isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints` at the side condition
*full support* — which that reduction carries because the Tag 02OL quotient has the same support
as the sheaf it replaces. -/
theorem isTwistDifferenceStep_of_supp_eq_univ [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (hX : HasNoEmbeddedPoints X) :
    IsTwistDifferenceStep k f L
      (fun G => _root_.SheafOfModules.supp G = Set.univ) :=
  isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints k f L hfin
    (fun _ _ hAB hB => hAB.trans hB)
    (isTwistDifferenceStep_of_supp_eq_univ_of_hasNoEmbeddedAssociatedPoints k f L hfin hX)

end SuppUniv

/-! ### The step on an arbitrary proper scheme, and Tag 0BEM from Tag 02O6 -/

section Assembly

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **The first-difference identity of [Stacks, Tag 0BEM] for a coherent sheaf without embedded
associated points**, on an arbitrary scheme proper over a field, given [Stacks, Tag 02O6].

This is the source's second and third paragraphs. [Stacks, Tag 02OM] replaces `X` by the closed
subscheme `Z` cut out by the annihilator of `𝒢`, on which `𝒢` becomes a coherent sheaf `𝒢'` of
full support with `i_*𝒢' ≅ 𝒢`, and `Z` has no embedded points;
`AlgebraicGeometry.isTwistDifferenceStep_of_supp_eq_univ` is the identity there, for the pulled
back twisting sheaves. It is read back on `X` by the four invariance statements of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/PushforwardTwist.lean`: the twisted Euler
characteristic (`eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`), the support
(`supp_pushforward_of_isClosedImmersion`), its dimension
(`natDimSupp_pushforward_of_isClosedImmersion`) and relative nowhere density
(`isNowhereDense_preimage_val_supp_pushforward_iff`).

Tag 02O6 is needed *downstairs* as well as upstairs, and is not an extra hypothesis:
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion` transports
it along the closed immersion. -/
theorem isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m)) :
    IsTwistDifferenceStep k f L HasNoEmbeddedAssociatedPoints := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro G hG hemb hG0 i
  have _hGc : G.IsCoherent := hG
  set ι := (annihilatorIdeal G).subschemeι with hι
  obtain ⟨hZ, G', hG'c, hG'supp, ⟨e⟩⟩ :=
    exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints G hemb
  have _hG'c : G'.IsCoherent := hG'c
  -- the closed subscheme of Tag 02OM, its structure morphism and the pulled back twisting sheaves
  have hinv : ∀ j, SheafOfModules.IsInvertible
      (annihilatorIdeal G).subscheme.presheaf (annihilatorIdeal G).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback ι).obj (L j)) :=
    fun j => SheafOfModules.isInvertible_pullback ι (L j)
  have hfin' := forall_finiteDimensional_cohomologyOverField_of_isClosedImmersion k f
    ι hfin
  -- the support, and hence the descent measure, is unchanged
  have hsuppG : _root_.SheafOfModules.supp ((Scheme.Modules.pushforward
      ι).obj G') = _root_.SheafOfModules.supp G :=
    _root_.SheafOfModules.supp_eq_of_iso e
  have hdimG : natDimSupp ((Scheme.Modules.pushforward
      ι).obj G') = natDimSupp G := by
    unfold natDimSupp
    rw [hsuppG]
  have hG'0 : natDimSupp G' ≠ 0 := by
    rw [← natDimSupp_pushforward_of_isClosedImmersion ι G', hdimG]
    exact hG0
  obtain ⟨G₁, G₂, c₁, c₂, hs₁, hnd₁, hs₂, hnd₂, hid⟩ :=
    isTwistDifferenceStep_of_supp_eq_univ k (ι ≫ f)
      (fun j => (Scheme.Modules.pullback ι).obj (L j)) hfin' hZ
      G' hG'c hG'supp hG'0 i
  have _hc₁ : G₁.IsCoherent := c₁
  have _hc₂ : G₂.IsCoherent := c₂
  -- support containment and relative nowhere density are read back on `X`
  have back : ∀ H : (annihilatorIdeal G).subscheme.Modules,
      _root_.SheafOfModules.supp H ⊆ _root_.SheafOfModules.supp G' →
      IsNowhereDense ((Subtype.val : ↥(_root_.SheafOfModules.supp G') → _) ⁻¹'
        _root_.SheafOfModules.supp H) →
      _root_.SheafOfModules.supp ((Scheme.Modules.pushforward ι).obj H) ⊆
        _root_.SheafOfModules.supp G ∧
      IsNowhereDense ((Subtype.val : ↥(_root_.SheafOfModules.supp G) → _) ⁻¹'
        _root_.SheafOfModules.supp ((Scheme.Modules.pushforward ι).obj H)) :=
    fun H hs hnd => ⟨by
      rw [supp_pushforward_of_isClosedImmersion]
      exact (Set.image_mono hs).trans
        ((supp_pushforward_of_isClosedImmersion _ G').symm.trans hsuppG).subset,
      isNowhereDense_preimage_val_congr hsuppG
        ((isNowhereDense_preimage_val_supp_pushforward_iff _ G' H).mpr hnd)⟩
  refine ⟨(Scheme.Modules.pushforward ι).obj G₁,
    (Scheme.Modules.pushforward ι).obj G₂, isCoherent_pushforward_of_isClosedImmersion ι G₁,
    isCoherent_pushforward_of_isClosedImmersion ι G₂,
    (back G₁ hs₁ hnd₁).1, (back G₁ hs₁ hnd₁).2, (back G₂ hs₂ hnd₂).1, (back G₂ hs₂ hnd₂).2,
    fun n => ?_⟩
  -- each of the four Euler characteristics is computed on `Z`
  have bridge : ∀ (N : (annihilatorIdeal G).subscheme.Modules) [hN : N.IsCoherent]
      (m : Fin r → ℤ),
      @eulerCharacteristic k _ X f _ (twistedSheaf ((Scheme.Modules.pushforward ι).obj N) L m)
          (@twistedSheaf_isCoherent X r _ L _
            (isCoherent_pushforward_of_isClosedImmersion ι N) m)
        = @eulerCharacteristic k _ (annihilatorIdeal G).subscheme (ι ≫ f) _
            (twistedSheaf N (fun j => (Scheme.Modules.pullback ι).obj (L j)) m)
            (@twistedSheaf_isCoherent _ r N _ _ hN m) :=
    fun N _ m => eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k ι f L N m _ _
  have eG : ∀ m : Fin r → ℤ,
      @eulerCharacteristic k _ X f _ (twistedSheaf G L m)
          (@twistedSheaf_isCoherent X r G L _ hG m)
        = @eulerCharacteristic k _ (annihilatorIdeal G).subscheme (ι ≫ f) _
            (twistedSheaf G' (fun j => (Scheme.Modules.pullback ι).obj (L j)) m)
            (@twistedSheaf_isCoherent _ r G' _ _ hG'c m) :=
    fun m => (eulerCharacteristic_twistedSheaf_eq_of_iso k f L hG
      (isCoherent_pushforward_of_isClosedImmersion ι G') e.symm m).trans (bridge G' m)
  rw [eG (Function.update n i (n i + 1)), eG n, bridge G₁ n, bridge G₂ n]
  exact hid n

/-- **[Stacks, Tag 0BEM] from [Stacks, Tag 02O6].** The Euler characteristics of the twists
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a scheme proper over a field are the
values of a rational polynomial which is zero or of total degree at most `dim Supp ℱ`.

The only hypothesis beyond the tag's own data is `hfin`, which is [Stacks, Tag 02O6]. Everything
else the source's proof uses — Tags 02OL, 02OM, 02OZ, 02P2, 089W and 01E8 — is proved and
discharged here.

No attribute: see the module docstring. Tag 02O6 is proved, so `hfin` is dischargeable, and the
tag attribute for Tag 0BEM sits on this declaration with `hfin` removed, namely on
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`. -/
theorem exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology [IsProper f]
    (hfin : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional k (cohomologyOverField k f G m))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (_root_.SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_hasNoEmbeddedAssociatedPointsStep k f L hfin
    (isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints k f L hfin) F hF

end Assembly

end AlgebraicGeometry

end
