module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentreExistence
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf

/-!
# Admissible blowups are stable under composition

Let `X` be a quasi-compact and quasi-separated scheme and `U ⊆ X` an open subscheme. If
`b : X' ⟶ X` is a `U`-admissible blowup and `b' : X'' ⟶ X'` is a `b⁻¹(U)`-admissible blowup,
then the composite `b' ≫ b : X'' ⟶ X` is a `U`-admissible blowup. That is [Stacks, Tag 080L],
whose proof there is one line: it is immediate from the more precise [Stacks, Tag 080B].

Unwinding the definition, `b` is the blowup of `X` in a finitely presented centre `I` supported
away from `U`, and `b'` is the blowup of `X'` in a finitely presented centre `K` supported away
from `b⁻¹(U)`. Transporting `K` across the identification of `X'` with the blowup of `X` in `I`
gives a centre `Z'` on that blowup, and the single centre exhibiting the composite as a blowup is
the product `I · J`, where `J` is an ideal sheaf on `X` whose inverse image on the blowup is
`E ^ d · Z'` for the exceptional ideal `E`. Everything then follows from the two halves of
[Stacks, Tag 080B]: the product centre is of finite presentation with support
`Supp I ∪ b(Supp Z')`, and the two-step blowup is the blowup in the product centre over `X`.

## Main definitions

* `Stacks.Blowup.SecondCentreFactorization`: the second-centre factorization of
  [Stacks, Tag 0803], written out as a `Prop` quantified over every quasi-compact
  quasi-separated base.  Nothing below consumes it — `…IsAdmissibleBlowup.comp` discharges the
  pair itself — but `AlgebraicGeometry.secondCentreFactorization` proves it and the flattening
  development carries it, so it is defined here, where both can see it.

## Main results

* `Stacks.Blowup.IsAdmissibleBlowup.comp_of_secondCentreIdeal`: the composite of a
  `U`-admissible blowup and a `b⁻¹(U)`-admissible blowup is a `U`-admissible blowup, from the
  second-centre ideal `J` on the base as an argument.
* `Stacks.Blowup.IsAdmissibleBlowup.comp`: **[Stacks, Tag 080L]** — the same statement with
  that argument supplied.
* `Stacks.Blowup.notMem_supportSet_of_secondCentreFactorization`: the ideal sheaf the
  factorization produces has no support outside `Supp I ∪ b(Supp Z')`.

## Implementation notes

### Where the second centre comes from

The pair `(d, J)` is `Stacks.Blowup.exists_secondCentre`, in
`StacksFrontier/AlgebraicGeometry/Blowup/SecondCentreExistence.lean`: it is the content of
[Stacks, Tag 0803] (Lemma 31.32.5) as used in the proof of [Stacks, Tag 080B], read at the Rees
algebra `⨁ Iⁿ` of the first centre. `Stacks.Blowup.IsAdmissibleBlowup.comp` below is tag 080L
with that pair supplied, and is where the project tag for 080L sits.

`Stacks.Blowup.IsAdmissibleBlowup.comp_of_secondCentreIdeal` is kept as the engine. Its
`secondCentreIdeal` argument is exactly, and only, the pair of properties `hJout` and `hcomap`
of the clauses of [Stacks, Tag 080B] in
`StacksFrontier/AlgebraicGeometry/Blowup/CompositeCentre.lean`, quantified over the centres on `X`
that the proof produces. Nothing more is consumed: the clauses `0 < d` and `J ≤ I ^ d` of the
cited lemma, and the stronger stalkwise agreement of `J` with `I ^ d` away from
`Supp I ∪ b(Supp Z')`, are all unused, and the argument is asked for over `X` alone rather than
over every quasi-compact quasi-separated scheme.

Quasi-compactness of `U` is not needed: it plays no role once the centres have been produced,
so both statements ask only that `U` be open. The source does state it, and it is a genuine
hypothesis of [Stacks, Tag 0803], so it is used inside `Stacks.Blowup.exists_secondCentre` —
but not by the bookkeeping below.

### The two blowup constructions

The predicate `Stacks.Blowup.IsAdmissibleBlowup` is phrased with `Stacks.Blowup.blowUp`, while
the results of [Stacks, Tag 080B] used here are phrased with `AlgebraicGeometry.blowUp`; the two
constructions are identified over the base by `Stacks.Blowup.isAdmissibleBlowup_iff`, which is
how the proof starts.

## References

* [Stacks Project, Tag 080L](https://stacks.math.columbia.edu/tag/080L)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

variable {X X' X'' : Scheme.{u}}

/-- A closed immersion cut out by an ideal sheaf is of finite presentation exactly when that
ideal sheaf is of finite type, by [Stacks, Tag 01TV]: the kernel of the inclusion of the closed
subscheme is the ideal sheaf itself. -/
private theorem finitePresentation_subschemeι_iff (I : X.IdealSheafData) :
    FinitePresentation I.subschemeι ↔ I.IsFiniteType := by
  rw [finitePresentation_iff_fg_ker, Scheme.IdealSheafData.ker_subschemeι]
  exact Iff.rfl

/-- Transporting a centre across an isomorphism transports its blowup: if the inverse image of
`Z` along an isomorphism `e` is `K`, then the blowup in `K` is isomorphic to the blowup in `Z`,
compatibly with the two blowup morphisms and `e`.

This is [Stacks, Tag 0805] for the flat morphism `e.hom`, whose base change along the blowup of
`Z` is an isomorphism. -/
private theorem exists_iso_blowUp_of_comap_eq {Y Y' : Scheme.{u}} (e : Y' ≅ Y)
    (Z : Y.IdealSheafData) (K : Y'.IdealSheafData) (hK : Z.comap e.hom = K) :
    ∃ g : AlgebraicGeometry.blowUp K ≅ AlgebraicGeometry.blowUp Z,
      g.hom ≫ AlgebraicGeometry.blowUpToBase Z =
        AlgebraicGeometry.blowUpToBase K ≫ e.hom := by
  subst hK
  obtain ⟨g, hg⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap e.hom Z
  have : IsIso g := hg.isIso_snd_of_isIso
  exact ⟨asIso g, hg.w.symm⟩

/-- A positive power of an ideal sheaf has the same support as the ideal sheaf itself, since the
support of a product is the union of the supports. -/
private theorem support_pow_of_pos (I : X.IdealSheafData) {d : ℕ} (hd : 0 < d) :
    (I ^ d).support = I.support := by
  induction d with
  | zero => exact absurd hd (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, zero_add, pow_one]
    · rw [pow_succ, Scheme.IdealSheafData.support_mul, ih hn, sup_idem]

/-- **The second-centre factorization of the cited Stacks Lemma 31.32.5 ([Stacks, Tag 0803]).**
For a finitely presented centre `I` on a quasi-compact and quasi-separated scheme `Y` and a
finitely presented centre `Z'` on its blowup, there are `d > 0` and a finite-type ideal sheaf
`J ≤ I ^ d` on `Y`, agreeing with `I ^ d` outside `Supp I ∪ b(Supp Z')`, whose inverse image on
the blowup is `E ^ d · Z'`.

This is the input that turns two successive blowups into one. It is proved by
`AlgebraicGeometry.secondCentreFactorization`, in a file importing this one, and the flattening
development carries it as a hypothesis.  `Stacks.Blowup.IsAdmissibleBlowup.comp` below does not:
it discharges the pair directly through `Stacks.Blowup.exists_secondCentre`.  It is quantified
over all
quasi-compact quasi-separated base schemes, because it is applied to bases produced inside the
proofs that use it. -/
def SecondCentreFactorization : Prop :=
  ∀ {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : Y.IdealSheafData), FinitePresentation I.subschemeι →
    ∀ Z' : (AlgebraicGeometry.blowUp I).IdealSheafData, FinitePresentation Z'.subschemeι →
      ∃ (d : ℕ) (J : Y.IdealSheafData), 0 < d ∧
        Scheme.IdealSheafData.IsFiniteType J ∧ J ≤ I ^ d ∧
        (∀ x : Y, x ∉ I.supportSet ∪
            (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet →
          AlgebraicGeometry.IdealSheafData.stalk J x =
            AlgebraicGeometry.IdealSheafData.stalk (I ^ d) x) ∧
        J.comap (AlgebraicGeometry.blowUpToBase I) =
          AlgebraicGeometry.exceptionalIdeal I ^ d * Z'

/-- **The ideal sheaf the second-centre factorization produces has no support outside
`Supp I ∪ b(Supp Z')`.** There it has the same stalk as `I ^ d`, whose support is that of `I`.

This is the shape in which the support hypothesis of
`AlgebraicGeometry.supportSet_mul_eq_union_image` consumes the factorization. -/
theorem notMem_supportSet_of_secondCentreFactorization {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (Z' : (AlgebraicGeometry.blowUp I).IdealSheafData) {d : ℕ} (hd : 0 < d)
    (J : Y.IdealSheafData)
    (hout : ∀ x : Y, x ∉ I.supportSet ∪
        (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet →
      AlgebraicGeometry.IdealSheafData.stalk J x =
        AlgebraicGeometry.IdealSheafData.stalk (I ^ d) x) :
    ∀ x : Y, x ∉ I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet → x ∉ J.supportSet := by
  intro x hx
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    ← AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support, hout x hx,
    AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support, support_pow_of_pos I hd]
  exact fun hxI ↦ hx (Set.mem_union_left _ hxI)

/-- The composite of a `U`-admissible blowup and a `b⁻¹(U)`-admissible blowup is a
`U`-admissible blowup, from the second-centre ideal as an argument. This is the engine of
[Stacks, Tag 080L]; `Stacks.Blowup.IsAdmissibleBlowup.comp` below is the tag itself, with the
argument supplied by `Stacks.Blowup.exists_secondCentre`. -/
theorem IsAdmissibleBlowup.comp_of_secondCentreIdeal [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (b : X' ⟶ X) (b' : X'' ⟶ X')
    (secondCentreIdeal : ∀ I : X.IdealSheafData, FinitePresentation I.subschemeι →
      ∀ Z' : (AlgebraicGeometry.blowUp I).IdealSheafData,
        FinitePresentation Z'.subschemeι →
          ∃ (d : ℕ) (J : X.IdealSheafData), J.IsFiniteType ∧
            (∀ x : X, x ∉ I.supportSet ∪
                (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet →
              x ∉ J.supportSet) ∧
            J.comap (AlgebraicGeometry.blowUpToBase I) =
              AlgebraicGeometry.exceptionalIdeal I ^ d * Z')
    (hb : IsAdmissibleBlowup U b) (hb' : IsAdmissibleBlowup (b ⁻¹ᵁ U) b') :
    IsAdmissibleBlowup U (b' ≫ b) := by
  rw [isAdmissibleBlowup_iff] at hb hb' ⊢
  obtain ⟨I, hI, hIU, e, he⟩ := hb
  obtain ⟨K, hK, hKU, e', he'⟩ := hb'
  obtain ⟨Z', hZ'def⟩ :
      ∃ Z' : (AlgebraicGeometry.blowUp I).IdealSheafData, Z' = K.comap e.inv := ⟨_, rfl⟩
  -- The transported centre is still of finite presentation, because finite type of an ideal
  -- sheaf is preserved by inverse images.
  have hZ'fp : FinitePresentation Z'.subschemeι := by
    rw [finitePresentation_subschemeι_iff, hZ'def]
    exact ((finitePresentation_subschemeι_iff K).1 hK).comap e.inv
  obtain ⟨d, J, hJ, -, hcomap⟩ := secondCentreIdeal I hI Z' hZ'fp
  -- The product centre is of finite presentation, with support `Supp I ∪ b(Supp Z')`; the
  -- factorization of the inverse image of `J` already forces that support identity.
  have hL : FinitePresentation (I * J).subschemeι := finitePresentation_mul_subschemeι I J hI hJ
  have hSupport : (I * J).supportSet =
      I.supportSet ∪ (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet :=
    supportSet_mul_eq_union_image I Z' d J hcomap
  -- The image of the support of `Z'` misses `U`, because the support of `K` misses `b⁻¹(U)`.
  have hImage : Disjoint (U : Set X)
      ((AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet) := by
    refine Set.disjoint_left.mpr ?_
    rintro x hxU ⟨z, hz, hzx⟩
    have hzK : e.inv z ∈ (K.support : Set X') := by
      have h : z ∈ (Z'.support : Set (AlgebraicGeometry.blowUp I)) := hz
      rw [hZ'def, Scheme.IdealSheafData.support_comap] at h
      exact h
    have hpoint : b (e.inv z) = (AlgebraicGeometry.blowUpToBase I) z := by
      have h := congrArg (fun f : X' ⟶ X => f (e.inv z)) he
      simpa [Scheme.Hom.comp_apply, e.inv_hom_id] using h.symm
    refine (Set.disjoint_left.mp hKU) ?_ hzK
    change b (e.inv z) ∈ (U : Set X)
    rw [hpoint, hzx]
    exact hxU
  have hLU : Disjoint (U : Set X) (((I * J).support : Set X)) := by
    change Disjoint (U : Set X) ((I * J).supportSet)
    rw [hSupport]
    exact Set.disjoint_union_right.mpr ⟨hIU, hImage⟩
  -- The two-step blowup is the blowup in the product centre, over `X`.
  obtain ⟨eBlow⟩ := nonempty_blowUpCompositionIso I Z' d J hcomap
  obtain ⟨g, hg⟩ := exists_iso_blowUp_of_comap_eq e Z' K (by
    rw [hZ'def, ← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id])
  refine ⟨I * J, hL, hLU, e' ≪≫ g ≪≫ (Over.forget X).mapIso eBlow, ?_⟩
  have hleft : eBlow.hom.left ≫ AlgebraicGeometry.blowUpToBase (I * J) =
      AlgebraicGeometry.blowUpToBase Z' ≫ AlgebraicGeometry.blowUpToBase I := eBlow.hom.w
  calc (e' ≪≫ g ≪≫ (Over.forget X).mapIso eBlow).hom ≫
        AlgebraicGeometry.blowUpToBase (I * J)
      = e'.hom ≫ g.hom ≫ eBlow.hom.left ≫ AlgebraicGeometry.blowUpToBase (I * J) := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
    _ = e'.hom ≫ (g.hom ≫ AlgebraicGeometry.blowUpToBase Z') ≫
          AlgebraicGeometry.blowUpToBase I := by
        rw [hleft, Category.assoc]
    _ = (e'.hom ≫ AlgebraicGeometry.blowUpToBase K) ≫
          e.hom ≫ AlgebraicGeometry.blowUpToBase I := by
        rw [hg, Category.assoc, Category.assoc]
    _ = b' ≫ b := by rw [he, he']

/-- **Stacks Project, Tag 080L.** Let `X` be a quasi-compact and quasi-separated scheme and
`U ⊆ X` an open subscheme. If `b : X' ⟶ X` is a `U`-admissible blowup and `b' : X'' ⟶ X'` is a
`b⁻¹(U)`-admissible blowup, then the composite `b' ≫ b : X'' ⟶ X` is a `U`-admissible blowup.

The single centre is the product of the first centre with the second-centre ideal of
`Stacks.Blowup.exists_secondCentre`, and the two halves of [Stacks, Tag 080B] do the rest. The
support clause that `…comp_of_secondCentreIdeal` asks for comes from
`AlgebraicGeometry.supportSet_mul_eq_union_image` together with
`AlgebraicGeometry.Scheme.IdealSheafData.support_mul`: the support of the product centre is the
support of the first centre together with the image of the support of the second, and it
contains the support of `J`. -/
@[stacks 080L]
theorem IsAdmissibleBlowup.comp [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (b : X' ⟶ X) (b' : X'' ⟶ X')
    (hb : IsAdmissibleBlowup U b) (hb' : IsAdmissibleBlowup (b ⁻¹ᵁ U) b') :
    IsAdmissibleBlowup U (b' ≫ b) := by
  refine IsAdmissibleBlowup.comp_of_secondCentreIdeal U b b' ?_ hb hb'
  intro K hKfp Y hYfp
  obtain ⟨d, J, -, hJft, -, hcomap⟩ := Stacks.Blowup.exists_secondCentre K
    ((finitePresentation_subschemeι_iff K).1 hKfp) Y
    ((finitePresentation_subschemeι_iff Y).1 hYfp)
  refine ⟨d, J, hJft, ?_, hcomap⟩
  intro x hx hxJ
  refine hx ?_
  have hsup : ((K * J).support : Set X) = (K.support : Set X) ∪ (J.support : Set X) :=
    (congrArg (fun T : TopologicalSpace.Closeds X ↦ (T : Set X))
      (Scheme.IdealSheafData.support_mul (I := K) (J := J))).trans
      (TopologicalSpace.Closeds.coe_sup _ _)
  have hmem : x ∈ (K * J).supportSet := by
    change x ∈ ((K * J).support : Set X)
    rw [hsup]
    exact Or.inr hxJ
  rwa [supportSet_mul_eq_union_image K Y d J hcomap] at hmem

end Stacks.Blowup

end
