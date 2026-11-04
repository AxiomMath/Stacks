module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.EtaleLifting

/-!
# Functoriality of the strict henselization
-/

@[expose] public section

universe u v w

/-!
# Functoriality of the strict henselization

Let `R` be a ring, let `Rsh` be a local `R`-algebra which is a filtered colimit of étale
`R`-algebras, let `Ssh` be a henselian local `R`-algebra, and let
`φ : ResidueField Rsh →+* ResidueField Ssh` be compatible with the residue maps of `R → Rsh` and
`R → Ssh`. Then there is exactly one `R`-algebra map `f : Rsh → Ssh` inducing `φ` on residue
fields, and it is a local ring map. Applied to strict henselizations `Rsh = R^sh` and
`Ssh = S^sh` of a local map of local rings `R → S`, this is Stacks 04GU: the unique local ring
map `R^sh → S^sh` over `R → S` inducing a prescribed `φ : κ₁^sep → κ₂^sep`.

The proof is the source's, namely that this follows from Lemma 08HR
(`Stacks.Henselian.EtaleLifting.algHom`). That lemma lifts a *residue datum* along an ind-étale
`R`-algebra `A`: given a prime `q ⊆ A` over `p = R ∩ 𝔪 Ssh` and a `κ(p)`-algebra map
`τ : κ(q) → κ(Ssh)`, there is exactly one `R`-algebra map `f : A → Ssh` with `q = f⁻¹(𝔪 Ssh)`
which induces `τ` on residue fields. Here the datum comes from the hypotheses at both of its
places, and each place is a lemma of this file:

* `q = 𝔪 Rsh`, and that it lies over `p` is `comap_maximalIdeal_eq_of_comp_residue_eq`, the one
  place where injectivity of `φ` is used: the image of `x : R` in `κ(Ssh)` is `φ` of its image in
  `κ(Rsh)`, so the one vanishes exactly when the other does, and the two structure maps therefore
  contract the maximal ideals to the same prime of `R`. (Neither structure map has to be assumed
  local, and `R` need not be local: that equality of contractions is all 08HR asks of them.)
* `τ` is `φ` itself. Indeed `κ(𝔪 Rsh)` is the fraction field of `Rsh ⧸ 𝔪 Rsh = ResidueField Rsh`,
  which is already a field, so `φ` factors through the canonical `Rsh → κ(𝔪 Rsh)`
  (`residueDatum`); and any such factorization is a `κ(p)`-algebra map because `φ` is
  compatible with the structure maps (`comp_residueFieldMapFib_eq`).

With the datum so described, 08HR's two conditions on `f` are the two conjuncts of this
conclusion: `InducesResidueMap (𝔪 Rsh) f τ` is `(residue Ssh) ∘ f = φ ∘ (residue Rsh)` because `τ`
factors `φ` (`inducesResidueMap_iff_comp_residue_eq`), and `𝔪 Rsh = f⁻¹(𝔪 Ssh)` is locality of `f`
(`isLocalHom_iff_maximalIdeal_eq_comap`). So 04GU is the case of 08HR in which the residue
extension is prescribed rather than forced — the difference from the henselization sibling 04GS,
where triviality of that extension is a hypothesis and `τ` is not a choice.

## Main results

* `Stacks.StrictHenselization.Functoriality.map`,
  `Stacks.StrictHenselization.Functoriality.comp_residue_map`,
  `Stacks.StrictHenselization.Functoriality.isLocalHom_map`,
  `Stacks.StrictHenselization.Functoriality.map_unique`: the map of
  `HenselianLocalRing.indEtaleAlgHomOfResidue` (Stacks 04GU), its two properties and its
  uniqueness.

## Implementation notes

Unlike in 04GS, nothing has to be said about `R` being local or the structure maps being local:
the prime `p = R ∩ 𝔪 Ssh` of Lemma 08HR is taken as it stands, and the only fact needed about it
is that `𝔪 Rsh` lies over it. The two lemmas that mention `p` therefore write it as that
contraction, so that 08HR's hypothesis on `p` is `rfl`.

The factorization of `φ` through `κ(𝔪 Rsh)` is the `Ideal.ResidueField.lift` of `residueDatum`,
rather than the isomorphism `ResidueField Rsh ≃+* κ(𝔪 Rsh)` it inverts: the two lemmas that use
it need nothing about the factorization beyond its defining equation `residueDatum_spec`, and are
stated for an arbitrary `τ` satisfying that equation.

Both conditions of 08HR are used, and each corresponds to one conjunct of the source's
conclusion: neither conjunct is needed to obtain the other.

## References

* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [StacksProject 08HR](https://stacks.math.columbia.edu/tag/08HR)
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
-/

namespace Stacks.StrictHenselization.Functoriality

open CategoryTheory IsLocalRing Stacks.Henselian.EtaleLifting



section

variable {R : Type u} {A : Type v} {S : Type w} {K : Type*}
  [CommRing R] [CommRing A] [CommRing S] [Field K]
  [IsLocalRing A] [IsLocalRing S] [Algebra R A] [Algebra R S]

/-- A ring map between local rings is local exactly when it pulls the maximal ideal back to the
maximal ideal. -/
private theorem isLocalHom_iff_maximalIdeal_eq_comap {F : Type*} [FunLike F A S]
    [RingHomClass F A S] (f : F) :
    IsLocalHom f ↔ maximalIdeal A = (maximalIdeal S).comap f := by
  simp only [Ideal.ext_iff, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  exact ⟨fun hf a => ⟨fun hu => hu.map f, hf.map_nonunit a⟩, fun h => ⟨fun a ha => (h a).2 ha⟩⟩

/-- **Where injectivity of `φ` enters.** If the residue fields of two local `R`-algebras are
related by a ring map `φ` compatible with the two structure maps, then the two maximal ideals
contract to the same prime of `R`: the image of `x : R` in `κ(S)` is `φ` of its image in `κ(A)`,
and `φ`, a map of fields, vanishes only at `0`. Neither structure map is assumed local, and `R`
is not assumed local. -/
private theorem comap_maximalIdeal_eq_of_comp_residue_eq (φ : ResidueField A →+* ResidueField S)
    (hφ : φ.comp ((residue A).comp (algebraMap R A)) = (residue S).comp (algebraMap R S)) :
    (maximalIdeal S).comap (algebraMap R S) = (maximalIdeal A).comap (algebraMap R A) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, ← residue_eq_zero_iff, ← residue_eq_zero_iff,
    ← show φ (residue A (algebraMap R A x)) = residue S (algebraMap R S x) from
      RingHom.congr_fun hφ x,
    map_eq_zero_iff φ φ.injective]

/-- **The residue datum of Tag 08HR at the maximal ideal, as a map of residue fields.** `κ(𝔪 A)`
is the fraction field of `A ⧸ 𝔪 A = ResidueField A`, which is already a field, so a ring map `φ`
out of `ResidueField A` to a field factors through the canonical map `A → κ(𝔪 A)`; this is that
factorization. -/
private noncomputable def residueDatum (φ : ResidueField A →+* K) :
    (maximalIdeal A).ResidueField →+* K :=
  Ideal.ResidueField.lift (maximalIdeal A) (φ.comp (residue A))
    (fun a ha => by
      rw [RingHom.mem_ker, RingHom.comp_apply, (residue_eq_zero_iff a).mpr ha, map_zero])
    (fun r hr => by
      simp only [Submonoid.mem_comap, RingHom.comp_apply, IsUnit.mem_submonoid_iff]
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff φ φ.injective).mpr
        ((residue_ne_zero_iff_isUnit r).mpr (notMem_maximalIdeal.mp hr))))

/-- `residueDatum φ` composed with the canonical map `A → κ(𝔪 A)` is `φ` composed with the
residue map of `A`. -/
private theorem residueDatum_spec (φ : ResidueField A →+* K) :
    (residueDatum φ).comp (algebraMap A (maximalIdeal A).ResidueField) = φ.comp (residue A) :=
  RingHom.ext fun x => by
    simp only [residueDatum, RingHom.comp_apply, Ideal.ResidueField.lift_algebraMap]

/-- An `R`-algebra map between local rings is local exactly when it pulls the maximal ideal back
to the maximal ideal. -/
private theorem isLocalHom_algHom_iff (f : A →ₐ[R] S) :
    IsLocalHom f ↔ maximalIdeal A = (maximalIdeal S).comap (f : A →+* S) := by
  rw [Ideal.comap_coe]; exact isLocalHom_iff_maximalIdeal_eq_comap f

/-- A factorization `τ` of `φ` through `A → κ(𝔪 A)` is a `κ(p)`-algebra map, for `p = R ∩ 𝔪 S`:
on the image of `R` in `κ(𝔪 A)` this is exactly the compatibility of `φ` with the two structure
maps. -/
private theorem comp_residueFieldMapFib_eq {φ : ResidueField A →+* ResidueField S}
    {τ : (maximalIdeal A).ResidueField →+* ResidueField S}
    (hτ : τ.comp (algebraMap A (maximalIdeal A).ResidueField) = φ.comp (residue A))
    (hφ : φ.comp ((residue A).comp (algebraMap R A)) = (residue S).comp (algebraMap R S)) :
    τ.comp (residueFieldMapFib (R := R) (A := A)
      ((maximalIdeal S).comap (algebraMap R S)) (maximalIdeal A)
        (comap_maximalIdeal_eq_of_comp_residue_eq φ hφ))
      = residueFieldMapBase ((maximalIdeal S).comap (algebraMap R S)) rfl := by
  refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun r => ?_)
  have hr : τ (algebraMap A (maximalIdeal A).ResidueField (algebraMap R A r))
      = residue S (algebraMap R S r) :=
    (RingHom.congr_fun hτ (algebraMap R A r)).trans (RingHom.congr_fun hφ r)
  simpa only [RingHom.coe_comp, Function.comp_apply, residueFieldMapFib,
    Ideal.ResidueField.map_algebraMap, residueFieldMapBase,
    Ideal.ResidueField.lift_algebraMap] using hr

/-- For a `τ` factoring `φ` through `A → κ(𝔪 A)`, Tag 08HR's residue condition on a ring map
`f : A → S` is the commuting square of residue fields prescribed by `φ`. -/
private theorem inducesResidueMap_iff_comp_residue_eq {φ : ResidueField A →+* ResidueField S}
    {τ : (maximalIdeal A).ResidueField →+* ResidueField S}
    (hτ : τ.comp (algebraMap A (maximalIdeal A).ResidueField) = φ.comp (residue A))
    (f : A →+* S) :
    InducesResidueMap (maximalIdeal A) f τ ↔ (residue S).comp f = φ.comp (residue A) := by
  rw [InducesResidueMap, hτ]
  exact eq_comm

end

section Map

variable {R : Type u} {Rsh : Type v} {Ssh : Type w} [CommRing R] [CommRing Rsh] [CommRing Ssh]
  [IsLocalRing Rsh] [HenselianLocalRing Ssh] [Algebra R Rsh] [Algebra R Ssh]
  (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
    (CommAlgCat.of R (ULift.{u} Rsh)))
  (φ : ResidueField Rsh →+* ResidueField Ssh)
  (hφ : φ.comp ((residue Rsh).comp (algebraMap R Rsh))
    = (residue Ssh).comp (algebraMap R Ssh))

/-- Tag 08HR's lift of `residueDatum φ` along the ind-étale `R`-algebra `Rsh`. -/
private noncomputable def map : Rsh →ₐ[R] Ssh :=
  Stacks.Henselian.EtaleLifting.algHom hind ((maximalIdeal Ssh).comap (algebraMap R Ssh)) rfl
    (maximalIdeal Rsh) (comap_maximalIdeal_eq_of_comp_residue_eq φ hφ) (residueDatum φ)
    (comp_residueFieldMapFib_eq (residueDatum_spec φ) hφ)

/-- `map` induces `φ` on residue fields. -/
private theorem comp_residue_map :
    (residue Ssh).comp (map hind φ hφ : Rsh →+* Ssh) = φ.comp (residue Rsh) :=
  (inducesResidueMap_iff_comp_residue_eq (residueDatum_spec φ) _).mp
    (Stacks.Henselian.EtaleLifting.inducesResidueMap_algHom hind _ rfl (maximalIdeal Rsh)
      (comap_maximalIdeal_eq_of_comp_residue_eq φ hφ) (residueDatum φ)
      (comp_residueFieldMapFib_eq (residueDatum_spec φ) hφ))

/-- `map` is a local ring map: 08HR's condition `𝔪 Rsh = f⁻¹(𝔪 Ssh)` *is* locality. -/
private theorem isLocalHom_map : IsLocalHom (map hind φ hφ) :=
  (isLocalHom_algHom_iff _).mpr
    (Stacks.Henselian.EtaleLifting.comap_maximalIdeal_algHom hind _ rfl (maximalIdeal Rsh)
      (comap_maximalIdeal_eq_of_comp_residue_eq φ hφ) (residueDatum φ)
      (comp_residueFieldMapFib_eq (residueDatum_spec φ) hφ))

/-- `map` is the only local `R`-algebra map `Rsh → Ssh` inducing `φ` on residue fields. -/
private theorem map_unique (f : Rsh →ₐ[R] Ssh) (hfloc : IsLocalHom f)
    (hf : (residue Ssh).comp (f : Rsh →+* Ssh) = φ.comp (residue Rsh)) :
    f = map hind φ hφ :=
  Stacks.Henselian.EtaleLifting.algHom_unique hind _ rfl (maximalIdeal Rsh)
    (comap_maximalIdeal_eq_of_comp_residue_eq φ hφ) (residueDatum φ)
    (comp_residueFieldMapFib_eq (residueDatum_spec φ) hφ) f
    ⟨(isLocalHom_algHom_iff f).mp hfloc,
      (inducesResidueMap_iff_comp_residue_eq (residueDatum_spec φ) (f : Rsh →+* Ssh)).mpr hf⟩

end Map

end Stacks.StrictHenselization.Functoriality

/-!
# Functoriality of the strict henselization

Let `R → S` be a local map of local rings, let `κ_R ⊆ κ₁^sep` and `κ_S ⊆ κ₂^sep` be separable
algebraic closures of the two residue fields, and let `R → R^sh` and `S → S^sh` be the
corresponding strict henselizations. A commutative square of fields

```
κ₁^sep --φ--> κ₂^sep
  ↑             ↑
 κ_R ---φ̄---> κ_S
```

over the residue field map `φ̄` of `R → S` determines a unique local ring map `f : R^sh → S^sh`
over `R → S` inducing `φ` on residue fields. Unlike the henselization (Lemma 04GS), the strict
henselization has many local maps over `R → S` — they are permuted by the Galois group of
`κ₂^sep` — and `φ` is exactly the datum that singles one out.

The statement proved here is the universal property that produces the map. Of the source ring
only that it is a ring is used; of `R^sh` only that it is local and a filtered colimit of étale
`R`-algebras; of `S^sh` only that it is henselian local. The prescribed map on residue fields is
a ring map `φ : ResidueField Rsh →+* ResidueField Ssh`, and the source's square is the single
hypothesis that `φ` is compatible with the two residue maps out of `R`.

## Main results

* `HenselianLocalRing.indEtaleAlgHomOfResidue`: for an ind-étale local `R`-algebra `Rsh`, a
  henselian local `R`-algebra `Ssh` and a compatible `φ`, the `R`-algebra map `Rsh → Ssh`
  inducing `φ` on residue fields, with
  `HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue`,
  `HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue` and
  `HenselianLocalRing.indEtaleAlgHomOfResidue_unique` saying that it induces `φ`, that it is
  local, and that it is the only such map.

## Implementation notes

*Departure from the source's form: the intermediate ring `S` is eliminated, as in Lemma 04GS.*
In the source's square `S` enters only through the composite `R → S → S^sh`, so carrying it
would make `IsLocalRing S` and the hypotheses saying that `S^sh` is a strict henselization of `S`
dead. `S^sh` is replaced by an arbitrary henselian local `R`-algebra `Ssh`. Lemma 04GU is the
instance `Rsh = R^sh`, `Ssh = S^sh` with `Algebra R Ssh` the composite of `R → S` and
`S → S^sh`, at which the vertical maps of the source's residue square are `κ_R → κ₁^sep` and
`κ_R → κ_S → κ₂^sep` and `hφ` is that square; an `R`-algebra map `R^sh → S^sh` is exactly a ring
map making the source's square of rings commute, so that square is the type of `f` and needs no
separate hypothesis.

*Departure: `R` is not assumed local, and neither structure map is assumed local.* Both are
consequences of `hφ` rather than hypotheses. Since `ResidueField Rsh` is a field, `φ` is
injective, so `hφ` gives `x ∈ (maximalIdeal Ssh).comap (algebraMap R Ssh)` if and only if
`x ∈ (maximalIdeal Rsh).comap (algebraMap R Rsh)`: the two structure maps contract the maximal
ideals to the same prime `p` of `R`, which is the hypothesis "`𝔪_{Rsh}` lies over
`p = R ∩ 𝔪_{Ssh}`" of Lemma 08HR, and which forces `IsLocalHom (algebraMap R Ssh)` as soon as
`algebraMap R Rsh` is local. When `R` is local and `R → Rsh` is local, `p = 𝔪_R` and `hφ` is
equivalent to `φ.comp (ResidueField.map (algebraMap R Rsh)) = ResidueField.map (algebraMap R Ssh)`,
which is the source's square literally; it is stated at the level of `R` so that no locality
instance is needed to write it down. Keeping `R` a bare ring is the generality of Lemma 08HR, and
is what lets Lemma 04GW apply the statement at a prime of an arbitrary ring without localizing
first.

*Locality of `f` is a conclusion, and uniqueness is among all `R`-algebra maps.* The second
conjunct alone implies the first: `residue Ssh (f a) = φ (residue Rsh a)` vanishes whenever
`residue Rsh a` does. So the `∃!` is equivalent to uniqueness among all `f : Rsh →ₐ[R] Ssh`
inducing `φ`, which is stronger than the source's uniqueness among local maps; `IsLocalHom f` is
nevertheless stated, because the source's conclusion asserts it and a user should not have to
re-derive it.

*The residue field is the local ring's own.* `ResidueField Rsh` is `IsLocalRing.ResidueField`,
the quotient by the maximal ideal, not `(maximalIdeal Rsh).ResidueField`; the two are isomorphic
and the second is the shape Lemma 08HR is phrased in, but the first is the intrinsic object and
the one the source's `κ₁^sep` is. Nothing is assumed about `ResidueField Rsh` being separably
closed, or `φ` being separable or algebraic: the lemma is true and used without that.

*Universes.* `R` and `Rsh` share a universe, the index category of the filtered colimit being
taken there, while the henselian target is in a universe of its own — as in Lemmas 04GS and 08HT.

Faithfulness to [StacksProject 04GU], point by point. (1) No hypothesis is dead, and each is
necessary: `hind` fails for `Rsh = K⟦t⟧`, `Ssh = K⟦u⟧` over `R = K`, where `φ = id` and both
`t ↦ 0` and `t ↦ u` induce it; `HenselianLocalRing Ssh` fails for `R = Ssh` the localization of
`ℤ` at `(5)`, `Rsh = R^h` and `φ = id`, since a root of `x² - 6` in `R^h` has no image; `hφ` is
equivalent to the existence half of the conclusion, being what `(residue Ssh).comp f = φ.comp
(residue Rsh)` says after composing with `algebraMap R Rsh`; and `φ` and `IsLocalRing Rsh` are
used by the conclusion itself. (2) The scalars and the base are the source's: `Rsh` and `Ssh` are
algebras over the ring `R` at the foot of the square, the filtered colimit is one of
`R`-algebras, `φ` is a map between the residue fields of `Rsh` and `Ssh` themselves, and the
unique map is a map of `R`-algebras — not of `Rsh`-algebras and not over a localization of `R`.
(3) The map the source names is pinned, not merely asserted to exist: `f` is the unique
`R`-algebra map whose induced map on residue fields is `φ`, which is the characterisation, and it
is genuinely a characterisation and not a formality — distinct `φ` give distinct `f`, so dropping
`φ` from the conclusion would make the statement false. (4) The instantiation is not degenerate:
`R = Rsh = Ssh = K` a field with `φ = RingHom.id` satisfies every hypothesis (`Field.henselian`;
`K` is étale over `K`, hence ind-étale by `CategoryTheory.ObjectProperty.le_ind`) with `f` the
identity, and the statement has content at `R` the localization of `ℤ` at `(5)`, `Rsh = R^sh` and
`Ssh` a strict henselization of `ℤ_[5]`, where the `φ` range over the embeddings
`𝔽_5^sep → 𝔽_5^sep` and produce the Galois orbit of local maps `R^sh → Ssh` over `R`.

## References

* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [StacksProject 08HR](https://stacks.math.columbia.edu/tag/08HR), the lemma the source deduces
  this from, available here as `Stacks.Henselian.EtaleLifting.algHom`
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS), the henselization sibling, in
  which the residue field map is forced rather than prescribed
* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP), existence of `R → R^sh`
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the strict henselization
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT), the isomorphism-level sibling

## Tags

strict henselization, henselization, henselian local ring, strictly henselian, separable
algebraic closure, ind-étale, étale algebra, filtered colimit, residue field, local ring map
-/



@[expose] public section

section

variable {R : Type u} {Rsh : Type v} {Ssh : Type w} [CommRing R] [CommRing Rsh] [CommRing Ssh]
  [IsLocalRing Rsh] [HenselianLocalRing Ssh] [Algebra R Rsh] [Algebra R Ssh]

open CategoryTheory IsLocalRing in
/-- **The map given by functoriality of the strict henselization** (Stacks 04GU). Let `R` be a
ring, let `Rsh` be a local `R`-algebra which is a filtered colimit of étale `R`-algebras, let
`Ssh` be a henselian local `R`-algebra, and let `φ : ResidueField Rsh →+* ResidueField Ssh` be
compatible with the residue maps of `R → Rsh` and `R → Ssh`. This is the `R`-algebra map
`f : Rsh → Ssh` inducing `φ` on residue fields; it is a local ring map, and is the only such map.
Applied to strict henselizations `Rsh = R^sh` and `Ssh = S^sh` of a local map of local rings
`R → S`, and to a map `φ : κ₁^sep → κ₂^sep` of separable algebraic closures over the residue field
map of `R → S`, it is the local ring map `R^sh → S^sh` over `R → S` inducing `φ`. -/
@[stacks 04GU "The map of the universal property: the target is an arbitrary
henselian local `R`-algebra `Ssh`, since the source's `S` enters only through the composite
`R → S → S^sh`, and of `R^sh` only locality and ind-étaleness — `(CommAlgCat.etale R).ind`, the
spelling of Lemma 04GP(3) — are used. The source's square of residue fields is `hφ`, stated at the
level of `R`; `R` local and both structure maps local are consequences of it, not hypotheses.
`isLocalHom_indEtaleAlgHomOfResidue`, `comp_residue_indEtaleAlgHomOfResidue` and
`indEtaleAlgHomOfResidue_unique` are its two properties and its uniqueness. See the module
docstring.", no_expose, ega "IV 18.8.8.1" "existence of A^hs->B", ega "IV 18.8.8"]
noncomputable def HenselianLocalRing.indEtaleAlgHomOfResidue
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rsh)))
    (φ : ResidueField Rsh →+* ResidueField Ssh)
    (hφ : φ.comp ((residue Rsh).comp (algebraMap R Rsh))
      = (residue Ssh).comp (algebraMap R Ssh)) :
    Rsh →ₐ[R] Ssh :=
  Stacks.StrictHenselization.Functoriality.map hind φ hφ

open CategoryTheory IsLocalRing in
/-- `HenselianLocalRing.indEtaleAlgHomOfResidue` induces `φ` on residue fields. -/
@[stacks 04GU "the defining property of `indEtaleAlgHomOfResidue`",
  ega "IV 18.8.8.1" "induces \\psi on residues", ega "IV 18.8.4" "partial"]
public theorem HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rsh)))
    (φ : ResidueField Rsh →+* ResidueField Ssh)
    (hφ : φ.comp ((residue Rsh).comp (algebraMap R Rsh))
      = (residue Ssh).comp (algebraMap R Ssh)) :
    (residue Ssh).comp
        (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ : Rsh →+* Ssh)
      = φ.comp (residue Rsh) :=
  Stacks.StrictHenselization.Functoriality.comp_residue_map hind φ hφ

open CategoryTheory IsLocalRing in
/-- `HenselianLocalRing.indEtaleAlgHomOfResidue` is a local ring map. -/
@[stacks 04GU "`indEtaleAlgHomOfResidue` is local, which the source asserts",
  ega "IV 18.8.8.1" "locality of A^hs->B"]
public theorem HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rsh)))
    (φ : ResidueField Rsh →+* ResidueField Ssh)
    (hφ : φ.comp ((residue Rsh).comp (algebraMap R Rsh))
      = (residue Ssh).comp (algebraMap R Ssh)) :
    IsLocalHom (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ) :=
  Stacks.StrictHenselization.Functoriality.isLocalHom_map hind φ hφ

open CategoryTheory IsLocalRing in
/-- `HenselianLocalRing.indEtaleAlgHomOfResidue` is the only local `R`-algebra map `Rsh → Ssh`
inducing `φ` on residue fields. -/
@[stacks 04GU "uniqueness of `indEtaleAlgHomOfResidue`", ega "IV 18.8.8.1" "uniqueness of A^hs->B"]
public theorem HenselianLocalRing.indEtaleAlgHomOfResidue_unique
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rsh)))
    (φ : ResidueField Rsh →+* ResidueField Ssh)
    (hφ : φ.comp ((residue Rsh).comp (algebraMap R Rsh))
      = (residue Ssh).comp (algebraMap R Ssh))
    (f : Rsh →ₐ[R] Ssh) (hfloc : IsLocalHom f)
    (hf : (residue Ssh).comp (f : Rsh →+* Ssh) = φ.comp (residue Rsh)) :
    f = HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ :=
  Stacks.StrictHenselization.Functoriality.map_unique hind φ hφ f hfloc hf

end

end

end

/-!
# Étale algebras and the strict henselization of a local ring

Stacks Tag 04GT (universal property of the strict henselization for etale algebras).

Let `phi : R -> S` be a local ring map of local rings. Let `kappa(S) subset kappa^sep`
be a separable algebraic closure of the residue field of `S` (Definition 2), and let
`S -> S^sh` be the strict henselization of `S` with respect to `kappa(S) subset kappa^sep`
(Definition 3). Let `R -> A` be an etale ring map, and let `q` be a prime ideal of `A`
lying over `m_R`, i.e. `q cap R = m_R`.

Given a field homomorphism `phibar : kappa(q) -> kappa^sep` making the residue field
square commute, there exists a *unique* ring homomorphism `f : A -> S^sh` such that:
1. (Compatibility) `f comp (R -> A) = (R --phi--> S -> S^sh)`;
2. (Prime condition) `f^{-1}(m_{S^sh}) = q`;
3. (Residue field condition) the induced field map `kappa(q) -> kappa(S^sh) = kappa^sep`
   equals the given `phibar`.

# Background and conventions

- "ring" means commutative ring with unit; "local ring" is `IsLocalRing`.
- A "local ring map" is a ring hom `f` between local rings with `IsLocalHom f`,
  equivalently `f^{-1}(m_S) = m_R` (`IsLocalRing.maximalIdeal_comap`).
- Residue fields. We use `Ideal.ResidueField` uniformly: for a local ring `T` the
  residue field `kappa(T)` is modelled as `(IsLocalRing.maximalIdeal T).ResidueField`
  (`= Frac(T / m_T)`), and for a prime `q` we write `kappa(q) = q.ResidueField`. This
  keeps all the residue-field maps `Ideal.ResidueField.map` type-compatible.
- The residue field map induced by a ring hom `g : R -> S` carrying a prime `I` to a
  prime `J` (i.e. `I = J.comap g`) is `Ideal.ResidueField.map I J g hf`.

# Definition 2 (Separable algebraic closure)

A separable algebraic closure of a field `k` is an algebraic extension `k subset k^sep`
with `k^sep` separably closed and `k^sep / k` separable. In Mathlib this is exactly the
predicate `IsSepClosure k k^sep` (equivalently `IsSepClosed k^sep` together with
`Algebra.IsSeparable k k^sep`, cf. `isSepClosure_iff`). Here `k = kappa(S)` is taken to be
`(IsLocalRing.maximalIdeal S).ResidueField` and `k^sep = kappa^sep` is an abstract field
equipped with `[Algebra kappa(S) kappa^sep]` and `[IsSepClosure kappa(S) kappa^sep]`.

# Definition 3 (Strict henselization)

The strict henselization `S^sh` is not (yet) a primitive Mathlib notion, so we encode it
as the data of an `S`-algebra `Ssh` (with structure map `S -> Ssh = algebraMap S Ssh`)
satisfying the four characterizing properties of the problem (cf. Stacks 04GP/04GU),
together with the chosen identification of its residue field with `kappa^sep`:

1. `Ssh` is strictly Henselian: `HenselianLocalRing Ssh` and its residue field is
   separably closed (`IsSepClosed (m_{Ssh}).ResidueField`);
2. `S -> Ssh` is a local ring map (`IsLocalHom`) realizing `Ssh` as a filtered colimit of
   etale `S`-algebras: concretely `Ssh` is the directed union (`iSup = top`) of a directed
   family of `S`-subalgebras, each etale over `S` (`Algebra.Etale`);
3. `m_S * Ssh = m_{Ssh}`, i.e. `(m_S).map (algebraMap S Ssh) = m_{Ssh}`;
4. the induced residue field map `kappa(S) -> kappa(Ssh)` realizes
   `kappa^sep ~= kappa(Ssh)`: an isomorphism `residueFieldEquiv : kappa^sep ~=+* kappa(Ssh)`
   compatible with `kappa(S) -> kappa^sep` and `kappa(S) -> kappa(Ssh)`.

# Definition 4 (Etale ring map)

A ring map `R -> A` is etale iff finitely presented, flat and unramified; this is the
standard Mathlib notion `Algebra.Etale`.
-/

@[expose] public section
open IsLocalRing

universe u v w

namespace Stacks.StrictHenselization

/-- A strict henselization of the local ring `S`
with respect to a chosen separable algebraic closure `kappa(S) subset kappa^sep` of its
residue field is the data of an `S`-algebra `Ssh` (the structure map `S -> Ssh` is
`algebraMap S Ssh`) satisfying the four characterizing properties (Stacks 04GP/04GU),
plus the identification of `kappa(Ssh)` with `kappa^sep`.

Here Definition 2 (separable algebraic closure) is recorded in the typeclass arguments via
`[Algebra (maximalIdeal S).ResidueField κsep]` and `[IsSepClosure (maximalIdeal S).ResidueField
κsep]`. -/
@[ega "IV 18.8.7"]
structure IsStrictHenselization
    (S : Type u) [CommRing S] [IsLocalRing S]
    (κsep : Type v) [Field κsep] [Algebra (maximalIdeal S).ResidueField κsep]
      [IsSepClosure (maximalIdeal S).ResidueField κsep]
    (Ssh : Type w) [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh] where
  /-- The structure map `S -> Ssh` is a local ring map (part of property (2)). -/
  isLocalHom : IsLocalHom (algebraMap S Ssh)
  /-- Property (1a): `Ssh` is Henselian. -/
  henselian : HenselianLocalRing Ssh
  /-- Property (1b): the residue field of `Ssh` is separably closed. -/
  sepClosed : IsSepClosed (maximalIdeal Ssh).ResidueField
  /-- Property (2): `Ssh` is a filtered colimit of etale `S`-algebras.
  The base and the algebra may lie in independent universes. The index category and
  the étale stages lie in `Type (max u w)`, as in `IsHenselization.ind_etale`.
  The cocone maps need not be injective; a presentation of `Ssh` as a directed union of
  étale `S`-subalgebras is one way to supply this, through
  `StacksDraft.indEtale_of_directed_etale_subalgebras`. -/
  isFilteredColimitEtale : (CommAlgCat.etale.{max u w} S).ind.{max u w}
    (CommAlgCat.of S (ULift.{u} Ssh))
  /-- Property (3): the maximal ideal of `Ssh` is generated by the image of `m_S`. -/
  maximalIdeal_map : (maximalIdeal S).map (algebraMap S Ssh) = maximalIdeal Ssh
  /-- Property (4), part 1: the chosen isomorphism `kappa^sep ~=+* kappa(Ssh)`. -/
  residueFieldEquiv : κsep ≃+* (maximalIdeal Ssh).ResidueField
  /-- Property (4), part 2: the isomorphism is compatible with the residue field maps
  `kappa(S) -> kappa^sep` (the separable closure inclusion) and
  `kappa(S) -> kappa(Ssh)` (induced by `S -> Ssh`). -/
  residueFieldEquiv_comp :
    haveI := isLocalHom
    (residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp
        (algebraMap (maximalIdeal S).ResidueField κsep)
      = Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (maximalIdeal_comap (algebraMap S Ssh)).symm

/- ============================================================================
   PROOF SKETCH (Stacks Tag 04GT)

   The theorem `strict_henselization_universal_property` is reduced below to two
   named sub-lemmas, `exists_lift` (existence) and `lift_unique` (uniqueness).
   Each carries the full informal argument as a comment.

   OVERALL STRATEGY (where the étale hypothesis is used):
   View `Ssh` as an `R`-algebra via `R --φ--> S -> Ssh` (this is the algebra
   structure `RingHom.comp (algebraMap S Ssh) φ`). Then a ring map `f : A -> Ssh`
   satisfying compatibility (1) is exactly an `R`-algebra map `A ->ₐ[R] Ssh`.

   * EXISTENCE. Because `R -> A` is étale (hence finitely presented and étale at
     every prime), the local structure theorem
     `Algebra.IsEtaleAt.exists_isStandardEtale` gives `h ∉ q` with `A[1/h]`
     STANDARD étale over `R`: `A[1/h] ≅ P.Ring = R[X,Y]/(f, Yg-1)` for a standard
     étale pair `P = (f,g)` (`f` monic, `f'` a unit on `D(g)`). The residue point
     `φbar : κ(q) -> κsep = κ(Ssh)` sends the image `x̄₀` of `X` to a root of the
     reduction `f̄` of `f` in `κ(Ssh)` at which `f̄'` is nonzero (`g(x̄₀)` is a unit
     because `Yg-1=0` forces it). Lift `x̄₀` through the surjection
     `Ssh ↠ κ(Ssh)` by Hensel's lemma (`hsh.henselian`, via the surjective-field-hom
     clause of `HenselianLocalRing.TFAE`) to a root `x ∈ Ssh` of `f` with `g(x)` a
     unit (units lift along a local ring map). Then `P.HasMap x` holds, and
     `StandardEtalePair.lift P x : P.Ring ->ₐ[R] Ssh` composed with
     `A -> A[1/h] ≅ P.Ring` gives the required `f : A -> Ssh`. Conditions (1)(2)(3)
     hold by construction: (1) is `R`-linearity; (2)/(3) because the residue of `f`
     is the chosen point `x̄₀ = φbar`, i.e. `f` reduces to `φbar` mod `m_{Ssh}`.

   * UNIQUENESS. Any `f` satisfying (1)(2)(3) is an `R`-algebra map `A ->ₐ[R] Ssh`
     inducing the SAME residue point `φbar`. After inverting `h ∉ q` (allowed: (2)
     forces `f(h) ∉ m_{Ssh}`, i.e. `f(h)` a unit, so `f` factors through `A[1/h] ≅
     P.Ring`), `f` is determined by the image `x := f(X) ∈ Ssh` of the standard-étale
     generator. That `x` is a root of `f` reducing to the fixed `x̄₀`, with `f'(x)` a
     unit; by the Henselian UNIQUENESS of such a root (two roots of a monic `f` with
     `f'` a unit that are congruent mod `m_{Ssh}` are equal — the contracting/Newton
     step, available from the Henselian structure / `FormallyUnramified`
     rigidity of `P.Ring` over `R`), `x` is unique, hence `f` is unique.
   ============================================================================ -/

/-- **Existence half of Stacks 04GT.** There is a ring map `f : A → Ssh` over the base
satisfying the prime and residue-field conditions.

INFORMAL PROOF (the analytic kernel of 04GT):
Give `Ssh` its `R`-algebra structure through `R --φ--> S → Ssh`, so a base-compatible
ring map `f` is an `R`-algebra map `A →ₐ[R] Ssh`.

1. `A` is étale over `R`, hence `Algebra.FinitePresentation R A` and `IsEtaleAt R q`. By
   `Algebra.IsEtaleAt.exists_isStandardEtale q` there is `h ∉ q` with
   `IsStandardEtale R (Localization.Away h)`; pick a standard étale presentation
   `A[1/h] ≃ₐ[R] P.Ring` with `P : StandardEtalePair R`, `P.f` monic and `P.g` with
   `P.f'` invertible on `D(P.g)` (`Algebra.IsStandardEtale.nonempty_standardEtalePresentation`).
2. The residue point. `q` corresponds to a prime `Q` of `A[1/h]` (since `h ∉ q`), and
   `φbar : κ(q) ≃ κ(Q) → κsep ≃ κ(Ssh)` sends the generator `X̄ := image of P's `X`-coordinate`
   to a root `x̄₀ ∈ κ(Ssh)` of the reduction `f̄ := P.f.map (residue)` with `f̄'(x̄₀) ≠ 0`
   (the relation `Y·g(X) = 1` forces `g(x̄₀)` to be a unit, and `f'` is a unit on `D(g)`).
3. Hensel lift. `Ssh` is Henselian (`hsh.henselian`); via the surjective-field-hom clause
   of `HenselianLocalRing.TFAE` applied to `Ssh ↠ κ(Ssh)` (surjective; `residue Ssh`),
   the monic `P.f`, and the root `x̄₀` with nonzero derivative, get `x ∈ Ssh` with
   `P.f.eval x = 0` and `x ≡ x̄₀` mod `m_{Ssh}`. Since `g(x) ≡ g(x̄₀) ≠ 0` mod `m_{Ssh}`,
   `g(x)` is a unit in the local ring `Ssh`. Hence `P.HasMap x`.
4. Build `f`. `StandardEtalePair.lift P x : P.Ring →ₐ[R] Ssh`; precompose with
   `A → A[1/h] ≃ₐ[R] P.Ring` (the localization map `A → A[1/h]`, which is an `R`-algebra
   map) to obtain `fₐ : A →ₐ[R] Ssh`, and set `f := fₐ.toRingHom`.
5. Verify (1): `f` is `R`-linear so `f ∘ algebraMap R A = algebraMap R Ssh = algebraMap S Ssh ∘ φ`
   (the latter by definition of the chosen `R`-algebra structure on `Ssh`).
   Verify (2)/(3): by construction `f` reduces mod `m_{Ssh}` to the residue point built from
   `φbar`; concretely the residue of `f(X)=x` is `x̄₀`, so the induced residue map
   `κ(q) → κ(Ssh)` equals `residueFieldEquiv ∘ φbar`, giving (3); and (2) `q = f⁻¹(m_{Ssh})`
   follows since the residue map `κ(q) → κ(Ssh)` is a field map (injective), forcing the
   contracted prime to be exactly `q`.

This is the standard Stacks 04GT argument, in the four steps above (standard-étale
presentation, residue point, Hensel lift, assembly). -/
@[ega "IV 18.8.4" "partial"]
theorem exists_lift
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ]
    (κsep : Type*) [Field κsep] [Algebra (maximalIdeal S).ResidueField κsep]
      [IsSepClosure (maximalIdeal S).ResidueField κsep]
    {Ssh : Type*} [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
    (hsh : IsStrictHenselization S κsep Ssh)
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : maximalIdeal R = q.comap (algebraMap R A))
    (φbar : q.ResidueField →+* κsep)
    (hsquare :
      φbar.comp (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq)
        =
      (algebraMap (maximalIdeal S).ResidueField κsep).comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ
          (maximalIdeal_comap φ).symm)) :
    ∃ f : A →+* Ssh,
      (f.comp (algebraMap R A) = (algebraMap S Ssh).comp φ) ∧
      (∃ hf : q = (maximalIdeal Ssh).comap f,
        Ideal.ResidueField.map q (maximalIdeal Ssh) f hf
          = (hsh.residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp φbar) := by
  -- Strategy: standard-étale presentation of `A` near `q`
  -- (`Algebra.IsEtaleAt.exists_isStandardEtale`) + Hensel lift of the residue point
  -- through `Ssh ↠ κ(Ssh)` (`hsh.henselian`, `HenselianLocalRing.TFAE`) +
  -- `StandardEtalePair.lift`. See the lemma docstring for the four-step decomposition.
  --
  -- STEP 1: standard-étale presentation of `A` near `q`.
  -- `A` is étale over `R`, hence finitely presented and étale at `q`.
  have hFP : Algebra.FinitePresentation R A := inferInstance
  have hEt : Algebra.IsEtaleAt R q := inferInstance
  obtain ⟨h, hhq, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  obtain ⟨pres⟩ := hstd.nonempty_standardEtalePresentation
  set P := pres.P with hP
  -- Give `Ssh` its `R`-algebra structure through `R --φ--> S → Ssh`.
  let algRSsh : Algebra R Ssh := ((algebraMap S Ssh).comp φ).toAlgebra
  -- The `R`-algebra structure map on `Ssh` is `algebraMap S Ssh ∘ φ` by construction.
  have halgRSsh : (algebraMap R Ssh) = (algebraMap S Ssh).comp φ := rfl
  -- The standard-étale presentation gives an `R`-algebra isomorphism
  -- `P.Ring ≃ₐ[R] A[1/h]`; let `einv : A[1/h] →ₐ[R] P.Ring` be its inverse.
  let e : P.Ring ≃ₐ[R] Localization.Away h :=
    AlgEquiv.ofBijective (P.lift pres.x pres.hasMap) pres.lift_bijective
  let einv : Localization.Away h →ₐ[R] P.Ring := e.symm.toAlgHom
  -- The localization map `A → A[1/h]` as an `R`-algebra map.
  let lmap : A →ₐ[R] Localization.Away h := IsScalarTower.toAlgHom R A (Localization.Away h)
  -- STEPS 2–3 (analytic kernel): the residue point built from `φbar` lifts (Hensel) to a
  -- root `x ∈ Ssh` of `P.f` with `P.g x` a unit (so `P.HasMap x`), reducing mod `m_{Ssh}`
  -- to the chosen residue point.  The companion `R`-algebra map `P.Ring →ₐ[R] Ssh` is then
  -- `P.lift x hx`, and the assembled `f` is `(P.lift x hx) ∘ einv ∘ lmap`.
  --
  -- Condition (1) (compatibility over the base) holds for ANY `x` with `P.HasMap x`,
  -- since the assembled map is an `R`-algebra map and the `R`-algebra structure on `Ssh`
  -- is exactly `algebraMap S Ssh ∘ φ`.  We record this as `cond1`.
  have cond1 : ∀ (x : Ssh) (hx : P.HasMap x),
      ((P.lift x hx).comp (einv.comp lmap)).toRingHom.comp (algebraMap R A)
        = (algebraMap S Ssh).comp φ := by
    intro x hx
    ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply]
    rw [show lmap (algebraMap R A r) = algebraMap R (Localization.Away h) r from
      (lmap.commutes r)]
    rw [show einv (algebraMap R (Localization.Away h) r) = algebraMap R P.Ring r from
      (einv.commutes r)]
    rw [show (P.lift x hx) (algebraMap R P.Ring r) = algebraMap R Ssh r from
      ((P.lift x hx).commutes r)]
    rw [halgRSsh]; rfl
  -- It remains to produce the Hensel-lifted root `x` and verify the prime/residue
  -- conditions (2)/(3); the residue conditions are the genuinely analytic content of 04GT.
  suffices hgoal :
      ∃ x : Ssh, ∃ hx : P.HasMap x,
        ∃ hf : q = (maximalIdeal Ssh).comap ((P.lift x hx).comp (einv.comp lmap)).toRingHom,
          Ideal.ResidueField.map q (maximalIdeal Ssh)
              ((P.lift x hx).comp (einv.comp lmap)).toRingHom hf
            = (hsh.residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp φbar by
    obtain ⟨x, hx, hf, h3⟩ := hgoal
    exact ⟨_, cond1 x hx, hf, h3⟩
  -- ANALYTIC KERNEL of 04GT, decomposed into three obligations.
  --
  -- The standard-étale algebra `P.Ring = R[X,Y]/(C f, X·C g − 1)` is generated over `R`
  -- by the class of the inner variable.  Its image `ξ ∈ A[1/h]` under `e` is a root of
  -- `P.f` with `P.g ξ` a unit.  The residue point we must hit is
  -- `x̄₀ := residueFieldEquiv (φbar (residue class of ξ in κ(q)))`.
  --
  -- STEP A (kernel_root): Hensel-lift `x̄₀` through `residue Ssh : Ssh ↠ ResidueField Ssh`
  --   to a root `x ∈ Ssh` of `P.f` (pushed to `Ssh` via `algebraMap R Ssh`) with `P.g x`
  --   a unit (so `P.HasMap x`), `x` reducing to the transported residue point.
  --   Uses `(HenselianLocalRing.TFAE Ssh).out 1 3` + `hsh.henselian` + `residue_surjective`,
  --   plus L3 (commuting reductions) to certify the Hensel-clause hypotheses.
  --   NOTE the two residue fields: `ResidueField Ssh = Ssh/m` (target of the Hensel TFAE)
  --   vs `(maximalIdeal Ssh).ResidueField = Frac(Ssh/m)` (problem statement); linked by the
  --   canonical field hom between them.
  -- STEP B (kernel_prime, the geometric crux / "Lemma A"): for the assembled `fx`, the
  --   contracted prime `(maximalIdeal Ssh).comap fx = q` (étale fiber over `m_R` is a finite
  --   product of separable field extensions; the residue point picks out exactly `q`).
  -- STEP C (kernel_residue): the induced residue map equals `residueFieldEquiv ∘ φbar`
  --   (`κ(q)` is generated over `κ(R)` by the generator class (L2); `fx` matches on it by
  --   STEP A and on `κ(R)` by `hsquare`/`hsh.residueFieldEquiv_comp`).
  --
  -- We first obtain the witness `x` with `P.HasMap x`; the bundled `hroot` records the
  -- residue-of-the-generator condition that STEPS B and C consume.
  --
  -- Set up the residue point `a0`.  We work with `K := (maximalIdeal Ssh).ResidueField`,
  -- the "fraction-field" residue field of the problem statement, and the canonical
  -- (bijective) field hom `up : ResidueField Ssh →+* K` (where `ResidueField Ssh = Ssh/m`
  -- is the target of the Hensel TFAE clause), realized as an isomorphism `upEquiv`.
  -- Since `h ∉ q`, `algebraMap A q.ResidueField h` is a unit, so the localization
  -- `Localization.Away h` admits a ring hom `ψq` to `κ(q)` extending `A → κ(q)`.  The
  -- residue point is the φbar-transport of the standard-étale generator `pres.x`:
  --   `a0 := upEquiv.symm (residueFieldEquiv (φbar (ψq pres.x)))  :  ResidueField Ssh`.
  set K := (maximalIdeal Ssh).ResidueField with hK
  -- the canonical map `up : ResidueField Ssh →+* K` and its bijectivity / inverse `upEquiv`.
  set up : IsLocalRing.ResidueField Ssh →+* K :=
    algebraMap (IsLocalRing.ResidueField Ssh) K with hup
  have hupcomp : up.comp (IsLocalRing.residue Ssh) = algebraMap Ssh K := by
    ext s
    simp only [RingHom.comp_apply, hup]
    rw [show IsLocalRing.residue Ssh s = algebraMap Ssh (IsLocalRing.ResidueField Ssh) s from rfl,
      ← IsScalarTower.algebraMap_apply]
  have hupbij : Function.Bijective up := by
    refine ⟨up.injective, ?_⟩
    intro y
    obtain ⟨s, hs⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal Ssh) y
    exact ⟨IsLocalRing.residue Ssh s, by rw [← RingHom.comp_apply, hupcomp, hs]⟩
  set upEquiv : IsLocalRing.ResidueField Ssh ≃+* K := RingEquiv.ofBijective up hupbij with hupEquiv
  -- the lift `ψq : Localization.Away h →+* q.ResidueField`.
  have hhq' : IsUnit ((algebraMap A q.ResidueField) h) :=
    isUnit_iff_ne_zero.mpr (by rwa [Ne, Ideal.algebraMap_residueField_eq_zero])
  set ψq : Localization.Away h →+* q.ResidueField :=
    IsLocalization.Away.lift h (S := Localization.Away h) hhq' with hψq
  -- `ψx := residueFieldEquiv ∘ φbar : κ(q) →+* K`, injective, and its transport `θ` to `A[1/h]`.
  set ψx : q.ResidueField →+* K := (hsh.residueFieldEquiv : κsep →+* K).comp φbar with hψx
  set θ : Localization.Away h →+* K := ψx.comp ψq with hθ
  set a0 : IsLocalRing.ResidueField Ssh := upEquiv.symm (θ pres.x) with ha0
  -- `θ ∘ (A → Loc) = ψx ∘ (A → κ(q))`.
  have hθlmap : θ.comp (algebraMap A (Localization.Away h)) = ψx.comp (algebraMap A
      q.ResidueField) := by
    rw [hθ, RingHom.comp_assoc, hψq, IsLocalization.Away.lift_comp]
  -- `θ` is a ring hom over `R`: `θ ∘ (R → Localization.Away h) = (R → Ssh) → K`.
  have hθR : θ.comp (algebraMap R (Localization.Away h))
      = (algebraMap Ssh K).comp (algebraMap R Ssh) := by
    ext r
    have e1 : θ (algebraMap R (Localization.Away h) r) = ψx (algebraMap R q.ResidueField r) := by
      rw [IsScalarTower.algebraMap_apply R A (Localization.Away h),
        IsScalarTower.algebraMap_apply R A q.ResidueField]
      exact RingHom.congr_fun hθlmap _
    change θ (algebraMap R (Localization.Away h) r) = algebraMap Ssh K (algebraMap R Ssh r)
    rw [e1]
    -- `algebraMap R q.ResidueField = (ResidueField.map ...) ∘ residue R`
    have e2 : (algebraMap R q.ResidueField) r
        = (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq)
            ((algebraMap R (maximalIdeal R).ResidueField) r) := by
      rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply]
    rw [e2]
    -- apply hsquare (pointwise) and residueFieldEquiv_comp (pointwise)
    have hsq := RingHom.congr_fun hsquare ((algebraMap R (maximalIdeal R).ResidueField) r)
    simp only [RingHom.comp_apply] at hsq
    rw [hψx, RingHom.comp_apply, hsq]
    have hrc := RingHom.congr_fun hsh.residueFieldEquiv_comp
      ((Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ (maximalIdeal_comap φ).symm)
        ((algebraMap R (maximalIdeal R).ResidueField) r))
    simp only [RingHom.comp_apply] at hrc
    rw [hrc]
    -- now `ResidueField.map (m_S)(m_Ssh)(algebraMap S Ssh)` of `ResidueField.map (m_R)(m_S) φ` of
    -- residue r
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
    -- goal: algebraMap Ssh K ((algebraMap S Ssh) (φ r)) = algebraMap Ssh K r
    rw [show (algebraMap S Ssh) (φ r) = algebraMap R Ssh r from by rw [halgRSsh]; rfl]
  -- Give `K` the `R`-algebra structure `R → Ssh → K` (matching `θ`'s `R`-linearity).
  let algRK : Algebra R K := ((algebraMap Ssh K).comp (algebraMap R Ssh)).toAlgebra
  have : IsScalarTower R Ssh K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- `algebraMap Ssh K` as an `R`-algebra map.
  let ψA : Ssh →ₐ[R] K := IsScalarTower.toAlgHom R Ssh K
  -- `θ` as an `R`-algebra map (it is `R`-linear by `hθR`, using the new structure on `K`).
  let θA : Localization.Away h →ₐ[R] K :=
    { θ with commutes' := fun r => RingHom.congr_fun hθR r }
  -- Hensel-lift `a0` (its image `θ pres.x = up a0` in `K`) to a root in `Ssh`.
  obtain ⟨x, hx, hroot⟩ : ∃ x : Ssh, ∃ hx : P.HasMap x,
      (IsLocalRing.residue Ssh) x = a0 := by
    -- STEP A — Hensel lift, producing `x`, `P.HasMap x`, and `residue Ssh x = a0`.
    set F : Polynomial Ssh := P.f.map (algebraMap R Ssh) with hF
    have hFmonic : F.Monic := P.monic_f.map _
    -- the surjective field hom `ψ := algebraMap Ssh K`.
    set ψ : Ssh →+* K := algebraMap Ssh K with hψ
    have hψsurj : Function.Surjective ψ := Ideal.algebraMap_residueField_surjective (maximalIdeal
        Ssh)
    -- `up a0 = θ pres.x`.
    have hupa0 : up a0 = θ pres.x := by
      rw [ha0]; exact upEquiv.apply_symm_apply (θ pres.x)
    -- the residue point is a root of `P` in `K`: `P.HasMap (θ pres.x)`.
    have hKmap : P.HasMap (θA pres.x) := pres.hasMap.map θA
    have hroot0 : Polynomial.eval₂ ψ (θ pres.x) F = 0 := by
      rw [hF, Polynomial.eval₂_map]
      exact hKmap.1
    -- the value `eval₂ ψ (θ pres.x) P.g` is a unit, hence ≠ 0.
    have hgne : Polynomial.eval₂ ψ (θ pres.x) (P.g.map (algebraMap R Ssh)) ≠ 0 := by
      rw [Polynomial.eval₂_map]
      exact hKmap.2.ne_zero
    have hderiv : Polynomial.eval₂ ψ (θ pres.x) (Polynomial.derivative F) ≠ 0 := by
      rw [hF, Polynomial.derivative_map, Polynomial.eval₂_map]
      exact hKmap.isUnit_derivative_f.ne_zero
    -- invoke Hensel clause 2.
    have hHensel := ((HenselianLocalRing.TFAE Ssh).out 1 3).mp hsh.henselian
    obtain ⟨x, hxroot, hxres⟩ :=
      hHensel ψ hψsurj F hFmonic (θ pres.x) hroot0 hderiv
    -- `aeval x P.f = 0`.
    have hxf : Polynomial.aeval x P.f = 0 := by
      have : F.eval x = 0 := hxroot
      rwa [hF, Polynomial.eval_map, ← Polynomial.aeval_def] at this
    -- `IsUnit (aeval x P.g)`: its image under `ψ` is `eval₂ ψ (θ pres.x) (P.g.map ...) ≠ 0`.
    have hxg : IsUnit (Polynomial.aeval x P.g) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← Ideal.algebraMap_residueField_eq_zero (I :=
          maximalIdeal Ssh)]
      show ψ (Polynomial.aeval x P.g) ≠ 0
      have hev : ψ (Polynomial.aeval x P.g) = Polynomial.eval₂ ψ (θ pres.x) (P.g.map (algebraMap R
          Ssh)) := by
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hxres, Polynomial.eval₂_map]
      rw [hev]
      exact hgne
    refine ⟨x, ⟨hxf, hxg⟩, ?_⟩
    -- `residue Ssh x = a0`: from `ψ x = θ pres.x = up a0` and `up` injective.
    have hinj : up (IsLocalRing.residue Ssh x) = up a0 := by
      rw [← RingHom.comp_apply, hupcomp]
      show ψ x = up a0
      rw [hxres, hupa0]
    exact up.injective hinj
  -- With `x` and `P.HasMap x` in hand, set `fx := (P.lift x hx).comp (einv.comp lmap)`.
  -- The composite `algebraMap Ssh K ∘ fx : A → K` equals
  -- `(residueFieldEquiv ∘ φbar) ∘ (A → κ(q))`.
  -- This single residue-field identity (`hcomp`) drives BOTH the prime condition (STEP B)
  -- and the residue condition (STEP C), so we establish it once here.
  set fx : A →+* Ssh := ((P.lift x hx).comp (einv.comp lmap)).toRingHom with hfx
  -- KEY: on `P.X`, `algebraMap Ssh K (P.lift x hx P.X) = θ pres.x`.
  have hKx : (algebraMap Ssh K) ((P.lift x hx) P.X) = θ pres.x := by
    rw [P.lift_X x hx, ← hupcomp, RingHom.comp_apply, hroot, ha0]
    exact upEquiv.apply_symm_apply (θ pres.x)
  -- LHS and RHS as `R`-algebra maps `P.Ring →ₐ[R] K`.
  let LHS : P.Ring →ₐ[R] K := ψA.comp (P.lift x hx)
  let RHS : P.Ring →ₐ[R] K := θA.comp e.toAlgHom
  have hLR : LHS = RHS := by
    apply StandardEtalePair.hom_ext
    show (algebraMap Ssh K) ((P.lift x hx) P.X) = θ (e P.X)
    rwa [show e P.X = pres.x from P.lift_X pres.x pres.hasMap]
  -- `algebraMap Ssh K ∘ fx = ψx ∘ (algebraMap A q.ResidueField)`.
  have hcomp : (algebraMap Ssh K).comp fx = ψx.comp (algebraMap A q.ResidueField) := by
    ext a
    simp only [RingHom.comp_apply, hfx, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.coe_comp, Function.comp_apply]
    -- `algebraMap Ssh K ((P.lift x hx) (einv (lmap a))) = LHS (einv (lmap a))`
    have h1 : (algebraMap Ssh K) ((P.lift x hx) (einv (lmap a))) = LHS (einv (lmap a)) := rfl
    rw [h1, hLR]
    -- `RHS (einv (lmap a)) = θ (e (einv (lmap a)))`
    show θ (e (einv (lmap a))) = ψx (algebraMap A q.ResidueField a)
    -- `e (einv y) = y`
    rw [show e (einv (lmap a)) = lmap a from e.apply_symm_apply (lmap a)]
    -- `lmap a = algebraMap A (Localization.Away h) a`
    have h2 : lmap a = algebraMap A (Localization.Away h) a := rfl
    rw [h2]
    exact RingHom.congr_fun hθlmap a
  -- `ψx` is injective.
  have hψxinj : Function.Injective ψx :=
    (hsh.residueFieldEquiv.injective).comp φbar.injective
  -- STEP B: the prime condition.
  have hf : q = (maximalIdeal Ssh).comap fx := by
    -- `m_{Ssh} = ker(algebraMap Ssh K)`, so `comap fx (m_{Ssh}) = ker(algebraMap Ssh K ∘ fx)`.
    have hmax : maximalIdeal Ssh = RingHom.ker (algebraMap Ssh K) :=
      (Ideal.ker_algebraMap_residueField (maximalIdeal Ssh)).symm
    -- Conclude: `q = ker(algebraMap A q.ResidueField) = comap (ψx ∘ algMap) ⊥ = comap fx
    -- (m_{Ssh})`.
    rw [hmax, RingHom.ker_eq_comap_bot, Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
    -- goal: `q = comap (algebraMap A κ(q)) (comap ψx ⊥)`
    rw [← RingHom.ker_eq_comap_bot ψx,
      (RingHom.injective_iff_ker_eq_bot ψx).mp hψxinj,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  -- STEP C: the residue condition.
  refine ⟨x, hx, hf, ?_⟩
  -- STEP C (residue): the induced residue map `κ(q) → K` equals `ψx = residueFieldEquiv ∘ φbar`.
  -- Both ring maps `κ(q) → K`, precomposed with `algebraMap A κ(q)`, equal
  -- `algebraMap Ssh K ∘ fx`:
  -- LHS by `Ideal.ResidueField.map_algebraMap`, RHS by `hcomp`.  By
  -- `Ideal.ResidueField.ringHom_ext`
  -- (a ring hom out of `κ(q) = Frac(A/q)` is determined by its restriction to `A`), they agree.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  -- LHS: `ResidueField.map ... fx hf (algebraMap A κ(q) a) = algebraMap Ssh K (fx a)`; RHS via
  -- `hcomp`.
  simp only [RingHom.comp_apply]
  rw [Ideal.ResidueField.map_algebraMap q (maximalIdeal Ssh) fx hf a]
  exact (RingHom.congr_fun hcomp a)

/-- At a root `x` of a standard étale pair with `g x` a unit, the derivative `f' x` is a unit. -/
theorem isUnit_aeval_derivative_of_hasMap {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (P : StandardEtalePair R) {x : T} (hx : P.HasMap x) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative P.f)) := by
  exact hx.isUnit_derivative_f

/-- Hensel uniqueness for a standard étale pair: two roots in a local ring with the same
residue coincide. -/
theorem eq_of_hasMap_of_residue_eq {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing T]
    [Algebra R T] (P : StandardEtalePair R) {x₁ x₂ : T} (hx₁ : P.HasMap x₁) (hx₂ : P.HasMap x₂)
    (h : algebraMap T (maximalIdeal T).ResidueField x₁ =
      algebraMap T (maximalIdeal T).ResidueField x₂) : x₁ = x₂ := by
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.f.map (algebraMap R T))
    ?_ ?_ ?_ ?_
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hx₁.left
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hx₂.left
  · rw [← IsLocalRing.notMem_maximalIdeal, not_not,
      ← Ideal.algebraMap_residueField_eq_zero (I := maximalIdeal T), map_sub, h, sub_self]
  · rw [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact isUnit_aeval_derivative_of_hasMap P hx₁

-- needed: `lift_unique`'s `rw [heX, P.lift_X]` after the `change` only matches once defeq
-- unfolds the `StandardEtalePair` coercion to its underlying `AlgHom`.
set_option backward.isDefEq.respectTransparency false in
/-- **Uniqueness half of Stacks 04GT.** Any two base-compatible ring maps `A → Ssh`
satisfying the prime and residue-field conditions agree.

INFORMAL PROOF:
Let `f₁, f₂ : A → Ssh` both satisfy (1)(2)(3). Both are `R`-algebra maps `A →ₐ[R] Ssh`
(condition (1) ⇔ `R`-linearity for the `R`-algebra structure `R --φ--> S → Ssh` on `Ssh`).
`A` is étale over `R`, hence `Algebra.FormallyUnramified R A`.

Take the standard-étale presentation near `q` (as in `exists_lift`): `h ∉ q`,
`A[1/h] ≃ₐ[R] P.Ring`, `P = (f,g)`. Condition (2) forces `fᵢ(h)` to be a unit (`h ∉ q`,
`q = fᵢ⁻¹(m_{Ssh})`), so each `fᵢ` factors through `A[1/h] ≃ P.Ring`, determined by the
generator image `xᵢ := fᵢ(X) ∈ Ssh`. Each `xᵢ` is a root of `P.f` with `P.g(xᵢ)` a unit,
and conditions (2)(3) say both reduce to the SAME residue point `x̄₀` mod `m_{Ssh}`
(`= φbar` transported). Since `P.f` is monic with `P.f'(xᵢ)` a unit (`f'` invertible on
`D(g)`), Hensel uniqueness — two roots of a monic polynomial congruent mod `m_{Ssh}` with
unit derivative coincide — gives `x₁ = x₂`, hence `f₁ = f₂`.

Mathlib route for the rigidity: `Algebra.FormallyUnramified.lift_unique_of_ringHom` gives
uniqueness of `R`-algebra lifts along a ring map with NILPOTENT kernel. The kernel
`m_{Ssh}` of `Ssh ↠ κ(Ssh)` is not nilpotent, so this is applied not to `Ssh` directly but
to the local structure: the two roots `x₁, x₂` of the monic `P.f` lie in the Henselian
local ring `Ssh` and are congruent mod `m_{Ssh}` with unit derivative; their equality is
the uniqueness clause of Hensel's lemma. Equivalently, formal unramifiedness of `P.Ring`
over `R` makes the `R`-algebra map `P.Ring → Ssh` determined by its residue, which is `x̄₀`
for both. One may either (a) prove a standalone Hensel-uniqueness lemma
("monic `f`, two roots `≡ a₀ (mod m)` with `f'(a₀)` a unit ⇒ equal" in a local ring — this
is the contracting Newton iteration and is the natural companion to `is_henselian`), or
(b) route through `FormallyUnramified` after reducing to a square-zero/`m`-adic situation. -/
theorem lift_unique
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ]
    (κsep : Type*) [Field κsep] [Algebra (maximalIdeal S).ResidueField κsep]
      [IsSepClosure (maximalIdeal S).ResidueField κsep]
    {Ssh : Type*} [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
    (hsh : IsStrictHenselization S κsep Ssh)
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime]
    (φbar : q.ResidueField →+* κsep)
    (f₁ f₂ : A →+* Ssh)
    (h₁ :
      (f₁.comp (algebraMap R A) = (algebraMap S Ssh).comp φ) ∧
      (∃ hf : q = (maximalIdeal Ssh).comap f₁,
        Ideal.ResidueField.map q (maximalIdeal Ssh) f₁ hf
          = (hsh.residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp φbar))
    (h₂ :
      (f₂.comp (algebraMap R A) = (algebraMap S Ssh).comp φ) ∧
      (∃ hf : q = (maximalIdeal Ssh).comap f₂,
        Ideal.ResidueField.map q (maximalIdeal Ssh) f₂ hf
          = (hsh.residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp φbar)) :
    f₁ = f₂ := by
  -- Setup mirrors `exists_lift`.
  obtain ⟨h, hhq, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  obtain ⟨pres⟩ := hstd.nonempty_standardEtalePresentation
  set P := pres.P with hP
  let algRSsh : Algebra R Ssh := ((algebraMap S Ssh).comp φ).toAlgebra
  have halgRSsh : (algebraMap R Ssh) = (algebraMap S Ssh).comp φ := rfl
  let e : P.Ring ≃ₐ[R] Localization.Away h :=
    AlgEquiv.ofBijective (P.lift pres.x pres.hasMap) pres.lift_bijective
  let einv : Localization.Away h →ₐ[R] P.Ring := e.symm.toAlgHom
  let lmap : A →ₐ[R] Localization.Away h := IsScalarTower.toAlgHom R A (Localization.Away h)
  have heX : e P.X = pres.x := P.lift_X pres.x pres.hasMap
  -- The residue field `K` of `Ssh` and the transport `θ` of `φbar`.
  set K := (maximalIdeal Ssh).ResidueField with hK
  have hhq' : IsUnit ((algebraMap A q.ResidueField) h) :=
    isUnit_iff_ne_zero.mpr (by rwa [Ne, Ideal.algebraMap_residueField_eq_zero])
  set ψq : Localization.Away h →+* q.ResidueField :=
    IsLocalization.Away.lift h (S := Localization.Away h) hhq' with hψq
  set ψx : q.ResidueField →+* K := (hsh.residueFieldEquiv : κsep →+* K).comp φbar with hψx
  set θ : Localization.Away h →+* K := ψx.comp ψq with hθ
  -- `θ ∘ (A → Loc) = ψx ∘ (A → κ(q))`.
  have hθlmap : θ.comp (algebraMap A (Localization.Away h)) = ψx.comp (algebraMap A
      q.ResidueField) := by
    rw [hθ, RingHom.comp_assoc, hψq, IsLocalization.Away.lift_comp]
  -- MAIN: process one `f` satisfying the three conditions.
  have process : ∀ (f : A →+* Ssh)
      (hc1 : f.comp (algebraMap R A) = (algebraMap S Ssh).comp φ)
      (hf2 : q = (maximalIdeal Ssh).comap f),
      Ideal.ResidueField.map q (maximalIdeal Ssh) f hf2
          = (hsh.residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp φbar →
      ∃ (x : Ssh) (hx : P.HasMap x),
        f = ((P.lift x hx).comp (einv.comp lmap)).toRingHom ∧
        (algebraMap Ssh K) x = θ pres.x := by
    intro f hc1 hf2 hc3
    -- `F : A →ₐ[R] Ssh`.
    let F : A →ₐ[R] Ssh :=
      { f with commutes' := fun r => by rw [halgRSsh]; exact RingHom.congr_fun hc1 r }
    have hFf : ∀ a, F a = f a := fun _ => rfl
    -- `IsUnit (F h)`.
    have hFhunit : IsUnit (F h) := by
      rw [hFf, ← IsLocalRing.notMem_maximalIdeal]
      exact fun hmem => hhq (by rwa [hf2, Ideal.mem_comap])
    -- units along `powers h`.
    have hu' : ∀ y : Submonoid.powers h, IsUnit (F (y : A)) := by
      rintro ⟨_, n, rfl⟩
      simpa only [map_pow] using hFhunit.pow n
    -- `G : Loc →ₐ[R] Ssh` lifting `F`.
    let G : Localization.Away h →ₐ[R] Ssh := IsLocalization.liftAlgHom (M := Submonoid.powers h) hu'
    have hGlmap : ∀ a : A, G (lmap a) = f a := by
      intro a
      show G (algebraMap A (Localization.Away h) a) = f a
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    -- the generator image `x`.
    set x : Ssh := G pres.x with hx0
    -- `P.HasMap x`.
    have hxf : Polynomial.aeval x P.f = 0 := by
      rw [hx0, Polynomial.aeval_algHom_apply, pres.hasMap.left, map_zero]
    have hxg : IsUnit (Polynomial.aeval x P.g) := by
      rw [hx0, Polynomial.aeval_algHom_apply]
      exact pres.hasMap.right.map G
    refine ⟨x, ⟨hxf, hxg⟩, ?_, ?_⟩
    · -- factorization `f = (P.lift x hx).comp (einv.comp lmap)`.
      -- First: `G.comp e.toAlgHom = P.lift x ⟨hxf,hxg⟩` (both send `P.X ↦ x`).
      have hGe : G.comp e.toAlgHom = P.lift x ⟨hxf, hxg⟩ := by
        apply StandardEtalePair.hom_ext
        show G (e P.X) = (P.lift x ⟨hxf, hxg⟩) P.X
        rw [heX, P.lift_X]
      apply RingHom.ext
      intro a
      show f a = (P.lift x ⟨hxf, hxg⟩) (einv (lmap a))
      rw [← hGlmap a, ← hGe]
      show G (lmap a) = G (e (einv (lmap a)))
      rw [show e (einv (lmap a)) = lmap a from e.apply_symm_apply (lmap a)]
    · -- residue: `algebraMap Ssh K x = θ pres.x`.
      -- `(algebraMap Ssh K).comp G = θ` as ring maps `Loc → K`.
      have hcompG : ((algebraMap Ssh K).comp G.toRingHom) = θ := by
        apply IsLocalization.ringHom_ext (Submonoid.powers h)
        rw [hθlmap]
        -- both sides composed with `algebraMap A Loc`.
        ext a
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        show (algebraMap Ssh K) (G (algebraMap A (Localization.Away h) a))
            = ψx (algebraMap A q.ResidueField a)
        rw [show G (algebraMap A (Localization.Away h) a) = f a from hGlmap a,
          ← Ideal.ResidueField.map_algebraMap q (maximalIdeal Ssh) f hf2 a, hc3]
      have := RingHom.congr_fun hcompG pres.x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      rwa [hx0]
  -- Apply to both `f₁` and `f₂`.
  obtain ⟨hc1₁, hf2₁, hc3₁⟩ := h₁
  obtain ⟨hc1₂, hf2₂, hc3₂⟩ := h₂
  obtain ⟨x₁, hx₁, hfac₁, hres₁⟩ := process f₁ hc1₁ hf2₁ hc3₁
  obtain ⟨x₂, hx₂, hfac₂, hres₂⟩ := process f₂ hc1₂ hf2₂ hc3₂
  obtain rfl := eq_of_hasMap_of_residue_eq P hx₁ hx₂ (hres₁.trans hres₂.symm)
  rw [hfac₁, hfac₂]

/-- **Theorem (Stacks Tag 04GT).** Let `φ : R → S` be a local ring map of local rings,
let `κ(S) ⊂ κsep` be a separable algebraic closure of the residue field of `S`, and let
`S → Ssh` be a strict henselization of `S` with respect to it. Let `R → A` be an étale
ring map and `q` a prime of `A` lying over `m_R`. Given a residue field point
`φbar : κ(q) → κsep` making the residue field square commute, there is a unique ring map
`f : A → Ssh` compatible over the base, with `f⁻¹(m_{Ssh}) = q`, and inducing `φbar` on
residue fields (via the identification `κ(Ssh) ≅ κsep`). -/
@[stacks 04GT]
theorem strict_henselization_universal_property
    -- Local rings and the local base map `φ : R → S`.
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ]
    -- A separable algebraic closure `κ(S) ⊂ κsep` of the residue field of `S` (Definition 2).
    (κsep : Type*) [Field κsep] [Algebra (maximalIdeal S).ResidueField κsep]
      [IsSepClosure (maximalIdeal S).ResidueField κsep]
    -- The strict henselization `S → Ssh` (Definition 3).
    {Ssh : Type*} [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
    (hsh : IsStrictHenselization S κsep Ssh)
    -- An étale `R`-algebra `A` and a prime `q` lying over `m_R`.
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : maximalIdeal R = q.comap (algebraMap R A))
    -- The given residue field point `φbar : κ(q) → κsep`.
    (φbar : q.ResidueField →+* κsep)
    -- Compatibility of the residue square:
    --   `φbar ∘ (κ(R) → κ(q)) = (κ(S) → κsep) ∘ (κ(R) → κ(S))`.
    (hsquare :
      φbar.comp (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq)
        =
      (algebraMap (maximalIdeal S).ResidueField κsep).comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ
          (maximalIdeal_comap φ).symm)) :
    ∃! f : A →+* Ssh,
      -- (1) Compatibility over the base.
      (f.comp (algebraMap R A) = (algebraMap S Ssh).comp φ) ∧
      -- (2) Prime condition: `f⁻¹(m_{Ssh}) = q`.
      (∃ hf : q = (maximalIdeal Ssh).comap f,
        -- (3) Residue field condition: the induced `κ(q) → κ(Ssh)` equals
        --     `κ(q) --φbar--> κsep ≃ κ(Ssh)`.
        Ideal.ResidueField.map q (maximalIdeal Ssh) f hf
          = (hsh.residueFieldEquiv : κsep →+* (maximalIdeal Ssh).ResidueField).comp φbar) :=
  existsUnique_of_exists_of_unique (exists_lift φ κsep hsh q hq φbar hsquare)
    (lift_unique φ κsep hsh q φbar)

end Stacks.StrictHenselization

end
