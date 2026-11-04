module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectTwist
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NewtonPowerSum

/-!
# The Chern classes of a perfect object depend only on its isomorphism class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes are defined
(Stacks 0F9E (1)). The total Chern class `c(E) ∈ ∏_{p ≥ 0} A^p(X)` of Stacks 0F9E (2) is
`Stacks.Chow.perfectChernClass`. This file records the two facts about it that every consumer of
the definition needs and which the construction does not provide:

* an isomorphism `E ≅ E'` in `D(𝒪_X)` carries an envelope presentation of `E` to one of `E'`, so
  the condition of Stacks 0F9E (1) and the class of Stacks 0F9E (2) depend only on the
  isomorphism class of the object; and
* when `E` is itself represented by a locally bounded complex `𝓔^•` of finite locally free
  `𝒪_X`-modules — no envelope needed — the class `c(E)` is the class `c(𝓔^•)` of Stacks 0ESZ.

## Main definitions

* `Stacks.Chow.EnvelopePresentation.congr` — the transport of an envelope presentation along an
  isomorphism of `D(𝒪_X)`.

## Main results

* `Stacks.Chow.hasDefinedChernClasses_of_iso` — the condition of Stacks 0F9E (1) is invariant
  under isomorphism.
* `Stacks.Chow.perfectChernClass_congr` — so is the class `c(E)` of Stacks 0F9E (2).
* `Stacks.Chow.perfectChernClass_eq_complexChern` — for `E` represented by a locally bounded
  complex of finite locally free `𝒪_X`-modules, `c(E)` is the class `c(𝓔^•)` of Stacks 0ESZ.
* `Stacks.Chow.complexRankClass`, `Stacks.Chow.complexPowerSumComponent`,
  `Stacks.Chow.complexChernCharacter` — the alternating rank class, and the classes `P_p(ℰ^•)`
  and `ch(ℰ^•)` of a locally bounded complex.
* `Stacks.Chow.complexRankClass_eq_of_iso`, `Stacks.Chow.complexPowerSumComponent_eq_of_iso`,
  `Stacks.Chow.complexChernCharacter_eq_of_iso` — **Stacks 0ESZ** for those classes.
* `Stacks.Chow.perfectRankClass`, `Stacks.Chow.perfectPowerSumComponent`,
  `Stacks.Chow.perfectChernCharacter` — **Stacks 0F9E (2)** for `P_p(E)` and `ch(E)`, by descent
  along an envelope, with `Stacks.Chow.res_perfectPowerSum` for the defining property.
* `Stacks.Chow.powerSumClassComplex_eq_of_iso_derivedCategory` and its two companions — the
  carried statements of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex`, improved to the
  derived-category hypothesis of the source; untagged, see the implementation notes.

## Implementation notes

### How `P_p` and `ch` are obtained

Stacks 0ESZ asserts that three classes are independent of the chosen complex, and Stacks 0F9E (2)
introduces three classes; all three are delivered here.

The universal power-sum polynomials of Stacks 0F9B live in
`StacksDraft.AlgebraicGeometry.Chow.SplittingPrinciple`, and
`AlgebraicGeometry.powerSumOfChernClasses` evaluates them at a rank and a family of Chern
classes. That evaluation goes through `MvPolynomial.eval₂Hom` and so needs a commutative ring,
while `Stacks.Chow.TotalChowClass` has a `Ring` instance and no `CommRing` instance — its
multiplication is composition of bivariant classes, Stacks 0FE0. Newton's formula does not need
commutativity: `AlgebraicGeometry.coe_powerSumPolynomial_succ` writes every product with a Chern
class on the left, so the recursion evaluates verbatim in any ring. That recursion is
`AlgebraicGeometry.newtonPowerSum`, and
`AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses` proves it agrees with
`AlgebraicGeometry.powerSumOfChernClasses` over a commutative ring, so it is Stacks 0F9B's `P_p`
and not a second definition of it.

The one place the rank enters `P_p` is the degree-zero member, `P_0 = r`. For a locally bounded
complex the alternating rank `∑_n (-1)^n rank(ℰ^n)` is an integer — not a natural number, which
is the second reason `AlgebraicGeometry.powerSumOfChernClasses` cannot be used directly — and it
is only a locally constant function of the point, hence a class in `A^0(Y)` and not a number at
all. `Stacks.Chow.complexRankClass` is that class: on the rank locus `Y_ρ` the complex has
constant ranks and the alternating rank is the integer `∑_n (-1)^n ρ(n)`, and the integer
multiples of `1` over the rank loci are assembled by Stacks 0FDZ.

Its independence, `Stacks.Chow.complexRankClass_eq_of_iso`, is pointwise and needs no constancy
hypothesis: over a nonempty open on which both complexes have constant ranks they are both
bounded, so each alternating rank is the Euler characteristic of the derived fibre of the object
there, and that characteristic does not mention the complex. The independence of `P_p` and of
`ch` then follows from that together with
`Stacks.Chow.complexChern_eq_of_iso`, since both classes are functions of the total Chern class
and the alternating rank class.

For a perfect object whose Chern classes are defined, the alternating rank class descends along
the envelope of a presentation exactly as the total Chern class does
(`Stacks.Chow.perfectRankClass`), and `P_p(E)` and `ch(E)` are the recursion applied to `c(E)`
and `r(E)`. `Stacks.Chow.res_perfectPowerSum` checks that `P_p(E)` restricts to `P_p(ℰ^•)` along
the envelope of every presentation, which is the property Stacks 0GUD defines the class by;
restriction is a ring homomorphism and commutes with taking homogeneous components, so it
commutes with Newton's recursion (`AlgebraicGeometry.map_newtonPowerSum`).

### The three carried statements below

`Stacks.Chow.powerSumClassComplex_eq_of_iso_derivedCategory` and its two companions improve the
carried statements of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex` without closing
anything: they put the *derived-category* hypothesis of the source in place of the degreewise data
of `Stacks.Chow.ComplexCohomologyComparison` — the finite local freeness of the kernels and images
(Stacks 0F8J), the identification of the cohomology modules, and Schanuel's lemma (Stacks 00O3) —
which `Stacks.Chow.alternatingKClass_eq_of_iso_derivedCategory` discharges. They are untagged: the
classes themselves are still the assumed data of `Stacks.Chow.PowerSumClassRule`, the complexes are
bounded rather than locally bounded, and the cohomology modules are assumed perfect of Tor
dimension at most one, which is what Stacks 0ESR would remove. For a carried class the source's
reduction to an integral test scheme (Stacks 02UC) and the proper birational modification
(Stacks 0ESR) cannot be run, a carried class not being known to commute with restriction.

## References

* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Transport along an isomorphism of the derived category -/

section Congr

variable {X : Scheme.{u}} {E E' : DerivedCategory X.Modules}

/-- **The transport of an envelope presentation along an isomorphism** `E ≅ E'` of `D(𝒪_X)`: the
same envelope and the same complex present `E'`, the representing isomorphism being composed with
the derived pullback of `E' ≅ E`. -/
def EnvelopePresentation.congr (H : EnvelopePresentation E) (e : E ≅ E') :
    EnvelopePresentation E' where
  Y := H.Y
  f := H.f
  envelope := H.envelope
  P := H.P
  locallyBounded := H.locallyBounded
  representation :=
    ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback H.f.toLRSHom.toShHom).mapIso
      e.symm ≪≫ H.representation.some⟩

/-- The envelope scheme of the transported presentation `H.congr e` is that of `H`. -/
@[simp]
theorem EnvelopePresentation.congr_Y (H : EnvelopePresentation E) (e : E ≅ E') :
    (H.congr e).Y = H.Y :=
  rfl

/-- The envelope morphism of the transported presentation `H.congr e` is that of `H`. -/
@[simp]
theorem EnvelopePresentation.congr_f (H : EnvelopePresentation E) (e : E ≅ E') :
    (H.congr e).f = H.f :=
  rfl

/-- The complex of the transported presentation `H.congr e` is the complex of `H`. -/
@[simp]
theorem EnvelopePresentation.congr_P (H : EnvelopePresentation E) (e : E ≅ E') :
    (H.congr e).P = H.P :=
  rfl

/-- **The condition of Stacks 0F9E (1) is invariant under isomorphism**: if the Chern classes of
`E` are defined and `E ≅ E'` in `D(𝒪_X)`, then the Chern classes of `E'` are defined. -/
theorem hasDefinedChernClasses_of_iso (hE : HasDefinedChernClasses E) (e : E ≅ E') :
    HasDefinedChernClasses E' :=
  ⟨hE.some.congr e⟩

end Congr

/-! ### The total Chern class depends only on the isomorphism class -/

section PerfectChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E E' : DerivedCategory X.Modules}

/-- **The total Chern class of Stacks 0F9E (2) depends only on the isomorphism class of the
object**: an isomorphism `E ≅ E'` of `D(𝒪_X)` gives `c(E) = c(E')`. The transported presentation
`Stacks.Chow.EnvelopePresentation.congr` has the same envelope and the same complex, so the
characterization `Stacks.Chow.res_perfectChernClass` of `c(E)` is also one of `c(E')`. -/
theorem perfectChernClass_congr (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses E') (e : E ≅ E') :
    perfectChernClass C sX hE = perfectChernClass C sX hE' :=
  eq_perfectChernClass C sX hE' (hE.some.congr e) (res_perfectChernClass C sX hE hE.some)

/-- **The total Chern class of an object represented by a locally bounded complex on `X`
itself.** If `𝓔^•` is a locally bounded complex of finite locally free `𝒪_X`-modules representing
`E`, then the class `c(E)` of Stacks 0F9E (2) is the class `c(𝓔^•)` of Stacks 0ESZ: the identity
of `X` is an envelope, so `(𝟙 X, 𝓔^•)` is an envelope presentation of `E`. -/
theorem perfectChernClass_eq_complexChern (hE : HasDefinedChernClasses E)
    {P : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hrep : DerivedCategory.Q.obj P ≅ E) :
    perfectChernClass C sX hE = complexChern C sX hP := by
  refine (eq_perfectChernClass C sX hE
    ⟨X, 𝟙 X, ⟨inferInstance, isCompletelyDecomposed_id X⟩, P, hP,
      ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app E ≪≫
        hrep.symm⟩⟩ ?_).symm
  rw [res_complexChern C sX hP (𝟙 X) rfl]
  exact complexChern_congr C (𝟙 X ≫ sX)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback (𝟙 X) P hP) hP
    fun n ↦ (Scheme.Modules.pullbackId X).app (P.X n)

/-! ### The alternating rank of a locally bounded complex as a class in `A^0` -/

section RankClass

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P P' : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
  (hP' : IsLocallyBoundedFiniteLocallyFree P')

/-- **The alternating rank `∑_n (-1)^n rank(ℰ^n)` of a locally bounded complex, as a class in
`A^0(Y)`.** This is the degree-zero power sum `P_0` of Stacks 0F9B, the rank variable, for the
complex: on the rank locus `Y_ρ` the complex has constant ranks `ρ` and the alternating rank is
the integer `∑_n (-1)^n ρ(n)`, so the class is that integer multiple of `1`, and the integers over
the rank loci are assembled by Stacks 0FDZ. The alternating rank is an integer and not a natural
number, which is why `AlgebraicGeometry.powerSumOfChernClasses`, whose rank argument is a natural
number, cannot be used in its place. -/
def complexRankClass : TotalChowClass C sY :=
  TotalChowClass.glue (isClopenDecomposition_complexRankLoci hP) fun ρ ↦
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ.down n : ℤ)) • 1

/-- **The restriction of the alternating rank class to a rank locus** is the integer
`∑_n (-1)^n ρ(n)` times `1`. -/
theorem res_complexRankClass_complexRankLocus (ρ : ℤ →₀ ℕ) :
    TotalChowClass.res (complexRankLocus hP ρ).ι rfl (complexRankClass C sY hP) =
      (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ)) • 1 :=
  TotalChowClass.res_glue (isClopenDecomposition_complexRankLoci hP) _ (ULift.up ρ)

/-- The inclusion of the preimage of a rank locus factors through that rank locus. -/
private theorem exists_comp_ι_eq_preimage_complexRankLoci {Z : Scheme.{u}} (g : Z ⟶ Y)
    (ρ : ULift (ℤ →₀ ℕ)) :
    ∃ φ : (g ⁻¹ᵁ complexRankLoci hP ρ).toScheme ⟶ (complexRankLoci hP ρ).toScheme,
      (g ⁻¹ᵁ complexRankLoci hP ρ).ι ≫ g = φ ≫ (complexRankLoci hP ρ).ι :=
  have ha : ∀ τ, g ⁻¹ᵁ complexRankLoci hP τ ≤ g ⁻¹ᵁ complexRankLoci hP (id τ) := fun _ ↦ le_rfl
  ⟨_, (pieceMap_comp_ι g _ _ id ha ρ).symm⟩

/-- Constant ranks of `a^*(b^*ℰ^•)` give constant ranks of `(a ≫ b)^*ℰ^•`. -/
private theorem isFiniteLocallyFreeOfRank_pullbackComplex_comp {A B : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ Y) (r : ℕ) (n : ℤ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex a (pullbackComplex b P)).X n) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (a ≫ b) P).X n) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackComp a b).app (P.X n)) h

/-- **The alternating rank class is locally the constant it should be.** If `h : Y' ⟶ Y` is such
that every rank locus of the complex meeting the image of `h` has alternating rank `m`, then the
restriction of the alternating rank class along `h` is `m` times `1`. -/
theorem res_complexRankClass_eq_zsmul_one {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (m : ℤ)
    (hm : ∀ ρ : ℤ →₀ ℕ, (h ⁻¹ᵁ complexRankLocus hP ρ : Set Y').Nonempty →
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ) = m) :
    TotalChowClass.res h hs (complexRankClass C sY hP) = m • 1 := by
  have hU := isClopenDecomposition_complexRankLoci hP
  refine TotalChowClass.eq_of_res_eq (hU.preimage h) fun ρ ↦ ?_
  obtain ⟨φ, hfac⟩ := exists_comp_ι_eq_preimage_complexRankLoci hP h ρ
  have : LocallyOfFiniteType (φ ≫ (complexRankLoci hP ρ).ι) := hfac ▸ inferInstance
  have := locallyOfFiniteType_of_comp φ (complexRankLoci hP ρ).ι
  have hpm : φ ≫ ((complexRankLoci hP ρ).ι ≫ sY) = (h ⁻¹ᵁ complexRankLoci hP ρ).ι ≫ sY' := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← TotalChowClass.res_res (complexRankLoci hP ρ).ι rfl _ hpm,
    res_complexRankClass_complexRankLocus, map_zsmul, map_one, map_zsmul, map_one]
  rcases (h ⁻¹ᵁ complexRankLocus hP ρ.down : Set Y').eq_empty_or_nonempty with he | hne
  · have : IsEmpty (h ⁻¹ᵁ complexRankLoci hP ρ).toScheme :=
      ⟨fun y ↦ (Set.eq_empty_iff_forall_notMem.1 he) y.1 y.2⟩
    exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · rw [hm ρ.down hne]

/-- **The terms of a locally bounded complex vanish off the support of the ranks on a rank
locus**, so the complex is bounded there, which is what the Euler characteristic of the derived
fibre is computed from. -/
theorem finite_not_isZero_of_isFiniteLocallyFreeOfRank {Y' : Scheme.{u}}
    (R : CochainComplex Y'.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.X n)
      (ρ n)) :
    {n : ℤ | ¬ IsZero (R.X n)}.Finite := by
  refine ρ.support.finite_toSet.subset fun n hn ↦ ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  have := hρ n
  rw [h0] at this
  exact hn (isZero_of_isFiniteLocallyFreeOfRank_zero _)

/-- **The alternating rank class is the alternating rank**: on a scheme over `Y` along which the
complex has constant ranks `σ`, the Euler characteristic of the derived fibre of the object the
complex represents is `∑_n (-1)^n σ(n)` at every point. -/
theorem chiDerivedFibre_pullbackComplex_eq {Y' : Scheme.{u}} (h : Y' ⟶ Y) (σ : ℤ →₀ ℕ)
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex h P).X n) (σ n))
    (hpc : RingedSpace.IsPseudoCoherent (X := Y'.toRingedSpace)
      (DerivedCategory.Q.obj (pullbackComplex h P))) (y : Y') :
    DerivedFibreBetti.chiDerivedFibre Y' (DerivedCategory.Q.obj (pullbackComplex h P)) hpc y =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (σ n : ℤ) :=
  DerivedFibreBetti.chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank Y'
    (pullbackComplex h P) (finite_not_isZero_of_isFiniteLocallyFreeOfRank _ σ hσ) σ hσ hpc y

/-- **The pullback of the complex to the preimage of a rank locus has constant ranks.** For
`g : Z ⟶ Y`, the complex `g^*ℰ^•` restricted to `g^{-1}(Y_ρ)` has the constant ranks `ρ`, because
`ℰ^•` has them on `Y_ρ` and `g` restricts to a morphism `g^{-1}(Y_ρ) ⟶ Y_ρ`. -/
theorem isFiniteLocallyFreeOfRank_pullbackComplex_preimage_complexRankLocus {Z : Scheme.{u}}
    (g : Z ⟶ Y) (ρ : ℤ →₀ ℕ) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex ((g ⁻¹ᵁ complexRankLocus hP ρ).ι ≫ g) P).X n) (ρ n) := by
  obtain ⟨φ, hfac⟩ := exists_comp_ι_eq_preimage_complexRankLoci hP g (ULift.up ρ)
  refine AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((pullbackPullbackIsoOfComp hfac (P.X n)).symm ≪≫
      (Scheme.Modules.pullbackComp (g ⁻¹ᵁ complexRankLocus hP ρ).ι g).app (P.X n)) ?_
  exact isFiniteLocallyFreeOfRank_pullbackComplex_X
    (pullbackComplex (complexRankLocus hP ρ).ι P) _ ρ
    (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ) n

include hP in
/-- **The alternating rank class along a morphism over which the complex has constant ranks.**
For `g : Z ⟶ Y` with `Z` nonempty and `g^*ℰ^•` of constant ranks `σ`, the restriction of the
alternating rank class along `g` is `∑_n (-1)^n σ(n)` times `1`: every rank locus of `ℰ^•` whose
preimage is nonempty has rank function `σ`. -/
theorem res_complexRankClass_of_constant_rank {Z : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] [Nonempty Z] (g : Z ⟶ Y) [LocallyOfFiniteType g]
    (hs : g ≫ sY = sZ) (σ : ℤ →₀ ℕ)
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g P).X n) (σ n)) :
    TotalChowClass.res g hs (complexRankClass C sY hP) =
      (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (σ n : ℤ)) • 1 := by
  refine res_complexRankClass_eq_zsmul_one C sY hP g hs _ fun ρ hne ↦ ?_
  obtain ⟨w, hw⟩ := hne
  have : Nonempty (g ⁻¹ᵁ complexRankLocus hP ρ).toScheme := ⟨⟨w, hw⟩⟩
  obtain rfl : ρ = σ := Finsupp.ext fun n ↦ by
    refine Scheme.Modules.isFiniteLocallyFreeOfRank_unique
      ((pullbackComplex ((g ⁻¹ᵁ complexRankLocus hP ρ).ι ≫ g) P).X n)
      (isFiniteLocallyFreeOfRank_pullbackComplex_preimage_complexRankLocus hP g ρ n) ?_ ⟨w, hw⟩
    exact isFiniteLocallyFreeOfRank_pullbackComplex_comp _ g _ n
      (isFiniteLocallyFreeOfRank_pullbackComplex_X (pullbackComplex g P) _ σ hσ n)
  rfl

include hP in
/-- **Restriction of the alternating rank class**: for `h : Y' ⟶ Y` the restriction of the
alternating rank class of `ℰ^•` is the alternating rank class of the termwise pullback
`h^*ℰ^•`. -/
theorem res_complexRankClass {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') :
    TotalChowClass.res h hs (complexRankClass C sY hP) =
      complexRankClass C sY'
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP) := by
  set hPb := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP with hPbdef
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hPb) fun σ ↦ ?_
  rw [res_complexRankClass_complexRankLocus C sY' hPb σ.down, TotalChowClass.res_res]
  rcases isEmpty_or_nonempty (complexRankLoci hPb σ).toScheme with _ | _
  · exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · refine res_complexRankClass_of_constant_rank C sY hP ((complexRankLoci hPb σ).ι ≫ h)
      (by rw [Category.assoc, hs]) σ.down fun n ↦ ?_
    exact isFiniteLocallyFreeOfRank_pullbackComplex_comp _ h _ n
      (isFiniteLocallyFreeOfRank_complexRankLocus hPb σ.down n)

/-- An object of `D(𝒪_Z)` represented by a locally bounded complex of finite locally free modules
is pseudo-coherent, which is what the Euler characteristic of its derived fibre is defined on. -/
theorem isPseudoCoherent_Q_of_isLocallyBoundedFiniteLocallyFree {Z : Scheme.{u}}
    {R : CochainComplex Z.Modules ℤ} (hR : IsLocallyBoundedFiniteLocallyFree R) :
    RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) (DerivedCategory.Q.obj R) :=
  DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
    ⟨R, Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree R hR,
      ⟨Iso.refl _⟩⟩

include hP hP' in
/-- **The alternating rank class depends only on the object the complex represents.** Two locally
bounded complexes of finite locally free `𝒪_Y`-modules representing the same object of `D(𝒪_Y)`
have the same alternating rank class.

This is the degree-zero third of Stacks 0ESZ, and unlike the rest of it the argument is
pointwise: over a nonempty open on which both complexes have constant ranks `ρ` and `σ` they are
both bounded, so each alternating rank is the Euler characteristic of the derived fibre of the
object there
(`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank`),
and that characteristic does not mention the complex
(`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_congr`). No constancy of the Euler
characteristic on `Y` is needed. -/
theorem complexRankClass_eq_of_iso (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    complexRankClass C sY hP = complexRankClass C sY hP' := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  rw [res_complexRankClass_complexRankLocus C sY hP ρ.down]
  refine (res_complexRankClass_eq_zsmul_one C sY hP' (complexRankLoci hP ρ).ι rfl _
    fun σ hne ↦ ?_).symm
  obtain ⟨w, hw⟩ := hne
  set W := (complexRankLoci hP ρ).ι ⁻¹ᵁ complexRankLocus hP' σ with hWdef
  have : Nonempty W.toScheme := ⟨⟨w, hw⟩⟩
  set g : W.toScheme ⟶ Y := W.ι ≫ (complexRankLoci hP ρ).ι with hgdef
  have hρg : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g P).X n) (ρ.down n) := fun n ↦
    isFiniteLocallyFreeOfRank_pullbackComplex_comp _ _ _ n
      (isFiniteLocallyFreeOfRank_pullbackComplex_X
        (pullbackComplex (complexRankLoci hP ρ).ι P) W.ι ρ.down
        (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down) n)
  have hσg : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex g P').X n) (σ n) :=
    isFiniteLocallyFreeOfRank_pullbackComplex_preimage_complexRankLocus hP'
      (complexRankLoci hP ρ).ι σ
  have hPg := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback g P hP
  have hP'g := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback g P' hP'
  have h1 := chiDerivedFibre_pullbackComplex_eq g ρ.down hρg
    (isPseudoCoherent_Q_of_isLocallyBoundedFiniteLocallyFree hPg) ⟨w, hw⟩
  have h2 := chiDerivedFibre_pullbackComplex_eq (P := P') g σ hσg
    (isPseudoCoherent_Q_of_isLocallyBoundedFiniteLocallyFree hP'g) ⟨w, hw⟩
  have h3 := congrFun (DerivedFibreBetti.chiDerivedFibre_congr W.toScheme
    (isPseudoCoherent_Q_of_isLocallyBoundedFiniteLocallyFree hPg)
    (isPseudoCoherent_Q_of_isLocallyBoundedFiniteLocallyFree hP'g)
    (pullbackComplexQIso hP hP' g e)) ⟨w, hw⟩
  exact h2.symm.trans (h3.symm.trans h1)

/-! ### The classes `P_p(ℰ^•)` and `ch(ℰ^•)` of a locally bounded complex -/

/-- **The class `P_p(ℰ^•)` of a locally bounded complex of finite locally free modules**, as a
total class: Newton's recursion of Stacks 0F9B (`AlgebraicGeometry.newtonPowerSum`) applied to
the components of the total Chern class `c(ℰ^•)`, with the alternating rank as the degree-zero
term. The recursion is the universal power-sum polynomial `P_p` of Stacks 0F9B wherever that
polynomial can be evaluated, by
`AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses`. -/
def complexPowerSum (p : ℕ) : TotalChowClass C sY :=
  newtonPowerSum (complexRankClass C sY hP)
    (fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ) (complexChern C sY hP)) p

/-- **The class `P_p(ℰ^•) ∈ A^p(Y)`**, the degree-`p` component of
`Stacks.Chow.complexPowerSum`. -/
@[stacks 0ESZ "the class P_p(E^bullet) in A^p(Y) of a locally bounded complex of finite locally \
free modules, as the universal power sum of Tag 0F9B applied to c(E^bullet) -- the degree-zero \
member being the alternating rank class"]
def complexPowerSumComponent (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sY (p : ℤ) :=
  complexPowerSum C sY hP p p

/-- **The degree-zero class is the alternating rank.** `P_0(ℰ^•)` is the alternating rank class,
the rank variable of Stacks 0F9B read on the complex. -/
theorem complexPowerSum_zero : complexPowerSum C sY hP 0 = complexRankClass C sY hP :=
  newtonPowerSum_zero _ _

/-- **The component `ch_p(ℰ^•) = P_p(ℰ^•)/p! ∈ A^p(Y) ⊗ 𝐐` of the Chern character of a locally
bounded complex of finite locally free modules.** The Chern character is read componentwise, as
the source reads it: `∏_{p ≥ 0} (A^p(Y) ⊗ 𝐐)` carries no ring structure, `𝐐 ⊗ -` not commuting
with infinite products. -/
def complexChernCharacterComponent (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sY (p : ℤ) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] complexPowerSumComponent C sY hP p

/-- **The Chern character `ch(ℰ^•) ∈ ∏_{p ≥ 0} (A^p(Y) ⊗ 𝐐)` of a locally bounded complex of
finite locally free modules**, the family of its components. -/
@[stacks 0ESZ "the class ch(E^bullet) in prod_{p >= 0} (A^p(Y) tensor Q) of a locally bounded \
complex of finite locally free modules, componentwise as ch_p = P_p/p! as the source reads it"]
def complexChernCharacter : fullRationalChowCohomology C (gysinSystemOfInvertible C) sY :=
  fun p ↦ complexChernCharacterComponent C sY hP p

include hP in
/-- **Restriction of `P_p(ℰ^•)`**: the restriction along `h : Y' ⟶ Y` of the class `P_p` of a
locally bounded complex is the class `P_p` of the termwise pullback. Restriction is a ring
homomorphism and commutes with taking homogeneous components, so it commutes with Newton's
recursion (`AlgebraicGeometry.map_newtonPowerSum`). -/
theorem res_complexPowerSum {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (p : ℕ) :
    TotalChowClass.res h hs (complexPowerSum C sY hP p) =
      complexPowerSum C sY'
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP) p := by
  rw [complexPowerSum, map_newtonPowerSum, res_complexRankClass, complexPowerSum]
  congr 1
  funext i
  rw [TotalChowClass.res_homComponent, res_complexChern]

include hP hP' in
/-- **Stacks 0ESZ for `P_p`.** The class `P_p(ℰ^•)` of a locally bounded complex of finite
locally free `𝒪_Y`-modules depends only on the object of `D(𝒪_Y)` that the complex represents:
it is a function of the total Chern class, which is independent by
`Stacks.Chow.complexChern_eq_of_iso`, and of the alternating rank class, which is independent by
`Stacks.Chow.complexRankClass_eq_of_iso`. -/
theorem complexPowerSum_eq_of_iso (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (p : ℕ) : complexPowerSum C sY hP p = complexPowerSum C sY hP' p := by
  rw [complexPowerSum, complexPowerSum, complexChern_eq_of_iso C sY hP hP' e,
    complexRankClass_eq_of_iso C sY hP hP' e]

include hP hP' in
/-- **Stacks 0ESZ for `P_p ∈ A^p(Y)`.** -/
@[stacks 0ESZ "the independence of the choice of the complex for P_p(E^bullet) in A^p(Y)"]
theorem complexPowerSumComponent_eq_of_iso
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') (p : ℕ) :
    complexPowerSumComponent C sY hP p = complexPowerSumComponent C sY hP' p := by
  rw [complexPowerSumComponent, complexPowerSumComponent,
    complexPowerSum_eq_of_iso C sY hP hP' e p]

include hP hP' in
/-- **Stacks 0ESZ for the Chern character.** Each component `ch_p(ℰ^•) ∈ A^p(Y) ⊗ 𝐐` depends only
on the object of `D(𝒪_Y)` that the complex represents. -/
theorem complexChernCharacterComponent_eq_of_iso
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') (p : ℕ) :
    complexChernCharacterComponent C sY hP p = complexChernCharacterComponent C sY hP' p := by
  rw [complexChernCharacterComponent, complexChernCharacterComponent,
    complexPowerSumComponent_eq_of_iso C sY hP hP' e p]

include hP hP' in
/-- **Stacks 0ESZ for the Chern character**, as the family
`ch(ℰ^•) ∈ ∏_{p ≥ 0} (A^p(Y) ⊗ 𝐐)`. -/
@[stacks 0ESZ "the independence of the choice of the complex for ch(E^bullet)"]
theorem complexChernCharacter_eq_of_iso
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    complexChernCharacter C sY hP = complexChernCharacter C sY hP' :=
  funext fun p ↦ complexChernCharacterComponent_eq_of_iso C sY hP hP' e p

end RankClass

end PerfectChern

/-! ### The alternating rank, `P_p` and `ch` of a perfect object whose Chern classes are defined -/

section PerfectPowerSum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- **The alternating rank classes of two presentations agree** after pulling back along
morphisms with equal composites to `X`: both complexes represent the derived pullback of `E`. -/
theorem complexRankClass_pullbackComplex_eq (H H' : EnvelopePresentation E) {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (h : Z ⟶ H.Y) (h' : Z ⟶ H'.Y)
    (e : h ≫ H.f = h' ≫ H'.f) :
    complexRankClass C sZ
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h H.P
          H.locallyBounded) =
      complexRankClass C sZ
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h' H'.P
          H'.locallyBounded) :=
  complexRankClass_eq_of_iso C sZ _ _ (H.pullbackRepresentationIso H' h h' e)

/-- **The alternating rank classes of two presentations agree after restriction** along
morphisms with equal composites to `X`. -/
theorem res_complexRankClass_eq_res_complexRankClass (H H' : EnvelopePresentation E)
    {Z : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (h : Z ⟶ H.Y)
    [LocallyOfFiniteType h] (h' : Z ⟶ H'.Y) [LocallyOfFiniteType h']
    (e : h ≫ H.f = h' ≫ H'.f) (hs : h ≫ (H.f ≫ sX) = sZ) (hs' : h' ≫ (H'.f ≫ sX) = sZ) :
    TotalChowClass.res h hs (complexRankClass C (H.f ≫ sX) H.locallyBounded) =
      TotalChowClass.res h' hs' (complexRankClass C (H'.f ≫ sX) H'.locallyBounded) := by
  rw [res_complexRankClass, res_complexRankClass]
  exact complexRankClass_pullbackComplex_eq C H H' sZ h h' e

/-- For an envelope presentation `(f, 𝓔^•)` of `E` there is a unique total class of `X` whose
restriction along `f` is the alternating rank class of `𝓔^•`. -/
theorem existsUnique_res_eq_complexRankClass (H : EnvelopePresentation E) :
    ∃! c : TotalChowClass C sX,
      TotalChowClass.res H.f rfl c = complexRankClass C (H.f ≫ sX) H.locallyBounded :=
  TotalChowClass.existsUnique_res_eq_of_isEnvelope H.f H.envelope rfl _
    (res_complexRankClass_eq_res_complexRankClass C sX H H (pullback.fst H.f H.f)
      (pullback.snd H.f H.f) pullback.condition rfl _)

/-- **The alternating rank class `r(E) ∈ A^0(X)` of an object whose Chern classes are defined**:
the unique total class whose restriction along the envelope of a presentation of `E` is the
alternating rank class of the presenting complex. This is the degree-zero power sum `P_0(E)` of
Stacks 0F9E (2). -/
def perfectRankClass (hE : HasDefinedChernClasses E) : TotalChowClass C sX :=
  (existsUnique_res_eq_complexRankClass C sX hE.some).exists.choose

/-- **The characterization of `r(E)`, at every presentation.** -/
theorem res_perfectRankClass (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E) :
    TotalChowClass.res H.f rfl (perfectRankClass C sX hE) =
      complexRankClass C (H.f ≫ sX) H.locallyBounded := by
  set H₀ := hE.some
  have hc₀ : TotalChowClass.res H₀.f rfl (perfectRankClass C sX hE) =
      complexRankClass C (H₀.f ≫ sX) H₀.locallyBounded :=
    (existsUnique_res_eq_complexRankClass C sX H₀).exists.choose_spec
  have hπ : IsEnvelope (pullback.snd H₀.f H.f) :=
    isEnvelope_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H₀.f H.f)
      H₀.envelope
  have e := (pullback.condition (f := H₀.f) (g := H.f)).symm
  refine TotalChowClass.res_injective_of_isEnvelope (pullback.snd H₀.f H.f) hπ rfl ?_
  have hs : pullback.fst H₀.f H.f ≫ (H₀.f ≫ sX) = pullback.snd H₀.f H.f ≫ (H.f ≫ sX) := by
    rw [← Category.assoc, ← e, Category.assoc]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr e _ hs,
    ← TotalChowClass.res_res H₀.f rfl _ hs, hc₀]
  exact res_complexRankClass_eq_res_complexRankClass C sX H₀ H _ _ e.symm _ _

/-- **Uniqueness of `r(E)`.** -/
theorem eq_perfectRankClass (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E)
    {c : TotalChowClass C sX}
    (hc : TotalChowClass.res H.f rfl c = complexRankClass C (H.f ≫ sX) H.locallyBounded) :
    c = perfectRankClass C sX hE :=
  TotalChowClass.res_injective_of_isEnvelope H.f H.envelope rfl
    (hc.trans (res_perfectRankClass C sX hE H).symm)

/-- **Stacks 0GUD for the alternating rank.** -/
theorem existsUnique_forall_res_eq_complexRankClass (hE : HasDefinedChernClasses E) :
    ∃! c : TotalChowClass C sX, ∀ H : EnvelopePresentation E,
      TotalChowClass.res H.f rfl c = complexRankClass C (H.f ≫ sX) H.locallyBounded :=
  ⟨perfectRankClass C sX hE, res_perfectRankClass C sX hE,
    fun _ hc ↦ eq_perfectRankClass C sX hE hE.some (hc hE.some)⟩

/-- **The class `P_p(E)` of a perfect object whose Chern classes are defined**, as a total class:
Newton's recursion of Stacks 0F9B applied to the components of the total Chern class `c(E)`, with
the alternating rank class `r(E)` as the degree-zero term. -/
def perfectPowerSum (hE : HasDefinedChernClasses E) (p : ℕ) : TotalChowClass C sX :=
  newtonPowerSum (perfectRankClass C sX hE)
    (fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ) (perfectChernClass C sX hE)) p

/-- **The class `P_p(E) ∈ A^p(X)`** of Stacks 0F9E (2), the degree-`p` component of
`Stacks.Chow.perfectPowerSum`. -/
@[stacks 0F9E "clause (2), the class P_p(E) in A^p(X): the universal power sum of Tag 0F9B \
applied to c(E), with the alternating rank class r(E) as its degree-zero member. It restricts to \
P_p(E^bullet) along the envelope of every presentation, which is the property Tag 0GUD defines \
it by (Stacks.Chow.res_perfectPowerSumComponent)"]
def perfectPowerSumComponent (hE : HasDefinedChernClasses E) (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  perfectPowerSum C sX hE p p

/-- The degree-zero class `P_0(E)` is the alternating rank class of `E`. -/
theorem perfectPowerSum_zero (hE : HasDefinedChernClasses E) :
    perfectPowerSum C sX hE 0 = perfectRankClass C sX hE :=
  newtonPowerSum_zero _ _

/-- **The component `ch_p(E) = P_p(E)/p! ∈ A^p(X) ⊗ 𝐐` of the Chern character of a perfect object
whose Chern classes are defined**, Stacks 0F9E (2), read componentwise as the source reads it. -/
def perfectChernCharacterComponent (hE : HasDefinedChernClasses E) (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] perfectPowerSumComponent C sX hE p

/-- **The Chern character `ch(E) ∈ ∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)` of a perfect object whose Chern
classes are defined**, Stacks 0F9E (2), the family of its components. -/
@[stacks 0F9E "clause (2), the class ch(E) in prod_{p >= 0} (A^p(X) tensor Q), componentwise as \
ch_p(E) = P_p(E)/p! as the source reads it"]
def perfectChernCharacter (hE : HasDefinedChernClasses E) :
    fullRationalChowCohomology C (gysinSystemOfInvertible C) sX :=
  fun p ↦ perfectChernCharacterComponent C sX hE p

/-- **`P_p(E)` restricts to `P_p(ℰ^•)` along the envelope of every presentation**, which is the
property Stacks 0F9E (2) defines the class by. -/
theorem res_perfectPowerSum (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E)
    (p : ℕ) :
    TotalChowClass.res H.f rfl (perfectPowerSum C sX hE p) =
      complexPowerSum C (H.f ≫ sX) H.locallyBounded p := by
  rw [perfectPowerSum, map_newtonPowerSum, res_perfectRankClass, complexPowerSum]
  congr 1
  funext i
  rw [TotalChowClass.res_homComponent, res_perfectChernClass]

/-- **`P_p(E) ∈ A^p(X)` restricts to `P_p(ℰ^•) ∈ A^p(Y)`.** -/
theorem res_perfectPowerSumComponent (hE : HasDefinedChernClasses E)
    (H : EnvelopePresentation E) (p : ℕ) :
    TotalChowClass.res H.f rfl (perfectPowerSum C sX hE p) p =
      complexPowerSumComponent C (H.f ≫ sX) H.locallyBounded p := by
  rw [res_perfectPowerSum, complexPowerSumComponent]

/-- **The classes `P_p(E)` and `ch_p(E)` depend only on the isomorphism class of `E`.** -/
theorem perfectPowerSum_congr {E' : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) (hE' : HasDefinedChernClasses E') (e : E ≅ E') (p : ℕ) :
    perfectPowerSum C sX hE p = perfectPowerSum C sX hE' p := by
  have hr : perfectRankClass C sX hE = perfectRankClass C sX hE' :=
    eq_perfectRankClass C sX hE' (hE.some.congr e) (res_perfectRankClass C sX hE hE.some)
  rw [perfectPowerSum, perfectPowerSum, hr, perfectChernClass_congr C sX hE hE' e]

/-- **`ch(E)` depends only on the isomorphism class of `E`.** -/
theorem perfectChernCharacter_congr {E' : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) (hE' : HasDefinedChernClasses E') (e : E ≅ E') :
    perfectChernCharacter C sX hE = perfectChernCharacter C sX hE' :=
  funext fun p ↦ by
    rw [perfectChernCharacter, perfectChernCharacter, perfectChernCharacterComponent,
      perfectChernCharacterComponent, perfectPowerSumComponent, perfectPowerSumComponent,
      perfectPowerSum_congr C sX hE hE' e p]

end PerfectPowerSum

/-! ### Stacks 0ESZ for the power sums and the Chern character of a bounded complex -/

section PowerSum

open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (P Q : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
  (hP : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
  (hQ : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (Q.X n))
  (hvanishP : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
  (hvanishQ : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (Q.X n))
  (E : DerivedCategory X.Modules) (hPE : Nonempty (E ≅ DerivedCategory.Q.obj P))
  (hQE : Nonempty (E ≅ DerivedCategory.Q.obj Q))
  (hE : ∀ i : ℤ,
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj E)) ∧
    HasTorAmplitude X.toRingedSpace ((DerivedCategory.singleFunctor X.Modules 0).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj E)) (-1) 0)

include hP hQ hvanishP hvanishQ hPE hQE hE in
/-- **Stacks 0ESZ for the class `P_p`, at the derived-category hypothesis of the source.** Two
bounded complexes of finite locally free `𝒪_X`-modules representing the same object `E` of
`D(𝒪_X)`, whose cohomology modules are perfect of Tor dimension at most one, have the same class
`P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n) ∈ A^p(X)`.

Against `Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison` this replaces the
degreewise data of `Stacks.Chow.ComplexCohomologyComparison` — Stacks 0F8J, the identification of
the cohomology modules, and Schanuel's lemma, Stacks 00O3 — by the isomorphism in `D(𝒪_X)` that
the source starts from. The constant-rank power sums and their additivity (Stacks 0F9B, 0F9C)
remain carried as `W`; see the implementation notes of this file.

It carries no `@[stacks 0ESZ]`, and deliberately so: against the source's clause it adds the
hypothesis `hE`, that the cohomology modules of `E` are perfect of Tor dimension at most one,
which the source does not assume but *reduces to* (by Stacks 02UC and the modification of
Stacks 0ESR), and it asks the two complexes to vanish outside one common window of degrees
rather than to be locally bounded. The clause itself, with no hypothesis beyond the source's and
with `P_p` constructed rather than carried, is `Stacks.Chow.complexPowerSumComponent_eq_of_iso`,
which is where this tag is registered. -/
theorem powerSumClassComplex_eq_of_iso_derivedCategory (W : PowerSumClassRule C Gy sX) (p : ℕ) :
    powerSumClassComplex C Gy sX W P a k p = powerSumClassComplex C Gy sX W Q a k p := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rw [powerSumClassComplex, powerSumClassComplex,
    alternatingKClass_eq_of_iso_derivedCategory P Q a k hP hQ hvanishP hvanishQ E hPE hQE hE]

include hP hQ hvanishP hvanishQ hPE hQE hE in
/-- **Stacks 0ESZ for the Chern character, at the derived-category hypothesis of the source.**
The component `ch_p(ℰ^•) = P_p(ℰ^•)/p! ∈ A^p(X) ⊗ 𝐐` of a bounded complex of finite locally free
`𝒪_X`-modules depends only on the object of `D(𝒪_X)` the complex represents, when the cohomology
modules of that object are perfect of Tor dimension at most one.

As for `Stacks.Chow.powerSumClassComplex_eq_of_iso_derivedCategory` this carries no
`@[stacks 0ESZ]`: the Tor-dimension hypothesis and the single common window of degrees are
restrictions the source does not impose, and the clause at the source's own hypotheses is
`Stacks.Chow.complexChernCharacter_eq_of_iso`, where the tag is registered. -/
theorem chernCharacterComplexComponent_eq_of_iso_derivedCategory (W : PowerSumClassRule C Gy sX)
    (p : ℕ) :
    chernCharacterComplexComponent C Gy sX W P a k p =
      chernCharacterComplexComponent C Gy sX W Q a k p := by
  rw [chernCharacterComplexComponent, chernCharacterComplexComponent,
    powerSumClassComplex_eq_of_iso_derivedCategory C Gy sX P Q a k hP hQ hvanishP hvanishQ E hPE
      hQE hE W p]

include hP hQ hvanishP hvanishQ hPE hQE hE in
/-- **Stacks 0ESZ for the total Chern class of a bounded complex, at the derived-category
hypothesis of the source**, in the carried form of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex`. The unconditional statement, for locally
bounded complexes and with the total Chern class constructed rather than carried, is
`Stacks.Chow.complexChern_eq_of_iso`. -/
theorem totalChernClassComplex_eq_of_iso_derivedCategory
    {R : ChowCohomologySeriesRing C Gy sX} (D : TotalChernClassSeries C Gy sX R) :
    totalChernClassComplex C Gy sX D P a k = totalChernClassComplex C Gy sX D Q a k := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rw [totalChernClassComplex, totalChernClassComplex,
    alternatingKClass_eq_of_iso_derivedCategory P Q a k hP hQ hvanishP hvanishQ E hPE hQE hE]

end PowerSum

end Stacks.Chow

end
