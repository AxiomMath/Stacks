module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRankIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseObjectNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerPolynomial

/-!
# The dévissage of the twisted Euler characteristics on a closed subspace

Let `k` be a field, `X` a proper algebraic space over `k`, `L₁, …, L_r` invertible
`𝒪_X`-modules and `i : Z ⟶ X` a closed subspace.  The proof of Stacks 0DN4 replaces `X` by the
scheme theoretic support `Z` of the module and runs the dévissage of Stacks 08AN on `Z` for the
property that the function

`n ↦ χ(X, i_*𝒢 ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`

is the restriction to the integral tuples of a rational polynomial of total degree at most
`dim Z`.  This file carries out that dévissage.  It takes two inputs as hypotheses, both
discharged in `StacksFrontier/AlgebraicGeometry/Spaces/TwistedEulerNumericalPolynomialProper.lean`,
where Stacks 0DN4 is assembled:

* the additivity of the twisted Euler characteristics along every short exact sequence of
  coherent `𝒪_X`-modules (`AlgebraicGeometry.Space.HasAdditiveTwistedEulerOnCoherent`), and
* condition (3) of the dévissage, a witness on every reduced closed subspace of `Z` with
  irreducible space of points.

Everything else is proved.  The dévissage itself is Stacks 08AN,
`AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree'`, whose one extra input,
the conclusion of Stacks 07UR, is
`AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`.  Conditions (1) and (2) of the
dévissage, and the zero-module condition that the library's form of Stacks 08AN asks for, are
derived from the additivity alone.  No isomorphism invariance, biproduct computation or
vanishing of the cohomology of a zero module is used beyond what additivity gives: each of those
is read off a suitable short exact sequence.

## Main definitions

* `AlgebraicGeometry.Space.HasAdditiveTwistedEulerOnCoherent`: additivity of the twisted Euler
  characteristics along every short exact sequence of coherent modules.
* `AlgebraicGeometry.Space.HasTwistedEulerPolynomialAlong`: the property of a module `𝒢` on a
  closed subspace `i : Z ⟶ X` that `𝒢` is coherent and that the twisted Euler characteristics of
  `i_*𝒢` on `X` are the values of a rational polynomial of total degree at most `d`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_twistedModuleUlift_of_isProper`: the twists of a coherent
  module on a proper algebraic space over a field are coherent.
* `AlgebraicGeometry.Space.eulerCharacteristic_twistedModuleUlift_eq_zero_of_isZero`: the twisted
  Euler characteristics of a zero module vanish.
* `AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE.of_iso`: the conclusion of
  Stacks 0DN4 is invariant under isomorphism of the module.
* `AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE.of_biproduct`: condition (2) of
  the dévissage, descent from a direct sum of copies.
* `AlgebraicGeometry.Space.hasTwistedEulerPolynomialAlong_of_isCoherent`: **the dévissage**,
  every coherent module on `Z` has the property, granted the two inputs above.
* `AlgebraicGeometry.Space.isTwistedEulerNumericalPolynomial_of_witness`: Stacks 0DN4 in the
  form `AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial`, granted the two inputs; the
  registered form is `AlgebraicGeometry.Space.isTwistedEulerNumericalPolynomial_of_isCoherent`.
* `AlgebraicGeometry.Space.isNoetherian_of_isClosedImmersion_of_isProper`: a closed subspace of
  an algebraic space proper over a Noetherian ring is Noetherian.

## Implementation notes

The property on `Z` packages the coherence of `𝒢` with the polynomial statement, because the
library's Stacks 08AN quantifies over all `𝒪_Z`-modules and the twisted Euler characteristics are
only defined for coherent ones.  The bound `d` is a parameter; the tag takes it to be `dim Z`.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

/-! ### Closed subspaces of a proper space are Noetherian -/

/-- **A closed subspace of an algebraic space proper over a Noetherian ring is Noetherian.**  The
composite `Z ⟶ X ⟶ Spec A` is proper, a closed immersion being proper, and an algebraic space
proper over `Spec A` is Noetherian
(`AlgebraicGeometry.Space.isNoetherian_of_isProper_baseObject`). -/
theorem isNoetherian_of_isClosedImmersion_of_isProper (A : Type u) [CommRing A]
    [IsNoetherianRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    {Z X : AlgebraicSpaces B (Spec (.of A)) hA} (f : X.1 ⟶ yoneda.obj (baseObject A B hA))
    (hf : IsProper B (Spec (.of A)) hA f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom) :
    IsNoetherian B (Spec (.of A)) hA B.contains_terminal Z.1 :=
  isNoetherian_of_isProper_baseObject A B hA Z.1 Z.2 (i.hom ≫ f)
    (isProper_comp B (Spec (.of A)) hA Z.2 X.2
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) i.hom f
      (isProper_of_isClosedImmersion B (Spec (.of A)) hA Z.2 X.2 i.hom hi) hf)

/-! ### Split sequences of direct sums of copies -/

section Biproducts

/-- The direct sum of no copies of an object is a zero object. -/
private theorem isZero_biproduct_fin_zero {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (M : C) : IsZero (⨁ fun _ : Fin 0 => M) :=
  (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j => j.elim0)

/-- A morphism into a zero object is an epimorphism. -/
private theorem epi_of_isZero_target {C : Type*} [Category* C] {M N : C} (hN : IsZero N)
    (g : M ⟶ N) : Epi g :=
  ⟨fun _ _ _ => hN.eq_of_src _ _⟩

/-- The split short exact sequence `0 ⟶ M ⟶ ⨁_{Fin (s+1)} M ⟶ ⨁_{Fin s} M ⟶ 0` which includes
`M` as the summand `0` and projects onto the remaining summands. -/
private abbrev biproductSuccShortComplex {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (M : C) (s : ℕ) : ShortComplex C :=
  ShortComplex.mk (biproduct.ι (fun _ : Fin (s + 1) => M) 0)
    (biproduct.desc (Fin.cases 0 fun j => biproduct.ι (fun _ : Fin s => M) j))
    (by simp)

/-- The sequence `biproductSuccShortComplex` is split, with retraction the projection onto the
summand `0` and section the inclusion of the remaining summands. -/
private def biproductSuccSplitting {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (M : C) (s : ℕ) : (biproductSuccShortComplex M s).Splitting where
  r := biproduct.π _ 0
  s := biproduct.desc fun j => biproduct.ι (fun _ : Fin (s + 1) => M) j.succ
  f_r := by simp [biproductSuccShortComplex]
  s_g := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    simp [biproductSuccShortComplex]
  id := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    cases i using Fin.cases with
    | zero => cases j using Fin.cases <;> simp
    | succ i =>
    cases j using Fin.cases with
    | zero => simp [Fin.succ_ne_zero]
    | succ j => simp [Fin.succ_ne_zero]

end Biproducts

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk) {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]

/-! ### Coherence of the twists -/

include hf in
/-- **The twists of a coherent module on a proper algebraic space over a field are coherent.**
A proper algebraic space over a field is locally Noetherian, which is the hypothesis of
`AlgebraicGeometry.Space.isCoherent_twistedModuleUlift`. -/
theorem isCoherent_twistedModuleUlift_of_isProper
    (M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hM : IsCoherent B (Spec (.of k)) hk X.1 X.2 M) (n : Fin r → ℤ) :
    IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n) :=
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf⟩
  isCoherent_twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n hM

/-! ### Additivity along short exact sequences of coherent modules -/

/-- **Additivity of the twisted Euler characteristics along every short exact sequence of
coherent `𝒪_X`-modules.**  For `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` short exact with coherent terms,
`χ(X, F₂ ⊗ L^{⊗ n}) = χ(X, F₁ ⊗ L^{⊗ n}) + χ(X, F₃ ⊗ L^{⊗ n})` for every integral tuple `n`.

This is Stacks 0DN2 at the twisted sequences; it is the input of conditions (1) and (2) of the
dévissage, and it is a named hypothesis here. -/
def HasAdditiveTwistedEulerOnCoherent : Prop :=
  ∀ E : ShortComplex (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2), E.ShortExact →
    ∀ (h₁ : IsCoherent B (Spec (.of k)) hk X.1 X.2 E.X₁)
      (h₂ : IsCoherent B (Spec (.of k)) hk X.1 X.2 E.X₂)
      (h₃ : IsCoherent B (Spec (.of k)) hk X.1 X.2 E.X₃),
      haveI := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L E.X₁ h₁
      haveI := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L E.X₂ h₂
      haveI := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L E.X₃ h₃
      HasAdditiveTwistedEuler.{u, w} k B hk X f hf E.X₁ E.X₂ E.X₃ L

/-- The twisted Euler characteristic `χ(X, M ⊗ L^{⊗ n})` of a coherent module `M`, the coherence
of the twist being supplied by `AlgebraicGeometry.Space.isCoherent_twistedModuleUlift_of_isProper`.
A private name for the term, so that `omega` sees one atom for it. -/
private def chiTwist (M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hM : IsCoherent B (Spec (.of k)) hk X.1 X.2 M) (n : Fin r → ℤ) : ℤ :=
  @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
    (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n)
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L M hM n)

variable {k B hk X f hf L}

/-- **The twisted Euler characteristics of a zero module vanish**, granted additivity: the
sequence `0 ⟶ M ⟶ M ⟶ M ⟶ 0` with maps `𝟙` and `0` is short exact when `M` is zero, and
additivity along it reads `χ = χ + χ`. -/
theorem eulerCharacteristic_twistedModuleUlift_eq_zero_of_isZero
    (hadd : HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L)
    {M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2} (hM : IsZero M) (n : Fin r → ℤ) :
    @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n)
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L M
        (isCoherent_of_isZero B (Spec (.of k)) hk X hM) n) = 0 := by
  have hc := isCoherent_of_isZero B (Spec (.of k)) hk X hM
  let E : ShortComplex (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) :=
    ShortComplex.mk (𝟙 M) (0 : M ⟶ M) (by simp)
  have hE : E.ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hM
      mono_f := inferInstanceAs (Mono (𝟙 M))
      epi_g := epi_of_isZero_target hM _ }
  let χ := chiTwist.{u, w} k B hk X f hf L
  have h : χ M hc n = χ M hc n + χ M hc n := hadd E hE hc hc hc n
  exact (by omega : χ M hc n = 0)

/-! ### Isomorphism invariance and descent from a direct sum -/

/-- **The conclusion of Stacks 0DN4 is invariant under isomorphism of the module**, granted
additivity: the sequence `0 ⟶ M ⟶ N ⟶ 0 ⟶ 0` built from an isomorphism `M ≅ N` is short
exact, so the twisted Euler characteristics of `M` and `N` agree. -/
theorem HasTwistedEulerPolynomialOfDegreeLE.of_iso
    (hadd : HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L)
    {M N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2} (e : M ≅ N)
    (hM : IsCoherent B (Spec (.of k)) hk X.1 X.2 M) (hN : IsCoherent B (Spec (.of k)) hk X.1 X.2 N)
    {d : WithBot ℕ∞}
    (h : @HasTwistedEulerPolynomialOfDegreeLE.{u, w} k _ B hk X r f hf N L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L N hN) d) :
    @HasTwistedEulerPolynomialOfDegreeLE.{u, w} k _ B hk X r f hf M L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L M hM) d := by
  have h0 : IsZero (⨁ fun _ : Fin 0 => N) := isZero_biproduct_fin_zero N
  have : HasZeroObject (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) := ⟨⟨_, h0⟩⟩
  let E : ShortComplex (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) :=
    ShortComplex.mk e.hom (0 : N ⟶ ⨁ fun _ : Fin 0 => N) (by simp)
  let σ : E.Splitting :=
    { r := e.inv
      s := 0
      f_r := e.hom_inv_id
      s_g := h0.eq_of_src _ _
      id := by simp [E] }
  have hc0 := isCoherent_of_isZero B (Spec (.of k)) hk X h0
  obtain ⟨P, hP, hdeg⟩ := h
  refine ⟨P, fun n => ?_, hdeg⟩
  let χ := chiTwist.{u, w} k B hk X f hf L
  have hn : χ N hN n = χ M hM n + χ _ hc0 n := hadd E σ.shortExact hM hN hc0 n
  have hz : χ _ hc0 n = 0 := eulerCharacteristic_twistedModuleUlift_eq_zero_of_isZero hadd h0 n
  have hNM : χ N hN n = χ M hM n := by omega
  exact (hP n).trans (congrArg (fun m : ℤ => (m : ℚ)) hNM)

/-- **The twisted Euler characteristics of `⨁_{Fin s} M` are `s` times those of `M`**, granted
additivity, by induction on `s` along `biproductSuccShortComplex`. -/
private theorem eulerCharacteristic_twistedModuleUlift_biproduct
    (hadd : HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L)
    (M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hM : IsCoherent B (Spec (.of k)) hk X.1 X.2 M)
    (n : Fin r → ℤ) (s : ℕ) :
    @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 (⨁ fun _ : Fin s => M) L n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _
          (isCoherent_biproductConst B (Spec (.of k)) hk X.1 X.2 M hM s) n) =
      s * @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M L n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L M hM n) := by
  induction s with
  | zero =>
    have hz : IsZero (⨁ fun _ : Fin 0 => M) := isZero_biproduct_fin_zero M
    simpa using eulerCharacteristic_twistedModuleUlift_eq_zero_of_isZero hadd hz n
  | succ s ih =>
    let χ := chiTwist.{u, w} k B hk X f hf L
    have hc := isCoherent_biproductConst B (Spec (.of k)) hk X.1 X.2 M hM
    have h : χ _ (hc (s + 1)) n = χ M hM n + χ _ (hc s) n :=
      hadd _ (biproductSuccSplitting M s).shortExact hM (hc (s + 1)) (hc s) n
    have ih' : χ _ (hc s) n = s * χ M hM n := ih
    show χ _ (hc (s + 1)) n = ((s + 1 : ℕ) : ℤ) * χ M hM n
    rw [h, ih']
    push_cast
    ring

/-- **Condition (2) of the dévissage: descent from a direct sum of copies.**  Granted additivity,
if the conclusion of Stacks 0DN4 holds for `⨁_{Fin s} M` with `s ≥ 1` then it holds for `M`, the
representing polynomial being divided by `s`. -/
theorem HasTwistedEulerPolynomialOfDegreeLE.of_biproduct
    (hadd : HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L)
    {M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2} (hM : IsCoherent B (Spec (.of k)) hk X.1 X.2 M)
    {s : ℕ} (hs : 1 ≤ s) {d : WithBot ℕ∞}
    (h : @HasTwistedEulerPolynomialOfDegreeLE.{u, w} k _ B hk X r f hf (⨁ fun _ : Fin s => M) L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _
        (isCoherent_biproductConst B (Spec (.of k)) hk X.1 X.2 M hM s)) d) :
    @HasTwistedEulerPolynomialOfDegreeLE.{u, w} k _ B hk X r f hf M L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L M hM) d := by
  obtain ⟨P, hP, hdeg⟩ := h
  have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨MvPolynomial.C (s : ℚ)⁻¹ * P, fun n => ?_, ?_⟩
  · have h1 := hP n
    rw [eulerCharacteristic_twistedModuleUlift_biproduct hadd M hM n s] at h1
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, h1]
    push_cast
    field_simp
  · rcases hdeg with rfl | hdeg
    · exact Or.inl (mul_zero _)
    · refine Or.inr (le_trans ?_ hdeg)
      exact_mod_cast (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-! ### The dévissage on a closed subspace -/

section Devissage

variable (k B hk X f hf L)
variable (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)

/-- **The property of a module on a closed subspace run through the dévissage.**  A module `𝒢`
on a closed subspace `i : Z ⟶ X` has it when `𝒢` is coherent and the twisted Euler
characteristics `χ(X, i_*𝒢 ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})` are the values at the integral
tuples of a rational polynomial which is zero or of total degree at most `d`. -/
def HasTwistedEulerPolynomialAlong (d : WithBot ℕ∞)
    (G : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2) : Prop :=
  ∃ hG : IsCoherent B (Spec (.of k)) hk Z.1 Z.2 G,
    @HasTwistedEulerPolynomialOfDegreeLE.{u, w} k _ B hk X r f hf
      ((modulePushforward B (Spec (.of k)) hk i).obj G) L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _
        (isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi G hG))
      d

variable {k B hk X f hf L Z i hi}

/-- **The dévissage of Stacks 0DN4 on a closed subspace.**  Let `i : Z ⟶ X` be a closed subspace
of a proper algebraic space over a field, with `Z` Noetherian.  Granted the additivity of the
twisted Euler characteristics along short exact sequences of coherent `𝒪_X`-modules and, for
every reduced closed subspace of `Z` with irreducible space of points, a coherent `𝒪_Z`-module
with that scheme theoretic support having the property, every coherent `𝒪_Z`-module has the
property: the twisted Euler characteristics of `i_*𝒢` are the values of a rational polynomial
which is zero or of total degree at most `d`.

This is Stacks 08AN on `Z`, its Stacks 07UR input being
`AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent`.  Its zero-module condition and its
conditions (1) and (2) are proved here from additivity: the direct image along a closed
immersion is exact, so a short exact sequence on `Z` gives one on `X`. -/
theorem hasTwistedEulerPolynomialAlong_of_isCoherent
    (hadd : HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L)
    (hZ : IsNoetherian B (Spec (.of k)) hk B.contains_terminal Z.1) {d : WithBot ℕ∞}
    (hwit : HasCoherentWitnessOnIntegralSubspaces B (Spec (.of k)) hk Z
      (HasTwistedEulerPolynomialAlong.{u, w} k B hk X f hf L Z i hi d))
    (G : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2)
    (hG : IsCoherent B (Spec (.of k)) hk Z.1 Z.2 G) :
    HasTwistedEulerPolynomialAlong.{u, w} k B hk X f hf L Z i hi d G := by
  have hXN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf
  have hcoh : ∀ M, IsCoherent B (Spec (.of k)) hk Z.1 Z.2 M →
      IsCoherent B (Spec (.of k)) hk X.1 X.2 ((modulePushforward B (Spec (.of k)) hk i).obj M) :=
    fun M hM => isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk hXN i hi M hM
  have hexact := (exactFunctor_iff _).1
    (exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity B (Spec (.of k)) hk
      i hi)
  have := hexact.1
  have := hexact.2
  have : HasFiniteProducts (Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2) :=
    Abelian.has_finite_products
  have : (modulePushforward B (Spec (.of k)) hk i).IsRightAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B (Spec (.of k)) hk i⟩⟩
  have : (modulePushforward B (Spec (.of k)) hk i).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have : HasBinaryProducts (Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2) :=
    hasLimitsOfShape_discrete (Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2) WalkingPair
  have : (modulePushforward B (Spec (.of k)) hk i).Additive :=
    Functor.additive_of_preserves_binary_products _
  refine property_of_integralWitness_and_twoOutOfThree' B (Spec (.of k)) hk B.contains_terminal Z hZ
    (fun M hM => hasIdealDevissage_of_isCoherent B (Spec (.of k)) hk B.contains_terminal Z hZ M hM)
    _ (fun M hM => ?_) (fun E hE h₁ h₂ h₃ => ?_) (fun M s hs hP => ?_) hwit G hG
  · -- zero modules
    have hc := isCoherent_of_isZero B (Spec (.of k)) hk Z hM
    have hz : IsZero ((modulePushforward B (Spec (.of k)) hk i).obj M) :=
      Functor.map_isZero _ hM
    refine ⟨hc, 0, fun n => ?_, Or.inl rfl⟩
    rw [map_zero]
    exact_mod_cast (eulerCharacteristic_twistedModuleUlift_eq_zero_of_isZero hadd hz n).symm
  · -- two out of three
    have hE' := hE.map_of_exact (modulePushforward B (Spec (.of k)) hk i)
    have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _ (hcoh _ h₁)
    have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _ (hcoh _ h₂)
    have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _ (hcoh _ h₃)
    have ha : HasAdditiveTwistedEuler.{u, w} k B hk X f hf
        ((modulePushforward B (Spec (.of k)) hk i).obj E.X₁)
        ((modulePushforward B (Spec (.of k)) hk i).obj E.X₂)
        ((modulePushforward B (Spec (.of k)) hk i).obj E.X₃) L :=
      hadd _ hE' (hcoh _ h₁) (hcoh _ h₂) (hcoh _ h₃)
    refine ⟨fun ⟨_, p₁⟩ ⟨_, p₃⟩ => ⟨h₂, ?_⟩, fun ⟨_, p₂⟩ ⟨_, p₃⟩ => ⟨h₁, ?_⟩,
      fun ⟨_, p₁⟩ ⟨_, p₂⟩ => ⟨h₃, ?_⟩⟩
    · exact hasTwistedEulerPolynomialOfDegreeLE_middle.{u, w} k B hk X f hf _ _ _ L d ha p₁ p₃
    · exact hasTwistedEulerPolynomialOfDegreeLE_left.{u, w} k B hk X f hf _ _ _ L d ha p₂ p₃
    · exact hasTwistedEulerPolynomialOfDegreeLE_right.{u, w} k B hk X f hf _ _ _ L d ha p₁ p₂
  · -- descent from a direct sum of copies
    obtain ⟨hc, hp⟩ := hP
    have hM := isCoherent_of_isCoherent_biproductConst B (Spec (.of k)) hk Z M s hs hc
    refine ⟨hM, HasTwistedEulerPolynomialOfDegreeLE.of_biproduct hadd (hcoh M hM) hs ?_⟩
    exact HasTwistedEulerPolynomialOfDegreeLE.of_iso hadd
      ((modulePushforward B (Spec (.of k)) hk i).mapBiproduct fun _ : Fin s => M).symm
      (isCoherent_biproductConst B (Spec (.of k)) hk X.1 X.2 _ (hcoh M hM) s) (hcoh _ hc) hp

/-- **Stacks 0DN4, granted its two remaining inputs.**  For a coherent `𝒪_X`-module `F` on a
proper algebraic space over a field, every closed subspace `i : Z ⟶ X` with `F ≅ i_*𝒢` for a
coherent `𝒪_Z`-module `𝒢` bounds the degree of the numerical polynomial of the twisted Euler
characteristics of `F` by `dim Z`, provided that

* the twisted Euler characteristics are additive along short exact sequences of coherent
  modules (`hadd`), and
* the witness condition of the dévissage holds on every closed subspace (`hwit`).

This is `AlgebraicGeometry.Space.hasTwistedEulerPolynomialAlong_of_isCoherent` at `𝒢`,
transported along `F ≅ i_*𝒢`.  The empty-support case needs no separate argument: on a closed
subspace with no points every coherent module is reached by the zero-module condition of the
dévissage, whose polynomial is `0`. -/
theorem isTwistedEulerNumericalPolynomial_of_witness
    (hadd : HasAdditiveTwistedEulerOnCoherent.{u, w} k B hk X f hf L)
    (hwit : ∀ (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom),
        HasCoherentWitnessOnIntegralSubspaces B (Spec (.of k)) hk Z
          (HasTwistedEulerPolynomialAlong.{u, w} k B hk X f hf L Z i hi
            (dimension B (Spec (.of k)) hk Z.1 Z.2)))
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F) :
    @IsTwistedEulerNumericalPolynomial.{u, w} k _ B hk X r f hf F L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF) := by
  intro Z i hi G hG e
  obtain ⟨_, h⟩ := hasTwistedEulerPolynomialAlong_of_isCoherent hadd
    (isNoetherian_of_isClosedImmersion_of_isProper k B hk f hf i hi) (hwit Z i hi) G hG
  exact HasTwistedEulerPolynomialOfDegreeLE.of_iso hadd e hF
    (isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi G hG) h

end Devissage

end AlgebraicGeometry.Space

end
