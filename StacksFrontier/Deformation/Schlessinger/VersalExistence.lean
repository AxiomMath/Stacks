module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.RingTheory.Ideal.Quotient.Small
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.SmallExtensionPullback
public import StacksFrontier.Deformation.Completed.InverseLimit
public import StacksFrontier.Deformation.Completed.PowerSeries
public import StacksFrontier.Deformation.Completed.SmoothModel
public import StacksFrontier.Deformation.FormalObject.VersalCriterion
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.Schlessinger.AssociatedTangentSpace
public import StacksFrontier.Deformation.Smallness
public import StacksFrontier.Deformation.VersalObject.LeastLiftingIdeal
public import StacksFrontier.RingTheory.FormallySmooth.SpecialFibre
import StacksFrontier.RingTheory.LocalRing.AdicCompleteRingEquiv
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.InjectiveBaseChange

/-!
# Schlessinger's existence theorem for versal formal objects

Schlessinger's theorem asserts that a predeformation category over `𝒞_Λ` satisfying his
conditions (S1) and (S2), and with a finite-dimensional tangent space, has a versal formal
object. This file carries out the construction that proves it: a formally smooth complete local
`Λ`-algebra with residue field `k`, the tower of presentations produced by iterating the
least-lifting-ideal construction of Stacks 06SZ, the formal object obtained from that tower by
passing to the limit, and the lifting step that verifies condition (2) of the versality
criterion of Stacks 06IU.

## Main definitions

* `Deformation.PresentedObject`: an object of a category cofibered in groupoids over `𝒞_Λ`
  together with a surjective presentation of its base by a fixed object of the completed base
  category. These are the `ξ_n` of Schlessinger's construction, each presented by the fixed
  ambient power series algebra `S`.

## Main results

* `Deformation.exists_formallySmooth_completeLocalAlgebra`: there is a Noetherian complete
  local `Λ`-algebra with residue field `k` which is formally smooth over `Λ` for its
  maximal-ideal-adic topology. This is the smoothness half of Stacks 06SM, obtained by
  completing a polynomial presentation of `k` at the kernel of that presentation.
* `Deformation.exists_tangent_generating_object`: with a finite-dimensional tangent space there
  is a single object over a finite-dimensional square-zero extension whose isomorphism class
  hits every tangent vector; this is Step 2 of Schlessinger's construction.
* `Deformation.exists_presented_tower`: condition (S1) produces the tower of presentations with
  the minimality property of Stacks 06SZ at each stage.
* `Deformation.exists_formalObject_of_presentedTower`: the tower assembles into a formal
  object whose base is the quotient of the ambient algebra by the intersection of the kernels,
  together with comparison maps from the tower to the levels of that formal object.
* `Deformation.exists_base_lift_of_tower_map`: a small-extension triangle over the base of
  that formal object is filled in, which is condition (2) of the criterion of Stacks 06IU;
  `Deformation.exists_base_lift_of_tower_over` is the form of this in which the small extension
  is given as an arrow of the base category together with a lift of it.
* `Deformation.formalLevelProjection`: the presentation of the `n`-th level of a formal object
  by its base, together with its surjectivity, its compatibility with the identifications of
  the residue fields, and its naturality in the formal object.
* `Deformation.exists_formalObject_differential_surjective_and_level_lifts`: the formal object
  produced by the construction satisfies both conditions of the criterion of Stacks 06IU, the
  second one in the form in which the small extension and the triangle are given inside `F`.
* `Deformation.exists_versalFormalObject`: Schlessinger's existence theorem itself, Stacks
  06IW.

## Implementation notes

The carrier universe of the Artinian algebras is kept independent of the universes of `Λ` and
`k`, as in Stacks 06GS and 06IH; the ambient complete local algebra is built in the carrier
universe of `Λ` and then transported by `Deformation.shrinkCompleteLocalAlgebra`, which uses
that a Noetherian local ring is small whenever its residue field is.

Schlessinger's construction needs the smooth base object of Stacks 06SM only through its
formal smoothness, never through its cotangent invariants, so only the smoothness half is
developed here, and it needs no Jacobian argument: a polynomial algebra over `Λ` is formally
smooth, and formal smoothness for the adic topology passes to the completion.

## References

* [Stacks Project, Tag 06IW](https://stacks.math.columbia.edu/tag/06IW)
* [Stacks Project, Tag 06SM](https://stacks.math.columbia.edu/tag/06SM)
-/

@[expose] public section

namespace Deformation

open CategoryTheory IsLocalRing

universe m t u v w uF vF

/-! ### Smallness and universe descent for complete local algebras -/

section Smallness

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An object of the completed base category is small in any universe in which `k` is. -/
private theorem small_completeLocalAlgebra (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    [Small.{t} k] : Small.{t} R := by
  let : IsNoetherianRing R := R.completeLocal.isNoetherian
  let : Small.{t} (ResidueField R) := small_map R.residueEquiv.toEquiv
  exact Module.small_of_small_residueField

/-- An object of the completed base category, transported into the smallest carrier universe
in which `k` lives. -/
private noncomputable def shrinkCompleteLocalAlgebra
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) [Small.{t} k] :
    CompleteLocalAlgCat.{u, t, w} Λ k := by
  letI : IsNoetherianRing R := R.completeLocal.isNoetherian
  letI : IsLocalRing R := R.completeLocal.isLocal
  letI : IsAdicComplete (maximalIdeal R) R := R.completeLocal.isComplete
  letI : Small.{t} R := small_completeLocalAlgebra R
  let T := Shrink.{t} R
  let e : T ≃ₐ[Λ] R := Shrink.algEquiv Λ R
  letI : IsLocalRing T := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  letI : IsNoetherianRing T := isNoetherianRing_of_ringEquiv R e.symm.toRingEquiv
  exact
    { carrier := T
      completeLocal :=
        { isNoetherian := inferInstance
          isLocal := inferInstance
          isComplete := isAdicComplete_maximalIdeal_of_ringEquiv e.symm.toRingEquiv }
      residueEquiv :=
        (ResidueField.mapAlgEquiv (R := Λ) e).trans R.residueEquiv }

/-- The transported object is isomorphic, as a `Λ`-algebra, to the original one. -/
private noncomputable def shrinkCompleteLocalAlgebraEquiv
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) [Small.{t} k] :
    shrinkCompleteLocalAlgebra.{t} R ≃ₐ[Λ] R := by
  letI : IsNoetherianRing R := R.completeLocal.isNoetherian
  letI : IsLocalRing R := R.completeLocal.isLocal
  letI : Small.{t} R := small_completeLocalAlgebra R
  exact Shrink.algEquiv Λ R

end Smallness

/-! ### A formally smooth complete local algebra with residue field `k` -/

section SmoothModel

/-- A field that is finite as a module over `Λ` is a quotient of a polynomial algebra over `Λ`
in finitely many variables. -/
private theorem exists_mvPolynomial_surjection (Λ : Type u) (k : Type w)
    [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k] :
    ∃ (n : ℕ) (q : MvPolynomial (Fin n) Λ →ₐ[Λ] k), Function.Surjective q := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Λ) (M := k)
  refine ⟨n, MvPolynomial.aeval s, ?_⟩
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span Λ (Set.range s) := by rw [hs]; trivial
  exact Algebra.span_le_adjoin Λ (Set.range s) hx

/-- There is a Noetherian complete local `Λ`-algebra with residue field `k` which is formally
smooth over `Λ` for its maximal-ideal-adic topology: complete a polynomial presentation of `k`
at the kernel of that presentation, then transport the result into the carrier universe of
`k`. This is the base object used to present a versal formal object. -/
@[ega "0 19.6.5.2" "more general", ega "0 22.2.6" "special case"]
public theorem exists_formallySmooth_completeLocalAlgebra (Λ : Type u) (k : Type w)
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    [Small.{t} k] :
    ∃ R : CompleteLocalAlgCat.{u, t, w} Λ k,
      RingHom.FormallySmoothNAdic.{t} (algebraMap Λ R) (maximalIdeal R) := by
  obtain ⟨n, q, hq⟩ := exists_mvPolynomial_surjection Λ k
  let P := MvPolynomial (Fin n) Λ
  have hfg : (RingHom.ker q.toRingHom).FG := IsNoetherian.noetherian _
  let Rbig := completionObjectOfSurjection q hq hfg
  let : IsLocalRing Rbig := Rbig.completeLocal.isLocal
  let : IsNoetherianRing Rbig := Rbig.completeLocal.isNoetherian
  let : IsAdicComplete (maximalIdeal Rbig) Rbig := Rbig.completeLocal.isComplete
  have hsmooth : RingHom.FormallySmoothNAdic.{t} (algebraMap Λ Rbig) (maximalIdeal Rbig) := by
    rw [completionObjectOfSurjection_maximalIdeal q hq hfg]
    exact formallySmoothNAdic_adicCompletion (A := Λ) (B := P) _ hfg
  refine ⟨shrinkCompleteLocalAlgebra.{t} Rbig, ?_⟩
  let : IsLocalRing (shrinkCompleteLocalAlgebra.{t} Rbig) :=
    (shrinkCompleteLocalAlgebra.{t} Rbig).completeLocal.isLocal
  exact RingHom.FormallySmoothNAdic.of_algEquiv
    (shrinkCompleteLocalAlgebraEquiv.{t} Rbig).symm hsmooth

end SmoothModel

/-! ### Artinian and complete quotients of an object of the completed base category -/

section Quotients

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue field of a local ring is that of its quotient by a proper ideal. -/
private noncomputable def residueFieldQuotientEquiv (S : Type*) [CommRing S] [Algebra Λ S]
    [IsLocalRing S] (I : Ideal S) [IsLocalRing (S ⧸ I)] :
    ResidueField S ≃ₐ[Λ] ResidueField (S ⧸ I) :=
  let q := Ideal.Quotient.mkₐ Λ I
  letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  AlgEquiv.ofBijective (ResidueField.mapAlgHom q) <| by
    refine ⟨RingHom.injective _, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue S r, by simp [q]⟩

/-- A proper ideal of an object of the completed base category containing a power of the
maximal ideal cuts out an object of `𝒞_Λ`. -/
private noncomputable def artinianQuotientObject
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (I : Ideal S)
    (hI : I < ⊤) (hpow : ∃ n, maximalIdeal S ^ n ≤ I) :
    ArtinianLocalAlgCat.{u, v, w} Λ k := by
  letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  letI : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsArtinianRing (S ⧸ I) := by
    obtain ⟨n, hn⟩ := hpow
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      have hone : (1 : S) ∈ I := hn (by simp)
      have htop : (⊤ : Ideal S) ≤ I := fun x _ ↦ by simpa using I.mul_mem_left x hone
      exact (ne_of_lt hI) (top_unique htop)
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    refine ⟨⟨inferInstance, le_maximalIdeal hI.ne⟩, fun q hq _ ↦ ?_⟩
    have := hq.1
    exact Ideal.IsPrime.le_of_pow_le (hn.trans hq.2)
  exact
    { carrier := S ⧸ I
      residueEquiv := (residueFieldQuotientEquiv S I).symm.trans S.residueEquiv }

/-- The residue-field identification of an Artinian quotient is compatible with residues of
representatives. -/
private theorem artinianQuotientObject_residueEquiv_mk
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (I : Ideal S)
    (hI : I < ⊤) (hpow : ∃ n, maximalIdeal S ^ n ≤ I) (r : S) :
    letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
    letI : IsLocalRing (S ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (artinianQuotientObject S I hI hpow).residueEquiv
      (residue (S ⧸ I) (Ideal.Quotient.mk I r)) = S.residueEquiv (residue S r) := by
  let _ : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  let _ : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact congrArg S.residueEquiv
    ((residueFieldQuotientEquiv (Λ := Λ) S I).symm_apply_apply (residue S r))

/-- A proper ideal of an object of the completed base category cuts out another object of the
completed base category. -/
private noncomputable def completeQuotientObject
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (I : Ideal S) (hI : I < ⊤) :
    CompleteLocalAlgCat.{u, v, w} Λ k := by
  letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  letI : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact
    { carrier := S ⧸ I
      completeLocal := quotient_isNoetherianCompleteLocalRing S.completeLocal I hI.ne
      residueEquiv := (residueFieldQuotientEquiv S I).symm.trans S.residueEquiv }

/-- The residue-field identification of a complete quotient is compatible with residues of
representatives. -/
private theorem completeQuotientObject_residueEquiv_mk
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (I : Ideal S) (hI : I < ⊤) (r : S) :
    letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
    letI : IsLocalRing (S ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (completeQuotientObject S I hI).residueEquiv
      (residue (S ⧸ I) (Ideal.Quotient.mk I r)) = S.residueEquiv (residue S r) := by
  let _ : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  let _ : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact congrArg S.residueEquiv
    ((residueFieldQuotientEquiv (Λ := Λ) S I).symm_apply_apply (residue S r))

/-- A decreasing sequence of ideals containing the shifted powers of the maximal ideal induces
an adic filtration on the quotient by its intersection. -/
private theorem quotientFiltration_isAdic_of_pow_shift_le
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (J : ℕ → Ideal S) (hJ : Antitone J) (c : ℕ)
    (hpow : ∀ n, maximalIdeal S ^ (n + c) ≤ J n) :
    Ideal.IsAdicFiltration
      (Ideal.map (Ideal.Quotient.mk (⨅ n, J n)) (maximalIdeal S))
      (fun n ↦ Ideal.map (Ideal.Quotient.mk (⨅ n, J n)) (J n)) := by
  let K : ℕ → Ideal S := fun n ↦ if n < c then ⊤ else J (n - c)
  have hK : Antitone K := by
    intro i j hij
    by_cases hj : j < c
    · simp [K, hj, lt_of_le_of_lt hij hj]
    by_cases hi : i < c
    · simp [K, hi]
    simpa [K, hi, hj] using hJ (Nat.sub_le_sub_right hij c)
  have hKpow : ∀ n, maximalIdeal S ^ n ≤ K n := by
    intro n
    by_cases hn : n < c
    · simp [K, hn]
    simpa [K, hn, Nat.sub_add_cancel (Nat.le_of_not_gt hn)] using hpow (n - c)
  have hKadd (n : ℕ) : K (n + c) = J n := by simp [K]
  have hInf : (⨅ n, K n) = ⨅ n, J n := by
    apply le_antisymm
    · exact le_iInf fun n ↦ (iInf_le K (n + c)).trans_eq (hKadd n)
    · apply le_iInf
      intro n
      by_cases hn : n < c
      · simp [K, hn]
      simpa [K, hn] using iInf_le J (n - c)
  have h := quotient_filtration_isAdic S K hK hKpow
  rw [hInf] at h
  refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
  · obtain ⟨m, hm⟩ := h.1 n
    by_cases hm' : m < c
    · exact ⟨0, (Ideal.map_mono (show J 0 ≤ K m by simp [K, hm'])).trans hm⟩
    · exact ⟨m - c, by simpa [K, hm'] using hm⟩
  · simpa only [hKadd] using h.2 (n + c)

/-- One more power of an ideal lands inside the product with anything that the previous power
is contained in. -/
private theorem ideal_pow_succ_le_mul {R : Type*} [CommRing R] (I J : Ideal R)
    (n : ℕ) (h : I ^ n ≤ J) : I ^ (n + 1) ≤ I * J :=
  calc
    I ^ (n + 1) = I ^ n * I := by rw [pow_succ]
    _ ≤ J * I := Ideal.mul_mono_left h
    _ = I * J := mul_comm _ _

/-- The transport morphism along an equality of objects of `𝒞_Λ` is bijective. -/
private theorem artinianLocalAlgCat_eqToHom_bijective
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : A = B) :
    Function.Bijective (eqToHom h).hom := by
  cases h
  exact Function.bijective_id

/-- Transporting back and forth along equalities of objects of `𝒞_Λ` is the identity. -/
private theorem artinianLocalAlgCat_eqToHom_hom_apply
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : A = B) (h' : B = A) (z : B) :
    (eqToHom h).hom ((eqToHom h').hom z) = z := by
  cases h
  rfl

/-- The transport morphism along an equality of objects of the completed base category is
bijective. -/
private theorem completeLocalAlgCat_eqToHom_bijective
    {A B : CompleteLocalAlgCat.{u, v, w} Λ k} (h : A = B) :
    Function.Bijective (eqToHom h).hom := by
  cases h
  exact Function.bijective_id

/-- Transporting back and forth along equalities of objects of the completed base category is
the identity. -/
private theorem completeLocalAlgCat_eqToHom_hom_apply
    {A B : CompleteLocalAlgCat.{u, v, w} Λ k} (h : A = B) (h' : B = A) (z : B) :
    (eqToHom h).hom ((eqToHom h').hom z) = z := by
  cases h
  rfl

/-- Elements of the maximal ideal of an Artinian local ring are nilpotent. -/
private theorem isNilpotent_of_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    {x : A} (hx : x ∈ maximalIdeal A) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow hx n
  rw [hn] at h
  exact h

/-- An ideal of length one over a local ring is killed by the maximal ideal. -/
private theorem maximalIdeal_mul_eq_bot_of_length_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : Module.length A I = 1) : maximalIdeal A * I = ⊥ := by
  let _ : IsSimpleModule A I := Module.length_eq_one_iff.mp hI
  have hAnn : Module.annihilator A I = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := A) (M := I))
  refine le_antisymm (Ideal.mul_le.mpr fun a ha b hb ↦ ?_) bot_le
  have h : a ∈ Module.annihilator A I := hAnn.symm ▸ ha
  exact congrArg Subtype.val ((Module.mem_annihilator.mp h) (⟨b, hb⟩ : I))

/-- A local map to a local ring whose maximal ideal has a vanishing power kills the same power
of the maximal ideal of the source. -/
private theorem maximalIdeal_pow_le_ker {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing R]
    [IsLocalRing A] (g : R →+* A) [IsLocalHom g] {n : ℕ} (hn : maximalIdeal A ^ n = ⊥) :
    maximalIdeal R ^ n ≤ RingHom.ker g := by
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  exact le_bot_iff.mp ((Ideal.pow_right_mono (map_maximalIdeal_le g) n).trans hn.le)

/-- If a composite with a surjective ring map is local, then so is its second factor. -/
private theorem isLocalHom_of_comp_surjective {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] {q : R →+* A} (hq : Function.Surjective q) {δ : A →+* B}
    (h : IsLocalHom (δ.comp q)) : IsLocalHom δ :=
  ⟨fun r hr ↦ by
    obtain ⟨s, rfl⟩ := hq r
    exact (isUnit_of_map_unit (δ.comp q) s hr).map q⟩

/-- The kernel of an algebra map is contained in the kernel of any composite with it. -/
private theorem ker_le_ker_of_comp_eq {Λ R A B : Type*} [CommSemiring Λ] [CommRing R] [CommRing A]
    [CommRing B] [Algebra Λ R] [Algebra Λ A] [Algebra Λ B] (f : R →ₐ[Λ] A) (g : A →ₐ[Λ] B)
    {h : R →ₐ[Λ] B} (hgf : g.comp f = h) :
    RingHom.ker f.toRingHom ≤ RingHom.ker h.toRingHom := by
  subst hgf
  intro x hx
  change g (f x) = 0
  rw [show f x = 0 from hx, map_zero]

end Quotients

/-! ### Descent and pushforward in a category cofibered in groupoids -/

section Cofibered

/-- In a category cofibered in groupoids a morphism descends along a morphism out of a common
source once the base triangle commutes. -/
private theorem exists_desc_of_cofibered
    {C : Type*} [Category C] {F : Type*} [Category F] (p : F ⥤ C)
    (hp : IsCofiberedInGroupoids p)
    {x y z : F} (a : x ⟶ y) (b : x ⟶ z)
    (f : p.obj y ⟶ p.obj z) (h : p.map a ≫ f = p.map b) :
    ∃ c : y ⟶ z, p.map c = f ∧ a ≫ c = b := by
  obtain ⟨c, hc, _⟩ := hp.unique_lift a.op b.op f.op (congrArg Quiver.Hom.op h)
  exact ⟨c.unop, congrArg Quiver.Hom.unop hc.1, congrArg Quiver.Hom.unop hc.2⟩

/-- The pushforward of an object along a morphism of the base, with its base equality and the
formula for the image of the structural arrow. -/
private theorem exists_pushforward_eq
    {C : Type*} [Category C] {F : Type*} [Category F] (p : F ⥤ C)
    (hp : IsCofiberedInGroupoids p)
    (x : F) {B : C} (f : p.obj x ⟶ B) :
    ∃ (y : F) (hy : p.obj y = B) (a : x ⟶ y),
      p.map a = f ≫ eqToHom hy.symm := by
  obtain ⟨y, a, ha⟩ := exists_pushforward hp f x rfl
  have hy : p.obj y = B := IsHomLift.codomain_eq p f a
  refine ⟨y, hy, a, ?_⟩
  simpa using IsHomLift.fac' p f a

end Cofibered

/-! ### Presentations of objects by a fixed complete local algebra -/

section Presented

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Formal smoothness of `Λ → R` for the `m_R`-adic topology lets a local map from `R` to the
target of a small extension be lifted to its source. -/
private theorem exists_formallySmooth_lift_smallExtension
    {R : Type v} [CommRing R] [Algebra Λ R] [IsLocalRing R]
    (hR : RingHom.FormallySmoothNAdic.{v} (algebraMap Λ R) (maximalIdeal R))
    {B A : Type v} [CommRing B] [Algebra Λ B] [CommRing A] [Algebra Λ A]
    [IsLocalRing B] [IsLocalRing A]
    (f : B →ₐ[Λ] A)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.toRingHom))
    (g : R →ₐ[Λ] A) [IsLocalHom g.toRingHom] :
    ∃ g' : R →ₐ[Λ] B, f.comp g' = g ∧ IsLocalHom g'.toRingHom := by
  classical
  let hsq :=
    (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection
      (CommRingCat.ofHom f.toRingHom) hf).2.2.2
  rcases hf with ⟨hB, hA, hArtB, hArtA, hsurj, hlen⟩
  let q : B →+* B ⧸ RingHom.ker f.toRingHom :=
    Ideal.Quotient.mk (RingHom.ker f.toRingHom)
  let e : (B ⧸ RingHom.ker f.toRingHom) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hsurj
  let ψ : R →+* B ⧸ RingHom.ker f.toRingHom := e.symm.toRingHom.comp g.toRingHom
  have hquot : e.symm.toRingHom.comp f.toRingHom = q :=
    RingHom.quotientKerEquivOfSurjective_symm_comp hsurj
  have hcomm : ψ.comp (algebraMap Λ R) = q.comp (algebraMap Λ B) := by
    calc
      ψ.comp (algebraMap Λ R) = e.symm.toRingHom.comp (algebraMap Λ A) := by
        change e.symm.toRingHom.comp (g.toRingHom.comp (algebraMap Λ R)) = _
        ext a
        exact congrArg e.symm (g.commutes' a)
      _ = e.symm.toRingHom.comp (f.toRingHom.comp (algebraMap Λ B)) := by
        ext a
        exact (congrArg e.symm (f.commutes' a)).symm
      _ = q.comp (algebraMap Λ B) := by rw [← RingHom.comp_assoc, hquot]
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 hArtA
  have hA_pow : maximalIdeal A ^ (n + 1) = ⊥ := by simp [pow_succ, hn]
  have hker_ψ : maximalIdeal R ^ (n + 1) ≤ RingHom.ker ψ := by
    intro x hx
    have hxg := RingHom.mem_ker.mp (maximalIdeal_pow_le_ker g.toRingHom hA_pow hx)
    change e.symm (g.toRingHom x) = 0
    rw [hxg, map_zero]
  obtain ⟨g', hq, hΛ⟩ := hR B (RingHom.ker f.toRingHom) hsq
    (algebraMap Λ B) ψ hcomm ⟨n + 1, by omega, hker_ψ⟩
  have hfactor : f.toRingHom.comp g' = g.toRingHom := by
    ext x
    have hx := congrArg e (RingHom.congr_fun hq x)
    change e (Ideal.Quotient.mk (RingHom.ker f.toRingHom) (g' x)) =
      e (e.symm (g.toRingHom x)) at hx
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk, e.apply_symm_apply] at hx
    exact hx
  let g'Alg : R →ₐ[Λ] B :=
    { toRingHom := g'
      commutes' := fun a ↦ RingHom.congr_fun hΛ a }
  refine ⟨g'Alg, ?_, ?_⟩
  · ext x
    exact RingHom.congr_fun hfactor x
  · have : IsLocalHom (f.toRingHom.comp g') := hfactor ▸ inferInstance
    exact isLocalHom_of_comp g' f.toRingHom

/-- An object of the category together with a surjective presentation of its base by a fixed
object of the completed base category. -/
public structure PresentedObject
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) where
  /-- The underlying object. -/
  obj : F
  /-- The presentation of its base. -/
  hom : S →ₐ[Λ] p.obj obj
  /-- The presentation is surjective. -/
  surjective : Function.Surjective hom
  /-- The presentation respects the chosen identifications of the residue fields. -/
  residue_comm : ∀ s, (p.obj obj).residueEquiv (residue _ (hom s)) =
    S.residueEquiv (residue S s)

/-- A surjection from an object of the completed base category whose kernel contains a proper
ideal with a power of the maximal ideal factors through the Artinian quotient. -/
private noncomputable def artinianQuotientLift
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (I : Ideal S) (hI : I < ⊤) (hpow : ∃ n, maximalIdeal S ^ n ≤ I)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : S →ₐ[Λ] A) (hf : Function.Surjective f)
    (hres : ∀ s, A.residueEquiv (residue A (f s)) = S.residueEquiv (residue S s))
    (hIf : I ≤ RingHom.ker f.toRingHom) :
    artinianQuotientObject S I hI hpow ⟶ A := by
  letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  letI : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let g := Ideal.Quotient.liftₐ I f (fun a ha ↦ hIf ha)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨s, rfl⟩ := hf a
    exact ⟨Ideal.Quotient.mk I s, rfl⟩
  refine ⟨g, IsLocalHom.of_surjective g.toRingHom hg, ?_⟩
  intro a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (hres s).trans (artinianQuotientObject_residueEquiv_mk S I hI hpow s).symm

/-- A map out of a complete local algebra whose composite with an essential surjection is
surjective is itself surjective. -/
private theorem surjective_of_essentialSurjection
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : B ⟶ A) (hf : IsEssentialSurjection f)
    (g : S →ₐ[Λ] B) [IsLocalHom g.toRingHom]
    (hres : ∀ s, B.residueEquiv (residue B (g s)) = S.residueEquiv (residue S s))
    (hfg : Function.Surjective (f.hom.comp g)) : Function.Surjective g := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 inferInstance
  have hker : maximalIdeal S ^ (n + 1) ≤ RingHom.ker g.toRingHom :=
    maximalIdeal_pow_le_ker g.toRingHom (by simp [pow_succ, hn])
  let I := maximalIdeal S ^ (n + 1)
  have hI : I < ⊤ := (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt
    (maximalIdeal.isMaximal S).lt_top
  let C := artinianQuotientObject S I hI ⟨n + 1, le_rfl⟩
  let _ : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  let _ : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : C ⟶ B :=
    { hom := Ideal.Quotient.liftₐ I g (fun _ hx ↦ hker hx)
      isLocal := ⟨fun x hx ↦ by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (Ideal.Quotient.mk I).isUnit_map
          (IsLocalHom.map_nonunit (f := g.toRingHom) s hx)⟩
      residue_comm := fun x ↦ by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (hres s).trans
          (artinianQuotientObject_residueEquiv_mk S I hI ⟨n + 1, le_rfl⟩ s).symm }
  have hφ : Function.Surjective (φ ≫ f).hom := by
    intro a
    obtain ⟨s, hs⟩ := hfg a
    exact ⟨Ideal.Quotient.mk I s, hs⟩
  intro b
  obtain ⟨c, hc⟩ := hf.2 φ hφ b
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨s, hc⟩

/-- The kernel of a presentation contains a power of the maximal ideal, since the target is
Artinian. -/
private theorem presentedObject_pow_le_ker
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : PresentedObject S p) :
    ∃ n, maximalIdeal S ^ n ≤ RingHom.ker X.hom.toRingHom := by
  have : IsLocalHom X.hom.toRingHom :=
    IsLocalHom.of_surjective X.hom.toRingHom X.surjective
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (p.obj X.obj)).1 inferInstance
  exact ⟨n, maximalIdeal_pow_le_ker X.hom.toRingHom hn⟩

/-- **The induction step of Schlessinger's construction.** Under (S1) there is a presentation
whose kernel is least among those containing `m_S` times the kernel of a given presentation
and admitting a morphism to it. -/
private theorem exists_least_presented_lift
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p) (X : PresentedObject S p) :
    ∃ (Y : PresentedObject S p) (a : Y.obj ⟶ X.obj),
      (p.map a).hom.comp Y.hom = X.hom ∧
      maximalIdeal S * RingHom.ker X.hom.toRingHom ≤ RingHom.ker Y.hom.toRingHom ∧
      ∀ (Z : PresentedObject S p) (b : Z.obj ⟶ X.obj),
        (p.map b).hom.comp Z.hom = X.hom →
        maximalIdeal S * RingHom.ker X.hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom →
        RingHom.ker Y.hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom := by
  classical
  let J := RingHom.ker X.hom.toRingHom
  let I := maximalIdeal S * J
  have hIJ : I ≤ J := Ideal.mul_le_right
  have hJ : J < ⊤ := lt_top_iff_ne_top.mpr (RingHom.ker_ne_top X.hom.toRingHom)
  have hI : I < ⊤ := hIJ.trans_lt hJ
  obtain ⟨n, hn⟩ := presentedObject_pow_le_ker X
  have hpow : ∃ m, maximalIdeal S ^ m ≤ I := ⟨n + 1, ideal_pow_succ_le_mul _ _ n hn⟩
  let B := artinianQuotientObject S I hI hpow
  let q : S →ₐ[Λ] B := Ideal.Quotient.mkₐ Λ I
  let f : B ⟶ p.obj X.obj :=
    artinianQuotientLift S I hI hpow X.hom X.surjective X.residue_comm hIJ
  have hf : Function.Surjective f.hom := by
    intro x
    obtain ⟨s, rfl⟩ := X.surjective x
    exact ⟨q s, rfl⟩
  have hkerf : RingHom.ker f.hom.toRingHom = Ideal.map q.toRingHom J :=
    Ideal.ker_quotient_lift X.hom.toRingHom (fun a ha ↦ hIJ ha)
  have hsmall : maximalIdeal B * RingHom.ker f.hom.toRingHom = ⊥ := by
    rw [hkerf, ← map_maximalIdeal_of_surjective q.toRingHom Ideal.Quotient.mk_surjective,
      ← Ideal.map_mul]
    refine (Ideal.map_eq_bot_iff_le_ker q.toRingHom (I := I)).2 ?_
    change I ≤ RingHom.ker (Ideal.Quotient.mk I)
    rw [Ideal.mk_ker]
  obtain ⟨L, ⟨hL, C, r, g, hr, hkr, hrg, y, hy, a, ha⟩, hleast⟩ :=
    exists_least_lifting_ideal p hp hS1 X.obj f hf hsmall
  subst C
  let Y : PresentedObject S p :=
    { obj := y
      hom := r.hom.comp q
      surjective := hr.comp Ideal.Quotient.mk_surjective
      residue_comm := fun s ↦ (r.residue_comm (q s)).trans
        (artinianQuotientObject_residueEquiv_mk S I hI hpow s) }
  have hY : (p.map a).hom.comp Y.hom = X.hom := by
    simp only [eqToHom_refl, Category.id_comp] at ha
    rw [ha]
    change g.hom.comp (r.hom.comp q) = X.hom
    rw [← AlgHom.comp_assoc, ← ArtinianLocalAlgCat.comp_hom, hrg]
    rfl
  refine ⟨Y, a, hY, ?_, ?_⟩
  · intro s hs
    change r.hom (q s) = 0
    rw [show q s = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hs, map_zero]
  · intro Z b hb hIZ
    let t : B ⟶ p.obj Z.obj :=
      artinianQuotientLift S I hI hpow Z.hom Z.surjective Z.residue_comm hIZ
    have ht : Function.Surjective t.hom := by
      intro z
      obtain ⟨s, rfl⟩ := Z.surjective z
      exact ⟨q s, rfl⟩
    have htb : t ≫ p.map b = f := by
      apply ArtinianLocalAlgCat.hom_ext
      ext z
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact DFunLike.congr_fun hb s
    have htker : RingHom.ker t.hom.toRingHom ≤ RingHom.ker f.hom.toRingHom := by
      rw [← htb]
      intro z hz
      change (p.map b).hom (t.hom z) = 0
      rw [show t.hom z = 0 from hz, map_zero]
    have hmin := hleast (RingHom.ker t.hom.toRingHom)
      ⟨htker, p.obj Z.obj, t, p.map b, ht, rfl, htb, Z.obj, rfl, b, by simp⟩
    intro s hs
    have hrs : q s ∈ L := by rw [← hkr]; exact hs
    exact hmin hrs

/-- The fibre product of a small extension with a morphism of the base, completed to a square
in the category, together with the dichotomy for its first projection. -/
private theorem exists_pullback_completion_of_smallExtension
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hS1 : SchlessingerConditionS1 p)
    {x₁ x₂ x : F} (b : x₁ ⟶ x) (g : x₂ ⟶ x)
    (hg : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (p.map g).hom.toRingHom)) :
    ∃ (P : ArtinianLocalAlgCat.{u, v, w} Λ k)
      (q₁ : P ⟶ p.obj x₁) (q₂ : P ⟶ p.obj x₂),
      IsPullback q₁ q₂ (p.map b) (p.map g) ∧
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom q₁.hom.toRingHom) ∧
      Nonempty (PullbackCompletion p b g q₁ q₂) ∧
      ((∃ s : p.obj x₁ ⟶ P, s ≫ q₁ = 𝟙 _) ∨ IsEssentialSurjection q₁) := by
  have hsurj : Function.Surjective (p.map g).hom := hg.2.2.2.2.1
  have := (ArtinianLocalAlgCat.hasPullback_of_surjective (p.map b) (p.map g) (Or.inr hsurj)).2
  let q₁ := Limits.pullback.fst (p.map b) (p.map g)
  let q₂ := Limits.pullback.snd (p.map b) (p.map g)
  have hpb : IsPullback q₁ q₂ (p.map b) (p.map g) := IsPullback.of_hasPullback _ _
  have hq₁ := ArtinianLocalAlgCat.isSmallExtension_pullback_fst (p.map b) (p.map g) hg
  refine ⟨_, q₁, q₂, hpb, hq₁, hS1.completion b g hsurj q₁ q₂ hpb.flip, ?_⟩
  by_cases he : IsEssentialSurjection q₁
  · exact Or.inr he
  · exact Or.inl ((not_isEssentialSurjection_iff_exists_section q₁ hq₁).mp he)

/-- Iterating the induction step produces the tower of presentations of Schlessinger's
construction. -/
public theorem exists_presented_tower
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p) (X₀ : PresentedObject S p) :
    ∃ (X : ℕ → PresentedObject S p) (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj),
      X 0 = X₀ ∧
      (∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom) ∧
      (∀ n, maximalIdeal S * RingHom.ker (X n).hom.toRingHom ≤
        RingHom.ker (X (n + 1)).hom.toRingHom) ∧
      ∀ n (Z : PresentedObject S p) (b : Z.obj ⟶ (X n).obj),
        (p.map b).hom.comp Z.hom = (X n).hom →
        maximalIdeal S * RingHom.ker (X n).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom →
        RingHom.ker (X (n + 1)).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom := by
  classical
  choose next arrow hcomm hmul hleast using exists_least_presented_lift hp hS1
  let X : ℕ → PresentedObject S p := fun n ↦ Nat.rec X₀ (fun _ ↦ next) n
  exact ⟨X, fun n ↦ arrow (X n), rfl, fun n ↦ hcomm (X n),
    fun n ↦ hmul (X n), fun n ↦ hleast (X n)⟩

/-- The kernels of a compatible tower of presentations decrease. -/
private theorem presentedTower_ker_antitone
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ℕ → PresentedObject S p) (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (hcomm : ∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom) :
    Antitone (fun n ↦ RingHom.ker (X n).hom.toRingHom) := by
  exact antitone_nat_of_succ_le fun n ↦ ker_le_ker_of_comp_eq _ _ (hcomm n)

/-- A tower of presentations admits a comparison morphism from any later stage to any earlier
one. -/
private theorem exists_presentedTower_arrow
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ℕ → PresentedObject S p) (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (hcomm : ∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom)
    {n m : ℕ} (h : n ≤ m) :
    ∃ b : (X m).obj ⟶ (X n).obj, (p.map b).hom.comp (X m).hom = (X n).hom := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨𝟙 _, by simp⟩
  | succ m hm ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨a m ≫ b, ?_⟩
    rw [p.map_comp, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_assoc, hcomm, hb]

end Presented

/-! ### A single object generating the tangent space -/

section Tangent

/-- In a tensor product with a finite-dimensional first factor there is a universal element:
every element of the tensor product with a one-dimensional space is the image of it under a
linear map in the second variable. -/
private theorem exists_tensor_universal_element
    {k : Type w} [Field k] {T : Type*} [AddCommGroup T] [Module k T]
    {U : Type*} [AddCommGroup U] [Module k U] (eU : U ≃ₗ[k] k)
    {W : Type*} [AddCommGroup W] [Module k W]
    {ι : Type*} [Finite ι] (b : Module.Basis ι k T) (bW : Module.Basis ι k W) :
    ∃ z : TensorProduct k T W,
      ∀ s : TensorProduct k T U, ∃ f : W →ₗ[k] U,
        TensorProduct.map (LinearMap.id : T →ₗ[k] T) f z = s := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let E : TensorProduct k T U ≃ₗ[k] T :=
    (TensorProduct.congr (LinearEquiv.refl k T) eU).trans (TensorProduct.rid k T)
  have hE (x : T) (y : U) : E (x ⊗ₜ[k] y) = eU y • x := by simp [E]
  refine ⟨∑ i, b i ⊗ₜ[k] bW i, fun s ↦ ?_⟩
  refine ⟨eU.symm.toLinearMap ∘ₗ ∑ i, b.repr (E s) i • bW.coord i, E.injective ?_⟩
  have hf (j : ι) : (eU.symm.toLinearMap ∘ₗ ∑ i, b.repr (E s) i • bW.coord i) (bW j) =
      eU.symm (b.repr (E s) j) := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, apply_ite]
  calc E (TensorProduct.map (LinearMap.id : T →ₗ[k] T)
        (eU.symm.toLinearMap ∘ₗ ∑ i, b.repr (E s) i • bW.coord i) (∑ i, b i ⊗ₜ[k] bW i))
      = ∑ i, b.repr (E s) i • b i := by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [TensorProduct.map_tmul, hE, LinearMap.id_apply, hf i, eU.apply_symm_apply]
    _ = E s := b.sum_repr _

/-- A functor on finite-dimensional vector spaces which is naturally a tensor product with a
fixed finite-dimensional space has a universal element at a space of the same dimension. -/
private theorem exists_universal_element_of_tensor_equivalences
    {k : Type w} [Field k] {T : Type*} [AddCommGroup T] [Module k T]
    {U W : Type v} [AddCommGroup U] [Module k U] [Module.Finite k U]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    {ι : Type*} [Finite ι]
    (eU : U ≃ₗ[k] k) (b : Module.Basis ι k T) (bW : Module.Basis ι k W)
    (G : FGModuleCat.{v} k ⥤ ModuleCat.{uF} k)
    (e : ∀ V : FGModuleCat.{v} k, TensorProduct k T V ≃ₗ[k] G.obj V)
    (he : ∀ (V V' : FGModuleCat.{v} k) (f : V ⟶ V') (z : TensorProduct k T V),
      (G.map f).hom (e V z) = e V' (TensorProduct.map LinearMap.id f.hom.hom z)) :
    ∃ z : G.obj (FGModuleCat.of k W),
      ∀ s : G.obj (FGModuleCat.of k U),
        ∃ f : FGModuleCat.of k W ⟶ FGModuleCat.of k U, (G.map f).hom z = s := by
  classical
  obtain ⟨z, hz⟩ := exists_tensor_universal_element eU b bW
  refine ⟨e _ z, fun s ↦ ?_⟩
  obtain ⟨f, hf⟩ := hz ((e _).symm s)
  refine ⟨FGModuleCat.ofHom f, ?_⟩
  rw [he, show (FGModuleCat.ofHom f).hom.hom = f from rfl, hf]
  exact (e _).apply_symm_apply s

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Every isomorphism class over an object of `𝒞_Λ` is the class of an object lying over it. -/
private theorem exists_object_representing_class
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (z : (isomorphismClasses 𝓕 hpre.cofibered).obj A) :
    ∃ x : 𝓕.obj, ∃ hxbase : 𝓕.p.obj x = A,
      classOf 𝓕 hpre.cofibered (A := A) ⟨x, hxbase⟩ = z := by
  obtain ⟨x, hx⟩ := classOf_surjective 𝓕 hpre.cofibered A z
  rcases x with ⟨x, hxbase⟩
  exact ⟨x, hxbase, hx⟩

/-- **Step 2 of Schlessinger's construction.** With a finite-dimensional tangent space there
is a single object over a finite-dimensional square-zero extension whose isomorphism class
hits every tangent vector after pushforward to the dual numbers. -/
public theorem exists_tangent_generating_object
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)))
    [Fact (IsPredeformationCategory.{u, v, w} 𝓕.p)]
    [Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)))]
    [FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses 𝓕 hpre.cofibered))] :
    ∃ (d : ℕ) (x : 𝓕.obj), ∃ _hx : 𝓕.p.obj x =
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj
        (FGModuleCat.of k (ULift.{v} (Fin d → k))),
      ∀ t : tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 hpre.cofibered),
        ∃ f : 𝓕.p.obj x ⟶ artinianDualNumbers.{u, w, v} Λ k,
          (isomorphismClasses 𝓕 hpre.cofibered).map f
            (classOf 𝓕 hpre.cofibered ⟨x, rfl⟩) = t := by
  classical
  let H := squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙
    isomorphismClasses 𝓕 hpre.cofibered
  let L := associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 hpre hS2
  let T := tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 hpre.cofibered)
  let d := Module.finrank k T
  let bW : Module.Basis (Fin d) k (ULift.{v} (Fin d → k)) :=
    (Pi.basisFun k (Fin d)).map
      (ULift.moduleEquiv (R := k) (M := Fin d → k)).symm
  have h : ∃ z : (L.functor ⋙ forget (ModuleCat.{uF} k)).obj
      (FGModuleCat.of k (ULift.{v} (Fin d → k))),
      ∀ t : (L.functor ⋙ forget (ModuleCat.{uF} k)).obj (FGModuleCat.of k (ULift.{v} k)),
        ∃ f : FGModuleCat.of k (ULift.{v} (Fin d → k)) ⟶ FGModuleCat.of k (ULift.{v} k),
          (L.functor ⋙ forget (ModuleCat.{uF} k)).map f z = t :=
    exists_universal_element_of_tensor_equivalences
      (ULift.moduleEquiv (R := k) (M := k)) (Module.finBasis k T) bW L.functor
      (associatedTangentSpaceFunctor_iso_tensorLeft.{u, v, w} 𝓕 hpre hS2)
      (associatedTangentSpaceFunctor_iso_tensorLeft_naturality.{u, v, w} 𝓕 hpre hS2)
  have hLH : L.functor ⋙ forget (ModuleCat.{uF} k) = H := L.forget_comp
  rw [hLH] at h
  obtain ⟨z, hz⟩ := h
  obtain ⟨x, hx, hxz⟩ := exists_object_representing_class 𝓕 hpre _ z
  refine ⟨d, x, hx, fun t ↦ ?_⟩
  obtain ⟨f, hf⟩ := hz t
  refine ⟨eqToHom hx ≫ (squareZeroExtensionArtinian.{u, w, max v w} Λ k).map f, ?_⟩
  rw [Functor.map_comp]
  change (isomorphismClasses 𝓕 hpre.cofibered).map
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map f)
    ((isomorphismClasses 𝓕 hpre.cofibered).map (eqToHom hx)
      (classOf 𝓕 hpre.cofibered ⟨x, rfl⟩)) = t
  have heq : (isomorphismClasses 𝓕 hpre.cofibered).map (eqToHom hx)
      (classOf 𝓕 hpre.cofibered ⟨x, rfl⟩) = classOf 𝓕 hpre.cofibered ⟨x, hx⟩ := by
    have : 𝓕.p.IsHomLift (eqToHom hx) (𝟙 x) := IsHomLift.of_fac 𝓕.p _ _ rfl hx (by simp)
    exact map_classOf 𝓕 hpre.cofibered (eqToHom hx) ⟨x, rfl⟩ ⟨x, hx⟩ (𝟙 x)
  rw [heq, hxz]
  exact hf

end Tangent

/-! ### Power series presentations -/

section PowerSeries

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

attribute [local instance_reducible] mvPowerSeriesObject

/-- The right action of a field on one of its vector spaces. -/
local instance squareZeroModuleMulOpposite (K : Type w) [Field K] (V : FGModuleCat.{m} K) :
    Module Kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring K V

/-- The left and right actions of a field on one of its vector spaces agree. -/
local instance squareZeroIsCentralScalar (K : Type w) [Field K] (V : FGModuleCat.{m} K) :
    IsCentralScalar K V :=
  Module.isCentralScalar_oppositeOfCommSemiring K V

/-- A vector space over `k` as a `Λ`-module through the structure map of `k`. -/
local instance squareZeroModuleOfAlgebra (A : Type u) (K : Type w) [CommRing A] [Field K]
    [Algebra A K] (V : FGModuleCat.{m} K) : Module A V :=
  Module.compHom V (algebraMap A K)

/-- The scalar tower from `Λ` through `k` to one of its vector spaces. -/
local instance squareZeroIsScalarTower (A : Type u) (K : Type w) [CommRing A] [Field K]
    [Algebra A K] (V : FGModuleCat.{m} K) : IsScalarTower A K V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The scalar tower from `Λ` through the opposite of `k` to one of its vector spaces. -/
local instance squareZeroIsScalarTowerMulOpposite (A : Type u) (K : Type w) [CommRing A]
    [Field K] [Algebra A K] (V : FGModuleCat.{m} K) : IsScalarTower A Kᵐᵒᵖ V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Substituting nilpotent elements for the variables defines a ring map out of a power series
ring in finitely many variables. -/
@[ega "0 19.3.4.1" "(ii)"]
private theorem exists_mvPowerSeries_eval
    {σ R A : Type*} [Finite σ] [CommRing R] [CommRing A]
    (f : R →+* A) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) :
    ∃ g : MvPowerSeries σ R →+* A,
      (∀ r, g (MvPowerSeries.C r) = f r) ∧ (∀ i, g (MvPowerSeries.X i) = x i) := by
  let _ : UniformSpace R := ⊥
  let _ : UniformSpace A := ⊥
  let he : MvPowerSeries.HasEval x := ⟨fun i ↦ (hx i).isTopologicallyNilpotent,
    by simp [Filter.cofinite_eq_bot]⟩
  refine ⟨MvPowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous f) he, ?_, ?_⟩
  · simpa only [MvPowerSeries.coe_eval₂Hom] using MvPowerSeries.eval₂_C f x
  · simpa only [MvPowerSeries.coe_eval₂Hom] using MvPowerSeries.eval₂_X f x

/-- A local map out of a power series algebra over a formally smooth base lifts along a small
extension: lift the coefficients by formal smoothness and the variables by surjectivity. -/
private theorem exists_mvPowerSeries_lift_of_formallySmooth
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (d : ℕ)
    (hR : RingHom.FormallySmoothNAdic.{v} (algebraMap Λ R) (maximalIdeal R))
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom))
    (g : mvPowerSeriesObject R d →ₐ[Λ] A) [IsLocalHom g.toRingHom]
    (hres : ∀ s, A.residueEquiv (residue A (g s)) =
      (mvPowerSeriesObject R d).residueEquiv (residue (mvPowerSeriesObject R d) s)) :
    ∃ h : mvPowerSeriesObject R d →ₐ[Λ] B, f.hom.comp h = g ∧
      ∀ s, B.residueEquiv (residue B (h s)) =
        (mvPowerSeriesObject R d).residueEquiv (residue (mvPowerSeriesObject R d) s) := by
  classical
  let _ : IsLocalRing R := R.completeLocal.isLocal
  let C : R →ₐ[Λ] mvPowerSeriesObject R d :=
    { toRingHom := (MvPowerSeries.C : R →+* MvPowerSeries (Fin d) R)
      commutes' := fun a ↦ by
        change (MvPowerSeries.C (algebraMap Λ R a) : MvPowerSeries (Fin d) R) =
          algebraMap Λ (MvPowerSeries (Fin d) R) a
        rw [MvPowerSeries.algebraMap_apply] }
  have hC_local : IsLocalHom C.toRingHom := by
    change IsLocalHom (MvPowerSeries.C : R →+* MvPowerSeries (Fin d) R)
    apply isLocalHom_of_leftInverse MvPowerSeries.constantCoeff
    intro r
    exact MvPowerSeries.constantCoeff_C r
  let _ : IsLocalHom (g.comp C).toRingHom := by
    change IsLocalHom (g.toRingHom.comp C.toRingHom)
    infer_instance
  obtain ⟨c, hc, _⟩ :=
    exists_formallySmooth_lift_smallExtension hR f.hom hf (g.comp C)
  choose x hx using fun i : Fin d ↦ hf.2.2.2.2.1 (g (MvPowerSeries.X i))
  have hgX (i : Fin d) : g (MvPowerSeries.X i) ∈ maximalIdeal A := by
    apply map_maximalIdeal_le g.toRingHom
    apply Ideal.mem_map_of_mem
    change ¬ IsUnit (MvPowerSeries.X i : MvPowerSeries (Fin d) R)
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hxnil (i : Fin d) : IsNilpotent (x i) := by
    apply isNilpotent_of_mem_maximalIdeal
    change ¬ IsUnit (x i)
    intro hunit
    exact (hgX i) (hx i ▸ hunit.map f.hom)
  obtain ⟨h, hCh, hXh⟩ := exists_mvPowerSeries_eval c.toRingHom x hxnil
  let hA : mvPowerSeriesObject R d →ₐ[Λ] B :=
    { toRingHom := h
      commutes' := fun a ↦ by
        change h (algebraMap Λ (MvPowerSeries (Fin d) R) a) = _
        rw [MvPowerSeries.algebraMap_apply, hCh]
        change c (algebraMap Λ R a) = algebraMap Λ B a
        exact c.commutes a }
  have hgC (r : R) : g (MvPowerSeries.C r) = f.hom (c r) :=
    (DFunLike.congr_fun hc r).symm
  have hfac : f.hom.comp hA = g := by
    apply AlgHom.coe_ringHom_injective
    apply MvPowerSeries.hom_ext_of_isNilpotent d
    · intro r
      change f.hom (h (MvPowerSeries.C r)) = g (MvPowerSeries.C r)
      rw [hCh, hgC]
      rfl
    · intro i
      change f.hom (h (MvPowerSeries.X i)) = g (MvPowerSeries.X i)
      rw [hXh]
      exact hx i
    · intro i
      change IsNilpotent (f.hom (h (MvPowerSeries.X i)))
      rw [hXh, show f.hom (x i) = g (MvPowerSeries.X i) from hx i]
      exact isNilpotent_of_mem_maximalIdeal (hgX i)
  refine ⟨hA, hfac, fun s ↦ ?_⟩
  rw [← f.residue_comm (hA s)]
  exact (congrArg (fun a ↦ A.residueEquiv (residue A a))
    (DFunLike.congr_fun hfac s)).trans (hres s)

/-- The power series algebra in `d` variables over `R` surjects onto the square-zero extension
of `k` by a `d`-dimensional vector space, by sending the variables to a basis. -/
private theorem exists_squareZero_mvPowerSeries_presentation
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (d : ℕ)
    (V : FGModuleCat.{m} k) (bV : Module.Basis (Fin d) k V) :
    ∃ q : mvPowerSeriesObject R d →ₐ[Λ] TrivSqZeroExt k V,
      Function.Surjective q ∧
      (∀ r, q (MvPowerSeries.C r) = TrivSqZeroExt.inl (R.residueEquiv (residue R r))) ∧
      (∀ i, q (MvPowerSeries.X i) = TrivSqZeroExt.inr (bV i)) := by
  classical
  let _ : IsLocalRing R := R.completeLocal.isLocal
  let f : R →+* TrivSqZeroExt k V :=
    (TrivSqZeroExt.inlHom k V).comp (R.residueEquiv.toRingHom.comp (residue R))
  obtain ⟨g, hgC, hgX⟩ := exists_mvPowerSeries_eval f (fun i ↦ TrivSqZeroExt.inr (bV i))
    (fun i ↦ ⟨2, by simp [pow_two]⟩)
  let q : mvPowerSeriesObject R d →ₐ[Λ] TrivSqZeroExt k V :=
    { toRingHom := g
      commutes' := fun a ↦ by
        change g (algebraMap Λ (MvPowerSeries (Fin d) R) a) = _
        rw [MvPowerSeries.algebraMap_apply, hgC]
        change TrivSqZeroExt.inl (R.residueEquiv (residue R (algebraMap Λ R a))) = _
        rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
          R.residueEquiv.commutes]
        rfl }
  refine ⟨q, ?_, hgC, hgX⟩
  intro a
  obtain ⟨r, hr⟩ := (R.residueEquiv.surjective.comp residue_surjective) a.fst
  choose c hc using fun i : Fin d ↦
    (R.residueEquiv.surjective.comp residue_surjective) (bV.repr a.snd i)
  refine ⟨MvPowerSeries.C r + ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i, ?_⟩
  change g _ = a
  simp only [map_add, map_sum, map_mul, hgC, hgX]
  dsimp only [Function.comp_apply] at hr hc
  change TrivSqZeroExt.inl (R.residueEquiv (residue R r)) +
    ∑ i, TrivSqZeroExt.inl (R.residueEquiv (residue R (c i))) *
      TrivSqZeroExt.inr (bV i) = a
  simp only [hr, hc, TrivSqZeroExt.inl_mul_inr]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum]

/-- A local map out of a power series algebra which is compatible with residues on constants
is compatible with residues everywhere. -/
private theorem mvPowerSeriesPresentation_residue
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (d : ℕ)
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : mvPowerSeriesObject R d →ₐ[Λ] A) [IsLocalHom f.toRingHom]
    (hC : ∀ r, A.residueEquiv (residue A (f (MvPowerSeries.C r))) =
      R.residueEquiv (residue R r)) :
    ∀ s, A.residueEquiv (residue A (f s)) =
      (mvPowerSeriesObject R d).residueEquiv (residue (mvPowerSeriesObject R d) s) := by
  intro s
  let _ : IsLocalRing R := R.completeLocal.isLocal
  have hs : s - MvPowerSeries.C (MvPowerSeries.constantCoeff s) ∈
      maximalIdeal (mvPowerSeriesObject R d) := by
    change ¬ IsUnit (s - MvPowerSeries.C (MvPowerSeries.constantCoeff s))
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hm := (map_maximalIdeal_le f.toRingHom) (Ideal.mem_map_of_mem f.toRingHom hs)
  have hzero : residue A (f (s - MvPowerSeries.C (MvPowerSeries.constantCoeff s))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have heq : residue A (f s) =
      residue A (f (MvPowerSeries.C (MvPowerSeries.constantCoeff s))) :=
    sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  rw [heq, hC]
  exact (mvPowerSeriesResidueEquiv_residue_C R d _).symm

/-- An object of the base category lying over a finite-dimensional square-zero extension of
`k` is presented by the power series algebra in that many variables over any object of the
completed base category, by sending the variables to a basis. -/
private theorem exists_mvPowerSeries_presentation_of_squareZero
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) (d : ℕ)
    (V : FGModuleCat.{max v w} k) (bV : Module.Basis (Fin d) k V)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (x : F)
    (hx : p.obj x = (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V) :
    ∃ q : mvPowerSeriesObject R d →ₐ[Λ] p.obj x,
      Function.Surjective q ∧
      ∀ s, (p.obj x).residueEquiv (residue (p.obj x) (q s)) =
        (mvPowerSeriesObject R d).residueEquiv
          (residue (mvPowerSeriesObject R d) s) := by
  obtain ⟨q, hq, hqC⟩ : ∃ q : mvPowerSeriesObject R d →ₐ[Λ]
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V),
      Function.Surjective q ∧
      ∀ r : R, q (MvPowerSeries.C r) =
        (TrivSqZeroExt.inl (R.residueEquiv (residue R r)) :
          ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V)) := by
    obtain ⟨q₀, hsurj, hC, -⟩ :=
      exists_squareZero_mvPowerSeries_presentation R d V bV
    exact ⟨q₀, hsurj, hC⟩
  have hinst : IsLocalHom q.toRingHom :=
    IsLocalHom.of_surjective q.toRingHom hq
  have hres := mvPowerSeriesPresentation_residue R d
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V) q
    (fun r ↦ by rw [hqC r]; rfl)
  refine ⟨(eqToHom hx.symm).hom.comp q, ?_, fun s ↦ ?_⟩
  · exact (artinianLocalAlgCat_eqToHom_bijective hx.symm).2.comp hq
  · exact ((eqToHom hx.symm).residue_comm (q s)).trans (hres s)

end PowerSeries

/-! ### Lifting the base of a presentation across a small extension -/

section BaseLift

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The key step of Schlessinger's construction.** Given the least lift `Y` of a
presentation `X` and a small extension in the category over a morphism out of `X`, the
presentation of `X` lifts to the source of the small extension, killing the kernel of `Y`.
Either the first projection of the fibre product has a section, in which case the lift is
immediate, or it is an essential surjection, in which case formal smoothness of the ambient
ring produces a surjective lift whose kernel is caught by minimality of `Y`. -/
private theorem exists_base_lift_of_least_presented_lift
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hS1 : SchlessingerConditionS1 p)
    (hlift : ∀ (B A : ArtinianLocalAlgCat.{u, v, w} Λ k) (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (g : S →ₐ[Λ] A), IsLocalHom g.toRingHom →
      (∀ s, A.residueEquiv (residue A (g s)) = S.residueEquiv (residue S s)) →
      ∃ h : S →ₐ[Λ] B, f.hom.comp h = g ∧
        ∀ s, B.residueEquiv (residue B (h s)) = S.residueEquiv (residue S s))
    (X Y : PresentedObject S p) (a : Y.obj ⟶ X.obj)
    (ha : (p.map a).hom.comp Y.hom = X.hom)
    (hleast : ∀ (Z : PresentedObject S p) (c : Z.obj ⟶ X.obj),
      (p.map c).hom.comp Z.hom = X.hom →
      maximalIdeal S * RingHom.ker X.hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom →
      RingHom.ker Y.hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom)
    {y x : F} (b : X.obj ⟶ x) (g : y ⟶ x)
    (hg : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (p.map g).hom.toRingHom)) :
    ∃ β : S →ₐ[Λ] p.obj y,
      (p.map g).hom.comp β = (p.map b).hom.comp X.hom ∧
      RingHom.ker Y.hom.toRingHom ≤ RingHom.ker β.toRingHom ∧
      ∀ s, (p.obj y).residueEquiv (residue (p.obj y) (β s)) =
        S.residueEquiv (residue S s) := by
  classical
  obtain ⟨P, q₁, q₂, hpb, hsmall, ⟨L⟩, hcase⟩ :=
    exists_pullback_completion_of_smallExtension hS1 b g hg
  have hXY := ker_le_ker_of_comp_eq _ _ ha
  suffices h : ∃ h : S →ₐ[Λ] P, q₁.hom.comp h = X.hom ∧
      RingHom.ker Y.hom.toRingHom ≤ RingHom.ker h.toRingHom ∧
      ∀ s, P.residueEquiv (residue P (h s)) = S.residueEquiv (residue S s) by
    obtain ⟨h, hh, hk, hr⟩ := h
    refine ⟨q₂.hom.comp h, ?_, ?_, fun s ↦ (q₂.residue_comm (h s)).trans (hr s)⟩
    · rw [← AlgHom.comp_assoc, ← ArtinianLocalAlgCat.comp_hom,
        ← hpb.w, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_assoc, hh]
    · exact hk.trans (ker_le_ker_of_comp_eq _ _ rfl)
  rcases hcase with ⟨s, hs⟩ | he
  · refine ⟨s.hom.comp X.hom, ?_, ?_, fun r ↦
        (s.residue_comm (X.hom r)).trans (X.residue_comm r)⟩
    · rw [← AlgHom.comp_assoc, ← ArtinianLocalAlgCat.comp_hom, hs]
      rfl
    · exact hXY.trans (ker_le_ker_of_comp_eq _ _ rfl)
  · obtain ⟨h, hh, hr⟩ := hlift P (p.obj X.obj) q₁ hsmall X.hom
      (IsLocalHom.of_surjective X.hom.toRingHom X.surjective) X.residue_comm
    have hlocalcomp : IsLocalHom (q₁.hom.toRingHom.comp h.toRingHom) := by
      change IsLocalHom (q₁.hom.comp h).toRingHom
      rw [hh]
      exact IsLocalHom.of_surjective X.hom.toRingHom X.surjective
    have hlocal : IsLocalHom h.toRingHom := isLocalHom_of_comp h.toRingHom q₁.hom.toRingHom
    have hsurj : Function.Surjective h := surjective_of_essentialSurjection S q₁ he h hr
      (by rw [hh]; exact X.surjective)
    let Z : PresentedObject S p :=
      { obj := L.apex
        hom := (eqToHom L.apex_eq.symm).hom.comp h
        surjective := (artinianLocalAlgCat_eqToHom_bijective L.apex_eq.symm).2.comp hsurj
        residue_comm := fun s ↦
          ((eqToHom L.apex_eq.symm).residue_comm (h s)).trans (hr s) }
    have hZ : (p.map L.toFirst).hom.comp Z.hom = X.hom := by
      rw [L.map_toFirst]
      change (eqToHom L.apex_eq ≫ q₁).hom.comp ((eqToHom L.apex_eq.symm).hom.comp h) = _
      rw [← AlgHom.comp_assoc, ← ArtinianLocalAlgCat.comp_hom]
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact hh
    have hker : RingHom.ker Z.hom.toRingHom = RingHom.ker h.toRingHom := by
      ext s
      change (eqToHom L.apex_eq.symm).hom (h s) = 0 ↔ h s = 0
      rw [← map_zero (eqToHom L.apex_eq.symm).hom]
      exact (artinianLocalAlgCat_eqToHom_bijective L.apex_eq.symm).1.eq_iff
    have hmul : maximalIdeal S * RingHom.ker X.hom.toRingHom ≤ RingHom.ker h.toRingHom := by
      refine Ideal.mul_le.mpr fun r hr' s hs ↦ ?_
      have h₁ : h r ∈ maximalIdeal P :=
        (map_maximalIdeal_le h.toRingHom) (Ideal.mem_map_of_mem h.toRingHom hr')
      have h₂ : h s ∈ RingHom.ker q₁.hom.toRingHom := by
        change q₁.hom (h s) = 0
        exact (DFunLike.congr_fun hh s).trans hs
      have hz := Ideal.mul_mem_mul h₁ h₂
      have hzero : maximalIdeal P * RingHom.ker q₁.hom.toRingHom = ⊥ :=
        maximalIdeal_mul_eq_bot_of_length_eq_one _ hsmall.2.2.2.2.2
      rw [hzero] at hz
      change h (r * s) = 0
      rw [map_mul]
      exact hz
    refine ⟨h, hh, ?_, hr⟩
    rw [← hker]
    exact hleast Z L.toFirst hZ (by rwa [hker])

/-- **Passing to the limit.** A tower of presentations whose kernels are cofinal in the
powers of the maximal ideal assembles into a formal object with that base, together with
comparison maps from the tower to its levels. -/
private theorem exists_formalObject_of_cofinal_presentations
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : ℕ → PresentedObject R p) (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (hcomm : ∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom)
    (hcofinal : ∀ n, ∃ m, RingHom.ker (X m).hom.toRingHom ≤ maximalIdeal R ^ (n + 1)) :
    ∃ ξ : FormalObject p, ∃ he : ξ.base = R,
      ∀ n, ∃ m, ∃ b : (X m).obj ⟶ ξ.level n,
        (p.map b).hom.comp (X m).hom =
          (eqToHom (ξ.level_eq n).symm).hom.comp
            (((AdicTruncation.functor n).map (eqToHom he.symm)).hom.comp
              (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n))) := by
  classical
  let D := AdicTruncation.obj R
  let q (n : ℕ) : R →ₐ[Λ] D n := Ideal.Quotient.mkₐ Λ _
  have hq (n : ℕ) : Function.Surjective (q n) := Ideal.Quotient.mk_surjective
  have hqres (n : ℕ) (r : R) : (D n).residueEquiv (residue (D n) (q n r)) =
      R.residueEquiv (residue R r) := AdicTruncation.residueEquiv_residue_mk R n r
  choose j hj using hcofinal
  let f (n : ℕ) : p.obj (X (j n)).obj ⟶ D n :=
    artinianFactorOfKerLe (X (j n)).hom (q n) (X (j n)).surjective (hq n)
      (fun r ↦ (hqres n r).trans (((X (j n)).residue_comm r).symm))
      (by
        change RingHom.ker (X (j n)).hom.toRingHom ≤
          RingHom.ker (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
        rw [Ideal.mk_ker]
        exact hj n)
  have hf (n : ℕ) : (f n).hom.comp (X (j n)).hom = q n :=
    AlgHom.liftOfSurjective_comp ..
  choose y hy i hi using fun n ↦ exists_pushforward_eq p hp (X (j n)).obj (f n)
  have hiq (n : ℕ) : (p.map (i n)).hom.comp (X (j n)).hom =
      (eqToHom (hy n).symm).hom.comp (q n) := by
    rw [hi, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_assoc, hf]
  have existsTransition (n : ℕ) : ∃ t : y (n + 1) ⟶ y n,
      p.IsHomLift (AdicTruncation.transition R n) t := by
    let m := max (j (n + 1)) (j n)
    obtain ⟨b₁, hb₁⟩ := exists_presentedTower_arrow X a hcomm (Nat.le_max_left (j (n + 1)) (j n))
    obtain ⟨b₂, hb₂⟩ := exists_presentedTower_arrow X a hcomm (Nat.le_max_right (j (n + 1)) (j n))
    let g : p.obj (y (n + 1)) ⟶ p.obj (y n) :=
      eqToHom (hy (n + 1)) ≫ AdicTruncation.transition R n ≫ eqToHom (hy n).symm
    have hg : p.map (b₁ ≫ i (n + 1)) ≫ g = p.map (b₂ ≫ i n) := by
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      obtain ⟨r, rfl⟩ := (X m).surjective z
      have h₁ := DFunLike.congr_fun hb₁ r
      have h₂ := DFunLike.congr_fun hb₂ r
      simp only [Functor.map_comp, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] at *
      rw [h₁, h₂]
      rw [show (p.map (i (n + 1))).hom ((X (j (n + 1))).hom r) =
        (eqToHom (hy (n + 1)).symm).hom (q (n + 1) r) from DFunLike.congr_fun (hiq (n + 1)) r]
      rw [show (p.map (i n)).hom ((X (j n)).hom r) =
        (eqToHom (hy n).symm).hom (q n r) from DFunLike.congr_fun (hiq n) r]
      change (eqToHom (hy n).symm).hom ((AdicTruncation.transition R n).hom
        ((eqToHom (hy (n + 1))).hom ((eqToHom (hy (n + 1)).symm).hom (q (n + 1) r)))) = _
      have heq : (eqToHom (hy (n + 1))).hom
          ((eqToHom (hy (n + 1)).symm).hom (q (n + 1) r)) = q (n + 1) r := by
        change ((eqToHom (hy (n + 1)).symm ≫ eqToHom (hy (n + 1))).hom) _ = _
        simp
      rw [heq]
      rfl
    obtain ⟨t, ht, _⟩ := exists_desc_of_cofibered p hp (b₁ ≫ i (n + 1)) (b₂ ≫ i n) g hg
    exact ⟨t, IsHomLift.of_fac p _ _ (hy (n + 1)) (hy n) (by simp [g, ht])⟩
  choose t ht using existsTransition
  let ξ : FormalObject p :=
    { base := R, level := y, level_eq := hy, transition := t, transition_lift := ht }
  refine ⟨ξ, rfl, fun n ↦ ⟨j n, i n, ?_⟩⟩
  change (p.map (i n)).hom.comp (X (j n)).hom =
    (eqToHom (hy n).symm).hom.comp
      (((AdicTruncation.functor n).map (𝟙 R)).hom.comp (q n))
  have hid : ((AdicTruncation.functor n).map (𝟙 R)).hom.comp (q n) = q n := by
    ext r
    rfl
  rw [hid]
  exact hiq n

/-- The tower of presentations over `S` descends to a tower over the quotient of `S` by the
intersection of the kernels, which is the base of the formal object produced. -/
public theorem exists_formalObject_of_presentedTower
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : ℕ → PresentedObject S p) (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (hcomm : ∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom)
    (c : ℕ) (hpow : ∀ n, maximalIdeal S ^ (n + c) ≤ RingHom.ker (X n).hom.toRingHom) :
    ∃ ξ : FormalObject p, ∃ q : S →ₐ[Λ] ξ.base,
      Function.Surjective q ∧
      (∀ s, ξ.base.residueEquiv (residue ξ.base (q s)) = S.residueEquiv (residue S s)) ∧
      RingHom.ker q.toRingHom = ⨅ n, RingHom.ker (X n).hom.toRingHom ∧
      ∀ n, ∃ m, ∃ b : (X m).obj ⟶ ξ.level n,
        (p.map b).hom.comp (X m).hom =
          (eqToHom (ξ.level_eq n).symm).hom.comp
            ((Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)).comp q) := by
  classical
  let J := fun n ↦ RingHom.ker (X n).hom.toRingHom
  let K := ⨅ n, J n
  have hK : K < ⊤ := (iInf_le J 0).trans_lt
    (lt_top_iff_ne_top.mpr (RingHom.ker_ne_top (X 0).hom.toRingHom))
  let R := completeQuotientObject S K hK
  let q : S →ₐ[Λ] R := Ideal.Quotient.mkₐ Λ K
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hqres (s : S) : R.residueEquiv (residue R (q s)) = S.residueEquiv (residue S s) :=
    completeQuotientObject_residueEquiv_mk S K hK s
  let Y (n : ℕ) : PresentedObject R p :=
    { obj := (X n).obj
      hom := Ideal.Quotient.liftₐ K (X n).hom (fun s hs ↦ (iInf_le J n) hs)
      surjective := by
        intro z
        obtain ⟨s, rfl⟩ := (X n).surjective z
        exact ⟨q s, rfl⟩
      residue_comm := fun r ↦ by
        obtain ⟨s, rfl⟩ := hq r
        exact ((X n).residue_comm s).trans (hqres s).symm }
  have hY (n : ℕ) : (Y n).hom.comp q = (X n).hom := rfl
  have hYcomm (n : ℕ) : (p.map (a n)).hom.comp (Y (n + 1)).hom = (Y n).hom := by
    ext r
    obtain ⟨s, rfl⟩ := hq r
    exact DFunLike.congr_fun (hcomm n) s
  have hcofinal : ∀ n, ∃ m, RingHom.ker (Y m).hom.toRingHom ≤ maximalIdeal R ^ (n + 1) := by
    intro n
    have hadic := quotientFiltration_isAdic_of_pow_shift_le S J
      (presentedTower_ker_antitone X a hcomm) c hpow
    obtain ⟨m, hm⟩ := hadic.1 (n + 1)
    refine ⟨m, ?_⟩
    intro r hr
    obtain ⟨s, rfl⟩ := hq r
    have hs : s ∈ J m := hr
    have hmem := hm (Ideal.mem_map_of_mem q.toRingHom hs)
    have hmax : Ideal.map q.toRingHom (maximalIdeal S) = maximalIdeal R :=
      map_maximalIdeal_of_surjective q.toRingHom hq
    change q s ∈ Ideal.map q.toRingHom (maximalIdeal S) ^ (n + 1) at hmem
    rwa [hmax] at hmem
  obtain ⟨ξ, he, hξ⟩ := exists_formalObject_of_cofinal_presentations R p hp Y a hYcomm hcofinal
  let q' : S →ₐ[Λ] ξ.base := (eqToHom he.symm).hom.comp q
  have hq' : Function.Surjective q' :=
    (completeLocalAlgCat_eqToHom_bijective he.symm).2.comp hq
  refine ⟨ξ, q', hq', ?_, ?_, ?_⟩
  · intro s
    exact ((eqToHom he.symm).residue_comm (q s)).trans (hqres s)
  · have hi := (completeLocalAlgCat_eqToHom_bijective he.symm).1
    ext s
    change (eqToHom he.symm).hom (q s) = 0 ↔ s ∈ K
    rw [← map_zero (eqToHom he.symm).hom, hi.eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  · intro n
    obtain ⟨m, b, hb⟩ := hξ n
    refine ⟨m, b, ?_⟩
    rw [← hY m, ← AlgHom.comp_assoc, hb]
    ext s
    change (eqToHom (ξ.level_eq n).symm).hom
      (((AdicTruncation.functor n).map (eqToHom he.symm)).hom
        (Ideal.Quotient.mk _ (q s))) =
      (eqToHom (ξ.level_eq n).symm).hom
        (Ideal.Quotient.mk _ ((eqToHom he.symm).hom (q s)))
    rfl

end BaseLift

/-! ### The associated morphism and the levels of a formal object -/

section Associated

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The presentation of the `n`-th level of a formal object by its base. -/
public noncomputable abbrev formalLevelProjection
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) (n : ℕ) : ξ.base →ₐ[Λ] p.obj (ξ.level n) :=
  (eqToHom (ξ.level_eq n).symm).hom.comp
    (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n))

/-- The presentation of a level is the quotient map followed by the transport. -/
public theorem formalLevelProjection_apply
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) (n : ℕ) (r : ξ.base) :
    formalLevelProjection ξ n r = (eqToHom (ξ.level_eq n).symm).hom
      (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r) := rfl

/-- The presentation of a level is surjective. -/
public theorem formalLevelProjection_surjective
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) (n : ℕ) : Function.Surjective (formalLevelProjection ξ n) :=
  (artinianLocalAlgCat_eqToHom_bijective (ξ.level_eq n).symm).2.comp
    Ideal.Quotient.mk_surjective

/-- The presentation of a level respects the chosen identifications of the residue fields. -/
public theorem formalLevelProjection_residue
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) (n : ℕ) (r : ξ.base) :
    (p.obj (ξ.level n)).residueEquiv (residue _ (formalLevelProjection ξ n r)) =
      ξ.base.residueEquiv (residue _ r) :=
  ((eqToHom (ξ.level_eq n).symm).residue_comm _).trans
    (AdicTruncation.residueEquiv_residue_mk ξ.base n r)

/-- The presentations of the levels are natural in morphisms of formal objects: transporting a
section of the base along a morphism and then presenting the target level agrees with
presenting the source level and then applying the level component. -/
public theorem formalLevelProjection_naturality
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {ξ η : FormalObject p} (a : ξ ⟶ η) (n : ℕ) :
    (p.map (a.app n)).hom.comp (formalLevelProjection ξ n) =
      (formalLevelProjection η n).comp a.base.hom := by
  have := a.app_lift n
  have hfac := IsHomLift.fac' p ((AdicTruncation.functor n).map a.base) (a.app n)
  refine AlgHom.ext fun r ↦ ?_
  change (p.map (a.app n)).hom (formalLevelProjection ξ n r) =
    formalLevelProjection η n (a.base.hom r)
  rw [hfac]
  exact congrArg (eqToHom (η.level_eq n).symm).hom
    (congrArg ((AdicTruncation.functor n).map a.base).hom
      (artinianLocalAlgCat_eqToHom_hom_apply
        (IsHomLift.domain_eq p ((AdicTruncation.functor n).map a.base) (a.app n))
        (ξ.level_eq n).symm _))

attribute [local implicit_reducible] BasedCategory.ofFunctor in
/-- The class of the value of the associated morphism at an Artinian point of the base is the
class of the level it selects, pushed forward along the induced map out of that level. -/
private theorem associatedMorphism_classOf_obj
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) (P : ChosenPushforwards p) (M : AssociatedMorphism ξ P)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (M.factor α)
        (classOf (BasedCategory.ofFunctor p) hp
          ⟨ξ.level (M.level α), ξ.level_eq (M.level α)⟩) =
      classOf (BasedCategory.ofFunctor p) hp
        ⟨M.toBasedFunctor.obj α, M.toBasedFunctor.w_obj α⟩ := by
  exact @map_classOf _ _ (BasedCategory.ofFunctor p) hp _ _ (M.factor α)
    ⟨ξ.level (M.level α), ξ.level_eq (M.level α)⟩
    ⟨M.toBasedFunctor.obj α, M.toBasedFunctor.w_obj α⟩ (M.pointInclusion α)
    (associatedMorphism_pointInclusion_isHomLift ξ M α)

attribute [local implicit_reducible] BasedCategory.ofFunctor in
/-- **The image of an Artinian point under the associated morphism, on isomorphism classes.**
The associated morphism carries the class of a point `α : R → A` of the base to the class of
the selected level of `ξ`, pushed forward along the map induced by `α`. -/
private theorem associatedMorphism_mapIsomorphismClasses_classOf
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) (P : ChosenPushforwards p) (M : AssociatedMorphism ξ P)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    mapIsomorphismClasses
        (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)) hp
        M.toBasedFunctor α.1
        (classOf (BasedCategory.ofFunctor
          (CategoryOfElements.π (restrictedCoyoneda ξ.base)))
          (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
          ⟨α, rfl⟩) =
      (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (M.factor α)
        (classOf (BasedCategory.ofFunctor p) hp
          ⟨ξ.level (M.level α), ξ.level_eq (M.level α)⟩) := by
  exact (mapIsomorphismClasses_classOf
      (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)) hp
      M.toBasedFunctor ⟨α, rfl⟩).trans
    (associatedMorphism_classOf_obj hp ξ P M α).symm

/-- The presentation of a level of a formal object is bijective as soon as the corresponding
power of the maximal ideal of its base vanishes. -/
private theorem formalLevelProjection_bijective
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ζ : FormalObject p) (n : ℕ) (h : AdicTruncation.ideal ζ.base n = ⊥) :
    Function.Bijective (formalLevelProjection ζ n) := by
  have h1 : Function.Bijective
      (Ideal.Quotient.mk (AdicTruncation.ideal ζ.base n)) := by
    refine ⟨fun r₁ r₂ hr ↦ ?_, Ideal.Quotient.mk_surjective⟩
    have h2 := Ideal.Quotient.eq.mp hr
    rw [h, Ideal.mem_bot, sub_eq_zero] at h2
    exact h2
  exact (artinianLocalAlgCat_eqToHom_bijective (ζ.level_eq n).symm).comp h1

/-- A formal object whose base is an Artinian algebra `A` is concentrated in any level `n` with
`m_A ^ (n + 1) = 0`: the presentation of that level is an isomorphism, and the resulting
identification of the level with `A` is the one induced by the base. -/
private theorem exists_artinianLevel_identification
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (ζ : FormalObject p) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (h : ζ.base = artinianToComplete.obj A) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ σ : p.obj (ζ.level n) ⟶ A, Function.Bijective σ.hom ∧
      Function.Bijective (formalLevelProjection ζ n) ∧
      σ.hom.comp (formalLevelProjection ζ n) = (eqToHom h).hom := by
  have hideal : AdicTruncation.ideal ζ.base n = ⊥ := by
    change maximalIdeal ζ.base ^ (n + 1) = ⊥
    rw [h]
    exact hn
  have hbij := formalLevelProjection_bijective ζ n hideal
  let e := AlgEquiv.ofBijective (formalLevelProjection ζ n) hbij
  let σhom : p.obj (ζ.level n) →ₐ[Λ] A := (eqToHom h).hom.comp e.symm.toAlgHom
  have hσfac : σhom.comp (formalLevelProjection ζ n) = (eqToHom h).hom := by
    refine AlgHom.ext fun r ↦ ?_
    exact congrArg (eqToHom h).hom (e.symm_apply_apply r)
  have hσbij : Function.Bijective σhom :=
    (completeLocalAlgCat_eqToHom_bijective h).comp e.symm.bijective
  have hσlocal : IsLocalHom σhom.toRingHom :=
    IsLocalHom.of_surjective σhom.toRingHom hσbij.2
  have hσres : ∀ z : p.obj (ζ.level n),
      A.residueEquiv (residue A (σhom z)) =
        (p.obj (ζ.level n)).residueEquiv (residue (p.obj (ζ.level n)) z) := by
    intro z
    obtain ⟨r, rfl⟩ := hbij.2 z
    rw [show σhom (formalLevelProjection ζ n r) = (eqToHom h).hom r from
      DFunLike.congr_fun hσfac r]
    exact ((eqToHom h).residue_comm r).trans (formalLevelProjection_residue ζ n r).symm
  exact ⟨⟨σhom, hσlocal, hσres⟩, hσbij, hbij, hσfac⟩

/-- **Condition (2) of the versality criterion.** A small-extension triangle over the base of
the formal object produced by a tower of presentations is filled in by the key lifting step at
a high enough stage. The small extension is the image of an arrow of `F`, and the map to be
lifted is prescribed on the base of the formal object through a stage of the tower. -/
public theorem exists_base_lift_of_tower_map
    (ambient : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hS1 : SchlessingerConditionS1 p)
    (hlift : ∀ (B A : ArtinianLocalAlgCat.{u, v, w} Λ k) (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (g : ambient →ₐ[Λ] A), IsLocalHom g.toRingHom →
      (∀ s, A.residueEquiv (residue A (g s)) = ambient.residueEquiv (residue ambient s)) →
      ∃ h : ambient →ₐ[Λ] B, f.hom.comp h = g ∧
        ∀ s, B.residueEquiv (residue B (h s)) = ambient.residueEquiv (residue ambient s))
    (X : ℕ → PresentedObject ambient p)
    (towerMap : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (ha : ∀ n, (p.map (towerMap n)).hom.comp (X (n + 1)).hom = (X n).hom)
    (hleast : ∀ n (Z : PresentedObject ambient p) (c : Z.obj ⟶ (X n).obj),
      (p.map c).hom.comp Z.hom = (X n).hom →
      maximalIdeal ambient * RingHom.ker (X n).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom →
      RingHom.ker (X (n + 1)).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom)
    (limitRing : CompleteLocalAlgCat.{u, v, w} Λ k)
    (q : ambient →ₐ[Λ] limitRing) (hq : Function.Surjective q)
    (hqr : ∀ s, limitRing.residueEquiv (residue limitRing (q s)) =
      ambient.residueEquiv (residue ambient s))
    (hker : ∀ n, RingHom.ker q.toRingHom ≤ RingHom.ker (X n).hom.toRingHom)
    {y x : F} (g : y ⟶ x)
    (hf : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (p.map g).hom.toRingHom))
    (δ : limitRing →ₐ[Λ] p.obj x) (n : ℕ) (toTarget : (X n).obj ⟶ x)
    (hb : (p.map toTarget).hom.comp (X n).hom = δ.comp q) :
    ∃ β : limitRing ⟶ artinianToComplete.obj (p.obj y),
      (p.map g).hom.comp β.hom = δ := by
  obtain ⟨β, hβ, hk, hr⟩ := exists_base_lift_of_least_presented_lift ambient p hS1 hlift
    (X n) (X (n + 1)) (towerMap n) (ha n) (hleast n) toTarget g hf
  let γ := AlgHom.liftOfSurjective q hq β ((hker (n + 1)).trans hk)
  have hγ : γ.comp q = β := AlgHom.liftOfSurjective_comp ..
  have hδ : (p.map g).hom.comp γ = δ := by
    refine AlgHom.ext fun r ↦ ?_
    obtain ⟨s, rfl⟩ := hq r
    exact (congrArg (p.map g).hom (DFunLike.congr_fun hγ s)).trans
      ((DFunLike.congr_fun hβ s).trans (DFunLike.congr_fun hb s))
  have hγlocal : IsLocalHom γ.toRingHom := by
    have h₁ : IsLocalHom (δ.comp q).toRingHom := by
      rw [← hb]
      have h₂ : IsLocalHom (X n).hom.toRingHom :=
        IsLocalHom.of_surjective _ (X n).surjective
      exact RingHom.isLocalHom_comp (p.map toTarget).hom.toRingHom (X n).hom.toRingHom
    have h₃ : IsLocalHom δ.toRingHom := isLocalHom_of_comp_surjective (q := q.toRingHom) hq h₁
    have h₄ : IsLocalHom ((p.map g).hom.toRingHom.comp γ.toRingHom) := by
      change IsLocalHom ((p.map g).hom.comp γ).toRingHom
      rw [hδ]
      infer_instance
    exact isLocalHom_of_comp γ.toRingHom (p.map g).hom.toRingHom
  refine ⟨{ hom := γ, isLocal := hγlocal, residue_comm := ?_ }, hδ⟩
  intro r
  obtain ⟨s, rfl⟩ := hq r
  change (p.obj y).residueEquiv (residue _ (γ (q s))) = _
  rw [show γ (q s) = β s from DFunLike.congr_fun hγ s]
  exact (hr s).trans (hqr s).symm

/-- **Condition (2) of the versality criterion**, in the form where the small extension is a
given arrow `f` of the base category and the arrow of `F` filling the triangle is a lift of
`f`. -/
public theorem exists_base_lift_of_tower_over
    (ambient : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hS1 : SchlessingerConditionS1 p)
    (hlift : ∀ (B A : ArtinianLocalAlgCat.{u, v, w} Λ k) (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (g : ambient →ₐ[Λ] A), IsLocalHom g.toRingHom →
      (∀ s, A.residueEquiv (residue A (g s)) = ambient.residueEquiv (residue ambient s)) →
      ∃ h : ambient →ₐ[Λ] B, f.hom.comp h = g ∧
        ∀ s, B.residueEquiv (residue B (h s)) = ambient.residueEquiv (residue ambient s))
    (X : ℕ → PresentedObject ambient p)
    (towerMap : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (ha : ∀ n, (p.map (towerMap n)).hom.comp (X (n + 1)).hom = (X n).hom)
    (hleast : ∀ n (Z : PresentedObject ambient p) (c : Z.obj ⟶ (X n).obj),
      (p.map c).hom.comp Z.hom = (X n).hom →
      maximalIdeal ambient * RingHom.ker (X n).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom →
      RingHom.ker (X (n + 1)).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom)
    (limitRing : CompleteLocalAlgCat.{u, v, w} Λ k)
    (q : ambient →ₐ[Λ] limitRing) (hq : Function.Surjective q)
    (hqr : ∀ s, limitRing.residueEquiv (residue limitRing (q s)) =
      ambient.residueEquiv (residue ambient s))
    (hker : ∀ n, RingHom.ker q.toRingHom ≤ RingHom.ker (X n).hom.toRingHom)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom))
    {y x : F} (g : y ⟶ x) (hg : p.IsHomLift f g)
    (δ : limitRing →ₐ[Λ] A) (n : ℕ) (toTarget : (X n).obj ⟶ x)
    (hb : (eqToHom (IsHomLift.codomain_eq p f g)).hom.comp
      ((p.map toTarget).hom.comp (X n).hom) = δ.comp q) :
    ∃ β : limitRing ⟶ artinianToComplete.obj B, f.hom.comp β.hom = δ := by
  subst_hom_lift p f g
  simp only [eqToHom_refl, ArtinianLocalAlgCat.id_hom, AlgHom.id_comp] at hb
  exact exists_base_lift_of_tower_map ambient p hS1 hlift X towerMap ha hleast limitRing q hq
    hqr hker g hf δ n toTarget hb

end Associated

/-! ### Schlessinger's existence theorem -/

section Existence

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The tower of Schlessinger's construction and its limit.** Condition (S1) turns a
presentation of a single object into a tower of presentations with the minimality property of
Stacks 06SZ at each stage, and that tower assembles into a formal object whose base is the
quotient of the ambient algebra by the intersection of the kernels. -/
private theorem exists_formalObject_of_presentedObject
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (hS1 : SchlessingerConditionS1 p)
    (X₀ : PresentedObject S p) :
    ∃ (ξ : FormalObject p) (q : S →ₐ[Λ] ξ.base) (X : ℕ → PresentedObject S p)
      (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj),
      X 0 = X₀ ∧
      Function.Surjective q ∧
      (∀ s, ξ.base.residueEquiv (residue ξ.base (q s)) = S.residueEquiv (residue S s)) ∧
      (∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom) ∧
      (∀ n (Z : PresentedObject S p) (b : Z.obj ⟶ (X n).obj),
        (p.map b).hom.comp Z.hom = (X n).hom →
        maximalIdeal S * RingHom.ker (X n).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom →
        RingHom.ker (X (n + 1)).hom.toRingHom ≤ RingHom.ker Z.hom.toRingHom) ∧
      (∀ n, RingHom.ker q.toRingHom ≤ RingHom.ker (X n).hom.toRingHom) ∧
      ∀ n, ∃ m, ∃ b : (X m).obj ⟶ ξ.level n,
        (p.map b).hom.comp (X m).hom = (formalLevelProjection ξ n).comp q := by
  have hlocal : IsLocalHom X₀.hom.toRingHom :=
    IsLocalHom.of_surjective _ X₀.surjective
  obtain ⟨c₀, hc₀⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (p.obj X₀.obj)).mp inferInstance
  have hc : maximalIdeal (p.obj X₀.obj) ^ (c₀ + 1) = ⊥ := by simp [pow_succ, hc₀]
  have hker0 : maximalIdeal S ^ (c₀ + 1) ≤ RingHom.ker X₀.hom.toRingHom :=
    maximalIdeal_pow_le_ker X₀.hom.toRingHom hc
  obtain ⟨X, a, hX0, hcomm, hmul, hleast⟩ := exists_presented_tower hp hS1 X₀
  have hpow : ∀ n, maximalIdeal S ^ (n + (c₀ + 1)) ≤ RingHom.ker (X n).hom.toRingHom := by
    intro n
    induction n with
    | zero => rw [hX0, Nat.zero_add]; exact hker0
    | succ n ih =>
      refine le_trans ?_ (hmul n)
      rw [show n + 1 + (c₀ + 1) = n + (c₀ + 1) + 1 from by omega]
      exact ideal_pow_succ_le_mul _ _ (n + (c₀ + 1)) ih
  obtain ⟨ξ, q, hqsurj, hqres, hkereq, hcompare⟩ :=
    exists_formalObject_of_presentedTower S p hp X a hcomm (c₀ + 1) hpow
  refine ⟨ξ, q, X, a, hX0, hqsurj, hqres, hcomm, hleast, fun n ↦ ?_, fun n ↦ ?_⟩
  · rw [hkereq]
    exact iInf_le _ n
  · obtain ⟨m, b, hb⟩ := hcompare n
    exact ⟨m, b, hb⟩

attribute [local implicit_reducible] BasedCategory.ofFunctor in
/-- **Condition (1) of the versality criterion, for the formal object of a tower.** Every
isomorphism class obtained by pushing forward the class of the bottom stage of the tower lies
in the image of the associated morphism of the formal object produced by that tower: a map out
of the bottom stage is induced by a point of the base of the formal object, and the value of
the associated morphism there is a pushforward of the level that point selects. -/
private theorem exists_associatedMorphism_class_image
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (ξ : FormalObject p) (q : S →ₐ[Λ] ξ.base) (hq : Function.Surjective q)
    (hqres : ∀ s, ξ.base.residueEquiv (residue ξ.base (q s)) = S.residueEquiv (residue S s))
    (X : ℕ → PresentedObject S p) (a : ∀ n, (X (n + 1)).obj ⟶ (X n).obj)
    (hcomm : ∀ n, (p.map (a n)).hom.comp (X (n + 1)).hom = (X n).hom)
    (hker : ∀ n, RingHom.ker q.toRingHom ≤ RingHom.ker (X n).hom.toRingHom)
    (hcompare : ∀ n, ∃ m, ∃ b : (X m).obj ⟶ ξ.level n,
      (p.map b).hom.comp (X m).hom = (formalLevelProjection ξ n).comp q)
    (P : ChosenPushforwards p)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : p.obj (X 0).obj ⟶ A) :
    ∃ z, mapIsomorphismClasses
        (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)) hp
        (associatedMorphism hp ξ P).toBasedFunctor A z =
      (isomorphismClasses (BasedCategory.ofFunctor p) hp).map f
        (classOf (BasedCategory.ofFunctor p) hp ⟨(X 0).obj, rfl⟩) := by
  classical
  have hX0local : IsLocalHom (X 0).hom.toRingHom :=
    IsLocalHom.of_surjective (X 0).hom.toRingHom (X 0).surjective
  have hflocal := f.isLocal
  have hcomplocal : IsLocalHom (f.hom.comp (X 0).hom).toRingHom := by
    change IsLocalHom (f.hom.toRingHom.comp (X 0).hom.toRingHom)
    infer_instance
  have hle := (hker 0).trans (ker_le_ker_of_comp_eq (X 0).hom f.hom rfl)
  let α : ξ.base →ₐ[Λ] A := AlgHom.liftOfSurjective q hq (f.hom.comp (X 0).hom) hle
  have hα : α.comp q = f.hom.comp (X 0).hom := AlgHom.liftOfSurjective_comp ..
  have hαq : IsLocalHom (α.comp q).toRingHom := by rw [hα]; exact hcomplocal
  have hαlocal : IsLocalHom α.toRingHom := isLocalHom_of_comp_surjective (q := q.toRingHom) hq hαq
  have hαres : ∀ r : ξ.base,
      A.residueEquiv (residue A (α r)) = ξ.base.residueEquiv (residue ξ.base r) := by
    intro r
    obtain ⟨s, rfl⟩ := hq r
    rw [show α (q s) = f.hom ((X 0).hom s) from DFunLike.congr_fun hα s, f.residue_comm,
      (X 0).residue_comm, hqres s]
  let αmor : ξ.base ⟶ artinianToComplete.obj A :=
    { hom := α, isLocal := hαlocal, residue_comm := hαres }
  let αE : (restrictedCoyoneda ξ.base).Elements :=
    (restrictedCoyoneda ξ.base).elementsMk A αmor
  let M := associatedMorphism hp ξ P
  set N := M.level αE with hN
  obtain ⟨m, b, hb⟩ := hcompare N
  obtain ⟨c, hc⟩ := exists_presentedTower_arrow X a hcomm (Nat.zero_le m)
  let gb : p.obj ((X m).obj) ⟶ (AdicTruncation.functor N).obj ξ.base :=
    p.map b ≫ eqToHom (ξ.level_eq N)
  have hgbLift : p.IsHomLift gb b :=
    IsHomLift.of_fac p gb b rfl (ξ.level_eq N) (by simp [gb])
  have hcLift : p.IsHomLift (p.map c) c := IsHomLift.of_fac p _ c rfl rfl (by simp)
  have h1 : (isomorphismClasses (BasedCategory.ofFunctor p) hp).map gb
      (classOf (BasedCategory.ofFunctor p) hp ⟨(X m).obj, rfl⟩) =
      classOf (BasedCategory.ofFunctor p) hp ⟨ξ.level N, ξ.level_eq N⟩ :=
    @map_classOf _ _ (BasedCategory.ofFunctor p) hp _ _ gb ⟨(X m).obj, rfl⟩
      ⟨ξ.level N, ξ.level_eq N⟩ b hgbLift
  have h2 : (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (p.map c)
      (classOf (BasedCategory.ofFunctor p) hp ⟨(X m).obj, rfl⟩) =
      classOf (BasedCategory.ofFunctor p) hp ⟨(X 0).obj, rfl⟩ :=
    @map_classOf _ _ (BasedCategory.ofFunctor p) hp _ _ (p.map c) ⟨(X m).obj, rfl⟩
      ⟨(X 0).obj, rfl⟩ c hcLift
  have hmaps : gb ≫ M.factor αE = p.map c ≫ f := by
    refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun z ↦ ?_)
    obtain ⟨s, rfl⟩ := (X m).surjective z
    have e2 : gb.hom ((X m).hom s) =
        Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) (q s) := by
      change (eqToHom (ξ.level_eq N)).hom ((p.map b).hom ((X m).hom s)) = _
      rw [show (p.map b).hom ((X m).hom s) = formalLevelProjection ξ N (q s) from
        DFunLike.congr_fun hb s]
      exact artinianLocalAlgCat_eqToHom_hom_apply (ξ.level_eq N) (ξ.level_eq N).symm _
    change (M.factor αE).hom (gb.hom ((X m).hom s)) = f.hom ((p.map c).hom ((X m).hom s))
    rw [e2, show (M.factor αE).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base N) (q s)) = α (q s) from
      DFunLike.congr_fun (M.factor_spec αE).2.2 (q s),
      show α (q s) = f.hom ((X 0).hom s) from DFunLike.congr_fun hα s,
      show (X 0).hom s = (p.map c).hom ((X m).hom s) from (DFunLike.congr_fun hc s).symm]
  refine ⟨_, (associatedMorphism_mapIsomorphismClasses_classOf hp ξ P M αE).trans ?_⟩
  calc (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (M.factor αE)
        (classOf (BasedCategory.ofFunctor p) hp ⟨ξ.level N, ξ.level_eq N⟩)
      = (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (M.factor αE)
          ((isomorphismClasses (BasedCategory.ofFunctor p) hp).map gb
            (classOf (BasedCategory.ofFunctor p) hp ⟨(X m).obj, rfl⟩)) := by rw [h1]
    _ = (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (gb ≫ M.factor αE)
          (classOf (BasedCategory.ofFunctor p) hp ⟨(X m).obj, rfl⟩) :=
        (Functor.map_comp_apply _ _ _ _).symm
    _ = (isomorphismClasses (BasedCategory.ofFunctor p) hp).map (p.map c ≫ f)
          (classOf (BasedCategory.ofFunctor p) hp ⟨(X m).obj, rfl⟩) := by rw [hmaps]
    _ = (isomorphismClasses (BasedCategory.ofFunctor p) hp).map f
          ((isomorphismClasses (BasedCategory.ofFunctor p) hp).map (p.map c)
            (classOf (BasedCategory.ofFunctor p) hp ⟨(X m).obj, rfl⟩)) :=
        Functor.map_comp_apply _ _ _ _
    _ = (isomorphismClasses (BasedCategory.ofFunctor p) hp).map f
          (classOf (BasedCategory.ofFunctor p) hp ⟨(X 0).obj, rfl⟩) := by rw [h2]

/-- **Steps 1 to 3 of Schlessinger's construction.** For a predeformation category satisfying
(S1) and (S2) and with a finite-dimensional tangent space there is a formal object whose
associated morphism is surjective on isomorphism classes over the dual numbers, and whose base
lifts across every small extension in `F` under which one of its levels maps to the target.
These are conditions (1) and (2) of the versality criterion of Stacks 06IU, the second one in
the form in which the small extension and the triangle are given inside `F`. -/
public theorem exists_formalObject_differential_surjective_and_level_lifts
    (Λ : Type u) (k : Type w) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (hS1 : SchlessingerConditionS1 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    [Fact (IsPredeformationCategory.{u, v, w} 𝓕.p)]
    [Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)))]
    [FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses 𝓕 hpre.cofibered))] :
    ∃ ξ : FormalObject 𝓕.p,
      (∀ P : ChosenPushforwards 𝓕.p,
        Function.Surjective (mapIsomorphismClasses
          (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
          hpre.cofibered (associatedMorphism hpre.cofibered ξ P).toBasedFunctor
          (artinianDualNumbers.{u, w, v} Λ k))) ∧
      ∀ ⦃y x : 𝓕.obj⦄ (g : y ⟶ x),
        InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (𝓕.p.map g).hom.toRingHom) →
        ∀ (N : ℕ) (c : ξ.level N ⟶ x),
          ∃ β : ξ.base ⟶ artinianToComplete.obj (𝓕.p.obj y),
            (𝓕.p.map g).hom.comp β.hom =
              ((𝓕.p.map c).hom.comp (formalLevelProjection ξ N)) := by
  classical
  have hsmall : Small.{max v w} k := small_max k
  have hS2bar := schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hpre.cofibered hS2
    (Or.inl hpre)
  obtain ⟨R, hR⟩ : ∃ R : CompleteLocalAlgCat.{u, max v w, w} Λ k,
      RingHom.FormallySmoothNAdic.{max v w} (algebraMap Λ R) (maximalIdeal R) :=
    exists_formallySmooth_completeLocalAlgebra Λ k
  obtain ⟨d, xgen, hxgen, hgen⟩ := exists_tangent_generating_object 𝓕 hpre hS2bar
  obtain ⟨q₀, hq₀surj, hq₀res⟩ :=
    exists_mvPowerSeries_presentation_of_squareZero R d
      (FGModuleCat.of k (ULift.{v} (Fin d → k)))
      ((Pi.basisFun k (Fin d)).map (ULift.moduleEquiv (R := k) (M := Fin d → k)).symm)
      𝓕.p xgen hxgen
  obtain ⟨ξ, q, X, a, hX0, hqsurj, hqres, hcomm, hleast, hker, hcompare⟩ :=
    exists_formalObject_of_presentedObject (mvPowerSeriesObject R d) 𝓕.p hpre.cofibered hS1
      { obj := xgen, hom := q₀, surjective := hq₀surj, residue_comm := hq₀res }
  obtain rfl : (X 0).obj = xgen := congrArg PresentedObject.obj hX0
  refine ⟨ξ, fun P z ↦ ?_, ?_⟩
  · obtain ⟨f, hf⟩ := hgen z
    obtain ⟨z', hz'⟩ := exists_associatedMorphism_class_image hpre.cofibered ξ q hqsurj hqres
      X a hcomm hker hcompare P f
    exact ⟨z', hz'.trans hf⟩
  · intro y x g hg N c
    obtain ⟨m, b, hb⟩ := hcompare N
    refine exists_base_lift_of_tower_map (mvPowerSeriesObject R d) 𝓕.p hS1 ?_ X a hcomm hleast
      ξ.base q hqsurj hqres hker g hg
      ((𝓕.p.map c).hom.comp (formalLevelProjection ξ N)) m (b ≫ c) ?_
    · intro B A f hf g' hg' hres
      exact @exists_mvPowerSeries_lift_of_formallySmooth Λ k _ _ _ R d hR B A f hf g' hg' hres
    · rw [𝓕.p.map_comp, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_assoc, hb]
      exact (AlgHom.comp_assoc _ _ _).symm

/-- **From level-wise lifting to condition (2) of the versality criterion.** If the base of a
formal object `ξ` lifts across every small extension that is the image of an arrow of `F`, with
the map to be lifted prescribed through one of the levels of `ξ`, then it lifts across every
small-extension triangle of formal objects — which is the second condition of the criterion of
[Stacks, Tag 06IU].

The two forms differ in where the small extension and the triangle live. In the hypothesis they
live inside `F`: the extension is `𝓕.p.map g` for an arrow `g` of `F`, and the map out of
`ξ.base` is presented as a map out of a level. In the conclusion they live in the category of
formal objects, as [Stacks, Tag 06IU] states them. The passage between the two is the
observation that a formal object over an *Artinian* base is concentrated in any level `N` with
`m ^ (N + 1) = 0` (`Deformation.exists_artinianLevel_identification`): choosing such an `N` for
both ends of the triangle identifies the two levels with the two algebras, pushing the level-`N`
component of `g` forward along those identifications produces the arrow of `F` the hypothesis
asks for, and `Deformation.isSmallExtension_eqToHom_comp` transports smallness to it. -/
public theorem baseLifts_of_levelLifts
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (ξ : FormalObject 𝓕.p)
    (hlevel : ∀ ⦃y x : 𝓕.obj⦄ (g : y ⟶ x),
      InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom (𝓕.p.map g).hom.toRingHom) →
      ∀ (N : ℕ) (c : ξ.level N ⟶ x),
        ∃ β : ξ.base ⟶ artinianToComplete.obj (𝓕.p.obj y),
          (𝓕.p.map g).hom.comp β.hom =
            ((𝓕.p.map c).hom.comp (formalLevelProjection ξ N))) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, max v w, w} Λ k⦄ (f : B ⟶ A),
      InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ ⦃y x : FormalObject 𝓕.p⦄ (g : y ⟶ x),
        (FormalObject.projection (p := 𝓕.p)).IsHomLift
          (artinianToComplete.map f) g →
      ∀ (a : ξ ⟶ x), ∃ b : ξ.base ⟶ y.base,
        b ≫ g.base = a.base := by
  classical
  intro B A f hf y x g hg α
  have hybase : y.base = artinianToComplete.obj B :=
    IsHomLift.domain_eq (FormalObject.projection (p := 𝓕.p)) (artinianToComplete.map f) g
  have hxbase : x.base = artinianToComplete.obj A :=
    IsHomLift.codomain_eq (FormalObject.projection (p := 𝓕.p)) (artinianToComplete.map f) g
  have hgbase : g.base = eqToHom hybase ≫ artinianToComplete.map f ≫ eqToHom hxbase.symm := by
    have hh := IsHomLift.fac' (FormalObject.projection (p := 𝓕.p))
      (artinianToComplete.map f) g
    simpa using hh
  obtain ⟨nA, hnA⟩ := exists_pow_maximalIdeal_eq_bot A
  obtain ⟨nB, hnB⟩ := exists_pow_maximalIdeal_eq_bot B
  set N := max nA nB with hNdef
  have hNA : maximalIdeal A ^ (N + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right
      (by omega : nA + 1 ≤ N + 1)).trans_eq hnA)
  have hNB : maximalIdeal B ^ (N + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right
      (by omega : nB + 1 ≤ N + 1)).trans_eq hnB)
  obtain ⟨σA, hσAbij, hπxbij, hσAfac⟩ :=
    exists_artinianLevel_identification x A hxbase N hNA
  obtain ⟨σB, hσBbij, hπybij, hσBfac⟩ :=
    exists_artinianLevel_identification y B hybase N hNB
  obtain ⟨xF, hxF, v, hv⟩ := exists_pushforward_eq 𝓕.p hpre.cofibered (x.level N) σA
  obtain ⟨yF, hyF, u, hu⟩ := exists_pushforward_eq 𝓕.p hpre.cofibered (y.level N) σB
  have hsquare : σB ≫ f = 𝓕.p.map (g.app N) ≫ σA := by
    refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun z ↦ ?_)
    obtain ⟨r, rfl⟩ := hπybij.2 z
    change f.hom (σB.hom (formalLevelProjection y N r)) =
      σA.hom ((𝓕.p.map (g.app N)).hom (formalLevelProjection y N r))
    rw [show σB.hom (formalLevelProjection y N r) = (eqToHom hybase).hom r from
        DFunLike.congr_fun hσBfac r,
      show (𝓕.p.map (g.app N)).hom (formalLevelProjection y N r) =
          formalLevelProjection x N (g.base.hom r) from
        DFunLike.congr_fun (formalLevelProjection_naturality g N) r,
      show σA.hom (formalLevelProjection x N (g.base.hom r)) =
          (eqToHom hxbase).hom (g.base.hom r) from
        DFunLike.congr_fun hσAfac (g.base.hom r), hgbase]
    exact (completeLocalAlgCat_eqToHom_hom_apply hxbase hxbase.symm
      ((artinianToComplete.map f).hom ((eqToHom hybase).hom r))).symm
  obtain ⟨gF, hgFmap, hgFfac⟩ := exists_desc_of_cofibered 𝓕.p hpre.cofibered u
    (g.app N ≫ v) (eqToHom hyF ≫ f ≫ eqToHom hxF.symm) (by
      rw [hu, 𝓕.p.map_comp, hv]
      calc (σB ≫ eqToHom hyF.symm) ≫ eqToHom hyF ≫ f ≫ eqToHom hxF.symm
          = σB ≫ f ≫ eqToHom hxF.symm := by simp
        _ = (σB ≫ f) ≫ eqToHom hxF.symm := (Category.assoc ..).symm
        _ = (𝓕.p.map (g.app N) ≫ σA) ≫ eqToHom hxF.symm := by rw [hsquare]
        _ = 𝓕.p.map (g.app N) ≫ σA ≫ eqToHom hxF.symm := Category.assoc ..)
  have hgFsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom (𝓕.p.map gF).hom.toRingHom) := by
    rw [hgFmap]
    exact isSmallExtension_eqToHom_comp hyF hxF.symm f hf
  obtain ⟨β, hβ⟩ := hlevel gF hgFsmall N (α.app N ≫ v)
  refine ⟨β ≫ artinianToComplete.map (eqToHom hyF) ≫ eqToHom hybase.symm, ?_⟩
  have hvinj : Function.Injective (𝓕.p.map v).hom := by
    rw [hv]
    exact ((artinianLocalAlgCat_eqToHom_bijective hxF.symm).comp hσAbij).1
  refine CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun r ↦ ?_)
  change g.base.hom ((eqToHom hybase.symm).hom
    ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r))) = α.base.hom r
  refine hπxbij.1 (hvinj ?_)
  have e2 : (𝓕.p.map u).hom (formalLevelProjection y N
      ((eqToHom hybase.symm).hom
        ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r)))) = β.hom r := by
    have h1 : σB.hom (formalLevelProjection y N ((eqToHom hybase.symm).hom
        ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r)))) =
        (eqToHom hyF).hom (β.hom r) :=
      (DFunLike.congr_fun hσBfac _).trans
        (completeLocalAlgCat_eqToHom_hom_apply hybase hybase.symm _)
    rw [hu]
    change (eqToHom hyF.symm).hom (σB.hom (formalLevelProjection y N _)) = β.hom r
    rw [h1]
    exact artinianLocalAlgCat_eqToHom_hom_apply hyF.symm hyF (β.hom r)
  calc (𝓕.p.map v).hom (formalLevelProjection x N (g.base.hom ((eqToHom hybase.symm).hom
        ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r)))))
      = (𝓕.p.map v).hom ((𝓕.p.map (g.app N)).hom (formalLevelProjection y N
          ((eqToHom hybase.symm).hom
            ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r))))) :=
        congrArg (𝓕.p.map v).hom
          (DFunLike.congr_fun (formalLevelProjection_naturality g N) _).symm
    _ = (𝓕.p.map (u ≫ gF)).hom (formalLevelProjection y N
          ((eqToHom hybase.symm).hom
            ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r)))) := by
        rw [hgFfac, 𝓕.p.map_comp]
        rfl
    _ = (𝓕.p.map gF).hom ((𝓕.p.map u).hom (formalLevelProjection y N
          ((eqToHom hybase.symm).hom
            ((artinianToComplete.map (eqToHom hyF)).hom (β.hom r))))) := by
        rw [𝓕.p.map_comp]
        rfl
    _ = (𝓕.p.map gF).hom (β.hom r) := congrArg (𝓕.p.map gF).hom e2
    _ = (𝓕.p.map (α.app N ≫ v)).hom (formalLevelProjection ξ N r) :=
        DFunLike.congr_fun hβ r
    _ = (𝓕.p.map v).hom ((𝓕.p.map (α.app N)).hom (formalLevelProjection ξ N r)) := by
        rw [𝓕.p.map_comp]
        rfl
    _ = (𝓕.p.map v).hom (formalLevelProjection x N (α.base.hom r)) :=
        congrArg (𝓕.p.map v).hom
          (DFunLike.congr_fun (formalLevelProjection_naturality α N) r)

/-- **Schlessinger's existence theorem.** A predeformation category over `𝒞_Λ` which satisfies
his conditions (S1) and (S2) and whose tangent space is finite dimensional has a versal formal
object. The formal object is the limit of the tower of presentations of Stacks 06SZ over a
power series algebra on a basis of the tangent space, taken over a complete local algebra which
is formally smooth over `Λ`; versality is checked through the criterion of Stacks 06IU, whose
condition (1) comes from the choice of the bottom stage of the tower and whose condition (2) is
the key lifting step.

The finite-dimensionality hypothesis speaks about the canonical `k`-vector space structure of
Stacks 06IH on the tangent space, which is available as soon as `𝓕` is a predeformation
category whose functor of isomorphism classes satisfies (S2); both of those are consequences
of the hypotheses — the second is `Deformation.schlessingerConditionS2_of_isIsomorphismClasses`
applied to `hS2` — so they are installed by the `letI` prefix of `hfin` rather than assumed. -/
@[stacks 06IW "existence of a versal formal object", sga "7 VI 1.11" "(i)+(ii) => versal"]
public theorem exists_versalFormalObject
    (Λ : Type u) (k : Type w) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (hS1 : SchlessingerConditionS1 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    (hfin :
      letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨hpre⟩
      letI : Fact (SchlessingerConditionS2
          (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered))) :=
        ⟨schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hpre.cofibered hS2 (Or.inl hpre)⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses 𝓕 hpre.cofibered))) :
    ∃ ξ : FormalObject 𝓕.p, IsVersal hpre.cofibered ξ := by
  classical
  let : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨hpre⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered))) :=
    ⟨schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hpre.cofibered hS2 (Or.inl hpre)⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
    (isomorphismClasses 𝓕 hpre.cofibered)) := hfin
  obtain ⟨ξ, htangent, hlevel⟩ :=
    exists_formalObject_differential_surjective_and_level_lifts Λ k 𝓕 hpre hS1 hS2
  refine ⟨ξ, (isVersal_iff_differential_surjective_and_base_lifts 𝓕 hpre hS1 hS2 ξ
    (chosenPushforwardsOfCofibered 𝓕.p hpre.cofibered)).2 ⟨htangent _, ?_⟩⟩
  intro B A f hf y x g hg α
  exact baseLifts_of_levelLifts 𝓕 hpre ξ hlevel f hf g hg α

end Existence

end Deformation

end
