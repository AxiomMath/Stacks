module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.Basic

/-!
# A principal-ideal counterexample for sections away from an ideal

Let `k` be a field and let `A` be the quotient of the polynomial ring over `k` in the variables
`x`, `y` and `zₙ` for `n ≥ 1` by the relations `xⁿ zₙ = 0`. Write `I = (x)`. The complement of
`V(I)` in `Spec(A)` is the single standard open `D(x)`, and the fraction `y/x` is a section of
the structure sheaf there. That section is **not** in the image of the canonical map from
`colim_n Hom_A(Iⁿ, A)` to the sections over the complement of `V(I)`. Hence that canonical map
is not an isomorphism in general, already for a *principal* ideal.

## Main definitions

* `relationIdeal` and `counterexampleRing`: the presented ring `A`.
* `x`, `y`, `z`: its distinguished coordinates.
* `principalIdeal`: the ideal `I = (x)`.
* `fractionSection`: the section `y/x` of `𝒪` on the complement of `V(I)`.

## Main results

* `complement_eq_basicOpen`: the complement of `V(I)` is `D(x)`.
* `fractionSection_restrict`: on `D(x)` the section `fractionSection` is the fraction `y/x`.
* `fractionSection_not_mem_range`: it is not in the range of the canonical map.
* `canonicalMapToSections_not_surjective` and `canonicalMapToSections_not_isIso`: consequently
  that canonical map is neither surjective nor an isomorphism.

## Implementation notes

The variables `zₙ₊₁` are indexed by `n : ℕ`, so the variable index type is `Fin 2 ⊕ ℕ` and the
`n`-th relation reads `xⁿ⁺¹ zₙ₊₁ = 0`.

Because `I` is principal the complement of `V(I)` *equals* the standard open `D(x)`, so no
gluing is needed: `ofBasicOpen` transports a section on `D(x)` to a section on the complement
along that equality of opens, and `restrictToBasicOpen` undoes it.

## References

* [Stacks Project, Tag 01PN](https://stacks.math.columbia.edu/tag/01PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPowerSections
open TopologicalSpace

universe u v w

namespace Stacks.AlgebraicGeometry.PrincipalIdealCounterexample

/-!
### Sections away from a principal ideal

For `I = (r)` the complement of `V(I)` is the standard open `D(r)`, so sections on the two
agree. This part is general: it does not refer to the counterexample ring.
-/

section Principal

/-- Any two inclusions between the same pair of opens agree. -/
private lemma opens_hom_eq {X : Type*} [TopologicalSpace X] {U V : Opens X} (f g : U ⟶ V) :
    f = g :=
  Subsingleton.elim f g

variable (A : Type u) [CommRing A]

/-- The lift of a principal ideal to the universe-lifted ring is principal. -/
lemma liftedIdeal_span_singleton (r : A) :
    liftedIdeal.{u, v} A (Ideal.span {r}) =
      Ideal.span {(ULift.up r : ULift.{v} A)} := by
  show (Ideal.span {r}).comap (ULift.ringEquiv : ULift.{v} A ≃+* A) = _
  rw [← Ideal.map_symm (ULift.ringEquiv : ULift.{v} A ≃+* A), Ideal.map_span,
    Set.image_singleton]
  congr 1

/-- For a principal ideal `(r)` the complement of the vanishing locus is the standard open
`D(r)`. -/
lemma complementVanishing_span_singleton (r : A) :
    complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A (Ideal.span {r})) =
      PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A) := by
  ext p
  show ¬ ((liftedIdeal.{u, v} A (Ideal.span {r}) : Ideal (ULift.{v} A)) ≤ p.1) ↔
    (ULift.up r : ULift.{v} A) ∉ p.1
  rw [liftedIdeal_span_singleton, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]

variable (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- When `D(r)` is the whole complement of `V(I)`, a section on `D(r)` is a section on the
complement. -/
noncomputable def ofBasicOpen (r : A)
    (hr : complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) =
      PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A)) :
    (sectionsPresheaf A M).obj (.op (PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A))) ⟶
      sectionsOnComplement A I M :=
  (sectionsPresheaf A M).map (homOfLE hr.le).op

/-- Restricting along `f : U ⟶ V` and then along `g : V ⟶ U` is the identity on sections. -/
private lemma map_op_map_op_eq_self {U V : Opens (PrimeSpectrum (ULift.{v} A))} (f : U ⟶ V)
    (g : V ⟶ U) (t : (sectionsPresheaf A M).obj (.op V)) :
    (sectionsPresheaf A M).map g.op ((sectionsPresheaf A M).map f.op t) = t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, opens_hom_eq (g ≫ f) (𝟙 _)]
  simp

/-- `ofBasicOpen` is a section of `restrictToBasicOpen`. -/
lemma restrictToBasicOpen_ofBasicOpen (r : A) (hrI : r ∈ I)
    (hr : complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) =
      PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A))
    (t : (sectionsPresheaf A M).obj
      (.op (PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A)))) :
    restrictToBasicOpen A I M r hrI (ofBasicOpen A I M r hr t) = t :=
  map_op_map_op_eq_self A M _ _ t

/-- `ofBasicOpen` is a retraction of `restrictToBasicOpen`. -/
lemma ofBasicOpen_restrictToBasicOpen (r : A) (hrI : r ∈ I)
    (hr : complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) =
      PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A))
    (s : sectionsOnComplement A I M) :
    ofBasicOpen A I M r hr (restrictToBasicOpen A I M r hrI s) = s :=
  map_op_map_op_eq_self A M _ _ s

/-- For a principal ideal, restriction to `D(r)` identifies the sections on the complement of
`V(I)` with the sections on `D(r)`. -/
lemma restrictToBasicOpen_bijective (r : A) (hrI : r ∈ I)
    (hr : complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) =
      PrimeSpectrum.basicOpen (ULift.up r : ULift.{v} A)) :
    Function.Bijective (restrictToBasicOpen A I M r hrI) :=
  ⟨Function.LeftInverse.injective (ofBasicOpen_restrictToBasicOpen A I M r hrI hr),
    Function.RightInverse.surjective (restrictToBasicOpen_ofBasicOpen A I M r hrI hr)⟩

/-- Two fractions with denominators powers of `f` agree on `D(f)` exactly when they agree after
multiplying by a further power of `f`. -/
lemma tildeBasicOpenFraction_eq_iff {R : CommRingCat.{w}} (N : ModuleCat.{w} R) (f : R)
    (n p : ℕ) (m m' : N) :
    tildeBasicOpenFraction N f n m = tildeBasicOpenFraction N f p m' ↔
      ∃ j : ℕ, f ^ (j + n) • m' = f ^ (j + p) • m := by
  rw [tildeBasicOpenFraction, tildeBasicOpenFraction, IsLocalizedModule.mk'_eq_mk'_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff (s : R) f).mp s.2
    refine ⟨j, ?_⟩
    simpa only [Submonoid.smul_def, ← hj, smul_smul, ← pow_add] using hs
  · rintro ⟨j, hj⟩
    refine ⟨⟨f ^ j, ⟨j, rfl⟩⟩, ?_⟩
    simpa only [Submonoid.smul_def, smul_smul, ← pow_add] using hj

/-- Two fractions with denominators powers of `r` agree on `D(r)` exactly when they agree after
multiplying by a further power of `r`. -/
lemma basicOpenFraction_eq_iff (r : A) (n p : ℕ) (m m' : M) :
    basicOpenFraction A M r n m = basicOpenFraction A M r p m' ↔
      ∃ j : ℕ, r ^ (j + n) • m' = r ^ (j + p) • m := by
  refine Iff.trans (tildeBasicOpenFraction_eq_iff (R := .of (ULift.{v} A))
    (ModuleCat.of (ULift.{v} A) (ULift.{u} M)) (ULift.up r) n p
    (ULift.up m) (ULift.up m')) ?_
  exact ⟨fun ⟨j, hj⟩ => ⟨j, congrArg ULift.down hj⟩,
    fun ⟨j, hj⟩ => ⟨j, congrArg ULift.up hj⟩⟩

/-- Every element of `colim_n Hom_A(Iⁿ, M)` is the image of a representative of some level. -/
lemma exists_colimit_ι_eq (ζ : ↥(colimit (idealPowersHom A I M))) :
    ∃ (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M),
      colimit.ι (idealPowersHom A I M) n φ = ζ := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0}
      (forget AddCommGrpCat.{max u v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have h2 : PreservesColimit (idealPowersHom A I M)
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat ⋙ forget AddCommGrpCat) :=
    comp_preservesColimit _ _
  have hpres : PreservesColimit (idealPowersHom A I M) (forget (ModuleCat.{max u v} A)) :=
    HasForget₂.forget_comp (C := ModuleCat.{max u v} A) (D := AddCommGrpCat) ▸ h2
  exact Concrete.colimit_exists_rep (idealPowersHom A I M) ζ

end Principal

/-!
### The ring `A = k[x,y,z₁,z₂,…]/(xⁿzₙ)`
-/

variable (k : Type u) [Field k]

/-- Indices for `x`, `y` and for `zₙ` with `n ≥ 1`. -/
abbrev variableIndex := Fin 2 ⊕ ℕ

/-- The relations `xⁿzₙ`, for positive `n`. -/
noncomputable def relationIdeal : Ideal (MvPolynomial (variableIndex) k) :=
  Ideal.span (Set.range fun n : ℕ =>
    (MvPolynomial.X (Sum.inl (0 : Fin 2)) : MvPolynomial variableIndex k) ^ (n + 1) *
      MvPolynomial.X (Sum.inr n))

/-- The ring `k[x,y,{zₙ}_{n≥1}]/({xⁿzₙ}_{n≥1})`. -/
abbrev counterexampleRing := MvPolynomial variableIndex k ⧸ relationIdeal k

/-- The coordinate `x` in the quotient ring. -/
noncomputable def x : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inl (0 : Fin 2)))

/-- The coordinate `y` in the quotient ring. -/
noncomputable def y : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inl (1 : Fin 2)))

/-- The coordinate `zₙ₊₁` in the quotient ring. -/
noncomputable def z (n : ℕ) : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inr n))

/-- The ideal `I = (x)` in the quotient ring. -/
noncomputable def principalIdeal : Ideal (counterexampleRing k) := Ideal.span {x k}

/-- The generator lies in the ideal it generates. -/
lemma x_mem_principalIdeal : x k ∈ principalIdeal k :=
  Ideal.subset_span rfl

/-- The defining relations of the counterexample ring: `xⁿ⁺¹ zₙ₊₁ = 0`. -/
lemma relation_at_index (n : ℕ) : x k ^ (n + 1) * z k n = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  show _ ∈ relationIdeal k
  rw [relationIdeal]
  exact Ideal.subset_span ⟨n, rfl⟩

/-- The element `zᵠ₊₁ xᵠ y` of the counterexample ring is nonzero, for every `q`. -/
private lemma obstruction_ne_zero (q : ℕ) : z k q * x k ^ q * y k ≠ 0 := by
  let S : Ideal (Polynomial k) := Ideal.span {(Polynomial.X : Polynomial k) ^ (q + 1)}
  let T := Polynomial k ⧸ S
  let t : T := Ideal.Quotient.mk S Polynomial.X
  let vars : variableIndex → T := fun v =>
    match v with
    | Sum.inl i => if i = 0 then t else 1
    | Sum.inr n => if n = q then 1 else 0
  let ev : MvPolynomial (variableIndex) k →+* T :=
    MvPolynomial.eval₂Hom (algebraMap k T) vars
  have ht : t ^ (q + 1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hrel : relationIdeal k ≤ RingHom.ker ev := by
    rw [relationIdeal]
    apply Ideal.span_le.mpr
    rintro p ⟨n, rfl⟩
    show ev _ = 0
    by_cases hn : n = q
    · subst n
      simp [ev, vars, ht]
    · simp [ev, vars, hn]
  let evQ : counterexampleRing k →+* T :=
    Ideal.Quotient.lift (relationIdeal k) ev
      (fun p hp => RingHom.mem_ker.mp (hrel hp))
  have hnonzero : t ^ q ≠ 0 := by
    intro heq
    have hmem : (Polynomial.X : Polynomial k) ^ q ∈ S :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [t] using heq)
    change (Polynomial.X : Polynomial k) ^ q ∈
      Ideal.span {(Polynomial.X : Polynomial k) ^ (q + 1)} at hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp ⟨c, hc⟩) q (by omega)
    simp at hcoeff
  have heval : evQ (z k q * x k ^ q * y k) = t ^ q := by
    simp [evQ, ev, vars, t, x, y, z, Ideal.Quotient.lift_mk]
  intro h
  have h' := congrArg evQ h
  rw [map_zero] at h'
  exact hnonzero (heval.symm.trans h')

/-!
### The section `y/x` and the failure of surjectivity
-/

/-- The complement of `V(x)` is the standard open `D(x)`. -/
lemma complement_eq_basicOpen :
    complementVanishing (ULift.{u} (counterexampleRing k))
        (liftedIdeal.{u, u} (counterexampleRing k) (principalIdeal k)) =
      PrimeSpectrum.basicOpen
        (ULift.up (x k) : ULift.{u, u} (counterexampleRing k)) :=
  complementVanishing_span_singleton (counterexampleRing k) (x k)

/-- The fraction `y/x`, as a section of `𝒪` on the complement of `V(x)`. -/
@[stacks 01PN "first example: the section y/x on Spec(A) minus V(x), A = k[x,y,z_n]/(x^n z_n)"]
noncomputable def fractionSection :
    sectionsOnComplement (counterexampleRing k) (principalIdeal k) (counterexampleRing k) :=
  ofBasicOpen (counterexampleRing k) (principalIdeal k) (counterexampleRing k) (x k)
    (complement_eq_basicOpen k)
    (basicOpenFraction (counterexampleRing k) (counterexampleRing k) (x k) 1 (y k))

/-- On `D(x)`, which is all of the complement of `V(x)`, the section is the fraction `y/x`. -/
@[stacks 01PN "first example: that section restricts on D(x) to the fraction y/x"]
lemma fractionSection_restrict :
    restrictToBasicOpen (counterexampleRing k) (principalIdeal k) (counterexampleRing k)
        (x k) (x_mem_principalIdeal k) (fractionSection k) =
      basicOpenFraction (counterexampleRing k) (counterexampleRing k) (x k) 1 (y k) :=
  restrictToBasicOpen_ofBasicOpen (counterexampleRing k) (principalIdeal k)
    (counterexampleRing k) (x k) (x_mem_principalIdeal k) (complement_eq_basicOpen k) _

/-- The fraction `y/x` is not obtained from a map out of any power of `(x)`. -/
@[stacks 01PN "first example: y/x is not in the range of the map from colim_n Hom_A((x)^n, A)"]
theorem fractionSection_not_mem_range :
    fractionSection k ∉ Set.range (canonicalMapToSections (counterexampleRing k)
      (principalIdeal k) (counterexampleRing k)) := by
  rintro ⟨ζ, hζ⟩
  obtain ⟨n, φ, rfl⟩ := exists_colimit_ι_eq (counterexampleRing k) (principalIdeal k)
    (counterexampleRing k) ζ
  have hx : x k ∈ principalIdeal k := x_mem_principalIdeal k
  have hres := congrArg (restrictToBasicOpen (counterexampleRing k) (principalIdeal k)
    (counterexampleRing k) (x k) hx) hζ
  have hres2 : basicOpenFraction (counterexampleRing k) (counterexampleRing k) (x k) n
        (φ ⟨x k ^ n, Ideal.pow_mem_pow hx n⟩) =
      basicOpenFraction (counterexampleRing k) (counterexampleRing k) (x k) 1 (y k) :=
    (canonicalMapToSections_restrict_ι (counterexampleRing k) (principalIdeal k)
      (counterexampleRing k) n φ (x k) hx).symm.trans (hres.trans (fractionSection_restrict k))
  obtain ⟨m, hm⟩ := (basicOpenFraction_eq_iff (counterexampleRing k) (counterexampleRing k)
    (x k) n 1 _ (y k)).mp hres2
  simp only [smul_eq_mul] at hm
  have hpow : (m + n) + 1 = (m + 1) + n := by omega
  have hmem : x k ^ ((m + n) + 1) * z k (m + n) ∈
      (principalIdeal k ^ n : Ideal (counterexampleRing k)) := by
    rw [principalIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨x k ^ (m + 1) * z k (m + n), ?_⟩
    rw [hpow, pow_add]
    ring
  have hdecomp :
      (⟨x k ^ ((m + n) + 1) * z k (m + n), hmem⟩ :
          ↥(principalIdeal k ^ n : Ideal (counterexampleRing k))) =
        (z k (m + n) * x k ^ (m + 1)) •
          (⟨x k ^ n, Ideal.pow_mem_pow hx n⟩ :
            ↥(principalIdeal k ^ n : Ideal (counterexampleRing k))) := by
    apply Subtype.ext
    show x k ^ ((m + n) + 1) * z k (m + n) = (z k (m + n) * x k ^ (m + 1)) * x k ^ n
    rw [hpow, pow_add]
    ring
  have hzero :
      (⟨x k ^ ((m + n) + 1) * z k (m + n), hmem⟩ :
        ↥(principalIdeal k ^ n : Ideal (counterexampleRing k))) = 0 :=
    Subtype.ext (relation_at_index k (m + n))
  have hphi : φ (⟨x k ^ ((m + n) + 1) * z k (m + n), hmem⟩ :
      ↥(principalIdeal k ^ n : Ideal (counterexampleRing k))) = 0 := by
    rw [hzero, map_zero]
  rw [hdecomp, map_smul, smul_eq_mul] at hphi
  refine obstruction_ne_zero k (m + n) ?_
  calc z k (m + n) * x k ^ (m + n) * y k
      = z k (m + n) * (x k ^ (m + n) * y k) := by ring
    _ = z k (m + n) * (x k ^ (m + 1) * φ ⟨x k ^ n, Ideal.pow_mem_pow hx n⟩) := by rw [hm]
    _ = (z k (m + n) * x k ^ (m + 1)) * φ ⟨x k ^ n, Ideal.pow_mem_pow hx n⟩ := by ring
    _ = 0 := hphi

/-- The canonical map is not surjective for the principal ideal `(x)`. -/
@[stacks 01PN "first example: the canonical map for I = (x) is not surjective"]
theorem canonicalMapToSections_not_surjective :
    ¬ Function.Surjective (canonicalMapToSections (counterexampleRing k)
      (principalIdeal k) (counterexampleRing k)) := fun h =>
  fractionSection_not_mem_range k (h (fractionSection k))

/-- The canonical map is not an isomorphism for the principal ideal `(x)`. -/
@[stacks 01PN "first example: the canonical map for I = (x) is not an isomorphism"]
theorem canonicalMapToSections_not_isIso :
    ¬ IsIso (canonicalMapToSections (counterexampleRing k)
      (principalIdeal k) (counterexampleRing k)) := by
  intro h
  refine fractionSection_not_mem_range k ⟨inv (canonicalMapToSections (counterexampleRing k)
    (principalIdeal k) (counterexampleRing k)) (fractionSection k), ?_⟩
  exact congrArg (fun f => f.hom (fractionSection k))
    (IsIso.inv_hom_id (canonicalMapToSections (counterexampleRing k)
      (principalIdeal k) (counterexampleRing k)))

end Stacks.AlgebraicGeometry.PrincipalIdealCounterexample
