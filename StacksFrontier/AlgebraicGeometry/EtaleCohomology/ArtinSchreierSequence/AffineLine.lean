module

public import Mathlib.RingTheory.PolynomialAlgebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.DegreeOneBoundary
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionSmoothCurve

/-!
# `H¹(𝐀¹_k, 𝐙/p𝐙)` and extension of the algebraically closed ground field

Let `k` be a field of characteristic `p > 0`. The Artin–Schreier sequence ([Stacks, Tag 0A3J])
on the affine line `𝐀¹_k = Spec k[x]` gives an exact sequence

`k[x] ⟶ k[x] ⟶ H¹(𝐀¹_k, 𝐙/p𝐙) ⟶ 0`

whose first arrow is `f ↦ f ^ p - f`. For `k` algebraically closed the polynomials
`∑_{p ∤ n} λₙ xⁿ` are a set of representatives of the cokernel
(`Polynomial.existsUnique_sub_mem_range_ringArtinSchreier`), and consequently, for an extension
`k'/k` of algebraically closed fields with `k' ≠ k`, the restriction map
`H¹(𝐀¹_k, 𝐙/p𝐙) → H¹(𝐀¹_{k'}, 𝐙/p𝐙)` is not surjective: the class of `λ x` with `λ ∈ k' ∖ k`
is not hit. On the other hand, with coefficients `𝐙/n𝐙` for `n` invertible in `k` the
restriction map is bijective in every degree, by statement (6) of Situation 0A52 (Tag 0A58,
proved through Lemma 0A5B). This is [Stacks, Tag 0A47].

## Main definitions

* `Stacks.ArtinSchreier.affineLine`: `𝐀¹_k = Spec k[x]`, with structure morphism
  `Stacks.ArtinSchreier.affineLineStructure`.
* `Stacks.ArtinSchreier.affineLineBoundary`: the boundary `k[x] →+ H¹(𝐀¹_k, 𝐙/p𝐙)`.
* `Stacks.ArtinSchreier.scalarExtensionAffineLineEquiv`: `Γ(𝐀¹_k ×_k k') ≃ k'[x]`.

## Main results

* `Stacks.ArtinSchreier.exact_affineLineBoundary`: the exact sequence.
* `Stacks.ArtinSchreier.existsUnique_affineLineBoundary_eq`: the representatives, in cohomology.
* `Stacks.ArtinSchreier.not_surjective_etaleCohomologyRestrictionMap_affineLine`: the restriction
  map is not surjective for `k ⊊ k'`.
* `Stacks.ArtinSchreier.exists_not_bijective_etaleCohomologyRestrictionMap_affineLine`: so it is
  not an isomorphism in general.
* `Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_affineLine_of_isUnit`: with
  coefficients prime to the characteristic it is an isomorphism.

## References

* [Stacks Project, Tag 0A47](https://stacks.math.columbia.edu/tag/0A47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Polynomial
open Stacks.EtaleCohomology

universe w v u

namespace Stacks.ArtinSchreier

section AffineLine

variable (k : Type u) [Field k]

/-- **The affine line** `𝐀¹_k = Spec k[x]`. -/
abbrev affineLine : Scheme.{u} :=
  Spec (.of k[X])

/-- The structure morphism `𝐀¹_k ⟶ Spec k`. -/
abbrev affineLineStructure : affineLine k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))

/-- The global functions on `𝐀¹_k` are the polynomials. -/
def affineLineGlobalSectionsEquiv : Γ(affineLine k, ⊤) ≃+* k[X] :=
  (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv

/-- The inverse of `Γ(𝐀¹_k) ≃ k[x]` is the inverse of `Γ(Spec R) ≅ R`. -/
theorem affineLineGlobalSectionsEquiv_symm_apply (f : k[X]) :
    (affineLineGlobalSectionsEquiv k).symm f = (Scheme.ΓSpecIso (.of k[X])).inv.hom f :=
  rfl

variable {k} {p : ℕ} [hp : Fact p.Prime] [CharP k p]

omit hp in
/-- `p` vanishes on `𝐀¹_k` when `k` has characteristic `p`. -/
theorem natCast_eq_zero_affineLine : (p : Γ(affineLine k, ⊤)) = 0 := by
  rw [← map_natCast (affineLineGlobalSectionsEquiv k).symm, CharP.cast_eq_zero, map_zero]

/-- `Γ(𝐀¹_k)` has characteristic `p` when `k` does. -/
instance : CharP Γ(affineLine k, ⊤) p :=
  charP_of_injective_ringHom (affineLineGlobalSectionsEquiv k).symm.injective p

variable (k p) [HasExt.{w} (Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The boundary `k[x] →+ H¹(𝐀¹_k, 𝐙/p𝐙)`** of the Artin–Schreier sequence on the affine
line. -/
def affineLineBoundary : k[X] →+ Sheaf.H.{w} (etaleConstantZMod (affineLine k) p) 1 :=
  (artinSchreierBoundary.{w} (affineLine k) hp.out natCast_eq_zero_affineLine).comp
    (affineLineGlobalSectionsEquiv k).symm.toAddMonoidHom

omit [HasExt.{w} (Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The Artin–Schreier map commutes with the ring isomorphism `Γ(𝐀¹_k) ≃ k[x]`. -/
theorem affineLineGlobalSectionsEquiv_symm_ringArtinSchreier (f : k[X]) :
    (affineLineGlobalSectionsEquiv k).symm (ringArtinSchreier k[X] p f) =
      ringArtinSchreier Γ(affineLine k, ⊤) p ((affineLineGlobalSectionsEquiv k).symm f) := by
  simp only [ringArtinSchreier_apply, map_sub, map_pow]

/-- **The exact sequence `k[x] ⟶ k[x] ⟶ H¹(𝐀¹_k, 𝐙/p𝐙) ⟶ 0`.** Let `k` be a field of
characteristic `p > 0`. The boundary of the Artin–Schreier sequence on the affine line is onto
`H¹(𝐀¹_k, 𝐙/p𝐙)` and its kernel is the image of `f ↦ f ^ p - f`.

The source states this for `k` algebraically closed; only the characteristic of `k` is needed. -/
@[stacks 0A47 "the exact sequence k[x] → k[x] → H¹(A¹_k, Z/p) → 0, first arrow f ↦ f^p - f"]
theorem exact_affineLineBoundary :
    Function.Exact (ringArtinSchreier k[X] p) (affineLineBoundary.{w} k p) ∧
      Function.Surjective (affineLineBoundary.{w} k p) := by
  refine ⟨fun f => ?_, ?_⟩
  · refine (exact_ringArtinSchreier_artinSchreierBoundary.{w} (affineLine k) hp.out
      natCast_eq_zero_affineLine ((affineLineGlobalSectionsEquiv k).symm f)).trans ?_
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨affineLineGlobalSectionsEquiv k g,
        (affineLineGlobalSectionsEquiv k).symm.injective ?_⟩
      rw [affineLineGlobalSectionsEquiv_symm_ringArtinSchreier, RingEquiv.symm_apply_apply, hg]
    · rintro ⟨g, rfl⟩
      exact ⟨_, (affineLineGlobalSectionsEquiv_symm_ringArtinSchreier k p g).symm⟩
  · intro c
    obtain ⟨a, ha⟩ := surjective_artinSchreierBoundary.{w} (affineLine k) hp.out
      natCast_eq_zero_affineLine c
    exact ⟨affineLineGlobalSectionsEquiv k a, by
      rw [affineLineBoundary, AddMonoidHom.comp_apply]
      exact (congrArg _ ((affineLineGlobalSectionsEquiv k).symm_apply_apply a)).trans ha⟩

/-- **The representatives, read in cohomology.** Let `k` be an algebraically closed field of
characteristic `p > 0`. Every class in `H¹(𝐀¹_k, 𝐙/p𝐙)` is the boundary of exactly one polynomial
`∑_{p ∤ n} λₙ xⁿ`. -/
@[stacks 0A47 "every class of H¹(A¹_k, Z/p) is the image of exactly one sum over p ∤ n of λ_n x^n"]
theorem existsUnique_affineLineBoundary_eq [IsAlgClosed k]
    (c : Sheaf.H.{w} (etaleConstantZMod (affineLine k) p) 1) :
    ∃! f : k[X], (∀ n, p ∣ n → f.coeff n = 0) ∧ affineLineBoundary.{w} k p f = c := by
  obtain ⟨hexact, hsurj⟩ := exact_affineLineBoundary.{w} k p
  obtain ⟨g, rfl⟩ := hsurj c
  obtain ⟨f, ⟨hf, hgf⟩, huniq⟩ := existsUnique_sub_mem_range_ringArtinSchreier (p := p) g
  have hδ : ∀ f', affineLineBoundary.{w} k p f' = affineLineBoundary.{w} k p g ↔
      g - f' ∈ (ringArtinSchreier k[X] p).range := fun f' => by
    rw [← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, neg_eq_zero]
    exact hexact (g - f')
  exact ⟨f, ⟨hf, (hδ f).2 hgf⟩, fun f' ⟨hf', h'⟩ => huniq f' ⟨hf', (hδ f').1 h'⟩⟩

end AffineLine

/-! ### Extension of the ground field -/

section ScalarExtension

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

attribute [local instance] Polynomial.algebra

/-- **The global functions on `𝐀¹_k ×_k k'` form the pushout of `k[x] ← k → k'`**, the two maps
into the pushout being the pullbacks of functions along the two projections. -/
theorem isPushout_scalarExtension_affineLine :
    IsPushout (CommRingCat.ofHom (algebraMap k k[X])) (CommRingCat.ofHom (algebraMap k k'))
      ((Scheme.ΓSpecIso (.of k[X])).inv ≫
        (scalarExtensionFst k k' (affineLineStructure k)).appTop)
      ((Scheme.ΓSpecIso (.of k')).inv ≫
        (scalarExtensionSnd k k' (affineLineStructure k)).appTop) :=
  (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback (affineLineStructure k)
    (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).of_iso
    (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _)
    (Scheme.ΓSpecIso_naturality _) (Scheme.ΓSpecIso_naturality _) (by simp) (by simp)

/-- **`Γ(𝐀¹_k ×_k k') ≅ k'[x]`**, the two pushouts of `k[x] ← k → k'` being identified. -/
def scalarExtensionAffineLineIso :
    Γ(scalarExtension k k' (affineLineStructure k), ⊤) ≅ CommRingCat.of k'[X] :=
  (isPushout_scalarExtension_affineLine k k').isoIsPushout _ _
    (CommRingCat.isPushout_of_isPushout k k[X] k' k'[X])

/-- `Γ(𝐀¹_k ×_k k') ≃ k'[x]` as a ring isomorphism. -/
def scalarExtensionAffineLineEquiv :
    Γ(scalarExtension k k' (affineLineStructure k), ⊤) ≃+* k'[X] :=
  (scalarExtensionAffineLineIso k k').commRingCatIsoToRingEquiv

/-- **The pullback of a polynomial to `𝐀¹_k ×_k k'` is its image in `k'[x]`.** -/
theorem scalarExtensionAffineLineEquiv_fst (f : k[X]) :
    scalarExtensionAffineLineEquiv k k'
        ((scalarExtensionFst k k' (affineLineStructure k)).appTop.hom
          ((affineLineGlobalSectionsEquiv k).symm f)) = f.map (algebraMap k k') :=
  ConcreteCategory.congr_hom (IsPushout.inl_isoIsPushout_hom _ _
    (isPushout_scalarExtension_affineLine k k')
    (CommRingCat.isPushout_of_isPushout k k[X] k' k'[X])) f

/-- **The pullback of a scalar `c ∈ k'` to `𝐀¹_k ×_k k'` is the constant polynomial `c`.** -/
theorem scalarExtensionAffineLineEquiv_snd (c : k') :
    scalarExtensionAffineLineEquiv k k'
        ((scalarExtensionSnd k k' (affineLineStructure k)).appTop.hom
          ((Scheme.ΓSpecIso (.of k')).inv.hom c)) = C c :=
  ConcreteCategory.congr_hom (IsPushout.inr_isoIsPushout_hom _ _
    (isPushout_scalarExtension_affineLine k k')
    (CommRingCat.isPushout_of_isPushout k k[X] k' k'[X])) c

variable {k k'} {p : ℕ} [hp : Fact p.Prime] [CharP k p]

/-- **The class of `μ x` over `k'` is not restricted from `k`.** Let `k` be algebraically closed of
characteristic `p` and `μ ∈ k'` not in `k`. For every `b ∈ k[x]`, the difference of the image of
`b` in `k'[x]` and `μ x` is not of the form `f ^ p - f`. -/
theorem not_sub_mem_range_ringArtinSchreier_map [IsAlgClosed k] {μ : k'}
    (hμ : μ ∉ Set.range (algebraMap k k')) (b : k[X]) :
    haveI : CharP k' p := charP_of_injective_algebraMap' k p
    b.map (algebraMap k k') - C μ * Polynomial.X ∉ (ringArtinSchreier k'[X] p).range := by
  have : CharP k' p := charP_of_injective_algebraMap' k p
  rintro ⟨u, hu⟩
  obtain ⟨f₀, ⟨hf₀, ⟨v, hv⟩⟩, -⟩ := existsUnique_sub_mem_range_ringArtinSchreier (p := p) b
  have hmap : ∀ g : k[X], (ringArtinSchreier k[X] p g).map (algebraMap k k') =
      ringArtinSchreier k'[X] p (g.map (algebraMap k k')) := fun g => by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  have hdiff :
      f₀.map (algebraMap k k') - C μ * Polynomial.X ∈ (ringArtinSchreier k'[X] p).range := by
    refine ⟨u - v.map (algebraMap k k'), ?_⟩
    rw [map_sub, hu, ← hmap, hv, Polynomial.map_sub]
    ring
  have hgood₁ : f₀.map (algebraMap k k') ∈ noCoeffPosDvdSubgroup k' p := fun n _ hn => by
    rw [coeff_map, hf₀ n hn, map_zero]
  have hgood₂ : C μ * Polynomial.X ∈ noCoeffPosDvdSubgroup k' p := fun n hn hpn => by
    rw [coeff_C_mul_X, if_neg]
    rintro rfl
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp hpn)
  have h1 := ((sub_mem_range_ringArtinSchreier_iff hgood₁ hgood₂).mp hdiff).1 1 one_ne_zero
  rw [coeff_map, coeff_C_mul_X, if_pos rfl] at h1
  exact hμ ⟨_, h1⟩

/-- **`H¹(𝐀¹_k, 𝐙/p𝐙) → H¹(𝐀¹_{k'}, 𝐙/p𝐙)` is not surjective.** Let `k` be an algebraically closed
field of characteristic `p > 0` and `k'/k` an extension with `k' ≠ k`. Then the restriction map
`H¹(𝐀¹_k, 𝐙/p𝐙) → H¹(𝐀¹_{k'}, 𝐙/p𝐙)` along `𝐀¹_{k'} ⟶ 𝐀¹_k` is not surjective — in particular not
an isomorphism: for `λ ∈ k' ∖ k` the class of `λ x` is not in its image.

The source takes `k'` algebraically closed; that is not used. -/
@[stacks 0A47 "H¹(A¹_k, Z/p) → H¹(A¹_{k'}, Z/p) is not surjective when k ⊊ k'"]
theorem not_surjective_etaleCohomologyRestrictionMap_affineLine [IsAlgClosed k]
    (hk : ¬ Function.Surjective (algebraMap k k'))
    [HasExt.{w} (Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k k' (affineLineStructure k)).smallEtaleTopology
      AddCommGrpCat.{u + 1})] :
    ¬ Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' (affineLineStructure k))
      (etaleConstantZMod (affineLine k) p) 1) := by
  intro hsurj
  obtain ⟨μ, hμ⟩ : ∃ μ : k', μ ∉ Set.range (algebraMap k k') := not_forall.mp hk
  have : CharP k' p := charP_of_injective_algebraMap' k p
  let g := scalarExtensionFst k k' (affineLineStructure k)
  let e := scalarExtensionAffineLineEquiv k k'
  have hX : (p : Γ(affineLine k, ⊤)) = 0 := natCast_eq_zero_affineLine
  have hX' : (p : Γ(scalarExtension k k' (affineLineStructure k), ⊤)) = 0 :=
    natCast_eq_zero_of_hom g hX
  have : CharP Γ(scalarExtension k k' (affineLineStructure k), ⊤) p :=
    charP_of_injective_ringHom e.symm.injective p
  let ι := (etaleAbelianInverseImageConstantIso.{u, 0} g).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))
  obtain ⟨c, hc⟩ := hsurj ((Stacks.Cohomology.CoefficientLift.sheafHIsoCongr ι 1).symm
    (artinSchreierBoundary.{w} _ hp.out hX' (e.symm (C μ * Polynomial.X))))
  obtain ⟨b, rfl⟩ := surjective_artinSchreierBoundary.{w} (affineLine k) hp.out hX c
  have hnat :=
    sheafHIsoCongr_etaleCohomologyRestrictionMap_artinSchreierBoundary.{w} g hp.out hX hX' b
  rw [hc, AddEquiv.apply_symm_apply] at hnat
  have hker : artinSchreierBoundary.{w} _ hp.out hX'
      (g.appTop.hom b - e.symm (C μ * Polynomial.X)) = 0 := by
    rw [map_sub, hnat, sub_self]
  obtain ⟨u, hu⟩ := (exact_ringArtinSchreier_artinSchreierBoundary.{w} _ hp.out hX' _).mp hker
  apply not_sub_mem_range_ringArtinSchreier_map (p := p) hμ (affineLineGlobalSectionsEquiv k b)
  refine ⟨e u, ?_⟩
  have hb : e (g.appTop.hom b) = (affineLineGlobalSectionsEquiv k b).map (algebraMap k k') := by
    rw [← scalarExtensionAffineLineEquiv_fst, RingEquiv.symm_apply_apply]
  rw [← hb, ← RingEquiv.apply_symm_apply e (C μ * Polynomial.X), ← map_sub, ← hu]
  simp only [ringArtinSchreier_apply, map_sub, map_pow]

omit [CharP k p] in
variable (k) in
/-- An algebraic closure of `k(t)` is a proper extension of `k`: it contains `t`. -/
theorem not_surjective_algebraMap_algebraicClosure_ratFunc :
    ¬ Function.Surjective (algebraMap k (AlgebraicClosure (RatFunc k))) := by
  intro hsurj
  obtain ⟨c, hc⟩ := hsurj (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) RatFunc.X)
  rw [IsScalarTower.algebraMap_apply k (RatFunc k)] at hc
  have h1 := (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).injective hc
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k), ← RatFunc.algebraMap_X] at h1
  exact Polynomial.X_ne_C c (IsFractionRing.injective k[X] (RatFunc k) h1).symm

/-- **The restriction map is not an isomorphism in general.** For every algebraically closed field
`k` of characteristic `p > 0` there is an algebraically closed extension `k'/k` — an algebraic
closure of `k(t)` — for which `H¹(𝐀¹_k, 𝐙/p𝐙) → H¹(𝐀¹_{k'}, 𝐙/p𝐙)` is not an isomorphism. -/
@[stacks 0A47 "so H¹(A¹_k, Z/p) → H¹(A¹_{k'}, Z/p) is not an isomorphism in general"]
theorem exists_not_bijective_etaleCohomologyRestrictionMap_affineLine [IsAlgClosed k] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : IsAlgClosed k'),
      ∀ [HasExt.{w} (Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1})]
        [HasExt.{w} (Sheaf (scalarExtension k k' (affineLineStructure k)).smallEtaleTopology
          AddCommGrpCat.{u + 1})],
        ¬ Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w}
          (scalarExtensionFst k k' (affineLineStructure k))
          (etaleConstantZMod (affineLine k) p) 1) :=
  ⟨AlgebraicClosure (RatFunc k), inferInstance, inferInstance, inferInstance,
    fun h => not_surjective_etaleCohomologyRestrictionMap_affineLine
      (not_surjective_algebraMap_algebraicClosure_ratFunc k) h.2⟩

end ScalarExtension

/-! ### Coefficients prime to the characteristic -/

section PrimeToCharacteristic

variable (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [Algebra k k'] [IsAlgClosed k']

/-- The affine line over an algebraically closed field, with the constant sheaf `𝐙/n𝐙`, is an
instance of Situation 0A52. -/
abbrev affineLineTorsionSheafSituation {n : ℕ} (hn : n ≠ 0) : TorsionSheafSituation.{u, v} where
  k := k
  X := affineLine k
  structureMorphism := affineLineStructure k
  isSeparated := inferInstance
  locallyOfFiniteType := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  quasiCompact := inferInstance
  dimension_le_one := (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim k[X]).trans_le (by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add])
  F := (constantSheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))
  isTorsion := fun U x => by
    obtain ⟨R, hR, hRx⟩ := exists_sieve_nsmul_eq_zero_constantSheaf
      (affineLine k).smallEtaleTopology n (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))
      (fun z => ULift.ext (by simp)) U x
    exact ⟨R, hR, fun V f hf => ⟨n, Nat.pos_of_ne_zero hn, hRx V f hf⟩⟩

/-- **The phenomenon only occurs with `p`-power torsion coefficients.** Let `k'/k` be an
extension of algebraically closed fields and let `n` be invertible in `k`. Then
`H^q(𝐀¹_k, 𝐙/n𝐙) → H^q(𝐀¹_{k'}, 𝐙/n𝐙)` is bijective in every degree `q`: this is statement (6)
of Situation 0A52 (Tag 0A58) for the affine line. In characteristic `0` every `n ≥ 1` is
invertible, so the base change map is an isomorphism for every finite cyclic coefficient group. -/
@[stacks 0A47 "only in characteristic p with p-power torsion: bijective for Z/n, n invertible in k"]
theorem bijective_etaleCohomologyRestrictionMap_affineLine_of_isUnit {n : ℕ} (hn : IsUnit (n : k))
    [HasExt.{w} (Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (scalarExtension k k' (affineLineStructure k)).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})] (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
      (scalarExtensionFst k k' (affineLineStructure k))
      ((constantSheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))) q) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  let S : TorsionSheafSituation.{u, v} := affineLineTorsionSheafSituation k hn0
  have key : ∀ r, ExpChar k r → n.Coprime r := by
    intro r hr
    cases hr with
    | zero => exact Nat.coprime_one_right n
    | prime hprime =>
      refine Nat.coprime_comm.mp ((Nat.coprime_or_dvd_of_prime hprime n).resolve_right fun hd => ?_)
      rw [(CharP.cast_eq_zero_iff k _ n).mpr hd] at hn
      exact not_isUnit_zero hn
  have hcop : n.Coprime (ringExpChar k) := key _ inferInstance
  have htors : Stacks.Torsion.IsPrimeToCharacteristicTorsion S.X.smallEtaleTopology
      (ringExpChar S.k) S.F := fun U x => by
    obtain ⟨R, hR, hRx⟩ := exists_sieve_nsmul_eq_zero_constantSheaf
      (affineLine k).smallEtaleTopology n (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod n)))
      (fun z => ULift.ext (by simp)) U x
    exact ⟨R, hR, fun V f hf => ⟨n, Nat.pos_of_ne_zero hn0, hcop, hRx V f hf⟩⟩
  exact TorsionSheafSituation.baseChangePrimeToCharacteristic.{w, v, u} S htors k' q

end PrimeToCharacteristic

end Stacks.ArtinSchreier

end
