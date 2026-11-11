module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.AffineOpenImmersion
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod

/-!
# The affine open-immersion criterion is not a local property of ring maps

The principal-localization criterion `RingHom.IsOpenImmersion` fails the third locality
condition of `RingHom.StacksPropertyIsLocal`: it does not descend from a finite principal
open cover of the target. The diagonal `k → k × k` of a field is the witness. Its two
principal localizations `k → (k × k)_{(1,0)}` and `k → (k × k)_{(0,1)}` are bijective, hence
satisfy the criterion, and `(1,0)` together with `(0,1)` generate the unit ideal; but the
diagonal itself does not satisfy the criterion, since an element of `k` not carried into a
prime of `k × k` is a unit, and localizing at a unit would make `k` and `k × k` isomorphic.

The other two locality conditions do hold, so the failure is confined to the third: condition
(1)(a) follows from stability under base change and condition (1)(b) from stability under
composition together with the criterion for a principal localization map.

## Main results

* `RingHom.isOpenImmersion_of_bijective` states that a bijective ring map satisfies the
  criterion.
* `RingHom.isOpenImmersion_algebraMap_away` states that a principal localization map satisfies
  the criterion.
* `RingHom.isOpenImmersion_localizationAwayPreserves` is locality condition (1)(a).
* `RingHom.isOpenImmersion_compPrincipalLocalizations` is locality condition (1)(b).
* `RingHom.not_ofLocalizationFiniteSpanTarget_isOpenImmersion` states that the criterion does
  not descend from a finite principal open cover of the target, which is locality condition
  (1)(c).
* `RingHom.not_stacksPropertyIsLocal_isOpenImmersion` states that the criterion is not a local
  property of ring maps.

## Implementation notes

The witness field is `ULift (ZMod 2)`, chosen so that the statement is refuted in every
universe. Nothing about the field is used beyond its having no idempotents other than `0`
and `1`.

Geometrically the failure is the standard one: an open immersion of affine schemes is not
detected on a cover of the source, `Spec (k × k) → Spec k` being a local isomorphism without
being injective.

Consequently part (2) of Tag 01SX is false as stated. The tag is carried here on the
refutation `RingHom.not_stacksPropertyIsLocal_isOpenImmersion` and on the three locality
conditions separately: the two that hold and the one that fails. The corrected form of part (2),
in which the localization of the target is taken at an element of the target, is the local
isomorphism property `Algebra.IsLocalIso`, and `RingHom.stacksPropertyIsLocal_isLocalIso`
(in `StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.LocalIso`) proves it local.

## References

* [Stacks Project, Tag 01SR](https://stacks.math.columbia.edu/tag/01SR)
* [Stacks Project, Tag 01SX](https://stacks.math.columbia.edu/tag/01SX)
-/

@[expose] public section

universe u

namespace RingHom

/-- Localizing away from a unit does not change the ring. -/
private theorem bijective_algebraMap_of_isUnit {T C : Type u} [CommRing T] [CommRing C]
    (t : T) (ht : IsUnit t) [Algebra T C] [IsLocalization.Away t C] :
    Function.Bijective (algebraMap T C) := by
  have e := IsLocalization.atUnit T C t ht
  have hcoe : ⇑e = algebraMap T C := by
    funext x
    simpa using e.commutes x
  rw [← hcoe]
  exact e.bijective

/-- For a bijective ring map the unit of the source witnesses the affine open-immersion
criterion at every prime. -/
private theorem away_one_of_bijective {R T : Type u} [CommRing R] [CommRing T]
    (θ : R →+* T) (hθ : Function.Bijective θ) (C : Type u) [CommRing C] [Algebra T C]
    [IsLocalization.Away (θ 1) C] :
    letI : Algebra R C := ((algebraMap T C).comp θ).toAlgebra
    IsLocalization.Away (1 : R) C := by
  let : Algebra R C := ((algebraMap T C).comp θ).toAlgebra
  refine IsLocalization.away_of_isUnit_of_bijective _ isUnit_one ?_
  simpa [RingHom.algebraMap_toAlgebra] using
    (bijective_algebraMap_of_isUnit (θ 1) (isUnit_one.map θ)).comp hθ

/-- A bijective homomorphism of commutative rings satisfies the affine open-immersion
criterion. -/
theorem isOpenImmersion_of_bijective {R T : Type u} [CommRing R] [CommRing T]
    (θ : R →+* T) (hθ : Function.Bijective θ) : θ.IsOpenImmersion := by
  intro q hq
  exact ⟨1, by simpa using hq.one_notMem, away_one_of_bijective θ hθ _⟩

/-- A localization that is carried isomorphically onto a further ring is a localization of the
base at the same element. -/
private theorem away_of_bijective_algebraMap {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] (x : R) [IsLocalization.Away x S] [Algebra S T]
    (hb : Function.Bijective (algebraMap S T)) :
    letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    IsLocalization.Away x T := by
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  let F : S →ₐ[R] T := { toRingHom := algebraMap S T, commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers x)
    (AlgEquiv.ofBijective F hb)

/-- A principal localization map of commutative rings satisfies the affine open-immersion
criterion, the localized element itself being the witness at every prime. -/
theorem isOpenImmersion_algebraMap_away {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] : (algebraMap R S).IsOpenImmersion := by
  intro q hq
  refine ⟨r, Ideal.notMem_of_isUnit q (IsLocalization.Away.algebraMap_isUnit r), ?_⟩
  exact away_of_bijective_algebraMap r
    (bijective_algebraMap_of_isUnit _ (IsLocalization.Away.algebraMap_isUnit r))

/-- Locality condition (1)(a): the affine open-immersion criterion is preserved by
simultaneous principal localization. This is base change along `R → R_r`. -/
@[stacks 01SX "part (2) (open immersion) as printed: locality condition (1)(a) of 01SR holds \
for the criterion R_f → A_f, which is preserved by simultaneous principal localization"]
theorem isOpenImmersion_localizationAwayPreserves :
    RingHom.LocalizationAwayPreserves
      (fun {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) ↦ φ.IsOpenImmersion) :=
  isOpenImmersion_isStableUnderBaseChange.localizationPreserves.away

/-- Locality condition (1)(b): if `R_f → A` satisfies the affine open-immersion criterion then
so does the induced composite `R → A_a`. -/
@[stacks 01SX "part (2) (open immersion) as printed: locality condition (1)(b) of 01SR holds \
for the criterion R_f → A_f, `P (R_f → A) ⟹ P (R → A_a)`"]
theorem isOpenImmersion_compPrincipalLocalizations
    {R A Rf Aa : Type u} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Aa] (f : R) (a : A)
    [Algebra R Rf] [IsLocalization.Away f Rf] [Algebra A Aa] [IsLocalization.Away a Aa]
    (g : Rf →+* A) (hg : g.IsOpenImmersion) :
    ((algebraMap A Aa).comp (g.comp (algebraMap R Rf))).IsOpenImmersion :=
  isOpenImmersion_stableUnderComposition _ _
    (isOpenImmersion_stableUnderComposition _ _ (isOpenImmersion_algebraMap_away f) hg)
    (isOpenImmersion_algebraMap_away a)

/-- The diagonal homomorphism of a commutative ring into its square. -/
private def diag (k : Type u) [CommRing k] : k →+* k × k :=
  (RingHom.id k).prod (RingHom.id k)

@[simp]
private lemma diag_apply {k : Type u} [CommRing k] (x : k) : diag k x = (x, x) := rfl

/-- Composing the diagonal with the localization away from an idempotent that a ring
projection carries to `1` gives a bijection. -/
private lemma bijective_awayDiag {k : Type u} [CommRing k] (e : k × k) (p : k × k →+* k)
    (he : IsIdempotentElem e) (hpe : p e = 1) (hp : ∀ x : k, p (x, x) = x)
    (hez : ∀ z : k × k, e * z = e * (p z, p z)) :
    Function.Bijective ((algebraMap (k × k) (Localization.Away e)).comp (diag k)) := by
  constructor
  · intro x y hxy
    rw [RingHom.comp_apply, RingHom.comp_apply, diag_apply, diag_apply,
      IsLocalization.eq_iff_exists (Submonoid.powers e) (Localization.Away e)] at hxy
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := hxy
    simpa [hpe, hp] using congrArg p hc
  · intro t
    obtain ⟨z, rfl⟩ :=
      IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he t
    refine ⟨p z, ?_⟩
    rw [RingHom.comp_apply, diag_apply,
      IsLocalization.eq_iff_exists (Submonoid.powers e) (Localization.Away e)]
    exact ⟨⟨e, Submonoid.mem_powers e⟩, (hez z).symm⟩

private lemma bijective_awayDiag_fst {k : Type u} [CommRing k] :
    Function.Bijective
      ((algebraMap (k × k) (Localization.Away ((1 : k), (0 : k)))).comp (diag k)) :=
  bijective_awayDiag _ (RingHom.fst k k) (by simp [IsIdempotentElem])
    (by simp) (by simp) fun ⟨a, b⟩ => by simp

private lemma bijective_awayDiag_snd {k : Type u} [CommRing k] :
    Function.Bijective
      ((algebraMap (k × k) (Localization.Away ((0 : k), (1 : k)))).comp (diag k)) :=
  bijective_awayDiag _ (RingHom.snd k k) (by simp [IsIdempotentElem])
    (by simp) (by simp) fun ⟨a, b⟩ => by simp

/-- The two coordinate idempotents generate the unit ideal of a square. -/
private lemma span_pair_eq_top (k : Type u) [CommRing k] :
    Ideal.span ({((1 : k), (0 : k)), ((0 : k), (1 : k))} : Set (k × k)) = ⊤ := by
  rw [Ideal.eq_top_iff_one,
    show (1 : k × k) = ((1 : k), (0 : k)) + ((0 : k), (1 : k)) by simp [Prod.ext_iff]]
  exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))

/-- Descent from a finite principal open cover of the target would make the diagonal of a
commutative ring satisfy the affine open-immersion criterion. -/
private lemma isOpenImmersion_diag_of_ofLocalizationFiniteSpanTarget (k : Type u) [CommRing k]
    (h : RingHom.OfLocalizationFiniteSpanTarget
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦ φ.IsOpenImmersion)) :
    (diag k).IsOpenImmersion := by
  classical
  refine h (diag k) {((1 : k), (0 : k)), ((0 : k), (1 : k))} ?_ ?_
  · simpa using span_pair_eq_top k
  · rintro ⟨r, hr⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact isOpenImmersion_of_bijective _ bijective_awayDiag_fst
    · exact isOpenImmersion_of_bijective _ bijective_awayDiag_snd

/-- The diagonal of a field does not satisfy the affine open-immersion criterion. -/
private lemma not_isOpenImmersion_diag (k : Type u) [Field k] : ¬ (diag k).IsOpenImmersion := by
  intro h
  have : ((⊥ : Ideal k).comap (RingHom.fst k k)).IsPrime := Ideal.IsPrime.comap _
  obtain ⟨f, hf, hloc⟩ := h ((⊥ : Ideal k).comap (RingHom.fst k k))
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (by simp [Ideal.mem_comap])
  have hfu : IsUnit f := hf0.isUnit
  let : Algebra k (Localization.Away (diag k f)) :=
    ((algebraMap (k × k) (Localization.Away (diag k f))).comp (diag k)).toAlgebra
  have : IsLocalization.Away f (Localization.Away (diag k f)) := hloc
  have e₁ : k ≃ₐ[k] Localization.Away (diag k f) := IsLocalization.atUnit k _ f hfu
  have e₂ : (k × k) ≃ₐ[k × k] Localization.Away (diag k f) :=
    IsLocalization.atUnit (k × k) _ (diag k f) (hfu.map (diag k))
  let E : k ≃+* k × k := e₁.toRingEquiv.trans e₂.toRingEquiv.symm
  have hidem : E.symm ((1 : k), (0 : k)) * E.symm ((1 : k), (0 : k))
      = E.symm ((1 : k), (0 : k)) := by
    rw [← map_mul]
    congr 1
    simp
  rcases mul_eq_zero.mp
      (show E.symm ((1 : k), (0 : k)) * (E.symm ((1 : k), (0 : k)) - 1) = 0 by
        linear_combination hidem) with h0 | h1
  · simpa using congrArg E h0
  · simpa using congrArg E (sub_eq_zero.mp h1)

/-- The affine open-immersion criterion does not descend from a finite principal open cover of
the target: this is the third locality condition of `RingHom.StacksPropertyIsLocal`. -/
@[stacks 01SX "part (2) (open immersion) as printed: locality condition (1)(c) of 01SR fails \
for the criterion R_f → A_f, the witness being the diagonal `k → k × k` of a field, whose two \
localizations at the coordinate idempotents are bijective while the diagonal itself is not a \
principal localization"]
theorem not_ofLocalizationFiniteSpanTarget_isOpenImmersion :
    ¬ RingHom.OfLocalizationFiniteSpanTarget
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦ φ.IsOpenImmersion) :=
  fun h => not_isOpenImmersion_diag (ULift.{u} (ZMod 2))
    (isOpenImmersion_diag_of_ofLocalizationFiniteSpanTarget (ULift.{u} (ZMod 2)) h)

/-- The affine open-immersion criterion is not a local property of commutative-ring
homomorphisms. -/
@[stacks 01SX "refutation of part (2) (open immersion): the criterion is NOT a local property \
of ring maps, so part (2) is false as stated: conditions (1)(a) and (1)(b) of 01SR hold \
(isOpenImmersion_localizationAwayPreserves, isOpenImmersion_compPrincipalLocalizations) and \
(1)(c) fails (not_ofLocalizationFiniteSpanTarget_isOpenImmersion). The corrected part (2), with \
R_f → A_a for some a ∉ 𝔮, is local: stacksPropertyIsLocal_isLocalIso. Parts (1), (3), (4) \
and (5) are carried in LocalRingIso, ReducedFibers, FiberDimension and NoetherianTarget"]
theorem not_stacksPropertyIsLocal_isOpenImmersion :
    ¬ RingHom.StacksPropertyIsLocal
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦ φ.IsOpenImmersion) :=
  fun h => not_ofLocalizationFiniteSpanTarget_isOpenImmersion h.ofLocalizationFiniteSpanTarget

end RingHom
