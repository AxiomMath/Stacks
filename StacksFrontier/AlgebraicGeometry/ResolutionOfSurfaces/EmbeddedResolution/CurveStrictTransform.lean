module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.UniversalProperty
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.IntersectionMultiplicity
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksFrontier.AlgebraicGeometry.F6Rank89.StalkDimension

/-!
# Blowing up two curves meeting at a point

When an integral curve is regular at a closed intersection point, blowing up the ambient scheme
at that point leaves the curve unchanged. Its strict transform meets the exceptional fibre
transversely at one point, and any remaining intersection with the other strict transform has
smaller multiplicity.

## Main definitions

* `AlgebraicGeometry.centerIdeal` is the reduced closed point used as the blowup centre.
* `AlgebraicGeometry.transformIdeal` is the ideal of a strict transform in the blown-up ambient
  scheme.

## Main results

* `AlgebraicGeometry.strictTransformToCurve_isIso` gives the isomorphism onto the regular curve.
* `AlgebraicGeometry.strictTransform_exceptional_unique` gives the unique exceptional point.
* `AlgebraicGeometry.strictTransform_exceptional_multiplicity_one` computes its multiplicity.
* `AlgebraicGeometry.strictTransform_intersectionMultiplicity_lt` gives the decrease in
  intersection multiplicity.

## Implementation notes

The strict transform is first constructed in the pullback of the blowup to the original closed
subscheme. Its composite closed immersion into the ambient blowup determines
`AlgebraicGeometry.transformIdeal`. Multiplicities are written as natural-valued lengths of the
relevant intersection local rings, as in
`AlgebraicGeometry.IntersectionMultiplicityContext.intersectionMultiplicity`.

Three blocks of `private` lemmas stand in for tags that are not yet formalized: the two instances of
[Stacks, Tag 080E] that the argument consumes, and the clause of [Stacks, Tag 0AG8] saying that
a stalkwise regular principal generator makes a closed subscheme an effective Cartier divisor.
Each block carries a note saying which tag it stands in for and that it is to be deleted once
that tag is formalized.

## References

* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

/-- The reduced closed point at which the ambient scheme is blown up. -/
public def centerIdeal {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩

/-! ### Stand-in for [Stacks, Tag 080E], first instance

The lemmas of this block are a **stand-in for [Stacks, Tag 080E]** in the instance used below:
if the inverse image of the centre is already an effective Cartier divisor, the strict
transform projects isomorphically onto its source. The block is to be deleted once tag 080E is
formalized, in favour of the tagged statement.
-/

/-- The whole scheme, as an open subscheme of itself, is scheme-theoretically dense. -/
private theorem isSchemeTheoreticallyDense_top {Z : Scheme.{u}} :
    Scheme.Opens.IsSchemeTheoreticallyDense (⊤ : Z.Opens) := by
  intro V
  rw [show V.ι ⁻¹ᵁ (⊤ : Z.Opens) = ⊤ from by simp]
  have : IsIso (⊤ : V.toScheme.Opens).ι := (Scheme.topIso V.toScheme).isIso_hom
  infer_instance

/-- If the inverse image of an open `U` along `h` is scheme-theoretically dense in the source,
then every section vanishing on `U` is killed by `h`: the kernel ideal sheaf of the inclusion of
`U` is contained in the kernel ideal sheaf of `h`. -/
private theorem ker_ι_le_ker_of_isSchemeTheoreticallyDense {A B : Scheme.{u}} (h : A ⟶ B)
    (U : B.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense (h ⁻¹ᵁ U)) :
    U.ι.ker ≤ h.ker := by
  have hdom : IsSchemeTheoreticallyDominant (h ⁻¹ᵁ U).ι :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense _ hU
  calc U.ι.ker ≤ (h ∣_ U ≫ U.ι).ker := Scheme.Hom.le_ker_comp _ _
    _ = ((h ⁻¹ᵁ U).ι ≫ h).ker := by rw [morphismRestrict_ι]
    _ = h.ker := by rw [Scheme.Hom.ker_comp, hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- **The geometric content of Stacks tags 0807 and 080E.** Let `b : X' ⟶ X` be separated and an
isomorphism over an open `V` of `X`, and let `g : C ⟶ X'` be a morphism whose inverse image of
`V` is scheme-theoretically dense in `C`. Then the closed subscheme of `C ×_X X'` cut out by the
sections of the structure sheaf vanishing on the inverse image `W` of `V` is carried
isomorphically onto `C` by the projection.

For `b` the blowup of `X` in `ℐ` and `V` the complement of the centre, `W` is the complement of
the inverse image of the exceptional divisor and the hypotheses on `g` say that `g` is a
morphism over `X` whose source carries the inverse image of the centre as an effective Cartier
divisor; the conclusion is then that the strict transform of `C` is `C`. -/
private theorem isIso_subschemeι_comp_fst {X Bl C : Scheme.{u}} (b : Bl ⟶ X) [IsSeparated b]
    (V : X.Opens) [IsIso (b ∣_ V)] (g : C ⟶ Bl)
    (W : (pullback (g ≫ b) b).Opens) (K : (pullback (g ≫ b) b).IdealSheafData)
    (hW : W = (pullback.fst (g ≫ b) b ≫ (g ≫ b)) ⁻¹ᵁ V)
    (hK : K = (Scheme.Opens.ι W).ker)
    (hdense : Scheme.Opens.IsSchemeTheoreticallyDense ((g ≫ b) ⁻¹ᵁ V)) :
    IsIso (K.subschemeι ≫ pullback.fst (g ≫ b) b) := by
  obtain ⟨s, hfst, hsnd, hs⟩ : ∃ s : C ⟶ pullback (g ≫ b) b,
      s ≫ pullback.fst (g ≫ b) b = 𝟙 C ∧ s ≫ pullback.snd (g ≫ b) b = g ∧
        IsClosedImmersion s :=
    ⟨pullback.lift (𝟙 C) g (Category.id_comp (g ≫ b)), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, inferInstance⟩
  have hpre : s ⁻¹ᵁ W = (g ≫ b) ⁻¹ᵁ V := by
    rw [hW, ← Scheme.Hom.comp_preimage, ← Category.assoc, hfst, Category.id_comp]
  have hdenseC : Scheme.Opens.IsSchemeTheoreticallyDense (s ⁻¹ᵁ W) := by
    rwa [hpre]
  have hAle : (Scheme.Opens.ι W).ker ≤ s.ker :=
    ker_ι_le_ker_of_isSchemeTheoreticallyDense s W hdenseC
  have hdenseW : Scheme.Opens.IsSchemeTheoreticallyDense
      ((Scheme.Opens.ι W ≫ pullback.fst (g ≫ b) b ≫ (g ≫ b)) ⁻¹ᵁ V) := by
    rw [Scheme.Hom.comp_preimage, ← hW, Scheme.Opens.ι_preimage_self]
    exact isSchemeTheoreticallyDense_top
  have hWfac : (Scheme.Opens.ι W ≫ pullback.fst (g ≫ b) b) ≫ s = Scheme.Opens.ι W := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, Category.comp_id]
    · rw [Category.assoc, hsnd]
      exact Stacks.Blowup.eq_of_comp_eq b hdenseW _ _ (by simp) (by simp [pullback.condition])
  have hBle : s.ker ≤ (Scheme.Opens.ι W).ker :=
    calc s.ker ≤ ((Scheme.Opens.ι W ≫ pullback.fst (g ≫ b) b) ≫ s).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = (Scheme.Opens.ι W).ker := by rw [hWfac]
  have hks : K = s.ker := hK.trans (le_antisymm hAle hBle)
  have hle : K.subschemeι.ker ≤ s.ker :=
    le_of_eq (by rw [Scheme.IdealSheafData.ker_subschemeι, hks])
  have ht : IsClosedImmersion.lift K.subschemeι s hle ≫ K.subschemeι = s :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift K.subschemeι s hle) :=
    IsClosedImmersion.isIso_of_ker_eq s K.subschemeι _ ht
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hks])
  have hcomp : IsClosedImmersion.lift K.subschemeι s hle ≫
      (K.subschemeι ≫ pullback.fst (g ≫ b) b) = 𝟙 C := by
    rw [← Category.assoc, ht, hfst]
  rw [← IsIso.inv_eq_of_hom_inv_id hcomp]
  infer_instance

/-- **Stacks Project, Tags 0807 and 080E** for `AlgebraicGeometry.blowUpToBase`, the
construction of the blowup that carries the universal property.

If the inverse image of the centre is already an effective Cartier divisor on `C`, then the
closed subscheme of `C ×_X X'` cut out by the sections vanishing off the inverse image of the
complement of the centre — which is what `Stacks.Blowup.strictTransformIdeal_eq_ker` says the
defining ideal of the strict transform is — is carried isomorphically onto `C` by the
projection. No hypothesis beyond the effective Cartier divisor is needed. -/
@[sga "7 X 2.6" "special case"]
private theorem isIso_subschemeι_ker_comp_fst {X C : Scheme.{u}} (f : C ⟶ X) (J : X.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap f)) :
    IsIso ((Scheme.Opens.ι ((pullback.fst f (AlgebraicGeometry.blowUpToBase J) ≫ f) ⁻¹ᵁ
        J.support.compl)).ker.subschemeι ≫
      pullback.fst f (AlgebraicGeometry.blowUpToBase J)) := by
  have : IsSeparated (AlgebraicGeometry.blowUpToBase J) :=
    Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase _
  obtain ⟨g, hgf⟩ := Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor J f hJ
  subst hgf
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense
      ((g ≫ AlgebraicGeometry.blowUpToBase J) ⁻¹ᵁ J.support.compl) := by
    rw [Stacks.Blowup.preimage_compl_support]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _ hJ
  exact isIso_subschemeι_comp_fst (AlgebraicGeometry.blowUpToBase J) J.support.compl g _ _ rfl
    rfl hdense

/-! ### Stand-in for [Stacks, Tag 080E], second instance

The lemmas of this block are a **stand-in for [Stacks, Tag 080E]** in the second instance used
below: the inverse image of the exceptional divisor on the strict transform is an effective
Cartier divisor. They prove it directly, without producing the isomorphism of the strict
transform with a blowup. DELETE THIS BLOCK when tag 080E lands.
-/

/-- The complement of the support of an inverse-image ideal sheaf is the inverse image of the
complement of the support. -/
private theorem support_compl_comap {A B : Scheme.{u}} (Ev : B.IdealSheafData) (m : A ⟶ B) :
    (Ev.comap m).support.compl = m ⁻¹ᵁ Ev.support.compl := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- **A locally principal closed subscheme whose complement receives a dominant morphism is an
effective Cartier divisor.**

More precisely, let `J` be a locally principal ideal sheaf on `T` and let `q : A ⟶ T` be a
quasi-compact scheme-theoretically dominant morphism whose source lies entirely over the
complement of the support of `J`. Then `J` is an effective Cartier divisor.

On an affine open `U` on which `J` is generated by `a`, the basic open `D(a)` is exactly
`U ∩ (T ∖ Supp J)`, so `q^{-1}(D(a)) = q^{-1}(U)`; a section killed by `a` therefore pulls back
to zero along `q`, and dominance makes it zero. -/
private theorem isEffectiveCartierDivisor_of_isLocallyPrincipal_of_preimage_compl_eq_top
    {T A : Scheme.{u}} (J : T.IdealSheafData) (hJ : Stacks.Divisors.IsLocallyPrincipal J)
    (q : A ⟶ T)
    [IsSchemeTheoreticallyDominant q] [QuasiCompact q]
    (hq : q ⁻¹ᵁ J.support.compl = ⊤) :
    Stacks.Divisors.IsEffectiveCartierDivisor J := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_mem_support J fun x _ ↦ ?_
  obtain ⟨U, hxU, a, ha⟩ := hJ x
  have hbo : T.basicOpen a = U.1 ⊓ J.support.compl :=
    Stacks.Divisors.basicOpen_eq_inf_compl_support_of_ideal_eq_span J U a ha
  have hpre : q ⁻¹ᵁ T.basicOpen a = q ⁻¹ᵁ U.1 := by
    rw [hbo, Scheme.Hom.preimage_inf, hq, inf_top_eq]
  have hle : q ⁻¹ᵁ U.1 ≤ q ⁻¹ᵁ T.basicOpen a := le_of_eq hpre.symm
  have hfac : T.presheaf.map (homOfLE (T.basicOpen_le a)).op ≫
      q.appLE (T.basicOpen a) (q ⁻¹ᵁ U.1) hle = q.app U.1 := by
    rw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.appLE_eq_app q
  have key : ∀ c : Γ(T, U.1), c * a = 0 → c = 0 := by
    intro c hc
    have hres : (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom c = 0 := by
      have hu : IsUnit ((T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom a) :=
        T.toRingedSpace.isUnit_res_basicOpen a
      have hmul : (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom c *
          (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom a = 0 := by
        rw [← map_mul, hc, map_zero]
      exact hu.mul_left_eq_zero.mp hmul
    have hzero : (q.app U.1).hom c = 0 := by
      rw [← hfac, CommRingCat.comp_apply, hres, map_zero]
    refine q.app_injective U.1 ?_
    rw [map_zero]
    exact hzero
  refine ⟨U, a, hxU, ha, mem_nonZeroDivisors_iff.mpr ⟨fun c hc ↦ key c ?_, key⟩⟩
  rwa [mul_comm]

/-- **The inverse image of a locally principal closed subscheme on a strict transform is an
effective Cartier divisor.**

Let `pr : Y ⟶ S'` be a morphism of schemes and let `Ev` be a locally principal ideal sheaf on
`S'`. Let `K` be the kernel ideal sheaf of the inclusion of `pr^{-1}(S' ∖ Supp Ev)` into `Y`,
that is, the defining ideal of the strict transform. Then the inverse image of `Ev` along the
composite of the closed immersion of the strict transform with `pr` is an effective Cartier
divisor.

The ideal sheaf is taken as a variable together with the equation identifying it with that
kernel, so that the result can be applied to `Stacks.StrictTransform.ideal` through
`Stacks.StrictTransform.ideal_eq_ker_ι` without rewriting inside a dependent type. -/
private theorem isEffectiveCartierDivisor_comap_subschemeι_comp {Y S' : Scheme.{u}} (pr : Y ⟶ S')
    (Ev : S'.IdealSheafData) (hEv : Stacks.Divisors.IsLocallyPrincipal Ev)
    [QuasiCompact (Scheme.Opens.ι (pr ⁻¹ᵁ Ev.support.compl))] (K : Y.IdealSheafData)
    (hK : K = (Scheme.Opens.ι (pr ⁻¹ᵁ Ev.support.compl)).ker) :
    Stacks.Divisors.IsEffectiveCartierDivisor (Ev.comap (K.subschemeι ≫ pr)) := by
  subst hK
  have := isSchemeTheoreticallyDominant_toImage (Scheme.Opens.ι (pr ⁻¹ᵁ Ev.support.compl))
  refine isEffectiveCartierDivisor_of_isLocallyPrincipal_of_preimage_compl_eq_top _
    (Stacks.Divisors.isLocallyPrincipal_comap _ Ev hEv)
    (Scheme.Opens.ι (pr ⁻¹ᵁ Ev.support.compl)).toImage ?_
  rw [support_compl_comap, ← Scheme.Hom.comp_preimage, ← Category.assoc,
    Scheme.Hom.toImage_imageι, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]

/-- **Stacks Project, Tag 080E, in the form its consumers use.** The inverse image of the
exceptional divisor of the blowup of `S` in `I` on the strict transform of `X ⟶ S` is an
effective Cartier divisor.

This is the usable consequence of tag 080E — that the strict transform of `X` is the blowup of
`X` in the inverse image of `I` — combined with tag 02OS part (2); it is proved here directly,
without producing that isomorphism, by
`Stacks.Divisors.isEffectiveCartierDivisor_comap_subschemeι_comp`. -/
private theorem isEffectiveCartierDivisor_comap_exceptionalIdeal {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((AlgebraicGeometry.exceptionalIdeal I).comap
        ((Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase I)
            (AlgebraicGeometry.exceptionalIdeal I)).subschemeι ≫
          Limits.pullback.snd f (AlgebraicGeometry.blowUpToBase I))) := by
  have hprin : Stacks.Divisors.IsLocallyPrincipal (AlgebraicGeometry.exceptionalIdeal I) :=
    Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  have : QuasiCompact
      (Scheme.Opens.ι (AlgebraicGeometry.exceptionalIdeal I).support.compl) := by
    have := Stacks.Divisors.isAffineHom_compl_of_isLocallyPrincipal _ hprin
    infer_instance
  exact isEffectiveCartierDivisor_comap_subschemeι_comp _ _ hprin _
    (Stacks.StrictTransform.ideal_eq_ker_ι f _ _)

/-! ### Stand-in for [Stacks, Tag 0AG8]

The lemmas of this block are a **stand-in for the clause of [Stacks, Tag 0AG8]** saying that a
stalkwise regular principal generator makes a closed subscheme an effective Cartier divisor.
Only the first clause of that tag is formalized; the block is to be deleted once the second
clause is.
-/

section Spreading

variable {A : Type*} [CommRing A]

/-- In a commutative ring, an element killing only `0` is regular. -/
private theorem isRegular_of_forall_mul_eq_zero {y : A} (h : ∀ a : A, a * y = 0 → a = 0) :
    _root_.IsRegular y :=
  isRegular_iff_mem_nonZeroDivisors.2 ⟨fun a ha => h a (by rw [mul_comm]; exact ha), h⟩

/-- A regular element kills only `0`. -/
private theorem eq_zero_of_mul_eq_zero_of_isRegular {y : A} (hy : _root_.IsRegular y) {a : A}
    (ha : a * y = 0) : a = 0 :=
  hy.right (by simpa using ha)

/-- **Spreading out a nonzerodivisor, the Noetherian half.** If `y` becomes a nonzerodivisor
in the localization of a Noetherian ring `A` at a prime `p`, then a single element `c ∉ p`
annihilates the whole annihilator of `y`: that ideal is finitely generated and each of its
generators dies in `A_p`. -/
private theorem exists_notMem_forall_mul_eq_zero [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization p.primeCompl S] (y : A)
    (hy : _root_.IsRegular (algebraMap A S y)) :
    ∃ c : A, c ∉ p ∧ ∀ a : A, a * y = 0 → c * a = 0 := by
  classical
  have hmem : ∀ a : A, a ∈ (Submodule.span A ({y} : Set A)).annihilator ↔ a * y = 0 := fun a => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing (Submodule.span A ({y} : Set A)).annihilator
  have hkill : ∀ a ∈ s, ∃ d : A, d ∉ p ∧ d * a = 0 := by
    intro a ha
    have haJ : a ∈ (Submodule.span A ({y} : Set A)).annihilator := by
      rw [← hs]; exact Ideal.subset_span (Finset.mem_coe.2 ha)
    have h0 : algebraMap A S a = 0 :=
      eq_zero_of_mul_eq_zero_of_isRegular hy (by rw [← map_mul, (hmem a).1 haJ, map_zero])
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl S a).1 h0
    exact ⟨m.1, m.2, hm⟩
  choose! d hdp hdz using hkill
  have hprod : (∏ a ∈ s, d a) ∈ p.primeCompl :=
    Submonoid.prod_mem _ fun a ha => hdp a ha
  refine ⟨∏ a ∈ s, d a, hprod, fun a hay => ?_⟩
  have hspan : (Ideal.span (s : Set A)) ≤
      (Submodule.span A ({∏ a ∈ s, d a} : Set A)).annihilator := by
    rw [Ideal.span_le]
    intro b hb
    have hb' : b ∈ s := Finset.mem_coe.1 hb
    simp only [SetLike.mem_coe, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    rw [← Finset.mul_prod_erase s d hb']
    calc b * (d b * ∏ u ∈ s.erase b, d u)
        = d b * b * ∏ u ∈ s.erase b, d u := by ring
      _ = 0 := by rw [hdz b hb', zero_mul]
  have haJ : a ∈ Ideal.span (s : Set A) := by rw [hs]; exact (hmem a).2 hay
  have hfin := hspan haJ
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hfin
  rw [mul_comm]
  exact hfin

/-- **Spreading out a nonzerodivisor, the localization half.** If one element `c` annihilates
the whole annihilator of `y`, then `y` is a nonzerodivisor in every localization of `A` away
from `c`. No finiteness hypothesis is needed. -/
private theorem isRegular_algebraMap_of_forall_mul_eq_zero {c y : A}
    (hc : ∀ a : A, a * y = 0 → c * a = 0) (T : Type*) [CommRing T] [Algebra A T]
    [IsLocalization.Away c T] : _root_.IsRegular (algebraMap A T y) := by
  refine isRegular_of_forall_mul_eq_zero fun t ht => ?_
  obtain ⟨⟨a, m⟩, hma⟩ := IsLocalization.surj (Submonoid.powers c) t
  have hzero : algebraMap A T (a * y) = 0 := by
    rw [map_mul, ← hma]
    calc t * algebraMap A T (m : A) * algebraMap A T y
        = t * algebraMap A T y * algebraMap A T (m : A) := by ring
      _ = 0 := by rw [ht, zero_mul]
  obtain ⟨m', hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c) T (a * y)).1 hzero
  have ha0 : algebraMap A T a = 0 := by
    refine (IsLocalization.map_eq_zero_iff (Submonoid.powers c) T a).2
      ⟨⟨c * (m' : A), Submonoid.mul_mem _ (Submonoid.mem_powers c) m'.2⟩, ?_⟩
    calc c * (m' : A) * a = c * ((m' : A) * a) := by ring
      _ = 0 := hc _ (by rw [mul_assoc]; exact hm')
  exact (IsUnit.mul_left_eq_zero
    (IsLocalization.map_units (M := Submonoid.powers c) T m)).1 (hma.trans ha0)

end Spreading

/-- **Stacks Project, Tag 0AG8, second clause.** A closed subscheme of a locally Noetherian
scheme is an effective Cartier divisor if, at every point of the subscheme, its ideal is
generated in the local ring by a single nonzerodivisor. -/
private theorem isEffectiveCartierDivisor_of_stalk_regular_principal
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : ∀ x : X, x ∈ I.support →
      ∃ f : X.presheaf.stalk x,
        _root_.IsRegular f ∧ AlgebraicGeometry.IdealSheafData.stalk I x = Ideal.span {f}) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  have hprin : Stacks.Divisors.IsLocallyPrincipal I :=
    Stacks.Divisors.isLocallyPrincipal_of_stalk_isPrincipal I fun z hz =>
      let ⟨g, _, hg⟩ := hI z hz; ⟨g, hg⟩
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen I fun x => ?_
  by_cases hx : x ∈ I.support
  swap
  · exact Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_notMem_support I x hx
  obtain ⟨f, hfreg, hfspan⟩ := hI x hx
  obtain ⟨W, hxW, hWprin⟩ := hprin x
  obtain ⟨y, hy⟩ := hWprin
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  let q : PrimeSpectrum Γ(X, W) := W.2.primeIdealOf ⟨x, hxW⟩
  let p : Ideal Γ(X, W) := q.asIdeal
  have : p.IsPrime := q.isPrime
  let _ : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have : IsLocalization p.primeCompl (X.presheaf.stalk x) := W.2.isLocalization_stalk ⟨x, hxW⟩
  have hyreg : _root_.IsRegular (algebraMap Γ(X, W) (X.presheaf.stalk x) y) := by
    have hstalk : IdealSheafData.stalk I x =
        Ideal.span {algebraMap Γ(X, W) (X.presheaf.stalk x) y} := by
      have h1 : IdealSheafData.stalk I x =
          Ideal.span {(X.presheaf.germ W.1 x hxW).hom y} := by
        rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I x W hxW, hy, Ideal.map_span,
          Set.image_singleton]
      exact h1
    have hfmem : f ∈ Ideal.span {algebraMap Γ(X, W) (X.presheaf.stalk x) y} := by
      rw [← hstalk, hfspan]; exact Ideal.mem_span_singleton_self f
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hfmem
    have hmul : _root_.IsRegular (b * algebraMap Γ(X, W) (X.presheaf.stalk x) y) := by
      rw [hb]; exact hfreg
    exact hmul.of_mul_right
  obtain ⟨c, hcp, hc⟩ :=
    exists_notMem_forall_mul_eq_zero p (X.presheaf.stalk x) y hyreg
  let V := X.affineBasicOpen c
  have hxV : x ∈ V.1 := by
    refine (X.mem_basicOpen' c ⟨x, hxW⟩).2 ?_
    change IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk x) c)
    exact IsLocalization.map_units (M := p.primeCompl) _ ⟨c, hcp⟩
  let _ : Algebra Γ(X, W) Γ(X, V) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le c)).op).hom.toAlgebra
  have : IsLocalization.Away c Γ(X, V) := W.2.isLocalization_basicOpen c
  refine ⟨V.1, V.2, hxV, algebraMap Γ(X, W) Γ(X, V) y,
    isRegular_algebraMap_of_forall_mul_eq_zero hc _, ?_⟩
  have hmapI : I.ideal V = (I.ideal W).map (algebraMap Γ(X, W) Γ(X, V)) := by
    rw [← I.map_ideal (X.basicOpen_le c)]; rfl
  rw [show I.ideal ⟨V.1, V.2⟩ = I.ideal V from rfl, hmapI, hy, Ideal.map_span,
    Set.image_singleton]

/-- The quasi-coherent ideal of the strict transform of the closed subscheme cut out by `I`
under the blowup of the ambient scheme at the closed point `p`. -/
public noncomputable abbrev strictTransformCenterIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    (pullback I.subschemeι
      (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))).IdealSheafData :=
  Stacks.StrictTransform.ideal I.subschemeι
    (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))
    (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp))

/-- The part of the base change on which the strict transform changes nothing is the inverse
image of the complement of the centre. -/
private theorem exceptionalComplement_centerIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    Stacks.StrictTransform.exceptionalComplement I.subschemeι
        (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))
        (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)) =
      (pullback.fst I.subschemeι
          (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)) ≫ I.subschemeι) ⁻¹ᵁ
        (centerIdeal p hp).support.compl := by
  change pullback.snd I.subschemeι (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)) ⁻¹ᵁ
      ((centerIdeal p hp).comap
        (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))).support.compl = _
  rw [← Stacks.Blowup.preimage_compl_support (centerIdeal p hp)
      (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)),
    ← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]

/-- The defining ideal of the strict transform is the kernel ideal sheaf of the inclusion of
the complement of the inverse image of the centre. -/
private theorem strictTransformCenterIdeal_eq_ker {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    strictTransformCenterIdeal I p hp =
      (Scheme.Opens.ι ((pullback.fst I.subschemeι
          (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)) ≫ I.subschemeι) ⁻¹ᵁ
        (centerIdeal p hp).support.compl)).ker := by
  change Stacks.StrictTransform.ideal I.subschemeι
      (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))
      (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)) = _
  rw [Stacks.StrictTransform.ideal_eq_ker_ι, exceptionalComplement_centerIdeal]

/-- The strict transform of a closed subscheme in the pullback presentation. -/
public def transform {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) : Scheme.{u} :=
  (strictTransformCenterIdeal I p hp).subscheme

/-- The canonical map of a strict transform to the ambient blowup. -/
public def transformToBlowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    transform I p hp ⟶ (AlgebraicGeometry.blowUp (centerIdeal p hp)) :=
  (strictTransformCenterIdeal I p hp).subschemeι ≫
    pullback.snd I.subschemeι (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))

/-- The defining ideal of a strict transform in the ambient blowup. -/
public def transformIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    (AlgebraicGeometry.blowUp (centerIdeal p hp)).IdealSheafData :=
  (transformToBlowUp I p hp).ker

/-- The canonical map of a strict transform to the original subscheme. -/
public def transformToCurve {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : X) (hp : IsClosed ({p} : Set X)) : transform I p hp ⟶ I.subscheme :=
  (strictTransformCenterIdeal I p hp).subschemeι ≫
    pullback.fst I.subschemeι (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))

private theorem transformToCurve_isIso_of_comap_effectiveCartier
    {X : Scheme.{u}} (I : X.IdealSheafData) (p : X)
    (hp : IsClosed ({p} : Set X))
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor
      ((centerIdeal p hp).comap I.subschemeι)) :
    IsIso (transformToCurve I p hp) := by
  have h := isIso_subschemeι_ker_comp_fst I.subschemeι (centerIdeal p hp) hI
  rw [← strictTransformCenterIdeal_eq_ker] at h
  exact h

/-- In a one-dimensional regular local ring, the maximal ideal has a regular
generator. This is the local parameter used in the affine proof of the lemma. -/
private theorem exists_regular_parameter_of_regular_one_dimensional_local_ring
    {A : Type*} [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 1) :
    ∃ t : A, _root_.IsRegular t ∧ IsLocalRing.maximalIdeal A = Ideal.span {t} := by
  have hspan : (IsLocalRing.maximalIdeal A).spanFinrank = 1 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨t, htgen⟩ :=
    (Submodule.spanFinrank_eq_one_iff (IsLocalRing.maximalIdeal A)).mp hspan |>.1
  have hne : t ≠ 0 := by
    intro ht
    have : IsLocalRing.maximalIdeal A = (⊥ : Ideal A) := by
      rw [htgen, ht]
      simp
    exact (Submodule.spanFinrank_eq_one_iff
      (IsLocalRing.maximalIdeal A)).mp hspan |>.2 this
  let : IsDomain A := IsRegularLocalRing.isDomain A
  exact ⟨t, isRegular_iff_ne_zero.mpr hne, htgen⟩


private theorem subschemePoint_isClosed_of_ambientPoint_isClosed
    {X : Scheme.{u}} (I : X.IdealSheafData) (p : X)
    (hp : IsClosed ({p} : Set X)) (x : I.subscheme)
    (hx : I.subschemeι x = p) : IsClosed ({x} : Set I.subscheme) := by
  have hpre : I.subschemeι ⁻¹' ({p} : Set X) = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact fun hy ↦ I.subschemeι.isClosedEmbedding.injective (hy.trans hx.symm)
    · rintro rfl
      exact hx
  rw [← hpre]
  exact hp.preimage I.subschemeι.continuous

private theorem exists_parameter_for_regular_point_on_integral_curve
    {X : Scheme.{u}} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (hIdim : topologicalKrullDim I.subscheme = 1) (x : I.subscheme)
    (hx : IsClosed ({x} : Set I.subscheme))
    (hregular : IsRegularLocalRing (I.subscheme.presheaf.stalk x)) :
    ∃ t : I.subscheme.presheaf.stalk x,
      _root_.IsRegular t ∧ IsLocalRing.maximalIdeal _ = Ideal.span {t} := by
  let : IsRegularLocalRing (I.subscheme.presheaf.stalk x) := hregular
  have hdim := ringKrullDim_stalk_eq_one_of_integral_curve
    I.subscheme hIdim x hx
  exact exists_regular_parameter_of_regular_one_dimensional_local_ring hdim

private theorem exists_curve_parameter_at_ambient_closed_point
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (hIdim : topologicalKrullDim I.subscheme = 1)
    (p : X) (hp : IsClosed ({p} : Set X)) (x : I.subscheme)
    (hx : I.subschemeι x = p)
    (hregular : IsRegularLocalRing (I.subscheme.presheaf.stalk x)) :
    ∃ t : I.subscheme.presheaf.stalk x,
      _root_.IsRegular t ∧ IsLocalRing.maximalIdeal _ = Ideal.span {t} :=
  exists_parameter_for_regular_point_on_integral_curve I hIdim x
    (subschemePoint_isClosed_of_ambientPoint_isClosed I p hp x hx) hregular



private theorem centerIdeal_ideal {X : Scheme.{u}} (p : X)
    (hp : IsClosed ({p} : Set X)) (U : X.affineOpens) (hpU : p ∈ U.1) :
    (centerIdeal p hp).ideal U = (U.2.primeIdealOf ⟨p, hpU⟩).asIdeal := by
  obtain ⟨U, hU⟩ := U
  change IsAffineOpen U at hU
  rw [centerIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  have hpre : hU.fromSpec ⁻¹' ({p} : Set X) = {hU.primeIdealOf ⟨p, hpU⟩} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact fun hz ↦
        hU.fromSpec.isOpenEmbedding.injective (hz.trans (hU.fromSpec_primeIdealOf ⟨p, hpU⟩).symm)
    · rintro rfl
      exact hU.fromSpec_primeIdealOf ⟨p, hpU⟩
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' ({p} : Set X)) = _
  exact (congrArg PrimeSpectrum.vanishingIdeal hpre).trans
    (PrimeSpectrum.vanishingIdeal_singleton _)

private theorem stalk_centerIdeal {X : Scheme.{u}} (p : X)
    (hp : IsClosed ({p} : Set X)) :
    AlgebraicGeometry.IdealSheafData.stalk (centerIdeal p hp) p =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  let V : X.affineOpens := ⟨U, hU⟩
  rw [IdealSheafData.stalk_eq_map_germ _ _ V hpU, centerIdeal_ideal p hp V hpU]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p, hpU⟩ : U)
  let := hU.isLocalization_stalk ⟨p, hpU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

private theorem stalk_comap_centerIdeal {X C : Scheme.{u}} (f : C ⟶ X)
    [SurjectiveOnStalks f] (p : X) (hp : IsClosed ({p} : Set X))
    (x : C) (hx : f x = p) :
    AlgebraicGeometry.IdealSheafData.stalk ((centerIdeal p hp).comap f) x =
      IsLocalRing.maximalIdeal (C.presheaf.stalk x) := by
  subst p
  rw [IdealSheafData.stalk_comap, stalk_centerIdeal]
  exact IsLocalRing.map_maximalIdeal_of_surjective _ (f.stalkMap_surjective x)

private theorem comap_centerIdeal_isEffectiveCartierDivisor
    {X : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (hYdim : topologicalKrullDim Y.subscheme = 1)
    (p : X) (hp : IsClosed ({p} : Set X))
    (yPoint : Y.subscheme) (hyPoint : Y.subschemeι yPoint = p)
    (hregular : IsRegularLocalRing (Y.subscheme.presheaf.stalk yPoint)) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((centerIdeal p hp).comap Y.subschemeι) := by
  have : IsLocallyNoetherian Y.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian Y.subschemeι
  apply isEffectiveCartierDivisor_of_stalk_regular_principal
  intro y hy
  have hyp : Y.subschemeι y = p := by
    rw [Scheme.IdealSheafData.support_comap] at hy
    change Y.subschemeι y ∈ ((centerIdeal p hp).support : Set X) at hy
    simpa only [centerIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_mk, Set.mem_singleton_iff] using hy
  have heq : y = yPoint := Y.subschemeι.isClosedEmbedding.injective (hyp.trans hyPoint.symm)
  subst y
  rw [stalk_comap_centerIdeal _ p hp yPoint hyPoint]
  exact exists_curve_parameter_at_ambient_closed_point Y hYdim p hp yPoint hyPoint hregular

/-- The length of the local intersection ring, viewed as a module over the
ambient local ring. -/
public def intersectionLength {X : Scheme.{u}} (I J : X.IdealSheafData)
    (q : X) (hq : q ∈ (I ⊔ J).support) : ℕ :=
  let i : (I ⊔ J).subscheme := ⟨q, hq⟩
  letI : Algebra (X.presheaf.stalk q) ((I ⊔ J).subscheme.presheaf.stalk i) :=
    (((I ⊔ J).subschemeι.stalkMap i).hom).toAlgebra
  (Module.length (X.presheaf.stalk q) ((I ⊔ J).subscheme.presheaf.stalk i)).toNat

/-- Part (1): a curve regular at the centre is unchanged by strict transform. -/
@[stacks 0BI7 "part (1)"] public theorem strictTransformToCurve_isIso
    {X : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (hYdim : topologicalKrullDim Y.subscheme = 1)
    (p : X) (hp : IsClosed ({p} : Set X))
    (yPoint : Y.subscheme) (hyPoint : Y.subschemeι yPoint = p)
    (hregular : IsRegularLocalRing (Y.subscheme.presheaf.stalk yPoint)) :
    IsIso (transformToCurve Y p hp) :=
  transformToCurve_isIso_of_comap_effectiveCartier Y p hp
    (comap_centerIdeal_isEffectiveCartierDivisor Y hYdim p hp yPoint hyPoint hregular)

private theorem transformToBlowUp_comp_toBase {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X)) :
    transformToBlowUp I p hp ≫ (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)) =
      transformToCurve I p hp ≫ I.subschemeι := by
  change ((strictTransformCenterIdeal I p hp).subschemeι ≫
      pullback.snd I.subschemeι (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))) ≫
      AlgebraicGeometry.blowUpToBase (centerIdeal p hp) =
    ((strictTransformCenterIdeal I p hp).subschemeι ≫
      pullback.fst I.subschemeι (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))) ≫
      I.subschemeι
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- Over a regular point of the curve, the pullback of the exceptional ideal to the strict
transform has the maximal ideal as stalk. -/
private theorem stalk_comap_exceptionalIdeal_transformToBlowUp {X : Scheme.{u}}
    (Y : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X))
    [IsIso (transformToCurve Y p hp)] (c : transform Y p hp)
    (hc : Y.subschemeι (transformToCurve Y p hp c) = p) :
    AlgebraicGeometry.IdealSheafData.stalk
      ((AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).comap
        (transformToBlowUp Y p hp)) c =
      IsLocalRing.maximalIdeal ((transform Y p hp).presheaf.stalk c) := by
  have hE : (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).comap
      (transformToBlowUp Y p hp) =
      (centerIdeal p hp).comap (transformToCurve Y p hp ≫ Y.subschemeι) := by
    change ((centerIdeal p hp).comap
      (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))).comap _ = _
    rw [← Scheme.IdealSheafData.comap_comp, transformToBlowUp_comp_toBase]
  rw [hE]
  exact stalk_comap_centerIdeal _ p hp c hc

/-- A point of the target lying in the support of the kernel of a closed immersion is in its
range. -/
private theorem mem_range_of_mem_support_ker {X C : Scheme.{u}} (f : C ⟶ X)
    [IsClosedImmersion f] {q : X} (h : q ∈ f.ker.support) : q ∈ Set.range f := by
  have h' : q ∈ (f.ker.support : Set X) := h
  rwa [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq] at h'

/-- The one-step strict transform is a closed subscheme of the ambient blowup. -/
public theorem isClosedImmersion_transformToBlowUp {X : Scheme.{u}}
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X)) :
    IsClosedImmersion (transformToBlowUp I p hp) := by
  change IsClosedImmersion ((strictTransformCenterIdeal I p hp).subschemeι ≫
    pullback.snd I.subschemeι (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)))
  infer_instance

/-- A point of the blowup lies on the exceptional divisor exactly when it lies over the
centre. -/
public theorem mem_exceptionalIdeal_support_iff {X : Scheme.{u}}
    (p : X) (hp : IsClosed ({p} : Set X))
    (q : (AlgebraicGeometry.blowUp (centerIdeal p hp))) :
    q ∈ (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).support ↔
      (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)) q = p := by
  change q ∈ ((centerIdeal p hp).comap
    (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))).support ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  change (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)) q ∈
    ((centerIdeal p hp).support : Set X) ↔ _
  simp only [centerIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_mk, Set.mem_singleton_iff]

/-- Part (2): the strict transform has exactly one point on the exceptional fibre. -/
@[stacks 0BI7 "part (2), unique point"] public theorem strictTransform_exceptional_unique
    {X : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (hYdim : topologicalKrullDim Y.subscheme = 1)
    (p : X) (hp : IsClosed ({p} : Set X))
    (yPoint : Y.subscheme) (hyPoint : Y.subschemeι yPoint = p)
    (hregular : IsRegularLocalRing (Y.subscheme.presheaf.stalk yPoint)) :
    ∃! q : (AlgebraicGeometry.blowUp (centerIdeal p hp)),
      q ∈ (transformIdeal Y p hp).support ∧
      q ∈ (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).support := by
  let f := transformToBlowUp Y p hp
  let g := transformToCurve Y p hp
  let π := (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))
  have : IsClosedImmersion f := isClosedImmersion_transformToBlowUp Y p hp
  have : IsIso g := strictTransformToCurve_isIso Y hYdim p hp yPoint hyPoint hregular
  let t : transform Y p hp := g.homeomorph.symm yPoint
  have ht : g t = yPoint := g.homeomorph.apply_symm_apply yPoint
  have hcomm (z : transform Y p hp) : π (f z) = Y.subschemeι (g z) :=
    congrArg (fun k => k z) (transformToBlowUp_comp_toBase Y p hp)
  refine ⟨f t, ⟨?_, ?_⟩, ?_⟩
  · exact f.range_subset_ker_support ⟨t, rfl⟩
  · rw [mem_exceptionalIdeal_support_iff]
    exact (hcomm t).trans (congrArg Y.subschemeι ht |>.trans hyPoint)
  · intro q hq
    obtain ⟨z, rfl⟩ := mem_range_of_mem_support_ker f hq.1
    have hz : g z = yPoint := Y.subschemeι.isClosedEmbedding.injective <| (hcomm z).symm.trans
      ((mem_exceptionalIdeal_support_iff p hp (f z)).mp hq.2 |>.trans hyPoint.symm)
    exact congrArg f (g.homeomorph.injective (hz.trans ht.symm))

private theorem stalk_bot {X : Scheme.{u}} (x : X) :
    AlgebraicGeometry.IdealSheafData.stalk (⊥ : X.IdealSheafData) x = ⊥ := by
  simp [AlgebraicGeometry.IdealSheafData.stalk]

private theorem comap_subschemeι_eq_bot {X : Scheme.{u}}
    {I J : X.IdealSheafData} (h : I ≤ J) : I.comap J.subschemeι = ⊥ := by
  apply le_bot_iff.mp
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  simpa using h

private theorem length_stalk_eq_one_of_isField {X C : Scheme.{u}}
    (i : C ⟶ X) [SurjectiveOnStalks i] (x : C)
    (h : IsField (C.presheaf.stalk x)) :
    letI := (i.stalkMap x).hom.toAlgebra
    Module.length (X.presheaf.stalk (i x)) (C.presheaf.stalk x) = 1 := by
  let := (i.stalkMap x).hom.toAlgebra
  rw [length_restrictScalars_eq_of_surjective _ _ (i.stalkMap x).hom
    (i.stalkMap_surjective x) (C.presheaf.stalk x)]
  let := h.toField
  exact Module.length_eq_one _ _

/-- Part (2): the exceptional intersection has multiplicity one. -/
@[stacks 0BI7 "part (2), multiplicity"] public theorem
    strictTransform_exceptional_multiplicity_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (hYdim : topologicalKrullDim Y.subscheme = 1)
    (p : X) (hp : IsClosed ({p} : Set X))
    (yPoint : Y.subscheme) (hyPoint : Y.subschemeι yPoint = p)
    (hregular : IsRegularLocalRing (Y.subscheme.presheaf.stalk yPoint))
    (q : (AlgebraicGeometry.blowUp (centerIdeal p hp)))
    (hq : q ∈ ((transformIdeal Y p hp) ⊔
      AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).support) :
    intersectionLength (transformIdeal Y p hp)
      (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)) q hq = 1 := by
  let f := transformToBlowUp Y p hp
  let g := transformToCurve Y p hp
  let π := (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))
  let E := AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)
  let D := transformIdeal Y p hp ⊔ E
  let i := D.subschemeι
  let d : D.subscheme := ⟨q, hq⟩
  have : IsClosedImmersion f := isClosedImmersion_transformToBlowUp Y p hp
  have : IsIso g := strictTransformToCurve_isIso Y hYdim p hp yPoint hyPoint hregular
  have hker : f.ker ≤ i.ker := by
    change f.ker ≤ D.subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact le_sup_left
  let a := IsClosedImmersion.lift f i hker
  have ha : a ≫ f = i := IsClosedImmersion.lift_fac f i hker
  have : IsClosedImmersion (a ≫ f) := ha ▸ inferInstance
  have : IsClosedImmersion a := IsClosedImmersion.of_comp_isClosedImmersion a f
  have hqE : q ∈ E.support :=
    Scheme.IdealSheafData.support_antitone (show E ≤ D from le_sup_right) hq
  have hx : (g ≫ Y.subschemeι) (a d) = p := by
    rw [← transformToBlowUp_comp_toBase Y p hp]
    change π (f (a d)) = p
    have hai : f (a d) = q := congrArg (fun k => k d) ha
    rw [hai]
    exact (mem_exceptionalIdeal_support_iff p hp q).mp hqE
  have hmax := stalk_comap_exceptionalIdeal_transformToBlowUp Y p hp (a d) hx
  have hzero : (E.comap f).comap a = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_comp, ha]
    exact comap_subschemeι_eq_bot (show E ≤ D from le_sup_right)
  have hmap : Ideal.map (a.stalkMap d).hom
      (IsLocalRing.maximalIdeal ((transform Y p hp).presheaf.stalk (a d))) = ⊥ := by
    rw [← hmax, ← IdealSheafData.stalk_comap, hzero, stalk_bot]
  have hfield : IsField (D.subscheme.presheaf.stalk d) := by
    apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    rwa [IsLocalRing.map_maximalIdeal_of_surjective _ (a.stalkMap_surjective d)] at hmap
  exact congrArg ENat.toNat (length_stalk_eq_one_of_isField i d hfield)

private theorem ideal_eq_span_of_chart {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) (hU : IsAffineOpen U) (f : Γ(X, U))
    (e : pullback I.subschemeι U.ι ≅
      Spec (.of (Γ(X, U) ⧸ Ideal.span {f})))
    (he : pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {f})))) :
    I.ideal ⟨U, hU⟩ = Ideal.span {f} :=
  Stacks.Divisors.ideal_eq_quotient_of_chart I U hU (Ideal.span {f}) e he

private theorem stalk_le_maximalIdeal_iff_mem_support
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    AlgebraicGeometry.IdealSheafData.stalk I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∈ I.support := by
  simp only [AlgebraicGeometry.IdealSheafData.stalk, iSup_le_iff]
  constructor
  · intro h
    rw [Scheme.IdealSheafData.mem_support_iff]
    intro U
    rw [Scheme.mem_zeroLocus_iff]
    intro s hs
    by_cases hxU : x ∈ U.1
    · have hs' : (X.presheaf.germ U.1 x hxU).hom s ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
        h U hxU (Ideal.mem_map_of_mem _ hs)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs'
      exact fun hbasic ↦ hs' ((Scheme.mem_basicOpen X s x hxU).mp hbasic)
    · intro hbasic
      exact hxU (X.basicOpen_le s hbasic)
  · intro h U hx
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hxnot : x ∉ X.basicOpen s := by
      rw [Scheme.IdealSheafData.mem_support_iff] at h
      have hxzero := h U
      rw [Scheme.mem_zeroLocus_iff] at hxzero
      exact hxzero s hs
    exact (Scheme.mem_basicOpen X s x hx).not.mp hxnot

private theorem exists_regular_generator_at_support
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hx : x ∈ I.support) :
    ∃ b : X.presheaf.stalk x,
      b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧ _root_.IsRegular b ∧
        AlgebraicGeometry.IdealSheafData.stalk I x = Ideal.span {b} := by
  have hx' : x ∈ I.supportSet := by
    rwa [Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
  obtain ⟨U, hU, hxU, a, ha, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hx'
  have hgen : I.ideal ⟨U, hU⟩ = Ideal.span {a} :=
    ideal_eq_span_of_chart I U hU a e he
  let b : X.presheaf.stalk x := (X.presheaf.germ U x hxU).hom a
  have hstalk : AlgebraicGeometry.IdealSheafData.stalk I x = Ideal.span {b} := by
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU, hgen, Ideal.map_span]
    simp [b]
  have hmax : b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    have hle := (stalk_le_maximalIdeal_iff_mem_support I x).2 hx
    rw [hstalk] at hle
    exact hle (Ideal.subset_span (Set.mem_singleton b))
  have hreg : _root_.IsRegular b := by
    let q := hU.primeIdealOf ⟨x, hxU⟩
    let A := Γ(X, U)
    let R := X.presheaf.stalk x
    let : Algebra A R := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    let : IsLocalization.AtPrime R q.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
    have ha' : a ∈ nonZeroDivisors A := (isRegular_iff_mem_nonZeroDivisors).1 ha
    have hb' : algebraMap A R a ∈ nonZeroDivisors R :=
      IsLocalization.map_nonZeroDivisors_le q.asIdeal.primeCompl R ⟨a, ha', rfl⟩
    change _root_.IsRegular (algebraMap A R a)
    exact (isRegular_iff_mem_nonZeroDivisors).2 hb'
  exact ⟨b, hmax, hreg, hstalk⟩

private theorem stalk_ker {X C : Scheme.{u}} (f : C ⟶ X)
    [IsClosedImmersion f] (x : C) :
    AlgebraicGeometry.IdealSheafData.stalk f.ker (f x) = RingHom.ker (f.stalkMap x).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(X, U)
  let B := Γ(C, V)
  let Rp := X.presheaf.stalk (f x)
  let Bp := C.presheaf.stalk x
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxU⟩
  let α : R →+* B := (f.app U).hom
  let : Algebra R Rp := X.presheaf.algebra_section_stalk ⟨f x, hxU⟩
  let : Algebra B Bp := C.presheaf.algebra_section_stalk (⟨x, hxU⟩ : V)
  have : IsLocalization.AtPrime Rp p.asIdeal := hU.isLocalization_stalk ⟨f x, hxU⟩
  have : IsLocalization.AtPrime Bp q.asIdeal := hV.isLocalization_stalk ⟨x, hxU⟩
  have hpq : q.asIdeal.comap α = p.asIdeal := by
    have h := hU.comap_primeIdealOf_appLE U V hV (le_refl _) hxU
    simpa only [R, B, α, p, q, V, Scheme.Hom.appLE_eq_app,
      PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal h
  have hT : p.asIdeal.primeCompl.map α = q.asIdeal.primeCompl := by
    simpa only [hpq] using
      Ideal.map_primeCompl_comap_of_surjective α (f.app_surjective U hU) q.asIdeal
  have hle : p.asIdeal.primeCompl ≤ q.asIdeal.primeCompl.comap α :=
    Submonoid.map_le_iff_le_comap.mp hT.le
  have hmap : (f.stalkMap x).hom =
      IsLocalization.map Bp α hle := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom (f.germ_stalkMap U x hxU)
  rw [IdealSheafData.stalk_eq_map_germ _ _ ⟨U, hU⟩ hxU, Scheme.Hom.ker_apply, hmap]
  exact (IsLocalization.ker_map Bp α hT).symm

private theorem stalk_sup {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    AlgebraicGeometry.IdealSheafData.stalk (I ⊔ J) x =
      AlgebraicGeometry.IdealSheafData.stalk I x ⊔ AlgebraicGeometry.IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  simp only [IdealSheafData.stalk_eq_map_germ _ _ ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, Ideal.map_sup]

private theorem length_eq_length_quotient_ker {R A : Type*}
    [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Surjective f) :
    letI := f.toAlgebra
    Module.length R A = Module.length R (R ⧸ RingHom.ker f) := by
  let := f.toAlgebra
  exact (Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId R A) hf).toLinearEquiv.length_eq.symm

private theorem length_quotient_sup_ker {R A : Type*}
    [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Surjective f)
    (J : Ideal R) :
    Module.length R (R ⧸ (RingHom.ker f ⊔ J)) =
      Module.length A (A ⧸ J.map f) := by
  let : Algebra R A := f.toAlgebra
  have hsurj : Function.Surjective (algebraMap R A) := hf
  have hmap : (algebraMap R (A ⧸ J.map f) : R →+* A ⧸ J.map f) =
      (Ideal.Quotient.mk (J.map f)).comp f := rfl
  have hsurj2 : Function.Surjective (algebraMap R (A ⧸ J.map f)) := by
    rw [hmap]
    exact Ideal.Quotient.mk_surjective.comp hf
  have hk : RingHom.ker (Algebra.ofId R (A ⧸ J.map f)) = RingHom.ker f ⊔ J := by
    change RingHom.ker (algebraMap R (A ⧸ J.map f)) = _
    rw [hmap]
    change (RingHom.ker (Ideal.Quotient.mk (J.map f))).comap f = _
    rw [Ideal.mk_ker, Ideal.comap_map_of_surjective f hf]
    exact sup_comm _ _
  have e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R (A ⧸ J.map f)) hsurj2
  rw [← hk, ← Module.length_eq_of_surjective (S := R) (R := A) (M := A ⧸ J.map f) hsurj]
  exact e.toLinearEquiv.length_eq

private theorem intersectionLength_eq_colength {X : Scheme.{u}}
    (I J : X.IdealSheafData) (q : X) (hq : q ∈ (I ⊔ J).support) :
    intersectionLength I J q hq =
      (Module.length (X.presheaf.stalk q)
        ((X.presheaf.stalk q) ⧸
          (AlgebraicGeometry.IdealSheafData.stalk I q ⊔
            AlgebraicGeometry.IdealSheafData.stalk J q))).toNat := by
  let d : (I ⊔ J).subscheme := ⟨q, hq⟩
  have hker := stalk_ker (I ⊔ J).subschemeι d
  rw [Scheme.IdealSheafData.ker_subschemeι, stalk_sup] at hker
  have h := length_eq_length_quotient_ker ((I ⊔ J).subschemeι.stalkMap d).hom
    ((I ⊔ J).subschemeι.stalkMap_surjective d)
  rw [← hker] at h
  exact congrArg ENat.toNat h


private theorem colength_comap_iso {X C : Scheme.{u}}
    (f : C ⟶ X) [IsIso f] (J : X.IdealSheafData) (c : C) :
    Module.length (X.presheaf.stalk (f c))
      ((X.presheaf.stalk (f c)) ⧸ AlgebraicGeometry.IdealSheafData.stalk J (f c)) =
    Module.length (C.presheaf.stalk c)
      ((C.presheaf.stalk c) ⧸ AlgebraicGeometry.IdealSheafData.stalk (J.comap f) c) := by
  rw [IdealSheafData.stalk_comap]
  have h := length_quotient_sup_ker (f.stalkMap c).hom (f.stalkMap_surjective c)
    (AlgebraicGeometry.IdealSheafData.stalk J (f c))
  have hk : RingHom.ker (f.stalkMap c).hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (f.stalkMap c).hom).mp
      (asIso (f.stalkMap c)).commRingCatIsoToRingEquiv.injective
  have hi : RingHom.ker (f.stalkMap c).hom ⊔
      AlgebraicGeometry.IdealSheafData.stalk J (f c) =
      AlgebraicGeometry.IdealSheafData.stalk J (f c) := by rw [hk, bot_sup_eq]
  exact (congrArg (fun K : Ideal (X.presheaf.stalk (f c)) =>
    Module.length (X.presheaf.stalk (f c)) ((X.presheaf.stalk (f c)) ⧸ K)) hi).symm.trans h

private theorem exists_regular_generator_exceptional_comap_transform
    {X : Scheme.{u}} (Z : X.IdealSheafData) (p : X)
    (hp : IsClosed ({p} : Set X)) (z : transform Z p hp)
    (hz : transformToBlowUp Z p hp z ∈
      (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).support) :
    ∃ b : (transform Z p hp).presheaf.stalk z, _root_.IsRegular b ∧
      AlgebraicGeometry.IdealSheafData.stalk
        ((AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).comap
          (transformToBlowUp Z p hp)) z = Ideal.span {b} := by
  have hz' : z ∈ ((AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).comap
      (transformToBlowUp Z p hp)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hz
  obtain ⟨b, -, hb, hgen⟩ := exists_regular_generator_at_support
    ((AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).comap
      (transformToBlowUp Z p hp)) z
    (isEffectiveCartierDivisor_comap_exceptionalIdeal Z.subschemeι (centerIdeal p hp)) hz'
  exact ⟨b, hb, hgen⟩

private theorem ideal_le_span_mul_ker {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (J : Ideal R) (t : R)
    (hJ : J ≤ Ideal.span {t}) (hz : J ≤ RingHom.ker f)
    (ht : _root_.IsRegular (f t)) : J ≤ Ideal.span {t} * RingHom.ker f := by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp (hJ hr)
  have hs : s ∈ RingHom.ker f := by
    apply ht.left
    simpa only [map_mul, mul_zero, RingHom.mem_ker] using hz hr
  exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton t)) hs

private theorem stalk_mono {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I ≤ J) (x : X) :
    AlgebraicGeometry.IdealSheafData.stalk I x ≤ AlgebraicGeometry.IdealSheafData.stalk J x :=
  iSup₂_mono fun U _ => Ideal.map_mono (h U)

private theorem totalTransform_stalk_le_exceptional_mul_strictTransform
    {X : Scheme.{u}} (Z : X.IdealSheafData) (p : X)
    (hp : IsClosed ({p} : Set X)) (hZ : Z ≤ centerIdeal p hp)
    (z : transform Z p hp)
    (hz : transformToBlowUp Z p hp z ∈
      (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)).support) :
    AlgebraicGeometry.IdealSheafData.stalk
      (Z.comap (AlgebraicGeometry.blowUpToBase (centerIdeal p hp)))
      (transformToBlowUp Z p hp z) ≤
      AlgebraicGeometry.IdealSheafData.stalk (AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp))
        (transformToBlowUp Z p hp z) *
      AlgebraicGeometry.IdealSheafData.stalk (transformIdeal Z p hp)
        (transformToBlowUp Z p hp z) := by
  let f := transformToBlowUp Z p hp
  let π := (AlgebraicGeometry.blowUpToBase (centerIdeal p hp))
  let E := AlgebraicGeometry.exceptionalIdeal (centerIdeal p hp)
  have : IsClosedImmersion f := isClosedImmersion_transformToBlowUp Z p hp
  obtain ⟨t, _, _, ht⟩ := exists_regular_generator_at_support E (f z)
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) hz
  have hzero : (Z.comap π).comap f = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_comp, transformToBlowUp_comp_toBase,
      Scheme.IdealSheafData.comap_comp, comap_subschemeι_eq_bot le_rfl,
      Scheme.IdealSheafData.comap_bot]
  have hker : AlgebraicGeometry.IdealSheafData.stalk (Z.comap π) (f z) ≤
      RingHom.ker (f.stalkMap z).hom := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [← IdealSheafData.stalk_comap, hzero, stalk_bot]
  have htreg : _root_.IsRegular ((f.stalkMap z).hom t) := by
    obtain ⟨b, hb, hbgen⟩ :=
      exists_regular_generator_exceptional_comap_transform Z p hp z hz
    rw [IdealSheafData.stalk_comap, ht, Ideal.map_span, Set.image_singleton] at hbgen
    have hdiv : (f.stalkMap z).hom t ∣ b := Ideal.mem_span_singleton.mp
      (hbgen ▸ Ideal.subset_span (Set.mem_singleton b))
    obtain ⟨r, hr⟩ := hdiv
    rw [hr] at hb
    exact hb.of_mul_left
  change _ ≤ _ * AlgebraicGeometry.IdealSheafData.stalk f.ker (f z)
  rw [stalk_ker, ht]
  apply ideal_le_span_mul_ker _ _ _ _ hker htreg
  rw [← ht]
  exact stalk_mono (Scheme.IdealSheafData.comap_mono π hZ) (f z)

private theorem length_quotient_bot_eq_top_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsNoetherianRing R] (hdim : ringKrullDim R = 1) :
    Module.length R (R ⧸ (⊥ : Ideal R)) = ⊤ := by
  have heq : Module.length R R = Module.length R (R ⧸ (⊥ : Ideal R)) :=
    (length_eq_length_quotient_ker (RingHom.id R) Function.surjective_id).trans
      (congrArg (fun K : Ideal R => Module.length R (R ⧸ K))
        ((RingHom.injective_iff_ker_eq_bot (RingHom.id R)).mp Function.injective_id))
  rw [← heq]
  by_contra h
  have : IsArtinianRing R := (isArtinianRing_iff_isFiniteLength R).mpr
    (Module.length_ne_top_iff.mp h)
  have hzero : Ring.KrullDimLE 0 R := isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  have hle := (Ring.krullDimLE_iff (R := R)).mp hzero
  rw [hdim] at hle
  norm_num at hle

private theorem colength_lt_of_le_maximalIdeal_mul
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hI : Module.length R (R ⧸ I) ≠ ⊤)
    (hR : Module.length R (R ⧸ (⊥ : Ideal R)) = ⊤)
    (hIJ : I ≤ IsLocalRing.maximalIdeal R * J) :
    (Module.length R (R ⧸ J)).toNat < (Module.length R (R ⧸ I)).toNat := by
  have hJ : J ≠ ⊥ := by
    intro h
    have hIbot : I = ⊥ := by simpa only [h, Ideal.mul_bot, le_bot_iff] using hIJ
    exact hI (hIbot ▸ hR)
  have hlt : I < J := by
    refine lt_of_le_of_ne (hIJ.trans Ideal.mul_le_right) ?_
    intro h
    have hN : (J : Submodule R R) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) J
        (IsNoetherian.noetherian J) (h ▸ hIJ) (by
          rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
    exact hJ hN
  have hle : Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
    simpa only [Module.length_quotient] using Order.coheight_anti hlt.le
  have hJfin : Module.length R (R ⧸ J) ≠ ⊤ := ne_top_of_le_ne_top hI hle
  have hlength : Module.length R (R ⧸ J) < Module.length R (R ⧸ I) := by
    simpa only [Module.length_quotient] using
      (Order.coheight_strictAnti hlt (show Order.coheight J < ⊤ from
        (by simpa only [Module.length_quotient] using hJfin.lt_top)))
  rw [← ENat.natCast_toNat hJfin, ← ENat.natCast_toNat hI] at hlength
  exact_mod_cast hlength

private noncomputable abbrev localIntersectionLength {X : Scheme.{u}}
    (I J : X.IdealSheafData) (q : X) (hq : q ∈ (I ⊔ J).support) : ℕ∞ :=
  let d : (I ⊔ J).subscheme := ⟨q, hq⟩
  letI : Algebra (X.presheaf.stalk q) ((I ⊔ J).subscheme.presheaf.stalk d) :=
    ((I ⊔ J).subschemeι.stalkMap d).hom.toAlgebra
  Module.length (X.presheaf.stalk q) ((I ⊔ J).subscheme.presheaf.stalk d)

private theorem localIntersectionLength_eq_colength {X : Scheme.{u}}
    (I J : X.IdealSheafData) (q : X) (hq : q ∈ (I ⊔ J).support) :
    localIntersectionLength I J q hq = Module.length (X.presheaf.stalk q)
      ((X.presheaf.stalk q) ⧸ (AlgebraicGeometry.IdealSheafData.stalk I q ⊔
        AlgebraicGeometry.IdealSheafData.stalk J q)) := by
  let d : (I ⊔ J).subscheme := ⟨q, hq⟩
  have hker := stalk_ker (I ⊔ J).subschemeι d
  rw [Scheme.IdealSheafData.ker_subschemeι, stalk_sup] at hker
  exact (length_eq_length_quotient_ker ((I ⊔ J).subschemeι.stalkMap d).hom
    ((I ⊔ J).subschemeι.stalkMap_surjective d)).trans
    (congrArg (fun K : Ideal (X.presheaf.stalk q) =>
      Module.length (X.presheaf.stalk q) ((X.presheaf.stalk q) ⧸ K)) hker.symm)

private theorem localIntersectionLength_eq_colength_comap {X C : Scheme.{u}}
    (f : C ⟶ X) [IsClosedImmersion f] (J : X.IdealSheafData)
    (c : C) (p : X) (hp : f c = p) (hc : p ∈ (f.ker ⊔ J).support) :
    localIntersectionLength f.ker J p hc =
      Module.length (C.presheaf.stalk c)
        ((C.presheaf.stalk c) ⧸ AlgebraicGeometry.IdealSheafData.stalk (J.comap f) c) := by
  subst p
  rw [localIntersectionLength_eq_colength, stalk_ker, IdealSheafData.stalk_comap]
  exact length_quotient_sup_ker (f.stalkMap c).hom (f.stalkMap_surjective c) _

private theorem localIntersectionLength_eq_colength_subscheme {X : Scheme.{u}}
    (I J : X.IdealSheafData) (c : I.subscheme) (p : X) (hp : I.subschemeι c = p)
    (hc : p ∈ (I ⊔ J).support) :
    localIntersectionLength I J p hc = Module.length (I.subscheme.presheaf.stalk c)
      ((I.subscheme.presheaf.stalk c) ⧸
        AlgebraicGeometry.IdealSheafData.stalk (J.comap I.subschemeι) c) := by
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using
    localIntersectionLength_eq_colength_comap I.subschemeι J c p hp
      (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using hc)

/-- Part (3): an intersection surviving the blowup has smaller multiplicity. -/
@[stacks 0BI7 "part (3)"] public theorem
    strictTransform_intersectionMultiplicity_lt
    (S : AlgebraicGeometry.IntersectionMultiplicityContext.{u})
    (yPoint : S.y.subscheme) (hyPoint : S.y.subschemeι yPoint = S.p)
    (hregular : IsRegularLocalRing (S.y.subscheme.presheaf.stalk yPoint))
    (q : (AlgebraicGeometry.blowUp (centerIdeal S.p S.p_isClosed)))
    (hqExceptional : q ∈
      (AlgebraicGeometry.exceptionalIdeal (centerIdeal S.p S.p_isClosed)).support)
    (hq : q ∈ ((transformIdeal S.y S.p S.p_isClosed) ⊔
      (transformIdeal S.z S.p S.p_isClosed)).support) :
    intersectionLength (transformIdeal S.y S.p S.p_isClosed)
      (transformIdeal S.z S.p S.p_isClosed) q hq <
      S.intersectionMultiplicity := by
  have : IsLocallyNoetherian S.X := S.locallyNoetherian
  have : IsIntegral S.y.subscheme := S.integralY
  have : IsLocallyNoetherian S.y.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian S.y.subschemeι
  let f := transformToBlowUp S.y S.p S.p_isClosed
  let fZ := transformToBlowUp S.z S.p S.p_isClosed
  let g := transformToCurve S.y S.p S.p_isClosed
  let E := AlgebraicGeometry.exceptionalIdeal (centerIdeal S.p S.p_isClosed)
  have : IsClosedImmersion f := isClosedImmersion_transformToBlowUp _ _ _
  have : IsClosedImmersion fZ := isClosedImmersion_transformToBlowUp _ _ _
  have : IsIso g := strictTransformToCurve_isIso S.y S.dimensionY S.p S.p_isClosed
    yPoint hyPoint hregular
  obtain ⟨c, rfl⟩ := mem_range_of_mem_support_ker f
    (Scheme.IdealSheafData.support_antitone le_sup_left hq)
  obtain ⟨z, hz⟩ := mem_range_of_mem_support_ker fZ
    (Scheme.IdealSheafData.support_antitone le_sup_right hq)
  have hc : S.y.subschemeι (g c) = S.p :=
    (congrArg (fun k => k c) (transformToBlowUp_comp_toBase S.y S.p S.p_isClosed)).symm.trans
      ((mem_exceptionalIdeal_support_iff S.p S.p_isClosed (f c)).mp hqExceptional)
  let R := (transform S.y S.p S.p_isClosed).presheaf.stalk c
  let J := S.z.comap (AlgebraicGeometry.blowUpToBase (centerIdeal S.p S.p_isClosed))
  let K := transformIdeal S.z S.p S.p_isClosed
  let I₀ : Ideal R := AlgebraicGeometry.IdealSheafData.stalk (J.comap f) c
  let I₁ : Ideal R := AlgebraicGeometry.IdealSheafData.stalk (K.comap f) c
  have : IsNoetherianRing R := isNoetherianRing_of_surjective
    (S.y.subscheme.presheaf.stalk (g c)) R (g.stalkMap c).hom (g.stalkMap_surjective c)
  have heq : (S.z.comap S.y.subschemeι).comap g = J.comap f := by
    rw [← Scheme.IdealSheafData.comap_comp, ← transformToBlowUp_comp_toBase,
      Scheme.IdealSheafData.comap_comp]
  have hOldCast : (S.intersectionMultiplicity : ℕ∞) = Module.length R (R ⧸ I₀) :=
    S.intersectionMultiplicity_natCast_eq_length.trans <|
      (localIntersectionLength_eq_colength_subscheme S.y S.z (g c) S.p hc
        S.p_mem_intersection).trans <|
        (colength_comap_iso g (S.z.comap S.y.subschemeι) c).trans <|
          congrArg (fun T => Module.length R (R ⧸ IdealSheafData.stalk T c)) heq
  have hfinite : Module.length R (R ⧸ I₀) ≠ ⊤ := hOldCast ▸ ENat.natCast_ne_top _
  have hwhole : Module.length R (R ⧸ (⊥ : Ideal R)) = ⊤ := by
    have hdim := ringKrullDim_stalk_eq_one_of_integral_curve
      S.y.subscheme S.dimensionY (g c)
      (subschemePoint_isClosed_of_ambientPoint_isClosed S.y S.p S.p_isClosed (g c) hc)
    have hright := congrArg (fun L : Ideal R => Module.length R (R ⧸ L))
      ((congrArg (fun T : (transform S.y S.p S.p_isClosed).IdealSheafData =>
        AlgebraicGeometry.IdealSheafData.stalk T c) (Scheme.IdealSheafData.comap_bot g)).trans
          (stalk_bot c))
    have hleft := congrArg (fun L : Ideal (S.y.subscheme.presheaf.stalk (g c)) =>
      Module.length (S.y.subscheme.presheaf.stalk (g c))
        ((S.y.subscheme.presheaf.stalk (g c)) ⧸ L)) (stalk_bot (g c))
    exact hright.symm.trans ((colength_comap_iso g ⊥ c).symm.trans
      (hleft.trans (length_quotient_bot_eq_top_of_ringKrullDim_eq_one _ hdim)))
  have hZcenter : S.z ≤ centerIdeal S.p S.p_isClosed := by
    apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    rintro r rfl
    exact Scheme.IdealSheafData.support_antitone le_sup_right S.p_mem_intersection
  have hzE : fZ z ∈ E.support := hz.symm ▸ hqExceptional
  have htotal : IdealSheafData.stalk J (f c) ≤
      IdealSheafData.stalk E (f c) * IdealSheafData.stalk K (f c) := by
    rw [← hz]
    exact totalTransform_stalk_le_exceptional_mul_strictTransform
      S.z S.p S.p_isClosed hZcenter z hzE
  have hmax : IdealSheafData.stalk (E.comap f) c = IsLocalRing.maximalIdeal R :=
    stalk_comap_exceptionalIdeal_transformToBlowUp S.y S.p S.p_isClosed c hc
  have hle : I₀ ≤ IsLocalRing.maximalIdeal R * I₁ := by
    have h := Ideal.map_mono (f := (f.stalkMap c).hom) htotal
    rwa [Ideal.map_mul, ← IdealSheafData.stalk_comap, ← IdealSheafData.stalk_comap,
      ← IdealSheafData.stalk_comap, hmax] at h
  have hNew : intersectionLength (transformIdeal S.y S.p S.p_isClosed) K (f c) hq =
      (Module.length R (R ⧸ I₁)).toNat :=
    congrArg ENat.toNat (localIntersectionLength_eq_colength_comap f K c (f c) rfl hq)
  rw [hNew, ← ENat.toNat_natCast S.intersectionMultiplicity, hOldCast]
  exact colength_lt_of_le_maximalIdeal_mul I₀ I₁ hfinite hwhole hle

end AlgebraicGeometry

end
