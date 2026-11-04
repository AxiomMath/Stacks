module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Chart
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RelativeDifference
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The containing subscheme of Stacks tag 063W

Stacks tag 063W concerns a closed subscheme `T` of a scheme `X` flat and locally of finite
presentation over a base `S`, at a point `x` of `T` whose fibre `T_s ⊆ X_s` is a quasi-regular
immersion near `x`.  Its **first** item assumes nothing else:  it asks for an open `U ∋ x` and a
relative quasi-regular immersion `Z ⊆ U` over `S` with `Z_s = T_s ∩ U_s` and `T ∩ U ⊆ Z`.  The
second item, which adds flatness and finite presentation of `T` and concludes `T ∩ U = Z`, is
`Stacks.AlgebraicGeometry.exists_mem_isRelativeQuasiRegularImmersion_of_flatAt`.

This file proves the first item.  Its heart is an affine chart:  an affine open `V ∋ x` lying
over an affine open `W` of the base and a finite family `c` of sections of the ideal of `T` over
`V` which is weakly regular in `Γ(X, V)`, whose quotient is flat over `Γ(S, W)`, and which
generates the ideal of `T` on the whole of the fibre `V_s`.  The closed subscheme `V(c) ⊆ V` is
the `Z` of the item:  weak regularity and flatness of the quotient are the affine criterion for
`Z ⊆ V` to be a relative quasi-regular immersion over `S` (Stacks tag 063G), the clause about the
fibre is `Z_s = T_s ∩ V_s`, and `c ⊆ I(T)` is `T ∩ V ⊆ Z`.  `Z` itself is
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop` applied to the ideal `c` generates in
`Γ(V, ⊤)`, and the three conditions are read off it by transport along
`AlgebraicGeometry.Scheme.Opens.topIso`.

The input the tag needed and the tree did not have is the middle clause:  the family produced
from the fibre at `x` generates the ideal of `T` not just in the local ring of the fibre but on a
whole neighbourhood.  The flat spreading out of Stacks 046Y
(`Stacks.RingTheory.SpreadingOut.exists_notMem_map_eq_map_away`) cannot supply it, since it
assumes the flatness of `B_q/IB_q` that item (1) drops.  Its substitute,
`Stacks.AlgebraicGeometry.exists_mem_forall_ideal_comap_fiberι_eq_span`, is a spreading out
inside the fibre, which is a Noetherian scheme because `f` is locally of finite type.

## Main results

* `Stacks.AlgebraicGeometry.isAffineHom_fiberι`: the inclusion of a fibre is an affine morphism,
  so the fibre of an affine open is an affine open of the fibre.
* `Stacks.AlgebraicGeometry.flat_of_isAffine_of_flat_appLE`: a morphism from an affine scheme
  into an affine open of the target is flat as soon as its map of sections is.
* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_subschemeι_of_isWeaklyRegular`: on an affine
  scheme a closed subscheme cut out by a weakly regular family of global sections is a
  quasi-regular immersion.
* `Stacks.AlgebraicGeometry.map_atPrime_eq_of_map_eq` and
  `Stacks.AlgebraicGeometry.flat_quotient_map_away_of_abstract`: passage between abstract and
  concrete localizations.
* `Stacks.AlgebraicGeometry.exists_mem_forall_ideal_comap_fiberι_eq_span`: **the fibre ideal of a
  chart spreads out from the point.**
* `Stacks.AlgebraicGeometry.exists_affineOpen_isWeaklyRegular_flat_quotient_ideal_fibre`: **the
  affine chart of item (1).**
* `Stacks.AlgebraicGeometry.isWeaklyRegular_topIso_inv`, `Stacks.AlgebraicGeometry.ι_appLE_top`,
  `Stacks.AlgebraicGeometry.appLE_comp_ι_top`,
  `Stacks.AlgebraicGeometry.ofIdealTop_ideal_top` and
  `Stacks.AlgebraicGeometry.flat_quotient_comp_of_bijective`: the transport along `topIso` that
  turns the chart into an ideal sheaf on `V`.
* `Stacks.AlgebraicGeometry.isRelativeQuasiRegularImmersion_subschemeι_of_chart`: a closed
  subscheme of the chart cut out by the chart family is a relative quasi-regular immersion.
* `Stacks.AlgebraicGeometry.exists_mem_isRelativeQuasiRegularImmersion_le_comap`: **item (1) of
  Stacks tag 063W.**

## Implementation notes

The spreading out inside the fibre runs over the affine open `(f.fiberι s)⁻¹V` of the fibre, whose
ring of sections is Noetherian;  the ideal of `T` there is the extension of the ideal on `V`
(`Stacks.IdealSheaf.ideal_comap_appLE`), and the two ideals are compared in the local ring at the
point, where the comparison is the hypothesis of the lemma.  Equality at the point then holds away
from one element
(`Stacks.RingTheory.SpreadingOut.exists_notMem_map_eq_map_away_of_map_atPrime_eq`), and the basic
open it cuts out on the fibre is the preimage of an open of `X` because the inclusion of a fibre is
a topological embedding.  That open is the neighbourhood the lemma returns, and the conclusion is
asserted over every affine open inside it, which is what lets the chart be shrunk again afterwards.

The chart itself is the basic open of `g₁ * (g₂ * s)`:  `g₁` carries the weak regularity of the
family, `g₂` carries the flatness of its quotient, and `s` carries the fibre equality.  Stacks
062Y (3) is therefore not used as a whole — its two halves
(`Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime` and
`Stacks.RingTheory.SpreadingOut.exists_notMem_forall_flat_atPrime_quotient_of_fg` followed by
`Stacks.RingTheory.SpreadingOut.flat_quotient_away_of_forall_of_fg`) are applied separately, so
that both survive the third shrinking.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 046Y](https://stacks.math.columbia.edu/tag/046Y)
* [Stacks Project, Lemma 31.20.2 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry RingTheory.Sequence
open Stacks.RingTheory.SpreadingOut
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **The inclusion of a fibre is an affine morphism.**  It is a base change of the morphism from
the spectrum of a residue field, whose source has a single point. -/
instance isAffineHom_fiberι (f : X ⟶ S) (s : S) : IsAffineHom (f.fiberι s) := by
  have : IsAffineHom (S.fromSpecResidueField s) :=
    ⟨fun _ _ => IsAffineOpen.of_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)⟩
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (CategoryTheory.IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip inferInstance

/-- **Flatness of a morphism from an affine scheme into an affine open of the target.** -/
theorem flat_of_isAffine_of_flat_appLE {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ S)
    {W : S.Opens} (hW : IsAffineOpen W) (hle : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ W)
    (h : (g.appLE W ⊤ hle).hom.Flat) : Flat g := by
  have _ : IsAffine W.toScheme := hW
  have _ : IsAffine (⊤ : Y.Opens).toScheme := isAffineOpen_top Y
  have htop : (g.resLE W ⊤ hle).appTop =
      W.topIso.hom ≫ g.appLE W ⊤ hle ≫ (⊤ : Y.Opens).topIso.inv :=
    Scheme.Hom.resLE_app_top g hle
  have hres : Flat (g.resLE W ⊤ hle) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), htop, ← Category.assoc]
    exact (RingHom.Flat.respectsIso.cancel_right_isIso _ (⊤ : Y.Opens).topIso.inv).mpr
      ((RingHom.Flat.respectsIso.cancel_left_isIso W.topIso.hom _).mpr h)
  have hfac : (⊤ : Y.Opens).ι ≫ g = g.resLE W ⊤ hle ≫ W.ι := (Scheme.Hom.resLE_comp_ι g hle).symm
  have _ : Flat ((⊤ : Y.Opens).ι ≫ g) := hfac ▸ inferInstance
  have hiso : Y.topIso.inv ≫ (⊤ : Y.Opens).ι ≫ g = g := by
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  exact hiso ▸ inferInstance

/-- **A closed subscheme of an affine scheme cut out by a weakly regular family of global
sections is a quasi-regular immersion.** -/
theorem isQuasiRegularImmersion_subschemeι_of_isWeaklyRegular {Y : Scheme.{u}} [IsAffine Y]
    (Z : Y.IdealSheafData) {r : ℕ} (c : Fin r → Γ(Y, ⊤))
    (hgen : Z.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span (Set.range c))
    (hwr : IsWeaklyRegular Γ(Y, ⊤) (List.ofFn c)) :
    IsQuasiRegularImmersion Z.subschemeι := by
  refine isQuasiRegularImmersion_of_isQuasiRegularIdealSheaf _ ?_
  refine (isQuasiRegularIdealSheaf_iff_exists_affine_generators Y _).mpr fun z _ => ?_
  exact ⟨⟨⊤, isAffineOpen_top Y⟩, trivial, r, c,
    isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span _ (isAffineOpen_top Y) c
      ((Z.ker_subschemeι_app ⟨⊤, isAffineOpen_top Y⟩).trans hgen),
    isQuasiRegular_of_isWeaklyRegular _ hwr⟩

/-- **An equality of extended ideals in an abstract localization at a prime holds in the concrete
localization at that prime.** -/
theorem map_atPrime_eq_of_map_eq {B O : Type*} [CommRing B] [CommRing O] [Algebra B O]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime O q] (J I : Ideal B)
    (h : I.map (algebraMap B O) = J.map (algebraMap B O)) :
    I.map (algebraMap B (Localization.AtPrime q))
      = J.map (algebraMap B (Localization.AtPrime q)) := by
  set ε : Localization.AtPrime q →+* O :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) O).toRingEquiv.toRingHom
    with hε
  have key : ∀ K : Ideal B,
      Ideal.map ε (K.map (algebraMap B (Localization.AtPrime q))) = K.map (algebraMap B O) := by
    intro K
    rw [hε, Ideal.map_map]
    exact congrArg (fun φ : B →+* O => Ideal.map φ K) (RingHom.ext fun z =>
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) O).commutes z)
  have hbij : Function.Bijective ε :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) O).bijective
  have h2 := congrArg (Ideal.comap ε) ((key I).trans (h.trans (key J).symm))
  rwa [Ideal.comap_map_of_surjective _ hbij.2, Ideal.comap_map_of_surjective _ hbij.2,
    Ideal.comap_bot_of_injective _ hbij.1, sup_bot_eq, sup_bot_eq] at h2

/-- **Flatness of the quotient by an extended ideal, moved to an abstract localization away from
an element.**  This is the `Away` counterpart of
`Stacks.AlgebraicGeometry.flat_quotient_map_atPrime_of_abstract`. -/
theorem flat_quotient_map_away_of_abstract {A B O : Type*} [CommRing A] [CommRing B] [CommRing O]
    [Algebra A B] [Algebra B O] [Algebra A O] [IsScalarTower A B O] (g : B)
    [IsLocalization.Away g O] (I : Ideal B)
    (hflat : Module.Flat A (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g)))) :
    Module.Flat A (O ⧸ I.map (algebraMap B O)) := by
  have hmap : I.map (algebraMap B (Localization.Away g)) = Ideal.map
      (IsLocalization.algEquiv (Submonoid.powers g) O
        (Localization.Away g)).toRingEquiv.toRingHom (I.map (algebraMap B O)) := by
    rw [Ideal.map_map]
    exact (congrArg (fun φ : B →+* Localization.Away g => Ideal.map φ I) (RingHom.ext fun z =>
      (IsLocalization.algEquiv (Submonoid.powers g) O (Localization.Away g)).commutes z)).symm
  exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlg
    (I.map (algebraMap B O)) (I.map (algebraMap B (Localization.Away g)))
    ((IsLocalization.algEquiv (Submonoid.powers g) O (Localization.Away g)).restrictScalars A)
    hmap).toLinearEquiv

/-- **The map from the stalk of `X` to the stalk of the fibre kills the base's maximal ideal.** -/
private theorem map_fiberStalk_map_maximalIdeal_eq_bot (f : X ⟶ S) (x : X) :
    Ideal.map (((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.comp
        (X.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom.hom)
      (Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))) = ⊥ := by
  have hcomp : ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.comp
        (X.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom.hom
      = (quotientStalkEquivFiberStalk f x).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))) :=
    RingHom.ext fun b => (quotientStalkEquivFiberStalk_mk f x b).symm
  rw [hcomp, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]

/-- **The germ on the fibre of a pulled-back section is the image of its germ on `X`.** -/
private theorem germ_appLE_fiberι (f : X ⟶ S) (x : X) {U : X.Opens} (hxU : x ∈ U)
    (hxA : f.asFiber x ∈ f.fiberι (f x) ⁻¹ᵁ U) (t : Γ(X, U)) :
    ((f.fiber (f x)).presheaf.germ (f.fiberι (f x) ⁻¹ᵁ U) (f.asFiber x) hxA).hom
        (((f.fiberι (f x)).appLE U (f.fiberι (f x) ⁻¹ᵁ U) le_rfl).hom t)
      = (((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.comp
          (X.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom.hom)
        ((X.presheaf.germ U x hxU).hom t) := by
  have hιxU : f.fiberι (f x) (f.asFiber x) ∈ U := hxA
  have h1 := RingHom.congr_fun (stalkMap_hom_comp_germ (f.fiberι (f x))
    (le_refl (f.fiberι (f x) ⁻¹ᵁ U)) hxA hιxU) t
  simp only [RingHom.comp_apply] at h1
  have h2 : (X.presheaf.stalkCongr
        (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom.hom
        ((X.presheaf.germ U x hxU).hom t)
      = (X.presheaf.germ U (f.fiberι (f x) (f.asFiber x)) hιxU).hom t := by
    rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply,
      X.presheaf.germ_stalkSpecializes hxU
        (Inseparable.of_eq (f.fiberι_asFiber x).symm).ge]
  rw [RingHom.comp_apply, h2]
  exact h1.symm

/-- **The extension of the ideal spanned by a finite family is spanned by the images.** -/
private theorem map_span_range_eq {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    {r : ℕ} (c : Fin r → R) :
    (Ideal.span (Set.range c)).map φ = Ideal.span (Set.range fun i => φ (c i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- **A point lies in the basic open of a section outside its prime of the affine open.** -/
private theorem mem_basicOpen_of_notMem_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hxU : x ∈ U) {t : Γ(X, U)} (ht : t ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    x ∈ X.basicOpen t := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have _ := hU.isLocalization_stalk ⟨x, hxU⟩
  have _ := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  rw [X.mem_basicOpen t x hxU]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal t).mpr ht

/-- **Spreading out the fibre ideal of Stacks tag 063W.**  Let `T` be a closed subscheme of `X`,
let `x` be a point of it and let `c` be a family of sections of the ideal of `T` over an affine
open `U ∋ x` which generates that ideal in the local ring of the fibre at `x`.  Then on an open
neighbourhood of `x` inside `U` the family generates the ideal of `T` on the whole fibre. -/
theorem exists_mem_forall_ideal_comap_fiberι_eq_span (f : X ⟶ S) [LocallyOfFiniteType f]
    (T : X.IdealSheafData) (x : X) (hx : x ∈ T.support)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) {r : ℕ} (c : Fin r → Γ(X, U))
    (hcT : ∀ i, c i ∈ T.ideal ⟨U, hU⟩)
    (hgen : stalkIdeal T x hx ≤
      Ideal.span (Set.range fun i => (X.presheaf.germ U x hxU).hom (c i)) ⊔
        Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))) :
    ∃ O : X.Opens, x ∈ O ∧ O ≤ U ∧ ∀ (V : X.Opens) (hV : IsAffineOpen V), V ≤ O →
      ∀ hle : f.fiberι (f x) ⁻¹ᵁ V ≤ f.fiberι (f x) ⁻¹ᵁ U,
        (T.comap (f.fiberι (f x))).ideal
            ⟨f.fiberι (f x) ⁻¹ᵁ V, hV.preimage (f.fiberι (f x))⟩
          = Ideal.span (Set.range fun i =>
              ((f.fiberι (f x)).appLE U (f.fiberι (f x) ⁻¹ᵁ V) hle).hom (c i)) := by
  classical
  have hιx : f.fiberι (f x) (f.asFiber x) = x := f.fiberι_asFiber x
  have hιxU : f.fiberι (f x) (f.asFiber x) ∈ U := by rwa [hιx]
  have hxA : f.asFiber x ∈ f.fiberι (f x) ⁻¹ᵁ U := hιxU
  have hA : IsAffineOpen (f.fiberι (f x) ⁻¹ᵁ U) := hU.preimage (f.fiberι (f x))
  have hιxT : f.fiberι (f x) (f.asFiber x) ∈ T.support := by rwa [hιx]
  have hy : f.asFiber x ∈ (T.comap (f.fiberι (f x))).support := by
    rwa [Scheme.IdealSheafData.support_comap]
  have _ : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber f (f x)
  have _ : IsNoetherianRing Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hA⟩
  -- the germ of the chart of the fibre at the point
  set γ : Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U) →+*
      (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
    ((f.fiber (f x)).presheaf.germ (f.fiberι (f x) ⁻¹ᵁ U) (f.asFiber x) hxA).hom with hγdef
  -- the two ideals of the chart of the fibre: the one of `T`, and the one generated by `c`
  set φ : Γ(X, U) →+* Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U) :=
    ((f.fiberι (f x)).appLE U (f.fiberι (f x) ⁻¹ᵁ U) le_rfl).hom with hφdef
  set J₂ : Ideal Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U) :=
    (T.comap (f.fiberι (f x))).ideal ⟨f.fiberι (f x) ⁻¹ᵁ U, hA⟩ with hJ₂def
  set J₁ : Ideal Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U) :=
    Ideal.span (Set.range fun i => φ (c i)) with hJ₁def
  have hJ₂eq : J₂ = (T.ideal ⟨U, hU⟩).map φ :=
    Stacks.IdealSheaf.ideal_comap_appLE T (f.fiberι (f x)) ⟨U, hU⟩ ⟨_, hA⟩ le_rfl
  have hJ₁₂ : J₁ ≤ J₂ := by
    rw [hJ₂eq, hJ₁def, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem _ (hcT i)
  -- the local ring of the fibre at the point, as a localization of the chart
  let _ : Algebra Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U)
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    (f.fiber (f x)).presheaf.algebra_section_stalk ⟨f.asFiber x, hxA⟩
  have _ : IsLocalization.AtPrime ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (hA.primeIdealOf ⟨f.asFiber x, hxA⟩).asIdeal := hA.isLocalization_stalk _
  have _ : (hA.primeIdealOf ⟨f.asFiber x, hxA⟩).asIdeal.IsPrime :=
    (hA.primeIdealOf ⟨f.asFiber x, hxA⟩).isPrime
  -- the canonical surjection `𝒪_{X, x} → 𝒪_{X_s, x}`
  set θ : X.presheaf.stalk x →+* (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
    ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.comp
      (X.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom.hom with hθdef
  have hθP : Ideal.map θ (Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))) = ⊥ :=
    map_fiberStalk_map_maximalIdeal_eq_bot f x
  have hgermθ : ∀ t : Γ(X, U), γ (φ t) = θ ((X.presheaf.germ U x hxU).hom t) :=
    germ_appLE_fiberι f x hxU hxA
  -- the two ideals agree in the local ring of the fibre at the point
  have hmapeq : Ideal.map γ J₂ = Ideal.map γ J₁ := by
    refine le_antisymm ?_ (Ideal.map_mono hJ₁₂)
    have h₂ : Ideal.map γ J₂ = Ideal.map θ (stalkIdeal T x hx) := by
      rw [hJ₂def, hγdef, ← stalkIdeal_eq_map_germ (T.comap (f.fiberι (f x))) _ hy hA hxA,
        stalkIdeal_comap T (f.fiberι (f x)) (f.asFiber x) hy hιxT,
        ← stalkIdeal_congr T (f.fiberι_asFiber x).symm hx hιxT, Ideal.map_map, hθdef]
    have h₁ : Ideal.map γ J₁ = Ideal.map θ (Ideal.span
        (Set.range fun i => (X.presheaf.germ U x hxU).hom (c i))) := by
      rw [hJ₁def, ← map_span_range_eq, ← map_span_range_eq, Ideal.map_map, Ideal.map_map]
      exact congrArg (fun ψ : Γ(X, U) →+* _ => Ideal.map ψ _) (RingHom.ext hgermθ)
    rw [h₂, h₁]
    refine (Ideal.map_mono hgen).trans ?_
    rw [Ideal.map_sup, hθP, sup_bot_eq]
  -- the equality spreads to a basic open of the chart of the fibre
  obtain ⟨g, hg, heq⟩ := exists_notMem_map_eq_map_away_of_map_atPrime_eq
    (hA.primeIdealOf ⟨f.asFiber x, hxA⟩).asIdeal J₁ J₂ hJ₁₂ (IsNoetherian.noetherian J₂)
    (map_atPrime_eq_of_map_eq _ J₁ J₂ hmapeq)
  have hres : Ideal.map ((f.fiber (f x)).presheaf.map
        (homOfLE ((f.fiber (f x)).basicOpen_le g)).op).hom J₂
      = Ideal.map ((f.fiber (f x)).presheaf.map
        (homOfLE ((f.fiber (f x)).basicOpen_le g)).op).hom J₁ :=
    map_res_basicOpen_eq_of_away hA g J₁ J₂ heq
  have hgbo : f.asFiber x ∈ (f.fiber (f x)).basicOpen g :=
    mem_basicOpen_of_notMem_primeIdealOf hA hxA hg
  -- an open of `X` cutting that basic open out on the fibre
  obtain ⟨G, hGopen, hGpre⟩ := ((f.fiberι (f x)).isEmbedding.isInducing.isOpen_iff
    (s := ((f.fiber (f x)).basicOpen g : Set (f.fiber (f x))))).mp
    ((f.fiber (f x)).basicOpen g).isOpen
  have hxG : x ∈ G := hιx ▸ hGpre.ge hgbo
  refine ⟨U ⊓ ⟨G, hGopen⟩, ⟨hxU, hxG⟩, inf_le_left, fun V hV hVO hle => ?_⟩
  have hVbo : f.fiberι (f x) ⁻¹ᵁ V ≤ (f.fiber (f x)).basicOpen g := fun z hz =>
    hGpre.le (show (f.fiberι (f x)) z ∈ G from (hVO hz).2)
  set ρ : Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ U) →+*
      Γ(f.fiber (f x), f.fiberι (f x) ⁻¹ᵁ V) :=
    ((f.fiber (f x)).presheaf.map (homOfLE hle).op).hom with hρdef
  have hlhs : (T.comap (f.fiberι (f x))).ideal
      ⟨f.fiberι (f x) ⁻¹ᵁ V, hV.preimage (f.fiberι (f x))⟩ = Ideal.map ρ J₂ :=
    ((T.comap (f.fiberι (f x))).map_ideal
      (U := ⟨f.fiberι (f x) ⁻¹ᵁ V, hV.preimage (f.fiberι (f x))⟩)
      (V := ⟨f.fiberι (f x) ⁻¹ᵁ U, hA⟩) hle).symm
  have hrhs : Ideal.span (Set.range fun i =>
      ((f.fiberι (f x)).appLE U (f.fiberι (f x) ⁻¹ᵁ V) hle).hom (c i)) = Ideal.map ρ J₁ := by
    rw [hJ₁def, map_span_range_eq]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    rw [hρdef, hφdef, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  rw [hlhs, hrhs, hρdef, ← map_res_res ((f.fiber (f x)).basicOpen_le g) hVbo hle J₂,
    ← map_res_res ((f.fiber (f x)).basicOpen_le g) hVbo hle J₁, hres]

/-- **Weak regularity on a basic open of a product.**  A family weakly regular after inverting
`g` stays weakly regular on the basic open of `g * t`. -/
private theorem isWeaklyRegular_res_basicOpen_mul {U : X.Opens} (hU : IsAffineOpen U)
    (g t : Γ(X, U)) {r : ℕ} (c : Fin r → Γ(X, U))
    (h : IsWeaklyRegular (Localization.Away g)
      (List.ofFn fun k => algebraMap Γ(X, U) (Localization.Away g) (c k))) :
    IsWeaklyRegular Γ(X, X.basicOpen (g * t))
      (List.ofFn fun k => X.presheaf.map (homOfLE (X.basicOpen_le (g * t))).op (c k)) := by
  have hV₁U : X.basicOpen g ≤ U := X.basicOpen_le g
  have hVV₁ : X.basicOpen (g * t) ≤ X.basicOpen g := by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  have hwr₂ := isWeaklyRegular_res_basicOpen (hU.basicOpen g)
    (X.presheaf.map (homOfLE hV₁U).op t)
    (by rw [X.basicOpen_res t (homOfLE hV₁U).op, Scheme.basicOpen_mul]) hVV₁
    (fun k => X.presheaf.map (homOfLE hV₁U).op (c k))
    (isWeaklyRegular_res_basicOpen_of_away hU g c h)
  have hresc : ∀ k, X.presheaf.map (homOfLE hVV₁).op (X.presheaf.map (homOfLE hV₁U).op (c k))
      = X.presheaf.map (homOfLE (X.basicOpen_le (g * t))).op (c k) := by
    intro k
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  simpa only [hresc] using hwr₂

/-- **Flatness of a quotient on a basic open from flatness after inverting the element.** -/
private theorem flat_quotient_appLE_basicOpen_of_flat_away (f : X ⟶ S) {W : S.Opens} {U : X.Opens}
    (hU : IsAffineOpen U) (hUW : U ≤ f ⁻¹ᵁ W) (g : Γ(X, U)) {r : ℕ} (c : Fin r → Γ(X, U))
    (hflat : letI := (f.appLE W U hUW).hom.toAlgebra
      Module.Flat Γ(S, W) (Localization.Away g ⧸
        (Ideal.span (Set.range c)).map (algebraMap Γ(X, U) (Localization.Away g)))) :
    ((Ideal.Quotient.mk (Ideal.span (Set.range fun k =>
        X.presheaf.map (homOfLE (X.basicOpen_le g)).op (c k)))).comp
      (f.appLE W (X.basicOpen g) ((X.basicOpen_le g).trans hUW)).hom).Flat := by
  letI := (f.appLE W U hUW).hom.toAlgebra
  letI : Algebra Γ(S, W) Γ(X, X.basicOpen g) :=
    (f.appLE W (X.basicOpen g) ((X.basicOpen_le g).trans hUW)).hom.toAlgebra
  have _ : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_basicOpen _
  have halgV : algebraMap Γ(X, U) Γ(X, X.basicOpen g)
      = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom := RingHom.algebraMap_toAlgebra _
  have _ : IsScalarTower Γ(S, W) Γ(X, U) Γ(X, X.basicOpen g) := by
    refine .of_algebraMap_eq fun t => ?_
    have h := congrArg (fun φ : Γ(S, W) ⟶ Γ(X, X.basicOpen g) => φ.hom t)
      (Scheme.Hom.appLE_map f hUW (homOfLE (X.basicOpen_le g)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [halgV]
    exact h.symm
  have hflatV := flat_quotient_map_away_of_abstract (A := Γ(S, W))
    (O := Γ(X, X.basicOpen g)) g (Ideal.span (Set.range c)) hflat
  rw [halgV, map_span_range_eq] at hflatV
  exact RingHom.flat_algebraMap_iff.mpr hflatV

/-- **The ideal generated by the image of a finite family is the extension of its span.** -/
private theorem ofList_ofFn_eq_map_span {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    {r : ℕ} (c : Fin r → R) :
    Ideal.ofList (List.ofFn fun j => φ (c j)) = (Ideal.span (Set.range c)).map φ := by
  rw [map_span_range_eq]
  exact congrArg Ideal.span (Set.ext fun _ => List.mem_ofFn.trans Set.mem_range.symm)

/-- **The affine chart of Stacks tag 063W, item (1).**  Let `f : X ⟶ S` be flat and locally of
finite presentation, let `T` be a closed subscheme of `X` and let `x` be a point of `T` whose
fibre over `f x` is a quasi-regular immersion near `x`.  Then every open neighbourhood of `x`
contains an affine open `V` lying over an affine open `W` of the base, carrying a family `c` of
sections of the ideal of `T` which is weakly regular, whose quotient is flat over `Γ(S, W)`,
which generates the ideal of `T` on the whole fibre of `V`, and whose germs at `x` are a regular
sequence modulo the extended maximal ideal of `𝒪_{S, f x}`.

The closed subscheme `V(c) ⊆ V` is the `Z` of item (1):  the weak regularity and the flatness say
that it is a relative quasi-regular immersion over `S`, the fourth clause says `Z_s = T_s ∩ V_s`,
and `c ⊆ T.ideal` says `T ∩ V ⊆ Z`.  The last clause is what item (3) adds to item (1):  it is
regularity of the germs of `c` in the local ring of the fibre, and it pins the length `r`. -/
theorem exists_affineOpen_isWeaklyRegular_flat_quotient_ideal_fibre (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (T : X.IdealSheafData) (x : X) (hx : x ∈ T.support)
    (hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧ IsQuasiRegularImmersion
      (((T.comap (f.fiberι (f x))).comap V.ι).subschemeι))
    (V₀ : X.Opens) (hxV₀ : x ∈ V₀) :
    ∃ (W : S.Opens) (hW : IsAffineOpen W) (V : X.Opens) (hV : IsAffineOpen V)
        (hVW : V ≤ f ⁻¹ᵁ W) (hxV : x ∈ V), V ≤ V₀ ∧ ∃ (r : ℕ) (c : Fin r → Γ(X, V)),
      (∀ i, c i ∈ T.ideal ⟨V, hV⟩) ∧
        IsWeaklyRegular Γ(X, V) (List.ofFn c) ∧
        ((Ideal.Quotient.mk (Ideal.span (Set.range c))).comp (f.appLE W V hVW).hom).Flat ∧
        (T.comap (f.fiberι (f x))).ideal
            ⟨f.fiberι (f x) ⁻¹ᵁ V, hV.preimage (f.fiberι (f x))⟩
          = Ideal.span (Set.range fun i =>
              ((f.fiberι (f x)).appLE V (f.fiberι (f x) ⁻¹ᵁ V) le_rfl).hom (c i)) ∧
        IsRegular (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
          (List.ofFn fun i => Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
            ((X.presheaf.germ V x hxV).hom (c i))) := by
  classical
  -- the chart: an affine open of the base, and an affine open inside `V₀` above it
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ V₀ ⊓ f ⁻¹ᵁ W from ⟨hxV₀, hxW⟩)
  have hUV₀ : U ≤ V₀ := fun _ h => (hUle h).1
  have hUW : U ≤ f ⁻¹ᵁ W := fun _ h => (hUle h).2
  let _ : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  have _ : Module.Flat Γ(S, W) Γ(X, U) := f.flat_appLE hW hU hUW
  have _ : Algebra.FinitePresentation Γ(S, W) Γ(X, U) := f.finitePresentation_appLE hW hU hUW
  have _ : (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal.IsPrime :=
    (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).isPrime
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  let _ : Algebra Γ(S, W) (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (f.appLE W U hUW).hom).toAlgebra
  have _ : IsScalarTower Γ(S, W) Γ(X, U) (X.presheaf.stalk x) := .of_algebraMap_eq fun _ => rfl
  have halg : ∀ t : Γ(S, W), algebraMap Γ(S, W) (X.presheaf.stalk x) t
      = (f.stalkMap x).hom ((S.presheaf.germ W (f x) hxW).hom t) := fun t =>
    (RingHom.congr_fun (stalkMap_hom_comp_germ f hUW hxU hxW) t).symm
  have hcomap : (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal.comap
        (algebraMap Γ(S, W) Γ(X, U)) = (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW U hU hUW hxU)
  let _ : Algebra Γ(S, W) (S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk ⟨f x, hxW⟩
  have _ : IsLocalization.AtPrime (S.presheaf.stalk (f x))
      (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).asIdeal := hW.isLocalization_stalk ⟨f x, hxW⟩
  have _ : (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).asIdeal.IsPrime :=
    (hW.primeIdealOf (⟨f x, hxW⟩ : ↥W)).isPrime
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have _ : IsScalarTower Γ(S, W) (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_algebraMap_eq halg
  have hP : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
      = ((hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal.comap
          (algebraMap Γ(S, W) Γ(X, U))).map (algebraMap Γ(S, W) (X.presheaf.stalk x)) := by
    rw [hcomap]
    exact map_maximalIdeal_eq_map_of_isLocalization _
  have hstalk : stalkIdeal T x hx
      = (T.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (X.presheaf.stalk x)) :=
    stalkIdeal_eq_map_germ T x hx hU hxU
  have hIq : T.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal :=
    ideal_le_primeIdealOf T hU hxU hx
  -- the fibre data, and the family of sections it produces on the chart
  obtain ⟨r, d, hd, hregd, hled⟩ := exists_mem_stalkIdeal_isRegular_quotient f T x hx hfib
  obtain ⟨c, hcI, hcreg, -, hcspan, hcregO⟩ := exists_mem_isRegular_fibre_atPrime
    (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal (T.ideal ⟨U, hU⟩) d _ hP
    (fun i => hstalk.le (hd i)) hregd (hstalk.ge.trans hled)
  have hgen : stalkIdeal T x hx
      ≤ Ideal.span (Set.range fun i => (X.presheaf.germ U x hxU).hom (c i)) ⊔
        Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) := by
    refine hled.trans (sup_le_sup_right (le_of_eq ?_) _)
    rw [hcspan, map_span_range_eq]
    rfl
  obtain ⟨O₁, hxO₁, -, hO₁fib⟩ :=
    exists_mem_forall_ideal_comap_fiberι_eq_span f T x hx hU hxU c hcI hgen
  -- Stacks 062Y (3), in its two halves
  obtain ⟨hregT, hflatT⟩ := isRegular_atPrime_and_flat_quotients_of_isRegular_fibre
    (A := Γ(S, W)) (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal c hcreg
  obtain ⟨g₁, hg₁, hwr⟩ := exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime
    (A := Γ(S, W)) (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal c (fun i => hIq (hcI i))
    hregT hflatT
  have hflatq : Module.Flat Γ(S, W)
      (Localization.AtPrime (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal ⧸
        (Ideal.span (Set.range c)).map (algebraMap Γ(X, U)
          (Localization.AtPrime (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal))) := by
    have h := hflatT r
    rwa [List.take_of_length_le (by simp), ofList_ofFn_eq_map_span] at h
  obtain ⟨g₂, hg₂, hg₂forall⟩ := exists_notMem_forall_flat_atPrime_quotient_of_fg
    (A := Γ(S, W)) (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal (Ideal.span (Set.range c))
    (Submodule.fg_span (Set.finite_range c))
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i => hIq (hcI i))) hflatq
  -- the chart: the basic open of `g₁ * (g₂ * s)`, inside `O₁`
  obtain ⟨s, hsO₁, hxs⟩ := hU.exists_basicOpen_le (V := O₁) ⟨x, hxO₁⟩ hxU
  have hVbo : X.basicOpen (g₁ * (g₂ * s))
      = X.basicOpen g₁ ⊓ (X.basicOpen g₂ ⊓ X.basicOpen s) := by
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul]
  have hV : IsAffineOpen (X.basicOpen (g₁ * (g₂ * s))) := hU.basicOpen _
  have hVU : X.basicOpen (g₁ * (g₂ * s)) ≤ U := X.basicOpen_le _
  have hxV : x ∈ X.basicOpen (g₁ * (g₂ * s)) :=
    hVbo ▸ ⟨mem_basicOpen_of_notMem_primeIdealOf hU hxU hg₁,
      mem_basicOpen_of_notMem_primeIdealOf hU hxU hg₂, hxs⟩
  have hVO₁ : X.basicOpen (g₁ * (g₂ * s)) ≤ O₁ :=
    (hVbo ▸ fun _ hz => hz.2.2 : X.basicOpen (g₁ * (g₂ * s)) ≤ X.basicOpen s).trans hsO₁
  have hVW : X.basicOpen (g₁ * (g₂ * s)) ≤ f ⁻¹ᵁ W := hVU.trans hUW
  refine ⟨W, hW, X.basicOpen (g₁ * (g₂ * s)), hV, hVW, hxV, hVU.trans hUV₀, r,
    fun k => X.presheaf.map (homOfLE hVU).op (c k), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← T.map_ideal (U := ⟨X.basicOpen (g₁ * (g₂ * s)), hV⟩) (V := ⟨U, hU⟩) hVU]
    exact Ideal.mem_map_of_mem _ (hcI i)
  · exact isWeaklyRegular_res_basicOpen_mul hU g₁ (g₂ * s) c hwr
  · -- flatness of the quotient
    have hflatAway : Module.Flat Γ(S, W) (Localization.Away (g₁ * (g₂ * s)) ⧸
        (Ideal.span (Set.range c)).map
          (algebraMap Γ(X, U) (Localization.Away (g₁ * (g₂ * s))))) := by
      refine flat_quotient_away_of_forall_of_fg (Ideal.span (Set.range c)) (g₁ * (g₂ * s))
        fun Q' hQ' => hg₂forall Q' fun hmem₂ => hQ' ?_
      rw [map_mul, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hmem₂)
    exact flat_quotient_appLE_basicOpen_of_flat_away f hU hUW (g₁ * (g₂ * s)) c hflatAway
  · -- the fibre ideal
    refine (hO₁fib _ hV hVO₁ fun _ hz => hVU hz).trans
      (congrArg Ideal.span (congrArg Set.range (funext fun i => ?_)))
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  · -- regularity of the germs modulo the extended maximal ideal
    have halg : ∀ i, algebraMap Γ(X, U) (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))) (c i)
        = Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
          ((X.presheaf.germ (X.basicOpen (g₁ * (g₂ * s))) x hxV).hom
            (X.presheaf.map (homOfLE hVU).op (c i))) := by
      intro i
      rw [← CommRingCat.comp_apply, X.presheaf.germ_res]
      rfl
    simpa only [halg] using hcregO

/-! ### Item (1) -/

/-- **The ideal of the ideal sheaf attached to an ideal of the global sections.** -/
theorem ofIdealTop_ideal_top {Y : Scheme.{u}} (J : Ideal Γ(Y, ⊤))
    (hY : IsAffineOpen (⊤ : Y.Opens)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, hY⟩ = J := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal,
    show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
  simp

/-- **Weak regularity carried to the global sections of an open subscheme.**  The sections over
an open and the global sections of the open subscheme it defines are isomorphic rings. -/
theorem isWeaklyRegular_topIso_inv {V : X.Opens} {r : ℕ} (c : Fin r → Γ(X, V))
    (hwr : IsWeaklyRegular Γ(X, V) (List.ofFn c)) :
    IsWeaklyRegular Γ(V.toScheme, ⊤) (List.ofFn fun i => V.topIso.inv.hom (c i)) := by
  set e : Γ(X, V) ≃+* Γ(V.toScheme, ⊤) := V.topIso.symm.commRingCatIsoToRingEquiv
  have hmap : (List.ofFn fun i => V.topIso.inv.hom (c i)) = (List.ofFn c).map e := by
    rw [List.map_ofFn]
    rfl
  rw [hmap]
  exact (e.toAddEquiv.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun z _ y => map_mul e z y))).mp hwr

/-- **Restriction along the inclusion of an open subscheme is the comparison isomorphism.** -/
theorem ι_appLE_top (V : X.Opens) (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ h = V.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/-- **Sections of a composite with an open immersion over the whole open subscheme.** -/
theorem appLE_comp_ι_top (f : X ⟶ S) (V : X.Opens) {W : S.Opens} (hVW : V ≤ f ⁻¹ᵁ W)
    (hle : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ W) :
    (V.ι ≫ f).appLE W ⊤ hle = f.appLE W V hVW ≫ V.topIso.inv := by
  have h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun z _ => z.2
  rw [← ι_appLE_top V h]
  exact (Scheme.Hom.appLE_comp_appLE V.ι f W V ⊤ hVW h).symm

/-- **Flatness of a quotient map carried along an isomorphism of the ring being quotiented.** -/
theorem flat_quotient_comp_of_bijective {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    (α : A →+* B) (β : B →+* B') (hβ : Function.Bijective β) (I : Ideal B)
    (h : ((Ideal.Quotient.mk I).comp α).Flat) :
    ((Ideal.Quotient.mk (I.map β)).comp (β.comp α)).Flat := by
  set e := Ideal.quotientEquiv I (I.map β) (RingEquiv.ofBijective β hβ) rfl
  have hcomp : (Ideal.Quotient.mk (I.map β)).comp β
      = (e : B ⧸ I →+* B' ⧸ I.map β).comp (Ideal.Quotient.mk I) :=
    RingHom.ext fun z => rfl
  rw [← RingHom.comp_assoc, hcomp, RingHom.comp_assoc]
  exact (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mpr h

/-- **The chart data makes a closed subscheme a relative quasi-regular immersion.**  If the ideal
of `Z ⊆ V` is generated by a family weakly regular in `Γ(X, V)` whose quotient is flat over
`Γ(S, W)`, then `Z` is a relative quasi-regular immersion over `S`. -/
theorem isRelativeQuasiRegularImmersion_subschemeι_of_chart (f : X ⟶ S) {W : S.Opens}
    (hW : IsAffineOpen W) {V : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ f ⁻¹ᵁ W)
    (hVtop : IsAffineOpen (⊤ : V.toScheme.Opens)) (Z : V.toScheme.IdealSheafData) {r : ℕ}
    (a : Fin r → Γ(X, V))
    (hZtop : Z.ideal ⟨⊤, hVtop⟩ = Ideal.span (Set.range fun i => V.topIso.inv.hom (a i)))
    (hwr : IsWeaklyRegular Γ(X, V) (List.ofFn a))
    (hflat : ((Ideal.Quotient.mk (Ideal.span (Set.range a))).comp (f.appLE W V hVW).hom).Flat) :
    IsRelativeQuasiRegularImmersion (V.ι ≫ f) Z.subschemeι := by
  have _ : IsAffine V.toScheme := hV
  refine ⟨?_, isQuasiRegularImmersion_subschemeι_of_isWeaklyRegular Z _ hZtop
    (isWeaklyRegular_topIso_inv a hwr)⟩
  have _ : IsAffine Z.subscheme := isAffine_of_isAffineHom Z.subschemeι
  have hle : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ W := fun z _ => hVW z.2
  have hflatZ : ((Ideal.Quotient.mk (Z.ideal ⟨⊤, hVtop⟩)).comp
      ((V.ι ≫ f).appLE W ⊤ hle).hom).Flat := by
    rw [hZtop, ← map_span_range_eq V.topIso.inv.hom a, appLE_comp_ι_top f V hVW hle,
      CommRingCat.hom_comp]
    exact flat_quotient_comp_of_bijective (f.appLE W V hVW).hom V.topIso.inv.hom
      (ConcreteCategory.bijective_of_isIso V.topIso.inv) (Ideal.span (Set.range a)) hflat
  have hle₂ : (⊤ : Z.subscheme.Opens) ≤ (Z.subschemeι ≫ V.ι ≫ f) ⁻¹ᵁ W :=
    fun z _ => hle trivial
  exact flat_of_isAffine_of_flat_appLE (Z.subschemeι ≫ V.ι ≫ f) hW hle₂
    (Stacks.Divisors.flat_appLE_of_flat_quotient_map (V.ι ≫ f) Z ⟨⊤, hVtop⟩ ⟨W, hW⟩ hle hflatZ)

/-- **Stacks tag 063W, item (1).**  Let `f : X ⟶ S` be flat and locally of finite presentation,
let `T` be a closed subscheme of `X` and let `x` be a point of `T` whose fibre over `f x` is a
quasi-regular immersion near `x`.  Then there is an open `U ∋ x` and a relative quasi-regular
immersion `Z ⊆ U` over `S` with `T ∩ U ⊆ Z` and `Z_s = T_s ∩ U_s`. -/
@[stacks 063W "item (1): containing"]
theorem exists_mem_isRelativeQuasiRegularImmersion_le_comap (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (T : X.IdealSheafData) (x : X) (hx : x ∈ T.support)
    (hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧ IsQuasiRegularImmersion
      (((T.comap (f.fiberι (f x))).comap V.ι).subschemeι)) :
    ∃ (U : X.Opens) (_ : x ∈ U) (Z : U.toScheme.IdealSheafData),
      IsRelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι ∧ Z ≤ T.comap U.ι ∧
        Z.comap ((f.fiberι (f x)).resLE U (f.fiberι (f x) ⁻¹ᵁ U) le_rfl)
          = (T.comap (f.fiberι (f x))).comap (f.fiberι (f x) ⁻¹ᵁ U).ι := by
  classical
  obtain ⟨W, hW, V, hV, hVW, hxV, -, r, c, hcI, hwr, hflatq, hfibeq, -⟩ :=
    exists_affineOpen_isWeaklyRegular_flat_quotient_ideal_fibre f T x hx hfib ⊤ trivial
  have _ : IsAffine V.toScheme := hV
  have hVtop : IsAffineOpen (⊤ : V.toScheme.Opens) := isAffineOpen_top V.toScheme
  set d : Fin r → Γ(V.toScheme, ⊤) := fun i => V.topIso.inv.hom (c i) with hd
  set Z : V.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range d))
  have hZtop : Z.ideal ⟨⊤, hVtop⟩ = Ideal.span (Set.range d) := ofIdealTop_ideal_top _ hVtop
  refine ⟨V, hxV, Z, isRelativeQuasiRegularImmersion_subschemeι_of_chart f hW hV hVW hVtop Z c
    hZtop hwr hflatq, ?_, ?_⟩
  · -- `T ∩ V ⊆ Z`
    refine Scheme.IdealSheafData.le_of_isAffine ?_
    rw [hZtop, ideal_comap_ι_top T hV hVtop, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem _ (hcI i)
  · -- `Z_s = T_s ∩ V_s`
    have hAaff : IsAffineOpen (f.fiberι (f x) ⁻¹ᵁ V) := hV.preimage (f.fiberι (f x))
    have _ : IsAffine (f.fiberι (f x) ⁻¹ᵁ V).toScheme := hAaff
    have hAtop : IsAffineOpen (⊤ : (f.fiberι (f x) ⁻¹ᵁ V).toScheme.Opens) :=
      isAffineOpen_top _
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine Z
        ((f.fiberι (f x)).resLE V (f.fiberι (f x) ⁻¹ᵁ V) le_rfl),
      ideal_comap_ι_top (T.comap (f.fiberι (f x))) hAaff hAtop, hfibeq, hZtop,
      Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    simp only [Function.comp_apply, hd, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply V.topIso.inv V.topIso.hom, V.topIso.inv_hom_id]
    rfl

end Stacks.AlgebraicGeometry

end
