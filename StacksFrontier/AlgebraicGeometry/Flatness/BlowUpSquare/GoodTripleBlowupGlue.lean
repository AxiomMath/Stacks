module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupUniversal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupTag

/-!
# The universal property of Stacks tag 0GTY relative to a morphism

Let `(X, D, M)` be a triple as in Situation 0F8S.  Stacks tag 0GTY asserts that there is a
unique morphism `b : X' ⟶ X` such that

1. the pullback `D' = b⁻¹D` is defined and `(X', D', Lb^*M)` is a good triple, and
2. every `h : Y ⟶ X` for which `E = h⁻¹D` is defined and `(Y, E, Lh^*M)` is a good triple
   factors uniquely through `b`,

and that over every affine chart `(U, A, f, M^•)` the restriction `b⁻¹(U) ⟶ U` is the blowing
up of `U` in the product of the determinantal ideals `I_i(M^•, f)`.  The morphism is
`AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`, with properties (1) and (2) by
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowup_goodBlowupToBase`.

This file records the universal property relative to an arbitrary morphism `m : Z ⟶ X`, the
locality of goodness on which it rests, and the resulting description of `b` over the domain of
an arbitrary affine chart as a Cartesian square.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupAlong`: for `m : Z ⟶ X`, a morphism
  `p : Y ⟶ Z` such that `p ≫ m` is good for the triple and every `g : T ⟶ Z` with `g ≫ m` good
  factors uniquely through `p`.  For `m = 𝟙 X` this is properties (1) and (2) of tag 0GTY; for
  the inclusion of an open `U` it is the universal property over `U` that the chart blowups
  have.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodOver.comp`: goodness passes to a
  composite `k ≫ h` along which the pullback of `D` is defined.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_forall_comp`: goodness is local
  on the source for the topology of open immersions.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupAlong.isPullback`: comparison
  squares between morphisms with the universal property are Cartesian.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isPullback_blowUpToBase`: **Stacks tag
  0GTY, over an affine chart**: for every affine chart `(U, A, f, M^•)` the part of `b` over
  `U` is the blowing up of `U` in `∏ᵢ I_i(M^•, f)`.

## Implementation notes

Goodness of a morphism `h : Y ⟶ X` is read through charts of `(X, D, M)` rather than of the
pulled-back triple (`isGoodTriple_pullback_iff`): `(Y, h⁻¹D, Lh^*M)` is good if and only if
every point of `h⁻¹D` has an affine neighbourhood `V` mapping into the domain `U` of a chart on
which the extensions `I_i(M^•, f)Γ(Y, V)` are principal.  One direction is part (1) of Stacks
tag 0F8T, the other is the transfer of principality from an arbitrary chart of the pulled-back
triple to the pulled-back chart, Stacks tags 0GST and 0GSS.  In this form the conditions only
involve rings of sections of `Y`, so they transport along open immersions by the isomorphisms
`AlgebraicGeometry.Scheme.Hom.appIso`, which is how goodness is shown to be local.

The universal property over an open `U` is phrased for morphisms into the open subscheme `U`
(`IsGoodBlowupAlong` with `m = U.ι`), the form in which
`AffineChart.existsUnique_lift_chartBlowup` provides it.  The structural fact about it is
`IsGoodBlowupAlong.isPullback`: if `p` has the universal property relative to `m` and `q` has it
relative to `j ≫ m` for an open immersion `j`, then any morphism from the source of `q` to that
of `p` over `j` makes a Cartesian square.  It identifies the part of `b` over the domain of any
chart with the blowup of that chart.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

open AlgebraicGeometry

namespace Stacks.Divisors

/-- **Being an effective Cartier divisor is local for the topology of open immersions.**  If a
jointly surjective family of open immersions `qᵢ : Yᵢ ⟶ X` pulls `J` back to effective Cartier
divisors, then `J` is an effective Cartier divisor: a nonzerodivisor generating the ideal of
`J.comap qᵢ` on an affine open `V` of `Yᵢ` transports to the affine open `qᵢ(V)` of `X` along
the isomorphism of rings of sections that an open immersion provides. -/
theorem isEffectiveCartierDivisor_of_forall_comap {X : Scheme.{u}} (J : X.IdealSheafData)
    {ι : Type*} {Y : ι → Scheme.{u}} (q : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (q i)]
    (hq : ∀ x : X, ∃ i, x ∈ Set.range (q i))
    (h : ∀ i, IsEffectiveCartierDivisor (J.comap (q i))) : IsEffectiveCartierDivisor J := by
  refine isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨i, z, rfl⟩ := hq x
  obtain ⟨V, hzV, -, g, hg, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le (J.comap (q i)) (h i) z ⊤ trivial
  have hsurj : Function.Surjective ((q i).appIso (V : (Y i).Opens)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso _).2
  refine ⟨q i ''ᵁ (V : (Y i).Opens), V.2.image_of_isOpenImmersion (q i), ⟨z, hzV, rfl⟩,
    ((q i).appIso (V : (Y i).Opens)).inv g,
    isRegular_ringEquiv ((q i).appIso (V : (Y i).Opens)).symm.commRingCatIsoToRingEquiv hg, ?_⟩
  rw [← Ideal.map_comap_of_surjective _ hsurj
      (J.ideal ⟨q i ''ᵁ (V : (Y i).Opens), V.2.image_of_isOpenImmersion (q i)⟩),
    ← Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (q i) V, hgen, Ideal.map_span,
    Set.image_singleton]

end Stacks.Divisors

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}}

/-! ### Goodness read through charts of the base -/

/-- **Goodness of a pulled-back triple, read through charts of the base.**  For `h : Y ⟶ X`
along which `h⁻¹D` is defined, `(Y, h⁻¹D, Lh^*M)` is a good triple if and only if every point
of `h⁻¹D` lies in an affine open `V ⊆ Y` mapping into the domain `U` of an affine chart
`(U, A, f, M^•)` of `(X, D, M)` such that every extension `I_i(M^•, f)Γ(Y, V)` is principal.

Given such `V`, the pulled-back chart of part (1) of Stacks tag 0F8T has these extensions as
its determinantal ideals.  Conversely, a chart of the pulled-back triple with principal
determinantal ideals at the point is restricted to an affine open `V` lying over the domain of
a chart of `(X, D, M)` through the image of the point, and principality passes to the
pulled-back chart over `V` by `AffineChart.isPrincipal_pullback_determinantalIdeal_of_chart`
(Stacks tags 0GST and 0GSS). -/
theorem isGoodTriple_pullback_iff {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    IsGoodTriple (S.pullback h hD) ↔ ∀ y ∈ (S.D.comap h).supportSet,
      ∃ (C : AffineChart S) (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)),
        y ∈ (V : Y.Opens) ∧ ∀ i : ℤ,
          (Ideal.map (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV).hom
            (C.determinantalIdeal i)).IsPrincipal := by
  constructor
  · intro hgood y hy
    obtain ⟨C', hyC', hC'⟩ := hgood y hy
    obtain ⟨C, hyC⟩ := S.exists_chart_mem (h.base y)
    let W : Y.Opens := C'.U.1
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hyV, hVsub⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ (W : Set Y) ∩ (h ⁻¹ᵁ (C.U : S.X.Opens) : Set Y) from ⟨hyC', hyC⟩)
        (W.isOpen.inter (h ⁻¹ᵁ (C.U : S.X.Opens)).isOpen)
    have hV' : V ≤ W := fun z hz => (hVsub hz).1
    have hV : V ≤ h ⁻¹ᵁ (C.U : S.X.Opens) := fun z hz => (hVsub hz).2
    refine ⟨C, ⟨V, hVaff⟩, hV, hyV, fun i => ?_⟩
    have : ((C.pullback h hD ⟨V, hVaff⟩ hV).determinantalIdeal i).IsPrincipal :=
      C.isPrincipal_pullback_determinantalIdeal_of_chart h hD
        (C'.restrict ⟨V, hVaff⟩ hV') hV i
        (C'.isPrincipal_restrict_determinantalIdeal ⟨V, hVaff⟩ hV' (hC' i))
    rwa [C.pullback_determinantalIdeal] at this
  · intro H y hy
    obtain ⟨C, V, hV, hyV, hprin⟩ := H y hy
    refine ⟨C.pullback h hD V hV, hyV, fun i => ?_⟩
    rw [C.pullback_determinantalIdeal]
    exact hprin i

/-- **Goodness passes to composites.**  If `h : Y ⟶ X` is good for the triple and `k : Z ⟶ Y`
is a morphism along which the pullback of `D` is still defined, then `k ≫ h` is good for the
triple.  In the form of `isGoodTriple_pullback_iff` this is the observation that the extension
of a principal ideal is principal. -/
theorem IsGoodOver.comp {Y Z : Scheme.{u}} {h : Y ⟶ S.X} (hh : S.IsGoodOver h) (k : Z ⟶ Y)
    (hk : Stacks.Divisors.IsPullbackDefined (k ≫ h) S.D) : S.IsGoodOver (k ≫ h) where
  pullbackDefined := hk
  isGoodTriple := by
    refine (isGoodTriple_pullback_iff (k ≫ h) hk).2 fun z hz => ?_
    have hz' : k.base z ∈ (S.D.comap h).supportSet := by
      have h1 : z ∈ ((S.D.comap h).comap k).support := by
        rwa [← Scheme.IdealSheafData.comap_comp]
      rwa [Scheme.IdealSheafData.support_comap] at h1
    obtain ⟨C, V, hV, hzV, hprin⟩ :=
      (isGoodTriple_pullback_iff h hh.pullbackDefined).1 hh.isGoodTriple _ hz'
    obtain ⟨-, ⟨W, hWaff, rfl⟩, hzW, hWsub⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open
        (show z ∈ (k ⁻¹ᵁ (V : Y.Opens) : Set Z) from hzV) (k ⁻¹ᵁ (V : Y.Opens)).isOpen
    have hW : W ≤ k ⁻¹ᵁ (V : Y.Opens) := hWsub
    have hW' : W ≤ (k ≫ h) ⁻¹ᵁ (C.U : S.X.Opens) := fun x hx => hV (hW hx)
    refine ⟨C, ⟨W, hWaff⟩, hW', hzW, fun i => ?_⟩
    rw [← Scheme.Hom.appLE_comp_appLE k h _ _ _ hV hW, CommRingCat.hom_comp, ← Ideal.map_map]
    exact (hprin i).map_ringHom _

/-- **Goodness is local on the source.**  If a jointly surjective family of open immersions
`qᵢ : Zᵢ ⟶ Y` has `qᵢ ≫ h` good for the triple for every `i`, then `h` is good for the triple.

The pullback of `D` along `h` is defined by
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_comap`.  At a point `qᵢ(v)` of `h⁻¹D`,
goodness of `qᵢ ≫ h` gives, by `isGoodTriple_pullback_iff`, an affine open `V ∋ v` of `Zᵢ` over
the domain of a chart on which the extended determinantal ideals are principal; the open
immersion identifies `Γ(Zᵢ, V)` with `Γ(Y, qᵢ(V))`, and with it the extensions to the two rings,
so `qᵢ(V)` serves at `qᵢ(v)`. -/
theorem isGoodOver_of_forall_comp {Y : Scheme.{u}} (h : Y ⟶ S.X) {ι : Type*}
    {Z : ι → Scheme.{u}} (q : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (q i)]
    (hq : ∀ y : Y, ∃ i, y ∈ Set.range (q i)) (hgood : ∀ i, S.IsGoodOver (q i ≫ h)) :
    S.IsGoodOver h := by
  have hD : Stacks.Divisors.IsPullbackDefined h S.D :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_forall_comap _ q hq fun i => by
      rw [← Scheme.IdealSheafData.comap_comp]
      exact (hgood i).pullbackDefined
  refine ⟨hD, (isGoodTriple_pullback_iff h hD).2 fun y hy => ?_⟩
  obtain ⟨i, v, rfl⟩ := hq y
  have hv : v ∈ (S.D.comap (q i ≫ h)).supportSet := by
    show v ∈ (S.D.comap (q i ≫ h)).support
    rwa [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.support_comap]
  obtain ⟨C, V, hV, hvV, hprin⟩ :=
    (isGoodTriple_pullback_iff _ (hgood i).pullbackDefined).1 (hgood i).isGoodTriple v hv
  let W : Y.affineOpens := ⟨q i ''ᵁ (V : (Z i).Opens), V.2.image_of_isOpenImmersion (q i)⟩
  have hW : (W : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hV hw
  refine ⟨C, W, hW, ⟨v, hvV, rfl⟩, fun j => ?_⟩
  have key : (q i ≫ h).appLE (C.U : S.X.Opens) (V : (Z i).Opens) hV =
      h.appLE (C.U : S.X.Opens) (W : Y.Opens) hW ≫ ((q i).appIso (V : (Z i).Opens)).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  have hmap : Ideal.map (h.appLE (C.U : S.X.Opens) (W : Y.Opens) hW).hom
      (C.determinantalIdeal j) = Ideal.map ((q i).appIso (V : (Z i).Opens)).inv.hom
        (Ideal.map ((q i ≫ h).appLE (C.U : S.X.Opens) (V : (Z i).Opens) hV).hom
          (C.determinantalIdeal j)) := by
    rw [key, CommRingCat.hom_comp, ← Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
      Iso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  rw [hmap]
  exact (hprin j).map_ringHom _

/-! ### The universal property relative to a morphism -/

/-- A morphism `p : Y ⟶ Z` **has the universal property of Stacks tag 0GTY relative to
`m : Z ⟶ X`** if `p ≫ m` is good for the triple and every `g : T ⟶ Z` with `g ≫ m` good for the
triple factors uniquely through `p`.  For `m = 𝟙 X` these are properties (1) and (2) of the tag
(`isGoodBlowupAlong_id_iff`); for the inclusion of an open `U ⊆ X` it is the universal property
over `U` of the blowup of an affine chart with domain `U`. -/
structure IsGoodBlowupAlong (S : ComplexAndDivisorSituation.{u, d}) {Z : Scheme.{u}}
    (m : Z ⟶ S.X) {Y : Scheme.{u}} (p : Y ⟶ Z) : Prop where
  /-- The composite `p ≫ m` is good for the triple. -/
  isGoodOver : S.IsGoodOver (p ≫ m)
  /-- A morphism to `Z` which is good for the triple after composing with `m` factors uniquely
  through `p`. -/
  existsUnique_lift : ∀ {T : Scheme.{u}} (g : T ⟶ Z), S.IsGoodOver (g ≫ m) →
    ∃! k : T ⟶ Y, k ≫ p = g

/-- Relative to `𝟙 X`, the universal property is properties (1) and (2) of Stacks tag 0GTY. -/
theorem isGoodBlowupAlong_id_iff {Y : Scheme.{u}} {b : Y ⟶ S.X} :
    S.IsGoodBlowupAlong (𝟙 S.X) b ↔ S.IsGoodBlowup b := by
  constructor <;>
    exact fun hb => ⟨by simpa using hb.isGoodOver,
      fun g hg => hb.existsUnique_lift g (by simpa using hg)⟩

namespace IsGoodBlowupAlong

variable {Z Y : Scheme.{u}} {m : Z ⟶ S.X} {p : Y ⟶ Z}

/-- The factorization through `p` of a morphism `g` to `Z` with `g ≫ m` good. -/
def lift (hp : S.IsGoodBlowupAlong m p) {T : Scheme.{u}} (g : T ⟶ Z)
    (hg : S.IsGoodOver (g ≫ m)) : T ⟶ Y :=
  (hp.existsUnique_lift g hg).exists.choose

/-- The factorization through `p` is a factorization. -/
@[reassoc (attr := simp)]
theorem lift_fac (hp : S.IsGoodBlowupAlong m p) {T : Scheme.{u}} (g : T ⟶ Z)
    (hg : S.IsGoodOver (g ≫ m)) : hp.lift g hg ≫ p = g :=
  (hp.existsUnique_lift g hg).exists.choose_spec

/-- Every factorization through `p` is the chosen one. -/
theorem eq_lift (hp : S.IsGoodBlowupAlong m p) {T : Scheme.{u}} {g : T ⟶ Z}
    (hg : S.IsGoodOver (g ≫ m)) {k : T ⟶ Y} (hk : k ≫ p = g) : k = hp.lift g hg :=
  (hp.existsUnique_lift g hg).unique hk (hp.lift_fac g hg)

/-- Two morphisms into the source of `p` agree as soon as their composites with `p` agree and
are good for the triple after composing with `m`. -/
theorem hom_ext (hp : S.IsGoodBlowupAlong m p) {T : Scheme.{u}} {k k' : T ⟶ Y}
    (hk : k ≫ p = k' ≫ p) (hg : S.IsGoodOver ((k ≫ p) ≫ m)) : k = k' :=
  (hp.eq_lift hg rfl).trans (hp.eq_lift hg hk.symm).symm

/-- Two morphisms with the universal property relative to the same `m` are isomorphic over
`Z`.  Each factors through the other, and both composites are identities by uniqueness of the
factorization of a morphism through itself. -/
theorem exists_iso {Y' : Scheme.{u}} {p' : Y' ⟶ Z} (hp : S.IsGoodBlowupAlong m p)
    (hp' : S.IsGoodBlowupAlong m p') : ∃ e : Y' ≅ Y, e.hom ≫ p = p' := by
  refine ⟨⟨hp.lift p' hp'.isGoodOver, hp'.lift p hp.isGoodOver, ?_, ?_⟩,
    hp.lift_fac p' hp'.isGoodOver⟩
  · exact hp'.hom_ext (by simp) (by simpa using hp'.isGoodOver)
  · exact hp.hom_ext (by simp) (by simpa using hp.isGoodOver)

/-- **Restriction of the universal property along an open immersion.**  If `p` has the universal
property relative to `m`, `j : Z' ⟶ Z` is an open immersion and `snd` is the base change of `p`
along `j`, then `snd` has the universal property relative to `j ≫ m`. -/
theorem of_isPullback (hp : S.IsGoodBlowupAlong m p) {Z' P : Scheme.{u}} (j : Z' ⟶ Z)
    [IsOpenImmersion j] {fst : P ⟶ Y} {snd : P ⟶ Z'} (hP : IsPullback fst snd p j) :
    S.IsGoodBlowupAlong (j ≫ m) snd where
  isGoodOver := by
    have : IsOpenImmersion fst := MorphismProperty.of_isPullback hP.flip inferInstance
    rw [← Category.assoc, ← hP.w, Category.assoc]
    exact hp.isGoodOver.comp_of_flat fst
  existsUnique_lift := by
    intro T g hg
    obtain ⟨k, hk, hku⟩ := hp.existsUnique_lift (g ≫ j) (by rwa [Category.assoc])
    refine ⟨hP.lift k g hk, hP.lift_snd _ _ _, fun k' (hk' : k' ≫ snd = g) => hP.hom_ext ?_ ?_⟩
    · rw [hP.lift_fst]
      exact hku _ (show (k' ≫ fst) ≫ p = g ≫ j by
        rw [Category.assoc, hP.w, ← Category.assoc, hk'])
    · exact hk'.trans (hP.lift_snd _ _ _).symm

/-- **Comparison squares between morphisms with the universal property are Cartesian.**  Let
`p : Y ⟶ Z` have the universal property relative to `m`, let `j : Z' ⟶ Z` be an open immersion
and let `q : Y' ⟶ Z'` have the universal property relative to `j ≫ m`.  Then any `a : Y' ⟶ Y`
with `a ≫ p = q ≫ j` exhibits `Y'` as the part of `Y` over `Z'`: the base change of `p` along
`j` has the same universal property as `q` by `IsGoodBlowupAlong.of_isPullback`, so the two are
isomorphic over `Z'`, and `a` is the comparison morphism by uniqueness of factorizations
through `p`. -/
theorem isPullback (hp : S.IsGoodBlowupAlong m p) {Z' Y' : Scheme.{u}} (j : Z' ⟶ Z)
    [IsOpenImmersion j] {m' : Z' ⟶ S.X} (hm : j ≫ m = m') {q : Y' ⟶ Z'}
    (hq : S.IsGoodBlowupAlong m' q) (a : Y' ⟶ Y) (ha : a ≫ p = q ≫ j) :
    IsPullback a q p j := by
  subst hm
  obtain ⟨e, he⟩ := (hp.of_isPullback j (IsPullback.of_hasPullback p j)).exists_iso hq
  have h1 : (e.hom ≫ pullback.fst p j) ≫ p = a ≫ p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he, ha]
  refine IsPullback.of_iso_pullback ⟨ha⟩ e (hp.hom_ext h1 ?_) he
  rw [h1, ha, Category.assoc]
  exact hq.isGoodOver

end IsGoodBlowupAlong

/-- **The blowup of an affine chart has the universal property over the chart.**  This is
clause (1) of Stacks tag 0GTY over the chart,
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.isGoodOver_chartBlowupToBase`, together
with clause (2) over it,
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.existsUnique_lift_chartBlowup`. -/
theorem AffineChart.isGoodBlowupAlong_blowUpToBase (C : AffineChart S) :
    S.IsGoodBlowupAlong (C.U : S.X.Opens).ι (blowUpToBase C.blowupCentreIdealSheaf) :=
  ⟨C.isGoodOver_chartBlowupToBase, fun g hg => C.existsUnique_lift_chartBlowup g hg⟩

/-- **Stacks tag 0GTY, over an affine chart.**  For every affine chart `(U, A, f, M^•)` of the
triple, the part `b⁻¹(U) ⟶ U` of `b` over `U` is the blowing up of `U` in the product
`∏ᵢ I_i(M^•, f)` of the determinantal ideals of the chart: there is a morphism from that blowup
to `X'` making the square with `b` and the inclusion of `U` Cartesian.

The chart need not be one of those used to glue `X'`: the blowup of any chart has the universal
property over its domain, and so does the part of `b` over it. -/
@[stacks 0GTY "over every affine chart, b is the blowing up in the product of the \
determinantal ideals"]
theorem exists_isPullback_blowUpToBase (S : ComplexAndDivisorSituation.{u, d})
    (C : AffineChart S) :
    ∃ e : blowUp C.blowupCentreIdealSheaf ⟶ S.goodBlowup,
      IsPullback e (blowUpToBase C.blowupCentreIdealSheaf) S.goodBlowupToBase
        (C.U : S.X.Opens).ι := by
  have hb := S.isGoodBlowup_goodBlowupToBase
  obtain ⟨e, he, -⟩ := hb.existsUnique_lift C.chartBlowupToBase C.isGoodOver_chartBlowupToBase
  exact ⟨e, (isGoodBlowupAlong_id_iff.2 hb).isPullback (C.U : S.X.Opens).ι (Category.comp_id _)
    C.isGoodBlowupAlong_blowUpToBase e he⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
