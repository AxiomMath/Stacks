module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantSheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.EtaleFlatUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.RingTheory.Etale.Height
public import StacksFrontier.RingTheory.QuasiFinite.Dimension

/-!
# Étaleness of a flat morphism unramified in codimension one

A flat morphism of locally Noetherian schemes which is quasi-finite at a point that is not the
generic point of an irreducible component of its source is étale at that point as soon as it is
unramified at every one-dimensional generization of the point.

## Main results

* `AlgebraicGeometry.etaleAt_of_flat_of_unramifiedAt_codimensionOne` is the étaleness criterion.

## Implementation notes

Flatness is a hypothesis on the whole morphism, so étaleness at the point reduces by Tag 02GV to
G-unramifiedness there, and over a locally Noetherian target that is unramifiedness. The argument
is therefore a transfer of unramifiedness along the étale localization of Tag 02LK, which makes
the morphism finite locally free near the point; the discriminant of Tag 0BJF is then a locally
principal ideal sheaf on the new base whose support is the image of the ramification locus. A
point of positive-dimensional local ring lying in the support of a locally principal ideal sheaf
has a one-dimensional generization still in that support, by Tag 0BJG applied to a local
generator; that generization pulls back to a one-dimensional generization of the original point,
where the hypothesis applies.

The hypothesis is used in contrapositive form: a base point in the support of the discriminant
would produce a ramified point over a one-dimensional generization, which the hypothesis forbids.

Quasi-finiteness at the point only provides affine neighbourhoods on which the morphism is of
finite type, so the typeclass `AlgebraicGeometry.LocallyOfFiniteType` is available for the
restricted morphism and not for the given one. Consequently the statement is reduced to the
restriction before any stalkwise criterion is used, and unramifiedness is pushed from the given
morphism to the restriction through the stalk map, whose formal unramifiedness follows from an
affine witness with no finiteness hypothesis.

## References

* [Stacks Project, Tag 0BJH](https://stacks.math.columbia.edu/tag/0BJH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Dimension of local rings -/

/-- The local ring of a scheme at a point which is not the generic point of an irreducible
component has positive dimension. -/
@[ega "I 2.4.3" "partial"]
private lemma one_le_ringKrullDim_stalk_of_notMem_genericPoints (X : Scheme.{u}) (x : X)
    (hx : x ∉ genericPoints X) : 1 ≤ ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_eq_coheight]
  have hpos : 0 < Order.coheight x :=
    Order.coheight_pos.mpr fun hmax => hx ((mem_genericPoints_iff_isMax X x).mpr hmax)
  simpa only [← WithBot.coe_one] using
    WithBot.coe_le_coe.mpr (Order.one_le_iff_ne_zero.mpr hpos.ne')

/-- For a flat algebra with Noetherian target, a prime which is quasi-finite over the prime it
lies over has the same height as that prime. -/
private lemma height_eq_height_of_liesOver_of_flat_of_quasiFiniteAt
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module.Flat A B]
    (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt A q] : q.height = p.height :=
  let _ : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  le_antisymm (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt p q)
    (Ideal.height_le_height_of_liesOver_of_hasGoingDown p q)

/-- A flat morphism of schemes which is quasi-finite at a point of a locally Noetherian source
does not change the dimension of the local ring there. -/
private lemma ringKrullDim_stalk_eq_of_flat_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [Flat f] (x : X)
    (hqf : f.QuasiFiniteAt x) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have _ : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have _ : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have _ : (IsLocalRing.maximalIdeal B).IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have _ : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have _ : Module.Flat A B :=
    RingHom.flat_algebraMap_iff.mp ((Flat.iff_flat_stalkMap f).mp inferInstance x)
  have _ : Algebra.QuasiFinite A B := RingHom.quasiFinite_algebraMap.mp hqf
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)]
  exact_mod_cast height_eq_height_of_liesOver_of_flat_of_quasiFiniteAt
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)

/-- A point of a locally Noetherian scheme lying in the support of a locally principal ideal
sheaf and not the generic point of an irreducible component has a one-dimensional generization
still lying in that support. -/
private lemma exists_specializes_ringKrullDim_stalk_eq_one_mem_support
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsLocallyPrincipal I)
    (x : X) (hx : x ∉ genericPoints X) (hxI : x ∈ I.support) :
    ∃ x' : X, x' ⤳ x ∧ ringKrullDim (X.presheaf.stalk x') = 1 ∧ x' ∈ I.support := by
  classical
  obtain ⟨U, hxU, hprincipal⟩ := hI x
  let R := Γ(X, U.1)
  let A := X.presheaf.stalk x
  let s : PrimeSpectrum R := U.2.primeIdealOf ⟨x, hxU⟩
  let a : R := hprincipal.generator
  let _ : Algebra R A := (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have _ : IsLocalization.AtPrime A s.asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hsx : U.2.fromSpec s = x := U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hxa : x ∉ X.basicOpen a := by
    have hz := (I.mem_support_iff_of_mem hxU).mp hxI
    rw [Scheme.mem_zeroLocus_iff] at hz
    exact hz a hprincipal.generator_mem
  have haMax : algebraMap R A a ∈ IsLocalRing.maximalIdeal A := by
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff A s.asIdeal a).2 ?_
    by_contra hsa
    have hpre : s ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen a := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen a s).mpr hsa
    exact hxa (hsx ▸ (hpre : U.2.fromSpec s ∈ X.basicOpen a))
  obtain ⟨p, hp, hap, hpheight⟩ :=
    IsLocalRing.exists_isPrime_height_eq_one_of_mem_maximalIdeal A
      (one_le_ringKrullDim_stalk_of_notMem_genericPoints X x hx) (algebraMap R A a) haMax
  have htle : Ideal.under R p ≤ s.asIdeal :=
    calc Ideal.under R p = p.comap (algebraMap R A) := rfl
      _ ≤ (IsLocalRing.maximalIdeal A).comap (algebraMap R A) :=
        Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime p)
      _ = s.asIdeal := IsLocalization.AtPrime.under_maximalIdeal A s.asIdeal
  have hat : a ∈ Ideal.under R p := hap
  have htheight : (Ideal.under R p).height = 1 := by
    rwa [IsLocalization.height_under s.asIdeal.primeCompl p]
  let z : Spec R := ⟨Ideal.under R p, inferInstance⟩
  have hspec : U.2.fromSpec z ⤳ x :=
    hsx ▸ U.2.fromSpec.base.hom.map_specializes ((PrimeSpectrum.le_iff_specializes z s).mp htle)
  refine ⟨U.2.fromSpec z, hspec, ?_, ?_⟩
  · have _ : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion U.2.fromSpec,
      ← idealHeight_eq_coheight (CommRingCat.of R) z]
    exact_mod_cast htheight
  · refine (I.mem_support_iff_of_mem (U := U) (hspec.mem_open U.1.2 hxU)).mpr ?_
    rw [Scheme.mem_zeroLocus_iff]
    intro r hr
    have hrt : r ∈ Ideal.under R p := by
      rw [← hprincipal.span_singleton_generator] at hr
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hat) hr
    have hnot : z ∉ U.2.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact fun hz => (PrimeSpectrum.mem_basicOpen r z).mp hz hrt
    exact hnot

/-- A point with a unique preimage under a closed map is a specialization of every point whose
image is a generization of its image. -/
private lemma specializes_of_specializes_of_isClosedMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (g : X → Y) (hg : IsClosedMap g)
    {x : X} {y : Y} (hunique : ∀ z : X, g z = y → z = x) {x' : X} (hgen : g x' ⤳ y) :
    x' ⤳ x := by
  have hmem : g x' ∈ g '' closure {x'} := ⟨x', subset_closure (Set.mem_singleton x'), rfl⟩
  have hsub : closure ({g x'} : Set Y) ⊆ g '' closure {x'} :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) (hg _ isClosed_closure)
  obtain ⟨z, hz, hzy⟩ := hsub (specializes_iff_mem_closure.mp hgen)
  exact specializes_iff_mem_closure.mpr (hunique z hzy ▸ hz)

/-! ### Unramifiedness and étaleness at a point under restriction -/

/-- An affine witness of unramifiedness at a point makes the stalk map formally unramified. -/
private lemma formallyUnramified_stalkMap_of_unramifiedAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : UnramifiedAt f x) : (f.stalkMap x).hom.FormallyUnramified := by
  obtain ⟨V, hV, hxV, U, hU, hVU, halg⟩ := h
  let _ := (f.appLE U V hVU).hom.toAlgebra
  exact (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mpr
    (Algebra.formallyUnramified_iff_forall.mp halg.formallyUnramified _)

/-- Unramifiedness of a morphism at a point passes to a restriction of the morphism to a
compatible pair of opens containing the point and its image. -/
private lemma unramifiedAt_resLE_of_unramifiedAt {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) [LocallyOfFiniteType (f.resLE U V hVU)]
    (z : V.toScheme) (h : UnramifiedAt f (V.ι z)) : UnramifiedAt (f.resLE U V hVU) z := by
  rw [unramifiedAt_iff_formallyUnramified_stalkMap]
  exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
    (f.resLEStalkMap hVU z)).mpr (formallyUnramified_stalkMap_of_unramifiedAt f (V.ι z) h)

/-- Unramifiedness of a morphism locally of finite type at a point of an open subscheme of its
source is unramifiedness of the morphism at the image point. -/
lemma unramifiedAt_comp_ι_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (W : X.Opens) (y : W.toScheme) :
    UnramifiedAt (W.ι ≫ f) y ↔ UnramifiedAt f (W.ι y) := by
  rw [unramifiedAt_iff_formallyUnramified_stalkMap, unramifiedAt_iff_formallyUnramified_stalkMap,
    Scheme.Hom.stalkMap_comp W.ι f y]
  exact RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ (W.ι.stalkMap y)

/-- Over a locally Noetherian target, unramifiedness at a point is G-unramifiedness there: the
finite-type algebra of sections witnessing it is of finite presentation. -/
alias gUnramifiedAt_of_unramifiedAt :=
  AlgebraicGeometry.gUnramifiedAt_of_unramifiedAt_of_isLocallyNoetherian

/-- Étaleness at a point of an open subscheme of the source is étaleness at the image point. -/
private alias etaleAt_of_etaleAt_comp := AlgebraicGeometry.etaleAt_of_open_precomp

/-- Étaleness at a point is preserved by composing with an open immersion of the target. -/
private lemma etaleAt_comp_of_etaleAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) (h : EtaleAt f x) : EtaleAt (f ≫ j) x := by
  obtain ⟨A, hA, hxA, V, hV, hAV, hEt⟩ := h
  have hW : IsAffineOpen (j ''ᵁ V) := j.isAffineOpen_iff_of_isOpenImmersion.mpr hV
  have hAW : A ≤ (f ≫ j) ⁻¹ᵁ (j ''ᵁ V) := fun z hz => ⟨f z, hAV hz, rfl⟩
  have _ : Etale (f.resLE V A hAV) := etale_resLE_of_appLE_etale f A hA V hV hAV hEt
  have heq : f.resLE V A hAV ≫ (j.isoImage V).hom = (f ≫ j).resLE (j ''ᵁ V) A hAW := by
    refine (cancel_mono (j ''ᵁ V).ι).1 ?_
    rw [Category.assoc, Scheme.Hom.isoImage_hom_ι, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hres : Etale ((f ≫ j).resLE (j ''ᵁ V) A hAW) := by
    rw [← heq]
    infer_instance
  have _ : IsAffine A.toScheme := hA
  have _ : IsAffine (j ''ᵁ V).toScheme := hW
  exact ⟨A, hA, hxA, j ''ᵁ V, hW, hAW,
    (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso (f ≫ j) (j ''ᵁ V) A hAW)).1
      ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hres)⟩

/-! ### Étaleness from unramifiedness in codimension one -/

/-- For a finite flat morphism and an étale morphism out of the same locally Noetherian source,
the local rings at a point and at its two images have the same dimension. -/
private lemma ringKrullDim_stalk_eq_of_isFinite_of_flat_of_etale
    {W Bs Y : Scheme.{u}} [IsLocallyNoetherian W] (p : W ⟶ Bs) [IsFinite p] [Flat p]
    (r : W ⟶ Y) [Etale r] (w : W) :
    ringKrullDim (Bs.presheaf.stalk (p w)) = ringKrullDim (Y.presheaf.stalk (r w)) :=
  (ringKrullDim_stalk_eq_of_flat_of_quasiFiniteAt p w (Scheme.Hom.quasiFiniteAt p w)).symm.trans
    (ringKrullDim_stalk_eq_of_etale r w)

/-- A point of the base of a finite locally free morphism with a unique preimage avoids the
discriminant, provided the morphism is unramified at every point whose image under an étale map
is a one-dimensional generization of the image of that preimage. -/
private lemma notMem_discriminantIdeal_support_of_unramifiedAt_codimensionOne
    {W Bs Y : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Bs]
    (p : W ⟶ Bs) [IsFinite p] [Flat p] [Stacks.Morphisms.IsFiniteLocallyFree p]
    (r : W ⟶ Y) [Etale r] (b : Bs) (v : W) (z : Y)
    (hvuniq : ∀ y : W, p y = b → y = v) (hrv : r v = z) (hbgen : b ∉ genericPoints Bs)
    (hunr : ∀ w : W, r w ⤳ z → ringKrullDim (Y.presheaf.stalk (r w)) = 1 → UnramifiedAt p w) :
    b ∉ (Stacks.Discriminant.discriminantIdeal p).support := by
  intro hbs
  obtain ⟨b', hb'b, hb'dim, hb'supp⟩ :=
    exists_specializes_ringKrullDim_stalk_eq_one_mem_support Bs
      (Stacks.Discriminant.discriminantIdeal p)
      (Stacks.Discriminant.discriminantIdeal_isLocallyPrincipal p) b hbgen hbs
  obtain ⟨w, hwb', hwunr⟩ :=
    (Stacks.Discriminant.mem_discriminantIdeal_support_iff p b').1 hb'supp
  have hpwb : p w ⤳ b := by rwa [hwb']
  have hwv : w ⤳ v := specializes_of_specializes_of_isClosedMap p p.isClosedMap hvuniq hpwb
  have hrw : r w ⤳ z := hrv ▸ r.base.hom.map_specializes hwv
  refine hwunr (hunr w hrw ?_)
  rwa [← ringKrullDim_stalk_eq_of_isFinite_of_flat_of_etale p r w, hwb']

/-- The heart of Tag 0BJH, for a flat morphism locally of finite type between locally Noetherian
schemes which an elementary étale base change has already made finite near the point.

The discriminant of the resulting finite locally free morphism is a locally principal ideal sheaf
on the new base; a base point in its support would, the local ring there being
positive-dimensional, have a one-dimensional generization carrying a ramified point, which the
codimension-one hypothesis forbids. -/
private lemma unramifiedAt_of_isFiniteNeighborhoodAt
    {V' U' : Scheme.{u}} (g : V' ⟶ U') [IsLocallyNoetherian V'] [IsLocallyNoetherian U']
    [LocallyOfFiniteType g] [Flat g] (z : V')
    {Bs : Scheme.{u}} (q : Bs ⟶ U') [Etale q] (b : Bs) (W : (pullback g q).Opens)
    (hfin : IsFinite (W.ι ≫ pullback.snd g q)) (v : W.toScheme)
    (hv : (W.ι ≫ pullback.snd g q) v = b)
    (hvuniq : ∀ y : W.toScheme, (W.ι ≫ pullback.snd g q) y = b → y = v)
    (hrv : (W.ι ≫ pullback.fst g q) v = z)
    (hdim : 1 ≤ ringKrullDim (V'.presheaf.stalk z))
    (hunr : ∀ z' : V', z' ⤳ z → ringKrullDim (V'.presheaf.stalk z') = 1 → UnramifiedAt g z') :
    UnramifiedAt g z := by
  classical
  set p := W.ι ≫ pullback.snd g q
  set r := W.ι ≫ pullback.fst g q
  have _ : IsFinite p := hfin
  have _ : IsLocallyNoetherian (pullback g q) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g q)
  have _ : IsLocallyNoetherian Bs := LocallyOfFiniteType.isLocallyNoetherian q
  have _ : Stacks.Morphisms.IsFiniteLocallyFree p :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian p).2
      ⟨hfin, inferInstance⟩
  -- Unramifiedness of `p` at a point is that of `g` at its image in `V'`.
  have hiff : ∀ w : W, UnramifiedAt g (r w) ↔ UnramifiedAt p w := fun w =>
    (unramifiedAt_iff_of_isPullback (IsPullback.of_hasPullback g q) (W.ι w)).trans
      (unramifiedAt_comp_ι_iff (pullback.snd g q) W w).symm
  -- The local rings at the point and at its image in the new base have the same dimension.
  have hdimb : 1 ≤ ringKrullDim (Bs.presheaf.stalk b) := by
    rwa [← hv, ringKrullDim_stalk_eq_of_isFinite_of_flat_of_etale p r v, hrv]
  have hbgen : b ∉ genericPoints Bs := by
    intro hbg
    rw [(ringKrullDim_stalk_eq_zero_iff_mem_genericPoints Bs b).2 hbg] at hdimb
    norm_num at hdimb
  have hbdisc : b ∉ (Stacks.Discriminant.discriminantIdeal p).support :=
    notMem_discriminantIdeal_support_of_unramifiedAt_codimensionOne p r b v z hvuniq hrv hbgen
      fun w hrw hdimw => (hiff w).mp (hunr (r w) hrw hdimw)
  -- Hence the finite locally free morphism is unramified over the base point, and that is the
  -- assertion for the given morphism read through the cartesian square.
  have hpv : UnramifiedAt p v := by
    by_contra hn
    exact hbdisc ((Stacks.Discriminant.mem_discriminantIdeal_support_iff p b).2 ⟨v, hv, hn⟩)
  rw [← hrv]
  exact (hiff v).mpr hpv

/-- **Stacks Project, Tag 0BJH.** A flat morphism of locally Noetherian schemes which is
quasi-finite at a point that is not the generic point of an irreducible component of its source
is étale at that point, provided it is unramified at every one-dimensional generization of the
point. -/
@[stacks 0BJH]
public theorem etaleAt_of_flat_of_unramifiedAt_codimensionOne
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (x : X) (hqf : quasiFiniteAt f x) (hgen : x ∉ genericPoints X)
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → UnramifiedAt f x') :
    EtaleAt f x := by
  classical
  obtain ⟨U, V, hxV, hVU, hft⟩ := hqf.1
  have _ : IsAffine V.1.toScheme := V.2
  have _ : IsAffine U.1.toScheme := U.2
  have _ : LocallyOfFiniteType (f.resLE U.1 V.1 hVU) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
      ((RingHom.finiteType_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f U.1 V.1 hVU)).mpr hft)
  set f₀ := f.resLE U.1 V.1 hVU
  set x₀ : V.1.toScheme := ⟨x, hxV⟩
  -- Replace the assertion by the corresponding one for the restriction to the affine opens.
  refine etaleAt_of_etaleAt_comp V.1.ι f x₀ ?_
  rw [← Scheme.Hom.resLE_comp_ι f hVU]
  refine etaleAt_comp_of_etaleAt f₀ U.1.ι x₀ ?_
  -- Flatness is global, so only unramifiedness at the point is at stake.
  refine (etaleAt_iff_isFlatAt_and_gUnramifiedAt f₀ x₀).mpr
    ⟨(Flat.iff_flat_stalkMap f₀).mp inferInstance x₀, gUnramifiedAt_of_unramifiedAt f₀ x₀ ?_⟩
  -- The point is isolated in its fibre, so an elementary étale base change makes the morphism
  -- finite near it.
  have hqf₀ : quasiFiniteAt f₀ x₀ :=
    ⟨⟨⟨⊤, isAffineOpen_top _⟩, ⟨⊤, isAffineOpen_top _⟩, by simp, by simp,
        f₀.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)⟩,
      (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
        (f.resLEStalkMap hVU x₀)).mpr hqf.2⟩
  obtain ⟨N⟩ :=
    Stacks.Flatness.exists_etaleNeighborhood_finiteAt f₀ x₀
      (((quasiFiniteAt_tfae f₀ x₀).out 1 2).mp hqf₀)
  obtain ⟨hfin, ⟨v, hv, hvuniq⟩, hvspec⟩ := N.spec
  refine unramifiedAt_of_isFiniteNeighborhoodAt f₀ x₀ N.neighborhood.toBase
    N.neighborhood.point N.openSubscheme hfin v hv hvuniq (hvspec v hv).1
    ((one_le_ringKrullDim_stalk_of_notMem_genericPoints X x hgen).trans_eq
      (ringKrullDim_stalk_eq_of_etale V.1.ι x₀).symm)
    fun z' hz' hd => unramifiedAt_resLE_of_unramifiedAt f U.1 V.1 hVU z'
      (hunr (V.1.ι z') (V.1.ι.base.hom.map_specializes hz')
        ((ringKrullDim_stalk_eq_of_etale V.1.ι z').symm.trans hd))

end AlgebraicGeometry

end
