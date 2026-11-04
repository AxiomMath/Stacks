module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Commuting
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized Chern classes of a closed cover commute with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i_j : X_j ⟶ X` (`j = 1, 2`) be closed immersions with `X = X₁ ∪ X₂`
set theoretically, and let `E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern classes are defined,
with `E₂|_{X₁ ∩ X₂}` zero, resp. finite locally free of rank `< p` in degree `0`. Stacks 0F9H gives
`P'_p(E₂)`, resp. `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`.

**Stacks 0FAJ**: for `f : Y ⟶ X` locally of finite type and `c ∈ A^*(Y ⟶ X)`,

  `c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c`,   resp.   `c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c`,

where `f₂ : Y₂ = X₂ ×_X Y ⟶ X₂` is the base change of `f` and `P'_p(Lf₂^*E₂)`, resp.
`c'_p(Lf₂^*E₂) ∈ A^p(Y₂ ⟶ Y)` is the class of Stacks 0F9H for the cover `Y = Y₁ ∪ Y₂` by the base
changes `Y_j = X_j ×_X Y`. As in Remark 0FA2 the left side is `res(c) ∘ P'_p(E₂)` with `res(c)`
the restriction of `c` along `i₂` (Stacks 0F9Z), and both composites are classes for the
morphism `Y₂ ⟶ X` (the source writes `A^*(Y₂ ⟶ Y)`, but a composite with `c ∈ A^*(Y ⟶ X)` is a
class over `X`).

The proof is the source's. The localized class commutes with `c` in the sense of Remark 0FA2
(`Stacks.Chow.bivariantCommute_closedCoverLocalizedClass_of_commutesWith`, whose input is
Stacks 0FAC for `c_p(E₂)` and `P_p(E₂)`); commuting classes have equal composites
(`Stacks.Chow.BivariantChowClass.restrict_comp_eq_of_bivariantCommute`); and the restriction of
the localized class along `f` is the localized class of `Lf₂^*E₂` for the cover of `Y`, by
Stacks 0GUG.

## Main results

* `Stacks.Chow.comp_closedCoverLocalizedClass_eq` — the identity for the localized class of any
  total class commuting with `c`, with the restriction of the localized class along `f` given by
  a class satisfying the conclusion of Stacks 0GUG.
* `Stacks.Chow.comp_localizedChernClassOfClosedCover` — **Stacks 0FAJ** for `c'_p`.
* `Stacks.Chow.comp_localizedPowerSumOfClosedCover` — **Stacks 0FAJ** for `P'_p`.

## Implementation notes

The scheme `Y` carries the structure morphism `f ≫ sX` over the base, as in Stacks 0GUG. The
composite `res(c) ∘ P'_p(E₂)` is a class for `Y ×_X X₂ ⟶ X₂ ⟶ X` and `P'_p(Lf₂^*E₂) ∘ c` one for
`X₂ ×_X Y ⟶ Y ⟶ X`; the second is read on `Y ×_X X₂` through the symmetry of the fibre product
and in the degree `r + p` instead of `p + r`, as in Stacks 0FAS and 0FBX.

## References

* [Stacks Project, Tag 0FAJ](https://stacks.math.columbia.edu/tag/0FAJ)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0GUG](https://stacks.math.columbia.edu/tag/0GUG)
* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Composites with a class read on an equal structure morphism -/

section Congr

variable {C : ChowSituation.{u}} {A B W X : Scheme.{u}} {sW : W ⟶ C.S} [LocallyOfFiniteType sW]
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {v : A ⟶ W} [LocallyOfFiniteType v] {g : W ⟶ X}
  [LocallyOfFiniteType g] {hg : g ≫ sX = sW} {p q : ℤ}

omit [LocallyOfFiniteType g] in
/-- The composite `a ∘ c`, read in another degree and transported along an isomorphism of its
source, only depends on the cap operations of `a`: two classes `a`, `a'` over equal structure
morphisms of their source with heterogeneously equal cap operations give the same class. -/
theorem comp_degreeCongr_transport_congr {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA]
    [LocallyOfFiniteType sA'] (hs : sA = sA') {hv : v ≫ sW = sA} {hv' : v ≫ sW = sA'}
    (a : BivariantChowClass C sA sW v hv p) (a' : BivariantChowClass C sA' sW v hv' p)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sW) k), a.cap t k α ≍ a'.cap t k α)
    (c : BivariantChowClass C sW sX g hg q) {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    {u : B ⟶ X} [LocallyOfFiniteType u] (hpq : p + q = q + p) (hu : u ≫ sX = sB) (θ : A ≅ B)
    (hθ : θ.hom ≫ u = v ≫ g) :
    ((a.comp c).degreeCongr hpq).transport hu θ hθ =
      ((a'.comp c).degreeCongr hpq).transport hu θ hθ := by
  subst hs
  obtain rfl : a = a' := BivariantChowClass.ext fun t _ k α ↦ eq_of_heq (h t k α)
  rfl

end Congr

/-! ### Stacks 0FAJ -/

section Composite

variable (C : ChowSituation.{u}) {X X₁ X₂ Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
  (f : Y ⟶ X) [LocallyOfFiniteType f] {r : ℤ}

/-- Pushforward along the identity of a scheme, between two equal structure morphisms, is the
identity up to the transport of structure morphisms. -/
theorem chowPushforwardOfIso_heq_self {A : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (e : A ⟶ A) [IsIso e] (he : e = 𝟙 A)
    (h : e ≫ sA' = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sA' e h k x ≍ x := by
  have hs : sA' = sA := by rw [← h, he, Category.id_comp]
  subst hs he
  exact heq_of_eq (chowPushforwardOfIso_id C sA' k x)

/-- **The composite of a localized class with an arbitrary bivariant class.** Let `x` be a total
class of `X₂` commuting with `c ∈ A^r(Y ⟶ X)` along `i₂`, let `p` be such that `x_p` vanishes on
`X₁ ∩ X₂`, and let `κ'` be a class of `A^p(X₂ ×_X Y ⟶ Y)` equal to the restriction along `f` of
the localized class `x_p' ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H. Then `res(c) ∘ x_p' = κ' ∘ c`. -/
theorem comp_closedCoverLocalizedClass_eq (x : TotalChowClass C (i₂ ≫ sX))
    (c : BivariantChowClass C (f ≫ sX) sX f rfl r)
    (hx : x.CommutesWith C sX f (BivariantChowClass.equivBivariantClass c) i₂ (i₂ ≫ sX) rfl)
    (p : ℕ) (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) (p : ℤ))
    (hκx : κ = x p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂)
      (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
    (κ' : BivariantClass C (gysinSystemOfInvertible C) (pullback.snd i₂ f ≫ f ≫ sX) (f ≫ sX)
      (pullback.snd i₂ f) rfl (p : ℤ))
    (hκ' : κ' = bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i₂ f ≫ i₂ ≫ sX)
        (pullback.snd i₂ f ≫ f ≫ sX) (f ≫ sX) (pullback.snd i₂ f)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
        (pullback.snd i₂ f) rfl (Iso.refl _) (Category.id_comp _) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C (i₂ ≫ sX) sX i₂ rfl f (p : ℤ)
          (closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ))) :
    (c.restrict i₂ rfl).comp (BivariantChowClass.equivBivariantClass.symm
        (closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ)) =
      (((BivariantChowClass.equivBivariantClass.symm κ').comp c).degreeCongr
        (add_comm (p : ℤ) r)).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl i₂ rfl) rfl)
        (pullbackSymmetry i₂ f) (pullbackSymmetry_hom_comp_snd_comp f i₂) := by
  set cloc := closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ
  have hcomm : BivariantCommute C (gysinSystemOfInvertible C) sX i₂ f (p : ℤ) r cloc
      (BivariantChowClass.equivBivariantClass c) :=
    bivariantCommute_closedCoverLocalizedClass_of_commutesWith C sX i₁ i₂ f
      (BivariantChowClass.equivBivariantClass c) hcover x hx p κ hκx hκ
  have hcomm' : BivariantCommute C (gysinSystemOfInvertible C) sX f i₂ r (p : ℤ)
      (BivariantChowClass.equivBivariantClass c)
      (BivariantChowClass.equivBivariantClass (BivariantChowClass.equivBivariantClass.symm cloc)) :=
    by rw [Equiv.apply_symm_apply]; exact hcomm.symm
  rw [BivariantChowClass.restrict_comp_eq_of_bivariantCommute sX f i₂ c
    (BivariantChowClass.equivBivariantClass.symm cloc) hcomm']
  refine comp_degreeCongr_transport_congr ?_ _ _ ?_ c _ _ _ _
  · rw [pullback.condition_assoc]
  · intro T t _ k α
    rw [hκ', BivariantChowClass.equivBivariantClass_symm_cap, bivariantTransport_cap,
      bivariantTransportCap_apply]
    refine HEq.symm ((chowPushforwardOfIso_heq_self C _ ?_ _ (k - p) _).trans ?_)
    · refine pullback.hom_ext ?_ ?_ <;> simp [transportPullbackIso]
    · rfl

variable {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)

/-- **Stacks 0FAJ, for the classes `c'_p`.** Let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let
`E₂ ∈ D(𝒪_{X₂})` be an object whose Chern classes are defined and whose restriction to
`X₁ ∩ X₂` is isomorphic to a finite locally free module of rank `< p` in degree `0`, so that
Stacks 0F9H gives `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`. Let `f : Y ⟶ X` be locally of finite type and
`c ∈ A^r(Y ⟶ X)`. Then

  `c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c`,

where `f₂ : X₂ ×_X Y ⟶ X₂` is the base change of `f` and `c'_p(Lf₂^*E₂) ∈ A^p(X₂ ×_X Y ⟶ Y)` is
the class of Stacks 0F9H for the cover of `Y` by the base changes `X_j ×_X Y` and the derived
pullback `Lf₂^*E₂` (which satisfies the hypotheses of Stacks 0F9H by
`Stacks.Chow.hasDefinedChernClasses_baseChange` and `Stacks.Chow.exists_iso_single_baseChange`).
The left side is `res(c) ∘ c'_p(E₂)`, a class for `Y ×_X X₂ ⟶ X` of degree `r + p`; the right side,
a class for `X₂ ×_X Y ⟶ X` of degree `p + r`, is read on `Y ×_X X₂` through the symmetry of the
fibre product. Perfectness of `E₂`, assumed in Stacks 0F9H, is not used for `c'_p`. -/
@[stacks 0FAJ "the classes c'_p: c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c for every bivariant class c in \
A^r(Y → X), f : Y → X locally of finite type, the composites read as in Remark 0FA2"]
theorem comp_localizedChernClassOfClosedCover
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M))
    (c : BivariantChowClass C (f ≫ sX) sX f rfl r) :
    (c.restrict i₂ rfl).comp (BivariantChowClass.equivBivariantClass.symm
        (localizedChernClassOfClosedCover C sX i₁ i₂ hcover hE₂ p hres)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (localizedChernClassOfClosedCover C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
            (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover f)
            (hasDefinedChernClasses_baseChange i₂ hE₂ f) p
            (exists_iso_single_baseChange i₁ i₂ p f hres))).comp c).degreeCongr
        (add_comm (p : ℤ) r)).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl i₂ rfl) rfl)
        (pullbackSymmetry i₂ f) (pullbackSymmetry_hom_comp_snd_comp f i₂) :=
  comp_closedCoverLocalizedClass_eq C sX i₁ i₂ hcover f (perfectChernClass C (i₂ ≫ sX) hE₂) c
    (TotalChowClass.commutesWith_perfectChernClass C sX f
      (BivariantChowClass.equivBivariantClass c) i₂ (i₂ ≫ sX) rfl hE₂) p _ rfl _ _
    (localizedChernClassOfClosedCover_baseChange C sX i₁ i₂ hcover hE₂ p f hres)

/-- **Stacks 0FAJ, for the classes `P'_p`.** Let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let
`E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern classes are defined and whose restriction to
`X₁ ∩ X₂` is zero, so that Stacks 0F9H gives `P'_p(E₂) ∈ A^p(X₂ ⟶ X)`. Let `f : Y ⟶ X` be
locally of finite type and `c ∈ A^r(Y ⟶ X)`. Then

  `c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c`,

where `f₂ : X₂ ×_X Y ⟶ X₂` is the base change of `f` and `P'_p(Lf₂^*E₂) ∈ A^p(X₂ ×_X Y ⟶ Y)` is
the class of Stacks 0F9H for the cover of `Y` by the base changes `X_j ×_X Y` and the derived
pullback `Lf₂^*E₂`, the composites being read as in
`Stacks.Chow.comp_localizedChernClassOfClosedCover`. -/
@[stacks 0FAJ "the classes P'_p: c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c for every bivariant class c in \
A^r(Y → X), f : Y → X locally of finite type, the composites read as in Remark 0FA2"]
theorem comp_localizedPowerSumOfClosedCover
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂))
    (c : BivariantChowClass C (f ≫ sX) sX f rfl r) :
    (c.restrict i₂ rfl).comp (BivariantChowClass.equivBivariantClass.symm
        (localizedPowerSumOfClosedCover C sX i₁ i₂ hcover hE₂ p perfect hzero)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (localizedPowerSumOfClosedCover C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
            (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover f)
            (hasDefinedChernClasses_baseChange i₂ hE₂ f) p (isPerfect_baseChange i₂ f perfect)
            (isZero_baseChange i₁ i₂ f hzero))).comp c).degreeCongr
        (add_comm (p : ℤ) r)).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl i₂ rfl) rfl)
        (pullbackSymmetry i₂ f) (pullbackSymmetry_hom_comp_snd_comp f i₂) :=
  comp_closedCoverLocalizedClass_eq C sX i₁ i₂ hcover f
    (perfectPowerSumTotal C (i₂ ≫ sX) hE₂) c
    (TotalChowClass.commutesWith_perfectPowerSumTotal C sX f
      (BivariantChowClass.equivBivariantClass c) i₂ (i₂ ≫ sX) rfl perfect hE₂) p _
    (perfectPowerSumTotal_apply C (i₂ ≫ sX) hE₂ p).symm _ _
    (localizedPowerSumOfClosedCover_baseChange C sX i₁ i₂ hcover hE₂ p f perfect hzero)

end Composite

end Stacks.Chow

end
