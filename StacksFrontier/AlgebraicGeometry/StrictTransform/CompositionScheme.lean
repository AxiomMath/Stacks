module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Iterated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Iterated strict transforms of a scheme: [Stacks, Tag 080I] part (2)

Let `f : X ⟶ S` be a morphism of schemes, let `b : S₁ ⟶ S` and `c : S₂ ⟶ S₁` be a composable
pair and let `d : T ⟶ S` be identified with `c ≫ b` as an `S`-scheme. The strict transform of
`X` along `b` is a closed subscheme `X₁` of `X ×_S S₁`, and it carries a morphism to `S₁`; its
strict transform along `c` is compared here with the strict transform of `X` along `d`, over the
identification `Stacks.IteratedBaseChange.iso` of the two base changes.

For blowups — `b` the blowup of `S` in `I`, `c` the blowup of the blowup in `J`, `d` the blowup
of `S` in a third centre `K` whose support is `Supp I ∪ b(Supp J)` — both hypotheses of the
general statement are theorems, so the comparison is unconditional. That is
[Stacks, Tag 080I] part (2).

## Main definitions

* `Stacks.StrictTransform.schemeToBase`: the strict transform of `X` as a scheme over `S₁`, i.e.
  the inclusion of the strict transform followed by the projection of the base change.

## Main results

* `Stacks.StrictTransform.iso_preimage_exceptionalComplement`: the open of the iterated base
  change over which both quotients are unchanged is the intersection of the two exceptional
  complements.
* `Stacks.StrictTransform.exists_scheme_iso_comp`: the comparison of iterated strict transforms
  of a scheme, for an arbitrary iterated base change, from the support identity and the open
  immersion away from the second exceptional divisor.
* `Stacks.StrictTransform.strictTransform_comp_blowUp`: **[Stacks, Tag 080I] part (2)**, in the
  shape that tag states it, unconditionally.

## Implementation notes

The Stacks Project states part (2) and proves only part (1); the scheme statement is the module
statement for the structure sheaf, and a direct translation would need the strict transform of
`𝒪_X` identified with the direct image of the structure sheaf of the strict transform, which is
[Stacks, Tag 080G] for a closed immersion. The route taken here avoids that identification
entirely and argues with ideal sheaves instead.

Write `Z` for the exceptional preimage and `V` for its open complement, with subscripts for the
three centres, and let `W` be the inverse image of `V_K` under the identification `G` of the two
base changes. Everything rests on one observation: `Stacks.StrictTransform.ideal_eq_ker_ι` says
the defining ideal of a strict transform is the kernel of the inclusion of the exceptional
complement, so **a strict transform is the scheme-theoretic image of that open**. Hence

* the strict transform in `K` is the scheme-theoretic image of `V_K`, and
* `V_{J'}` is scheme-theoretically dense in the strict transform in `J`
  (`Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDense_preimage_subschemeι`).

The comparison then follows from a kernel computation,
`Stacks.SchemeTheoreticImage.exists_iso_of_isSchemeTheoreticallyDense`, once `W` is identified
with an open `PP` of `V_{J'}` which is itself scheme-theoretically dense there. By
`Stacks.StrictTransform.iso_preimage_exceptionalComplement`, `W` is the intersection of the
inverse image of `V_I` with `V_J`; the first factor transports to `V_{J'}` along the open
immersion `V_{J'} ⟶ X₁` of
`Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst` — which is where
[Stacks, Tag 02OS] part (1) enters, for the *second* blowup — and `V_I` is dense in `X₁` by the
observation above, so `PP` is dense in `V_{J'}` by
`AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_preimage_of_isOpenImmersion`.

The mutually inverse morphisms `W ⟶ PP` and `PP ⟶ W` are built by hand rather than as a
range-equality isomorphism: `W ⟶ PP` comes from lifting the projections of `W` through the
closed immersion of the first strict transform and then through two open immersions, and
`PP ⟶ W` from lifting the other way; each is a section of the other because the comparison
morphism of base changes is a monomorphism.

The statements are unconditional for blowups because the two quasi-compactness instances are
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal` and tag 02OS part (1) is
the instance `AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransform

open Stacks.IteratedBaseChange Stacks.SchemeTheoreticImage

variable {X S S₁ S₂ T : Scheme.{u}}

/-- The strict transform of `X` along `b : S₁ ⟶ S`, as a scheme over `S₁`: the inclusion of the
strict transform into the base change followed by the projection to `S₁`. This is the morphism
whose strict transform along a second morphism `c : S₂ ⟶ S₁` the comparison of iterated strict
transforms is about. -/
@[sga "7 X 2.4" "more general"]
public abbrev schemeToBase (f : X ⟶ S) (b : S₁ ⟶ S) (E : S₁.IdealSheafData) :
    scheme f b E ⟶ S₁ :=
  (ideal f b E).subschemeι ≫ pullback.snd f b

/-- A morphism whose image lies in an open subscheme factors through its inclusion. -/
private theorem exists_comp_ι_eq_of_forall_mem {Y Z : Scheme.{u}} (U : Z.Opens) (φ : Y ⟶ Z)
    (h : ∀ y, φ y ∈ U) : ∃ l : Y ⟶ U.toScheme, l ≫ U.ι = φ :=
  ⟨IsOpenImmersion.lift U.ι φ (by simpa [Set.range_subset_iff] using h),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- **The open of the iterated base change over which neither strict transform changes anything
is the intersection of the two exceptional complements.** Open-subscheme form of
`Stacks.StrictTransform.iso_preimage_exceptionalPreimage`. -/
public theorem iso_preimage_exceptionalComplement (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁)
    (d : T ⟶ S) (e : Over.mk (c ≫ b) ≅ Over.mk d) (E : S₁.IdealSheafData)
    (E' : S₂.IdealSheafData) (E'' : T.IdealSheafData)
    (hZ : (Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹' exceptionalPreimage f d E'' =
      (pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
        exceptionalPreimage (pullback.snd f b) c E') :
    (Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ exceptionalComplement f d E'' =
      (pullback.fst (pullback.snd f b) c ⁻¹ᵁ exceptionalComplement f b E) ⊓
        exceptionalComplement (pullback.snd f b) c E' := by
  refine Opens.ext ?_
  have h1 : (((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'' : (baseChange (pullback.snd f b) c).Opens) :
      Set (baseChange (pullback.snd f b) c)) =
      ((Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹'
        exceptionalPreimage f d E'')ᶜ := by
    rw [show (((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
          exceptionalComplement f d E'' : (baseChange (pullback.snd f b) c).Opens) :
        Set (baseChange (pullback.snd f b) c)) =
        (Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹'
          ((exceptionalComplement f d E'' : (baseChange f d).Opens) :
            Set (baseChange f d)) from rfl,
      exceptionalPreimage_eq_compl, Set.preimage_compl, compl_compl]
  rw [h1, hZ, Set.compl_union, exceptionalPreimage_eq_compl, exceptionalPreimage_eq_compl,
    Set.preimage_compl, compl_compl, compl_compl]
  rfl

/-- **The comparison of iterated strict transforms of a scheme**, for an arbitrary iterated base
change: the strict transform along `c` of the strict transform along `b` agrees, over the
identification `Stacks.IteratedBaseChange.iso` of the two base changes, with the strict transform
along `d`.

The two inputs are `hZ`, the support identity
`Stacks.StrictTransform.iso_preimage_exceptionalPreimage`, and `hOI`, that away from the second
exceptional divisor the projection of the second base change to the first strict transform is an
open immersion — which for a blowup is
`Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst`. -/
public theorem exists_scheme_iso_comp (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁) (d : T ⟶ S)
    (e : Over.mk (c ≫ b) ≅ Over.mk d) (E : S₁.IdealSheafData) (E' : S₂.IdealSheafData)
    (E'' : T.IdealSheafData)
    [QuasiCompact (exceptionalComplement f b E).ι]
    [QuasiCompact (exceptionalComplement (schemeToBase f b E) c E').ι]
    (hZ : (Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹' exceptionalPreimage f d E'' =
      (pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
        exceptionalPreimage (pullback.snd f b) c E')
    (hOI : IsOpenImmersion ((exceptionalComplement (schemeToBase f b E) c E').ι ≫
      pullback.fst (schemeToBase f b E) c)) :
    ∃ g : scheme (schemeToBase f b E) c E' ≅ scheme f d E'',
      g.hom ≫ (ideal f d E'').subschemeι =
        (ideal (schemeToBase f b E) c E').subschemeι ≫
          sourceMap (ideal f b E).subschemeι (pullback.snd f b) c ≫
            (Stacks.IteratedBaseChange.iso f b c d e).hom := by
  have hWeq := iso_preimage_exceptionalComplement f b c d e E E' E'' hZ
  have hWI : (Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ exceptionalComplement f d E'' ≤
      pullback.fst (pullback.snd f b) c ⁻¹ᵁ exceptionalComplement f b E := by
    rw [hWeq]; exact inf_le_left
  have hWJ : (Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ exceptionalComplement f d E'' ≤
      exceptionalComplement (pullback.snd f b) c E' := by
    rw [hWeq]; exact inf_le_right
  -- the projection of `W` to `X`, lifted through the first strict transform
  have hi : (ideal f b E).subschemeι.ker ≤
      (((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'').ι ≫ pullback.fst (pullback.snd f b) c).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ideal_eq_ker_ι]
    refine ker_ι_le_ker_of_range_le _ _ ?_
    rintro _ ⟨x, rfl⟩
    exact hWI x.2
  let a := IsClosedImmersion.lift (ideal f b E).subschemeι
    (((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
      exceptionalComplement f d E'').ι ≫ pullback.fst (pullback.snd f b) c) hi
  have ha : a ≫ (ideal f b E).subschemeι =
      ((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'').ι ≫ pullback.fst (pullback.snd f b) c :=
    IsClosedImmersion.lift_fac _ _ _
  -- and the induced morphism of `W` into the second base change
  have hcomm : a ≫ schemeToBase f b E =
      (((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'').ι ≫ pullback.snd (pullback.snd f b) c) ≫ c := by
    rw [show (schemeToBase f b E) = (ideal f b E).subschemeι ≫ pullback.snd f b from rfl,
      ← Category.assoc, ha]
    simp only [Category.assoc]
    exact congrArg (fun v ↦ ((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
      exceptionalComplement f d E'').ι ≫ v)
      (pullback.condition (f := pullback.snd f b) (g := c))
  let aa := pullback.lift (f := schemeToBase f b E) (g := c) a
    (((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
      exceptionalComplement f d E'').ι ≫ pullback.snd (pullback.snd f b) c) hcomm
  have haa_fst : aa ≫ pullback.fst (schemeToBase f b E) c = a := pullback.lift_fst _ _ _
  have haa_snd : aa ≫ pullback.snd (schemeToBase f b E) c =
      ((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'').ι ≫ pullback.snd (pullback.snd f b) c :=
    pullback.lift_snd _ _ _
  have haa : aa ≫ sourceMap (ideal f b E).subschemeι (pullback.snd f b) c =
      ((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'').ι := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sourceMap_fst, ← Category.assoc, haa_fst, ha]
    · rw [Category.assoc, sourceMap_snd, haa_snd]
  have _hoi := hOI
  -- `W` lands in the second exceptional complement
  obtain ⟨w2, hw2⟩ := exists_comp_ι_eq_of_forall_mem
    (exceptionalComplement (schemeToBase f b E) c E') aa fun x ↦ by
    change (aa ≫ pullback.snd (schemeToBase f b E) c) x ∈ (E'.support.compl : Set S₂)
    rw [haa_snd]
    exact hWJ x.2
  have hchain : ((w2 ≫ (exceptionalComplement (schemeToBase f b E) c E').ι) ≫
        pullback.fst (schemeToBase f b E) c) ≫ (ideal f b E).subschemeι =
      ((Stacks.IteratedBaseChange.iso f b c d e).hom ⁻¹ᵁ
        exceptionalComplement f d E'').ι ≫ pullback.fst (pullback.snd f b) c := by
    rw [hw2, haa_fst, ha]
  -- and in the dense open of it
  obtain ⟨ww, hww0⟩ := exists_comp_ι_eq_of_forall_mem
    (((exceptionalComplement (schemeToBase f b E) c E').ι ≫
      pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
      ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)) w2 fun x ↦ by
    change (((w2 ≫ (exceptionalComplement (schemeToBase f b E) c E').ι) ≫
      pullback.fst (schemeToBase f b E) c) ≫ (ideal f b E).subschemeι) x ∈
        (exceptionalComplement f b E : Set (baseChange f b))
    rw [hchain]
    exact hWI x.2
  have hww : ww ≫ (((exceptionalComplement (schemeToBase f b E) c E').ι ≫
      pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
      ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι = aa := by
    rw [← Category.assoc, hww0, hw2]
  -- the morphism back
  have h1 : ((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          sourceMap (ideal f b E).subschemeι (pullback.snd f b) c) ≫
        pullback.fst (pullback.snd f b) c =
      ((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ≫ (ideal f b E).subschemeι := by
    simp only [Category.assoc, sourceMap_fst]
  have h2 : ((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          sourceMap (ideal f b E).subschemeι (pullback.snd f b) c) ≫
        pullback.snd (pullback.snd f b) c =
      (((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.snd (schemeToBase f b E) c := by
    simp only [Category.assoc, sourceMap_snd]
  obtain ⟨vv, hvv⟩ := exists_comp_ι_eq_of_forall_mem ((Stacks.IteratedBaseChange.iso f b c d e).hom
      ⁻¹ᵁ exceptionalComplement f d E'')
    ((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          sourceMap (ideal f b E).subschemeι (pullback.snd f b) c) fun x ↦ by
    rw [hWeq]
    refine ⟨?_, ?_⟩
    · change (((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          sourceMap (ideal f b E).subschemeι (pullback.snd f b) c) ≫
        pullback.fst (pullback.snd f b) c) x ∈
          (exceptionalComplement f b E : Set (baseChange f b))
      rw [h1]
      exact x.2
    · change (((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι ≫
        (exceptionalComplement (schemeToBase f b E) c E').ι ≫
          sourceMap (ideal f b E).subschemeι (pullback.snd f b) c) ≫
        pullback.snd (pullback.snd f b) c) x ∈ (E'.support.compl : Set S₂)
      rw [h2]
      exact (((((exceptionalComplement (schemeToBase f b E) c E').ι ≫
          pullback.fst (schemeToBase f b E) c) ⁻¹ᵁ
        ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)).ι) x).2
  -- the two density inputs
  have hdomTau := isSchemeTheoreticallyDominant_toSubscheme
    (ideal (schemeToBase f b E) c E') (exceptionalComplement (schemeToBase f b E) c E')
    (ideal_eq_ker_ι (schemeToBase f b E) c E')
  have hPdense := Scheme.Opens.isSchemeTheoreticallyDense_preimage_of_isOpenImmersion
    ((ideal f b E).subschemeι ⁻¹ᵁ exceptionalComplement f b E)
    (isSchemeTheoreticallyDense_preimage_subschemeι (ideal f b E)
      (exceptionalComplement f b E) (ideal_eq_ker_ι f b E))
    ((exceptionalComplement (schemeToBase f b E) c E').ι ≫
      pullback.fst (schemeToBase f b E) c)
  have hdomP := isSchemeTheoreticallyDominant_of_dense _ hPdense
  exact exists_iso_of_isSchemeTheoreticallyDense _ _ _ _ _ _ _
    (toSubscheme_subschemeι (ideal (schemeToBase f b E) c E')
      (exceptionalComplement (schemeToBase f b E) c E')
      (ideal_eq_ker_ι (schemeToBase f b E) c E')) _
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ideal_eq_ker_ι]) aa haa ww hww vv hvv

variable {X S : Scheme.{u}}

/-- **[Stacks, Tag 080I] part (2).** For `b` the blowup of `S` in `I`, `c` the blowup of the
blowup in `J`, and `d` the blowup of `S` in a third centre `K` whose support is
`Supp I ∪ b(Supp J)`, the strict transform along `c` of the strict transform of `X` along `b`
agrees with the strict transform of `X` along `d`, compatibly with both projections.

Unconditional: the support identity is
`Stacks.StrictTransform.iso_preimage_exceptionalPreimage_blowUp` and the open immersion away from
the second exceptional divisor is
`Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst`, both of which are
theorems now that [Stacks, Tag 02OS] part (1) is the instance
`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`. -/
@[stacks 080I "part (2): strict transform of a scheme"]
public theorem strictTransform_comp_blowUp (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase J ≫ AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase K)) :
    let X₁ := scheme f (AlgebraicGeometry.blowUpToBase I) (AlgebraicGeometry.exceptionalIdeal I)
    let f₁ : X₁ ⟶ AlgebraicGeometry.blowUp I :=
      (ideal f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I)).subschemeι ≫
        pullback.snd f (AlgebraicGeometry.blowUpToBase I)
    ∃ g : scheme f₁ (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.exceptionalIdeal J) ≅
        scheme f (AlgebraicGeometry.blowUpToBase K) (AlgebraicGeometry.exceptionalIdeal K),
      (g.hom ≫ (ideal f (AlgebraicGeometry.blowUpToBase K)
            (AlgebraicGeometry.exceptionalIdeal K)).subschemeι ≫
          pullback.fst f (AlgebraicGeometry.blowUpToBase K) =
        (ideal f₁ (AlgebraicGeometry.blowUpToBase J)
            (AlgebraicGeometry.exceptionalIdeal J)).subschemeι ≫
          pullback.fst f₁ (AlgebraicGeometry.blowUpToBase J) ≫
          (ideal f (AlgebraicGeometry.blowUpToBase I)
            (AlgebraicGeometry.exceptionalIdeal I)).subschemeι ≫
          pullback.fst f (AlgebraicGeometry.blowUpToBase I)) ∧
      (g.hom ≫ (ideal f (AlgebraicGeometry.blowUpToBase K)
            (AlgebraicGeometry.exceptionalIdeal K)).subschemeι ≫
          pullback.snd f (AlgebraicGeometry.blowUpToBase K) =
        (ideal f₁ (AlgebraicGeometry.blowUpToBase J)
            (AlgebraicGeometry.exceptionalIdeal J)).subschemeι ≫
          pullback.snd f₁ (AlgebraicGeometry.blowUpToBase J) ≫ e.hom.left) := by
  intro X₁ f₁
  obtain ⟨g, hg⟩ := exists_scheme_iso_comp f (AlgebraicGeometry.blowUpToBase I)
    (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.blowUpToBase K) e
    (AlgebraicGeometry.exceptionalIdeal I) (AlgebraicGeometry.exceptionalIdeal J)
    (AlgebraicGeometry.exceptionalIdeal K)
    (iso_preimage_exceptionalPreimage_blowUp f I K J hK e)
    (isOpenImmersion_exceptionalComplement_ι_comp_fst f₁ J)
  have haux1 : sourceMap (ideal f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I)).subschemeι
        (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
        (AlgebraicGeometry.blowUpToBase J) ≫
      pullback.fst (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J) ≫
        pullback.fst f (AlgebraicGeometry.blowUpToBase I) =
      pullback.fst f₁ (AlgebraicGeometry.blowUpToBase J) ≫
        (ideal f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I)).subschemeι ≫
        pullback.fst f (AlgebraicGeometry.blowUpToBase I) := by
    rw [← Category.assoc, sourceMap_fst]; simp only [Category.assoc]; rfl
  have haux2 : sourceMap (ideal f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I)).subschemeι
        (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
        (AlgebraicGeometry.blowUpToBase J) ≫
      pullback.snd (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
        (AlgebraicGeometry.blowUpToBase J) ≫ e.hom.left =
      pullback.snd f₁ (AlgebraicGeometry.blowUpToBase J) ≫ e.hom.left := by
    rw [← Category.assoc, sourceMap_snd]
  refine ⟨g, ?_, ?_⟩
  · rw [← Category.assoc, hg]
    simp only [Category.assoc]
    rw [Stacks.IteratedBaseChange.iso_hom_fst, haux1]
  · rw [← Category.assoc, hg]
    simp only [Category.assoc]
    rw [Stacks.IteratedBaseChange.iso_hom_snd, haux2]

end Stacks.StrictTransform

end
