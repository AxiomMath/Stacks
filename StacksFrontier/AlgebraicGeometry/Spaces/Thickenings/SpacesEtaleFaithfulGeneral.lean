module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering

/-!
# Faithfulness of base change on spaces-étale sites, at a surjective morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is surjective on points.
Base change `V ↦ X ×_Y V` is then *faithful* from the spaces-étale site of `Y` to that of `X`; this
is the faithfulness half of Stacks 05ZH. In particular it holds at the inclusion of a thickening of
arbitrary order, which is surjective on points by Stacks 05ZK, part (1).

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_fst_agreementLocus` and
  `AlgebraicGeometry.Space.fst_agreementLocus_comp_eq`: the agreement locus of two morphisms
  into a space unramified over the base is an open subspace of the source, and its inclusion
  equalises the two morphisms.
* `AlgebraicGeometry.Space.eq_of_comp_eq_of_isSurjective`: two morphisms into a space
  unramified over the base which agree after a point-surjective base change are equal.
* `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective`: base change along a
  morphism surjective on points is faithful on spaces-étale sites.
* `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isThickening`: the same at the
  inclusion of a thickening of arbitrary order.

## References

* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The agreement locus of two morphisms into an unramified space -/

section Agreement

variable {T V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The projection to `T` of the agreement locus of two morphisms `α, β : T ⟶ V` over `Y` is an
open immersion, when `V ⟶ Y` is unramified; the agreement locus is the fibre product of
`(α, β)` and the relative diagonal of `V ⟶ Y`. -/
theorem isOpenImmersion_fst_agreementLocus (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y) (v : V ⟶ Y) (hv : IsUnramified B S hS v)
    (α β : T ⟶ V) (hαβ : α ≫ v = β ≫ v) :
    IsOpenImmersion B S hS
      (pullback.fst (pullback.lift α β hαβ) (pullback.diagonal v)) :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback
    (IsPullback.of_hasPullback (pullback.lift α β hαβ) (pullback.diagonal v)).flip
    (isOpenImmersion_diagonal_of_isUnramified B S hS hV hY v hv)

/-- The projection to `T` of the agreement locus of `α, β : T ⟶ V` equalises `α` and `β`. -/
theorem fst_agreementLocus_comp_eq (v : V ⟶ Y) (α β : T ⟶ V) (hαβ : α ≫ v = β ≫ v) :
    pullback.fst (pullback.lift α β hαβ) (pullback.diagonal v) ≫ α =
      pullback.fst (pullback.lift α β hαβ) (pullback.diagonal v) ≫ β := by
  have hsq := pullback.condition (f := pullback.lift α β hαβ) (g := pullback.diagonal v)
  have hα := congrArg (fun k ↦ k ≫ pullback.fst v v) hsq
  have hβ := congrArg (fun k ↦ k ≫ pullback.snd v v) hsq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at hα hβ
  rw [hα, hβ]

/-- If `α, β : T ⟶ V` are morphisms over `Y` with `V ⟶ Y` unramified, and
`p : P ⟶ T` is a morphism surjective on points which equalises `α` and `β`, then `α = β`. -/
theorem eq_of_comp_eq_of_isSurjective {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y)
    (v : V ⟶ Y) (hv : IsUnramified B S hS v) (α β : T ⟶ V) (hαβ : α ≫ v = β ≫ v)
    (p : P ⟶ T) (hp : IsSurjective B S hS p) (hpe : p ≫ α = p ≫ β) :
    α = β := by
  have hcomm : p ≫ pullback.lift α β hαβ = (p ≫ α) ≫ pullback.diagonal v := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id]
      exact hpe.symm
  have hsurj : Function.Surjective (pointsMap B S hS _
      (pullback.fst (pullback.lift α β hαβ) (pullback.diagonal v))) := by
    intro x
    obtain ⟨w, rfl⟩ := hp x
    exact ⟨pointsMap B S hS P (pullback.lift p (p ≫ α) hcomm) w,
      by rw [← pointsMap_comp_apply, pullback.lift_fst]⟩
  have : IsIso (pullback.fst (pullback.lift α β hαβ) (pullback.diagonal v)) :=
    isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS _
      (isOpenImmersion_fst_agreementLocus B S hS hV hY v hv α β hαβ) hsurj
  exact (cancel_epi _).mp (fst_agreementLocus_comp_eq B S hS v α β hαβ)

end Agreement

/-! ### Faithfulness of base change at a surjective morphism -/

section Faithful

variable {X Y : AlgebraicSpaces B S hS}

/-- Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` which is surjective on points. Base change
`V ↦ X ×_Y V` is faithful from the spaces-étale site of `Y` to that of `X`. -/
@[stacks 05ZH "FAITHFULNESS ONLY, for an arbitrary morphism surjective on points -- so at a \
thickening of ARBITRARY order, and under a hypothesis weaker than the source's integral, \
universally injective and surjective. The library's other Stacks 05ZH statements are \
restricted to a FIRST-ORDER thickening because they go through the square-zero lifting \
property of Stacks 0611; this one reproduces the source's own route instead. FULLNESS is also \
available at arbitrary order, at a thickening, as \
`AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening`; ESSENTIAL SURJECTIVITY \
remains first-order, see \
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening`"]
theorem faithful_spacesBaseChange_of_isSurjective (f : X ⟶ Y)
    (hf : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.Faithful where
  map_injective {V' V} {a b} hab := by
    have hw : ∀ c : V' ⟶ V, ((SpacesEtale.toSpaces B S hS Y).map c).hom ≫ (V.1.hom).hom =
        (V'.1.hom).hom := fun c ↦ congrArg (fun k ↦ k.hom) (Over.w c.hom)
    have hnat : ∀ c : V' ⟶ V,
        ((spacesBaseChange B S hS f).projection.app V').hom ≫
            ((SpacesEtale.toSpaces B S hS Y).map c).hom =
          ((SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange B S hS f).functor.map c)).hom ≫
            ((spacesBaseChange B S hS f).projection.app V).hom := fun c ↦ by
      simpa using congrArg (fun k ↦ k.hom)
        ((spacesBaseChange B S hS f).projection.naturality c).symm
    have hpe : ((spacesBaseChange B S hS f).projection.app V').hom ≫
          ((SpacesEtale.toSpaces B S hS Y).map a).hom =
        ((spacesBaseChange B S hS f).projection.app V').hom ≫
          ((SpacesEtale.toSpaces B S hS Y).map b).hom := by
      rw [hnat a, hnat b, hab]
    have hps : IsSurjective B S hS
        ((spacesBaseChange B S hS f).projection.app V').hom :=
      isSurjective_of_isPullback B S hS ((spacesBaseChange B S hS f).isPullback V').flip hf
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (eq_of_comp_eq_of_isSurjective B S hS (V.1.left).property Y.property (V.1.hom).hom
        (isUnramified_of_isEtale B S hS V.property) _ _ ((hw a).trans (hw b).symm) _ hps hpe)))

/-- Let `G ⊂ X` be a thickening of algebraic spaces over `S`, of arbitrary order. Base change
along the inclusion, `V ↦ G ×_X V`, is faithful from the spaces-étale site of `X` to that of
`G`. -/
@[stacks 05ZH "FAITHFULNESS ONLY, at a thickening of ARBITRARY order. FULLNESS at arbitrary \
order is `AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening`; ESSENTIAL \
SURJECTIVITY at arbitrary order is \
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`"]
theorem faithful_spacesBaseChange_of_isThickening {G : Subfunctor X.1}
    (hG : IsThickening B S hS X G) :
    (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.Faithful :=
  faithful_spacesBaseChange_of_isSurjective B S hS _ hG.2

end Faithful

end AlgebraicGeometry.Space

end
