module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.BigSitePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairOpenExtensionTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The quotients of extended kernel-pair relations, and their transition morphisms

For an extended kernel-pair relation `E` (`AlgebraicGeometry.Space.OpenKernelPairExtension`),
the glued relation `R ⇉ V` is an étale equivalence relation, so by Stacks 02WW its quotient
sheaf `V/R` is an algebraic space with a surjective étale chart `V ⟶ V/R` whose kernel pair is
`R`. A transition `E ⟶ E'` induces a morphism `V/R ⟶ V'/R'` of quotients, and the square formed
by it, the two charts and `v : V ⟶ V'` is cartesian (Stacks 07S3, from the cartesian square
Stacks 07SV); when `v` is affine, so is `V/R ⟶ V'/R'` (Stacks 03WG).

These are the stages `X_i = V_i/R_i` and the transition morphisms `X_i ⟶ X_{i'}` of the proof
of absolute Noetherian approximation, Stacks 07SU.

## Main definitions

* `AlgebraicGeometry.Space.OpenKernelPairExtension.quotient` and
  `AlgebraicGeometry.Space.OpenKernelPairExtension.π`: the quotient `V/R` and its chart.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.φ`: the induced morphism of
  quotients.

## Main results

* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isPullback_π_φ`: the chart of `E`
  is the base change of the chart of `E'`.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isAffineHom_φ`: the induced
  morphism of quotients is affine when `v` is.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

/-- A commutative square of the site whose image in schemes is cartesian is cartesian. -/
theorem isPullback_of_isPullback_map {P₁ P₂ P₃ P₄ : BigFppfOver B S hS}
    {a : P₁ ⟶ P₂} {b : P₁ ⟶ P₃} {c : P₂ ⟶ P₄} {d : P₃ ⟶ P₄} (w : a ≫ c = b ≫ d)
    (h : IsPullback ((F).map a) ((F).map b) ((F).map c) ((F).map d)) : IsPullback a b c d :=
  IsPullback.of_map (Over.forget _) w (IsPullback.of_map B.inclusion (by
    rw [← (Over.forget _).map_comp, ← (Over.forget _).map_comp, w]) h)

namespace OpenKernelPairExtension

attribute [local instance] hasSheafify_bigFppfOver

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W V' W' : BigFppfOver B S hS}
  (E : OpenKernelPairExtension B S hS X V W) (E' : OpenKernelPairExtension B S hS X' V' W')

/-- The glued relation `R ⇉ V` of an extended kernel-pair relation is an étale equivalence
relation. -/
instance : IsEtaleEquivalenceRelation (relation B S hS E.s E.t) := E.isEtaleEquivalenceRelation

/-- The quotient `V/R` of the extended relation. -/
noncomputable abbrev quotient : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (relation B S hS E.s E.t)).obj

/-- The chart `V ⟶ V/R` of the quotient. -/
noncomputable abbrev π : yoneda.obj V ⟶ E.quotient := quotientMap B S hS E.s E.t

/-- **Stacks 02WW.** The quotient is an algebraic space. -/
theorem isAlgebraicSpace_quotient : IsAlgebraicSpace B S hS E.quotient :=
  isAlgebraicSpace_quotient_unconditional B S hS E.s E.t

/-- The chart `V ⟶ V/R` is surjective. -/
theorem π_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) E.π :=
  quotientMap_surjective_unconditional B S hS E.s E.t

/-- The chart `V ⟶ V/R` is étale. -/
theorem π_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (F))) E.π :=
  quotientMap_etale_unconditional B S hS E.s E.t

/-- The kernel pair of the chart of the quotient is the glued relation. -/
theorem isPullback_π : IsPullback (yoneda.map E.t) (yoneda.map E.s) E.π E.π :=
  quotientMap_isPullback B S hS E.s E.t

/-- The chart `π` is the canonical chart `quotientChart` of the quotient sheaf. -/
theorem π_eq_quotientChart :
    E.π = quotientChart (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
      V (relation B S hS E.s E.t) :=
  yonedaEquiv_symm_app_toQuotientSheaf _ _ _ _

/-- The source map of the glued relation is the image of `E.s`. -/
theorem relation_source :
    (relation B S hS E.s E.t).source = (Over.post (X := B.obj hS) B.inclusion).map E.s :=
  prod.lift_snd _ _

/-- The target map of the glued relation is the image of `E.t`. -/
theorem relation_target :
    (relation B S hS E.s E.t).target = (Over.post (X := B.obj hS) B.inclusion).map E.t :=
  prod.lift_fst _ _

namespace Transition

variable {E E'} (T : Transition E E')

/-- The morphism of relations of a transition commutes with the source maps. -/
theorem r_s : T.r ≫ E'.s = E.s ≫ T.v :=
  BigFppfOver.map_toScheme_injective B S hS (by exact T.rScheme_sourceScheme)

/-- The morphism of relations of a transition commutes with the target maps. -/
theorem r_t : T.r ≫ E'.t = E.t ≫ T.v :=
  BigFppfOver.map_toScheme_injective B S hS (by exact T.rScheme_targetScheme)

/-- The image of the morphism of relations commutes with the source maps of the glued relations. -/
theorem post_r_source :
    (Over.post (X := B.obj hS) B.inclusion).map T.r ≫ (relation B S hS E'.s E'.t).source =
      (relation B S hS E.s E.t).source ≫ (Over.post (X := B.obj hS) B.inclusion).map T.v := by
  rw [relation_source, relation_source, ← Functor.map_comp, ← Functor.map_comp, T.r_s]

/-- The image of the morphism of relations commutes with the target maps of the glued relations. -/
theorem post_r_target :
    (Over.post (X := B.obj hS) B.inclusion).map T.r ≫ (relation B S hS E'.s E'.t).target =
      (relation B S hS E.s E.t).target ≫ (Over.post (X := B.obj hS) B.inclusion).map T.v := by
  rw [relation_target, relation_target, ← Functor.map_comp, ← Functor.map_comp, T.r_t]

/-- The morphism of quotients `V/R ⟶ V'/R'` induced by a transition. -/
noncomputable def φ : E.quotient ⟶ E'.quotient :=
  (quotientSheafMap (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (relation B S hS E.s E.t) (relation B S hS E'.s E'.t)
    ((Over.post (X := B.obj hS) B.inclusion).map T.r)
    ((Over.post (X := B.obj hS) B.inclusion).map T.v) T.post_r_source T.post_r_target).hom

/-- **Stacks 07S3 for the extended relations.** The chart of `E` is the base change of the chart
of `E'` along the induced morphism of quotients. -/
theorem isPullback_π_φ : IsPullback E.π (yoneda.map T.v) T.φ E'.π := by
  have hcart : IsPullback ((Over.post (X := B.obj hS) B.inclusion).map T.r)
      (relation B S hS E.s E.t).source (relation B S hS E'.s E'.t).source
      ((Over.post (X := B.obj hS) B.inclusion).map T.v) := by
    have w := T.post_r_source
    rw [relation_source, relation_source] at w ⊢
    exact IsPullback.of_map (Over.forget _) w T.isPullback_rScheme_sourceScheme
  have h07S3 := isPullback_toQuotientSheaf_of_subcanonical (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (relation B S hS E.s E.t)
    (relation B S hS E'.s E'.t) ((Over.post (X := B.obj hS) B.inclusion).map T.r)
    ((Over.post (X := B.obj hS) B.inclusion).map T.v) T.post_r_source T.post_r_target hcart
  have hleft : IsPullback (yonedaToPoints (Over.post (X := B.obj hS) B.inclusion) V)
      (yoneda.map T.v)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map T.v)))
      (yonedaToPoints (Over.post (X := B.obj hS) B.inclusion) V') :=
    IsPullback.of_horiz_isIso ⟨yonedaToPoints_naturality _ T.v⟩
  rw [π_eq_quotientChart, π_eq_quotientChart]
  exact hleft.paste_horiz h07S3

/-- The square formed by the charts, `v` and the induced morphism of quotients commutes. -/
theorem π_φ : E.π ≫ T.φ = yoneda.map T.v ≫ E'.π := T.isPullback_π_φ.w

/-- **Stacks 03WG for the transition.** The induced morphism of quotients is affine when `v`
is an affine morphism of schemes: its base change along the surjective étale chart of `V'/R'`
is `v`. -/
theorem isAffineHom_φ [_root_.AlgebraicGeometry.IsAffineHom ((F).map T.v)] :
    IsAffineHom B S hS T.φ := by
  have hv : IsAffineHom B S hS (yoneda.map T.v) := isAffineHom_of_presheaf
    ((presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsAffineHom.{u})
      inferInstance T.v).2 inferInstance)
  have hsnd : IsAffineHom B S hS (pullback.snd T.φ E'.π) := by
    have h := T.isPullback_π_φ
    have : pullback.snd T.φ E'.π = h.isoPullback.inv ≫ yoneda.map T.v :=
      h.isoPullback_inv_snd.symm
    rw [this]
    exact isAffineHom_iso_comp _ hv
  have htfae := isAffineHom_tfae_of_isAlgebraicSpace B S hS T.φ E.isAlgebraicSpace_quotient
    E'.isAlgebraicSpace_quotient
  have h42 : (∃ (V₀ : BigFppfOver B S hS) (g : yoneda.obj V₀ ⟶ E'.quotient),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧ IsAffineHom B S hS (pullback.snd T.φ g)) →
      IsAffineHom B S hS T.φ := (htfae.out 4 2).mp
  exact h42 ⟨V', E'.π, isSurjective_of_presheafSurjective B S hS E'.π E'.π_surjective,
    isEtale_of_presheaf_etale B S hS E'.π_etale, hsnd⟩

end Transition

end OpenKernelPairExtension

end AlgebraicGeometry.Space

end
