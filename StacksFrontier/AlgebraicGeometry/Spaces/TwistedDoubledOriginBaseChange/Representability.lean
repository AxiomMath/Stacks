module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange.KernelPair
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.KernelPair
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.Representability
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.PointsLocallySurjective

/-!
# Stacks 03FN, part (6): the glued scheme represents the base change of the quotient

The base change `X' = S' ×_S X` of the twisted doubled origin along the chart, formed in
presheaves on the big fppf site of the base, is represented by the glued scheme, so the chart is
a surjective, finite, étale morphism trivialising `X`.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange`, whose module
docstring describes the whole argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

variable [FiniteDimensional k K] [IsGalois k K]

/-! ### The glued scheme represents the base change of the quotient -/

section BaseChange

variable (B : BigFppfSite.{u}) (hS : B.Contains (base k))

/-- The restricted functor of points, as a functor from schemes over the base to presheaves on
the big fppf site of the base. On objects it is `Stacks.Groupoids.points`, and on morphisms the
whiskering of a Yoneda morphism; packaging it as a functor is what makes the functor of points
visibly limit-preserving. -/
abbrev pointsFunctor : Over (base k) ⥤ ((BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post (X := B.obj hS) B.inclusion).op

/-- **Any two morphisms of presheaves into the functor of points of the base agree.** The base
is the terminal object of its own slice category, so its functor of points is a terminal
presheaf. -/
theorem hom_ext_points_baseOverBase
    {P : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u}
    (x y : P ⟶ (pointsFunctor k B hS).obj (baseOverBase k)) : x = y := by
  ext T p
  exact (Over.mkIdTerminal (X := base k)).hom_ext _ _

/-- The morphism `S' ⟶ S` of part (6), read on functors of points over the big fppf site. -/
abbrev pointsCoverToBase : (pointsFunctor k B hS).obj (coverOverBase k K) ⟶
    (pointsFunctor k B hS).obj (baseOverBase k) :=
  (pointsFunctor k B hS).map (uToBase k K)

omit [FiniteDimensional k K] [IsGalois k K] in
/-- **The functor of points takes the self-product of the chart to a fibre product.** A point of
`U ×_S U` over a test object is exactly a pair of points of `U` lying over a common point of the
base, and the functor of points of the base is a terminal presheaf; so the two projections
exhibit the functor of points of the self-product as the fibre product of two copies of that of
the chart over that of the base.

The functor of points is the Yoneda embedding followed by restriction along the site, and both
preserve limits, so this is the product square of the slice category over the base — a fibre
square over its terminal object — transported along it. -/
theorem isPullback_pointsCoverSelfProduct :
    IsPullback
      ((pointsFunctor k B hS).map
        (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)))
      ((pointsFunctor k B hS).map
        (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)))
      (pointsCoverToBase k K B hS) (pointsCoverToBase k K B hS) := by
  have hprod : IsPullback (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K))
      (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)) (uToBase k K)
      (uToBase k K) := by
    refine (IsPullback.of_is_product (prodIsProd (coverOverBase k K) (coverOverBase k K))
      (Over.mkIdTerminal (X := base k))).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) ?_ ?_ <;>
      exact (Category.comp_id _).trans
        (((Over.mkIdTerminal (X := base k)).hom_ext _ _).trans (Category.id_comp _).symm)
  exact hprod.map (pointsFunctor k B hS)

variable [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)]

/-- **The base change of the twisted doubled origin along the chart.** This is `X' = S' ×_S X`
of part (6), formed in presheaves on the big fppf site of the base: the fibre product of the
functor of points of the chart with the quotient, over the functor of points of the base. -/
abbrev baseChangePresheaf (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u :=
  pullback (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS)

/-- The base change of part (6) is a sheaf, being a fibre product of sheaves. -/
theorem isSheaf_baseChangePresheaf (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    Presheaf.IsSheaf (BigFppfOver.topology B (base k) hS)
      (baseChangePresheaf k K B hS hdegree σ hσ) := by
  apply ObjectProperty.prop_of_isLimit
    (Presheaf.IsSheaf (BigFppfOver.topology B (base k) hS) (A := Type u))
    (pullback.isLimit (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS))
  rintro (_ | _ | _)
  · exact BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (baseOverBase k)
  · exact BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (coverOverBase k K)
  · exact (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).property

/-- **The comparison map from the self-product of the chart to the base change of part (6).**
Its first component is the first projection of the self-product, its second the quotient map
applied to the second projection: a pair of points of the chart over a common point of the base
gives the first of them together with the class of the second in the quotient. -/
def coverSelfProductToBaseChange (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (pointsFunctor k B hS).obj (coverOverBase k K ⨯ coverOverBase k K) ⟶
      baseChangePresheaf k K B hS hdegree σ hσ :=
  pullback.lift
    ((pointsFunctor k B hS).map
      (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)))
    ((pointsFunctor k B hS).map
        (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)) ≫
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ))
    (hom_ext_points_baseOverBase k B hS _ _)

/-- The first component of `coverSelfProductToBaseChange` is the first projection of the
self-product of the chart. -/
@[simp]
theorem coverSelfProductToBaseChange_comp_fst (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    coverSelfProductToBaseChange k K B hS hdegree σ hσ ≫
        pullback.fst (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS) =
      (pointsFunctor k B hS).map
        (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)) :=
  pullback.lift_fst _ _ _

/-- The second component of `coverSelfProductToBaseChange` is the second projection of the
self-product of the chart followed by the quotient map. -/
@[simp]
theorem coverSelfProductToBaseChange_comp_snd (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    coverSelfProductToBaseChange k K B hS hdegree σ hσ ≫
        pullback.snd (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS) =
      (pointsFunctor k B hS).map
          (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)) ≫
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
          (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ) :=
  pullback.lift_snd _ _ _

/-- **The comparison map to the base change is a base change of the quotient map.** The square
whose other two sides are the second projection of the self-product and the projection of the
base change onto the quotient is Cartesian: it is the self-product square of
`isPullback_pointsCoverSelfProduct` with the defining square of the base change divided out on
the right, the two composites to the functor of points of the base agreeing because that
presheaf is terminal. -/
theorem isPullback_coverSelfProductToBaseChange (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsPullback (coverSelfProductToBaseChange k K B hS hdegree σ hσ)
      ((pointsFunctor k B hS).map
        (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)))
      (pullback.snd (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS))
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ)) := by
  refine IsPullback.of_right ?_
    (coverSelfProductToBaseChange_comp_snd k K B hS hdegree σ hσ)
    (IsPullback.of_hasPullback _ _)
  rw [coverSelfProductToBaseChange_comp_fst,
    show Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ) ≫
        quotientBaseMap k K hdegree σ hσ B hS = pointsCoverToBase k K B hS from
      hom_ext_points_baseOverBase k B hS _ _]
  exact isPullback_pointsCoverSelfProduct k K B hS

/-- The comparison map to the base change coequalizes the two legs of the base-changed relation:
on the first component both legs are the first projection of the self-product, and on the second
they become the two legs of the twisted relation, which the quotient map identifies. -/
theorem doubledRelation_comp_coverSelfProductToBaseChange (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ) ≫
        coverSelfProductToBaseChange k K B hS hdegree σ hσ =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ) ≫
        coverSelfProductToBaseChange k K B hS hdegree σ hσ := by
  have hfst : (doubledRelation k K σ).source ≫
      (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)) =
      (doubledRelation k K σ).target ≫ prod.fst := by
    rw [doubledRelation_source, doubledRelation_target, prod.map_fst, prod.map_fst]
  have hsnd : (doubledRelation k K σ).source ≫
      (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)) =
      prod.snd ≫ (twistedRelation k K σ).source := by
    rw [doubledRelation_source, prod.map_snd, twistedRelation_source]
  have hsnd' : (doubledRelation k K σ).target ≫
      (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)) =
      prod.snd ≫ (twistedRelation k K σ).target := by
    rw [doubledRelation_target, prod.map_snd, twistedRelation_target]
  apply pullback.hom_ext
  · simp only [Category.assoc, coverSelfProductToBaseChange_comp_fst]
    show (pointsFunctor k B hS).map (doubledRelation k K σ).source ≫
        (pointsFunctor k B hS).map prod.fst =
      (pointsFunctor k B hS).map (doubledRelation k K σ).target ≫
        (pointsFunctor k B hS).map prod.fst
    rw [← Functor.map_comp, ← Functor.map_comp, hfst]
  · simp only [Category.assoc, coverSelfProductToBaseChange_comp_snd]
    show (pointsFunctor k B hS).map (doubledRelation k K σ).source ≫
        (pointsFunctor k B hS).map prod.snd ≫
          Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
            (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ) =
      (pointsFunctor k B hS).map (doubledRelation k K σ).target ≫
        (pointsFunctor k B hS).map prod.snd ≫
          Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
            (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ)
    rw [← Category.assoc ((pointsFunctor k B hS).map (doubledRelation k K σ).source),
      ← Category.assoc ((pointsFunctor k B hS).map (doubledRelation k K σ).target),
      ← Functor.map_comp, ← Functor.map_comp, hsnd, hsnd', Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc]
    exact congrArg (fun z => (pointsFunctor k B hS).map
      (prod.snd (X := coverOverBase k K) (Y := relationOverBase k K)) ≫ z)
      (Stacks.Groupoids.sourceMap_toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ))

/-- **The comparison map of part (6), descended to the quotient of the base-changed relation.**
This is the map whose bijectivity identifies the base change `X'` with the quotient of
`U ×_S U` by the base-changed relation. -/
def quotientToBaseChange (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Stacks.Groupoids.quotientPresheaf (Over.post (X := B.obj hS) B.inclusion)
        (doubledRelation k K σ) ⟶
      baseChangePresheaf k K B hS hdegree σ hσ :=
  coequalizer.desc (coverSelfProductToBaseChange k K B hS hdegree σ hσ)
    (doubledRelation_comp_coverSelfProductToBaseChange k K B hS hdegree σ hσ)

/-- The quotient map of the base-changed relation followed by `quotientToBaseChange` is
`coverSelfProductToBaseChange`. -/
theorem toQuotientPresheaf_comp_quotientToBaseChange (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Stacks.Groupoids.toQuotientPresheaf (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ) ≫
        quotientToBaseChange k K B hS hdegree σ hσ =
      coverSelfProductToBaseChange k K B hS hdegree σ hσ :=
  coequalizer.π_desc (coverSelfProductToBaseChange k K B hS hdegree σ hσ)
    (doubledRelation_comp_coverSelfProductToBaseChange k K B hS hdegree σ hσ)

/-- **The descended comparison map is locally surjective.** The comparison map from the
self-product is a base change of the quotient map, which is locally surjective, and local
surjectivity is stable under base change; the descended map inherits it through the
factorisation. -/
theorem isLocallySurjective_quotientToBaseChange (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      (quotientToBaseChange k K B hS hdegree σ hσ) := by
  have _hq : Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ)) :=
    Stacks.Groupoids.isLocallySurjective_toQuotientSheaf _ _ _
  have _h0 : Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      (coverSelfProductToBaseChange k K B hS hdegree σ hσ) :=
    Presheaf.isLocallySurjective_of_isPullback _
      (isPullback_coverSelfProductToBaseChange k K B hS hdegree σ hσ)
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (toQuotientPresheaf_comp_quotientToBaseChange k K B hS hdegree σ hσ)

/-- **The descended comparison map is injective, not merely locally injective.** Two points of
the self-product with the same image have the same first coordinate and second coordinates with
the same class in the quotient; the relation is the kernel pair of the quotient map
(`Stacks.Groupoids.isPullback_toQuotientSheaf_self`, a Cartesian square of presheaves, hence
Cartesian in every degree), so the second coordinates are related by an honest point of the
relation scheme, and that point together with the common first coordinate is a point of the
base-changed relation joining the two. -/
theorem injective_quotientToBaseChange (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) (T : (BigFppfOver B (base k) hS)ᵒᵖ) :
    Function.Injective ((quotientToBaseChange k K B hS hdegree σ hσ).app T) := by
  have _hrel := twistedRelation_isEtaleEquivalenceRelation k K hdegree σ hσ
  -- the relation is the kernel pair of the quotient map, in every degree
  have hkp := (Stacks.Groupoids.isPullback_toQuotientSheaf_self
    (BigFppfOver.topology B (base k) hS) (Over.post (X := B.obj hS) B.inclusion)
    (twistedRelation k K σ)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (relationOverBase k K))
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (coverOverBase k K))).map
    ((evaluation (BigFppfOver B (base k) hS)ᵒᵖ (Type u)).obj T)
  -- the projection onto the quotient presheaf is pointwise surjective
  have hπ : Function.Surjective
      ((Stacks.Groupoids.toQuotientPresheaf (Over.post (X := B.obj hS) B.inclusion)
        (doubledRelation k K σ)).app T) := by
    have hepi : Epi (Stacks.Groupoids.toQuotientPresheaf
        (Over.post (X := B.obj hS) B.inclusion) (doubledRelation k K σ)) := coequalizer.π_epi
    have : Epi ((Stacks.Groupoids.toQuotientPresheaf
        (Over.post (X := B.obj hS) B.inclusion) (doubledRelation k K σ)).app T) :=
      (NatTrans.epi_iff_epi_app _).1 hepi T
    exact surjective_of_epi _
  have hfac : ∀ w, (quotientToBaseChange k K B hS hdegree σ hσ).app T
      ((Stacks.Groupoids.toQuotientPresheaf (Over.post (X := B.obj hS) B.inclusion)
        (doubledRelation k K σ)).app T w) =
      (coverSelfProductToBaseChange k K B hS hdegree σ hσ).app T w := by
    intro w
    have h := congrArg (fun η => η.app T w)
      (toQuotientPresheaf_comp_quotientToBaseChange k K B hS hdegree σ hσ)
    simpa using h
  have hrel : ∀ x, (Stacks.Groupoids.toQuotientPresheaf
        (Over.post (X := B.obj hS) B.inclusion) (doubledRelation k K σ)).app T
        ((Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ)).app T x) =
      (Stacks.Groupoids.toQuotientPresheaf (Over.post (X := B.obj hS) B.inclusion)
        (doubledRelation k K σ)).app T
        ((Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ)).app T x) := by
    intro x
    have h := congrArg (fun η => η.app T x)
      (coequalizer.condition
        (Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ))
        (Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion)
          (doubledRelation k K σ)))
    simpa using h.symm
  intro α β hαβ
  obtain ⟨w₁, rfl⟩ := hπ α
  obtain ⟨w₂, rfl⟩ := hπ β
  rw [hfac, hfac] at hαβ
  -- the two components of the comparison map
  have hcfst : ∀ w, (pullback.fst (pointsCoverToBase k K B hS)
        (quotientBaseMap k K hdegree σ hσ B hS)).app T
        ((coverSelfProductToBaseChange k K B hS hdegree σ hσ).app T w) = w ≫ prod.fst :=
    fun w => congrArg (fun η => η.app T w)
      (coverSelfProductToBaseChange_comp_fst k K B hS hdegree σ hσ)
  have hcsnd : ∀ w, (pullback.snd (pointsCoverToBase k K B hS)
        (quotientBaseMap k K hdegree σ hσ B hS)).app T
        ((coverSelfProductToBaseChange k K B hS hdegree σ hσ).app T w) =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ)).app T
        (w ≫ prod.snd) :=
    fun w => congrArg (fun η => η.app T w)
      (coverSelfProductToBaseChange_comp_snd k K B hS hdegree σ hσ)
  have hc₁ : w₁ ≫ prod.fst = w₂ ≫ prod.fst :=
    (hcfst w₁).symm.trans ((congrArg ((pullback.fst (pointsCoverToBase k K B hS)
      (quotientBaseMap k K hdegree σ hσ B hS)).app T) hαβ).trans (hcfst w₂))
  have hc₂ : (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ)).app T
        (w₁ ≫ prod.snd) =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
        (Over.post (X := B.obj hS) B.inclusion) (twistedRelation k K σ)).app T
        (w₂ ≫ prod.snd) :=
    (hcsnd w₁).symm.trans ((congrArg ((pullback.snd (pointsCoverToBase k K B hS)
      (quotientBaseMap k K hdegree σ hσ B hS)).app T) hαβ).trans (hcsnd w₂))
  -- the point of the relation scheme joining the two second coordinates
  obtain ⟨r, hr₁, hr₂⟩ := Types.exists_of_isPullback hkp (w₁ ≫ prod.snd) (w₂ ≫ prod.snd) hc₂
  -- the point of the base-changed relation joining the two
  have hjoin : ∀ (w : (pointsFunctor k B hS).obj (coverOverBase k K ⨯ coverOverBase k K) |>.obj T)
      (a : _ ⟶ _) (f : relationOverBase k K ⟶ coverOverBase k K), a = w ≫ prod.fst →
      r ≫ f = w ≫ prod.snd → prod.lift a r ≫ prod.map (𝟙 (coverOverBase k K)) f = w :=
    fun w a f ha hf => prod.hom_ext (by simp [ha]) (by simp [hf])
  have htgt := hjoin w₁ _ (relationFirst k K) rfl (by rw [← twistedRelation_target]; exact hr₁)
  have hsrc := hjoin w₂ (w₁ ≫ prod.fst) (relationSecond k K σ) hc₁
    (by rw [← twistedRelation_source]; exact hr₂)
  rw [← htgt, ← hsrc, ← doubledRelation_target, ← doubledRelation_source]
  exact hrel _

/-- **The glued scheme represents the base change of part (6).** The base change
`X' = S' ×_S X` is isomorphic to the functor of points of two copies of the chart glued along
the puncture, hence is a scheme.

Both the comparison map to the base change and the comparison map to the functor of points of
the glued scheme are locally bijective maps out of the quotient presheaf of the base-changed
relation, so they identify their two targets. The second is locally bijective by the
representability criterion of Stacks 03C5: the comparison map of part (6) is an fppf covering
(`doubledChartsToGlued_fppf`), hence a local surjection on functors of points, and the
base-changed relation is exactly its kernel pair (`isPullback_doubledRelation`). -/
theorem exists_isIso_baseChangePresheaf (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    ∃ χ : baseChangePresheaf k K B hS hdegree σ hσ ⟶
        (pointsFunctor k B hS).obj (doubledOverBase k K),
      IsIso χ := by
  obtain ⟨hflat, hfp, hsurj⟩ := doubledChartsToGlued_fppf k K
  have _hflat : Flat (doubledChartsToGlued k K) := hflat
  have _hfp : LocallyOfFinitePresentation (doubledChartsToGlued k K) := hfp
  have _hsurj : Surjective (doubledChartsToGlued k K) := hsurj
  have _hF : Flat (doubledSelfProductToGlued k K hdegree σ hσ).left := by
    rw [doubledSelfProductToGlued_left]; infer_instance
  have _hP : LocallyOfFinitePresentation (doubledSelfProductToGlued k K hdegree σ hσ).left := by
    rw [doubledSelfProductToGlued_left]; infer_instance
  have _hSu : Surjective (doubledSelfProductToGlued k K hdegree σ hσ).left := by
    rw [doubledSelfProductToGlued_left]; infer_instance
  -- the two hypotheses of the representability criterion of Stacks 03C5
  have _hU := isLocallySurjective_points_map_of_fppf B (base k) hS
    (doubledSelfProductToGlued k K hdegree σ hσ)
  have _hRiso := isIso_pullbackLift_doubledRelation k K hdegree σ hσ
  have _hRmap : IsIso ((pointsFunctor k B hS).map
      (pullback.lift (doubledRelation k K σ).target (doubledRelation k K σ).source
        (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))) :=
    inferInstance
  have _hR : Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      ((pointsFunctor k B hS).map
        (pullback.lift (doubledRelation k K σ).target (doubledRelation k K σ).source
          (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))) :=
    inferInstance
  -- the comparison map to the functor of points of the glued scheme
  have _hMinj := Stacks.Groupoids.quotientPresheafToPoints_isLocallyInjective
    (BigFppfOver.topology B (base k) hS) (Over.post (X := B.obj hS) B.inclusion)
    (doubledRelation k K σ) (doubledSelfProductToGlued k K hdegree σ hσ)
    (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ) _hR
  have _hMsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      (Stacks.Groupoids.quotientPresheafToPoints (Over.post (X := B.obj hS) B.inclusion)
        (doubledRelation k K σ) (doubledSelfProductToGlued k K hdegree σ hσ)
        (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ)) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (Stacks.Groupoids.toQuotientPresheaf_comp_quotientPresheafToPoints
        (Over.post (X := B.obj hS) B.inclusion) (doubledRelation k K σ)
        (doubledSelfProductToGlued k K hdegree σ hσ)
        (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))
  -- the comparison map to the base change
  have _hBsurj := isLocallySurjective_quotientToBaseChange k K B hS hdegree σ hσ
  have _hBinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B (base k) hS)
      (quotientToBaseChange k K B hS hdegree σ hσ) :=
    Presheaf.isLocallyInjective_of_injective _ _
      (injective_quotientToBaseChange k K B hS hdegree σ hσ)
  obtain ⟨χ, hχ, -⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective
    (BigFppfOver.topology B (base k) hS) (quotientToBaseChange k K B hS hdegree σ hσ)
    (Stacks.Groupoids.quotientPresheafToPoints (Over.post (X := B.obj hS) B.inclusion)
      (doubledRelation k K σ) (doubledSelfProductToGlued k K hdegree σ hσ)
      (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (doubledOverBase k K))
  exact ⟨χ, Presheaf.isIso_of_isLocallyBijective_fac _ _ _
    (isSheaf_baseChangePresheaf k K B hS hdegree σ hσ)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (doubledOverBase k K)) hχ⟩

/-- **Stacks 03FN, part (6).** There is a surjective, finite, étale morphism `S' ⟶ S` such
that the base change `X' = S' ×_S X` is a scheme: take `S' = U = Spec K[x]`, the chart itself,
and then `X'` is two copies of `U` glued along the puncture.

The chart is surjective, finite and étale over the base because `K[x]` is the base change of the
finite separable extension `K/k` along `k → k[x]`. For the base change: pulling the quotient
`X = U/R` back along `U ⟶ S` presents `X'` as the quotient of the self-product `U ×_S U` by the
base change of `R`; the self-product is two copies of `U` (`coverFiberProductSplitIso`), and the
induced relation is exactly the gluing relation of two copies of `U` along the puncture, which is
`isPullback_doubledRelation` — the base-changed relation is the kernel pair of the map to the
glued scheme. The representability criterion of Stacks 03C5 then identifies the quotient of the
base-changed relation with the functor of points of the glued scheme, and `X'` is that same
quotient. -/
@[stacks 03FN "part (6): finite etale cover trivialising X"]
theorem surjective_isFinite_etale_and_baseChange_isScheme
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (Surjective (coverMap k K) ∧ IsFinite (coverMap k K) ∧ Etale (coverMap k K)) ∧
      ∃ χ : baseChangePresheaf k K B hS hdegree σ hσ ⟶
          (pointsFunctor k B hS).obj (doubledOverBase k K),
        IsIso χ :=
  ⟨surjective_isFinite_etale_coverMap k K,
    exists_isIso_baseChangePresheaf k K B hS hdegree σ hσ⟩

end BaseChange

end AlgebraicGeometry.TwistedDoubledOrigin

end
