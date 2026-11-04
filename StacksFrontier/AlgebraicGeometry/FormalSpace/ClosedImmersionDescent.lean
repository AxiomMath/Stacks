module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Descent of closed immersions of formal algebraic spaces

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of
`S`. This file proves that `f` is a closed immersion as soon as there is a family
`{Y_i ⟶ Y}` whose induced map from the coproduct is a surjection of sheaves and along which
every base change of `f` is a closed immersion. Nothing is assumed of `f` itself; in
particular representability by algebraic spaces, which is half of the definition of a closed
immersion, is part of the conclusion rather than a hypothesis.

This is the descent step of Stacks 0GHY, and it contains the sufficiency of both of that tag's
descent conditions: condition (4), whose family is the étale atlas of a formal algebraic space,
and condition (5), whose family is a single surjective flat morphism locally of finite
presentation.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_locallySurjectiveFamily`:
  **Stacks 0GHY**, the descent step along a surjection of sheaves.

## Implementation notes

The statement is made for an arbitrary family rather than for either of the two shapes the
source gives, so that one proof serves both, and it asks nothing of `f`.

The proof tests `f` against one scheme-valued point `T ⟶ Y` of the target at a time. That
point lies, locally on `T`, in the image of a single member of the family, by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff`, so over each arrow of the resulting
covering sieve of `T` the base change of `f` is a base change of one of the given closed
immersions, and in particular is represented by an object of the site. The base change of `f`
along the point itself is therefore pointwise small —
`AlgebraicGeometry.FormalSpace.small_of_representable_on_coveringSieve`: a section of it over
an object restricts, over a covering sieve of that object, to sections of represented fibres,
and the site is essentially small, so a small amount of data determines the section — hence
the universe lift of a morphism of presheaves in the value universe of the site, where
effective fppf descent of closed immersions along the covering sieves of the site is
available: closed immersions of schemes are affine monomorphisms locally of finite type, so
effective descent along the covering sieves at the affine monomorphisms locally of finite type
applies, and the property itself is recovered because closed immersions are Zariski local on
the target and satisfy fppf descent.

That smallness argument is why no representability hypothesis on `f` is needed: the covering
sieve supplies the pointwise smallness of the base change along a point, and the representing
objects the descent returns then exhibit the base changes as algebraic spaces, which is the
representability of `f`.

Conditions (3), (4) and (5) themselves, and the remaining arrows of the equivalence, are in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionTfae`. Two features of the source
are worth recording. The printed form of condition (5) asks that `X ×_Y Z ⟶ X` be a closed
immersion; that is a typo, since the descent it is used for concerns the projection to `Z`,
and the intended condition is that `X ×_Y Z ⟶ Z` be a closed immersion. The printed list also
ends with an editorial note asking for more conditions, so the source's list is open-ended;
the equivalence formalized is the one among conditions (1)–(5).

## References

* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The descent step of Stacks 0GHY -/

/-- A closed immersion of schemes is an affine monomorphism locally of finite type. -/
@[ega "I 10.14.3" "special case",
  ega "I 6.6.6" "(i), closed immersions",
  ega "IV 1.3.4" "Clause (i), special case"]
private theorem isClosedImmersion_le_affineMonoLocallyOfFiniteType :
    (@AlgebraicGeometry.IsClosedImmersion.{u}) ≤
      AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u} := by
  intro X Y f hf
  have _ : AlgebraicGeometry.IsClosedImmersion f := hf
  exact ⟨⟨((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono f).mp hf).2,
    inferInstance⟩, inferInstance⟩

/-- Closed immersions of schemes satisfy fppf descent: a morphism whose base change along a
surjective flat morphism locally of finite presentation is a closed immersion is itself one. -/
private theorem isClosedImmersion_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (@AlgebraicGeometry.IsClosedImmersion.{u})
      (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation) :=
  AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc _

/-- Closed immersions of schemes descend effectively along the covering sieves of the big fppf
site of `S`: a morphism of sheaves whose base change along every arrow of a covering sieve of
the base is represented by a closed immersion of the site is represented by one over the
base. -/
private theorem isEffectiveDescentAlongCoveringSieve_isClosedImmersion :
    Space.IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) :=
  have _ := isClosedImmersion_descendsAlong_fppf.{u}
  Space.isEffectiveDescentAlongCoveringSieve_of_le
    (Space.isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType B S hS)
    isClosedImmersion_le_affineMonoLocallyOfFiniteType.{u}

/-- **Closed immersions descend effectively along the covering sieves of the big fppf site of
`S`**: a morphism of sheaves whose base change along every arrow of a covering sieve of the base
is represented by a closed immersion of the site is represented by one over the base. -/
alias closedImmersion_isEffectiveDescentAlongCoveringSieve :=
  isEffectiveDescentAlongCoveringSieve_isClosedImmersion

/-- The property of being represented by a closed immersion of the big fppf site of `S`, for a
morphism of presheaves of `Type (u + 1)` tested against the universe-lifted scheme-valued
points: the property appearing in `AlgebraicGeometry.FormalSpace.IsClosedImmersion`. -/
private abbrev relativeIsClosedImmersion :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})

/-- Being represented by a closed immersion of the site is invariant under isomorphism. -/
private theorem relativeIsClosedImmersion_respectsIso :
    (relativeIsClosedImmersion B S hS).RespectsIso :=
  (MorphismProperty.relative_isStableUnderBaseChange _ (F := uliftYoneda.{u + 1})).respectsIso

/-- Being represented by a closed immersion of the site is read off the base change along any
one of two equal morphisms. -/
private theorem closedImmersionPresheafProperty_pullback_snd_congr
    {F G Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) {g g' : Z ⟶ G} (hg : g = g')
    (h : Space.closedImmersionPresheafProperty B S hS (pullback.snd a g)) :
    Space.closedImmersionPresheafProperty B S hS (pullback.snd a g') := by
  subst hg
  exact h

/-- **Descent of closed immersions along a covering sieve, in the value universe of the
site.** A morphism to a representable presheaf out of a sheaf is represented by a closed
immersion of the site as soon as its base change along every arrow of some covering sieve of
the base is. -/
theorem presheafIsClosedImmersion_of_coveringSieve
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U : BigFppfOver B S hS} (a : F ⟶ yoneda.obj U)
    {T : Sieve U} (hT : T ∈ BigFppfOver.topology B S hS U)
    (hall : ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), T q →
      Space.closedImmersionPresheafProperty B S hS (pullback.snd a (yoneda.map q))) :
    Space.closedImmersionPresheafProperty B S hS a := by
  have hall' : ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), T q →
      Space.closedImmersionPresheafProperty B S hS
        (pullback.snd a (yoneda.map q ≫ 𝟙 (yoneda.obj U))) := fun V q hq ↦
    closedImmersionPresheafProperty_pullback_snd_congr B S hS a
      (Category.comp_id (yoneda.map q)).symm (hall q hq)
  have h0 : Space.closedImmersionPresheafProperty B S hS (pullback.snd a (𝟙 (yoneda.obj U))) :=
    isEffectiveDescentAlongCoveringSieve_isClosedImmersion B S hS a hF
      (BigFppfOver.isSheaf_yoneda_obj B S hS U) (𝟙 (yoneda.obj U)) T hT hall'
  have _ : (Space.closedImmersionPresheafProperty B S hS).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _ (F := yoneda)).respectsIso
  have hid : IsPullback (𝟙 F) a a (𝟙 (yoneda.obj U)) := IsPullback.of_id_fst
  have h1 := ((Space.closedImmersionPresheafProperty B S hS).cancel_left_of_respectsIso
    (hid.isoIsPullback _ _ (IsPullback.of_hasPullback a (𝟙 (yoneda.obj U)))).hom
    (pullback.snd a (𝟙 (yoneda.obj U)))).mpr h0
  rwa [hid.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback a (𝟙 (yoneda.obj U)))] at h1

/-- The universe lift on presheaves of types on the big fppf site of `S`. -/
public abbrev uliftPresheaf : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}

/-- Being represented by a closed immersion of the site is unchanged by the universe lift. -/
private theorem relativeIsClosedImmersion_map_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    relativeIsClosedImmersion B S hS ((uliftPresheaf B S hS).map a) ↔
      Space.closedImmersionPresheafProperty B S hS a :=
  Space.relative_comp_map_iff yoneda (uliftPresheaf B S hS) _ a

/-- A morphism of presheaves on the big fppf site of `S` which is the universe lift of a
morphism represented by a closed immersion of the site is itself represented by one. -/
private theorem relativeIsClosedImmersion_of_eq_map
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    {b : (uliftPresheaf B S hS).obj F ⟶ (uliftPresheaf B S hS).obj G}
    (hb : (uliftPresheaf B S hS).map a = b)
    (h : Space.closedImmersionPresheafProperty B S hS a) : relativeIsClosedImmersion B S hS b := by
  subst hb
  exact (relativeIsClosedImmersion_map_iff B S hS a).mpr h

/-! ### Pointwise smallness along a covering sieve -/

/-- A section of a presheaf over an object, read as a morphism out of the universe-lifted
Yoneda presheaf of that object, restricts along a morphism of the site by precomposition. -/
private theorem uliftYonedaEquiv_symm_map
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {Z V : BigFppfOver B S hS} (g : Z ⟶ V)
    (z : A.obj (Opposite.op V)) :
    uliftYonedaEquiv.{u + 1}.symm (A.map g.op z) =
      (uliftYoneda.{u + 1}).map g ≫ uliftYonedaEquiv.{u + 1}.symm z := by
  rw [Equiv.symm_apply_eq]
  simpa using uliftYonedaEquiv_naturality.{u + 1} (uliftYonedaEquiv.{u + 1}.symm z) g.op

/-- **The fibre of a represented base change is `u`-small.** If the base change of
`m : A ⟶ uliftYoneda U` along a scheme-valued point `q` of `U` is the universe-lifted Yoneda
presheaf of an object `W` of the site, then the sections of `A` over `V` lying above `q` are a
`u`-small family: such a section is a lift of the identity of `V` through the projection, hence
is determined by a morphism of the site `V ⟶ W`. -/
private theorem small_fiber_of_isPullback
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U V W : BigFppfOver B S hS}
    {m : A ⟶ (uliftYoneda.{u + 1}).obj U} {q : V ⟶ U}
    {p : (uliftYoneda.{u + 1}).obj W ⟶ A} {π : W ⟶ V}
    (hpb : IsPullback p ((uliftYoneda.{u + 1}).map π) m ((uliftYoneda.{u + 1}).map q)) :
    Small.{u} {a : A.obj (Opposite.op V) //
      uliftYonedaEquiv.{u + 1}.symm a ≫ m = (uliftYoneda.{u + 1}).map q} := by
  have hhom : Small.{u} ((uliftYoneda.{u + 1}).obj V ⟶ (uliftYoneda.{u + 1}).obj W) :=
    small_of_surjective (f := fun t : V ⟶ W => (uliftYoneda.{u + 1}).map t)
      (fun g => ⟨(ULiftYoneda.fullyFaithful _).preimage g,
        (ULiftYoneda.fullyFaithful _).map_preimage g⟩)
  apply small_of_injective
    (f := fun a => hpb.lift (uliftYonedaEquiv.{u + 1}.symm a.1) (𝟙 _)
      (by rw [Category.id_comp]; exact a.2))
  intro a b hab
  have h1 : uliftYonedaEquiv.{u + 1}.symm a.1 = uliftYonedaEquiv.{u + 1}.symm b.1 := by
    rw [← hpb.lift_fst (uliftYonedaEquiv.{u + 1}.symm a.1) (𝟙 _)
        (by rw [Category.id_comp]; exact a.2),
      ← hpb.lift_fst (uliftYonedaEquiv.{u + 1}.symm b.1) (𝟙 _)
        (by rw [Category.id_comp]; exact b.2)]
    exact congrArg (fun z => z ≫ p) hab
  exact Subtype.ext (uliftYonedaEquiv.{u + 1}.symm.injective h1)

/-- **Pointwise `u`-smallness descends along a covering sieve.** A sheaf `A` on the big fppf
site of `S` with values in `Type (u + 1)` mapping to the universe-lifted Yoneda presheaf of an
object `U` is pointwise `u`-small as soon as the base change along every arrow of some covering
sieve of `U` is representable.

A section `x` of `A` over `V₀` restricts to the point `k` of `U` it lies above, and the pullback
of the sieve along `k` is a covering sieve of `V₀`; over each of its arrows the restriction of
`x` lies in a fibre of `m` over an arrow of the given sieve, which is `u`-small by
`AlgebraicGeometry.FormalSpace.small_fiber_of_isPullback`. The site being essentially `u`-small,
recording those restrictions is a `u`-small amount of data, and it determines `x` because `A` is
separated for the covering sieve. -/
private theorem small_of_representable_on_coveringSieve
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A)
    {U : BigFppfOver B S hS} (m : A ⟶ (uliftYoneda.{u + 1}).obj U)
    {T : Sieve U} (hT : T ∈ BigFppfOver.topology B S hS U)
    (hrep : ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), T q →
      ∃ (W : BigFppfOver B S hS) (p : (uliftYoneda.{u + 1}).obj W ⟶ A) (π : W ⟶ V),
        IsPullback p ((uliftYoneda.{u + 1}).map π) m ((uliftYoneda.{u + 1}).map q))
    (V₀ : BigFppfOver B S hS) : Small.{u} (A.obj (Opposite.op V₀)) := by
  classical
  have hC : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  let E := equivSmallModel.{u} (BigFppfOver B S hS)
  let Fib (V : BigFppfOver B S hS) : Type (u + 1) :=
    Σ k : {k : V ⟶ U // T k},
      {a : A.obj (Opposite.op V) //
        uliftYonedaEquiv.{u + 1}.symm a ≫ m = (uliftYoneda.{u + 1}).map k.1}
  have hFib (V) : Small.{u} (Fib V) := by
    have hk (k : {k : V ⟶ U // T k}) :
        Small.{u} {a : A.obj (Opposite.op V) //
          uliftYonedaEquiv.{u + 1}.symm a ≫ m = (uliftYoneda.{u + 1}).map k.1} := by
      obtain ⟨W, p, π, hpb⟩ := hrep k.1 k.2
      exact small_fiber_of_isPullback B S hS hpb
    exact inferInstance
  let encode : A.obj (Opposite.op V₀) →
      (V : SmallModel.{u} (BigFppfOver B S hS)) → (E.inverse.obj V ⟶ V₀) →
        Fib (E.inverse.obj V) → Prop :=
    fun x V g t => t.2.1 = A.map g.op x
  apply small_of_injective (f := encode)
  intro x y h
  set k : V₀ ⟶ U := (ULiftYoneda.fullyFaithful (BigFppfOver B S hS)).preimage
    (uliftYonedaEquiv.{u + 1}.symm x ≫ m) with hkdef
  have hk : (uliftYoneda.{u + 1}).map k = uliftYonedaEquiv.{u + 1}.symm x ≫ m :=
    (ULiftYoneda.fullyFaithful (BigFppfOver B S hS)).map_preimage _
  refine hA.isSeparated V₀ (Sieve.pullback k T)
    ((BigFppfOver.topology B S hS).pullback_stable _ hT) x y ?_
  intro Z g hg
  have hgT : T (g ≫ k) := hg
  let V := E.functor.obj Z
  let e := E.unitIso.app Z
  have hgT' : T ((e.inv ≫ g) ≫ k) := by
    rw [Category.assoc]
    exact T.downward_closed hgT e.inv
  let t : Fib (E.inverse.obj V) :=
    ⟨⟨(e.inv ≫ g) ≫ k, hgT'⟩, ⟨A.map (e.inv ≫ g).op x, by
      rw [uliftYonedaEquiv_symm_map B S hS (e.inv ≫ g) x, Category.assoc, ← hk,
        ← Functor.map_comp]⟩⟩
  have hx : encode x V (e.inv ≫ g) t := rfl
  have hy : encode y V (e.inv ≫ g) t := by rw [← h]
  have hxy : A.map e.inv.op (A.map g.op x) = A.map e.inv.op (A.map g.op y) := by
    simpa only [op_comp, A.map_comp, types_comp_apply] using hx.symm.trans hy
  exact (CategoryTheory.injective_of_mono (A.map e.inv.op)) hxy

/-- The source of a morphism to a universe-lifted Yoneda presheaf which is represented by
morphisms of the site is an algebraic space over `S`: the base change along the identity of
the target exhibits the source as a universe-lifted Yoneda presheaf. -/
private theorem isAlgebraicSpaceULift_of_relativelyRepresentable
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U : BigFppfOver B S hS}
    {m : A ⟶ (uliftYoneda.{u + 1}).obj U}
    (hm : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable m) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS A := by
  obtain ⟨W, π, s, hpb⟩ := hm (𝟙 ((uliftYoneda.{u + 1}).obj U))
  have _ : IsIso s := hpb.isIso_fst_of_isIso
  exact Space.isAlgebraicSpaceULift_of_iso B S hS (asIso s)
    (Space.isAlgebraicSpaceULift_uliftYoneda B S hS W)

/-- The fibre product of two morphisms of fppf sheaves, formed in sheaves, is a pullback square
of the underlying presheaves, the inclusion of sheaves into presheaves creating limits. -/
private theorem isPullback_pullback_hom {X Y Z : FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (pullback.fst f g).hom (pullback.snd f g).hom f.hom g.hom :=
  (IsPullback.of_hasPullback f g).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- The base change of a morphism of fppf sheaves along a scheme-valued point of its target,
formed in presheaves, is again a sheaf: it is isomorphic to the fibre product taken in
sheaves, the inclusion of sheaves into presheaves creating limits. -/
private theorem isSheaf_pullback_uliftYoneda {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {U : BigFppfOver B S hS} (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.1) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ f.hom) := by
  let g : yonedaSheaf B S hS U ⟶ Y := ⟨ξ⟩
  exact (Presheaf.isSheaf_of_iso_iff (isPullback_pullback_hom B S hS f g).flip.isoPullback).mp
    (pullback f g).2

/-! ### The descent step -/

/-- **Descent of closed immersions along a covering sieve.** A morphism `m` to a
universe-lifted representable presheaf whose source is an fppf sheaf is represented by a closed
immersion of the site as soon as every base change of `m` along an arrow of some covering sieve
of the base is.

The hypothesis already makes the source pointwise `u`-small, by
`AlgebraicGeometry.FormalSpace.small_of_representable_on_coveringSieve`, so `m` is the universe
lift of a morphism of presheaves in the value universe of the site, where effective fppf descent
of closed immersions is available. No algebraic-space hypothesis on the source is needed: that
the source is an algebraic space is part of the conclusion. -/
private theorem relativeIsClosedImmersion_of_coveringSieve
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A)
    {U : BigFppfOver B S hS} (m : A ⟶ (uliftYoneda.{u + 1}).obj U)
    {T : Sieve U} (hT : T ∈ BigFppfOver.topology B S hS U)
    (hall : ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), T q →
      ∀ ⦃P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)⦄ (p : P ⟶ (uliftYoneda.{u + 1}).obj V)
        (r : P ⟶ A), IsPullback p r ((uliftYoneda.{u + 1}).map q) m →
        relativeIsClosedImmersion B S hS p) :
    relativeIsClosedImmersion B S hS m := by
  have hsmall : FunctorToTypes.Small.{u} A := by
    intro Tob
    refine small_of_representable_on_coveringSieve B S hS hA m hT ?_ Tob.unop
    intro V q hq
    obtain ⟨W, π, s, hpb⟩ := (hall q hq (pullback.fst ((uliftYoneda.{u + 1}).map q) m)
      (pullback.snd ((uliftYoneda.{u + 1}).map q) m)
      (IsPullback.of_hasPullback _ _)).rep (𝟙 ((uliftYoneda.{u + 1}).obj V))
    have _ : IsIso s := hpb.isIso_fst_of_isIso
    refine ⟨W, s ≫ pullback.snd ((uliftYoneda.{u + 1}).map q) m, π, IsPullback.flip ?_⟩
    apply (IsPullback.of_hasPullback ((uliftYoneda.{u + 1}).map q) m).of_iso'
      (asIso s) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa using hpb.w
    all_goals simp
  let F := FunctorToTypes.shrink.{u} A
  let e : F ⋙ uliftFunctor.{u + 1} ≅ A := Space.shrinkCompUliftFunctorIso A
  have hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F :=
    Presheaf.isSheaf_of_isSheaf_comp _ F uliftFunctor
      ((Presheaf.isSheaf_of_iso_iff e).mpr hA)
  obtain ⟨a, ha⟩ := (uliftPresheaf B S hS).map_surjective
    (X := F) (Y := yoneda.obj U) (e.hom ≫ m)
  have _ := relativeIsClosedImmersion_respectsIso B S hS
  have key : Space.closedImmersionPresheafProperty B S hS a := by
    refine presheafIsClosedImmersion_of_coveringSieve B S hS hF a hT ?_
    intro V q hq
    refine (relativeIsClosedImmersion_map_iff B S hS (pullback.snd a (yoneda.map q))).mp ?_
    refine hall q hq ((uliftPresheaf B S hS).map (pullback.snd a (yoneda.map q)))
      ((uliftPresheaf B S hS).map (pullback.fst a (yoneda.map q)) ≫ e.hom) ?_
    refine (((IsPullback.of_hasPullback a (yoneda.map q)).map
      (uliftPresheaf B S hS)).flip).of_iso' (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [uliftYoneda]
    · simp
    · simp [uliftYoneda]
    · rw [ha]
      exact (Iso.inv_hom_id_assoc e m).trans (Category.comp_id m).symm
  exact ((relativeIsClosedImmersion B S hS).cancel_left_of_respectsIso e.hom m).mp
    (relativeIsClosedImmersion_of_eq_map B S hS ha key)

/-- **Stacks 0GHY**, the descent step along a surjection of sheaves: a morphism `f : X ⟶ Y` of
fppf sheaves on the big fppf site of `S` is a closed immersion as soon as there is a family
`{Y_i ⟶ Y}` whose induced map from the coproduct is a surjection of sheaves with every base
change `X ×_Y Y_i ⟶ Y_i` a closed immersion.

A scheme-valued point of `Y` lies, locally on the point, in the image of a single member of the
family; over that covering sieve the base change of `f` is a base change of one of the given
closed immersions, so the base change of `f` along the point is a closed immersion by effective
fppf descent of closed immersions.

Representability of `f` by algebraic spaces is **not** assumed: it is part of the conclusion,
and it is produced by the same descent. The base change of `f` along a point of `Y` is a sheaf,
and being represented by a closed immersion of the site after a covering sieve of that point
already makes it pointwise `u`-small, which is all the descent step needs; the representing
objects it returns then exhibit the base changes as algebraic spaces.

This is the sufficiency in both descent conditions of the source. For condition (4) the family
is the étale atlas of the target, and Definition 0AIM asks of it exactly that it be a surjection
of sheaves, so this *is* condition (4) implies condition (1):
`AlgebraicGeometry.FormalSpace.isClosedImmersion_iff_exists_affineEtaleCover`. For condition (5)
the family has one member, but the source asks only that it be surjective *on points*, so the
hypothesis must be upgraded first; that is done in
`AlgebraicGeometry.FormalSpace.isClosedImmersion_of_hasFlatClosedImmersionCover`, which is
condition (5) implies condition (1). -/
@[stacks 0GHY "the descent step along a surjection of sheaves, which is the sufficiency in \
conditions (4) and (5)"]
theorem isClosedImmersion_of_locallySurjectiveFamily {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (c : ∀ i, Yi i ⟶ Y)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c))
    (hci : ∀ i, IsClosedImmersion B S hS (pullback.snd f (c i))) :
    IsClosedImmersion B S hS f := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have key : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.1),
      relativeIsClosedImmersion B S hS (pullback.fst ξ f.hom) := ?_
  · exact ⟨fun U ξ => isAlgebraicSpaceULift_of_relativelyRepresentable B S hS (key U ξ).rep,
      fun U ξ => key U ξ⟩
  intro U ξ
  obtain ⟨T, hT, hlocal⟩ :=
    (Sheaf.isLocallySurjective_sigmaDesc_iff c).1 hsurj (uliftYonedaEquiv.{u + 1} ξ)
  refine relativeIsClosedImmersion_of_coveringSieve B S hS
    (isSheaf_pullback_uliftYoneda B S hS f ξ) (pullback.fst ξ f.hom) hT ?_
  intro V q hq P p r hpb
  obtain ⟨i, z, hz⟩ := hlocal q hq
  obtain ⟨hrepi, hpropi⟩ := hci i
  set η : (uliftYoneda.{u + 1}).obj V ⟶ (Yi i).1 := uliftYonedaEquiv.{u + 1}.symm z with hη
  have hfac : η ≫ (c i).hom = (uliftYoneda.{u + 1}).map q ≫ ξ := by
    rw [hη, uliftYonedaEquiv_symm_comp, hz, uliftYonedaEquiv_naturality]
    exact uliftYonedaEquiv.symm_apply_apply _
  have hp1 : IsPullback (pullback.fst η (pullback.snd f (c i)).hom)
      (pullback.snd η (pullback.snd f (c i)).hom ≫ (pullback.fst f (c i)).hom)
      ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom := by
    rw [← hfac]
    exact ((IsPullback.of_hasPullback η (pullback.snd f (c i)).hom).flip.paste_horiz
      (isPullback_pullback_hom B S hS f (c i))).flip
  have hp2 : IsPullback p (r ≫ pullback.snd ξ f.hom)
      ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom :=
    (hpb.flip.paste_horiz (IsPullback.of_hasPullback ξ f.hom).flip).flip
  have _ := relativeIsClosedImmersion_respectsIso B S hS
  have hR : relativeIsClosedImmersion B S hS
      (pullback.fst η (pullback.snd f (c i)).hom) := hpropi V η
  refine ((relativeIsClosedImmersion B S hS).cancel_left_of_respectsIso
    (hp1.isoIsPullback _ _ hp2).hom p).mp ?_
  rwa [hp1.isoIsPullback_hom_fst _ _ hp2]


end AlgebraicGeometry.FormalSpace

end
