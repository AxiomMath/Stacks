module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Permanence properties of integral and finite morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is integral, respectively finite, when its
base change along every morphism out of an affine object of the big fppf site of `S` is
represented by an affine object whose projection to the test object is an integral,
respectively finite, morphism of schemes. This file proves that both properties are stable
under base change, that each descends from a composite along a separated second leg, that a
finite morphism is quasi-finite, and that a morphism out of a finite coproduct of algebraic
spaces is finite as soon as its restriction to every summand is.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_of_isPullback` and
  `AlgebraicGeometry.Space.isFinite_of_isPullback`: a base change of an integral, respectively
  finite, morphism is integral, respectively finite.
  `AlgebraicGeometry.Space.isIntegralHom_pullback_snd` and
  `AlgebraicGeometry.Space.isFinite_pullback_snd` are the same for the chosen fibre product.
* `AlgebraicGeometry.Space.isIntegralHom_of_comp_of_isSeparated` and
  `AlgebraicGeometry.Space.isFinite_of_comp_of_isSeparated`: if a composite is integral,
  respectively finite, and its second leg is separated, then its first leg is integral,
  respectively finite.
* `AlgebraicGeometry.Space.isQuasiFinite_of_isFinite`: a finite morphism is quasi-finite.
* `AlgebraicGeometry.Space.isFinite_coproduct`: a morphism out of a finite coproduct of
  algebraic spaces whose restriction to each summand is finite is finite.
* `AlgebraicGeometry.Space.HoldsOnAffineBaseChange.comp`: the affine-base-change pattern of a
  property of scheme morphisms stable under composition is stable under composition.

## References

* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 04NY](https://stacks.math.columbia.edu/tag/04NY)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 081Z](https://stacks.math.columbia.edu/tag/081Z)
* [Stacks Project, Tag 0CYI](https://stacks.math.columbia.edu/tag/0CYI)
* [Stacks Project, Tag 0CZ2](https://stacks.math.columbia.edu/tag/0CZ2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Composition -/

/-- If `Q` is stable under composition and `f` and `g` satisfy `Q` on affine base changes, then
so does `f ≫ g`. -/
theorem HoldsOnAffineBaseChange.comp {Q : MorphismProperty Scheme.{u}}
    [Q.IsStableUnderComposition] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : HoldsOnAffineBaseChange B S hS Q f) (hg : HoldsOnAffineBaseChange B S hS Q g) :
    HoldsOnAffineBaseChange B S hS Q (f ≫ g) := by
  intro T hT ξ
  obtain ⟨V, p, j, hVpb, hVaff, hp⟩ := hg T hT ξ
  obtain ⟨W, q, i, hWpb, hWaff, hq⟩ := hf V hVaff j
  refine ⟨W, q ≫ p, i, ?_, hWaff, ?_⟩
  · simpa using hWpb.paste_vert hVpb
  · rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ hq hp

/-! ### Base change -/

/-- A base change of an integral morphism of algebraic spaces over `S` is integral: if `f'` sits
in a Cartesian square over `f`, then `f'` is integral as soon as `f` is. -/
@[stacks 03ZS "integral"]
theorem isIntegralHom_of_isPullback {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : IsIntegralHom B S hS f) : IsIntegralHom B S hS f' :=
  HoldsOnAffineBaseChange.of_isPullback sq hf

/-- A base change of a finite morphism of algebraic spaces over `S` is finite. -/
@[stacks 03ZS "finite"]
theorem isFinite_of_isPullback {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : IsFinite B S hS f) : IsFinite B S hS f' :=
  (isFinite_iff_holdsOnAffineBaseChange f').2
    (HoldsOnAffineBaseChange.of_isPullback sq ((isFinite_iff_holdsOnAffineBaseChange f).1 hf))

/-- The second projection of the chosen fibre product of an integral morphism of algebraic
spaces along an arbitrary morphism is integral. -/
theorem isIntegralHom_pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : IsIntegralHom B S hS f) : IsIntegralHom B S hS (pullback.snd f g) :=
  isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf

/-- The second projection of the chosen fibre product of a finite morphism of algebraic
spaces along an arbitrary morphism is finite. -/
theorem isFinite_pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z) (hf : IsFinite B S hS f) :
    IsFinite B S hS (pullback.snd f g) :=
  isFinite_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf

/-! ### Permanence along a separated morphism -/

/-- If a composite of morphisms of algebraic spaces over `S` is integral and its second leg is
separated, then its first leg is integral. -/
@[stacks 081Z "part (2): integral", ega "II 6.1.5" "(v) integral"]
theorem isIntegralHom_of_comp_of_isSeparated (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsIntegralHom B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsIntegralHom B S hS f := by
  simpa using isIntegralHom_comp B S hS
    (isIntegralHom_of_isClosedImmersion B S hS _
      (isClosedImmersion_graph_of_isSeparated B S hS f g hg))
    (isIntegralHom_pullback_snd B S hS (f ≫ g) g hfg)

/-- If a composite of morphisms of algebraic spaces over `S` is finite and its second leg is
separated, then its first leg is finite. -/
@[stacks 081Z "part (1): finite", ega "II 6.1.5" "(v) finite"]
theorem isFinite_of_comp_of_isSeparated (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsFinite B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsFinite B S hS f := by
  simpa using isFinite_comp B S hS
    (isFinite_of_isClosedImmersion B S hS _
      (isClosedImmersion_graph_of_isSeparated B S hS f g hg))
    (isFinite_pullback_snd B S hS (f ≫ g) g hfg)

/-! ### Quasi-finiteness -/

/-- A finite morphism of algebraic spaces over `S` is quasi-finite. -/
@[stacks 04NY]
theorem isQuasiFinite_of_isFinite (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsFinite B S hS f) :
    IsQuasiFinite B S hS f := by
  have hrel := ((isFinite_iff_representable B S hS f hX hY).1 hf).2
  have hqf : MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
        (BigFppfOver.toScheme B S hS) := by
    intro _ _ p hp
    have : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) := hp
    exact ⟨inferInstance, inferInstance⟩
  have hqc : MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
    intro _ _ p hp
    have : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) := hp
    exact (inferInstance : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map p))
  exact ⟨presheafImpliesHoldsOnEveryEtaleChart_locallyQuasiFinite B S hS f
      (MorphismProperty.relative_monotone hqf _ hrel),
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      (MorphismProperty.relative_monotone hqc _ hrel)⟩

/-! ### Finite coproducts -/

/-- Let `F i ⟶ Y`, for `i` in a finite index type, be finite morphisms of algebraic spaces over
`S`, and let `G` be their coproduct as a sheaf of sets on the big fppf site of `S`, given by a
colimit cofan. Then the induced morphism `G ⟶ Y` is finite. -/
@[stacks 0CZ2]
theorem isFinite_coproduct {I : Type v} [Finite I]
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i)) (hY : IsAlgebraicSpace B S hS Y)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (fᵢ : ∀ i, F i ⟶ Y) (f : G.obj ⟶ Y) (hf : ∀ i, (ι i).hom ≫ f = fᵢ i)
    (hfin : ∀ i, IsFinite B S hS (fᵢ i)) :
    IsFinite B S hS f := by
  classical
  have := AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  intro U hU ξ
  choose V p a hV hp hpb using fun i ↦ hfin i U hU ξ
  let T := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  let Fs : I → Sheaf J (Type u) := fun i ↦ ⟨F i, (hF i).isSheaf⟩
  let Ys : Sheaf J (Type u) := ⟨Y, hY.isSheaf⟩
  let W := BigFppfOver.sigmaObj B S hS V
  let d : W ⟶ U := Cofan.IsColimit.desc (BigFppfOver.isColimit_sigmaCofan B S hS V) p
  have hdfac : ∀ i, BigFppfOver.sigmaIncl B S hS V i ≫ d = p i := fun i ↦
    Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS V) p i
  have hdfacS : ∀ i, Sigma.ι (fun j ↦ T.obj (V j)) i ≫ T.map d = T.map (p i) := by
    intro i
    have h : T.map (BigFppfOver.sigmaIncl B S hS V i) ≫ T.map d = T.map (p i) := by
      rw [← Functor.map_comp, hdfac]
    exact (congrArg (· ≫ T.map d) (BigFppfOver.toScheme_map_sigmaIncl B S hS V i)).symm.trans h
  have hd : T.map d = Sigma.desc fun i ↦ T.map (p i) :=
    Sigma.hom_ext _ _ fun i ↦ (hdfacS i).trans (Sigma.ι_desc (fun j ↦ T.map (p j)) i).symm
  have : ∀ i, _root_.AlgebraicGeometry.IsFinite (T.map (p i)) := hp
  have hdfin : _root_.AlgebraicGeometry.IsFinite (T.map d) := by
    rw [hd]; exact isFinite_sigmaDesc
  have hWaff : IsAffine (T.obj W) := isAffine_of_isFinite (T.map d) hdfin hU
  have hcolim := BigFppfOver.isColimit_yoneda_sigmaCofan B S hS V
  let as : ∀ i, J.yoneda.obj (V i) ⟶ Fs i := fun i ↦ ⟨a i⟩
  let fs : ∀ i, Fs i ⟶ Ys := fun i ↦ ⟨fᵢ i⟩
  have hsq : ∀ i, IsPullback (as i) (J.yoneda.map (p i)) (fs i)
      (⟨ξ⟩ : J.yoneda.obj U ⟶ Ys) := fun i ↦ isPullback_sheaf_of_hom (hpb i)
  have hwhole := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    hG).isPullback_of_isColimit_right fs (⟨f⟩ : G ⟶ Ys) (⟨ξ⟩ : J.yoneda.obj U ⟶ Ys) as
    (fun i ↦ J.yoneda.map (p i)) hsq hcolim (fun i ↦ Sheaf.hom_ext (hf i))
  have hdesc : Cofan.IsColimit.desc hcolim (fun i ↦ J.yoneda.map (p i)) = J.yoneda.map d := by
    refine Cofan.IsColimit.hom_ext hcolim _ _ fun i ↦ ?_
    rw [Cofan.IsColimit.fac]
    simp only [Cofan.inj, Cofan.mk_ι_app]
    rw [← Functor.map_comp, hdfac]
  rw [hdesc] at hwhole
  exact ⟨W, d, (Cofan.IsColimit.desc hcolim fun i ↦ as i ≫ ι i).hom, hWaff, hdfin,
    hwhole.map (sheafToPresheaf J (Type u))⟩

end AlgebraicGeometry.Space

end
