module

public import StacksFrontier.AlgebraicGeometry.Gluing.IsoDescentCartesian
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverAtlasFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# The universal atlas of `ℋ_d` is limit preserving on objects

Let `B` be a big fppf site, `S` a scheme contained in it and `d` a positive natural number. The
1-morphism `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas` from the scheme of structure
constants over `S` into the category `ℋ_d` of degree-`d` finite locally free covers is **limit
preserving on objects** in the sense of **Stacks 06CU**. This is the limit-preservation input of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint`, the closing step of
Stacks 06DC, for the presentation of `ℋ_d` that the source's proof of **Stacks 05YQ** uses.

Nothing about the scheme of structure constants is needed beyond two facts: its structure
morphism to `S` is locally of finite presentation, and the universal cover over it is finite
locally free of degree `d`. So the statement is proved for an arbitrary scheme-valued point of
`ℋ_d`, that is for `AlgebraicGeometry.Stack.finiteCoverPointHom` of a degree-`d` cover
`c : W ⟶ U` of an object of the site whose structure morphism to `S` is locally of finite
presentation, and then specialised.

## The two halves of the descent

Limit preservation on objects asks, for a cofiltered limit `lim U_i` of affine objects of the
site, an object `T ⟶ U` of the slice at `U` with `T = lim U_i`, and a cartesian comparison of
the cover `W ×_U T ⟶ T` it cuts out with a degree-`d` cover `Z ⟶ U_i` at a stage, for the whole
package to come from a later stage. It splits in two.

* *The point descends.* A morphism out of the limit into `U` factors through a stage because `U`
  is locally of finite presentation over `S`. That is **Stacks 01ZC**, available at the level of
  schemes over a base as `AlgebraicGeometry.Scheme.exists_comp_eq_of_isLimitPreserving`; the
  passage to the site is `exists_stage_comp_eq_of_locallyOfFinitePresentation` below, which
  carries the diagram over by `CategoryTheory.Over.post` of the site's inclusion into schemes —
  fully faithful, so the factorisation comes back — and reads the limit cone in `Over S` off the
  one in schemes, `CategoryTheory.Over.forget` creating connected limits.
* *The comparison descends with it.* Once the point is defined at a stage, the cover it cuts out
  there and the given cover `Z ⟶ U_i` are two finitely presented objects over a stage whose base
  changes to the limit are identified; that identification descends by **Stacks 01ZM** part (2)
  and becomes an isomorphism at a later stage by **Stacks 081E**. Compatibility with the given
  comparison is the content of
  `AlgebraicGeometry.exists_stage_isPullback_of_isPullback_limit`.

Finiteness of the *source* of the atlas is therefore one of two ingredients, not the whole
statement: by itself it descends the point and says nothing about the comparison.

## Main results

* `AlgebraicGeometry.Stack.exists_stage_comp_eq_of_locallyOfFinitePresentation`: Stacks 01ZC at
  the big fppf site.
* `AlgebraicGeometry.Stack.exists_stage_finiteCoverPoint_comparison` and
  `AlgebraicGeometry.Stack.exists_stage_finiteCoverPoint_comparison_of_eq`: the spreading-out
  statement, on the nose and with the two base objects presented by equalities.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_finiteCoverPointHom`: a scheme-valued point
  of `ℋ_d` given by a degree-`d` cover of an object locally of finite presentation over `S` is
  limit preserving on objects.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_finiteCoverUniversalAtlas`: the universal
  atlas of `ℋ_d` is limit preserving on objects.

## Implementation notes

The index categories are those of the universe of the schemes, which is the size at which
Stacks 01ZC and Stacks 01ZM are available here and the size at which
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint` consumes the hypothesis.

The spreading-out statement is given twice because limit preservation on objects presents its
data with the base of the object of the slice and the base of the object of `ℋ_d` merely *equal*
to the apex of the cone and to the stage, and with the comparison lying over the leg of the cone
transported along those two equalities; that is
`CategoryTheory.Functor.IsHomLift.fac'`. The second form takes those equalities as hypotheses and
substitutes them away, so the first form can be stated without `eqToHom`.

The compatibility clause of the spreading-out statement is quantified over an arbitrary morphism
characterised by its two projections rather than stated for the gap map itself. That is what the
consumer holds: the cover component of the morphism of `ℋ_d` produced by
`AlgebraicGeometry.Stack.finiteCoverPointMap` is a gap map presented by
`AlgebraicGeometry.Stack.finiteCoverPointMap_g_comp_fst` and
`AlgebraicGeometry.Stack.finiteCoverPointMap_g_comp_snd`, and no equation identifying it with a
chosen lift is needed.

No `@[stacks]` attribute is placed here. Stacks 06CU is tagged on the definition of limit
preservation on objects; the statements below are instances of it for particular 1-morphisms, and
the source states them inside the proof of Stacks 05YQ rather than as tagged results.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

attribute [local instance] IsCofiltered.isConnected

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 01ZC at the big fppf site.** A morphism of the big fppf site of `S` out of a
cofiltered limit of affine objects into an object whose structure morphism to `S` is locally of
finite presentation factors through one of the stages. -/
theorem exists_stage_comp_eq_of_locallyOfFinitePresentation
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (cc : Cone D)
    (hcc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cc))
    (U : BigFppfOver B S hS)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (x : (BigAffineFppf.inclusion B S hS).obj cc.pt ⟶ U) :
    ∃ (i : I) (xi : (BigAffineFppf.inclusion B S hS).obj (D.obj i) ⟶ U),
      (BigAffineFppf.inclusion B S hS).map (cc.π.app i) ≫ xi = x := by
  classical
  have hUfp : LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom := hU
  have hpres : Scheme.IsLimitPreserving S (yoneda.obj ((Over.post B.inclusion).obj U)) :=
    Scheme.isLimitPreserving_yoneda_of_locallyOfFinitePresentation _
  have hD : ∀ i, IsAffine
      (((D ⋙ BigAffineFppf.inclusion B S hS ⋙ Over.post B.inclusion).obj i).left) :=
    fun i => (D.obj i).property
  have hc₀ : IsLimit ((Over.forget S).mapCone
      ((Over.post B.inclusion).mapCone ((BigAffineFppf.inclusion B S hS).mapCone cc))) := hcc
  obtain ⟨i, gi, hgi⟩ := Scheme.exists_comp_eq_of_isLimitPreserving hpres
    (D ⋙ BigAffineFppf.inclusion B S hS ⋙ Over.post B.inclusion)
    ((Over.post B.inclusion).mapCone ((BigAffineFppf.inclusion B S hS).mapCone cc))
    (isLimitOfReflects (Over.forget S) hc₀) hD ((Over.post B.inclusion).map x)
  exact ⟨i, (Over.post B.inclusion).preimage gi,
    (Over.post B.inclusion).map_injective (by rwa [Functor.map_comp, Functor.map_preimage])⟩

/-- A finite locally free morphism of fixed degree is of finite presentation. -/
private theorem finitePresentation_of_isFiniteLocallyFreeOfRank {Xs Ys : Scheme.{u}}
    (f : Xs ⟶ Ys) (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] :
    FinitePresentation f := by
  obtain ⟨hfin, -, hlfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d)
  have := hfin
  exact ⟨hlfp, inferInstance, inferInstance⟩

/-- For `c : W ⟶ U` and `f : X ⟶ Y` over `U`, the gap map `W ×_U X ⟶ W ×_U Y` induced by `f`
exists and makes a cartesian square over `f`. -/
private theorem exists_pullback_map_isPullback {C : Type*} [Category C] [HasPullbacks C]
    {W U X Y : C} (c : W ⟶ U) {x : X ⟶ U} {t : Y ⟶ U} (f : X ⟶ Y) (hf : f ≫ t = x) :
    ∃ g : pullback c x ⟶ pullback c t,
      g ≫ pullback.fst c t = pullback.fst c x ∧
        g ≫ pullback.snd c t = pullback.snd c x ≫ f ∧
        IsPullback g (pullback.snd c x) (pullback.snd c t) f := by
  have hw : pullback.fst c x ≫ c = (pullback.snd c x ≫ f) ≫ t := by
    rw [Category.assoc, hf]
    exact pullback.condition
  exact ⟨(IsPullback.of_hasPullback c t).lift _ _ hw,
    (IsPullback.of_hasPullback c t).lift_fst _ _ hw,
    (IsPullback.of_hasPullback c t).lift_snd _ _ hw, isPullback_liftPullbackSnd c f t x hf hw⟩

/-- A morphism of schemes between objects of the big fppf site of `S` which commutes with their
structure morphisms is the image of a morphism of the site. -/
private theorem exists_toScheme_map_eq_of_comp_hom {X Y : BigFppfOver B S hS}
    (h₀ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hh₀ : h₀ ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom) :
    ∃ hs : X ⟶ Y, (BigFppfOver.toScheme B S hS).map hs = h₀ :=
  ⟨Over.homMk (B.inclusion.preimage h₀)
    (B.inclusion.map_injective (by rwa [Functor.map_comp, Functor.map_preimage])),
    B.inclusion.map_preimage h₀⟩

/-- **A degree-`d` cover of a cofiltered limit of affine objects which is cut out by a point of
the slice at `U`, together with a cartesian comparison to a cover at a stage, descends.**

Let `cmap : W ⟶ U` be a degree-`d` finite locally free cover of an object of the big fppf site
whose structure morphism to `S` is locally of finite presentation, let `qy : Zy ⟶ D.obj i` be a
degree-`d` cover at a stage, let `xh` be a point of the slice at `U` over the limit, and let
`glim` present the base change `W ×_U lim` of `cmap` along `xh` as the base change of `qy` along
the leg of the cone. Then at some stage `i'` over `i` the point `xh` is the restriction of a
point `xh'`, and the base change of `cmap` along `xh'` is presented as the base change of `qy`
along the transition, compatibly with `glim`.

This is the spreading-out content of limit preservation on objects of
`AlgebraicGeometry.Stack.finiteCoverPointHom`: the point descends by Stacks 01ZC, and the
comparison descends with it by
`AlgebraicGeometry.exists_stage_isPullback_of_isPullback_limit`. The compatibility is stated
through an arbitrary morphism `k` characterised by its two projections, which is how the morphism
of `ℋ_d` produced by `AlgebraicGeometry.Stack.finiteCoverPointMap` presents the gap map. -/
theorem exists_stage_finiteCoverPoint_comparison
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (cc : Cone D)
    (hcc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cc))
    {d : ℕ} {W U : BigFppfOver B S hS} (cmap : W ⟶ U)
    (hcf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map cmap) d)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (i : I) {Zy : BigFppfOver B S hS}
    (qy : Zy ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i))
    (hqy : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map qy) d)
    (xh : (BigAffineFppf.inclusion B S hS).obj cc.pt ⟶ U)
    (glim : pullback cmap xh ⟶ Zy)
    (hglim : IsPullback glim (pullback.snd cmap xh) qy
      ((BigAffineFppf.inclusion B S hS).map (cc.π.app i))) :
    ∃ (i' : I) (j : i' ⟶ i) (xh' : (BigAffineFppf.inclusion B S hS).obj (D.obj i') ⟶ U),
      (BigAffineFppf.inclusion B S hS).map (cc.π.app i') ≫ xh' = xh ∧
        ∃ h : pullback cmap xh' ⟶ Zy,
          IsPullback h (pullback.snd cmap xh') qy
              ((BigAffineFppf.inclusion B S hS).map (D.map j)) ∧
            ∀ k : pullback cmap xh ⟶ pullback cmap xh',
              k ≫ pullback.fst cmap xh' = pullback.fst cmap xh →
              k ≫ pullback.snd cmap xh'
                = pullback.snd cmap xh ≫
                  (BigAffineFppf.inclusion B S hS).map (cc.π.app i') →
              k ≫ h = glim := by
  classical
  have : EssentiallySmall.{u} I := inferInstance
  have := hcf
  have := hqy
  have hDaff : ∀ a : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj a) :=
    fun a => (D.obj a).property
  have : ∀ a : I, CompactSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj a) :=
    fun _ => inferInstance
  have : ∀ a : I, QuasiSeparatedSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj a) :=
    fun _ => inferInstance
  have : ∀ {a b : I} (ee : a ⟶ b),
      IsAffineHom ((D ⋙ BigAffineFppf.toScheme B S hS).map ee) := fun _ => inferInstance
  -- Stacks 01ZC: the point descends to a stage, which cofilteredness moves over `i`.
  obtain ⟨i₀, xh₀, hxh₀⟩ :=
    exists_stage_comp_eq_of_locallyOfFinitePresentation B S hS D cc hcc U hU xh
  obtain ⟨i₁, aa, j₁, -⟩ := IsCofilteredOrEmpty.cone_objs i₀ i
  obtain ⟨xh₁, hxh₁⟩ : ∃ t : (BigAffineFppf.inclusion B S hS).obj (D.obj i₁) ⟶ U,
      (BigAffineFppf.inclusion B S hS).map (cc.π.app i₁) ≫ t = xh :=
    ⟨(BigAffineFppf.inclusion B S hS).map (D.map aa) ≫ xh₀, by
      rwa [← Category.assoc, ← Functor.map_comp, cc.w aa]⟩
  -- The cover of the limit is the base change of the cover at the stage `i₁`.
  obtain ⟨gap₁, hg1fst, hg1snd, hg1sq⟩ := exists_pullback_map_isPullback cmap _ hxh₁
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (pullback.snd cmap xh₁)) d :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      ((IsPullback.of_hasPullback cmap xh₁).map (BigFppfOver.toScheme B S hS))
  -- Push the two squares to schemes and descend the comparison there.
  have hPsch : IsPullback ((BigFppfOver.toScheme B S hS).map gap₁)
      ((BigFppfOver.toScheme B S hS).map (pullback.snd cmap xh))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd cmap xh₁))
      (((BigAffineFppf.toScheme B S hS).mapCone cc).π.app i₁) :=
    hg1sq.map (BigFppfOver.toScheme B S hS)
  have hgsch : IsPullback ((BigFppfOver.toScheme B S hS).map glim)
      ((BigFppfOver.toScheme B S hS).map (pullback.snd cmap xh))
      ((BigFppfOver.toScheme B S hS).map qy)
      (((BigAffineFppf.toScheme B S hS).mapCone cc).π.app i₁ ≫
        (D ⋙ BigAffineFppf.toScheme B S hS).map j₁) := by
    have h := hglim.map (BigFppfOver.toScheme B S hS)
    rwa [((BigAffineFppf.toScheme B S hS).mapCone cc).w j₁]
  obtain ⟨i₂, e, hstage⟩ := exists_stage_isPullback_of_isPullback_limit
    (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone cc) hcc
    i₁ i j₁ ((BigFppfOver.toScheme B S hS).map (pullback.snd cmap xh₁))
    ((BigFppfOver.toScheme B S hS).map qy)
    (finitePresentation_of_isFiniteLocallyFreeOfRank _ d)
    (finitePresentation_of_isFiniteLocallyFreeOfRank _ d) hPsch hgsch
  -- The point at the final stage, and the two cartesian squares it sits in.
  obtain ⟨xh', hxh'e, hxh'fac⟩ :
      ∃ t : (BigAffineFppf.inclusion B S hS).obj (D.obj i₂) ⟶ U,
        (BigAffineFppf.inclusion B S hS).map (D.map e) ≫ xh₁ = t ∧
          (BigAffineFppf.inclusion B S hS).map (cc.π.app i₂) ≫ t = xh :=
    ⟨_, rfl, by rwa [← Category.assoc, ← Functor.map_comp, cc.w e]⟩
  obtain ⟨b₂, hb2fst, hb2snd, hb2sq⟩ := exists_pullback_map_isPullback cmap _ hxh'e
  obtain ⟨gap₂, hg2fst, hg2snd, -⟩ := exists_pullback_map_isPullback cmap _ hxh'fac
  have hgap : gap₂ ≫ b₂ = gap₁ := by
    refine (IsPullback.of_hasPullback cmap xh₁).hom_ext ?_ ?_
    · rw [Category.assoc, hb2fst, hg2fst, hg1fst]
    · rw [Category.assoc, hb2snd, ← Category.assoc, hg2snd, hg1snd, Category.assoc,
        ← Functor.map_comp, cc.w e]
  -- Transport the descended comparison back into the site.
  obtain ⟨h₀, hh0sq, hh0comp⟩ := hstage
    (b := (BigFppfOver.toScheme B S hS).map b₂)
    (p₂ := (BigFppfOver.toScheme B S hS).map (pullback.snd cmap xh'))
    (hb2sq.map (BigFppfOver.toScheme B S hS))
    (k := (BigFppfOver.toScheme B S hS).map gap₂)
    (by rw [← Functor.map_comp, hgap])
    (by
      rw [← Functor.map_comp, hg2snd, Functor.map_comp]
      rfl)
  have hstr : ∀ {a b : I}, (f : a ⟶ b) →
      (D ⋙ BigAffineFppf.toScheme B S hS).map f ≫
        B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj (D.obj b)).hom
        = B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj (D.obj a)).hom :=
    fun f => BigFppfOver.toScheme_map_comp_hom ((BigAffineFppf.inclusion B S hS).map (D.map f))
  obtain ⟨hsite, hsitemap⟩ := exists_toScheme_map_eq_of_comp_hom B S hS h₀ <| by
    rw [← BigFppfOver.toScheme_map_comp_hom qy, ← Category.assoc, hh0sq.w]
    simp only [Category.assoc]
    rw [hstr, hstr, BigFppfOver.toScheme_map_comp_hom]
  refine ⟨i₂, e ≫ j₁, xh', hxh'fac, hsite,
    IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_, fun k hkfst hksnd => ?_⟩
  · have hDcomp : (D ⋙ BigAffineFppf.toScheme B S hS).map e ≫
        (D ⋙ BigAffineFppf.toScheme B S hS).map j₁
        = (BigFppfOver.toScheme B S hS).map
          ((BigAffineFppf.inclusion B S hS).map (D.map (e ≫ j₁))) :=
      ((D ⋙ BigAffineFppf.toScheme B S hS).map_comp e j₁).symm
    rwa [hsitemap, ← hDcomp]
  · obtain rfl : k = gap₂ := (IsPullback.of_hasPullback cmap xh').hom_ext
      (hkfst.trans hg2fst.symm) (hksnd.trans hg2snd.symm)
    exact (BigFppfOver.toScheme B S hS).map_injective (by rwa [Functor.map_comp, hsitemap])

/-- `AlgebraicGeometry.Stack.exists_stage_finiteCoverPoint_comparison` with the base objects of
the point and of the cover at the stage presented by equalities rather than on the nose.

This is the shape in which limit preservation on objects presents its data: the base of the
object of the slice and the base of the object of `ℋ_d` are equal to the apex of the cone and to
the stage, and the comparison lies over the leg of the cone transported along those two
equalities, which is `CategoryTheory.Functor.IsHomLift.fac'`. -/
theorem exists_stage_finiteCoverPoint_comparison_of_eq
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (cc : Cone D)
    (hcc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cc))
    {d : ℕ} {W U : BigFppfOver B S hS} (cmap : W ⟶ U)
    (hcf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map cmap) d)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (i : I) {Xl Yu Zy : BigFppfOver B S hS}
    (ex : Xl = (BigAffineFppf.inclusion B S hS).obj cc.pt)
    (ey : Yu = (BigAffineFppf.inclusion B S hS).obj (D.obj i))
    (qy : Zy ⟶ Yu)
    (hqy : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map qy) d)
    (xh : Xl ⟶ U) (glim : pullback cmap xh ⟶ Zy)
    (hglim : IsPullback glim (pullback.snd cmap xh) qy
      (eqToHom ex ≫ (BigAffineFppf.inclusion B S hS).map (cc.π.app i) ≫ eqToHom ey.symm)) :
    ∃ (i' : I) (j : i' ⟶ i) (xh' : (BigAffineFppf.inclusion B S hS).obj (D.obj i') ⟶ U),
      eqToHom ex ≫ (BigAffineFppf.inclusion B S hS).map (cc.π.app i') ≫ xh' = xh ∧
        ∃ h : pullback cmap xh' ⟶ Zy,
          IsPullback h (pullback.snd cmap xh') qy
              ((BigAffineFppf.inclusion B S hS).map (D.map j) ≫ eqToHom ey.symm) ∧
            ∀ k : pullback cmap xh ⟶ pullback cmap xh',
              k ≫ pullback.fst cmap xh' = pullback.fst cmap xh →
              k ≫ pullback.snd cmap xh' = pullback.snd cmap xh ≫
                (eqToHom ex ≫ (BigAffineFppf.inclusion B S hS).map (cc.π.app i')) →
              k ≫ h = glim := by
  subst ex
  subst ey
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hglim ⊢
  exact exists_stage_finiteCoverPoint_comparison B S hS D cc hcc cmap hcf hU i qy hqy xh glim
    hglim

/-- **A scheme-valued point of `ℋ_d` given by a degree-`d` cover of an object locally of finite
presentation over `S` is limit preserving on objects.**

The 1-morphism is `AlgebraicGeometry.Stack.finiteCoverPointHom`, which sends an object `T ⟶ U`
of the slice of the site at `U` to the base change `W ×_U T ⟶ T` of the given cover. Limit
preservation on objects (**Stacks 06CU**) asks for an object of the slice over a cofiltered
limit of affine objects, together with a cartesian comparison of the cover it cuts out with a
cover at a stage, to come from a later stage; that is
`AlgebraicGeometry.Stack.exists_stage_finiteCoverPoint_comparison`, whose two inputs are
Stacks 01ZC for the point and Stacks 01ZM together with Stacks 081E for the comparison. -/
theorem isLimitPreservingOnObjects_finiteCoverPointHom
    {d : ℕ} {W U : BigFppfOver B S hS} (cmap : W ⟶ U)
    (hcf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map cmap) d)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom)) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS U) (finiteCoverFibered B S hS d)
      (finiteCoverPointHom cmap hcf) := by
  intro I _ _ D cc hcc i y x γ hγ
  have hdom : x.1.left = (BigAffineFppf.inclusion B S hS).obj cc.pt := x.2
  have hcod : y.1.U = (BigAffineFppf.inclusion B S hS).obj (D.obj i) := y.2
  have : (finiteCoverFibered B S hS d).val.p.IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (cc.π.app i)) γ := hγ.toIsHomLift
  have hf : γ.f = eqToHom hdom ≫
      (BigAffineFppf.inclusion B S hS).map (cc.π.app i) ≫ eqToHom hcod.symm :=
    IsHomLift.fac' (finiteCoverFibered B S hS d).val.p
      ((BigAffineFppf.inclusion B S hS).map (cc.π.app i)) γ
  obtain ⟨i', j, xh', hfac, h, hsq, hcompat⟩ :=
    exists_stage_finiteCoverPoint_comparison_of_eq B S hS D cc hcc cmap hcf hU i hdom hcod
      y.1.q y.1.finiteLocallyFree x.1.hom γ.g (hf ▸ γ.square)
  have hδw : (eqToHom hdom ≫
      (BigAffineFppf.inclusion B S hS).map (cc.π.app i')) ≫ xh' = x.1.hom := by
    rwa [Category.assoc]
  obtain ⟨δ, hδleft⟩ : ∃ dd : x.1 ⟶ (Over.mk xh' : Over U),
      dd.left = eqToHom hdom ≫ (BigAffineFppf.inclusion B S hS).map (cc.π.app i') :=
    ⟨Over.homMk _ hδw, rfl⟩
  obtain ⟨γ', hγ'f, hγ'g⟩ :
      ∃ gg : (finiteCoverPointFunctor cmap hcf).obj (Over.mk xh') ⟶ y.1,
        gg.f = (BigAffineFppf.inclusion B S hS).map (D.map j) ≫ eqToHom hcod.symm ∧ gg.g = h :=
    ⟨{ f := (BigAffineFppf.inclusion B S hS).map (D.map j) ≫ eqToHom hcod.symm
       g := h
       square := hsq }, rfl, rfl⟩
  have hδlift : (schemeFibredCategory B S hS U).val.p.IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (cc.π.app i')) δ := by
    refine IsHomLift.of_fac' _ _ _ hdom rfl ?_
    show δ.left = _
    rw [hδleft]
    rfl
  have hγ'lift : (finiteCoverFibered B S hS d).val.p.IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (D.map j)) γ' := by
    refine IsHomLift.of_fac' _ _ _ rfl hcod ?_
    show γ'.f = _
    rw [hγ'f]
    rfl
  refine ⟨i', j, ⟨Over.mk xh', rfl⟩, x, δ, 𝟙 x.1, γ',
    (schemeFibredCategory B S hS U).isFiberedInGroupoids.isStronglyCartesian_homLift _ δ,
    IsHomLift.id hdom, inferInstance,
    (finiteCoverFibered B S hS d).isFiberedInGroupoids.isStronglyCartesian_homLift _ γ', ?_⟩
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  refine FiniteCover.Hom.ext ?_ ?_
  · have hcone : (BigAffineFppf.inclusion B S hS).map (cc.π.app i') ≫
        (BigAffineFppf.inclusion B S hS).map (D.map j)
        = (BigAffineFppf.inclusion B S hS).map (cc.π.app i) := by
      rw [← CategoryTheory.Functor.map_comp, cc.w j]
    show δ.left ≫ γ'.f = γ.f
    rw [hδleft, hγ'f, hf, Category.assoc,
      ← Category.assoc ((BigAffineFppf.inclusion B S hS).map (cc.π.app i')), hcone]
  · show (finiteCoverPointMap cmap hcf δ).g ≫ γ'.g = γ.g
    rw [hγ'g]
    have h2 := finiteCoverPointMap_g_comp_snd cmap hcf δ
    rw [hδleft] at h2
    exact hcompat _ (finiteCoverPointMap_g_comp_fst cmap hcf δ) h2

/-- **The universal atlas of `ℋ_d` is limit preserving on objects.**

The 1-morphism `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas` out of the scheme of
structure constants over `S` is the base change of the universal degree-`d` cover, and the scheme
of structure constants over `S` is locally of finite presentation over `S` by
`AlgebraicGeometry.Stack.locallyOfFinitePresentation_structureConstantsBaseChangeSnd`, so
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_finiteCoverPointHom` applies.

This is the limit-preservation input of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint`, the closing step of
**Stacks 06DC**, for the presentation of `ℋ_d` that the source's proof of **Stacks 05YQ**
uses. -/
theorem isLimitPreservingOnObjects_finiteCoverUniversalAtlas (d : ℕ) [NeZero d] :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS (structureConstantsOver B S hS d))
      (finiteCoverFibered B S hS d)
      (finiteCoverUniversalAtlas B S hS d) :=
  isLimitPreservingOnObjects_finiteCoverPointHom B S hS
    (universalFiniteCoverMapOver B S hS d)
    (isFiniteLocallyFreeOfRank_universalFiniteCoverMapOver B S hS d)
    (locallyOfFinitePresentation_structureConstantsBaseChangeSnd S d)

end AlgebraicGeometry.Stack

end
