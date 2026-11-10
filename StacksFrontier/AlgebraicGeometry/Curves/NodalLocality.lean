module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ZariskiToEtale
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Syntomic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Unramified
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalDescentAlongLimit
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings

/-!
# Locality of at-worst-nodal families of relative dimension one

A morphism of schemes which is at-worst-nodal of relative dimension one stays so after an
arbitrary base change and after composition with an étale morphism of the base, a morphism is
at-worst-nodal of relative dimension one as soon as its base changes along the members of an
fpqc covering of its target are, and it is at-worst-nodal of relative dimension one as soon as
its restrictions to the members of an étale covering of its source are. Taken together these
make the property étale local on the source and target in the sense of Tag 04QZ.

## Main results

* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange`:
  **Stacks 0C5B.**
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isLocalAtTarget_fpqc`:
  **Stacks 0C5E.**
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_comp_etale_base`:
  **Stacks 0CD8.**
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isLocalAtSource_etale`:
  **Stacks 0C5D.**
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget`:
  **Stacks 04QZ** for this property, obtained from the three preceding statements.
* `AlgebraicGeometry.isPullback_subschemeι_comp`: in a cartesian square, the structure morphism
  of the inverse image of a closed subscheme is a base change of the structure morphism of that
  closed subscheme.

## Implementation notes

Both halves of the at-worst-nodal condition are treated separately throughout. Syntomicity of
relative dimension one is stable under base change, fpqc local on the target and étale local on
the source, and the relative singular subscheme is the inverse image of the relative singular
subscheme under base change (`AlgebraicGeometry.fittingIdeal_relativeDifferentials_comap` at
index one) and under étale precomposition
(`AlgebraicGeometry.relativeSingularIdeal_comap_etale`), so the inclusion of the relative
singular subscheme followed by the morphism is a base change in the first case and admits an
étale covering by such inclusions in the second. The remaining condition on it is
unramifiedness, which is stable under base change, fpqc local on the target and étale local on
the source.

For an étale morphism of the base the relative singular subscheme does not change at all: the
canonical map `Ω_{X/S} ⟶ Ω_{X/S'}` is an isomorphism, so the two first Fitting ideals agree.
The relative dimension is unchanged because a flat composition adds fibre dimensions
(Tag 02JS) and an étale morphism has fibres of local dimension zero.

## References

* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 0C5B](https://stacks.math.columbia.edu/tag/0C5B)
* [Stacks Project, Tag 0C5D](https://stacks.math.columbia.edu/tag/0C5D)
* [Stacks Project, Tag 0C5E](https://stacks.math.columbia.edu/tag/0C5E)
* [Stacks Project, Tag 0CD8](https://stacks.math.columbia.edu/tag/0CD8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- In a cartesian square with right edge `f` and base edge `g`, the inclusion of the
inverse-image closed subscheme followed by the base change of `f` is a base change of the
inclusion of the closed subscheme followed by `f`. -/
public theorem isPullback_subschemeι_comp {X' X S' S : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    (I : X.IdealSheafData) :
    IsPullback ((I.comapIso g').hom ≫ pullback.snd g' I.subschemeι)
      ((I.comap g').subschemeι ≫ f') (I.subschemeι ≫ f) g := by
  simpa only [Category.assoc] using
    (IsPullback.of_iso_pullback
      (CommSq.mk (by simp only [← I.comapIso_hom_fst, Category.assoc,
        pullback.condition])) (I.comapIso g') (I.comapIso_hom_fst g') rfl).flip.paste_vert h

/-- **Stacks 0C5B.** A base change of a morphism which is at-worst-nodal of relative dimension
one is again at-worst-nodal of relative dimension one. -/
@[stacks 0C5B]
public instance isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) := by
  constructor
  intro T₁ T₂ T₃ T₄ p q a b sq hq
  have hlfp : LocallyOfFinitePresentation q := locallyOfFinitePresentation hq.1.1
  refine ⟨(syntomicOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq hq.1, ?_⟩
  have hI : (relativeSingularIdeal q).comap a = relativeSingularIdeal b :=
    fittingIdeal_relativeDifferentials_comap a b q p sq 1
  rw [← hI]
  exact MorphismProperty.of_isPullback
    (isPullback_subschemeι_comp a b q p sq (relativeSingularIdeal q)) hq.2

/-- **Stacks 0C5E.** Being at-worst-nodal of relative dimension one is fpqc local on the
target: a morphism has the property exactly when all of its base changes along the members of
an fpqc covering of its target do. -/
@[stacks 0C5E]
public instance isAtWorstNodalOfRelativeDimensionOne_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have : MorphismProperty.RespectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHypercover ?_
  intro X S f 𝒰
  constructor
  · intro hf i
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (𝒰.f i)) hf
  · intro hi
    have hsyn : Syntomic f :=
      MorphismProperty.IsLocalAtTarget.of_zeroHypercover
        (P := @Syntomic.{u}) 𝒰 (fun i => (hi i).1.1)
    have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hsyn
    have hdim : ∀ x : X,
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (1 : WithBot ℕ∞) := by
      intro x
      obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff
        𝒰.toPreZeroHypercover).mp
        (Scheme.propQCPrecoverage_le_precoverage (P := @Flat.{u}) S 𝒰.mem₀)).1 (f x)
      obtain ⟨z, hzX, _⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := f) (g := 𝒰.f i) x y hy.symm
      rw [← hzX]
      exact (topologicalKrullDimAt_fiber_eq_of_isPullback
        (IsPullback.of_hasPullback f (𝒰.f i)) z).symm.trans ((hi i).1.2 z)
    refine ⟨⟨hsyn, hdim⟩, ?_⟩
    apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := @Unramified.{u}) 𝒰
    intro i
    have : MorphismProperty.RespectsIso (@Unramified.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hsq := IsPullback.of_hasPullback f (𝒰.f i)
    have hsing := isPullback_subschemeι_comp (pullback.fst f (𝒰.f i))
      (pullback.snd f (𝒰.f i)) f (𝒰.f i) hsq (relativeSingularIdeal f)
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @Unramified.{u}) hsing.isoPullback.hom _).mp
    have hIJ : (relativeSingularIdeal f).comap (pullback.fst f (𝒰.f i)) =
        relativeSingularIdeal (pullback.snd f (𝒰.f i)) :=
      fittingIdeal_relativeDifferentials_comap (pullback.fst f (𝒰.f i))
        (pullback.snd f (𝒰.f i)) f (𝒰.f i) hsq 1
    rw [hsing.isoPullback_hom_snd, hIJ]
    exact (hi i).2

/-! ### Composition with an étale morphism of the base -/

/-- The fibres of an étale morphism have local dimension zero at every point: an étale morphism
is locally quasi-finite, and local quasi-finiteness at a point is exactly the vanishing of the
local dimension of the fibre there. -/
private theorem topologicalKrullDimAt_fiber_eq_zero_of_etale {Y S : Scheme.{u}} (g : Y ⟶ S)
    [Etale g] (y : Y) :
    topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y) = 0 := by
  have hqf := locallyQuasiFinite_of_etale g
  have : LocallyOfFiniteType g := hqf.1
  exact (quasiFiniteAt_iff_fiberDimensionAt_eq_zero g y).mp
    ((forall_quasiFiniteAt_iff g).mpr hqf y)

/-- **An étale morphism of the base does not change the relative singular subscheme.** For `g`
étale the canonical map `Ω_{X/S} ⟶ Ω_{X/S'}` is an isomorphism, so the two first Fitting ideals
agree. -/
public theorem relativeSingularIdeal_comp_etale_base {X S' S : Scheme.{u}} (f : X ⟶ S')
    (g : S' ⟶ S) [Etale g] [LocallyOfFiniteType f] :
    relativeSingularIdeal (f ≫ g) = relativeSingularIdeal f := by
  have hlfpg : LocallyOfFinitePresentation g := locallyOfFinitePresentation_of_etale g
  have hiso : IsIso (Scheme.Hom.toRelativeDifferentials f g) :=
    Scheme.Hom.isIso_toRelativeDifferentials_of_etale f g
  change fittingIdeal (Scheme.Hom.relativeDifferentials (f ≫ g)) 1 =
    fittingIdeal (Scheme.Hom.relativeDifferentials f) 1
  exact fittingIdeal_congr (asIso (Scheme.Hom.toRelativeDifferentials f g)) 1

/-- **Stacks 0CD8.** Composing a morphism which is at-worst-nodal of relative dimension one
with an étale morphism of the base again gives a morphism which is at-worst-nodal of relative
dimension one. -/
@[stacks 0CD8]
public theorem isAtWorstNodalOfRelativeDimensionOne_comp_etale_base {X S' S : Scheme.{u}}
    (f : X ⟶ S') (g : S' ⟶ S) [Etale g] (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    IsAtWorstNodalOfRelativeDimensionOne (f ≫ g) := by
  have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have hflatf : Flat f := flat hf.1.1
  have hlfpg : LocallyOfFinitePresentation g := locallyOfFinitePresentation_of_etale g
  refine ⟨⟨MorphismProperty.comp_mem _ f g hf.1.1 (syntomic_of_etale g), fun x => ?_⟩, ?_⟩
  · rw [topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt f g x (Flat.stalkMap f x),
      topologicalKrullDimAt_fiber_eq_zero_of_etale g (f x), hf.1.2 x, add_zero]
  · rw [relativeSingularIdeal_comp_etale_base f g, ← Category.assoc]
    exact MorphismProperty.comp_mem _ _ g hf.2 (unramified_of_etale g)

/-- Postcomposition with an étale morphism preserves being at-worst-nodal of relative
dimension one. -/
public instance isAtWorstNodalOfRelativeDimensionOne_respectsRight_etale :
    MorphismProperty.RespectsRight
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf :=
    have : Etale i := hi
    isAtWorstNodalOfRelativeDimensionOne_comp_etale_base f i hf

/-- Postcomposition with an open immersion preserves being at-worst-nodal of relative
dimension one, an open immersion being étale. -/
public instance isAtWorstNodalOfRelativeDimensionOne_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
  respectsRight_isOpenImmersion_of_etale_postcomp _ fun f g hf hg =>
    have : Etale g := hg
    isAtWorstNodalOfRelativeDimensionOne_comp_etale_base f g hf

/-! ### Étale locality on the source -/

/-- The inclusion of the inverse image of a closed subscheme along `g`, followed by `g` and a
morphism `f` out of the target of `g`, factors as the base change of `g` along the inclusion of
the closed subscheme, followed by that inclusion and `f`. -/
private theorem subschemeι_comap_comp {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (I : X.IdealSheafData) :
    ((I.comapIso g).hom ≫ pullback.snd g I.subschemeι) ≫ (I.subschemeι ≫ f) =
      (I.comap g).subschemeι ≫ (g ≫ f) := by
  simp only [← I.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]

/-- Precomposition with an étale morphism does not change the local dimension of a fibre: the
induced morphism of fibres is a base change of the étale morphism, hence étale, and an étale
morphism preserves the local dimension of a point. -/
theorem topologicalKrullDimAt_fiber_comp_etale {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ X) [Etale g] (y : Y) :
    topologicalKrullDimAt ((g ≫ f).fiber ((g ≫ f) y)) ((g ≫ f).asFiber y) =
      topologicalKrullDimAt (f.fiber (f (g y))) (f.asFiber (g y)) := by
  have : Etale (fiberMapOfComp g f ((g ≫ f) y)) :=
    MorphismProperty.of_isPullback (isPullback_fiberMapOfComp g f ((g ≫ f) y)).flip inferInstance
  rw [topologicalKrullDimAt_eq_of_etale (fiberMapOfComp g f ((g ≫ f) y)) ((g ≫ f).asFiber y),
    fiberMapOfComp_asFiber g f y]
  rfl

/-- Unramifiedness over the base of the relative singular subscheme is étale local on the
source: the relative singular subscheme of the restriction of `f` to a member of an étale
covering of its source is the inverse image of the relative singular subscheme of `f`, and the
resulting maps form an étale covering of the latter. -/
private theorem unramified_relativeSingular_of_etale_cover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {ι : Type*} (U : ι → Scheme.{u}) (g : ∀ i, U i ⟶ X)
    (hg : ∀ i, Etale (g i)) (hcov : ∀ x : X, ∃ (i : ι) (y : U i), g i y = x)
    (h : ∀ i, Unramified ((relativeSingularIdeal (g i ≫ f)).subschemeι ≫ (g i ≫ f))) :
    Unramified ((relativeSingularIdeal f).subschemeι ≫ f) := by
  let φ (i : ι) := ((relativeSingularIdeal f).comapIso (g i)).hom ≫
    pullback.snd (g i) (relativeSingularIdeal f).subschemeι
  have hmap : ∀ i, Etale (φ i) := fun i => have := hg i; inferInstanceAs (Etale (_ ≫ _))
  have hcovers : ∀ z : (relativeSingularIdeal f).subscheme, ∃ (i : ι)
      (w : ((relativeSingularIdeal f).comap (g i)).subscheme), φ i w = z := by
    intro z
    obtain ⟨i, y, hy⟩ := hcov ((relativeSingularIdeal f).subschemeι z)
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := g i) (g := (relativeSingularIdeal f).subschemeι) y z hy
    refine ⟨i, ((relativeSingularIdeal f).comapIso (g i)).inv w, ?_⟩
    have hinv : ((relativeSingularIdeal f).comapIso (g i)).hom
        (((relativeSingularIdeal f).comapIso (g i)).inv w) = w := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      simp
    rw [Scheme.Hom.comp_apply, hinv, hw]
  let 𝒱 : (relativeSingularIdeal f).subscheme.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers ι (fun i => ((relativeSingularIdeal f).comap (g i)).subscheme) φ
      hcovers hmap
  refine MorphismProperty.IsLocalAtSource.of_zeroHypercover (P := @Unramified.{u}) 𝒱 fun i => ?_
  have := hg i
  change Unramified (φ i ≫ ((relativeSingularIdeal f).subschemeι ≫ f))
  rw [subschemeι_comap_comp f (g i) (relativeSingularIdeal f),
    relativeSingularIdeal_comap_etale f (g i)]
  exact h i

/-- **Stacks 0C5D.** Being at-worst-nodal of relative dimension one is étale local on the
source: a morphism has the property exactly when all of its restrictions to the members of an
étale covering of its source do. -/
@[stacks 0C5D]
public instance isAtWorstNodalOfRelativeDimensionOne_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage := by
  have : MorphismProperty.RespectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover ?_
  intro X S f 𝒰
  obtain ⟨hcov, hetale⟩ :=
    (Scheme.presieve₀_mem_precoverage_iff (P := @Etale.{u}) 𝒰.toPreZeroHypercover).mp 𝒰.mem₀
  refine ⟨fun hf i => ?_, fun hi => ?_⟩
  · have : Etale (𝒰.f i) := hetale i
    exact isAtWorstNodalOfRelativeDimensionOne_comp_etale f (𝒰.f i) hf
  · have hsyn : Syntomic f :=
      MorphismProperty.IsLocalAtSource.of_zeroHypercover
        (P := @Syntomic.{u}) 𝒰 (fun i => (hi i).1.1)
    have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hsyn
    refine ⟨⟨hsyn, fun x => ?_⟩, ?_⟩
    · obtain ⟨i, y, rfl⟩ := hcov x
      have : Etale (𝒰.f i) := hetale i
      rw [← topologicalKrullDimAt_fiber_comp_etale f (𝒰.f i) y]
      exact (hi i).1.2 y
    · exact unramified_relativeSingular_of_etale_cover f 𝒰.X 𝒰.f hetale hcov fun i => (hi i).2

/-- Being at-worst-nodal of relative dimension one is étale local on the target, the étale
coverings being fpqc coverings. -/
public instance isAtWorstNodalOfRelativeDimensionOne_isLocalAtTarget_etale :
    MorphismProperty.IsLocalAtTarget
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.etalePrecoverage_le_fpqcPrecoverage

/-- Being at-worst-nodal of relative dimension one is Zariski local on the target, an open
covering being an fpqc covering. -/
public instance isAtWorstNodalOfRelativeDimensionOne_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsAtWorstNodalOfRelativeDimensionOne.{u}) :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage

/-- Being at-worst-nodal of relative dimension one is Zariski local on the source, an open
immersion being étale. -/
public instance isAtWorstNodalOfRelativeDimensionOne_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@IsAtWorstNodalOfRelativeDimensionOne.{u}) :=
  have hle : Scheme.zariskiPrecoverage.{u} ≤ Scheme.etalePrecoverage.{u} :=
    Scheme.precoverage_mono fun _ _ _ hi => have := hi; inferInstance
  MorphismProperty.IsLocalAtSource.of_le hle

/-- **Stacks 04QZ** for at-worst-nodal morphisms of relative dimension one: the property is
étale local on the source and target, being étale local on the source, stable under base change
and preserved by postcomposition with an étale morphism. -/
public theorem isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@IsAtWorstNodalOfRelativeDimensionOne.{u}) :=
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

end AlgebraicGeometry

end
