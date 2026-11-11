module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Isomorphisms descend to a stage of a directed limit of algebraic spaces

Let `B = lim B_i` be a directed inverse limit of quasi-compact and quasi-separated algebraic
spaces over `S` with affine transition morphisms, and let `f₀ : X₀ ⟶ Y₀` be a morphism of
quasi-compact and quasi-separated algebraic spaces over one stage `B₀`. If `f₀` is locally of
finite presentation and its base change to `B` is an isomorphism, then its base change to some
stage `B_i` is already an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective`: a
  morphism of algebraic spaces which is étale, universally injective and surjective is an
  isomorphism.
* `MorphismDescentSituation.exists_isIso_mapAt_of_siteContainsBaseChangeLimits` (in
  `AlgebraicGeometry.Space`): **Stacks 0852** (and 084S), the isomorphism descends to a stage
  of the inverse system, under the chapter's convention 07SD.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isIso_mapAt`: the same for a system
  whose index is bounded by the cofinality of the site's cutoff.

## Implementation notes

An isomorphism is étale, universally injective and surjective, and each of those three
properties descends to a stage by Stacks 07SL, 084X and 07SN respectively; by directedness the
three stages are dominated by one, so it suffices to know that the three properties together
force a morphism of algebraic spaces to be an isomorphism. That is Stacks 05W5: étaleness makes
the relative diagonal an open immersion, which together with universal injectivity makes the
morphism a monomorphism, while an étale surjection is surjective as a map of fppf sheaves, and a
locally surjective monomorphism of sheaves is invertible.

Transporting a property from a stage to a later one uses that the base change `f_j` of `f₀` is a
base change of `f_i` whenever `i ≤ j`; the cartesian square witnessing this is obtained by
pasting, from the two squares exhibiting `f_i` and `f_j` as base changes of `f₀` itself.

Local finite presentation of `f₀` is the hypothesis of Stacks 07SL and 07SN, while Stacks 084X
asks only for local finite type, which it implies.

## References

* [Stacks Project, Tag 0852](https://stacks.math.columbia.edu/tag/0852)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SN](https://stacks.math.columbia.edu/tag/07SN)
* [Stacks Project, Tag 084X](https://stacks.math.columbia.edu/tag/084X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Criterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A monomorphism of presheaves of types which is locally surjective for a topology and whose
source and target are sheaves is an isomorphism. -/
private theorem isIso_of_mono_of_isLocallySurjective
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) (f : X ⟶ Y) (hmono : Mono f)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) : IsIso f := by
  let J := BigFppfOver.topology B S hS
  let g : (⟨X, hX⟩ : Sheaf J (Type u)) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).1
    ⟨Presheaf.isLocallyInjective_of_injective J f
      fun T ↦ (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).1 hmono T), hloc⟩
  exact (sheafToPresheaf J (Type u)).map_isIso g

/-- **Stacks 05W5.** A morphism of algebraic spaces over `S` which is étale, universally
injective and surjective is an isomorphism.

An étale morphism is unramified, so its relative diagonal is an open immersion; together with
universal injectivity this makes the morphism a monomorphism. An étale surjection is flat and
locally of finite presentation, hence a one-member fppf covering of its target and so surjective
as a map of fppf sheaves. -/
@[stacks 05W5]
theorem isIso_of_isEtale_of_universallyInjective_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (he : IsEtale B S hS f) (hui : UniversallyInjective B S hS f)
    (hsurj : IsSurjective B S hS f) : IsIso f :=
  isIso_of_mono_of_isLocallySurjective B S hS hX.isSheaf hY.isSheaf f
    (mono_of_isOpenImmersion_diagonal_of_universallyInjective B S hS hX f
      (isOpenImmersion_diagonal_of_isUnramified B S hS hX hY f
        (isUnramified_of_isEtale B S hS he)) hui)
    (isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation B S hS hX hY f hsurj
      (isFlat_of_isEtale B S hS he) (isLocallyOfFinitePresentation_of_isEtale B S hS he))

end Criterion

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out otherwise
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_isoDescent {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_isoDescent {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage is itself a base change of `f₀`, along
the projections of `X_i` and `Y_i` to `X₀` and `Y₀`. -/
private theorem isPullback_mapAt_aux
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : MorphismDescentSituation B S hS hZ I)
    (i : I) (hi : E.initial ≤ i) :
    IsPullback (pullback.snd (E.baseAtToInitial i hi) E.sourceToBase) (E.mapAt i hi) E.map₀
      (pullback.snd (E.baseAtToInitial i hi) E.targetToBase) := by
  have e₁ : E.mapAt i hi ≫ pullback.fst (E.baseAtToInitial i hi) E.targetToBase =
      pullback.fst (E.baseAtToInitial i hi) E.sourceToBase := E.mapAt_fst i hi
  have e₂ : E.map₀ ≫ E.targetToBase = E.sourceToBase := E.map₀_over
  have e₃ : E.mapAt i hi ≫ pullback.snd (E.baseAtToInitial i hi) E.targetToBase =
      pullback.snd (E.baseAtToInitial i hi) E.sourceToBase ≫ E.map₀ := E.mapAt_snd i hi
  refine IsPullback.of_bot ?_ e₃.symm (E.targetAt_isPullback i hi).flip
  convert (E.sourceAt_isPullback i hi).flip using 2
  exact e₁

/-- The base change of `f₀` to a later stage is a base change of its base change to an earlier
one: `X_j = Y_j ×_{Y_i} X_i` for `i ≤ j`. -/
private theorem exists_isPullback_mapAt_of_le_aux
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : MorphismDescentSituation B S hS hZ I)
    {i j : I} (hi : E.initial ≤ i) (hij : i ≤ j) :
    ∃ (α : E.sourceAt j (hi.trans hij) ⟶ E.sourceAt i hi)
      (β : E.targetAt j (hi.trans hij) ⟶ E.targetAt i hi),
      IsPullback α (E.mapAt j (hi.trans hij)) (E.mapAt i hi) β := by
  have hj : E.initial ≤ j := hi.trans hij
  have htb : E.base.map (homOfLE hij).op ≫ E.baseAtToInitial i hi = E.baseAtToInitial j hj :=
    (E.base.map_comp (homOfLE hij).op (homOfLE hi).op).symm.trans
      (congrArg E.base.map (Subsingleton.elim _ _))
  have hcomm : (pullback.fst (E.baseAtToInitial j hj) E.targetToBase ≫
        E.base.map (homOfLE hij).op) ≫ E.baseAtToInitial i hi =
      pullback.snd (E.baseAtToInitial j hj) E.targetToBase ≫ E.targetToBase := by
    rw [Category.assoc, htb]
    exact pullback.condition
  have hβ : (pullback.lift _ _ hcomm : E.targetAt j hj ⟶ E.targetAt i hi) ≫
      pullback.snd (E.baseAtToInitial i hi) E.targetToBase =
      pullback.snd (E.baseAtToInitial j hj) E.targetToBase := pullback.lift_snd _ _ _
  have hs : IsPullback (pullback.snd (E.baseAtToInitial j hj) E.sourceToBase) (E.mapAt j hj)
      E.map₀ ((pullback.lift _ _ hcomm : E.targetAt j hj ⟶ E.targetAt i hi) ≫
        pullback.snd (E.baseAtToInitial i hi) E.targetToBase) := by
    rw [hβ]
    exact isPullback_mapAt_aux E j hj
  exact ⟨_, pullback.lift _ _ hcomm, IsPullback.of_right' hs (isPullback_mapAt_aux E i hi)⟩

/-- Étaleness of the base change of `f₀` passes from a stage to every later stage. -/
private theorem isEtale_mapAt_of_le_aux
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : MorphismDescentSituation B S hS hZ I)
    {i j : I} (hi : E.initial ≤ i) (hij : i ≤ j)
    (h : IsEtale B S hS (E.mapAt i hi)) : IsEtale B S hS (E.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := exists_isPullback_mapAt_of_le_aux E hi hij
  have hfst : hpb.flip.isoPullback.hom ≫ pullback.fst β (E.mapAt i hi) =
      E.mapAt j (hi.trans hij) := hpb.flip.isoPullback_hom_fst
  rw [← hfst]
  exact isEtale_comp B S hS (isEtale_of_iso B S hS hpb.flip.isoPullback)
    (isEtale_pullback_fst B S hS (E.targetAt_isAlgebraicSpace j (hi.trans hij))
      (E.targetAt_isAlgebraicSpace i hi) (E.sourceAt_isAlgebraicSpace i hi) β
      (E.mapAt i hi) h)

/-- Universal injectivity of the base change of `f₀` passes from a stage to every later
stage. -/
private theorem universallyInjective_mapAt_of_le_aux
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : MorphismDescentSituation B S hS hZ I)
    {i j : I} (hi : E.initial ≤ i) (hij : i ≤ j)
    (h : UniversallyInjective B S hS (E.mapAt i hi)) :
    UniversallyInjective B S hS (E.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := exists_isPullback_mapAt_of_le_aux E hi hij
  exact universallyInjective_of_isPullback B S hS (E.sourceAt_isAlgebraicSpace i hi)
    (E.targetAt_isAlgebraicSpace j (hi.trans hij)) (E.targetAt_isAlgebraicSpace i hi)
    (E.mapAt i hi) β h hpb.flip

/-- Surjectivity of the base change of `f₀` passes from a stage to every later stage. -/
private theorem isSurjective_mapAt_of_le_aux
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : MorphismDescentSituation B S hS hZ I)
    {i j : I} (hi : E.initial ≤ i) (hij : i ≤ j)
    (h : IsSurjective B S hS (E.mapAt i hi)) :
    IsSurjective B S hS (E.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := exists_isPullback_mapAt_of_le_aux E hi hij
  exact surjective_pointsMap_of_isPullback B S hS hpb h

namespace MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage is itself a base change of `f₀`, along
the projections of `X_i` and `Y_i` to `X₀` and `Y₀`. -/
theorem isPullback_mapAt (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) (D.mapAt i hi) D.map₀
      (pullback.snd (D.baseAtToInitial i hi) D.targetToBase) :=
  isPullback_mapAt_aux D.toSituation i hi

/-- The base change of `f₀` to a later stage is a base change of its base change to an earlier
one: `X_j = Y_j ×_{Y_i} X_i` for `i ≤ j`. -/
theorem exists_isPullback_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j) :
    ∃ (α : D.sourceAt j (hi.trans hij) ⟶ D.sourceAt i hi)
      (β : D.targetAt j (hi.trans hij) ⟶ D.targetAt i hi),
      IsPullback α (D.mapAt j (hi.trans hij)) (D.mapAt i hi) β :=
  exists_isPullback_mapAt_of_le_aux D.toSituation hi hij

/-- Étaleness of the base change of `f₀` passes from a stage to every later stage. -/
theorem isEtale_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsEtale B S hS (D.mapAt i hi)) : IsEtale B S hS (D.mapAt j (hi.trans hij)) :=
  isEtale_mapAt_of_le_aux D.toSituation hi hij h

/-- Universal injectivity of the base change of `f₀` passes from a stage to every later
stage. -/
theorem universallyInjective_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : UniversallyInjective B S hS (D.mapAt i hi)) :
    UniversallyInjective B S hS (D.mapAt j (hi.trans hij)) :=
  universallyInjective_mapAt_of_le_aux D.toSituation hi hij h

/-- Surjectivity of the base change of `f₀` passes from a stage to every later stage. -/
theorem isSurjective_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsSurjective B S hS (D.mapAt i hi)) :
    IsSurjective B S hS (D.mapAt j (hi.trans hij)) :=
  isSurjective_mapAt_of_le_aux D.toSituation hi hij h

end MorphismDescentSystem

/-! ### The situation of Stacks 084W

The same results for `AlgebraicGeometry.Space.MorphismDescentSituation`, which imposes no
condition on the size of the index; the descent of isomorphisms then takes the explicit
hypothesis `hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D.base`, the
chapter's convention of Section 70.2 (tag 07SD), and is also stated under
`hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`, which implies it. -/

namespace MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage is itself a base change of `f₀`, along
the projections of `X_i` and `Y_i` to `X₀` and `Y₀`. -/
theorem isPullback_mapAt (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) (D.mapAt i hi) D.map₀
      (pullback.snd (D.baseAtToInitial i hi) D.targetToBase) :=
  isPullback_mapAt_aux D i hi

/-- The base change of `f₀` to a later stage is a base change of its base change to an earlier
one: `X_j = Y_j ×_{Y_i} X_i` for `i ≤ j`. -/
theorem exists_isPullback_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j) :
    ∃ (α : D.sourceAt j (hi.trans hij) ⟶ D.sourceAt i hi)
      (β : D.targetAt j (hi.trans hij) ⟶ D.targetAt i hi),
      IsPullback α (D.mapAt j (hi.trans hij)) (D.mapAt i hi) β :=
  exists_isPullback_mapAt_of_le_aux D hi hij

/-- Étaleness of the base change of `f₀` passes from a stage to every later stage. -/
theorem isEtale_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsEtale B S hS (D.mapAt i hi)) : IsEtale B S hS (D.mapAt j (hi.trans hij)) :=
  isEtale_mapAt_of_le_aux D hi hij h

/-- Universal injectivity of the base change of `f₀` passes from a stage to every later
stage. -/
theorem universallyInjective_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : UniversallyInjective B S hS (D.mapAt i hi)) :
    UniversallyInjective B S hS (D.mapAt j (hi.trans hij)) :=
  universallyInjective_mapAt_of_le_aux D hi hij h

/-- Surjectivity of the base change of `f₀` passes from a stage to every later stage. -/
theorem isSurjective_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsSurjective B S hS (D.mapAt i hi)) :
    IsSurjective B S hS (D.mapAt j (hi.trans hij)) :=
  isSurjective_mapAt_of_le_aux D hi hij h

/-- **Stacks 0852**, and **Stacks 084S**. In the situation of Stacks 084W, if the base change
`f` of `f₀` to the limit `B` is an isomorphism and `f₀` is locally of finite presentation, then
the base change `f_i` of `f₀` to some stage `B_i` is an isomorphism.

This is Stacks 0852. Stacks 084S draws the same conclusion in the limit situation of Stacks
084R, with the source and the target in addition assumed representable over the stage;
hypothesis (a) of that tag is not needed here, since the three properties into which being an
isomorphism is decomposed all descend without it.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. -/
@[stacks 0852 "under the convention 07SD (hconv)", stacks 084S "without hypothesis (a)",
  ega "IV 8.8.2.5" "f iso ⇒ f_i iso"]
theorem exists_isIso_mapAt_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsIso D.mapLimit)
    (hfp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsIso (D.mapAt i hi) := by
  have hEt : IsEtale B S hS D.mapLimit := isEtale_of_iso B S hS (asIso D.mapLimit)
  have hUI : UniversallyInjective B S hS D.mapLimit := universallyInjective_of_isIso B S hS _
  have hSurj : IsSurjective B S hS D.mapLimit := fun y ↦
    ⟨pointsMap B S hS D.targetLimit (inv D.mapLimit) y, by
      rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]⟩
  obtain ⟨i₁, hi₁, hEt₁⟩ := D.exists_isEtale_mapAt_of_siteContainsBaseChangeLimits hconv hEt hfp
  obtain ⟨i₂, hi₂, hUI₂⟩ := D.exists_universallyInjective_mapAt_of_siteContainsBaseChangeLimits
    hconv hUI (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp)
  obtain ⟨i₃, hi₃, hSurj₃⟩ :=
    D.exists_isSurjective_mapAt_of_siteContainsBaseChangeLimits hconv hSurj hfp
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  obtain ⟨j, hjk, hj₃⟩ := directed_of (· ≤ ·) k i₃
  refine ⟨j, hi₁.trans (hk₁.trans hjk), ?_⟩
  exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
    (D.sourceAt_isAlgebraicSpace j _) (D.targetAt_isAlgebraicSpace j _) _
    (D.isEtale_mapAt_of_le hi₁ (hk₁.trans hjk) hEt₁)
    (D.universallyInjective_mapAt_of_le hi₂ (hk₂.trans hjk) hUI₂)
    (D.isSurjective_mapAt_of_le hi₃ hj₃ hSurj₃)

/-- **Stacks 0852**, and **Stacks 084S**. In the situation of Stacks 084W, if the base change
`f` of `f₀` to the limit `B` is an isomorphism and `f₀` is locally of finite presentation, then
the base change `f_i` of `f₀` to some stage `B_i` is an isomorphism.

This is Stacks 0852. Stacks 084S draws the same conclusion in the limit situation of Stacks
084R, with the source and the target in addition assumed representable over the stage;
hypothesis (a) of that tag is not needed here, since the three properties into which being an
isomorphism is decomposed all descend without it.

This is the statement under smallness of the system for the site, which implies the chapter's
convention; see `exists_isIso_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isIso_mapAt (hb : IsSiteSmall B S hS D.base) (hf : IsIso D.mapLimit)
    (hfp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsIso (D.mapAt i hi) :=
  have : Nonempty I := ⟨D.initial⟩
  D.exists_isIso_mapAt_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) hf hfp

end MorphismDescentSituation

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- **Isomorphisms descend to a stage, for an index bounded by the site's cutoff.** For a
morphism descent system, if the base change `f` of `f₀` to the limit `B` is an isomorphism and
`f₀` is locally of finite presentation, then the base change `f_i` of `f₀` to some stage `B_i`
is an isomorphism.

This is the conclusion of Stacks 0852 (and of Stacks 084S), but a morphism descent system
carries the bound `MorphismDescentSystem.indexSize`, `#I < cof(cutoff.ord)`, on the index, which
is stronger than the chapter's convention of Section 70.2 (tag 07SD). The statement of Stacks
0852 under exactly that convention, with no condition on the index, is
`exists_isIso_mapAt_of_siteContainsBaseChangeLimits` in the namespace
`AlgebraicGeometry.Space.MorphismDescentSituation`, which carries both tags. -/
theorem exists_isIso_mapAt (hf : IsIso D.mapLimit)
    (hfp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsIso (D.mapAt i hi) :=
  D.toSituation.exists_isIso_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) hf hfp

end AlgebraicGeometry.Space.MorphismDescentSystem

end
