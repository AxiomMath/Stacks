module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSourceLocalityFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteTypeWellNighAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.ModuliSpaceSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Étale local nature of Stacks 0DUX

The étale-local step of Stacks 0DUX: if `f : 𝒳 ⟶ M` is a 1-morphism to an algebraic space and
`g_i : 𝒳_i ⟶ 𝒳` is a family of well-nigh affine algebraic stacks over `𝒳`, étale and
representable by algebraic spaces, jointly surjective on points, whose categorical moduli spaces
`M_i` map étale to `M` compatibly with `f`, then for every `p : 𝒳 ⟶ Y` locally of finite type to
a locally Noetherian algebraic space and every `q : M ⟶ Y` with `f ≫ q ≅ p`, the morphism `q` is
locally of finite type.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isEtale`: an étale
  1-morphism representable by algebraic spaces is locally of finite type.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale_cover`: local finite type descends
  along a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_cover`: the
  étale-local step.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_squares`: the
  same, with the moduli spaces of the pieces mapping étale to *some* uniform categorical moduli
  space of `𝒳`.

## References

* [Stacks Project, Tag 0DUX](https://stacks.math.columbia.edu/tag/0DUX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local finite type descends along a jointly surjective family of étale morphisms.** -/
theorem isLocallyOfFiniteType_of_isEtale_cover {ι : Type v} {X Y : AlgebraicSpaces B S hS}
    (Xi : ι → AlgebraicSpaces B S hS) (a : ∀ i, Xi i ⟶ X) (ha : ∀ i, IsEtale B S hS (a i).hom)
    (hcover : ∀ x : points B S hS X.obj, ∃ i y, pointsMap B S hS (Xi i).obj (a i).hom y = x)
    (f : X ⟶ Y) (hf : ∀ i, IsLocallyOfFiniteType B S hS ((a i).hom ≫ f.hom)) :
    IsLocallyOfFiniteType B S hS f.hom := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsLocallyOfFiniteType B S hS k.hom
  let _ : P.IsLocalAtSource (Topology.precoverage.{u, v} .fppf B S hS) :=
    isLocallyOfFiniteType_isLocalAtSource_fppf.{u, v} B S hS
  have hR : Presieve.ofArrows Xi a ∈ Topology.precoverage.{u, v} .fppf B S hS X :=
    ⟨ι, _, _, rfl, X.property, fun i => (Xi i).property, isFppfCovering_of_isEtaleCovering B S hS
      ⟨X.property, fun i => (Xi i).property, ha,
        Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr (hcover x)⟩⟩
  exact MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR fun _ _ ⟨i⟩ => hf i

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale 1-morphism of algebraic stacks representable by algebraic spaces is locally of
finite type.** -/
theorem AlgebraicStacks.isLocallyOfFiniteType_of_isEtale {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (he : IsEtale B S hS f) : AlgebraicStacks.IsLocallyOfFiniteType B S hS f := by
  obtain ⟨-, hrel⟩ := isRelativelyEtale_of_isEtale B S hS f hrep he
  apply (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒳.property 𝒴.property f.hom).2
  apply (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒳.property 𝒴.property f.hom hrep).2
  exact fun V y hy G hG e => Space.isLocallyOfFiniteType_of_isEtale' B S hS _ (hrel V y hy G hG e)

/-- The map on points of the 1-morphism attached to a morphism of algebraic spaces is the map on
points of that morphism, through `AlgebraicGeometry.Stack.spacePointsEquiv`. -/
theorem pointsMap_algebraicSpaceStackMap_spacePointsEquiv {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (φ : F ⟶ G)
    (x : Space.points B S hS F) :
    AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hF hG φ)
        (spacePointsEquiv B S hS F x) =
      spacePointsEquiv B S hS G (Space.pointsMap B S hS F φ x) :=
  (spacePointMap_pointsMap_associatedMap B S hS φ x).symm

/-- **The moduli spaces of a jointly surjective family over `𝒳` cover `M`.** If `f : 𝒳 ⟶ M` is
surjective on points, `g_i : 𝒳_i ⟶ 𝒳` are jointly surjective on points, and `f_i ≫ b_i ≅ g_i ≫ f`
for 1-morphisms `f_i : 𝒳_i ⟶ M_i` and morphisms `b_i : M_i ⟶ M` of algebraic spaces, then the
`b_i` are jointly surjective on points. -/
theorem exists_pointsMap_eq_of_twoCommSq {ι : Type v} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {M : AlgebraicSpaces B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : Function.Surjective (AlgebraicStacks.pointsMap B S hS f))
    (𝒳i : ι → AlgebraicStacks.{u, w} B S hS) (g : ∀ i, 𝒳i i ⟶ 𝒳)
    (hg : ∀ x : AlgebraicStacks.points B S hS 𝒳,
      ∃ i y, AlgebraicStacks.pointsMap B S hS (g i) y = x)
    (Mi : ι → AlgebraicSpaces B S hS)
    (fi : ∀ i, 𝒳i i ⟶ algebraicSpaceStack.{u, w} B S hS (Mi i).obj (Mi i).property)
    (b : ∀ i, Mi i ⟶ M)
    (hcomm : ∀ i, Nonempty ((fi i).hom ≫ (associatedMap B S hS (b i).hom).1 ≅ (g i).hom ≫ f.hom))
    (z : Space.points B S hS M.obj) :
    ∃ i y, Space.pointsMap B S hS (Mi i).obj (b i).hom y = z := by
  obtain ⟨x, hx⟩ := hf (spacePointsEquiv B S hS M.obj z)
  obtain ⟨i, y, hy⟩ := hg x
  obtain ⟨ε⟩ := hcomm i
  refine ⟨i, (spacePointsEquiv B S hS (Mi i).obj).symm (AlgebraicStacks.pointsMap B S hS (fi i) y),
    (spacePointsEquiv B S hS M.obj).injective ?_⟩
  rw [← pointsMap_algebraicSpaceStackMap_spacePointsEquiv.{u, w} B S hS (Mi i).property
    M.property, Equiv.apply_symm_apply]
  have h1 : AlgebraicStacks.pointsMap B S hS
      (fi i ≫ algebraicSpaceStackMap.{u, w} B S hS (Mi i).property M.property (b i).hom) =
      AlgebraicStacks.pointsMap B S hS (g i ≫ f) :=
    pointsMap_eq_of_basedNatTrans B S hS _ _ _ ε.hom.hom
  have h2 := congrFun h1 y
  rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at h2
  exact h2.trans ((congrArg _ hy).trans hx)

/-- Pasting a 2-isomorphism `f ≫ u ≅ g ≫ f₀` with `f₀ ≫ v ≅ r` gives `f ≫ (u ≫ v) ≅ g ≫ r`. -/
private def comp_iso_of_comp_isos {C : Type*} [Bicategory C] {a b c d e : C} {f : a ⟶ b}
    {u : b ⟶ c} {v : c ⟶ d} {g : a ⟶ e} {f₀ : e ⟶ c} {r : e ⟶ d} (ε : f ≫ u ≅ g ≫ f₀)
    (η : f₀ ≫ v ≅ r) : f ≫ (u ≫ v) ≅ g ≫ r :=
  (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso ε _ ≪≫
    Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso g η

/-- **The étale-local step of Stacks 0DUX.** Let `f : 𝒳 ⟶ M` be surjective on points, and let
`g_i : 𝒳_i ⟶ 𝒳` be a family of well-nigh affine algebraic stacks, each `g_i` étale and
representable by algebraic spaces, jointly surjective on points, with categorical moduli spaces
`f_i : 𝒳_i ⟶ M_i` and étale morphisms `b_i : M_i ⟶ M` such that `f_i ≫ b_i ≅ g_i ≫ f`. Then for
`p : 𝒳 ⟶ Y` locally of finite type to a locally Noetherian algebraic space, every `q : M ⟶ Y` with
`f ≫ q ≅ p` is locally of finite type. -/
theorem isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_cover {ι : Type v}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {Y : AlgebraicSpaces B S hS}
    (hY : Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hp : AlgebraicStacks.IsLocallyOfFiniteType B S hS p) {M : AlgebraicSpaces B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : Function.Surjective (AlgebraicStacks.pointsMap B S hS f)) (q : M ⟶ Y)
    (hq : Nonempty (f.hom ≫ (associatedMap B S hS q.hom).1 ≅ p.hom))
    (𝒳i : ι → AlgebraicStacks.{u, w} B S hS) (h𝒳i : ∀ i, IsWellNighAffine.{u, w} B S hS (𝒳i i))
    (g : ∀ i, 𝒳i i ⟶ 𝒳) (hgrep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (g i).hom.hom)
    (hget : ∀ i, IsEtale B S hS (g i))
    (hg : ∀ x : AlgebraicStacks.points B S hS 𝒳,
      ∃ i y, AlgebraicStacks.pointsMap B S hS (g i) y = x)
    (Mi : ι → AlgebraicSpaces B S hS)
    (fi : ∀ i, 𝒳i i ⟶ algebraicSpaceStack.{u, w} B S hS (Mi i).obj (Mi i).property)
    (hfi : ∀ i, IsCategoricalModuliSpace B S hS (Mi i) (fi i).hom) (b : ∀ i, Mi i ⟶ M)
    (hb : ∀ i, Space.IsEtale B S hS (b i).hom)
    (hcomm : ∀ i, Nonempty ((fi i).hom ≫ (associatedMap B S hS (b i).hom).1 ≅ (g i).hom ≫ f.hom)) :
    Space.IsLocallyOfFiniteType B S hS q.hom := by
  refine Space.isLocallyOfFiniteType_of_isEtale_cover B S hS Mi b hb
    (exists_pointsMap_eq_of_twoCommSq B S hS f hf 𝒳i g hg Mi fi b hcomm) q (fun i => ?_)
  obtain ⟨ε⟩ := hcomm i
  obtain ⟨η⟩ := hq
  have hpi := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS (g i) p
    (AlgebraicStacks.isLocallyOfFiniteType_of_isEtale B S hS (g i) (hgrep i) (hget i)) hp
  refine isLocallyOfFiniteType_of_isWellNighAffine_of_isCategoricalModuliSpace B S hS (𝒳i i)
    (h𝒳i i) hY (g i ≫ p) hpi (fi i) (hfi i) (b i ≫ q) ⟨?_⟩
  change (fi i).hom ≫ (associatedMap B S hS ((b i).hom ≫ q.hom)).1 ≅ (g i).hom ≫ p.hom
  rw [associatedMap_comp]
  exact comp_iso_of_comp_isos ε η

/-- **The étale-local step of Stacks 0DUX, from étale squares of uniform moduli spaces.** As
`isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_cover`, with `f` a categorical moduli space
which is a universal homeomorphism, and with each piece `g_i : 𝒳_i ⟶ 𝒳` given a uniform
categorical moduli space `f'_i : 𝒳_i ⟶ M'_i`, a uniform categorical moduli space
`f₀ : 𝒳 ⟶ M₀` and an étale morphism `M'_i ⟶ M₀` with `f'_i ≫ (M'_i ⟶ M₀) = g_i ≫ f₀`. -/
theorem isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_squares {ι : Type v}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {Y : AlgebraicSpaces B S hS}
    (hY : Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hp : AlgebraicStacks.IsLocallyOfFiniteType B S hS p) {M : AlgebraicSpaces B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : IsCategoricalModuliSpace B S hS M f.hom) (hUH : UniversalHomeomorphism B S hS f)
    (q : M ⟶ Y) (hq : Nonempty (f.hom ≫ (associatedMap B S hS q.hom).1 ≅ p.hom))
    (𝒳i : ι → AlgebraicStacks.{u, w} B S hS) (h𝒳i : ∀ i, IsWellNighAffine.{u, w} B S hS (𝒳i i))
    (g : ∀ i, 𝒳i i ⟶ 𝒳) (hgrep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (g i).hom.hom)
    (hget : ∀ i, IsEtale B S hS (g i))
    (hg : ∀ x : AlgebraicStacks.points B S hS 𝒳,
      ∃ i y, AlgebraicStacks.pointsMap B S hS (g i) y = x)
    (hsq : ∀ i, ∃ (M₀ M' : AlgebraicSpaces B S hS)
      (f₀ : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M₀.obj M₀.property)
      (f' : 𝒳i i ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property) (g' : M' ⟶ M₀),
      f'.hom ≫ (associatedMap B S hS g'.hom).1 = (g i).hom ≫ f₀.hom ∧
        Space.IsEtale B S hS g'.hom ∧ IsUniformCategoricalModuliSpace B S hS M₀ f₀.hom ∧
          IsUniformCategoricalModuliSpace B S hS M' f'.hom) :
    Space.IsLocallyOfFiniteType B S hS q.hom := by
  choose M₀ M' f₀ f' g' hcomm hg' hu₀ hu' using hsq
  have he : ∀ i, ∃ e : M₀ i ≅ M, (f₀ i).hom ≫ (associatedMap B S hS e.hom.hom).1 = f.hom :=
    fun i => exists_iso_of_isCategoricalModuliSpace B S hS
      (isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS (hu₀ i)) hf
  choose e he using he
  have hsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS f) :=
    isSurjective_of_universalHomeomorphism B S hS f
      (fun 𝒵 k => hUH 𝒵 k (twoFibreProductSquareAlgebraicStacks B S hS k f)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k f))
  refine isLocallyOfFiniteType_of_wellNighAffine_etale_moduli_cover B S hS hY p hp f hsurj q hq
    𝒳i h𝒳i g hgrep hget hg M' f'
    (fun i => isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS (hu' i))
    (fun i => g' i ≫ (e i).hom)
    (fun i => Space.isEtale_comp B S hS (hg' i)
      (Space.isEtale_of_isIso B S hS ((ObjectProperty.ι _).map (e i).hom)))
    (fun i => ⟨?_⟩)
  change (f' i).hom ≫ (associatedMap B S hS ((g' i).hom ≫ (e i).hom.hom)).1 ≅ (g i).hom ≫ f.hom
  rw [associatedMap_comp]
  exact comp_iso_of_comp_isos (eqToIso (hcomm i)) (eqToIso (he i))

end Stack

end AlgebraicGeometry

end
