module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria

/-!
# Surjectivity of an inverse image along an étale morphism from local surjectivity on charts

Let `j : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `φ : M ⟶ N` be a morphism of `𝒪_X`-modules.  Along `j` the inverse image
of modules is étale restriction (Stacks 03LW), so `j^*φ` is an epimorphism as soon as `φ` is
locally surjective at the étale charts of `X` which factor through `j` — a condition much weaker
than `φ` being an epimorphism when `j` is the inclusion of an open subspace.

## Main definitions

* `Stacks.SheafOfModules.IsLocallySurjectiveAt`: local surjectivity of a morphism of presheaves
  of modules at one object of the site.
* `AlgebraicGeometry.Space.liftChartOfRangeLE`: an étale chart of `X` landing in an open subspace
  `U`, read as an étale chart of `U`; postcomposing it with the inclusion of `U` gives the chart
  back on the nose (`AlgebraicGeometry.Space.smallEtalePostcomp_liftChart`).

## Main results

* `AlgebraicGeometry.Space.epi_modulePullback_map_of_isLocallySurjectiveAt`: **if `φ` is locally
  surjective at every étale chart of `X` of the form `j ∘ W`, then `j^*φ` is an epimorphism.**
* `AlgebraicGeometry.Space.epi_modulePullback_comp_map` and
  `AlgebraicGeometry.Space.isIso_modulePullback_comp_map`: surjectivity and invertibility of an
  inverse image along a composite `a ≫ b` follow from those of the inverse image along `b`.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {O : Cᵒᵖ ⥤ RingCat.{w}}
  {F G : PresheafOfModules.{w} O}

/-- **Local surjectivity of a morphism of presheaves of modules at one object.**  Every section
of the target over `U` lifts along `ψ` locally on `U`: its image sieve is a covering sieve
of `U`. -/
def IsLocallySurjectiveAt (ψ : F ⟶ G) (U : C) : Prop :=
  ∀ s : ToType (((PresheafOfModules.toPresheaf _).obj G).obj (op U)),
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map ψ) s ∈ J U

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inverse images along a composite -/

/-- **An inverse image along a composite `a ≫ b` is surjective as soon as the inverse image along
`b` is.** -/
theorem epi_modulePullback_comp_map {W U X : AlgebraicSpaces B S hS} (a : W ⟶ U) (b : U ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : Epi ((modulePullback B S hS b).map φ)) :
    Epi ((modulePullback B S hS (a ≫ b)).map φ) := by
  have h₁ : Epi ((modulePullback B S hS b ⋙ modulePullback B S hS a).map φ) :=
    @Functor.map_epi _ _ _ _ _ (preservesEpimorphisms_modulePullback B S hS a) _ _ _ h
  rw [← NatIso.naturality_1 (modulePullbackCompIso B S hS a b) φ]
  exact @epi_comp _ _ _ _ _ _
    (@IsIso.epi_of_iso _ _ _ _ _ (((modulePullbackCompIso B S hS a b).app M).isIso_inv)) _
    (@epi_comp _ _ _ _ _ _ h₁ _
      (@IsIso.epi_of_iso _ _ _ _ _ (((modulePullbackCompIso B S hS a b).app N).isIso_hom)))

/-- **An inverse image along a composite `a ≫ b` is invertible as soon as the inverse image along
`b` is.** -/
theorem isIso_modulePullback_comp_map {W U X : AlgebraicSpaces B S hS} (a : W ⟶ U) (b : U ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : IsIso ((modulePullback B S hS b).map φ)) :
    IsIso ((modulePullback B S hS (a ≫ b)).map φ) := by
  have h₁ : IsIso ((modulePullback B S hS b ⋙ modulePullback B S hS a).map φ) :=
    show IsIso ((modulePullback B S hS a).map ((modulePullback B S hS b).map φ)) from
      Functor.map_isIso _ _
  rw [← NatIso.naturality_1 (modulePullbackCompIso B S hS a b) φ]
  infer_instance

/-! ### Surjectivity of an étale inverse image -/

/-- **The inverse image along an étale morphism `j` of a morphism of modules which is locally
surjective at the charts `j ∘ W` is an epimorphism.** -/
theorem epi_modulePullback_map_of_isLocallySurjectiveAt {U X : AlgebraicSpaces B S hS}
    (j : U ⟶ X) (hj : IsEtale B S hS j.hom) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ W : SmallEtale B S hS U.1, Stacks.SheafOfModules.IsLocallySurjectiveAt
      (SmallEtale.topology B S hS X.1) φ.val ((smallEtalePostcomp B S hS j hj).obj W)) :
    Epi ((modulePullback B S hS j).map φ) := by
  have he : Epi ((etaleModulePullback.{u, u} B S hS j hj).map φ) := by
    refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {W} s => ?_⟩
    refine (SmallEtale.topology B S hS U.1).superset_covering ?_
      (SmallEtale.smallEtalePostcomp_cover_lift B S hS j hj W _ (h W s))
    intro W' a ha
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, hm⟩
  rw [← NatIso.naturality_2 (modulePullbackIsoEtaleModulePullback B S hS j hj) φ]
  exact @epi_comp _ _ _ _ _ _
    (@IsIso.epi_of_iso _ _ _ _ _
      (((modulePullbackIsoEtaleModulePullback B S hS j hj).app M).isIso_hom)) _
    (@epi_comp _ _ _ _ _ _ he _
      (@IsIso.epi_of_iso _ _ _ _ _
        (((modulePullbackIsoEtaleModulePullback B S hS j hj).app N).isIso_inv)))

/-! ### Charts landing in an open subspace -/

/-- Being étale is invariant under isomorphisms of schemes, read through the big fppf site. -/
theorem respectsIso_inverseImage_etale :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
  MorphismProperty.RespectsIso.inverseImage _ _

/-- **An étale chart of `X` landing in a subfunctor `U`, read as an étale chart of `U`.**  Its
structure morphism is the factorisation through `U`, which is étale because its composite with
the monomorphism `U ⟶ X` is. -/
noncomputable def liftChartOfRangeLE {X : AlgebraicSpaces B S hS} (U : Subfunctor X.1)
    (hU : IsAlgebraicSpace B S hS U.toFunctor) (V : SmallEtale B S hS X.1)
    (hV : Subfunctor.range V.1.hom ≤ U) :
    SmallEtale B S hS (⟨U.toFunctor, hU⟩ : AlgebraicSpaces B S hS).1 :=
  ⟨CostructuredArrow.mk (Subfunctor.lift V.1.hom hV),
    @MorphismProperty.presheaf_of_comp_mono _ _ _ (respectsIso_inverseImage_etale B S hS) _ _ _
      _ U.ι _
      (show (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
        Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.lift V.1.hom hV ≫ U.ι)
        by rw [Subfunctor.lift_ι]; exact V.2)⟩

/-- Postcomposing the lifted chart with the inclusion of the subfunctor gives the chart back. -/
theorem smallEtalePostcomp_liftChart {X : AlgebraicSpaces B S hS} (U : Subfunctor X.1)
    (hU : IsAlgebraicSpace B S hS U.toFunctor)
    (hE : IsEtale B S hS
      (ObjectProperty.homMk U.ι : (⟨U.toFunctor, hU⟩ : AlgebraicSpaces B S hS) ⟶ X).hom)
    (V : SmallEtale B S hS X.1) (hV : Subfunctor.range V.1.hom ≤ U) :
    (smallEtalePostcomp B S hS (ObjectProperty.homMk U.ι) hE).obj
      (liftChartOfRangeLE B S hS U hU V hV) = V :=
  rfl

/-- A chart postcomposed with the inclusion of a subfunctor lands in that subfunctor. -/
theorem range_smallEtalePostcomp_le {X : AlgebraicSpaces B S hS} (U : Subfunctor X.1)
    (hU : IsAlgebraicSpace B S hS U.toFunctor)
    (hE : IsEtale B S hS
      (ObjectProperty.homMk U.ι : (⟨U.toFunctor, hU⟩ : AlgebraicSpaces B S hS) ⟶ X).hom)
    (W : SmallEtale B S hS (⟨U.toFunctor, hU⟩ : AlgebraicSpaces B S hS).1) :
    Subfunctor.range ((smallEtalePostcomp B S hS (ObjectProperty.homMk U.ι) hE).obj W).1.hom ≤
      U :=
  (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι U).le

/-- Landing in a subfunctor passes to charts over a chart. -/
theorem range_le_of_hom {X : AlgebraicSpaces B S hS} (U : Subfunctor X.1)
    {V V' : SmallEtale B S hS X.1} (a : V' ⟶ V) (hV : Subfunctor.range V.1.hom ≤ U) :
    Subfunctor.range V'.1.hom ≤ U := by
  have h : V'.1.hom = yoneda.map a.hom.left ≫ V.1.hom := by
    have := CostructuredArrow.w a.hom
    exact this.symm
  rw [h]
  exact (Subfunctor.range_comp_le _ _).trans hV

end AlgebraicGeometry.Space

end
