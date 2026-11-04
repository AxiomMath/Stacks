module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatGroupoidPresentationQuasicoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatGroupoidPresentationRestriction

/-!
# The coherator of Stacks 0778 and Stacks 0779, through a flat groupoid presentation

Let `𝒳` be an algebraic stack with a flat groupoid presentation `P = (U, R, s, t, c)`.  Following
the proof of **Stacks 0778**, the coherator is

```
Q = q₁ ∘ q₂ : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(U, R, s, t, c) ⟶ QCoh(𝒪_𝒳),
```

`q₂ = AlgebraicGeometry.Stack.FlatGroupoidPresentation.flatBaseChangeRestriction` and `q₁` the
inverse of the equivalence of Stacks 06WT
(`AlgebraicGeometry.Stack.FlatGroupoidPresentation.quasicoherentEquivalenceGroupoid`), whose
forward functor is `q₂` on quasi-coherent modules.  It is right adjoint to the inclusion
`i : QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)` because `Hom(i 𝒢, ℱ) = Hom(q₂ i 𝒢, q₂ ℱ)` (Stacks 076S) and
`q₂ ∘ i` is an equivalence (`Stacks.CategoryTheory.CoreflectionDetection.adjunctionOfEquivalence`).

Stacks 0779 is then the formal argument of `Stacks.CategoryTheory.CoreflectionDetection` for the
exact functor `ℱ ↦ x^*ℱ|_{U_étale}`, which inverts the counit `i Q ℱ ⟶ ℱ` and detects zero
quasi-coherent modules; with Stacks 0779 (1) in the form of
`AlgebraicGeometry.Stack.isParasitic_iff_forall_subsingleton_flatGroupoidPresentation_chart` it
gives that the kernel of `Q` is exactly the parasitic modules of `LQCoh^fbc(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.flatBaseChangeCoherator` and
  `…flatBaseChangeCoheratorAdjunction`: **Stacks 0778**, `i ⊣ Q`.
* `…isZero_flatBaseChangeCoherator_obj_iff` and
  `…isZero_flatBaseChangeCoherator_obj_iff_parasitic`: **Stacks 0779 (1)**.
* `…preservesFiniteColimits_flatBaseChangeCoherator`: `Q` is right exact, part of
  **Stacks 0779 (3)** (it is left exact as a right adjoint).

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack.FlatGroupoidPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : FlatGroupoidPresentation 𝒳)

section Coherator

/-- The forgetful functor from quasi-coherent modules on the groupoid `P.G` is faithful. -/
instance : (Space.QuasicoherentModule.forget P.G).Faithful where
  map_injective h := Space.QuasicoherentModule.Hom.ext h

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- `q₂ ∘ i` is the equivalence `Φ = q₁⁻¹` of Stacks 06WT: on quasi-coherent modules `q₂` is the
pointwise descent functor. -/
def quasicoherentInclusionCompIso :
    quasicoherentInclusion 𝒳 ⋙ P.flatBaseChangeRestriction ≅
      P.quasicoherentEquivalenceGroupoid.functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (Iso.refl _))
        (fun f => by ext1; rfl))
      (pointwiseDescentFunctor P.F P.hF 𝒳.val.isFiberedInGroupoids) ≪≫
    eqToIso P.quasicoherentEquivalenceGroupoid_functor.symm

/-- **The coherator of Stacks 0778**, `Q = q₁ ∘ q₂ : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`. -/
def flatBaseChangeCoherator :
    (lqcFbcFppf B S hS 𝒳).FullSubcategory ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  P.flatBaseChangeRestriction ⋙ P.quasicoherentEquivalenceGroupoid.inverse

/-- **Stacks 0778**: `Q` is right adjoint to the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`. -/
def flatBaseChangeCoheratorAdjunction :
    quasicoherentInclusion 𝒳 ⊣ P.flatBaseChangeCoherator :=
  Stacks.CategoryTheory.CoreflectionDetection.adjunctionOfEquivalence _ _ _
    P.quasicoherentInclusionCompIso
    (fun G F => P.bijective_flatBaseChangeRestriction_map _ F G.property)

/-- The coherator `Q` is a right adjoint. -/
instance : P.flatBaseChangeCoherator.IsRightAdjoint :=
  P.flatBaseChangeCoheratorAdjunction.isRightAdjoint

/-- The restriction `ℱ ↦ x^*ℱ|_{U_étale}` to the chart sends the counit `i Q ℱ ⟶ ℱ` to an
isomorphism. -/
theorem isIso_chartRestriction_map_counit (F : (lqcFbcFppf B S hS 𝒳).FullSubcategory) :
    IsIso (P.chartRestriction.map (P.flatBaseChangeCoheratorAdjunction.counit.app F)) := by
  have := Stacks.CategoryTheory.CoreflectionDetection.isIso_map_adjunctionOfEquivalence_counit_app
    _ _ _ P.quasicoherentInclusionCompIso
    (fun G F => P.bijective_flatBaseChangeRestriction_map _ F G.property) F
  have : IsIso (P.flatBaseChangeRestriction.map
      (P.flatBaseChangeCoheratorAdjunction.counit.app F)) := this
  exact (Space.QuasicoherentModule.forget P.G).map_isIso _

/-- A quasi-coherent module `𝒢` on `𝒳` is zero if its restriction `x^*𝒢|_{U_étale}` to the chart
is zero. -/
theorem isZero_of_isZero_chartRestriction_obj
    (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)
    (hG : IsZero (P.chartRestriction.obj ((quasicoherentInclusion 𝒳).obj G))) : IsZero G := by
  have h1 : IsZero (P.flatBaseChangeRestriction.obj ((quasicoherentInclusion 𝒳).obj G)) := by
    refine (IsZero.iff_id_eq_zero _).2 ((Space.QuasicoherentModule.forget P.G).map_injective ?_)
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hG
  exact IsZero.of_full_of_faithful_of_isZero P.quasicoherentEquivalenceGroupoid.functor G
    (h1.of_iso (P.quasicoherentInclusionCompIso.app G).symm)

end Coherator


section Exact

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- The inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` is faithful. -/
instance : (quasicoherentInclusion 𝒳).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (congrArg (fun f => f.hom) h :)

/-- The inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` is full. -/
instance : (quasicoherentInclusion 𝒳).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom, rfl⟩

/-- **Stacks 0779 (1)**, through the chart: `Q ℱ = 0` exactly when `ℱ|_{U_étale} = 0`. -/
theorem isZero_flatBaseChangeCoherator_obj_iff (F : (lqcFbcFppf B S hS 𝒳).FullSubcategory) :
    IsZero (P.flatBaseChangeCoherator.obj F) ↔ IsZero (P.chartRestriction.obj F) :=
  have := P.preservesFiniteLimits_chartRestriction
  have := P.preservesFiniteColimits_chartRestriction
  Stacks.CategoryTheory.CoreflectionDetection.isZero_obj_iff P.flatBaseChangeCoheratorAdjunction
    P.chartRestriction (fun F => ⟨_, _, P.isIso_chartRestriction_map_counit F⟩)
    P.isZero_of_isZero_chartRestriction_obj F

/-- **Stacks 0779 (3)**: `Q` is right exact. -/
theorem preservesFiniteColimits_flatBaseChangeCoherator :
    PreservesFiniteColimits P.flatBaseChangeCoherator :=
  have := P.preservesFiniteLimits_chartRestriction
  have := P.preservesFiniteColimits_chartRestriction
  Stacks.CategoryTheory.CoreflectionDetection.preservesFiniteColimits
    P.flatBaseChangeCoheratorAdjunction P.chartRestriction
    (fun F => ⟨_, _, P.isIso_chartRestriction_map_counit F⟩)
    P.isZero_of_isZero_chartRestriction_obj

/-- **Stacks 0779 (1)**: the kernel of the coherator of the flat groupoid presentation is exactly
the parasitic modules of `LQCoh^fbc(𝒪_𝒳)`. -/
theorem isZero_flatBaseChangeCoherator_obj_iff_parasitic
    (F : (lqcFbcFppf B S hS 𝒳).FullSubcategory) :
    IsZero ((flatGroupoidPresentation 𝒳).flatBaseChangeCoherator.obj F) ↔
      parasiticModules.{u, w, u} B S hS 𝒳 .fppf F.obj := by
  rw [isZero_flatBaseChangeCoherator_obj_iff]
  refine (Space.isZero_etaleRestrictedModuleInverseImage_iff B S hS _ _ _ _ _ _ _ _).trans ?_
  exact (isParasitic_iff_forall_subsingleton_flatGroupoidPresentation_chart 𝒳 F.obj
    F.property).symm

end Exact

end AlgebraicGeometry.Stack.FlatGroupoidPresentation
