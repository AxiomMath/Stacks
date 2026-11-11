module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherentExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules

/-!
# The functor `d` of Stacks 0GQS reflects exactness

Item (11) of Stacks 0GQS: for `f` flat and surjective, a complex `ℱ^•` of `QCoh(𝒪_𝒳)` is exact if
and only if `d(ℱ^•)` is exact. One direction is the exactness of `d` (item (5)); for the other,
`d(H^i(ℱ^•)) = H^i(d(ℱ^•)) = 0`, and an object `𝒢` of `QCoh(𝒪_𝒳)` with `d(𝒢) = 0` is zero: it
is parasitic by item (10), and a quasi-coherent parasitic module is zero.

## Main results

* `CategoryTheory.Functor.exactAt_mapHomologicalComplex_iff`: an exact functor between abelian
  categories which reflects zero objects preserves and reflects the exactness of complexes.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]

/-- An exact functor `F` between abelian categories which reflects zero objects preserves and
reflects exactness of complexes: `F(K)` is exact at `i` if and only if `K` is. Indeed `F`
commutes with homology, `H_i(F K) ≅ F(H_i K)`. -/
theorem exactAt_mapHomologicalComplex_iff (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ X : C, IsZero (F.obj X) → IsZero X) {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).ExactAt i ↔ K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  have e : ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
    (K.sc i).mapHomologyIso F
  exact ⟨fun h => hF _ (h.of_iso e.symm), fun h => (F.map_isZero h).of_iso e⟩

/-- An exact functor between abelian categories which reflects zero objects preserves and
reflects acyclicity of complexes. -/
theorem acyclic_mapHomologicalComplex_iff (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ X : C, IsZero (F.obj X) → IsZero X) {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    ((F.mapHomologicalComplex c).obj K).Acyclic ↔ K.Acyclic :=
  forall_congr' fun i => exactAt_mapHomologicalComplex_iff F hF c K i

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open Opposite

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- The inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`: a quasi-coherent module read on the étale site
of `𝒳` is locally quasi-coherent with the flat base change property. -/
def qcohToLqcohFbc :
    AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ lqcohFbcModules B S hS 𝒳 :=
  ObjectProperty.lift _
    (FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)
    fun M => lqcohSheafFbcFppfModules_quasicoherentInclusion B (associatedBigEtaleSite B) rfl S
      hS 𝒳 M

/-- `c` restricted to `QCoh(𝒪_𝒳)` is `d`. -/
theorem qcohToLqcohFbc_comp_lqcohFbcSpaceRestriction :
    qcohToLqcohFbc B S hS 𝒳 ⋙ lqcohFbcSpaceRestriction B S hS 𝒳 U hU f =
      qcohSpaceRestriction B S hS 𝒳 U hU f :=
  rfl

/-- **A quasi-coherent parasitic module is zero.** The zero endomorphism of a quasi-coherent
module whose sections vanish at every flat object is bijective at every flat object, hence an
isomorphism (`AlgebraicGeometry.Stack.isIso_of_flatObject`). -/
theorem isZero_of_isParasitic (G : AlgebraicStacks.quasicoherentModules B S hS 𝒳)
    (hG : IsParasitic B S hS 𝒳 .fppf G.obj.val) : IsZero G := by
  have hψ : IsIso (0 : G ⟶ G).hom :=
    isIso_of_flatObject G.property G.property (0 : G ⟶ G).hom fun x hx =>
      have := hG x hx
      ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have : IsIso ((ObjectProperty.ι _).map (0 : G ⟶ G)) := hψ
  have : IsIso (0 : G ⟶ G) := isIso_of_reflects_iso _ (ObjectProperty.ι _)
  exact IsZero.of_mono_zero G G

end AlgebraicGeometry.Stack.AlgebraicStacks

end
