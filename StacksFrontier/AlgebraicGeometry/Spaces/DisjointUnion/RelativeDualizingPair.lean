module

public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.Derived
public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange

/-!
# Relative dualizing pairs on a disjoint union

Let `Z = ⨆ i, X i` and `Y = ⨆ i, Y i` be disjoint unions of algebraic spaces, with injections
`j i : X i ⟶ Z` and `b i : Y i ⟶ Y`, and let `f : Z ⟶ Y` restrict to `f i : X i ⟶ Y i`, that is,
`j i ≫ f = f i ≫ b i`, all flat and of finite presentation. Given a pair `(ω i, τ i)` for each
`f i` (a `Y i`-perfect `ω i` with `τ i : R(f i)_* ω i ⟶ 𝒪_{Y i}`), there is a pair `(ω, τ)` for
`f` together with isomorphisms `e i : L(j i)^* ω ≅ ω i` under which `L(b i)^* τ`, read through
the base change map `L(b i)^* Rf_* ω ⟶ R(f i)_* L(j i)^* ω` of Stacks 07A7, is `τ i`. This is the
pair "constructed using the pairs on the pieces" in the proof of Stacks 0E61.

The base change maps along the injections of a disjoint union are invertible: an injection is an
open immersion, so this is
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isEtale`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_cofanInj_of_isColimit`: the base
  change maps along the injections of a disjoint union are isomorphisms.
* `AlgebraicGeometry.Space.exists_relativeDualizingPair_of_isColimit_cofan`: the pair on the
  disjoint union assembled from the pairs on the pieces.

## Implementation notes

The derived categories are taken at `HasDerivedCategory.standard`, as a plain local instance:
no global `HasDerivedCategory` instance applies to the categories of `𝒪`-modules on the small
étale sites here (`#synth HasDerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)` fails without it).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] modules_abelian Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over
  Stacks.hasSheafCompose_forget₂_commRingCat RingedSite.sliceHasSheafify
  RingedSite.sliceWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type u} {X : ι → AlgebraicSpaces B S hS} {Z : AlgebraicSpaces B S hS}
  {j : ∀ i, X i ⟶ Z}

/-- **Base change along the injection of a summand is invertible**: for a cartesian square whose
bottom arrow is the injection `j i` of a disjoint union, the base change map of Stacks 07A7 is an
isomorphism, the injection being an étale open immersion. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_cofanInj_of_isColimit
    (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
      fun i => (algebraicSpacesToSheaf B S hS).map (j i))) (i : ι)
    {W W' : AlgebraicSpaces B S hS} {f : W ⟶ Z} {f' : W' ⟶ X i} {g' : W' ⟶ W}
    (sq : IsPullback g' f' f (j i))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f (j i) f' g' sq.w K) :=
  isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f (j i) f' g' sq
    (isEtale_cofanInj_of_isColimit hc i) (isOpenImmersion_cofanInj_of_isColimit hc i).1 K

variable (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
    fun i => (algebraicSpacesToSheaf B S hS).map (j i)))
  {Y : AlgebraicSpaces B S hS} {Yi : ι → AlgebraicSpaces B S hS} {b : ∀ i, Yi i ⟶ Y}
  (hcY : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Y)
    fun i => (algebraicSpacesToSheaf B S hS).map (b i)))
  (f : Z ⟶ Y) (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
  (fi : ∀ i, X i ⟶ Yi i) (hfli : ∀ i, IsFlat B S hS (fi i).hom)
  (hfpi : ∀ i, IsFinitePresentation B S hS (fi i).hom) (w : ∀ i, j i ≫ f = fi i ≫ b i)

include hc hcY in
/-- **The relative dualizing pair on a disjoint union, from the pairs on the pieces.** For
`f : ⨆ i, X i ⟶ ⨆ i, Y i` restricting to `f i : X i ⟶ Y i`, a pair `(ω i, τ i)` for every `f i`
gives a pair `(ω, τ)` for `f` and isomorphisms `e i : L(j i)^* ω ≅ ω i` such that `L(b i)^* τ`,
composed with the identification `L(b i)^* 𝒪_Y ≅ 𝒪_{Y i}`, is the base change map of Stacks 07A7
followed by `R(f i)_* (e i)` and `τ i`. -/
theorem exists_relativeDualizingPair_of_isColimit_cofan
    (P : ∀ i, RelativeDualizingPair (fi i) (hfli i) (hfpi i)) :
    ∃ (Q : RelativeDualizingPair f hfl hfp)
      (e : ∀ i, (smallEtaleDerivedModulePullback B S hS (j i)).obj Q.ω ≅ (P i).ω),
      ∀ i, (smallEtaleDerivedModulePullback B S hS (b i)).map Q.τ ≫
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (b i)).hom =
        smallEtaleDerivedModuleBaseChangeMap B S hS f (b i) (fi i) (j i) (w i) Q.ω ≫
          (derivedModulePushforward B S hS (fi i)).map (e i).hom ≫ (P i).τ := by
  have hZ := isEquivalence_pi'_smallEtaleDerivedModulePullback hc
  have hY := isEquivalence_pi'_smallEtaleDerivedModulePullback hcY
  obtain ⟨ω, ⟨eω⟩⟩ := hZ.essSurj.mem_essImage fun i => (P i).ω
  let e : ∀ i, (smallEtaleDerivedModulePullback B S hS (j i)).obj ω ≅ (P i).ω :=
    fun i => Pi.isoApp eω i
  have hω : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hfp.1 ω :=
    (isPerfectRelativeToCanonical_iff_forall_smallEtaleDerivedModulePullback hc f hfl hfp.1
      fi b hfli (fun i => (hfpi i).1) (isEtale_cofanInj_of_isColimit hcY) w ω).2 fun i =>
        isPerfectRelativeToCanonical_of_iso (fi i) (hfli i) (hfpi i).1 (e i).symm
          (P i).isPerfectRelativeTo
  obtain ⟨τ, hτ⟩ := hY.full.map_surjective
    (X := (derivedModulePushforward B S hS f).obj ω)
    (Y := (derivedStructureSheaf B S hS Y.1 Y.2).obj) fun i =>
      (smallEtaleDerivedModuleBaseChangeMap B S hS f (b i) (fi i) (j i) (w i) ω ≫
        (derivedModulePushforward B S hS (fi i)).map (e i).hom ≫ (P i).τ) ≫
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (b i)).inv
  refine ⟨⟨ω, hω, τ⟩, e, fun i => ?_⟩
  have h := congrFun hτ i
  change (smallEtaleDerivedModulePullback B S hS (b i)).map τ = _ at h
  rw [h]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
    (Category.comp_id _))

end AlgebraicGeometry.Space

end
