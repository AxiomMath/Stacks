module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FaithfullyFlatLocalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion

/-!
# The support of a flat pullback of a quasi-coherent module

Let `g : X' ⟶ X` be a flat morphism of algebraic spaces over a scheme `S` and let `F` be a
quasi-coherent `𝒪_X`-module.  Then

`Supp(g^* F) = |g|^{-1}(Supp(F))`.

For a module of finite type this is the support clause of Stacks 07TZ, part (3), and holds for
an arbitrary `g`.  Flatness of `g` replaces the finite-type hypothesis: at a geometric point
`ȳ` of `X'` the stalk of `g^* F` is the base change of the stalk of `F` at the image geometric
point along the homomorphism `𝒪_{X, g ∘ ȳ} ⟶ 𝒪_{X', ȳ}` of étale local rings, which is
faithfully flat, and a faithfully flat base change of a nonzero module is nonzero.

## Main results

* `AlgebraicGeometry.Space.nontrivial_extendScalars_of_faithfullyFlat`: a faithfully flat base
  change of a nonzero module is nonzero, read at `ModuleCat.extendScalars`.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq_of_isFlat`: the equality of
  supports.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-- **A faithfully flat base change of a nonzero module is nonzero**, read at
`ModuleCat.extendScalars`: the tensor product `T ⊗_R M` is nonzero for `T` faithfully flat over
`R` and `M` nonzero. -/
theorem nontrivial_extendScalars_of_faithfullyFlat {R T : Type v} [CommRing R] [CommRing T]
    {φ : R →+* T} (hφ : φ.FaithfullyFlat) (M : ModuleCat.{v} R) [Nontrivial M] :
    Nontrivial ((ModuleCat.extendScalars φ).obj M) := by
  let : Algebra R T := φ.toAlgebra
  have : Module.FaithfullyFlat R T := hφ
  exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R T).mpr ‹Nontrivial M›

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : AlgebraicSpaces B S hS}

/-- **The support of a flat pullback of a quasi-coherent module is the inverse image of the
support.**  For a flat morphism `g : X' ⟶ X` of algebraic spaces and a quasi-coherent
`𝒪_X`-module `F`,

`Supp(g^* F) = |g|^{-1}(Supp(F))`.

One inclusion holds for every morphism.  For the other, a point of `X'` is represented by a
geometric point `ȳ`, the stalk of `F` at the image geometric point is nonzero because `F` is
quasi-coherent, and the stalk of `g^* F` at `ȳ` is its base change along the faithfully flat
homomorphism of étale local rings of Stacks 03MK. -/
theorem supportOfSheaf_modulePullback_eq_of_isFlat (g : X' ⟶ X) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite) :
    supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) =
      pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  have := hqc
  refine Set.Subset.antisymm
    (supportOfSheaf_modulePullback_subset_preimage B S hS g F) fun pt hpt => ?_
  rw [mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X' _ pt]
  obtain ⟨ybar, hyb⟩ := exists_geometricRepresentative B S hS X'.1 pt
  have : Nontrivial (geometricModuleStalk B S hS X (geometricPointMap g.hom ybar) F) :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X F
      (geometricPointMap g.hom ybar) (pointsMap B S hS X'.1 g.hom pt)
      ((geometricPointMap_image g.hom ybar).trans (congrArg _ hyb))).1 hpt
  refine ⟨ybar, hyb, ?_⟩
  exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
      (geometricModuleStalkPullbackIso B S hS g ybar F).hom)).nontrivial_congr.2
    (nontrivial_extendScalars_of_faithfullyFlat
      (faithfullyFlat_etaleLocalRingMap B S hS X'.2 X.2 g.hom hg ybar) _)

end AlgebraicGeometry.Space

end
