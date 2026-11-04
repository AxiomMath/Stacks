module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Right derived functors and endomorphisms of the identity functor

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with injective
resolutions, and let `λ : 𝟭 𝒜 ⟶ 𝟭 𝒜` and `μ : 𝟭 ℬ ⟶ 𝟭 ℬ` be endomorphisms of the identity
functors (for instance multiplication by a scalar in a linear category) such that
`F (λ_X) = μ_{F X}` for every `X`. Then `R^n F (λ_X) = μ_{R^n F (X)}` for every `n`.

This is how the module structure of a higher direct image is read off functorially: if `F` is
the direct image of sheaves of modules over a commutative ring `A`, multiplication by `a ∈ A` on
`R^n F (X)` is `R^n F` applied to multiplication by `a` on `X`.

## Main results

* `CategoryTheory.HomologicalComplex.homologyMap_homOfNatTrans`: on the homology of a complex, the
  chain map given termwise by an endomorphism of the identity functor is that endomorphism.
* `CategoryTheory.Functor.rightDerived_map_app_of_natTrans`: the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section Homology

variable {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ] (μ : 𝟭 ℬ ⟶ 𝟭 ℬ)
  {ι : Type*} {c : ComplexShape ι}

/-- The chain map given termwise by an endomorphism `μ` of the identity functor. -/
@[simps]
def HomologicalComplex.homOfNatTrans (K : HomologicalComplex ℬ c) : K ⟶ K where
  f i := μ.app (K.X i)
  comm' i j _ := (μ.naturality (K.d i j)).symm

/-- On homology, the chain map given termwise by an endomorphism `μ` of the identity functor is
`μ` itself. -/
theorem HomologicalComplex.homologyMap_homOfNatTrans (K : HomologicalComplex ℬ c) (i : ι) :
    HomologicalComplex.homologyMap (HomologicalComplex.homOfNatTrans μ K) i =
      μ.app (K.homology i) := by
  have hcyc : HomologicalComplex.cyclesMap (HomologicalComplex.homOfNatTrans μ K) i =
      μ.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i]
    exact μ.naturality (K.iCycles i)
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hcyc]
  exact (μ.naturality (K.homologyπ i)).symm

end Homology

section Derived

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
  {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] (lam : 𝟭 𝒜 ⟶ 𝟭 𝒜) (μ : 𝟭 ℬ ⟶ 𝟭 ℬ)

/-- **Right derived functors commute with endomorphisms of the identity functors.** If
`F (λ_X) = μ_{F X}` for every `X`, then `R^n F (λ_X) = μ_{R^n F (X)}`. The termwise action of
`λ` on an injective resolution of `X` lifts `λ_X`, and `F` turns it into the termwise action of
`μ`, which on homology is `μ`. -/
theorem Functor.rightDerived_map_app_of_natTrans
    (h : ∀ X : 𝒜, F.map (lam.app X) = μ.app (F.obj X)) (n : ℕ) (X : 𝒜) :
    (F.rightDerived n).map (lam.app X) = μ.app ((F.rightDerived n).obj X) := by
  let I := injectiveResolution X
  let φ := HomologicalComplex.homOfNatTrans lam I.cocomplex
  have hφ : (F.mapHomologicalComplex _).map φ =
      HomologicalComplex.homOfNatTrans μ ((F.mapHomologicalComplex _).obj I.cocomplex) := by
    ext k
    exact h _
  rw [← cancel_mono (I.isoRightDerivedObj F n).hom,
    InjectiveResolution.isoRightDerivedObj_hom_naturality (lam.app X) I I φ
      (lam.naturality (I.ι.f 0)) F n]
  dsimp only [Functor.comp_map]
  rw [hφ, HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_homOfNatTrans]
  exact μ.naturality (I.isoRightDerivedObj F n).hom

end Derived

end CategoryTheory
