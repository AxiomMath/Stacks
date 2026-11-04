module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedInfinitesimalFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedTangentFiniteDimensional
public import StacksFrontier.Deformation.Artin.Infinitesimal.FunctorDataComparison
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0D4S: deformation spaces of polarized schemes over a field are finite dimensional

Let `k` be a field and `x = (X → Spec k, ℒ)` an object of `𝒫olarized` over `Spec k`.

* (2) The tangent functor `T_x` and the functor `Inf_x` of Stacks 07Y9 exist — `𝒫olarized`
  satisfies (RS*) by Stacks 0D44 (`AlgebraicGeometry.satisfiesRSStar_polarizedSliceProjection`) —
  and `T_x(k)`, `Inf_x(k)` are finite dimensional: they inject linearly into the tangent space,
  respectively the degree-preserving derivations, of the graded algebra
  `P = k ⊕ ⨁_{d ≥ d₀} H^0(X, ℒ^{⊗ d})`, which are finite dimensional (Stacks 0DVZ).
* (1) If `k` is of finite type over the base, the deformation category `𝓕_{𝒳,k,x}` is a
  deformation category with finite-dimensional tangent space and infinitesimal automorphisms: by
  Stacks 0D18 these are `T_x(k)` and `Inf_x(k)`.

## Main results

* `PolarizedDeformation.finiteDimensional_tangentFunctor_infinitesimalAutomorphismFunctor`:
  **Stacks 0D4S (2)**.
* `PolarizedDeformation.isFiniteDimensionalDeformationCategory_predeformationCategory`:
  **Stacks 0D4S (1)**.

## References

* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
* [Stacks Project, Tag 0D18](https://stacks.math.columbia.edu/tag/0D18)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Deformation Deformation.Artin

universe u

@[expose] public noncomputable section

namespace AlgebraicGeometry.PolarizedDeformation

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **Stacks Project, Tag 0D4S, part (2).** Let `k` be a field and let `x = (X → Spec k, ℒ)` be an
object of `𝒫olarized` over `Spec k`. Then the tangent functor `T_x` and the functor of
infinitesimal automorphisms `Inf_x` of Stacks 07Y9 exist, and `T_x(k)` and `Inf_x(k)` are
finite-dimensional `k`-vector spaces.

Each functor is stated as a structure (`TangentFunctorData`,
`InfinitesimalAutomorphismFunctorData`) carrying a `k`-linear functor on the site modules together
with its identification with the isomorphism classes of lifts of `x`, respectively with the
infinitesimal automorphisms of the trivial lifts of `x`, natural in the module. The statement gives
that such a functor exists and that the value at `k` of every such functor is finite-dimensional.
No condition on `k` is assumed. -/
@[stacks 0D4S "(2): for a polarized proper scheme x over any field k, the functors T_x and Inf_x \
of Stacks 07Y9 exist (𝒫olarized satisfies RS* by 0D44) and T_x(k) and Inf_x(k) are finite \
dimensional; both finiteness statements hold for every k-linear functor carrying the \
identifications of 07Y9"]
theorem finiteDimensional_tangentFunctor_infinitesimalAutomorphismFunctor {k : Type u} [Field k]
    (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k))) (x : PolarizedFamily B)
    (hx : (polarizedSliceProjection B hS hT).obj x = algebraOver k B S hS toS hk) :
    (Nonempty (TangentFunctorData k B S hS toS hk (polarizedSliceProjection B hS hT) x hx) ∧
      ∀ T : TangentFunctorData k B S hS toS hk (polarizedSliceProjection B hS hT) x hx,
        FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) ∧
    (Nonempty (InfinitesimalAutomorphismFunctorData k B S hS toS hk
        (polarizedSliceProjection B hS hT) x hx
        (isFiberedInGroupoids_polarizedSliceProjection B hS hT)) ∧
      ∀ I : InfinitesimalAutomorphismFunctorData k B S hS toS hk
          (polarizedSliceProjection B hS hT) x hx
          (isFiberedInGroupoids_polarizedSliceProjection B hS hT),
        FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) :=
  ⟨⟨exists_tangentFunctor k B S hS toS hk _ x hx _
        (satisfiesRSStar_polarizedSliceProjection B hS hT),
      fun T => finiteDimensional_tangentFunctor_obj B hS hT toS hk x hx T⟩,
    ⟨exists_infinitesimalAutomorphismFunctor k B S hS toS hk _ x hx _
        (satisfiesRSStar_polarizedSliceProjection B hS hT),
      fun I => finiteDimensional_infinitesimalAutomorphismFunctor_obj B hS hT toS hk x hx I⟩⟩

attribute [local instance] PredeformationConstruction.category

/-- **Stacks Project, Tag 0D4S, part (1).** Let `k` be a field of finite type over the base (for
the base `Spec ℤ`: of finite type over `ℤ`), presented through `Spec k ⟶ Spec Λ ⟶ S`, and let
`x = (X → Spec k, ℒ)` be an object of `𝒫olarized` over `Spec k`. Then the predeformation category
`𝓕_{𝒳,k,x}` of Stacks 07T2 is a deformation category whose tangent space `T𝓕_{𝒳,k,x}` and whose
infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x})` (Stacks 07WY) are finite-dimensional `k`-vector
spaces.

The base is any scheme `S` which is terminal in the big fppf site; no condition is put on `Λ`
beyond the factorization. -/
@[stacks 0D4S "(1): for a field k of finite type over the base and a polarized proper scheme x \
over k, the deformation category F_{X,k,x} has finite dimensional tangent space T F_{X,k,x} and \
finite dimensional Inf(F_{X,k,x}); the base is any terminal scheme of the site, e.g. Spec Z"]
theorem isFiniteDimensionalDeformationCategory_predeformationCategory
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x : PolarizedFamily B)
    (hx₀ : (polarizedSliceProjection B hS hT ⋙ Over.post B.inclusion).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    IsFiniteDimensionalDeformationCategory
      (predeformationCategory iΛ (polarizedSliceProjection B hS hT ⋙ Over.post B.inclusion) x
        hx₀).projection := by
  have hp := isFiberedInGroupoids_polarizedSliceProjection B hS hT
  have hRS := satisfiesRSStar_polarizedSliceProjection B hS hT
  have hb : B.inclusion.obj ((polarizedSliceProjection B hS hT).obj x).left = Spec (.of k) :=
    congrArg Comma.left hx₀
  have hk : B.Contains (Spec (.of k)) :=
    hb ▸ ((polarizedSliceProjection B hS hT).obj x).left.property
  let toS := Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  have hx : (polarizedSliceProjection B hS hT).obj x = algebraOver k B S hS toS hk :=
    BigFppfOver.obj_injective_post_inclusion B S hS hx₀
  have hD := isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS _ hp hRS iΛ x
    hx₀ hfinite.1 hfinite.2
  refine ⟨hD, ?_, ?_⟩
  · let T := tangentFunctor k B S hS toS hk _ x hx hp hRS
    let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor (predeformationCategory iΛ
        (polarizedSliceProjection B hS hT ⋙ Over.post B.inclusion) x hx₀).projection).p) :=
      ⟨hD.predeformation⟩
    let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses (BasedCategory.ofFunctor (predeformationCategory iΛ
          (polarizedSliceProjection B hS hT ⋙ Over.post B.inclusion) x hx₀).projection)
          hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
    obtain ⟨e, -⟩ := tangentSpace_deformationCategory_linearEquiv_of_tangentFunctorData B S hS iΛ
      toS hk _ hp x hx₀ hx T hD
    have := finiteDimensional_tangentFunctor_obj B hS hT toS hk x hx T
    exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace _ hD.predeformation
      (tangentConditionS2 hD) e.symm.finiteDimensional
  · intro y hy PF
    let I := infinitesimalAutomorphismFunctor k B S hS toS hk _ x hx hp hRS
    obtain ⟨E⟩ := nonempty_linearEquiv_infinitesimalAutomorphismLinearLift B S hS iΛ toS hk _ hp x
      hx₀ hx I hD y hy PF (FGModuleCat.of k (ULift.{u} k))
    have := finiteDimensional_infinitesimalAutomorphismFunctor_obj B hS hT toS hk x hx I
    have : FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj
        (FGModuleCat.of k (ULift.{u} k)))) :=
      (I.functor.mapIso ((fgSiteModule B hk).mapIso
        fgModuleCatULiftSelfIso)).toLinearEquiv.symm.finiteDimensional
    exact E.symm.finiteDimensional

end AlgebraicGeometry.PolarizedDeformation

end
