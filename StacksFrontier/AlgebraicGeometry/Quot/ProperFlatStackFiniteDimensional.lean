module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesRSStar
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0D1K: deformation spaces of `Spaces'_{fp, flat, proper}` are finite dimensional

Let `k` be a field and let `x = (X → Spec k)` be an object of
`𝒳 = Spaces'_{fp, flat, proper}` over `Spec k`, the stack being formed over the big fppf site of
`Spec ℤ`.

* (1) If `k` is of finite type over `ℤ`, the predeformation category `𝓕_{𝒳,k,x}` over `𝒞_ℤ` is a
  deformation category, and the vector spaces `T𝓕_{𝒳,k,x}` and `Inf(𝓕_{𝒳,k,x})` of Stacks 07WY
  are finite dimensional. Over `𝒞_ℤ`, `𝓕_{𝒳,k,x}` is equivalent to the deformation category of
  the algebraic space `X` over `k`
  (`AlgebraicGeometry.ProperFlatSpaceDeformation.toSpaceDeformationFunctor`), and its tangent space
  and infinitesimal automorphisms embed in `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` and
  `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` (Stacks 0D17, 0E41).
* (2) For every field `k`, the functors `T_x` and `Inf_x` of Stacks 07Y9 exist, `𝒳` satisfying
  (RS*) by Stacks 0D1J (`AlgebraicGeometry.satisfiesRSStar_cartesianProperFlatProjection`), and
  `T_x(k)` and `Inf_x(k)` are finite dimensional: by Stacks 0D18 they are the tangent space and the
  infinitesimal automorphisms of `𝓕_{𝒳,k,x}` over `𝒞_ℤ`.

## Main results

* `ProperFlatSpaceDeformation.finiteDimensional_predeformationCategory`: for `k` of finite type
  over `ℤ`, `𝓕_{𝒳,k,x}` is a deformation category with finite-dimensional tangent space and
  infinitesimal automorphisms.
* `ProperFlatSpaceDeformation.finiteDimensional_tangentFunctor_infinitesimalAutomorphismFunctor`:
  for every field `k`, the functors `T_x` and `Inf_x` exist and `T_x(k)`, `Inf_x(k)` are finite
  dimensional.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
* [Stacks Project, Tag 07Y6](https://stacks.math.columbia.edu/tag/07Y6)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] PredeformationConstruction.category in
/-- Let `k` be a field of finite type over `ℤ` and let `x = (X → Spec k)` be an object of
`𝒳 = Spaces'_{fp, flat, proper}` over `Spec k`. Then the predeformation category `𝓕_{𝒳,k,x}` of
Stacks 07T2, over `𝒞_ℤ`, is a deformation category, its tangent space `T𝓕_{𝒳,k,x}` is a
finite-dimensional `k`-vector space, and so are its infinitesimal automorphisms
`Inf(𝓕_{𝒳,k,x})` (Stacks 07WY), at every object of the special fibre and for every choice of its
pushforwards.

The stack is formed over the big fppf site of `Spec ℤ`, and `𝓕_{𝒳,k,x}` over `𝒞_Λ` with `Λ = ℤ`,
`Spec Λ = Spec ℤ` the affine open of the base containing the image of `Spec k` (Stacks 07T2). -/
@[stacks 0D1K "(1): for a field k of finite type over Z and an object x of Spaces'_{fp,flat,proper} \
over Spec k, the predeformation category F_{X,k,x} over C_Z is a deformation category whose \
tangent space T F_{X,k,x} and infinitesimal automorphisms Inf(F_{X,k,x}) (Section 07WY) are \
finite dimensional"]
theorem finiteDimensional_predeformationCategory {k : Type u} [Field k]
    [Algebra (ULift.{u} ℤ) k] [Algebra.FiniteType (ULift.{u} ℤ) k]
    (x : CartesianProperFlatSpaces B integerBase hZ)
    (hx : (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) ≫ 𝟙 integerBase)) :
    ∃ hD : IsDeformationCategory.{u, u, u} (predeformationCategory (𝟙 integerBase)
        (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion) x hx).projection,
      (letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor (predeformationCategory
          (𝟙 integerBase) (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion)
            x hx).projection).p) := ⟨hD.predeformation⟩;
        letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
          (isomorphismClasses (BasedCategory.ofFunctor (predeformationCategory (𝟙 integerBase)
            (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion) x
              hx).projection) hD.predeformation.cofibered))) := ⟨tangentConditionS2.{u, u, u} hD⟩;
        FiniteDimensional k (artinianTangentSpace (ULift.{u} ℤ) k
          (isomorphismClasses (BasedCategory.ofFunctor (predeformationCategory (𝟙 integerBase)
            (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion) x
              hx).projection) hD.predeformation.cofibered))) ∧
      ∀ y, (predeformationCategory (𝟙 integerBase)
          (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion) x
            hx).projection.obj y = residueFieldObject.{u, u, u} (ULift.{u} ℤ) k →
        ∀ PF : ChosenPushforwardsAt (predeformationCategory (𝟙 integerBase)
            (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion) x
              hx).projection y,
          FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} PF
            hD.satisfiesRS).functor.obj (FGModuleCat.of k (ULift.{u} k))) :=
  ⟨isDeformationCategory_predeformation x hx, finiteDimensional_tangentSpace x hx,
    fun y hy PF => finiteDimensional_infinitesimalAutomorphisms x hx y hy PF⟩

/-- Let `k` be a field and let `x = (X → Spec k)` be an object of
`𝒳 = Spaces'_{fp, flat, proper}` over `Spec k`. Then the tangent functor `T_x` and the functor of
infinitesimal automorphisms `Inf_x` of Stacks 07Y9 (Section 07Y6) exist — `𝒳` satisfies (RS*) by
Stacks 0D1J — and `T_x(k)` and `Inf_x(k)` are finite-dimensional `k`-vector spaces.

Each functor is stated as a structure (`TangentFunctorData`,
`InfinitesimalAutomorphismFunctorData`) carrying a `k`-linear functor on the site modules together
with its identification with the isomorphism classes of lifts of `x`, respectively with the
infinitesimal automorphisms of the trivial lifts of `x`, natural in the module. The statement gives
that such a functor exists and that the value at `k` of *every* such functor is finite-dimensional,
so it holds for the functors `T_x` and `Inf_x` of Stacks 07Y9, which are determined by these
identifications. No condition on `k` is assumed. -/
@[stacks 0D1K "(2): for an object x of Spaces'_{fp,flat,proper} over a field k, the functors T_x \
and Inf_x of Stacks 07Y9 exist (the stack satisfies RS* by 0D1J) and T_x(k) and Inf_x(k) are \
finite dimensional; both finiteness statements hold for every k-linear functor carrying the \
identifications of 07Y9"]
theorem finiteDimensional_tangentFunctor_infinitesimalAutomorphismFunctor {k : Type u} [Field k]
    (toS : Spec (.of k) ⟶ integerBase) (hk : B.Contains (Spec (.of k)))
    (x : CartesianProperFlatSpaces B integerBase hZ)
    (hx : (cartesianProperFlatProjection B integerBase hZ).obj x =
      algebraOver k B integerBase hZ toS hk) :
    (Nonempty (TangentFunctorData k B integerBase hZ toS hk
        (cartesianProperFlatProjection B integerBase hZ) x hx) ∧
      ∀ T : TangentFunctorData k B integerBase hZ toS hk
          (cartesianProperFlatProjection B integerBase hZ) x hx,
        FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) ∧
    (Nonempty (InfinitesimalAutomorphismFunctorData k B integerBase hZ toS hk
        (cartesianProperFlatProjection B integerBase hZ) x hx
        (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ)) ∧
      ∀ I : InfinitesimalAutomorphismFunctorData k B integerBase hZ toS hk
          (cartesianProperFlatProjection B integerBase hZ) x hx
          (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ),
        FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) :=
  ⟨⟨exists_tangentFunctor k B integerBase hZ toS hk _ x hx _
      (satisfiesRSStar_cartesianProperFlatProjection B integerBase hZ),
      finiteDimensional_tangentFunctorData_obj toS hk x hx⟩,
    ⟨exists_infinitesimalAutomorphismFunctor k B integerBase hZ toS hk _ x hx _
        (satisfiesRSStar_cartesianProperFlatProjection B integerBase hZ),
      finiteDimensional_infinitesimalAutomorphismFunctorData_obj toS hk x hx⟩⟩

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
