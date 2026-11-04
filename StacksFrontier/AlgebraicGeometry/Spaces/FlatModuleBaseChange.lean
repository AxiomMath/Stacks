module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChangeAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence

/-!
# Stacks 05VW: relative flatness of a module under base change and descent

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site, let `F` be a
quasi-coherent `𝒪_X`-module and let `F' = (g')^* F` be its pullback.  Stacks 05VW says, for a
geometric point `x̄'` of `X'` with image `x̄` in `X`:

1. if `F` is flat over `Y` at `x̄`, then `F'` is flat over `Y'` at `x̄'`;
2. conversely, if `g` is flat at the image `ȳ'` of `x̄'` in `Y'` and `F'` is flat over `Y'` at
   `x̄'`, then `F` is flat over `Y` at `x̄`;

and consequently, if `F` is flat over `Y` then `F'` is flat over `Y'`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`: part (1).
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback`: part (2).
* `AlgebraicGeometry.Space.isFlatOver_modulePullback`: the final assertion.
* `AlgebraicGeometry.Space.isFlatOver_modulePullback_of_hasLocalInverseImagePresentations`: the
  final assertion with quasi-coherence of the pullback supplied by Stacks 03GA.

## Implementation notes

Flatness of a module over the target at a point is read at geometric points, as condition (2) of
Stacks 05VU: `AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint` is flatness of the geometric
stalk `F_{x̄}` over the étale local ring `𝒪_{Y, ȳ}`.  That is the form in which the source's
reduction to commutative algebra is available here, and by
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint` it assembles to the
chartwise flatness of Stacks 05VV for a quasi-coherent module, which is how the final assertion
is obtained.

Both parts rest on the base-change formula for the geometric stalk of a pullback,
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso` of Stacks 05VQ:
`F'_{x̄'} = 𝒪_{X', x̄'} ⊗_{𝒪_{X, x̄}} F_{x̄}`.  Writing `R`, `A`, `R'`, `A'` for the étale local
rings of `Y`, `X`, `Y'`, `X'` at the four points, and `P = A ⊗_R R'`, the two parts are then:

1. `A'` is flat over `P` (`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`), so
   `A' ⊗_A F_{x̄}` is flat over `R'` whenever `F_{x̄}` is flat over `R`, which is
   `Module.Flat.tensorProduct_of_isPushout`;
2. flatness of `g` at `ȳ'` makes `R'` flat over `R`, hence `P` flat over `A` and so `A'` flat
   over `A`; as `A → A'` is a local homomorphism of local rings it is then faithfully flat, and
   flatness of `A' ⊗_A F_{x̄}` over `R` descends to flatness of `F_{x̄}` over `R` by
   Stacks 0584 (2).  What provides flatness of `A' ⊗_A F_{x̄}` over `R` is part (1) of
   Stacks 05VX, `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_comp`, applied to
   `f' ≫ g = g' ≫ f`.

The final assertion asks for quasi-coherence of the pullback `F'` as well as of `F`: it is the
pointwise condition at every geometric point of `X'` that part (1) delivers, and Stacks 05VU
turns that into chartwise flatness only for a quasi-coherent module.  Quasi-coherence of a
pullback is Stacks 03GA, which holds along an arbitrary morphism of algebraic spaces by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`.  The
last result below derives the instance instead from the narrower
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback`, whose binder `hg'` is
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations`; that binder is now redundant, the
unconditional form of 03GA supplying the instance from quasi-coherence of `F` alone.

## References

* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VX](https://stacks.math.columbia.edu/tag/05VX)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Flatness of a ring homomorphism is unchanged by transporting its source along an equality of
rings. -/
private theorem flat_eqToHom_comp {R₁ R₂ A : CommRingCat.{u + 1}} (hR : R₁ = R₂) (ψ : R₂ →+* A)
    (hψ : ψ.Flat) : ((eqToHom hR ≫ CommRingCat.ofHom ψ).hom).Flat := by
  subst hR
  simpa using hψ

/-- **Stacks 05VW, part (1).**  In a cartesian square of algebraic spaces

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

let `x̄'` be a geometric point of `X'` and let `F` be an `𝒪_X`-module flat over `Y` at the image
`x̄` of `x̄'`.  Then the pullback `(g')^* F` is flat over `Y'` at `x̄'`.

At the geometric stalks this is base change of flatness over a pushout of rings: the stalk of
`(g')^* F` at `x̄'` is `𝒪_{X', x̄'} ⊗_{𝒪_{X, x̄}} F_{x̄}` by Stacks 05VQ, and `𝒪_{X', x̄'}` is flat
over `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}`, so flatness of `F_{x̄}` over `𝒪_{Y, ȳ}` passes to
flatness of the base change over `𝒪_{Y', ȳ'}`. -/
@[stacks 05VW "part (1): the pullback of a module flat over the target at a point is flat over
  the new target at every point above it"]
theorem isFlatOverAtGeometricPoint_modulePullback
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    (x' : GeometricPoint B S hS X'.1)
    (hF : IsFlatOverAtGeometricPoint B S hS f F (geometricPointMap g'.hom x')) :
    IsFlatOverAtGeometricPoint B S hS f' ((modulePullback B S hS g').obj F) x' := by
  have h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫ CommRingCat.ofHom
      (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ :=
    cartesian_etaleStalk_tensor_flat B S hS g' f' f g hpb x'
  let T := TensorProduct
    ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
    ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
  let : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
    Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra T ↥(etaleLocalRing B S hS X'.1 x') := φ.toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 g'.hom x').toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 f'.hom x').toAlgebra
  let : IsScalarTower ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) T
      ↥(etaleLocalRing B S hS X'.1 x') := IsScalarTower.of_algebraMap_eq' hleft.symm
  let : IsScalarTower ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T
      ↥(etaleLocalRing B S hS X'.1 x') := IsScalarTower.of_algebraMap_eq' hright.symm
  let : Algebra.IsPushout
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) T :=
    TensorProduct.isPushout.symm
  have : Module.Flat T ↥(etaleLocalRing B S hS X'.1 x') := hflat
  let : Module
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x'))
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F) := hF
  have key := Module.Flat.tensorProduct_of_isPushout
    ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
    ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) T
    ↥(etaleLocalRing B S hS X'.1 x')
    ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F)
  exact (ModuleCat.flat_iff_of_iso (etaleLocalRingMap X'.2 f'.hom x')
    (geometricModuleStalkPullbackIso B S hS g' x' F)).mpr
      ((ModuleCat.flat_extendScalars_obj_iff _ _ _).mpr key)

/-- **Stacks 05VW, part (2).**  In a cartesian square of algebraic spaces

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

let `x̄'` be a geometric point of `X'`, let `F` be an `𝒪_X`-module and suppose that `g` is flat
at the image `ȳ'` of `x̄'` in `Y'`.  If the pullback `(g')^* F` is flat over `Y'` at `x̄'`, then
`F` is flat over `Y` at the image `x̄` of `x̄'`.

Flatness of `g` at `ȳ'` makes `(g')^* F` flat over `Y` at `x̄'` by Stacks 05VX, part (1); over
the étale local rings that reads as flatness of `𝒪_{X', x̄'} ⊗_{𝒪_{X, x̄}} F_{x̄}` over
`𝒪_{Y, ȳ}` through Stacks 05VQ.  The same flatness of `g` makes `𝒪_{X, x̄} → 𝒪_{X', x̄'}` flat,
and it is a local homomorphism of local rings, hence faithfully flat; so flatness of `F_{x̄}`
over `𝒪_{Y, ȳ}` follows by Stacks 0584 (2). -/
@[stacks 05VW "part (2): relative flatness of a module at a point descends along a base change
  flat at the image point"]
theorem isFlatOverAtGeometricPoint_of_modulePullback
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    (x' : GeometricPoint B S hS X'.1)
    (hg : IsFlatAt B S hS g.hom (geometricPointMap f'.hom x').image)
    (hF : IsFlatOverAtGeometricPoint B S hS f' ((modulePullback B S hS g').obj F) x') :
    IsFlatOverAtGeometricPoint B S hS f F (geometricPointMap g'.hom x') := by
  have h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w
  have hcomp := isFlatOverAtGeometricPoint_comp B S hS f' g
    ((modulePullback B S hS g').obj F) x' hF hg
  have hcomp' : IsFlatOverAtGeometricPoint B S hS (g' ≫ f)
      ((modulePullback B S hS g').obj F) x' := by
    rw [hpb.w]; exact hcomp
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫ CommRingCat.ofHom
      (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ :=
    cartesian_etaleStalk_tensor_flat B S hS g' f' f g hpb x'
  have : Module.Flat
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
    flat_eqToHom_comp (congrArg (etaleLocalRing B S hS Y.1) h) _
      ((isFlatAt_iff_etaleLocalRingMap_flat Y'.2 Y.2 g.hom
        (geometricPointMap f'.hom x')).mp hg)
  let T := TensorProduct
    ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
    ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
    ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
  let : Algebra T ↥(etaleLocalRing B S hS X'.1 x') := φ.toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 g'.hom x').toAlgebra
  let : IsScalarTower ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) T
      ↥(etaleLocalRing B S hS X'.1 x') := IsScalarTower.of_algebraMap_eq' hleft.symm
  have : Module.Flat T ↥(etaleLocalRing B S hS X'.1 x') := hflat
  have : Module.Flat ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) T :=
    Module.Flat.baseChange _ _ _
  have : Module.Flat ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := Module.Flat.trans _ T _
  let : IsLocalRing ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 _
  let : IsLocalRing ↥(etaleLocalRing B S hS X'.1 x') :=
    isLocalRing_etaleLocalRing B S hS X'.1 X'.2 x'
  have : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x')) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact isLocalHom_etaleLocalRingMap B S hS X'.2 X.2 g'.hom x'
  have : Module.FaithfullyFlat ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X'.1 x') :=
    (etaleLocalRingMap X'.2 (g' ≫ f).hom x').toAlgebra
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') :=
    IsScalarTower.of_algebraMap_eq' (etaleLocalRingMap_comp X'.2 X.2 g'.hom f.hom x').symm
  let : Module
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x'))
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have key := (ModuleCat.flat_extendScalars_obj_iff (etaleLocalRingMap X'.2 g'.hom x')
    (etaleLocalRingMap X'.2 (g' ≫ f).hom x')
    (geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F)).mp
      ((ModuleCat.flat_iff_of_iso (etaleLocalRingMap X'.2 (g' ≫ f).hom x')
        (geometricModuleStalkPullbackIso B S hS g' x' F)).mp hcomp')
  exact Module.Flat.tensorProduct_iff_of_faithfullyFlat.mp key

/-- **Stacks 05VW, the final assertion.**  In a cartesian square of algebraic spaces

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

the pullback of a quasi-coherent `𝒪_X`-module flat over `Y` is flat over `Y'`.

Chartwise flatness of Stacks 05VV is flatness of the geometric stalks over the étale local rings
of the base at every geometric point, by Stacks 05VU, and that pointwise condition is carried by
the base change at each geometric point of `X'`. -/
@[stacks 05VW "the final assertion: the pullback of a quasi-coherent module flat over the target
  is flat over the new target"]
theorem isFlatOver_modulePullback {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hpb : IsPullback g' f' f g)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [((modulePullback B S hS g').obj F).IsQuasicoherentOnSite]
    (hF : IsFlatOver B S hS X.2 f.hom F) :
    IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) :=
  (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f'
      ((modulePullback B S hS g').obj F)).mpr fun x' =>
    isFlatOverAtGeometricPoint_modulePullback B S hS hpb F x'
      ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f F).mp hF _)

/-- **Stacks 05VW, the final assertion**, with quasi-coherence of the pullback deduced from
Stacks 03GA: in a cartesian square of algebraic spaces whose upper horizontal morphism has local
inverse-image presentations, the pullback of a quasi-coherent `𝒪_X`-module flat over `Y` is flat
over `Y'`. -/
theorem isFlatOver_modulePullback_of_hasLocalInverseImagePresentations
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (hg' : HasLocalInverseImagePresentations B S hS g')
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (hF : IsFlatOver B S hS X.2 f.hom F) :
    IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) :=
  have := hqc
  have := isQuasicoherentOnSite_modulePullback B S hS g' hg' F hqc
  isFlatOver_modulePullback B S hS hpb F hF

end AlgebraicGeometry.Space

end
