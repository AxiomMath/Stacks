module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact

/-!
# The two coefficient functors of flat base change, and their exactness

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes and let `G` be a quasi-coherent `𝒪_{S'}`-module which is flat
over `S`. The base-change statement [Stacks, Tag 0GN5] compares two functors, one on the base
and one upstairs:

`Φ : M ↦ g^*M ⊗_{𝒪_{S'}} G` on `𝒪_S`-modules, and
`Ψ : F ↦ (g')^*F ⊗_{𝒪_{X'}} (f')^*G` on `𝒪_X`-modules.

Both are exact, and this is the observation on which the whole statement rests: `Φ` is exact
because `G` is flat over `S` ([Stacks, Tag 0GMU]), and `Ψ` is exact by the same criterion
applied to `g'`, because `(f')^*G` is flat over `X` — flatness of a quasi-coherent module over
the base is stable under base change ([Stacks, Tag 01U8]).

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseCoefficients`: the functor `Φ`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.totalCoefficients`: the functor `Ψ`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isFlatOver_pullbackCoefficients`: `(f')^*G` is
  flat over `X` along `g'`, for a cartesian square and a quasi-coherent `G` flat over `S`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.exact_baseCoefficients` and
  `Stacks.AlgebraicGeometry.ModuleBaseChange.exact_totalCoefficients`: **both coefficient
  functors are exact.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.preservesFiniteLimits_baseCoefficients`,
  `preservesFiniteColimits_baseCoefficients`,
  `preservesFiniteLimits_totalCoefficients`,
  `preservesFiniteColimits_totalCoefficients`: the two halves of exactness, in the form the
  right-derived-functor machinery consumes.

## Implementation notes

The tensor product is the one of [Stacks, Tag 01CB], the sheafification of the sectionwise
tensor product; the two coefficient functors are *defined* as instances of
`Stacks.SheafOfModules.pullbackTensorFunctor`, so that the exactness theorem of
[Stacks, Tag 0GMU] applies to them with no transport. Writing the fixed tensor factor on the
right is what that theorem's shape dictates; the tensor product of sheaves of modules is
symmetric, so this is a choice of spelling and not of mathematical content.

Everything is written over `SheafOfModules (structureSheafRing _)` and with the inverse and
direct images `RingedSpaceModuleAdjunction.modulePullback` and `modulePushforward`, rather than
over `AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.Scheme.Modules.pullback`. The
two are definitionally equal, but `AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own
`Category` instance with `Hom := AlgebraicGeometry.Scheme.Modules.Hom`, and a goal mixing the
two spellings is not type-correct at reducible transparency, which disables `rw` and `simp` on
it; the tensor product and the projection formula are stated over the first spelling, so that is
the one used throughout.

Flatness of `(f')^*G` over `X` is [Stacks, Tag 01U8] applied to the *transpose* of the given
cartesian square: `AlgebraicGeometry.modulePullback_isFlatOver` pulls a module flat over the
base of a cartesian square back along the other horizontal morphism, and reading the square
`IsPullback g' f' f g` as `IsPullback f' g' g f` turns "`G` is flat over `S` along `g`" into
"`(f')^*G` is flat over `X` along `g'`".

Exactness is Mathlib's `CategoryTheory.exactFunctor`; the two preservation statements are its
components, extracted by `CategoryTheory.exactFunctor_iff`. They are theorems rather than
instances because they depend on the flatness hypothesis, which is not a class.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-! ### The two functors -/

/-- **The coefficient functor on the base**, `Φ : M ↦ g^*M ⊗_{𝒪_{S'}} G`. -/
def baseCoefficients (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing S.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing S'.toRingedSpace) :=
  Stacks.SheafOfModules.pullbackTensorFunctor g.toLRSHom.toShHom G

/-- **The coefficient functor upstairs**, `Ψ : F ↦ (g')^*F ⊗_{𝒪_{X'}} (f')^*G`. -/
def totalCoefficients (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing X'.toRingedSpace) :=
  Stacks.SheafOfModules.pullbackTensorFunctor g'.toLRSHom.toShHom
    ((modulePullback f'.toLRSHom.toShHom).obj G)

/-- `Φ` is the inverse image along `g` followed by tensoring with `G`. -/
theorem baseCoefficients_eq (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    baseCoefficients g G =
      modulePullback g.toLRSHom.toShHom ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨S'.toRingedSpace.presheaf, S'.toRingedSpace.IsSheaf⟩).flip.obj G :=
  rfl

/-- `Ψ` is the inverse image along `g'` followed by tensoring with `(f')^*G`. -/
theorem totalCoefficients_eq (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    totalCoefficients g' f' G =
      modulePullback g'.toLRSHom.toShHom ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).flip.obj
            ((modulePullback f'.toLRSHom.toShHom).obj G) :=
  rfl

/-- `Φ` sends `M` to the [Stacks, Tag 01CB] tensor product of `g^*M` with `G`. -/
theorem baseCoefficients_obj (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (baseCoefficients g G).obj M =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S'.toRingedSpace)).presheaf, ((S'.toRingedSpace)).IsSheaf⟩).obj
          (((modulePullback g.toLRSHom.toShHom).obj M))).obj (G)) :=
  rfl

/-- `Ψ` sends `F` to the [Stacks, Tag 01CB] tensor product of `(g')^*F` with `(f')^*G`. -/
theorem totalCoefficients_obj (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (totalCoefficients g' f' G).obj F =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X'.toRingedSpace)).presheaf, ((X'.toRingedSpace)).IsSheaf⟩).obj
          (((modulePullback g'.toLRSHom.toShHom).obj F))).obj
            (((modulePullback f'.toLRSHom.toShHom).obj G))) :=
  rfl

/-- A natural transformation `T.map f` at `Z` is `T` uncurried applied to `(f, 𝟙 Z)`. -/
private theorem app_map_eq_uncurry_map {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) {X Y : C} (f : X ⟶ Y) (Z : D) :
    (T.map f).app Z = (Functor.uncurry.obj T).map ((f, 𝟙 Z) : (X, Z) ⟶ (Y, Z)) := by
  simp

/-- `Φ` sends `φ` to the tensor product of `g^*φ` with the identity of `G`. -/
theorem baseCoefficients_map (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    {M N : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (φ : M ⟶ N) :
    (baseCoefficients g G).map φ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((S'.toRingedSpace)).presheaf, ((S'.toRingedSpace)).IsSheaf⟩)).map
          ((((modulePullback g.toLRSHom.toShHom).map φ), (𝟙 G)) : (_, _) ⟶ (_, _))) := by
  exact app_map_eq_uncurry_map (Stacks.SheafOfModules.Tensor.sheafTensor _) _ _

/-- `Ψ` sends `φ` to the tensor product of `(g')^*φ` with the identity of `(f')^*G`. -/
theorem totalCoefficients_map (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    {F F' : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (φ : F ⟶ F') :
    (totalCoefficients g' f' G).map φ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X'.toRingedSpace)).presheaf, ((X'.toRingedSpace)).IsSheaf⟩)).map
          ((((modulePullback g'.toLRSHom.toShHom).map φ),
            (𝟙 ((modulePullback f'.toLRSHom.toShHom).obj G))) : (_, _) ⟶ (_, _))) := by
  exact app_map_eq_uncurry_map (Stacks.SheafOfModules.Tensor.sheafTensor _) _ _

/-- The coefficient functor `Φ` is additive. -/
instance additive_baseCoefficients (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (baseCoefficients g G).Additive :=
  Stacks.SheafOfModules.additive_pullbackTensorFunctor g.toLRSHom.toShHom G

/-- The coefficient functor `Ψ` is additive. -/
instance additive_totalCoefficients (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (totalCoefficients g' f' G).Additive :=
  Stacks.SheafOfModules.additive_pullbackTensorFunctor g'.toLRSHom.toShHom _

/-- The coefficient functor `Φ` preserves zero morphisms. -/
instance preservesZeroMorphisms_baseCoefficients (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (baseCoefficients g G).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The coefficient functor `Ψ` preserves zero morphisms. -/
instance preservesZeroMorphisms_totalCoefficients (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (totalCoefficients g' f' G).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-! ### Flatness of the coefficient module upstairs -/

/-- **The pullback of the coefficient module to `X'` is flat over `X`.**  Flatness of a
quasi-coherent module over the base is stable under base change ([Stacks, Tag 01U8]); applying
that to the transpose of the cartesian square turns flatness of `G` over `S` along `g` into
flatness of `(f')^*G` over `X` along `g'`. -/
theorem isFlatOver_pullbackCoefficients {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    AlgebraicGeometry.IsFlatOver g'.toLRSHom.toShHom
      ((modulePullback f'.toLRSHom.toShHom).obj G) :=
  AlgebraicGeometry.modulePullback_isFlatOver H.flip G hG

/-! ### Exactness -/

/-- **The coefficient functor on the base is exact.**  This is [Stacks, Tag 0GMU] for the
morphism `g` and the module `G`, whose flatness over `S` is the hypothesis of
[Stacks, Tag 0GN5]. -/
theorem exact_baseCoefficients (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    exactFunctor (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (baseCoefficients g G) :=
  Stacks.SheafOfModules.pullbackTensorFunctor_exact g.toLRSHom.toShHom G hG

/-- **The coefficient functor upstairs is exact.**  This is [Stacks, Tag 0GMU] for the morphism
`g'` and the module `(f')^*G`, whose flatness over `X` is
`isFlatOver_pullbackCoefficients`. -/
theorem exact_totalCoefficients {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    exactFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) (totalCoefficients g' f' G) :=
  Stacks.SheafOfModules.pullbackTensorFunctor_exact g'.toLRSHom.toShHom _
    (isFlatOver_pullbackCoefficients H G hG)

/-- If `G` is flat over `S`, then the coefficient functor `Φ` preserves finite limits. -/
theorem preservesFiniteLimits_baseCoefficients (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    PreservesFiniteLimits (baseCoefficients g G) :=
  ((exactFunctor_iff (baseCoefficients g G)).1 (exact_baseCoefficients g G hG)).1

/-- If `G` is flat over `S`, then the coefficient functor `Φ` preserves finite colimits. -/
theorem preservesFiniteColimits_baseCoefficients (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    PreservesFiniteColimits (baseCoefficients g G) :=
  ((exactFunctor_iff (baseCoefficients g G)).1 (exact_baseCoefficients g G hG)).2

/-- If `G` is flat over `S`, then the coefficient functor `Ψ` preserves finite limits. -/
theorem preservesFiniteLimits_totalCoefficients {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    PreservesFiniteLimits (totalCoefficients g' f' G) :=
  ((exactFunctor_iff (totalCoefficients g' f' G)).1 (exact_totalCoefficients H G hG)).1

/-- If `G` is flat over `S`, then the coefficient functor `Ψ` preserves finite colimits. -/
theorem preservesFiniteColimits_totalCoefficients {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    PreservesFiniteColimits (totalCoefficients g' f' G) :=
  ((exactFunctor_iff (totalCoefficients g' f' G)).1 (exact_totalCoefficients H G hG)).2

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
