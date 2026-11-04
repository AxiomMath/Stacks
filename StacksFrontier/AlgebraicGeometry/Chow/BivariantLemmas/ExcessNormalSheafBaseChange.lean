module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap

/-!
# The excess normal sheaf under base change

Let `i : Z ⟶ X` be an immersion of schemes and `𝒩` a virtual normal sheaf for it, with surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` (Stacks 0FBQ). Its *excess normal sheaf* is `ℰ = (ker σ)^∨`
(`Stacks.Chow.VirtualNormalBundle.excessNormalSheaf`). For a cartesian square

```
Z' --i'--→ X'
|          |
g          f
↓          ↓
Z  --i---→ X
```

the pullback `g^*𝒩` is a virtual normal sheaf for `i'` (Stacks 0FBJ), whose surjection is the
dual base-change isomorphism, followed by `g^*σ` and by the surjection
`g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 0473. This file proves two facts about the excess normal
sheaves of these base changes.

First, base change is transitive up to isomorphism on excess normal sheaves: for two stacked
cartesian squares, the excess normal sheaf of the base change along the second square of the base
change along the first is the excess normal sheaf of the base change along the composite square.
Only the kernels of the surjections enter, and these see the surjections only up to isomorphisms
of their sources; the maps of conormal sheaves compose by Stacks 04G2.

Second, along an open immersion `f : X' ⟶ X` the excess normal sheaf of `g^*𝒩` is the pullback
`g^*ℰ`: the map `g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` is an isomorphism (Stacks 0473, flat base change),
pullback along the open immersion `g` is exact, and it commutes with duals of finite locally free
modules (Stacks 0GMX).

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.excessNormalSheafBaseChangeCompIso` — the excess normal sheaf
  of an iterated base change is that of the base change along the composite square.
* `Stacks.Chow.VirtualNormalBundle.excessNormalSheafBaseChangeOpenIso` — along an open
  immersion, the excess normal sheaf of the base change is the pullback of the excess normal
  sheaf.

## Main results

* `Stacks.Chow.pullback_map_comp_immersionConormalSheafMap_comp` — the pullback of a map into a
  conormal sheaf, followed by the conormal map of a composite square, factors through the
  conormal maps of the two squares (Stacks 04G2).
* `Stacks.Chow.VirtualNormalBundle.baseChange_congr` — the base change only depends on the two
  edges of the square.

## References

* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### Kernels of the surjections of iterated base changes -/

section Composite

variable {Z₁ Z₂ Z₃ X₁ X₂ X₃ : Scheme.{u}} {i₁ : Z₁ ⟶ X₁} {i₂ : Z₂ ⟶ X₂} {i₃ : Z₃ ⟶ X₃}
  [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃] {f₁ : Z₁ ⟶ Z₂} {g₁ : X₁ ⟶ X₂}
  {f₂ : Z₂ ⟶ Z₃} {g₂ : X₂ ⟶ X₃}

/-- **The conormal map of a composite square, after a pullback.** For two stacked commutative
squares of immersions and a map `σ : M ⟶ 𝒞_{Z₃/X₃}`, the pullback of `σ` along `f₁ ≫ f₂` followed
by the conormal map of the composite square is, up to the identification
`(f₁ ≫ f₂)^* ≅ f₁^* f₂^*`, the pullback along `f₁` of the pullback of `σ` along `f₂` followed by
the conormal map of the lower square, followed by the conormal map of the upper square. This is
the composition law of Stacks 04G2 and the naturality of the identification. -/
theorem pullback_map_comp_immersionConormalSheafMap_comp (comm₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    (comm₂ : i₂ ≫ g₂ = f₂ ≫ i₃) {M : Z₃.Modules}
    (σ : M ⟶ Stacks.Thickenings.immersionConormalSheaf i₃) :
    (modulePullback (f₁ ≫ f₂).toLRSHom.toShHom).map σ ≫
        Stacks.Immersion.immersionConormalSheafMap i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂)
          (Stacks.Immersion.toShHom_square (Stacks.Immersion.square_comp comm₁ comm₂)) =
      (modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app M ≫
        (modulePullback f₁.toLRSHom.toShHom).map
          ((modulePullback f₂.toLRSHom.toShHom).map σ ≫
            Stacks.Immersion.immersionConormalSheafMap i₂ i₃ f₂ g₂
              (Stacks.Immersion.toShHom_square comm₂)) ≫
          Stacks.Immersion.immersionConormalSheafMap i₁ i₂ f₁ g₁
            (Stacks.Immersion.toShHom_square comm₁) := by
  rw [Stacks.Immersion.immersionConormalSheafMap_comp i₁ i₂ i₃ f₁ g₁ comm₁ f₂ g₂ comm₂,
    Functor.map_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans
    (((modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.naturality σ =≫ _).trans
      (Category.assoc _ _ _))

/-- **The kernel of the surjection of an iterated base change.** For a virtual normal sheaf `𝒩`
of `i₃` and two stacked cartesian squares, the kernel of the surjection of the base change along
the upper square of the base change along the lower square is the kernel of the surjection of the
base change along the composite square. The two surjections differ by an isomorphism of their
sources, by `Stacks.Chow.pullback_map_comp_immersionConormalSheafMap_comp`. -/
def VirtualNormalBundle.kernelBaseChangeCompIso (N : VirtualNormalBundle i₃)
    (sq₂ : IsPullback i₂ f₂ g₂ i₃) (sq₁ : IsPullback i₁ f₁ g₁ i₂) :
    kernel ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).conormalSurjection ≅
      kernel (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).conormalSurjection :=
  let W : @Quiver.Hom Z₁.Modules _ ((modulePullback f₁.toLRSHom.toShHom).obj
      ((modulePullback f₂.toLRSHom.toShHom).obj (dualSheaf N.bundle))) (conormalModule i₁) :=
    (modulePullback f₁.toLRSHom.toShHom).map
      ((modulePullback f₂.toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i₂ i₃ f₂ g₂
          (Stacks.Immersion.toShHom_square sq₂.w)) ≫
    Stacks.Immersion.immersionConormalSheafMap i₁ i₂ f₁ g₁
      (Stacks.Immersion.toShHom_square sq₁.w)
  let P₂ := @asIso _ _ _ _ (pullbackDualMap f₂ N.bundle)
    (pullbackDualMap_isIso f₂ N.bundle N.isFiniteLocallyFree)
  let P₁ := @asIso _ _ _ _ (pullbackDualMap f₁ (N.baseChange i₃ i₂ f₂ g₂ sq₂).bundle)
    (pullbackDualMap_isIso f₁ _ (N.baseChange i₃ i₂ f₂ g₂ sq₂).isFiniteLocallyFree)
  let P := @asIso _ _ _ _ (pullbackDualMap (f₁ ≫ f₂) N.bundle)
    (pullbackDualMap_isIso (f₁ ≫ f₂) N.bundle N.isFiniteLocallyFree)
  let Q : @Iso Z₁.Modules _
      (dualSheaf ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).bundle)
      ((modulePullback f₁.toLRSHom.toShHom).obj
        ((modulePullback f₂.toLRSHom.toShHom).obj (dualSheaf N.bundle))) :=
    P₁.symm ≪≫ (modulePullback f₁.toLRSHom.toShHom).mapIso P₂.symm
  let Q' : @Iso Z₁.Modules _
      (dualSheaf (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).bundle)
      ((modulePullback f₁.toLRSHom.toShHom).obj
        ((modulePullback f₂.toLRSHom.toShHom).obj (dualSheaf N.bundle))) :=
    P.symm ≪≫ (modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).app _
  have hA : ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).conormalSurjection =
      Q.hom ≫ W :=
    (P₁.inv ≫= (Functor.map_comp (modulePullback f₁.toLRSHom.toShHom) P₂.inv _ =≫
      Stacks.Immersion.immersionConormalSheafMap i₁ i₂ f₁ g₁
        (Stacks.Immersion.toShHom_square sq₁.w))).trans
      ((P₁.inv ≫= Category.assoc _ _ _).trans (Category.assoc _ _ _).symm)
  have hB : (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).conormalSurjection =
      Q'.hom ≫ W :=
    (P.inv ≫= pullback_map_comp_immersionConormalSheafMap_comp sq₁.w sq₂.w N.surjection).trans
      (Category.assoc _ _ _).symm
  kernelIsoOfEq hA ≪≫ @kernelIsIsoComp _ _ _ _ _ _ Q.hom W (Iso.isIso_hom Q) _ ≪≫
    (@kernelIsIsoComp _ _ _ _ _ _ Q'.hom W (Iso.isIso_hom Q') _).symm ≪≫
    (kernelIsoOfEq hB).symm

/-- **The excess normal sheaf of an iterated base change** is the excess normal sheaf of the base
change along the composite square: the duals of the kernels of
`Stacks.Chow.VirtualNormalBundle.kernelBaseChangeCompIso`. -/
def VirtualNormalBundle.excessNormalSheafBaseChangeCompIso (N : VirtualNormalBundle i₃)
    (sq₂ : IsPullback i₂ f₂ g₂ i₃) (sq₁ : IsPullback i₁ f₁ g₁ i₂) :
    ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).excessNormalSheaf ≅
      (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).excessNormalSheaf :=
  (dualFunctor Z₁).mapIso (N.kernelBaseChangeCompIso sq₂ sq₁).symm.op

end Composite

/-! ### Base change along equal edges -/

/-- **The base change of a virtual normal sheaf only depends on the edges of the square**, not on
the proof that it is cartesian. -/
theorem VirtualNormalBundle.baseChange_congr {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsImmersion i] [IsImmersion i'] (N : VirtualNormalBundle i) {g g' : Z' ⟶ Z}
    {f f' : X' ⟶ X} (hg : g = g') (hf : f = f') (sq : IsPullback i' g f i)
    (sq' : IsPullback i' g' f' i) :
    N.baseChange i i' g f sq = N.baseChange i i' g' f' sq' := by
  subst hg hf
  rfl

/-! ### Base change along an open immersion -/

section Open

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'} [IsImmersion i] [IsImmersion i']
  (N : VirtualNormalBundle i) {w : Z' ⟶ Z} {o : X' ⟶ X} [IsOpenImmersion o]

/-- **The kernel of the surjection of a base change along an open immersion** is the pullback of
the kernel of the surjection: the conormal map of the square is an isomorphism (Stacks 0473, flat
base change) and pullback along the open immersion `Z' ⟶ Z` is exact. -/
def VirtualNormalBundle.kernelBaseChangeOpenIso (sq : IsPullback i' w o i) :
    kernel (N.baseChange i i' w o sq).conormalSurjection ≅
      (Scheme.Modules.pullback w).obj (kernel N.conormalSurjection) := by
  haveI : IsOpenImmersion w := MorphismProperty.of_isPullback sq (P := @IsOpenImmersion)
    inferInstance
  haveI : PreservesFiniteLimits (Scheme.Modules.pullback w) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback w)
  let P : @Iso Z'.Modules _ (dualSheaf (N.baseChange i i' w o sq).bundle)
      ((Scheme.Modules.pullback w).obj (dualSheaf N.bundle)) :=
    (@asIso _ _ _ _ (pullbackDualMap w N.bundle)
      (pullbackDualMap_isIso w N.bundle N.isFiniteLocallyFree)).symm
  let K : @Iso Z'.Modules _ ((Scheme.Modules.pullback w).obj (conormalModule i))
      (conormalModule i') :=
    @asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap i' i w o
        (Stacks.Immersion.toShHom_square sq.w))
      (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat i' i w o sq)
  have h : (N.baseChange i i' w o sq).conormalSurjection =
      P.hom ≫ ((Scheme.Modules.pullback w).map N.conormalSurjection ≫ K.hom) := rfl
  exact kernelIsoOfEq h ≪≫ kernelIsIsoComp P.hom _ ≪≫ kernelCompMono _ K.hom ≪≫
    (PreservesKernel.iso (Scheme.Modules.pullback w) N.conormalSurjection).symm

/-- **The excess normal sheaf of a base change along an open immersion** is the pullback of the
excess normal sheaf, when the conormal sheaf is finite locally free: the dual of
`Stacks.Chow.VirtualNormalBundle.kernelBaseChangeOpenIso`, followed by the dual base-change
isomorphism of Stacks 0GMX for the finite locally free kernel. -/
def VirtualNormalBundle.excessNormalSheafBaseChangeOpenIso (sq : IsPullback i' w o i)
    (hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i)) :
    (N.baseChange i i' w o sq).excessNormalSheaf ≅
      (Scheme.Modules.pullback w).obj N.excessNormalSheaf :=
  haveI := pullbackDualMap_isIso w (kernel N.conormalSurjection)
    (N.isFiniteLocallyFree_kernel_surjection hC)
  (dualFunctor Z').mapIso (N.kernelBaseChangeOpenIso sq).symm.op ≪≫
    (asIso (pullbackDualMap w (kernel N.conormalSurjection))).symm

end Open

end Stacks.Chow

end
