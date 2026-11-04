module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionMaps
public import StacksFrontier.Deformation.RingedSpaceThickening.ModuleExtension
import StacksCore.Tactic.StacksAttribute

/-!
# Compatibility of the canonical maps of two extensions (Stacks 08L5, part 1)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces and let

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0    and    0 ⟶ i_* ℒ ⟶ 𝒢' ⟶ i_* 𝒢 ⟶ 0

be two extensions of `𝒪_{X'}`-modules as in Tag 08L4, together with maps `φ : ℱ ⟶ 𝒢` and
`ψ : 𝒦 ⟶ ℒ`. This file proves the first clause of Tag 08L5: if some `𝒪_{X'}`-module map
`φ' : ℱ' ⟶ 𝒢'` is compatible with `φ` and `ψ`, then the square

    ℐ ⊗_{𝒪_X} ℱ --c_{ℱ'}--> 𝒦
        |                    |
      1 ⊗ φ                  ψ
        v                    v
    ℐ ⊗_{𝒪_X} 𝒢 --c_{𝒢'}--> ℒ

commutes. The second clause — that the set of such `φ'` is, when nonempty, a principal
homogeneous space under `Hom_{𝒪_X}(ℱ, ℒ)` — is
`AlgebraicGeometry.RingedSpaceThickening.ExtensionPair.exists_compatibleMap_translate`
together with `.existsUnique_translate`, in
`StacksFrontier.Deformation.RingedSpaceThickening.ExtensionMaps`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison_naturality`: the
  comparison `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(i^* ℐ ⊗_{𝒪_X} ℱ)` of Tag 08L4 is natural in `ℱ`.
* `AlgebraicGeometry.RingedSpaceThickening.ExtensionPair.extensionAction_naturality`:
  **Stacks 08L5**, part (1), the commuting square displayed above.

## Implementation notes

Both sides of the square are maps out of `i^* ℐ ⊗_{𝒪_X} ℱ`, so
`AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison_cancel` reduces the
identity to one on `X'`. There the two canonical maps are characterised by their effect on a
local lift, and the square becomes the two commuting squares of the compatible map, which is
where the hypothesis on `φ'` is used; the reduction to pure tensors is legitimate because
`1 ⊗ (ℱ' ⟶ i_* ℱ)` is an epimorphism.

Naturality of the comparison is proved in two declarations rather than one. The comparison is
an adjoint transpose, so naturality amounts to naturality of the map it transposes — the
Tag 01CD isomorphism followed by the counit of `i^* ⊣ i_*` in the second factor — and that is
`extensionTensorComparisonTranspose_naturality`. Keeping the two apart matters: the two halves
together exceed the default heartbeat budget of a single declaration. `comp_tensorSheafMap_comp_right`
fixes the bracketing of the two induced maps in advance, so that no step has to transport an
association across a spelling change, and `tensorSheafMap_eq_tensorSheaf_map` records that the
tensor product of two morphisms and the corresponding map of the tensor-product bifunctor are
the same term, which is what lets a step name either one.

Three transparency opt-ins carry the file, and all three are needed. `sheafTensor` is lowered
to `irreducible`: every statement here composes a map of the tensor-product bifunctor, whose
domain is `(uncurry.obj (sheafTensor R)).obj (A, B)`, with a morphism — `extensionTensorComparison`,
or the hom of the Tag 01CD isomorphism — whose type spells that same object as
`((sheafTensor R).obj A).obj B`. The two are one iota step apart, but the unifier sees
`Functor.obj` on both sides, tries the arguments first, and on failing falls back to weak-head
normalising, which unfolds `sheafTensor` into the sheafification of a presheaf tensor product and
spends the whole heartbeat budget. Nothing here needs that body. Writing the universes out fixes
none of it, at any statement in the file, whereas opacity fixes all of it.

`Tensor.ringSheaf` and `SheafedSpace.sheaf` are raised instead, and both are needed, because there
are three spellings of the structure sheaf of rings on this path and not two: the bifunctor lands
in `SheafOfModules (Tensor.ringSheaf ⟨𝒪_X, _⟩)`, the Tag 01CC epimorphism lemma is stated over
`Tensor.ringSheaf X.sheaf`, and the modules here are typed `SheafOfModules (structureSheafRing X)`.
All three are equal by `rfl`, but only `structureSheafRing` unfolds during instance search, so
without both opt-ins two objects of one category are not recognised as such and `Epi (𝟙 ℐ)` is not
found. Raising `TopCat.Sheaf` too is not needed here; dropping either of the other two reinstates
that failure.

Separately, a map of the bifunctor is written `.map ((f, g) : (A, C) ⟶ (B, D))` with the two pairs
spelled out wherever the resulting equation is chained against `tensorSheafMap_comp_right` or an
adjunction naturality lemma — in `hu` and `h5` of `extensionAction_naturality_ambient`, in `hL`
and `hR` below, and in the last step of `extensionAction_naturality`. The elaborated proposition
is the same as with `(_, _) ⟶ (_, _)`, and opacity alone does not make those steps affordable: it
is the order in which the pair's objects get solved that decides whether the chaining costs a few
thousand heartbeats or more than the budget, at each of those five sites.

## References

* [Stacks Project, Tag 08L5](https://stacks.math.columbia.edu/tag/08L5)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorPresentations (tensorSheafMap_epi_of_epi_of_epi)

universe u

-- Nothing here needs the body of the tensor-product bifunctor, and the two spellings of the
-- structure sheaf of rings have to be reconciled throughout; see the implementation note.
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The tensor product of two morphisms of sheaves of modules on a ringed space, read as a map
of the tensor-product bifunctor: the two spellings agree on the nose. -/
theorem tensorSheafMap_eq_tensorSheaf_map {Y : RingedSpace.{u, u}}
    {A B C D : SheafOfModules.{u} (structureSheafRing Y)} (f : A ⟶ B) (g : C ⟶ D) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map ((f, g) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map ((f, g) : ((A, C) : _ × _) ⟶ (B, D)) := rfl

/-- **Stacks 01CD**, naturality in the second variable: the comparison isomorphism
`i^*(A ⊗ B) ≅ i^* A ⊗ i^* B` is natural in `B`, with the identity in the first variable. -/
theorem comparisonBifunctorIso_naturality_right (A : SheafOfModules.{u} (structureSheafRing X'))
    {C D : SheafOfModules.{u} (structureSheafRing X')} (g : C ⟶ D) :
    (modulePullback i).map (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 A), g) : (_, _) ⟶ (_, _)))) ≫
        (Stacks.RingedSpace.comparisonBifunctorIso i).hom.app (A, D) =
      (Stacks.RingedSpace.comparisonBifunctorIso i).hom.app (A, C) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 ((modulePullback i).obj A)), ((modulePullback i).map g)) : (_, _) ⟶ (_, _))) := by
  refine ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.naturality
    ((𝟙 A, g) : ((A, C) : _ × _) ⟶ (A, D))).trans ?_
  exact congrArg (fun z => (Stacks.RingedSpace.comparisonBifunctorIso i).hom.app (A, C) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).map z)
    (Prod.ext ((modulePullback i).map_id A) rfl)

/-- Absorbing a second induced map into the first, after an arbitrary map in: the form of
`tensorSheafMap_comp_right` whose two sides are already bracketed as they occur. -/
theorem comp_tensorSheafMap_comp_right {Y : RingedSpace.{u, u}}
    (A : SheafOfModules.{u} (structureSheafRing Y)) {C D E Z : SheafOfModules.{u} (structureSheafRing Y)}
    (k : Z ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj (A)).obj (C))) (f : C ⟶ D) (g : D ⟶ E) :
    (k ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), f) : (_, _) ⟶ (_, _)))) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), g) : (_, _) ⟶ (_, _))) =
      k ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), (f ≫ g)) : (_, _) ⟶ (_, _))) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun z => k ≫ z) (tensorSheafMap_comp_right A f g))

/-- The map transposed by `extensionTensorComparison` — the **Stacks 01CD** isomorphism
followed by the counit of `i^* ⊣ i_*` in the second tensor factor, which is
`homEquiv_symm_extensionTensorComparison` — is natural in the module. -/
theorem extensionTensorComparisonTranspose_naturality
    (F G : SheafOfModules.{u} (structureSheafRing X)) (φ : F ⟶ G) :
    ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app F)) : (_, _) ⟶ (_, _)))) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), φ) : (_, _) ⟶ (_, _))) =
      (modulePullback i).map (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), ((modulePushforward i).map φ)) : (_, _) ⟶ (_, _)))) ≫
        ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj G) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app G)) : (_, _) ⟶ (_, _)))) := by
  have hcounit : (modulePullbackPushforwardAdjunction i).counit.app F ≫ φ =
      (modulePullback i).map ((modulePushforward i).map φ) ≫
        (modulePullbackPushforwardAdjunction i).counit.app G :=
    ((modulePullbackPushforwardAdjunction i).counit.naturality φ).symm
  refine (comp_tensorSheafMap_comp_right _ _ _ _).trans ?_
  rw [hcounit]
  refine (comp_tensorSheafMap_comp_right _ _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (comparisonBifunctorIso_naturality_right i _ _).symm

/-- The comparison `extensionTensorComparison` of Tag 08L4 is natural in the module: it does
not matter whether `φ` is applied in the second tensor factor before or after transporting the
tensor product from the thickening down to `X`. -/
theorem extensionTensorComparison_naturality
    (F G : SheafOfModules.{u} (structureSheafRing X)) (φ : F ⟶ G) :
    extensionTensorComparison i F ≫
        (modulePushforward i).map (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), φ) : (_, _) ⟶ (_, _)))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), ((modulePushforward i).map φ)) : (_, _) ⟶ (_, _))) ≫
        extensionTensorComparison i G := by
  exact ((modulePullbackPushforwardAdjunction i).homEquiv_naturality_right _ _).symm.trans
    ((congrArg ((modulePullbackPushforwardAdjunction i).homEquiv _ _)
      (extensionTensorComparisonTranspose_naturality i F G φ)).trans
      ((modulePullbackPushforwardAdjunction i).homEquiv_naturality_left _ _))

section Skeleton

universe v v' w w'

variable {C : Type v} [Category.{w} C]

/-- Precomposing the image of a composite: the form of `CategoryTheory.Functor.map_comp` whose
two sides are already bracketed as they occur after a map into the image of the functor. -/
theorem comp_functor_map_comp {D : Type v'} [Category.{w'} D] (P : C ⥤ D) {A B E : C} {W : D}
    (k : W ⟶ P.obj A) (f : A ⟶ B) (g : B ⟶ E) :
    k ≫ P.map (f ≫ g) = (k ≫ P.map f) ≫ P.map g := by
  simp

/-- The categorical skeleton of Tag 08L5, part (1). Two maps `dF` and `dG` out of objects
carrying an action — `u ≫ dF ≫ ef = aF` and `wq ≫ dG ≫ ef' = aL` — are intertwined by `pψ`
and `t` as soon as the actions are, by `h3`, and the two compatibility squares `h4` and `h5`
hold. It is stated for an abstract category because the only content is the bracketing. -/
theorem descendedAction_naturality_of_squares
    {T TF TG TL KK LL FF GG : C}
    (u : T ⟶ TF) (v : T ⟶ TL) (wq : TL ⟶ TG) (t : TF ⟶ TG)
    (dF : TF ⟶ KK) (dG : TG ⟶ LL) (ef : KK ⟶ FF) (ef' : LL ⟶ GG)
    (pψ : KK ⟶ LL) (ch : FF ⟶ GG) (aF : T ⟶ FF) (aL : TL ⟶ GG)
    (hu : Epi u) (hm : Mono ef')
    (h1 : u ≫ dF ≫ ef = aF) (h2 : wq ≫ dG ≫ ef' = aL)
    (h3 : aF ≫ ch = v ≫ aL) (h4 : ef ≫ ch = pψ ≫ ef')
    (h5 : u ≫ t = v ≫ wq) :
    dF ≫ pψ = t ≫ dG := by
  have := hu
  have := hm
  refine (cancel_mono ef').1 ((cancel_epi u).1 ?_)
  calc u ≫ (dF ≫ pψ) ≫ ef'
      = (u ≫ dF ≫ ef) ≫ ch := by simp only [Category.assoc]; rw [← h4]
    _ = v ≫ aL := by rw [h1, h3]
    _ = (u ≫ t) ≫ dG ≫ ef' := by rw [← h2, h5]; simp only [Category.assoc]
    _ = u ≫ (t ≫ dG) ≫ ef' := by simp only [Category.assoc]

end Skeleton

namespace ExtensionPair

/-- The content of Tag 08L5, part (1), on the thickened space: the comparison followed by the
canonical map of the first extension, composed with `i_* ψ`, is `1 ⊗ i_* φ` followed by the
same for the second extension. -/
theorem extensionAction_naturality_ambient (S : ExtensionPair.{u}) (c : CompatibleMap S) :
    (extensionTensorComparison S.i S.F ≫ (modulePushforward S.i).map
          (firstOrderExtensionAction S.i S.F S.K S.firstOrder S.firstExtension).val) ≫
        (modulePushforward S.i).map S.kernelMap =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X')).presheaf, ((S.X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf S.i)), ((modulePushforward S.i).map S.quotientMap)) : (_, _) ⟶ (_, _))) ≫
        (extensionTensorComparison S.i S.G ≫ (modulePushforward S.i).map
          (firstOrderExtensionAction S.i S.G S.L S.firstOrder S.secondExtension).val) := by
  have hgEpi : @Epi (SheafOfModules.{u} (structureSheafRing S.X')) _ _ _
      S.firstExtension.g := S.firstExtension.epi_g
  have hu := tensorSheafMap_epi_of_epi_of_epi S.X'
    (𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf S.i)) S.firstExtension.g
  have h5 := (tensorSheafMap_comp_right (AlgebraicGeometry.SheafOfModules.idealSheaf S.i)
        S.firstExtension.g ((modulePushforward S.i).map S.quotientMap)).trans
      ((congrArg (fun z : S.firstExtension.Z.left ⟶ (modulePushforward S.i).obj S.G =>
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.X'.presheaf, S.X'.IsSheaf⟩)).map
          (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf S.i)), z) : (_, _) ⟶ (_, _))))
        c.quotient_commutes).symm.trans
        (tensorSheafMap_comp_right (AlgebraicGeometry.SheafOfModules.idealSheaf S.i)
          c.hom S.secondExtension.g).symm)
  exact descendedAction_naturality_of_squares _ _ _ _ _ _ _ _ _ c.hom _ _
    hu S.secondExtension.mono_f
    (firstOrderExtensionAction_comp S.i S.F S.K S.firstOrder S.firstExtension)
    (firstOrderExtensionAction_comp S.i S.G S.L S.firstOrder S.secondExtension)
    (idealAction_naturality S.i c.hom) c.kernel_commutes h5

/-- **Stacks Project, Tag 08L5**, part (1). If the middle terms of two extensions across a
first order thickening are linked by a map `φ'` compatible with `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ`,
then the canonical maps of the two extensions commute with `1 ⊗ φ` and `ψ`. -/
@[stacks 08L5 "part (1): compatibility of the canonical maps"]
theorem extensionAction_naturality (S : ExtensionPair.{u}) (c : CompatibleMap S) :
    (firstOrderExtensionAction S.i S.F S.K S.firstOrder S.firstExtension).val ≫ S.kernelMap =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback S.i)), S.quotientMap) : (_, _) ⟶ (_, _))) ≫
        (firstOrderExtensionAction S.i S.G S.L S.firstOrder S.secondExtension).val := by
  refine extensionTensorComparison_cancel S.i S.firstOrder.1 _ _ ?_
  refine (comp_functor_map_comp (modulePushforward S.i) (extensionTensorComparison S.i S.F)
    (firstOrderExtensionAction S.i S.F S.K S.firstOrder S.firstExtension).val
    S.kernelMap).trans ((extensionAction_naturality_ambient S c).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg
    (fun z => z ≫ (modulePushforward S.i).map
      (firstOrderExtensionAction S.i S.G S.L S.firstOrder S.secondExtension).val)
    (extensionTensorComparison_naturality S.i S.F S.G S.quotientMap).symm).trans ?_)
  exact (comp_functor_map_comp (modulePushforward S.i) (extensionTensorComparison S.i S.F)
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback S.i)), S.quotientMap) : (idealSheafPullback S.i, S.F) ⟶ (idealSheafPullback S.i, S.G))))
    (firstOrderExtensionAction S.i S.G S.L S.firstOrder S.secondExtension).val).symm

end ExtensionPair

end AlgebraicGeometry.RingedSpaceThickening

end
