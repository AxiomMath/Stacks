module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.TwistMultTransport.Structural
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.InternalHomLocallyFree

/-!
# Pullback of the internal hom of two modules on a scheme

Let `f : W ⟶ Z` be a morphism of schemes and let `G`, `F` be `𝒪_Z`-modules. This file constructs
the canonical comparison `f^* SheafHom(G, F) ⟶ SheafHom(f^* G, f^* F)`, the morphism which the
tensor–internal-hom correspondence attaches to the pullback of the evaluation pairing
`SheafHom(G, F) ⊗ G ⟶ F`. It computes the comparison on local sections and identifies it on
global sections with the pullback of a morphism. For `G` finite locally free it also constructs an
isomorphism `f^* SheafHom(G, F) ≅ SheafHom(f^* G, f^* F)` from `SheafHom(G, F) ≅ F ⊗ G^∨`.

## Main definitions

* `Stacks.Algebraization.sheafHomUnitIso`: `SheafHom(𝒪_Z, F) ≅ F`.
* `Stacks.Algebraization.tensorDualSheafHomIso`: `F ⊗ G^∨ ≅ SheafHom(G, F)` for `G` finite
  locally free.
* `Stacks.Algebraization.sheafHomEvaluation`: the evaluation pairing `SheafHom(G, F) ⊗ G ⟶ F`.
* `Stacks.Algebraization.pullbackSheafHomEvaluation`: its pullback, read on the tensor product of
  the pullbacks.
* `Stacks.Algebraization.pullbackSheafHomMap`: the canonical comparison
  `f^* SheafHom(G, F) ⟶ SheafHom(f^* G, f^* F)`.
* `Stacks.Algebraization.pullbackSheafHomIso`: an isomorphism
  `f^* SheafHom(G, F) ≅ SheafHom(f^* G, f^* F)` for `G` finite locally free.
* `Stacks.Algebraization.pullbackSheafHomEquiv`: the bijection between the global sections of
  `f^* SheafHom(G, F)` and the morphisms `f^* G ⟶ f^* F`, for `G` finite locally free.
* `Stacks.Algebraization.pullbackSheafHomUnitEquiv`: the same bijection for `G = 𝒪_Z`.

## Main results

* `Stacks.Algebraization.isLocallyDirectSummandOfFiniteFree_of_isFiniteLocallyFree`: a finite
  locally free module on a scheme is locally a direct summand of a finite free module.
* `Stacks.Algebraization.sheafHomEvaluation_tmul`: the evaluation pairing on a local pure tensor.
* `Stacks.Algebraization.pullbackSheafHomMap_eval`: the morphism the comparison attaches to a
  local section of `f^* SheafHom(G, F)` evaluates on a local section of `f^* G` through the
  pulled-back evaluation pairing.
* `Stacks.Algebraization.pullbackSheafHomMap_unit_eval`: on the canonical image of a local section
  `s` of `SheafHom(G, F)` and the canonical image of a local section `m` of `G`, the comparison
  computes the canonical image of `s(m)`.
* `Stacks.Algebraization.pullbackSheafHomMap_app_top`: on global sections the comparison sends the
  section of `SheafHom(G, F)` attached to a morphism `φ : G ⟶ F` to the section attached to
  `f^* φ`.
* `Stacks.Algebraization.hom_ext_pullback_of_unit`: two morphisms out of a pullback agreeing on the
  canonical images of local sections are equal.
* `Stacks.Algebraization.sheafHomSection_app_terminal`: a section of the internal hom, evaluated at
  an object of the slice site, is its restriction evaluated at the terminal object of the smaller
  slice site.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Algebraization

variable {Z W : Scheme.{u}}

/-! ### Restriction of a section of the internal hom -/

/-- Restriction along the identity acts trivially on sections of a module. -/
private theorem map_id_apply {S : Scheme.{u}} (M : S.Modules) (U : S.Opens) (x : Γ(M, U)) :
    M.presheaf.map (𝟙 (op U)) x = x := by
  rw [M.presheaf.map_id]
  rfl

/-- A section of `SheafHom(G, M)` over `U`, evaluated at an object `V` of the slice site over `U`,
is its restriction to `V.left` evaluated at the terminal object of the slice site over `V.left`. -/
public theorem sheafHomSection_app_terminal (G M : Z.Modules) {U : Z.Opens}
    (t : ((sheafHomFunctor Z G).obj M).val.obj (op U)) (V : Over U) (x : Γ(G, V.left)) :
    ((((sheafHomFunctor Z G).obj M).presheaf.map
            (homOfLE (leOfHom V.hom)).op t).app (op (Over.mk (𝟙 V.left)))).hom x =
      (t.app (op V)).hom x := by
  refine Eq.trans (congrArg (fun y => (t.app
    (op (Over.mk ((Over.mk (𝟙 V.left)).hom ≫ homOfLE (leOfHom V.hom)) : Over U))).hom y)
      (map_id_apply G V.left x).symm) ?_
  refine (PresheafOfModules.naturality_apply t
    (op (Over.homMk (𝟙 V.left) (Subsingleton.elim _ _) :
      (Over.mk ((Over.mk (𝟙 V.left)).hom ≫ homOfLE (leOfHom V.hom)) : Over U) ⟶ V)) x).trans ?_
  exact map_id_apply M V.left _

/-! ### The internal hom out of the structure sheaf -/

/-- The isomorphism `SheafHom(𝒪_Z, F) ≅ F` of modules on a scheme `Z`. -/
public def sheafHomUnitIso (F : Z.Modules) :
    (sheafHomFunctor Z (SheafOfModules.unit Z.ringCatSheaf)).obj F ≅ F :=
  Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso
    (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Z) F

/-! ### Finite local freeness of the internal hom -/

/-- A finite locally free module on a scheme is locally a direct summand of a finite free
module. -/
public theorem isLocallyDirectSummandOfFiniteFree_of_isFiniteLocallyFree (G : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree
      Z.presheaf Z.ringCatSheaf.property G := by
  obtain ⟨q, hq, hqf⟩ := hG.exists_isFiniteLocallyFreeData
  intro U
  refine ⟨Sieve.ofObjects q.X U, q.coversTop U, ?_⟩
  intro V i hi
  obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff q.X i).mp hi
  refine ⟨(q.generators k).I, (hqf.isFiniteType k).finite, ⟨?_⟩⟩
  let e := Stacks.SheafOfModules.overIsoFree (M := G) b (q.generators k).I
    (@asIso _ _ _ _ _ (hq.isIso k)).symm
  exact ⟨e.hom, e.inv, e.hom_inv_id⟩

/-- The isomorphism `F ⊗ G^∨ ≅ SheafHom(G, F)` for `G` finite locally free, whose forward map
`Stacks.SheafOfModules.tensorDualToSheafHom` sends a local pure tensor `m ⊗ λ` to the operator
`g ↦ λ(g) • m`. -/
public def tensorDualSheafHomIso (G F : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    ((sheafTensor ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj F).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G) ≅
      (sheafHomFunctor Z G).obj F :=
  @asIso _ _ _ _ (Stacks.SheafOfModules.tensorDualToSheafHom Z.presheaf
      Z.ringCatSheaf.property G F)
    (Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand
      Z.presheaf Z.ringCatSheaf.property G F
      (isLocallyDirectSummandOfFiniteFree_of_isFiniteLocallyFree G hG))

/-! ### The evaluation pairing -/

/-- The evaluation pairing `SheafHom(G, F) ⊗ G ⟶ F`: the morphism which the tensor–internal-hom
correspondence carries to the identity of `SheafHom(G, F)`. -/
public def sheafHomEvaluation (G F : Z.Modules) :
    ((sheafTensor ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj
        (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F)).obj G ⟶ F :=
  (Stacks.SheafOfModules.tensorHomEquiv Z.toRingedSpace
      (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G F).symm
    (𝟙 (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F))

/-- The evaluation pairing sends a local pure tensor `s ⊗ m` to `s(m)`. -/
public theorem sheafHomEvaluation_tmul (G F : Z.Modules) (U : Z.Opens)
    (s : (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F).val.obj (op U))
    (m : G.val.obj (op U)) :
    (sheafHomEvaluation G F).val.app (op U)
        (Stacks.Chow.tensorSheafPure Z
          (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G U
          (s ⊗ₜ[Z.presheaf.obj (op U)] m)) =
      (s.app (op (Over.mk (𝟙 U)))).hom m := by
  have h := Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry Z.toRingedSpace
    (sheafHomEvaluation G F) U s m
  rw [sheafHomEvaluation, Equiv.apply_symm_apply] at h
  exact h.symm

/-! ### The comparison map -/

/-- The pulled-back evaluation pairing `f^* SheafHom(G, F) ⊗ f^* G ⟶ f^* F`: the pullback of
`Stacks.Algebraization.sheafHomEvaluation`, precomposed with the inverse of the tensor
comparison `f^* (A ⊗ B) ≅ f^* A ⊗ f^* B`. -/
public def pullbackSheafHomEvaluation (f : W ⟶ Z) (G F : Z.Modules) :
    ((sheafTensor ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pullback f).obj
          (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F))).obj
        ((Scheme.Modules.pullback f).obj G) ⟶
      (Scheme.Modules.pullback f).obj F :=
  (Stacks.Chow.pullbackTensorIso f
      (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G).inv ≫
    (Scheme.Modules.pullback f).map (sheafHomEvaluation G F)

/-- On sections, precomposing `Stacks.Algebraization.pullbackSheafHomEvaluation` with the tensor
comparison gives the pullback of the evaluation pairing. -/
public theorem pullbackSheafHomEvaluation_comparison_app (f : W ⟶ Z) (G F : Z.Modules)
    (V : W.Opens)
    (w : ((Scheme.Modules.pullback f).obj
      (((sheafTensor ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj
        (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F)).obj G)).val.obj (op V)) :
    (pullbackSheafHomEvaluation f G F).val.app (op V)
        ((Stacks.RingedSpace.comparison f.toLRSHom.toShHom
          (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G).val.app (op V) w) =
      ((Scheme.Modules.pullback f).map (sheafHomEvaluation G F)).val.app (op V) w := by
  have h : Stacks.RingedSpace.comparison f.toLRSHom.toShHom
        (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G ≫
          pullbackSheafHomEvaluation f G F =
      (Scheme.Modules.pullback f).map (sheafHomEvaluation G F) :=
    Iso.hom_inv_id_assoc (Stacks.Chow.pullbackTensorIso f
      (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G) _
  exact (Stacks.Chow.comp_val_app _ _ V w).symm.trans
    (congrArg (fun t => t.val.app (op V) w) h)

/-- The canonical comparison `f^* SheafHom(G, F) ⟶ SheafHom(f^* G, f^* F)` for a morphism of
schemes `f`: the morphism which the tensor–internal-hom correspondence attaches to the
pulled-back evaluation pairing. -/
public def pullbackSheafHomMap (f : W ⟶ Z) (G F : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((sheafHomFunctor Z G).obj F) ⟶
      (sheafHomFunctor W ((Scheme.Modules.pullback f).obj G)).obj
        ((Scheme.Modules.pullback f).obj F) :=
  Stacks.SheafOfModules.tensorHomEquiv W.toRingedSpace _ _ _ (pullbackSheafHomEvaluation f G F)

/-- The morphism which the comparison attaches to a local section `a` of `f^* SheafHom(G, F)`
sends a local section `b` of `f^* G` over the same open to the value of the pulled-back
evaluation pairing on `a ⊗ b`. -/
public theorem pullbackSheafHomMap_eval (f : W ⟶ Z) (G F : Z.Modules) (V : W.Opens)
    (a : ((Scheme.Modules.pullback f).obj ((sheafHomFunctor Z G).obj F)).val.obj (op V))
    (b : Γ((Scheme.Modules.pullback f).obj G, V)) :
    (((pullbackSheafHomMap f G F).val.app (op V) a).app (op (Over.mk (𝟙 V)))).hom b =
      (pullbackSheafHomEvaluation f G F).val.app (op V)
        (Stacks.Chow.tensorSheafPure W _ _ V (a ⊗ₜ[W.presheaf.obj (op V)] b)) :=
  Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry W.toRingedSpace
    (pullbackSheafHomEvaluation f G F) V a b

/-- The morphism which the comparison attaches to the canonical image of a local section `s` of
`SheafHom(G, F)` over `U` sends the canonical image of a local section `m` of `G` over `U` to the
canonical image of `s(m)`. -/
public theorem pullbackSheafHomMap_unit_eval (f : W ⟶ Z) (G F : Z.Modules) (U : Z.Opens)
    (s : ((sheafHomFunctor Z G).obj F).val.obj (op U)) (m : Γ(G, U)) :
    ((((pullbackSheafHomMap f G F).val.app (op (f ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              ((sheafHomFunctor Z G).obj F)).val.app (op U) s)).app
          (op (Over.mk (𝟙 (f ⁻¹ᵁ U))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U) m)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U)
        ((s.app (op (Over.mk (𝟙 U)))).hom m) :=
  (pullbackSheafHomMap_eval f G F (f ⁻¹ᵁ U) _ _).trans
    ((congrArg (fun t => (pullbackSheafHomEvaluation f G F).val.app (op (f ⁻¹ᵁ U)) t)
        (Stacks.Chow.comparison_tensorSheafPure f
          (Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace G F) G U s m)).symm.trans
      ((pullbackSheafHomEvaluation_comparison_app f G F (f ⁻¹ᵁ U) _).trans
        ((Stacks.Chow.pullback_map_unit_app f (sheafHomEvaluation G F) U _).trans
          (congrArg (fun t =>
              ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) t)
            (sheafHomEvaluation_tmul G F U s m)))))

/-! ### The comparison on global sections -/

/-- Two morphisms `f^* A ⟶ P` which agree on the canonical images of the local sections of `A`
are equal. -/
public theorem hom_ext_pullback_of_unit (f : W ⟶ Z) (A : Z.Modules) {P : W.Modules}
    {p q : (Scheme.Modules.pullback f).obj A ⟶ P}
    (h : ∀ (U : Z.Opens) (x : Γ(A, U)),
      p.val.app (op (f ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app (op U) x) =
        q.val.app (op (f ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app (op U) x)) :
    p = q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A P).injective <| by
    ext U x
    exact h U x

/-- The global section of `SheafHom(G, M)` attached to a morphism `G ⟶ M` has, at an object `V`
of the slice site over the whole space, the component of that morphism at `V.left`. -/
public theorem internalHomSectionsTopMapAddEquiv_app (G M : Z.Modules) (g : G ⟶ M)
    (V : Over (⊤ : Z.Opens)) :
    (internalHomSectionsTopMapAddEquiv G M g).app (op V) = g.val.app (op V.left) := rfl

/-- The morphism attached to a global section of `SheafHom(G, M)` has, at `V.left`, the component
that the section has at `V`. -/
public theorem internalHomSectionsTopEquiv_app (G M : Z.Modules)
    (s : ((sheafHomFunctor Z G).obj M).val.obj (op (⊤ : Z.Opens))) (V : Over (⊤ : Z.Opens)) :
    (internalHomSectionsTopEquiv G M s).val.app (op V.left) = s.app (op V) :=
  (internalHomSectionsTopMapAddEquiv_app G M (internalHomSectionsTopEquiv G M s) V).symm.trans
    (congrArg (fun t : ((sheafHomFunctor Z G).obj M).val.obj (op (⊤ : Z.Opens)) => t.app (op V))
      ((internalHomSectionsTopMapAddEquiv G M).apply_symm_apply s))

/-- Restricting the canonical image of a global section to `f⁻¹U` is the canonical image of the
restriction of that section to `U`. -/
public theorem pullbackGlobalSections_restrict (f : W ⟶ Z) (H : Z.Modules) (U : Z.Opens)
    (s : Γ(H, (⊤ : Z.Opens))) :
    ((Scheme.Modules.pullback f).obj H).presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op ((pullbackGlobalSections f H).hom s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).val.app (op U)
        (H.presheaf.map (homOfLE (le_top : U ≤ (⊤ : Z.Opens))).op s) := by
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).val
    (homOfLE (le_top : U ≤ (⊤ : Z.Opens))).op s).symm
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit]
  exact congrArg (fun k : (f ⁻¹ᵁ U ⟶ (⊤ : W.Opens)) =>
      ((Scheme.Modules.pullback f).obj H).presheaf.map k.op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).val.app
          (op (⊤ : Z.Opens)) s))
    (Subsingleton.elim _ _)

/-- The global section of `SheafHom(G, M)` attached to a morphism, read through
`Stacks.Algebraization.internalHomSectionsTopEquiv`. -/
public theorem internalHomSectionsTopEquiv_symm_apply (G M : Z.Modules) (g : G ⟶ M) :
    (internalHomSectionsTopEquiv G M).symm g = internalHomSectionsTopMapAddEquiv G M g := rfl

/-- Restricting the image under the comparison of the canonical image of a global section of
`SheafHom(G, F)` to `f⁻¹U` is the value of the comparison on the canonical image of the
restriction of that section to `U`. -/
public theorem pullbackSheafHomMap_app_top_restrict (f : W ⟶ Z) (G F : Z.Modules) (U : Z.Opens)
    (t : Γ((sheafHomFunctor Z G).obj F, (⊤ : Z.Opens))) :
    ((sheafHomFunctor W ((Scheme.Modules.pullback f).obj G)).obj
            ((Scheme.Modules.pullback f).obj F)).presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op
        ((pullbackSheafHomMap f G F).val.app (op (⊤ : W.Opens))
          ((pullbackGlobalSections f ((sheafHomFunctor Z G).obj F)).hom t)) =
      (pullbackSheafHomMap f G F).val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((sheafHomFunctor Z G).obj F)).val.app (op U)
          (((sheafHomFunctor Z G).obj F).presheaf.map
            (homOfLE (le_top : U ≤ (⊤ : Z.Opens))).op t)) :=
  (PresheafOfModules.naturality_apply (pullbackSheafHomMap f G F).val
      (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op
      ((pullbackGlobalSections f ((sheafHomFunctor Z G).obj F)).hom t)).symm.trans
    (congrArg (fun z => (pullbackSheafHomMap f G F).val.app (op (f ⁻¹ᵁ U)) z)
      (pullbackGlobalSections_restrict f ((sheafHomFunctor Z G).obj F) U t))

/-- The restriction to `U` of a global section of `SheafHom(G, M)`, evaluated at the terminal
object of the slice site over `U`, is the global section evaluated at `U`. -/
public theorem sheafHomSection_restrict_top (G M : Z.Modules) (U : Z.Opens)
    (t : Γ((sheafHomFunctor Z G).obj M, (⊤ : Z.Opens))) (m : Γ(G, U)) :
    ((((sheafHomFunctor Z G).obj M).presheaf.map
            (homOfLE (le_top : U ≤ (⊤ : Z.Opens))).op t).app (op (Over.mk (𝟙 U)))).hom m =
      (t.app (op (Over.mk (homOfLE (le_top : U ≤ (⊤ : Z.Opens)))))).hom m :=
  sheafHomSection_app_terminal G M t (Over.mk (homOfLE (le_top : U ≤ (⊤ : Z.Opens)))) m

/-- The morphism which the comparison attaches to the canonical image of a global section `t`,
read at `f⁻¹U`, is the morphism it attaches to the canonical image of the restriction of `t`
to `U`. The evaluation argument is arbitrary. -/
public theorem pullbackSheafHomMap_app_top_terminal (f : W ⟶ Z) (G F : Z.Modules) (U : Z.Opens)
    (t : Γ((sheafHomFunctor Z G).obj F, (⊤ : Z.Opens)))
    (b : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ U)) :
    (((pullbackSheafHomMap f G F).val.app (op (⊤ : W.Opens))
            ((pullbackGlobalSections f ((sheafHomFunctor Z G).obj F)).hom t)).app
          (op (Over.mk (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤))))).hom b =
      (((pullbackSheafHomMap f G F).val.app (op (f ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                ((sheafHomFunctor Z G).obj F)).val.app (op U)
              (((sheafHomFunctor Z G).obj F).presheaf.map
                (homOfLE (le_top : U ≤ (⊤ : Z.Opens))).op t))).app
          (op (Over.mk (𝟙 (f ⁻¹ᵁ U))))).hom b := by
  refine (sheafHomSection_app_terminal ((Scheme.Modules.pullback f).obj G)
    ((Scheme.Modules.pullback f).obj F) _
    (Over.mk (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤))) b).symm.trans ?_
  exact congrArg (fun z => ((z.app (op (Over.mk (𝟙 (f ⁻¹ᵁ U))))).hom b))
    (pullbackSheafHomMap_app_top_restrict f G F U t)

/-- The morphism which the comparison attaches to the canonical image of a global section `t` of
`SheafHom(G, F)` sends the canonical image of a local section `m` of `G` over `U` to the
canonical image of the value of `t` at `U` on `m`. -/
public theorem pullbackSheafHomMap_app_top_eval (f : W ⟶ Z) (G F : Z.Modules) (U : Z.Opens)
    (t : Γ((sheafHomFunctor Z G).obj F, (⊤ : Z.Opens))) (m : Γ(G, U)) :
    (((pullbackSheafHomMap f G F).val.app (op (⊤ : W.Opens))
            ((pullbackGlobalSections f ((sheafHomFunctor Z G).obj F)).hom t)).app
          (op (Over.mk (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U) m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U)
        ((t.app (op (Over.mk (homOfLE (le_top : U ≤ (⊤ : Z.Opens)))))).hom m) :=
  (pullbackSheafHomMap_app_top_terminal f G F U t _).trans
    ((pullbackSheafHomMap_unit_eval f G F U _ m).trans
      (Stacks.Chow.val_app_congr
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) U
        (sheafHomSection_restrict_top G F U t m)))

/-- On global sections the comparison is the pullback of morphisms: it carries the canonical image
of the global section of `SheafHom(G, F)` attached to `φ : G ⟶ F` to the global section of
`SheafHom(f^* G, f^* F)` attached to `f^* φ`. -/
public theorem pullbackSheafHomMap_app_top (f : W ⟶ Z) (G F : Z.Modules) (φ : G ⟶ F) :
    internalHomSectionsTopEquiv ((Scheme.Modules.pullback f).obj G)
        ((Scheme.Modules.pullback f).obj F)
        ((pullbackSheafHomMap f G F).val.app (op (⊤ : W.Opens))
          ((pullbackGlobalSections f ((sheafHomFunctor Z G).obj F)).hom
            ((internalHomSectionsTopEquiv G F).symm φ))) =
      (Scheme.Modules.pullback f).map φ := by
  refine hom_ext_pullback_of_unit f G (fun U m => ?_)
  refine Eq.trans (congrArg (fun k => k.hom
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op U) m))
    (internalHomSectionsTopEquiv_app ((Scheme.Modules.pullback f).obj G)
      ((Scheme.Modules.pullback f).obj F) _
      (Over.mk (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤))))) ?_
  refine (pullbackSheafHomMap_app_top_eval f G F U
    ((internalHomSectionsTopEquiv G F).symm φ) m).trans ?_
  refine Eq.trans (congrArg (fun z =>
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) z)
    (congrArg (fun k => k.hom m) (internalHomSectionsTopMapAddEquiv_app G F φ
      (Over.mk (homOfLE (le_top : U ≤ (⊤ : Z.Opens))))))) ?_
  exact (Stacks.Chow.pullback_map_unit_app f φ U m).symm

/-! ### The comparison on global sections as a bijection -/

/-- The isomorphism `f^* SheafHom(G, F) ≅ SheafHom(f^* G, f^* F)` for `G` finite locally free,
composed of `f^* SheafHom(G, F) ≅ f^* (F ⊗ G^∨)`, the tensor comparison
`f^* (F ⊗ G^∨) ≅ f^* F ⊗ f^* (G^∨)`, the dual base-change isomorphism `f^* (G^∨) ≅ (f^* G)^∨`,
and `f^* F ⊗ (f^* G)^∨ ≅ SheafHom(f^* G, f^* F)`. -/
public def pullbackSheafHomIso (f : W ⟶ Z) (G F : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    (Scheme.Modules.pullback f).obj ((sheafHomFunctor Z G).obj F) ≅
      (sheafHomFunctor W ((Scheme.Modules.pullback f).obj G)).obj
        ((Scheme.Modules.pullback f).obj F) :=
  ((Scheme.Modules.pullback f).mapIso (tensorDualSheafHomIso G F hG)).symm ≪≫
    Stacks.Chow.pullbackTensorIso f F
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G) ≪≫
      ((sheafTensor ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback f).obj F)).mapIso
          (@asIso _ _ _ _ (Stacks.Chow.pullbackDualMap f G)
            (Stacks.Chow.pullbackDualMap_isIso f G hG)) ≪≫
        tensorDualSheafHomIso ((Scheme.Modules.pullback f).obj G)
          ((Scheme.Modules.pullback f).obj F)
          (Stacks.Chow.isFiniteLocallyFree_pullback f G hG)

/-- The bijection between the global sections of `f^* SheafHom(G, F)` and the morphisms
`f^* G ⟶ f^* F`, for `G` finite locally free, induced by
`Stacks.Algebraization.pullbackSheafHomIso`. -/
public def pullbackSheafHomEquiv (f : W ⟶ Z) (G F : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    Γ((Scheme.Modules.pullback f).obj ((sheafHomFunctor Z G).obj F), (⊤ : W.Opens)) ≃
      ((Scheme.Modules.pullback f).obj G ⟶ (Scheme.Modules.pullback f).obj F) :=
  (Stacks.FundamentalGroup.appTopEquiv (pullbackSheafHomIso f G F hG)).trans
    (internalHomSectionsTopEquiv ((Scheme.Modules.pullback f).obj G)
      ((Scheme.Modules.pullback f).obj F)).toEquiv

/-- The bijection between the global sections of `f^* SheafHom(𝒪_Z, F)` and the morphisms
`f^* 𝒪_Z ⟶ f^* F`. -/
public def pullbackSheafHomUnitEquiv (f : W ⟶ Z) (F : Z.Modules) :
    Γ((Scheme.Modules.pullback f).obj
        ((sheafHomFunctor Z (SheafOfModules.unit Z.ringCatSheaf)).obj F), (⊤ : W.Opens)) ≃
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
        (Scheme.Modules.pullback f).obj F) :=
  pullbackSheafHomEquiv f (SheafOfModules.unit Z.ringCatSheaf) F
    (AlgebraicGeometry.isFiniteLocallyFree_unit Z)

end Stacks.Algebraization

end
