module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map from the pullback of a dual to the dual of a pullback

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed sites and let `F` be a sheaf of
`O_Y`-modules.  Writing `F^∨ = SheafHom_{O_Y}(F, O_Y)` for the dual, there is a canonical map

`can : f^*(F^∨) ⟶ (f^*F)^∨`

of sheaves of `O_X`-modules.  It is the canonical map
`f^* SheafHom_{O_Y}(F, G) ⟶ SheafHom_{O_X}(f^*F, f^*G)` of
[Stacks, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX) taken at `G = O_Y`, followed by
the identification `f^*O_Y = O_X` of the pullback of the structure sheaf.

[Stacks, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB) introduces the dual and a map
`can : p^*(M^∨) ⟶ (p^*M)^∨` for a module `M` over `A/Iⁿ`, in the situation of a blowup
`p : X → Spec(A)` of a Noetherian ring in an ideal `I`, built from a chosen presentation
`(A/I^n)^{⊕s} → (A/I^n)^{⊕r} → M → 0` of the module.  The map of this file is its sheaf-level
ingredient: no presentation is chosen, the map is the transpose of the pulled-back evaluation
pairing, and `pullbackDualMap_unique` shows it is the *only* morphism inducing that pairing.
The source's `can`, whose source is `p^*(M^∨) = f^*((M^∨)~)` rather than `f^*((M~)^∨)`, is
`Stacks.LocalCohomology.UniformityIII.pullbackModuleDualMap` of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackSource`, which is
built from this one and from a comparison `(M^∨)~ ≅ (M~)^∨` for finitely presented `M`.

## Main definitions

* `Stacks.SheafOfModules.PullbackDual.dualModuleSheaf`: the dual `F^∨ = SheafHom_O(F, O)` of a
  sheaf of modules on a ringed site — the `(-)^∨` of the source.
* `Stacks.SheafOfModules.PullbackDual.pullbackUnitHom`: the identification `f^*O_Y ⟶ O_X`.
* `Stacks.SheafOfModules.PullbackDual.pullbackDualMap`: the canonical map
  `f^*(F^∨) ⟶ (f^*F)^∨`.
* `Stacks.SheafOfModules.PullbackDual.pullbackDualEvaluation`: the pairing
  `f^*(F^∨) ⊗_{O_X} f^*F ⟶ O_X` obtained by pulling back the evaluation pairing of `F^∨` and
  identifying `f^*O_Y` with `O_X`.
* `Stacks.SheafOfModules.PullbackDual.dualModuleSheafMap` and
  `Stacks.SheafOfModules.PullbackDual.dualSheafFunctor`: the functorial action `c^∨` of the dual
  on a morphism `c : F' ⟶ F`, and the dual as a functor `Mod(O_Z)ᵒᵖ ⥤ Mod(O_Z)`.
* `Stacks.SheafOfModules.PullbackDual.pullbackDualNatTrans`: `can` as a natural transformation
  `(-)^∨ ⋙ f^* ⟶ (f^*)ᵒᵖ ⋙ (-)^∨`.
* `Stacks.SheafOfModules.PullbackDual.isIso_pullbackDualMap_unit`: `can` is an isomorphism at
  the structure sheaf.

## Main results

* `Stacks.SheafOfModules.PullbackDual.tensorEvaluation_pullbackDualMap`: tensoring `can` with
  `f^*F` and evaluating gives that pairing.
* `Stacks.SheafOfModules.PullbackDual.pullbackDualMap_unique`: `can` is the unique morphism
  with that property.
* `Stacks.SheafOfModules.PullbackDual.dualModuleSheafMap_id` and
  `Stacks.SheafOfModules.PullbackDual.dualModuleSheafMap_comp`: the dual is contravariantly
  functorial.
* `Stacks.SheafOfModules.PullbackDual.pullbackDualMap_naturality`: the functoriality of the map
  in `F`.

## Implementation notes

The source works with coherent modules on a scheme, but the construction uses none of that:
the two inputs it needs — the internal-Hom pullback comparison of Tag 0GMX and the
identification of `f^*O_Y` with `O_X` — exist for an arbitrary morphism of ringed sites, so
that is the generality here.  Consequently the blowup situation of the source does not appear:
there is no ring `A`, no ideal `I`, no blowup `p` and no thickening `Y_n`, and in particular
no finiteness, coherence or Noetherian hypothesis is carried.

A scheme-level map of the same shape, built the same way from the pulled-back evaluation
pairing, is `Stacks.Chow.pullbackDualMap`; it is not used here, so that this file depends only
on the ringed-site layer.

The equations are stated against the named morphism `pullbackDualEvaluation` rather than
against its defining composite written out; writing the composite inline makes the elaborator
unify the two sides of the equation from scratch, which does not terminate within the default
heartbeat budget.  For the same reason the proofs introduce their inputs with `have` before
combining them, so that each type is elaborated once on its own.

The functoriality in `F` is proved here, as `pullbackDualMap_naturality`: the contravariant
functoriality of the internal Hom in its first argument is `internalHomPre` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat`, its
compatibility with the pullback comparison is `pullbackInternalHomNatural` there, and all that
is left is to move the identification `f^*O_Y = O_X` past it.

The rest of Tag 0GAB — the source's `can` with source `p^*(M^∨)`, its functoriality in the
module, its invertibility at a finite free module, and the annihilation of its kernel and
cokernel by `I^c` for an `(A, n, c)`-module — is stated and proved in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackSource`, from the
results of this file and of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackFinFree`.  The
tag sits there; here it is only on the dual `dualModuleSheaf`.

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.InternalHom

namespace Stacks.SheafOfModules.PullbackDual

universe u

/-- The dual `F^∨ = SheafHom_O(F, O)` of a sheaf of modules on a ringed site: the internal Hom
of Tag 03EM out of `F` into the structure sheaf, the structure sheaf being read as a module
over itself.  This is the `(-)^∨` of Tag 0GAB. -/
@[stacks 0GAB "the dual F^∨ = SheafHom(F, O), for a sheaf of modules on a ringed site",
  ega "0 4.1.5",
  sga "3 I 4.6.5.1" "more general",
  sga "3 III 0.6",
  sga "3 VIIA 4.3.3" "more general"]
noncomputable def dualModuleSheaf (Z : RingedSite.{u, u, u})
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    _root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O) :=
  (internalHomSecondFunctor Z.J Z.O F).obj
    (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O))

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- The pullback of the structure sheaf of the target is the structure sheaf of the source:
the canonical morphism `f^*O_Y ⟶ O_X`, read off the isomorphism that corepresentability
supplies. -/
noncomputable def pullbackUnitHom :
    (ringedSitePullback f).obj (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)) ⟶
      _root_.SheafOfModules.unit (Tensor.ringSheaf X.O) :=
  (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
    f.ringedToposHom.toModulesHom).inv

/-- **The canonical map `f^*(F^∨) ⟶ (f^*F)^∨`.**  For a morphism of ringed sites `f` and a sheaf
of `O_Y`-modules `F`: the internal-Hom pullback comparison of Tag 0GMX at the structure sheaf,
followed by the identification `f^*O_Y = O_X`.  The map `can` of Tag 0GAB is built from it in
`Stacks.LocalCohomology.UniformityIII.pullbackModuleDualMap`. -/
@[ega "0 5.4.5"]
noncomputable def pullbackDualMap
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)) :
    (ringedSitePullback f).obj (dualModuleSheaf Y F) ⟶
      dualModuleSheaf X ((ringedSitePullback f).obj F) :=
  pullbackInternalHomMap f F (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)) ≫
    (internalHomSecondFunctor X.J X.O ((ringedSitePullback f).obj F)).map (pullbackUnitHom f)

/-- The pulled-back evaluation pairing `f^*(F^∨) ⊗_{O_X} f^*F ⟶ O_X`: the pullback of the
evaluation pairing of `F^∨`, read through the tensor comparison of Tag 03EL and followed by
the identification `f^*O_Y = O_X`. -/
noncomputable def pullbackDualEvaluation
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        ((ringedSitePullback f).obj (dualModuleSheaf Y F))).obj
          ((ringedSitePullback f).obj F) ⟶
      _root_.SheafOfModules.unit (Tensor.ringSheaf X.O) :=
  pullbackEvaluation f F (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)) ≫
    pullbackUnitHom f

/-- **The evaluation pairing of `can`.**  Tensoring `can` with `f^*F` and evaluating the dual
of `f^*F` gives the pulled-back evaluation pairing of `F^∨`. -/
theorem tensorEvaluation_pullbackDualMap
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)) :
    tensorEvaluation X.O ((ringedSitePullback f).obj F)
        (_root_.SheafOfModules.unit (Tensor.ringSheaf X.O)) (pullbackDualMap f F) =
      pullbackDualEvaluation f F := by
  have h1 := tensorEvaluation_comp_internalHomSecondFunctor_map X.O (pullbackUnitHom f)
    (pullbackInternalHomMap f F (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)))
  have h2 := tensorEvaluation_pullbackInternalHomMap f F
    (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O))
  exact h1.trans (congrArg (fun t => t ≫ pullbackUnitHom f) h2)

/-- **`can` is the only map with that evaluation pairing.**  The construction therefore
depends on no choice: the source builds `can` from a chosen presentation of the module, and
any morphism so built which induces the pulled-back evaluation pairing equals this one. -/
theorem pullbackDualMap_unique
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O))
    (g : (ringedSitePullback f).obj (dualModuleSheaf Y F) ⟶
      dualModuleSheaf X ((ringedSitePullback f).obj F))
    (hg : tensorEvaluation X.O ((ringedSitePullback f).obj F)
        (_root_.SheafOfModules.unit (Tensor.ringSheaf X.O)) g =
      pullbackDualEvaluation f F) :
    g = pullbackDualMap f F :=
  tensorEvaluation_injective X.O ((ringedSitePullback f).obj F)
    (_root_.SheafOfModules.unit (Tensor.ringSheaf X.O))
    (hg.trans (tensorEvaluation_pullbackDualMap f F).symm)

section Reassociation

variable {E : Type*} [Category* E]

/-- From `B ≫ Cm = C' ≫ B'` and `A ≫ C' = D ≫ A'` conclude `(A ≫ B) ≫ Cm = D ≫ A' ≫ B'`.

Over a plain category on purpose, for the reason recorded in the implementation notes: the
identity it is used for mixes reducibly equal spellings of one sheaf of rings whose
`CategoryStruct.comp` instances are reached by different paths, and a reassociation performed
in place there is not accepted by the transparency at which `rw` type-checks its motive. -/
private theorem comp_comp_comp_of_comp_eq {W Z T V S U' : E}
    (A : W ⟶ Z) (B : Z ⟶ T) (Cm : T ⟶ V) (C' : Z ⟶ S) (B' : S ⟶ V) (D : W ⟶ U') (A' : U' ⟶ S)
    (h1 : B ≫ Cm = C' ≫ B') (h2 : A ≫ C' = D ≫ A') :
    (A ≫ B) ≫ Cm = D ≫ A' ≫ B' := by
  rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc]

end Reassociation

/-- The dual is contravariant in `F`: a morphism `c : F' ⟶ F` of sheaves of modules induces
`c^∨ : F^∨ ⟶ F'^∨`.  It is the comparison `internalHomPre` in the first variable of the internal
Hom sheaf of Tag 03EM, read at the structure sheaf. -/
@[ega "0 4.1.5" "partial", sga "3 VIIA 4.3.3" "more general"]
noncomputable def dualModuleSheafMap (Z : RingedSite.{u, u, u})
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O)} (c : F' ⟶ F) :
    dualModuleSheaf Z F ⟶ dualModuleSheaf Z F' :=
  (internalHomPre Z.O c).app (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O))

/-- Dualizing the identity gives the identity. -/
@[simp]
theorem dualModuleSheafMap_id (Z : RingedSite.{u, u, u})
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    dualModuleSheafMap Z (𝟙 F) = 𝟙 (dualModuleSheaf Z F) := by
  simp only [dualModuleSheafMap, dualModuleSheaf, internalHomPre_id, NatTrans.id_app]

/-- Dualizing is contravariantly functorial: `(c ≫ d)^∨ = d^∨ ≫ c^∨`. -/
theorem dualModuleSheafMap_comp (Z : RingedSite.{u, u, u})
    {F F' F'' : _root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O)}
    (c : F'' ⟶ F') (d : F' ⟶ F) :
    dualModuleSheafMap Z (c ≫ d) = dualModuleSheafMap Z d ≫ dualModuleSheafMap Z c := by
  simp only [dualModuleSheafMap, dualModuleSheaf, ← internalHomPre_comp, NatTrans.comp_app]

/-- **The map `f^*(F^∨) ⟶ (f^*F)^∨` is functorial in `F`**: for `c : F' ⟶ F` the square built
from the map at `F` and at `F'`, from the pullback of `c^∨` and from `(f^*c)^∨` commutes.

It is the first-variable functoriality of the canonical map of Tag 0GMX,
`pullbackInternalHomNatural`, moved past the identification `f^*O_Y = O_X` by the naturality of
the first-variable comparison `internalHomPre` in its second variable. -/
@[ega "0 5.4.5" "partial"]
theorem pullbackDualMap_naturality
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)} (c : F' ⟶ F) :
    pullbackDualMap f F ≫ dualModuleSheafMap X ((ringedSitePullback f).map c) =
      (ringedSitePullback f).map (dualModuleSheafMap Y c) ≫ pullbackDualMap f F' := by
  have hnat :=
    (internalHomPre X.O ((ringedSitePullback f).map c)).naturality (pullbackUnitHom f)
  have hpre :=
    pullbackInternalHomNatural f (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)) c
  dsimp only [pullbackDualMap, dualModuleSheafMap]
  exact comp_comp_comp_of_comp_eq _ _ _ _ _ _ _ hnat hpre

/-- **The map `f^*(F^∨) ⟶ (f^*F)^∨` is an isomorphism at the structure sheaf.**  This is
Stacks 0GN2 at the structure sheaf, which needs neither flatness nor finiteness, followed by
the identification `f^*O_Y = O_X`, which is invertible. -/
theorem isIso_pullbackDualMap_unit :
    IsIso (pullbackDualMap f (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O))) := by
  have h1 : IsIso (pullbackInternalHomMap f
      (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O))
      (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O))) :=
    isIso_pullbackInternalHomMap_structureSheaf f _
  have h2 : IsIso (pullbackUnitHom f) :=
    Iso.isIso_inv (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      f.ringedToposHom.toModulesHom)
  have h3 : IsIso ((internalHomSecondFunctor X.J X.O ((ringedSitePullback f).obj
      (_root_.SheafOfModules.unit (Tensor.ringSheaf Y.O)))).map (pullbackUnitHom f)) := by
    have := h2
    infer_instance
  unfold pullbackDualMap
  exact IsIso.comp_isIso' h1 h3

/-- The dual as a functor `Mod(O_Z)ᵒᵖ ⥤ Mod(O_Z)`, assembled from `dualModuleSheaf` and
`dualModuleSheafMap`. -/
@[ega "0 4.1.5", sga "3 I 4.6.5.1" "more general", sga "3 VIIA 4.3.3" "more general"]
noncomputable def dualSheafFunctor (Z : RingedSite.{u, u, u}) :
    (_root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O))ᵒᵖ ⥤
      _root_.SheafOfModules.{u} (Tensor.ringSheaf Z.O) where
  obj F := dualModuleSheaf Z F.unop
  map c := dualModuleSheafMap Z c.unop
  map_id _ := dualModuleSheafMap_id Z _
  map_comp c d := dualModuleSheafMap_comp Z d.unop c.unop

/-- **The maps `f^*(F^∨) ⟶ (f^*F)^∨` as a natural transformation**

`(-)^∨ ⋙ f^* ⟶ (f^*)ᵒᵖ ⋙ (-)^∨`

of functors `Mod(O_Y)ᵒᵖ ⥤ Mod(O_X)`; the naturality squares are `pullbackDualMap_naturality`. -/
noncomputable def pullbackDualNatTrans :
    dualSheafFunctor Y ⋙ ringedSitePullback f ⟶
      (ringedSitePullback f).op ⋙ dualSheafFunctor X where
  app F := pullbackDualMap f F.unop
  naturality _ _ c := (pullbackDualMap_naturality f c.unop).symm

end Stacks.SheafOfModules.PullbackDual

end
