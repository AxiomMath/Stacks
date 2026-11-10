module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality

/-!
# The right-unitality coherence of Tag 03EL, reduced to one identity on `f⁻¹O_D`

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The comparison of
**Tag 03EL**, `f^*(F ⊗_{O_D} G) ⟶ f^*F ⊗_{O_C} f^*G`, is owed three coherences before it is a
monoidal structure on the pullback, and they are collected in
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`. This file treats the **right**
unitor,

`f^*(ρ_F) = c ≫ (f^*F ◁ ν) ≫ ρ_{f^*F}`,

for `ν : f^*O_D ≅ O_C` the unit comparison. It first reduces that coherence to a single identity
of morphisms of sheaves of sets over `f⁻¹O_D` in which the comparison of Tag 03EL no longer
occurs, and then **discharges that identity** and so proves the coherence. Both halves are at
**independent** coefficient universes. It is the right-handed mirror of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality`, whose lemmas it
consumes; nothing of that file is copied.

## Main results

* `Stacks.SheafOfModules.RingedToposPullback.rightUnitality_of_pairing`: the coherence follows
  from the single identity of pairings over `f⁻¹O_D` that step 3 of the chain of Tag 03EL
  produces. Steps 6, 5 and 4 are peeled by injectivity of the chain.
* `Stacks.SheafOfModules.RingedToposPullback.step1_rightUnitor`,
  `step2_rightUnitor` and `step3_rightUnitor`: **steps 1 to 3 of the chain of Tag 03EL on the
  pullback of the right unitor, evaluated.** The pairing they produce is `(a, t) ↦ t • (1 ⊗ a)`,
  the scalar action of `f⁻¹O_D` on `f⁻¹F` in the order the right unitor presents it, followed by
  the unit of Tag 03CZ.
* `Stacks.SheafOfModules.RingedToposPullback.rightUnitality_of_residual`: **the field
  `rightUnitality` of `PullbackCoherence`, verbatim, from one explicit named hypothesis.**
* `Stacks.SheafOfModules.RingedToposPullback.invImage_smulUnitHom`: the inverse image of the
  pairing `(a, r) ↦ r · a` is that pairing over `f⁻¹O_D`. This is
  `Stacks.Sheaves.ToposPullback.moduleSMul_map_aux'` together with the compatibility of a product
  comparison with the swap of the two factors.
* `Stacks.SheafOfModules.RingedToposPullback.step456_rightUnitor_pairingApp` and
  `step123_rightUnitor_pairingApp`: **the two pairings of the residual, each read on a pair of
  local sections.** Both are `f♯(t) · (1 ⊗ a)`.
* `Stacks.SheafOfModules.RingedToposPullback.residual_rightUnitality`: **the residual identity,
  discharged.**
* `Stacks.SheafOfModules.RingedToposPullback.rightUnitality`: **the field `rightUnitality` of
  `PullbackCoherence`, proved**, at the structure's own universes.

## Implementation notes

**Why no direct image is read on sections.** Step 1 of the chain is the adjunction of Tag 03D7,
which is the composite of Tag 03D3 with Tag 03CZ; on underlying sheaves of sets the unit of
Tag 03D3 *is* the unit of the adjunction of the underlying topoi
(`Stacks.SheafOfModules.RingedToposPullback.moduleSheafFunctor_map_invImageUnit`), and step 3
transposes back along that same adjunction. The two cancel by the triangle identity
(`Stacks.SheafOfModules.RingedToposPullback.invImage_pullbackUnit_comp_counit`), so the composite
of steps 1 to 3 is computed without ever evaluating `f_*` on sections — which matters, because for
a `CategoryTheory.Sheaf.MorphismOfTopoi` the direct image has no description on sections, and
`Stacks.SheafOfModules.pairingApp_inverseImageBilinearEquiv` stops at the unit for exactly that
reason.

**The swap.** The right unitor presents the scalar action in the order `(a, r) ↦ r · a`, so the
pairing is `Limits.prod.lift Limits.prod.snd Limits.prod.fst` followed by
`CategoryTheory.Sheaf.moduleSMulHom`, whereas the left unitor needs no such swap. The one extra
input is `prodComparison_comp_lift_swap`, that a product comparison commutes with the swap; it is
stated for an arbitrary finite-product-preserving functor, where every object is a variable, so
that `simp` can prove it.

**Spellings.** `Stacks.SheafOfModules.RingedToposPullback.rightUnitorHom`,
`smulUnitHom` and `smulUnitHomInvImage` are the right unitor and the two scalar actions with
their types **ascribed** at the spellings the chain of Tag 03EL uses; every crossing between two
definitionally equal spellings happens once, inside a defeq-tolerant `:=`, exactly as the
implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal` prescribe. Nothing
here raises a compiler limit or disables a linter.

**What discharges the residual, and what does not.** The residual says that the pairing
`(a, t) ↦ t • (1 ⊗ a)` over `f⁻¹O_D`, which steps 1 to 3 produce, is the pairing that
`(- ◁ ν) ≫ ρ` produces through steps 6, 5 and 4 run backwards. On a pair of local sections both
are `f♯(t) · (1 ⊗ a)`: the left-hand one because the unit of Tag 03CZ is **semilinear** over
`f♯` (`structureAdjunction_unit_sections_smul`), the right-hand one because step 6 carries
`1 ⊗ (a ⊗ t)` to `(1 ⊗ a) ⊗ (1 ⊗ t)`
(`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_unit_tmul`) and `ν` sends
`1 ⊗ t` to `f♯(t)` (`pullbackUnitComparison_val_app_unit`). No identity of tensor products of
modules is used, and the factoring of `ν` through
`Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso` and
`Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor` is not needed: the section formula for `ν`
enters only as that one black box.

**Universes.** `X : RingedTopos.{v, u, w}` and `Y : RingedTopos.{v', u', w'}`: throughout, the
two sites and the two coefficient universes are **independent**, as in
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence` itself. The adjunction of Tag 03CZ
is named by `Stacks.SheafOfModules.RingedToposPullback.structureAdjunction` as well as
`Stacks.Sheaves.RingedToposModules.fSharpAdjunction`; at independent coefficient universes the two
are the same abbreviation written twice and may be merged.

The section `Residual` is at the same generality. The only section formula `ν` admits is
`Stacks.Sheaves.RingedToposModules`.
`moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`, which rests on
`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`. Identifying the two coefficient universes
is not needed for `pullbackModuleUnitIso` — it is `Iso.refl` between two definitionally equal
objects at any pair of coefficient universes — although it is forced for the finite-free
comparison beside it; `pullbackModuleUnitIso` therefore has its own section at independent
coefficient universes in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree`, and
neither the `ν` formula nor this file identifies them. `rightUnitality_of_residual` keeps its
independent universes and is handed a residual at that generality.

## What this file does not contain

**No monoidal structure.** `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence` is not
constructed — its associativity field is untouched — no `CategoryTheory.Functor.Monoidal` or
`CategoryTheory.Functor.LaxMonoidal` instance is registered, and no tagged statement gains a
monoidal hypothesis.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u' v₁ u₁

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace Stacks.SheafOfModules.RingedToposPullback

section Abstract

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
  [Limits.HasFiniteProducts C₁] [Limits.HasFiniteProducts C₂]

omit [Limits.HasFiniteProducts C₁] in
/-- The product comparison of a finite-product-preserving functor commutes with the swap of the
two factors. -/
lemma prodComparison_comp_lift_swap (Φ : C₂ ⥤ C₁) [Limits.PreservesFiniteProducts Φ]
    (A B : C₂) :
    Limits.prodComparison Φ A B ≫ Limits.prod.lift Limits.prod.snd Limits.prod.fst =
      Φ.map (Limits.prod.lift Limits.prod.snd Limits.prod.fst) ≫
        Limits.prodComparison Φ B A := by
  refine Limits.prod.hom_ext ?_ ?_ <;> simp [← Functor.map_comp]

variable {C₃ : Type u₁} [Category.{v₁} C₃] {J₃ : GrothendieckTopology C₃}
  [J₃.HasSheafCompose (forget RingCat.{w})] [J₃.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **The pairing `(a, r) ↦ r · a`** of a sheaf of modules with the free module of rank one:
the scalar action of a sheaf of rings, read in the order the *right* unitor presents it. -/
def flipSMul (R : Sheaf J₃ RingCat.{w}) (G : _root_.SheafOfModules.{w} R) :
    Sheaf.moduleSheaf R G ⨯ Sheaf.moduleSheaf R (_root_.SheafOfModules.unit R) ⟶
      Sheaf.moduleSheaf R G :=
  Limits.prod.lift Limits.prod.snd Limits.prod.fst ≫ Sheaf.moduleSMulHom R G

/-- `Stacks.SheafOfModules.RingedToposPullback.flipSMul` on a pair of local sections. -/
lemma pairingApp_flipSMul (R : Sheaf J₃ RingCat.{w})
    (G : _root_.SheafOfModules.{w} R) (U : C₃ᵒᵖ)
    (a : (Sheaf.sectionsFunctor J₃ U).obj (Sheaf.moduleSheaf R G))
    (b : (Sheaf.sectionsFunctor J₃ U).obj R.ringSheaf) :
    Stacks.SheafOfModules.pairingApp R (flipSMul R G) U a b = b • a := by
  have hinner : (Sheaf.sectionsFunctor J₃ U).map
        (Limits.prod.lift (Limits.prod.snd (X := Sheaf.moduleSheaf R G) (Y := R.ringSheaf))
          Limits.prod.fst)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor J₃ U)
          (A := Sheaf.moduleSheaf R G) (B := R.ringSheaf) a b) =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor J₃ U)
        (A := R.ringSheaf) (B := Sheaf.moduleSheaf R G) b a := by
    rw [Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  exact (((Sheaf.sectionsFunctor J₃ U).map_comp_apply
      (Limits.prod.lift (Limits.prod.snd (X := Sheaf.moduleSheaf R G) (Y := R.ringSheaf))
        Limits.prod.fst) (Sheaf.moduleSMulHom R G)
      (Functor.prodObjMk (P := Sheaf.sectionsFunctor J₃ U)
        (A := Sheaf.moduleSheaf R G) (B := R.ringSheaf) a b)).trans
    ((congrArg (fun x ↦ (Sheaf.sectionsFunctor J₃ U).map (Sheaf.moduleSMulHom R G) x) hinner).trans
      (Sheaf.sectionsFunctor_map_moduleSMulHom R G U b a)))

end Abstract

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- The right unitor of the structure of Tag 01CA, with its source ascribed at the tensor
bifunctor of Tag 0GMW, exactly as
`Stacks.SheafOfModules.RingedToposPullback.leftUnitorHom` is for the left unitor. -/
def rightUnitorHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj (𝟙_ (_root_.SheafOfModules.{w'}
        (Tensor.ringSheaf Y.O))) ⟶ F :=
  (ρ_ F).hom

/-- The scalar action of the structure sheaf in the order the right unitor presents it,
`(a, r) ↦ r · a`, with its source ascribed at the underlying sheaf of sets of the unit object
`𝟙_` of the structure of Tag 01CA rather than at the sheaf of rings. -/
def smulUnitHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F ⨯
        Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ⟶
      Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F :=
  flipSMul (Tensor.ringSheaf Y.O) F

/-- The same pairing over the inverse image `f⁻¹O_D` of the structure sheaf of the target. -/
def smulUnitHomInvImage (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) ⨯
        Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) :=
  flipSMul (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
    ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)

/-- `Stacks.SheafOfModules.RingedToposPullback.smulUnitHom` on a pair of local sections. -/
theorem pairingApp_smulUnitHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (U : Y.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor Y.J U).obj (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F))
    (r : (Sheaf.sectionsFunctor Y.J U).obj (Tensor.ringSheaf Y.O).ringSheaf) :
    Stacks.SheafOfModules.pairingApp (Tensor.ringSheaf Y.O) (smulUnitHom F) U a r = r • a :=
  pairingApp_flipSMul (Tensor.ringSheaf Y.O) F U a r

open Stacks.SheafOfModules in
/-- Peeling the last three steps of the chain: the right-unitality coherence follows from the
single identity of pairings over `f⁻¹O_D` which step 3 of the chain of Tag 03EL produces. -/
theorem rightUnitality_of_pairing (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (hP : pullbackTensorStep3 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
          (f.pullbackModules.obj F)
          (pullbackTensorStep2 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
            (f.pullbackModules.obj F)
            (pullbackTensorStep1 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
              (f.pullbackModules.obj F) (f.pullbackModules.map (rightUnitorHom F)))) =
        (pullbackTensorStep4 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
            (f.pullbackModules.obj F)).symm
          ((pullbackTensorStep5 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep6 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                (f.pullbackModules.obj F)).symm
              ((f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
                (ρ_ (f.pullbackModules.obj F)).hom)))) :
    f.pullbackModules.map (ρ_ F).hom =
      pullbackTensorComparison f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ≫
        (f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
          (ρ_ (f.pullbackModules.obj F)).hom :=
  eq_comparison_comp f _ _
    ((chain_apply f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
        (f.pullbackModules.obj F) (f.pullbackModules.map (rightUnitorHom F))).trans
      (by rw [hP]; simp only [Equiv.apply_symm_apply]))

open Stacks.SheafOfModules in
/-- Step 1 of the chain on the pullback of the right unitor. -/
theorem step1_rightUnitor (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    pullbackTensorStep1 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
        (f.pullbackModules.obj F) (f.pullbackModules.map (rightUnitorHom F)) =
      rightUnitorHom F ≫ (pullbackAdjPushforwardModules f).unit.app F :=
  ((pullbackAdjPushforwardModules f).homEquiv_unit _ _ _).trans
    ((pullbackAdjPushforwardModules f).unit.naturality (rightUnitorHom F)).symm

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
open Stacks.SheafOfModules in
/-- The pairing of the right unitor followed by a morphism is `(a, r) ↦ r · a` followed by it. -/
theorem step2_rightUnitor (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (m : F ⟶ (pushforwardModules f).obj N) :
    (pullbackTensorStep2 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) N
        (rightUnitorHom F ≫ m)).1 =
      smulUnitHom F ≫ (Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map m :=
  pairing_ext (Tensor.ringSheaf Y.O) fun U a r ↦
    (pairingApp_step2 f F _ N (rightUnitorHom F ≫ m) U a r).trans
      ((Stacks.SheafOfModules.comp_val_app_apply _ _ _ _).trans
        ((congrArg (fun z ↦ m.val.app U z)
            (Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul Y.O.obj _ F U a r)).trans
          ((congrArg (fun z ↦ (Sheaf.sectionsFunctor Y.J U).map
                ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map m) z)
              (pairingApp_smulUnitHom F U a r)).symm.trans
            (pairingApp_comp (smulUnitHom F) m U a r).symm)))

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse image of the pairing `(a, r) ↦ r · a` is the same pairing over `f⁻¹O_D`. -/
theorem invImage_smulUnitHom (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (PreservesLimitPair.iso f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).inv ≫
        f.toToposHom.inverseImage.map (smulUnitHom F) =
      smulUnitHomInvImage f F := by
  have hswap : Limits.prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))) ≫
        smulUnitHomInvImage f F =
      f.toToposHom.inverseImage.map (smulUnitHom F) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ Sheaf.moduleSMulHom
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))
          (prodComparison_comp_lift_swap f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
            (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
              (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m ↦ f.toToposHom.inverseImage.map
                (Limits.prod.lift (Limits.prod.snd
                  (X := Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
                  (Y := Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
                    (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))))
                  Limits.prod.fst) ≫ m)
              (Stacks.Sheaves.ToposPullback.moduleSMul_map_aux' X.J f.toToposHom.inverseImage
                (Tensor.ringSheaf Y.O) F).symm).trans
            (f.toToposHom.inverseImage.map_comp _ _).symm)))
  have hid : (PreservesLimitPair.iso f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).inv ≫
        Limits.prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))) = 𝟙 _ :=
    (congrArg (fun m ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).inv ≫ m)
        (PreservesLimitPair.iso_hom f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
            (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).symm).trans
      (Iso.inv_hom_id _)
  exact ((congrArg (fun m ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).inv ≫ m)
      hswap).symm.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m ↦ m ≫ smulUnitHomInvImage f F) hid).trans
          (Category.id_comp _))))

/-- Reassociation of a four-fold composite, stated with every object a variable so that the
rewrite happens where the spellings of the objects do not have to be decided. -/
private alias assoc_mid := reassoc₄

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the chain of Tag 03EL on the pullback of the right unitor.** The pairing
over `f⁻¹O_D` they produce is `(a, t) ↦ t • (1 ⊗ a)`: the scalar action of `f⁻¹O_D` on `f⁻¹F`,
in the order the right unitor presents it, followed by the unit of Tag 03CZ.

The unit of Tag 03D3 is carried to the unit of the adjunction of the underlying topoi
(`Stacks.SheafOfModules.RingedToposPullback.moduleSheafFunctor_map_invImageUnit`), and step 3
transposes back along that same adjunction, so the two cancel by the triangle identity; no
reading of a direct image on sections is needed. -/
theorem step3_rightUnitor (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (pullbackTensorStep3 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
          (f.pullbackModules.obj F)
          (pullbackTensorStep2 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
            (f.pullbackModules.obj F)
            (pullbackTensorStep1 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
              (f.pullbackModules.obj F)
              (f.pullbackModules.map (rightUnitorHom F))))).1 =
      smulUnitHomInvImage f F ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
          ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) := by
  refine Eq.trans (congrArg (fun z ↦ (pullbackTensorStep3 f F
      (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
      (f.pullbackModules.obj F)
      (pullbackTensorStep2 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
        (f.pullbackModules.obj F) z)).1)
    (step1_rightUnitor f F)) ?_
  refine Eq.trans (inverseImageBilinearEquiv_symm_apply_coe_eq_comp_counit f.toToposHom
    (Tensor.ringSheaf Y.O) F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).inv ≫
      f.toToposHom.inverseImage.map m ≫ f.toToposHom.adj.counit.app _)
    (step2_rightUnitor f F (f.pullbackModules.obj F)
      ((pullbackAdjPushforwardModules f).unit.app F))) ?_
  refine Eq.trans (congrArg (fun z ↦ (PreservesLimitPair.iso f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Tensor.ringSheaf Y.O)
          (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))))).inv ≫ z ≫
      f.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            (f.pullbackModules.obj F))))
    (f.toToposHom.inverseImage.map_comp (smulUnitHom F)
      ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F)))) ?_
  exact (assoc_mid _ _ _ _).trans
    (congrArg₂ (fun p q ↦ p ≫ q) (invImage_smulUnitHom f F)
      (invImage_pullbackUnit_comp_counit f F))

open Stacks.SheafOfModules in
/-- **The right-unitality coherence of Tag 03EL, from one explicit identity.** Everything the
chain of Tag 03EL contributes is discharged here: what is left is the single identity `h`,
between two morphisms of sheaves of sets over `f⁻¹O_D`, in which the comparison of Tag 03EL no
longer occurs and no transpose of it is taken. Informally `h` says that `t • (1 ⊗ a)` and
`f♯(t) · (1 ⊗ a)` agree, the left-hand side being the pairing steps 1 to 3 produce and the
right-hand side the one `(- ◁ ν) ≫ ρ` produces through steps 4 to 6. -/
theorem rightUnitality_of_residual (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (h : smulUnitHomInvImage f F ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) =
        ((pullbackTensorStep4 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep5 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                (f.pullbackModules.obj F)).symm
              ((pullbackTensorStep6 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                  (f.pullbackModules.obj F)).symm
                ((f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
                  (ρ_ (f.pullbackModules.obj F)).hom)))).1) :
    f.pullbackModules.map (ρ_ F).hom =
      pullbackTensorComparison f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ≫
        (f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
          (ρ_ (f.pullbackModules.obj F)).hom :=
  rightUnitality_of_pairing f F (Subtype.ext ((step3_rightUnitor f F).trans h))

/-! ## The residual, discharged -/

section Residual

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Left whiskering of the monoidal structure of Tag 01CA on a local pure tensor: it acts in the
**second** factor. This is the mirror of
`Stacks.SheafOfModules.RingedToposPullback.whiskerRight_val_app_toSheafify`, which is what the
left unitor needs; the right unitor whiskers on the other side. -/
theorem whiskerLeft_val_app_toSheafify
    {A B B' : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (b : B ⟶ B') (U : X.Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (A ◁ b).val.app U
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
          (Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
        (Tensor.ringSheaf X.O).property (A.val ⊗ B'.val)).app U (x ⊗ₜ b.val.app U y) :=
  (congrArg (fun m : A ⊗ B ⟶ A ⊗ B' ↦ m.val.app U
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
          (Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y)))
      (Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map X.O.obj
        (Tensor.ringSheaf X.O).property A b)).trans
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app X.O.obj
      (Tensor.ringSheaf X.O).property (A.val ◁ b.val) U (x ⊗ₜ y))

open Stacks.SheafOfModules in
/-- **Steps 4 to 6 of the chain of Tag 03EL, inverted, on `(f^*F ◁ ν) ≫ ρ`**, read on a pair of
local sections: the pairing they produce carries `(a, t)` to `f♯(t) · (1 ⊗ a)`.

Step 6 is `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_unit_tmul`,
step 5 the unit form of the bijection of Tag 03CZ and step 4 the universal property of the tensor
product sheaf on a local pure tensor. The two factors of `(- ◁ ν) ≫ ρ` are then
`whiskerLeft_val_app_toSheafify` and `Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul`, and
the value of `ν` is `pullbackUnitComparison_val_app_unit`. -/
theorem step456_rightUnitor_pairingApp (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)))
    (t : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
        (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))))) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        ((pullbackTensorStep4 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep5 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                (f.pullbackModules.obj F)).symm
              ((pullbackTensorStep6 f F
                  (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                  (f.pullbackModules.obj F)).symm
                ((f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
                  (ρ_ (f.pullbackModules.obj F)).hom)))).1 U a t =
      Sheaf.moduleSMulObj (Tensor.ringSheaf X.O) (f.pullbackModules.obj F)
        (Sheaf.sectionsFunctor X.J U)
        ((Sheaf.sectionsFunctor X.J U).map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) t)
        (((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U a) :=
  (pairingApp_bilinearEquivTensorSheafHom_symm
        (hA := isSheaf_inverseImageStructureCommRing f) _ U a t).trans
    ((congrArg (fun m : inverseImageTensorSheaf f
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
              (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))) ⟶
          (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            (f.pullbackModules.obj F) ↦ m.val.app U _)
          ((structureAdjunction f).homEquiv_unit _ _ _)).trans
      ((congrArg (fun z ↦ ((f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
              (ρ_ (f.pullbackModules.obj F)).hom).val.app U z)
          (extendScalarsTensorIso_hom_val_app_unit_tmul (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O)).property
            (Tensor.ringSheaf X.O).property
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)
            ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
              (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))) U a t)).trans
        ((congrArg (fun z ↦ (ρ_ (f.pullbackModules.obj F)).hom.val.app U z)
              (whiskerLeft_val_app_toSheafify (pullbackUnitComparison f).hom U _ _)).trans
          ((Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul X.O.obj _
                (f.pullbackModules.obj F) U _ _).trans
            ((Sheaf.sectionsFunctor_map_moduleSMulHom (Tensor.ringSheaf X.O)
                  (f.pullbackModules.obj F) U _ _).symm.trans
              (congrArg (fun r ↦ Sheaf.moduleSMulObj (Tensor.ringSheaf X.O)
                  (f.pullbackModules.obj F) (Sheaf.sectionsFunctor X.J U) r _)
                (pullbackUnitComparison_val_app_unit f U t)))))))

open Stacks.SheafOfModules in
/-- **Steps 1 to 3 of the chain of Tag 03EL on `f^*(ρ_F)`**, read on a pair of local sections:
the pairing `step3_rightUnitor` produces carries `(a, t)` to `1 ⊗ (t · a)`, which is
`f♯(t) · (1 ⊗ a)` by semilinearity of the unit of Tag 03CZ
(`structureAdjunction_unit_sections_smul`). -/
theorem step123_rightUnitor_pairingApp (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)))
    (t : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj
        (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))))) :
    pairingApp (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
        (smulUnitHomInvImage f F ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) U a t =
      Sheaf.moduleSMulObj (Tensor.ringSheaf X.O) (f.pullbackModules.obj F)
        (Sheaf.sectionsFunctor X.J U)
        ((Sheaf.sectionsFunctor X.J U).map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) t)
        (((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)).val.app U a) :=
  (pairingApp_comp (smulUnitHomInvImage f F) _ U a t).trans
    ((congrArg (fun z ↦ (Sheaf.sectionsFunctor X.J U).map
          ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F))) z)
        (pairingApp_flipSMul (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) U a t)).trans
      (structureAdjunction_unit_sections_smul f
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F) U t a))

open Stacks.SheafOfModules in
/-- **The residual identity, discharged**: the two pairings over `f⁻¹O_D` agree, because on a
pair of local sections both are `f♯(t) · (1 ⊗ a)`. This is the hypothesis `h` of
`rightUnitality_of_residual`. -/
theorem residual_rightUnitality (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    smulUnitHomInvImage f F ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))).map
            ((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj F)) =
        ((pullbackTensorStep4 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
              (f.pullbackModules.obj F)).symm
            ((pullbackTensorStep5 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                (f.pullbackModules.obj F)).symm
              ((pullbackTensorStep6 f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)))
                  (f.pullbackModules.obj F)).symm
                ((f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
                  (ρ_ (f.pullbackModules.obj F)).hom)))).1 :=
  pairing_ext (inverseImageRingSheaf f.toToposHom (Tensor.ringSheaf Y.O))
    fun U a t ↦ (step123_rightUnitor_pairingApp f F U a t).trans
      (step456_rightUnitor_pairingApp f F U a t).symm

/-- **The right-unitality coherence of Tag 03EL**: the comparison of Tag 03EL is compatible
with the right unitor of the structure of Tag 01CA, the
unit object being matched by `ν : f^*O_D ≅ O_C`. This is the field
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.rightUnitality`, character for
character. -/
theorem rightUnitality (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    f.pullbackModules.map (ρ_ F).hom =
      pullbackTensorComparison f F (𝟙_ (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))) ≫
        (f.pullbackModules.obj F ◁ (pullbackUnitComparison f).hom) ≫
          (ρ_ (f.pullbackModules.obj F)).hom :=
  rightUnitality_of_residual f F (residual_rightUnitality f F)

end Residual

end Stacks.SheafOfModules.RingedToposPullback

end
