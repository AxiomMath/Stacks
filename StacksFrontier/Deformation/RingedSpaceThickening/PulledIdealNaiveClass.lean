module

public import StacksFrontier.Deformation.RingedSpaceThickening.PulledIdealNaiveQuasiIso
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedNaiveMapConormal
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceNaiveTruncation

/-!
# The pulled-back ideal of a first order thickening in the naive cotangent complex

Let `t : S ⟶ S'` be a first order thickening of ringed spaces with ideal sheaf `𝒥`, and
`f : X ⟶ S` a morphism. Write `A' = (f ∘ t)⁻¹𝒪_{S'}`, `A = f⁻¹𝒪_S`, `g : A' ⟶ A` and
`h : A ⟶ 𝒪_X` for the tower of Tag 08T4. The pulled-back ideal `f^* t^* 𝒥` is the conormal
sheaf of `g` extended to `𝒪_X` (`AlgebraicGeometry.RingedSpaceThickening.pulledIdealConormalIso`),
the conormal sheaf of `g` maps to degree `-1` of `NL_{A/A'}`, and
`CategoryTheory.Sheaf.baseChangedNaiveMap` maps `NL_{A/A'} ⊗_A 𝒪_X` to `NL_{𝒪_X/A'}`. This file
computes the composite `f^* t^* 𝒥 ⟶ NL_{𝒪_X/A'}.X (-1)` on sections, after transposing along
`(f ∘ t)^* ⊣ (f ∘ t)_*`: a section `s` of `𝒪_{S'}` killed by `t^♯` goes to the conormal class of
the coefficient image of `s` for the canonical presentation `A'[𝒪_X] ⟶ 𝒪_X`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.transpose_pulledIdealBaseNaiveMap_eqToHom`.
* `AlgebraicGeometry.RingedSpaceThickening.baseChangedNaiveComparison_comp_towerNaiveMap`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction inverseImageSheaf)
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap structureModules)

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}}

/-- For an isomorphism `e : M ≅ N` of sheaves of modules, `e.hom` undoes `e.inv` on sections. -/
theorem iso_hom_val_app_inv_val_app {R : Sheaf J RingCat.{max u v w}}
    {M N : _root_.SheafOfModules.{max u v w} R} (e : M ≅ N) (U : Cᵒᵖ) (x : N.val.obj U) :
    e.hom.val.app U (e.inv.val.app U x) = x :=
  (congrArg (fun z : N ⟶ N => z.val.app U x) e.inv_hom_id).trans rfl

/-- For an isomorphism `e : M ≅ N` of sheaves of modules, `e.inv` undoes `e.hom` on sections. -/
theorem iso_inv_val_app_hom_val_app {R : Sheaf J RingCat.{max u v w}}
    {M N : _root_.SheafOfModules.{max u v w} R} (e : M ≅ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x :=
  (congrArg (fun z : M ⟶ M => z.val.app U x) e.hom_inv_id).trans rfl

/-- Transport of the canonical map `L_{B/A} ⟶ NL_{B/A}` of Tag 08US along an equality of
structure maps. -/
theorem canonicalNaiveComparison_comp_eqToHom {k k' : A ⟶ B} (e : k = k') :
    canonicalNaiveComparison.{u, v, w} J k ≫
        eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u}
          J A B k) e) =
      eqToHom (congrArg (fun k => cotangentComplex.{u, v, w} J k) e) ≫
        canonicalNaiveComparison.{u, v, w} J k' := by
  subst e
  simp

/-- Transport of the classes of `naiveConormalClass` along an equality of structure maps. -/
theorem eqToHom_naiveConormalClass {k k' : A ⟶ B} (e : k = k') (U : Cᵒᵖ) (r : A.obj.obj U)
    (hr : (k.hom.app U).hom r = 0) (hr' : (k'.hom.app U).hom r = 0) :
    ((eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u}
        J A B k) e)).f (-1)).val.app U (naiveConormalClass.{u, v, w} J k U
          (coefficientRelation.{u, v, w} J k U r hr)) =
      naiveConormalClass.{u, v, w} J k' U (coefficientRelation.{u, v, w} J k' U r hr') := by
  subst e
  rfl

/-- `naiveConormalClass` is the conormal class read through the identification of the degree
`-1` term of the two-term complex `NL_{B/A}`. -/
theorem naiveConormalClass_eq_doubleXIso₀_inv (k : A ⟶ B) (U : Cᵒᵖ)
    (z : Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B k).hom U) :
    naiveConormalClass.{u, v, w} J k U z =
      ((HomologicalComplex.doubleXIso₀
        (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J A B k).f
        ComplexShape.upIntRelNegOneZero).inv.val.app U)
        (Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ B
          (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
            (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
          (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B k) U z) :=
  rfl

/-- The class of the coefficient image of a local section `r` of `A` killed by `k`, read back in
the conormal sheaf of the canonical presentation `A[B] ⟶ B`. -/
theorem doubleXIso₀_hom_naiveConormalClass_coefficientRelation (k : A ⟶ B) (U : Cᵒᵖ)
    (r : A.obj.obj U) (hr : (k.hom.app U).hom r = 0)
    (h : ((Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)).hom.app U).hom r ∈
      Stacks.Sites.Conormal.kernelIdeal
        (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B k).hom U) :
    ((HomologicalComplex.doubleXIso₀
        (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J A B k).f
        ComplexShape.upIntRelNegOneZero).hom.val.app U)
      (naiveConormalClass.{u, v, w} J k U (coefficientRelation.{u, v, w} J k U r hr)) =
      Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
          (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
        (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B k) U ⟨_, h⟩ := by
  rw [naiveConormalClass_eq_doubleXIso₀_inv]
  refine (iso_hom_val_app_inv_val_app J _ U _).trans ?_
  exact congrArg _ (Subtype.ext (coefficientRelation_coe.{u, v, w} J k U r hr))

end CategoryTheory.Sheaf

namespace Stacks.SheafOfModules

variable {Y : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
  (a : A ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) a.hom]

/-- The map from the conormal sheaf of a locally surjective `a : A ⟶ B` to degree `-1` of
`NL_{B/A}` sends the class of a local relation `r` to the class of its coefficient image. -/
theorem trivialConormalSequence_f_conormalClass (U : (Opens Y)ᵒᵖ)
    (r : Stacks.Sites.Conormal.kernelIdeal a.hom U) :
    (ShortComplex.mk _ _ (trivialConormalMap_comp_naiveCotangentComplex_d A B a)).f.val.app U
        (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} (Opens.grothendieckTopology Y) A A B
          (𝟙 A) a U r) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} (Opens.grothendieckTopology Y) a U
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} (Opens.grothendieckTopology Y) a U r.1
          r.2) := by
  have hmid := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, u, u}
    (Opens.grothendieckTopology Y) A B A
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf (Opens.grothendieckTopology Y) A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology Y) B))
    (𝟙 A) (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology Y) B))
    a (Stacks.Sites.FreeAlgebra.canonicalPresentation (Opens.grothendieckTopology Y) A B a)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology Y) B))
    (freeAlgebraSheafCoefficientMap_comp_presentation_id A B a) U r
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ hmid).trans ?_
  exact congrArg _ (congrArg _ (Subtype.ext
    (CategoryTheory.Sheaf.coefficientRelation_coe.{u, u, u} _ _ _ _ _).symm))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) {t : S ⟶ S'}


local notation "Jₓ" => Opens.grothendieckTopology X.carrier
local notation "hₓ" => Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f

/-- The transpose along `(f ∘ t)^* ⊣ (f ∘ t)_*` of a composite `c₁ ≫ c₂ ≫ φ`, on sections. -/
theorem homEquiv_comp_comp_val_app {I : SheafOfModules.{u} (structureSheafRing S')}
    {N₁ N₂ N₃ : SheafOfModules.{u} (structureSheafRing X)}
    (c₁ : (modulePullback (f ≫ t)).obj I ⟶ N₁) (c₂ : N₁ ⟶ N₂) (φ : N₂ ⟶ N₃)
    (V : (Opens S'.carrier)ᵒᵖ) (y : I.val.obj V) :
    ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _ (c₁ ≫ c₂ ≫ φ)).val.app V y =
      φ.val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _ (c₁ ≫ c₂)).val.app V y) := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

/-- **The map `f^* t^* 𝒥 ⟶ NL_{𝒪_X/A'}.X (-1)`**: the identification of `f^* t^* 𝒥` with the
extended conormal sheaf of `g`, the extended map of the conormal sheaf of `g` into degree `-1`
of `NL_{A/A'}`, and the map `NL_{A/A'} ⊗_A 𝒪_X ⟶ NL_{𝒪_X/A'}` in degree `-1`. -/
def pulledIdealBaseNaiveMap (ht : IsFirstOrderThickening t) :
    (modulePullback f).obj ((modulePullback t).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
      (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ
        (inverseImageSheaf (f ≫ t)) X.sheaf (baseStructureMap f t ≫ hₓ)).X (-1) :=
  pulledIdealNaiveMapNegOne f ht ≫
    (CategoryTheory.Sheaf.baseChangedNaiveMap.{u, u, u} Jₓ (baseStructureMap f t) hₓ).f (-1)

/-- The map from the conormal sheaf of `g` to degree `-1` of `NL_{A/A'}` sends the class of the
unit image of a section `s` of `𝒪_{S'}` killed by `t^♯` to the class of its coefficient image. -/
theorem baseConormalSequence_f_conormalClass (ht : IsFirstOrderThickening t)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    haveI := isLocallySurjective_baseStructureMap f ht.1
    (baseConormalSequence f ht).f.val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} Jₓ
          (inverseImageSheaf (f ≫ t)) (inverseImageSheaf (f ≫ t)) (inverseImageSheaf f) (𝟙 _)
          (baseStructureMap f t) (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
          ⟨(((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V).hom s,
            unit_mem_kernelIdeal f V s hs⟩) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ
        (baseStructureMap f t) (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ
          (baseStructureMap f t) _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s)
          (RingHom.mem_ker.1 (unit_mem_kernelIdeal f V s hs))) := by
  have := isLocallySurjective_baseStructureMap f ht.1
  exact Stacks.SheafOfModules.trivialConormalSequence_f_conormalClass _ _ _ _ _

/-- **The map `f^* t^* 𝒥 ⟶ NL_{𝒪_X/A'}.X (-1)` on sections.** Transposed along
`(f ∘ t)^* ⊣ (f ∘ t)_*` and `(f ∘ t)^* = f^* t^*`, it sends a section `s` of `𝒪_{S'}` killed by
`t^♯` to the conormal class, for the canonical presentation `A'[𝒪_X] ⟶ 𝒪_X`, of the coefficient
image of `s`. -/
theorem transpose_pulledIdealBaseNaiveMap (ht : IsFirstOrderThickening t)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
        ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫
          pulledIdealBaseNaiveMap f ht)).val.app V (baseIdealSection t V s hs) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ (baseStructureMap f t ≫ hₓ)
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ (baseStructureMap f t ≫ hₓ)
          _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s)
          ((congrArg ((hₓ).hom.app _).hom
            (RingHom.mem_ker.1 (unit_mem_kernelIdeal f V s hs))).trans (map_zero _))) := by
  have := isLocallySurjective_baseStructureMap f ht.1
  have hP2 := pulledIdealConormalIso_transpose_baseIdealSection f ht V s hs
  refine (homEquiv_comp_comp_val_app f
    ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t))
    (pulledIdealNaiveMapNegOne f ht)
    ((CategoryTheory.Sheaf.baseChangedNaiveMap.{u, u, u} Jₓ (baseStructureMap f t) hₓ).f (-1))
    V (baseIdealSection t V s hs)).trans ?_
  refine (congrArg (((CategoryTheory.Sheaf.baseChangedNaiveMap.{u, u, u} Jₓ (baseStructureMap f t)
      hₓ).f (-1)).val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop)))
    ((homEquiv_comp_comp_val_app f
      ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t))
      (pulledIdealConormalIso f ht).hom
      ((CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ).map (baseConormalSequence f ht).f)
      V (baseIdealSection t V s hs)).trans
      (congrArg (((CategoryTheory.Sheaf.towerExtendScalars.{u, u, u} Jₓ hₓ).map
        (baseConormalSequence f ht).f).val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop)))
        hP2))).trans ?_
  refine (congrArg _ (CategoryTheory.Sheaf.map_extendUnit.{u, u, u} Jₓ hₓ _ _ _)).trans ?_
  refine (congrArg (fun z => ((CategoryTheory.Sheaf.baseChangedNaiveMap.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ).f (-1)).val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
      (CategoryTheory.Sheaf.extendUnit.{u, u, u} Jₓ hₓ _ _ z))
    (baseConormalSequence_f_conormalClass f ht V s hs)).trans ?_
  exact CategoryTheory.Sheaf.baseChangedNaiveMap_naiveConormalClass.{u, u, u} Jₓ _ _ _ _ _

/-- `CategoryTheory.Sheaf.baseChangedNaiveMap` for the tower `A' ⟶ A ⟶ 𝒪_X`, read on the naive
cotangent complex of any spelling `k` of the composite `g ≫ h`. -/
def towerNaiveMapOf (t : S ⟶ S') (k : inverseImageSheaf (f ≫ t) ⟶ X.sheaf)
    (e : baseStructureMap f t ≫ hₓ = k) :
    CategoryTheory.Sheaf.baseChangedNaiveCotangentComplex.{u, u, u} Jₓ (baseStructureMap f t) hₓ ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ (inverseImageSheaf (f ≫ t))
        X.sheaf k :=
  CategoryTheory.Sheaf.baseChangedNaiveMap.{u, u, u} Jₓ (baseStructureMap f t) hₓ ≫
    eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ
      (inverseImageSheaf (f ≫ t)) X.sheaf k) e)

/-- **The map `NL_{A/A'} ⊗_A 𝒪_X ⟶ NL_{X/S'}`**: `CategoryTheory.Sheaf.baseChangedNaiveMap` for the
tower `A' ⟶ A ⟶ 𝒪_X`, read on `NL_{X/S'}` through `g ≫ h = (f ∘ t)⁻¹𝒪_{S'} ⟶ 𝒪_X`. -/
abbrev towerNaiveMap (t : S ⟶ S') :
    CategoryTheory.Sheaf.baseChangedNaiveCotangentComplex.{u, u, u} Jₓ (baseStructureMap f t) hₓ ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ (inverseImageSheaf (f ≫ t))
        X.sheaf (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t)) :=
  towerNaiveMapOf f t _ (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp f t)

/-- **The first arrow of Tag 08T4 followed by `L_{X/S'} ⟶ NL_{X/S'}` factors through
`L_{A/A'} ⊗_A 𝒪_X ⟶ NL_{A/A'} ⊗_A 𝒪_X`.** -/
theorem baseChangedNaiveComparison_comp_towerNaiveMap (t : S ⟶ S') :
    CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ (baseStructureMap f t) hₓ ≫
        towerNaiveMap f t =
      Stacks.Sheaves.RingedSpaceCotangent.cotangentBaseChange f t ≫
        Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison (f ≫ t) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (CategoryTheory.Sheaf.baseChangedNaiveComparison_comp_baseChangedNaiveMap.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ)).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (CategoryTheory.Sheaf.canonicalNaiveComparison_comp_eqToHom.{u, u, u} Jₓ
      (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp f t))).trans
    (Category.assoc _ _ _).symm)))

/-- `transpose_pulledIdealBaseNaiveMap`, transported along an equality `g ≫ h = k`. -/
theorem transpose_pulledIdealBaseNaiveMap_eqToHom (ht : IsFirstOrderThickening t)
    (k : inverseImageSheaf (f ≫ t) ⟶ X.sheaf) (e : baseStructureMap f t ≫ hₓ = k)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hk : (k.hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
      (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) = 0) :
    ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
        ((modulePullbackCompUniq f t).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf t) ≫
          pulledIdealBaseNaiveMap f ht ≫
          (eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ
            (inverseImageSheaf (f ≫ t)) X.sheaf k) e)).f (-1))).val.app V
        (baseIdealSection t V s hs) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ k
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ k
          _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) hk) := by
  subst e
  simp only [eqToHom_refl, HomologicalComplex.id_f]
  exact transpose_pulledIdealBaseNaiveMap f ht V s hs

/-- The map `f^* t^* 𝒥 ⟶ NL_{𝒪_X/A'}.X (-1)`, through `prescribedIdealMap`, sends a section `s`
of `𝒪_{S'}` killed by `t^♯` to the conormal class of the coefficient image of `s`. -/
theorem prescribedIdealMap_pulledIdealBaseNaiveMap (ht : IsFirstOrderThickening t)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    ((prescribedIdealMap (pulledIdealBaseNaiveMap f ht)).val.app V) (baseIdealSection t V s hs) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ (baseStructureMap f t ≫ hₓ)
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ (baseStructureMap f t ≫ hₓ)
          _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s)
          ((congrArg ((hₓ).hom.app _).hom
            (RingHom.mem_ker.1 (unit_mem_kernelIdeal f V s hs))).trans (map_zero _))) :=
  transpose_pulledIdealBaseNaiveMap f ht V s hs

/-- `prescribedIdealMap_pulledIdealBaseNaiveMap`, transported along an equality `g ≫ h = k`. -/
theorem prescribedIdealMap_pulledIdealBaseNaiveMap_eqToHom (ht : IsFirstOrderThickening t)
    (k : inverseImageSheaf (f ≫ t) ⟶ X.sheaf) (e : baseStructureMap f t ≫ hₓ = k)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hk : (k.hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
      (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) = 0) :
    ((prescribedIdealMap (pulledIdealBaseNaiveMap f ht ≫
        (eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ
          (inverseImageSheaf (f ≫ t)) X.sheaf k) e)).f (-1))).val.app V)
        (baseIdealSection t V s hs) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ k
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ k
          _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) hk) := by
  subst e
  simp only [eqToHom_refl, HomologicalComplex.id_f]
  exact prescribedIdealMap_pulledIdealBaseNaiveMap f ht V s hs

/-- The transpose of the pulled ideal followed by `towerNaiveMapOf` in degree `-1`. -/
theorem prescribedIdealMap_towerNaiveMapOf (ht : IsFirstOrderThickening t)
    (k : inverseImageSheaf (f ≫ t) ⟶ X.sheaf) (e : baseStructureMap f t ≫ hₓ = k)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hk : (k.hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
      (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) = 0) :
    ((prescribedIdealMap (pulledIdealNaiveMapNegOne f ht ≫
        (towerNaiveMapOf f t k e).f (-1))).val.app V)
        (baseIdealSection t V s hs) =
      CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ k
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ k
          _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) hk) := by
  subst e
  exact prescribedIdealMap_pulledIdealBaseNaiveMap f ht V s hs

/-- In degree `-1`, `pulledIdealNaiveMapNegOne` followed by `towerNaiveMapOf` is
`pulledIdealBaseNaiveMap` transported along `g ≫ h = k`. -/
theorem pulledIdealNaiveMapNegOne_comp_towerNaiveMapOf_f (ht : IsFirstOrderThickening t)
    (k : inverseImageSheaf (f ≫ t) ⟶ X.sheaf) (e : baseStructureMap f t ≫ hₓ = k) :
    pulledIdealNaiveMapNegOne f ht ≫ (towerNaiveMapOf f t k e).f (-1) =
      pulledIdealBaseNaiveMap f ht ≫
        (eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ
          (inverseImageSheaf (f ≫ t)) X.sheaf k) e)).f (-1) := by
  subst e
  simp only [towerNaiveMapOf, eqToHom_refl, HomologicalComplex.id_f]
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
