module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExteriorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerIsSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft

/-!
# The affine exterior-power comparison on a wedge of global sections

`AlgebraicGeometry.tildeExteriorPowerIso` compares the associated sheaf `(⋀ⁿ_R M)~` of the
`n`-th exterior power of an `R`-module `M` with the `n`-th exterior power `⋀ⁿ(M~)` of the
associated sheaf on `Spec R`. This file computes that comparison on the global sections which
determine it: the wedges `m₁ ∧ ⋯ ∧ mₙ` of elements of `M`.

## Main results

* `PresheafOfModules.homogeneousProd_exteriorAlgebraGen`: in the sectionwise exterior algebra of
  a presheaf of modules, the ordered product of the degree-one generators at local sections
  `s i` is the wedge `s₀ ∧ ⋯ ∧ s_{n-1}` of the degree-`n` sectionwise exterior power.
* `SheafOfModules.presheafModelExteriorPowerIso_ιMulti`: the presheaf-model comparison carries
  the unit-image of a wedge of local sections of a presheaf model to the ordered product of the
  degree-one generators of `⋀ⁿ F`.
* `AlgebraicGeometry.tildeExteriorPowerIso_hom_ιMulti`: **the comparison carries the global
  section `m₁ ∧ ⋯ ∧ mₙ` of `(⋀ⁿ_R M)~` to the ordered product of the degree-one generators of
  `⋀(M~)` at the global sections attached to the `mᵢ`.**

## Implementation notes

The ordered product in `AlgebraicGeometry.tildeExteriorPowerIso_hom_ιMulti` is written with
`Stacks.GradedAlgebra.homogeneousProdLeft`, the left-handed recursion `m₁ · (m₂ ⋯ mₙ)` the
source uses; the other results use the right-handed `Stacks.GradedAlgebra.homogeneousProd`, which
needs no transport along `1 + (n : ℤ) = ((n + 1 : ℕ) : ℤ)`.

Every statement about a sectionwise exterior power is written at
`PresheafOfModules.exteriorAlgebraPiece`, the `ℤ`-graded spelling the pieces of the sheafified
algebra come in, and never at the `ℕ`-graded `PresheafOfModules.extPow`: the two presheaves are
definitionally equal, but the sheafification *units* at the two spellings are components of an
adjunction built by `CategoryTheory.Adjunction.mkOfHomEquiv` and comparing them does not
elaborate. The implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerIsSheafification` record the same
constraint for the symmetric side.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace
open Stacks.AssociatedSheaf
open scoped TensorProduct

universe v u w a

/-! ### The sectionwise exterior algebra -/

namespace PresheafOfModules

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- In the sectionwise exterior algebra the ordered product of the degree-one generators at local
sections `s i` is, read in the exterior algebra of the sections, the wedge of the `s i`. -/
theorem exteriorAlgebraPieceVal_homogeneousProd_gen (X : Cᵒᵖ) (n : ℕ) :
    ∀ s : Fin n → F.obj X,
      exteriorAlgebraPieceVal (n : ℤ) F X
          ((exteriorAlgebraGradedAlgebra F).homogeneousProd X n
            fun i => Hom.app (exteriorAlgebraGen F) X (s i)) =
        ExteriorAlgebra.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s := by
  induction n with
  | zero =>
      intro s
      exact (exteriorAlgebraPieceVal_one F X).trans
        (ExteriorAlgebra.ιMulti_zero_apply s).symm
  | succ n ih =>
      intro s
      refine Eq.trans (exteriorAlgebraPieceVal_mul F (n : ℤ) 1 X
        ((exteriorAlgebraGradedAlgebra F).homogeneousProd X n
          fun i => Hom.app (exteriorAlgebraGen F) X (s i.castSucc))
        (Hom.app (exteriorAlgebraGen F) X (s (Fin.last n)))) ?_
      refine Eq.trans (congrArg₂ (· * ·) (ih fun i => s i.castSucc)
        (exteriorAlgebraPieceVal_gen F X (s (Fin.last n)))) ?_
      exact (ExteriorAlgebra.ιMulti_succ_last n s).symm

/-- The ordered product, in the sectionwise exterior algebra, of the degree-one generators
attached to local sections `s i` is the wedge `s₀ ∧ ⋯ ∧ s_{n-1}` of the degree-`n` sectionwise
exterior power. -/
theorem homogeneousProd_exteriorAlgebraGen (X : Cᵒᵖ) (n : ℕ) (s : Fin n → F.obj X) :
    (exteriorAlgebraGradedAlgebra F).homogeneousProd X n
        (fun i => Hom.app (exteriorAlgebraGen F) X (s i)) =
      exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s :=
  exteriorAlgebraPieceVal_injective (n : ℤ) F X
    ((exteriorAlgebraPieceVal_homogeneousProd_gen F X n s).trans
      (exteriorPower.ιMulti_apply_coe _ n s).symm)

end Sectionwise

end PresheafOfModules

/-! ### The presheaf-model comparison -/

namespace SheafOfModules

open PresheafOfModules Stacks.GradedAlgebra

/-- An isomorphism of sheaves of modules is sectionwise inverse on sections. -/
private theorem iso_inv_hom_apply_val {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {G H : SheafOfModules R} (e : G ≅ H) (X : Cᵒᵖ) (y : H.val.obj X) :
    e.hom.val.app X (e.inv.val.app X y) = y :=
  congrArg (fun k : H ⟶ H => k.val.app X y) e.inv_hom_id

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (P : PresheafOfModules.{w} (toRingCat J Osharp).obj)

/-- **The sheafification unit on an ordered product of degree-one local sections** of the
sectionwise exterior algebra of an arbitrary presheaf of modules. -/
theorem sheafifyUnit_homogeneousProd_exteriorModel (n : ℕ) (X : Cᵒᵖ)
    (z : Fin n → (exteriorAlgebraPiece (1 : ℤ) P).obj X) :
    Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (exteriorAlgebraPiece (n : ℤ) P)) X
        ((exteriorAlgebraGradedAlgebra P).homogeneousProd X n z) =
      ((exteriorAlgebraGradedAlgebra P).sheafify
          (𝟙 (toRingCat J Osharp).obj)).toPresheafGradedAlgebra.homogeneousProd X n
        (fun i => Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (exteriorAlgebraPiece (1 : ℤ) P)) X (z i)) :=
  (exteriorAlgebraGradedAlgebra P).homogeneousProd_map
    ((exteriorAlgebraGradedAlgebra P).sheafify
      (𝟙 (toRingCat J Osharp).obj)).toPresheafGradedAlgebra X
    (fun m y => Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
      (exteriorAlgebraPiece m P)) X y)
    ((exteriorAlgebraGradedAlgebra P).sheafify_one_eval
      (𝟙 (toRingCat J Osharp).obj) X).symm
    (fun i j x y => ((exteriorAlgebraGradedAlgebra P).sheafify_mul_unit
      (𝟙 (toRingCat J Osharp).obj) i j X x y).symm)
    n z

variable {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (A : TensorExteriorSymmetricAlgebras J F) (e : F ≅ sheafifyModulePresheaf J P)

/-- **The degree-one presheaf-model comparison on a sectionwise generator.** It carries the
unit-image of the sectionwise degree-one generator at a local section `p` of `P` to the
degree-one generator of the exterior algebra of `F` at the section of `F` that `p`
represents. -/
theorem presheafModelExteriorPowerIso_gen_unit (X : Cᵒᵖ) (p : P.obj X) :
    (presheafModelExteriorPowerIso J P A e 1).hom.val.app X
        (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (exteriorAlgebraPiece (1 : ℤ) P)) X (Hom.app (exteriorAlgebraGen P) X p)) =
      A.exteriorGenerator.val.app X
        (e.inv.val.app X
          (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj) P) X p)) := by
  set t : F.val.obj X :=
    e.inv.val.app X
      (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj) P) X p) with ht
  have hgen := congrArg
    (fun k : F ⟶ A.exterior.piece 1 => k.val.app X t)
    (presheafModelExteriorPowerIso_generator J P A e)
  refine Eq.trans ?_ hgen
  refine congrArg ((presheafModelExteriorPowerIso J P A e 1).hom.val.app X) ?_
  exact Eq.trans
    (((exteriorAlgebraGradedAlgebra P).sheafifyGen_unit (𝟙 (toRingCat J Osharp).obj)
      (exteriorAlgebraGen P) X p).symm)
    (congrArg (((exteriorAlgebraGradedAlgebra P).sheafifyGen
      (𝟙 (toRingCat J Osharp).obj) (exteriorAlgebraGen P)).val.app X)
      (iso_inv_hom_apply_val e X _).symm)

/-- **The presheaf-model comparison on a wedge of local sections.** For local sections `s i` of a
presheaf model `P` of `F`, the comparison carries the unit-image of `s₀ ∧ ⋯ ∧ s_{n-1}` to the
ordered product, in the exterior algebra of `F`, of the degree-one generators at the sections of
`F` that the `s i` represent. -/
theorem presheafModelExteriorPowerIso_ιMulti (n : ℕ) (X : Cᵒᵖ) (s : Fin n → P.obj X) :
    (presheafModelExteriorPowerIso J P A e (n : ℤ)).hom.val.app X
        (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
            (exteriorAlgebraPiece (n : ℤ) P)) X
          (exteriorPower.ιMulti
            ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) n s)) =
      A.exterior.toPresheafGradedAlgebra.homogeneousProd X n
        (fun i => A.exteriorGenerator.val.app X
          (e.inv.val.app X (Hom.app (PresheafOfModules.sheafifyUnit
            (𝟙 (toRingCat J Osharp).obj) P) X (s i)))) := by
  refine Eq.trans (congrArg ((presheafModelExteriorPowerIso J P A e (n : ℤ)).hom.val.app X)
    (Eq.trans (congrArg (Hom.app (PresheafOfModules.sheafifyUnit
        (𝟙 (toRingCat J Osharp).obj) (exteriorAlgebraPiece (n : ℤ) P)) X)
      (homogeneousProd_exteriorAlgebraGen P X n s).symm)
      (sheafifyUnit_homogeneousProd_exteriorModel J P n X
        fun i => Hom.app (exteriorAlgebraGen P) X (s i)))) ?_
  refine Eq.trans
    (((exteriorAlgebraGradedAlgebra P).sheafify
        (𝟙 (toRingCat J Osharp).obj)).toPresheafGradedAlgebra.homogeneousProd_map
      A.exterior.toPresheafGradedAlgebra X
      (fun m y => (presheafModelExteriorPowerIso J P A e m).hom.val.app X y)
      (presheafModelExteriorPowerIso_one J P A e X)
      (fun i j x y => presheafModelExteriorPowerIso_mul J P A e i j X x y) n _) ?_
  exact congrArg (A.exterior.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => presheafModelExteriorPowerIso_gen_unit J P A e X (s i))

end SheafOfModules

/-! ### The affine comparison -/

namespace AlgebraicGeometry

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

section Affine

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (p : ℕ)

/-- The comparison of Tag 01I7 carries the canonical global section of `N~` attached to `y : N`
to the unit-image of `1 ⊗ y`. -/
private theorem tildeExtModel_toOpen (N : ModuleCat.{u} R) (y : N) :
    (specTildeModel R N).hom.val.app (specGlobalOpen R) (tilde.toOpen N ⊤ y) =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
          (specTildePresheaf R N)) (specGlobalOpen R) (specTildePresheafUnit R N y) :=
  (tildeAssociatedSheafNatIso R).property N y

/-- The inverse of the comparison of Tag 01I7 carries the unit-image of `1 ⊗ y` back to the
canonical global section of `N~`. -/
private theorem tildeExtModel_inv_unit (N : ModuleCat.{u} R) (y : N) :
    (specTildeModel R N).inv.val.app (specGlobalOpen R)
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
          (specTildePresheaf R N)) (specGlobalOpen R) (specTildePresheafUnit R N y)) =
      tilde.toOpen N ⊤ y :=
  Eq.trans
    (congrArg ((specTildeModel R N).inv.val.app (specGlobalOpen R))
      (tildeExtModel_toOpen R N y).symm)
    (SheafOfModules.iso_inv_hom_apply_val (specTildeModel R N).symm _ _)

/-- The presheaf-level comparison on the global section `1 ⊗ (m₁ ∧ ⋯ ∧ mₚ)`: it is the wedge of
the sectionwise global sections `1 ⊗ mᵢ`. -/
private theorem specTildeExteriorPowerPresheafIso_unit_ιMulti (m : Fin p → ↥M) :
    PresheafOfModules.Hom.app (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M p).hom (specGlobalOpen R)
        (specTildePresheafUnit R (exteriorPowerSource R M p)
          (exteriorPower.ιMulti ↥R p m)) =
      exteriorPower.ιMulti
        ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) p
        (fun i => specTildePresheafUnit R M (m i)) := by
  let : Algebra ↥R ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) :=
    ((globalSectionsMap (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom).app
      (specGlobalOpen R)).hom.toAlgebra
  refine Subtype.ext ?_
  refine Eq.trans (ExteriorAlgebra.intPieceBaseChange_tmul ↥R
    ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M p 1
    (exteriorPower.ιMulti ↥R p m)) ?_
  refine congrArg Subtype.val ?_
  refine Eq.trans (one_smul ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R))
    (ExteriorAlgebra.exteriorPowerBaseChangeMap ↥R
      ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M p
      (exteriorPower.ιMulti ↥R p m))) ?_
  exact ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti ↥R
    ↥((Spec R).toRingedSpace.presheaf.obj (specGlobalOpen R)) ↥M p m

/-- The comparison on a global section of the algebraic exterior power: it is the presheaf-level
comparison at `1 ⊗ x`, followed by the sheafification unit and the presheaf-model comparison. -/
private theorem tildeExteriorPowerIso_hom_toOpen
    (x : ↥(⋀[↥R]^p ↥M)) :
    (tildeExteriorPowerIso R M p).hom.val.app (specGlobalOpen R)
        (tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^p ↥M)) ⊤ x) =
      (SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology ↥(Spec R))
          (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
          (p : ℤ)).hom.val.app (specGlobalOpen R)
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
            (PresheafOfModules.exteriorAlgebraPiece (p : ℤ) (specTildePresheaf R M)))
          (specGlobalOpen R)
          (PresheafOfModules.Hom.app (specTildeExteriorPowerPresheafIso R
              (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom M p).hom (specGlobalOpen R)
            (specTildePresheafUnit R (exteriorPowerSource R M p) x))) :=
  congrArg
    ((SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology ↥(Spec R))
      (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
      (p : ℤ)).hom.val.app (specGlobalOpen R))
    (Eq.trans
      (congrArg (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafification
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)).map
            (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
              (Scheme.ΓSpecIso R).inv.hom M p).hom).val (specGlobalOpen R))
        (tildeExtModel_toOpen R (exteriorPowerSource R M p) x))
      (PresheafOfModules.unit_naturality_apply
        (α := 𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
        (specTildeExteriorPowerPresheafIso R (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom M p).hom (specGlobalOpen R)
        (specTildePresheafUnit R (exteriorPowerSource R M p) x)))

/-- **The affine exterior-power comparison on a wedge of global sections.** The comparison
`(⋀ᵖ_R M)~ ≅ ⋀ᵖ(M~)` carries the global section of `(⋀ᵖ_R M)~` attached to `m₁ ∧ ⋯ ∧ mₚ` to the
ordered product, in the exterior algebra of `M~`, of the degree-one generators at the global
sections attached to the `mᵢ`. -/
theorem tildeExteriorPowerIso_hom_ιMulti (m : Fin p → ↥M) :
    (tildeExteriorPowerIso R M p).hom.val.app (op ⊤)
        (tilde.toOpen (ModuleCat.of ↥R ↥(⋀[↥R]^p ↥M)) ⊤ (exteriorPower.ιMulti ↥R p m)) =
      (specTildeAlgebras R M).exterior.toPresheafGradedAlgebra.homogeneousProdLeft (op ⊤) p
        (fun i => (specTildeAlgebras R M).exteriorGenerator.val.app (op ⊤)
          (tilde.toOpen M ⊤ (m i))) := by
  refine Eq.trans (tildeExteriorPowerIso_hom_toOpen R M p (exteriorPower.ιMulti ↥R p m)) ?_
  refine Eq.trans (congrArg (fun y =>
    (SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology ↥(Spec R))
        (specTildePresheaf R M) (specTildeAlgebras R M) (specTildeModel R M)
        (p : ℤ)).hom.val.app (specGlobalOpen R)
      (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (𝟙 (structureSheafRing (Spec R).toRingedSpace).obj)
          (PresheafOfModules.exteriorAlgebraPiece (p : ℤ) (specTildePresheaf R M)))
        (specGlobalOpen R) y))
    (specTildeExteriorPowerPresheafIso_unit_ιMulti R M p m)) ?_
  refine Eq.trans (SheafOfModules.presheafModelExteriorPowerIso_ιMulti
    (Opens.grothendieckTopology ↥(Spec R)) (specTildePresheaf R M) (specTildeAlgebras R M)
    (specTildeModel R M) p (specGlobalOpen R)
    (fun i => specTildePresheafUnit R M (m i))) ?_
  refine Eq.trans (congrArg
    ((specTildeAlgebras R M).exterior.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) p)
    (funext fun i => congrArg
      ((specTildeAlgebras R M).exteriorGenerator.val.app (specGlobalOpen R))
      (tildeExtModel_inv_unit R M (m i)))) ?_
  exact ((specTildeAlgebras R M).exterior.toPresheafGradedAlgebra
    |>.homogeneousProdLeft_eq_homogeneousProd (specGlobalOpen R) p
      (fun i => (specTildeAlgebras R M).exteriorGenerator.val.app (specGlobalOpen R)
        (tilde.toOpen M ⊤ (m i)))).symm

end Affine

end AlgebraicGeometry

end
