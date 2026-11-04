module

public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.TensorTotalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal map into the internal Hom of a tensor product

Let `(X, O_X)` be a ringed space and let `K` and `L` be complexes of `O_X`-modules. A local
section `k` of `K` in degree `n` sends a local section `l` of `L` in degree `p` to the pure
tensor `k ⊗ l`, a section of the total tensor product in degree `n + p`. These maps are the
components of a homogeneous local section of the internal Hom complex from `L` to the total
tensor product, and they assemble into a morphism of complexes
`K ⟶ SheafHom^•(L, Tot(K ⊗ L))`, natural in `K` and dinatural in `L`.

## Main definitions

* `Stacks.SheafOfModules.diagonalTensorHom`: the canonical morphism from `K` to the internal
  Hom complex from `L` to the total tensor product of `K` and `L`.

## Main results

* `Stacks.SheafOfModules.diagonalTensorHom_apply`: on homogeneous local sections the morphism
  is formation of the pure tensor.
* `Stacks.SheafOfModules.diagonalTensorHom_natural` (Stacks 0A8Q): its simultaneous naturality
  in both complexes.

## Implementation notes

Restricting a local section of a sheaf of modules to a smaller open lands, in Mathlib's
spelling, in a restriction of scalars of the module of sections there. `restrictSection` is
that restriction with the module of sections as its declared result type; the same device at
the level of the structure sheaf is `restrictScalar`.

The total tensor product is a degreewise sheafification, so a local pure tensor is the image
under the sheafification unit of a summand inclusion of the presheaf total complex; that
composite is `localTensorTotalSummand`.

A section of the internal Hom complex over `U` is a cochain on the slice site over `U`, so the
diagonal section is built from its components `slicePureTensorMap`, one for every object of
that slice.

## References

* [Stacks Project, Tag 0A8Q](https://stacks.math.columbia.edu/tag/0A8Q)
* [Stacks Project, Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open CochainComplex.HomComplex

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- The complex of `O_X(U)`-modules of sections over `U` of a complex of `O_X`-modules. -/
private noncomputable abbrev moduleSectionComplex
    (U : Opens X) (K : CochainComplex (StructureSheafModules Rc) ℤ) :
    CochainComplex (ModuleCat ((structureSheaf Rc).obj.obj (op U))) ℤ where
  X n := ModuleCat.of _ ((K.X n).val.obj (op U))
  d n m := (K.d n m).val.app (op U)
  shape n m h := congrArg (fun f => f.val.app (op U)) (K.shape n m h)
  d_comp_d' i j k hij hjk := by
    change ((K.d i j).val.app (op U) ≫ (K.d j k).val.app (op U)) = 0
    exact congrArg (fun f : K.X i ⟶ K.X k => f.val.app (op U))
      (K.d_comp_d' i j k hij hjk)

/-- Restriction of a local section of a sheaf of `O_X`-modules to a smaller open, with the
sections over that open as declared result type. -/
private noncomputable abbrev restrictSection (M : StructureSheafModules Rc) {U W : Opens X}
    (hWU : W ≤ U) (s : (M.val.obj (op U) : ModuleCat _)) : (M.val.obj (op W) : ModuleCat _) :=
  M.val.map (homOfLE hWU).op s

/-- Restriction of a local section of the structure sheaf of rings to a smaller open. -/
private noncomputable abbrev restrictScalar {U W : Opens X} (hWU : W ≤ U)
    (r : ((structureSheaf Rc).obj.obj (op U) : RingCat)) :
    ((structureSheaf Rc).obj.obj (op W) : RingCat) :=
  (structureSheaf Rc).obj.map (homOfLE hWU).op r

/-- Restriction of sections is additive. -/
private lemma restrictSection_add (M : StructureSheafModules Rc) {U W : Opens X} (hWU : W ≤ U)
    (s t : (M.val.obj (op U) : ModuleCat _)) :
    restrictSection Rc M hWU (s + t) =
      restrictSection Rc M hWU s + restrictSection Rc M hWU t :=
  map_add _ _ _

/-- Restriction of sections is semilinear over restriction of scalars. -/
private lemma restrictSection_smul (M : StructureSheafModules Rc) {U W : Opens X} (hWU : W ≤ U)
    (r : ((structureSheaf Rc).obj.obj (op U) : RingCat))
    (s : (M.val.obj (op U) : ModuleCat _)) :
    restrictSection Rc M hWU (r • s) =
      restrictScalar Rc hWU r • restrictSection Rc M hWU s :=
  PresheafOfModules.map_smul M.val (homOfLE hWU).op r s

/-- Restricting twice is restricting once. -/
private lemma restrictSection_comp (M : StructureSheafModules Rc) {U V W : Opens X}
    (hWV : W ≤ V) (hVU : V ≤ U) (s : (M.val.obj (op U) : ModuleCat _)) :
    restrictSection Rc M hWV (restrictSection Rc M hVU s) =
      restrictSection Rc M (hWV.trans hVU) s :=
  (PresheafOfModules.map_comp_apply M.val (homOfLE hVU).op (homOfLE hWV).op s).symm

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
private lemma restrictSection_map {M N : StructureSheafModules Rc} (f : M ⟶ N)
    {U W : Opens X} (hWU : W ≤ U) (s : (M.val.obj (op U) : ModuleCat _)) :
    (f.val.app (op W)) (restrictSection Rc M hWU s) =
      restrictSection Rc N hWU (f.val.app (op U) s) :=
  PresheafOfModules.naturality_apply f.val (homOfLE hWU).op s

/-- Evaluating a sign-scaled morphism of presheaves of modules on an open set scales the
value by the same sign. -/
private theorem presheaf_units_smul_app
    (z : ℤˣ) {A B : PresheafOfModules.{u} (structureSheaf Rc).obj}
    (f : A ⟶ B) (U : Opens X) :
    (z • f).app (op U) = z • f.app (op U) := by
  rw [Units.smul_def, Units.smul_def, PresheafOfModules.zsmul_app]

/-- The total complex of the tensor-product double complex of the underlying presheaves. -/
private noncomputable abbrev presheafTotalComplex
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) :=
  HomologicalComplex.mapBifunctor (underlyingComplex Rc K) (underlyingComplex Rc L)
    (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)) (ComplexShape.up ℤ)

/-- Over an open set `U`, the inclusion of the bidegree `(n, p)` summand into the total tensor
product: the summand inclusion of the presheaf total complex followed by the sheafification
unit. -/
private noncomputable def localTensorTotalSummand
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p q : ℤ) (hnpq : n + p = q) :
    (K.X n).val.obj (op U) ⊗ (L.X p).val.obj (op U) ⟶
      ((tensorTotal Rc K L).X q).val.obj (op U) :=
  ((HomologicalComplex.ιTensorObj (underlyingComplex Rc K) (underlyingComplex Rc L)
      n p q hnpq).app (op U)) ≫
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
      ((presheafTotalComplex Rc K L).X q)).app (op U))

/-- The summand inclusion sends a pure tensor to the corresponding local pure tensor. -/
private theorem localTensorTotalSummand_tmul
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p : ℤ) (k : (K.X n).val.obj (op U)) (l : (L.X p).val.obj (op U)) :
    (localTensorTotalSummand Rc U K L n p (n + p) rfl).hom
      (k ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] l) =
    tensorTotalSection Rc K L U n p k l := rfl

/-- On the bidegree `(n, p)` summand the differential of the total tensor product is
`d_K(k) ⊗ l + (-1)^n k ⊗ d_L(l)`. -/
private theorem localTensorTotalSummand_d
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ) (n p : ℤ) :
    localTensorTotalSummand Rc U K L n p (n + p) rfl ≫
        (moduleSectionComplex Rc U (tensorTotal Rc K L)).d (n + p) (n + p + 1) =
      ((moduleSectionComplex Rc U K).d n (n + 1) ▷
        (moduleSectionComplex Rc U L).X p) ≫
          localTensorTotalSummand Rc U K L (n + 1) p (n + p + 1) (by omega) +
      n.negOnePow •
        (((moduleSectionComplex Rc U K).X n ◁
          (moduleSectionComplex Rc U L).d p (p + 1)) ≫
          localTensorTotalSummand Rc U K L n (p + 1) (n + p + 1) (by omega)) := by
  let P := presheafTotalComplex Rc K L
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf Rc).obj)).unit
  have hP :
      HomologicalComplex.ιTensorObj (underlyingComplex Rc K) (underlyingComplex Rc L)
          n p (n + p) rfl ≫ P.d (n + p) (n + p + 1) =
        (((underlyingComplex Rc K).d n (n + 1) ▷ (underlyingComplex Rc L).X p) ≫
            HomologicalComplex.ιTensorObj (underlyingComplex Rc K)
              (underlyingComplex Rc L) (n + 1) p (n + p + 1) (by omega)) +
          n.negOnePow •
            (((underlyingComplex Rc K).X n ◁ (underlyingComplex Rc L).d p (p + 1)) ≫
              HomologicalComplex.ιTensorObj (underlyingComplex Rc K)
                (underlyingComplex Rc L) n (p + 1) (n + p + 1) (by omega)) := by
    dsimp [P, presheafTotalComplex]
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) _ _
        (by change (n + 1) + p = n + p + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) _
        (by change n + (p + 1) = n + p + 1; omega)]
    simp only [ComplexShape.ε₁, TotalComplexShape.ε₁, one_smul,
      MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight]
    rfl
  dsimp [localTensorTotalSummand, moduleSectionComplex, tensorTotal, presheafTotalComplex]
  let T := PresheafOfModules.sheafification (𝟙 (structureSheaf Rc).obj) ⋙
    SheafOfModules.forget (structureSheaf Rc) ⋙
      PresheafOfModules.restrictScalars (𝟙 (structureSheaf Rc).obj)
  change
    ((HomologicalComplex.ιTensorObj (underlyingComplex Rc K) (underlyingComplex Rc L)
        n p (n + p) rfl).app (op U) ≫
      (η.app (P.X (n + p))).app (op U)) ≫
        (T.map (P.d (n + p) (n + p + 1))).app (op U) = _
  have hPU := congrArg (fun f => f.app (op U)) hP
  rw [PresheafOfModules.comp_app, PresheafOfModules.add_app,
    presheaf_units_smul_app] at hPU
  have hη := congrArg (fun f => f.app (op U)) (η.naturality (P.d (n + p) (n + p + 1)))
  change (P.d (n + p) (n + p + 1)).app (op U) ≫
      (η.app (P.X (n + p + 1))).app (op U) =
    (η.app (P.X (n + p))).app (op U) ≫
      (T.map (P.d (n + p) (n + p + 1))).app (op U) at hη
  rw [Category.assoc, ← hη, ← Category.assoc, hPU]
  simp only [Preadditive.add_comp, Units.smul_def, Preadditive.zsmul_comp]
  rfl

/-- The differential formula of `localTensorTotalSummand_d` at an arbitrary total degree. -/
private theorem localTensorTotalSummand_d_of_eq
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p q : ℤ) (hnpq : n + p = q) :
    localTensorTotalSummand Rc U K L n p q hnpq ≫
        (moduleSectionComplex Rc U (tensorTotal Rc K L)).d q (q + 1) =
      ((moduleSectionComplex Rc U K).d n (n + 1) ▷
        (moduleSectionComplex Rc U L).X p) ≫
          localTensorTotalSummand Rc U K L (n + 1) p (q + 1) (by omega) +
      n.negOnePow •
        (((moduleSectionComplex Rc U K).X n ◁
          (moduleSectionComplex Rc U L).d p (p + 1)) ≫
          localTensorTotalSummand Rc U K L n (p + 1) (q + 1) (by omega)) := by
  subst q
  exact localTensorTotalSummand_d Rc U K L n p

/-- On the bidegree `(n, p)` summand, a morphism of total tensor products induced by two chain
maps is the tensor product of their components. -/
private theorem localTensorTotalSummand_natural
    (U : Opens X) {K K' L L' : CochainComplex (StructureSheafModules Rc) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (n p q : ℤ) (hnpq : n + p = q) :
    localTensorTotalSummand Rc U K L n p q hnpq ≫
        ((tensorTotalMap Rc f g).f q).val.app (op U) =
      ((f.f n).val.app (op U) ⊗ₘ (g.f p).val.app (op U)) ≫
        localTensorTotalSummand Rc U K' L' n p q hnpq := by
  subst q
  exact ModuleCat.hom_ext (TensorProduct.ext' (tensorTotalMap_section Rc f g U n p))

/-- Local pure tensors are compatible with restriction to a smaller open. -/
private theorem localTensorTotalSummand_restrict
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) {U W : Opens X} (hWU : W ≤ U)
    (n p q : ℤ) (hnpq : n + p = q)
    (a : (K.X n).val.obj (op U)) (b : (L.X p).val.obj (op U)) :
    (localTensorTotalSummand Rc W K L n p q hnpq).hom
        (restrictSection Rc (K.X n) hWU a ⊗ₜ[(structureSheaf Rc).obj.obj (op W)]
          restrictSection Rc (L.X p) hWU b) =
      restrictSection Rc ((tensorTotal Rc K L).X q) hWU
        ((localTensorTotalSummand Rc U K L n p q hnpq).hom
          (a ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] b)) := by
  refine Eq.trans (congrArg (fun z => (localTensorTotalSummand Rc W K L n p q hnpq).hom z)
    (PresheafOfModules.Monoidal.tensorObj_map_tmul (homOfLE hWU).op a b).symm) ?_
  exact PresheafOfModules.naturality_apply
    (HomologicalComplex.ιTensorObj (underlyingComplex Rc K) (underlyingComplex Rc L)
        n p q hnpq ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
        ((presheafTotalComplex Rc K L).X q)) (homOfLE hWU).op
    (a ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] b)

/-- The component at an object `W` of the slice site over `U` of the degree-`n` local section
of the internal Hom complex determined by a section `k` of `K`: it sends `l` to the pure
tensor of `k|_W` with `l`. -/
private noncomputable def slicePureTensorMap
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p q : ℤ) (hnpq : n + p = q) (k : (K.X n).val.obj (op U)) :
    (restrictComplex Rc L U).X p ⟶
      (restrictComplex Rc (tensorTotal Rc K L) U).X q := by
  refine ⟨{ app := fun V => ?_, naturality := ?_ }⟩
  · let _ : CommRing (((structureSheaf Rc).over U).obj.obj V) :=
      inferInstanceAs (CommRing (Rc.obj.obj (op V.unop.left)))
    exact Stacks.HomComplex.TensorHomMap.tmulLeft _
        (restrictSection Rc (K.X n) (leOfHom V.unop.hom) k) ≫
      localTensorTotalSummand Rc V.unop.left K L n p q hnpq
  · intro V V' f
    apply ModuleCat.hom_ext
    ext l
    refine Eq.trans (congrArg (fun z =>
      (localTensorTotalSummand Rc V'.unop.left K L n p q hnpq).hom
        (z ⊗ₜ[(structureSheaf Rc).obj.obj (op V'.unop.left)]
          restrictSection Rc (L.X p) (leOfHom (unop f).left) l))
      (restrictSection_comp Rc (K.X n) (leOfHom (unop f).left)
        (leOfHom V.unop.hom) k).symm) ?_
    exact localTensorTotalSummand_restrict Rc K L (leOfHom (unop f).left) n p q hnpq
      (restrictSection Rc (K.X n) (leOfHom V.unop.hom) k) l

/-- The degree-`n` cochain on the slice site over `U` whose components are the pure-tensor
maps determined by a section `k` of `K`. -/
private noncomputable def sliceDiagonalCochain
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n : ℤ) (k : (K.X n).val.obj (op U)) :
    Cochain (restrictComplex Rc L U) (restrictComplex Rc (tensorTotal Rc K L) U) n :=
  Cochain.mk fun p q hpq => slicePureTensorMap Rc U K L n p q (by omega) k

/-- The component of the diagonal cochain at an object of the slice site, evaluated on a
local section of `L`. -/
private theorem slicePureTensorMap_app
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p q : ℤ) (hnpq : n + p = q) (k : (K.X n).val.obj (op U))
    {W : Opens X} (hWU : W ≤ U) (l : (L.X p).val.obj (op W)) :
    ((slicePureTensorMap Rc U K L n p q hnpq k).val.app (op (Over.mk (homOfLE hWU)))) l =
      (localTensorTotalSummand Rc W K L n p q hnpq).hom
        (restrictSection Rc (K.X n) hWU k ⊗ₜ[(structureSheaf Rc).obj.obj (op W)] l) := rfl

/-- The local section of the internal Hom complex corresponding to `sliceDiagonalCochain`. -/
private noncomputable def diagonalLocalHomSection
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n : ℤ) (k : (K.X n).val.obj (op U)) :
    ((sheafHomComplex Rc L (tensorTotal Rc K L)).obj.X n).val.obj (op U) :=
  (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).inv.f n)
    (sliceDiagonalCochain Rc U K L n k)

/-- The pure-tensor map is additive in the section of `K`. -/
private theorem slicePureTensorMap_add
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p q : ℤ) (hnpq : n + p = q)
    (k k' : (K.X n).val.obj (op U)) :
    slicePureTensorMap Rc U K L n p q hnpq (k + k') =
      slicePureTensorMap Rc U K L n p q hnpq k +
        slicePureTensorMap Rc U K L n p q hnpq k' := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rw [SheafOfModules.add_val, PresheafOfModules.add_app]
  show Stacks.HomComplex.TensorHomMap.tmulLeft _ (restrictSection Rc (K.X n) (leOfHom V.unop.hom)
    (k + k')) ≫
      localTensorTotalSummand Rc V.unop.left K L n p q hnpq =
    Stacks.HomComplex.TensorHomMap.tmulLeft _ (restrictSection Rc (K.X n) (leOfHom V.unop.hom) k) ≫
      localTensorTotalSummand Rc V.unop.left K L n p q hnpq +
    Stacks.HomComplex.TensorHomMap.tmulLeft _ (restrictSection Rc (K.X n) (leOfHom V.unop.hom) k') ≫
      localTensorTotalSummand Rc V.unop.left K L n p q hnpq
  rw [restrictSection_add, Stacks.HomComplex.TensorHomMap.tmulLeft_add, Preadditive.add_comp]

/-- The diagonal cochain is additive in the section of `K`. -/
private theorem sliceDiagonalCochain_add
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ)
    (k k' : (K.X n).val.obj (op U)) :
    sliceDiagonalCochain Rc U K L n (k + k') =
      sliceDiagonalCochain Rc U K L n k + sliceDiagonalCochain Rc U K L n k' := by
  apply Cochain.ext
  intro p q hpq
  exact slicePureTensorMap_add Rc U K L n p q (by omega) k k'

/-- The diagonal local Hom section is additive in the section of `K`. -/
private theorem diagonalLocalHomSection_add
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n : ℤ) (k k' : (K.X n).val.obj (op U)) :
    diagonalLocalHomSection Rc U K L n (k + k') =
      diagonalLocalHomSection Rc U K L n k + diagonalLocalHomSection Rc U K L n k' := by
  unfold diagonalLocalHomSection
  rw [sliceDiagonalCochain_add]
  exact map_add (AddCommGrpCat.Hom.hom
    (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).inv.f n)) _ _

/-- Evaluating a sign-scaled morphism of sheaves of modules on an object scales the value by
the same sign. -/
private theorem sheaf_units_smul_app
    {C : Type*} [Category C] {J : GrothendieckTopology C} (R : Sheaf J RingCat)
    {A B : SheafOfModules R} (z : ℤˣ) (f : A ⟶ B) (V : Cᵒᵖ) :
    (z • f).val.app V = z • f.val.app V := by
  have : (SheafOfModules.evaluation R V).Additive := { map_add := by intros; rfl }
  show (SheafOfModules.evaluation R V).map (z • f) =
    z • (SheafOfModules.evaluation R V).map f
  exact Functor.map_units_smul _ _ _

/-- The pure-tensor maps satisfy the Leibniz rule for the differentials of `K` and `L`. -/
private theorem slicePureTensorMap_d
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n p q : ℤ) (hnpq : n + p = q) (k : (K.X n).val.obj (op U)) :
    slicePureTensorMap Rc U K L n p q hnpq k ≫
        (restrictComplex Rc (tensorTotal Rc K L) U).d q (q + 1) =
      slicePureTensorMap Rc U K L (n + 1) p (q + 1) (by omega)
          ((K.d n (n + 1)).val.app (op U) k) +
        n.negOnePow • ((restrictComplex Rc L U).d p (p + 1) ≫
          slicePureTensorMap Rc U K L n (p + 1) (q + 1) (by omega) k) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rw [SheafOfModules.add_val, PresheafOfModules.add_app, sheaf_units_smul_app]
  show (Stacks.HomComplex.TensorHomMap.tmulLeft _ (restrictSection Rc (K.X n) (leOfHom V.unop.hom)
    k) ≫
      localTensorTotalSummand Rc V.unop.left K L n p q hnpq) ≫
      (moduleSectionComplex Rc V.unop.left (tensorTotal Rc K L)).d q (q + 1) =
    (Stacks.HomComplex.TensorHomMap.tmulLeft ((structureSheaf Rc).obj.obj (op V.unop.left))
      (Kn := (K.X (n + 1)).val.obj (op V.unop.left))
      (restrictSection Rc (K.X (n + 1)) (leOfHom V.unop.hom)
        ((K.d n (n + 1)).val.app (op U) k)) ≫
        localTensorTotalSummand Rc V.unop.left K L (n + 1) p (q + 1) (by omega) +
      n.negOnePow • ((L.d p (p + 1)).val.app (op V.unop.left) ≫
        Stacks.HomComplex.TensorHomMap.tmulLeft _ (restrictSection Rc (K.X n) (leOfHom V.unop.hom)
          k) ≫
          localTensorTotalSummand Rc V.unop.left K L n (p + 1) (q + 1) (by omega)))
  rw [Category.assoc, localTensorTotalSummand_d_of_eq,
    Preadditive.comp_add, ← Category.assoc,
      Stacks.HomComplex.TensorHomMap.tmulLeft_comp_whiskerRight,
    Linear.comp_units_smul, ← Category.assoc,
      Stacks.HomComplex.TensorHomMap.tmulLeft_comp_whiskerLeft,
    Category.assoc, restrictSection_map]

/-- The differential of the diagonal cochain is the diagonal cochain of the differential. -/
private theorem sliceDiagonalCochain_d
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n : ℤ) (k : (K.X n).val.obj (op U)) :
    δ n (n + 1) (sliceDiagonalCochain Rc U K L n k) =
      sliceDiagonalCochain Rc U K L (n + 1) ((K.d n (n + 1)).val.app (op U) k) := by
  apply Cochain.ext
  intro p q hpq
  rw [δ_v n (n + 1) rfl _ p q hpq (n + p) (p + 1) (by omega) rfl]
  obtain rfl : q = n + p + 1 := by omega
  show slicePureTensorMap Rc U K L n p (n + p) rfl k ≫
      (restrictComplex Rc (tensorTotal Rc K L) U).d (n + p) (n + p + 1) +
      (n + 1).negOnePow • ((restrictComplex Rc L U).d p (p + 1) ≫
        slicePureTensorMap Rc U K L n (p + 1) (n + p + 1) (by omega) k) = _
  rw [slicePureTensorMap_d, Int.negOnePow_succ, Units.neg_smul]
  exact add_neg_cancel_right _ _

/-- The pure-tensor maps are natural in `K` and dinatural in `L`. -/
private theorem slicePureTensorMap_natural
    (U : Opens X) {K K' L L' : CochainComplex (StructureSheafModules Rc) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (n p q : ℤ) (hnpq : n + p = q)
    (k : (K.X n).val.obj (op U)) :
    slicePureTensorMap Rc U K L n p q hnpq k ≫ ((tensorTotalMap Rc f g).f q).over U =
      (g.f p).over U ≫ slicePureTensorMap Rc U K' L' n p q hnpq
        ((f.f n).val.app (op U) k) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  show (Stacks.HomComplex.TensorHomMap.tmulLeft _ (restrictSection Rc (K.X n) (leOfHom V.unop.hom)
    k) ≫
      localTensorTotalSummand Rc V.unop.left K L n p q hnpq) ≫
      ((tensorTotalMap Rc f g).f q).val.app (op V.unop.left) =
    (g.f p).val.app (op V.unop.left) ≫
      Stacks.HomComplex.TensorHomMap.tmulLeft ((structureSheaf Rc).obj.obj (op V.unop.left))
        (Kn := (K'.X n).val.obj (op V.unop.left))
        (restrictSection Rc (K'.X n) (leOfHom V.unop.hom)
          ((f.f n).val.app (op U) k)) ≫
      localTensorTotalSummand Rc V.unop.left K' L' n p q hnpq
  rw [Category.assoc, localTensorTotalSummand_natural, ← Category.assoc,
    Stacks.HomComplex.TensorHomMap.tmulLeft_comp_tensorHom, Category.assoc, restrictSection_map]

/-- Two local sections of an internal Hom complex agree as soon as all components of the
corresponding cochains agree. -/
private theorem homSection_ext
    {A B : CochainComplex (StructureSheafModules Rc) ℤ} (H : SheafHomComplex Rc A B)
    (U : Opens X) (n : ℤ) (s t : (H.obj.X n).val.obj (op U))
    (h : ∀ (p q : ℤ) (hpq : p + n = q) (W : Opens X) (hWU : W ≤ U)
      (x : (A.X p).val.obj (op W)),
      ((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq).val.app
          (op (Over.mk (homOfLE hWU))) x =
        ((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) t).v p q hpq).val.app
          (op (Over.mk (homOfLE hWU))) x) : s = t := by
  apply (AddCommGrpCat.mono_iff_injective ((H.sectionsIso U).hom.f n)).mp inferInstance
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext V x
  exact h p q hpq V.unop.left (leOfHom V.unop.hom) x

/-- The cochain attached to the diagonal local Hom section is the diagonal cochain. -/
private theorem diagonalLocalHomSection_cochain
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n : ℤ) (k : (K.X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom
      (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).hom.f n)
        (diagonalLocalHomSection Rc U K L n k) =
      sliceDiagonalCochain Rc U K L n k := by
  show (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).inv.f n ≫
    ((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).hom.f n)
      (sliceDiagonalCochain Rc U K L n k) = _
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id]
  rfl

/-- The diagonal local Hom section is `O_X(U)`-linear in the section of `K`. -/
private theorem diagonalLocalHomSection_smul
    (U : Opens X) (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (n : ℤ) (r : (structureSheaf Rc).obj.obj (op U)) (k : (K.X n).val.obj (op U)) :
    diagonalLocalHomSection Rc U K L n (r • k) =
      r • diagonalLocalHomSection Rc U K L n k := by
  apply homSection_ext Rc (sheafHomComplex Rc L (tensorTotal Rc K L))
  intro p q hpq W hWU x
  rw [(sheafHomComplex Rc L (tensorTotal Rc K L)).smul_natural]
  simp only [diagonalLocalHomSection_cochain, sliceDiagonalCochain, Cochain.mk_v]
  rw [slicePureTensorMap_app, slicePureTensorMap_app, restrictSection_smul]
  refine Eq.trans (congrArg
    (ModuleCat.Hom.hom (localTensorTotalSummand Rc W K L n p q (by omega)))
    (TensorProduct.smul_tmul' (restrictScalar Rc hWU r)
      (restrictSection Rc (K.X n) hWU k) x)) ?_
  exact LinearMap.map_smul
    (ModuleCat.Hom.hom (localTensorTotalSummand Rc W K L n p q (by omega)))
    (restrictScalar Rc hWU r)
    (restrictSection Rc (K.X n) hWU k ⊗ₜ[(structureSheaf Rc).obj.obj (op W)] x)

/-- The diagonal local Hom sections are compatible with restriction to a smaller open. -/
private theorem diagonalLocalHomSection_restrict
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) {U V : Opens X} (hVU : V ≤ U)
    (n : ℤ) (k : (K.X n).val.obj (op U)) :
    restrictSection Rc ((sheafHomComplex Rc L (tensorTotal Rc K L)).obj.X n) hVU
        (diagonalLocalHomSection Rc U K L n k) =
      diagonalLocalHomSection Rc V K L n (restrictSection Rc (K.X n) hVU k) := by
  refine homSection_ext Rc (sheafHomComplex Rc L (tensorTotal Rc K L)) V n _ _ ?_
  intro p q hpq W hWV x
  rw [← (sheafHomComplex Rc L (tensorTotal Rc K L)).restrict_natural hVU]
  simp only [diagonalLocalHomSection_cochain, sliceDiagonalCochain, Cochain.mk_v]
  rw [slicePureTensorMap_app, slicePureTensorMap_app, restrictSection_comp]

/-- The degree-`n` component of the diagonal morphism. -/
private noncomputable def diagonalDegree
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ) :
    K.X n ⟶ (sheafHomComplex Rc L (tensorTotal Rc K L)).obj.X n :=
  ⟨{ app := fun U => ModuleCat.ofHom {
       toFun := diagonalLocalHomSection Rc U.unop K L n
       map_add' := diagonalLocalHomSection_add Rc U.unop K L n
       map_smul' := diagonalLocalHomSection_smul Rc U.unop K L n }
     naturality := by
       intro U V f
       ext x
       exact (diagonalLocalHomSection_restrict Rc K L (leOfHom f.unop) n x).symm }⟩

/-- The components of the diagonal morphism commute with the differentials. -/
private theorem diagonalDegree_comm
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ) :
    diagonalDegree Rc K L n ≫
        (sheafHomComplex Rc L (tensorTotal Rc K L)).obj.d n (n + 1) =
      K.d n (n + 1) ≫ diagonalDegree Rc K L (n + 1) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext k
  let H := sheafHomComplex Rc L (tensorTotal Rc K L)
  apply (AddCommGrpCat.mono_iff_injective ((H.sectionsIso U.unop).hom.f (n + 1))).mp
    inferInstance
  have hc := congrArg (fun f => f (diagonalLocalHomSection Rc U.unop K L n k))
    ((H.sectionsIso U.unop).hom.comm n (n + 1))
  change δ n (n + 1) (AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f n)
      (diagonalLocalHomSection Rc U.unop K L n k)) =
    AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f (n + 1))
      ((H.obj.d n (n + 1)).val.app U (diagonalLocalHomSection Rc U.unop K L n k)) at hc
  show AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f (n + 1))
      ((H.obj.d n (n + 1)).val.app U (diagonalLocalHomSection Rc U.unop K L n k)) =
    AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f (n + 1))
      (diagonalLocalHomSection Rc U.unop K L (n + 1) ((K.d n (n + 1)).val.app U k))
  rw [← hc]
  dsimp only [H]
  rw [diagonalLocalHomSection_cochain, diagonalLocalHomSection_cochain,
    sliceDiagonalCochain_d]

/-- There is a morphism of complexes whose effect on homogeneous local sections is formation
of the pure tensor. -/
theorem diagonalTensorHom_exists
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) :
    ∃ d : K ⟶ (sheafHomComplex Rc L (tensorTotal Rc K L)).obj,
    ∀ (U : Opens X) (n p : ℤ) (k : (K.X n).val.obj (op U))
      (l : (L.X p).val.obj (op U)) (hpq : p + n = n + p),
      applyHomSection Rc (sheafHomComplex Rc L (tensorTotal Rc K L))
        U n p (n + p) hpq ((d.f n).val.app (op U) k) l =
      tensorTotalSection Rc K L U n p k l := by
  refine ⟨{ f := diagonalDegree Rc K L, comm' := ?_ }, ?_⟩
  · intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    exact diagonalDegree_comm Rc K L n
  · intro U n p k l hpq
    show ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).hom.f n)
      (diagonalLocalHomSection Rc U K L n k)).v p (n + p) (by omega)).val.app
        (op (Over.mk (𝟙 U))) l = _
    rw [diagonalLocalHomSection_cochain]
    show (localTensorTotalSummand Rc U K L n p (n + p) rfl).hom
      (restrictSection Rc (K.X n) (le_refl U) k ⊗ₜ[_] l) = _
    have hid : restrictSection Rc (K.X n) (le_refl U) k = k := by
      show ((K.X n).val.map (𝟙 (op U))) k = k
      rw [PresheafOfModules.map_id]
      rfl
    rw [hid]
    exact localTensorTotalSummand_tmul Rc U K L n p k l

/-- The diagonal morphism sends a homogeneous section `k` of `K` to the homogeneous map
`l ↦ k ⊗ l` from `L` to the total tensor product. -/
@[stacks 0A8Q "canonical diagonal morphism"]
noncomputable def diagonalTensorHom
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) :
    K ⟶ (sheafHomComplex Rc L (tensorTotal Rc K L)).obj :=
  Classical.choose (diagonalTensorHom_exists Rc K L)

/-- On local sections, the diagonal morphism is inclusion of the pure tensor in the
appropriate summand of the total complex. -/
@[stacks 0A8Q "canonical characterization"]
theorem diagonalTensorHom_apply
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X)
    (n p : ℤ) (k : (K.X n).val.obj (op U))
    (l : (L.X p).val.obj (op U)) :
    applyHomSection Rc (sheafHomComplex Rc L (tensorTotal Rc K L))
        U n p (n + p) (by omega)
        (((diagonalTensorHom Rc K L).f n).val.app (op U) k) l =
      tensorTotalSection Rc K L U n p k l :=
  Classical.choose_spec (diagonalTensorHom_exists Rc K L) U n p k l (by omega)

/-- The cochain attached to a local section of the diagonal morphism is the diagonal
cochain. -/
private theorem diagonalTensorHom_cochain
    (K L : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X)
    (n : ℤ) (k : (K.X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom
      (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).hom.f n)
        (((diagonalTensorHom Rc K L).f n).val.app (op U) k) =
      sliceDiagonalCochain Rc U K L n k := by
  apply Cochain.ext
  intro p q hpq
  obtain rfl : q = n + p := by omega
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext l
  show ((AddCommGrpCat.Hom.hom
    (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso U).hom.f n)
    (((diagonalTensorHom Rc K L).f n).val.app (op U) k)).v p (n + p) hpq).val.app
      (op (Over.mk (homOfLE (leOfHom V.unop.hom)))) l =
    tensorTotalSection Rc K L V.unop.left n p
      (restrictSection Rc (K.X n) (leOfHom V.unop.hom) k) l
  refine ((sheafHomComplex Rc L (tensorTotal Rc K L)).restrict_natural
    (leOfHom V.unop.hom) n p (n + p) hpq
    (((diagonalTensorHom Rc K L).f n).val.app (op U) k) (le_refl V.unop.left) l).trans ?_
  refine (congrArg (fun z => ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Rc L (tensorTotal Rc K L)).sectionsIso V.unop.left).hom.f n) z).v
      p (n + p) hpq).val.app (op (Over.mk (homOfLE (le_refl V.unop.left)))) l)
    (restrictSection_map Rc ((diagonalTensorHom Rc K L).f n)
      (leOfHom V.unop.hom) k).symm).trans ?_
  exact diagonalTensorHom_apply Rc K L V.unop.left n p
    (restrictSection Rc (K.X n) (leOfHom V.unop.hom) k) l

/-- The diagonal morphism is natural in `K` and dinatural in `L`. -/
@[stacks 0A8Q "functoriality in both complexes"]
theorem diagonalTensorHom_natural
    {K K' L L' : CochainComplex (StructureSheafModules Rc) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    diagonalTensorHom Rc K L ≫
        sheafHomComplexMap Rc (𝟙 L) (tensorTotalMap Rc f g) =
      f ≫ diagonalTensorHom Rc K' L' ≫
        sheafHomComplexMap Rc g (𝟙 (tensorTotal Rc K' L')) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext k
  refine homSection_ext Rc (sheafHomComplex Rc L (tensorTotal Rc K' L'))
    U.unop n _ _ ?_
  intro p q hpq W hWU l
  show ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Rc L (tensorTotal Rc K' L')).sectionsIso U.unop).hom.f n)
      (((sheafHomComplexMap Rc (𝟙 L) (tensorTotalMap Rc f g)).f n).val.app U
        (((diagonalTensorHom Rc K L).f n).val.app U k))).v p q hpq).val.app
          (op (Over.mk (homOfLE hWU))) l =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Rc L (tensorTotal Rc K' L')).sectionsIso U.unop).hom.f n)
      (((sheafHomComplexMap Rc g (𝟙 (tensorTotal Rc K' L'))).f n).val.app U
        (((diagonalTensorHom Rc K' L').f n).val.app U ((f.f n).val.app U k)))).v
          p q hpq).val.app (op (Over.mk (homOfLE hWU))) l
  rw [sheafHomComplexMap_isInduced, sheafHomComplexMap_isInduced,
    diagonalTensorHom_cochain Rc K L U.unop n k,
    diagonalTensorHom_cochain Rc K' L' U.unop n ((f.f n).val.app U k)]
  show ((slicePureTensorMap Rc U.unop K L n p q (by omega) k ≫
    ((tensorTotalMap Rc f g).f q).over U.unop).val.app
      (op (Over.mk (homOfLE hWU)))) l =
    (((g.f p).over U.unop ≫ slicePureTensorMap Rc U.unop K' L' n p q (by omega)
      ((f.f n).val.app U k)).val.app (op (Over.mk (homOfLE hWU)))) l
  rw [slicePureTensorMap_natural]

end Stacks.SheafOfModules

end
