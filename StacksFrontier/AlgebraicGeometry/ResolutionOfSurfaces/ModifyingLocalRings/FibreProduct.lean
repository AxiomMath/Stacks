module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatDimensionFunctorRepresentability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineDescent
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverFunctorIso

/-!
# Iterated fibre products of schemes over a base

A finite family of morphisms `X i ⟶ S` has a fibre product `X 0 ×_S ⋯ ×_S X (n-1) ⟶ S`, formed
here by iterating the binary fibre product. This file constructs it, records that it is a
product in `Over S`, and derives the three facts about it that recognize a modification of `S`
supported at finitely many closed points:

* its structure morphism is of finite presentation as soon as every factor's is;
* it becomes an isomorphism over any base to which every factor restricts to an isomorphism;
* it becomes the `i`th factor over any base to which every *other* factor restricts to an
  isomorphism.

The last two rest on the fact that `CategoryTheory.Over.pullback` is a right adjoint, hence
carries a fibre product to a fibre product. An object of an over-category is terminal exactly
when its structure morphism is invertible, so a factor that restricts to an isomorphism
disappears from the product.

## Main definitions

* `CategoryTheory.Over.binProd`: the fibre product over `T` of two objects of `Over T`,
  together with `CategoryTheory.Over.binProdIsLimit` exhibiting it as a binary product.
* `AlgebraicGeometry.finFibreProduct`: the iterated fibre product of a finite family of schemes
  over a base.

## Main results

* `AlgebraicGeometry.finitePresentation_finFibreProduct_hom`: the iterated fibre product of
  morphisms of finite presentation is of finite presentation.
* `AlgebraicGeometry.isIso_pullback_finFibreProduct_hom`: the iterated fibre product restricts
  to an isomorphism over any base over which every factor does.
* `AlgebraicGeometry.nonempty_pullback_finFibreProduct_iso`: over a base over which every factor
  other than the `i`th restricts to an isomorphism, the iterated fibre product is the `i`th
  factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {T : C}

/-- Invertibility of the structure morphism of an object of `Over T` depends only on its
isomorphism class. -/
theorem isIso_hom_iff_isIso_hom_of_iso {X Y : Over T} (e : X ≅ Y) : IsIso X.hom ↔ IsIso Y.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget T).map e.hom))
  rw [← Over.w e.hom, isIso_comp_left_iff]

/-- An object of `Over T` whose structure morphism is invertible is terminal, so any two
morphisms into it agree. -/
theorem hom_ext_of_isIso_hom_target {X Y : Over T} [IsIso Y.hom] (f g : X ⟶ Y) : f = g :=
  Over.OverMorphism.ext ((cancel_mono Y.hom).mp ((Over.w f).trans (Over.w g).symm))

/-- Two objects of `Over T` with invertible structure morphisms are canonically isomorphic. -/
noncomputable def isoOfIsIsoHomOfIsIsoHom (X Y : Over T) [IsIso X.hom] [IsIso Y.hom] : X ≅ Y :=
  Over.isoMk (asIso X.hom ≪≫ (asIso Y.hom).symm)

/-- An object of `Over T` whose structure morphism is invertible is a terminal object. -/
noncomputable def isTerminalOfIsIsoHom {X : Over T} (h : IsIso X.hom) : IsTerminal X :=
  IsTerminal.ofUniqueHom (fun W ↦ Over.homMk (W.hom ≫ inv X.hom) (by simp))
    fun _ _ ↦ hom_ext_of_isIso_hom_target _ _

section BinProd

variable [HasPullbacks C]

/-- The fibre product over `T` of two objects of `Over T`. -/
noncomputable def binProd (A B : Over T) : Over T :=
  Over.mk (pullback.fst A.hom B.hom ≫ A.hom)

/-- The first projection of the fibre product over `T`. -/
noncomputable def binProdFst (A B : Over T) : binProd A B ⟶ A :=
  Over.homMk (pullback.fst A.hom B.hom)

/-- The second projection of the fibre product over `T`. -/
noncomputable def binProdSnd (A B : Over T) : binProd A B ⟶ B :=
  Over.homMk (pullback.snd A.hom B.hom) pullback.condition.symm

/-- The morphism into the fibre product over `T` determined by a pair of morphisms. -/
noncomputable def binProdLift {W A B : Over T} (f : W ⟶ A) (g : W ⟶ B) : W ⟶ binProd A B :=
  Over.homMk (pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm)) (by
    change pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm) ≫
      pullback.fst A.hom B.hom ≫ A.hom = W.hom
    rw [← Category.assoc, pullback.lift_fst]
    exact Over.w f)

/-- The morphism into the fibre product followed by the first projection is the first
component. -/
@[simp]
theorem binProdLift_fst {W A B : Over T} (f : W ⟶ A) (g : W ⟶ B) :
    binProdLift f g ≫ binProdFst A B = f :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The morphism into the fibre product followed by the second projection is the second
component. -/
@[simp]
theorem binProdLift_snd {W A B : Over T} (f : W ⟶ A) (g : W ⟶ B) :
    binProdLift f g ≫ binProdSnd A B = g :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- A morphism into the fibre product over `T` is determined by its two components. -/
theorem binProd_hom_ext {W A B : Over T} {f g : W ⟶ binProd A B}
    (h₁ : f ≫ binProdFst A B = g ≫ binProdFst A B)
    (h₂ : f ≫ binProdSnd A B = g ≫ binProdSnd A B) : f = g :=
  Over.OverMorphism.ext (pullback.hom_ext (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂))

/-- The fibre product over `T` is the binary product in `Over T`. -/
noncomputable def binProdIsLimit (A B : Over T) :
    IsLimit (BinaryFan.mk (binProdFst A B) (binProdSnd A B)) :=
  BinaryFan.isLimitMk (fun s ↦ binProdLift (BinaryFan.fst s) (BinaryFan.snd s))
    (fun _ ↦ binProdLift_fst _ _) (fun _ ↦ binProdLift_snd _ _)
    fun _ _ h₁ h₂ ↦ binProd_hom_ext (h₁.trans (binProdLift_fst _ _).symm)
      (h₂.trans (binProdLift_snd _ _).symm)

/-- Base change carries the fibre product over `T` to a fibre product. -/
noncomputable def binProdIsLimitPullback {T' : C} (h : T' ⟶ T) (A B : Over T)
    [PreservesLimit (pair A B) (Over.pullback h)] :
    IsLimit (BinaryFan.mk ((Over.pullback h).map (binProdFst A B))
      ((Over.pullback h).map (binProdSnd A B))) :=
  isLimitMapConeBinaryFanEquiv (Over.pullback h) (binProdFst A B) (binProdSnd A B)
    (isLimitOfPreserves (Over.pullback h) (binProdIsLimit A B))

end BinProd

end CategoryTheory.Over

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {A B P : C} {p : P ⟶ A} {q : P ⟶ B}

/-- A binary product of two terminal objects is terminal. -/
noncomputable def isTerminalOfBinaryFanIsLimit (hl : IsLimit (BinaryFan.mk p q))
    (hA : IsTerminal A) (hB : IsTerminal B) : IsTerminal P :=
  IsTerminal.ofUniqueHom (fun W ↦ hl.lift (BinaryFan.mk (hA.from W) (hB.from W)))
    fun _ _ ↦ BinaryFan.IsLimit.hom_ext hl (hA.hom_ext _ _) (hB.hom_ext _ _)

/-- A binary product whose second factor is terminal is its first factor. -/
theorem isIso_fst_of_binaryFan_isLimit (hl : IsLimit (BinaryFan.mk p q)) (hB : IsTerminal B) :
    IsIso p := by
  have hfst : hl.lift (BinaryFan.mk (𝟙 A) (hB.from A)) ≫ p = 𝟙 A := by
    simpa using hl.fac (BinaryFan.mk (𝟙 A) (hB.from A)) ⟨WalkingPair.left⟩
  refine ⟨hl.lift (BinaryFan.mk (𝟙 A) (hB.from A)), ?_, hfst⟩
  refine BinaryFan.IsLimit.hom_ext hl ?_ (hB.hom_ext _ _)
  simp only [BinaryFan.mk_fst, Category.assoc, hfst, Category.comp_id, Category.id_comp]

/-- A binary product whose first factor is terminal is its second factor. -/
theorem isIso_snd_of_binaryFan_isLimit (hl : IsLimit (BinaryFan.mk p q)) (hA : IsTerminal A) :
    IsIso q :=
  isIso_fst_of_binaryFan_isLimit (BinaryFan.isLimitFlip hl) hA

end CategoryTheory.Limits

namespace AlgebraicGeometry

open CategoryTheory.Over

variable {S : Scheme.{u}}

/-- The iterated fibre product over `S` of a finite family of schemes over `S`. -/
noncomputable def finFibreProduct : {m : ℕ} → (Fin m → Over S) → Over S
  | 0, _ => Over.mk (𝟙 S)
  | _ + 1, Z => binProd (Z 0) (finFibreProduct fun j ↦ Z j.succ)

/-- The iterated fibre product of morphisms of finite presentation is of finite
presentation. -/
theorem finitePresentation_finFibreProduct_hom :
    ∀ {m : ℕ} (Z : Fin m → Over S), (∀ j, FinitePresentation (Z j).hom) →
      FinitePresentation (finFibreProduct Z).hom
  | 0, _, _ => show FinitePresentation (𝟙 S) from
    ⟨inferInstance, inferInstance, inferInstance⟩
  | _ + 1, _, h => ExtendingFunctors.finitePresentation_comp
    (finitePresentation_pullback_fst _ _
      (finitePresentation_finFibreProduct_hom _ fun j ↦ h j.succ)) (h 0)

/-- The iterated fibre product restricts to an isomorphism over any base over which every
factor restricts to an isomorphism. -/
theorem isIso_pullback_finFibreProduct_hom {T : Scheme.{u}} (g : T ⟶ S) :
    ∀ {m : ℕ} (Z : Fin m → Over S), (∀ j, IsIso ((Over.pullback g).obj (Z j)).hom) →
      IsIso ((Over.pullback g).obj (finFibreProduct Z)).hom
  | 0, _, _ => by
    change IsIso (pullback.snd (𝟙 S) g)
    infer_instance
  | _ + 1, Z, h =>
    isIso_hom_of_isTerminal (isTerminalOfBinaryFanIsLimit
      (binProdIsLimitPullback g (Z 0) (finFibreProduct fun j ↦ Z j.succ))
      (isTerminalOfIsIsoHom (h 0))
      (isTerminalOfIsIsoHom (isIso_pullback_finFibreProduct_hom g _ fun j ↦ h j.succ)))

/-- Over a base over which every factor other than the `i`th restricts to an isomorphism, the
iterated fibre product is the `i`th factor. -/
theorem nonempty_pullback_finFibreProduct_iso {T : Scheme.{u}} (g : T ⟶ S) :
    ∀ {m : ℕ} (Z : Fin m → Over S) (i : Fin m),
      (∀ j, j ≠ i → IsIso ((Over.pullback g).obj (Z j)).hom) →
        Nonempty ((Over.pullback g).obj (finFibreProduct Z) ≅ (Over.pullback g).obj (Z i))
  | 0, _, i, _ => absurd i.isLt (Nat.not_lt_zero _)
  | m + 1, Z, i, h => by
    have hlim := binProdIsLimitPullback g (Z 0) (finFibreProduct fun j ↦ Z j.succ)
    induction i using Fin.cases with
    | zero =>
      have hterm := isTerminalOfIsIsoHom (isIso_pullback_finFibreProduct_hom g
        (fun j ↦ Z j.succ) fun j ↦ h j.succ (Fin.succ_ne_zero j))
      have hiso : IsIso ((Over.pullback g).map (binProdFst (Z 0)
          (finFibreProduct fun j ↦ Z j.succ))) :=
        isIso_fst_of_binaryFan_isLimit hlim hterm
      exact ⟨@asIso _ _ _ _ _ hiso⟩
    | succ k =>
      have hterm := isTerminalOfIsIsoHom (h 0 fun hcon ↦ Fin.succ_ne_zero k hcon.symm)
      have hiso : IsIso ((Over.pullback g).map (binProdSnd (Z 0)
          (finFibreProduct fun j ↦ Z j.succ))) :=
        isIso_snd_of_binaryFan_isLimit hlim hterm
      obtain ⟨e⟩ := nonempty_pullback_finFibreProduct_iso g (fun j ↦ Z j.succ) k
        fun j hj ↦ h j.succ fun hcon ↦ hj (Fin.succ_injective _ hcon)
      exact ⟨(@asIso _ _ _ _ _ hiso) ≪≫ e⟩

end AlgebraicGeometry

end
