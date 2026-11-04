module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.Duality.InvertibleTwistExt
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DerivedPushforwardTwist
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialNumerical

/-!
# The twisted inverse image of the structure sheaf on projective space

Let `S` be an affine scheme, `n ≥ 0`, `f : X = ℙⁿ_S ⟶ S` the structure morphism and `a` the right
adjoint of `R f_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` of [Stacks, Tag 0A9E]. This file proves
`a(𝒪_S) ≅ 𝒪(-n-1)[n]`, the case of projective space of [Stacks, Tag 0A9W], by the source's
proof.

The trace `R f_*(𝒪(-n-1)[n]) ≅ 𝒪_S` (`dualizingTwistTrace`, from the display of
[Stacks, Tag 01XW]) determines `c : 𝒪(-n-1)[n] ⟶ a(𝒪_S)` by adjunction. The functors
`F_{i,p} = Hom(𝒪(i), (-)[p])`, `-n ≤ i ≤ 0`, carry `c` to bijections: for `i = 0` because
`R f_*` is bijective on morphisms out of `𝒪_X[0]⟦q⟧` (the unit `𝒪_S ⟶ R f_* 𝒪_X` of
`L f^* ⊣ R f_*` is invertible), for `-n ≤ i ≤ -1` because both sides vanish
(`R f_* 𝒪(i) = 0`, and `Hom(𝒪(i), 𝒪(-n-1)[p]) = H^p(X, 𝒪(-n-1-i)) = 0`, read through the twist
autoequivalence `- ⊗ 𝒪(-i)` and `L f^* ⊣ R f_*`). The cone of `c` is bounded below by
[Stacks, Tag 0A9I], so the generation of `D^+_QCoh(𝒪_X)` by the twists
(`StacksFrontier/AlgebraicGeometry/Duality/ProjectiveSpace/TwistGeneration.lean`) kills it.

## Main results

* `Stacks.Duality.ProjectiveSpace.dualizingTwistComparison` — the comparison map `c`.
* `Stacks.Duality.ProjectiveSpace.isIso_dualizingTwistComparison` — `c` is an isomorphism.
* `Stacks.Duality.ProjectiveSpace.nonempty_twistedInverseImage_derivedStructureSheaf_iso` —
  `a(𝒪_S) ≅ 𝒪(-n-1)[n]`.

## Implementation notes

The invertibility of the unit `𝒪_S[0] ⟶ R f_*(𝒪_X[0])` is not computed: `R f_*(𝒪_X[0])` is
abstractly `𝒪_S[0]` (`nonempty_derivedPushforward_twistOver_zero_iso`), every endomorphism of
`𝒪_S[0]` is `R f_*` of one of `𝒪_X[0]` composed with the unit, and endomorphisms of the
structure sheaf commute; a morphism with these properties acquires a two-sided inverse
(`isIso_of_surjective_comp_map`).

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.Duality.ProjectiveSpace

/-! ### Three formal lemmas -/

section Formal

variable {C D : Type*} [Category C] [Category D]

/-- Precomposition with an isomorphism is a bijection on morphisms. -/
theorem bijective_comp_left_of_isIso {X Y : C} (Z : C) (f : X ⟶ Y) [IsIso f] :
    Function.Bijective fun g : Y ⟶ Z => f ≫ g :=
  ⟨fun _ _ h => (cancel_epi f).1 h, fun y => ⟨inv f ≫ y, by simp⟩⟩

/-- Postcomposition with an isomorphism is a bijection on morphisms. -/
theorem bijective_comp_right_of_isIso {Y Z : C} (X : C) (f : Y ⟶ Z) [IsIso f] :
    Function.Bijective fun g : X ⟶ Y => g ≫ f :=
  ⟨fun _ _ h => (cancel_mono f).1 h, fun y => ⟨y ≫ inv f, by simp⟩⟩

/-- Let `u : P ⟶ R(Q)` be such that every endomorphism of `R(Q)` factors as `u ≫ R(φ)` up to an
abstract isomorphism `R(Q) ≅ P`. If the endomorphisms of `P` commute with each other, `u` is an
isomorphism: it acquires a right inverse, which is then a two-sided one. -/
theorem isIso_of_surjective_comp_map (R : C ⥤ D) {P : D} {Q : C} (u : P ⟶ R.obj Q)
    (hu : Function.Surjective fun φ : Q ⟶ Q => u ≫ R.map φ) (w : R.obj Q ≅ P)
    (hcomm : ∀ a b : P ⟶ P, a ≫ b = b ≫ a) : IsIso u := by
  obtain ⟨φ, hφ⟩ := hu w.inv
  have hab : (u ≫ w.hom) ≫ (w.inv ≫ R.map φ ≫ w.hom) = 𝟙 P := by
    simp [reassoc_of% hφ]
  have : IsIso (u ≫ w.hom) := ⟨_, hab, (hcomm _ _).trans hab⟩
  exact IsIso.of_isIso_comp_right u w.hom

/-- Through an adjunction `L ⊣ R` and an isomorphism `L(P) ≅ Q`, the map
`φ ↦ u ≫ R(φ) : (Q ⟶ Z) → (P ⟶ R(Z))` is bijective, `u` being the unit followed by `R` of the
isomorphism. -/
theorem bijective_unit_comp_map {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R) {P : D} {Q : C}
    (e : L.obj P ≅ Q) (Z : C) :
    Function.Bijective fun φ : Q ⟶ Z => (adj.unit.app P ≫ R.map e.hom) ≫ R.map φ := by
  have : (fun φ : Q ⟶ Z => (adj.unit.app P ≫ R.map e.hom) ≫ R.map φ) =
      (adj.homEquiv P Z) ∘ (fun φ : Q ⟶ Z => e.hom ≫ φ) := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [this]
  exact (adj.homEquiv P Z).bijective.comp (bijective_comp_left_of_isIso _ e.hom)

/-- If `φ ↦ u ≫ R(φ)` is bijective and `u` is invertible, then `R` is bijective on morphisms
out of `Q`. -/
theorem bijective_map_of_isIso (R : C ⥤ D) {P : D} {Q Z : C} (u : P ⟶ R.obj Q) [IsIso u]
    (hu : Function.Bijective fun φ : Q ⟶ Z => u ≫ R.map φ) :
    Function.Bijective fun φ : Q ⟶ Z => R.map φ := by
  have : (fun φ : Q ⟶ Z => R.map φ) = (fun ψ => inv u ≫ ψ) ∘ (fun φ => u ≫ R.map φ) := by
    funext φ
    simp
  rw [this]
  exact (bijective_comp_left_of_isIso _ (inv u)).comp hu

/-- Bijectivity of `F` on morphisms out of an object transfers along an isomorphism. -/
theorem bijective_map_of_domain_iso (F : C ⥤ D) {A B : C} (e : A ≅ B) (Z : C)
    (h : Function.Bijective fun φ : B ⟶ Z => F.map φ) :
    Function.Bijective fun φ : A ⟶ Z => F.map φ := by
  have : (fun φ : A ⟶ Z => F.map φ) =
      (fun ψ => F.map e.hom ≫ ψ) ∘ (fun φ => F.map φ) ∘ (fun φ => e.inv ≫ φ) := by
    funext φ
    simp
  rw [this]
  exact (bijective_comp_left_of_isIso _ (F.map e.hom)).comp
    (h.comp (bijective_comp_left_of_isIso _ e.inv))

end Formal

section Triangles

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a distinguished triangle `N ⟶ M ⟶ Z ⟶ N⟦1⟧`, an object `W` for which composition with
`N ⟶ M` is surjective on `W ⟶ N` and composition with `N⟦1⟧ ⟶ M⟦1⟧` is injective on
`W ⟶ N⟦1⟧` admits no nonzero morphism to `Z`. -/
theorem eq_zero_of_mem_distTriang (T : Triangle C) (hT : T ∈ distTriang C) {W : C}
    (hsurj : Function.Surjective fun φ : W ⟶ T.obj₁ => φ ≫ T.mor₁)
    (hinj : Function.Injective
      fun ψ : W ⟶ (shiftFunctor C (1 : ℤ)).obj T.obj₁ => ψ ≫ (shiftFunctor C (1 : ℤ)).map T.mor₁)
    (x : W ⟶ T.obj₃) : x = 0 := by
  have h₂ : x ≫ T.mor₃ = 0 := hinj (by
    dsimp only
    rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero, zero_comp])
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ T hT x h₂
  obtain ⟨φ, rfl⟩ := hsurj y
  rw [hy, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Injectivity of composition with `c : N ⟶ M` on morphisms out of `W'` gives injectivity of
composition with `c⟦1⟧` on morphisms out of any `W ≅ W'⟦1⟧`. -/
theorem injective_comp_shift_map {W W' N M : C} (c : N ⟶ M)
    (ε : W ≅ (shiftFunctor C (1 : ℤ)).obj W')
    (h : Function.Injective fun φ : W' ⟶ N => φ ≫ c) :
    Function.Injective
      fun ψ : W ⟶ (shiftFunctor C (1 : ℤ)).obj N => ψ ≫ (shiftFunctor C (1 : ℤ)).map c := by
  intro ψ₁ ψ₂ hψ
  dsimp only at hψ
  let F := shiftFunctor C (1 : ℤ)
  have key : F.preimage (ε.inv ≫ ψ₁) ≫ c = F.preimage (ε.inv ≫ ψ₂) ≫ c := by
    refine F.map_injective ?_
    simp only [F, Functor.map_comp, Functor.map_preimage, Category.assoc, hψ]
  have := congrArg F.map (h key)
  simp only [F, Functor.map_preimage] at this
  simpa using congrArg (ε.hom ≫ ·) this

end Triangles

/-! ### The endomorphisms of the structure sheaf commute -/

/-- The endomorphisms of the structure sheaf of a scheme, as a module over itself, commute: on
each open they are multiplications by sections of a commutative ring. -/
theorem unit_hom_comm {X : Scheme.{u}}
    (g h : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    g ≫ h = h ≫ g := by
  ext U
  have hF : ∀ (F : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(X, U.unop)) (x : Γ(X, U.unop)),
      F x = x * F 1 := fun F x => by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  let Fg : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(X, U.unop) := (g.val.app U).hom
  let Fh : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(X, U.unop) := (h.val.app U).hom
  change Fh (Fg 1) = Fg (Fh 1)
  rw [hF Fh (Fg 1), hF Fg (Fh 1), mul_comm]

/-- The endomorphisms of a shift of the structure sheaf placed in degree zero commute, in any
model of the derived category: the single functor and the shift are fully faithful. -/
theorem shift_single_unit_hom_comm {X : Scheme.{u}} [HasDerivedCategory.{u} X.Modules] (q : ℤ)
    (a b : (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) ⟶ (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) :
    a ≫ b = b ≫ a := by
  set F := DerivedCategory.singleFunctor X.Modules 0 ⋙ shiftFunctor (DerivedCategory X.Modules) q
  have hF : F.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor X.Modules 0)).comp
      (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor (DerivedCategory X.Modules) q))
  obtain ⟨a', rfl⟩ := hF.map_surjective a
  obtain ⟨b', rfl⟩ := hF.map_surjective b
  exact (F.map_comp a' b').symm.trans
    ((congrArg F.map (unit_hom_comm a' b')).trans (F.map_comp b' a'))

/-! ### Derived pullback of the structure sheaf, and the unit of `L f^* ⊣ R f_*` -/

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `L f^*` commutes with the shift at the locally small model, as the left adjoint of `R f_*`,
which does. -/
@[instance_reducible]
noncomputable def derivedPullbackCommShift : (Stacks.Duality.derivedPullback f).CommShift ℤ :=
  (Stacks.Duality.derivedAdjunction f).leftAdjointCommShift ℤ

/-- `L f^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, at the locally small model and in the scheme spelling: the
structure sheaf is flat, and its ordinary pullback is the structure sheaf. -/
def derivedPullbackUnitIso :
    (Stacks.Duality.derivedPullback f).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPullbackSingleIsoOfFlat f _
      (Stacks.Chow.isFlat_of_isInvertible (h := Stacks.Ample.isInvertibleModule_unit Y) _) ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso f)

/-- `L f^*(𝒪_Y[0]⟦q⟧) ≅ 𝒪_X[0]⟦q⟧`. -/
def derivedPullbackShiftUnitIso (q : ℤ) :
    (Stacks.Duality.derivedPullback f).obj ((shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  letI := derivedPullbackCommShift f
  ((Stacks.Duality.derivedPullback f).commShiftIso q).app _ ≪≫
    (shiftFunctor _ q).mapIso (derivedPullbackUnitIso f)

/-- The map `𝒪_Y[0]⟦q⟧ ⟶ R f_*(𝒪_X[0]⟦q⟧)`: the unit of `L f^* ⊣ R f_*` followed by
`derivedPullbackShiftUnitIso`. -/
def shiftUnitToDerivedPushforward (q : ℤ) :
    (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) ⟶
      (Stacks.Duality.derivedPushforward f).obj ((shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) :=
  (Stacks.Duality.derivedAdjunction f).unit.app _ ≫
    (Stacks.Duality.derivedPushforward f).map (derivedPullbackShiftUnitIso f q).hom

/-- Morphisms out of `𝒪_X[0]⟦q⟧` are morphisms out of `𝒪_Y[0]⟦q⟧` into the derived direct
image: `H^{-q}(X, -) = H^{-q}(Y, R f_* -)`. -/
theorem bijective_shiftUnitToDerivedPushforward_comp_map (q : ℤ)
    (Z : DerivedCategory X.Modules) :
    Function.Bijective fun φ : (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) ⟶ Z =>
      shiftUnitToDerivedPushforward f q ≫ (Stacks.Duality.derivedPushforward f).map φ :=
  bijective_unit_comp_map (Stacks.Duality.derivedAdjunction f) (derivedPullbackShiftUnitIso f q) Z

end Pullback

section Twist

/-- **Twisting by an invertible module preserves the vanishing of morphisms between shifted
modules.** If `M ⊗ ℒ ≅ M'` and `N ⊗ ℒ ≅ N'` for an invertible `ℒ`, a vanishing statement about
`M'[0]⟦q⟧ ⟶ N'[0]⟦k⟧` gives the one about `M[0]⟦q⟧ ⟶ N[0]⟦k⟧`: tensoring by `ℒ` is an exact
autoequivalence of `X.Modules`, hence induces one of `D(𝒪_X)` compatible with the single functor
and the shift. -/
theorem subsingleton_shift_single_hom_of_tensor {X : Scheme.{u}} [HasDerivedCategory.{u} X.Modules]
    (L : X.Modules) [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.property L] {M N M' N' : X.Modules}
    (eM : (Stacks.SheafOfModules.Invertible.tensorModuleFunctor L).obj M ≅ M')
    (eN : (Stacks.SheafOfModules.Invertible.tensorModuleFunctor L).obj N ≅ N') (q k : ℤ)
    (h : Subsingleton ((shiftFunctor _ q).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M') ⟶
      (shiftFunctor _ k).obj ((DerivedCategory.singleFunctor X.Modules 0).obj N'))) :
    Subsingleton ((shiftFunctor _ q).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M) ⟶
      (shiftFunctor _ k).obj ((DerivedCategory.singleFunctor X.Modules 0).obj N)) := by
  let G := Stacks.SheafOfModules.Invertible.tensorModuleFunctor L
  let T := G.mapDerivedCategory
  have : G.asEquivalence.functor.Additive := inferInstanceAs G.Additive
  have : T.IsEquivalence :=
    inferInstanceAs (G.asEquivalence.functor.mapDerivedCategory.IsEquivalence)
  have tw : ∀ (P P' : X.Modules) (_ : G.obj P ≅ P') (j : ℤ),
      T.obj ((shiftFunctor _ j).obj ((DerivedCategory.singleFunctor X.Modules 0).obj P)) ≅
        (shiftFunctor _ j).obj ((DerivedCategory.singleFunctor X.Modules 0).obj P') :=
    fun P P' e j => (T.commShiftIso j).app _ ≪≫
      (shiftFunctor _ j).mapIso ((G.mapDerivedCategorySingleFunctor 0).app P ≪≫
        (DerivedCategory.singleFunctor X.Modules 0).mapIso e)
  exact ⟨fun a b => T.map_injective
    (((Iso.homCongr (tw M M' eM q) (tw N N' eN k)).subsingleton_congr.2 h).elim _ _)⟩

end Twist

/-! ### The direct images of `𝒪`, `𝒪(-1)`, …, `𝒪(-n-1)` on `ℙⁿ_S`, for every `n ≥ 0` -/

section DirectImages

variable (n : ℕ) (S : Scheme.{u})

/-- `ℙ⁰_S ⟶ S` is an isomorphism: it is the base change of `ℙ⁰_ℤ ⟶ Spec ℤ`, which is one. -/
instance isIso_projectiveSpaceOver_zero : IsIso (projectiveSpaceOver 0 S ↘ S) := by
  have := Stacks.DeRham.isIso_terminalFrom_projectiveSpaceAtUniverse_of_zero.{u}
  change IsIso (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 0)))
  infer_instance

/-- `R f_*(𝒪_X[0]) ≅ 𝒪_S[0]` for the isomorphism `f : ℙ⁰_S ⟶ S`. -/
theorem nonempty_derivedPushforward_unit_iso_zero :
    Nonempty ((Stacks.Duality.derivedPushforward (projectiveSpaceOver 0 S ↘ S)).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver 0 S).Modules 0).obj
          (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf)) := by
  set K := (Stacks.Duality.derivedPushforward (projectiveSpaceOver 0 S ↘ S)).obj
    ((DerivedCategory.singleFunctor (projectiveSpaceOver 0 S).Modules 0).obj
      (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf))
  have ht := nonempty_homology_derivedPushforward_iso_rightDerived.{u}
    (projectiveSpaceOver 0 S ↘ S) (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf)
  have hK : ∀ j : ℤ, j ≠ 0 → IsZero ((DerivedCategory.homologyFunctor S.Modules j).obj K) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact isZero_homology_derivedPushforward_of_neg _ _ j hj
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj.le
      obtain ⟨t⟩ := ht k
      open Stacks.Cohomology.Affine.HigherDirectImage in
      exact IsZero.of_iso
        (isZero_rightDerivedNat_pushforward_of_isAffineHom _ _ k (by exact_mod_cast hj)) t
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K 0 hK
  obtain ⟨t⟩ := ht 0
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor S.Modules 0).mapIso (t ≪≫
    (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso _).app _ ≪≫
      Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.pushforwardUnitIso 0 S)⟩

/-- **`R f_*(𝒪_X[0]) ≅ 𝒪_S[0]`** for `f : ℙⁿ_S ⟶ S` and every `n ≥ 0`. For `n ≥ 1` this is
`nonempty_derivedPushforward_twistOver_zero_iso`; for `n = 0` the morphism `f` is an isomorphism,
hence affine, so the higher direct images vanish ([Stacks, Tag 01XC]) and `f_* 𝒪_X = 𝒪_S`. -/
theorem nonempty_derivedPushforward_unit_iso :
    Nonempty ((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf)) := by
  rcases n with _ | m
  · exact nonempty_derivedPushforward_unit_iso_zero S
  · obtain ⟨w⟩ := nonempty_derivedPushforward_twistOver_zero_iso.{u} m S
    exact ⟨(Stacks.Duality.derivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit (m + 1) S).symm) ≪≫ w⟩

/-- **`R f_*(𝒪(-n-1)[0]) ≅ 𝒪_S[-n]`** for `f : ℙⁿ_S ⟶ S` and every `n ≥ 0`: for `n ≥ 1` this is
`nonempty_derivedPushforward_dualizingTwist_iso`, and on `ℙ⁰_S` every twist is trivial. -/
theorem nonempty_derivedPushforward_twistOver_neg_succ_iso :
    Nonempty ((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S (-(n : ℤ) - 1))) ≅
      (DerivedCategory.singleFunctor S.Modules (n : ℤ)).obj
        (SheafOfModules.unit S.ringCatSheaf)) := by
  rcases n with _ | m
  · obtain ⟨w⟩ := nonempty_derivedPushforward_unit_iso 0 S
    exact ⟨(Stacks.Duality.derivedPushforward (projectiveSpaceOver 0 S ↘ S)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (AlgebraicGeometry.projectiveTwistingSheafZeroIsoUnit S _)) ≪≫ w⟩
  · exact nonempty_derivedPushforward_dualizingTwist_iso.{u} m S

/-- `R f_*(𝒪(d)[0]) = 0` for `-n ≤ d ≤ -1`, `f : ℙⁿ_S ⟶ S`. -/
theorem isZero_derivedPushforward_twistOver' {d : ℤ} (hd₁ : -(n : ℤ) ≤ d) (hd₂ : d < 0) :
    IsZero ((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S d))) := by
  rcases n with _ | m
  · omega
  · exact isZero_derivedPushforward_twistOver.{u} m S hd₁ hd₂

end DirectImages

/-! ### Morphisms out of the structure sheaf of projective space -/

section ProjectiveSpace

variable (n : ℕ) (S : Scheme.{u})

/-- On `ℙⁿ_S`, `n ≥ 0`, the map `𝒪_S[0]⟦q⟧ ⟶ R f_*(𝒪_X[0]⟦q⟧)` is an isomorphism: the
target is abstractly `𝒪_S[0]⟦q⟧` (`nonempty_derivedPushforward_unit_iso`) and the
endomorphisms of `𝒪_S[0]⟦q⟧` commute. -/
theorem isIso_shiftUnitToDerivedPushforward (q : ℤ) :
    IsIso (shiftUnitToDerivedPushforward (projectiveSpaceOver n S ↘ S) q) := by
  obtain ⟨w₀⟩ := nonempty_derivedPushforward_unit_iso n S
  exact isIso_of_surjective_comp_map _ _
    (bijective_shiftUnitToDerivedPushforward_comp_map (projectiveSpaceOver n S ↘ S) q _).2
    (((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).commShiftIso q).app _ ≪≫
      (shiftFunctor _ q).mapIso w₀)
    (shift_single_unit_hom_comm q)

/-- **`R f_*` is bijective on morphisms out of `𝒪_X[0]⟦q⟧`**, for `f : ℙⁿ_S ⟶ S`. -/
theorem bijective_derivedPushforward_map_shift_unit (q : ℤ)
    (Z : DerivedCategory (projectiveSpaceOver n S).Modules) :
    Function.Bijective fun φ : (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)) ⟶ Z =>
      (Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).map φ := by
  have := isIso_shiftUnitToDerivedPushforward n S q
  exact bijective_map_of_isIso _ _
    (bijective_shiftUnitToDerivedPushforward_comp_map (projectiveSpaceOver n S ↘ S) q Z)

/-- `R f_*(𝒪(d)[0]⟦k⟧) = 0` for `-n ≤ d ≤ -1`, `f : ℙⁿ_S ⟶ S`. -/
theorem isZero_derivedPushforward_shift_twistOver (k : ℤ) {d : ℤ} (hd₁ : -(n : ℤ) ≤ d)
    (hd₂ : d < 0) :
    IsZero ((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).obj
      ((shiftFunctor _ k).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S d)))) :=
  IsZero.of_iso (Functor.map_isZero _ (isZero_derivedPushforward_twistOver' n S hd₁ hd₂))
    (((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).commShiftIso k).app _)

/-- For `-n ≤ d ≤ -1` there are no nonzero morphisms `𝒪_X[0]⟦q⟧ ⟶ 𝒪(d)[0]⟦k⟧` on `ℙⁿ_S`:
they are morphisms into `R f_*(𝒪(d)[0])⟦k⟧ = 0`. -/
theorem subsingleton_shift_unit_hom_shift_twistOver (q k : ℤ) {d : ℤ}
    (hd₁ : -(n : ℤ) ≤ d) (hd₂ : d < 0) :
    Subsingleton ((shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)) ⟶
      (shiftFunctor _ k).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S d))) :=
  ⟨fun _ _ => (bijective_shiftUnitToDerivedPushforward_comp_map (projectiveSpaceOver n S ↘ S) q
    _).1 ((isZero_derivedPushforward_shift_twistOver n S k hd₁ hd₂).eq_of_tgt _ _)⟩

/-- The twisting sheaf `𝒪(d)` on `ℙⁿ_S` is an invertible `𝒪`-module. -/
instance isInvertible_twistOver (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveSpaceOver n S).presheaf
      (projectiveSpaceOver n S).ringCatSheaf.property (twistOver n S d) :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n S d

/-- The multiplication isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`, read through the functor
`- ⊗ 𝒪(b)`. -/
def tensorTwistOverIso (a b : ℤ) :
    (Stacks.SheafOfModules.Invertible.tensorModuleFunctor (twistOver n S b)).obj
      (twistOver n S a) ≅ twistOver n S (a + b) :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso n S a b

/-- `𝒪(-b) ⊗ 𝒪(b) ≅ 𝒪`, read through the functor `- ⊗ 𝒪(b)`. -/
def tensorTwistOverNegIso (b : ℤ) :
    (Stacks.SheafOfModules.Invertible.tensorModuleFunctor (twistOver n S b)).obj
      (twistOver n S (-b)) ≅
        SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf :=
  tensorTwistOverIso n S (-b) b ≪≫ eqToIso (congrArg (twistOver n S) (neg_add_cancel b)) ≪≫
    Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit n S

/-- For `1 ≤ i ≤ n` there are no nonzero morphisms `𝒪(-i)[0]⟦q⟧ ⟶ 𝒪(-n-1)[0]⟦n⟧` on `ℙⁿ_S`.
Tensoring by the invertible module `𝒪(i)` carries them to morphisms
`𝒪_X[0]⟦q⟧ ⟶ 𝒪(i-n-1)[0]⟦n⟧`, and `-n ≤ i-n-1 ≤ -1`. -/
theorem subsingleton_shift_twistOver_hom_shift_dualizingTwist (q : ℤ) (i : ℕ) (hi₁ : 1 ≤ i)
    (hi₂ : i ≤ n) :
    Subsingleton ((shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S (-(i : ℤ)))) ⟶
      (shiftFunctor _ (n : ℤ)).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S (-(n : ℤ) - 1)))) :=
  subsingleton_shift_single_hom_of_tensor (twistOver n S (i : ℤ))
    (tensorTwistOverNegIso n S (i : ℤ)) (tensorTwistOverIso n S _ (i : ℤ)) q _
    (subsingleton_shift_unit_hom_shift_twistOver n S q (n : ℤ) (by omega) (by omega))

end ProjectiveSpace

/-! ### The comparison map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_S)` -/

section Comparison

variable (n : ℕ) (S : Scheme.{u})

/-- A shift of a quasi-coherent module placed in degree zero lies in `D_QCoh`. -/
theorem derivedCategoryB_shift_single {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (k : ℤ) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((shiftFunctor _ k).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M)) := by
  have := DerivedCategoryB.derivedCategoryB_isStableUnderShift
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  exact ObjectProperty.le_shift _ k _
    (Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj M inferInstance)

/-- **The relative dualizing complex of `ℙⁿ_S`**: `𝒪(-n-1)[n]`, as an object of
`D_QCoh(𝒪_{ℙⁿ_S})`. -/
def dualizingTwist : Stacks.Duality.quasiCoherentDerivedCategory (projectiveSpaceOver n S) :=
  ⟨(shiftFunctor _ (n : ℤ)).obj
    ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
      (twistOver n S (-(n : ℤ) - 1))), derivedCategoryB_shift_single _ _⟩

/-- **The trace `R f_*(𝒪(-n-1)[n]) ≅ 𝒪_S`** of the proof of [Stacks, Tag 0A9W]: the higher
direct images of `𝒪(-n-1)` vanish outside degree `n`, and the degree-`n` one is `𝒪_S`. -/
noncomputable def dualizingTwistTrace :
    (Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).obj (dualizingTwist n S).obj ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf) :=
  ((Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).commShiftIso
      (n : ℤ)).app _ ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso
      (nonempty_derivedPushforward_twistOver_neg_succ_iso n S).some ≪≫
    ((DerivedCategory.singleFunctors S.Modules).shiftIso (n : ℤ) 0 (n : ℤ)
      (by simp)).app _

/-- The source's computation of `Hom(𝒪(-i)[0]⟦q⟧, -)` applied to the trace: for `0 ≤ i ≤ n`,
`φ ↦ tr ∘ R f_*(φ)` is a bijection from morphisms `𝒪(-i)[0]⟦q⟧ ⟶ 𝒪(-n-1)[n]` to morphisms
`R f_*(𝒪(-i)[0]⟦q⟧) ⟶ 𝒪_S`. For `i = 0` this is the bijectivity of `R f_*` out of
`𝒪_X[0]⟦q⟧`; for `1 ≤ i ≤ n` both sides vanish. -/
theorem bijective_derivedPushforward_map_comp_dualizingTwistTrace (i : ℕ) (hi : i ≤ n)
    (q : ℤ) :
    Function.Bijective fun φ : (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S (-(i : ℤ)))) ⟶ (dualizingTwist n S).obj =>
      (Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).map φ ≫
        (dualizingTwistTrace n S).hom := by
  suffices h₁ : Function.Bijective fun φ : (shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S (-(i : ℤ)))) ⟶ (dualizingTwist n S).obj =>
      (Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).map φ from
    (bijective_comp_right_of_isIso _ (dualizingTwistTrace n S).hom).comp h₁
  rcases Nat.eq_zero_or_pos i with rfl | hi₁
  · let e : (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S (-((0 : ℕ) : ℤ)))) ≅ (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)) :=
      (shiftFunctor _ q).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        (eqToIso (congrArg (twistOver n S) (by simp)) ≪≫
          Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit n S))
    exact bijective_map_of_domain_iso _ e _ (bijective_derivedPushforward_map_shift_unit n S q _)
  · exact ⟨fun a b _ =>
      (subsingleton_shift_twistOver_hom_shift_dualizingTwist n S q i hi₁ hi).elim a b,
      fun _ => ⟨0, (isZero_derivedPushforward_shift_twistOver n S q
        (by omega) (by omega)).eq_of_src _ _⟩⟩

end Comparison

/-! ### Tag 0A9W -/

section Main

variable (n : ℕ) (S : Scheme.{u})

/-- The twisting sheaf `𝒪(d)` on `ℙⁿ_S` is a quasi-coherent module. -/
instance isQuasicoherent_twistOver (d : ℤ) : (twistOver n S d).IsQuasicoherent :=
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- A module placed in degree zero lives in degrees `≥ 0`. -/
theorem isGE_singleFunctor_zero {X : Scheme.{u}} (M : X.Modules) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj M).IsGE 0 :=
  inferInstance

/-- `𝒪(-n-1)[n]⟦1⟧` lives in degrees `≥ -n-1`. -/
theorem isGE_shift_one_dualizingTwist :
    ((shiftFunctor _ (1 : ℤ)).obj (dualizingTwist n S).obj).IsGE (-(n : ℤ) - 1) :=
  have h₀ := isGE_singleFunctor_zero (twistOver n S (-(n : ℤ) - 1))
  have h₁ : ((dualizingTwist n S).obj).IsGE (-(n : ℤ)) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 (n : ℤ) (-(n : ℤ)) (by omega)
  DerivedCategory.TStructure.t.isGE_shift _ (-(n : ℤ)) 1 _ (by omega)

variable [IsAffine S]

/-- The trace, as an isomorphism in `D_QCoh(𝒪_S)`. -/
noncomputable def dualizingTwistTraceIso :
    (Stacks.Duality.quasiCoherentDerivedPushforward (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj
        (dualizingTwist n S) ≅ Stacks.Duality.DerivedPushforward.derivedStructureSheaf S :=
  ObjectProperty.isoMk _ (dualizingTwistTrace n S)

/-- The comparison map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_S)` of the proof of [Stacks, Tag 0A9W]: the
morphism adjoint to the trace `R f_*(𝒪(-n-1)[n]) ≅ 𝒪_S` under `R f_* ⊣ a`. -/
noncomputable def dualizingTwistComparison :
    dualizingTwist n S ⟶ (Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf S) :=
  (Stacks.Duality.twistedInverseImageAdjunction (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (projectiveSpaceOver n S ↘ S))).homEquiv _ _ (dualizingTwistTraceIso n S).hom

/-- The comparison map, composed after a morphism `φ` out of a shifted twist, is the morphism
adjoint to `tr ∘ R f_*(φ)`. -/
theorem comp_dualizingTwistComparison_hom (T : Stacks.Duality.quasiCoherentDerivedCategory
      (projectiveSpaceOver n S)) (φ : T.obj ⟶ (dualizingTwist n S).obj) :
    φ ≫ (dualizingTwistComparison n S).hom =
      ((Stacks.Duality.twistedInverseImageAdjunction (projectiveSpaceOver n S ↘ S)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (projectiveSpaceOver n S ↘ S))).homEquiv
          T _ (ObjectProperty.homMk ((Stacks.Duality.derivedPushforward
            (projectiveSpaceOver n S ↘ S)).map φ ≫ (dualizingTwistTrace n S).hom))).hom :=
  (congrArg InducedCategory.Hom.hom
    ((Stacks.Duality.twistedInverseImageAdjunction (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (projectiveSpaceOver n S ↘ S))).homEquiv_naturality_left
      (ObjectProperty.homMk φ : T ⟶ dualizingTwist n S) (dualizingTwistTraceIso n S).hom)).symm

/-- For `0 ≤ i ≤ n`, composition with `c` is a bijection on morphisms out of
`𝒪(-i)[0]⟦q⟧`: the functors `F_{i,p}` of the source's proof carry `c` to bijections. -/
theorem bijective_comp_dualizingTwistComparison_hom (i : ℕ) (hi : i ≤ n) (q : ℤ) :
    Function.Bijective fun φ : (shiftFunctor _ q).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
          (twistOver n S (-(i : ℤ)))) ⟶ (dualizingTwist n S).obj =>
      φ ≫ (dualizingTwistComparison n S).hom := by
  let T : Stacks.Duality.quasiCoherentDerivedCategory (projectiveSpaceOver n S) :=
    ⟨_, derivedCategoryB_shift_single (twistOver n S (-(i : ℤ))) q⟩
  have hfun : (fun φ : T.obj ⟶ (dualizingTwist n S).obj =>
      φ ≫ (dualizingTwistComparison n S).hom) =
      (fun ψ => ψ.hom) ∘
        ((Stacks.Duality.twistedInverseImageAdjunction (projectiveSpaceOver n S ↘ S)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (projectiveSpaceOver n S ↘ S))).homEquiv T _) ∘ ObjectProperty.homMk ∘
        (fun φ : T.obj ⟶ (dualizingTwist n S).obj =>
          (Stacks.Duality.derivedPushforward (projectiveSpaceOver n S ↘ S)).map φ ≫
            (dualizingTwistTrace n S).hom) :=
    funext fun φ => comp_dualizingTwistComparison_hom n S T φ
  change Function.Bijective (fun φ : T.obj ⟶ (dualizingTwist n S).obj =>
      φ ≫ (dualizingTwistComparison n S).hom)
  rw [hfun]
  exact ((ObjectProperty.fullyFaithfulι _).map_bijective _ _).comp
    ((Equiv.bijective _).comp (Function.Bijective.comp
      ⟨fun _ _ h => congrArg InducedCategory.Hom.hom h, fun y => ⟨y.hom, rfl⟩⟩
      (bijective_derivedPushforward_map_comp_dualizingTwistTrace n S i hi q)))

/-- **The comparison map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_S)` is an isomorphism**, for `S` affine and
`n ≥ 0`. Its cone `Z` is bounded below ([Stacks, Tag 0A9I] for `a(𝒪_S)`) with quasi-coherent
cohomology, and receives no nonzero morphism from a shift of `𝒪, 𝒪(-1), …, 𝒪(-n)`, because `c`
induces bijections on morphisms out of those; hence `Z = 0` by the generation of
`D^+_QCoh(𝒪_{ℙⁿ_S})` by the twists. -/
theorem isIso_dualizingTwistComparison : IsIso (dualizingTwistComparison n S) := by
  set c := dualizingTwistComparison n S
  set P := DerivedCategoryB.derivedCategoryB (A := (projectiveSpaceOver n S).Modules)
    (SheafOfModules.isQuasicoherent (projectiveSpaceOver n S).ringCatSheaf)
  have : P.IsTriangulated := DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre _)
  suffices IsIso c.hom from
    have : IsIso ((ObjectProperty.ι P).map c) := this
    (ObjectProperty.fullyFaithfulι P).isIso_of_isIso_map c
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle c.hom
  have hT' := rot_of_distTriang _ hT
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  -- the cone receives no morphism from the generators
  have hZ : ∀ i : ℕ, i ≤ n → ∀ q : ℤ, Subsingleton ((shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S (-(i : ℤ)))) ⟶ Z) := fun i hi q =>
    subsingleton_of_forall_eq 0 fun x => eq_zero_of_mem_distTriang _ hT
      (bijective_comp_dualizingTwistComparison_hom n S i hi q).2
      (injective_comp_shift_map c.hom
        ((shiftFunctorAdd' (DerivedCategory (projectiveSpaceOver n S).Modules)
          (q - 1) 1 q (by omega)).app _)
        (bijective_comp_dualizingTwistComparison_hom n S i hi (q - 1)).1) x
  -- the cone is bounded below
  obtain ⟨N₀, hN₀⟩ := exists_isGE_twistedInverseImage_obj (projectiveSpaceOver n S ↘ S)
  have := hN₀ (Stacks.Duality.DerivedPushforward.derivedStructureSheaf S) 0
    (isGE_singleFunctor_zero (SheafOfModules.unit S.ringCatSheaf))
  set k : ℤ := min (0 - N₀) (-(n : ℤ) - 1)
  have hN : ((shiftFunctor _ (1 : ℤ)).obj (dualizingTwist n S).obj).IsGE k :=
    have := isGE_shift_one_dualizingTwist n S
    DerivedCategory.TStructure.t.isGE_of_ge _ k _ (min_le_right _ _)
  have hM' : ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf S)).obj.IsGE k :=
    DerivedCategory.TStructure.t.isGE_of_ge _ k _ (min_le_left _ _)
  have hZge : Z.IsGE k :=
    DerivedCategory.TStructure.t.isGE₂ _ hT' k hM' hN
  -- the cone has quasi-coherent cohomology
  have hZqc : P Z := P.ext_of_isTriangulatedClosed₂ _ hT'
    ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf S)).property
    (P.le_shift 1 _ (dualizingTwist n S).property)
  exact isZero_of_subsingleton_twistOver_shift_hom n S Z k hZge hZqc
    (subsingleton_twistOver_shift_hom n S Z hZ)

/-- **[Stacks, Tag 0A9W], the case of projective space.** Let `S` be an affine scheme, `n ≥ 0`,
`f : ℙⁿ_S ⟶ S` the structure morphism, and `a` the right adjoint of
`R f_* : D_QCoh(𝒪_{ℙⁿ_S}) ⥤ D_QCoh(𝒪_S)` of [Stacks, Tag 0A9E]. Then
`a(𝒪_S) ≅ 𝒪(-n-1)[n]`.

The source states the lemma for the projective bundle `𝐏(ℰ)` of a finite locally free module of
rank `n + 1` over a quasi-compact quasi-separated base, with `ℰ = 𝒪^{⊕ n+1}` giving `ℙⁿ`; this is
the case `ℰ = 𝒪_S^{⊕ n+1}` over an affine base, which is why no tag attribute is attached: the
general base and the projective bundle need the locality of `a` on the base
([Stacks, Tag 0A9P]), which is not in this library. -/
theorem nonempty_twistedInverseImage_derivedStructureSheaf_iso :
    Nonempty ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf S) ≅ dualizingTwist n S) := by
  have := isIso_dualizingTwistComparison n S
  exact ⟨(asIso (dualizingTwistComparison n S)).symm⟩

/-- `a(𝒪_S) ≅ 𝒪(-n-1)[n]` on `ℙⁿ_S`, `S` affine, with the right-hand side read as the module
`𝒪(-n-1)` placed in cohomological degree `-n`. -/
theorem nonempty_twistedInverseImage_derivedStructureSheaf_obj_iso_single :
    Nonempty (((Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf S)).obj ≅
      (DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules (-(n : ℤ))).obj
        (twistOver n S (-(n : ℤ) - 1))) := by
  obtain ⟨e⟩ := nonempty_twistedInverseImage_derivedStructureSheaf_iso n S
  exact ⟨(ObjectProperty.ι _).mapIso e ≪≫
    ((DerivedCategory.singleFunctors (projectiveSpaceOver n S).Modules).shiftIso (n : ℤ)
      (-(n : ℤ)) 0 (by omega)).app _⟩

end Main

end Stacks.Duality.ProjectiveSpace
