module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.LinearAlgebra.BilinearMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Coherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite Tor dimension and the perfect objects over a left Noetherian ring

Let `Λ` be a ring, not assumed commutative, and let `D(Λ)` be the derived category of left
`Λ`-modules. An object `K` of `D(Λ)` has *finite Tor dimension* when there are integers `a ≤ b`
such that, for every right `Λ`-module `N`, the cohomology of `N ⊗ᴸ[Λ] K` vanishes in every degree
outside `[a, b]`. When `Λ` is left Noetherian this condition, together with finiteness of every
cohomology module, characterizes the perfect objects of `D(Λ)` in the sense of
`StacksDraft.Perfect.IsPerfect`.

## Main definitions

* `StacksDraft.Perfect.BalancedDerivedTensoring`: the balanced tensor product of a right and a
  left `Λ`-module, pinned down by its universal property, together with its total left derived
  functor.
* `StacksDraft.Perfect.HasFiniteTorDimension`: finite Tor dimension of an object of `D(Λ)`.

## Main results

* `StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology`: over a left
  Noetherian ring an object of `D(Λ)` is perfect exactly when it has finite Tor dimension and all
  of its cohomology modules are finite.
* `StacksDraft.Perfect.hasFiniteTorDimension_iff_of_balancedDerivedTensoring`: finite Tor
  dimension does not depend on which balanced derived tensor product is used to read it off.

## References

* [Stacks Project, Tag 03TN](https://stacks.math.columbia.edu/tag/03TN)
* [Stacks Project, Tag 03TO](https://stacks.math.columbia.edu/tag/03TO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### The balanced derived tensor product as a parameter -/

/-- The balanced tensor product of a right and a left module over a possibly noncommutative ring,
together with its total left derived functor. The `pure` tensors and their universal property pin
down the ordinary bifunctor, and `comparison` together with `isLeftDerived` pins down the derived
bifunctor. -/
structure BalancedDerivedTensoring (Λ : Type u) [Ring Λ] where
  /-- Ordinary balanced tensoring of a right `Λ`-module with a left `Λ`-module. -/
  ordinary : ModuleCat.{v} (MulOpposite Λ) ⥤ ModuleCat.{v} Λ ⥤ ModuleCat.{v} ℤ
  /-- The pure tensor `n ⊗ m`, additive in each variable. -/
  pure : ∀ (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ),
    N →ₗ[ℤ] M →ₗ[ℤ] ((ordinary.obj N).obj M)
  /-- Pure tensors are balanced: `n · a ⊗ m = n ⊗ a · m`. -/
  balanced : ∀ (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (n : N) (a : Λ) (m : M),
      pure N M (MulOpposite.op a • n) m = pure N M n (a • m)
  /-- Every balanced biadditive map factors uniquely through the pure tensors. -/
  universal : ∀ (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q),
      (∀ (n : N) (a : Λ) (m : M), f (MulOpposite.op a • n) m = f n (a • m)) →
      ∃! g : ((ordinary.obj N).obj M) ⟶ Q, ∀ (n : N) (m : M), g (pure N M n m) = f n m
  /-- Functoriality in the right module acts on pure tensors in the first variable. -/
  natural_left : ∀ {N N' : ModuleCat.{v} (MulOpposite Λ)}
    (f : N ⟶ N') (M : ModuleCat.{v} Λ) (n : N) (m : M),
      ((ordinary.map f).app M) (pure N M n m) = pure N' M (f n) m
  /-- Functoriality in the left module acts on pure tensors in the second variable. -/
  natural_right : ∀ (N : ModuleCat.{v} (MulOpposite Λ))
    {M M' : ModuleCat.{v} Λ} (f : M ⟶ M') (n : N) (m : M),
      ((ordinary.obj N).map f) (pure N M n m) = pure N M' n (f m)
  /-- Tensoring with a fixed right module is an additive functor. -/
  additive : ∀ N : ModuleCat.{v} (MulOpposite Λ), (ordinary.obj N).Additive
  /-- The derived tensor bifunctor on `D(Λ)`. -/
  derived : ModuleCat.{v} (MulOpposite Λ) ⥤
    DerivedCategory (ModuleCat.{v} Λ) ⥤ DerivedCategory (ModuleCat.{v} ℤ)
  /-- The comparison of the derived bifunctor with termwise ordinary tensoring. -/
  comparison : ∀ N : ModuleCat.{v} (MulOpposite Λ),
    DerivedCategory.Q ⋙ derived.obj N ⟶
      (ordinary.obj N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  /-- The comparison exhibits each `N ⊗ᴸ -` as the total left derived functor of `N ⊗ -`. -/
  isLeftDerived : ∀ N : ModuleCat.{v} (MulOpposite Λ),
    (derived.obj N).IsLeftDerivedFunctor (comparison N)
      (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ))

/-- An object `K` of `D(Λ)` has *finite Tor dimension* if there are integers `a, b` such that
`Hⁱ(N ⊗ᴸ[Λ] K) = 0` for every right `Λ`-module `N` and every `i ∉ [a, b]`. -/
@[stacks 03TN, sga "4½ Rapport 4.5" "finite tor dimension"]
def HasFiniteTorDimension {Λ : Type u} [Ring Λ] (D : BalancedDerivedTensoring.{u, v} Λ)
    (K : DerivedCategory (ModuleCat.{v} Λ)) : Prop :=
  ∃ a b : ℤ, ∀ (N : ModuleCat.{v} (MulOpposite Λ)) (i : ℤ),
    i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i).obj
        ((D.derived.obj N).obj K))

/-! ### Invertibility of the comparison at a K-projective complex -/

section Comparison

private lemma isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft
    {C C' E H : Type*} [Category* C] [Category* C'] [Category* E] [Category* H]
    (q : C' ⥤ C) [((whiskeringLeft C' C H).obj q).Full]
    [((whiskeringLeft C' C H).obj q).Faithful]
    {L : C ⥤ E} {F : C ⥤ H} (LF : E ⥤ H) (α : L ⋙ LF ⟶ F) :
    LF.IsRightKanExtension α ↔ LF.IsRightKanExtension
      ((Functor.associator _ _ _).hom ≫ whiskerLeft q α) := by
  have : (RightExtension.precomp L F q).IsEquivalence := by
    apply CostructuredArrow.isEquivalenceMap₂
  let eq : (RightExtension.mk LF α).IsUniversal ≃
      (RightExtension.mk LF ((Functor.associator _ _ _).hom ≫ whiskerLeft q α)).IsUniversal :=
    (IsTerminal.isTerminalIffObj (RightExtension.precomp L F q)
      (RightExtension.mk LF α)).trans
      (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  exact ⟨fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension LF α)⟩⟩,
    fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension LF _)⟩⟩⟩

private lemma isRightKanExtension_iff_of_iso
    {C E H : Type*} [Category* C] [Category* E] [Category* H]
    {L₀ L₁ : C ⥤ E} {F₀ F₁ : C ⥤ H} (LF : E ⥤ H)
    (eL : L₀ ≅ L₁) (eF : F₁ ≅ F₀) (α : L₁ ⋙ LF ⟶ F₁) :
    LF.IsRightKanExtension α ↔
      LF.IsRightKanExtension (whiskerRight eL.hom LF ≫ α ≫ eF.hom) := by
  have h₁ := isRightKanExtension_iff_postcomp₁ (𝟭 E) (Functor.rightUnitor L₀ ≪≫ eL) α
  have heq : (Functor.associator L₀ (𝟭 E) LF).inv ≫
      whiskerRight (Functor.rightUnitor L₀ ≪≫ eL).hom LF ≫ α =
      whiskerRight eL.hom LF ≫ α := by ext; simp
  rw [heq] at h₁
  exact h₁.trans (isRightKanExtension_iff_of_iso₂
    (whiskerRight eL.hom LF ≫ α) (whiskerRight eL.hom LF ≫ α ≫ eF.hom)
    eF (Iso.refl LF) (by simp))

/-- The copower of an object by the morphisms out of a fixed object. -/
private abbrev pointCopower
    {C H : Type*} [Category* C] [Category* H] (X : C)
    [∀ Y : C, HasCoproductsOfShape (X ⟶ Y) H] (A : H) : C ⥤ H where
  obj Y := ∐ fun _ : X ⟶ Y => A
  map f := Sigma.desc fun g => Sigma.ι (fun _ => A) (g ≫ f)

/-- The map out of the copower determined by one morphism `A ⟶ F X`. -/
private def pointCopowerDesc
    {C H : Type*} [Category* C] [Category* H] (X : C)
    [∀ Y : C, HasCoproductsOfShape (X ⟶ Y) H] (A : H)
    (F : C ⥤ H) (f : A ⟶ F.obj X) : pointCopower X A ⟶ F where
  app Y := Sigma.desc fun g => f ≫ F.map g
  naturality := by intros; ext; simp [pointCopower, Functor.map_comp]

/-- A right Kan extension along `q` is invertible at an object out of which `q` is bijective on
morphisms. -/
private lemma isIso_app_of_isRightKanExtension_of_map_bijective
    {C E H : Type*} [Category* C] [Category* E] [Category* H]
    (q : C ⥤ E) (F : C ⥤ H) (LF : E ⥤ H) (α : q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] (X : C)
    [∀ Y : E, HasCoproductsOfShape (q.obj X ⟶ Y) H]
    (hq : ∀ Y : C, Function.Bijective (q.map : (X ⟶ Y) → (q.obj X ⟶ q.obj Y))) :
    IsIso (α.app X) := by
  classical
  let e (Y : C) := Equiv.ofBijective (q.map : (X ⟶ Y) → _) (hq Y)
  have he (Y : C) (f : q.obj X ⟶ q.obj Y) : q.map ((e Y).symm f) = f :=
    (e Y).apply_symm_apply f
  have heid : (e X).symm (𝟙 (q.obj X)) = 𝟙 X := by
    apply (hq X).injective
    simp [he]
  let G := pointCopower (q.obj X) (F.obj X)
  let β : q ⋙ G ⟶ F := {
    app Y := Sigma.desc fun f => F.map ((e Y).symm f)
    naturality := by
      intro Y Z g
      dsimp [G, pointCopower]
      ext f
      simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, colimit.ι_desc]
      rw [← F.map_comp]
      congr 1
      apply (hq Z).injective
      rw [he, q.map_comp, he] }
  let φ := LF.liftOfIsRightKanExtension α G β
  let s : F.obj X ⟶ LF.obj (q.obj X) :=
    Sigma.ι (fun _ : q.obj X ⟶ q.obj X => F.obj X) (𝟙 _) ≫ φ.app (q.obj X)
  have hs : s ≫ α.app X = 𝟙 _ := by
    dsimp [s, φ]
    rw [Category.assoc, LF.liftOfIsRightKanExtension_fac_app α G β X]
    dsimp [β]
    simp [heid]
  have hm : Mono (α.app X) := by
    constructor
    intro A f g hfg
    let δf := pointCopowerDesc (q.obj X) A LF f
    let δg := pointCopowerDesc (q.obj X) A LF g
    have hδ : δf = δg := by
      apply LF.hom_ext_of_isRightKanExtension α
      ext Y
      dsimp [δf, δg, pointCopowerDesc]
      ext k
      simp only [Category.assoc, colimit.ι_desc_assoc, Cofan.mk_ι_app]
      rw [← he Y k]
      have hn := α.naturality ((e Y).symm k)
      change LF.map (q.map ((e Y).symm k)) ≫ α.app Y =
        α.app X ≫ F.map ((e Y).symm k) at hn
      rw [hn, ← Category.assoc, ← Category.assoc, hfg]
    have hh := congrArg (fun δ =>
      Sigma.ι (fun _ : q.obj X ⟶ q.obj X => A) (𝟙 _) ≫ δ.app (q.obj X)) hδ
    simpa [δf, δg, pointCopowerDesc] using hh
  exact ⟨s, by apply (cancel_mono (α.app X)).1; simp [hs], hs⟩

private lemma moduleCatInt_hasCoproducts (J : Type*) [Small.{v} J] :
    HasCoproductsOfShape J (DerivedCategory (ModuleCat.{v} ℤ)) := by
  have : HasCoproductsOfShape J (ModuleCat.{v} ℤ) := hasCoproductsOfShape_of_small _ J
  have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} ℤ) :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})
  have : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := ModuleCat.{v} ℤ)) :=
    derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives _ J
  constructor
  intro F
  let G := Discrete.functor (fun j : J => DerivedCategory.Q.objPreimage (F.obj ⟨j⟩))
  have : HasColimit (G ⋙ DerivedCategory.Q) := inferInstance
  exact hasColimit_of_iso (F := G ⋙ DerivedCategory.Q) (Discrete.natIso fun j =>
    (DerivedCategory.Q.objObjPreimageIso (F.obj j)).symm)

/-- The comparison between a total left derived functor and termwise application is invertible at
a K-projective complex. -/
private lemma isIso_comparison_of_isKProjective
    {Λ : Type u} [Ring Λ]
    (F : ModuleCat.{v} Λ ⥤ ModuleCat.{v} ℤ) [F.Additive]
    (LF : DerivedCategory (ModuleCat.{v} Λ) ⥤ DerivedCategory (ModuleCat.{v} ℤ))
    (α : DerivedCategory.Q ⋙ LF ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [LF.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ))]
    (P : CochainComplex (ModuleCat.{v} Λ) ℤ) [P.IsKProjective] : IsIso (α.app P) := by
  let q := HomotopyCategory.quotient (ModuleCat.{v} Λ) (ComplexShape.up ℤ)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let eL := DerivedCategory.quotientCompQhIso (ModuleCat.{v} Λ)
  let eF : q ⋙ Fh ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (ModuleCat.{v} ℤ))
  let β : DerivedCategory.Qh ⋙ LF ⟶ Fh :=
    ((whiskeringLeft _ _ _).obj q).preimage
      ((Functor.associator _ _ _).inv ≫ whiskerRight eL.hom LF ≫ α ≫ eF.inv)
  have hβ : (Functor.associator _ _ _).hom ≫ whiskerLeft q β =
      whiskerRight eL.hom LF ≫ α ≫ eF.inv := by
    dsimp [β]
    rw [← whiskeringLeft_obj_map, map_preimage]
    simp
  have : LF.IsRightKanExtension β := by
    rw [isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft q LF β, hβ]
    exact (isRightKanExtension_iff_of_iso LF eL eF.symm α).1
      (IsLeftDerivedFunctor.isRightKanExtension LF α
        (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ)))
  have hcop (Y : DerivedCategory (ModuleCat.{v} Λ)) :
      HasCoproductsOfShape (DerivedCategory.Qh.obj (q.obj P) ⟶ Y)
        (DerivedCategory (ModuleCat.{v} ℤ)) := by
    let Y' := DerivedCategory.Qh.objPreimage Y
    have hs : Small.{v} (DerivedCategory.Qh.obj (q.obj P) ⟶ DerivedCategory.Qh.obj Y') :=
      small_of_surjective (CochainComplex.IsKProjective.Qh_map_bijective P Y').surjective
    have : Small.{v} (DerivedCategory.Qh.obj (q.obj P) ⟶ Y) :=
      small_of_surjective ((Iso.refl _).homCongr
        (DerivedCategory.Qh.objObjPreimageIso Y)).surjective
    exact moduleCatInt_hasCoproducts _
  have hiso : IsIso (β.app (q.obj P)) :=
    isIso_app_of_isRightKanExtension_of_map_bijective DerivedCategory.Qh Fh LF β (q.obj P)
      (fun Y => CochainComplex.IsKProjective.Qh_map_bijective P Y)
  have heq := congr_app hβ P
  simp only [NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
    Category.id_comp, whiskerRight_app] at heq
  rw [heq] at hiso
  have : IsIso ((LF.map (eL.hom.app P) ≫ α.app P) ≫ eF.inv.app P) := by
    simpa only [Category.assoc] using hiso
  have := IsIso.of_isIso_comp_right (LF.map (eL.hom.app P) ≫ α.app P) (eF.inv.app P)
  exact IsIso.of_isIso_comp_left (LF.map (eL.hom.app P)) (α.app P)

/-- If the comparison is invertible at a complex `P` with `Q P ≅ K`, then `Hⁱ(N ⊗ᴸ[Λ] K)` vanishes
exactly when the `i`-th cohomology of the termwise tensor product `N ⊗ P` does. -/
private lemma isZero_homology_tensor_iff {Λ : Type u} [Ring Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (N : ModuleCat.{v} Λᵐᵒᵖ)
    (P : CochainComplex (ModuleCat.{v} Λ) ℤ) (K : DerivedCategory (ModuleCat.{v} Λ))
    (e : DerivedCategory.Q.obj P ≅ K) [(D.ordinary.obj N).PreservesZeroMorphisms]
    [IsIso ((D.comparison N).app P)] (i : ℤ) :
    IsZero (((D.ordinary.obj N).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj P).homology i) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i).obj
        ((D.derived.obj N).obj K)) :=
  Iso.isZero_iff
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} ℤ) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i).mapIso
        ((asIso ((D.comparison N).app P)).symm ≪≫ (D.derived.obj N).mapIso e))

/-- The comparison of a balanced derived tensor product is invertible at a K-projective
complex. -/
private lemma isIso_comparison_app_of_isKProjective {Λ : Type u} [Ring Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (N : ModuleCat.{v} Λᵐᵒᵖ)
    (P : CochainComplex (ModuleCat.{v} Λ) ℤ) [P.IsKProjective] :
    IsIso ((D.comparison N).app P) := by
  let _ : (D.ordinary.obj N).Additive := D.additive N
  let _ : (D.derived.obj N).IsLeftDerivedFunctor (D.comparison N)
      (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ)) :=
    D.isLeftDerived N
  exact isIso_comparison_of_isKProjective (D.ordinary.obj N) (D.derived.obj N) (D.comparison N) P

end Comparison

/-! ### Perfect objects have finite Tor dimension and finite cohomology -/

section OfIsPerfect

/-- Over a left Noetherian ring the cohomology of a complex in a degree whose term is finite is
finite. -/
private lemma finite_homology_of_finite_term
    {Λ : Type u} [Ring Λ] [IsNoetherianRing Λ]
    (P : CochainComplex (ModuleCat.{v} Λ) ℤ) (i : ℤ)
    [Module.Finite Λ (P.X i)] :
    Module.Finite Λ
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} Λ)
        (ComplexShape.up ℤ) i).obj P) := by
  change Module.Finite Λ (P.homology i)
  have : IsNoetherian Λ (P.X i) := inferInstance
  have : Module.Finite Λ (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (P.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Over a left Noetherian ring every cohomology module of a perfect object is finite. -/
public lemma finite_homology_of_isPerfect
    (Λ : Type u) [Ring Λ] [IsNoetherianRing Λ]
    (K : DerivedCategory (ModuleCat.{v} Λ)) (hK : IsPerfect K) :
    ∀ i : ℤ,
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj K) := by
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hK
  intro i
  let _ : Module.Finite Λ (P.X i) := hfinite i
  have := finite_homology_of_finite_term P i
  have hQ : Module.Finite Λ
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj
        (DerivedCategory.Q.obj P)) :=
    Module.Finite.equiv
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} Λ) i).app P).symm.toLinearEquiv)
  exact Module.Finite.equiv
    ((((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).mapIso e).toLinearEquiv).symm)

/-- A perfect object has finite Tor dimension. -/
private lemma hasFiniteTorDimension_of_isPerfect
    {Λ : Type u} [Ring Λ] (D : BalancedDerivedTensoring.{u, v} Λ)
    (K : DerivedCategory (ModuleCat.{v} Λ)) (hK : IsPerfect K) :
    HasFiniteTorDimension D K := by
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hK
  refine ⟨a, b, fun N i hi => ?_⟩
  let F := D.ordinary.obj N
  let _ : F.Additive := D.additive N
  let T : CochainComplex (ModuleCat.{v} ℤ) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i
  have hPproj : ∀ j : ℤ, Module.Projective Λ (P.X j) := hprojective
  let _ (j : ℤ) : Module.Projective Λ (P.X j) := hPproj j
  let _ := hLE
  let _ : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  have hcomp : IsIso ((D.comparison N).app P) :=
    isIso_comparison_app_of_isKProjective D N P
  have hTGE : T.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact F.map_isZero ((CochainComplex.isStrictlyGE_iff P a).mp hGE j hj)
  have hTLE : T.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact F.map_isZero ((CochainComplex.isStrictlyLE_iff P b).mp hLE j hj)
  have hTzero : IsZero (T.homology i) := by
    let _ := hTGE
    let _ := hTLE
    refine IsZero.of_iso ?_
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} ℤ) i).app T).symm
    rcases lt_or_ge i a with hlow | hlow
    · let _ : (DerivedCategory.Q.obj T).IsGE a := by infer_instance
      exact DerivedCategory.isZero_of_isGE _ a i hlow
    · have hhigh : b < i := by
        have h := hi
        simp only [Set.mem_Icc] at h
        omega
      let _ : (DerivedCategory.Q.obj T).IsLE b := by infer_instance
      exact DerivedCategory.isZero_of_isLE _ b i hhigh
  exact (isZero_homology_tensor_iff D N P K e.symm i).1 hTzero

end OfIsPerfect

/-! ### Tensoring with the regular right module -/

section Regular

/-- An additive map between `ℤ`-modules is `ℤ`-linear. -/
private def intLinearMap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  __ := f
  map_smul' n x := by simpa using (map_intCast_smul f ℤ ℤ n x)

/-- Two maps out of a balanced tensor product agreeing on pure tensors are equal. -/
private lemma tensor_hom_ext {Λ : Type u} [Ring Λ] (D : BalancedDerivedTensoring.{u, v} Λ)
    (N : ModuleCat.{v} Λᵐᵒᵖ) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (f g : (D.ordinary.obj N).obj M ⟶ Q)
    (h : ∀ n m, f (D.pure N M n m) = g (D.pure N M n m)) : f = g := by
  let b : N →ₗ[ℤ] M →ₗ[ℤ] Q :=
    intLinearMap {
      toFun n := f.hom.comp (D.pure N M n)
      map_zero' := by ext m; simp
      map_add' n n' := by ext m; simp }
  have hb : ∀ (n : N) (a : Λ) (m : M), b (MulOpposite.op a • n) m = b n (a • m) := by
    intro n a m
    exact congrArg f (D.balanced N M n a m)
  obtain ⟨l, hl, hu⟩ := D.universal N M Q b hb
  exact (hu f (by intro n m; rfl)).trans (hu g (by intro n m; exact (h n m).symm)).symm

/-- Tensoring with the regular right module is restriction of scalars to `ℤ`. -/
private def regularTensorIso {Λ : Type u} [Ring Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) :
    D.ordinary.obj (ModuleCat.of Λᵐᵒᵖ (Shrink.{v} Λ)) ≅
      ModuleCat.restrictScalars (Int.castRingHom Λ) := by
  let N := ModuleCat.of Λᵐᵒᵖ (Shrink.{v} Λ)
  let e := Shrink.linearEquiv.{v} Λᵐᵒᵖ Λ
  let one : N := e.symm 1
  let b (M : ModuleCat.{v} Λ) :
      N →ₗ[ℤ] M →ₗ[ℤ] ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M) :=
    intLinearMap {
      toFun n := @intLinearMap M ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M)
        _ _ _ ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M).isModule {
          toFun m := (e n) • m
          map_zero' := by change (e n) • (0 : M) = 0; exact smul_zero (e n)
          map_add' := by intro x y; exact smul_add (e n) x y }
      map_zero' := by ext m; change (e 0) • m = 0; simp
      map_add' n n' := by ext m; change (e (n + n')) • m = (e n) • m + (e n') • m; simp [add_smul] }
  have hb (M : ModuleCat.{v} Λ) (n : N) (a : Λ) (m : M) :
      b M (MulOpposite.op a • n) m = b M n (a • m) := by
    change (e (MulOpposite.op a • n)) • m = (e n) • a • m
    calc
      _ = (MulOpposite.op a • e n) • m :=
        congrArg (fun r : Λ => r • m) (e.map_smul (MulOpposite.op a) n)
      _ = _ := by simp [MulOpposite.smul_eq_mul_unop, mul_smul]
  choose f hf huniq using fun M => D.universal N M
    ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M) (b M) (hb M)
  have hf' (M : ModuleCat.{v} Λ) (n : N) (m : M) :
      f M (D.pure N M n m) = (e n) • m := hf M n m
  let g (M : ModuleCat.{v} Λ) :
      (ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M ⟶ (D.ordinary.obj N).obj M :=
    @ModuleCat.ofHom ℤ _
      ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M) ((D.ordinary.obj N).obj M)
      _ ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M).isModule _ _
      (@intLinearMap ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M)
        ((D.ordinary.obj N).obj M) _ _
        ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M).isModule
        ((D.ordinary.obj N).obj M).isModule (D.pure N M one).toAddMonoidHom)
  have hg (M : ModuleCat.{v} Λ) (n : N) (m : M) :
      g M ((e n) • m) = D.pure N M n m := by
    change D.pure N M one ((e n) • m) = _
    rw [← D.balanced]
    congr 2
    apply e.injective
    simp [one, MulOpposite.smul_eq_mul_unop]
  let ei (M : ModuleCat.{v} Λ) :
      (D.ordinary.obj N).obj M ≅ (ModuleCat.restrictScalars (Int.castRingHom Λ)).obj M := {
    hom := f M
    inv := g M
    hom_inv_id := by
      apply tensor_hom_ext D N M
      intro n m
      change g M (f M (D.pure N M n m)) = D.pure N M n m
      rw [hf', hg]
    inv_hom_id := by
      ext m
      change f M (D.pure N M one m) = m
      have hh := hf' M one m
      rw [show e one = (1 : Λ) by simp [one]] at hh
      exact hh.trans (one_smul Λ m) }
  exact NatIso.ofComponents ei (by
    intro M M' k
    apply tensor_hom_ext D N M
    intro n m
    change f M' (((D.ordinary.obj N).map k) (D.pure N M n m)) = k (f M (D.pure N M n m))
    rw [D.natural_right, hf', hf', _root_.map_smul])

/-- Vanishing of `Hⁱ(N ⊗ᴸ[Λ] K)` for every right module `N` forces `Hⁱ(K) = 0`. -/
private lemma homology_isZero_of_tor_bound {Λ : Type u} [Ring Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (K : DerivedCategory (ModuleCat.{v} Λ)) (i : ℤ)
    (h : ∀ N : ModuleCat.{v} Λᵐᵒᵖ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i).obj
        ((D.derived.obj N).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj K) := by
  let N := ModuleCat.of Λᵐᵒᵖ (Shrink.{v} Λ)
  let F := D.ordinary.obj N
  let G := ModuleCat.restrictScalars (Int.castRingHom Λ)
  let e : F ≅ G := regularTensorIso D
  let _ : F.Additive := D.additive N
  let U := forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}
  let _ : PreservesFiniteLimits (G ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}))
  let _ : PreservesColimitsOfSize.{0, 0} (G ⋙ U) := by
    change PreservesColimitsOfSize.{0, 0} (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})
    exact ModuleCat.forget₂PreservesColimitsOfSize.{v, u, 0, 0} Λ
  let _ : PreservesFiniteColimits (G ⋙ U) := PreservesColimitsOfSize0.preservesFiniteColimits _
  let _ : PreservesFiniteLimits G := preservesFiniteLimits_of_reflects_of_preserves G U
  let _ : PreservesFiniteColimits G := preservesFiniteColimits_of_reflects_of_preserves G U
  let _ : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso e.symm
  let _ : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso e.symm
  let _ : (D.derived.obj N).IsLeftDerivedFunctor (D.comparison N)
      (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ)) := D.isLeftDerived N
  have : IsIso (D.comparison N) :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      (W := HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ))
      (D.derived.obj N) (D.comparison N)
      (by
        intro X Y f hf
        let _ : QuasiIso f := hf
        change IsIso (DerivedCategory.Q.map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
        infer_instance)
  let P := DerivedCategory.Q.objPreimage K
  let eP : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let T := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hz : IsZero (T.homology i) :=
    (isZero_homology_tensor_iff D N P K eP i).2 (h N)
  have hz' : IsZero (G.obj (P.homology i)) :=
    hz.of_iso ((P.sc i).mapHomologyIso F ≪≫ e.app (P.homology i)).symm
  have hzP : IsZero (P.homology i) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ((ModuleCat.isZero_iff_subsingleton (M := G.obj (P.homology i))).mp hz')
  exact hzP.of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).mapIso eP.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} Λ) i).app P)

end Regular

/-! ### Projectivity of the cokernel at the bottom of the window -/

section Cokernel

/-- Coordinates of a balanced tensor product with a finite free left module. -/
private lemma exists_tensor_coordinates {Λ : Type u} [Ring Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (N : ModuleCat.{v} Λᵐᵒᵖ)
    (M : ModuleCat.{v} Λ) {ι : Type v} [Fintype ι] (b : Module.Basis ι Λ M) :
    ∃ c : (D.ordinary.obj N).obj M →ₗ[ℤ] (ι → N),
      (∀ n m i, c (D.pure N M n m) i = MulOpposite.op (b.repr m i) • n) ∧
      ∀ t, (∑ i, D.pure N M (c t i) (b i)) = t := by
  classical
  let β : N →ₗ[ℤ] M →ₗ[ℤ] (ι → N) := intLinearMap {
    toFun n := intLinearMap {
      toFun m i := MulOpposite.op (b.repr m i) • n
      map_zero' := by ext i; simp
      map_add' := by intros; ext i; simp [add_smul] }
    map_zero' := by ext m i; simp [intLinearMap]
    map_add' := by intros; ext m i; simp [intLinearMap, smul_add] }
  have hβ (n : N) (a : Λ) (m : M) : β (MulOpposite.op a • n) m = β n (a • m) := by
    ext i
    change MulOpposite.op (b.repr m i) • (MulOpposite.op a • n) =
      MulOpposite.op (b.repr (a • m) i) • n
    simp [← mul_smul, MulOpposite.op_mul]
  obtain ⟨c, hc, -⟩ := D.universal N M (ModuleCat.of ℤ (ι → N)) β hβ
  have hc' (n : N) (m : M) (i : ι) :
      c (D.pure N M n m) i = MulOpposite.op (b.repr m i) • n :=
    congrFun (hc n m) i
  let r : ModuleCat.of ℤ (ι → N) ⟶ (D.ordinary.obj N).obj M :=
    ModuleCat.ofHom (intLinearMap {
      toFun x := ∑ i, D.pure N M (x i) (b i)
      map_zero' := by simp
      map_add' := by intros; simp [Finset.sum_add_distrib] })
  have hcr : c ≫ r = 𝟙 _ := by
    apply tensor_hom_ext D N M
    intro n m
    change (∑ i, D.pure N M (c (D.pure N M n m) i) (b i)) = D.pure N M n m
    simp only [hc', D.balanced]
    rw [← _root_.map_sum, b.sum_repr]
  exact ⟨c.hom, hc', fun t => congrArg (fun f => f t) hcr⟩

/-- The dual basis expansion of a linear functional on a finite free module. -/
private lemma sum_dual_basis {Λ : Type u} [Ring Λ] (M : ModuleCat.{v} Λ)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι Λ M) (φ : M →ₗ[Λ] Λ) :
    (∑ i, MulOpposite.op (φ (b i)) • b.coord i) = φ := by
  classical
  apply b.ext; intro i
  simp [Module.Basis.coord_apply, MulOpposite.smul_eq_mul_unop, Finsupp.single_apply]

/-- If tensoring a two-step complex of finite free modules with every right module stays exact in
the middle, the cokernel of its second map is projective. -/
private lemma projective_cokernel_of_tensor_exact {Λ : Type u} [Ring Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (S : ShortComplex (ModuleCat.{v} Λ))
    [Module.Finite Λ S.X₁] [Module.Free Λ S.X₁]
    [Module.Finite Λ S.X₂] [Module.Free Λ S.X₂]
    [Module.Finite Λ S.X₃] [Module.Free Λ S.X₃]
    (hex : ∀ (N : ModuleCat.{v} Λᵐᵒᵖ) (x : (D.ordinary.obj N).obj S.X₂),
      (D.ordinary.obj N).map S.g x = 0 → ∃ y, (D.ordinary.obj N).map S.f y = x) :
    Module.Projective Λ (cokernel S.g : ModuleCat.{v} Λ) := by
  classical
  let bA := Module.Free.chooseBasis Λ S.X₂
  let bB := Module.Free.chooseBasis Λ S.X₃
  let bC := Module.Free.chooseBasis Λ S.X₁
  let V := LinearMap.range (LinearMap.lcomp Λᵐᵒᵖ Λ S.g.hom)
  have : Small.{v} (S.X₂ →ₗ[Λ] Λ) := small_of_injective DFunLike.coe_injective
  have : Small.{v} ((S.X₂ →ₗ[Λ] Λ) ⧸ V) := inferInstance
  let N := ModuleCat.of Λᵐᵒᵖ (Shrink.{v} ((S.X₂ →ₗ[Λ] Λ) ⧸ V))
  let q : (S.X₂ →ₗ[Λ] Λ) →ₗ[Λᵐᵒᵖ] N :=
    (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm.toLinearMap.comp V.mkQ
  have hq_surj : Function.Surjective q :=
    (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm.surjective.comp
      (Submodule.mkQ_surjective V)
  have hq_zero (φ : S.X₃ →ₗ[Λ] Λ) : q (φ.comp S.g.hom) = 0 := by
    have hv : V.mkQ (φ.comp S.g.hom) = 0 :=
      (Submodule.Quotient.mk_eq_zero V).2 ⟨φ, rfl⟩
    change (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm
      (V.mkQ (φ.comp S.g.hom)) = 0
    rw [hv, map_zero]
  obtain ⟨cA, hcA, hrA⟩ := exists_tensor_coordinates D N S.X₂ bA
  obtain ⟨cB, hcB, hrB⟩ := exists_tensor_coordinates D N S.X₃ bB
  obtain ⟨cC, hcC, hrC⟩ := exists_tensor_coordinates D N S.X₁ bC
  let x := ∑ i, D.pure N S.X₂ (q (bA.coord i)) (bA i)
  have hx : (D.ordinary.obj N).map S.g x = 0 := by
    have hz : cB ((D.ordinary.obj N).map S.g x) = 0 := by
      funext j
      change cB ((D.ordinary.obj N).map S.g (∑ i, _)) j = 0
      simp +instances only [_root_.map_sum, Finset.sum_apply, D.natural_right, hcB]
      calc
        _ = q (∑ i, MulOpposite.op (bB.repr (S.g (bA i)) j) • bA.coord i) := by
          simp +instances
        _ = 0 := by
          change q (∑ i, MulOpposite.op (((bB.coord j).comp S.g.hom) (bA i)) •
            bA.coord i) = 0
          rw [sum_dual_basis]
          exact hq_zero _
    rw [← hrB ((D.ordinary.obj N).map S.g x), hz]
    simp
  obtain ⟨y, hy⟩ := hex N x hx
  choose φ hφ using fun l => hq_surj (cC y l)
  let h : S.X₂ →ₗ[Λ] S.X₁ := ∑ l, (φ l).smulRight (bC l)
  have hycoord (i : Module.Free.ChooseBasisIndex Λ S.X₂) :
      q (bA.coord i) = q ((bA.coord i).comp (S.f.hom.comp h)) := by
    have he := congrArg (fun t => cA t i) hy
    rw [← hrC y] at he
    simp +instances only [_root_.map_sum, Finset.sum_apply, D.natural_right, hcA] at he
    have hxi : cA x i = q (bA.coord i) := by
      simp +instances only [_root_.map_sum, Finset.sum_apply, hcA, Module.Basis.repr_self,
        Finsupp.single_apply, apply_ite, MulOpposite.op_one, MulOpposite.op_zero, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, x]
      exact one_smul Λᵐᵒᵖ _
    rw [hxi] at he
    rw [← he]
    simp +instances only [← hφ, ← _root_.map_smul, ← _root_.map_sum]
    congr 1
    ext a
    simp +instances [h, LinearMap.sum_apply, _root_.map_sum, _root_.map_smul,
      MulOpposite.smul_eq_mul_unop]
  have hmem (i : Module.Free.ChooseBasisIndex Λ S.X₂) :
      bA.coord i - (bA.coord i).comp (S.f.hom.comp h) ∈ V := by
    have hh : q (bA.coord i - (bA.coord i).comp (S.f.hom.comp h)) = 0 := by
      rw [_root_.map_sub, hycoord, sub_self]
    apply (Submodule.Quotient.mk_eq_zero V).1
    apply (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm.injective
    rw [map_zero]
    exact hh
  choose ψ hψ using hmem
  let s : S.X₃ →ₗ[Λ] S.X₂ := ∑ i, (ψ i).smulRight (bA i)
  have hs (a : S.X₂) : s (S.g a) = a - S.f (h a) := by
    change (∑ i, (ψ i).smulRight (bA i)) (S.g a) = _
    simp +instances only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    have hψ' (i : Module.Free.ChooseBasisIndex Λ S.X₂) :
        ψ i (S.g a) = bA.repr a i - bA.repr (S.f (h a)) i :=
      LinearMap.congr_fun (hψ i) a
    simp +instances only [hψ', sub_smul, Finset.sum_sub_distrib, bA.sum_repr]
  let s' : S.X₃ ⟶ S.X₂ := ModuleCat.ofHom s
  have hgs : S.g ≫ s' ≫ S.g = S.g := by
    ext a
    change S.g (s (S.g a)) = S.g a
    rw [hs, _root_.map_sub]
    have hz : S.g (S.f (h a)) = 0 :=
      congrArg (fun f : S.X₁ ⟶ S.X₃ => f (h a)) S.zero
    rw [hz, sub_zero]
  let i : cokernel S.g ⟶ S.X₃ := cokernel.desc S.g (𝟙 S.X₃ - s' ≫ S.g) (by
    simp +instances only [Preadditive.comp_sub, hgs, Category.comp_id, sub_self])
  have hi : i ≫ cokernel.π S.g = 𝟙 _ := by
    apply (cancel_epi (cokernel.π S.g)).1
    dsimp +instances [i]
    simp +instances [Preadditive.sub_comp, Category.id_comp]
  exact Module.Projective.of_split i.hom (cokernel.π S.g).hom
    (by simpa using congrArg ModuleCat.Hom.hom hi)

end Cokernel

/-! ### The characterization -/

/-- Let `Λ` be a left Noetherian ring and let `K` be an object of `D(Λ)`. Then `K` is perfect if
and only if `K` has finite Tor dimension and `Hⁱ(K)` is a finite `Λ`-module for every `i`. -/
@[stacks 03TO, sga "5 VIII 8.1" "Noetherian case", sga "4½ Rapport 4.5.1"]
theorem isPerfect_iff_hasFiniteTorDimension_and_finite_homology
    {Λ : Type u} [Ring Λ] [IsNoetherianRing Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (K : DerivedCategory (ModuleCat.{v} Λ)) :
    IsPerfect K ↔
      (HasFiniteTorDimension D K ∧
        ∀ i : ℤ,
          Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj K)) := by
  constructor
  · exact fun hK => ⟨hasFiniteTorDimension_of_isPerfect D K hK,
      finite_homology_of_isPerfect Λ K hK⟩
  · rintro ⟨⟨a, b, hab⟩, hfin⟩
    have hzero (i : ℤ) (hi : i ∉ Set.Icc a b) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj K) :=
      homology_isZero_of_tor_bound D K i (fun N => hab N i hi)
    have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
      (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
        K 0 ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) 0).obj K)).2.1.mpr
        ⟨⟨b, fun i hi => hzero i (by simp only [Set.mem_Icc]; omega)⟩, hfin⟩
    obtain ⟨F, hF, ⟨eF⟩⟩ := hpseudo
    obtain ⟨c, hFc⟩ := hF.upperBound
    have hFfin (i : ℤ) : Module.Finite Λ (F.X i) := (hF.finiteFree i).1
    have hFfree (i : ℤ) : Module.Free Λ (F.X i) := (hF.finiteFree i).2
    let _ (i : ℤ) : Module.Finite Λ (F.X i) := hFfin i
    let _ (i : ℤ) : Module.Free Λ (F.X i) := hFfree i
    have hFproj (i : ℤ) : Module.Projective Λ (F.X i) := inferInstance
    let _ (i : ℤ) : Module.Projective Λ (F.X i) := hFproj i
    let _ := hFc
    let _ : F.IsKProjective := CochainComplex.isKProjective_of_projective F c
    have hFge : F.IsGE a := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (hzero i (by simp only [Set.mem_Icc]; omega)).of_iso
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} Λ) i).app F).symm ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).mapIso eF)
    have hcoker : Module.Projective Λ (cokernel (F.d (a - 1) a) : ModuleCat.{v} Λ) := by
      let S := ShortComplex.mk (F.d (a - 2) (a - 1)) (F.d (a - 1) a) (F.d_comp_d _ _ _)
      apply projective_cokernel_of_tensor_exact D S
      intro N x hx
      let _ : (D.ordinary.obj N).Additive := D.additive N
      let T := (D.ordinary.obj N).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj F
      have : IsIso ((D.comparison N).app F) := isIso_comparison_app_of_isKProjective D N F
      have hz : IsZero (T.homology (a - 1)) :=
        (isZero_homology_tensor_iff D N F K eF (a - 1)).2
          (hab N (a - 1) (by simp only [Set.mem_Icc]; omega))
      have hex := (HomologicalComplex.exactAt_iff_isZero_homology T (a - 1)).mpr hz
      rw [HomologicalComplex.exactAt_iff' T (a - 2) (a - 1) a
        (by simp; omega) (by simp), ShortComplex.moduleCat_exact_iff] at hex
      exact hex x hx
    let E := F.truncGE a
    have hEc : E.IsStrictlyLE c := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      have : Epi ((F.πTruncGE a).f i) := by
        unfold CochainComplex.πTruncGE
        infer_instance
      exact IsZero.of_epi ((F.πTruncGE a).f i) (F.isZero_of_isStrictlyLE c i hi)
    have hE (i : ℤ) : Module.Finite Λ (E.X i) ∧ Module.Projective Λ (E.X i) := by
      by_cases hi : i < a
      · have : Subsingleton (E.X i) := ModuleCat.isZero_iff_subsingleton.mp
          (E.isZero_of_isStrictlyGE a i hi)
        exact ⟨inferInstance, inferInstance⟩
      · rcases (le_of_not_gt hi).eq_or_lt with rfl | hai
        · let e : E.X a ≅ cokernel (F.d (a - 1) a) :=
            F.truncGEXIsoOpcycles a ≪≫
              IsColimit.coconePointUniqueUpToIso
                (F.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
          have : Module.Finite Λ (cokernel (F.d (a - 1) a) : ModuleCat.{v} Λ) :=
            Module.Finite.of_surjective (cokernel.π (F.d (a - 1) a)).hom
              ((ModuleCat.epi_iff_surjective _).mp inferInstance)
          exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
            Module.Projective.of_equiv' e.toLinearEquiv.symm⟩
        · let e : E.X i ≅ F.X i := F.truncGEXIso a i hai
          exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
            Module.Projective.of_equiv' e.toLinearEquiv.symm⟩
    exact ⟨E, a, c, inferInstance, hEc, fun i => (hE i).1, fun i => (hE i).2,
      ⟨eF.symm ≪≫ asIso (DerivedCategory.Q.map (F.πTruncGE a))⟩⟩

/-! ### Independence of the chosen balanced derived tensor product -/

section Independence

/-- The comparison of two balanced tensor products at a fixed pair of modules: the morphism the
universal property of the first produces from the pure tensors of the second. -/
def tensorCompare {Λ : Type u} [Ring Λ] (D D' : BalancedDerivedTensoring.{u, v} Λ)
    (N : ModuleCat.{v} Λᵐᵒᵖ) (M : ModuleCat.{v} Λ) :
    (D.ordinary.obj N).obj M ⟶ (D'.ordinary.obj N).obj M :=
  (D.universal N M ((D'.ordinary.obj N).obj M) (D'.pure N M) (D'.balanced N M)).choose

/-- `tensorCompare D D'` sends a pure tensor of `D` to the corresponding pure tensor of `D'`. -/
private lemma tensorCompare_pure {Λ : Type u} [Ring Λ] (D D' : BalancedDerivedTensoring.{u, v} Λ)
    (N : ModuleCat.{v} Λᵐᵒᵖ) (M : ModuleCat.{v} Λ) (n : N) (m : M) :
    tensorCompare D D' N M (D.pure N M n m) = D'.pure N M n m :=
  (D.universal N M ((D'.ordinary.obj N).obj M) (D'.pure N M)
    (D'.balanced N M)).choose_spec.1 n m

/-- Tensoring with a fixed right `Λ`-module is independent of the chosen balanced tensor
product. -/
def ordinaryIso {Λ : Type u} [Ring Λ] (D D' : BalancedDerivedTensoring.{u, v} Λ)
    (N : ModuleCat.{v} Λᵐᵒᵖ) :
    D.ordinary.obj N ≅ D'.ordinary.obj N :=
  NatIso.ofComponents
    (fun M =>
      { hom := tensorCompare D D' N M
        inv := tensorCompare D' D N M
        hom_inv_id := by
          refine tensor_hom_ext D N M _ _ _ fun n m => ?_
          change tensorCompare D' D N M (tensorCompare D D' N M (D.pure N M n m)) =
            D.pure N M n m
          rw [tensorCompare_pure, tensorCompare_pure]
        inv_hom_id := by
          refine tensor_hom_ext D' N M _ _ _ fun n m => ?_
          change tensorCompare D D' N M (tensorCompare D' D N M (D'.pure N M n m)) =
            D'.pure N M n m
          rw [tensorCompare_pure, tensorCompare_pure] })
    (fun {M M'} f => by
      refine tensor_hom_ext D N M _ _ _ fun n m => ?_
      change tensorCompare D D' N M' (((D.ordinary.obj N).map f) (D.pure N M n m)) =
        ((D'.ordinary.obj N).map f) (tensorCompare D D' N M (D.pure N M n m))
      rw [D.natural_right, tensorCompare_pure, tensorCompare_pure, D'.natural_right])

/-- Derived tensoring with a fixed right `Λ`-module is independent of the chosen balanced
derived tensor product. -/
def derivedIso {Λ : Type u} [Ring Λ] (D D' : BalancedDerivedTensoring.{u, v} Λ)
    (N : ModuleCat.{v} Λᵐᵒᵖ) :
    D.derived.obj N ≅ D'.derived.obj N := by
  letI := D.additive N
  letI := D'.additive N
  letI := D.isLeftDerived N
  letI := D'.isLeftDerived N
  exact Functor.leftDerivedNatIso (D.derived.obj N) (D'.derived.obj N)
    (D.comparison N) (D'.comparison N)
    (HomologicalComplex.quasiIso (ModuleCat.{v} Λ) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ordinaryIso D D' N) (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- **Finite Tor dimension does not depend on the chosen balanced derived tensor product.** The
predicate `HasFiniteTorDimension` reads the same proposition off any two terms of
`BalancedDerivedTensoring Λ`. -/
theorem hasFiniteTorDimension_iff_of_balancedDerivedTensoring {Λ : Type u} [Ring Λ]
    (D D' : BalancedDerivedTensoring.{u, v} Λ) (K : DerivedCategory (ModuleCat.{v} Λ)) :
    HasFiniteTorDimension D K ↔ HasFiniteTorDimension D' K := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, fun N i hi => (h N i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i).mapIso
        ((derivedIso D D' N).symm.app K))⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, fun N i hi => (h N i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ) i).mapIso
        ((derivedIso D D' N).app K))⟩

end Independence

end StacksDraft.Perfect

end
