module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering
public import StacksFrontier.Algebra.Homology.QuasiIsoSingleLeftExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SliceExtDeltaFunctor

/-!
# Local `Ext` of a locally constant abelian sheaf into a divisible sheaf

Let `(C, K)` be a site, `G` an abelian sheaf which is locally constant with finite values, and
`ω` an abelian sheaf on which multiplication by every positive integer is an epimorphism. If
`ω ⟶ J` is an injective resolution, the complex `ℋom(G, J)` is a resolution of `ℋom(G, ω)`:
the local `Ext` sheaves `ℰxtⁱ(G, ω)` vanish for `i > 0`.

The proof is local on the site, which reduces it to a constant sheaf `M̲` with `M` finite;
dévissage on `M` along the long exact cohomology sequences of `ℋom(-, J)`, which is exact
because the terms of `J` are injective (Tag 01DR), reduces it to `M = ℤ`, where
`ℋom(ℤ̲, -)` is the identity, and to `M = ℤ/m`, where the obstruction is the cokernel of
multiplication by `m` on `ω`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)

section Additive

/-- **The contravariant internal Hom `ℋom(-, J)` is additive.** -/
instance internalHomFunctor_additive (J : Sheaf K AddCommGrpCat.{max u v}) :
    (internalHomFunctor K J).Additive where
  map_add {F F'} f g := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun a => NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext
        (AddMonoidHom.ext fun y => ?_)))))
    exact map_add (a.app W).hom _ _

/-- The covariant internal Hom `ℋom(G, -)` is additive. -/
instance internalHomRightFunctor_additive (G : Sheaf K AddCommGrpCat.{max u v}) :
    (internalHomRightFunctor K G).Additive where
  map_add {F F'} f g := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun a => NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext
        (AddMonoidHom.ext fun y => ?_)))))
    rfl

end Additive

section Slice

variable (X : C) (F G : Sheaf K AddCommGrpCat.{max u v})

/-- A section of `ℋom(F, G)` over `R.left`, read as a section of `ℋom(F|_X, G|_X)` over `R`, by
restriction along `CategoryTheory.Over.iteratedSliceForward`. -/
def internalHomSliceSection (R : Over X)
    (α : (Over.forget R.left).op ⋙ F.obj ⟶ (Over.forget R.left).op ⋙ G.obj) :
    (Over.forget R).op ⋙ ((K.overPullback AddCommGrpCat.{max u v} X).obj F).obj ⟶
      (Over.forget R).op ⋙ ((K.overPullback AddCommGrpCat.{max u v} X).obj G).obj :=
  Functor.whiskerLeft (Over.iteratedSliceForward R).op α

/-- Restriction along `CategoryTheory.Over.iteratedSliceForward` is a bijection on sections of
the internal Hom. -/
lemma bijective_internalHomSliceSection (R : Over X) :
    Function.Bijective (internalHomSliceSection K X F G R) := by
  let e := (Over.iteratedSliceEquiv R).op.congrLeft (E := AddCommGrpCat.{max u v})
  exact e.fullyFaithfulInverse.map_bijective _ _

/-- Reading a section of the internal Hom on the slice site, as a morphism of presheaves on
`C/X`. -/
def internalHomOverPullbackNatTrans :
    ((K.overPullback AddCommGrpCat.{max u v} X).obj (internalHomSheaf K F G)).obj ⟶
      (internalHomSheaf (K.over X) ((K.overPullback AddCommGrpCat.{max u v} X).obj F)
        ((K.overPullback AddCommGrpCat.{max u v} X).obj G)).obj where
  app R := AddCommGrpCat.ofHom
    { toFun := fun α => internalHomSliceSection K X F G R.unop α
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- Each component of `internalHomOverPullbackNatTrans` is an isomorphism. -/
instance isIso_internalHomOverPullbackNatTrans_app (R : (Over X)ᵒᵖ) :
    IsIso ((internalHomOverPullbackNatTrans K X F G).app R) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_internalHomSliceSection K X F G R.unop

/-- The comparison `internalHomOverPullbackNatTrans` is an isomorphism of presheaves. -/
instance isIso_internalHomOverPullbackNatTrans :
    IsIso (internalHomOverPullbackNatTrans K X F G) :=
  NatIso.isIso_of_isIso_app _

/-- **The internal Hom commutes with restriction to a slice site**:
`ℋom(F, G)|_X ≅ ℋom(F|_X, G|_X)`. -/
def overPullbackInternalHomIso :
    (K.overPullback AddCommGrpCat.{max u v} X).obj (internalHomSheaf K F G) ≅
      internalHomSheaf (K.over X) ((K.overPullback AddCommGrpCat.{max u v} X).obj F)
        ((K.overPullback AddCommGrpCat.{max u v} X).obj G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (asIso (internalHomOverPullbackNatTrans K X F G))

/-- The underlying morphism of presheaves of `overPullbackInternalHomIso`. -/
lemma overPullbackInternalHomIso_hom_hom :
    (overPullbackInternalHomIso K X F G).hom.hom = internalHomOverPullbackNatTrans K X F G :=
  rfl

/-- The comparison `ℋom(F, G)|_X ≅ ℋom(F|_X, G|_X)` is natural in `G`. -/
lemma overPullbackInternalHomIso_hom_naturality_right {G G' : Sheaf K AddCommGrpCat.{max u v}}
    (g : G ⟶ G') :
    (K.overPullback AddCommGrpCat.{max u v} X).map ((internalHomRightFunctor K F).map g) ≫
        (overPullbackInternalHomIso K X F G').hom =
      (overPullbackInternalHomIso K X F G).hom ≫
        (internalHomRightFunctor (K.over X) ((K.overPullback AddCommGrpCat.{max u v} X).obj F)).map
          ((K.overPullback AddCommGrpCat.{max u v} X).map g) :=
  rfl

/-- The comparison `ℋom(F, G)|_X ≅ ℋom(F|_X, G|_X)` is natural in `F`. -/
lemma overPullbackInternalHomIso_hom_naturality_left {F F' : Sheaf K AddCommGrpCat.{max u v}}
    (f : F' ⟶ F) :
    (K.overPullback AddCommGrpCat.{max u v} X).map ((internalHomFunctor K G).map f.op) ≫
        (overPullbackInternalHomIso K X F' G).hom =
      (overPullbackInternalHomIso K X F G).hom ≫
        (internalHomFunctor (K.over X) ((K.overPullback AddCommGrpCat.{max u v} X).obj G)).map
          ((K.overPullback AddCommGrpCat.{max u v} X).map f).op :=
  rfl

end Slice

section Unit

/-- The constant abelian sheaf `ℤ̲`. -/
abbrev unitSheaf : Sheaf K AddCommGrpCat.{max u v} :=
  (constantSheaf K AddCommGrpCat.{max u v}).obj (AddCommGrpCat.of (ULift.{max u v} ℤ))

/-- The section `1` of `ℤ̲` over `U`. -/
abbrev unitSection (U : Cᵒᵖ) : (unitSheaf K).obj.obj U :=
  ((toSheafify K ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max u v} ℤ)))).app U).hom
    (ULift.up 1)

/-- The sections `1` of `ℤ̲` are compatible with restriction. -/
lemma unitSection_map {U U' : Cᵒᵖ} (f : U ⟶ U') :
    unitSection K U' = ((unitSheaf K).obj.map f).hom (unitSection K U) :=
  ConcreteCategory.congr_hom
    ((toSheafify K ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max u v} ℤ)))).naturality f)
    (ULift.up 1)

/-- **Evaluation at the section `1`**, `ℋom(ℤ̲, F) ⟶ F`: a local morphism `ℤ̲|_U ⟶ F|_U` is sent
to its value at `1` over `U`. -/
def evalUnit (F : Sheaf K AddCommGrpCat.{max u v}) :
    (internalHomSheaf K (unitSheaf K) F).obj ⟶ F.obj where
  app U := AddCommGrpCat.ofHom
    { toFun := fun α => (α.app (op (Over.mk (𝟙 U.unop)))).hom (unitSection K U)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality U U' f := by
    ext α
    have hα := ConcreteCategory.congr_hom (α.naturality
      (Over.homMk (U := Over.mk (𝟙 U'.unop ≫ f.unop)) (V := Over.mk (𝟙 U.unop)) f.unop
        (by simp)).op) (unitSection K U)
    change (α.app (op (Over.mk (𝟙 U'.unop ≫ f.unop)))).hom (unitSection K U') =
      (F.obj.map f).hom ((α.app (op (Over.mk (𝟙 U.unop)))).hom (unitSection K U))
    rw [unitSection_map K f]
    exact hα

/-- `evalUnit` sends a local morphism `ℤ̲|_U ⟶ F|_U` to its value at `1` over `U`. -/
lemma evalUnit_app_apply (F : Sheaf K AddCommGrpCat.{max u v}) (U : Cᵒᵖ)
    (α : (internalHomSheaf K (unitSheaf K) F).obj.obj U) :
    ((evalUnit K F).app U).hom α = (α.app (op (Over.mk (𝟙 U.unop)))).hom (unitSection K U) :=
  rfl

/-- Evaluation at `1` is a bijection on sections over each object. -/
lemma bijective_evalUnit_app (F : Sheaf K AddCommGrpCat.{max u v}) (U : Cᵒᵖ) :
    Function.Bijective ((evalUnit K F).app U).hom := by
  let Z := AddCommGrpCat.of (ULift.{max u v} ℤ)
  let S := (K.overPullback AddCommGrpCat.{max u v} U.unop).obj F
  let ι := (Stacks.ConstantSheaf.overPullbackConstantSheafIso K AddCommGrpCat.{max u v}
    U.unop).app Z
  let e : ((Over.forget U.unop).op ⋙ (unitSheaf K).obj ⟶ (Over.forget U.unop).op ⋙ F.obj) ≃
      F.obj.obj U :=
    ((fullyFaithfulSheafToPresheaf (K.over U.unop) AddCommGrpCat.{max u v}).homEquiv.symm.trans
      (ι.symm.homCongr (Iso.refl S))).trans
      (((constantSheafAdj (K.over U.unop) AddCommGrpCat.{max u v} Over.mkIdTerminal).homEquiv
        Z S).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv)
  have hfun : ∀ α, ((evalUnit K F).app U).hom α = e α := by
    intro α
    let α₀ : (Over.forget U.unop).op ⋙ (unitSheaf K).obj ⟶ (Over.forget U.unop).op ⋙ F.obj := α
    let α' : (K.overPullback AddCommGrpCat.{max u v} U.unop).obj (unitSheaf K) ⟶ S :=
      ObjectProperty.homMk α₀
    have hadj := Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply (K.over U.unop)
      AddCommGrpCat.{max u v} (Over.mkIdTerminal (X := U.unop)) Z S (ι.hom ≫ α' ≫ 𝟙 S)
    have hc := ConcreteCategory.congr_hom
      (Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso K AddCommGrpCat.{max u v}
        U.unop Z) (ULift.up 1)
    have h1 : e α = (α₀.app (op (Over.mk (𝟙 U.unop)))).hom
        ((ι.hom.hom.app (op (Over.mk (𝟙 U.unop)))).hom
          (((toSheafify (K.over U.unop) ((Functor.const (Over U.unop)ᵒᵖ).obj Z)).app
            (op (Over.mk (𝟙 U.unop)))).hom (ULift.up 1))) := by
      show ((constantSheafAdj (K.over U.unop) AddCommGrpCat.{max u v} Over.mkIdTerminal).homEquiv
        Z S (ι.hom ≫ α' ≫ 𝟙 S)).hom (ULift.up 1) = _
      rw [hadj]
      rfl
    rw [h1]
    exact (congrArg (fun z => (α₀.app (op (Over.mk (𝟙 U.unop)))).hom z) hc).symm
  exact (funext hfun ▸ e.bijective :
    Function.Bijective ((AddCommGrpCat.Hom.hom ((evalUnit K F).app U) : _ → _)))

/-- Evaluation at `1`, `ℋom(ℤ̲, F) ⟶ F`, is an isomorphism. -/
instance isIso_evalUnit (F : Sheaf K AddCommGrpCat.{max u v}) : IsIso (evalUnit K F) := by
  have : ∀ U, IsIso ((evalUnit K F).app U) := fun U => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_evalUnit_app K F U
  exact NatIso.isIso_of_isIso_app _

/-- **`ℋom(ℤ̲, -)` is the identity functor** on abelian sheaves, by evaluation at `1`. -/
def internalHomUnitIso : internalHomRightFunctor K (unitSheaf K) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (@asIso _ _ _ _ (evalUnit K F) (isIso_evalUnit K F)))
    (fun _ => rfl)

/-- The components of `internalHomUnitIso` are given by evaluation at `1`. -/
lemma internalHomUnitIso_hom_app_hom (F : Sheaf K AddCommGrpCat.{max u v}) :
    ((internalHomUnitIso K).hom.app F).hom = evalUnit K F := rfl

end Unit

section Devissage

/-- An additive functor takes `m • 𝟙 A` to `m • 𝟙 (F.obj A)`. -/
private theorem map_zsmul_id {D E : Type*} [Category D] [Category E] [Preadditive D]
    [Preadditive E] (F : D ⥤ E) [F.Additive] (m : ℤ) (A : D) :
    F.map (m • 𝟙 A) = m • 𝟙 (F.obj A) := by
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]

variable (J : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ)

/-- **The complex `ℋom(A, J)`**, the internal Hom out of `A` applied termwise to `J`. -/
abbrev homComplex (A : Sheaf K AddCommGrpCat.{max u v}) :
    CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ :=
  ((internalHomRightFunctor K A).mapHomologicalComplex (ComplexShape.up ℤ)).obj J

/-- Precomposition with `f : A ⟶ B`, as a map of complexes `ℋom(B, J) ⟶ ℋom(A, J)`. -/
def homComplexMap {A B : Sheaf K AddCommGrpCat.{max u v}} (f : A ⟶ B) :
    homComplex K J B ⟶ homComplex K J A where
  f n := (internalHomFunctor K (J.X n)).map f.op
  comm' _ _ _ := rfl

/-- The degree `n` component of `homComplexMap` is precomposition with `f` in `ℋom(-, J^n)`. -/
lemma homComplexMap_f {A B : Sheaf K AddCommGrpCat.{max u v}} (f : A ⟶ B) (n : ℤ) :
    (homComplexMap K J f).f n = (internalHomFunctor K (J.X n)).map f.op := rfl

/-- Precomposition with `m • 𝟙 A` is multiplication by `m` on `ℋom(A, J)`. -/
lemma homComplexMap_zsmul_id (A : Sheaf K AddCommGrpCat.{max u v}) (m : ℤ) :
    homComplexMap K J (m • 𝟙 A) = m • 𝟙 (homComplex K J A) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h : (internalHomFunctor K (J.X n)).map (m • 𝟙 A).op =
      m • 𝟙 ((internalHomFunctor K (J.X n)).obj (op A)) := by
    rw [op_zsmul, op_id, map_zsmul_id]
  exact h

/-- The composite `ℋom(S.X₃, J) ⟶ ℋom(S.X₂, J) ⟶ ℋom(S.X₁, J)` is zero. -/
lemma homComplexMap_comp_eq_zero (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v})) :
    homComplexMap K J S.g ≫ homComplexMap K J S.f = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h : (internalHomFunctor K (J.X n)).map S.g.op ≫ (internalHomFunctor K (J.X n)).map S.f.op =
      0 := by
    rw [← Functor.map_comp, ← op_comp, S.zero, op_zero, Functor.map_zero]
  exact h

/-- The short complex of complexes `ℋom(S.X₃, J) ⟶ ℋom(S.X₂, J) ⟶ ℋom(S.X₁, J)`. -/
abbrev homComplexShortComplex (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v})) :
    ShortComplex (CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ) :=
  ShortComplex.mk (homComplexMap K J S.g) (homComplexMap K J S.f) (homComplexMap_comp_eq_zero K J S)

variable [∀ n, Injective (J.X n)]

/-- **`ℋom(-, J)` takes a short exact sequence to a short exact sequence of complexes**, the
terms of `J` being injective (Tag 01DR). -/
lemma shortExact_homComplexShortComplex (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v}))
    (hS : S.ShortExact) : (homComplexShortComplex K J S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    internalHom_exact_of_injective K (J.X n) S hS

/-- The local `Ext` sheaves `ℋⁿ(ℋom(A, J))` vanish in positive degrees. -/
def ExtVanishes (A : Sheaf K AddCommGrpCat.{max u v}) : Prop :=
  ∀ n : ℤ, 0 < n → IsZero ((homComplex K J A).homology n)

omit [∀ n, Injective (J.X n)] in
/-- The local `Ext` sheaves out of a zero sheaf vanish. -/
lemma extVanishes_of_isZero {A : Sheaf K AddCommGrpCat.{max u v}} (hA : IsZero A) :
    ExtVanishes K J A := by
  intro n _
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  exact Functor.map_isZero (internalHomFunctor K (J.X n)) hA.op

/-- In a short exact sequence, vanishing of the local `Ext` sheaves out of the outer terms
implies vanishing out of the middle term. -/
lemma extVanishes_mid (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (h₁ : ExtVanishes K J S.X₁) (h₃ : ExtVanishes K J S.X₃) : ExtVanishes K J S.X₂ := fun n hn =>
  ((shortExact_homComplexShortComplex K J S hS).homology_exact₂ n).isZero_X₂
    ((h₃ n hn).eq_of_src _ _) ((h₁ n hn).eq_of_tgt _ _)

/-- In a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0`, vanishing of the local `Ext`
sheaves out of `S.X₁` and `S.X₂`, together with surjectivity of `ℋ⁰(ℋom(S.X₂, J)) ⟶
ℋ⁰(ℋom(S.X₁, J))`, implies vanishing out of `S.X₃`. -/
lemma extVanishes_quot (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (h₁ : ExtVanishes K J S.X₁) (h₂ : ExtVanishes K J S.X₂)
    (h0 : Epi (HomologicalComplex.homologyMap (homComplexMap K J S.f) 0)) :
    ExtVanishes K J S.X₃ := by
  intro n hn
  have hT := shortExact_homComplexShortComplex K J S hS
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 := hT.homology_exact₁ m (m + 1) rfl
  by_cases hm : 0 < m
  · exact e1.isZero_X₂ ((h₁ m hm).eq_of_src _ _) ((h₂ (m + 1) hn).eq_of_tgt _ _)
  · obtain rfl : m = 0 := by omega
    have hδ : Epi (hT.δ 0 (0 + 1) rfl) := e1.epi_f ((h₂ (0 + 1) hn).eq_of_tgt _ _)
    have hcomp := (ShortComplex.mk _ _ (hT.comp_δ 0 (0 + 1) rfl)).zero
    have h0' : Epi (HomologicalComplex.homologyMap (homComplexShortComplex K J S).g 0) := h0
    have hz : hT.δ 0 (0 + 1) rfl = 0 := (cancel_epi _).1 (hcomp.trans (comp_zero).symm)
    exact IsZero.of_epi_eq_zero _ hz

end Devissage

section Groups

universe w

/-- The short exact sequence `0 → ℤ →(m) ℤ → ⟨x⟩ → 0` of a group element `x` of order `m`. -/
def cyclicShortComplex {M : AddCommGrpCat.{w}} (x : M) : ShortComplex AddCommGrpCat.{w} :=
  ShortComplex.mk ((addOrderOf x : ℤ) • 𝟙 (AddCommGrpCat.of (ULift.{w} ℤ)))
    (AddCommGrpCat.ofHom ((zmultiplesHom (AddSubgroup.zmultiples x)
      ⟨x, AddSubgroup.mem_zmultiples x⟩).comp AddEquiv.ulift.toAddMonoidHom))
    (by
      ext ⟨n⟩
      change ((addOrderOf x : ℤ) * n) • x = 0
      have h0 : (addOrderOf x : ℤ) • x = 0 := by
        rw [natCast_zsmul]
        exact addOrderOf_nsmul_eq_zero x
      rw [mul_comm, mul_zsmul, h0, zsmul_zero])

/-- The first map of `cyclicShortComplex x` is multiplication by the order of `x`. -/
lemma cyclicShortComplex_f {M : AddCommGrpCat.{w}} (x : M) :
    (cyclicShortComplex x).f = (addOrderOf x : ℤ) • 𝟙 (AddCommGrpCat.of (ULift.{w} ℤ)) := rfl

/-- For `x` in a finite group, `0 → ℤ →(m) ℤ → ⟨x⟩ → 0` is short exact. -/
lemma cyclicShortComplex_shortExact {M : AddCommGrpCat.{w}} [Finite M] (x : M) :
    (cyclicShortComplex x).ShortExact := by
  have hm : (addOrderOf x : ℤ) ≠ 0 := by exact_mod_cast (addOrderOf_pos x).ne'
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    rintro ⟨n⟩ hn
    have hn' : n • x = 0 := congrArg Subtype.val hn
    obtain ⟨k, rfl⟩ := (addOrderOf_dvd_iff_zsmul_eq_zero).2 hn'
    exact ⟨ULift.up k, rfl⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    rintro ⟨a⟩ ⟨b⟩ h
    have h' : (addOrderOf x : ℤ) * a = (addOrderOf x : ℤ) * b := congrArg ULift.down h
    exact congrArg ULift.up (mul_left_cancel₀ hm h')
  · rw [AddCommGrpCat.epi_iff_surjective]
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
    exact ⟨ULift.up k, rfl⟩

/-- The short exact sequence `0 → ⟨x⟩ → M → M/⟨x⟩ → 0`. -/
def quotientShortComplex {M : AddCommGrpCat.{w}} (x : M) :
    ShortComplex AddCommGrpCat.{w} :=
  haveI : (AddSubgroup.zmultiples x).Normal := AddSubgroup.normal_of_isAddCommutative _
  ShortComplex.mk
    (AddCommGrpCat.ofHom (AddSubgroup.zmultiples x).subtype :
      AddCommGrpCat.of (AddSubgroup.zmultiples x) ⟶ M)
    (AddCommGrpCat.ofHom (QuotientAddGroup.mk' (AddSubgroup.zmultiples x)) :
      M ⟶ AddCommGrpCat.of (M ⧸ AddSubgroup.zmultiples x))
    (by
      ext ⟨y, hy⟩
      exact (QuotientAddGroup.eq_zero_iff y).2 hy)

/-- The sequence `0 → ⟨x⟩ → M → M/⟨x⟩ → 0` is short exact. -/
lemma quotientShortComplex_shortExact {M : AddCommGrpCat.{w}} (x : M) :
    (quotientShortComplex x).ShortExact := by
  have hN : (AddSubgroup.zmultiples x).Normal := AddSubgroup.normal_of_isAddCommutative _
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro y hy
    exact ⟨⟨y, (@QuotientAddGroup.eq_zero_iff _ _ (AddSubgroup.zmultiples x) hN y).1 hy⟩, rfl⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [AddCommGrpCat.epi_iff_surjective]
    exact @QuotientAddGroup.mk'_surjective _ _ (AddSubgroup.zmultiples x) hN

end Groups

section Constant

variable (J : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ) [∀ n, Injective (J.X n)]
  {ω : Sheaf K AddCommGrpCat.{max u v}}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]

/-- `ℋom(ℤ̲, J) ≅ J`. -/
def homComplexUnitIso : homComplex K J (unitSheaf K) ≅ J :=
  (NatIso.mapHomologicalComplex (internalHomUnitIso K) (ComplexShape.up ℤ)).app J ≪≫
    (Functor.mapHomologicalComplexIdIso _ _).app J

/-- `H⁰(J) ≅ ω` for a resolution `ω ⟶ J`. -/
def homologyZeroIsoOfQuasiIsoSingle : J.homology 0 ≅ ω :=
  (asIso (HomologicalComplex.homologyMap ι 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ 0 ω

include ι in
omit [∀ n, Injective (J.X n)] in
/-- The local `Ext` sheaves `ℋⁿ(ℋom(ℤ̲, J))` vanish for `n > 0`. -/
lemma extVanishes_unitSheaf : ExtVanishes K J (unitSheaf K) := fun n hn =>
  (Stacks.LeftExactHomology.isZero_homology_of_quasiIso_single ι n (ne_of_gt hn)).of_iso
    (HomologicalComplex.homologyMapIso (homComplexUnitIso K J) n)

omit [∀ n, Injective (J.X n)] [QuasiIso ι] in
/-- Multiplication by `m` is an epimorphism on `X` if it is one on an isomorphic `Y`. -/
lemma epi_zsmul_id_of_iso {X Y : Sheaf K AddCommGrpCat.{max u v}} (e : X ≅ Y) (m : ℤ)
    (h : Epi (m • 𝟙 Y)) : Epi (m • 𝟙 X) := by
  have : m • 𝟙 X = e.hom ≫ (m • 𝟙 Y) ≫ e.inv := by
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Iso.hom_inv_id]
  rw [this]
  infer_instance

include ι in
omit [∀ n, Injective (J.X n)] in
/-- If multiplication by `m` is an epimorphism on `ω`, then precomposition with `m • 𝟙 ℤ̲`
induces an epimorphism on `ℋ⁰(ℋom(ℤ̲, J))`. -/
lemma epi_homologyMap_homComplexMap_zsmul (m : ℤ) (hω : Epi (m • 𝟙 ω)) :
    Epi (HomologicalComplex.homologyMap (homComplexMap K J (m • 𝟙 (unitSheaf K))) 0) := by
  rw [homComplexMap_zsmul_id]
  have h : HomologicalComplex.homologyMap (m • 𝟙 (homComplex K J (unitSheaf K))) 0 =
      m • 𝟙 _ := by
    rw [← HomologicalComplex.homologyFunctor_map, map_zsmul_id]
    rfl
  rw [h]
  exact epi_zsmul_id_of_iso K (HomologicalComplex.homologyMapIso (homComplexUnitIso K J) 0 ≪≫
    homologyZeroIsoOfQuasiIsoSingle K J ι) m hω

omit [∀ n, Injective (J.X n)] in
/-- The constant sheaf functor takes short exact sequences of abelian groups to short exact
sequences of abelian sheaves. -/
lemma shortExact_map_constantSheaf {S : ShortComplex AddCommGrpCat.{max u v}}
    (hS : S.ShortExact) : (S.map (constantSheaf K AddCommGrpCat.{max u v})).ShortExact := by
  have : PreservesFiniteLimits (constantSheaf K AddCommGrpCat.{max u v}) := by
    unfold constantSheaf; infer_instance
  have : PreservesFiniteColimits (constantSheaf K AddCommGrpCat.{max u v}) := by
    unfold constantSheaf; infer_instance
  exact hS.map_of_exact _

include ι in
/-- **Local `Ext` vanishing for a constant sheaf on a finite group, into a divisible sheaf.** -/
theorem extVanishes_constantSheaf_of_finite
    (hω : ∀ m : ℕ, 0 < m → Epi ((m : ℤ) • 𝟙 ω))
    (M : AddCommGrpCat.{max u v}) [Finite M] :
    ExtVanishes K J ((constantSheaf K AddCommGrpCat.{max u v}).obj M) := by
  induction h : Nat.card M using Nat.strong_induction_on generalizing M with
  | _ N ih =>
    by_cases hM : ∀ y : M, y = 0
    · have : Subsingleton M := ⟨fun a b => (hM a).trans (hM b).symm⟩
      exact extVanishes_of_isZero K J
        (Functor.map_isZero _ (AddCommGrpCat.isZero_of_subsingleton M))
    · simp only [not_forall] at hM
      obtain ⟨x, hx⟩ := hM
      -- the cyclic subgroup
      have hcyc : ExtVanishes K J
          ((constantSheaf K AddCommGrpCat.{max u v}).obj
            (AddCommGrpCat.of (AddSubgroup.zmultiples x))) := by
        have hS := shortExact_map_constantSheaf K (cyclicShortComplex_shortExact x)
        refine extVanishes_quot K J _ hS (extVanishes_unitSheaf K J ι)
          (extVanishes_unitSheaf K J ι) ?_
        have hf : ((cyclicShortComplex x).map (constantSheaf K AddCommGrpCat.{max u v})).f =
            ((addOrderOf x : ℤ)) • 𝟙 (unitSheaf K) := by
          have : (constantSheaf K AddCommGrpCat.{max u v}).Additive :=
            Functor.additive_of_preserves_binary_products _
          exact map_zsmul_id _ _ _
        rw [hf]
        exact epi_homologyMap_homComplexMap_zsmul K J ι _ (hω _ (addOrderOf_pos x))
      -- the quotient, of smaller order
      have hlt : Nat.card (M ⧸ AddSubgroup.zmultiples x) < N := by
        rw [← h, (AddSubgroup.zmultiples x).card_eq_card_quotient_mul_card_addSubgroup]
        have h1 : 1 < Nat.card (AddSubgroup.zmultiples x) := by
          rw [Nat.card_zmultiples]
          exact lt_of_le_of_ne (addOrderOf_pos x)
            (fun h => hx (AddMonoid.addOrderOf_eq_one_iff.1 h.symm))
        have h2 : 0 < Nat.card (M ⧸ AddSubgroup.zmultiples x) := Nat.card_pos
        nlinarith
      have hquot := ih _ hlt (AddCommGrpCat.of (M ⧸ AddSubgroup.zmultiples x)) rfl
      exact extVanishes_mid K J _
        (shortExact_map_constantSheaf K (quotientShortComplex_shortExact x)) hcyc hquot

end Constant

section Local

/-- `homComplexMap` is contravariantly functorial: it takes `f ≫ g` to the reversed composite. -/
lemma homComplexMap_comp {A B D : Sheaf K AddCommGrpCat.{max u v}} (J) (f : A ⟶ B) (g : B ⟶ D) :
    homComplexMap K J (f ≫ g) = homComplexMap K J g ≫ homComplexMap K J f := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h : (internalHomFunctor K (J.X n)).map (f ≫ g).op =
      (internalHomFunctor K (J.X n)).map g.op ≫ (internalHomFunctor K (J.X n)).map f.op := by
    rw [op_comp, Functor.map_comp]
  exact h

/-- `homComplexMap` takes the identity to the identity. -/
lemma homComplexMap_id (A : Sheaf K AddCommGrpCat.{max u v}) (J) :
    homComplexMap K J (𝟙 A) = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h : (internalHomFunctor K (J.X n)).map (𝟙 A).op = 𝟙 _ := by
    rw [op_id, CategoryTheory.Functor.map_id]
  exact h

/-- An isomorphism `A ≅ B` induces `ℋom(B, J) ≅ ℋom(A, J)`. -/
def homComplexIso {A B : Sheaf K AddCommGrpCat.{max u v}} (J) (e : A ≅ B) :
    homComplex K J B ≅ homComplex K J A where
  hom := homComplexMap K J e.hom
  inv := homComplexMap K J e.inv
  hom_inv_id := by rw [← homComplexMap_comp, e.inv_hom_id, homComplexMap_id]
  inv_hom_id := by rw [← homComplexMap_comp, e.hom_inv_id, homComplexMap_id]

variable (J : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ) [∀ n, Injective (J.X n)]
  {ω : Sheaf K AddCommGrpCat.{max u v}}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]

/-- `ℋom(G, J)|_X ≅ ℋom(G|_X, J|_X)`, as complexes. -/
def overPullbackHomComplexIso (X : C) (G : Sheaf K AddCommGrpCat.{max u v}) :
    ((K.overPullback AddCommGrpCat.{max u v} X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homComplex K J G) ≅
      homComplex (K.over X) (((K.overPullback AddCommGrpCat.{max u v} X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ((K.overPullback AddCommGrpCat.{max u v} X).obj G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => overPullbackInternalHomIso K X G (J.X n))
    (fun i j _ => overPullbackInternalHomIso_hom_naturality_right K X G (J.d i j))

include ι in
/-- **Local `Ext` vanishing**: for an abelian sheaf `G` which is locally constant with finite
values and a divisible abelian sheaf `ω` with injective resolution `ω ⟶ J`, the cohomology
sheaves `ℋⁿ(ℋom(G, J))` vanish for `n > 0`. -/
theorem extVanishes_of_isFiniteLocallyConstant (G : Sheaf K AddCommGrpCat.{max u v})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant K G]
    (hω : ∀ m : ℕ, 0 < m → Epi ((m : ℤ) • 𝟙 ω)) : ExtVanishes K J G := by
  intro n hn
  refine Sheaf.isZero_of_forall_isZero_sections _ fun U => ?_
  obtain ⟨I, V, f, hf, h⟩ :=
    (inferInstance : Stacks.ConstantSheaf.IsFiniteLocallyConstant K G).exists_finite_cover U
  refine Sheaf.isZero_sections_of_isZero_sections_of_covering _ (Presieve.ofArrows V f) hf ?_
  rintro _ _ ⟨i⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : ∀ n, Injective ((((K.overPullback AddCommGrpCat.{max u v} (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J).X n) :=
    fun n => overPullback_preservesInjective K (V i) (J.X n)
  have hω' : ∀ m : ℕ, 0 < m →
      Epi ((m : ℤ) • 𝟙 ((K.overPullback AddCommGrpCat.{max u v} (V i)).obj ω)) := fun m hm => by
    have := hω m hm
    have h1 : (K.overPullback AddCommGrpCat.{max u v} (V i)).map ((m : ℤ) • 𝟙 ω) =
        (m : ℤ) • 𝟙 ((K.overPullback AddCommGrpCat.{max u v} (V i)).obj ω) := by
      rw [map_zsmul_id]
    rw [← h1]
    infer_instance
  have : Finite (E : Type (max u v)) := hE
  have key := extVanishes_constantSheaf_of_finite (K.over (V i))
    (((K.overPullback AddCommGrpCat.{max u v} (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J)
    ((HomologicalComplex.singleMapHomologicalComplex (K.overPullback AddCommGrpCat.{max u v} (V i))
      (ComplexShape.up ℤ) 0).inv.app ω ≫
      ((K.overPullback AddCommGrpCat.{max u v} (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ι)
    hω' E n hn
  have hP : IsZero ((K.overPullback AddCommGrpCat.{max u v} (V i)).obj
      ((homComplex K J G).homology n)) :=
    key.of_iso ((((homComplex K J G).sc n).mapHomologyIso
        (K.overPullback AddCommGrpCat.{max u v} (V i))).symm ≪≫
      HomologicalComplex.homologyMapIso (overPullbackHomComplexIso K J (V i) G) n ≪≫
      HomologicalComplex.homologyMapIso (homComplexIso (K.over (V i)) _ e) n)
  exact Functor.map_isZero ((sheafSections (K.over (V i)) AddCommGrpCat.{max u v}).obj
    (op (Over.mk (𝟙 (V i))))) hP

include ι in
/-- **`ℋom(G, -)` takes an injective resolution of a divisible sheaf to a resolution**: for
`G` locally constant with finite values, `ω` divisible and `ω ⟶ J` an injective resolution
concentrated in nonnegative degrees, the induced map
`ℋom(G, ω)[0] ⟶ ℋom(G, J)` is a quasi-isomorphism. -/
theorem quasiIso_internalHomRightFunctor_map (G : Sheaf K AddCommGrpCat.{max u v})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant K G] [J.IsStrictlyGE 0]
    (hω : ∀ m : ℕ, 0 < m → Epi ((m : ℤ) • 𝟙 ω)) :
    QuasiIso (((internalHomRightFunctor K G).mapHomologicalComplex (ComplexShape.up ℤ)).map ι) := by
  let H := internalHomRightFunctor K G
  have : PreservesLimits H := (sheafTensorAdj K G).rightAdjoint_preservesLimits
  have hiso : ∀ {X Y : Sheaf K AddCommGrpCat.{max u v}} (φ : X ⟶ Y), IsZero X → IsZero Y →
      IsIso φ := fun φ hX hY => ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩
  have hzero : ∀ n : ℤ, n ≠ 0 →
      IsZero (((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω)).homology n) := fun n hn =>
    ShortComplex.isZero_homology_of_isZero_X₂ _
      (Functor.map_isZero H (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn))
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rcases lt_trichotomy n 0 with hlt | rfl | hgt
  · refine hiso _ (hzero n hlt.ne) ?_
    exact ShortComplex.isZero_homology_of_isZero_X₂
      (((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).sc n)
      (Functor.map_isZero H (J.isZero_of_isStrictlyGE 0 n hlt))
  · rw [← quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff]
    have h₁ : H.PreservesLeftHomologyOf
        (HomologicalComplex.sc ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω) 0) :=
      Stacks.LeftExactHomology.preservesLeftHomologyOf_of_isZero_X₁ H _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 ω _ (by simp))
    have h₂ : H.PreservesLeftHomologyOf (J.sc 0) :=
      Stacks.LeftExactHomology.preservesLeftHomologyOf_of_isZero_X₁ H _
        (J.isZero_of_isStrictlyGE 0 _ (by simp))
    have : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor _ _ 0).map ι) :=
      (quasiIsoAt_iff ι 0).1 inferInstance
    exact ShortComplex.quasiIso_map_of_preservesLeftHomology H
      ((HomologicalComplex.shortComplexFunctor _ _ 0).map ι)
  · exact hiso _ (hzero n hgt.ne')
      (extVanishes_of_isFiniteLocallyConstant K J ι G hω n hgt)

end Local

end Stacks.AbelianInternalHom
