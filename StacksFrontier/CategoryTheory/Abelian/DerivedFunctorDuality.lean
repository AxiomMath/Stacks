module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Transfer
public import StacksFrontier.CategoryTheory.Abelian.LeftDerivedTransport

/-!
# Derived functors across an anti-equivalence

Let `C` be an abelian category with enough injectives and `e : Cᵒᵖ ≌ C'` an anti-equivalence
with an abelian category `C'`. This file turns `e` into an identification of derived functors.

* The opposite of an injective resolution of `X` is a projective resolution of `op X` in `Cᵒᵖ`,
  and dually (`CategoryTheory.InjectiveResolution.op`, `CategoryTheory.ProjectiveResolution.op`).
  Applying an additive `F : C ⥤ A` to a resolution and taking homology commutes with passing to
  opposites, so the left derived functors of `F.op : Cᵒᵖ ⥤ Aᵒᵖ` are the opposites of the right
  derived functors of `F`, and dually
  (`CategoryTheory.Functor.leftDerivedOpIso`, `CategoryTheory.Functor.rightDerivedOpIso`).
* `C'` is abelian as soon as it is preadditive, and has enough projectives
  (`CategoryTheory.Equivalence.abelianOfAntiEquivalence`,
  `CategoryTheory.Equivalence.enoughProjectives_of_antiEquivalence`).
* If `F : C ⥤ A` and `F' : C' ⥤ A'` are additive and `δ : Aᵒᵖ ⥤ A'` is additive and preserves
  homology (for instance it is exact), then a natural isomorphism `e.functor ⋙ F' ≅ F.op ⋙ δ`
  induces `e.functor ⋙ F'.leftDerived n ≅ (F.rightDerived n).op ⋙ δ` for every `n`
  (`CategoryTheory.Equivalence.leftDerivedCompIsoOfAntiEquivalence`): an injective resolution of
  `M` goes under `e` to a projective resolution of `e (op M)`, and `δ` commutes with homology.

This is the formal part of the "trivial duality" `Hⁱ(G, M)^∧ = Hᵢ(G, M^∧)` of Section 03VI of the
Stacks project, where `C` is the category of discrete `G`-modules, `C'` that of compact
`G`-modules, `e` is Pontryagin duality, `F` is the invariants and `F'` the coinvariants.

## Main definitions

* `CochainComplex.opFunctor`, `ChainComplex.opFunctor`: the opposite of an `ℕ`-indexed
  (co)chain complex as an `ℕ`-indexed (co)chain complex in the opposite category.
* `CategoryTheory.InjectiveResolution.op`, `CategoryTheory.ProjectiveResolution.op`.
* `CategoryTheory.Functor.leftDerivedOpIso`: `F.op.leftDerived n ≅ (F.rightDerived n).op`.
* `CategoryTheory.Functor.rightDerivedOpIso`: `F.op.rightDerived n ≅ (F.leftDerived n).op`.
* `CategoryTheory.Equivalence.abelianOfAntiEquivalence`.
* `CategoryTheory.Equivalence.leftDerivedCompIsoOfAntiEquivalence` and its objectwise form
  `CategoryTheory.Equivalence.leftDerivedObjIsoOfAntiEquivalence`.

## References

* [Stacks: Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- The opposite of an `ℕ`-indexed cochain complex, as an `ℕ`-indexed chain complex. -/
def opFunctor : (CochainComplex C ℕ)ᵒᵖ ⥤ ChainComplex Cᵒᵖ ℕ :=
  HomologicalComplex.opFunctor C (ComplexShape.up ℕ)

variable {C}

/-- The objects of the opposite complex are the opposites of the objects. -/
@[simp] lemma opFunctor_obj_X (K : (CochainComplex C ℕ)ᵒᵖ) (n : ℕ) :
    ((opFunctor C).obj K).X n = op (K.unop.X n) := rfl

/-- The differentials of the opposite complex are the opposites of the differentials. -/
@[simp] lemma opFunctor_obj_d (K : (CochainComplex C ℕ)ᵒᵖ) (i j : ℕ) :
    ((opFunctor C).obj K).d i j = (K.unop.d j i).op := rfl

/-- The components of the opposite of a morphism of complexes. -/
@[simp] lemma opFunctor_map_f {K L : (CochainComplex C ℕ)ᵒᵖ} (φ : K ⟶ L) (n : ℕ) :
    ((opFunctor C).map φ).f n = (φ.unop.f n).op := rfl

/-- The opposite of a complex with homology in degree `i` has homology in degree `i`. -/
instance (K : (CochainComplex C ℕ)ᵒᵖ) (i : ℕ) [K.unop.HasHomology i] :
    ((opFunctor C).obj K).HasHomology i :=
  inferInstanceAs (((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).obj
    (op K.unop)).HasHomology i)

/-- The opposite of a quasi-isomorphism is a quasi-isomorphism. -/
instance {K L : CochainComplex C ℕ} (φ : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [QuasiIso φ] : QuasiIso ((opFunctor C).map φ.op) :=
  inferInstanceAs (QuasiIso ((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map φ.op))

/-- The opposite of the cochain complex concentrated in degree `0` is the chain complex
concentrated in degree `0`. -/
def opFunctorSingle₀Iso [HasZeroObject C] (X : C) :
    (opFunctor C).obj (op ((single₀ C).obj X)) ≅ (ChainComplex.single₀ Cᵒᵖ).obj (op X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => match i with
      | 0 => Iso.refl _
      | n + 1 => IsZero.iso
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)).op
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)))
    (by intros; simp [HomologicalComplex.single_obj_d])

/-- In degree `0` the comparison of single complexes is the identity. -/
lemma opFunctorSingle₀Iso_hom_f_zero [HasZeroObject C] (X : C) :
    (opFunctorSingle₀Iso X).hom.f 0 = 𝟙 _ :=
  rfl

/-- The homology of the opposite of a cochain complex is the opposite of its homology. -/
def opFunctorHomologyIso (K : CochainComplex C ℕ) (i : ℕ) [K.HasHomology i] :
    ((opFunctor C).obj (op K)).homology i ≅ op (K.homology i) :=
  K.homologyOp i

/-- Naturality of `CochainComplex.opFunctorHomologyIso`. -/
@[reassoc]
lemma opFunctorHomologyIso_hom_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) (i : ℕ)
    [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.homologyMap ((opFunctor C).map φ.op) i ≫ (opFunctorHomologyIso K i).hom =
      (opFunctorHomologyIso L i).hom ≫ (HomologicalComplex.homologyMap φ i).op :=
  HomologicalComplex.homologyOp_hom_naturality φ i

end CochainComplex

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- The opposite of an `ℕ`-indexed chain complex, as an `ℕ`-indexed cochain complex. -/
def opFunctor : (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex Cᵒᵖ ℕ :=
  HomologicalComplex.opFunctor C (ComplexShape.down ℕ)

variable {C}

/-- The objects of the opposite complex are the opposites of the objects. -/
@[simp] lemma opFunctor_obj_X (K : (ChainComplex C ℕ)ᵒᵖ) (n : ℕ) :
    ((opFunctor C).obj K).X n = op (K.unop.X n) := rfl

/-- The differentials of the opposite complex are the opposites of the differentials. -/
@[simp] lemma opFunctor_obj_d (K : (ChainComplex C ℕ)ᵒᵖ) (i j : ℕ) :
    ((opFunctor C).obj K).d i j = (K.unop.d j i).op := rfl

/-- The components of the opposite of a morphism of complexes. -/
@[simp] lemma opFunctor_map_f {K L : (ChainComplex C ℕ)ᵒᵖ} (φ : K ⟶ L) (n : ℕ) :
    ((opFunctor C).map φ).f n = (φ.unop.f n).op := rfl

/-- The opposite of a complex with homology in degree `i` has homology in degree `i`. -/
instance (K : (ChainComplex C ℕ)ᵒᵖ) (i : ℕ) [K.unop.HasHomology i] :
    ((opFunctor C).obj K).HasHomology i :=
  inferInstanceAs (((HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).obj
    (op K.unop)).HasHomology i)

/-- The opposite of a quasi-isomorphism is a quasi-isomorphism. -/
instance {K L : ChainComplex C ℕ} (φ : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [QuasiIso φ] : QuasiIso ((opFunctor C).map φ.op) :=
  inferInstanceAs (QuasiIso ((HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).map φ.op))

/-- The opposite of the chain complex concentrated in degree `0` is the cochain complex
concentrated in degree `0`. -/
def opFunctorSingle₀Iso [HasZeroObject C] (X : C) :
    (opFunctor C).obj (op ((single₀ C).obj X)) ≅ (CochainComplex.single₀ Cᵒᵖ).obj (op X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => match i with
      | 0 => Iso.refl _
      | n + 1 => IsZero.iso
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)).op
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)))
    (by intros; simp [HomologicalComplex.single_obj_d])

/-- In degree `0` the comparison of single complexes is the identity. -/
lemma opFunctorSingle₀Iso_inv_f_zero [HasZeroObject C] (X : C) :
    (opFunctorSingle₀Iso X).inv.f 0 = 𝟙 _ :=
  rfl

/-- The homology of the opposite of a chain complex is the opposite of its homology. -/
def opFunctorHomologyIso (K : ChainComplex C ℕ) (i : ℕ) [K.HasHomology i] :
    ((opFunctor C).obj (op K)).homology i ≅ op (K.homology i) :=
  K.homologyOp i

/-- Naturality of `ChainComplex.opFunctorHomologyIso`. -/
@[reassoc]
lemma opFunctorHomologyIso_hom_naturality {K L : ChainComplex C ℕ} (φ : K ⟶ L) (i : ℕ)
    [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.homologyMap ((opFunctor C).map φ.op) i ≫ (opFunctorHomologyIso K i).hom =
      (opFunctorHomologyIso L i).hom ≫ (HomologicalComplex.homologyMap φ i).op :=
  HomologicalComplex.homologyOp_hom_naturality φ i

end ChainComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace InjectiveResolution

variable {X : C} (I : InjectiveResolution X)

/-- **The opposite of an injective resolution is a projective resolution.** -/
abbrev op : ProjectiveResolution (op X) where
  complex := (CochainComplex.opFunctor C).obj (Opposite.op I.cocomplex)
  projective n := by dsimp; infer_instance
  π := (CochainComplex.opFunctor C).map I.ι.op ≫ (CochainComplex.opFunctorSingle₀Iso X).hom
  quasiIso := inferInstance

/-- The complex of the opposite resolution. -/
@[simp] lemma op_complex :
    I.op.complex = (CochainComplex.opFunctor C).obj (Opposite.op I.cocomplex) :=
  rfl

/-- The augmentation of the opposite resolution is the opposite of the augmentation. -/
lemma op_π_f_zero : I.op.π.f 0 = (I.ι.f 0).op :=
  Category.comp_id _

end InjectiveResolution

namespace ProjectiveResolution

variable {X : C} (P : ProjectiveResolution X)

/-- **The opposite of a projective resolution is an injective resolution.** -/
abbrev op : InjectiveResolution (op X) where
  cocomplex := (ChainComplex.opFunctor C).obj (Opposite.op P.complex)
  injective n := by dsimp; infer_instance
  ι := (ChainComplex.opFunctorSingle₀Iso X).inv ≫ (ChainComplex.opFunctor C).map P.π.op
  quasiIso := inferInstance

/-- The cocomplex of the opposite resolution. -/
@[simp] lemma op_cocomplex :
    P.op.cocomplex = (ChainComplex.opFunctor C).obj (Opposite.op P.complex) :=
  rfl

/-- The augmentation of the opposite resolution is the opposite of the augmentation. -/
lemma op_ι_f_zero : P.op.ι.f 0 = (P.π.f 0).op :=
  Category.id_comp _

end ProjectiveResolution

namespace Functor

/-- Four commuting squares pasted side by side. -/
private lemma paste_squares {E : Type*} [Category* E] {X₀ X₁ Y₀ Y₁ Z₀ Z₁ W₀ W₁ V₀ V₁ : E}
    {f : X₀ ⟶ X₁} {a₀ : X₀ ⟶ Y₀} {a₁ : X₁ ⟶ Y₁} {g : Y₀ ⟶ Y₁} {b₀ : Y₀ ⟶ Z₀} {b₁ : Y₁ ⟶ Z₁}
    {h : Z₀ ⟶ Z₁} {c₀ : Z₀ ⟶ W₀} {c₁ : Z₁ ⟶ W₁} {k : W₀ ⟶ W₁} {d₀ : W₀ ⟶ V₀} {d₁ : W₁ ⟶ V₁}
    {l : V₀ ⟶ V₁} (h₁ : f ≫ a₁ = a₀ ≫ g) (h₂ : g ≫ b₁ = b₀ ≫ h) (h₃ : h ≫ c₁ = c₀ ≫ k)
    (h₄ : k ≫ d₁ = d₀ ≫ l) :
    f ≫ a₁ ≫ b₁ ≫ c₁ ≫ d₁ = (a₀ ≫ b₀ ≫ c₀ ≫ d₀) ≫ l := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

variable {A : Type*} [Category* A] [Abelian A] (F : C ⥤ A) [F.Additive]

/-- Applying `F.op` to the opposite of a cochain complex is the opposite of applying `F`. -/
def mapCochainComplexOpIso (K : CochainComplex C ℕ) :
    (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((CochainComplex.opFunctor C).obj (op K)) ≅
      (CochainComplex.opFunctor A).obj (op ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; simp)

/-- Naturality of `CategoryTheory.Functor.mapCochainComplexOpIso`. -/
@[reassoc]
lemma mapCochainComplexOpIso_hom_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (F.op.mapHomologicalComplex _).map ((CochainComplex.opFunctor C).map φ.op) ≫
        (F.mapCochainComplexOpIso K).hom =
      (F.mapCochainComplexOpIso L).hom ≫
        (CochainComplex.opFunctor A).map ((F.mapHomologicalComplex _).map φ).op := by
  ext n : 1
  exact (Category.comp_id _).trans (Category.id_comp _).symm

section Injective

variable [EnoughInjectives C]

/-- The component at `X` of `CategoryTheory.Functor.leftDerivedOpIso`. -/
def leftDerivedOpObjIso (n : ℕ) (X : Cᵒᵖ) :
    (F.op.leftDerived n).obj X ≅ op ((F.rightDerived n).obj X.unop) :=
  (injectiveResolution X.unop).op.isoLeftDerivedObj F.op n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (F.mapCochainComplexOpIso _) ≪≫
    CochainComplex.opFunctorHomologyIso _ n ≪≫
    ((injectiveResolution X.unop).isoRightDerivedObj F n).op

/-- **The left derived functors of `F.op` are the opposites of the right derived functors of
`F`**: `(F.op).leftDerived n ≅ (F.rightDerived n).op`, computed on the opposite of the chosen
injective resolution, which is a projective resolution in `Cᵒᵖ`. -/
def leftDerivedOpIso (n : ℕ) : F.op.leftDerived n ≅ (F.rightDerived n).op :=
  NatIso.ofComponents (F.leftDerivedOpObjIso n) (fun {X Y} f => by
    let I := injectiveResolution X.unop
    let J := injectiveResolution Y.unop
    let ψ := InjectiveResolution.desc f.unop I J
    have h₁ := I.op.isoLeftDerivedObj_hom_naturality f J.op
      ((CochainComplex.opFunctor C).map ψ.op) (by
        rw [InjectiveResolution.op_π_f_zero, InjectiveResolution.op_π_f_zero]
        exact congrArg Quiver.Hom.op (InjectiveResolution.desc_commutes_zero f.unop I J)) F.op n
    have h₂ := InjectiveResolution.isoRightDerivedObj_hom_naturality f.unop J I ψ
      (InjectiveResolution.desc_commutes_zero _ _ _) F n
    have h₃ : HomologicalComplex.homologyMap
          ((F.op.mapHomologicalComplex _).map ((CochainComplex.opFunctor C).map ψ.op)) n ≫
          HomologicalComplex.homologyMap (F.mapCochainComplexOpIso _).hom n =
        HomologicalComplex.homologyMap (F.mapCochainComplexOpIso _).hom n ≫
          HomologicalComplex.homologyMap
            ((CochainComplex.opFunctor A).map ((F.mapHomologicalComplex _).map ψ).op) n := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        mapCochainComplexOpIso_hom_naturality]
    exact paste_squares h₁ h₃
      (CochainComplex.opFunctorHomologyIso_hom_naturality ((F.mapHomologicalComplex _).map ψ) n)
      (congrArg Quiver.Hom.op h₂).symm)

end Injective

/-- Applying `F.op` to the opposite of a chain complex is the opposite of applying `F`. -/
def mapChainComplexOpIso (K : ChainComplex C ℕ) :
    (F.op.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((ChainComplex.opFunctor C).obj (op K)) ≅
      (ChainComplex.opFunctor A).obj (op ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; simp)

/-- Naturality of `CategoryTheory.Functor.mapChainComplexOpIso`. -/
@[reassoc]
lemma mapChainComplexOpIso_hom_naturality {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (F.op.mapHomologicalComplex _).map ((ChainComplex.opFunctor C).map φ.op) ≫
        (F.mapChainComplexOpIso K).hom =
      (F.mapChainComplexOpIso L).hom ≫
        (ChainComplex.opFunctor A).map ((F.mapHomologicalComplex _).map φ).op := by
  ext n : 1
  exact (Category.comp_id _).trans (Category.id_comp _).symm

section Projective

variable [EnoughProjectives C]

/-- The component at `X` of `CategoryTheory.Functor.rightDerivedOpIso`. -/
def rightDerivedOpObjIso (n : ℕ) (X : Cᵒᵖ) :
    (F.op.rightDerived n).obj X ≅ op ((F.leftDerived n).obj X.unop) :=
  (projectiveResolution X.unop).op.isoRightDerivedObj F.op n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (F.mapChainComplexOpIso _) ≪≫
    ChainComplex.opFunctorHomologyIso _ n ≪≫
    ((projectiveResolution X.unop).isoLeftDerivedObj F n).op

/-- **The right derived functors of `F.op` are the opposites of the left derived functors of
`F`**: `(F.op).rightDerived n ≅ (F.leftDerived n).op`, computed on the opposite of the chosen
projective resolution, which is an injective resolution in `Cᵒᵖ`. -/
def rightDerivedOpIso (n : ℕ) : F.op.rightDerived n ≅ (F.leftDerived n).op :=
  NatIso.ofComponents (F.rightDerivedOpObjIso n) (fun {X Y} f => by
    let P := projectiveResolution X.unop
    let Q := projectiveResolution Y.unop
    let ψ := ProjectiveResolution.lift f.unop Q P
    have h₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality f P.op Q.op
      ((ChainComplex.opFunctor C).map ψ.op) (by
        rw [ProjectiveResolution.op_ι_f_zero, ProjectiveResolution.op_ι_f_zero]
        exact congrArg Quiver.Hom.op (ProjectiveResolution.lift_commutes_zero f.unop Q P)) F.op n
    have h₂ := ProjectiveResolution.isoLeftDerivedObj_hom_naturality f.unop Q P ψ
      (ProjectiveResolution.lift_commutes_zero _ _ _) F n
    have h₃ : HomologicalComplex.homologyMap
          ((F.op.mapHomologicalComplex _).map ((ChainComplex.opFunctor C).map ψ.op)) n ≫
          HomologicalComplex.homologyMap (F.mapChainComplexOpIso _).hom n =
        HomologicalComplex.homologyMap (F.mapChainComplexOpIso _).hom n ≫
          HomologicalComplex.homologyMap
            ((ChainComplex.opFunctor A).map ((F.mapHomologicalComplex _).map ψ).op) n := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        mapChainComplexOpIso_hom_naturality]
    exact paste_squares h₁ h₃
      (ChainComplex.opFunctorHomologyIso_hom_naturality ((F.mapHomologicalComplex _).map ψ) n)
      (congrArg Quiver.Hom.op h₂).symm)

end Projective

end Functor

namespace Equivalence

section AntiEquivalence

variable {C' : Type*} [Category* C'] (e : Cᵒᵖ ≌ C')

/-- **A preadditive category anti-equivalent to an abelian category is abelian.** -/
@[instance_reducible]
def abelianOfAntiEquivalence [Preadditive C'] : Abelian C' :=
  haveI : HasFiniteProducts C' :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  abelianOfEquivalence e.inverse

omit [Abelian C] in
/-- **A category anti-equivalent to a category with enough injectives has enough
projectives**: `Cᵒᵖ` has enough projectives, and these are transported along `e`. -/
lemma enoughProjectives_of_antiEquivalence (e : Cᵒᵖ ≌ C') [EnoughInjectives C] :
    EnoughProjectives C' :=
  e.enoughProjectives

end AntiEquivalence

variable {A : Type*} [Category* A] [Abelian A] {A' : Type*} [Category* A'] [Abelian A']
  {C' : Type*} [Category* C'] [Abelian C'] [HasProjectiveResolutions C'] [EnoughInjectives C]

/-- **Derived functors across an exact anti-equivalence.** Let `e : Cᵒᵖ ≌ C'` be an
anti-equivalence of abelian categories, `F : C ⥤ A` and `F' : C' ⥤ A'` additive functors, and
`δ : Aᵒᵖ ⥤ A'` an additive functor preserving homology (for instance an exact functor), with
`e.functor ⋙ F' ≅ F.op ⋙ δ`. Then for every `n` the `n`-th left derived functor of `F'` is,
on `e.functor.obj (op M)`, the image under `δ` of the `n`-th right derived functor of `F` at
`M`: the image under `e` of an injective resolution of `M` is a projective resolution of
`e.functor.obj (op M)`. -/
def leftDerivedCompIsoOfAntiEquivalence (e : Cᵒᵖ ≌ C') (F : C ⥤ A) [F.Additive]
    (F' : C' ⥤ A') [F'.Additive] (δ : Aᵒᵖ ⥤ A') [δ.Additive] [δ.PreservesHomology]
    (α : e.functor ⋙ F' ≅ F.op ⋙ δ) (n : ℕ) :
    e.functor ⋙ F'.leftDerived n ≅ (F.rightDerived n).op ⋙ δ :=
  haveI : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  (e.compLeftDerivedIso F' n).symm ≪≫ Functor.leftDerivedIsoOfNatIso α n ≪≫
    F.op.leftDerivedCompIso δ n ≪≫ Functor.isoWhiskerRight (F.leftDerivedOpIso n) δ

/-- The objectwise form of `CategoryTheory.Equivalence.leftDerivedCompIsoOfAntiEquivalence`:
`L_n F' (e (op M)) ≅ δ (op (R^n F M))`. -/
def leftDerivedObjIsoOfAntiEquivalence (e : Cᵒᵖ ≌ C') (F : C ⥤ A) [F.Additive]
    (F' : C' ⥤ A') [F'.Additive] (δ : Aᵒᵖ ⥤ A') [δ.Additive] [δ.PreservesHomology]
    (α : e.functor ⋙ F' ≅ F.op ⋙ δ) (n : ℕ) (M : C) :
    (F'.leftDerived n).obj (e.functor.obj (Opposite.op M)) ≅
      δ.obj (Opposite.op ((F.rightDerived n).obj M)) :=
  (e.leftDerivedCompIsoOfAntiEquivalence F F' δ α n).app (Opposite.op M)

end Equivalence

end CategoryTheory
