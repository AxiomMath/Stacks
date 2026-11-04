module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeTwoCoverGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactZariskiLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition

/-!
# Merging two open subspaces carrying sections of a stack

Let `P` be an algebraic space, `A₀, A₁ ⊆ P` open subspaces and `M` their union (the
sheafification of the union of subfunctors). This file shows that `M` is an open subspace, that
it is quasi-compact when `A₀` and `A₁` are, and that two 1-morphisms `y₀ : A₀ ⟶ 𝒳`,
`y₁ : A₁ ⟶ 𝒳` related by a 2-morphism over `A₀ ∩ A₁` glue to a 1-morphism `y : M ⟶ 𝒳`; if
moreover `y₀` and `y₁` are sections of `f : 𝒳 ⟶ Y` over `g : P ⟶ Y`, then so is `y`.

This is the descent step of the proof of [Stacks, Tag 0CQ7], carried out one pair of opens at a
time (see `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.exists_hom_of_twoCover`).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.unionOpen`: the union of two
  subfunctors of a sheaf.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.isOpenSubspace_unionOpen`: the union of
  two open subspaces is an open subspace.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.isQuasiCompactSpace_unionOpen`: the
  union of two quasi-compact open subspaces is quasi-compact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.exists_hom_unionOpen`: sections over
  two open subspaces agreeing over their intersection glue to a section over the union.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### 1-morphisms of space stacks -/

section StackMaps

variable {T Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
  (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The 1-morphism of a composite `a ≫ b`, followed by `x`, is the 1-morphism of `a` followed by
the 1-morphism of `b` and `x`. -/
lemma stackMap_comp_assoc (a : T ⟶ Z) (b : Z ⟶ Z')
    (x : algebraicSpaceStack.{u, w} B S hS Z' hZ' ⟶ 𝒳) :
    algebraicSpaceStackMap.{u, w} B S hS hT hZ' (a ≫ b) ≫ x =
      algebraicSpaceStackMap.{u, w} B S hS hT hZ a ≫
        (algebraicSpaceStackMap.{u, w} B S hS hZ hZ' b ≫ x) := by
  rw [algebraicSpaceStackMap_comp B S hS hT hZ hZ' a b]
  rfl

/-- Restricting a 1-morphism along two factorisations of the same morphism gives the same
1-morphism. -/
lemma stackMap_comp_comp_eq {Z₁ Z₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ₁ : IsAlgebraicSpace B S hS Z₁) (hZ₂ : IsAlgebraicSpace B S hS Z₂)
    (a : T ⟶ Z₁) (b : Z₁ ⟶ Z') (a' : T ⟶ Z₂) (b' : Z₂ ⟶ Z') (h : a ≫ b = a' ≫ b')
    (x : algebraicSpaceStack.{u, w} B S hS Z' hZ' ⟶ 𝒳) :
    algebraicSpaceStackMap.{u, w} B S hS hT hZ₁ a ≫
        (algebraicSpaceStackMap.{u, w} B S hS hZ₁ hZ' b ≫ x) =
      algebraicSpaceStackMap.{u, w} B S hS hT hZ₂ a' ≫
        (algebraicSpaceStackMap.{u, w} B S hS hZ₂ hZ' b' ≫ x) := by
  rw [← stackMap_comp_assoc hT hZ₁ hZ' a b, h, stackMap_comp_assoc hT hZ₂ hZ' a' b']

/-- The 1-morphism of an identity morphism of algebraic spaces acts as the identity. -/
lemma stackMap_id_comp (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    Nonempty (algebraicSpaceStackMap.{u, w} B S hS hZ hZ (𝟙 Z) ≫ x ≅ x) := by
  obtain ⟨e₀⟩ := nonempty_twoIso_associatedMap_id B S hS Z
  exact ⟨Bicategory.whiskerRightIso (Bicategory.InducedBicategory.isoMk e₀ :
      algebraicSpaceStackMap.{u, w} B S hS hZ hZ (𝟙 Z) ≅ 𝟙 _) x ≪≫ Bicategory.leftUnitor x⟩

/-- Restricting a section `x` of `f` over `g` along `a` gives a section over `a ≫ g`. -/
lemma nonempty_comp_iso_of_iso {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (a : T ⟶ Z) (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (g : Z ⟶ Y)
    (hx : Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY g)) :
    Nonempty ((algebraicSpaceStackMap.{u, w} B S hS hT hZ a ≫ x) ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS hT hY (a ≫ g)) := by
  obtain ⟨e⟩ := hx
  exact ⟨Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso _ e ≪≫
    eqToIso (algebraicSpaceStackMap_comp B S hS hT hZ hY a g).symm⟩

/-- Two sections of `f : 𝒳 ⟶ Y` over the same morphism are 2-isomorphic after composing with
`f`. -/
lemma nonempty_comp_iso_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (x x' : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (g : Z ⟶ Y)
    (hx : Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY g))
    (hx' : Nonempty (x' ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY g)) :
    Nonempty (x ≫ f ≅ x' ≫ f) := by
  obtain ⟨e⟩ := hx
  obtain ⟨e'⟩ := hx'
  exact ⟨e ≪≫ e'.symm⟩

end StackMaps

/-! ### The union of two open subspaces -/

section Union

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The union of two subfunctors `A₀, A₁` of a sheaf, as the sheafification of the
two-member supremum (indexed by `ULift Bool` so as to lie in `Type u`). -/
abbrev unionOpen (A₀ A₁ : Subfunctor P) : Subfunctor P :=
  (⨆ b : ULift.{u} Bool, bif b.down then A₁ else A₀).sheafify (BigFppfOver.topology B S hS)

/-- `A₀` is contained in the union of `A₀` and `A₁`. -/
lemma le_unionOpen_left (A₀ A₁ : Subfunctor P) :
    A₀ ≤ unionOpen (B := B) (S := S) (hS := hS) A₀ A₁ :=
  (le_iSup (fun b : ULift.{u} Bool => bif b.down then A₁ else A₀) ⟨false⟩).trans
    (Subfunctor.le_sheafify _ _)

/-- `A₁` is contained in the union of `A₀` and `A₁`. -/
lemma le_unionOpen_right (A₀ A₁ : Subfunctor P) :
    A₁ ≤ unionOpen (B := B) (S := S) (hS := hS) A₀ A₁ :=
  (le_iSup (fun b : ULift.{u} Bool => bif b.down then A₁ else A₀) ⟨true⟩).trans
    (Subfunctor.le_sheafify _ _)

/-- An element of the union lies fppf locally in `A₀` or in `A₁`. -/
lemma exists_covering_of_mem_unionOpen (A₀ A₁ : Subfunctor P) {T : BigFppfOver B S hS}
    {z : P.obj (op T)} (hz : z ∈ (unionOpen (B := B) (S := S) (hS := hS) A₀ A₁).obj (op T)) :
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f →
      P.map f.op z ∈ A₀.obj (op V) ∨ P.map f.op z ∈ A₁.obj (op V) := by
  refine ⟨_, hz, fun V f hf => ?_⟩
  have hf' : P.map f.op z ∈ (⨆ b : ULift.{u} Bool, bif b.down then A₁ else A₀).obj (op V) := hf
  rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hf'
  obtain ⟨⟨b⟩, hb⟩ := hf'
  cases b
  exacts [Or.inl hb, Or.inr hb]

/-- **The union of two open subspaces of an algebraic space is an open subspace.** -/
theorem isOpenSubspace_unionOpen (hP : IsAlgebraicSpace B S hS P) {A₀ A₁ : Subfunctor P}
    (h₀ : Space.IsOpenSubspace B S hS A₀) (h₁ : Space.IsOpenSubspace B S hS A₁) :
    Space.IsOpenSubspace B S hS (unionOpen (B := B) (S := S) (hS := hS) A₀ A₁) := by
  have hι := Space.isOpenImmersion_sheafify_iSup_ι B S hS hP.isSheaf
    (fun b : ULift.{u} Bool => bif b.down then A₁ else A₀)
    (fun b => by rcases b with ⟨b⟩; cases b; exacts [h₀.2, h₁.2])
  exact ⟨AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS _ hι.rep hP, hι⟩

/-- **The union of two quasi-compact open subspaces is quasi-compact.** -/
theorem isQuasiCompactSpace_unionOpen (hP : IsAlgebraicSpace B S hS P) {A₀ A₁ : Subfunctor P}
    (h₀ : Space.IsOpenSubspace B S hS A₀) (h₁ : Space.IsOpenSubspace B S hS A₁)
    (h₀qc : Space.IsQuasiCompactSpace B S hS A₀.toFunctor)
    (h₁qc : Space.IsQuasiCompactSpace B S hS A₁.toFunctor) :
    Space.IsQuasiCompactSpace B S hS
      (unionOpen (B := B) (S := S) (hS := hS) A₀ A₁).toFunctor := by
  set M := unionOpen (B := B) (S := S) (hS := hS) A₀ A₁
  have hM := isOpenSubspace_unionOpen hP h₀ h₁
  have hsup : (A₀.preimage M.ι ⊔ A₁.preimage M.ι).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
    refine top_le_iff.1 fun T z _ => ?_
    obtain ⟨R, hR, hRU⟩ := exists_covering_of_mem_unionOpen A₀ A₁ z.2
    refine (BigFppfOver.topology B S hS).superset_covering (fun V f hf => hRU hf) hR
  refine Space.isQuasiCompactSpace_of_finite_jointly_surjective' B S hS hM.1
    (A := fun b : Bool => (bif b then A₁ else A₀).toFunctor)
    (fun b => by cases b; exacts [h₀.1, h₁.1])
    (fun b => Subfunctor.homOfLe (show (bif b then A₁ else A₀) ≤ M by
      cases b; exacts [le_unionOpen_left A₀ A₁, le_unionOpen_right A₀ A₁]))
    (fun b => by cases b; exacts [h₀qc, h₁qc]) fun w => ?_
  rcases Space.mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top B S hS _ _ hsup w with
    ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨false, Space.pointsMap B S hS _ (A₀.fromPreimage M.ι) v,
      (Space.pointsMap_comp_apply B S hS _ _ v).symm⟩
  · exact ⟨true, Space.pointsMap B S hS _ (A₁.fromPreimage M.ι) v,
      (Space.pointsMap_comp_apply B S hS _ _ v).symm⟩

end Union

/-! ### Gluing over the union -/

section Glue

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The comparison `A ⟶ A.preimage M.ι` for `A ≤ M`. -/
def toPreimageOfLe {A M : Subfunctor P} (h : A ≤ M) : A.toFunctor ⟶ (A.preimage M.ι).toFunctor where
  app T := ↾fun z => ⟨⟨z.1, h T z.2⟩, z.2⟩

/-- Composing `toPreimageOfLe h` with the inclusion of `A.preimage M.ι` gives the inclusion
`A ⟶ M`. -/
lemma toPreimageOfLe_ι {A M : Subfunctor P} (h : A ≤ M) :
    toPreimageOfLe h ≫ (A.preimage M.ι).ι = Subfunctor.homOfLe h := by
  ext T z
  rfl

/-- `toPreimageOfLe h` is a section of `A.fromPreimage M.ι`. -/
lemma toPreimageOfLe_fromPreimage {A M : Subfunctor P} (h : A ≤ M) :
    toPreimageOfLe h ≫ A.fromPreimage M.ι = 𝟙 _ := by
  ext T z
  rfl

/-- The comparison `(A₀.preimage M.ι) ⊓ (A₁.preimage M.ι) ⟶ A₀ ⊓ A₁`. -/
def interPreimageToInter (A₀ A₁ M : Subfunctor P) :
    (A₀.preimage M.ι ⊓ A₁.preimage M.ι).toFunctor ⟶ (A₀ ⊓ A₁).toFunctor where
  app T := ↾fun z => ⟨z.1.1, z.2.1, z.2.2⟩

/-- **Gluing over the union of two open subspaces.** Let `A₀, A₁` be open subspaces of an
algebraic space `P`, `M` their union, `y₀ : A₀ ⟶ 𝒳`, `y₁ : A₁ ⟶ 𝒳` 1-morphisms into an algebraic
stack and `e : y₀|_{A₀ ∩ A₁} ⟶ y₁|_{A₀ ∩ A₁}` a 2-morphism. If `y₀` and `y₁` are sections of
`f : 𝒳 ⟶ Y` over `g|_{A₀}` and `g|_{A₁}` for some `g : P ⟶ Y`, there is a section `y : M ⟶ 𝒳`
of `f` over `g|_M` restricting to `y₀` and `y₁`. -/
theorem exists_hom_unionOpen (hP : IsAlgebraicSpace B S hS P) {A₀ A₁ : Subfunctor P}
    (h₀ : Space.IsOpenSubspace B S hS A₀) (h₁ : Space.IsOpenSubspace B S hS A₁)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (y₀ : algebraicSpaceStack.{u, w} B S hS A₀.toFunctor h₀.1 ⟶ 𝒳)
    (y₁ : algebraicSpaceStack.{u, w} B S hS A₁.toFunctor h₁.1 ⟶ 𝒳)
    (e : algebraicSpaceStackMap.{u, w} B S hS (Space.isOpenSubspace_inf B S hS hP A₀ A₁ h₀ h₁).1
        h₀.1 (Subfunctor.homOfLe inf_le_left) ≫ y₀ ⟶
      algebraicSpaceStackMap.{u, w} B S hS (Space.isOpenSubspace_inf B S hS hP A₀ A₁ h₀ h₁).1
        h₁.1 (Subfunctor.homOfLe inf_le_right) ≫ y₁)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (g : P ⟶ Y)
    (hy₀ : Nonempty (y₀ ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS h₀.1 hY (A₀.ι ≫ g)))
    (hy₁ : Nonempty (y₁ ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS h₁.1 hY (A₁.ι ≫ g))) :
    ∃ y : algebraicSpaceStack.{u, w} B S hS
        (unionOpen (B := B) (S := S) (hS := hS) A₀ A₁).toFunctor
        (isOpenSubspace_unionOpen hP h₀ h₁).1 ⟶ 𝒳,
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS h₀.1 (isOpenSubspace_unionOpen hP h₀ h₁).1
          (Subfunctor.homOfLe (le_unionOpen_left A₀ A₁)) ≫ y ≅ y₀) ∧
        Nonempty (algebraicSpaceStackMap.{u, w} B S hS h₁.1
          (isOpenSubspace_unionOpen hP h₀ h₁).1
          (Subfunctor.homOfLe (le_unionOpen_right A₀ A₁)) ≫ y ≅ y₁) ∧
        Nonempty (y ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
          (isOpenSubspace_unionOpen hP h₀ h₁).1 hY
          ((unionOpen (B := B) (S := S) (hS := hS) A₀ A₁).ι ≫ g)) := by
  set M := unionOpen (B := B) (S := S) (hS := hS) A₀ A₁
  have hM := isOpenSubspace_unionOpen hP h₀ h₁
  have hA₀₁ := Space.isOpenSubspace_inf B S hS hP A₀ A₁ h₀ h₁
  have hU₀ := Space.isOpenSubspace_preimage B S hS M.ι A₀ hP hM.1 h₀
  have hU₁ := Space.isOpenSubspace_preimage B S hS M.ι A₁ hP hM.1 h₁
  have hU₀₁ := Space.isOpenSubspace_inf B S hS hM.1 _ _ hU₀ hU₁
  -- the two pieces over the inverse images in `M`
  let z₀ := algebraicSpaceStackMap.{u, w} B S hS hU₀.1 h₀.1 (A₀.fromPreimage M.ι) ≫ y₀
  let z₁ := algebraicSpaceStackMap.{u, w} B S hS hU₁.1 h₁.1 (A₁.fromPreimage M.ι) ≫ y₁
  let r := interPreimageToInter A₀ A₁ M
  have hr₀ := stackMap_comp_comp_eq (𝒳 := 𝒳) hU₀₁.1 h₀.1 hU₀.1 hA₀₁.1
    (Subfunctor.homOfLe inf_le_left) (A₀.fromPreimage M.ι) r (Subfunctor.homOfLe inf_le_left)
    (by ext T z; rfl) y₀
  have hr₁ := stackMap_comp_comp_eq (𝒳 := 𝒳) hU₀₁.1 h₁.1 hU₁.1 hA₀₁.1
    (Subfunctor.homOfLe inf_le_right) (A₁.fromPreimage M.ι) r (Subfunctor.homOfLe inf_le_right)
    (by ext T z; rfl) y₁
  let eU : algebraicSpaceStackMap.{u, w} B S hS hU₀₁.1 hU₀.1 (Subfunctor.homOfLe inf_le_left) ≫
      z₀ ⟶ algebraicSpaceStackMap.{u, w} B S hS hU₀₁.1 hU₁.1 (Subfunctor.homOfLe inf_le_right) ≫
      z₁ :=
    eqToHom hr₀ ≫ Bicategory.whiskerLeft
      (algebraicSpaceStackMap.{u, w} B S hS hU₀₁.1 hA₀₁.1 r) e ≫ eqToHom hr₁.symm
  have hcov : ∀ (T : BigFppfOver B S hS) (z : M.toFunctor.obj (op T)),
      ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f →
        M.toFunctor.map f.op z ∈ (A₀.preimage M.ι).obj (op V) ∨
          M.toFunctor.map f.op z ∈ (A₁.preimage M.ι).obj (op V) :=
    fun T z => exists_covering_of_mem_unionOpen A₀ A₁ z.2
  obtain ⟨y, ⟨e₀⟩, ⟨e₁⟩⟩ := exists_hom_of_twoCover hM.1 (A₀.preimage M.ι) (A₁.preimage M.ι)
    hU₀.1 hU₁.1 hU₀₁.1 z₀ z₁ eU hcov
  -- reading the restrictions to `A₀`, `A₁` back
  have back : ∀ {A : Subfunctor P} (hA : Space.IsOpenSubspace B S hS A) (hle : A ≤ M)
      (hU : Space.IsOpenSubspace B S hS (A.preimage M.ι))
      (yA : algebraicSpaceStack.{u, w} B S hS A.toFunctor hA.1 ⟶ 𝒳),
      (algebraicSpaceStackMap.{u, w} B S hS hU.1 hM.1 (A.preimage M.ι).ι ≫ y ≅
        algebraicSpaceStackMap.{u, w} B S hS hU.1 hA.1 (A.fromPreimage M.ι) ≫ yA) →
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS hA.1 hM.1 (Subfunctor.homOfLe hle) ≫ y ≅
        yA) := by
    intro A hA hle hU yA eA
    obtain ⟨eid⟩ := stackMap_id_comp hA.1 yA
    refine ⟨eqToIso ?_ ≪≫ Bicategory.whiskerLeftIso
      (algebraicSpaceStackMap.{u, w} B S hS hA.1 hU.1 (toPreimageOfLe hle)) eA ≪≫
      eqToIso ?_ ≪≫ eid⟩
    · rw [← toPreimageOfLe_ι hle, stackMap_comp_assoc hA.1 hU.1 hM.1]
    · rw [← stackMap_comp_assoc hA.1 hU.1 hA.1, toPreimageOfLe_fromPreimage]
  -- `y` is a section of `f` over `g|_M`
  refine ⟨y, back h₀ (le_unionOpen_left A₀ A₁) hU₀ y₀ e₀,
    back h₁ (le_unionOpen_right A₀ A₁) hU₁ y₁ e₁, ?_⟩
  refine ChowGerbeGlue.nonempty_iso_algebraicSpaceStackMap_of_cover hM.1 hY
    (twoCoverFamily (A₀.preimage M.ι) (A₁.preimage M.ι))
    (isAlgebraicSpace_twoCoverFamily _ _ hU₀.1 hU₁.1) (y ≫ f) (M.ι ≫ g) (fun b => ?_)
    (fun T z => by
      obtain ⟨R, hR, hRU⟩ := hcov T z
      exact ⟨R, hR, fun V f hf => (hRU hf).elim (fun h => ⟨false, h⟩) fun h => ⟨true, h⟩⟩)
  cases b
  · obtain ⟨k⟩ := nonempty_comp_iso_of_iso hU₀.1 h₀.1 hY f (A₀.fromPreimage M.ι) y₀ _ hy₀
    exact ⟨(Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e₀ f ≪≫ k ≪≫
      eqToIso (by rw [Subfunctor.fromPreimage_ι_assoc]; rfl)⟩
  · obtain ⟨k⟩ := nonempty_comp_iso_of_iso hU₁.1 h₁.1 hY f (A₁.fromPreimage M.ι) y₁ _ hy₁
    exact ⟨(Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e₁ f ≪≫ k ≪≫
      eqToIso (by rw [Subfunctor.fromPreimage_ι_assoc]; rfl)⟩

end Glue

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge

end
