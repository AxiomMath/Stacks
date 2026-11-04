module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModulesPairingFiber

/-!
# Naturality of the pairing of finite locally constant abelian sheaves

Let `e` be an equivalence of the finite locally constant sheaves of sets on a site with the finite
continuous `G`-sets and `E` the equivalence of finite locally constant abelian sheaves with finite
discrete `G`-modules that it induces (Tag 0DV5 (2)). An equivariant biadditive map
`P : M × N → L` gives a biadditive pairing of sections `E⁻¹M × E⁻¹N → E⁻¹L`
(`Stacks.ConstantSheaf.finiteLocallyConstantPairing`). Here this pairing is shown to be natural
in each of the three modules: for `f : M' → M` the pairing attached to `P` evaluated on
`E⁻¹(f)(a)` is the pairing attached to `P ∘ (f × 1)` evaluated on `a`, and similarly in the second
variable and in the target.

The point is the module-theoretic consequence: if the three modules carry compatible actions of a
commutative ring `Λ` through equivariant endomorphisms, and `P` is `Λ`-bilinear, then the pairing
of sections is `Λ`-bilinear for the `Λ`-module structures transported by `E⁻¹`. This is what
makes the pairing of lisse sheaves of `Λ`-modules a morphism out of their tensor product over
`Λ`, for coefficient rings `Λ` such as `O/ℓⁿ⁺¹` where additivity does not imply linearity.

## Main definitions

* `Stacks.ConstantSheaf.finiteGModuleCommGrpMap`: the morphism of group objects of finite
  `G`-sets attached to a morphism of finite discrete `G`-modules.

## Main results

* `Stacks.ConstantSheaf.finiteLocallyConstantInverseObjIso_hom_app_map`: `E⁻¹` on morphisms is
  read off from `e⁻¹`.
* `Stacks.ConstantSheaf.finiteLocallyConstantPairing_map_left`,
  `Stacks.ConstantSheaf.finiteLocallyConstantPairing_map_right`,
  `Stacks.ConstantSheaf.map_finiteLocallyConstantPairing`: the naturality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u u' w

attribute [local instance] cartesianMonoidalSheafType braidedSheafType
  braidedContinuousGSetIsFinite braidedι_continuousGSetIsFinite
  cartesianMonoidalContinuousGSet braidedContinuousGSet

namespace Stacks.ConstantSheaf

section Finite

variable {G : Type u'} [Group G] [TopologicalSpace G]

/-- The morphism of commutative group objects of finite continuous `G`-sets attached to a morphism
of finite discrete `G`-modules. -/
def finiteGModuleCommGrpMap {M M' : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory}
    (f : M ⟶ M') : finiteGModuleCommGrp G M ⟶ finiteGModuleCommGrp G M' :=
  (ObjectProperty.pullCommGrpSubFunctor _).map
    (ObjectProperty.homMk ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.map f.hom))

/-- The counit `finiteGModuleCommGrpCounit` is natural. -/
theorem finiteGModuleCommGrpCounit_map
    {M M' : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory} (f : M ⟶ M')
    (t : (finiteGSetForget.{w, w} G).obj (finiteGModuleCommGrp G M).X) :
    (finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit M')
        ((finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpMap f).hom.hom.hom t) =
      f.hom.hom.hom.hom.hom ((finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit M) t) :=
  congrArg (fun k : (commGrpContinuousGSetEquivalence.{u', w} (G := G)).functor.obj
        ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj M.obj) ⟶ M'.obj =>
      (AlgebraicGeometry.ContinuousGSet.forget G).map
        ((ContinuousGAddCommGrp.forgetAction G).map k) t)
    ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.hom.naturality f.hom)

variable {M M' N N' L L' : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory}

/-- Morphisms of finite continuous `G`-sets out of a group object agree when they agree after the
counit. -/
theorem finiteGSetHom_ext_of_counit
    {X : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory}
    {φ ψ : X ⟶ (finiteGModuleCommGrp G L).X}
    (h : ∀ w, (finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit L)
        ((finiteGSetForget.{w, w} G).map φ w) =
      (finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit L)
        ((finiteGSetForget.{w, w} G).map ψ w)) : φ = ψ := by
  iterate 3 apply ObjectProperty.hom_ext
  ext w
  exact (finiteGModuleCommGrpCounit_bijective L).1 (h w)

/-- **The pairing of group objects is natural in the first module.** -/
theorem whiskerRight_finiteGModulePairing (f : M' ⟶ M)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M'.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M'.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P' ((M'.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = P (f.hom.hom.hom.hom.hom a) b) :
    (finiteGModuleCommGrpMap f).hom.hom.hom ▷ (finiteGModuleCommGrp G N).X ≫
        finiteGModulePairing M N L P hP = finiteGModulePairing M' N L P' hP' := by
  refine finiteGSetHom_ext_of_counit fun w => ?_
  rw [Functor.map_comp, types_comp_apply, finiteGModuleCommGrpCounit_finiteGModulePairing,
    finiteGModuleCommGrpCounit_finiteGModulePairing]
  refine Eq.trans ?_ (hPP' _ _).symm
  rw [← types_comp_apply
      ((finiteGSetForget.{w, w} G).map _) ((finiteGSetForget.{w, w} G).map (fst _ _)),
    ← Functor.map_comp, whiskerRight_fst, Functor.map_comp, types_comp_apply,
    finiteGModuleCommGrpCounit_map, ← types_comp_apply ((finiteGSetForget.{w, w} G).map _)
      ((finiteGSetForget.{w, w} G).map (snd _ _)), ← Functor.map_comp, whiskerRight_snd]

/-- **The pairing of group objects is natural in the second module.** -/
theorem whiskerLeft_finiteGModulePairing (f : N' ⟶ N)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M.obj.obj.obj.V →+ N'.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N'.obj.obj.obj.V),
      P' ((M.obj.obj.obj.ρ g).hom a) ((N'.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = P a (f.hom.hom.hom.hom.hom b)) :
    (finiteGModuleCommGrp G M).X ◁ (finiteGModuleCommGrpMap f).hom.hom.hom ≫
        finiteGModulePairing M N L P hP = finiteGModulePairing M N' L P' hP' := by
  refine finiteGSetHom_ext_of_counit fun w => ?_
  rw [Functor.map_comp, types_comp_apply, finiteGModuleCommGrpCounit_finiteGModulePairing,
    finiteGModuleCommGrpCounit_finiteGModulePairing]
  refine Eq.trans ?_ (hPP' _ _).symm
  rw [← types_comp_apply
      ((finiteGSetForget.{w, w} G).map _) ((finiteGSetForget.{w, w} G).map (snd _ _)),
    ← Functor.map_comp, whiskerLeft_snd, Functor.map_comp, types_comp_apply,
    finiteGModuleCommGrpCounit_map, ← types_comp_apply ((finiteGSetForget.{w, w} G).map _)
      ((finiteGSetForget.{w, w} G).map (fst _ _)), ← Functor.map_comp, whiskerLeft_fst]

/-- **The pairing of group objects is natural in the target module.** -/
theorem finiteGModulePairing_comp_map (f : L ⟶ L')
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L'.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P' ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L'.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = f.hom.hom.hom.hom.hom (P a b)) :
    finiteGModulePairing M N L P hP ≫ (finiteGModuleCommGrpMap f).hom.hom.hom =
      finiteGModulePairing M N L' P' hP' := by
  refine finiteGSetHom_ext_of_counit fun w => ?_
  rw [Functor.map_comp, types_comp_apply, finiteGModuleCommGrpCounit_map,
    finiteGModuleCommGrpCounit_finiteGModulePairing,
    finiteGModuleCommGrpCounit_finiteGModulePairing]
  exact (hPP' _ _).symm

end Finite

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The pairing of sections attached to `(φ ▷ S) ≫ β` is that of `β` after `φ` in the first
variable. -/
theorem sectionsPairing_map_left {R R' S T : CommGrp (Sheaf J (Type w))} (φ : R' ⟶ R)
    {β : R.X ⊗ S.X ⟶ T.X} {β' : R'.X ⊗ S.X ⟶ T.X} (hβ : IsBimultiplicative β)
    (hβ' : IsBimultiplicative β') (h : φ.hom.hom.hom ▷ S.X ≫ β = β') (U : Cᵒᵖ)
    (x : ((Sites.AbelianSheaf.externalSheaf J).obj R').obj.obj U)
    (y : ((Sites.AbelianSheaf.externalSheaf J).obj S).obj.obj U) :
    Sites.AbelianSheaf.sectionsPairing hβ U
        (((Sites.AbelianSheaf.externalSheaf J).map φ).hom.app U x) y =
      Sites.AbelianSheaf.sectionsPairing hβ' U x y := by
  let : (sheafToPresheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  subst h
  show ((Functor.LaxMonoidal.μ (sheafToPresheaf J (Type w)) R.X S.X ≫
      (sheafToPresheaf J (Type w)).map β).app U _) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf J (Type w)) R'.X S.X ≫
      (sheafToPresheaf J (Type w)).map (φ.hom.hom.hom ▷ S.X ≫ β)).app U _)
  rw [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  rfl

/-- The pairing of sections attached to `(R ◁ φ) ≫ β` is that of `β` after `φ` in the second
variable. -/
theorem sectionsPairing_map_right {R S S' T : CommGrp (Sheaf J (Type w))} (φ : S' ⟶ S)
    {β : R.X ⊗ S.X ⟶ T.X} {β' : R.X ⊗ S'.X ⟶ T.X} (hβ : IsBimultiplicative β)
    (hβ' : IsBimultiplicative β') (h : R.X ◁ φ.hom.hom.hom ≫ β = β') (U : Cᵒᵖ)
    (x : ((Sites.AbelianSheaf.externalSheaf J).obj R).obj.obj U)
    (y : ((Sites.AbelianSheaf.externalSheaf J).obj S').obj.obj U) :
    Sites.AbelianSheaf.sectionsPairing hβ U x
        (((Sites.AbelianSheaf.externalSheaf J).map φ).hom.app U y) =
      Sites.AbelianSheaf.sectionsPairing hβ' U x y := by
  let : (sheafToPresheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  subst h
  show ((Functor.LaxMonoidal.μ (sheafToPresheaf J (Type w)) R.X S.X ≫
      (sheafToPresheaf J (Type w)).map β).app U _) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf J (Type w)) R.X S'.X ≫
      (sheafToPresheaf J (Type w)).map (R.X ◁ φ.hom.hom.hom ≫ β)).app U _)
  rw [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_right_assoc]
  rfl

/-- The pairing of sections attached to `β ≫ φ` is `φ` after that of `β`. -/
theorem map_sectionsPairing {R S T T' : CommGrp (Sheaf J (Type w))} (φ : T ⟶ T')
    {β : R.X ⊗ S.X ⟶ T.X} {β' : R.X ⊗ S.X ⟶ T'.X} (hβ : IsBimultiplicative β)
    (hβ' : IsBimultiplicative β') (h : β ≫ φ.hom.hom.hom = β') (U : Cᵒᵖ)
    (x : ((Sites.AbelianSheaf.externalSheaf J).obj R).obj.obj U)
    (y : ((Sites.AbelianSheaf.externalSheaf J).obj S).obj.obj U) :
    ((Sites.AbelianSheaf.externalSheaf J).map φ).hom.app U
        (Sites.AbelianSheaf.sectionsPairing hβ U x y) =
      Sites.AbelianSheaf.sectionsPairing hβ' U x y := by
  subst h
  rfl

end Sections

/-- A lax monoidal functor carries the first-variable naturality of a morphism out of a tensor
product to the one of `μ ≫ F.map g`. -/
private theorem whiskerRight_μ_comp_map {A B : Type*} [Category A] [MonoidalCategory A]
    [Category B] [MonoidalCategory B] (F : A ⥤ B) [F.LaxMonoidal] {X X' Y Z : A} (f : X' ⟶ X)
    (g : X ⊗ Y ⟶ Z) (g' : X' ⊗ Y ⟶ Z) (h : f ▷ Y ≫ g = g') :
    F.map f ▷ F.obj Y ≫ Functor.LaxMonoidal.μ F X Y ≫ F.map g =
      Functor.LaxMonoidal.μ F X' Y ≫ F.map g' := by
  subst h
  simp [Functor.LaxMonoidal.μ_natural_left_assoc]

/-- A lax monoidal functor carries the second-variable naturality of a morphism out of a tensor
product to the one of `μ ≫ F.map g`. -/
private theorem whiskerLeft_μ_comp_map {A B : Type*} [Category A] [MonoidalCategory A]
    [Category B] [MonoidalCategory B] (F : A ⥤ B) [F.LaxMonoidal] {X Y Y' Z : A} (f : Y' ⟶ Y)
    (g : X ⊗ Y ⟶ Z) (g' : X ⊗ Y' ⟶ Z) (h : X ◁ f ≫ g = g') :
    F.obj X ◁ F.map f ≫ Functor.LaxMonoidal.μ F X Y ≫ F.map g =
      Functor.LaxMonoidal.μ F X Y' ≫ F.map g' := by
  subst h
  simp [Functor.LaxMonoidal.μ_natural_right_assoc]

section Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {G : Type u'} [Group G] [TopologicalSpace G]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
  (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory)

attribute [local instance] braidedFiniteLocallyConstantSetSheaf
  braidedι_finiteLocallyConstantSetSheaf

variable {M M' N N' L L' : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory}

/-- **`E⁻¹` on morphisms is read off from `e⁻¹`**: under the identification
`Stacks.ConstantSheaf.finiteLocallyConstantInverseObjIso`, the morphism of abelian sheaves
attached to `f : M ⟶ M'` by the equivalence of Tag 0DV5 (2) is the morphism of group objects that
`e⁻¹` attaches to the morphism of group objects of `f`. -/
theorem finiteLocallyConstantInverseObjIso_hom_app_map (f : M ⟶ M') (U : Cᵒᵖ)
    (a : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      M).obj.obj.obj U) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    (finiteLocallyConstantInverseObjIso J e M').hom.hom.app U
        (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.map
          f).hom.hom.app U a) =
      ((Sites.AbelianSheaf.externalSheaf J).map
        ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.map
          (e.inverse.mapCommGrp.map (finiteGModuleCommGrpMap f)))).hom.app U
        ((finiteLocallyConstantInverseObjIso J e M).hom.hom.app U a) := by
  simp only [finiteLocallyConstantAbelianEquivalenceOfSetEquivalence,
    ObjectProperty.commGrpEquivalence, Sites.AbelianSheaf.equivalence]
  rfl

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] in
/-- The internal pairing is natural in the first module. -/
theorem whiskerRight_finiteLocallyConstantInternalPairing (f : M' ⟶ M)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M'.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M'.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P' ((M'.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = P (f.hom.hom.hom.hom.hom a) b) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map
        (e.inverse.map (finiteGModuleCommGrpMap f).hom.hom.hom) ▷ _ ≫
        finiteLocallyConstantInternalPairing J e M N L P hP =
      finiteLocallyConstantInternalPairing J e M' N L P' hP' := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  dsimp only [finiteLocallyConstantInternalPairing]
  exact whiskerRight_μ_comp_map (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι _ _ _
    (whiskerRight_μ_comp_map e.inverse _ _ _
    (whiskerRight_finiteGModulePairing f P hP P' hP' hPP'))

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] in
/-- The internal pairing is natural in the second module. -/
theorem whiskerLeft_finiteLocallyConstantInternalPairing (f : N' ⟶ N)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M.obj.obj.obj.V →+ N'.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N'.obj.obj.obj.V),
      P' ((M.obj.obj.obj.ρ g).hom a) ((N'.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = P a (f.hom.hom.hom.hom.hom b)) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    _ ◁ (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map
        (e.inverse.map (finiteGModuleCommGrpMap f).hom.hom.hom) ≫
        finiteLocallyConstantInternalPairing J e M N L P hP =
      finiteLocallyConstantInternalPairing J e M N' L P' hP' := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  dsimp only [finiteLocallyConstantInternalPairing]
  exact whiskerLeft_μ_comp_map (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι _ _ _
    (whiskerLeft_μ_comp_map e.inverse _ _ _
    (whiskerLeft_finiteGModulePairing f P hP P' hP' hPP'))

omit [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] in
/-- The internal pairing is natural in the target module. -/
theorem finiteLocallyConstantInternalPairing_comp_map (f : L ⟶ L')
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L'.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P' ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L'.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = f.hom.hom.hom.hom.hom (P a b)) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    finiteLocallyConstantInternalPairing J e M N L P hP ≫
        (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map
          (e.inverse.map (finiteGModuleCommGrpMap f).hom.hom.hom) =
      finiteLocallyConstantInternalPairing J e M N L' P' hP' := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  dsimp only [finiteLocallyConstantInternalPairing]
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    (congrArg (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map ?_)))
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    (congrArg e.inverse.map ?_)))
  exact finiteGModulePairing_comp_map f P hP P' hP' hPP'

/-- **The pairing of sections is natural in the first module**: evaluated on `E⁻¹(f)(a)` it is the
pairing attached to `P ∘ (f × 1)` evaluated on `a`. -/
theorem finiteLocallyConstantPairing_map_left (f : M' ⟶ M)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M'.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M'.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P' ((M'.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = P (f.hom.hom.hom.hom.hom a) b) (U : Cᵒᵖ)
    (a : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      M').obj.obj.obj U)
    (b : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      N).obj.obj.obj U) :
    finiteLocallyConstantPairing J e M N L P hP U
        (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.map
          f).hom.hom.app U a) b =
      finiteLocallyConstantPairing J e M' N L P' hP' U a b := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  simp only [finiteLocallyConstantPairing, AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply]
  rw [finiteLocallyConstantInverseObjIso_hom_app_map,
    sectionsPairing_map_left ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.map
      (e.inverse.mapCommGrp.map (finiteGModuleCommGrpMap f)))
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N L P hP)
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M' N L P' hP')
    (whiskerRight_finiteLocallyConstantInternalPairing J e f P hP P' hP' hPP')]

/-- **The pairing of sections is natural in the second module.** -/
theorem finiteLocallyConstantPairing_map_right (f : N' ⟶ N)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M.obj.obj.obj.V →+ N'.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N'.obj.obj.obj.V),
      P' ((M.obj.obj.obj.ρ g).hom a) ((N'.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = P a (f.hom.hom.hom.hom.hom b)) (U : Cᵒᵖ)
    (a : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      M).obj.obj.obj U)
    (b : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      N').obj.obj.obj U) :
    finiteLocallyConstantPairing J e M N L P hP U a
        (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.map
          f).hom.hom.app U b) =
      finiteLocallyConstantPairing J e M N' L P' hP' U a b := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  simp only [finiteLocallyConstantPairing, AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply]
  rw [finiteLocallyConstantInverseObjIso_hom_app_map,
    sectionsPairing_map_right ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.map
      (e.inverse.mapCommGrp.map (finiteGModuleCommGrpMap f)))
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N L P hP)
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N' L P' hP')
    (whiskerLeft_finiteLocallyConstantInternalPairing J e f P hP P' hP' hPP')]

/-- **The pairing of sections is natural in the target module.** -/
theorem map_finiteLocallyConstantPairing (f : L ⟶ L')
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L.obj.obj.obj.ρ g).hom (P a b))
    (P' : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L'.obj.obj.obj.V)
    (hP' : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P' ((M.obj.obj.obj.ρ g).hom a) ((N.obj.obj.obj.ρ g).hom b) =
        (L'.obj.obj.obj.ρ g).hom (P' a b))
    (hPP' : ∀ a b, P' a b = f.hom.hom.hom.hom.hom (P a b)) (U : Cᵒᵖ)
    (a : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      M).obj.obj.obj U)
    (b : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
      N).obj.obj.obj U) :
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.map
        f).hom.hom.app U (finiteLocallyConstantPairing J e M N L P hP U a b) =
      finiteLocallyConstantPairing J e M N L' P' hP' U a b := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  have hinj : Function.Injective ((finiteLocallyConstantInverseObjIso J e L').hom.hom.app U) :=
    (((sheafToPresheaf J AddCommGrpCat.{max u v}).mapIso
      (finiteLocallyConstantInverseObjIso J e L')).app U).addCommGroupIsoToAddEquiv.injective
  have hinv : ∀ (A : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory) z,
      (finiteLocallyConstantInverseObjIso J e A).hom.hom.app U
        ((finiteLocallyConstantInverseObjIso J e A).inv.hom.app U z) = z := fun A z =>
    (((sheafToPresheaf J AddCommGrpCat.{max u v}).mapIso
      (finiteLocallyConstantInverseObjIso J e A)).app U).addCommGroupIsoToAddEquiv.apply_symm_apply
      z
  apply hinj
  rw [finiteLocallyConstantInverseObjIso_hom_app_map]
  simp only [finiteLocallyConstantPairing, AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply]
  refine (congrArg (fun z => ((Sites.AbelianSheaf.externalSheaf J).map
      ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.map
      (e.inverse.mapCommGrp.map (finiteGModuleCommGrpMap f)))).hom.app U z)
    (hinv L _)).trans ((map_sectionsPairing
      ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.mapCommGrp.map
      (e.inverse.mapCommGrp.map (finiteGModuleCommGrpMap f)))
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N L P hP)
    (isBimultiplicative_finiteLocallyConstantInternalPairing J e M N L' P' hP')
    (finiteLocallyConstantInternalPairing_comp_map J e f P hP P' hP' hPP') U _ _).trans
    (hinv L' _).symm)

end Sheaf

end Stacks.ConstantSheaf
