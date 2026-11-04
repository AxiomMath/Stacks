module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue

/-!
# Recognizing the unit comparison `f^*O_D ≅ O_C` by its transpose

For a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` in the sense of
Stacks 01D3, the transpose along `f^* ⊣ f_*` of the explicit comparison
`f^*O_D ⟶ O_C` (Stacks 03LU) is, on underlying sheaves of sets, the structure map
`f♯ : O_D ⟶ f_*O_C`. Consequently a morphism `f^*A ⟶ B` between modules isomorphic to the
structure sheaves is invertible as soon as its transpose is `f♯` on underlying sheaves of sets.

## Main results

* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_homEquiv_pullbackModulesUnitIso_inv`:
  the transpose of the unit comparison is `f♯` on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.isIso_homEquiv_symm_of_moduleSheafFunctor_map`: a morphism
  `f^*A ⟶ B` whose transpose is `f♯`, read through isomorphisms `O_D ≅ A` and `B ≅ O_C`, is
  invertible; `isIso_homEquiv_symm_of_eq_unit` is the variant for modules equal to the
  structure sheaves.
* `AlgebraicGeometry.RingedToposHom.isIso_homEquiv_symm_iff_of_eq`: transposes along equal
  morphisms of maps with the same underlying sheaf map are invertible together.
-/

@[expose] public section

open CategoryTheory

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- **The transpose of the unit comparison `f^*O_D ⟶ O_C` is the structure map**, on
underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_homEquiv_pullbackModulesUnitIso_inv :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        (f.pullbackAdjPushforwardModules.homEquiv _ _
          (Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso f.toModulesHom).inv) =
      (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing := by
  refine (congrArg
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
    (Adjunction.homEquiv_ofNatIsoRight_apply
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
      f.toModulesPushforwardIso
      (Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso f.toModulesHom).inv)).trans ?_
  rw [Functor.map_comp,
    Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv,
    ← f.toModulesHom.fSharp_adjunct]
  exact Category.comp_id _

/-- **A morphism `f^*A ⟶ B` whose transpose is the structure map is invertible.** If `a : O_D ≅ A`
and `b : B ≅ O_C` and the transpose `β : A ⟶ f_*B` satisfies `a ≫ β ≫ f_*b = f♯` on underlying
sheaves of sets, then the morphism `f^*A ⟶ B` adjunct to `β` is an
isomorphism: it is the unit comparison of Stacks 03LU conjugated by the two isomorphisms. -/
theorem isIso_homEquiv_symm_of_moduleSheafFunctor_map
    {A : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
    {B : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⟶ A)
    (ha : IsIso a)
    (b : B ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (hb : IsIso b)
    (β : A ⟶ f.pushforwardModules.obj B)
    (hβ : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        (a ≫ β ≫ f.pushforwardModules.map b) =
      (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing) :
    IsIso ((f.pullbackAdjPushforwardModules.homEquiv A B).symm β) := by
  have := ha
  have := hb
  have key : f.toModulesHom.pullbackModules.map a ≫
      (f.pullbackAdjPushforwardModules.homEquiv A B).symm β ≫
      b = (Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso f.toModulesHom).inv := by
    apply (f.pullbackAdjPushforwardModules.homEquiv _ _).injective
    apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    rw [moduleSheafFunctor_map_homEquiv_pullbackModulesUnitIso_inv,
      f.pullbackAdjPushforwardModules.homEquiv_naturality_left,
      f.pullbackAdjPushforwardModules.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact hβ
  have hk : IsIso (f.toModulesHom.pullbackModules.map a ≫
      (f.pullbackAdjPushforwardModules.homEquiv A B).symm β ≫ b) := by
    have := (Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso f.toModulesHom).isIso_inv
    rw [key]
    exact this
  have e : (f.pullbackAdjPushforwardModules.homEquiv A B).symm β =
      inv (f.toModulesHom.pullbackModules.map a) ≫ (f.toModulesHom.pullbackModules.map a ≫
        (f.pullbackAdjPushforwardModules.homEquiv A B).symm β ≫ b) ≫ inv b := by
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- **A morphism `f^*A ⟶ B` between modules that are the structure sheaves is invertible when
its transpose is the structure map.** The variant of
`isIso_homEquiv_symm_of_moduleSheafFunctor_map` for modules equal to the structure sheaves, the
transpose being compared with `f♯` as a heterogeneous equality. -/
theorem isIso_homEquiv_symm_of_eq_unit
    {A : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
    {B : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (hA : A = SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (hB : B = SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (β : A ⟶ f.pushforwardModules.obj B)
    (hβ : (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map β ≍
      (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing) :
    IsIso ((f.pullbackAdjPushforwardModules.homEquiv A B).symm β) := by
  subst hA hB
  refine f.isIso_homEquiv_symm_of_moduleSheafFunctor_map (𝟙 _) inferInstance (𝟙 _)
    inferInstance β ?_
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact eq_of_heq hβ

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Transposes along equal morphisms of ringed topoi, of morphisms with the same underlying
morphism of sheaves of sets, are invertible together. -/
theorem isIso_homEquiv_symm_iff_of_eq {g : RingedToposHom X Y} (hg : f = g)
    {A A' : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
    (hA : A = A')
    {B B' : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (hB : B = B')
    (β : A ⟶ f.pushforwardModules.obj B) (β' : A' ⟶ g.pushforwardModules.obj B')
    (h : (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map β ≍
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map β') :
    IsIso ((f.pullbackAdjPushforwardModules.homEquiv A B).symm β) ↔
      IsIso ((g.pullbackAdjPushforwardModules.homEquiv A' B').symm β') := by
  subst hg hA hB
  obtain rfl := Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor (eq_of_heq h)
  rfl

end AlgebraicGeometry.RingedToposHom

end
