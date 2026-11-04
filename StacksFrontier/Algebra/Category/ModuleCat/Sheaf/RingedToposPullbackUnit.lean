module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposTerminalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback of the structure sheaf along a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The pullback of
sheaves of modules `f^* = O_C ⊗_{f⁻¹O_D} f⁻¹(-)` of Stacks 03D6 part (2) carries the structure
sheaf of the target to the structure sheaf of the source, i.e. `f^*O_D ≅ O_C`.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`: the pullback of the structure
  sheaf of the target along a morphism of ringed topoi is the structure sheaf of the source.
-/

@[expose] public section

open CategoryTheory Limits Opposite CategoryTheory.Sheaf AlgebraicGeometry

universe w w' v u v' u'

namespace CategoryTheory.Functor.CorepresentableBy

/-- **The comparison morphism of two corepresenting objects, characterised.**  If `e` and `e'`
corepresent one functor `F` by `Y` and `Y'`, then composing the comparison isomorphism
`Y ≅ Y'` with a morphism `q : Y' ⟶ Z` is transporting `q` along the two bijections:

`(e.uniqueUpToIso e').hom ≫ q = e.homEquiv.symm (e'.homEquiv q)`. -/
@[ega "0 8.1.11" "partial"]
theorem uniqueUpToIso_hom_comp {C : Type u} [Category.{v} C] {F : C ⥤ Type v} {Y Y' : C}
    (e : F.CorepresentableBy Y) (e' : F.CorepresentableBy Y') {Z : C} (q : Y' ⟶ Z) :
    (e.uniqueUpToIso e').hom ≫ q = e.homEquiv.symm (e'.homEquiv q) := by
  rw [Functor.CorepresentableBy.uniqueUpToIso_hom]
  exact congrArg
    (fun α : coyoneda.obj (op Y') ⟶ coyoneda.obj (op Y) =>
      ConcreteCategory.hom (α.app Z) q)
    (Coyoneda.fullyFaithful.map_preimage _)

end CategoryTheory.Functor.CorepresentableBy

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Morphisms from the free sheaf of modules of rank one over `O_D` into the direct image of a
sheaf of `O_C`-modules `N` are the global sections of `N`, i.e. the morphisms from the terminal
sheaf into the underlying sheaf of sets of `N`. -/
noncomputable def pushforwardModulesUnitHomEquiv (f : RingedToposHom X Y)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
        (pushforwardModules f).obj N) ≃
      (⊤_ (Sheaf X.J (Type w)) ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) :=
  (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj N)).trans
    (f.toToposHom.pushforwardTerminalHomEquiv
      (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `pushforwardModulesUnitHomEquiv` is natural in the sheaf of modules. -/
lemma pushforwardModulesUnitHomEquiv_comp (f : RingedToposHom X Y)
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (q : N ⟶ N')
    (b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj N) :
    pushforwardModulesUnitHomEquiv f N' (b ≫ (pushforwardModules f).map q) =
      pushforwardModulesUnitHomEquiv f N b ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map q :=
  (congrArg (f.toToposHom.pushforwardTerminalHomEquiv
        (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N'))
      (unitTerminalHomEquiv_comp (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) b
        ((pushforwardModules f).map q))).trans
    (MorphismOfTopoi.pushforwardTerminalHomEquiv_comp f.toToposHom
      ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map q)
      (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N) b))

/-- The pullback of the free sheaf of modules of rank one over `O_D` corepresents the functor
corepresented by the free sheaf of modules of rank one over `O_C`, through the adjunction of
Stacks 03D7 and `pushforwardModulesUnitHomEquiv`. -/
noncomputable def pullbackModulesObjUnitCorepresentableBy (f : RingedToposHom X Y) :
    (coyoneda.obj
        (op (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).CorepresentableBy
      ((f.pullbackModules).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) where
  homEquiv {N} := ((pullbackAdjPushforwardModules f).homEquiv _ N).trans
    ((pushforwardModulesUnitHomEquiv f N).trans
      (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N).symm)
  homEquiv_comp {N N'} q h :=
    (congrArg (fun t ↦ (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N').symm
        (pushforwardModulesUnitHomEquiv f N' t))
      ((pullbackAdjPushforwardModules f).homEquiv_naturality_right h q)).trans
      ((congrArg (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N').symm
          (pushforwardModulesUnitHomEquiv_comp f q
            ((pullbackAdjPushforwardModules f).homEquiv _ N h))).trans
        (unitTerminalHomEquiv_symm_comp (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (pushforwardModulesUnitHomEquiv f N
            ((pullbackAdjPushforwardModules f).homEquiv _ N h)) q))

/-- **The pullback of the structure sheaf is the structure sheaf**: for a morphism of ringed
topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` the pullback `f^*O_D = O_C ⊗_{f⁻¹O_D} f⁻¹O_D` of
Stacks 03D6 part (2) is canonically isomorphic to `O_C`, both sheaves of modules being read as
the free module of rank one over the respective structure sheaf. -/
noncomputable def pullbackModulesObjUnitIso (f : RingedToposHom X Y) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      (f.pullbackModules).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Functor.CorepresentableBy.uniqueUpToIso
    (Functor.CorepresentableBy.coyoneda
      (op (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (pullbackModulesObjUnitCorepresentableBy f)

/-- **The inverse image of the structure sheaf, identified by its universal property**, for a
morphism of ringed topoi: composing the comparison `1_{O_C} ⟶ f^*1_{O_D}` with a morphism out
of `f^*1_{O_D}` gives the corepresentability bijection of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy`. -/
theorem pullbackModulesObjUnitIso_hom_comp (f : RingedToposHom X Y)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (q : f.pullbackModules.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ N) :
    (pullbackModulesObjUnitIso f).hom ≫ q
      = (pullbackModulesObjUnitCorepresentableBy f).homEquiv q :=
  Functor.CorepresentableBy.uniqueUpToIso_hom_comp _ _ q

end Stacks.Sheaves.RingedToposModules

end
