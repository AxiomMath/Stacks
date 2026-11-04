module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtension

/-!
# Presheaves of section modules over a restricted algebra

Let `F : C' ⥤ C` be a functor of chaotic sites, `(A, d)` a sheaf of differential graded algebras
on `C` and `(A', d)` its restriction to `C'`. The algebra of sections `A'(U')` is the algebra of
sections `A(F U')`, through the isomorphism
`SheafOfModules.DifferentialGradedAlgebra.restrictSectionHom`.
Reading modules through it identifies presheaves of section modules over `A'` with presheaves of
section modules along `F`: this file gives the equivalence.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.toAlong`: a presheaf of section
  modules over `A'`, read along `F`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.ofAlong`: a presheaf of section
  modules along `F`, read over `A'`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.alongEquivalence`: the two are
  mutually inverse equivalences.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf
open DifferentialGradedModule (restrictScalars restrictScalarsHom restrictScalarsFunctor
  restrictScalarsAlongSquare)
open DifferentialGraded.Bimodule (restrictScalarsInverseIso)

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace DifferentialGradedModule

/-- A family of isomorphisms of the modules of two presheaves of section modules commuting with
the restriction homomorphisms is an isomorphism of presheaves of section modules. -/
def SectionSystem.isoMk {C : Type u} [Category.{u} C]
    [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {X Y : SectionSystem B} (e : ∀ U, X.obj U ≅ Y.obj U)
    (h : ∀ {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M),
      Y.restrFun a ((e V).hom.toFun x) = (e U).hom.toFun (X.restrFun a x)) : X ≅ Y where
  hom := ⟨fun U => (e U).hom, fun a x => h a x⟩
  inv := ⟨fun U => (e U).inv, fun {U V} a y => by
    have h1 : ∀ z, (e U).hom.toFun ((e U).inv.toFun z) = z := fun z =>
      congrArg (fun g => g.toFun z) (e U).inv_hom_id
    have h2 : ∀ z, (e V).hom.toFun ((e V).inv.toFun z) = z := fun z =>
      congrArg (fun g => g.toFun z) (e V).inv_hom_id
    have h3 : ∀ z, (e U).inv.toFun ((e U).hom.toFun z) = z := fun z =>
      congrArg (fun g => g.toFun z) (e U).hom_inv_id
    have key := h a ((e V).inv.toFun y)
    rw [h2] at key
    rw [key, h3]⟩
  hom_inv_id := SectionSystem.hom_ext fun U => (e U).hom_inv_id
  inv_hom_id := SectionSystem.hom_ext fun U => (e U).inv_hom_id

namespace ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] {F : C' ⥤ C}
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-- A family of isomorphisms of the modules of two presheaves of section modules along `F`
commuting with the restriction homomorphisms is an isomorphism. -/
def AlongSystem.isoMk {X Y : AlongSystem F A} (e : ∀ U', X.obj U' ≅ Y.obj U')
    (h : ∀ {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (x : (X.obj V').M),
      Y.restrFun a ((e V').hom.toFun x) = (e U').hom.toFun (X.restrFun a x)) : X ≅ Y where
  hom := ⟨fun U' => (e U').hom, fun a x => h a x⟩
  inv := ⟨fun U' => (e U').inv, fun {U' V'} a y => by
    have h2 : ∀ z, (e V').hom.toFun ((e V').inv.toFun z) = z := fun z =>
      congrArg (fun g => g.toFun z) (e V').inv_hom_id
    have h3 : ∀ z, (e U').inv.toFun ((e U').hom.toFun z) = z := fun z =>
      congrArg (fun g => g.toFun z) (e U').hom_inv_id
    have key := h a ((e V').inv.toFun y)
    rw [h2] at key
    rw [key, h3]⟩
  hom_inv_id := AlongSystem.hom_ext fun U' => (e U').hom_inv_id
  inv_hom_id := AlongSystem.hom_ext fun U' => (e U').inv_hom_id

/-! ### From presheaves of section modules over `A'` to presheaves along `F` -/

section ToAlong

variable (X X' X'' : SectionSystem (A.restrict F))

/-- A presheaf of section modules over `A'`, read along `F`: over `U'` it is `X(U')` read over
`A(F U')`. -/
def toAlongObj : AlongSystem F A where
  obj U' := _root_.DifferentialGradedModule.restrictScalars (A.restrictSectionInv F U') (X.obj U')
  restr {U' V'} a := restrictScalarsAlongSquare (A.restrictSectionInv F V')
    (A.restrictSectionInv F U') (A.sectionRestriction (F.op.map a))
    ((A.restrict F).sectionRestriction a)
    (fun b => (DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A a b).symm)
    (X.restr a)
  restr_id U' x :=
    DifferentialGradedModule.restrictScalarsAlongSquare_apply_eq_self
      (A.restrictSectionInv F U') (A.sectionRestriction (F.op.map (𝟙 U')))
      ((A.restrict F).sectionRestriction (𝟙 U'))
      (fun b => (DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A (𝟙 U')
        b).symm) (X.restr (𝟙 U')) (X.restr_id U') x
  restr_comp {U' V' W'} a b x :=
    DifferentialGradedModule.restrictScalarsAlongSquare_apply_comp
      (A.restrictSectionInv F W') (A.restrictSectionInv F V') (A.restrictSectionInv F U')
      (A.sectionRestriction (F.op.map b)) (A.sectionRestriction (F.op.map a))
      (A.sectionRestriction (F.op.map (b ≫ a))) ((A.restrict F).sectionRestriction b)
      ((A.restrict F).sectionRestriction a) ((A.restrict F).sectionRestriction (b ≫ a))
      (fun c => (DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A b c).symm)
      (fun c => (DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A a c).symm)
      (fun c => (DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A (b ≫ a)
        c).symm)
      (X.restr b) (X.restr a) (X.restr (b ≫ a)) (X.restr_comp a b) x

variable {X X' X''}

/-- A morphism of presheaves of section modules over `A'`, read along `F`. -/
def toAlongMap (f : X ⟶ X') : toAlongObj X ⟶ toAlongObj X' where
  app U' :=
    _root_.DifferentialGradedModule.restrictScalarsHom (A.restrictSectionInv F U') (f.app U')
  naturality {U' V'} a x :=
    DifferentialGradedModule.restrictScalarsAlongSquare_naturality
      (A.restrictSectionInv F V') (A.restrictSectionInv F U')
      (A.sectionRestriction (F.op.map a)) ((A.restrict F).sectionRestriction a)
      (fun c => (DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A a c).symm)
      (X.restr a) (X'.restr a) (f.app V') (f.app U') (fun y => f.naturality a y) x

variable (F A) in
/-- **Reading presheaves of section modules over `A'` along `F`.** -/
def toAlong : SectionSystem (A.restrict F) ⥤ AlongSystem F A where
  obj X := toAlongObj X
  map f := toAlongMap f
  map_id X₀ := AlongSystem.hom_ext fun U' =>
    (restrictScalarsFunctor (A.restrictSectionInv F U')).map_id (X₀.obj U')
  map_comp f g := AlongSystem.hom_ext fun U' =>
    (restrictScalarsFunctor (A.restrictSectionInv F U')).map_comp (f.app U') (g.app U')

end ToAlong

/-! ### From presheaves along `F` to presheaves of section modules over `A'` -/

section OfAlong

variable (Z Z' : AlongSystem F A)

/-- A presheaf of section modules along `F`, read over `A'`: over `U'` it is `Z(U')` read over
`A'(U')`. -/
def ofAlongObj : SectionSystem (A.restrict F) where
  obj U' := _root_.DifferentialGradedModule.restrictScalars (A.restrictSectionHom F U') (Z.obj U')
  restr {U' V'} a := restrictScalarsAlongSquare (A.restrictSectionHom F V')
    (A.restrictSectionHom F U') ((A.restrict F).sectionRestriction a)
    (A.sectionRestriction (F.op.map a))
    (fun b => (DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A a b).symm)
    (Z.restr a)
  restr_id U' x :=
    DifferentialGradedModule.restrictScalarsAlongSquare_apply_eq_self
      (A.restrictSectionHom F U') ((A.restrict F).sectionRestriction (𝟙 U'))
      (A.sectionRestriction (F.op.map (𝟙 U')))
      (fun b => (DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A (𝟙 U')
        b).symm) (Z.restr (𝟙 U')) (Z.restr_id U') x
  restr_comp {U' V' W'} a b x :=
    DifferentialGradedModule.restrictScalarsAlongSquare_apply_comp
      (A.restrictSectionHom F W') (A.restrictSectionHom F V') (A.restrictSectionHom F U')
      ((A.restrict F).sectionRestriction b) ((A.restrict F).sectionRestriction a)
      ((A.restrict F).sectionRestriction (b ≫ a)) (A.sectionRestriction (F.op.map b))
      (A.sectionRestriction (F.op.map a)) (A.sectionRestriction (F.op.map (b ≫ a)))
      (fun c => (DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A b c).symm)
      (fun c => (DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A a c).symm)
      (fun c => (DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A (b ≫ a)
        c).symm)
      (Z.restr b) (Z.restr a) (Z.restr (b ≫ a)) (Z.restr_comp a b) x

variable {Z Z'}

/-- A morphism of presheaves of section modules along `F`, read over `A'`. -/
def ofAlongMap (f : Z ⟶ Z') : ofAlongObj Z ⟶ ofAlongObj Z' where
  app U' :=
    _root_.DifferentialGradedModule.restrictScalarsHom (A.restrictSectionHom F U') (f.app U')
  naturality {U' V'} a x :=
    DifferentialGradedModule.restrictScalarsAlongSquare_naturality
      (A.restrictSectionHom F V') (A.restrictSectionHom F U')
      ((A.restrict F).sectionRestriction a) (A.sectionRestriction (F.op.map a))
      (fun c => (DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A a c).symm)
      (Z.restr a) (Z'.restr a) (f.app V') (f.app U') (fun y => f.naturality a y) x

variable (F A) in
/-- **Reading presheaves of section modules along `F` over `A'`.** -/
def ofAlong : AlongSystem F A ⥤ SectionSystem (A.restrict F) where
  obj Z := ofAlongObj Z
  map f := ofAlongMap f
  map_id Z₀ := SectionSystem.hom_ext fun U' =>
    (restrictScalarsFunctor (A.restrictSectionHom F U')).map_id (Z₀.obj U')
  map_comp f g := SectionSystem.hom_ext fun U' =>
    (restrictScalarsFunctor (A.restrictSectionHom F U')).map_comp (f.app U') (g.app U')

end OfAlong

/-! ### The equivalence -/

/-- The unit of the equivalence: `X(U') ≅ (X(U') read over A(F U')) read over A'(U')`. -/
def alongUnitIso (X : SectionSystem (A.restrict F)) :
    X ≅ (ofAlong F A).obj ((toAlong F A).obj X) :=
  SectionSystem.isoMk (fun U' => restrictScalarsInverseIso (A.restrictSectionHom F U')
      (A.restrictSectionInv F U') (A.restrictSectionInv_hom F U') (X.obj U'))
    (fun _ _ => rfl)

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- The counit of the equivalence: `(Z(U') read over A'(U')) read over A(F U') ≅ Z(U')`. -/
def alongCounitIso (Z : AlongSystem F A) :
    (toAlong F A).obj ((ofAlong F A).obj Z) ≅ Z :=
  (AlongSystem.isoMk (fun U' => restrictScalarsInverseIso (A.restrictSectionInv F U')
      (A.restrictSectionHom F U') (A.restrictSectionHom_inv F U') (Z.obj U'))
    (fun _ _ => rfl)).symm

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
variable (F A) in
/-- **Presheaves of section modules over the restriction `A'` are presheaves of section modules
along `F`.** -/
def alongEquivalence : SectionSystem (A.restrict F) ≌ AlongSystem F A :=
  CategoryTheory.Equivalence.mk (toAlong F A) (ofAlong F A)
    (NatIso.ofComponents alongUnitIso fun _ =>
      SectionSystem.hom_ext fun _ => _root_.DifferentialGradedModule.Hom.ext rfl)
    (NatIso.ofComponents alongCounitIso fun _ =>
      AlongSystem.hom_ext fun _ => _root_.DifferentialGradedModule.Hom.ext
        (DFunLike.ext _ _ fun _ => rfl))

end ChaoticExtension

end DifferentialGradedModule

end SheafOfModules

end
