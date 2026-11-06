module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Center.Linear
public import StacksFrontier.CategoryTheory.Center.Shift

/-!
# Complexes of abelian groups with a central action of a ring, as complexes of modules

Let `A` be a ring. A ring map `ρ : A →+* End K` into the endomorphisms of a complex `K` of
abelian groups makes every term of `K` an `A`-module, and the differentials of `K` are
`A`-linear because the endomorphisms `ρ a` are morphisms of complexes; this is
`Stacks.CenterLift.liftComplex`, a complex of `A`-modules whose underlying complex of abelian
groups is `K` itself.

The typical source of such a ring map is the centre of a preadditive category `C`: a ring map
`ρ : A →+* CatCenter C` and an additive functor `G : C ⥤ HomologicalComplex Ab c` give, at
each object `X`, the ring map `a ↦ G.map ((ρ a).app X)`. Every `G.map f` commutes with these
actions, by naturality of the central elements, so `G` lifts to a functor
`Stacks.CenterLift.liftFunctor G ρ` into complexes of `A`-modules, and every natural
transformation `G ⟶ G'` of such functors lifts as well. A morphism of lifted complexes is a
quasi-isomorphism exactly when the underlying morphism of complexes of abelian groups is one.

For a sheaf of rings `O`, the centre of the category of complexes of `O`-modules receives
`Γ(X, O)` (multiplication by a global section), and the construction of this file applied to
sections, to Čech complexes or to any additive functor built from sections produces their
`Γ(X, O)`-linear, and by composition `A`-linear, versions at once.

## Main definitions

* `Stacks.CenterLift.liftComplex`: a complex of abelian groups with a ring map into its
  endomorphisms, as a complex of modules.
* `Stacks.CenterLift.liftHom`: a morphism of complexes commuting with the two actions, as a
  morphism of complexes of modules.
* `Stacks.CenterLift.liftFunctor` and `Stacks.CenterLift.liftNatTrans`: the same, functorially,
  for an additive functor out of a category with a ring map into its centre.
* `Stacks.CenterLift.catCenterHomologicalComplex`: a central element of `C` acting termwise on
  complexes, as a ring map into the centre of the category of complexes.

## Main results

* `Stacks.CenterLift.liftFunctorForgetIso`: forgetting the module structures recovers `G`.
* `Stacks.CenterLift.quasiIso_liftFunctor_map_iff` and
  `Stacks.CenterLift.quasiIso_liftNatTrans_app_iff`: quasi-isomorphisms are detected on the
  underlying complexes of abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u t s

namespace Stacks.CenterLift

variable {A : Type w} [Ring A] {ι : Type s} {c : ComplexShape ι}

section Complex

variable (K : HomologicalComplex AddCommGrpCat.{v} c) (ρ : A →+* End K)

/-- The action of `A` on a term of a complex of abelian groups with a ring map
`A →+* End K`: `a` acts on `K.X i` by the `i`-th component of `ρ a`. -/
@[instance_reducible]
def termSMul (i : ι) : SMul A (K.X i) where
  smul a x := ((ρ a).asHom.f i).hom x

/-- Under `termSMul K ρ i`, `a • x` is the image of `x` under the `i`-th component of `ρ a`. -/
theorem termSMul_smul (i : ι) (a : A) (x : K.X i) :
    letI := termSMul K ρ i
    a • x = ((ρ a).asHom.f i).hom x :=
  rfl

/-- The `A`-module structure on a term of a complex of abelian groups with a ring map
`A →+* End K`. -/
@[instance_reducible]
def termModule (i : ι) : Module A (K.X i) :=
  letI := termSMul K ρ i
  { one_smul x := by
      rw [termSMul_smul, map_one]
      rfl
    mul_smul a b x := by
      rw [termSMul_smul, termSMul_smul, termSMul_smul, map_mul]
      rfl
    smul_zero a := map_zero _
    smul_add a x y := map_add _ x y
    add_smul a b x := by
      rw [termSMul_smul, termSMul_smul, termSMul_smul, map_add]
      rfl
    zero_smul x := by
      rw [termSMul_smul, map_zero]
      rfl }

/-- Under `termModule K ρ i`, `a • x` is the image of `x` under the `i`-th component of
`ρ a`. -/
theorem termModule_smul (i : ι) (a : A) (x : K.X i) :
    letI := termModule K ρ i
    a • x = ((ρ a).asHom.f i).hom x :=
  rfl

/-- The term `K.X i`, as an `A`-module. -/
def liftX (i : ι) : ModuleCat.{v} A :=
  letI := termModule K ρ i
  ModuleCat.of A (K.X i)

variable {K ρ} in
/-- An additive map between terms commuting with the actions, as a morphism of `A`-modules. -/
def liftXHom {L : HomologicalComplex AddCommGrpCat.{v} c} {σ : A →+* End L} {i j : ι}
    (g : K.X i ⟶ L.X j) (hg : ∀ a, (ρ a).asHom.f i ≫ g = g ≫ (σ a).asHom.f j) :
    liftX K ρ i ⟶ liftX L σ j :=
  letI := termModule K ρ i
  letI := termModule L σ j
  ModuleCat.ofHom
    { toFun := g.hom
      map_add' := map_add _
      map_smul' := fun a x ↦ ConcreteCategory.congr_hom (hg a) x }

/-- **A complex of abelian groups with a ring map `A →+* End K`, as a complex of
`A`-modules.** The terms are those of `K` with `a` acting through `ρ a`, and the differentials
are those of `K`. -/
def liftComplex : HomologicalComplex (ModuleCat.{v} A) c where
  X i := liftX K ρ i
  d i j := liftXHom (K.d i j) fun a ↦ ((ρ a).asHom.comm i j)
  shape i j h := by
    ext x
    exact ConcreteCategory.congr_hom (K.shape i j h) x
  d_comp_d' i j k _ _ := by
    ext x
    exact ConcreteCategory.congr_hom (K.d_comp_d i j k) x

variable {K ρ} in
/-- A morphism of complexes of abelian groups commuting with the two actions, as a morphism of
complexes of `A`-modules. -/
def liftHom {L : HomologicalComplex AddCommGrpCat.{v} c} {σ : A →+* End L} (φ : K ⟶ L)
    (hφ : ∀ a, (ρ a).asHom ≫ φ = φ ≫ (σ a).asHom) : liftComplex K ρ ⟶ liftComplex L σ where
  f i := liftXHom (φ.f i) fun a ↦ by
    rw [← HomologicalComplex.comp_f, hφ a, HomologicalComplex.comp_f]
  comm' i j _ := by
    ext x
    exact ConcreteCategory.congr_hom (φ.comm i j) x

/-- Forgetting the module structures of `liftComplex K ρ` gives back `K`. -/
def liftComplexForgetIso :
    ((forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).mapHomologicalComplex c).obj
      (liftComplex K ρ) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl)

end Complex

section Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (G : C ⥤ HomologicalComplex AddCommGrpCat.{t} c) [G.Additive] (ρ : A →+* CatCenter C)

/-- The ring map `A →+* End (G X)`: `a` acts on `G X` through the image under `G` of the
component at `X` of the central element `ρ a`. -/
def endRingHom (X : C) : A →+* End (G.obj X) where
  toFun a := .of (G.map ((ρ a).app X))
  map_one' := by
    ext1
    rw [map_one]
    exact G.map_id X
  map_mul' a b := by
    ext1
    rw [map_mul, CatCenter.mul_app', G.map_comp]
    rfl
  map_zero' := by
    ext1
    rw [map_zero]
    exact G.map_zero X X
  map_add' a b := by
    ext1
    rw [map_add, CatCenter.app_add, G.map_add]
    rfl

/-- `endRingHom G ρ X a` is `G.map ((ρ a).app X)`. -/
theorem endRingHom_apply (X : C) (a : A) : endRingHom G ρ X a = .of (G.map ((ρ a).app X)) := rfl

/-- The action of `a` on `G X` and `G Y` commutes with `G.map f` for every `f : X ⟶ Y`. -/
theorem endRingHom_comm {X Y : C} (f : X ⟶ Y) (a : A) :
    (endRingHom G ρ X a).asHom ≫ G.map f = G.map f ≫ (endRingHom G ρ Y a).asHom := by
  rw [endRingHom_apply, endRingHom_apply, ← G.map_comp, ← G.map_comp]
  exact congrArg G.map ((ρ a).naturality f).symm

/-- Quasi-isomorphisms of module complexes are detected after forgetting, up to isomorphism. -/
private theorem quasiIso_iff_of_forget_iso {P Q : HomologicalComplex (ModuleCat.{t} A) c}
    {K L : HomologicalComplex AddCommGrpCat.{t} c} (f : P ⟶ Q) (g : K ⟶ L)
    (e : ((forget₂ (ModuleCat.{t} A) AddCommGrpCat.{t}).mapHomologicalComplex c).obj P ≅ K)
    (e' : ((forget₂ (ModuleCat.{t} A) AddCommGrpCat.{t}).mapHomologicalComplex c).obj Q ≅ L)
    (w : e.hom ≫ g =
      ((forget₂ (ModuleCat.{t} A) AddCommGrpCat.{t}).mapHomologicalComplex c).map f ≫ e'.hom) :
    QuasiIso f ↔ QuasiIso g := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (forget₂ (ModuleCat.{t} A) AddCommGrpCat.{t})]
  exact quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk e e' w)

/-- **The lift of an additive functor along a central action.** For a ring map
`ρ : A →+* CatCenter C` and an additive functor `G` into complexes of abelian groups, the
functor sending `X` to `G X` with `a` acting through `G.map ((ρ a).app X)`. -/
@[simps obj]
def liftFunctor : C ⥤ HomologicalComplex (ModuleCat.{t} A) c where
  obj X := liftComplex (G.obj X) (endRingHom G ρ X)
  map f := liftHom (G.map f) (endRingHom_comm G ρ f)
  map_id X := by
    ext i x
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (G.map_id X) i) x
  map_comp f g := by
    ext i x
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (G.map_comp f g) i) x

/-- On elements, the components of `(liftFunctor G ρ).map f` are those of `G.map f`. -/
theorem liftFunctor_map_f_apply {X Y : C} (f : X ⟶ Y) (i : ι) (x : (G.obj X).X i) :
    ((liftFunctor G ρ).map f).f i x = ((G.map f).f i).hom x :=
  rfl

/-- The scalar action on a term of `liftFunctor G ρ` is the action through `G` of the central
element. -/
theorem liftFunctor_smul (X : C) (i : ι) (a : A) (x : ((liftFunctor G ρ).obj X).X i) :
    a • x = ((G.map ((ρ a).app X)).f i).hom x :=
  rfl

/-- The functor `liftFunctor G ρ` is additive. -/
instance : (liftFunctor G ρ).Additive where
  map_add {X Y f g} := by
    ext i x
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (G.map_add (f := f) (g := g)) i) x

/-- Forgetting the module structures, `liftFunctor G ρ` is `G`. -/
def liftFunctorForgetIso :
    liftFunctor G ρ ⋙ (forget₂ (ModuleCat.{t} A) AddCommGrpCat.{t}).mapHomologicalComplex c ≅
      G :=
  NatIso.ofComponents (fun X ↦ liftComplexForgetIso (G.obj X) (endRingHom G ρ X))
    (fun f ↦ by ext; rfl)

/-- **Quasi-isomorphisms of lifted complexes are detected on the underlying complexes.** -/
theorem quasiIso_liftFunctor_map_iff {X Y : C} (f : X ⟶ Y) :
    QuasiIso ((liftFunctor G ρ).map f) ↔ QuasiIso (G.map f) := by
  exact quasiIso_iff_of_forget_iso _ _ ((liftFunctorForgetIso G ρ).app X)
    ((liftFunctorForgetIso G ρ).app Y) ((liftFunctorForgetIso G ρ).hom.naturality f).symm

variable {G} in
/-- A natural transformation between additive functors into complexes of abelian groups lifts
to their lifts along a central action. -/
@[simps]
def liftNatTrans {G' : C ⥤ HomologicalComplex AddCommGrpCat.{t} c} [G'.Additive]
    (η : G ⟶ G') : liftFunctor G ρ ⟶ liftFunctor G' ρ where
  app X := liftHom (η.app X) fun a ↦ η.naturality ((ρ a).app X)
  naturality X Y f := by
    ext i x
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (η.naturality f) i) x

/-- On elements, the components of `(liftNatTrans ρ η).app X` are those of `η.app X`. -/
theorem liftNatTrans_app_f_apply {G' : C ⥤ HomologicalComplex AddCommGrpCat.{t} c}
    [G'.Additive] (η : G ⟶ G') (X : C) (i : ι) (x : (G.obj X).X i) :
    ((liftNatTrans ρ η).app X).f i x = ((η.app X).f i).hom x :=
  rfl

/-- **Quasi-isomorphisms are detected on the underlying complexes**, for the components of a
lifted natural transformation. -/
theorem quasiIso_liftNatTrans_app_iff {G' : C ⥤ HomologicalComplex AddCommGrpCat.{t} c}
    [G'.Additive] (η : G ⟶ G') (X : C) :
    QuasiIso ((liftNatTrans ρ η).app X) ↔ QuasiIso (η.app X) := by
  exact quasiIso_iff_of_forget_iso _ _ ((liftFunctorForgetIso G ρ).app X)
    ((liftFunctorForgetIso G' ρ).app X) rfl

end Functor

section Complexes

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **The termwise action of the centre of `C` on complexes**, as a ring map into the centre
of the category of complexes. -/
def catCenterHomologicalComplex : CatCenter C →+* CatCenter (HomologicalComplex C c) where
  toFun z := z.homologicalComplex c
  map_one' := by ext K i; rfl
  map_mul' _ _ := by ext K i; rfl
  map_zero' := by ext K i; rfl
  map_add' _ _ := by ext K i; rfl

end Complexes

end Stacks.CenterLift

end
