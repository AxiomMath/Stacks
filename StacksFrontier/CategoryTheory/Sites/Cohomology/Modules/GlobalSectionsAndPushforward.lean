module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage

/-!
# Global sections are unchanged by a pushforward of modules

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. Global sections of a
sheaf of `O_C`-modules `N` are the same thing as global sections of its pushforward `f_*N`:

`Γ(D, f_*N) = Γ(C, N)`.

The two sides are modules over different rings — `Γ(D, O_D)` and `Γ(C, O_C)` — so the comparison
is an isomorphism after restricting scalars along the ring map
`globalSectionsRingHom f : Γ(D, O_D) ⟶ Γ(C, O_C)` induced by the structure morphism. The
resulting natural isomorphism `globalSectionsPushforwardIso` is the factorisation
`Γ(C, -) = Γ(D, -) ∘ f_*` of the functor of global sections, which is what makes the Leray
spectral sequence of a morphism of ringed topoi a Grothendieck spectral sequence.

## Main definitions

* `Stacks.Cohomology.SiteModules.unitEnd` and `unitEndEquiv`: a compatible family of sections of
  a sheaf of rings `R`, read as an endomorphism of the free sheaf of `R`-modules of rank one, and
  the bijection between the two.
* `Stacks.Cohomology.SiteModules.globalSectionsRingHom`: the ring map
  `Γ(D, O_D) ⟶ Γ(C, O_C)` induced on global sections by the structure morphism of a morphism of
  ringed topoi.
* `Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv`: the bijection
  `Γ(D, f_*N) ≃ Γ(C, N)`.

## Main results

* `Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`: **global sections are unchanged by
  a pushforward**, as an isomorphism of functors
  `f_* ⋙ Γ(D, -) ≅ Γ(C, -) ⋙ restrictScalars (Γ(D, O_D) ⟶ Γ(C, O_C))`.
* `Stacks.Cohomology.SiteModules.globalSectionsPushforwardIsoGeneral`: the same, for ringed
  topoi whose object universes differ.
* `Stacks.Cohomology.SiteModules.globalSectionsPushforwardForgetIso`: the same comparison read in
  abelian groups, where no restriction of scalars is needed.
* The pushforward of sheaves of modules along a morphism of ringed topoi is additive by
  `Stacks.Sheaves.RingedToposModules.additive_pushforwardModules`, and the direct image of
  Stacks 03D1 by `Stacks.Sheaves.ToposPushforward.additive_pushforwardModuleFunctor`; both are
  instances of `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdditivityOfDirectAndInverseImage.lean`.

## Implementation notes

The pushforward along a morphism of topoi is an abstract right adjoint, so `Γ(D, f_*N)` has no
description in terms of sections of `N`; the whole comparison is therefore made through hom-sets
out of the free module of rank one, which is what `Mathlib`'s `SheafOfModules.unitHomEquiv`
identifies with global sections. Scalar multiplication by a global section of `R` corresponds
under that identification to precomposition with the endomorphism `unitEnd` of the free module of
rank one, and composition of such endomorphisms corresponds to multiplication of scalars. That is
what produces the ring map on global sections: it is the endomorphism of the free `O_C`-module of
rank one obtained by transporting `unitEnd` across the pullback of the free `O_D`-module of rank
one, which is the free `O_C`-module of rank one by
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`.

Additivity of the comparison is additivity of the adjunction bijection, which needs the
pushforward of modules to be an additive functor. That is proved here from the single
computation that the underlying morphism of sheaves of sets of a sum of morphisms of sheaves of
modules is the sum transported along the addition morphism of the target.

The object universes of the two sites and the two module universes are independent for the ring
map `globalSectionsRingHom` and for the bijection `globalSectionsPushforwardEquiv`. The
isomorphism of functors forces `max u' w' = max u w`, because restriction of scalars does not
change the module universe. `globalSectionsPushforwardIsoGeneral` states it at the universes
`C ∈ Type (max u t)`, `D ∈ Type (max u s)` with sections in `Type (max w t s)`, which covers ringed
topoi of different object universes, and `globalSectionsPushforwardIso` is its case of equal
object and module universes, the universes of the morphisms of the two sites remaining
independent in both.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor Opposite
open AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Cohomology.SiteModules

universe w w' v u v' u'

/-! ### Global sections as endomorphisms of the free module of rank one -/

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- Multiplication on the right by a compatible family of sections of a sheaf of rings `R`, as an
endomorphism of the free sheaf of `R`-modules of rank one. Right multiplication is used because
it is the one that is `R`-linear without assuming `R` commutative. -/
def unitEnd (a : RingCat.sectionsSubring R.obj) :
    SheafOfModules.unit R ⟶ SheafOfModules.unit R :=
  ⟨{ app Z := ModuleCat.ofHom
        { toFun x := x * a.1 Z
          map_add' p q := add_mul p q (a.1 Z)
          map_smul' r x := mul_assoc r x (a.1 Z) }
     naturality := by
      intro Z Z' g
      ext
      change R.obj.map g (1 : R.obj.obj Z) * a.1 Z' = R.obj.map g (1 * a.1 Z)
      rw [one_mul, map_one, one_mul]
      exact (a.2 g).symm }⟩

/-- On local sections, `unitEnd` is right multiplication by the local scalar. -/
lemma unitEnd_app_apply (a : RingCat.sectionsSubring R.obj) (Z : Cᵒᵖ) (x : R.obj.obj Z) :
    (unitEnd R a).val.app Z x = x * a.1 Z := rfl

/-- The compatible family of sections of `R` attached to an endomorphism of the free sheaf of
`R`-modules of rank one: its value at the unit section. -/
def unitEndSection (h : SheafOfModules.unit R ⟶ SheafOfModules.unit R) :
    RingCat.sectionsSubring R.obj :=
  ⟨fun Z => h.val.app Z (1 : R.obj.obj Z), by
    intro Z Z' g
    exact (PresheafOfModules.naturality_apply h.val g (1 : R.obj.obj Z)).symm.trans
      (congrArg (h.val.app Z') ((R.obj.map g).hom.map_one))⟩

/-- The scalar attached to an endomorphism of the free module of rank one is its value at the
unit section. -/
lemma unitEndSection_val (h : SheafOfModules.unit R ⟶ SheafOfModules.unit R) (Z : Cᵒᵖ) :
    (unitEndSection R h).1 Z = h.val.app Z (1 : R.obj.obj Z) := rfl

/-- **The global sections of a sheaf of rings are the endomorphisms of the free module of rank
one**: a scalar acts by multiplication, and an endomorphism is determined by its value at the
unit section. -/
def unitEndEquiv :
    (RingCat.sectionsSubring R.obj) ≃ (SheafOfModules.unit R ⟶ SheafOfModules.unit R) where
  toFun := unitEnd R
  invFun := unitEndSection R
  left_inv a := Subtype.ext (funext fun Z => one_mul (a.1 Z))
  right_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (1 : R.obj.obj Z) * (unitEndSection R h).1 Z = (unitEndSection R h).1 Z
    exact one_mul _

/-- Two endomorphisms of the free module of rank one agreeing at the unit sections are equal. -/
private theorem unitEnd_ext {h h' : SheafOfModules.unit R ⟶ SheafOfModules.unit R}
    (H : ∀ Z, h.val.app Z (1 : R.obj.obj Z) = h'.val.app Z (1 : R.obj.obj Z)) :
    h = h' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Z ↦ ?_)
  exact ModuleCat.hom_ext (LinearMap.ext_ring (H Z))

/-- The unit scalar acts as the identity. -/
lemma unitEnd_one : unitEnd R 1 = 𝟙 _ :=
  unitEnd_ext R fun Z => by exact one_mul (1 : R.obj.obj Z)

/-- The zero scalar acts as the zero endomorphism. -/
lemma unitEnd_zero : unitEnd R 0 = 0 :=
  unitEnd_ext R fun Z => by exact mul_zero (1 : R.obj.obj Z)

/-- A product of scalars acts as the composite of the two multiplications. -/
lemma unitEnd_mul (a b : RingCat.sectionsSubring R.obj) :
    unitEnd R (a * b) = unitEnd R a ≫ unitEnd R b := by
  refine unitEnd_ext R fun Z => ?_
  show (1 : R.obj.obj Z) * (a * b).1 Z = (1 * a.1 Z) * b.1 Z
  rw [one_mul, one_mul]
  rfl

/-- A sum of scalars acts as the sum of the two multiplications. -/
lemma unitEnd_add (a b : RingCat.sectionsSubring R.obj) :
    unitEnd R (a + b) = unitEnd R a + unitEnd R b := by
  refine unitEnd_ext R fun Z => ?_
  show (1 : R.obj.obj Z) * (a + b).1 Z = 1 * a.1 Z + 1 * b.1 Z
  rw [one_mul, one_mul, one_mul]
  rfl

/-- The endomorphism attached to the scalar attached to an endomorphism is the endomorphism. -/
lemma unitEnd_unitEndSection (h : SheafOfModules.unit R ⟶ SheafOfModules.unit R) :
    unitEnd R (unitEndSection R h) = h := (unitEndEquiv R).right_inv h

/-- The scalar attached to multiplication by a scalar is that scalar. -/
lemma unitEndSection_unitEnd (a : RingCat.sectionsSubring R.obj) :
    unitEndSection R (unitEnd R a) = a := (unitEndEquiv R).left_inv a

/-- The identity endomorphism corresponds to the unit scalar. -/
lemma unitEndSection_id : unitEndSection R (𝟙 _) = 1 := by
  rw [← unitEnd_one R, unitEndSection_unitEnd]

/-- The zero endomorphism corresponds to the zero scalar. -/
lemma unitEndSection_zero : unitEndSection R 0 = 0 := by
  rw [← unitEnd_zero R, unitEndSection_unitEnd]

/-- Composition of endomorphisms of the free module of rank one is multiplication of the
corresponding scalars. -/
lemma unitEndSection_comp (h k : SheafOfModules.unit R ⟶ SheafOfModules.unit R) :
    unitEndSection R (h ≫ k) = unitEndSection R h * unitEndSection R k := by
  have e := unitEnd_mul R (unitEndSection R h) (unitEndSection R k)
  rw [unitEnd_unitEndSection, unitEnd_unitEndSection] at e
  rw [← e, unitEndSection_unitEnd]

/-- Addition of endomorphisms of the free module of rank one is addition of the corresponding
scalars. -/
lemma unitEndSection_add (h k : SheafOfModules.unit R ⟶ SheafOfModules.unit R) :
    unitEndSection R (h + k) = unitEndSection R h + unitEndSection R k := by
  have e := unitEnd_add R (unitEndSection R h) (unitEndSection R k)
  rw [unitEnd_unitEndSection, unitEnd_unitEndSection] at e
  rw [← e, unitEndSection_unitEnd]

/-- **Scalar multiplication on global sections is precomposition with `unitEnd`**: under the
identification of `Γ(C, M)` with the morphisms out of the free module of rank one, multiplying a
global section by a global scalar is precomposing with multiplication by that scalar. -/
lemma unitHomEquiv_unitEnd_comp {M : SheafOfModules.{w} R}
    (a : RingCat.sectionsSubring R.obj) (b : SheafOfModules.unit R ⟶ M) :
    SheafOfModules.unitHomEquiv M (unitEnd R a ≫ b) = a • SheafOfModules.unitHomEquiv M b := by
  apply Subtype.ext
  funext Z
  refine Eq.trans (congrArg (fun x : R.obj.obj Z => b.val.app Z x) ?_)
    ((b.val.app Z).hom.map_smul (a.1 Z) (1 : R.obj.obj Z))
  show (1 : R.obj.obj Z) * a.1 Z = a.1 Z • (1 : R.obj.obj Z)
  rw [smul_eq_mul, one_mul, mul_one]

/-- The identification of `Γ(C, M)` with the morphisms out of the free module of rank one is
additive. -/
lemma unitHomEquiv_add {M : SheafOfModules.{w} R} (b c : SheafOfModules.unit R ⟶ M) :
    SheafOfModules.unitHomEquiv M (b + c) =
      SheafOfModules.unitHomEquiv M b + SheafOfModules.unitHomEquiv M c :=
  Subtype.ext (funext fun _ => rfl)

/-- The identification of the morphisms out of the free module of rank one with `Γ(C, M)` is
additive. -/
lemma unitHomEquiv_symm_add {M : SheafOfModules.{w} R} (s t : M.sections) :
    (SheafOfModules.unitHomEquiv M).symm (s + t) =
      (SheafOfModules.unitHomEquiv M).symm s + (SheafOfModules.unitHomEquiv M).symm t :=
  (AddEquiv.mk (SheafOfModules.unitHomEquiv M) (unitHomEquiv_add R)).symm.map_add s t

end Unit

/-! ### Additivity of the module functors attached to a functor of sheaves of sets -/

section Additive

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{w'})

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- The underlying morphism of sheaves of sets of a sum of two morphisms of sheaves of modules is
the pair of underlying morphisms followed by the addition morphism of the target. -/
lemma moduleSheafFunctor_map_add_eq {G G' : SheafOfModules.{w'} O} (φ φ' : G ⟶ G') :
    (moduleSheafFunctor O).map (φ + φ') =
      Limits.prod.lift ((moduleSheafFunctor O).map φ) ((moduleSheafFunctor O).map φ') ≫
        moduleAddHom O G' := by
  refine hom_ext_sections (fun Z s ↦ ?_)
  rw [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  rfl

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The image of a sum of morphisms of sheaves of modules under a finite-product-preserving
functor of sheaves of sets is the sum of the images, for the transported addition. -/
lemma map_moduleSheafFunctor_map_add_apply {G G' : SheafOfModules.{w'} O} (φ φ' : G ⟶ G')
    (Z : Cᵒᵖ) (x : (Φ ⋙ sectionsFunctor J Z).obj (moduleSheaf O G)) :
    (Φ ⋙ sectionsFunctor J Z).map ((moduleSheafFunctor O).map (φ + φ')) x =
      moduleAddObj O G' (Φ ⋙ sectionsFunctor J Z)
        ((Φ ⋙ sectionsFunctor J Z).map ((moduleSheafFunctor O).map φ) x)
        ((Φ ⋙ sectionsFunctor J Z).map ((moduleSheafFunctor O).map φ') x) := by
  rw [SiteModules.moduleSheafFunctor_map_add_eq (O := O) φ φ', Functor.map_comp_apply,
    Functor.map_lift_apply]
  rfl

end Additive


/-! ### The ring map and the bijection on global sections -/

section RingedTopos

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The pullback of sheaves of modules along a morphism of ringed topoi is additive, being left
adjoint to the additive pushforward. -/
instance pullbackModules_additive : (f.pullbackModules).Additive :=
  (pullbackAdjPushforwardModules f).left_adjoint_additive

/-- **Morphisms out of the free module of rank one are unchanged by a pushforward**: by the
adjunction of Stacks 03D7 they are morphisms out of the pullback of the free `O_D`-module of rank
one, which is the free `O_C`-module of rank one. -/
def pushforwardUnitHomEquiv (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
        (pushforwardModules f).obj N) ≃
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ N) :=
  ((pullbackAdjPushforwardModules f).homEquiv _ N).symm.trans
    (pullbackModulesObjUnitIso f).symm.homFromEquiv

/-- `pushforwardUnitHomEquiv` is the adjunct morphism read on the free `O_C`-module of rank
one. -/
lemma pushforwardUnitHomEquiv_apply
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj N) :
    pushforwardUnitHomEquiv f N b = (pullbackModulesObjUnitIso f).hom ≫
      ((pullbackAdjPushforwardModules f).homEquiv _ N).symm b := rfl

/-- Multiplication by a global section of `O_D`, transported to an endomorphism of the free
`O_C`-module of rank one through the pullback of the free `O_D`-module of rank one. -/
def pushforwardUnitEndMap
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (pullbackModulesObjUnitIso f).hom ≫
    (f.pullbackModules).map (unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) a) ≫
      (pullbackModulesObjUnitIso f).inv

/-- `pushforwardUnitHomEquiv` turns precomposition with multiplication by a global section of
`O_D` into precomposition with its transported endomorphism. -/
lemma pushforwardUnitHomEquiv_unitEnd_comp
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    (b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj N) :
    pushforwardUnitHomEquiv f N (unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) a ≫ b) =
      pushforwardUnitEndMap f a ≫ pushforwardUnitHomEquiv f N b := by
  rw [pushforwardUnitHomEquiv_apply, pushforwardUnitHomEquiv_apply, pushforwardUnitEndMap,
    Adjunction.homEquiv_naturality_left_symm]
  simp

/-- `pushforwardUnitHomEquiv` is additive, the two adjoint functors being additive. -/
lemma pushforwardUnitHomEquiv_add
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (b b' : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj N) :
    pushforwardUnitHomEquiv f N (b + b') =
      pushforwardUnitHomEquiv f N b + pushforwardUnitHomEquiv f N b' := by
  rw [pushforwardUnitHomEquiv_apply, pushforwardUnitHomEquiv_apply,
    pushforwardUnitHomEquiv_apply, Adjunction.homAddEquiv_symm_add, Preadditive.comp_add]

/-- `pushforwardUnitHomEquiv` is natural in the sheaf of modules. -/
lemma pushforwardUnitHomEquiv_comp
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (q : N ⟶ N')
    (b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj N) :
    pushforwardUnitHomEquiv f N' (b ≫ (pushforwardModules f).map q) =
      pushforwardUnitHomEquiv f N b ≫ q := by
  rw [pushforwardUnitHomEquiv_apply, pushforwardUnitHomEquiv_apply,
    Adjunction.homEquiv_naturality_right_symm, Category.assoc]

/-- The morphism from the free `O_D`-module of rank one to the pushforward of the free
`O_C`-module of rank one that corresponds to the identity. -/
def pushforwardUnitSection :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (pushforwardUnitHomEquiv f
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm (𝟙 _)

/-- The transported multiplication is the image of multiplication by the scalar on the canonical
morphism `pushforwardUnitSection`. This presentation makes its additivity visible. -/
lemma pushforwardUnitEndMap_eq
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    pushforwardUnitEndMap f a =
      pushforwardUnitHomEquiv f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) a ≫ pushforwardUnitSection f) := by
  rw [pushforwardUnitHomEquiv_unitEnd_comp, pushforwardUnitSection, Equiv.apply_symm_apply,
    Category.comp_id]

/-- The transported multiplication is additive in the scalar. -/
lemma pushforwardUnitEndMap_add
    (a b : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    pushforwardUnitEndMap f (a + b) =
      pushforwardUnitEndMap f a + pushforwardUnitEndMap f b := by
  rw [pushforwardUnitEndMap_eq, pushforwardUnitEndMap_eq, pushforwardUnitEndMap_eq,
    unitEnd_add, Preadditive.add_comp, pushforwardUnitHomEquiv_add]

/-- The transported multiplication by the zero scalar is zero. -/
lemma pushforwardUnitEndMap_zero : pushforwardUnitEndMap f 0 = 0 := by
  rw [pushforwardUnitEndMap, unitEnd_zero, Functor.map_zero]
  simp

/-- The transported multiplication by the unit scalar is the identity. -/
lemma pushforwardUnitEndMap_one : pushforwardUnitEndMap f 1 = 𝟙 _ := by
  rw [pushforwardUnitEndMap, unitEnd_one, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id]

/-- The transported multiplication by a product of scalars is the composite of the two
transported multiplications. -/
lemma pushforwardUnitEndMap_mul
    (a b : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    pushforwardUnitEndMap f (a * b) =
      pushforwardUnitEndMap f a ≫ pushforwardUnitEndMap f b := by
  rw [pushforwardUnitEndMap, pushforwardUnitEndMap, pushforwardUnitEndMap, unitEnd_mul,
    CategoryTheory.Functor.map_comp]
  simp

/-- **The ring map `Γ(D, O_D) ⟶ Γ(C, O_C)` induced by a morphism of ringed topoi**: a global
section of `O_D` acts on the free `O_D`-module of rank one, and its action is transported to the
free `O_C`-module of rank one, where it is again multiplication by a global section. -/
def globalSectionsRingHom :
    RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj →+*
      RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj where
  toFun a := unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (pushforwardUnitEndMap f a)
  map_one' := by rw [pushforwardUnitEndMap_one, unitEndSection_id]
  map_mul' a b := by rw [pushforwardUnitEndMap_mul, unitEndSection_comp]
  map_zero' := by rw [pushforwardUnitEndMap_zero, unitEndSection_zero]
  map_add' a b := by rw [pushforwardUnitEndMap_add, unitEndSection_add]

/-- Multiplication by the image of a scalar under `globalSectionsRingHom` is the transported
multiplication. -/
lemma unitEnd_globalSectionsRingHom
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (globalSectionsRingHom f a) =
      pushforwardUnitEndMap f a :=
  unitEnd_unitEndSection _ _

/-- **Global sections are unchanged by a pushforward**: `Γ(D, f_*N) ≃ Γ(C, N)`, obtained by
reading both sides as morphisms out of the free module of rank one. -/
def globalSectionsPushforwardEquiv
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((pushforwardModules f).obj N).sections ≃ N.sections :=
  (SheafOfModules.unitHomEquiv ((pushforwardModules f).obj N)).symm.trans
    ((pushforwardUnitHomEquiv f N).trans (SheafOfModules.unitHomEquiv N))

/-- `globalSectionsPushforwardEquiv` is the comparison of hom-sets out of the free module of rank
one, read on global sections. -/
lemma globalSectionsPushforwardEquiv_apply
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : ((pushforwardModules f).obj N).sections) :
    globalSectionsPushforwardEquiv f N s =
      SheafOfModules.unitHomEquiv N (pushforwardUnitHomEquiv f N
        ((SheafOfModules.unitHomEquiv ((pushforwardModules f).obj N)).symm s)) := rfl

/-- The comparison of global sections is additive. -/
lemma globalSectionsPushforwardEquiv_add
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s t : ((pushforwardModules f).obj N).sections) :
    globalSectionsPushforwardEquiv f N (s + t) =
      globalSectionsPushforwardEquiv f N s + globalSectionsPushforwardEquiv f N t := by
  rw [globalSectionsPushforwardEquiv_apply, globalSectionsPushforwardEquiv_apply,
    globalSectionsPushforwardEquiv_apply, unitHomEquiv_symm_add, pushforwardUnitHomEquiv_add,
    unitHomEquiv_add]

/-- The comparison of global sections carries the action of a global section of `O_D` to the
action of its image in `Γ(C, O_C)`. -/
lemma globalSectionsPushforwardEquiv_smul
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    (s : ((pushforwardModules f).obj N).sections) :
    letI := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N
    letI := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj N)
    globalSectionsPushforwardEquiv f N (a • s) =
      globalSectionsRingHom f a • globalSectionsPushforwardEquiv f N s := by
  let := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N
  let := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N)
  have h : (SheafOfModules.unitHomEquiv ((pushforwardModules f).obj N)).symm (a • s) =
      unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) a ≫
        (SheafOfModules.unitHomEquiv ((pushforwardModules f).obj N)).symm s :=
    (SheafOfModules.unitHomEquiv ((pushforwardModules f).obj N)).injective (by
      rw [Equiv.apply_symm_apply, unitHomEquiv_unitEnd_comp, Equiv.apply_symm_apply])
  rw [globalSectionsPushforwardEquiv_apply, globalSectionsPushforwardEquiv_apply, h,
    pushforwardUnitHomEquiv_unitEnd_comp, ← unitEnd_globalSectionsRingHom,
    unitHomEquiv_unitEnd_comp]

/-- The comparison of global sections is natural in the sheaf of modules. -/
lemma globalSectionsPushforwardEquiv_naturality
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (q : N ⟶ N')
    (s : ((pushforwardModules f).obj N).sections) :
    globalSectionsPushforwardEquiv f N'
        (SheafOfModules.sectionsMap ((pushforwardModules f).map q) s) =
      SheafOfModules.sectionsMap q (globalSectionsPushforwardEquiv f N s) := by
  rw [globalSectionsPushforwardEquiv_apply, globalSectionsPushforwardEquiv_apply,
    ← SheafOfModules.unitHomEquiv_symm_comp, pushforwardUnitHomEquiv_comp,
    SheafOfModules.unitHomEquiv_comp_apply]

/-- The inverse comparison of global sections is additive. -/
lemma globalSectionsPushforwardEquiv_symm_add
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (s t : N.sections) :
    (globalSectionsPushforwardEquiv f N).symm (s + t) =
      (globalSectionsPushforwardEquiv f N).symm s +
        (globalSectionsPushforwardEquiv f N).symm t :=
  (AddEquiv.mk (globalSectionsPushforwardEquiv f N)
    (globalSectionsPushforwardEquiv_add f N)).symm.map_add s t

/-- The inverse comparison of global sections carries the action of the image of a global section
of `O_D` to the action of that global section. -/
lemma globalSectionsPushforwardEquiv_symm_smul
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    (t : N.sections) :
    letI := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N
    letI := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj N)
    (globalSectionsPushforwardEquiv f N).symm (globalSectionsRingHom f a • t) =
      a • (globalSectionsPushforwardEquiv f N).symm t :=
  let := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N
  let := sectionsModule (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N)
  (globalSectionsPushforwardEquiv f N).injective (by
    rw [Equiv.apply_symm_apply, globalSectionsPushforwardEquiv_smul, Equiv.apply_symm_apply])

end RingedTopos

/-! ### The factorisation `Γ(C, -) = Γ(D, -) ∘ f_*`

The two functors take values in `ModuleCat.{max u w}` and `ModuleCat.{max u' w'}` for the object
universes `u`, `u'` and the section universes `w`, `w'` of the two ringed topoi, and restriction of
scalars does not change the module universe, so the isomorphism needs `max u w = max u' w'`. It is
stated first at the universes `C ∈ Type (max u t)`, `D ∈ Type (max u s)`, sections in
`Type (max w t s)`, where both module universes are `max u w t s`; this covers the ringed topoi of
different object universes, such as a crystalline topos over a Zariski topos. The case `t = s = 0`
is the classical one of equal object and section universes. -/

section GlobalSectionsIsoGeneral

universe t s

variable {X : RingedTopos.{v, max u t, max w t s}} {Y : RingedTopos.{v', max u s, max w t s}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max w t s} RingCat.{max w t s})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max w t s} RingCat.{max w t s})]
  [X.J.HasSheafCompose (forget RingCat.{max w t s})]
  [Y.J.HasSheafCompose (forget RingCat.{max w t s})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max w t s})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max w t s})]
  [HasWeakSheafify X.J AddCommGrpCat.{max w t s}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w t s}]
  (f : RingedToposHom X Y)

/-- The comparison `Γ(D, f_*N) ≅ Γ(C, N)` of global sections as `Γ(D, O_D)`-modules, the right
hand side taken with scalars restricted along `globalSectionsRingHom f`, for ringed topoi whose
object universes may differ. -/
def globalSectionsPushforwardIsoAppGeneral
    (N : SheafOfModules.{max w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (pushforwardModules f ⋙
        globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N ≅
      (globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ModuleCat.restrictScalars (globalSectionsRingHom f)).obj N where
  hom := ModuleCat.ofHom
    (X := (pushforwardModules f ⋙
      globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N)
    (Y := (globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      ModuleCat.restrictScalars (globalSectionsRingHom f)).obj N)
    { toFun := globalSectionsPushforwardEquiv f N
      map_add' := globalSectionsPushforwardEquiv_add f N
      map_smul' := globalSectionsPushforwardEquiv_smul f N }
  inv := ModuleCat.ofHom
    (X := (globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      ModuleCat.restrictScalars (globalSectionsRingHom f)).obj N)
    (Y := (pushforwardModules f ⋙
      globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N)
    { toFun := (globalSectionsPushforwardEquiv f N).symm
      map_add' := globalSectionsPushforwardEquiv_symm_add f N
      map_smul' := globalSectionsPushforwardEquiv_symm_smul f N }
  hom_inv_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    exact (globalSectionsPushforwardEquiv f N).symm_apply_apply s
  inv_hom_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    exact (globalSectionsPushforwardEquiv f N).apply_symm_apply s

/-- **Global sections of modules are unchanged by a pushforward along a morphism of ringed
topoi**, as an isomorphism of functors, for ringed topoi whose object universes may differ:
`Γ(C, -) = Γ(D, -) ∘ f_*` after restricting scalars along the induced ring map
`Γ(D, O_D) ⟶ Γ(C, O_C)` on global sections. -/
def globalSectionsPushforwardIsoGeneral :
    pushforwardModules f ⋙ globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ModuleCat.restrictScalars (globalSectionsRingHom f) :=
  NatIso.ofComponents (globalSectionsPushforwardIsoAppGeneral.{w, v, u, v', t, s} f)
    (fun {N N'} q ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
      exact globalSectionsPushforwardEquiv_naturality f q s)

end GlobalSectionsIsoGeneral

section GlobalSectionsIso

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- The comparison `Γ(D, f_*N) ≅ Γ(C, N)` of global sections as `Γ(D, O_D)`-modules, the right
hand side taken with scalars restricted along `globalSectionsRingHom f`: the case of
`globalSectionsPushforwardIsoAppGeneral` with equal object and section universes. -/
def globalSectionsPushforwardIsoApp
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (pushforwardModules f ⋙
        globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N ≅
      (globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ModuleCat.restrictScalars (globalSectionsRingHom f)).obj N :=
  globalSectionsPushforwardIsoAppGeneral.{w, v, u, v', 0, 0} f N

/-- **Global sections of modules are unchanged by a pushforward along a morphism of ringed
topoi**, as an isomorphism of functors: `Γ(C, -) = Γ(D, -) ∘ f_*` after restricting scalars along
the induced ring map `Γ(D, O_D) ⟶ Γ(C, O_C)` on global sections. This is the factorisation of
`Γ(C, -)` that makes the Leray spectral sequence of Stacks 0732 a Grothendieck spectral
sequence. It is `globalSectionsPushforwardIsoGeneral` with equal object and section
universes. -/
def globalSectionsPushforwardIso :
    pushforwardModules f ⋙ globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ModuleCat.restrictScalars (globalSectionsRingHom f) :=
  globalSectionsPushforwardIsoGeneral.{w, v, u, v', 0, 0} f

/-- The same comparison read in abelian groups, where the two sides are modules over the same
ring — namely none — and no restriction of scalars is needed:
`Γ(C, -) = Γ(D, -) ∘ f_*` as functors to abelian groups. -/
def globalSectionsPushforwardForgetIso :
    pushforwardModules f ⋙ globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        forget₂ (ModuleCat.{max u w}
            (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
          AddCommGrpCat.{max u w} ≅
      globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        forget₂ (ModuleCat.{max u w}
            (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          AddCommGrpCat.{max u w} :=
  Functor.isoWhiskerRight (globalSectionsPushforwardIso f)
    (forget₂ (ModuleCat.{max u w}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
      AddCommGrpCat.{max u w})

end GlobalSectionsIso

end Stacks.Cohomology.SiteModules

end
