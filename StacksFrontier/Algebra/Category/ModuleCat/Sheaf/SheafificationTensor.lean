module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification commutes with tensor products of presheaves of modules

Let `O` be a presheaf of commutative rings and `a : O ⟶ O♯` a morphism to an associated sheaf of
commutative rings. For presheaves of `O`-modules `F` and `G`, in module universes independent of
each other and of the universe of the ring, the sheafification of the objectwise tensor product
`F ⊗_O G` is the tensor product over `O♯` of the sheafifications of `F` and `G`.

## Main definitions

* `CategoryTheory.Sheaf.toRingCat`: the underlying sheaf of rings of a sheaf of commutative rings.
* `PresheafOfModules.moduleSheafification` and `PresheafOfModules.moduleSheafificationUnit`:
  sheafification of presheaves of modules along a morphism to an associated sheaf of commutative
  rings, and the unit of its adjunction.
* `Stacks.SheafOfModules.Tensor.sheafTensor`: the tensor product of two sheaves of modules, the
  sheafification of the objectwise tensor product of the underlying presheaves.
* `Stacks.BilinearMap.ofRestrictScalars`: a bilinear map of restrictions of scalars along a locally
  surjective morphism of presheaves of rings, with values in a separated presheaf, as a bilinear
  map over the larger ring.
* `PresheafOfModules.ofBilinear` and `PresheafOfModules.toBilinear`: the correspondence between
  bilinear maps on sections and morphisms out of the objectwise tensor product.
* `PresheafOfModules.tensorBaseChange`: the canonical morphism `M|_O ⊗_O N|_O ⟶ (M ⊗_{O'} N)|_O`
  along a morphism of presheaves of commutative rings.
* `PresheafOfModules.tensorSheafifyComparison` and `PresheafOfModules.tensorSheafifyDesc`: the two
  mutually inverse comparison morphisms between the associated sheaf of an objectwise tensor
  product and the tensor product of the associated sheaves.

## Main results

* `PresheafOfModules.sheafification_hom_ext`: two morphisms out of the sheafification of a
  presheaf of modules whose composites with the unit agree are equal.
* `PresheafOfModules.sheafificationTensorIso`: sheafification commutes with the tensor product of
  presheaves of modules, naturally in both presheaves of modules.
* `PresheafOfModules.sheafificationTensorIso_hom_unit_tmul`: that isomorphism sends the image of
  a pure tensor of sheafification-unit images to the sheafification-unit image of the original
  pure tensor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe v u w z z₁ z₂

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying sheaf of rings of a sheaf of commutative rings. -/
abbrev toRingCat (Osharp : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  ⟨Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w},
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj Osharp).property⟩

/-- The map of presheaves of rings underlying a morphism from a presheaf of commutative rings
to (the sections of) a sheaf of commutative rings. -/
abbrev toRingCatMap {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}}
    (a : O ⟶ Osharp.obj) :
    O ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶ (toRingCat J Osharp).obj :=
  Functor.whiskerRight a (forget₂ CommRingCat.{w} RingCat.{w})

end CategoryTheory.Sheaf

namespace PresheafOfModules

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]

section Defs

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]

/-- Sheafification of presheaves of modules along a morphism to an associated sheaf of
commutative rings. -/
noncomputable abbrev moduleSheafification :
    PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat) ⥤
      SheafOfModules.{z} (toRingCat J Osharp) :=
  PresheafOfModules.sheafification (toRingCatMap J a)

/-- The unit of the sheafification adjunction for presheaves of modules. -/
noncomputable abbrev moduleSheafificationUnit
    (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) :=
  (PresheafOfModules.sheafificationAdjunction (toRingCatMap J a)).unit.app F

end Defs

end PresheafOfModules

namespace PresheafOfModules

universe sheafSite sheafHom sheafRing sheafModule

variable {C : Type sheafSite} [Category.{sheafHom} C] {J : GrothendieckTopology C}
  {coefficientPresheaf : Cᵒᵖ ⥤ RingCat.{sheafRing}} (ring : Sheaf J RingCat.{sheafRing})
  (scalarMap : coefficientPresheaf ⟶ ring.obj)
  [Presheaf.IsLocallyInjective J scalarMap] [Presheaf.IsLocallySurjective J scalarMap]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sheafModule}]
  [HasWeakSheafify J AddCommGrpCat.{sheafModule}]

/-- Module sheafification along a locally bijective coefficient map is additive. -/
instance sheafification_additive [HasBinaryBiproducts (SheafOfModules.{sheafModule} ring)] :
    (sheafification (R := ring) scalarMap : PresheafOfModules.{sheafModule} coefficientPresheaf ⥤
      SheafOfModules.{sheafModule} ring).Additive :=
  have : PreservesBinaryBiproducts
      (sheafification (R := ring) scalarMap : PresheafOfModules.{sheafModule} coefficientPresheaf ⥤
        SheafOfModules.{sheafModule} ring) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- Module sheafification inverts its adjunction unit. -/
instance sheafification_map_unit_isIso
    (presheaf : PresheafOfModules.{sheafModule} coefficientPresheaf) :
    IsIso ((sheafification (R := ring) scalarMap).map
      ((sheafificationAdjunction (R := ring) scalarMap).unit.app presheaf)) := by
  let sheafificationFunctor : PresheafOfModules.{sheafModule} coefficientPresheaf ⥤
      SheafOfModules.{sheafModule} ring := sheafification (R := ring) scalarMap
  let adjunction : sheafificationFunctor ⊣
      SheafOfModules.forget.{sheafModule} ring ⋙ restrictScalars scalarMap :=
    sheafificationAdjunction (R := ring) scalarMap
  change IsIso (sheafificationFunctor.map (adjunction.unit.app presheaf))
  let : IsIso (adjunction.counit.app (sheafificationFunctor.obj presheaf)) := inferInstance
  have inverseEquation : sheafificationFunctor.map (adjunction.unit.app presheaf) =
      inv (adjunction.counit.app (sheafificationFunctor.obj presheaf)) := by
    rw [← cancel_mono (adjunction.counit.app (sheafificationFunctor.obj presheaf)),
      IsIso.inv_hom_id]
    exact adjunction.left_triangle_components presheaf
  rw [inverseEquation]
  infer_instance

end PresheafOfModules

namespace Stacks.SheafOfModules.Tensor

universe siteUniverse morphismUniverse coefficientUniverse leftUniverse rightUniverse

variable {C : Type siteUniverse} [Category.{morphismUniverse} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{coefficientUniverse})

section Tensor

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max leftUniverse rightUniverse}]
  [HasWeakSheafify J AddCommGrpCat.{max leftUniverse rightUniverse}]

/-- The tensor product of module sheaves in independent section universes, obtained by
sheafifying the canonical objectwise tensor product of their underlying presheaves. -/
@[stacks 01CA "the section's definition of the tensor product sheaf
`F ⊗_O G = (F ⊗_{p, O} G)^#`, the sheafification of the tensor product presheaf; over an
arbitrary site, the ringed-space case being the site of opens of `X`"]
noncomputable def sheafTensor :
    SheafOfModules.{leftUniverse} (ringSheaf R) ⥤ SheafOfModules.{rightUniverse} (ringSheaf R) ⥤
      SheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R) :=
  SheafOfModules.forget.{leftUniverse} (ringSheaf R) ⋙
    PresheafOfModules.tensorBifunctor.{morphismUniverse, siteUniverse, coefficientUniverse,
      leftUniverse, rightUniverse} R.obj ⋙
    (Functor.whiskeringLeft
      (SheafOfModules.{rightUniverse} (ringSheaf R))
      (PresheafOfModules.{rightUniverse} (ringSheaf R).obj)
      (PresheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R).obj)).obj
        (SheafOfModules.forget.{rightUniverse} (ringSheaf R)) ⋙
    (Functor.whiskeringRight
      (SheafOfModules.{rightUniverse} (ringSheaf R))
      (PresheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R).obj)
      (SheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R))).obj
        (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj))

/-- The tensor product of two sheaves of modules is the sheafification of the objectwise
tensor product of their underlying presheaves. -/
@[simp]
lemma sheafTensor_obj_obj (left : SheafOfModules.{leftUniverse} (ringSheaf R))
    (right : SheafOfModules.{rightUniverse} (ringSheaf R)) :
    ((sheafTensor R).obj left).obj right =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).obj
        (PresheafOfModules.tensorObj (O := R.obj) left.val right.val) := rfl

/-- The tensor product sheaf, on a morphism in the second variable. -/
@[simp]
lemma sheafTensor_obj_map (left : SheafOfModules.{leftUniverse} (ringSheaf R))
    {right right' : SheafOfModules.{rightUniverse} (ringSheaf R)} (rightHom : right ⟶ right') :
    ((sheafTensor R).obj left).map rightHom =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
        (PresheafOfModules.tensorHom (O := R.obj) (𝟙 left.val) rightHom.val) := rfl

/-- The tensor product sheaf, on a morphism in the first variable. -/
@[simp]
lemma sheafTensor_map_app {left left' : SheafOfModules.{leftUniverse} (ringSheaf R)}
    (leftHom : left ⟶ left') (right : SheafOfModules.{rightUniverse} (ringSheaf R)) :
    ((sheafTensor R).map leftHom).app right =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
        (PresheafOfModules.tensorHom (O := R.obj) leftHom.val (𝟙 right.val)) := rfl

/-- The tensor product sheaf, on a pair of morphisms: the sheafification of their objectwise
tensor product. -/
@[simp]
lemma sheafTensor_uncurry_map {left left' : SheafOfModules.{leftUniverse} (ringSheaf R)}
    {right right' : SheafOfModules.{rightUniverse} (ringSheaf R)}
    (leftHom : left ⟶ left') (rightHom : right ⟶ right') :
    (Functor.uncurry.obj (sheafTensor R)).map
        ((leftHom, rightHom) : (left, right) ⟶ (left', right')) =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
        (PresheafOfModules.tensorHom (O := R.obj) leftHom.val rightHom.val) := by
  let sheafificationFunctor : PresheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R).obj ⥤
      SheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R) :=
    PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)
  exact (sheafificationFunctor.map_comp
    (PresheafOfModules.tensorHom (O := R.obj) leftHom.val (𝟙 right.val))
    (PresheafOfModules.tensorHom (O := R.obj) (𝟙 left'.val) rightHom.val)).symm.trans
    (congrArg (sheafificationFunctor.map
      (X := PresheafOfModules.tensorObj (O := R.obj) left.val right.val)
      (Y := PresheafOfModules.tensorObj (O := R.obj) left'.val right'.val))
      (PresheafOfModules.tensorBifunctor_uncurry_map (O := R.obj) leftHom.val rightHom.val))

variable [HasBinaryBiproducts (SheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R))]

/-- The tensor product of sheaves of modules is additive in the first variable. -/
instance sheafTensor_additive :
    (sheafTensor.{siteUniverse, morphismUniverse, coefficientUniverse,
      leftUniverse, rightUniverse} R).Additive where
  map_add {left left'} leftHom leftHom' := by
    let sheafificationFunctor :
        PresheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R).obj ⥤
          SheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R) :=
      PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)
    let : sheafificationFunctor.Additive :=
      PresheafOfModules.sheafification_additive (ringSheaf R) (𝟙 (ringSheaf R).obj)
    apply NatTrans.ext
    funext right
    exact (congrArg (sheafificationFunctor.map
      (X := PresheafOfModules.tensorObj (O := R.obj) left.val right.val)
      (Y := PresheafOfModules.tensorObj (O := R.obj) left'.val right.val))
      (PresheafOfModules.tensorHom_add_left (O := R.obj)
        leftHom.val leftHom'.val (𝟙 right.val))).trans
      (sheafificationFunctor.map_add
        (f := PresheafOfModules.tensorHom (O := R.obj) leftHom.val (𝟙 right.val))
        (g := PresheafOfModules.tensorHom (O := R.obj) leftHom'.val (𝟙 right.val)))

/-- The tensor product of sheaves of modules is additive in the second variable. -/
instance sheafTensor_obj_additive (left : SheafOfModules.{leftUniverse} (ringSheaf R)) :
    ((sheafTensor.{siteUniverse, morphismUniverse, coefficientUniverse,
      leftUniverse, rightUniverse} R).obj left).Additive where
  map_add {right right'} rightHom rightHom' := by
    let sheafificationFunctor :
        PresheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R).obj ⥤
          SheafOfModules.{max leftUniverse rightUniverse} (ringSheaf R) :=
      PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)
    let : sheafificationFunctor.Additive :=
      PresheafOfModules.sheafification_additive (ringSheaf R) (𝟙 (ringSheaf R).obj)
    exact (congrArg (sheafificationFunctor.map
      (X := PresheafOfModules.tensorObj (O := R.obj) left.val right.val)
      (Y := PresheafOfModules.tensorObj (O := R.obj) left.val right'.val))
      (PresheafOfModules.tensorHom_add_right (O := R.obj)
        (𝟙 left.val) rightHom.val rightHom'.val)).trans
      (sheafificationFunctor.map_add
        (f := PresheafOfModules.tensorHom (O := R.obj) (𝟙 left.val) rightHom.val)
        (g := PresheafOfModules.tensorHom (O := R.obj) (𝟙 left.val) rightHom'.val))

end Tensor

end Stacks.SheafOfModules.Tensor

namespace Stacks.BilinearMap

open PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Postcomp

variable {R : Cᵒᵖ ⥤ RingCat.{w}} {M : PresheafOfModules.{z} R} {N : PresheafOfModules.{z₁} R}
  {P Q : PresheafOfModules.{z₂} R}

/-- An equality of bilinear maps, read on a pair of sections. -/
lemma congr_app {β γ : BilinearMap M N P} (h : β = γ) (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    β.app X x y = γ.app X x y := by rw [h]

/-- Post-composition of a bilinear map with a morphism of presheaves of modules. -/
def postcomp (β : BilinearMap M N P) (ψ : P ⟶ Q) : BilinearMap M N Q where
  app X := AddMonoidHom.mk'
      (fun x => AddMonoidHom.mk' (fun y => Hom.app ψ X (β.app X x y))
        (fun y y' => by
          change Hom.app ψ X (β.app X x (y + y')) = _
          rw [map_add (β.app X x), map_add]))
      (fun x x' => by
        ext y
        change Hom.app ψ X (β.app X (x + x') y) = _
        rw [β.map_add_left, map_add]
        rfl)
  map_smul_left X r x y := by
    change Hom.app ψ X (β.app X (r • x) y) = r • Hom.app ψ X (β.app X x y)
    rw [β.map_smul_left, map_smul]
  map_smul_right X r x y := by
    change Hom.app ψ X (β.app X x (r • y)) = r • Hom.app ψ X (β.app X x y)
    rw [β.map_smul_right, map_smul]
  naturality {X Y} f x y := by
    change Q.map f (Hom.app ψ X (β.app X x y)) =
      Hom.app ψ Y (β.app Y (M.map f x) (N.map f y))
    rw [← naturality_apply ψ f, β.naturality]

/-- `Stacks.BilinearMap.postcomp`, on a pair of sections. -/
lemma postcomp_app (β : BilinearMap M N P) (ψ : P ⟶ Q) (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    (β.postcomp ψ).app X x y = Hom.app ψ X (β.app X x y) := rfl

end Postcomp

section Upgrade

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{w}} (ρ : R₀ ⟶ R)
  {M : PresheafOfModules.{z} R} {N : PresheafOfModules.{z₁} R} {P : PresheafOfModules.{z₂} R}
  (β : BilinearMap ((restrictScalars ρ).obj M) ((restrictScalars ρ).obj N)
    ((restrictScalars ρ).obj P))

/-- The map on sections of a bilinear map of restrictions of scalars, as a map between the modules
over the larger ring. -/
def appLarger (X : Cᵒᵖ) : M.obj X →+ N.obj X →+ P.obj X := β.app X

/-- `Stacks.BilinearMap.appLarger` agrees with the map on sections of the bilinear map. -/
lemma appLarger_apply (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    appLarger ρ β X x y = β.app X x y := rfl

/-- `Stacks.BilinearMap.appLarger` commutes with the restriction maps. -/
lemma appLarger_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) (y : N.obj X) :
    P.restrictₛₗ f (appLarger ρ β X x y)
      = appLarger ρ β Y (M.restrictₛₗ f x) (N.restrictₛₗ f y) :=
  β.naturality f x y

/-- `Stacks.BilinearMap.appLarger` is linear in the first variable for scalars in the image
of the smaller ring. -/
lemma appLarger_map_smul_left_of_small (X : Cᵒᵖ) (r₀ : R₀.obj X) (x : M.obj X) (y : N.obj X) :
    appLarger ρ β X (ρ.app X r₀ • x) y = ρ.app X r₀ • appLarger ρ β X x y :=
  β.map_smul_left X r₀ x y

/-- `Stacks.BilinearMap.appLarger` is linear in the second variable for scalars in the image
of the smaller ring. -/
lemma appLarger_map_smul_right_of_small (X : Cᵒᵖ) (r₀ : R₀.obj X) (x : M.obj X) (y : N.obj X) :
    appLarger ρ β X x (ρ.app X r₀ • y) = ρ.app X r₀ • appLarger ρ β X x y :=
  β.map_smul_right X r₀ x y

section

variable [Presheaf.IsLocallySurjective J ρ] (hP : Presheaf.IsSeparated J P.presheaf)
include hP

/-- Over a locally surjective morphism of presheaves of rings, with separated target, `p = r • q`
as soon as this holds after restricting along every map where `r` comes from the smaller ring. -/
private theorem eq_smul_of_restrict_eq_smul {X : C} {r : R.obj (op X)} {p q : P.obj (op X)}
    (h : ∀ {Y : C} (f : Y ⟶ X) (r₀ : R₀.obj (op Y)), ρ.app (op Y) r₀ = R.map f.op r →
      P.restrictₛₗ f.op p = ρ.app (op Y) r₀ • P.restrictₛₗ f.op q) : p = r • q := by
  refine hP _ _ (Presheaf.imageSieve_mem J ρ r) _ _ ?_
  rintro Y f ⟨r₀, hr₀⟩
  change P.restrictₛₗ f.op _ = P.restrictₛₗ f.op _
  rw [map_smulₛₗ, ← hr₀]
  exact h f r₀ hr₀

/-- Along a locally surjective morphism of presheaves of rings, with separated target,
`Stacks.BilinearMap.appLarger` is linear in the first variable over the larger ring. -/
lemma appLarger_map_smul_left (X : Cᵒᵖ) (r : R.obj X) (x : M.obj X) (y : N.obj X) :
    appLarger ρ β X (r • x) y = r • appLarger ρ β X x y :=
  eq_smul_of_restrict_eq_smul ρ hP fun f r₀ hr₀ ↦ by
    rw [appLarger_naturality, map_smulₛₗ (M.restrictₛₗ f.op), ← hr₀,
      appLarger_map_smul_left_of_small, appLarger_naturality]

/-- Along a locally surjective morphism of presheaves of rings, with separated target,
`Stacks.BilinearMap.appLarger` is linear in the second variable over the larger ring. -/
lemma appLarger_map_smul_right (X : Cᵒᵖ) (r : R.obj X) (x : M.obj X) (y : N.obj X) :
    appLarger ρ β X x (r • y) = r • appLarger ρ β X x y :=
  eq_smul_of_restrict_eq_smul ρ hP fun f r₀ hr₀ ↦ by
    rw [appLarger_naturality, map_smulₛₗ (N.restrictₛₗ f.op), ← hr₀,
      appLarger_map_smul_right_of_small, appLarger_naturality]

/-- A bilinear map for the restrictions of scalars along a locally surjective morphism of
presheaves of rings, with values in a separated presheaf of modules, is a bilinear map for
the larger ring. -/
def ofRestrictScalars : BilinearMap M N P where
  app := appLarger ρ β
  map_smul_left := appLarger_map_smul_left ρ β hP
  map_smul_right := appLarger_map_smul_right ρ β hP
  naturality f x y := appLarger_naturality ρ β f x y

/-- `Stacks.BilinearMap.ofRestrictScalars` has the same map on sections as the original
bilinear map. -/
@[simp]
lemma ofRestrictScalars_app (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    (ofRestrictScalars ρ β hP).app X x y = β.app X x y := rfl

end

end Upgrade

end Stacks.BilinearMap

namespace PresheafOfModules

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]

/-- An equation between morphisms of presheaves of modules, read on sections. -/
lemma hom_congr_apply' {R' : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{z} R'}
    {φ ψ : M ⟶ N} (h : φ = ψ) (X : Cᵒᵖ) (x : M.obj X) :
    Hom.app φ X x = Hom.app ψ X x := by rw [h]

/-- The unit of the sheafification adjunction for presheaves of modules is the canonical
morphism `PresheafOfModules.toSheafify`. -/
lemma sheafificationAdjunction_unit_app_eq (M : PresheafOfModules.{z} R₀) :
    (sheafificationAdjunction α).unit.app M =
      toSheafify α (CategoryTheory.toSheafify J M.presheaf) :=
  (toPresheaf _).map_injective rfl

/-- The unit of the sheafification adjunction for presheaves of modules is locally
surjective. -/
instance isLocallySurjective_sheafificationAdjunction_unit_app (M : PresheafOfModules.{z} R₀) :
    IsLocallySurjective J ((sheafificationAdjunction α).unit.app M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J M.presheaf))

/-- The unit of the sheafification adjunction for presheaves of modules is locally
injective. -/
instance isLocallyInjective_sheafificationAdjunction_unit_app (M : PresheafOfModules.{z} R₀) :
    IsLocallyInjective J ((sheafificationAdjunction α).unit.app M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M.presheaf))

/-- The defining property of the morphism out of a sheafification associated with a morphism
out of the presheaf. -/
lemma sheafificationAdjunction_unit_comp_homEquiv_symm {M : PresheafOfModules.{z} R₀}
    {N : SheafOfModules.{z} R}
    (φ : M ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj N) :
    (sheafificationAdjunction α).unit.app M ≫ (SheafOfModules.forget R ⋙ restrictScalars α).map
        (((sheafificationAdjunction α).homEquiv M N).symm φ) = φ := by
  have h := ((sheafificationAdjunction α).homEquiv M N).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at h
  exact h

variable {α}

/-- Two morphisms out of the sheafification of a presheaf of modules are equal as soon as
their composites with the unit of the sheafification adjunction agree. -/
lemma sheafification_hom_ext {M : PresheafOfModules.{z} R₀} {N : SheafOfModules.{z} R}
    {f g : (sheafification α).obj M ⟶ N}
    (h : (sheafificationAdjunction α).unit.app M ≫
          (SheafOfModules.forget R ⋙ restrictScalars α).map f =
        (sheafificationAdjunction α).unit.app M ≫
          (SheafOfModules.forget R ⋙ restrictScalars α).map g) :
    f = g := by
  refine ((sheafificationAdjunction α).homEquiv M N).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

/-- Naturality of the unit of the sheafification adjunction. -/
lemma unit_comp_map {M N : PresheafOfModules.{z} R₀} (φ : M ⟶ N) :
    (sheafificationAdjunction α).unit.app M ≫
        (SheafOfModules.forget R ⋙ restrictScalars α).map ((sheafification α).map φ) =
      φ ≫ (sheafificationAdjunction α).unit.app N :=
  ((sheafificationAdjunction α).unit.naturality φ).symm

/-- Naturality of the unit of the sheafification adjunction, on sections. -/
lemma unit_naturality_apply {M N : PresheafOfModules.{z} R₀} (φ : M ⟶ N) (X : Cᵒᵖ)
    (x : M.obj X) :
    Hom.app ((sheafification α).map φ).val X
        (Hom.app ((sheafificationAdjunction α).unit.app M) X x) =
      Hom.app ((sheafificationAdjunction α).unit.app N) X (Hom.app φ X x) :=
  hom_congr_apply' (unit_comp_map φ) X x

/-- Composition of morphisms of presheaves of modules, on sections. -/
lemma comp_app_apply {R' : Cᵒᵖ ⥤ RingCat.{w}} {M N P : PresheafOfModules.{z} R'}
    (φ : M ⟶ N) (ψ : N ⟶ P) (X : Cᵒᵖ) (x : M.obj X) :
    Hom.app (φ ≫ ψ) X x = Hom.app ψ X (Hom.app φ X x) := rfl

end Unit

end PresheafOfModules

namespace PresheafOfModules

section OfBilinear

open Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)}
  {P : PresheafOfModules.{max z z₁} (O ⋙ forget₂ CommRingCat RingCat)}

/-- A bilinear map of presheaves of modules, given on sections, determines a morphism out of
the objectwise tensor product. -/
noncomputable def ofBilinear (β : BilinearMap F G P) : tensorObj F G ⟶ P :=
  tensorMk (fun X x y ↦ β.app X x y) (fun X ↦ β.map_add_left X) (fun X ↦ β.map_smul_left X)
    (fun X x ↦ map_add (β.app X x)) (fun X ↦ β.map_smul_right X)
    (fun {_ _} f x y ↦ β.naturality f x y)

/-- `PresheafOfModules.ofBilinear β` sends a pure tensor `x ⊗ₜ y` to `β.app X x y`. -/
@[simp]
lemma ofBilinear_tmul (β : BilinearMap F G P) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    Hom.app (ofBilinear β) X (x ⊗ₜ y) = β.app X x y :=
  ModuleCat.tensorLift_tmul _ _ _ _ _ _ _

end OfBilinear

end PresheafOfModules

namespace PresheafOfModules

section RestrictScalarsRestrict

variable {C : Type u} [Category.{v} C] {R₀ R : Cᵒᵖ ⥤ RingCat.{w}} (ρ : R₀ ⟶ R)
  (M : PresheafOfModules.{z} R)

/-- A section of a restriction of scalars, as a section of the original presheaf of modules. -/
def unrestrict {X : Cᵒᵖ} (m : ((restrictScalars ρ).obj M).obj X) : M.obj X := m

/-- `PresheafOfModules.unrestrict` turns the action of `r` into the action of `ρ.app X r`. -/
@[simp]
lemma unrestrict_smul {X : Cᵒᵖ} (r : R₀.obj X) (m : ((restrictScalars ρ).obj M).obj X) :
    unrestrict ρ M (r • m) = ρ.app X r • unrestrict ρ M m := rfl

/-- The restriction maps of a restriction of scalars are those of the original presheaf of
modules. -/
lemma restrictScalars_restrictₛₗ_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : ((restrictScalars ρ).obj M).obj X) :
    unrestrict ρ M (((restrictScalars ρ).obj M).restrictₛₗ f m)
      = M.restrictₛₗ f (unrestrict ρ M m) := rfl

end RestrictScalarsRestrict

section ToBilinear

open Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)}
  {P : PresheafOfModules.{max z z₁} (O ⋙ forget₂ CommRingCat RingCat)}

/-- The bilinear map on sections underlying a morphism out of an objectwise tensor product.
This is inverse to `PresheafOfModules.ofBilinear`. -/
noncomputable def toBilinear (φ : tensorObj F G ⟶ P) : BilinearMap F G P where
  app X := AddMonoidHom.mk'
      (fun x ↦ AddMonoidHom.mk' (fun y ↦ Hom.app φ X (x ⊗ₜ y))
        (fun y y' ↦ (congrArg (fun t ↦ Hom.app φ X t) (TensorProduct.tmul_add x y y')).trans
          (map_add (ConcreteCategory.hom (Hom.app φ X)) _ _)))
      (fun x x' ↦ by
        ext y
        exact (congrArg (fun t ↦ Hom.app φ X t) (TensorProduct.add_tmul x x' y)).trans
          (map_add (ConcreteCategory.hom (Hom.app φ X)) _ _))
  map_smul_left X r x y :=
    (congrArg (fun t ↦ Hom.app φ X t) (TensorProduct.smul_tmul' r x y)).trans
      (map_smul (ConcreteCategory.hom (Hom.app φ X)) r (x ⊗ₜ y))
  map_smul_right X r x y :=
    (congrArg (fun t ↦ Hom.app φ X t) (TensorProduct.tmul_smul r x y)).trans
      (map_smul (ConcreteCategory.hom (Hom.app φ X)) r (x ⊗ₜ y))
  naturality {X Y} f x y :=
    (naturality_apply φ f (x ⊗ₜ y)).symm.trans
      (congrArg (fun t ↦ Hom.app φ Y t) (tensorObj_restrictₛₗ_tmul f x y))

/-- `PresheafOfModules.toBilinear φ` sends `(x, y)` to the image of `x ⊗ₜ y` under `φ`. -/
@[simp]
lemma toBilinear_app (φ : tensorObj F G ⟶ P) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    (toBilinear φ).app X x y = Hom.app φ X (x ⊗ₜ y) := rfl

end ToBilinear

section BaseChange

variable {C : Type u} [Category.{v} C] {O O' : Cᵒᵖ ⥤ CommRingCat.{w}}
  (ρ' : O ⋙ forget₂ CommRingCat RingCat ⟶ O' ⋙ forget₂ CommRingCat RingCat)
  (M : PresheafOfModules.{z} (O' ⋙ forget₂ CommRingCat RingCat))
  (N : PresheafOfModules.{z₁} (O' ⋙ forget₂ CommRingCat RingCat))

/-- The canonical morphism from the objectwise tensor product over `O` of the restrictions of
scalars of two presheaves of `O'`-modules to the restriction of scalars of their objectwise
tensor product over `O'`. On sections it is the identity on pure tensors; only the ring over
which the tensor product is formed changes. -/
noncomputable def tensorBaseChange :
    tensorObj ((restrictScalars ρ').obj M) ((restrictScalars ρ').obj N) ⟶
      (restrictScalars ρ').obj (tensorObj M N) :=
  tensorMk (fun X x y ↦ unrestrict ρ' M x ⊗ₜ[(O' ⋙ forget₂ CommRingCat RingCat).obj X]
      unrestrict ρ' N y)
    (fun _ _ _ _ ↦ TensorProduct.add_tmul _ _ _)
    (fun X r x y ↦ TensorProduct.smul_tmul' (ρ'.app X r) (unrestrict ρ' M x) (unrestrict ρ' N y))
    (fun _ _ _ _ ↦ TensorProduct.tmul_add _ _ _)
    (fun X r x y ↦ TensorProduct.tmul_smul (ρ'.app X r) (unrestrict ρ' M x) (unrestrict ρ' N y))
    (fun {_ _} f x y ↦ tensorObj_restrictₛₗ_tmul (O := O') (F := M) (G := N) f
      (unrestrict ρ' M x) (unrestrict ρ' N y))

end BaseChange

end PresheafOfModules

namespace PresheafOfModules

open CategoryTheory.Sheaf Stacks

section TensorSheafify

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]

/-- An equation between morphisms of presheaves of modules, read on sections. -/
lemma hom_congr_apply {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{z} R} {φ ψ : M ⟶ N}
    (h : φ = ψ) (X : Cᵒᵖ) (x : M.obj X) : Hom.app φ X x = Hom.app ψ X x := by rw [h]

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]

/-- A sheaf of modules over an associated sheaf of rings `O♯`, as a presheaf of `O`-modules by
restriction of scalars along `a`. -/
noncomputable abbrev restrictSheaf (M : SheafOfModules.{z} (toRingCat J Osharp)) :
    PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat) :=
  (SheafOfModules.forget (toRingCat J Osharp) ⋙ restrictScalars (toRingCatMap J a)).obj M

end

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z₁}] [HasWeakSheafify J AddCommGrpCat.{z₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z z₁}]
  [HasWeakSheafify J AddCommGrpCat.{max z z₁}]
  (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat))
  (G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z₁}] [HasWeakSheafify J AddCommGrpCat.{z₁}] in
/-- The tensor product bifunctor on sheaves of modules, on morphisms: it is the sheafification
functor applied to the objectwise tensor product of the two morphisms of sections. -/
lemma tensorSheafBifunctor_map
    {M₁ M₂ : SheafOfModules.{z} (toRingCat J Osharp)}
    {N₁ N₂ : SheafOfModules.{z₁} (toRingCat J Osharp)} (fg : (M₁, N₁) ⟶ (M₂, N₂)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁}
        Osharp))).map fg =
      (sheafification (𝟙 (toRingCat J Osharp).obj)).map
        ((Functor.prod (SheafOfModules.forget.{z} (toRingCat J Osharp))
          (SheafOfModules.forget.{z₁} (toRingCat J Osharp)) ⋙
            (Functor.uncurry.obj (tensorBifunctor Osharp.obj))).map fg) :=
  (Functor.map_comp
    (sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj))
    (tensorHom fg.1.val (𝟙 N₁.val)) (tensorHom (𝟙 M₂.val) fg.2.val)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z₁}] [HasWeakSheafify J AddCommGrpCat.{z₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z z₁}]
  [HasWeakSheafify J AddCommGrpCat.{max z z₁}] in
/-- The objectwise tensor product of the two morphisms of sections underlying a morphism in
the product category of sheaves of modules. -/
lemma prodForget_comp_tensorBifunctor_map
    {M₁ M₂ : SheafOfModules.{z} (toRingCat J Osharp)}
    {N₁ N₂ : SheafOfModules.{z₁} (toRingCat J Osharp)} (fg : (M₁, N₁) ⟶ (M₂, N₂)) :
    (Functor.prod (SheafOfModules.forget.{z} (toRingCat J Osharp))
        (SheafOfModules.forget.{z₁} (toRingCat J Osharp)) ⋙ (Functor.uncurry.obj
            (tensorBifunctor Osharp.obj))).map fg =
      tensorHom fg.1.val fg.2.val :=
  tensorBifunctor_uncurry_map fg.1.val fg.2.val

/-- The unit exhibiting the tensor product of two sheaves of modules as a sheafification,
composed with the base-change map: a morphism of presheaves of `O`-modules out of the
objectwise tensor product over `O` of the two sheaves of sections. -/
noncomputable abbrev tensorSheafUnitRestrict :
    tensorObj (restrictSheaf.{v, u, w, z} J a ((moduleSheafification.{v, u, w, z} J a).obj F))
        (restrictSheaf.{v, u, w, z₁} J a ((moduleSheafification.{v, u, w, z₁} J a).obj G)) ⟶
      restrictSheaf.{v, u, w, max z z₁} J a (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
        ((moduleSheafification.{v, u, w, z} J a).obj F,
          (moduleSheafification.{v, u, w, z₁} J a).obj G)) :=
  tensorBaseChange (toRingCatMap J a) ((moduleSheafification.{v, u, w, z} J a).obj F).val
      ((moduleSheafification.{v, u, w, z₁} J a).obj G).val ≫
    (restrictScalars (toRingCatMap J a)).map
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
          (tensorObj (((moduleSheafification.{v, u, w, z} J a).obj F)).val
            (((moduleSheafification.{v, u, w, z₁} J a).obj G)).val))

/-- The morphism of presheaves of `O`-modules from the objectwise tensor product of `F` and
`G` to the tensor product of their associated sheaves: on a pure tensor of sections it takes
the tensor product of the two sheafification-unit images, and then the unit exhibiting the
tensor product sheaf as a sheafification. -/
noncomputable def tensorSheafifyUnit :
    tensorObj F G ⟶ restrictSheaf J a (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
      ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G)) :=
  tensorHom (moduleSheafificationUnit.{v, u, w, z} J a F)
      (moduleSheafificationUnit.{v, u, w, z₁} J a G) ≫ tensorSheafUnitRestrict J a F G

/-- The comparison morphism from the associated sheaf of the objectwise tensor product of two
presheaves of modules to the tensor product of their associated sheaves. It is the morphism
descending `PresheafOfModules.tensorSheafifyUnit` along the sheafification unit. -/
noncomputable def tensorSheafifyComparison :
    (moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
        ((moduleSheafification.{v, u, w, z} J a).obj F,
          (moduleSheafification.{v, u, w, z₁} J a).obj G) :=
  ((sheafificationAdjunction (toRingCatMap J a)).homEquiv (tensorObj F G) _).symm
    (tensorSheafifyUnit J a F G)

/-- The comparison morphism `PresheafOfModules.tensorSheafifyComparison` sends the
sheafification-unit image of a pure tensor `x ⊗ₜ y` to the unit image of the pure tensor of the
sheafification-unit images of `x` and `y`. -/
@[simp]
lemma tensorSheafifyComparison_unit_tmul (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    Hom.app (tensorSheafifyComparison J a F G).val X
        (Hom.app (moduleSheafificationUnit.{v, u, w, max z z₁} J a (tensorObj F G)) X
          (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
          (tensorObj (((moduleSheafification.{v, u, w, z} J a).obj F)).val
            (((moduleSheafification.{v, u, w, z₁} J a).obj G)).val)) X
        (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a F) X x ⊗ₜ
          Hom.app (moduleSheafificationUnit.{v, u, w, z₁} J a G) X y) :=
  hom_congr_apply (sheafificationAdjunction_unit_comp_homEquiv_symm (toRingCatMap J a)
    (N := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁}
        Osharp))).obj
      ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G))
    (tensorSheafifyUnit J a F G)) X (x ⊗ₜ y)

/-- The bilinear map on sections of `F` and `G` given by the sheafification unit of their
objectwise tensor product. -/
noncomputable abbrev unitTensorBilinear :
    BilinearMap F G (restrictSheaf.{v, u, w, max z z₁} J a
      ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G))) :=
  toBilinear (F := F) (G := G)
    (moduleSheafificationUnit.{v, u, w, max z z₁} J a (tensorObj F G))

/-- The bilinear map on sections of the associated sheaf of `F` and of `G` obtained by
extending `PresheafOfModules.unitTensorBilinear` in the first variable. -/
noncomputable abbrev unitTensorBilinearLeft :
    BilinearMap
      (restrictSheaf.{v, u, w, z} J a ((moduleSheafification.{v, u, w, z} J a).obj F)) G
      (restrictSheaf.{v, u, w, max z z₁} J a
        ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G))) :=
  (BilinearMap.compLeftEquiv (N := G)
      (P := restrictSheaf.{v, u, w, max z z₁} J a
        ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)))
      ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).isSheaf
      (moduleSheafificationUnit.{v, u, w, z} J a F)).symm
    (unitTensorBilinear J a F G)

/-- The bilinear map on sections of the two associated sheaves which extends, in each variable, the
bilinear map `(x, y) ↦ η (x ⊗ y)` on sections of `F` and `G`. -/
noncomputable def tensorSheafifyBilinear :
    BilinearMap
      (restrictSheaf.{v, u, w, z} J a ((moduleSheafification.{v, u, w, z} J a).obj F))
      (restrictSheaf.{v, u, w, z₁} J a ((moduleSheafification.{v, u, w, z₁} J a).obj G))
      (restrictSheaf.{v, u, w, max z z₁} J a
        ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G))) :=
  (BilinearMap.compRightEquiv
      (M := restrictSheaf.{v, u, w, z} J a ((moduleSheafification.{v, u, w, z} J a).obj F))
      (P := restrictSheaf.{v, u, w, max z z₁} J a
        ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)))
      ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).isSheaf
      (moduleSheafificationUnit.{v, u, w, z₁} J a G)).symm
    (unitTensorBilinearLeft J a F G)

/-- `PresheafOfModules.tensorSheafifyBilinear`, on the sheafification-unit images of `x` and
`y`, is the sheafification-unit image of `x ⊗ₜ y`. -/
@[simp]
lemma tensorSheafifyBilinear_unit (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    (tensorSheafifyBilinear J a F G).app X
        (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a F) X x)
        (Hom.app (moduleSheafificationUnit.{v, u, w, z₁} J a G) X y) =
      Hom.app (moduleSheafificationUnit.{v, u, w, max z z₁} J a (tensorObj F G)) X
        (x ⊗ₜ y) :=
  (BilinearMap.congr_app
      ((BilinearMap.compRightEquiv
        (M := restrictSheaf.{v, u, w, z} J a ((moduleSheafification.{v, u, w, z} J a).obj F))
        (P := restrictSheaf.{v, u, w, max z z₁} J a
          ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)))
        ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).isSheaf
        (moduleSheafificationUnit.{v, u, w, z₁} J a G)).apply_symm_apply
      (unitTensorBilinearLeft J a F G)) X
      (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a F) X x) y).trans
    (BilinearMap.congr_app
      ((BilinearMap.compLeftEquiv (N := G)
        (P := restrictSheaf.{v, u, w, max z z₁} J a
          ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)))
        ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).isSheaf
        (moduleSheafificationUnit.{v, u, w, z} J a F)).apply_symm_apply
      (unitTensorBilinear J a F G)) X x y)

/-- The bilinear map `PresheafOfModules.tensorSheafifyBilinear`, upgraded to be bilinear over
the associated sheaf of rings. -/
noncomputable abbrev tensorSheafifyBilinearSharp :
    BilinearMap ((moduleSheafification.{v, u, w, z} J a).obj F).val
      ((moduleSheafification.{v, u, w, z₁} J a).obj G).val
      ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).val :=
  BilinearMap.ofRestrictScalars (toRingCatMap J a) (tensorSheafifyBilinear J a F G)
    ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).isSheaf.isSeparated

/-- The morphism of presheaves of `O♯`-modules descending the extended bilinear map. -/
noncomputable abbrev tensorSheafifyDescUnit :
    tensorObj ((moduleSheafification.{v, u, w, z} J a).obj F).val
        ((moduleSheafification.{v, u, w, z₁} J a).obj G).val ⟶
      ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)).val :=
  ofBilinear (F := ((moduleSheafification.{v, u, w, z} J a).obj F).val)
    (G := ((moduleSheafification.{v, u, w, z₁} J a).obj G).val)
    (tensorSheafifyBilinearSharp J a F G)

/-- The morphism from the tensor product of the two associated sheaves to the associated sheaf of
the objectwise tensor product, descending the extended bilinear map
`PresheafOfModules.tensorSheafifyBilinear`. -/
noncomputable def tensorSheafifyDesc :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
        ((moduleSheafification.{v, u, w, z} J a).obj F,
          (moduleSheafification.{v, u, w, z₁} J a).obj G) ⟶
      (moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G) :=
  ((sheafificationAdjunction (𝟙 (toRingCat J Osharp).obj)).homEquiv
      (tensorObj ((moduleSheafification.{v, u, w, z} J a).obj F).val
        ((moduleSheafification.{v, u, w, z₁} J a).obj G).val)
      ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G))).symm
    (tensorSheafifyDescUnit J a F G)

/-- `PresheafOfModules.tensorSheafifyDesc`, on the unit image of a pure tensor `A ⊗ₜ B`, is
`PresheafOfModules.tensorSheafifyBilinear` evaluated at `A` and `B`. -/
@[simp]
lemma tensorSheafifyDesc_unit_tmul (X : Cᵒᵖ)
    (A : ((moduleSheafification.{v, u, w, z} J a).obj F).val.obj X)
    (B : ((moduleSheafification.{v, u, w, z₁} J a).obj G).val.obj X) :
    Hom.app (tensorSheafifyDesc J a F G).val X
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
            (tensorObj (((moduleSheafification.{v, u, w, z} J a).obj F)).val
              (((moduleSheafification.{v, u, w, z₁} J a).obj G)).val)) X (A ⊗ₜ B)) =
      (tensorSheafifyBilinear J a F G).app X A B :=
  hom_congr_apply (sheafificationAdjunction_unit_comp_homEquiv_symm
    (𝟙 (toRingCat J Osharp).obj)
    (N := (moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G))
    (tensorSheafifyDescUnit J a F G)) X (A ⊗ₜ B)

/-- The comparison morphism is a section of the descended morphism. -/
lemma tensorSheafifyComparison_desc :
    tensorSheafifyComparison J a F G ≫ tensorSheafifyDesc J a F G =
      𝟙 ((moduleSheafification.{v, u, w, max z z₁} J a).obj (tensorObj F G)) := by
  refine sheafification_hom_ext (tensorObj_hom_ext (fun X x y ↦ ?_))
  exact ((congrArg (fun t ↦ Hom.app (tensorSheafifyDesc J a F G).val X t)
      (tensorSheafifyComparison_unit_tmul J a F G X x y)).trans
    ((tensorSheafifyDesc_unit_tmul J a F G X _ _).trans
      (tensorSheafifyBilinear_unit J a F G X x y)))

/-- The extended bilinear map `PresheafOfModules.tensorSheafifyBilinear`, followed by the
comparison morphism, is the pure-tensor map. -/
lemma tensorSheafifyBilinear_postcomp_comparison :
    (tensorSheafifyBilinear J a F G).postcomp
        ((SheafOfModules.forget (toRingCat J Osharp) ⋙ restrictScalars (toRingCatMap J a)).map
          (tensorSheafifyComparison J a F G)) =
      toBilinear (tensorSheafUnitRestrict J a F G) := by
  refine (BilinearMap.compRightEquiv
    (M := restrictSheaf.{v, u, w, z} J a ((moduleSheafification.{v, u, w, z} J a).obj F))
    (P := restrictSheaf.{v, u, w, max z z₁} J a (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
      ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G)))
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
      ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G)).isSheaf
    (moduleSheafificationUnit.{v, u, w, z₁} J a G)).injective ?_
  refine (BilinearMap.compLeftEquiv (N := G)
    (P := restrictSheaf.{v, u, w, max z z₁} J a (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
      ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G)))
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).obj
      ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G)).isSheaf
    (moduleSheafificationUnit.{v, u, w, z} J a F)).injective ?_
  refine BilinearMap.ext (fun X x y ↦ ?_)
  exact (congrArg (fun t ↦ Hom.app (tensorSheafifyComparison J a F G).val X t)
      (tensorSheafifyBilinear_unit J a F G X x y)).trans
    (tensorSheafifyComparison_unit_tmul J a F G X x y)

/-- The comparison morphism is a retraction of the descended morphism. -/
lemma tensorSheafifyDesc_comparison :
    tensorSheafifyDesc J a F G ≫ tensorSheafifyComparison J a F G =
      𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁}
          Osharp))).obj
        ((moduleSheafification.{v, u, w, z} J a).obj F,
          (moduleSheafification.{v, u, w, z₁} J a).obj G)) := by
  refine sheafification_hom_ext (tensorObj_hom_ext (fun X A B ↦ ?_))
  exact (congrArg (fun t ↦ Hom.app (tensorSheafifyComparison J a F G).val X t)
      (tensorSheafifyDesc_unit_tmul J a F G X A B)).trans
    (BilinearMap.congr_app (tensorSheafifyBilinear_postcomp_comparison J a F G) X A B)

section Naturality

variable {F₂ : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G₂ : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)} (f : F ⟶ F₂) (g : G ⟶ G₂)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{z₁}] [HasWeakSheafify J AddCommGrpCat.{z₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z z₁}]
  [HasWeakSheafify J AddCommGrpCat.{max z z₁}] in
/-- Naturality of the sheafification unit, with both values read in the module of sections of
the associated sheaf itself rather than in its restriction of scalars. -/
lemma unit_naturality_unrestrict_apply
    {M N : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)} (φ : M ⟶ N) (X : Cᵒᵖ)
    (x : M.obj X) :
    Hom.app ((moduleSheafification.{v, u, w, z} J a).map φ).val X
        (unrestrict (toRingCatMap J a) ((moduleSheafification.{v, u, w, z} J a).obj M).val
          (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a M) X x)) =
      unrestrict (toRingCatMap J a) ((moduleSheafification.{v, u, w, z} J a).obj N).val
        (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a N) X (Hom.app φ X x)) :=
  unit_naturality_apply (α := toRingCatMap J a) φ X x

/-- A pair of morphisms of presheaves of modules, sheafified, as a single morphism in the
product category. -/
noncomputable abbrev sheafifyPairMap :
    ((moduleSheafification.{v, u, w, z} J a).obj F,
        (moduleSheafification.{v, u, w, z₁} J a).obj G) ⟶
      ((moduleSheafification.{v, u, w, z} J a).obj F₂,
        (moduleSheafification.{v, u, w, z₁} J a).obj G₂) :=
  ((moduleSheafification.{v, u, w, z} J a).map f, (moduleSheafification.{v, u, w, z₁} J a).map g)

/-- The naturality square of the comparison morphism, evaluated on the sheafification-unit
image of a pure tensor of sections. -/
lemma tensorSheafifyComparison_naturality_apply (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    Hom.app (tensorSheafifyComparison J a F₂ G₂).val X
        (Hom.app ((moduleSheafification.{v, u, w, max z z₁} J a).map (tensorHom f g)).val X
          (Hom.app (moduleSheafificationUnit.{v, u, w, max z z₁} J a (tensorObj F G)) X
            (x ⊗ₜ y))) =
      Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁}
          Osharp))).map
          (sheafifyPairMap J a F G f g)).val X
        (Hom.app (tensorSheafifyComparison J a F G).val X
          (Hom.app (moduleSheafificationUnit.{v, u, w, max z z₁} J a (tensorObj F G)) X
            (x ⊗ₜ y))) := by
  rw [tensorSheafBifunctor_map]
  have e1 := unit_naturality_apply (α := toRingCatMap J a) (tensorHom f g) X (x ⊗ₜ y)
  have e2 := tensorSheafifyComparison_unit_tmul J a F₂ G₂ X (Hom.app f X x) (Hom.app g X y)
  have e3 := tensorSheafifyComparison_unit_tmul J a F G X x y
  have e4 := unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    ((Functor.prod (SheafOfModules.forget.{z} (toRingCat J Osharp))
      (SheafOfModules.forget.{z₁} (toRingCat J Osharp)) ⋙ (Functor.uncurry.obj
          (tensorBifunctor Osharp.obj))).map
        (sheafifyPairMap J a F G f g)) X
    (unrestrict (toRingCatMap J a) ((moduleSheafification.{v, u, w, z} J a).obj F).val
        (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a F) X x) ⊗ₜ
      unrestrict (toRingCatMap J a) ((moduleSheafification.{v, u, w, z₁} J a).obj G).val
        (Hom.app (moduleSheafificationUnit.{v, u, w, z₁} J a G) X y))
  refine ((congrArg (fun t ↦ Hom.app (tensorSheafifyComparison J a F₂ G₂).val X t) e1).trans
    e2).trans ?_
  refine (((congrArg (fun t ↦ Hom.app ((sheafification (𝟙 (toRingCat J Osharp).obj)).map
      ((Functor.prod (SheafOfModules.forget.{z} (toRingCat J Osharp))
        (SheafOfModules.forget.{z₁} (toRingCat J Osharp)) ⋙ (Functor.uncurry.obj
            (tensorBifunctor Osharp.obj))).map
          (sheafifyPairMap J a F G f g))).val X t) e3).trans e4).trans ?_).symm
  refine congrArg (fun t ↦ Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (tensorObj (((moduleSheafification.{v, u, w, z} J a).obj F₂)).val
        (((moduleSheafification.{v, u, w, z₁} J a).obj G₂)).val)) X t) ?_
  rw [prodForget_comp_tensorBifunctor_map]
  refine (tensorHom_tmul _ _ X _ _).trans ?_
  exact congrArg₂ (fun p q ↦ p ⊗ₜ[(Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj X] q)
    (unit_naturality_unrestrict_apply J a f X x) (unit_naturality_unrestrict_apply J a g X y)

/-- The comparison morphism is natural in both arguments. -/
lemma tensorSheafifyComparison_naturality :
    (moduleSheafification.{v, u, w, max z z₁} J a).map (tensorHom f g) ≫
        tensorSheafifyComparison J a F₂ G₂ =
      tensorSheafifyComparison J a F G ≫ ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp))).map
        (sheafifyPairMap J a F G f g) :=
  sheafification_hom_ext (tensorObj_hom_ext
    (fun X x y ↦ tensorSheafifyComparison_naturality_apply J a F G f g X x y))

end Naturality

/-- Sheafification commutes with the tensor product of presheaves of modules: there is an
isomorphism `F⁺ ⊗_{O⁺} G⁺ ≅ (F ⊗_{p,O} G)⁺`, natural in both presheaves of modules, where the
left-hand tensor product is the sheafification of the objectwise tensor product of the two sheaves
of sections. -/
@[stacks 0GMW]
noncomputable def sheafificationTensorIso :
    Functor.prod (moduleSheafification.{v, u, w, z} J a)
          (moduleSheafification.{v, u, w, z₁} J a) ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp)) ≅
      Functor.uncurry.obj (tensorBifunctor.{v, u, w, z, z₁} O) ⋙
        moduleSheafification.{v, u, w, max z z₁} J a :=
  (NatIso.ofComponents
    (fun PP ↦
      { hom := tensorSheafifyComparison.{v, u, w, z, z₁} J a PP.1 PP.2
        inv := tensorSheafifyDesc.{v, u, w, z, z₁} J a PP.1 PP.2
        hom_inv_id := tensorSheafifyComparison_desc.{v, u, w, z, z₁} J a PP.1 PP.2
        inv_hom_id := tensorSheafifyDesc_comparison.{v, u, w, z, z₁} J a PP.1 PP.2 })
    (fun {sourcePair targetPair} pairHom ↦ by
      rcases pairHom with ⟨leftHom, rightHom⟩
      exact (congrArg
        (fun morphism => (moduleSheafification.{v, u, w, max z z₁} J a).map morphism ≫
          tensorSheafifyComparison.{v, u, w, z, z₁} J a targetPair.1 targetPair.2)
        (tensorBifunctor_uncurry_map leftHom rightHom)).trans
        (tensorSheafifyComparison_naturality.{v, u, w, z, z₁} J a sourcePair.1 sourcePair.2
          leftHom rightHom))).symm

/-- The isomorphism `sheafificationTensorIso` sends the image, under the unit exhibiting the tensor
product sheaf as a sheafification, of a pure tensor of two sheafification-unit images to the
sheafification-unit image of the original pure tensor. -/
@[stacks 0GMW]
lemma sheafificationTensorIso_hom_unit_tmul (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U) :
    Hom.app ((sheafificationTensorIso.{v, u, w, z, z₁} J a).hom.app (F, G)).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
            (tensorObj (((moduleSheafification.{v, u, w, z} J a).obj F)).val
              (((moduleSheafification.{v, u, w, z₁} J a).obj G)).val)) U
          (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a F) U x ⊗ₜ
            Hom.app (moduleSheafificationUnit.{v, u, w, z₁} J a G) U y)) =
      Hom.app (moduleSheafificationUnit.{v, u, w, max z z₁} J a (tensorObj F G)) U (x ⊗ₜ y) :=
  (tensorSheafifyDesc_unit_tmul J a F G U _ _).trans (tensorSheafifyBilinear_unit J a F G U x y)

/-- Sheafification inverts the canonical tensor product of its two adjunction units. -/
lemma isIso_sheafification_tensor_units :
    IsIso ((moduleSheafification.{v, u, w, max z z₁} J a).map
      (tensorHom (moduleSheafificationUnit.{v, u, w, z} J a F)
        (moduleSheafificationUnit.{v, u, w, z₁} J a G))) := by
  let leftUnit := moduleSheafificationUnit.{v, u, w, z} J a F
  let rightUnit := moduleSheafificationUnit.{v, u, w, z₁} J a G
  let : IsIso ((moduleSheafification.{v, u, w, z} J a).map leftUnit) :=
    sheafification_map_unit_isIso (toRingCat J Osharp) (toRingCatMap J a) F
  let : IsIso ((moduleSheafification.{v, u, w, z₁} J a).map rightUnit) :=
    sheafification_map_unit_isIso (toRingCat J Osharp) (toRingCatMap J a) G
  have mappedPairIsIso : IsIso
      ((Functor.prod (moduleSheafification.{v, u, w, z} J a)
          (moduleSheafification.{v, u, w, z₁} J a) ⋙
        Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp)).map
        ((leftUnit, rightUnit) : (F, G) ⟶ (_, _))) := by
    let mappedPairIso :
        ((moduleSheafification.{v, u, w, z} J a).obj F,
          (moduleSheafification.{v, u, w, z₁} J a).obj G) ≅ (_, _) :=
      { hom := ((moduleSheafification.{v, u, w, z} J a).map leftUnit,
          (moduleSheafification.{v, u, w, z₁} J a).map rightUnit)
        inv := (inv ((moduleSheafification.{v, u, w, z} J a).map leftUnit),
          inv ((moduleSheafification.{v, u, w, z₁} J a).map rightUnit))
        hom_inv_id := Prod.ext (IsIso.hom_inv_id _) (IsIso.hom_inv_id _)
        inv_hom_id := Prod.ext (IsIso.inv_hom_id _) (IsIso.inv_hom_id _) }
    change IsIso ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp)).map
      (((moduleSheafification.{v, u, w, z} J a).map leftUnit,
        (moduleSheafification.{v, u, w, z₁} J a).map rightUnit) :
        ((moduleSheafification.{v, u, w, z} J a).obj F,
          (moduleSheafification.{v, u, w, z₁} J a).obj G) ⟶ (_, _)))
    exact Iso.isIso_hom ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp)).mapIso mappedPairIso)
  have mappedTensorIsIso := (NatIso.isIso_map_iff
    (sheafificationTensorIso.{v, u, w, z, z₁} J a)
      ((leftUnit, rightUnit) : (F, G) ⟶ (_, _))).mp mappedPairIsIso
  exact (congrArg (fun morphism => IsIso morphism)
    (congrArg (fun morphism => (moduleSheafification.{v, u, w, max z z₁} J a).map morphism)
      (tensorBifunctor_uncurry_map leftUnit rightUnit))).mp mappedTensorIsIso

end TensorSheafify

end PresheafOfModules
