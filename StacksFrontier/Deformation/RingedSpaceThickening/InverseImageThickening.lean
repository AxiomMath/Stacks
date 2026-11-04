module

public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtension
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.Stalk.PullbackUnit
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentInverseImageExt

/-!
# The inverse image of a square-zero thickening, and the map `g⁻¹ℱ ⟶ 𝒢`

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces,
`0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` an extension of `f⁻¹𝒪_S`-algebras with `ℱ` of square zero, `𝒢` an
`𝒪_Y`-module and `c : ℱ ⟶ g_*𝒢` a `g`-map. This file provides the ingredients of the first
construction of **Stacks 0GQ2** on `Y`:

* the ringed space `(Y, g⁻¹𝒪_X)` (`inverseImageRingedSpace`) and its morphism to `S`
  (`inverseImageSpaceHom`), with the identification of the structure map of `g ≫ f` through it
  (`ringedSpaceStructureMap_comp_eq`);
* `g⁻¹𝒪_{X'}`, its reduction `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` (surjective:
  `isLocallySurjective_inverseImageReduction`) and its `g⁻¹f⁻¹𝒪_S`-algebra structure
  (`inverseImageBase`);
* the map `c : g⁻¹ℱ ⟶ 𝒢` on the kernel `g⁻¹ℱ` of the reduction (`idealMap`), characterised by
  `idealMap_app_unitSec`: on the image of a section `a` of `ℱ ⊆ 𝒪_{X'}` it is `c(a)`.

## Implementation notes

The inverse image is Mathlib's `TopCat.Sheaf.pullback`, an abstract left adjoint; all local
computations go through the stalk comparison `Stacks.Sheaves.PullbackUnit.stalkComparison`, by
which every section of the inverse image is locally the image of a section
(`Stacks.Sheaves.PullbackUnit.exists_restrict_eq_unit`). The kernel of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` is
locally the image of `ℱ` (`exists_localRep`), and two sections of `ℱ` with the same image near a
point agree near its image (`exists_eq_of_germ_unitSec_eq`); so the values `c(a)` glue
(`exists_glued_value`). This is the exactness of `g⁻¹` used by the source.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (f : X ⟶ S) (g : Y ⟶ X)

/-- The ringed space `(Y, g⁻¹𝒪_X)`. It is the ringed space
`AlgebraicGeometry.RingedSpaceThickening.inverseImageSpace g`, that is
`AlgebraicGeometry.RingedSpace.inverseImage X g.hom.base` (`inverseImageRingedSpace_eq`), with
its fields spelled out so that its underlying space is reducibly the space of `Y`.

The explicit presentation is needed because `AlgebraicGeometry.RingedSpace.inverseImage` is a
plain definition: through it, `(inverseImageSpace g).carrier` is the space of `Y` only after
unfolding that definition, which instance search and unification at reducible transparency do
not do. Every sheaf of modules on `(Y, g⁻¹𝒪_X)` built in this development is compared with
sheaves on `Y` (restriction of scalars along `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`, the lift
`(Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X)` with identity underlying map), and over the base presentation those
comparisons fail: the category of sheaves of modules over `𝒪_Y` is no longer found, and the
pullback–pushforward adjunctions along the projection no longer agree componentwise by `rfl`. -/
abbrev inverseImageRingedSpace : RingedSpace.{u, u} where
  carrier := Y.carrier
  presheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj
  IsSheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).property

/-- **`inverseImageRingedSpace g` is the ringed space `inverseImageSpace g`**, the
inverse-image ringed space `(Y, g⁻¹𝒪_X)`; the two differ only in how their fields are
presented. -/
theorem inverseImageRingedSpace_eq : inverseImageRingedSpace g = inverseImageSpace g :=
  rfl

/-- `(Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X) ⟶ (S, 𝒪_S)`. -/
abbrev inverseImageSpaceHom : inverseImageRingedSpace g ⟶ S :=
  (show inverseImageRingedSpace g ⟶ X from RingedSpace.inverseImageProjection X g.hom.base) ≫ f

/-- `𝒢`, an `𝒪_Y`-module, read as a `g⁻¹𝒪_X`-module through `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
abbrev restrictedModule (G : SheafOfModules.{u} (structureSheafRing Y)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageRingedSpace g).sheaf) :=
  (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology Y.carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (ringedSpaceStructureMap g))).obj G

/-- The inverse-image/direct-image adjunction for sheaves of commutative rings. -/
abbrev adjP {T T' : TopCat.{u}} (k : T ⟶ T') :=
  TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} k

/-- The structure map of a morphism of ringed spaces is the adjoint transpose of its
comorphism. -/
theorem ringedSpaceStructureMap_eq_iff {T T' : RingedSpace.{u, u}} (k : T ⟶ T')
    (a : (TopCat.Sheaf.pullback CommRingCat.{u} k.hom.base).obj T'.sheaf ⟶ T.sheaf) :
    ringedSpaceStructureMap k = a ↔ ((adjP k.hom.base).homEquiv _ _ a).hom = k.hom.c := by
  constructor
  · rintro rfl
    exact congrArg (fun t => t.hom) (((adjP k.hom.base).homEquiv _ _).apply_symm_apply _)
  · intro h
    refine ((adjP k.hom.base).homEquiv _ _).injective ?_
    refine (((adjP k.hom.base).homEquiv _ _).apply_symm_apply _).trans ?_
    exact Sheaf.hom_ext h.symm

/-- The structure sheaf datum of a morphism, as the unit followed by the pushforward of the
structure map. -/
theorem c_eq_unit_comp {T T' : RingedSpace.{u, u}} (k : T ⟶ T') :
    k.hom.c = ((adjP k.hom.base).unit.app T'.sheaf).hom ≫
      (TopCat.Presheaf.pushforward CommRingCat.{u} k.hom.base).map
        (ringedSpaceStructureMap k).hom := by
  rw [← (ringedSpaceStructureMap_eq_iff k (ringedSpaceStructureMap k)).1 rfl,
    Adjunction.homEquiv_unit]
  rfl

/-- The structure map `g⁻¹f⁻¹𝒪_S ⟶ g⁻¹𝒪_X` of `(Y, g⁻¹𝒪_X)` over `S`. -/
abbrev baseToMid : inverseImageBaseRing (g ≫ f) ⟶
    (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  ringedSpaceStructureMap (inverseImageSpaceHom f g)

/-- The adjoint transpose of the structure map is the comorphism. -/
theorem homEquiv_ringedSpaceStructureMap {T T' : RingedSpace.{u, u}} (k : T ⟶ T') :
    (adjP k.hom.base).homEquiv _ _ (ringedSpaceStructureMap k) = ObjectProperty.homMk k.hom.c :=
  ((adjP k.hom.base).homEquiv _ _).apply_symm_apply _

/-- The structure map of `g ≫ f` factors through `(Y, g⁻¹𝒪_X)`. -/
theorem ringedSpaceStructureMap_comp_eq :
    ringedSpaceStructureMap (g ≫ f) = baseToMid f g ≫ ringedSpaceStructureMap g := by
  refine ((adjP (g ≫ f).hom.base).homEquiv _ _).injective ?_
  refine (homEquiv_ringedSpaceStructureMap (g ≫ f)).trans ?_
  refine Eq.trans ?_ ((adjP (g ≫ f).hom.base).homEquiv_naturality_right _ _).symm
  refine Eq.trans ?_ (congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (g ≫ f).hom.base).map (ringedSpaceStructureMap g))
    (homEquiv_ringedSpaceStructureMap (inverseImageSpaceHom f g))).symm
  apply Sheaf.hom_ext
  show f.hom.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.hom.base).map g.hom.c =
    (f.hom.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.hom.base).map
      ((adjP g.hom.base).unit.app X.sheaf).hom) ≫
      (TopCat.Presheaf.pushforward CommRingCat.{u} f.hom.base).map
        ((TopCat.Presheaf.pushforward CommRingCat.{u} g.hom.base).map
          (ringedSpaceStructureMap g).hom)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (f.hom.c ≫ ·) ?_
  refine Eq.trans ?_ (Functor.map_comp _ _ _)
  exact congrArg _ (c_eq_unit_comp g)

/-- Two restrictions of a section of a presheaf of rings on a space compose to the restriction
along any inclusion. -/
theorem ringMap_map {T : TopCat.{u}} (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {U V W : Opens T}
    (j : V ⟶ U) (i : W ⟶ V) (k : W ⟶ U) (x : R.obj (op U)) :
    (R.map i.op).hom ((R.map j.op).hom x) = (R.map k.op).hom x := by
  rw [← CommRingCat.comp_apply, ← R.map_comp, show j.op ≫ i.op = k.op from rfl]

/-! ### The inverse image of the thickening `𝒪_{X'}` -/

section InverseImage

variable {f g} {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : SquareZeroAlgebraExtension f F)

/-- `g⁻¹𝒪_{X'}`, the inverse image along `g` of the extended structure sheaf. -/
abbrev inverseImageRing : Sheaf (Opens.grothendieckTopology Y.carrier) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj P.sheaf

/-- `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X`, the inverse image of the reduction. -/
abbrev inverseImageReduction : inverseImageRing (g := g) P ⟶
    (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map P.reduction

variable (g) in
/-- The unit `𝒪_{X'}(U) ⟶ (g⁻¹𝒪_{X'})(g⁻¹U)` of the inverse-image adjunction, on sections. -/
abbrev unitSec (R : TopCat.Sheaf CommRingCat.{u} X.carrier) (U : Opens X.carrier) :
    R.obj.obj (op U) →+*
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj R).obj.obj
        (op ((Opens.map g.hom.base).obj U)) :=
  (((adjP g.hom.base).unit.app R).hom.app (op U)).hom

variable (g) in
/-- The unit is natural in the sheaf of rings. -/
theorem unitSec_naturality {R R' : TopCat.Sheaf CommRingCat.{u} X.carrier} (φ : R ⟶ R')
    (U : Opens X.carrier) (a : R.obj.obj (op U)) :
    unitSec g R' U ((φ.hom.app (op U)).hom a) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map φ).hom.app
        (op ((Opens.map g.hom.base).obj U))).hom (unitSec g R U a) :=
  congrArg (fun t : R ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj R') => (t.hom.app (op U)).hom a)
    ((adjP g.hom.base).unit.naturality φ)

variable (g) in
/-- The unit commutes with restriction. -/
theorem unitSec_map (R : TopCat.Sheaf CommRingCat.{u} X.carrier) {U U' : Opens X.carrier}
    (i : U' ⟶ U) (a : R.obj.obj (op U)) :
    unitSec g R U' ((R.obj.map i.op).hom a) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj R).obj.map
        ((Opens.map g.hom.base).map i).op).hom (unitSec g R U a) :=
  NatTrans.naturality_apply ((adjP g.hom.base).unit.app R).hom i.op a

variable (g) in
/-- **Two sections of a sheaf of rings with the same image in the inverse image near `y` agree
near `g y`.**  The stalk comparison of the unit is an isomorphism. -/
theorem exists_eq_of_germ_unitSec_eq (R : TopCat.Sheaf CommRingCat.{u} X.carrier)
    {U₁ U₂ : Opens X.carrier} (a₁ : R.obj.obj (op U₁)) (a₂ : R.obj.obj (op U₂)) (y : Y.carrier)
    (h₁ : g.hom.base y ∈ U₁) (h₂ : g.hom.base y ∈ U₂)
    (h : ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj R).presheaf.germ _ y h₁
        (unitSec g R U₁ a₁) =
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj R).presheaf.germ _ y h₂
        (unitSec g R U₂ a₂)) :
    ∃ (U : Opens X.carrier) (_ : g.hom.base y ∈ U) (i₁ : U ⟶ U₁) (i₂ : U ⟶ U₂),
      (R.obj.map i₁.op).hom a₁ = (R.obj.map i₂.op).hom a₂ := by
  have hiso := Stacks.Sheaves.PullbackUnit.isIso_stalkComparison g.hom.base R y
  have e : ∀ (U : Opens X.carrier) (hU : g.hom.base y ∈ U) (a : R.obj.obj (op U)),
      Stacks.Sheaves.PullbackUnit.stalkComparison g.hom.base CommRingCat.{u}
          ((adjP g.hom.base).unit.app R).hom y (R.presheaf.germ U (g.hom.base y) hU a) =
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj R).presheaf.germ _ y hU
          (unitSec g R U a) := fun U hU a =>
    congrArg (fun t => (ConcreteCategory.hom t) a)
      (Stacks.Sheaves.PullbackUnit.germ_stalkComparison g.hom.base CommRingCat.{u}
        ((adjP g.hom.base).unit.app R).hom y U hU)
  have hinj : Function.Injective (ConcreteCategory.hom
      (Stacks.Sheaves.PullbackUnit.stalkComparison g.hom.base CommRingCat.{u}
        ((adjP g.hom.base).unit.app R).hom y)) := by
    intro x x' hx
    have hl := congrArg (fun t => (ConcreteCategory.hom t) x) (@IsIso.hom_inv_id _ _ _ _ _ hiso)
    have hr := congrArg (fun t => (ConcreteCategory.hom t) x') (@IsIso.hom_inv_id _ _ _ _ _ hiso)
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at hl hr
    rw [← hl, ← hr, hx]
  exact R.presheaf.germ_eq (g.hom.base y) h₁ h₂ a₁ a₂
    (hinj ((e U₁ h₁ a₁).trans (h.trans (e U₂ h₂ a₂).symm)))

/-- **The inverse image of the reduction is surjective.** Locally a section of `g⁻¹𝒪_X` is the
image of a section of `𝒪_X`, which lifts locally to `𝒪_{X'}`. -/
instance isLocallySurjective_inverseImageReduction :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageReduction (g := g) P).hom where
  imageSieve_mem {V} b := by
    intro y hy
    obtain ⟨U, W, hyW, iV, iU, a, hab⟩ :=
      Stacks.Sheaves.PullbackUnit.exists_restrict_eq_unit g.hom.base X.sheaf y V hy b
    have hgy : g.hom.base y ∈ U := iU.le hyW
    have := P.reduction_surjective
    obtain ⟨U', iU', ⟨a', ha'⟩, hU'⟩ :=
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology X.carrier) P.reduction.hom a)
        (g.hom.base y) hgy
    refine ⟨W ⊓ (Opens.map g.hom.base).obj U', homOfLE (inf_le_left.trans iV.le),
      ⟨unitSec g P.sheaf U' a' |> fun z =>
        (((inverseImageRing (g := g) P).obj.map
          (homOfLE (inf_le_right : W ⊓ (Opens.map g.hom.base).obj U' ≤ _)).op).hom z), ?_⟩,
      ⟨hyW, hU'⟩⟩
    let W' := W ⊓ (Opens.map g.hom.base).obj U'
    change ((inverseImageReduction (g := g) P).hom.app (op W')).hom
        (((inverseImageRing (g := g) P).obj.map (homOfLE inf_le_right).op).hom
          (unitSec g P.sheaf U' a')) =
      (((inverseImageRingedSpace g).sheaf.obj.map (homOfLE (inf_le_left.trans iV.le)).op).hom b)
    have e1 := NatTrans.naturality_apply (inverseImageReduction (g := g) P).hom
      (homOfLE (inf_le_right : W' ≤ (Opens.map g.hom.base).obj U')).op (unitSec g P.sheaf U' a')
    have e2 := unitSec_naturality g P.reduction U' a'
    have e3 := unitSec_map g X.sheaf iU' a
    let R₁ := ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj
    refine e1.trans ?_
    refine (congrArg (fun z => (R₁.map (homOfLE inf_le_right : W' ⟶ _).op).hom z) e2.symm).trans ?_
    refine (congrArg (fun z => (R₁.map (homOfLE inf_le_right : W' ⟶ _).op).hom
      (unitSec g X.sheaf U' z)) ha').trans ?_
    refine (congrArg (fun z => (R₁.map (homOfLE inf_le_right : W' ⟶ _).op).hom z) e3).trans ?_
    refine (ringMap_map R₁ _ _ (homOfLE (inf_le_left.trans iU.le)) _).trans ?_
    refine (ringMap_map R₁ iU (homOfLE inf_le_left) _ _).symm.trans ?_
    refine (congrArg (fun z => (R₁.map (homOfLE inf_le_left : W' ⟶ W).op).hom z) hab.symm).trans ?_
    exact ringMap_map R₁ iV _ _ _

/-- `g⁻¹f⁻¹𝒪_S ⟶ g⁻¹𝒪_{X'}`, the `g⁻¹f⁻¹𝒪_S`-algebra structure of `g⁻¹𝒪_{X'}`: the adjoint
transpose of `𝒪_S ⟶ f_*𝒪_{X'} ⟶ f_*g_*g⁻¹𝒪_{X'}`, the structure map of `X'` over `S` followed by
the unit of the inverse image along `g`. -/
def inverseImageBase : inverseImageBaseRing (g ≫ f) ⟶ inverseImageRing (g := g) P :=
  ((adjP (g ≫ f).hom.base).homEquiv _ _).symm
    ((adjP f.hom.base).homEquiv _ _ P.base ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        ((adjP g.hom.base).unit.app P.sheaf))

/-- The adjoint transpose of `g⁻¹f⁻¹𝒪_S ⟶ g⁻¹𝒪_{X'}`. -/
theorem homEquiv_inverseImageBase :
    (adjP (g ≫ f).hom.base).homEquiv _ _ (inverseImageBase P) =
      (adjP f.hom.base).homEquiv _ _ P.base ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          ((adjP g.hom.base).unit.app P.sheaf) :=
  ((adjP (g ≫ f).hom.base).homEquiv _ _).apply_symm_apply _

/-- **`g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` is a morphism of `g⁻¹f⁻¹𝒪_S`-algebras**: composed with the structure
map of `g⁻¹𝒪_{X'}` it is the structure map of `(Y, g⁻¹𝒪_X)` over `S`. -/
theorem inverseImageBase_comp_inverseImageReduction :
    inverseImageBase P ≫ inverseImageReduction (g := g) P = baseToMid f g := by
  refine ((adjP (g ≫ f).hom.base).homEquiv _ _).injective ?_
  refine ((adjP (g ≫ f).hom.base).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (g ≫ f).hom.base).map (inverseImageReduction (g := g) P))
      (homEquiv_inverseImageBase P)).trans ?_
  refine Eq.trans ?_ (homEquiv_ringedSpaceStructureMap (inverseImageSpaceHom f g)).symm
  refine (Category.assoc _ _ _).trans ?_
  have hu : P.reduction ≫ (adjP g.hom.base).unit.app X.sheaf =
      (adjP g.hom.base).unit.app P.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
          (inverseImageReduction (g := g) P) :=
    (adjP g.hom.base).unit.naturality P.reduction
  have e1 : (adjP f.hom.base).homEquiv _ _ P.base ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map P.reduction =
      ObjectProperty.homMk f.hom.c :=
    ((adjP f.hom.base).homEquiv_naturality_right P.base P.reduction).symm.trans
      ((congrArg _ P.base_comp_reduction).trans (homEquiv_ringedSpaceStructureMap f))
  let Hf := TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base
  let Hg := TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base
  show (adjP f.hom.base).homEquiv _ _ P.base ≫ Hf.map ((adjP g.hom.base).unit.app P.sheaf) ≫
      Hf.map (Hg.map (inverseImageReduction (g := g) P)) = _
  refine (congrArg (_ ≫ ·) (Hf.map_comp _ _).symm).trans ?_
  refine (congrArg (fun t => (adjP f.hom.base).homEquiv _ _ P.base ≫ Hf.map t) hu.symm).trans ?_
  refine (congrArg (_ ≫ ·) (Hf.map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ Hf.map ((adjP g.hom.base).unit.app X.sheaf)) e1).trans ?_
  rfl

/-! ### The map `g⁻¹ℱ ⟶ 𝒢` on the kernel of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` -/

section IdealMap

variable (G : SheafOfModules.{u} (structureSheafRing Y)) (c : F ⟶ (modulePushforward g).obj G)

/-- Two restrictions of a section of a sheaf of modules on a space compose to the restriction
along any inclusion. -/
theorem moduleMap_map {T : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing T))
    {U V W : Opens T.carrier} (j : V ⟶ U) (i : W ⟶ V) (k : W ⟶ U) (x : M.val.obj (op U)) :
    M.val.map i.op (M.val.map j.op x) = M.val.map k.op x :=
  (M.val.map_comp_apply j.op i.op x).symm

/-- A section of a sheaf of modules on a space is determined by its restrictions to a
neighbourhood of each point. -/
theorem moduleSection_ext {T : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing T))
    {V : Opens T.carrier} (t t' : M.val.obj (op V))
    (h : ∀ y ∈ V, ∃ (W : Opens T.carrier) (_ : y ∈ W) (i : W ⟶ V),
      M.val.map i.op t = M.val.map i.op t') : t = t' := by
  let Msh : TopCat.Sheaf AddCommGrpCat.{u} T.carrier := ⟨M.val.presheaf, M.isSheaf⟩
  choose W hW i hi using fun y : V => h y.1 y.2
  exact Msh.eq_of_locally_eq' W V i (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hW ⟨y, hy⟩⟩) t t' hi

/-- `c(ρ(a)) ∈ 𝒢(g⁻¹U)` for a local section `a` of the ideal of `𝒪_{X'}`, `ρ` the identification
of that ideal with `ℱ`. -/
def idealValue (U : Opens X.carrier) (a : kernelIdeal P.reduction.hom (op U)) :
    G.val.obj (op ((Opens.map g.hom.base).obj U)) :=
  c.val.app (op U) (P.ideal.app (op U) a)

/-- `idealValue` commutes with restriction. -/
theorem idealValue_map {U U' : Opens X.carrier} (i : U' ⟶ U)
    (a : kernelIdeal P.reduction.hom (op U)) :
    idealValue P G c U' ⟨(P.sheaf.obj.map i.op).hom a.1,
        Stacks.Sites.Conormal.map_kernel P.reduction.hom i.op a.2⟩ =
      G.val.map ((Opens.map g.hom.base).map i).op (idealValue P G c U a) := by
  unfold idealValue
  rw [P.ideal.app_map]
  exact PresheafOfModules.naturality_apply c.val i.op _

/-- A local representation of a section `s` of `g⁻¹𝒪_{X'}` over `V`: on an open `W ⊆ V`, `s`
is the image of a section `a` of the ideal of `𝒪_{X'}` over an open `U` with `W ⊆ g⁻¹U`. -/
structure LocalRep (V : Opens Y.carrier) (s : (inverseImageRing (g := g) P).obj.obj (op V)) where
  /-- The open of `Y` on which the representation holds. -/
  W : Opens Y.carrier
  /-- It lies in `V`. -/
  le_V : W ≤ V
  /-- The open of `X`. -/
  U : Opens X.carrier
  /-- `W` lies over it. -/
  le_U : W ≤ (Opens.map g.hom.base).obj U
  /-- The section of the ideal of `𝒪_{X'}`. -/
  a : kernelIdeal P.reduction.hom (op U)
  /-- On `W`, `s` is the image of `a`. -/
  eq : ((inverseImageRing (g := g) P).obj.map (homOfLE le_V).op).hom s =
    ((inverseImageRing (g := g) P).obj.map (homOfLE le_U).op).hom (unitSec g P.sheaf U a.1)

variable {P G c}

/-- Two sections with the same restriction to `W` have the same germ at each point of `W`. -/
private theorem germ_eq_of_map_eq {T : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} T)
    {U₁ U₂ W : Opens T} (i₁ : W ⟶ U₁) (i₂ : W ⟶ U₂) {y : T} (hy : y ∈ W) (a₁ : R.obj (op U₁))
    (a₂ : R.obj (op U₂)) (h : (R.map i₁.op).hom a₁ = (R.map i₂.op).hom a₂) :
    R.germ U₁ y (i₁.le hy) a₁ = R.germ U₂ y (i₂.le hy) a₂ := by
  rw [← TopCat.Presheaf.germ_res_apply R i₁ y hy, ← TopCat.Presheaf.germ_res_apply R i₂ y hy, h]

/-- If `s` is, near `W`, the image of `a` in `g⁻¹𝒪_{X'}`, then on `W' ≤ W` over a smaller `U'`
it is the image of the restriction of `a` to `U'`. -/
private theorem restrict_eq_unitSec_map {V : Opens Y.carrier}
    {s : (inverseImageRing (g := g) P).obj.obj (op V)} {W W' : Opens Y.carrier}
    {U U' : Opens X.carrier} (iV : W ⟶ V) (iU : W ⟶ (Opens.map g.hom.base).obj U)
    (a : P.sheaf.obj.obj (op U))
    (h : ((inverseImageRing (g := g) P).obj.map iV.op).hom s =
      ((inverseImageRing (g := g) P).obj.map iU.op).hom (unitSec g P.sheaf U a))
    (i : U' ⟶ U) (hW : W' ≤ W) (hW' : W' ≤ (Opens.map g.hom.base).obj U') :
    ((inverseImageRing (g := g) P).obj.map (homOfLE (hW.trans iV.le)).op).hom s =
      ((inverseImageRing (g := g) P).obj.map (homOfLE hW').op).hom
        (unitSec g P.sheaf U' ((P.sheaf.obj.map i.op).hom a)) := by
  let A' := (inverseImageRing (g := g) P).obj
  rw [unitSec_map g P.sheaf i a, ringMap_map A' _ _ (homOfLE (hW'.trans
      ((Opens.map g.hom.base).map i).le)),
    ← ringMap_map A' iV (homOfLE hW) (homOfLE (hW.trans iV.le)), h]
  exact ringMap_map A' iU _ _ _

/-- **The values of `c` attached to two representations agree where the representations do.**
Where the images of `a₁` and `a₂` in `g⁻¹𝒪_{X'}` agree, `a₁` and `a₂` agree near the image
point, by the stalk comparison, and so do their images under `c ∘ ρ`. -/
theorem idealValue_eq_of_unitSec_eq {U₁ U₂ : Opens X.carrier}
    (a₁ : kernelIdeal P.reduction.hom (op U₁)) (a₂ : kernelIdeal P.reduction.hom (op U₂))
    {W : Opens Y.carrier} (h₁ : W ≤ (Opens.map g.hom.base).obj U₁)
    (h₂ : W ≤ (Opens.map g.hom.base).obj U₂)
    (h : ((inverseImageRing (g := g) P).obj.map (homOfLE h₁).op).hom (unitSec g P.sheaf U₁ a₁.1) =
      ((inverseImageRing (g := g) P).obj.map (homOfLE h₂).op).hom (unitSec g P.sheaf U₂ a₂.1)) :
    G.val.map (homOfLE h₁).op (idealValue P G c U₁ a₁) =
      G.val.map (homOfLE h₂).op (idealValue P G c U₂ a₂) := by
  refine moduleSection_ext (V := W) G _ _ fun y hy => ?_
  obtain ⟨U, hU, i₁, i₂, hU'⟩ := exists_eq_of_germ_unitSec_eq g P.sheaf a₁.1 a₂.1 y (h₁ hy) (h₂ hy)
    (germ_eq_of_map_eq _ (homOfLE h₁) (homOfLE h₂) hy _ _ h)
  refine ⟨W ⊓ (Opens.map g.hom.base).obj U, ⟨hy, hU⟩, homOfLE inf_le_left, ?_⟩
  rw [moduleMap_map G (homOfLE h₁) (homOfLE inf_le_left) (homOfLE (inf_le_left.trans h₁)),
    moduleMap_map G (homOfLE h₂) (homOfLE inf_le_left) (homOfLE (inf_le_left.trans h₂)),
    ← moduleMap_map G ((Opens.map g.hom.base).map i₁) (homOfLE inf_le_right)
      (homOfLE (inf_le_left.trans h₁)),
    ← moduleMap_map G ((Opens.map g.hom.base).map i₂) (homOfLE inf_le_right)
      (homOfLE (inf_le_left.trans h₂)),
    ← idealValue_map, ← idealValue_map]
  exact congrArg (fun z => G.val.map (homOfLE (inf_le_right :
    W ⊓ (Opens.map g.hom.base).obj U ≤ _)).op (idealValue P G c U z)) (Subtype.ext hU')

variable (P G c) in
/-- The value of `c` attached to a local representation, on the open where it holds. -/
def LocalRep.value {V : Opens Y.carrier} {s : (inverseImageRing (g := g) P).obj.obj (op V)}
    (r : LocalRep P V s) : G.val.obj (op r.W) :=
  G.val.map (homOfLE r.le_U).op (idealValue P G c r.U r.a)

/-- **Every section of the kernel of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` is locally the image of a section of
the ideal of `𝒪_{X'}`.**  Locally it is the image of a section `a` of `𝒪_{X'}`; the image of
`a` in `𝒪_X` then has zero image in `g⁻¹𝒪_X` near the point, so it vanishes near the image point
by the stalk comparison, and `a` restricted there lies in the ideal. -/
theorem exists_localRep (V : Opens Y.carrier) (s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) (y : Y.carrier)
    (hy : y ∈ V) : ∃ r : LocalRep P V s, y ∈ r.W := by
  obtain ⟨U, W, hyW, iV, iU, a, hab⟩ :=
    Stacks.Sheaves.PullbackUnit.exists_restrict_eq_unit g.hom.base P.sheaf y V hy s
  have hgy : g.hom.base y ∈ U := iU.le hyW
  let R₁ := ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj
  let π' := (inverseImageReduction (g := g) P).hom
  have hzero : (R₁.map iU.op).hom (unitSec g X.sheaf U ((P.reduction.hom.app (op U)).hom a)) =
      0 := by
    rw [unitSec_naturality g P.reduction U a]
    refine (NatTrans.naturality_apply π' iU.op _).symm.trans ?_
    refine (congrArg (π'.app (op W)).hom hab.symm).trans ?_
    refine (NatTrans.naturality_apply π' iV.op s).trans ?_
    show (R₁.map iV.op).hom ((π'.app (op V)).hom s) = 0
    rw [show (π'.app (op V)).hom s = 0 from hs, map_zero]
  have h0 : (R₁.map iU.op).hom (unitSec g X.sheaf U 0) = 0 :=
    (congrArg (R₁.map iU.op).hom (map_zero (unitSec g X.sheaf U))).trans (map_zero _)
  obtain ⟨U', hU', i₁, i₂, hU''⟩ := exists_eq_of_germ_unitSec_eq g X.sheaf _ _ y hgy hgy
    (germ_eq_of_map_eq _ iU iU hyW _ _ (hzero.trans h0.symm))
  have ha' : (P.sheaf.obj.map i₁.op).hom a ∈ kernelIdeal P.reduction.hom (op U') := by
    show (P.reduction.hom.app (op U')).hom ((P.sheaf.obj.map i₁.op).hom a) = 0
    rw [NatTrans.naturality_apply P.reduction.hom i₁.op a]
    refine hU''.trans ?_
    exact map_zero _
  refine ⟨⟨W ⊓ (Opens.map g.hom.base).obj U', inf_le_left.trans iV.le, U', inf_le_right,
    ⟨_, ha'⟩, ?_⟩, ⟨hyW, hU'⟩⟩
  exact restrict_eq_unitSec_map iV iU a hab i₁ inf_le_left inf_le_right

variable (P G c) in
/-- **The values attached to the local representations of a section glue.** -/
theorem exists_glued_value (V : Opens Y.carrier) (s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) :
    ∃ t : G.val.obj (op V), ∀ r : LocalRep P V s,
      G.val.map (homOfLE r.le_V).op t = r.value P G c := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} Y.carrier := ⟨G.val.presheaf, G.isSheaf⟩
  let A' := (inverseImageRing (g := g) P).obj
  obtain ⟨t, ht, -⟩ := Gsh.existsUnique_gluing' (fun r : LocalRep P V s => r.W) V
    (fun r => homOfLE r.le_V) (fun y hy => by
      obtain ⟨r, hr⟩ := exists_localRep (P := P) V s hs y hy
      exact Opens.mem_iSup.2 ⟨r, hr⟩) (fun r => r.value P G c) (by
      intro r₁ r₂
      show G.val.map (homOfLE inf_le_left).op (r₁.value P G c) =
        G.val.map (homOfLE inf_le_right).op (r₂.value P G c)
      unfold LocalRep.value
      rw [moduleMap_map G _ _ (homOfLE (inf_le_left.trans r₁.le_U)),
        moduleMap_map G _ _ (homOfLE (inf_le_right.trans r₂.le_U))]
      apply idealValue_eq_of_unitSec_eq
      rw [← ringMap_map A' (homOfLE r₁.le_U) (homOfLE inf_le_left), ← r₁.eq,
        ← ringMap_map A' (homOfLE r₂.le_U) (homOfLE inf_le_right), ← r₂.eq,
        ringMap_map A' _ _ (homOfLE (inf_le_left.trans r₁.le_V)),
        ringMap_map A' _ _ (homOfLE (inf_le_left.trans r₁.le_V))])
  exact ⟨t, ht⟩

variable (P G c) in
/-- **The map `g⁻¹ℱ ⟶ 𝒢` on a section of the kernel of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X`**: the section of
`𝒢` which, wherever the section is the image of a section `a` of the ideal `ℱ` of `𝒪_{X'}`, is
`c(a)`. -/
def idealMapValue (V : Opens Y.carrier) (s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) : G.val.obj (op V) :=
  (exists_glued_value P G c V s hs).choose

/-- `idealMapValue` restricts to the value of every local representation. -/
theorem idealMapValue_spec (V : Opens Y.carrier) (s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) (r : LocalRep P V s) :
    G.val.map (homOfLE r.le_V).op (idealMapValue P G c V s hs) = r.value P G c :=
  (exists_glued_value P G c V s hs).choose_spec r

/-- `idealMapValue` is the only section restricting near each point to the value of some local
representation. -/
theorem eq_idealMapValue (V : Opens Y.carrier) (s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) (t : G.val.obj (op V))
    (h : ∀ y ∈ V, ∃ r : LocalRep P V s, y ∈ r.W ∧
      G.val.map (homOfLE r.le_V).op t = r.value P G c) :
    t = idealMapValue P G c V s hs := by
  refine moduleSection_ext G _ _ fun y hy => ?_
  obtain ⟨r, hr, ht⟩ := h y hy
  exact ⟨r.W, hr, homOfLE r.le_V, ht.trans (idealMapValue_spec V s hs r).symm⟩

/-- A local representation restricts to every smaller open, on the side of `g⁻¹𝒪_{X'}`. -/
theorem LocalRep.map_eq {V : Opens Y.carrier} {s : (inverseImageRing (g := g) P).obj.obj (op V)}
    (r : LocalRep P V s) {W : Opens Y.carrier} (hW : W ≤ r.W) :
    ((inverseImageRing (g := g) P).obj.map (homOfLE (hW.trans r.le_V)).op).hom s =
      ((inverseImageRing (g := g) P).obj.map (homOfLE (hW.trans r.le_U)).op).hom
        (unitSec g P.sheaf r.U r.a.1) := by
  rw [← ringMap_map _ (homOfLE r.le_V) (homOfLE hW), r.eq, ringMap_map]

/-- A local representation restricts to every smaller open, on the side of `𝒢`. -/
theorem idealMapValue_map_of_le {V : Opens Y.carrier}
    {s : (inverseImageRing (g := g) P).obj.obj (op V)}
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V))
    (r : LocalRep P V s) {W : Opens Y.carrier} (hW : W ≤ r.W) :
    G.val.map (homOfLE (hW.trans r.le_V)).op (idealMapValue P G c V s hs) =
      G.val.map (homOfLE (hW.trans r.le_U)).op (idealValue P G c r.U r.a) := by
  rw [← moduleMap_map G (homOfLE r.le_V) (homOfLE hW), idealMapValue_spec V s hs r,
    LocalRep.value, moduleMap_map]

/-- The image of a restricted section of `𝒪_{X'}` in `g⁻¹𝒪_{X'}`. -/
theorem map_unitSec_map {U U' : Opens X.carrier} (i : U' ⟶ U) (a : P.sheaf.obj.obj (op U))
    {W : Opens Y.carrier} (hW : W ≤ (Opens.map g.hom.base).obj U') :
    ((inverseImageRing (g := g) P).obj.map (homOfLE hW).op).hom
        (unitSec g P.sheaf U' ((P.sheaf.obj.map i.op).hom a)) =
      ((inverseImageRing (g := g) P).obj.map (homOfLE (hW.trans
        ((Opens.map g.hom.base).map i).le)).op).hom (unitSec g P.sheaf U a) := by
  rw [unitSec_map g P.sheaf i a, ringMap_map]

/-- The value of `c` on a restricted section of the ideal. -/
theorem map_idealValue_map {U U' : Opens X.carrier} (i : U' ⟶ U)
    (a : kernelIdeal P.reduction.hom (op U)) {W : Opens Y.carrier}
    (hW : W ≤ (Opens.map g.hom.base).obj U') :
    G.val.map (homOfLE hW).op (idealValue P G c U' ⟨(P.sheaf.obj.map i.op).hom a.1,
        Stacks.Sites.Conormal.map_kernel P.reduction.hom i.op a.2⟩) =
      G.val.map (homOfLE (hW.trans ((Opens.map g.hom.base).map i).le)).op
        (idealValue P G c U a) := by
  rw [idealValue_map, moduleMap_map]

/-- Restricting a local representation along `U ⟶ r.U`, on the side of `g⁻¹𝒪_{X'}`. -/
private theorem localRep_map_eq_restrict {V : Opens Y.carrier}
    {s : (inverseImageRing (g := g) P).obj.obj (op V)} (r : LocalRep P V s) {U : Opens X.carrier}
    (i : U ⟶ r.U) {W : Opens Y.carrier} (hW : W ≤ r.W)
    (hWU : W ≤ (Opens.map g.hom.base).obj U) :
    ((inverseImageRing (g := g) P).obj.map (homOfLE (hW.trans r.le_V)).op).hom s =
      ((inverseImageRing (g := g) P).obj.map (homOfLE hWU).op).hom
        (unitSec g P.sheaf U ((P.sheaf.obj.map i.op).hom r.a.1)) :=
  (r.map_eq hW).trans (map_unitSec_map i r.a.1 hWU).symm

/-- Restricting a local representation along `U ⟶ r.U`, on the side of `𝒢`. -/
private theorem idealMapValue_map_restrict {V : Opens Y.carrier}
    {s : (inverseImageRing (g := g) P).obj.obj (op V)}
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V))
    (r : LocalRep P V s) {U : Opens X.carrier} (i : U ⟶ r.U) {W : Opens Y.carrier}
    (hW : W ≤ r.W) (hWU : W ≤ (Opens.map g.hom.base).obj U) :
    G.val.map (homOfLE (hW.trans r.le_V)).op (idealMapValue P G c V s hs) =
      G.val.map (homOfLE hWU).op (idealValue P G c U ⟨(P.sheaf.obj.map i.op).hom r.a.1,
        Stacks.Sites.Conormal.map_kernel P.reduction.hom i.op r.a.2⟩) :=
  (idealMapValue_map_of_le hs r hW).trans (map_idealValue_map i r.a hWU).symm

/-- `idealValue` is additive. -/
theorem idealValue_add (U : Opens X.carrier) (a b : kernelIdeal P.reduction.hom (op U)) :
    idealValue P G c U (a + b) = idealValue P G c U a + idealValue P G c U b := by
  unfold idealValue
  exact (congrArg _ (map_add _ a b)).trans (map_add _ _ _)

/-- `idealValue` vanishes on `0`. -/
theorem idealValue_zero (U : Opens X.carrier) : idealValue P G c U 0 = 0 := by
  unfold idealValue
  exact (congrArg _ (map_zero _)).trans (map_zero _)

/-- On the image of a section `a` of the ideal of `𝒪_{X'}`, `idealMapValue` is `c(a)`. -/
theorem idealMapValue_unitSec (U : Opens X.carrier) (a : kernelIdeal P.reduction.hom (op U))
    (ha : unitSec g P.sheaf U a.1 ∈
      kernelIdeal (inverseImageReduction (g := g) P).hom (op ((Opens.map g.hom.base).obj U))) :
    idealMapValue P G c _ (unitSec g P.sheaf U a.1) ha = idealValue P G c U a := by
  refine (eq_idealMapValue _ _ ha _ fun y hy => ⟨⟨_, le_rfl, U, le_rfl, a, rfl⟩, hy, rfl⟩).symm

/-- The value of the map `g⁻¹ℱ ⟶ 𝒢` vanishes on `0`. -/
theorem idealMapValue_zero (V : Opens Y.carrier)
    (h0 : (0 : (inverseImageRing (g := g) P).obj.obj (op V)) ∈
      kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) :
    idealMapValue P G c V 0 h0 = 0 := by
  refine (eq_idealMapValue V 0 h0 0 fun y hy => ⟨⟨V, le_rfl, ⊤, fun _ _ => trivial, 0, ?_⟩,
    hy, ?_⟩).symm
  · exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  · exact (map_zero _).trans ((congrArg _ (idealValue_zero ⊤)).trans (map_zero _)).symm

/-- The value of the map `g⁻¹ℱ ⟶ 𝒢` is additive. -/
theorem idealMapValue_add (V : Opens Y.carrier)
    (s₁ s₂ : (inverseImageRing (g := g) P).obj.obj (op V))
    (h₁ : s₁ ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V))
    (h₂ : s₂ ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V))
    (h : s₁ + s₂ ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) :
    idealMapValue P G c V (s₁ + s₂) h =
      idealMapValue P G c V s₁ h₁ + idealMapValue P G c V s₂ h₂ := by
  let A' := (inverseImageRing (g := g) P).obj
  refine (eq_idealMapValue V _ h _ fun y hy => ?_).symm
  obtain ⟨r₁, hr₁⟩ := exists_localRep (P := P) V s₁ h₁ y hy
  obtain ⟨r₂, hr₂⟩ := exists_localRep (P := P) V s₂ h₂ y hy
  let U := r₁.U ⊓ r₂.U
  let W := r₁.W ⊓ r₂.W
  have hWU : W ≤ (Opens.map g.hom.base).obj U := fun z hz => ⟨r₁.le_U hz.1, r₂.le_U hz.2⟩
  let i₁ : U ⟶ r₁.U := homOfLE inf_le_left
  let i₂ : U ⟶ r₂.U := homOfLE inf_le_right
  let a : kernelIdeal P.reduction.hom (op U) :=
    ⟨(P.sheaf.obj.map i₁.op).hom r₁.a.1, Stacks.Sites.Conormal.map_kernel P.reduction.hom
        i₁.op r₁.a.2⟩ +
      ⟨(P.sheaf.obj.map i₂.op).hom r₂.a.1, Stacks.Sites.Conormal.map_kernel P.reduction.hom
        i₂.op r₂.a.2⟩
  refine ⟨⟨W, inf_le_left.trans r₁.le_V, U, hWU, a, ?_⟩, ⟨hr₁, hr₂⟩, ?_⟩
  · show (A'.map _).hom (s₁ + s₂) = (A'.map (homOfLE hWU).op).hom (unitSec g P.sheaf U
      ((P.sheaf.obj.map i₁.op).hom r₁.a.1 + (P.sheaf.obj.map i₂.op).hom r₂.a.1))
    rw [map_add, map_add, map_add, ← localRep_map_eq_restrict r₁ i₁ (inf_le_left : W ≤ r₁.W) hWU,
      ← localRep_map_eq_restrict r₂ i₂ (inf_le_right : W ≤ r₂.W) hWU]
  · exact (map_add _ _ _).trans ((congrArg₂ (· + ·)
      (idealMapValue_map_restrict h₁ r₁ i₁ (inf_le_left : W ≤ r₁.W) hWU)
      (idealMapValue_map_restrict h₂ r₂ i₂ (inf_le_right : W ≤ r₂.W) hWU)).trans
      ((map_add _ _ _).symm.trans (congrArg _ (idealValue_add U _ _).symm)))

/-- The value of the map `g⁻¹ℱ ⟶ 𝒢` commutes with restriction. -/
theorem idealMapValue_map {V V' : Opens Y.carrier} (i : V' ⟶ V)
    (s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V))
    (hs' : ((inverseImageRing (g := g) P).obj.map i.op).hom s ∈
      kernelIdeal (inverseImageReduction (g := g) P).hom (op V')) :
    idealMapValue P G c V' (((inverseImageRing (g := g) P).obj.map i.op).hom s) hs' =
      G.val.map i.op (idealMapValue P G c V s hs) := by
  let A' := (inverseImageRing (g := g) P).obj
  refine (eq_idealMapValue V' _ hs' _ fun y hy => ?_).symm
  obtain ⟨r, hr⟩ := exists_localRep (P := P) V s hs y (i.le hy)
  refine ⟨⟨r.W ⊓ V', inf_le_right, r.U, inf_le_left.trans r.le_U, r.a, ?_⟩, ⟨hr, hy⟩, ?_⟩
  · show (A'.map (homOfLE inf_le_right).op).hom ((A'.map i.op).hom s) = _
    rw [ringMap_map A' i (homOfLE inf_le_right) (homOfLE (inf_le_left.trans r.le_V))]
    exact r.map_eq inf_le_left
  · exact (moduleMap_map G i (homOfLE inf_le_right) (homOfLE (inf_le_left.trans r.le_V)) _).trans
      (idealMapValue_map_of_le hs r inf_le_left)

/-- `c ∘ ρ` is linear: `c(ρ(x a)) = g^♯(x̄) · c(ρ(a))`, `x̄` the image of `x` in `𝒪_X`. -/
theorem idealValue_smul (U : Opens X.carrier) (x : P.sheaf.obj.obj (op U))
    (a : kernelIdeal P.reduction.hom (op U)) :
    idealValue P G c U (x • a) =
      (show (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj U)) from
        (g.hom.c.app (op U)).hom ((P.reduction.hom.app (op U)).hom x)) •
        idealValue P G c U a := by
  unfold idealValue
  rw [P.ideal.app_smul]
  exact (c.val.app (op U)).hom.map_smul _ _

variable (g) in
/-- `g^♯ : 𝒪_X ⟶ g_*𝒪_Y` on sections is the unit followed by `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
theorem c_app_eq (U : Opens X.carrier) (x : X.sheaf.obj.obj (op U)) :
    (g.hom.c.app (op U)).hom x =
      ((ringedSpaceStructureMap g).hom.app (op ((Opens.map g.hom.base).obj U))).hom
        (unitSec g X.sheaf U x) :=
  congrArg (fun t => (t.app (op U)).hom x) (c_eq_unit_comp g)

/-- **The map `g⁻¹ℱ ⟶ 𝒢` is `g⁻¹𝒪_{X'}`-linear**, `g⁻¹𝒪_{X'}` acting on `𝒢` through
`g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
theorem idealMapValue_mul (V : Opens Y.carrier)
    (b s : (inverseImageRing (g := g) P).obj.obj (op V))
    (hs : s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V))
    (hbs : b * s ∈ kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) :
    idealMapValue P G c V (b * s) hbs =
      (show (structureSheafRing Y).obj.obj (op V) from
        ((ringedSpaceStructureMap g).hom.app (op V)).hom
          (((inverseImageReduction (g := g) P).hom.app (op V)).hom b)) •
        idealMapValue P G c V s hs := by
  let A' := (inverseImageRing (g := g) P).obj
  let R₁ := ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj
  let π' := (inverseImageReduction (g := g) P).hom
  let σ := (ringedSpaceStructureMap g).hom
  refine (eq_idealMapValue V _ hbs _ fun y hy => ?_).symm
  obtain ⟨r, hr⟩ := exists_localRep (P := P) V s hs y hy
  obtain ⟨U₂, W₂, hyW₂, iV₂, iU₂, b₀, hb⟩ :=
    Stacks.Sheaves.PullbackUnit.exists_restrict_eq_unit g.hom.base P.sheaf y V hy b
  let U := r.U ⊓ U₂
  let W := r.W ⊓ W₂
  have hWU : W ≤ (Opens.map g.hom.base).obj U := fun z hz => ⟨r.le_U hz.1, iU₂.le hz.2⟩
  let i₁ : U ⟶ r.U := homOfLE inf_le_left
  let i₂ : U ⟶ U₂ := homOfLE inf_le_right
  let a₁ : kernelIdeal P.reduction.hom (op U) :=
    ⟨(P.sheaf.obj.map i₁.op).hom r.a.1, Stacks.Sites.Conormal.map_kernel P.reduction.hom
        i₁.op r.a.2⟩
  let b₁ := (P.sheaf.obj.map i₂.op).hom b₀
  have hb' : (A'.map (homOfLE (inf_le_right.trans iV₂.le) : W ⟶ V).op).hom b =
      (A'.map (homOfLE hWU).op).hom (unitSec g P.sheaf U b₁) := by
    exact restrict_eq_unitSec_map iV₂ iU₂ b₀ hb i₂ inf_le_right hWU
  refine ⟨⟨W, inf_le_left.trans r.le_V, U, hWU, b₁ • a₁, ?_⟩, ⟨hr, hyW₂⟩, ?_⟩
  · show (A'.map _).hom (b * s) = (A'.map (homOfLE hWU).op).hom (unitSec g P.sheaf U
      (b₁ * (P.sheaf.obj.map i₁.op).hom r.a.1))
    refine (map_mul _ b s).trans ((congrArg₂ (· * ·) hb'
      (localRep_map_eq_restrict r i₁ (inf_le_left : W ≤ r.W) hWU)).trans ?_)
    exact (map_mul _ _ _).symm.trans (congrArg _ (map_mul _ _ _).symm)
  · have h1 := idealMapValue_map_restrict (G := G) (c := c) hs r i₁ (inf_le_left : W ≤ r.W) hWU
    have h2 : ((structureSheafRing Y).obj.map (homOfLE (inf_le_left.trans r.le_V) : W ⟶ V).op).hom
        (show (structureSheafRing Y).obj.obj (op V) from
          (σ.app (op V)).hom ((π'.app (op V)).hom b)) =
        ((structureSheafRing Y).obj.map (homOfLE hWU).op).hom
          (show (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj U)) from
            (g.hom.c.app (op U)).hom ((P.reduction.hom.app (op U)).hom b₁)) := by
      show (Y.sheaf.obj.map _).hom _ = (Y.sheaf.obj.map _).hom _
      refine (NatTrans.naturality_apply σ (homOfLE (inf_le_left.trans r.le_V) : W ⟶ V).op
        _).symm.trans ?_
      refine (congrArg (σ.app (op W)).hom (NatTrans.naturality_apply π' _ b).symm).trans ?_
      refine (congrArg (fun z => (σ.app (op W)).hom ((π'.app (op W)).hom z)) hb').trans ?_
      refine (congrArg (σ.app (op W)).hom
        (NatTrans.naturality_apply π' (homOfLE hWU).op _)).trans ?_
      refine (congrArg (fun z => (σ.app (op W)).hom ((R₁.map (homOfLE hWU).op).hom z))
        (unitSec_naturality g P.reduction U b₁).symm).trans ?_
      refine (NatTrans.naturality_apply σ (homOfLE hWU).op _).trans ?_
      exact congrArg _ (c_app_eq g U _).symm
    have e3 := PresheafOfModules.map_smul G.val (homOfLE (inf_le_left.trans r.le_V) : W ⟶ V).op
      (show (structureSheafRing Y).obj.obj (op V) from
          (σ.app (op V)).hom ((π'.app (op V)).hom b)) (idealMapValue P G c V s hs)
    have e4 := PresheafOfModules.map_smul G.val (homOfLE hWU).op
      (show (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj U)) from
            (g.hom.c.app (op U)).hom ((P.reduction.hom.app (op U)).hom b₁))
      (idealValue P G c U a₁)
    exact e3.trans ((congrArg₂ (fun (x : (structureSheafRing Y).obj.obj (op W))
      (m : G.val.obj (op W)) => x • m) h2 h1).trans
      (e4.symm.trans (congrArg _ (idealValue_smul (G := G) (c := c) U b₁ a₁).symm)))

variable (P G c) in
/-- **The map `c : g⁻¹ℱ ⟶ 𝒢` on the kernel `g⁻¹ℱ` of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X`**, as a natural family
of `g⁻¹𝒪_{X'}`-linear maps on sections into `𝒢` read as a `g⁻¹𝒪_X`-module: on the image of a
section `a` of the ideal `ℱ ⊆ 𝒪_{X'}` it is `c(a)` (`idealMap_app_unitSec`), and it is determined
by this since such images generate the kernel locally (`exists_localRep`). -/
def idealMap : Stacks.Sites.Conormal.IdealRestriction.{u, u, u, u}
    (inverseImageReduction (g := g) P) (restrictedModule g G) where
  app V :=
    { toFun := fun s => idealMapValue P G c V.unop s.1 s.2
      map_zero' := idealMapValue_zero _ _
      map_add' := fun s₁ s₂ => idealMapValue_add _ _ _ s₁.2 s₂.2 _ }
  app_smul _ r s := idealMapValue_mul _ r s.1 s.2 (r • s).2
  app_map f s := idealMapValue_map f.unop s.1 s.2
    (Stacks.Sites.Conormal.map_kernel (inverseImageReduction (g := g) P).hom f s.2)

/-- `idealMap` on sections. -/
theorem idealMap_app (V : Opens Y.carrier)
    (s : kernelIdeal (inverseImageReduction (g := g) P).hom (op V)) :
    (idealMap P G c).app (op V) s = idealMapValue P G c V s.1 s.2 := rfl

/-- **On the image of a section of the ideal `ℱ ⊆ 𝒪_{X'}`, `idealMap` is `c`.** -/
theorem idealMap_app_unitSec (U : Opens X.carrier) (a : kernelIdeal P.reduction.hom (op U))
    (ha : unitSec g P.sheaf U a.1 ∈
      kernelIdeal (inverseImageReduction (g := g) P).hom (op ((Opens.map g.hom.base).obj U))) :
    (idealMap P G c).app (op _) ⟨unitSec g P.sheaf U a.1, ha⟩ =
      c.val.app (op U) (P.ideal.app (op U) a) :=
  idealMapValue_unitSec (G := G) (c := c) U a ha

end IdealMap









end InverseImage

end AlgebraicGeometry.RingedSpaceThickening
