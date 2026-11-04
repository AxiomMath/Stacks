module
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Bijectivity

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyA
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BasicUnconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
import all Mathlib.CategoryTheory.Limits.HasLimits
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of direct images along a finite morphism, for sheaves in any universe

Let `f : X ⟶ Y` be a morphism in a big étale site, let `y` be a geometric point of `Y` and let
`F` be a sheaf of sets on the small étale site of `X`, with values in `Type (max (u + 1) v)`.
The stalk of the direct image `f_* F` at `y` maps canonically to the product of the stalks of
`F` at the lifts of `y` through `f`. This map is injective when `f` is integral and bijective
when `f` is finite; the latter is part (1) of Tag 03QP for sheaves of sets.

## Main definitions

* `AlgebraicGeometry.pushforwardEtaleStalkComponentUniv`: the canonical map from the stalk of
  `f_* F` at `y` to the stalk of `F` at a geometric point of `X` lying over `y`.
* `AlgebraicGeometry.finitePushforwardStalkToProductUniv`: the comparison map from the stalk of
  `f_* F` at `y` to the product of the stalks of `F` at the lifts of `y`.
* `AlgebraicGeometry.finitePushforwardStalkEquivUniv`: for finite `f`, the stalk of `f_* F` at
  `y` is the product of the stalks of `F` at the lifts of `y`.

## Main results

* `AlgebraicGeometry.pushforwardEtaleStalkComponent_germ_univ`: the comparison map on germs.
* `AlgebraicGeometry.pushforwardEtaleStalkComponent_natural_univ`: the comparison map is
  natural in the sheaf.
* `AlgebraicGeometry.finitePushforwardStalkComponent_injective_univ`: for integral `f`, the
  comparison map to the product of the stalks is injective.
* `AlgebraicGeometry.finitePushforwardStalkToProduct_bijective_univ`: for finite `f`, the
  comparison map to the product of the stalks is bijective.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry

section Finiteness

end Finiteness

section Component

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The canonical map from the stalk of a direct image at a geometric point `y` of the target
to the stalk at a geometric point `x` of the source lying over `y`.

The stalk at `x` of the inverse image of a sheaf on the target is the stalk of that sheaf at
`x`'s image (Tag 03Q1); applying this to the direct image `f_* F` and following with the stalk
at `x` of the counit `f^* f_* F ⟶ F` gives the map. -/
public def pushforwardEtaleStalkComponentUniv
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj →
      etaleStalk B X.1 X.property x F.obj :=
  fun z =>
    (etaleStalkFunctor.{u, max (u + 1) v} B X.1 X.property x).map
      (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).counit.app F)
      ((smallEtalePullbackStalkIsoUniv B f x).inv.app
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F) (h.symm ▸ z))

/-- **The comparison on germs.** A section `s` of `F` over the base change `U ×_Y X` of an étale
neighborhood `U` of `y` — that is, a section of `f_* F` over `U` — has germ at `y` sent to the
germ at `x` of the restriction of `s` to any étale neighborhood `V` of `x` equipped with a map
to `U ×_Y X` compatible with the two points. -/
public theorem pushforwardEtaleStalkComponent_germ_univ
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property x).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (ht : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ U.2.1)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    pushforwardEtaleStalkComponentUniv B f x y h F
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj) (op U) s) =
      colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj) (op V) (F.obj.map t.op s) := by
  subst y
  let adj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (max (u + 1) v))
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)
  let P := ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F
  let D := (CategoryOfElements.π (geometricPointFiber B Y.1 Y.property
    (x.map (B.inclusion.map f)))).op ⋙ P.obj
  let L := ((smallEtaleBaseChange B f).sheafPullback (Type (max (u + 1) v))
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj P
  let E := (CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ L.obj
  let Q := (CategoryOfElements.π (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj
  let e := (smallEtalePullbackStalkIsoUniv B f x).app P
  simp only [eqToHom_refl, Category.id_comp] at ht
  have hg := smallEtalePullbackStalkIso_germ_univ B f x P V U t ht s
  have hi : e.inv (colimit.ι D (op U) s) =
      colimit.ι E (op V) (pullbackSectionAlongUniv B f P U.1 V.1 t s) := by
    rw [← hg]
    exact ConcreteCategory.congr_hom e.hom_inv_id _
  show (etaleStalkFunctor.{u, max (u + 1) v} B X.1 X.property x).map (adj.counit.app F)
    (e.inv (colimit.ι D (op U) s)) = colimit.ι Q (op V) (F.obj.map t.op s)
  rw [hi]
  show (colimit.ι E (op V) ≫ colim.map
    (Functor.whiskerLeft (CategoryOfElements.π
      (geometricPointFiber B X.1 X.property x)).op (adj.counit.app F).hom)) _ = _
  rw [colimit.ι_map]
  show colimit.ι Q (op V)
    ((adj.counit.app F).hom.app (op V.1) (pullbackSectionAlongUniv B f P U.1 V.1 t s)) = _
  congr 1
  unfold pullbackSectionAlongUniv
  have hn := (adj.counit.app F).hom.naturality t.op
  have htri := congrArg (fun a => a.hom.app (op U.1)) (adj.right_triangle_components F)
  have hn' := ConcreteCategory.congr_hom hn
  have htri' := ConcreteCategory.congr_hom htri s
  dsimp at hn' htri'
  show (adj.counit.app F).hom.app (op V.1)
    (L.obj.map t.op ((adj.unit.app P).hom.app (op U.1) s)) = F.obj.map t.op s
  change (adj.counit.app F).hom.app (op ((smallEtaleBaseChange B f).obj U.1))
    ((adj.unit.app P).hom.app (op U.1) s) = s at htri'
  exact (hn' _).trans (congrArg (fun z => F.obj.map t.op z) htri')

/-- **Naturality of the comparison in the sheaf.** The map
`AlgebraicGeometry.pushforwardEtaleStalkComponentUniv` commutes with the maps on stalks induced
by a morphism of sheaves `α : F ⟶ G`. -/
public theorem pushforwardEtaleStalkComponent_natural_univ
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1)
    (h : x.map (B.inclusion.map f) = y)
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))} (α : F ⟶ G)
    (z : etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj) :
    pushforwardEtaleStalkComponentUniv B f x y h G
        ((etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property y).map
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).map α) z) =
      (etaleStalkFunctor.{u, max (u + 1) v} B X.1 X.property x).map α
        (pushforwardEtaleStalkComponentUniv B f x y h F z) := by
  subst y
  let J := SmallEtale.topology B Y.1 Y.property
  let K := SmallEtale.topology B X.1 X.property
  let bc := smallEtaleBaseChange B f
  let PF := bc.sheafPushforwardContinuous (Type (max (u + 1) v)) J K
  let PB := bc.sheafPullback (Type (max (u + 1) v)) J K
  let adj := bc.sheafAdjunctionContinuous (Type (max (u + 1) v)) J K
  let SX := etaleStalkFunctor.{u, max (u + 1) v} B X.1 X.property x
  let SY := etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property (x.map (B.inclusion.map f))
  let iso := smallEtalePullbackStalkIsoUniv B f x
  have key : SY.map (PF.map α) ≫ iso.inv.app (PF.obj G) ≫ SX.map (adj.counit.app G) =
      iso.inv.app (PF.obj F) ≫ SX.map (adj.counit.app F) ≫ SX.map α := by
    rw [← Category.assoc, iso.inv.naturality (PF.map α), Category.assoc]
    congr 1
    show SX.map (PB.map (PF.map α)) ≫ SX.map (adj.counit.app G) = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg SX.map (adj.counit.naturality α)
  exact congrArg (fun k => k z) key

end Component

section Lifts

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)

/-- The canonical map from the stalk of a direct image at `y` to the stalk at one lift of `y`,
induced by the counit of inverse and direct image. This is
`AlgebraicGeometry.pushforwardEtaleStalkComponentUniv` at the geometric point
`AlgebraicGeometry.geometricPointLift`. -/
public def finitePushforwardStalkComponentUniv
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj →
    etaleStalk B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x) F.obj :=
  pushforwardEtaleStalkComponentUniv B f (geometricPointLift (B.inclusion.map f) y x) y
    (geometricPointLift_map (B.inclusion.map f) y x) F

/-- **The comparison on germs at a lift, along an arbitrary morphism of neighborhoods.** The
germ at `y` of a section of `f_* F` over an étale neighborhood `V` is sent to the germ at the
lift `x` of its restriction to any pointed étale neighborhood of `x` over `V ×_Y X`. -/
private theorem finitePushforwardStalkComponent_germ_of_hom_general
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).Elements)
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1)
    (t : F.obj.obj (op ((smallEtaleBaseChange B f).obj V.1))) :
    finitePushforwardStalkComponentUniv B f y F x
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj) (op V) t) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj) (op U)
        (F.obj.map a.op t) :=
  pushforwardEtaleStalkComponent_germ_univ B f (geometricPointLift (B.inclusion.map f) y x) y
    (geometricPointLift_map (B.inclusion.map f) y x) F V U a (by simpa using ha) t

/-- **The comparison on germs, at a lift.** The germ at `y` of a section `s` of `F` over the
base change `U ×_Y X` of an étale neighborhood `U` of `y` — that is, of a section of `f_* F`
over `U` — is sent to the germ of `s` at the pointed neighborhood
`AlgebraicGeometry.liftedEtaleNeighborhood`. -/
public theorem finitePushforwardStalkComponent_germ_univ
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    finitePushforwardStalkComponentUniv B f y F x
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj) (op U) s) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj)
        (op (liftedEtaleNeighborhood B f y x U)) s := by
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  refine (finitePushforwardStalkComponent_germ_of_hom_general B f y F x
    (liftedEtaleNeighborhood B f y x U) U (𝟙 _) (by simp [liftedEtaleNeighborhood]) s).trans ?_
  congr 1
  exact ConcreteCategory.congr_hom (F.obj.map_id _) s

/-- **The comparison map.** The map from the stalk of the direct image `f_* F` at `y` to the
product of the stalks of `F` at the lifts of `y`, whose component at a lift `x` is
`AlgebraicGeometry.finitePushforwardStalkComponentUniv`. -/
public def finitePushforwardStalkToProductUniv
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj →
      (∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        etaleStalk B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x) F.obj) :=
  fun z x => finitePushforwardStalkComponentUniv B f y F x z

/-- The equivalence between the stalk of the direct image `f_* F` at `y` and the product of the
stalks of `F` at the lifts of `y`, given by the comparison map
`AlgebraicGeometry.finitePushforwardStalkToProductUniv` when that map is bijective. -/
public def finitePushforwardStalkEquivOfBijectiveUniv
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (hbij : Function.Bijective (finitePushforwardStalkToProductUniv B f y F)) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj ≃
      (∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        etaleStalk B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x) F.obj) :=
  Equiv.ofBijective _ hbij

end Lifts

section Bijectivity

private theorem finitePushforwardStalkComponent_germ_eq_iff_general
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (V : (geometricPointFiber B Y.1 Y.property y).Elements)
    (t t' : F.obj.obj (op ((smallEtaleBaseChange B f).obj V.1))) :
    (let D := (CategoryOfElements.π
      (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
    finitePushforwardStalkComponentUniv B f y F x (colimit.ι D (op V) t) =
      finitePushforwardStalkComponentUniv B f y F x (colimit.ι D (op V) t')) ↔
    ∃ (W : (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x)).Elements)
      (a : W ⟶ liftedEtaleNeighborhood B f y x V),
      F.obj.map a.1.op t = F.obj.map a.1.op t' := by
  dsimp only
  rw [finitePushforwardStalkComponent_germ_univ,
    finitePushforwardStalkComponent_germ_univ]
  let D := (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj
  exact (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D)
    (i := op (liftedEtaleNeighborhood B f y x V)) t t').trans
    ⟨fun ⟨W, a, ha⟩ ↦ ⟨W.unop, a.unop, ha⟩, fun ⟨W, a, ha⟩ ↦ ⟨op W, a.op, ha⟩⟩

open Opposite in
private theorem sections_ext_of_etale_covering_general
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (max (u + 1) v)))
    (U : SmallEtale B S hS) (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U))
    (t t' : F.obj.obj (op U))
    (h : ∀ i, F.obj.map (E.f i).op t = F.obj.map (E.f i).op t') : t = t' := by
  let a : PUnit.{max (u + 1) v + 1} ⟶ F.obj.obj (op U) := ↾fun _ => t
  let b : PUnit.{max (u + 1) v + 1} ⟶ F.obj.obj (op U) := ↾fun _ => t'
  have hab : a = b := F.property.hom_ext_ofArrows E.f
    (_root_.AlgebraicGeometry.smallEtale_generate_covering B S hS U E hE) (fun i => by
      ext z
      exact h i)
  exact ConcreteCategory.congr_hom hab PUnit.unit

open CategoryTheory.Limits Opposite in
private theorem sections_ext_of_range_subset_general
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (max (u + 1) v)))
    {U V : SmallEtale B S hS} (a : V ⟶ U)
    {I : Type (u + 1)} (W : I → SmallEtale B S hS) (b : ∀ i, W i ⟶ U)
    (hcover : Set.range ((SmallEtale.toScheme B S hS).map a) ⊆
      ⋃ i, Set.range ((SmallEtale.toScheme B S hS).map (b i)))
    (t t' : F.obj.obj (op U))
    (h : ∀ i, F.obj.map (b i).op t = F.obj.map (b i).op t') :
    F.obj.map a.op t = F.obj.map a.op t' := by
  let T := SmallEtale.toScheme B S hS
  let E : PreZeroHypercover.{u + 1} V :=
    { I₀ := I, X := fun i => pullback (b i) a, f := fun i => pullback.snd (b i) a }
  apply sections_ext_of_etale_covering_general B S hS F V E
  · show (E.map T).presieve₀ ∈ Scheme.precoverage @Etale (T.obj V)
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (E.map T)).2
      ⟨fun v ↦ ?_, fun i ↦ _root_.AlgebraicGeometry.etale_smallEtale_map B S hS (E.f i)⟩
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self v))
    obtain ⟨p, hp, hp'⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (b i) a).map T) w v hw
    exact ⟨i, p, hp'⟩
  · intro i
    show F.obj.map (pullback.snd (b i) a).op (F.obj.map a.op t) =
      F.obj.map (pullback.snd (b i) a).op (F.obj.map a.op t')
    have he : a.op ≫ (pullback.snd (b i) a).op =
        (b i).op ≫ (pullback.fst (b i) a).op :=
      congrArg Quiver.Hom.op (pullback.condition (f := b i) (g := a)).symm
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, he]
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, h i]


/-- **Germs of a direct image along an integral morphism are detected at the lifts.** For an
integral morphism `f` and a geometric point `y` of the target, an element of the stalk of
`f_* F` at `y` is determined by its images in the stalks of `F` at the lifts of `y`. -/
public theorem finitePushforwardStalkComponent_injective_univ
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsIntegralHom (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    Function.Injective (fun z x => finitePushforwardStalkComponentUniv B f y F x z) := by
  classical
  intro z z' hz
  let D := (CategoryOfElements.π
    (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
  obtain ⟨V, t, t', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit D) z z'
  have hx := fun x => (finitePushforwardStalkComponent_germ_eq_iff_general
    B f y F x V.unop t t').mp (congrFun hz x)
  choose W a ha using hx
  let T := SmallEtale.toScheme B X.1 X.property
  have he (x) : Etale (T.map (a x).1) :=
    _root_.AlgebraicGeometry.etale_smallEtale_map B X.1 X.property _
  let O : (T.obj ((smallEtaleBaseChange B f).obj V.unop.1)).Opens :=
    ⟨⋃ x, Set.range (T.map (a x).1), isOpen_iUnion fun x =>
      (T.map (a x).1).isOpenMap.isOpen_range⟩
  have hO (x) : (liftedEtaleNeighborhood B f y x V.unop).2.1 default ∈ O :=
    Set.mem_iUnion.mpr
      ⟨x, (W x).2.1 default, congrArg (fun k => k default) (congrArg Subtype.val (a x).2)⟩
  obtain ⟨V', b, hb⟩ := exists_baseChange_refinement_range_subset_of_isIntegralHom B f y V.unop O hO
  have ht : F.obj.map ((smallEtaleBaseChange B f).map b.1).op t =
      F.obj.map ((smallEtaleBaseChange B f).map b.1).op t' := by
    refine sections_ext_of_range_subset_general B X.1 X.property F
      ((smallEtaleBaseChange B f).map b.1)
      (fun x : ULift.{u + 1} {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}
        => (W x.down).1) (fun x => (a x.down).1) (fun p hp ↦ ?_) t t' (fun x => ha x.down)
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hb hp)
    exact Set.mem_iUnion.mpr ⟨⟨x⟩, hx⟩
  exact (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D) t t').mpr
    ⟨op V', b.op, ht⟩

open Opposite in
private theorem subsingleton_sections_of_isEmpty_general
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (max (u + 1) v)))
    (U : SmallEtale B S hS) [IsEmpty ((SmallEtale.toScheme B S hS).obj U)] :
    Subsingleton (F.obj.obj (op U)) := by
  refine ⟨fun t t' => ?_⟩
  let E : PreZeroHypercover.{u + 1} U :=
    { I₀ := PEmpty.{u + 2}, X := PEmpty.elim, f := fun i => i.elim }
  exact sections_ext_of_etale_covering_general B S hS F U E
    ((Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (E.map (SmallEtale.toScheme B S hS))).2
      ⟨fun p => isEmptyElim p, fun i => i.elim⟩) t t' (fun i => i.elim)

open Opposite in
private theorem exists_section_of_disjoint_cover_general
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (max (u + 1) v)))
    (U : SmallEtale B S hS) (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U))
    [∀ i, Mono (E.f i)]
    (hdis : Pairwise (fun i j => Disjoint
      (Set.range ((SmallEtale.toScheme B S hS).map (E.f i)))
      (Set.range ((SmallEtale.toScheme B S hS).map (E.f j)))))
    (t : ∀ i, F.obj.obj (op (E.X i))) :
    ∃ s : F.obj.obj (op U), ∀ i, F.obj.map (E.f i).op s = t i := by
  let T := SmallEtale.toScheme B S hS
  let t' (i) : PUnit.{max (u + 1) v + 1} ⟶ F.obj.obj (op (E.X i)) := ↾fun _ => t i
  obtain ⟨s, hs, _⟩ := F.property.existsUnique_amalgamation_ofArrows E.f
    (_root_.AlgebraicGeometry.smallEtale_generate_covering B S hS U E hE) t' (by
      intro W i j a b hab
      by_cases hij : i = j
      · subst j
        obtain rfl := (cancel_mono (E.f i)).mp hab
        rfl
      · have : IsEmpty (T.obj W) := ⟨fun w => by
          have he := congrArg (fun k => T.map k w) hab
          simp only [Functor.map_comp, Scheme.Hom.comp_apply] at he
          exact Set.disjoint_left.mp (hdis hij)
            (Set.mem_range_self (T.map a w))
            (he.symm ▸ Set.mem_range_self (T.map b w))⟩
        ext
        exact (subsingleton_sections_of_isEmpty_general B S hS F W).elim _ _)
  exact ⟨s PUnit.unit, fun i => ConcreteCategory.congr_hom (hs i) PUnit.unit⟩

open CategoryTheory.Limits Opposite in
private theorem finitePushforwardStalkComponent_surjective_of_partitions_general
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (h : ∀ U, Nonempty (EtaleNeighborhoodPartition B f y U)) :
    Function.Surjective (fun z x => finitePushforwardStalkComponentUniv B f y F x z) := by
  classical
  intro t
  let D (x) := (CategoryOfElements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x))).op ⋙ F.obj
  have hrep (x) := Types.jointly_surjective_of_isColimit (colimit.isColimit (D x)) (t x)
  choose U s hs using hrep
  let Q := Classical.choice (h fun x => (U x).unop)
  let L := {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}
  let E : PreZeroHypercover.{u + 1} ((smallEtaleBaseChange B f).obj Q.base.1) :=
    { I₀ := ULift.{u + 1} L, X := fun x => (Q.neighborhood x.down).1,
      f := fun x => Q.toBase x.down }
  have hE : (E.map (SmallEtale.toScheme B X.1 X.property)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B X.1 X.property).obj
        ((smallEtaleBaseChange B f).obj Q.base.1)) := by
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) _).2
      ⟨fun p ↦ ?_, fun x ↦ _root_.AlgebraicGeometry.etale_smallEtale_map B X.1 X.property _⟩
    obtain ⟨x, hx⟩ := Q.covers p
    exact ⟨⟨x⟩, hx⟩
  have hmono (i : E.I₀) : Mono (E.f i) := Q.mono_toBase i.down
  obtain ⟨s', hs'⟩ := exists_section_of_disjoint_cover_general B X.1 X.property F _ E hE
    (fun i j hij => Q.disjoint (fun he => hij (ULift.ext _ _ he)))
    (fun i => F.obj.map (Q.toNeighborhood i.down).1.op (s i.down))
  let D' := (CategoryOfElements.π
    (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj
  refine ⟨colimit.ι D' (op Q.base) s', funext fun x => ?_⟩
  refine (finitePushforwardStalkComponent_germ_of_hom_general B f y F x
    (Q.neighborhood x) Q.base (Q.toBase x) (Q.point_toBase x) s').trans ?_
  rw [hs' ⟨x⟩]
  show colimit.ι (D x) (op (Q.neighborhood x))
      ((D x).map (Q.toNeighborhood x).op (s x)) = t x
  rw [← ConcreteCategory.comp_apply, colimit.w]
  exact hs x

/-- For a finite morphism the comparison map
`AlgebraicGeometry.finitePushforwardStalkToProductUniv` from the stalk of a direct image to the
product of the stalks over the lifts of the geometric point is bijective. -/
public theorem finitePushforwardStalkToProduct_bijective_univ
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    Function.Bijective (finitePushforwardStalkToProductUniv B f y F) := by
  classical
  exact ⟨finitePushforwardStalkComponent_injective_univ B f y F,
    finitePushforwardStalkComponent_surjective_of_partitions_general B f y F
      (exists_etaleNeighborhoodPartition B f y)⟩

/-- The stalk at a geometric point `y` of the direct image of a sheaf of sets along a finite
morphism is the product of the stalks of the sheaf over the lifts of `y`. -/
@[sga "4 VIII 5.5" "partial"]
public def finitePushforwardStalkEquivUniv
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] (y : GeometricPoint Y.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    etaleStalk B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F).obj ≃
      (∀ x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom},
        etaleStalk B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x) F.obj) :=
  finitePushforwardStalkEquivOfBijectiveUniv B f y F
    (finitePushforwardStalkToProduct_bijective_univ B f y F)

end Bijectivity

section Abelian

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)

private theorem etaleStalk_preservesColimits_general
    (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget AddCommGrpCat.{max (u + 1) v}) := by
  have : IsCofiltered (geometricPointFiber B S hS s).Elements :=
    isCofiltered_geometricPointFiber_elements B S hS s
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u}
      (forget AddCommGrpCat.{max (u + 1) v})
  exact Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u}
      ((geometricPointFiber B S hS s).Elementsᵒᵖ)) _

attribute [local instance] etaleStalk_preservesColimits_general

end Abelian

end AlgebraicGeometry

end
