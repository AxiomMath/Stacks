module

public import StacksFrontier.AlgebraicGeometry.ProjMapCard.Multiplication
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistSectionOn

/-!
# The structural isomorphisms of the inverse image are monoidal for the Tag 01CD comparison

Tag 01NO's canonical comparison on the `n`-th twist
(`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`) is six factors: three
components of the pseudofunctoriality isomorphisms of the inverse image
(`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, `pullbackComp`, `pullbackId`) and the functor
image of Tag 01MY's twist map. Tag 01MY's multiplication identity
(`Stacks.AlgebraicGeometry.ProjMapCard.projMapData_preserves_products`) is about the twist map
alone, and transporting it along the other five factors needs those five to be *monoidal* for
the Tag 01CD comparison `Stacks.PullbackTensorIso.pullbackTensorIso`. That is what this file
proves, for an arbitrary morphism of schemes and arbitrary sheaves of modules -- nothing here
mentions `Proj`.

## Main results

* `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp` and
  `comparison_pullbackComp_hom`: **the pseudofunctoriality isomorphism for a composite is
  monoidal**, in both directions.
* `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackId`: **the identification of
  the inverse image along the identity with the identity functor is monoidal.**
* `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackCongr_inv` and
  `comparison_pullbackCongr_hom`: **the congruence isomorphism for two equal morphisms is
  monoidal.**
* `Stacks.AlgebraicGeometry.TwistMultTransport.transport_congr_step`: the congruence factor's
  whole transport step, in one lemma, for the reason recorded below.

## Implementation notes

The extensionality principle the coherences below are proved with quantifies over **every** open
of the target, so what they need is the pullback unit against the structural isomorphisms over
an **arbitrary** open. That is `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn`,
together with `pullbackId_hom_pullbackSectionOn`, `pullbackComp_inv_pullbackSectionOn`,
`pullbackComp_hom_pullbackSectionOn` and `pullback_map_pullbackSectionOn`. The congruence factor
has no general-open analogue.

The two `pullbackComp` statements and the `pullbackId` statement are proved with
`Stacks.AlgebraicGeometry.ProjMapCard.pullbackTensor_hom_ext` -- two morphisms out of the
inverse image of a tensor product agree as soon as they agree on the pullback-unit images of the
sheafification-unit images of pure tensors -- and then the unit lemmas above compute both sides.
The `hom` direction for a composite is the `inv` direction cancelled on both sides, which is
`Stacks.AlgebraicGeometry.TwistMultTransport.comp_cancel_swap`.

The two `pullbackCongr` statements are proved by `subst`, after which
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso` of a reflexivity
proof and every component is the identity. No extensionality is involved and no transport
survives.

Elaboration obstacles that shape the proofs:

* **Evaluate composites at abstract morphisms.** `sheaf_comp_apply_eq` keeps the native paired
  tensor map opaque while computing a composite on a section, rather than unfolding both
  curried factors of that map during conversion.
* **`rw` and `simp` cannot match `CategoryTheory.Category.assoc` at these types.** The category
  instance on sheaves of modules on a scheme is reached through a `def`, so the pattern is
  invisible at reducible transparency. Every reassociation below is therefore an `exact`
  against a named lemma stated at the level of variables (`comp_cancel_swap`,
  `transport_congr_step`), never a rewrite at the instance.
* **A component of `pullbackCongr` must never be reached by unification.** It is `eqToIso` of a
  transport of the inverse image functor, and converting such a component against a second
  spelling of its module argument exhausts the deterministic budget (an `isDefEq` timeout).
  `transport_congr_step` takes the whole step at the level of variables and discharges it by
  `subst`.
* **Heartbeats are counted cumulatively over a declaration.** The extensionality reduction of
  `comparison_pullbackComp` and each of the transitivity steps that follow it fit in the budget
  on their own, but not together, so the elementwise chain is cut in half, as
  `comparison_pullbackComp_unit_left` and `comparison_pullbackComp_unit_right`, with the middle
  term -- the sheafification-unit image of the pure tensor of the twice-pulled-back sections --
  written out in both, so that neither half reaches it by unification.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjMapCard Stacks.AlgebraicGeometry.PullbackUnit
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistMultTransport

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

universe u

variable {X Y Z : Scheme.{u}}

private theorem sheaf_comp_apply_eq {Site : Type*} [Category Site]
    {topology : GrothendieckTopology Site} {coefficient : Sheaf topology RingCat.{u}}
    {source middle target : SheafOfModules.{u} coefficient}
    (first : source ⟶ middle) (second : middle ⟶ target) (openSet : Siteᵒᵖ)
    (sectionValue : source.val.obj openSet) (value : middle.val.obj openSet)
    (hypothesis : Hom.app first.val openSet sectionValue = value) :
    Hom.app (first ≫ second).val openSet sectionValue = Hom.app second.val openSet value :=
  congrArg (fun element => Hom.app second.val openSet element) hypothesis

/-! ### The Tag 01CD comparison against the structural isomorphisms -/

/-- **The left half of the composite comparison, elementwise.** The comparison for `f ≫ g`
followed by the tensor of the two components of the pseudofunctoriality isomorphism, evaluated on
the pullback-unit image of the sheafification-unit image of a pure tensor, is the
sheafification-unit image of the pure tensor of the twice-pulled-back sections. -/
private theorem comparison_pullbackComp_unit_left (f : X ⟶ Y) (g : Y ⟶ Z)
    (P Q : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
    (W : Opens Z.carrier) (x : P.val.obj (op W)) (y : Q.val.obj (op W)) :
    Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
            (f ≫ g).toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
              ((Scheme.Modules.pullback (f ≫ g)).obj P, (Scheme.Modules.pullback (f ≫ g)).obj Q))
              (Y := ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj P),
              (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj Q)))
              ((((Scheme.Modules.pullbackComp f g).inv.app P),
              ((Scheme.Modules.pullbackComp f g).inv.app Q)) : (_, _) ⟶ (_, _)))).val
        (op ((opensMap (f ≫ g).toLRSHom.toShHom).obj W))
        (pullbackUnit (f ≫ g).toLRSHom.toShHom
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) (op W)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)) (𝟙
              (Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Z.toRingedSpace).presheaf) (P).val (Q).val))
              (op W) (x ⊗ₜ y))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)) (𝟙
          (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
          (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj P))).val
          (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj Q))).val))
        (op ((f ≫ g) ⁻¹ᵁ W))
        (pullbackSectionOn f ((Scheme.Modules.pullback g).obj P) (g ⁻¹ᵁ W)
            (pullbackSectionOn g P W x) ⊗ₜ
          pullbackSectionOn f ((Scheme.Modules.pullback g).obj Q) (g ⁻¹ᵁ W)
            (pullbackSectionOn g Q W y)) := by
  refine Eq.trans (sheaf_comp_apply_eq
    ((Stacks.PullbackTensorIso.pullbackTensorIso (f ≫ g).toLRSHom.toShHom).hom.app (P, Q))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
      (X := ((Scheme.Modules.pullback (f ≫ g)).obj P, (Scheme.Modules.pullback (f ≫ g)).obj Q))
      (Y := ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj P),
        (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj Q)))
      ((Scheme.Modules.pullbackComp f g).inv.app P, (Scheme.Modules.pullbackComp f g).inv.app Q))
    (op ((f ≫ g) ⁻¹ᵁ W)) _ _
    (comparison_pullbackUnit_tensorSheafUnit (f ≫ g).toLRSHom.toShHom P Q W x y)) ?_
  refine Eq.trans (tensorSheaf_map_unit_tmul X.toRingedSpace
    ((Scheme.Modules.pullbackComp f g).inv.app P)
    ((Scheme.Modules.pullbackComp f g).inv.app Q) (op ((f ≫ g) ⁻¹ᵁ W)) _ _) ?_
  exact congrArg (fun z => Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)) (𝟙
      (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
      (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj P))).val
      (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj Q))).val))
        (op ((f ≫ g) ⁻¹ᵁ W)) z)
    (congrArg₂ (fun a b => a ⊗ₜ b)
      (pullbackComp_inv_pullbackSectionOn f g P W x)
      (pullbackComp_inv_pullbackSectionOn f g Q W y))

/-- **The right half of the composite comparison, elementwise.** The same middle term is the
value of the other side of `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp`
on the same element: the pseudofunctoriality isomorphism first, then the comparison for `g`
pulled back along `f`, then the comparison for `f`. -/
private theorem comparison_pullbackComp_unit_right (f : X ⟶ Y) (g : Y ⟶ Z)
    (P Q : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
    (W : Opens Z.carrier) (x : P.val.obj (op W)) (y : Q.val.obj (op W)) :
    Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf
        (X.toRingedSpace)) (𝟙 (Stacks.RingedSpace.structureRingSheaf
        (X.toRingedSpace)).obj)).unit.app (PresheafOfModules.tensorObj (O :=
        (X.toRingedSpace).presheaf) (((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback g).obj P))).val (((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback g).obj Q))).val))
        (op ((f ≫ g) ⁻¹ᵁ W))
        (pullbackSectionOn f ((Scheme.Modules.pullback g).obj P) (g ⁻¹ᵁ W)
            (pullbackSectionOn g P W x) ⊗ₜ
          pullbackSectionOn f ((Scheme.Modules.pullback g).obj Q) (g ⁻¹ᵁ W)
            (pullbackSectionOn g Q W y)) =
      Hom.app ((Scheme.Modules.pullbackComp f g).inv.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) ≫
          (Scheme.Modules.pullback f).map
              ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q)) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
              ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)).val
        (op ((opensMap (f ≫ g).toLRSHom.toShHom).obj W))
        (pullbackUnit (f ≫ g).toLRSHom.toShHom
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) (op W)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)) (𝟙
              (Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Z.toRingedSpace).presheaf) (P).val (Q).val))
              (op W) (x ⊗ₜ y))) := by
  refine Eq.trans ?_ (congrArg
    (((Scheme.Modules.pullback f).map
        ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q)) ≫
      (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
        ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)).val.app
      (op ((f ≫ g) ⁻¹ᵁ W)))
    (pullbackComp_inv_pullbackSectionOn f g
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) W
      (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)) (𝟙
          (Stacks.RingedSpace.structureRingSheaf (Z.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (Z.toRingedSpace).presheaf) (P).val (Q).val)) (op W)
          (x ⊗ₜ y)))).symm
  refine Eq.trans ?_ (congrArg
    (((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
        ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)).val.app
      (op (f ⁻¹ᵁ (g ⁻¹ᵁ W))))
    (pullbackUnit_naturality f.toLRSHom.toShHom
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q))
      (op (g ⁻¹ᵁ W)) _)).symm
  refine Eq.trans ?_ (congrArg
    (((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
        ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)).val.app
      (op (f ⁻¹ᵁ (g ⁻¹ᵁ W))))
    (congrArg (pullbackUnit f.toLRSHom.toShHom _ (op (g ⁻¹ᵁ W)))
      (comparison_pullbackUnit_tensorSheafUnit g.toLRSHom.toShHom P Q W x y))).symm
  exact (comparison_pullbackUnit_tensorSheafUnit f.toLRSHom.toShHom
    ((Scheme.Modules.pullback g).obj P) ((Scheme.Modules.pullback g).obj Q) (g ⁻¹ᵁ W)
    (pullbackUnit g.toLRSHom.toShHom P (op W) x)
    (pullbackUnit g.toLRSHom.toShHom Q (op W) y)).symm

/-- The comparison, for a composite, against the pseudofunctoriality isomorphism. -/
public theorem comparison_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (P Q : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)) :
    (Stacks.PullbackTensorIso.pullbackTensorIso (f ≫ g).toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback (f ≫ g)).obj P, (Scheme.Modules.pullback (f ≫ g)).obj Q))
            (Y := ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj P),
            (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj Q)))
            ((((Scheme.Modules.pullbackComp f g).inv.app P),
            ((Scheme.Modules.pullbackComp f g).inv.app Q)) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackComp f g).inv.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) ≫
        (Scheme.Modules.pullback f).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q)) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q) :=
  pullbackTensor_hom_ext (f ≫ g).toLRSHom.toShHom P Q _ _ fun W x y =>
    (comparison_pullbackComp_unit_left f g P Q W x y).trans
      (comparison_pullbackComp_unit_right f g P Q W x y)

/-! ### The remaining structural comparisons -/

/-- The tensor product of two identities is the identity. -/
public theorem tensorSheafMap_id (W : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureRingSheaf W)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((W)).presheaf,
        ((W)).IsSheaf⟩)).map (((𝟙 A), (𝟙 B)) : (_, _) ⟶ (_, _))) = 𝟙 _ :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((W)).presheaf,
      ((W)).IsSheaf⟩))).map_id (A, B)

/-- The tensor product of two composites is the composite of the tensor products. -/
public theorem tensorSheafMap_comp (W : RingedSpace.{u, u})
    {A A' A'' B B' B'' : SheafOfModules.{u} (structureRingSheaf W)}
    (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((W)).presheaf,
        ((W)).IsSheaf⟩)).map (((a ≫ a'), (b ≫ b')) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((W)).presheaf, ((W)).IsSheaf⟩)).map ((a, b) : (_, _) ⟶ (_, _))) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((W)).presheaf, ((W)).IsSheaf⟩)).map ((a', b') : (_, _) ⟶ (_, _))) :=
  (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_comp W a a' b b').symm

/-- A component of the congruence isomorphism along a reflexivity proof is the identity. -/
public theorem pullbackCongr_rfl_inv_app (f : X ⟶ Y) (P : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).inv.app P = 𝟙 _ := rfl

/-- The same for the `hom` direction. -/
public theorem pullbackCongr_rfl_hom_app (f : X ⟶ Y) (P : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app P = 𝟙 _ := rfl

/-- The tensor product of two endomorphisms that are identities is the identity. -/
private theorem tensorSheafMap_eq_id (W : RingedSpace.{u, u})
    {A B : SheafOfModules.{u} (structureRingSheaf W)} {a : A ⟶ A} {b : B ⟶ B}
    (ha : a = 𝟙 A) (hb : b = 𝟙 B) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((W)).presheaf,
        ((W)).IsSheaf⟩)).map ((a, b) : (_, _) ⟶ (_, _))) = 𝟙 _ :=
  (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.presheaf, W.IsSheaf⟩)).map (X := (A, B)) (Y := (A, B))) (Prod.ext ha hb)).trans
    (tensorSheafMap_id W _ _)

/-- The comparison commutes with a pair of identity components and an identity component of the
pulled-back tensor product. -/
private theorem comparison_comp_map_eq_comp_of_eq_id (f : X ⟶ Y)
    (P Q : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace))
    {a : (Scheme.Modules.pullback f).obj P ⟶ (Scheme.Modules.pullback f).obj P}
    {b : (Scheme.Modules.pullback f).obj Q ⟶ (Scheme.Modules.pullback f).obj Q}
    {c : (Scheme.Modules.pullback f).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (P)).obj (Q)) ⟶
      (Scheme.Modules.pullback f).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (P)).obj (Q))}
    (ha : a = 𝟙 _) (hb : b = 𝟙 _) (hc : c = 𝟙 _) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
            ((a, b) : (_, _) ⟶ (_, _))) =
      c ≫ (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) := by
  refine Eq.trans (congrArg (fun k =>
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫ k)
      (tensorSheafMap_eq_id X.toRingedSpace ha hb)) ?_
  refine Eq.trans (Category.comp_id _) ?_
  refine Eq.trans (Category.id_comp _).symm ?_
  exact congrArg (fun k => k ≫
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q)) hc.symm

/-- The comparison against the congruence isomorphism, backwards. -/
public theorem comparison_pullbackCongr_inv {f g : X ⟶ Y} (hf : f = g)
    (P Q : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)) :
    (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) (Y :=
            ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q))
            ((((Scheme.Modules.pullbackCongr hf).inv.app P),
            ((Scheme.Modules.pullbackCongr hf).inv.app Q)) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackCongr hf).inv.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (P)).obj (Q))) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) := by
  subst hf
  exact comparison_comp_map_eq_comp_of_eq_id f P Q (pullbackCongr_rfl_inv_app f P)
    (pullbackCongr_rfl_inv_app f Q) (pullbackCongr_rfl_inv_app f _)

/-- The comparison against the congruence isomorphism, forwards. -/
public theorem comparison_pullbackCongr_hom {f g : X ⟶ Y} (hf : f = g)
    (P Q : SheafOfModules.{u} (structureRingSheaf Y.toRingedSpace)) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q)) (Y :=
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            ((((Scheme.Modules.pullbackCongr hf).hom.app P),
            ((Scheme.Modules.pullbackCongr hf).hom.app Q)) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackCongr hf).hom.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (P)).obj (Q))) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) := by
  subst hf
  exact comparison_comp_map_eq_comp_of_eq_id f P Q (pullbackCongr_rfl_hom_app f P)
    (pullbackCongr_rfl_hom_app f Q) (pullbackCongr_rfl_hom_app f _)

/-- The comparison against the identification of the pullback along the identity. -/
public theorem comparison_pullbackId (W : Scheme.{u})
    (P Q : SheafOfModules.{u} (structureRingSheaf W.toRingedSpace)) :
    (Stacks.PullbackTensorIso.pullbackTensorIso
          (𝟙 W : W ⟶ W).toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback (𝟙 W)).obj P, (Scheme.Modules.pullback (𝟙 W)).obj Q)) (Y :=
            (P, Q)) ((((Scheme.Modules.pullbackId W).hom.app P),
            ((Scheme.Modules.pullbackId W).hom.app Q)) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackId W).hom.app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) := by
  refine pullbackTensor_hom_ext (𝟙 W : W ⟶ W).toLRSHom.toShHom P Q _ _ fun V x y => ?_
  refine Eq.trans (sheaf_comp_apply_eq
    ((Stacks.PullbackTensorIso.pullbackTensorIso (𝟙 W : W ⟶ W).toLRSHom.toShHom).hom.app (P, Q))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
      (X := ((Scheme.Modules.pullback (𝟙 W)).obj P, (Scheme.Modules.pullback (𝟙 W)).obj Q))
      (Y := (P, Q)) ((Scheme.Modules.pullbackId W).hom.app P,
        (Scheme.Modules.pullbackId W).hom.app Q)) (op V) _ _
    (comparison_pullbackUnit_tensorSheafUnit (𝟙 W : W ⟶ W).toLRSHom.toShHom P Q V x y)) ?_
  refine Eq.trans (tensorSheaf_map_unit_tmul W.toRingedSpace
    ((Scheme.Modules.pullbackId W).hom.app P)
    ((Scheme.Modules.pullbackId W).hom.app Q) (op V) _ _) ?_
  refine Eq.trans (congrArg
    (fun z => Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace)) (𝟙
        (Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (W.toRingedSpace).presheaf) (P).val (Q).val)) (op V) z)
    (congrArg₂ (fun a b => a ⊗ₜ b)
      (pullbackId_hom_pullbackSectionOn W P V x)
      (pullbackId_hom_pullbackSectionOn W Q V y))) ?_
  exact (pullbackId_hom_pullbackSectionOn W
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) V
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace)) (𝟙
        (Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (W.toRingedSpace).presheaf) (P).val (Q).val)) (op V)
        (x ⊗ₜ y))).symm

section Cancel

variable {C : Type*} [Category C]

/-- A two-sided cancellation, at the level of variables so that `rw` can be used: from a
commuting square with an invertible vertical and an invertible horizontal, the square with both
inverted commutes.

Stated generically on purpose. At the concrete instances below neither `rw` nor `simp` can match
`CategoryTheory.Category.assoc`, because the category instance on sheaves of modules on a scheme
is reached through a `def` and the pattern is therefore invisible at reducible transparency; an
`exact` against this lemma unifies instead of rewriting. -/
public theorem comp_cancel_swap {A A' B B' : C} {ch : A' ⟶ A} {c : A ⟶ A'} {d : A ⟶ B}
    {t : B ⟶ B'} {t' : B' ⟶ B} {e : A' ⟶ B'} (hc : ch ≫ c = 𝟙 A') (ht : t ≫ t' = 𝟙 B)
    (h : d ≫ t = c ≫ e) : e ≫ t' = ch ≫ d := by
  rw [← Category.comp_id d, ← ht, ← Category.assoc d t t', h, Category.assoc,
    ← Category.assoc ch c, hc, Category.id_comp]

end Cancel

/-- The comparison, for a composite, against the pseudofunctoriality isomorphism, forwards. -/
public theorem comparison_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (P Q : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)) :
    ((Scheme.Modules.pullback f).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q)) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj P),
            (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj Q))) (Y :=
            ((Scheme.Modules.pullback (f ≫ g)).obj P, (Scheme.Modules.pullback (f ≫ g)).obj Q))
            ((((Scheme.Modules.pullbackComp f g).hom.app P),
            ((Scheme.Modules.pullbackComp f g).hom.app Q)) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackComp f g).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))).obj (P, Q)) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso
          (f ≫ g).toLRSHom.toShHom).hom.app (P, Q) :=
  comp_cancel_swap (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp f g) _)
    ((tensorSheafMap_comp X.toRingedSpace _ _ _ _).symm.trans
      (tensorSheafMap_eq_id X.toRingedSpace (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp f g) P)
        (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp f g) Q)))
    (comparison_pullbackComp f g P Q)

/-- **The congruence factor of the transport, in one step.** The leading factor of Tag 01NO's
comparison is a component of `AlgebraicGeometry.Scheme.Modules.pullbackCongr`, which is
`CategoryTheory.eqToIso` of a transport of the pullback functor, and converting such a
component against a second spelling of its module argument exhausts the deterministic budget.
So this step is taken at the level of variables and discharged by `subst`, after which the
component is the identity and no transport survives. -/
public theorem transport_congr_step {f g : X ⟶ Y} (hf : f = g)
    {P Q R : Y.Modules} {Pf Qf E : X.Modules}
    (mult : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (P)).obj (Q)) ⟶ R)
    (r' : (Scheme.Modules.pullback f).obj R ⟶ E)
    (rP : (Scheme.Modules.pullback f).obj P ⟶ Pf)
    (rQ : (Scheme.Modules.pullback f).obj Q ⟶ Qf)
    (multF : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Pf)).obj (Qf)) ⟶ E)
    (ih : (Scheme.Modules.pullback f).map mult ≫ r' =
      (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q)) (Y := (Pf, Qf))
            ((rP, rQ) : (_, _) ⟶ (_, _))) ≫ multF) :
    (Scheme.Modules.pullback g).map mult ≫
        ((Scheme.Modules.pullbackCongr hf).inv.app R ≫ r') =
      (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X :=
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) (Y := (Pf, Qf))
            ((((Scheme.Modules.pullbackCongr hf).inv.app P ≫ rP),
            ((Scheme.Modules.pullbackCongr hf).inv.app Q ≫ rQ)) : (_, _) ⟶ (_, _))) ≫ multF := by
  subst hf
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.pullback f).map mult ≫ z ≫ r')
    (pullbackCongr_rfl_inv_app f R)) ?_
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.pullback f).map mult ≫ z)
    (Category.id_comp r')) ?_
  refine Eq.trans ih ?_
  refine congrArg (fun z =>
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
      z ≫ multF) ?_
  refine congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
    (X := ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q))
    (Y := (Pf, Qf))) (Prod.ext ?_ ?_)
  · exact (Category.id_comp rP).symm.trans
      (congrArg (fun z => z ≫ rP) (pullbackCongr_rfl_inv_app f P).symm)
  · exact (Category.id_comp rQ).symm.trans
      (congrArg (fun z => z ≫ rQ) (pullbackCongr_rfl_inv_app f Q).symm)

end Stacks.AlgebraicGeometry.TwistMultTransport

end
