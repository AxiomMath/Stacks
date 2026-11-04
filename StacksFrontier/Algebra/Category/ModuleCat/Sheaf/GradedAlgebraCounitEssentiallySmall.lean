module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The counit of the graded pullback-pushforward adjunction, at unrelated universes

This is the counit half of the graded pullback-pushforward adjunction, and part (3) of Stacks 0FQX,
with the objects, the morphisms and the sections of the structure sheaf of the ringed topos in
three unrelated universes, so that it applies to
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, a `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`.
The hypotheses are the original ones together with `CategoryTheory.EssentiallySmall.{w} Y.C`,
which is what the identification of local sections of a direct image needs.

## Main definitions

* `counitApp` is the counit as a homomorphism of sheaves of graded algebras.
* `gradedAlgebraPullbackPushforwardAdjunction` is part (3) of Stacks 0FQX: pullback of sheaves
  of graded algebras is left adjoint to the direct image, with the direct-image graded algebras
  as the values of the right adjoint on objects.

## Main results

* `scalarExtension_induction`, `scalarExtension_ext_left` and `scalarExtension_bilinear_ext`:
  two maps out of an extension of scalars that agree on pure tensors agree.
* `counit_mul_inverseImageSections` and `counit_mul_scalarUnit`: the counit preserves products
  of homogeneous local sections, first on inverse-image sections and then on pure tensors.

## Implementation notes

Nothing here passes through the identification of local sections of a sheaf of sets, so this
file is the original argument with the universes of the ringed topos separated and no further
change; the universe-bound step lives in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedAlgebraPushforwardEssentiallySmall.lean`.
The two ringed topoi share their three universes, as they do in
`Stacks.Sheaves.GradedAlgebraPullback`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry TensorProduct Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraExtendScalars
open Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraPullback
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

variable {X Y : RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-! ### Local generation of an extension of scalars by the change-of-rings unit -/

/-- The extension of scalars along the inverse-image form of the structure map: the
change-of-rings half of the pullback of sheaves of modules. -/
public noncomputable abbrev scalarExtend
    (M : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (extendScalarsFSharp f.toRingedToposModulesHom).obj M

/-- The change-of-rings unit, read on a local section: the pure tensor `1 ⊗ x`. -/
public noncomputable abbrev scalarUnitAt
    (M : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (U : X.Cᵒᵖ) (x : M.val.obj U) : (scalarExtend f M).val.obj U :=
  ((scalarAdjunction f).unit.app M).val.app U x

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
omit [EssentiallySmall.{w} Y.C] in
/-- **Induction over an extension of scalars.** A property of local sections of an extension of
scalars which holds on the images of the change-of-rings unit, and which is stable under zero,
sums, scalars, restriction and locality, holds of every local section.

The property cuts out a submodule, whose locality is exactly the sheaf condition of a submodule
of a sheaf of modules, and the submodule is everything by
`scalarExtension_submodule_eq_top`. -/
public theorem scalarExtension_induction
    (M : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (predicate : ∀ U : X.Cᵒᵖ, (scalarExtend f M).val.obj U → Prop)
    (zero : ∀ U, predicate U 0)
    (add : ∀ U x y, predicate U x → predicate U y → predicate U (x + y))
    (smul : ∀ (U : X.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) x,
      predicate U x → predicate U (r • x))
    (restriction : ∀ {U V : X.Cᵒᵖ} (g : U ⟶ V) x, predicate U x →
      predicate V (Stacks.sectionRestrict (scalarExtend f M).val g x))
    (locality : ∀ (U : X.Cᵒᵖ) x (cover : Sieve U.unop), cover ∈ X.J U.unop →
      (∀ (V : X.C) (g : V ⟶ U.unop), cover g →
        predicate (Opposite.op V) (Stacks.sectionRestrict (scalarExtend f M).val g.op x)) →
      predicate U x)
    (generator : ∀ U x, predicate U (scalarUnitAt f M U x)) :
    ∀ U x, predicate U x := by
  let sub : (scalarExtend f M).Submodule :=
    { obj := fun U =>
        { carrier := {x | predicate U x}
          zero_mem' := zero U
          add_mem' := add U _ _
          smul_mem' := fun r {x} hx => smul U r x hx }
      map := fun g x hx => restriction g x hx
      isSheaf := fun {U} x cover => locality U x _ cover (fun _ _ member => member) }
  exact fun U x => scalarExtension_submodule_eq_top f M sub generator U x

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Two local sections of a sheaf of modules whose restrictions along a covering sieve agree are
equal. -/
public theorem moduleSection_eq_of_cover
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.Cᵒᵖ) (cover : Sieve U.unop) (covering : cover ∈ X.J U.unop)
    (left right : P.val.obj U)
    (local_eq : ∀ (V : X.C) (g : V ⟶ U.unop), cover g →
      Stacks.sectionRestrict P.val g.op left = Stacks.sectionRestrict P.val g.op right) :
    left = right := by
  have sheaf := (isSheaf_iff_isSheaf_of_type X.J _).mp
    (Stacks.underlyingModuleSheaf X.J P).property
  exact (sheaf cover covering).isSeparatedFor.ext local_eq

omit [EssentiallySmall.{w} Y.C] in
omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **A map out of an extension of scalars is determined by its values on the images of the
change-of-rings unit**, as soon as it is additive, linear and compatible with restriction in
that variable. The second variable is an arbitrary family of types with restriction, so that
the statement can be instantiated both with the second variable ranging over another extension
of scalars and with it ranging over an unextended sheaf of modules. -/
public theorem scalarExtension_ext_left
    (M : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : X.Cᵒᵖ → Type w} (rest : ∀ {U V : X.Cᵒᵖ}, (U ⟶ V) → T U → T V)
    (L R : ∀ U : X.Cᵒᵖ, (scalarExtend f M).val.obj U → T U → P.val.obj U)
    (Lzero : ∀ U t, L U 0 t = 0) (Rzero : ∀ U t, R U 0 t = 0)
    (Ladd : ∀ U a b t, L U (a + b) t = L U a t + L U b t)
    (Radd : ∀ U a b t, R U (a + b) t = R U a t + R U b t)
    (Lsmul : ∀ (U : X.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) a t,
      L U (r • a) t = r • L U a t)
    (Rsmul : ∀ (U : X.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) a t,
      R U (r • a) t = r • R U a t)
    (Lnat : ∀ {U V : X.Cᵒᵖ} (g : U ⟶ V) a t, Stacks.sectionRestrict P.val g (L U a t) =
      L V (Stacks.sectionRestrict (scalarExtend f M).val g a) (rest g t))
    (Rnat : ∀ {U V : X.Cᵒᵖ} (g : U ⟶ V) a t, Stacks.sectionRestrict P.val g (R U a t) =
      R V (Stacks.sectionRestrict (scalarExtend f M).val g a) (rest g t))
    (generators : ∀ U x t, L U (scalarUnitAt f M U x) t = R U (scalarUnitAt f M U x) t) :
    ∀ U a t, L U a t = R U a t := by
  have key : ∀ (W : X.Cᵒᵖ) (z : (scalarExtend f M).val.obj W),
      ∀ (V : X.Cᵒᵖ) (g : W ⟶ V) (t : T V),
        L V (Stacks.sectionRestrict (scalarExtend f M).val g z) t =
          R V (Stacks.sectionRestrict (scalarExtend f M).val g z) t := by
    refine scalarExtension_induction f M
      (fun W z => ∀ (V : X.Cᵒᵖ) (g : W ⟶ V) (t : T V),
        L V (Stacks.sectionRestrict (scalarExtend f M).val g z) t =
          R V (Stacks.sectionRestrict (scalarExtend f M).val g z) t) ?_ ?_ ?_ ?_ ?_ ?_
    · intro W V g t
      rw [map_zero, Lzero, Rzero]
    · intro W z z' hz hz' V g t
      rw [map_add, Ladd, Radd, hz V g t, hz' V g t]
    · intro W r z hz V g t
      rw [Stacks.sectionRestrict_smul, Lsmul, Rsmul, hz V g t]
    · intro W V g z hz Z h t
      rw [← Stacks.sectionRestrict_comp, hz Z (g ≫ h) t]
    · intro W z cover covering local_h V g t
      refine moduleSection_eq_of_cover P V (cover.pullback g.unop)
        (X.J.pullback_stable g.unop covering) _ _ fun Z h member => ?_
      rw [Lnat, Rnat, ← Stacks.sectionRestrict_comp]
      have inst := local_h Z (h ≫ g.unop) member (Opposite.op Z) (CategoryStruct.id _)
        (rest h.op t)
      rw [Stacks.sectionRestrict_id] at inst
      exact inst
    · intro W z V g t
      have unitNat : ((scalarAdjunction f).unit.app M).val.app V
            (Stacks.sectionRestrict M.val g z) =
          Stacks.sectionRestrict (scalarExtend f M).val g (scalarUnitAt f M W z) :=
        PresheafOfModules.naturality_apply ((scalarAdjunction f).unit.app M).val g z
      rw [← unitNat, generators]
  intro U a t
  have equation := key U a U (CategoryStruct.id U) t
  rwa [Stacks.sectionRestrict_id] at equation

omit [EssentiallySmall.{w} Y.C] in
omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **A bilinear map of two extensions of scalars is determined by its values on the images of
the change-of-rings units.** The second variable is reduced to those images first, with the
first variable arbitrary, and the first variable is reduced afterwards. -/
public theorem scalarExtension_bilinear_ext
    (M N : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (left right : SheafOfModules.BilinearMap (scalarExtend f M) (scalarExtend f N) P)
    (generators : ∀ (U : X.Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      left.app U (scalarUnitAt f M U x) (scalarUnitAt f N U y) =
        right.app U (scalarUnitAt f M U x) (scalarUnitAt f N U y)) :
    ∀ (U : X.Cᵒᵖ) a b, left.app U a b = right.app U a b := by
  have natL : ∀ {U V : X.Cᵒᵖ} (g : U ⟶ V) (a : (scalarExtend f M).val.obj U)
      (b : (scalarExtend f N).val.obj U),
      Stacks.sectionRestrict P.val g (left.app U a b) =
        left.app V (Stacks.sectionRestrict (scalarExtend f M).val g a)
          (Stacks.sectionRestrict (scalarExtend f N).val g b) :=
    fun g a b => left.naturality g a b
  have natR : ∀ {U V : X.Cᵒᵖ} (g : U ⟶ V) (a : (scalarExtend f M).val.obj U)
      (b : (scalarExtend f N).val.obj U),
      Stacks.sectionRestrict P.val g (right.app U a b) =
        right.app V (Stacks.sectionRestrict (scalarExtend f M).val g a)
          (Stacks.sectionRestrict (scalarExtend f N).val g b) :=
    fun g a b => right.naturality g a b
  have unitNatN : ∀ {U V : X.Cᵒᵖ} (g : U ⟶ V) (y : N.val.obj U),
      scalarUnitAt f N V (Stacks.sectionRestrict N.val g y) =
        Stacks.sectionRestrict (scalarExtend f N).val g (scalarUnitAt f N U y) :=
    fun g y => PresheafOfModules.naturality_apply ((scalarAdjunction f).unit.app N).val g y
  have step : ∀ (U : X.Cᵒᵖ) (a : (scalarExtend f M).val.obj U) (y : N.val.obj U),
      left.app U a (scalarUnitAt f N U y) = right.app U a (scalarUnitAt f N U y) := by
    refine scalarExtension_ext_left f M P (T := fun U => N.val.obj U)
      (fun g y => Stacks.sectionRestrict N.val g y)
      (fun U a y => left.app U a (scalarUnitAt f N U y))
      (fun U a y => right.app U a (scalarUnitAt f N U y))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ generators
    · exact fun U y => congrArg (fun k => k (scalarUnitAt f N U y)) (map_zero (left.app U))
    · exact fun U y => congrArg (fun k => k (scalarUnitAt f N U y)) (map_zero (right.app U))
    · exact fun U a b y =>
        congrArg (fun k => k (scalarUnitAt f N U y)) (map_add (left.app U) a b)
    · exact fun U a b y =>
        congrArg (fun k => k (scalarUnitAt f N U y)) (map_add (right.app U) a b)
    · exact fun U r a y => left.map_smul_left U r a _
    · exact fun U r a y => right.map_smul_left U r a _
    · exact fun {U V} g a y => (natL g a _).trans
        (congrArg (left.app V (Stacks.sectionRestrict (scalarExtend f M).val g a))
          (unitNatN g y).symm)
    · exact fun {U V} g a y => (natR g a _).trans
        (congrArg (right.app V (Stacks.sectionRestrict (scalarExtend f M).val g a))
          (unitNatN g y).symm)
  refine fun U a b => ?_
  refine scalarExtension_ext_left f N P (T := fun U => (scalarExtend f M).val.obj U)
    (fun g a => Stacks.sectionRestrict (scalarExtend f M).val g a)
    (fun U b a => left.app U a b) (fun U b a => right.app U a b)
    (fun U a => map_zero (left.app U a)) (fun U a => map_zero (right.app U a))
    (fun U b b' a => map_add (left.app U a) b b') (fun U b b' a => map_add (right.app U a) b b')
    (fun U r b a => left.map_smul_right U r a b) (fun U r b a => right.map_smul_right U r a b)
    (fun {U V} g b a => natL g a b) (fun {U V} g b a => natR g a b)
    (fun U y a => step U a y) U b a

/-! ### Postcomposition of a bilinear map with a morphism of presheaves of modules -/

section Postcomp

variable {C : Type u₁} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {M N P Q : PresheafOfModules.{w} R}

/-- **Postcomposition of a bilinear map with a morphism out of its target.** The two
restrictions of a bilinear map along morphisms in its variables are
`Stacks.BilinearMap.compLeft` and `compRight`; this is the remaining composition. -/
public noncomputable def bilinearPostcomp (b : Stacks.BilinearMap M N P) (g : P ⟶ Q) :
    Stacks.BilinearMap M N Q where
  app U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.comp (ConcreteCategory.hom (g.app U)).toAddMonoidHom (b.app U x))
    (fun x x' => AddMonoidHom.ext fun y => by
      change (ConcreteCategory.hom (g.app U)) (b.app U (x + x') y) = _
      rw [b.map_add_left, map_add]
      rfl)
  map_smul_left U r x y := by
    change (ConcreteCategory.hom (g.app U)) (b.app U (r • x) y) =
      r • (ConcreteCategory.hom (g.app U)) (b.app U x y)
    rw [b.map_smul_left, _root_.map_smul]
  map_smul_right U r x y := by
    change (ConcreteCategory.hom (g.app U)) (b.app U x (r • y)) =
      r • (ConcreteCategory.hom (g.app U)) (b.app U x y)
    rw [b.map_smul_right, _root_.map_smul]
  naturality {U V} k x y := by
    change Q.map k ((ConcreteCategory.hom (g.app U)) (b.app U x y)) =
      (ConcreteCategory.hom (g.app V)) (b.app V (M.map k x) (N.map k y))
    rw [← PresheafOfModules.naturality_apply g k, b.naturality k]

/-- Postcomposition of a bilinear map, on sections. -/
public theorem bilinearPostcomp_app (b : Stacks.BilinearMap M N P) (g : P ⟶ Q) (U : Cᵒᵖ)
    (x : M.obj U) (y : N.obj U) :
    (bilinearPostcomp b g).app U x y = (ConcreteCategory.hom (g.app U)) (b.app U x y) := rfl

end Postcomp

/-! ### The counit on underlying sheaves of sets -/

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EssentiallySmall.{w} Y.C] in
/-- The direct image of a morphism of sheaves of modules along a morphism of ringed topoi is,
on underlying sheaves of sets, the direct image of the underlying morphism. -/
public theorem moduleSheafFunctor_map_pushforwardModules_map
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : M ⟶ N) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pushforwardModules.map g) =
      f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g) := rfl

omit [EssentiallySmall.{w} Y.C] in
/-- **The change-of-rings half of the unit at a direct image, followed by the counit of the
pullback adjunction, is the counit of the underlying adjunction of topoi.**

Both sides have the same adjunct: the adjunct of the left-hand side is the underlying morphism
of the composite of the unit and the direct image of the counit, which is the identity by the
triangle identity, and the adjunct of a counit component is the identity. -/
public theorem pullbackScalarUnit_comp_counit
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    pullbackScalarUnit f (f.pushforwardModules.obj N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (f.pullbackAdjPushforwardModulesViaComparison.counit.app N) =
      f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J N) := by
  refine (f.toToposHom.adj.homEquiv
    (Stacks.underlyingModuleSheaf Y.J (f.pushforwardModules.obj N))
    (Stacks.underlyingModuleSheaf X.J N)).injective ?_
  refine Eq.trans (f.toToposHom.adj.homEquiv_naturality_right
    (pullbackScalarUnit f (f.pushforwardModules.obj N)) _) ?_
  refine Eq.trans (congrArg (fun k => k ≫ f.toToposHom.pushforward.map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        (f.pullbackAdjPushforwardModulesViaComparison.counit.app N)))
    (moduleSheafFunctor_map_pullbackUnit f (f.pushforwardModules.obj N)).symm) ?_
  refine Eq.trans (congrArg (fun k =>
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pullbackAdjPushforwardModulesViaComparison.unit.app (f.pushforwardModules.obj N)) ≫ k)
    (moduleSheafFunctor_map_pushforwardModules_map f
      (f.pullbackAdjPushforwardModulesViaComparison.counit.app N)).symm) ?_
  refine Eq.trans
    (((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _).symm) ?_
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (f.pullbackAdjPushforwardModulesViaComparison.right_triangle_components N)) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_id _) ?_
  exact ((congrArg (f.toToposHom.adj.homEquiv _ _)
      (f.toToposHom.adj.homEquiv_symm_id
        (Stacks.underlyingModuleSheaf X.J N)).symm).trans
    (Equiv.apply_symm_apply _ _)).symm


/-! ### Multiplicativity of the counit of the adjunction of topoi -/

omit [EssentiallySmall.{w} Y.C] in
omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The adjunct of a component of the counit of the adjunction of topoi is the identity. -/
public theorem homEquiv_counit_app (B : Sheaf X.J (Type w)) :
    f.toToposHom.adj.homEquiv (f.toToposHom.pushforward.obj B) B
        (f.toToposHom.adj.counit.app B) =
      CategoryTheory.CategoryStruct.id (f.toToposHom.pushforward.obj B) :=
  (congrArg (f.toToposHom.adj.homEquiv _ _)
      (f.toToposHom.adj.homEquiv_symm_id B).symm).trans
    (Equiv.apply_symm_apply _ _)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The multiplication of a sheaf of graded algebras, read as a morphism of the underlying
sheaves of sets, evaluated on a local section of the product. -/
public theorem mulSheafHom_app
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) (V : X.Cᵒᵖ)
    (w : (Stacks.underlyingModuleSheaf X.J (A.piece i) ⨯
      Stacks.underlyingModuleSheaf X.J (A.piece j)).obj.obj V) :
    (mulSheafHom A i j).hom.app V w =
      (A.mul i j).app V
        ((Limits.prod.fst : Stacks.underlyingModuleSheaf X.J (A.piece i) ⨯
          Stacks.underlyingModuleSheaf X.J (A.piece j) ⟶ _).hom.app V w)
        ((Limits.prod.snd : Stacks.underlyingModuleSheaf X.J (A.piece i) ⨯
          Stacks.underlyingModuleSheaf X.J (A.piece j) ⟶ _).hom.app V w) := rfl

/-- **The direct image of the multiplication of a sheaf of graded algebras is the
multiplication of its direct image, read through the product comparison.**

A local section of a direct image is a morphism out of the inverse image of a sheafified Yoneda
object, the multiplication of the direct image is pointwise multiplication in the source algebra
on such morphisms, and the two projections of the product comparison are the direct images of
the two projections. -/
public theorem prodComparison_comp_mulSheafHom
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) :
    Limits.prodComparison f.toToposHom.pushforward
          (Stacks.underlyingModuleSheaf X.J (A.piece i))
          (Stacks.underlyingModuleSheaf X.J (A.piece j)) ≫
        mulSheafHom (pushforwardGradedAlgebra f A) i j =
      f.toToposHom.pushforward.map (mulSheafHom A i j) := by
  refine Sheaf.hom_ext_sections fun U z => ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ z) ?_
  refine Eq.trans (congrArg
    ((Sheaf.sectionsFunctor Y.J U).map (mulSheafHom (pushforwardGradedAlgebra f A) i j))
    (CategoryTheory.Functor.map_prodComparison_apply (P := Sheaf.sectionsFunctor Y.J U)
      f.toToposHom.pushforward (Stacks.underlyingModuleSheaf X.J (A.piece i))
      (Stacks.underlyingModuleSheaf X.J (A.piece j)) z)) ?_
  refine Eq.trans (sections_mulSheafHom (pushforwardGradedAlgebra f A) i j U _ _) ?_
  refine Eq.trans (pushforwardGradedAlgebra_mul_app f A i j U _ _) ?_
  refine Eq.trans ?_ (Sheaf.sectionsFunctor_map_apply
    (f.toToposHom.pushforward.map (mulSheafHom A i j)) z).symm
  refine (transposedSectionEquiv f U
    (Stacks.underlyingModuleSheaf X.J (A.piece (i + j)))).injective ?_
  refine Eq.trans ?_ (transposedSectionEquiv_comp f U (mulSheafHom A i j) z).symm
  refine Sheaf.hom_ext_sections fun V e => ?_
  refine Eq.trans (Sheaf.sectionsFunctor_map_apply _ e) ?_
  refine Eq.trans ?_ (Sheaf.sectionsFunctor_map_apply
    (transposedSectionEquiv f U (pieceSheaf A i ⨯ pieceSheaf A j) z ≫ mulSheafHom A i j)
    e).symm
  refine Eq.trans (congrArg (fun k => k.hom.app V e)
    (pushedSectionEquiv_eq_transposedSectionEquiv f (A.piece (i + j)) U _).symm) ?_
  refine Eq.trans (transposedMultiplicationAt_apply f A i j U _ _ V e) ?_
  have key : ∀ (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      {B : Sheaf X.J (Type w)} (p : B ⟶ Stacks.underlyingModuleSheaf X.J M)
      (z : (f.toToposHom.pushforward.obj B).obj.obj U),
      (pushedSectionEquiv f M U ((f.toToposHom.pushforward.map p).hom.app U z)).hom.app V e =
        p.hom.app V ((transposedSectionEquiv f U B z).hom.app V e) := fun M B p z =>
    (congrArg (fun k => k.hom.app V e)
      ((pushedSectionEquiv_eq_transposedSectionEquiv f M U _).trans
        (transposedSectionEquiv_comp f U p z))).trans
      (sheafHom_comp_app_apply X.J (transposedSectionEquiv f U B z) p V e)
  have hi := key (A.piece i) Limits.prod.fst z
  have hj := key (A.piece j) Limits.prod.snd z
  refine Eq.trans (congrArg₂ (fun a b => (A.mul i j).app V a b) hi hj) ?_
  refine Eq.trans (mulSheafHom_app A i j V _).symm ?_
  exact (sheafHom_comp_app_apply X.J (transposedSectionEquiv f U _ z)
    (mulSheafHom A i j) V e).symm

/-- **The counit of the adjunction of topoi is multiplicative** for the inverse image of the
direct image of a sheaf of graded algebras: the inverse image of the multiplication of the
direct image, followed by the counit, is the product of the counits followed by the
multiplication.

This is `Stacks.Sheaves.RingedToposModules.homEquiv_binary_iff` for the adjunction of topoi: the
adjunct of a counit component is the identity, so the transposed condition is trivial, and the
only input is `prodComparison_comp_mulSheafHom`. -/
public theorem inverseImage_mulSheafHom_comp_counit
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) :
    f.toToposHom.inverseImage.map (mulSheafHom (pushforwardGradedAlgebra f A) i j) ≫
        f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece (i + j))) =
      Limits.prod.lift
          (f.toToposHom.inverseImage.map (Limits.prod.fst :
              f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece i)) ⨯
                f.toToposHom.pushforward.obj
                  (Stacks.underlyingModuleSheaf X.J (A.piece j)) ⟶ _) ≫
            f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece i)))
          (f.toToposHom.inverseImage.map (Limits.prod.snd :
              f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece i)) ⨯
                f.toToposHom.pushforward.obj
                  (Stacks.underlyingModuleSheaf X.J (A.piece j)) ⟶ _) ≫
            f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece j))) ≫
        mulSheafHom A i j := by
  have hbridge : Limits.prodComparison f.toToposHom.inverseImage
          (f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece i)))
          (f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece j))) ≫
        Limits.prod.map
          (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece i)))
          (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece j))) =
      Limits.prod.lift
        (f.toToposHom.inverseImage.map (Limits.prod.fst :
            f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece i)) ⨯
              f.toToposHom.pushforward.obj
                (Stacks.underlyingModuleSheaf X.J (A.piece j)) ⟶ _) ≫
          f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece i)))
        (f.toToposHom.inverseImage.map (Limits.prod.snd :
            f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece i)) ⨯
              f.toToposHom.pushforward.obj
                (Stacks.underlyingModuleSheaf X.J (A.piece j)) ⟶ _) ≫
          f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece j))) := by
    refine Limits.prod.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.prod.map_fst, ← Category.assoc, Limits.prodComparison_fst,
        Limits.prod.lift_fst]
    · rw [Category.assoc, Limits.prod.map_snd, ← Category.assoc, Limits.prodComparison_snd,
        Limits.prod.lift_snd]
  refine Eq.trans ?_ (Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun k => k ≫ mulSheafHom A i j) hbridge))
  refine (homEquiv_binary_iff f.toToposHom.adj
    (B := Stacks.underlyingModuleSheaf X.J (A.piece (i + j)))
    (B₁ := Stacks.underlyingModuleSheaf X.J (A.piece i))
    (B₂ := Stacks.underlyingModuleSheaf X.J (A.piece j))
    (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece (i + j))))
    (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece i)))
    (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece j)))
    (mulSheafHom (pushforwardGradedAlgebra f A) i j) (mulSheafHom A i j)
    (mulSheafHom (pushforwardGradedAlgebra f A) i j)
    (prodComparison_comp_mulSheafHom f A i j)).mpr ?_
  rw [homEquiv_counit_app, homEquiv_counit_app, homEquiv_counit_app]
  exact (Category.comp_id (mulSheafHom (pushforwardGradedAlgebra f A) i j)).trans
    ((Category.id_comp (mulSheafHom (pushforwardGradedAlgebra f A) i j)).symm.trans
      (congrArg (fun k => k ≫ mulSheafHom (pushforwardGradedAlgebra f A) i j)
        Limits.prod.map_id_id.symm))


/-- **The counit of the adjunction of topoi is multiplicative on local sections** of the inverse
image of the direct image of a sheaf of graded algebras. This is
`inverseImage_mulSheafHom_comp_counit` read through the sections functor: the multiplication of
an inverse image is the inverse image of the multiplication, read on a pair of sections. -/
public theorem counit_mul_inverseImageSections
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) (U : X.Cᵒᵖ)
    (x : ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (pushforwardGradedAlgebra f A)).piece i).val.obj U)
    (y : ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (pushforwardGradedAlgebra f A)).piece j).val.obj U) :
    (f.toToposHom.adj.counit.app
          (Stacks.underlyingModuleSheaf X.J (A.piece (i + j)))).hom.app U
        (((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (pushforwardGradedAlgebra f A)).mul i j).app U x y) =
      (A.mul i j).app U
        ((f.toToposHom.adj.counit.app
          (Stacks.underlyingModuleSheaf X.J (A.piece i))).hom.app U x)
        ((f.toToposHom.adj.counit.app
          (Stacks.underlyingModuleSheaf X.J (A.piece j))).hom.app U y) := by
  have happ := congrArg
    (fun k => (Sheaf.sectionsFunctor X.J U).map k
      (CategoryTheory.Functor.prodObjMk
        (P := transportSections X.J f.toToposHom.inverseImage U) x y))
    (inverseImage_mulSheafHom_comp_counit f A i j)
  refine Eq.trans ?_ (Eq.trans happ ?_)
  · exact (((Sheaf.sectionsFunctor X.J U).map_comp_apply _ _ _).trans
      (Sheaf.sectionsFunctor_map_apply _ _)).symm
  · have key : ∀ {B : Sheaf X.J (Type w)}
        (k : f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece i)) ⨯
          f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J (A.piece j)) ⟶
            f.toToposHom.pushforward.obj B)
        (t : (f.toToposHom.inverseImage.obj (f.toToposHom.pushforward.obj B)).obj.obj U),
        (Sheaf.sectionsFunctor X.J U).map (f.toToposHom.inverseImage.map k)
          (CategoryTheory.Functor.prodObjMk
            (P := transportSections X.J f.toToposHom.inverseImage U) x y) = t →
        (Sheaf.sectionsFunctor X.J U).map
          (f.toToposHom.inverseImage.map k ≫ f.toToposHom.adj.counit.app B)
          (CategoryTheory.Functor.prodObjMk
            (P := transportSections X.J f.toToposHom.inverseImage U) x y) =
        (f.toToposHom.adj.counit.app B).hom.app U t := fun k t h =>
      ((Sheaf.sectionsFunctor X.J U).map_comp_apply _ _ _).trans
        ((Sheaf.sectionsFunctor_map_apply _ _).trans (congrArg _ h))
    have hx := key _ _ (CategoryTheory.Functor.map_fst_prodObjMk
      (P := transportSections X.J f.toToposHom.inverseImage U) x y)
    have hy := key _ _ (CategoryTheory.Functor.map_snd_prodObjMk
      (P := transportSections X.J f.toToposHom.inverseImage U) x y)
    refine Eq.trans ((Sheaf.sectionsFunctor X.J U).map_comp_apply _ _ _) ?_
    refine Eq.trans ?_ (sections_mulSheafHom A i j U
      ((f.toToposHom.adj.counit.app
        (Stacks.underlyingModuleSheaf X.J (A.piece i))).hom.app U x)
      ((f.toToposHom.adj.counit.app
        (Stacks.underlyingModuleSheaf X.J (A.piece j))).hom.app U y))
    refine congrArg ((Sheaf.sectionsFunctor X.J U).map (mulSheafHom A i j)) ?_
    refine Eq.trans (CategoryTheory.Functor.map_lift_apply _ _ _) ?_
    exact congrArg₂ (fun a b => CategoryTheory.Functor.prodObjMk
      (P := Sheaf.sectionsFunctor X.J U)
      (A := Stacks.underlyingModuleSheaf X.J (A.piece i))
      (B := Stacks.underlyingModuleSheaf X.J (A.piece j)) a b) hx hy


/-! ### The counit as a homomorphism of sheaves of graded algebras -/

omit [EssentiallySmall.{w} Y.C] in
/-- **The counit on the image of the change-of-rings unit is the counit of the adjunction of
topoi**, read on local sections. -/
public theorem counit_scalarUnit_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : X.Cᵒᵖ)
    (z : ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      (f.pushforwardModules.obj N)).val.obj V) :
    (f.pullbackAdjPushforwardModulesViaComparison.counit.app N).val.app V
        ((pullbackScalarUnit f (f.pushforwardModules.obj N)).hom.app V z) =
      (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J N)).hom.app V z :=
  (sheafHom_comp_app_apply X.J
        (pullbackScalarUnit f (f.pushforwardModules.obj N))
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (f.pullbackAdjPushforwardModulesViaComparison.counit.app N)) V z).symm.trans
    (congrArg (fun k => k.hom.app V z) (pullbackScalarUnit_comp_counit f N))

/-- **The counit preserves products of the images of the change-of-rings unit.** Extension of
scalars multiplies pure tensors componentwise, and on pure tensors the counit of the pullback
adjunction is the counit of the adjunction of topoi, which is multiplicative. -/
public theorem counit_mul_scalarUnit
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) (V : X.Cᵒᵖ)
    (a : ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (pushforwardGradedAlgebra f A)).piece i).val.obj V)
    (b : ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (pushforwardGradedAlgebra f A)).piece j).val.obj V) :
    (f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece (i + j))).val.app V
        (((toposPullbackGradedAlgebra f.toRingedToposModulesHom
            (pushforwardGradedAlgebra f A)).mul i j).app V
          ((pullbackScalarUnit f (f.pushforwardModules.obj (A.piece i))).hom.app V a)
          ((pullbackScalarUnit f (f.pushforwardModules.obj (A.piece j))).hom.app V b)) =
      (A.mul i j).app V
        ((f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece i)).val.app V
          ((pullbackScalarUnit f (f.pushforwardModules.obj (A.piece i))).hom.app V a))
        ((f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece j)).val.app V
          ((pullbackScalarUnit f (f.pushforwardModules.obj (A.piece j))).hom.app V b)) := by
  refine Eq.trans (congrArg
    (fun t =>
      (f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece (i + j))).val.app V t)
    (pullbackScalarUnit_mul f (pushforwardGradedAlgebra f A) i j V a b).symm) ?_
  refine Eq.trans (counit_scalarUnit_app f (A.piece (i + j)) V _) ?_
  refine Eq.trans (counit_mul_inverseImageSections f A i j V a b) ?_
  exact congrArg₂ (fun s t => (A.mul i j).app V s t)
    (counit_scalarUnit_app f (A.piece i) V a).symm
    (counit_scalarUnit_app f (A.piece j) V b).symm

/-- **The counit of the Stacks 03D7 adjunction as a homomorphism of sheaves of graded
algebras.** Its degreewise components are the degreewise counits, and they preserve products of
homogeneous local sections: both sides of multiplicativity are bilinear maps of two extensions
of scalars, so it is enough to check them on the images of the change-of-rings unit, which is
`counit_mul_scalarUnit`. -/
public noncomputable def counitApp
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (pullFunctor f).obj ((pushFunctor f).obj A) ⟶ A where
  app n := f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece n)
  map_mul i j U x y :=
    scalarExtension_bilinear_ext f
      ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (pushforwardGradedAlgebra f A)).piece i)
      ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (pushforwardGradedAlgebra f A)).piece j)
      (A.piece (i + j))
      (bilinearPostcomp
        (M := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (pushforwardGradedAlgebra f A)).piece i)).val)
        (N := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (pushforwardGradedAlgebra f A)).piece j)).val)
        (P := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (pushforwardGradedAlgebra f A)).piece (i + j))).val)
        (Q := (A.piece (i + j)).val)
        (((pullFunctor f).obj ((pushFunctor f).obj A)).mul i j)
        (f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece (i + j))).val)
      (Stacks.BilinearMap.compRight
        (Stacks.BilinearMap.compLeft
          (M := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (pushforwardGradedAlgebra f A)).piece i)).val)
          (A.mul i j) (f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece i)).val)
        (N := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (pushforwardGradedAlgebra f A)).piece j)).val)
        (f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece j)).val)
      (counit_mul_scalarUnit f A i j) U x y

/-! ### The adjunction -/

/-- **Part (3) of Stacks 0FQX**: pullback of sheaves of graded algebras along a morphism of
ringed topoi is left adjoint to the direct image, and the right adjoint has the direct-image
graded algebras as its values on objects.

The unit and the counit are `unitApp` and `counitApp`, whose degreewise components are those of
the Stacks 03D7 adjunction for sheaves of modules; everything else is
`adjunctionOfGradedUnitCounit`. -/
@[stacks 0FQX "part (3): adjunction for graded algebras"]
public noncomputable def gradedAlgebraPullbackPushforwardAdjunction :
    Σ G : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      { _adj : (gradedAlgebraPullbackSpecification f.toRingedToposModulesHom).1 ⊣ G //
        ∀ A, G.obj A = pushforwardGradedAlgebra f A } :=
  adjunctionOfGradedUnitCounit f (unitApp f)
    (counitApp f) (fun _ _ => rfl) (fun _ _ => rfl)


end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
