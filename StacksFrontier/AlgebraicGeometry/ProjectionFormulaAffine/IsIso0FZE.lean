module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# Restricting the projection-formula map to an open of the base

Let `h : T ⟶ S` be a morphism of schemes, `G` a sheaf of `𝒪_T`-modules, `H` a sheaf of
`𝒪_S`-modules and `V` an open of `S`.  Write `h ∣_ V : h⁻¹(V) ⟶ V` for the restriction of `h`
and `j = V.ι`, `j' = (h ⁻¹ᵁ V).ι` for the two open immersions.

`StacksDraft.AlgebraicGeometry.F4.ProjectionFormulaAffine.Basic` reduces Stacks 0FZE to
invertibility of the restrictions `(Scheme.Modules.restrictFunctor (V i).ι).map
(projectionFormulaMap h G H)` along an open covering of `S`, and records that composing that
reduction with the affine criterion needs a statement identifying such a restriction with the
projection-formula map of `h ∣_ V`.  This file supplies the half of that statement which is
about *objects*: it builds the two canonical identifications

* `restrictedProjectionFormulaSourceIso`:
  `j^*(h_*G ⊗_{𝒪_S} H) ≅ (h ∣_ V)_*(j'^*G) ⊗_{𝒪_V} j^*H`;
* `restrictedProjectionFormulaTargetIso`:
  `j^*(h_*(G ⊗_{𝒪_T} h^*H)) ≅ (h ∣_ V)_*(j'^*G ⊗_{𝒪_{h⁻¹V}} (h ∣_ V)^*(j^*H))`,

and transports `j^*(projectionFormulaMap h G H)` across them.  The transported morphism
`restrictedProjectionFormulaMap` has, *on the nose*, the type of
`projectionFormulaMap (h ∣_ V) (j'^*G) (j^*H)`, and `isIso_restrictedProjectionFormulaMap_iff`
says it is invertible exactly when the restriction of the projection-formula map is.  So Stacks
0FZE for an arbitrary base follows from the affine-base case together with the single equation

`restrictedProjectionFormulaMap h V G H = projectionFormulaMap (h ∣_ V) (j'^*G) (j^*H)`,

which is *not* proved here (see "What is still missing", below).

## Main definitions

* `pullbackTensorIso` is Stacks 01CD in the scheme vocabulary: pulling back a tensor product
  of sheaves of modules is the tensor product of the pullbacks.
* `restrictTensorIso` is the same statement for `Scheme.Modules.restrictFunctor`, i.e.
  restriction to an open subscheme commutes with
    `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`.
* `pullbackSquareIso` is the pullback half of the restriction square,
  `h^* ⋙ j'^* ≅ j^* ⋙ (h ∣_ V)^*`.
* `pushforwardBaseChangeIso` is the pushforward half, `j^* h_* ≅ (h ∣_ V)_* j'^*`, as an
  isomorphism rather than a natural transformation.
* `restrictedProjectionFormulaSourceIso`, `restrictedProjectionFormulaTargetIso` and
  `restrictedProjectionFormulaMap` are as above.

## Main results

* `isIso_restrictFunctor_map_iff_isIso_pullback_map`: restriction to an open subscheme and
  pullback along the corresponding open immersion detect invertibility equally.
* `isIso_restrictedProjectionFormulaMap_iff`: the transported morphism is invertible exactly
  when the restriction of the projection-formula map is.
* `isIso_projectionFormulaMap_iff_forall_affineOpen_restricted`: the projection-formula map is
  invertible exactly when `restrictedProjectionFormulaMap h V G H` is invertible for every
  affine open `V` of `S`.  This is Basic.lean's locality reduction re-expressed on data that
  has the shape of a projection-formula map over `V`; like that reduction it is an
  equivalence, so it does not narrow the assertion of the source.

## Implementation notes

Stacks 01CD is available unconditionally, as `Stacks.RingedSpace.comparisonNatTrans_isIso` and
`Stacks.RingedSpace.comparisonBifunctorIso`; in particular the open-immersion case of 01CD, which
is what restriction to an open subscheme commuting with `tensorSheaf` amounts to, is *not* a
missing ingredient.  Every tensor-restriction isomorphism below is obtained
from it, rather than from `AlgebraicGeometry.tensorRestrictionIso`, which is stated for the
over-site model `SheafOfModules.over U` and
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and carries no
characterisation lemma.

Three spellings of the structure sheaf of a scheme occur — `X.ringCatSheaf`,
`structureSheafRing X.toRingedSpace` and
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`, the last of which is what
`Stacks.RingedSpace.tensorSheaf` is indexed by — and all three are equal by `rfl`.  Terms
therefore cross freely, but *unification* across the difference is expensive: writing
`(Stacks.RingedSpace.tensorSheaf X).obj (F, G)` where a
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X F G` is
expected costs a `whnf` timeout as soon as `F` is a composite of pushforwards and pullbacks.
`tensorSheafIsoMk` therefore states its conclusion at the
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` spelling,
which is the one `projectionFormulaMap` is written in, and does the crossing once, internally,
on bare variables.  For the same reason no `eqToIso` and no `Scheme.Modules.pullbackCongr`
appears: `pullbackSquareIso` is assembled from `pullbackRestrictIso` and
`Scheme.Modules.restrictFunctorIsoPullback` instead of from the equality of the two composites.

### What is still missing for Stacks 0FZE

Two statements, both about *morphisms*.

* The compatibility equation displayed above.  Its two sides have the same type, which is
  checked by `restrictedProjectionFormulaMap` elaborating against that type; what is missing is
  the diagram chase, which has to commute `j^*` past the adjoint transpose defining
  `projectionFormulaMap`.  The template for it is
  `AlgebraicGeometry.RingedSpace.modulePullbackUnitToUnit_ofRestrict`, which runs the same
  manoeuvre -- inject along `(modulePullbackPushforwardAdjunction _).homEquiv` and rewrite the
  transpose -- for the unit of the structure sheaf.
* The tensor half of Stacks 01I8, as recorded in Basic.lean: a natural isomorphism
  `M̃ ⊗_{𝒪_{Spec R}} Ñ ≅ (M ⊗_R N)~`.  This is what the affine-base case itself waits on, and
  it is independent of everything here.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.AlgebraicGeometry.AffineBaseChange Stacks.AlgebraicGeometry.AffinePushforward

universe u

/-! ### Isomorphisms of tensor products of sheaves of modules -/

/-- The tensor product of two isomorphisms of sheaves of modules on a ringed space, as an
isomorphism of the tensor-product sheaves.

The conclusion is stated at the `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`
  spelling, which is the one
`projectionFormulaMap` uses; the crossing to the bifunctor `Stacks.RingedSpace.tensorSheaf`,
over whose index the two spellings of the structure sheaf differ, happens here once on bare
variables rather than at each use site on a composite of pushforwards and pullbacks. -/
def tensorSheafIsoMk {X : RingedSpace.{u, u}}
    {F F' G G' : SheafOfModules.{u} (structureSheafRing X)} (e : F ≅ F') (d : G ≅ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F')).obj
        (G')) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, X.IsSheaf⟩)).mapIso (X := (F, G)) (Y := (F', G')) (e.prod d)

/-- The forward map of `tensorSheafIsoMk` is the tensor product of the two forward maps. -/
@[simp]
lemma tensorSheafIsoMk_hom {X : RingedSpace.{u, u}}
    {F F' G G' : SheafOfModules.{u} (structureSheafRing X)} (e : F ≅ F') (d : G ≅ G') :
    (tensorSheafIsoMk e d).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((e.hom, d.hom) : (_, _) ⟶ (_, _))) := rfl

/-- The inverse map of `tensorSheafIsoMk` is the tensor product of the two inverse maps. -/
@[simp]
lemma tensorSheafIsoMk_inv {X : RingedSpace.{u, u}}
    {F F' G G' : SheafOfModules.{u} (structureSheafRing X)} (e : F ≅ F') (d : G ≅ G') :
    (tensorSheafIsoMk e d).inv =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((e.inv, d.inv) : (_, _) ⟶ (_, _))) := rfl

/-! ### Restriction and pullback detect invertibility equally -/

/-- **Restriction to an open subscheme and pullback along the corresponding open immersion
detect invertibility equally.**  The two functors are naturally isomorphic
(`Scheme.Modules.restrictFunctorIsoPullback`), so this is naturality of that isomorphism.

It is what lets the locality reduction of Basic.lean, which is phrased with
`Scheme.Modules.restrictFunctor`, be fed by statements phrased with
`Scheme.Modules.pullback`, which is the vocabulary Stacks 01CD is available in. -/
lemma isIso_restrictFunctor_map_iff_isIso_pullback_map {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules} (φ : M ⟶ N) :
    IsIso ((Scheme.Modules.restrictFunctor j).map φ) ↔
      IsIso ((Scheme.Modules.pullback j).map φ) :=
  NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j) φ

/-! ### Stacks 01CD in the scheme vocabulary -/

/-- **Stacks 01CD for a morphism of schemes.**  Pulling back a tensor product of sheaves of
modules is the tensor product of the pullbacks.  This is
`Stacks.RingedSpace.comparisonBifunctorIso`, which holds for an arbitrary morphism of ringed
spaces, read at the tensor-product spelling the projection formula uses. -/
def pullbackTensorIso {X Y : Scheme.{u}} (j : X ⟶ Y) (F G : Y.Modules) :
    (Scheme.Modules.pullback j).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pullback j).obj F))).obj (((Scheme.Modules.pullback j).obj G))) :=
  (Stacks.RingedSpace.comparisonBifunctorIso j.toLRSHom.toShHom).app (F, G)

/-- The forward map of `pullbackTensorIso` is the Stacks 01CD comparison morphism, so the
characterisation `Stacks.RingedSpace.comparisonBifunctorIso_hom_homEquiv_unit_tmul` of that
morphism on unit images of pure tensors applies to it. -/
@[simp]
lemma pullbackTensorIso_hom {X Y : Scheme.{u}} (j : X ⟶ Y) (F G : Y.Modules) :
    (pullbackTensorIso j F G).hom =
      (Stacks.RingedSpace.comparisonNatTrans j.toLRSHom.toShHom).app (F, G) := rfl

/-- **Restriction to an open subscheme commutes with the tensor product of sheaves of
modules.**  This is `pullbackTensorIso` conjugated by
`Scheme.Modules.restrictFunctorIsoPullback`.

Unlike `AlgebraicGeometry.tensorRestrictionIso` this is stated for
`Scheme.Modules.restrictFunctor` and `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, so
  it applies directly to the
locality reduction of Basic.lean. -/
def restrictTensorIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (F G : Y.Modules) :
    (Scheme.Modules.restrictFunctor j).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.restrictFunctor j).obj F))).obj
        (((Scheme.Modules.restrictFunctor j).obj G))) :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫ pullbackTensorIso j F G ≪≫
    tensorSheafIsoMk ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm
      ((Scheme.Modules.restrictFunctorIsoPullback j).app G).symm

/-! ### The two halves of the restriction square -/

variable {T S : Scheme.{u}} (h : T ⟶ S) (V : S.Opens)

/-- **The pullback half of the restriction square.**  Pulling back along `h` and then
restricting to `h⁻¹(V)` is restricting to `V` and then pulling back along `h ∣_ V`.

Assembled from `pullbackRestrictIso` and `Scheme.Modules.restrictFunctorIsoPullback`
rather than from `Scheme.Modules.pullbackCongr`, which is an `eqToIso`. -/
def pullbackSquareIso :
    Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ V).ι ≅
      Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (h ∣_ V) :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback (h ⁻¹ᵁ V).ι).symm ≪≫
    pullbackRestrictIso h V ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι) _

/-- **The pushforward half of the restriction square**, as an isomorphism.  Restricting the
pushforward along `h` to `V` is the pushforward along `h ∣_ V` of the restriction to
`h⁻¹(V)`.

This is the base-change morphism of the restriction square, which
`isIso_baseChangeNatTrans_restrictSquare` proves invertible. -/
def pushforwardBaseChangeIso (G : T.Modules) :
    (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward h).obj G) ≅
      (Scheme.Modules.pushforward (h ∣_ V)).obj
        ((Scheme.Modules.pullback (h ⁻¹ᵁ V).ι).obj G) :=
  @asIso _ _ _ _ ((baseChangeNatTrans (restrictSquare h V)).app G)
    (isIso_baseChangeNatTrans_restrictSquare h V G)

/-! ### Restricting the projection-formula map -/

variable (G : T.Modules) (H : S.Modules)

/-- **The source of the projection-formula map restricts to the source of the restricted
one.**  The tensor product of the pushforward of `G` with `H`, restricted to `V`, is the
tensor product of the pushforward along `h ∣_ V` of the restriction of `G` with the
restriction of `H`. -/
def restrictedProjectionFormulaSourceIso :
    (Scheme.Modules.pullback V.ι).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pushforward h).obj G))).obj (H))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((V : Scheme.{u}).toRingedSpace)).presheaf,
          (((V : Scheme.{u}).toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pushforward (h ∣_ V)).obj
          ((Scheme.Modules.pullback (h ⁻¹ᵁ V).ι).obj G)))).obj
        (((Scheme.Modules.pullback V.ι).obj H))) :=
  pullbackTensorIso V.ι _ _ ≪≫ tensorSheafIsoMk (pushforwardBaseChangeIso h V G) (Iso.refl _)

/-- **The target of the projection-formula map restricts to the target of the restricted
one.**  The pushforward of the tensor product of `G` with the inverse image of `H`, restricted
to `V`, is the pushforward along `h ∣_ V` of the tensor product of the restriction of `G` with
the inverse image along `h ∣_ V` of the restriction of `H`.

The three factors are the base change of the pushforward, Stacks 01CD for `(h ⁻¹ᵁ V).ι`, and
the pullback half of the restriction square. -/
def restrictedProjectionFormulaTargetIso :
    (Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pushforward h).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((T.toRingedSpace)).presheaf, ((T.toRingedSpace)).IsSheaf⟩).obj (G)).obj
              (((Scheme.Modules.pullback h).obj H))))) ≅
      (Scheme.Modules.pushforward (h ∣_ V)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((↑(h ⁻¹ᵁ V) :
          Scheme.{u}).toRingedSpace)).presheaf, (((↑(h ⁻¹ᵁ V) :
          Scheme.{u}).toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pullback (h ⁻¹ᵁ V).ι).obj G))).obj
          (((Scheme.Modules.pullback (h ∣_ V)).obj
            ((Scheme.Modules.pullback V.ι).obj H))))) :=
  pushforwardBaseChangeIso h V _ ≪≫
    (Scheme.Modules.pushforward (h ∣_ V)).mapIso
      (pullbackTensorIso (h ⁻¹ᵁ V).ι G _ ≪≫
        tensorSheafIsoMk (Iso.refl _) ((pullbackSquareIso h V).app H))

/-- **The restriction of the projection-formula map, read on the restricted data.**  The
inverse image along `V.ι` of `projectionFormulaMap h G H`, transported along
`restrictedProjectionFormulaSourceIso` and `restrictedProjectionFormulaTargetIso`.

Its type is, on the nose, the type of
`projectionFormulaMap (h ∣_ V) ((Scheme.Modules.pullback (h ⁻¹ᵁ V).ι).obj G)
((Scheme.Modules.pullback V.ι).obj H)`; that the two morphisms are *equal* is the statement
this file does not prove. -/
def restrictedProjectionFormulaMap :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((V : Scheme.{u}).toRingedSpace)).presheaf,
        (((V : Scheme.{u}).toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pushforward (h ∣_ V)).obj
          ((Scheme.Modules.pullback (h ⁻¹ᵁ V).ι).obj G)))).obj
      (((Scheme.Modules.pullback V.ι).obj H))) ⟶
      (Scheme.Modules.pushforward (h ∣_ V)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((↑(h ⁻¹ᵁ V) :
          Scheme.{u}).toRingedSpace)).presheaf, (((↑(h ⁻¹ᵁ V) :
          Scheme.{u}).toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pullback (h ⁻¹ᵁ V).ι).obj G))).obj
          (((Scheme.Modules.pullback (h ∣_ V)).obj
            ((Scheme.Modules.pullback V.ι).obj H))))) :=
  (restrictedProjectionFormulaSourceIso h V G H).inv ≫
    (Scheme.Modules.pullback V.ι).map (projectionFormulaMap h G H) ≫
      (restrictedProjectionFormulaTargetIso h V G H).hom

/-- **The transported morphism detects invertibility of the restriction.**  Since the two
identifications it is transported along are isomorphisms, `restrictedProjectionFormulaMap` is
invertible exactly when the restriction of the projection-formula map to `V` is. -/
lemma isIso_restrictedProjectionFormulaMap_iff :
    IsIso (restrictedProjectionFormulaMap h V G H) ↔
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H)) :=
  ((@isIso_comp_left_iff _ _ _ _ _ (restrictedProjectionFormulaSourceIso h V G H).inv
        ((Scheme.Modules.pullback V.ι).map (projectionFormulaMap h G H) ≫
          (restrictedProjectionFormulaTargetIso h V G H).hom)
        (restrictedProjectionFormulaSourceIso h V G H).isIso_inv).trans
      (@isIso_comp_right_iff _ _ _ _ _
        ((Scheme.Modules.pullback V.ι).map (projectionFormulaMap h G H))
        (restrictedProjectionFormulaTargetIso h V G H).hom
        (restrictedProjectionFormulaTargetIso h V G H).isIso_hom)).trans
    (isIso_restrictFunctor_map_iff_isIso_pullback_map V.ι (projectionFormulaMap h G H)).symm

/-- **Stacks 0FZE is detected on the affine opens of the base, on restricted data.**  The
projection-formula map of `h` is invertible exactly when, for every affine open `V` of `S`, the
restriction of the projection-formula map transported onto the restricted data is invertible.

This is the locality reduction `isIso_projectionFormulaMap_iff_forall_affineOpen` of Basic.lean
composed with `isIso_restrictedProjectionFormulaMap_iff`.  Like that reduction it is an
equivalence -- the hypothesis is also a consequence of the conclusion -- so it does not narrow
the assertion of the source; what it adds is that the data it is stated on lives over `V` and
has the type of a projection-formula map there. -/
theorem isIso_projectionFormulaMap_iff_forall_affineOpen_restricted :
    IsIso (projectionFormulaMap h G H) ↔
      ∀ V : S.affineOpens, IsIso (restrictedProjectionFormulaMap h (V : S.Opens) G H) := by
  rw [isIso_projectionFormulaMap_iff_forall_affineOpen h G H]
  exact ⟨fun hV W ↦ (isIso_restrictedProjectionFormulaMap_iff h _ G H).mpr (hV W),
    fun hV W ↦ (isIso_restrictedProjectionFormulaMap_iff h _ G H).mp (hV W)⟩

end Stacks.ProjectionFormula

end
