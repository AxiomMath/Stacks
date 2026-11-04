module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealTorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
import StacksCore.Tactic.StacksAttribute

/-!
# Extensions of modules across a first order thickening of ringed spaces (Stacks 08L4)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces, with ideal
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`. An *extension of an `𝒪_X`-module `ℱ` by an `𝒪_X`-module `𝒦`
across `i`* is a short exact sequence of `𝒪_{X'}`-modules

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0.

Multiplication by a section of `ℐ` carries `ℱ'` into `i_* 𝒦`, because `ℐ` annihilates `i_* ℱ`,
and the result depends only on the image of the section of `ℱ'` in `i_* ℱ`, because `ℐ`
annihilates `i_* 𝒦` as well. The resulting map is the *canonical map* of the extension,

    c_{ℱ'} : ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦,

characterised by `c_{ℱ'}(a ⊗ s) = a · s'` for any local lift `s'` of `s` to `ℱ'`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.idealSheafι`: the inclusion of the ideal of the
  thickening into `𝒪_{X'}`, and
  `AlgebraicGeometry.RingedSpaceThickening.idealSheafPullback`: the ideal read as an
  `𝒪_X`-module, by pullback along `i`.
* `AlgebraicGeometry.RingedSpaceThickening.idealAction`: the action `ℐ ⊗_{𝒪_{X'}} 𝒩 ⟶ 𝒩` of
  the ideal on an `𝒪_{X'}`-module.
* `AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison`: the comparison
  `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(i^* ℐ ⊗_{𝒪_X} ℱ)` between the tensor product on the thickening
  and the pushforward of the tensor product downstairs, and
  `AlgebraicGeometry.RingedSpaceThickening.extensionTensorIso`: the isomorphism it is the
  adjoint transpose of.
* `AlgebraicGeometry.RingedSpaceThickening.ambientExtensionAction`: the ideal action on the
  middle term of an extension, descended to a map `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_* 𝒦` on `X'`.
* `AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction`: **Stacks 08L4**, the
  canonical map `c_{ℱ'}` of an extension, bundled with the local lifting formula that
  characterises it.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.idealAction_app_tmul`: the ideal action on the image
  of a pure tensor of local sections is multiplication by the section of the ideal.
* `AlgebraicGeometry.RingedSpaceThickening.idealAction_naturality`: the ideal action is natural
  in the module.
* `AlgebraicGeometry.RingedSpaceThickening.idealAction_eq_zero_of_essImage`: the ideal acts as
  zero on a module in the essential image of `i_*`, in particular on a pushforward `i_* ℱ`.
  This is what makes the canonical map well defined.
* `AlgebraicGeometry.RingedSpaceThickening.isIso_counit_app`: for a thickening the counit of
  `i^* ⊣ i_*` is invertible, and
  `AlgebraicGeometry.RingedSpaceThickening.isIso_tensorSheafMap_id_left`: tensoring an
  isomorphism with the identity gives an isomorphism. Together they make
  `extensionTensorIso` an isomorphism.
* `AlgebraicGeometry.RingedSpaceThickening.tensorSheafMap_comp_right`: bifunctoriality of the
  tensor product in the second factor, and
  `AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison_cancel`: two maps out of
  `i^* ℐ ⊗_{𝒪_X} ℱ` agreeing after the comparison are equal, since the comparison is the
  adjoint transpose of an isomorphism.
* `AlgebraicGeometry.RingedSpaceThickening.tensorSheaf_hom_ext`: two maps out of a tensor
  product of sheaves of modules agreeing on the images of pure tensors of local sections are
  equal, and
  `AlgebraicGeometry.RingedSpaceThickening.homEquiv_symm_extensionTensorComparison`: the
  adjoint transpose of `extensionTensorComparison`, by construction.

## Implementation notes

The homeomorphic underlying spaces of `X` and `X'` are not identified. An `𝒪_X`-module is
instead transported to `X'` by `i_*`, and the `𝒪_X`-module structure on the ideal is its
pullback `i^* ℐ`. Accordingly the canonical map is produced on `X'`, as a map out of the
ambient tensor product `ℐ ⊗_{𝒪_{X'}} i_* ℱ`, and then transported downstairs: the comparison
`extensionTensorComparison` is the adjoint transpose of the Tag 01CD isomorphism followed by
the counit of `i^* ⊣ i_*`, and the local lifting formula is stated after that comparison, on
every open set on which a lift exists, as is appropriate for an epimorphism of sheaves.

The construction of the canonical map is: the ideal action on `ℱ'` composed with `ℱ' ⟶ i_* ℱ`
is zero, since `ℐ` annihilates `i_* ℱ`, so it factors through the kernel `i_* 𝒦`; the factor
`ℐ ⊗ ℱ' ⟶ i_* 𝒦` kills the image of `ℐ ⊗ i_* 𝒦`, since `ℐ` annihilates `i_* 𝒦`, so it
descends along `ℐ ⊗ ℱ' ⟶ ℐ ⊗ i_* ℱ`, which is a cokernel by the right exactness of the tensor
product (Tag 01CC, transported across the braiding); and full faithfulness of `i_*` for a
thickening (Tag 08KS) moves the descended map downstairs. Only `IsThickening` is used — the
square-zero condition of `IsFirstOrderThickening` is not needed for the construction — but the
hypothesis is stated as in the source.

The modules on `X'` are taken over `Stacks.SheafOfModules.TensorStalkRingedSpace`'s spelling
of the structure sheaf wherever a tensor product appears, since that is the spelling its tensor
product and the Tag 01CC results are stated over; it is definitionally
`structureSheafRing`, so no transport is involved.

## References

* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction MonoidalCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorPresentations (tensorSheafSwap tensorSheafSwap_naturality
  tensorSheafMap_epi_of_epi_of_epi)

attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

add_to_stacks 08L4 "the short exact sequence" CategoryTheory.Abelian.YonedaExtension

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The inclusion of the ideal of a thickening `i : X ⟶ X'` into `𝒪_{X'}`: the kernel
inclusion of `𝒪_{X'} ⟶ i_* 𝒪_X`. -/
noncomputable abbrev idealSheafι :
    AlgebraicGeometry.SheafOfModules.idealSheaf i ⟶ SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩) :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))

/-- The ideal of a thickening `i : X ⟶ X'`, read as an `𝒪_X`-module by pulling back along
`i`. -/
noncomputable abbrev idealSheafPullback : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩) :=
  (modulePullback i).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i)

/-- The action `ℐ ⊗_{𝒪_{X'}} 𝒩 ⟶ 𝒩` of the ideal of a thickening on an `𝒪_{X'}`-module: the
multiplication map of the ideal, `a ⊗ n ↦ a · n`. -/
noncomputable abbrev idealAction
    (N : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (N)) ⟶ N :=
  Stacks.IdealTorsion.idealTensorMultiplication X' (idealSheafι i) N

/-- The ideal action on the image of a pure tensor of local sections is multiplication by the
corresponding section of `𝒪_{X'}`. -/
theorem idealAction_app_tmul
    (N : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)) (U : Opens X')
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op U)) (n : N.val.obj (op U)) :
    ((idealAction i N).val.app (op U)).hom
        (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N (op U)
          (a ⊗ₜ[X'.presheaf.obj (op U)] n)) =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩).obj.obj
          (op U) : Type u) from
        ((idealSheafι i).val.app (op U)).hom a) • n := by
  classical
  let _mon : MonoidalCategory (PresheafOfModules.{u} (O X')) :=
    PresheafOfModules.monoidalCategory
  unfold idealAction Stacks.IdealTorsion.idealTensorMultiplication
  set adj := PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        ⟨X'.presheaf, X'.IsSheaf⟩).obj) with hadj
  set r : ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩).obj.obj
      (op U) : Type u) :=
    ((idealSheafι i).val.app (op U)).hom a with hr
  -- The presheaf left unitor is the identification `r ⊗ n = r • n`.
  have hunitor : ((λ_ N.val).hom.app (op U)).hom
      ((show (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)).val.obj
          (op U) from r) ⊗ₜ[
        X'.presheaf.obj (op U)] n) = r • n := rfl
  -- The counit of sheafification undoes its unit on a sheaf.
  have hcounit : ∀ y : N.val.obj (op U),
      ((adj.counit.app N).val.app (op U)).hom
        ((adj.unit.app N.val).app (op U) y) = y := fun y =>
    congrArg (fun α : N.val ⟶ _ => (PresheafOfModules.Hom.app α (op U)).hom y)
      (adj.right_triangle_components N)
  -- The unit of sheafification is natural.
  have hnat : ∀ t : ((PresheafOfModules.tensorObj (O := (X').presheaf)
      ((SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)).val)
      (N.val))).obj (op U),
      (((sheafifyFunctor X').map (λ_ N.val).hom).val.app (op U)).hom
          ((adj.unit.app ((PresheafOfModules.tensorObj (O := (X').presheaf)
              ((SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)).val)
              (N.val)))).app (op U) t) =
        (adj.unit.app N.val).app (op U) (((λ_ N.val).hom.app (op U)).hom t) := fun t =>
    (congrArg (fun α : _ ⟶ _ => (PresheafOfModules.Hom.app α (op U)).hom t)
      (adj.unit.naturality (λ_ N.val).hom)).symm
  show ((adj.counit.app N).val.app (op U)).hom
      ((((sheafifyFunctor X').map (λ_ N.val).hom).val.app (op U)).hom
        (((((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
            (((idealSheafι i), (𝟙 N)) : (AlgebraicGeometry.SheafOfModules.idealSheaf i, N) ⟶
            (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩),
            N)))).val.app (op U)).hom
          (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N (op U)
            (a ⊗ₜ[X'.presheaf.obj (op U)] n)))) = r • n
  have hmap : ((((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
      (((idealSheafι i), (𝟙 N)) : (AlgebraicGeometry.SheafOfModules.idealSheaf i, N) ⟶
      (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩), N)))).val.app
      (op U)).hom
      (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N (op U)
        (a ⊗ₜ[X'.presheaf.obj (op U)] n)) =
      (adj.unit.app ((PresheafOfModules.tensorObj (O := (X').presheaf)
          ((SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)).val)
          (N.val)))).app (op U)
        (r ⊗ₜ[X'.presheaf.obj (op U)] n) :=
    (tensorSheafMap_app_toTensorSheafSection X'
      (AlgebraicGeometry.SheafOfModules.idealSheaf i) N
      (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)) N
          (idealSheafι i) (𝟙 N) U a n).trans rfl
  rw [hmap]
  exact Eq.trans
    (congrArg (fun z => ((adj.counit.app N).val.app (op U)).hom z)
      ((hnat (r ⊗ₜ[X'.presheaf.obj (op U)] n)).trans
        (congrArg (fun w => (adj.unit.app N.val).app (op U) w) hunitor)))
    (hcounit (r • n))

/-- Two morphisms out of a tensor product of sheaves of modules on a ringed space which agree
on the images of pure tensors of local sections are equal. -/
theorem tensorSheaf_hom_ext {Y : RingedSpace.{u, u}}
    {F G : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)}
    {Q : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)}
        {p q : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj (F)).obj (G)) ⟶ Q}
    (h : ∀ (V : Opens Y) (m : F.val.obj (op V)) (n : G.val.obj (op V)),
      (p.val.app (op V)).hom
          (toTensorSheafSection Y F G (op V) (m ⊗ₜ[Y.presheaf.obj (op V)] n)) =
        (q.val.app (op V)).hom
          (toTensorSheafSection Y F G (op V) (m ⊗ₜ[Y.presheaf.obj (op V)] n))) :
    p = q :=
  PresheafOfModules.tensorSheaf_hom_ext (Osharp := Y.sheaf) fun U => h U.unop

/-- Applying `1 ⊗ f` to a pure tensor of local sections applies `f` to the second factor. -/
private theorem tensorSheafMap_id_app_toTensorSheafSection {Y : RingedSpace.{u, u}}
    (A : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩))
    {C D : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)} (f : C ⟶ D)
    (V : Opens Y) (a : A.val.obj (op V)) (n : C.val.obj (op V)) :
    ((((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), f) : (A, C) ⟶ (A, D))).val.app
        (op V)).hom (toTensorSheafSection Y A C (op V) (a ⊗ₜ[Y.presheaf.obj (op V)] n))) =
      toTensorSheafSection Y A D (op V)
        (a ⊗ₜ[Y.presheaf.obj (op V)] (f.val.app (op V)).hom n) :=
  (tensorSheafMap_app_toTensorSheafSection Y A C A D (𝟙 A) f V a n).trans rfl

/-- Bifunctoriality of the tensor product in the second factor: composing two induced maps
with the identity in the first factor is the induced map of the composite. -/
theorem tensorSheafMap_comp_right {Y : RingedSpace.{u, u}}
    (A : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩))
    {C D E : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)} (f : C ⟶ D)
        (g : D ⟶ E) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), f) : (A, C) ⟶ (A, D))) ≫
        ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), g) : (A, D) ⟶ (A, E))) =
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), (f ≫ g)) : (A, C) ⟶ (A, E))) := by
  refine tensorSheaf_hom_ext fun V a n => ?_
  have h₁ := tensorSheafMap_id_app_toTensorSheafSection A f V a n
  have h₂ := tensorSheafMap_id_app_toTensorSheafSection A g V a ((f.val.app (op V)).hom n)
  have h₃ := tensorSheafMap_id_app_toTensorSheafSection A (f ≫ g) V a n
  exact (congrArg _ h₁).trans (h₂.trans h₃.symm)

/-- The ideal action is natural in the module: acting and then applying `φ` is applying `φ` in
the second tensor factor and then acting. -/
theorem idealAction_naturality
    {N N' : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩)} (φ : N ⟶ N') :
    idealAction i N ≫ φ =
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
          (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), φ) :
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, N) ⟶
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, N'))) ≫
        idealAction i N' := by
  refine tensorSheaf_hom_ext fun V a n => ?_
  have hmap := tensorSheafMap_id_app_toTensorSheafSection
    (AlgebraicGeometry.SheafOfModules.idealSheaf i) φ V a n
  calc (φ.val.app (op V)).hom (((idealAction i N).val.app (op V)).hom
          (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N (op V)
            (a ⊗ₜ[X'.presheaf.obj (op V)] n)))
      = (φ.val.app (op V)).hom
          ((show ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
              ⟨X'.presheaf, X'.IsSheaf⟩).obj.obj (op V) : Type u) from
            ((idealSheafι i).val.app (op V)).hom a) • n) :=
        congrArg (φ.val.app (op V)).hom (idealAction_app_tmul i N V a n)
    _ = (show ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩).obj.obj
        (op V) : Type u) from
          ((idealSheafι i).val.app (op V)).hom a) • (φ.val.app (op V)).hom n :=
        map_smul (φ.val.app (op V)).hom _ n
    _ = ((idealAction i N').val.app (op V)).hom
          (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N' (op V)
            (a ⊗ₜ[X'.presheaf.obj (op V)] (φ.val.app (op V)).hom n)) :=
        (idealAction_app_tmul i N' V a ((φ.val.app (op V)).hom n)).symm
    _ = ((idealAction i N').val.app (op V)).hom
          (((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
              (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), φ) :
              (AlgebraicGeometry.SheafOfModules.idealSheaf i, N) ⟶
              (AlgebraicGeometry.SheafOfModules.idealSheaf i, N')))).val.app
            (op V)).hom
            (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N (op V)
              (a ⊗ₜ[X'.presheaf.obj (op V)] n))) :=
        congrArg ((idealAction i N').val.app (op V)).hom hmap.symm

/-- The ideal of a thickening acts as zero on a module in the essential image of `i_*`: by
**Stacks 08KS** such a module is annihilated by the kernel ideal. -/
theorem idealAction_eq_zero_of_essImage (hi : IsThickening i)
    (N : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩))
    (hN : (modulePushforward i).essImage N) :
    idealAction i N = 0 := by
  have hann := (closedQuotientOfIsThickening i hi).modulePushforward_essImage_iff N |>.1 hN
  refine tensorSheaf_hom_ext fun V a n => ?_
  show ((idealAction i N).val.app (op V)).hom
    (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) N (op V)
      (a ⊗ₜ[X'.presheaf.obj (op V)] n)) = 0
  refine (idealAction_app_tmul i N V a n).trans ?_
  have hmem := ClosedQuotientMorphismOfRingedSpaces.mem_kernelIdeal_iff_mem_ker_structureSheafHom
    (S := closedQuotientOfIsThickening i hi) (U := op V)
    (a := ((idealSheafι i).val.app (op V)).hom a)
  exact hann V _ (hmem.1 (RingHom.mem_ker.mpr (congrArg
    (fun k : AlgebraicGeometry.SheafOfModules.idealSheaf i ⟶
        (modulePushforward i).obj
            (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)) =>
      (k.val.app (op V)).hom a)
    (kernel.condition
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)))))) n

/-- Tensoring an isomorphism of sheaves of modules on a ringed space with the identity in the
first factor gives an isomorphism. -/
theorem isIso_tensorSheafMap_id_left {Y : RingedSpace.{u, u}}
    (A : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩))
    {B C : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)} (f : B ⟶ C)
        (hf : IsIso f) :
    IsIso (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), f) : (A, B) ⟶ (A, C)))) :=
  (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).mapIso
    (Iso.prod (Iso.refl A) (@asIso _ _ _ _ f hf))).isIso_hom

/-- For a thickening the counit of `i^* ⊣ i_*` is invertible, because `i_*` is fully faithful
(**Stacks 08KS**). -/
theorem isIso_counit_app (hi : IsThickening i)
    (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)) :
    IsIso ((modulePullbackPushforwardAdjunction i).counit.app F) := by
  have counitIsIso := @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _
    (modulePullbackPushforwardAdjunction i)
    (closedQuotientOfIsThickening i hi).full_modulePushforward
    (closedQuotientOfIsThickening i hi).faithful_modulePushforward
  exact ((@asIso _ _ _ _ (modulePullbackPushforwardAdjunction i).counit counitIsIso).app
      F).isIso_hom

section ComparisonFamily

/- The four declarations below state the Tag 01CD comparison, whose type
`Stacks.RingedSpace.comparisonBifunctorIso` gives as a composite of bifunctors, against the
spelling of the tensor product used in the rest of this file. Reconciling the two is one
`isDefEq`, but `Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}` is a definition over
the reducible `Stacks.SheafOfModules.Tensor.ringSheaf`, so each traversal re-unfolds that
abbreviation and re-reduces the structure projection underneath it, and the reconciliation does
not terminate within the heartbeat budget. Making the bifunctor opaque for these four
declarations — and only these four, since the section computations elsewhere in the file need
it transparent — lets the two spellings be matched syntactically. Nothing about the terms
produced changes. -/
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor

/-- The canonical comparison `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(i^* ℐ ⊗_{𝒪_X} ℱ)` from the tensor
product on the thickened space to the pushforward of the tensor product on the original space:
the adjoint transpose of the **Stacks 01CD** isomorphism `i^*(A ⊗ B) ≅ i^* A ⊗ i^* B` followed
by the counit of `i^* ⊣ i_*` in the second factor. -/
noncomputable def extensionTensorComparison
    (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (((modulePushforward i).obj F))) ⟶
      (modulePushforward i).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F))) :=
  (modulePullbackPushforwardAdjunction i).homEquiv _ _
    ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F) ≫
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app F)) :
          (idealSheafPullback i, (modulePushforward i ⋙ modulePullback i).obj F) ⟶
          (idealSheafPullback i, F))))

/-- The adjoint transpose of `extensionTensorComparison` is, by construction, the Tag 01CD
isomorphism followed by the counit of `i^* ⊣ i_*` in the second tensor factor. -/
theorem homEquiv_symm_extensionTensorComparison
    (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)) :
    ((modulePullbackPushforwardAdjunction i).homEquiv
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj
              ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj
              (((modulePushforward i).obj F))))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)))).symm
        (extensionTensorComparison i F) =
      (Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F) ≫
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
            (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app F)) :
            (idealSheafPullback i, (modulePushforward i ⋙ modulePullback i).obj F) ⟶
            (idealSheafPullback i, F))) :=
  Equiv.symm_apply_apply _ _

/-- The comparison underlying `extensionTensorComparison`, before transposition, is an
isomorphism `i^*(ℐ ⊗_{𝒪_{X'}} i_* ℱ) ≅ i^* ℐ ⊗_{𝒪_X} ℱ`: the **Stacks 01CD** isomorphism
followed by the counit of `i^* ⊣ i_*`, which is invertible for a thickening. -/
noncomputable def extensionTensorIso (hi : IsThickening i)
    (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)) :
    (modulePullback i).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (((modulePushforward i).obj F)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) :=
  (Stacks.RingedSpace.comparisonBifunctorIso i).app
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F) ≪≫
    @asIso _ _ _ _ (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
        (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app F)) :
        (idealSheafPullback i, (modulePushforward i ⋙ modulePullback i).obj F) ⟶
        (idealSheafPullback i, F))))
      (isIso_tensorSheafMap_id_left (idealSheafPullback i)
        ((modulePullbackPushforwardAdjunction i).counit.app F) (isIso_counit_app i hi F))

/-- Two maps out of `i^* ℐ ⊗_{𝒪_X} ℱ` which agree after `extensionTensorComparison` are equal:
the comparison is the adjoint transpose of the isomorphism `extensionTensorIso`. This is what
makes an identity between canonical maps of extensions checkable on the thickened space. -/
theorem extensionTensorComparison_cancel (hi : IsThickening i)
    {F K : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩)}
    (c d : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (h : extensionTensorComparison i F ≫ (modulePushforward i).map c =
      extensionTensorComparison i F ≫ (modulePushforward i).map d) :
    c = d := by
  have hc : ((modulePullbackPushforwardAdjunction i).homEquiv _ _)
      ((extensionTensorIso i hi F).hom ≫ c) =
      ((modulePullbackPushforwardAdjunction i).homEquiv _ _)
        ((extensionTensorIso i hi F).hom ≫ d) :=
    ((modulePullbackPushforwardAdjunction i).homEquiv_naturality_right
        (extensionTensorIso i hi F).hom c).trans
      (h.trans (((modulePullbackPushforwardAdjunction i).homEquiv_naturality_right
        (extensionTensorIso i hi F).hom d).symm))
  exact ((extensionTensorIso i hi F).cancel_iso_hom_left c d).1
    (((modulePullbackPushforwardAdjunction i).homEquiv _ _).injective hc)

end ComparisonFamily

/-- The ideal action on the middle term `ℱ'` of an extension
`0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0`, descended to a map `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_* 𝒦` on the ambient
space `X'`.

It exists because the action kills `i_* 𝒦` and lands in `i_* 𝒦`, both of which hold because
`ℐ` annihilates a pushforward (**Stacks 08KS**), and because tensoring the extension by `ℐ`
leaves `ℐ ⊗ ℱ' ⟶ ℐ ⊗ i_* ℱ` a cokernel (**Stacks 01CC**). The bundled equation says that the
descended map recovers the action after composing with those two maps. -/
noncomputable def ambientExtensionAction
    (F K : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩))
        (hi : IsThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0) :
    { dbar : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (((modulePushforward i).obj F))) ⟶
        (modulePushforward i).obj K //
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
          (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F))) ≫ dbar ≫
          E.f =
        idealAction i E.Z.left } := by
  classical
  let I : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩) :=
    AlgebraicGeometry.SheafOfModules.idealSheaf i
  let Ebase : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩) :=
      (modulePushforward i).obj K
  let Eleft : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩) := E.Z.left
  let Eright : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X'.presheaf, X'.IsSheaf⟩) :=
      (modulePushforward i).obj F
  let ef : Ebase ⟶ Eleft := E.f
  let eg : Eleft ⟶ Eright := E.g
  haveI : Mono ef := E.mono_f
  haveI : Epi eg := E.epi_g
  have hzero : ef ≫ eg = 0 := E.exact_g.toIsComplex.zero 0
  let seq : ShortComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      ⟨X'.presheaf, X'.IsSheaf⟩)) :=
    ShortComplex.mk ef eg hzero
  have hSeq : seq.Exact := (ShortComplex.exact_iff_exact_toComposableArrows _).2 E.exact_g
  -- The ideal acts as zero on the two outer terms, which are pushforwards.
  have hActRight :=
    idealAction_eq_zero_of_essImage i hi Eright
      (Functor.obj_mem_essImage (modulePushforward i) F)
  have hActBase :=
    idealAction_eq_zero_of_essImage i hi Ebase
      (Functor.obj_mem_essImage (modulePushforward i) K)
  -- Hence the action on the middle term factors through the kernel `i_* 𝒦`.
  have hActG := (idealAction_naturality i eg).trans
    ((congrArg (fun morphism =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X'.presheaf, X'.IsSheaf⟩)).map
          ((𝟙 I, eg) : (I, Eleft) ⟶ (I, Eright)) ≫ morphism) hActRight).trans comp_zero)
  let hFork : IsLimit (KernelFork.ofι ef hzero) :=
    Classical.choice (seq.exact_and_mono_f_iff_f_is_kernel.mp ⟨hSeq, inferInstance⟩)
  let d := hFork.lift (KernelFork.ofι (idealAction i Eleft) hActG)
  have hd : d ≫ ef = idealAction i Eleft :=
    hFork.fac (KernelFork.ofι (idealAction i Eleft) hActG) WalkingParallelPair.zero
  -- `d` kills the image of `ℐ ⊗ i_* 𝒦`, on which the action is zero.
  have hLeftD : ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 I), ef) : (I, Ebase) ⟶ (I, Eleft))) ≫ d = 0 := by
    refine (cancel_mono ef).1 ?_
    have hassoc : (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 I), ef) : (I, Ebase) ⟶ (I, Eleft))) ≫ d) ≫ ef =
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 I), ef) : (I, Ebase) ⟶ (I, Eleft))) ≫
            idealAction i Eleft := by
      rw [Category.assoc, hd]
    have hnat : idealAction i Ebase ≫ ef =
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 I), ef) : (I, Ebase) ⟶ (I, Eleft))) ≫
            idealAction i Eleft := idealAction_naturality i ef
    rw [hassoc, ← hnat, hActBase]
  let tensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X'.presheaf, X'.IsSheaf⟩
  let leftTensor := tensor.obj I
  letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    ⟨X'.presheaf, X'.IsSheaf⟩ I
  letI : PreservesColimitsOfSize.{u, u} leftTensor :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits
      (Opens.grothendieckTopology X'.carrier) ⟨X'.presheaf, X'.IsSheaf⟩ I
  letI : PreservesFiniteColimits leftTensor :=
    PreservesColimitsOfSize.preservesFiniteColimits leftTensor
  let seqLeft := seq.map leftTensor
  have mappedExact := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    leftTensor).1 inferInstance seq (ShortComplex.ShortExact.mk' hSeq E.mono_f E.epi_g)
  have hSeqLeft : seqLeft.Exact := mappedExact.1
  haveI : Epi seqLeft.g := mappedExact.2
  have firstPair := (congrArg (· ≫ leftTensor.map ef)
    (NatTrans.congr_app (tensor.map_id I) Ebase)).trans (Category.id_comp _)
  have secondPair := (congrArg (· ≫ leftTensor.map eg)
    (NatTrans.congr_app (tensor.map_id I) Eleft)).trans (Category.id_comp _)
  have kernelEquation : seqLeft.f ≫ d = 0 :=
    (congrArg (· ≫ d) firstPair).symm.trans hLeftD
  let hCok : IsColimit (CokernelCofork.ofπ seqLeft.g seqLeft.zero) :=
    Classical.choice (seqLeft.exact_and_epi_g_iff_g_is_cokernel.mp ⟨hSeqLeft, inferInstance⟩)
  let action := hCok.desc (CokernelCofork.ofπ d kernelEquation)
  refine ⟨action, ?_⟩
  exact (congrArg (· ≫ action ≫ ef) secondPair).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ef) (Cofork.IsColimit.π_desc hCok)).trans hd))

/-- **Stacks Project, Tag 08L4.** The canonical map `c_{ℱ'} : i^* ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦` of an
extension `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` of `𝒪_{X'}`-modules across a first order thickening
`i`.

The bundled equation is the local lifting characterisation from the source: on an open set of
`X'` over which a section `s` of `i_* ℱ` lifts to a section `s'` of `ℱ'`, the image in `ℱ'` of
`c_{ℱ'}(a ⊗ s)` is the scalar multiple `a · s'`. -/
@[stacks 08L4 "the canonical map"]
noncomputable def firstOrderExtensionAction
    (F K : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩))
        (hi : IsFirstOrderThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0) :
    { c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K //
      ∀ (U : Opens X') (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op U))
        (s : ((modulePushforward i).obj F).val.obj (op U)) (s' : E.Z.left.val.obj (op U)),
        (E.g.val.app (op U)).hom s' = s →
          (E.f.val.app (op U)).hom
              ((((modulePushforward i).map c).val.app (op U)).hom
                (((extensionTensorComparison i F).val.app (op U)).hom
                  (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i)
                    ((modulePushforward i).obj F) (op U)
                    (a ⊗ₜ[X'.presheaf.obj (op U)] s)))) =
            (show ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
                ⟨X'.presheaf, X'.IsSheaf⟩).obj.obj (op U) : Type u) from
              ((idealSheafι i).val.app (op U)).hom a) • s' } := by
  classical
  obtain ⟨dbar, hdbar⟩ := ambientExtensionAction i F K hi.1 E
  let c : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K :=
    (extensionTensorIso i hi.1 F).inv ≫
      ((modulePullbackPushforwardAdjunction i).homEquiv _ _).symm dbar
  have hComparison : extensionTensorComparison i F ≫ (modulePushforward i).map c = dbar := by
    refine ((modulePullbackPushforwardAdjunction i).homEquiv _ _).symm.injective ?_
    exact (((modulePullbackPushforwardAdjunction i).homEquiv_naturality_right_symm
        (extensionTensorComparison i F) c).trans
      (congrArg (fun z => z ≫ c) (homEquiv_symm_extensionTensorComparison i F))).trans
      (Iso.hom_inv_id_assoc (extensionTensorIso i hi.1 F) _)
  refine ⟨c, ?_⟩
  intro U a s s' hgs
  have hinner : ((((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
      (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F)))).val.app
      (op U)).hom
      (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) E.Z.left (op U)
        (a ⊗ₜ[X'.presheaf.obj (op U)] s')) =
      toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i)
        ((modulePushforward i).obj F) (op U) (a ⊗ₜ[X'.presheaf.obj (op U)] s) :=
    (tensorSheafMap_app_toTensorSheafSection X'
      (AlgebraicGeometry.SheafOfModules.idealSheaf i) E.Z.left
      (AlgebraicGeometry.SheafOfModules.idealSheaf i) ((modulePushforward i).obj F)
      (𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)) E.g U a s').trans
      (congrArg (fun t => toTensorSheafSection X'
        (AlgebraicGeometry.SheafOfModules.idealSheaf i) ((modulePushforward i).obj F) (op U)
        (a ⊗ₜ[X'.presheaf.obj (op U)] t)) hgs)
  have hComposite : ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
      (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F))) ≫
      (extensionTensorComparison i F ≫ (modulePushforward i).map c) ≫ E.f =
      idealAction i E.Z.left :=
    (congrArg (fun z => ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
        (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
        (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
        (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F))) ≫ z ≫ E.f)
        hComparison).trans hdbar
  have hGlob := congrArg
      (fun f : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj
      (E.Z.left)) ⟶ E.Z.left =>
    (f.val.app (op U)).hom
      (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) E.Z.left (op U)
        (a ⊗ₜ[X'.presheaf.obj (op U)] s'))) hComposite
  have hL : ((((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
      (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F))) ≫
        (extensionTensorComparison i F ≫ (modulePushforward i).map c) ≫ E.f).val.app (op U)).hom
      (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) E.Z.left (op U)
        (a ⊗ₜ[X'.presheaf.obj (op U)] s')) =
      (E.f.val.app (op U)).hom
        ((((modulePushforward i).map c).val.app (op U)).hom
          (((extensionTensorComparison i F).val.app (op U)).hom
            (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i)
              ((modulePushforward i).obj F) (op U)
              (a ⊗ₜ[X'.presheaf.obj (op U)] s)))) := by
    rw [← hinner]; rfl
  exact (hL.symm.trans hGlob).trans (idealAction_app_tmul i E.Z.left U a s')

/-- The global form of the local lifting formula characterising the canonical map of an
extension: precomposed with `1 ⊗ (ℱ' ⟶ i_* ℱ)` and postcomposed with `i_* 𝒦 ⟶ ℱ'`, the
comparison followed by `c_{ℱ'}` is the action of the ideal on `ℱ'`.

This says that `extensionTensorComparison i ℱ ≫ i_* c_{ℱ'}` is the map `ambientExtensionAction`
descends the action to, and it is the form in which the canonical map is used away from
sections. -/
theorem firstOrderExtensionAction_comp
    (F K : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} ⟨X.presheaf, X.IsSheaf⟩))
    (hi : IsFirstOrderThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
        (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
        (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
        (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F))) ≫
        (extensionTensorComparison i F ≫
            (modulePushforward i).map (firstOrderExtensionAction i F K hi E).val) ≫ E.f =
      idealAction i E.Z.left := by
  refine tensorSheaf_hom_ext fun U a s' => ?_
  have hinner := tensorSheafMap_id_app_toTensorSheafSection
    (AlgebraicGeometry.SheafOfModules.idealSheaf i) E.g U a s'
  exact (congrArg
      (fun z => (E.f.val.app (op U)).hom
        ((((modulePushforward i).map
            (firstOrderExtensionAction i F K hi E).val).val.app (op U)).hom
          (((extensionTensorComparison i F).val.app (op U)).hom z))) hinner).trans
    (((firstOrderExtensionAction i F K hi E).property U a
        ((E.g.val.app (op U)).hom s') s' rfl).trans
      (idealAction_app_tmul i E.Z.left U a s').symm)

end AlgebraicGeometry.RingedSpaceThickening

end
