module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Deformation.RingedSpaceThickening.IdealMultiple
public import StacksFrontier.Deformation.RingedSpaceThickening.MapLift
public import StacksFrontier.RingTheory.ColimitPresentation.FinitePresentation
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.RingedSpace.StrictThickening
import StacksCore.Tactic.StacksAttribute

/-!
# The flatness criterion across a strict morphism of first-order thickenings (Stacks 08LI, 08LJ)

Let

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

be a morphism of first-order thickenings of ringed spaces (Stacks 08KZ), with ideal sheaves
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)` on `X'` and `𝒥 = ker(𝒪_{S'} ⟶ t_* 𝒪_S)` on `S'`, and suppose the
square is *strict* (Stacks 08L1): the canonical map `(f')^* 𝒥 ⟶ ℐ` is surjective. Let `ℱ'` be an
`𝒪_{X'}`-module whose restriction `ℱ = i^* ℱ'` is flat over `S`. Then `ℱ'` is flat over `S'` if
and only if the canonical map

    f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐℱ'

is an isomorphism, and in that case the two maps it factors through,

    f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ i^* ℐ ⊗_{𝒪_X} ℱ    and    i^* ℐ ⊗_{𝒪_X} ℱ ⟶ ℐℱ',

are isomorphisms as well. The ideal multiple `ℐℱ'` is read on `X` as the pullback along `i` of
`ker(ℱ' ⟶ i_* i^* ℱ')`, which is `ℐℱ'` by
`AlgebraicGeometry.RingedSpaceThickening.idealMultipleIso`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseToSourceIdealTensor`: the first of the two maps,
  obtained by tensoring the reduced canonical ideal map `f^* 𝒥 ⟶ i^* ℐ` of Stacks 08L1 with the
  identity of `ℱ`.
* `AlgebraicGeometry.RingedSpaceThickening.sourceIdealActionImage`: the second of the two maps,
  obtained from the ideal action `ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ'` on `X'` by the Stacks 01CD comparison
  for `i^*` and the identification `ℐℱ' = ker(ℱ' ⟶ i_* i^* ℱ')`.
* `AlgebraicGeometry.RingedSpaceThickening.baseToInfinitesimal`: their composite, the canonical
  map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐℱ'`.
* `AlgebraicGeometry.RingedSpaceThickening.tensorSheafCommIso`: the symmetry
  `ℱ ⊗_{𝒪_Y} 𝒢 ≅ 𝒢 ⊗_{𝒪_Y} ℱ` of the tensor product of sheaves of modules.
* `AlgebraicGeometry.RingedSpaceThickening.restrictionTensorBaseIdeal`: the module
  `𝒢 ⊗_{𝒪_X} f^* 𝒥` under which the lifts of a map transform, and
  `AlgebraicGeometry.RingedSpaceThickening.infinitesimalTensorIso`: its identification with
  `ℐ𝒢'` when `𝒢'` is flat over `S'`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isFlatOver_iff_baseToInfinitesimal_isIso`: the
  criterion itself.
* `AlgebraicGeometry.RingedSpaceThickening.baseToSourceIdealTensor_isIso` and
  `AlgebraicGeometry.RingedSpaceThickening.sourceIdealActionImage_isIso`: the two isomorphisms of
  the final assertion.
* `AlgebraicGeometry.RingedSpaceThickening.mapLift_isTorsor_tensor`: **Stacks 08LJ**, the lifts
  of an `𝒪_X`-linear `φ : ℱ ⟶ 𝒢` to an `𝒪_{X'}`-linear `ℱ' ⟶ 𝒢'` form, when nonempty, a
  principal homogeneous space under `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`: that group acts on them,
  and simply transitively.
* `AlgebraicGeometry.RingedSpaceThickening.mapLift_isPrincipalHomogeneous_tensor`: the simple
  transitivity alone, the second half of the preceding.

## Implementation notes

The proof is local: everything is reduced to the corresponding statement about the stalk of `ℱ'`
at a point, read as a module over the stalk of `𝒪_{S'}` through `(f')^♯`. The two ingredients of
that reduction are

* the stalk of a pullback is a base change (Stacks 0098,
  `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`), so that the stalk of
  `(f')^* 𝒥` is `𝒪_{X',x} ⊗_{𝒪_{S',f'(x)}} 𝒥_{f'(x)}` and the ideal action becomes a base-changed
  multiplication map; and
* the local criterion of flatness in the square-zero case
  (`flat_of_sq_zero_local_criterion`), which turns flatness of `ℱ'_x` over `𝒪_{S',f'(x)}` into
  injectivity of `𝒥_{f'(x)} ⊗ ℱ'_x ⟶ ℱ'_x` once `ℱ_x` is known to be flat over
  `𝒪_{S',f'(x)}/𝒥_{f'(x)}`.

Strictness enters twice: it makes the reduced canonical ideal map epimorphic
(`MorphismOfThickenings.epi_baseToSourceIdeal`), and it identifies the stalk of `ℐ` with the
extension of the stalk of `𝒥` (`strict_stalkIdeal_eq_map`), which is what exhibits
`𝒪_{X',x} ⊗_{𝒪_{S',f'(x)}} (𝒪_{S',f'(x)}/𝒥_{f'(x)})` as `𝒪_{X,x}` and therefore lets the flatness
of `ℱ` over `S` supply the quotient hypothesis of the local criterion.

Two spellings of the sheaf of rings `𝒪_X` are in play, `structureSheafRing`,
in which the adjunction `i^* ⊣ i_*` is stated, and
`structureSheafRing`, in which the tensor product and
the ideal action are; they agree by `rfl`. Likewise the module structure on the stalk of a
sheaf of modules has two names, Mathlib's instance and
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, which is that instance by definition;
`stalkModule_eq_mathlib` records the `rfl`. `AlgebraicGeometry.IsFlatOverAt` is stated with
Mathlib's name, every stalk computation here with the other.

The group `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)` of Tag 08LJ has its tensor factors in the order the
source writes them, which is the opposite of the order the criterion above uses; the symmetry
`tensorSheafCommIso` crosses between the two, and `restrictionTensorBaseIdeal` names the result
in the `structureSheafRing` spelling so that sums of morphisms out of it are found by instance search.
Tag 08LJ is **Stacks 08LH** transported along that identification, so only the first-order
condition on `i` — not on `t` — is needed for it.

## References

* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 08LH](https://stacks.math.columbia.edu/tag/08LH)
* [Stacks Project, Tag 08LJ](https://stacks.math.columbia.edu/tag/08LJ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction MonoidalCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.IdealTorsion (idealTensorMultiplication)
open AlgebraicGeometry.SheafOfModules (stalkAddCommGroupFunctor stalkShortComplex
  exact_iff_stalkShortComplex_exact)
open RingedSpaceModuleAdjunction (modulePullbackUnitToUnit homEquiv_modulePullbackUnitToUnit)
open scoped TensorProduct

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf PresheafOfModules.tensorObj

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Epimorphisms and monomorphisms of sheaves of modules on stalks -/

/-- A morphism of sheaves of modules on a ringed space is a monomorphism exactly when it is
injective on every stalk. -/
private theorem mono_iff_stalk_injective (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X)) (f : F ⟶ G) :
    Mono f ↔ ∀ x : X,
      Function.Injective ((stalkAddCommGroupFunctor (structureSheafRing X) x).map f).hom := by
  let _iab : Abelian (SheafOfModules.{u} (structureSheafRing X)) := SheafOfModules.instAbelian _
  let _inp : NonPreadditiveAbelian (SheafOfModules.{u} (structureSheafRing X)) :=
    Abelian.nonPreadditiveAbelian
  let S : ShortComplex (SheafOfModules.{u} (structureSheafRing X)) :=
    ShortComplex.mk (0 : F ⟶ F) f (by simp)
  rw [← S.exact_iff_mono (by simp [S]), exact_iff_stalkShortComplex_exact]
  have hTf : ∀ x : X, (stalkShortComplex (structureSheafRing X) S x).f = 0 := fun x => by
    change (stalkAddCommGroupFunctor (structureSheafRing X) x).map (0 : F ⟶ F) = 0
    exact Functor.map_zero _ _ _
  constructor
  · intro h x
    exact (AddCommGrpCat.mono_iff_injective _).mp
      (((stalkShortComplex (structureSheafRing X) S x).exact_iff_mono (hTf x)).mp (h x))
  · intro h x
    exact ((stalkShortComplex (structureSheafRing X) S x).exact_iff_mono (hTf x)).mpr
      ((AddCommGrpCat.mono_iff_injective _).mpr (h x))

/-- A morphism of sheaves of modules on a ringed space is an epimorphism exactly when it is
surjective on every stalk. -/
private theorem epi_iff_stalk_surjective (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X)) (f : F ⟶ G) :
    Epi f ↔ ∀ x : X,
      Function.Surjective ((stalkAddCommGroupFunctor (structureSheafRing X) x).map f).hom := by
  let _iab : Abelian (SheafOfModules.{u} (structureSheafRing X)) := SheafOfModules.instAbelian _
  let _inp : NonPreadditiveAbelian (SheafOfModules.{u} (structureSheafRing X)) :=
    Abelian.nonPreadditiveAbelian
  let S : ShortComplex (SheafOfModules.{u} (structureSheafRing X)) :=
    ShortComplex.mk f (0 : G ⟶ G) (by simp)
  rw [← S.exact_iff_epi (by simp [S]), exact_iff_stalkShortComplex_exact]
  have hTg : ∀ x : X, (stalkShortComplex (structureSheafRing X) S x).g = 0 := fun x => by
    change (stalkAddCommGroupFunctor (structureSheafRing X) x).map (0 : G ⟶ G) = 0
    exact Functor.map_zero _ _ _
  constructor
  · intro h x
    exact (AddCommGrpCat.epi_iff_surjective _).mp
      (((stalkShortComplex (structureSheafRing X) S x).exact_iff_epi (hTg x)).mp (h x))
  · intro h x
    exact ((stalkShortComplex (structureSheafRing X) S x).exact_iff_epi (hTg x)).mpr
      ((AddCommGrpCat.epi_iff_surjective _).mpr (h x))

/-- A morphism of sheaves of modules that vanishes on every stalk is zero. -/
private theorem hom_eq_zero_of_stalkMap_eq_zero (X : RingedSpace.{u, u})
    {F G : SheafOfModules.{u} (structureSheafRing X)} (f : F ⟶ G)
    (hf : ∀ x : X, (stalkAddCommGroupFunctor (structureSheafRing X) x).map f = 0) : f = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  induction U with | op U => ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply TopCat.Presheaf.section_ext ⟨G.val.presheaf, G.isSheaf⟩ U
  intro x hx
  have h := CategoryTheory.congr_fun (hf x) (TopCat.Presheaf.germ F.val.presheaf U x hx s)
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map f.val))
      (TopCat.Presheaf.germ F.val.presheaf U x hx s) = 0 at h
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map f.val) s
  exact he.symm.trans (h.trans (map_zero _).symm)

/-! ### The stalk of the structure sheaf, read as the stalk of the unit module -/

/-- The stalk of the unit sheaf of modules is the stalk of the structure sheaf, as abelian
groups: both are the colimit of the sections over the neighbourhoods of the point, taken in
`AddCommGrpCat` and in `CommRingCat` respectively. -/
private noncomputable def unitStalkAddEquiv (X : RingedSpace.{u, u}) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x ≃+
    TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.presheaf x :=
  (preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf)).symm.addCommGroupIsoToAddEquiv

/-- `unitStalkAddEquiv` carries the germ of a section of the unit module to the germ of the
corresponding section of the structure sheaf. -/
private theorem unitStalkAddEquiv_germ (X : RingedSpace.{u, u}) (x : X)
    (U : Opens X.carrier) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
    unitStalkAddEquiv X x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf U x hx r) =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf U x hx r :=
  congrArg (fun f : AddCommGrpCat.of (X.presheaf.obj (op U)) ⟶
      AddCommGrpCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.presheaf x) => f r)
    (ι_preservesColimitIso_inv
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf) (.op ⟨U, hx⟩))

/-- `unitStalkAddEquiv` is linear over the stalk of the structure sheaf, the scalar action on
the stalk of the structure sheaf being multiplication. -/
private noncomputable def unitStalkLinearEquiv (X : RingedSpace.{u, u}) (x : X) :
    letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.presheaf x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
      stalkModule X (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x
      ≃ₗ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.presheaf x]
        TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.presheaf x := by
  let PU := PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)
  letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.presheaf x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) PU.presheaf x) :=
    stalkModule X PU x
  refine { unitStalkAddEquiv X x with map_smul' := ?_ }
  intro r m
  change unitStalkAddEquiv X x (r • m) = r • unitStalkAddEquiv X x m
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) X.presheaf r
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) PU.presheaf m
  let W : Opens X.carrier := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let aW := X.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op a
  let bW := PU.map (homOfLE (show W ≤ V from inf_le_right)).op b
  rw [← TopCat.Presheaf.germ_res_apply (C := CommRingCat.{u}) X.presheaf
      (homOfLE (show W ≤ U from inf_le_left)) x hxW a,
    ← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) PU.presheaf
      (homOfLE (show W ≤ V from inf_le_right)) x hxW b]
  have hsmul := stalkModule_germ_smul X PU x W hxW aW bW
  let bWr : X.presheaf.obj (op W) := bW
  have hsection : aW • bWr = aW * bWr := rfl
  calc
    unitStalkAddEquiv X x
        ((TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW).hom aW •
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) PU.presheaf W x hxW bW) =
      unitStalkAddEquiv X x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) PU.presheaf W x hxW (aW • bW)) :=
        congrArg (unitStalkAddEquiv X x) hsmul.symm
    _ = TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW (aW • bW) :=
      unitStalkAddEquiv_germ X x W hxW (aW • bW)
    _ = (TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW).hom aW *
        (TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW).hom bW := by
          change (TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW).hom
            (aW • bWr) = _
          rw [hsection]
          exact (TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW).hom.map_mul aW bW
    _ = (TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf W x hxW).hom aW •
        unitStalkAddEquiv X x
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) PU.presheaf W x hxW bW) := by
          rw [unitStalkAddEquiv_germ X x W hxW bW]
          simp [smul_eq_mul]

/-- `unitStalkLinearEquiv` carries the germ of a section of the unit module to the germ of the
corresponding section of the structure sheaf. -/
private theorem unitStalkLinearEquiv_germ (X : RingedSpace.{u, u}) (x : X)
    (U : Opens X.carrier) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
    unitStalkLinearEquiv X x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf U x hx r) =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) X.presheaf U x hx r :=
  unitStalkAddEquiv_germ X x U hx r

/-- The stalk of a morphism into the unit module carries the germ of a section to the germ of
its image, read as a section of the structure sheaf. -/
private theorem unit_stalkMap_germ (Y : RingedSpace.{u, u}) (I : SheafOfModules.{u} (structureSheafRing Y))
    (k : I ⟶ SheafOfModules.unit (structureSheafRing Y)) (x : Y) (U : Opens Y) (hx : x ∈ U)
    (m : I.val.obj (op U)) :
    unitStalkLinearEquiv Y x
      (((stalkAddCommGroupFunctor (structureSheafRing Y) x).map k).hom
        (TopCat.Presheaf.germ I.val.presheaf U x hx m)) =
      Y.presheaf.germ U x hx (k.val.app (op U) m) :=
  (congrArg (unitStalkLinearEquiv Y x)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
        ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map k.val) m)).trans
    (unitStalkLinearEquiv_germ Y x U hx (k.val.app (op U) m))

/-! ### The ideal action on sections and on stalks -/

/-- The multiplication map of an ideal sheaf acts on the image of a pure tensor of local
sections by multiplication: `a ⊗ n ↦ a · n`. -/
private theorem idealTensorMultiplication_app_tmul (Y : RingedSpace.{u, u})
    {I : SheafOfModules.{u} (structureSheafRing Y)}
    (j : I ⟶ SheafOfModules.unit (structureSheafRing Y))
    (N : SheafOfModules.{u} (structureSheafRing Y)) (U : Opens Y)
    (a : I.val.obj (op U)) (n : N.val.obj (op U)) :
    ((idealTensorMultiplication Y j N).val.app (op U)).hom
        (toTensorSheafSection Y I N (op U) (a ⊗ₜ[Y.presheaf.obj (op U)] n)) =
      (show ((structureSheafRing Y).obj.obj (op U) : Type u) from
        ((j.val.app (op U)).hom a)) • n := by
  let _mon : MonoidalCategory (PresheafOfModules.{u} (O Y)) :=
    PresheafOfModulesOfCommRing.monoidalCategory
  unfold Stacks.IdealTorsion.idealTensorMultiplication
  set adj := PresheafOfModules.sheafificationAdjunction
    (R := structureSheafRing Y) (𝟙 (structureSheafRing Y).obj) with hadj
  set r : ((structureSheafRing Y).obj.obj (op U) : Type u) :=
    ((j.val.app (op U)).hom a) with hr
  have hunitor : ((λ_ N.val).hom.app (op U)).hom
      ((show (SheafOfModules.unit (structureSheafRing Y)).val.obj (op U) from r) ⊗ₜ[
        Y.presheaf.obj (op U)] n) = r • n := rfl
  have hcounit : ∀ y : N.val.obj (op U),
      ((adj.counit.app N).val.app (op U)).hom
        ((adj.unit.app N.val).app (op U) y) = y := fun y =>
    congrArg (fun α : N.val ⟶ _ => (PresheafOfModules.Hom.app α (op U)).hom y)
      (adj.right_triangle_components N)
  have hnat : ∀ t : ((PresheafOfModules.tensorObj (O := (Y).presheaf) ((SheafOfModules.unit (structureSheafRing Y)).val) (N.val))).obj (op U),
      (((sheafifyFunctor Y).map (λ_ N.val).hom).val.app (op U)).hom
          ((adj.unit.app ((PresheafOfModules.tensorObj (O := (Y).presheaf) ((SheafOfModules.unit (structureSheafRing Y)).val) (N.val)))).app (op U) t) =
        (adj.unit.app N.val).app (op U) (((λ_ N.val).hom.app (op U)).hom t) := fun t =>
    (congrArg (fun α : _ ⟶ _ => (PresheafOfModules.Hom.app α (op U)).hom t)
      (adj.unit.naturality (λ_ N.val).hom)).symm
  change ((adj.counit.app N).val.app (op U)).hom
      ((((sheafifyFunctor Y).map (λ_ N.val).hom).val.app (op U)).hom
        (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map ((j, (𝟙 N)) : (_, _) ⟶ (_, _)))).val.app (op U)).hom
          (toTensorSheafSection Y I N (op U) (a ⊗ₜ[Y.presheaf.obj (op U)] n)))) = r • n
  have hmap : ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map ((j, (𝟙 N)) : (_, _) ⟶ (_, _)))).val.app (op U)).hom
      (toTensorSheafSection Y I N (op U) (a ⊗ₜ[Y.presheaf.obj (op U)] n)) =
      (adj.unit.app ((PresheafOfModules.tensorObj (O := (Y).presheaf) ((SheafOfModules.unit (structureSheafRing Y)).val) (N.val)))).app (op U)
        (r ⊗ₜ[Y.presheaf.obj (op U)] n) :=
    (tensorSheafMap_app_toTensorSheafSection Y I N
      (SheafOfModules.unit (structureSheafRing Y)) N j (𝟙 N) U a n).trans rfl
  rw [hmap]
  exact Eq.trans
    (congrArg (fun z => ((adj.counit.app N).val.app (op U)).hom z)
      ((hnat (r ⊗ₜ[Y.presheaf.obj (op U)] n)).trans
        (congrArg (fun w => (adj.unit.app N.val).app (op U) w) hunitor)))
    (hcounit (r • n))

/-- Two morphisms out of a tensor product that agree on images of pure tensors of local sections
agree; `AlgebraicGeometry.RingedSpaceThickening.tensorSheaf_hom_ext` with the arguments in the
shape used here. -/
private theorem tensorSheaf_hom_ext' {Y : RingedSpace.{u, u}}
    {F G Q : SheafOfModules.{u} (structureSheafRing Y)} {p q : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (F)).obj (G)) ⟶ Q}
    (h : ∀ (V : Opens Y) (m : F.val.obj (op V)) (n : G.val.obj (op V)),
      (p.val.app (op V)).hom (toTensorSheafSection Y F G (op V)
          (m ⊗ₜ[Y.presheaf.obj (op V)] n)) =
        (q.val.app (op V)).hom (toTensorSheafSection Y F G (op V)
          (m ⊗ₜ[Y.presheaf.obj (op V)] n))) :
    p = q :=
  tensorSheaf_hom_ext h

/-- The ideal action is natural in the ideal: tensoring a map of ideals with the identity and
then acting is acting through the composite inclusion. -/
private theorem idealTensorMultiplication_naturality_left (Y : RingedSpace.{u, u})
    {J I : SheafOfModules.{u} (structureSheafRing Y)} (a : J ⟶ I)
    (j : I ⟶ SheafOfModules.unit (structureSheafRing Y))
    (M : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map ((a, (𝟙 M)) : (_, _) ⟶ (_, _))) ≫ idealTensorMultiplication Y j M =
      idealTensorMultiplication Y (a ≫ j) M := by
  refine tensorSheaf_hom_ext' fun V b n => ?_
  have hmap := (tensorSheafMap_app_toTensorSheafSection Y J M I M a (𝟙 M) V b n).trans rfl
  calc ((idealTensorMultiplication Y j M).val.app (op V)).hom
          (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map ((a, (𝟙 M)) : (_, _) ⟶ (_, _)))).val.app (op V)).hom
            (toTensorSheafSection Y J M (op V) (b ⊗ₜ[Y.presheaf.obj (op V)] n)))
      = ((idealTensorMultiplication Y j M).val.app (op V)).hom
          (toTensorSheafSection Y I M (op V)
            ((a.val.app (op V)).hom b ⊗ₜ[Y.presheaf.obj (op V)] n)) := congrArg _ hmap
    _ = (show ((structureSheafRing Y).obj.obj (op V) : Type u) from
          ((j.val.app (op V)).hom ((a.val.app (op V)).hom b))) • n :=
        idealTensorMultiplication_app_tmul Y j M V _ n
    _ = ((idealTensorMultiplication Y (a ≫ j) M).val.app (op V)).hom
          (toTensorSheafSection Y J M (op V) (b ⊗ₜ[Y.presheaf.obj (op V)] n)) :=
        (idealTensorMultiplication_app_tmul Y (a ≫ j) M V b n).symm

/-- Two germs at a point of sections of presheaves of modules are germs of sections over one
common open neighbourhood. -/
private theorem exists_grpGerm_pair (Y : RingedSpace.{u, u}) (F G : PresheafOfModules.{u} (O Y))
    (y : Y.carrier) (p : grpStalk Y F y) (m : grpStalk Y G y) :
    ∃ (W : Opens Y.carrier) (hW : y ∈ W) (a : F.obj (op W)) (b : G.obj (op W)),
      grpGerm Y F y W hW a = p ∧ grpGerm Y G y W hW b = m := by
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) F.presheaf p
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) G.presheaf m
  have hxW : y ∈ U ⊓ V := ⟨hxU, hxV⟩
  exact ⟨U ⊓ V, hxW, F.map (homOfLE inf_le_left).op a, G.map (homOfLE inf_le_right).op b,
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) F.presheaf (homOfLE inf_le_left) y
      hxW a,
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) G.presheaf (homOfLE inf_le_right) y
      hxW b⟩

/-- **The ideal action on stalks.** At a point, the multiplication map `I ⊗ F ⟶ F` of an ideal
sheaf becomes the base-ring multiplication `I_x ⊗ F_x ⟶ F_x`: the stalk of the ideal maps to the
stalk of the structure sheaf by `j`, and that scalar acts. -/
private theorem idealTensorMultiplication_stalk_formula (Y : RingedSpace.{u, u})
    {I : SheafOfModules.{u} (structureSheafRing Y)}
    (j : I ⟶ SheafOfModules.unit (structureSheafRing Y))
    (F : SheafOfModules.{u} (structureSheafRing Y)) (y : Y) :
    let R := ringStalk Y y
    let MF := grpStalk Y F.val y
    letI : Module R MF := stalkModule Y F.val y
    stalkMapL Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (I)).obj (F))).val F.val (idealTensorMultiplication Y j F).val y =
      ((TensorProduct.lid R MF).toLinearMap.comp
        (((unitStalkLinearEquiv Y y).toLinearMap.comp
          (stalkMapL Y I.val (SheafOfModules.unit (structureSheafRing Y)).val j.val
            y)).rTensor MF)).comp
          (tensorStalkIso Y y I F).toLinearMap := by
  let R := ringStalk Y y
  let MF := grpStalk Y F.val y
  let _iMF : Module R MF := stalkModule Y F.val y
  let e := tensorStalkIso Y y I F
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ : ∃ w, e.symm w = z := ⟨e z, e.symm_apply_apply z⟩
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul p m =>
      obtain ⟨W, hxW, aW, sW, hp, hs⟩ := exists_grpGerm_pair Y I.val F.val y p m
      have hsymm : e.symm (grpGerm Y I.val y W hxW aW ⊗ₜ[R] grpGerm Y F.val y W hxW sW) =
          grpGerm Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (I)).obj (F))).val y W hxW
            (toTensorSheafSection Y I F (op W) (aW ⊗ₜ[Y.presheaf.obj (op W)] sW)) := by
        rw [LinearEquiv.symm_apply_eq]
        exact (tensorStalkIso_germ Y y I F W hxW aW sW).symm
      have hjst : (unitStalkLinearEquiv Y y).toLinearMap.comp
            (stalkMapL Y I.val (SheafOfModules.unit (structureSheafRing Y)).val j.val y)
            (grpGerm Y I.val y W hxW aW) =
          Y.presheaf.germ W y hxW ((j.val.app (op W)).hom aW) :=
        unit_stalkMap_germ Y I j y W hxW aW
      have hL : stalkMapL Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (I)).obj (F))).val F.val
            (idealTensorMultiplication Y j F).val y
              (grpGerm Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (I)).obj (F))).val y W hxW
                (toTensorSheafSection Y I F (op W) (aW ⊗ₜ[Y.presheaf.obj (op W)] sW))) =
          (Y.presheaf.germ W y hxW ((j.val.app (op W)).hom aW)) •
            grpGerm Y F.val y W hxW sW := by
        rw [stalkMapL_germ Y _ _ (idealTensorMultiplication Y j F).val y W hxW
            (toTensorSheafSection Y I F (op W) (aW ⊗ₜ[Y.presheaf.obj (op W)] sW)),
          idealTensorMultiplication_app_tmul Y j F W aW sW]
        exact stalkModule_germ_smul Y F.val y W hxW ((j.val.app (op W)).hom aW) sW
      have hR : ((TensorProduct.lid R MF).toLinearMap.comp
              (((unitStalkLinearEquiv Y y).toLinearMap.comp
                (stalkMapL Y I.val (SheafOfModules.unit (structureSheafRing Y)).val j.val
                  y)).rTensor MF)).comp (tensorStalkIso Y y I F).toLinearMap
            (grpGerm Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (I)).obj (F))).val y W hxW
              (toTensorSheafSection Y I F (op W) (aW ⊗ₜ[Y.presheaf.obj (op W)] sW))) =
          (Y.presheaf.germ W y hxW ((j.val.app (op W)).hom aW)) •
            grpGerm Y F.val y W hxW sW := by
        change (TensorProduct.lid R MF)
            ((((unitStalkLinearEquiv Y y).toLinearMap.comp
              (stalkMapL Y I.val (SheafOfModules.unit (structureSheafRing Y)).val j.val
                y)).rTensor MF)
              ((tensorStalkIso Y y I F)
                (grpGerm Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (I)).obj (F))).val y W hxW
                  (toTensorSheafSection Y I F (op W)
                    (aW ⊗ₜ[Y.presheaf.obj (op W)] sW))))) = _
        rw [tensorStalkIso_germ Y y I F W hxW aW sW, LinearMap.rTensor_tmul,
          TensorProduct.lid_tmul, hjst]
      rw [← hp, ← hs, hsymm]
      exact hL.trans hR.symm

/-! ### Stalks of pushforwards and pullbacks -/

/-- The stalk of a morphism of sheaves of modules carries the germ of a section to the germ of
its image. -/
private theorem stalkAddCommGroupFunctor_map_germ (X : RingedSpace.{u, u})
    {F G : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ G) (x : X) (U : Opens X) (hx : x ∈ U)
    (s : F.val.obj (op U)) :
    ((stalkAddCommGroupFunctor (structureSheafRing X) x).map φ).hom
        (TopCat.Presheaf.germ F.val.presheaf U x hx s) =
      TopCat.Presheaf.germ G.val.presheaf U x hx ((φ.val.app (op U)).hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map φ.val) s

/-- The stalk comparison of a pushforward carries the germ of a section to the germ of that
section over the preimage. -/
private theorem pushforward_stalk_germ {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing X)) (x : X) (U : Opens Y) (hx : f.hom.base x ∈ U)
    (m : ((modulePushforward f).obj M).val.obj (op U)) :
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base M.val.presheaf x)
      (TopCat.Presheaf.germ ((modulePushforward f).obj M).val.presheaf U (f.hom.base x) hx m) =
      TopCat.Presheaf.germ M.val.presheaf ((opensMap f).obj U) x hx m :=
  CategoryTheory.congr_fun
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.hom.base M.val.presheaf U x hx) m

/-- The module structure on the stalk of a sheaf of modules named in
`Stacks.SheafOfModules.TensorStalkRingedSpace` is Mathlib's, by definition. -/
private theorem stalkModule_eq_mathlib (X : RingedSpace.{u, u})
    (F : SheafOfModules.{u} (structureSheafRing X)) (x : X) :
    stalkModule X F.val x =
      F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x :=
  rfl

/-- `AlgebraicGeometry.IsFlatOverAt` unfolded, with the module structure on the stalk pinned to
Mathlib's. The statement of `IsFlatOverAt` resolves it by instance search in a context where
only Mathlib's instance exists, so this records which instance is meant. -/
private theorem isFlatOverAt_eq {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X)) (x : X) :
    AlgebraicGeometry.IsFlatOverAt f F x =
      (letI M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
       letI : Module (X.presheaf.stalk x)
           (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
         M.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
       letI : Module (Y.presheaf.stalk (f.hom.base x))
           (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
         Module.compHom _ (f.hom.stalkMap x).hom
       Module.Flat (Y.presheaf.stalk (f.hom.base x))
         (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)) :=
  rfl

/-- **Flatness over the target at a point, read through `stalkModule`.** This is
`AlgebraicGeometry.IsFlatOverAt`, with the module structure on the stalk given by
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` rather than by Mathlib's instance. -/
private theorem flat_stalkModule_iff_isFlatOverAt {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X)) (x : X) :
    letI := stalkModule X F.val x
    letI : Module (Y.presheaf.stalk (f.hom.base x)) (grpStalk X F.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    Module.Flat (Y.presheaf.stalk (f.hom.base x)) (grpStalk X F.val x) ↔
      AlgebraicGeometry.IsFlatOverAt f F x := by
  rw [isFlatOverAt_eq, stalkModule_eq_mathlib X F x]

/-- **A flat morphism makes the structure sheaf flat over the target.** The stalk of the unit
module at `x` is the local ring `𝒪_{X,x}`, linearly over itself and hence over `𝒪_{Y,f(x)}`, and
flatness of `f` at `x` is flatness of `𝒪_{X,x}` over `𝒪_{Y,f(x)}`. -/
theorem isFlatOver_unit_of_isFlat {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.IsFlat f) :
    AlgebraicGeometry.IsFlatOver f (SheafOfModules.unit (structureSheafRing X)) := by
  intro x
  refine (flat_stalkModule_iff_isFlatOverAt f _ x).1 ?_
  letI := stalkModule X (SheafOfModules.unit (structureSheafRing X)).val x
  letI : Module (Y.presheaf.stalk (f.hom.base x))
      (grpStalk X (SheafOfModules.unit (structureSheafRing X)).val x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) := hf x
  let e := unitStalkLinearEquiv X x
  let e' : grpStalk X (SheafOfModules.unit (structureSheafRing X)).val x ≃ₗ[
      Y.presheaf.stalk (f.hom.base x)] X.presheaf.stalk x :=
    { e.toAddEquiv with
      map_smul' := fun r m => e.map_smul ((f.hom.stalkMap x).hom r) m }
  exact Module.Flat.of_linearEquiv e'

/-- **Stacks 0098.** The stalk of a pullback is the base change of the stalk along the stalk map
of `f`, by an equivalence sending the canonical image of a germ to `1 ⊗ germ`. This is
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, read through the comparison
`(f_* f^* 𝒢)_{f(x)} ⟶ (f^* 𝒢)_x`. -/
private theorem modulePullback_unit_stalk_formula {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI : Module (Y.presheaf.stalk (f.hom.base x)) (TopCat.Presheaf.stalk
        (C := AddCommGrpCat.{u}) G.val.presheaf (f.hom.base x)) :=
      G.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (f.hom.base x)
    letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((modulePullback f).obj G).val.presheaf x) :=
      ((modulePullback f).obj G).val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        x
    ∃ e : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((modulePullback f).obj G).val.presheaf x) ≃ₗ[X.presheaf.stalk x]
        (X.presheaf.stalk x) ⊗[Y.presheaf.stalk (f.hom.base x)]
          ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf (f.hom.base x)),
      ∀ m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf (f.hom.base x)),
        e ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
          ((modulePullback f).obj G).val.presheaf x).hom
          (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
            ((modulePullbackPushforwardAdjunction f).unit.app G)).hom m)) =
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m := by
  let GP : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
  let PP : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((modulePullback f).obj G).val
  let _iAlg : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let _iA : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) GP.presheaf (f.hom.base x)) :=
    GP.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (f.hom.base x)
  let _iR : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) PP.presheaf x) :=
    PP.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  obtain ⟨e, he⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f G x
  refine ⟨e, ?_⟩
  intro m
  obtain ⟨V, hxV, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) GP.presheaf m
  let η := (modulePullbackPushforwardAdjunction f).unit.app G
  let ηab := (PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map η.val
  let ηst := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map ηab
  have hηgerm : ηst (TopCat.Presheaf.germ GP.presheaf V (f.hom.base x) hxV s) =
      TopCat.Presheaf.germ
        ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).obj
          ((modulePullback f ⋙ modulePushforward f).obj G).val)
        V (f.hom.base x) hxV (η.val.app (op V) s) := by
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map ηab)
        (TopCat.Presheaf.germ
          ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).obj
            ((𝟭 (SheafOfModules (structureSheafRing Y))).obj G).val)
          V (f.hom.base x) hxV s) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply V (f.hom.base x) hxV ηab s]
    simp only [ηab]
    exact congrArg (fun t =>
      (ConcreteCategory.hom (TopCat.Presheaf.germ
        ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).obj
          ((modulePullback f ⋙ modulePushforward f).obj G).val) V
          (f.hom.base x) hxV)) t)
      (PresheafOfModules.toPresheaf_map_app_apply η.val (op V) s)
  change e ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base PP.presheaf x).hom
    (ηst (TopCat.Presheaf.germ GP.presheaf V (f.hom.base x) hxV s))) = _
  rw [hηgerm]
  change e (ConcreteCategory.hom
    (TopCat.Presheaf.germ
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj PP.presheaf)
      V (f.hom.base x) hxV ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base PP.presheaf x)
      ((η.val.app (op V)) s)) = _
  rw [TopCat.Presheaf.stalkPushforward_germ]
  exact he V hxV s

/-- `modulePullback_unit_stalk_formula`, read through the module structures of
`Stacks.SheafOfModules.TensorStalkRingedSpace`. -/
private theorem pullback_stalk_formula {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI := stalkModule Y G.val (f.hom.base x)
    letI := stalkModule X ((modulePullback f).obj G).val x
    ∃ e : grpStalk X ((modulePullback f).obj G).val x ≃ₗ[X.presheaf.stalk x]
        (X.presheaf.stalk x) ⊗[Y.presheaf.stalk (f.hom.base x)] grpStalk Y G.val (f.hom.base x),
      ∀ m : grpStalk Y G.val (f.hom.base x),
        e ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
          ((modulePullback f).obj G).val.presheaf x)
          (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
            ((modulePullbackPushforwardAdjunction f).unit.app G)).hom m)) =
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m := by
  rw [stalkModule_eq_mathlib Y G (f.hom.base x),
    stalkModule_eq_mathlib X ((modulePullback f).obj G) x]
  exact modulePullback_unit_stalk_formula f G x

/-- The stalk of the structure-sheaf map of `f`, read through `unitStalkLinearEquiv`, is the
stalk map of `f`. -/
private theorem structureSheaf_stalk_formula {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X)
    (m : grpStalk Y (SheafOfModules.unit (structureSheafRing Y)).val (f.hom.base x)) :
    unitStalkLinearEquiv X x
      ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
        (SheafOfModules.unit (structureSheafRing X)).val.presheaf x)
        (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))).hom m)) =
      (f.hom.stalkMap x).hom (unitStalkLinearEquiv Y (f.hom.base x) m) := by
  let α := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)
  obtain ⟨U, hx, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (SheafOfModules.unit (structureSheafRing Y)).val.presheaf m
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply' U (f.hom.base x) hx
    ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map α.val) a
  change ((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map α).hom
      (TopCat.Presheaf.germ (SheafOfModules.unit (structureSheafRing Y)).val.presheaf
        U (f.hom.base x) hx a) = _ at hmap
  let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
    (SheafOfModules.unit (structureSheafRing X)).val.presheaf x
  have hp := pushforward_stalk_germ f (SheafOfModules.unit (structureSheafRing X)) x U hx
    (α.val.app (op U) a)
  calc
    _ = unitStalkLinearEquiv X x
        (p (TopCat.Presheaf.germ ((modulePushforward f).obj
          (SheafOfModules.unit (structureSheafRing X))).val.presheaf U (f.hom.base x) hx
            (α.val.app (op U) a))) := congrArg (fun z => unitStalkLinearEquiv X x (p z)) hmap
    _ = unitStalkLinearEquiv X x
        (TopCat.Presheaf.germ (SheafOfModules.unit (structureSheafRing X)).val.presheaf
          ((opensMap f).obj U) x hx (α.val.app (op U) a)) :=
      congrArg (unitStalkLinearEquiv X x) hp
    _ = X.presheaf.germ ((opensMap f).obj U) x hx (f.hom.c.app (op U) a) :=
      unitStalkLinearEquiv_germ X x ((opensMap f).obj U) hx (f.hom.c.app (op U) a)
    _ = (f.hom.stalkMap x).hom (Y.presheaf.germ U (f.hom.base x) hx a) :=
      (CategoryTheory.congr_fun (PresheafedSpace.stalkMap_germ f.hom U x hx) a).symm
    _ = _ := congrArg (f.hom.stalkMap x).hom
      (unitStalkLinearEquiv_germ Y (f.hom.base x) U hx a).symm

/-- The stalk comparison of a pushforward is natural. -/
private theorem stalkPushforward_naturality {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {M N : SheafOfModules.{u} (structureSheafRing X)} (g : M ⟶ N) (x : X)
    (z : grpStalk Y ((modulePushforward f).obj M).val (f.hom.base x)) :
    ((stalkAddCommGroupFunctor (structureSheafRing X) x).map g).hom
      ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base M.val.presheaf x) z) =
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base N.val.presheaf x)
      (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
        ((modulePushforward f).map g)).hom z) := by
  obtain ⟨U, hx, m, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq ((modulePushforward f).obj M).val.presheaf z
  have e1 := congrArg ((stalkAddCommGroupFunctor (structureSheafRing X) x).map g).hom
    (pushforward_stalk_germ f M x U hx m)
  have e2 := stalkAddCommGroupFunctor_map_germ X g x ((opensMap f).obj U) hx m
  have e3 := congrArg
    (fun w => (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base N.val.presheaf x) w)
    (stalkAddCommGroupFunctor_map_germ Y ((modulePushforward f).map g) (f.hom.base x) U hx m)
  have e4 := pushforward_stalk_germ f N x U hx
    (((modulePushforward f).map g).val.app (op U) m)
  exact (e1.trans e2).trans (e3.trans e4).symm

/-- Transposing along `f^* ⊣ f_*` on stalks: the stalk of the transpose of `q` applied to a germ
is the stalk of `q` applied to the canonical image of that germ. -/
private theorem pullback_stalk_transpose {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (N : SheafOfModules.{u} (structureSheafRing X))
    (q : (modulePullback f).obj G ⟶ N) (x : X) (m : grpStalk Y G.val (f.hom.base x)) :
    ((stalkAddCommGroupFunctor (structureSheafRing X) x).map q).hom
      ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
        ((modulePullback f).obj G).val.presheaf x)
        (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
          ((modulePullbackPushforwardAdjunction f).unit.app G)).hom m)) =
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base N.val.presheaf x)
      (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
        ((modulePullbackPushforwardAdjunction f).homEquiv G N q)).hom m) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  exact stalkPushforward_naturality f q x
    (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
      ((modulePullbackPushforwardAdjunction f).unit.app G)).hom m)

/-- The stalk of the map `f^* 𝒥 ⟶ 𝒪_X` obtained by pulling back an ideal inclusion: on the base
change `B ⊗_A 𝒥_{f(x)}` it is `b ⊗ z ↦ b · f^♯(j z)`. -/
private theorem pullbackIdeal_stalk_formula {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (J : SheafOfModules.{u} (structureSheafRing Y)) (j : J ⟶ SheafOfModules.unit (structureSheafRing Y)) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI := stalkModule Y J.val (f.hom.base x)
    letI := stalkModule X ((modulePullback f).obj J).val x
    ∃ e : grpStalk X ((modulePullback f).obj J).val x ≃ₗ[X.presheaf.stalk x]
        (X.presheaf.stalk x) ⊗[Y.presheaf.stalk (f.hom.base x)] grpStalk Y J.val (f.hom.base x),
      ∀ (b : X.presheaf.stalk x) (m : grpStalk Y J.val (f.hom.base x)),
      unitStalkLinearEquiv X x
          (((stalkAddCommGroupFunctor (structureSheafRing X) x).map
            ((modulePullback f).map j ≫ modulePullbackUnitToUnit f)).hom
            (e.symm (b ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m))) =
        b * (f.hom.stalkMap x).hom
          (unitStalkLinearEquiv Y (f.hom.base x)
            (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map j).hom m)) := by
  let _iAlg : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let _iJ := stalkModule Y J.val (f.hom.base x)
  let _iP := stalkModule X ((modulePullback f).obj J).val x
  obtain ⟨e, he⟩ := pullback_stalk_formula f J x
  refine ⟨e, ?_⟩
  intro b m
  have hq : (modulePullbackPushforwardAdjunction f).homEquiv J
        (SheafOfModules.unit (structureSheafRing X))
        ((modulePullback f).map j ≫ modulePullbackUnitToUnit f) =
      j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) := by
    rw [Adjunction.homEquiv_naturality_left, homEquiv_modulePullbackUnitToUnit]
    rfl
  have hsymm : e.symm ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m) =
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
        ((modulePullback f).obj J).val.presheaf x)
        (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
          ((modulePullbackPushforwardAdjunction f).unit.app J)).hom m) :=
    (congrArg e.symm (he m)).symm.trans (e.symm_apply_apply _)
  have hgen : unitStalkLinearEquiv X x
        (((stalkAddCommGroupFunctor (structureSheafRing X) x).map
          ((modulePullback f).map j ≫ modulePullbackUnitToUnit f)).hom
          (e.symm ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m))) =
      (f.hom.stalkMap x).hom
        (unitStalkLinearEquiv Y (f.hom.base x)
          (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map j).hom m)) := by
    have hcomp : ((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
          (j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))).hom m =
        ((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))).hom
          (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map j).hom m) :=
      (congrArg (fun w : (stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).obj J ⟶
          (stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).obj
            ((modulePushforward f).obj (SheafOfModules.unit (structureSheafRing X))) =>
        (AddCommGrpCat.Hom.hom w) m)
        ((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map_comp j
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)))).trans rfl
    rw [hsymm, pullback_stalk_transpose f J _
      ((modulePullback f).map j ≫ modulePullbackUnitToUnit f) x m, hq]
    exact (congrArg (fun z => unitStalkLinearEquiv X x
        ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
          (SheafOfModules.unit (structureSheafRing X)).val.presheaf x) z)) hcomp).trans
      (structureSheaf_stalk_formula f x
        (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map j).hom m))
  have hlin : ∀ (c : X.presheaf.stalk x)
      (z : grpStalk X ((modulePullback f).obj J).val x),
      unitStalkLinearEquiv X x
          (((stalkAddCommGroupFunctor (structureSheafRing X) x).map
            ((modulePullback f).map j ≫ modulePullbackUnitToUnit f)).hom (c • z)) =
        c * unitStalkLinearEquiv X x
          (((stalkAddCommGroupFunctor (structureSheafRing X) x).map
            ((modulePullback f).map j ≫ modulePullbackUnitToUnit f)).hom z) := by
    intro c z
    exact ((unitStalkLinearEquiv X x).toLinearMap.comp
      (stalkMapL X ((modulePullback f).obj J).val (SheafOfModules.unit (structureSheafRing X)).val
        ((modulePullback f).map j ≫ modulePullbackUnitToUnit f).val x)).map_smul c z
  have hbt : e.symm (b ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m) =
      b • e.symm ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m) := by
    rw [← map_smul]
    exact congrArg e.symm
      (((congrArg (fun c => c ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m)
        (mul_one b)).symm).trans (TensorProduct.smul_tmul' b (1 : X.presheaf.stalk x) m))
  rw [hbt, hlin, hgen]

/-! ### Two categorical criteria -/

/-- **Transporting an isomorphism across a tensor-pullback comparison.** Let `P` be a functor
with a comparison `α : T ⋙ P ≅ P × P ⋙ U` between a bifunctor `T` downstairs and a bifunctor
`U` upstairs, let `e : R ≅ P K` and `d : P H ≅ Q` be isomorphisms. Then the composite
`U(e ≫ P f, 1) ≫ α⁻¹ ≫ P g ≫ d` is an isomorphism exactly when `P (T(f, 1) ≫ g)` is: the
naturality square of `α` at `(f, 1)` turns the first into the second up to the invertible
factors.

This is the shape in which the criterion of Stacks 08LI is reduced from the reduced source `X`
to the ambient source `X'`. -/
private theorem isIso_tensor_pullback_map_iff {C E : Type*} [Category* C] [Category* E]
    (P : C ⥤ E) (T : C × C ⥤ C) (U : E × E ⥤ E) (α : T ⋙ P ≅ Functor.prod P P ⋙ U)
    {K I M H : C} {R Q : E} (e : R ≅ P.obj K) (f : K ⟶ I) (g : T.obj (I, M) ⟶ H)
    (d : P.obj H ≅ Q) :
    IsIso (U.map (show (R, P.obj M) ⟶ (P.obj I, P.obj M) from (e.hom ≫ P.map f, 𝟙 _)) ≫
        α.inv.app (I, M) ≫ P.map g ≫ d.hom) ↔
      IsIso (P.map (T.map (show (K, M) ⟶ (I, M) from (f, 𝟙 _)) ≫ g)) := by
  let v : (R, P.obj M) ⟶ (P.obj K, P.obj M) := (e.hom, 𝟙 _)
  have : IsIso v := (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (U.map v) := Functor.map_isIso U v
  let w : (K, M) ⟶ (I, M) := (f, 𝟙 _)
  have hw : (e.hom ≫ P.map f, 𝟙 (P.obj M)) = v ≫ (Functor.prod P P).map w := by simp [v, w]
  rw [hw, U.map_comp]
  have hn := α.inv.naturality w
  change U.map ((Functor.prod P P).map w) ≫ α.inv.app (I, M) =
    α.inv.app (K, M) ≫ P.map (T.map w) at hn
  rw [Category.assoc, ← Category.assoc (U.map ((Functor.prod P P).map w)), hn]
  simp only [Category.assoc]
  rw [← P.map_comp_assoc]
  constructor
  · intro h
    have := h
    have : IsIso (α.inv.app (K, M) ≫ P.map (T.map w ≫ g) ≫ d.hom) :=
      IsIso.of_isIso_comp_left (U.map v) _
    have : IsIso (P.map (T.map w ≫ g) ≫ d.hom) :=
      IsIso.of_isIso_comp_left (α.inv.app (K, M)) _
    exact IsIso.of_isIso_comp_right _ d.hom
  · intro h
    have := h
    infer_instance

/-- **Descending invertibility across a left adjoint.** In a balanced category, if `g` is an
epimorphism and the unit of an adjunction is a monomorphism at its source, then `L g` is
invertible exactly when `g` is. -/
private theorem isIso_map_iff_of_epi_of_mono_unit {C E : Type*} [Category* C] [Category* E]
    [Balanced C] {L : C ⥤ E} {R : E ⥤ C} (adj : L ⊣ R) {M N : C} (g : M ⟶ N) (hg : Epi g)
    (hu : Mono (adj.unit.app M)) :
    IsIso (L.map g) ↔ IsIso g := by
  have := hg
  have := hu
  constructor
  · intro h
    have := h
    have : Mono (adj.unit.app M ≫ R.map (L.map g)) := by infer_instance
    have heq : g ≫ adj.unit.app N = adj.unit.app M ≫ R.map (L.map g) := adj.unit.naturality g
    have : Mono (g ≫ adj.unit.app N) := heq.symm ▸ inferInstance
    have : Mono g := mono_of_mono g (adj.unit.app N)
    exact isIso_of_mono_of_epi g
  · intro h
    have := h
    infer_instance

/-! ### The ideal of a thickening on stalks -/

/-- **The stalk of the ideal of a thickening is the kernel of the stalk map.** For a morphism of
ringed spaces whose underlying map is a homeomorphism and whose structure-sheaf map is
surjective, the stalk of the ideal sheaf maps onto the kernel of the stalk map of `f`, and the
stalk map is surjective. -/
@[ega "IV 16.1.1" "special case"]
private theorem stalkIdeal_exact {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [IsIso f.hom.base]
    (hα : Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))) (x : X) :
    Function.Exact (fun a => unitStalkLinearEquiv Y (f.hom.base x)
        (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
          (idealSheafι f)).hom a)) (f.hom.stalkMap x).hom ∧
      Function.Surjective (f.hom.stalkMap x).hom := by
  have hS : (ShortComplex.mk (idealSheafι f)
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))
      (kernel.condition _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have hex : Function.Exact
      ((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map (idealSheafι f)).hom
      ((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))).hom :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      ((exact_iff_stalkShortComplex_exact (structureSheafRing Y) _).mp hS (f.hom.base x))
  have hsurj := (epi_iff_stalk_surjective Y _ _
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))).mp hα (f.hom.base x)
  have hiso : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      (SheafOfModules.unit (structureSheafRing X)).val.presheaf x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
      (TopCat.homeoOfIso (asIso f.hom.base)).isInducing _ x
  have hp := (AddCommGrpCat.mono_iff_injective
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      (SheafOfModules.unit (structureSheafRing X)).val.presheaf x)).mp hiso.mono_of_iso
  constructor
  · intro a
    constructor
    · intro ha
      refine (hex ((unitStalkLinearEquiv Y (f.hom.base x)).symm a)).mp ?_ |>.imp
        fun b hb => ?_
      · apply hp
        apply (unitStalkLinearEquiv X x).injective
        refine Eq.trans ?_
          (((congrArg (unitStalkLinearEquiv X x) (map_zero _)).trans (map_zero _)).symm :
            (0 : X.presheaf.stalk x) = _)
        refine Eq.trans
          (structureSheaf_stalk_formula f x ((unitStalkLinearEquiv Y (f.hom.base x)).symm a)) ?_
        rw [(unitStalkLinearEquiv Y (f.hom.base x)).apply_symm_apply, ha]
      · exact (congrArg (unitStalkLinearEquiv Y (f.hom.base x)) hb).trans
          ((unitStalkLinearEquiv Y (f.hom.base x)).apply_symm_apply a)
    · rintro ⟨b, rfl⟩
      have hz := (hex (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map
        (idealSheafι f)).hom b)).mpr ⟨b, rfl⟩
      refine Eq.trans (structureSheaf_stalk_formula f x _).symm ?_
      rw [hz]
      exact (congrArg (unitStalkLinearEquiv X x) (map_zero _)).trans (map_zero _)
  · intro a
    obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
        (SheafOfModules.unit (structureSheafRing X)).val.presheaf x)).mp hiso.epi_of_iso
      ((unitStalkLinearEquiv X x).symm a)
    obtain ⟨c, hc⟩ := hsurj b
    refine ⟨unitStalkLinearEquiv Y (f.hom.base x) c, ?_⟩
    refine Eq.trans (structureSheaf_stalk_formula f x c).symm ?_
    rw [hc, hb]
    exact (unitStalkLinearEquiv X x).apply_symm_apply a

/-- **The kernel of the stalk map of a first-order thickening has square zero.** The square of
the ideal vanishes on every open set, so the square of its stalk, which is the kernel of the
stalk map by `stalkIdeal_exact`, vanishes. -/
private theorem stalkMap_kernel_square_zero {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsFirstOrderThickening f) (x : X) :
    RingHom.ker (f.hom.stalkMap x).hom ^ 2 = ⊥ := by
  have : IsIso f.hom.base := hf.1.1
  let α := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)
  let I := kernel α
  let k := kernel.ι α
  let T := stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)
  let j := fun a => unitStalkLinearEquiv Y (f.hom.base x) ((T.map k).hom a)
  have hex := (stalkIdeal_exact f hf.1.2.1 x).1
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  obtain ⟨m, hm⟩ := (hex a).mp ha
  obtain ⟨n, hn⟩ := (hex b).mp hb
  obtain ⟨W, hxW, mW, nW, rfl, rfl⟩ := exists_grpGerm_pair Y I.val I.val (f.hom.base x) m n
  have hmW : Y.presheaf.germ W (f.hom.base x) hxW (k.val.app (op W) mW) = a := by
    rw [← unit_stalkMap_germ Y I k (f.hom.base x) W hxW mW]
    exact hm
  have hnW : Y.presheaf.germ W (f.hom.base x) hxW (k.val.app (op W) nW) = b := by
    rw [← unit_stalkMap_germ Y I k (f.hom.base x) W hxW nW]
    exact hn
  have hker (z : I.val.obj (op W)) :
      k.val.app (op W) z ∈ RingHom.ker ((structureSheafHom f).hom.app (op W)).hom :=
    congrArg (fun l : I ⟶ (SheafOfModules.pushforward (structureSheafHom f)).obj
      (SheafOfModules.unit (structureSheafRing X)) => l.val.app (op W) z) (kernel.condition α)
  let r : Y.presheaf.obj (op W) := k.val.app (op W) mW
  let t : Y.presheaf.obj (op W) := k.val.app (op W) nW
  let L : Ideal (Y.presheaf.obj (op W)) :=
    RingHom.ker ((structureSheafHom f).hom.app (op W)).hom
  have hmul : r * t ∈ L ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (show r ∈ L from hker mW) (show t ∈ L from hker nW)
  have hnil : L ^ 2 = ⊥ := hf.2 W
  rw [hnil] at hmul
  have hzero : r * t = 0 := hmul
  change a * b = 0
  rw [← hmW, ← hnW]
  change (Y.presheaf.germ W (f.hom.base x) hxW) r * (Y.presheaf.germ W (f.hom.base x) hxW) t = 0
  rw [← map_mul, hzero, map_zero]

/-- The stalk of the ideal of a thickening, as an ideal of the stalk of `𝒪_Y`: the stalk of the
inclusion is injective with image the kernel of the stalk map of `f`. -/
private theorem exists_stalkIdealLinearEquiv {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsThickening f) (x : X) :
    letI := stalkModule Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val (f.hom.base x)
    ∃ e : grpStalk Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val (f.hom.base x)
        ≃ₗ[Y.presheaf.stalk (f.hom.base x)] RingHom.ker (f.hom.stalkMap x).hom,
      ∀ m, (e m).val = unitStalkLinearEquiv Y (f.hom.base x)
        (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map (idealSheafι f)).hom m) := by
  let J := AlgebraicGeometry.SheafOfModules.idealSheaf f
  let _iJ := stalkModule Y J.val (f.hom.base x)
  have : IsIso f.hom.base := hf.1
  let T := stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)
  let k := idealSheafι f
  let l := (unitStalkLinearEquiv Y (f.hom.base x)).toLinearMap.comp
    (stalkMapL Y J.val (SheafOfModules.unit (structureSheafRing Y)).val k.val (f.hom.base x))
  have hinj : Function.Injective l := (unitStalkLinearEquiv Y (f.hom.base x)).injective.comp
    ((mono_iff_stalk_injective Y _ _ k).mp inferInstance (f.hom.base x))
  have hex := (stalkIdeal_exact f hf.2.1 x).1
  let l' : grpStalk Y J.val (f.hom.base x) →ₗ[Y.presheaf.stalk (f.hom.base x)]
      RingHom.ker (f.hom.stalkMap x).hom :=
    l.codRestrict _ fun m => (hex (l m)).mpr ⟨m, rfl⟩
  have hbij : Function.Bijective l' := by
    constructor
    · intro a b h
      exact hinj (congrArg Subtype.val h)
    · intro a
      obtain ⟨b, hb⟩ := (hex a).mp a.property
      exact ⟨b, Subtype.ext hb⟩
  exact ⟨LinearEquiv.ofBijective l' hbij, fun _ => rfl⟩

/-- **The ideal of a first-order thickening is a square-zero ideal on stalks.** -/
private theorem firstOrder_stalkIdeal {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsFirstOrderThickening f) (y : Y) :
    letI := stalkModule Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val y
    ∃ J : Ideal (Y.presheaf.stalk y), J ^ 2 = ⊥ ∧
      ∃ e : grpStalk Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val y
          ≃ₗ[Y.presheaf.stalk y] J,
        ∀ m, (e m).val = unitStalkLinearEquiv Y y
          (((stalkAddCommGroupFunctor (structureSheafRing Y) y).map (idealSheafι f)).hom m) := by
  have : IsIso f.hom.base := hf.1.1
  obtain ⟨x, rfl⟩ := (TopCat.homeoOfIso (asIso f.hom.base)).surjective y
  exact ⟨_, stalkMap_kernel_square_zero f hf x, exists_stalkIdealLinearEquiv f hf.1 x⟩

/-- Any ideal of the stalk realising the stalk of the ideal sheaf through the stalk of its
inclusion is the kernel of the stalk map of `f`. -/
private theorem stalkIdeal_eq_stalkMap_ker {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsThickening f) (x : X) (J : Ideal (Y.presheaf.stalk (f.hom.base x)))
    (e : letI := stalkModule Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val (f.hom.base x)
      grpStalk Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val (f.hom.base x)
        ≃ₗ[Y.presheaf.stalk (f.hom.base x)] J)
    (he : ∀ z, (e z).val = unitStalkLinearEquiv Y (f.hom.base x)
      (((stalkAddCommGroupFunctor (structureSheafRing Y) (f.hom.base x)).map (idealSheafι f)).hom z)) :
    J = RingHom.ker (f.hom.stalkMap x).hom := by
  have : IsIso f.hom.base := hf.1
  have hex := (stalkIdeal_exact f hf.2.1 x).1
  ext a
  constructor
  · intro ha
    exact (hex a).2 ⟨e.symm ⟨a, ha⟩,
      (he (e.symm ⟨a, ha⟩)).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩))⟩
  · intro ha
    obtain ⟨z, hz⟩ := (hex a).1 ha
    exact ((he z).trans hz) ▸ (e z).property

/-- `stalkIdeal_eq_stalkMap_ker` at a point of the target presented as the image of a point of
the source. -/
private theorem stalkIdeal_eq_stalkMap_ker_of_base_eq {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsThickening f) (x : X) (y : Y) (hxy : f.hom.base x = y) (J : Ideal (Y.presheaf.stalk y))
    (e : letI := stalkModule Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val y
      grpStalk Y (AlgebraicGeometry.SheafOfModules.idealSheaf f).val y
        ≃ₗ[Y.presheaf.stalk y] J)
    (he : ∀ z, (e z).val = unitStalkLinearEquiv Y y
      (((stalkAddCommGroupFunctor (structureSheafRing Y) y).map (idealSheafι f)).hom z)) :
    J = (congrArg (fun p : Y => Ideal (Y.presheaf.stalk p)) hxy).mp
      (RingHom.ker (f.hom.stalkMap x).hom) := by
  cases hxy
  exact stalkIdeal_eq_stalkMap_ker f hf x J e he

/-- Transporting the kernel of a ring homomorphism out of a stalk along an equality of
points. -/
private theorem stalk_ker_transport (S : RingedSpace.{u, u}) {s t : S} (h : s = t)
    {C : CommRingCat.{u}} (f : S.presheaf.stalk t ⟶ C) :
    RingHom.ker ((eqToHom (congrArg S.presheaf.stalk h) ≫ f).hom) =
      (congrArg (fun p : S => Ideal (S.presheaf.stalk p)) h.symm).mp (RingHom.ker f.hom) := by
  cases h
  rfl

/-! ### The local algebra -/

/-- **The square-zero local criterion of flatness, in the shape used here.** For a square-zero
ideal `J` with `M/JM` flat over `R/J`, flatness of `M` is injectivity of the multiplication map
`J ⊗ M ⟶ M`. The forward implication is flatness applied to the inclusion of `J`. -/
private theorem flat_iff_squareZero_idealAction_injective {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    (hquot : Module.Flat (R ⧸ J) (M ⧸ J • (⊤ : Submodule R M))) :
    Module.Flat R M ↔
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)) := by
  constructor
  · intro hflat
    have hmul : TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype) =
        (TensorProduct.lid R M).comp (J.subtype.rTensor M) := by
      apply TensorProduct.ext'
      intro a m
      simp
    rw [hmul]
    exact (TensorProduct.lid R M).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap (M := M) J.subtype J.injective_subtype)
  · exact fun hinj => flat_of_sq_zero_local_criterion J hJ hquot hinj

/-- **Base change of an ideal multiplication map.** If `q : B ⊗_A J ⟶ B` is the base change of
`j : J ⟶ A`, then injectivity of the induced map `(B ⊗_A J) ⊗_B M ⟶ M` is injectivity of
`J ⊗_A M ⟶ M`: the two are conjugate by the cancellation of the base change. -/
private theorem baseChange_idealAction_injective_iff {A B J M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup J] [Module A J] (j : J →ₗ[A] A) (q : B ⊗[A] J →ₗ[B] B)
    (hq : ∀ (b : B) (z : J), q (b ⊗ₜ[A] z) = b * algebraMap A B (j z)) :
    Function.Injective ((TensorProduct.lid B M).toLinearMap.comp (q.rTensor M)) ↔
      Function.Injective ((TensorProduct.lid A M).toLinearMap.comp (j.rTensor M)) := by
  let e : ((B ⊗[A] J) ⊗[B] M) ≃ₗ[A] (J ⊗[A] M) :=
    ((TensorProduct.comm B (B ⊗[A] J) M).restrictScalars A).trans
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B M J).restrictScalars A).trans
        (TensorProduct.comm A M J))
  let μ := (TensorProduct.lid A M).toLinearMap.comp (j.rTensor M)
  let ν := (TensorProduct.lid B M).toLinearMap.comp (q.rTensor M)
  have h : ν.restrictScalars A = μ.comp e.toLinearMap := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul z m =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b z =>
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply,
          LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hq, LinearEquiv.coe_coe,
          e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
          TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          μ, ν]
        rw [mul_smul, IsScalarTower.algebraMap_smul B (j z) m, smul_comm]
      | add z w hz hw => simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hz hw
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  change Function.Injective ν ↔ Function.Injective μ
  have hfun : (ν : _ → _) = μ ∘ e := by
    funext z
    exact congrArg (fun l => l z) h
  rw [hfun]
  constructor
  · intro hinj p q' hpq
    exact e.symm.injective (hinj (by simpa using hpq))
  · intro hinj
    exact hinj.comp e.injective

/-- Injectivity of the multiplication `Q ⊗ V ⟶ V` induced by a map `q : Q ⟶ B` is invariant under
a linear equivalence `e : Q ≃ Q'` with `q = q' ∘ e`. -/
private theorem lid_rTensor_comp_injective_iff {B Q Q' V : Type*} [CommRing B] [AddCommGroup Q]
    [Module B Q] [AddCommGroup Q'] [Module B Q'] [AddCommGroup V] [Module B V] (e : Q ≃ₗ[B] Q')
    (q : Q →ₗ[B] B) (q' : Q' →ₗ[B] B) (h : ∀ p, q p = q' (e p)) :
    Function.Injective ((TensorProduct.lid B V).toLinearMap.comp (q.rTensor V)) ↔
      Function.Injective ((TensorProduct.lid B V).toLinearMap.comp (q'.rTensor V)) := by
  have hc : (TensorProduct.lid B V).toLinearMap.comp (q.rTensor V) =
      ((TensorProduct.lid B V).toLinearMap.comp (q'.rTensor V)).comp
        (TensorProduct.congr e (LinearEquiv.refl B V)).toLinearMap := by
    apply TensorProduct.ext'
    intro p v
    simp [h]
  rw [hc, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact EquivLike.injective_comp (TensorProduct.congr e (LinearEquiv.refl B V)) _

/-- A base-changed ideal whose generators multiply to zero acts as zero on the base change
itself. -/
private theorem squareZero_baseChange_injectiveAction_smul_eq_zero {A B J : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup J] [Module A J] (j : J →ₗ[A] A)
    (hj : Function.Injective j) (hjj : ∀ z w : J, j z * j w = 0) (q : B ⊗[A] J →ₗ[B] B)
    (hq : ∀ (b : B) (z : J), q (b ⊗ₜ[A] z) = b * algebraMap A B (j z)) (z w : B ⊗[A] J) :
    q z • w = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, add_smul, hz, hz', add_zero]
  | tmul b a =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [smul_add, hw, hw', add_zero]
    | tmul c d =>
      have had : j a • d = 0 := by
        apply hj
        rw [map_smul, smul_eq_mul, hjj, map_zero]
      rw [hq, TensorProduct.smul_tmul']
      change ((b * algebraMap A B (j a)) * c) ⊗ₜ[A] d = 0
      rw [show (b * algebraMap A B (j a)) * c = (j a) • (b * c) by
        simp only [Algebra.smul_def]; ring]
      rw [TensorProduct.smul_tmul, had, TensorProduct.tmul_zero]

/-- Injectivity of multiplication by an ideal, read through a linear equivalence realising the
ideal. -/
private theorem idealAction_injective_of_idealEquiv {A : Type u} [CommRing A] {V L : Type u}
    [AddCommGroup V] [Module A V] [AddCommGroup L] [Module A L] (J : Ideal A) (e : L ≃ₗ[A] J)
    (j : L →ₗ[A] A) (hj : ∀ z, j z = (e z : A))
    (hinj : Function.Injective ((TensorProduct.lid A V).toLinearMap.comp (j.rTensor V))) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul A V).comp J.subtype)) := by
  let E := TensorProduct.congr e (LinearEquiv.refl A V)
  have heq : (TensorProduct.lid A V).toLinearMap.comp (j.rTensor V) =
      (TensorProduct.lift ((LinearMap.lsmul A V).comp J.subtype)).comp E.toLinearMap := by
    apply TensorProduct.ext'
    intro z v
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul]
    exact (hj z).symm ▸ rfl
  intro a b hab
  apply E.symm.injective
  apply hinj
  rw [heq]
  change (TensorProduct.lift ((LinearMap.lsmul A V).comp J.subtype)) (E (E.symm a)) =
    (TensorProduct.lift ((LinearMap.lsmul A V).comp J.subtype)) (E (E.symm b))
  simpa only [E.apply_symm_apply] using hab

/-- **Flatness of a quotient from flatness of a base change along a surjection.** If
`R ⟶ S` is surjective and `S ⊗_R M` is flat over `S`, then `M/JM` is flat over `R/J` for
`J = ker(R ⟶ S)`. -/
private theorem flat_quotient_of_flat_tensor_surjective {R S M : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    (hs : Function.Surjective (algebraMap R S)) (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat (R ⧸ RingHom.ker (algebraMap R S))
      (M ⧸ RingHom.ker (algebraMap R S) • (⊤ : Submodule R M)) := by
  let J := RingHom.ker (algebraMap R S)
  let Q := R ⧸ J
  let eR : Q ≃+* S := RingHom.quotientKerEquivOfSurjective hs
  let : Algebra Q S := eR.toRingHom.toAlgebra
  have : IsScalarTower R Q S := IsScalarTower.of_algebraMap_smul (by
    intro a s
    simp only [Algebra.smul_def]
    change eR (Ideal.Quotient.mk J a) * s = (algebraMap R S a) * s
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk])
  let : Module Q (S ⊗[R] M) := Module.compHom _ eR.toRingHom
  have iST : IsScalarTower Q S (S ⊗[R] M) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat Q S :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective eR.bijective)
  have hflatQ : Module.Flat Q (S ⊗[R] M) :=
    @Module.Flat.trans Q S (S ⊗[R] M) _ _ _ _ _ _ iST _ _
  let eS : S ≃ₗ[Q] Q :=
    { eR.symm.toAddEquiv with
      map_smul' := by
        intro a s
        change eR.symm (eR a * s) = a * eR.symm s
        rw [map_mul, eR.symm_apply_apply] }
  let eM : (S ⊗[R] M) ≃ₗ[Q] (M ⧸ J • (⊤ : Submodule R M)) :=
    (TensorProduct.AlgebraTensorModule.congr eS (LinearEquiv.refl R M)).trans
      (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
        (TensorProduct.quotTensorEquivQuotSMul M J))
  exact Module.Flat.of_linearEquiv eM.symm

/-- **A commutative square of surjections of rings whose kernels correspond is a pushout.** -/
private alias ring_isPushout_of_surjective :=
  Stacks.ColimitPresentation.FiniteStage.isPushout_of_surjective

/-- **A commutative square of surjections of rings whose kernels correspond is a pushout.** If
`p : S ⟶ A'` and `π : T ⟶ A` are surjective, `p ≫ a = v ≫ π`, and the kernel of `π` is the
image under `v` of the kernel of `p`, the square is a pushout. -/
alias ring_isPushout_of_surjective_of_ker_eq_map :=
  Stacks.ColimitPresentation.FiniteStage.isPushout_of_surjective

/-- `ring_isPushout_of_surjective` in the language of algebras. -/
private theorem algebra_isPushout_of_surjective_kernel {A B C E : Type u} [CommRing A]
    [CommRing B] [CommRing C] [CommRing E] [Algebra A B] [Algebra A C] [Algebra B E]
    [Algebra C E] [Algebra A E] [IsScalarTower A B E] [IsScalarTower A C E]
    (hc : Function.Surjective (algebraMap A C)) (he : Function.Surjective (algebraMap B E))
    (hker : RingHom.ker (algebraMap B E) = (RingHom.ker (algebraMap A C)).map (algebraMap A B)) :
    Algebra.IsPushout A C B E := by
  apply CommRingCat.isPushout_iff_isPushout.mp
  apply ring_isPushout_of_surjective
    (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (algebraMap C E)) (CommRingCat.ofHom (algebraMap B E))
  · ext z
    exact (IsScalarTower.algebraMap_apply A C E z).symm.trans
      (IsScalarTower.algebraMap_apply A B E z)
  · exact hc
  · exact he
  · exact hker

/-- **Flatness of a quotient from flatness over a pushout.** -/
private theorem flat_quotient_of_flat_pushout {A B C D M : Type u} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D]
    [Algebra A D] [IsScalarTower A B D] [IsScalarTower A C D] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] (hp : Function.Surjective (algebraMap A C))
    (hpo : Algebra.IsPushout A C B D) (hflat : Module.Flat C (D ⊗[B] M)) :
    Module.Flat (A ⧸ RingHom.ker (algebraMap A C))
      (M ⧸ RingHom.ker (algebraMap A C) • (⊤ : Submodule A M)) := by
  have : Algebra.IsPushout A C B D := hpo
  have hflatC : Module.Flat C (C ⊗[A] M) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A C B D M).symm
  exact flat_quotient_of_flat_tensor_surjective hp hflatC

/-- **An ideal receiving a surjection from a base-changed ideal is the extension of it.** -/
private theorem ideal_eq_map_of_surjective_tensor {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (J : Ideal A) (I : Ideal B) (q : (B ⊗[A] J) →ₗ[B] I)
    (hq : Function.Surjective q)
    (hformula : ∀ (b : B) (z : J), (q (b ⊗ₜ[A] z) : B) = b * algebraMap A B z) :
    I = J.map (algebraMap A B) := by
  apply le_antisymm
  · intro b hb
    obtain ⟨w, hw⟩ := hq (⟨b, hb⟩ : I)
    have hmem (w : B ⊗[A] J) : (q w : B) ∈ J.map (algebraMap A B) := by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w z hw hz =>
        rw [map_add, Submodule.coe_add]
        exact Ideal.add_mem _ hw hz
      | tmul c z =>
        rw [hformula]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ z.property)
    simpa [hw] using hmem w
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    have hmem := (q ((1 : B) ⊗ₜ[A] (⟨a, ha⟩ : J))).property
    change (algebraMap A B a) ∈ I
    simpa only [hformula, one_mul] using hmem

/-! ### The three canonical maps -/

section CanonicalMaps

/- The three canonical maps are composites of the tensor bifunctor with the pullback
comparison of `Stacks.RingedSpace.comparisonBifunctorIso`, and reconciling the two spellings is
one `isDefEq` that does not terminate within the heartbeat budget while
`Stacks.SheafOfModules.Tensor.sheafTensor` is transparent: each traversal re-unfolds it and
re-reduces the sheafification underneath. Making the bifunctor opaque here — and only here,
since the section computations above and below need it transparent — lets the two spellings be
matched syntactically. Nothing about the terms produced changes. -/
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor

/-- The canonical ideal map of the square, read on the reduced source and tensored with
`ℱ = i^* ℱ'`: the map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ i^* ℐ ⊗_{𝒪_X} ℱ`. -/
noncomputable def baseToSourceIdealTensor (D : MorphismOfThickenings.{u})
    (F' : SheafOfModules.{u} (structureSheafRing D.X')) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u})).obj (((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ)))).obj (((modulePullback D.i).obj F'))) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u})).obj (((modulePullback D.i).obj D.idealI))).obj (((modulePullback D.i).obj F'))) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u}))).map
    ((D.baseToSourceIdeal, (𝟙 ((modulePullback D.i).obj F'))) : (_, _) ⟶ (_, _)))

/-- The ideal action on the reduced source: the map `i^* ℐ ⊗_{𝒪_X} ℱ ⟶ ℐℱ'` obtained from the
action `ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ'` by the **Stacks 01CD** comparison for `i^*` and the identification
of the ideal multiple with the kernel of the reduction. -/
noncomputable def sourceIdealActionImage (D : MorphismOfThickenings.{u})
    (F' : SheafOfModules.{u} (structureSheafRing D.X')) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u})).obj (((modulePullback D.i).obj D.idealI))).obj (((modulePullback D.i).obj F'))) ⟶
      (modulePullback D.i).obj
        (kernel ((modulePullbackPushforwardAdjunction D.i).unit.app F')) :=
  (Stacks.RingedSpace.comparisonBifunctorIso D.i).inv.app (D.idealI, F') ≫
    (modulePullback D.i).map (Abelian.factorThruImage (idealAction D.i F')) ≫
      (modulePullback D.i).map (idealMultipleIso D.i D.i_isThickening F').1.hom

/-- The canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐℱ'` whose invertibility is the criterion of
**Stacks 08LI**: the reduced canonical ideal map tensored with `ℱ`, followed by the ideal
action. -/
noncomputable def baseToInfinitesimal (D : MorphismOfThickenings.{u})
    (F' : SheafOfModules.{u} (structureSheafRing D.X')) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u})).obj (((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ)))).obj (((modulePullback D.i).obj F'))) ⟶
      (modulePullback D.i).obj
        (kernel ((modulePullbackPushforwardAdjunction D.i).unit.app F')) :=
  baseToSourceIdealTensor D F' ≫ sourceIdealActionImage D F'

/-- For a strict square the reduced canonical ideal map stays epimorphic after tensoring. -/
private theorem baseToSourceIdealTensor_epi (D : MorphismOfThickenings.{u})
    (hs : D.IsStrict) (F' : SheafOfModules.{u} (structureSheafRing D.X')) :
    Epi (baseToSourceIdealTensor D F') :=
  @AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi D.X _ _
    ((modulePullback D.i).obj F') D.baseToSourceIdeal (D.epi_baseToSourceIdeal hs)

/-- The ideal action on the reduced source is an epimorphism: each of its three factors is. -/
private theorem sourceIdealActionImage_epi (D : MorphismOfThickenings.{u})
    (F' : SheafOfModules.{u} (structureSheafRing D.X')) :
    Epi (sourceIdealActionImage D F') := by
  let p := Abelian.factorThruImage (idealAction D.i F')
  have hp : Epi p := Abelian.instEpiFactorThruImage (idealAction D.i F')
  let a := (Stacks.RingedSpace.comparisonBifunctorIso D.i).inv.app (D.idealI, F')
  let b := (modulePullback D.i).map p
  let c := (modulePullback D.i).map (idealMultipleIso D.i D.i_isThickening F').1.hom
  have ha : Epi a := ((isIso_iff_mono_and_epi _).mp
    (NatIso.isIso_app_of_isIso (Stacks.RingedSpace.comparisonBifunctorIso D.i).inv _)).2
  have hb : Epi b :=
    @Functor.map_epi _ _ _ _ (modulePullback D.i)
      (Functor.preservesEpimorphisms_of_adjunction
        (modulePullbackPushforwardAdjunction D.i)) _ _ p hp
  have hc : Epi c := ((isIso_iff_mono_and_epi _).mp
    ((modulePullback D.i).mapIso (idealMultipleIso D.i D.i_isThickening F').1).isIso_hom).2
  unfold sourceIdealActionImage
  change Epi (a ≫ b ≫ c)
  exact @epi_comp _ _ _ _ _ (a ≫ b) (@epi_comp _ _ _ _ _ a ha b hb) c hc

/-- The criterion of **Stacks 08LI** transported to the ambient source: `baseToInfinitesimal` is
invertible exactly when `i^*` of the ideal action, factored through its image, is. -/
private theorem baseToInfinitesimal_isIso_iff_pullback_imageMap_isIso
    (D : MorphismOfThickenings.{u}) (M : SheafOfModules.{u} (structureSheafRing D.X')) :
    IsIso (baseToInfinitesimal D M) ↔
      IsIso ((modulePullback D.i).map (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u}))).map ((D.idealMap.1, (𝟙 M)) : (_, _) ⟶ (_, _))) ≫
        Abelian.factorThruImage (idealAction D.i M))) :=
  isIso_tensor_pullback_map_iff (modulePullback D.i) _ _
    (Stacks.RingedSpace.comparisonBifunctorIso D.i) D.reducedPullbackComparison.symm
    D.idealMap.1 (Abelian.factorThruImage (idealAction D.i M))
    ((modulePullback D.i).mapIso (idealMultipleIso D.i D.i_isThickening M).1)

/-- `MorphismOfThickenings.ambientIdealMap` written with the better-typed transpose
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` of the structure-sheaf map. -/
private theorem ambientIdealMap_eq (D : MorphismOfThickenings.{u}) :
    D.ambientIdealMap =
      (modulePullback D.f').map (idealSheafι D.t) ≫ modulePullbackUnitToUnit D.f' :=
  rfl

/-- Factoring the ideal action through the image of the canonical ideal map: the composite
`(f')^* 𝒥 ⊗ ℱ' ⟶ ℐ ⊗ ℱ' ⟶ ℐℱ'` is monomorphic exactly when the action of `(f')^* 𝒥` is. -/
private theorem mono_imageMap_iff_mono_ambientIdealAction (D : MorphismOfThickenings.{u})
    (M : SheafOfModules.{u} (structureSheafRing D.X')) :
    Mono (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u}))).map ((D.idealMap.1, (𝟙 M)) : (_, _) ⟶ (_, _))) ≫
        Abelian.factorThruImage (idealAction D.i M)) ↔
      Mono (idealTensorMultiplication D.X' D.ambientIdealMap M) := by
  have heq : (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u}))).map
        ((D.idealMap.1, (𝟙 M)) : (_, _) ⟶ (_, _))) ≫
        Abelian.factorThruImage (idealAction D.i M)) ≫ Abelian.image.ι (idealAction D.i M) =
      idealTensorMultiplication D.X' D.ambientIdealMap M := by
    rw [Category.assoc, Abelian.image.fac,
      idealTensorMultiplication_naturality_left D.X' D.idealMap.1 (idealSheafι D.i) M,
      D.idealMap.2]
  have hcongr := congrArg Mono heq
  constructor
  · intro h
    exact hcongr.mp (@mono_comp _ _ _ _ _ _ h _ inferInstance)
  · intro h
    have := hcongr.mpr h
    exact mono_of_mono _ (Abelian.image.ι (idealAction D.i M))

end CanonicalMaps

/-- For a strict square the tensored ideal map followed by the factorisation of the ideal action
through its image is an epimorphism. -/
private theorem epi_idealMap_tensor_comp_factorThruImage (D : MorphismOfThickenings.{u})
    (hs : D.IsStrict) (M : SheafOfModules.{u} (structureSheafRing D.X')) :
    Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u}))).map
        ((D.idealMap.1, (𝟙 M)) : (_, _) ⟶ (_, _))) ≫
      Abelian.factorThruImage (idealAction D.i M)) :=
  @epi_comp _ _ _ _ _ _
    (@AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi D.X' _ _ M D.idealMap.1 hs) _
    (Abelian.instEpiFactorThruImage (idealAction D.i M))

/-- **If the ideal acts as zero on a module then the reduction of that module is injective.**
The reduction is a cokernel of the action, so the short complex formed by the action and the
reduction is exact; with a zero action, exactness is injectivity of the reduction. -/
private theorem mono_reduction_unit_of_idealAction_eq_zero {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsThickening f) (M : SheafOfModules.{u} (structureSheafRing Y))
    (hM : idealAction f M = 0) :
    Mono ((modulePullbackPushforwardAdjunction f).unit.app M) :=
  ((ShortComplex.mk (idealAction f M) (moduleReductionMap f M)
    (idealAction_comp_moduleReductionMap_eq_zero f hf M)).exact_iff_mono hM).mp
      (exact_idealAction_moduleReductionMap f hf M)

/-- The criterion of **Stacks 08LI** as a monomorphism condition on the ambient ideal action,
given that the reduction is injective on the relevant tensor product. -/
private theorem baseToInfinitesimal_isIso_iff_ambientIdealAction_mono
    (D : MorphismOfThickenings.{u}) (hs : D.IsStrict)
    (M : SheafOfModules.{u} (structureSheafRing D.X'))
    (hunit : Mono ((modulePullbackPushforwardAdjunction D.i).unit.app
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (M))))) :
    IsIso (baseToInfinitesimal D M) ↔
      Mono (idealTensorMultiplication D.X' D.ambientIdealMap M) := by
  have hepi := epi_idealMap_tensor_comp_factorThruImage D hs M
  exact (baseToInfinitesimal_isIso_iff_pullback_imageMap_isIso D M).trans
    ((isIso_map_iff_of_epi_of_mono_unit (modulePullbackPushforwardAdjunction D.i) _
        hepi hunit).trans
      ((isIso_iff_mono_and_epi _).trans
        ((and_iff_left hepi).trans (mono_imageMap_iff_mono_ambientIdealAction D M))))

/-- **Flatness makes the action of a pulled-back ideal injective.** If `ℳ` is flat over `Y` then
the action of `f^* 𝒥` on `ℳ` is a monomorphism: on stalks it is the base change of the
multiplication map of `𝒥`, which flatness makes injective. -/
private theorem pullbackIdealAction_mono_of_isFlatOver {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (J : SheafOfModules.{u} (structureSheafRing Y)) (j : J ⟶ SheafOfModules.unit (structureSheafRing Y)) [Mono j]
    (M : SheafOfModules.{u} (structureSheafRing X)) (hM : AlgebraicGeometry.IsFlatOver f M) :
    Mono (idealTensorMultiplication X
      ((modulePullback f).map j ≫ modulePullbackUnitToUnit f) M) := by
  let P : SheafOfModules.{u} (structureSheafRing X) := (modulePullback f).obj J
  let a := (modulePullback f).map j ≫ modulePullbackUnitToUnit f
  apply (mono_iff_stalk_injective X _ _ _).mpr
  intro x
  let A := Y.presheaf.stalk (f.hom.base x)
  let B := X.presheaf.stalk x
  let N := grpStalk X M.val x
  let L := grpStalk Y J.val (f.hom.base x)
  let _iAlg : Algebra A B := (f.hom.stalkMap x).hom.toAlgebra
  let _iM := stalkModule X M.val x
  let _iP := stalkModule X P.val x
  let _iJ := stalkModule Y J.val (f.hom.base x)
  let _iAN : Module A N := Module.compHom _ (f.hom.stalkMap x).hom
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat A N := (flat_stalkModule_iff_isFlatOverAt f M x).mpr (hM x)
  let jA : L →ₗ[A] A := (unitStalkLinearEquiv Y (f.hom.base x)).toLinearMap.comp
    (stalkMapL Y J.val (SheafOfModules.unit (structureSheafRing Y)).val j.val (f.hom.base x))
  have hjA : Function.Injective jA := (unitStalkLinearEquiv Y (f.hom.base x)).injective.comp
    ((mono_iff_stalk_injective Y _ _ j).mp inferInstance (f.hom.base x))
  let q := (unitStalkLinearEquiv X x).toLinearMap.comp
    (stalkMapL X P.val (SheafOfModules.unit (structureSheafRing X)).val a.val x)
  obtain ⟨e, he⟩ := pullbackIdeal_stalk_formula f J j x
  let q' : B ⊗[A] L →ₗ[B] B := q.comp e.symm.toLinearMap
  have hq' : ∀ (b : B) (z : L), q' (b ⊗ₜ[A] z) = b * algebraMap A B (jA z) := he
  have hflat := (TensorProduct.lid A N).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := N) jA hjA)
  have hinj := (baseChange_idealAction_injective_iff (M := N) jA q' hq').mpr hflat
  have hinj' := (lid_rTensor_comp_injective_iff (V := N) e q q'
    fun p => (congrArg q (e.symm_apply_apply p)).symm).mpr hinj
  let P' : SheafOfModules.{u} (structureSheafRing X) := (modulePullback f).obj J
  let M' : SheafOfModules.{u} (structureSheafRing X) := M
  let a' : P' ⟶ SheafOfModules.unit (structureSheafRing X) :=
    (modulePullback f).map j ≫ modulePullbackUnitToUnit f
  change Function.Injective (stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (P')).obj (M'))).val M'.val
    (idealTensorMultiplication X a' M').val x)
  rw [idealTensorMultiplication_stalk_formula]
  exact hinj'.comp (tensorStalkIso X x P' M').injective

/-- **Flatness implies the criterion.** For a strict square and a module flat over `S'`, the
canonical map `f^* 𝒥 ⊗ ℱ ⟶ ℐℱ'` is an isomorphism. -/
private theorem baseToInfinitesimal_isIso_of_isFlatOver (D : MorphismOfThickenings.{u})
    (hs : D.IsStrict) (M : SheafOfModules.{u} (structureSheafRing D.X'))
    (hM : AlgebraicGeometry.IsFlatOver D.f' M) :
    IsIso (baseToInfinitesimal D M) := by
  refine (baseToInfinitesimal_isIso_iff_pullback_imageMap_isIso D M).mpr ?_
  have hepi := epi_idealMap_tensor_comp_factorThruImage D hs M
  have hmono := (mono_imageMap_iff_mono_ambientIdealAction D M).mpr (by
    rw [ambientIdealMap_eq]
    exact pullbackIdealAction_mono_of_isFlatOver D.f' D.idealJ (idealSheafι D.t) M hM)
  have := @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi
  infer_instance

/-- **The ideal of a first-order thickening acts as zero on a tensor product with its own
pullback.** On stalks the ideal acts through a square-zero ideal of the base, so its action on
the base change is zero, hence so is its action after tensoring. -/
private theorem pullbackIdeal_tensorAction_eq_zero {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (t : Z ⟶ Y) (ht : IsFirstOrderThickening t) (M : SheafOfModules.{u} (structureSheafRing X)) :
    idealTensorMultiplication X
        ((modulePullback f).map (idealSheafι t) ≫ modulePullbackUnitToUnit f)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (((modulePullback f).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)))).obj (M))) = 0 := by
  let J : SheafOfModules.{u} (structureSheafRing Y) := AlgebraicGeometry.SheafOfModules.idealSheaf t
  let j : J ⟶ SheafOfModules.unit (structureSheafRing Y) := idealSheafι t
  let P : SheafOfModules.{u} (structureSheafRing X) := (modulePullback f).obj J
  let q : P ⟶ SheafOfModules.unit (structureSheafRing X) :=
    (modulePullback f).map j ≫ modulePullbackUnitToUnit f
  let N : SheafOfModules.{u} (structureSheafRing X) := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (P)).obj (M))
  apply hom_eq_zero_of_stalkMap_eq_zero X
  intro x
  let A := Y.presheaf.stalk (f.hom.base x)
  let B := X.presheaf.stalk x
  let K := grpStalk Y J.val (f.hom.base x)
  let Q := grpStalk X P.val x
  let V := grpStalk X M.val x
  let _iAlg : Algebra A B := (f.hom.stalkMap x).hom.toAlgebra
  let _iJ := stalkModule Y J.val (f.hom.base x)
  let _iP := stalkModule X P.val x
  let _iM := stalkModule X M.val x
  let _iN := stalkModule X N.val x
  let jA : K →ₗ[A] A := (unitStalkLinearEquiv Y (f.hom.base x)).toLinearMap.comp
    (stalkMapL Y J.val (SheafOfModules.unit (structureSheafRing Y)).val j.val (f.hom.base x))
  have hjA : Function.Injective jA := (unitStalkLinearEquiv Y (f.hom.base x)).injective.comp
    ((mono_iff_stalk_injective Y _ _ j).mp inferInstance (f.hom.base x))
  obtain ⟨K₀, hK₀, e₀, he₀⟩ := firstOrder_stalkIdeal t ht (f.hom.base x)
  have hsq : ∀ z w : K, jA z * jA w = 0 := by
    intro z w
    have hmem := Ideal.mul_mem_mul (e₀ z).property (e₀ w).property
    rw [← pow_two, hK₀] at hmem
    change (e₀ z).val * (e₀ w).val = 0 at hmem
    have hje (v : K) : jA v = (e₀ v).val := (he₀ v).symm
    simpa only [hje] using hmem
  let qB : Q →ₗ[B] B := (unitStalkLinearEquiv X x).toLinearMap.comp
    (stalkMapL X P.val (SheafOfModules.unit (structureSheafRing X)).val q.val x)
  obtain ⟨e, he⟩ := pullbackIdeal_stalk_formula f J j x
  let q' : B ⊗[A] K →ₗ[B] B := qB.comp e.symm.toLinearMap
  have hq' : ∀ b z, q' (b ⊗ₜ[A] z) = b * algebraMap A B (jA z) := he
  have hsq' := squareZero_baseChange_injectiveAction_smul_eq_zero jA hjA hsq q' hq'
  have hq_smul (a b : Q) : qB a • b = 0 := by
    apply e.injective
    rw [map_smul, map_zero]
    rw [show qB a = q' (e a) by
      change qB a = qB (e.symm (e a))
      rw [e.symm_apply_apply]]
    exact hsq' (e a) (e b)
  have hq_tensor (a : Q) (z : Q ⊗[B] V) : qB a • z = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [smul_add, hz, hw, add_zero]
    | tmul b v => rw [TensorProduct.smul_tmul', hq_smul a b, TensorProduct.zero_tmul]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let P' : SheafOfModules.{u} (structureSheafRing X) := (modulePullback f).obj J
  let N' : SheafOfModules.{u} (structureSheafRing X) := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (P)).obj (M))
  let q' : P' ⟶ SheafOfModules.unit (structureSheafRing X) :=
    (modulePullback f).map j ≫ modulePullbackUnitToUnit f
  change (stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (P')).obj (N'))).val N'.val
    (idealTensorMultiplication X q' N').val x) z = 0
  rw [idealTensorMultiplication_stalk_formula]
  let eN := tensorStalkIso X x P' N'
  let eM := tensorStalkIso X x P' M
  change (TensorProduct.lid B _) (qB.rTensor _ (eN z)) = 0
  induction eN z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul a n =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    apply eM.injective
    rw [map_smul, map_zero]
    exact hq_tensor a (eM n)

/-- **The source ideal acts as zero on `(f')^* 𝒥 ⊗ ℱ'`.** For a strict square the canonical
ideal map is epimorphic, so the action of `ℐ` is cancelled by the action of `(f')^* 𝒥`, which is
zero by `pullbackIdeal_tensorAction_eq_zero`. -/
private theorem sourceIdeal_action_on_baseIdealTensor_eq_zero (D : MorphismOfThickenings.{u})
    (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (M : SheafOfModules.{u} (structureSheafRing D.X')) :
    idealAction D.i ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (M))) = 0 := by
  let PJ : SheafOfModules.{u} (structureSheafRing D.X') := (modulePullback D.f').obj D.idealJ
  let II : SheafOfModules.{u} (structureSheafRing D.X') := D.idealI
  let jI : II ⟶ SheafOfModules.unit (structureSheafRing D.X') := idealSheafι D.i
  let aI : PJ ⟶ II := D.idealMap.1
  have key : ∀ N : SheafOfModules.{u} (structureSheafRing D.X'),
      idealTensorMultiplication D.X' (aI ≫ jI) N = 0 →
      idealTensorMultiplication D.X' jI N = 0 := by
    intro N hzero
    have hepi : Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u}))).map ((aI, (𝟙 N)) : (_, _) ⟶ (_, _)))) :=
      @AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi D.X' _ _ N aI hs
    refine (@cancel_epi _ _ _ _ _ _ hepi _ _).1 ?_
    rw [comp_zero, idealTensorMultiplication_naturality_left]
    exact hzero
  refine key ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (M))) ?_
  have hmap : idealTensorMultiplication D.X' (aI ≫ jI)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (M))) =
      idealTensorMultiplication D.X' D.ambientIdealMap
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (M))) :=
    congrArg (fun z => idealTensorMultiplication D.X' z
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (M)))) D.idealMap.2
  rw [hmap, ambientIdealMap_eq]
  exact pullbackIdeal_tensorAction_eq_zero D.f' D.t ht M

/-- **The ambient ideal action on stalks.** If the action of `(f')^* 𝒥` on `ℱ'` is a
monomorphism, then on every stalk the multiplication map `𝒥_{f'(x)} ⊗ ℱ'_x ⟶ ℱ'_x` is
injective. -/
private theorem ambientIdealAction_stalk_injective (D : MorphismOfThickenings.{u})
    (M : SheafOfModules.{u} (structureSheafRing D.X'))
    (hmono : Mono (idealTensorMultiplication D.X' D.ambientIdealMap M)) (x : D.X') :
    letI : Algebra (D.S'.presheaf.stalk (D.f'.hom.base x)) (D.X'.presheaf.stalk x) :=
      (D.f'.hom.stalkMap x).hom.toAlgebra
    letI := stalkModule D.S' D.idealJ.val (D.f'.hom.base x)
    letI := stalkModule D.X' M.val x
    letI : Module (D.S'.presheaf.stalk (D.f'.hom.base x)) (grpStalk D.X' M.val x) :=
      Module.compHom _ (D.f'.hom.stalkMap x).hom
    Function.Injective ((TensorProduct.lid (D.S'.presheaf.stalk (D.f'.hom.base x))
        (grpStalk D.X' M.val x)).toLinearMap.comp
      (((unitStalkLinearEquiv D.S' (D.f'.hom.base x)).toLinearMap.comp
        (stalkMapL D.S' D.idealJ.val (SheafOfModules.unit (structureSheafRing D.S')).val
          (idealSheafι D.t).val (D.f'.hom.base x))).rTensor (grpStalk D.X' M.val x))) := by
  let A := D.S'.presheaf.stalk (D.f'.hom.base x)
  let B := D.X'.presheaf.stalk x
  let V := grpStalk D.X' M.val x
  let P : SheafOfModules.{u} (structureSheafRing D.X') := (modulePullback D.f').obj D.idealJ
  let P' : SheafOfModules.{u} (structureSheafRing D.X') := (modulePullback D.f').obj D.idealJ
  let M' : SheafOfModules.{u} (structureSheafRing D.X') := M
  let q'' : P' ⟶ SheafOfModules.unit (structureSheafRing D.X') :=
    (modulePullback D.f').map (idealSheafι D.t) ≫ modulePullbackUnitToUnit D.f'
  let _iAlg : Algebra A B := (D.f'.hom.stalkMap x).hom.toAlgebra
  let _iJ := stalkModule D.S' D.idealJ.val (D.f'.hom.base x)
  let _iM := stalkModule D.X' M.val x
  let _iP := stalkModule D.X' P.val x
  let _iAV : Module A V := Module.compHom _ (D.f'.hom.stalkMap x).hom
  have : IsScalarTower A B V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let j : grpStalk D.S' D.idealJ.val (D.f'.hom.base x) →ₗ[A] A :=
    (unitStalkLinearEquiv D.S' (D.f'.hom.base x)).toLinearMap.comp
      (stalkMapL D.S' D.idealJ.val (SheafOfModules.unit (structureSheafRing D.S')).val
        (idealSheafι D.t).val (D.f'.hom.base x))
  let q : grpStalk D.X' P.val x →ₗ[B] B := (unitStalkLinearEquiv D.X' x).toLinearMap.comp
    (stalkMapL D.X' P.val (SheafOfModules.unit (structureSheafRing D.X')).val
      ((modulePullback D.f').map (idealSheafι D.t) ≫ modulePullbackUnitToUnit D.f').val x)
  obtain ⟨e, he⟩ := pullbackIdeal_stalk_formula D.f' D.idealJ (idealSheafι D.t) x
  let q' : B ⊗[A] grpStalk D.S' D.idealJ.val (D.f'.hom.base x) →ₗ[B] B :=
    q.comp e.symm.toLinearMap
  have hq' : ∀ b z, q' (b ⊗ₜ[A] z) = b * algebraMap A B (j z) := he
  have hi : Function.Injective ((TensorProduct.lid B V).toLinearMap.comp (q.rTensor V)) := by
    have hm := (mono_iff_stalk_injective D.X' _ _ _).mp
      (ambientIdealMap_eq D ▸ hmono) x
    change Function.Injective (stalkMapL D.X' ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (P')).obj (M'))).val M'.val
      (idealTensorMultiplication D.X' q'' M').val x) at hm
    rw [idealTensorMultiplication_stalk_formula] at hm
    exact (Function.Injective.of_comp_iff' _ (tensorStalkIso D.X' x P M).bijective).mp hm
  exact (baseChange_idealAction_injective_iff j q' hq').mp
    ((lid_rTensor_comp_injective_iff (V := V) e q q'
      fun p => (congrArg q (e.symm_apply_apply p)).symm).mp hi)

/-- **Strictness on stalks.** For a strict square the stalk of `ℐ` is the extension of the stalk
of `𝒥` along the stalk map of `f'`: the canonical ideal map is epimorphic, hence surjective on
stalks, and the base-changed multiplication map computes its image. -/
private theorem strict_stalkIdeal_eq_map (D : MorphismOfThickenings.{u}) (hs : D.IsStrict)
    (y : D.X') (I : Ideal (D.X'.presheaf.stalk y))
    (eI : letI := stalkModule D.X' D.idealI.val y
      grpStalk D.X' D.idealI.val y ≃ₗ[D.X'.presheaf.stalk y] I)
    (heI : ∀ z, (eI z).val = unitStalkLinearEquiv D.X' y
      (((stalkAddCommGroupFunctor (structureSheafRing D.X') y).map (idealSheafι D.i)).hom z))
    (J : Ideal (D.S'.presheaf.stalk (D.f'.hom.base y)))
    (eJ : letI := stalkModule D.S' D.idealJ.val (D.f'.hom.base y)
      grpStalk D.S' D.idealJ.val (D.f'.hom.base y)
        ≃ₗ[D.S'.presheaf.stalk (D.f'.hom.base y)] J)
    (heJ : ∀ z, (eJ z).val = unitStalkLinearEquiv D.S' (D.f'.hom.base y)
      (((stalkAddCommGroupFunctor (structureSheafRing D.S') (D.f'.hom.base y)).map
        (idealSheafι D.t)).hom z)) :
    I = J.map (D.f'.hom.stalkMap y).hom := by
  let A := D.S'.presheaf.stalk (D.f'.hom.base y)
  let B := D.X'.presheaf.stalk y
  let P : SheafOfModules.{u} (structureSheafRing D.X') := (modulePullback D.f').obj D.idealJ
  let T := stalkAddCommGroupFunctor (structureSheafRing D.X') y
  let a := D.idealMap.1
  let _iAlg : Algebra A B := (D.f'.hom.stalkMap y).hom.toAlgebra
  let _iJ := stalkModule D.S' D.idealJ.val (D.f'.hom.base y)
  let _iP := stalkModule D.X' P.val y
  let _iI := stalkModule D.X' D.idealI.val y
  have ha : Function.Surjective (T.map a).hom :=
    (epi_iff_stalk_surjective D.X' _ _ a).mp hs y
  obtain ⟨eP, heP⟩ := pullbackIdeal_stalk_formula D.f' D.idealJ (idealSheafι D.t) y
  let c : (B ⊗[A] J) ≃ₗ[B] (B ⊗[A] grpStalk D.S' D.idealJ.val (D.f'.hom.base y)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) eJ.symm
  let q : (B ⊗[A] J) →ₗ[B] I :=
    eI.toLinearMap.comp ((stalkMapL D.X' P.val D.idealI.val a.val y).comp
      (eP.symm.toLinearMap.comp c.toLinearMap))
  have hq : Function.Surjective q :=
    eI.surjective.comp (ha.comp (eP.symm.surjective.comp c.surjective))
  have hformula (b : B) (z : J) : (q (b ⊗ₜ[A] z) : B) = b * algebraMap A B z := by
    have hc (p : grpStalk D.X' P.val y) : (eI ((T.map a).hom p)).val =
        unitStalkLinearEquiv D.X' y
          ((T.map ((modulePullback D.f').map (idealSheafι D.t) ≫
            modulePullbackUnitToUnit D.f')).hom p) := by
      refine Eq.trans (heI ((T.map a).hom p)) ?_
      have hcomp := D.idealMap.2
      change a ≫ idealSheafι D.i = D.ambientIdealMap at hcomp
      rw [← ambientIdealMap_eq, ← hcomp, Functor.map_comp]
      rfl
    change (eI ((T.map a).hom (eP.symm (c (b ⊗ₜ[A] z))))).val = _
    rw [hc]
    simp only [c, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
    have hP := heP b (eJ.symm z)
    change (unitStalkLinearEquiv D.X' y)
      ((T.map ((modulePullback D.f').map (idealSheafι D.t) ≫
        modulePullbackUnitToUnit D.f')).hom (eP.symm (b ⊗ₜ[A] eJ.symm z))) = _ at hP
    rw [← heJ, eJ.apply_symm_apply] at hP
    exact hP
  exact ideal_eq_map_of_surjective_tensor J I q hq hformula

/-- **A strict morphism of first order thickenings, read on stalks, in terms of chosen ideals.**
With `I` and `J` realising the stalks of the ideals of `i` and `t`, the stalk map `p` of `t` is
surjective with kernel `J`, the stalk map of `i` is surjective, and its kernel is `J` extended. -/
private theorem strict_stalkMap_facts (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (x : D.X)
    (hpt : D.f'.hom.base (D.i.hom.base x) = D.t.hom.base (D.f.hom.base x))
    (I : Ideal (D.X'.presheaf.stalk (D.i.hom.base x)))
    (eI : letI := stalkModule D.X' D.idealI.val (D.i.hom.base x)
      grpStalk D.X' D.idealI.val (D.i.hom.base x)
        ≃ₗ[D.X'.presheaf.stalk (D.i.hom.base x)] I)
    (heI : ∀ z, (eI z).val = unitStalkLinearEquiv D.X' (D.i.hom.base x)
      (((stalkAddCommGroupFunctor (structureSheafRing D.X') (D.i.hom.base x)).map
        (idealSheafι D.i)).hom z))
    (J : Ideal (D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x))))
    (eJ : letI := stalkModule D.S' D.idealJ.val (D.f'.hom.base (D.i.hom.base x))
      grpStalk D.S' D.idealJ.val (D.f'.hom.base (D.i.hom.base x))
        ≃ₗ[D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x))] J)
    (heJ : ∀ z, (eJ z).val = unitStalkLinearEquiv D.S' (D.f'.hom.base (D.i.hom.base x))
      (((stalkAddCommGroupFunctor (structureSheafRing D.S') (D.f'.hom.base (D.i.hom.base x))).map
        (idealSheafι D.t)).hom z)) :
    Function.Surjective (eqToHom (congrArg D.S'.presheaf.stalk hpt) ≫
        D.t.hom.stalkMap (D.f.hom.base x)).hom ∧
      J = RingHom.ker (eqToHom (congrArg D.S'.presheaf.stalk hpt) ≫
        D.t.hom.stalkMap (D.f.hom.base x)).hom ∧
      Function.Surjective (D.i.hom.stalkMap x).hom ∧
      RingHom.ker (D.i.hom.stalkMap x).hom =
        (RingHom.ker (eqToHom (congrArg D.S'.presheaf.stalk hpt) ≫
          D.t.hom.stalkMap (D.f.hom.base x)).hom).map (D.f'.hom.stalkMap (D.i.hom.base x)).hom := by
  have : IsIso D.t.hom.base := ht.1.1
  have : IsIso D.i.hom.base := hi.1.1
  have hJker := stalkIdeal_eq_stalkMap_ker_of_base_eq D.t D.t_isThickening (D.f.hom.base x) _
    hpt.symm J eJ heJ
  have hJp := hJker.trans (stalk_ker_transport D.S' hpt (D.t.hom.stalkMap (D.f.hom.base x))).symm
  refine ⟨(stalkIdeal_exact D.t D.t_isThickening.2.1 (D.f.hom.base x)).2.comp
    (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg D.S'.presheaf.stalk hpt))).2, hJp,
    (stalkIdeal_exact D.i D.i_isThickening.2.1 x).2, ?_⟩
  rw [← stalkIdeal_eq_stalkMap_ker D.i D.i_isThickening x I eI heI, ← hJp]
  exact strict_stalkIdeal_eq_map D hs (D.i.hom.base x) I eI heI J eJ heJ

/-! ### The criterion -/

/-- **Stacks Project, Tag 08LI.** For a strict morphism of first-order thickenings of ringed
spaces and an `𝒪_{X'}`-module `ℱ'` whose restriction `ℱ = i^* ℱ'` is flat over `S`, the module
`ℱ'` is flat over `S'` if and only if the canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐℱ'` is an
isomorphism.

One direction is `baseToInfinitesimal_isIso_of_isFlatOver`: flatness makes the ideal action
injective, and the map in question is `i^*` of an epimorphism which that injectivity turns into
an isomorphism. For the other, invertibility makes the action of `(f')^* 𝒥` on `ℱ'` a
monomorphism, hence injective on every stalk after base change; the flatness of `ℱ` over `S`
supplies the quotient hypothesis of the square-zero local criterion, and strictness is what
identifies the relevant quotient of `𝒪_{X',x}` with `𝒪_{X,x}`. -/
@[stacks 08LI "flatness criterion", sga "3 XV 2.7" "more general"]
theorem isFlatOver_iff_baseToInfinitesimal_isIso (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF : AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj F')) :
    AlgebraicGeometry.IsFlatOver D.f' F' ↔ IsIso (baseToInfinitesimal D F') := by
  constructor
  · exact baseToInfinitesimal_isIso_of_isFlatOver D hs F'
  · intro h
    let N := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj (((modulePullback D.f').obj D.idealJ))).obj (F'))
    have hzero := sourceIdeal_action_on_baseIdealTensor_eq_zero D ht hs F'
    have hunit : Mono ((modulePullbackPushforwardAdjunction D.i).unit.app N) :=
      mono_reduction_unit_of_idealAction_eq_zero D.i D.i_isThickening N hzero
    have hmono : Mono (idealTensorMultiplication D.X' D.ambientIdealMap F') :=
      (baseToInfinitesimal_isIso_iff_ambientIdealAction_mono D hs F' hunit).mp h
    intro y
    let A := D.S'.presheaf.stalk (D.f'.hom.base y)
    let V := grpStalk D.X' F'.val y
    let L := grpStalk D.S' D.idealJ.val (D.f'.hom.base y)
    let _iJ := stalkModule D.S' D.idealJ.val (D.f'.hom.base y)
    let _iV := stalkModule D.X' F'.val y
    let _iAV : Module A V := Module.compHom _ (D.f'.hom.stalkMap y).hom
    let j : L →ₗ[A] A := (unitStalkLinearEquiv D.S' (D.f'.hom.base y)).toLinearMap.comp
      (stalkMapL D.S' D.idealJ.val (SheafOfModules.unit (structureSheafRing D.S')).val
        (idealSheafι D.t).val (D.f'.hom.base y))
    obtain ⟨J, hJ, eJ, heJ⟩ := firstOrder_stalkIdeal D.t ht (D.f'.hom.base y)
    obtain ⟨I, hI, eI, heI⟩ := firstOrder_stalkIdeal D.i hi y
    have hj (z : L) : j z = (eJ z : A) := (heJ z).symm
    have hinj : Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A V).comp J.subtype)) :=
      idealAction_injective_of_idealEquiv J eJ j hj
        (ambientIdealAction_stalk_injective D F' hmono y)
    have hquot : Module.Flat (A ⧸ J) (V ⧸ J • (⊤ : Submodule A V)) := by
      have : IsIso D.i.hom.base := hi.1.1
      obtain ⟨x, rfl⟩ := (TopCat.homeoOfIso (asIso D.i.hom.base)).surjective y
      have hFx := hF x
      let C := D.S.presheaf.stalk (D.f.hom.base x)
      let E := D.X.presheaf.stalk x
      let N' := grpStalk D.X ((modulePullback D.i).obj F').val x
      let _iN' := stalkModule D.X ((modulePullback D.i).obj F').val x
      let _iCN : Module C N' := Module.compHom _ (D.f.hom.stalkMap x).hom
      have hflatN : Module.Flat C N' :=
        (flat_stalkModule_iff_isFlatOverAt D.f ((modulePullback D.i).obj F') x).mpr hFx
      have hcomm : D.f'.hom.base (D.i.hom.base x) = D.t.hom.base (D.f.hom.base x) := by
        have h := congrArg (fun g : D.X ⟶ D.S' => g.hom.base x) D.comm
        simpa using h
      obtain ⟨hp, hJp, hsurjSource, hker⟩ :=
        strict_stalkMap_facts D hi ht hs x hcomm I eI heI J eJ heJ
      let p : A →+* C :=
        (eqToHom (congrArg D.S'.presheaf.stalk hcomm) ≫ D.t.hom.stalkMap (D.f.hom.base x)).hom
      let B := D.X'.presheaf.stalk (D.i.hom.base x)
      let _iAB : Algebra A B := (D.f'.hom.stalkMap (D.i.hom.base x)).hom.toAlgebra
      let _iAC : Algebra A C := p.toAlgebra
      let _iBE : Algebra B E := (D.i.hom.stalkMap x).hom.toAlgebra
      let _iCE : Algebra C E := (D.f.hom.stalkMap x).hom.toAlgebra
      let _iAE : Algebra A E :=
        ((D.i.hom.stalkMap x).hom.comp (D.f'.hom.stalkMap (D.i.hom.base x)).hom).toAlgebra
      have : IsScalarTower A B E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have : IsScalarTower A C E := by
        apply IsScalarTower.of_algebraMap_smul
        intro a z
        have hc := PresheafedSpace.stalkMap.congr_hom (D.i ≫ D.f').hom (D.f ≫ D.t).hom
          (congrArg (fun g : D.X ⟶ D.S' => g.hom) D.comm) x
        change (D.i.hom ≫ D.f'.hom).stalkMap x =
          eqToHom _ ≫ (D.f.hom ≫ D.t.hom).stalkMap x at hc
        rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at hc
        have hc' := congrArg CommRingCat.Hom.hom hc
        exact congrArg (fun b => b * z) (congrArg (fun g : A →+* E => g a) hc').symm
      let _iBV : Module B V := stalkModule D.X' F'.val (D.i.hom.base x)
      have : IsScalarTower A B V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have : IsScalarTower C E N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have hpo : Algebra.IsPushout A C B E :=
        algebra_isPushout_of_surjective_kernel hp hsurjSource hker
      obtain ⟨e, he⟩ := pullback_stalk_formula D.i F' x
      have hflatTensor : Module.Flat C (E ⊗[B] V) :=
        Module.Flat.of_linearEquiv (e.restrictScalars C).symm
      have hq := flat_quotient_of_flat_pushout hp hpo hflatTensor
      change Module.Flat (A ⧸ RingHom.ker p) (V ⧸ RingHom.ker p • (⊤ : Submodule A V)) at hq
      rwa [show RingHom.ker p = J from hJp.symm] at hq
    have hflat : Module.Flat A V :=
      (flat_iff_squareZero_idealAction_injective J hJ hquot).mpr hinj
    exact (flat_stalkModule_iff_isFlatOverAt D.f' F' y).mp hflat

/-- **Stacks Project, Tag 08LI.** Under the hypotheses of the criterion and flatness of `ℱ'`
over `S'`, the reduced canonical ideal map tensored with `ℱ` is an isomorphism: it is an
epimorphism by strictness, and a monomorphism because the composite with the ideal action is
one. -/
@[stacks 08LI "first isomorphism in the final assertion"]
theorem baseToSourceIdealTensor_isIso (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF : AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj F'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F') :
    IsIso (baseToSourceIdealTensor D F') := by
  have hcomp : IsIso (baseToInfinitesimal D F') :=
    (isFlatOver_iff_baseToInfinitesimal_isIso D hi ht hs F' hF).1 hF'
  let p := baseToSourceIdealTensor D F'
  let g := sourceIdealActionImage D F'
  have : Epi p := baseToSourceIdealTensor_epi D hs F'
  have : IsIso (p ≫ g) := by simpa [p, g, baseToInfinitesimal] using hcomp
  have : Mono (p ≫ g) := ((isIso_iff_mono_and_epi (p ≫ g)).mp inferInstance).1
  have : Mono p := mono_of_mono p g
  exact isIso_of_mono_of_epi p

/-- **Stacks Project, Tag 08LI.** Under the hypotheses of the criterion and flatness of `ℱ'`
over `S'`, the ideal action on the reduced source identifies `i^* ℐ ⊗_{𝒪_X} ℱ` with the ideal
multiple `ℐℱ'`. -/
@[stacks 08LI "second isomorphism in the final assertion"]
theorem sourceIdealActionImage_isIso (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF : AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj F'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F') :
    IsIso (sourceIdealActionImage D F') := by
  have hcomp : IsIso (baseToInfinitesimal D F') :=
    (isFlatOver_iff_baseToInfinitesimal_isIso D hi ht hs F' hF).1 hF'
  let p := baseToSourceIdealTensor D F'
  let g := sourceIdealActionImage D F'
  have : IsIso p := baseToSourceIdealTensor_isIso D hi ht hs F' hF hF'
  have : IsIso (p ≫ g) := by simpa [p, g, baseToInfinitesimal] using hcomp
  have : Epi g := sourceIdealActionImage_epi D F'
  exact IsIso.of_isIso_comp_left p g

/-! ### The symmetry of the tensor product, and the lifts of a map -/

/-- The symmetry `ℱ(U) ⊗_{𝒪_Y(U)} 𝒢(U) → 𝒢(U) ⊗_{𝒪_Y(U)} ℱ(U)` of the sections of the presheaf
tensor product. -/
noncomputable def tCommAdd {Y : RingedSpace.{u, u}} (F G : PresheafOfModules.{u} (O Y))
    (U : (Opens Y.carrier)ᵒᵖ) :
    TensorProduct (Y.presheaf.obj U) (F.obj U) (G.obj U) →+
      TensorProduct (Y.presheaf.obj U) (G.obj U) (F.obj U) :=
  (TensorProduct.comm (Y.presheaf.obj U) (F.obj U) (G.obj U)).toLinearMap.toAddMonoidHom

lemma tCommAdd_tmul {Y : RingedSpace.{u, u}} (F G : PresheafOfModules.{u} (O Y))
    (U : (Opens Y.carrier)ᵒᵖ) (m : F.obj U) (n : G.obj U) :
    tCommAdd F G U (m ⊗ₜ[Y.presheaf.obj U] n) = n ⊗ₜ[Y.presheaf.obj U] m := rfl

/-- The symmetry of the sections of the presheaf tensor product is compatible with restriction:
restricting and then exchanging the two factors is exchanging and then restricting. -/
lemma tCommAdd_comp_tRestrAdd {Y : RingedSpace.{u, u}} (F G : PresheafOfModules.{u} (O Y))
    {U V : (Opens Y.carrier)ᵒᵖ} (f : U ⟶ V) :
    (tCommAdd F G V).comp
        (((PresheafOfModules.tensorObj (O := Y.presheaf) F G).restrictₛₗ f).toAddMonoidHom) =
      (((PresheafOfModules.tensorObj (O := Y.presheaf) G F).restrictₛₗ f).toAddMonoidHom).comp
        (tCommAdd F G U) := by
  refine AddMonoidHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m n => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The symmetry of the presheaf tensor product, as a morphism of the underlying presheaves of
abelian groups. Its naturality is the lemma `tCommAdd_comp_tRestrAdd`. -/
noncomputable def presheafTensorCommNat {Y : RingedSpace.{u, u}}
    (F G : PresheafOfModules.{u} (O Y)) :
    (PresheafOfModules.tensorObj (O := Y.presheaf) F G).presheaf ⟶
      (PresheafOfModules.tensorObj (O := Y.presheaf) G F).presheaf where
  app U := AddCommGrpCat.ofHom (tCommAdd F G U)
  naturality _ _ f := by
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun t => ?_
    exact DFunLike.congr_fun (tCommAdd_comp_tRestrAdd F G f) t

/-- The symmetry of the presheaf tensor product is `𝒪_Y`-linear. -/
lemma presheafTensorCommNat_linear {Y : RingedSpace.{u, u}}
    (F G : PresheafOfModules.{u} (O Y)) (U : (Opens Y.carrier)ᵒᵖ) (r : (O Y).obj U)
    (m : (PresheafOfModules.tensorObj (O := Y.presheaf) F G).obj U) :
    (presheafTensorCommNat F G).app U (r • m) = r • (presheafTensorCommNat F G).app U m :=
  (TensorProduct.comm (Y.presheaf.obj U) (F.obj U) (G.obj U)).map_smul r m

/-- **The symmetry `ℱ ⊗^{pre}_{𝒪_Y} 𝒢 ⟶ 𝒢 ⊗^{pre}_{𝒪_Y} ℱ`** of the presheaf tensor product of
two presheaves of `𝒪_Y`-modules. -/
noncomputable def presheafTensorCommHom {Y : RingedSpace.{u, u}}
    (F G : PresheafOfModules.{u} (O Y)) :
    (PresheafOfModules.tensorObj (O := Y.presheaf) F G) ⟶
      (PresheafOfModules.tensorObj (O := Y.presheaf) G F) :=
  PresheafOfModules.homMk (presheafTensorCommNat F G) (presheafTensorCommNat_linear F G)

/-- The symmetry of the presheaf tensor product is an involution. -/
lemma presheafTensorCommHom_comp {Y : RingedSpace.{u, u}}
    (F G : PresheafOfModules.{u} (O Y)) :
    presheafTensorCommHom F G ≫ presheafTensorCommHom G F =
      𝟙 (PresheafOfModules.tensorObj (O := Y.presheaf) F G) := by
  refine PresheafOfModules.tensorObj_hom_ext fun U m n => ?_
  rfl

/-- **The symmetry `ℱ ⊗_{𝒪_Y} 𝒢 ≅ 𝒢 ⊗_{𝒪_Y} ℱ` of the tensor product of sheaves of modules**
on a ringed space, obtained by sheafifying the symmetry of the presheaf tensor product. -/
noncomputable def tensorSheafCommIso (Y : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing Y)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (F)).obj (G)) ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u})).obj (G)).obj (F)) where
  hom := (sheafifyFunctor Y).map (presheafTensorCommHom F.val G.val)
  inv := (sheafifyFunctor Y).map (presheafTensorCommHom G.val F.val)
  hom_inv_id := ((sheafifyFunctor Y).map_comp _ _).symm.trans
    ((congrArg (sheafifyFunctor Y).map (presheafTensorCommHom_comp F.val G.val)).trans
      ((sheafifyFunctor Y).map_id _))
  inv_hom_id := ((sheafifyFunctor Y).map_comp _ _).symm.trans
    ((congrArg (sheafifyFunctor Y).map (presheafTensorCommHom_comp G.val F.val)).trans
      ((sheafifyFunctor Y).map_id _))

/-- **Flatness implies the criterion of Stacks 08LI.** For a strict morphism of thickenings and
an `𝒪_{X'}`-module flat over `S'`, the canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐℱ'` is an
isomorphism. -/
alias isIso_baseToInfinitesimal_of_isFlatOver := baseToInfinitesimal_isIso_of_isFlatOver

/-- The coefficient module `𝒢 ⊗_{𝒪_X} f^* 𝒥` of **Stacks 08LJ**: the tensor product over `𝒪_X`
of the restriction `𝒢 = i^* 𝒢'` with the pullback to `X` of the ideal `𝒥` of the lower
thickening. -/
noncomputable def restrictionTensorBaseIdeal (D : MorphismOfThickenings.{u})
    (G' : SheafOfModules.{u} (structureSheafRing D.X')) : SheafOfModules.{u} (structureSheafRing D.X) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u})).obj (((modulePullback D.i).obj G'))).obj (((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ))))

/-- **Stacks Project, Tag 08LJ.** For a strict morphism of thickenings and an `𝒪_{X'}`-module
`𝒢'` flat over `S'`, the canonical map identifies `𝒢 ⊗_{𝒪_X} f^* 𝒥` with the ideal multiple
`ℐ𝒢'`, read on `X` as the kernel of the reduction `𝒢' ⟶ i_* i^* 𝒢'`.

It is the symmetry of the tensor product followed by the canonical map
`f^* 𝒥 ⊗_{𝒪_X} 𝒢 ⟶ ℐ𝒢'` of **Stacks 08LI**, which flatness makes invertible. -/
@[sga "3 XV 2.7" "more general"]
noncomputable def infinitesimalTensorIso (D : MorphismOfThickenings.{u}) (hs : D.IsStrict)
    (G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G') :
    restrictionTensorBaseIdeal D G' ≅ infinitesimalPartOnSource D.i G' :=
  tensorSheafCommIso D.X ((modulePullback D.i).obj G')
      ((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ)) ≪≫
    @asIso _ _ _ _ (baseToInfinitesimal D G')
      (isIso_baseToInfinitesimal_of_isFlatOver D hs G' hG')

/-- **Stacks Project, Tag 08LJ.** Let `(f, f')` be a morphism of thickenings with `i` a first
order thickening, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules, set `ℱ = i^* ℱ'` and `𝒢 = i^* 𝒢'`,
and let `φ : ℱ ⟶ 𝒢` be `𝒪_X`-linear. If `𝒢'` is flat over `S'` and `(f, f')` is strict, the
lifts of `φ` to an `𝒪_{X'}`-linear `φ' : ℱ' ⟶ 𝒢'` form, when nonempty, a principal homogeneous
space under `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`, which acts through `infinitesimalTensorIso`: each
`δ` translates a lift to a lift, and any two lifts are translated to one another by exactly one
`δ`.

The group acts because `i^*` is additive and kills a map through `ℐ𝒢'`, which is
`modulePullback_map_add_comp_infinitesimalι`. That the action is simply transitive is **Stacks
08LH**, which gives the same conclusion for `Hom_{𝒪_X}(ℱ, ℐ𝒢')`, transported along **Stacks
08LI**, which identifies `ℐ𝒢'` with `𝒢 ⊗_{𝒪_X} f^* 𝒥`. -/
@[stacks 08LJ]
theorem mapLift_isTorsor_tensor (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G')
    (hne : Nonempty (MapLift D.i F' G' φ)) :
    (∀ (δ : (modulePullback D.i).obj F' ⟶ restrictionTensorBaseIdeal D G')
        (φ₁ : MapLift D.i F' G' φ),
        (modulePullback D.i).map
            (infinitesimalHomEquiv D.i hi F' G'
                  (δ ≫ (infinitesimalTensorIso D hs G' hG').hom) ≫ infinitesimalι D.i G' +
                φ₁.1) =
          φ) ∧
      ∀ φ₁ φ₂ : MapLift D.i F' G' φ,
        ∃! δ : (modulePullback D.i).obj F' ⟶ restrictionTensorBaseIdeal D G',
          infinitesimalHomEquiv D.i hi F' G'
                (δ ≫ (infinitesimalTensorIso D hs G' hG').hom) ≫ infinitesimalι D.i G' + φ₁.1 =
              φ₂.1 := by
  refine ⟨fun δ φ₁ =>
    (modulePullback_map_add_comp_infinitesimalι D.i _ φ₁.1).trans φ₁.2, fun φ₁ φ₂ => ?_⟩
  obtain ⟨δ₀, hδ₀, huniq⟩ := mapLift_isPrincipalHomogeneous D.i hi F' G' φ hne φ₁ φ₂
  refine ⟨δ₀ ≫ (infinitesimalTensorIso D hs G' hG').inv, ?_, fun δ hδ => ?_⟩
  · change infinitesimalHomEquiv D.i hi F' G'
        ((δ₀ ≫ (infinitesimalTensorIso D hs G' hG').inv) ≫
          (infinitesimalTensorIso D hs G' hG').hom) ≫ infinitesimalι D.i G' + φ₁.1 = φ₂.1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hδ₀
  · rw [← huniq (δ ≫ (infinitesimalTensorIso D hs G' hG').hom) hδ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

/-- The simple transitivity on its own: any two lifts of `φ` are translated to one another by
exactly one `δ : ℱ ⟶ 𝒢 ⊗_{𝒪_X} f^* 𝒥`.

This is the second component of `mapLift_isTorsor_tensor`, kept as a named form for the
consumers that need only the difference of two lifts. It is deliberately **not** registered for
[Stacks, Tag 08LJ]: the tag asserts that the group acts on the lifts and acts simply
transitively, and this statement is half of that, so `mapLift_isTorsor_tensor` carries the tag
alone. -/
theorem mapLift_isPrincipalHomogeneous_tensor (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F' G' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hG' : AlgebraicGeometry.IsFlatOver D.f' G')
    (φ : (modulePullback D.i).obj F' ⟶ (modulePullback D.i).obj G')
    (hne : Nonempty (MapLift D.i F' G' φ)) :
    ∀ φ₁ φ₂ : MapLift D.i F' G' φ,
      ∃! δ : (modulePullback D.i).obj F' ⟶ restrictionTensorBaseIdeal D G',
        infinitesimalHomEquiv D.i hi F' G'
              (δ ≫ (infinitesimalTensorIso D hs G' hG').hom) ≫ infinitesimalι D.i G' + φ₁.1 =
            φ₂.1 :=
  (mapLift_isTorsor_tensor D hi hs F' G' hG' φ hne).2

/-! ### A strict morphism of first order thickenings on stalks -/

/-- **A strict morphism of first order thickenings, read on stalks.** Let `x` be a point of `X`
and `z = i(x)` the corresponding point of `X'`, so that `f'(z) = t(f(x))`. The stalk map
`p : 𝒪_{S',f'(z)} ⟶ 𝒪_{S,f(x)}` of `t` is surjective with square-zero kernel `𝔧`, the stalk map
`ε : 𝒪_{X',z} ⟶ 𝒪_{X,x}` of `i` is surjective, and strictness says that its kernel is
`𝔧 𝒪_{X',z}`. The point `z` is taken with an equation `i(x) = z` so that the statement can be
read at a point of `X'` presented in another way. -/
theorem stalkMap_facts_of_isStrict (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (x : D.X) (z : D.X') (hz : D.i.hom.base x = z)
    (hpt : D.f'.hom.base z = D.t.hom.base (D.f.hom.base x)) :
    Function.Surjective (eqToHom (congrArg D.S'.presheaf.stalk hpt) ≫
        D.t.hom.stalkMap (D.f.hom.base x)).hom ∧
      RingHom.ker (eqToHom (congrArg D.S'.presheaf.stalk hpt) ≫
        D.t.hom.stalkMap (D.f.hom.base x)).hom ^ 2 = ⊥ ∧
      Function.Surjective (eqToHom (congrArg D.X'.presheaf.stalk hz.symm) ≫
        D.i.hom.stalkMap x).hom ∧
      RingHom.ker (eqToHom (congrArg D.X'.presheaf.stalk hz.symm) ≫ D.i.hom.stalkMap x).hom =
        (RingHom.ker (eqToHom (congrArg D.S'.presheaf.stalk hpt) ≫
          D.t.hom.stalkMap (D.f.hom.base x)).hom).map (D.f'.hom.stalkMap z).hom := by
  subst hz
  obtain ⟨J, hJ, eJ, heJ⟩ := firstOrder_stalkIdeal D.t ht (D.f'.hom.base (D.i.hom.base x))
  obtain ⟨I, hI, eI, heI⟩ := firstOrder_stalkIdeal D.i hi (D.i.hom.base x)
  obtain ⟨hp, hJp, hsurj, hker⟩ := strict_stalkMap_facts D hi ht hs x hpt I eI heI J eJ heJ
  exact ⟨hp, hJp ▸ hJ, by simpa using hsurj, by simpa using hker⟩

/-! ### Pullback along a square which is a pushout on stalks -/

/-- The point equation `g_Z(q(y)) = q_S(g_Y(y))` of a commutative square of ringed spaces. -/
theorem stalkSquare_point {Y Z T W : RingedSpace.{u, u}} {q : Y ⟶ Z} {qS : T ⟶ W}
    {gY : Y ⟶ T} {gZ : Z ⟶ W} (hcomm : q ≫ gZ = gY ≫ qS) (y : Y) :
    gZ.hom.base (q.hom.base y) = qS.hom.base (gY.hom.base y) := by
  have h := congrArg (fun g : Y ⟶ W => g.hom.base y) hcomm
  simpa using h

/-- The stalk maps of a commutative square of ringed spaces commute: the two ways from
`𝒪_{W,g_Z(q(y))}` to `𝒪_{Y,y}` agree. -/
theorem stalkSquare_comm {Y Z T W : RingedSpace.{u, u}} {q : Y ⟶ Z} {qS : T ⟶ W}
    {gY : Y ⟶ T} {gZ : Z ⟶ W} (hcomm : q ≫ gZ = gY ≫ qS) (y : Y) :
    gZ.hom.stalkMap (q.hom.base y) ≫ q.hom.stalkMap y =
      (eqToHom (congrArg W.presheaf.stalk (stalkSquare_point hcomm y)) ≫
        qS.hom.stalkMap (gY.hom.base y)) ≫ gY.hom.stalkMap y := by
  have hc := PresheafedSpace.stalkMap.congr_hom (q ≫ gZ).hom (gY ≫ qS).hom
    (congrArg (fun g : Y ⟶ W => g.hom) hcomm) y
  change (q.hom ≫ gZ.hom).stalkMap y = eqToHom _ ≫ (gY.hom ≫ qS.hom).stalkMap y at hc
  rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at hc
  rw [hc, Category.assoc]
  rfl

/-- **The stalk square of a commutative square of ringed spaces is a pushout of rings.** For
`q ≫ g_Z = g_Y ≫ q_S`, at every point `y` the square of local rings

    𝒪_{W,g_Z(q(y))} ⟶ 𝒪_{T,g_Y(y)}
          ↓                 ↓
    𝒪_{Z,q(y)}     ⟶    𝒪_{Y,y}

is a pushout, `𝒪_{Y,y} = 𝒪_{T,g_Y(y)} ⊗ 𝒪_{Z,q(y)}`. -/
def StalkSquareIsPushout {Y Z T W : RingedSpace.{u, u}} (q : Y ⟶ Z) (qS : T ⟶ W)
    (gY : Y ⟶ T) (gZ : Z ⟶ W) (hcomm : q ≫ gZ = gY ≫ qS) : Prop :=
  ∀ y : Y,
    letI : Algebra (W.presheaf.stalk (gZ.hom.base (q.hom.base y)))
        (T.presheaf.stalk (gY.hom.base y)) :=
      (eqToHom (congrArg W.presheaf.stalk (stalkSquare_point hcomm y)) ≫
        qS.hom.stalkMap (gY.hom.base y)).hom.toAlgebra
    letI : Algebra (W.presheaf.stalk (gZ.hom.base (q.hom.base y)))
        (Z.presheaf.stalk (q.hom.base y)) := (gZ.hom.stalkMap (q.hom.base y)).hom.toAlgebra
    letI : Algebra (T.presheaf.stalk (gY.hom.base y)) (Y.presheaf.stalk y) :=
      (gY.hom.stalkMap y).hom.toAlgebra
    letI : Algebra (Z.presheaf.stalk (q.hom.base y)) (Y.presheaf.stalk y) :=
      (q.hom.stalkMap y).hom.toAlgebra
    letI : Algebra (W.presheaf.stalk (gZ.hom.base (q.hom.base y))) (Y.presheaf.stalk y) :=
      ((q.hom.stalkMap y).hom.comp (gZ.hom.stalkMap (q.hom.base y)).hom).toAlgebra
    haveI : IsScalarTower (W.presheaf.stalk (gZ.hom.base (q.hom.base y)))
        (Z.presheaf.stalk (q.hom.base y)) (Y.presheaf.stalk y) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower (W.presheaf.stalk (gZ.hom.base (q.hom.base y)))
        (T.presheaf.stalk (gY.hom.base y)) (Y.presheaf.stalk y) :=
      IsScalarTower.of_algebraMap_smul fun a b => congrArg (fun r => r * b)
        (congrArg (fun g : W.presheaf.stalk (gZ.hom.base (q.hom.base y)) ⟶
          Y.presheaf.stalk y => g.hom a) (stalkSquare_comm hcomm y)).symm
    Algebra.IsPushout (W.presheaf.stalk (gZ.hom.base (q.hom.base y)))
      (T.presheaf.stalk (gY.hom.base y)) (Z.presheaf.stalk (q.hom.base y)) (Y.presheaf.stalk y)

/-- **Pullback along a square which is a pushout on stalks preserves flatness over the base.**
If `q ≫ g_Z = g_Y ≫ q_S` is a pushout on every stalk and `ℳ` is an `𝒪_Z`-module flat over `W`,
then `q^* ℳ` is flat over `T`: its stalk is `𝒪_{Y,y} ⊗ ℳ_{q(y)}`, which the pushout identifies
with the base change `𝒪_{T,g_Y(y)} ⊗ ℳ_{q(y)}` of a flat module (Stacks 0098). -/
theorem isFlatOver_modulePullback_of_stalkSquareIsPushout {Y Z T W : RingedSpace.{u, u}}
    (q : Y ⟶ Z) (qS : T ⟶ W) (gY : Y ⟶ T) (gZ : Z ⟶ W) (hcomm : q ≫ gZ = gY ≫ qS)
    (hpo : StalkSquareIsPushout q qS gY gZ hcomm) (M : SheafOfModules.{u} (structureSheafRing Z))
    (hM : AlgebraicGeometry.IsFlatOver gZ M) :
    AlgebraicGeometry.IsFlatOver gY ((modulePullback q).obj M) := by
  intro y
  let AW := W.presheaf.stalk (gZ.hom.base (q.hom.base y))
  let AT := T.presheaf.stalk (gY.hom.base y)
  let AZ := Z.presheaf.stalk (q.hom.base y)
  let AY := Y.presheaf.stalk y
  letI _iWT : Algebra AW AT :=
    (eqToHom (congrArg W.presheaf.stalk (stalkSquare_point hcomm y)) ≫
      qS.hom.stalkMap (gY.hom.base y)).hom.toAlgebra
  letI _iWZ : Algebra AW AZ := (gZ.hom.stalkMap (q.hom.base y)).hom.toAlgebra
  letI _iTY : Algebra AT AY := (gY.hom.stalkMap y).hom.toAlgebra
  letI _iZY : Algebra AZ AY := (q.hom.stalkMap y).hom.toAlgebra
  letI _iWY : Algebra AW AY :=
    ((q.hom.stalkMap y).hom.comp (gZ.hom.stalkMap (q.hom.base y)).hom).toAlgebra
  haveI : IsScalarTower AW AZ AY := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower AW AT AY :=
    IsScalarTower.of_algebraMap_smul fun a b => congrArg (fun r => r * b)
      (congrArg (fun g : W.presheaf.stalk (gZ.hom.base (q.hom.base y)) ⟶
        Y.presheaf.stalk y => g.hom a) (stalkSquare_comm hcomm y)).symm
  haveI : Algebra.IsPushout AW AT AZ AY := hpo y
  let V := grpStalk Z M.val (q.hom.base y)
  let N := grpStalk Y ((modulePullback q).obj M).val y
  letI _iV : Module AZ V := stalkModule Z M.val (q.hom.base y)
  letI _iN : Module AY N := stalkModule Y ((modulePullback q).obj M).val y
  letI _iWV : Module AW V := Module.compHom _ (gZ.hom.stalkMap (q.hom.base y)).hom
  letI _iTN : Module AT N := Module.compHom _ (gY.hom.stalkMap y).hom
  haveI : IsScalarTower AW AZ V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower AT AY N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hV : Module.Flat AW V := (flat_stalkModule_iff_isFlatOverAt gZ M (q.hom.base y)).2
    (hM (q.hom.base y))
  obtain ⟨e, -⟩ := pullback_stalk_formula q M y
  have hflatT : Module.Flat AT (AT ⊗[AW] V) := Module.Flat.baseChange AW AT V
  have hflatY : Module.Flat AT (AY ⊗[AZ] V) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange AW AT AZ AY V)
  have hflatN : Module.Flat AT N := Module.Flat.of_linearEquiv (e.restrictScalars AT)
  exact (flat_stalkModule_iff_isFlatOverAt gY ((modulePullback q).obj M) y).1 hflatN

/-- **The stalk square of a strict morphism of first order thickenings is a pushout**:
`𝒪_{X,x} = 𝒪_{S,f(x)} ⊗_{𝒪_{S',f'(i(x))}} 𝒪_{X',i(x)}`. Both stalk maps of the thickenings are
surjective, and strictness identifies the kernel of the first with the extension of the kernel
of the second. -/
theorem stalkSquareIsPushout_of_isStrict (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict) :
    StalkSquareIsPushout D.i D.t D.f D.f' D.comm := by
  intro x
  obtain ⟨hp, -, hsurj, hker⟩ := stalkMap_facts_of_isStrict D hi ht hs x (D.i.hom.base x) rfl
    (stalkSquare_point D.comm x)
  simp only [eqToHom_refl, Category.id_comp] at hsurj hker
  letI : Algebra (D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x)))
      (D.S.presheaf.stalk (D.f.hom.base x)) :=
    (eqToHom (congrArg D.S'.presheaf.stalk (stalkSquare_point D.comm x)) ≫
      D.t.hom.stalkMap (D.f.hom.base x)).hom.toAlgebra
  letI : Algebra (D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x)))
      (D.X'.presheaf.stalk (D.i.hom.base x)) :=
    (D.f'.hom.stalkMap (D.i.hom.base x)).hom.toAlgebra
  letI : Algebra (D.S.presheaf.stalk (D.f.hom.base x)) (D.X.presheaf.stalk x) :=
    (D.f.hom.stalkMap x).hom.toAlgebra
  letI : Algebra (D.X'.presheaf.stalk (D.i.hom.base x)) (D.X.presheaf.stalk x) :=
    (D.i.hom.stalkMap x).hom.toAlgebra
  letI : Algebra (D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x)))
      (D.X.presheaf.stalk x) :=
    ((D.i.hom.stalkMap x).hom.comp (D.f'.hom.stalkMap (D.i.hom.base x)).hom).toAlgebra
  haveI : IsScalarTower (D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x)))
      (D.X'.presheaf.stalk (D.i.hom.base x)) (D.X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower (D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x)))
      (D.S.presheaf.stalk (D.f.hom.base x)) (D.X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun a b => congrArg (fun r => r * b)
      (congrArg (fun g : D.S'.presheaf.stalk (D.f'.hom.base (D.i.hom.base x)) ⟶
        D.X.presheaf.stalk x => g.hom a) (stalkSquare_comm D.comm x)).symm
  exact algebra_isPushout_of_surjective_kernel hp hsurj hker

/-- **The restriction of a module flat over `S'` is flat over `S`.** For a strict morphism of
first order thickenings, `i^* ℱ'` is flat over `S` as soon as `ℱ'` is flat over `S'`: on stalks
`(i^* ℱ')_x = 𝒪_{S,f(x)} ⊗ ℱ'_{i(x)}` is a base change. -/
theorem isFlatOver_modulePullback_of_isStrict (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (F' : SheafOfModules.{u} (structureSheafRing D.X'))
    (hF' : AlgebraicGeometry.IsFlatOver D.f' F') :
    AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj F') :=
  isFlatOver_modulePullback_of_stalkSquareIsPushout D.i D.t D.f D.f' D.comm
    (stalkSquareIsPushout_of_isStrict D hi ht hs) F' hF'

end AlgebraicGeometry.RingedSpaceThickening

end
