module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
import StacksCore.Tactic.StacksAttribute

/-!
# The module structure on the pushout of an extension along a morphism of thickenings

Let `(X, 𝒪_X)` be a ringed space, let `i : X ⟶ X'` be a first order thickening with ideal `ℐ₁`,
and let a second first order thickening of `(X, 𝒪_X)` be presented on the same space by a sheaf
of rings `𝒪'₂` together with `h^♯ : 𝒪'₂ ⟶ 𝒪_{X'}`; the structure map of the second thickening
is then `h^♯` followed by `i^♯`, so that `h` is a morphism of thickenings over `(X, 𝒪_X)`, and
its ideal is `ℐ₂`. Fix an `𝒪_X`-module `ℱ`, modules `𝒦₁`, `𝒦₂` with canonical maps
`c_k : ℐ_k ⊗_{𝒪_X} ℱ ⟶ 𝒦_k` and a map `κ : 𝒦₂ ⟶ 𝒦₁` making the square with `ℐ₂ ⟶ ℐ₁` commute.
Then an extension `0 ⟶ 𝒦₂ ⟶ ℱ'₂ ⟶ ℱ ⟶ 0` over the second thickening whose canonical map is
`c₂` is carried to an extension `0 ⟶ 𝒦₁ ⟶ ℱ'₁ ⟶ ℱ ⟶ 0` over the first, with middle term the
pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁`, and the canonical map of the new extension is `c₁`.

The content is the `𝒪_{X'}`-module structure on that pushout, which the source omits. Write
`T = 𝒪'₂ ⋉ ℐ₁` for the trivial square-zero extension and `q : T ⟶ 𝒪_{X'}` for
`(a, m) ↦ h^♯(a) - m`, a locally surjective map of sheaves of rings whose kernel consists of
the pairs `(ι₂ b, ℐ₂ ⟶ ℐ₁ (b))`. The pushout is a `T`-module through `T ↠ 𝒪'₂` once its action
is twisted by `(a, m) ⊛ p := a · p - c₁(m ⊗ p̄)`; the Leibniz rule for `(a, m) ↦ m` is exactly
associativity of the twisted action, and the kernel of `q` annihilates the twisted module, so it
descends along `q`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.structureReshape` and
  `AlgebraicGeometry.RingedSpaceThickening.reshapeHom`: the ringed space on the space of `X'`
  with a prescribed structure sheaf, and the second thickening of `X` landing in it.
* `AlgebraicGeometry.RingedSpaceThickening.SecondThickening`: the second thickening together
  with the morphism of thickenings `h^♯` to the first.
* `AlgebraicGeometry.RingedSpaceThickening.SecondThickening.spaceHom`: the morphism
  `h : X'₁ ⟶ X'₂` that `h^♯` presents, under which `i₁ ≫ h = i₂` holds by `rfl`
  (`SecondThickening.comp_spaceHom`). This is the form Tags 08LC and 08LD are stated in.
* `AlgebraicGeometry.RingedSpaceThickening.SecondThickening.sqZeroRing` and
  `.sqZeroProj`: the sheaf of rings `T = 𝒪'₂ ⋉ ℐ₁` and the map `q : T ⟶ 𝒪_{X'}`.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData`: the data `ℱ`, `𝒦₁`, `𝒦₂`,
  `c₁`, `c₂`, `κ` of the remark with its commuting square.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.twist` and `.twistedSheaf`: the
  twisting term `c₁(m ⊗ p̄)` and the resulting `T`-module on the pushout.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.middle`: the `𝒪_{X'}`-module
  obtained from the twisted `T`-module by descent along `q`.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.extensionOne`: **Stacks 08LC**,
  the resulting extension of `ℱ` by `𝒦₁` over the first thickening.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.SecondThickening.sqZeroProj_locallySurjective`:
  `q` is locally surjective, because the structure map of the second thickening is and `ℐ₁` is
  the kernel of `i^♯`.
* `AlgebraicGeometry.RingedSpaceThickening.SecondThickening.exists_ideal_of_sqZeroProj_eq_zero`
  and `.sqZeroProj_eq_zero_of_ideal`: a section of `T` is killed by `q` exactly when its ring
  component lies in `ℐ₂` and its ideal component is its image in `ℐ₁`.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.inclTwo_smul_eq`: multiplication
  on the pushout by a section of `ℐ₂` is the twisting term by its image in `ℐ₁`. This is what
  makes the kernel of `q` annihilate the twisted action, and it is where the commuting square of
  the two canonical maps is used.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.extensionOne_action`:
  **Stacks 08LC**, the canonical map of the new extension is the prescribed `c₁`.

## Implementation notes

The source identifies the underlying topological spaces of `X`, `X'₁` and `X'₂` — "thinking of
all the sheaves as sheaves on `X`" — and so does this file: the second thickening is presented
by a sheaf of rings on the space of the first, and `reshapeHom` turns that presentation into a
morphism of ringed spaces to which the Tag 08L4 development applies verbatim. The morphism `h`
of thickenings is then the identity on the underlying space, which is why only its comorphism
`h^♯` appears in the construction below; `SecondThickening.spaceHom` assembles the two into the
morphism `X'₁ ⟶ X'₂` itself, which is what the functoriality of Tags 08LC and 08LD is stated
under. Nothing else identifies the spaces: `𝒪_X`-modules are still carried to the thickened
space by `i_*`, as in Tag 08L4.

Because `reshapeHom` leaves the underlying continuous map of `i` untouched, `i_* 𝒩` and
`(i₂)_* 𝒩` have the same sections over every open and differ only in which sheaf of rings acts;
`toSecond` and `ofSecond` name that identification, and they are the identity on sections.

The pushout and its canonical map are not rebuilt here: they are
`AlgebraicGeometry.RingedSpaceThickening.pushoutExtension` and
`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_pushoutExtension` of
`StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFunctoriality`, which already provide
the extension over the second thickening with canonical map `c₂ ≫ κ`. The descent of a module
along a locally surjective map of sheaves of rings whose kernel annihilates it is
`Deformation.ToposThickening.descendModule`, stated for an arbitrary site and so applicable to
the site of opens of `X'` without change; the same holds for
`Deformation.ToposThickening.moduleOfAxioms` and
`Deformation.ToposThickening.shortExact_of_fullyFaithful_map`.

The commuting square of the source is recorded on local pure tensors, as
`PushoutDescentData.comm`: the induced map `ℐ₂ ⟶ ℐ₁` is not a morphism of sheaves of modules
over either structure sheaf, so instead of naming it the square is stated for a section `m` of
`ℐ₁` and a section `b` of `ℐ₂` whose images in `𝒪_{X'}` agree, which says exactly that `m` is
the image of `b`.

## References

* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.ClosedImmersion (exists_idealSheaf_section_of_app_eq_zero
  injective_idealSheafι_val_app)
open RingedSpaceModuleAdjunction (structureSheafModuleHom)
open Stacks.Cohomology.Generators (toTensorSheafSection_restrict toTensorSheafSection_smul_left
  toTensorSheafSection_smul_right)
open Stacks.Thickenings

universe u

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

attribute [local implicit_reducible] CategoryTheory.ConcreteCategory.hom
  CategoryTheory.sheafCompose SheafOfModules.unit PresheafOfModules.unit
  SheafOfModules.forget SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}}

/-- The ringed space on the underlying space of `X'` with a prescribed structure sheaf. This is
how the second thickening of the remark is presented: on the space of the first. -/
def structureReshape (X' : RingedSpace.{u, u})
    (O₂ : TopCat.Presheaf CommRingCat.{u} X'.carrier)
    (hO₂ : TopCat.Presheaf.IsSheaf O₂) : RingedSpace.{u, u} where
  carrier := X'.carrier
  presheaf := O₂
  IsSheaf := hO₂

/-- The second thickening of `X`, as a morphism of ringed spaces: the underlying continuous map
of `i`, with structure map the given `h^♯ : 𝒪'₂ ⟶ 𝒪_{X'}` followed by `i^♯`. -/
noncomputable def reshapeHom (i : X ⟶ X')
    (O₂ : TopCat.Presheaf CommRingCat.{u} X'.carrier) (hO₂ : TopCat.Presheaf.IsSheaf O₂)
    (hSharp : O₂ ⟶ X'.presheaf) : X ⟶ structureReshape X' O₂ hO₂ :=
  InducedCategory.homMk
    ({ base := i.hom.base, c := hSharp ≫ i.hom.c } :
      X.toPresheafedSpace ⟶ (structureReshape X' O₂ hO₂).toPresheafedSpace)

/-- The second thickening has the same underlying continuous map as the first. -/
@[simp] theorem reshapeHom_base (i : X ⟶ X')
    (O₂ : TopCat.Presheaf CommRingCat.{u} X'.carrier) (hO₂ : TopCat.Presheaf.IsSheaf O₂)
    (hSharp : O₂ ⟶ X'.presheaf) : (reshapeHom i O₂ hO₂ hSharp).hom.base = i.hom.base := rfl

/-- The structure map of the second thickening is `h^♯` followed by `i^♯`, on local sections. -/
theorem reshapeHom_c_app (i : X ⟶ X')
    (O₂ : TopCat.Presheaf CommRingCat.{u} X'.carrier) (hO₂ : TopCat.Presheaf.IsSheaf O₂)
    (hSharp : O₂ ⟶ X'.presheaf) (V : Opens X'.carrier) (a : O₂.obj (op V)) :
    (reshapeHom i O₂ hO₂ hSharp).hom.c.app (op V) a =
      i.hom.c.app (op V) (hSharp.app (op V) a) := rfl

/-- Local sections of a sheaf of `𝒪_{X'}`-modules are a module over the *commutative* ring of
local sections of `𝒪_{X'}`, which is the ring at which the sections of the structure sheaf are
named below. -/
@[instance_reducible]
noncomputable def sectionsModuleOverSpace (M : SheafOfModules.{u} (structureSheafRing X'))
    (V : Opens X'.carrier) : Module (X'.presheaf.obj (op V)) (M.val.obj (op V)) :=
  (M.val.obj (op V)).isModule

/-- Local sections of a sheaf of `𝒪_X`-modules are a module over the ring of local sections of
`𝒪_X` at which the tensor product is formed. -/
@[instance_reducible]
noncomputable def sectionsModuleOverBase (N : SheafOfModules.{u} (structureSheafRing X))
    (W : Opens X.carrier) : Module ((structureSheafRing X).obj.obj (op W)) (N.val.obj (op W)) :=
  (N.val.obj (op W)).isModule

attribute [local instance] sectionsModuleOverSpace sectionsModuleOverBase

/-- The structure map `i^♯` of a thickening on local sections. -/
noncomputable def iSharpApp (i : X ⟶ X') (V : Opens X'.carrier)
    (s : X'.presheaf.obj (op V)) :
    ((structureSheafRing X).obj.obj (op ((opensMap i).obj V)) : Type u) :=
  (structureSheafHom i).hom.app (op V) s

/-- `i^♯` respects differences of local sections. -/
theorem iSharpApp_sub (i : X ⟶ X') (V : Opens X'.carrier) (s s' : X'.presheaf.obj (op V)) :
    iSharpApp i V (s - s') = iSharpApp i V s - iSharpApp i V s' :=
  map_sub ((structureSheafHom i).hom.app (op V)).hom s s'

/-- `i^♯` commutes with restriction. -/
theorem iSharpApp_naturality (i : X ⟶ X') {V W : Opens X'.carrier} (g : W ⟶ V)
    (s : X'.presheaf.obj (op V)) :
    iSharpApp i W (X'.presheaf.map g.op s) =
      (structureSheafRing X).obj.map ((opensMap i).map g).op (iSharpApp i V s) :=
  ConcreteCategory.congr_hom ((structureSheafHom i).hom.naturality g.op) s

/-- The image in `𝒪_{X'}` of a local section of the ideal of a thickening `i : X ⟶ X'`. -/
noncomputable def idealIncl (i : X ⟶ X') (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) : X'.presheaf.obj (op V) :=
  (idealSheafι i).val.app (op V) m

/-- The inclusion of the ideal is additive. -/
theorem idealIncl_add (i : X ⟶ X') (V : Opens X'.carrier)
    (m m' : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    idealIncl i V (m + m') = idealIncl i V m + idealIncl i V m' :=
  map_add ((idealSheafι i).val.app (op V)).hom m m'

/-- The inclusion of the ideal kills zero. -/
theorem idealIncl_zero (i : X ⟶ X') (V : Opens X'.carrier) :
    idealIncl i V (0 : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) = 0 :=
  map_zero ((idealSheafι i).val.app (op V)).hom

/-- The inclusion of the ideal is odd. -/
theorem idealIncl_neg (i : X ⟶ X') (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    idealIncl i V (-m) = -idealIncl i V m :=
  map_neg ((idealSheafι i).val.app (op V)).hom m

/-- The inclusion of the ideal is injective on sections. -/
theorem idealIncl_injective (i : X ⟶ X') (V : Opens X'.carrier) :
    Function.Injective (idealIncl i V) :=
  injective_idealSheafι_val_app i V

/-- Equal morphisms of sheaves of modules agree on local sections. -/
private theorem sheafOfModules_hom_app_congr {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    {f g : M ⟶ N} (h : f = g) (U : Cᵒᵖ) (x : M.val.obj U) : f.val.app U x = g.val.app U x := by
  rw [h]

/-- A local section of the ideal of `i` is killed by `i^♯`. -/
theorem iSharpApp_idealIncl (i : X ⟶ X') (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    iSharpApp i V (idealIncl i V m) = 0 :=
  sheafOfModules_hom_app_congr (kernel.condition (structureSheafModuleHom i)) (op V) m

/-- The ideal of a first order thickening has square zero on local sections. -/
theorem idealIncl_mul_idealIncl {i : X ⟶ X'} (hi : IsFirstOrderThickening i)
    (V : Opens X'.carrier)
    (m m' : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    idealIncl i V m * idealIncl i V m' = 0 := by
  have hker : ∀ n : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V),
      idealIncl i V n ∈ RingHom.ker ((structureSheafHom i).hom.app (op V)).hom := fun n =>
    RingHom.mem_ker.mpr (iSharpApp_idealIncl i V n)
  have hp : (RingHom.ker ((structureSheafHom i).hom.app (op V)).hom) ^ 2 = ⊥ := hi.2 V
  rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one] at hp
  exact (Submodule.eq_bot_iff _).1 hp _ (Ideal.mul_mem_mul (hker m) (hker m'))

/-- A second first order thickening of `(X, 𝒪_X)`, presented on the space of a first one, with a
morphism of thickenings `h^♯` to it. The underlying continuous map of `h` is the identity, as the
source arranges by viewing every sheaf in sight as a sheaf on `X`. -/
structure SecondThickening (i : X ⟶ X') where
  /-- The structure sheaf `𝒪'₂` of the second thickening. -/
  O : TopCat.Presheaf CommRingCat.{u} X'.carrier
  /-- It is a sheaf. -/
  isSheaf : TopCat.Presheaf.IsSheaf O
  /-- The comorphism `h^♯ : 𝒪'₂ ⟶ 𝒪_{X'}` of the morphism of thickenings. -/
  hSharp : O ⟶ X'.presheaf
  /-- The second thickening is a first order thickening. -/
  firstOrder : IsFirstOrderThickening (reshapeHom i O isSheaf hSharp)

namespace SecondThickening

variable {i : X ⟶ X'} (S : SecondThickening i)

/-- The second thickened ringed space. -/
noncomputable abbrev space : RingedSpace.{u, u} := structureReshape X' S.O S.isSheaf

/-- The second thickening, as a morphism of ringed spaces. -/
noncomputable abbrev hom : X ⟶ S.space := reshapeHom i S.O S.isSheaf S.hSharp

/-- The ideal `ℐ₂` of the second thickening. -/
noncomputable abbrev ideal : SheafOfModules.{u} (structureSheafRing S.space) :=
  Stacks.ClosedImmersion.idealSheaf S.hom

/-- The image in `𝒪'₂` of a local section of `ℐ₂`. -/
noncomputable def inclTwo (V : Opens X'.carrier) (b : S.ideal.val.obj (op V)) : S.O.obj (op V) :=
  (idealSheafι S.hom).val.app (op V) b

/-- A local section of `ℐ₂` is killed by the structure map of the second thickening. -/
theorem iSharpApp_inclTwo (V : Opens X'.carrier) (b : S.ideal.val.obj (op V)) :
    iSharpApp S.hom V (S.inclTwo V b) = 0 :=
  sheafOfModules_hom_app_congr (kernel.condition (structureSheafModuleHom S.hom)) (op V) b

/-- The morphism `h : X'₁ ⟶ X'₂` of thickenings of `(X, 𝒪_X)` that `h^♯` presents: the identity
on the underlying space — which is the same space for both thickenings here — with comorphism
`S.hSharp`. -/
noncomputable def spaceHom : X' ⟶ S.space :=
  InducedCategory.homMk
    ({ base := 𝟙 X'.carrier, c := S.hSharp } :
      X'.toPresheafedSpace ⟶ S.space.toPresheafedSpace)

/-- `h` is the identity on the underlying space. -/
@[simp] theorem spaceHom_base : S.spaceHom.hom.base = 𝟙 X'.carrier := rfl

/-- The comorphism of `h` is `h^♯`. -/
@[simp] theorem spaceHom_c : S.spaceHom.hom.c = S.hSharp := rfl

/-- **`h` is a morphism of thickenings of `(X, 𝒪_X)`**: the first thickening followed by `h` is
the second, which is the hypothesis `i₁ ≫ h = i₂` that the functoriality of Tags 08LC and 08LD
is stated under. It holds on the nose: the structure map of the second thickening is `h^♯`
followed by `i^♯` by construction, and composing with a morphism that is the identity on the
space changes neither component. -/
theorem comp_spaceHom : i ≫ S.spaceHom = S.hom := rfl

/-! ### The sheaf of rings `T = 𝒪'₂ ⋉ ℐ₁` and its structure map to `𝒪_{X'}` -/

/-- The ideal `ℐ₁` of the first thickening, read as a presheaf of `𝒪'₂`-modules through
`h^♯`. -/
noncomputable def idealOneOverTwo :
    PresheafOfModules.{u} (S.O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight S.hSharp (forget₂ CommRingCat.{u} RingCat.{u}))).obj
      (Stacks.ClosedImmersion.idealSheaf i).val

/-- The ideal of the first thickening is a module over the sections of `𝒪'₂`, through `h^♯`.
This is the module structure the ring structure of `T` is formed with. -/
@[instance_reducible]
noncomputable def sectionsModuleOverTwo (V : Opens X'.carrier) :
    Module (S.O.obj (op V)) ((Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :=
  (S.idealOneOverTwo.obj (op V)).isModule

attribute [local instance] sectionsModuleOverTwo

/-- The trivial square-zero extension `T = 𝒪'₂ ⋉ ℐ₁`, as a presheaf of commutative rings. -/
noncomputable def sqRing : TopCat.Presheaf CommRingCat.{u} X'.carrier :=
  PresheafOfModules.sqZeroExtPresheaf S.idealOneOverTwo

/-- `T` is a sheaf, because `𝒪'₂` and `ℐ₁` are. -/
theorem isSheaf_sqRing : TopCat.Presheaf.IsSheaf S.sqRing :=
  PresheafOfModules.isSheaf_sqZeroExtPresheaf S.idealOneOverTwo S.isSheaf
    (Stacks.ClosedImmersion.idealSheaf i).isSheaf

/-- The trivial square-zero extension `T = 𝒪'₂ ⋉ ℐ₁`, as a sheaf of commutative rings. -/
noncomputable def sqZeroSheaf : TopCat.Sheaf CommRingCat.{u} X'.carrier :=
  ⟨S.sqRing, S.isSheaf_sqRing⟩

/-- The trivial square-zero extension `T = 𝒪'₂ ⋉ ℐ₁`, as a sheaf of rings. -/
noncomputable def sqZeroRing :
    Sheaf (Opens.grothendieckTopology X'.carrier) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X'.carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj S.sqZeroSheaf

/-- The ring of local sections of `T`. -/
noncomputable abbrev sqSections (V : Opens X'.carrier) : CommRingCat.{u} := S.sqRing.obj (op V)

/-- The section of `T` with the given ring and ideal components. -/
noncomputable def sqMk (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) : S.sqSections V := (a, m)

/-- The ring component of a section of `T`. -/
noncomputable def sqFst {V : Opens X'.carrier} (s : S.sqSections V) : S.O.obj (op V) := s.1

/-- The ideal component of a section of `T`. -/
noncomputable def sqSnd {V : Opens X'.carrier} (s : S.sqSections V) :
    (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V) := s.2

/-- Two sections of `T` with the same components agree. -/
theorem sq_ext {V : Opens X'.carrier} {s s' : S.sqSections V} (h₁ : S.sqFst s = S.sqFst s')
    (h₂ : S.sqSnd s = S.sqSnd s') : s = s' := TrivSqZeroExt.ext h₁ h₂

/-- The ring component of a section of `T` with prescribed components. -/
@[simp] theorem sqFst_mk (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    S.sqFst (S.sqMk V a m) = a := rfl

/-- The ideal component of a section of `T` with prescribed components. -/
@[simp] theorem sqSnd_mk (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    S.sqSnd (S.sqMk V a m) = m := rfl

/-- The ring component of zero. -/
@[simp] theorem sqFst_zero (V : Opens X'.carrier) : S.sqFst (0 : S.sqSections V) = 0 := rfl

/-- The ideal component of zero. -/
@[simp] theorem sqSnd_zero (V : Opens X'.carrier) : S.sqSnd (0 : S.sqSections V) = 0 := rfl

/-- The ring component of one. -/
@[simp] theorem sqFst_one (V : Opens X'.carrier) : S.sqFst (1 : S.sqSections V) = 1 := rfl

/-- The ideal component of one. -/
@[simp] theorem sqSnd_one (V : Opens X'.carrier) : S.sqSnd (1 : S.sqSections V) = 0 := rfl

/-- The ring component is additive. -/
@[simp] theorem sqFst_add {V : Opens X'.carrier} (s s' : S.sqSections V) :
    S.sqFst (s + s') = S.sqFst s + S.sqFst s' := rfl

/-- The ideal component is additive. -/
@[simp] theorem sqSnd_add {V : Opens X'.carrier} (s s' : S.sqSections V) :
    S.sqSnd (s + s') = S.sqSnd s + S.sqSnd s' := rfl

/-- The ring component is multiplicative. -/
@[simp] theorem sqFst_mul {V : Opens X'.carrier} (s s' : S.sqSections V) :
    S.sqFst (s * s') = S.sqFst s * S.sqFst s' := rfl

/-- `h^♯` on local sections, read in the ring at which `ℐ₁` is a module. -/
noncomputable def hSharpApp (V : Opens X'.carrier) (a : S.O.obj (op V)) :
    X'.presheaf.obj (op V) := (S.hSharp.app (op V)).hom a

/-- `h^♯` is additive on local sections. -/
theorem hSharpApp_add (V : Opens X'.carrier) (a a' : S.O.obj (op V)) :
    S.hSharpApp V (a + a') = S.hSharpApp V a + S.hSharpApp V a' :=
  map_add (S.hSharp.app (op V)).hom a a'

/-- `h^♯` is multiplicative on local sections. -/
theorem hSharpApp_mul (V : Opens X'.carrier) (a a' : S.O.obj (op V)) :
    S.hSharpApp V (a * a') = S.hSharpApp V a * S.hSharpApp V a' :=
  map_mul (S.hSharp.app (op V)).hom a a'

/-- `h^♯` preserves the unit. -/
theorem hSharpApp_one (V : Opens X'.carrier) : S.hSharpApp V 1 = 1 :=
  map_one (S.hSharp.app (op V)).hom

/-- `h^♯` preserves zero. -/
theorem hSharpApp_zero (V : Opens X'.carrier) : S.hSharpApp V 0 = 0 :=
  map_zero (S.hSharp.app (op V)).hom

/-- The action of `𝒪'₂` on the ideal of the first thickening is the action of `𝒪_{X'}` through
`h^♯`. -/
theorem smul_eq_hSharpApp_smul (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    a • m = S.hSharpApp V a • m := rfl

/-- The ideal component of a product in `T`, by the Leibniz rule of the square-zero
multiplication. -/
@[simp] theorem sqSnd_mul {V : Opens X'.carrier} (s s' : S.sqSections V) :
    S.sqSnd (s * s') = S.sqFst s • S.sqSnd s' + S.sqFst s' • S.sqSnd s := rfl

/-- The ideal component of a product in `T`, with the ring components acting through `h^♯`. -/
theorem sqSnd_mul' {V : Opens X'.carrier} (s s' : S.sqSections V) :
    S.sqSnd (s * s') =
      S.hSharpApp V (S.sqFst s) • S.sqSnd s' + S.hSharpApp V (S.sqFst s') • S.sqSnd s := by
  rw [S.sqSnd_mul, S.smul_eq_hSharpApp_smul, S.smul_eq_hSharpApp_smul]

/-- The inclusion of `ℐ₁` is linear over `𝒪'₂`, which acts through `h^♯`. -/
theorem idealIncl_hSharpApp_smul (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    idealIncl i V (S.hSharpApp V a • m) =
      S.hSharpApp V a * idealIncl i V m :=
  map_smul ((idealSheafι i).val.app (op V)).hom (S.hSharpApp V a) m

/-- The structure map `q : T ⟶ 𝒪_{X'}` on local sections: the image under `h^♯` of the ring
component minus the image in `𝒪_{X'}` of the ideal component. It is a ring homomorphism because
`ℐ₁` has square zero. -/
noncomputable def sqZeroProjHom (hi : IsFirstOrderThickening i) (V : Opens X'.carrier) :
    S.sqRing.obj (op V) ⟶ X'.presheaf.obj (op V) :=
  CommRingCat.ofHom
    ({ toFun := fun s => S.hSharpApp V (S.sqFst s) - idealIncl i V (S.sqSnd s)
       map_one' := by
         rw [S.sqFst_one, S.sqSnd_one, idealIncl_zero, sub_zero]
         exact S.hSharpApp_one V
       map_zero' := by
         rw [S.sqFst_zero, S.sqSnd_zero, idealIncl_zero, sub_zero]
         exact S.hSharpApp_zero V
       map_add' := fun s s' => by
         rw [S.sqFst_add, S.sqSnd_add, S.hSharpApp_add, idealIncl_add]
         abel
       map_mul' := fun s s' => by
         have hsq : idealIncl i V (S.sqSnd s) * idealIncl i V (S.sqSnd s') = 0 :=
           idealIncl_mul_idealIncl hi V _ _
         rw [S.sqFst_mul, S.sqSnd_mul', S.hSharpApp_mul, idealIncl_add,
           S.idealIncl_hSharpApp_smul,
           S.idealIncl_hSharpApp_smul, sub_mul, mul_sub, mul_sub, hsq]
         ring } : (S.sqRing.obj (op V) : Type u) →+* (X'.presheaf.obj (op V) : Type u))

/-- The structure map `q : T ⟶ 𝒪_{X'}` of the square-zero extension, as a morphism of sheaves
of commutative rings. -/
noncomputable def sqZeroProjCommRing (hi : IsFirstOrderThickening i) :
    S.sqZeroSheaf ⟶ X'.sheaf :=
  ObjectProperty.homMk
    { app := fun V => S.sqZeroProjHom hi V.unop
      naturality := fun {V W} g => by
        refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
        have h1 : (S.hSharp.app W).hom ((S.O.map g).hom (S.sqFst s)) =
            (X'.presheaf.map g).hom ((S.hSharp.app V).hom (S.sqFst s)) :=
          ConcreteCategory.congr_hom (S.hSharp.naturality g) (S.sqFst s)
        have h2 : idealIncl i W.unop
              ((Stacks.ClosedImmersion.idealSheaf i).val.map g (S.sqSnd s)) =
            (X'.presheaf.map g).hom (idealIncl i V.unop (S.sqSnd s)) :=
          PresheafOfModules.naturality_apply (idealSheafι i).val g (S.sqSnd s)
        change (S.hSharp.app W).hom ((S.O.map g).hom (S.sqFst s)) -
            idealIncl i W.unop
              ((Stacks.ClosedImmersion.idealSheaf i).val.map g (S.sqSnd s)) =
          (X'.presheaf.map g).hom
            ((S.hSharp.app V).hom (S.sqFst s) - idealIncl i V.unop (S.sqSnd s))
        rw [map_sub, h1, h2] }

/-- The structure map `q : T ⟶ 𝒪_{X'}` of the square-zero extension. -/
noncomputable def sqZeroProj (hi : IsFirstOrderThickening i) :
    S.sqZeroRing ⟶ structureSheafRing X' :=
  (sheafCompose (Opens.grothendieckTopology X'.carrier)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (S.sqZeroProjCommRing hi)

/-- The structure map of the square-zero extension, on local sections. -/
@[simp] theorem sqZeroProj_hom_app (hi : IsFirstOrderThickening i) (V : Opens X'.carrier)
    (s : S.sqSections V) :
    (S.sqZeroProj hi).hom.app (op V) s =
      S.hSharpApp V (S.sqFst s) - idealIncl i V (S.sqSnd s) := rfl

/-- The structure map of the second thickening is `h^♯` followed by that of the first, on
local sections. -/
theorem iSharpApp_hSharpApp (V : Opens X'.carrier) (a : S.O.obj (op V)) :
    iSharpApp i V (S.hSharpApp V a) = iSharpApp S.hom V a := rfl

/-- **The structure map of the square-zero extension is locally surjective.** A section of
`𝒪_{X'}` maps into `𝒪_X`, lifts locally along the structure map of the second thickening, and
the difference lies in `ℐ₁`. -/
theorem sqZeroProj_locallySurjective (hi : IsFirstOrderThickening i) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X'.carrier)
      (S.sqZeroProj hi).hom := by
  constructor
  intro V s₀
  set s : X'.presheaf.obj (op V) := s₀ with hsdef
  refine (Opens.grothendieckTopology X'.carrier).superset_covering ?_
    ((isLocallySurjective_of_isThickening S.hom S.firstOrder.1).imageSieve_mem
      (iSharpApp i V s))
  rintro W g ⟨a₀, ha₀⟩
  set a : (S.O.obj (op W) : Type u) := a₀ with hadef
  have ha : iSharpApp S.hom W a =
      (structureSheafRing X).obj.map ((opensMap i).map g).op (iSharpApp i V s) := ha₀
  set s' : X'.presheaf.obj (op W) := X'.presheaf.map g.op s with hs'
  have hzero : iSharpApp i W (s' - S.hSharpApp W a) = 0 := by
    rw [iSharpApp_sub, S.iSharpApp_hSharpApp, ha, hs', iSharpApp_naturality, sub_self]
  obtain ⟨m, hm⟩ := exists_idealSheaf_section_of_app_eq_zero i W _ hzero
  have hm' : idealIncl i W m = s' - S.hSharpApp W a := hm
  refine ⟨S.sqMk W a (-m), ?_⟩
  change S.hSharpApp W (S.sqFst (S.sqMk W a (-m))) -
    idealIncl i W (S.sqSnd (S.sqMk W a (-m))) = s'
  rw [S.sqFst_mk, S.sqSnd_mk, idealIncl_neg, sub_neg_eq_add, hm']
  abel

/-- A section of `T` killed by `q` has ring component in `ℐ₂`. -/
theorem exists_ideal_of_sqZeroProj_eq_zero (hi : IsFirstOrderThickening i)
    (V : Opens X'.carrier) (s : S.sqSections V)
    (hs : (S.sqZeroProj hi).hom.app (op V) s = 0) :
    ∃ b : S.ideal.val.obj (op V), S.inclTwo V b = S.sqFst s := by
  have heq : S.hSharpApp V (S.sqFst s) = idealIncl i V (S.sqSnd s) := sub_eq_zero.1 hs
  have hring : iSharpApp S.hom V (S.sqFst s) = 0 := by
    rw [← S.iSharpApp_hSharpApp, heq]
    exact iSharpApp_idealIncl i V (S.sqSnd s)
  obtain ⟨b, hb⟩ := exists_idealSheaf_section_of_app_eq_zero S.hom V _ hring
  exact ⟨b, hb⟩

/-- The ideal component of a section of `T` killed by `q` is the image of its ring component. -/
theorem idealIncl_sqSnd_of_sqZeroProj_eq_zero (hi : IsFirstOrderThickening i)
    (V : Opens X'.carrier) (s : S.sqSections V)
    (hs : (S.sqZeroProj hi).hom.app (op V) s = 0) :
    idealIncl i V (S.sqSnd s) = S.hSharpApp V (S.sqFst s) :=
  (sub_eq_zero.1 hs).symm

/-- Conversely, a section of `T` whose ring component is a section of `ℐ₂` and whose ideal
component has the same image in `𝒪_{X'}` is killed by `q`. -/
theorem sqZeroProj_eq_zero_of_ideal (hi : IsFirstOrderThickening i) (V : Opens X'.carrier)
    (b : S.ideal.val.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (hm : idealIncl i V m = S.hSharpApp V (S.inclTwo V b)) :
    (S.sqZeroProj hi).hom.app (op V) (S.sqMk V (S.inclTwo V b) m) = 0 := by
  change S.hSharpApp V (S.sqFst (S.sqMk V (S.inclTwo V b) m)) -
    idealIncl i V (S.sqSnd (S.sqMk V (S.inclTwo V b) m)) = 0
  rw [S.sqFst_mk, S.sqSnd_mk, hm, sub_self]

/-- The section of `T` with zero ring component and ideal component `-m` is carried by `q` to
the image of `m` in `𝒪_{X'}`. -/
theorem sqZeroProj_mk_zero_neg (hi : IsFirstOrderThickening i) (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    (S.sqZeroProj hi).hom.app (op V) (S.sqMk V 0 (-m)) = idealIncl i V m := by
  change S.hSharpApp V (S.sqFst (S.sqMk V 0 (-m))) -
    idealIncl i V (S.sqSnd (S.sqMk V 0 (-m))) = idealIncl i V m
  rw [S.sqFst_mk, S.sqSnd_mk, S.hSharpApp_zero, idealIncl_neg, zero_sub, neg_neg]

/-- Restriction of scalars along `q` is fully faithful, since `q` is locally surjective. -/
noncomputable def sqZeroRestrictFullyFaithful (hi : IsFirstOrderThickening i) :
    (SheafOfModules.restrictScalars.{u} (S.sqZeroProj hi)).FullyFaithful :=
  letI := S.sqZeroProj_locallySurjective hi
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective.{u} _

/-- Local sections of a sheaf of modules over `T` form a module over the *commutative* ring of
local sections of `T`, which is the ring at which the sections of `T` are named above. -/
@[instance_reducible]
noncomputable def sectionsModuleOverSq (M : SheafOfModules.{u} S.sqZeroRing)
    (V : Opens X'.carrier) : Module (S.sqSections V) (M.val.obj (op V)) :=
  (M.val.obj (op V)).isModule

attribute [local instance] sectionsModuleOverSq

/-! ### Comparing the two direct images

The two thickenings have the same underlying continuous map, so `i_* 𝒩` and `(i₂)_* 𝒩` have the
same sections over every open; only the acting sheaf of rings differs. -/

/-- Local sections of a sheaf of modules over the second thickened structure sheaf form a module
over the sections of `𝒪'₂`. -/
@[instance_reducible]
noncomputable def sectionsModuleOverTwoSpace (M : SheafOfModules.{u} (structureSheafRing S.space))
    (V : Opens X'.carrier) : Module (S.O.obj (op V)) (M.val.obj (op V)) :=
  (M.val.obj (op V)).isModule

attribute [local instance] sectionsModuleOverTwoSpace

/-- A local section of `(i₂)_* 𝒩` read as a local section of `i_* 𝒩`. -/
noncomputable def ofSecond (N : SheafOfModules.{u} (structureSheafRing X))
    (V : Opens X'.carrier) (y : ((modulePushforward S.hom).obj N).val.obj (op V)) :
    ((modulePushforward i).obj N).val.obj (op V) := y

/-- A local section of `i_* 𝒩` read as a local section of `(i₂)_* 𝒩`. -/
noncomputable def toSecond (N : SheafOfModules.{u} (structureSheafRing X))
    (V : Opens X'.carrier) (y : ((modulePushforward i).obj N).val.obj (op V)) :
    ((modulePushforward S.hom).obj N).val.obj (op V) := y

/-- The two readings are additive. -/
theorem ofSecond_add (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (y y' : ((modulePushforward S.hom).obj N).val.obj (op V)) :
    S.ofSecond N V (y + y') = S.ofSecond N V y + S.ofSecond N V y' := rfl

/-- The second reading is additive. -/
theorem toSecond_add (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (y y' : ((modulePushforward i).obj N).val.obj (op V)) :
    S.toSecond N V (y + y') = S.toSecond N V y + S.toSecond N V y' := rfl

/-- The second reading kills zero. -/
theorem toSecond_zero (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier) :
    S.toSecond N V 0 = 0 := rfl

/-- The second reading respects differences. -/
theorem toSecond_sub (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (y y' : ((modulePushforward i).obj N).val.obj (op V)) :
    S.toSecond N V (y - y') = S.toSecond N V y - S.toSecond N V y' := rfl

/-- The first reading respects differences. -/
theorem ofSecond_sub (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (y y' : ((modulePushforward S.hom).obj N).val.obj (op V)) :
    S.ofSecond N V (y - y') = S.ofSecond N V y - S.ofSecond N V y' := rfl

/-- The `𝒪_{X'}`-action through `h^♯` on `i_* 𝒩` is the `𝒪'₂`-action on `(i₂)_* 𝒩`: both are the
`𝒪_X`-action through the structure map of the second thickening. -/
theorem toSecond_smul (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (a : S.O.obj (op V)) (y : ((modulePushforward i).obj N).val.obj (op V)) :
    S.toSecond N V (S.hSharpApp V a • y) = a • S.toSecond N V y := rfl

/-- The same identification, read in the other direction. -/
theorem ofSecond_smul (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (a : S.O.obj (op V)) (y : ((modulePushforward S.hom).obj N).val.obj (op V)) :
    S.ofSecond N V (a • y) = S.hSharpApp V a • S.ofSecond N V y := rfl

/-- The two readings commute with restriction. -/
theorem ofSecond_restrict (N : SheafOfModules.{u} (structureSheafRing X))
    {V W : Opens X'.carrier} (g : W ⟶ V)
    (y : ((modulePushforward S.hom).obj N).val.obj (op V)) :
    S.ofSecond N W (((modulePushforward S.hom).obj N).val.map g.op y) =
      ((modulePushforward i).obj N).val.map g.op (S.ofSecond N V y) := rfl

/-- The second reading commutes with restriction. -/
theorem toSecond_restrict (N : SheafOfModules.{u} (structureSheafRing X))
    {V W : Opens X'.carrier} (g : W ⟶ V)
    (y : ((modulePushforward i).obj N).val.obj (op V)) :
    S.toSecond N W (((modulePushforward i).obj N).val.map g.op y) =
      ((modulePushforward S.hom).obj N).val.map g.op (S.toSecond N V y) := rfl

end SecondThickening

/-! ### The data of the remark, and the twisted module structure on the pushout -/

attribute [local instance] sectionsModuleOverSpace sectionsModuleOverBase

/-- The data of the remark: an `𝒪_X`-module `ℱ`, kernel modules for the two thickenings with
their prescribed canonical maps, and a map of kernel modules making the square with the induced
map of defining ideals commute. -/
structure PushoutDescentData {i : X ⟶ X'} (S : SecondThickening i) where
  /-- The `𝒪_X`-module whose extensions are compared. -/
  F : SheafOfModules.{u} (structureSheafRing X)
  /-- The kernel module for the first thickening. -/
  K₁ : SheafOfModules.{u} (structureSheafRing X)
  /-- The kernel module for the second thickening. -/
  K₂ : SheafOfModules.{u} (structureSheafRing X)
  /-- The prescribed canonical map `c₁ : i^* ℐ₁ ⊗_{𝒪_X} ℱ ⟶ 𝒦₁`. -/
  c₁ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K₁
  /-- The prescribed canonical map `c₂ : i₂^* ℐ₂ ⊗_{𝒪_X} ℱ ⟶ 𝒦₂`. -/
  c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback S.hom))).obj (F)) ⟶ K₂
  /-- The map `κ : 𝒦₂ ⟶ 𝒦₁` of kernel modules. -/
  kernelMap : K₂ ⟶ K₁
  /-- The square formed by the two canonical maps, the map of kernel modules and the induced map
  of defining ideals commutes, read on local pure tensors. The section `m` of `ℐ₁` is required to
  have the same image in `𝒪_{X'}` as the section `b` of `ℐ₂`, which says exactly that `m` is the
  image of `b` under the map `ℐ₂ ⟶ ℐ₁` induced by `h^♯`. -/
  comm : ∀ (V : Opens X'.carrier) (b : S.ideal.val.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)),
    idealIncl i V m = S.hSharpApp V (S.inclTwo V b) →
      ∀ y : ((modulePushforward S.hom).obj F).val.obj (op V),
        (descendedActionOfMap S.hom F K₁ (c₂ ≫ kernelMap)).val.app (op V)
            (toTensorSheafSection S.space (Stacks.ClosedImmersion.idealSheaf S.hom)
              ((modulePushforward S.hom).obj F) (op V)
              (b ⊗ₜ[S.space.presheaf.obj (op V)] y)) =
          S.toSecond K₁ V ((descendedActionOfMap i F K₁ c₁).val.app (op V)
            (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
              ((modulePushforward i).obj F) (op V)
              (m ⊗ₜ[X'.presheaf.obj (op V)] S.ofSecond F V y)))

namespace PushoutDescentData

variable {i : X ⟶ X'} {S : SecondThickening i} (dat : PushoutDescentData S)
  (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.hom).obj dat.F)
    ((modulePushforward S.hom).obj dat.K₂) 0)

attribute [local instance] sectionsModuleOverSpace sectionsModuleOverBase
  SecondThickening.sectionsModuleOverTwo SecondThickening.sectionsModuleOverTwoSpace
  SecondThickening.sectionsModuleOverSq

/-- The extension of `ℱ` by `𝒦₁` over the second thickening obtained by pushing the given
extension out along `κ`. -/
noncomputable abbrev pushoutExt :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.hom).obj dat.F)
      ((modulePushforward S.hom).obj dat.K₁) 0 :=
  pushoutExtension S.hom dat.F dat.K₁ dat.K₂ dat.kernelMap E₂

/-- The pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁`, an `𝒪'₂`-module. -/
noncomputable abbrev pushoutMod : SheafOfModules.{u} (structureSheafRing S.space) :=
  (dat.pushoutExt E₂).Z.left

/-- The image in the pushout of a local section of `𝒦₁`. -/
noncomputable def inclSection (V : Opens X'.carrier)
    (k : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    (dat.pushoutMod E₂).val.obj (op V) := (dat.pushoutExt E₂).f.val.app (op V) k

/-- The image in `ℱ` of a local section of the pushout. -/
noncomputable def quotSection (V : Opens X'.carrier) (p : (dat.pushoutMod E₂).val.obj (op V)) :
    ((modulePushforward S.hom).obj dat.F).val.obj (op V) :=
  (dat.pushoutExt E₂).g.val.app (op V) p

/-- The inclusion of `𝒦₁` into the pushout is additive. -/
theorem inclSection_add (V : Opens X'.carrier)
    (k k' : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    dat.inclSection E₂ V (k + k') = dat.inclSection E₂ V k + dat.inclSection E₂ V k' :=
  map_add ((dat.pushoutExt E₂).f.val.app (op V)).hom k k'

/-- The inclusion of `𝒦₁` into the pushout kills zero. -/
theorem inclSection_zero (V : Opens X'.carrier) :
    dat.inclSection E₂ V 0 = 0 :=
  map_zero ((dat.pushoutExt E₂).f.val.app (op V)).hom

/-- The inclusion of `𝒦₁` into the pushout respects differences. -/
theorem inclSection_sub (V : Opens X'.carrier)
    (k k' : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    dat.inclSection E₂ V (k - k') = dat.inclSection E₂ V k - dat.inclSection E₂ V k' :=
  map_sub ((dat.pushoutExt E₂).f.val.app (op V)).hom k k'

/-- The inclusion of `𝒦₁` into the pushout is `𝒪'₂`-linear. -/
theorem inclSection_smul (V : Opens X'.carrier) (a : S.O.obj (op V))
    (k : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    dat.inclSection E₂ V (a • k) = a • dat.inclSection E₂ V k :=
  map_smul ((dat.pushoutExt E₂).f.val.app (op V)).hom a k

/-- The inclusion of `𝒦₁` into the pushout commutes with restriction. -/
theorem inclSection_restrict {V W : Opens X'.carrier} (g : W ⟶ V)
    (k : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    dat.inclSection E₂ W (((modulePushforward S.hom).obj dat.K₁).val.map g.op k) =
      (dat.pushoutMod E₂).val.map g.op (dat.inclSection E₂ V k) :=
  PresheafOfModules.naturality_apply (dat.pushoutExt E₂).f.val g.op k

/-- The quotient map onto `ℱ` is additive. -/
theorem quotSection_add (V : Opens X'.carrier) (p p' : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.quotSection E₂ V (p + p') = dat.quotSection E₂ V p + dat.quotSection E₂ V p' :=
  map_add ((dat.pushoutExt E₂).g.val.app (op V)).hom p p'

/-- The quotient map onto `ℱ` respects differences. -/
theorem quotSection_sub (V : Opens X'.carrier) (p p' : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.quotSection E₂ V (p - p') = dat.quotSection E₂ V p - dat.quotSection E₂ V p' :=
  map_sub ((dat.pushoutExt E₂).g.val.app (op V)).hom p p'

/-- The quotient map onto `ℱ` is `𝒪'₂`-linear. -/
theorem quotSection_smul (V : Opens X'.carrier) (a : S.O.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.quotSection E₂ V (a • p) = a • dat.quotSection E₂ V p :=
  map_smul ((dat.pushoutExt E₂).g.val.app (op V)).hom a p

/-- The quotient map onto `ℱ` commutes with restriction. -/
theorem quotSection_restrict {V W : Opens X'.carrier} (g : W ⟶ V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.quotSection E₂ W ((dat.pushoutMod E₂).val.map g.op p) =
      ((modulePushforward S.hom).obj dat.F).val.map g.op (dat.quotSection E₂ V p) :=
  PresheafOfModules.naturality_apply (dat.pushoutExt E₂).g.val g.op p

/-- The quotient map onto `ℱ` kills the sections coming from `𝒦₁`. -/
theorem quotSection_inclSection (V : Opens X'.carrier)
    (k : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    dat.quotSection E₂ V (dat.inclSection E₂ V k) = 0 :=
  sheafOfModules_hom_app_congr
    (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero (dat.pushoutExt E₂)) (op V) k

/-- The image in `ℐ₁ ⊗_{𝒪_{X'}} i_* ℱ` of a pure tensor of local sections. -/
noncomputable def tensorMk (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj ((Stacks.ClosedImmersion.idealSheaf i))).obj (((modulePushforward i).obj dat.F)))).val.obj (op V) :=
  toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
    ((modulePushforward i).obj dat.F) (op V) (m ⊗ₜ[X'.presheaf.obj (op V)] y)

/-- A pure tensor is additive in its ideal factor. -/
theorem tensorMk_add_left (V : Opens X'.carrier)
    (m m' : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.tensorMk V (m + m') y = dat.tensorMk V m y + dat.tensorMk V m' y :=
  (congrArg (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
        ((modulePushforward i).obj dat.F) (op V))
      (TensorProduct.add_tmul (R := X'.presheaf.obj (op V)) m m' y)).trans
    (map_add ((sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf) ((Stacks.ClosedImmersion.idealSheaf i).val) (((modulePushforward i).obj dat.F).val)))).app (op V)).hom _ _)

/-- A pure tensor is additive in its module factor. -/
theorem tensorMk_add_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y y' : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.tensorMk V m (y + y') = dat.tensorMk V m y + dat.tensorMk V m y' :=
  (congrArg (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
        ((modulePushforward i).obj dat.F) (op V))
      (TensorProduct.tmul_add (R := X'.presheaf.obj (op V)) m y y')).trans
    (map_add ((sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf) ((Stacks.ClosedImmersion.idealSheaf i).val) (((modulePushforward i).obj dat.F).val)))).app (op V)).hom _ _)

/-- A pure tensor respects differences in its module factor. -/
theorem tensorMk_sub_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y y' : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.tensorMk V m (y - y') = dat.tensorMk V m y - dat.tensorMk V m y' :=
  (congrArg (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
        ((modulePushforward i).obj dat.F) (op V))
      (TensorProduct.tmul_sub (R := X'.presheaf.obj (op V)) m y y')).trans
    (map_sub ((sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf) ((Stacks.ClosedImmersion.idealSheaf i).val) (((modulePushforward i).obj dat.F).val)))).app (op V)).hom _ _)

/-- A pure tensor with zero ideal factor vanishes. -/
theorem tensorMk_zero_left (V : Opens X'.carrier)
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.tensorMk V 0 y = 0 :=
  (congrArg (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
        ((modulePushforward i).obj dat.F) (op V))
      (TensorProduct.zero_tmul (R := X'.presheaf.obj (op V))
        ((Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) y)).trans
    (map_zero ((sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf) ((Stacks.ClosedImmersion.idealSheaf i).val) (((modulePushforward i).obj dat.F).val)))).app (op V)).hom)

/-- A pure tensor with zero module factor vanishes. -/
theorem tensorMk_zero_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    dat.tensorMk V m 0 = 0 :=
  (congrArg (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
        ((modulePushforward i).obj dat.F) (op V))
      (TensorProduct.tmul_zero (R := X'.presheaf.obj (op V))
        (((modulePushforward i).obj dat.F).val.obj (op V)) m)).trans
    (map_zero ((sheafifyUnit X' ((PresheafOfModules.tensorObj (O := (X').presheaf) ((Stacks.ClosedImmersion.idealSheaf i).val) (((modulePushforward i).obj dat.F).val)))).app (op V)).hom)

/-- A scalar on the ideal factor of a pure tensor comes out. -/
theorem tensorMk_smul_left (V : Opens X'.carrier) (r : X'.presheaf.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.tensorMk V (r • m) y = r • dat.tensorMk V m y :=
  toTensorSheafSection_smul_left X' (Stacks.ClosedImmersion.idealSheaf i)
    ((modulePushforward i).obj dat.F) V r m y

/-- A scalar on the module factor of a pure tensor comes out. -/
theorem tensorMk_smul_right (V : Opens X'.carrier) (r : X'.presheaf.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.tensorMk V m (r • y) = r • dat.tensorMk V m y :=
  toTensorSheafSection_smul_right X' (Stacks.ClosedImmersion.idealSheaf i)
    ((modulePushforward i).obj dat.F) V r m y

/-- A pure tensor commutes with restriction. -/
theorem tensorMk_restrict {V W : Opens X'.carrier} (g : W ⟶ V)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj ((Stacks.ClosedImmersion.idealSheaf i))).obj (((modulePushforward i).obj dat.F)))).val.map g.op (dat.tensorMk V m y) =
      dat.tensorMk W ((Stacks.ClosedImmersion.idealSheaf i).val.map g.op m)
        (((modulePushforward i).obj dat.F).val.map g.op y) :=
  toTensorSheafSection_restrict X' (Stacks.ClosedImmersion.idealSheaf i)
    ((modulePushforward i).obj dat.F) g.le m y

/-- The prescribed canonical map of the first thickening, applied to a pure tensor of local
sections. -/
noncomputable def actOne (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    ((modulePushforward i).obj dat.K₁).val.obj (op V) :=
  (descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V) (dat.tensorMk V m y)

/-- `c₁` is additive in the ideal factor. -/
theorem actOne_add_left (V : Opens X'.carrier)
    (m m' : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.actOne V (m + m') y = dat.actOne V m y + dat.actOne V m' y :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_add_left V m m' y)).trans
    (map_add ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom _ _)

/-- `c₁` is additive in the module factor. -/
theorem actOne_add_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y y' : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.actOne V m (y + y') = dat.actOne V m y + dat.actOne V m y' :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_add_right V m y y')).trans
    (map_add ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom _ _)

/-- `c₁` respects differences in the module factor. -/
theorem actOne_sub_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y y' : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.actOne V m (y - y') = dat.actOne V m y - dat.actOne V m y' :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_sub_right V m y y')).trans
    (map_sub ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom _ _)

/-- `c₁` vanishes on a zero ideal factor. -/
theorem actOne_zero_left (V : Opens X'.carrier)
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.actOne V 0 y = 0 :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_zero_left V y)).trans
    (map_zero ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom)

/-- `c₁` vanishes on a zero module factor. -/
theorem actOne_zero_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V)) :
    dat.actOne V m 0 = 0 :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_zero_right V m)).trans
    (map_zero ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom)

/-- `c₁` is linear in the ideal factor. -/
theorem actOne_smul_left (V : Opens X'.carrier) (r : X'.presheaf.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.actOne V (r • m) y = r • dat.actOne V m y :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_smul_left V r m y)).trans
    (map_smul ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom r _)

/-- `c₁` is linear in the module factor. -/
theorem actOne_smul_right (V : Opens X'.carrier) (r : X'.presheaf.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    dat.actOne V m (r • y) = r • dat.actOne V m y :=
  (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V))
      (dat.tensorMk_smul_right V r m y)).trans
    (map_smul ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op V)).hom r _)

/-- `c₁` commutes with restriction. -/
theorem actOne_restrict {V W : Opens X'.carrier} (g : W ⟶ V)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (y : ((modulePushforward i).obj dat.F).val.obj (op V)) :
    ((modulePushforward i).obj dat.K₁).val.map g.op (dat.actOne V m y) =
      dat.actOne W ((Stacks.ClosedImmersion.idealSheaf i).val.map g.op m)
        (((modulePushforward i).obj dat.F).val.map g.op y) :=
  (PresheafOfModules.naturality_apply (descendedActionOfMap i dat.F dat.K₁ dat.c₁).val g.op
      (dat.tensorMk V m y)).symm.trans
    (congrArg ((descendedActionOfMap i dat.F dat.K₁ dat.c₁).val.app (op W))
      (dat.tensorMk_restrict g m y))

/-- The twisting term `c₁(m ⊗ p̄)`, read in the pushout: the correction by which the action of
`𝒪'₂` is modified to an action of `T = 𝒪'₂ ⋉ ℐ₁`. -/
noncomputable def twist (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) : (dat.pushoutMod E₂).val.obj (op V) :=
  dat.inclSection E₂ V (S.toSecond dat.K₁ V
    (dat.actOne V m (S.ofSecond dat.F V (dat.quotSection E₂ V p))))

/-- The twisting term, unfolded. -/
theorem twist_eq (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V m p = dat.inclSection E₂ V (S.toSecond dat.K₁ V
      (dat.actOne V m (S.ofSecond dat.F V (dat.quotSection E₂ V p)))) := rfl

/-- The twisting term is additive in the ideal section. -/
theorem twist_add_left (V : Opens X'.carrier)
    (m m' : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V (m + m') p = dat.twist E₂ V m p + dat.twist E₂ V m' p := by
  simp only [dat.twist_eq]
  rw [dat.actOne_add_left, S.toSecond_add, dat.inclSection_add]

/-- The twisting term vanishes on the zero ideal section. -/
theorem twist_zero_left (V : Opens X'.carrier) (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V 0 p = 0 := by
  simp only [dat.twist_eq]
  rw [dat.actOne_zero_left, S.toSecond_zero, dat.inclSection_zero]

/-- The twisting term is odd in the ideal section. -/
theorem twist_neg_left (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V (-m) p = -dat.twist E₂ V m p := by
  have h := dat.twist_add_left E₂ V m (-m) p
  rw [add_neg_cancel, dat.twist_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- The twisting term is additive in the pushout section. -/
theorem twist_add_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p p' : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V m (p + p') = dat.twist E₂ V m p + dat.twist E₂ V m p' := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_add, S.ofSecond_add, dat.actOne_add_right, S.toSecond_add,
    dat.inclSection_add]

/-- The twisting term respects differences of pushout sections. -/
theorem twist_sub_right (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p p' : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V m (p - p') = dat.twist E₂ V m p - dat.twist E₂ V m p' := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_sub, S.ofSecond_sub, dat.actOne_sub_right, S.toSecond_sub,
    dat.inclSection_sub]

/-- The twisting term is linear in the ideal section over `𝒪'₂`, which acts through `h^♯`. -/
theorem twist_smul_left (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V (S.hSharpApp V a • m) p = a • dat.twist E₂ V m p := by
  simp only [dat.twist_eq]
  rw [dat.actOne_smul_left, S.toSecond_smul, dat.inclSection_smul]

/-- Moving a scalar from the pushout section to the ideal section leaves the twisting term
unchanged. -/
theorem twist_smul_right (V : Opens X'.carrier) (a : S.O.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V m (a • p) = a • dat.twist E₂ V m p := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_smul, S.ofSecond_smul, dat.actOne_smul_right, S.toSecond_smul,
    dat.inclSection_smul]

/-- The twisting term vanishes on sections coming from `𝒦₁`; in particular it is killed by
twisting again. This is the square-zero condition making the twisted action associative. -/
theorem twist_inclSection (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (k : ((modulePushforward S.hom).obj dat.K₁).val.obj (op V)) :
    dat.twist E₂ V m (dat.inclSection E₂ V k) = 0 := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_inclSection, show S.ofSecond dat.F V 0 = 0 from rfl,
    dat.actOne_zero_right, S.toSecond_zero, dat.inclSection_zero]

/-- The twisting term is killed by twisting. -/
theorem twist_twist (V : Opens X'.carrier)
    (m m' : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twist E₂ V m (dat.twist E₂ V m' p) = 0 :=
  dat.twist_inclSection E₂ V m _

/-- The twisting term is killed by the quotient map onto `ℱ`. -/
theorem quotSection_twist (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.quotSection E₂ V (dat.twist E₂ V m p) = 0 :=
  dat.quotSection_inclSection E₂ V _

/-- Restriction of a local section of the pushout, with its type named so that the restriction
lemmas below are stated in a position `rw` can act on. -/
noncomputable def restSection {V W : Opens X'.carrier} (g : W ⟶ V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) : (dat.pushoutMod E₂).val.obj (op W) :=
  (dat.pushoutMod E₂).val.map g.op p

/-- Restriction of sections of the pushout respects differences. -/
theorem restSection_sub {V W : Opens X'.carrier} (g : W ⟶ V)
    (p p' : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.restSection E₂ g (p - p') = dat.restSection E₂ g p - dat.restSection E₂ g p' :=
  map_sub ((dat.pushoutMod E₂).val.map g.op).hom p p'

/-- Restriction of sections of the pushout is semilinear. -/
theorem restSection_smul {V W : Opens X'.carrier} (g : W ⟶ V) (a : S.O.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.restSection E₂ g (a • p) = (S.O.map g.op).hom a • dat.restSection E₂ g p :=
  (dat.pushoutMod E₂).val.map_smul g.op a p

/-- The twisting term commutes with restriction. -/
theorem twist_restrict {V W : Opens X'.carrier} (g : W ⟶ V)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.restSection E₂ g (dat.twist E₂ V m p) =
      dat.twist E₂ W ((Stacks.ClosedImmersion.idealSheaf i).val.map g.op m)
        (dat.restSection E₂ g p) := by
  change (dat.pushoutMod E₂).val.map g.op (dat.twist E₂ V m p) = _
  simp only [dat.twist_eq]
  rw [← dat.inclSection_restrict, ← S.toSecond_restrict, dat.actOne_restrict,
    ← S.ofSecond_restrict, ← dat.quotSection_restrict]
  rfl

/-- The twisted action of a local section of `T = 𝒪'₂ ⋉ ℐ₁` on a local section of the pushout:
the action of the ring component, corrected by the twisting term of the ideal component. -/
noncomputable def twistedSmul (V : Opens X'.carrier) (s : S.sqSections V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) : (dat.pushoutMod E₂).val.obj (op V) :=
  S.sqFst s • p - dat.twist E₂ V (S.sqSnd s) p

/-- The twisted action, unfolded. -/
theorem twistedSmul_eq (V : Opens X'.carrier) (s : S.sqSections V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twistedSmul E₂ V s p = S.sqFst s • p - dat.twist E₂ V (S.sqSnd s) p := rfl

/-- The twisted action is additive in the pushout section. -/
theorem twistedSmul_add_right (V : Opens X'.carrier) (s : S.sqSections V)
    (p p' : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twistedSmul E₂ V s (p + p') =
      dat.twistedSmul E₂ V s p + dat.twistedSmul E₂ V s p' := by
  simp only [dat.twistedSmul_eq]
  rw [smul_add, dat.twist_add_right]
  abel

/-- The twisted action is additive in the section of `T`. -/
theorem twistedSmul_add_left (V : Opens X'.carrier) (s s' : S.sqSections V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twistedSmul E₂ V (s + s') p =
      dat.twistedSmul E₂ V s p + dat.twistedSmul E₂ V s' p := by
  simp only [dat.twistedSmul_eq, S.sqFst_add, S.sqSnd_add]
  rw [add_smul, dat.twist_add_left]
  abel

/-- The twisted action is associative: this is the Leibniz rule for the ideal component of a
product in `T` together with the vanishing of the twisting term on `𝒦₁`. -/
theorem twistedSmul_mul (V : Opens X'.carrier) (s s' : S.sqSections V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twistedSmul E₂ V (s * s') p =
      dat.twistedSmul E₂ V s (dat.twistedSmul E₂ V s' p) := by
  simp only [dat.twistedSmul_eq, S.sqFst_mul, S.sqSnd_mul']
  rw [mul_smul, dat.twist_add_left, dat.twist_smul_left, dat.twist_smul_left, smul_sub,
    dat.twist_sub_right, dat.twist_twist, sub_zero, dat.twist_smul_right]
  abel

/-- The unit of `T` acts as the identity. -/
theorem twistedSmul_one (V : Opens X'.carrier) (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twistedSmul E₂ V 1 p = p := by
  simp only [dat.twistedSmul_eq, S.sqFst_one, S.sqSnd_one]
  rw [one_smul, dat.twist_zero_left, sub_zero]

/-- The twisted action makes the local sections of the pushout a module over the local sections
of `T = 𝒪'₂ ⋉ ℐ₁`. -/
@[instance_reducible]
noncomputable def twistedModule (V : Opens X'.carrier) :
    Module (S.sqZeroRing.obj.obj (op V)) ((dat.pushoutMod E₂).val.obj (op V)) :=
  Deformation.ToposThickening.moduleOfAxioms (dat.twistedSmul E₂ V)
    (dat.twistedSmul_add_right E₂ V) (dat.twistedSmul_add_left E₂ V)
    (dat.twistedSmul_mul E₂ V) (dat.twistedSmul_one E₂ V)

/-- The twisted action is semilinear for restriction. -/
theorem twistedSmul_restrict {V W : Opens X'.carrier} (g : W ⟶ V) (s : S.sqSections V)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.restSection E₂ g (dat.twistedSmul E₂ V s p) =
      dat.twistedSmul E₂ W ((S.sqRing.map g.op).hom s) (dat.restSection E₂ g p) := by
  simp only [dat.twistedSmul_eq]
  rw [dat.restSection_sub, dat.restSection_smul, dat.twist_restrict]
  rfl

/-- The pushout with its twisted action, as a presheaf of modules over `T = 𝒪'₂ ⋉ ℐ₁`. -/
noncomputable def twistedPresheaf : PresheafOfModules.{u} S.sqZeroRing.obj :=
  letI _inst : ∀ U : (Opens X'.carrier)ᵒᵖ, Module (S.sqZeroRing.obj.obj U)
      ((dat.pushoutMod E₂).val.presheaf.obj U) := fun U => dat.twistedModule E₂ U.unop
  PresheafOfModules.ofPresheaf (dat.pushoutMod E₂).val.presheaf
    (fun {_ _} f s p => dat.twistedSmul_restrict E₂ f.unop s p)

/-- The pushout with its twisted action, as a sheaf of modules over `T = 𝒪'₂ ⋉ ℐ₁`. -/
noncomputable def twistedSheaf : SheafOfModules.{u} S.sqZeroRing where
  val := dat.twistedPresheaf E₂
  isSheaf := (dat.pushoutMod E₂).isSheaf

/-- The ideal of the first thickening annihilates a direct image along `i`. -/
theorem idealIncl_smul_pushforward (N : SheafOfModules.{u} (structureSheafRing X))
    (V : Opens X'.carrier) (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (k : ((modulePushforward i).obj N).val.obj (op V)) :
    idealIncl i V m • k = 0 := by
  have h : idealIncl i V m • k =
      iSharpApp i V (idealIncl i V m) •
        (show N.val.obj (op ((opensMap i).obj V)) from k) := rfl
  rw [h, iSharpApp_idealIncl, zero_smul]
  rfl

/-- The action of `T` on a direct image along `i`, through `q`, is the action of its ring
component through `h^♯`: the ideal component acts as zero. -/
theorem sqZeroProj_smul_pushforward (hi : IsFirstOrderThickening i)
    (N : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (r : S.sqSections V) (k : ((modulePushforward i).obj N).val.obj (op V)) :
    (S.sqZeroProj hi).hom.app (op V) r • k = S.hSharpApp V (S.sqFst r) • k :=
  calc (S.sqZeroProj hi).hom.app (op V) r • k
      = (S.hSharpApp V (S.sqFst r) - idealIncl i V (S.sqSnd r)) • k := rfl
    _ = S.hSharpApp V (S.sqFst r) • k - idealIncl i V (S.sqSnd r) • k := sub_smul _ _ _
    _ = S.hSharpApp V (S.sqFst r) • k - 0 :=
        congrArg (fun z => S.hSharpApp V (S.sqFst r) • k - z)
          (idealIncl_smul_pushforward N V (S.sqSnd r) k)
    _ = S.hSharpApp V (S.sqFst r) • k := sub_zero _

/-- The inclusion of `𝒦₁` into the pushout is linear for the twisted action. -/
theorem inclSection_smul_sq (hi : IsFirstOrderThickening i) (V : Opens X'.carrier)
    (r : S.sqSections V) (k : ((modulePushforward i).obj dat.K₁).val.obj (op V)) :
    dat.inclSection E₂ V (S.toSecond dat.K₁ V ((S.sqZeroProj hi).hom.app (op V) r • k)) =
      dat.twistedSmul E₂ V r (dat.inclSection E₂ V (S.toSecond dat.K₁ V k)) := by
  rw [dat.twistedSmul_eq, dat.twist_inclSection, sub_zero,
    sqZeroProj_smul_pushforward hi dat.K₁ V r k, S.toSecond_smul, dat.inclSection_smul]

/-- The quotient map from the pushout onto `ℱ` is linear for the twisted action. -/
theorem quotSection_smul_sq (hi : IsFirstOrderThickening i) (V : Opens X'.carrier)
    (r : S.sqSections V) (p : (dat.pushoutMod E₂).val.obj (op V)) :
    S.ofSecond dat.F V (dat.quotSection E₂ V (dat.twistedSmul E₂ V r p)) =
      (S.sqZeroProj hi).hom.app (op V) r • S.ofSecond dat.F V (dat.quotSection E₂ V p) := by
  have h1 : dat.quotSection E₂ V (dat.twistedSmul E₂ V r p) =
      S.sqFst r • dat.quotSection E₂ V p := by
    rw [dat.twistedSmul_eq, dat.quotSection_sub, dat.quotSection_twist, dat.quotSection_smul,
      sub_zero]
  exact (congrArg (S.ofSecond dat.F V) h1).trans
    ((S.ofSecond_smul dat.F V (S.sqFst r) (dat.quotSection E₂ V p)).trans
      (sqZeroProj_smul_pushforward hi dat.F V r
        (S.ofSecond dat.F V (dat.quotSection E₂ V p))).symm)

/-- The inclusion of `𝒦₁` into the pushout, as a map of `T`-modules. -/
noncomputable def twistedIncl (hi : IsFirstOrderThickening i) :
    (SheafOfModules.restrictScalars (S.sqZeroProj hi)).obj
        ((modulePushforward i).obj dat.K₁) ⟶ dat.twistedSheaf E₂ :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (structureSheafRing S.space).obj).map (dat.pushoutExt E₂).f.val)
    (fun U r k => dat.inclSection_smul_sq E₂ hi U.unop r k)⟩

/-- The quotient map from the pushout onto `ℱ`, as a map of `T`-modules. -/
noncomputable def twistedQuot (hi : IsFirstOrderThickening i) :
    dat.twistedSheaf E₂ ⟶ (SheafOfModules.restrictScalars (S.sqZeroProj hi)).obj
      ((modulePushforward i).obj dat.F) :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (structureSheafRing S.space).obj).map (dat.pushoutExt E₂).g.val)
    (fun U r p => dat.quotSection_smul_sq E₂ hi U.unop r p)⟩

/-- The two maps of `T`-modules compose to zero. -/
theorem twistedIncl_twistedQuot (hi : IsFirstOrderThickening i) :
    dat.twistedIncl E₂ hi ≫ dat.twistedQuot E₂ hi = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro k
  exact dat.quotSection_inclSection E₂ U.unop (S.toSecond dat.K₁ U.unop k)

/-- The pushout sequence, read as a sequence of `T`-modules, is short exact: short exactness is
a property of the underlying sequence of abelian sheaves, which the twisting does not change. -/
theorem twisted_shortExact (hi : IsFirstOrderThickening i) :
    (ShortComplex.mk (dat.twistedIncl E₂ hi) (dat.twistedQuot E₂ hi)
      (dat.twistedIncl_twistedQuot E₂ hi)).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful (SheafOfModules.toSheaf S.sqZeroRing)
  change ((ShortComplex.mk (dat.pushoutExt E₂).f (dat.pushoutExt E₂).g
    (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero (dat.pushoutExt E₂))).map
      (SheafOfModules.toSheaf (structureSheafRing S.space))).ShortExact
  exact (CategoryTheory.Abelian.YonedaExtension.shortExact (dat.pushoutExt E₂)).map_of_exact
    (SheafOfModules.toSheaf (structureSheafRing S.space))

/-- `descendedActionOfMap` applied to a local section, in the shape in which the local lifting
formula of Tag 08L4 produces it. -/
theorem descendedActionOfMap_app {Y : RingedSpace.{u, u}} (j : X ⟶ Y)
    (N P : SheafOfModules.{u} (structureSheafRing X))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback j))).obj (N)) ⟶ P) (V : Opens Y.carrier)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj ((Stacks.ClosedImmersion.idealSheaf j))).obj (((modulePushforward j).obj N)))).val.obj (op V)) :
    (descendedActionOfMap j N P c).val.app (op V) t =
      ((modulePushforward j).map c).val.app (op V)
        ((extensionTensorComparison j N).val.app (op V) t) := rfl

/-- **Multiplication by a section of `ℐ₂` is the twisting term.** For a section `b` of `ℐ₂` and a
section `m` of `ℐ₁` with the same image in `𝒪_{X'}`, multiplication on the pushout by `ι₂ b` is
the twisting term by `m`. This is what makes the kernel of `q` annihilate the twisted action, and
it is where the commuting square of the two canonical maps is used. -/
theorem inclTwo_smul_eq
    (hE₂ : (firstOrderExtensionAction S.hom dat.F dat.K₂ S.firstOrder E₂).val = dat.c₂)
    (V : Opens X'.carrier) (b : S.ideal.val.obj (op V))
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (hm : idealIncl i V m = S.hSharpApp V (S.inclTwo V b))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    S.inclTwo V b • p = dat.twist E₂ V m p := by
  have hc : (firstOrderExtensionAction S.hom dat.F dat.K₁ S.firstOrder
      (dat.pushoutExt E₂)).val = dat.c₂ ≫ dat.kernelMap :=
    (firstOrderExtensionAction_pushoutExtension S.hom dat.F dat.K₁ dat.K₂ S.firstOrder
      dat.kernelMap E₂).trans (congrArg (fun z => z ≫ dat.kernelMap) hE₂)
  have hact := (firstOrderExtensionAction S.hom dat.F dat.K₁ S.firstOrder
    (dat.pushoutExt E₂)).property V b (dat.quotSection E₂ V p) p rfl
  rw [hc] at hact
  have hact' : dat.inclSection E₂ V
      ((descendedActionOfMap S.hom dat.F dat.K₁ (dat.c₂ ≫ dat.kernelMap)).val.app (op V)
        (toTensorSheafSection S.space (Stacks.ClosedImmersion.idealSheaf S.hom)
          ((modulePushforward S.hom).obj dat.F) (op V)
          (b ⊗ₜ[S.space.presheaf.obj (op V)] dat.quotSection E₂ V p))) =
      S.inclTwo V b • p := hact
  exact ((congrArg (dat.inclSection E₂ V)
    (dat.comm V b m hm (dat.quotSection E₂ V p)).symm).trans hact').symm

/-- **The kernel of `q` annihilates the twisted action.** -/
theorem twistedSmul_eq_zero (hi : IsFirstOrderThickening i)
    (hE₂ : (firstOrderExtensionAction S.hom dat.F dat.K₂ S.firstOrder E₂).val = dat.c₂)
    (V : Opens X'.carrier) (s : S.sqSections V)
    (hs : (S.sqZeroProj hi).hom.app (op V) s = 0)
    (p : (dat.pushoutMod E₂).val.obj (op V)) : dat.twistedSmul E₂ V s p = 0 := by
  obtain ⟨b, hb⟩ := S.exists_ideal_of_sqZeroProj_eq_zero hi V s hs
  have hm : idealIncl i V (S.sqSnd s) = S.hSharpApp V (S.inclTwo V b) := by
    rw [S.idealIncl_sqSnd_of_sqZeroProj_eq_zero hi V s hs, hb]
  rw [dat.twistedSmul_eq, ← hb, dat.inclTwo_smul_eq E₂ hE₂ V b (S.sqSnd s) hm p, sub_self]

/-- **The `𝒪_{X'}`-module structure on the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁`**: the twisted `T`-module
descends along the locally surjective `q : T ⟶ 𝒪_{X'}`, whose kernel annihilates it. This is the
step the source omits. -/
noncomputable def descendedModule (hi : IsFirstOrderThickening i)
    (hE₂ : (firstOrderExtensionAction S.hom dat.F dat.K₂ S.firstOrder E₂).val = dat.c₂) :
    Σ N : SheafOfModules.{u} (structureSheafRing X'),
      (SheafOfModules.restrictScalars (S.sqZeroProj hi)).obj N ≅ dat.twistedSheaf E₂ :=
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X'.carrier)
      (S.sqZeroProj hi).hom := S.sqZeroProj_locallySurjective hi
  Deformation.ToposThickening.descendModule (S.sqZeroProj hi) (dat.twistedSheaf E₂)
    (fun U a ha z => dat.twistedSmul_eq_zero E₂ hi hE₂ U.unop a ha z)

variable (hi : IsFirstOrderThickening i)
  (hE₂ : (firstOrderExtensionAction S.hom dat.F dat.K₂ S.firstOrder E₂).val = dat.c₂)

/-- The middle term of the extension over the first thickening: the pushout with the
`𝒪_{X'}`-module structure descended along `q`. -/
noncomputable def middle : SheafOfModules.{u} (structureSheafRing X') :=
  (dat.descendedModule E₂ hi hE₂).1

/-- Restricting the middle term along `q` gives back the pushout with its twisted action. -/
noncomputable def middleIso :
    (SheafOfModules.restrictScalars (S.sqZeroProj hi)).obj (dat.middle E₂ hi hE₂) ≅
      dat.twistedSheaf E₂ :=
  (dat.descendedModule E₂ hi hE₂).2

/-- The inclusion of `𝒦₁` into the middle term, over the first thickening. -/
noncomputable def extInclOne : (modulePushforward i).obj dat.K₁ ⟶ dat.middle E₂ hi hE₂ :=
  (S.sqZeroRestrictFullyFaithful hi).preimage
    (dat.twistedIncl E₂ hi ≫ (dat.middleIso E₂ hi hE₂).inv)

/-- The quotient map from the middle term onto `ℱ`, over the first thickening. -/
noncomputable def extQuotOne : dat.middle E₂ hi hE₂ ⟶ (modulePushforward i).obj dat.F :=
  (S.sqZeroRestrictFullyFaithful hi).preimage
    ((dat.middleIso E₂ hi hE₂).hom ≫ dat.twistedQuot E₂ hi)

/-- The inclusion of `𝒦₁` is the pushout inclusion, after restricting scalars along `q` and
comparing with the pushout. -/
theorem restrictScalars_extInclOne :
    (SheafOfModules.restrictScalars (S.sqZeroProj hi)).map (dat.extInclOne E₂ hi hE₂) =
      dat.twistedIncl E₂ hi ≫ (dat.middleIso E₂ hi hE₂).inv :=
  (S.sqZeroRestrictFullyFaithful hi).map_preimage _

/-- The quotient map onto `ℱ` is the pushout quotient map, after restricting scalars along `q`
and comparing with the pushout. -/
theorem restrictScalars_extQuotOne :
    (SheafOfModules.restrictScalars (S.sqZeroProj hi)).map (dat.extQuotOne E₂ hi hE₂) =
      (dat.middleIso E₂ hi hE₂).hom ≫ dat.twistedQuot E₂ hi :=
  (S.sqZeroRestrictFullyFaithful hi).map_preimage _

/-- The two maps over the first thickening compose to zero. -/
theorem extInclOne_extQuotOne :
    dat.extInclOne E₂ hi hE₂ ≫ dat.extQuotOne E₂ hi hE₂ = 0 := by
  apply (S.sqZeroRestrictFullyFaithful hi).map_injective
  rw [Functor.map_comp, dat.restrictScalars_extInclOne E₂ hi hE₂,
    dat.restrictScalars_extQuotOne E₂ hi hE₂, Functor.map_zero, Category.assoc,
    Iso.inv_hom_id_assoc, dat.twistedIncl_twistedQuot]

/-- **The sequence `0 → 𝒦₁ → ℱ'₂ ⊔_{𝒦₂} 𝒦₁ → ℱ → 0` is short exact over the first
thickening**: restriction of scalars along the locally surjective `q` is fully faithful, hence
reflects short exactness. -/
theorem extOne_shortExact :
    (ShortComplex.mk (dat.extInclOne E₂ hi hE₂) (dat.extQuotOne E₂ hi hE₂)
      (dat.extInclOne_extQuotOne E₂ hi hE₂)).ShortExact := by
  apply Deformation.ToposThickening.shortExact_of_fullyFaithful_map
    (SheafOfModules.restrictScalars (S.sqZeroProj hi)) (S.sqZeroRestrictFullyFaithful hi)
  have ha := dat.restrictScalars_extInclOne E₂ hi hE₂
  have hb := dat.restrictScalars_extQuotOne E₂ hi hE₂
  let eS : (ShortComplex.mk (dat.extInclOne E₂ hi hE₂) (dat.extQuotOne E₂ hi hE₂)
        (dat.extInclOne_extQuotOne E₂ hi hE₂)).map
        (SheafOfModules.restrictScalars (S.sqZeroProj hi)) ≅
      ShortComplex.mk (dat.twistedIncl E₂ hi) (dat.twistedQuot E₂ hi)
        (dat.twistedIncl_twistedQuot E₂ hi) :=
    ShortComplex.isoMk (Iso.refl _) (dat.middleIso E₂ hi hE₂) (Iso.refl _)
      (by simp only [ShortComplex.map_f, Iso.refl_hom, Category.id_comp, ha,
            Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by simp only [ShortComplex.map_g, Iso.refl_hom, Category.comp_id, hb])
  exact ShortComplex.shortExact_of_iso eS.symm (dat.twisted_shortExact E₂ hi)

/-- **Stacks Project, Tag 08LC.** The extension over the first thickening produced from an
extension over the second: the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁` carries an `𝒪_{X'}`-module structure,
built by descending the action of `T = 𝒪'₂ ⋉ ℐ₁` twisted by `c₁` along the locally surjective
`q : T ⟶ 𝒪_{X'}`, and sits in a short exact sequence `0 → i_* 𝒦₁ → ℱ'₁ → i_* ℱ → 0` of
`𝒪_{X'}`-modules. Its middle term restricted along `q` is identified with the pushout by
`middleIso`, compatibly with the two maps by `restrictScalars_extInclOne` and
`restrictScalars_extQuotOne`. -/
@[stacks 08LC "the canonical map on extensions, by pushout along the map of kernel modules"]
noncomputable def extensionOne :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj dat.F)
      ((modulePushforward i).obj dat.K₁) 0 where
  Z := ComposableArrows.mk₀ (dat.middle E₂ hi hE₂)
  f := dat.extInclOne E₂ hi hE₂
  g := dat.extQuotOne E₂ hi hE₂
  mono_f := (dat.extOne_shortExact E₂ hi hE₂).mono_f
  exact := ComposableArrows.exact₁ _
  exact_g := (dat.extOne_shortExact E₂ hi hE₂).exact.exact_toComposableArrows
  epi_g := (dat.extOne_shortExact E₂ hi hE₂).epi_g

/-- The inclusion of `𝒦₁`, on local sections. -/
theorem extInclOne_app (V : Opens X'.carrier)
    (k : ((modulePushforward i).obj dat.K₁).val.obj (op V)) :
    (dat.extInclOne E₂ hi hE₂).val.app (op V) k =
      (dat.middleIso E₂ hi hE₂).inv.val.app (op V)
        (dat.inclSection E₂ V (S.toSecond dat.K₁ V k)) :=
  sheafOfModules_hom_app_congr (dat.restrictScalars_extInclOne E₂ hi hE₂) (op V) k

/-- The quotient map onto `ℱ`, on local sections. -/
theorem extQuotOne_app (V : Opens X'.carrier) (x : (dat.middle E₂ hi hE₂).val.obj (op V)) :
    (dat.extQuotOne E₂ hi hE₂).val.app (op V) x =
      S.ofSecond dat.F V
        (dat.quotSection E₂ V ((dat.middleIso E₂ hi hE₂).hom.val.app (op V) x)) :=
  sheafOfModules_hom_app_congr (dat.restrictScalars_extQuotOne E₂ hi hE₂) (op V) x

/-- The comparison with the pushout is bijective on local sections. -/
theorem middleIso_inv_hom (V : Opens X'.carrier)
    (x : (dat.middle E₂ hi hE₂).val.obj (op V)) :
    (dat.middleIso E₂ hi hE₂).inv.val.app (op V)
        ((dat.middleIso E₂ hi hE₂).hom.val.app (op V) x) = x :=
  sheafOfModules_hom_app_congr (dat.middleIso E₂ hi hE₂).hom_inv_id (op V) x

/-- Multiplication on the middle term by a section of `ℐ₁` corresponds, under the comparison
with the pushout, to the twisting term. -/
theorem middleIso_hom_idealIncl_smul (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (x : (dat.middle E₂ hi hE₂).val.obj (op V)) :
    (dat.middleIso E₂ hi hE₂).hom.val.app (op V) (idealIncl i V m • x) =
      dat.twist E₂ V m ((dat.middleIso E₂ hi hE₂).hom.val.app (op V) x) := by
  have key : ∀ (r : S.sqSections V)
      (z : ((SheafOfModules.restrictScalars (S.sqZeroProj hi)).obj
        (dat.middle E₂ hi hE₂)).val.obj (op V)),
      (dat.middleIso E₂ hi hE₂).hom.val.app (op V) (r • z) =
        dat.twistedSmul E₂ V r ((dat.middleIso E₂ hi hE₂).hom.val.app (op V) z) :=
    fun r z => map_smul ((dat.middleIso E₂ hi hE₂).hom.val.app (op V)).hom r z
  have hsm : ∀ z : (dat.pushoutMod E₂).val.obj (op V),
      dat.twistedSmul E₂ V (S.sqMk V 0 (-m)) z = dat.twist E₂ V m z := fun z =>
    calc dat.twistedSmul E₂ V (S.sqMk V 0 (-m)) z
        = (0 : S.O.obj (op V)) • z - dat.twist E₂ V (-m) z := rfl
      _ = 0 - dat.twist E₂ V (-m) z :=
          congrArg (fun w => w - dat.twist E₂ V (-m) z) (zero_smul (S.O.obj (op V)) z)
      _ = 0 - -dat.twist E₂ V m z :=
          congrArg (fun w => (0 : (dat.pushoutMod E₂).val.obj (op V)) - w)
            (dat.twist_neg_left E₂ V m z)
      _ = dat.twist E₂ V m z := (zero_sub _).trans (neg_neg _)
  refine Eq.trans ?_ ((key (S.sqMk V 0 (-m)) x).trans (hsm _))
  exact congrArg (fun z : X'.presheaf.obj (op V) =>
    (dat.middleIso E₂ hi hE₂).hom.val.app (op V) (z • x))
    (S.sqZeroProj_mk_zero_neg hi V m).symm

/-- The extension over the first thickening satisfies the local lifting formula of Tag 08L4 for
`c₁`: multiplication by a section of `ℐ₁` on the middle term is the twisting term, which is
exactly `c₁` composed with the inclusion of `𝒦₁`. -/
theorem extensionOne_action_spec (V : Opens X'.carrier)
    (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (x : (dat.extensionOne E₂ hi hE₂).Z.left.val.obj (op V)) :
    (dat.extensionOne E₂ hi hE₂).f.val.app (op V)
        (dat.actOne V m ((dat.extensionOne E₂ hi hE₂).g.val.app (op V) x)) =
      idealIncl i V m • x := by
  have h₁ : (dat.extQuotOne E₂ hi hE₂).val.app (op V) x =
      S.ofSecond dat.F V
        (dat.quotSection E₂ V ((dat.middleIso E₂ hi hE₂).hom.val.app (op V) x)) :=
    dat.extQuotOne_app E₂ hi hE₂ V x
  have h₂ := dat.extInclOne_app E₂ hi hE₂ V (dat.actOne V m
    (S.ofSecond dat.F V
      (dat.quotSection E₂ V ((dat.middleIso E₂ hi hE₂).hom.val.app (op V) x))))
  change (dat.extInclOne E₂ hi hE₂).val.app (op V)
      (dat.actOne V m ((dat.extQuotOne E₂ hi hE₂).val.app (op V) x)) = _
  exact (congrArg (fun y => (dat.extInclOne E₂ hi hE₂).val.app (op V) (dat.actOne V m y))
      h₁).trans
    (h₂.trans ((congrArg (fun z => (dat.middleIso E₂ hi hE₂).inv.val.app (op V) z)
        (dat.middleIso_hom_idealIncl_smul E₂ hi hE₂ V m x).symm).trans
      (dat.middleIso_inv_hom E₂ hi hE₂ V (idealIncl i V m • x))))

/-- **Stacks Project, Tag 08LC.** The canonical map of Tag 08L4 of the extension produced over
the first thickening is the prescribed `c₁`. -/
@[stacks 08LC "the canonical map of the pushed-out extension is c₁"]
theorem extensionOne_action :
    (firstOrderExtensionAction i dat.F dat.K₁ hi (dat.extensionOne E₂ hi hE₂)).val = dat.c₁ := by
  refine (eq_firstOrderExtensionAction_of_comp i dat.F dat.K₁ hi (dat.extensionOne E₂ hi hE₂)
    dat.c₁ ?_).symm
  refine tensorSheaf_hom_ext fun V m x => ?_
  have hinner := (tensorSheafMap_app_toTensorSheafSection X'
    (Stacks.ClosedImmersion.idealSheaf i) (dat.extensionOne E₂ hi hE₂).Z.left
    (Stacks.ClosedImmersion.idealSheaf i) ((modulePushforward i).obj dat.F)
    (𝟙 (Stacks.ClosedImmersion.idealSheaf i)) (dat.extensionOne E₂ hi hE₂).g V m x).trans rfl
  calc ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (Stacks.ClosedImmersion.idealSheaf i)), (dat.extensionOne E₂ hi hE₂).g) : (_, _) ⟶ (_, _))) ≫
          (extensionTensorComparison i dat.F ≫
            (modulePushforward i).map dat.c₁) ≫
          (dat.extensionOne E₂ hi hE₂).f).val.app (op V))
        (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
          (dat.extensionOne E₂ hi hE₂).Z.left (op V)
          (m ⊗ₜ[X'.presheaf.obj (op V)] x))
      = (dat.extensionOne E₂ hi hE₂).f.val.app (op V)
          (dat.actOne V m ((dat.extensionOne E₂ hi hE₂).g.val.app (op V) x)) :=
        congrArg (fun t => (dat.extensionOne E₂ hi hE₂).f.val.app (op V)
          (((modulePushforward i).map dat.c₁).val.app (op V)
            ((extensionTensorComparison i dat.F).val.app (op V) t))) hinner
    _ = idealIncl i V m • x := dat.extensionOne_action_spec E₂ hi hE₂ V m x
    _ = ((idealAction i (dat.extensionOne E₂ hi hE₂).Z.left).val.app (op V))
          (toTensorSheafSection X' (Stacks.ClosedImmersion.idealSheaf i)
            (dat.extensionOne E₂ hi hE₂).Z.left (op V)
            (m ⊗ₜ[X'.presheaf.obj (op V)] x)) :=
        (idealAction_app_tmul i (dat.extensionOne E₂ hi hE₂).Z.left V m x).symm

end PushoutDescentData

end AlgebraicGeometry.RingedSpaceThickening

end
