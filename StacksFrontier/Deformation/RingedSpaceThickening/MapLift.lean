module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.Deformation.RingedSpaceThickening.IdealMultiple
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Topology.Sheaves.RingedSpace.Thickening

/-!
# Lifting a map of modules across a first-order thickening (Stacks 08LH)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed spaces with ideal
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules, and let
`φ : i^* ℱ' ⟶ i^* 𝒢'` be a map of their pullbacks. A *lift* of `φ` is an `𝒪_{X'}`-linear
`φ' : ℱ' ⟶ 𝒢'` with `i^* φ' = φ`. If a lift exists, the lifts form a principal homogeneous
space under `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢')`: the difference of two lifts is killed by the reduction
`𝒢' ⟶ i_* i^* 𝒢'`, hence factors uniquely through `ℐ𝒢' = ker(𝒢' ⟶ i_* i^* 𝒢')`, and
conversely every element of the Hom group translates one lift into another.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.infinitesimalPart`: the ideal multiple `ℐ𝒢'`, read
  as the kernel of the reduction `𝒢' ⟶ i_* i^* 𝒢'`, an `𝒪_{X'}`-module.
* `AlgebraicGeometry.RingedSpaceThickening.infinitesimalPartOnSource`: the same module read on
  `X`, by pullback along `i`.
* `AlgebraicGeometry.RingedSpaceThickening.infinitesimalι`: the inclusion `ℐ𝒢' ⟶ 𝒢'`.
* `AlgebraicGeometry.RingedSpaceThickening.InfinitesimalHom`: the group
  `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢')` acting on lifts.
* `AlgebraicGeometry.RingedSpaceThickening.MapLift`: the lifts of a map between pullbacks.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.idealAction_eq_zero_of_iso`: the ideal acts as zero
  on any module isomorphic to one on which it acts as zero.
* `AlgebraicGeometry.RingedSpaceThickening.idealAction_infinitesimalPart_eq_zero`: across a
  first-order thickening the ideal annihilates `ℐ𝒢'`.
* `AlgebraicGeometry.RingedSpaceThickening.infinitesimalPart_unit_isIso`: consequently `ℐ𝒢'` is
  already a module on the reduced space, the unit of `i^* ⊣ i_*` at it being invertible.
* `AlgebraicGeometry.RingedSpaceThickening.infinitesimalHomEquiv` and
  `AlgebraicGeometry.RingedSpaceThickening.infinitesimalHomEquiv_add`: the resulting additive
  identification `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢') ≃ Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')`.
* `AlgebraicGeometry.RingedSpaceThickening.modulePullback_map_add_comp_infinitesimalι`: a lift
  translated by a map through `ℐ𝒢'` is again a lift, so that group acts on the lifts.
* `AlgebraicGeometry.RingedSpaceThickening.mapLift_isPrincipalHomogeneous`: **Stacks 08LH**, the
  simple transitivity of that group on the lifts, stated as unique existence of the translating
  element.

## Implementation notes

Everything rests on `ℐ(ℐ𝒢') = 0`, which is where the square-zero hypothesis enters: once the
ideal acts as zero on `ℐ𝒢'`, **Stacks 08KS** puts `ℐ𝒢'` in the essential image of `i_*` and the
unit at it is invertible, which is what makes the two Hom groups above agree. That vanishing is
proved not on `ℐ𝒢'` itself but on the tensor product `ℐ ⊗_{𝒪_{X'}} 𝒢'` surjecting onto it,
where the ideal action is computable on local pure tensors: a local section of
`ℐ ⊗_{𝒪_{X'}} 𝒢'` is, on a covering sieve, a sum of pure tensors `a ⊗ b`, the action sends
`a ⊗ b` to `a · b`, and a further section `r` of `ℐ` multiplies that to `(ra) · b = 0`. The
vanishing then descends formally to the image of the action, by cancelling the factorization
`ℐ ⊗_{𝒪_{X'}} 𝒢' ⟶ ℐ𝒢'` through the image on the left and the inclusion of the image on the
right; and it transfers from the image to the kernel of the reduction along the identification
`idealMultipleIso` of **Stacks 08LI**.

Simple transitivity is phrased as `∃!`. The hypothesis that a lift exists is not needed for that
phrasing — with no lifts the statement is vacuous — but it is kept because the source asserts
the principal homogeneous space only when the set of lifts is nonempty.

Three spellings of the sheaf of rings `𝒪_{X'}` meet here, and every declaration below is stated
at the first of them. The adjunction `i^* ⊣ i_*` and the modules are indexed by
`structureSheafRing X'`. The tensor product `ℐ ⊗_{𝒪_{X'}} 𝒢'` is a value of
`Stacks.SheafOfModules.Tensor.sheafTensor`, whose target category is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨X'.presheaf, X'.IsSheaf⟩`; and
`Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi`, which supplies the
epimorphisms cancelled below, is stated at `Stacks.SheafOfModules.Tensor.ringSheaf X'.sheaf`.
All three are equal by `rfl`, but only `structureSheafRing` is `@[instance_reducible]`;
`Tensor.ringSheaf` and `AlgebraicGeometry.SheafedSpace.sheaf` are plain semireducible
definitions, so instance search could not recognise the three categories as one, and the zero
morphism `ℐ ⊗_{𝒪_{X'}} 𝒢' ⟶ 𝒢'`, the action of a section of `𝒪_{X'}` on a section of `𝒢'` and
`Epi` of a map already known to be epimorphic were all unsynthesisable.

The structures themselves are present at every spelling, which is what identifies the fix:
`Abelian`, `Preadditive` and `HasZeroMorphisms` are each found by `inferInstance` at
`Tensor.ringSheaf ⟨X'.presheaf, X'.IsSheaf⟩`, so nothing is missing. Nor does a type ascription
on the object help, since it only forces a defeq check and leaves the `Quiver.Hom` carrier as it
was. What is needed is for the two folded definitions to unfold *during search*, and that is
what the two `attribute [local instance_reducible]` lines below do. They are the per-file opt-in
that the docstring of `structureSheafRing` itself prescribes, they are scoped to this file, and
they change no statement: with them every declaration here is stated at `structureSheafRing X'`
and no bridging definition or second module structure exists.

`tensorSheafMap_epi_of_epi_of_epi` is applied with its two morphism arguments written out. Left
to unification they are recovered only as projections of the pair handed to the uncurried
tensor, so the instance goals come back as `Epi (𝟙 I, f).1`, which instance search cannot
reduce; naming them turns those goals into `Epi (𝟙 I)` and `Epi f`, which the transparency
opt-in discharges.

The square-zero computation itself is not repeated here: `squareZero_kernel_smul_eq_zero` of
`StacksFrontier/Topology/Sheaves/RingedSpace/Thickening.lean` already says that a section of the
kernel ideal annihilates that ideal, and it is reached by `import all` rather than restated. It
appears only inside proofs, so no declaration here needs `@[no_expose]`.

## References

* [Stacks Project, Tag 08LH](https://stacks.math.columbia.edu/tag/08LH)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- The ideal multiple `ℐ𝒢'` of an `𝒪_{X'}`-module along a morphism `i : X ⟶ X'` of ringed
spaces, read as the kernel of the reduction `𝒢' ⟶ i_* i^* 𝒢'`. For a thickening the two
descriptions agree, by `AlgebraicGeometry.RingedSpaceThickening.idealMultipleIso`. -/
noncomputable abbrev infinitesimalPart (G' : SheafOfModules.{u} (structureSheafRing X')) :
    SheafOfModules.{u} (structureSheafRing X') :=
  kernel ((modulePullbackPushforwardAdjunction i).unit.app G')

/-- The ideal multiple `ℐ𝒢'` read as an `𝒪_X`-module, by pullback along `i`. -/
noncomputable abbrev infinitesimalPartOnSource (G' : SheafOfModules.{u} (structureSheafRing X')) :
    SheafOfModules.{u} (structureSheafRing X) :=
  (modulePullback i).obj (infinitesimalPart i G')

/-- The inclusion `ℐ𝒢' ⟶ 𝒢'` of the ideal multiple into the module. -/
noncomputable def infinitesimalι (G' : SheafOfModules.{u} (structureSheafRing X')) :
    infinitesimalPart i G' ⟶ G' :=
  kernel.ι ((modulePullbackPushforwardAdjunction i).unit.app G')

/-- The inclusion of the ideal multiple into the module is a monomorphism, being a kernel
inclusion. -/
instance mono_infinitesimalι (G' : SheafOfModules.{u} (structureSheafRing X')) :
    Mono (infinitesimalι i G') := by
  unfold infinitesimalι
  infer_instance

/-- **A section of the kernel ideal annihilates the image of the ideal action.** For a morphism
of ringed spaces whose kernel ideal `ℐ` has square zero, a section `r` of `ℐ` kills every
section of `𝒢'` in the image of the action `ℐ ⊗_{𝒪_{X'}} 𝒢' ⟶ 𝒢'`.

A local section of `ℐ ⊗_{𝒪_{X'}} 𝒢'` is, on a covering sieve, a finite sum of pure tensors
`a ⊗ b`, on which the action is multiplication by `a`; so `r` multiplies its image by `r a`,
which vanishes because `r` and `a` both lie in `ℐ` and `ℐ ^ 2 = 0`. The conclusion is a
statement about one section of the sheaf `𝒢'`, so it follows from the local one. -/
private theorem smul_idealAction_app_eq_zero
    (hsq : ∀ U : Opens X', (RingHom.ker ((structureSheafHom i).hom.app (op U)).hom) ^ 2 = ⊥)
    (G' : SheafOfModules.{u} (structureSheafRing X')) (V : Opens X')
    (r : (structureSheafRing X').obj.obj (op V))
    (hr : ((structureSheafHom i).hom.app (op V)).hom r = 0)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj
      ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (G'))).val.obj (op V)) :
    r • ((idealAction i G').val.app (op V)).hom t = 0 := by
  obtain ⟨S, hS, hsum⟩ := Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection
    X' (AlgebraicGeometry.SheafOfModules.idealSheaf i) G' V t
  suffices key : ∀ ⦃W : Opens X'⦄ (f : W ⟶ V), S f →
      G'.val.map f.op (r • ((idealAction i G').val.app (op V)).hom t) = 0 by
    exact G'.isSheaf.isSeparated V S hS _ 0
      fun W f hf => (key f hf).trans (map_zero _).symm
  intro W f hf
  obtain ⟨n, a, b, hab⟩ := hsum f hf
  have hres := PresheafOfModules.naturality_apply (idealAction i G').val f.op t
  have hrW : ((structureSheafHom i).hom.app (op W)).hom
      ((structureSheafRing X').obj.map f.op r) = 0 :=
    (NatTrans.naturality_apply (structureSheafHom i).hom f.op r).trans
      (by rw [hr, map_zero])
  have hmul : ∀ j : Fin n,
      (show ((structureSheafRing X').obj.obj (op W) : Type u) from
          (structureSheafRing X').obj.map f.op r) •
        ((idealSheafι i).val.app (op W)).hom (a j) = 0 := fun j =>
    (((idealSheafι i).val.app (op W)).hom.map_smul _ (a j)).symm.trans
      ((congrArg ((idealSheafι i).val.app (op W)).hom
          (squareZero_kernel_smul_eq_zero i hsq W _
            (RingHom.mem_ker.mpr hrW) (a j))).trans (map_zero _))
  refine ((G'.val.restrictₛₗ f.op).map_smulₛₗ r
    (((idealAction i G').val.app (op V)).hom t)).trans ?_
  rw [PresheafOfModules.restrictₛₗ_apply, ← hres, hab, map_sum]
  refine Finset.smul_sum.trans (Finset.sum_eq_zero fun j _ => ?_)
  rw [idealAction_app_tmul i G' W (a j) (b j), smul_smul]
  exact (congrArg (fun z : ((structureSheafRing X').obj.obj (op W) : Type u) => z • b j)
    (hmul j)).trans (zero_smul _ _)

/-- The ideal acts as zero on the target of an epimorphism killing the ideal action. -/
private theorem idealAction_eq_zero_of_epi_of_comp_eq_zero
    {M N : SheafOfModules.{u} (structureSheafRing X')} (f : M ⟶ N) [Epi f]
    (h : idealAction i M ≫ f = 0) : idealAction i N = 0 := by
  let I : SheafOfModules.{u} (structureSheafRing X') :=
    AlgebraicGeometry.SheafOfModules.idealSheaf i
  let g := (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf, X'.IsSheaf⟩)).map
      (((𝟙 I), f) : (_, _) ⟶ (_, _))
  have : Epi g :=
    Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi X' (𝟙 I) f
  refine (cancel_epi g).1 ?_
  rw [comp_zero, ← idealAction_naturality i f, h]

/-- **The ideal acts as zero on the ideal multiple `ℐ𝒢'`**, when its square is zero. `ℐ𝒢'` is
read here as the image of the action `ℐ ⊗_{𝒪_{X'}} 𝒢' ⟶ 𝒢'`.

The action on `ℐ ⊗_{𝒪_{X'}} 𝒢'` followed by the action on `𝒢'` is zero by
`smul_idealAction_app_eq_zero`; the action is natural and `ℐ ⊗_{𝒪_{X'}} 𝒢'` surjects onto the
image, so the vanishing descends by cancelling an epimorphism on the left and the inclusion of
the image on the right. -/
private theorem idealAction_image_eq_zero
    (hsq : ∀ U : Opens X', (RingHom.ker ((structureSheafHom i).hom.app (op U)).hom) ^ 2 = ⊥)
    (G' : SheafOfModules.{u} (structureSheafRing X')) :
    idealAction i (Abelian.image (idealAction i G')) = 0 := by
  let I : SheafOfModules.{u} (structureSheafRing X') :=
    AlgebraicGeometry.SheafOfModules.idealSheaf i
  have hcomp : idealAction i ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
      ((X')).IsSheaf⟩).obj (I)).obj (G'))) ≫ idealAction i G' = 0 := by
    refine tensorSheaf_hom_ext fun V a t => ?_
    have hzero : ((0 : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
        ((X')).IsSheaf⟩).obj (I)).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj (I)).obj (G'))))) ⟶ G').val.app (op V)).hom
        (toTensorSheafSection X' I ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
          ((X')).IsSheaf⟩).obj (I)).obj (G'))) (op V)
          (a ⊗ₜ[X'.presheaf.obj (op V)] t)) = 0 := rfl
    have hsplit : ((idealAction i ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
        ((X')).IsSheaf⟩).obj (I)).obj (G'))) ≫ idealAction i G').val.app (op V)).hom
        (toTensorSheafSection X' I ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
          ((X')).IsSheaf⟩).obj (I)).obj (G'))) (op V)
          (a ⊗ₜ[X'.presheaf.obj (op V)] t)) =
        ((idealAction i G').val.app (op V)).hom
          (((idealAction i ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
            ((X')).IsSheaf⟩).obj (I)).obj (G')))).val.app (op V)).hom
            (toTensorSheafSection X' I ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj (I)).obj (G'))) (op V)
              (a ⊗ₜ[X'.presheaf.obj (op V)] t))) := rfl
    rw [hzero, hsplit, idealAction_app_tmul i ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj (I)).obj (G'))) V a t, _root_.map_smul]
    have hker : ((structureSheafHom i).hom.app (op V)).hom
        (((idealSheafι i).val.app (op V)).hom a) = 0 :=
      congrArg
        (fun k : AlgebraicGeometry.SheafOfModules.idealSheaf i ⟶
            (modulePushforward i).obj (SheafOfModules.unit (structureSheafRing X)) =>
          (k.val.app (op V)).hom a)
        (kernel.condition (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)))
    exact smul_idealAction_app_eq_zero i hsq G' V _ hker t
  have hzero : idealAction i ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf,
      ((X')).IsSheaf⟩).obj (I)).obj (G'))) ≫
      Abelian.factorThruImage (idealAction i G') = 0 :=
    zero_of_comp_mono (Abelian.image.ι (idealAction i G'))
      (by rw [Category.assoc, Abelian.image.fac]; exact hcomp)
  exact idealAction_eq_zero_of_epi_of_comp_eq_zero i (Abelian.factorThruImage (idealAction i G'))
    hzero

/-- **The ideal acts as zero on any module isomorphic to one on which it acts as zero.** The
action is natural, and tensoring an isomorphism with the identity of the ideal is again an
epimorphism, which the naturality square cancels. -/
theorem idealAction_eq_zero_of_iso {M N : SheafOfModules.{u} (structureSheafRing X')}
    (e : M ≅ N) (h : idealAction i M = 0) : idealAction i N = 0 := by
  exact idealAction_eq_zero_of_epi_of_comp_eq_zero i e.hom (by rw [h, zero_comp])

/-- **The ideal acts as zero on the ideal multiple of a module**, across a first-order
thickening. By **Stacks 08LI** the kernel of the reduction `𝒢' ⟶ i_* i^* 𝒢'` is the image of
the ideal action on `𝒢'`, where the square-zero hypothesis makes the action vanish. -/
theorem idealAction_infinitesimalPart_eq_zero (hi : IsFirstOrderThickening i)
    (G' : SheafOfModules.{u} (structureSheafRing X')) :
    idealAction i (kernel ((modulePullbackPushforwardAdjunction i).unit.app G')) = 0 :=
  idealAction_eq_zero_of_iso i (idealMultipleIso i hi.1 G').1
    (idealAction_image_eq_zero i hi.2 G')

/-- **Across a first-order thickening the ideal multiple `ℐ𝒢'` is a module on the reduced
space**: the unit of `i^* ⊣ i_*` at it is an isomorphism. The ideal acts as zero on `ℐ𝒢'`
because its square does, so **Stacks 08KS** places `ℐ𝒢'` in the essential image of `i_*`. -/
theorem infinitesimalPart_unit_isIso (hi : IsFirstOrderThickening i)
    (G' : SheafOfModules.{u} (structureSheafRing X')) :
    IsIso ((modulePullbackPushforwardAdjunction i).unit.app (infinitesimalPart i G')) := by
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  exact ((modulePullbackPushforwardAdjunction i).isIso_unit_app_iff_mem_essImage).2
    (essImage_of_idealAction_eq_zero i hi.1 (infinitesimalPart i G')
      (idealAction_infinitesimalPart_eq_zero i hi G'))

/-- The pushforward of modules along a morphism of ringed spaces is additive. -/
private theorem modulePushforward_additive : (modulePushforward i).Additive :=
  have := modulePushforward_isRightAdjoint i
  Functor.additive_of_preserves_binary_products _

/-- The pullback of modules along a morphism of ringed spaces is additive. -/
private theorem modulePullback_additive : (modulePullback i).Additive :=
  have := modulePushforward_additive i
  (modulePullbackPushforwardAdjunction i).left_adjoint_additive

/-- The additive group `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢')` which acts on the lifts of a map
`i^* ℱ' ⟶ i^* 𝒢'`. -/
noncomputable abbrev InfinitesimalHom (F' G' : SheafOfModules.{u} (structureSheafRing X')) :=
  (modulePullback i).obj F' ⟶ infinitesimalPartOnSource i G'

/-- **The two Hom groups agree**: across a first-order thickening the adjunction `i^* ⊣ i_*`
and the invertibility of its unit at `ℐ𝒢'` identify `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢')` with
`Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')`. -/
noncomputable def infinitesimalHomEquiv (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X')) :
    InfinitesimalHom i F' G' ≃ (F' ⟶ infinitesimalPart i G') := by
  have := infinitesimalPart_unit_isIso i hi G'
  exact ((modulePullbackPushforwardAdjunction i).homEquiv F'
    (infinitesimalPartOnSource i G')).trans
      (asIso ((modulePullbackPushforwardAdjunction i).unit.app
        (infinitesimalPart i G'))).symm.homToEquiv

/-- The identification of the two Hom groups is additive: both halves of it are, the adjunction
because `i^*` and `i_*` are additive functors. -/
theorem infinitesimalHomEquiv_add (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X')) (f g : InfinitesimalHom i F' G') :
    infinitesimalHomEquiv i hi F' G' (f + g) =
      infinitesimalHomEquiv i hi F' G' f + infinitesimalHomEquiv i hi F' G' g := by
  have := infinitesimalPart_unit_isIso i hi G'
  have := modulePushforward_additive i
  have := modulePullback_additive i
  simp only [infinitesimalHomEquiv, Equiv.trans_apply, Adjunction.homAddEquiv_add,
    Iso.homToEquiv_apply, Iso.symm_hom, asIso_inv, Preadditive.add_comp]

/-- **The translating maps vanish on the ideal multiple.** A map `ℱ' ⟶ ℐ𝒢'` produced by
`infinitesimalHomEquiv` factors through the reduction `ℱ' ⟶ i_* i^* ℱ'`, which kills `ℐℱ'`. -/
theorem infinitesimalι_comp_infinitesimalHomEquiv (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X')) (δ : InfinitesimalHom i F' G') :
    infinitesimalι i F' ≫ infinitesimalHomEquiv i hi F' G' δ = 0 := by
  have := infinitesimalPart_unit_isIso i hi G'
  simp [infinitesimalHomEquiv, infinitesimalι, Adjunction.homEquiv_unit]

/-- **A map into the ideal multiple restricts to zero on the reduced space.** Its adjoint
transpose is the map followed by the reduction `𝒢' ⟶ i_* i^* 𝒢'`, which kills `ℐ𝒢'`. -/
theorem modulePullback_map_comp_infinitesimalι
    {F' G' : SheafOfModules.{u} (structureSheafRing X')} (h : F' ⟶ infinitesimalPart i G') :
    (modulePullback i).map (h ≫ infinitesimalι i G') = 0 := by
  have := modulePushforward_additive i
  apply ((modulePullbackPushforwardAdjunction i).homEquiv F' _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality,
    Functor.map_zero, comp_zero, Category.assoc]
  simp [infinitesimalι]

/-- **Translating a map by one through the ideal multiple does not change its restriction.**
The pullback `i^*` is additive, and it kills a map into `ℐ𝒢'` followed by the inclusion
`ℐ𝒢' ⟶ 𝒢'` by `modulePullback_map_comp_infinitesimalι`. Hence the group of maps into `ℐ𝒢'`
acts on the lifts of a fixed map of restrictions. -/
theorem modulePullback_map_add_comp_infinitesimalι
    {F' G' : SheafOfModules.{u} (structureSheafRing X')} (h : F' ⟶ infinitesimalPart i G')
    (φ' : F' ⟶ G') :
    (modulePullback i).map (h ≫ infinitesimalι i G' + φ') = (modulePullback i).map φ' := by
  have := modulePushforward_additive i
  have := modulePullback_additive i
  rw [Functor.map_add, modulePullback_map_comp_infinitesimalι, zero_add]

/-- The lifts across `i` of a map `φ : i^* ℱ' ⟶ i^* 𝒢'` between the pullbacks of two
`𝒪_{X'}`-modules: the `𝒪_{X'}`-linear maps `ℱ' ⟶ 𝒢'` whose pullback is `φ`. -/
noncomputable abbrev MapLift (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G') :=
  {φ' : F' ⟶ G' // (modulePullback i).map φ' = φ}

/-- **Stacks Project, Tag 08LH.** Let `i : X ⟶ X'` be a first-order thickening of ringed spaces
with ideal `ℐ`, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules and let `φ : i^* ℱ' ⟶ i^* 𝒢'`. If `φ`
lifts to `X'`, its lifts form a principal homogeneous space under `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢')`:
any two lifts differ by exactly one element of that group.

The difference of two lifts is killed by `𝒢' ⟶ i_* i^* 𝒢'`, so it factors uniquely through
`ℐ𝒢'`, and `infinitesimalHomEquiv` turns that factorization into the translating element. -/
@[stacks 08LH]
theorem mapLift_isPrincipalHomogeneous (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G')
    (_hne : Nonempty (MapLift i F' G' φ)) :
    ∀ φ₁ φ₂ : MapLift i F' G' φ,
      ∃! δ : InfinitesimalHom i F' G',
        infinitesimalHomEquiv i hi F' G' δ ≫ infinitesimalι i G' + φ₁.1 = φ₂.1 := by
  intro φ₁ φ₂
  have := modulePushforward_additive i
  have := modulePullback_additive i
  have hmap : (modulePullback i).map (φ₂.1 - φ₁.1) = 0 := by
    rw [Functor.map_sub, φ₁.2, φ₂.2, sub_self]
  have hd : (φ₂.1 - φ₁.1) ≫ (modulePullbackPushforwardAdjunction i).unit.app G' = 0 := by
    have hnat : (φ₂.1 - φ₁.1) ≫ (modulePullbackPushforwardAdjunction i).unit.app G' =
        (modulePullbackPushforwardAdjunction i).unit.app F' ≫
          (modulePushforward i).map ((modulePullback i).map (φ₂.1 - φ₁.1)) :=
      (modulePullbackPushforwardAdjunction i).unit.naturality _
    rw [hnat, hmap, Functor.map_zero, comp_zero]
  have he : kernel.lift ((modulePullbackPushforwardAdjunction i).unit.app G')
      (φ₂.1 - φ₁.1) hd ≫ infinitesimalι i G' = φ₂.1 - φ₁.1 := kernel.lift_ι _ _ hd
  have key : ∀ δ : InfinitesimalHom i F' G',
      infinitesimalHomEquiv i hi F' G' δ ≫ infinitesimalι i G' + φ₁.1 = φ₂.1 ↔
        infinitesimalHomEquiv i hi F' G' δ =
          kernel.lift ((modulePullbackPushforwardAdjunction i).unit.app G')
            (φ₂.1 - φ₁.1) hd := by
    intro δ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine (cancel_mono (infinitesimalι i G')).1 ?_
      rw [he]
      exact add_right_cancel (h.trans (sub_add_cancel φ₂.1 φ₁.1).symm)
    · rw [h, he, sub_add_cancel]
  refine ⟨(infinitesimalHomEquiv i hi F' G').symm _, (key _).2
    ((infinitesimalHomEquiv i hi F' G').apply_symm_apply _), fun δ' hδ' => ?_⟩
  exact (infinitesimalHomEquiv i hi F' G').injective
    (((key δ').1 hδ').trans ((infinitesimalHomEquiv i hi F' G').apply_symm_apply _).symm)

end AlgebraicGeometry.RingedSpaceThickening

end
