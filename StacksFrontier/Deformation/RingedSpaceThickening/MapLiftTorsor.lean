module

public import StacksFrontier.Deformation.RingedSpaceThickening.MapLift
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.ModuleMapLifts

/-!
# The lifts of a map of modules form a torsor (Stacks 08LH)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed spaces with ideal
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules, set `ℱ = i^* ℱ'` and
`𝒢 = i^* 𝒢'`, and let `φ : ℱ ⟶ 𝒢` be `𝒪_X`-linear. Stacks 08LH asserts that the set of lifts
of `φ` to an `𝒪_{X'}`-linear `φ' : ℱ' ⟶ 𝒢'` is, if nonempty, a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℐ𝒢')`.

Here `ℐ𝒢'` is the ideal multiple, the image of the action `ℐ ⊗_{𝒪_{X'}} 𝒢' ⟶ 𝒢'`, and it is
read as an `𝒪_X`-module by pullback along `i`; across a first-order thickening this is the
unique `𝒪_X`-module structure the source refers to, since the unit `ℐ𝒢' ⟶ i_* i^* (ℐ𝒢')` is
invertible. The lifts are `AlgebraicGeometry.RingedSpaceThickening.MapLift`, the
`𝒪_{X'}`-linear maps `φ' : ℱ' ⟶ 𝒢'` with `i^* φ' = φ`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.idealMultipleHomEquiv`: the additive identification
  `Hom_{𝒪_X}(i^* ℱ', i^*(ℐ𝒢')) ≃+ Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')` given by the adjunction
  `i^* ⊣ i_*` and the inverse of its unit at `ℐ𝒢'`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isIso_unit_app_idealMultiple`: across a first-order
  thickening the unit of `i^* ⊣ i_*` at `ℐ𝒢'` is invertible, so `ℐ𝒢'` is an `𝒪_X`-module.
* `AlgebraicGeometry.RingedSpaceThickening.exists_addTorsor_mapLift`: **Stacks 08LH**, a
  nonempty set of lifts carries a structure of torsor under `Hom_{𝒪_X}(i^* ℱ', i^*(ℐ𝒢'))`,
  an element `δ` acting by adding the corresponding map `ℱ' ⟶ ℐ𝒢' ⟶ 𝒢'`.

## Implementation notes

The proof is the exact sequence
`0 ⟶ Hom(ℱ', ℐ𝒢') ⟶ Hom(ℱ', 𝒢') ⟶ Hom(ℱ, 𝒢)` of the source: the second map is `i^*`,
whose kernel consists of the maps killed by the reduction `𝒢' ⟶ i_* i^* 𝒢'`, that is of the
maps factoring through `ker(𝒢' ⟶ i_* i^* 𝒢') = ℐ𝒢'` (**Stacks 08LI**,
`idealMultipleIso`). The torsor is then produced by the general fibre-of-an-exact-sequence
construction `Deformation.ToposThickening.addTorsor_fiber_of_exact`. The core of the proof is
stated for an arbitrary additive bijection onto `Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')`, so that the unfolding
of the canonical one, `idealMultipleHomEquiv`, never enters the defeq checks of the proof; the
registered statement then specialises it to that canonical bijection.

The ideal multiple is the image of `idealAction`, whose category of modules is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`, while the adjunction is indexed by
`structureSheafRing`; the two `attribute [local instance_reducible]` lines are the same per-file
opt-in as in `MapLift.lean`, letting instance search identify the two spellings.

## References

* [Stacks Project, Tag 08LH](https://stacks.math.columbia.edu/tag/08LH)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- **Across a first-order thickening the ideal multiple `ℐ𝒢'` is a module on the reduced
space**: the unit of `i^* ⊣ i_*` at the image of the ideal action is invertible. The ideal acts
as zero on `ℐ𝒢'`, which is isomorphic to `ker(𝒢' ⟶ i_* i^* 𝒢')` by **Stacks 08LI**, so
**Stacks 08KS** places it in the essential image of `i_*`. -/
theorem isIso_unit_app_idealMultiple (hi : IsFirstOrderThickening i)
    (G' : SheafOfModules.{u} (structureSheafRing X')) :
    IsIso ((modulePullbackPushforwardAdjunction i).unit.app
      (Abelian.image (idealAction i G'))) := by
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  exact ((modulePullbackPushforwardAdjunction i).isIso_unit_app_iff_mem_essImage).2
    (essImage_of_idealAction_eq_zero i hi.1 _
      (idealAction_eq_zero_of_iso i (idealMultipleIso i hi.1 G').1.symm
        (idealAction_infinitesimalPart_eq_zero i hi G')))

/-- **`Hom_{𝒪_X}(ℱ, ℐ𝒢') = Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')`.** Across a first-order thickening, the
adjunction `i^* ⊣ i_*` followed by the inverse of its unit at the ideal multiple `ℐ𝒢'` (the
image of the ideal action on `𝒢'`) is an additive bijection. -/
noncomputable def idealMultipleHomEquiv (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X')) :
    ((modulePullback i).obj F' ⟶ (modulePullback i).obj (Abelian.image (idealAction i G'))) ≃+
      (F' ⟶ Abelian.image (idealAction i G')) :=
  haveI := isIso_unit_app_idealMultiple i hi G'
  haveI := modulePushforward_isRightAdjoint i
  haveI : (modulePushforward i).Additive := Functor.additive_of_preserves_binary_products _
  haveI : (modulePullback i).Additive :=
    (modulePullbackPushforwardAdjunction i).left_adjoint_additive
  AddEquiv.mk' (((modulePullbackPushforwardAdjunction i).homEquiv F' _).trans
      (asIso ((modulePullbackPushforwardAdjunction i).unit.app
        (Abelian.image (idealAction i G')))).symm.homToEquiv) fun f g => by
    simp only [Equiv.trans_apply, Adjunction.homAddEquiv_add, Iso.homToEquiv_apply,
      Iso.symm_hom, asIso_inv, Preadditive.add_comp]

/-- **The reduction kills the ideal multiple.** For a thickening, the inclusion of the image of
the ideal action into `𝒢'` followed by the reduction `𝒢' ⟶ i_* i^* 𝒢'` is zero, because the
action followed by the reduction is, and the action surjects onto its image. -/
theorem image_ι_comp_moduleReductionMap (hi : IsThickening i)
    (G' : SheafOfModules.{u} (structureSheafRing X')) :
    Abelian.image.ι (idealAction i G') ≫ moduleReductionMap i G' = 0 := by
  have h := idealAction_comp_moduleReductionMap_eq_zero i hi G'
  rw [← Abelian.image.fac (idealAction i G'), Category.assoc] at h
  exact (cancel_epi (Abelian.factorThruImage (idealAction i G'))).1 (h.trans comp_zero.symm)

/-- **The lifts are a torsor under any group identified with `Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')`.** For an
additive bijection `e` from an additive group onto the maps `ℱ' ⟶ ℐ𝒢'`, a nonempty set of lifts
of `φ` carries a torsor structure in which `δ` acts by adding `e δ` followed by the inclusion
`ℐ𝒢' ⟶ 𝒢'`. The maps `ℱ' ⟶ 𝒢'` killed by `i^*` are those killed by the reduction
`𝒢' ⟶ i_* i^* 𝒢'`, that is those factoring through `ℐ𝒢'` by **Stacks 08LI**; this is the
exact sequence `0 ⟶ Hom(ℱ', ℐ𝒢') ⟶ Hom(ℱ', 𝒢') ⟶ Hom(ℱ, 𝒢)` of the source. -/
private theorem exists_addTorsor_mapLift_of_addEquiv (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G')
    (hne : Nonempty (MapLift i F' G' φ)) {A : Type*} [AddCommGroup A]
    (e : A ≃+ (F' ⟶ Abelian.image (idealAction i G'))) :
    ∃ t : AddTorsor A (MapLift i F' G' φ),
      ∀ (δ : A) (φ' : MapLift i F' G' φ),
        (t.vadd δ φ').1 = φ'.1 + e δ ≫ Abelian.image.ι (idealAction i G') := by
  have := modulePushforward_isRightAdjoint i
  have : (modulePushforward i).Additive := Functor.additive_of_preserves_binary_products _
  have : (modulePullback i).Additive :=
    (modulePullbackPushforwardAdjunction i).left_adjoint_additive
  let adj := modulePullbackPushforwardAdjunction i
  let E := (idealMultipleIso i hi.1 G').1
  let k : A →+ (F' ⟶ G') := (Preadditive.compHom.flip (Abelian.image.ι (idealAction i G'))).comp
    e.toAddMonoidHom
  have hk : Function.Injective k := fun a b hab =>
    e.injective ((cancel_mono (Abelian.image.ι (idealAction i G'))).mp hab)
  have hEinv : E.inv ≫ Abelian.image.ι (idealAction i G') = kernel.ι (adj.unit.app G') :=
    E.inv_comp_eq.2 (idealMultipleIso i hi.1 G').2.symm
  have hker (g : F' ⟶ G') : (modulePullback i).map g = 0 ↔ g ≫ adj.unit.app G' = 0 := by
    rw [← (adj.homEquiv_unit _ _ _).trans (adj.unit_naturality g)]
    exact (adj.homAddEquiv F' ((modulePullback i).obj G')).map_eq_zero_iff.symm
  have hex (g : F' ⟶ G') : (modulePullback i).mapAddHom g = 0 ↔ ∃ a, k a = g := by
    change (modulePullback i).map g = 0 ↔ _
    rw [hker]
    constructor
    · intro hd
      refine ⟨e.symm (kernel.lift _ g hd ≫ E.inv), ?_⟩
      change e (e.symm _) ≫ Abelian.image.ι (idealAction i G') = g
      rw [e.apply_symm_apply, Category.assoc, hEinv, kernel.lift_ι]
    · rintro ⟨a, rfl⟩
      exact (Category.assoc _ _ _).trans
        ((e a ≫= image_ι_comp_moduleReductionMap i hi.1 G').trans comp_zero)
  exact (Deformation.ToposThickening.addTorsor_fiber_of_exact k (modulePullback i).mapAddHom
    hk hex φ (hne.elim fun p => ⟨⟨p.1, p.2⟩⟩)).elim fun t ht => ⟨t, ht⟩

/-- **Stacks Project, Tag 08LH.** Let `i : X ⟶ X'` be a first-order thickening of ringed spaces
with ideal `ℐ`, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules, `ℱ = i^* ℱ'`, `𝒢 = i^* 𝒢'`, and let
`φ : ℱ ⟶ 𝒢` be `𝒪_X`-linear. If the set of lifts of `φ` to an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'` (those with `i^* φ' = φ`) is nonempty, it is a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℐ𝒢')`, where `ℐ𝒢'` is the image of the ideal action `ℐ ⊗ 𝒢' ⟶ 𝒢'` read as an
`𝒪_X`-module: there is a torsor structure in which `δ` acts on a lift `φ'` by adding the
`𝒪_{X'}`-linear map `ℱ' ⟶ ℐ𝒢' ⟶ 𝒢'` corresponding to `δ`. -/
@[stacks 08LH]
theorem exists_addTorsor_mapLift (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G')
    (hne : Nonempty (MapLift i F' G' φ)) :
    ∃ t : AddTorsor
        ((modulePullback i).obj F' ⟶ (modulePullback i).obj (Abelian.image (idealAction i G')))
        (MapLift i F' G' φ),
      ∀ (δ : (modulePullback i).obj F' ⟶
          (modulePullback i).obj (Abelian.image (idealAction i G')))
        (φ' : MapLift i F' G' φ),
        (t.vadd δ φ').1 =
          φ'.1 + idealMultipleHomEquiv i hi F' G' δ ≫ Abelian.image.ι (idealAction i G') :=
  exists_addTorsor_mapLift_of_addEquiv i hi F' G' φ hne (idealMultipleHomEquiv i hi F' G')

end AlgebraicGeometry.RingedSpaceThickening

end
