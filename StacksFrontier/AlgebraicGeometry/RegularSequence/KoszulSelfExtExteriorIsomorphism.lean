module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDegreeZeroIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtDegreeOneGenerated
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtExteriorCriterion
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtStalkPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafUnitEvaluation

/-!
# The comparison of Stacks 0BQY outside the positive degrees

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals, write `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The comparison
map of Stacks 0BQY,

`⋀ⁱ_{O_X}(Ext¹_{O♯}(O_X, O_X)) ⟶ Extⁱ_{O♯}(O_X, O_X)`,

is asserted to be an isomorphism for **every** integer `i`, and
`Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra_iff` quantifies over
`i : ℤ` accordingly. The degrees split into three kinds, and only the positive ones carry the
local computation. This file disposes of the negative ones and collects the degree-zero material.

In a negative degree both sides vanish: the exterior algebra of a sheaf of modules has no
nonzero piece in negative degree, and the self-Ext sheaf is the internal Hom sheaf out of a term
of the Koszul complex which is itself zero there. A morphism between two zero objects is an
isomorphism, with no reference to the comparison map's construction.

In degree zero the Koszul complex is the structure sheaf, so the self-Ext sheaf is the quotient
and the unit of the self-Ext algebra is the augmentation. Degree zero therefore carries no
information about the comparison map either, by
`SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero`; what is still missing to apply that is
the descended form of the degree-zero identification, over the quotient ring sheaf rather than
over `O♯`.

## Main results

* `Stacks.RegularSequence.KoszulChainData.isZero_extSelfAlgebra_piece_of_neg`: the self-Ext
  sheaf vanishes in negative degree.
* `Stacks.RegularSequence.KoszulChainData.isIso_extComparison_of_neg`: **the comparison map is an
  isomorphism in every negative degree.**
* `Stacks.RegularSequence.KoszulChainData.homologyPieceZeroIsoQuotient`: in degree zero, before
  descent, the self-Ext sheaf is the quotient itself.
* `Stacks.RegularSequence.KoszulChainData.homIso_app_apply_homologyOne`: **the unit of the
  self-Ext algebra corresponds to the augmentation**, which is the degree-zero content needed to
  see the zeroth piece as free of rank one on the identity class.
* `Stacks.RegularSequence.KoszulChainData.homologyPieceZeroIsoQuotient_hom_val_app_homologyOne`:
  **the zeroth identification carries the algebra unit to the image of `1` under the quotient
  map** — the undescended half of "`Ext⁰` is free of rank one on the identity class".

## Implementation notes

**The vanishing of the descended piece is read off from the undescended one on sections.** Descent
along the quotient of the ring sheaf leaves the underlying presheaf of abelian groups untouched,
so the two pieces have literally the same sections; `isZero_of_forall_section_eq_zero` and its
converse `section_eq_zero_of_isZero` cross between the two statements, with
`Stacks.RegularSequence.KoszulChainData.descendPieceAddEquiv` transporting a section from one
spelling to the other. Nothing is said about the module structures, which is as well, since they
are over different rings.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-- **The self-Ext sheaf vanishes in negative degree.** Its undescended form is the internal Hom
sheaf out of the degree-`i` term of the Koszul complex, which is zero for `i < 0`; descent leaves
the sections untouched, so the descended piece has only the zero section as well. -/
theorem isZero_extSelfAlgebra_piece_of_neg {i : ℤ} (hi : i < 0) :
    IsZero ((extSelfAlgebra Rc K).piece i) := by
  have hhom : IsZero (RingedSite.internalHomSheaf (ringedSite Rc) (K.chain.X i)
      (quotient Rc (φ := φ))) :=
    RingedSite.internalHomSheaf_isZero_of_isZero (ringedSite Rc) (K.isZero_chain_X_of_neg hi)
  have horig : IsZero ((homologyGradedAlgebra Rc (cochain Rc K)).piece i) :=
    IsZero.of_iso hhom (homIso Rc K i)
  rw [IsZero.iff_id_eq_zero]
  ext U y
  obtain ⟨z, rfl⟩ := (descendPieceAddEquiv Rc K i U).surjective y
  rw [section_eq_zero_of_isZero horig U z, map_zero, map_zero, map_zero]

/-- **The comparison map of Stacks 0BQY is an isomorphism in every negative degree.** Both sides
are zero objects there — the exterior algebra has no nonzero negative piece, and the self-Ext sheaf
vanishes by `isZero_extSelfAlgebra_piece_of_neg` — and a morphism between zero objects is an
isomorphism, the zero morphism being its inverse. -/
theorem isIso_extComparison_of_neg {i : ℤ} (hi : i < 0) : IsIso (extComparison Rc K i) := by
  have hsrc : IsZero ((extSelfExteriorAlgebra Rc K).exterior.piece i) :=
    isZero_exteriorPiece_of_neg (extSelfExteriorAlgebra Rc K) hi
  have htgt : IsZero ((extSelfAlgebra Rc K).piece i) :=
    isZero_extSelfAlgebra_piece_of_neg Rc K hi
  exact ⟨0, hsrc.eq_of_src _ _, htgt.eq_of_tgt _ _⟩

/-- **The zeroth self-Ext sheaf, before descent, is the quotient itself.** In degree zero the
Koszul complex is the structure sheaf, so the internal Hom sheaf out of it is its target:

`Ext⁰_{O♯}(O_X, O_X) ≅ SheafHom_{O♯}(K_0, O_X) ≅ SheafHom_{O♯}(O♯, O_X) ≅ O_X`.

The first identification is `Stacks.RegularSequence.KoszulChainData.homIso`, the second the
trivialisation `Stacks.RegularSequence.KoszulChainData.chainXZeroIsoUnit` of the degree-zero term,
and the third `Stacks.SheafOfModules.internalHomSheafIsoOfIsoUnit`, which evaluates a homomorphism
out of a trivialised sheaf at the unit section.

This is the degree-zero description that both remaining degree-zero facts of Stacks 0BQY rest on:
that `Ext⁰` is free of rank one on the identity class, which is the hypothesis
`SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` consumes for the target, and that the
augmentation reads off a scalar at a stalk. -/
def homologyPieceZeroIsoQuotient :
    (homologyGradedAlgebra Rc (cochain Rc K)).piece 0 ≅ quotient Rc (φ := φ) :=
  homIso Rc K 0 ≪≫
    Stacks.SheafOfModules.internalHomSheafIsoOfIsoUnit Rc (quotient Rc (φ := φ))
      K.chainXZeroIsoUnit

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **The identification of the zeroth piece carries the algebra unit to the augmentation.** The
unit of the self-Ext algebra is the class of the identity cocycle
(`Stacks.SheafOfModules.homologyOne_eval`, whose cycle is
`Stacks.SheafOfModules.iCycles_oneCycle` the identity cochain), and evaluating a cochain whose
every component is the identity returns its argument
(`AlgebraicGeometry.RingedSite.applyHomSectionOver_idSection`). So
`Stacks.RegularSequence.KoszulChainData.homIso` carries the unit to the homomorphism
`K_0 ⟶ O_X` which is the augmentation itself.

This is the degree-zero content needed to see `Ext⁰` as free of rank one on the identity class:
the unit corresponds, under the trivialisation of `K_0`, to the image of `1` under the quotient
map. The degree transports here are between *closed* integer terms — `-0` and `0 - 0` against
`0` — so unlike the general degree they reduce, and the statement needs no normalisation. -/
theorem homIso_app_apply_homologyOne (U V : Opens ↥X) (i : V ⟶ U)
    (y : ((K.chain.X 0).over U).val.obj (op (Over.mk i))) :
    ((homIso Rc K 0).hom.val.app (op U)
          ((Stacks.SheafOfModules.homologyOne Rc (cochain Rc K)).val (op U))).app
        (op (Over.mk i)) y =
      eqToHom (congrArg
          (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk i)))
          (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))).X ((0 : ℤ) - 0) = quotient Rc (φ := φ) from
            by rw [sub_self]; rfl))
        (((augSingle Rc K).f ((0 : ℤ) - 0)).val.app (op V)
          (eqToHom (congrArg
            (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk i)))
            (congrArg K.chain.X (neg_neg (0 : ℤ))).symm) y)) := by
  refine Eq.trans (homIso_app_apply Rc K 0 U V i
    ((Stacks.SheafOfModules.oneCycle Rc (cochain Rc K)).val.app (op U)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Rc).obj.obj (op U))) y) ?_
  refine congrArg _ (congrArg _ ?_)
  refine Eq.trans (congrArg
    (fun w => RingedSite.applyHomSectionOver (ringedSite Rc)
      (RingedSite.sheafHomComplex (ringedSite Rc) (cochain Rc K) (cochain Rc K))
      U V i 0 (-(0 : ℤ)) ((0 : ℤ) - 0) (by ring) w
      (eqToHom (congrArg
        (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk i)))
        (congrArg K.chain.X (neg_neg (0 : ℤ))).symm) y))
    (Stacks.SheafOfModules.iCycles_oneCycle Rc (cochain Rc K) (op U))) ?_
  exact RingedSite.applyHomSectionOver_idSection (ringedSite Rc) (cochain Rc K) U V i
    (-(0 : ℤ)) _

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **The zeroth identification carries the algebra unit to the image of `1` under the quotient
map.** Composing `internalHomSheafIsoOfIsoUnit`, which evaluates a homomorphism at the image of
the unit section, with `homIso_app_apply_homologyOne`, which says the unit corresponds to the
augmentation: the augmentation precomposed with the trivialisation of the degree-zero term is the
quotient map, which is
`Stacks.RegularSequence.KoszulChainData.quotientPi` by its own definition.

This is the undescended half of "`Ext⁰` is free of rank one on the identity class". The transport
is the one `homIso` carries in degree zero, between the degree `0 - 0` term of the complex
concentrated in degree zero and the quotient. -/
theorem homologyPieceZeroIsoQuotient_hom_val_app_homologyOne (U : Opens ↥X) :
    (homologyPieceZeroIsoQuotient Rc K).hom.val.app (op U)
        ((Stacks.SheafOfModules.homologyOne Rc (cochain Rc K)).val (op U)) =
      eqToHom (congrArg
          (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk (𝟙 U))))
          (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))).X ((0 : ℤ) - 0) = quotient Rc (φ := φ) from
            by rw [sub_self]; rfl))
        ((quotientPi Rc K).val.app (op U)
          (1 : (structureSheaf Rc).obj.obj (op U))) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op U) _) ?_
  refine Eq.trans (Stacks.SheafOfModules.internalHomSheafIsoOfIsoUnit_hom_val_app Rc
    (quotient Rc (φ := φ)) K.chainXZeroIsoUnit U _) ?_
  refine Eq.trans (homIso_app_apply_homologyOne Rc K U U (𝟙 U) _) ?_
  refine congrArg _ ?_
  exact (SheafOfModules.comp_val_app_apply K.chainXZeroIsoUnit.inv ((augSingle Rc K).f 0) (op U)
    (1 : (structureSheaf Rc).obj.obj (op U))).symm

/-- **The degree-zero identification, after restricting scalars.** The composite of three
identifications already available: the descended piece restricts to the piece before descent
(`SheafOfModules.GradedAlgebra.restrictScalars_descend_piece_iso`), that piece is the quotient in
degree zero (`homologyPieceZeroIsoQuotient`), and the quotient — the cokernel of `φ` — is the
restriction of scalars of the unit of the quotient sheaf of rings
(`Stacks.Sites.cokernelIsoQuotientRingOfHom`).

Named separately from `extSelfAlgebraPieceZeroIsoUnit`, of which it is the image under restriction
of scalars, so that the value of that isomorphism on a section can be computed: restriction of
scalars is the identity on sections, so the two agree there. -/
def extSelfAlgebraPieceZeroIsoUnitRestricted :
    (SheafOfModules.restrictScalars (quotientRingHom (quotientIdeal Rc φ))).obj
        ((extSelfAlgebra Rc K).piece 0) ≅
      (SheafOfModules.restrictScalars (quotientRingHom (quotientIdeal Rc φ))).obj
        (SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X)
          (quotientStructureSheaf Rc φ))) :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  (SheafOfModules.GradedAlgebra.restrictScalars_descend_piece_iso
      (quotientRingHom (quotientIdeal Rc φ)) (homologyGradedAlgebra Rc (cochain Rc K))
      (smul_homologyPiece_eq_zero Rc K) 0 :
    (SheafOfModules.restrictScalars (quotientRingHom (quotientIdeal Rc φ))).obj
        ((extSelfAlgebra Rc K).piece 0) ≅
      (homologyGradedAlgebra Rc (cochain Rc K)).piece 0) ≪≫
    homologyPieceZeroIsoQuotient Rc K ≪≫ Stacks.Sites.cokernelIsoQuotientRingOfHom φ

/-- **The zeroth piece of the self-Ext algebra is the unit of the quotient sheaf of rings.**
Restriction of scalars along the quotient map is fully faithful, so the isomorphism of
`extSelfAlgebraPieceZeroIsoUnitRestricted` descends.

This is the hypothesis that `SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` consumes for
the target; `Stacks.SheafOfModules.exteriorPieceZeroIsoUnit` supplies it for the source. -/
def extSelfAlgebraPieceZeroIsoUnit :
    (extSelfAlgebra Rc K).piece 0 ≅
      SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X)
        (quotientStructureSheaf Rc φ)) :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (quotientRingHom (quotientIdeal Rc φ))).preimageIso
    (extSelfAlgebraPieceZeroIsoUnitRestricted Rc K)

/-- Equal morphisms of sheaves of modules agree on every local section. -/
private theorem val_app_apply_congr {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R}
    {f g : M ⟶ N} (h : f = g) (V : Cᵒᵖ) (y : M.val.obj V) :
    f.val.app V y = g.val.app V y := by
  rw [h]

/-- **The descended identification agrees with the restricted one on sections.** Restriction of
scalars leaves the underlying presheaf of abelian groups untouched, so it is the identity on
sections; and the descended isomorphism is by construction the one whose image under restriction
of scalars is the restricted one, which is
`CategoryTheory.Functor.FullyFaithful.map_preimage`. -/
theorem extSelfAlgebraPieceZeroIsoUnit_hom_val_app (U : (Opens ↥X)ᵒᵖ)
    (x : ((extSelfAlgebra Rc K).piece 0).val.obj U) :
    (extSelfAlgebraPieceZeroIsoUnit Rc K).hom.val.app U x =
      (extSelfAlgebraPieceZeroIsoUnitRestricted Rc K).hom.val.app U x := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  exact val_app_apply_congr
    ((Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (quotientRingHom (quotientIdeal Rc φ))).map_preimage
      (extSelfAlgebraPieceZeroIsoUnitRestricted Rc K).hom) U x

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  [QuasiIso K.augmentation] in
/-- **The three degree-zero transports compose to the identity.** The identification of the
degree-zero term of a chain complex concentrated in degree zero, the comparison of the two readings
of such a complex, and the transport that `homIso` carries in degree zero, all sit between objects
that are the quotient, and their composite is the identity.

**Proved by reducing to sections.** Categorically this is not a reflexivity: each factor is
definitionally the identity by proof irrelevance, but `𝟙 ≫ 𝟙 ≫ 𝟙 = 𝟙` is `Category.id_comp`
rather than a definitional equality. On sections, however, composition *is* function composition
and each factor is a transport of definitionally equal types, hence the identity function — so
after `hom_ext` the goal closes by `rfl`. Neither `simp` nor `rw` nor `calc` reaches it: `simp` and
`rw` are blocked by the two spellings of the sheaf of rings, and `calc` by `Trans` synthesis. -/
theorem singleObjXSelf_inv_comp_quotientSingleIso_comp_eqToHom :
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0
          (koszulQuotient.{u, u, u} φ)).inv ≫
        ((quotientSingleIso Rc (φ := φ)).hom).f 0 ≫
        eqToHom (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ))).X ((0 : ℤ) - 0) = quotient Rc (φ := φ) from
          by rw [sub_self]; rfl) =
      𝟙 (quotient Rc (φ := φ)) := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.hom_ext ?_
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  [QuasiIso K.augmentation] in
/-- **The quotient map read into the degree-zero term of the single complex, transported back, is
the quotient map.** The two transports that `quotientPi` carries cancel against the one `homIso`
carries, by `singleObjXSelf_inv_comp_quotientSingleIso_comp_eqToHom`, and the trivialisation of the
degree-zero Koszul term cancels against its inverse.

Also proved on sections, where the cancellation of the trivialisation is
`Stacks.SheafOfModules.iso_inv_hom_app_apply`. -/
theorem quotientPi_comp_eqToHom :
    quotientPi Rc K ≫
        eqToHom (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ))).X ((0 : ℤ) - 0) = quotient Rc (φ := φ) from
          by rw [sub_self]; rfl) =
      koszulQuotientπ.{u, u, u} φ := by
  have hT : ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
      (quotient Rc (φ := φ))).X ((0 : ℤ) - 0) = quotient Rc (φ := φ) := by
    rw [sub_self]; rfl
  have h0 : (augSingle Rc K).f 0 = K.chainXZeroIsoUnit.hom ≫ koszulQuotientπ.{u, u, u} φ ≫
      ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0
          (koszulQuotient.{u, u, u} φ)).inv ≫ ((quotientSingleIso Rc (φ := φ)).hom).f 0) := by
    rw [show (augSingle Rc K).f 0 = K.augmentation.f 0 ≫
        ((quotientSingleIso Rc (φ := φ)).hom).f 0 from rfl, K.augmentation_f_zero,
      show K.augmentationZero = K.chainXZeroIsoUnit.hom ≫ koszulQuotientπ.{u, u, u} φ from rfl]
    exact Category.assoc _ _ _
  have hτ := singleObjXSelf_inv_comp_quotientSingleIso_comp_eqToHom Rc (φ := φ)
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.hom_ext ?_
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  refine Eq.trans (congrArg (fun t => (eqToHom hT).val.app U t)
    (val_app_apply_congr h0 U (K.chainXZeroIsoUnit.inv.val.app U c))) ?_
  refine Eq.trans (val_app_apply_congr hτ U
    ((koszulQuotientπ.{u, u, u} φ).val.app U
      (K.chainXZeroIsoUnit.hom.val.app U (K.chainXZeroIsoUnit.inv.val.app U c)))) ?_
  exact congrArg (fun t => (koszulQuotientπ.{u, u, u} φ).val.app U t)
    (val_app_apply_congr K.chainXZeroIsoUnit.inv_hom_id U c)

/-- **The degree-zero identification carries the algebra unit to `1`.** This is the hypothesis
`SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` consumes for the target of the comparison.

The chain is: the descended identification agrees with the restricted one on sections
(`extSelfAlgebraPieceZeroIsoUnit_hom_val_app`); restriction of scalars is the identity on
sections, so the first factor of the restricted composite carries the unit of the descended
algebra to the unit of the undescended one (`SheafOfModules.GradedAlgebra.descend_one_eval`);
that unit goes to the image of `1` under `quotientPi`
(`homologyPieceZeroIsoQuotient_hom_val_app_homologyOne`); the transport there is the sheaf-level
one (`Stacks.SheafOfModules.eqToHom_over_val_app` and `over_val_app_id`), so
`quotientPi_comp_eqToHom` applies and turns it into the image of `1` under the cokernel
projection; and the last factor carries that projection to the quotient map
(`Stacks.Sites.cokernelπ_comp_cokernelIsoQuotientRingOfHom`), which on sections is the quotient
map of sheaves of rings and so sends `1` to `1`. -/
theorem extSelfAlgebraPieceZeroIsoUnit_hom_val_app_one (U : Opens ↥X) :
    (extSelfAlgebraPieceZeroIsoUnit Rc K).hom.val.app (op U)
        ((extSelfAlgebra Rc K).one.eval (op U)) =
      (1 : (toRingCat (Opens.grothendieckTopology ↥X)
        (quotientStructureSheaf Rc φ)).obj.obj (op U)) := by
  have hT : ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
      (quotient Rc (φ := φ))).X ((0 : ℤ) - 0) = quotient Rc (φ := φ) := by
    rw [sub_self]; rfl
  refine Eq.trans (extSelfAlgebraPieceZeroIsoUnit_hom_val_app Rc K (op U) _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op U) _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op U) _) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.Sites.cokernelIsoQuotientRingOfHom
    φ).hom.val.app (op U) z)
    (homologyPieceZeroIsoQuotient_hom_val_app_homologyOne Rc K U)) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.Sites.cokernelIsoQuotientRingOfHom
    φ).hom.val.app (op U) z)
    ((Stacks.SheafOfModules.eqToHom_over_val_app Rc hT U (op (Over.mk (𝟙 U))) _).symm.trans
      (Stacks.SheafOfModules.over_val_app_id Rc (eqToHom hT) U _))) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.Sites.cokernelIsoQuotientRingOfHom
    φ).hom.val.app (op U) z)
    ((SheafOfModules.comp_val_app_apply (quotientPi Rc K) (eqToHom hT) (op U)
      (1 : (structureSheaf Rc).obj.obj (op U))).symm.trans
      (val_app_apply_congr (quotientPi_comp_eqToHom Rc K) (op U) _))) ?_
  refine Eq.trans ((SheafOfModules.comp_val_app_apply (koszulQuotientπ.{u, u, u} φ)
    (Stacks.Sites.cokernelIsoQuotientRingOfHom φ).hom (op U)
    (1 : (structureSheaf Rc).obj.obj (op U))).symm.trans
    (val_app_apply_congr (Stacks.Sites.cokernelπ_comp_cokernelIsoQuotientRingOfHom φ)
      (op U) _)) ?_
  exact map_one ((quotientRingHom (quotientIdeal Rc φ)).hom.app (op U)).hom


/-- **The comparison of Stacks 0BQY is an isomorphism in degree zero.** Both graded algebras have
their zeroth piece free of rank one on the unit — the exterior algebra by construction
(`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit`), the self-Ext algebra
because `Ext⁰` is the quotient, generated by the identity class
(`extSelfAlgebraPieceZeroIsoUnit`) — and a homomorphism of graded algebras preserves the unit, so
`SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` applies.

Together with `isIso_extComparison_of_neg` this leaves only the positive degrees. -/
theorem isIso_extComparison_zero : IsIso (extComparison Rc K 0) :=
  SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero
    (extSelfExteriorAlgebra Rc K).exteriorPieceZeroIsoUnit
    (extSelfExteriorAlgebra Rc K).exteriorPieceZeroIsoUnit_one
    (extSelfAlgebraPieceZeroIsoUnit Rc K)
    (fun U => extSelfAlgebraPieceZeroIsoUnit_hom_val_app_one Rc K U.unop) _


end Stacks.RegularSequence.KoszulChainData

end
