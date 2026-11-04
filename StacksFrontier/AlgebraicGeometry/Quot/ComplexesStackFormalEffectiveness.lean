module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeOpen
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFormalEffective
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectJacobsonFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentPullbackRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent

/-!
# Strong formal effectiveness of `Complexes_{X/S}` (Stacks 0DLM), from the results it uses

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over a scheme
`S`, with `Y = S` (the source's `B = S`).  Stacks 0DLM says that `Complexes_{X/S}` is strongly
formally effective: given an inverse system `(R_n)` with surjective transition maps whose kernels
are locally nilpotent, `R = lim R_n`, and objects `ξ_n` of `Complexes_{X/S}` over `Spec R_n`
compatible under restriction, there is an object over `Spec R` restricting to all of them.  This
is condition (3) of Artin's criterion in the proof of Stacks 0DLN, and the strong formal
effectiveness Stacks 0CXU asks for in its condition (4).

The source's proof uses

* Stacks 0DIQ (derived Grothendieck existence; not yet proved here), to produce a
  pseudo-coherent `E` on `X_R` restricting to the `E_n`;
* Stacks 0CT7 (available, `henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical`), so that
  `Ker(R → R_0)` lies in the Jacobson radical of `R`;
* Stacks 0DL5 (available, `isRelativelyPerfect_of_isRelativelyPerfect_closedFibre`), to see that
  `E` is `R`-perfect;
* Stacks 0DLC, clause (1) (`AlgebraicGeometry.Space.ExistsNegativeExtLocus`; pending with 0DLC,
  which needs Stacks 0DKY and 0DKX, not yet proved here), the openness of the locus where the
  negative self-exts vanish, to get condition (2) of Stacks 0DLD.

The two missing results are explicit hypotheses `h0DIQ` and `h0DLC`, each stated at the content
of its tag: 0DIQ read at the base change `X_T ⟶ T` of the standing situation, 0DLC in its stated
form.  The rest of the source's argument is proved.  Nothing here
is registered.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower`: a tower of test schemes `T_n` with
  `T_n ≅ Spec R_n`, mapping compatibly to a test scheme `T ≅ Spec (lim R_n)`, the transition maps
  of `(R_n)` being surjective with locally nilpotent kernels: the geometric data of Situation
  0DIK at `X_T ⟶ T`.
* `AlgebraicGeometry.Space.ComplexesSituation.NegativeExtLocusOpen`: Stacks 0DLC, clause (1), at
  `X_T ⟶ T` with an open of the scheme `T`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.negativeExtLocusOpen_of_existsNegativeExtLocus`:
  the open subspace of 0DLC (1) gives an open of the scheme `T` (Stacks 03BZ, 03BX).
* `AlgebraicGeometry.Space.ComplexesSituation.exists_realization_of_specLimitTower`: the source's
  proof, for a compatible system of objects over the levels of a tower: there is an object over
  its limit with compatible morphisms from all levels.
* `AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of`: for `Y = S`, every
  formal object of `Complexes_{X/S}` is effective (Stacks 07X7); this is the hypothesis `h0DLM`
  of `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.
* `AlgebraicGeometry.Space.ComplexesSituation.isStronglyFormallyEffective_complexes_of`: for
  `Y = S` locally Noetherian, `Complexes_{X/S}` is strongly formally effective (Stacks 0CXT).

## Implementation notes

The hypothesis `h0DIQ` is written out in each statement rather than named by a definition.  A
proposition-valued definition has its nested proofs abstracted into auxiliary lemmas, and
comparing the derived-category terms it then produces with the same terms elaborated in a
statement exhausts the kernel; the inline form is elaborated with the statements it is compared
with.  For the same reason the levels and transitions of a sequence of objects are passed to it
through the names `AlgebraicGeometry.Space.ComplexesSituation.levelOf` and
`AlgebraicGeometry.Space.ComplexesSituation.transitionOf` rather than as `fun`s.

## References

* [Stacks Project, Tag 0DLM](https://stacks.math.columbia.edu/tag/0DLM)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DL5](https://stacks.math.columbia.edu/tag/0DL5)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0CT7](https://stacks.math.columbia.edu/tag/0CT7)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] complexesCategory

variable (D : ComplexesSituation B S hS)

/-! ### The tower of test schemes -/

/-- **A tower of test schemes over a limit of rings.**  Test schemes `T_n` over `Y` with
transition maps `T_n ⟶ T_{n+1}` (the parameters), a test scheme `T` with compatible maps
`T_n ⟶ T`, an inverse system of rings `(R_n)` with surjective transition maps whose kernels are
locally nilpotent and a limit cone `R = lim R_n`, and identifications `T_n ≅ Spec R_n`,
`T ≅ Spec R` under which the maps are the ones induced by the rings.

This is the geometric data of Situation 0DIK read at the base change `X_T ⟶ T`: the base changes
`X_{T_n}` are the base changes of `X_T` along `Spec R_n ⟶ Spec R`. -/
structure SpecLimitTower (level : ℕ → SchemesOver D.Y)
    (transition : ∀ n, level n ⟶ level (n + 1)) where
  /-- The inverse system of rings `(R_n)`. -/
  R : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- The limit cone `R = lim R_n`. -/
  cR : Cone R
  /-- It is a limit. -/
  isLimit : IsLimit cR
  /-- The transition maps are surjective. -/
  surjective (n : ℕ) : Function.Surjective (R.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of the transition maps are locally nilpotent. -/
  locallyNilpotent (n : ℕ) :
    (RingHom.ker (R.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The test scheme over the limit. -/
  T : SchemesOver D.Y
  /-- The maps from the levels to it. -/
  toLimit (n : ℕ) : level n ⟶ T
  /-- They are compatible with the transitions. -/
  transition_toLimit (n : ℕ) : transition n ≫ toLimit (n + 1) = toLimit n
  /-- The identification `T_n ≅ Spec R_n`. -/
  e (n : ℕ) : (BigFppfOver.toScheme B S hS).obj (level n).left ≅ Spec (R.obj (op n))
  /-- The identification `T ≅ Spec R`. -/
  eLimit : (BigFppfOver.toScheme B S hS).obj T.left ≅ Spec cR.pt
  /-- The transitions are the maps induced by the rings. -/
  transition_e (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (transition n).left ≫ (e (n + 1)).hom =
      (e n).hom ≫ Spec.map (R.map (homOfLE (Nat.le_succ n)).op)
  /-- The maps to the limit are the maps induced by the limit projections. -/
  toLimit_e (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (toLimit n).left ≫ eLimit.hom =
      (e n).hom ≫ Spec.map (cR.π.app (op n))

/-! ### The results the source's proof uses, at the base changes of the situation -/

/-- **Stacks 0DLC, clause (1), at `X_T ⟶ T`, with an open of the scheme `T`.**  For `K`
pseudo-coherent and `E` `T`-perfect in `D(𝒪_{X_T})` there is an open `W` of `T` such that a point
`y : Spec k ⟶ T` with values in a field lies in `W` if and only if
`Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for all `i < 0`.  It follows from the form of 0DLC (1) with an
open subspace, `AlgebraicGeometry.Space.ExistsNegativeExtLocus`, by
`AlgebraicGeometry.Space.ComplexesSituation.negativeExtLocusOpen_of_existsNegativeExtLocus`. -/
def NegativeExtLocusOpen : Prop :=
  ∀ (T : SchemesOver D.Y) (K E : derivedModules B S hS (D.space T)),
    (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).IsPseudoCoherent K →
    D.IsRelativelyPerfect T E →
    ∃ W : ((BigFppfOver.toScheme B S hS).obj T.left).Opens,
      ∀ (T₀ : SchemesOver D.Y), Stack.IsFieldObject B S hS T₀.left → ∀ y : T₀ ⟶ T,
        (Set.range ((BigFppfOver.toScheme B S hS).map y.left).base ⊆ (W : Set _) ↔
          ∀ i : ℤ, i < 0 →
            Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj K ⟶
              (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E)⟦i⟧))

namespace SpecLimitTower

variable {D} {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
  (L : D.SpecLimitTower level transition)

/-- The projection `lim R_n ⟶ R_0` is surjective, the transition maps being surjective. -/
theorem surjective_π_zero : Function.Surjective (L.cR.π.app (op 0)).hom :=
  Concrete.surjective_π_app_zero_of_surjective_map L.isLimit L.surjective

/-- **Stacks 0CT7.** The kernel of `lim R_n ⟶ R_n` lies in the Jacobson radical of `lim R_n`. -/
theorem ker_π_le_jacobson (n : ℕ) :
    RingHom.ker (L.cR.π.app (op n)).hom ≤ (⊥ : Ideal L.cR.pt).jacobson :=
  (henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical L.R L.cR L.isLimit
    (fun k => ⟨L.surjective k, fun x hx => (mem_nilradical).2 (L.locallyNilpotent k x hx)⟩) n).jac

end SpecLimitTower

/-! ### Points with values in residue fields -/

/-- The spectrum `Spec κ(w)` of the residue field at a point `w` of an object `U` of the site, as
an object of the site over `S`, through `Spec κ(w) ⟶ U`. -/
def fieldPointOver (U : BigFppfOver B S hS) (w : (BigFppfOver.toScheme B S hS).obj U) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj (B.residueField_spec_contains U.left.2 w))
    (Y := U.left) (Scheme.fromSpecResidueField _ w) ≫ U.hom)

/-- The morphism `Spec κ(w) ⟶ U`. -/
def fieldPointOverHom (U : BigFppfOver B S hS) (w : (BigFppfOver.toScheme B S hS).obj U) :
    fieldPointOver U w ⟶ U :=
  Over.homMk (ObjectProperty.homMk (X := B.obj (B.residueField_spec_contains U.left.2 w))
    (Y := U.left) (Scheme.fromSpecResidueField _ w)) rfl

/-- The test scheme `Spec κ(w)` over `Y` at a point `w` of a test scheme `T`. -/
def fieldPointTestScheme (T : SchemesOver D.Y) (w : (BigFppfOver.toScheme B S hS).obj T.left) :
    SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (fieldPointOverHom T.left w) ≫ T.hom)

/-- The morphism of test schemes `Spec κ(w) ⟶ T`. -/
def fieldPointTestSchemeHom (T : SchemesOver D.Y)
    (w : (BigFppfOver.toScheme B S hS).obj T.left) : D.fieldPointTestScheme T w ⟶ T :=
  CostructuredArrow.homMk (fieldPointOverHom T.left w) rfl

/-- `Spec κ(w)` is the spectrum of a field. -/
theorem isFieldObject_fieldPointTestScheme (T : SchemesOver D.Y)
    (w : (BigFppfOver.toScheme B S hS).obj T.left) :
    Stack.IsFieldObject B S hS (D.fieldPointTestScheme T w).left :=
  ⟨_, inferInstance, ⟨Iso.refl _⟩⟩

/-- The point `w` is the image of `Spec κ(w) ⟶ T`. -/
theorem mem_range_fieldPointTestSchemeHom (T : SchemesOver D.Y)
    (w : (BigFppfOver.toScheme B S hS).obj T.left) :
    w ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (D.fieldPointTestSchemeHom T w).left).base := by
  show w ∈ Set.range (Scheme.fromSpecResidueField _ w).base
  rw [Scheme.range_fromSpecResidueField]
  rfl

namespace SpecLimitTower

variable {D} {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
  (L : D.SpecLimitTower level transition)

/-- The map `T_0 ⟶ T` is `T_0 ≅ Spec R_0 ⟶ Spec (lim R_n) ≅ T`, read in schemes. -/
private theorem map_toLimit_zero_left :
    (BigFppfOver.toScheme B S hS).map (L.toLimit 0).left =
      (L.e 0).hom ≫ Spec.map (L.cR.π.app (op 0)) ≫ L.eLimit.inv := by
  rw [← reassoc_of% (L.toLimit_e 0)]
  simp

/-- **An open of `T = Spec (lim R_n)` containing the image of `T_0` is everything**: the kernel of
`lim R_n ⟶ R_0` lies in the Jacobson radical (Stacks 0CT7), so every nonempty closed subset of
`Spec (lim R_n)` meets its zero locus, which is the image of `Spec R_0`. -/
theorem mem_of_range_toLimit_zero_subset
    (W : ((BigFppfOver.toScheme B S hS).obj L.T.left).Opens)
    (hW : Set.range ((BigFppfOver.toScheme B S hS).map (L.toLimit 0).left).base ⊆ (W : Set _))
    (z : (BigFppfOver.toScheme B S hS).obj L.T.left) : z ∈ W := by
  by_contra hz
  let Z : Set (PrimeSpectrum L.cR.pt) := L.eLimit.inv.base ⁻¹' (W : Set _)ᶜ
  have hZ : IsClosed Z := W.isOpen.isClosed_compl.preimage L.eLimit.inv.continuous
  have hne : Z.Nonempty := ⟨L.eLimit.hom.base z, by
    show L.eLimit.inv.base (L.eLimit.hom.base z) ∉ W
    rwa [show L.eLimit.inv.base (L.eLimit.hom.base z) = z from
      (Scheme.homeoOfIso L.eLimit).symm_apply_apply z]⟩
  obtain ⟨p, hpZ, hpI⟩ := exists_mem_inter_zeroLocus_of_isClosed hZ hne (L.ker_π_le_jacobson 0)
  rw [← range_comap_of_surjective _ _ L.surjective_π_zero] at hpI
  obtain ⟨q, rfl⟩ := hpI
  apply hpZ
  let q' : Spec (L.R.obj (op 0)) := q
  have hq : (L.e 0).hom ((L.e 0).inv q') = q' := (Scheme.homeoOfIso (L.e 0)).apply_symm_apply q'
  have := hW ⟨(L.e 0).inv q', rfl⟩
  rwa [L.map_toLimit_zero_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hq] at this

end SpecLimitTower

/-! ### Clause (1) of Stacks 0DLC with an open of the scheme -/

section NegativeExtLocus

attribute [local instance] pointTopology

/-- **Stacks 0DLC, clause (1), at `X_T ⟶ T` with an open of the scheme `T`**, from its form
`AlgebraicGeometry.Space.ExistsNegativeExtLocus` with an open subspace.  The open subspace `W` of
`T` is the subspace cut out by its points (Stacks 03BZ), whose image in the scheme `T` is open
(Stacks 03BX); a point `y : T₀ ⟶ T` with values in a field lies in `W` exactly when its image
does, and the fibre of `X_T ⟶ T` over `y` is `X_{T₀}`. -/
theorem negativeExtLocusOpen_of_existsNegativeExtLocus (h : ExistsNegativeExtLocus B S hS) :
    D.NegativeExtLocusOpen := by
  intro T K E hK hE
  let F := (schemeSpaceFunctor B S hS).obj T.left
  obtain ⟨W, hW⟩ := h (D.projection T)
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.proper)
    (D.projection_isFlat T)
    ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation)
    K E hK hE
  let P := pointsOpensOfOpenSubspace B S hS F.1 W
  have hWP : W = ⟨openSubspaceOfPoints B S hS F.1 P,
      isOpenSubspace_openSubspaceOfPoints B S hS F.2 _ P.2⟩ :=
    (openSubspacesOrderIso B S hS F.1 F.2).injective (TopologicalSpace.Opens.ext
      (range_pointsMap_ι_openSubspaceOfPoints B S hS (F := F.1) (P : Set _)).symm)
  refine ⟨⟨pointsToScheme B S hS T.left '' P.1,
    (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS T.left P.1).1 P.2⟩, fun T₀ hT₀ y => ?_⟩
  let T₀' : SchemesOver F := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map y.left)
  have hpb := isPullback_baseChangeMap D.f y
  let φ := hpb.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS
    (D.projection T) T₀'.hom)
  have hφ : φ.hom ≫ baseChangeProjection (D.projection T) T₀' = D.relativeMap y :=
    hpb.isoIsPullback_hom_fst _ _ _
  have hmem : testPoint T₀' ∈ W.1.obj (Opposite.op T₀'.left) ↔
      Set.range (pointsMap B S hS (yoneda.obj T₀.left) (yoneda.map y.left)) ⊆ P.1 := by
    rw [hWP]
    exact (mem_openSubspaceOfPoints_iff B S hS (P : Set _) (testPoint T₀')).trans
      (by rw [yonedaEquiv_symm_testPoint])
  have hext : HasNoNegativeExtAt (D.projection T) K E T₀' ↔ ∀ i : ℤ, i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E)⟦i⟧) :=
    forall_congr' fun i => imp_congr_right fun _ => subsingleton_pull_iff_of_iso φ hφ K E i
  exact (range_pointsMap_yoneda_subset_iff B S hS y.left P.1).symm.trans
    (hmem.symm.trans ((hW T₀' hT₀).trans hext))

end NegativeExtLocus

/-! ### The limit of a tower as a spectrum -/

namespace SpecLimitTower

variable {D} {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
  (L : D.SpecLimitTower level transition)

/-- `Spec (lim R_n)` belongs to the site, being isomorphic to `T`. -/
theorem contains_spec_limit : B.Contains (Spec L.cR.pt) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact L.eLimit.inv) L.T.left.left.2

/-- `Spec (lim R_n / I)` belongs to the site, `I` being the kernel of `lim R_n ⟶ R_0`. -/
theorem contains_spec_quotient :
    B.Contains (Spec (CommRingCat.of (L.cR.pt ⧸ RingHom.ker (L.cR.π.app (op 0)).hom))) := by
  have : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (RingHom.ker (L.cR.π.app (op 0)).hom)))) :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker (L.cR.π.app (op 0)).hom))))) L.contains_spec_limit

/-- The structure morphism `Spec (lim R_n) ≅ T ⟶ S`. -/
abbrev limitStructureMap : B.obj L.contains_spec_limit ⟶ B.obj hS :=
  ObjectProperty.homMk (L.eLimit.inv ≫ L.T.left.hom.hom)

/-- The identification `Spec (lim R_n) ≅ T`, one direction, in the site over `S`. -/
def limitSpecHom : specFppfOver B S hS L.contains_spec_limit L.limitStructureMap ⟶ L.T.left :=
  Over.homMk (ObjectProperty.homMk L.eLimit.inv) rfl

/-- The identification `Spec (lim R_n) ≅ T`, the other direction, in the site over `S`. -/
def limitSpecInv : L.T.left ⟶ specFppfOver B S hS L.contains_spec_limit L.limitStructureMap :=
  Over.homMk (ObjectProperty.homMk L.eLimit.hom) (by
    apply ObjectProperty.hom_ext
    change L.eLimit.hom ≫ L.eLimit.inv ≫ L.T.left.hom.hom = L.T.left.hom.hom
    rw [Iso.hom_inv_id_assoc])

/-- The map `T ⟶ Spec (lim R_n) ⟶ T` is the identity. -/
theorem limitSpecInv_limitSpecHom : L.limitSpecInv ≫ L.limitSpecHom = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact L.eLimit.hom_inv_id

/-- `Spec (lim R_n)` as a test scheme over `Y`, through `T`. -/
abbrev limitSpec : SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map L.limitSpecHom ≫ L.T.hom)

/-- The test-scheme morphism `Spec (lim R_n) ⟶ T`. -/
def limitSpecToT : L.limitSpec ⟶ L.T := CostructuredArrow.homMk L.limitSpecHom rfl

/-- The test-scheme morphism `T ⟶ Spec (lim R_n)`. -/
def limitSpecOfT : L.T ⟶ L.limitSpec :=
  CostructuredArrow.homMk L.limitSpecInv (by
    change (schemeSpaceFunctor B S hS).map L.limitSpecInv ≫
      (schemeSpaceFunctor B S hS).map L.limitSpecHom ≫ L.T.hom = L.T.hom
    rw [← Functor.map_comp_assoc, limitSpecInv_limitSpecHom, CategoryTheory.Functor.map_id,
      Category.id_comp])

/-- The test-scheme morphism `T ⟶ Spec (lim R_n) ⟶ T` is the identity. -/
theorem limitSpecOfT_limitSpecToT : L.limitSpecOfT ≫ L.limitSpecToT = 𝟙 _ :=
  CostructuredArrow.hom_ext _ _ L.limitSpecInv_limitSpecHom

/-- `Spec (lim R_n / I)` as a test scheme over `Y`, through `Spec (lim R_n)`. -/
abbrev closedFibreSpec : SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (quotientSpecMap B S hS
    L.contains_spec_limit L.limitStructureMap (RingHom.ker (L.cR.π.app (op 0)).hom)
    L.contains_spec_quotient) ≫ L.limitSpec.hom)

/-- The closed immersion `Spec (lim R_n / I) ⟶ Spec (lim R_n)` of test schemes. -/
def closedFibreSpecMap : L.closedFibreSpec ⟶ L.limitSpec := CostructuredArrow.homMk _ rfl

/-- The isomorphism `R_0 ≅ lim R_n / I`, read as a ring map `R_0 ⟶ lim R_n / I`. -/
abbrev quotientOfLevelZero :
    L.R.obj (op 0) ⟶ CommRingCat.of (L.cR.pt ⧸ RingHom.ker (L.cR.π.app (op 0)).hom) :=
  CommRingCat.ofHom (RingHom.quotientKerEquivOfSurjective L.surjective_π_zero).symm.toRingHom

/-- The composite `lim R_n ⟶ R_0 ≅ lim R_n / I` is the quotient map. -/
theorem π_zero_comp_quotientOfLevelZero :
    L.cR.π.app (op 0) ≫ L.quotientOfLevelZero =
      CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (L.cR.π.app (op 0)).hom)) := by
  ext x
  exact (RingEquiv.symm_apply_eq _).2
    (RingHom.quotientKerEquivOfSurjective_apply_mk L.surjective_π_zero x).symm

/-- The map `Spec (lim R_n / I) ≅ Spec R_0 ≅ T_0 ⟶ T` is
`Spec (lim R_n / I) ⟶ Spec (lim R_n) ≅ T`. -/
theorem specMap_quotientOfLevelZero_comp :
    Spec.map L.quotientOfLevelZero ≫ (L.e 0).inv ≫
        (BigFppfOver.toScheme B S hS).map (L.toLimit 0).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (L.cR.π.app (op 0)).hom))) ≫
        L.eLimit.inv := by
  rw [map_toLimit_zero_left, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc,
    π_zero_comp_quotientOfLevelZero]

/-- The map `Spec (lim R_n / I) ⟶ T_0` in the site over `S`. -/
def closedFibreToLevelZeroLeft :
    (L.closedFibreSpec).left ⟶ (level 0).left :=
  Over.homMk (ObjectProperty.homMk (Spec.map L.quotientOfLevelZero ≫ (L.e 0).inv)) (by
    apply ObjectProperty.hom_ext
    have hw := congrArg (fun g => g.hom) (Over.w (L.toLimit 0).left)
    change (Spec.map L.quotientOfLevelZero ≫ (L.e 0).inv) ≫ (level 0).left.hom.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (L.cR.π.app (op 0)).hom))) ≫
        L.eLimit.inv ≫ L.T.left.hom.hom
    rw [← hw]
    change (Spec.map L.quotientOfLevelZero ≫ (L.e 0).inv) ≫
      (BigFppfOver.toScheme B S hS).map (L.toLimit 0).left ≫ L.T.left.hom.hom = _
    simpa only [Category.assoc] using
      congrArg (fun g => g ≫ (Over.hom L.T.left).hom) L.specMap_quotientOfLevelZero_comp)

/-- The maps `Spec (lim R_n / I) ⟶ T_0 ⟶ T` and `Spec (lim R_n / I) ⟶ Spec (lim R_n) ≅ T` agree
in the site over `S`. -/
theorem closedFibreToLevelZeroLeft_comp :
    L.closedFibreToLevelZeroLeft ≫ (L.toLimit 0).left =
      L.closedFibreSpecMap.left ≫ L.limitSpecHom := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact (Category.assoc _ _ _).trans L.specMap_quotientOfLevelZero_comp

/-- The test-scheme morphism `Spec (lim R_n / I) ⟶ T_0`. -/
def closedFibreToLevelZero : L.closedFibreSpec ⟶ level 0 :=
  CostructuredArrow.homMk L.closedFibreToLevelZeroLeft (by
    have hw := CostructuredArrow.w (L.toLimit 0)
    change (schemeSpaceFunctor B S hS).map L.closedFibreToLevelZeroLeft ≫ (level 0).hom =
      (schemeSpaceFunctor B S hS).map L.closedFibreSpecMap.left ≫
        (schemeSpaceFunctor B S hS).map L.limitSpecHom ≫ L.T.hom
    rw [← hw, ← Functor.map_comp_assoc, closedFibreToLevelZeroLeft_comp, Functor.map_comp_assoc])

/-- The test-scheme morphisms `Spec (lim R_n / I) ⟶ T_0 ⟶ T` and
`Spec (lim R_n / I) ⟶ Spec (lim R_n) ⟶ T` agree. -/
theorem closedFibreToLevelZero_comp :
    L.closedFibreToLevelZero ≫ L.toLimit 0 = L.closedFibreSpecMap ≫ L.limitSpecToT :=
  CostructuredArrow.hom_ext _ _ L.closedFibreToLevelZeroLeft_comp

end SpecLimitTower

/-! ### The source's proof over a tower -/

/-- **Condition (1) of Stacks 0DLD over the limit of a tower**, by Stacks 0DL5: a pseudo-coherent
`E` on `X_T` whose restriction to `X_{T_0}` is `T_0`-perfect is `T`-perfect, `Ker(R → R_0)` lying
in the Jacobson radical of `R = lim R_n` (Stacks 0CT7).

Stacks 0DL5 (`AlgebraicGeometry.Space.isRelativelyPerfect_of_isRelativelyPerfect_closedFibre`) is
stated over `Spec R` and `Spec (R/I)` themselves, so it is applied to the derived pullback `E'`
of `E` along `X_{Spec R} ⟶ X_T`, with `I = Ker(R → R_0)`.  The restriction of `E'` to
`X_{Spec (R/I)}` is the pullback of `E_0` along `Spec (R/I) ≅ Spec R_0 ≅ T_0`, which is
`Spec (R/I)`-perfect by Stacks 0DKT; and `E` is the pullback of `E'` along `T ≅ Spec R`, hence
`T`-perfect by Stacks 0DKT again. -/
theorem isRelativelyPerfect_of_specLimitTower
    {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
    (L : D.SpecLimitTower level transition) (E : derivedModules B S hS (D.space L.T))
    (hE : (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E)
    {E₀ : derivedModules B S hS (D.space (level 0))} (h₀ : D.IsRelativelyPerfect (level 0) E₀)
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (L.toLimit 0))).obj E ≅ E₀) :
    D.IsRelativelyPerfect L.T E := by
  let P := smallEtaleDerivedPullbackData B S hS
  let E' := (P.pull (D.relativeMap L.limitSpecToT)).obj E
  have hE' : (smallEtaleRingedSite B S hS (D.space L.limitSpec).1
      (D.space L.limitSpec).2).IsPseudoCoherent E' :=
    isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS
      (D.relativeMap L.limitSpecToT) (relativelyRepresentable_baseChangeMap B S hS D.f _) E hE
  have hiso : ∀ (T : SchemesOver D.Y) {M M' : derivedModules B S hS (D.space T)} (e : M ≅ M'),
      D.IsRelativelyPerfect T M → D.IsRelativelyPerfect T M' := fun T M M' e hM => by
    have := isClosedUnderIsomorphisms_isPerfectRelativeTo B S hS (D.projection T)
      (D.projection_isFlat T) (D.projection_isLocallyOfFinitePresentation T)
      (canonicalSliceDerivedTensorProduct B S hS (D.projection T))
    exact (isPerfectRelativeTo B S hS (D.projection T) (D.projection_isFlat T)
      (D.projection_isLocallyOfFinitePresentation T)
      (canonicalSliceDerivedTensorProduct B S hS (D.projection T))).prop_of_iso e hM
  have h₀' : D.IsRelativelyPerfect L.closedFibreSpec
      ((P.pull (D.relativeMap L.closedFibreSpecMap)).obj E') :=
    hiso _ (((P.pull (D.relativeMap L.closedFibreToLevelZero)).mapIso ψ).symm ≪≫
        ((D.compComparison L.closedFibreToLevelZero (L.toLimit 0)).app E).symm ≪≫
        (D.relativeMapComparison L.closedFibreToLevelZero_comp).app E ≪≫
        (D.compComparison L.closedFibreSpecMap L.limitSpecToT).app E)
      (D.relativelyPerfectBaseChange L.closedFibreToLevelZero E₀ h₀)
  -- The instances of Stacks 0DL5 are stated with the target written as a represented space.
  let 𝒮 : AlgebraicSpaces B S hS := ⟨yoneda.obj (specFppfOver B S hS L.contains_spec_limit
    L.limitStructureMap), isAlgebraicSpace_yoneda B S hS _⟩
  let 𝒮₀ : AlgebraicSpaces B S hS := ⟨yoneda.obj (specFppfOver B S hS L.contains_spec_quotient
    (quotientStructureMap B S hS L.contains_spec_limit L.limitStructureMap
      (RingHom.ker (L.cR.π.app (op 0)).hom) L.contains_spec_quotient)),
    isAlgebraicSpace_yoneda B S hS _⟩
  let f : D.space L.limitSpec ⟶ 𝒮 := D.projection L.limitSpec
  let f₀ : D.space L.closedFibreSpec ⟶ 𝒮₀ := D.projection L.closedFibreSpec
  let : HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u}
      (inverseImageRingedSite B S hS f)) := HasDerivedCategory.standard _
  let : ∀ U : (inverseImageRingedSite B S hS f).C, HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) :=
    fun _ => HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u}
      (inverseImageRingedSite B S hS f₀)) := HasDerivedCategory.standard _
  let : ∀ U : (inverseImageRingedSite B S hS f₀).C, HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f₀).over U)) :=
    fun _ => HasDerivedCategory.standard _
  have h' : D.IsRelativelyPerfect L.limitSpec E' :=
    isRelativelyPerfect_of_isRelativelyPerfect_closedFibre B S hS (R := L.cR.pt)
      (hR := L.contains_spec_limit) (gR := L.limitStructureMap)
      (I := RingHom.ker (L.cR.π.app (op 0)).hom) (hR₀ := L.contains_spec_quotient)
      f f₀ (L.ker_π_le_jacobson 0) (D.relativeMap L.closedFibreSpecMap)
      (isPullback_baseChangeMap D.f L.closedFibreSpecMap)
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f L.limitSpec.hom) D.proper)
      (D.projection_isFlat _) (D.projection_isLocallyOfFinitePresentation _) E' hE' h₀'
  exact hiso _ (((D.compComparison L.limitSpecOfT L.limitSpecToT).app E).symm ≪≫
      (D.relativeMapComparison L.limitSpecOfT_limitSpecToT).app E ≪≫ (D.idComparison L.T).app E)
    (D.relativelyPerfectBaseChange L.limitSpecOfT E' h')

/-- **Condition (2) of Stacks 0DLD over the limit of a tower**, by Stacks 0DLC: the points of `T`
where the negative self-exts of the fibres of `E` vanish form an open, which contains the image
of `T_0` because there the fibres of `E` are those of its restriction `E_0`; `Ker(R → R_0)` lying
in the Jacobson radical (Stacks 0CT7), that open is everything. -/
theorem hasNoNegativeFibreExt_of_specLimitTower (h0DLC : D.NegativeExtLocusOpen)
    {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
    (L : D.SpecLimitTower level transition) (E : derivedModules B S hS (D.space L.T))
    (hE : (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E)
    (h₁ : D.IsRelativelyPerfect L.T E)
    {E₀ : derivedModules B S hS (D.space (level 0))} (h₀ : D.HasNoNegativeFibreExt (level 0) E₀)
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (L.toLimit 0))).obj E ≅ E₀) :
    D.HasNoNegativeFibreExt L.T E := by
  obtain ⟨W, hW⟩ := h0DLC L.T E E hE h₁
  have hall : ∀ z, z ∈ W := L.mem_of_range_toLimit_zero_subset W (by
    rintro _ ⟨w, rfl⟩
    by_contra hz
    have hy := (hW _ (D.isFieldObject_fieldPointTestScheme (level 0) w)
      (D.fieldPointTestSchemeHom (level 0) w ≫ L.toLimit 0)).not.mp (by
        intro hsub
        apply hz
        obtain ⟨s, hs⟩ := D.mem_range_fieldPointTestSchemeHom (level 0) w
        have := hsub ⟨s, rfl⟩
        rwa [CostructuredArrow.comp_left, Functor.map_comp, Scheme.Hom.comp_apply, hs] at this)
    apply hy
    intro i hi
    have := h₀ _ (D.isFieldObject_fieldPointTestScheme (level 0) w)
      (D.fieldPointTestSchemeHom (level 0) w) i hi
    let e := (D.compComparison (D.fieldPointTestSchemeHom (level 0) w) (L.toLimit 0)).app E ≪≫
      ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (D.fieldPointTestSchemeHom (level 0) w))).mapIso ψ
    exact Equiv.subsingleton (e.homCongr ((shiftFunctor _ i).mapIso e)))
  intro T₀ hT₀ y i hi
  exact (hW T₀ hT₀ y).mp (fun x _ => hall x) i hi

/-- The test schemes of a sequence of objects of `Complexes_{X/Y}`.  A name rather than a
`fun`, so that instantiating a hypothesis at it leaves no β-redex for the kernel to compare. -/
abbrev levelOf {D : ComplexesSituation B S hS} (A : ℕ → ComplexesObject D) (n : ℕ) :
    SchemesOver D.Y :=
  (A n).T

/-- The base maps of a sequence of morphisms of `Complexes_{X/Y}`. -/
abbrev transitionOf {D : ComplexesSituation B S hS} {A : ℕ → ComplexesObject D}
    (m : ∀ n, A n ⟶ A (n + 1)) (n : ℕ) :
    levelOf A n ⟶ levelOf A (n + 1) :=
  (m n : ComplexesHom (A n) (A (n + 1))).base

/-- The complexes of a sequence of objects of `Complexes_{X/Y}`. -/
abbrev complexAt {D : ComplexesSituation B S hS} (A : ℕ → ComplexesObject D) (n : ℕ) :
    derivedModules B S hS (D.space (levelOf A n)) :=
  (A n).E

/-- The comparisons of complexes of a sequence of morphisms of `Complexes_{X/Y}`. -/
abbrev comparisonOf {D : ComplexesSituation B S hS} {A : ℕ → ComplexesObject D}
    (m : ∀ n, A n ⟶ A (n + 1)) (n : ℕ) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (transitionOf m n))).obj
      (complexAt A (n + 1)) ⟶ complexAt A n :=
  (m n : ComplexesHom (A n) (A (n + 1))).fibre

/-- **The morphisms to the limit are compatible with the transitions**: given maps
`g_n : T_n ⟶ T` with `h_n ≫ g_{n+1} = g_n` and isomorphisms `ψ_n : L(X_{g_n})^* E ⟶ E_n`
compatible with the comparisons `φ_n` of the given morphisms `(h_n, φ_n) : ξ_n ⟶ ξ_{n+1}`, the
morphisms `(g_n, ψ_n) : ξ_n ⟶ (T, E)` satisfy `(h_n, φ_n) ≫ (g_{n+1}, ψ_{n+1}) = (g_n, ψ_n)`. -/
theorem comp_towerHom_eq {A : ℕ → ComplexesObject D} (m : ∀ n, A n ⟶ A (n + 1))
    (L : D.SpecLimitTower (levelOf A) (transitionOf m)) (E : derivedModules B S hS (D.space L.T))
    (h₁ : D.IsRelativelyPerfect L.T E) (h₂ : D.HasNoNegativeFibreExt L.T E)
    (ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (L.toLimit n))).obj E ⟶
      complexAt A n) (hψ : ∀ n, IsIso (ψ n))
    (hc : ∀ n, Functor.fibreComp (D.compComparison (transitionOf m n) (L.toLimit (n + 1)))
        (comparisonOf m n) (ψ (n + 1)) =
      (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n) (n : ℕ) :
    ComplexesHom.comp (A'' := (⟨L.T, E, h₁, h₂⟩ : ComplexesObject D)) (m n)
      ⟨L.toLimit (n + 1), ψ (n + 1), hψ (n + 1)⟩ = ⟨L.toLimit n, ψ n, hψ n⟩ := by
  refine complexesHom_eq_of_heq (L.transition_toLimit n) ?_
  refine heq_of_eq_eqToHom_comp (congrArg (fun k : (A n).T ⟶ L.T =>
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj E)
      (L.transition_toLimit n)) (ψ n) ?_
  rw [ComplexesHom.comp_fibre]
  exact (hc n).trans (by rw [D.relativeMapComparison_hom_app])

/-- **The source's proof of Stacks 0DLM, over a tower of test schemes.**  Let `ξ_n = (T_n, E_n)`
be objects of `Complexes_{X/Y}` with morphisms `ξ_n ⟶ ξ_{n+1}`, over a tower `T_n ≅ Spec R_n` with
limit `T ≅ Spec R`, `R = lim R_n`.  Then there is an object `(T, E)` over the limit with morphisms
`ξ_n ⟶ (T, E)` over the maps `T_n ⟶ T`, compatible with the given ones.

* Stacks 0DIQ (`h0DIQ`; not yet proved here), read at `X_T ⟶ T`: for pseudo-coherent
  `K_n` on `X_{T_n}` with isomorphisms `φ_n : L(X_{T_n} ⟶ X_{T_{n+1}})^* K_{n+1} ⟶ K_n` there is a
  pseudo-coherent `K` on `X_T` with isomorphisms `ψ_n : L(X_{T_n} ⟶ X_T)^* K ⟶ K_n` compatible
  with the `φ_n` (the composite of the composition comparison, the pullback of `ψ_{n+1}` and
  `φ_n` is `ψ_n`).  It produces `E` restricting to the `E_n` compatibly with the transitions;
  these are the morphisms `ξ_n ⟶ (T, E)`.
* `Ker(R → R_0)` lies in the Jacobson radical of `R` (Stacks 0CT7), so Stacks 0DL5 shows that
  `E` is `T`-perfect, its restriction `E_0` to `X_{T_0}` being `T_0`-perfect.
* By Stacks 0DLC, clause (1) (`h0DLC`; pending with 0DLC, which needs Stacks 0DKY and 0DKX, not yet
  proved here) the points of `T` where the negative self-exts of the fibres of `E`
  vanish form an open; it contains the image of `T_0`, where the fibres are those of `E_0`, hence
  is everything, `Ker(R → R_0)` lying in the Jacobson radical. -/
theorem exists_realization_of_specLimitTower
    (h0DIQ : ∀ {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B S hS (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B S hS (D.space L.T)),
        (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h0DLC : ExistsNegativeExtLocus B S hS)
    (A : ℕ → ComplexesObject D) (m : ∀ n, A n ⟶ A (n + 1))
    (L : D.SpecLimitTower (levelOf A) (transitionOf m)) :
    ∃ (E : derivedModules B S hS (D.space L.T)) (h₁ : D.IsRelativelyPerfect L.T E)
      (h₂ : D.HasNoNegativeFibreExt L.T E)
      (r : ∀ n, ComplexesHom (A n) (⟨L.T, E, h₁, h₂⟩ : ComplexesObject D)),
      (∀ n, (r n).base = L.toLimit n) ∧ ∀ n, ComplexesHom.comp (m n) (r (n + 1)) = r n := by
  obtain ⟨E, hE, ψ, hψ, hcompat⟩ := h0DIQ L (complexAt A)
    (fun n => (A n).relativelyPerfect.1) (comparisonOf m)
    (fun n => inferInstanceAs (IsIso (m n).fibre))
  have := hψ 0
  have h₁ := D.isRelativelyPerfect_of_specLimitTower L E hE (A 0).relativelyPerfect
    (asIso (ψ 0))
  have h₂ := D.hasNoNegativeFibreExt_of_specLimitTower
    (D.negativeExtLocusOpen_of_existsNegativeExtLocus h0DLC) L E hE h₁ (A 0).noNegativeFibreExt
    (asIso (ψ 0))
  refine ⟨E, h₁, h₂, fun n => ⟨L.toLimit n, ψ n, hψ n⟩, fun n => rfl, fun n => ?_⟩
  exact D.comp_towerHom_eq m L E h₁ h₂ ψ hψ hcompat n

/-! ### Formal objects -/

section FormalObjects

open Deformation.Artin IsLocalRing AlgebraicGeometry.PolarizedFormal

variable {D} (hY : IsTerminal D.Y) (ξ : FormalObject B S hS (complexesFunctor D))

/-- Read in schemes, a morphism of the site which is a transport of `t` along equalities of its
ends is `t`, transported along the induced equalities of schemes. -/
theorem toScheme_map_comp_eqToHom {X₀ X₁ Y₀ Y₁ : BigFppfOver B S hS} (h₀ : X₀ = Y₀)
    (h₁ : X₁ = Y₁) {t : Y₀ ⟶ Y₁} {f : X₀ ⟶ X₁} (hf : f = eqToHom h₀ ≫ t ≫ eqToHom h₁.symm) :
    (BigFppfOver.toScheme B S hS).map f ≫
        (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj h₁)).hom =
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj h₀)).hom ≫
        (BigFppfOver.toScheme B S hS).map t := by
  subst h₀ h₁ hf
  simp

/-- Read in schemes, a morphism of the site out of a transport along an equality is the transport
of the morphism. -/
theorem toScheme_map_eqToHom_comp_comp_id {X Y Z : BigFppfOver B S hS} (h : X = Y)
    (r : Y ⟶ Z) :
    (BigFppfOver.toScheme B S hS).map (eqToHom h ≫ r) ≫ 𝟙 _ =
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj h)).hom ≫
        (BigFppfOver.toScheme B S hS).map r := by
  subst h
  simp

/-- The test scheme `Spec R` over `Y` of a formal object of `Complexes_{X/Y}`, `Y` being
terminal. -/
def formalObjectTestScheme : SchemesOver D.Y :=
  CostructuredArrow.mk (Y := baseOver B S hS ξ.base ξ.contains_spec_base) (hY.from _)

/-- The tower `Spec (R / 𝔪^{n+1}) ⟶ Spec R` of a formal object of `Complexes_{X/Y}`, with
`R = lim R / 𝔪^{n+1}` because `R` is complete. -/
def formalObjectSpecLimitTower :
    D.SpecLimitTower (levelOf ξ.level) (transitionOf ξ.transition) where
  R := powQuotientRingDiagram ξ.base.R (maximalIdeal ξ.base.R)
  cR := powQuotientRingCone ξ.base.R (maximalIdeal ξ.base.R)
  isLimit := letI := ξ.base.complete; powQuotientRingConeIsLimit _ _
  surjective n := Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.le_succ n)))
  locallyNilpotent n := locallyNilpotent_ker_factor_pow (I := maximalIdeal ξ.base.R)
    (a := n + 1) (b := n + 1 + 1) (Nat.succ_ne_zero n)
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  T := formalObjectTestScheme hY ξ
  toLimit n := CostructuredArrow.homMk
    (eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base ξ.contains_spec_base ξ.contains n)
    (hY.hom_ext _ _)
  transition_toLimit n := by
    refine CostructuredArrow.hom_ext _ _ ?_
    change (complexesFunctor D).map (ξ.transition n) ≫ eqToHom (ξ.level_eq (n + 1)) ≫
        restrictionToBase B S hS ξ.base ξ.contains_spec_base ξ.contains (n + 1) =
      eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base ξ.contains_spec_base ξ.contains n
    rw [FormalObject.map_transition]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      restrictionToBase_succ]
  e n := eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj (ξ.level_eq n))
  eLimit := Iso.refl _
  transition_e n := toScheme_map_comp_eqToHom (ξ.level_eq n) (ξ.level_eq (n + 1))
    (FormalObject.map_transition ξ n)
  toLimit_e n := toScheme_map_eqToHom_comp_comp_id (ξ.level_eq n) _

/-- **Stacks 0DLM, condition (3) of Stacks 07Y4: formal objects of `Complexes_{X/S}` are
effective**, from the results the source's proof uses.  For `Y = S` (`Y` terminal), every formal
object `ξ = (R, ξ_n)` of `Complexes_{X/S}` (Stacks 07X4) is effective (Stacks 07X7): the tower
`Spec (R / 𝔪^{n+1}) ⟶ Spec R` is one of `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower`
because `R` is complete, and
`AlgebraicGeometry.Space.ComplexesSituation.exists_realization_of_specLimitTower` realizes `ξ` by
an object over `Spec R`.  The hypotheses are those of that theorem: Stacks 0DIQ (`h0DIQ`, not yet
proved here) and Stacks 0DLC, clause (1) (`h0DLC`, pending with 0DLC). -/
theorem isEffective_formalObject_of
    (h0DIQ : ∀ {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B S hS (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B S hS (D.space L.T)),
        (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h0DLC : ExistsNegativeExtLocus B S hS)
    (hY : IsTerminal D.Y) (ξ : FormalObject B S hS (complexesFunctor D)) :
    FormalObject.IsEffective B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D)
      ξ := by
  obtain ⟨E, h₁, h₂, r, hr, hrc⟩ := D.exists_realization_of_specLimitTower h0DIQ h0DLC
    ξ.level ξ.transition (formalObjectSpecLimitTower hY ξ)
  refine FormalObject.isEffective_of_realization (hA := ξ.contains_spec_base)
    (complexesFunctor_isFiberedInGroupoids D)
    (x := (⟨formalObjectTestScheme hY ξ, E, h₁, h₂⟩ : ComplexesObject D)) (hx := rfl)
    ⟨r, hrc, fun n => ?_⟩
  show ((r n).base).left = _
  rw [hr n]
  rfl

end FormalObjects

/-! ### Strong formal effectiveness -/

section Strong

open Deformation.Artin

/-- The forgetful functor from commutative `Λ`-algebras to commutative rings preserves limits of
sequences: it is the equivalence with the rings under `Λ` followed by the forgetful functor of
that coslice, which creates limits. -/
theorem preservesLimitsOfShape_forget₂_commAlgCat (Λ : Type u) [CommRing Λ] :
    PreservesLimitsOfShape ℕᵒᵖ (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}) :=
  have : PreservesLimitsOfShape ℕᵒᵖ
      ((commAlgCatEquivUnder (.of Λ)).functor ⋙ Under.forget (CommRingCat.of Λ)) :=
    inferInstance
  preservesLimitsOfShape_of_natIso
    (F := (commAlgCatEquivUnder (.of Λ)).functor ⋙ Under.forget (CommRingCat.of Λ))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- Two cocones with the same vertex and the same legs, read through the equality of vertices,
are equal. -/
theorem coconeEq_of_pt_eq {J : Type*} [Category* J] {C : Type*} [Category* C] {F : J ⥤ C}
    {c₁ c₂ : Cocone F} (hpt : c₁.pt = c₂.pt) (hι : ∀ j, c₁.ι.app j ≫ eqToHom hpt = c₂.ι.app j) :
    c₁ = c₂ := by
  obtain ⟨pt₁, ι₁⟩ := c₁
  obtain ⟨pt₂, ι₂⟩ := c₂
  dsimp only at hpt
  subst hpt
  simp only [eqToHom_refl, Category.comp_id] at hι
  congr
  ext j
  exact hι j

variable {D}

/-- The morphisms `ξ_n ⟶ ξ_{n+1}` of a sequence of objects of `Complexes_{X/Y}`. -/
abbrev succMapOf (ξ : ℕ ⥤ ComplexesObject D) (n : ℕ) : ξ.obj n ⟶ ξ.obj (n + 1) :=
  ξ.map (homOfLE (Nat.le_succ n))

/-- A cocone of a sequence of objects of `Complexes_{X/Y}` from morphisms `ξ_n ⟶ x` compatible
with the morphisms `ξ_n ⟶ ξ_{n+1}`. -/
def coconeOfSuccCompatible (ξ : ℕ ⥤ ComplexesObject D) (x : ComplexesObject D)
    (r : ∀ n, ComplexesHom (ξ.obj n) x)
    (hr : ∀ n, ComplexesHom.comp (succMapOf ξ n) (r (n + 1)) = r n) : Cocone ξ where
  pt := x
  ι :=
    { app n := r n
      naturality i j f := by
        have key : ∀ k, ξ.map (homOfLE (Nat.le_add_right i k)) ≫ (r (i + k) : ξ.obj (i + k) ⟶ x) =
            r i := by
          intro k
          induction k with
          | zero =>
            exact (congrArg (· ≫ (r i : ξ.obj i ⟶ x)) (ξ.map_id i)).trans (Category.id_comp _)
          | succ k ih =>
            rw [← ih, show homOfLE (Nat.le_add_right i (k + 1)) =
                homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_succ (i + k)) from rfl,
              ξ.map_comp, Category.assoc]
            exact congrArg (ξ.map (homOfLE (Nat.le_add_right i k)) ≫ ·) (hr (i + k))
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
        exact (key k).trans (ComplexesHom.comp_id (r i)).symm }

/-- **Stacks 0DLM: `Complexes_{X/S}` is strongly formally effective** (Stacks 0CXT), from the
results the source's proof uses.  For `Y = S` (`Y` terminal) and `S` locally Noetherian, a
system `(ξ_n)` of objects of `Complexes_{X/S}` over a tower `Spec R_n` of `Λ`-algebras with
surjective transition maps whose kernels are locally nilpotent is effective over
`Spec (lim R_n)`.  This is
`AlgebraicGeometry.Space.ComplexesSituation.exists_realization_of_specLimitTower`, whose
hypotheses it carries: Stacks 0DIQ (`h0DIQ`, not yet proved here) and Stacks 0DLC,
clause (1) (`h0DLC`, pending with 0DLC). -/
theorem isStronglyFormallyEffective_complexes_of
    (h0DIQ : ∀ {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B S hS (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B S hS (D.space L.T)),
        (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h0DLC : ExistsNegativeExtLocus B S hS)
    [IsLocallyNoetherian S] (hY : IsTerminal D.Y) :
    IsStronglyFormallyEffective B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) := by
  intro Λ _ _ _ R cR hcR hsurj hnil ξ c e eLimit he heLimit _
  have := preservesLimitsOfShape_forget₂_commAlgCat Λ
  let L : D.SpecLimitTower (levelOf ξ.obj) (transitionOf (succMapOf ξ)) :=
    { R := R ⋙ forget₂ _ _
      cR := (forget₂ _ _).mapCone cR
      isLimit := isLimitOfPreserves _ hcR
      surjective := fun _ => hsurj _
      locallyNilpotent := fun _ => hnil _
      T := CostructuredArrow.mk (Y := c.pt) (hY.from _)
      toLimit := fun n => CostructuredArrow.homMk (c.ι.app n) (hY.hom_ext _ _)
      transition_toLimit := fun n => CostructuredArrow.hom_ext _ _ (c.w (homOfLE (Nat.le_succ n)))
      e := e
      eLimit := eLimit
      transition_e := fun n => he (homOfLE (Nat.le_succ n))
      toLimit_e := heLimit }
  obtain ⟨E, h₁, h₂, r, hr, hrc⟩ := D.exists_realization_of_specLimitTower h0DIQ h0DLC
    ξ.obj (succMapOf ξ) L
  refine ⟨coconeOfSuccCompatible ξ ⟨L.T, E, h₁, h₂⟩ r hrc, ?_⟩
  exact coconeEq_of_pt_eq rfl fun n =>
    (Category.comp_id _).trans (congrArg (fun g => g.left) (hr n))

end Strong

end AlgebraicGeometry.Space.ComplexesSituation

end
