module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSplittingDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.PicardPushforwardUnitIso
public import StacksFrontier.AlgebraicGeometry.Quot.StructureSheafMapIsoBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent

/-!
# The split section of `(π_*𝒪_Y)|_U` cut out by an open and closed piece isomorphic to `U`

Let `π : Y ⟶ X` be a morphism of algebraic spaces, `u : U ⟶ X` étale, `V = U ×_X Y` with
projections `p : V ⟶ U` and `q : V ⟶ Y`, and let `V` be the disjoint union of two open and closed
pieces `a : W ⟶ V`, `a' : W' ⟶ V` with `W ⟶ U` an **isomorphism**.  Then the restriction of
`π_*𝒪_Y` to `U` has a **split** global section `ε : 𝒪_U ⟶ (π_*𝒪_Y)|_U` — the indicator of the piece
`W` — with retraction `pr` the restriction to `W`.  Moreover, for every sheaf of ideals `ℐ ⊆ 𝒪_Y`
which becomes the unit ideal on `W`, the section `ε` factors through `(π_*ℐ)|_U`.

These are two facts about the clopen splitting of [Stacks, Tag 0ADU], as they enter
[Stacks, Tag 0GUZ]: the first says that the trace is surjective on the first summand of
`π_*(-)|_U`, the second applies to `ℐ^n`, as `ℐ^n|_W = 𝒪_W`.

## Main definitions

* `AlgebraicGeometry.Space.clopenSplitting`: `N ≅ a_*a^*N ⊞ a'_*a'^*N`.
* `AlgebraicGeometry.Space.clopenInclusion`: the inclusion `a_*a^*N ⟶ N` of the summand.
* `AlgebraicGeometry.Space.clopenSplitSection` and `AlgebraicGeometry.Space.clopenSplitRetraction`:
  the section `ε` and its retraction.

## Main results

* `AlgebraicGeometry.Space.clopenSplitSection_comp_clopenSplitRetraction`: `ε ≫ pr = 𝟙`.
* `AlgebraicGeometry.Space.clopenIndicator_comp_restriction`: the same identity with `ε` and `pr`
  written out (see the implementation notes).
* `AlgebraicGeometry.Space.clopenIndicatorIdeal_comp`: **`ε` factors through `(π_*ℐ)|_U`** for a
  sheaf of ideals `ℐ` which is the unit ideal on `W`, assembled from the two naturality squares
  `AlgebraicGeometry.Space.baseChangeDirectImageIso_inv_naturality_ι` and
  `AlgebraicGeometry.Space.clopenInclusion_map_ι`.
* `AlgebraicGeometry.Space.isIso_modulePullback_map_etaleModulePullback_map`: if `(ℐ ⟶ 𝒪_Y)|_W`
  is invertible, then so is `a^*((ℐ ⟶ 𝒪_Y)|_V)`.

## Implementation notes

The factorization is stated with `ε` written out rather than as `clopenSplitSection`.  The body of
a definition carries the auxiliary proofs that elaboration abstracts out of it (such as
`clopenSplitting._proof_1` for the algebraic-space proof `V.2`), whereas a statement elaborated
afresh carries the proofs themselves.  The two terms agree up to proof irrelevance, which the
elaborator sees at once; the kernel, however, unfolds the reducible abbreviations around them
first and exceeds its deterministic budget.  Identifying the definition with its
unfolding fails this way, even `simp only [clopenSplitSection]` on an equation whose sides differ
only in those proofs.  Statements in which every such term is elaborated afresh check at once.

## References

* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Splitting

variable {V W W' : AlgebraicSpaces B S hS} (a : W ⟶ V) (a' : W' ⟶ V)
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hca : IsClosedImmersion B S hS a.hom) (hca' : IsClosedImmersion B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))

/-- **The splitting `N ≅ a_*a^*N ⊞ a'_*a'^*N`** of a module along a decomposition into two open
and closed pieces: the pair of units, invertible by
`AlgebraicGeometry.Space.isIso_biprod_lift_unit_of_clopen`. -/
def clopenSplitting (N : Modules.{u, u} B S hS V.1 V.2) :
    N ≅ (modulePushforward B S hS a).obj ((modulePullback B S hS a).obj N) ⊞
      (modulePushforward B S hS a').obj ((modulePullback B S hS a').obj N) :=
  @asIso _ _ _ _ (biprod.lift ((modulePullbackAdjunction B S hS a).unit.app N)
    ((modulePullbackAdjunction B S hS a').unit.app N))
    (isIso_biprod_lift_unit_of_clopen B S hS a a' ha ha' hca hca' hcov hdisj N)

/-- The forward map of `AlgebraicGeometry.Space.clopenSplitting` is the pair of units. -/
theorem clopenSplitting_hom (N : Modules.{u, u} B S hS V.1 V.2) :
    (clopenSplitting B S hS a a' ha ha' hca hca' hcov hdisj N).hom =
      biprod.lift ((modulePullbackAdjunction B S hS a).unit.app N)
        ((modulePullbackAdjunction B S hS a').unit.app N) := rfl

/-- The inclusion `a_*a^*N ⟶ N` of the summand supported on `W`. -/
def clopenInclusion (N : Modules.{u, u} B S hS V.1 V.2) :
    (modulePushforward B S hS a).obj ((modulePullback B S hS a).obj N) ⟶ N :=
  biprod.inl ≫ (clopenSplitting B S hS a a' ha ha' hca hca' hcov hdisj N).inv

/-- The inclusion `a_*a^*N ⟶ N` followed by the unit `N ⟶ a_*a^*N` is the identity. -/
theorem clopenInclusion_unit (N : Modules.{u, u} B S hS V.1 V.2) :
    clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj N ≫
      (modulePullbackAdjunction B S hS a).unit.app N = 𝟙 _ := by
  have h : (modulePullbackAdjunction B S hS a).unit.app N =
      (clopenSplitting B S hS a a' ha ha' hca hca' hcov hdisj N).hom ≫ biprod.fst := by
    rw [clopenSplitting_hom]
    exact (biprod.lift_fst _ _).symm
  rw [h, clopenInclusion, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst]

/-- The splitting `N ≅ a_*a^*N ⊞ a'_*a'^*N` is natural in `N`. -/
theorem clopenSplitting_hom_naturality {N N' : Modules.{u, u} B S hS V.1 V.2} (f : N ⟶ N') :
    f ≫ (clopenSplitting B S hS a a' ha ha' hca hca' hcov hdisj N').hom =
      (clopenSplitting B S hS a a' ha ha' hca hca' hcov hdisj N).hom ≫
        biprod.map ((modulePushforward B S hS a).map ((modulePullback B S hS a).map f))
          ((modulePushforward B S hS a').map ((modulePullback B S hS a').map f)) := by
  rw [clopenSplitting_hom, clopenSplitting_hom, biprod.lift_map, biprod.comp_lift]
  congr 1
  · exact (modulePullbackAdjunction B S hS a).unit.naturality f
  · exact (modulePullbackAdjunction B S hS a').unit.naturality f

/-- **The inclusion of the summand is natural.** -/
theorem clopenInclusion_naturality {N N' : Modules.{u, u} B S hS V.1 V.2} (f : N ⟶ N') :
    (modulePushforward B S hS a).map ((modulePullback B S hS a).map f) ≫
        clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj N' =
      clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj N ≫ f := by
  have h := clopenSplitting_hom_naturality B S hS a a' ha ha' hca hca' hcov hdisj f
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
  rw [clopenInclusion, clopenInclusion, Category.assoc, h, ← Category.assoc, ← Category.assoc,
    biprod.inl_map]

/-- After `p_*`, the inclusion of the summand on `W` followed by the unit is the identity. -/
private theorem clopenInclusion_map_comp_map_unit {U : AlgebraicSpaces B S hS}
    (pV : V ⟶ U) (N : Modules.{u, u} B S hS V.1 V.2) :
    (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj N) ≫
      (modulePushforward B S hS pV).map ((modulePullbackAdjunction B S hS a).unit.app N) =
      𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, clopenInclusion_unit, CategoryTheory.Functor.map_id]

end Splitting

section Neighbourhood

variable {X Y U V W W' : AlgebraicSpaces B S hS} (π : Y ⟶ X) (u : U ⟶ X)
    (hu : IsEtale B S hS u.hom) (iV : V ⟶ Y) (pV : V ⟶ U) (sqV : IsPullback iV pV π u)
    (a : W ⟶ V) (a' : W' ⟶ V)
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hca : IsClosedImmersion B S hS a.hom) (hca' : IsClosedImmersion B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))
    [IsIso (a ≫ pV)]

/-- The restriction of `𝒪_Y` to `V`. -/
abbrev clopenBaseUnit : Modules.{u, u} B S hS V.1 V.2 :=
  (etaleModulePullback B S hS iV (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).obj
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))

/-- The base change of Stacks 03LX, read from `(π_*𝒢)|_U` to `p_*(𝒢|_V)`. -/
abbrev baseChangeDirectImageIso (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModulePullback B S hS u hu).obj ((modulePushforward B S hS π).obj G) ≅
      (modulePushforward B S hS pV).obj ((etaleModulePullback B S hS iV
        (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).obj G) :=
  ((modulePushforwardEtaleBaseChangeIso B S hS iV pV π u sqV hu).app G).symm

/-- `𝒪_U ≅ p_*(a_*(a^*(𝒪_Y|_V)))`: the piece `W` maps isomorphically onto `U`. -/
def clopenUnitIso :
    SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O) ≅
      (modulePushforward B S hS pV).obj ((modulePushforward B S hS a).obj
        ((modulePullback B S hS a).obj (clopenBaseUnit B S hS π u hu iV pV sqV))) :=
  @asIso _ _ _ _ (pushforwardStructureProjection B S hS (a ≫ pV))
      (isIso_pushforwardStructureProjection (a ≫ pV) (isIso_structureSharp_of_isIso (a ≫ pV))) ≪≫
    (modulePushforward B S hS (a ≫ pV)).mapIso (modulePullbackUnitIso B S hS a).symm ≪≫
    ((modulePushforwardCompIso B S hS a pV).app _).symm

/-- **The indicator `ε : 𝒪_U ⟶ (π_*𝒪_Y)|_U` of the piece `W`.** -/
def clopenSplitSection :
    SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O) ⟶
      (etaleModulePullback B S hS u hu).obj ((modulePushforward B S hS π).obj
        (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) :=
  (clopenUnitIso B S hS π u hu iV pV sqV a).hom ≫
    (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj
      (clopenBaseUnit B S hS π u hu iV pV sqV)) ≫
    (baseChangeDirectImageIso B S hS π u hu iV pV sqV
      (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).inv

/-- **The restriction `(π_*𝒪_Y)|_U ⟶ 𝒪_U` to the piece `W`.** -/
def clopenSplitRetraction :
    (etaleModulePullback B S hS u hu).obj ((modulePushforward B S hS π).obj
        (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ⟶
      SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O) :=
  (baseChangeDirectImageIso B S hS π u hu iV pV sqV
      (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
    (modulePushforward B S hS pV).map ((modulePullbackAdjunction B S hS a).unit.app
      (clopenBaseUnit B S hS π u hu iV pV sqV)) ≫
    (clopenUnitIso B S hS π u hu iV pV sqV a).inv

/-- **`ε ≫ pr = 𝟙`**: the indicator of `W` is a split section. -/
theorem clopenSplitSection_comp_clopenSplitRetraction :
    clopenSplitSection B S hS π u hu iV pV sqV a a' ha ha' hca hca' hcov hdisj ≫
      clopenSplitRetraction B S hS π u hu iV pV sqV a = 𝟙 _ := by
  have h2 := clopenInclusion_map_comp_map_unit B S hS a a' ha ha' hca hca' hcov hdisj pV
    (clopenBaseUnit B S hS π u hu iV pV sqV)
  simp only [clopenSplitSection, clopenSplitRetraction, Category.assoc, Iso.inv_hom_id_assoc,
    reassoc_of% h2, Iso.hom_inv_id]

/-- **`ε ≫ pr = 𝟙`, with `ε` and `pr` written out.**  This is
`AlgebraicGeometry.Space.clopenSplitSection_comp_clopenSplitRetraction` with both definitions
unfolded in the statement. -/
theorem clopenIndicator_comp_restriction :
    ((clopenUnitIso B S hS π u hu iV pV sqV a).hom ≫
      (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj
        (clopenBaseUnit B S hS π u hu iV pV sqV)) ≫
      (baseChangeDirectImageIso B S hS π u hu iV pV sqV (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).inv) ≫
      (baseChangeDirectImageIso B S hS π u hu iV pV sqV (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).hom ≫
      (modulePushforward B S hS pV).map ((modulePullbackAdjunction B S hS a).unit.app
        (clopenBaseUnit B S hS π u hu iV pV sqV)) ≫
      (clopenUnitIso B S hS π u hu iV pV sqV a).inv = 𝟙 _ := by
  have h2 := clopenInclusion_map_comp_map_unit B S hS a a' ha ha' hca hca' hcov hdisj pV
    (clopenBaseUnit B S hS π u hu iV pV sqV)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h2, Iso.hom_inv_id]

variable (K : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule)

/-- The base change isomorphism `p_*(𝒢|_V) ≅ (π_*𝒢)|_U` commutes with the inclusion `ℐ ⟶ 𝒪_Y`. -/
theorem baseChangeDirectImageIso_inv_naturality_ι :
    (baseChangeDirectImageIso B S hS π u hu iV pV sqV K.toSheafOfModules).inv ≫
      (etaleModulePullback B S hS u hu).map ((modulePushforward B S hS π).map K.ι) =
      (modulePushforward B S hS pV).map ((etaleModulePullback B S hS iV
        (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map K.ι) ≫
      (baseChangeDirectImageIso B S hS π u hu iV pV sqV (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).inv := by
  have hnat := (modulePushforwardEtaleBaseChangeIso B S hS iV pV π u sqV hu).hom.naturality K.ι
  simp only [Functor.comp_map] at hnat
  simp only [baseChangeDirectImageIso, Iso.symm_inv, Iso.app_hom]
  exact hnat.symm

omit [IsIso (a ≫ pV)] in
/-- After `p_*`, the inclusion of the summand on `W` commutes with the inclusion
`ℐ|_V ⟶ 𝒪_Y|_V`. -/
theorem clopenInclusion_map_ι :
    (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj
      ((etaleModulePullback B S hS iV
        (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).obj K.toSheafOfModules)) ≫
      (modulePushforward B S hS pV).map ((etaleModulePullback B S hS iV
        (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map K.ι) =
      (modulePushforward B S hS pV).map ((modulePushforward B S hS a).map
        ((modulePullback B S hS a).map ((etaleModulePullback B S hS iV
          (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map K.ι))) ≫
      (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov
        hdisj (clopenBaseUnit B S hS π u hu iV pV sqV)) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    clopenInclusion_naturality]

variable [IsIso ((modulePullback B S hS a).map ((etaleModulePullback B S hS iV
    (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map K.ι))]

/-- The comparison `p_*(a_*(a^*(ℐ|_V))) ⟶ p_*(a_*(a^*(𝒪_Y|_V)))`, invertible when `ℐ` restricts
to the unit ideal on `W`. -/
abbrev clopenIdealComparison :
    (modulePushforward B S hS pV).obj ((modulePushforward B S hS a).obj
        ((modulePullback B S hS a).obj ((etaleModulePullback B S hS iV
          (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).obj K.toSheafOfModules))) ⟶
      (modulePushforward B S hS pV).obj ((modulePushforward B S hS a).obj
        ((modulePullback B S hS a).obj (clopenBaseUnit B S hS π u hu iV pV sqV))) :=
  (modulePushforward B S hS pV).map ((modulePushforward B S hS a).map
    ((modulePullback B S hS a).map ((etaleModulePullback B S hS iV
      (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map K.ι)))

/-- The comparison `p_*(a_*(a^*(ℐ|_V))) ⟶ p_*(a_*(a^*(𝒪_Y|_V)))` is an isomorphism when
`a^*((ℐ ⟶ 𝒪_Y)|_V)` is. -/
instance isIso_clopenIdealComparison :
    IsIso (clopenIdealComparison B S hS π u hu iV pV sqV a K) := by
  dsimp only [clopenIdealComparison]
  infer_instance

omit [IsIso (a ≫ pV)]
  [IsIso ((modulePullback B S hS a).map ((etaleModulePullback B S hS iV
    (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map K.ι))] in
/-- The tail of the factorization of the indicator of `W` through `(π_*ℐ)|_U`. -/
theorem clopenIndicatorIdeal_tail :
    (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj
      ((etaleModulePullback B S hS iV
        (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).obj K.toSheafOfModules)) ≫
    (baseChangeDirectImageIso B S hS π u hu iV pV sqV K.toSheafOfModules).inv ≫
      (etaleModulePullback B S hS u hu).map ((modulePushforward B S hS π).map K.ι) =
    clopenIdealComparison B S hS π u hu iV pV sqV a K ≫
      (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov
        hdisj (clopenBaseUnit B S hS π u hu iV pV sqV)) ≫
      (baseChangeDirectImageIso B S hS π u hu iV pV sqV (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).inv := by
  rw [baseChangeDirectImageIso_inv_naturality_ι, ← Category.assoc,
    clopenInclusion_map_ι B S hS π u hu iV pV sqV a a' ha ha' hca hca' hcov hdisj K,
    Category.assoc]

/-- **The indicator of `W` factors through `(π_*ℐ)|_U`**, for a sheaf of ideals `ℐ` which
restricts to the unit ideal on `W`: the explicit section
`𝒪_U ≅ p_*a_*a^*(𝒪_Y|_V) ≅ p_*a_*a^*(ℐ|_V) ⟶ p_*(ℐ|_V) ≅ (π_*ℐ)|_U`, followed by the inclusion
`(π_*ℐ)|_U ⟶ (π_*𝒪_Y)|_U`, is the indicator `ε` of
`AlgebraicGeometry.Space.clopenIndicator_comp_restriction`. -/
theorem clopenIndicatorIdeal_comp :
    (clopenUnitIso B S hS π u hu iV pV sqV a).hom ≫
    inv (clopenIdealComparison B S hS π u hu iV pV sqV a K) ≫
    (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj
      ((etaleModulePullback B S hS iV
        (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).obj K.toSheafOfModules)) ≫
    (baseChangeDirectImageIso B S hS π u hu iV pV sqV K.toSheafOfModules).inv ≫
      (etaleModulePullback B S hS u hu).map ((modulePushforward B S hS π).map K.ι) =
    (clopenUnitIso B S hS π u hu iV pV sqV a).hom ≫
      (modulePushforward B S hS pV).map (clopenInclusion B S hS a a' ha ha' hca hca' hcov hdisj
        (clopenBaseUnit B S hS π u hu iV pV sqV)) ≫
      (baseChangeDirectImageIso B S hS π u hu iV pV sqV (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).inv := by
  rw [clopenIndicatorIdeal_tail, IsIso.inv_hom_id_assoc]

end Neighbourhood

/-- **Invertibility of `a^*((ℐ ⟶ 𝒪)|_V)` from invertibility of `(ℐ ⟶ 𝒪)|_W`**: the inverse image
along `a : W ⟶ V` of an étale restriction along `i : V ⟶ Y` is the étale restriction along the
composite, by the comparisons of Stacks 03LW and of Stacks 03LU for a composition. -/
theorem isIso_modulePullback_map_etaleModulePullback_map {W V Y : AlgebraicSpaces B S hS}
    (a : W ⟶ V) (i : V ⟶ Y) (hi : IsEtale B S hS i.hom) (hai : IsEtale B S hS (a ≫ i).hom)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (φ : M ⟶ N)
    (h : IsIso ((etaleModulePullback B S hS (a ≫ i) hai).map φ)) :
    IsIso ((modulePullback B S hS a).map ((etaleModulePullback B S hS i hi).map φ)) := by
  have e1 : IsIso ((modulePullback B S hS (a ≫ i)).map φ) :=
    (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS (a ≫ i) hai) φ).2 h
  have e2 : IsIso ((modulePullback B S hS i ⋙ modulePullback B S hS a).map φ) :=
    (NatIso.isIso_map_iff (modulePullbackCompIso B S hS a i) φ).2 e1
  exact (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS i hi)
      (modulePullback B S hS a)) φ).1 e2

end AlgebraicGeometry.Space
