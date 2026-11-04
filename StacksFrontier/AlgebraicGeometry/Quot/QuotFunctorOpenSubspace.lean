module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionDirectImageSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleConditions
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset

/-!
# The Quot functor of an open subspace (Stacks 0DP3)

Let `B` be an algebraic space, let `j : X ⟶ Y` be an open immersion of algebraic spaces which are
separated and of finite presentation over `B`, let `G` be a quasi-coherent `𝒪_Y`-module and set
`F = j^*G`.  Stacks 0DP3 asserts that there is an open immersion
`Quot_{F/X/B} ⟶ Quot_{G/Y/B}` of algebraic spaces over `B`.

Over a test scheme `T` of `B` write `j_T : X_T ⟶ Y_T` for the base change, again an open
immersion, and identify `F_T` with `j_T^*G_T`.  A member `F_T ⟶ Q` of `Quot_{F/X/B}(T)` has
support proper over `T`, so, `Y_T` being separated over `T`, the image of its support in `Y_T` is
closed.  The composite `G_T ⟶ j_{T,*}j_T^*G_T ≅ j_{T,*}F_T ⟶ j_{T,*}Q` is then surjective, and
`j_{T,*}Q` is of finite presentation, flat over `T` and has support proper over `T`.  Conversely, a
member `G_T ⟶ Q` of `Quot_{G/Y/B}(T)` whose support lies in `X_T` is the direct image of its
restriction `F_T ⟶ j_T^*Q`, the unit `Q ⟶ j_{T,*}j_T^*Q` being an isomorphism.  So the direct image
is injective, its image consists of the quotients supported in `X_T`, and since the support of a
base change of `Q` is the inverse image of the support of `Q`, the locus of a test scheme over
which a quotient is supported in the open subspace is the complement of the image of the part of
the support outside `X_T` — closed, that part being proper over `T`.

## Main definitions

* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation`: the standing data of Stacks 0DP3, and
  `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.ofOpenImmersion`, which assembles it from the
  source's hypotheses.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.restrictQuotient` and
  `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.extendQuotient`: the restriction of a quotient
  of `G_T` to `X_T` and the direct image of a quotient of `F_T`, recorded by their kernels.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.quotFunctorMap`: the morphism
  `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` sending a quotient `F_T ⟶ Q` to `G_T ⟶ j_{T,*}Q`.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.supportLocus`: the locus of a test scheme
  over which a quotient is supported in the open subspace.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.quotModelMap`: the morphism read in models of
  the two Quot presheaves of the site.

## Main results

* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.extendQuotient_mem` and
  `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.restrictQuotient_mem`: the direct image and
  the restriction preserve the four conditions of Stacks 09TR, the second for quotients supported
  in the open subspace.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.restrictQuotient_extendQuotient` and
  `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.extendQuotient_restrictQuotient`: the two are
  mutually inverse.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.extendQuotient_quotientPullback`: the direct
  image commutes with pullback along a morphism of test schemes.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.supportedInOpen_baseChange_iff` and
  `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.isOpen_supportLocus`: the support condition
  after base change is membership in that locus, and the locus is open.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.isOpenImmersion_quotModelMap`: the morphism
  read in any models is an open immersion over `B`.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.isOpenImmersion_quotSitePresheafModelMap`:
  the same for the canonical models.
* `QuotOpenSubspaceSituation.isOpenImmersion_quotSitePresheafModelMap_ofOpenImmersion`:
  **Stacks 0DP3**, for the canonical models, with the hypotheses written out.

## Implementation notes

Being an open immersion is a property of a morphism of presheaves of `Type u` on the schemes of
the site, while the Quot functor of Stacks 09TR takes values in `Type (u + 1)`, quotients being
recorded by subobjects.  As for the representability statement Stacks 09TU and for the Hilbert
functor of an open subspace, Stacks 0DPE, the assertion is therefore made about the morphism
induced on models (`AlgebraicGeometry.Space.QuotSitePresheafModel`) of the two Quot presheaves of
the site.  The registered statement is for the canonical models
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafModel`, which exist with no hypothesis, the
quotients over a scheme of the site forming a small set; the same holds for every choice of
models.

Naturality of the direct image is not computed: both sides of it are quotients supported in the
open subspace, which are determined by their restrictions, and restriction commutes with pullback
by the associativity coherence of the inverse images of Stacks 03LU.

## References

* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The `𝒪_{X_T}`-modules here have their sections in the universe of the schemes, which the
-- ambient-universe abelian structure on modules over a site cannot describe; left in place it
-- is selected ahead of `SheafOfModules.instAbelian` and leaves the module universe of every
-- subobject and cokernel below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- The quotients of Stacks 082M are cokernels in the abelian structure; the separately
-- constructed cokernels of `𝒪`-modules are equal to them only through an expensive unfolding.
attribute [-instance] AlgebraicGeometry.Space.hasCokernel_modules

/-- Conjugating by a comparison whiskered on the left is conjugating at the image object. -/
theorem CategoryTheory.Functor.conjSubobject_isoWhiskerLeft {C' C D₁ D₂ : Type*} [Category* C']
    [Category* C] [Category* D₁] [Category* D₂] [Abelian D₁] [Abelian D₂] (F : C' ⥤ C)
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M : C'}
    (K : Subobject (P₁.obj (F.obj M))) :
    Functor.conjSubobject (P₁ := F ⋙ P₁) (Functor.isoWhiskerLeft F e) K =
      Functor.conjSubobject e K :=
  rfl

/-- Composing a comparison with a functor composite with the associator and the identity
whiskering returns it. -/
theorem CategoryTheory.Iso.trans_eq_trans_associator_trans_isoWhiskerLeft_refl_symm
    {C D₀ D₁ D₂ : Type*} [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]
    {P : C ⥤ D₀} {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {X Y : C ⥤ D₂} (α : X ≅ Y)
    (β : Y ≅ (P ⋙ L₁) ⋙ L₂) :
    α ≪≫ β = (α ≪≫ β ≪≫ Functor.associator P L₁ L₂) ≪≫
      (Functor.isoWhiskerLeft P (Iso.refl (L₁ ⋙ L₂))).symm := by
  ext
  simp

/-- Composing a comparison followed by a whiskered isomorphism is composing it with the
associator and the inverse of the inverse whiskering. -/
theorem CategoryTheory.Iso.trans_isoWhiskerLeft_eq_trans_associator_trans_isoWhiskerLeft_symm_symm
    {C D₀ D₁ D₂ : Type*} [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]
    {P : C ⥤ D₀} {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂} {X Y : C ⥤ D₂} (α : X ≅ Y)
    (β : Y ≅ (P ⋙ L₁) ⋙ L₂) (σ : L₁ ⋙ L₂ ≅ L) :
    (α ≪≫ β) ≪≫ Functor.isoWhiskerLeft P σ =
      (α ≪≫ β ≪≫ Functor.associator P L₁ L₂) ≪≫
        (Functor.isoWhiskerLeft P σ.symm).symm := by
  ext
  simp

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The standing data of Stacks 0DP3.**  An open immersion `j : X ⟶ Y` of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`, together with a
quasi-coherent `𝒪_Y`-module `G`. -/
structure QuotOpenSubspaceSituation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- The base algebraic space. -/
  base : AlgebraicSpaces B S hS
  /-- The open subspace. -/
  X : AlgebraicSpaces B S hS
  /-- The ambient space. -/
  Y : AlgebraicSpaces B S hS
  /-- The open immersion. -/
  j : X ⟶ Y
  /-- The structure morphism of the open subspace. -/
  structureX : X ⟶ base
  /-- The structure morphism of the ambient space. -/
  structureY : Y ⟶ base
  /-- The open immersion is a morphism over the base. -/
  comp : j ≫ structureY = structureX
  /-- The module on the ambient space. -/
  G : Modules.{u, u} B S hS Y.1 Y.2
  /-- It is quasi-coherent. -/
  quasicoherent : G.IsQuasicoherentOnSite
  /-- The morphism is an open immersion. -/
  openImmersion : IsOpenImmersion B S hS j.hom
  /-- The open subspace is separated over the base. -/
  separatedX : IsSeparated B S hS structureX.hom
  /-- The ambient space is separated over the base. -/
  separatedY : IsSeparated B S hS structureY.hom
  /-- The open subspace is of finite presentation over the base. -/
  finitePresentationX : IsFinitePresentation B S hS structureX.hom
  /-- The ambient space is of finite presentation over the base. -/
  finitePresentationY : IsFinitePresentation B S hS structureY.hom

namespace QuotOpenSubspaceSituation

variable (D : QuotOpenSubspaceSituation B S hS)

/-! ### The two quotient situations -/

/-- The module `F = j^*G` on the open subspace. -/
abbrev F : Modules.{u, u} B S hS D.X.1 D.X.2 := (modulePullback B S hS D.j).obj D.G

/-- The quotient situation `F/X/B` of Stacks 09TR. -/
abbrev sourceSituation : QuotSituation B S hS where
  X := D.X
  Y := D.base
  f := D.structureX
  F := D.F
  quasicoherent :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.j D.G D.quasicoherent
  finitePresentation := D.finitePresentationX

/-- The quotient situation `G/Y/B` of Stacks 09TR. -/
abbrev targetSituation : QuotSituation B S hS where
  X := D.Y
  Y := D.base
  f := D.structureY
  F := D.G
  quasicoherent := D.quasicoherent
  finitePresentation := D.finitePresentationY

/-! ### The base change of the open immersion -/

/-- The base change `j_T : X_T ⟶ Y_T` of the open immersion to a test scheme over the base. -/
def baseChangeOfMap (T : SchemesOver D.base) :
    D.sourceSituation.space T ⟶ D.targetSituation.space T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift
    (baseChangeProjection D.structureX T ≫ D.j) (baseChangeInclusion D.structureX T) (by
      rw [Category.assoc, D.comp]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureX T.hom).w)

/-- The base change `j_T` followed by the projection `Y_T ⟶ Y` is the projection `X_T ⟶ X`
followed by `j`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_projection (T : SchemesOver D.base) :
    D.baseChangeOfMap T ≫ D.targetSituation.sourceProjection T =
      D.sourceSituation.sourceProjection T ≫ D.j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift_fst _ _ _

/-- The base change `j_T` followed by the projection `Y_T ⟶ T` is the projection `X_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_inclusion (T : SchemesOver D.base) :
    D.baseChangeOfMap T ≫ D.targetSituation.projection T = D.sourceSituation.projection T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift_snd _ _ _

/-- The square of the base change of the open immersion is cartesian. -/
theorem isPullback_baseChangeOfMap (T : SchemesOver D.base) :
    IsPullback (D.baseChangeOfMap T) (D.sourceSituation.sourceProjection T)
      (D.targetSituation.sourceProjection T) D.j := by
  have outer : IsPullback (D.baseChangeOfMap T ≫ D.targetSituation.projection T)
      (D.sourceSituation.sourceProjection T) T.hom (D.j ≫ D.structureY) := by
    rw [D.baseChangeOfMap_comp_inclusion T, D.comp]
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureX T.hom).flip
  exact outer.of_right (D.baseChangeOfMap_comp_projection T)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).flip

/-- The base change of the open immersion is an open immersion (Stacks 02YW). -/
theorem isOpenImmersion_baseChangeOfMap {T : SchemesOver D.base} :
    IsOpenImmersion B S hS (D.baseChangeOfMap T).hom :=
  isOpenImmersion_of_isPullback B S hS (D.isPullback_baseChangeOfMap T).flip D.openImmersion

/-- The base changes of the open immersion are compatible with a morphism of test schemes. -/
@[reassoc]
theorem relativeMap_comp_baseChangeOfMap {T' T : SchemesOver D.base} (h : T' ⟶ T) :
    D.sourceSituation.relativeMap h ≫ D.baseChangeOfMap T =
      D.baseChangeOfMap T' ≫ D.targetSituation.relativeMap h := by
  refine baseChange_hom_ext D.structureY ?_ ?_
  · show _ ≫ D.baseChangeOfMap T ≫ D.targetSituation.sourceProjection T =
      _ ≫ D.targetSituation.relativeMap h ≫ D.targetSituation.sourceProjection T
    rw [D.baseChangeOfMap_comp_projection, baseChangeMap_comp_projection,
      baseChangeMap_comp_projection_assoc, D.baseChangeOfMap_comp_projection]
  · show _ ≫ D.baseChangeOfMap T ≫ D.targetSituation.projection T =
      _ ≫ D.targetSituation.relativeMap h ≫ D.targetSituation.projection T
    rw [D.baseChangeOfMap_comp_inclusion, baseChangeMap_comp_inclusion,
      baseChangeMap_comp_inclusion, D.baseChangeOfMap_comp_inclusion_assoc]

/-- The square formed by the base changes of the open immersion along a morphism of test schemes
is cartesian. -/
theorem isPullback_relativeMap {T' T : SchemesOver D.base} (h : T' ⟶ T) :
    IsPullback (D.sourceSituation.relativeMap h) (D.baseChangeOfMap T')
      (D.baseChangeOfMap T) (D.targetSituation.relativeMap h) := by
  have outer : IsPullback (D.sourceSituation.relativeMap h ≫ D.sourceSituation.sourceProjection T)
      (D.baseChangeOfMap T') D.j
      (D.targetSituation.relativeMap h ≫ D.targetSituation.sourceProjection T) := by
    rw [baseChangeMap_comp_projection, baseChangeMap_comp_projection]
    exact (D.isPullback_baseChangeOfMap T').flip
  exact IsPullback.of_right outer (D.relativeMap_comp_baseChangeOfMap h)
    (D.isPullback_baseChangeOfMap T).flip

/-! ### Restriction and extension of quotients -/

/-- The comparison of `F_T = (X_T ⟶ X)^*j^*G` with `j_T^*G_T`, from the two factorisations of
`X_T ⟶ Y`. -/
def restrictionComparison (T : SchemesOver D.base) :
    modulePullback B S hS D.j ⋙ modulePullback B S hS (D.sourceSituation.sourceProjection T) ≅
      modulePullback B S hS (D.targetSituation.sourceProjection T) ⋙
        modulePullback B S hS (D.baseChangeOfMap T) :=
  modulePullbackSquare B S hS rfl (D.baseChangeOfMap_comp_projection T)

/-- **The restriction of a quotient of `G_T` to `X_T`**, a quotient of `F_T = j_T^*G_T`, recorded
by its kernel. -/
def restrictQuotient (T : SchemesOver D.base)
    (K : Subobject (D.targetSituation.baseChangeModule T)) :
    Subobject (D.sourceSituation.baseChangeModule T) :=
  Functor.conjSubobject (D.restrictionComparison T) K

/-- The quotient of `F_T` by the restriction of a quotient is the restriction of the quotient. -/
def restrictQuotientCokernelIso (T : SchemesOver D.base)
    (K : Subobject (D.targetSituation.baseChangeModule T)) :
    D.sourceSituation.quotientModule T (D.restrictQuotient T K) ≅
      (modulePullback B S hS (D.baseChangeOfMap T)).obj (D.targetSituation.quotientModule T K) :=
  Functor.conjSubobjectCokernelIso (D.restrictionComparison T) K

/-- The projection onto the quotient by the restriction of a quotient is the restriction of the
projection, read through `restrictQuotientCokernelIso`. -/
theorem quotientProjection_comp_restrictQuotientCokernelIso_hom (T : SchemesOver D.base)
    (K : Subobject (D.targetSituation.baseChangeModule T)) :
    D.sourceSituation.quotientProjection T (D.restrictQuotient T K) ≫
        (D.restrictQuotientCokernelIso T K).hom =
      Functor.conjQuotientProjection (D.restrictionComparison T) K :=
  Functor.cokernel_π_comp_conjSubobjectCokernelIso_hom (D.restrictionComparison T) K

/-- **Stacks 0DP3, the direct image of a quotient**: the kernel of the morphism
`G_T ⟶ j_{T,*}(F_T/K)` adjoint to `j_T^*G_T ≅ F_T ⟶ F_T/K`. -/
def extendQuotient (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Subobject (D.targetSituation.baseChangeModule T) :=
  extendSubobject B S hS (D.baseChangeOfMap T) (D.restrictionComparison T)
    (D.sourceSituation.quotientProjection T K)

/-- The support of a quotient of `F_T` lying in `Quot_{F/X/B}(T)` has closed image in `Y_T`, by
Stacks 0CZG: it is proper over `T` and `Y_T` is separated over `T`. -/
theorem isClosed_image_support_of_mem (T : SchemesOver D.base)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    IsClosed (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom ''
      D.sourceSituation.support T (D.sourceSituation.quotientModule T K)) := by
  obtain ⟨hcl, hproper⟩ := hK.2
  exact isClosed_image_of_isProperOver B S hS (D.sourceSituation.space T).2
    (D.targetSituation.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
    (D.baseChangeOfMap T).hom (D.sourceSituation.projection T).hom
    (D.targetSituation.projection T).hom
    (congrArg (fun k => k.hom) (D.baseChangeOfMap_comp_inclusion T))
    (D.sourceSituation.isLocallyOfFiniteType_projection T)
    (D.targetSituation.isLocallyOfFiniteType_projection T)
    (isSeparated_pullbackSnd B S hS _ D.separatedY) _ hcl hproper

/-- **The restriction of the direct image of a quotient is that quotient**, when the support of
the quotient has closed image in `Y_T`. -/
theorem restrictQuotient_extendQuotient (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hcl : IsClosed (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom ''
      D.sourceSituation.support T (D.sourceSituation.quotientModule T K))) :
    D.restrictQuotient T (D.extendQuotient T K) = K :=
  (conjSubobject_extendSubobject B S hS (D.baseChangeOfMap T)
    (D.isOpenImmersion_baseChangeOfMap (T := T)) (D.restrictionComparison T)
    (D.sourceSituation.quotientProjection T K) hcl).trans (kernelSubobject_cokernel_π K)

/-- **The direct image of the restriction of a quotient is that quotient**, when the support of
the quotient is closed and lies in `X_T`. -/
theorem extendQuotient_restrictQuotient (T : SchemesOver D.base)
    (L : Subobject (D.targetSituation.baseChangeModule T))
    (hcl : IsClosed (D.targetSituation.support T (D.targetSituation.quotientModule T L)))
    (hsub : D.targetSituation.support T (D.targetSituation.quotientModule T L) ⊆
      Set.range (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom)) :
    D.extendQuotient T (D.restrictQuotient T L) = L := by
  have hη := isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset B S hS
    (D.baseChangeOfMap T) (D.isOpenImmersion_baseChangeOfMap (T := T)) _ hcl hsub
  exact extendSubobject_eq_of_isIso_unit B S hS (D.baseChangeOfMap T)
    (D.restrictionComparison T) L (D.sourceSituation.quotientProjection T (D.restrictQuotient T L))
    (D.restrictQuotientCokernelIso T L)
    (D.quotientProjection_comp_restrictQuotientCokernelIso_hom T L) hη

/-! ### The conditions of Stacks 09TR across the open immersion -/

/-- The base change `j_T` followed by the projection `Y_T ⟶ T` is the projection `X_T ⟶ T`,
as an equality of underlying morphisms. -/
theorem baseChangeOfMap_comp_inclusion_hom (T : SchemesOver D.base) :
    (D.baseChangeOfMap T ≫ D.targetSituation.projection T).hom =
      (D.sourceSituation.projection T).hom :=
  congrArg (fun k => k.hom) (D.baseChangeOfMap_comp_inclusion T)

/-- The epimorphism `G_T ⟶ j_{T,*}(F_T/K)`, for a member of `Quot_{F/X/B}(T)`. -/
theorem epi_extensionProjection (T : SchemesOver D.base)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    Epi ((modulePullbackAdjunction B S hS (D.baseChangeOfMap T)).homEquiv
      (D.targetSituation.baseChangeModule T) (D.sourceSituation.quotientModule T K)
      ((D.restrictionComparison T).inv.app D.G ≫ D.sourceSituation.quotientProjection T K)) :=
  epi_homEquiv_of_isOpenImmersion B S hS (D.baseChangeOfMap T)
    (D.isOpenImmersion_baseChangeOfMap (T := T)) _ _ _
    (epi_comp' (IsIso.epi_of_iso _) (D.sourceSituation.epi_quotientProjection T K))
    (by
      rw [supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion B S hS _
        (D.isOpenImmersion_baseChangeOfMap (T := T)) _ (D.isClosed_image_support_of_mem T hK)]
      exact Set.image_subset_range _ _)

/-- The quotient of `G_T` by the direct image of a member `F_T ⟶ Q` of `Quot_{F/X/B}(T)` is
`j_{T,*}Q`. -/
def extendQuotientCokernelIso (T : SchemesOver D.base)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.targetSituation.quotientModule T (D.extendQuotient T K) ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.quotientModule T K) :=
  extendSubobjectCokernelIso B S hS (D.baseChangeOfMap T)
    (D.isOpenImmersion_baseChangeOfMap (T := T))
    (D.restrictionComparison T) (D.sourceSituation.quotientProjection T K)
    (D.isClosed_image_support_of_mem T hK)

/-- **Stacks 0DP3, the morphism of Stacks 0DN9 for the open immersion.**  The direct image
`j_{T,*}Q` of a member `F_T ⟶ Q` of `Quot_{F/X/B}(T)` is quasi-coherent, of finite presentation,
flat over `T` and has support proper over `T`. -/
theorem isQuotModule_modulePushforward (T : SchemesOver D.base)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.targetSituation.IsQuotModule T ((modulePushforward B S hS (D.baseChangeOfMap T)).obj
      (D.sourceSituation.quotientModule T K)) := by
  have hj := D.isOpenImmersion_baseChangeOfMap (T := T)
  have hcl := D.isClosed_image_support_of_mem T hK
  have hfp := isFinitePresentationOnSite_modulePushforward_of_isOpenImmersion B S hS _ hj _
    hK.1.2 hcl
  have hqc : ((modulePushforward B S hS (D.baseChangeOfMap T)).obj
      (D.sourceSituation.quotientModule T K)).IsQuasicoherentOnSite :=
    @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _ hfp
  refine ⟨hqc, ?_, hfp, ?_⟩
  · refine isFlatOver_modulePushforward_of_isOpenImmersion B S hS _ hj
      (D.targetSituation.projection T) _ hcl hqc ?_
    rw [D.baseChangeOfMap_comp_inclusion_hom T]
    exact hK.1.1.2
  · refine hasProperSupport_modulePushforward_of_isOpenImmersion B S hS _ hj
      (D.targetSituation.projection T) (D.targetSituation.isLocallyOfFiniteType_projection T)
      (by rw [D.baseChangeOfMap_comp_inclusion_hom T];
          exact D.sourceSituation.isLocallyOfFiniteType_projection T)
      (isSeparated_pullbackSnd B S hS _ D.separatedY) _ ?_
    exact hasProperSupport_of_eq B S hS _ _ (D.baseChangeOfMap_comp_inclusion_hom T).symm _ _ hK.2

/-- **Stacks 0DP3, the direct image of a member of `Quot_{F/X/B}(T)` is a member of
`Quot_{G/Y/B}(T)`.** -/
theorem extendQuotient_mem (T : SchemesOver D.base)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.extendQuotient T K ∈ D.targetSituation.properlySupportedQuotients T :=
  (D.targetSituation.mem_properlySupportedQuotients_iff T _).mpr
    (QuotSituation.IsQuotModule.of_iso (D.extendQuotientCokernelIso T hK).symm
      (D.isQuotModule_modulePushforward T hK))

/-- The support of the quotient by the direct image of a member of `Quot_{F/X/B}(T)` lies in
`X_T`. -/
theorem support_extendQuotient_subset (T : SchemesOver D.base)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.targetSituation.support T (D.targetSituation.quotientModule T (D.extendQuotient T K)) ⊆
      Set.range (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom) := by
  have h := supportOfSheaf_cokernel_extendSubobject B S hS
    (D.baseChangeOfMap T) (D.isOpenImmersion_baseChangeOfMap (T := T)) (D.restrictionComparison T)
    (D.sourceSituation.quotientProjection T K) (D.isClosed_image_support_of_mem T hK)
  exact (le_of_eq h).trans (Set.image_subset_range _ _)

/-- **The restriction to `X_T` of a member of `Quot_{G/Y/B}(T)` supported in `X_T` is a member of
`Quot_{F/X/B}(T)`.** -/
theorem restrictQuotient_mem (T : SchemesOver D.base)
    {L : Subobject (D.targetSituation.baseChangeModule T)}
    (hL : L ∈ D.targetSituation.properlySupportedQuotients T)
    (hsub : D.targetSituation.support T (D.targetSituation.quotientModule T L) ⊆
      Set.range (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom)) :
    D.restrictQuotient T L ∈ D.sourceSituation.properlySupportedQuotients T := by
  have hj := D.isOpenImmersion_baseChangeOfMap (T := T)
  refine (D.sourceSituation.mem_properlySupportedQuotients_iff T _).mpr
    (QuotSituation.IsQuotModule.of_iso (D.restrictQuotientCokernelIso T L).symm ?_)
  refine ⟨isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hL.1.1.1, ?_,
    isFinitePresentationOnSite_modulePullback B S hS _ _ hL.1.2, ?_⟩
  · have h := isFlatOver_comp_modulePullback_of_isFlat B S hS (D.baseChangeOfMap T)
      (D.targetSituation.projection T) _ hL.1.1.1 (isFlat_of_isEtale B S hS
        (isEtale_of_isOpenImmersion B S hS hj)) hL.1.1.2
    rwa [D.baseChangeOfMap_comp_inclusion_hom T] at h
  · exact hasProperSupport_modulePullback_of_isOpenImmersion B S hS _ hj
      (D.targetSituation.projection T) (D.sourceSituation.projection T)
      (D.baseChangeOfMap_comp_inclusion T) (D.targetSituation.isLocallyOfFiniteType_projection T)
      (D.sourceSituation.isLocallyOfFiniteType_projection T) _ hL.2 hsub

/-! ### Compatibility with pullback along a morphism of test schemes -/

/-- The square of comparisons of inverse images formed by the base changes of the open immersion
along a morphism of test schemes. -/
def relativeMapSquare {T' T : SchemesOver D.base} (h : T' ⟶ T) :
    modulePullback B S hS (D.baseChangeOfMap T) ⋙
        modulePullback B S hS (D.sourceSituation.relativeMap h) ≅
      modulePullback B S hS (D.targetSituation.relativeMap h) ⋙
        modulePullback B S hS (D.baseChangeOfMap T') :=
  modulePullbackSquare B S hS (k := D.sourceSituation.relativeMap h ≫ D.baseChangeOfMap T)
    rfl (D.relativeMap_comp_baseChangeOfMap h).symm

/-- **The cube of comparisons of inverse images commutes**, by the associativity coherence of
Stacks 03LU. -/
theorem restrictionComparison_trans_baseChangeComparison {T' T : SchemesOver D.base}
    (h : T' ⟶ T) :
    D.restrictionComparison T' ≪≫
        Functor.isoWhiskerRight (D.targetSituation.baseChangeComparison h)
          (modulePullback B S hS (D.baseChangeOfMap T')) =
      Functor.isoWhiskerLeft (modulePullback B S hS D.j)
          (D.sourceSituation.baseChangeComparison h) ≪≫
        Functor.isoWhiskerRight (D.restrictionComparison T)
          (modulePullback B S hS (D.sourceSituation.relativeMap h)) ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.targetSituation.sourceProjection T))
          (D.relativeMapSquare h) :=
  modulePullbackSquare_comp (modulePushforwardCoherence B S hS)
    (ε := D.baseChangeOfMap T') (ε' := D.baseChangeOfMap T) (ε'' := D.j)
    (a := D.sourceSituation.relativeMap h) (a' := D.sourceSituation.sourceProjection T)
    (aa := D.sourceSituation.sourceProjection T')
    (b := D.targetSituation.relativeMap h) (b' := D.targetSituation.sourceProjection T)
    (bb := D.targetSituation.sourceProjection T')
    (baseChangeMap_comp_projection D.structureX h) (baseChangeMap_comp_projection D.structureY h)
    (km := D.sourceSituation.relativeMap h ≫ D.baseChangeOfMap T) rfl
    (D.relativeMap_comp_baseChangeOfMap h).symm
    (kn := D.sourceSituation.sourceProjection T ≫ D.j) rfl (D.baseChangeOfMap_comp_projection T)
    (k := D.sourceSituation.sourceProjection T' ≫ D.j) rfl (D.baseChangeOfMap_comp_projection T')

/-- **Restriction of quotients commutes with pullback along a morphism of test schemes.**  Both
sides are conjugations of the quotient by the two composites of comparisons of inverse images
around the cube formed by `X_{T'}, X_T, X, Y_{T'}, Y_T, Y`, which agree by the associativity
coherence of Stacks 03LU, in the form of `restrictionComparison_trans_baseChangeComparison`. -/
theorem restrictQuotient_quotientPullback {T' T : SchemesOver D.base} (h : T' ⟶ T)
    (L : Subobject (D.targetSituation.baseChangeModule T)) :
    D.restrictQuotient T' (D.targetSituation.quotientPullback h L) =
      D.sourceSituation.quotientPullback h (D.restrictQuotient T L) := by
  have hL := Functor.conjSubobject_comp (D.targetSituation.baseChangeComparison h)
    (D.restrictionComparison T') _ (Iso.refl _)
    (Iso.trans_eq_trans_associator_trans_isoWhiskerLeft_refl_symm _ _) L
  have hR := Functor.conjSubobject_comp (D.restrictionComparison T)
    (Functor.isoWhiskerLeft (modulePullback B S hS D.j) (D.sourceSituation.baseChangeComparison h))
    _ (D.relativeMapSquare h).symm
    (Iso.trans_isoWhiskerLeft_eq_trans_associator_trans_isoWhiskerLeft_symm_symm _ _ _) L
  unfold restrictQuotient QuotientSituation.quotientPullback
  rw [← hL, ← Functor.conjSubobject_isoWhiskerLeft, ← hR]
  congr 1
  exact (D.restrictionComparison_trans_baseChangeComparison h).trans (Iso.trans_assoc _ _ _).symm

/-- The points of `X_{T'}` in `Y_{T'}` are the inverse image of the points of `X_T` in `Y_T`. -/
theorem range_pointsMap_baseChangeOfMap {T' T : SchemesOver D.base} (h : T' ⟶ T) :
    Set.range (pointsMap B S hS (D.sourceSituation.space T').1 (D.baseChangeOfMap T').hom) =
      pointsMap B S hS (D.targetSituation.space T').1 (D.targetSituation.relativeMap h).hom ⁻¹'
        Set.range (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom) := by
  have h₁ := preimage_image_pointsMap_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback_relativeMap h)) Set.univ
  rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at h₁
  exact h₁.symm

/-- The support of the quotient of `G_{T'}` by the pullback of a member of `Quot_{G/Y/B}(T)` is
the inverse image of the support of the quotient. -/
private theorem support_quotientPullback_eq {T' T : SchemesOver D.base} (h : T' ⟶ T)
    {L : Subobject (D.targetSituation.baseChangeModule T)}
    (hL : L ∈ D.targetSituation.properlySupportedQuotients T) :
    D.targetSituation.support T'
        (D.targetSituation.quotientModule T' (D.targetSituation.quotientPullback h L)) =
      pointsMap B S hS (D.targetSituation.space T').1 (D.targetSituation.relativeMap h).hom ⁻¹'
        D.targetSituation.support T (D.targetSituation.quotientModule T L) := by
  have hft : SheafOfModules.IsFiniteTypeOnSite (D.targetSituation.quotientModule T L) :=
    @SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ hL.1.2
  rw [QuotSituation.support, supportOfSheaf_eq_of_iso B S hS _
    (D.targetSituation.quotientPullbackCokernelIso h L)]
  exact supportOfSheaf_modulePullback_eq B S hS _ _ hL.1.1.1 hft

/-- **Stacks 0DP3, naturality.**  The direct image of quotients commutes with pullback along a
morphism of test schemes. -/
theorem extendQuotient_quotientPullback {T' T : SchemesOver D.base} (h : T' ⟶ T)
    {K : Subobject (D.sourceSituation.baseChangeModule T)}
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.extendQuotient T' (D.sourceSituation.quotientPullback h K) =
      D.targetSituation.quotientPullback h (D.extendQuotient T K) := by
  have hmem := D.targetSituation.quotientPullback_mem_properlySupportedQuotients h _
    (D.extendQuotient_mem T hK)
  have hsub : D.targetSituation.support T'
      (D.targetSituation.quotientModule T' (D.targetSituation.quotientPullback h
        (D.extendQuotient T K))) ⊆
      Set.range (pointsMap B S hS (D.sourceSituation.space T').1 (D.baseChangeOfMap T').hom) := by
    rw [D.support_quotientPullback_eq h (D.extendQuotient_mem T hK),
      D.range_pointsMap_baseChangeOfMap h]
    exact Set.preimage_mono (D.support_extendQuotient_subset T hK)
  rw [← D.extendQuotient_restrictQuotient T' _
    (D.targetSituation.isClosed_support_of_mem hmem.1) hsub,
    D.restrictQuotient_quotientPullback h,
    D.restrictQuotient_extendQuotient T K (D.isClosed_image_support_of_mem T hK)]

/-! ### The morphism of Quot functors -/

/-- **Stacks 0DP3, the morphism of Quot functors.**  The morphism
`Quot_{F/X/B} ⟶ Quot_{G/Y/B}` sending a quotient `F_T ⟶ Q` to `G_T ⟶ j_{T,*}Q`. -/
def quotFunctorMap : D.sourceSituation.quotFunctor ⟶ D.targetSituation.quotFunctor where
  app T := ↾fun K ↦ ⟨D.extendQuotient T.unop K.1, D.extendQuotient_mem T.unop K.2⟩
  naturality {T T'} m := by
    apply ConcreteCategory.hom_ext
    intro K
    exact Subtype.ext (D.extendQuotient_quotientPullback m.unop K.2)

/-- The direct image of a quotient over a scheme of the site. -/
def quotFamilyOverExtend (T : BigFppfOver B S hS) (x : QuotFamilyOver D.sourceSituation T) :
    QuotFamilyOver D.targetSituation T where
  toBase := x.toBase
  subobject := D.extendQuotient _ x.subobject
  mem := D.extendQuotient_mem _ x.mem

/-- The direct image of a quotient over a scheme of the site is the morphism of Quot functors at
the test scheme the quotient lies over. -/
theorem quotFamilyOverExtend_subobject (T : BigFppfOver B S hS)
    (x : QuotFamilyOver D.sourceSituation T) :
    (D.quotFamilyOverExtend T x).subobject =
      ((D.quotFunctorMap.app (Opposite.op (CostructuredArrow.mk x.toBase)))
        ⟨x.subobject, x.mem⟩).1 :=
  rfl

/-- Taking the direct image of a quotient commutes with base change. -/
theorem quotFamilyOverExtend_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D.sourceSituation T) :
    D.quotFamilyOverExtend T' (x.baseChange g) = (D.quotFamilyOverExtend T x).baseChange g := by
  obtain ⟨b, K, hK⟩ := x
  have key : D.extendQuotient (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ b))
      (D.sourceSituation.quotientPullback
        (QuotFamilyOver.restrict (D := D.sourceSituation) g b) K) =
      D.targetSituation.quotientPullback (QuotFamilyOver.restrict (D := D.targetSituation) g b)
        (D.extendQuotient (CostructuredArrow.mk b) K) :=
    D.extendQuotient_quotientPullback (QuotFamilyOver.restrict (D := D.sourceSituation) g b) hK
  dsimp only [quotFamilyOverExtend, QuotFamilyOver.baseChange]
  congr 1

/-- The morphism of Quot presheaves of the site induced by the direct image. -/
def quotSitePresheafMap :
    D.sourceSituation.quotSitePresheaf ⟶ D.targetSituation.quotSitePresheaf where
  app T := TypeCat.ofHom fun x => D.quotFamilyOverExtend T.unop x
  naturality {T T'} g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact D.quotFamilyOverExtend_baseChange g.unop x

/-- The direct image of quotients over a scheme of the site is injective: restricting recovers
the quotient. -/
theorem quotFamilyOverExtend_injective (T : BigFppfOver B S hS) :
    Function.Injective (D.quotFamilyOverExtend T) := by
  rintro ⟨ab, aK, aM⟩ ⟨bb, bK, bM⟩ hab
  simp only [quotFamilyOverExtend] at hab
  have hbase : ab = bb := congrArg QuotFamilyOver.toBase hab
  subst hbase
  have hsub : D.extendQuotient (CostructuredArrow.mk ab) aK =
      D.extendQuotient (CostructuredArrow.mk ab) bK :=
    eq_of_heq (QuotFamilyOver.subobject_heq hab)
  have hK : aK = bK := by
    rw [← D.restrictQuotient_extendQuotient _ aK (D.isClosed_image_support_of_mem _ aM),
      ← D.restrictQuotient_extendQuotient _ bK (D.isClosed_image_support_of_mem _ bM), hsub]
  subst hK
  rfl

/-- The condition `Supp(Q) ⊆ |X_T|` on a quotient `G_T ⟶ Q` over a scheme of the site. -/
def SupportedInOpen {T : BigFppfOver B S hS} (y : QuotFamilyOver D.targetSituation T) : Prop :=
  D.targetSituation.support (CostructuredArrow.mk y.toBase)
      (D.targetSituation.quotientModule _ y.subobject) ⊆
    Set.range (pointsMap B S hS (D.sourceSituation.space (CostructuredArrow.mk y.toBase)).1
      (D.baseChangeOfMap (CostructuredArrow.mk y.toBase)).hom)

/-- **A quotient of `G_T` is the direct image of a quotient of `F_T` exactly when its support
lies in `X_T`.** -/
theorem exists_quotFamilyOverExtend_eq_iff {T : BigFppfOver B S hS}
    (y : QuotFamilyOver D.targetSituation T) :
    (∃ x, D.quotFamilyOverExtend T x = y) ↔ D.SupportedInOpen y := by
  obtain ⟨b, L, hL⟩ := y
  constructor
  · rintro ⟨⟨b₂, K, hK⟩, hx⟩
    dsimp only [quotFamilyOverExtend] at hx
    injection hx with hb hs
    subst hb
    have hsub : D.extendQuotient (CostructuredArrow.mk b₂) K = L := eq_of_heq hs
    subst hsub
    unfold SupportedInOpen
    exact D.support_extendQuotient_subset (CostructuredArrow.mk b₂) hK
  · intro hsupp
    refine ⟨⟨b, D.restrictQuotient _ L, D.restrictQuotient_mem _ hL hsupp⟩, ?_⟩
    have key := D.extendQuotient_restrictQuotient (CostructuredArrow.mk b) L
      (D.targetSituation.isClosed_support_of_mem hL.1) hsupp
    dsimp only [quotFamilyOverExtend]
    congr 1

/-! ### The open locus of quotients supported in the open subspace -/

/-- The locus of points `t` of a scheme of the site over which a quotient `G_T ⟶ Q` has
`Supp(Q_t) ⊆ |X_t|`: the complement of the image in `T` of the part of the support of `Q` lying
outside `X_T`. -/
def supportLocus {T : BigFppfOver B S hS} (y : QuotFamilyOver D.targetSituation T) :
    Set (points B S hS (yoneda.obj T)) :=
  (pointsMap B S hS (D.targetSituation.space (CostructuredArrow.mk y.toBase)).1
      (D.targetSituation.projection (CostructuredArrow.mk y.toBase)).hom ''
    (D.targetSituation.support (CostructuredArrow.mk y.toBase)
        (D.targetSituation.quotientModule _ y.subobject) \
      Set.range (pointsMap B S hS (D.sourceSituation.space (CostructuredArrow.mk y.toBase)).1
        (D.baseChangeOfMap (CostructuredArrow.mk y.toBase)).hom)))ᶜ

/-- **The locus is open.**  The part of the support of `Q` outside `X_T` is closed in the support,
which is proper over `T`, so it is proper over `T` and its image in `T` is closed. -/
theorem isOpen_supportLocus {T : BigFppfOver B S hS} (y : QuotFamilyOver D.targetSituation T) :
    IsOpen (D.supportLocus y) := by
  obtain ⟨hZcl, hZproper⟩ := y.mem.2
  have hR : IsOpen (Set.range (pointsMap B S hS
      (D.sourceSituation.space (CostructuredArrow.mk y.toBase)).1
      (D.baseChangeOfMap (CostructuredArrow.mk y.toBase)).hom)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _
      (D.isOpenImmersion_baseChangeOfMap (T := CostructuredArrow.mk y.toBase))
  have hCcl := hZcl.inter hR.isClosed_compl
  have hCproper := isProperOver_of_subset B S hS
    (D.targetSituation.space (CostructuredArrow.mk y.toBase)).2
    ((schemeSpaceFunctor B S hS).obj T).2 _
    (D.targetSituation.isLocallyOfFiniteType_projection (CostructuredArrow.mk y.toBase)) _ _
    hCcl hZcl Set.inter_subset_left hZproper
  exact (isClosed_image_of_universallyClosed_ι_comp B S hS
    (D.targetSituation.space (CostructuredArrow.mk y.toBase)).2
    ((schemeSpaceFunctor B S hS).obj T).2 _ _ hCcl hCproper.2.2).isOpen_compl

/-- **The support condition after base change is the locus.**  For `g : U ⟶ T`, the base change
of a quotient of `G_T` to `U` is supported in `X_U` exactly when `g` lands in the locus: the
support of the base change is the inverse image of the support (Stacks 07TZ, part (3)), the
points of `X_U` are the inverse image of those of `X_T`, and by Stacks 03H4 a point of `Y_T`
over `g(u)` lifts to `Y_U`. -/
theorem supportedInOpen_baseChange_iff {T U : BigFppfOver B S hS}
    (y : QuotFamilyOver D.targetSituation T) (g : U ⟶ T) :
    D.SupportedInOpen (y.baseChange g) ↔
      Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map g)) ⊆ D.supportLocus y := by
  obtain ⟨b, L, hL⟩ := y
  set m := QuotFamilyOver.restrict (D := D.targetSituation) g b
  have hsupp := D.support_quotientPullback_eq m hL
  have h03H4 := preimage_image_pointsMap_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.structureY m))
    (D.targetSituation.support _ (D.targetSituation.quotientModule _ L) \
      Set.range (pointsMap B S hS (D.sourceSituation.space (CostructuredArrow.mk b)).1
        (D.baseChangeOfMap (CostructuredArrow.mk b)).hom))
  show D.targetSituation.support _
      (D.targetSituation.quotientModule _ (D.targetSituation.quotientPullback m L)) ⊆
    Set.range (pointsMap B S hS _ (D.baseChangeOfMap _).hom) ↔ _
  rw [hsupp, D.range_pointsMap_baseChangeOfMap m, ← Set.diff_eq_empty, ← Set.preimage_diff,
    ← Set.image_eq_empty (f := pointsMap B S hS _ (baseChangeInclusion D.structureY _).hom),
    ← h03H4]
  unfold supportLocus
  constructor
  · rintro h _ ⟨u, rfl⟩ hu
    exact (Set.eq_empty_iff_forall_notMem.mp h) u hu
  · intro h
    exact Set.eq_empty_of_forall_notMem fun u hu => h ⟨u, rfl⟩ hu

/-! ### The open immersion -/

/-- The morphism of Quot presheaves induced by the direct image, read in given models of the two
Quot presheaves of the site. -/
def quotModelMap (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation) : MX.presheaf ⟶ MY.presheaf :=
  MY.mapFrom (MX.iso.hom ≫ D.quotSitePresheafMap)

/-- The morphism of models is the direct image of quotients. -/
theorem familyEquiv_quotModelMap (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation) (T : BigFppfOver B S hS)
    (z : MX.presheaf.obj (Opposite.op T)) :
    MY.familyEquiv T ((D.quotModelMap MX MY).app (Opposite.op T) z) =
      D.quotFamilyOverExtend T (MX.familyEquiv T z) :=
  types_congr_hom (MY.iso.inv_hom_id_app (Opposite.op T))
    ((MX.iso.hom ≫ D.quotSitePresheafMap).app (Opposite.op T) (ULift.up z))

/-- The morphism of models is a monomorphism. -/
theorem mono_quotModelMap (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation) : Mono (D.quotModelMap MX MY) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro a b hab
  have hq := congrArg (MY.familyEquiv T.unop) hab
  rw [D.familyEquiv_quotModelMap, D.familyEquiv_quotModelMap] at hq
  exact (MX.familyEquiv T.unop).injective (D.quotFamilyOverExtend_injective T.unop hq)

/-- A section of the model of `Quot_{G/Y/B}` is in the range exactly when the quotient it names
is a direct image. -/
theorem mem_range_quotModelMap_iff (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation) (T : BigFppfOver B S hS)
    (z : MY.presheaf.obj (Opposite.op T)) :
    z ∈ Set.range ((D.quotModelMap MX MY).app (Opposite.op T)) ↔
      ∃ x, D.quotFamilyOverExtend T x = MY.familyEquiv T z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨MX.familyEquiv T w, (D.familyEquiv_quotModelMap MX MY T w).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(MX.familyEquiv T).symm x, ?_⟩
    apply (MY.familyEquiv T).injective
    rw [D.familyEquiv_quotModelMap, Equiv.apply_symm_apply, hx]

/-- The morphism of models is a morphism over the base. -/
theorem quotModelMap_comp_toBase (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation) :
    D.quotModelMap MX MY ≫ MY.toBase = MX.toBase := by
  ext T z
  have h := D.familyEquiv_quotModelMap MX MY T.unop z
  show (D.targetSituation.quotSitePresheafToBase.app T
      (MY.iso.hom.app T ⟨(D.quotModelMap MX MY).app T z⟩)).down =
    (D.sourceSituation.quotSitePresheafToBase.app T (MX.iso.hom.app T ⟨z⟩)).down
  rw [QuotSituation.quotSitePresheafToBase_app_apply,
    QuotSituation.quotSitePresheafToBase_app_apply]
  exact congrArg (fun x : QuotFamilyOver D.targetSituation T.unop => yonedaEquiv x.toBase.hom) h

/-- **Stacks 0DP3.**  Let `j : X ⟶ Y` be an open immersion of algebraic spaces which are
separated and of finite presentation over an algebraic space `B`, let `G` be a quasi-coherent
`𝒪_Y`-module and set `F = j^*G`.  Then the morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` sending a
quotient `F_T ⟶ Q` to `G_T ⟶ j_{T,*}Q` is an open immersion of spaces over `B`, read in any
models of the two Quot functors.

It is a monomorphism, restriction to `X_T` recovering a quotient from its direct image; a
section of the target over a scheme `T` of the site is a quotient `G_T ⟶ Q`, and a morphism
`U ⟶ T` lies in the inverse image of the range exactly when the base change of `Q` to `U` is
supported in `X_U`, that is, exactly when `U` maps into the complement of the image in `T` of
the part of the support of `Q` outside `X_T`, which is open because that support is proper over
`T`.

The statement is for arbitrary models;
`isOpenImmersion_quotSitePresheafModelMap_ofOpenImmersion` is the one for the canonical models. -/
theorem isOpenImmersion_quotModelMap (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation) :
    IsOpenImmersion B S hS (D.quotModelMap MX MY) ∧
      D.quotModelMap MX MY ≫ MY.toBase = MX.toBase := by
  refine ⟨?_, D.quotModelMap_comp_toBase MX MY⟩
  have _ := D.mono_quotModelMap MX MY
  apply isOpenImmersion_of_isOpenSubspace_range_preimage
  intro T q
  set y := MY.familyEquiv T (yonedaEquiv q) with hy
  have heq : (Subfunctor.range (D.quotModelMap MX MY)).preimage q =
      openSubspaceOfPoints B S hS (yoneda.obj T) (D.supportLocus y) := by
    ext U g
    have hqg : q.app U g = MY.presheaf.map (Quiver.Hom.op g) (yonedaEquiv q) := by
      have hnat := NatTrans.naturality_apply q (Quiver.Hom.op g) (𝟙 T)
      rw [yonedaEquiv_apply]
      simpa using hnat
    show q.app U g ∈ Set.range ((D.quotModelMap MX MY).app U) ↔
      g ∈ (openSubspaceOfPoints B S hS (yoneda.obj T) (D.supportLocus y)).obj U
    rw [hqg, D.mem_range_quotModelMap_iff MX MY, QuotSitePresheafModel.familyEquiv_map,
      D.exists_quotFamilyOverExtend_eq_iff, D.supportedInOpen_baseChange_iff,
      mem_openSubspaceOfPoints_iff]
    rfl
  rw [heq]
  exact isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS T) _
    (D.isOpen_supportLocus y)

/-- The morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` read in the canonical models of the two Quot
presheaves in the universe of the site
(`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafModel`). -/
abbrev quotSitePresheafModelMap :
    D.sourceSituation.quotSitePresheafModel.presheaf ⟶
      D.targetSituation.quotSitePresheafModel.presheaf :=
  D.quotModelMap D.sourceSituation.quotSitePresheafModel D.targetSituation.quotSitePresheafModel

/-- Let `B` be an algebraic space, let `j : X ⟶ Y` be an open immersion of algebraic spaces which
are separated and of finite presentation over `B`, let `G` be a quasi-coherent `𝒪_Y`-module and set
`F = j^*G`.  Then the morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`, sending a quotient `F_T ⟶ Q` to
`G_T ⟶ j_{T,*}Q`, is an open immersion of spaces over `B`.

The Quot functors are read in their canonical models in the universe of the site
(`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafModel`); for arbitrary models this is
`AlgebraicGeometry.Space.QuotOpenSubspaceSituation.isOpenImmersion_quotModelMap`. -/
@[stacks 0DP3]
theorem isOpenImmersion_quotSitePresheafModelMap :
    IsOpenImmersion B S hS
        (D.quotModelMap D.sourceSituation.quotSitePresheafModel
          D.targetSituation.quotSitePresheafModel) ∧
      D.quotModelMap D.sourceSituation.quotSitePresheafModel
          D.targetSituation.quotSitePresheafModel ≫ D.targetSituation.quotSitePresheafModel.toBase =
        D.sourceSituation.quotSitePresheafModel.toBase :=
  D.isOpenImmersion_quotModelMap _ _

/-- The standing data of Stacks 0DP3 assembled from its hypotheses: an algebraic space `B`
(`base`), algebraic spaces `X` and `Y` over it with structure morphisms `X ⟶ B` and `Y ⟶ B`, both
separated and of finite presentation, an open immersion `j : X ⟶ Y` over `B`, and a quasi-coherent
`𝒪_Y`-module `G`. -/
def ofOpenImmersion (base X Y : AlgebraicSpaces B S hS) (j : X ⟶ Y)
    (structureX : X ⟶ base) (structureY : Y ⟶ base) (comp : j ≫ structureY = structureX)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (quasicoherent : G.IsQuasicoherentOnSite)
    (openImmersion : IsOpenImmersion B S hS j.hom)
    (separatedX : IsSeparated B S hS structureX.hom)
    (separatedY : IsSeparated B S hS structureY.hom)
    (finitePresentationX : IsFinitePresentation B S hS structureX.hom)
    (finitePresentationY : IsFinitePresentation B S hS structureY.hom) :
    QuotOpenSubspaceSituation B S hS where
  base := base
  X := X
  Y := Y
  j := j
  structureX := structureX
  structureY := structureY
  comp := comp
  G := G
  quasicoherent := quasicoherent
  openImmersion := openImmersion
  separatedX := separatedX
  separatedY := separatedY
  finitePresentationX := finitePresentationX
  finitePresentationY := finitePresentationY

/-- Let `B` be an algebraic space, let `j : X ⟶ Y` be an open immersion of algebraic spaces which
are separated and of finite presentation over `B`, let `G` be a quasi-coherent `𝒪_Y`-module and set
`F = j^*G`.  Then the morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`, sending a quotient `F_T ⟶ Q` to
`G_T ⟶ j_{T,*}Q`, is an open immersion of spaces over `B`.

The situation `D` is assembled from the hypotheses by
`AlgebraicGeometry.Space.QuotOpenSubspaceSituation.ofOpenImmersion`.  Its source Quot situation
`D.sourceSituation` is `F/X/B` of Stacks 09TR with `F = (modulePullback B S hS j).obj G`, the
inverse image `j^*G` (quasi-coherent by Stacks 03GA), and its target Quot situation
`D.targetSituation` is `G/Y/B`.  The Quot functors are read in their canonical models in the
universe of the site (`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafModel`), where being
an open immersion of algebraic spaces is defined (Stacks 02YU); for arbitrary models this is
`AlgebraicGeometry.Space.QuotOpenSubspaceSituation.isOpenImmersion_quotModelMap`.  Over a test
scheme the morphism takes a quotient to its direct image
(`AlgebraicGeometry.Space.QuotOpenSubspaceSituation.familyEquiv_quotModelMap`), and the second
conjunct says it is a morphism over `B`. -/
@[stacks 0DP3]
theorem isOpenImmersion_quotSitePresheafModelMap_ofOpenImmersion
    (base X Y : AlgebraicSpaces B S hS) (j : X ⟶ Y)
    (structureX : X ⟶ base) (structureY : Y ⟶ base) (comp : j ≫ structureY = structureX)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (quasicoherent : G.IsQuasicoherentOnSite)
    (openImmersion : IsOpenImmersion B S hS j.hom)
    (separatedX : IsSeparated B S hS structureX.hom)
    (separatedY : IsSeparated B S hS structureY.hom)
    (finitePresentationX : IsFinitePresentation B S hS structureX.hom)
    (finitePresentationY : IsFinitePresentation B S hS structureY.hom) :
    let D := ofOpenImmersion base X Y j structureX structureY comp G quasicoherent openImmersion
      separatedX separatedY finitePresentationX finitePresentationY
    D.sourceSituation.F = (modulePullback B S hS j).obj G ∧
      IsOpenImmersion B S hS D.quotSitePresheafModelMap ∧
      D.quotSitePresheafModelMap ≫ D.targetSituation.quotSitePresheafModel.toBase =
        D.sourceSituation.quotSitePresheafModel.toBase :=
  ⟨rfl, (ofOpenImmersion base X Y j structureX structureY comp G quasicoherent openImmersion
    separatedX separatedY finitePresentationX
    finitePresentationY).isOpenImmersion_quotSitePresheafModelMap⟩

end QuotOpenSubspaceSituation

end AlgebraicGeometry.Space

end
