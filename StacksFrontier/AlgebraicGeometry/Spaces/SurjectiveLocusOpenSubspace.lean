module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties

/-!
# The locus where a map of quasi-coherent modules is surjective is an open subspace

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `u : F ⟶ G` be a
map of quasi-coherent `𝒪_X`-modules, that is, a situation of Stacks 083F.  Assume `f` is
locally of finite presentation, `G` is of finite type, and the support of `G` is proper over
`Y`.  Then the locus `F_surj` of schemes `T` over `Y` at which the base change `u_T` is
surjective is the open subspace of `Y` on the complement of `|f|(Supp(Coker u))`.

The argument is the one of the source.  Pullback of modules is a left adjoint, hence right
exact, so `Coker(u_T) = (Coker u)_T`; and `u_T` is surjective exactly when its cokernel
vanishes, which — a module being zero exactly when its support is empty — happens exactly when
the support of `(Coker u)_T` is empty.  Formation of the support commutes with pullback, so that
support is the inverse image under the base-change projection `X_T ⟶ X` of `Supp(Coker u)`, and
it is empty exactly when the image of `|T|` in `|Y|` misses `|f|(Supp(Coker u))`: that is the
surjectivity of the comparison map from the points of a fibre product onto the fibre product of
the point sets, Stacks 03H4.  Finally `Supp(Coker u)` is a closed subset of `Supp(G)`, hence
proper over `Y`, so its image is closed by Stacks 0CZG, and the complement of that image carries
an open subspace of `Y` by Stacks 03BZ.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.cokernelSupportImage`: the set
  `|f|(Supp(Coker u))` of points of `Y`.

## Main results

* `AlgebraicGeometry.Space.range_le_openSubspaceOfPoints_iff`: a morphism from a representable
  presheaf factors through the subfunctor cut out by a set of points exactly when the image of
  its points lies in that set.
* `AlgebraicGeometry.Space.ModuleMapSituation.isClosed_cokernelSupportImage`: the image of the
  support of the cokernel is closed.
* `AlgebraicGeometry.Space.ModuleMapSituation.isSurjectiveAt_iff_range_pointsMap_subset`: the
  pointwise form — the base change of the map at a test scheme is surjective exactly when the
  image of the points of the test scheme misses `|f|(Supp(Coker u))`.
* `AlgebraicGeometry.Space.ModuleMapSituation.exists_isOpenSubspace_isSurjectiveAt_iff`:
  **Stacks 09TP** — the surjectivity locus is represented by an open subspace of `Y`, so it is
  an algebraic space and its morphism to `Y` is an open immersion.

## Implementation notes

The equality of supports `Supp(g^*M) = |g|⁻¹(Supp M)` the argument turns on is
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`, Stacks 07TZ part (3), which holds
for an arbitrary morphism `g` of algebraic spaces and a quasi-coherent `M` of finite type.  It is
proved from the stalk formula `(g^*M)_x̄ = M_ȳ ⊗_{𝒪_{Y,ȳ}} 𝒪_{X,x̄}` of Stacks 05VQ, which is
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso` with no hypothesis on `g` at all; an
étale `g` would not suffice, since the base-change projection `X ×_Y T ⟶ X` is not étale.

The two hypotheses the equality wants of `Coker u` are both discharged here.  It is of finite
type because `𝒢` is, by
`AlgebraicGeometry.Space.ModuleMapSituation.isFiniteTypeOnSite_cokernelModule`;
and it is quasi-coherent by
`AlgebraicGeometry.Space.ModuleMapSituation.isQuasicoherentOnSite_cokernel_u`, which is
unconditional — the local presentation step is discharged
in `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`.

The Stacks Project's proof of Stacks 09TP cites Stacks 07TY for "formation of the support commutes
with pullback"; 07TY is the étale-chart case and the fact actually used is part (3) of
Stacks 07TZ.

The surjectivity locus is `AlgebraicGeometry.Space.ModuleMapSituation.surjFunctor`, a
subterminal presheaf on the test schemes over `Y`.  Saying that it *is an algebraic space with
an open immersion to `Y`* is saying that it is represented by an open subspace of `Y`: the
conclusion below produces a subfunctor `U` of `Y` which is an
`AlgebraicGeometry.Space.IsOpenSubspace` — an algebraic space whose inclusion is an open
immersion — together with, at every test scheme, the identification of the value of the locus
with the factorizations of the structure morphism through `U`.  Since both are subterminal, that
identification is the isomorphism of functors over `Y`.

Everything is at the module universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullbackSystem` — the system of pullback functors the loci of
Stacks 083F consume — is available only there; this follows Stacks 0CVM,
`AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor_secondMap_eq_zeroFunctor`, which is
stated at `ModuleMapSituation.{u, u}` for the same reason.

## References

* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring a representable presheaf through the subspace cut out by a set of points -/

/-- A morphism from a representable presheaf factors through the subfunctor cut out by a set
`W` of points exactly when the image of its points lies in `W`.

One direction is the definition of `AlgebraicGeometry.Space.openSubspaceOfPoints` read at the
identity section; the other restricts a section to the representable presheaf it is defined
over. -/
theorem range_le_openSubspaceOfPoints_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Set (points B S hS F)) {A : BigFppfOver B S hS} (t : yoneda.obj A ⟶ F) :
    Subfunctor.range t ≤ openSubspaceOfPoints B S hS F W ↔
      Set.range (pointsMap B S hS (yoneda.obj A) t) ⊆ W := by
  constructor
  · intro h
    have h1 : t.app (Opposite.op A) (𝟙 A) ∈
        (openSubspaceOfPoints B S hS F W).obj (Opposite.op A) := h _ ⟨𝟙 A, rfl⟩
    rw [mem_openSubspaceOfPoints_iff] at h1
    have ht : yonedaEquiv.symm (t.app (Opposite.op A) (𝟙 A)) = t := by
      rw [← yonedaEquiv_apply, Equiv.symm_apply_apply]
    rwa [ht] at h1
  · rintro h X x ⟨g, rfl⟩
    rw [mem_openSubspaceOfPoints_iff]
    have hg : yonedaEquiv.symm (t.app X g) = yoneda.map g ≫ t := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rw [hg, pointsMap_comp]
    exact (Set.range_comp_subset_range _ _).trans h

/-- A morphism from a representable presheaf whose points land in a set of points factors
through the subfunctor that set cuts out, and conversely. -/
theorem exists_factor_openSubspaceOfPoints_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Set (points B S hS F)) {A : BigFppfOver B S hS} (t : yoneda.obj A ⟶ F) :
    (∃ k : yoneda.obj A ⟶ (openSubspaceOfPoints B S hS F W).toFunctor,
        k ≫ (openSubspaceOfPoints B S hS F W).ι = t) ↔
      Set.range (pointsMap B S hS (yoneda.obj A) t) ⊆ W := by
  rw [← range_le_openSubspaceOfPoints_iff B S hS W t]
  refine ⟨fun ⟨k, hk⟩ X x hx => ?_, fun h => ⟨Subfunctor.lift t h, Subfunctor.lift_ι t h⟩⟩
  obtain ⟨y, rfl⟩ := hx
  exact hk ▸ (k.app X y).property

namespace ModuleMapSituation

variable {B S hS} (D : ModuleMapSituation.{u, u} B S hS)

/-! ### The support of the cokernel and its image in the base -/

/-- The cokernel of the map of the situation, as an `𝒪_X`-module.  Naming it fixes the module
universe before the cokernel is formed, which the elaborator does not do on its own when the
cokernel appears under `SheafOfModules.toSheaf`. -/
abbrev cokernelModule : Modules.{u, u} B S hS D.X.1 D.X.2 := cokernel D.u

/-- The image in the points of `Y` of the support of the cokernel of the map: the set

`|f|(Supp(Coker u))`

whose complement is the surjectivity locus of Stacks 09TP. -/
@[sga "6 XII 4.6" "partial"]
def cokernelSupportImage : Set (points B S hS D.Y.1) :=
  pointsMap B S hS D.X.1 D.f.hom ''
    supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.cokernelModule)

/-- The cokernel of the map is of finite type as soon as its target is, being a quotient of
it; this is the finite type clause of Stacks 05VR for a quotient. -/
theorem isFiniteTypeOnSite_cokernelModule (hG : SheafOfModules.IsFiniteTypeOnSite D.G) :
    SheafOfModules.IsFiniteTypeOnSite D.cokernelModule :=
  isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS D.X.1 D.X.property D.u hG

/-- The support of the cokernel of the map is closed, by Stacks 07TZ applied to it: it is of
finite type because its target is. -/
theorem isClosed_supportOfSheaf_cokernelModule (hG : SheafOfModules.IsFiniteTypeOnSite D.G) :
    IsClosed (supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.cokernelModule)) :=
  have := D.isFiniteTypeOnSite_cokernelModule hG
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS D.X.1 D.X.property D.cokernelModule

/-- **Stacks 04KB part (5)** for the projection onto the cokernel: the support of the cokernel
of the map is contained in the support of its target. -/
theorem supportOfSheaf_cokernelModule_subset :
    supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.cokernelModule) ⊆
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) :=
  @supportOfSheaf_subset_of_isLocallySurjective B S hS D.X.1 D.X.property _ _
    ((SheafOfModules.toSheaf _).map (cokernel.π D.u))
    (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (cokernel.π D.u))

/-- **Stacks 0CZE** for the cokernel: if the support of the target of the map is proper over
`Y`, so is the support of the cokernel, which is a closed subset of it. -/
theorem hasProperSupport_cokernel (hf : IsLocallyOfFiniteType B S hS D.f.hom)
    (hG : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom hf
      ((SheafOfModules.toSheaf _).obj D.G)) :
    HasProperSupport B S hS D.X.property D.Y.property D.f.hom hf
      ((SheafOfModules.toSheaf _).obj D.cokernelModule) :=
  hasProperSupport_of_subset B S hS D.X.property D.Y.property D.f.hom hf
    (D.isClosed_supportOfSheaf_cokernelModule hG) D.supportOfSheaf_cokernelModule_subset
    hproper

/-- **Stacks 0CZG.** The image in `Y` of the support of the cokernel is closed: that support is
proper over `Y`, so the reduced induced subspace on it is universally closed over `Y` and
therefore closed on points. -/
@[sga "6 XII 4.6" "partial"]
theorem isClosed_cokernelSupportImage (hf : IsLocallyOfFiniteType B S hS D.f.hom)
    (hG : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom hf
      ((SheafOfModules.toSheaf _).obj D.G)) :
    IsClosed D.cokernelSupportImage := by
  obtain ⟨hcl, hpr⟩ := D.hasProperSupport_cokernel hf hG hproper
  exact isClosed_image_of_universallyClosed_ι_comp B S hS D.X.property D.Y.property D.f.hom
    _ hcl hpr.2.2

/-! ### The pointwise criterion -/

/-- The base change of the map at a test scheme is surjective exactly when the pullback of the
cokernel to that base change is zero.

Pullback of modules is a left adjoint, hence preserves cokernels, so the cokernel of the base
changed map is the pullback of the cokernel; and a map in an abelian category is an epimorphism
exactly when its cokernel is zero. -/
theorem isSurjectiveAt_iff_isZero_modulePullback_cokernelModule (T : D.SchemesOver) :
    D.IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      IsZero ((modulePullback B S hS (D.baseChangeProjection T)).obj D.cokernelModule) := by
  have hadj := modulePullbackAdjunction B S hS (D.baseChangeProjection T)
  have := hadj.isLeftAdjoint
  have hpc : PreservesColimitsOfSize.{0, 0}
      (modulePullback B S hS (D.baseChangeProjection T)) :=
    hadj.leftAdjoint_preservesColimits
  show Epi ((modulePullback B S hS (D.baseChangeProjection T)).map D.u) ↔ _
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact ⟨fun h => h.of_iso
      (PreservesCokernel.iso (modulePullback B S hS (D.baseChangeProjection T)) D.u),
    fun h => h.of_iso
      (PreservesCokernel.iso (modulePullback B S hS (D.baseChangeProjection T)) D.u).symm⟩

/-- The inverse image under the base-change projection of a set of points of `X` is empty
exactly when the image of the points of the test scheme misses the image of that set in `Y`.

This is Stacks 03H4, the surjectivity of the comparison map from the points of a fibre product
onto the fibre product of the point sets, applied to the cartesian square defining `X_T`. -/
theorem preimage_eq_empty_iff (T : D.SchemesOver) (Z : Set (points B S hS D.X.1)) :
    pointsMap B S hS (D.baseChangeSpace T).1 (D.baseChangeProjection T).hom ⁻¹' Z = ∅ ↔
      Set.range (pointsMap B S hS (yoneda.obj T.left) T.hom.hom) ⊆
        (pointsMap B S hS D.X.1 D.f.hom '' Z)ᶜ := by
  have hsq : IsPullback (D.baseChangeProjection T).hom (D.baseChangeInclusion T).hom
      D.f.hom T.hom.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom)
  constructor
  · intro h
    rintro b ⟨s, rfl⟩ ⟨x, hxZ, hxb⟩
    obtain ⟨w, hwx, -⟩ := exists_points_of_isPullback B S hS hsq x s hxb
    refine Set.eq_empty_iff_forall_notMem.1 h w ?_
    rwa [Set.mem_preimage, hwx]
  · intro h
    refine Set.eq_empty_iff_forall_notMem.2 fun w hw => ?_
    refine h ⟨pointsMap B S hS (D.baseChangeSpace T).1 (D.baseChangeInclusion T).hom w, rfl⟩
      ⟨pointsMap B S hS (D.baseChangeSpace T).1 (D.baseChangeProjection T).hom w, hw, ?_⟩
    exact pointsMap_apply_comm B S hS hsq.w w

/-- **The pointwise form of Stacks 09TP.** The base change of the map at a test scheme `T` over
`Y` is surjective exactly when the image of the points of `T` in `|Y|` misses
`|f|(Supp(Coker u))`.

The support of the pullback of `Coker u` to the base change `X_T` is the inverse image of
`Supp(Coker u)` by Stacks 07TZ part (3),
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`, whose two hypotheses on `Coker u`
are met: it is quasi-coherent unconditionally, and it is of finite type because `𝒢` is. -/
theorem isSurjectiveAt_iff_range_pointsMap_subset
    (hG : SheafOfModules.IsFiniteTypeOnSite D.G) (T : D.SchemesOver) :
    D.IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      Set.range (pointsMap B S hS (yoneda.obj T.left) T.hom.hom) ⊆
        D.cokernelSupportImageᶜ := by
  have hft := D.isFiniteTypeOnSite_cokernelModule hG
  have hpre : pointsMap B S hS (D.baseChangeSpace T).1 (D.baseChangeProjection T).hom ⁻¹'
        supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.cokernelModule) = ∅ ↔
      supportOfSheaf B S hS (D.baseChangeSpace T).1
        ((SheafOfModules.toSheaf _).obj
          ((modulePullback B S hS (D.baseChangeProjection T)).obj D.cokernelModule)) = ∅ := by
    rw [supportOfSheaf_modulePullback_eq B S hS (D.baseChangeProjection T) D.cokernelModule
      D.isQuasicoherentOnSite_cokernel_u hft]
  exact ((D.isSurjectiveAt_iff_isZero_modulePullback_cokernelModule T).trans
    (supportOfSheaf_eq_empty_iff_isZero B S hS (D.baseChangeSpace T) _).symm).trans
      (hpre.symm.trans (D.preimage_eq_empty_iff T _))

/-! ### Stacks 09TP -/

/-- **Stacks 09TP.** In the situation of Stacks 083F, assume that `f` is locally of finite
presentation, that `G` is of finite type and that the support of `G` is proper over `Y`.  Then
the locus `F_surj` on which the base change of `u` is surjective is represented by an open
subspace of `Y`; in particular it is an algebraic space and its morphism to `Y` is an open
immersion.

The open subspace is the one of Stacks 03BZ on the complement of `|f|(Supp(Coker u))`, which is
open because that image is closed by Stacks 0CZG, the support of the cokernel being a closed
subset of the support of `G` and hence proper over `Y`.  The identification at a test scheme is
`AlgebraicGeometry.Space.ModuleMapSituation.isSurjectiveAt_iff_range_pointsMap_subset`. -/
@[stacks 09TP, sga "6 XII 4.6" "partial"]
theorem exists_isOpenSubspace_isSurjectiveAt_iff
    (hf : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hG : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj D.G)) :
    ∃ U : Subfunctor D.Y.1, IsOpenSubspace B S hS U ∧
      ∀ T : D.SchemesOver,
        D.IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
          ∃ k : yoneda.obj T.left ⟶ U.toFunctor, k ≫ U.ι = T.hom.hom := by
  have hcl : IsClosed D.cokernelSupportImage :=
    D.isClosed_cokernelSupportImage
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf) hG hproper
  refine ⟨openSubspaceOfPoints B S hS D.Y.1 D.cokernelSupportImageᶜ,
    isOpenSubspace_openSubspaceOfPoints B S hS D.Y.property _ hcl.isOpen_compl,
    fun T => ?_⟩
  exact (D.isSurjectiveAt_iff_range_pointsMap_subset hG T).trans
    (exists_factor_openSubspaceOfPoints_iff B S hS (A := T.left)
      D.cokernelSupportImageᶜ T.hom.hom).symm

end ModuleMapSituation

end AlgebraicGeometry.Space

end
