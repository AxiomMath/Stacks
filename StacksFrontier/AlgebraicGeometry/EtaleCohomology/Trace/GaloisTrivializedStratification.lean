module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FlatSmoothStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.DescentModuleProjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteProjectivePullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyDescentIso
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois-trivialized stratification

Let `X` be a scheme of finite type over a perfect field `k` and `F` a constructible flat sheaf of
`Λ`-modules on the small étale site of `X`. Then `X` has a constructible stratification, whose
strata are the successive differences of a closed filtration of `X`, such that on each stratum `Z`
the sheaf `F|_Z` is the descent of a constant sheaf along a connected finite étale Galois covering
`V → Z` with a finite group `H`. Equivalently, `F|_Z` corresponds to a `Λ[H]`-module which is
finite projective over `Λ`. This is the input the dévissage of Tag 03UZ needs. Each stratum is open
in one member of the filtration with the next member as closed complement, so excision removes the
strata one at a time. On each stratum the identity is reduced to the cohomology of the Galois
covering with the group ring coefficients.

## Main results

* `AlgebraicGeometry.exists_etaleGaloisCovering_iso_descentSheaf_sheafEquiv`: a finite type locally
  constant sheaf on an irreducible geometrically unibranch object of a big étale site is, on
  Mathlib's small étale site, a descent sheaf of a finite étale Galois covering.
* `AlgebraicGeometry.exists_etaleGaloisCovering_iso_descentSheaf_of_smooth`: the Galois
  trivialization on one irreducible stratum smooth over `k`, with a finite projective module.
* `AlgebraicGeometry.exists_galoisTrivialized_stratification_of_isConstructibleFlatModuleSheaf`:
  the Galois-trivialized stratification.
* `exists_galoisTrivialized_stageStratification_of_isConstructibleFlatModuleSheaf`:
  the same, with the strata the open stages of the closed filtration.

## Implementation notes

The strata are irreducible and smooth over `k`
(`AlgebraicGeometry.exists_smooth_stratification_of_isConstructibleFlatModuleSheaf`), hence normal
and so geometrically unibranch (Stacks 0BQ3). That is the hypothesis under which
`AlgebraicGeometry.exists_etaleGaloisCovering_iso_descentSheaf` produces the Galois covering. That
statement is on Mathlib's small étale site, so the sheaf is carried there by the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`. Finite type local constancy is the same on the two sites
by Tag 093U
(`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff`).

The group of the covering lies in `Type`, so the group rings `Λ[H]` live in the coefficient
universe of `Λ`.

No `@[stacks]` attribute appears in this file: it is a step of the proof of Tag 03UZ, which the
source omits.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
* [Stacks Project, Tag 0BQ3](https://stacks.math.columbia.edu/tag/0BQ3)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u r

namespace AlgebraicGeometry

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

/-- **A finite type locally constant sheaf on an object of the big étale site is a descent
sheaf of a finite étale Galois covering.** Let `T` be an irreducible geometrically unibranch
object of a big étale site and `G` a sheaf of `Λ`-modules on the small étale site of `T` of
Tag 021B which is locally constant of finite type. Its counterpart on Mathlib's small étale site
of `T` is the descent sheaf of a finitely generated `Λ`-module with an action of a finite group
`H` along a connected finite étale Galois covering of `T` with group `H`. -/
@[sga "4½ Rapport 5.12" "partial",
  sga "4½ Th_finitude 2.2" "Clause (c), special case",
  sga "5 X 6.1" "partial"]
public theorem exists_etaleGaloisCovering_iso_descentSheaf_sheafEquiv (B : BigEtaleSite.{u})
    (T : B.Scheme) [IrreducibleSpace T.obj] (hT : IsGeometricallyUnibranch T.obj)
    (Λ : Type r) [Ring Λ]
    (G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B T.obj T.property) G) :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (C : EtaleGaloisCovering T.obj H)
      (N : Type (max (u + 1) r)) (_ : AddCommGroup N) (_ : Module Λ N)
      (ρ : H →* Module.End Λ N),
      Module.Finite Λ N ∧ IsFinite C.cover.hom ∧ ConnectedSpace C.cover.left ∧
        Nonempty ((SmallEtale.sheafEquiv B T.obj T.property
          (ModuleCat.{max (u + 1) r} Λ)).functor.obj G ≅ C.descentSheaf Λ N ρ) := by
  let E := SmallEtale.sheafEquiv B T.obj T.property (ModuleCat.{max (u + 1) r} Λ)
  have hG' : ftlcProperty T.obj Λ (E.functor.obj G) := by
    have h :=
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff
        (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology
        (SmallEtale.toEtaleSite B T.obj T.property) Λ (E.functor.obj G)).mp
    exact h (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ (E.unitIso.app G) hG)
  exact exists_etaleGaloisCovering_iso_descentSheaf hT
    (GeometricPoint.ofPoint T.obj (Classical.arbitrary T.obj)) (E.functor.obj G) hG'

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

/-- **The Galois trivialization on one smooth irreducible stratum.** Let `g : T ⟶ X` be a
morphism of the big étale site with `T` irreducible and smooth over `k`, along which the sheaf `F`
becomes locally constant with finite projective values. Read on Mathlib's small étale site of `T`,
`F|_T` is the descent sheaf of a finite projective `Λ`-module with an action of a finite group `H`
along a connected finite étale Galois covering of `T` with group `H`. -/
@[sga "4½ Rapport 5.12" "partial", sga "4½ Th_finitude 2.2" "Clause (c), special case"]
public theorem exists_etaleGaloisCovering_iso_descentSheaf_of_smooth {k : Type u} [Field k]
    (f : X.obj ⟶ Spec (.of k))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    {T : B.Scheme} (g : T ⟶ X) [IrreducibleSpace T.obj] [Smooth (B.inclusion.map g ≫ f)]
    (hP : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B T.obj T.property) (smallEtalePullObj B g F)) :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (C : EtaleGaloisCovering T.obj H)
      (N : Type (max (u + 1) r)) (_ : AddCommGroup N) (_ : Module Λ N)
      (ρ : H →* Module.End Λ N),
      Module.Finite Λ N ∧ Module.Projective Λ N ∧ IsFinite C.cover.hom ∧
        ConnectedSpace C.cover.left ∧
        Nonempty ((SmallEtale.sheafEquiv B T.obj T.property
          (ModuleCat.{max (u + 1) r} Λ)).functor.obj (smallEtalePullObj B g F) ≅
            C.descentSheaf Λ N ρ) := by
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal T.obj := isNormal_of_smooth (B.inclusion.map g ≫ f)
  have hT : IsGeometricallyUnibranch T.obj := isGeometricallyUnibranch_of_isNormal
  obtain ⟨H, _, _, C, N, _, _, ρ, hN, hfin, hconn, ⟨e⟩⟩ :=
    exists_etaleGaloisCovering_iso_descentSheaf_sheafEquiv B T hT Λ _
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteProjectiveLocallyConstant _ _
        hP)
  -- the restriction of `F` stays locally constant with finite projective values on Mathlib's site
  let E := SmallEtale.sheafEquiv B T.obj T.property (ModuleCat.{max (u + 1) r} Λ)
  have hFP : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      T.obj.smallEtaleTopology (E.functor.obj (smallEtalePullObj B g F)) :=
    (SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff B T Λ _).mp
      (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ (E.unitIso.app _) hP)
  exact ⟨H, inferInstance, inferInstance, C, N, inferInstance, inferInstance, ρ, hN,
    (C.finite_projective_of_isFiniteProjectiveLocallyConstant hT N ρ _ hFP e).2, hfin, hconn, ⟨e⟩⟩

/-- **The Galois-trivialized stratification of a constructible flat sheaf.** Let `X` be of finite
type over a perfect field `k` and `F` a constructible flat sheaf of `Λ`-modules on its small étale
site. There is a constructible stratification `s` of `X`, whose strata are the successive
differences of a closed filtration of `X`, such that each stratum `Z` is irreducible and smooth
over `k`, the restriction `F|_Z` is locally constant with finite projective values, and `F|_Z`,
read on Mathlib's small étale site of `Z`, is the descent sheaf of a finite projective `Λ`-module
with an action of a finite group `H` along a connected finite étale Galois covering of `Z` with
group `H`.

Projectivity of the module is
`AlgebraicGeometry.EtaleGaloisCovering.finite_projective_of_isFiniteProjectiveLocallyConstant`: the
descent module is one of the finite projective values of `F|_Z`. -/
public theorem exists_galoisTrivialized_stratification_of_isConstructibleFlatModuleSheaf
    {k : Type u} [Field k] [PerfectField k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    ∃ s : ConstructibleStratification B X ⊤, Nonempty s.ClosedFiltration ∧
      ∀ i, IrreducibleSpace (s.piece i).obj ∧ Smooth (B.inclusion.map (s.inclusion i) ≫ f) ∧
        Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          (smallEtalePullObj B (s.inclusion i) F) ∧
        ∃ (H : Type) (_ : Group H) (_ : Fintype H) (C : EtaleGaloisCovering (s.piece i).obj H)
          (N : Type (max (u + 1) r)) (_ : AddCommGroup N) (_ : Module Λ N)
          (ρ : H →* Module.End Λ N),
          Module.Finite Λ N ∧ Module.Projective Λ N ∧ IsFinite C.cover.hom ∧
            ConnectedSpace C.cover.left ∧
            Nonempty ((SmallEtale.sheafEquiv B (s.piece i).obj (s.piece i).property
              (ModuleCat.{max (u + 1) r} Λ)).functor.obj (smallEtalePullObj B (s.inclusion i) F) ≅
                C.descentSheaf Λ N ρ) := by
  obtain ⟨s, hirr, hsm, hP, hfil⟩ :=
    exists_smooth_stratification_of_isConstructibleFlatModuleSheaf B X Λ f hF
  refine ⟨s, hfil, fun i => ⟨hirr i, hsm i, hP i, ?_⟩⟩
  have := hirr i
  have := hsm i
  exact exists_etaleGaloisCovering_iso_descentSheaf_of_smooth B X Λ f F (s.inclusion i) (hP i)

/-- **The Galois-trivialized stratification, on the stages of the closed filtration.** The same
statement as `exists_galoisTrivialized_stratification_of_isConstructibleFlatModuleSheaf`, with each
stratum taken to be the open complement `Φ.stageOpenObj i` of the `(i + 1)`-th member of the closed
filtration in the `i`-th, included in `X` by `Φ.stageOpenInclusion i ≫ Φ.stageInclusion i`. These
are the strata of `Φ.toStageStratification`, definitionally, and `Φ.toStageFiltration` is the
closed filtration of that stratification. So the excision sequence of the open stage in the `i`-th
member of the filtration and its closed complement lands on the strata themselves. -/
public theorem exists_galoisTrivialized_stageStratification_of_isConstructibleFlatModuleSheaf
    {k : Type u} [Field k] [PerfectField k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    ∃ (s : ConstructibleStratification B X ⊤) (Φ : s.ClosedFiltration), ∀ i : Fin s.n,
      IrreducibleSpace (Φ.stageOpenObj i).obj ∧
      Smooth (B.inclusion.map (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) ≫ f) ∧
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B (Φ.stageOpenObj i).obj (Φ.stageOpenObj i).property)
        (smallEtalePullObj B (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) F) ∧
      ∃ (H : Type) (_ : Group H) (_ : Fintype H)
        (C : EtaleGaloisCovering (Φ.stageOpenObj i).obj H)
        (N : Type (max (u + 1) r)) (_ : AddCommGroup N) (_ : Module Λ N)
        (ρ : H →* Module.End Λ N),
        Module.Finite Λ N ∧ Module.Projective Λ N ∧ IsFinite C.cover.hom ∧
          ConnectedSpace C.cover.left ∧
          Nonempty ((SmallEtale.sheafEquiv B (Φ.stageOpenObj i).obj (Φ.stageOpenObj i).property
            (ModuleCat.{max (u + 1) r} Λ)).functor.obj
              (smallEtalePullObj B (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) F) ≅
              C.descentSheaf Λ N ρ) := by
  obtain ⟨s, hirr, hsm, hP, ⟨Φ⟩⟩ :=
    exists_smooth_stratification_of_isConstructibleFlatModuleSheaf B X Λ f hF
  refine ⟨s, Φ, fun i => ?_⟩
  obtain ⟨e, he⟩ := Φ.exists_pieceIso_stageOpenObj i
  have hι : Φ.stageOpenInclusion i ≫ Φ.stageInclusion i = e.inv ≫ s.inclusion i := by
    rw [← he, Iso.inv_hom_id_assoc]
  have := hsm i
  have : IrreducibleSpace (B.inclusion.obj (s.piece i)) := hirr i
  have : IrreducibleSpace (Φ.stageOpenObj i).obj :=
    (Scheme.homeoOfIso (B.inclusion.mapIso e)).surjective.irreducibleSpace
      (Scheme.homeoOfIso (B.inclusion.mapIso e)).continuous
  have : Smooth (B.inclusion.map (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) ≫ f) := by
    rw [hι, Functor.map_comp, Category.assoc]
    infer_instance
  have hP' : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B (Φ.stageOpenObj i).obj (Φ.stageOpenObj i).property)
      (smallEtalePullObj B (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) F) := by
    rw [hι]
    exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _
      ((smallEtaleSheafPullbackCompIso B _ _ _ e.inv (s.inclusion i) _).app F)
      (isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ e.inv _ (hP i))
  exact ⟨inferInstance, inferInstance, hP',
    exists_etaleGaloisCovering_iso_descentSheaf_of_smooth B X Λ f F _ hP'⟩

end AlgebraicGeometry

end
