module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageConeLimitOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties

/-!
# Quasi-separatedness of the image system of a good diagram, with no bound on the index type

The limit of a Noetherian limit system is quasi-separated, and so are the members of the system
of scheme-theoretic images of a good diagram with quasi-separated source, with no bound on the
size of the index type: the projections of the limit are affine because the limit is an
algebraic space (Stacks 07SF, part (1)).

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_limitCone_pt_of_algebraicLimit`: the limit
  of a Noetherian limit system is quasi-separated.
* `GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit` and
  `GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit`
  (in the namespace `AlgebraicGeometry.Space`): the members `X_{i'}` of the image system are
  quasi-separated.

The forms carrying the bound `#I < B.cutoff.ord.cof` are in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties`.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section SiteIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I]

/-- **The limit of a directed inverse system of Noetherian algebraic spaces with affine
transition morphisms is quasi-separated.** Its projection to a stage is affine, hence
quasi-separated, and that stage is Noetherian, hence quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_limitCone_pt_of_algebraicLimit
    (D : NoetherianLimitSystem B S hS hZ I) :
    IsAbsolutelyQuasiSeparated B S hS hZ D.limitCone.pt := by
  obtain ⟨i⟩ : Nonempty I := inferInstance
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ D.limit_isAlgebraicSpace
    (D.noetherian i).2.1
    (isQuasiSeparated_of_isAffineHom B S hS (D.limitCone.π.app (op i))
      D.limit_isAlgebraicSpace (D.system_isAlgebraicSpace i)
      (isAffineHom_limitCone_π_of_algebraicLimit B S hS D (op i)))

/-- **An algebraic space quasi-separated over the limit of a directed inverse system of
Noetherian algebraic spaces with affine transition morphisms is quasi-separated.** The limit
is quasi-separated, so this is Stacks 04ZH, part (2). -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone_of_algebraicLimit
    {D : NoetherianLimitSystem B S hS hZ I} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ D.limitCone.pt} (hf : IsQuasiSeparated B S hS f) :
    IsAbsolutelyQuasiSeparated B S hS hZ X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX
    (isAbsolutelyQuasiSeparated_limitCone_pt_of_algebraicLimit D) hf

end SiteIndex

namespace GoodDiagram

section SiteIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}
    (G : GoodDiagram B S hS hZ D f)

/-- **The points of codimension zero of a member `X_{i'}` of the system of scheme-theoretic
images of a good diagram with quasi-separated source are represented by monomorphisms from
spectra of fields.** The stage map `X ⟶ B_{i'} ×_{B_i} W` is quasi-compact, so by Stacks 089B
its scheme-theoretic image `X_{i'}` receives a field-valued point of `X` above any point of
codimension zero; the morphism representing it is `Spec k ⟶ X ⟶ X_{i'}`, which is
quasi-compact because `X` is quasi-separated and `Spec k` is affine, and a point with a
quasi-compact field-valued representative has a monomorphic one by Stacks 03JV. -/
theorem imageSystem_hasMonomorphicCodimensionZeroPoints_of_algebraicLimit
    (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (j : Over (op G.index)) :
    HasMonomorphicCodimensionZeroPoints B S hS ((imageSystem G).obj j) := by
  intro z hz
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_toSchemeTheoreticImage_of_localRingDimension_eq_zero
    B S hS (stageMap G j) hX (isAlgebraicSpace_stageTarget G j)
    (isQuasiCompact_stageMap_of_algebraicLimit G j) z hz
  have hqcp : IsQuasiCompact B S hS (fieldMorphism B S hS X p) :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS (hZ := hZ) hX hqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS (p.siteObject B S hS X)
        ((inferInstance : IsAffine (Spec (CommRingCat.of p.carrier)))))
      (fieldMorphism B S hS X p)
  have hqci : IsQuasiCompact B S hS (toSchemeTheoreticImage B S hS (stageMap G j)) :=
    isQuasiCompact_of_comp_mono B S hS _ _
      (by rw [toSchemeTheoreticImage_ι]; exact isQuasiCompact_stageMap_of_algebraicLimit G j)
  refine (hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative
      B S hS _ (imageSystem_isAlgebraicSpace G j)
      ⟨FieldValuedPoint.map B S hS X (toSchemeTheoreticImage B S hS (stageMap G j)) p, ?_,
        ?_⟩).hasMonomorphicFieldRepresentative B S hS _
  · rw [← pointsMap_class]
    exact hp
  · rw [fieldMorphism_map]
    exact isQuasiCompact_comp B S hS hX (imageSystem_isAlgebraicSpace G j) _ _ hqcp hqci

/-- **A member `X_{i'}` of the system of scheme-theoretic images of a good diagram with
quasi-separated source is quasi-separated.** The points of `X_{i'}` of codimension zero are
represented by monomorphisms from spectra of fields, so Stacks 0BB8 makes `X_{i'}` reasonable,
hence decent, and Stacks 0BB6 applies. -/
theorem imageSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit
    (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (j : Over (op G.index)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((imageSystem G).obj j) :=
  imageSystem_isAbsolutelyQuasiSeparated_of_mono G j
    (imageSystem_hasMonomorphicCodimensionZeroPoints_of_algebraicLimit G hX hqs j)

/-- **A member `X_{i'}` of the system of scheme-theoretic images of a good diagram whose
source is quasi-separated over the limit is quasi-separated.** The limit is quasi-separated,
so the source is, and
`AlgebraicGeometry.Space.GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit`
applies. This is the hypothesis under which Stacks 0CP7 produces a good diagram. -/
theorem imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_algebraicLimit
    (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsQuasiSeparated B S hS f) (j : Over (op G.index)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((imageSystem G).obj j) :=
  imageSystem_isAbsolutelyQuasiSeparated_of_algebraicLimit G hX
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone_of_algebraicLimit hX hqs) j

end SiteIndex

end GoodDiagram

end AlgebraicGeometry.Space

end
