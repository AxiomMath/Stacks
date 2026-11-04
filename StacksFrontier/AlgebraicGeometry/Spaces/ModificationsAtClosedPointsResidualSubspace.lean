module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

/-!
# The residual subspace at a chosen closed point and the fibre of its neighborhood

Let `f : V ⟶ X` be an étale morphism of algebraic spaces over `S` and let `ρ : Spec(k) ⟶ V` be a
morphism from the spectrum of a field for which `ρ ≫ f` is a monomorphism. Write `T ⊆ X` for the
image of `ρ ≫ f`, a subspace carried by the single point `x` that `ρ ≫ f` hits. If `ρ` already
accounts for every point of `V` above `x`, then `f` carries the inverse image `f⁻¹T`
isomorphically onto `T`.

For a `ClosedPointNeighborhoods` datum this applies to `Uᵢ ⟶ X` and the residue-field point of
the distinguished point `uᵢ`, and produces the second standing hypothesis of Stacks 0BGY at the
pair `(Uᵢ ⟶ X, {xᵢ})`.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.residualObject`,
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.residualToNeighborhood` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.residualToSpace` are the residue-field point
  `Spec κ(uᵢ)` of the distinguished point of the `i`th chosen neighborhood and its canonical
  morphisms into that neighborhood and into the space.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.pointSubspace` is the subspace `{xᵢ}`, namely
  the image of `Spec κ(uᵢ) ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.isIso_fromPreimage_range_of_isEtale`: the general statement, for an
  étale morphism and a monomorphic field-valued point of its target which exhausts the fibre.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.pointSubspace_eq_range` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.range_pointsMap_ι_pointSubspace`: the
  subspace `{xᵢ}` is the image of `Spec κ(uᵢ) ⟶ X`, and its point set is `{xᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_fromPreimage_pointSubspace`: the
  morphism `Uᵢ ⟶ X` carries `f⁻¹{xᵢ}` isomorphically onto `{xᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.pointsMap_residualToSpace`,
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.subsingleton_points_residualObject` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_points_residualObject`: the point
  set of `Spec κ(uᵢ)` is a singleton, and its point is carried to `xᵢ`. These are not private to
  this module because
  `StacksFrontier/AlgebraicGeometry/Spaces/ModificationsAtClosedPointsResidualSpace.lean` reads the
  two point-set clauses of `AlgebraicGeometry.Space.IsResidualSpaceAt` off them.

## Implementation notes

The inverse image `f⁻¹T` is the fibre product `T ×_X V` by
`CategoryTheory.Subfunctor.isPullback_fromPreimage`, so the assertion is that the projection
`T ×_X V ⟶ T` is an isomorphism. It is a split epimorphism: `ρ` lands in `f⁻¹T` because
`ρ ≫ f` lands in its own image, and the resulting section `Spec(k) ⟶ T ×_X V` composed with the
projection is the isomorphism `Spec(k) ≅ T` coming from `ρ ≫ f` being a monomorphism. So it is
enough to prove that section an isomorphism, and that is Stacks 06QY: the section is a
monomorphism, and `T ×_X V` is reduced, locally Noetherian and carries exactly one point.

Reducedness and local Noetherianity of `T ×_X V` come from `T ≅ Spec(k)` through
`AlgebraicGeometry.Space.hasEtaleLocalProperty_of_representable` and the étaleness of the
projection, the two properties being étale-local on schemes. That the point set is a singleton is
where the hypothesis on the fibre of `f` is used: the other projection `T ×_X V ⟶ V` is a
monomorphism, being a base change of the monomorphism `T ⟶ X`, so the point set of `T ×_X V`
injects into that of `V`, and every point of `V` in the image lies above `x`, hence is the image
of the point of `Spec(k)`.

The subspace `{xᵢ}` is realized as the image of the residue-field point of `uᵢ`, not as
`AlgebraicGeometry.Space.reducedClosedSubspace` on `{xᵢ}`. The two are not identified here:
`AlgebraicGeometry.Space.eq_reducedClosedSubspace` would ask in addition for the inclusion of the
image to be a closed immersion, and the only route to that in this library,
`AlgebraicGeometry.Space.isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt`, assumes
the ambient space locally Noetherian, which a `ClosedPointNeighborhoods` datum does not record.
What is proved about the image instead is that its point set is `{xᵢ}`, which is what fixes its
open complement to be `X ∖ {xᵢ}`.

Nothing in this file is a statement of the Stacks project in its own right, so nothing carries a
tag: it is infrastructure inside the instantiation of Stacks 0BGY used by Stacks 0BHB.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 06QX](https://stacks.math.columbia.edu/tag/06QX)
* [Stacks Project, Tag 06QY](https://stacks.math.columbia.edu/tag/06QY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section General

variable {V X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R : BigFppfOver B S hS}

/-- **An étale morphism is an isomorphism over a monomorphic field-valued point of its target
whose fibre it exhausts.** Let `f : V ⟶ X` be an étale morphism of algebraic spaces over `S` and
let `ρ : Spec(k) ⟶ V` be a morphism from the spectrum of a field, reduced and locally Noetherian
with a single point, such that `ρ ≫ f` is a monomorphism and every point of `V` above the point
hit by `ρ ≫ f` is the image of the point of `Spec(k)`. Then `f` carries the inverse image of the
image of `ρ ≫ f` isomorphically onto that image. -/
theorem isIso_fromPreimage_range_of_isEtale (hV : IsAlgebraicSpace B S hS V)
    (hX : IsAlgebraicSpace B S hS X) (f : V ⟶ X) (hf : IsEtale B S hS f)
    (hred : IsReduced ((BigFppfOver.toScheme B S hS).obj R))
    (hnoe : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R))
    (hsub : Subsingleton (points B S hS (yoneda.obj R)))
    (hne : Nonempty (points B S hS (yoneda.obj R)))
    (ρ : yoneda.obj R ⟶ V) (hmono : Mono (ρ ≫ f))
    (hfib : ∀ (w : points B S hS V) (z : points B S hS (yoneda.obj R)),
      pointsMap B S hS V f w = pointsMap B S hS (yoneda.obj R) (ρ ≫ f) z →
        w = pointsMap B S hS (yoneda.obj R) ρ z) :
    IsIso ((Subfunctor.range (ρ ≫ f)).fromPreimage f) := by
  set T : Subfunctor X := Subfunctor.range (ρ ≫ f)
  set l : yoneda.obj R ⟶ T.toFunctor := Subfunctor.toRange (ρ ≫ f) with hldef
  have hliso : IsIso l := by
    rw [hldef]
    infer_instance
  have hlι : l ≫ T.ι = ρ ≫ f := Subfunctor.toRange_ι (ρ ≫ f)
  have hT : IsAlgebraicSpace B S hS T.toFunctor :=
    (isAlgebraicSpace_yoneda B S hS R).of_iso (asIso l)
  have hW : IsAlgebraicSpace B S hS (pullback T.ι f) :=
    isAlgebraicSpace_pullback B S hS T.ι f hT hV hX
  have hfst : IsEtale B S hS (pullback.fst T.ι f) :=
    isEtale_pullback_fst B S hS hT hX hV T.ι f hf
  set σ : yoneda.obj R ⟶ pullback T.ι f := pullback.lift l ρ hlι
  have hσfst : σ ≫ pullback.fst T.ι f = l := pullback.lift_fst _ _ _
  have hσmono : Mono σ := mono_of_mono_fac hσfst
  have hWloc : ∀ (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage],
      P ((BigFppfOver.toScheme B S hS).obj R) → HasEtaleLocalProperty B S hS (pullback T.ι f) P :=
    fun P _ h => hasEtaleLocalProperty_of_isEtale B S hS hW hT hfst
      (hasEtaleLocalProperty_of_representable B S hS T.toFunctor P R (asIso l).symm h)
  have hWred := hWloc (fun Y : Scheme.{u} => IsReduced Y) hred
  have hWnoe := hWloc (fun Y : Scheme.{u} => IsLocallyNoetherian Y) hnoe
  have hWne : Nonempty (points B S hS (pullback T.ι f)) :=
    ⟨pointsMap B S hS (yoneda.obj R) σ hne.some⟩
  have key : ∀ c : points B S hS (pullback T.ι f),
      pointsMap B S hS (pullback T.ι f) (pullback.snd T.ι f) c =
        pointsMap B S hS (yoneda.obj R) ρ hne.some := by
    intro c
    obtain ⟨z, hz⟩ := pointsMap_surjective_of_isIso B S hS l
      (pointsMap B S hS (pullback T.ι f) (pullback.fst T.ι f) c)
    refine (hfib _ z ?_).trans (congrArg _ (hsub.elim z hne.some))
    rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply, ← hz,
      ← pointsMap_comp_apply, hlι]
  have hWsub : Subsingleton (points B S hS (pullback T.ι f)) :=
    ⟨fun a b => pointsMap_injective_of_mono B S hS (pullback.snd T.ι f)
      ((key a).trans (key b).symm)⟩
  -- Stacks 06QX and 06QY
  have hcover : HasLocallyOfFinitePresentationFlatFieldCover B S hS (pullback T.ι f) :=
    (isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover B S hS
      (pullback T.ι f) hW).1 ⟨hWred, hWnoe, hWne, hWsub⟩
  have hσiso : IsIso σ := by
    rcases isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover B S hS
      (isAlgebraicSpace_yoneda B S hS R) hW σ hcover with hempty | hiso
    · exact (hempty.false hne.some).elim
    · exact hiso
  have hfstiso : IsIso (pullback.fst T.ι f) := IsIso.of_isIso_fac_left hσfst
  have hfac := (Subfunctor.isPullback_fromPreimage T f).isoPullback_hom_fst
  rw [← hfac]
  infer_instance

end General

namespace ClosedPointNeighborhoods

variable {B S hS} {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The residue-field point of the distinguished point of the `i`th chosen neighborhood, as an
object of the big fppf site over `S`. -/
abbrev residualObject (i : Fin n) : BigFppfOver B S hS :=
  residueFieldObject B S hS (D.neighborhood i).scheme (D.neighborhood i).point
    (D.neighborhood i).residueField_contained

/-- The canonical morphism from the residue-field point of the distinguished point of the `i`th
chosen neighborhood into that neighborhood. -/
abbrev residualToNeighborhood (i : Fin n) :
    yoneda.obj (D.residualObject i) ⟶ (D.neighborhoodSpace i).obj :=
  yoneda.map (residueFieldMap B S hS (D.neighborhood i).scheme (D.neighborhood i).point
    (D.neighborhood i).residueField_contained)

/-- The canonical morphism `Spec κ(uᵢ) ⟶ X` from the residue-field point of the distinguished
point of the `i`th chosen neighborhood into the space. -/
abbrev residualToSpace (i : Fin n) : yoneda.obj (D.residualObject i) ⟶ D.space.obj :=
  D.residualToNeighborhood i ≫ (D.toSpaceHom i).hom

/-- The subspace `{xᵢ}` of `X`: the image of the residue-field point of the distinguished point
of the `i`th chosen neighborhood. -/
def pointSubspace (i : Fin n) : Subfunctor D.space.obj :=
  Subfunctor.range (D.residualToSpace i)

/-- The subspace `{xᵢ}` is by definition the image of the canonical morphism
`Spec κ(uᵢ) ⟶ X`. -/
theorem pointSubspace_eq_range (i : Fin n) :
    D.pointSubspace i = Subfunctor.range (D.residualToSpace i) := rfl

/-- The residue-field point of the distinguished point of the `i`th chosen neighborhood, as a
field-valued point of that neighborhood. -/
private def residualPoint (i : Fin n) :
    FieldValuedPoint B S hS (yoneda.obj (D.neighborhood i).scheme) :=
  ⟨(D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point,
    (D.neighborhood i).residueField_contained,
    (D.neighborhood i).scheme.left.1.fromSpecResidueField (D.neighborhood i).point ≫
      (D.neighborhood i).scheme.hom.1,
    residueFieldMap B S hS (D.neighborhood i).scheme (D.neighborhood i).point
      (D.neighborhood i).residueField_contained⟩

/-- Every point of the residue-field point of the distinguished point of the `i`th chosen
neighborhood is carried to that distinguished point. -/
private theorem pointsMap_residualToNeighborhood (i : Fin n)
    (z : points B S hS (yoneda.obj (D.residualObject i))) :
    pointsMap B S hS (yoneda.obj (D.residualObject i)) (D.residualToNeighborhood i) z =
      D.neighborhoodPoint i := by
  have hval : yonedaEquiv.symm (D.residualPoint i).value = D.residualToNeighborhood i :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
  have h := FieldValuedPoint.pointsMap_eq_class B S hS (D.residualPoint i) z
  rwa [hval] at h

/-- Every point of the residue-field point of the distinguished point of the `i`th chosen
neighborhood is carried to the `i`th chosen point of the space. -/
theorem pointsMap_residualToSpace (i : Fin n)
    (z : points B S hS (yoneda.obj (D.residualObject i))) :
    pointsMap B S hS (yoneda.obj (D.residualObject i)) (D.residualToSpace i) z = D.point i := by
  rw [residualToSpace, pointsMap_comp_apply, D.pointsMap_residualToNeighborhood i]
  exact (D.neighborhood i).map_point

/-- The point set of the residue-field point of the distinguished point of the `i`th chosen
neighborhood is a subsingleton: it is the spectrum of a field. -/
theorem subsingleton_points_residualObject (i : Fin n) :
    Subsingleton (points B S hS (yoneda.obj (D.residualObject i))) :=
  subsingleton_points_yoneda_siteObject B S hS (D.residualPoint i)

/-- The point set of the residue-field point of the distinguished point of the `i`th chosen
neighborhood is nonempty. -/
theorem nonempty_points_residualObject (i : Fin n) :
    Nonempty (points B S hS (yoneda.obj (D.residualObject i))) :=
  ⟨(FieldValuedPoint.tautological B S hS (D.residualPoint i)).class B S hS _⟩

/-- **The subspace `{xᵢ}` has point set `{xᵢ}`.** Its inclusion is, up to the isomorphism
exhibiting it as the image of a monomorphism, the canonical morphism `Spec κ(uᵢ) ⟶ X`, and every
point of `Spec κ(uᵢ)` is carried to `xᵢ`. -/
theorem range_pointsMap_ι_pointSubspace (i : Fin n) :
    Set.range (pointsMap B S hS (D.pointSubspace i).toFunctor (D.pointSubspace i).ι) =
      {D.point i} := by
  have : Mono (D.residualToSpace i) := (D.neighborhood i).mono_residueField
  rw [D.pointSubspace_eq_range i]
  have hlι : Subfunctor.toRange (D.residualToSpace i) ≫
      (Subfunctor.range (D.residualToSpace i)).ι = D.residualToSpace i :=
    Subfunctor.toRange_ι _
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz⟩ := pointsMap_surjective_of_isIso B S hS
      (Subfunctor.toRange (D.residualToSpace i)) t
    rw [← hz, ← pointsMap_comp_apply, hlι]
    exact Set.mem_singleton_iff.2 (D.pointsMap_residualToSpace i z)
  · rintro _ rfl
    refine ⟨pointsMap B S hS (yoneda.obj (D.residualObject i))
      (Subfunctor.toRange (D.residualToSpace i))
      (D.nonempty_points_residualObject i).some, ?_⟩
    rw [← pointsMap_comp_apply, hlι, D.pointsMap_residualToSpace i]

/-- **The second standing hypothesis of Stacks 0BGY at `(Uᵢ ⟶ X, {xᵢ})`.** The étale morphism
`Uᵢ ⟶ X` carries the inverse image of the subspace `{xᵢ}` isomorphically onto it: the fibre of
`Uᵢ ⟶ X` over `xᵢ` is the single point `uᵢ` with residue field the residue field at `xᵢ`. -/
theorem isIso_fromPreimage_pointSubspace (i : Fin n) :
    IsIso ((D.pointSubspace i).fromPreimage (D.toSpaceHom i).hom) := by
  have hmono : Mono (D.residualToNeighborhood i ≫ (D.toSpaceHom i).hom) :=
    (D.neighborhood i).mono_residueField
  rw [D.pointSubspace_eq_range i]
  refine isIso_fromPreimage_range_of_isEtale B S hS (D.neighborhoodSpace i).property
    D.space.property (D.toSpaceHom i).hom (D.neighborhood i).etale_toSpace ?_ ?_
    (D.subsingleton_points_residualObject i) (D.nonempty_points_residualObject i)
    (D.residualToNeighborhood i) hmono ?_
  · exact inferInstanceAs (IsReduced
      (Spec (.of ((D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point))))
  · exact inferInstanceAs (IsLocallyNoetherian
      (Spec (.of ((D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point))))
  · intro w z hw
    rw [D.pointsMap_residualToSpace i z] at hw
    rw [D.pointsMap_residualToNeighborhood i z]
    exact D.eq_of_map_eq_point i w hw

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
