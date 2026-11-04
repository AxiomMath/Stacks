module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldLift
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Points of a fibre over a large algebraically closed field

Let `X` be an algebraic space over a scheme `S` and let `s̄ : Spec k → S` be a geometric point
of `S` whose field is larger than the cardinal `λ` of a scheme atlas of `X`. Every point of
the fibre `X_s = Spec κ(s) ×_S X` is then represented by a `k`-valued point of `X` lying over
`s̄`.

## Main definitions

* `AlgebraicGeometry.Space.baseSiteObject` is the terminal object `S` of the big fppf site
  over `S`, and `AlgebraicGeometry.Space.residueSiteObject` is `Spec κ(s)` as an object of
  that site.
* `AlgebraicGeometry.Space.fibrePointOfFieldPoint` is the map `X(k) → |X_s|`.

## Main results

* `AlgebraicGeometry.Space.surjective_fibrePointOfFieldPoint` is Stacks 0488 part (3).

## Implementation notes

The fibre `X_s = Spec κ(s) ×_S X` is a fibre product over the base scheme `S`, which is the
terminal object of the big fppf site over `S`; so it is presented here as an arbitrary
cartesian square over that terminal object, exactly as Tag 03H4 is presented in
`AlgebraicGeometry.Space.exists_points_of_isPullback`. The instance at the categorical
pullback is
`AlgebraicGeometry.Space.surjective_fibrePointOfFieldPoint_pullback`.

The map `X(k) → |X_s|` pairs a `k`-valued point of `X` with the factorisation of `s̄` through
`Spec κ(s)`; the two agree over `S` because `S` is terminal.

Following the source, part (3) is deduced from part (4),
`AlgebraicGeometry.Space.exists_lift_of_large_field`, applied to the structure morphism
`X → S`: a point of `X_s` maps to a point of `X` lying over `s`, part (4) represents the
latter by a `k`-valued point over `s̄`, and the resulting point of `X_s` agrees with the
given one because `X_s → X` is a monomorphism, being a base change of the monomorphism
`Spec κ(s) → S`.

## References

* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The base and the residue field spectrum as objects of the site -/

/-- The base scheme `S`, viewed as the terminal object of the big fppf site over `S`. -/
abbrev baseSiteObject : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The structure morphism of an object of the big fppf site over `S`, read as a morphism to
the terminal object. -/
def toBaseSiteObject (W : BigFppfOver B S hS) : W ⟶ baseSiteObject B S hS :=
  Over.homMk W.hom (by simp)

/-- The presheaf represented by the base scheme is terminal: a section of any presheaf over
an object `W` of the site can only be sent to the structure morphism of `W`. -/
noncomputable def isTerminal_yoneda_baseSiteObject :
    IsTerminal (yoneda.obj (baseSiteObject B S hS) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda (baseSiteObject B S hS)

/-- The unique morphism from a presheaf on the big fppf site over `S` to the presheaf
represented by the base scheme `S`. -/
noncomputable def toBaseSiteMap (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    F ⟶ yoneda.obj (baseSiteObject B S hS) :=
  (isTerminal_yoneda_baseSiteObject B S hS).from F

/-- `Spec κ(s)`, for `s` a point of the base scheme, as an object of the big fppf site
over `S`. -/
noncomputable def residueSiteObject (s : S) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.residueField_spec_contains hS s) (S.fromSpecResidueField s)

/-- The structure morphism of `Spec κ(s)` to the terminal object of the big fppf site over
`S` is a monomorphism, because `Spec κ(s) → S` is. -/
theorem mono_toBaseSiteObject_residueSiteObject (s : S) :
    Mono (toBaseSiteObject B S hS (residueSiteObject B S hS s)) := by
  have hmono : Mono (S.fromSpecResidueField s) := inferInstance
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono

/-- A morphism `Spec k ⟶ S` from the spectrum of a field of the site whose set-theoretic
image is the point `s` factors through `Spec κ(s)`; this is the resulting morphism of the
site. -/
noncomputable def residueFactor {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S) (s : S) (hs : ∀ y, b y = s) :
    (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ residueSiteObject B S hS s :=
  BigFppfOver.homMk B S hS (B.residueField_spec_contains hS s) (S.fromSpecResidueField s)
    (Spec.map (exists_residueFieldHom_comp_fromSpecResidueField b s hs).choose)
    (exists_residueFieldHom_comp_fromSpecResidueField b s hs).choose_spec

/-- The point set of the presheaf represented by `Spec κ(s)` has at most one element. -/
theorem subsingleton_points_yoneda_residueSiteObject (s : S) :
    Subsingleton (points B S hS (yoneda.obj (residueSiteObject B S hS s))) := by
  have hsub : Subsingleton (Spec (S.residueField s)) := inferInstance
  exact @Equiv.subsingleton _ _
    (pointsEquivScheme B S hS (residueSiteObject B S hS s)) hsub

/-! ### The map from the field-valued points to the points of the fibre -/

/-- **Stacks 0488, part (3).** The map `X(k) → |X_s|`: a `k`-valued point of `X` over the
geometric point `s̄` of `S`, paired with the factorisation of `s̄` through `Spec κ(s)`, is a
`k`-valued point of the fibre `X_s`, hence a point of `X_s`. -/
noncomputable def fibrePointOfFieldPoint
    {X Xs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (s : S) (hs : ∀ y, b y = s)
    (pr : Xs ⟶ X) (pr' : Xs ⟶ yoneda.obj (residueSiteObject B S hS s))
    (hpb : IsPullback pr pr' (toBaseSiteMap B S hS X)
      (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s))))
    (z : X.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))) :
    points B S hS Xs :=
  (⟨k, hk, b, yonedaEquiv (hpb.lift (yonedaEquiv.symm z)
      (yoneda.map (residueFactor B S hS hk b s hs))
      ((isTerminal_yoneda_baseSiteObject B S hS).hom_ext _ _))⟩ :
    FieldValuedPoint B S hS Xs).class B S hS Xs

/-- The point of `X` underlying the point of the fibre attached to a `k`-valued point of `X`
is the point of `X` that the `k`-valued point represents. -/
theorem pointsMap_fibrePointOfFieldPoint
    {X Xs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (s : S) (hs : ∀ y, b y = s)
    (pr : Xs ⟶ X) (pr' : Xs ⟶ yoneda.obj (residueSiteObject B S hS s))
    (hpb : IsPullback pr pr' (toBaseSiteMap B S hS X)
      (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s))))
    (z : X.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))) :
    pointsMap B S hS Xs pr
        (fibrePointOfFieldPoint B S hS hk b s hs pr pr' hpb z) =
      (⟨k, hk, b, z⟩ : FieldValuedPoint B S hS X).class B S hS X := by
  rw [fibrePointOfFieldPoint, pointsMap_class]
  congr 1
  refine congrArg (fun w => (⟨k, hk, b, w⟩ : FieldValuedPoint B S hS X)) ?_
  show pr.app _ (yonedaEquiv (hpb.lift _ _ _)) = z
  rw [← yonedaEquiv_comp, hpb.lift_fst, Equiv.apply_symm_apply]

/-- **Stacks 0488, part (3).** For any geometric point `s̄ : Spec k → S` whose field has
cardinality `> λ(X)` the map `X(k) → |X_s|` is surjective, where `X_s = Spec κ(s) ×_S X`
and `s ∈ S` is the point corresponding to `s̄`.

Following the source, `λ(X)` is read off from a chosen scheme atlas `U → X`, carried along
as an explicit parameter; the fibre `X_s` is presented as an arbitrary cartesian square over
the terminal object `S` of the site. -/
theorem surjective_fibrePointOfFieldPoint
    {X Xs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X)
    (hp_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hp_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (hlarge : ((BigFppfOver.toScheme B S hS).obj U).lambdaCard < Cardinal.mk k)
    (s : S) (hs : ∀ y, b y = s)
    (pr : Xs ⟶ X) (pr' : Xs ⟶ yoneda.obj (residueSiteObject B S hS s))
    (hpb : IsPullback pr pr' (toBaseSiteMap B S hS X)
      (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s)))) :
    Function.Surjective (fibrePointOfFieldPoint B S hS hk b s hs pr pr' hpb) := by
  classical
  intro ξ
  have hsub := subsingleton_points_yoneda_residueSiteObject B S hS s
  have hmonoY : Mono (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s))) :=
    haveI := mono_toBaseSiteObject_residueSiteObject B S hS s
    inferInstance
  have hmonoPr : Mono pr :=
    PullbackCone.mono_fst_of_is_pullback_of_mono hpb.isLimit
  -- The image of `ξ` in `|X|` lies over the geometric point `s̄` of the base.
  have hpr' : pointsMap B S hS Xs pr' ξ =
      (⟨k, hk, b, residueFactor B S hS hk b s hs⟩ :
          FieldValuedPoint B S hS (yoneda.obj (residueSiteObject B S hS s))).class B S hS _ :=
    Subsingleton.elim _ _
  have hxy : pointsMap B S hS X (toBaseSiteMap B S hS X) (pointsMap B S hS Xs pr ξ) =
      (⟨k, hk, b, toBaseSiteObject B S hS (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))⟩ :
          FieldValuedPoint B S hS (yoneda.obj (baseSiteObject B S hS))).class B S hS _ := by
    rw [← pointsMap_comp_apply, hpb.w, pointsMap_comp_apply, hpr', pointsMap_class]
    refine congrArg (fun w => FieldValuedPoint.class B S hS _
      (⟨k, hk, b, w⟩ : FieldValuedPoint B S hS (yoneda.obj (baseSiteObject B S hS)))) ?_
    exact Over.mkIdTerminal.hom_ext _ _
  obtain ⟨z, -, hz_class⟩ :=
    exists_lift_of_large_field B S hS hX
      (isAlgebraicSpace_yoneda B S hS (baseSiteObject B S hS)) (toBaseSiteMap B S hS X)
      U p hp_surjective hp_etale k hk b hlarge (pointsMap B S hS Xs pr ξ) _ hxy
  refine ⟨z, pointsMap_injective_of_mono B S hS pr ?_⟩
  rw [pointsMap_fibrePointOfFieldPoint, hz_class]

/-- **Stacks 0488, part (3)** at the categorical fibre product. The instance of
`AlgebraicGeometry.Space.surjective_fibrePointOfFieldPoint` at the fibre product
`Spec κ(s) ×_S X` formed in the presheaf category. -/
theorem surjective_fibrePointOfFieldPoint_pullback
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X)
    (hp_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hp_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (hlarge : ((BigFppfOver.toScheme B S hS).obj U).lambdaCard < Cardinal.mk k)
    (s : S) (hs : ∀ y, b y = s) :
    Function.Surjective (fibrePointOfFieldPoint B S hS hk b s hs
      (pullback.fst (toBaseSiteMap B S hS X)
        (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s))))
      (pullback.snd (toBaseSiteMap B S hS X)
        (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s))))
      (IsPullback.of_hasPullback _ _)) :=
  surjective_fibrePointOfFieldPoint B S hS hX U p hp_surjective hp_etale k hk b hlarge s hs
    _ _ (IsPullback.of_hasPullback _ _)

end AlgebraicGeometry.Space

end
