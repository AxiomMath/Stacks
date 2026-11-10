module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverFiberPoints
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceStalkInjectivity

/-!
# Covariance on the stalk decomposition of the direct image with compact support

Let `j : X' ⟶ X` be an open immersion and let `f : X ⟶ Y` be locally of finite type and locally
quasi-finite in a big étale site. On the stalk decompositions

`((j ≫ f)_!(F|_{X'}))_s ≅ ⊕_y (F|_{X'})_y`, `(f_!F)_s ≅ ⊕_x F_x`

of Stacks 0F5F over the geometric fibres, the covariance map `(j ≫ f)_!(F|_{X'}) ⟶ f_!F` of
Stacks 0F6S is extension by zero along the inclusion of geometric fibres: it carries the summand
of a point `y` of the geometric fibre of `j ≫ f` to the summand of its image in the geometric
fibre of `f`. This is Stacks 0F6S part (1), transported from the finite-support direct image
presheaf to its sheafification.

For a family of opens `U : I → Opens X`, a point of the geometric fibre of `f` together with a
tuple of indices of opens containing it is read as a point of the geometric fibre of the
intersection cut out by the tuple, inverting the reindexing
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverFiberTupleEquiv` of the Čech index set of
Stacks 0F5H.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverFiberLift` — a point of the geometric fibre
  of `f` together with a tuple of indices of opens containing it, read as a point of the geometric
  fibre of the intersection cut out by the tuple.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleStalkFShriekFunctorIso_inv_comp_sheafFiber_openCovariance` —
  the stalk of the covariance map of the direct images with compact support is the stalk of the
  covariance map of the finite-support direct image presheaves.
* `AlgebraicGeometry.SmallEtale.ofHom_of_comp_fShriekStalkIso_openCovariance` — **Stacks 0F6S,
  part (1)**, on the stalk decompositions of Stacks 0F5F.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.openFiberPoint_coverFiberLift` and
  `AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverFiberTupleEquiv_coverFiberLift` — the lift of
  a point of the geometric fibre into an intersection lies over that point, and the reindexing of
  the Čech index set takes it back to the point together with its tuple.

## Implementation notes

The transport is the naturality in the presheaf of the comparison
`AlgebraicGeometry.etaleStalkSheafificationMap` of the stalk of a sheafification with the stalk of
the presheaf: the covariance map of the direct images with compact support is the sheafification
of the covariance map of presheaves, so its stalk is conjugate to the stalk of the latter, which
is `AlgebraicGeometry.SmallEtale.openCovarianceStalkMap`.

The inclusions of the summands are written as `DirectSum.of`, which needs a decidable equality on
the geometric fibre; that decidable structure is carried as an instance argument rather than
chosen, so that the statements compose with whatever choice a caller has made.

## References

* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Covariance

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Y.obj)

/-- The stalk at a geometric point of the covariance map of the direct images with compact
support is the stalk of the covariance map of the finite-support direct image presheaves: the
comparison of the stalk of a sheafification with the stalk of the presheaf is natural. -/
public theorem etaleStalkFShriekFunctorIso_inv_comp_sheafFiber_openCovariance :
    (etaleStalkFShriekFunctorIso.{u, v} B (j ≫ f) s
          ((openRestriction.{u, v} B j).obj F)).inv ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B j f).app F) =
      openCovarianceStalkMap.{u, v} B j f F s ≫
        (etaleStalkFShriekFunctorIso.{u, v} B f s F).inv := by
  have h := congrArg
    (etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}).map
    (toSheafify_naturality (J := SmallEtale.topology B Y.obj Y.property)
      ((openCovariancePresheafMap.{u, v} B j f).val.app F))
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h.symm

/-- The stalk at a geometric point of the covariance map of the direct images with compact
support, read on a germ of the finite-support direct image presheaf. -/
private theorem sheafFiber_openCovariance_apply
    (t : ↑(etaleStalk B Y.obj Y.property s
      ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B j).obj F)))) :
    ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        ((openCovarianceShriekMap.{u, v} B j f).app F)
      ((etaleStalkFShriekFunctorIso.{u, v} B (j ≫ f) s
        ((openRestriction.{u, v} B j).obj F)).inv t) =
      (etaleStalkFShriekFunctorIso.{u, v} B f s F).inv
        (openCovarianceStalkMap.{u, v} B j f F s t) :=
  ConcreteCategory.congr_hom
    (etaleStalkFShriekFunctorIso_inv_comp_sheafFiber_openCovariance.{u, v} B j f F s) t

/-- **Stacks 0F6S, part (1)**, on the germ decompositions of Stacks 0F6P: the covariance map of
the finite-support direct image presheaves carries a germ supported in the summand of a point of
the geometric fibre of `j ≫ f` to a germ supported in the summand of its image in the geometric
fibre of `f`. -/
private theorem finiteSupportStalkIso_openCovarianceStalkMap_of
    [DecidableEq (GeometricFiberPoint B (j ≫ f) s)]
    [DecidableEq (GeometricFiberPoint B f s)] (y : GeometricFiberPoint B (j ≫ f) s)
    (w : ↑(etaleStalk B X'.obj X'.property (y.toGeometricPoint B (j ≫ f) s)
      ((openRestriction.{u, v} B j).obj F).obj)) :
    (finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
        ((openCovarianceStalkMap.{u, v} B j f F s)
          ((finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
            ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).inv
              (DirectSum.of (fun y' : GeometricFiberPoint B (j ≫ f) s =>
                ↑(etaleStalk B X'.obj X'.property (y'.toGeometricPoint B (j ≫ f) s)
                  ((openRestriction.{u, v} B j).obj F).obj)) y w))) =
      DirectSum.of (fun x : GeometricFiberPoint B f s =>
          ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj))
        (openFiberPoint B j f s y)
        ((openFiberStalkIso.{u, v} B j f F s y).hom w) := by
  set z := (finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
    ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).inv
      (DirectSum.of _ y w) with hzdef
  have hz : (finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
      ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).hom z =
      DirectSum.of _ y w := by
    rw [hzdef]
    exact congrArg (fun φ => φ (DirectSum.of _ y w))
      ((finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
        ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).inv_hom_id)
  refine DirectSum.ext fun x => ?_
  by_cases hx : ∃ x' : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s x' = x
  · obtain ⟨x', rfl⟩ := hx
    rw [fiberStalks_openCovarianceStalkMap_apply.{u, v} B j f F s z x', hz]
    by_cases hxy : x' = y
    · subst hxy
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hxy, map_zero,
        DirectSum.of_eq_of_ne _ _ _ fun hc => hxy (openFiberPoint_injective B j f s hc)]
  · rw [fiberStalks_openCovarianceStalkMap_apply_eq_zero.{u, v} B j f F s z x
      (fun x' hc => hx ⟨x', hc⟩),
      DirectSum.of_eq_of_ne _ x _ fun hc => hx ⟨y, hc.symm⟩]

/-- **Stacks 0F6S, part (1)**, on the stalk decompositions of Stacks 0F5F: on the direct sums of
stalks over the geometric fibres the covariance map of the direct images with compact support is
extension by zero along the inclusion of geometric fibres, so it carries the summand of a point of
the geometric fibre of `j ≫ f` to the summand of its image in the geometric fibre of `f`. -/
@[stacks 0F6S "part (1), stalk compatibility on the stalk decomposition of Stacks 0F5F"]
public theorem ofHom_of_comp_fShriekStalkIso_openCovariance
    [DecidableEq (GeometricFiberPoint B (j ≫ f) s)]
    [DecidableEq (GeometricFiberPoint B f s)] (y : GeometricFiberPoint B (j ≫ f) s) :
    AddCommGrpCat.ofHom (DirectSum.of (fun y' : GeometricFiberPoint B (j ≫ f) s =>
          ↑(etaleStalk B X'.obj X'.property (y'.toGeometricPoint B (j ≫ f) s)
            ((openRestriction.{u, v} B j).obj F).obj)) y) ≫
        (fShriekStalkIso.{u, v} B (j ≫ f) s ((openRestriction.{u, v} B j).obj F)).inv ≫
        ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B j f).app F) ≫
        (fShriekStalkIso.{u, v} B f s F).hom =
      (openFiberStalkIso.{u, v} B j f F s y).hom ≫
        AddCommGrpCat.ofHom (DirectSum.of (fun x : GeometricFiberPoint B f s =>
          ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj))
            (openFiberPoint B j f s y)) := by
  refine ConcreteCategory.hom_ext _ _ fun w => ?_
  change (finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
      ((etaleStalkFShriekFunctorIso.{u, v} B f s F).hom
        (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
              (A := AddCommGrpCat.{max (u + 1) v})).map
            ((openCovarianceShriekMap.{u, v} B j f).app F)
          ((etaleStalkFShriekFunctorIso.{u, v} B (j ≫ f) s
              ((openRestriction.{u, v} B j).obj F)).inv
            ((finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
              ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).inv
                (DirectSum.of _ y w))))) =
    DirectSum.of _ (openFiberPoint B j f s y) ((openFiberStalkIso.{u, v} B j f F s y).hom w)
  rw [sheafFiber_openCovariance_apply.{u, v} B j f F s, Iso.inv_hom_id_apply]
  exact finiteSupportStalkIso_openCovarianceStalkMap_of B j f F s y w

end Covariance

namespace OpenCoverShriek

section Lift

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)
  (s : GeometricPoint Y.obj)

/-- A point of the geometric fibre of `f` over `s` together with a tuple of indices of opens
containing it, read as a point of the geometric fibre of the intersection cut out by the tuple. -/
public def coverFiberLift (x : GeometricFiberPoint B f s) {n : ℕ}
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    GeometricFiberPoint B (openSchemeι B (coverOpen B U fun k => (q k).1) ≫ f) s :=
  (openSchemeFiberPointEquiv B f s (coverOpen B U fun k => (q k).1)).symm
    ⟨x, (mem_coverOpen_iff.{u, v} B U _ _).2 fun k => (q k).2⟩

/-- The reindexing of the Čech index set by the geometric fibre takes a point of the fibre
together with a tuple of indices of opens containing it to that tuple and the corresponding point
of the fibre of the intersection. -/
public theorem coverFiberTupleEquiv_symm_apply (x : GeometricFiberPoint B f s) {n : ℕ}
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    (coverFiberTupleEquiv.{u, v} B f s U n).symm ⟨x, q⟩ =
      ⟨fun k => (q k).1, coverFiberLift.{u, v} B f U s x q⟩ :=
  rfl

/-- The reindexing of the Čech index set by the geometric fibre takes a point of the fibre of an
intersection obtained from a tuple back to the point and the tuple. -/
public theorem coverFiberTupleEquiv_coverFiberLift (x : GeometricFiberPoint B f s) {n : ℕ}
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    coverFiberTupleEquiv.{u, v} B f s U n
        ⟨fun k => (q k).1, coverFiberLift.{u, v} B f U s x q⟩ = ⟨x, q⟩ := by
  rw [← coverFiberTupleEquiv_symm_apply.{u, v} B f U s x q, Equiv.apply_symm_apply]

/-- The point of the geometric fibre of `f` underlying the lift of a point of the fibre into the
intersection cut out by a tuple of indices of opens containing it is that point. -/
public theorem openFiberPoint_coverFiberLift (x : GeometricFiberPoint B f s) {n : ℕ}
    (q : Fin n → fiberPointCoverIndex.{u, v} B f U s x) :
    openFiberPoint B (openSchemeι B (coverOpen B U fun k => (q k).1)) f s
        (coverFiberLift.{u, v} B f U s x q) = x :=
  congrArg Sigma.fst (coverFiberTupleEquiv_coverFiberLift.{u, v} B f U s x q)

end Lift

end OpenCoverShriek

end AlgebraicGeometry.SmallEtale

end
