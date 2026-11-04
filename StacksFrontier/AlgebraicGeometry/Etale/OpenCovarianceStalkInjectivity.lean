module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion

/-!
# Injectivity of covariance for the direct image with compact support

Let `j : X' ⟶ X` be an open immersion and let `f : X ⟶ Y` be locally of finite type and locally
quasi-finite in a big étale site. The covariance map `(j ≫ f)_!(F|_{X'}) ⟶ f_!F` of Stacks 0F6S is
a monomorphism, with no separatedness hypothesis on `f`. This is Stacks 0F6S, part (4).

The argument is the one of the source. An element of the stalk of the finite-support direct image
at a geometric point of `Y` is a finite sum of germs of supported sections over one pointed étale
neighbourhood, so the description of part (1) on such germs extends to arbitrary elements of the
stalk: on the stalk decompositions of Stacks 0F6P the covariance map is extension by zero along
the inclusion of geometric fibres, which is injective because that inclusion is. The stalk of the
sheafification is the stalk of the presheaf, the stalk at a geometric point being the fibre of a
point of the site, and the stalks at the geometric points jointly detect monomorphisms.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_listSum_finiteSupportStalkGenerator` — every element of the
  stalk of the finite-support direct image is a finite sum of germs of supported sections over one
  common pointed étale neighbourhood.
* `AlgebraicGeometry.SmallEtale.fiberStalks_openCovarianceStalkMap_apply` and
  `AlgebraicGeometry.SmallEtale.fiberStalks_openCovarianceStalkMap_apply_eq_zero` — **Stacks 0F6S,
  part (1)** on an arbitrary element of the stalk, not only on a germ of a supported section.
* `AlgebraicGeometry.SmallEtale.injective_openCovarianceStalkMap` — the covariance map of
  finite-support direct-image presheaves is injective on the stalk at a geometric point.
* `AlgebraicGeometry.SmallEtale.mono_openCovarianceShriekMap_app_general` — **Stacks 0F6S,
  part (4)**, in its unrestricted form: no separatedness is assumed.

## Implementation notes

The comparison of the stalk of a sheafification with the stalk of the presheaf is Mathlib's
`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`, the statement that
the fibre functor on sheaves is the fibre functor on presheaves localized at the local
isomorphisms; it applies because `AlgebraicGeometry.etaleStalk` *is* the fibre functor of the
point `AlgebraicGeometry.geometricPointSitePoint` of the small étale site.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Sum

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (g : S ⟶ T)
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
  (t : GeometricPoint T.obj)

/-- Every element of the stalk of the finite-support direct image is a finite sum of germs of
supported sections, all of them over one common pointed étale neighbourhood of the geometric
point of the base. -/
public theorem exists_listSum_finiteSupportStalkGenerator
    (z : ↑(etaleStalk B T.obj T.property t
      ((finiteSupportPushforward.{u, max (u + 1) v} B g
        (fun _ => inferInstance)).val.obj G))) :
    ∃ (V : SmallEtale B T.obj T.property)
      (w : (geometricPointFiber B T.obj T.property t).obj V)
      (l : List ((E : FiniteSupport B g V) × ↑((finiteSupportDiagram B g G V).obj E))),
      (l.map (fun pr => finiteSupportStalkGenerator.{u, v} B g G t
        (Functor.elementsMk (geometricPointFiber B T.obj T.property t) V w)
        pr.1 pr.2)).sum = z := by
  obtain ⟨U, l, hl⟩ := exists_listSum_generators_eq_etaleStalk.{u, max (u + 1) v} B g t G
    (fun _ => inferInstance) z
  exact ⟨U.1, U.2, l, hl⟩

end Sum

section Stalk

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Y.obj)

/-- **Stacks 0F6S, part (1)** on a finite sum of germs of supported sections over one pointed
étale neighbourhood, in a summand indexed by a point of the geometric fibre of `j ≫ f`. -/
public theorem fiberStalks_openCovarianceStalkMap_listSum
    (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V)
    (l : List ((E : FiniteSupport B (j ≫ f) V) ×
      ↑((finiteSupportDiagram B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V).obj E)))
    (x : GeometricFiberPoint B (j ≫ f) s) :
    ((finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
          ((openCovarianceStalkMap.{u, v} B j f F s)
            (l.map (fun pr => finiteSupportStalkGenerator.{u, v} B (j ≫ f)
              ((openRestriction.{u, v} B j).obj F) s
              (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)
              pr.1 pr.2)).sum) :
        fiberStalks.{u, max (u + 1) v} B f s F) (openFiberPoint B j f s x) =
      (openFiberStalkIso.{u, v} B j f F s x).hom
        (((finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
              ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).hom
            (l.map (fun pr => finiteSupportStalkGenerator.{u, v} B (j ≫ f)
              ((openRestriction.{u, v} B j).obj F) s
              (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)
              pr.1 pr.2)).sum :
          fiberStalks.{u, max (u + 1) v} B (j ≫ f) s
            ((openRestriction.{u, v} B j).obj F)) x) := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero, DirectSum.zero_apply]
  | cons p l ih =>
    have hgen := fiberStalks_openCovarianceStalkMap_openFiberPoint.{u, v} B j f F s V w
      p.1 p.2 x
    simp only [List.map_cons, List.sum_cons, map_add, DirectSum.add_apply]
    rw [ih, hgen]

/-- **Stacks 0F6S, part (1)** on a finite sum of germs of supported sections over one pointed
étale neighbourhood, in a summand outside the image of the geometric fibre of `j ≫ f`. -/
public theorem fiberStalks_openCovarianceStalkMap_listSum_eq_zero
    (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V)
    (l : List ((E : FiniteSupport B (j ≫ f) V) ×
      ↑((finiteSupportDiagram B (j ≫ f) ((openRestriction.{u, v} B j).obj F) V).obj E)))
    (y : GeometricFiberPoint B f s)
    (hy : ∀ x : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s x ≠ y) :
    ((finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
        ((openCovarianceStalkMap.{u, v} B j f F s)
          (l.map (fun pr => finiteSupportStalkGenerator.{u, v} B (j ≫ f)
            ((openRestriction.{u, v} B j).obj F) s
            (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w)
            pr.1 pr.2)).sum) :
      fiberStalks.{u, max (u + 1) v} B f s F) y = 0 := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero, DirectSum.zero_apply]
  | cons p l ih =>
    have hgen := fiberStalks_openCovarianceStalkMap_eq_zero.{u, v} B j f F s V w
      p.1 p.2 y hy
    simp only [List.map_cons, List.sum_cons, map_add, DirectSum.add_apply]
    rw [ih, hgen, add_zero]

/-- **Stacks 0F6S, part (1)** on an arbitrary element of the stalk: on the stalk decompositions of
Stacks 0F6P the covariance map carries the component at a point of the geometric fibre of `j ≫ f`
to the component at its image, through the identification of the two stalks. -/
@[stacks 0F6S "part (1), stalk compatibility, presheaf form, summands in the open, any element"]
public theorem fiberStalks_openCovarianceStalkMap_apply
    (z : ↑(etaleStalk B Y.obj Y.property s
      ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B j).obj F))))
    (x : GeometricFiberPoint B (j ≫ f) s) :
    ((finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
          ((openCovarianceStalkMap.{u, v} B j f F s) z) :
        fiberStalks.{u, max (u + 1) v} B f s F) (openFiberPoint B j f s x) =
      (openFiberStalkIso.{u, v} B j f F s x).hom
        (((finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
              ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).hom z :
          fiberStalks.{u, max (u + 1) v} B (j ≫ f) s
            ((openRestriction.{u, v} B j).obj F)) x) := by
  obtain ⟨V, w, l, hl⟩ := exists_listSum_finiteSupportStalkGenerator.{u, v} B (j ≫ f)
    ((openRestriction.{u, v} B j).obj F) s z
  subst hl
  exact fiberStalks_openCovarianceStalkMap_listSum B j f F s V w l x

/-- **Stacks 0F6S, part (1)** on an arbitrary element of the stalk, in a summand outside the image
of the geometric fibre of `j ≫ f`: the component of the image vanishes there. -/
@[stacks 0F6S "part (1), stalk compatibility, presheaf form, summands outside, any element"]
public theorem fiberStalks_openCovarianceStalkMap_apply_eq_zero
    (z : ↑(etaleStalk B Y.obj Y.property s
      ((finiteSupportPushforward.{u, max (u + 1) v} B (j ≫ f)
        (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B j).obj F))))
    (y : GeometricFiberPoint B f s)
    (hy : ∀ x : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s x ≠ y) :
    ((finiteSupportStalkIso.{u, max (u + 1) v} B f s F (fun _ => inferInstance)).hom
        ((openCovarianceStalkMap.{u, v} B j f F s) z) :
      fiberStalks.{u, max (u + 1) v} B f s F) y = 0 := by
  obtain ⟨V, w, l, hl⟩ := exists_listSum_finiteSupportStalkGenerator.{u, v} B (j ≫ f)
    ((openRestriction.{u, v} B j).obj F) s z
  subst hl
  exact fiberStalks_openCovarianceStalkMap_listSum_eq_zero B j f F s V w l y hy

/-- The covariance map of finite-support direct-image presheaves is injective on the stalk at a
geometric point of the base: on the stalk decompositions of Stacks 0F6P it is extension by zero
along the inclusion of geometric fibres, which is injective. -/
public theorem injective_openCovarianceStalkMap :
    Function.Injective (openCovarianceStalkMap.{u, v} B j f F s) := by
  have hiso : Function.Injective (finiteSupportStalkIso.{u, max (u + 1) v} B (j ≫ f) s
      ((openRestriction.{u, v} B j).obj F) (fun _ => inferInstance)).hom :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hinj : Function.Injective (openCovarianceStalkMap.{u, v} B j f F s).hom := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    refine hiso (Eq.trans (DFinsupp.ext fun x => ?_) (map_zero _).symm)
    have hcomp : Function.Injective (openFiberStalkIso.{u, v} B j f F s x).hom :=
      (AddCommGrpCat.mono_iff_injective _).1 inferInstance
    refine hcomp (Eq.trans ?_ (map_zero _).symm)
    refine (fiberStalks_openCovarianceStalkMap_apply B j f F s z x).symm.trans ?_
    rw [hz, map_zero, DirectSum.zero_apply]
  exact hinj

end Stalk

section Sheafification

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The map induced by the covariance map of finite-support direct-image presheaves on the fibre
of the point of the small étale site attached to a geometric point is the map on the geometric
stalk: the stalk at a geometric point is that fibre. -/
public theorem presheafFiber_map_openCovariancePresheafMap (s : GeometricPoint Y.obj) :
    ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        ((openCovariancePresheafMap.{u, v} B j f).val.app F) =
      openCovarianceStalkMap.{u, v} B j f F s :=
  rfl

/-- The covariance map of the direct images with compact support is a monomorphism on the stalk at
every geometric point: the stalk of a sheafification is the stalk of the presheaf, and the stalk
of the presheaf map is injective. -/
public theorem mono_sheafFiber_openCovarianceShriekMap_app (s : GeometricPoint Y.obj) :
    Mono (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map
        ((openCovarianceShriekMap.{u, v} B j f).app F)) := by
  have hpre : Mono (((geometricPointSitePoint B Y.obj Y.property s).presheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map
        ((openCovariancePresheafMap.{u, v} B j f).val.app F)) := by
    rw [presheafFiber_map_openCovariancePresheafMap B j f F s]
    exact (AddCommGrpCat.mono_iff_injective _).2
      (injective_openCovarianceStalkMap.{u, v} B j f F s)
  have he : (openCovarianceShriekMap.{u, v} B j f).app F =
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
        AddCommGrpCat.{max (u + 1) v}).map
        ((openCovariancePresheafMap.{u, v} B j f).val.app F) :=
    Category.id_comp _
  rw [he]
  set e := (geometricPointSitePoint B Y.obj Y.property s).presheafToSheafCompSheafFiberIso
    AddCommGrpCat.{max (u + 1) v} with he'
  have hnat : ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map
        ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
          AddCommGrpCat.{max (u + 1) v}).map
          ((openCovariancePresheafMap.{u, v} B j f).val.app F)) ≫
      e.hom.app ((wholeFiniteSupportPushforward.{u, v} B f).obj F) =
        e.hom.app ((openFiniteSupportPushforward.{u, v} B j f).obj F) ≫
          ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map
            ((openCovariancePresheafMap.{u, v} B j f).val.app F) :=
    e.hom.naturality ((openCovariancePresheafMap.{u, v} B j f).val.app F)
  have hcomp : Mono (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
            AddCommGrpCat.{max (u + 1) v}).map
            ((openCovariancePresheafMap.{u, v} B j f).val.app F)) ≫
        e.hom.app ((wholeFiniteSupportPushforward.{u, v} B f).obj F)) := by
    rw [hnat]
    infer_instance
  exact mono_of_mono _ (e.hom.app ((wholeFiniteSupportPushforward.{u, v} B f).obj F))

/-- **Stacks Project, Tag 0F6S, part (4)**, in its unrestricted form: for an open immersion
`j : X' ⟶ X` and a morphism `f : X ⟶ Y` locally of finite type and locally quasi-finite, with no
separatedness assumed, the covariance map `(j ≫ f)_!(F|_{X'}) ⟶ f_!F` of the direct images with
compact support is a monomorphism.

On the stalk at a geometric point the map is extension by zero along the inclusion of geometric
fibres of Stacks 0F6P, hence injective; the stalks at the geometric points jointly detect
monomorphisms of abelian sheaves on the small étale site. -/
@[stacks 0F6S "part (4), injectivity"]
public theorem mono_openCovarianceShriekMap_app_general :
    Mono ((openCovarianceShriekMap.{u, v} B j f).app F) := by
  have hst : ∀ s : GeometricPoint Y.obj,
      Mono (((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
          ((openCovarianceShriekMap.{u, v} B j f).app F)) :=
    mono_sheafFiber_openCovarianceShriekMap_app B j f F
  exact (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Y.obj
    Y.property).jointlyReflectMonomorphisms.mono _

end Sheafification

end AlgebraicGeometry.SmallEtale

end
