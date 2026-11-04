module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeMap

/-!
# The base-change map of the direct image with compact support is an isomorphism

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally quasi-finite,
and let `F` be an abelian sheaf on the small étale site of `X`. The base-change map
`g⁻¹f_!F ⟶ f'_!(p⁻¹F)` of `StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeMap` is an
isomorphism, functorially in `F`, and on the stalk at a geometric point of `Y'` it is the
base-change comparison of the stalk decompositions of Stacks 0F5F. This is Stacks 0F5J.

The route is the source's. The germ at a geometric point `t` of `Y'` of the image of a generator
`(Z, s)` of `f_{p!}F` is the germ of the generator `(Z', s')` carrying the base-changed support
and the pulled-back section; on a single summand of the stalk decompositions that is the
statement that the germ of `s'` at a point of the geometric fibre of `f'` is the germ of `s` at
the corresponding point of the geometric fibre of `f`, which is the germ formula of Stacks 03Q1
for the inverse image along `p`. Summing over the fibre, the stalk of the base-change map is the
isomorphism `fShriekStalkBaseChangeIso`, so the base-change map is an isomorphism on every
geometric stalk and hence an isomorphism, by Stacks 03PU.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso` — the isomorphism
  `g⁻¹f_!F ≅ f'_!(p⁻¹F)`, as an isomorphism of functors, which is its functoriality in `F`.

## Main results

* `AlgebraicGeometry.SmallEtale.fiberPointLift_comp_fiberBaseChangeScheme` — the lift to
  `X'_{V'}` of a point of the geometric fibre of `f'` lies over the lift to `X_V` of the
  corresponding point of the geometric fibre of `f`.
* `AlgebraicGeometry.SmallEtale.fiberStalkComponent_fiberBaseChangeSectionsMap` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeDiagramMap_comp_fiberStalkHom` — the germ of a
  base-changed supported section at a point of the geometric fibre, and the resulting exchange
  of the germ decompositions of Stacks 0F5F.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMap_stalk` and
  `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMap_stalk_eq` — the base-change map on the
  stalk at a geometric point of `Y'` is the stalkwise base-change isomorphism.
* `AlgebraicGeometry.SmallEtale.isIso_fShriekBaseChangeMap` — the base-change map is an
  isomorphism.
* `AlgebraicGeometry.SmallEtale.exists_fShriekBaseChangeIso` — the statement of the source: such
  an isomorphism exists, functorially in `F`, and agrees with the stalk descriptions of
  Stacks 0F5F.

## Implementation notes

The identifications of a stalk with a colimit, of the finite-support direct image presheaf with
its colimits of supported sections, and of a sheafification with the sheaf it defines are all
available only up to maps which are isomorphisms but not identities, so the germ computation is
carried out on a generator of the double colimit and transported; the two comparisons
`colimit_ι_comp_etaleStalkSheafificationMap` fix one spelling of the diagrams for the whole file,
the auxiliary `comp_reassoc` and `comp_reassoc₄` let an equality of composites be used inside a
longer composite, and the chains are written as explicit composites of congruences rather than
by rewriting, the terms involved being too large for the rewriting tactics to re-associate.

## References

* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

/-- An equality of composites may be used inside a longer composite. -/
private theorem comp_reassoc {𝒞 : Type*} [Category 𝒞] {W X Y Z T : 𝒞} {a : W ⟶ X} {b : X ⟶ Y}
    {a' : W ⟶ Z} {b' : Z ⟶ Y} (h : a ≫ b = a' ≫ b') (k : Y ⟶ T) :
    a ≫ b ≫ k = a' ≫ b' ≫ k := by
  rw [← Category.assoc, h, Category.assoc]

/-- An equality whose left-hand side is a fourfold composite may be used inside a longer
composite. -/
private theorem comp_reassoc₄ {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ T : 𝒞} {a : A₀ ⟶ A₁}
    {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄} {e : A₀ ⟶ A₄} (h : a ≫ b ≫ c ≫ d = e)
    (k : A₄ ⟶ T) : a ≫ b ≫ c ≫ d ≫ k = e ≫ k := by
  have hassoc : a ≫ b ≫ c ≫ d ≫ k = (a ≫ b ≫ c ≫ d) ≫ k := by
    simp only [Category.assoc]
  rw [hassoc, h]

section Fibre

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  (t : GeometricPoint Y'.obj)

/-- The lift of `t` to the base change of a test object of `Y` lies over the chosen lift of the
image point. -/
public theorem geometricPointFiberBaseChangeEquiv_comp_fiberProjection
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).obj V) :
    (geometricPointFiberBaseChangeEquiv B g t V u).1 ≫
      B.inclusion.map (fiberProjection B g V) = u.1 := by
  rw [geometricPointFiberBaseChangeEquiv_apply_val]
  exact (congrArg (fun k => k ≫ B.inclusion.map (fiberProjection B g V))
      (Category.comp_id _)).trans
    (((IsPullback.of_hasPullback V.obj.hom g).map B.inclusion).lift_fst _ _ _)

/-- The lift to `X'_{V'}` of a point of the geometric fibre of `f'` lies over the lift to `X_V`
of the corresponding point of the geometric fibre of `f`. -/
public theorem fiberPointLift_comp_fiberBaseChangeScheme
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).obj V)
    (x : GeometricFiberPoint B f' t) :
    fiberPointLift B f' t (baseChange B g V)
          (geometricPointFiberBaseChangeEquiv B g t V u) x ≫
        fiberBaseChangeScheme B p f' f g sq V =
      fiberPointLift B f (t.map (B.inclusion.map g)) V u
        (fiberPointBaseChange B p f' f g sq t x) := by
  have hfst := congrArg B.inclusion.map (fiberBaseChangeMap_fst B p f' f g sq V)
  have hsnd := congrArg B.inclusion.map (fiberBaseChangeMap_snd B p f' f g sq V)
  rw [Functor.map_comp, Functor.map_comp] at hfst
  rw [Functor.map_comp, Functor.map_comp] at hsnd
  refine ((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => fiberPointLift B f' t (baseChange B g V)
            (geometricPointFiberBaseChangeEquiv B g t V u) x ≫ k) hfst).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ B.inclusion.map (fiberProjection B g V))
              (fiberPointLift_comp_fst B f' t (baseChange B g V)
                (geometricPointFiberBaseChangeEquiv B g t V u) x)).trans
            ((geometricPointFiberBaseChangeEquiv_comp_fiberProjection B g t V u).trans
              (fiberPointLift_comp_fst B f (t.map (B.inclusion.map g)) V u
                (fiberPointBaseChange B p f' f g sq t x)).symm))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => fiberPointLift B f' t (baseChange B g V)
            (geometricPointFiberBaseChangeEquiv B g t V u) x ≫ k) hsnd).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ B.inclusion.map p)
              (fiberPointLift_comp_snd B f' t (baseChange B g V)
                (geometricPointFiberBaseChangeEquiv B g t V u) x)).trans
            (fiberPointLift_comp_snd B f (t.map (B.inclusion.map g)) V u
              (fiberPointBaseChange B p f' f g sq t x)).symm)))

/-- The image under the comparison of the two étale base changes of the lift of a point of the
geometric fibre of `f'` is the lift of the corresponding point of the geometric fibre of `f`. -/
public theorem fiberPointLift_base_fiberBaseChangeScheme
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).obj V)
    (x : GeometricFiberPoint B f' t) :
    (fiberBaseChangeScheme B p f' f g sq V).base
        ((fiberPointLift B f' t (baseChange B g V)
          (geometricPointFiberBaseChangeEquiv B g t V u) x).base default) =
      (fiberPointLift B f (t.map (B.inclusion.map g)) V u
        (fiberPointBaseChange B p f' f g sq t x)).base default := by
  have h := congrArg (fun k : t.source ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) => k.base default)
    (fiberPointLift_comp_fiberBaseChangeScheme B p f' f g sq t V u x)
  simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h

section Germ

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
  (V : SmallEtale B Y.obj Y.property)
  (u : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).obj V)
  (E : FiniteSupport B f V)

/-- The comparison arrow of the base-changed support carries the lift of a point of the
geometric fibre of `f'` to the lift of the corresponding point of the geometric fibre of `f`:
the compatibility consumed by the germ formula of Stacks 03Q1. -/
private theorem fiberBaseChangeSupportArrow_lift
    (x : GeometricFiberPoint B f' t)
    (hx : (fiberPointLift B f' t (baseChange B g V)
      (geometricPointFiberBaseChangeEquiv B g t V u) x).base default ∈
      (fiberBaseChangeSupportOpen B p f' f g sq V E :
        Set ((SmallEtale.toScheme B X'.obj X'.property).obj
          (baseChange B f' (baseChange B g V)))))
    (hE : (fiberPointLift B f (t.map (B.inclusion.map g)) V u
      (fiberPointBaseChange B p f' f g sq t x)).base default ∈
      (finiteSupportOpen B f V E :
        Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)))) :
    (openObjectLift B X'.obj X'.property (x.toGeometricPoint B f' t)
            (baseChange B f' (baseChange B g V))
            (fiberPointElement B f' t (baseChange B g V)
              (geometricPointFiberBaseChangeEquiv B g t V u) x)
            (fiberBaseChangeSupportOpen B p f' f g sq V E) hx).1 ≫
        (SmallEtale.toScheme B X'.obj X'.property).map
          (fiberBaseChangeSupportArrow B p f' f g sq V E) ≫
        B.inclusion.map (baseChangeObjProjection B p (finiteSupportOpenObject B f V E)) =
      (openObjectLift B X.obj X.property
        (((fiberPointBaseChange B p f' f g sq t x).toGeometricPoint B f
          (t.map (B.inclusion.map g)))) (baseChange B f V)
        (fiberPointElement B f (t.map (B.inclusion.map g)) V u
          (fiberPointBaseChange B p f' f g sq t x))
        (finiteSupportOpen B f V E) hE).1 := by
  refine (cancel_mono (finiteSupportOpen B f V E).ι).1 ?_
  rw [Category.assoc, fiberBaseChangeSupportArrow_comp, ← Category.assoc]
  exact ((congrArg (fun k => k ≫ fiberBaseChangeScheme B p f' f g sq V)
      (openObjectLift_comp_ι B X'.obj X'.property (x.toGeometricPoint B f' t)
        (baseChange B f' (baseChange B g V))
        (fiberPointElement B f' t (baseChange B g V)
          (geometricPointFiberBaseChangeEquiv B g t V u) x)
        (fiberBaseChangeSupportOpen B p f' f g sq V E) hx)).trans
    ((fiberPointLift_comp_fiberBaseChangeScheme B p f' f g sq t V u x).trans
      (openObjectLift_comp_ι B X.obj X.property
        ((fiberPointBaseChange B p f' f g sq t x).toGeometricPoint B f
          (t.map (B.inclusion.map g))) (baseChange B f V)
        (fiberPointElement B f (t.map (B.inclusion.map g)) V u
          (fiberPointBaseChange B p f' f g sq t x))
        (finiteSupportOpen B f V E) hE).symm))

/-- **Stacks 0F5J.** The germ at a point of the geometric fibre of `f'` of the base change of a
supported section is the germ of the section at the corresponding point of the geometric fibre
of `f`, read through the identification of the two stalks. This is the commutative square of the
source, on a single summand of the stalk decompositions of Stacks 0F5F. -/
@[stacks 0F5J "the germ of a base-changed supported section at a point of the geometric fibre"]
public theorem fiberStalkComponent_fiberBaseChangeSectionsMap
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))
    (x : GeometricFiberPoint B f' t) :
    fiberStalkComponent.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)
        (baseChange B g V) (geometricPointFiberBaseChangeEquiv B g t V u)
        (fiberBaseChangeSupport B p f' f g sq V E)
        (fiberBaseChangeSectionsMap.{u, u + 1} B p f' f g sq V E F s) x =
      (fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F x).hom
        (fiberStalkComponent.{u, u + 1} B f (t.map (B.inclusion.map g)) F V u E s
          (fiberPointBaseChange B p f' f g sq t x)) := by
  by_cases hx : (fiberPointLift B f' t (baseChange B g V)
      (geometricPointFiberBaseChangeEquiv B g t V u) x).base default ∈
    (fiberBaseChangeSupport B p f' f g sq V E).1
  · have hxE : (fiberPointLift B f (t.map (B.inclusion.map g)) V u
        (fiberPointBaseChange B p f' f g sq t x)).base default ∈ E.1 := by
      rw [← fiberPointLift_base_fiberBaseChangeScheme B p f' f g sq t V u x]
      exact hx
    have h' : HasFiberLift B f' t (baseChange B g V)
        (geometricPointFiberBaseChangeEquiv B g t V u)
        (fiberBaseChangeSupport B p f' f g sq V E) x :=
      subset_supportOpen B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E)) hx
    have hE : HasFiberLift B f (t.map (B.inclusion.map g)) V u E
        (fiberPointBaseChange B p f' f g sq t x) :=
      subset_supportOpen B X.obj X.property (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E) hxE
    have hpre : (fiberPointLift B f' t (baseChange B g V)
        (geometricPointFiberBaseChangeEquiv B g t V u) x).base default ∈
        (fiberBaseChangeSupportOpen B p f' f g sq V E :
          Set ((SmallEtale.toScheme B X'.obj X'.property).obj
            (baseChange B f' (baseChange B g V)))) :=
      fiberBaseChangeSupport_subset_open B p f' f g sq V E hx
    rw [fiberStalkComponent_of_hasFiberLift B f' t ((abPullback.{u, u + 1} B p).obj F)
        (baseChange B g V) (geometricPointFiberBaseChangeEquiv B g t V u)
        (fiberBaseChangeSupport B p f' f g sq V E) _ x h',
      fiberStalkComponent_of_hasFiberLift B f (t.map (B.inclusion.map g)) F V u E s _ hE]
    have hq : (geometricPointFiber B X'.obj X'.property (x.toGeometricPoint B f' t)).map
          (openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
            (fiberBaseChangeSupportOpen_le B p f' f g sq V E))
          (openObjectLift B X'.obj X'.property (x.toGeometricPoint B f' t)
            (baseChange B f' (baseChange B g V))
            (fiberPointElement B f' t (baseChange B g V)
              (geometricPointFiberBaseChangeEquiv B g t V u) x)
            (fiberBaseChangeSupportOpen B p f' f g sq V E) hpre) =
        openObjectLift B X'.obj X'.property (x.toGeometricPoint B f' t)
          (baseChange B f' (baseChange B g V))
          (fiberPointElement B f' t (baseChange B g V)
            (geometricPointFiberBaseChangeEquiv B g t V u) x)
          (finiteSupportOpen B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E)) h' := by
      refine openObjectLift_ext B X'.obj X'.property (x.toGeometricPoint B f' t)
        (baseChange B f' (baseChange B g V)) _ _ _ ?_
      show ((openObjectLift B X'.obj X'.property (x.toGeometricPoint B f' t)
            (baseChange B f' (baseChange B g V))
            (fiberPointElement B f' t (baseChange B g V)
              (geometricPointFiberBaseChangeEquiv B g t V u) x)
            (fiberBaseChangeSupportOpen B p f' f g sq V E) hpre).1 ≫
          (SmallEtale.toScheme B X'.obj X'.property).map
            (openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
              (fiberBaseChangeSupportOpen_le B p f' f g sq V E))) ≫ _ =
        (openObjectLift B X'.obj X'.property (x.toGeometricPoint B f' t)
          (baseChange B f' (baseChange B g V))
          (fiberPointElement B f' t (baseChange B g V)
            (geometricPointFiberBaseChangeEquiv B g t V u) x)
          (finiteSupportOpen B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E)) h').1 ≫ _
      rw [Category.assoc, openObjectHomOfLE_map, Scheme.homOfLE_ι]
      exact (openObjectLift_comp_ι B X'.obj X'.property (x.toGeometricPoint B f' t)
          (baseChange B f' (baseChange B g V))
          (fiberPointElement B f' t (baseChange B g V)
            (geometricPointFiberBaseChangeEquiv B g t V u) x)
          (fiberBaseChangeSupportOpen B p f' f g sq V E) hpre).trans
        (openObjectLift_comp_ι B X'.obj X'.property (x.toGeometricPoint B f' t)
          (baseChange B f' (baseChange B g V))
          (fiberPointElement B f' t (baseChange B g V)
            (geometricPointFiberBaseChangeEquiv B g t V u) x)
          (finiteSupportOpen B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E)) h').symm
    rw [← etaleGerm_map B X'.obj X'.property (x.toGeometricPoint B f' t)
        ((abPullback.{u, u + 1} B p).obj F).obj
        (openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupportOpen_le B p f' f g sq V E)) _ _ hq,
      fiberBaseChangeSectionsMap_restrict.{u, u + 1}]
    have hgerm := ConcreteCategory.congr_hom
      (etaleStalkSmallEtalePullObjIso_germ B p (x.toGeometricPoint B f' t)
        AddCommGrpCat.{u + 1} F
        ⟨openObject B X'.obj X'.property (baseChange B f' (baseChange B g V))
            (fiberBaseChangeSupportOpen B p f' f g sq V E),
          openObjectLift B X'.obj X'.property (x.toGeometricPoint B f' t)
            (baseChange B f' (baseChange B g V))
            (fiberPointElement B f' t (baseChange B g V)
              (geometricPointFiberBaseChangeEquiv B g t V u) x)
            (fiberBaseChangeSupportOpen B p f' f g sq V E) hpre⟩
        ⟨finiteSupportOpenObject B f V E,
          openObjectLift B X.obj X.property
            ((fiberPointBaseChange B p f' f g sq t x).toGeometricPoint B f
              (t.map (B.inclusion.map g))) (baseChange B f V)
            (fiberPointElement B f (t.map (B.inclusion.map g)) V u
              (fiberPointBaseChange B p f' f g sq t x))
            (finiteSupportOpen B f V E) hE⟩
        (fiberBaseChangeSupportArrow B p f' f g sq V E)
        (fiberBaseChangeSupportArrow_lift B p f' f g sq t V u E x hpre hE)) s.val
    simp only [ConcreteCategory.comp_apply] at hgerm
    exact (Iso.hom_inv_id_apply
        (etaleStalkSmallEtalePullObjIso B p (x.toGeometricPoint B f' t)
          AddCommGrpCat.{u + 1} F) _).symm.trans
      (congrArg (fun z => (etaleStalkSmallEtalePullObjIso B p (x.toGeometricPoint B f' t)
        AddCommGrpCat.{u + 1} F).inv z) hgerm)
  · rw [fiberStalkComponent_eq_zero_of_notMem B f' t ((abPullback.{u, u + 1} B p).obj F)
      (baseChange B g V) (geometricPointFiberBaseChangeEquiv B g t V u)
      (fiberBaseChangeSupport B p f' f g sq V E) _ x hx]
    rw [fiberStalkComponent_eq_zero_of_notMem B f (t.map (B.inclusion.map g)) F V u E s _ ?_,
      map_zero]
    rw [← fiberPointLift_base_fiberBaseChangeScheme B p f' f g sq t V u x]
    exact hx

/-- **Stacks 0F5J.** The germ decompositions of Stacks 0F5F on the two sides of the square are
exchanged by the base-change map on supported sections and the comparison of the direct sums of
stalks over the two geometric fibres. -/
@[stacks 0F5J "the germ decompositions exchanged by the base-change map on supported sections"]
public theorem fiberBaseChangeDiagramMap_comp_fiberStalkHom
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f')] :
    fiberBaseChangeDiagramMap.{u, u + 1} B p f' f g sq V F E ≫
        fiberStalkHom.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)
          (baseChange B g V) (geometricPointFiberBaseChangeEquiv B g t V u)
          (fiberBaseChangeSupport B p f' f g sq V E) =
      fiberStalkHom.{u, u + 1} B f (t.map (B.inclusion.map g)) F V u E ≫
        (AddEquiv.toAddCommGrpIso
          (fiberStalksBaseChangeEquiv.{u, u + 1} B p f' f g sq t F)).hom := by
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext fun s => DFinsupp.ext fun x => ?_
  simp only [ConcreteCategory.comp_apply]
  exact (fiberStalkComponent_fiberBaseChangeSectionsMap.{u} B p f' f g sq t F V u E s x).trans
    (fiberStalksBaseChangeEquiv_apply.{u, u + 1} B p f' f g sq t F
      (fiberStalkSum.{u, u + 1} B f (t.map (B.inclusion.map g)) F V u E s) x).symm

end Germ

section Stalk

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- The germ at `t` of the inverse image of a section of `f_!F` over a test object is the germ
of the section at the image point, read through the comparison of the two stalks. -/
private theorem etaleStalk_pullObjIso_inv_germ
    (U : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements) :
    colimit.ι (etaleStalkDiagram B Y.obj Y.property (t.map (B.inclusion.map g))
          ((fShriekFunctor.{u, u + 1} B f).obj F).obj) (op U) ≫
        (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F)).inv =
      pullbackSectionAlongHom B g AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F) U.1
          ((smallEtaleBaseChange B g).obj U.1) (𝟙 _) ≫
        colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
          ((abPullback.{u, u + 1} B g).obj ((fShriekFunctor.{u, u + 1} B f).obj F)).obj)
          (op ⟨(smallEtaleBaseChange B g).obj U.1,
            geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩) := by
  have hgerm := etaleStalkSmallEtalePullObjIso_germ B g t AddCommGrpCat.{u + 1}
    ((fShriekFunctor.{u, u + 1} B f).obj F)
    ⟨(smallEtaleBaseChange B g).obj U.1,
      geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ U (𝟙 _) (by
        rw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact geometricPointFiberBaseChangeEquiv_comp_fiberProjection B g t U.1 U.2)
  rw [← hgerm]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => pullbackSectionAlongHom B g AddCommGrpCat.{u + 1}
        ((fShriekFunctor.{u, u + 1} B f).obj F) U.1
        ((smallEtaleBaseChange B g).obj U.1) (𝟙 _) ≫ k)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
              ((abPullback.{u, u + 1} B g).obj ((fShriekFunctor.{u, u + 1} B f).obj F)).obj)
              (op (⟨(smallEtaleBaseChange B g).obj U.1,
                geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ :
                (geometricPointFiber B Y'.obj Y'.property t).Elements)) ≫ k)
            (Iso.hom_inv_id _)).trans (Category.comp_id _))))

/-- The inverse image along `g` of a section of `f_!F` over a test object is carried by the
base-change map to the image of that section under the sheafified map `c`. -/
private theorem pullbackSectionAlongHom_comp_fShriekBaseChangeMap
    (V : SmallEtale B Y.obj Y.property) :
    pullbackSectionAlongHom B g AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F) V
          ((smallEtaleBaseChange B g).obj V) (𝟙 _) ≫
        (fShriekBaseChangeMap.{u} B p f' f g sq F).hom.app
          (op ((smallEtaleBaseChange B g).obj V)) =
      (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F).hom.app (op V) := by
  have h := NatTrans.congr_app
    (congrArg (fun z : (fShriekFunctor.{u, u + 1} B f).obj F ⟶
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).obj
            ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)) => z.hom)
      (fShriekBaseChangeMap_triangle.{u} B p f' f g sq F)) (op V)
  have hpsa : pullbackSectionAlongHom B g AddCommGrpCat.{u + 1}
        ((fShriekFunctor.{u, u + 1} B f).obj F) V
        ((smallEtaleBaseChange B g).obj V) (𝟙 _) =
      (((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).unit.app
        ((fShriekFunctor.{u, u + 1} B f).obj F)).hom.app (op V) := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
    exact ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id
      ((((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).obj
        ((fShriekFunctor.{u, u + 1} B f).obj F)).obj)
      (op ((smallEtaleBaseChange B g).obj V)))
      ((((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).unit.app
        ((fShriekFunctor.{u, u + 1} B f).obj F)).hom.app (op V) z)
  exact Eq.trans (congrArg (fun k => k ≫ (fShriekBaseChangeMap.{u} B p f' f g sq F).hom.app
    (op ((smallEtaleBaseChange B g).obj V))) hpsa) h

/-- The component of the map `c` over a test object, read on the colimit of supported
sections. -/
private theorem eqToHom_comp_fiberBaseChangePresheafApp
    (V : SmallEtale B Y.obj Y.property) :
    eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V).symm ≫
        fiberBaseChangePresheafApp.{u} B p f' f g sq F V =
      fiberBaseChangeColimitMap.{u, u + 1} B p f' f g sq V F ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f'
            (fun _ => inferInstance)).2.obj_eq ((abPullback.{u, u + 1} B p).obj F)
          (baseChange B g V)).symm ≫
        (toSheafify (SmallEtale.topology B Y'.obj Y'.property)
          ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
            ((abPullback.{u, u + 1} B p).obj F))).app (op (baseChange B g V)) := by
  rw [fiberBaseChangePresheafApp]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Stacks 0F5J.** The base-change map sends the germ at the image point of `t` of the
generator of `f_{p!}F` attached to a supported section to the germ at `t` of the generator of
`f'_{p!}(p⁻¹F)` attached to its base change. -/
private theorem fShriekBaseChangeMap_germ_generator
    (U : (geometricPointFiber B Y.obj Y.property (t.map (B.inclusion.map g))).Elements)
    (E : FiniteSupport B f U.1) {Z : AddCommGrpCat.{u + 1}}
    (k : etaleStalk B Y'.obj Y'.property t
      ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)).obj ⟶ Z) :
    colimit.ι (finiteSupportDiagram B f F U.1) E ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F U.1).symm ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property (t.map (B.inclusion.map g))
          ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F))
          (op U) ≫
        etaleStalkSheafificationMap B Y.obj Y.property (t.map (B.inclusion.map g))
          ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F) ≫
        (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F)).inv ≫
        (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
          (fShriekBaseChangeMap.{u} B p f' f g sq F).hom ≫ k =
      fiberBaseChangeDiagramMap.{u, u + 1} B p f' f g sq U.1 F E ≫
        colimit.ι (finiteSupportDiagram B f' ((abPullback.{u, u + 1} B p).obj F)
          (baseChange B g U.1)) (fiberBaseChangeSupport B p f' f g sq U.1 E) ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f'
            (fun _ => inferInstance)).2.obj_eq ((abPullback.{u, u + 1} B p).obj F)
          (baseChange B g U.1)).symm ≫
        colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
            ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
              ((abPullback.{u, u + 1} B p).obj F)))
          (op ⟨(smallEtaleBaseChange B g).obj U.1,
            geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩) ≫
        etaleStalkSheafificationMap B Y'.obj Y'.property t
          ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
            ((abPullback.{u, u + 1} B p).obj F)) ≫ k := by
  set ιE := colimit.ι (finiteSupportDiagram B f F U.1) E with hιE
  set e₁ := eqToHom ((finiteSupportPushforward.{u, u + 1} B f
    (fun _ => inferInstance)).2.obj_eq F U.1).symm with he₁
  set ι₁ := colimit.ι (etaleStalkDiagram B Y.obj Y.property (t.map (B.inclusion.map g))
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F))
      (op U) with hι₁
  set Ψ := etaleStalkSheafificationMap B Y.obj Y.property (t.map (B.inclusion.map g))
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F) with hΨ
  set Γ := (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
    (fShriekBaseChangeMap.{u} B p f' f g sq F).hom with hΓ
  set κ := (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
    ((fShriekFunctor.{u, u + 1} B f).obj F)).inv with hκ
  set τ := (toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F)).app
      (op U.1) with hτ
  set ι₁ₛ := colimit.ι (etaleStalkDiagram B Y.obj Y.property (t.map (B.inclusion.map g))
    ((fShriekFunctor.{u, u + 1} B f).obj F).obj) (op U) with hι₁ₛ
  set ϖ := pullbackSectionAlongHom B g AddCommGrpCat.{u + 1}
    ((fShriekFunctor.{u, u + 1} B f).obj F) U.1
    ((smallEtaleBaseChange B g).obj U.1) (𝟙 _) with hϖ
  set ι₂ := colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
    ((abPullback.{u, u + 1} B g).obj ((fShriekFunctor.{u, u + 1} B f).obj F)).obj)
      (op (⟨(smallEtaleBaseChange B g).obj U.1,
        geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ :
        (geometricPointFiber B Y'.obj Y'.property t).Elements)) with hι₂
  set ι₂ₛ := colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
    ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)).obj)
      (op (⟨(smallEtaleBaseChange B g).obj U.1,
        geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ :
        (geometricPointFiber B Y'.obj Y'.property t).Elements)) with hι₂ₛ
  set γapp := (fShriekBaseChangeMap.{u} B p f' f g sq F).hom.app
    (op ((smallEtaleBaseChange B g).obj U.1)) with hγapp
  set βapp := (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F).hom.app (op U.1)
    with hβapp
  set appV := fiberBaseChangePresheafApp.{u} B p f' f g sq F U.1 with happV
  set cV := fiberBaseChangeColimitMap.{u, u + 1} B p f' f g sq U.1 F with hcV
  set e₂ := eqToHom ((finiteSupportPushforward.{u, u + 1} B f'
      (fun _ => inferInstance)).2.obj_eq ((abPullback.{u, u + 1} B p).obj F)
    (baseChange B g U.1)).symm with he₂
  set τ' := (toSheafify (SmallEtale.topology B Y'.obj Y'.property)
    ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
      ((abPullback.{u, u + 1} B p).obj F))).app (op (baseChange B g U.1)) with hτ'
  set ι₃ := colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
    ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
      ((abPullback.{u, u + 1} B p).obj F)))
      (op (⟨(smallEtaleBaseChange B g).obj U.1,
        geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ :
        (geometricPointFiber B Y'.obj Y'.property t).Elements)) with hι₃
  set Ψ' := etaleStalkSheafificationMap B Y'.obj Y'.property t
    ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
      ((abPullback.{u, u + 1} B p).obj F)) with hΨ'
  set dm := fiberBaseChangeDiagramMap.{u, u + 1} B p f' f g sq U.1 F E with hdm
  set ιE' := colimit.ι (finiteSupportDiagram B f' ((abPullback.{u, u + 1} B p).obj F)
    (baseChange B g U.1)) (fiberBaseChangeSupport B p f' f g sq U.1 E) with hιE'
  have s1 : ιE ≫ e₁ ≫ ι₁ ≫ Ψ ≫ κ ≫ Γ ≫ k = ιE ≫ e₁ ≫ τ ≫ ι₁ₛ ≫ κ ≫ Γ ≫ k :=
    congrArg (fun z => ιE ≫ e₁ ≫ z)
      (comp_reassoc (colimit_ι_comp_etaleStalkSheafificationMap B Y.obj Y.property
        (t.map (B.inclusion.map g))
        ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F) (op U))
        (κ ≫ Γ ≫ k))
  have s2 : ιE ≫ e₁ ≫ τ ≫ ι₁ₛ ≫ κ ≫ Γ ≫ k = ιE ≫ e₁ ≫ τ ≫ ϖ ≫ ι₂ ≫ Γ ≫ k :=
    congrArg (fun z => ιE ≫ e₁ ≫ τ ≫ z)
      (comp_reassoc (etaleStalk_pullObjIso_inv_germ.{u} B f g t F U) (Γ ≫ k))
  have s3 : ιE ≫ e₁ ≫ τ ≫ ϖ ≫ ι₂ ≫ Γ ≫ k =
      ιE ≫ e₁ ≫ τ ≫ ϖ ≫ γapp ≫ ι₂ₛ ≫ k := by
    refine congrArg (fun z => ιE ≫ e₁ ≫ τ ≫ ϖ ≫ z) ?_
    refine comp_reassoc ?_ k
    exact colimit.ι_map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B Y'.obj Y'.property t)).op
        (fShriekBaseChangeMap.{u} B p f' f g sq F).hom)
      (op (⟨(smallEtaleBaseChange B g).obj U.1,
        geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ :
        (geometricPointFiber B Y'.obj Y'.property t).Elements))
  have s4 : ιE ≫ e₁ ≫ τ ≫ ϖ ≫ γapp ≫ ι₂ₛ ≫ k = ιE ≫ e₁ ≫ τ ≫ βapp ≫ ι₂ₛ ≫ k :=
    congrArg (fun z => ιE ≫ e₁ ≫ τ ≫ z)
      (comp_reassoc
        (pullbackSectionAlongHom_comp_fShriekBaseChangeMap.{u} B p f' f g sq F U.1)
        (ι₂ₛ ≫ k))
  have s5 : ιE ≫ e₁ ≫ τ ≫ βapp ≫ ι₂ₛ ≫ k = ιE ≫ e₁ ≫ appV ≫ ι₂ₛ ≫ k :=
    congrArg (fun z => ιE ≫ e₁ ≫ z)
      ((Category.assoc τ βapp (ι₂ₛ ≫ k)).symm.trans
        (congrArg (fun z => z ≫ ι₂ₛ ≫ k)
          (toSheafify_app_comp_fShriekBaseChangePushforwardMap.{u} B p f' f g sq F U.1)))
  have s6 : ιE ≫ e₁ ≫ appV ≫ ι₂ₛ ≫ k = ιE ≫ cV ≫ (e₂ ≫ τ') ≫ ι₂ₛ ≫ k :=
    congrArg (fun z => ιE ≫ z)
      (comp_reassoc (eqToHom_comp_fiberBaseChangePresheafApp.{u} B p f' f g sq F U.1)
        (ι₂ₛ ≫ k))
  have s7 : ιE ≫ cV ≫ (e₂ ≫ τ') ≫ ι₂ₛ ≫ k = ιE ≫ cV ≫ e₂ ≫ τ' ≫ ι₂ₛ ≫ k :=
    congrArg (fun z => ιE ≫ cV ≫ z) (Category.assoc e₂ τ' (ι₂ₛ ≫ k))
  have s8 : ιE ≫ cV ≫ e₂ ≫ τ' ≫ ι₂ₛ ≫ k = ιE ≫ cV ≫ e₂ ≫ ι₃ ≫ Ψ' ≫ k :=
    congrArg (fun z => ιE ≫ cV ≫ e₂ ≫ z)
      (comp_reassoc (colimit_ι_comp_etaleStalkSheafificationMap B Y'.obj Y'.property t
        ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
          ((abPullback.{u, u + 1} B p).obj F))
        (op ⟨(smallEtaleBaseChange B g).obj U.1,
          geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩)).symm k)
  have s9 : ιE ≫ cV ≫ e₂ ≫ ι₃ ≫ Ψ' ≫ k = dm ≫ ιE' ≫ e₂ ≫ ι₃ ≫ Ψ' ≫ k :=
    comp_reassoc (fiberBaseChangeColimitMap_ι.{u, u + 1} B p f' f g sq U.1 F E)
      (e₂ ≫ ι₃ ≫ Ψ' ≫ k)
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans
    (s6.trans (s7.trans (s8.trans s9)))))))

/-- **Stacks 0F5J.** On the stalk at a geometric point `t` of `Y'` the base-change map is the
base-change comparison of stalks: the identification of the stalk of an inverse image, the stalk
decomposition of Stacks 0F5F for `f`, and the comparison of the direct sums of stalks over the
two geometric fibres. -/
@[stacks 0F5J "the base-change map on the stalk at a geometric point, through the 0F5F \
decompositions"]
public theorem fShriekBaseChangeMap_stalk :
    (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
          (fShriekBaseChangeMap.{u} B p f' f g sq F).hom ≫
        (fShriekStalkIso.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)).hom =
      (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F)).hom ≫
        (fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).hom ≫
        (AddEquiv.toAddCommGrpIso
          (fiberStalksBaseChangeEquiv.{u, u + 1} B p f' f g sq t F)).hom := by
  set eqv : AddCommGrpCat.of (fiberStalks.{u, u + 1} B f (t.map (B.inclusion.map g)) F) ⟶
      AddCommGrpCat.of
        (fiberStalks.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)) :=
    (AddEquiv.toAddCommGrpIso
      (fiberStalksBaseChangeEquiv.{u, u + 1} B p f' f g sq t F)).hom with heqv
  refine (cancel_epi (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
    ((fShriekFunctor.{u, u + 1} B f).obj F)).inv).1 ?_
  refine Eq.trans ?_ (Iso.inv_hom_id_assoc _ _).symm
  refine (cancel_epi (etaleStalkSheafificationMap B Y.obj Y.property
    (t.map (B.inclusion.map g))
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F))).1 ?_
  have hR : etaleStalkSheafificationMap B Y.obj Y.property (t.map (B.inclusion.map g))
          ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F) ≫
        (fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).hom ≫ eqv =
      finiteSupportStalkToFiberStalks.{u, u + 1} B f (t.map (B.inclusion.map g)) F
          (fun _ => inferInstance) ≫ eqv :=
    (Category.assoc
        (etaleStalkSheafificationMap B Y.obj Y.property (t.map (B.inclusion.map g))
          ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F))
        (fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).hom eqv).symm.trans
      (congrArg (fun z => z ≫ eqv)
        (fShriekStalkIso_comp_sheafification.{u, u + 1} B f
          (t.map (B.inclusion.map g)) F))
  refine Eq.trans ?_ hR.symm
  refine colimit.hom_ext fun W => ?_
  obtain ⟨U⟩ := W
  refine (cancel_epi (eqToHom ((finiteSupportPushforward.{u, u + 1} B f
    (fun _ => inferInstance)).2.obj_eq F U.1).symm)).1 ?_
  refine colimit.hom_ext fun E => ?_
  have h1 := fShriekBaseChangeMap_germ_generator.{u} B p f' f g sq t F U E
    (fShriekStalkIso.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)).hom
  have h2 := congrArg (fun z => fiberBaseChangeDiagramMap.{u, u + 1} B p f' f g sq U.1 F E ≫
      colimit.ι (finiteSupportDiagram B f' ((abPullback.{u, u + 1} B p).obj F)
          (baseChange B g U.1)) (fiberBaseChangeSupport B p f' f g sq U.1 E) ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f'
            (fun _ => inferInstance)).2.obj_eq ((abPullback.{u, u + 1} B p).obj F)
          (baseChange B g U.1)).symm ≫
        colimit.ι (etaleStalkDiagram B Y'.obj Y'.property t
            ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
              ((abPullback.{u, u + 1} B p).obj F)))
            (op (⟨(smallEtaleBaseChange B g).obj U.1,
              geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩ :
              (geometricPointFiber B Y'.obj Y'.property t).Elements)) ≫ z)
    (fShriekStalkIso_comp_sheafification.{u, u + 1} B f' t
      ((abPullback.{u, u + 1} B p).obj F))
  have h3 := congrArg
    (fun z => fiberBaseChangeDiagramMap.{u, u + 1} B p f' f g sq U.1 F E ≫ z)
    (finiteSupportStalkToFiberStalks_generator.{u, u + 1} B f' t
      ((abPullback.{u, u + 1} B p).obj F) (fun _ => inferInstance)
      ⟨(smallEtaleBaseChange B g).obj U.1,
        geometricPointFiberBaseChangeEquiv B g t U.1 U.2⟩
      (fiberBaseChangeSupport B p f' f g sq U.1 E))
  have h4 := fiberBaseChangeDiagramMap_comp_fiberStalkHom.{u} B p f' f g sq t F U.1 U.2 E
  have h5 := comp_reassoc₄ (finiteSupportStalkToFiberStalks_generator.{u, u + 1} B f
      (t.map (B.inclusion.map g)) F (fun _ => inferInstance) U E) eqv
  exact h1.trans (h2.trans (h3.trans (h4.trans h5.symm)))

/-- **Stacks 0F5J.** The base-change map is, on the stalk at a geometric point of `Y'`, the
base-change isomorphism of stalks of `StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChange`. -/
@[stacks 0F5J "the stalk of the base-change map is the stalkwise base-change isomorphism"]
public theorem fShriekBaseChangeMap_stalk_eq :
    (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
        (fShriekBaseChangeMap.{u} B p f' f g sq F).hom =
      (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq t F).hom :=
  (cancel_mono (fShriekStalkIso.{u, u + 1} B f' t
      ((abPullback.{u, u + 1} B p).obj F)).hom).1
    ((fShriekBaseChangeMap_stalk.{u} B p f' f g sq t F).trans
      (fShriekStalkBaseChangeIso_hom_comp.{u, u + 1} B p f' f g sq t F).symm)

end Stalk

section Iso

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- **Stacks 0F5J.** The base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` is an isomorphism: it is an
isomorphism on the stalk at every geometric point of `Y'`, both sides becoming the direct sum of
the stalks of `F` over the geometric fibre, and a map of abelian étale sheaves which is an
isomorphism on every geometric stalk is an isomorphism, which is Stacks 03PU. -/
@[stacks 0F5J "the base-change map is an isomorphism"]
public instance isIso_fShriekBaseChangeMap :
    IsIso (fShriekBaseChangeMap.{u} B p f' f g sq F) := by
  refine isIso_of_isIso_etaleStalkMap B Y'.obj Y'.property
    (fShriekBaseChangeMap.{u} B p f' f g sq F) fun s => ?_
  rw [fShriekBaseChangeMap_stalk_eq.{u} B p f' f g sq s F]
  exact Iso.isIso_hom (fShriekStalkBaseChangeIso.{u, u + 1} B p f' f g sq s F)

end Iso

section NatIso

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- **Stacks 0F5J.** For a cartesian square with `f` locally quasi-finite there is an
isomorphism `g⁻¹f_!F ≅ f'_!(p⁻¹F)`, functorial in the abelian sheaf `F` on the small étale site
of `X`: the map `c` of the source, sheafified and transposed, which is an isomorphism because it
is one on every geometric stalk. -/
@[stacks 0F5J "the isomorphism g⁻¹f_!F ≅ f'_!(p⁻¹F), functorial in F"]
public def fShriekBaseChangeNatIso :
    fShriekFunctor.{u, u + 1} B f ⋙ abPullback.{u, u + 1} B g ≅
      abPullback.{u, u + 1} B p ⋙ fShriekFunctor.{u, u + 1} B f' :=
  NatIso.ofComponents (fun F => asIso (fShriekBaseChangeMap.{u} B p f' f g sq F))
    (fun φ => (fShriekBaseChangeNatTrans.{u} B p f' f g sq).naturality φ)

/-- The base-change isomorphism is the base-change map. -/
public theorem fShriekBaseChangeNatIso_hom_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app F =
      fShriekBaseChangeMap.{u} B p f' f g sq F :=
  rfl

/-- **Stacks 0F5J.** The base-change isomorphism agrees with the stalk descriptions of
Stacks 0F5F: on the stalk at a geometric point `t` of `Y'` it is the identification of the stalk
of an inverse image followed by the stalk decomposition of `f_!F` at the image point, the
comparison of the direct sums of stalks over the two geometric fibres, and the inverse of the
stalk decomposition of `f'_!(p⁻¹F)`. -/
@[stacks 0F5J "the isomorphism agrees with the stalk descriptions of 0F5F"]
public theorem fShriekBaseChangeNatIso_stalk (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
          ((fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app F).hom ≫
        (fShriekStalkIso.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)).hom =
      (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
          ((fShriekFunctor.{u, u + 1} B f).obj F)).hom ≫
        (fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).hom ≫
        (AddEquiv.toAddCommGrpIso
          (fiberStalksBaseChangeEquiv.{u, u + 1} B p f' f g sq t F)).hom :=
  fShriekBaseChangeMap_stalk.{u} B p f' f g sq t F

end NatIso

section Statement

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0F5J.** For a cartesian square of a big étale site with `f` locally quasi-finite
there is an isomorphism `g⁻¹f_!F ≅ f'_!(p⁻¹F)`, functorial in `F` in the abelian sheaves on the
small étale site of `X`, which agrees with the stalk descriptions of Stacks 0F5F: on the stalk
at a geometric point `t` of `Y'` it is the identification of the stalk of an inverse image, the
stalk decomposition of `f_!F` at the image point, and the comparison of the direct sums of the
stalks over the two geometric fibres.

Only the hypotheses of the source are assumed: the finite-type and quasi-finiteness conditions
on the base change `f'` are supplied from the cartesian square. -/
@[stacks 0F5J "the isomorphism, functorial in the sheaf and compatible with the 0F5F stalk \
descriptions"]
public theorem exists_fShriekBaseChangeIso :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    ∃ e : fShriekFunctor.{u, u + 1} B f ⋙ abPullback.{u, u + 1} B g ≅
        abPullback.{u, u + 1} B p ⋙ fShriekFunctor.{u, u + 1} B f',
      ∀ (t : GeometricPoint Y'.obj)
        (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}),
        (etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map
              (e.hom.app F).hom ≫
            (fShriekStalkIso.{u, u + 1} B f' t ((abPullback.{u, u + 1} B p).obj F)).hom =
          (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1}
              ((fShriekFunctor.{u, u + 1} B f).obj F)).hom ≫
            (fShriekStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F).hom ≫
            (AddEquiv.toAddCommGrpIso
              (fiberStalksBaseChangeEquiv.{u, u + 1} B p f' f g sq t F)).hom := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  exact ⟨fShriekBaseChangeNatIso.{u} B p f' f g sq,
    fShriekBaseChangeNatIso_stalk.{u} B p f' f g sq⟩

end Statement


end Fibre

end AlgebraicGeometry.SmallEtale

end
