module

public import StacksFrontier.Algebra.Category.Grp.ColimitGenerators
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSectionsClopen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SingletonFibreGeometricPoint

/-!
# The surjectivity half of the germ decomposition of a finite-support stalk

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `ȳ` be a geometric
point of `Y` and let `F` be an abelian sheaf on the small étale site of `X`. The canonical map
`(f_{p!}F)_ȳ ⟶ ⊕_{f(x̄) = ȳ} F_x̄` of `StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk` is
proved here to be **surjective**, from one hypothesis about the geometry of `f` and nothing else:
that every germ at a point of the geometric fibre is represented by a section over an *open* of
some base change `X_V` which is finite over `V` and meets the geometric fibre in that single point,
with purely inseparable residue field extension there. That hypothesis is the content of Stacks
63.4.2's appeal to More on Morphisms 37.41.3 and Étale Morphisms 41.14.2; everything the source
derives from it for surjectivity is proved here.

Two things make the reduction work. An open support meeting the geometric fibre in one point
with purely inseparable residue extension meets it in exactly one *geometric* point — a morphism
from the spectrum of a field into the open is determined by its image point and an embedding of the
residue field, and pure inseparability leaves at most one such embedding
(`AlgebraicGeometry.eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable`). And on an open
support the group `H_Z(F)` is the group of sections over `Z`, so a section coming from an étale
neighbourhood of the point of the geometric fibre can be pushed into `H_Z(F)` with its germ
unchanged.

The file also records the description of an element of the stalk which the injectivity half starts
from: a *finite sum* of germs of supported sections. The index of the colimit of Stacks 0F6M is a
partially ordered set and is not filtered — the source says so explicitly, directedness being
asserted only for separated `f` in Stacks 0F6N — so an element of `f_{p!}F(V)` need not come from a
single support, and a finite sum is both what holds and what the argument needs.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteSupport_of_isFinite_opens` — an open of `X_V` finite over
  `V` is an eligible support in the sense of Stacks 0F6M.
* `AlgebraicGeometry.SmallEtale.eq_of_fiberPointLift_mem_of_preimage_singleton` — at most one point
  of the geometric fibre lifts into such an open when its fibre over the chosen point of `V` is a
  single point with purely inseparable residue extension.
* `AlgebraicGeometry.SmallEtale.fiberStalkComponent_openSupport` — the component of the germ
  decomposition at that point is the germ of the section it was transported from.
* `AlgebraicGeometry.SmallEtale.fiberStalkSum_eq_of_unique` — the germ decomposition of a section
  supported on a support met by exactly one point of the geometric fibre is concentrated in that
  one summand.
* `AlgebraicGeometry.SmallEtale.exists_preimage_of_openFiniteSupport` and
  `AlgebraicGeometry.SmallEtale.surjective_finiteSupportStalkToFiberStalks_of_exists_openSupport` —
  the preimage of a single-summand germ, and surjectivity of the germ decomposition map.
* `AlgebraicGeometry.SmallEtale.exists_colimitListSum_finiteSupportDiagram` and
  `AlgebraicGeometry.SmallEtale.exists_listSum_generators_eq_etaleStalk` — every finite-support
  section over an étale neighbourhood, and every element of the stalk, is a finite sum of
  generators.

## Implementation notes

The geometric hypothesis of
`AlgebraicGeometry.SmallEtale.surjective_finiteSupportStalkToFiberStalks_of_exists_openSupport` is
carried as an explicit named hypothesis rather than proved, and the theorem therefore carries no
Stacks attribute: it is not Tag 0F6P, which also asserts injectivity and asserts surjectivity
unconditionally. What it does is to make the outstanding content of the surjectivity half a
statement about schemes alone, with no reference to the small étale site, to supported sections or
to the stalk.

Pure inseparability is assumed in the `RingHom.IsPurelyInseparable` form, which is the form
Stacks 02LM (`AlgebraicGeometry.exists_etale_finite_opens_of_isolated_fiber_points`) produces, so
that the hypothesis can be discharged from that lemma without transport.

The étale neighbourhood of the geometric point of `Y` is taken as a single object `U` of the
category of elements of `AlgebraicGeometry.geometricPointFiber` rather than as a pair of an object
of the site and a lift. That is the form the outer colimit is indexed by, and taking it apart into
a pair makes the reassociation of the triple composite of colimit injections fail its
type-correctness check.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 02LM](https://stacks.math.columbia.edu/tag/02LM)
* [Stacks Project, Tag 04DH](https://stacks.math.columbia.edu/tag/04DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section OpenSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)

/-- An open of `X_V` whose structure morphism to `V` is finite is an eligible support. -/
public theorem isFiniteSupport_of_isFinite_opens (V : SmallEtale B Y.obj Y.property)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens)
    (hfin : IsFinite (O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f))) :
    IsFiniteSupport B f V (O : Set ((SmallEtale.toScheme B X.obj X.property).obj
      (baseChange B f V))) :=
  ⟨O.toScheme, O.ι, inferInstance, hfin, O.range_ι⟩

/-- If a morphism factors through an open `O` via `m`, each of its points lies in `O`. -/
private theorem base_mem_opens_of_comp_eq {X T : Scheme.{u}} (O : X.Opens) (m : T ⟶ O.toScheme)
    (e : T ⟶ X) (hp : m ≫ O.ι = e) (t : T) : e.base t ∈ (O : Set X) := by
  rw [← hp, ← Scheme.Opens.range_ι O]
  exact ⟨m.base t, rfl⟩

/-- A point of the geometric fibre whose lift meets an open of `X_V` has its whole image in it. -/
public theorem fiberPointLift_range_subset_opens (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (x : GeometricFiberPoint B f s)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens)
    (hx : (fiberPointLift B f s V u x).base default ∈
      (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)))) :
    Set.range (fiberPointLift B f s V u x).base ⊆ Set.range O.ι.base := by
  rintro _ ⟨z, rfl⟩
  rw [Subsingleton.elim z default, Scheme.Opens.range_ι]
  exact hx

/-- **Uniqueness of the point of the geometric fibre lifting into a singleton-fibre open.** -/
public theorem eq_of_fiberPointLift_mem_of_preimage_singleton (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens)
    (z : O.toScheme)
    (hfib : (O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)).base ⁻¹'
        {(O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)).base z} = {z})
    (hpure : RingHom.IsPurelyInseparable
      ((O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)).residueFieldMap z).hom)
    (hz : (O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f)).base z = u.1.base default)
    (x x' : GeometricFiberPoint B f s)
    (hx : (fiberPointLift B f s V u x).base default ∈
      (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))))
    (hx' : (fiberPointLift B f s V u x').base default ∈
      (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)))) :
    x = x' := by
  set g := O.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f) with hg
  have key : ∀ (y : GeometricFiberPoint B f s),
      (fiberPointLift B f s V u y).base default ∈
        (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))) →
      ∃ l : s.source ⟶ O.toScheme, l ≫ O.ι = fiberPointLift B f s V u y ∧
        l ≫ g = u.1 ∧ l.base (IsLocalRing.closedPoint s.residueField) = z := by
    intro y hy
    set l := IsOpenImmersion.lift O.ι (fiberPointLift B f s V u y)
      (fiberPointLift_range_subset_opens B f s V u y O hy) with hl
    have hlO : l ≫ O.ι = fiberPointLift B f s V u y := IsOpenImmersion.lift_fac _ _ _
    have hlg : l ≫ g = u.1 := by
      rw [hg, ← Category.assoc, hlO]
      exact fiberPointLift_comp_fst B f s V u y
    refine ⟨l, hlO, hlg, ?_⟩
    have hmem : l.base (IsLocalRing.closedPoint s.residueField) ∈ g.base ⁻¹' {g.base z} := by
      change g.base _ = g.base z
      rw [hz]
      exact (congrArg (fun m : s.source ⟶ (SmallEtale.toScheme B Y.obj Y.property).obj V =>
        m.base (IsLocalRing.closedPoint s.residueField)) hlg).trans
        (congrArg u.1.base (Subsingleton.elim _ _))
    rwa [hfib] at hmem
  obtain ⟨l, hl, hlg, hlz⟩ := key x hx
  obtain ⟨l', hl', hl'g, hl'z⟩ := key x' hx'
  have hll : l = l' :=
    eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable g z hfib l l'
      (hlg.trans hl'g.symm) hlz hpure
  have hfl : fiberPointLift B f s V u x = fiberPointLift B f s V u x' := by
    rw [← hl, ← hl', hll]
  exact Subtype.ext ((fiberPointLift_comp_snd B f s V u x).symm.trans
    ((congrArg (fun m => m ≫ B.inclusion.map (pullback.snd V.obj.hom f)) hfl).trans
      (fiberPointLift_comp_snd B f s V u x')))

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})

/-- Every element of the group of finite-support sections over an étale neighbourhood is a finite
sum of sections supported on individual eligible supports. The index of the colimit of Stacks 0F6M
is only a partially ordered set, not a filtered category, so an element need not come from a single
support; a finite sum is all that holds, and all that is needed. -/
public theorem exists_colimitListSum_finiteSupportDiagram (V : SmallEtale B Y.obj Y.property)
    [Small.{max u v} (FiniteSupport B f V)] (g : ↑(finiteSupportSections B f F V)) :
    ∃ l : List ((E : FiniteSupport B f V) × ↑((finiteSupportDiagram B f F V).obj E)),
      AddCommGrpCat.colimitListSum (finiteSupportDiagram B f F V) l = g :=
  AddCommGrpCat.exists_colimitListSum_eq _ g

/-- The germ decomposition of a section transported from an étale neighbourhood of a point of the
geometric fibre onto an open support: its component at that point is the germ there. -/
public theorem fiberStalkComponent_openSupport (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens)
    (hO : IsFiniteSupport B f V (O : Set ((SmallEtale.toScheme B X.obj X.property).obj
      (baseChange B f V))))
    (x : GeometricFiberPoint B f s) (W : SmallEtale B X.obj X.property)
    (q : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj W)
    (a₀ : F.obj.obj (op W))
    (τ : openObject B X.obj X.property (baseChange B f V) O ⟶ W)
    (p : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj
      (openObject B X.obj X.property (baseChange B f V) O))
    (hτ : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).map τ p = q)
    (hp : p.1 ≫ O.ι = fiberPointLift B f s V u x) :
    fiberStalkComponent B f s F V u ⟨(O : Set _), hO⟩
        ((supportedSectionsOpenEquivSections B X.obj X.property F (baseChange B f V) O
          (finiteSupport_isLocallyClosed B f V ⟨(O : Set _), hO⟩)).symm
          (F.obj.map τ.op a₀)) x =
      etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj W q a₀ := by
  set E : FiniteSupport B f V := ⟨(O : Set _), hO⟩ with hE
  set hZ := finiteSupport_isLocallyClosed B f V E with hZdef
  set a := (supportedSectionsOpenEquivSections B X.obj X.property F (baseChange B f V) O hZ).symm
    (F.obj.map τ.op a₀) with hadef
  have hle : O ≤ finiteSupportOpen B f V E :=
    subset_supportOpen B X.obj X.property (baseChange B f V) (O : Set _) hZ
  have hmem : HasFiberLift B f s V u E x := by
    exact hle (base_mem_opens_of_comp_eq O p.1 _ hp _)
  rw [fiberStalkComponent_of_hasFiberLift B f s F V u E a x hmem]
  have hmap : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).map
      (openObjectHomOfLE B X.obj X.property (baseChange B f V) hle) p =
      openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
        (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) hmem := by
    refine openObjectLift_ext B X.obj X.property (x.toGeometricPoint B f s)
      (baseChange B f V) (finiteSupportOpen B f V E) _ _ ?_
    refine Eq.trans ?_ (openObjectLift_comp_ι B X.obj X.property (x.toGeometricPoint B f s)
      (baseChange B f V) (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) hmem).symm
    show (p.1 ≫ (SmallEtale.toScheme B X.obj X.property).map
      (openObjectHomOfLE B X.obj X.property (baseChange B f V) hle)) ≫
      (finiteSupportOpen B f V E).ι = fiberPointLift B f s V u x
    rw [openObjectHomOfLE_map, Category.assoc, Scheme.homOfLE_ι]
    exact hp
  have hrestr : F.obj.map (openObjectHomOfLE B X.obj X.property (baseChange B f V) hle).op a.val =
      F.obj.map τ.op a₀ := by
    have h1 := supportedSectionsOpenEquivSections_apply B X.obj X.property F
      (baseChange B f V) O hZ a
    rw [hadef, AddEquiv.apply_symm_apply] at h1
    exact h1.symm
  have h2 := etaleGerm_map B X.obj X.property (x.toGeometricPoint B f s) F.obj
    (openObjectHomOfLE B X.obj X.property (baseChange B f V) hle)
    (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
      (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) hmem) p hmap a.val
  exact h2.symm.trans ((congrArg (etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj
      (openObject B X.obj X.property (baseChange B f V) O) p) hrestr).trans
    (etaleGerm_map B X.obj X.property (x.toGeometricPoint B f s) F.obj τ q p hτ a₀))

variable [LocallyOfFiniteType (B.inclusion.map f)]

open Classical in
/-- If exactly one point of the geometric fibre lifts into the support, the germ decomposition of
a section supported on it is concentrated in that summand. -/
public theorem fiberStalkSum_eq_of_unique (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))
    (x : GeometricFiberPoint B f s)
    (huniq : ∀ x' : GeometricFiberPoint B f s,
      (fiberPointLift B f s V u x').base default ∈ E.1 → x' = x) :
    fiberStalkSum B f s F V u E a =
      DirectSum.of (fun y : GeometricFiberPoint B f s =>
        ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x
        (fiberStalkComponent B f s F V u E a x) := by
  refine DFinsupp.ext fun y => ?_
  by_cases hy : y = x
  · subst hy
    rw [fiberStalkSum_apply, DirectSum.of_eq_same]
  · rw [fiberStalkSum_apply, DirectSum.of_eq_of_ne _ _ _ hy]
    exact fiberStalkComponent_eq_zero_of_notMem B f s F V u E a y
      (fun hmem => hy (huniq y hmem))

variable [LocallyQuasiFinite (B.inclusion.map f)]

open Classical in
/-- **The surjectivity input of Stacks 0F6P, discharged.** The preimage of a single-summand germ
under the germ decomposition map, produced from an open of `X_V` finite over the étale
neighbourhood `V` of the geometric point of `Y` which meets the geometric fibre in a single point
with purely inseparable residue extension, and which maps to the étale neighbourhood of the point
of the geometric fibre carrying the germ. -/
public theorem exists_preimage_of_openFiniteSupport
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
    (x : GeometricFiberPoint B f s) (W : SmallEtale B X.obj X.property)
    (q : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj W)
    (a₀ : F.obj.obj (op W))
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens)
    (z : O.toScheme)
    (τ : openObject B X.obj X.property (baseChange B f U.1) O ⟶ W)
    (p : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj
      (openObject B X.obj X.property (baseChange B f U.1) O))
    (hfin : IsFinite (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)))
    (hfib : (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base ⁻¹'
      {(O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base z} = {z})
    (hz : (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base z = U.2.1.base default)
    (hpure : RingHom.IsPurelyInseparable
      ((O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).residueFieldMap z).hom)
    (hτ : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).map τ p = q)
    (hp : p.1 ≫ O.ι = fiberPointLift B f s U.1 U.2 x) :
    ∃ g, finiteSupportStalkToFiberStalks B f s F hsmall g =
      DirectSum.of (fun y : GeometricFiberPoint B f s =>
        ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x
        (etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj W q a₀) := by
  have hO : IsFiniteSupport B f U.1
      (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) :=
    isFiniteSupport_of_isFinite_opens B f U.1 O hfin
  set E : FiniteSupport B f U.1 := ⟨(O : Set _), hO⟩ with hE
  set a := (supportedSectionsOpenEquivSections B X.obj X.property F (baseChange B f U.1) O
    (finiteSupport_isLocallyClosed B f U.1 E)).symm (F.obj.map τ.op a₀) with hadef
  have hxmem : (fiberPointLift B f s U.1 U.2 x).base default ∈ E.1 := by
    exact base_mem_opens_of_comp_eq O p.1 _ hp _
  have huniq : ∀ x' : GeometricFiberPoint B f s,
      (fiberPointLift B f s U.1 U.2 x').base default ∈ E.1 → x' = x := fun x' hx' =>
    eq_of_fiberPointLift_mem_of_preimage_singleton B f s U.1 U.2 O z hfib hpure hz x' x hx' hxmem
  have hcomp : (colimit.ι (finiteSupportDiagram B f F U.1) E ≫
      (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
      colimit.ι (etaleStalkDiagram B Y.obj Y.property s
        ((finiteSupportPushforward B f hsmall).1.obj F)) (op U))) ≫
      finiteSupportStalkToFiberStalks B f s F hsmall = fiberStalkHom B f s F U.1 U.2 E :=
    ((Category.assoc _ _ _).trans
      (congrArg (fun m => colimit.ι (finiteSupportDiagram B f F U.1) E ≫ m)
        (Category.assoc _ _ _))).trans
      (finiteSupportStalkToFiberStalks_generator B f s F hsmall U E)
  refine ⟨(colimit.ι (finiteSupportDiagram B f F U.1) E ≫
    (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
    colimit.ι (etaleStalkDiagram B Y.obj Y.property s
      ((finiteSupportPushforward B f hsmall).1.obj F)) (op U))) a, ?_⟩
  have h4 : finiteSupportStalkToFiberStalks B f s F hsmall
      ((colimit.ι (finiteSupportDiagram B f F U.1) E ≫
        (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward B f hsmall).1.obj F)) (op U))) a) =
      fiberStalkHom B f s F U.1 U.2 E a :=
    ConcreteCategory.congr_hom hcomp a
  rw [h4, fiberStalkHom_apply, fiberStalkSum_eq_of_unique B f s F U.1 U.2 E a x huniq]
  exact congrArg (DirectSum.of (fun y : GeometricFiberPoint B f s =>
    ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x)
    (fiberStalkComponent_openSupport B f s F U.1 U.2 O hO x W q a₀ τ p hτ hp)

open Classical in
/-- **The surjectivity half of Stacks 0F6P, reduced to one scheme-theoretic statement.** The germ
decomposition map is surjective as soon as every germ at a point of the geometric fibre is
represented on an open of some `X_V` which is finite over `V` and meets the geometric fibre in that
one point with purely inseparable residue extension. -/
public theorem surjective_finiteSupportStalkToFiberStalks_of_exists_openSupport
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
    (hgeom : ∀ (x : GeometricFiberPoint B f s) (W : SmallEtale B X.obj X.property)
      (q : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj W),
      ∃ (U : (geometricPointFiber B Y.obj Y.property s).Elements)
        (O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens)
        (z : O.toScheme)
        (τ : openObject B X.obj X.property (baseChange B f U.1) O ⟶ W)
        (p : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).obj
          (openObject B X.obj X.property (baseChange B f U.1) O)),
        IsFinite (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) ∧
        (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base ⁻¹'
            {(O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base z} = {z} ∧
        (O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base z = U.2.1.base default ∧
        RingHom.IsPurelyInseparable
          ((O.ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).residueFieldMap z).hom ∧
        (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).map τ p = q ∧
        p.1 ≫ O.ι = fiberPointLift B f s U.1 U.2 x) :
    Function.Surjective (finiteSupportStalkToFiberStalks B f s F hsmall) := by
  refine surjective_finiteSupportStalkToFiberStalks_of_exists_preimage B f s F hsmall ?_
  intro x W q a₀
  obtain ⟨U, O, z, τ, p, hfin, hfib, hz, hpure, hτ, hp⟩ := hgeom x W q
  exact exists_preimage_of_openFiniteSupport B f s F hsmall x W q a₀ U O z τ p hfin hfib hz
    hpure hτ hp

/-- Every element of the stalk of the finite-support direct image is a finite sum of generators:
there are an étale neighbourhood of the geometric point of `Y` and finitely many pairs of an
eligible support over it and a section supported on that support, whose germs add up to the given
element. This is the description of an element of the stalk that the injectivity half of Stacks
0F6P starts from. -/
public theorem exists_listSum_generators_eq_etaleStalk
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
    (g : ↑(etaleStalk B Y.obj Y.property s ((finiteSupportPushforward B f hsmall).1.obj F))) :
    ∃ (U : (geometricPointFiber B Y.obj Y.property s).Elements)
      (l : List ((E : FiniteSupport B f U.1) × ↑((finiteSupportDiagram B f F U.1).obj E))),
      (l.map (fun pr => (colimit.ι (finiteSupportDiagram B f F U.1) pr.1 ≫
        eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward B f hsmall).1.obj F)) (op U)) pr.2)).sum = g := by
  obtain ⟨V, u, c, hc⟩ := exists_etaleGerm_eq B Y.obj Y.property s
    ((finiteSupportPushforward B f hsmall).1.obj F) g
  let : Small.{max u v} (FiniteSupport B f V) := hsmall V
  obtain ⟨l, hl⟩ := exists_colimitListSum_finiteSupportDiagram B f F V
    (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F V) c)
  refine ⟨⟨V, u⟩, l, ?_⟩
  have hcl : (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F V).symm ≫
      colimit.ι (etaleStalkDiagram B Y.obj Y.property s
        ((finiteSupportPushforward B f hsmall).1.obj F))
        (op (⟨V, u⟩ : (geometricPointFiber B Y.obj Y.property s).Elements)))
      (AddCommGrpCat.colimitListSum (finiteSupportDiagram B f F V) l) = g := by
    rw [hl]
    refine Eq.trans ?_ hc
    have h0 : eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F V) ≫
        eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F V).symm = 𝟙 _ := by
      rw [eqToHom_trans, eqToHom_refl]
    exact congrArg (colimit.ι (etaleStalkDiagram B Y.obj Y.property s
      ((finiteSupportPushforward B f hsmall).1.obj F))
      (op (⟨V, u⟩ : (geometricPointFiber B Y.obj Y.property s).Elements)))
      (ConcreteCategory.congr_hom h0 c)
  refine Eq.trans ?_ hcl
  rw [AddCommGrpCat.colimitListSum_eq]
  refine Eq.trans ?_ (map_list_sum
    (eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F V).symm ≫
      colimit.ι (etaleStalkDiagram B Y.obj Y.property s
        ((finiteSupportPushforward B f hsmall).1.obj F))
        (op (⟨V, u⟩ : (geometricPointFiber B Y.obj Y.property s).Elements))).hom
    (l.map (fun pr => (colimit.ι (finiteSupportDiagram B f F V) pr.1) pr.2))).symm
  rw [List.map_map]
  rfl

end OpenSupport

end AlgebraicGeometry.SmallEtale

end
