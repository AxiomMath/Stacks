module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Rational maps at the generic points of the source

For schemes `X` and `Y` over `S`, with finitely many irreducible components of `X`, an
`S`-rational map determines a point of `Y` and a local map on stalks over `S` at the generic
point of every component.

A rational map is an equivalence class of partial maps defined on dense opens. Every dense open
contains all the chosen generic points, because the complement of the other components is open
and nonempty inside the component in question; so a representative can be evaluated at each
generic point, and representatives that agree on a dense open agree there. That is what makes
the assignment well defined on the equivalence class.

## Main definitions

* `AlgebraicGeometry.GenericPointMapContext` packages the schemes, their structure morphisms,
  and an enumeration of the irreducible components and their generic points.
* `AlgebraicGeometry.GenericPointMapContext.RationalMapsOver` is the type of rational maps
  commuting with the structure morphisms.
* `AlgebraicGeometry.GenericPointMapContext.GenericPointLocalMap` is a point over the relevant
  point of `S` together with a local map of stalks over `S`.
* `AlgebraicGeometry.GenericPointMapContext.GenericPointMap` specifies the generic-point map by
  its values on representatives.
* `AlgebraicGeometry.GenericPointMapContext.genericPointMapForRationalMaps` constructs this map.

## Main results

* `AlgebraicGeometry.GenericPointMapContext.nonempty_genericPointMap` asserts existence of the
  map with both its point and stalk characterizations.

## Implementation notes

The components are enumerated by `Fin n`, allowing `n = 0` for the empty source. The image of a
generic point in the base is expressed using the source's structure morphism rather than stored
as additional data.

An `S`-rational map is represented by the subtype of rational maps whose composition with
`Y ⟶ S` is the rational map associated to `X ⟶ S`. By
`AlgebraicGeometry.Scheme.RationalMap.isOver_iff`, this is equivalent to having an `S`-morphism
as representative.

The construction includes its characterization on every representative which is an
`S`-morphism. Every dense open contains the chosen generic points. Heterogeneous equality
expresses the stalk map without an artificial transport along the equality of its image point.
Compatibility with the base is expressed by a commuting diagram of stalk maps, with transport
along the equality of the two points of `S`.

## References

* [Stacks Project, Section 29.49, Lemma 0BX8](https://stacks.math.columbia.edu/tag/0BX8)
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry



/-- The context in which rational maps are evaluated at the generic points of
the finitely many irreducible components of their source. -/
public structure GenericPointMapContext where
  S : Scheme.{u}
  X : Scheme.{u}
  Y : Scheme.{u}
  toBaseSource : X ⟶ S
  toBaseTarget : Y ⟶ S
  numberOfComponents : ℕ
  components : Fin numberOfComponents ≃ {Z : Set X // Z ∈ irreducibleComponents X}
  genericPoint : Fin numberOfComponents → X
  isGenericPoint : ∀ i, IsGenericPoint (genericPoint i) (components i : Set X)

namespace GenericPointMapContext

variable (C : GenericPointMapContext.{u})

/-- Rational maps in the context which commute with the structure morphisms. -/
public abbrev RationalMapsOver :=
  {f : C.X.RationalMap C.Y //
    f.compHom C.toBaseTarget = C.toBaseSource.toRationalMap}

/-- The datum at one generic point: a point of the target over the corresponding
point of the base, and a local homomorphism of stalks compatible with the base. -/
public structure GenericPointLocalMap (i : Fin C.numberOfComponents) where
  point : C.Y
  mapsTo : C.toBaseTarget point = C.toBaseSource (C.genericPoint i)
  stalkMap : C.Y.presheaf.stalk point ⟶ C.X.presheaf.stalk (C.genericPoint i)
  isLocalHom : IsLocalHom stalkMap.hom
  commutes :
    C.toBaseTarget.stalkMap point ≫ stalkMap =
      eqToHom (congrArg (fun x ↦ C.S.presheaf.stalk x) mapsTo) ≫
        C.toBaseSource.stalkMap (C.genericPoint i)

/-- A map from rational maps over the base to their generic-point data, together
with its characterization on every representative defined at the chosen generic
points and commuting with the structure maps. -/
public structure GenericPointMap where
  toFun : C.RationalMapsOver → ∀ i, C.GenericPointLocalMap i
  map_point (f : C.RationalMapsOver) (g : C.X.PartialMap C.Y)
      (represents : g.toRationalMap = f.1)
      (over : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ C.toBaseSource)
      (mem : ∀ i, C.genericPoint i ∈ g.domain) (i) :
      (toFun f i).point = g.hom ⟨C.genericPoint i, mem i⟩
  map_stalk (f : C.RationalMapsOver) (g : C.X.PartialMap C.Y)
      (represents : g.toRationalMap = f.1)
      (over : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ C.toBaseSource)
      (mem : ∀ i, C.genericPoint i ∈ g.domain) (i) :
      HEq (toFun f i).stalkMap
        (g.hom.stalkMap ⟨C.genericPoint i, mem i⟩ ≫
          (g.domain.stalkIso ⟨C.genericPoint i, mem i⟩).hom)

/-- A generic-point map is applied to a rational map over the base through its `toFun`. -/
public instance : CoeFun C.GenericPointMap
    (fun _ ↦ C.RationalMapsOver → ∀ i, C.GenericPointLocalMap i) :=
  ⟨GenericPointMap.toFun⟩

/-- The irreducible components of `C.X` form a finite set: they are indexed by
`Fin C.numberOfComponents`. -/
public lemma finite_irreducibleComponents :
    (irreducibleComponents C.X).Finite := by
  let : Fintype {Z : Set C.X // Z ∈ irreducibleComponents C.X} :=
    Fintype.ofEquiv (Fin C.numberOfComponents) C.components
  exact Set.toFinite _

/-- A dense open contains the chosen generic point of every irreducible component. -/
public lemma genericPoint_mem_dense_open (U : C.X.Opens) (hU : Dense (U : Set C.X))
    (i : Fin C.numberOfComponents) : C.genericPoint i ∈ U := by
  let Z : Set C.X := C.components i
  have hZ : Z ∈ irreducibleComponents C.X := (C.components i).property
  let V : Set C.X := (⋃₀ (irreducibleComponents C.X \ {Z}))ᶜ
  have hVopen : IsOpen V := by
    rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact C.finite_irreducibleComponents.sdiff.isClosed_biUnion
      (fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1)
  have hVne : V.Nonempty := by
    by_contra hV
    rw [Set.not_nonempty_iff_eq_empty] at hV
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      C.finite_irreducibleComponents Z hZ
    change closure V = Z at hcl
    rw [hV, closure_empty] at hcl
    rw [← hcl] at hZ
    exact Set.not_nonempty_empty hZ.1.1
  obtain ⟨x, hxV, hxU⟩ := hU.inter_open_nonempty V hVopen hVne
  apply (IsGenericPoint.mem_open_set_iff (C.isGenericPoint i) U.2).2
  refine ⟨x, ?_, hxU⟩
  have hxcl : x ∈ closure V := subset_closure hxV
  rw [closure_sUnion_irreducibleComponents_sdiff_singleton
    C.finite_irreducibleComponents Z hZ] at hxcl
  exact hxcl

/-- The stalk comparison isomorphism along an equality of points is `eqToHom`. -/
public lemma stalkCongr_hom_eqToHom {T : TopCat.{u}} (F : T.Presheaf CommRingCat)
    {x y : T} (h : x = y) :
    (F.stalkCongr (.of_eq h)).hom = eqToHom (congrArg F.stalk h) := by
  subst y
  simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]

private lemma heq_of_stalkCongr_eq {Y : Scheme.{u}} {x y : Y} {R : CommRingCat}
    {f : Y.presheaf.stalk x ⟶ R} {g : Y.presheaf.stalk y ⟶ R}
    (h : x = y)
    (H : f = (Y.presheaf.stalkCongr (.of_eq h)).hom ≫ g) : HEq f g := by
  cases h
  simpa using H

private lemma heq_of_stalkCongr_right {Y : Scheme.{u}} {x y : Y} {R : CommRingCat}
    {f : R ⟶ Y.presheaf.stalk y} {g : R ⟶ Y.presheaf.stalk x}
    (h : x = y)
    (H : g ≫ (Y.presheaf.stalkCongr (.of_eq h)).hom = f) : HEq f g := by
  cases h
  simpa using H.symm

/-- Two maps into stalks at equal points are heterogeneously equal when one factors
through the other along `eqToHom`. -/
public lemma heq_of_eqToHom_right {X : Scheme.{u}} {x y : X} {R : CommRingCat}
    {f : R ⟶ X.presheaf.stalk x} {g : R ⟶ X.presheaf.stalk y}
    (h : x = y)
    (H : f = g ≫ eqToHom (congrArg X.presheaf.stalk h.symm)) : HEq f g := by
  cases h
  simpa using H

/-- A dependent function takes heterogeneously equal values at equal arguments. -/
public lemma heq_apply_of_eq {α : Sort u} {β : α → Sort v}
    (f : ∀ a, β a) {x y : α} (h : x = y) : HEq (f x) (f y) := by
  cases h
  rfl

private lemma homOfLE_stalkMap_stalkIso_eq {X : Scheme.{u}} (U V : X.Opens)
    (h : U ≤ V) (x : U) :
    HEq ((X.homOfLE h).stalkMap x ≫ (U.stalkIso x).hom)
      ((V.stalkIso (X.homOfLE h x)).hom) := by
  let r := (𝟙 X : X ⟶ X).resLE V U h
  have hres : r = X.homOfLE h := Scheme.Hom.resLE_id h
  let iso := (𝟙 X : X ⟶ X).resLEStalkMap (U := V) (V := U) h x
  have hp' : V.ι (X.homOfLE h x) = (x : X) := by
    have hp' := congrArg (fun q : U.toScheme ⟶ X => q x) (X.homOfLE_ι h)
    change V.ι (X.homOfLE h x) = U.ι x at hp'
    simpa only [Scheme.Opens.ι_apply] using hp'
  have hx : r x = X.homOfLE h x :=
    congrArg (fun k : U.toScheme ⟶ V.toScheme => k x) hres
  have hp : V.ι (r x) = (x : X) := (congrArg V.ι hx).trans hp'
  have hcomp :
      (V.stalkIso (r x)).hom ≫
          (X.presheaf.stalkCongr (.of_eq hp)).hom =
        r.stalkMap x ≫ (U.stalkIso x).hom := by
    have hw := iso.hom.w
    change
      (V.stalkIso (r x)).hom ≫
          (X.presheaf.stalkCongr (.of_eq hp)).hom ≫
            (Scheme.Hom.stalkMap (𝟙 X) (x : X)) =
        r.stalkMap x ≫ (U.stalkIso x).hom
      at hw
    rw [Scheme.Hom.stalkMap_id] at hw
    calc
      _ = ((V.stalkIso (r x)).hom ≫
          (X.presheaf.stalkCongr (.of_eq hp)).hom) ≫
            𝟙 (X.presheaf.stalk (x : X)) := (Category.comp_id _).symm
      _ = _ := hw
  have hmain := heq_of_stalkCongr_right hp hcomp
  have hmap := Scheme.Hom.stalkMap_congr_hom r (X.homOfLE h) hres x
  have hmap' : r.stalkMap x ≫ (U.stalkIso x).hom =
      (V.toScheme.presheaf.stalkCongr (.of_eq hx)).hom ≫
        ((X.homOfLE h).stalkMap x ≫ (U.stalkIso x).hom) := by
    rw [hmap]
    simp only [Category.assoc]
  have hmap'' := heq_of_stalkCongr_eq hx hmap'
  have hiso : HEq (V.stalkIso (r x)).hom (V.stalkIso (X.homOfLE h x)).hom :=
    heq_apply_of_eq (fun z => (V.stalkIso z).hom) hx
  exact hmap''.symm.trans (hmain.trans hiso)

/-- The stalk map of a partial map restricted to a smaller open, at a point over `x`, agrees
with the stalk map of the partial map at `x`. -/
private lemma stalkMap_homOfLE_comp_heq {X Y : Scheme.{u}} (f : X.PartialMap Y) (W : X.Opens)
    (hW : W ≤ f.domain) (z : W) (x : f.domain) (h : X.homOfLE hW z = x) :
    HEq ((X.homOfLE hW ≫ f.hom).stalkMap z ≫ (W.stalkIso z).hom)
      (f.hom.stalkMap x ≫ (f.domain.stalkIso x).hom) := by
  subst h
  have hp : f.domain.ι (X.homOfLE hW z) = W.ι z :=
    (Scheme.Hom.comp_apply (X.homOfLE hW) f.domain.ι z).symm.trans
      (congrArg (fun k : W.toScheme ⟶ X ↦ k z) (X.homOfLE_ι hW))
  have hs : (X.homOfLE hW ≫ f.hom).stalkMap z =
      f.hom.stalkMap (X.homOfLE hW z) ≫ (X.homOfLE hW).stalkMap z :=
    Scheme.Hom.stalkMap_comp _ _ _
  rw [hs]
  refine (heq_of_eq (Category.assoc _ _ _)).trans (CategoryTheory.heq_comp
    (f := f.hom.stalkMap (X.homOfLE hW z))
    (g := (X.homOfLE hW).stalkMap z ≫ (W.stalkIso z).hom)
    (f' := f.hom.stalkMap (X.homOfLE hW z))
    (g' := (f.domain.stalkIso (X.homOfLE hW z)).hom)
    rfl rfl (congrArg X.presheaf.stalk hp.symm) HEq.rfl
    (homOfLE_stalkMap_stalkIso_eq W f.domain hW z))

private noncomputable def genericPointLocalMapOfPartial
    (g : C.X.PartialMap C.Y)
    (over : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ C.toBaseSource)
    (i : Fin C.numberOfComponents) : C.GenericPointLocalMap i := by
  -- The point is written out as `⟨C.genericPoint i, hx⟩` rather than abbreviated by a `let`.
  -- A `let`-bound point blocks the projection `z.1` from reducing to `C.genericPoint i` at the
  -- transparency `rw` and `simp` build their motives at, which leaves the `commutes` goal
  -- ill-typed there and defeats every rewrite — including `Category.assoc`.
  have hx : C.genericPoint i ∈ g.domain :=
    C.genericPoint_mem_dense_open g.domain g.dense_domain i
  have mapsTo : C.toBaseTarget (g.hom ⟨C.genericPoint i, hx⟩) =
      C.toBaseSource (C.genericPoint i) :=
    congrArg (fun k : g.domain.toScheme ⟶ C.S ↦ k ⟨C.genericPoint i, hx⟩) over
  refine
    { point := g.hom ⟨C.genericPoint i, hx⟩
      mapsTo := mapsTo
      stalkMap := g.hom.stalkMap ⟨C.genericPoint i, hx⟩ ≫
        (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom
      isLocalHom := by
        change IsLocalHom
          ((g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom.hom.comp
            (g.hom.stalkMap ⟨C.genericPoint i, hx⟩).hom)
        have : IsLocalHom (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom.hom := ⟨by
          intro a ha
          have ha' := ha.map (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).inv.hom
          simpa using ha'⟩
        have : IsLocalHom (g.hom.stalkMap ⟨C.genericPoint i, hx⟩).hom :=
          g.hom.prop ⟨C.genericPoint i, hx⟩
        exact RingHom.isLocalHom_comp _ _
      commutes := ?_ }
  -- Both `stalkMap_comp` instances are introduced as separately annotated equations, so their
  -- statements are elaborated (at full transparency) in the spelling the goal uses, and the
  -- rewrites below never have to bridge `↥g.domain` against `↥g.domain.toScheme`.
  have h := Scheme.Hom.stalkMap_congr_hom
    (g.hom ≫ C.toBaseTarget) (g.domain.ι ≫ C.toBaseSource) over ⟨C.genericPoint i, hx⟩
  have hcompL : (g.hom ≫ C.toBaseTarget).stalkMap ⟨C.genericPoint i, hx⟩ =
      C.toBaseTarget.stalkMap (g.hom ⟨C.genericPoint i, hx⟩) ≫
        g.hom.stalkMap ⟨C.genericPoint i, hx⟩ :=
    Scheme.Hom.stalkMap_comp _ _ _
  have hcompR : (g.domain.ι ≫ C.toBaseSource).stalkMap ⟨C.genericPoint i, hx⟩ =
      C.toBaseSource.stalkMap (C.genericPoint i) ≫
        (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).inv :=
    (Scheme.Hom.stalkMap_comp _ _ _).trans
      (congrArg (fun q ↦ C.toBaseSource.stalkMap (C.genericPoint i) ≫ q)
        (Scheme.Opens.stalkIso_inv g.domain ⟨C.genericPoint i, hx⟩).symm)
  rw [hcompL, hcompR] at h
  have hiso : (C.toBaseSource.stalkMap (C.genericPoint i) ≫
        (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).inv) ≫
      (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom =
      C.toBaseSource.stalkMap (C.genericPoint i) := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- The comparison isomorphism of stalks is abstracted to an opaque `sc`, carrying both the
  -- facts needed about it. Every step below is then a term, not a rewrite: `rw` cannot act on
  -- this goal at all, because the `≫` instances it elaborates in a standalone `have` are not
  -- the ones the goal carries.
  obtain ⟨sc, hsc, hscEq⟩ :
      ∃ sc, (C.toBaseTarget.stalkMap (g.hom ⟨C.genericPoint i, hx⟩) ≫
            g.hom.stalkMap ⟨C.genericPoint i, hx⟩ =
          sc ≫ (C.toBaseSource.stalkMap (C.genericPoint i) ≫
            (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).inv)) ∧
          sc = eqToHom (congrArg (fun x ↦ C.S.presheaf.stalk x) mapsTo) :=
    ⟨_, h, stalkCongr_hom_eqToHom C.S.presheaf mapsTo⟩
  calc C.toBaseTarget.stalkMap (g.hom ⟨C.genericPoint i, hx⟩) ≫
        g.hom.stalkMap ⟨C.genericPoint i, hx⟩ ≫
          (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom
      = (C.toBaseTarget.stalkMap (g.hom ⟨C.genericPoint i, hx⟩) ≫
          g.hom.stalkMap ⟨C.genericPoint i, hx⟩) ≫
          (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom := (Category.assoc _ _ _).symm
    _ = (sc ≫ (C.toBaseSource.stalkMap (C.genericPoint i) ≫
          (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).inv)) ≫
          (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom :=
        congrArg (fun q ↦ q ≫ (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom) hsc
    _ = sc ≫ ((C.toBaseSource.stalkMap (C.genericPoint i) ≫
          (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).inv) ≫
          (g.domain.stalkIso ⟨C.genericPoint i, hx⟩).hom) := Category.assoc _ _ _
    _ = sc ≫ C.toBaseSource.stalkMap (C.genericPoint i) := congrArg (fun q ↦ sc ≫ q) hiso
    _ = _ := congrArg (fun q ↦ q ≫ C.toBaseSource.stalkMap (C.genericPoint i)) hscEq

private lemma point_eq_of_equiv (f g : C.X.PartialMap C.Y) (h : f.equiv g)
    (i : Fin C.numberOfComponents) :
    f.hom ⟨C.genericPoint i, C.genericPoint_mem_dense_open f.domain f.dense_domain i⟩ =
      g.hom ⟨C.genericPoint i, C.genericPoint_mem_dense_open g.domain g.dense_domain i⟩ := by
  obtain ⟨W, hW, hWf, hWg, e⟩ := h
  change C.X.homOfLE hWf ≫ f.hom = C.X.homOfLE hWg ≫ g.hom at e
  let hx := C.genericPoint_mem_dense_open W hW i
  have he := congrArg (fun k : W.toScheme ⟶ C.Y ↦ k ⟨C.genericPoint i, hx⟩) e
  have hf : C.X.homOfLE hWf ⟨C.genericPoint i, hx⟩ =
      ⟨C.genericPoint i, C.genericPoint_mem_dense_open f.domain f.dense_domain i⟩ :=
    Subtype.ext (by simp)
  have hg : C.X.homOfLE hWg ⟨C.genericPoint i, hx⟩ =
      ⟨C.genericPoint i, C.genericPoint_mem_dense_open g.domain g.dense_domain i⟩ :=
    Subtype.ext (by simp)
  have key : f.hom (C.X.homOfLE hWf ⟨C.genericPoint i, hx⟩) =
      g.hom (C.X.homOfLE hWg ⟨C.genericPoint i, hx⟩) := he
  rwa [hf, hg] at key

private lemma stalkMap_heq_of_equiv (f g : C.X.PartialMap C.Y) (h : f.equiv g)
    (i : Fin C.numberOfComponents) :
    HEq (f.hom.stalkMap
          ⟨C.genericPoint i, C.genericPoint_mem_dense_open f.domain f.dense_domain i⟩ ≫
        (f.domain.stalkIso
          ⟨C.genericPoint i, C.genericPoint_mem_dense_open f.domain f.dense_domain i⟩).hom)
      (g.hom.stalkMap
          ⟨C.genericPoint i, C.genericPoint_mem_dense_open g.domain g.dense_domain i⟩ ≫
        (g.domain.stalkIso
          ⟨C.genericPoint i, C.genericPoint_mem_dense_open g.domain g.dense_domain i⟩).hom) := by
  obtain ⟨W, hW, hWf, hWg, e⟩ := h
  change C.X.homOfLE hWf ≫ f.hom = C.X.homOfLE hWg ≫ g.hom at e
  let hx := C.genericPoint_mem_dense_open W hW i
  let z : W := ⟨C.genericPoint i, hx⟩
  have hpoint :
      (C.X.homOfLE hWf ≫ f.hom) z = (C.X.homOfLE hWg ≫ g.hom) z :=
    congrArg (fun k : W.toScheme ⟶ C.Y ↦ k z) e
  have he := Scheme.Hom.stalkMap_congr_hom
    (C.X.homOfLE hWf ≫ f.hom) (C.X.homOfLE hWg ≫ g.hom) e z
  have he' := congrArg (fun q ↦ q ≫ (W.stalkIso z).hom) he
  have heqW : HEq
      ((C.X.homOfLE hWf ≫ f.hom).stalkMap z ≫ (W.stalkIso z).hom)
      ((C.X.homOfLE hWg ≫ g.hom).stalkMap z ≫ (W.stalkIso z).hom) := by
    apply heq_of_stalkCongr_eq hpoint
    simpa only [stalkCongr_hom_eqToHom, Category.assoc] using he'
  have zf : C.X.homOfLE hWf z =
      ⟨C.genericPoint i, C.genericPoint_mem_dense_open f.domain f.dense_domain i⟩ :=
    Subtype.ext (by simp [z])
  have zg : C.X.homOfLE hWg z =
      ⟨C.genericPoint i, C.genericPoint_mem_dense_open g.domain g.dense_domain i⟩ :=
    Subtype.ext (by simp [z])
  exact (stalkMap_homOfLE_comp_heq f W hWf z _ zf).symm.trans
    (heqW.trans (stalkMap_homOfLE_comp_heq g W hWg z _ zg))

/-- A chosen partial-map representative, over the base, of a rational map over the base. -/
public noncomputable def representativeOver (f : C.RationalMapsOver) :
    C.X.PartialMap C.Y := by
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  let : f.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr f.2
  exact Classical.choose (f.1.exists_partialMap_over C.S)

/-- The chosen representative of a rational map over the base is itself over the base. -/
public lemma representativeOver_base (f : C.RationalMapsOver) :
    (representativeOver C f).hom ≫ C.toBaseTarget =
      (representativeOver C f).domain.ι ≫ C.toBaseSource := by
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  let : f.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr f.2
  exact (Scheme.PartialMap.isOver_iff).mp
    (Classical.choose_spec (f.1.exists_partialMap_over C.S)).1

/-- The chosen representative of a rational map over the base induces that rational map. -/
public lemma representativeOver_toRationalMap (f : C.RationalMapsOver) :
    (representativeOver C f).toRationalMap = f.1 := by
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  let : f.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr f.2
  exact (Classical.choose_spec (f.1.exists_partialMap_over C.S)).2

/-- The generic-point map exists with its specified values on every
representative over the base. -/
public theorem nonempty_genericPointMap : Nonempty C.GenericPointMap := by
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  classical
  have he : ∀ (f : C.RationalMapsOver) (g : C.X.PartialMap C.Y), g.toRationalMap = f.1 →
      (representativeOver C f).equiv g := fun f g represents ↦
    (Scheme.PartialMap.toRationalMap_eq_iff).mp
      ((representativeOver_toRationalMap C f).trans represents.symm)
  refine ⟨{
    toFun := fun f i =>
      genericPointLocalMapOfPartial C (representativeOver C f)
        (representativeOver_base C f) i
    map_point := ?_
    map_stalk := ?_ }⟩
  · intro f g represents over mem i
    exact C.point_eq_of_equiv _ g (he f g represents) i
  · intro f g represents over mem i
    simpa only [genericPointLocalMapOfPartial] using
      C.stalkMap_heq_of_equiv _ g (he f g represents) i

/-- Evaluation of an `S`-rational map at the generic points of the irreducible
components, including the induced local maps of stalks. -/
public noncomputable def genericPointMapForRationalMaps : C.GenericPointMap :=
  Classical.choice C.nonempty_genericPointMap

end GenericPointMapContext


end AlgebraicGeometry
