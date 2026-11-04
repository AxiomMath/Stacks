module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A criterion for birationality over a base

For irreducible schemes locally of finite presentation over a base, birationality over the base
can be tested either on nonempty open subschemes or on the local rings at their generic points.

## Main results

* `AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso` characterizes birationality
  over the base by an isomorphism between nonempty open subschemes over the base.
* `AlgebraicGeometry.birationalOver_iff_generic_stalk_iso` characterizes it by an isomorphism of
  the generic local rings over the local ring of the base.

## Implementation notes

In `AlgebraicGeometry.birationalOver_iff_generic_stalk_iso`, transport along the equality of the
images of the generic points identifies the two base local rings before the isomorphism of local
rings is asked to respect their structure maps.

## References

* [Stacks Project, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If the transport of `f ≫ e.hom` along `h : a = b` equals `g`, then `g ≫ e.inv` is `f`
precomposed with the identification `P b ⟶ P a` induced by `h`. -/
lemma transport_comp_inv
    {α : Type u} (P : α → CommRingCat.{u}) {a b : α} (h : a = b)
    {A B : CommRingCat.{u}} (f : P a ⟶ A) (e : A ≅ B) (g : P b ⟶ B)
    (H : h ▸ (f ≫ e.hom) = g) :
    g ≫ e.inv = eqToHom (congrArg P h.symm) ≫ f := by
  cases h
  simpa using congrArg (fun k => k ≫ e.inv) H.symm

/-- If `g ≫ e.inv` is `f` precomposed with the identification `P b ⟶ P a` induced by
`h : a = b`, then the transport of `f ≫ e.hom` along `h` equals `g`. -/
lemma transport_comp_of_inv
    {α : Type u} (P : α → CommRingCat.{u}) {a b : α} (h : a = b)
    {A B : CommRingCat.{u}} (f : P a ⟶ A) (e : A ≅ B) (g : P b ⟶ B)
    (H : g ≫ e.inv = eqToHom (congrArg P h.symm) ≫ f) :
    h ▸ (f ≫ e.hom) = g := by
  cases h
  simpa using congrArg (· ≫ e.hom) H.symm

/-- A morphism heterogeneously equal to an isomorphism, with equal source and target objects, is
an isomorphism. -/
lemma isIso_of_heq_of_eq {C : Type u} [CategoryTheory.Category C]
    {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (hA : A' = A) (hB : B' = B) (h : HEq f g) [IsIso f] : IsIso g := by
  cases hA
  cases hB
  obtain rfl := eq_of_heq h
  infer_instance

/-- The generic-point context of Tag 0BX8 for an irreducible source, with its unique
irreducible component. -/
noncomputable abbrev genericPointContext {S X Y : Scheme.{u}} [IrreducibleSpace X]
    (sX : X ⟶ S) (sY : Y ⟶ S) : GenericPointMapContext :=
  { S := S
    X := X
    Y := Y
    toBaseSource := sX
    toBaseTarget := sY
    numberOfComponents := 1
    components :=
      { toFun := fun _ => ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; simp⟩
        invFun := fun _ => 0
        left_inv := by intro i; fin_cases i; rfl
        right_inv := by
          intro Z
          apply Subtype.ext
          have hZ : (Z : Set X) ∈ ({Set.univ} : Set (Set X)) := by
            simpa only [irreducibleComponents_eq_singleton] using Z.property
          exact (Set.mem_singleton_iff.mp hZ).symm }
    genericPoint := fun _ => genericPoint X
    isGenericPoint := fun _ => genericPoint_spec X }

/-- A nonempty open subscheme of an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_opens {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : IrreducibleSpace U.toScheme :=
  have : Nonempty ((TopologicalSpace.Opens.toTopCat _).obj U) := hU.to_subtype
  U.isOpenEmbedding.irreducibleSpace

/-- The generic point of an irreducible open subscheme is the generic point of the ambient
irreducible scheme. -/
private theorem genericPoint_opens_val {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    [IrreducibleSpace U.toScheme] : (genericPoint U.toScheme).1 = genericPoint X := by
  have hd : Dense (U : Set X) := U.2.dense ⟨_, (genericPoint U.toScheme).2⟩
  have h := (genericPoint_spec U.toScheme).image U.ι.continuous
  exact (by simpa [Set.image_univ, U.range_ι, hd.closure_eq] using h :
    IsGenericPoint (U.ι (genericPoint U.toScheme)) (Set.univ : Set X)).eq (genericPoint_spec X)

/-- For irreducible schemes, birationality over a base is witnessed by an
isomorphism of nonempty open subschemes over that base. -/
@[stacks 0BAD "parts (1) and (2)"]
public theorem birationalOver_iff_exists_nonempty_open_iso
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    Scheme.BirationalOver sX sY ↔
      ∃ (U : X.Opens) (V : Y.Opens),
        (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
          ∃ e : U.toScheme ≅ V.toScheme,
            e.hom ≫ V.ι ≫ sY = U.ι ≫ sX := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.source, f.target, f.dense_source.nonempty, f.dense_target.nonempty,
      ⟨f.iso, hf⟩⟩
  · rintro ⟨U, V, hU, hV, e, he⟩
    exact ⟨{ source := U, dense_source := U.2.dense hU, target := V,
             dense_target := V.2.dense hV, iso := e }, he⟩

/-- For irreducible schemes locally of finite presentation over a base,
birationality over that base is equivalent to an isomorphism of their generic
local rings as algebras over the local ring of the common image. -/
@[stacks 0BAD "parts (1) and (3)", ega "I 6.5.4" "(ii), special case"]
public theorem birationalOver_iff_generic_stalk_iso
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace Y]
    [LocallyOfFinitePresentation sX] [LocallyOfFinitePresentation sY] :
    Scheme.BirationalOver sX sY ↔
      ∃ (h : sX (genericPoint X) = sY (genericPoint Y))
        (e : X.presheaf.stalk (genericPoint X) ≅
          Y.presheaf.stalk (genericPoint Y)),
          h ▸ (sX.stalkMap (genericPoint X) ≫ e.hom) =
            sY.stalkMap (genericPoint Y) := by
  constructor
  · intro hBir
    rcases hBir with ⟨p, hp⟩
    have hSourceNonempty : (p.source : Set X).Nonempty :=
      p.dense_source.nonempty_iff.mpr inferInstance
    have hTargetNonempty : (p.target : Set Y).Nonempty :=
      p.dense_target.nonempty_iff.mpr inferInstance
    let : IrreducibleSpace p.source.toScheme := irreducibleSpace_opens p.source hSourceNonempty
    let xU : p.source.toScheme := genericPoint p.source.toScheme
    have hSourcePoint : xU.1 = genericPoint X := genericPoint_opens_val p.source
    let : IrreducibleSpace p.target.toScheme := irreducibleSpace_opens p.target hTargetNonempty
    let : IsIso (p.iso.hom) := inferInstance
    have hYGenOpen : IsGenericPoint (p.iso.hom xU) (Set.univ : Set p.target.toScheme) := by
      have h := (genericPoint_spec p.source.toScheme).image p.iso.hom.continuous
      have hsurj : Set.range p.iso.hom = Set.univ :=
        Set.range_eq_univ.mpr p.iso.hom.homeomorph.surjective
      simpa [Set.image_univ, hsurj] using h
    let C := genericPointContext sX sY
    let i0 : Fin C.numberOfComponents := ⟨0, by simp [C]⟩
    let pmap : X.PartialMap Y :=
      { domain := p.source, dense_domain := p.dense_source,
        hom := p.iso.hom ≫ p.target.ι }
    have hx : genericPoint X ∈ p.source := hSourcePoint ▸ xU.2
    let x0 : pmap.domain.toScheme := ⟨genericPoint X, by simpa [pmap] using hx⟩
    have hx0 : x0 = xU := Subtype.ext hSourcePoint.symm
    have hTargetPoint0 : p.target.ι (p.iso.hom x0) = genericPoint Y := by
      rw [hx0, hYGenOpen.eq (genericPoint_spec _)]
      exact genericPoint_opens_val p.target
    have hxC : C.genericPoint i0 ∈ pmap.domain := by
      simpa [C, i0, pmap] using hx
    have hpEq : pmap.hom ≫ sY = pmap.domain.ι ≫ sX := by
      simpa [pmap, Category.assoc, Scheme.PartialIso.IsOver] using hp
    let : LocallyOfFinitePresentation C.toBaseTarget := by
      show LocallyOfFinitePresentation sY
      infer_instance
    let : C.X.Over C.S := ⟨C.toBaseSource⟩
    let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
    let : pmap.IsOver C.S :=
      (Scheme.PartialMap.isOver_iff).mpr hpEq
    let r : C.RationalMapsOver :=
      ⟨pmap.toRationalMap,
        (Scheme.RationalMap.isOver_iff).mp
          (show pmap.toRationalMap.IsOver C.S from inferInstance)⟩
    generalize hd : C.genericPointMapForRationalMaps r i0 = data
    have hPointAux : data.point = pmap.hom ⟨C.genericPoint i0, hxC⟩ := by
      rw [← hd]
      exact C.genericPointMapForRationalMaps.map_point r pmap rfl hpEq
        (fun _ => hxC) i0
    have hTargetPoint' :
        pmap.hom ⟨C.genericPoint i0, hxC⟩ = genericPoint Y := by
      show p.target.ι (p.iso.hom ⟨C.genericPoint i0, hxC⟩) = genericPoint Y
      simpa [C, i0, pmap] using hTargetPoint0
    have hPoint : data.point = genericPoint Y := hPointAux.trans hTargetPoint'
    have hStalkAux :=
      C.genericPointMapForRationalMaps.map_stalk r pmap rfl hpEq
        (fun _ => hxC) i0
    rcases data with ⟨q, hq, φ, hφ, hcomm⟩
    change q = genericPoint Y at hPoint
    cases hPoint
    have hStalkIso : IsIso φ := by
      have hPartialStalk : IsIso (pmap.hom.stalkMap x0) := by
        show IsIso ((p.iso.hom ≫ p.target.ι).stalkMap x0)
        rw [Scheme.Hom.stalkMap_comp]
        let : IsIso (p.iso.hom.stalkMap x0) := inferInstance
        let : IsIso (p.target.ι.stalkMap (p.iso.hom x0)) := by
          rw [← Scheme.Opens.stalkIso_inv (U := p.target) (x := p.iso.hom x0)]
          exact CategoryTheory.Iso.isIso_inv _
        exact (isIso_comp_left_iff
          (p.target.ι.stalkMap (p.iso.hom x0))
          (p.iso.hom.stalkMap x0)).2 inferInstance
      have hComposite :
          IsIso (pmap.hom.stalkMap x0 ≫ (pmap.domain.stalkIso x0).hom) := by
        let : IsIso (pmap.hom.stalkMap x0) := hPartialStalk
        exact (isIso_comp_left_iff
          (pmap.hom.stalkMap x0) (pmap.domain.stalkIso x0).hom).2
            (CategoryTheory.Iso.isIso_hom _)
      rw [hd] at hStalkAux
      have hStalk : HEq φ
          (pmap.hom.stalkMap x0 ≫ (pmap.domain.stalkIso x0).hom) := by
        simpa [C, i0, x0] using hStalkAux
      have hCod : X.presheaf.stalk x0.1 = X.presheaf.stalk (genericPoint X) := rfl
      have hDom : Y.presheaf.stalk (genericPoint Y) =
          Y.presheaf.stalk (pmap.hom x0) := by
        simpa [pmap] using
          congrArg (fun z : Y => Y.presheaf.stalk z) hTargetPoint0.symm
      exact isIso_of_heq_of_eq
        (A := Y.presheaf.stalk (pmap.hom x0))
        (B := X.presheaf.stalk x0.1)
        (A' := Y.presheaf.stalk (genericPoint Y))
        (B' := X.presheaf.stalk (genericPoint X))
        (f := pmap.hom.stalkMap x0 ≫ (pmap.domain.stalkIso x0).hom)
        (g := φ) hDom hCod.symm hStalk.symm
    let e : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y) :=
      (asIso φ).symm
    have h : sX (genericPoint X) = sY (genericPoint Y) := hq.symm
    refine ⟨h, e, ?_⟩
    apply transport_comp_of_inv S.presheaf.stalk h
      (sX.stalkMap (genericPoint X)) e (sY.stalkMap (genericPoint Y))
    simpa [e] using hcomm
  · rintro ⟨h, e, H⟩
    let C := genericPointContext sX sY
    let d : ∀ i : Fin C.numberOfComponents, C.GenericPointLocalMap i := fun i =>
      { point := genericPoint Y
        mapsTo := h.symm
        stalkMap := e.inv
        isLocalHom := isLocalHom_of_iso e.symm
        commutes := transport_comp_inv C.S.presheaf.stalk h
          (C.toBaseSource.stalkMap (C.genericPoint i)) e
          (C.toBaseTarget.stalkMap (genericPoint Y)) H }
    let : LocallyOfFinitePresentation C.toBaseTarget := by
      show LocallyOfFinitePresentation sY
      infer_instance
    have hbij :=
      GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_locallyOfFinitePresentation
        C
    obtain ⟨r, hr⟩ := hbij.2 d
    let : IrreducibleSpace C.X := by
      show IrreducibleSpace X
      infer_instance
    let : IrreducibleSpace C.Y := by
      show IrreducibleSpace Y
      infer_instance
    let : C.X.Over C.S := ⟨C.toBaseSource⟩
    let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
    let : r.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr r.2
    obtain ⟨g, hgOver, hgR⟩ := r.1.exists_partialMap_over C.S
    let i0 : Fin C.numberOfComponents := ⟨0, by simp [C]⟩
    have hxmem : C.genericPoint i0 ∈ g.domain := by
      have hne : (g.domain : Set C.X).Nonempty :=
        g.dense_domain.nonempty_iff.mpr inferInstance
      apply (C.isGenericPoint i0).mem_open_set_iff g.domain.2 |>.2
      simpa [C, i0] using hne
    let z : g.domain.toScheme := ⟨C.genericPoint i0, hxmem⟩
    have hpoint :=
      C.genericPointMapForRationalMaps.map_point r g hgR
        (Scheme.PartialMap.isOver_iff.mp hgOver) (fun _ => hxmem) i0
    have hdata : C.genericPointMapForRationalMaps r i0 = d i0 :=
      congrArg (fun m => m i0) hr
    have hpointData :
        (C.genericPointMapForRationalMaps r i0).point = genericPoint Y := by
      rw [hdata]
    have hmap : g.hom z = genericPoint Y := hpoint.symm.trans hpointData
    have hstalk :=
      C.genericPointMapForRationalMaps.map_stalk r g hgR
        (Scheme.PartialMap.isOver_iff.mp hgOver) (fun _ => hxmem) i0
    have hstalkHEq : HEq e.inv (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) := by
      have hEq := hstalk
      rw [congrFun hr i0] at hEq
      simpa [d] using hEq
    have hstalkIso : IsIso (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) := by
      have hDom : C.Y.presheaf.stalk (g.hom z) =
          Y.presheaf.stalk (genericPoint Y) := by
        rw [hmap]
      have hCod : C.X.presheaf.stalk z.1 =
          X.presheaf.stalk (genericPoint X) := by
        simp [z, C]
      exact isIso_of_heq_of_eq hDom hCod hstalkHEq
    let U := g.domain
    let : IrreducibleSpace U.toScheme :=
      irreducibleSpace_opens U (g.dense_domain.nonempty_iff.mpr inferInstance)
    have hz : z = genericPoint U.toScheme := Subtype.ext (genericPoint_opens_val U).symm
    have hmapU : g.hom (genericPoint U.toScheme) = genericPoint C.Y := by
      calc
        g.hom (genericPoint U.toScheme) = g.hom z := congrArg g.hom hz.symm
        _ = genericPoint C.Y := hmap
    have hbijU : Set.BijOn g.hom (genericPoints U.toScheme) (genericPoints C.Y) := by
      rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
      exact Set.bijOn_singleton.mpr hmapU
    have hstalkU : IsIso (g.hom.stalkMap (genericPoint U.toScheme)) := by
      rw [← hz]
      let : IsIso ((g.domain.stalkIso z).hom) := inferInstance
      exact (isIso_comp_right_iff (g.hom.stalkMap z) (g.domain.stalkIso z).hom).mp hstalkIso
    have hbir : IsBirational g.hom :=
      isBirational_of_bijOn_of_isIso_stalkMap g.hom hbijU (by
        intro x hx
        have hx' : x = genericPoint U.toScheme := by
          simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
        subst x
        exact hstalkU)
    let : Finite (irreducibleComponents U.toScheme) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    let : Finite (irreducibleComponents C.Y) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    have hgOverEq : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ C.toBaseSource :=
      (Scheme.PartialMap.isOver_iff).mp hgOver
    let : LocallyOfFinitePresentation (g.hom ≫ C.toBaseTarget) := by
      rw [hgOverEq]
      infer_instance
    have hloc : LocallyOfFinitePresentation g.hom :=
      locallyOfFinitePresentation_of_comp g.hom C.toBaseTarget
    have hUY : Scheme.BirationalOver (U.ι ≫ C.toBaseSource) C.toBaseTarget :=
      birationalOver_of_isBirational (U.ι ≫ C.toBaseSource) C.toBaseTarget g.hom
        hbir hgOverEq (Or.inr hloc)
    show Scheme.BirationalOver sX sY
    exact (U.birationalOver_of_dense C.toBaseSource g.dense_domain).symm.trans hUY


end AlgebraicGeometry

end
