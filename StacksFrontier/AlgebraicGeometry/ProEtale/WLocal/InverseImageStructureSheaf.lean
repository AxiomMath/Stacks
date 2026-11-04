module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms to an inverse-image locally ringed space

Let `p : Y ⟶ X` be a morphism of locally ringed spaces whose structure sheaf is the inverse image
of the structure sheaf of `X`. Then a morphism to `Y` over `X` is uniquely determined by its
underlying continuous map, and every continuous map over `X` lifts.

## Main definitions

* `AlgebraicGeometry.ProEtale.inverseImageStructureMap`: the adjoint form `p⁻¹ 𝒪_X ⟶ 𝒪_Y` of the
  structure morphism of `p`.

## Main results

* `AlgebraicGeometry.ProEtale.bijective_forgetToTop_morphism_over`: forgetting the sheaf map
  gives a bijection from locally-ringed-space morphisms over `X` to continuous maps over the
  underlying topological space of `X`.

## Implementation notes

The condition `𝒪_Y = p⁻¹ 𝒪_X` is expressed invariantly by requiring the canonical adjoint
structure map `p⁻¹ 𝒪_X ⟶ 𝒪_Y` to be an isomorphism. Morphisms in the two slice categories are
displayed as subtypes, so the map in the result is definitionally the operation which forgets the
sheaf map.

## References

* [Stacks Project, Tag 096K](https://stacks.math.columbia.edu/tag/096K)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.ProEtale

/-- The map `p⁻¹ 𝒪_X ⟶ 𝒪_Y` adjoint to the structure map
`𝒪_X ⟶ p_* 𝒪_Y` of a morphism of locally ringed spaces. -/
noncomputable def inverseImageStructureMap
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) :
    (TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪 ⟶ Y.𝒪 :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv X.𝒪 Y.𝒪).symm
    ⟨p.c⟩

/-- The structure map `𝒪_X ⟶ f_* 𝒪_Y` of a morphism `f : Y ⟶ X`, as a map of sheaves. -/
abbrev asSheafHom {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) :
    X.𝒪 ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.𝒪 :=
  ⟨f.c⟩

/-- The adjoint structure map is adjoint to the structure map. -/
lemma inverseImageStructureMap_unit {X Y : LocallyRingedSpace.{u}}
    (p : Y ⟶ X) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app X.𝒪 ≫
      (TopCat.Sheaf.pushforward CommRingCat p.base).map (inverseImageStructureMap p) =
        asSheafHom p := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base
  calc
    _ = adj.homEquiv X.𝒪 Y.𝒪 (inverseImageStructureMap p) :=
      (adj.homEquiv_unit X.𝒪 Y.𝒪 (inverseImageStructureMap p)).symm
    _ = asSheafHom p := by
      show adj.homEquiv X.𝒪 Y.𝒪
        ((adj.homEquiv X.𝒪 Y.𝒪).symm (⟨p.c⟩ : X.𝒪 ⟶
          (TopCat.Sheaf.pushforward CommRingCat p.base).obj Y.𝒪)) = ⟨p.c⟩
      exact Equiv.apply_symm_apply _ _

/-- Postcomposing the adjoint structure map corresponds, under the adjunction, to postcomposing
the pushforward of the structure map. -/
private lemma adjunct_structure_comp
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X)
    (g : Z.toTopCat ⟶ Y.toTopCat)
    (c : Y.𝒪 ⟶ (TopCat.Sheaf.pushforward CommRingCat g).obj Z.𝒪) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv
        X.𝒪 ((TopCat.Sheaf.pushforward CommRingCat g).obj Z.𝒪)
        (inverseImageStructureMap p ≫ c) =
      asSheafHom p ≫ (TopCat.Sheaf.pushforward CommRingCat p.base).map c := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base
  rw [adj.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    inverseImageStructureMap_unit]

/-- The stalk of the inverse-image sheaf `p⁻¹ 𝒪_X` at `y` is the stalk of `𝒪_X` at `p y`. -/
noncomputable def pullbackStalkComparison
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) (y : Y) :
    (TopCat.Presheaf.stalkFunctor CommRingCat y).obj
        ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).obj
          ((TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪)) ≅
    (TopCat.Presheaf.stalkFunctor CommRingCat (p.base y)).obj X.𝒪.presheaf := by
  let G := (TopCat.Presheaf.pullback CommRingCat p.base).obj X.𝒪.presheaf
  let iso1 := (TopCat.Sheaf.forget CommRingCat Y.toTopCat).mapIso
    ((TopCat.Sheaf.pullbackIso CommRingCat p.base).app X.𝒪)
  refine (TopCat.Presheaf.stalkFunctor CommRingCat y).mapIso iso1 ≪≫ ?_
  have hunit : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat y).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y.toTopCat) G)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y CommRingCat _
  refine (@asIso _ _ _ _ _ hunit).symm ≪≫ ?_
  exact (TopCat.Presheaf.stalkPullbackIso CommRingCat p.base X.𝒪.presheaf y).symm

/-- Under the stalk comparison, the adjoint structure map induces the stalk map of `p`. -/
lemma inverseImageStructureMap_stalk_compat
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) (y : Y) :
    (pullbackStalkComparison p y).inv ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat y).map
        ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map
          (inverseImageStructureMap p)) = p.stalkMap y := by
  have hcont : Functor.IsContinuous (TopologicalSpace.Opens.map p.base)
      (Opens.grothendieckTopology X.toTopCat)
      (Opens.grothendieckTopology Y.toTopCat) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map p.base)
      (coverPreserving_opens_map p.base)
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base
  let adjC := CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (TopologicalSpace.Opens.map p.base) CommRingCat
      (Opens.grothendieckTopology X.toTopCat)
      (Opens.grothendieckTopology Y.toTopCat)
  let pbIso := TopCat.Sheaf.pullbackIso CommRingCat p.base
  let phi := inverseImageStructureMap p
  have hUnitRel : adj.unit.app X.𝒪 ≫
      (TopCat.Sheaf.pushforward CommRingCat p.base).map (pbIso.hom.app X.𝒪) =
        adjC.unit.app X.𝒪 :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app adj adjC X.𝒪
  have hUnitC : adjC.unit.app X.𝒪 ≫
      (TopCat.Sheaf.pushforward CommRingCat p.base).map (pbIso.inv.app X.𝒪 ≫ phi) =
        asSheafHom p := by
    have hmap :
        (TopCat.Sheaf.pushforward CommRingCat p.base).map (pbIso.hom.app X.𝒪) ≫
          (TopCat.Sheaf.pushforward CommRingCat p.base).map
            (pbIso.inv.app X.𝒪 ≫ phi) =
        (TopCat.Sheaf.pushforward CommRingCat p.base).map phi := by
      rw [← Functor.map_comp, ← Category.assoc, pbIso.hom_inv_id_app X.𝒪]
      simp
    have hswap : adjC.unit.app X.𝒪 ≫
        (TopCat.Sheaf.pushforward CommRingCat p.base).map (pbIso.inv.app X.𝒪 ≫ phi) =
          (adj.unit.app X.𝒪 ≫
            (TopCat.Sheaf.pushforward CommRingCat p.base).map (pbIso.hom.app X.𝒪)) ≫
              (TopCat.Sheaf.pushforward CommRingCat p.base).map
                (pbIso.inv.app X.𝒪 ≫ phi) :=
      congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat p.base).map
        (pbIso.inv.app X.𝒪 ≫ phi)) hUnitRel.symm
    refine hswap.trans ?_
    rw [Category.assoc, hmap]
    exact inverseImageStructureMap_unit p
  let raw := (TopCat.Presheaf.pullback CommRingCat p.base).obj X.𝒪.presheaf
  let eta := CategoryTheory.toSheafify (Opens.grothendieckTopology Y.toTopCat) raw
  let psi : raw ⟶ Y.𝒪.presheaf := eta ≫
    (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map (pbIso.inv.app X.𝒪) ≫
      (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map phi
  have hUnitCP := congrArg ((TopCat.Sheaf.forget CommRingCat X.toTopCat).map) hUnitC
  have hCompU (U : TopologicalSpace.Opens X.toTopCat) :
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
          X.𝒪.presheaf).app (op U) ≫
          psi.app (op ((TopologicalSpace.Opens.map p.base).obj U)) =
        p.c.app (op U) :=
    congrArg (fun t => t.app (op U)) hUnitCP
  refine TopCat.Presheaf.stalk_hom_ext X.𝒪.presheaf fun U hU => ?_
  have hMap : y ∈ (TopologicalSpace.Opens.map p.base).obj U := by
    simpa using hU
  have hGerm : X.𝒪.presheaf.germ U (p.base y) hU ≫
      TopCat.Presheaf.stalkPullbackHom CommRingCat p.base X.𝒪.presheaf y =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
          X.𝒪.presheaf).app (op U) ≫
          raw.germ ((TopologicalSpace.Opens.map p.base).obj U) y hMap :=
    TopCat.Presheaf.germ_stalkPullbackHom CommRingCat p.base
    X.𝒪.presheaf y U hU
  have hGermMap := congrArg
    (fun k => k ≫ (TopCat.Presheaf.stalkFunctor CommRingCat y).map psi) hGerm
  have hNat := TopCat.Presheaf.stalkFunctor_map_germ
    ((TopologicalSpace.Opens.map p.base).obj U) y hMap psi
  have hIsoComp : X.𝒪.presheaf.germ U (p.base y) hU ≫
      (pullbackStalkComparison p y).inv ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat y).map
          ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map phi) =
          (X.𝒪.presheaf.germ U (p.base y) hU ≫
        TopCat.Presheaf.stalkPullbackHom CommRingCat p.base X.𝒪.presheaf y) ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat y).map psi := by
    have hcinv : (pullbackStalkComparison p y).inv =
        TopCat.Presheaf.stalkPullbackHom CommRingCat p.base X.𝒪.presheaf y ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat y).map eta ≫
            (TopCat.Presheaf.stalkFunctor CommRingCat y).map
              ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map (pbIso.inv.app X.𝒪)) := rfl
    have hmc : (TopCat.Presheaf.stalkFunctor CommRingCat y).map
          ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map (pbIso.inv.app X.𝒪) ≫
            (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map phi) =
        (TopCat.Presheaf.stalkFunctor CommRingCat y).map
            ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map (pbIso.inv.app X.𝒪)) ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat y).map
            ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map phi) :=
      Functor.map_comp _ _ _
    have hassoc : ∀ {R₀ R₁ R₂ R₃ R₄ R₅ : CommRingCat} (g₀ : R₀ ⟶ R₁) (g₁ : R₁ ⟶ R₂)
        (g₂ : R₂ ⟶ R₃) (g₃ : R₃ ⟶ R₄) (g₄ : R₄ ⟶ R₅),
        g₀ ≫ (g₁ ≫ g₂ ≫ g₃) ≫ g₄ = (g₀ ≫ g₁) ≫ g₂ ≫ g₃ ≫ g₄ := by
      simp
    have hmc2 :
        (TopCat.Presheaf.stalkFunctor CommRingCat y).map eta ≫
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).map
                ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map (pbIso.inv.app X.𝒪)) ≫
              (TopCat.Presheaf.stalkFunctor CommRingCat y).map
                ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map phi)) =
          (TopCat.Presheaf.stalkFunctor CommRingCat y).map psi :=
      ((Functor.map_comp _ _ _).trans
        (congrArg (fun t => (TopCat.Presheaf.stalkFunctor CommRingCat y).map eta ≫ t) hmc)).symm
    exact (hassoc _ _ _ _ _).trans
      (congrArg (fun t => (X.𝒪.presheaf.germ U (p.base y) hU ≫
        TopCat.Presheaf.stalkPullbackHom CommRingCat p.base X.𝒪.presheaf y) ≫ t) hmc2)
  exact hIsoComp.trans (hGermMap.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun t => ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
        p.base).unit.app X.𝒪.presheaf).app (op U) ≫ t) hNat).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ Y.𝒪.presheaf.germ
            ((TopologicalSpace.Opens.map p.base).obj U) y hMap) (hCompU U)).trans
          (LocallyRingedSpace.stalkMap_germ p U y hU).symm)))))

/-- If the adjoint structure map of `p` is an isomorphism, then so is every stalk map of `p`. -/
private lemma structureMap_stalk_isIso
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X)
    [IsIso (inverseImageStructureMap p)] (y : Y) : IsIso (p.stalkMap y) := by
  let compIso := (pullbackStalkComparison p y).symm ≪≫
    (TopCat.Presheaf.stalkFunctor CommRingCat y).mapIso
      ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).mapIso
        (asIso (inverseImageStructureMap p)))
  have hcomp : compIso.hom = p.stalkMap y := by
    show (pullbackStalkComparison p y).inv ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat y).map
        ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map
          (asIso (inverseImageStructureMap p)).hom) = p.stalkMap y
    simpa only [asIso_hom, TopCat.Presheaf.stalkFunctor_obj] using
      inverseImageStructureMap_stalk_compat p y
  exact hcomp ▸ compIso.isIso_hom

/-- If the structure sheaf of `Y` is the inverse image of that of `X`, then
forgetting the sheaf map bijects morphisms `Z ⟶ Y` over `X` with continuous
maps between the underlying spaces over `X`. -/
@[stacks 096K]
theorem bijective_forgetToTop_morphism_over
    {X Y Z : LocallyRingedSpace.{u}}
    (p : Y ⟶ X) (q : Z ⟶ X)
    [IsIso (inverseImageStructureMap p)] :
    Function.Bijective
      (fun f : {f : Z ⟶ Y // f ≫ p = q} ↦
        (⟨f.1.base, congrArg (fun k : Z ⟶ X ↦ k.base) f.2⟩ :
          {g : Z.toTopCat ⟶ Y.toTopCat // g ≫ p.base = q.base})) := by
  classical
  let ei := asIso (inverseImageStructureMap p)
  have hIsoHom : IsIso (inverseImageStructureMap p).hom :=
    ⟨⟨ei.inv.hom,
      congrArg InducedCategory.Hom.hom ei.hom_inv_id,
      congrArg InducedCategory.Hom.hom ei.inv_hom_id⟩⟩
  let A (f : {f : Z ⟶ Y // f ≫ p = q}) :
      {g : Z.toTopCat ⟶ Y.toTopCat // g ≫ p.base = q.base} :=
    ⟨f.1.base, congrArg (fun k : Z ⟶ X ↦ k.base) f.2⟩
  have hA : Function.Injective A := by
    intro f g h
    rcases f with ⟨f, hf⟩
    rcases g with ⟨g, hg⟩
    rcases f with ⟨⟨fbase, fc⟩, fprop⟩
    rcases g with ⟨⟨gbase, gc⟩, gprop⟩
    have hbase : fbase = gbase := by
      simpa [A] using congrArg Subtype.val h
    cases hbase
    let f : Z ⟶ Y := ⟨⟨fbase, fc⟩, fprop⟩
    let g : Z ⟶ Y := ⟨⟨fbase, gc⟩, gprop⟩
    have hcomp : f ≫ p = g ≫ p := hf.trans hg.symm
    have hc : HEq (f ≫ p).c (g ≫ p).c := by rw [hcomp]
    have hsheaf : inverseImageStructureMap p ≫ asSheafHom f =
        inverseImageStructureMap p ≫ asSheafHom g := by
      apply (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv
        X.𝒪 ((TopCat.Sheaf.pushforward CommRingCat f.base).obj Z.𝒪) |>.injective
      rw [adjunct_structure_comp p f.base (asSheafHom f),
        adjunct_structure_comp p g.base (asSheafHom g)]
      exact InducedCategory.hom_ext (eq_of_heq hc)
    have hfc : asSheafHom f = asSheafHom g :=
      (cancel_epi (inverseImageStructureMap p)).1 hsheaf
    apply Subtype.ext
    apply LocallyRingedSpace.Hom.ext'
    show (⟨fbase, fc⟩ : Z.toPresheafedSpace ⟶ Y.toPresheafedSpace) =
      (⟨fbase, gc⟩ : Z.toPresheafedSpace ⟶ Y.toPresheafedSpace)
    apply PresheafedSpace.ext
      (α := (⟨fbase, fc⟩ : Z.toPresheafedSpace ⟶ Y.toPresheafedSpace))
      (β := (⟨fbase, gc⟩ : Z.toPresheafedSpace ⟶ Y.toPresheafedSpace)) rfl
    have hfc' : fc = gc := congrArg (fun k : Y.𝒪 ⟶
      (TopCat.Sheaf.pushforward CommRingCat f.base).obj Z.𝒪 => k.hom) hfc
    rw [hfc']
    simp only [eqToHom_refl, Functor.whiskerRight_id']
    exact Category.comp_id gc
  have hsurj : Function.Surjective A := by
    intro g
    let e := inverseImageStructureMap p
    have hmap : (TopologicalSpace.Opens.map (g.1 ≫ p.base)).op =
        (TopologicalSpace.Opens.map q.base).op := by
      rw [g.2]
    let b : X.𝒪 ⟶
        (TopCat.Sheaf.pushforward CommRingCat p.base).obj
          ((TopCat.Sheaf.pushforward CommRingCat g.1).obj Z.𝒪) :=
      InducedCategory.homMk
        (q.c ≫ Functor.whiskerRight (eqToHom hmap.symm) Z.presheaf)
    let a : (TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪 ⟶
        (TopCat.Sheaf.pushforward CommRingCat g.1).obj Z.𝒪 :=
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv _ _ |>.symm b
    let c : Y.𝒪 ⟶ (TopCat.Sheaf.pushforward CommRingCat g.1).obj Z.𝒪 := inv e ≫ a
    let F : Z.toPresheafedSpace ⟶ Y.toPresheafedSpace := { base := g.1, c := c.hom }
    have hcomp : F ≫ p.toHom = q.toHom := by
      have hw : (F ≫ p.toHom).base = q.base := g.2
      apply PresheafedSpace.ext _ _ hw
      have hsheaf : asSheafHom p ≫
          (TopCat.Sheaf.pushforward CommRingCat p.base).map c = b := by
        calc
          _ = (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv
              X.𝒪 ((TopCat.Sheaf.pushforward CommRingCat g.1).obj Z.𝒪)
              (e ≫ c) := (adjunct_structure_comp p g.1 c).symm
          _ = (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv
              X.𝒪 ((TopCat.Sheaf.pushforward CommRingCat g.1).obj Z.𝒪) a := by
            simp [c, e]
          _ = b := by simp [a]
      show (PresheafedSpace.comp F p.toHom).c ≫ _ = q.c
      rw [PresheafedSpace.comp_c]
      have hsheaf' : p.c ≫
          (TopCat.Presheaf.pushforward CommRingCat p.base).map F.c = b.hom :=
        congrArg InducedCategory.Hom.hom hsheaf
      show (p.c ≫
        (TopCat.Presheaf.pushforward CommRingCat p.base).map F.c) ≫ _ = q.c
      rw [hsheaf']
      have hcast : Functor.whiskerRight (eqToHom hmap.symm) Z.presheaf ≫
          Functor.whiskerRight (eqToHom hmap) Z.presheaf = 𝟙 _ := by
        rw [← Functor.whiskerRight_comp]
        simp
      show q.c ≫ Functor.whiskerRight (eqToHom hmap.symm) Z.presheaf ≫
        Functor.whiskerRight (eqToHom hmap) Z.presheaf = q.c
      rw [hcast]
      exact Category.comp_id q.c
    let f : Z ⟶ Y :=
      LocallyRingedSpace.Hom.mk { base := g.1, c := c.hom } (by
        intro x
        show IsLocalHom (F.stalkMap x).hom
        have hc : IsLocalHom ((F ≫ p.toHom).stalkMap x).hom := by
          rw [PresheafedSpace.stalkMap.congr_hom (F ≫ p.toHom) q.toHom hcomp x]
          infer_instance
        rw [PresheafedSpace.stalkMap.comp] at hc
        change IsLocalHom ((F.stalkMap x).hom.comp
          (p.stalkMap (g.1 x)).hom) at hc
        have hpiso : IsIso (p.stalkMap (g.1 x)) :=
          structureMap_stalk_isIso p (g.1 x)
        let ei := asIso (p.stalkMap (g.1 x))
        have heiinv : IsLocalHom ei.inv.hom := IsLocalHom.of_surjective ei.inv.hom
          (ConcreteCategory.bijective_of_isIso ei.inv).2
        have hcancel :
            ((F.stalkMap x).hom.comp (p.stalkMap (g.1 x)).hom).comp ei.inv.hom =
              (F.stalkMap x).hom := by
          have hp : (p.stalkMap (g.1 x)).hom.comp ei.inv.hom = RingHom.id _ :=
            congrArg CommRingCat.Hom.hom ei.inv_hom_id
          rw [RingHom.comp_assoc, hp, RingHom.comp_id]
        exact hcancel ▸ (RingHom.isLocalHom_comp _ _))
    refine ⟨⟨f, ?_⟩, ?_⟩
    · exact LocallyRingedSpace.Hom.ext' (by simpa [f, F] using hcomp)
    · exact Subtype.ext rfl
  exact ⟨hA, hsurj⟩

end AlgebraicGeometry.ProEtale
