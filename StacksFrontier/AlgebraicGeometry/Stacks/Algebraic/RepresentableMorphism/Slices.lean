module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of a category with pullbacks induces a representable morphism of slices

In a category `C` with pullbacks, a morphism `f : X ⟶ Y` induces, by postcomposition, the
functor `Over.map f : C/X ⥤ C/Y` between the slice categories regarded as categories fibred
in groupoids over `C`, and this 1-morphism is representable: for any `U` and any 1-morphism
`C/U ⥤ C/Y` over `C`, the first projection off the 2-fibre product is represented by the
object `X ×_Y U` of `C/U`.

The proof is the one in the source. A 1-morphism `C/U ⥤ C/Y` over `C` is necessarily
`Over.map g` for the morphism `g : U ⟶ Y` it assigns to the identity of `U`, and the 2-fibre
product `(C/U) ×_{C/Y} (C/X)` is then equivalent over `C/U` to the slice of `C/U` at the
pullback `X ×_Y U`, the equivalence sending a point of the 2-fibre product to the morphism it
induces into that pullback.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_overMap`: postcomposition between slice
  categories is a
  representable 1-morphism.

## Implementation notes

The source works on the big fppf category over a scheme, but uses only the existence of
pullbacks in the base category, so the statement is made for an arbitrary category with
pullbacks. For the big fppf category over a scheme the required pullbacks are supplied by
Stacks 021U, so the source's assertion is the special case of this one.

## References

* [Stacks Project, Tag 02ZR](https://stacks.math.columbia.edu/tag/02ZR)
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RepresentableMorphism

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C}

private noncomputable def overMapAtTop {U Y : C} (G : Over U ⥤ Over Y)
    (hG : G ⋙ Over.forget Y = Over.forget U) : U ⟶ Y :=
  eqToHom (show U = (G.obj (Over.mk (𝟙 U))).left from
    (congrArg (fun F : Over U ⥤ C => F.obj (Over.mk (𝟙 U))) hG).symm) ≫
      (G.obj (Over.mk (𝟙 U))).hom

omit [HasPullbacks C] in
private theorem overMapAtTop_obj_left {U Y : C} (G : Over U ⥤ Over Y)
    (hG : G ⋙ Over.forget Y = Over.forget U) (Z : Over U) :
    (G.obj Z).left = Z.left := by
  simpa using congrArg (fun F : Over U ⥤ C => F.obj Z) hG

omit [HasPullbacks C] in
private theorem overMapAtTop_obj_hom {U Y : C} (G : Over U ⥤ Over Y)
    (hG : G ⋙ Over.forget Y = Over.forget U) (Z : Over U) :
    (G.obj Z).hom = eqToHom (overMapAtTop_obj_left G hG Z) ≫ Z.hom ≫
      overMapAtTop G hG := by
  have hcomp := Functor.congr_hom hG (Over.mkIdTerminal.from Z)
  simp only [Functor.comp_map, Over.forget_map, Over.mkIdTerminal_from_left] at hcomp
  calc
    (G.obj Z).hom = (G.map (Over.mkIdTerminal.from Z)).left ≫
        (G.obj (Over.mk (𝟙 U))).hom := (Over.w (G.map (Over.mkIdTerminal.from Z))).symm
    _ = eqToHom (overMapAtTop_obj_left G hG Z) ≫ Z.hom ≫
        overMapAtTop G hG := by
      rw [hcomp]
      simp [overMapAtTop, Category.assoc]

omit [HasPullbacks C] in
private theorem overObj_ext {T : C} {a b : Over T} (hl : a.left = b.left)
    (hh : eqToHom hl ≫ b.hom = a.hom) : a = b := by
  cases a with
  | mk al ar ah =>
    cases b with
    | mk bl br bh =>
      cases hl
      simp only [eqToHom_refl, Category.id_comp] at hh
      cases hh
      obtain rfl : ar = br := Subsingleton.elim _ _
      rfl

omit [HasPullbacks C] in
private theorem overMapAtTop_obj_eq {U Y : C} (G : Over U ⥤ Over Y)
    (hG : G ⋙ Over.forget Y = Over.forget U) (Z : Over U) :
    G.obj Z = (Over.map (overMapAtTop G hG)).obj Z := by
  apply overObj_ext (overMapAtTop_obj_left G hG Z)
  simpa using (overMapAtTop_obj_hom G hG Z).symm

omit [HasPullbacks C] in
private theorem overFunctor_eq_map {U Y : C} (G : Over U ⥤ Over Y)
    (hG : G ⋙ Over.forget Y = Over.forget U) :
    G = Over.map (overMapAtTop G hG) := by
  refine CategoryTheory.Functor.ext (overMapAtTop_obj_eq G hG) fun A B φ => ?_
  apply Over.OverMorphism.ext
  simpa using Functor.congr_hom hG φ

private abbrev OverMapRep (U : C) (g : U ⟶ Y) (f : X ⟶ Y) :=
  TwoFibreProductOver (Over.forget U) (Over.forget X) (Over.forget Y)
    (Over.map g) (Over.map f)

private noncomputable abbrev OverMapRep.sliceBase (U : C) (g : U ⟶ Y) (f : X ⟶ Y) : Over U :=
  Over.mk (pullback.snd f g)

omit [HasPullbacks C] in
private theorem OverMapRep.cone {U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    (P : OverMapRep U g f) :
    (P.iso.hom.left ≫ P.y.hom) ≫ f = P.x.hom ≫ g := by
  simpa only [Over.map_obj_hom, Category.assoc] using (Over.w P.iso.hom)

private noncomputable def OverMapRep.lift {U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    (P : OverMapRep U g f) : P.x.left ⟶ pullback f g :=
  pullback.lift (P.iso.hom.left ≫ P.y.hom) P.x.hom (P.cone g f)

private noncomputable def OverMapRep.toSlice {U : C} (g : U ⟶ Y) (f : X ⟶ Y) :
    OverMapRep U g f ⥤ Over (OverMapRep.sliceBase U g f) where
  obj P := Over.mk (Over.homMk (P.lift g f) (by
    simp [OverMapRep.lift, OverMapRep.sliceBase, pullback.lift_snd]))
  map {P Q} φ := Over.homMk φ.a (by
    apply Over.OverMorphism.ext
    change φ.a.left ≫ pullback.lift (Q.iso.hom.left ≫ Q.y.hom) Q.x.hom (Q.cone g f) =
      pullback.lift (P.iso.hom.left ≫ P.y.hom) P.x.hom (P.cone g f)
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      have hw := congrArg Over.Hom.left φ.w
      simp only [Over.comp_left, Over.map_map_left] at hw
      calc
        φ.a.left ≫ Q.iso.hom.left ≫ Q.y.hom =
            (P.iso.hom.left ≫ φ.b.left) ≫ Q.y.hom := by
              simpa [Category.assoc] using congrArg (fun k => k ≫ Q.y.hom) hw
        _ = P.iso.hom.left ≫ P.y.hom := by
          rw [Category.assoc, Over.w φ.b]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact Over.w φ.a)
  map_id P := by
    apply Over.OverMorphism.ext
    rfl
  map_comp φ ψ := by
    apply Over.OverMorphism.ext
    rfl

private theorem OverMapRep.toSlice_over {U : C} (g : U ⟶ Y) (f : X ⟶ Y) :
    OverMapRep.toSlice g f ⋙ Over.forget (OverMapRep.sliceBase U g f) =
      TwoFibreProductOver.fst (Over.forget U) (Over.forget X) (Over.forget Y)
        (Over.map g) (Over.map f) := by
  refine CategoryTheory.Functor.ext (fun P => ?_) ?_
  · rfl
  · intro P Q φ
    show φ.a = eqToHom rfl ≫ φ.a ≫ eqToHom rfl
    simp

private noncomputable def OverMapRep.fromSlice {U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    (Z : Over (OverMapRep.sliceBase U g f)) : OverMapRep U g f :=
    { base := Z.left.left
      x := Z.left
      y := Over.mk (Z.hom.left ≫ pullback.fst f g)
      hx := rfl
      hy := rfl
      iso := Over.isoMk (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom]
        calc
          (Z.hom.left ≫ pullback.fst f g) ≫ f =
              Z.hom.left ≫ pullback.snd f g ≫ g := by
                rw [Category.assoc, pullback.condition]
          _ = Z.left.hom ≫ g := by
            simpa [OverMapRep.sliceBase, Category.assoc] using
              congrArg (fun k => k ≫ g) (Over.w Z.hom))
      vertical := by
        apply CategoryTheory.IsHomLift.of_fac' (Over.forget Y) (𝟙 Z.left.left) _ rfl rfl
        simp [Over.forget_map, Over.isoMk_hom_left] }

omit [HasPullbacks C] in
private theorem OverMapRep.iso_left {U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    (P : OverMapRep U g f) :
    P.iso.hom.left = eqToHom P.hx ≫ eqToHom P.hy.symm := by
  have := P.vertical
  simpa only [Over.forget_map, Over.map_obj_left, Category.id_comp] using
    IsHomLift.fac' (Over.forget Y) (𝟙 P.base) P.iso.hom

omit [HasPullbacks C] in
private theorem OverMapRep.iso_inv_left {U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    (P : OverMapRep U g f) :
    P.iso.inv.left = eqToHom P.hy ≫ eqToHom P.hx.symm := by
  have := P.vertical
  have : (Over.forget Y).IsHomLift (𝟙 P.base) P.iso.inv :=
    IsHomLift.lift_id_inv (Over.forget Y) P.base P.iso
  simpa only [Over.forget_map, Over.map_obj_left, Category.id_comp] using
    IsHomLift.fac' (Over.forget Y) (𝟙 P.base) P.iso.inv

private theorem OverMapRep.toSlice_faithful {U : C} (g : U ⟶ Y) (f : X ⟶ Y) :
    (OverMapRep.toSlice g f).Faithful := by
  refine ⟨fun {P Q} φ ψ h => ?_⟩
  have ha : φ.a = ψ.a := by
    apply Over.OverMorphism.ext
    exact congrArg Over.Hom.left (by simpa [OverMapRep.toSlice] using congrArg Over.Hom.left h)
  have hφ := congrArg Over.Hom.left φ.w
  have hψ := congrArg Over.Hom.left ψ.w
  simp only [Over.comp_left, Over.map_map_left] at hφ hψ
  rw [ha] at hφ
  have hb : φ.b = ψ.b := by
    apply Over.OverMorphism.ext
    have : IsIso P.iso.hom.left := inferInstanceAs (IsIso ((Over.forget Y).map P.iso.hom))
    exact (cancel_epi P.iso.hom.left).1 (hφ.symm.trans hψ)
  exact TwoFibreProductOver.Hom.ext' ha hb

private theorem OverMapRep.toSlice_full {U : C} (g : U ⟶ Y) (f : X ⟶ Y) :
    (OverMapRep.toSlice g f).Full := by
  constructor
  intro P Q k
  let a : P.x ⟶ Q.x := k.left
  have hk := congrArg Over.Hom.left (Over.w k)
  change a.left ≫ pullback.lift (Q.iso.hom.left ≫ Q.y.hom) Q.x.hom (Q.cone g f) =
    pullback.lift (P.iso.hom.left ≫ P.y.hom) P.x.hom (P.cone g f) at hk
  have hcoord := congrArg (fun t => t ≫ pullback.fst f g) hk
  simp only [Category.assoc, pullback.lift_fst] at hcoord
  let b : P.y ⟶ Q.y := Over.homMk
    (P.iso.inv.left ≫ a.left ≫ Q.iso.hom.left) (by
      calc
        (P.iso.inv.left ≫ a.left ≫ Q.iso.hom.left) ≫ Q.y.hom =
            P.iso.inv.left ≫ (a.left ≫ Q.iso.hom.left ≫ Q.y.hom) := by
              simp only [Category.assoc]
        _ = P.iso.inv.left ≫ (P.iso.hom.left ≫ P.y.hom) := by rw [hcoord]
        _ = P.y.hom := by simp)
  have hbase : eqToHom P.hy.symm ≫ b.left ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ a.left ≫ eqToHom Q.hx := by
    show eqToHom P.hy.symm ≫
      (P.iso.inv.left ≫ a.left ≫ Q.iso.hom.left) ≫ eqToHom Q.hy = _
    rw [OverMapRep.iso_inv_left g f P, OverMapRep.iso_left g f Q]
    simp [Category.assoc]
  have hw : (Over.map g).map a ≫ Q.iso.hom =
      P.iso.hom ≫ (Over.map f).map b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.map_map_left]
    simp [b]
  exact ⟨TwoFibreProductOver.Hom.mk' a b hbase hw, Over.OverMorphism.ext rfl⟩

private theorem OverMapRep.to_from_hom {U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    (Z : Over (OverMapRep.sliceBase U g f)) :
    ((OverMapRep.toSlice g f).obj (OverMapRep.fromSlice g f Z)).hom = Z.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [OverMapRep.toSlice, OverMapRep.fromSlice, OverMapRep.lift, pullback.lift_fst]
  · simpa [OverMapRep.toSlice, OverMapRep.fromSlice, OverMapRep.lift, pullback.lift_snd,
      OverMapRep.sliceBase] using (Over.w Z.hom).symm

private theorem OverMapRep.verticalPreimages {U : C} (g : U ⟶ Y) (f : X ⟶ Y) :
    Functor.HasVerticalPreimages
      (TwoFibreProductOver.fst (Over.forget U) (Over.forget X) (Over.forget Y)
        (Over.map g) (Over.map f))
      (Over.forget (OverMapRep.sliceBase U g f)) (OverMapRep.toSlice g f) := by
  intro Z
  have hleft : ((OverMapRep.toSlice g f).obj (OverMapRep.fromSlice g f Z)).left =
      Z.left := rfl
  let α : Z ≅ (OverMapRep.toSlice g f).obj (OverMapRep.fromSlice g f Z) :=
    Over.isoMk (eqToIso hleft.symm) (hw := by
      show eqToHom (rfl : Z.left = Z.left) ≫ _ = _
      rw [eqToHom_refl]
      exact (Category.id_comp _).trans (OverMapRep.to_from_hom g f Z))
  refine ⟨OverMapRep.fromSlice g f Z, rfl, α, ?_⟩
  apply (CategoryTheory.IsHomLift.id_iff_exists_eqToHom
    (Over.forget (OverMapRep.sliceBase U g f)) α.hom).2
  refine ⟨hleft.symm, ?_⟩
  simp [α]

private noncomputable def OverMapRep.isEquivalenceOver {U : C} (g : U ⟶ Y) (f : X ⟶ Y) :
    Functor.IsEquivalenceOver
      (TwoFibreProductOver.fst (Over.forget U) (Over.forget X) (Over.forget Y)
        (Over.map g) (Over.map f))
      (Over.forget (OverMapRep.sliceBase U g f)) (OverMapRep.toSlice g f) := by
  letI := OverMapRep.toSlice_full g f
  letI := OverMapRep.toSlice_faithful g f
  exact Functor.isEquivalenceOver_of_exists_vertical_iso
    (OverMapRep.toSlice_over g f) (OverMapRep.verticalPreimages g f)

/-- An isomorphism lying over an identity, and its inverse, map to `eqToHom`s. -/
private theorem map_iso_eq_eqToHom_of_isHomLift_id {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    {p : 𝒳 ⥤ 𝒮} {s : 𝒮} {a b : 𝒳} {α : a ≅ b} (hα : p.IsHomLift (𝟙 s) α.hom)
    : (∀ h : p.obj a = p.obj b, p.map α.hom = eqToHom h) ∧
      ∀ h : p.obj b = p.obj a, p.map α.inv = eqToHom h := by
  have : p.IsHomLift (𝟙 s) α.inv := IsHomLift.lift_id_inv p s α
  exact ⟨fun _ => by rw [IsHomLift.fac' p (𝟙 s) α.hom]; simp,
    fun _ => by rw [IsHomLift.fac' p (𝟙 s) α.inv]; simp⟩

private noncomputable def OverMapRep.sliceEquivalenceOver {U : C} (g : U ⟶ Y)
    (f : X ⟶ Y) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.forget U) (Over.forget X) (Over.forget Y)
        (Over.map g) (Over.map f)) (Over.forget (OverMapRep.sliceBase U g f)) := by
  let e := OverMapRep.isEquivalenceOver g f
  refine
    { hom := ⟨OverMapRep.toSlice g f, OverMapRep.toSlice_over g f⟩
      inv := ⟨e.inv, e.inv_over⟩
      unitIso := e.unitIso.symm
      counitIso := e.counitIso
      unit_over := ?_
      counit_over := ?_ }
  · ext P
    simp only [Functor.whiskerRight_app, Iso.symm_hom, eqToHom_app]
    exact congrArg Over.Hom.left
      ((map_iso_eq_eqToHom_of_isHomLift_id (α := e.unitIso.app P) (e.unit_vertical P)).2 _)
  · ext Z
    simp only [Functor.whiskerRight_app, eqToHom_app]
    exact congrArg Over.Hom.left
      ((map_iso_eq_eqToHom_of_isHomLift_id (α := e.counitIso.app Z) (e.counit_vertical Z)).1 _)

/-- **Stacks 02ZR.** A morphism in a category with pullbacks induces a
representable 1-morphism of the categories fibred in groupoids of objects over
its source and target. -/
@[stacks 02ZR]
public theorem isRepresentableMorphism_overMap (f : X ⟶ Y) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism (Over.forget X) (Over.forget Y)
      (Over.map f) := by
  intro U G hG
  let g := overMapAtTop G hG
  rw [overFunctor_eq_map G hG]
  exact isRepresentableCFG_of_isRepresentable _
    ⟨OverMapRep.sliceBase U g f, ⟨OverMapRep.sliceEquivalenceOver g f⟩⟩

end Stacks.RepresentableMorphism
