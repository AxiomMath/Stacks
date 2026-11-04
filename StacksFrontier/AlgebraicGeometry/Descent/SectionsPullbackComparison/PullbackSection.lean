module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Pulling a section back, as a map of sections

`AlgebraicGeometry.Scheme.Modules.pullbackSection` sends a section of `F` over an open `U` of
the target to a section of `f⁺F` over an open `V` of the source contained in `f⁻¹U`.  It is
defined elementwise, as the image of the section under the unit of `f⁺ ⊣ f_*` restricted to `V`,
and the type it lands in is `(f⁺F).val.obj (op V)` rather than the notation `Γ(f⁺F, V)` the
module structures are stated for.  This file records it as a morphism of abelian groups between
groups of sections, proves it semilinear, and identifies the restriction maps of the
pullback-sections presheaf of Tag 03DS with it.

## Main definitions

* `AlgebraicGeometry.pullbackSectionHom`: pulling a section back, as a morphism
  `Γ(F, U) ⟶ Γ(f⁺F, V)` of abelian groups.

## Main results

* `AlgebraicGeometry.pullbackSectionHom_smul`: pulling a section back is semilinear over
  `AlgebraicGeometry.Scheme.Hom.appLE`.
* `AlgebraicGeometry.pullbackSectionHom_map`: pulling back a section already restricted to a
  smaller open of the target gives the same answer.
* `AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`: the restriction maps of the
  presheaf of Tag 03DS carry the pullback of a section over an open of the base to the pullback
  of that same section.  This is what makes `U ↦ Γ(U, U.ι⁺F)` a morphism of presheaves out of
  `F`.

## Implementation notes

`AlgebraicGeometry.pullbackSectionsMap` takes its argument in `Γ(f⁺F, ⊤)` while
`AlgebraicGeometry.Scheme.Modules.pullbackSection` produces an element of
`(f⁺F).val.obj (op ⊤)`.  The two types are definitionally equal but not syntactically so, and a
rewrite whose motive mentions both is rejected at `implicit` transparency; naming the composite
once, at the type the sections notation carries, is what `AlgebraicGeometry.pullbackSectionHom`
is for.  For the same reason the proofs below are `exact` chains of `Eq.trans` rather than
`rw`/`simp` sequences.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Pulling a section back, as a map of sections.**  For `f : Y ⟶ X`, an open `U` of `X` and
an open `V` of `Y` inside `f⁻¹U`, this is the morphism of abelian groups
`Γ(F, U) ⟶ Γ(f⁺F, V)` whose underlying function is
`AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
public noncomputable def pullbackSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op

/-- `AlgebraicGeometry.pullbackSectionHom` applied to a section is
`AlgebraicGeometry.Scheme.Modules.pullbackSection` of that section. -/
@[simp]
public theorem pullbackSectionHom_apply {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : M.val.obj (op U)) :
    pullbackSectionHom f M U V h a = Scheme.Modules.pullbackSection f M U V h a := rfl

/-- **Pulling a section back is semilinear.**  A global function on the target acts on the
pullback of a section through its image under `AlgebraicGeometry.Scheme.Hom.appLE`. -/
public theorem pullbackSectionHom_smul {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, U)) (a : Γ(M, U)) :
    pullbackSectionHom f M U V h (r • a) =
      f.appLE U V h r • pullbackSectionHom f M U V h a := by
  set N := (Scheme.Modules.pullback f).obj M with hN
  set y : Γ(N, f ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U a with hy
  have h2 : (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U (r • a) :
      Γ(N, f ⁻¹ᵁ U)) = f.app U r • y :=
    Scheme.Modules.Hom.app_smul _ r a
  have h1 : pullbackSectionHom f M U V h (r • a) =
      N.presheaf.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U (r • a) :
          Γ(N, f ⁻¹ᵁ U)) := rfl
  have h1' : pullbackSectionHom f M U V h a = N.presheaf.map (homOfLE h).op y := rfl
  rw [h1, h2, h1', Scheme.Modules.map_smul]
  rfl

/-- **Restricting the section first changes nothing.**  Pulling back the restriction of a
section to a smaller open of the target gives the same section of the pullback. -/
public theorem pullbackSectionHom_map {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U U' : X.Opens) (hUU' : U' ≤ U) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : V ≤ f ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    pullbackSectionHom f M U' V h (M.val.map (homOfLE hUU').op a) =
      pullbackSectionHom f M U V h' a := by
  have hnat := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE hUU').op a
  dsimp only [Functor.id_obj] at hnat
  show Scheme.Modules.pullbackSection f M U' V h _ =
    Scheme.Modules.pullbackSection f M U V h' a
  unfold Scheme.Modules.pullbackSection
  rw [hnat]
  show ConcreteCategory.hom (((Scheme.Modules.pullback f).obj M).val.map (homOfLE h).op)
      (ConcreteCategory.hom (((Scheme.Modules.pullback f).obj M).val.map
        ((Opens.map f.base).map (homOfLE hUU')).op) _) = _
  exact (PresheafOfModules.map_comp_apply (((Scheme.Modules.pullback f).obj M).val)
    ((Opens.map f.base).map (homOfLE hUU')).op (homOfLE h).op _).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)

/-- The restriction map of the presheaf of Tag 03DS along a morphism of schemes over `S`,
written as the comparison of iterated pullbacks applied to the pullback of a section. -/
public theorem pullbackSectionsMap_eq_comp {S : Scheme.{u}} (F : S.Modules) {X Y : Over S}
    (g : X ⟶ Y) (h' : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens))
    (s : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F g s =
      ((Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).val.app (op ⊤)
        (((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F).val.app (op ⊤)
          (Scheme.Modules.pullbackSection g.left ((Scheme.Modules.pullback Y.hom).obj F) ⊤ ⊤
            h' s)) := by
  set aM : (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback Y.hom).obj F) ⟶
      (Scheme.Modules.pullback X.hom).obj F :=
    (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F with haM
  have hr : ((Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).val.app (op ⊤)
        (((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F).val.app (op ⊤)
          (Scheme.Modules.pullbackSection g.left ((Scheme.Modules.pullback Y.hom).obj F) ⊤ ⊤
            h' s)) =
      aM.val.app (op ⊤)
        (Scheme.Modules.pullbackSection g.left ((Scheme.Modules.pullback Y.hom).obj F) ⊤ ⊤
          h' s) := rfl
  rw [hr]
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply aM.val (homOfLE h').op
    ((((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
      ((Scheme.Modules.pullback Y.hom).obj F)).val.app (op ⊤)) s)).symm
  exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _

/-- **The presheaf of Tag 03DS carries pullbacks of sections to pullbacks of sections.**  For a
morphism `g : X ⟶ Y` of schemes over `S` and a section `c` of `F` over an open `W` of `S` whose
preimage in `Y` and in `X` is everything, the restriction map of the presheaf of Tag 03DS sends
the pullback of `c` to `Y` to the pullback of `c` to `X`. -/
public theorem pullbackSectionsMap_pullbackSectionHom {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y) (W : S.Opens) (hY : (⊤ : Y.left.Opens) ≤ Y.hom ⁻¹ᵁ W)
    (hX : (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ W) (c : F.val.obj (op W)) :
    pullbackSectionsMap F g (pullbackSectionHom Y.hom F W ⊤ hY c) =
      pullbackSectionHom X.hom F W ⊤ hX c := by
  have h' : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens) := by simp
  have hcomp : (⊤ : X.left.Opens) ≤ (g.left ≫ Y.hom) ⁻¹ᵁ W := by
    rw [Over.w g]; exact hX
  have e2 := Scheme.Modules.pullbackSection_comp g.left Y.hom F W ⊤ ⊤ hY h' hcomp c
  have e3 := Scheme.Modules.pullbackSection_congr (Over.w g) F W ⊤ hcomp hX c
  rw [pullbackSectionsMap_eq_comp F g h' (pullbackSectionHom Y.hom F W ⊤ hY c)]
  exact (congrArg (fun z => ConcreteCategory.hom
    (((Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).val.app (op ⊤)) z) e2).trans e3

end AlgebraicGeometry

end
