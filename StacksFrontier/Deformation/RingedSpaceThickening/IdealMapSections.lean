module

public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningLayer
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization

/-!
# The ideal map of a square of first order thickenings, on sections

Let `(i, t, f, f')` be a commutative square of ringed spaces of Stacks 08KZ whose rows
`i : X ⟶ X'` and `t : S ⟶ S'` are first order thickenings, let `𝒢` be a module on `X` with an
identification `κ : Ker(i^♯) ≅ i_*𝒢`, and let `c : f^*t^*𝒥 ⟶ 𝒢` be a map from the pulled back
ideal of `t`. The compatibility equation of Stacks 08U7 asks that the first order ideal map of
the square, read through `κ`, be `c`. This file reads that equation on sections: it holds if
and only if, for every section `j` of the ideal `𝒥` of `t`, the image `f'^♯(j)` is the section
of `𝒪_{X'}` corresponding through `κ` to the section `c(j)` of `𝒢`, where `c(j)` means the
adjoint transpose `𝒥 ⟶ t_*f_*𝒢` of `c` evaluated at `j`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.idealι`: the inclusion of the ideal of a morphism of
  ringed spaces, on sections.
* `AlgebraicGeometry.RingedSpaceThickening.doubleTranspose`: the transpose
  `𝒥 ⟶ t_*f_*𝒢` of a map `f^*t^*𝒥 ⟶ 𝒢`.

## Main results

* `RingedSpaceModuleAdjunction.homEquiv_comp_modulePullbackCompUniq_hom`: the adjunction for a
  composite, read through the comparison `(f ≫ g)^* ≅ g^* ⋙ f^*`.
* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.firstOrderIdealMap_eq_iff`:
  **the compatibility equation, on sections.**

## Implementation notes

Both sides of the equation are transposed twice: along `f'^* ⊣ f'_*` they become maps
`𝒥 ⟶ f'_*i_*𝒢`, and these are equal exactly when they agree on sections. The left-hand side is
read through the specification of the ideal map, the right-hand side through the
characterization of the comparison `(f ≫ g)^* ≅ g^* ⋙ f^*` as the comparison of two left
adjoints (`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`).

## References

* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Deformation.ToposThickening

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y Z : RingedSpace.{u, u}}

/-- **The adjunction for a composite, read through the comparison of pullbacks.** Transposing
`(f ≫ g)^*M ⟶ g^* f^* ... ⟶ N` along `(f ≫ g)^* ⊣ (f ≫ g)_*` is transposing along `f` and then
along `g`. -/
theorem homEquiv_comp_modulePullbackCompUniq_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (structureSheafRing Z)) (N : SheafOfModules.{u} (structureSheafRing X))
    (v : (modulePullback f).obj ((modulePullback g).obj M) ⟶ N) :
    (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
        ((modulePullbackCompUniq f g).hom.app M ≫ v) =
      (modulePullbackPushforwardAdjunction g).homEquiv M _
          ((modulePullbackPushforwardAdjunction f).homEquiv _ N v) ≫
        (modulePushforwardComp f g).hom.app N := by
  let : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  let : (SheafOfModules.pushforward (structureSheafHom g)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g
  let : (SheafOfModules.pushforward (structureSheafHom (f ≫ g))).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (f ≫ g)
  let adj2 := ((modulePullbackPushforwardAdjunction g).comp
    (modulePullbackPushforwardAdjunction f)).ofNatIsoRight (modulePushforwardCompSymm f g).symm
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (modulePullbackPushforwardAdjunction (f ≫ g)) adj2 M
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change ((modulePullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
    (modulePushforward (f ≫ g)).map
      (((modulePullbackPushforwardAdjunction (f ≫ g)).leftAdjointUniq adj2).hom.app M)) ≫ _ = _
  rw [hu]
  refine (adj2.homEquiv_unit (f := v)).symm.trans ?_
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

/-- The inverse form of `homEquiv_comp_modulePullbackCompUniq_hom`. -/
theorem homEquiv_homEquiv_modulePullbackCompUniq_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (structureSheafRing Z)) (N : SheafOfModules.{u} (structureSheafRing X))
    (w : (modulePullback (f ≫ g)).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction g).homEquiv M _
        ((modulePullbackPushforwardAdjunction f).homEquiv _ N
          ((modulePullbackCompUniq f g).inv.app M ≫ w)) =
      (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M N w ≫
        (modulePushforwardComp f g).inv.app N := by
  have h := homEquiv_comp_modulePullbackCompUniq_hom f g M N
    ((modulePullbackCompUniq f g).inv.app M ≫ w)
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at h
  rw [h, Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- **Transposition along equal morphisms of ringed spaces.** -/
theorem homEquiv_eqToHom_comp {k₁ k₂ : X ⟶ Y} (h : k₁ = k₂)
    (M : SheafOfModules.{u} (structureSheafRing Y)) (N : SheafOfModules.{u} (structureSheafRing X))
    (v : (modulePullback k₂).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction k₁).homEquiv M N
        (eqToHom (congrArg (fun k => (modulePullback k).obj M) h) ≫ v) =
      (modulePullbackPushforwardAdjunction k₂).homEquiv M N v ≫
        eqToHom (congrArg (fun k => (modulePushforward k).obj N) h.symm) := by
  subst h
  simp

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpaceThickening

/-- The transport of sections of a pushforward along an equality of morphisms of ringed spaces
is a restriction. -/
theorem eqToHom_modulePushforward_val_app {X Y : RingedSpace.{u, u}} {k₁ k₂ : X ⟶ Y}
    (h : k₁ = k₂) (N : SheafOfModules.{u} (structureSheafRing X)) (U : Opens Y.carrier)
    (hle : (Opens.map k₂.hom.base).obj U ≤ (Opens.map k₁.hom.base).obj U)
    (x : N.val.obj (op ((Opens.map k₁.hom.base).obj U))) :
    (eqToHom (congrArg (fun k => (modulePushforward k).obj N) h)).val.app (op U) x =
      mres N hle x := by
  subst h
  exact (mres_self N hle x).symm

/-- The inclusion of the ideal of a morphism of ringed spaces, on sections. -/
abbrev idealι {X X' : RingedSpace.{u, u}} (i : X ⟶ X') (W : Opens X'.carrier) :
    (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op W) →+ X'.presheaf.obj (op W) :=
  ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))).val.app
    (op W)).hom.toAddMonoidHom

/-- The double transpose `𝒥 ⟶ t_*f_*𝒢` of a map `c : f^*t^*𝒥 ⟶ 𝒢`. -/
abbrev doubleTranspose {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) (t : S ⟶ S')
    {J : SheafOfModules.{u} (structureSheafRing S')} {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj ((modulePullback t).obj J) ⟶ G) :
    J ⟶ (modulePushforward t).obj ((modulePushforward f).obj G) :=
  (modulePullbackPushforwardAdjunction t).homEquiv _ _
    ((modulePullbackPushforwardAdjunction f).homEquiv _ _ c)

/-- The sections of the double transpose of `c : f^*t^*𝒥 ⟶ 𝒢`, with values spelled as sections
of `𝒢`. -/
def dtApp {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) (t : S ⟶ S')
    {J : SheafOfModules.{u} (structureSheafRing S')} {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj ((modulePullback t).obj J) ⟶ G) (W : Opens S'.carrier)
    (j : J.val.obj (op W)) :
    G.val.obj (op ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj W))) :=
  (doubleTranspose f t c).val.app (op W) j

/-- The sections of a morphism into a direct image of sheaves of modules, with values spelled as
sections of the module upstairs. -/
def pushApp {X Y : RingedSpace.{u, u}} {k : X ⟶ Y} {M : SheafOfModules.{u} (structureSheafRing Y)}
    {N : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ (modulePushforward k).obj N)
    (V : Opens Y.carrier) (x : M.val.obj (op V)) : N.val.obj (op ((Opens.map k.hom.base).obj V)) :=
  φ.val.app (op V) x

/-- The sections of a morphism into a direct image commute with restriction. -/
theorem pushApp_mres {X Y : RingedSpace.{u, u}} {k : X ⟶ Y}
    {M : SheafOfModules.{u} (structureSheafRing Y)} {N : SheafOfModules.{u} (structureSheafRing X)}
    (φ : M ⟶ (modulePushforward k).obj N) {V V' : Opens Y.carrier} (h : V' ≤ V)
    (x : M.val.obj (op V)) :
    pushApp φ V' (mres M h x) = mres N (opensMap_le k.hom.base h) (pushApp φ V x) :=
  mres_naturality M φ h x

/-- The sections of the double transpose commute with restriction. -/
theorem dtApp_mres {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) (t : S ⟶ S')
    {J : SheafOfModules.{u} (structureSheafRing S')} {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj ((modulePullback t).obj J) ⟶ G) {W W' : Opens S'.carrier}
    (h : W' ≤ W) (j : J.val.obj (op W)) :
    dtApp f t c W' (mres J h j) =
      mres G (opensMap_le f.hom.base (opensMap_le t.hom.base h)) (dtApp f t c W j) :=
  mres_naturality J (doubleTranspose f t c) h j

namespace MorphismOfThickenings

variable (D : MorphismOfThickenings.{u})

/-- The preimages of an open of `S'` along the two composites of the square. -/
theorem preimage_le (W : Opens D.S'.carrier) :
    (Opens.map D.i.hom.base).obj ((Opens.map D.f'.hom.base).obj W) ≤
      (Opens.map D.f.hom.base).obj ((Opens.map D.t.hom.base).obj W) := by
  intro x hx
  change D.t.hom.base (D.f.hom.base x) ∈ W
  rw [← thickening_comm_apply D.i D.t D.f D.f' D.comm x]
  exact hx

/-- The transpose of the ideal map, on sections: it sends a section `j` of `𝒥` to the section of
the ideal of `i` whose image in `𝒪_{X'}` is `f'^♯(j)`. -/
theorem idealι_homEquiv_idealMap (W : Opens D.S'.carrier) (j : D.idealJ.val.obj (op W)) :
    idealι D.i _ (((modulePullbackPushforwardAdjunction D.f').homEquiv _ _ D.idealMap.1).val.app
        (op W) j) = D.f'.hom.c.app (op W) (idealι D.t W j) :=
  congrArg (fun k => k.val.app (op W) j) (homEquiv_idealMap_comp_idealι D)

variable (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
  (G : SheafOfModules.{u} (structureSheafRing D.X))
  (κ : D.idealI ≅ (modulePushforward D.i).obj G)

/-- The transpose of the right-hand side of the compatibility equation. -/
theorem homEquiv_firstOrderSurjection_comp
    (c : (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶ G) :
    (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
        (D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c) =
      doubleTranspose D.f D.t c ≫ (modulePushforwardComp D.f D.t).hom.app G ≫
        eqToHom (congrArg (fun k => (modulePushforward k).obj G) D.comm.symm) ≫
        (modulePushforwardComp D.i D.f').inv.app G := by
  have h1 : D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c =
      (modulePullbackPushforwardAdjunction D.i).homEquiv _ _
        (D.reducedPullbackComparison.hom ≫ c) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    rfl
  rw [h1]
  change (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
    ((modulePullbackPushforwardAdjunction D.i).homEquiv _ _
      ((modulePullbackCompUniq D.i D.f').inv.app D.idealJ ≫
        (eqToHom (congrArg (fun h : D.X ⟶ D.S' => (modulePullback h).obj D.idealJ) D.comm) ≫
          (modulePullbackCompUniq D.f D.t).hom.app D.idealJ) ≫ c)) = _
  rw [homEquiv_homEquiv_modulePullbackCompUniq_inv, Category.assoc,
    homEquiv_eqToHom_comp D.comm, homEquiv_comp_modulePullbackCompUniq_hom]
  simp only [Category.assoc]

/-- **The compatibility equation of Stacks 08U7, on sections.** The first order ideal map of the
square, read through `κ`, is `c` exactly when, for every section `j` of the ideal `𝒥` of `t`,
the image `f'^♯(j)` in `𝒪_{X'}` is the section corresponding through `κ` to the section of `𝒢`
that the transpose of `c` attaches to `j`. -/
theorem firstOrderIdealMap_eq_iff
    (c : (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶ G) :
    (D.firstOrderIdealMap hi ht).1 ≫ κ.hom = (modulePushforward D.i).map c ↔
      ∀ (W : Opens D.S'.carrier) (j : D.idealJ.val.obj (op W)),
        D.f'.hom.c.app (op W) (idealι D.t W j) =
          layerIdealIncl D.i G κ ((Opens.map D.f'.hom.base).obj W)
            (mres G (D.preimage_le W) (dtApp D.f D.t c W j)) := by
  have hepi : Epi (D.firstOrderSurjection hi ht) := D.firstOrderSurjection_epi hi ht
  have hstep : (D.firstOrderIdealMap hi ht).1 ≫ κ.hom = (modulePushforward D.i).map c ↔
      (modulePullbackPushforwardAdjunction D.f').homEquiv _ _ (D.idealMap.1 ≫ κ.hom) =
        (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
          (D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c) := by
    rw [Equiv.apply_eq_iff_eq]
    have e : D.idealMap.1 ≫ κ.hom =
        D.firstOrderSurjection hi ht ≫ (D.firstOrderIdealMap hi ht).1 ≫ κ.hom := by
      rw [← Category.assoc, (D.firstOrderIdealMap hi ht).2.1]
    rw [e]
    exact (cancel_epi _).symm
  rw [hstep, homEquiv_firstOrderSurjection_comp, Adjunction.homEquiv_naturality_right]
  have e : ∀ (W : Opens D.S'.carrier) (n : D.idealI.val.obj (op ((Opens.map D.f'.hom.base).obj W))),
      layerIdealIncl D.i G κ _ (κ.hom.val.app (op ((Opens.map D.f'.hom.base).obj W)) n) =
        idealι D.i _ n := fun W n => by
    change idealι D.i _ ((κ.hom ≫ κ.inv).val.app _ n) = _
    rw [Iso.hom_inv_id]
    rfl
  refine ⟨fun h W j => ?_, fun h => ?_⟩
  · refine (idealι_homEquiv_idealMap D W j).symm.trans ((e W _).symm.trans ?_)
    exact congrArg (layerIdealIncl D.i G κ _) ((congrArg (fun k => k.val.app (op W) j) h).trans
      (eqToHom_modulePushforward_val_app D.comm.symm G W (D.preimage_le W) _))
  · ext W j
    obtain ⟨W⟩ := W
    apply layerIdealIncl_injective D.i G κ
    refine (e W _).trans ((idealι_homEquiv_idealMap D W j).trans ((h W j).trans ?_))
    exact congrArg (layerIdealIncl D.i G κ _)
      (eqToHom_modulePushforward_val_app D.comm.symm G W (D.preimage_le W) _).symm

end MorphismOfThickenings

end AlgebraicGeometry.RingedSpaceThickening

end
