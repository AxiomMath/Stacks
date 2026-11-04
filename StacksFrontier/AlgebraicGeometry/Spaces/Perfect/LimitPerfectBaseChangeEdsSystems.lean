module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectBaseChangeRebase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingDescentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The three pieces of an elementary distinguished square along a directed system

Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square and let `j ↦ W_j` be a directed
system over `W` with a cone `W_∞`.  By Stacks 08GN the square base changes to an elementary
distinguished square of every `W_j` and of `W_∞`
(`AlgebraicGeometry.Space.edsPreimage`), and the transition morphisms and the projections of the
system induce morphisms between them (`AlgebraicGeometry.Space.edsPreimageOpenMap` and its two
companions).  This file assembles the open subspaces `U_j = U ×_W W_j`, the étale algebraic
spaces `V_j = V ×_W W_j` and the intersections `U_j ×_{W_j} V_j` into three directed systems,
over `U`, over `V` and over `U ×_W V`, and proves that when the system over `W` is presented as
a base change of Situation 09RH (`AlgebraicGeometry.Space.DescentSituation.BaseChangeData`), so
are the three new ones.

## Main definitions

* `AlgebraicGeometry.Space.edsOpenSystem`, `edsEtaleSystem`, `edsInterSystem`: the three
  systems.
* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData.edsOpen`, `edsEtale`, `edsInter`:
  their presentations.

## References

* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Maps out of the base changes of a square -/

section Maps

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- Two morphisms into the open subspace of an elementary distinguished square agree as soon as
they agree in the ambient space. -/
theorem edsOpen_hom_ext {T : AlgebraicSpaces B S hS} {a b : T ⟶ edsOpen B S hS hsq}
    (h : a ≫ edsOpenHom B S hS hsq = b ≫ edsOpenHom B S hS hsq) : a = b :=
  ObjectProperty.hom_ext _ ((cancel_mono Uo.ι).1 (congrArg (fun φ => φ.hom) h))

variable {W' W'' : AlgebraicSpaces B S hS}

/-- The open subspace of the base change of the square along `p` maps to the open subspace of
the square. -/
def edsPreimageOpenToSquare (p : W' ⟶ W) :
    edsOpen B S hS (edsPreimage hsq p) ⟶ edsOpen B S hS hsq :=
  ObjectProperty.homMk (Uo.fromPreimage p.hom)

/-- The map `edsPreimageOpenToSquare hsq p` lies over `p`. -/
@[reassoc]
theorem edsPreimageOpenToSquare_comp (p : W' ⟶ W) :
    edsPreimageOpenToSquare hsq p ≫ edsOpenHom B S hS hsq =
      edsOpenHom B S hS (edsPreimage hsq p) ≫ p :=
  ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι Uo p.hom)

/-- The étale algebraic space of the base change of the square along `p` maps to the étale
algebraic space of the square. -/
def edsPreimageEtaleToSquare (p : W' ⟶ W) :
    edsEtale B S hS (edsPreimage hsq p) ⟶ edsEtale B S hS hsq :=
  ObjectProperty.homMk (pullback.fst fV p.hom)

/-- The map `edsPreimageEtaleToSquare hsq p` lies over `p`. -/
@[reassoc]
theorem edsPreimageEtaleToSquare_comp (p : W' ⟶ W) :
    edsPreimageEtaleToSquare hsq p ≫ edsEtaleHom B S hS hsq =
      edsEtaleHom B S hS (edsPreimage hsq p) ≫ p :=
  ObjectProperty.hom_ext _ pullback.condition

/-- Two morphisms into the étale algebraic space of the base change of the square along `p`
agree as soon as they agree in the étale algebraic space of the square and in `W'`. -/
theorem edsPreimageEtale_hom_ext (p : W' ⟶ W) {T : AlgebraicSpaces B S hS}
    {a b : T ⟶ edsEtale B S hS (edsPreimage hsq p)}
    (h₁ : a ≫ edsPreimageEtaleToSquare hsq p = b ≫ edsPreimageEtaleToSquare hsq p)
    (h₂ : a ≫ edsEtaleHom B S hS (edsPreimage hsq p) = b ≫ edsEtaleHom B S hS (edsPreimage hsq p)) :
    a = b :=
  ObjectProperty.hom_ext _ (pullback.hom_ext (congrArg (fun φ => φ.hom) h₁)
    (congrArg (fun φ => φ.hom) h₂))

/-- Two morphisms into the intersection of an elementary distinguished square agree as soon as
they agree in its open subspace and in its étale algebraic space. -/
theorem edsInter_hom_ext {T : AlgebraicSpaces B S hS} {a b : T ⟶ edsInter B S hS hsq}
    (h₁ : a ≫ edsFst B S hS hsq = b ≫ edsFst B S hS hsq)
    (h₂ : a ≫ edsSnd B S hS hsq = b ≫ edsSnd B S hS hsq) : a = b :=
  ObjectProperty.hom_ext _ (pullback.hom_ext (congrArg (fun φ => φ.hom) h₁)
    (congrArg (fun φ => φ.hom) h₂))

/-- The intersection of the base change of the square along `p` maps to the intersection of the
square. -/
def edsPreimageInterToSquare (p : W' ⟶ W) :
    edsInter B S hS (edsPreimage hsq p) ⟶ edsInter B S hS hsq :=
  ObjectProperty.homMk (pullback.lift
    ((edsFst B S hS (edsPreimage hsq p)).hom ≫ (edsPreimageOpenToSquare hsq p).hom)
    ((edsSnd B S hS (edsPreimage hsq p)).hom ≫ (edsPreimageEtaleToSquare hsq p).hom) (by
      have h₁ := congrArg (fun φ => φ.hom) (edsPreimageOpenToSquare_comp hsq p)
      have h₂ := congrArg (fun φ => φ.hom) (edsPreimageEtaleToSquare_comp hsq p)
      have h₀ := congrArg (fun φ => φ.hom) (isPullback_edsInter B S hS (edsPreimage hsq p)).w
      dsimp only [ObjectProperty.FullSubcategory.comp_hom] at h₁ h₂ h₀
      change ((edsFst B S hS (edsPreimage hsq p)).hom ≫ (edsPreimageOpenToSquare hsq p).hom) ≫
          (edsOpenHom B S hS hsq).hom =
        ((edsSnd B S hS (edsPreimage hsq p)).hom ≫ (edsPreimageEtaleToSquare hsq p).hom) ≫
          (edsEtaleHom B S hS hsq).hom
      rw [Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc, ← Category.assoc, h₀]))

/-- The map `edsPreimageInterToSquare hsq p` commutes with the projections to the open
subspaces. -/
@[reassoc]
theorem edsPreimageInterToSquare_fst (p : W' ⟶ W) :
    edsPreimageInterToSquare hsq p ≫ edsFst B S hS hsq =
      edsFst B S hS (edsPreimage hsq p) ≫ edsPreimageOpenToSquare hsq p :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The map `edsPreimageInterToSquare hsq p` commutes with the projections to the étale
algebraic spaces. -/
@[reassoc]
theorem edsPreimageInterToSquare_snd (p : W' ⟶ W) :
    edsPreimageInterToSquare hsq p ≫ edsSnd B S hS hsq =
      edsSnd B S hS (edsPreimage hsq p) ≫ edsPreimageEtaleToSquare hsq p :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- **The intersection of the base change along `p` is the base change of the intersection to
the open subspace of the base change**: `U' ×_{W'} V' = U' ×_U (U ×_W V)`. -/
theorem isPullback_edsPreimageInter (p : W' ⟶ W) :
    IsPullback (edsFst B S hS (edsPreimage hsq p)).hom (edsPreimageInterToSquare hsq p).hom
      (edsPreimageOpenToSquare hsq p).hom (edsFst B S hS hsq).hom := by
  have L : IsPullback (edsSnd B S hS (edsPreimage hsq p)).hom
      (edsFst B S hS (edsPreimage hsq p)).hom (pullback.snd fV p.hom) (Uo.preimage p.hom).ι :=
    (IsPullback.of_hasPullback (Uo.preimage p.hom).ι (pullback.snd fV p.hom)).flip
  have outer : IsPullback ((edsPreimageInterToSquare hsq p).hom ≫ pullback.snd Uo.ι fV)
      (edsFst B S hS (edsPreimage hsq p)).hom fV (Uo.fromPreimage p.hom ≫ Uo.ι) := by
    have h := L.paste_horiz (IsPullback.of_hasPullback fV p.hom)
    convert h using 1
    · exact pullback.lift_snd _ _ _
    · exact Subfunctor.fromPreimage_ι Uo p.hom
  exact (outer.of_right (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback Uo.ι fV).flip).flip

/-! ### Maps between the base changes along a composite -/

variable (p₁ : W' ⟶ W) (p₂ : W'' ⟶ W)

/-- The map of open subspaces induced by `q` over `W` commutes with the maps to the open
subspace of the square. -/
@[reassoc]
theorem edsPreimageOpenMap_comp_toBase (q : W'' ⟶ W') (hq : q ≫ p₁ = p₂) :
    edsPreimageOpenMap hsq p₁ p₂ q hq ≫ edsPreimageOpenToSquare hsq p₁ =
      edsPreimageOpenToSquare hsq p₂ :=
  edsOpen_hom_ext hsq (by
    rw [Category.assoc, edsPreimageOpenToSquare_comp, ← Category.assoc,
      ← edsPreimageOpenMap_comp, Category.assoc, hq, edsPreimageOpenToSquare_comp])

/-- The map of étale algebraic spaces induced by `q` over `W` commutes with the maps to the
étale algebraic space of the square. -/
@[reassoc]
theorem edsPreimageEtaleMap_comp_toBase (q : W'' ⟶ W') (hq : q ≫ p₁ = p₂) :
    edsPreimageEtaleMap hsq p₁ p₂ q hq ≫ edsPreimageEtaleToSquare hsq p₁ =
      edsPreimageEtaleToSquare hsq p₂ :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The map of intersections induced by `q` over `W` commutes with the maps to the
intersection of the square. -/
@[reassoc]
theorem edsPreimageInterMap_comp_toBase (q : W'' ⟶ W') (hq : q ≫ p₁ = p₂) :
    edsPreimageInterMap hsq p₁ p₂ q hq ≫ edsPreimageInterToSquare hsq p₁ =
      edsPreimageInterToSquare hsq p₂ :=
  edsInter_hom_ext hsq
    (by rw [Category.assoc, edsPreimageInterToSquare_fst, ← Category.assoc,
      ← edsFst_comp_edsPreimageOpenMap, Category.assoc, edsPreimageOpenMap_comp_toBase,
      edsPreimageInterToSquare_fst])
    (by rw [Category.assoc, edsPreimageInterToSquare_snd, ← Category.assoc,
      ← edsSnd_comp_edsPreimageEtaleMap, Category.assoc, edsPreimageEtaleMap_comp_toBase,
      edsPreimageInterToSquare_snd])

variable {W''' : AlgebraicSpaces B S hS} (p₃ : W''' ⟶ W)

/-- The maps of open subspaces induced by `q'` and `q` compose to the map induced by
`q' ≫ q`. -/
@[reassoc]
theorem edsPreimageOpenMap_comp_map (q : W'' ⟶ W') (hq : q ≫ p₁ = p₂) (q' : W''' ⟶ W'')
    (hq' : q' ≫ p₂ = p₃) :
    edsPreimageOpenMap hsq p₂ p₃ q' hq' ≫ edsPreimageOpenMap hsq p₁ p₂ q hq =
      edsPreimageOpenMap hsq p₁ p₃ (q' ≫ q) (by rw [Category.assoc, hq, hq']) :=
  edsOpen_hom_ext (edsPreimage hsq p₁) (by
    rw [Category.assoc, ← edsPreimageOpenMap_comp, ← Category.assoc, ← edsPreimageOpenMap_comp,
      ← edsPreimageOpenMap_comp, Category.assoc])

/-- The maps of étale algebraic spaces induced by `q'` and `q` compose to the map induced by
`q' ≫ q`. -/
@[reassoc]
theorem edsPreimageEtaleMap_comp_map (q : W'' ⟶ W') (hq : q ≫ p₁ = p₂) (q' : W''' ⟶ W'')
    (hq' : q' ≫ p₂ = p₃) :
    edsPreimageEtaleMap hsq p₂ p₃ q' hq' ≫ edsPreimageEtaleMap hsq p₁ p₂ q hq =
      edsPreimageEtaleMap hsq p₁ p₃ (q' ≫ q) (by rw [Category.assoc, hq, hq']) :=
  edsPreimageEtale_hom_ext hsq p₁
    (by rw [Category.assoc, edsPreimageEtaleMap_comp_toBase, edsPreimageEtaleMap_comp_toBase,
      edsPreimageEtaleMap_comp_toBase])
    (by rw [Category.assoc, ← edsPreimageEtaleMap_comp, ← Category.assoc,
      ← edsPreimageEtaleMap_comp, ← edsPreimageEtaleMap_comp, Category.assoc])

/-- The maps of intersections induced by `q'` and `q` compose to the map induced by
`q' ≫ q`. -/
@[reassoc]
theorem edsPreimageInterMap_comp_map (q : W'' ⟶ W') (hq : q ≫ p₁ = p₂) (q' : W''' ⟶ W'')
    (hq' : q' ≫ p₂ = p₃) :
    edsPreimageInterMap hsq p₂ p₃ q' hq' ≫ edsPreimageInterMap hsq p₁ p₂ q hq =
      edsPreimageInterMap hsq p₁ p₃ (q' ≫ q) (by rw [Category.assoc, hq, hq']) :=
  edsInter_hom_ext (edsPreimage hsq p₁)
    (by rw [Category.assoc, ← edsFst_comp_edsPreimageOpenMap, ← Category.assoc,
      ← edsFst_comp_edsPreimageOpenMap, Category.assoc, edsPreimageOpenMap_comp_map,
      ← edsFst_comp_edsPreimageOpenMap])
    (by rw [Category.assoc, ← edsSnd_comp_edsPreimageEtaleMap, ← Category.assoc,
      ← edsSnd_comp_edsPreimageEtaleMap, Category.assoc, edsPreimageEtaleMap_comp_map,
      ← edsSnd_comp_edsPreimageEtaleMap])

end Maps

/-! ### The three systems -/

section Systems

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {J : Type w} [Preorder J] (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W J)

/-- **The open subspaces `U ×_W W_j` of the base changes of an elementary distinguished square
along a directed system over `W`**, as a directed system over `U`. -/
abbrev edsOpenSystem : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) (edsOpen B S hS hsq) J
    where
  stage j := edsOpen B S hS (edsPreimage hsq (Sys.toBase j))
  toBase j := edsPreimageOpenToSquare hsq (Sys.toBase j)
  transition {i j} h := edsPreimageOpenMap hsq (Sys.toBase i) (Sys.toBase j) (Sys.transition h)
    (Sys.transition_toBase h)
  transition_toBase _ := edsPreimageOpenMap_comp_toBase hsq _ _ _ _
  transition_comp _ _ := (edsPreimageOpenMap_comp_map hsq _ _ _ _ _ _ _).trans (by
    congr 1; exact Sys.transition_comp _ _)
  limit := edsOpen B S hS (edsPreimage hsq Sys.limitToBase)
  limitToBase := edsPreimageOpenToSquare hsq Sys.limitToBase
  proj j := edsPreimageOpenMap hsq (Sys.toBase j) Sys.limitToBase (Sys.proj j) (Sys.proj_toBase j)
  proj_toBase _ := edsPreimageOpenMap_comp_toBase hsq _ _ _ _
  proj_transition _ := (edsPreimageOpenMap_comp_map hsq _ _ _ _ _ _ _).trans (by
    congr 1; exact Sys.proj_transition _)

/-- **The étale algebraic spaces `V ×_W W_j` of the base changes of an elementary distinguished
square along a directed system over `W`**, as a directed system over `V`. -/
abbrev edsEtaleSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) (edsEtale B S hS hsq) J where
  stage j := edsEtale B S hS (edsPreimage hsq (Sys.toBase j))
  toBase j := edsPreimageEtaleToSquare hsq (Sys.toBase j)
  transition {i j} h := edsPreimageEtaleMap hsq (Sys.toBase i) (Sys.toBase j) (Sys.transition h)
    (Sys.transition_toBase h)
  transition_toBase _ := edsPreimageEtaleMap_comp_toBase hsq _ _ _ _
  transition_comp _ _ := (edsPreimageEtaleMap_comp_map hsq _ _ _ _ _ _ _).trans (by
    congr 1; exact Sys.transition_comp _ _)
  limit := edsEtale B S hS (edsPreimage hsq Sys.limitToBase)
  limitToBase := edsPreimageEtaleToSquare hsq Sys.limitToBase
  proj j := edsPreimageEtaleMap hsq (Sys.toBase j) Sys.limitToBase (Sys.proj j) (Sys.proj_toBase j)
  proj_toBase _ := edsPreimageEtaleMap_comp_toBase hsq _ _ _ _
  proj_transition _ := (edsPreimageEtaleMap_comp_map hsq _ _ _ _ _ _ _).trans (by
    congr 1; exact Sys.proj_transition _)

/-- **The intersections `U_j ×_{W_j} V_j` of the base changes of an elementary distinguished
square along a directed system over `W`**, as a directed system over `U ×_W V`. -/
abbrev edsInterSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) (edsInter B S hS hsq) J where
  stage j := edsInter B S hS (edsPreimage hsq (Sys.toBase j))
  toBase j := edsPreimageInterToSquare hsq (Sys.toBase j)
  transition {i j} h := edsPreimageInterMap hsq (Sys.toBase i) (Sys.toBase j) (Sys.transition h)
    (Sys.transition_toBase h)
  transition_toBase _ := edsPreimageInterMap_comp_toBase hsq _ _ _ _
  transition_comp _ _ := (edsPreimageInterMap_comp_map hsq _ _ _ _ _ _ _).trans (by
    congr 1; exact Sys.transition_comp _ _)
  limit := edsInter B S hS (edsPreimage hsq Sys.limitToBase)
  limitToBase := edsPreimageInterToSquare hsq Sys.limitToBase
  proj j := edsPreimageInterMap hsq (Sys.toBase j) Sys.limitToBase (Sys.proj j) (Sys.proj_toBase j)
  proj_toBase _ := edsPreimageInterMap_comp_toBase hsq _ _ _ _
  proj_transition _ := (edsPreimageInterMap_comp_map hsq _ _ _ _ _ _ _).trans (by
    congr 1; exact Sys.proj_transition _)

end Systems

/-! ### Their presentations -/

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I}
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {y : W ⟶ D.stage D.base}
  {Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages}
  (β : D.BaseChangeData y Sys)

namespace BaseChangeData

/-- **The open subspaces of the base changes of the square form a presented system.** -/
def edsOpen {y' : edsOpen B S hS hsq ⟶ D.stage D.base} (hy : edsOpenHom B S hS hsq ≫ y = y') :
    D.BaseChangeData y' (edsOpenSystem hsq Sys) :=
  β.ofIsPullback (edsOpenHom B S hS hsq) hy
    (fun j => edsOpenHom B S hS (edsPreimage hsq (Sys.toBase j)))
    (fun j => (Subfunctor.isPullback_preimage (Sys.toBase j).hom Uo).flip)
    (fun h => (edsPreimageOpenMap_comp hsq _ _ _ (Sys.transition_toBase h)).symm)
    (edsOpenHom B S hS (edsPreimage hsq Sys.limitToBase))
    (Subfunctor.isPullback_preimage Sys.limitToBase.hom Uo).flip
    (fun j => (edsPreimageOpenMap_comp hsq _ _ _ (Sys.proj_toBase j)).symm)

/-- **The étale algebraic spaces of the base changes of the square form a presented system.** -/
def edsEtale {y' : edsEtale B S hS hsq ⟶ D.stage D.base} (hy : edsEtaleHom B S hS hsq ≫ y = y') :
    D.BaseChangeData y' (edsEtaleSystem hsq Sys) :=
  β.ofIsPullback (edsEtaleHom B S hS hsq) hy
    (fun j => edsEtaleHom B S hS (edsPreimage hsq (Sys.toBase j)))
    (fun j => (IsPullback.of_hasPullback fV (Sys.toBase j).hom).flip)
    (fun h => (edsPreimageEtaleMap_comp hsq _ _ _ (Sys.transition_toBase h)).symm)
    (edsEtaleHom B S hS (edsPreimage hsq Sys.limitToBase))
    (IsPullback.of_hasPullback fV Sys.limitToBase.hom).flip
    (fun j => (edsPreimageEtaleMap_comp hsq _ _ _ (Sys.proj_toBase j)).symm)

/-- **The intersections of the base changes of the square form a presented system.** -/
def edsInter {y' : edsInter B S hS hsq ⟶ D.stage D.base}
    (hy : edsFst B S hS hsq ≫ edsOpenHom B S hS hsq ≫ y = y') :
    D.BaseChangeData y' (edsInterSystem hsq Sys) :=
  (β.edsOpen hsq rfl).ofIsPullback (edsFst B S hS hsq) hy
    (fun j => edsFst B S hS (edsPreimage hsq (Sys.toBase j)))
    (fun j => isPullback_edsPreimageInter hsq (Sys.toBase j))
    (fun h => (edsFst_comp_edsPreimageOpenMap hsq _ _ _ (Sys.transition_toBase h)).symm)
    (edsFst B S hS (edsPreimage hsq Sys.limitToBase))
    (isPullback_edsPreimageInter hsq Sys.limitToBase)
    (fun j => (edsFst_comp_edsPreimageOpenMap hsq _ _ _ (Sys.proj_toBase j)).symm)

end BaseChangeData

end DescentSituation

end AlgebraicGeometry.Space

end
