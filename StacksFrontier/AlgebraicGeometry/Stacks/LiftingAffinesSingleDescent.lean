module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackOneMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentRepresentableCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering

/-!
# Descent of smooth lifts along one étale surjective morphism (Stacks 0CJU)

Let `ε : X ⟶ U` be an étale surjective morphism of the spaces-étale site of `W` with `X`
representable, `ξ` a smooth lift over `X` and `σ₁, σ₂ : η ⟶ ξ` morphisms of smooth lifts over the
two projections of `X ×_U X` which are reflexive, symmetric and transitive. This file constructs
the source's quotient `U' = Y / R'`, where `Y` and `R'` are the ambient spaces of `ξ` and `η`, and
shows that `U` is the base change of `U'` along the quotient map.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_quotientData`: the quotient `Q`, the quotient
  map `e : Y ⟶ Q`, the descended inclusion `U ⟶ Q`, and the cartesian square `X = U ×_Q Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **Stacks 05ZR, unconditionally.** The ambient space of a smooth lift over a representable base
is representable. -/
theorem isRepresentable_ambient (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (hrep : ξ.base.obj.left.obj.IsRepresentable) : ξ.ambient.obj.IsRepresentable :=
  Space.isRepresentable_of_isThickeningHom_of_affineCase B S hS ξ.inclusion
    (isThickeningHom_inclusion ξ) hrep
    (fun j hP hW hj hs ha =>
      Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace B S hS j hP hW
        hj hs ha)

variable {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (σ₁ σ₂ : η ⟶ ξ)
  {U : Space.SpacesEtale B S hS W} {ε : ξ.base ⟶ U}

/-- The base of the overlap is representable when the base of `ξ` is. -/
theorem isRepresentable_overlap (hrep : ξ.base.obj.left.obj.IsRepresentable)
    (hpb : IsPullback (Hom.base σ₁) (Hom.base σ₂) ε ε) :
    η.base.obj.left.obj.IsRepresentable := by
  let iX := ξ.base.obj.left.obj.reprW
  have hP := AlgebraicSpaces.isPullback_hom B S hS
    (hpb.map (Space.SpacesEtale.toSpaces B S hS W))
  have hP' : IsPullback ((Hom.base σ₁).hom.left.hom ≫ iX.inv) ((Hom.base σ₂).hom.left.hom ≫ iX.inv)
      (iX.hom ≫ ε.hom.left.hom) (iX.hom ≫ ε.hom.left.hom) :=
    hP.of_iso (Iso.refl _) iX.symm iX.symm (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have := Space.isRepresentable_pullback_of_yoneda B S hS (Y := U.obj.left)
    (iX.hom ≫ ε.hom.left.hom) (iX.hom ≫ ε.hom.left.hom)
  exact isRepresentable_of_natIso _ hP'.isoPullback.symm

/-- **The quotient of the relation and the descended inclusion** (Stacks 0CJU). Under the
hypotheses of this section, there are an algebraic space `Q`, an étale surjective `e : Y ⟶ Q` with
kernel pair `(t, s)`, and `i : U ⟶ Q` with `X = U ×_Q Y`. -/
theorem exists_quotientData (hrep : ξ.base.obj.left.obj.IsRepresentable)
    (hsurj : Space.IsSurjective B S hS ε.hom.left.hom)
    (hpb : IsPullback (Hom.base σ₁) (Hom.base σ₂) ε ε)
    (hrefl : ∃ r : ξ ⟶ η, r ≫ σ₁ = 𝟙 ξ ∧ r ≫ σ₂ = 𝟙 ξ)
    (hsymm : ∃ v : η ⟶ η, v ≫ σ₁ = σ₂ ∧ v ≫ σ₂ = σ₁)
    (htrans : ∀ (ω : EtaleSmoothLift B S hS ι hι W x hx) (a b : ω ⟶ η),
      IsPullback (Hom.base a) (Hom.base b) (Hom.base σ₂) (Hom.base σ₁) → a ≫ σ₂ = b ≫ σ₁ →
        ∃ c : ω ⟶ η, c ≫ σ₁ = a ≫ σ₁ ∧ c ≫ σ₂ = b ≫ σ₂) :
    ∃ (Q : AlgebraicSpaces B S hS) (e : ξ.ambient ⟶ Q) (i : U.obj.left ⟶ Q),
      IsPullback (Hom.ambient σ₂) (Hom.ambient σ₁) e e ∧ Space.IsEtale B S hS e.hom ∧
        Space.IsSurjective B S hS e.hom ∧ ξ.inclusion ≫ e = ε.hom.left ≫ i ∧
          IsPullback ξ.inclusion ε.hom.left e i := by
  have hYrep := isRepresentable_ambient ξ hrep
  have hRrep := isRepresentable_ambient η (isRepresentable_overlap σ₁ σ₂ hrep hpb)
  obtain ⟨Q, e, hkp, het, hsur⟩ := Space.exists_etaleQuotient_of_isEquivalenceRelation B S hS
    hRrep hYrep (Hom.ambient σ₁) (Hom.ambient σ₂) (Hom.isEtale_ambient η ξ σ₁)
    (Hom.isEtale_ambient η ξ σ₂) (isEquivalenceRelation_ambient σ₁ σ₂ hpb hrefl hsymm htrans)
  let X := ξ.base.obj.left
  let b₁ := (Hom.base σ₁).hom.left
  let b₂ := (Hom.base σ₂).hom.left
  have hpbA : IsPullback b₁ b₂ ε.hom.left ε.hom.left :=
    hpb.map (Space.SpacesEtale.toSpaces B S hS W)
  have hw₁ : η.inclusion ≫ Hom.ambient σ₁ = b₁ ≫ ξ.inclusion := Hom.inclusion_comp σ₁
  have hw₂ : η.inclusion ≫ Hom.ambient σ₂ = b₂ ≫ ξ.inclusion := Hom.inclusion_comp σ₂
  have hεet : Space.IsEtale B S hS ε.hom.left.hom :=
    Space.SpacesEtale.isEtale_toSpaces_map B S hS W ε
  have hcovε : Space.IsEtaleCovering B S hS (fun _ : PUnit.{u + 1} => X.obj)
      (fun _ => ε.hom.left.hom) :=
    ⟨U.obj.left.property, fun _ => X.property, fun _ => hεet, by
      refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨PUnit.unit, hsurj y⟩⟩
  obtain ⟨i, hi, -⟩ := Space.existsUnique_desc_of_fpqcCovering B S hS (I := PUnit.{u + 1})
    (X := fun _ => X) (fun _ => ε.hom.left)
    (Space.isFpqcCovering_of_isEtaleCovering B S hS _ _ hcovε) Q (fun _ => ξ.inclusion ≫ e)
    (fun _ _ => by
      let P := AlgebraicSpaces.fiberProduct B S hS ε.hom.left ε.hom.left
      have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS ε.hom.left ε.hom.left
      let k : P ⟶ η.base.obj.left := hpbA.lift _ _ hP.w
      have hk₁ : k ≫ b₁ = ObjectProperty.homMk (pullback.fst _ _) := hpbA.lift_fst _ _ _
      have hk₂ : k ≫ b₂ = ObjectProperty.homMk (pullback.snd _ _) := hpbA.lift_snd _ _ _
      show (ObjectProperty.homMk (pullback.fst _ _) : P ⟶ X) ≫ ξ.inclusion ≫ e =
        (ObjectProperty.homMk (pullback.snd _ _) : P ⟶ X) ≫ ξ.inclusion ≫ e
      rw [← hk₁, ← hk₂, Category.assoc, Category.assoc, ← reassoc_of% hw₁, ← reassoc_of% hw₂,
        hkp.w])
  have hcomm : ξ.inclusion ≫ e = ε.hom.left ≫ i := (hi PUnit.unit).symm
  refine ⟨Q, e, i, hkp, het, hsur, hcomm, ?_⟩
  let P := AlgebraicSpaces.fiberProduct B S hS e i
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS e i
  let Pf : P ⟶ ξ.ambient := ObjectProperty.homMk (pullback.fst e.hom i.hom)
  let Ps : P ⟶ U.obj.left := ObjectProperty.homMk (pullback.snd e.hom i.hom)
  let c : X ⟶ P := hP.lift ξ.inclusion ε.hom.left hcomm
  have hc₁ : c ≫ Pf = ξ.inclusion := hP.lift_fst _ _ _
  have hc₂ : c ≫ Ps = ε.hom.left := hP.lift_snd _ _ _
  suffices hc : IsIso c from hP.of_iso' (asIso c) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using hc₁) (by simpa using hc₂) (by simp) (by simp)
  let P' := AlgebraicSpaces.fiberProduct B S hS Ps ε.hom.left
  have hP' := AlgebraicSpaces.isPullback_fiberProduct B S hS Ps ε.hom.left
  let g : P' ⟶ P := ObjectProperty.homMk (pullback.fst Ps.hom ε.hom.left.hom)
  let g' : P' ⟶ X := ObjectProperty.homMk (pullback.snd Ps.hom ε.hom.left.hom)
  have hcov : Space.IsEtaleCovering B S hS (fun _ : PUnit.{u + 1} => P'.obj) (fun _ => g.hom) :=
    Space.isEtaleCovering_pullback B S hS Ps.hom P.property (fun _ => X.obj)
      (fun _ => ε.hom.left.hom) hcovε
  have hk : IsIso (pullback.snd c g) := by
    let mk : η.base.obj.left ⟶ P' := hP'.lift (b₁ ≫ c) b₂ (by rw [Category.assoc, hc₂, hpbA.w])
    have hmk₁ : mk ≫ g = b₁ ≫ c := hP'.lift_fst _ _ _
    have hmk₂ : mk ≫ g' = b₂ := hP'.lift_snd _ _ _
    have hsq : IsPullback b₁ mk c g :=
      IsPullback.of_bot (by rw [hmk₂, hc₂]; exact hpbA) hmk₁.symm hP'
    have A2 := isPullback_of_hom σ₂
    have hr : (g' ≫ ξ.inclusion) ≫ e = (g ≫ Pf) ≫ e := by
      rw [Category.assoc, hcomm, ← Category.assoc, ← hP'.w, Category.assoc, ← hP.w,
        Category.assoc]
    let r : P' ⟶ η.ambient := hkp.lift (g' ≫ ξ.inclusion) (g ≫ Pf) hr
    have hr₁ : r ≫ Hom.ambient σ₂ = g' ≫ ξ.inclusion := hkp.lift_fst _ _ _
    have hr₂ : r ≫ Hom.ambient σ₁ = g ≫ Pf := hkp.lift_snd _ _ _
    let wv : P' ⟶ η.base.obj.left := A2.lift r g' hr₁
    have hv₁ : wv ≫ η.inclusion = r := A2.lift_fst _ _ _
    have hv₂ : wv ≫ b₂ = g' := A2.lift_snd _ _ _
    have hmkiso : IsIso mk := by
      refine ⟨⟨wv, ?_, ?_⟩⟩
      · apply A2.hom_ext
        · rw [Category.assoc, hv₁, Category.id_comp]
          apply hkp.hom_ext
          · rw [Category.assoc, hr₁, ← Category.assoc, hmk₂, hw₂]
          · rw [Category.assoc, hr₂, ← Category.assoc, hmk₁, Category.assoc, hc₁, hw₁]
        · rw [Category.assoc, hv₂, hmk₂, Category.id_comp]
      · apply hP'.hom_ext
        · rw [Category.assoc, hmk₁, Category.id_comp]
          apply hP.hom_ext
          · rw [Category.assoc, Category.assoc, hc₁, ← hw₁, ← Category.assoc, hv₁, hr₂]
          · rw [Category.assoc, Category.assoc, hc₂, hpbA.w, ← Category.assoc, hv₂, ← hP'.w]
        · rw [Category.assoc, hmk₂, hv₂, Category.id_comp]
    rw [← hsq.isoPullback_inv_snd]
    infer_instance
  let Kp := Space.Topology.precoverage.{u, u} .fpqc B S hS
  let _ : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget Kp :=
    Space.isomorphisms_isLocalAtTarget_fpqc.{u, u} B S hS
  have hmem : Presieve.ofArrows (fun _ : PUnit.{u + 1} => P') (fun _ => g) ∈ Kp P :=
    ⟨PUnit.{u + 1}, fun _ => P', fun _ => g, rfl, P.property, fun _ => P'.property,
      Space.isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := MorphismProperty.isomorphisms _) hmem
  rintro V gV _ ⟨k⟩
  exact hk

end EtaleSmoothLift

end AlgebraicGeometry.Stack
