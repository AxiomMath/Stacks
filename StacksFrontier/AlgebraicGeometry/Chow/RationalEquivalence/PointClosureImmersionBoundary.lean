module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureSummandIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainLocalization
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.StalkMilnorBoundaryTransport

/-!
# The local boundary of Stacks 0GU9 along an immersion

Let `f : Z ⟶ X` be a morphism inducing an isomorphism on every residue field — a closed or an
open immersion — and let `x ⇝ t` be a specialization in `Z` with a drop of one in relative
dimension. Stacks 0GUA needs that the local component `∂_{𝒪_{W_x, t}}` of the first differential
of Stacks 0GU9 is the same computed in `Z` and computed in `X`, under the identifications of the
residue fields at `x` and at `t`.

That is what this file proves. The whole content is a comparison of the two reduced closures: the
reduced closure of `x` in `Z` must map to the reduced closure of `f x` in `X` by a morphism `ψ`
over `f` which is an open immersion, hence an isomorphism on local rings. Both immersions supply
such a `ψ` — an isomorphism for a closed immersion
(`Stacks.Chow.exists_iso_integralComponentAt_comp`), the base change of `f` for an open immersion
(`Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`) — and the comparison is then
`Stacks.Chow.stalkMilnorBoundary_ringEquiv`.

## Main definitions

* `Stacks.Chow.pointClosureImmersionMap` — the comparison morphism of reduced closures along an
  open immersion.

## Main results

* `Stacks.Chow.pointClosureResidueFieldEquiv_residue_stalkMap` — the identification of Stacks
  01RV of the residue field of `closure {x}` at one of its points with the residue field of the
  ambient scheme, computed on the residue of a germ pulled back along the closed immersion.
* `Stacks.Chow.pointClosureFunctionFieldEquiv_compat` — the fraction-field compatibility the
  transport of the tame symbol consumes.
* `Stacks.Chow.pointClosureMilnorBoundary_naturality` — **the local component of the first
  differential of Stacks 0GU9 is natural along a morphism admitting such a comparison.**
* `Stacks.Chow.pointClosureMilnorBoundary_naturality_isClosedImmersion`,
  `Stacks.Chow.pointClosureMilnorBoundary_naturality_isOpenImmersion` — the two immersions supply
  the comparison.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-- Two homomorphisms of fields agreeing on every element induce the same transport of Milnor
K-theory. Stated so that the two homomorphisms can be read off a goal, whatever shape the
coercions in it have. -/
theorem milnorKTransport_congr {k₁ k₂ : Type u} [Field k₁] [Field k₂] (φ φ' : k₁ →+* k₂)
    (hφ : ∀ a, φ a = φ' a) (n : ℕ) (y : MilnorKTheory k₁ n) :
    milnorKTransport φ n y = milnorKTransport φ' n y := by
  rw [show φ = φ' from RingHom.ext hφ]

/-! ### The residue field of a point of a reduced closure -/

/-- **Stacks 01RV, computed on a germ pulled back from the ambient scheme.** The identification of
the residue field of `closure {w}` at one of its points `z` with the residue field of `X` at the
image of `z` sends the residue of the germ pulled back along the closed immersion to the residue
of the germ itself. -/
theorem pointClosureResidueFieldEquiv_residue_stalkMap {X : Scheme.{u}} (w : X) {w' : X}
    (h : w' ∈ closure ({w} : Set X))
    (s : ↥(X.presheaf.stalk ((integralComponentAt w).subschemeι (pointClosurePoint w h)))) :
    pointClosureResidueFieldEquiv w h
        ((integralComponentAt w).subscheme.residue (pointClosurePoint w h)
          (((integralComponentAt w).subschemeι.stalkMap (pointClosurePoint w h)).hom s)) =
      X.residue w'
        ((X.presheaf.stalkCongr
          (Inseparable.of_eq (subschemeι_pointClosurePoint w h))).hom.hom s) := by
  have h1 : (integralComponentAt w).subscheme.residue (pointClosurePoint w h)
        (((integralComponentAt w).subschemeι.stalkMap (pointClosurePoint w h)).hom s) =
      ((integralComponentAt w).subschemeι.residueFieldMap (pointClosurePoint w h)).hom
        (X.residue ((integralComponentAt w).subschemeι (pointClosurePoint w h)) s) :=
    (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (Scheme.residue_residueFieldMap (integralComponentAt w).subschemeι
        (pointClosurePoint w h))) s).symm
  have h2 : pointClosureResidueFieldEquiv w h
        (((integralComponentAt w).subschemeι.residueFieldMap (pointClosurePoint w h)).hom
          (X.residue ((integralComponentAt w).subschemeι (pointClosurePoint w h)) s)) =
      (X.residueFieldCongr (subschemeι_pointClosurePoint w h)).hom.hom
        (X.residue ((integralComponentAt w).subschemeι (pointClosurePoint w h)) s) := by
    show (X.residueFieldCongr (subschemeι_pointClosurePoint w h)).hom.hom
      ((RingEquiv.ofBijective
        ((integralComponentAt w).subschemeι.residueFieldMap (pointClosurePoint w h)).hom
        (bijective_residueFieldMap_of_isClosedImmersion _ _)).symm
        (((integralComponentAt w).subschemeι.residueFieldMap (pointClosurePoint w h)).hom
          (X.residue ((integralComponentAt w).subschemeι (pointClosurePoint w h)) s))) = _
    exact congrArg (X.residueFieldCongr (subschemeι_pointClosurePoint w h)).hom.hom
      ((RingEquiv.symm_apply_eq _).mpr rfl)
  rw [h1, h2]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
    (X.residue_residueFieldCongr (subschemeι_pointClosurePoint w h))) s

/-- The residue field identification along `f` sends the residue of a germ to the residue of its
pullback. -/
private theorem immersionResidueFieldEquiv_residue {X Z : Scheme.{u}} (f : Z ⟶ X)
    (hbij : ∀ t : Z, Function.Bijective (f.residueFieldMap t).hom) (t : Z)
    (d : ↥(X.presheaf.stalk (f.base t))) :
    immersionResidueFieldEquiv f hbij t (X.residue (f.base t) d) =
      Z.residue t ((f.stalkMap t).hom d) :=
  (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (Scheme.residue_residueFieldMap f t)) d).symm

/-! ### The comparison of reduced closures along a morphism -/

section Comparison

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (x : Z)
  (ψ : (integralComponentAt x).subscheme ⟶ (integralComponentAt (f.base x)).subscheme)
  (hψ : ψ ≫ (integralComponentAt (f.base x)).subschemeι =
    (integralComponentAt x).subschemeι ≫ f)

include hψ

/-- The comparison morphism of reduced closures lies over `f`: the image in `X` of the image of a
point of `closure {x}` is the image under `f` of its image in `Z`. -/
theorem subschemeι_pointClosureComparison (v : (integralComponentAt x).subscheme) :
    (integralComponentAt (f.base x)).subschemeι.base (ψ.base v) =
      f.base ((integralComponentAt x).subschemeι.base v) := by
  have h := congrArg (fun g : (integralComponentAt x).subscheme ⟶ X => g.base v) hψ
  simpa using h

/-- The comparison morphism carries the point of `closure {x}` at `t` to the point of
`closure {f x}` at `f t`. -/
theorem pointClosureComparison_pointClosurePoint {t : Z} (h : t ∈ closure ({x} : Set Z))
    (h' : f.base t ∈ closure ({f.base x} : Set X)) :
    ψ.base (pointClosurePoint x h) = pointClosurePoint (f.base x) h' := by
  refine (integralComponentAt (f.base x)).subschemeι.isClosedEmbedding.injective ?_
  rw [subschemeι_pointClosureComparison f x ψ hψ, subschemeι_pointClosurePoint,
    subschemeι_pointClosurePoint]

/-- The stalk square of the comparison morphism, on a germ of the closure of `f x`. -/
private theorem stalkMap_pointClosureComparison (v : (integralComponentAt x).subscheme)
    (s : ↥(X.presheaf.stalk ((integralComponentAt (f.base x)).subschemeι.base (ψ.base v)))) :
    (ψ.stalkMap v).hom (((integralComponentAt (f.base x)).subschemeι.stalkMap (ψ.base v)).hom s) =
      ((integralComponentAt x).subschemeι.stalkMap v).hom
        ((f.stalkMap ((integralComponentAt x).subschemeι.base v)).hom
          ((X.presheaf.stalkCongr
            (Inseparable.of_eq (subschemeι_pointClosureComparison f x ψ hψ v))).hom.hom s)) := by
  have h : ((ψ ≫ (integralComponentAt (f.base x)).subschemeι).stalkMap v).hom s =
      (((integralComponentAt x).subschemeι ≫ f).stalkMap v).hom
        ((X.presheaf.stalkCongr
          (Inseparable.of_eq (subschemeι_pointClosureComparison f x ψ hψ v))).hom.hom s) := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hψ v]
    rfl
  rwa [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h

/-- **The fraction-field compatibility of the comparison.** The identification of Stacks 01RV of
the function field of a reduced closure with the residue field at its generic point turns the
germ map at a point of `closure {x}` into the residue at `x` of a specialized germ; both sides of
the square are therefore computed on the ambient schemes, where the compatibility is the
naturality of a stalk map against specialization. -/
theorem pointClosureFunctionFieldEquiv_comparison
    (hbij : ∀ t : Z, Function.Bijective (f.residueFieldMap t).hom)
    (v : (integralComponentAt x).subscheme)
    (hspec : x ⤳ (integralComponentAt x).subschemeι.base v)
    (hspec' : f.base x ⤳ (integralComponentAt (f.base x)).subschemeι.base (ψ.base v))
    (a : ↥((integralComponentAt (f.base x)).subscheme.presheaf.stalk (ψ.base v))) :
    immersionResidueFieldEquiv f hbij x
        (pointClosureFunctionFieldEquiv (f.base x)
          (algebraMap ↥((integralComponentAt (f.base x)).subscheme.presheaf.stalk (ψ.base v))
            ↥((integralComponentAt (f.base x)).subscheme.functionField) a)) =
      pointClosureFunctionFieldEquiv x
        (algebraMap ↥((integralComponentAt x).subscheme.presheaf.stalk v)
          ↥((integralComponentAt x).subscheme.functionField) ((ψ.stalkMap v).hom a)) := by
  have hsurj := (inferInstance :
    SurjectiveOnStalks (integralComponentAt (f.base x)).subschemeι).stalkMap_surjective
  obtain ⟨s, rfl⟩ := hsurj (ψ.base v) a
  have hpt := subschemeι_pointClosureComparison f x ψ hψ v
  -- the left-hand side, computed in `X` and then transported to `Z`
  rw [pointClosureFunctionFieldEquiv_algebraMap_stalkMap (f.base x) (ψ.base v) hspec' s]
  -- the right-hand side, computed in `Z`
  rw [stalkMap_pointClosureComparison f x ψ hψ v s,
    pointClosureFunctionFieldEquiv_algebraMap_stalkMap x v hspec]
  -- both sides are now residues of specialized germs
  change immersionResidueFieldEquiv f hbij x
      (X.residue (f.base x) ((X.presheaf.stalkSpecializes hspec').hom s)) = _
  rw [immersionResidueFieldEquiv_residue]
  refine congrArg (Z.residue x) ?_
  have key : ∀ {y y' : X} (hyy' : y = y') (hs : f.base x ⤳ y) (hs' : f.base x ⤳ y')
      (b : ↥(X.presheaf.stalk y)),
      (X.presheaf.stalkSpecializes hs).hom b =
        (X.presheaf.stalkSpecializes hs').hom
          ((X.presheaf.stalkCongr (Inseparable.of_eq hyy')).hom.hom b) := by
    intro y y' hyy' hs hs' b
    subst hyy'
    have hid : (X.presheaf.stalkCongr (Inseparable.of_eq (rfl : y = y))).hom =
        CategoryTheory.CategoryStruct.id _ := X.presheaf.stalkSpecializes_refl y
    rw [hid]
    rfl
  rw [key hpt hspec' (f.base.hom.map_specializes hspec) s,
    Scheme.Hom.stalkSpecializes_stalkMap_apply f x
      ((integralComponentAt x).subschemeι.base v) hspec]

omit hψ in
/-- Transport of a germ along an equality of points, read at the same point, is the identity. -/
theorem stalkCongr_hom_apply_rfl {y : X} (hy : y = y) (b : ↥(X.presheaf.stalk y)) :
    (X.presheaf.stalkCongr (Inseparable.of_eq hy)).hom.hom b = b := by
  have hid : (X.presheaf.stalkCongr (Inseparable.of_eq hy)).hom =
      CategoryTheory.CategoryStruct.id _ := X.presheaf.stalkSpecializes_refl y
  rw [hid]
  rfl

omit hψ in
/-- Transport of a germ along two equalities of points is transport along their composite. -/
theorem stalkCongr_hom_apply_trans {y₁ y₂ y₃ : X} (h₁₂ : y₁ = y₂) (h₂₃ : y₂ = y₃)
    (h₁₃ : y₁ = y₃) (b : ↥(X.presheaf.stalk y₁)) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h₂₃)).hom.hom
        ((X.presheaf.stalkCongr (Inseparable.of_eq h₁₂)).hom.hom b) =
      (X.presheaf.stalkCongr (Inseparable.of_eq h₁₃)).hom.hom b := by
  subst h₁₂
  subst h₂₃
  simp only [stalkCongr_hom_apply_rfl]

/-- **The residue-field compatibility of the comparison.** The identification of Stacks 01RV of
the residue field of a reduced closure at one of its points with the residue field of the ambient
scheme turns both sides of the square into the residue of a transported germ. -/
theorem pointClosureResidueFieldEquiv_comparison
    (hbij : ∀ t : Z, Function.Bijective (f.residueFieldMap t).hom) [IsOpenImmersion ψ]
    {t : Z} (h : t ∈ closure ({x} : Set Z)) (h' : f.base t ∈ closure ({f.base x} : Set X))
    (hzz : ψ.base (pointClosurePoint x h) = pointClosurePoint (f.base x) h')
    (b : ↥((integralComponentAt (f.base x)).subscheme.residueField
      (ψ.base (pointClosurePoint x h)))) :
    immersionResidueFieldEquiv f hbij t
        (pointClosureResidueFieldEquiv (f.base x) h'
          (((integralComponentAt (f.base x)).subscheme.residueFieldCongr hzz).hom.hom b)) =
      pointClosureResidueFieldEquiv x h
        (residueFieldEquivOfStalkEquiv
          (asIso (ψ.stalkMap (pointClosurePoint x h))).commRingCatIsoToRingEquiv b) := by
  have hsurj := (inferInstance :
    SurjectiveOnStalks (integralComponentAt (f.base x)).subschemeι).stalkMap_surjective
  obtain ⟨c, hc⟩ := (integralComponentAt (f.base x)).subscheme.residue_surjective
    (ψ.base (pointClosurePoint x h)) b
  obtain ⟨s, hs⟩ := hsurj (ψ.base (pointClosurePoint x h)) c
  subst hc
  subst hs
  have hpt := subschemeι_pointClosureComparison f x ψ hψ (pointClosurePoint x h)
  -- the right-hand side
  have hstalk : (asIso (ψ.stalkMap (pointClosurePoint x h))).commRingCatIsoToRingEquiv
      (((integralComponentAt (f.base x)).subschemeι.stalkMap
        (ψ.base (pointClosurePoint x h))).hom s) = _ :=
    stalkMap_pointClosureComparison f x ψ hψ _ s
  rw [residueFieldEquivOfStalkEquiv_residue, hstalk,
    pointClosureResidueFieldEquiv_residue_stalkMap x h]
  -- the left-hand side
  have hcongr : ((integralComponentAt (f.base x)).subscheme.residueFieldCongr hzz).hom.hom
        ((integralComponentAt (f.base x)).subscheme.residue (ψ.base (pointClosurePoint x h))
          (((integralComponentAt (f.base x)).subschemeι.stalkMap
            (ψ.base (pointClosurePoint x h))).hom s)) =
      (integralComponentAt (f.base x)).subscheme.residue (pointClosurePoint (f.base x) h')
        (((integralComponentAt (f.base x)).subschemeι.stalkMap
            (pointClosurePoint (f.base x) h')).hom
          ((X.presheaf.stalkCongr (Inseparable.of_eq
            (congrArg (integralComponentAt (f.base x)).subschemeι.base hzz))).hom.hom s)) := by
    have h1 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      ((integralComponentAt (f.base x)).subscheme.residue_residueFieldCongr hzz))
      (((integralComponentAt (f.base x)).subschemeι.stalkMap
        (ψ.base (pointClosurePoint x h))).hom s)
    have h2 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (Scheme.Hom.stalkMap_congr_point (integralComponentAt (f.base x)).subschemeι
        (ψ.base (pointClosurePoint x h)) (pointClosurePoint (f.base x) h') hzz)) s
    exact h1.trans (congrArg ((integralComponentAt (f.base x)).subscheme.residue
      (pointClosurePoint (f.base x) h')) h2)
  rw [hcongr, pointClosureResidueFieldEquiv_residue_stalkMap (f.base x) h']
  -- both sides are the residue at `t` of one transported germ
  rw [immersionResidueFieldEquiv_residue, stalkCongr_hom_apply_trans
    (congrArg (integralComponentAt (f.base x)).subschemeι.base hzz)
    (subschemeι_pointClosurePoint (f.base x) h')
    ((congrArg f.base (subschemeι_pointClosurePoint x h)).symm.trans hpt.symm).symm]
  refine congrArg (Z.residue t) ?_
  have hfc : (Z.presheaf.stalkCongr
        (Inseparable.of_eq (subschemeι_pointClosurePoint x h))).hom.hom
      ((f.stalkMap ((integralComponentAt x).subschemeι.base (pointClosurePoint x h))).hom
        ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom s)) =
      (f.stalkMap t).hom ((X.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg f.base (subschemeι_pointClosurePoint x h)))).hom.hom
          ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom s)) :=
    DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (Scheme.Hom.stalkMap_congr_point f
        ((integralComponentAt x).subschemeι.base (pointClosurePoint x h)) t
        (subschemeι_pointClosurePoint x h)))
      ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom s)
  rw [hfc, stalkCongr_hom_apply_trans hpt
    (congrArg f.base (subschemeι_pointClosurePoint x h))
    (hpt.trans (congrArg f.base (subschemeι_pointClosurePoint x h)))]

/-! ### Naturality of the local boundary -/

/-- **The local component `∂_{𝒪_{W_x, t}}` of the first differential of Stacks 0GU9 is natural
along a morphism carrying reduced closures to reduced closures.** Both squares the transport of
`Stacks.Chow.stalkMilnorBoundary_ringEquiv` consumes are supplied by the comparison `ψ`: the
fraction-field square by `Stacks.Chow.pointClosureFunctionFieldEquiv_comparison` and the
residue-field square by `Stacks.Chow.pointClosureResidueFieldEquiv_comparison`. -/
theorem pointClosureMilnorBoundary_comparison
    (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (q : Z ⟶ C.S) [LocallyOfFiniteType q]
    (hbij : ∀ t : Z, Function.Bijective (f.residueFieldMap t).hom) [IsOpenImmersion ψ]
    {t : Z} (h : t ∈ closure ({x} : Set Z)) (h' : f.base t ∈ closure ({f.base x} : Set X))
    (hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h)) = 1)
    (hdim' : ringKrullDim ((integralComponentAt (f.base x)).subscheme.presheaf.stalk
      (pointClosurePoint (f.base x) h')) = 1)
    (α : MilnorKTheory ↥(X.residueField (f.base x)) 2) :
    milnorKTransport (immersionResidueFieldEquiv f hbij t : _ →+* _) 1
        (pointClosureMilnorBoundary C p (f.base x) h' hdim' α) =
      pointClosureMilnorBoundary C q x h hdim
        (milnorKTransport (immersionResidueFieldEquiv f hbij x : _ →+* _) 2 α) := by
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ q)
  let : IsLocallyNoetherian (integralComponentAt (f.base x)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt (f.base x)).subschemeι ≫ p)
  have hzz : ψ.base (pointClosurePoint x h) = pointClosurePoint (f.base x) h' :=
    pointClosureComparison_pointClosurePoint f x ψ hψ h h'
  have hdimA : ringKrullDim ((integralComponentAt (f.base x)).subscheme.presheaf.stalk
      (ψ.base (pointClosurePoint x h))) = 1 := by rw [hzz]; exact hdim'
  have hspec : x ⤳ (integralComponentAt x).subschemeι.base (pointClosurePoint x h) := by
    rw [subschemeι_pointClosurePoint]
    exact specializes_iff_mem_closure.mpr h
  have hspec' : f.base x ⤳ (integralComponentAt (f.base x)).subschemeι.base
      (ψ.base (pointClosurePoint x h)) := by
    rw [subschemeι_pointClosureComparison f x ψ hψ, subschemeι_pointClosurePoint]
    exact specializes_iff_mem_closure.mpr h'
  have hSB := stalkMilnorBoundary_ringEquiv
    (pointClosureFunctionFieldEquiv (f.base x)) (pointClosureFunctionFieldEquiv x)
    (ψ.base (pointClosurePoint x h)) (pointClosurePoint x h)
    (asIso (ψ.stalkMap (pointClosurePoint x h))).commRingCatIsoToRingEquiv
    (immersionResidueFieldEquiv f hbij x)
    (fun a ↦ pointClosureFunctionFieldEquiv_comparison f x ψ hψ hbij
      (pointClosurePoint x h) hspec hspec' a) hdimA hdim α
  have hpc := stalkMilnorBoundary_point_congr (pointClosureFunctionFieldEquiv (f.base x))
    hzz hdimA hdim' α
  change milnorKTransport (immersionResidueFieldEquiv f hbij t : _ →+* _) 1
      (milnorKOneTransport (pointClosureResidueFieldEquiv (f.base x) h')
        (stalkMilnorBoundary (pointClosureFunctionFieldEquiv (f.base x))
          (pointClosurePoint (f.base x) h') hdim' α)) =
    milnorKOneTransport (pointClosureResidueFieldEquiv x h)
      (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h) hdim
        (milnorKTransport (immersionResidueFieldEquiv f hbij x : _ →+* _) 2 α))
  rw [← milnorKTransport_eq_milnorKOneTransport, ← milnorKTransport_eq_milnorKOneTransport,
    ← hpc, ← hSB, milnorKTransport_comp_apply, milnorKTransport_comp_apply,
    milnorKTransport_comp_apply]
  refine milnorKTransport_congr _ _ (fun b ↦ ?_) 1 _
  exact pointClosureResidueFieldEquiv_comparison f x ψ hψ hbij h h' hzz b

end Comparison

/-! ### The two immersions supply the comparison -/

/-- An equality of ideal sheaf data transports the closed immersion of the subscheme. -/
theorem eqToHom_subscheme_subschemeι {X : Scheme.{u}} (I J : X.IdealSheafData) (hIJ : I = J) :
    CategoryTheory.eqToHom (congrArg Scheme.IdealSheafData.subscheme hIJ) ≫ J.subschemeι =
      I.subschemeι := by
  subst hIJ
  simp

/-- **The comparison of reduced closures along an open immersion.** The reduced closure of `u` in
`U` is the inverse image of the reduced closure of `j u` in `X`
(`Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`), and the restriction of `j` to that
inverse image is a base change of `j`, hence again an open immersion. -/
def pointClosureOpenComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (u : U) :
    (integralComponentAt u).subscheme ⟶ (integralComponentAt (j.base u)).subscheme :=
  CategoryTheory.eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (comap_integralComponentAt_of_isOpenImmersion j u).symm) ≫
    comapRestrict (integralComponentAt (j.base u)) j

/-- The comparison of reduced closures along an open immersion is an open immersion. -/
instance {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (u : U) :
    IsOpenImmersion (pointClosureOpenComparison j u) := by
  have : IsOpenImmersion (comapRestrict (integralComponentAt (j.base u)) j) :=
    MorphismProperty.of_isPullback
      (isPullback_comapRestrict (integralComponentAt (j.base u)) j) inferInstance
  exact inferInstanceAs
    (IsOpenImmersion (CategoryTheory.eqToHom _ ≫ comapRestrict _ j))

/-- The comparison of reduced closures along an open immersion lies over the immersion. -/
theorem pointClosureOpenComparison_subschemeι {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (u : U) :
    pointClosureOpenComparison j u ≫ (integralComponentAt (j.base u)).subschemeι =
      (integralComponentAt u).subschemeι ≫ j := by
  rw [pointClosureOpenComparison, Category.assoc, comapRestrict_subschemeι, ← Category.assoc,
    eqToHom_subscheme_subschemeι (integralComponentAt u)
      ((integralComponentAt (j.base u)).comap j)
      (comap_integralComponentAt_of_isOpenImmersion j u).symm]

/-- **The local component of the first differential of Stacks 0GU9 is natural along an open
immersion.** -/
theorem pointClosureMilnorBoundary_isOpenImmersion (C : ChowSituation.{u}) {U X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : U ⟶ C.S) [LocallyOfFiniteType q] (j : U ⟶ X)
    [IsOpenImmersion j] (hbij : ∀ t : U, Function.Bijective (j.residueFieldMap t).hom) (u : U)
    {t : U} (h : t ∈ closure ({u} : Set U))
    (h' : j.base t ∈ closure ({j.base u} : Set X))
    (hdim : ringKrullDim ((integralComponentAt u).subscheme.presheaf.stalk
      (pointClosurePoint u h)) = 1)
    (hdim' : ringKrullDim ((integralComponentAt (j.base u)).subscheme.presheaf.stalk
      (pointClosurePoint (j.base u) h')) = 1)
    (α : MilnorKTheory ↥(X.residueField (j.base u)) 2) :
    milnorKTransport (immersionResidueFieldEquiv j hbij t : _ →+* _) 1
        (pointClosureMilnorBoundary C p (j.base u) h' hdim' α) =
      pointClosureMilnorBoundary C q u h hdim
        (milnorKTransport (immersionResidueFieldEquiv j hbij u : _ →+* _) 2 α) :=
  pointClosureMilnorBoundary_comparison j u (pointClosureOpenComparison j u)
    (pointClosureOpenComparison_subschemeι j u) C p q hbij h h' hdim hdim' α

/-- **The local component of the first differential of Stacks 0GU9 is natural along a closed
immersion.** The reduced closure of `y` in `Y` and the reduced closure of `i y` in `X` have the
same ideal sheaf, so they are isomorphic over `X`. -/
theorem pointClosureMilnorBoundary_isClosedImmersion (C : ChowSituation.{u}) {Y X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : Y ⟶ C.S) [LocallyOfFiniteType q] (i : Y ⟶ X)
    [IsClosedImmersion i] (hbij : ∀ t : Y, Function.Bijective (i.residueFieldMap t).hom) (y : Y)
    {t : Y} (h : t ∈ closure ({y} : Set Y)) (h' : i.base t ∈ closure ({i.base y} : Set X))
    (hdim : ringKrullDim ((integralComponentAt y).subscheme.presheaf.stalk
      (pointClosurePoint y h)) = 1)
    (hdim' : ringKrullDim ((integralComponentAt (i.base y)).subscheme.presheaf.stalk
      (pointClosurePoint (i.base y) h')) = 1)
    (α : MilnorKTheory ↥(X.residueField (i.base y)) 2) :
    milnorKTransport (immersionResidueFieldEquiv i hbij t : _ →+* _) 1
        (pointClosureMilnorBoundary C p (i.base y) h' hdim' α) =
      pointClosureMilnorBoundary C q y h hdim
        (milnorKTransport (immersionResidueFieldEquiv i hbij y : _ →+* _) 2 α) := by
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt_comp i y
  have : IsOpenImmersion e.hom := inferInstance
  exact pointClosureMilnorBoundary_comparison i y e.hom he C p q hbij h h' hdim hdim' α


end Stacks.Chow

end
