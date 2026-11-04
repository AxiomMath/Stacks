module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesDescentMorphisms
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SpacesImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSupportedLift
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleAmbient

/-!
# The étale equivalence relation of a descent datum along one étale morphism (Stacks 0CJU)

Let `ξ` be a smooth lift of an étale open `X ⟶ W` along a thickening `ι : 𝒳 ⟶ 𝒳'`, and let
`σ₁, σ₂ : η ⟶ ξ` be morphisms of smooth lifts lying over the two projections of a fibre product
`X ×_U X`, for an étale `ε : X ⟶ U`. Their ambient components `s, t : R' ⟶ Y` are the two legs of
the relation of the source's proof of Stacks 0CJU. This file shows that `(t, s)` is an
equivalence relation on the presheaf of `Y`, granted the reflexivity, symmetry and transitivity
of the pair `(σ₁, σ₂)` as morphisms of smooth lifts.

The relation is jointly monic by **Stacks 0BPJ**, part (6): `(s, t) : R' ⟶ Y × Y` restricts, along
the thickenings `X ×_U X ⊂ R'` and `X × X ⊂ Y × Y`, to the monomorphism `X ×_U X ⟶ X × X`, and the
square is cartesian. This is the source's "a monomorphism by Stacks 0BPG part (6)".

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.mono_lift_ambient`: `(s, t) : R' ⟶ Y × Y` is a
  monomorphism.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.equivalenceRelation_ambient`: `(t, s)` is an
  equivalence relation of presheaves.
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

/-- **A product of thickenings is a thickening.** The map `X × X ⟶ Y × Y` induced by a
thickening `i : X ⟶ Y` is the composite of two base changes of `i`. -/
theorem isThickeningHom_prodMap {X Y : AlgebraicSpaces B S hS} {i : X ⟶ Y}
    (hi : Space.IsThickeningHom B S hS i) :
    Space.IsThickeningHom B S hS
      (ObjectProperty.homMk (prod.map i.hom i.hom) :
        AlgebraicSpaces.product B S hS X X ⟶ AlgebraicSpaces.product B S hS Y Y) := by
  let P₁ := AlgebraicSpaces.product B S hS X X
  let P₂ := AlgebraicSpaces.product B S hS Y X
  let P₃ := AlgebraicSpaces.product B S hS Y Y
  let j₁ : P₁ ⟶ P₂ := ObjectProperty.homMk (prod.map i.hom (𝟙 X.obj))
  let j₂ : P₂ ⟶ P₃ := ObjectProperty.homMk (prod.map (𝟙 Y.obj) i.hom)
  have h₁ : Space.IsThickeningHom B S hS j₁ :=
    Space.IsThickeningHom.of_isPullback B S hS (i := i)
      (g := (ObjectProperty.homMk prod.fst : P₂ ⟶ Y))
      (l := (ObjectProperty.homMk prod.fst : P₁ ⟶ X))
      (Space.isPullback_of_isPullback_hom B S hS (IsPullback.of_prod_fst_with_id i.hom X.obj))
      hi
  have h₂ : Space.IsThickeningHom B S hS j₂ :=
    Space.IsThickeningHom.of_isPullback B S hS (i := i)
      (g := (ObjectProperty.homMk prod.snd : P₃ ⟶ Y))
      (l := (ObjectProperty.homMk prod.snd : P₂ ⟶ X))
      (Space.isPullback_of_isPullback_hom B S hS (IsPullback.of_prod_snd_with_id i.hom Y.obj))
      hi
  have hc : (ObjectProperty.homMk (prod.map i.hom i.hom) : P₁ ⟶ P₃) = j₁ ≫ j₂ :=
    ObjectProperty.hom_ext _ (by
      show prod.map i.hom i.hom = prod.map i.hom (𝟙 X.obj) ≫ prod.map (𝟙 Y.obj) i.hom
      refine prod.hom_ext ?_ ?_ <;> simp)
  rw [hc]
  obtain ⟨c₁, s₁⟩ := (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS j₁).1 h₁
  obtain ⟨c₂, s₂⟩ := (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS j₂).1 h₂
  exact (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).2
    ⟨Space.isClosedImmersion_comp B S hS _ _ c₁ c₂, Space.isSurjective_comp B S hS s₁ s₂⟩

variable {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (σ₁ σ₂ : η ⟶ ξ)
  {U : Space.SpacesEtale B S hS W} {ε : ξ.base ⟶ U}

/-- **The relation is a monomorphism into `Y × Y`** (**Stacks 0BPJ**, part (6)). -/
theorem mono_lift_ambient (hpb : IsPullback (Hom.base σ₁) (Hom.base σ₂) ε ε) :
    Mono (ObjectProperty.homMk (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom) :
      η.ambient ⟶ AlgebraicSpaces.product B S hS ξ.ambient ξ.ambient) := by
  let X := ξ.base.obj.left
  let b₁ := (Hom.base σ₁).hom.left
  let b₂ := (Hom.base σ₂).hom.left
  let f : η.base.obj.left ⟶ AlgebraicSpaces.product B S hS X X :=
    ObjectProperty.homMk (prod.lift b₁.hom b₂.hom)
  let f' : η.ambient ⟶ AlgebraicSpaces.product B S hS ξ.ambient ξ.ambient :=
    ObjectProperty.homMk (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom)
  let j : AlgebraicSpaces.product B S hS X X ⟶
      AlgebraicSpaces.product B S hS ξ.ambient ξ.ambient :=
    ObjectProperty.homMk (prod.map ξ.inclusion.hom ξ.inclusion.hom)
  have hA := AlgebraicSpaces.isPullback_hom B S hS (isPullback_of_hom σ₁)
  have hmono : Mono ξ.inclusion.hom := by
    have := ξ.mono_inclusion
    exact (ObjectProperty.ι _).map_mono ξ.inclusion
  have hw₂ : η.inclusion.hom ≫ (Hom.ambient σ₂).hom = b₂.hom ≫ ξ.inclusion.hom :=
    congrArg (·.hom) (Hom.inclusion_comp σ₂)
  -- the square of Stacks 0BPJ, part (6), is cartesian
  have hsq0 : IsPullback (prod.lift b₁.hom b₂.hom) η.inclusion.hom
      (prod.map ξ.inclusion.hom ξ.inclusion.hom)
      (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom) := by
    refine IsPullback.of_isLimit' ⟨?_⟩
      (PullbackCone.IsLimit.mk _ (fun c => hA.lift c.snd (c.fst ≫ prod.fst) ?_) ?_ ?_ ?_)
    · refine prod.hom_ext ?_ ?_
      · simpa using (congrArg (·.hom) (Hom.inclusion_comp σ₁)).symm
      · simpa using hw₂.symm
    · have hc : c.snd ≫ prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom =
          c.fst ≫ prod.map ξ.inclusion.hom ξ.inclusion.hom := c.condition.symm
      have h := congrArg (· ≫ prod.fst) hc
      simp only [Category.assoc, prod.lift_fst, prod.map_fst] at h
      rw [h, Category.assoc]
    · intro c
      refine prod.hom_ext ?_ ?_
      · simpa using hA.lift_snd _ _ _
      · rw [← cancel_mono ξ.inclusion.hom]
        have hc' : c.snd ≫ prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom =
            c.fst ≫ prod.map ξ.inclusion.hom ξ.inclusion.hom := c.condition.symm
        have hc := (congrArg (· ≫ prod.snd) hc').symm
        simp only [Category.assoc, prod.lift_snd, prod.map_snd] at hc ⊢
        rw [← hw₂, ← Category.assoc, hA.lift_fst, ← hc]
    · intro c
      exact hA.lift_fst _ _ _
    · intro c m hm₁ hm₂
      apply hA.hom_ext
      · rw [hA.lift_fst]; exact hm₂
      · rw [hA.lift_snd, ← hm₁]
        simp
        rfl
  have hsq : IsPullback f η.inclusion j f' :=
    Space.isPullback_of_isPullback_hom B S hS (fst := f) (snd := η.inclusion) (f := j) (g := f')
      hsq0
  have hi := isThickeningHom_inclusion η
  have hj : Space.IsThickeningHom B S hS j := isThickeningHom_prodMap (isThickeningHom_inclusion ξ)
  have hb₁ : Space.IsEtale B S hS b₁.hom := Space.SpacesEtale.isEtale_toSpaces_map B S hS W _
  have hs : Space.IsEtale B S hS (Hom.ambient σ₁).hom := Hom.isEtale_ambient η ξ σ₁
  have hft : Space.locallyOfFiniteTypeProperty B S hS f :=
    Space.isLocallyOfFiniteType_of_comp B S hS η.base.obj.left.property
      (AlgebraicSpaces.product B S hS X X).property X.property f.hom prod.fst
      (by
        show Space.IsLocallyOfFiniteType B S hS (prod.lift b₁.hom b₂.hom ≫ prod.fst)
        rw [prod.lift_fst]
        exact Space.isLocallyOfFiniteType_of_isEtale B S hS X.property hb₁)
  have hft' : Space.locallyOfFiniteTypeProperty B S hS f' :=
    Space.isLocallyOfFiniteType_of_comp B S hS η.ambient.property
      (AlgebraicSpaces.product B S hS ξ.ambient ξ.ambient).property ξ.ambient.property f'.hom
      prod.fst
      (by
        show Space.IsLocallyOfFiniteType B S hS
          (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom ≫ prod.fst)
        rw [prod.lift_fst]
        exact Space.isLocallyOfFiniteType_of_isEtale B S hS ξ.ambient.property hs)
  have hfmono : Mono f := by
    have hpb' := AlgebraicSpaces.isPullback_hom B S hS
      (hpb.map (Space.SpacesEtale.toSpaces B S hS W))
    refine ⟨fun g h hgh => ObjectProperty.hom_ext _ (hpb'.hom_ext ?_ ?_)⟩
    · have h1 : g.hom ≫ prod.lift b₁.hom b₂.hom = h.hom ≫ prod.lift b₁.hom b₂.hom :=
        congrArg (·.hom) hgh
      simpa using congrArg (· ≫ prod.fst) h1
    · have h1 : g.hom ≫ prod.lift b₁.hom b₂.hom = h.hom ≫ prod.lift b₁.hom b₂.hom :=
        congrArg (·.hom) hgh
      simpa using congrArg (· ≫ prod.snd) h1
  exact (Space.mono_iff_of_cartesianSquareOfThickeningHoms B S hS hi hj hsq hft hft').1 hfmono

/-- A pullback of a smooth lift along a morphism of the spaces-étale site, with its base read
as the given source up to an equality. -/
theorem exists_hom_base_eq {V : Space.SpacesEtale B S hS W} (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (f : V ⟶ ξ.base) :
    ∃ (η : EtaleSmoothLift B S hS ι hι W x hx) (φ : η ⟶ ξ) (h : η.base = V),
      Hom.base φ = eqToHom h ≫ f := by
  obtain ⟨η, φ, hφ⟩ := exists_hom_isHomLift ξ f
  refine ⟨η, φ, IsHomLift.domain_eq proj f φ, ?_⟩
  have h := IsHomLift.fac' proj f φ
  have h2 : eqToHom (IsHomLift.codomain_eq proj f φ).symm = 𝟙 ξ.base := eqToHom_refl _ _
  rw [h2] at h
  exact h.trans (congrArg (eqToHom (IsHomLift.domain_eq proj f φ) ≫ ·) (Category.comp_id f))

/-- **The relation of a descent datum along one étale morphism is an equivalence relation.**
Let `σ₁, σ₂ : η ⟶ ξ` lie over the two projections of `X ×_U X`. If the pair `(σ₁, σ₂)` is
reflexive, symmetric and transitive as a pair of morphisms of smooth lifts, then the ambient
components `(t, s)` form an equivalence relation of presheaves: jointly monic by
`AlgebraicGeometry.Stack.EtaleSmoothLift.mono_lift_ambient`, and the three witnesses are the
ambient components of the given ones, the fibre product of `(s, t)` being the ambient space of a
smooth lift over the triple overlap by
`AlgebraicGeometry.Stack.EtaleSmoothLift.isPullback_ambient`. -/
theorem isEquivalenceRelation_ambient (hpb : IsPullback (Hom.base σ₁) (Hom.base σ₂) ε ε)
    (hrefl : ∃ r : ξ ⟶ η, r ≫ σ₁ = 𝟙 ξ ∧ r ≫ σ₂ = 𝟙 ξ)
    (hsymm : ∃ v : η ⟶ η, v ≫ σ₁ = σ₂ ∧ v ≫ σ₂ = σ₁)
    (htrans : ∀ (ω : EtaleSmoothLift B S hS ι hι W x hx) (a b : ω ⟶ η),
      IsPullback (Hom.base a) (Hom.base b) (Hom.base σ₂) (Hom.base σ₁) → a ≫ σ₂ = b ≫ σ₁ →
        ∃ c : ω ⟶ η, c ≫ σ₁ = a ≫ σ₁ ∧ c ≫ σ₂ = b ≫ σ₂) :
    IsEquivalenceRelation (Hom.ambient σ₂).hom (Hom.ambient σ₁).hom := by
  have hm := mono_lift_ambient σ₁ σ₂ hpb
  have hm' : Mono (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom) := by
    have hk := AlgebraicSpaces.isPullback_hom B S hS (IsKernelPair.id_of_mono
      (ObjectProperty.homMk (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom) :
        η.ambient ⟶ AlgebraicSpaces.product B S hS ξ.ambient ξ.ambient))
    exact IsKernelPair.mono_of_isIso_fst hk
  have jm : JointlyMono₂ (Hom.ambient σ₂).hom (Hom.ambient σ₁).hom :=
    ⟨fun _ f g h₂ h₁ => (cancel_mono (prod.lift (Hom.ambient σ₁).hom (Hom.ambient σ₂).hom)).1
      (prod.hom_ext (by simpa using h₁) (by simpa using h₂))⟩
  obtain ⟨r, hr₁, hr₂⟩ := hrefl
  obtain ⟨v, hv₁, hv₂⟩ := hsymm
  obtain ⟨ω, a, hω, ha⟩ := exists_hom_base_eq η (pullback.fst (Hom.base σ₂) (Hom.base σ₁))
  have hh : (eqToHom hω ≫ pullback.snd (Hom.base σ₂) (Hom.base σ₁)) ≫ Hom.base σ₁ =
      Hom.base (a ≫ σ₂) := by
    show _ = Hom.base a ≫ Hom.base σ₂
    rw [ha, Category.assoc, Category.assoc, pullback.condition]
  let b : ω ⟶ η := fillIn σ₁ (a ≫ σ₂) _ hh
  have hab : a ≫ σ₂ = b ≫ σ₁ := (fillIn_comp σ₁ (a ≫ σ₂) _ hh).symm
  have hbase : IsPullback (Hom.base a) (Hom.base b) (Hom.base σ₂) (Hom.base σ₁) := by
    refine (IsPullback.of_hasPullback (Hom.base σ₂) (Hom.base σ₁)).of_iso (eqToIso hω.symm)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp [ha]
    · show _ = _ ≫ (eqToHom hω ≫ pullback.snd _ _)
      simp
  obtain ⟨c, hc₁, hc₂⟩ := htrans ω a b hbase hab
  have hamb := (AlgebraicSpaces.isPullback_hom B S hS
    (isPullback_ambient σ₂ σ₁ a b hab hbase)).flip
  exact ⟨⟨{ toJointlyMono₂ := jm,
             r := (Hom.ambient r).hom,
             reflexivity₁ := congrArg (fun m => (Hom.ambient m).hom) hr₂,
             reflexivity₂ := congrArg (fun m => (Hom.ambient m).hom) hr₁,
             s := (Hom.ambient v).hom,
             symmetry₁ := congrArg (fun m => (Hom.ambient m).hom) hv₂,
             symmetry₂ := congrArg (fun m => (Hom.ambient m).hom) hv₁,
             c := hamb.cone,
             isLimit := hamb.isLimit,
             t := (Hom.ambient c).hom,
             transitivity₁ := congrArg (fun m => (Hom.ambient m).hom) hc₂,
             transitivity₂ := congrArg (fun m => (Hom.ambient m).hom) hc₁ }⟩⟩

end EtaleSmoothLift

end AlgebraicGeometry.Stack
