module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.IsomProper
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The isomorphism sheaf over the gerbe locus

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space over `S` and let
`V ⊆ Y` be an open subspace over which `𝒳` is a gerbe: the first projection of
`𝒳_V = V ×_Y 𝒳` is a gerbe. The proof of Stacks 0CQ7 uses that for two 1-morphisms
`x₁, x₂ : Z ⟶ 𝒳` out of an algebraic space with `x₁ ≫ f = x₂ ≫ f` factoring through `V`, the
algebraic space `Isom_𝒳(x₁, x₂)` of Stacks 06PP is surjective, flat and locally of finite
presentation over `Z`. This is Stacks 0CPR (4) for the gerbe `𝒳_V ⟶ V`, read through two
identifications:

* both points lift strictly to `𝒳_V` (`AlgebraicGeometry.Stack.twoFibreProductLiftOfEq`), and the
  isomorphism sheaf of the lifts is `Isom_𝒳(x₁, x₂)`
  (`AlgebraicGeometry.Stack.isIso_isomSpaceOverSpaceMap_snd_twoFibreProductLiftOfEq`), because
  the fibres of the algebraic stacks of `V` and `Y` are discrete;
* over the algebraic space `V` the target of the map of Stacks 0CPR (4) is `Z`
  (`AlgebraicGeometry.Stack.relativePropertyHolds_isomSpaceOverSpaceProj`).

## Main results

* `isSurjective_isFlat_isLocallyOfFinitePresentation_isomSpaceOverSpaceProj_of_isGerbeOver`, in
  the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`: **Stacks 0CPR (4)** for the
  isomorphism sheaf over the gerbe locus.

## References

* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor.Fiber

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)

attribute [local implicit_reducible] pointFiber

section TwoFibreProduct

variable {V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
  (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (u : algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
  (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- **The 1-morphism into the canonical 2-fibre product named by two 1-morphisms over the cospan
which agree on the nose.** Its components are `a` and `x` themselves, and its comparison
isomorphism is the identity transported along `a ≫ u = x ≫ f`. -/
def twoFibreProductLiftOfEq {𝒜 : AlgebraicStacks.{u, w} B S hS}
    (a : 𝒜 ⟶ algebraicSpaceStack.{u, w} B S hS V hV) (x : 𝒜 ⟶ 𝒳) (h : a ≫ u = x ≫ f) :
    𝒜 ⟶ (twoFibreProductSquareAlgebraicStacks B S hS u f).pt :=
  Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} u.hom f.hom
      { pt := 𝒜.val
        fst := a.hom
        snd := x.hom
        iso := eqToIso (congrArg Bicategory.InducedBicategory.Hom.hom h) })

/-- The lift is strictly compatible with the first projection. -/
theorem twoFibreProductLiftOfEq_fst {𝒜 : AlgebraicStacks.{u, w} B S hS}
    (a : 𝒜 ⟶ algebraicSpaceStack.{u, w} B S hS V hV) (x : 𝒜 ⟶ 𝒳) (h : a ≫ u = x ≫ f) :
    twoFibreProductLiftOfEq B S hS hV hY u f a x h ≫
      (twoFibreProductSquareAlgebraicStacks B S hS u f).fst = a :=
  rfl

/-- The lift is strictly compatible with the second projection. -/
theorem twoFibreProductLiftOfEq_snd {𝒜 : AlgebraicStacks.{u, w} B S hS}
    (a : 𝒜 ⟶ algebraicSpaceStack.{u, w} B S hS V hV) (x : 𝒜 ⟶ 𝒳) (h : a ≫ u = x ≫ f) :
    twoFibreProductLiftOfEq B S hS hV hY u f a x h ≫
      (twoFibreProductSquareAlgebraicStacks B S hS u f).snd = x :=
  rfl

variable (a : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
  (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (h₁ : a ≫ u = x₁ ≫ f) (h₂ : a ≫ u = x₂ ≫ f)

/-- **The component in the space factor of a vertical morphism between two lifts is the
identity.** It lies over the identity of the base, between two objects of a category with discrete
fibres. -/
theorem twoFibreProductLiftOfEq_fiber_hom_a {W : BigFppfOver B S hS}
    (z : Z.obj (Opposite.op W))
    (Φ : pointFiber B S hS Z hZ (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁) W z ⟶
      pointFiber B S hS Z hZ (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂) W z) :
    Φ.1.a = 𝟙 _ := by
  have : (twoFibreProductSquareAlgebraicStacks B S hS u f).pt.val.val.p.IsHomLift (𝟙 W) Φ.1 :=
    Φ.2
  have hbase : Φ.1.hbase = 𝟙 W :=
    (IsHomLift.fac' (twoFibreProductSquareAlgebraicStacks B S hS u f).pt.val.val.p (𝟙 W)
      Φ.1).trans ((Category.id_comp _).trans (Category.comp_id _))
  have ha := Φ.1.ha
  rw [hbase] at ha
  exact fibredCategory_hom_eq_of_isHomLift B S hS (𝟙 W) _ _ ha
    (IsHomLift.id (Functor.congr_obj a.hom.hom.w _))

/-- The second projection is injective on sections of the isomorphism sheaves of the lifts. -/
private theorem injective_isomSpaceOverSpaceMap_snd_twoFibreProductLiftOfEq_app
    (W : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((isomSpaceOverSpaceMap B S hS Z hZ
      (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂)).app W) := by
  rintro ⟨z, φ, hφ⟩ ⟨z', ψ, hψ⟩ hst
  obtain rfl : z = z' := congrArg Sigma.fst hst
  have hb := congrArg Subtype.val
    ((isomSection_mk_eq_iff B S hS Z hZ _ _ z
      (φ := pointFiberMap B S hS Z hZ (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
        _ _ W.unop z φ)
      (ψ := pointFiberMap B S hS Z hZ (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
        _ _ W.unop z ψ)
      (isIso_fiberHom B S hS 𝒳 _) (isIso_fiberHom B S hS 𝒳 _)).mp hst)
  refine (isomSection_mk_eq_iff B S hS Z hZ _ _ z hφ hψ).mpr
    (Subtype.ext (TwoFibreProductOver.Hom.ext' ?_ hb))
  exact (twoFibreProductLiftOfEq_fiber_hom_a B S hS Z hZ hV hY u f a x₁ x₂ h₁ h₂ z φ).trans
    (twoFibreProductLiftOfEq_fiber_hom_a B S hS Z hZ hV hY u f a x₁ x₂ h₁ h₂ z ψ).symm

/-- The second projection is surjective on sections of the isomorphism sheaves of the lifts. -/
private theorem surjective_isomSpaceOverSpaceMap_snd_twoFibreProductLiftOfEq_app
    (W : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Surjective ((isomSpaceOverSpaceMap B S hS Z hZ
      (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂)).app W) := by
  rintro ⟨z, ψ, hψ⟩
  have hψ' : 𝒳.val.val.p.IsHomLift (𝟙 W.unop) ψ.1 := ψ.2
  have hfψ : (fibredCategory B S hS Y).val.p.IsHomLift (𝟙 W.unop)
      (f.hom.hom.toFunctor.map ψ.1) :=
    Functor.isHomLift_map_of_comp_eq f.hom.hom.w (𝟙 W.unop) ψ.1
  let P₁ := (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁).hom.hom.toFunctor.obj
    (spacePoint.{u, w} B S hS Z hZ W.unop z)
  let P₂ := (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂).hom.hom.toFunctor.obj
    (spacePoint.{u, w} B S hS Z hZ W.unop z)
  have he₁ : (fibredCategory B S hS Y).val.p.IsHomLift (𝟙 W.unop)
      P₁.iso.hom := P₁.vertical
  have he₂ : (fibredCategory B S hS Y).val.p.IsHomLift (𝟙 W.unop)
      P₂.iso.hom := P₂.vertical
  let Φ : P₁ ⟶ P₂ :=
    { hbase := 𝟙 W.unop
      a := 𝟙 _
      b := ψ.1
      ha := IsHomLift.id (Functor.congr_obj a.hom.hom.w _)
      hb := ψ.2
      w := by
        have h₀ : (algebraicSpaceStack.{u, w} B S hS V hV).val.val.p.IsHomLift (𝟙 W.unop)
            (𝟙 P₁.x) := IsHomLift.id (Functor.congr_obj a.hom.hom.w _)
        have h₀' : (fibredCategory B S hS Y).val.p.IsHomLift (𝟙 W.unop)
            (u.hom.hom.toFunctor.map (𝟙 P₁.x)) :=
          Functor.isHomLift_map_of_comp_eq u.hom.hom.w (𝟙 W.unop) _
        exact fibredCategory_hom_eq_of_isHomLift B S hS (𝟙 W.unop) _ _
          (Functor.isHomLift_comp_of_isHomLift_id _ _ _ _ h₀' he₂)
          (Functor.isHomLift_comp_of_isHomLift_id _ _ _ _ he₁ hfψ) }
  have hΦ : (twoFibreProductSquareAlgebraicStacks B S hS u f).pt.val.val.p.IsHomLift
      (𝟙 W.unop) Φ :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by simp only [Category.id_comp]; rfl)
  exact ⟨⟨z, ⟨⟨Φ, hΦ⟩, isIso_fiberHom B S hS _ _⟩⟩,
    (isomSection_mk_eq_iff B S hS Z hZ
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁ ≫
        (twoFibreProductSquareAlgebraicStacks B S hS u f).snd)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂ ≫
        (twoFibreProductSquareAlgebraicStacks B S hS u f).snd) z
      (φ := pointFiberMap B S hS Z hZ (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
        _ _ W.unop z ⟨Φ, hΦ⟩) (ψ := ψ)
      (isIso_fiberHom B S hS 𝒳 _) hψ).mpr (Subtype.ext rfl)⟩

/-- **The isomorphisms between two lifts to the 2-fibre product are those between the two
points.** For two 1-morphisms `x₁, x₂ : Z ⟶ 𝒳` lifted to `V ×_Y 𝒳` along the same `a : Z ⟶ V`,
the second projection identifies `Isom_{V ×_Y 𝒳}` of the lifts with `Isom_𝒳(x₁, x₂)`: an
isomorphism of the 2-fibre product is a pair of isomorphisms of the factors compatible with the
comparison isomorphisms, the one in `V` is the identity and the compatibility holds automatically,
because the fibres of the algebraic stacks of `V` and `Y` are discrete. -/
instance isIso_isomSpaceOverSpaceMap_snd_twoFibreProductLiftOfEq :
    IsIso (isomSpaceOverSpaceMap B S hS Z hZ (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂)) := by
  have : ∀ W, IsIso ((isomSpaceOverSpaceMap B S hS Z hZ
      (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂)).app W) := fun W =>
    (isIso_iff_bijective _).mpr
      ⟨injective_isomSpaceOverSpaceMap_snd_twoFibreProductLiftOfEq_app B S hS Z hZ hV hY u f a x₁ x₂
        h₁ h₂ W,
      surjective_isomSpaceOverSpaceMap_snd_twoFibreProductLiftOfEq_app B S hS Z hZ hV hY u f a x₁ x₂
        h₁ h₂ W⟩
  exact NatIso.isIso_of_isIso_app _

/-- **A relative property of `Isom` of the lifts over the space factor transfers to
`Isom_𝒳(x₁, x₂)` over `Z`.** The second projection identifies the two isomorphism sheaves, and
over the algebraic space `V` the isomorphism sheaf of the lifts is `Z`. -/
private theorem relativePropertyHolds_isomSpaceOverSpaceProj_of_twoFibreProductLiftOfEq
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : RelativePropertyHolds B S hS P (HigherDiagonal.isomMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS u f).fst Z hZ
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂))) :
    RelativePropertyHolds B S hS P
      (algebraicSpaceStackMap.{u, w} B S hS
        (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂) hZ
        (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂)).hom :=
  relativePropertyHolds_algebraicSpaceStackMap_of_iso B S hS P
    (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ _ _) hZ _ hZ _ _
    (asIso (isomSpaceOverSpaceMap B S hS Z hZ (twoFibreProductSquareAlgebraicStacks B S hS u f).snd
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₁ h₁)
      (twoFibreProductLiftOfEq B S hS hV hY u f a x₂ h₂))).symm (Iso.refl Z)
    (by
      rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      exact (Iso.inv_comp_eq _).2 (isomSpaceOverSpaceMap_comp_proj B S hS Z hZ _ _ _).symm)
    (relativePropertyHolds_isomSpaceOverSpaceProj B S hS Z hZ hV _ _ _ P
      ((twoFibreProductLiftOfEq_fst B S hS hV hY u f a x₁ h₁).trans
        (twoFibreProductLiftOfEq_fst B S hS hV hY u f a x₂ h₂).symm) hP)

end TwoFibreProduct

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CPR (4), for the isomorphism sheaf over the gerbe locus.** Let `f : 𝒳 ⟶ Y` be a
1-morphism from an algebraic stack to an algebraic space over `S` and `V ⊆ Y` an open subspace
over which `𝒳` is a gerbe, i.e. `𝒳_V = V ×_Y 𝒳 ⟶ V` is a gerbe. Let `x₁, x₂ : Z ⟶ 𝒳` be two
1-morphisms out of an algebraic space with `x₁ ≫ f = x₂ ≫ f = g ≫ (V ⊆ Y)` for some `g : Z ⟶ V`.
Then the algebraic space `Isom_𝒳(x₁, x₂)` of Stacks 06PP is surjective, flat and locally of
finite presentation over `Z`.

Both points lift to `𝒳_V` along `g`, and `Isom_𝒳(x₁, x₂)` is the isomorphism sheaf of the lifts
there, the fibres of `V` and `Y` being discrete. Stacks 0CPR (4) makes
`Isom_{𝒳_V} ⟶ Isom_V(g, g)` surjective, flat and locally of finite presentation, and
`Isom_V(g, g)` is `Z`. -/
theorem isSurjective_isFlat_isLocallyOfFinitePresentation_isomSpaceOverSpaceProj_of_isGerbeOver
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (g : Z ⟶ V.toFunctor)
    (h₁ : x₁ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι))
    (h₂ : x₂ ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι)) :
    Space.IsSurjective B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ∧
      Space.IsFlat B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) ∧
      Space.IsLocallyOfFinitePresentation B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) := by
  have e : ∀ (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳),
      x ≫ f = algebraicSpaceStackMap.{u, w} B S hS hZ hY (g ≫ V.ι) →
      algebraicSpaceStackMap.{u, w} B S hS hZ hV.1 g ≫
        algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι = x ≫ f := fun x h =>
    (algebraicSpaceStackMap_comp.{u, w} B S hS hZ hV.1 hY g V.ι).symm.trans h.symm
  have hrel := (isomMap_isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver
    B S hS _ hG Z hZ
    (twoFibreProductLiftOfEq B S hS hV.1 hY _ f _ x₁ (e x₁ h₁))
    (twoFibreProductLiftOfEq B S hS hV.1 hY _ f _ x₂ (e x₂ h₂))).2
  have key := relativePropertyHolds_isomSpaceOverSpaceProj_of_twoFibreProductLiftOfEq
    B S hS Z hZ hV.1 hY _ f _ x₁ x₂ (e x₁ h₁) (e x₂ h₂)
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have fin : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      RelativePropertyHolds B S hS P (HigherDiagonal.isomMap B S hS _ Z hZ
        (twoFibreProductLiftOfEq B S hS hV.1 hY _ f _ x₁ (e x₁ h₁))
        (twoFibreProductLiftOfEq B S hS hV.1 hY _ f _ x₂ (e x₂ h₂))) →
      P (ObjectProperty.homMk (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) :
        (⟨_, isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩) :=
    fun P _ _ hP => (hasRelativeProperty_algebraicSpaceStackMap_iff.{u, w} B S hS
      (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂) hZ _ P).1 (key P hP)
  exact ⟨fin (Space.surjectiveMorphismProperty B S hS)
      fun U z hz G hG e' => (hrel U z hz G hG e').1,
    fin (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h))
      fun U z hz G hG e' => (hrel U z hz G hG e').2.1,
    fin (spaceProperty B S hS (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h))
      fun U z hz G hG e' => (hrel U z hz G hG e').2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
