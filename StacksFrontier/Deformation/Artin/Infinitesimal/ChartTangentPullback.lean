module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartTangentMod
public import StacksFrontier.Deformation.Artin.Obstruction.TangentPullback

/-!
# The map of Stacks 07YA at chart points

With the notation of `Deformation.Artin.ChartLift.tangentToMod`, let `g : X → Y` be a map of
small `A'`-algebras and `ψ : M → N` a `g`-semilinear map of coefficients. The point `ξ (g ∘ w)`
over `Spec Y` is the pullback of `ξ w` along the cartesian arrow `ξ (g ∘ w) ⟶ ξ w`. Under the
identifications of the tangent modules with the modules of the groupoid of the chart, the map
`T_{ξ w}(M) → T_{ξ (g ∘ w)}(N)` of Stacks 07YA is the map `Mod w → Mod (g ∘ w)` induced by the
map of thickenings `X[M] → Y[N]` (`Deformation.Artin.ChartLift.tangentToMod_tangentPullbackFun`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Stack.GroupoidLift AlgebraicGeometry.Space.ChartDescent
open AlgebraicGeometry.Stack.GroupoidLift.StackChart

namespace Deformation.Artin.ChartLift

universe u

section BaseHom

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}

/-- The map `X[M] → Y[N]` of a map of algebras and a semilinear map of coefficients, as a map
of small `A'`-algebras. -/
def sqzBaseMap {X Y : SmallAlg A' κ} (g : X ⟶ Y) {M : ModuleCat.{u} X.obj} {N : ModuleCat.{u} Y.obj}
    (ψ : M ⟶ (ModuleCat.restrictScalars (g.hom.hom : X.obj →+* Y.obj)).obj N)
    (hM : Cardinal.mk (TrivSqZeroExt X.obj M) < κ) (hN : Cardinal.mk (TrivSqZeroExt Y.obj N) < κ) :
    sqzAlg X M hM ⟶ sqzAlg Y N hN :=
  SmallAlg.homMk
    { squareZeroRingBaseMap (g.hom.hom : X.obj →+* Y.obj)
        (restrictScalarsAddHom (g.hom.hom : X.obj →+* Y.obj) ψ)
        (restrictScalarsAddHom_smul (g.hom.hom : X.obj →+* Y.obj) ψ) with
      commutes' := fun a ↦ TrivSqZeroExt.ext (g.hom.hom.commutes a) ψ.hom.map_zero }

/-- The map of thickenings `X[M] → Y[N]` over `g`. -/
def sqzBaseHom {X Y : SmallAlg A' κ} (g : X ⟶ Y) {M : ModuleCat.{u} X.obj}
    {N : ModuleCat.{u} Y.obj}
    (ψ : M ⟶ (ModuleCat.restrictScalars (g.hom.hom : X.obj →+* Y.obj)).obj N)
    (hM : Cardinal.mk (TrivSqZeroExt X.obj M) < κ) (hN : Cardinal.mk (TrivSqZeroExt Y.obj N) < κ) :
    SqZero.Hom (sqzE X M hM) (sqzE Y N hN) where
  top := sqzBaseMap g ψ hM hN
  bot := g
  w := by
    ext z
    rfl

/-- The map `X[M] → Y[N]` sends `(c, 0) + y` to `(g c, 0) + (g, ψ)(y)`. -/
theorem sqzBaseMap_inl_add {X Y : SmallAlg A' κ} (g : X ⟶ Y) {M : ModuleCat.{u} X.obj}
    {N : ModuleCat.{u} Y.obj}
    (ψ : M ⟶ (ModuleCat.restrictScalars (g.hom.hom : X.obj →+* Y.obj)).obj N)
    (hM : Cardinal.mk (TrivSqZeroExt X.obj M) < κ) (hN : Cardinal.mk (TrivSqZeroExt Y.obj N) < κ)
    (c : X.obj) (y : (sqzAlg X M hM).obj) :
    (sqzBaseMap g ψ hM hN).hom.hom (sqzInl X M hM c + y) =
      sqzInl Y N hN (g.hom.hom c) + (sqzBaseMap g ψ hM hN).hom.hom y := by
  rw [_root_.map_add]
  congr 1
  exact TrivSqZeroExt.ext rfl ψ.hom.map_zero

end BaseHom

section Pullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : Stack.schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
  {X Y : SmallAlg (ringOf B S hS T') B.cutoff} {w : P.obj →ₐ[ringOf B S hS T'] X.obj}

variable (a ι) in
/-- The lift of `ξ w` of a lift `ℓ` and the cartesian arrows of a square of thickenings. -/
theorem liftArrow_trans_square {X' Y' : SmallAlg (ringOf B S hS T') B.cutoff} {eX : SqZero X' X}
    {eY : SqZero Y' Y} (g : X ⟶ Y) (top : X' ⟶ Y') (hw : top ≫ eY.q = eX.q ≫ g)
    (ℓ : P.obj →ₐ[ringOf B S hS T'] X'.obj) (hℓ : eX.q.hom.hom.comp ℓ = w)
    (hℓ' : eY.q.hom.hom.comp (top.hom.hom.comp ℓ) = g.hom.hom.comp w) :
    liftArrow (a := a) (ι := ι) (e := eY) (top.hom.hom.comp ℓ) hℓ' ≫ trans a ι top ℓ =
      trans a ι g w ≫ liftArrow (a := a) (ι := ι) (e := eX) ℓ hℓ := by
  subst hℓ
  simp only [liftArrow, Category.assoc, eqToHom_refl, Category.id_comp]
  rw [← trans_comp, ← trans_comp, trans_congr a ι hw]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (eqToHom_trans _ _)).trans
    (Category.id_comp _))

variable (g : X ⟶ Y)

/-- The structure morphism `Spec Y → S` factors through `Spec g : Spec Y → Spec X`. -/
theorem toSOf_comp : Spec.map (CommRingCat.ofHom (g.hom.hom : X.obj →+* Y.obj)) ≫ toSOf X =
    toSOf Y := by
  rw [toSOf, toSOf, ← Category.assoc, specMap_comp_specToBase]

/-- The map `Spec Y → Spec X` of algebras over `S` induced by `g` is `specOverMap g`. -/
theorem algebraOverMapOfRingHom_eq :
    algebraOverMapOfRingHom (g.hom.hom : X.obj →+* Y.obj) B S hS (toSOf X) (toSOf Y)
      (contains_spec X) (contains_spec Y) (toSOf_comp g) = specOverMap g := rfl

variable {M : SiteModule X.obj B} {N : SiteModule Y.obj B}
  (ψ : M.obj ⟶ (ModuleCat.restrictScalars (g.hom.hom : X.obj →+* Y.obj)).obj N.obj)

/-- The map of thickenings `X[M] → Y[N]` for site modules. -/
abbrev sqzBaseHomOf : SqZero.Hom (sqzEOf X M) (sqzEOf Y N) :=
  sqzBaseHom g ψ (card_sqz_lt M) (card_sqz_lt N)

/-- The map `Spec Y[N] → Spec X[M]` of the tangent pullback is, up to the identifications
`squareZeroOver_eq_specOver`, the map `specOverMap` of `X[M] → Y[N]`. -/
theorem tangentPullbackBase_heq :
    HEq (tangentPullbackBase (hS := hS) (g.hom.hom : X.obj →+* Y.obj) (toSOf_comp g) ψ)
      (specOverMap (sqzBaseHomOf g ψ).top) := by
  have h₁ : ((BigFppfOver.toScheme B S hS).map
      (tangentPullbackBase (hS := hS) (g.hom.hom : X.obj →+* Y.obj) (toSOf_comp g) ψ) :
        Spec (squareZeroRing Y.obj N.obj) ⟶ Spec (squareZeroRing X.obj M.obj)) =
      Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap (g.hom.hom : X.obj →+* Y.obj)
        (restrictScalarsAddHom (g.hom.hom : X.obj →+* Y.obj) ψ)
        (restrictScalarsAddHom_smul (g.hom.hom : X.obj →+* Y.obj) ψ))) := rfl
  have h₂ : Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap (g.hom.hom : X.obj →+* Y.obj)
        (restrictScalarsAddHom (g.hom.hom : X.obj →+* Y.obj) ψ)
        (restrictScalarsAddHom_smul (g.hom.hom : X.obj →+* Y.obj) ψ))) =
      ((BigFppfOver.toScheme B S hS).map (specOverMap (sqzBaseHomOf g ψ).top) :
        Spec (squareZeroRing Y.obj N.obj) ⟶ Spec (squareZeroRing X.obj M.obj)) := rfl
  exact hom_heq_of_toScheme (squareZeroOver_eq_specOver Y N) (squareZeroOver_eq_specOver X M)
    ((heq_of_eq h₁).trans (heq_of_eq h₂))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The map of thickenings `X[M] → Y[N]` is `g` on the bases. -/
theorem sqzBaseHom_bot_comp : (sqzBaseHomOf g ψ).bot.hom.hom.comp w = g.hom.hom.comp w := rfl

variable (hrel : ∀ (M : SiteModule X.obj B) {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf X M).obj},
    (sqzEOf X M).q.hom.hom.comp ℓ₁ = w → (sqzEOf X M).q.hom.hom.comp ℓ₂ = w →
      (Rel (stackGroupoid a ι) (sqzEOf X M) w ℓ₁ ℓ₂ ↔ ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈
        AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) (sqzEOf X M) w))
  (hrel' : ∀ (N : SiteModule Y.obj B) {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf Y N).obj},
    (sqzEOf Y N).q.hom.hom.comp ℓ₁ = g.hom.hom.comp w →
      (sqzEOf Y N).q.hom.hom.comp ℓ₂ = g.hom.hom.comp w →
      (Rel (stackGroupoid a ι) (sqzEOf Y N) (g.hom.hom.comp w) ℓ₁ ℓ₂ ↔
        ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈
          AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) (sqzEOf Y N)
            (g.hom.hom.comp w)))
  (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
  (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m')
  (F : TangentFunctorData X.obj B S hS (toSOf X) (contains_spec X) 𝒳.val.p (ξ a ι w)
    (ξ_obj a ι w))
  (G : TangentFunctorData Y.obj B S hS (toSOf Y) (contains_spec Y) 𝒳.val.p
    (ξ a ι (g.hom.hom.comp w)) (ξ_obj a ι (g.hom.hom.comp w)))

/-- `modMap` of `X[M] → Y[N]` on the class of a derivation `D`: the class of
`(g, ψ) ∘ (ℓ₀ + D) - ℓ₀`. -/
theorem modMap_sqzBaseHom_mk (D : P.obj →ₗ[ringOf B S hS T'] (sqzAlgOf X M).obj)
    (hD : D ∈ Der (sqzEOf X M) w) :
    modMap (G := stackGroupoid a ι) (sqzBaseHomOf g ψ) (sqzBaseHom_bot_comp g ψ) (mkMod D hD) =
      mkMod (((sqzBaseHomOf g ψ).top.hom.hom.comp
          (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))).toLinearMap -
        (ℓ₀ (g.hom.hom.comp w) N).toLinearMap) (sub_mem_Der (ℓ₀_reduce (g.hom.hom.comp w) N)
          (by rw [SqZero.Hom.w_comp, addLift_reduce]; rfl)) := by
  rw [modMap_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext fun x ↦ ?_))
  simp only [postcomp_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    addLift_apply]
  exact Eq.symm ((congrArg (· - (sqzInl Y N.obj (card_sqz_lt N)) (g.hom.hom (w x)))
    (sqzBaseMap_inl_add g ψ (card_sqz_lt M) (card_sqz_lt N) (w x) (D x))).trans
      (add_sub_cancel_left _ _))

include hrel hrel' ha hι in
/-- **The map of Stacks 07YA at chart points is the map of the modules of the groupoid** induced
by the map of thickenings `X[M] → Y[N]`. -/
theorem tangentToMod_tangentPullbackFun (z : (F.functor.obj M : Type _)) :
    tangentToMod N hrel' ha hι G (tangentPullbackFun (g.hom.hom : X.obj →+* Y.obj)
        (toSOf_comp g) 𝒳.property (trans a ι g w) (trans_isHomLift a ι g w) F G ψ z) =
      modMap (G := stackGroupoid a ι) (sqzBaseHomOf g ψ) (sqzBaseHom_bot_comp g ψ)
        (tangentToMod M hrel ha hι F z) := by
  suffices key : ∀ m, tangentToMod M hrel ha hι F z = m →
      tangentToMod N hrel' ha hι G (tangentPullbackFun (g.hom.hom : X.obj →+* Y.obj)
        (toSOf_comp g) 𝒳.property (trans a ι g w) (trans_isHomLift a ι g w) F G ψ z) =
      modMap (G := stackGroupoid a ι) (sqzBaseHomOf g ψ) (sqzBaseHom_bot_comp g ψ) m from
    key _ rfl
  intro m hm
  induction m using Submodule.Quotient.induction_on with
  | H D' =>
  obtain ⟨D, hD⟩ := D'
  have hL := liftEquiv_eq_of_tangentToMod M hrel ha hι F hD hm
  have hℓ' : (sqzEOf Y N).q.hom.hom.comp ((sqzBaseHomOf g ψ).top.hom.hom.comp
      (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))) = g.hom.hom.comp w := by
    rw [SqZero.Hom.w_comp, addLift_reduce]; rfl
  have hu : G.liftEquiv N (tangentPullbackFun (g.hom.hom : X.obj →+* Y.obj)
      (toSOf_comp g) 𝒳.property (trans a ι g w) (trans_isHomLift a ι g w) F G ψ z) =
      Quotient.mk _ (sqzLift a ι (g.hom.hom.comp w) N _ hℓ') := by
    refine (liftEquiv_tangentPullbackFun _ _ _ _ _ F G ψ z).trans ?_
    rw [hL]
    exact (eq_underFiberClassPullback_of_cartesian _ _ _ _ _ _ _ _ rfl rfl
      (trans a ι (sqzBaseHomOf g ψ).top (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M)))
      (isStronglyCartesian_of_heq 𝒳.val.p (squareZeroOver_eq_specOver Y N).symm
        (squareZeroOver_eq_specOver X M).symm (tangentPullbackBase_heq g ψ).symm
        (trans_isStronglyCartesian a ι _ _))
      (liftArrow_trans_square a ι g _ (sqzBaseHomOf g ψ).w _
        (addLift_reduce D hD (ℓ₀ w M) (ℓ₀_reduce w M)) hℓ')).symm
  exact (tangentToMod_of_liftEquiv N hrel' ha hι G hℓ' hu).trans
    (modMap_sqzBaseHom_mk g ψ D hD).symm

end Pullback

end Deformation.Artin.ChartLift

end
