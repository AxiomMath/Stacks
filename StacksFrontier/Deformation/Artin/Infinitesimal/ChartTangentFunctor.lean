module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartTangentMod

/-!
# The tangent functor of a chart point

With the notation of `Deformation.Artin.ChartLift.tangentToMod`, let `w : P → C` be a point of a
chart formally smooth on objects whose relation of isomorphism of lifts is the relation of the
modules `Mod` of the groupoid of the chart (as it is at a point through which a formally étale
chart of the arrows passes, `Deformation.Artin.ChartLift.rel_iff_of_chart`). Then
`M ↦ Mod (C[M] → C) w`, a `C`-module through `C → C[M]` and functorial through the maps
`C[M] → C[N]`, is a tangent functor of `ξ w` in the sense of Stacks 07Y9
(`Deformation.Artin.ChartLift.chartTangentData`). No (RS*) is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Stack.GroupoidLift AlgebraicGeometry.Space.ChartDescent
open AlgebraicGeometry.Stack.GroupoidLift.StackChart

namespace Deformation.Artin.ChartLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : Stack.schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)
  {C : SmallAlg (ringOf B S hS T') B.cutoff} (w : P.obj →ₐ[ringOf B S hS T'] C.obj)

/-- `TrivSqZeroExt.map` of the identity is the identity. -/
theorem tsze_map_id_apply {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
    (y : TrivSqZeroExt R M) : TrivSqZeroExt.map (LinearMap.id : M →ₗ[R] M) y = y := by
  ext <;> simp

/-- `TrivSqZeroExt.map` is compatible with composition of linear maps. -/
theorem tsze_map_comp_apply {R : Type u} [CommRing R] {M N K : ModuleCat.{u} R}
    (φ : M →ₗ[R] N) (χ : N →ₗ[R] K) (y : TrivSqZeroExt R M) :
    TrivSqZeroExt.map (χ ∘ₗ φ) y = TrivSqZeroExt.map χ (TrivSqZeroExt.map φ y) := by
  ext <;> simp

/-- On an element `y` with `y.fst = 0`, `TrivSqZeroExt.map (c • φ)` is multiplication by
`(c, 0)` after `TrivSqZeroExt.map φ`. -/
theorem tsze_map_smul_comp_apply {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} (c : R)
    (φ : M →ₗ[R] N) (y : TrivSqZeroExt R M) (hy : y.fst = 0) :
    TrivSqZeroExt.map (c • φ) y = TrivSqZeroExt.inl c * TrivSqZeroExt.map φ y := by
  ext
  · simp [hy]
  · simp [hy]

/-- The module `Mod (C[M] → C) w`, as a type carrying its `C`-module structure through
`C → C[M]`. -/
def ModC (M : SiteModule C.obj B) : Type u := Mod (stackGroupoid a ι) (sqzEOf C M) w

/-- `ModC a ι w M` is an additive group, as `Mod (C[M] → C) w` is. -/
instance (M : SiteModule C.obj B) : AddCommGroup (ModC a ι w M) :=
  inferInstanceAs (AddCommGroup (Mod (stackGroupoid a ι) (sqzEOf C M) w))

/-- `ModC a ι w M` is a `C[M]`-module, as `Mod (C[M] → C) w` is. -/
instance (M : SiteModule C.obj B) : Module (sqzAlgOf C M).obj (ModC a ι w M) :=
  inferInstanceAs (Module (sqzAlgOf C M).obj (Mod (stackGroupoid a ι) (sqzEOf C M) w))

/-- `ModC a ι w M` is a `C`-module through `C → C[M]`, `c ↦ (c, 0)`. -/
instance (M : SiteModule C.obj B) : Module C.obj (ModC a ι w M) :=
  Module.compHom _ (sqzInl C M.obj (card_sqz_lt M)).toRingHom

/-- The `C`-action on `ModC a ι w M` is the action of `(c, 0) ∈ C[M]`. -/
theorem ModC.smul_def {M : SiteModule C.obj B} (c : C.obj) (m : ModC a ι w M) :
    c • m = sqzInl C M.obj (card_sqz_lt M) c • m := rfl

variable {a ι w}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The map `C[M] → C[N]` of a map of site modules sends `(c, 0)` to `(c, 0)`. -/
theorem sqzHom_top_inl {M N : SiteModule C.obj B} (f : M ⟶ N) (c : C.obj) :
    (sqzHomOf f).top.hom.hom (sqzInl C M.obj (card_sqz_lt M) c) =
      sqzInl C N.obj (card_sqz_lt N) c :=
  TrivSqZeroExt.map_inl f.hom.hom c

/-- The map `Mod (C[M] → C) w → Mod (C[N] → C) w` of a map of site modules, `C`-linearly. -/
def modMapC {M N : SiteModule C.obj B} (f : M ⟶ N) : ModC a ι w M →ₗ[C.obj] ModC a ι w N where
  toFun := modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f)
  map_add' := _root_.map_add _
  map_smul' c m :=
    ((modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f)).map_smulₛₗ
      (sqzInl C M.obj (card_sqz_lt M) c) m).trans
      (congrArg (· • modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f) m)
        (sqzHom_top_inl f c))

/-- `modMapC f` is `modMap` of the map of thickenings `C[M] → C[N]` induced by `f`. -/
theorem modMapC_apply {M N : SiteModule C.obj B} (f : M ⟶ N) (m : ModC a ι w M) :
    modMapC f m = modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f) m :=
  rfl

/-- `modMapC` of the identity is the identity. -/
theorem modMapC_id (M : SiteModule C.obj B) (m : ModC a ι w M) : modMapC (𝟙 M) m = m := by
  obtain ⟨D, hD, rfl⟩ := Mod.mk_surjective (G := stackGroupoid a ι) m
  exact (modMap_mk (G := stackGroupoid a ι) (sqzHomOf (𝟙 M)) (sqzHom_bot_comp (w := w) (𝟙 M))
    D hD).trans (mkMod_congr (LinearMap.ext fun x ↦ tsze_map_id_apply (D x)) _ _)

/-- `modMapC` is compatible with composition. -/
theorem modMapC_comp {M N K : SiteModule C.obj B} (f : M ⟶ N) (g : N ⟶ K) (m : ModC a ι w M) :
    modMapC (f ≫ g) m = modMapC g (modMapC f m) :=
  (modMap_modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHomOf g) (sqzHomOf (f ≫ g))
    (fun y ↦ tsze_map_comp_apply f.hom.hom g.hom.hom y) (sqzHom_bot_comp (w := w) f)
    (sqzHom_bot_comp (w := w) g)
    (sqzHom_bot_comp (w := w) (f ≫ g)) m).symm

variable (a ι w) in
/-- **The tangent functor of a chart point**: `M ↦ Mod (C[M] → C) w`. -/
def chartFunctor : SiteModule C.obj B ⥤ ModuleCat.{u + 1} C.obj where
  obj M := ModuleCat.of C.obj (ULift.{u + 1} (ModC a ι w M))
  map f := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ modMapC f ∘ₗ
    ULift.moduleEquiv.toLinearMap)
  map_id M := by
    ext ⟨m⟩
    exact modMapC_id M m
  map_comp f g := by
    ext ⟨m⟩
    exact modMapC_comp f g m

/-- On `ULift.up m`, the map of `chartFunctor` of `f` is `ULift.up (modMapC f m)`. -/
theorem chartFunctor_map_up {M N : SiteModule C.obj B} (f : M ⟶ N) (m : ModC a ι w M) :
    (chartFunctor a ι w).map f (ULift.up m) = ULift.up (modMapC f m) := rfl

/-- The tangent functor of a chart point is additive. -/
instance : (chartFunctor a ι w).Additive where
  map_add {M N f g} := by
    ext ⟨m⟩
    exact congrArg ULift.up (modMap_sqzHom_add f g m)

/-- The tangent functor of a chart point is `C`-linear. -/
instance : (chartFunctor a ι w).Linear C.obj where
  map_smul {M N} f c := by
    ext ⟨m⟩
    change ULift.up (modMapC (c • f) m) = ULift.up (sqzInl C N.obj (card_sqz_lt N) c • modMapC f m)
    obtain ⟨D, hD, rfl⟩ := Mod.mk_surjective (G := stackGroupoid a ι) m
    refine congrArg ULift.up
      ((congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext fun x ↦ ?_))).trans
        (Submodule.Quotient.mk_smul _ _ _))
    exact tsze_map_smul_comp_apply c f.hom.hom (D x) (hD.1 x)

variable (hrel : ∀ (M : SiteModule C.obj B) {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj},
    (sqzEOf C M).q.hom.hom.comp ℓ₁ = w → (sqzEOf C M).q.hom.hom.comp ℓ₂ = w →
      (Rel (stackGroupoid a ι) (sqzEOf C M) w ℓ₁ ℓ₂ ↔ ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈
        AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) (sqzEOf C M) w))
  (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
  (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m')

/-- The identification of `Mod (C[M] → C) w` with the lift classes of `ξ w` to `C[M]`. -/
def chartModLiftEquiv (M : SiteModule C.obj B) :
    ((chartFunctor a ι w).obj M : Type (u + 1)) ≃
      squareZeroLiftClasses C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w)
        (ξ_obj a ι w) M :=
  Equiv.ulift.trans ((Equiv.ofBijective _ (bijective_modToLiftClasses (ℓ₀ w M) (ℓ₀_reduce w M)
    (hrel M) ha hι)).trans (sqzLiftClassesEquiv a ι w M).symm)

/-- `chartModLiftEquiv` sends the class of a derivation `D` to the class of the lift
`ℓ₀ + D` of `ξ w` to `C[M]`. -/
theorem chartModLiftEquiv_mk (M : SiteModule C.obj B)
    (D : P.obj →ₗ[ringOf B S hS T'] (sqzAlgOf C M).obj) (hD : D ∈ Der (sqzEOf C M) w) :
    chartModLiftEquiv hrel ha hι M
        (ULift.up (α := ModC a ι w M) (mkMod (G := stackGroupoid a ι) D hD)) =
      Quotient.mk _ (sqzLift a ι w M (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))
        (addLift_reduce D hD (ℓ₀ w M) (ℓ₀_reduce w M))) :=
  (Equiv.symm_apply_eq _).mpr (sqzLiftClassesEquiv_mk a ι w M _ _).symm

/-- `chartModLiftEquiv` is compatible with the maps induced by a map `f : M ⟶ N` of site
modules: the image of `z` under `chartFunctor.map f` is the pullback of the lift class of `z`
along `f`. -/
theorem isPullback_chartModLiftEquiv {M N : SiteModule C.obj B} (f : M ⟶ N)
    (z : ((chartFunctor a ι w).obj M : Type (u + 1))) :
    IsPullbackOfSquareZeroLift C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w)
      (ξ_obj a ι w) f (chartModLiftEquiv hrel ha hι M z)
      (chartModLiftEquiv hrel ha hι N ((chartFunctor a ι w).map f z)) := by
  obtain ⟨m⟩ := z
  obtain ⟨D, hD, rfl⟩ := Mod.mk_surjective (G := stackGroupoid a ι) m
  have hℓ' : (sqzEOf C N).q.hom.hom.comp ((sqzHomOf f).top.hom.hom.comp
      (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))) = w := by
    rw [SqZero.Hom.w_comp, addLift_reduce]; rfl
  have hmap : (chartFunctor a ι w).map f (ULift.up (α := ModC a ι w M)
      (mkMod (G := stackGroupoid a ι) D hD)) = ULift.up (α := ModC a ι w N)
      (mkMod (G := stackGroupoid a ι) _ (sub_mem_Der (ℓ₀_reduce w N) hℓ')) :=
    congrArg ULift.up (modMap_sqzHom_mk f D hD)
  have h1 := chartModLiftEquiv_mk hrel ha hι M D hD
  have h2 := chartModLiftEquiv_mk hrel ha hι N _ (sub_mem_Der (ℓ₀_reduce w N) hℓ')
  have key := isPullback_sqzLift a ι w f _ (addLift_reduce D hD (ℓ₀ w M) (ℓ₀_reduce w M)) hℓ'
  refine (congrArg₂ (IsPullbackOfSquareZeroLift C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p
    (ξ a ι w) (ξ_obj a ι w) f) h1 ((congrArg _ hmap).trans h2)).mpr ?_
  have e : ∀ {ℓ ℓ' : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C N).obj} (_ : ℓ = ℓ')
      (hℓ : (sqzEOf C N).q.hom.hom.comp ℓ = w) (hℓ'' : (sqzEOf C N).q.hom.hom.comp ℓ' = w),
      sqzLift a ι w N ℓ hℓ = sqzLift a ι w N ℓ' hℓ'' := by
    intro ℓ ℓ' h _ _
    subst h
    rfl
  rw [e (eq_addLift (ℓ₀_reduce w N) hℓ').symm _ hℓ']
  exact key

/-- **A chart point has a tangent functor** (Stacks 07Y9 without (RS*)): `M ↦ Mod (C[M] → C) w`. -/
def chartTangentData :
    TangentFunctorData C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w)
      (ξ_obj a ι w) where
  functor := chartFunctor a ι w
  liftEquiv := chartModLiftEquiv hrel ha hι
  naturality {M N} f z := by
    obtain ⟨b, hb, hb'⟩ := exists_isCanonicalLiftTransition_isPullbackOfSquareZeroLift C.obj B S
      hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w) (ξ_obj a ι w) 𝒳.property f
      (chartModLiftEquiv hrel ha hι M z)
    have hbz := isPullbackOfSquareZeroLift_unique C.obj B S hS (toSOf C) (contains_spec C)
      𝒳.val.p (ξ a ι w) (ξ_obj a ι w) 𝒳.property f hb' (isPullback_chartModLiftEquiv hrel ha hι f z)
    exact hbz ▸ hb
  liftEquiv_natural f z := isPullback_chartModLiftEquiv hrel ha hι f z

end Deformation.Artin.ChartLift

end
