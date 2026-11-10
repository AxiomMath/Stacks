module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedOverBase
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# `S-𝒫olarized` is limit preserving

The fibres of `S-𝒫olarized` over the big fppf site of `S` are the fibres of `𝒫olarized` over the
big fppf site of a terminal base, read through the functor forgetting the morphisms to `S`; a
morphism of `S-𝒫olarized` lies over a morphism of the site of `S` exactly when it lies over its
underlying morphism of schemes. The three colimit-free descent conditions characterising limit
preservation (`Deformation.Artin.DescentObj`, `Deformation.Artin.DescentHom`,
`Deformation.Artin.DescentEq`) therefore pass from `𝒫olarized` to `S-𝒫olarized`, and Stacks 0D43
(`AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`) gives limit preservation of
`S-𝒫olarized`.

## Main results

* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.descentObj_of_slice`,
  `AlgebraicGeometry.PolarizedVersality.PolarizedOver.descentHom_of_slice`,
  `AlgebraicGeometry.PolarizedVersality.PolarizedOver.descentEq_of_slice`.
* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.isLimitPreserving_stack`.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

namespace AlgebraicGeometry.PolarizedVersality.PolarizedOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : Scheme.{u}}
  {hT' : B.Contains T} (hT : IsTerminal (B.obj hT'))

/-- An object of the big fppf site of `S`, read over the terminal base. -/
abbrev toTerminal : BigFppfOver B S hS ⥤ BigFppfOver B T hT' :=
  Over.forget (B.obj hS) ⋙ (Over.equivalenceOfIsTerminal hT).inverse

/-- The polarized family of an object of `S-𝒫olarized` over `V` lies over `V` read over the
terminal base. -/
theorem polarizedSliceProjection_obj_eq {x : Family B S hS} {V : BigFppfOver B S hS}
    (hx : (projection B S hS).obj x = V) :
    (polarizedSliceProjection B hT' hT).obj x.polarized = (toTerminal hT).obj V :=
  (polarizedProjection B).sliceAtTerminal_obj_eq hT (congrArg Comma.left hx)

/-- A morphism of polarized families between objects of `S-𝒫olarized` lying over `V` and `W`
lies over a morphism between `V` and `W` read over the terminal base as soon as it lies over its
underlying morphism of schemes. -/
theorem isHomLift_slice {V W : BigFppfOver B S hS}
    (g : (toTerminal hT).obj V ⟶ (toTerminal hT).obj W) {x y : Family B S hS}
    (φ : x.polarized ⟶ y.polarized) (hx : (projection B S hS).obj x = V)
    (hy : (projection B S hS).obj y = W) (h : (polarizedProjection B).IsHomLift g.left φ) :
    (polarizedSliceProjection B hT' hT).IsHomLift g φ :=
  isHomLift_sliceAtTerminal_of_left (polarizedProjection B) hT g φ
    (polarizedSliceProjection_obj_eq hT hx) (polarizedSliceProjection_obj_eq hT hy) h

/-- The object of `S-𝒫olarized` over `V` given by an object of `𝒫olarized` over `V` read over the
terminal base. -/
def liftFiber {V : BigFppfOver B S hS}
    (x : (polarizedSliceProjection B hT' hT).Fiber ((toTerminal hT).obj V)) :
    (projection B S hS).Fiber V :=
  ⟨ofBase x.1 V (congrArg Comma.left x.2), projection_obj_ofBase _ _ _⟩

/-- The object of `𝒫olarized` over the terminal base underlying an object of `S-𝒫olarized`. -/
def toSliceFiber {V : BigFppfOver B S hS} (x : (projection B S hS).Fiber V) :
    (polarizedSliceProjection B hT' hT).Fiber ((toTerminal hT).obj V) :=
  ⟨x.1.polarized, polarizedSliceProjection_obj_eq hT x.2⟩

/-- The morphism of `S-𝒫olarized` given by a morphism of polarized families lying over the
underlying morphism of a morphism of the site of `S`. -/
def liftHom {x y : Family B S hS} {V W : BigFppfOver B S hS}
    (hx : (projection B S hS).obj x = V) (hy : (projection B S hS).obj y = W) (f : V ⟶ W)
    (φ : x.polarized ⟶ y.polarized) (h : (polarizedProjection B).IsHomLift f.left φ) : x ⟶ y :=
  homMk φ (by
    rw [toBase_eq hy, toBase_eq hx]
    exact comp_eqToHom_hom_eq f φ.baseMap _ _ (IsHomLift.fac' (polarizedProjection B) f.left φ))

/-- The morphism `liftHom hx hy f φ h` of `S-𝒫olarized` lies over `f`. -/
theorem isHomLift_liftHom {x y : Family B S hS} {V W : BigFppfOver B S hS}
    (hx : (projection B S hS).obj x = V) (hy : (projection B S hS).obj y = W) (f : V ⟶ W)
    (φ : x.polarized ⟶ y.polarized) (h : (polarizedProjection B).IsHomLift f.left φ) :
    (projection B S hS).IsHomLift f (liftHom hx hy f φ h) :=
  isHomLift_projection f _ hx hy h

variable {I : Type*} [Category I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)

/-- Descent of objects passes from `𝒫olarized` to `S-𝒫olarized`. -/
theorem descentObj_of_slice
    (h : DescentObj (polarizedSliceProjection B hT' hT) (D ⋙ toTerminal hT)
      ((toTerminal hT).mapCone c)) :
    DescentObj (projection B S hS) D c := by
  intro x
  obtain ⟨i, xi, δ, hδ⟩ := h (toSliceFiber hT x)
  let xi' := liftFiber hT (V := D.obj i) xi
  exact ⟨i, xi', liftHom x.2 xi'.2 (c.π.app i) δ
      (isHomLift_left_of_sliceAtTerminal _ hT _ δ hδ),
    isHomLift_liftHom _ _ _ _ _⟩

/-- Descent of vertical morphisms passes from `𝒫olarized` to `S-𝒫olarized`. -/
theorem descentHom_of_slice
    (h : DescentHom (polarizedSliceProjection B hT' hT) (D ⋙ toTerminal hT)
      ((toTerminal hT).mapCone c)) :
    DescentHom (projection B S hS) D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  obtain ⟨k, s, xk, yk, dx, dy, δk, ψ, h1, h2, h3, h4, e1, e2⟩ :=
    h i (toSliceFiber hT xi) (toSliceFiber hT yi) (toSliceFiber hT x) (toSliceFiber hT y)
      δ.polarizedHom ε.polarizedHom
      (isHomLift_slice hT _ _ x.2 xi.2 (isHomLift_polarizedProjection (c.π.app i) δ hδ))
      (isHomLift_slice hT _ _ y.2 yi.2 (isHomLift_polarizedProjection (c.π.app i) ε hε))
      φ.polarizedHom
      (isHomLift_slice hT (𝟙 _) _ x.2 y.2 (isHomLift_polarizedProjection (𝟙 c.pt) φ hφ))
  let xk' := liftFiber hT (V := D.obj k) xk
  let yk' := liftFiber hT (V := D.obj k) yk
  refine ⟨k, s, xk', yk',
    liftHom xk'.2 xi.2 (D.map s) dx (isHomLift_left_of_sliceAtTerminal _ hT _ dx h1),
    liftHom yk'.2 yi.2 (D.map s) dy (isHomLift_left_of_sliceAtTerminal _ hT _ dy h2),
    liftHom x.2 xk'.2 (c.π.app k) δk (isHomLift_left_of_sliceAtTerminal _ hT _ δk h3),
    liftHom xk'.2 yk'.2 (𝟙 (D.obj k)) ψ (isHomLift_left_of_sliceAtTerminal _ hT _ ψ h4),
    isHomLift_liftHom _ _ _ _ _, isHomLift_liftHom _ _ _ _ _, isHomLift_liftHom _ _ _ _ _,
    isHomLift_liftHom _ _ _ _ _, PolarizedFamilyOver.Hom.ext e1, PolarizedFamilyOver.Hom.ext e2⟩

/-- Descent of equalities of vertical morphisms passes from `𝒫olarized` to `S-𝒫olarized`. -/
theorem descentEq_of_slice
    (h : DescentEq (polarizedSliceProjection B hT' hT) (D ⋙ toTerminal hT)
      ((toTerminal hT).mapCone c)) :
    DescentEq (projection B S hS) D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  obtain ⟨k, s, xk, dx, h1, e⟩ :=
    h i (toSliceFiber hT xi) (toSliceFiber hT yi) (toSliceFiber hT x) δ.polarizedHom
      (isHomLift_slice hT _ _ x.2 xi.2 (isHomLift_polarizedProjection (c.π.app i) δ hδ))
      ψ.polarizedHom ψ'.polarizedHom
      (isHomLift_slice hT (𝟙 _) _ xi.2 yi.2 (isHomLift_polarizedProjection (𝟙 _) ψ hψ))
      (isHomLift_slice hT (𝟙 _) _ xi.2 yi.2 (isHomLift_polarizedProjection (𝟙 _) ψ' hψ'))
      (congrArg PolarizedFamilyOver.Hom.polarizedHom hδψ)
  let xk' := liftFiber hT (V := D.obj k) xk
  exact ⟨k, s, xk',
    liftHom xk'.2 xi.2 (D.map s) dx (isHomLift_left_of_sliceAtTerminal _ hT _ dx h1),
    isHomLift_liftHom _ _ _ _ _, PolarizedFamilyOver.Hom.ext e⟩

variable (B S hS) in
/-- **`S-𝒫olarized` is limit preserving** (Stacks 07XL), by Stacks 0D43. -/
theorem isLimitPreserving_stack :
    IsLimitPreserving.{u, u, u, u + 1, u} B S hS (stack B S hS) := by
  intro I _ _ D c hc
  have hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))) := by
    change (Spec (CommRingCat.of (ULift.{u} ℤ))).size < B.cutoff
    rw [Scheme.size_Spec]
    simpa using B.aleph0_lt_cutoff
  let hT := isTerminal_obj_specULiftZ B hZ
  let Φa : BigAffineFppf B S hS ⥤ BigAffineFppf B _ hZ :=
    ObjectProperty.lift _ (BigAffineFppf.inclusion B S hS ⋙ toTerminal hT) (fun V => V.property)
  have hc' : IsLimit ((BigAffineFppf.toScheme B _ hZ).mapCone (Φa.mapCone c)) := hc
  let : (polarizedSliceProjection B hZ hT).IsFibered :=
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
  have hp : (polarizedSliceProjection B hZ hT).IsFiberedInGroupoids :=
    polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT
  have h0 : (colimitComparison (polarizedSliceProjection B hZ hT)
      ((D ⋙ BigAffineFppf.inclusion B S hS) ⋙ toTerminal hT)
      ((toTerminal hT).mapCone ((BigAffineFppf.inclusion B S hS).mapCone c))).IsEquivalence :=
    isLimitPreservingPolarizedUnconditional B hZ hT I (D ⋙ Φa) (Φa.mapCone c) hc'
  have hO := descentObj_of_essSurj (p := polarizedSliceProjection B hZ hT)
    (D := (D ⋙ BigAffineFppf.inclusion B S hS) ⋙ toTerminal hT)
    (c := (toTerminal hT).mapCone ((BigAffineFppf.inclusion B S hS).mapCone c))
  have hH := descentHom_of_full (p := polarizedSliceProjection B hZ hT) hp
    (D := (D ⋙ BigAffineFppf.inclusion B S hS) ⋙ toTerminal hT)
    (c := (toTerminal hT).mapCone ((BigAffineFppf.inclusion B S hS).mapCone c))
  have hE := descentEq_of_faithful (p := polarizedSliceProjection B hZ hT) hp
    (D := (D ⋙ BigAffineFppf.inclusion B S hS) ⋙ toTerminal hT)
    (c := (toTerminal hT).mapCone ((BigAffineFppf.inclusion B S hS).mapCone c))
  have hpS := isFiberedInGroupoids_projection B S hS
  exact
    { faithful := faithful_of_descentEq (projection B S hS) hpS _ _ (descentEq_of_slice hT _ _ hE)
      full := full_of_descentHom (projection B S hS) hpS _ _ (descentHom_of_slice hT _ _ hH)
      essSurj := essSurj_of_descentObj (projection B S hS) hpS _ _
        (descentObj_of_slice hT _ _ hO) }

end AlgebraicGeometry.PolarizedVersality.PolarizedOver

end
