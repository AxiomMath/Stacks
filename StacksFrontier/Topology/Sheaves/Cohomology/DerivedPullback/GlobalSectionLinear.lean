module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands

/-!
# The derived pullback is linear over the global sections of the target

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and put `A = Γ(Y, 𝒪_Y)`.
Multiplication by a global section makes sheaves of `𝒪_Y`-modules an `A`-linear category, and
multiplication by the image `f^♯(a) ∈ Γ(X, 𝒪_X)` makes sheaves of `𝒪_X`-modules an `A`-linear
category as well. For these structures the pushforward `f_*`, the pullback `f^*` and the
unbounded derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` are `A`-linear functors: a global section
`a` of `𝒪_Y` acts on `Lf^* K` as the derived pullback of multiplication by `a` on `K`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackLinear.linearTop`: the `A`-linear structure on sheaves of
  modules on a ringed space given by a ring map `A →+* Γ(Z, 𝒪_Z)`.
* `AlgebraicGeometry.Scheme.linearOXMod`, `AlgebraicGeometry.Scheme.linearStructureSheafRing`,
  `AlgebraicGeometry.Scheme.Hom.linearStructureSheafModules` and
  `AlgebraicGeometry.Scheme.Hom.linearStructureSheafRing`: the `Γ(X, ⊤)`-linear structures on
  `𝒪_X`-modules and, through `g^♯`, on `𝒪_Y`-modules for `g : Y ⟶ X`, in each of the spellings
  of these categories that the derived pullback and the derived internal hom are stated in.

## Main results

* `Stacks.Cohomology.DerivedPullbackLinear.modulePushforward_linear` and
  `Stacks.Cohomology.DerivedPullbackLinear.modulePullback_linear`: `f_*` and `f^*` are
  `Γ(Y, 𝒪_Y)`-linear.
* `Stacks.Cohomology.DerivedPullbackLinear.derivedPullback_linear`: `Lf^*` is
  `Γ(Y, 𝒪_Y)`-linear.
* `AlgebraicGeometry.Scheme.Hom.derivedPullback_map_smul_id` and
  `AlgebraicGeometry.Scheme.Hom.derivedPullback_map_smul`: for a morphism of schemes
  `g : Y ⟶ X` and `a ∈ Γ(X, ⊤)`, `Lg^*(a • 𝟙_K) = a • 𝟙_{Lg^* K}` and `Lg^*(a • φ) = a • Lg^* φ`,
  where `a` acts on `D(𝒪_Y)` through `g^♯ : Γ(X, ⊤) ⟶ Γ(Y, ⊤)`.

## Implementation notes

The pushforward is linear on sections: on `f_* N (V) = N(f⁻¹ V)` the action of `a|_V` is that
of `f^♯(a|_V) = f^♯(a)|_{f⁻¹ V}`. The pullback is its left adjoint, and a left adjoint of a
linear functor is linear because the adjunction bijection carries `a • -` to `a • -`. The
derived pullback is the total left derived functor of degreewise pullback; two natural
transformations into a left derived functor agree once they agree after composing with its
counit, and on the homotopy category both `Lf^*(a • 𝟙)` and `a • 𝟙` become multiplication by `a`
on the degreewise pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DerivedPullbackLinear

/-- The rings of sections of the structure sheaf of a ringed space are commutative, in the
unbundled form multiplication by a global section asks for. -/
instance isMulCommutative_structureSheafRing (Z : RingedSpace.{u, u})
    (U : (Opens Z.carrier)ᵒᵖ) : IsMulCommutative ((structureSheafRing Z).obj.obj U) :=
  inferInstanceAs (IsMulCommutative (Z.presheaf.obj U))

/-- **Sheaves of modules on a ringed space as an `A`-linear category**, for a ring map
`φ : A →+* Γ(Z, 𝒪_Z)`: a scalar acts by multiplication by its image. -/
@[instance_reducible]
def linearTop (Z : RingedSpace.{u, u}) (A : Type u) [Ring A]
    (φ : A →+* Z.presheaf.obj (op ⊤)) :
    Linear A (SheafOfModules.{u} (structureSheafRing Z)) :=
  Stacks.SheafOfModules.linearOfTerminalSection (structureSheafRing Z) A ⊤ isTerminalTop φ

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The ring map `f^♯ : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` on global sections. -/
abbrev globalSectionsMap : Y.presheaf.obj (op ⊤) →+* X.presheaf.obj (op ⊤) :=
  (f.hom.c.app (op ⊤)).hom

/-- **The pushforward carries multiplication by `f^♯(a)` to multiplication by `a`**: on sections
over `V` both act on `N(f⁻¹ V)` by `f^♯(a)|_{f⁻¹ V} = f^♯(a|_V)`. -/
theorem modulePushforward_map_smul (a : Y.presheaf.obj (op ⊤))
    {M N : SheafOfModules.{u} (structureSheafRing X)} (ψ : M ⟶ N) :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (modulePushforward f).map (a • ψ) = a • (modulePushforward f).map ψ := by
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  ext U x
  have h₁ := Stacks.SheafOfModules.smul_val_app (structureSheafRing X) _ ⊤ isTerminalTop
    (globalSectionsMap f) a ψ (op ((Opens.map f.hom.base).obj U.unop)) x
  have h₂ := Stacks.SheafOfModules.smul_val_app (structureSheafRing Y) _ ⊤ isTerminalTop
    (RingHom.id _) a ((modulePushforward f).map ψ) U x
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  change _ = (f.hom.c.app U).hom (Y.presheaf.map (isTerminalTop.from U.unop).op a) •
    ψ.val.app (op ((Opens.map f.hom.base).obj U.unop)) x
  congr 1
  have h := congrArg (fun φ : Y.presheaf.obj (op ⊤) ⟶ X.presheaf.obj
      (op ((Opens.map f.hom.base).obj U.unop)) => φ.hom a)
    (f.hom.c.naturality (isTerminalTop.from U.unop).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

/-- **The pushforward is linear over the global sections of the target.** -/
theorem modulePushforward_linear :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (modulePushforward f).Linear (Y.presheaf.obj (op ⊤)) :=
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  ⟨fun ψ a => modulePushforward_map_smul f a ψ⟩

/-- **The pullback carries multiplication by `a` to multiplication by `f^♯(a)`.** Its transpose
under `f^* ⊣ f_*` is computed by the unit, which commutes with scalars, and by `f_*`, which is
linear. -/
theorem modulePullback_map_smul (a : Y.presheaf.obj (op ⊤))
    {M N : SheafOfModules.{u} (structureSheafRing Y)} (ψ : M ⟶ N) :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (modulePullback f).map (a • ψ) = a • (modulePullback f).map ψ := by
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  let adj := modulePullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality ψ
  have hn' := adj.unit.naturality (a • ψ)
  simp only [Functor.id_map, Functor.comp_map] at hn hn'
  calc adj.unit.app M ≫ (modulePushforward f).map ((modulePullback f).map (a • ψ))
      = (a • ψ) ≫ adj.unit.app N := hn'.symm
    _ = a • (ψ ≫ adj.unit.app N) := Linear.smul_comp _ _ _ _ _ _
    _ = a • (adj.unit.app M ≫ (modulePushforward f).map ((modulePullback f).map ψ)) := by
        rw [hn]
    _ = adj.unit.app M ≫ (a • (modulePushforward f).map ((modulePullback f).map ψ)) := by
        rw [Linear.comp_smul]
    _ = adj.unit.app M ≫ (modulePushforward f).map (a • (modulePullback f).map ψ) := by
        rw [modulePushforward_map_smul]

/-- **The pullback is linear over the global sections of the target.** -/
theorem modulePullback_linear :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (modulePullback f).Linear (Y.presheaf.obj (op ⊤)) :=
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  ⟨fun ψ a => modulePullback_map_smul f a ψ⟩

/-- A linear functor carries `a • 𝟙 M` to `a • 𝟙 (F M)`. -/
private theorem map_smul_id {R : Type*} [Semiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : C ⥤ D) [F.Additive]
    [F.Linear R] (a : R) (M : C) : F.map (a • 𝟙 M) = a • 𝟙 (F.obj M) :=
  (F.map_smul _ _).trans (congrArg (a • ·) (F.map_id M))

variable [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (structureSheafRing Y))]

open DerivedAdjunctionOnRingedSpaces in
/-- **The derived pullback carries multiplication by `a` to multiplication by `f^♯(a)`.** -/
theorem derivedPullback_map_smul_id (a : Y.presheaf.obj (op ⊤))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (derivedPullback f).map (a • 𝟙 K) = a • 𝟙 ((derivedPullback f).obj K) := by
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  have := modulePullback_linear f
  let γ₁ : derivedPullback f ⟶ derivedPullback f :=
    { app := fun K => (derivedPullback f).map (a • 𝟙 K)
      naturality := fun K L φ => by
        simp only [← Functor.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
          Category.comp_id] }
  let γ₂ : derivedPullback f ⟶ derivedPullback f :=
    { app := fun K => a • 𝟙 ((derivedPullback f).obj K)
      naturality := fun K L φ => by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id] }
  have h : γ₁ = γ₂ := by
    refine Functor.leftDerived_ext (derivedPullback f) (derivedPullbackComparison f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) _ γ₁ γ₂ ?_
    ext M
    have hQ := map_smul_id DerivedCategory.Qh a M
    have hH := map_smul_id ((modulePullback f).mapHomotopyCategory (.up ℤ)) a M
    have hF : (pullbackOnHomotopy f).map (a • 𝟙 M) = a • 𝟙 ((pullbackOnHomotopy f).obj M) := by
      change DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategory (.up ℤ)).map
        (a • 𝟙 M)) = _
      rw [hH]
      exact map_smul_id DerivedCategory.Qh a _
    have hn : (derivedPullback f).map (DerivedCategory.Qh.map (a • 𝟙 M)) ≫
        (derivedPullbackComparison f).app M =
          (derivedPullbackComparison f).app M ≫ (pullbackOnHomotopy f).map (a • 𝟙 M) :=
      (derivedPullbackComparison f).naturality (a • 𝟙 M)
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerLeft_app]
    simp only [γ₁, γ₂]
    refine (congrArg (fun t => (derivedPullback f).map t ≫ (derivedPullbackComparison f).app M)
      hQ.symm).trans (hn.trans ?_)
    exact (congrArg ((derivedPullbackComparison f).app M ≫ ·) hF).trans
      ((Linear.comp_smul _ _ _ _ _ _).trans ((congrArg (a • ·)
        ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
          (Linear.smul_comp _ _ _ _ _ _).symm))
  exact congrArg (fun γ : derivedPullback f ⟶ derivedPullback f => γ.app K) h

open DerivedAdjunctionOnRingedSpaces in
/-- **The derived pullback is linear over the global sections of the target**: `Lf^*(a • φ)` is
`a • Lf^* φ`, where `a` acts on `D(𝒪_X)` through `f^♯`. -/
theorem derivedPullback_map_smul (a : Y.presheaf.obj (op ⊤))
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (φ : K ⟶ L) :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (derivedPullback f).map (a • φ) = a • (derivedPullback f).map φ := by
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  have h : a • φ = (a • 𝟙 K) ≫ φ :=
    ((Linear.smul_comp _ _ _ _ _ _).trans (congrArg (a • ·) (Category.id_comp φ))).symm
  exact (congrArg (derivedPullback f).map h).trans (((derivedPullback f).map_comp _ _).trans
    ((congrArg (· ≫ (derivedPullback f).map φ) (derivedPullback_map_smul_id f a K)).trans
      ((Linear.smul_comp _ _ _ _ _ _).trans (congrArg (a • ·) (Category.id_comp _)))))

open DerivedAdjunctionOnRingedSpaces in
/-- `Lf^*` as a `Γ(Y, 𝒪_Y)`-linear functor. -/
theorem derivedPullback_linear :
    letI := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
    letI := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
    (derivedPullback f).Linear (Y.presheaf.obj (op ⊤)) :=
  let := linearTop X (Y.presheaf.obj (op ⊤)) (globalSectionsMap f)
  let := linearTop Y (Y.presheaf.obj (op ⊤)) (RingHom.id _)
  ⟨fun φ a => derivedPullback_map_smul f a φ⟩

end Stacks.Cohomology.DerivedPullbackLinear

namespace AlgebraicGeometry.Scheme

open StrictlyPerfect Stacks.SheafOfModules

/-- The `Γ(X, ⊤)`-linear structure on sheaves of `𝒪_X`-modules, in the spelling
`OXMod X.toRingedSpace` that relative perfectness and relative dualizing complexes use. -/
@[instance_reducible]
def linearOXMod (X : Scheme.{u}) : Linear Γ(X, ⊤) (OXMod.{u, u} X.toRingedSpace) :=
  Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id _)

/-- The `Γ(X, ⊤)`-linear structure on sheaves of `𝒪_X`-modules, in the spelling
`SheafOfModules (structureSheafRing X.toSheafedSpace)` of the derived pullback. -/
@[instance_reducible]
def linearStructureSheafRing (X : Scheme.{u}) :
    Linear Γ(X, ⊤) (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) :=
  Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id _)

/-- The `Γ(X, ⊤)`-linear structure on sheaves of `𝒪_Y`-modules through `g^♯`, in the spelling
`StructureSheafModules Y.sheaf` of the derived internal hom. -/
@[instance_reducible]
def Hom.linearStructureSheafModules {X Y : Scheme.{u}} (g : Y ⟶ X) :
    Linear Γ(X, ⊤) (StructureSheafModules Y.sheaf) :=
  Scheme.linearOfRingHom Y Γ(X, ⊤) g.appTop.hom

/-- The `Γ(X, ⊤)`-linear structure on sheaves of `𝒪_Y`-modules through `g^♯`, in the spelling
`SheafOfModules (structureSheafRing Y.toSheafedSpace)` of the derived pullback. -/
@[instance_reducible]
def Hom.linearStructureSheafRing {X Y : Scheme.{u}} (g : Y ⟶ X) :
    Linear Γ(X, ⊤) (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)) :=
  Scheme.linearOfRingHom Y Γ(X, ⊤) g.appTop.hom

namespace Hom

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **The derived pullback along a morphism of schemes `g : Y ⟶ X` is `Γ(X, ⊤)`-linear**, for
`Γ(X, ⊤)` acting on `D(𝒪_Y)` through `g^♯ : Γ(X, ⊤) ⟶ Γ(Y, ⊤)`: `Lg^*(a • φ) = a • Lg^* φ`. -/
theorem derivedPullback_map_smul (a : Γ(X, ⊤))
    {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (φ : K ⟶ L) :
    letI := linearOXMod X
    letI := Scheme.linearStructureSheafRing X
    letI := g.linearStructureSheafRing
    (derivedPullback g.toLRSHom.toShHom).map (a • φ) =
      a • (derivedPullback g.toLRSHom.toShHom).map φ :=
  Stacks.Cohomology.DerivedPullbackLinear.derivedPullback_map_smul g.toLRSHom.toShHom a φ

/-- **`Lg^*(a • 𝟙_K) = a • 𝟙_{Lg^* K}`** for a morphism of schemes `g : Y ⟶ X` and
`a ∈ Γ(X, ⊤)`, with `a` acting on `D(𝒪_Y)` through `g^♯`. -/
theorem derivedPullback_map_smul_id (a : Γ(X, ⊤))
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    letI := linearOXMod X
    letI := Scheme.linearStructureSheafRing X
    letI := g.linearStructureSheafRing
    (derivedPullback g.toLRSHom.toShHom).map (a • 𝟙 K) =
      a • 𝟙 ((derivedPullback g.toLRSHom.toShHom).obj K) :=
  Stacks.Cohomology.DerivedPullbackLinear.derivedPullback_map_smul_id g.toLRSHom.toShHom a K

/-- `Lg^*` as a `Γ(X, ⊤)`-linear functor, for a morphism of schemes `g : Y ⟶ X`. -/
theorem derivedPullback_linear :
    letI := linearOXMod X
    letI := Scheme.linearStructureSheafRing X
    letI := g.linearStructureSheafRing
    (derivedPullback g.toLRSHom.toShHom).Linear Γ(X, ⊤) :=
  Stacks.Cohomology.DerivedPullbackLinear.derivedPullback_linear g.toLRSHom.toShHom

end Hom

end AlgebraicGeometry.Scheme
