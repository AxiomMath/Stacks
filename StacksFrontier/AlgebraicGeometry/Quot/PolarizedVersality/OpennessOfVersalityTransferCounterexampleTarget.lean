module

public import StacksFrontier.Deformation.Artin.Versality.OpennessCounterexampleAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack

/-!
# The target stack of the counterexample to the second route of Stacks 0D4W

Over `S = Spec k[s, t]`, let `𝒳′` be the category of Stacks 07XR
(`Deformation.Artin.artinAxiomsCategory`) and let `𝒲` be the sheaf of locally nilpotent
functions, `T ↦ {f ∈ Γ(T, 𝒪_T) | D(f) = ∅}`. This file builds the product `𝒴 = 𝒳′ × 𝒲` as the
category of elements of the sheaf of sets
`T ↦ {f ∈ Γ(T, 𝒪_T) | D(f) = ∅ and T ∈ 𝒳′}` (the fibres of `𝒳′` have at most one object), shows
that it is a stack in groupoids for the fppf topology, and builds the 1-morphism
`F = (id, 0) : 𝒳′ ⟶ 𝒴`.

## Main definitions

* `AlgebraicGeometry.PolarizedVersality.OpennessTransfer.nilpotentFunctions`: the sheaf of sets
  whose category of elements is `𝒴`.
* `AlgebraicGeometry.PolarizedVersality.OpennessTransfer.targetStack`: `𝒴`, a stack in groupoids.
* `AlgebraicGeometry.PolarizedVersality.OpennessTransfer.sourceStack`: `𝒳′`, a stack in groupoids.
* `AlgebraicGeometry.PolarizedVersality.OpennessTransfer.zeroSection`: the 1-morphism `(id, 0)`.

## Main results

* `AlgebraicGeometry.PolarizedVersality.OpennessTransfer.isSheaf_nilpotentFunctions`: the presheaf
  is an fppf sheaf: global functions are one (Stacks 03DU), the empty basic open is detected on a
  jointly surjective family, and the condition of Stacks 07XR is fppf local.

## Implementation notes

A function `f` is locally nilpotent exactly when its basic open `D(f)` is empty; this form of the
condition is inherited along every morphism (`D(φ^* f) = φ⁻¹ D(f)`) and descends along jointly
surjective families, which is all the sheaf property asks.
-/

@[expose] public noncomputable section

universe u w wX wY

open CategoryTheory Opposite Deformation.Artin

namespace AlgebraicGeometry.PolarizedVersality.OpennessTransfer

variable {k : Type u} [Field k] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))

/-- The global functions of an object of the big fppf site of `Spec k[s,t]`, as a type. -/
abbrev functions (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS) : Type u :=
  Γ(B.inclusion.obj T.left, ⊤)

/-- The pullback of global functions along a morphism of the big fppf site. -/
abbrev pullbackFunction {T T' : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS}
    (φ : T' ⟶ T) (f : functions B hS T) : functions B hS T' :=
  (B.inclusion.map φ.left).appTop f

/-- The condition on a global function of `T` defining the values of the sheaf: `f` is locally
nilpotent (its basic open is empty) and `T` is an object of the category of Stacks 07XR. -/
def IsNilpotentPoint (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
    (f : functions B hS T) : Prop :=
  (B.inclusion.obj T.left).basicOpen f = ⊥ ∧ IsArtinAxiomsObject k B hS T

/-- The condition `AlgebraicGeometry.PolarizedVersality.OpennessTransfer.IsNilpotentPoint` is
stable under pullback of functions along a morphism `T' ⟶ T`. -/
theorem IsNilpotentPoint.pullback {T T' : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS}
    (φ : T' ⟶ T) {f : functions B hS T} (hf : IsNilpotentPoint B hS T f) :
    IsNilpotentPoint B hS T' (pullbackFunction B hS φ f) := by
  refine ⟨?_, hf.2.of_hom B hS φ⟩
  show (B.inclusion.obj T'.left).basicOpen ((B.inclusion.map φ.left).app ⊤ f) = ⊥
  rw [← Scheme.preimage_basicOpen, hf.1]
  rfl

/-- Pulling back functions is functorial. -/
theorem pullbackFunction_comp {T T' T'' : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS}
    (φ : T'' ⟶ T') (ψ : T' ⟶ T) (f : functions B hS T) :
    pullbackFunction B hS (φ ≫ ψ) f = pullbackFunction B hS φ (pullbackFunction B hS ψ f) := by
  show (B.inclusion.map (φ.left ≫ ψ.left)).appTop f =
    (B.inclusion.map φ.left).appTop ((B.inclusion.map ψ.left).appTop f)
  rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The presheaf `T ↦ {f ∈ Γ(T, 𝒪_T) | D(f) = ∅ and T ∈ 𝒳′}`; its category of elements is
`𝒳′ × 𝒲`. -/
def nilpotentFunctions :
    (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)ᵒᵖ ⥤ Type u where
  obj T := {f : functions B hS T.unop // IsNilpotentPoint B hS T.unop f}
  map φ := ↾ (fun f => ⟨pullbackFunction B hS φ.unop f.1, f.2.pullback B hS φ.unop⟩)
  map_id T := by
    ext f
    change (B.inclusion.map (𝟙 T.unop.left)).appTop f.1 = f.1
    rw [CategoryTheory.Functor.map_id]
    simp
  map_comp φ ψ := by
    ext f
    change (B.inclusion.map (ψ.unop.left ≫ φ.unop.left)).appTop f.1 =
      (B.inclusion.map ψ.unop.left).appTop ((B.inclusion.map φ.unop.left).appTop f.1)
    rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

/-- The presheaf of global functions on the big fppf site of `Spec k[s,t]`, as types. -/
abbrev functionsPresheaf :
    (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)ᵒᵖ ⥤ Type u :=
  (Over.forget (B.obj hS)).op ⋙ B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat

/-- The presheaf of global functions on the big fppf site of `Spec k[s,t]` is a sheaf of types for
the fppf topology (Stacks 03DU). -/
theorem isSheaf_functionsPresheaf :
    Presieve.IsSheaf (BigFppfOver.topology B _ hS) (functionsPresheaf B hS) := by
  have h := (Sheaf.over (⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (B.isSheaf_globalSections)⟩ :
    Sheaf B.topology (Type u)) (B.obj hS)).property
  rwa [isSheaf_iff_isSheaf_of_type] at h

/-- **The presheaf of locally nilpotent functions on objects of `𝒳′` is an fppf sheaf.** A
compatible family glues as a family of functions (Stacks 03DU); the glued function has empty
basic open because the members of a covering are jointly surjective and the basic open of a
pullback is the preimage of the basic open; and the condition of Stacks 07XR is fppf local. -/
theorem isSheaf_nilpotentFunctions :
    Presheaf.IsSheaf (BigFppfOver.topology B _ hS) (nilpotentFunctions B hS) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR x hx
  let x' : Presieve.FamilyOfElements (functionsPresheaf B hS) R.arrows :=
    fun V f hf => (x f hf).1
  have hx' : x'.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    congrArg Subtype.val (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨t, ht, htu⟩ := isSheaf_functionsPresheaf B hS R hR x' hx'
  have hbot : (B.inclusion.obj T.left).basicOpen (t : functions B hS T) = ⊥ := by
    obtain ⟨E, hE, hle⟩ := BigFppfOver.exists_isCovering_sieve₀_le B _ hS hR
    obtain ⟨hsurj, -⟩ := B.jointlySurjective_and_flat_and_lfp_of_isCovering hE
    refine eq_bot_iff.mpr fun p hp => ?_
    obtain ⟨i, y, rfl⟩ := hsurj p
    have h1 := (x (E.f i) (hle _ (E.sieve₀_f i))).2.1
    have h2 : (x (E.f i) (hle _ (E.sieve₀_f i))).1 =
        (B.inclusion.map (E.f i).left).appTop (t : functions B hS T) :=
      (ht (E.f i) (hle _ (E.sieve₀_f i))).symm
    rw [h2] at h1
    exact (congrArg (y ∈ ·) h1).mp ((Scheme.preimage_basicOpen_top
      (B.inclusion.map (E.f i).left) (t : functions B hS T)).subst (motive := (y ∈ ·)) hp)
  have hT : IsArtinAxiomsObject k B hS T :=
    isArtinAxiomsObject_of_mem_topology B hS hR fun V f hf => (x f hf).2.2
  refine ⟨⟨t, hbot, hT⟩, fun V f hf => Subtype.ext (ht f hf), fun y hy => ?_⟩
  exact Subtype.ext (htu y.1 fun V f hf => congrArg Subtype.val (hy f hf))

/-- The underlying category of `𝒴 = 𝒳′ × 𝒲`: the category of elements of
`AlgebraicGeometry.PolarizedVersality.OpennessTransfer.nilpotentFunctions`. -/
abbrev targetBased : BasedCategory (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS) :=
  presheafOfCategories (nilpotentFunctions B hS ⋙ typeToCat)

/-- The objects of `𝒴 = 𝒳′ × 𝒲`, written as the category of elements itself, so that their two
components are well typed at reducible transparency. -/
abbrev TargetObj : Type (u + 1) :=
  Pseudofunctor.CoGrothendieck (nilpotentFunctions B hS ⋙ typeToCat).toPseudofunctor'

variable {B hS} in
/-- The locally nilpotent function of an object of `𝒴`. -/
def objFn (x : TargetObj B hS) : functions B hS x.base := x.fiber.as.1

variable {B hS} in
/-- The locally nilpotent function of an object of `𝒴` has empty basic open. -/
theorem basicOpen_objFn (x : TargetObj B hS) :
    (B.inclusion.obj x.base.left).basicOpen (objFn x) = ⊥ :=
  x.fiber.as.2.1

variable {B hS} in
/-- The base of an object of `𝒴` is an object of the category of Stacks 07XR. -/
theorem isArtinAxiomsObject_objFn (x : TargetObj B hS) : IsArtinAxiomsObject k B hS x.base :=
  x.fiber.as.2.2

/-- `𝒴 = 𝒳′ × 𝒲` is fibred in groupoids, being fibred in sets. -/
theorem isFiberedInGroupoids_targetBased : (targetBased B hS).p.IsFiberedInGroupoids :=
  Functor.IsFiberedInSets.isFiberedInGroupoids _

/-- **`𝒴 = 𝒳′ × 𝒲` is a stack in groupoids** for the fppf topology: it is the category of
elements of a sheaf of sets. -/
theorem isStackInGroupoids_targetBased :
    (targetBased B hS).p.IsStackInGroupoids.{w} (BigFppfOver.topology B _ hS) :=
  ((PresheafOfCategories.isStackInSets_discreteProjection _ _
    (isSheaf_nilpotentFunctions B hS)).isStack).isStackInGroupoids
    (isFiberedInGroupoids_targetBased B hS)

/-- `𝒴 = 𝒳′ × 𝒲` as a stack in groupoids over the big fppf site of `Spec k[s,t]`. -/
def targetStack : StackInGroupoids.{w} (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
    (BigFppfOver.topology B _ hS) :=
  ⟨targetBased B hS, isStackInGroupoids_targetBased B hS⟩

/-- `𝒳′`, the category of Stacks 07XR, as a stack in groupoids over the big fppf site of
`Spec k[s,t]`. -/
def sourceStack : StackInGroupoids.{w} (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
    (BigFppfOver.topology B _ hS) :=
  ⟨BasedCategory.ofFunctor (ObjectProperty.ι (IsArtinAxiomsObject k B hS)),
    isStackInGroupoids_artinAxiomsCategory B hS⟩

/-- A morphism of `𝒴` from a morphism of the site pulling back the function of its target to the
function of its source. -/
def targetHom {X Y : (targetBased B hS).obj} (f : X.base ⟶ Y.base)
    (h : X.fiber.as = (nilpotentFunctions B hS).map f.op Y.fiber.as) : X ⟶ Y :=
  ⟨f, ⟨h⟩⟩

/-- Morphisms of `𝒴` are determined by their underlying morphisms of the site. -/
theorem targetHom_ext {X Y : (targetBased B hS).obj} {a b : X ⟶ Y} (h : a.base = b.base) :
    a = b :=
  Pseudofunctor.CoGrothendieck.Hom.ext _ _ h Discrete.hom_eq

/-- A morphism of `𝒴` pulls back the function of its target to the function of its source. -/
theorem fiber_eq_of_hom {X Y : (targetBased B hS).obj} (a : X ⟶ Y) :
    X.fiber.as = (nilpotentFunctions B hS).map a.base.op Y.fiber.as :=
  Discrete.eq_of_hom a.fiber

/-- A morphism of `𝒴` pulls back the function of its target to the function of its source. -/
theorem objFn_eq_of_hom {X Y : TargetObj B hS} (a : X ⟶ Y) :
    objFn X = pullbackFunction B hS a.base (objFn Y) :=
  congrArg Subtype.val (fiber_eq_of_hom B hS a)

/-- The object `(T, 0)` of `𝒴` over an object `T` of `𝒳′`. -/
def zeroObj (x : artinAxiomsCategory k B hS) : (targetBased B hS).obj :=
  ⟨x.obj, Discrete.mk ⟨0, by
    refine ⟨?_, x.property⟩
    change (B.inclusion.obj x.obj.left).basicOpen (0 : functions B hS x.obj) = ⊥
    exact Scheme.basicOpen_zero _ _⟩⟩

/-- **The 1-morphism `F = (id, 0) : 𝒳′ ⟶ 𝒳′ × 𝒲`.** -/
def zeroSection : (sourceStack.{u, wX} B hS).toBasedCategory ⥤ᵇ
    (targetStack.{u, wY} B hS).toBasedCategory where
  obj x := zeroObj B hS x
  map {x y} φ := targetHom B hS (X := zeroObj B hS x) (Y := zeroObj B hS y) φ.hom
    (Subtype.ext (by
      change (0 : functions B hS x.obj) = (B.inclusion.map φ.hom.left).appTop 0
      rw [map_zero]))
  map_id x := targetHom_ext B hS rfl
  map_comp φ ψ := targetHom_ext B hS rfl
  w := rfl

end AlgebraicGeometry.PolarizedVersality.OpennessTransfer
