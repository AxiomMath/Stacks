module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.DualSheafIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.UnitDual
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Duality on the Grothendieck ring of vector bundles

Let `X` be a scheme and let `K₀(Vect(X))` be the Grothendieck ring of finite locally free
`𝒪_X`-modules, whose multiplication is induced by tensor product and whose unit is the class of
the structure sheaf. Dualizing a finite locally free module, `ℰ ↦ ℰ^∨ = SheafHom(ℰ, 𝒪_X)`,
induces a ring endomorphism `ψ^{-1}` of `K₀(Vect(X))`, the *minus-one Adams operation*, which is
compatible with pullback (Stacks 0FV8).

The construction uses two properties of duality: `DualPreservesFiniteLocallyFree`, that the dual
of a finite locally free module is finite locally free, and `DualShortExact`, that duality
carries a short exact sequence of finite locally free modules to a short exact sequence. Both hold
on every scheme, by `dualPreservesFiniteLocallyFree` and `dualShortExact`. For a finite locally
free module the dual sheaf is a *left dual* in the monoidal category of `𝒪_X`-modules, so the
uniqueness of left duals identifies `(ℰ ⊗ ℱ)^∨` with `ℱ^∨ ⊗ ℰ^∨`, which makes `ψ^{-1}`
multiplicative.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.dualSheafExactPairing`: the dual of a finite locally free
  module on a scheme, with the canonical coevaluation and evaluation, is a left dual of it.
* `AlgebraicGeometry.VectorBundleKZero.DualPreservesFiniteLocallyFree` and
  `AlgebraicGeometry.VectorBundleKZero.DualShortExact`: the two properties of duality from which
  the ring endomorphism is built.
* `AlgebraicGeometry.VectorBundleKZero.classOfDual` and
  `AlgebraicGeometry.VectorBundleKZero.dualAddHom`: the function on sheaves of modules sending a
  finite locally free module to the class of its dual, and the additive endomorphism of
  `K₀(Vect(X))` it descends to.
* `AlgebraicGeometry.VectorBundleKZero.dualRingHom`: that additive endomorphism as a ring
  endomorphism of `K₀(Vect(X))`.
* `AlgebraicGeometry.VectorBundleKZero.pullbackDualSheafIso`: duality commutes with pullback of
  finite locally free modules, `f^*(ℰ^∨) ≅ (f^*ℰ)^∨`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.dualSheaf_tensorObj_iso`: `(ℰ ⊗ ℱ)^∨ ≅ ℱ^∨ ⊗ ℰ^∨` for
  finite locally free `ℰ` and `ℱ`.
* `AlgebraicGeometry.VectorBundleKZero.classOf_dualSheaf_unit`: the class of `𝒪_X^∨` is the unit
  of `K₀(Vect(X))`.
* `AlgebraicGeometry.VectorBundleKZero.dualAddHom_classOf` and
  `AlgebraicGeometry.VectorBundleKZero.dualAddHom_mul_classOf`: the additive endomorphism sends
  the class of a finite locally free module to the class of its dual, and is multiplicative on
  such classes.
* `AlgebraicGeometry.VectorBundleKZero.exists_dualRingHom`: **the minus-one Adams operation**, as
  a ring endomorphism of `K₀(Vect(X))` sending the class of a finite locally free module to the
  class of its dual, granted the two properties of duality.
* `AlgebraicGeometry.VectorBundleKZero.dualPreservesFiniteLocallyFree` and
  `AlgebraicGeometry.VectorBundleKZero.dualShortExact`: the two properties of duality, for every
  scheme.
* `AlgebraicGeometry.VectorBundleKZero.exists_dualRingHom_of_dualShortExact`: the minus-one
  Adams operation, granted only the exactness of duality.
* `AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_pullback` and
  `AlgebraicGeometry.VectorBundleKZero.dualAddHom_pullback`: the pullback of a finite locally
  free module is finite locally free, and the minus-one Adams operation commutes with any ring
  map of Grothendieck rings realising pullback.
* `AlgebraicGeometry.VectorBundleKZero.exists_minusOneAdamsOperator`: **the minus-one Adams
  operation on every scheme**, with its values on finite locally free modules and its
  compatibility with pullbacks.

## Implementation notes

`DualShortExact` asks only for the *existence* of a short exact sequence of the duals, not for
one whose morphisms are the duals of the given ones: the defining relation of the Grothendieck
group refers to the objects of a short exact sequence and not to its morphisms.

**Where the monoidal structure is used.** The dual sheaf is a left dual for the monoidal
structure `Stacks.SheafOfModules.OnSpace.monoidal` on sheaves of modules over a ringed space,
whose tensor product on objects *is* the tensor product sheaf that `K₀(Vect(X))` multiplies
with. That monoidal structure can only be synthesised at the spelling
`CategoryTheory.SheafOfModules (structureSheafRing X.toRingedSpace)` of the category of
`𝒪_X`-modules: the instance is found by unifying `structureSheafRing ?Y` with the sheaf of rings,
which fails at the spelling `AlgebraicGeometry.Scheme.ringCatSheaf` carried by
`AlgebraicGeometry.Scheme.Modules`. The two are definitionally equal, so the declarations about
left duals take their modules at the first spelling and are applied at the second.

The isomorphism `(ℰ ⊗ ℱ)^∨ ≅ ℱ^∨ ⊗ ℰ^∨` is `CategoryTheory.rightDualIso` applied to two exact
pairings with the same left member: the canonical pairing on `ℰ ⊗ ℱ`, and the tensor product
`CategoryTheory.ExactPairing.tensor` of the canonical pairings on `ℰ` and on `ℱ`. The order of
the two factors of the target is the one forced by that construction; where the commuted form is
wanted, as in `dualAddHom_mul_classOf`, commutativity is applied in the ring `K₀(Vect(X))`.

**Compatibility with pullback.** As in the third clause of Tag 0FEJ,
`AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator`, the pullback of classes is
given as an arbitrary ring map `p : K₀(Vect(X)) → K₀(Vect(Y))` sending `[ℰ]` to `[f^*ℰ]`. Its
geometric content, `f^*(ℰ^∨) ≅ (f^*ℰ)^∨`, is `pullbackDualSheafIso`, the dual base-change map
`Stacks.Chow.pullbackDualMap` together with its invertibility on a finite locally free module.

## References

* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.FiniteLocallyFree Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.VectorBundleKZero

open Stacks.SheafOfModules.OnSpace

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable (X : Scheme.{u})

/-- The dual `ℰ^∨ = SheafHom(ℰ, 𝒪_X)` of a sheaf of modules on a scheme is the dual formed over
the underlying ringed space: the two constructions are definitionally equal. -/
theorem dualSheaf_eq_dualSheafRingedSpace
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M =
      Stacks.SheafOfModules.OnSpace.dualSheaf X.toRingedSpace M := rfl

/-- A finite locally free sheaf of modules on a scheme is locally a direct summand of a finite
free module. -/
theorem isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    Stacks.SheafOfModules.IsLocallyFiniteFreeSummand X.toRingedSpace M := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) M :=
    @Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree X M hM
  exact Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
    X.toRingedSpace M

/-- **The dual of a finite locally free module on a scheme is a left dual of it**, with the
canonical coevaluation `𝒪_X ⟶ ℰ ⊗ ℰ^∨` and the canonical evaluation `ℰ^∨ ⊗ ℰ ⟶ 𝒪_X`. This is
Stacks Tag 0FNV read on a scheme, its local hypothesis supplied by finite local freeness. -/
@[instance_reducible]
noncomputable def dualSheafExactPairing
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    ExactPairing M (dualSheaf X.toRingedSpace M) :=
  Stacks.SheafOfModules.OnSpace.dualSheafExactPairing X.toRingedSpace M
    (isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X M hM)

/-- **The dual of a tensor product of finite locally free modules**, `(ℰ ⊗ ℱ)^∨ ≅ ℱ^∨ ⊗ ℰ^∨`.
Both sides are left duals of `ℰ ⊗ ℱ` — the first canonically, the second as the tensor product
of the canonical left duals of `ℰ` and of `ℱ` — and a left dual is unique up to a canonical
isomorphism. -/
@[sga "3 VIIA 3.1.1"]
noncomputable def dualSheaf_tensorObj_iso
    (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    dualSheaf X.toRingedSpace ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (N))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((dualSheaf X.toRingedSpace N))).obj ((dualSheaf X.toRingedSpace M))) :=
  letI := hM
  letI := hN
  letI := dualSheafExactPairing X M hM
  letI := dualSheafExactPairing X N hN
  rightDualIso
    (dualSheafExactPairing X (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).obj N)
      (isFiniteLocallyFree_tensorObj M N))
    (ExactPairing.tensor (X₁ := M) (Y₁ := dualSheaf X.toRingedSpace M)
      (X₂ := N) (Y₂ := dualSheaf X.toRingedSpace N))

/-- **The dual of the structure sheaf is the structure sheaf**, and therefore its class is the
unit of `K₀(Vect(X))`. -/
theorem classOf_dualSheaf_unit :
    classOf X (dualSheaf X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf)) = 1 := by
  have hu : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (dualSheaf X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf)) :=
    @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _
      (Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso X).symm
      (isFiniteLocallyFree_unit X)
  exact (classOf_eq_of_iso
    (Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso X) hu).trans (classOf_unit X)

/-- Duality preserves finite local freeness: the dual of a finite locally free sheaf of modules
on `X` is again finite locally free. -/
def DualPreservesFiniteLocallyFree : Prop :=
  ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (dualSheaf X.toRingedSpace M)

/-- Duality is exact on short exact sequences of finite locally free sheaves of modules: a short
exact sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally free modules gives rise to a short exact
sequence `0 → 𝒢^∨ → ℱ^∨ → ℰ^∨ → 0` (only the existence of such a sequence is asked for). -/
def DualShortExact : Prop :=
  ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact →
            ∃ (f' : dualSheaf X.toRingedSpace G ⟶ dualSheaf X.toRingedSpace F)
              (g' : dualSheaf X.toRingedSpace F ⟶ dualSheaf X.toRingedSpace E)
              (w' : f' ≫ g' = 0), (ShortComplex.mk f' g' w').ShortExact

open scoped Classical in
/-- The class of the dual of a finite locally free module, and zero on the sheaves of modules
that are not finite locally free. -/
@[sga "6 VIII 3.4"]
noncomputable def classOfDual (M : X.Modules) : VectorBundleKZero X :=
  if IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M then
    classOf X (dualSheaf X.toRingedSpace M) else 0

variable {X}

/-- On a finite locally free module, `classOfDual` is the class of the dual. -/
@[sga "6 VIII 3.4"]
theorem classOfDual_of_isFiniteLocallyFree (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    classOfDual X M = classOf X (dualSheaf X.toRingedSpace M) := by
  rw [classOfDual, if_pos hM]

/-- `classOfDual` vanishes off the finite locally free modules. -/
theorem classOfDual_eq_zero (M : X.Modules)
    (hM : ¬ IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    classOfDual X M = 0 := by
  rw [classOfDual, if_neg hM]

/-- Additivity of `classOfDual` along a short exact sequence of finite locally free modules,
granted that duality preserves finite local freeness and is exact. -/
theorem classOfDual_shortExact (h₁ : DualPreservesFiniteLocallyFree X)
    (h₂ : DualShortExact X) {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact) :
    classOfDual X F = classOfDual X E + classOfDual X G := by
  obtain ⟨f', g', w', hSE⟩ := h₂ f g w hE hF hG hmono hepi hex
  rw [classOfDual_of_isFiniteLocallyFree E hE, classOfDual_of_isFiniteLocallyFree F hF,
    classOfDual_of_isFiniteLocallyFree G hG]
  exact (@classOf_shortExact X _ _ _ f' g' hSE.mono_f hSE.epi_g w'
    (h₁ G hG) (h₁ F hF) (h₁ E hE) hSE.exact).trans (add_comm _ _)

/-- The additive endomorphism of `K₀(Vect(X))` induced by duality. -/
noncomputable def dualAddHom (h₁ : DualPreservesFiniteLocallyFree X) (h₂ : DualShortExact X) :
    VectorBundleKZero X →+ VectorBundleKZero X :=
  liftAddHom (classOfDual X) classOfDual_eq_zero (classOfDual_shortExact h₁ h₂)

/-- The additive endomorphism induced by duality sends the class of a finite locally free module
to the class of its dual. -/
theorem dualAddHom_classOf (h₁ : DualPreservesFiniteLocallyFree X) (h₂ : DualShortExact X)
    (M : X.Modules) (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    dualAddHom h₁ h₂ (classOf X M) = classOf X (dualSheaf X.toRingedSpace M) :=
  (liftAddHom_classOf (classOfDual X) classOfDual_eq_zero
    (classOfDual_shortExact h₁ h₂) M).trans (classOfDual_of_isFiniteLocallyFree M hM)

/-- The endomorphism induced by duality is multiplicative on the classes of finite locally free
modules: the dual of a tensor product is the tensor product of the duals. -/
theorem dualAddHom_mul_classOf (h₁ : DualPreservesFiniteLocallyFree X) (h₂ : DualShortExact X)
    (M N : X.Modules) (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    dualAddHom h₁ h₂ (classOf X M * classOf X N) =
      dualAddHom h₁ h₂ (classOf X M) * dualAddHom h₁ h₂ (classOf X N) := by
  have hMN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.tensorObjRingedSpace X M N) :=
    @isFiniteLocallyFree_tensorObj X M N hM hN
  rw [classOf_mul M N hM hN, dualAddHom_classOf h₁ h₂ _ hMN,
    dualAddHom_classOf h₁ h₂ M hM, dualAddHom_classOf h₁ h₂ N hN, mul_comm,
    classOf_mul _ _ (h₁ N hN) (h₁ M hM)]
  exact classOf_eq_of_iso (dualSheaf_tensorObj_iso X M N hM hN) (h₁ _ hMN)

/-- The endomorphism induced by duality is multiplicative. -/
theorem dualAddHom_map_mul (h₁ : DualPreservesFiniteLocallyFree X) (h₂ : DualShortExact X)
    (a b : VectorBundleKZero X) :
    dualAddHom h₁ h₂ (a * b) = dualAddHom h₁ h₂ a * dualAddHom h₁ h₂ b := by
  have key : ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
      (dualAddHom h₁ h₂).comp (mul X (classOf X M)) =
        (mul X (dualAddHom h₁ h₂ (classOf X M))).comp (dualAddHom h₁ h₂) :=
    fun M hM => addHom_ext fun N hN => dualAddHom_mul_classOf h₁ h₂ M N hM hN
  have h : (dualAddHom h₁ h₂).comp (mulRight b) =
      (mulRight (dualAddHom h₁ h₂ b)).comp (dualAddHom h₁ h₂) :=
    addHom_ext fun M hM =>
      DFunLike.congr_fun (key M hM) b
  exact DFunLike.congr_fun h a

/-- The endomorphism induced by duality is unital. -/
theorem dualAddHom_map_one (h₁ : DualPreservesFiniteLocallyFree X) (h₂ : DualShortExact X) :
    dualAddHom h₁ h₂ 1 = 1 :=
  (dualAddHom_classOf h₁ h₂ _ (isFiniteLocallyFree_unit X)).trans (classOf_dualSheaf_unit X)

/-- **The minus-one Adams operation** `ψ^{-1}`, as a ring endomorphism of `K₀(Vect(X))`, granted
the two properties of duality. Its underlying additive map is `dualAddHom`. -/
noncomputable def dualRingHom (h₁ : DualPreservesFiniteLocallyFree X)
    (h₂ : DualShortExact X) : VectorBundleKZero X →+* VectorBundleKZero X where
  toFun := dualAddHom h₁ h₂
  map_one' := dualAddHom_map_one h₁ h₂
  map_mul' := dualAddHom_map_mul h₁ h₂
  map_zero' := map_zero (dualAddHom h₁ h₂)
  map_add' := map_add (dualAddHom h₁ h₂)

/-- The ring endomorphism `dualRingHom` agrees pointwise with `dualAddHom`. -/
@[simp] theorem dualRingHom_apply (h₁ : DualPreservesFiniteLocallyFree X)
    (h₂ : DualShortExact X) (a : VectorBundleKZero X) :
    dualRingHom h₁ h₂ a = dualAddHom h₁ h₂ a := rfl

/-- **The minus-one Adams operation, granted the two properties of duality.** There is a ring
endomorphism `ψ^{-1}` of `K₀(Vect(X))` which sends the class of a finite locally free module to
the class of its dual. -/
theorem exists_dualRingHom (X : Scheme.{u}) (h₁ : DualPreservesFiniteLocallyFree X)
    (h₂ : DualShortExact X) :
    ∃ ψ : VectorBundleKZero X →+* VectorBundleKZero X,
      ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
        ψ (classOf X M) = classOf X (dualSheaf X.toRingedSpace M) :=
  ⟨dualRingHom h₁ h₂, fun M hM => dualAddHom_classOf h₁ h₂ M hM⟩

/-- **Duality preserves finite local freeness.** The dual of a finite locally free module on `X`
is finite locally free. -/
@[ega "IV 16.5.8" "dual-local-freeness", ega "IV 18.5.1" "partial"]
theorem dualPreservesFiniteLocallyFree (X : Scheme.{u}) :
    DualPreservesFiniteLocallyFree X := by
  intro M hM
  let _ := hM
  have h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) M :=
    Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree M
  let _ := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf M h
  exact Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)

/-- **The minus-one Adams operation, granted that duality is exact.** If duality is exact on
short exact sequences of finite locally free modules, there is a ring endomorphism `ψ^{-1}` of
`K₀(Vect(X))` sending the class of a finite locally free module to the class of its dual. -/
theorem exists_dualRingHom_of_dualShortExact (X : Scheme.{u}) (h₂ : DualShortExact X) :
    ∃ ψ : VectorBundleKZero X →+* VectorBundleKZero X,
      ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
        ψ (classOf X M) = classOf X (dualSheaf X.toRingedSpace M) :=
  exists_dualRingHom X (dualPreservesFiniteLocallyFree X) h₂

/-- **Duality is exact on short exact sequences of finite locally free modules.** A short exact
sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally free modules on `X` gives rise to a short exact
sequence `0 → 𝒢^∨ → ℱ^∨ → ℰ^∨ → 0`. -/
theorem dualShortExact (X : Scheme.{u}) : DualShortExact X := by
  intro E F G f g w hE hF hG hmono hepi hex
  obtain ⟨w', hSE⟩ := Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact
    f g w hmono hepi hex hE hF hG
  exact ⟨Stacks.AlgebraicGeometry.ReflexiveModules.dualMap g,
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap f, w', hSE⟩

/-! ### Compatibility with pullback -/

section Pullback

/-- **The pullback of a finite locally free module is finite locally free**, at the spelling of
finite local freeness that `K₀(Vect(X))` is built over. -/
theorem isFiniteLocallyFree_pullback {Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) ((Scheme.Modules.pullback f).obj M) :=
  @Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree Y
    ((Scheme.Modules.pullback f).obj M)
    (Stacks.Chow.isFiniteLocallyFree_pullback f M
      (@Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree X M hM))

/-- **Duality commutes with pullback of finite locally free modules**, `f^*(ℰ^∨) ≅ (f^*ℰ)^∨`.
This is the dual base-change map `Stacks.Chow.pullbackDualMap`, which is invertible on a finite
locally free module by `Stacks.Chow.pullbackDualMap_isIso`; it is the case `𝒢 = 𝒪` of the
internal-Hom base-change comparison of Tag 0GMX. -/
@[ega "0 5.4.5" "special case",
  ega "III 7.7.9" "(i)",
  ega "IV 18.5.1" "base change of the dual",
  sga "3 I 4.6.5" "Case F′ = O_S"]
noncomputable def pullbackDualSheafIso {Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    (Scheme.Modules.pullback f).obj (dualSheaf X.toRingedSpace M) ≅
      dualSheaf Y.toRingedSpace ((Scheme.Modules.pullback f).obj M) :=
  @asIso _ _ _ _ (Stacks.Chow.pullbackDualMap f M) (Stacks.Chow.pullbackDualMap_isIso f M
    (@Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree X M hM))

/-- **The minus-one Adams operation is compatible with pullback.** Let `f : Y ⟶ X` be a morphism
of schemes and let `p` be a ring homomorphism `K₀(Vect(X)) → K₀(Vect(Y))` sending the class of a
finite locally free module `ℰ` to the class of `f^*ℰ`. Then duality commutes with `p`. -/
theorem dualAddHom_pullback {Y : Scheme.{u}} (f : Y ⟶ X)
    (h₁ : DualPreservesFiniteLocallyFree X) (h₂ : DualShortExact X)
    (k₁ : DualPreservesFiniteLocallyFree Y) (k₂ : DualShortExact Y)
    (p : VectorBundleKZero X →+* VectorBundleKZero Y)
    (hp : ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
      p (classOf X M) = classOf Y ((Scheme.Modules.pullback f).obj M))
    (a : VectorBundleKZero X) :
    dualAddHom k₁ k₂ (p a) = p (dualAddHom h₁ h₂ a) := by
  have hcomp : (dualAddHom k₁ k₂).comp (p : VectorBundleKZero X →+ VectorBundleKZero Y) =
      (p : VectorBundleKZero X →+ VectorBundleKZero Y).comp (dualAddHom h₁ h₂) := by
    refine addHom_ext fun M hM => ?_
    show dualAddHom k₁ k₂ (p (classOf X M)) = p (dualAddHom h₁ h₂ (classOf X M))
    rw [hp M hM, dualAddHom_classOf k₁ k₂ _ (isFiniteLocallyFree_pullback f M hM),
      dualAddHom_classOf h₁ h₂ M hM, hp _ (h₁ M hM)]
    exact (classOf_eq_of_iso (pullbackDualSheafIso f M hM)
      (isFiniteLocallyFree_pullback f _ (h₁ M hM))).symm
  exact DFunLike.congr_fun hcomp a

end Pullback

/-- **The minus-one Adams operation.** There is a ring endomorphism `ψ^{-1}` of `K₀(Vect(X))`
which sends the class of a finite locally free module to the class of its dual, and which
commutes with duality along any ring map `p : K₀(Vect(X)) → K₀(Vect(Y))` sending the class of a
finite locally free module `ℰ` to the class of `f^*ℰ`, for a morphism `f : Y ⟶ X`. -/
@[stacks 0FV8 "the ring map, its values on finite locally free modules and its compatibility \
  with pullback", sga "6 VIII 3.4" "more general"]
theorem exists_minusOneAdamsOperator (X : Scheme.{u}) :
    ∃ ψ : VectorBundleKZero X →+* VectorBundleKZero X,
      (∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
          ψ (classOf X M) = classOf X (dualSheaf X.toRingedSpace M)) ∧
        ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (p : VectorBundleKZero X →+* VectorBundleKZero Y),
          (∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
              p (classOf X M) = classOf Y ((Scheme.Modules.pullback f).obj M)) →
            ∀ a : VectorBundleKZero X,
              dualAddHom (dualPreservesFiniteLocallyFree Y) (dualShortExact Y) (p a) = p (ψ a) :=
  ⟨dualRingHom (dualPreservesFiniteLocallyFree X) (dualShortExact X),
    fun M hM => dualAddHom_classOf (dualPreservesFiniteLocallyFree X) (dualShortExact X) M hM,
    fun _Y f p hp a => dualAddHom_pullback f (dualPreservesFiniteLocallyFree X)
      (dualShortExact X) (dualPreservesFiniteLocallyFree _) (dualShortExact _) p hp a⟩

end AlgebraicGeometry.VectorBundleKZero
