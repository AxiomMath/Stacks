module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleTensorLeft
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.FreeTensorTwist
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxGraded
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# The free graded module on a sheaf of modules placed in a single degree

Let `X` be a scheme and `𝓟` a sheaf of graded `𝒪_X`-algebras. For a sheaf of `𝒪_X`-modules `F`
and an integer `d` this file builds the graded `𝓟`-module

`F ⊗_{𝒪_X} 𝓟(-d)`,  with degree-`n` piece  `F ⊗_{𝒪_X} 𝓟_{n-d}`,

and proves that it is **free on `F` in degree `d`**: a morphism of `𝒪_X`-modules
`φ : F ⟶ N_d` into the degree-`d` piece of a graded `𝓟`-module `N` extends to a homomorphism of
graded `𝓟`-modules `F ⊗ 𝓟(-d) ⟶ N`, by `x ⊗ a ↦ φ(x) · a`.

This is the object the dévissage of part (2) of [Stacks, Tag 0897] needs as the middle term of its
presentation, and the one the module
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxPresentation`
records as missing. `SheafOfModules.freeGradedModule` builds the free graded module on a sheaf of
graded *sets*, and `Stacks.extByZero` the free one on a single generator supported on an open;
neither has uniformly acyclic twists. The point of allowing a *sheaf of modules* in the generating
degree is that `F` may be taken to be a negative twist `L ^⊗ (-k)` of an ample invertible module,
whose finite direct sums have uniformly acyclic twists.

## Main definitions

* `Stacks.Coherent.shiftedAlgebraModule` is `𝓟(-d)`: the sheaf of graded algebras `𝓟` read as a
  right graded module over itself (`SheafOfModules.GradedModule.regularModule`) with its degrees
  shifted by `-d` (`SheafOfModules.GradedModule.shift`), so that the unit sits in degree `d`.
* `Stacks.Coherent.freeGradedModuleOn` is `F ⊗_{𝒪_X} 𝓟(-d)`, obtained from
  `SheafOfModules.GradedModule.tensorLeft`, and `Stacks.Coherent.freeGradedMk` is the image of a
  pure tensor of local sections in one of its pieces.
* `Stacks.Coherent.freeGradedAct` is the value `φ(x) · a` of the bilinear map attached to
  `φ : F ⟶ N_d`, `Stacks.Coherent.freeGradedBil` the bilinear map itself, and
* `Stacks.Coherent.freeGradedModuleOnDesc` the homomorphism of graded `𝓟`-modules it descends to.

## Main results

* `Stacks.Coherent.freeGradedModuleOn_piece`: the degree-`n` piece of `F ⊗ 𝓟(-d)` **is** the
  tensor product sheaf `F ⊗ 𝓟_{n-d}`, on the nose rather than up to isomorphism. Everything
  cohomological about the pieces is therefore literally a statement about that tensor product,
  and no transport intervenes — which is what the dévissage needs, it reading its acyclicity
  hypothesis off the pieces.
* `Stacks.Coherent.freeGradedBil_map_smul`: the bilinear maps are compatible with the two
  actions, which is what makes them descend.
* `Stacks.Coherent.freeGradedModuleOnDesc_app_tmul`: **the computation rule of the universal
  property** — the descended homomorphism sends `x ⊗ a` to `φ(x) · a`.
* `Stacks.Coherent.isZero_Hgroup_tensorLeft_piece_tensorPowModule` and its instance
  `Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule`: **the twists of the
  pieces are acyclic, uniformly in the homogeneous degree**, as soon as the twists of `F` are and
  the pieces of the graded module being tensored are free of finite rank. This is the reason the
  object exists: it is the acyclicity the dévissage of part (2) of [Stacks, Tag 0897] asks of the
  middle term of its presentation, and it is uniform in the degree because the hypothesis on `F`
  does not mention the degree.

## Implementation notes

**Why the shift is applied to the regular module and not written out.** The degree-`n` piece of
`𝓟(-d)` has to be `𝓟_{n-d}` *definitionally*, since the pieces of `F ⊗ 𝓟(-d)` are the tensor
product sheaves of `F` with those pieces on the nose
(`SheafOfModules.GradedModule.tensorLeft_piece`). `SheafOfModules.GradedModule.shift` keeps the
pieces in that way, so the composite does too and `freeGradedModuleOn_piece` is `rfl`.

**The spelling of the shifted degree is `n + -d`, not `n - d`.**
`SheafOfModules.GradedModule.shift` is defined with `piece n = N.piece (n + k)`, so `𝓟(-d)` has
`piece n = 𝓟_{n + -d}`. The two integers are definitionally equal, but a statement written with
`n - d` is not what `rw` sees after unfolding a piece, so the degree is written `n + -d`
throughout and the subtraction never appears.

**Why the value of the bilinear map is a named definition.** The action of `𝓟` on `F ⊗ 𝓟(-d)`
lands in degree `n + i` while `φ(x) · a` is built in degree `d + (n + -d)`; the two are equal but
not definitionally, so the formula carries one `SheafOfModules.castHom`. Were the bilinear map
assembled directly out of `AddMonoidHom.comp`, the action would sit under a composition and the
patterns of `SheafOfModules.GradedModule.smul_smul_left`, `smul_castHom_left` and their
companions would not appear syntactically in any goal; `rw` then fails on every law. Naming the
value as `Stacks.Coherent.freeGradedAct` keeps the action at the head of every subterm, and the
four laws of the bilinear map and the compatibility with the two actions are each a two-line
rewrite.

**Where the transports are discharged.** The compatibility of the family with the two actions is
`SheafOfModules.GradedModule.smul_mul` of `N` — a heterogeneous equality between degrees
`(d + (n + -d)) + i` and `d + ((n + -d) + i)` — read through
`SheafOfModules.castHom_eq_castHom`, which is exactly the lemma for comparing two transports of
heterogeneously equal sections into a common degree. No `eqToHom` and no `simp` on degrees
occurs.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open scoped TensorProduct

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}} {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-! ### `𝓟(-d)`, the algebra with its unit moved to degree `d` -/

/-- **`𝓟(-d)`**: the sheaf of graded algebras `𝓟`, read as a right graded module over itself and
with its degrees shifted so that the unit sits in degree `d`. Its degree-`n` piece is `𝓟_{n-d}`,
definitionally. -/
public abbrev shiftedAlgebraModule (P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (d : ℤ) : SheafOfModules.GradedModule P :=
  (SheafOfModules.GradedModule.regularModule P).shift (-d)

/-- The degree-`n` piece of `𝓟(-d)` is `𝓟_{n-d}`. -/
public theorem shiftedAlgebraModule_piece (d n : ℤ) :
    (shiftedAlgebraModule P d).piece n = P.piece (n + -d) := rfl

/-! ### `F ⊗ 𝓟(-d)`, the free graded module on `F` in degree `d` -/

/-- **The free graded `𝓟`-module on a sheaf of modules `F` placed in degree `d`**,
`F ⊗_{𝒪_X} 𝓟(-d)`. Its degree-`n` piece is the tensor product sheaf `F ⊗ 𝓟_{n-d}`, and a
homogeneous local section `y` of `𝓟` acts by `(x ⊗ a) · y = x ⊗ (a y)`. -/
public def freeGradedModuleOn (F : X.Modules)
    (P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (d : ℤ) :
    SheafOfModules.GradedModule P :=
  SheafOfModules.GradedModule.tensorLeft X.presheaf (isSheaf_structureRingPresheaf X) F
    (shiftedAlgebraModule P d)

/-- **The degree-`n` piece of `F ⊗ 𝓟(-d)` is the tensor product sheaf `F ⊗ 𝓟_{n-d}`**, on the
nose. -/
public theorem freeGradedModuleOn_piece (F : X.Modules) (d n : ℤ) :
    (freeGradedModuleOn F P d).piece n = tensorModules X F (P.piece (n + -d)) := rfl

/-- The image of a pure tensor `x ⊗ a` of local sections in the degree-`n` piece of
`F ⊗ 𝓟(-d)`. -/
public abbrev freeGradedMk (F : X.Modules) (d n : ℤ) (U : X.Opensᵒᵖ) :
    SheafOfModules.GradedModule.tensorLeftSection X.presheaf
        (isSheaf_structureRingPresheaf X) F (shiftedAlgebraModule P d) n U →+
      ((freeGradedModuleOn F P d).piece n).val.obj U :=
  SheafOfModules.GradedModule.tensorLeftMk X.presheaf (isSheaf_structureRingPresheaf X) F
    (shiftedAlgebraModule P d) n U

/-! ### The universal property -/

section Universal

variable (F : X.Modules) {N : SheafOfModules.GradedModule P} {d : ℤ}

/-- **`φ(x) · a`**: the value of the bilinear map attached to a morphism `φ : F ⟶ N_d` into the
degree-`d` piece of a graded `𝓟`-module. The action lands in degree `d + (n - d)`, so the formula
carries one `SheafOfModules.castHom`. -/
public def freeGradedAct (φ : F ⟶ N.piece d) (n : ℤ) (U : X.Opensᵒᵖ) (x : F.val.obj U)
    (a : (P.piece (n + -d)).val.obj U) : (N.piece n).val.obj U :=
  SheafOfModules.castHom N.piece (show d + (n + -d) = n by omega) U
    (N.smul d (n + -d) U (φ.val.app U x) a)

/-- `freeGradedAct F φ n U x a` is additive in the section `x` of `F`. -/
public theorem freeGradedAct_add_left (φ : F ⟶ N.piece d) (n : ℤ) (U : X.Opensᵒᵖ)
    (x x' : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    freeGradedAct F φ n U (x + x') a =
      freeGradedAct F φ n U x a + freeGradedAct F φ n U x' a := by
  simp only [freeGradedAct, map_add, AddMonoidHom.add_apply]

/-- `freeGradedAct F φ n U x a` is additive in the section `a` of `𝓟_{n-d}`. -/
public theorem freeGradedAct_add_right (φ : F ⟶ N.piece d) (n : ℤ) (U : X.Opensᵒᵖ)
    (x : F.val.obj U) (a a' : (P.piece (n + -d)).val.obj U) :
    freeGradedAct F φ n U x (a + a') =
      freeGradedAct F φ n U x a + freeGradedAct F φ n U x a' := by
  simp only [freeGradedAct, map_add]

/-- `freeGradedAct F φ n U x a` is linear over `𝒪_X(U)` in the section `x` of `F`. -/
public theorem freeGradedAct_smul_left (φ : F ⟶ N.piece d) (n : ℤ) (U : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.obj.obj U) (x : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    freeGradedAct F φ n U (r • x) a = r • freeGradedAct F φ n U x a := by
  simp only [freeGradedAct]
  rw [map_smul, N.smul_smul_left, SheafOfModules.castHom_smul]

/-- `freeGradedAct F φ n U x a` is linear over `𝒪_X(U)` in the section `a` of `𝓟_{n-d}`. -/
public theorem freeGradedAct_smul_right (φ : F ⟶ N.piece d) (n : ℤ) (U : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.obj.obj U) (x : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    freeGradedAct F φ n U x (r • a) = r • freeGradedAct F φ n U x a := by
  simp only [freeGradedAct]
  rw [N.smul_smul_right, SheafOfModules.castHom_smul]

/-- `freeGradedAct F φ n` commutes with restriction of sections along `U ⟶ V`. -/
public theorem freeGradedAct_naturality (φ : F ⟶ N.piece d) (n : ℤ) {U V : X.Opensᵒᵖ}
    (f : U ⟶ V) (x : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    (N.piece n).val.map f (freeGradedAct F φ n U x a) =
      freeGradedAct F φ n V (F.val.map f x) ((P.piece (n + -d)).val.map f a) := by
  simp only [freeGradedAct]
  rw [SheafOfModules.castHom_naturality, N.smul_naturality,
    PresheafOfModules.naturality_apply φ.val f x]

/-- **The bilinear maps `F × 𝓟_{n-d} → N_n`, `(x, a) ↦ φ(x) · a`**, attached to a morphism
`φ : F ⟶ N_d`. -/
public def freeGradedBil (φ : F ⟶ N.piece d) (n : ℤ) :
    Stacks.BilinearMap F.val ((shiftedAlgebraModule P d).piece n).val (N.piece n).val where
  app U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun a => freeGradedAct F φ n U x a)
      (freeGradedAct_add_right F φ n U x))
    (fun x x' => AddMonoidHom.ext fun a => freeGradedAct_add_left F φ n U x x' a)
  map_smul_left U r x y := freeGradedAct_smul_left F φ n U r x y
  map_smul_right U r x y := freeGradedAct_smul_right F φ n U r x y
  naturality f x y := freeGradedAct_naturality F φ n f x y

/-- The bilinear map `freeGradedBil F φ n` sends `(x, a)` to `freeGradedAct F φ n U x a`, that is,
to `φ(x) · a`. -/
public theorem freeGradedBil_app (φ : F ⟶ N.piece d) (n : ℤ) (U : X.Opensᵒᵖ)
    (x : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    (freeGradedBil F φ n).app U x a = freeGradedAct F φ n U x a := rfl

/-- **The family `Stacks.Coherent.freeGradedBil` is compatible with the two actions**: acting on
the second variable by a homogeneous section `y` of `𝓟` is acting on the value by `y`. This is
associativity of the action of `𝓟` on `N`, `SheafOfModules.GradedModule.smul_mul`, read through
the two transports the shifted degrees force. -/
public theorem freeGradedBil_map_smul (φ : F ⟶ N.piece d) (n i : ℤ) (U : X.Opensᵒᵖ)
    (x : F.val.obj U) (a : ((shiftedAlgebraModule P d).piece n).val.obj U)
    (y : (P.piece i).val.obj U) :
    (freeGradedBil F φ (n + i)).app U x ((shiftedAlgebraModule P d).smul n i U a y) =
      N.smul n i U ((freeGradedBil F φ n).app U x a) y := by
  have key : ∀ b : (P.piece (n + -d)).val.obj U,
      SheafOfModules.castHom N.piece (show d + (n + i + -d) = n + i by omega) U
          (N.smul d (n + i + -d) U (φ.val.app U x)
            (SheafOfModules.castHom P.piece (show n + -d + i = n + i + -d by omega) U
              ((P.mul (n + -d) i).app U b y)))
        = N.smul n i U
            (SheafOfModules.castHom N.piece (show d + (n + -d) = n by omega) U
              (N.smul d (n + -d) U (φ.val.app U x) b)) y := by
    intro b
    rw [SheafOfModules.Cofree.smul_castHom_right, SheafOfModules.Cofree.castHom_castHom,
      SheafOfModules.Cofree.smul_castHom_left]
    exact SheafOfModules.Cofree.castHom_eq_castHom _ _ U
      (N.smul_mul d (n + -d) i U (φ.val.app U x) b y).symm
  exact key a

/-- **The universal property of `F ⊗ 𝓟(-d)`.** A morphism of `𝒪_X`-modules `φ : F ⟶ N_d` into the
degree-`d` piece of a right graded `𝓟`-module `N` extends to a homomorphism of graded
`𝓟`-modules `F ⊗ 𝓟(-d) ⟶ N`, by `x ⊗ a ↦ φ(x) · a`. -/
public def freeGradedModuleOnDesc (φ : F ⟶ N.piece d) : freeGradedModuleOn F P d ⟶ N :=
  SheafOfModules.GradedModule.tensorLeftDesc X.presheaf (isSheaf_structureRingPresheaf X) F
    (shiftedAlgebraModule P d) N (freeGradedBil F φ) (freeGradedBil_map_smul F φ)

/-- **The computation rule of the universal property**: the extension sends the image of the pure
tensor `x ⊗ a` to `φ(x) · a`. -/
public theorem freeGradedModuleOnDesc_app_tmul (φ : F ⟶ N.piece d) (n : ℤ)
    (U : X.Opensᵒᵖ) (x : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    ((freeGradedModuleOnDesc F φ).app n).val.app U (freeGradedMk F d n U (x ⊗ₜ a)) =
      freeGradedAct F φ n U x a :=
  SheafOfModules.GradedModule.tensorLeftDesc_app_tmul X.presheaf
    (isSheaf_structureRingPresheaf X) F (shiftedAlgebraModule P d) N (freeGradedBil F φ)
    (freeGradedBil_map_smul F φ) n U x a

end Universal

/-! ### Uniform acyclicity of the twists of the pieces -/

section Acyclicity

variable (X)

/-- **Acyclicity of a twist of `F ⊗ G` when `G` is finite free**, transported from the same
statement for `F` itself.

`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_Hgroup_tensorModules_free` is stated with
the free factor on the *left* of the inner tensor product; the two orders are exchanged by
`tensorModulesFreeIso` and `freeTensorModulesIso`, both of which identify the tensor product with
`⊕_{κ} F`. Nothing is assumed of `F`, of `X` or of the exponent `e`: this is a transfer lemma, and
the bound on `e` comes from wherever the hypothesis does. -/
public theorem isZero_Hgroup_tensorModules_free_right (F L : X.Modules)
    [IsInvertibleModule X L] (G : X.Modules) (κ : Type u) [Finite κ]
    (ε : G ≅ SheafOfModules.free κ) (p : ℕ) (e : ℤ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X F (tensorPowModule X L e)))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X (tensorModules X F G) (tensorPowModule X L e))) := by
  refine (Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_Hgroup_tensorModules_free X F L
    κ p e h).of_iso ?_
  exact (Hfunctor X.ringCatSheaf ⊤ p).mapIso
    (Stacks.RelativeVeryAmple.tensorModulesMapIso X
      ((Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl F) ε).trans
        ((Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.tensorModulesFreeIso X F κ).trans
          (Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.freeTensorModulesIso X F κ).symm))
      (Iso.refl (tensorPowModule X L e)))

/-- **The twists of the pieces of `F ⊗ M` are acyclic as soon as those of `F` are, uniformly in
the homogeneous degree, whenever the pieces of `M` are free of finite rank.**

This is the property that makes a tensor product `F ⊗ M` usable as the middle term of the
dévissage of part (2) of [Stacks, Tag 0897]. The degree-`n` piece of `F ⊗ M` is `F ⊗ Mₙ` on the
nose (`SheafOfModules.GradedModule.tensorLeft_piece`), and when `Mₙ` is free of finite rank that
is a finite direct sum of copies of `F`. The hypothesis `h` does not mention `n`, so one exponent
`e` serves every homogeneous degree at once — which is exactly the uniformity
`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over` asks for and which a
graded module over the associated graded algebra itself cannot provide, its pieces not being
free.

The statement is at an arbitrary graded `𝓟`-module `M` rather than at `𝓟(-d)`, because the
middle term of a presentation is a finite direct sum of such modules and its pieces are then
again finite free; `Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule` is
the case `M = 𝓟(-d)`. -/
public theorem isZero_Hgroup_tensorLeft_piece_tensorPowModule {P}
    (F L : X.Modules) [IsInvertibleModule X L] (M : SheafOfModules.GradedModule P)
    (hfree : ∀ m : ℤ, ∃ κ : Type u, ∃ _ : Finite κ,
      Nonempty (M.piece m ≅ SheafOfModules.free κ))
    (p : ℕ) (e : ℤ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X F (tensorPowModule X L e))))
    (n : ℤ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X ((SheafOfModules.GradedModule.tensorLeft X.presheaf
        (isSheaf_structureRingPresheaf X) F M).piece n) (tensorPowModule X L e))) := by
  obtain ⟨κ, hκ, ⟨ε⟩⟩ := hfree n
  exact isZero_Hgroup_tensorModules_free_right X F L (M.piece n) κ ε p e h

/-- **`Stacks.Coherent.isZero_Hgroup_tensorLeft_piece_tensorPowModule` at `M = 𝓟(-d)`**: the
twists of the pieces of the free graded module `F ⊗ 𝓟(-d)` are acyclic as soon as those of `F`
are, uniformly in the homogeneous degree, whenever the pieces of `𝓟` are free of finite rank. -/
public theorem isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule {P}
    (F L : X.Modules) [IsInvertibleModule X L] (d : ℤ)
    (hfree : ∀ m : ℤ, ∃ κ : Type u, ∃ _ : Finite κ,
      Nonempty (P.piece m ≅ SheafOfModules.free κ))
    (p : ℕ) (e : ℤ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X F (tensorPowModule X L e))))
    (n : ℤ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X ((freeGradedModuleOn F P d).piece n) (tensorPowModule X L e))) :=
  isZero_Hgroup_tensorLeft_piece_tensorPowModule X F L (shiftedAlgebraModule P d)
    (fun m => hfree (m + -d)) p e h n

end Acyclicity

end Stacks.Coherent

end
