module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of Stacks 01CD is monoidal

Let `f : X ⟶ Y` be a morphism of ringed spaces. Stacks 01CD provides the canonical comparison
`c_{A,B} : f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of sheaves of `𝒪_X`-modules
(`Stacks.RingedSpace.comparison`), and `Stacks.PullbackTensor` proves it invertible. This file
proves that it is natural in each variable and compatible with the associator and with the two
unitors of the monoidal structure of Tag 01CA — i.e. that `f^*`, with the inverses of these
comparisons as its tensorator, is a monoidal functor in the elementary sense.

The proofs rest on one observation, and it is what makes them short where the same statements
are expensive through the localization machinery. Every morphism being compared has source a
**pullback**, so the adjunction `f^* ⊣ f_*` makes it equal to its adjoint transpose, and the
transposes have source an *iterated tensor product sheaf*, where
`PresheafOfModules.tensorSheaf_hom_ext` and `PresheafOfModules.tensorSheaf_hom_ext₂` reduce
equality to the local pure tensors. On those, every morphism involved is computed by a section
formula that is already available: `Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`
for the comparison, and the formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge` for the associator, the
unitors and the two whiskerings. No tensorator of a monoidal functor appears anywhere; in
particular nothing here depends on how the monoidal structure of
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal` is assembled.

## Main definitions

* `Stacks.PullbackTensorCoherence.tmul`: the image of a pure tensor of two local sections in the
  tensor product sheaf, with its type **ascribed** at the monoidal spelling `(A ⊗ B).val.obj U`.
* `Stacks.PullbackTensorCoherence.pullbackTensorComparison`: `Stacks.RingedSpace.comparison`,
  retyped so that its source and target are spelled with the monoidal product `⊗`.
* `Stacks.PullbackTensorCoherence.pullbackUnitComparison`:
  `Stacks.PullbackAlgebra.unitComparison`, retyped at the unit object `𝟙_` of Tag 01CA.
* `Stacks.PullbackTensorCoherence.pullbackCoreMonoidal` and `pullbackComparisonMonoidal`: **`f^*`
  as a monoidal functor whose tensorator is the comparison of Stacks 01CD**, assembled from the
  coherences below by `CategoryTheory.Functor.CoreMonoidal.mk'`.

## Main results

* `tensor_hom_ext` and `tensor_hom_ext₂`: morphisms out of a tensor product, or out of a
  twice-iterated tensor product, are determined by their values on the local pure tensors.
* `tensorHom_tmul`, `whiskerRight_tmul`, `whiskerLeft_tmul`, `associator_hom_tmul`,
  `leftUnitor_hom_tmul`,
  `rightUnitor_hom_tmul`: the section formulas of Tag 01CA, read at `tmul`.
* `mulHom`, `oneMorphism`, `oneSec`, with `mulHom_tmul`, `mulHom_assoc`, `oneMorphism_mulHom`,
  `mulHom_oneMorphism` and `oneMorphism_val_app_oneSec`: the multiplication and the global unit of
  a sheaf of graded algebras as morphisms out of `⊗` and out of `𝟙_`, their values on local
  sections, and the associativity and unit laws as equalities of morphisms.
* `inv_val_app_apply` and `val_app_inv_val_app`: an invertible morphism of sheaves of modules and
  its inverse cancel on local sections, stated for `CategoryTheory.inv` rather than for an
  `Iso`, which is the spelling a comparison carrying an `IsIso` instance produces.
* `pullback_hom_ext`, `pullback_tensor_hom_ext`, `pullback_tensor_hom_ext₂`: two morphisms out
  of `f^*M` agreeing on the pullback-unit images of local sections of `M` are equal, and — when
  `M` is a tensor product, or a twice-iterated one — agreement on the pullback-unit images of
  the local pure tensors suffices.
* `pullbackTensorComparison_naturality_left` and `..._naturality_right`: **naturality of the
  comparison of Stacks 01CD in each variable separately**, in the whiskered form that the
  associativity calculation of a graded algebra uses.
* `pullbackTensorComparison_associator`: **the comparison of Stacks 01CD is compatible with the
  associator of Tag 01CA.**
* `pullbackTensorComparison_leftUnitor` and `pullbackTensorComparison_rightUnitor`: **the
  comparison of Stacks 01CD is compatible with the two unitors of Tag 01CA**, the unit object
  being matched by `pullbackUnitComparison`.

## Implementation notes

**One spelling per statement, and `tmul` is what makes it possible.**
`(Stacks.RingedSpace.tensorSheaf Z).obj (A, B)` and `A ⊗ B` are equal by `rfl` and are not
syntactically equal, and a term mixing them — such as `pullbackUnit f (A ⊗ B) U
((tensorSheafUnit A B).app U (a ⊗ₜ b))` — is not type-correct at `implicit` transparency, so
`rw` and `simp` refuse any goal containing it, reporting a pattern rather than the cause. The
cure prescribed in this directory is a `def` with an **ascribed** type: `tmul` is the pure
tensor ascribed at `(A ⊗ B).val.obj U`, every statement below is written with it, and the
crossing happens once per lemma inside a proof given by `:=` or `exact`, which are
defeq-tolerant. The section formulas of `Stacks.TensorSheafWorld` are re-exported at `tmul` for
exactly this reason; they are the same theorems, not new ones.

**Why the unitor statements mention `unitComparison`.** The unit object of Tag 01CA is the
structure sheaf read as a module over itself, and `f^*` does not send it to the unit object on
the nose: the comparison is `Stacks.PullbackAlgebra.unitComparison`, invertible because `f⁻¹` is
a final functor on open subsets. So the unit coherence of `f^*` is a statement about the pair
(`pullbackTensorComparison`, `unitComparison`), as it must be.

**Universes.** Everything is at a single universe `u`, forced by
`RingedSpaceModuleAdjunction.modulePullback`, which exists only for `RingedSpace.{u, u}` with
modules in `u`. Nothing is narrowed relative to the imports.

**A second monoidal structure on `f^*`, and the dedup it owes.**
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` already makes `f^*` monoidal, through the
monoidal structure of the localization. `pullbackComparisonMonoidal` is a *different datum* for
the same functor: its tensorator is `Stacks.RingedSpace.comparison` on the nose, which is what
gives it a formula on local sections (`pullbackTensorComparison_pullbackUnit`) and hence what
makes a graded algebra built on it usable. The two structures agree: their unit morphisms are
identified by `Stacks.PullbackStrictUnit.epsilon_pullbackFunctor` and their tensorators by
`Stacks.PullbackStrictTensorator.delta_pullbackStrictMonoidal_eq`. **Neither structure is
registered as a global instance**, so that instance search never chooses between them; with the
identification proved, the two graded-algebra structures on `f^*A` collapse to one, and this
file's `def` is owed deletion in favour of the older one.

**No `@[stacks]` attribute.** Tag 01CD is already carried by `Stacks.RingedSpace.comparisonIso`
and Tag 01CA by the monoidal structure consumed here; the statements below are coherence
properties of those two results, not new results, so tagging them would register one result
twice.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace PresheafOfModules

open scoped TensorProduct

universe u

namespace Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### Pure tensors of local sections, at the monoidal spelling -/

section Sections

variable (Z : RingedSpace.{u, u})

/-- **The pure tensor of two local sections**, as a local section of the tensor product sheaf,
with its type ascribed at the monoidal spelling `(A ⊗ B).val.obj U` rather than at the tensor
bifunctor spelling of `PresheafOfModules.tensorSheafUnit`. The two are definitionally equal; the
ascription is what lets `rw` be used in a goal mentioning it. -/
noncomputable def tmul (A B : SheafOfModules.{u} (structureRingSheaf Z))
    (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) : (A ⊗ B).val.obj U :=
  (tensorSheafUnit A B).app U (a ⊗ₜ b)

variable {Z}
variable {A B D Q : SheafOfModules.{u} (structureRingSheaf Z)}

/-- **Two morphisms out of a tensor product sheaf which agree on the local pure tensors are
equal.** -/
theorem tensor_hom_ext {φ ψ : A ⊗ B ⟶ Q}
    (h : ∀ (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      φ.val.app U (tmul Z A B U a b) = ψ.val.app U (tmul Z A B U a b)) :
    φ = ψ :=
  PresheafOfModules.tensorSheaf_hom_ext (Osharp := Z.sheaf) (F := A) (G := B) (Q := Q) h

/-- **Two morphisms out of a twice-iterated tensor product sheaf which agree on the local triple
pure tensors are equal.** -/
theorem tensor_hom_ext₂ {φ ψ : (A ⊗ B) ⊗ D ⟶ Q}
    (h : ∀ (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U),
      φ.val.app U (tmul Z (A ⊗ B) D U (tmul Z A B U a b) d) =
        ψ.val.app U (tmul Z (A ⊗ B) D U (tmul Z A B U a b) d)) :
    φ = ψ :=
  PresheafOfModules.tensorSheaf_hom_ext₂ (Osharp := Z.sheaf) (F := A) (G := B) (H := D)
    (Q := Q) h

/-- The inverse of an invertible morphism of sheaves of modules undoes it on local sections. -/
theorem inv_val_app_apply {M N : SheafOfModules.{u} (structureRingSheaf Z)} (θ : M ⟶ N)
    [IsIso θ] (U : (Opens Z.carrier)ᵒᵖ) (x : M.val.obj U) :
    (inv θ).val.app U (θ.val.app U x) = x :=
  Stacks.SheafOfModules.inv_val_app_hom_val_app (asIso θ) U x

/-- An invertible morphism of sheaves of modules undoes its inverse on local sections. -/
theorem val_app_inv_val_app {M N : SheafOfModules.{u} (structureRingSheaf Z)} (θ : M ⟶ N)
    [IsIso θ] (U : (Opens Z.carrier)ᵒᵖ) (y : N.val.obj U) :
    θ.val.app U ((inv θ).val.app U y) = y :=
  Stacks.SheafOfModules.hom_val_app_inv_val_app (asIso θ) U y

/-- Right whiskering on a local pure tensor. -/
theorem whiskerRight_tmul {A' : SheafOfModules.{u} (structureRingSheaf Z)} (u : A ⟶ A')
    (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (u ▷ B).val.app U (tmul Z A B U a b) = tmul Z A' B U (u.val.app U a) b :=
  Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Z.sheaf
    (structureSheafRing Z).property U u B a b

/-- Left whiskering on a local pure tensor. -/
theorem whiskerLeft_tmul {B' : SheafOfModules.{u} (structureRingSheaf Z)} (v : B ⟶ B')
    (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (A ◁ v).val.app U (tmul Z A B U a b) = tmul Z A B' U a (v.val.app U b) :=
  Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Z.sheaf
    (structureSheafRing Z).property U A v a b

/-- The tensor product of two morphisms on a local pure tensor. -/
theorem tensorHom_tmul {A' B' : SheafOfModules.{u} (structureRingSheaf Z)} (u : A ⟶ A')
    (v : B ⟶ B') (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (u ⊗ₘ v).val.app U (tmul Z A B U a b) =
      tmul Z A' B' U (u.val.app U a) (v.val.app U b) := by
  rw [MonoidalCategory.tensorHom_def, SheafOfModules.comp_val_app_apply, whiskerRight_tmul,
    whiskerLeft_tmul]

/-- The associator of Tag 01CA on a local triple pure tensor. -/
theorem associator_hom_tmul (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U)
    (d : D.val.obj U) :
    (α_ A B D).hom.val.app U (tmul Z (A ⊗ B) D U (tmul Z A B U a b) d) =
      tmul Z A (B ⊗ D) U a (tmul Z B D U b d) :=
  Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Z.sheaf
    (structureSheafRing Z).property A B D U a b d

/-- The left unitor of Tag 01CA on a local pure tensor. -/
theorem leftUnitor_hom_tmul (U : (Opens Z.carrier)ᵒᵖ)
    (r : (structureRingSheaf Z).obj.obj U) (b : B.val.obj U) :
    (λ_ B).hom.val.app U
        (tmul Z (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) B U r b) = r • b :=
  Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Z.sheaf
    (structureSheafRing Z).property B U r b

/-- The right unitor of Tag 01CA on a local pure tensor. -/
theorem rightUnitor_hom_tmul (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U)
    (r : (structureRingSheaf Z).obj.obj U) :
    (ρ_ A).hom.val.app U
        (tmul Z A (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) U a r) = r • a :=
  Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit Z.sheaf
    (structureSheafRing Z).property A U a r

/-- **The unit local section of the unit object** `𝟙_` of Tag 01CA: the section `1` of the
structure sheaf, with its type ascribed at `(𝟙_ _).val.obj U`. The ascription is needed for the
same reason as for `tmul`, and here also because the numeral `1` does not elaborate at the
unascribed type: `OfNat` is not found through the unit object. -/
noncomputable def oneSec (W : RingedSpace.{u, u}) (U : (Opens W.carrier)ᵒᵖ) :
    (𝟙_ (SheafOfModules.{u} (structureRingSheaf W))).val.obj U :=
  (1 : (structureRingSheaf W).obj.obj U)

/-- **The global unit of a sheaf of graded algebras as a morphism out of the monoidal unit**,
i.e. `SheafOfModules.GradedAlgebra.oneHom` with its source ascribed at the `𝟙_` spelling of this
file's monoidal structure. -/
noncomputable def oneMorphism (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z)) :
    𝟙_ (SheafOfModules.{u} (structureRingSheaf Z)) ⟶ G.piece 0 :=
  SheafOfModules.GradedAlgebra.oneHom G

/-- The unit morphism of a sheaf of graded algebras carries the unit section to the global unit
of the algebra. -/
theorem oneMorphism_val_app_oneSec
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z))
    (U : (Opens Z.carrier)ᵒᵖ) :
    (oneMorphism G).val.app U (oneSec Z U) = G.one.eval U :=
  (SheafOfModules.GradedAlgebra.oneHom_val_app G U 1).trans (one_smul _ _)

/-- The global section of `G_0` that a morphism out of the monoidal unit corresponds to, read on
the unit section. -/
theorem unitHomEquiv_eval (M : SheafOfModules.{u} (structureRingSheaf Z))
    (h : 𝟙_ (SheafOfModules.{u} (structureRingSheaf Z)) ⟶ M) (U : (Opens Z.carrier)ᵒᵖ) :
    (M.unitHomEquiv h).eval U = h.val.app U (oneSec Z U) :=
  rfl

/-- **The multiplication of a sheaf of graded algebras as a morphism out of the monoidal
product**, i.e. `SheafOfModules.GradedAlgebra.mulSheaf` with its source ascribed at the `⊗`
spelling. As for `tmul`, the ascription is what makes a `rw` whose pattern mentions the source
of this morphism type-correct. -/
noncomputable def mulHom (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z))
    (i j : ℤ) : G.piece i ⊗ G.piece j ⟶ G.piece (i + j) :=
  SheafOfModules.GradedAlgebra.mulSheaf G i j

/-- The multiplication of a sheaf of graded algebras on a local pure tensor. -/
theorem mulHom_tmul (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z)) (i j : ℤ)
    (U : (Opens Z.carrier)ᵒᵖ) (x : (G.piece i).val.obj U) (y : (G.piece j).val.obj U) :
    (mulHom G i j).val.app U (tmul Z (G.piece i) (G.piece j) U x y) = (G.mul i j).app U x y :=
  SheafOfModules.GradedAlgebra.mulSheaf_unit G i j U x y

/-- **Associativity of the multiplication of a sheaf of graded algebras, as an equality of
morphisms**, read at `mulHom`. -/
theorem mulHom_assoc (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z))
    (i j k : ℤ) :
    mulHom G i j ▷ G.piece k ≫ mulHom G (i + j) k =
      (α_ (G.piece i) (G.piece j) (G.piece k)).hom ≫ G.piece i ◁ mulHom G j k ≫
        (mulHom G i (j + k) ≫ eqToHom (congrArg G.piece (add_assoc i j k).symm)) :=
  Stacks.TensorSheafWorld.mulSheaf_assoc Z.sheaf
    (structureSheafRing Z).property G i j k

/-- **The left unit law of a sheaf of graded algebras, as an equality of morphisms**, read at
`mulHom`. -/
theorem oneMorphism_mulHom (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z))
    (i : ℤ) :
    oneMorphism G ▷ G.piece i ≫ mulHom G 0 i =
      (λ_ (G.piece i)).hom ≫ eqToHom (congrArg G.piece (zero_add i).symm) :=
  SheafOfModules.GradedAlgebra.mulSheaf_one_mul G
    (structureSheafRing Z).property i

/-- **The right unit law of a sheaf of graded algebras, as an equality of morphisms**, read at
`mulHom`. -/
theorem mulHom_oneMorphism (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z))
    (i : ℤ) :
    G.piece i ◁ oneMorphism G ≫ mulHom G i 0 =
      (ρ_ (G.piece i)).hom ≫ eqToHom (congrArg G.piece (add_zero i).symm) :=
  SheafOfModules.GradedAlgebra.mulSheaf_mul_one G
    (structureSheafRing Z).property i

end Sections

/-! ### Extensionality for morphisms out of a pullback -/

section Pullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Two morphisms out of a pullback that agree on the pullback-unit images of local sections
are equal.** The pullback-unit images do not exhaust the sections of `f^*M`; what makes this
work is that they determine the adjoint transpose, which determines the morphism. -/
theorem pullback_hom_ext {M : SheafOfModules.{u} (structureRingSheaf Y)}
    {N : SheafOfModules.{u} (structureRingSheaf X)}
    {θ₁ θ₂ : (pullbackFunctor f).obj M ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (x : M.val.obj U),
      θ₁.val.app ((opensMap f).op.obj U) (pullbackUnit f M U x) =
        θ₂.val.app ((opensMap f).op.obj U) (pullbackUnit f M U x)) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction f).homEquiv M N).injective ?_
  ext U x
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₁ U x).trans ((h U x).trans
    (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₂ U x).symm)

/-- **Two morphisms out of the pullback of a tensor product that agree on the pullback-unit
images of the local pure tensors are equal.** -/
theorem pullback_tensor_hom_ext {A B : SheafOfModules.{u} (structureRingSheaf Y)}
    {N : SheafOfModules.{u} (structureRingSheaf X)}
    {θ₁ θ₂ : (pullbackFunctor f).obj (A ⊗ B) ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      θ₁.val.app ((opensMap f).op.obj U) (pullbackUnit f (A ⊗ B) U (tmul Y A B U a b)) =
        θ₂.val.app ((opensMap f).op.obj U) (pullbackUnit f (A ⊗ B) U (tmul Y A B U a b))) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction f).homEquiv (A ⊗ B) N).injective ?_
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Y.sheaf) (F := A) (G := B)
    (Q := (pushforwardFunctor f).obj N) fun U a b ↦ ?_
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₁ U _).trans
    ((h U a b).trans (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₂ U _).symm)

/-- **Two morphisms out of the pullback of a twice-iterated tensor product that agree on the
pullback-unit images of the local triple pure tensors are equal.** -/
theorem pullback_tensor_hom_ext₂ {A B D : SheafOfModules.{u} (structureRingSheaf Y)}
    {N : SheafOfModules.{u} (structureRingSheaf X)}
    {θ₁ θ₂ : (pullbackFunctor f).obj ((A ⊗ B) ⊗ D) ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U),
      θ₁.val.app ((opensMap f).op.obj U)
          (pullbackUnit f ((A ⊗ B) ⊗ D) U (tmul Y (A ⊗ B) D U (tmul Y A B U a b) d)) =
        θ₂.val.app ((opensMap f).op.obj U)
          (pullbackUnit f ((A ⊗ B) ⊗ D) U (tmul Y (A ⊗ B) D U (tmul Y A B U a b) d))) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction f).homEquiv ((A ⊗ B) ⊗ D) N).injective ?_
  refine PresheafOfModules.tensorSheaf_hom_ext₂ (Osharp := Y.sheaf) (F := A) (G := B) (H := D)
    (Q := (pushforwardFunctor f).obj N) fun U a b d ↦ ?_
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₁ U _).trans
    ((h U a b d).trans (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₂ U _).symm)

/-! ### The comparison of Stacks 01CD at the monoidal spelling -/

variable (A B D : SheafOfModules.{u} (structureRingSheaf Y))

/-- **The canonical comparison of Stacks 01CD**, `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B`, with source and
target spelled through the monoidal product of Tag 01CA. -/
noncomputable def pullbackTensorComparison :
    (pullbackFunctor f).obj (A ⊗ B) ⟶
      (pullbackFunctor f).obj A ⊗ (pullbackFunctor f).obj B :=
  comparison f A B

/-- The comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` is an isomorphism. -/
instance isIso_pullbackTensorComparison : IsIso (pullbackTensorComparison f A B) :=
  Stacks.PullbackTensor.isIso_comparison f A B

/-- **The comparison of Stacks 01CD on a local pure tensor**: it carries the pullback-unit image
of the pure tensor `a ⊗ b` to the pure tensor of the two pullback-unit images. -/
theorem pullbackTensorComparison_pullbackUnit (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U)
    (b : B.val.obj U) :
    (pullbackTensorComparison f A B).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A ⊗ B) U (tmul Y A B U a b)) =
      tmul X ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B) ((opensMap f).op.obj U)
        (pullbackUnit f A U a) (pullbackUnit f B U b) :=
  Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul f A B U a b

/-- **The comparison `f^*𝒪_Y ⟶ 𝒪_X`** of `Stacks.PullbackAlgebra.unitComparison`, retyped so
that its source and target are spelled with the unit object `𝟙_` of the monoidal structure of
Tag 01CA rather than with `SheafOfModules.unit`. -/
noncomputable def pullbackUnitComparison :
    (pullbackFunctor f).obj (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) ⟶
      𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) :=
  Stacks.PullbackAlgebra.unitComparison f

/-- The comparison `f^*𝒪_Y ⟶ 𝒪_X` is an isomorphism. -/
instance isIso_pullbackUnitComparison : IsIso (pullbackUnitComparison f) :=
  Stacks.PullbackAlgebra.isIso_unitComparison f

/-- The structure-sheaf comparison carries the pullback-unit image of a local section `r` of
`𝒪_Y` to its image `f^♯(r)` under the structure morphism of `f`. -/
theorem pullbackUnitComparison_pullbackUnit (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureRingSheaf Y).obj.obj U) :
    (pullbackUnitComparison f).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) U r) = sharp f U r :=
  Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f U r

/-- The structure morphism of `f` preserves the unit section. -/
theorem sharp_one (U : (Opens Y.carrier)ᵒᵖ) :
    sharp f U 1 = (1 : (structureRingSheaf X).obj.obj ((opensMap f).op.obj U)) :=
  map_one _

/-- The structure-sheaf comparison carries the pullback-unit image of the unit section to the
unit section. -/
theorem pullbackUnitComparison_oneSec (U : (Opens Y.carrier)ᵒᵖ) :
    (pullbackUnitComparison f).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) U (oneSec Y U)) =
      oneSec X ((opensMap f).op.obj U) :=
  (pullbackUnitComparison_pullbackUnit f U 1).trans (sharp_one f U)

/-! ### Naturality in each variable -/

variable {A B D}

/-- **Naturality of the comparison in the first variable**, in whiskered form. -/
theorem pullbackTensorComparison_naturality_left
    {A' : SheafOfModules.{u} (structureRingSheaf Y)} (u : A ⟶ A') :
    (pullbackFunctor f).map (u ▷ B) ≫ pullbackTensorComparison f A' B =
      pullbackTensorComparison f A B ≫ ((pullbackFunctor f).map u ▷ (pullbackFunctor f).obj B) :=
  pullback_tensor_hom_ext f fun U a b ↦ by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackUnit_naturality, whiskerRight_tmul, pullbackTensorComparison_pullbackUnit,
      pullbackTensorComparison_pullbackUnit, whiskerRight_tmul, pullbackUnit_naturality]

/-- **Naturality of the comparison in the second variable**, in whiskered form. -/
theorem pullbackTensorComparison_naturality_right
    {B' : SheafOfModules.{u} (structureRingSheaf Y)} (v : B ⟶ B') :
    (pullbackFunctor f).map (A ◁ v) ≫ pullbackTensorComparison f A B' =
      pullbackTensorComparison f A B ≫ ((pullbackFunctor f).obj A ◁ (pullbackFunctor f).map v) :=
  pullback_tensor_hom_ext f fun U a b ↦ by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackUnit_naturality, whiskerLeft_tmul, pullbackTensorComparison_pullbackUnit,
      pullbackTensorComparison_pullbackUnit, whiskerLeft_tmul, pullbackUnit_naturality]

/-! ### Compatibility with the associator and the unitors -/

variable (A B D)

/-- **The comparison of Stacks 01CD is compatible with the associator of Tag 01CA.** Both sides
are morphisms out of the pullback `f^*((A ⊗ B) ⊗ D)`, hence determined by their values on the
pullback-unit images of the local triple pure tensors, where the section formulas for the
comparison, the associator and the two whiskerings compute them to the same thing. -/
theorem pullbackTensorComparison_associator :
    (pullbackFunctor f).map (α_ A B D).hom ≫ pullbackTensorComparison f A (B ⊗ D) ≫
        ((pullbackFunctor f).obj A ◁ pullbackTensorComparison f B D) =
      pullbackTensorComparison f (A ⊗ B) D ≫
        (pullbackTensorComparison f A B ▷ (pullbackFunctor f).obj D) ≫
          (α_ ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)
            ((pullbackFunctor f).obj D)).hom :=
  pullback_tensor_hom_ext₂ f fun U a b d ↦ by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackUnit_naturality, associator_hom_tmul, pullbackTensorComparison_pullbackUnit,
      whiskerLeft_tmul, pullbackTensorComparison_pullbackUnit,
      pullbackTensorComparison_pullbackUnit, whiskerRight_tmul,
      pullbackTensorComparison_pullbackUnit, associator_hom_tmul]

/-- **The comparison of Stacks 01CD is compatible with the left unitor of Tag 01CA**, the unit
object being matched by `Stacks.PullbackAlgebra.unitComparison`. -/
theorem pullbackTensorComparison_leftUnitor :
    (pullbackFunctor f).map (λ_ A).hom =
      pullbackTensorComparison f (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) A ≫
        (pullbackUnitComparison f ▷ (pullbackFunctor f).obj A) ≫
          (λ_ ((pullbackFunctor f).obj A)).hom :=
  pullback_tensor_hom_ext f fun U r a ↦ by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackUnit_naturality]
    refine ((congrArg (pullbackUnit f A U) (leftUnitor_hom_tmul U r a)).trans
      (pullbackUnit_smul f A U r a)).trans ?_
    rw [pullbackTensorComparison_pullbackUnit, whiskerRight_tmul,
      pullbackUnitComparison_pullbackUnit f U r]
    exact (leftUnitor_hom_tmul _ _ _).symm

/-- **The comparison of Stacks 01CD is compatible with the right unitor of Tag 01CA**, the unit
object being matched by `Stacks.PullbackAlgebra.unitComparison`. -/
theorem pullbackTensorComparison_rightUnitor :
    (pullbackFunctor f).map (ρ_ A).hom =
      pullbackTensorComparison f A (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) ≫
        ((pullbackFunctor f).obj A ◁ pullbackUnitComparison f) ≫
          (ρ_ ((pullbackFunctor f).obj A)).hom :=
  pullback_tensor_hom_ext f fun U a r ↦ by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackUnit_naturality]
    refine ((congrArg (pullbackUnit f A U) (rightUnitor_hom_tmul U a r)).trans
      (pullbackUnit_smul f A U r a)).trans ?_
    rw [pullbackTensorComparison_pullbackUnit, whiskerLeft_tmul,
      pullbackUnitComparison_pullbackUnit f U r]
    exact (rightUnitor_hom_tmul _ _ _).symm

/-! ### The pullback as a monoidal functor with the comparison of Stacks 01CD as tensorator -/

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a monoidal
functor whose tensorator is the comparison of Stacks 01CD.** This is
`CategoryTheory.Functor.CoreMonoidal.mk'` applied to the two naturality statements and the three
coherences above; no coherence is discharged by automation that is not already proved here.

This is not the same *term* as `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, which is
obtained from the monoidal structure of the localization; but the two agree, and both halves of
that agreement are now proved. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit`
identifies the two *unit* morphisms, by transposing both along the adjunction `f^* ⊣ f_*`, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictTensorator` identifies the two
*tensorators*: `Stacks.PullbackStrictTensorator.delta_pullbackStrictMonoidal_eq`. That had to
wait for the localization tensorator to be computed on local sections, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite` does. A statement about
the multiplication of `f^*A` therefore no longer has to say which of the two structures it is
about, any more than a statement about its unit does. -/
@[ega "0 4.3.4" "εIso"]
noncomputable def pullbackCoreMonoidal : (pullbackFunctor f).CoreMonoidal :=
  Functor.CoreMonoidal.mk'
    (εIso := (asIso (pullbackUnitComparison f)).symm)
    (μIso := fun M N ↦ (asIso (pullbackTensorComparison f M N)).symm)
    (μIso_inv_natural_left := fun u N ↦
      (pullbackTensorComparison_naturality_left f (B := N) u).symm)
    (μIso_inv_natural_right := fun M v ↦
      (pullbackTensorComparison_naturality_right f (A := M) v).symm)
    (oplax_associativity := fun M N P ↦ (pullbackTensorComparison_associator f M N P).symm)
    (oplax_left_unitality := fun M ↦ by
      rw [← cancel_mono (λ_ ((pullbackFunctor f).obj M)).hom, Iso.inv_hom_id, Category.assoc,
        Category.assoc]
      simp only [Iso.symm_inv, asIso_hom]
      rw [← pullbackTensorComparison_leftUnitor, ← CategoryTheory.Functor.map_comp,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id])
    (oplax_right_unitality := fun M ↦ by
      rw [← cancel_mono (ρ_ ((pullbackFunctor f).obj M)).hom, Iso.inv_hom_id, Category.assoc,
        Category.assoc]
      simp only [Iso.symm_inv, asIso_hom]
      rw [← pullbackTensorComparison_rightUnitor, ← CategoryTheory.Functor.map_comp,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id])

/-- The monoidal functor structure on `f^*` whose tensorator is the comparison of Stacks 01CD.
Deliberately **not** a global instance: `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` is
a second `CategoryTheory.Functor.Monoidal` structure on the same functor, and registering both
would make instance search choose between them silently. -/
@[instance_reducible]
noncomputable def pullbackComparisonMonoidal : (pullbackFunctor f).Monoidal :=
  (pullbackCoreMonoidal f).toMonoidal

/-- The tensorator of `pullbackComparisonMonoidal` is the inverse of the comparison of Stacks
01CD, by construction. -/
theorem pullbackComparisonMonoidal_mu (M N : SheafOfModules.{u} (structureRingSheaf Y)) :
    Functor.LaxMonoidal.μ (self := (pullbackComparisonMonoidal f).toLaxMonoidal)
        (pullbackFunctor f) M N = inv (pullbackTensorComparison f M N) :=
  rfl

/-- The unit morphism of `pullbackComparisonMonoidal` is the inverse of the structure-sheaf
comparison, by construction. -/
theorem pullbackComparisonMonoidal_epsilon :
    Functor.LaxMonoidal.ε (self := (pullbackComparisonMonoidal f).toLaxMonoidal)
        (pullbackFunctor f) = inv (pullbackUnitComparison f) :=
  rfl

end Pullback

end Stacks.PullbackTensorCoherence

end
