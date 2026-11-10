module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-!
# Two different factors of a product of sheaves of rings have vanishing tensor product

Let `R ≅ ∏_{i} factor i` be a sheaf of commutative rings presented as a product, and read each
`factor n` as a sheaf of `R`-modules through the `n`-th projection
(`Stacks.SheafOfModules.RingSheafProductFactor.factorModule`). For `n ≠ m` the tensor product
`factor n ⊗_R factor m` is the zero sheaf of `R`-modules.

This is the orthogonality `𝒪_n ⊗_{𝒪_X} 𝒪_m = 0` that the Stacks proof of `(2) ⟹ (1)` in
Tag 0FPG uses, and it is proved here on sections rather than from flatness of the factors: over
every object `U` of the site the element `e` of `R(U)` whose `n`-th component is `1` and whose
other components vanish acts as the identity on `factor n` and as zero on `factor m`, so every
pure tensor `a ⊗ b = (e • a) ⊗ b = a ⊗ (e • b) = 0`. The presheaf tensor product is therefore
already zero, and sheafification carries a zero object to a zero object.

## Main results

* `Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.exists_idempotentSection`:
  over every object of the site there is a section of `R` acting as the identity on the `n`-th
  factor and as zero on every other factor. This is the whole content of the vanishing.
* `Stacks.SheafOfModules.RingSheafProductFactor.isZero_presheafTensor_factorModule`: the presheaf
  tensor product of two different factors is zero.
* `Stacks.SheafOfModules.RingSheafProductFactor.isZero_sheafTensor_factorModule` and
  `isZero_tensorObj_factorModule`: the tensor product sheaf of two different factors is a zero
  object, at the bifunctor spelling `Stacks.SheafOfModules.Tensor.sheafTensor` and at the monoidal
  spelling `F ⊗ G` of `SheafOfModules.monoidalCategorySheafTensor`.

## Implementation notes

**Why the scalar action is handled through two private lemmas with every object a variable.** The
module of sections of `factorModule hp n` over `U` is a scalar restriction, so
`e • a` unfolds to `(π n)(e) • a` by `ModuleCat.restrictScalars.smul_def`, which is `rfl`. But the
goal written at the concrete sheaves is **not type-correct at `implicit` transparency**: the
carrier of the sections of `Stacks.SheafOfModules.Tensor.ringSheaf R` over `U` receives a `Ring`
instance through `RingCat` while the same carrier, read as the sections of `R`, receives one
through `CommRingCat`, and the two are not identified at that transparency. Every `rw` and
`simp only` on such a goal fails — `rw` reporting that it cannot find `?r • ?m` in a goal visibly
containing it. The two lemmas below state the one step needed with the two rings, the module and
the section all variables, where no such mixture occurs; applying them by `exact` costs a single
`isDefEq` at default transparency, which does cross the spelling.

**The vanishing is genuinely local.** The idempotents cutting out the factors are sections of `R`
over the objects of the site, not endomorphisms of `R`, so there is no argument at the level of
morphisms of sheaves: the proof has to descend to sections, and that is why it is written this
way.

`Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules` is the same criterion for
*sheaves* of modules; the presheaf form is needed here because the vanishing is established before
sheafification, and is stated below rather than there to keep this file's imports to the two it
needs.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose proof uses this vanishing.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TensorProduct

universe v u w t

noncomputable section

namespace Stacks.SheafOfModules.RingSheafProductFactor

/-- Scalar restriction along a ring morphism carrying `r` to `1`: then `r` acts as the identity.

Stated with both rings, the module and the section variables, so that it can be applied by
`exact` at a concrete sheaf of modules, where the goal is not type-correct at `implicit`
transparency and no rewriting tactic can act on it.

Public because
`Stacks.SheafOfModules.RingSheafProductFactor.presheafRetractRestrictScalars` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRetract` needs exactly this
step, in exactly this all-variables shape, and reuses it rather than declaring a second copy. -/
public theorem restrictScalars_smul_eq_self {A B : RingCat.{w}} (f : A ⟶ B)
    {M : ModuleCat.{w} B} (r : ↥A) (hr : f.hom r = 1)
    (m : ↥((ModuleCat.restrictScalars f.hom).obj M)) : r • m = m := by
  rw [ModuleCat.restrictScalars.smul_def, hr, one_smul]

/-- A scalar killed by a ring map acts as zero on a restriction of scalars along it. -/
public theorem _root_.ModuleCat.restrictScalars.smul_eq_zero_of_map_eq_zero {R : Type*}
    {S : Type*} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat S} (r : R) (hr : f r = 0)
    (m : (ModuleCat.restrictScalars f).obj M) : r • m = 0 := by
  rw [ModuleCat.restrictScalars.smul_def, hr, zero_smul]
  rfl

/-- **An element acting as the identity on one factor of a tensor product and as zero on the
other kills it.** Every pure tensor is `(e • a) ⊗ b = e • (a ⊗ b) = a ⊗ (e • b) = 0`, and the pure
tensors generate. -/
public theorem subsingleton_tensorProduct_of_smul {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {N : Type*} [AddCommGroup N] [Module A N]
    (e : A) (hM : ∀ m : M, e • m = m) (hN : ∀ n : N, e • n = 0) :
    Subsingleton (TensorProduct A M N) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [← hM a, TensorProduct.smul_tmul, hN b, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- A presheaf of modules all of whose modules of sections are trivial is a zero object. This is
the presheaf form of `Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections`. -/
public theorem isZero_presheaf_of_forall_subsingleton_sections {C : Type u} [Category.{v} C]
    {Rp : Cᵒᵖ ⥤ RingCat.{w}} (P : PresheafOfModules.{w} Rp)
    (h : ∀ U, Subsingleton ↥(P.obj U)) : IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (h U).elim _ _

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type t}
  {factor : ι → Sheaf J CommRingCat.{max u v}} {R : Sheaf J CommRingCat.{max u v}}
  (hp : ProductPresentation R factor)

/-- The morphism of sheaves of (not necessarily commutative) rings underlying the `n`-th
projection of a product presentation.  This is the morphism along which an `n`-th factor module
is read as an `R`-module, and `factorModule hp n` is its restriction of scalars applied to the
unit. -/
public def projRing (n : ι) : Tensor.ringSheaf R ⟶ Tensor.ringSheaf (factor n) :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map (hp.π n)

/-- `factorModule` is the restriction of scalars along `projRing` of the unit module. -/
public theorem factorModule_eq_restrictScalars_unit (n : ι) :
    factorModule hp n =
      (_root_.SheafOfModules.restrictScalars (projRing hp n)).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n))) :=
  rfl

namespace ProductPresentation

/-- **The idempotent cutting out the `n`-th factor, on sections, acting on arbitrary modules.**
Over every object `U` of the site there is a section of `R` which acts as the identity on the
sections of *every* module over the `n`-th factor and as zero on the sections of every module
over every other factor: the section with `n`-th component `1` and all other components zero.

The two properties depend only on the ring homomorphism `R(U) ⟶ (factor m)(U)` — on that it
carries the section to `1` for `m = n` and to `0` otherwise — and not on the module, which is why
one section serves all of them at once.  That is what makes the orthogonality below hold for
arbitrary modules and not only for the factors themselves.

Phrased as an existential rather than as a definition because the two properties are what every
consumer uses, and because stating them separately would force the section's type to be written
at a spelling instance search does not accept. -/
public theorem exists_idempotentSection_restrictScalars (n : ι) (U : Cᵒᵖ)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    ∃ e : ↥((Tensor.ringSheaf R).obj.obj U),
      (∀ a : ↥(((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L).val.obj U),
        e • a = a) ∧
      (∀ m : ι, m ≠ n → ∀ L' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor m)),
        ∀ b : ↥(((_root_.SheafOfModules.restrictScalars (projRing hp m)).obj L').val.obj U),
          e • b = 0) := by
  classical
  refine ⟨hp.inclSection n U 1, fun a => ?_, fun m hmn L' b => ?_⟩
  · exact restrictScalars_smul_eq_self _ _ (hp.app_inclSection_self n U 1) a
  · exact ModuleCat.restrictScalars.smul_eq_zero_of_map_eq_zero _ _
      (hp.app_inclSection_of_ne hmn U 1) b

/-- **The idempotent cutting out the `n`-th factor, on sections.** Over every object `U` of the
site there is a section of `R` which acts as the identity on the sections of the `n`-th factor and
as zero on those of every other factor: the section with `n`-th component `1` and all other
components zero.

This is `exists_idempotentSection_restrictScalars` at the unit modules. -/
public theorem exists_idempotentSection (n : ι) (U : Cᵒᵖ) :
    ∃ e : ↥((Tensor.ringSheaf R).obj.obj U),
      (∀ a : ↥((factorModule hp n).val.obj U), e • a = a) ∧
      (∀ m : ι, m ≠ n → ∀ b : ↥((factorModule hp m).val.obj U), e • b = 0) := by
  obtain ⟨e, h1, h2⟩ := hp.exists_idempotentSection_restrictScalars n U
    (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n)))
  exact ⟨e, h1, fun m hmn b =>
    h2 m hmn (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor m))) b⟩

end ProductPresentation

/-- **The presheaf tensor product of a module over one factor with a module over another
vanishes.** Over every object of the site the idempotent cutting out the `n`-th factor acts as
the identity on one tensor factor and as zero on the other, whatever the two modules are. -/
public theorem isZero_presheafTensor_restrictScalars {n m : ι} (hmn : m ≠ n)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n)))
    (L' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor m))) :
    IsZero ((((PresheafOfModules.tensorBifunctor (R).obj)).obj
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L).val).obj
      ((_root_.SheafOfModules.restrictScalars (projRing hp m)).obj L').val) := by
  refine isZero_presheaf_of_forall_subsingleton_sections _ fun U => ?_
  obtain ⟨e, h1, h2⟩ := hp.exists_idempotentSection_restrictScalars n U L
  exact subsingleton_tensorProduct_of_smul e h1 (h2 m hmn L')

/-- **The presheaf tensor product of two different factors vanishes.** This is
`isZero_presheafTensor_restrictScalars` at the unit modules. -/
public theorem isZero_presheafTensor_factorModule {n m : ι} (hmn : m ≠ n) :
    IsZero ((((PresheafOfModules.tensorBifunctor (R).obj)).obj (factorModule hp n).val).obj
      (factorModule hp m).val) :=
  isZero_presheafTensor_restrictScalars hp hmn
    (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n)))
    (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor m)))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- **The tensor product sheaf of a module over one factor with a module over another is a zero
object.** The presheaf tensor product is already zero and sheafification preserves zero
morphisms. -/
public theorem isZero_sheafTensor_restrictScalars {n m : ι} (hmn : m ≠ n)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n)))
    (L' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor m))) :
    IsZero (((Tensor.sheafTensor R).obj
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)).obj
      ((_root_.SheafOfModules.restrictScalars (projRing hp m)).obj L')) :=
  ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).map_isZero
    (isZero_presheafTensor_restrictScalars hp hmn L L')

/-- **The tensor product sheaf of two different factors is a zero object.** -/
public theorem isZero_sheafTensor_factorModule {n m : ι} (hmn : m ≠ n) :
    IsZero (((Tensor.sheafTensor R).obj (factorModule hp n)).obj (factorModule hp m)) :=
  isZero_sheafTensor_restrictScalars hp hmn
    (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n)))
    (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor m)))

/-- **The orthogonality of the factors for arbitrary modules, at the monoidal spelling.**
`L ⊗ L' = 0` in `Mod R` for `L` a module over `factor n`, `L'` a module over `factor m` and
`n ≠ m`, each read as an `R`-module along its projection and the tensor product being that of
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` on the nose.

This is the form the assembly of the implication `(2) ⟹ (1)` of Stacks 0FPG consumes: there the
two modules are the invertible `ℋ^n` and `(ℋ^m)^{-1}` of clause (2), not the factors
themselves. -/
public theorem isZero_tensorObj_restrictScalars {n m : ι} (hmn : m ≠ n)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n)))
    (L' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor m))) :
    letI := SheafOfModules.monoidalCategorySheafTensor R
    IsZero ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L ⊗
      (_root_.SheafOfModules.restrictScalars (projRing hp m)).obj L') :=
  isZero_sheafTensor_restrictScalars hp hmn L L'

/-- **The orthogonality of the factors, at the monoidal spelling.** `factor n ⊗ factor m = 0` in
`Mod R` for `n ≠ m`, the tensor product being that of
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` on the nose. -/
public theorem isZero_tensorObj_factorModule {n m : ι} (hmn : m ≠ n) :
    letI := SheafOfModules.monoidalCategorySheafTensor R
    IsZero (factorModule hp n ⊗ factorModule hp m) :=
  isZero_sheafTensor_factorModule hp hmn

end Stacks.SheafOfModules.RingSheafProductFactor

end

end
