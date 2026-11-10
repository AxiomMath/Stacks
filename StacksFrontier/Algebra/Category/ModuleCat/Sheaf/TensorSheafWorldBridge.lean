module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The tensor product bifunctor is the tensor product sheaf of Tag 05NA

The tensor product of sheaves of modules `Stacks.SheafOfModules.Tensor.sheafTensor Osharp` is a
bifunctor on sheaves of modules over the sheaf of rings `CategoryTheory.Sheaf.toRingCat J O♯`
underlying a sheaf of commutative rings; the graded-algebra machinery and the presentations of
symmetric and exterior powers are stated over it. The monoidal structure of Tag 01CA, whose
structural morphisms `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections`
computes on local sections, is stated over the sheaf of rings
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO` built from a presheaf of
commutative rings together with a sheaf condition.

**The two are the same construction, and this file records that they are equal by `rfl`** — on
the ring sheaf, on objects, on the morphism exhibiting the tensor product as a sheafification,
and (at the level of presheaves of modules) on morphisms. So nothing has to be transported
between the two, and the section formulas for the associator and the unitors of Tag 01CA are
restated here in the tensor-bifunctor spelling with `:=`, not along an isomorphism.

The remainder of the file is the infrastructure that identification unlocks. The multiplication
of a sheaf of graded algebras is recorded by `SheafOfModules.GradedAlgebra` as a bilinear map on
local sections, in each pair of degrees, with associativity an `HEq` between its values at
arbitrary local sections. Here it is turned into a morphism out of the tensor product sheaf in
two *general* degrees, `mulSheaf`, and that sectionwise associativity is turned into an equality
of morphisms, `mulSheaf_assoc`. The two inputs that makes possible are an extensionality
principle for a twice-iterated tensor product of sheaves of modules, `tensorSheaf_hom_ext₂`,
and the section formulas for the structural morphisms and the whiskerings of Tag 01CA, read in
the tensor-bifunctor spelling.

## Main definitions

* `Stacks.TensorSheafWorld.monoidalCategory`: the monoidal structure of Tag 01CA, named once at
  the `CategoryTheory.Sheaf.toRingCat` spelling of the ring sheaf so that instance resolution
  finds it there.
* `SheafOfModules.GradedAlgebra.mulPresheaf` and `SheafOfModules.GradedAlgebra.mulSheaf`:
  multiplication in degrees `i` and `j`, `A_i ⊗ A_j ⟶ A_{i+j}`, as a morphism out of the
  objectwise tensor product of the underlying presheaves of modules and as a morphism out of the
  tensor product sheaf.

## Main results

* `Stacks.TensorSheafWorld.structureSheaf_eq`,
  `Stacks.TensorSheafWorld.tensorSheafBifunctor_obj_eq`,
  `Stacks.TensorSheafWorld.tensorSheafUnit_eq` and
  `Stacks.TensorSheafWorld.tensorHom_eq_monoidalTensorHom`: **the bridge.** The two ring
  sheaves, the two tensor products on objects, the two sheafification units and the two tensor
  products of morphisms of presheaves of modules agree, each by `rfl`.
* `Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit`: the tensor product
  bifunctor on morphisms, computed on a local pure tensor.
* `Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit`,
  `Stacks.TensorSheafWorld.associator_inv_val_app_tensorSheafUnit`,
  `Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit` and
  `Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit`: the section formulas of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections` for the structural
  morphisms of Tag 01CA, in the tensor-bifunctor spelling.
* `Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit` and
  `Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit`: the same for the two
  whiskerings.
* `Stacks.TensorSheafWorld.heq_eqToHom_val_app`: transport of a degreewise family of sheaves of
  modules along an equality of degrees acts on local sections as the identity, up to `HEq`.
* `PresheafOfModules.tensorObj_hom_ext₂` and
  `PresheafOfModules.tensorObj_hom_ext_of_isLocallySurjective`: the two presheaf-level
  extensionality principles for a twice-iterated objectwise tensor product.
* `PresheafOfModules.tensorSheaf_hom_ext₂`: **a morphism out of `(F ⊗ G) ⊗ H` is determined by
  its values on the images of the triple pure tensors of local sections.** This is the two-level
  form of `PresheafOfModules.tensorSheaf_hom_ext`.
* `SheafOfModules.GradedAlgebra.mulSheaf_unit`: `mulSheaf` computes the product of two
  homogeneous local sections.
* `Stacks.TensorSheafWorld.mulSheaf_assoc`: **the multiplication of a sheaf of graded algebras
  is associative as an equality of morphisms out of `(A_i ⊗ A_j) ⊗ A_k`.** The structure
  `SheafOfModules.GradedAlgebra` states associativity only sectionwise, and a monoidal
  coherence argument cannot supply this: coherence is about the structural morphisms, and
  nothing identifies `mulSheaf` with any of them. The route is instead to evaluate both
  composites on a local pure tensor, using the section formulas for the associator and the
  whiskerings, and to appeal to `tensorSheaf_hom_ext₂` for the converse direction.

## Implementation notes

**What is forced.** Nothing here is a choice of mathematical definition: every object named is
already fixed, and most of the content is that two names denote one object. The only genuinely
new constructions are `mulSheaf`, which is forced by the multiplication of
`SheafOfModules.GradedAlgebra`, and the extensionality principles, which are forced by the
tensor product.

**Why `mulSheaf_assoc` has to be proved on sections.** Associativity of the *structural*
morphisms of a monoidal category is the pentagon, and Mathlib's `monoidal` tactic proves it.
That is of no use here: `SheafOfModules.GradedAlgebra.mul` is a `Stacks.BilinearMap` on local
sections and its `mul_assoc` field is an `HEq` between values at *arbitrary* local sections,
while the multiplication of a graded algebra is not a structural morphism of anything. The
bridge between the two levels is the section formula for the associator, which is why that had
to exist first; the statement is then assembled by evaluating both composites on the image of a
triple pure tensor and quoting `mul_assoc` there.

**What is chosen: one spelling per instance.**
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO` and
`CategoryTheory.Sheaf.toRingCat J O♯` are definitionally equal — `structureSheaf_eq` — but they
are different `DiscrTree` keys, so an instance declared for one is invisible at the other.
`Stacks.TensorSheafWorld.monoidalCategory` therefore names the monoidal structure of Tag 01CA
once, at the `toRingCat` spelling, taking the sheaf condition in the one form `Osharp` itself
determines, `(toRingCat J Osharp).property`; every argument of it is then recoverable from its
type, so it can be registered as a local instance, which
`Stacks.SheafOfModules.Strict.monoidalCategory` cannot be at this spelling. Because the sheaf
condition is a proposition, this is definitionally the structure for *any* proof `hO`, which is
why the section formulas below transfer by `:=`.

**The sheaf-level morphism identification is a heartbeat hazard.** The equality of morphisms
`((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map f).app G ≫
  ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F').map g =
(Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (f.val ⊗ₘ g.val)` is true
by `rfl` in the same sense as the others, and `rfl` *does not prove it*: it exhausts the
heartbeat budget in `whnf`, because the two sides present the sheafification functor through
different compositions and reduction descends into the sheafification rather than stopping at
the congruence. The presheaf-level half, `tensorHom_eq_monoidalTensorHom`, is `rfl` in
milliseconds, and `tensorSheafBifunctor_map_val_app_tensorSheafUnit` gives the value of the
sheaf-level morphism on a local pure tensor; with `PresheafOfModules.tensorSheaf_hom_ext` those
two determine the morphism, so no statement is lost and no limit is raised.

**Universes.** The bridge and the section formulas keep the site `C : Type u` with
`Category.{v} C` arbitrary and put the ring sheaf and the modules in a single universe `w`.
That is inherited, not narrowed: Mathlib's monoidal structure on presheaves of modules, and
hence everything about the associator of Tag 01CA, exists only in that form. The
graded-algebra multiplication and the extensionality principles, which involve no monoidal unit,
keep the module universe `a` free and independent of the ring universe `w`, exactly as
`Stacks.SheafOfModules.Tensor.sheafTensor` and `SheafOfModules.GradedAlgebra.generatorMul` do.
`tensorObj` of two presheaves of modules in universes `z` and `z₁` lands in `max z z₁`, so an
iterated tensor product forces its three arguments and its target into one universe; that is a
typing constraint of the construction, not a restriction imposed here. `mulSheaf_assoc` names
the associator, hence a monoidal unit, so there the graded pieces are back in `w`.

**Three spelling hazards, and what defeated them.** All three are instances of the pattern
already recorded in this area: `(A_i ⊗ A_j) ⊗ A_k` and
`((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
  (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A_i).obj A_j)).obj A_k` are
definitionally equal and not syntactically so, and a term that mixes them elaborates while the
unifier then struggles. (i) Applying `tensorSheaf_hom_ext₂` to a goal in the `⊗` spelling leaves
its four sheaf arguments as metavariables to be solved across that boundary, and `isDefEq` exhausts
its budget; passing all four explicitly turns the same check into a metavariable-free one that
succeeds at once. (ii) Assembling the right-hand composite as a single nested `congrArg` chain
reaches the recursion depth limit; the identical argument split into four `have`s with ascribed
types succeeds. (iii) No `rw` or `simp` appears in `mulSheaf_assoc`: every step is `Eq.trans` or
`congrArg`, because a rewrite across the boundary is not type-correct at `implicit` transparency.
No limit is raised anywhere.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — sheafification and
  tensor products.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v u w a

namespace Stacks.TensorSheafWorld

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

section Bridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
    Osharp.obj))

/-- **The sheaf of rings of Tag 05NA is the sheaf of rings underlying a sheaf of commutative
rings.** -/
theorem structureSheaf_eq : Stacks.SheafOfModules.TensorSheafification.structureSheaf Osharp.obj hO
  = toRingCat J Osharp := rfl

omit hO in
/-- **The objectwise tensor product of presheaves of modules is Mathlib's monoidal product**, on
morphisms. On objects this is `Stacks.TensorSheafDedup.presheafTensor_eq_monoidalTensorObj`
read through `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk`. -/
theorem tensorHom_eq_monoidalTensorHom
    {P P' Q Q' : PresheafOfModules.{w} (toRingCat J Osharp).obj} (u : P ⟶ P') (v : Q ⟶ Q') :
    PresheafOfModules.tensorHom u v = u ⊗ₘ v := rfl

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F G : SheafOfModules.{w} (toRingCat J Osharp))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The tensor product sheaf of Tag 05NA is the value of the tensor product bifunctor.** -/
theorem tensorSheafBifunctor_obj_eq [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (F G : SheafOfModules.{w} (toRingCat J Osharp)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G =
      (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G) := rfl

/-- **The two sheafification units agree**: the morphism exhibiting the value of the tensor
product bifunctor as a sheafification is the Tag 05NA unit of the monoidal product of the
underlying presheaves of modules. This is what lets the section formulas of Tag 01CA be read in
the tensor-bifunctor spelling. -/
theorem tensorSheafUnit_eq :
    tensorSheafUnit F G = Stacks.SheafOfModules.TensorSheafification.toSheafify Osharp.obj hO (F.val
      ⊗ G.val) := rfl

variable {F' G' : SheafOfModules.{w} (toRingCat J Osharp)}

omit hO in
/-- **The tensor product bifunctor on morphisms, computed on a local pure tensor.** -/
theorem tensorSheafBifunctor_map_val_app_tensorSheafUnit (f : F ⟶ F') (g : G ⟶ G') (V : Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map f).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).map g)).val.app V
        ((tensorSheafUnit F G).app V (x ⊗ₜ y)) =
      (tensorSheafUnit F' G').app V (f.val.app V x ⊗ₜ g.val.app V y) := by
  refine (PresheafOfModules.hom_congr_apply'
    (congrArg (SheafOfModules.forget
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).map
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Osharp f g)) V
    ((tensorSheafUnit F G).app V (x ⊗ₜ y))).trans ?_
  exact (unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
      (PresheafOfModules.tensorHom f.val g.val) V (x ⊗ₜ y)).trans
    (congrArg ((tensorSheafUnit F' G').app V)
      (PresheafOfModules.tensorHom_tmul f.val g.val V x y))

end Bridge

section Monoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The monoidal structure of Tag 01CA, named once at the `CategoryTheory.Sheaf.toRingCat`
spelling of the ring sheaf. Every argument is determined by the type, so this can be registered
as an instance; `Stacks.SheafOfModules.Strict.monoidalCategory` cannot be, at this spelling,
because the sheaf condition it takes is not recoverable from `toRingCat J Osharp`. -/
@[instance_reducible]
noncomputable def monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (toRingCat J Osharp)) :=
  Stacks.SheafOfModules.Strict.monoidalCategory Osharp.obj (toRingCat J Osharp).property

attribute [local instance] monoidalCategory

variable (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
  Osharp.obj))
  (M N P : SheafOfModules.{w} (toRingCat J Osharp)) (V : Cᵒᵖ)

include hO

/-- **The associator of Tag 01CA on local pure tensors**, in the tensor-bifunctor spelling. -/
theorem associator_hom_val_app_tensorSheafUnit
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (α_ M N P).hom.val.app V
        ((tensorSheafUnit (M ⊗ N) P).app V ((tensorSheafUnit M N).app V (m ⊗ₜ n) ⊗ₜ p)) =
      (tensorSheafUnit M (N ⊗ P)).app V (m ⊗ₜ (tensorSheafUnit N P).app V (n ⊗ₜ p)) :=
  Stacks.SheafOfModules.associator_hom_val_app_tmul Osharp.obj hO M N P V m n p

/-- **The inverse associator of Tag 01CA on local pure tensors**, in the tensor-bifunctor
spelling. -/
theorem associator_inv_val_app_tensorSheafUnit
    (m : M.val.obj V) (n : N.val.obj V) (p : P.val.obj V) :
    (α_ M N P).inv.val.app V
        ((tensorSheafUnit M (N ⊗ P)).app V (m ⊗ₜ (tensorSheafUnit N P).app V (n ⊗ₜ p))) =
      (tensorSheafUnit (M ⊗ N) P).app V ((tensorSheafUnit M N).app V (m ⊗ₜ n) ⊗ₜ p) :=
  Stacks.SheafOfModules.associator_inv_val_app_tmul Osharp.obj hO M N P V m n p

/-- **The left unitor of Tag 01CA on local pure tensors**, in the tensor-bifunctor spelling. -/
theorem leftUnitor_hom_val_app_tensorSheafUnit (r : (toRingCat J Osharp).obj.obj V)
    (m : M.val.obj V) :
    (λ_ M).hom.val.app V
        ((tensorSheafUnit (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp))) M).app V (r ⊗ₜ m)) =
      r • m :=
  Stacks.SheafOfModules.leftUnitor_hom_val_app_tmul Osharp.obj hO M V r m

/-- **The right unitor of Tag 01CA on local pure tensors**, in the tensor-bifunctor spelling. -/
theorem rightUnitor_hom_val_app_tensorSheafUnit (m : M.val.obj V)
    (r : (toRingCat J Osharp).obj.obj V) :
    (ρ_ M).hom.val.app V
        ((tensorSheafUnit M (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app V (m ⊗ₜ r)) =
      r • m :=
  Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul Osharp.obj hO M V m r

/-- A morphism of sheaves of modules which is the sheafification of a morphism `ψ` of presheaves
acts on the image of a local section `a` under the sheafification unit by acting as `ψ` on `a`. -/
private theorem val_app_unit_of_eq_sheafify_map
    {M₁ M₂ N₁ N₂ : SheafOfModules.{w} (toRingCat J Osharp)} (φ : M₁ ⊗ N₁ ⟶ M₂ ⊗ N₂)
    (ψ : M₁.val ⊗ N₁.val ⟶ M₂.val ⊗ N₂.val)
    (h : φ = (Stacks.SheafOfModules.TensorSheafification.sheafify Osharp.obj hO).map ψ)
    (a : (M₁.val ⊗ N₁.val).obj V) :
    φ.val.app V ((tensorSheafUnit M₁ N₁).app V a) = (tensorSheafUnit M₂ N₂).app V (ψ.app V a) :=
  (congrArg (fun φ : M₁ ⊗ N₁ ⟶ M₂ ⊗ N₂ ↦ φ.val.app V ((tensorSheafUnit M₁ N₁).app V a)) h).trans
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app Osharp.obj hO ψ V a)

/-- **Right whiskering of Tag 01CA on local pure tensors**, in the tensor-bifunctor spelling. -/
theorem whiskerRight_val_app_tensorSheafUnit {M M' : SheafOfModules.{w} (toRingCat J Osharp)}
    (f : M ⟶ M') (Z : SheafOfModules.{w} (toRingCat J Osharp)) (m : M.val.obj V)
    (z : Z.val.obj V) :
    (f ▷ Z).val.app V ((tensorSheafUnit M Z).app V (m ⊗ₜ z)) =
      (tensorSheafUnit M' Z).app V (f.val.app V m ⊗ₜ z) :=
  val_app_unit_of_eq_sheafify_map Osharp hO V _ _
    (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map Osharp.obj hO f Z) _

/-- **Left whiskering of Tag 01CA on local pure tensors**, in the tensor-bifunctor spelling. -/
theorem whiskerLeft_val_app_tensorSheafUnit (Z : SheafOfModules.{w} (toRingCat J Osharp))
    {M M' : SheafOfModules.{w} (toRingCat J Osharp)} (f : M ⟶ M') (z : Z.val.obj V)
    (m : M.val.obj V) :
    (Z ◁ f).val.app V ((tensorSheafUnit Z M).app V (z ⊗ₜ m)) =
      (tensorSheafUnit Z M').app V (z ⊗ₜ f.val.app V m) :=
  val_app_unit_of_eq_sheafify_map Osharp hO V _ _
    (Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map Osharp.obj hO Z f) _

end Monoidal

end Stacks.TensorSheafWorld

namespace PresheafOfModules

/-! ### Morphisms out of a twice-iterated tensor product -/

section IteratedHomExt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G H T Q : PresheafOfModules.{a} (O ⋙ forget₂ CommRingCat RingCat)}

/-- Two morphisms out of a twice-iterated objectwise tensor product of presheaves of modules
which agree on the triple pure tensors `(x ⊗ₜ y) ⊗ₜ z` of local sections are equal. This is the
two-level form of `PresheafOfModules.tensorObj_hom_ext`. -/
theorem tensorObj_hom_ext₂ {φ ψ : tensorObj (tensorObj F G) H ⟶ Q}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U) (z : H.obj U),
      Hom.app φ U ((x ⊗ₜ y) ⊗ₜ z) = Hom.app ψ U ((x ⊗ₜ y) ⊗ₜ z)) :
    φ = ψ :=
  hom_ext fun U ↦ ModuleCat.hom_ext (TensorProduct.ext_threefold (h U))

/-- Two morphisms out of `tensorObj T H` agreeing on the pure tensors `η (x ⊗ₜ y) ⊗ₜ z` are
equal, provided the target is separated and `η : tensorObj F G ⟶ T` is locally surjective. The
first variable is handled by `Stacks.BilinearMap.app_eq_of_isLocallySurjective`, which lifts the
agreement from the image of `η` to all of `T`, and the agreement on that image is
`tensorObj_hom_ext₂`. -/
theorem tensorObj_hom_ext_of_isLocallySurjective (hQ : Presheaf.IsSeparated J Q.presheaf)
    (η : tensorObj F G ⟶ T) [IsLocallySurjective J η] {φ ψ : tensorObj T H ⟶ Q}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U) (z : H.obj U),
      Hom.app φ U (Hom.app η U (x ⊗ₜ y) ⊗ₜ z) = Hom.app ψ U (Hom.app η U (x ⊗ₜ y) ⊗ₜ z)) :
    φ = ψ := by
  have key : ofBilinear ((toBilinear φ).compLeft η) = ofBilinear ((toBilinear ψ).compLeft η) :=
    tensorObj_hom_ext₂ fun U x y z ↦
      (ofBilinear_tmul ((toBilinear φ).compLeft η) U (x ⊗ₜ y) z).trans
        ((h U x y z).trans (ofBilinear_tmul ((toBilinear ψ).compLeft η) U (x ⊗ₜ y) z).symm)
  refine tensorObj_hom_ext fun U t z ↦ ?_
  exact Stacks.BilinearMap.app_eq_of_isLocallySurjective hQ η (toBilinear φ) (toBilinear ψ)
    (fun X x y ↦ (ofBilinear_tmul _ X x y).symm.trans
      ((congrArg (fun ϑ ↦ Hom.app ϑ X (x ⊗ₜ y)) key).trans (ofBilinear_tmul _ X x y))) U t z

end IteratedHomExt

section TensorSheafIteratedHomExt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {F G H Q : SheafOfModules.{a} (toRingCat J Osharp)}

/-- **Two morphisms out of a twice-iterated tensor product of sheaves of modules which agree on
the images of the triple pure tensors of local sections are equal.** This is the two-level form
of `PresheafOfModules.tensorSheaf_hom_ext`.

The sections of the shape `η (η (x ⊗ₜ y) ⊗ₜ z)` do not exhaust `((F ⊗ G) ⊗ H)(U)`, and the
two levels are handled differently. The outer one is sheafification, which
`tensorSheaf_hom_ext` already reduces away; the inner one is local surjectivity of
`tensorSheafUnit F G`, which is `tensorObj_hom_ext_of_isLocallySurjective`. -/
theorem tensorSheaf_hom_ext₂
    {φ ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G)).obj H ⟶ Q}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) (z : H.val.obj U),
      φ.val.app U ((tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj
          G)
          H).app U ((tensorSheafUnit F G).app U (x ⊗ₜ y) ⊗ₜ z)) =
        ψ.val.app U ((tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj
            G)
          H).app U ((tensorSheafUnit F G).app U (x ⊗ₜ y) ⊗ₜ z))) :
    φ = ψ := by
  have : IsLocallySurjective J (tensorSheafUnit F G) :=
    isLocallySurjective_sheafificationAdjunction_unit_app (𝟙 (toRingCat J Osharp).obj)
      (tensorObj F.val G.val)
  refine tensorSheaf_hom_ext fun U t z ↦ ?_
  exact hom_congr_apply' (tensorObj_hom_ext_of_isLocallySurjective Q.isSheaf.isSeparated
    (tensorSheafUnit F G)
    (φ := tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G) H ≫
        φ.val)
    (ψ := tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G) H ≫
        ψ.val)
    h) U (t ⊗ₜ z)

end TensorSheafIteratedHomExt

end PresheafOfModules

namespace SheafOfModules.GradedAlgebra

/-! ### Multiplication of a sheaf of graded algebras in two general degrees -/

section Mul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  (A : GradedAlgebra.{w, a} (toRingCat J Osharp))

/-- Multiplication in degrees `i` and `j`, `A_i ⊗ A_j ⟶ A_{i+j}`, as a morphism out of the
objectwise tensor product of the underlying presheaves of modules. -/
noncomputable def mulPresheaf (i j : ℤ) :
    tensorObj (A.piece i).val (A.piece j).val ⟶ (A.piece (i + j)).val :=
  PresheafOfModules.ofBilinear (A.mul i j)

/-- On local sections, `mulPresheaf A i j` sends `x ⊗ₜ y` to the product
`(A.mul i j).app U x y`. -/
@[simp]
theorem mulPresheaf_tmul (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    PresheafOfModules.Hom.app (mulPresheaf A i j) U (x ⊗ₜ y) = (A.mul i j).app U x y :=
  PresheafOfModules.ofBilinear_tmul (A.mul i j) U x y

variable [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- **Multiplication in degrees `i` and `j`, `A_i ⊗ A_j ⟶ A_{i+j}`, as a morphism of sheaves of
modules out of the tensor product sheaf.** The multiplication of a sheaf of graded algebras is
given on local sections, as a bilinear map; this is the morphism out of the tensor product
sheaf that it descends to. `SheafOfModules.GradedAlgebra.generatorMul` is the special case in
which the first degree is `1` and the first factor is pulled back along a degree-one
generator. -/
noncomputable def mulSheaf (i j : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A.piece i)).obj (A.piece j) ⟶ A.piece (i
        + j) :=
  tensorSheafDesc (mulPresheaf A i j)

/-- On the image of a local section `x ⊗ₜ y` under the sheafification unit, `mulSheaf A i j` is
the product `(A.mul i j).app U x y`. -/
@[simp]
theorem mulSheaf_unit (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    (mulSheaf A i j).val.app U
        ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) = (A.mul i j).app U x y :=
  (tensorSheafDesc_unit (mulPresheaf A i j) U x y).trans (mulPresheaf_tmul A i j U x y)

end Mul

end SheafOfModules.GradedAlgebra


namespace Stacks.TensorSheafWorld

/-! ### Associativity of the multiplication of a sheaf of graded algebras -/

section Assoc

open SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}}

/-- Transport of a degreewise family of sheaves of modules along an equality of degrees acts on
local sections as the identity, up to `HEq`. -/
theorem heq_eqToHom_val_app (Y : ℤ → SheafOfModules.{a} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (y : (Y i).val.obj U) :
    HEq ((eqToHom (congrArg Y h)).val.app U y) y := by
  subst h; rfl

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory

variable (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
  Osharp.obj))
  (A : SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp)) (i j k : ℤ)

include hO

/-- **The multiplication of a sheaf of graded algebras is associative as a morphism out of the
twice-iterated tensor product sheaf.** The structure `SheafOfModules.GradedAlgebra` records
associativity as an `HEq` between the values of its multiplication at *arbitrary* local
sections, which is weaker-looking than an equality of morphisms only because a morphism out of
a tensor product sheaf is not determined by its values on local pure tensors alone; the two are
equivalent, and `PresheafOfModules.tensorSheaf_hom_ext₂` is what makes them so. -/
theorem mulSheaf_assoc :
    MonoidalCategoryStruct.whiskerRight (C := SheafOfModules.{w} (toRingCat J Osharp))
        (mulSheaf A i j) (A.piece k) ≫ mulSheaf A (i + j) k =
      (α_ (A.piece i) (A.piece j) (A.piece k)).hom ≫ A.piece i ◁ mulSheaf A j k ≫
        mulSheaf A i (j + k) ≫ eqToHom (congrArg A.piece (add_assoc i j k).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext₂ (Osharp := Osharp) (F := A.piece i)
    (G := A.piece j) (H := A.piece k) (Q := A.piece (i + j + k)) fun U x y z ↦ ?_
  have hL : (MonoidalCategoryStruct.whiskerRight (C := SheafOfModules.{w} (toRingCat J Osharp))
        (mulSheaf A i j) (A.piece k) ≫ mulSheaf A (i + j) k).val.app U
        ((tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A.piece i)).obj
            (A.piece j)) (A.piece k)).app U
          ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y) ⊗ₜ z)) =
      (A.mul (i + j) k).app U ((A.mul i j).app U x y) z :=
    (congrArg ((mulSheaf A (i + j) k).val.app U)
        ((whiskerRight_val_app_tensorSheafUnit Osharp hO U (mulSheaf A i j) (A.piece k)
            ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) z).trans
          (congrArg (fun t ↦ (tensorSheafUnit (A.piece (i + j)) (A.piece k)).app U (t ⊗ₜ z))
            (mulSheaf_unit A i j U x y)))).trans
      (mulSheaf_unit A (i + j) k U ((A.mul i j).app U x y) z)
  have h1 : (α_ (A.piece i) (A.piece j) (A.piece k)).hom.val.app U
        ((tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A.piece i)).obj
            (A.piece j)) (A.piece k)).app U
          ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y) ⊗ₜ z)) =
      (tensorSheafUnit (A.piece i) (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A.piece
          j)).obj (A.piece k))).app U
        (x ⊗ₜ (tensorSheafUnit (A.piece j) (A.piece k)).app U (y ⊗ₜ z)) :=
    associator_hom_val_app_tensorSheafUnit Osharp hO (A.piece i) (A.piece j) (A.piece k) U x y z
  have h2 : (A.piece i ◁ mulSheaf A j k).val.app U
        ((tensorSheafUnit (A.piece i) (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
            (A.piece j)).obj (A.piece k))).app U
          (x ⊗ₜ (tensorSheafUnit (A.piece j) (A.piece k)).app U (y ⊗ₜ z))) =
      (tensorSheafUnit (A.piece i) (A.piece (j + k))).app U (x ⊗ₜ (A.mul j k).app U y z) :=
    (whiskerLeft_val_app_tensorSheafUnit Osharp hO U (A.piece i) (mulSheaf A j k) x
        ((tensorSheafUnit (A.piece j) (A.piece k)).app U (y ⊗ₜ z))).trans
      (congrArg (fun t ↦ (tensorSheafUnit (A.piece i) (A.piece (j + k))).app U (x ⊗ₜ t))
        (mulSheaf_unit A j k U y z))
  have h3 : (mulSheaf A i (j + k)).val.app U
        ((tensorSheafUnit (A.piece i) (A.piece (j + k))).app U
          (x ⊗ₜ (A.mul j k).app U y z)) =
      (A.mul i (j + k)).app U x ((A.mul j k).app U y z) :=
    mulSheaf_unit A i (j + k) U x ((A.mul j k).app U y z)
  have h4 : (A.mul (i + j) k).app U ((A.mul i j).app U x y) z =
      (eqToHom (congrArg A.piece (add_assoc i j k).symm)).val.app U
        ((A.mul i (j + k)).app U x ((A.mul j k).app U y z)) :=
    eq_of_heq ((A.mul_assoc i j k U x y z).trans
      (heq_eqToHom_val_app A.piece (add_assoc i j k).symm U
        ((A.mul i (j + k)).app U x ((A.mul j k).app U y z))).symm)
  refine hL.trans (h4.trans ?_)
  refine congrArg ((eqToHom (congrArg A.piece (add_assoc i j k).symm)).val.app U) ?_
  exact (h3.symm.trans (congrArg ((mulSheaf A i (j + k)).val.app U) h2.symm)).trans
    (congrArg (fun w ↦ (mulSheaf A i (j + k)).val.app U
      ((A.piece i ◁ mulSheaf A j k).val.app U w)) h1.symm)

end Assoc

end Stacks.TensorSheafWorld

end
