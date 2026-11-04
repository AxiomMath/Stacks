module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DualBasisRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The dual sheaf is a left dual: the snake identities for the canonical pairing

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of rings
is a sheaf, and let `F` be a sheaf of `𝒪`-modules which is locally a direct summand of a finite
free sheaf of modules. [Stacks, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV) asserts that
the dual `F^∨ = SheafHom(F, 𝒪)`, together with the canonical evaluation `F^∨ ⊗ F ⟶ 𝒪` and the
canonical coevaluation `𝒪 ⟶ F ⊗ F^∨`, is a **left dual** of `F` in the monoidal category of
sheaves of `𝒪`-modules of Tag 01CA.

All four objects are already in this library: `Stacks.SheafOfModules.dualSheaf` and
`Stacks.SheafOfModules.evaluation` in `...Sheaf.SheafHom`,
`Stacks.SheafOfModules.coevaluation` in `...Sheaf.TensorDualEndomorphism`, and the monoidal
structure `Stacks.SheafOfModules.Strict.monoidalCategory` of `...Sheaf.MonoidalStrict`, whose
tensor product *is* the tensor product sheaf of Tag 05NA on the nose. What was missing is the
assertion itself: the two **snake identities** that make them an exact pairing. This file proves
them, and packages the result as a `CategoryTheory.ExactPairing`.

## Main definitions

* `Stacks.SheafOfModules.tensorPt`: a *local pure tensor* — the image under the sheafification
  unit of a pure tensor of local sections — as a section of the tensor product sheaf.
* `Stacks.SheafOfModules.exactPairingDualSheaf`: **the exact pairing** exhibiting `F^∨` as a left
  dual of `F`, with the canonical coevaluation and evaluation, from finite dual bases on a
  covering family.
* `Stacks.SheafOfModules.exactPairingDualSheafOfRetract`: the same with the local hypothesis in
  the form Stacks states it, a retract of `F|_{X k}` onto a finite free sheaf of modules.
* `Stacks.SheafOfModules.hasRightDualOfLocalDualBasis`: the same read as
  `CategoryTheory.HasRightDual F`, which is Mathlib's spelling of Stacks' "`F^∨` is a left dual
  of `F`".

## Main results

* `Stacks.SheafOfModules.evaluation_tensorPt`: **the canonical evaluation on a local pure
  tensor** is the value of the functional, i.e. `Stacks.SheafOfModules.evalSection`. This is the
  companion of
  `Stacks.SheafOfModules.tensorDualToEndomorphism_toTensorSheafSection`.
* `Stacks.SheafOfModules.coevaluation_app_eq_sum`: the canonical coevaluation at an arbitrary
  section `r` of the structure sheaf over an object carrying a finite dual basis is
  `∑ i, (r • eᵢ) ⊗ λᵢ`. This is the known value at `1` made linear.
* `Stacks.SheafOfModules.coevaluation_evaluation_tensorPt` and
  `evaluation_coevaluation_tensorPt`: **the two snake identities, read on a local pure tensor
  over an object carrying a finite dual basis.** These are where the mathematics happens: both
  reduce to the dual-basis identity `Stacks.SheafOfModules.FiniteDualBasis.coord_smul`,
  respectively `FiniteDualBasis.eq_sum_smul_lam`.
* `Stacks.SheafOfModules.hom_ext_of_coversTop_tensorPt`: two morphisms out of a tensor product
  sheaf agree as soon as they agree on the local pure tensors over the objects admitting a
  morphism into a member of a covering family. This is the localization step, and it is what
  turns the two displayed identities into identities of morphisms.
* `Stacks.SheafOfModules.coevaluation_evaluation_dualSheaf` and
  `evaluation_coevaluation_dualSheaf`: **the two snake identities themselves.**

## Implementation notes

**The route taken, and the route not taken.** Tag 0FNV's proof is local, and the obvious
formalization is to use `CategoryTheory.ExactPairing.ofJointlyFaithful` of
`StacksFrontier.CategoryTheory.Monoidal.RigidJointlyFaithful` with
the family of restrictions to a covering family: those are monoidal
(`...SliceRestrictionMonoidal.overFunctorMonoidal`) and jointly faithful
(`overFunctor_map_injective`), and over each member `F|_{X k}` is a finite free summand, so
`CategoryTheory.hasRightDualOfRetract` (Tag 0FFU) supplies an exact pairing there. That route
needs the *identification* of the pairing coming from the retract with the restriction of the
canonical one, and for that it needs the action of the restriction functor's tensorator on local
sections, which `...SliceRestrictionMonoidal` explicitly does not compute.

This file avoids that identification entirely: it proves the two snake identities **directly, on
local sections**, using the formulas for the associator and the unitors of Tag 01CA's monoidal
structure that `...Sheaf.TensorAssociatorSections` supplies. So neither
`CategoryTheory.ExactPairing.ofJointlyFaithful`, nor `CategoryTheory.hasRightDualOfRetract`, nor
`CategoryTheory.IsIdempotentComplete`, nor a right dual for the free sheaf of modules is used.
The locality that Stacks' proof gets from restricting to a cover is used here only through
`hom_ext_of_coversTop_tensorPt`, which is the sheaf condition for the target and nothing more.

**Where the localization sits.** A section of `F ⊗ F^∨` over an arbitrary object is not a local
pure tensor, and the coevaluation can only be computed over an object carrying a finite dual
basis. Both difficulties are handled in one place. Morphisms out of a tensor product sheaf, which
is a sheafification, correspond under the Tag 05NA adjunction to morphisms out of the *objectwise*
tensor product, where every section genuinely is a sum of pure tensors; and a morphism of
presheaves of modules into a sheaf is determined by its components over the objects admitting a
morphism into a member of a `GrothendieckTopology.CoversTop` family
(`presheaf_hom_ext_of_coversTop`, the section-level analogue of `overFunctor_map_injective`).
Composing the two reductions leaves exactly the pure-tensor statement over the objects where a
dual basis is available, by `FiniteDualBasis.restrict`.

**Local pure tensors are named.** `tensorPt 𝒪 h𝒪 A B V a b` is the image of `a ⊗ₜ b` under the
sheafification unit, with its type ascribed as a section of `A ⊗ B` for the monoidal structure of
Tag 01CA rather than of `Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 A B`. The two
  are definitionally equal and
`Stacks.SheafOfModules.toTensorSheafSection` of `...Sheaf.TensorDualEndomorphism` is the same
construction in the second spelling (`toTensorSheafSection_tmul` records that it is `rfl`);
naming the first fixes one spelling for every statement here, which is what keeps the chains below
free of rewriting across the transparency boundary.

**Why the proofs are `Eq.trans` chains and not `rw`.** The source of a whiskering such as
`coev ▷ F` is `𝟙_ ⊗ F` while `Stacks.SheafOfModules.whiskerRight_eq_sheafify_map` presents the
morphism as `(Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map (coev.val ▷ F.val)`,
  whose source is spelled
`(Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).obj (𝟙_.val ⊗ F.val)`. Those are
  definitionally equal and not
syntactically so, so after rewriting the morphism the goal is no longer type-correct at `implicit`
transparency and the next `rw` fails with a message naming a pattern. Every step here is therefore
a `congrArg`/`Eq.trans`/`exact`, which tolerate defeq. Two further points of the same
kind: `set Fd := dualSheaf 𝒪 h𝒪 F` makes the final defeq check of
`coevaluation_evaluation_tensorPt` exceed the recursion limit, and `tensorPt_sum_right` must have
its `A` and `B` named at the two call sites where the first argument is the section `1`, which
does not determine them — unnamed, it is a `whnf` timeout reported at a one-line application.

**Universes.** The site is `C : Type u` with `Category.{v} C` and the module universe is
`max u v`. This is the universe at which `Stacks.SheafOfModules.dualSheaf`,
`evaluation` and `coevaluation` are stated, and the reason is recorded in `...Sheaf.SheafHom`: the
internal hom of Tag 03EM lands in `PresheafOfModules.{max u v t}` for arguments in
`PresheafOfModules.{t}`, so `SheafHom(F, G)` is an object of the same category as `F` and `G` only
when `max u v ≤ t`, and Mathlib's monoidal structure on presheaves of modules forces the module
universe to equal the ring universe. Nothing here is narrowed relative to the imported files.

**Hypotheses.** `J.WEqualsLocallyBijective AddCommGrpCat` and `HasWeakSheafify J AddCommGrpCat`,
which is what the Tag 05NA sheafification functor and the tensor product sheaf need. No
`GrothendieckTopology.HasSheafCompose` instance is used: the variable
declared for it in `StacksDraft.Ch17.Sec16.Tag05NA` is not used by
  `Stacks.SheafOfModules.TensorSheafification.sheafify`, so it is
not a parameter of `tensorSheaf`, of `evaluation` or of anything below.
`exactPairingDualSheafOfRetract` additionally assumes the slice-site sheafification instances for
the members of the covering family, which is what `SheafOfModules.free` and
`Stacks.SheafOfModules.freeProj` need in order for its hypothesis to be stateable at all.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP) — left duals in a
  monoidal category, i.e. `CategoryTheory.ExactPairing`.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal structure.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — the tensor product
  sheaf as a sheafification.
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ) — the converse.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite SheafOfModules

open scoped TensorProduct

universe v u

namespace Stacks.SheafOfModules

attribute [local instance] Strict.monoidalCategory monoidalCategoryPresheafOfModules
  symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-! ### Local pure tensors -/

/-- **A local pure tensor.** The image under the Tag 05NA sheafification unit of a pure tensor of
local sections, read as a section of the tensor product `A ⊗ B` of the monoidal structure of
Tag 01CA. -/
noncomputable def tensorPt (A B : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (V : Cᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) : (A ⊗ B).val.obj V :=
  (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V (a ⊗ₜ b)

variable {A A' B B' : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-- `Stacks.SheafOfModules.toTensorSheafSection` on a pure tensor is a local pure tensor: the
two spellings of the construction agree on the nose. -/
lemma toTensorSheafSection_tmul (V : Cᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) :
    toTensorSheafSection 𝒪 h𝒪 A B V (a ⊗ₜ b) = tensorPt 𝒪 h𝒪 A B V a b := rfl

/-- Right whiskering on a local pure tensor acts on the first factor. -/
lemma tensorPt_whiskerRight (f : A ⟶ A') (V : Cᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) :
    (f ▷ B).val.app V (tensorPt 𝒪 h𝒪 A B V a b)
      = tensorPt 𝒪 h𝒪 A' B V (f.val.app V a) b :=
  (congrArg (fun φ : A ⊗ B ⟶ A' ⊗ B =>
      φ.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
        V (a ⊗ₜ b)))
    (whiskerRight_eq_sheafify_map 𝒪 h𝒪 f B)).trans
      (sheafify_map_toSheafify_app 𝒪 h𝒪 (f.val ▷ B.val) V (a ⊗ₜ b))

/-- Left whiskering on a local pure tensor acts on the second factor. -/
lemma tensorPt_whiskerLeft (g : B ⟶ B') (V : Cᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) :
    (A ◁ g).val.app V (tensorPt 𝒪 h𝒪 A B V a b)
      = tensorPt 𝒪 h𝒪 A B' V a (g.val.app V b) :=
  (congrArg (fun φ : A ⊗ B ⟶ A ⊗ B' =>
      φ.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
        V (a ⊗ₜ b)))
    (whiskerLeft_eq_sheafify_map 𝒪 h𝒪 A g)).trans
      (sheafify_map_toSheafify_app 𝒪 h𝒪 (A.val ◁ g.val) V (a ⊗ₜ b))

/-- A local pure tensor is homogeneous in its first factor. -/
lemma tensorPt_smul_left (V : Cᵒᵖ) (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).obj.obj V)
    (a : A.val.obj V) (b : B.val.obj V) :
    tensorPt 𝒪 h𝒪 A B V (r • a) b = r • tensorPt 𝒪 h𝒪 A B V a b :=
  ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V).hom.map_smul
    r (a ⊗ₜ b)

/-- A local pure tensor is homogeneous in its second factor. -/
lemma tensorPt_smul_right (V : Cᵒᵖ) (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  𝒪 h𝒪).obj.obj V)
    (a : A.val.obj V) (b : B.val.obj V) :
    tensorPt 𝒪 h𝒪 A B V a (r • b) = r • tensorPt 𝒪 h𝒪 A B V a b := by
  have h : (a ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V] (r •
    b))
      = r • (a ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V] b) :=
    TensorProduct.tmul_smul r a b
  exact (congrArg ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
    V) h).trans
    (((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app
      V).hom.map_smul r (a ⊗ₜ b))

/-- A pure tensor which is a sum of pure tensors in the objectwise tensor product gives the
corresponding sum of local pure tensors. -/
private lemma tensorPt_eq_sum_of_tmul_eq {V : Cᵒᵖ} {ι : Type*} (s : Finset ι) {a : A.val.obj V}
    {b : B.val.obj V} {a' : ι → A.val.obj V} {b' : ι → B.val.obj V}
    (h : (a ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V] b)
      = ∑ i ∈ s, (a' i ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪).obj.obj V] b' i)) :
    tensorPt 𝒪 h𝒪 A B V a b = ∑ i ∈ s, tensorPt 𝒪 h𝒪 A B V (a' i) (b' i) :=
  (congrArg ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app V)
    h).trans (map_sum ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
      (A.val ⊗ B.val)).app V).hom _ s)

/-- A local pure tensor is additive in its first factor. -/
lemma tensorPt_sum_left (V : Cᵒᵖ) {ι : Type*} (s : Finset ι) (a : ι → A.val.obj V)
    (b : B.val.obj V) :
    tensorPt 𝒪 h𝒪 A B V (∑ i ∈ s, a i) b = ∑ i ∈ s, tensorPt 𝒪 h𝒪 A B V (a i) b :=
  tensorPt_eq_sum_of_tmul_eq 𝒪 h𝒪 s (TensorProduct.sum_tmul s a b)

/-- A local pure tensor is additive in its second factor. -/
lemma tensorPt_sum_right (V : Cᵒᵖ) {ι : Type*} (s : Finset ι) (a : A.val.obj V)
    (b : ι → B.val.obj V) :
    tensorPt 𝒪 h𝒪 A B V a (∑ i ∈ s, b i) = ∑ i ∈ s, tensorPt 𝒪 h𝒪 A B V a (b i) :=
  tensorPt_eq_sum_of_tmul_eq 𝒪 h𝒪 s (TensorProduct.tmul_sum a s b)

/-! ### The structural morphisms of Tag 01CA on local pure tensors -/

/-- The associator of Tag 01CA on local pure tensors, in the `tensorPt` spelling. -/
lemma tensorPt_associator_hom
    (A B D : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) (V : Cᵒᵖ)
    (a : A.val.obj V) (b : B.val.obj V) (d : D.val.obj V) :
    (α_ A B D).hom.val.app V (tensorPt 𝒪 h𝒪 (A ⊗ B) D V (tensorPt 𝒪 h𝒪 A B V a b) d)
      = tensorPt 𝒪 h𝒪 A (B ⊗ D) V a (tensorPt 𝒪 h𝒪 B D V b d) :=
  associator_hom_val_app_tmul 𝒪 h𝒪 A B D V a b d

/-- The inverse associator of Tag 01CA on local pure tensors, in the `tensorPt` spelling. -/
lemma tensorPt_associator_inv
    (A B D : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) (V : Cᵒᵖ)
    (a : A.val.obj V) (b : B.val.obj V) (d : D.val.obj V) :
    (α_ A B D).inv.val.app V (tensorPt 𝒪 h𝒪 A (B ⊗ D) V a (tensorPt 𝒪 h𝒪 B D V b d))
      = tensorPt 𝒪 h𝒪 (A ⊗ B) D V (tensorPt 𝒪 h𝒪 A B V a b) d :=
  associator_inv_val_app_tmul 𝒪 h𝒪 A B D V a b d

/-- The left unitor of Tag 01CA on a local pure tensor, in the `tensorPt` spelling. -/
lemma tensorPt_leftUnitor_hom (V : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) (a : A.val.obj
      V) :
    (λ_ A).hom.val.app V
        (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) A V r a)
      = r • a :=
  leftUnitor_hom_val_app_tmul 𝒪 h𝒪 A V r a

/-- The right unitor of Tag 01CA on a local pure tensor, in the `tensorPt` spelling. -/
lemma tensorPt_rightUnitor_hom (V : Cᵒᵖ) (a : A.val.obj V)
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) :
    (ρ_ A).hom.val.app V
        (tensorPt 𝒪 h𝒪 A (𝟙_ (SheafOfModules.{max u v}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) V a r)
      = r • a :=
  rightUnitor_hom_val_app_tmul 𝒪 h𝒪 A V a r

/-- The inverse right unitor of Tag 01CA takes a local section to its local pure tensor with the
unit section. -/
lemma rightUnitor_inv_eq_tensorPt (V : Cᵒᵖ) (a : A.val.obj V) :
    (ρ_ A).inv.val.app V a
      = tensorPt 𝒪 h𝒪 A (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) V a
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) :=
  (congrArg ((ρ_ A).inv.val.app V)
      ((tensorPt_rightUnitor_hom 𝒪 h𝒪 V a 1).trans (one_smul _ a))).symm.trans
    (inv_val_app_hom_val_app (ρ_ A) V _)

/-- The inverse left unitor of Tag 01CA takes a local section to the local pure tensor of the
unit section with it. -/
lemma leftUnitor_inv_eq_tensorPt (V : Cᵒᵖ) (a : A.val.obj V) :
    (λ_ A).inv.val.app V a
      = tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) A V
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) a :=
  (congrArg ((λ_ A).inv.val.app V)
      ((tensorPt_leftUnitor_hom 𝒪 h𝒪 V 1 a).trans (one_smul _ a))).symm.trans
    (inv_val_app_hom_val_app (λ_ A) V _)

/-- A local pure tensor with a section of the structure sheaf in the second slot absorbs that
section as a scalar into the first. -/
lemma tensorPt_unit_right (A : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (V : Cᵒᵖ) (a : A.val.obj V) (s : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).obj.obj V) :
    tensorPt 𝒪 h𝒪 A (𝟙_ (SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) V a s
      = tensorPt 𝒪 h𝒪 A (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) V
          (s • a) (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V)
            := by
  have hs : (s : (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪)).val.obj V)
      = s • unitOne (S := Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) V :=
        toUnit_eq_smul V s
  refine Eq.trans (congrArg (tensorPt 𝒪 h𝒪 A
    (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
      V a) hs) ?_
  exact (tensorPt_smul_right 𝒪 h𝒪 V s a _).trans (tensorPt_smul_left 𝒪 h𝒪 V s a _).symm

/-- A local pure tensor with a section of the structure sheaf in the first slot absorbs that
section as a scalar into the second. -/
lemma tensorPt_unit_left (A : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (V : Cᵒᵖ) (s : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) (a :
      A.val.obj V) :
    tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) A V s a
      = tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) A V
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) (s • a)
            := by
  have hs : (s : (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪)).val.obj V)
      = s • unitOne (S := Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) V :=
        toUnit_eq_smul V s
  refine Eq.trans (congrArg (fun z :
      (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪))).val.obj V =>
      tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) A V z a)
    hs) ?_
  exact (tensorPt_smul_left 𝒪 h𝒪 V s _ a).trans (tensorPt_smul_right 𝒪 h𝒪 V s _ a).symm

/-! ### The canonical pairing on local pure tensors -/

/-- **The canonical evaluation pairing on a local pure tensor** is the value of the functional
on the section. This is the companion, for `Stacks.SheafOfModules.evaluation`, of the
section formula `Stacks.SheafOfModules.tensorDualToEndomorphism_toTensorSheafSection`. -/
lemma evaluation_tensorPt (F : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (V : Cᵒᵖ) (lam : (dualSheaf 𝒪 h𝒪 F).val.obj V) (x : F.val.obj V) :
    (evaluation 𝒪 h𝒪 F).val.app V (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) F V lam x)
      = evalSection 𝒪 F.val
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val
            V lam x :=
  congrArg (fun φ => φ.app V (lam ⊗ₜ x))
    (((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv
      ((PresheafOfModules.tensorObj (O := 𝒪) ((dualSheaf 𝒪 h𝒪 F).val) (F.val)))
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪))).apply_symm_apply
        (evaluationPresheaf 𝒪 h𝒪 F))

section Snake

variable (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪))
  {K : Type*} {X : K → C} (hX : J.CoversTop X) {I : K → Type*} [∀ k, Fintype (I k)]
  (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k))

/-- **The canonical coevaluation at an arbitrary section of the structure sheaf**, over an object
carrying a finite dual basis: it is `∑ i, (r • eᵢ) ⊗ λᵢ`. This is the value at `1`,
`Stacks.SheafOfModules.coevaluation_app_one_eq_sum_of_dualBasis`, made linear. -/
lemma coevaluation_app_eq_sum (U : C) {I' : Type*} [Fintype I']
    (c : FiniteDualBasis 𝒪 h𝒪 F U I')
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) :
    (coevaluation 𝒪 h𝒪 F hX b).val.app (op U) r
      = ∑ i : I', tensorPt 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U) (r • c.e i) (c.lam i) := by
  have hr : (r : (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪)).val.obj (op U))
      = r • unitOne (S := Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) (op U) :=
    toUnit_eq_smul (op U) r
  refine Eq.trans (congrArg ((coevaluation 𝒪 h𝒪 F hX b).val.app (op U)) hr) ?_
  refine Eq.trans (((coevaluation 𝒪 h𝒪 F hX b).val.app (op U)).hom.map_smul r _) ?_
  refine Eq.trans (congrArg (r • ·)
    (coevaluation_app_one_eq_sum_of_dualBasis 𝒪 h𝒪 F hX b U c)) ?_
  refine Eq.trans Finset.smul_sum (Finset.sum_congr rfl fun i _ => ?_)
  exact (tensorPt_smul_left 𝒪 h𝒪 (op U) r (c.e i) (c.lam i)).symm

/-- **The second snake identity on a local pure tensor**, over an object carrying a finite dual
basis. The computation is: the coevaluation expands as `∑ i, (r • eᵢ) ⊗ λᵢ`, the associator
re-brackets, the evaluation contracts `λᵢ` against `x`, and the resulting sum
`∑ i, λᵢ(x) • (r • eᵢ)` is `r • x` by the dual-basis identity. -/
lemma evaluation_coevaluation_tensorPt (U : C) {I' : Type*} [Fintype I']
    (c : FiniteDualBasis 𝒪 h𝒪 F U I')
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (x :
      F.val.obj (op U)) :
    (coevaluation 𝒪 h𝒪 F hX b ▷ F ≫ (α_ F (dualSheaf 𝒪 h𝒪 F) F).hom ≫
          F ◁ evaluation 𝒪 h𝒪 F).val.app (op U)
        (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) F
          (op U) r x)
      = ((λ_ F).hom ≫ (ρ_ F).inv).val.app (op U)
        (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) F
          (op U) r x) := by
  have hL1 : (coevaluation 𝒪 h𝒪 F hX b ▷ F).val.app (op U)
        (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) F
          (op U) r x)
      = ∑ i : I', tensorPt 𝒪 h𝒪 (F ⊗ dualSheaf 𝒪 h𝒪 F) F (op U)
          (tensorPt 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U) (r • c.e i) (c.lam i)) x :=
    (tensorPt_whiskerRight 𝒪 h𝒪 (coevaluation 𝒪 h𝒪 F hX b) (op U) r x).trans
      ((congrArg (fun z => tensorPt 𝒪 h𝒪 (F ⊗ dualSheaf 𝒪 h𝒪 F) F (op U) z x)
          (coevaluation_app_eq_sum 𝒪 h𝒪 F hX b U c r)).trans
        (tensorPt_sum_left 𝒪 h𝒪 (op U) Finset.univ _ x))
  have hL2 : ∀ i : I',
      (F ◁ evaluation 𝒪 h𝒪 F).val.app (op U)
        ((α_ F (dualSheaf 𝒪 h𝒪 F) F).hom.val.app (op U)
          (tensorPt 𝒪 h𝒪 (F ⊗ dualSheaf 𝒪 h𝒪 F) F (op U)
            (tensorPt 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U) (r • c.e i) (c.lam i)) x))
      = tensorPt 𝒪 h𝒪 F (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (op U) (dualEval (c.lam i) x • (r • c.e i))
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) :=
            by
    intro i
    refine Eq.trans (congrArg ((F ◁ evaluation 𝒪 h𝒪 F).val.app (op U))
      (tensorPt_associator_hom 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) F (op U)
        (r • c.e i) (c.lam i) x)) ?_
    refine Eq.trans
      (tensorPt_whiskerLeft 𝒪 h𝒪 (evaluation 𝒪 h𝒪 F) (op U) (r • c.e i) _) ?_
    refine Eq.trans (congrArg (tensorPt 𝒪 h𝒪 F
        (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪))) (op U) (r • c.e i))
      (evaluation_tensorPt 𝒪 h𝒪 F (op U) (c.lam i) x)) ?_
    exact tensorPt_unit_right 𝒪 h𝒪 F (op U) (r • c.e i) (dualEval (c.lam i) x)
  have hL : (F ◁ evaluation 𝒪 h𝒪 F).val.app (op U)
        ((α_ F (dualSheaf 𝒪 h𝒪 F) F).hom.val.app (op U)
          ((coevaluation 𝒪 h𝒪 F hX b ▷ F).val.app (op U)
            (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) F
              (op U) r x)))
      = tensorPt 𝒪 h𝒪 F (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (op U) (r • x) (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
            h𝒪).obj.obj (op U)) := by
    refine Eq.trans (congrArg (fun z => (F ◁ evaluation 𝒪 h𝒪 F).val.app (op U)
      ((α_ F (dualSheaf 𝒪 h𝒪 F) F).hom.val.app (op U) z)) hL1) ?_
    refine Eq.trans (map_sum (((F ◁ evaluation 𝒪 h𝒪 F).val.app (op U)).hom.comp
      ((α_ F (dualSheaf 𝒪 h𝒪 F) F).hom.val.app (op U)).hom) _ Finset.univ) ?_
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hL2 i) ?_
    refine Eq.trans (tensorPt_sum_left 𝒪 h𝒪 (A := F)
      (B := 𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        𝒪 h𝒪)))
      (op U) Finset.univ (fun i : I' => dualEval (c.lam i) x • (r • c.e i))
      (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))).symm ?_
    refine congrArg (fun z => tensorPt 𝒪 h𝒪 F
      (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪))) (op U) z
      (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))) ?_
    refine Eq.trans (Finset.sum_congr rfl fun i _ =>
      smul_comm (dualEval (c.lam i) x) r (c.e i)) ?_
    exact Finset.smul_sum.symm.trans (congrArg (r • ·) (c.coord_smul 𝒪 h𝒪 x))
  have hR : (ρ_ F).inv.val.app (op U)
        ((λ_ F).hom.val.app (op U)
          (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) F
            (op U) r x))
      = tensorPt 𝒪 h𝒪 F (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (op U) (r • x) (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
            h𝒪).obj.obj (op U)) :=
    (congrArg ((ρ_ F).inv.val.app (op U))
        (tensorPt_leftUnitor_hom 𝒪 h𝒪 (op U) r x)).trans
      (rightUnitor_inv_eq_tensorPt 𝒪 h𝒪 (op U) (r • x))
  rw [comp_val_app_apply, comp_val_app_apply, comp_val_app_apply]
  exact hL.trans hR.symm

/-- **The first snake identity on a local pure tensor**, over an object carrying a finite dual
basis. The computation is the mirror image of
`Stacks.SheafOfModules.evaluation_coevaluation_tensorPt`: the resulting sum
`∑ i, (r * μ(eᵢ)) • λᵢ` is `r • μ` by
`Stacks.SheafOfModules.FiniteDualBasis.eq_sum_smul_lam`. -/
lemma coevaluation_evaluation_tensorPt (U : C) {I' : Type*} [Fintype I']
    (c : FiniteDualBasis 𝒪 h𝒪 F U I')
    (mu : (dualSheaf 𝒪 h𝒪 F).val.obj (op U))
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) :
    (dualSheaf 𝒪 h𝒪 F ◁ coevaluation 𝒪 h𝒪 F hX b ≫
          (α_ (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F)).inv ≫
          MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)).val.app (op U)
        (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F)
          (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
            h𝒪))) (op U) mu r)
      = ((ρ_ (dualSheaf 𝒪 h𝒪 F)).hom ≫ (λ_ (dualSheaf 𝒪 h𝒪 F)).inv).val.app (op U)
        (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F)
          (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
            h𝒪))) (op U) mu r) := by
  have hL1 : (dualSheaf 𝒪 h𝒪 F ◁ coevaluation 𝒪 h𝒪 F hX b).val.app (op U)
        (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F)
          (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
            h𝒪))) (op U) mu r)
      = ∑ i : I', tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) (F ⊗ dualSheaf 𝒪 h𝒪 F) (op U) mu
          (tensorPt 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U) (r • c.e i) (c.lam i)) :=
    (tensorPt_whiskerLeft 𝒪 h𝒪 (coevaluation 𝒪 h𝒪 F hX b) (op U) mu r).trans
      ((congrArg (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) (F ⊗ dualSheaf 𝒪 h𝒪 F) (op U) mu)
          (coevaluation_app_eq_sum 𝒪 h𝒪 F hX b U c r)).trans
        (tensorPt_sum_right 𝒪 h𝒪 (op U) Finset.univ mu _))
  have hev : ∀ i : I', dualEval mu (r • c.e i) = r * dualEval mu (c.e i) :=
    fun i => evalSection_smul_right 𝒪 F.val
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val (op
        U) r mu (c.e i)
  have hL2 : ∀ i : I',
      (MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)).val.app (op U)
        ((α_ (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F)).inv.val.app (op U)
          (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) (F ⊗ dualSheaf 𝒪 h𝒪 F) (op U) mu
            (tensorPt 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U) (r • c.e i) (c.lam i))))
      = tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (dualSheaf 𝒪 h𝒪 F) (op U)
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))
          ((r * dualEval mu (c.e i)) • c.lam i) := by
    intro i
    refine Eq.trans (congrArg ((MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)).val.app (op U))
      (tensorPt_associator_inv 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F) (op U) mu
        (r • c.e i) (c.lam i))) ?_
    refine Eq.trans
      (tensorPt_whiskerRight 𝒪 h𝒪 (evaluation 𝒪 h𝒪 F) (op U) _ (c.lam i)) ?_
    refine Eq.trans (congrArg (fun z :
        (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪))).val.obj (op U) =>
        tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (dualSheaf 𝒪 h𝒪 F) (op U) z (c.lam i))
      ((evaluation_tensorPt 𝒪 h𝒪 F (op U) mu (r • c.e i)).trans (hev i))) ?_
    exact tensorPt_unit_left 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) (op U)
      (r * dualEval mu (c.e i)) (c.lam i)
  have hL : (MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)).val.app (op U)
        ((α_ (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F)).inv.val.app (op U)
          ((dualSheaf 𝒪 h𝒪 F ◁ coevaluation 𝒪 h𝒪 F hX b).val.app (op U)
            (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F)
              (𝟙_ (SheafOfModules.{max u v}
                (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) (op U) mu r)))
      = tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (dualSheaf 𝒪 h𝒪 F) (op U)
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (r •
            mu) := by
    refine Eq.trans (congrArg (fun z =>
      (MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)).val.app (op U)
        ((α_ (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F)).inv.val.app (op U) z)) hL1) ?_
    refine Eq.trans
      (map_sum (((MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)).val.app (op U)).hom.comp
        ((α_ (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F)).inv.val.app (op U)).hom)
        _ Finset.univ) ?_
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hL2 i) ?_
    refine Eq.trans (tensorPt_sum_right 𝒪 h𝒪
      (A := 𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        𝒪 h𝒪)))
      (B := dualSheaf 𝒪 h𝒪 F) (op U) Finset.univ
      (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))
      (fun i : I' => (r * dualEval mu (c.e i)) • c.lam i)).symm ?_
    refine congrArg (tensorPt 𝒪 h𝒪
      (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪))) (dualSheaf 𝒪 h𝒪 F)
      (op U) (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)))
        ?_
    refine Eq.trans (Finset.sum_congr rfl fun i _ =>
      mul_smul r (dualEval mu (c.e i)) (c.lam i)) ?_
    exact Finset.smul_sum.symm.trans (congrArg (r • ·) (c.eq_sum_smul_lam 𝒪 h𝒪 mu))
  have hR : (λ_ (dualSheaf 𝒪 h𝒪 F)).inv.val.app (op U)
        ((ρ_ (dualSheaf 𝒪 h𝒪 F)).hom.val.app (op U)
          (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F)
            (𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
              𝒪 h𝒪))) (op U) mu r))
      = tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
          (dualSheaf 𝒪 h𝒪 F) (op U)
          (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (r •
            mu) :=
    (congrArg ((λ_ (dualSheaf 𝒪 h𝒪 F)).inv.val.app (op U))
        (tensorPt_rightUnitor_hom 𝒪 h𝒪 (op U) mu r)).trans
      (leftUnitor_inv_eq_tensorPt 𝒪 h𝒪 (op U) (r • mu))
  rw [comp_val_app_apply, comp_val_app_apply, comp_val_app_apply]
  exact hL.trans hR.symm

end Snake

/-! ### From local pure tensors to morphisms -/

/-- Two morphisms out of a sheafification agree as soon as they agree on the image of the
sheafification unit, by the Tag 05NA adjunction. -/
lemma hom_ext_toSheafify {P : PresheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    {D : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (f g : (Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).obj P ⟶ D)
    (h : ∀ (V : Cᵒᵖ) (t : P.obj V),
      f.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app V t)
        = g.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app V t)) : f
          = g := by
  refine ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv P
    D).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext (h V))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- **A morphism of presheaves of modules into a sheaf is determined by its components over the
objects admitting a morphism into a member of a family covering the final object.** This is the
section-level analogue of
`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`, and it is the only use of
locality below. -/
lemma presheaf_hom_ext_of_coversTop {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {P : PresheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).obj}
    {D : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (φ ψ : P ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪) ⋙
      PresheafOfModules.restrictScalars (𝟙
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj D)
    (h : ∀ (k : K) (W : C) (_ : W ⟶ X k) (t : P.obj (op W)),
      φ.app (op W) t = ψ.app (op W) t) : φ = ψ := by
  refine (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪).obj).map_injective
    (NatTrans.ext (funext fun V => ?_))
  refine D.isSheaf.hom_ext (hX.cover V.unop) _ _ ?_
  rintro ⟨W, a, ⟨k, ⟨q⟩⟩⟩
  have hW : ((PresheafOfModules.toPresheaf
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map φ).app
        (op W)
      = ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪).obj).map ψ).app
        (op W) := by
    ext t
    exact h k W q t
  exact (((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪).obj).map φ).naturality
      a.op).symm.trans
    ((congrArg (fun z => ((PresheafOfModules.toPresheaf
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj).obj P).map a.op ≫ z)
          hW).trans
      (((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪).obj).map ψ).naturality
        a.op))

/-- **Two morphisms out of a tensor product sheaf agree as soon as they agree on the local pure
tensors over the objects admitting a morphism into a member of a covering family.** This is the
localization step of Tag 0FNV: the Tag 05NA adjunction removes the sheafification, where every
section is a sum of pure tensors, and
`Stacks.SheafOfModules.presheaf_hom_ext_of_coversTop` removes the objects over which no dual
basis is available. -/
lemma hom_ext_of_coversTop_tensorPt {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {D : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
      (f g : A ⊗ B ⟶ D)
    (h : ∀ (k : K) (W : C) (_ : W ⟶ X k) (a : A.val.obj (op W)) (b : B.val.obj (op W)),
      f.val.app (op W) (tensorPt 𝒪 h𝒪 A B (op W) a b)
        = g.val.app (op W) (tensorPt 𝒪 h𝒪 A B (op W) a b)) : f = g := by
  refine ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv (A.val ⊗
    B.val) D).injective ?_
  refine presheaf_hom_ext_of_coversTop 𝒪 h𝒪 hX _ _ fun k W q t => ?_
  have hlin : ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app (op
    W) ≫ f.val.app (op W))
      = ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 (A.val ⊗ B.val)).app (op W) ≫
        g.val.app (op W)) :=
    ModuleCat.MonoidalCategory.tensor_ext fun a c => h k W q a c
  refine Eq.trans (congrArg (fun α : A.val ⊗ B.val ⟶ _ => α.app (op W) t)
    (Adjunction.homEquiv_unit (adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
      𝒪 h𝒪) (f := f))) ?_
  refine Eq.trans (ConcreteCategory.congr_hom hlin t) ?_
  exact (congrArg (fun α : A.val ⊗ B.val ⟶ _ => α.app (op W) t)
    (Adjunction.homEquiv_unit (adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
      𝒪 h𝒪) (f := g))).symm

/-! ### The exact pairing -/

section Pairing

variable (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪))
  {K : Type*} {X : K → C} (hX : J.CoversTop X) {I : K → Type*} [∀ k, Fintype (I k)]
  (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k))

/-- **The first snake identity for the canonical evaluation and coevaluation.** -/
theorem coevaluation_evaluation_dualSheaf :
    dualSheaf 𝒪 h𝒪 F ◁ coevaluation 𝒪 h𝒪 F hX b ≫
        (α_ (dualSheaf 𝒪 h𝒪 F) F (dualSheaf 𝒪 h𝒪 F)).inv ≫
        MonoidalCategoryStruct.whiskerRight
        (self := Strict.monoidalCategoryStruct 𝒪 h𝒪)
        (evaluation 𝒪 h𝒪 F) (dualSheaf 𝒪 h𝒪 F)
      = (ρ_ (dualSheaf 𝒪 h𝒪 F)).hom ≫ (λ_ (dualSheaf 𝒪 h𝒪 F)).inv :=
  hom_ext_of_coversTop_tensorPt 𝒪 h𝒪
    (A := dualSheaf 𝒪 h𝒪 F)
    (B := 𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)))
    (D := 𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) ⊗ dualSheaf 𝒪 h𝒪 F)
    hX _ _ fun k W q mu r =>
      coevaluation_evaluation_tensorPt 𝒪 h𝒪 F hX b W ((b k).restrict 𝒪 h𝒪 q) mu r

/-- **The second snake identity for the canonical evaluation and coevaluation.** -/
theorem evaluation_coevaluation_dualSheaf :
    coevaluation 𝒪 h𝒪 F hX b ▷ F ≫ (α_ F (dualSheaf 𝒪 h𝒪 F) F).hom ≫
        F ◁ evaluation 𝒪 h𝒪 F
      = (λ_ F).hom ≫ (ρ_ F).inv :=
  hom_ext_of_coversTop_tensorPt 𝒪 h𝒪
    (A := 𝟙_ (SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪))) (B := F)
    (D := F ⊗ 𝟙_ (SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
    hX _ _ fun k W q r x =>
      evaluation_coevaluation_tensorPt 𝒪 h𝒪 F hX b W ((b k).restrict 𝒪 h𝒪 q) r x

/-- **The dual sheaf is a left dual of `F`, with the canonical coevaluation and evaluation**, for
a sheaf of modules carrying finite dual bases on a family covering the final object.

This is the assertion of Tag 0FNV; it is stated here with the local hypothesis in its
sectionwise form, and `Stacks.SheafOfModules.exactPairingDualSheafOfRetract` is the same
statement with the hypothesis in the form Stacks gives it. The tag sits on that one, which is
the faithful rendering, rather than on both. -/
@[instance_reducible]
noncomputable def exactPairingDualSheaf : ExactPairing F (dualSheaf 𝒪 h𝒪 F) where
  coevaluation' := coevaluation 𝒪 h𝒪 F hX b
  evaluation' := evaluation 𝒪 h𝒪 F
  coevaluation_evaluation' := coevaluation_evaluation_dualSheaf 𝒪 h𝒪 F hX b
  evaluation_coevaluation' := evaluation_coevaluation_dualSheaf 𝒪 h𝒪 F hX b

/-- `Stacks.SheafOfModules.exactPairingDualSheaf` read as Mathlib's
`CategoryTheory.HasRightDual F`, which is Stacks' "`F^∨` is a left dual of `F`". -/
@[instance_reducible]
noncomputable def hasRightDualOfLocalDualBasis : HasRightDual F where
  rightDual := dualSheaf 𝒪 h𝒪 F
  exact := exactPairingDualSheaf 𝒪 h𝒪 F hX b

end Pairing

section Retract

variable (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪))
  {K : Type*} {X : K → C} (hX : J.CoversTop X) {I : K → Type (max u v)}
  [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
  [∀ k, HasWeakSheafify (J.over (X k)) AddCommGrpCat.{max u v}]
  [∀ k, (J.over (X k)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Stacks Project, Tag 0FNV.** Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and
let `F` be a sheaf of `𝒪`-modules which is locally a direct summand of a finite free sheaf of
modules: on the members of a family covering the final object, `F` restricts to a retract of
`SheafOfModules.free (I k)` with `I k` finite. Then the dual
`F^∨ = SheafHom(F, 𝒪)`, with the canonical coevaluation `𝒪 ⟶ F ⊗ F^∨` and the canonical
evaluation `F^∨ ⊗ F ⟶ 𝒪`, is a **left dual** of `F` in the monoidal category of sheaves of
`𝒪`-modules of Tag 01CA.

The retracts are converted into the dual bases that the canonical coevaluation is built from by
`Stacks.SheafOfModules.FiniteDualBasis.ofRetract`, and the two snake identities are
`Stacks.SheafOfModules.coevaluation_evaluation_dualSheaf` and
`evaluation_coevaluation_dualSheaf`. -/
@[stacks 0FNV "the LEFT-DUAL assertion itself: the canonical coevaluation `𝒪 ⟶ ℱ ⊗ ℱ^∨` and \
evaluation `ℱ^∨ ⊗ ℱ ⟶ 𝒪` satisfy the two snake identities, so `ℱ^∨` is a left dual of `ℱ` in \
the monoidal category of Tag 01CA, for `ℱ` locally a retract of a finite free sheaf of modules. \
This is the clause none of `dual_sheaf`, `evaluation`, `coevaluation` or the rank-one \
isomorphism `ℱ ⊗ ℱ^∨ ≅ 𝓗om(ℱ,ℱ)` asserts: those construct the four objects and compute them on \
sections, this one is the duality", instance_reducible]
noncomputable def exactPairingDualSheafOfRetract
    (h : ∀ k, Retract (F.over (X k))
      (free (R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over (X k)) (I
        k))) :
    ExactPairing F (dualSheaf 𝒪 h𝒪 F) :=
  exactPairingDualSheaf 𝒪 h𝒪 F hX fun k => FiniteDualBasis.ofRetract 𝒪 h𝒪 (h k)

end Retract

end Stacks.SheafOfModules

end
