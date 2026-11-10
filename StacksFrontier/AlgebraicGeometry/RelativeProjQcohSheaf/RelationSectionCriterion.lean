module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTensorGeneral
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# Checking the balancing relations of `ℳ̃_T` on global sections

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra and `ℳ` a graded `𝒜`-module (Situation 01NN).
The module `ℳ̃_T` of [Stacks, Tag 01O6] attached to a quadruple `(d, f : T → S, L, ψ)` is the
quotient of `⨁_{n ∈ ℤ} f^*ℳ_{nd} ⊗ L^{⊗ (-n)}` by the balancing relations
`(x · a) ⊗ l = x ⊗ (ψ(a) · l)`, and by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.existsUnique_hom` a morphism out of it
is a family `b n : f^*ℳ_{nd} ⊗ L^{⊗ (-n)} ⟶ 𝒩` satisfying, in each bidegree `(n, i)`,

`relationLeft ≫ b (n + i) = relationRight ≫ b n`.

Over an **affine** base `S` that equation ought to be checkable on global sections, since
`f^*ℳ_{nd}` and `f^*𝒜_{id}` are pullbacks of quasi-coherent modules from `S`. It is **not**
directly checkable: the two sides are morphisms out of

`(f^*ℳ_{nd} ⊗ f^*𝒜_{id}) ⊗ L^{⊗ (-(n+i))}`,

and the outer factor `L^{⊗ (-(n+i))}` is an invertible `𝒪_T`-module with no relation to `S`, so
neither `Stacks.AlgebraicGeometry.AffineHomRecovery.hom_ext` — whose source must be a pullback
`f^*ℳ` — nor `Stacks.AlgebraicGeometry.AffineTensorGeneral.tensor_hom_ext_of_sections` — whose
source must be a tensor product of **two** pullbacks — applies to it. An invertible module need
have no nonzero global section at all, so there is nothing on the outer factor to evaluate.

This file supplies the missing step. Tensoring by an invertible object is an equivalence
([Stacks, Tag 0FFM]), so a morphism out of `X ⊗ K` is determined by its *untwisting*, a morphism
out of `X`, and the untwisting of a relation summand is a morphism out of
`f^*ℳ_{nd} ⊗ f^*𝒜_{id}`, where the affine criterion does apply. The result is
`relationLeft_eq_relationRight_of_sections`: a balancing relation holds as soon as the two
untwisted sides agree on the pure tensors of the pullback-unit images of global sections of
`ℳ_{nd}` and `𝒜_{id}`.

## The untwisting

For `e : K ⊗ K' ≅ 𝟙` the composite

`X ≅ X ⊗ 𝟙 ≅ X ⊗ (K ⊗ K') ≅ (X ⊗ K) ⊗ K'`

is `untwistIso`, and `untwist e u` is `u ▷ K'` precomposed with it. It is injective in `u`
because `- ⊗ K'` is faithful, which for `K' = L^{⊗ n}` holds because the two inverse laws
`L^{⊗ n} ⊗ L^{⊗ (-n)} ≅ 𝒪_T` of the coherent multiplication of [Stacks, Tag 01CU] exhibit
`L^{⊗ n}` as an invertible object (`laurentHasInverse`).

## Main definitions

* `Stacks.Monoidal.untwistIso` and `Stacks.Monoidal.untwist`: the comparison
  `X ≅ (X ⊗ K) ⊗ K'` attached to an inverse law `K ⊗ K' ≅ 𝟙`, and the untwisting of a morphism
  out of `X ⊗ K` that it defines.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.laurentInvLaw` and
  `laurentHasInverse`: the inverse law `L^{⊗ (-k)} ⊗ L^{⊗ k} ≅ 𝒪_T` of the Laurent algebra of
  `L`, and the two-sided tensor inverse of `L^{⊗ k}` it assembles.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.relLeftComp` and
  `relRightComp`: the two sides of a balancing relation, with their common source declared as a
  twisted tensor product of two pullbacks rather than as
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relationSummand`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.twistLaw` and `rightLaw`: the
  action `(a, l) ↦ ψ(a) · l` of `ψ(𝒜_{id})` on the Laurent algebra, and the `ψ`-side of a
  balancing relation with the pullback of `ℳ_{nd}` replaced by an arbitrary object.

## Main results

* `Stacks.Monoidal.hom_ext_of_untwist`: **a morphism out of `X ⊗ K` is determined by its
  untwisting**, for `K'` a tensor inverse of `K`.
* `Stacks.Monoidal.untwist_whiskerRight_comp`: untwisting carries a composite
  `v ▷ K ≫ u` to `v ≫ untwist u`, so a morphism whose first factor is whiskered unwhiskers.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.untwist_hom_ext_of_sections`:
  **two morphisms `(f^*F ⊗ f^*G) ⊗ K ⟶ 𝒩` whose untwistings agree on the pure tensors of the
  pullback-unit images of global sections are equal**, for `F` and `G` quasi-coherent on an
  affine `S`, `f : T ⟶ S` arbitrary, `K` invertible and `𝒩` arbitrary.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.twistedPullbackPair_eq`: the
  source of the criterion is the relation summand of [Stacks, Tag 01O6] on the nose.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.untwist_relLeftComp`: the
  untwisting of the relation-free side of a balancing relation is the pulled-back action
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.act` followed by the untwisting of `b (n+i)`.
* `RelativeProjQcohSheaf.RelationSections.relationLeft_eq_relationRight_of_sections`: **a balancing
  relation of [Stacks, Tag 01O6] over an affine base is checkable on the pure tensors of global
  sections.**
* `Stacks.Monoidal.untwist_whiskerLeft_comp`: untwisting splits the first factor off a
  middle-whiskered composite, which is the shape of the `ψ`-side of a relation.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.untwist_relRightComp`: **the
  `ψ`-side of a balancing relation untwists with its module factor split off**, leaving a
  composite in which no homogeneous piece of `ℳ` occurs at all.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections.relation_of_untwist_eq`: **a
  balancing relation of [Stacks, Tag 01O6] follows from one identity between morphisms out of
  `f^*ℳ_{nd} ⊗ f^*𝒜_{id}`** — that the family's degreewise first factor intertwines the action
  of `𝒜` with the action of `ψ(𝒜)`. The source is a tensor product of two pullbacks from the
  affine base, so the identity is reachable by
  `Stacks.AlgebraicGeometry.AffineTensorGeneral.tensor_hom_ext_of_sections` with no further
  untwisting, and the reduction loses nothing, the untwisting being injective.

## What is NOT here

No balancing relation is verified, and no normalisation on sections of the comparison
isomorphisms of
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso` is proved; this file
only makes the global-section computation that such a verification would consist of into a
sufficient criterion. No tag is carried.

This file belongs to the route to property (1) of [Stacks, Tag 01O7] through the
isomorphism `α : h^*𝒪(d) ≅ L`, and the remarks in this section concern that route only.
The comparison `ℳ̃_T ≅ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] is built by another route,
in `StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/`, which uses nothing from this
file:
on a chart datum (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`) the
degreewise maps send `x ⊗ l` to `g^*(x / c^m) · (l · w^m)`, their balancing relations are
verified directly (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.bmap_balanced`), and the
inverse is written down.

The balancing relations are nevertheless **reduced** here, by `relation_of_untwist_eq`, to one
identity per bidegree; for the degreewise family of property (1) on a chart that identity is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.Intertwines`, which is a
hypothesis on this route — and which, as that file's docstring records, is a *compatibility* of the
isomorphism `α : h^*𝒪(d) ≅ L` with `ψ` rather than a property of either: `ψ` enters a relation
only through `twistLaw` below, and it is exactly what stands between the two sides' degrees.

What the untwisting does to that comparison *is* proved, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerContractSnake`: the untwisting along
`laurentInvLaw` cancels the contraction `powContractIso` against the opposite tensor power, so
the untwisting of `pullbackShiftedContractIso` is `pullbackShiftedIso`. That is an identity
between morphisms; it is not an evaluation on sections, and it is not a balancing relation.

## Implementation notes

`relLeftComp` and `relRightComp` exist only to declare the source of the two sides at the
spelling `untwist_hom_ext_of_sections` consumes. The equality with
`relationSummand f ℳ d L p` is `rfl`, but a bare type ascription does not make the elaborator
use it — the two spellings are compared only after the pullback functor and the Laurent algebra
are unfolded, and the comparison of the resulting hypothesis types exceeds the recursion limit.
A named declaration with the target type declared does make it use it.

Quasi-coherence of a homogeneous piece is asked at the `AlgebraicGeometry.Scheme.Modules`
spelling through `modulePiece` and `algebraPiece`. The class
`SheafOfModules.IsQuasicoherent` is indexed by the sheaf of rings, and the two spellings of the
structure sheaf of a scheme, while equal by `rfl`, are different keys for instance search, so an
instance registered at one of them is not found at the other.

## References

* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower
open RingedSpaceModuleAdjunction (opensMap)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe v u

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The comparison `X ≅ (X ⊗ K) ⊗ K'` attached to an inverse law `e : K ⊗ K' ≅ 𝟙`**: the
right unitor, `e` inserted backwards, and the associator. -/
def untwistIso {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) (X : C) : X ≅ (X ⊗ K) ⊗ K' :=
  (ρ_ X).symm ≪≫ whiskerLeftIso X e.symm ≪≫ (α_ X K K').symm

/-- `untwistIso` is natural in `X`, the morphisms on the right being whiskered twice. -/
theorem untwistIso_hom_naturality {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X Y : C} (v : X ⟶ Y) :
    (untwistIso e X).hom ≫ (v ▷ K) ▷ K' = v ≫ (untwistIso e Y).hom := by
  simp only [untwistIso, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc]
  rw [← MonoidalCategory.associator_inv_naturality_left, ← Category.assoc (X ◁ e.inv),
    MonoidalCategory.whisker_exchange, Category.assoc,
    ← Category.assoc (ρ_ X).inv, ← MonoidalCategory.rightUnitor_inv_naturality,
    Category.assoc]

/-- **The untwisting of a morphism out of `X ⊗ K`**: the morphism `X ⟶ N ⊗ K'` obtained by
whiskering by a tensor inverse `K'` of `K` and precomposing with `untwistIso`. -/
def untwist {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X N : C} (u : X ⊗ K ⟶ N) : X ⟶ N ⊗ K' :=
  (untwistIso e X).hom ≫ u ▷ K'

/-- **Untwisting unwhiskers a first factor.** The untwisting of a morphism out of `X ⊗ K` whose
first step is a morphism `v` whiskered by `K` is `v` followed by the untwisting of the rest. -/
theorem untwist_whiskerRight_comp {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X Y N : C} (v : X ⟶ Y)
    (u : Y ⊗ K ⟶ N) : untwist e (v ▷ K ≫ u) = v ≫ untwist e u := by
  simp only [untwist, MonoidalCategory.comp_whiskerRight]
  rw [← Category.assoc, untwistIso_hom_naturality, Category.assoc]

/-- **Untwisting splits off the first factor of a middle-whiskered composite.** A morphism out
of `(X ⊗ Y) ⊗ K` whose shape is: associate, act on `Y ⊗ K` by `ν`, then apply a morphism out of
`X ⊗ W` whose own first step is a morphism `v` whiskered by `W`, untwists to `v ▷ Y` followed by
the untwisting of the same composite with `X` replaced by the target of `v`.

This is the shape of the `ψ`-side of a balancing relation of [Stacks, Tag 01O6]: there `X` is
the pullback of a homogeneous piece of `ℳ`, `ν` carries a homogeneous piece of `𝒜` into the
Laurent algebra, and `v` is the degreewise map's own first factor. The point is that the
remaining composite no longer involves `X`, so the whole dependence of the relation on `ℳ`
is in `v ▷ Y`. -/
theorem untwist_whiskerLeft_comp {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X Y Z W N : C}
    (ν : Y ⊗ K ⟶ W) (v : X ⟶ Z) (u : Z ⊗ W ⟶ N) :
    untwist e ((α_ X Y K).hom ≫ X ◁ ν ≫ v ▷ W ≫ u) =
      v ▷ Y ≫ untwist e ((α_ Z Y K).hom ≫ Z ◁ ν ≫ u) := by
  have h : (α_ X Y K).hom ≫ X ◁ ν ≫ v ▷ W ≫ u =
      (v ▷ Y) ▷ K ≫ ((α_ Z Y K).hom ≫ Z ◁ ν ≫ u) := by
    rw [← Category.assoc (X ◁ ν), MonoidalCategory.whisker_exchange]
    simp only [Category.assoc]
    rw [← MonoidalCategory.associator_naturality_left_assoc]
  rw [h, untwist_whiskerRight_comp]

/-- `untwist_whiskerLeft_comp` with the three composites supplied as free morphisms and their
shapes as hypotheses, which is how it is applied: at the point of use each hypothesis is `rfl`
or the factorisation of the degreewise family, while the statement names only one spelling of
each object. A goal that mentions two `rfl`-equal spellings of the same sheaf of modules is not
type-correct at the `implicit` transparency level, so `rw` cannot be used to bring the composites
into shape in place. -/
theorem untwist_eq_of_whiskerLeft {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) {X Y Z W N : C}
    (ν : Y ⊗ K ⟶ W) (v : X ⟶ Z) (u : Z ⊗ W ⟶ N) {bn : X ⊗ W ⟶ N}
    {w : (X ⊗ Y) ⊗ K ⟶ N} {g : (Z ⊗ Y) ⊗ K ⟶ N}
    (hb : bn = v ▷ W ≫ u) (hw : w = ((α_ X Y K).hom ≫ X ◁ ν) ≫ bn)
    (hg : g = ((α_ Z Y K).hom ≫ Z ◁ ν) ≫ u) :
    untwist e w = v ▷ Y ≫ untwist e g := by
  subst hb hw hg
  simpa only [Category.assoc] using untwist_whiskerLeft_comp e ν v u

/-- **A morphism out of `X ⊗ K` is determined by its untwisting**, `K'` being a tensor inverse
of `K`: tensoring on the right by `K'` is then faithful, and `untwistIso` is an isomorphism. -/
theorem hom_ext_of_untwist {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C)
    [(MonoidalCategory.tensorRight K').Faithful] {X N : C} {u u' : X ⊗ K ⟶ N}
    (hu : untwist e u = untwist e u') : u = u' :=
  (MonoidalCategory.tensorRight K').map_injective
    ((cancel_epi (untwistIso e X).hom).mp hu)

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections

open Stacks.Monoidal (untwist untwist_whiskerRight_comp hom_ext_of_untwist)

variable {S T : Scheme.{u}} (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-! ### The tensor powers of `L` are invertible objects -/

/-- Tensoring on the right by `L` is an equivalence, at the spelling of the structure sheaf that
the Laurent algebra of `L` is indexed by. The instance is the one
`Stacks.SheafOfModules.IsInvertible` already provides; it is named again here because the sheaf
condition `isSheafStruct T` occurs in the general statement only inside a proof of the sheaf
condition on `𝒪_T`, which instance search cannot recover from the goal. -/
instance isEquivalence_tensorRightFunctor_laurent :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
        (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L).IsEquivalence :=
  isEquivalence_tensorRightFunctor T.toRingedSpace.presheaf (isSheafStruct T) L

/-- **The inverse law `L^{⊗ (-k)} ⊗ L^{⊗ k} ≅ 𝒪_T`** of the Laurent algebra of `L`: the coherent
multiplication of [Stacks, Tag 01CU] in the bidegree `(-k, k)`, followed by the reindexing to the
degree zero, whose tensor power is the unit object. -/
def laurentInvLaw (k : ℤ) :
    (laurent L).piece (-k) ⊗ (laurent L).piece k ≅
      𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :=
  coherentMulIso T.toRingedSpace.presheaf (isSheafStruct T) L (-k) k ≪≫
    tensorPowerReindex T.toRingedSpace.presheaf (isSheafStruct T) L (neg_add_cancel k)

/-- **`L^{⊗ k}` is an invertible object**, with tensor inverse `L^{⊗ (-k)}`: the two inverse laws
are the coherent multiplication in the bidegrees `(k, -k)` and `(-k, k)`. -/
def laurentHasInverse (k : ℤ) :
    MonoidalCategory.HasInverse ((laurent L).piece k) where
  inv := (laurent L).piece (-k)
  isoLeft := coherentMulIso T.toRingedSpace.presheaf (isSheafStruct T) L k (-k) ≪≫
    tensorPowerReindex T.toRingedSpace.presheaf (isSheafStruct T) L (add_neg_cancel k)
  isoRight := laurentInvLaw L k

/-- Tensoring on the right by `L^{⊗ k}` is an equivalence of categories, by [Stacks, Tag 0FFM]
applied to `laurentHasInverse`. In particular it is faithful, which is what the untwisting
criterion asks for. -/
instance isEquivalence_tensorRight_laurent (k : ℤ) :
    (MonoidalCategory.tensorRight ((laurent L).piece k)).IsEquivalence :=
  (laurentHasInverse L k).tensorRightEquivalence.isEquivalence_functor

/-! ### The criterion -/

variable [IsAffine S] (f : T ⟶ S)
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)

/-- The degree-`nd` homogeneous piece of `ℳ`, as an object of
`AlgebraicGeometry.Scheme.Modules`, which is the spelling the affine criterion and the
quasi-coherence class are stated at. -/
abbrev modulePiece (n : ℤ) : S.Modules := M.piece (n * d)

/-- The degree-`id` homogeneous piece of `𝒜`, as an object of
`AlgebraicGeometry.Scheme.Modules`. -/
abbrev algebraPiece (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (d i : ℤ) : S.Modules := A.piece (i * d)

/-- **Two morphisms `(f^*F ⊗ f^*G) ⊗ K ⟶ 𝒩` whose untwistings agree on the pure tensors of the
pullback-unit images of global sections are equal.**

`S` is affine and `F`, `G` are quasi-coherent on it; `f : T ⟶ S`, the invertible-object datum
`K ⊗ K' ≅ 𝒪_T` and the target `𝒩` are arbitrary. The untwistings are morphisms out of
`f^*F ⊗ f^*G`, where
`Stacks.AlgebraicGeometry.AffineTensorGeneral.tensor_hom_ext_of_sections` applies. -/
theorem untwist_hom_ext_of_sections (F G : S.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {K K' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (e : K ⊗ K' ≅ 𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))
    [(MonoidalCategory.tensorRight K').Faithful]
    (N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    {u u' : (AffineTensorGeneral.pullbackSheafMod f F ⊗
      AffineTensorGeneral.pullbackSheafMod f G) ⊗ K ⟶ N}
    (hyp : ∀ (s : Γ(F, ⊤)) (t : Γ(G, ⊤)),
      (untwist e u).val.app ((opensMap f.toLRSHom.toShHom).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul f F G s t) =
        (untwist e u').val.app ((opensMap f.toLRSHom.toShHom).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul f F G s t)) :
    u = u' :=
  hom_ext_of_untwist e (AffineTensorGeneral.tensor_hom_ext_of_sections f F G (N ⊗ K') hyp)

/-- The source `(f^*ℳ_{nd} ⊗ f^*𝒜_{id}) ⊗ L^{⊗ (-(n+i))}` of a balancing relation, with its two
inner factors declared as pullbacks of modules on `S`. It is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relationSummand` on the nose. -/
abbrev twistedPullbackPair (p : ℤ × ℤ) :
    SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  (AffineTensorGeneral.pullbackSheafMod f (modulePiece M d p.1) ⊗
      AffineTensorGeneral.pullbackSheafMod f (algebraPiece A d p.2)) ⊗
    (laurent L).piece (-(p.1 + p.2))

omit [IsAffine S] in
/-- **`twistedPullbackPair` is `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relationSummand`
on the nose**: the pullback of a homogeneous piece along the morphism of ringed spaces underlying
`f` is the pullback the affine criterion is stated with, and the degree-`(-(n+i))` homogeneous
piece of the Laurent algebra is the tensor power the relation summand is twisted by. -/
theorem twistedPullbackPair_eq (p : ℤ × ℤ) :
    twistedPullbackPair L f M d p = relationSummand f M d L p := rfl

/-- The side `(x, a, l) ↦ (x · a) ⊗ l` of a balancing relation followed by the degree-`(n+i)`
member of a family out of the degreewise pure tensors, with its source declared as
`twistedPullbackPair`. -/
def relLeftComp {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N) (p : ℤ × ℤ) :
    twistedPullbackPair L f M d p ⟶ N :=
  relationLeft f M d L p ≫ b (p.1 + p.2)

/-- The side `(x, a, l) ↦ x ⊗ (ψ(a) · l)` of a balancing relation followed by the degree-`n`
member of a family out of the degreewise pure tensors, with its source declared as
`twistedPullbackPair`. -/
def relRightComp {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (ψ : Twisting f A d L) (b : ∀ n : ℤ, summand f M d L n ⟶ N) (p : ℤ × ℤ) :
    twistedPullbackPair L f M d p ⟶ N :=
  Twisting.relationRight M ψ p ≫ b p.1

omit [IsAffine S] in
/-- **The `ψ`-free side of a balancing relation untwists to the pulled-back action.** Its first
step is the action `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.act` whiskered by
`L^{⊗ (-(n+i))}`, which untwisting unwhiskers. -/
theorem untwist_relLeftComp {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N) (p : ℤ × ℤ) :
    untwist (laurentInvLaw L (p.1 + p.2)) (relLeftComp L f M d b p) =
      act f M d p.1 p.2 ≫ untwist (laurentInvLaw L (p.1 + p.2)) (b (p.1 + p.2)) :=
  untwist_whiskerRight_comp _ _ _

/-! ### Splitting the module off the `ψ`-side -/

/-- **The `ψ`-and-Laurent part of a balancing relation in bidegree `(n, i)`**, the morphism
`f^*𝒜_{id} ⊗ L^{⊗ (-(n+i))} ⟶ L^{⊗ (-n)}` sending `(a, l)` to `ψ(a) · l`. It is the morphism
that `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.relationRight` whiskers the
pullback of `ℳ_{nd}` by, and it is the only place `ψ` occurs in a relation. -/
def twistLaw (ψ : Twisting f A d L) (p : ℤ × ℤ) :
    AffineTensorGeneral.pullbackSheafMod f (algebraPiece A d p.2) ⊗
        (laurent L).piece (-(p.1 + p.2)) ⟶
      (laurent L).piece (-p.1) :=
  MonoidalCategoryStruct.whiskerRight (ψ.app p.2) ((laurent L).piece (-(p.1 + p.2))) ≫
    (laurent L).mulSheaf p.2 (-(p.1 + p.2)) ≫
      eqToHom (congrArg (laurent L).piece (by ring : p.2 + -(p.1 + p.2) = -p.1))

omit [IsAffine S] in
/-- **The `ψ`-side of a balancing relation is the associator followed by `twistLaw`** whiskered
into the pullback of `ℳ_{nd}`. -/
theorem relRightComp_eq (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N) (p : ℤ × ℤ) :
    relRightComp L f M d ψ b p =
      ((α_ (AffineTensorGeneral.pullbackSheafMod f (modulePiece M d p.1))
            (AffineTensorGeneral.pullbackSheafMod f (algebraPiece A d p.2))
            ((laurent L).piece (-(p.1 + p.2)))).hom ≫
          MonoidalCategoryStruct.whiskerLeft _ (twistLaw L f d ψ p)) ≫ b p.1 :=
  rfl

/-- **The `ψ`-side of a balancing relation with the module factor replaced by an arbitrary
object.** For `u : Z ⊗ L^{⊗ (-n)} ⟶ 𝒩` this is `(z, a, l) ↦ u(z, ψ(a) · l)`; taking `Z` to be
the target of the degreewise family's own first factor and `u` the rest of it recovers
`relRightComp`, by `untwist_relRightComp`. No homogeneous piece of `ℳ` occurs in it. -/
def rightLaw (ψ : Twisting f A d L) (p : ℤ × ℤ)
    {Z N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (u : Z ⊗ (laurent L).piece (-p.1) ⟶ N) :
    (Z ⊗ AffineTensorGeneral.pullbackSheafMod f (algebraPiece A d p.2)) ⊗
        (laurent L).piece (-(p.1 + p.2)) ⟶ N :=
  ((α_ _ _ _).hom ≫ MonoidalCategoryStruct.whiskerLeft Z (twistLaw L f d ψ p)) ≫ u

omit [IsAffine S] in
/-- **The `ψ`-side of a balancing relation untwists with the module factor split off.** If the
degree-`n` member of the family factors as a morphism `v` whiskered by `L^{⊗ (-n)}` followed by
`u` — which is how the comparison of property (1) of [Stacks, Tag 01O7] is built, `v` being the
canonical map `f^*ℳ_{nd} ⟶ h^*(ℳ(nd)~)` — then the untwisting of the `ψ`-side is `v` whiskered
by `f^*𝒜_{id}`, followed by the untwisting of `rightLaw`, in which `ℳ` no longer occurs.

Together with `untwist_relLeftComp` this reduces a balancing relation to a single identity
between morphisms out of `f^*ℳ_{nd} ⊗ f^*𝒜_{id}`; that is `relation_of_untwist_eq`. -/
theorem untwist_relRightComp (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N) (p : ℤ × ℤ)
    {Z : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (v : AffineTensorGeneral.pullbackSheafMod f (modulePiece M d p.1) ⟶ Z)
    (u : Z ⊗ (laurent L).piece (-p.1) ⟶ N)
    (hb : b p.1 = MonoidalCategoryStruct.whiskerRight v ((laurent L).piece (-p.1)) ≫ u) :
    untwist (laurentInvLaw L (p.1 + p.2)) (relRightComp L f M d ψ b p) =
      MonoidalCategoryStruct.whiskerRight v
          (AffineTensorGeneral.pullbackSheafMod f (algebraPiece A d p.2)) ≫
        untwist (laurentInvLaw L (p.1 + p.2)) (rightLaw L f d ψ p u) :=
  Stacks.Monoidal.untwist_eq_of_whiskerLeft (laurentInvLaw L (p.1 + p.2)) (twistLaw L f d ψ p)
    v u hb (relRightComp_eq L f M d ψ b p) rfl

omit [IsAffine S] in
/-- **A balancing relation of [Stacks, Tag 01O6] holds as soon as one identity between
morphisms out of `f^*ℳ_{nd} ⊗ f^*𝒜_{id}` does**, for a family whose degree-`n` member factors
as a morphism `v` out of `f^*ℳ_{nd}` whiskered by `L^{⊗ (-n)}` followed by a morphism `u`.

The identity is the *intertwining*: the pulled-back action of `𝒜` on `ℳ` followed by the
untwisted degree-`(n+i)` member agrees with `v` followed by the action of `ψ(𝒜)` on the Laurent
algebra. Both sides are morphisms out of a tensor product of two pullbacks from the base, where
`Stacks.AlgebraicGeometry.AffineTensorGeneral.tensor_hom_ext_of_sections` applies directly, with
no further untwisting, and no tensor power of `L` occurs on the left-hand side at all. The
converse holds too, the untwisting being injective, so nothing is lost by checking it instead. -/
theorem relation_of_untwist_eq (ψ : Twisting f A d L) (p : ℤ × ℤ)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N)
    {Z : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (v : AffineTensorGeneral.pullbackSheafMod f (modulePiece M d p.1) ⟶ Z)
    (u : Z ⊗ (laurent L).piece (-p.1) ⟶ N)
    (hb : b p.1 = MonoidalCategoryStruct.whiskerRight v ((laurent L).piece (-p.1)) ≫ u)
    (hint : act f M d p.1 p.2 ≫ untwist (laurentInvLaw L (p.1 + p.2)) (b (p.1 + p.2)) =
      MonoidalCategoryStruct.whiskerRight v
          (AffineTensorGeneral.pullbackSheafMod f (algebraPiece A d p.2)) ≫
        untwist (laurentInvLaw L (p.1 + p.2)) (rightLaw L f d ψ p u)) :
    relationLeft f M d L p ≫ b (p.1 + p.2) = Twisting.relationRight M ψ p ≫ b p.1 :=
  hom_ext_of_untwist (laurentInvLaw L (p.1 + p.2)) (u := relLeftComp L f M d b p)
    (u' := relRightComp L f M d ψ b p)
    ((untwist_relLeftComp L f M d b p).trans
      (hint.trans (untwist_relRightComp L f M d ψ b p v u hb).symm))

/-- **A balancing relation of [Stacks, Tag 01O6] over an affine base is checkable on global
sections.** For a quadruple `(d, f : T → S, L, ψ)` with `S` affine and the two homogeneous pieces
`ℳ_{nd}` and `𝒜_{id}` quasi-coherent, the relation

`relationLeft ≫ b (n + i) = relationRight ≫ b n`

holds as soon as the untwistings of its two sides agree on the pure tensors of the pullback-unit
images of global sections of `ℳ_{nd}` and `𝒜_{id}`. The untwisting is what makes this possible:
the relation itself is an equality of morphisms out of a module with the invertible factor
`L^{⊗ (-(n+i))}`, which has no global sections to test on. -/
theorem relationLeft_eq_relationRight_of_sections (ψ : Twisting f A d L) (p : ℤ × ℤ)
    [(modulePiece M d p.1).IsQuasicoherent] [(algebraPiece A d p.2).IsQuasicoherent]
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N)
    (hyp : ∀ (s : Γ(modulePiece M d p.1, ⊤)) (t : Γ(algebraPiece A d p.2, ⊤)),
      (untwist (laurentInvLaw L (p.1 + p.2)) (relLeftComp L f M d b p)).val.app
          ((opensMap f.toLRSHom.toShHom).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul f (modulePiece M d p.1)
            (algebraPiece A d p.2) s t) =
        (untwist (laurentInvLaw L (p.1 + p.2)) (relRightComp L f M d ψ b p)).val.app
          ((opensMap f.toLRSHom.toShHom).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul f (modulePiece M d p.1)
            (algebraPiece A d p.2) s t)) :
    relationLeft f M d L p ≫ b (p.1 + p.2) = Twisting.relationRight M ψ p ≫ b p.1 := by
  refine untwist_hom_ext_of_sections f (modulePiece M d p.1) (algebraPiece A d p.2)
    (laurentInvLaw L (p.1 + p.2)) N (u := relLeftComp L f M d b p)
    (u' := relRightComp L f M d ψ b p) ?_
  exact hyp

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RelationSections

end
