module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageGeometric
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleClosedSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSetsToposInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of a free differential graded module along a morphism of ringed topoi

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `A` be a sheaf of differential graded
`O_Y`-algebras, let `B` be a sheaf of differential graded `O_X`-algebras, let `ψ : A ⟶ f_*B` be a
unital homomorphism, and let `S` be a sheaf of graded sets on `Y`. **The free differential graded
`B`-module `B[f⁻¹S]` on the inverse image of `S` corepresents morphisms out of `A[S]` into the
direct image**, that is

`Hom_B(B[f⁻¹S], Q) ≃ Hom_A(A[S], f_{*,ψ}Q)` naturally in `Q`.

No functor `f^*` on all differential graded modules is needed for this, and none is assumed: the
object `B[f⁻¹S]` is **constructed**, and what is proved is its universal property. The chain is

`Hom_B(B[f⁻¹S], Q)`
  `≃ ∀ i, ((f⁻¹S)_i ⟶ Z_i Q)`         the universal property of `B[f⁻¹S]` on `X`
  `≃ ∀ i, (f⁻¹(S_i) ⟶ Z_i Q)`          the grading survives the inverse image
  `≃ ∀ i, (S_i ⟶ f_* Z_i Q)`           the adjunction `f⁻¹ ⊣ f_*` of sheaves of sets
  `≃ ∀ i, (S_i ⟶ Z_i (f_{*,ψ}Q))`      the closed sections of the direct image
  `≃ Hom_A(A[S], f_{*,ψ}Q)`            the universal property of `A[S]` on `Y`,

where `S_i` is the sheaf of degree-`i` local sections of `S` and `Z_i` the sheaf of closed
degree-`i` local sections. Every step is a bijection of morphisms of **sheaves of sets** natural
in `Q`, which is the whole point of trading the universal property of a free module for
`Stacks.degreeFiberSheaf` and `closedSectionSheaf`.

## Main definitions

* `SheafOfModules.freeDGModuleToposHomEquiv` is the composite bijection.
* `SheafOfModules.freeDGModuleToposCorepresentableBy`: **the corepresentability witness**, in
  Mathlib's `CategoryTheory.Functor.CorepresentableBy`.
* `SheafOfModules.IsGoodToposBaseChange`: **a good right differential graded module, Tag 0FSA.**
  Condition (3) is read over the source's own base changes, morphisms of ringed topoi, with
  existence of the pullback part of the conclusion. Its binders are those of Tag 0FSA's
  condition (3) and no others, which is why this and not one of the site-indexed variants is
  where the tag is registered. The three site-indexed variants
  `SheafOfModules.DifferentialGradedModule.IsGood`, `IsGoodCocontinuousBaseChange` and
  `IsGoodSiteBaseChange` remain in the library as auxiliary definitions.
* `SheafOfModules.toposDirectImageModules`, `toposDirectImageModules_laxMonoidal` and
  `toposDirectImageModulesSetIso`: the direct image of sheaves of modules along a morphism of
  ringed topoi, with the two data the differential graded transport asks of it — a lax monoidal
  structure and the comparison `ν` — both unconditional.

## Main results

* `SheafOfModules.freeDGModuleToposHomEquiv_comp`: the bijection is natural in `Q`.
* `SheafOfModules.leftAdjointObjIsDefined_freeDGModule`: the direct image has a partial left
  adjoint defined at `A[S]`, in Mathlib's
  `CategoryTheory.Functor.leftAdjointObjIsDefined`. So the pullback of `A[S]` exists as a
  universal object without any global adjunction.
* `SheafOfModules.isoFreeDGModuleOfToposCorepresentableBy`: **any object corepresenting the same
  functor is isomorphic to `B[f⁻¹S]`**, by `Functor.CorepresentableBy.uniqueUpToIso`. This is
  what identifies every chosen pullback of `A[S]` with the free module on `f⁻¹S`.
* `SheafOfModules.isGradedFlat_isKFlat_of_toposCorepresentableBy`: **every object corepresenting
  the pullback of `A[S]` is flat as a graded module and K-flat** — the clause of condition (3) of
  Tag 0FSA for `A[S]` at the base change `(f, B, ψ)`, quantified over the chosen pullback rather
  than fixing one.
* `SheafOfModules.nonempty_corepresentableBy_and_flat`: the same clause with **existence
  included and not assumed** — a corepresenting pullback exists, and every one is flat and
  K-flat. A `Prop`, so it can be a conjunct of a goodness predicate.
* `SheafOfModules.freeDGModule_isGoodToposBaseChange`: **Tag 0FSG at the source's own
  quantification** — the free differential graded module `A[S]` on a sheaf of graded sets is good
  in the sense of `IsGoodToposBaseChange`.
* `SheafOfModules.IsGoodToposBaseChange.isGradedFlat`, `isKFlat` and `baseChange` expose the
  three conditions of Tag 0FSA to consumers.

## Implementation notes

The corepresentability is stated for the functor `f_{*,ψ} ⋙ coyoneda.obj (op A[S])`, which is
exactly Mathlib's shape, so `Functor.leftAdjointObjIsDefined`,
`Functor.partialLeftAdjointObj` and `Functor.CorepresentableBy.uniqueUpToIso` apply directly and
no bespoke uniqueness development is needed. `SheafOfModules.isoFreeDGModuleOfNatEquiv` of
`FreeDifferentialGradedModuleClosedSections.lean` remains available for a caller who has a bare
natural bijection, but the statements here go through the standard API.

The naturality of the composite is assembled from the naturality of its five steps: two uses of
`SheafOfModules.freeDGModuleHomToClosed_comp` and `freeDGModuleHomEquiv_symm_comp`, the
right-naturality of an adjunction's hom-set bijection, and
`closedSectionToposPushforwardIso_naturality`. The second step contributes nothing, being
independent of `Q`.

The hypotheses of the section are those of `DifferentialGradedToposDirectImage.lean`, with no
addition: `G` additive and lax monoidal, the comparison `ν`, and `ψ` unital. In particular there
is **no** functor between the two underlying categories, no continuity, no `Small` or
`EssentiallySmall`, and the two sites' universes are independent; the coefficient universe is
common to the two ringed topoi, which is that file's recorded boundary. The two
`HasSheafify _ (Type w)` instances are what let `Stacks.degreeFiberSheaf` be formed on each site,
and Mathlib supplies them at `Type (max u v)`.

`IsGoodToposBaseChange` quantifies none of `G`, its lax monoidal structure or `ν`: at a morphism
of ringed topoi all three are determined, `G` being `toposDirectImageModules` and `ν` the
identity, and the lax monoidal structure coming from
`Stacks.SheafOfModules.RingedToposPullback.pushforwardLaxMonoidal` at the coherence of Tag 03EL,
which `RingedToposPullbackCoherence.lean` proves. So condition (3) has a clause at each base
change the source has one at, and at no other.

**Where Tag 0FSA is registered, and why here.** Condition (3) of Tag 0FSA quantifies over
morphisms of ringed topoi `(f, f^#) : (Sh(C'), O') ⟶ (Sh(C), O)`, over a differential graded
`O'`-algebra `A'` and over a homomorphism `φ : f⁻¹A ⟶ A'`, and asks conditions (1) and (2) of
`f^*P` as a differential graded `A'`-module. `IsGoodToposBaseChange` has those binders and no
others, so the tag is registered on it, a definition carrying the definition of the tag. The
three site-indexed variants in `GoodDifferentialGradedModule.lean` and
`GoodDifferentialGradedSiteColimit.lean` quantify something else — a bare functor of the two
underlying categories, or a continuous one — and are auxiliary definitions, used by the
consumers already stated against them. The two halves of the tag for the regular module in
`DifferentialGradedRelativeTensorUnitor.lean` are conditions (1) and (2) of it, each one clause
of the definition, so neither carries the tag either.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.SheafOfGradedSets Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules

open DifferentialGradedModule

section ToposPullback

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J (Type w)]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [HasSheafify K (Type w)]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (ν : toSetSheaf (toRingCat J Osharp) ⋙ f.pushforward ≅
    G ⋙ toSetSheaf (toRingCat K Psharp))
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
  (S : SheafOfGradedSets.{w} K)

/-- **The per-degree step of the chain.** A morphism from the degree-`i` sections of `f⁻¹S` into
the closed degree-`i` sections of `Q` is a morphism from the degree-`i` sections of `S` into the
closed degree-`i` sections of the direct image: read the source through
`Stacks.inverseImageDegreeFiberIso`, transpose across `f⁻¹ ⊣ f_*`, and compare the closed
sections. -/
noncomputable def toposDegreeStep (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    (degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶ closedSectionSheaf Q i) ≃
      (degreeFiberSheaf S i ⟶
        closedSectionSheaf ((toposPushforward G ψ hψ).obj Q) i) :=
  (Iso.homCongr (inverseImageDegreeFiberIso f S i)
      (Iso.refl (closedSectionSheaf Q i))).symm.trans
    ((f.adj.homEquiv (degreeFiberSheaf S i) (closedSectionSheaf Q i)).trans
      (Iso.homCongr (Iso.refl (degreeFiberSheaf S i))
        (closedSectionToposPushforwardIso G f ν ψ hψ Q i)))

/-- `toposDegreeStep` sends `F` to the adjoint transpose of `F` precomposed with
`inverseImageDegreeFiberIso`, followed by `closedSectionToposPushforwardIso`. -/
@[simp]
theorem toposDegreeStep_apply (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ)
    (F : degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶ closedSectionSheaf Q i) :
    toposDegreeStep G f ν ψ hψ S Q i F =
      f.adj.homEquiv (degreeFiberSheaf S i) (closedSectionSheaf Q i)
          ((inverseImageDegreeFiberIso f S i).hom ≫ F) ≫
        (closedSectionToposPushforwardIso G f ν ψ hψ Q i).hom := by
  change (Iso.refl (degreeFiberSheaf S i)).inv ≫
      (f.adj.homEquiv (degreeFiberSheaf S i) (closedSectionSheaf Q i)
        ((inverseImageDegreeFiberIso f S i).hom ≫ F ≫
          (Iso.refl (closedSectionSheaf Q i)).inv)) ≫
        (closedSectionToposPushforwardIso G f ν ψ hψ Q i).hom = _
  rw [Iso.refl_inv, Iso.refl_inv, Category.comp_id, Category.id_comp]

/-- **The per-degree step is natural in `Q`.** -/
theorem toposDegreeStep_comp {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q') (i : ℤ)
    (F : degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶ closedSectionSheaf Q i) :
    toposDegreeStep G f ν ψ hψ S Q' i (F ≫ closedSectionMap g i) =
      toposDegreeStep G f ν ψ hψ S Q i F ≫
        closedSectionMap ((toposPushforward G ψ hψ).map g) i := by
  rw [toposDegreeStep_apply, toposDegreeStep_apply, Category.assoc,
    ← closedSectionToposPushforwardIso_naturality G f ν ψ hψ g i, ← Category.assoc,
    ← Category.assoc]
  refine congrArg (fun ϑ ↦ ϑ ≫ (closedSectionToposPushforwardIso G f ν ψ hψ Q' i).hom) ?_
  rw [← f.adj.homEquiv_naturality_right, Category.assoc]

/-- **The pullback of `A[S]` along `f` is the free module on `f⁻¹S`**, as a bijection of
hom-sets: a morphism `B[f⁻¹S] ⟶ Q` is a morphism `A[S] ⟶ f_{*,ψ}Q`. -/
noncomputable def freeDGModuleToposHomEquiv (Q : DifferentialGradedModule.{w, w, w} B) :
    (freeDGModule (SheafOfGradedSets.inverseImage f S) B ⟶ Q) ≃
      (freeDGModule S A ⟶ (toposPushforward G ψ hψ).obj Q) :=
  (freeDGModuleHomEquiv (SheafOfGradedSets.inverseImage f S) B Q).trans
    ((Equiv.piCongrRight (toposDegreeStep G f ν ψ hψ S Q)).trans
      (freeDGModuleHomEquiv S A ((toposPushforward G ψ hψ).obj Q)).symm)

/-- `freeDGModuleToposHomEquiv` applies `toposDegreeStep` in each degree to the closed sections
determined by a morphism out of the free module. -/
theorem freeDGModuleToposHomEquiv_apply (Q : DifferentialGradedModule.{w, w, w} B)
    (h : freeDGModule (SheafOfGradedSets.inverseImage f S) B ⟶ Q) :
    freeDGModuleToposHomEquiv G f ν ψ hψ S Q h =
      (freeDGModuleHomEquiv S A ((toposPushforward G ψ hψ).obj Q)).symm (fun i =>
        toposDegreeStep G f ν ψ hψ S Q i
          (freeDGModuleHomToClosed (SheafOfGradedSets.inverseImage f S) B Q h i)) :=
  rfl

/-- **The bijection is natural in `Q`.** Each of its three steps is. -/
theorem freeDGModuleToposHomEquiv_comp {Q Q' : DifferentialGradedModule.{w, w, w} B}
    (g : Q ⟶ Q') (h : freeDGModule (SheafOfGradedSets.inverseImage f S) B ⟶ Q) :
    freeDGModuleToposHomEquiv G f ν ψ hψ S Q' (h ≫ g) =
      freeDGModuleToposHomEquiv G f ν ψ hψ S Q h ≫ (toposPushforward G ψ hψ).map g := by
  rw [freeDGModuleToposHomEquiv_apply, freeDGModuleToposHomEquiv_apply,
    ← freeDGModuleHomEquiv_symm_comp]
  refine congrArg (freeDGModuleHomEquiv S A ((toposPushforward G ψ hψ).obj Q')).symm ?_
  refine funext fun i => ?_
  rw [freeDGModuleHomToClosed_comp, toposDegreeStep_comp]

/-- **The corepresentability witness.** `B[f⁻¹S]` corepresents
`Q ↦ Hom_A(A[S], f_{*,ψ}Q)`, which is the universal property of the pullback of `A[S]` at a
morphism of ringed topoi — constructed, not assumed. -/
noncomputable def freeDGModuleToposCorepresentableBy :
    ((toposPushforward G ψ hψ) ⋙
        coyoneda.obj (Opposite.op (freeDGModule S A))).CorepresentableBy
      (freeDGModule (SheafOfGradedSets.inverseImage f S) B) where
  homEquiv {Q} := freeDGModuleToposHomEquiv G f ν ψ hψ S Q
  homEquiv_comp g h := freeDGModuleToposHomEquiv_comp G f ν ψ hψ S g h

include f ν in
/-- **The direct image of differential graded modules has a partial left adjoint defined at
`A[S]`**, in the sense of Mathlib's `CategoryTheory.Functor.leftAdjointObjIsDefined`. So the
pullback of `A[S]` exists as a universal object, with no global adjunction assumed and no
uninhabited datum quantified over. -/
theorem leftAdjointObjIsDefined_freeDGModule :
    (toposPushforward G ψ hψ).leftAdjointObjIsDefined (freeDGModule S A) :=
  (freeDGModuleToposCorepresentableBy G f ν ψ hψ S).isCorepresentable

/-- **Every object corepresenting the pullback of `A[S]` is the free module on `f⁻¹S`.** This is
`Functor.CorepresentableBy.uniqueUpToIso`, so it applies in particular to the value at `A[S]` of
any global left adjoint of the direct image, through `Adjunction.corepresentableBy`. -/
noncomputable def isoFreeDGModuleOfToposCorepresentableBy
    {T : DifferentialGradedModule.{w, w, w} B}
    (e : ((toposPushforward G ψ hψ) ⋙
      coyoneda.obj (Opposite.op (freeDGModule S A))).CorepresentableBy T) :
    T ≅ freeDGModule (SheafOfGradedSets.inverseImage f S) B :=
  e.uniqueUpToIso (freeDGModuleToposCorepresentableBy G f ν ψ hψ S)

/-! ### Conditions (1) and (2) of Tag 0FSA for the pullback -/

section Flat

variable [HasSheafify J AddCommGrpCat.{w}]

omit [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}] in
/-- **The constructed pullback of `A[S]` is flat as a graded module and K-flat**: it is the free
differential graded `B`-module on `f⁻¹S`, and the first two paragraphs of the source's proof of
Tag 0FSG, which carry no hypotheses, apply to it over the source topos. -/
theorem isGradedFlat_isKFlat_freeDGModule_inverseImage :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded
        (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) ∧
      RelativeTensor.IsKFlat (freeDGModule (SheafOfGradedSets.inverseImage f S) B) :=
  ⟨freeDGModule_isGradedFlat B (SheafOfGradedSets.inverseImage f S),
    freeDGModule_isKFlat (SheafOfGradedSets.inverseImage f S) B⟩

include f ν in
/-- **Every object corepresenting the pullback of `A[S]` is flat as a graded module and K-flat.**
This is the clause of condition (3) of Tag 0FSA for `A[S]` at the base change `(f, B, ψ)`, in a
form that quantifies over the chosen pullback rather than fixing one: by
`Functor.CorepresentableBy.uniqueUpToIso` any such object is isomorphic to `B[f⁻¹S]`, and both
conditions transport along an isomorphism. -/
theorem isGradedFlat_isKFlat_of_toposCorepresentableBy
    {T : DifferentialGradedModule.{w, w, w} B}
    (e : ((toposPushforward G ψ hψ) ⋙
      coyoneda.obj (Opposite.op (freeDGModule S A))).CorepresentableBy T) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T) ∧
      RelativeTensor.IsKFlat T :=
  isGradedFlat_isKFlat_of_iso_freeDGModule (SheafOfGradedSets.inverseImage f S)
    (isoFreeDGModuleOfToposCorepresentableBy G f ν ψ hψ S e)

include f ν in
/-- **The clause of condition (3) of Tag 0FSA for `A[S]` at a geometric base change, with
existence included and not assumed**: a corepresenting pullback object exists, and every one of
them is flat as a graded module and K-flat. The existence half is `Nonempty` of the
corepresentability datum, so the statement is a `Prop` and can be a conjunct of a predicate. -/
theorem nonempty_corepresentableBy_and_flat :
    Nonempty (((toposPushforward G ψ hψ) ⋙
        coyoneda.obj (Opposite.op (freeDGModule S A))).CorepresentableBy
      (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) ∧
      ∀ {T : DifferentialGradedModule.{w, w, w} B},
        ((toposPushforward G ψ hψ) ⋙
          coyoneda.obj (Opposite.op (freeDGModule S A))).CorepresentableBy T →
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T) ∧
          RelativeTensor.IsKFlat T :=
  ⟨⟨freeDGModuleToposCorepresentableBy G f ν ψ hψ S⟩,
    fun e => isGradedFlat_isKFlat_of_toposCorepresentableBy G f ν ψ hψ S e⟩

end Flat

end ToposPullback

/-! ### The faithful reading of goodness, and `A[S]` at it -/

section Predicate

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

section DirectImage

variable {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]

/-- **The direct image of sheaves of modules along a morphism of ringed topoi, with its sheaves
of rings spelled `CategoryTheory.Sheaf.toRingCat`.** This is
`Stacks.Sheaves.RingedToposModules.pushforwardModules` and nothing else; the two spellings
`structureRingSheaf X` and `toRingCat X.J X.O` of the sheaf of rings are equal by `rfl`, and the
ascription is what lets the differential graded transport of
`DifferentialGradedToposDirectImage.lean`, which is typed at the `toRingCat` spelling, be applied
to it. -/
@[sga "4 V 5.0" "special case", sga "4 Vbis 1.3.6" "special case"]
noncomputable def toposDirectImageModules (f : RingedToposHom X Y) :
    SheafOfModules.{w} (toRingCat X.J X.O) ⥤ SheafOfModules.{w} (toRingCat Y.J Y.O) :=
  pushforwardModules f

/-- The direct image `toposDirectImageModules f` is an additive functor. -/
instance toposDirectImageModules_additive (f : RingedToposHom X Y) :
    (toposDirectImageModules f).Additive :=
  inferInstanceAs (pushforwardModules f).Additive

/-- **The direct image of sheaves of modules along a morphism of ringed topoi is lax monoidal**,
at the `toRingCat` spelling of the two sheaves of rings. This is
`Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal`, the coherence of
Tag 03EL being proved in `RingedToposPullbackCoherence.lean`; it carries no hypothesis. The
monoidal structure of Tag 01CA at the `toRingCat` spelling is
`Stacks.TensorSheafWorld.monoidalCategory` and at the `structureRingSheaf` spelling it is
`Stacks.Sheaves.RingedToposModules.structureMonoidalCategory`; the two are equal by `rfl`, which
is why this is a transport and not a construction. -/
@[instance_reducible]
noncomputable instance toposDirectImageModules_laxMonoidal (f : RingedToposHom X Y) :
    (toposDirectImageModules f).LaxMonoidal :=
  Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal f

/-- **The comparison `ν` for the geometric direct image is the identity**, at the `toRingCat`
spelling. This is `Stacks.Sheaves.RingedToposModules.toposPushforwardSetIso`. -/
noncomputable def toposDirectImageModulesSetIso (f : RingedToposHom X Y) :
    toSetSheaf (toRingCat X.J X.O) ⋙ f.toToposHom.pushforward ≅
      toposDirectImageModules f ⋙ toSetSheaf (toRingCat Y.J Y.O) :=
  toposPushforwardSetIso f

end DirectImage

/-- **A good right differential graded module**, with condition (3) read over the source's own
base changes. A right differential graded `A`-module is good when it is flat as a graded
module, K-flat, and for **every** base
change along a morphism of ringed topoi — a second ringed topos `X`, a morphism of ringed topoi
`f : X ⟶ Y`, a sheaf of differential graded algebras `B` on `X` and a **unital** homomorphism
`ψ : A ⟶ f_*B`, which is the adjoint form of the source's `φ : f⁻¹A ⟶ B` — a pullback of `P`
**exists**, as an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`, and every such object is flat
as a graded module and K-flat.

This is the quantification of Tag 0FSA's condition (3), binder for binder: a morphism of ringed
topoi, a differential graded algebra on its source, a homomorphism over it, and conditions (1)
and (2) required of the base-changed module. Nothing weaker and nothing stronger is quantified;
in particular condition (3) is **not** vacuous and **not** an assumption of the sought-for
isomorphism, the existential conjunct being part of the conclusion, and the second conjunct then
transports to every chosen pullback by `Functor.CorepresentableBy.uniqueUpToIso`.

The direct image of sheaves of modules is `toposDirectImageModules f`, whose lax monoidal
structure is `toposDirectImageModules_laxMonoidal` — unconditional, the coherence of Tag 03EL
being proved in `RingedToposPullbackCoherence.lean` — so the target `f_*B` of `ψ` is formed from
`f` alone and no monoidal datum is quantified beside it.

This is **not** `SheafOfModules.DifferentialGradedModule.IsGood` with its binders rewritten, and
the two are **incomparable**, which is why no implication between them is proved here in either
direction. `IsGood` quantifies bare functors of the two underlying categories: such a functor
induces no morphism of topoi and yet can carry a `PullbackData` — the identity functor of a site
at the trivial topology does, every presheaf being a sheaf there — so `IsGood` has clauses this
definition has none at. In the other direction a morphism of topoi need not be induced by any
functor of the two given sites, only by one of a site equivalent to the target (Tag 03CR, the
first step of the source's own proof of Tag 0FSB), so `IsGood` has no clause at such a base
change. What the two do share is conditions (1) and (2), verbatim; `isGradedFlat` and `isKFlat`
below are the comparison that exists.

`IsGoodCocontinuousBaseChange` and `IsGoodSiteBaseChange` restrict `IsGood`'s condition (3) to
fewer base changes, so each is implied by `IsGood` and each is incomparable with this definition
for the second of the two reasons above: a morphism of topoi induced by no functor of the two
given sites is a clause of this definition and of neither of theirs.

**Two restrictions on condition (3), stated rather than hidden.** First, the second ringed topos
carries `HasSheafify X.J (Type w)` and `HasSheafify X.J AddCommGrpCat.{w}`, together with the
three `GrothendieckTopology.HasSheafCompose` instances a morphism of ringed topoi and its direct
image need. The sheafification of abelian groups is what the relative tensor product of the
conclusion needs; the sheafification of types is what lets a sheaf of graded sets and its degree
fibres be formed there, and it is the instance the proof for `A[S]` consumes. Mathlib supplies
both at `Type (max u v)` for a site `C : Type u` with `[Category.{v} C]`, so they hold wherever
the source's sites live, but a reading of condition (3) *without* them would be strictly stronger
and this is not it. Second, the coefficient universe `w` is common to the two ringed topoi, where
`Stacks.Sheaves.RingedToposModules.RingedToposHom` allows them independent; that boundary comes
from the differential graded transport and is recorded in
`DifferentialGradedToposDirectImage.lean`. Neither restriction is a hypothesis on a functor
between the two underlying categories — there is none — and neither is a smallness assumption. -/
@[stacks 0FSA]
def IsGoodToposBaseChange (P : DifferentialGradedModule.{w, w, w} A) : Prop :=
  RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
    RelativeTensor.IsKFlat P ∧
      ∀ {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
        [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
        [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
        [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
        [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
        [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X.J (Type w)]
        (f : RingedToposHom X Y)
        (B : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O))
        (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital),
        (∃ T : DifferentialGradedModule.{w, w, w} B,
            Nonempty ((toposPushforward (toposDirectImageModules f) ψ hψ ⋙
              coyoneda.obj (Opposite.op P)).CorepresentableBy T)) ∧
          ∀ T : DifferentialGradedModule.{w, w, w} B,
            (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
                coyoneda.obj (Opposite.op P)).CorepresentableBy T →
              RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T) ∧
                RelativeTensor.IsKFlat T

namespace IsGoodToposBaseChange

variable {P : DifferentialGradedModule.{w, w, w} A}

omit [HasSheafify Y.J (Type w)] in
/-- **Condition (1).** The underlying graded module of a good right differential graded module is
flat. -/
theorem isGradedFlat (hP : IsGoodToposBaseChange.{w, v₁, u₁} P) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) :=
  hP.1

omit [HasSheafify Y.J (Type w)] in
/-- **Condition (2).** A good right differential graded module is K-flat. -/
theorem isKFlat (hP : IsGoodToposBaseChange.{w, v₁, u₁} P) : RelativeTensor.IsKFlat P :=
  hP.2.1

omit [HasSheafify Y.J (Type w)] in
/-- **Condition (3).** At every base change along a morphism of ringed topoi a pullback of a good
right differential graded module exists, as an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`,
and every such object is flat as a graded module and K-flat. -/
theorem baseChange (hP : IsGoodToposBaseChange.{w, v₁, u₁} P)
    {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X.J (Type w)]
    (f : RingedToposHom X Y)
    (B : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O))
    (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital) :
    (∃ T : DifferentialGradedModule.{w, w, w} B,
        Nonempty ((toposPushforward (toposDirectImageModules f) ψ hψ ⋙
          coyoneda.obj (Opposite.op P)).CorepresentableBy T)) ∧
      ∀ T : DifferentialGradedModule.{w, w, w} B,
        (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
            coyoneda.obj (Opposite.op P)).CorepresentableBy T →
          RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T) ∧
            RelativeTensor.IsKFlat T :=
  hP.2.2 f B ψ hψ

end IsGoodToposBaseChange

/-- **Tag 0FSG: the free differential graded module `A[S]` on a sheaf of graded sets is good**, at
the source's own quantification. Conditions (1) and (2) are the two unconditional theorems of
`FreeGradedModuleFlat.lean`; condition (3) is the corepresentability of `B[f⁻¹S]` together with
the flatness of every object corepresenting the same functor, which is
`SheafOfModules.nonempty_corepresentableBy_and_flat` at the geometric direct image. There is no
hypothesis beyond those under which `A[S]` exists. -/
@[stacks 0FSG "the free differential graded module on a sheaf of graded sets is good, with \
condition (3) of 0FSA read over morphisms of ringed topoi"]
theorem freeDGModule_isGoodToposBaseChange [HasWeakSheafify Y.J (Type w)]
    (S : Stacks.SheafOfGradedSets.{w} Y.J) :
    IsGoodToposBaseChange.{w, v₁, u₁} (freeDGModule S A) := by
  refine ⟨freeDGModule_isGradedFlat A S, freeDGModule_isKFlat S A, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  obtain ⟨hex, hflat⟩ := nonempty_corepresentableBy_and_flat (toposDirectImageModules f)
    f.toToposHom (toposDirectImageModulesSetIso f) ψ hψ S
  exact ⟨⟨_, hex⟩, fun _ e => hflat e⟩

end Predicate


end SheafOfModules

end
