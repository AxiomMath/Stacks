module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceTensorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.BourbakiFiniteTypePointwise
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Bourbaki's formula for a finite type module flat over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `F` be a finite type quasi-coherent `𝒪_X`-module which is flat over `Y`, and let `G`
be a quasi-coherent `𝒪_Y`-module. Stacks 0CVL asserts the set equality

`WeakAss_X(F ⊗_{𝒪_X} f^*G) = Ass_{X/Y}(F) ∩ |f|^{-1}(WeakAss_Y(G))`.

The source proves it in one line, as an immediate consequence of its pointwise form,
Stacks 0CVK, and that is how it is proved here. The pointwise form is proved, under exactly
the hypotheses of this tag, as
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType` of
`StacksFrontier.AlgebraicGeometry.Spaces.Flat.BourbakiFiniteTypePointwise`.

One thing makes the passage from the pointwise form to the set equality more than a
restatement: Stacks 0CVK asks for flatness of `F` over `Y` *at the point being tested*, while
the tag assumes `F` flat over `Y` outright, in the chartwise sense of Stacks 05VV. The two are
reconciled by `AlgebraicGeometry.Space.isFlatOverAtPoint_forall_of_isFlatOver`: every point of
`|X|` is carried by the source chart of some commuting square of étale scheme charts over `f`,
and on such a square the global condition is the pointwise one at every point of that chart.

## Main definitions

* `AlgebraicGeometry.Space.IsBourbakiFormulaAtFlatPoints` is the pointwise formula of
  Stacks 0CVK for `f`, `F` and `G`: at every point of `|X|` at which `F` is flat over `Y`, the
  point is weakly associated to `F ⊗_{𝒪_X} f^*G` exactly when it lies in `WeakAss_{X/Y}(F)`
  above a weakly associated point of `G`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtPoint_forall_of_isFlatOver`: a module flat over the
  target is flat over the target at every point of the source.
* `AlgebraicGeometry.Space.isBourbakiFormulaAtFlatPoints_of_finiteType`: the pointwise formula
  holds under the hypotheses of this tag, which is Stacks 0CVK with its two conjuncts in the
  order the source writes them.
* `AlgebraicGeometry.Space.isBourbakiFormulaAtFlatPoints_of_chart`: the pointwise formula
  descends from a surjective étale chart, which is the étale-localization step of the source's
  proof of Stacks 0CVK.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_tensor_modulePullback_eq_inter_preimage`:
  **Stacks 0CVL**, the set equality, from the pointwise formula.

## Implementation notes

Flatness over the target is `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV and its
pointwise form `AlgebraicGeometry.Space.IsFlatOverAtPoint`, both read on the commuting squares
of étale scheme charts, which is the only form in which a module on an algebraic space is
compared with a module on a scheme here. Quasi-coherence is
`SheafOfModules.IsQuasicoherentOnSite` of Stacks 03DL(6) and finite type is
`SheafOfModules.IsFiniteType`, local generation by finitely many sections; both are instances,
as elsewhere in the development.

The right-hand side is written as an intersection with a preimage, as the tag writes it. Its
first factor is `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints` of Stacks 0CV0, the
set the source writes `Ass_{X/Y}(F)` once the fibres of `f` are locally Noetherian — which they
are here, `f` being locally of finite type, by Stacks 0CUY — and its second is the preimage of
`AlgebraicGeometry.Space.weaklyAssociatedPoints` of Stacks 0CTX. Neither set presupposes local
Noetherianity to be formed, so no such hypothesis is imposed.

`AlgebraicGeometry.Space.IsBourbakiFormulaAtFlatPoints` writes the two conjuncts of the
pointwise formula in the order of the source, `WeakAss_{X/Y}(F)` first, whereas Stacks 0CVK is
stated with the base condition first; the two differ by `and_comm` and by nothing else, the
membership predicates of the two sets being the abbreviations of their defining conditions.

The local-finite-type hypothesis `hf` of the tag is exactly the one Stacks 0CVK carries, and the
others — finite type and quasi-coherence of `F`, quasi-coherence of `G` — are the instances
above; the tag's flatness hypothesis is what turns the pointwise flatness side condition of
Stacks 0CVK into something available at every point. Nothing in the passage to the set equality
uses the hypotheses further.

The tensor product is `AlgebraicGeometry.Space.modulesMonoidalCategory`, the tensor product of
Stacks 01CA on the small étale ringed site, activated as a local instance; the module universe
is that of the structure rings, the only one at which both that tensor product and Stacks 0CUU
exist, so the chart descent below lives there too.

## References

* [Stacks Project, Tag 0CVL](https://stacks.math.columbia.edu/tag/0CVL)
* [Stacks Project, Tag 0CVK](https://stacks.math.columbia.edu/tag/0CVK)
* [Stacks Project, Tag 0CV1](https://stacks.math.columbia.edu/tag/0CV1)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flatness over the target at every point -/

/-- A module flat over the target is flat over the target at every point of the source.

Every point of `|X|` is the image of a point of the source chart of some commuting square of
étale scheme charts, by `AlgebraicGeometry.Space.exists_chartDiagram_pointOfEtaleChart`, and on
such a square flatness over the target chart is asked at every point of the source chart, which
is `AlgebraicGeometry.Space.isFlatOverAtPoint_of_isFlatOver`. -/
theorem isFlatOverAtPoint_forall_of_isFlatOver {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (h : IsFlatOver B S hS hX f F)
    (x : points B S hS X) :
    IsFlatOverAtPoint B S hS hX f F x := by
  obtain ⟨d, u, hu⟩ := exists_chartDiagram_pointOfEtaleChart B S hS hX hY f x
  subst hu
  exact isFlatOverAtPoint_of_isFlatOver hX F h d u

/-! ### The pointwise formula -/

attribute [local instance] modulesMonoidalCategory

variable {X X' Y : AlgebraicSpaces B S hS}

/-- The pointwise formula of **Stacks 0CVK** for a morphism `f : X ⟶ Y` of algebraic spaces, an
`𝒪_X`-module `F` and an `𝒪_Y`-module `G`: at every point of `|X|` at which `F` is flat over `Y`,
the point is weakly associated to `F ⊗_{𝒪_X} f^*G` exactly when it lies in the relative weak
assassin `WeakAss_{X/Y}(F)` and its image is weakly associated to `G`.

Flatness is read as `AlgebraicGeometry.Space.IsFlatOverAtPoint`, the pointwise form of
Stacks 05VV, which is the shape in which the source hypothesises it. -/
noncomputable abbrev IsBourbakiFormulaAtFlatPoints (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2) : Prop :=
  ∀ x : points B S hS X.1, IsFlatOverAtPoint B S hS X.2 f.hom F x →
    (IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G) x ↔
      (IsRelativeWeaklyAssociatedPoint B S hS f F x ∧
        IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x)))

/-- **The pointwise formula of Stacks 0CVK holds under the hypotheses of Stacks 0CVL.** This is
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType`, whose
right-hand side differs from the one here only in the order of its two conjuncts. -/
theorem isBourbakiFormulaAtFlatPoints_of_finiteType (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] [G.IsQuasicoherentOnSite] :
    IsBourbakiFormulaAtFlatPoints B S hS f F G := fun x hx =>
  (isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType B S hS f hf F G x hx).trans
    and_comm

/-- **The étale-localization step of the source's proof of Stacks 0CVK.** The pointwise formula
descends from a surjective étale chart `φ : X' ⟶ X`: the left-hand condition transfers by
Stacks 0CUU, once `φ^*(F ⊗ f^*G)` is identified with `φ^*F ⊗ (φ ≫ f)^*G` by Stacks 03EL; the
relative half of the right-hand condition transfers by Stacks 0CUZ, and its other half is
unchanged because `φ` lies over `Y`.

The chart formula `hchart` is asked only where `F` is flat over `Y`, as Stacks 0CVK asks it, the
flatness being read at the image point in `|X|`, which is where the library's Stacks 05VV
predicate for `F` is stated. -/
theorem isBourbakiFormulaAtFlatPoints_of_chart (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hsurj : Function.Surjective (pointsMap B S hS X'.1 φ.hom))
    (hchart : ∀ x : points B S hS X'.1,
      IsFlatOverAtPoint B S hS X.2 f.hom F (pointsMap B S hS X'.1 φ.hom x) →
        (IsWeaklyAssociatedPoint B S hS X'
            ((modulePullback B S hS φ).obj F ⊗
              (modulePullback B S hS (φ ≫ f)).obj G) x ↔
          (IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f)
              ((modulePullback B S hS φ).obj F) x ∧
            IsWeaklyAssociatedPoint B S hS Y G
              (pointsMap B S hS X'.1 (φ ≫ f).hom x)))) :
    IsBourbakiFormulaAtFlatPoints B S hS f F G := by
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← isWeaklyAssociatedPoint_tensor_modulePullback_iff B S hS φ hφ f F G y, hchart y hx,
    isRelativeWeaklyAssociatedPoint_and_mem_modulePullback_iff B S hS φ hφ f F G y]

/-! ### Bourbaki's formula as a set equality -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of
finite type, let `F` be a finite type quasi-coherent `𝒪_X`-module which is flat over `Y`, and let
`G` be a quasi-coherent `𝒪_Y`-module. Then the weakly associated points of `F ⊗_{𝒪_X} f^*G` are
exactly the points of `Ass_{X/Y}(F)` lying over weakly associated points of `G`.

This is the source's own proof, which is that the statement is an immediate consequence of its
pointwise form, Stacks 0CVK, available here as
`AlgebraicGeometry.Space.isBourbakiFormulaAtFlatPoints_of_finiteType`. The tag's flatness
hypothesis is what makes the pointwise flatness side condition hold at every point, by
`AlgebraicGeometry.Space.isFlatOverAtPoint_forall_of_isFlatOver`. -/
@[stacks 0CVL "the full set equality, in the intersection-with-a-preimage form the tag writes, \
under the tag's own assumptions and with the source's own proof: the statement is an immediate \
consequence of its pointwise form, Stacks 0CVK, proved in its own generality as \
Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType and is applied here \
through Space.isBourbakiFormulaAtFlatPoints_of_finiteType, the two differing by and_comm. The \
sets are Space.relativeWeaklyAssociatedPoints of Stacks 0CV0, the Ass_{X/Y}(F) of the tag once \
the fibres of f are locally Noetherian as they are here by Stacks 0CUY, and \
Space.weaklyAssociatedPoints of Stacks 0CTX. The tag's flatness assumption hF is used, through \
Space.isFlatOverAtPoint_forall_of_isFlatOver, to discharge the pointwise flatness side \
condition of Stacks 0CVK at every point. Nothing beyond the tag's own assumptions is used: \
every binder of this theorem is one of them, namely f locally of finite type, F \
quasi-coherent of finite type, G quasi-coherent, and F flat over Y"]
theorem weaklyAssociatedPoints_tensor_modulePullback_eq_inter_preimage (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] [G.IsQuasicoherentOnSite]
    (hF : IsFlatOver B S hS X.2 f.hom F) :
    weaklyAssociatedPoints B S hS X (F ⊗ (modulePullback B S hS f).obj G) =
      relativeWeaklyAssociatedPoints B S hS f F ∩
        pointsMap B S hS X.1 f.hom ⁻¹' weaklyAssociatedPoints B S hS Y G :=
  Set.ext fun x ↦ isBourbakiFormulaAtFlatPoints_of_finiteType B S hS f hf F G x
    (isFlatOverAtPoint_forall_of_isFlatOver B S hS X.2 Y.2 f.hom F hF x)

end AlgebraicGeometry.Space

end
