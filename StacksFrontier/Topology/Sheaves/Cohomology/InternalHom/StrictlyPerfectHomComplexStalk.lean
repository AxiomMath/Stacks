module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectTermStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of the internal Hom complex of a strictly perfect complex

Let `Rc` be a sheaf of commutative rings on a topological space `X`, write `O_X` for the
underlying sheaf of rings, let `E` and `F` be complexes of `O_X`-modules and let `x ∈ X`. This
file identifies the stalk at `x` of the internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z
with the naive Hom complex of the complexes of stalks over the stalk ring `O_{X,x}`, in two
independent halves.

**Degreewise.** For `E` bounded with every term a finite free summand,
`sheafHomComplexStalkDegreeEquiv` is an `O_{X,x}`-linear equivalence

`SheafHom(E, F)^n_x ≃ ⨁_q (E^{-q}_x →ₗ[O_{X,x}] F^{n-q}_x)`.

It is the composite of the degreewise direct-sum description of Stacks 08DM
(`strictlyPerfectHomDegreeIso`, which needs only boundedness of `E`), of Stacks 01AH for the
stalk of a coproduct (`modStalkCoprodEquiv`, which needs nothing), and of Stacks 01CP at each
summand (`internalHomSheafStalkEquivOfIsFiniteFreeSummand`, which is where the condition on the
terms of `E` enters).

**As a complex.** `sheafHomComplexStalkChainMap` is a morphism of complexes

`SheafHom(E, F)_x ⟶ Hom^•_{O_{X,x}}(E_x, F_x)`,

with **no hypothesis on `E` or `F`**. Its degree-`n` component sends the germ of a local cochain
of homomorphisms `E|_U ⟶ F|_U` to the cochain of the induced maps on stalks, and the content is
that these commute with the differentials.

## Main definitions

* `Stacks.SheafOfModules.SheafHomStalk.modStalkCoprodEquiv`: the stalk of a coproduct of
  `O_X`-modules, indexed by a type in `Type 0`, is the direct sum of the stalks, as an
  `O_{X,x}`-linear equivalence. This is Stacks 01AH read through
  `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, generalized from the
  `Type u`-indexed `SheafOfModules.stalkCoprodEquiv` to an index type in `Type 0`, which is what
  a coproduct over `ℤ` needs.
* `Stacks.SheafOfModules.SheafHomStalk.modStalkMapEquiv`: the stalk of an isomorphism of
  `O_X`-modules, as a linear equivalence of stalks.
* `Stacks.SheafOfModules.modStalkComplex`: **the complex of stalks** of a complex of
  `O_X`-modules, as a complex of `O_{X,x}`-modules. This exists because the stalk functor is
  additive (`AlgebraicGeometry.SheafOfModules.stalkFunctor_additive`).
* `Stacks.SheafOfModules.SheafHomStalk.cochainStalk`: the stalk of a degree-`n` cochain of
  homomorphisms of the restrictions to an open neighbourhood of `x`.
* `Stacks.SheafOfModules.sheafHomComplexStalkComparison`,
  `Stacks.SheafOfModules.sheafHomComplexStalkChainMap`: the comparison of complexes, for an
  arbitrary realization of the internal Hom complex and for the canonical one.

## Main results

* `Stacks.SheafOfModules.sheafHomComplexStalkDegreeEquiv`: the degreewise identification.
* `Stacks.SheafOfModules.SheafHomStalk.cochainStalk_δ`: **the differential assembly.** Taking
  the stalk of a cochain commutes with the Hom-complex differential `δ`. The differential of a
  Hom complex is the signed sum of a postcomposition and a precomposition map, so this rests on
  taking stalks of local homomorphisms being additive (`stalkLinearMap_add`), compatible with
  integer multiples (`stalkLinearMap_zsmul`), functorial (`stalkLinearMap_comp`) and carrying
  the restriction of a global homomorphism to its stalk (`stalkLinearMap_over`).

## Implementation notes

**Which comparison the differentials are assembled along.** The degreewise equivalence and the
comparison of complexes are built along *different* routes, and are not shown to agree *in this
file*. The comparison of complexes goes through `SheafHomComplex.sectionsIso` directly — which
*is* an isomorphism of complexes, so the commutation with differentials reduces to
`cochainStalk_δ` — and through `SheafHomComplex.restrict_natural`, which is what makes the
degreewise comparison descend from sections over a neighbourhood to the stalk. What is
consequently not available here is that `sheafHomComplexStalkChainMap` is an isomorphism: that
needs the degreewise comparison to be identified with `sheafHomComplexStalkDegreeEquiv`.
`strictlyPerfectHomDegreeIso` is `public` but not `@[expose]`, so it cannot be unfolded for
that; what it is instead computed with are
`AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection` and
`AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection_of_ne`, which
say that its inverse carries the `q`-th coproduct inclusion to the `q`-th projection
`homDegreeProjection` and kills the others, and so determine it.

That identification is carried out downstream, in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomComplexStalkIso`:
`Stacks.SheafOfModules.homComplexStalkCochainMap_v` is the agreement — the `(-q, n-q)`
component of the degreewise comparison is Stacks 01CP at the `q`-th term applied to the stalk
map of `homDegreeProjection X E F n q`, which are exactly the two ingredients of
`sheafHomComplexStalkDegreeEquiv` — and
`Stacks.SheafOfModules.isIso_sheafHomComplexStalkChainMap` concludes that
`sheafHomComplexStalkChainMap` is an isomorphism for `E` bounded with every term a direct
summand of a finite free module. Its surjectivity half uses the product half of the stalk/limit
interchange, `Stacks.SheafOfModules.sheafHomDegreeStalkProdEquiv` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomComplexStalkProduct`.

**The index type of the coproduct.** `SheafOfModules.stalkCoprodEquiv` is stated for a family
indexed by `ι : Type u` with the space in `TopCat.{u}`, and `SheafOfModules.natStalkCoprodEquiv`
repeats the chain for `ι = ℕ`. The coproduct of Stacks 08DM is indexed by `ℤ`, which is in
`Type 0`; rather than pin the space at `TopCat.{0}` or repeat the chain a third time, the chain
is given here once for an arbitrary `ι : Type 0` with the space in `TopCat.{u}`, with
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` moving Stacks 01AH from shapes in
`Type u` to `Discrete ι`. Nothing is narrowed, since `max 0 u = u`.

**The target of the comparison is `AddCommGrpCat`-valued.** `CochainComplex.HomComplex` takes
values in complexes of abelian groups even for complexes of modules, the linearity being
recorded in its terms: a degree-`n` term of `Hom^•_{O_{X,x}}(E_x, F_x)` is a family of
`O_{X,x}`-linear maps. So the source of the comparison is the complex of stalks with its module
structure forgotten, `modStalkAbComplex`. This is exactly the shape of
`SheafHomComplex.sectionsIso`, whose source `sectionComplex` is likewise `AddCommGrpCat`-valued.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry DirectSum

-- The structure sheaf of rings of a ringed space is a single definition whose body stops at an
-- explicit-constructor projection, so the module structures on stalks below need this Mathlib
-- definition unfolded to be found by instance search. The same attribute is set, for the same
-- reason, in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded`.
attribute [local instance_reducible] CategoryTheory.sheafCompose

universe u

namespace Stacks.SheafOfModules.SheafHomStalk

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

/-! ### The stalk of an isomorphism of sheaves of modules -/

section Iso

variable {M N : SheafOfModules.{u} (structureSheaf Rc)}

/-- The stalk at `x` of an isomorphism of `O_X`-modules, as an `O_{X,x}`-linear equivalence of
stalks. -/
def modStalkMapEquiv (e : M ≅ N) (x : X) : modStalk M x ≃ₗ[ringStalk Rc x] modStalk N x :=
  LinearEquiv.ofLinearMap (modStalkMap e.hom x) (modStalkMap e.inv x)
    (by rw [← modStalkMap_comp, e.inv_hom_id, modStalkMap_id])
    (by rw [← modStalkMap_comp, e.hom_inv_id, modStalkMap_id])

/-- The stalk equivalence of an isomorphism `e` acts as the stalk map of `e.hom`. -/
@[simp]
lemma modStalkMapEquiv_apply (e : M ≅ N) (x : X) (t : modStalk M x) :
    modStalkMapEquiv e x t = modStalkMap e.hom x t := rfl

/-- The stalk map of `SheafHomStalk` is the action of the stalk functor on sheaves of modules.
The two spellings differ only in the scalar ring recorded — `CommRingCat`-valued on the left,
`RingCat`-valued on the right — and both send a germ to the germ of the image. -/
lemma modStalkMap_eq_stalkFunctor_map (f : M ⟶ N) (x : X) (t : modStalk M x) :
    modStalkMap f x t =
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheaf Rc) x).map f).hom t := by
  obtain ⟨U, hxU, s, rfl⟩ := exists_germ_eq M t
  rw [modStalkMap_germ f x U hxU s]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((PresheafOfModules.toPresheaf (structureSheaf Rc).obj).map f.val) s).symm

end Iso

/-! ### The stalk of a small coproduct -/

section Coproduct

variable {ι : Type} [DecidableEq ι]
  (P : ι → SheafOfModules.{u} (structureSheaf Rc)) (x : X)

/-- A family of `O_X`-modules indexed by a type in `Type 0` has a coproduct. -/
instance : HasCoproduct P := inferInstance

/-- The canonical comparison from the direct sum of the stalks to the stalk of the coproduct. -/
def modStalkCoprodComparison :
    (⨁ i : ι, modStalk (P i) x) →ₗ[ringStalk Rc x] modStalk (∐ P) x :=
  DirectSum.toModule _ ι _ fun i => modStalkMap (Sigma.ι P i) x

/-- The comparison map sends the `i`-th summand to the stalk of the `i`-th coproduct
inclusion. -/
lemma modStalkCoprodComparison_of (i : ι) (t : modStalk (P i) x) :
    modStalkCoprodComparison P x (DirectSum.of _ i t) = modStalkMap (Sigma.ι P i) x t := by
  rw [← DirectSum.lof_eq_of (ringStalk Rc x)]
  exact DirectSum.toModule_lof (M := fun i => modStalk (P i) x) _ i t

/-- The image under the stalk functor of the coproduct cofan is a colimit cofan. This is
Stacks 01AH, `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, transported
from shapes in `Type u` to `Discrete ι` with `ι : Type 0` by
`CategoryTheory.Limits.preservesColimitsOfSize_shrink`; nothing is narrowed, since
`max 0 u = u`. -/
def modStalkCoprodIsColimit :
    IsColimit ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheaf Rc) x).mapCocone (Cofan.mk (∐ P) (Sigma.ι P))) := by
  letI : PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheaf Rc) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits _ _
  letI : PreservesColimitsOfSize.{0, 0} (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheaf Rc) x) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact isColimitOfPreserves _ (coproductIsCoproduct P)

/-- The stalk of the coproduct, identified with the direct sum of the stalks in `ModuleCat` over
the `RingCat`-valued stalk of the sheaf of rings. -/
def modStalkCoprodModuleIso :
    AlgebraicGeometry.SheafOfModules.stalkObj (structureSheaf Rc) x (∐ P) ≅
      ModuleCat.of ↑(TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheaf Rc).obj x)
        (⨁ i : ι, modStalk (P i) x) :=
  IsColimit.coconePointsIsoOfNatIso (modStalkCoprodIsColimit P x)
    (ModuleCat.coproductCoconeIsColimit
      (fun i : ι => AlgebraicGeometry.SheafOfModules.stalkObj (structureSheaf Rc) x (P i)))
    (Discrete.natIso fun _ => Iso.refl _)

/-- The inverse of `modStalkCoprodModuleIso` sends the `i`-th summand to the stalk of the `i`-th
coproduct inclusion. -/
lemma modStalkCoprodModuleIso_inv_of (i : ι) (t : modStalk (P i) x) :
    (modStalkCoprodModuleIso P x).inv.hom (DirectSum.of _ i t) =
      modStalkMap (Sigma.ι P i) x t := by
  have h := IsColimit.comp_coconePointsIsoOfNatIso_inv (modStalkCoprodIsColimit P x)
    (ModuleCat.coproductCoconeIsColimit
      (fun i : ι => AlgebraicGeometry.SheafOfModules.stalkObj (structureSheaf Rc) x (P i)))
    (Discrete.natIso fun _ => Iso.refl _) ⟨i⟩
  refine Eq.trans (congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f t) h) ?_
  exact (modStalkMap_eq_stalkFunctor_map (Sigma.ι P i) x t).symm

/-- The inverse of `modStalkCoprodModuleIso`, as an additive map whose codomain is spelled
`modStalk (∐ P) x` rather than `AlgebraicGeometry.SheafOfModules.stalkObj _ x (∐ P)`. The
ascribed type is the point: the two spellings are definitionally equal but a goal mixing them is
not type-correct at `implicit` transparency, so neither `rw` nor `simp` will accept it. -/
def modStalkCoprodAddHom : (⨁ i : ι, modStalk (P i) x) →+ modStalk (∐ P) x :=
  (modStalkCoprodModuleIso P x).inv.hom.toAddMonoidHom

/-- `modStalkCoprodAddHom` sends the `i`-th summand to the stalk of the `i`-th coproduct
inclusion. -/
lemma modStalkCoprodAddHom_of (i : ι) (t : modStalk (P i) x) :
    modStalkCoprodAddHom P x (DirectSum.of _ i t) = modStalkMap (Sigma.ι P i) x t :=
  modStalkCoprodModuleIso_inv_of P x i t

/-- The comparison from the direct sum of the stalks to the stalk of the coproduct is bijective. -/
theorem bijective_modStalkCoprodComparison :
    Function.Bijective (modStalkCoprodComparison P x) := by
  have key : (modStalkCoprodComparison P x).toAddMonoidHom = modStalkCoprodAddHom P x :=
    DirectSum.addHom_ext (β := fun i => modStalk (P i) x) fun i y =>
      (modStalkCoprodComparison_of P x i y).trans (modStalkCoprodAddHom_of P x i y).symm
  have h : Function.Bijective ((modStalkCoprodComparison P x).toAddMonoidHom) :=
    key ▸ ConcreteCategory.bijective_of_isIso (modStalkCoprodModuleIso P x).inv
  exact h

/-- The stalk at `x` of a coproduct of `O_X`-modules indexed by a type in `Type 0` is the direct
sum of the stalks, as an `O_{X,x}`-linear equivalence. -/
def modStalkCoprodEquiv : (⨁ i : ι, modStalk (P i) x) ≃ₗ[ringStalk Rc x] modStalk (∐ P) x :=
  LinearEquiv.ofBijective _ (bijective_modStalkCoprodComparison P x)

/-- `modStalkCoprodEquiv` sends the `i`-th summand to the stalk of the `i`-th coproduct
inclusion. -/
@[simp]
lemma modStalkCoprodEquiv_of (i : ι) (t : modStalk (P i) x) :
    modStalkCoprodEquiv P x (DirectSum.of _ i t) = modStalkMap (Sigma.ι P i) x t :=
  modStalkCoprodComparison_of P x i t

end Coproduct

/-! ### Direct sums along a family of linear equivalences -/

/-- A family of linear equivalences induces a linear equivalence of direct sums. -/
def directSumLequivOfFamily {R : Type*} [Semiring R] {ι : Type*}
    {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (e : ∀ i, M i ≃ₗ[R] N i) : (⨁ i, M i) ≃ₗ[R] ⨁ i, N i :=
  LinearEquiv.ofBijective (DirectSum.lmap (fun i => (e i).toLinearMap))
    ⟨(DirectSum.lmap_injective _).2 fun i => (e i).injective,
      (DirectSum.lmap_surjective _).2 fun i => (e i).surjective⟩

/-- `directSumLequivOfFamily e` sends `of M i t` to `of N i (e i t)`. -/
@[simp]
lemma directSumLequivOfFamily_of {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (e : ∀ i, M i ≃ₗ[R] N i) (i : ι) (t : M i) :
    directSumLequivOfFamily e (DirectSum.of M i t) = DirectSum.of N i (e i t) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (e i))

end Stacks.SheafOfModules.SheafHomStalk

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  (E F : CochainComplex (StructureSheafModules Rc) ℤ)

/-- **The stalk of the internal Hom complex, degreewise.** For `E` bounded with every term a
finite free summand and `F` arbitrary, the stalk at `x` of the degree-`n` term of the internal
Hom complex `SheafHom(E, F)` is the direct sum over `q : ℤ` of the modules of
`O_{X,x}`-linear maps `E^{-q}_x → F^{n-q}_x`.

The three steps are: the degreewise direct-sum description `strictlyPerfectHomDegreeIso` of
Stacks 08DM, which needs only boundedness of `E`; the spelling bridge
`modStalkCoprodEquiv`, that is Stacks 01AH, which needs nothing; and Stacks 01CP at each
summand, `internalHomSheafStalkEquivOfIsFiniteFreeSummand`, which is where the condition on the
terms of `E` enters. -/
def sheafHomComplexStalkDegreeEquiv
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i))
    (n : ℤ) (x : X) :
    modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x
        ≃ₗ[ringStalk Rc x]
      ⨁ q : ℤ, (modStalk (E.X (-q)) x →ₗ[ringStalk Rc x] modStalk (F.X (n - q)) x) :=
  (modStalkMapEquiv (strictlyPerfectHomDegreeIso Rc E F hE n) x).trans
    ((modStalkCoprodEquiv
        (fun q : ℤ => RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q)))
        x).symm.trans
      (directSumLequivOfFamily fun q : ℤ =>
        internalHomSheafStalkEquivOfIsFiniteFreeSummand Rc (E.X (-q)) (F.X (n - q))
          (hterm (-q)) x))

end Stacks.SheafOfModules

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry DirectSum CochainComplex.HomComplex

universe u

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

section StalkComplex

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

/-- **The complex of stalks.** The stalk at `x` of a complex of `O_X`-modules, taken degreewise,
as a complex of modules over the stalk ring `O_{X,x}`. -/
def modStalkComplex (K : CochainComplex (StructureSheafModules Rc) ℤ) (x : X) :
    CochainComplex (ModuleCat.{u} (ringStalk Rc x)) ℤ where
  X n := ModuleCat.of _ (modStalk (K.X n) x)
  d n m := ModuleCat.ofHom (modStalkMap (K.d n m) x)
  shape n m h := by
    rw [K.shape n m h, modStalkMap_zero]
    rfl
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    change (modStalkMap (K.d m k) x).comp (modStalkMap (K.d n m) x) = _
    rw [← modStalkMap_comp, K.d_comp_d, modStalkMap_zero]
    rfl

/-- The degree-`n` term of `modStalkComplex K x` is the stalk at `x` of `K.X n`. -/
@[simp]
lemma modStalkComplex_X (K : CochainComplex (StructureSheafModules Rc) ℤ) (x : X) (n : ℤ) :
    (modStalkComplex K x).X n = ModuleCat.of _ (modStalk (K.X n) x) := rfl

/-- The differential of `modStalkComplex K x` is the stalk map of the differential of `K`. -/
@[simp]
lemma modStalkComplex_d (K : CochainComplex (StructureSheafModules Rc) ℤ) (x : X) (n m : ℤ) :
    (modStalkComplex K x).d n m = ModuleCat.ofHom (modStalkMap (K.d n m) x) := rfl

/-- The complex of stalks with the module structure forgotten. This is the source of the
comparison with the naive Hom complex, exactly as `sectionComplex` is the source of
`SheafHomComplex.sectionsIso`: `CochainComplex.HomComplex` is `AddCommGrpCat`-valued even for
complexes of modules, the linearity being recorded in its terms. -/
def modStalkAbComplex (K : CochainComplex (StructureSheafModules Rc) ℤ) (x : X) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  ((forget₂ (ModuleCat.{u} (ringStalk Rc x)) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (modStalkComplex K x)

end StalkComplex

namespace SheafHomStalk

/-! ### Composition, zero and restriction for the stalk of a local homomorphism -/

section Components

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {A B C : SheafOfModules.{u} (structureSheaf Rc)}

/-- Evaluating a composite of local homomorphisms on sections over `W` is the composite of the
evaluations. -/
lemma appAt_comp {U W : Opens X} (hWU : W ≤ U) (φ : A.over U ⟶ B.over U)
    (ψ : B.over U ⟶ C.over U) (t : (commVal (Rc := Rc) A).obj (op W)) :
    appAt hWU (φ ≫ ψ) t = appAt hWU ψ (appAt hWU φ t) := rfl

/-- The zero local homomorphism evaluates to zero on every section. -/
lemma appAt_zero_hom {U W : Opens X} (hWU : W ≤ U)
    (t : (commVal (Rc := Rc) A).obj (op W)) :
    appAt hWU (0 : A.over U ⟶ B.over U) t = 0 := rfl

/-- Evaluating the restriction `f.over U` of a global homomorphism on sections over `W ≤ U` is
evaluating `f` on sections over `W`. -/
lemma appAt_over {U W : Opens X} (hWU : W ≤ U) (f : A ⟶ B)
    (t : (commVal (Rc := Rc) A).obj (op W)) :
    appAt hWU (f.over U) t = f.val.app (op W) t := rfl

/-- Two linear maps out of a stalk at `x ∈ U` agree if they agree on germs of sections over
opens `W ≤ U`. -/
private lemma linearMap_ext_of_le {U : Opens X} {x : X} (hxU : x ∈ U)
    {ψ₁ ψ₂ : modStalk A x →ₗ[ringStalk Rc x] modStalk B x}
    (h : ∀ (W : Opens X), W ≤ U → ∀ (hxW : x ∈ W) (t : (commVal (Rc := Rc) A).obj (op W)),
      ψ₁ (germAt A W x hxW t) = ψ₂ (germAt A W x hxW t)) : ψ₁ = ψ₂ := by
  refine linearMap_ext fun W hxW t ↦ ?_
  rw [← germAt_resLE A (inf_le_left : W ⊓ U ≤ W) (mem_inf hxW hxU) t]
  exact h _ inf_le_right _ _

/-- Taking stalks of local homomorphisms is compatible with composition. -/
lemma stalkLinearMap_comp {U : Opens X} (φ : A.over U ⟶ B.over U) (ψ : B.over U ⟶ C.over U)
    {x : X} (hxU : x ∈ U) :
    stalkLinearMap (φ ≫ ψ) hxU = (stalkLinearMap ψ hxU).comp (stalkLinearMap φ hxU) := by
  refine linearMap_ext_of_le hxU fun W hWU hxW t ↦ ?_
  rw [LinearMap.comp_apply, stalkLinearMap_apply (φ ≫ ψ) hxU, stalkLinearMap_apply φ hxU,
    stalkLinearMap_apply ψ hxU, stalkMap_germ (φ ≫ ψ) hxU hWU hxW, stalkMap_germ φ hxU hWU hxW,
    stalkMap_germ ψ hxU hWU hxW, appAt_comp]

/-- The stalk of the zero local homomorphism is zero. -/
lemma stalkLinearMap_zero {U : Opens X} {x : X} (hxU : x ∈ U) :
    stalkLinearMap (0 : A.over U ⟶ B.over U) hxU = 0 := by
  refine linearMap_ext_of_le hxU fun W hWU hxW t ↦ ?_
  rw [stalkLinearMap_apply, stalkMap_germ _ hxU hWU hxW, LinearMap.zero_apply, appAt_zero_hom,
    germAt_zero]

/-- Taking the stalk of a local homomorphism, packaged as an additive map. -/
def stalkLinearMapAddHom (A B : SheafOfModules.{u} (structureSheaf Rc)) {U : Opens X} {x : X}
    (hxU : x ∈ U) :
    (A.over U ⟶ B.over U) →+ (modStalk A x →ₗ[ringStalk Rc x] modStalk B x) where
  toFun φ := stalkLinearMap φ hxU
  map_zero' := stalkLinearMap_zero hxU
  map_add' φ ψ := stalkLinearMap_add φ ψ hxU

/-- Taking stalks of local homomorphisms commutes with integer multiples. The signs in the
differential of a Hom complex make this the form in which additivity is used. -/
lemma stalkLinearMap_zsmul {U : Opens X} (k : ℤ) (φ : A.over U ⟶ B.over U) {x : X}
    (hxU : x ∈ U) : stalkLinearMap (k • φ) hxU = k • stalkLinearMap φ hxU :=
  map_zsmul (stalkLinearMapAddHom A B hxU) k φ

/-- The stalk of the restriction of a global homomorphism is the stalk of that homomorphism. -/
lemma stalkLinearMap_over {U : Opens X} (f : A ⟶ B) {x : X} (hxU : x ∈ U) :
    stalkLinearMap (f.over U) hxU = modStalkMap f x := by
  refine linearMap_ext_of_le hxU fun W hWU hxW t ↦ ?_
  rw [stalkLinearMap_apply, stalkMap_germ _ hxU hWU hxW, appAt_over, modStalkMap_germ]

end Components

/-! ### The stalk of a cochain of local homomorphisms -/

section CochainStalk

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {E F : CochainComplex (StructureSheafModules Rc) ℤ} {x : X}

/-- The stalk at `x` of a degree-`n` cochain of homomorphisms between the restrictions to an
open `U` containing `x`: componentwise, the stalk of each local homomorphism. -/
def cochainStalk {U : Opens X} (hxU : x ∈ U) {n : ℤ}
    (z : Cochain (restrictComplex Rc E U) (restrictComplex Rc F U) n) :
    Cochain (modStalkComplex E x) (modStalkComplex F x) n :=
  Cochain.mk fun p q hpq => ModuleCat.ofHom (stalkLinearMap (z.v p q hpq) hxU)

/-- The `(p, q)` component of `cochainStalk hxU z` is the stalk of the `(p, q)` component of
`z`. -/
@[simp]
lemma cochainStalk_v {U : Opens X} (hxU : x ∈ U) {n : ℤ}
    (z : Cochain (restrictComplex Rc E U) (restrictComplex Rc F U) n) (p q : ℤ)
    (hpq : p + n = q) :
    (cochainStalk (E := E) (F := F) hxU z).v p q hpq =
      ModuleCat.ofHom (stalkLinearMap (z.v p q hpq) hxU) := rfl

/-- Taking the stalk of a cochain is additive. -/
lemma cochainStalk_add {U : Opens X} (hxU : x ∈ U) {n : ℤ}
    (z z' : Cochain (restrictComplex Rc E U) (restrictComplex Rc F U) n) :
    cochainStalk (E := E) (F := F) hxU (z + z')
      = cochainStalk hxU z + cochainStalk hxU z' := by
  ext p q hpq
  rw [cochainStalk_v, Cochain.add_v, Cochain.add_v, cochainStalk_v, cochainStalk_v,
    stalkLinearMap_add]
  rfl

/-- The stalk of the zero cochain is zero. -/
lemma cochainStalk_zero {U : Opens X} (hxU : x ∈ U) (n : ℤ) :
    cochainStalk (E := E) (F := F) hxU (0 : Cochain _ _ n) = 0 := by
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  rw [cochainStalk_v, Cochain.zero_v, Cochain.zero_v, stalkLinearMap_zero]
  rfl

/-- Taking the stalk of a cochain of local homomorphisms, packaged as an additive map. -/
def cochainStalkAddHom {U : Opens X} (hxU : x ∈ U) (n : ℤ) :
    Cochain (restrictComplex Rc E U) (restrictComplex Rc F U) n →+
      Cochain (modStalkComplex E x) (modStalkComplex F x) n where
  toFun := cochainStalk hxU
  map_zero' := cochainStalk_zero hxU n
  map_add' := cochainStalk_add hxU

/-- **The stalk of a cochain commutes with the Hom-complex differential.** This is the
differential assembly: the differential of a Hom complex is the signed sum of a
postcomposition and a precomposition, and taking stalks of local homomorphisms is additive,
functorial, and carries the restriction of a differential of `E` or `F` to its stalk. -/
lemma cochainStalk_δ {U : Opens X} (hxU : x ∈ U) {n m : ℤ} (hnm : n + 1 = m)
    (z : Cochain (restrictComplex Rc E U) (restrictComplex Rc F U) n) :
    cochainStalk (E := E) (F := F) hxU (δ n m z) = δ n m (cochainStalk hxU z) := by
  ext p q hpq
  rw [cochainStalk_v, δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl,
    δ_v n m hnm (cochainStalk hxU z) p q hpq (q - 1) (p + 1) rfl rfl,
    Units.smul_def, Units.smul_def, stalkLinearMap_add, stalkLinearMap_zsmul,
    stalkLinearMap_comp, stalkLinearMap_comp, cochainStalk_v, cochainStalk_v,
    show (restrictComplex Rc F U).d (q - 1) q = (F.d (q - 1) q).over U from rfl,
    show (restrictComplex Rc E U).d p (p + 1) = (E.d p (p + 1)).over U from rfl,
    stalkLinearMap_over, stalkLinearMap_over]
  rfl

/-- Restricting a cochain of local homomorphisms to a smaller open neighbourhood of `x` does not
change its stalk at `x`. This is the cocone compatibility underlying the comparison below, and
it is where `SheafHomComplex.restrict_natural` is used. -/
lemma stalkLinearMap_restrict_component (H : SheafHomComplex Rc E F) {U V : Opens X}
    (hVU : V ≤ U) (hxV : x ∈ V) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) :
    stalkLinearMap ((AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n)
          ((H.obj.X n).val.map (homOfLE hVU).op s)).v p q hpq) hxV
      = stalkLinearMap ((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq)
          (hVU hxV) := by
  refine linearMap_ext fun W hxW t ↦ ?_
  rw [stalkLinearMap_apply, stalkLinearMap_apply, stalkMap_germ_inf, stalkMap_germ_inf]
  have key : appAt (inf_le_right : W ⊓ V ≤ V)
        ((AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n)
          ((H.obj.X n).val.map (homOfLE hVU).op s)).v p q hpq)
        (resLE (E.X p) (inf_le_left : W ⊓ V ≤ W) t)
      = appAt ((inf_le_right : W ⊓ V ≤ V).trans hVU)
          ((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq)
          (resLE (E.X p) (inf_le_left : W ⊓ V ≤ W) t) :=
    (H.restrict_natural hVU n p q hpq s (inf_le_right : W ⊓ V ≤ V)
      (resLE (E.X p) (inf_le_left : W ⊓ V ≤ W) t)).symm
  rw [key]
  have h1 : W ⊓ V ≤ W ⊓ U := inf_le_inf_left W hVU
  rw [show resLE (E.X p) (inf_le_left : W ⊓ V ≤ W) t
      = resLE (E.X p) h1 (resLE (E.X p) (inf_le_left : W ⊓ U ≤ W) t) from
    (resLE_resLE (E.X p) _ h1 t).symm]
  exact germ_appAt (inf_le_right : W ⊓ U ≤ U) h1 (mem_inf hxW hxV) _ _

/-- Restricting a section of the internal Hom complex to a smaller open neighbourhood `V` of `x`
does not change the stalk at `x` of the corresponding cochain. -/
lemma cochainStalk_restrict (H : SheafHomComplex Rc E F) {U V : Opens X} (hVU : V ≤ U)
    (hxV : x ∈ V) (n : ℤ) (s : (H.obj.X n).val.obj (op U)) :
    cochainStalk (E := E) (F := F) hxV
        (AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n)
          ((H.obj.X n).val.map (homOfLE hVU).op s))
      = cochainStalk (hVU hxV) (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s) :=
  Cochain.ext _ _ fun p q hpq =>
    congrArg ModuleCat.ofHom (stalkLinearMap_restrict_component H hVU hxV n p q hpq s)

end CochainStalk

/-! ### The comparison with the naive Hom complex over the stalk ring -/

section StalkComparison

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {E F : CochainComplex (StructureSheafModules Rc) ℤ}
  (H : SheafHomComplex Rc E F) (n : ℤ) (x : X)

/-- The component at an open neighbourhood `U` of `x` of the cocone defining the comparison: a
section of the degree-`n` term of the internal Hom complex over `U` is a degree-`n` cochain of
homomorphisms of the restrictions to `U`, whose stalk at `x` is a degree-`n` cochain of the
complexes of stalks. -/
def homComplexStalkCoconeApp (U : (OpenNhds x)ᵒᵖ) :
    ((OpenNhds.inclusion x).op ⋙ (commVal (Rc := Rc) (H.obj.X n)).presheaf).obj U ⟶
      AddCommGrpCat.of (Cochain (modStalkComplex E x) (modStalkComplex F x) n) :=
  (H.sectionsIso U.unop.1).hom.f n ≫
    AddCommGrpCat.ofHom (cochainStalkAddHom (E := E) (F := F) U.unop.2 n)

/-- The cocone on the diagram computing the stalk of the degree-`n` term of the internal Hom
complex, with vertex the degree-`n` term of the naive Hom complex of the complexes of stalks. -/
def homComplexStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ (commVal (Rc := Rc) (H.obj.X n)).presheaf) where
  pt := AddCommGrpCat.of (Cochain (modStalkComplex E x) (modStalkComplex F x) n)
  ι :=
    { app := homComplexStalkCoconeApp H n x
      naturality := by
        intro U V f
        ext s
        exact cochainStalk_restrict H f.unop.le V.unop.2 n s }

/-- **The degree-`n` comparison.** The canonical map from the stalk at `x` of the degree-`n`
term of the internal Hom complex `SheafHom(E, F)` to the degree-`n` term of the naive Hom
complex of the complexes of stalks over `O_{X,x}`. It sends the germ of a local cochain to the
cochain of the induced maps on stalks; there is no hypothesis on `E` or `F`. -/
@[ega "0 4.1.5" "more general"]
def homComplexStalkCochainMap :
    modStalk (H.obj.X n) x ⟶
      AddCommGrpCat.of (Cochain (modStalkComplex E x) (modStalkComplex F x) n) :=
  colimit.desc _ (homComplexStalkCocone H n x)

/-- The germ formula characterising the degree-`n` comparison. -/
lemma homComplexStalkCochainMap_germ (U : Opens X) (hxU : x ∈ U)
    (s : (commVal (Rc := Rc) (H.obj.X n)).obj (op U)) :
    homComplexStalkCochainMap H n x (germAt (H.obj.X n) U x hxU s)
      = cochainStalk hxU (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (homComplexStalkCocone H n x) (op (⟨U, hxU⟩ : OpenNhds x))) s

end StalkComparison

end SheafHomStalk

section StalkComparison

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {E F : CochainComplex (StructureSheafModules Rc) ℤ}

/-- **The stalk of the internal Hom complex, as a complex.** For any realization `H` of the
internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z, the degreewise comparisons
`homComplexStalkCochainMap` commute with the differentials, so they assemble into a morphism of
complexes from the stalk at `x` of `SheafHom(E, F)` to the naive Hom complex of the complexes of
stalks over the stalk ring `O_{X,x}`.

There is no hypothesis on `E` or `F`. The differential of a Hom complex is the signed sum of a
postcomposition and a precomposition map; the commutation is `cochainStalk_δ`, read through the
fact that `H.sectionsIso U` is an isomorphism *of complexes* onto the Hom complex of the
restrictions to `U`. -/
@[ega "0 4.1.5" "more general"]
def sheafHomComplexStalkComparison (H : SheafHomComplex Rc E F) (x : X) :
    modStalkAbComplex H.obj x ⟶ (modStalkComplex E x).HomComplex (modStalkComplex F x) where
  f n := SheafHomStalk.homComplexStalkCochainMap H n x
  comm' n m hnm := by
    have hnm' : n + 1 = m := hnm
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro σ
    obtain ⟨U, hxU, s, rfl⟩ := SheafHomStalk.exists_germ_eq (H.obj.X n) σ
    have hcomm := ConcreteCategory.congr_hom ((H.sectionsIso U).hom.comm n m) s
    change δ n m (SheafHomStalk.homComplexStalkCochainMap H n x
        (SheafHomStalk.germAt (H.obj.X n) U x hxU s)) =
      SheafHomStalk.homComplexStalkCochainMap H m x
        (SheafHomStalk.modStalkMap (H.obj.d n m) x
          (SheafHomStalk.germAt (H.obj.X n) U x hxU s))
    rw [SheafHomStalk.modStalkMap_germ (H.obj.d n m) x U hxU s,
      SheafHomStalk.homComplexStalkCochainMap_germ H m x U hxU,
      SheafHomStalk.homComplexStalkCochainMap_germ H n x U hxU]
    have hcomm' : δ n m (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s)
        = AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f m)
            ((H.obj.d n m).val.app (op U) s) := hcomm
    exact (SheafHomStalk.cochainStalk_δ hxU hnm' _).symm.trans
      (congrArg (fun z => SheafHomStalk.cochainStalk hxU (n := m) z) hcomm')

end StalkComparison

section Canonical

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (E F : CochainComplex (StructureSheafModules Rc) ℤ)

/-- **The stalk of the canonical internal Hom complex, as a complex.** The comparison
`sheafHomComplexStalkComparison` at the canonical internal Hom complex
`AlgebraicGeometry.RingedSite.sheafHomComplex` of Stacks 0A8X: a morphism of complexes from the
stalk at `x` of `SheafHom(E, F)` to the naive Hom complex of the complexes of stalks over the
stalk ring `O_{X,x}`.

No hypothesis on `E` or `F`. In particular this applies with `F` the structure sheaf placed in
degree zero, which is the case Stacks 0G02 needs. -/
@[ega "0 4.1.5" "more general"]
def sheafHomComplexStalkChainMap (x : X) :
    modStalkAbComplex (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj x ⟶
      (modStalkComplex E x).HomComplex (modStalkComplex F x) :=
  sheafHomComplexStalkComparison
    (ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)) x

end Canonical

end Stacks.SheafOfModules

end
