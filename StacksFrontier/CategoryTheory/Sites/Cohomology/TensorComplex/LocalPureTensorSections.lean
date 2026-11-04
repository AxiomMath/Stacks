module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductSheafification
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# A local section of a total tensor complex is a finite sum of pure tensors

Let `(C, O)` be a ringed site and let `A` and `B` be complexes of `O`-modules. A section of the
degree-`n` term of the total tensor complex `Tot(A ⊗_O B)` of Stacks 06YM is, after restriction
along the arrows of a covering sieve, a **finite** sum

`∑ⱼ aⱼ ⊗ bⱼ`

of pure tensors `AlgebraicGeometry.RingedSite.tensorTotalSection` of sections `aⱼ` of `A^{tⱼ}`
and `bⱼ` of `B^{rⱼ}` with `tⱼ + rⱼ = n`. Over a ringed space the same statement is available in
the neighbourhood form a shrinking argument consumes.

This is the step the proof of Stacks 0FPD, conclusion (a), opens with: *"after shrinking `X` we
can find an integer `N` and for `i = 1, …, N` integers `nᵢ` and sections `fᵢ` and `gᵢ` of
`M^{nᵢ}` and `N^{-nᵢ}` such that `η(1) = ∑ᵢ fᵢ ⊗ gᵢ`"*. Nothing here is a clause of a tag — it
is a step of a proof — so no `@[stacks …]` attribute is attached.

## Main results

* `Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_sum_inj`: a point of the vertex
  of a colimiting cofan of modules is a finite sum of injections. This is the companion of
  `Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_inj`, which says only
  that all but finitely many *components* vanish; expressing the point itself as the sum of its
  components is what a decomposition statement needs, and is not a consequence of the vanishing.
* `HomologicalComplex.isColimitCofanιMapBifunctor`: the summand inclusions
  `A^t ⊗ B^r ⟶ Tot(A ⊗ B)^n`, for `t + r = n`, form a colimiting cofan.
* `AlgebraicGeometry.RingedSite.exists_sum_tmul_tensorTotalPresheaf`: **at the presheaf level
  there is no shrinking at all** — every section of the degree-`n` term of the presheaf-level
  total complex is, over the very object it is given on, a finite sum of pure tensors.
* `AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection`: the sieve form, at
  `AlgebraicGeometry.RingedSite.tensorTotal`, with the summands the pure tensors
  `AlgebraicGeometry.RingedSite.tensorTotalSectionAt` of the development.
* `AlgebraicGeometry.RingedSpace.exists_nhd_sum_tensorTotalSection`: the neighbourhood form over
  a ringed space.

## Implementation notes

**Why the presheaf-level total complex carries the argument.**
`AlgebraicGeometry.RingedSite.tensorTotal` totalises the double complex of *presheaf* tensor
products and sheafifies degreewise afterwards. That ordering is what makes this file short: the
degree-`n` term of the presheaf-level total complex is a coproduct of presheaves of modules,
which is computed objectwise, and the objectwise tensor product of presheaves of modules is the
tensor product of the modules of sections. So the two finiteness facts — that a point of a
coproduct of modules is a finite sum of injections, and that an element of a tensor product of
modules is a finite sum of pure tensors — both apply **over the given object**, with no covering
in sight, and the whole statement needs exactly **one** localization: the sheafification unit of
the single presheaf `Tot(A ⊗ B)^n`, whose local surjectivity is
`isLocallySurjective_unit_tensorTotalPresheaf`.

The other spelling of the total complex, `Stacks.SheafOfModules.Tensor.tensorComplex`, sheafifies
each tensor product first and totalises afterwards. Read there, the same argument needs the
coproduct localized as well as the tensor products, hence a covering sieve per summand and a
finite intersection of them; the two spellings are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, but that isomorphism is not known to
carry `tensorTotalSection` to `AlgebraicGeometry.RingedSite.tensorComplexSection`, so a consumer
that wants the statement at the `tensorComplex` spelling still owes that compatibility. **This
file does not supply it.**

**The pure tensors are the development's own, and no new ones are introduced.** The sum in
degree `n` is a sum of `AlgebraicGeometry.RingedSite.tensorTotalSectionAt`, the pure tensor of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism`, which already
carries the degree equality `t + r = n` as a hypothesis instead of landing in degree `t + r`, so
that the sum needs no transport; and that file's `tensorTotalSectionAt_self` already identifies
it, by `rfl`, with `AlgebraicGeometry.RingedSite.tensorTotalSection` when `n` is literally
`t + r`. The presheaf-level total complex, its summands and their inclusions are likewise taken
from there — `tensorTotalPresheaf`, `tensorTotalPresheafTerm`, `ιTensorTotalPresheaf` and
`tensorTotalTmulMap` — so the only thing this file adds at that level is
`ιTensorTotalPresheafSections`, the summand inclusion read on sections. The `rfl` that unfolds
the pure tensor into the unit after that inclusion is
`AlgebraicGeometry.RingedSite.tensorTotalSectionAt_eq_unit_ι` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalShiftSections`, stated there
with the summand inclusion spelled as Mathlib's `HomologicalComplex.ιMapBifunctor`; that spelling
and `ιTensorTotalPresheafSections` are definitionally equal, so no statement of it is needed
here and `exists_sieve_sum_tensorTotalSection` crosses between them without a rewrite.

**Where `.hom` is needed.** A `ModuleCat` morphism is applied to an element through
`ModuleCat.Hom.hom`; the summand inclusions of this file are `ModuleCat` morphisms and so carry
it, while the sheafification unit is a morphism of presheaves of modules and its `app` is
applied directly, as in `AlgebraicGeometry.RingedSite.tensorTotalSection`. The final step of
`exists_sieve_sum_tensorTotalSection` is an `Eq.trans` rather than a rewrite: the restriction
`(Tot(A ⊗ B)^n).val.map g.op` lands in a `ModuleCat.restrictScalars` of the sections module, and
although that has the same carrier, a goal stated with the restriction on the left is not
type-correct at the `implicit` transparency level, so `rw` on it fails.

**The index type.** The decomposition is indexed by an unconstrained finite type rather than by
`Fin N`: it is assembled as a sigma type over the finite set of summands that actually occur, and
reindexing it to `Fin N` would add nothing a consumer cannot do.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM) — the total tensor
  complex.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD) — the proof whose first
  step this is.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite DirectSum HomologicalComplex

noncomputable section

namespace Stacks.SheafOfModules.CoproductSheafification

universe v u u'

variable {A : Type u} [Ring A] {I : Type v} {Z : I → ModuleCat.{max v u'} A}

/-- **A point of the vertex of a colimiting cofan of modules is a finite sum of injections.**
The finite set is the support of the corresponding element of the direct sum, and the summands
are its components there.

This is the statement `exists_finset_eq_zero_of_inj` does *not* give: that all but finitely many
components of a point vanish leaves open whether the point is recovered from the ones that do
not, which for a coproduct of modules it is. -/
public theorem exists_finset_eq_sum_inj {c : Cofan Z} (hc : IsColimit c) (t : c.pt) :
    ∃ (S : Finset I) (y : ∀ i, Z i), t = S.sum (fun i => (c.inj i).hom (y i)) := by
  classical
  let e : c.pt ≅ ModuleCat.of A (⨁ i, Z i) :=
    hc.coconePointUniqueUpToIso (ModuleCat.coproductCoconeIsColimit Z)
  have hinj : ∀ j : I, c.inj j =
      ModuleCat.ofHom (DirectSum.lof A I (fun i => Z i) j) ≫ e.inv := fun j =>
    (Iso.eq_comp_inv e).mpr
      (hc.comp_coconePointUniqueUpToIso_hom (ModuleCat.coproductCoconeIsColimit Z) ⟨j⟩)
  set d := e.hom.hom t
  refine ⟨d.support, fun i => d i, ?_⟩
  have hsum : d.support.sum (fun i => DirectSum.lof A I (fun k => Z k) i (d i)) = d :=
    DFinsupp.sum_single
  calc t = e.inv.hom d := (congrArg (fun f : c.pt ⟶ c.pt => f.hom t) e.hom_inv_id).symm
    _ = e.inv.hom (d.support.sum (fun i => DirectSum.lof A I (fun k => Z k) i (d i))) := by
        rw [hsum]
    _ = d.support.sum (fun i => e.inv.hom (DirectSum.lof A I (fun k => Z k) i (d i))) :=
        map_sum _ _ _
    _ = d.support.sum (fun i => (c.inj i).hom (d i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hinj i]
        rfl

end Stacks.SheafOfModules.CoproductSheafification

namespace HomologicalComplex

universe w₁ w₂ w₃ w₄ w₅ w₆

variable {C₁ : Type w₁} [Category.{w₂} C₁] {C₂ : Type w₃} [Category.{w₄} C₂]
  {D : Type w₅} [Category.{w₆} D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D)
  [F.PreservesZeroMorphisms] [∀ Y, (F.obj Y).PreservesZeroMorphisms]
  [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] (n : ℤ)

/-- **The summand inclusions of the degree-`n` term of a total complex form a colimiting cofan**,
indexed by the pairs `(t, r)` of integers with `t + r = n`. This is the universal property of
`HomologicalComplex.mapBifunctorDesc` and `HomologicalComplex.mapBifunctor.hom_ext` read as a
coproduct. -/
public def isColimitCofanιMapBifunctor :
    IsColimit (Cofan.mk ((mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)).X n)
      (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
        ιMapBifunctor K₁ K₂ F (ComplexShape.up ℤ) ij.1.1 ij.1.2 n (by simpa using ij.2))) := by
  refine Cofan.IsColimit.mk _
    (fun s => mapBifunctorDesc (fun i j h => s.inj ⟨(i, j), by simpa using h⟩))
    (fun s ij => ι_mapBifunctorDesc _ ij.1.1 ij.1.2 (by simpa using ij.2))
    (fun s m hm => mapBifunctor.hom_ext fun i j h => ?_)
  rw [ι_mapBifunctorDesc]
  exact hm ⟨(i, j), by simpa using h⟩

end HomologicalComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (n : ℤ) (W : X.C)

/-- The inclusion of the `(t, r)` summand into the degree-`n` term of the presheaf-level total
tensor complex `AlgebraicGeometry.RingedSite.tensorTotalPresheaf`, read on sections over `W`. -/
public abbrev ιTensorTotalPresheafSections (t r : ℤ) (h : t + r = n) :
    (tensorTotalPresheafTerm X A B t r).obj (op W) ⟶
      ((tensorTotalPresheaf X A B).X n).obj (op W) :=
  (PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op W)).map
    (ιTensorTotalPresheaf X A B t r n h)

/-- **The summand inclusions into the degree-`n` term of the presheaf-level total complex, read
on sections over `W`, form a colimiting cofan of modules.** The presheaf-level total complex is
a coproduct of presheaves of modules, and evaluation at `W` preserves it. -/
public def isColimitCofanTensorTotalPresheafSections :
    IsColimit (Cofan.mk (((tensorTotalPresheaf X A B).X n).obj (op W))
      (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
        ιTensorTotalPresheafSections X A B n W ij.1.1 ij.1.2 ij.2)) :=
  isColimitCofanMkObjOfIsColimit
    (PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op W)) _ _
    (HomologicalComplex.isColimitCofanιMapBifunctor (underlyingPresheafComplex X A)
      (underlyingPresheafComplex X B)
      (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) n)

/-- **Every section of the degree-`n` term of the presheaf-level total tensor complex is a finite
sum of pure tensors — over the very object it is given on.** No shrinking occurs: the
presheaf-level total complex is a coproduct formed objectwise, and the objectwise tensor product
of presheaves of modules is the tensor product of the modules of sections. -/
public theorem exists_sum_tmul_tensorTotalPresheaf
    (u : ((tensorTotalPresheaf X A B).X n).obj (op W)) :
    ∃ (κ : Type) (_ : Fintype κ) (t r : κ → ℤ) (h : ∀ j, t j + r j = n)
      (a : ∀ j, (A.X (t j)).val.obj (op W)) (b : ∀ j, (B.X (r j)).val.obj (op W)),
      u = ∑ j, (ιTensorTotalPresheafSections X A B n W (t j) (r j) (h j)).hom
        (a j ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b j) := by
  classical
  obtain ⟨S, y, hy⟩ := Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_sum_inj
    (isColimitCofanTensorTotalPresheafSections X A B n W) u
  choose m a b hab using fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
    TensorProduct.exists_sum_tmul_eq (y ij)
  have key : ∀ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
      (ιTensorTotalPresheafSections X A B n W ij.1.1 ij.1.2 ij.2).hom (y ij) =
        ∑ j : Fin (m ij), (ιTensorTotalPresheafSections X A B n W ij.1.1 ij.1.2 ij.2).hom
          (a ij j ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b ij j) := by
    intro ij
    rw [hab ij]
    exact map_sum (ιTensorTotalPresheafSections X A B n W ij.1.1 ij.1.2 ij.2).hom _ Finset.univ
  refine ⟨(ij : {x // x ∈ S}) × Fin (m ij.1), inferInstance,
    fun j => (j.1 : {ij : ℤ × ℤ // ij.1 + ij.2 = n}).1.1,
    fun j => (j.1 : {ij : ℤ × ℤ // ij.1 + ij.2 = n}).1.2,
    fun j => (j.1 : {ij : ℤ × ℤ // ij.1 + ij.2 = n}).2,
    fun j => a (j.1 : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) j.2,
    fun j => b (j.1 : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) j.2, ?_⟩
  rw [Fintype.sum_sigma, hy, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun ij _ => key ij

/-- The sheafification unit of the degree-`n` term of the presheaf-level total tensor complex is
locally surjective: this is the one localization the decomposition needs. -/
public theorem isLocallySurjective_unit_tensorTotalPresheaf :
    Presheaf.IsLocallySurjective X.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((tensorTotalPresheaf X A B).X n))) := by
  show Presheaf.IsLocallySurjective X.J
    (CategoryTheory.toSheafify X.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj
        ((tensorTotalPresheaf X A B).X n)))
  infer_instance

/-- **A section of the total tensor complex is, on a covering sieve, a finite sum of pure
tensors.** For a section `s` of `Tot(A ⊗_O B)^n` over `U` there is a covering sieve of `U` on
each of whose members `s` restricts to `∑ⱼ aⱼ ⊗ bⱼ` for finitely many sections `aⱼ` of `A^{tⱼ}`
and `bⱼ` of `B^{rⱼ}` with `tⱼ + rⱼ = n`.

This is the passage through a total complex that the single-tensor statement
`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_monoidalTensorSection` does not give, and it
is the first step of the proof of Stacks 0FPD, conclusion (a). -/
public theorem exists_sieve_sum_tensorTotalSection (U : X.C)
    (s : ((tensorTotal X A B).X n).val.obj (op U)) :
    ∃ T : Sieve U, T ∈ X.J U ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ U), T.arrows g →
      ∃ (κ : Type) (_ : Fintype κ) (t r : κ → ℤ) (h : ∀ j, t j + r j = n)
        (a : ∀ j, (A.X (t j)).val.obj (op W)) (b : ∀ j, (B.X (r j)).val.obj (op W)),
        ((tensorTotal X A B).X n).val.map g.op s =
          ∑ j, tensorTotalSectionAt X A B W (t j) (r j) n (h j) (a j) (b j) := by
  refine ⟨_, (isLocallySurjective_unit_tensorTotalPresheaf X A B n).imageSieve_mem s, ?_⟩
  rintro W g ⟨u, hu⟩
  obtain ⟨κ, hκ, t, r, h, a, b, hab⟩ := exists_sum_tmul_tensorTotalPresheaf X A B n W u
  refine ⟨κ, hκ, t, r, h, a, b, hu.symm.trans ?_⟩
  rw [hab]
  exact map_sum (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
    ((tensorTotalPresheaf X A B).X n)).app (op W)).hom _ Finset.univ

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedSpace

open TopologicalSpace AlgebraicGeometry.RingedSite

universe u

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
  (A B : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) ℤ) (n : ℤ)

/-- **A section of the total tensor complex on a ringed space is, on a neighbourhood of each
point, a finite sum of pure tensors.** Given a section `s` of `Tot(A ⊗_{𝒪_X} B)^n` over an open
`U` and a point `x ∈ U`, there is an open `V` with `x ∈ V ≤ U` on which `s` restricts to
`∑ⱼ aⱼ ⊗ bⱼ` for finitely many sections `aⱼ` of `A^{tⱼ}` and `bⱼ` of `B^{rⱼ}` over `V` with
`tⱼ + rⱼ = n`.

This is the shape the shrinking argument of Stacks 0FPD, conclusion (a), consumes: membership of
a sieve in the open-cover topology is by definition the existence of such a `V` at every
point. -/
public theorem exists_nhd_sum_tensorTotalSection (U : Opens X.carrier)
    (s : ((tensorTotal (ringedSite X) A B).X n).val.obj (op U)) (x : X.carrier) (hx : x ∈ U) :
    ∃ (V : Opens X.carrier) (hVU : V ≤ U), x ∈ V ∧
      ∃ (κ : Type) (_ : Fintype κ) (t r : κ → ℤ) (h : ∀ j, t j + r j = n)
        (a : ∀ j, (A.X (t j)).val.obj (op V)) (b : ∀ j, (B.X (r j)).val.obj (op V)),
        ((tensorTotal (ringedSite X) A B).X n).val.map (homOfLE hVU).op s =
          ∑ j, tensorTotalSectionAt (ringedSite X) A B V (t j) (r j) n (h j) (a j) (b j) := by
  obtain ⟨T, hT, hsum⟩ := exists_sieve_sum_tensorTotalSection (ringedSite X) A B n U s
  obtain ⟨V, k, hk, hxV⟩ := (Opens.mem_grothendieckTopology _).mp hT x hx
  obtain ⟨κ, hκ, t, r, h, a, b, hab⟩ := hsum k hk
  exact ⟨V, leOfHom k, hxV, κ, hκ, t, r, h, a, b, by
    rwa [Subsingleton.elim (homOfLE (leOfHom k)) k]⟩

end AlgebraicGeometry.RingedSpace

end

end
