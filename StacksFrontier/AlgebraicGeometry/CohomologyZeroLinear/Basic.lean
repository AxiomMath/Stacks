module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree-zero cohomology over a field, `k`-linearly, and descent of a span

This file records the two inputs that a *descent along a field extension* of a statement about
`H⁰` needs, and that the library did not have.

`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` already identifies `H⁰(X, ℱ)` with
`Γ(ℱ, ⊤)`, but only as a bare `Equiv`: its own docstring records that `Γ(ℱ, ⊤)` carries no
`Module k` instance, the `k`-vector space structure being the one restriction of scalars along
the structure morphism puts on it. So the identification transports *surjectivity* of a map —
which is all its consumers so far have asked of it — and nothing linear: not a subspace, not a
span, not a base change. `AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` is the same
identification as an isomorphism in `ModuleCat k`, with `Γ(ℱ, ⊤)` carrying exactly that
restriction of scalars, together with the naturality that pins it down.

`Submodule.eq_top_of_span_image_baseChange` is the algebraic half: a `k`-subspace `V ≤ W` is
everything as soon as, after base change to a faithfully flat `k`-algebra `K`, the ambient
`K ⊗_k W` is spanned by elements of `V.baseChange K`. Faithfully flat descent for submodules is
Mathlib's `Submodule.baseChange_injective`; what is added here is the span form, which is the
shape a surjectivity-of-multiplication statement arrives in.

## Main definitions

* `AlgebraicGeometry.restrictScalarsOverBase`: restriction of scalars from `Γ(X, ⊤)` to `k`
  along the structure morphism `X ⟶ Spec k` — the functor that gives cohomology on a scheme
  over `k` its `k`-vector space structure, named publicly.

## Main results

* `AlgebraicGeometry.cohomologyOverFieldZeroLinearIso`: **`H⁰(X, ℱ) ≅ Γ(ℱ, ⊤)` in
  `ModuleCat k`.** Global sections are left exact, so the zeroth right derived functor is the
  global sections functor itself; restricting scalars is a functor, so the comparison is an
  isomorphism of `k`-modules and not merely a bijection.
* `AlgebraicGeometry.cohomologyOverFieldZeroLinearIso_naturality` and
  `cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap`: the isomorphism intertwines
  `H⁰(X, φ)` with `φ.app ⊤`, as an equation of morphisms and on elements.
* `Submodule.eq_top_of_span_image_baseChange`: **descent of a span along a faithfully flat
  extension.**

## Implementation notes

`AlgebraicGeometry.cohomologyOverFieldMap` is `@[expose]`d but `@[irreducible]`, and the
comparison of this file's isomorphism with it is exactly the "consumer that genuinely has to
unfold it" its own implementation note describes; `with_unfolding_all` is asked for there, as
that note prescribes, and nowhere else.

The naturality cannot be read off
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap` instead, because
that would need the two identifications to be the same function, and the existing one is built
from a `private` isomorphism whose body no other module can unfold. The two *are* the same
function; this file simply reconstructs it at the `SheafOfModules.evaluation` spelling, which is
public.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

/-! ### Descent of a span along a faithfully flat extension -/

/-- **Descent of a span along a faithfully flat extension.** Let `V` be a `k`-submodule of `W`
and let `K` be a faithfully flat `k`-algebra. If `K ⊗_k W`, read through any `K`-linear
identification with a module `W'`, is spanned by a set each of whose elements comes from
`V.baseChange K`, then `V = W`.

Faithfully flat descent for submodules is `Submodule.baseChange_injective`; the content here is
only that a spanning set inside the base-changed subspace forces the base change to be
everything, which is the form in which a surjectivity statement about a multiplication map
arrives. -/
@[ega "IV 2.2.7" "special case"]
public theorem Submodule.eq_top_of_span_image_baseChange
    {k K W W' : Type*} [CommRing k] [CommRing K] [Algebra k K] [Module.FaithfullyFlat k K]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module K W'] (V : Submodule k W)
    (e : K ⊗[k] W ≃ₗ[K] W') (T : Set W') (hT : Submodule.span K T = ⊤)
    (hTV : ∀ t ∈ T, e.symm t ∈ V.baseChange K) : V = ⊤ := by
  refine Submodule.baseChange_injective (A := K) ?_
  rw [Submodule.baseChange_top]
  have key : Submodule.span K T ≤ (V.baseChange K).comap (e.symm : W' →ₗ[K] K ⊗[k] W) :=
    Submodule.span_le.2 fun t ht => by simpa using hTV t ht
  exact top_le_iff.1 fun x _ => by simpa using key (hT.ge Submodule.mem_top (x := e x))

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Degree-zero cohomology is global sections, `k`-linearly -/

/-- **Restriction of scalars from `Γ(X, ⊤)` to `k` along the structure morphism.** This is the
functor that gives cohomology on a scheme over `k` its `k`-vector space structure in
`AlgebraicGeometry.cohomologyOverField`; it is `private` there, and is named here so that the
`k`-module `Γ(ℱ, ⊤)` can be spoken of outside that file. -/
public abbrev restrictScalarsOverBase : ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- **`H⁰(X, ℱ)` is the module of global sections of `ℱ`, as an isomorphism of `k`-modules.**
Global sections are left exact, so the zeroth right derived functor computing `H⁰` is the global
sections functor itself; restriction of scalars along the structure morphism then turns that
isomorphism of `Γ(X, ⊤)`-modules into one of `k`-modules.

This is `AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` with its linearity: the
underlying function is the same, but the target here is `Γ(ℱ, ⊤)` with the `k`-action it gets
from `AlgebraicGeometry.restrictScalarsOverBase`, so subspaces, spans and base changes transport
across it. -/
public def cohomologyOverFieldZeroLinearIso (F : X.Modules) :
    cohomologyOverField k f F 0 ≅
      (restrictScalarsOverBase k f).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F) :=
  (restrictScalarsOverBase k f).mapIso
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app F)

/-- **`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` intertwines `H⁰(X, φ)` with
`φ.app ⊤`**, as an equation of `k`-linear maps. This is naturality of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` at the global sections functor, pushed through
restriction of scalars. -/
public theorem cohomologyOverFieldZeroLinearIso_naturality {F G : X.Modules} (φ : F ⟶ G) :
    cohomologyOverFieldMap k f φ 0 ≫ (cohomologyOverFieldZeroLinearIso k f G).hom
      = (cohomologyOverFieldZeroLinearIso k f F).hom ≫
        (restrictScalarsOverBase k f).map
          ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map φ) := by
  with_unfolding_all
  exact ((restrictScalarsOverBase k f).map_comp
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived 0).map φ)
        ((SheafOfModules.evaluation X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app G).hom).symm.trans
      ((congrArg (restrictScalarsOverBase k f).map
          (NatTrans.naturality (SheafOfModules.evaluation X.ringCatSheaf
            (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.hom φ)).trans
        ((restrictScalarsOverBase k f).map_comp _ _))

/-- **`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` intertwines `H⁰(X, φ)` with
`φ.app ⊤`**, on elements. -/
public theorem cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap {F G : X.Modules}
    (φ : F ⟶ G) (a : cohomologyOverField k f F 0) :
    (cohomologyOverFieldZeroLinearIso k f G).hom
        (ConcreteCategory.hom (cohomologyOverFieldMap k f φ 0) a)
      = φ.app ⊤ ((cohomologyOverFieldZeroLinearIso k f F).hom a) :=
  DFunLike.congr_fun
    (congrArg ConcreteCategory.hom (cohomologyOverFieldZeroLinearIso_naturality k f φ)) a

end AlgebraicGeometry

end
