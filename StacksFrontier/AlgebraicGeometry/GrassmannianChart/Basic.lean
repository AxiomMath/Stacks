module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The chart functor of the Grassmannian, and its representing affine space

[Stacks, Tag 089T] asserts that for `0 < k < n` the Grassmannian functor `G(k, n)` of
[Stacks, Tag 089S] is representable by a scheme. The source's proof has five steps, and this
module supplies one of them in reusable form: the step that identifies each chart subfunctor
`F_i ⊆ G(k, n)` with a product of copies of the global-sections functor and concludes that `F_i`
is representable by `𝐀^{k(n-k)}_𝐙`.

The step is isolated here because it is the only one of the five that is independent of the
Grassmannian functor itself. Concretely, after the source identifies `Q` with
`O_S^{⊕(n-k)}` along `q ∘ s_i`, an element of `F_i(S)` is exactly a choice of the `k` remaining
images `q(e_{n-k+1}), …, q(e_n)` in `Γ(S, O_S^{⊕(n-k)})`, i.e. a `k × (n - k)` matrix of global
sections of `O_S`. So `F_i` is the functor

    S ↦ (ι → Γ(S, O_S))      with  ι = Fin k × Fin (n - k),

and what has to be proved is that *that* functor is representable. The source cites
[Stacks, Tag 01JH] (the case of a single index) together with the fact that a fibre product over
`Spec 𝐙` is a product of schemes.

## Main definitions

* `Stacks.AlgebraicGeometry.GrassmannianChart.sectionsFunctor`: the contravariant functor
  `S ↦ (ι → Γ(S, O_S))` on schemes, for an arbitrary index type `ι`, acting on morphisms by
  pullback of global sections.
* `Stacks.AlgebraicGeometry.GrassmannianChart.grassmannianChartFunctor`: the same functor at the
  index type `Fin k × Fin (n - k)` that occurs in the proof of [Stacks, Tag 089T].

## Main results

* `Stacks.AlgebraicGeometry.GrassmannianChart.sectionsRepresentableBy`: the functor is
  representable by `Spec 𝐙[ι]`, naturally in the scheme.
* `Stacks.AlgebraicGeometry.GrassmannianChart.sectionsRepresentableByAffineSpace`: the same, with
  the representing object presented as the affine space `𝐀(ι; Spec 𝐙)`.
* `Stacks.AlgebraicGeometry.GrassmannianChart.homEquiv_id_apply`: the universal family is the
  tuple of coordinates, which is the computation the source performs for a single index.
* `Stacks.AlgebraicGeometry.GrassmannianChart.sectionsRepresentableByReindex`: the representing
  object may be reindexed along any equivalence of index types, which is what turns the index
  type `Fin k × Fin (n - k)` into `Fin (k * (n - k))`.
* `Stacks.AlgebraicGeometry.GrassmannianChart.grassmannianChartFunctor_isRepresentable`: the chart
  functor of [Stacks, Tag 089T] is representable, by `𝐀^{k(n-k)}_𝐙`.

## Implementation notes

The whole content is Mathlib's `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv`, which is the
bijection `(X ⟶ Spec 𝐙[ι]) ≃ (ι → Γ(X, ⊤))` for an arbitrary index type, together with
`AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp`, which is its naturality and holds by
`rfl`. The work here is to package that pair as a
`CategoryTheory.Functor.RepresentableBy`, which is the form the gluing criterion
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` (Mathlib's
[Stacks, Tag 01JJ]) consumes. Every naturality and universal-family obligation discharged below
holds by `rfl`; the remaining declarations are transports along `ofIso`/`ofIsoObj`.

The category structure on `Type u` has a *bundled* hom (`TypeCat.Hom`, a structure
wrapping `TypeCat.Fun`), so a functor into `Type u` cannot have its `map` field written as a bare
lambda: the elaborator reports a type mismatch between `(ι → A) → (ι → B)` and
`(ι → A) ⟶ (ι → B)` and, with implicit lambdas in play, blames the binders instead. The `↾`
(`ofHom`) notation is required. For the same reason `(sectionsFunctor ι).obj X` does not reduce
during application elaboration, so the universal-family statement ascribes the type explicitly.

## References

* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
* [Stacks Project, Tag 01JH](https://stacks.math.columbia.edu/tag/01JH)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GrassmannianChart

/-- The contravariant functor sending a scheme `S` to the `ι`-indexed tuples of global sections
of its structure sheaf, and a morphism to the pullback of global sections along it.

For `ι` a singleton this is the functor of [Stacks, Tag 01JH]; for
`ι = Fin k × Fin (n - k)` it is the chart subfunctor `F_i` appearing in the proof of
[Stacks, Tag 089T], once an element of `F_i(S)` has been written as the tuple of images of the
last `k` basis vectors. -/
def sectionsFunctor (ι : Type u) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj X := ι → Γ(X.unop, ⊤)
  map f := ↾(fun v i => f.unop.appTop (v i))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The value of `sectionsFunctor ι` at a scheme `X` is the type of `ι`-indexed tuples of
global sections of `X`. -/
@[simp]
theorem sectionsFunctor_obj (ι : Type u) (X : Scheme.{u}ᵒᵖ) :
    (sectionsFunctor ι).obj X = (ι → Γ(X.unop, ⊤)) :=
  rfl

/-- `sectionsFunctor ι` acts on a morphism by pulling back each global section of the tuple along
it. -/
@[simp]
theorem sectionsFunctor_map_apply {ι : Type u} {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (v : ι → Γ(X.unop, ⊤)) (i : ι) :
    (sectionsFunctor ι).map f v i = f.unop.appTop (v i) :=
  rfl

/-- Reindexing the tuples along an equivalence of index types is a natural isomorphism of
functors. This is what lets the index type `Fin k × Fin (n - k)` of the Grassmannian chart be
replaced by `Fin (k * (n - k))`. -/
def sectionsFunctorCongr {ι ι' : Type u} (e : ι ≃ ι') :
    sectionsFunctor ι ≅ sectionsFunctor ι' :=
  NatIso.ofComponents
    (fun X => (Equiv.arrowCongr e (Equiv.refl Γ(X.unop, ⊤))).toIso)
    (fun _ => rfl)

/-- **The chart step of [Stacks, Tag 089T].** The functor `S ↦ (ι → Γ(S, O_S))` is representable
by `Spec 𝐙[ι]`, for an arbitrary index type `ι`.

This is [Stacks, Tag 01JH] with an arbitrary index set in place of a single variable; the source
of 089T obtains the indexed form from the single-variable one by remarking that a fibre product
over `Spec 𝐙` is a product of schemes, whereas here `Spec 𝐙[ι]` is already the required object. -/
noncomputable def sectionsRepresentableBy (ι : Type u) :
    (sectionsFunctor ι).RepresentableBy
      (Spec (CommRingCat.of (MvPolynomial ι (ULift.{u} ℤ)))) where
  homEquiv := AffineSpace.toSpecMvPolyIntEquiv ι
  homEquiv_comp _ _ := rfl

/-- The universal family of `sectionsRepresentableBy`: the tuple of sections corresponding to the
identity of the representing scheme is the tuple of coordinates `X i`. For a single index this is
the computation `ξ = x` with which [Stacks, Tag 01JH] ends. -/
theorem homEquiv_id_apply (ι : Type u) (i : ι) :
    ((sectionsRepresentableBy ι).homEquiv
        (𝟙 (Spec (CommRingCat.of (MvPolynomial ι (ULift.{u} ℤ))))) :
          ι → Γ(Spec (CommRingCat.of (MvPolynomial ι (ULift.{u} ℤ))), ⊤)) i =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι (ULift.{u} ℤ)))).inv
        (MvPolynomial.X i) :=
  rfl

/-- `sectionsRepresentableBy` with the representing object presented as the affine space
`𝐀(ι; Spec 𝐙)`, which is the form in which the proof of [Stacks, Tag 089T] names it
(`𝐀^{k(n-k)}_𝐙`). -/
noncomputable def sectionsRepresentableByAffineSpace (ι : Type u) :
    (sectionsFunctor ι).RepresentableBy
      (AffineSpace ι (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  (sectionsRepresentableBy ι).ofIsoObj
    (AffineSpace.SpecIso ι (CommRingCat.of (ULift.{u} ℤ)))

/-- The representing object may be reindexed along any equivalence of index types. -/
noncomputable def sectionsRepresentableByReindex {ι ι' : Type u} (e : ι ≃ ι') :
    (sectionsFunctor ι).RepresentableBy
      (Spec (CommRingCat.of (MvPolynomial ι' (ULift.{u} ℤ)))) :=
  (sectionsRepresentableBy ι').ofIso (sectionsFunctorCongr e).symm

/-- Reindexed form of `sectionsRepresentableByAffineSpace`. -/
noncomputable def sectionsRepresentableByAffineSpaceReindex {ι ι' : Type u} (e : ι ≃ ι') :
    (sectionsFunctor ι).RepresentableBy
      (AffineSpace ι' (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  (sectionsRepresentableByAffineSpace ι').ofIso (sectionsFunctorCongr e).symm

/-- The functor `S ↦ (ι → Γ(S, O_S))` is representable, by `sectionsRepresentableBy`. -/
theorem sectionsFunctor_isRepresentable (ι : Type u) :
    (sectionsFunctor ι).IsRepresentable :=
  (sectionsRepresentableBy ι).isRepresentable

/-- The single-index case, with the representing object spelled as `Spec 𝐙[x]` in the univariate
polynomial ring rather than as `Spec 𝐙[PUnit]`. This is the scheme named by
[Stacks, Tag 01JH]. -/
noncomputable def sectionsRepresentableByPolynomial :
    (sectionsFunctor PUnit.{u + 1}).RepresentableBy
      (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))) :=
  (sectionsRepresentableBy PUnit.{u + 1}).ofIsoObj
    (Scheme.Spec.mapIso
      (RingEquiv.toCommRingCatIso
        (MvPolynomial.uniqueAlgEquiv (ULift.{u} ℤ) PUnit.{u + 1}).toRingEquiv).op)

/-- The chart subfunctor of the Grassmannian functor `G(k, n)` of [Stacks, Tag 089S], written in
the coordinates the proof of [Stacks, Tag 089T] introduces: having identified the quotient `Q`
with `O_S^{⊕(n-k)}` along `q ∘ s_i`, the remaining data of `q` is the `k × (n - k)` matrix of
global sections given by the images of `e_{n-k+1}, …, e_n`.

This is a *definition of the coordinate functor*, not of `F_i` as a subfunctor of `G(k, n)`: the
identification of the two is step 3 of the source's proof and uses [Stacks, Tag 089Q]. -/
abbrev grassmannianChartFunctor (k n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  sectionsFunctor (ULift.{u} (Fin k × Fin (n - k)))

/-- The chart functor of [Stacks, Tag 089T] is representable by the affine space of dimension
`k * (n - k)` over `Spec 𝐙`, i.e. by `𝐀^{k(n-k)}_𝐙`. -/
noncomputable def grassmannianChartRepresentableBy (k n : ℕ) :
    (grassmannianChartFunctor.{u} k n).RepresentableBy
      (AffineSpace (ULift.{u} (Fin (k * (n - k)))) (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  sectionsRepresentableByAffineSpaceReindex
    (Equiv.ulift.trans (finProdFinEquiv.trans Equiv.ulift.symm))

/-- The chart functor of [Stacks, Tag 089T] is representable, by
`grassmannianChartRepresentableBy`. -/
theorem grassmannianChartFunctor_isRepresentable (k n : ℕ) :
    (grassmannianChartFunctor.{u} k n).IsRepresentable :=
  (grassmannianChartRepresentableBy k n).isRepresentable

end Stacks.AlgebraicGeometry.GrassmannianChart

end
