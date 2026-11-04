module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize

/-!
# An acyclic K-flat complex annihilates the total complex against every argument

K-flatness of `K` says that `Tot(F(G, K))` is acyclic whenever `G` is. This file records the
companion statement in which the acyclicity hypothesis sits on `K` instead of on `G`, and the
second argument is left completely unconstrained:

> if `K` is K-flat for `F` **and acyclic**, then `Tot(F(G, K))` is acyclic for *every* `G`.

The two statements are not formally related — K-flatness alone says nothing about `Tot(F(G, K))`
for a `G` with homology, and acyclicity of `K` alone says nothing either, since `Tot(F(-, -))`
is not computed degreewise. What bridges them is a left K-flat resolution of `G`: replacing `G`
by a complex `P` which is K-flat in the *first* variable of `F` makes `Tot(F(P, K))` acyclic for
the trivial reason that `K` is acyclic, and K-flatness of `K` is exactly what lets the
quasi-isomorphism `P ⟶ G` be pushed through `Tot(F(-, K))`.

The argument is therefore two applications of the bifunctor engine, and the only input
that is specific to a category is the existence of left K-flat resolutions. It is taken as a
hypothesis in `CochainComplex.KFlatBifunctor.acyclic_totalComplex_of_kFlat_of_acyclic` and
discharged on a ringed site by `Stacks.DerivedTensor.RingedSite.exists_kFlatLeft_quasiIso`.

## Main results

* `HomologicalComplex.acyclic_iff_of_quasiIso`: a quasi-isomorphism of cochain complexes in an
  abelian category has acyclic source exactly when it has acyclic target.
* `CochainComplex.KFlatBifunctor.acyclic_totalComplex_of_kFlat_of_acyclic`: the statement above,
  for an arbitrary additive bifunctor, with a left K-flat resolution of `G` supplied.
* `Stacks.DerivedTensor.RingedSite.acyclic_tensorComplex_of_kFlat_of_acyclic`: the same on a ringed
  site, with the
  resolution discharged, so that the only hypotheses left are K-flatness and acyclicity of `K`.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HomologicalComplex

/-- **Acyclicity is invariant under quasi-isomorphism.** A morphism of cochain complexes which
is a quasi-isomorphism induces an isomorphism on homology in every degree, and a complex is
acyclic exactly when all of its homology vanishes, so either of the two complexes is acyclic
exactly when the other is.

Only the direction from the source to the target is used below, but the hypothesis is symmetric
and both readings cost the same, so the biconditional is recorded. -/
theorem acyclic_iff_of_quasiIso {E : Type*} [Category E] [Abelian E]
    {K L : CochainComplex E ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    K.Acyclic ↔ L.Acyclic :=
  forall_congr' fun n ↦ by
    simpa only [exactAt_iff_isZero_homology] using (asIso (homologyMap f n)).isZero_iff

end HomologicalComplex

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **An acyclic K-flat complex makes the total complex acyclic against an arbitrary second
argument**, given a left K-flat resolution of that argument.

The two hypotheses on `K` are used once each and in different variables of `F`. Acyclicity of
`K` is what makes `Tot(F(P, K))` acyclic, by left K-flatness of `P`; K-flatness of `K` is what
makes `Tot(F(-, K))` carry the quasi-isomorphism `q : P ⟶ G` to a quasi-isomorphism, along
which that acyclicity transports to `Tot(F(G, K))`. Neither hypothesis can be dropped, and no
constraint on `G` is needed beyond the existence of `q`. -/
theorem acyclic_totalComplex_of_kFlat_of_acyclic
    {K : CochainComplex B ℤ} (hK : KFlat F K) (hKac : K.Acyclic)
    {G P : CochainComplex A ℤ} (q : P ⟶ G) (hq : QuasiIso q) (hP : KFlatLeft F P) :
    (totalComplex F G K).Acyclic :=
  (HomologicalComplex.acyclic_iff_of_quasiIso _
    (quasiIso_of_kFlat F K hK q hq)).1 (hP K hKac)

end CochainComplex.KFlatBifunctor

namespace Stacks.DerivedTensor.RingedSite

universe v u w

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
      (ComplexShape.up ℤ)]

/-- **An acyclic K-flat complex of `O`-modules makes `Tot(G ⊗_O K)` acyclic for every complex
`G` of `O`-modules.**

This is `CochainComplex.KFlatBifunctor.acyclic_totalComplex_of_kFlat_of_acyclic` at the tensor
product of a ringed site.  No hypothesis on `G` survives: on a ringed site every complex
admits a quasi-isomorphism from a K-flat one (Tag 06YS,
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`), and a K-flat complex
is K-flat in the *left* variable of `⊗_O` by the symmetry of the tensor product
(`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`), which is what the general statement
asks of the resolution.

The resolution is taken this way rather than from
`Stacks.DerivedTensor.RingedSite.exists_kFlatLeft_quasiIso`, which runs the resolution engine a
second time at the flipped bifunctor and is stated on a small site with all four universes
equal.  Routing through the unflipped resolution and the braiding instead leaves the object
universe `u`, the morphism universe `v` and the module universe `w` independent, so this
reaches an `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`. -/
theorem acyclic_tensorComplex_of_kFlat_of_acyclic
    {K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ}
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) K)
    (hKac : K.Acyclic)
    (G : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ) :
    (CochainComplex.KFlatBifunctor.totalComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) G K).Acyclic := by
  obtain ⟨P, q, hP, -, hq, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize R G
  exact CochainComplex.KFlatBifunctor.acyclic_totalComplex_of_kFlat_of_acyclic
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) hK hKac q hq
      (kFlatLeft_of_kFlat R hP)

end Stacks.DerivedTensor.RingedSite

end

end
