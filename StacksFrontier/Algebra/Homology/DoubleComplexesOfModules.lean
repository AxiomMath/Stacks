module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
public import StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions

/-!
# The product total complex of a double complex of modules

Stacks 09J0 (`HomologicalComplex₂.quasiIso_toProductTotal`) is a statement about complexes of
*abelian groups*: given an exact complex of complexes `0 → M^• → A_0^• → A_1^• → ⋯` whose
induced complexes of cokernels are exact too, the map `M^• → Tot_π(A^{•,•})` is a
quasi-isomorphism. Its consumers, however, live in `CochainComplex (ModuleCat R) ℤ` — the
underlying complex of a differential graded module over a differential graded algebra over `R`
is a complex of `R`-modules, and quasi-isomorphy of differential graded modules is
quasi-isomorphy of those complexes. This file is the bridge: it restates 09J0 for a double
complex of `R`-modules.

The bridge is a transport along `forget₂ (ModuleCat R) AddCommGrpCat`, which is additive,
faithful and preserves homology. Both hypotheses of 09J0 push forward along it, and its
conclusion — being a quasi-isomorphism — comes back along it, so nothing is lost: the
`ModuleCat` statement is equivalent to the `AddCommGrpCat` one and no new mathematics is
needed. What *cannot* be transported is the product total complex itself, because
`HomologicalComplex₂.productTotal` is built by hand out of dependent functions of abelian
groups. So the `ModuleCat`-side total complex is a parameter of the statement: a consumer
supplies its own complex `T` of `R`-modules, a map `φ : M ⟶ T`, and an identification of the
underlying complex of abelian groups of `T` with `Tot_π` of the underlying double complex of
abelian groups, under which `φ` becomes the canonical map. This is exactly the shape a consumer
has, since it builds `T` as a graded product in its own category and not as
`HomologicalComplex₂.productTotal`.

## Main results

* `HomologicalComplex₂.acyclic_augment_forget₂`: the exactness hypothesis of 09J0 pushes
  forward along the forgetful functor.
* `HomologicalComplex₂.acyclic_opcycles_augment_forget₂`: so does the hypothesis on the
  complexes of cokernels.
* `HomologicalComplex₂.quasiIso_toProductTotal_forget₂`: 09J0 applied to the underlying double
  complex of abelian groups of a double complex of `R`-modules, with the hypotheses stated for
  `R`-modules.
* `HomologicalComplex₂.quasiIso_of_isProductTotal`: the bridge proper — a map of complexes of
  `R`-modules which the forgetful functor identifies with the canonical map to the product
  total complex is a quasi-isomorphism.

## References

* [Stacks 09J0](https://stacks.math.columbia.edu/tag/09J0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CochainComplex

/-- The forgetful functor from cochain complexes of `R`-modules to cochain complexes of abelian
groups, degreewise `forget₂ (ModuleCat R) AddCommGrpCat`. -/
abbrev forget₂AddCommGrpCat (R : Type u) [Ring R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)

end CochainComplex

namespace HomologicalComplex₂

/-- The forgetful functor from double complexes of `R`-modules, with first index in `ℕ` and
second index in `ℤ`, to double complexes of abelian groups. -/
abbrev forget₂AddCommGrpCat (R : Type u) [Ring R] :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℤ) ⥤
      HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  (CochainComplex.forget₂AddCommGrpCat.{u} R).mapHomologicalComplex (ComplexShape.up ℕ)

variable {R : Type u} [Ring R]
  {K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℤ)}
  {M : CochainComplex (ModuleCat.{u} R) ℤ} (ε : M ⟶ K.X 0) (w : ε ≫ K.d 0 1 = 0)

include w

/-- The image of `ε` under the forgetful functor is still killed by the first differential of
the double complex, so the underlying double complex of abelian groups can be augmented by
it. -/
lemma forget₂AddCommGrpCat_w :
    (CochainComplex.forget₂AddCommGrpCat.{u} R).map ε ≫
      ((forget₂AddCommGrpCat.{u} R).obj K).d 0 1 = 0 :=
  CochainComplex.map_augment_w K ε w _

/-- The augmentation of the underlying double complex of abelian groups by the image of `ε` is
the image of the augmentation of `K` by `ε`. -/
def forget₂AddCommGrpCatAugmentIso :
    ((CochainComplex.forget₂AddCommGrpCat.{u} R).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (CochainComplex.augment K ε w) ≅
      CochainComplex.augment ((forget₂AddCommGrpCat.{u} R).obj K)
        ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ε) (forget₂AddCommGrpCat_w ε w) :=
  CochainComplex.mapHomologicalComplexAugmentIso K ε w _

/-- The first hypothesis of Stacks 09J0 pushes forward along the forgetful functor: if the
complex of complexes `0 → M^• → A_0^• → ⋯` of `R`-modules is exact, so is the underlying
complex of complexes of abelian groups. -/
lemma acyclic_augment_forget₂ (hA : (CochainComplex.augment K ε w).Acyclic) :
    (CochainComplex.augment ((forget₂AddCommGrpCat.{u} R).obj K)
      ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ε)
      (forget₂AddCommGrpCat_w ε w)).Acyclic :=
  fun i => ((hA i).map _).of_iso (forget₂AddCommGrpCatAugmentIso ε w)

/-- The second hypothesis of Stacks 09J0 pushes forward along the forgetful functor: if the
complexes of cokernels `0 → Coker(d_M^q) → Coker(d_{A_0}^q) → ⋯` of `R`-modules are exact, so
are the underlying complexes of abelian groups. Here `Coker(d^q)` is the object of opcycles in
degree `q + 1`, so the hypothesis is the acyclicity of the image of the augmented complex under
the functor of opcycles in degree `q`. -/
lemma acyclic_opcycles_augment_forget₂
    (hC : ∀ q : ℤ, (((HomologicalComplex.opcyclesFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CochainComplex.augment K ε w)).Acyclic) (q : ℤ) :
    (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
        q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CochainComplex.augment ((forget₂AddCommGrpCat.{u} R).obj K)
        ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ε)
        (forget₂AddCommGrpCat_w ε w))).Acyclic :=
  fun i => ((hC q i).map (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).of_iso
    ((NatIso.mapHomologicalComplex
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplexOpcyclesFunctorIso
          (ComplexShape.up ℤ) q).symm (ComplexShape.up ℕ)).app
        (CochainComplex.augment K ε w) ≪≫
      ((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
        q).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
          (forget₂AddCommGrpCatAugmentIso ε w))

/-- Stacks 09J0 for the underlying double complex of abelian groups of a double complex of
`R`-modules: with the two exactness hypotheses stated in `ModuleCat R`, the canonical map from
the underlying complex of `M^•` to `Tot_π` of the underlying double complex is a
quasi-isomorphism. -/
theorem quasiIso_toProductTotal_forget₂ (hA : (CochainComplex.augment K ε w).Acyclic)
    (hC : ∀ q : ℤ, (((HomologicalComplex.opcyclesFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CochainComplex.augment K ε w)).Acyclic) :
    QuasiIso (toProductTotal (K := (forget₂AddCommGrpCat.{u} R).obj K)
      ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ε) (forget₂AddCommGrpCat_w ε w)) :=
  quasiIso_toProductTotal _ _ (acyclic_augment_forget₂ ε w hA)
    (acyclic_opcycles_augment_forget₂ ε w hC)

/-- **The bridge for Stacks 09J0 from abelian groups to modules.** Let `K` be a double complex
of `R`-modules with first index in `ℕ`, let `ε : M^• → K^{0,•}` be a map of complexes of
`R`-modules with `d_1 ∘ ε = 0`, and assume the two exactness hypotheses of Stacks 09J0: the
augmented complex of complexes `0 → M^• → K^{0,•} → K^{1,•} → ⋯` is exact, and so are its
complexes of cokernels. Let `φ : M^• → T^•` be any map of complexes of `R`-modules whose
underlying map of complexes of abelian groups is, up to the isomorphism `e`, the canonical map
`M^• → Tot_π(K^{•,•})`. Then `φ` is a quasi-isomorphism.

This is the form in which a consumer uses 09J0: it builds its own total complex `T^•` in its
own category, identifies the underlying complex of abelian groups with
`HomologicalComplex₂.productTotal`, and gets a quasi-isomorphism of complexes of `R`-modules
back. The conclusion really is a statement about `R`-modules: `forget₂` reflects
isomorphisms, so being a quasi-isomorphism is detected by the underlying complexes of abelian
groups. -/
theorem quasiIso_of_isProductTotal {T : CochainComplex (ModuleCat.{u} R) ℤ} (φ : M ⟶ T)
    (hA : (CochainComplex.augment K ε w).Acyclic)
    (hC : ∀ q : ℤ, (((HomologicalComplex.opcyclesFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CochainComplex.augment K ε w)).Acyclic)
    (e : (CochainComplex.forget₂AddCommGrpCat.{u} R).obj T ≅
      ((forget₂AddCommGrpCat.{u} R).obj K).productTotal)
    (he : (CochainComplex.forget₂AddCommGrpCat.{u} R).map φ ≫ e.hom =
      toProductTotal (K := (forget₂AddCommGrpCat.{u} R).obj K)
        ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ε) (forget₂AddCommGrpCat_w ε w)) :
    QuasiIso φ := by
  have := quasiIso_toProductTotal_forget₂ ε w hA hC
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]
  refine quasiIso_of_arrow_mk_iso
    (toProductTotal (K := (forget₂AddCommGrpCat.{u} R).obj K)
      ((CochainComplex.forget₂AddCommGrpCat.{u} R).map ε) (forget₂AddCommGrpCat_w ε w))
    ((CochainComplex.forget₂AddCommGrpCat.{u} R).map φ)
    (Arrow.isoMk (Iso.refl _) e.symm ?_)
  dsimp only [Arrow.mk_hom, Iso.refl_hom, Iso.symm_hom]
  rw [Category.id_comp, ← he, Category.assoc, e.hom_inv_id, Category.comp_id]

end HomologicalComplex₂
