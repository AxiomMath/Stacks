module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation

/-!
# The derived currying isomorphism against the currying of complexes, at an arbitrary target

Let `(X, O_X)` be a ringed space and let `A`, `B`, `C` be complexes of `O_X`-modules with `B`
K-flat.  The derived currying isomorphism of Stacks 08DJ,

`RSheafHom(QA, RSheafHom(QB, QC)) ≅ RSheafHom(QA ⊗^L_{O_X} QB, QC)`,

and the currying isomorphism of internal Hom complexes of Stacks 0A8M,

`SheafHom^•(A, SheafHom^•(B, C)) ≅ SheafHom^•(Tot(A ⊗_{O_X} B), C)`,

are compared by the canonical maps `strictlyPerfectHomComparison` of Stacks 08DM out of the
classes of the internal Hom complexes.  This file proves that the resulting square commutes
**with no hypothesis on the target `C`**.

`Stacks.SheafOfModules.derivedCurryIso_comparison` is that compatibility for a K-injective `C`,
which is where the derived currying isomorphism is constructed: there the two comparisons are
invertible and the square is the statement that `derivedCurryIso` *is* the complex-level
currying isomorphism conjugated by them.  Releasing `C` is for the currying isomorphism what
Stacks 08DM is for the internal Hom alone, and it is the shape in which the comparison can be
used at a K-flat — rather than K-injective — target, which is what the dévissage of Tag 0GM7
from a general perfect `K` to the unit case asks for.

## Main results

* `Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedCurryIso_of_isKInjective`: the
  square at a K-injective target, which is `derivedCurryIso_comparison` with both comparisons
  written as `strictlyPerfectHomComparison`.
* `Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedCurryIso`: **the square at an
  arbitrary target.**

## Nothing here is tagged

The square is a step of the proof of Tag 0GM7, not a clause of a published statement: the
published derived currying isomorphism is `Stacks.SheafOfModules.derivedCurryingData`, which
carries `@[stacks 08DJ]`, and its comparison with the currying of complexes at the K-injective
target where it is constructed carries `@[stacks 08J9]` at
`AlgebraicGeometry.RingedSite.derivedCurryIso_comparison`.  Neither Stacks 08DJ nor Stacks 08DM
asserts the square below; it is the join of the two.  So no declaration here carries a tag.

## The proof

The target is released from the K-injective case along its K-injective augmentation
`j : C ⟶ C'`.  The morphism `RSheafHom(QA ⊗^L QB, QC) ⟶ RSheafHom(QA ⊗^L QB, QC')` induced by
`Q j` is an isomorphism, because `j` is a quasi-isomorphism, so it may be cancelled from the
right; and each of the two legs of the square, composed with it, is the image of the map
`SheafHom^•(A, SheafHom^•(B, j))` of internal Hom complexes followed by the same leg at `C'`.

On the left that uses the naturality of the comparison of Stacks 08DM in its target
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_target`), twice — once
for the inner internal Hom complex and once for the outer one — together with the naturality of
the derived currying isomorphism of Stacks 08DJ in its target.  On the right it uses the same
comparison naturality once, the three-variable naturality of the complex-level currying
isomorphism of Stacks 0A8M
(`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso_natural`) at the identity of `A` and of
`B`, and the naturality of the morphism of bifunctors induced by the K-flat comparison of the
derived tensor product.

This is the same release the composition square of Stacks 0A91 against Stacks 0A98 uses in
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition`; here only one release
is needed, since the K-flatness of `B` is a hypothesis of the complex-level statement and not
an artefact of the construction, so it is never released.

## Implementation notes

The two legs of the square are released in separate declarations.  The elaborator's budget is
spent per declaration and the two halves do not fit in one; that is the discipline recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality` and
followed throughout this cluster.

Every statement is at the ringed-space spelling, with the comparison of Stacks 08DM taken at
`Stacks.SheafOfModules.derivedInternalHom`, the derived internal Hom whose bifunctor is
`Stacks.SheafOfModules.derivedSheafHom` on the nose.  The site-level
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom` is a `Classical.choice` of an
inhabitant of the same structure and is *not* that bifunctor, so a site-level statement joining
`strictlyPerfectHomComparison` to `derivedCurryIso` — which is built from
`derivedSheafHomBifunctor` directly — would not typecheck.  Each site-level lemma used below is
therefore instantiated at `Stacks.SheafOfModules.ringedSite Rc` and at
`Stacks.SheafOfModules.derivedInternalHom Rc`, and its conclusion is restated as a `have` in the
space-level spelling so that the identification of the two is settled once by elaboration rather
than at every rewrite.

## References

* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-! ### The two naturality inputs, at the ringed-space spelling -/

omit [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)] in
/-- **Naturality of the comparison of Stacks 08DM in its target**, at the ringed-space
spelling.  This is
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_target` at
`Stacks.SheafOfModules.derivedInternalHom`. -/
theorem strictlyPerfectHomComparison_naturality_target
    (E F F' : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ) (g : F ⟶ F') :
    DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 E) g) ≫
        strictlyPerfectHomComparison Rc E F' =
      strictlyPerfectHomComparison Rc E F ≫
        ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj E))).map
          (DerivedCategory.Q.map g) :=
  RingedSite.strictlyPerfectHomComparison_naturality_target (ringedSite Rc)
    (derivedInternalHom Rc) E F F' g

/-- **Naturality of the derived currying isomorphism of Stacks 08DJ in its target**: this is
`Stacks.SheafOfModules.derivedCurryIso_natural` at the identity of the source and of the middle
object, with the two induced maps written as images under the derived internal Hom. -/
theorem derivedCurryIso_naturality_target
    (K L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))} (m : M ⟶ M') :
    ((derivedSheafHom Rc).obj (op K)).map (((derivedSheafHom Rc).obj (op L)).map m) ≫
        (derivedCurryIso Rc K L M').hom =
      (derivedCurryIso Rc K L M).hom ≫
        ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj K).obj L))).map m := by
  have h := derivedCurryIso_natural Rc (𝟙 K) (𝟙 L) m
  have e₁ : derivedSheafHomMap Rc (𝟙 L) m = ((derivedSheafHom Rc).obj (op L)).map m :=
    RingedSite.derivedSheafHomMap_id_left (ringedSite Rc) (derivedInternalHom Rc) L m
  have e₂ : derivedSheafHomMap Rc (𝟙 K) (((derivedSheafHom Rc).obj (op L)).map m) =
      ((derivedSheafHom Rc).obj (op K)).map (((derivedSheafHom Rc).obj (op L)).map m) :=
    RingedSite.derivedSheafHomMap_id_left (ringedSite Rc) (derivedInternalHom Rc) K _
  have e₃ : derivedTensorMap Rc (𝟙 K) (𝟙 L) = 𝟙 (((derivedTensor Rc).obj K).obj L) :=
    (RingedSite.derivedTensorMap_id_left (ringedSite Rc)
        (canonicalDerivedTensorProduct (ringedSite Rc)) K (𝟙 L)).trans
      (CategoryTheory.Functor.map_id ((derivedTensor Rc).obj K) L)
  have e₄ : derivedSheafHomMap Rc (𝟙 (((derivedTensor Rc).obj K).obj L)) m =
      ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj K).obj L))).map m :=
    RingedSite.derivedSheafHomMap_id_left (ringedSite Rc) (derivedInternalHom Rc) _ m
  rw [e₁, e₂, e₃, e₄] at h
  exact h

/-! ### The square at a K-injective target -/

/-- **The square at a K-injective target.** For `B` K-flat and `C` K-injective the comparison
of Stacks 08DM identifies each of the two internal Hom complexes with the derived internal Hom
it computes, and the derived currying isomorphism of Stacks 08DJ is the currying isomorphism of
complexes of Stacks 0A8M conjugated by those identifications.

This is `Stacks.SheafOfModules.derivedCurryIso_comparison` with the two model identifications
written as `strictlyPerfectHomComparison`: at a K-injective target the comparison is the
inverse of the model comparison, by
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_eq_homComparison_inv`, and the two
model identifications are exactly the composites that occur here. -/
theorem strictlyPerfectHomComparison_derivedCurryIso_of_isKInjective
    (A B C : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ) (hB : IsKFlat Rc B)
    [hC : C.IsKInjective] :
    strictlyPerfectHomComparison Rc A (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj ≫
        ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map
            (strictlyPerfectHomComparison Rc B C) ≫
          (derivedCurryIso Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
            (DerivedCategory.Q.obj C)).hom =
      DerivedCategory.Q.map (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C).hom ≫
        strictlyPerfectHomComparison Rc (((Tensor.tensorComplex Rc).obj A).obj B) C ≫
          ((derivedSheafHom Rc).map
              ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A B
                hB).hom.op).app
            (DerivedCategory.Q.obj C) := by
  have hHom := RingedSite.isKInjective_sheafHomComplex_of_isKFlat (ringedSite Rc) B C hB
  have hσ : ∀ (E F : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
      [hF : F.IsKInjective], strictlyPerfectHomComparison Rc E F =
        (derivedSheafHomComparison Rc E F (hI := hF)).inv := fun E F _ =>
    RingedSite.strictlyPerfectHomComparison_eq_homComparison_inv (ringedSite Rc)
      (derivedInternalHom Rc) E F
  have hiter : (RingedSite.iteratedHomRepresentativeIso (ringedSite Rc) A B C hB).inv =
      (derivedSheafHomComparison Rc A
            (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj (hI := hHom)).inv ≫
        ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map
          (derivedSheafHomComparison Rc B C (hI := hC)).inv := rfl
  have htens : (RingedSite.tensorHomRepresentativeIso (ringedSite Rc) A B C hB).inv =
      (derivedSheafHomComparison Rc (((Tensor.tensorComplex Rc).obj A).obj B) C (hI := hC)).inv ≫
        ((derivedSheafHom Rc).map
            ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A B
              hB).hom.op).app
          (DerivedCategory.Q.obj C) := rfl
  have h := derivedCurryIso_comparison Rc A B C hB
  have key : (RingedSite.iteratedHomRepresentativeIso (ringedSite Rc) A B C hB).inv ≫
        (derivedCurryIso Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj C)).hom =
      DerivedCategory.Q.map (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C).hom ≫
        (RingedSite.tensorHomRepresentativeIso (ringedSite Rc) A B C hB).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 h).trans (Category.assoc _ _ _))
  rw [hiter, htens, ← hσ, ← hσ, ← hσ] at key
  exact (Category.assoc _ _ _).symm.trans key

/-! ### Releasing the target -/

/-- Three commuting squares in a row paste.  Stated over an arbitrary category with every
object and morphism a variable: each of the two legs of the square below is released by one
instance of it, which costs a single `isDefEq` instead of a dozen keyed rewrites inside the
derived category of a category of module sheaves. -/
private lemma paste_three_squares {D : Type*} [Category D]
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : D}
    (s : a₀ ⟶ a₁) (p : a₁ ⟶ a₂) (q : a₂ ⟶ a₃)
    (s' : b₀ ⟶ b₁) (p' : b₁ ⟶ b₂) (q' : b₂ ⟶ b₃)
    (w : a₀ ⟶ b₀) (l : a₁ ⟶ b₁) (x : a₂ ⟶ b₂) (y : a₃ ⟶ b₃)
    (h₀ : s ≫ l = w ≫ s') (h₁ : p ≫ x = l ≫ p') (h₂ : q ≫ y = x ≫ q') :
    (s ≫ p ≫ q) ≫ y = w ≫ s' ≫ p' ≫ q' := by
  rw [Category.assoc, Category.assoc, h₂, ← Category.assoc p, h₁, Category.assoc,
    ← Category.assoc s, h₀, Category.assoc]

/-- **The left-hand leg of the square is natural in the target.**  Composing it with the map
`RSheafHom(QA ⊗^L QB, QC) ⟶ RSheafHom(QA ⊗^L QB, QC')` induced by a morphism `j : C ⟶ C'`
gives the image of `SheafHom^•(A, SheafHom^•(B, j))` followed by the leg at `C'`.

The three squares pasted are the naturality of the comparison of Stacks 08DM in its target for
the inner internal Hom complex, the same for the outer one, and the naturality of the derived
currying isomorphism of Stacks 08DJ in its target. -/
private lemma curryComparisonLeft_naturality_target
    (A B C C' : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ) (j : C ⟶ C') :
    (strictlyPerfectHomComparison Rc A (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj ≫
          ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map
              (strictlyPerfectHomComparison Rc B C) ≫
            (derivedCurryIso Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
              (DerivedCategory.Q.obj C)).hom) ≫
        ((derivedSheafHom Rc).obj
            (op (((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).obj
              (DerivedCategory.Q.obj B)))).map (DerivedCategory.Q.map j) =
      DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 A)
          (RingedSite.homMap (ringedSite Rc) (𝟙 B) j)) ≫
        strictlyPerfectHomComparison Rc A
            (RingedSite.sheafHomComplex (ringedSite Rc) B C').obj ≫
          ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map
              (strictlyPerfectHomComparison Rc B C') ≫
            (derivedCurryIso Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
              (DerivedCategory.Q.obj C')).hom := by
  have hinner := strictlyPerfectHomComparison_naturality_target Rc B C C' j
  have houter := strictlyPerfectHomComparison_naturality_target Rc A
    (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj
    (RingedSite.sheafHomComplex (ringedSite Rc) B C').obj
    (RingedSite.homMap (ringedSite Rc) (𝟙 B) j)
  have hcurry := derivedCurryIso_naturality_target Rc (DerivedCategory.Q.obj A)
    (DerivedCategory.Q.obj B) (DerivedCategory.Q.map j)
  have hmid :=
    ((((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map_comp _ _).symm.trans
        (congrArg (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map) hinner)).trans
      (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map_comp _ _)
  exact paste_three_squares _ _ _ _ _ _ _ _ _ _ houter.symm hmid.symm hcurry.symm

/-- **The right-hand leg of the square is natural in the target.**  The three squares pasted
are the three-variable naturality of the currying isomorphism of complexes of Stacks 0A8M at
the identity of `A` and of `B`, the naturality of the comparison of Stacks 08DM in its target,
and the naturality of the morphism of bifunctors induced by the K-flat comparison of the
derived tensor product. -/
private lemma curryComparisonRight_naturality_target
    (A B C C' : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ) (hB : IsKFlat Rc B)
    (j : C ⟶ C') :
    (DerivedCategory.Q.map (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C).hom ≫
          strictlyPerfectHomComparison Rc (((Tensor.tensorComplex Rc).obj A).obj B) C ≫
            ((derivedSheafHom Rc).map
                ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A B
                  hB).hom.op).app
              (DerivedCategory.Q.obj C)) ≫
        ((derivedSheafHom Rc).obj
            (op (((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).obj
              (DerivedCategory.Q.obj B)))).map (DerivedCategory.Q.map j) =
      DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 A)
          (RingedSite.homMap (ringedSite Rc) (𝟙 B) j)) ≫
        DerivedCategory.Q.map (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C').hom ≫
          strictlyPerfectHomComparison Rc (((Tensor.tensorComplex Rc).obj A).obj B) C' ≫
            ((derivedSheafHom Rc).map
                ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A B
                  hB).hom.op).app
              (DerivedCategory.Q.obj C') := by
  have hnat := RingedSite.sheafHomTensorCurryIso_natural (ringedSite Rc) (𝟙 A) (𝟙 B) j
  have hid : ((Tensor.tensorComplex Rc).map (𝟙 A)).app B ≫
      ((Tensor.tensorComplex Rc).obj A).map (𝟙 B) =
        𝟙 (((Tensor.tensorComplex Rc).obj A).obj B) := by
    have hA : (Tensor.tensorComplex Rc).map (𝟙 A) = 𝟙 ((Tensor.tensorComplex Rc).obj A) :=
      (Tensor.tensorComplex Rc).map_id A
    have hB' : ((Tensor.tensorComplex Rc).obj A).map (𝟙 B) =
        𝟙 (((Tensor.tensorComplex Rc).obj A).obj B) :=
      ((Tensor.tensorComplex Rc).obj A).map_id B
    rw [hA, hB']
    exact Category.comp_id _
  rw [hid] at hnat
  have hleft : DerivedCategory.Q.map
        (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C).hom ≫
          DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
            (𝟙 (((Tensor.tensorComplex Rc).obj A).obj B)) j) =
      DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 A)
          (RingedSite.homMap (ringedSite Rc) (𝟙 B) j)) ≫
        DerivedCategory.Q.map
          (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C').hom := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hnat]
  have hmid := strictlyPerfectHomComparison_naturality_target Rc
    (((Tensor.tensorComplex Rc).obj A).obj B) C C' j
  have hright := ((derivedSheafHom Rc).map
    ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A B
      hB).hom.op).naturality (DerivedCategory.Q.map j)
  exact paste_three_squares _ _ _ _ _ _ _ _ _ _ hleft hmid.symm hright.symm

/-! ### The square at an arbitrary target -/

/-- **The square at an arbitrary target.**  For complexes `A`, `B`, `C` of `O_X`-modules with
`B` K-flat and `C` *arbitrary*, the canonical comparisons of Stacks 08DM carry the currying
isomorphism of internal Hom complexes of Stacks 0A8M to the derived currying isomorphism of
Stacks 08DJ:

`Q SheafHom^•(A, SheafHom^•(B, C)) ⟶ RSheafHom(QA, RSheafHom(QB, QC))
  ⟶ RSheafHom(QA ⊗^L QB, QC)`

agrees with

`Q SheafHom^•(A, SheafHom^•(B, C)) ⟶ Q SheafHom^•(Tot(A ⊗ B), C)
  ⟶ RSheafHom(Q Tot(A ⊗ B), QC) ⟶ RSheafHom(QA ⊗^L QB, QC)`.

No hypothesis on the target is carried: `C` is released from the K-injective case of
`strictlyPerfectHomComparison_derivedCurryIso_of_isKInjective` along its K-injective
augmentation `j : C ⟶ C'`, by cancelling from the right the induced isomorphism
`RSheafHom(QA ⊗^L QB, QC) ⟶ RSheafHom(QA ⊗^L QB, QC')`, each leg being natural in the target
by `curryComparisonLeft_naturality_target` and
`curryComparisonRight_naturality_target`.  The K-flatness of `B` is a hypothesis of the
complex-level statement itself — it is what makes `Tot(A ⊗_{O_X} B)` compute the derived tensor
product — and so is never released. -/
theorem strictlyPerfectHomComparison_derivedCurryIso
    (A B C : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ) (hB : IsKFlat Rc B) :
    strictlyPerfectHomComparison Rc A (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj ≫
        ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).map
            (strictlyPerfectHomComparison Rc B C) ≫
          (derivedCurryIso Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
            (DerivedCategory.Q.obj C)).hom =
      DerivedCategory.Q.map (RingedSite.sheafHomTensorCurryIso (ringedSite Rc) A B C).hom ≫
        strictlyPerfectHomComparison Rc (((Tensor.tensorComplex Rc).obj A).obj B) C ≫
          ((derivedSheafHom Rc).map
              ((canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight A B
                hB).hom.op).app
            (DerivedCategory.Q.obj C) := by
  obtain ⟨j, hj⟩ : ∃ j : C ⟶ (RingedSite.kInjectiveResolution (ringedSite Rc)).obj C,
      j = (RingedSite.kInjectiveAugmentation (ringedSite Rc)).app C := ⟨_, rfl⟩
  have hqi : QuasiIso j := by rw [hj]; infer_instance
  have resolutionIsIso : IsIso (DerivedCategory.Q.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqi
  let targetFunctor := (derivedSheafHom Rc).obj
    (op (((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).obj
      (DerivedCategory.Q.obj B)))
  have : IsIso (targetFunctor.map (DerivedCategory.Q.map j)) :=
    (targetFunctor.mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map j) resolutionIsIso)).isIso_hom
  refine (cancel_mono (targetFunctor.map (DerivedCategory.Q.map j))).1 ?_
  refine (curryComparisonLeft_naturality_target Rc A B C _ j).trans
    (((congrArg (fun t => DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 A)
        (RingedSite.homMap (ringedSite Rc) (𝟙 B) j)) ≫ t)
      (strictlyPerfectHomComparison_derivedCurryIso_of_isKInjective Rc A B
        ((RingedSite.kInjectiveResolution (ringedSite Rc)).obj C) hB))).trans
      (curryComparisonRight_naturality_target Rc A B C _ hB j).symm)

end Stacks.SheafOfModules

end
