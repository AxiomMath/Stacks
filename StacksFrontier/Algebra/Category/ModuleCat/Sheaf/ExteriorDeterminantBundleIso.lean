module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru

/-!
# The determinant is carried by a comparison of exterior algebras

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `F` be a sheaf of
`O`-modules. `SheafOfModules.TensorExteriorSymmetricAlgebras.determinant` builds `det(F)` as the
direct sum over the degrees of the annihilators `annₙ(F) ⊆ ⋀ⁿ F` of the degree-one part, and
`SheafOfModules.TensorExteriorSymmetricAlgebras.IsExteriorAnnihilated` phrases the annihilator
condition in terms of two fields of the bundle of algebras: the degree-one generator
`A.exteriorGenerator` and the multiplication `A.exterior.mul 1 n`.

This file is what makes that condition transportable. A degreewise comparison
`φ n : ⋀ⁿ F ≅ ⋀ⁿ G` of the exterior algebras of two bundles which **matches the degree-one
generators along an isomorphism `e : F ≅ G` and is multiplicative on homogeneous local
sections** carries the annihilator of either bundle onto the annihilator of the other, hence
`det(F) ≅ det(G)`. The two compatibilities are exactly the two conclusions
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso_generator` and
`exteriorAlgebraIso_mul` draw from the universal property of the exterior algebra, so the
two instantiations below are immediate: the determinant does not depend on the choice of bundle,
and it is carried along an isomorphism of the underlying sheaf of modules.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilatorIso`: **the comparison
  carries `annₙ(F)` onto `annₙ(G)`**, as an isomorphism of the subsheaves.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoOfComparison`:
  **`det(F) ≅ det(G)`**, the direct sum of those isomorphisms.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIso`: **the determinant does not
  depend on the choice of bundle of algebras** — two bundles over one sheaf of modules have
  isomorphic determinants.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoOfIso`: **the determinant is
  carried along an isomorphism of the underlying sheaf of modules.**
* `SheafOfModules.Submodule.factorThruOfLocally`: **a morphism into a sheaf of modules whose
  values lie *locally* in a submodule factors through that submodule.** The annihilator
  condition is read over every arrow out of an object, so a morphism out of a sheafification
  cannot be checked to land in it section by section; this is the form in which the locality of
  the condition — the `isSheaf` field of a `SheafOfModules.Submodule` — is usable.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_of_comparison` and
  `isExteriorAnnihilated_iff_of_comparison`: a local section of `⋀ⁿ F` is exterior annihilated
  exactly when its image under the comparison is. The quantification over arrows out of the
  object and over degree-one sections there is unchanged by the comparison; only the degree-one
  section is translated, along `e`.
* `SheafOfModules.Submodule.ι_val_app_mem`: a local section of the sheaf of modules attached to
  a submodule lies in that submodule, read through the inclusion.

## Implementation notes

**Why the hypotheses are a family of isomorphisms rather than a homomorphism of graded
algebras.** `A.exterior` and `B.exterior` are graded algebras over the same sheaf of rings, so a
`SheafOfModules.GradedAlgebra.UnitalHom` between them would carry the multiplicativity for free;
but the comparisons this is meant to be applied to are produced by
`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`, which returns one isomorphism per degree
together with the two compatibilities separately, and reassembling those into a homomorphism and
then inverting it degreewise would add a layer with nothing in it. Taking `φ`, `hgen` and `hmul`
as the hypotheses lets each of the available comparisons be passed as it stands.

**The isomorphism `e` is not determined by `φ`.** The annihilator condition on a section of
`⋀ⁿ F` quantifies over the local sections `m` of `F` itself, not over sections of the exterior
algebra, so transporting it needs a translation of those; `e` is that translation, and `hgen`
is what ties it to `φ`. For two bundles over the same sheaf of modules `e` is the identity.

**The reverse implication is the forward one at the inverse data.** The inverse family
`fun i => (φ i).symm` satisfies the two compatibilities relative to `e.symm`, and the
derivations of those are the only computation in the file: `hgen` is transposed across `e` and
`φ 1`, and `hmul` is read at the inverse images of the two arguments.

**Why the two factorization hypotheses are separate theorems.** The sections of
`N.toSheafOfModules` over an object are the submodule `N.obj X` itself, but only after the
coercion of `N.toPresheafOfModules.obj X` is unfolded, so writing `y.2` inside the fields of the
isomorphism leaves the elaborated proof ill-typed at `implicit` transparency and the subsequent
`cancel_mono` rewrites fail on it. `comparison_ι_mem_exteriorAnnihilator` and
`comparison_inv_ι_mem_exteriorAnnihilator` state the two membership facts on their own, with the
object and the section given explicitly, and `SheafOfModules.Submodule.ι_val_app_mem` is where
the subtype projection happens, in a statement with nothing else in it.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe w v u

namespace SheafOfModules.Submodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A local section of the sheaf of modules attached to a submodule lies in that submodule,
read through the inclusion. This is `Subtype.property`, isolated so that the subtype structure
of the sections is not exposed where a factorization through the submodule is being built. -/
theorem ι_val_app_mem {M : SheafOfModules.{w} R} (N : M.Submodule) (X : Cᵒᵖ)
    (y : N.toSheafOfModules.val.obj X) : N.ι.val.app X y ∈ N.obj X := y.2

/-- **A morphism into a sheaf of modules whose values lie *locally* in a submodule factors
through that submodule.** Membership in a `SheafOfModules.Submodule` is a local condition — that
is its `isSheaf` field — so the hypothesis of `SheafOfModules.Submodule.factorThru` only has to
be checked on a covering of each object. -/
noncomputable def factorThruOfLocally {M : SheafOfModules.{w} R} (N : M.Submodule)
    {P : SheafOfModules.{w} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.val.obj X),
      N.toSubmodule.toSubfunctor.sieveOfSection (f.val.app X x) ∈ J X.unop) :
    P ⟶ N.toSheafOfModules :=
  N.factorThru f fun X x => N.isSheaf _ (hf X x)

/-- The local factorization, composed with the inclusion of the submodule, is the original
morphism. -/
@[reassoc (attr := simp)]
lemma factorThruOfLocally_ι {M : SheafOfModules.{w} R} (N : M.Submodule)
    {P : SheafOfModules.{w} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.val.obj X),
      N.toSubmodule.toSubfunctor.sieveOfSection (f.val.app X x) ∈ J X.unop) :
    N.factorThruOfLocally f hf ≫ N.ι = f :=
  N.factorThru_ι f _

end SheafOfModules.Submodule

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F G : SheafOfModules.{w} (toRingCat J Osharp)}

section Comparison

variable (A : TensorExteriorSymmetricAlgebras J F) (B : TensorExteriorSymmetricAlgebras J G)
  (e : F ≅ G) (φ : ∀ i : ℤ, A.exterior.piece i ≅ B.exterior.piece i)

/-- The compatibility of the inverse comparison with the degree-one generators. -/
theorem symm_comparison_generator
    (hgen : (e.inv ≫ A.exteriorGenerator) ≫ (φ 1).hom = B.exteriorGenerator) :
    (e.symm.inv ≫ B.exteriorGenerator) ≫ (φ 1).symm.hom = A.exteriorGenerator := by
  have h : e.hom ≫ B.exteriorGenerator = A.exteriorGenerator ≫ (φ 1).hom := by
    rw [← hgen, ← Category.assoc, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  show (e.hom ≫ B.exteriorGenerator) ≫ (φ 1).inv = A.exteriorGenerator
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The multiplicativity of the inverse comparison, read at the inverse images of the two
arguments. -/
theorem symm_comparison_mul
    (hmul : ∀ (i j : ℤ) (V : Cᵒᵖ) (x : (A.exterior.piece i).val.obj V)
      (y : (A.exterior.piece j).val.obj V),
      (φ (i + j)).hom.val.app V ((A.exterior.mul i j).app V x y) =
        (B.exterior.mul i j).app V ((φ i).hom.val.app V x) ((φ j).hom.val.app V y))
    (i j : ℤ) (V : Cᵒᵖ) (x : (B.exterior.piece i).val.obj V)
    (y : (B.exterior.piece j).val.obj V) :
    (φ (i + j)).symm.hom.val.app V ((B.exterior.mul i j).app V x y) =
      (A.exterior.mul i j).app V ((φ i).symm.hom.val.app V x)
        ((φ j).symm.hom.val.app V y) := by
  have e1 : (φ i).hom.val.app V ((φ i).inv.val.app V x) = x :=
    hom_congr_app_apply (φ i).inv_hom_id V x
  have e2 : (φ j).hom.val.app V ((φ j).inv.val.app V y) = y :=
    hom_congr_app_apply (φ j).inv_hom_id V y
  have h := hmul i j V ((φ i).inv.val.app V x) ((φ j).inv.val.app V y)
  rw [e1, e2] at h
  show (φ (i + j)).inv.val.app V ((B.exterior.mul i j).app V x y) =
    (A.exterior.mul i j).app V ((φ i).inv.val.app V x) ((φ j).inv.val.app V y)
  rw [← h]
  exact hom_congr_app_apply (φ (i + j)).hom_inv_id V _

variable (hgen : (e.inv ≫ A.exteriorGenerator) ≫ (φ 1).hom = B.exteriorGenerator)
  (hmul : ∀ (i j : ℤ) (V : Cᵒᵖ) (x : (A.exterior.piece i).val.obj V)
      (y : (A.exterior.piece j).val.obj V),
    (φ (i + j)).hom.val.app V ((A.exterior.mul i j).app V x y) =
      (B.exterior.mul i j).app V ((φ i).hom.val.app V x) ((φ j).hom.val.app V y))

include hgen hmul

/-- **A generator- and multiplication-compatible comparison carries exterior annihilated
sections to exterior annihilated sections.** A degree-one local section of `G` is `e.inv` of one
of `F`, the comparison commutes with restriction because it is a morphism of sheaves of modules,
and `hmul` turns the product computed in `B` into the image of the product computed in `A`,
which vanishes. -/
theorem isExteriorAnnihilated_of_comparison (n : ℕ) {V : Cᵒᵖ}
    {x : (A.exteriorPower n).val.obj V} (hx : A.IsExteriorAnnihilated n x) :
    B.IsExteriorAnnihilated n ((φ (n : ℤ)).hom.val.app V x) := by
  intro W f m
  have hres : (B.exteriorPower n).val.restrictₛₗ f ((φ (n : ℤ)).hom.val.app V x) =
      (φ (n : ℤ)).hom.val.app W ((A.exteriorPower n).val.restrictₛₗ f x) :=
    (PresheafOfModules.naturality_apply (φ (n : ℤ)).hom.val f x).symm
  have hm : B.exteriorGenerator.val.app W m =
      (φ 1).hom.val.app W (A.exteriorGenerator.val.app W (e.inv.val.app W m)) :=
    (hom_congr_app_apply hgen W m).symm
  rw [hres, hm, ← hmul 1 (n : ℤ) W _ _, hx W f (e.inv.val.app W m)]
  exact map_zero _

/-- **The inverse comparison carries exterior annihilated sections to exterior annihilated
sections.** This is the forward statement at the inverse data, which satisfies the same two
compatibilities relative to `e.symm`. -/
theorem isExteriorAnnihilated_of_comparison_inv (n : ℕ) {V : Cᵒᵖ}
    {z : (B.exteriorPower n).val.obj V} (hz : B.IsExteriorAnnihilated n z) :
    A.IsExteriorAnnihilated n ((φ (n : ℤ)).inv.val.app V z) :=
  isExteriorAnnihilated_of_comparison B A e.symm (fun i => (φ i).symm)
    (symm_comparison_generator A B e φ hgen) (symm_comparison_mul A B φ hmul) n hz

/-- **A generator- and multiplication-compatible comparison identifies the two annihilator
conditions.** -/
theorem isExteriorAnnihilated_iff_of_comparison (n : ℕ) {V : Cᵒᵖ}
    (x : (A.exteriorPower n).val.obj V) :
    A.IsExteriorAnnihilated n x ↔
      B.IsExteriorAnnihilated n ((φ (n : ℤ)).hom.val.app V x) := by
  refine ⟨isExteriorAnnihilated_of_comparison A B e φ hgen hmul n, fun hy => ?_⟩
  have h := isExteriorAnnihilated_of_comparison_inv A B e φ hgen hmul n hy
  have hx : (φ (n : ℤ)).inv.val.app V ((φ (n : ℤ)).hom.val.app V x) = x :=
    hom_congr_app_apply (φ (n : ℤ)).hom_inv_id V x
  rwa [hx] at h

/-- The values of `annₙ(F) ⟶ ⋀ⁿ G` lie in `annₙ(G)`: this is the hypothesis of
`SheafOfModules.Submodule.factorThru` for the forward comparison. -/
theorem comparison_ι_mem_exteriorAnnihilator (n : ℕ) (X : Cᵒᵖ)
    (y : (A.exteriorAnnihilator n).toSheafOfModules.val.obj X) :
    ((A.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).hom).val.app X y ∈
      (B.exteriorAnnihilator n).obj X :=
  (mem_exteriorAnnihilator_obj B n
      (((A.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).hom).val.app X y)).mpr
    (isExteriorAnnihilated_of_comparison A B e φ hgen hmul n (V := X)
      (x := (A.exteriorAnnihilator n).ι.val.app X y)
      ((mem_exteriorAnnihilator_obj A n _).mp
        (Submodule.ι_val_app_mem (A.exteriorAnnihilator n) X y)))

/-- The values of `annₙ(G) ⟶ ⋀ⁿ F` lie in `annₙ(F)`: this is the hypothesis of
`SheafOfModules.Submodule.factorThru` for the inverse comparison. -/
theorem comparison_inv_ι_mem_exteriorAnnihilator (n : ℕ) (X : Cᵒᵖ)
    (y : (B.exteriorAnnihilator n).toSheafOfModules.val.obj X) :
    ((B.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).inv).val.app X y ∈
      (A.exteriorAnnihilator n).obj X :=
  (mem_exteriorAnnihilator_obj A n
      (((B.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).inv).val.app X y)).mpr
    (isExteriorAnnihilated_of_comparison_inv A B e φ hgen hmul n (V := X)
      (z := (B.exteriorAnnihilator n).ι.val.app X y)
      ((mem_exteriorAnnihilator_obj B n _).mp
        (Submodule.ι_val_app_mem (B.exteriorAnnihilator n) X y)))

end Comparison

section Determinant

variable (A : TensorExteriorSymmetricAlgebras J F) (B : TensorExteriorSymmetricAlgebras J G)

/-- **A generator- and multiplication-compatible comparison carries `annₙ(F)` onto
`annₙ(G)`.** Both directions are the factorization of the comparison through the annihilator,
and the two round trips are equalities of morphisms into a subsheaf, hence can be cancelled
against its inclusion. -/
def exteriorAnnihilatorIso (e : F ≅ G) (φ : ∀ i : ℤ, A.exterior.piece i ≅ B.exterior.piece i)
    (hgen : (e.inv ≫ A.exteriorGenerator) ≫ (φ 1).hom = B.exteriorGenerator)
    (hmul : ∀ (i j : ℤ) (V : Cᵒᵖ) (x : (A.exterior.piece i).val.obj V)
        (y : (A.exterior.piece j).val.obj V),
      (φ (i + j)).hom.val.app V ((A.exterior.mul i j).app V x y) =
        (B.exterior.mul i j).app V ((φ i).hom.val.app V x) ((φ j).hom.val.app V y))
    (n : ℕ) :
    (A.exteriorAnnihilator n).toSheafOfModules ≅
      (B.exteriorAnnihilator n).toSheafOfModules where
  hom := (B.exteriorAnnihilator n).factorThru
    ((A.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).hom)
    (comparison_ι_mem_exteriorAnnihilator A B e φ hgen hmul n)
  inv := (A.exteriorAnnihilator n).factorThru
    ((B.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).inv)
    (comparison_inv_ι_mem_exteriorAnnihilator A B e φ hgen hmul n)
  hom_inv_id := by
    refine (cancel_mono (A.exteriorAnnihilator n).ι).mp ?_
    rw [Category.assoc, Submodule.factorThru_ι, ← Category.assoc, Submodule.factorThru_ι,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine (cancel_mono (B.exteriorAnnihilator n).ι).mp ?_
    rw [Category.assoc, Submodule.factorThru_ι, ← Category.assoc, Submodule.factorThru_ι,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- **The determinant is carried by a generator- and multiplication-compatible comparison of
the exterior algebras**, degree by degree. -/
def determinantIsoOfComparison (e : F ≅ G)
    (φ : ∀ i : ℤ, A.exterior.piece i ≅ B.exterior.piece i)
    (hgen : (e.inv ≫ A.exteriorGenerator) ≫ (φ 1).hom = B.exteriorGenerator)
    (hmul : ∀ (i j : ℤ) (V : Cᵒᵖ) (x : (A.exterior.piece i).val.obj V)
        (y : (A.exterior.piece j).val.obj V),
      (φ (i + j)).hom.val.app V ((A.exterior.mul i j).app V x y) =
        (B.exterior.mul i j).app V ((φ i).hom.val.app V x) ((φ j).hom.val.app V y)) :
    A.determinant ≅ B.determinant :=
  Sigma.mapIso fun n : ℕ => exteriorAnnihilatorIso A B e φ hgen hmul n

/-- **The determinant is carried along an isomorphism of the underlying sheaf of modules.** The
transported bundle `SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso` has the *same* exterior
algebra as the original, with its degree-one generator precomposed with `e.inv`, so the canonical
comparison of its exterior algebra with that of `B` is a comparison of the exterior algebra of
`A` with that of `B`, matching the generators along `e`. -/
def determinantIsoOfIso (e : F ≅ G) : A.determinant ≅ B.determinant :=
  determinantIsoOfComparison A B e (exteriorAlgebraIso (ofIso J e A) B)
    (exteriorAlgebraIso_generator (ofIso J e A) B)
    (exteriorAlgebraIso_mul (ofIso J e A) B)

end Determinant

/-- **The determinant does not depend on the choice of bundle of tensor, exterior and symmetric
algebras.** Section 17.21 pins the exterior algebra only up to canonical isomorphism, and the
canonical comparison `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso` matches
the generators and is multiplicative, which is exactly what the annihilator condition needs. -/
def determinantIso (A B : TensorExteriorSymmetricAlgebras J F) :
    A.determinant ≅ B.determinant :=
  determinantIsoOfComparison A B (Iso.refl F) (exteriorAlgebraIso A B)
    (by rw [Iso.refl_inv, Category.id_comp]; exact exteriorAlgebraIso_generator A B)
    (exteriorAlgebraIso_mul A B)

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
