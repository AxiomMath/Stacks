module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictClosed
public import StacksFrontier.CategoryTheory.Monoidal.InternalEndFunctor
public import StacksFrontier.CategoryTheory.Monoidal.InternalEndMonoid
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteLocallyFree
public import StacksFrontier.CategoryTheory.Monoidal.InternalEndTensorIso
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomDual
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of algebras on a scheme, their tensor product, and endomorphism algebras

Let `S` be a scheme. A sheaf of (not necessarily commutative) `𝒪_S`-algebras is a monoid object
in the symmetric monoidal category of sheaves of `𝒪_S`-modules, the tensor product being the
tensor product sheaf of [Stacks, Tag 01CA]. Unwinding the definition, this is a sheaf of
`𝒪_S`-modules `A` together with an `𝒪_S`-bilinear, associative multiplication and a unit
section; `𝒪_S`-bilinearity of the multiplication is exactly the requirement that the image of
`𝒪_S` be central, so no centrality hypothesis has to be carried separately.

Taking monoid objects in a *symmetric* monoidal category produces a monoidal category again,
and that monoidal structure is the tensor product `A ⊗_{𝒪_S} B` of sheaves of algebras, with
`𝒪_S` itself as unit. These are the operations the Brauer group of a scheme
([Stacks, Tag 0A2J]) is built from.

Tag 0A2J names three things. An `𝒪_S`-algebra is **Azumaya** if it is étale locally a matrix
algebra, i.e. if there is an étale covering `{φ_i : U_i → S}` with `φ_i^* A ≅ Mat_{d_i}(𝒪_{U_i})`
for some `d_i ≥ 1`. Two Azumaya algebras `A` and `B` are **equivalent** if there are finite
locally free `𝒪_S`-modules `F` and `G` of positive rank at every point with
`A ⊗_{𝒪_S} 𝓗om(F,F) ≅ B ⊗_{𝒪_S} 𝓗om(G,G)` as `𝒪_S`-algebras. The **Brauer group** `Br(S)` is
the set of equivalence classes of Azumaya `𝒪_S`-algebras with the operation induced by the
tensor product. The second of the three is `IsSimilar` below, with `similarSetoid` and
`IsSimilar.tensor` supplying the relation and the operation; the first is `IsAzumaya`, and
`BrauerGroup` with `BrauerGroup.mul` is `Br(S)` with its operation.

The other ingredient is the endomorphism algebra `End(E)` of a sheaf of `𝒪_S`-modules `E`. The
tensor product sheaf makes sheaves of `𝒪_S`-modules monoidal *closed*
(`Stacks.SheafOfModules.Strict.strictMonoidalClosed`), and in any closed monoidal category the
internal hom `E ⟶[·] E` is a monoid object; `endAlgebra` is that monoid object. The matrix
algebra `Mat_d(𝒪_S)` is the endomorphism algebra of the free module of rank `d`.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.ModuleSheaf`: sheaves of `𝒪_S`-modules, in the spelling
  carrying the tensor-product-sheaf monoidal structure.
* `Stacks.EtaleCohomology.BrauerScheme.AlgebraSheaf`: sheaves of (not necessarily commutative)
  `𝒪_S`-algebras, as monoid objects in `ModuleSheaf S`; the tensor product of two of them is
  the monoidal product of `Mon`.
* `Stacks.EtaleCohomology.BrauerScheme.endAlgebra`: the endomorphism algebra sheaf of a sheaf
  of `𝒪_S`-modules, and `matrixAlgebra` the algebra of `d × d` matrices over `𝒪_S`.
* `Stacks.EtaleCohomology.BrauerScheme.endAlgebraTensorHom`: the canonical map of `𝒪_S`-algebras
  `End(E) ⊗ End(F) ⟶ End(E ⊗ F)`, and `endAlgebraTensorIso` the isomorphism it is for finite
  locally free `E` and `F`.
* `Stacks.EtaleCohomology.BrauerScheme.HasPositiveRank`: a sheaf of modules is locally free
  with inhabited local bases, i.e. has positive rank at every point.
* `Stacks.EtaleCohomology.BrauerScheme.oppositeAlgebra`: the opposite of a sheaf of
  `𝒪_S`-algebras.
* `Stacks.EtaleCohomology.BrauerScheme.similarSetoid`: similarity as a setoid.
* `Stacks.EtaleCohomology.BrauerScheme.algebraPullback`: the pullback of a sheaf of
  `𝒪_S`-algebras along a morphism of schemes.
* `Stacks.EtaleCohomology.BrauerScheme.IsAzumaya`: **the Azumaya condition of Tag 0A2J** — étale
  locally a matrix algebra.
* `Stacks.EtaleCohomology.BrauerScheme.Azumaya`, `azumayaSetoid` and
  `Stacks.EtaleCohomology.BrauerScheme.BrauerGroup`: the Azumaya algebra sheaves, similarity on
  them, and **`Br(S)`** as the set of similarity classes; `brauerClass` is the class of an
  Azumaya algebra.
* `Stacks.EtaleCohomology.BrauerScheme.endAlgebraCongr` and `matrixAlgebraTensorIso`:
  `𝓗om(E,E) ≅ 𝓗om(F,F)` for `E ≅ F`, and `Mat_d(𝒪_S) ⊗ Mat_e(𝒪_S) ≅ Mat_{d·e}(𝒪_S)`.
* `Stacks.EtaleCohomology.BrauerScheme.IsTrivialClass`: an algebra sheaf is the endomorphism
  algebra of a finite locally free sheaf of modules of positive rank. These are the algebras
  whose Brauer class is trivial.
* `Stacks.EtaleCohomology.BrauerScheme.IsSimilar`: the equivalence of [Stacks, Tag 0A2J], that
  two algebra sheaves become isomorphic after tensoring each with the endomorphism algebra of
  a finite locally free sheaf of modules of positive rank.
* `Stacks.EtaleCohomology.BrauerScheme.braidedModulePullback`, `algebraPullbackComp` and
  `modulePullbackFreeIso`: the pullback of sheaves of modules is braided monoidal, hence acts
  on sheaves of algebras; it splits along a composite; and it carries a free sheaf of modules
  to a free sheaf of modules.
* `Stacks.EtaleCohomology.BrauerScheme.coverInter`: **the common refinement of two étale
  coverings**, the family of fibre products.
* `Stacks.EtaleCohomology.BrauerScheme.BrauerGroup.mul`: **the operation of Tag 0A2J's Brauer
  group**, induced by the tensor product.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.tensorUnit_eq`: the unit algebra sheaf is `𝒪_S`.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_free` and
  `hasPositiveRank_free`: a free sheaf of modules on a finite inhabited index type is finite
  locally free of positive rank, so `matrixAlgebra S d` has trivial class for `0 < d`.
* `Stacks.EtaleCohomology.BrauerScheme.IsSimilar.refl`,
  `Stacks.EtaleCohomology.BrauerScheme.IsSimilar.symm` and
  `Stacks.EtaleCohomology.BrauerScheme.IsSimilar.of_iso`: similarity is reflexive and
  symmetric, and isomorphic algebra sheaves are similar.
* `Stacks.EtaleCohomology.BrauerScheme.IsTrivialClass.endAlgebra`: the endomorphism algebra of
  a finite locally free sheaf of modules of positive rank has trivial class.
* `Stacks.EtaleCohomology.BrauerScheme.nonempty_hasRightDual_of_isFiniteLocallyFree` and
  `isIso_tensorInternalEnd_of_isFiniteLocallyFree`: a finite locally free sheaf of modules is
  dualizable, so the comparison `End(E) ⊗ End(F) ⟶ End(E ⊗ F)` is invertible.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_tensor` and `hasPositiveRank_tensor`:
  a tensor product of finite locally free sheaves of modules of positive rank is again one.
* `Stacks.EtaleCohomology.BrauerScheme.IsSimilar.trans`,
  `Stacks.EtaleCohomology.BrauerScheme.isSimilar_equivalence` and
  `Stacks.EtaleCohomology.BrauerScheme.similarSetoid`: **similarity is an equivalence
  relation.**
* `Stacks.EtaleCohomology.BrauerScheme.IsSimilar.tensor`: similarity is compatible with the
  tensor product, so the tensor product descends to similarity classes. This is half of the
  well-definedness of the multiplication of the Brauer group.
* `Stacks.EtaleCohomology.BrauerScheme.nonempty_endAlgebraPullbackIso` and
  `nonempty_matrixAlgebraPullbackIso`: **the pullback of an endomorphism algebra of a finite
  locally free sheaf of modules is the endomorphism algebra of the pullback**, and in
  particular the pullback of a matrix algebra is a matrix algebra.
* `Stacks.EtaleCohomology.BrauerScheme.IsAzumaya.tensor`: **a tensor product of Azumaya
  algebra sheaves is Azumaya.** This is the other half of the well-definedness of the
  multiplication of the Brauer group.

## Implementation notes

The monoidal structure used on `ModuleSheaf S` is the *strict* one of
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product is the tensor product
sheaf of Tag 01CA on the nose, rather than the localized structure, which is only isomorphic to
it. Its braiding, symmetry and closedness are the ones transported there.

None of the monoidal instances on `ModuleSheaf S` is global: a global monoidal instance on
sheaves of modules would be found by instance search in every statement about sheaves of
modules, including those meaning a different tensor product. They are declared `scoped` in
`Stacks.EtaleCohomology.BrauerScheme`, so a consumer activates them all at once by opening that
namespace. `AlgebraSheaf` is an abbreviation, so the instance it is elaborated against is baked
into the resulting term and does not have to be re-synthesized downstream.

**Which monoidal structure on the pullback.** The Azumaya condition needs the pullback of a
sheaf of *algebras*, so it needs `modulePullback φ` as a monoidal functor, and the library has
**two** such structures on the same functor, neither registered as an instance:
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, whose tensorator is by
construction the comparison `φ^*(A ⊗ B) ≅ φ^*A ⊗ φ^*B` of Tag 01CD
(`Stacks.RingedSpace.comparison`), and `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`,
obtained from the monoidal structure of the localization. `monoidalModulePullback` below
chooses the first, so the Azumaya condition is stated against the canonical comparison of
Tag 01CD that the source means. Both structures are for the *same* monoidal categories on
source and target, so the choice does not change which category `AlgebraSheaf` is; it changes
only which isomorphism `algebraPullback` transports a multiplication along.

**The identification that is not made here.** That the two monoidal structures agree is not
proved anywhere — `PullbackTensorCoherence`'s own module docstring says so. It remains open, so
here is the route. It is *not* available from the uniqueness of the comparison
(`Stacks.RingedSpace.comparison_unique`): that reduces the goal to the action of the localized
oplax tensorator on the sheafification-unit images of local pure tensors, which is exactly what
the universal property of the localization does not supply, so the uniqueness clause's
hypothesis is itself the unknown. What does work is a formal unfold:
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal_mu` expresses the localized tensorator through
`liftingIso`, the *presheaf*-level tensorator and the sheafification oplax structure map; then
`Stacks.PullbackMonoidalSheaf.presheafPullback_mu_comp` identifies that presheaf-level
tensorator with the inverse of `Stacks.PullbackTensor.pullbackTensorIso`, the presheaf-level
comparison of Tag 01CD — which is objectwise and therefore does compute on pure tensors. The
two bridges `Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal` and
`fromLocalizedMonoidalMonoidal`, which make the identity functor between the strict and the
localized spellings monoidal in both directions, close the gap. When that is proved,
`pullbackStrictMonoidal` and `pullbackComparisonMonoidal` collapse to one structure and the
choice recorded in the previous paragraph stops being a choice.

**All four things Tag 0A2J names are here**: the Azumaya condition `IsAzumaya`, the equivalence
`IsSimilar`, the Brauer group `BrauerGroup` and its operation `BrauerGroup.mul`. The operation
is well defined because `IsSimilar.tensor` makes the tensor product descend to similarity
classes and `IsAzumaya.tensor` keeps it inside the Azumaya algebras. The latter rests on three
comparisons for the pullback, each proved elsewhere and used here:

* `modulePullback φ` is braided monoidal (`braidedModulePullback`), so
  `CategoryTheory.Functor.mapMon` is monoidal and the pullback's tensorator
  `φ^*(A ⊗ B) ≅ φ^*A ⊗ φ^*B` is an isomorphism of sheaves of *algebras*.
* the composition law `algebraPullbackComp`, which splits the pullback along a composite,
  because a member of the common refinement of two étale coverings reaches `S` through one of
  the two given coverings.
* `nonempty_matrixAlgebraPullbackIso`, that the pullback of a matrix algebra is a matrix
  algebra. This comes from `CategoryTheory.MonoidalClosed.internalEndFunctorIso` — a braided
  monoidal functor commutes with the internal endomorphism monoid of a dualizable object —
  together with `modulePullbackFreeIso`.

The common refinement of the two coverings is `coverInter`, the family of fibre products
`U_i ×_S V_j`. It is built by hand rather than with
`CategoryTheory.Precoverage.ZeroHypercover.inter`, which would need the étale precoverage
registered as stable under base change and composition; it is not, because
`AlgebraicGeometry.Scheme.etalePrecoverage` is a plain definition and instance search does not
unfold it.

Tag 0A2J's `Br(S)` is "the set of equivalence classes with the operation induced by tensor
product", so it is a commutative monoid; a *group* structure is not part of what the tag states.
The inverse of a class would be the opposite algebra, `oppositeAlgebra`, and it needs
`A ⊗ Aᵒᵖ ≅ 𝓗om(A,A)` for an Azumaya `A`, which does not follow from `endAlgebraTensorIso`: that
compares endomorphism algebras of two modules, whereas this compares an arbitrary Azumaya
algebra with the endomorphisms of its own underlying module, and proving it means descending the
matrix case along the étale covering.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2K](https://stacks.math.columbia.edu/tag/0A2K)
* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable (S : Scheme.{u})

/-- Sheaves of `𝒪_S`-modules on a scheme `S`, spelled so as to carry the monoidal structure
whose tensor product is the tensor product sheaf of Tag 01CA. -/
abbrev ModuleSheaf : Type (u + 1) := Stacks.SheafOfModules.Strict.Mod S.sheaf

/-- The tensor product of sheaves of `𝒪_S`-modules, Tag 01CA. -/
scoped instance monoidalModuleSheaf : MonoidalCategory (ModuleSheaf S) :=
  (Stacks.SheafOfModules.Strict.monoidalCategory (S.sheaf).obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.sheaf)).property)

/-- The tensor product of sheaves of `𝒪_S`-modules is braided. -/
scoped instance braidedModuleSheaf : BraidedCategory (ModuleSheaf S) :=
  Strict.braidedCategory S.sheaf.obj (Strict.isSheaf_ringSheaf S.sheaf)

/-- The braiding of the tensor product of sheaves of `𝒪_S`-modules is a symmetry. -/
scoped instance symmetricModuleSheaf : SymmetricCategory (ModuleSheaf S) :=
  Strict.symmetricCategory S.sheaf.obj (Strict.isSheaf_ringSheaf S.sheaf)

/-- Sheaves of `𝒪_S`-modules are monoidal closed for the tensor product sheaf; the internal
hom is the sheaf hom. -/
scoped instance closedModuleSheaf : MonoidalClosed (ModuleSheaf S) :=
  Strict.strictMonoidalClosed S.sheaf

/-- A sheaf of (not necessarily commutative) `𝒪_S`-algebras: a monoid object in the symmetric
monoidal category of sheaves of `𝒪_S`-modules. The structure morphism from `𝒪_S` is central
because the multiplication is a morphism out of the tensor product over `𝒪_S`. -/
abbrev AlgebraSheaf : Type (u + 1) := Mon (ModuleSheaf S)

/-- Morphisms of sheaves of `𝒪_S`-algebras. -/
scoped instance categoryAlgebraSheaf : Category (AlgebraSheaf S) := inferInstance

/-- The tensor product `A ⊗_{𝒪_S} B` of sheaves of `𝒪_S`-algebras, with unit `𝒪_S`. -/
scoped instance monoidalAlgebraSheaf : MonoidalCategory (AlgebraSheaf S) := inferInstance

/-- The tensor product of sheaves of `𝒪_S`-algebras is symmetric. -/
scoped instance symmetricAlgebraSheaf : SymmetricCategory (AlgebraSheaf S) := inferInstance

/-- The underlying sheaf of modules of the unit algebra sheaf is `𝒪_S`. -/
lemma tensorUnit_eq : (𝟙_ (AlgebraSheaf S)).X = SheafOfModules.unit _ := rfl

/-- The underlying sheaf of modules of a tensor product of algebra sheaves is the tensor
product of the underlying sheaves of modules. -/
lemma tensorObj_X (A B : AlgebraSheaf S) : (A ⊗ B).X = A.X ⊗ B.X := rfl

variable {S}

/-- The endomorphism algebra sheaf `End(E)` of a sheaf of `𝒪_S`-modules: the internal hom
`Hom_{𝒪_S}(E, E)` with composition as multiplication. -/
abbrev endAlgebra (E : ModuleSheaf S) : AlgebraSheaf S := MonoidalClosed.internalEnd E

/-- The canonical map of `𝒪_S`-algebras `End(E) ⊗ End(F) ⟶ End(E ⊗ F)`, the external tensor
product of endomorphisms. It is an isomorphism when `E` and `F` are dualizable; see the
implementation notes of `StacksFrontier.CategoryTheory.Monoidal.InternalEndMonoid`. -/
@[sga "5 IIIB 5.12" "special case"]
abbrev endAlgebraTensorHom (E F : ModuleSheaf S) :
    endAlgebra E ⊗ endAlgebra F ⟶ endAlgebra (E ⊗ F) :=
  MonoidalClosed.tensorInternalEndHom E F

/-- **A finite locally free sheaf of `𝒪_S`-modules admits a dual**, Tag 0FNY. -/
theorem nonempty_hasRightDual_of_isFiniteLocallyFree {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E) : Nonempty (HasRightDual E) :=
  Stacks.SheafOfModules.nonempty_hasRightDual_of_isFiniteLocallyFree S.presheaf _ E hE

/-- **The comparison `End(E) ⊗ End(F) ⟶ End(E ⊗ F)` is invertible for finite locally free
sheaves of modules**, because those are dualizable. -/
theorem isIso_tensorInternalEnd_of_isFiniteLocallyFree {E F : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F) :
    IsIso (MonoidalClosed.tensorInternalEnd E F) :=
  MonoidalClosed.isIso_tensorInternalEnd_of_nonempty_hasRightDual E F
    (nonempty_hasRightDual_of_isFiniteLocallyFree hE)
    (nonempty_hasRightDual_of_isFiniteLocallyFree hF)

/-- **`End(E) ⊗ End(F) ≅ End(E ⊗ F)` as `𝒪_S`-algebras, for finite locally free `E` and `F`.**
This is the input transitivity of `IsSimilar` needs. -/
def endAlgebraTensorIso {E F : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F) :
    endAlgebra E ⊗ endAlgebra F ≅ endAlgebra (E ⊗ F) :=
  letI := isIso_tensorInternalEnd_of_isFiniteLocallyFree hE hF
  MonoidalClosed.tensorInternalEndIso E F

/-- **An isomorphism of sheaves of modules induces an isomorphism of their endomorphism
algebra sheaves**, by conjugation. -/
def endAlgebraCongr {E F : ModuleSheaf S} (e : E ≅ F) : endAlgebra E ≅ endAlgebra F :=
  MonoidalClosed.internalEndCongr e

variable (S)

/-- The sheaf of `d × d` matrices over `𝒪_S`, as the endomorphism algebra of the free sheaf of
modules of rank `d`. -/
abbrev matrixAlgebra (d : ℕ) : AlgebraSheaf S :=
  endAlgebra (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)
    (ULift.{u, 0} (Fin d)))

variable {S}

/-- A sheaf of `𝒪_S`-modules has positive rank if it admits local generators which are local
bases and whose indexing types are all inhabited. This is Tag 0A2J's "positive rank at every
`s ∈ S`": a point of `S` lies in some member of the covering, and the rank there is the
cardinality of that member's index type, so inhabitedness of every index type is positivity of
the rank at every point. It is also the positivity hypothesis under which Tag 0A2K determines a
sheaf of modules from its endomorphism algebra. -/
def HasPositiveRank (E : ModuleSheaf S) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} E,
    q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I

/-- A free sheaf of modules on a finite index type is finite locally free. -/
lemma isFiniteLocallyFree_free (I : Type u) [Finite I] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S)
      (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf) I) := by
  constructor
  refine ⟨(SheafOfModules.free.generatingSections
      (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf) I).localGeneratorsData, ?_, ?_⟩
  · infer_instance
  · exact { isFiniteType := fun _ => { finite := inferInstanceAs (Finite I) } }

/-- A free sheaf of modules on an inhabited index type has positive rank. -/
lemma hasPositiveRank_free (I : Type u) [Nonempty I] :
    HasPositiveRank
      (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf) I) :=
  ⟨(SheafOfModules.free.generatingSections I).localGeneratorsData, inferInstance,
    fun _ => inferInstanceAs (Nonempty I)⟩

/-- A sheaf of `𝒪_S`-algebras has trivial Brauer class if it is the endomorphism algebra of a
finite locally free sheaf of `𝒪_S`-modules of positive rank. -/
def IsTrivialClass (A : AlgebraSheaf S) : Prop :=
  ∃ E : ModuleSheaf S, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E ∧
    HasPositiveRank E ∧ Nonempty (A ≅ endAlgebra E)

/-- **The equivalence of Tag 0A2J.** Two sheaves of `𝒪_S`-algebras `A` and `B` are similar if
there are finite locally free sheaves of `𝒪_S`-modules `F` and `G` of positive rank at every
point of `S` with `A ⊗_{𝒪_S} 𝓗om(F,F) ≅ B ⊗_{𝒪_S} 𝓗om(G,G)` as `𝒪_S`-algebras. The Brauer
group of `S` is the set of equivalence classes of *Azumaya* `𝒪_S`-algebras for this relation,
with the operation induced by the tensor product. -/
@[stacks 0A2J "the equivalence of Azumaya algebras"]
def IsSimilar (A B : AlgebraSheaf S) : Prop :=
  ∃ E F : ModuleSheaf S,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E ∧ HasPositiveRank E ∧
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F ∧ HasPositiveRank F ∧
    Nonempty (A ⊗ endAlgebra E ≅ B ⊗ endAlgebra F)

/-- Isomorphic sheaves of `𝒪_S`-algebras are similar. -/
lemma IsSimilar.of_iso {A B : AlgebraSheaf S} (e : A ≅ B) : IsSimilar A B :=
  ⟨SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)
      (ULift.{u, 0} (Fin 1)),
    SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)
      (ULift.{u, 0} (Fin 1)),
    isFiniteLocallyFree_free _, hasPositiveRank_free _,
    isFiniteLocallyFree_free _, hasPositiveRank_free _,
    ⟨e ⊗ᵢ Iso.refl _⟩⟩

/-- Similarity of sheaves of `𝒪_S`-algebras is reflexive. -/
lemma IsSimilar.refl (A : AlgebraSheaf S) : IsSimilar A A := IsSimilar.of_iso (Iso.refl A)

/-- Similarity of sheaves of `𝒪_S`-algebras is symmetric. -/
lemma IsSimilar.symm {A B : AlgebraSheaf S} (h : IsSimilar A B) : IsSimilar B A := by
  obtain ⟨E, F, hE, hEp, hF, hFp, ⟨e⟩⟩ := h
  exact ⟨F, E, hF, hFp, hE, hEp, ⟨e.symm⟩⟩

/-- The endomorphism algebra of a finite locally free sheaf of modules of positive rank has
trivial Brauer class. -/
lemma IsTrivialClass.endAlgebra {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E) (hEp : HasPositiveRank E) :
    IsTrivialClass (BrauerScheme.endAlgebra E) :=
  ⟨E, hE, hEp, ⟨Iso.refl _⟩⟩

/-- The sheaf of `d × d` matrices over `𝒪_S` has trivial Brauer class for `0 < d`. -/
lemma isTrivialClass_matrixAlgebra (S : Scheme.{u}) {d : ℕ} (hd : 0 < d) :
    IsTrivialClass (matrixAlgebra S d) :=
  have : Nonempty (ULift.{u, 0} (Fin d)) := ⟨⟨⟨0, hd⟩⟩⟩
  IsTrivialClass.endAlgebra (isFiniteLocallyFree_free _) (hasPositiveRank_free _)

/-- **Similarity of sheaves of `𝒪_S`-algebras is transitive**, given that a tensor product of
finite locally free sheaves of `𝒪_S`-modules of positive rank is again finite locally free of
positive rank. -/
theorem IsSimilar.trans_of
    (hflf : ∀ E F : ModuleSheaf S,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
        (J := Opens.grothendieckTopology S) E →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
        (J := Opens.grothendieckTopology S) F →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
        (J := Opens.grothendieckTopology S) (E ⊗ F))
    (hpos : ∀ E F : ModuleSheaf S, HasPositiveRank E → HasPositiveRank F →
      HasPositiveRank (E ⊗ F))
    {A B D : AlgebraSheaf S} (h₁ : IsSimilar A B) (h₂ : IsSimilar B D) : IsSimilar A D := by
  obtain ⟨E, F, hE, hEp, hF, hFp, ⟨e₁⟩⟩ := h₁
  obtain ⟨G, H, hG, hGp, hH, hHp, ⟨e₂⟩⟩ := h₂
  refine ⟨E ⊗ G, H ⊗ F, hflf _ _ hE hG, hpos _ _ hEp hGp, hflf _ _ hH hF,
    hpos _ _ hHp hFp, ⟨?_⟩⟩
  calc A ⊗ endAlgebra (E ⊗ G)
      ≅ A ⊗ (endAlgebra E ⊗ endAlgebra G) := whiskerLeftIso A (endAlgebraTensorIso hE hG).symm
    _ ≅ (A ⊗ endAlgebra E) ⊗ endAlgebra G := (α_ _ _ _).symm
    _ ≅ (B ⊗ endAlgebra F) ⊗ endAlgebra G := tensorIso e₁ (Iso.refl _)
    _ ≅ B ⊗ (endAlgebra F ⊗ endAlgebra G) := α_ _ _ _
    _ ≅ B ⊗ (endAlgebra G ⊗ endAlgebra F) := whiskerLeftIso B (β_ _ _)
    _ ≅ (B ⊗ endAlgebra G) ⊗ endAlgebra F := (α_ _ _ _).symm
    _ ≅ (D ⊗ endAlgebra H) ⊗ endAlgebra F := tensorIso e₂ (Iso.refl _)
    _ ≅ D ⊗ (endAlgebra H ⊗ endAlgebra F) := α_ _ _ _
    _ ≅ D ⊗ endAlgebra (H ⊗ F) := whiskerLeftIso D (endAlgebraTensorIso hH hF)

/-- **A tensor product of finite locally free sheaves of `𝒪_S`-modules is finite locally
free**, Tag 03L6 for the finite locally free condition. -/
theorem isFiniteLocallyFree_tensor {E F : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) (E ⊗ F) :=
  Stacks.SheafOfModules.isFiniteLocallyFree_tensor S.sheaf hE hF

/-- **A tensor product of sheaves of `𝒪_S`-modules of positive rank has positive rank.** -/
theorem hasPositiveRank_tensor {E F : ModuleSheaf S} (hE : HasPositiveRank E)
    (hF : HasPositiveRank F) : HasPositiveRank (E ⊗ F) :=
  Stacks.SheafOfModules.exists_isLocallyFreeData_nonempty_tensor S.sheaf hE hF

/-- **Similarity of sheaves of `𝒪_S`-algebras is transitive.** -/
theorem IsSimilar.trans {A B D : AlgebraSheaf S} (h₁ : IsSimilar A B) (h₂ : IsSimilar B D) :
    IsSimilar A D :=
  IsSimilar.trans_of (fun _ _ hE hF => isFiniteLocallyFree_tensor hE hF)
    (fun _ _ hE hF => hasPositiveRank_tensor hE hF) h₁ h₂

/-- **The opposite of a sheaf of `𝒪_S`-algebras**: the same sheaf of modules with the
multiplication twisted by the braiding. In `Br(S)` the class of `Aᵒᵖ` is the inverse of the
class of `A`; that needs the identification `A ⊗ Aᵒᵖ ≅ 𝓗om(A,A)` for an Azumaya `A`, which is
not available here. -/
def oppositeAlgebra (S : Scheme.{u}) : AlgebraSheaf S ⥤ AlgebraSheaf S :=
  (mopFunctor (ModuleSheaf S)).mapMon ⋙ (MonObj.mopEquiv (ModuleSheaf S)).inverse

/-- The underlying sheaf of modules of the opposite algebra `Aᵒᵖ` is that of `A`. -/
@[simp]
lemma oppositeAlgebra_obj_X (A : AlgebraSheaf S) : ((oppositeAlgebra S).obj A).X = A.X := rfl

/-- The interchange isomorphism of `𝒪_S`-algebras. -/
def tensorμIso (A B P R : AlgebraSheaf S) : (A ⊗ B) ⊗ (P ⊗ R) ≅ (A ⊗ P) ⊗ (B ⊗ R) where
  hom := tensorμ A B P R
  inv := tensorδ A B P R
  hom_inv_id := tensorμ_tensorδ _ _ _ _
  inv_hom_id := tensorδ_tensorμ _ _ _ _

/-- **Similarity is compatible with the tensor product**, so the tensor product descends to
similarity classes. This is the well-definedness of the multiplication of the Brauer group. -/
theorem IsSimilar.tensor {A A' B B' : AlgebraSheaf S} (h₁ : IsSimilar A A')
    (h₂ : IsSimilar B B') : IsSimilar (A ⊗ B) (A' ⊗ B') := by
  obtain ⟨E, F, hE, hEp, hF, hFp, ⟨e₁⟩⟩ := h₁
  obtain ⟨G, H, hG, hGp, hH, hHp, ⟨e₂⟩⟩ := h₂
  refine ⟨E ⊗ G, F ⊗ H, isFiniteLocallyFree_tensor hE hG, hasPositiveRank_tensor hEp hGp,
    isFiniteLocallyFree_tensor hF hH, hasPositiveRank_tensor hFp hHp, ⟨?_⟩⟩
  calc (A ⊗ B) ⊗ endAlgebra (E ⊗ G)
      ≅ (A ⊗ B) ⊗ (endAlgebra E ⊗ endAlgebra G) :=
        whiskerLeftIso _ (endAlgebraTensorIso hE hG).symm
    _ ≅ (A ⊗ endAlgebra E) ⊗ (B ⊗ endAlgebra G) := tensorμIso _ _ _ _
    _ ≅ (A' ⊗ endAlgebra F) ⊗ (B' ⊗ endAlgebra H) := tensorIso e₁ e₂
    _ ≅ (A' ⊗ B') ⊗ (endAlgebra F ⊗ endAlgebra H) := (tensorμIso _ _ _ _).symm
    _ ≅ (A' ⊗ B') ⊗ endAlgebra (F ⊗ H) :=
        whiskerLeftIso _ (endAlgebraTensorIso hF hH)

/-- **Similarity of sheaves of `𝒪_S`-algebras is an equivalence relation.** -/
theorem isSimilar_equivalence (S : Scheme.{u}) :
    Equivalence (IsSimilar (S := S)) where
  refl := IsSimilar.refl
  symm := IsSimilar.symm
  trans := IsSimilar.trans

/-- Similarity of sheaves of `𝒪_S`-algebras as a setoid. The Brauer group of `S` is the
quotient of the Azumaya algebra sheaves by this relation. -/
def similarSetoid (S : Scheme.{u}) : Setoid (AlgebraSheaf S) where
  r := IsSimilar
  iseqv := isSimilar_equivalence S

/-- The pullback of sheaves of modules along a morphism of schemes, read through the underlying
morphism of ringed spaces. -/
abbrev modulePullback {T S : Scheme.{u}} (φ : T ⟶ S) : ModuleSheaf S ⥤ ModuleSheaf T :=
  Stacks.RingedSpace.pullbackFunctor φ.toLRSHom.toShHom

/-- **The pullback of sheaves of modules along a morphism of schemes is monoidal**, Tag 01CD:
`φ^*(A ⊗ B) ≅ φ^*A ⊗ φ^*B` and `φ^* 𝒪_S ≅ 𝒪_T`, the first comparison being the one of Tag 01CD
on the nose (`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal_mu`).

The library has a second `CategoryTheory.Functor.Monoidal` structure on this same functor,
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, coming from the monoidal structure of
the localization; the two are for the same monoidal categories but are not known to be equal.
This one is chosen because its tensorator *is* the comparison of Tag 01CD, which is the map the
Stacks Project means; see the implementation notes.

Deliberately not an instance: `braidedModulePullback` below is the instance, and
`CategoryTheory.Functor.Braided` extends `CategoryTheory.Functor.Monoidal`, so registering both
would give instance search two routes to the same monoidal structure. -/
@[instance_reducible]
def monoidalModulePullback {T S : Scheme.{u}} (φ : T ⟶ S) :
    (modulePullback φ).Monoidal :=
  Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal φ.toLRSHom.toShHom

/-- **The pullback of sheaves of modules along a morphism of schemes is braided monoidal**: the
comparison of Tag 01CD commutes with the symmetry constraint of Tag 01CA
(`Stacks.PullbackTensorCoherence.pullbackComparisonBraided`). This is the instance carrying the
monoidal structure of `monoidalModulePullback`, and it is what makes the pullback act on
sheaves of algebras as a monoidal functor. -/
@[instance_reducible]
scoped instance braidedModulePullback {T S : Scheme.{u}} (φ : T ⟶ S) :
    (modulePullback φ).Braided :=
  Stacks.PullbackTensorCoherence.pullbackComparisonBraided φ.toLRSHom.toShHom

/-- **The composition law for the pullback of sheaves of modules**, `ρ^* φ^* ≅ (ρ ≫ φ)^*` of
Tag 0097, named at the spelling of this namespace. -/
def modulePullbackComp {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) :
    modulePullback φ ⋙ modulePullback ρ ≅ modulePullback (ρ ≫ φ) :=
  Stacks.PullbackTensorCoherence.pullbackCompIso ρ.toLRSHom.toShHom φ.toLRSHom.toShHom

/-- **The composition law for pullback is a monoidal natural isomorphism**, so it carries over
to sheaves of algebras. -/
theorem isMonoidal_modulePullbackComp {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) :
    NatTrans.IsMonoidal (modulePullbackComp ρ φ).hom :=
  Stacks.PullbackTensorCoherence.isMonoidal_pullbackCompIso_hom ρ.toLRSHom.toShHom
    φ.toLRSHom.toShHom

/-- **The pullback of a sheaf of `𝒪_S`-algebras** along a morphism of schemes: the pullback of
the underlying sheaf of modules, with the multiplication transported along the monoidal
structure of `modulePullback`, i.e. along the comparison of Tag 01CD.

An abbreviation, so that the monoidal structure of `CategoryTheory.Functor.mapMon` — which
exists because `modulePullback φ` is braided (`braidedModulePullback`) — is found by instance
search through it: `φ^*(A ⊗ B) ≅ φ^*A ⊗ φ^*B` as sheaves of algebras, not merely as sheaves of
modules. -/
abbrev algebraPullback {T S : Scheme.{u}} (φ : T ⟶ S) : AlgebraSheaf S ⥤ AlgebraSheaf T :=
  (modulePullback φ).mapMon

/-- **The pullback of a sheaf of `𝒪_S`-algebras along a composite**,
`(ρ ≫ φ)^* A ≅ ρ^* φ^* A`, as sheaves of algebras.

The underlying isomorphism of sheaves of modules is the composition law of Tag 0097, and
`Stacks.PullbackTensorCoherence.isMonoidal_pullbackCompIso_hom` says it is a monoidal natural
isomorphism, so `CategoryTheory.Functor.mapMonNatIso` carries it to monoid objects. This is what
makes the Azumaya condition stable under refining the covering: a member of a common refinement
of two étale coverings reaches `S` through one of the two given coverings. -/
def algebraPullbackComp {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) :
    algebraPullback (ρ ≫ φ) ≅ algebraPullback φ ⋙ algebraPullback ρ :=
  letI := isMonoidal_modulePullbackComp ρ φ
  (Functor.mapMonNatIso (modulePullbackComp ρ φ)).symm ≪≫ Functor.mapMonCompIso

/-- **The pullback of a free sheaf of modules is free.** This is
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`, whose finality hypothesis on the functor of
sites holds for any morphism of schemes because `Opens.map` of a continuous map is
representably flat. -/
def modulePullbackFreeIso {T S : Scheme.{u}} (φ : T ⟶ S) (I : Type u) :
    (modulePullback φ).obj (SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) I) ≅
      SheafOfModules.free (R := Tensor.ringSheaf T.sheaf) I :=
  haveI : (RingedSpaceModuleAdjunction.opensMap φ.toLRSHom.toShHom).Final :=
    CategoryTheory.final_of_representablyFlat _
  SheafOfModules.pullbackObjFreeIso
    (RingedSpaceModuleAdjunction.structureSheafHom φ.toLRSHom.toShHom) I

/-- **The pullback of an endomorphism algebra is the endomorphism algebra of the pullback**, for
a finite locally free sheaf of modules: `φ^* 𝓗om(E,E) ≅ 𝓗om(φ^*E, φ^*E)` as sheaves of algebras.

This is `CategoryTheory.MonoidalClosed.internalEndFunctorIso` for the braided monoidal functor
`modulePullback φ`: a braided monoidal functor commutes with the internal endomorphism monoid of
a dualizable object, and a finite locally free sheaf of modules is dualizable. The conclusion is
stated with `Nonempty` because a right dual is data and finite local freeness only asserts its
existence. -/
theorem nonempty_endAlgebraPullbackIso {T S : Scheme.{u}} (φ : T ⟶ S) (E : ModuleSheaf S)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (C := Opens S) (J := Opens.grothendieckTopology S) E) :
    Nonempty ((algebraPullback φ).obj (endAlgebra E) ≅
      endAlgebra ((modulePullback φ).obj E)) :=
  MonoidalClosed.nonempty_internalEndFunctorIso (modulePullback φ) E
    (nonempty_hasRightDual_of_isFiniteLocallyFree hE)

/-- **The pullback of a matrix algebra is a matrix algebra**, `φ^* Mat_d(𝒪_S) ≅ Mat_d(𝒪_T)` as
sheaves of algebras. This is `nonempty_endAlgebraPullbackIso` for the free module of rank `d`,
followed by `modulePullbackFreeIso`. It is what makes the Azumaya condition of Tag 0A2J stable
under refining the étale covering. -/
theorem nonempty_matrixAlgebraPullbackIso {T S : Scheme.{u}} (φ : T ⟶ S) (d : ℕ) :
    Nonempty ((algebraPullback φ).obj (matrixAlgebra S d) ≅ matrixAlgebra T d) := by
  obtain ⟨e⟩ := nonempty_endAlgebraPullbackIso φ
    (SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)))
    (isFiniteLocallyFree_free _)
  exact ⟨e ≪≫ endAlgebraCongr (modulePullbackFreeIso φ (ULift.{u, 0} (Fin d)))⟩

/-- **Being a matrix algebra after pullback is inherited by any further pullback.** If `φ^* A` is
a matrix algebra and `ψ` factors through `φ`, then `ψ^* A` is a matrix algebra of the same rank:
`algebraPullbackComp` splits the pullback along the composite and
`nonempty_matrixAlgebraPullbackIso` recognises the pullback of the matrix algebra. -/
theorem nonempty_matrixAlgebra_iso_of_comp {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S)
    {A : AlgebraSheaf S} {d : ℕ}
    (h : Nonempty ((algebraPullback φ).obj A ≅ matrixAlgebra T d)) :
    Nonempty ((algebraPullback (ρ ≫ φ)).obj A ≅ matrixAlgebra V d) := by
  obtain ⟨i⟩ := h
  obtain ⟨m⟩ := nonempty_matrixAlgebraPullbackIso ρ d
  exact ⟨(algebraPullbackComp ρ φ).app A ≪≫ (algebraPullback ρ).mapIso i ≪≫ m⟩

/-! ### The tensor product of Azumaya algebra sheaves -/

/-- **The two halves of "étale covering"** packaged by an
`AlgebraicGeometry.Scheme.Cover` at `AlgebraicGeometry.Scheme.etalePrecoverage`: the family is
jointly surjective, and every member is étale. -/
theorem etaleCover_spec {S : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S) :
    (∀ x : S, ∃ i, x ∈ Set.range (𝒰.f i)) ∧ ∀ i, AlgebraicGeometry.Etale (𝒰.f i) :=
  (Scheme.ofArrows_mem_precoverage_iff (@AlgebraicGeometry.Etale)).mp 𝒰.mem₀

/-- **The common refinement of two étale coverings of `S`**: the family of fibre products
`U_i ×_S V_j`, mapping to `S` through `U_i`. Each member is étale, being a base change of an
étale morphism followed by an étale morphism, and the family is jointly surjective because a
point of `S` in the image of `U_i` and of `V_j` lifts to the fibre product.

This is the refinement the Azumaya condition of Tag 0A2J is closed under: a tensor product of
Azumaya algebra sheaves is trivialised on it. `CategoryTheory.Precoverage.ZeroHypercover.inter`
is the same construction in general, but it needs the étale precoverage to be registered as
stable under base change and composition, which it is not — `AlgebraicGeometry.Scheme.Cover` is
defined from a precoverage given as a plain definition that instance search does not unfold. -/
def coverInter {S : Scheme.{u}} (𝒰 𝒱 : Scheme.Cover.{u} Scheme.etalePrecoverage S) :
    Scheme.Cover.{u} Scheme.etalePrecoverage S :=
  haveI (i : 𝒰.I₀) : AlgebraicGeometry.Etale (𝒰.f i) := (etaleCover_spec 𝒰).2 i
  haveI (j : 𝒱.I₀) : AlgebraicGeometry.Etale (𝒱.f j) := (etaleCover_spec 𝒱).2 j
  Scheme.Cover.mkOfCovers (𝒰.I₀ × 𝒱.I₀)
    (fun k ↦ Limits.pullback (𝒰.f k.1) (𝒱.f k.2))
    (fun k ↦ Limits.pullback.fst (𝒰.f k.1) (𝒱.f k.2) ≫ 𝒰.f k.1)
    (fun x ↦ by
      obtain ⟨i, u, hu⟩ := (etaleCover_spec 𝒰).1 x
      obtain ⟨j, v, hv⟩ := (etaleCover_spec 𝒱).1 x
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback u v (hu.trans hv.symm)
      exact ⟨(i, j), w, by rw [Scheme.Hom.comp_apply, hw, hu]⟩)

/-- The structure morphism of the component `U_i ×_S V_j` of `coverInter 𝒰 𝒱` is the first
projection followed by `𝒰.f i`. -/
@[simp]
lemma coverInter_f {S : Scheme.{u}} (𝒰 𝒱 : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (k : 𝒰.I₀ × 𝒱.I₀) :
    (coverInter 𝒰 𝒱).f k = Limits.pullback.fst (𝒰.f k.1) (𝒱.f k.2) ≫ 𝒰.f k.1 :=
  rfl

/-- **The Azumaya condition of Tag 0A2J.** A sheaf of `𝒪_S`-algebras is Azumaya if it is étale
locally a matrix algebra: there is an étale covering `{φ_i : U_i → S}` of `S` and integers
`d_i ≥ 1` with `φ_i^* A ≅ Mat_{d_i}(𝒪_{U_i})` as `𝒪_{U_i}`-algebras. An
`AlgebraicGeometry.Scheme.Cover` at `AlgebraicGeometry.Scheme.etalePrecoverage` packages both
halves of "étale covering": every `𝒰.f i` is étale, and the family is jointly surjective.

The pullback `φ_i^*` of the sheaf of algebras is `algebraPullback`, which transports the
multiplication along the tensor comparison of Tag 01CD — the map
`φ^*(A ⊗ B) ⟶ φ^*A ⊗ φ^*B` of `Stacks.RingedSpace.comparison`, see `monoidalModulePullback`. -/
@[stacks 0A2J "the Azumaya condition"]
def IsAzumaya {S : Scheme.{u}} (A : AlgebraSheaf S) : Prop :=
  ∃ (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S) (d : 𝒰.I₀ → ℕ), (∀ i, 1 ≤ d i) ∧
    ∀ i, Nonempty ((algebraPullback (𝒰.f i)).obj A ≅ matrixAlgebra (𝒰.X i) (d i))

/-- The Azumaya `𝒪_S`-algebras. -/
def Azumaya (S : Scheme.{u}) : Type (u + 1) := {A : AlgebraSheaf S // IsAzumaya A}

/-- Similarity of Azumaya `𝒪_S`-algebras, as a setoid. -/
def azumayaSetoid (S : Scheme.{u}) : Setoid (Azumaya S) where
  r A B := IsSimilar A.1 B.1
  iseqv :=
    ⟨fun A => IsSimilar.refl A.1, fun h => IsSimilar.symm h, fun h₁ h₂ => IsSimilar.trans h₁ h₂⟩

/-- **The Brauer group of a scheme**, Tag 0A2J: the set of equivalence classes of Azumaya
`𝒪_S`-algebras for the equivalence of `IsSimilar`. The operation induced by the tensor product
is `BrauerGroup.mul`. -/
@[stacks 0A2J "the Brauer group"]
def BrauerGroup (S : Scheme.{u}) : Type (u + 1) := Quotient (azumayaSetoid S)

/-- The class of an Azumaya `𝒪_S`-algebra in the Brauer group. -/
def brauerClass {S : Scheme.{u}} (A : Azumaya S) : BrauerGroup S := Quotient.mk _ A

/-- `Mat_d(𝒪_S) ⊗ Mat_e(𝒪_S) ≅ Mat_{d·e}(𝒪_S)` as `𝒪_S`-algebras. -/
def matrixAlgebraTensorIso (S : Scheme.{u}) (d e : ℕ) :
    matrixAlgebra S d ⊗ matrixAlgebra S e ≅ matrixAlgebra S (d * e) :=
  endAlgebraTensorIso (isFiniteLocallyFree_free _) (isFiniteLocallyFree_free _) ≪≫
    endAlgebraCongr (Stacks.SheafOfModules.freeTensorFreeIso
        (Opens.grothendieckTopology S) (Osharp := S.sheaf) _ _ ≪≫
      (SheafOfModules.freeFunctor (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)).mapIso
        (((Equiv.ulift.prodCongr Equiv.ulift).trans finProdFinEquiv).trans
          Equiv.ulift.symm).toIso)

/-- **A tensor product of Azumaya `𝒪_S`-algebras is Azumaya.** On the common refinement
`coverInter` of the two trivialising coverings, the pullback of `A ⊗ B` is the tensor product of
the pullbacks — the pullback of sheaves of algebras is monoidal, `monoidalAlgebraPullback` — each
of which is a matrix algebra by `nonempty_matrixAlgebra_iso_of_comp`, and a tensor product of
matrix algebras is a matrix algebra by `matrixAlgebraTensorIso`.

With `IsSimilar.tensor` this is the well-definedness of the operation of Tag 0A2J's Brauer
group on the Azumaya algebra sheaves. -/
theorem IsAzumaya.tensor {S : Scheme.{u}} {A B : AlgebraSheaf S}
    (hA : IsAzumaya A) (hB : IsAzumaya B) : IsAzumaya (A ⊗ B) := by
  obtain ⟨𝒰, d, hd, hA'⟩ := hA
  obtain ⟨𝒱, e, he, hB'⟩ := hB
  refine ⟨coverInter 𝒰 𝒱, fun k ↦ d k.1 * e k.2,
    fun k ↦ by simpa using Nat.mul_le_mul (hd k.1) (he k.2), fun k ↦ ?_⟩
  obtain ⟨m₁⟩ := nonempty_matrixAlgebra_iso_of_comp
    (Limits.pullback.fst (𝒰.f k.1) (𝒱.f k.2)) (𝒰.f k.1) (hA' k.1)
  obtain ⟨m₂⟩ := nonempty_matrixAlgebra_iso_of_comp
    (Limits.pullback.snd (𝒰.f k.1) (𝒱.f k.2)) (𝒱.f k.2) (hB' k.2)
  have hcond : (coverInter 𝒰 𝒱).f k =
      Limits.pullback.snd (𝒰.f k.1) (𝒱.f k.2) ≫ 𝒱.f k.2 :=
    Limits.pullback.condition
  refine ⟨(Functor.Monoidal.μIso (algebraPullback ((coverInter 𝒰 𝒱).f k)) A B).symm ≪≫
    tensorIso m₁ (eqToIso (congrArg (fun φ ↦ (algebraPullback φ).obj B) hcond) ≪≫ m₂) ≪≫
    matrixAlgebraTensorIso _ (d k.1) (e k.2)⟩

/-- The tensor product of Azumaya `𝒪_S`-algebras, as Azumaya algebras. -/
def Azumaya.tensor {S : Scheme.{u}} (A B : Azumaya S) : Azumaya S :=
  ⟨A.1 ⊗ B.1, A.2.tensor B.2⟩

/-- **The operation of the Brauer group of Tag 0A2J**: the one induced by the tensor product of
sheaves of algebras. It is well defined because a tensor product of Azumaya algebra sheaves is
Azumaya (`IsAzumaya.tensor`) and because similarity is compatible with the tensor product
(`IsSimilar.tensor`). -/
@[stacks 0A2J "the operation of the Brauer group"]
def BrauerGroup.mul {S : Scheme.{u}} : BrauerGroup S → BrauerGroup S → BrauerGroup S :=
  Quotient.map₂ Azumaya.tensor fun _ _ h₁ _ _ h₂ ↦ IsSimilar.tensor h₁ h₂

/-- The multiplication of the Brauer group, `BrauerGroup.mul`. -/
instance {S : Scheme.{u}} : Mul (BrauerGroup S) := ⟨BrauerGroup.mul⟩

/-- The class of a tensor product of Azumaya algebra sheaves is the product of their classes. -/
@[simp]
theorem brauerClass_tensor {S : Scheme.{u}} (A B : Azumaya S) :
    brauerClass (Azumaya.tensor A B) = brauerClass A * brauerClass B :=
  rfl

end Stacks.EtaleCohomology.BrauerScheme
