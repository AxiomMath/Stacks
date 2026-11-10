module

public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of the canonical polynomial presentation and of the degree-zero term of
the naive cotangent complex

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a : A ⟶ B` a homomorphism of sheaves of
commutative rings on `D`. The inverse image of the canonical polynomial presentation
`A[B] ⟶ B` of Stacks 08TU is the canonical polynomial presentation `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹B` of
the inverse-image homomorphism. Consequently the inverse image of the degree-`0` term
`B ⊗_{A[B]} Ω_{A[B]/A}` of the naive cotangent complex of `a` and the degree-`0` term of the
naive cotangent complex of `f⁻¹a` represent the same functor of relative derivations.

## Main definitions

* `Stacks.Sites.FreeAlgebra.variableSheaf` reads the variables `[b]` of `A[B]` as a morphism
  of the underlying sheaves of sets.
* `Stacks.Sites.FreeAlgebra.toPushforwardFreeAlgebra` is the morphism
  `A[B] ⟶ f_*((f⁻¹A)[f⁻¹B])` classifying the unit on coefficients and the inverse image of the
  variables.
* `Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraIso` is the identification
  `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`.
* `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv` is the universal property of the
  degree-`0` term of the naive cotangent complex: morphisms out of it are the `A`-derivations
  of `A[B]` with values in the module with scalars restricted along `A[B] ⟶ B`.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivationEquiv` is the corresponding
  universal property of the inverse image of that term, for the inverse-image homomorphism.

## Main results

* `Stacks.Sites.FreeAlgebra.map_coefficientMap_comp_inverseImageFreeAlgebraHom` and
  `Stacks.Sites.FreeAlgebra.inverseImage_variableSheaf_comp_inverseImageFreeAlgebraHom`: the
  identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` is a morphism of `f⁻¹A`-algebras carrying the
  inverse image of the variable `[b]` to the variable `[b]`, and these two properties
  determine it.
* `Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraHom_comp_canonicalPresentation`: it carries
  the canonical presentation of `f⁻¹B` over `f⁻¹A` to the inverse image of the canonical
  presentation of `B` over `A`.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroHomEquiv`: the inverse image of the
  degree-`0` term of the naive cotangent complex of `a` and the degree-`0` term of the naive
  cotangent complex of `f⁻¹a` have the same morphisms into every sheaf of `f⁻¹B`-modules.

## Implementation notes

A morphism out of `f⁻¹(A[B])` is read through the adjunction `f⁻¹ ⊣ f_*` of sheaves of
commutative rings as a morphism out of `A[B]`, where the universal property of the free algebra
sheaf applies; the variables are transported by the geometric adjunction on sheaves of sets,
which is the same bijection on underlying sheaves of sets by
`CategoryTheory.MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget`. No description of the
sections of an inverse image is used, and for the identification of the free algebras the two
sites, their morphism universes and the two universes of sections all vary independently.

Several steps are term-mode `Eq.trans`/`congrArg` chains rather than `rw`: the underlying sheaf
of sets of `f⁻¹O` *is* the inverse image of the underlying sheaf of sets of `O`, but the two
spellings are definitionally and not syntactically equal, and a composition mixing them is not
type-correct at the transparency `rw` uses.

The universal property of the degree-`0` term is obtained from
`Stacks.Sites.Conormal.tensorDifferentialsIso`, which identifies it with the extension of
scalars of `Ω_{A[B]/A}` along `A[B] ⟶ B`, composed with the extension/restriction of scalars
adjunction and the corepresentability of relative derivations of Stacks 04BL. The same property
for its inverse image is the composition of six bijections: the hom-set bijection of
Stacks 03D3, that universal property on the target site, the identification of the direct image
of a restriction of scalars with the restriction of scalars of the direct image, the
transposition of derivations of Stacks 08TQ, the transport along the equality of the two
restriction morphisms, and the transport along the identification of the free algebras. Each of
the six is a separate declaration, stated at the spelling of the library lemma it instantiates:
composing them in one term exhausts the heartbeat budget on the intermediate defeq checks.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical
  polynomial presentation.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex.
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ), the inverse image of
  the sheaf of relative differentials.
-/
@[expose] public section

open CategoryTheory

namespace Stacks.Sites.FreeAlgebra

universe w w' v u v' u'

section OneSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] (A B : Sheaf J CommRingCat.{w})

/-- The variables `[b]` of `A[B]`, read as a morphism of the underlying sheaves of sets. -/
noncomputable def variableSheaf :
    (sheafCompose J (forget CommRingCat.{w})).obj B ⟶
      (sheafCompose J (forget CommRingCat.{w})).obj
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) :=
  ObjectProperty.homMk (freeAlgebraSheafVariable J A (underlyingPresheaf J B))

/-- The canonical presentation carries the variable `[b]` to `b`. -/
theorem variableSheaf_comp_canonicalPresentation (a : A ⟶ B) :
    variableSheaf J A B ≫
        (sheafCompose J (forget CommRingCat.{w})).map (canonicalPresentation J A B a) =
      𝟙 ((sheafCompose J (forget CommRingCat.{w})).obj B) :=
  Sheaf.hom_ext (freeAlgebraSheafVariable_comp_desc J A B (underlyingPresheaf J B) a (𝟙 _))

end OneSite

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify K CommRingCat.{w'}]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) (A B : Sheaf K CommRingCat.{w'})

/-- The morphism `A[B] ⟶ f_*((f⁻¹A)[f⁻¹B])` classifying the unit on coefficients and the
inverse image of the variables. -/
noncomputable def toPushforwardFreeAlgebra :
    freeAlgebraSheaf K A (underlyingPresheaf K B) ⟶
      f.pushforwardRing.obj (freeAlgebraSheaf J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B))) :=
  freeAlgebraSheafDesc K A (f.pushforwardRing.obj (freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B))))
    (underlyingPresheaf K B)
    (f.ringAdjunction.unit.app A ≫ f.pushforwardRing.map
      (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B))))
    (f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj B)
      ((sheafCompose J (forget CommRingCat.{w})).obj
        (freeAlgebraSheaf J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))))
      (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B))).hom

/-- On coefficients, the classifying morphism is the unit followed by the structural morphism
of `(f⁻¹A)[f⁻¹B]`. -/
theorem coefficientMap_comp_toPushforwardFreeAlgebra :
    freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B) ≫
        toPushforwardFreeAlgebra f A B =
      f.ringAdjunction.unit.app A ≫ f.pushforwardRing.map
        (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))) :=
  freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- On variables, the classifying morphism is the adjunct of the variables of
`(f⁻¹A)[f⁻¹B]`. -/
theorem freeAlgebraSheafVariable_comp_toPushforwardFreeAlgebra :
    freeAlgebraSheafVariable K A (underlyingPresheaf K B) ≫
        Functor.whiskerRight ((sheafToPresheaf K CommRingCat.{w'}).map
          (toPushforwardFreeAlgebra f A B)) (forget CommRingCat.{w'}) =
      (f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj B)
        ((sheafCompose J (forget CommRingCat.{w})).obj
          (freeAlgebraSheaf J (f.inverseImageRing.obj A)
            (underlyingPresheaf J (f.inverseImageRing.obj B))))
        (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B))).hom :=
  freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

/-- The comparison `f⁻¹(A[B]) ⟶ (f⁻¹A)[f⁻¹B]`. -/
noncomputable def inverseImageFreeAlgebraHom :
    f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)) ⟶
      freeAlgebraSheaf J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B)) :=
  (f.ringAdjunction.homEquiv _ _).symm (toPushforwardFreeAlgebra f A B)

/-- The comparison `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹(A[B])`. -/
noncomputable def inverseImageFreeAlgebraInv :
    freeAlgebraSheaf J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B)) ⟶
      f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)) :=
  freeAlgebraSheafDesc J (f.inverseImageRing.obj A)
    (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
    (underlyingPresheaf J (f.inverseImageRing.obj B))
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
    (f.inverseImage.map (variableSheaf K A B)).hom

/-- The comparison `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹(A[B])` is a morphism of `f⁻¹A`-algebras. -/
theorem coefficientMap_comp_inverseImageFreeAlgebraInv :
    freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B)) ≫
      inverseImageFreeAlgebraInv f A B =
        f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) :=
  freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- The comparison `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹(A[B])` carries the variable `[b]` to the inverse image
of the variable `[b]`. -/
theorem freeAlgebraSheafVariable_comp_inverseImageFreeAlgebraInv :
    freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B)) ≫
        Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map
          (inverseImageFreeAlgebraInv f A B)) (forget CommRingCat.{w}) =
      (f.inverseImage.map (variableSheaf K A B)).hom :=
  freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

/-- The same identity, read on sheaves of sets. -/
theorem variableSheaf_comp_inverseImageFreeAlgebraInv :
    variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
        (sheafCompose J (forget CommRingCat.{w})).map (inverseImageFreeAlgebraInv f A B) =
      f.inverseImage.map (variableSheaf K A B) :=
  Sheaf.hom_ext (freeAlgebraSheafVariable_comp_inverseImageFreeAlgebraInv f A B)

/-- The comparison `f⁻¹(A[B]) ⟶ (f⁻¹A)[f⁻¹B]` is, on underlying sheaves of sets, the adjunct
of the morphism `A[B] ⟶ f_*((f⁻¹A)[f⁻¹B])` that classifies it. -/
theorem homEquiv_inverseImageFreeAlgebraHom_forget :
    f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj
          (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((sheafCompose J (forget CommRingCat.{w})).obj
          (freeAlgebraSheaf J (f.inverseImageRing.obj A)
            (underlyingPresheaf J (f.inverseImageRing.obj B))))
        ((sheafCompose J (forget CommRingCat.{w})).map (inverseImageFreeAlgebraHom f A B)) =
      (sheafCompose K (forget CommRingCat.{w'})).map (toPushforwardFreeAlgebra f A B) :=
  (congrArg (f.adj.homEquiv _ _) (f.ringAdjunction_homEquiv_symm_forget _ _
    (toPushforwardFreeAlgebra f A B))).trans (Equiv.apply_symm_apply _ _)

/-- The comparison `f⁻¹(A[B]) ⟶ (f⁻¹A)[f⁻¹B]` is a morphism of `f⁻¹A`-algebras. -/
theorem map_coefficientMap_comp_inverseImageFreeAlgebraHom :
    f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) ≫
        inverseImageFreeAlgebraHom f A B =
      freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B)) := by
  refine (f.ringAdjunction.homEquiv A (freeAlgebraSheaf J (f.inverseImageRing.obj A)
    (underlyingPresheaf J (f.inverseImageRing.obj B)))).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]
  change _ ≫ (f.ringAdjunction.homEquiv _ _)
      ((f.ringAdjunction.homEquiv _ _).symm (toPushforwardFreeAlgebra f A B)) = _
  rw [Equiv.apply_symm_apply]
  exact freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- The comparison `f⁻¹(A[B]) ⟶ (f⁻¹A)[f⁻¹B]` carries the inverse image of the variable `[b]`
to the variable `[b]`, on sheaves of sets. -/
theorem inverseImage_variableSheaf_comp_inverseImageFreeAlgebraHom :
    f.inverseImage.map (variableSheaf K A B) ≫
        (sheafCompose J (forget CommRingCat.{w})).map (inverseImageFreeAlgebraHom f A B) =
      variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) := by
  refine (f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj B)
    ((sheafCompose J (forget CommRingCat.{w})).obj
      (freeAlgebraSheaf J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B))))).injective ?_
  refine (Adjunction.homEquiv_naturality_left f.adj (variableSheaf K A B)
    ((sheafCompose J (forget CommRingCat.{w})).map
      (inverseImageFreeAlgebraHom f A B))).trans ?_
  rw [homEquiv_inverseImageFreeAlgebraHom_forget]
  exact Sheaf.hom_ext (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _)

/-- The variables of `(f⁻¹A)[f⁻¹B]` are fixed by the composition of the two comparisons. -/
theorem variableSheaf_comp_inv_comp_hom :
    variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
        (sheafCompose J (forget CommRingCat.{w})).map
          (inverseImageFreeAlgebraInv f A B ≫ inverseImageFreeAlgebraHom f A B) =
      variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
        (sheafCompose J (forget CommRingCat.{w})).map
          (𝟙 (freeAlgebraSheaf J (f.inverseImageRing.obj A)
            (underlyingPresheaf J (f.inverseImageRing.obj B)))) := by
  refine Eq.trans (congrArg
    (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫ ·)
    ((sheafCompose J (forget CommRingCat.{w})).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ (sheafCompose J (forget CommRingCat.{w})).map
      (inverseImageFreeAlgebraHom f A B))
    (variableSheaf_comp_inverseImageFreeAlgebraInv f A B)) ?_
  refine (inverseImage_variableSheaf_comp_inverseImageFreeAlgebraHom f A B).trans ?_
  refine Eq.trans (Category.comp_id _).symm ?_
  exact congrArg (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫ ·)
    ((sheafCompose J (forget CommRingCat.{w})).map_id _).symm

/-- The two comparisons compose to the identity of `(f⁻¹A)[f⁻¹B]`. -/
theorem inverseImageFreeAlgebraInv_comp_hom :
    inverseImageFreeAlgebraInv f A B ≫ inverseImageFreeAlgebraHom f A B =
      𝟙 (freeAlgebraSheaf J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B))) := by
  refine freeAlgebraSheaf_hom_ext J _ _ _ ?_ ?_
  · rw [← Category.assoc, coefficientMap_comp_inverseImageFreeAlgebraInv,
      map_coefficientMap_comp_inverseImageFreeAlgebraHom, Category.comp_id]
  · exact congrArg Sheaf.homEquiv (variableSheaf_comp_inv_comp_hom f A B)

/-- If a morphism `g` out of `(f⁻¹A)[f⁻¹B]` carries the variables to the inverse image of the
variables followed by `h`, then the adjunct of the variables followed by the direct image of `g`
is the variables followed by `h` and the unit. -/
private theorem homEquiv_variableSheaf_comp_pushforward_of_comp
    {Y : Sheaf K CommRingCat.{w'}} (h : freeAlgebraSheaf K A (underlyingPresheaf K B) ⟶ Y)
    (g : freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)) ⟶ f.inverseImageRing.obj Y)
    (hv : variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
        (sheafCompose J (forget CommRingCat.{w})).map g =
      f.inverseImage.map (variableSheaf K A B ≫ (sheafCompose K (forget CommRingCat.{w'})).map h)) :
    f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj B)
          ((sheafCompose J (forget CommRingCat.{w})).obj
            (freeAlgebraSheaf J (f.inverseImageRing.obj A)
              (underlyingPresheaf J (f.inverseImageRing.obj B))))
          (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)) ≫
        (sheafCompose K (forget CommRingCat.{w'})).map (f.pushforwardRing.map g) =
      variableSheaf K A B ≫ (sheafCompose K (forget CommRingCat.{w'})).map
        (h ≫ f.ringAdjunction.unit.app Y) := by
  refine Eq.trans (congrArg (f.adj.homEquiv _ _
    (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)) ≫ ·)
    (f.pushforwardRing_map_forget g)) ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_right f.adj _ _).symm ?_
  refine Eq.trans (congrArg (f.adj.homEquiv _ _) hv) ?_
  refine ((Adjunction.homEquiv_unit f.adj _ _ _).trans (f.adj.unit.naturality _).symm).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (variableSheaf K A B ≫ ·)
    ((congrArg (_ ≫ ·) (f.ringAdjunction_unit_forget Y).symm).trans
      ((sheafCompose K (forget CommRingCat.{w'})).map_comp _ _).symm))

/-- A morphism `g` out of `(f⁻¹A)[f⁻¹B]` which is compatible with the coefficients and the
variables is the comparison `f⁻¹(A[B]) ⟶ (f⁻¹A)[f⁻¹B]` followed by `g`, when `g` is the
inverse image of `h`. -/
private theorem inverseImageFreeAlgebraHom_comp_eq_map {Y : Sheaf K CommRingCat.{w'}}
    (h : freeAlgebraSheaf K A (underlyingPresheaf K B) ⟶ Y)
    (g : freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)) ⟶ f.inverseImageRing.obj Y)
    (hc : freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B)) ≫ g =
      f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B) ≫ h))
    (hv : variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
        (sheafCompose J (forget CommRingCat.{w})).map g =
      f.inverseImage.map (variableSheaf K A B ≫ (sheafCompose K (forget CommRingCat.{w'})).map h)) :
    inverseImageFreeAlgebraHom f A B ≫ g = f.inverseImageRing.map h := by
  have hrhs : f.ringAdjunction.homEquiv _ _ (f.inverseImageRing.map h) =
      h ≫ f.ringAdjunction.unit.app Y :=
    (Adjunction.homEquiv_unit f.ringAdjunction _ _ _).trans
      (f.ringAdjunction.unit.naturality h).symm
  refine (f.ringAdjunction.homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, hrhs]
  change (f.ringAdjunction.homEquiv _ _)
      ((f.ringAdjunction.homEquiv _ _).symm (toPushforwardFreeAlgebra f A B)) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  refine freeAlgebraSheaf_hom_ext K _ _ _ ?_ ?_
  · rw [← Category.assoc, coefficientMap_comp_toPushforwardFreeAlgebra, Category.assoc,
      ← f.pushforwardRing.map_comp, hc]
    exact (f.ringAdjunction.unit.naturality _).symm.trans (Category.assoc _ _ _)
  · have hcomp : Functor.whiskerRight ((sheafToPresheaf K CommRingCat.{w'}).map
          (toPushforwardFreeAlgebra f A B ≫ f.pushforwardRing.map g)) (forget CommRingCat.{w'}) =
        Functor.whiskerRight ((sheafToPresheaf K CommRingCat.{w'}).map
            (toPushforwardFreeAlgebra f A B)) (forget CommRingCat.{w'}) ≫
          Functor.whiskerRight ((sheafToPresheaf K CommRingCat.{w'}).map
            (f.pushforwardRing.map g)) (forget CommRingCat.{w'}) := rfl
    rw [hcomp, ← Category.assoc, freeAlgebraSheafVariable_comp_toPushforwardFreeAlgebra]
    exact congrArg Sheaf.homEquiv (homEquiv_variableSheaf_comp_pushforward_of_comp f A B h g hv)

/-- The variables of `A[B]`, followed by the direct image of the comparison, are the unit of
the inverse-image adjunction on the variables. -/
theorem homEquiv_variableSheaf_comp_pushforward :
    f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj B)
          ((sheafCompose J (forget CommRingCat.{w})).obj
            (freeAlgebraSheaf J (f.inverseImageRing.obj A)
              (underlyingPresheaf J (f.inverseImageRing.obj B))))
          (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)) ≫
        (sheafCompose K (forget CommRingCat.{w'})).map
          (f.pushforwardRing.map (inverseImageFreeAlgebraInv f A B)) =
      variableSheaf K A B ≫ (sheafCompose K (forget CommRingCat.{w'})).map
        (f.ringAdjunction.unit.app (freeAlgebraSheaf K A (underlyingPresheaf K B))) := by
  refine (homEquiv_variableSheaf_comp_pushforward_of_comp f A B (𝟙 _) _ ?_).trans ?_
  · rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact variableSheaf_comp_inverseImageFreeAlgebraInv f A B
  · rw [Category.id_comp]

/-- The two comparisons compose to the identity of `f⁻¹(A[B])`. -/
theorem inverseImageFreeAlgebraHom_comp_inv :
    inverseImageFreeAlgebraHom f A B ≫ inverseImageFreeAlgebraInv f A B =
      𝟙 (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B))) := by
  refine (inverseImageFreeAlgebraHom_comp_eq_map f A B (𝟙 _) _ ?_ ?_).trans
    (f.inverseImageRing.map_id _)
  · rw [Category.comp_id]
    exact coefficientMap_comp_inverseImageFreeAlgebraInv f A B
  · rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact variableSheaf_comp_inverseImageFreeAlgebraInv f A B

/-- The inverse image of the free `A`-algebra on `B` is the free `f⁻¹A`-algebra on `f⁻¹B`:
`f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`. -/
noncomputable def inverseImageFreeAlgebraIso :
    f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)) ≅
      freeAlgebraSheaf J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B)) where
  hom := inverseImageFreeAlgebraHom f A B
  inv := inverseImageFreeAlgebraInv f A B
  hom_inv_id := inverseImageFreeAlgebraHom_comp_inv f A B
  inv_hom_id := inverseImageFreeAlgebraInv_comp_hom f A B

/-- On variables, the direct image of the canonical presentation of `f⁻¹a` composes with the
adjunct of the variables to the unit of the adjunction. -/
theorem homEquiv_variableSheaf_comp_canonicalPresentation (a : A ⟶ B) :
    f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{w'})).obj B)
          ((sheafCompose J (forget CommRingCat.{w})).obj
            (freeAlgebraSheaf J (f.inverseImageRing.obj A)
              (underlyingPresheaf J (f.inverseImageRing.obj B))))
          (variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)) ≫
        (sheafCompose K (forget CommRingCat.{w'})).map (f.pushforwardRing.map
          (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
            (f.inverseImageRing.map a))) =
      variableSheaf K A B ≫ (sheafCompose K (forget CommRingCat.{w'})).map
        (canonicalPresentation K A B a ≫ f.ringAdjunction.unit.app B) := by
  refine homEquiv_variableSheaf_comp_pushforward_of_comp f A B _ _ ?_
  refine (variableSheaf_comp_canonicalPresentation J _ _ _).trans ?_
  rw [variableSheaf_comp_canonicalPresentation]
  exact (f.inverseImage.map_id _).symm

/-- **Stacks Project, Tag 08TZ.** The inverse image of the canonical polynomial presentation
`A[B] ⟶ B` is the canonical polynomial presentation `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹B` of the inverse-image
homomorphism of sheaves of commutative rings. -/
@[stacks 08TZ "the inverse image of the canonical polynomial presentation is the canonical \
polynomial presentation of the inverse image, from which both terms of the complex are built"]
theorem inverseImageFreeAlgebraHom_comp_canonicalPresentation (a : A ⟶ B) :
    inverseImageFreeAlgebraHom f A B ≫
        canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map a) =
      f.inverseImageRing.map (canonicalPresentation K A B a) := by
  refine inverseImageFreeAlgebraHom_comp_eq_map f A B (canonicalPresentation K A B a) _ ?_ ?_
  · rw [canonicalPresentation_comp_coefficientMap, canonicalPresentation_comp_coefficientMap]
  · refine (variableSheaf_comp_canonicalPresentation J _ _ _).trans ?_
    rw [variableSheaf_comp_canonicalPresentation]
    exact (f.inverseImage.map_id _).symm

end InverseImage

end Stacks.Sites.FreeAlgebra

namespace Stacks.SheafOfModules

section NaiveCotangentZero

universe uu vv ww

open CategoryTheory AlgebraicGeometry.SheafOfModules Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal (tensorDifferentialsIso)

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max uu vv ww}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uu vv ww} RingCat.{max uu vv ww})]
  (A B : Sheaf J CommRingCat.{max uu vv ww}) (a : A ⟶ B)

/-- Precomposition with the identification of the degree-`0` term of the naive cotangent
complex with the extension of scalars of `Ω_{A[B]/A}`. -/
noncomputable def zeroDerivationStep₁
    (N : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    ((canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww}
        J A B a).X₂ ⟶ N) ≃
      ((_root_.SheafOfModules.pullback
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj
        (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))) ⟶ N) :=
  { toFun := fun x ↦ (tensorDifferentialsIso.{vv, uu, max uu vv ww, max uu vv ww} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a)).inv ≫ x
    invFun := fun y ↦ (tensorDifferentialsIso.{vv, uu, max uu vv ww, max uu vv ww} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a)).hom ≫ y
    left_inv := fun x ↦ by
      dsimp only
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    right_inv := fun y ↦ by
      dsimp only
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp] }

/-- The extension/restriction of scalars adjunction along the canonical presentation. -/
noncomputable def zeroDerivationStep₂
    (N : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    ((_root_.SheafOfModules.pullback
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj
        (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))) ⟶ N) ≃
      (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) ⟶
        (_root_.SheafOfModules.pushforward
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj N) :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction
    (Stacks.Sites.Conormal.underlyingRingHomForPullback J
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (canonicalPresentation J A B a))).homEquiv _ N

/-- The corepresentability of relative derivations of Stacks 04BL. -/
noncomputable def zeroDerivationStep₃
    (N : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) ⟶
        (_root_.SheafOfModules.pushforward
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj N) ≃
      PresheafOfModulesOfCommRing.Derivation' ((((_root_.SheafOfModules.pushforward
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj N)).val)
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom :=
  (derivationsFunctor.{max uu vv ww} A (freeAlgebraSheaf J A (underlyingPresheaf J B))
    (freeAlgebraSheafCoefficientMap J A
      (underlyingPresheaf J B))).corepresentableBy.homEquiv

/-- **The universal property of the degree-`0` term of the naive cotangent complex.** A
morphism from `B ⊗_{A[B]} Ω_{A[B]/A}` to a sheaf of `B`-modules is an `A`-derivation of `A[B]`
with values in that module, its scalars restricted along the canonical presentation. -/
noncomputable def naiveCotangentZeroDerivationEquiv
    (N : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    ((canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww}
        J A B a).X₂ ⟶ N) ≃
      PresheafOfModulesOfCommRing.Derivation' ((((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{vv, uu, max uu vv ww} J).map
            (canonicalPresentation J A B a))).obj N)).val)
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom :=
  (zeroDerivationStep₁ J A B a N).trans
    ((zeroDerivationStep₂ J A B a N).trans (zeroDerivationStep₃ J A B a N))

end NaiveCotangentZero

section InverseImageNaiveCotangentZero

universe u v w u' v' w'

open CategoryTheory AlgebraicGeometry.SheafOfModules Stacks.Sites.FreeAlgebra
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{max u v w}] [HasWeakSheafify K CommRingCat.{max u' v' w'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- The hom-set bijection of the inverse image and direct image of sheaves of modules. -/
noncomputable def inverseImageZeroStep₁
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    ((inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'}
          K A B a).X₂ ⟶ M) ≃
      ((canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'}
          K A B a).X₂ ⟶
        (directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj M) :=
  toposModulesHomEquiv f (Tensor.ringSheaf.{u', v', max u' v' w'} B) _ M

/-- The universal property of the degree-`0` term on the target site. -/
noncomputable def inverseImageZeroStep₂
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    ((canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'}
          K A B a).X₂ ⟶
        (directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj M) ≃
      PresheafOfModulesOfCommRing.Derivation' ((((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
            (canonicalPresentation K A B a))).obj
            ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
              M))).val)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom :=
  naiveCotangentZeroDerivationEquiv.{u', v', w'} K A B a _

/-- The direct image of a restriction of scalars is the restriction of scalars of the
direct image. -/
noncomputable def inverseImageZeroStep₃
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    PresheafOfModulesOfCommRing.Derivation' ((((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
            (canonicalPresentation K A B a))).obj
            ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
              M))).val)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom ≃
      PresheafOfModulesOfCommRing.Derivation' (((directImageModules f
        (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).obj
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom :=
  PresheafOfModules.Derivation.postcompEquiv
    ((_root_.SheafOfModules.forget _).mapIso (directImageModulesRestrictScalarsIso f
      (underlyingRingHomOfSite (canonicalPresentation K A B a)) M))

/-- The transposition of derivations along the inverse image of Stacks 08TQ. -/
noncomputable def inverseImageZeroStep₄
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    PresheafOfModulesOfCommRing.Derivation' (((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).obj
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom ≃
      PresheafOfModulesOfCommRing.Derivation' (((show _root_.SheafOfModules.{max u v w}
        (Tensor.ringSheaf.{u, v, max u v w}
            (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))) from
          (_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val)
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom :=
  (inverseImageDerivationEquiv f (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
    (show _root_.SheafOfModules.{max u v w} (Tensor.ringSheaf.{u, v, max u v w}
        (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))) from
      (_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
        (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).symm

/-- The transport along the equality of the two restriction morphisms. -/
noncomputable def inverseImageZeroStep₅
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    PresheafOfModulesOfCommRing.Derivation' (((show _root_.SheafOfModules.{max u v w}
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
            (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))) from
          (_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val)
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom ≃
      PresheafOfModulesOfCommRing.Derivation' (((_root_.SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
          (f.inverseImageRing.map (canonicalPresentation K A B a)))).obj M).val)
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom :=
  restrictScalarsDerivationCongr M
    (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage
      (canonicalPresentation K A B a)).symm
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))

/-- The transport along the identification of the two free algebras. -/
noncomputable def inverseImageZeroStep₆
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    PresheafOfModulesOfCommRing.Derivation' (((_root_.SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
          (f.inverseImageRing.map (canonicalPresentation K A B a)))).obj M).val)
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom ≃
      PresheafOfModulesOfCommRing.Derivation' (((_root_.SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
          (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
            (f.inverseImageRing.map a)))).obj M).val)
        (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))).hom :=
  derivationRingEquiv M (inverseImageFreeAlgebraIso f A B)
    (map_coefficientMap_comp_inverseImageFreeAlgebraHom f A B)
    (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B a)

/-- **The universal property of the inverse image of the degree-`0` term of the naive cotangent
complex.** A morphism from `f⁻¹(B ⊗_{A[B]} Ω_{A[B]/A})` to a sheaf of `f⁻¹B`-modules is an
`f⁻¹A`-derivation of `(f⁻¹A)[f⁻¹B]` with values in that module, its scalars restricted along the
canonical presentation of `f⁻¹B`. -/
noncomputable def inverseImageNaiveCotangentZeroDerivationEquiv
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    ((inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation' ((((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
              (f.inverseImageRing.map a)))).obj M)).val)
        (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))).hom :=
  (inverseImageZeroStep₁ J K f a M).trans ((inverseImageZeroStep₂ J K f a M).trans
    ((inverseImageZeroStep₃ J K f a M).trans ((inverseImageZeroStep₄ J K f a M).trans
      ((inverseImageZeroStep₅ J K f a M).trans (inverseImageZeroStep₆ J K f a M)))))

/-- **Stacks Project, Tag 08TZ.** The inverse image of the degree-`0` term of the naive
cotangent complex of `a` and the degree-`0` term of the naive cotangent complex of `f⁻¹a` have
the same morphisms into every sheaf of `f⁻¹B`-modules: both represent the `f⁻¹A`-derivations of
the canonical polynomial presentation of `f⁻¹B` over `f⁻¹A`. -/
@[stacks 08TZ "the degree 0 term: its inverse image and the degree 0 term of the inverse image \
represent the same functor of derivations. Naturality of this bijection is \
`inverseImageNaiveCotangentZeroHomEquiv_naturality` and the resulting isomorphism of degree 0 \
terms is `inverseImageNaiveCotangentZeroIso`; the isomorphism of complexes assembled from it \
is `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`"]
noncomputable def inverseImageNaiveCotangentZeroHomEquiv
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :
    ((inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) ≃
      ((canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂ ⟶ M) :=
  (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M).trans
    (naiveCotangentZeroDerivationEquiv.{u, v, w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a) M).symm

end InverseImageNaiveCotangentZero

end Stacks.SheafOfModules

end
