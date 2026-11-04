module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafLocalIso

/-!
# The inverse image of a free algebra sheaf

Let `f : Y ⟶ X` be a continuous map of topological spaces, `A` a sheaf of commutative rings on
`X` and `E` a presheaf of sets on `X`. The inverse image of the free `A`-algebra on `E` is the
free `f⁻¹A`-algebra on the inverse image of `E`, by an isomorphism compatible with the
structural morphisms from `f⁻¹A` and with the variables. For `E` the underlying presheaf of sets
of a sheaf of commutative rings `B`, the inverse image of the presheaf of sets is identified with
the underlying presheaf of sets of the sheaf inverse image `f⁻¹B` after sheafification, so that
`f⁻¹(A[B])` is the free `f⁻¹A`-algebra on `f⁻¹B`, compatibly with the canonical presentations.

## Main definitions

* `Stacks.Sites.FreeAlgebra.inverseImageVariable`: the variables `f⁻¹E ⟶ f⁻¹(A[E])`.
* `Stacks.Sites.FreeAlgebra.toPushforwardFreeAlgebraSheaf`: the morphism
  `A[E] ⟶ f_*((f⁻¹A)[f⁻¹E])` classifying the unit on coefficients and the variables.
* `Stacks.Sites.FreeAlgebra.inverseImageHom`: the comparison `f⁻¹(A[E]) ⟶ (f⁻¹A)[f⁻¹E]`.
* `Stacks.Sites.FreeAlgebra.inverseImageInv`: the comparison `(f⁻¹A)[f⁻¹E] ⟶ f⁻¹(A[E])`.
* `Stacks.Sites.FreeAlgebra.inverseImageIso`: the isomorphism `f⁻¹(A[E]) ≅ (f⁻¹A)[f⁻¹E]`.
* `Stacks.Sites.FreeAlgebra.toSheafInverseImage`: the comparison of presheaves of commutative
  rings from the presheaf inverse image of `B` to the sheaf inverse image `f⁻¹B`.
* `Stacks.Sites.FreeAlgebra.toUnderlyingInverseImage`: the same comparison on underlying
  presheaves of sets.
* `Stacks.Sites.FreeAlgebra.underlyingPullbackIso`: the inverse image of presheaves commutes
  with the forgetful functor to presheaves of sets.
* `Stacks.Sites.FreeAlgebra.underlyingInverseImageIso`: the isomorphism
  `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`.

## Main results

* `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_inverseImage_hom_ext`: two morphisms out of
  `f⁻¹(A[E])` agreeing on the coefficients and on the variables are equal.
* `Stacks.Sites.FreeAlgebra.map_freeAlgebraSheafCoefficientMap_comp_inverseImageHom` and
  `Stacks.Sites.FreeAlgebra.inverseImageVariable_comp_inverseImageHom`: the comparison is a
  morphism of `f⁻¹A`-algebras carrying the inverse image of the variable `[x]` to `[x]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_inverseImageInv` and
  `Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_inverseImageInv`: the same for the
  comparison in the other direction.
* `Stacks.Sites.FreeAlgebra.w_toSheafInverseImage`: the sheaf inverse image is the
  sheafification of the presheaf inverse image.
* `Stacks.Sites.FreeAlgebra.isLocallyInjective_toUnderlyingInverseImage` and
  `Stacks.Sites.FreeAlgebra.isLocallySurjective_toUnderlyingInverseImage`: the comparison of
  presheaves of sets is a local isomorphism.
* `Stacks.Sites.FreeAlgebra.map_freeAlgebraSheafCoefficientMap_comp_underlyingInverseImageIso`
  and `Stacks.Sites.FreeAlgebra.underlyingInverseImageIso_comp_canonicalPresentation`: the
  isomorphism `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` is compatible with the structural morphisms from
  `f⁻¹A` and with the canonical presentations.

## Implementation notes

The inverse image of the presheaf of sets `E` is `TopCat.Presheaf.pullback`, the left Kan
extension along `(Opens.map f).op`, and not its sheafification: the free algebra is built on an
arbitrary presheaf of sets, and the left Kan extension is already left adjoint to the
pushforward of presheaves of sets, which is all the universal property needs. Sheafifying `E`
would give the same free algebra sheaf but no shorter proof.

The identification is read off the universal property on both sides rather than from sections:
a morphism `f⁻¹(A[E]) ⟶ C` transposes to a morphism `A[E] ⟶ f_*C`, which by the universal
property of `A[E]` is a morphism `A ⟶ f_*C` of sheaves of rings together with a morphism
`E ⟶ f_*C` of presheaves of sets, and the latter transposes back to a morphism
`f⁻¹E ⟶ C` of presheaves of sets because the pushforward of presheaves of sets commutes with
the forgetful functor on the nose. The two comparison morphisms are then built directly by
`freeAlgebraSheafDesc` and shown to be mutually inverse.

A sheaf of commutative rings on a space carries two definitionally equal spellings of its
category structure, the one derived for `TopCat.Sheaf` and the one of
`CategoryTheory.Sheaf` for the topology of opens, and the free algebra sheaf is stated in the
second. The two spellings are not syntactically equal, so `rw` cannot see a composition that
mixes them; the proofs below therefore compose such equalities with `Eq.trans` and `congrArg`,
which work at the default transparency level.

That the sheaf inverse image is the sheafification of the presheaf inverse image is proved from
the two adjunctions rather than from `TopCat.Sheaf.pullbackIso`: the morphisms to a sheaf out of
the underlying presheaf of `f⁻¹B` and out of the presheaf inverse image of `B` are identified by
composing four bijections, which is exactly the membership of the comparison morphism in
`CategoryTheory.GrothendieckTopology.W`, and local bijectivity follows. That the inverse image of
presheaves commutes with the forgetful functor is `Functor.lanCompIsoOfPreserves`: the comma
categories indexing the left Kan extension are filtered, so `forget CommRingCat` preserves the
colimits computing it.

## References

* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Sites.FreeAlgebra

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (A : TopCat.Sheaf CommRingCat.{u} X)
  (E : (Opens X)ᵒᵖ ⥤ Type u)

/-- The variables of `A[E]`, read as a morphism `f⁻¹E ⟶ f⁻¹(A[E])` of presheaves of sets. -/
noncomputable def inverseImageVariable :
    (TopCat.Presheaf.pullback (Type u) f).obj E ⟶
      underlyingPresheaf (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv E _).symm
    (freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E ≫
      Functor.whiskerRight
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)).hom (forget CommRingCat.{u}))

/-- The transpose of the inverse image of the variables is the variables of `A[E]` followed by
the unit `A[E] ⟶ f_*f⁻¹(A[E])`. -/
theorem homEquiv_inverseImageVariable :
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv E _
        (inverseImageVariable f A E) =
      freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E ≫
        Functor.whiskerRight
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
            (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)).hom (forget CommRingCat.{u}) :=
  Equiv.apply_symm_apply _ _

/-- Transposing a morphism out of `f⁻¹(A[E])` turns its effect on the inverse image of the
variables into the effect of its transpose on the variables of `A[E]`. -/
theorem freeAlgebraSheafVariable_comp_homEquiv (Cs : TopCat.Sheaf CommRingCat.{u} Y)
    (g : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) ⟶ Cs) :
    freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ Cs g))
      (forget CommRingCat.{u}) =
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv E _
      (inverseImageVariable f A E ≫ Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map g)
        (forget CommRingCat.{u})) := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_inverseImageVariable]
  rfl

/-- Two morphisms out of `f⁻¹(A[E])` which agree on the coefficients and on the variables are
equal. -/
theorem freeAlgebraSheaf_inverseImage_hom_ext {Cs : TopCat.Sheaf CommRingCat.{u} Y}
    {g₁ g₂ : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) ⟶ Cs}
    (hc : (TopCat.Sheaf.pullback CommRingCat.{u} f).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E) ≫ g₁ =
        (TopCat.Sheaf.pullback CommRingCat.{u} f).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E) ≫ g₂)
    (hv : inverseImageVariable f A E ≫ Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map g₁)
          (forget CommRingCat.{u}) =
        inverseImageVariable f A E ≫ Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map g₂)
          (forget CommRingCat.{u})) :
    g₁ = g₂ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ Cs).injective
  refine freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X) A _ E ?_ ?_
  · exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        f).homEquiv_naturality_left _ _).symm.trans
      ((congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ Cs)
          hc).trans ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            f).homEquiv_naturality_left _ _))
  · rw [freeAlgebraSheafVariable_comp_homEquiv f A E Cs g₁,
      freeAlgebraSheafVariable_comp_homEquiv f A E Cs g₂, hv]

/-- The morphism `A[E] ⟶ f_*((f⁻¹A)[f⁻¹E])` sending a coefficient to its inverse-image section
and the variable `[x]` to the variable at the inverse image of `x`. -/
noncomputable def toPushforwardFreeAlgebraSheaf :
    freeAlgebraSheaf (Opens.grothendieckTopology X) A E ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Presheaf.pullback (Type u) f).obj E)) :=
  freeAlgebraSheafDesc (Opens.grothendieckTopology X) A _ E
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv A _
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) _ _))
    ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv E _
      (freeAlgebraSheafVariable (Opens.grothendieckTopology Y) _ _))

/-- The comparison morphism `f⁻¹(A[E]) ⟶ (f⁻¹A)[f⁻¹E]`. -/
noncomputable def inverseImageHom :
    (TopCat.Sheaf.pullback CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) ⟶
      freeAlgebraSheaf (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Presheaf.pullback (Type u) f).obj E) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _).symm
    (toPushforwardFreeAlgebraSheaf f A E)

/-- The transpose of the comparison morphism. -/
theorem homEquiv_inverseImageHom :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _
        (inverseImageHom f A E) = toPushforwardFreeAlgebraSheaf f A E :=
  Equiv.apply_symm_apply _ _

/-- The comparison morphism respects the structural morphisms from `f⁻¹A`. -/
theorem map_freeAlgebraSheafCoefficientMap_comp_inverseImageHom :
    (TopCat.Sheaf.pullback CommRingCat.{u} f).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E) ≫
      inverseImageHom f A E =
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Presheaf.pullback (Type u) f).obj E) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv A _).injective
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv_naturality_left
    _ _).trans ?_
  refine (congrArg (fun t ↦ freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E ≫ t)
    (homEquiv_inverseImageHom f A E)).trans ?_
  exact freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- The comparison morphism carries the inverse image of the variable `[x]` to the variable at
the inverse image of `x`. -/
theorem inverseImageVariable_comp_inverseImageHom :
    inverseImageVariable f A E ≫ Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
          (inverseImageHom f A E)) (forget CommRingCat.{u}) =
      freeAlgebraSheafVariable (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Presheaf.pullback (Type u) f).obj E) := by
  apply ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv E _).injective
  rw [← freeAlgebraSheafVariable_comp_homEquiv f A E _ (inverseImageHom f A E)]
  refine (congrArg (fun t ↦ freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E ≫
    Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map t)
      (forget CommRingCat.{u})) (homEquiv_inverseImageHom f A E)).trans ?_
  exact freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

/-- The comparison morphism `(f⁻¹A)[f⁻¹E] ⟶ f⁻¹(A[E])`. -/
noncomputable def inverseImageInv :
    freeAlgebraSheaf (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Presheaf.pullback (Type u) f).obj E) ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) :=
  freeAlgebraSheafDesc (Opens.grothendieckTopology Y) _ _ _
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).map
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E))
    (inverseImageVariable f A E)

/-- The comparison morphism `(f⁻¹A)[f⁻¹E] ⟶ f⁻¹(A[E])` respects the structural morphisms from
`f⁻¹A`. -/
theorem freeAlgebraSheafCoefficientMap_comp_inverseImageInv :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Presheaf.pullback (Type u) f).obj E) ≫ inverseImageInv f A E =
      (TopCat.Sheaf.pullback CommRingCat.{u} f).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E) :=
  freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- The comparison morphism `(f⁻¹A)[f⁻¹E] ⟶ f⁻¹(A[E])` carries the variable at the inverse
image of `x` to the inverse image of the variable `[x]`. -/
theorem freeAlgebraSheafVariable_comp_inverseImageInv :
    freeAlgebraSheafVariable (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Presheaf.pullback (Type u) f).obj E) ≫
        Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
            (inverseImageInv f A E)) (forget CommRingCat.{u}) =
      inverseImageVariable f A E :=
  freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

/-- **The inverse image of a free algebra sheaf.** The inverse image of the free `A`-algebra on
a presheaf of sets `E` is the free `f⁻¹A`-algebra on the inverse image of `E`. -/
noncomputable def inverseImageIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) ≅
      freeAlgebraSheaf (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Presheaf.pullback (Type u) f).obj E) where
  hom := inverseImageHom f A E
  inv := inverseImageInv f A E
  hom_inv_id := by
    refine freeAlgebraSheaf_inverseImage_hom_ext f A E ?_ ?_
    · exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ inverseImageInv f A E)
            (map_freeAlgebraSheafCoefficientMap_comp_inverseImageHom f A E)).trans
          (freeAlgebraSheafCoefficientMap_comp_inverseImageInv f A E))).trans
        (Category.comp_id _).symm
    · have h : inverseImageVariable f A E ≫ Functor.whiskerRight
            ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
                (inverseImageHom f A E) ≫
              (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
                (inverseImageInv f A E)) (forget CommRingCat.{u}) =
          inverseImageVariable f A E := by
        rw [Functor.whiskerRight_comp, ← Category.assoc,
          inverseImageVariable_comp_inverseImageHom,
          freeAlgebraSheafVariable_comp_inverseImageInv]
      exact h.trans (Category.comp_id _).symm
  inv_hom_id := by
    refine freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology Y) _ _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ inverseImageHom f A E)
            (freeAlgebraSheafCoefficientMap_comp_inverseImageInv f A E)).trans
          (map_freeAlgebraSheafCoefficientMap_comp_inverseImageHom f A E))).trans
        (Category.comp_id _).symm
    · have h : freeAlgebraSheafVariable (Opens.grothendieckTopology Y)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
              ((TopCat.Presheaf.pullback (Type u) f).obj E) ≫
            Functor.whiskerRight
              ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
                  (inverseImageInv f A E) ≫
                (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
                  (inverseImageHom f A E)) (forget CommRingCat.{u}) =
          freeAlgebraSheafVariable (Opens.grothendieckTopology Y)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
              ((TopCat.Presheaf.pullback (Type u) f).obj E) := by
        rw [Functor.whiskerRight_comp, ← Category.assoc,
          freeAlgebraSheafVariable_comp_inverseImageInv,
          inverseImageVariable_comp_inverseImageHom]
      exact h.trans (Category.comp_id _).symm

/-- The forward morphism of `inverseImageIso` is `inverseImageHom`. -/
@[simp]
theorem inverseImageIso_hom : (inverseImageIso f A E).hom = inverseImageHom f A E := rfl

/-- The inverse morphism of `inverseImageIso` is `inverseImageInv`. -/
@[simp]
theorem inverseImageIso_inv : (inverseImageIso f A E).inv = inverseImageInv f A E := rfl

/-! ### The inverse image of the underlying presheaf of sets of a sheaf -/

variable (B : TopCat.Sheaf CommRingCat.{u} X)

/-- The comparison morphism of presheaves of sets from the inverse image of the underlying
presheaf of sets of a sheaf of commutative rings `B` to the underlying presheaf of sets of the
inverse image sheaf `f⁻¹B`. -/
noncomputable def toUnderlyingInverseImage :
    (TopCat.Presheaf.pullback (Type u) f).obj
        (underlyingPresheaf (Opens.grothendieckTopology X) B) ⟶
      underlyingPresheaf (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _).symm
    (Functor.whiskerRight
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom
      (forget CommRingCat.{u}))

/-- The transpose of the comparison morphism is the unit `B ⟶ f_*f⁻¹B` of the inverse-image
adjunction for sheaves of commutative rings, read on underlying presheaves of sets. -/
theorem homEquiv_toUnderlyingInverseImage :
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _
        (toUnderlyingInverseImage f B) =
      Functor.whiskerRight
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom
        (forget CommRingCat.{u}) :=
  Equiv.apply_symm_apply _ _

/-- Transposing a morphism out of `f⁻¹B` turns its effect on the comparison morphism into the
effect of its transpose on the unit `B ⟶ f_*f⁻¹B`. -/
theorem toUnderlyingInverseImage_comp_homEquiv (T : (Opens Y)ᵒᵖ ⥤ Type u)
    (g : underlyingPresheaf (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) ⟶ T) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ T
        (toUnderlyingInverseImage f B ≫ g) =
      Functor.whiskerRight
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom
          (forget CommRingCat.{u}) ≫
        (TopCat.Presheaf.pushforward (Type u) f).map g := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_toUnderlyingInverseImage]
  rfl

/-! ### The comparison morphism is a local isomorphism -/

/-- The inverse image of a presheaf of commutative rings along a continuous map is a pointwise
left Kan extension: the comma categories indexing the colimits are filtered. -/
instance hasPointwiseLeftKanExtension_opensMap_op (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}) :
    (Opens.map f).op.HasPointwiseLeftKanExtension F := fun _ => inferInstance

/-- Forgetting the ring structure preserves the pointwise left Kan extension computing the
inverse image of a presheaf of commutative rings: the colimits involved are filtered. -/
instance forget_preservesPointwiseLeftKanExtension (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}) :
    (forget CommRingCat.{u}).PreservesPointwiseLeftKanExtension F (Opens.map f).op :=
  fun _ => inferInstance

/-- **The inverse image of presheaves commutes with the forgetful functor.** The underlying
presheaf of sets of the presheaf inverse image of `B` is the presheaf inverse image of the
underlying presheaf of sets of `B`, because the colimits computing the inverse image are
filtered and are therefore preserved by `forget CommRingCat`. -/
noncomputable def underlyingPullbackIso :
    (TopCat.Presheaf.pullback CommRingCat.{u} f).obj B.obj ⋙ forget CommRingCat.{u} ≅
      (TopCat.Presheaf.pullback (Type u) f).obj
        (underlyingPresheaf (Opens.grothendieckTopology X) B) :=
  (Functor.lanCompIsoOfPreserves (forget CommRingCat.{u}) (Opens.map f).op).app B.obj

/-- The transpose of the inverse of `Stacks.Sites.FreeAlgebra.underlyingPullbackIso` is the unit
of the inverse-image adjunction for presheaves of commutative rings, read on underlying
presheaves of sets. -/
theorem homEquiv_underlyingPullbackIso_inv :
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _
        (underlyingPullbackIso f B).inv =
      Functor.whiskerRight
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B.obj)
        (forget CommRingCat.{u}) := by
  rw [Adjunction.homEquiv_unit]
  exact NatTrans.ext <| funext fun U =>
    Functor.leftKanExtensionCompIsoOfPreserves_inv_fac_app (forget CommRingCat.{u}) B.obj
      (Opens.map f).op U

/-- The comparison morphism of presheaves of commutative rings from the presheaf inverse image
of `B` to the underlying presheaf of the sheaf inverse image `f⁻¹B`, obtained by transposing the
unit `B ⟶ f_*f⁻¹B`. -/
noncomputable def toSheafInverseImage :
    (TopCat.Presheaf.pullback CommRingCat.{u} f).obj B.obj ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B).obj :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom

/-- **The sheaf inverse image is the sheafification of the presheaf inverse image.** The
comparison morphism becomes an isomorphism after sheafification: precomposing with it identifies
the morphisms to a sheaf out of the underlying presheaf of `f⁻¹B` with those out of the presheaf
inverse image, by the two inverse-image adjunctions. -/
theorem w_toSheafInverseImage :
    (Opens.grothendieckTopology Y).W (toSheafInverseImage f B) := by
  intro T hT
  let T' : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u} := ⟨T, hT⟩
  let E : (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B).obj ⟶ T) ≃
      ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj B.obj ⟶ T) :=
    ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).homEquiv
        (X := (TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) (Y := T')).symm.trans
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv B T').trans
        (((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv
            (X := B) (Y := (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj T')).trans
          ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
            B.obj T).symm))
  have hEq : (fun g => toSheafInverseImage f B ≫ g) = E := by
    funext g
    exact (Adjunction.homEquiv_naturality_right_symm _ _ _).symm
  rw [hEq]
  exact E.bijective

/-- The comparison morphism `toSheafInverseImage f B` is locally injective. -/
instance isLocallyInjective_toSheafInverseImage :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) (toSheafInverseImage f B) :=
  (((Opens.grothendieckTopology Y).W_iff_isLocallyBijective
    (toSheafInverseImage f B)).mp (w_toSheafInverseImage f B)).1

/-- The comparison morphism `toSheafInverseImage f B` is locally surjective. -/
instance isLocallySurjective_toSheafInverseImage :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) (toSheafInverseImage f B) :=
  (((Opens.grothendieckTopology Y).W_iff_isLocallyBijective
    (toSheafInverseImage f B)).mp (w_toSheafInverseImage f B)).2

/-- The comparison morphism of presheaves of sets factors as the identification of the inverse
image of the underlying presheaf of sets with the underlying presheaf of sets of the inverse
image, followed by the comparison morphism of presheaves of commutative rings. -/
theorem toUnderlyingInverseImage_eq_comp :
    toUnderlyingInverseImage f B =
      (underlyingPullbackIso f B).inv ≫
        Functor.whiskerRight (toSheafInverseImage f B) (forget CommRingCat.{u}) := by
  apply ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _).injective
  have h : (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B.obj ≫
      (TopCat.Presheaf.pushforward CommRingCat.{u} f).map (toSheafInverseImage f B) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  rw [homEquiv_toUnderlyingInverseImage, Adjunction.homEquiv_naturality_right,
    homEquiv_underlyingPullbackIso_inv]
  exact (congrArg (fun α => Functor.whiskerRight α (forget CommRingCat.{u})) h).symm

/-- **The comparison morphism of presheaves of sets is locally injective.** -/
instance isLocallyInjective_toUnderlyingInverseImage :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (toUnderlyingInverseImage f B) := by
  rw [toUnderlyingInverseImage_eq_comp]
  infer_instance

/-- **The comparison morphism of presheaves of sets is locally surjective.** -/
instance isLocallySurjective_toUnderlyingInverseImage :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (toUnderlyingInverseImage f B) := by
  rw [toUnderlyingInverseImage_eq_comp]
  infer_instance

/-! ### The inverse image of the canonical presentation -/

/-- The canonical presentation `A[B] ⟶ B` carries the variable `[b]` to `b`. -/
theorem freeAlgebraSheafVariable_comp_canonicalPresentation {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{u}]
    (A' B' : Sheaf J CommRingCat.{u}) (a : A' ⟶ B') :
    freeAlgebraSheafVariable J A' (underlyingPresheaf J B') ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{u}).map (canonicalPresentation J A' B' a))
        (forget CommRingCat.{u}) = 𝟙 _ :=
  freeAlgebraSheafVariable_comp_desc J A' B' (underlyingPresheaf J B') a (𝟙 _)

/-- The canonical presentation `A[B] ⟶ B` followed by a morphism `B ⟶ D` carries the variable
`[b]` to the image of `b`. -/
theorem freeAlgebraSheafVariable_comp_canonicalPresentation_comp {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{u}]
    (A' B' D' : Sheaf J CommRingCat.{u}) (a : A' ⟶ B') (g : B' ⟶ D') :
    freeAlgebraSheafVariable J A' (underlyingPresheaf J B') ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{u}).map (canonicalPresentation J A' B' a) ≫
          (sheafToPresheaf J CommRingCat.{u}).map g) (forget CommRingCat.{u}) =
      Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{u}).map g)
        (forget CommRingCat.{u}) := by
  rw [Functor.whiskerRight_comp, ← Category.assoc,
    freeAlgebraSheafVariable_comp_canonicalPresentation, Category.id_comp]

/-- The comparison `f⁻¹(A[E]) ⟶ (f⁻¹A)[f⁻¹E]`, followed by the morphism induced by a morphism
`τ : f⁻¹E ⟶ E₂` of presheaves of sets and by a morphism `g` out of `(f⁻¹A)[E₂]`, carries the
inverse image of the variable `[x]` to the image under `g` of the variable `[τ x]`. -/
theorem inverseImageVariable_comp_inverseImageHom_map_comp
    (E₂ : (Opens Y)ᵒᵖ ⥤ Type u)
    (τ : (TopCat.Presheaf.pullback (Type u) f).obj E ⟶ E₂)
    (Cs : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (g : freeAlgebraSheaf (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) E₂ ⟶ Cs) :
    inverseImageVariable f A E ≫ Functor.whiskerRight
        (((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
              (inverseImageHom f A E) ≫
            (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
              (freeAlgebraSheafMap (Opens.grothendieckTopology Y)
                ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) τ)) ≫
          (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map g)
        (forget CommRingCat.{u}) =
      τ ≫ freeAlgebraSheafVariable (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) E₂ ≫
        Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map g)
          (forget CommRingCat.{u}) := by
  rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, ← Category.assoc, ← Category.assoc,
    inverseImageVariable_comp_inverseImageHom]
  exact (congrArg (· ≫ Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map g)
        (forget CommRingCat.{u}))
      (freeAlgebraSheafVariable_comp_map (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) τ)).trans (Category.assoc _ _ _)

/-- **The inverse image of a free algebra sheaf on a sheaf of rings.** The inverse image of the
free `A`-algebra `A[B]` on a sheaf of commutative rings `B` is the free `f⁻¹A`-algebra on
`f⁻¹B`. -/
noncomputable def underlyingInverseImageIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) ≅
      freeAlgebraSheaf (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        (underlyingPresheaf (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) :=
  (inverseImageIso f A (underlyingPresheaf (Opens.grothendieckTopology X) B)).trans
    (freeAlgebraSheafMapIso ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      (toUnderlyingInverseImage f B))

/-- The forward morphism of `underlyingInverseImageIso` is `inverseImageHom` followed by the map
of free algebra sheaves induced by `toUnderlyingInverseImage f B`. -/
@[simp]
theorem underlyingInverseImageIso_hom :
    (underlyingInverseImageIso f A B).hom =
      inverseImageHom f A (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫
        freeAlgebraSheafMap (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A) (toUnderlyingInverseImage f B) :=
  rfl

/-- If `a ≫ g = b` and `b ≫ h = k`, then `a ≫ g ≫ h = k`. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X}
    {g : X ⟶ Y} {h : Y ⟶ Z} {b : W ⟶ Y} {k : W ⟶ Z} (e₁ : a ≫ g = b) (e₂ : b ≫ h = k) :
    a ≫ g ≫ h = k :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) e₁).trans e₂)

/-- The isomorphism `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` respects the structural morphisms from
`f⁻¹A`. -/
theorem map_freeAlgebraSheafCoefficientMap_comp_underlyingInverseImageIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} f).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) ≫
        (underlyingInverseImageIso f A B).hom =
      freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        (underlyingPresheaf (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) :=
  comp_comp_eq_of_comp_eq
    (map_freeAlgebraSheafCoefficientMap_comp_inverseImageHom f A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (freeAlgebraSheafCoefficientMap_comp_map (Opens.grothendieckTopology Y) _
      (toUnderlyingInverseImage f B))

/-- The isomorphism `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` followed by the canonical presentation of
`f⁻¹B` carries the inverse image of the variable `[b]` to `b`. -/
theorem inverseImageVariable_comp_underlyingInverseImageIso_canonicalPresentation
    (a : A ⟶ B) :
    inverseImageVariable f A (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫
        Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
            ((underlyingInverseImageIso f A B).hom ≫
              canonicalPresentation (Opens.grothendieckTopology Y)
                ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
                ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
                ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)))
          (forget CommRingCat.{u}) =
      toUnderlyingInverseImage f B :=
  (inverseImageVariable_comp_inverseImageHom_map_comp f A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) _
      (toUnderlyingInverseImage f B) _ _).trans
    ((congrArg (toUnderlyingInverseImage f B ≫ ·)
        (freeAlgebraSheafVariable_comp_canonicalPresentation (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))).trans (Category.comp_id _))

/-- The inverse image of the canonical presentation carries the inverse image of the variable
`[b]` to `b`. -/
theorem inverseImageVariable_comp_map_canonicalPresentation (a : A ⟶ B) :
    inverseImageVariable f A (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫
        Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map
              (canonicalPresentation (Opens.grothendieckTopology X) A B a)))
          (forget CommRingCat.{u}) =
      toUnderlyingInverseImage f B := by
  apply ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _).injective
  have hu : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map
          (canonicalPresentation (Opens.grothendieckTopology X) A B a)) =
      canonicalPresentation (Opens.grothendieckTopology X) A B a ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B :=
    (Adjunction.homEquiv_unit _ _ _ _).trans
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.naturality _).symm)
  refine ((freeAlgebraSheafVariable_comp_homEquiv f A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) _
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map
        (canonicalPresentation (Opens.grothendieckTopology X) A B a))).symm.trans ?_).trans
    (homEquiv_toUnderlyingInverseImage f B).symm
  exact (congrArg (fun t => freeAlgebraSheafVariable (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫ Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map t)
        (forget CommRingCat.{u})) hu).trans
    (freeAlgebraSheafVariable_comp_canonicalPresentation_comp (Opens.grothendieckTopology X)
      A B _ a ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B))

/-- **The isomorphism `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` is compatible with the canonical
presentations.** The inverse image of the canonical presentation of `B` is the canonical
presentation of `f⁻¹B` read through the isomorphism. -/
theorem underlyingInverseImageIso_comp_canonicalPresentation (a : A ⟶ B) :
    (underlyingInverseImageIso f A B).hom ≫
        canonicalPresentation (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a) =
      (TopCat.Sheaf.pullback CommRingCat.{u} f).map
        (canonicalPresentation (Opens.grothendieckTopology X) A B a) := by
  refine freeAlgebraSheaf_inverseImage_hom_ext f A _ ?_ ?_
  · refine (comp_comp_eq_of_comp_eq
      (map_freeAlgebraSheafCoefficientMap_comp_underlyingInverseImageIso f A B)
      (canonicalPresentation_comp_coefficientMap (Opens.grothendieckTopology Y) _ _ _)).trans ?_
    exact ((((TopCat.Sheaf.pullback CommRingCat.{u} f).map_comp _ _).symm).trans
      (congrArg ((TopCat.Sheaf.pullback CommRingCat.{u} f).map)
        (canonicalPresentation_comp_coefficientMap (Opens.grothendieckTopology X) A B a))).symm
  · exact (inverseImageVariable_comp_underlyingInverseImageIso_canonicalPresentation f A B a).trans
      (inverseImageVariable_comp_map_canonicalPresentation f A B a).symm

end Stacks.Sites.FreeAlgebra

end
