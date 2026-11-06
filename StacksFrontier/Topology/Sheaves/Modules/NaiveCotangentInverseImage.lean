module

public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.CategoryTheory.Homology.HomFromMapDouble
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.RingTheory.KaehlerDifferentialIso
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.InverseImage
public import StacksFrontier.Topology.Sheaves.Modules.InverseImageStalk
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso

/-!
# The inverse image of the naive cotangent complex

Let `f : Y ⟶ X` be a continuous map of topological spaces and `a : A ⟶ B` a morphism of sheaves
of commutative rings on `X`. The inverse image of the canonical polynomial presentation
`A[B] ⟶ B` is the canonical polynomial presentation `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹B`, and the comparison
of the two conormal sequences gives a chain map

`f⁻¹ NL_{B/A} ⟶ NL_{f⁻¹B/f⁻¹A}`.

## Main definitions

* `Stacks.Sites.Conormal.sectionsMapAlong`: a morphism `ψ : A₁ ⟶ f_*A₂` of sheaves of
  commutative rings, read on sections over an open of `X`.
* `Stacks.Sites.Conormal.conormalSheafMapAlong`: the map `I₁/I₁² ⟶ f_*(I₂/I₂²)` of conormal
  sheaves induced by a presentation `φ₂ : A₂ ⟶ f⁻¹B` of `f⁻¹B` receiving a presentation
  `φ₁ : A₁ ⟶ B` of `B` through `ψ`.
* `Stacks.Sites.Conormal.tensorSheafMapAlong`: the map
  `B ⊗[A₁] Ω[A₁/R] ⟶ f_*(f⁻¹B ⊗[A₂] Ω[A₂/f⁻¹R])` induced by the same data over `R`.
* `Stacks.SheafOfModules.inverseImagePresentationHom`: the morphism `A[B] ⟶ f_*((f⁻¹A)[f⁻¹B])`
  transposing the identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`.
* `Stacks.SheafOfModules.inverseImageConormalMap` and
  `Stacks.SheafOfModules.inverseImageTensorMap`: the comparison maps `f⁻¹(I/I²) ⟶ I'/(I')²` and
  `f⁻¹(B ⊗[A[B]] Ω[A[B]/A]) ⟶ f⁻¹B ⊗[(f⁻¹A)[f⁻¹B]] Ω[(f⁻¹A)[f⁻¹B]/f⁻¹A]` for the canonical
  presentations.
* `Stacks.SheafOfModules.naiveCotangentComplexInverseImageMap`: the chain map
  `f⁻¹ NL_{B/A} ⟶ NL_{f⁻¹B/f⁻¹A}`.
* `HomologicalComplex.homFromMapDouble`, a morphism out of the image under an additive functor
  of a two-term complex given by its two components, is used here and defined in
  `StacksFrontier/CategoryTheory/Homology/HomFromMapDouble.lean`.
* `Stacks.SheafOfModules.stalkRingMapAlong`: the map `(A₁)_{f y} → (A₂)_y` on ring stalks
  induced by `ψ`.
* `Stacks.SheafOfModules.inverseImageConormalMapAlong`: the comparison
  `f⁻¹(I₁/I₁²) ⟶ I₂/I₂²` of conormal sheaves for a change of presentation along `f`, of which
  `Stacks.SheafOfModules.inverseImageConormalMap` is the case of the canonical presentations, and
  `Stacks.SheafOfModules.inverseImageTensorMapAlong`: likewise for the scalar extensions of the
  differentials.
* `Stacks.Sites.Conormal.tensorDifferentialsSheafStalkPresheafLinearEquiv`: the stalk of
  `B ⊗[A] Ω[A/R]`, identified with `(A_x/I_x) ⊗[A_x] Ω(A)_x` where the second factor is the
  stalk of the presheaf of sectionwise differentials.
* `Stacks.SheafOfModules.stalkQuotientMapAlongₛₗ` and
  `Stacks.SheafOfModules.stalkOmegaMapAlongₛₗ`: the maps `(A₁)_{f y}/(I₁)_{f y} → (A₂)_y/(I₂)_y`
  and `(Ω[A₁/R])_{f y} → (Ω[A₂/f⁻¹R])_y` induced by `ψ`.
* `Stacks.SheafOfModules.naiveCotangentComplexInverseImageIso`: the isomorphism
  `f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}`.
* `LinearMap.inverseOfBijective`: the inverse of a bijective semilinear map, semilinear over the
  inverse ring isomorphism.

## Main results

* `Stacks.SheafOfModules.inverseImagePresentationHom_comp_canonicalPresentation`: the inverse
  image of the canonical presentation is the canonical presentation of `f⁻¹a`, and
  `Stacks.SheafOfModules.kernelIdeal_le_comap_inverseImagePresentationHom`: consequently the
  inverse image carries the kernel ideal of the canonical presentation into the kernel ideal of
  the canonical presentation of `f⁻¹a`.
* `Stacks.Sites.Conormal.conormalSheafMapAlong_conormalClass` and
  `Stacks.Sites.Conormal.tensorSheafMapAlong_tensorDifferential`: the two comparison maps send
  the conormal class of `g` to the conormal class of `ψ g` and `1 ⊗ d g` to `1 ⊗ d (ψ g)`.
* `Stacks.Sites.Conormal.conormalSequence_f_naturality_along` and
  `Stacks.SheafOfModules.inverseImageConormalMap_comp_conormalSequence_f`: the two comparison
  maps commute with the left-hand maps of the two conormal sequences.
* `Stacks.SheafOfModules.naiveCotangentComplexInverseImageMap_f_negOne` and
  `Stacks.SheafOfModules.naiveCotangentComplexInverseImageMap_f_zero`: the two nonzero
  components of the chain map.
* `Stacks.SheafOfModules.bijective_cotangentMap_stalkRingMapAlong`: a bijective map of ring
  stalks matches the kernel ideals of the two presentations, hence their conormal modules.
* `Stacks.SheafOfModules.conormalSheafStalkLinearEquiv_stalkMap_inverseImageConormalMapAlong`:
  under the identification of the stalks of the two conormal sheaves with those conormal
  modules, the comparison of conormal sheaves is that map.
* `Stacks.SheafOfModules.isIso_inverseImageConormalMapAlong`: the comparison of conormal
  sheaves along `f` is an isomorphism as soon as the induced map on ring stalks is bijective at
  every point of `Y`, and
  `Stacks.SheafOfModules.isIso_inverseImageConormalMap`: it is for the canonical presentations.
* `Stacks.SheafOfModules.isIso_naiveCotangentComplexInverseImageMap_f_negOne`: consequently the
  degree `-1` component of the comparison chain map is an isomorphism.
* `Stacks.SheafOfModules.bijective_stalkOmegaMapAlongₛₗ`: the induced map on the stalks of the
  sectionwise differentials is bijective as soon as the induced map on ring stalks is, and
  `Stacks.SheafOfModules.isIso_inverseImageTensorMapAlong`: hence so is the comparison of the
  scalar extensions of the differentials along `f`.
* `Stacks.SheafOfModules.isIso_naiveCotangentComplexInverseImageMap_f_zero` and
  `Stacks.SheafOfModules.isIso_naiveCotangentComplexInverseImageMap`: the degree `0` component,
  and hence the comparison chain map itself, is an isomorphism.
* `TensorProduct.bijective_map`: the tensor product of two bijective semilinear maps over a
  bijective ring homomorphism is bijective.

## Implementation notes

The comparison maps are built in their *transposed* form: a morphism out of the inverse image of
a sheaf of modules is a morphism into the pushforward, and the source of each comparison map is a
sheafification, so `Stacks.Sites.Conormal.sheafifyLiftDesc` presents the transpose by a formula
on presheaf sections. Nothing below needs a description of the sections of an inverse image.

For the same reason the square expressing that the comparison maps commute with the differential
is proved in transposed form and transported across the hom-equivalence: both sides of the
untransposed square transpose to the two sides of
`Stacks.Sites.Conormal.conormalSequence_f_naturality_along` by naturality of the
hom-equivalence.

A morphism `ψ : A₁ ⟶ f_*A₂` of sheaves of commutative rings has two readings on sections over an
open `U` of `X`, with target the sections of `f_*A₂` over `U` or the sections of `A₂` over
`f⁻¹U`. The two spellings are definitionally equal but only the second lets instance search find
the module structures over the target ring, so every semilinear map below is stated over
`Stacks.Sites.Conormal.sectionsMapAlong`, which is the second reading.

A sheaf of commutative rings on a space carries two definitionally equal spellings of its
category structure, the one derived for `TopCat.Sheaf` and the one of `CategoryTheory.Sheaf` for
the topology of opens; `rw` cannot see a composition that mixes them, so equalities of
composites are composed with `Eq.trans` and `congrArg` instead.

The same is true of the underlying sheaf of rings: `f⁻¹B`-modules are read over
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf` of `f⁻¹B` on the inverse-image side,
since that is the target ring sheaf of `Stacks.SheafOfModules.inverseImageRingHom`, and over
`Stacks.SheafOfModules.Tensor.ringSheaf` of `f⁻¹B` on the side of the naive cotangent complex.
The two agree by definition but not reducibly, so a composite with one end over each is
well-typed while instance search, which unfolds no further than reducibly, cannot place its two
ends in a single category. Where such a composite appears, the structure that search would have
had to find is named instead: the zero morphism of
`Stacks.SheafOfModules.inverseImageTensorMap_comp_d`, the additivity of the inverse image in the
two component formulas, and the invertibility of each factor in the two degreewise
isomorphisms.

That the comparison of conormal sheaves is an isomorphism is proved stalkwise. The stalk at `y`
of the inverse image of a sheaf of modules is its stalk at `f y`
(`Stacks.InverseImageStalk.inverseImageModuleStalkEquiv`), the stalk of a conormal sheaf is the
conormal module of the kernel of the presentation on stalks
(`Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv`), and under these two identifications the
comparison becomes the map on conormal modules induced by the map on ring stalks. A bijective
map of ring stalks carries the kernel ideal of one presentation onto the kernel ideal of the
other, because the two presentations are compatible and the map on the stalks of the target is
an isomorphism; a ring isomorphism matching two ideals matches their conormal modules.

The comparison is therefore treated for an arbitrary compatible change of presentation and not
only for the canonical one: the canonical presentations are the case in which the map on ring
stalks is the stalk of the identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`, hence bijective.

The degree `0` comparison follows the same plan, with the stalk of `B ⊗[A] Ω[A/R]` taken in the
form `(A_x/I_x) ⊗[A_x] Ω(A)_x`, the Kähler differentials of the stalk map being left
unidentified. The comparison then becomes a tensor product of two semilinear bijections: the map
on the stalks of the quotients, bijective for the same reason as for the conormal modules, and
the map on the stalks of the sectionwise differentials. The second is bijective because, read
through `Stacks.RelativeDifferentialStalk.stalkLinearEquiv`, it is the map on Kähler
differentials induced by a square of ring isomorphisms — the map on the stalks of the base being
`Stacks.InverseImageStalk.ringStalkEquiv` — and such a map is bijective by
`Stacks.KaehlerDifferentialSquare.bijective_of_map_D`. Germs of local sections `1 ⊗ ω` exhaust
the stalk, which is enough to identify the comparison with that tensor product.

The two factors are semilinear over a map of ring stalks rather than linear over one ring, so
`TensorProduct.congr` does not apply and the inverse of the tensor product is built from the
inverses of the factors.

## References

* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR), the inverse image of
  the module of differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u v₁ u₁ w z

-- The three declarations that stood here are now imported from
-- `StacksFrontier/CategoryTheory/Homology/HomFromMapDouble.lean`: `mkHomFromMapDouble` →
-- `homFromMapDouble`, `mkHomFromMapDouble_f₀` → `homFromMapDouble_f₀`, `mkHomFromMapDouble_f₁` →
-- `homFromMapDouble_f₁`.

/-! ### Semilinear inverses and tensor products of bijections -/

namespace LinearMap

section SemilinearInverse

variable {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ : R₁ →+* R₂}
  {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]

/-- The inverse of a bijective semilinear map, semilinear over the inverse of the bijective ring
homomorphism it is semilinear over. -/
noncomputable def inverseOfBijective (hσ : Function.Bijective σ) (g : M₁ →ₛₗ[σ] M₂)
    (hg : Function.Bijective g) :
    M₂ →ₛₗ[((RingEquiv.ofBijective σ hσ).symm : R₂ →+* R₁)] M₁ where
  toFun := (Equiv.ofBijective g hg).symm
  map_add' x z := hg.1 <| by
    refine ((Equiv.ofBijective g hg).apply_symm_apply (x + z)).trans (Eq.symm ?_)
    refine (map_add g _ _).trans ?_
    exact congrArg₂ (· + ·) ((Equiv.ofBijective g hg).apply_symm_apply x)
      ((Equiv.ofBijective g hg).apply_symm_apply z)
  map_smul' r x := hg.1 <| by
    refine ((Equiv.ofBijective g hg).apply_symm_apply (r • x)).trans (Eq.symm ?_)
    refine (map_smulₛₗ g _ _).trans ?_
    exact congrArg₂ (· • ·) ((RingEquiv.ofBijective σ hσ).apply_symm_apply r)
      ((Equiv.ofBijective g hg).apply_symm_apply x)

/-- The inverse of a bijective semilinear map `g` sends `g x` to `x`. -/
@[simp]
theorem inverseOfBijective_apply_apply (hσ : Function.Bijective σ) (g : M₁ →ₛₗ[σ] M₂)
    (hg : Function.Bijective g) (x : M₁) : inverseOfBijective hσ g hg (g x) = x :=
  (Equiv.ofBijective g hg).symm_apply_apply x

/-- A bijective semilinear map `g` sends the image of `x` under its inverse to `x`. -/
@[simp]
theorem apply_inverseOfBijective_apply (hσ : Function.Bijective σ) (g : M₁ →ₛₗ[σ] M₂)
    (hg : Function.Bijective g) (x : M₂) : g (inverseOfBijective hσ g hg x) = x :=
  (Equiv.ofBijective g hg).apply_symm_apply x

end SemilinearInverse

end LinearMap

namespace TensorProduct

variable {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂] {σ : R₁ →+* R₂}
  {M₁ N₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid N₁] [Module R₁ N₁]
  {M₂ N₂ : Type*} [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid N₂] [Module R₂ N₂]

/-- **The tensor product of two bijective semilinear maps is bijective.** -/
theorem bijective_map (hσ : Function.Bijective σ) (g : M₁ →ₛₗ[σ] M₂) (h : N₁ →ₛₗ[σ] N₂)
    (hg : Function.Bijective g) (hh : Function.Bijective h) :
    Function.Bijective (TensorProduct.map g h) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨TensorProduct.map (LinearMap.inverseOfBijective hσ g hg)
      (LinearMap.inverseOfBijective hσ h hh), fun t => ?_, fun t => ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n => rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        LinearMap.inverseOfBijective_apply_apply, LinearMap.inverseOfBijective_apply_apply]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  · induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n => rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        LinearMap.apply_inverseOfBijective_apply, LinearMap.apply_inverseOfBijective_apply]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']

end TensorProduct

/-- A map is bijective if, up to equivalences on both sides, it agrees with a bijective map. -/
private theorem Function.Bijective.of_equivLike_comp_eq {α β γ δ ε E₁ E₁' E₂ : Type*}
    [EquivLike E₁ γ α] [EquivLike E₁' γ ε] [EquivLike E₂ β δ] {F : α → β} {g : ε → δ}
    (e₁ : E₁) (e₁' : E₁') (e₂ : E₂) (hg : Function.Bijective g)
    (h : ∀ c, e₂ (F (e₁ c)) = g (e₁' c)) : Function.Bijective F := by
  refine (EquivLike.bijective_comp e₁ F).1 ((EquivLike.comp_bijective (F ∘ e₁) e₂).1 ?_)
  rw [show ⇑e₂ ∘ F ∘ ⇑e₁ = g ∘ e₁' from funext h]
  exact hg.comp (EquivLike.bijective e₁')

namespace Stacks.Sites.Conormal

open AlgebraicGeometry.SheafOfModules (inverseImageRingHom)

/-! ### Change of presentation along a continuous map

Let `f : Y ⟶ X` be a continuous map, let `φ₁ : A₁ ⟶ B` be a presentation of a sheaf of
commutative rings on `X` and let `φ₂ : A₂ ⟶ f⁻¹B` be a presentation of its inverse image. A
morphism `ψ : A₁ ⟶ f_*A₂` compatible with the two presentations carries the kernel ideal of
`φ₁` over `U` into the kernel ideal of `φ₂` over `f⁻¹U`, and hence induces maps from the terms
of the conormal sequence of `φ₁` to the pushforwards of the terms of the conormal sequence of
`φ₂`.
-/

section ChangeOfPresentationAlong

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (B : TopCat.Sheaf CommRingCat.{u} X)
  {A₁ : TopCat.Sheaf CommRingCat.{u} X} {A₂ : TopCat.Sheaf CommRingCat.{u} Y}
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ (TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
  (ψ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂)

/-- A morphism `ψ : A₁ ⟶ f_*A₂` of sheaves of commutative rings, read on sections over an open
`U` of `X` as a ring homomorphism `A₁(U) → A₂(f⁻¹U)`. -/
noncomputable def sectionsMapAlong (U : (Opens X)ᵒᵖ) :
    A₁.obj.obj U ⟶ A₂.obj.obj ((Opens.map f).op.obj U) :=
  ψ.hom.app U

/-- The sections of `ψ` commute with the restriction maps. -/
theorem sectionsMapAlong_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : A₁.obj.obj U) :
    (sectionsMapAlong f ψ V).hom ((A₁.obj.map i).hom s) =
      (A₂.obj.map ((Opens.map f).op.map i)).hom ((sectionsMapAlong f ψ U).hom s) :=
  NatTrans.naturality_apply ψ.hom i s

variable (hψ : ψ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map φ₂ =
  φ₁ ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)

include hψ in
/-- Compatibility of `ψ` with the two presentations, on sections: the image of a section `s` of
`A₁` under `φ₂ ∘ ψ` is the inverse-image section of `φ₁ s`. -/
theorem sectionsMapAlong_comp_apply (U : (Opens X)ᵒᵖ) (s : A₁.obj.obj U) :
    (φ₂.hom.app ((Opens.map f).op.obj U)).hom ((sectionsMapAlong f ψ U).hom s) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B).hom.app U).hom
        ((φ₁.hom.app U).hom s) :=
  congrArg (fun t : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) ↦ ((t.hom.app U).hom s)) hψ

include hψ in
/-- **`ψ` carries the kernel ideal of `φ₁` into the kernel ideal of `φ₂`.** -/
theorem kernelIdeal_le_comap_sectionsMapAlong (U : (Opens X)ᵒᵖ) :
    kernelIdeal φ₁.hom U ≤
      (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)).comap (sectionsMapAlong f ψ U).hom := by
  intro s hs
  refine (sectionsMapAlong_comp_apply f B φ₁ φ₂ ψ hψ U s).trans ?_
  exact (congrArg ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f).unit.app B).hom.app U).hom) hs).trans (map_zero _)

include hψ in
/-- The induced map on quotients is compatible with the inclusions into `B` and `f⁻¹B`. -/
theorem quotientToTarget_quotientMapAlong (U : (Opens X)ᵒᵖ)
    (r : (quotientPresheaf φ₁.hom).obj U) :
    (quotientToTarget φ₂.hom).app ((Opens.map f).op.obj U)
        (Ideal.quotientMap (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
          (sectionsMapAlong f ψ U).hom
          (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U) r) =
      ((inverseImageRingHom f B).hom.app U).hom ((quotientToTarget φ₁.hom).app U r) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact sectionsMapAlong_comp_apply f B φ₁ φ₂ ψ hψ U r

include hψ in
/-- The induced map `A₁(U)/I₁(U) → A₂(f⁻¹U)/I₂(f⁻¹U)`, semilinear over `ψ`. -/
noncomputable def quotientMapAlongₛₗ (U : (Opens X)ᵒᵖ) :
    (A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) →ₛₗ[(sectionsMapAlong f ψ U).hom]
      (A₂.obj.obj ((Opens.map f).op.obj U) ⧸ kernelIdeal φ₂.hom ((Opens.map f).op.obj U)) where
  toFun := Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
    (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U)
  map_add' := map_add (Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
    (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U))
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((sectionsMapAlong f ψ U).hom (r * x)) =
      Ideal.Quotient.mk _ ((sectionsMapAlong f ψ U).hom r * (sectionsMapAlong f ψ U).hom x)
    exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)))
      (map_mul (sectionsMapAlong f ψ U).hom r x)

include hψ in
/-- The induced map on quotients commutes with the restriction maps. -/
theorem quotientMapAlongₛₗ_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (b : (quotientPresheaf φ₁.hom).obj U) :
    quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ V ((quotientPresheaf φ₁.hom).map i b) =
      (quotientPresheaf φ₂.hom).map ((Opens.map f).op.map i)
        (quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ U b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  show Ideal.Quotient.mk _ ((sectionsMapAlong f ψ V).hom ((A₁.obj.map i).hom b)) =
    Ideal.Quotient.mk _
      ((A₂.obj.map ((Opens.map f).op.map i)).hom ((sectionsMapAlong f ψ U).hom b))
  exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂.hom ((Opens.map f).op.obj V)))
    (sectionsMapAlong_naturality f ψ i b)

include hψ in
/-- The induced map on conormal modules commutes with the restriction maps. -/
theorem cotangentMapAlong_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (c : (conormalPresheaf φ₁.hom).obj U) :
    cotangentMap (kernelIdeal φ₁.hom V) (kernelIdeal φ₂.hom ((Opens.map f).op.obj V))
        (sectionsMapAlong f ψ V).hom
        (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ V)
        ((conormalPresheaf φ₁.hom).map i c) =
      (conormalPresheaf φ₂.hom).map ((Opens.map f).op.map i)
        (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
          (sectionsMapAlong f ψ U).hom
          (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U) c) := by
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁.hom U).toCotangent_surjective c
  show (kernelIdeal φ₂.hom _).toCotangent
      ⟨(sectionsMapAlong f ψ V).hom ((A₁.obj.map i).hom (c : A₁.obj.obj U)), _⟩ =
    (kernelIdeal φ₂.hom _).toCotangent
      ⟨(A₂.obj.map ((Opens.map f).op.map i)).hom
        ((sectionsMapAlong f ψ U).hom (c : A₁.obj.obj U)), _⟩
  congr 1
  ext
  exact sectionsMapAlong_naturality f ψ i (c : A₁.obj.obj U)

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom]

include hψ in
/-- **The comparison of conormal sheaves along `f`.** The map `I₁/I₁² ⟶ f_*(I₂/I₂²)` sending the
conormal class of a section `s` of `I₁` to the conormal class of `ψ s`. -/
noncomputable def conormalSheafMapAlong :
    conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁ ⟶
      (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂) := by
  refine sheafifyLiftDesc.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
    (conormalPresheaf φ₁.hom) _
    (fun U c ↦ toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂
      (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj U)
      (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
        (sectionsMapAlong f ψ U).hom
        (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U) c)) ?_ ?_ ?_
  · intro U c c'
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj U))
      (map_add (cotangentMap (kernelIdeal φ₁.hom U)
        (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)) (sectionsMapAlong f ψ U).hom
        (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U)) c c')).trans
      (toAssociatedModule_add.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) _ _ _)
  · intro U r c
    refine (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj U))
      (map_smulₛₗ (cotangentMap (kernelIdeal φ₁.hom U)
        (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)) (sectionsMapAlong f ψ U).hom
        (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U)) r c)).trans ?_
    refine (toAssociatedModule_smul.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
      (conormalPresheaf φ₂.hom) _ _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)).obj.obj
        ((Opens.map f).op.obj U) ↦ s • toAssociatedModule.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ _ φ₂ (conormalPresheaf φ₂.hom)
          ((Opens.map f).op.obj U)
          (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
            (sectionsMapAlong f ψ U).hom
            (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U) c))
      (quotientToTarget_quotientMapAlong f B φ₁ φ₂ ψ hψ U r)
  · intro U V i c
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj V))
      (cotangentMapAlong_naturality f B φ₁ φ₂ ψ hψ i c)).trans
      (toAssociatedModule_map.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.map i) _)

include hψ in
/-- On presheaf sections the comparison of conormal sheaves is the induced map on conormal
modules. -/
theorem conormalSheafMapAlong_toAssociatedModule (U : (Opens X)ᵒᵖ)
    (c : (conormalPresheaf φ₁.hom).obj U) :
    ((conormalSheafMapAlong f B φ₁ φ₂ ψ hψ).val.app U)
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
          (conormalPresheaf φ₁.hom) U c) =
      toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ (conormalPresheaf φ₂.hom)
        ((Opens.map f).op.obj U)
        (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
          (sectionsMapAlong f ψ U).hom
          (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U) c) := by
  apply sheafifyLiftDesc_toAssociatedModule.{u, u, u, u}

variable (R : TopCat.Sheaf CommRingCat.{u} X) (a₁ : R ⟶ A₁)
  (a₂ : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj R ⟶ A₂)

include hψ in
/-- **The comparison of conormal sheaves carries conormal classes to conormal classes.** The
conormal class of a section `s` of `I₁` goes to the conormal class of `ψ s`. -/
theorem conormalSheafMapAlong_conormalClass (U : (Opens X)ᵒᵖ) (s : kernelIdeal φ₁.hom U) :
    ((conormalSheafMapAlong f B φ₁ φ₂ ψ hψ).val.app U)
        (conormalClass.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U s) =
      conormalClass.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ ((Opens.map f).op.obj U)
        ⟨(sectionsMapAlong f ψ U).hom s,
          kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U s.2⟩ :=
  conormalSheafMapAlong_toAssociatedModule f B φ₁ φ₂ ψ hψ U _

/-! #### The comparison on the scalar extension of the differentials -/

variable (ha : a₁ ≫ ψ =
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app R ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} f).map a₂)

include ha in
/-- The commutative square of rings over an open `U` of `X` inducing the map on relative
differentials. -/
theorem differentialsSquareAlong (U : (Opens X)ᵒᵖ) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app R).hom.app U) ≫
        a₂.hom.app ((Opens.map f).op.obj U) =
      a₁.hom.app U ≫ sectionsMapAlong f ψ U :=
  (congrArg (fun t : R ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂ ↦ t.hom.app U)
    ha).symm

include ha in
/-- The map `Ω[A₁(U)/R(U)] → Ω[A₂(f⁻¹U)/(f⁻¹R)(f⁻¹U)]` induced by `ψ`, semilinear over `ψ`. -/
noncomputable def differentialsMapAlong (U : (Opens X)ᵒᵖ) :
    (differentialsPresheaf a₁.hom).obj U →ₛₗ[(sectionsMapAlong f ψ U).hom]
      (differentialsPresheaf a₂.hom).obj ((Opens.map f).op.obj U) where
  toFun := CommRingCat.KaehlerDifferential.map (g' := sectionsMapAlong f ψ U)
    (differentialsSquareAlong f ψ R a₁ a₂ ha U)
  map_add' := map_add _
  map_smul' := (CommRingCat.KaehlerDifferential.map (g' := sectionsMapAlong f ψ U)
    (differentialsSquareAlong f ψ R a₁ a₂ ha U)).hom.map_smul

include ha in
/-- The map on relative differentials sends `d s` to `d` of the image of `s` under the map on
sections. -/
@[simp]
theorem differentialsMapAlong_d (U : (Opens X)ᵒᵖ) (s : A₁.obj.obj U) :
    differentialsMapAlong f ψ R a₁ a₂ ha U (CommRingCat.KaehlerDifferential.d s) =
      CommRingCat.KaehlerDifferential.d ((sectionsMapAlong f ψ U).hom s) :=
  CommRingCat.KaehlerDifferential.map_d (differentialsSquareAlong f ψ R a₁ a₂ ha U) s

include ha in
/-- The map on relative differentials commutes with the restriction maps. -/
theorem differentialsMapAlong_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (ω : (differentialsPresheaf a₁.hom).obj U) :
    differentialsMapAlong f ψ R a₁ a₂ ha V ((differentialsPresheaf a₁.hom).map i ω) =
      (differentialsPresheaf a₂.hom).map ((Opens.map f).op.map i)
        (differentialsMapAlong f ψ R a₁ a₂ ha U ω) := by
  show differentialsMapAlong f ψ R a₁ a₂ ha V ((differentialsPresheaf a₁.hom).restrictₛₗ i ω) =
    (differentialsPresheaf a₂.hom).restrictₛₗ ((Opens.map f).op.map i)
      (differentialsMapAlong f ψ R a₁ a₂ ha U ω)
  let := (a₁.hom.app U).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj.obj U)
      (Set.range (KaehlerDifferential.D (R.obj.obj U) (A₁.obj.obj U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨s, rfl⟩ := hs
      show differentialsMapAlong f ψ R a₁ a₂ ha V ((differentialsPresheaf a₁.hom).map i
          (CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) s)) =
        (differentialsPresheaf a₂.hom).map ((Opens.map f).op.map i)
          (differentialsMapAlong f ψ R a₁ a₂ ha U
            (CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) s))
      have h₁ : (differentialsPresheaf a₁.hom).map i (CommRingCat.KaehlerDifferential.d s) =
          CommRingCat.KaehlerDifferential.d (f := a₁.hom.app V) ((A₁.obj.map i).hom s) :=
        PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d a₁.hom i s
      have h₂ : (differentialsPresheaf a₂.hom).map ((Opens.map f).op.map i)
            (CommRingCat.KaehlerDifferential.d (f := a₂.hom.app ((Opens.map f).op.obj U))
              ((sectionsMapAlong f ψ U).hom s)) =
          CommRingCat.KaehlerDifferential.d (f := a₂.hom.app ((Opens.map f).op.obj V))
            ((A₂.obj.map ((Opens.map f).op.map i)).hom ((sectionsMapAlong f ψ U).hom s)) :=
        PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d a₂.hom
          ((Opens.map f).op.map i) _
      rw [h₁, differentialsMapAlong_d, differentialsMapAlong_d, h₂]
      exact congrArg CommRingCat.KaehlerDifferential.d (sectionsMapAlong_naturality f ψ i s)
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, map_add, map_add, ihx, ihy]
  | smul r ω hω ih =>
      rw [map_smulₛₗ, map_smulₛₗ, ih, map_smulₛₗ, map_smulₛₗ]
      exact congrArg (fun s : A₂.obj.obj ((Opens.map f).op.obj V) ↦ s •
        (differentialsPresheaf a₂.hom).restrictₛₗ ((Opens.map f).op.map i)
          (differentialsMapAlong f ψ R a₁ a₂ ha U ω))
        (sectionsMapAlong_naturality f ψ i r)

include hψ ha in
/-- The induced map `(A₁(U)/I₁(U)) ⊗[A₁(U)] Ω[A₁(U)/R(U)] →
(A₂(f⁻¹U)/I₂(f⁻¹U)) ⊗[A₂(f⁻¹U)] Ω[A₂(f⁻¹U)/(f⁻¹R)(f⁻¹U)]`, semilinear over `ψ`. -/
noncomputable def tensorMapAlongₛₗ (U : (Opens X)ᵒᵖ) :
    ((A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗[A₁.obj.obj U]
        ((differentialsPresheaf a₁.hom).obj U)) →ₛₗ[(sectionsMapAlong f ψ U).hom]
      ((A₂.obj.obj ((Opens.map f).op.obj U) ⧸ kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
        ⊗[A₂.obj.obj ((Opens.map f).op.obj U)]
        ((differentialsPresheaf a₂.hom).obj ((Opens.map f).op.obj U))) :=
  TensorProduct.map (quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ U)
    (differentialsMapAlong f ψ R a₁ a₂ ha U)

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom] in
include hψ ha in
/-- The induced map on the tensor product is semilinear over the induced map on `A₁/I₁`. -/
theorem tensorMapAlongₛₗ_smul (U : (Opens X)ᵒᵖ) (r : A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U)
    (x : (A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗[A₁.obj.obj U]
      ((differentialsPresheaf a₁.hom).obj U)) :
    tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U (r • x) =
      quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ U r •
        tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b ω =>
    show tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U ((r * b) ⊗ₜ ω) =
      quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ U r •
        tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U (b ⊗ₜ ω)
    simp only [tensorMapAlongₛₗ, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    congr 1
    exact map_mul (Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
      (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U)) r b
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom] in
include hψ ha in
/-- The induced map on the tensor product commutes with the restriction maps. -/
theorem tensorMapAlongₛₗ_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x : (A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗[A₁.obj.obj U]
      ((differentialsPresheaf a₁.hom).obj U)) :
    tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha V (tensorMapₛₗ φ₁.hom a₁.hom i x) =
      tensorMapₛₗ φ₂.hom a₂.hom ((Opens.map f).op.map i)
        (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b ω =>
    refine (congrArg (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha V)
      (TensorProduct.map_tmul _ _ b ω)).trans ?_
    refine (TensorProduct.map_tmul _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (tensorMapₛₗ φ₂.hom a₂.hom ((Opens.map f).op.map i))
      (TensorProduct.map_tmul _ _ b ω)).symm
    refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
    exact congrArg₂ (fun b (ω : (differentialsPresheaf a₂.hom).obj
        ((Opens.map f).op.obj V)) ↦ b ⊗ₜ[A₂.obj.obj ((Opens.map f).op.obj V)] ω)
      (quotientMapAlongₛₗ_naturality f B φ₁ φ₂ ψ hψ i b)
      (differentialsMapAlong_naturality f ψ R a₁ a₂ ha i ω)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f`.** The map
`B ⊗[A₁] Ω[A₁/R] ⟶ f_*(f⁻¹B ⊗[A₂] Ω[A₂/f⁻¹R])` sending `1 ⊗ d s` to `1 ⊗ d (ψ s)`. -/
noncomputable def tensorSheafMapAlong :
    tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ ⟶
      (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).obj
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂) := by
  refine sheafifyLiftDesc.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
    (tensorPresheaf φ₁.hom a₁.hom) _
    (fun U t ↦ toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂
      (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U)
      (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U t)) ?_ ?_ ?_
  · intro U t t'
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U))
      (map_add (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U) t t')).trans
      (toAssociatedModule_add.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) _ _ _)
  · intro U r t
    refine (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U))
      (tensorMapAlongₛₗ_smul f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U r t)).trans ?_
    refine (toAssociatedModule_smul.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
      (tensorPresheaf φ₂.hom a₂.hom) _ _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)).obj.obj
        ((Opens.map f).op.obj U) ↦ s • toAssociatedModule.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ _ φ₂ (tensorPresheaf φ₂.hom a₂.hom)
          ((Opens.map f).op.obj U) (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U t))
      (quotientToTarget_quotientMapAlong f B φ₁ φ₂ ψ hψ U r)
  · intro U V i t
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj V))
      (tensorMapAlongₛₗ_naturality f B φ₁ φ₂ ψ hψ R a₁ a₂ ha i t)).trans
      (toAssociatedModule_map.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.map i) _)

include hψ ha in
/-- On presheaf sections the comparison of the scalar extensions of the differentials is the
induced map on the tensor products. -/
theorem tensorSheafMapAlong_toAssociatedModule (U : (Opens X)ᵒᵖ)
    (t : (tensorPresheaf φ₁.hom a₁.hom).obj U) :
    ((tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha).val.app U)
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
          (tensorPresheaf φ₁.hom a₁.hom) U t) =
      toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ (tensorPresheaf φ₂.hom a₂.hom)
        ((Opens.map f).op.obj U)
        (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U t) := by
  apply sheafifyLiftDesc_toAssociatedModule.{u, u, u, u}

include hψ ha in
/-- **The comparison of the scalar extensions carries `1 ⊗ d s` to `1 ⊗ d (ψ s)`.** -/
theorem tensorSheafMapAlong_tensorDifferential (U : (Opens X)ᵒᵖ) (s : A₁.obj.obj U) :
    ((tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha).val.app U)
        (tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U s) =
      tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ ((Opens.map f).op.obj U)
        ((sectionsMapAlong f ψ U).hom s) := by
  have h : ((tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha).val.app U)
      (tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U s) =
      toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U)
        (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U
          ((1 : A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗ₜ[A₁.obj.obj U]
            CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) s)) := by
    apply sheafifyLiftDesc_toAssociatedModule.{u, u, u, u}
  refine h.trans ?_
  refine congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂
    (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U)) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg₂ (fun b (ω : (differentialsPresheaf a₂.hom).obj ((Opens.map f).op.obj U)) ↦
      b ⊗ₜ[A₂.obj.obj ((Opens.map f).op.obj U)] ω)
    (map_one (Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
      (kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ U)))
    (differentialsMapAlong_d f ψ R a₁ a₂ ha U s)

include hψ ha in
/-- **The comparison maps commute with the left-hand maps of the two conormal sequences.** -/
theorem conormalSequence_f_naturality_along :
    (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁).f ≫
        tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha =
      conormalSheafMapAlong f B φ₁ φ₂ ψ hψ ≫
        (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).map
          (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂).f := by
  apply sheafify_hom_ext.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
    (conormalPresheaf φ₁.hom)
  intro U c
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁.hom U).toCotangent_surjective c
  refine Eq.trans (congrArg ((tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha).val.app U)
    (conormalSequence_f_class.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U c)) ?_
  refine Eq.trans (tensorSheafMapAlong_tensorDifferential f B φ₁ φ₂ ψ hψ R a₁ a₂ ha U c) ?_
  refine Eq.symm (Eq.trans (congrArg
    ((conormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂).f.val.app
        ((Opens.map f).op.obj U))
    (conormalSheafMapAlong_conormalClass f B φ₁ φ₂ ψ hψ R a₁ a₂ U c)) ?_)
  exact conormalSequence_f_class.{u, u, u, u} (Opens.grothendieckTopology Y)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ ((Opens.map f).op.obj U) _

end ChangeOfPresentationAlong

/-! ### The stalk of the tensor-differentials sheaf, with the differentials unidentified -/

section TensorDifferentialsStalk

variable {Z : TopCat.{u}} (R' A' B' : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
  (a' : R' ⟶ A')
  (φ' : A' ⟶ B') [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z) φ'.hom] (x : Z)

/-- **The stalk of the tensor-differentials sheaf**, identified with
`(A_x/I_x) ⊗[A_x] Ω(A)_x`, where the second factor is the stalk of the presheaf of sectionwise
relative differentials. This is
`Stacks.Sites.Conormal.tensorDifferentialsSheafStalkLinearEquiv` with the second factor left
unidentified. -/
noncomputable def tensorDifferentialsSheafStalkPresheafLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Z) R' A' B' a'
          φ').val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk A'.obj x)]
      ((ToType (TopCat.Presheaf.stalk A'.obj x) ⧸ stalkKernelIdeal φ'.hom x)
        ⊗[ToType (TopCat.Presheaf.stalk A'.obj x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (differentialsPresheaf a'.hom).presheaf x)) :=
  (tensorSheafStalkSheafifyLinearEquiv R' A' B' a' φ' x).symm.trans
    (tensorPresheafStalkLinearEquiv φ'.hom a'.hom x)

/-- The identification carries the germ of a section of the tensor presheaf to its image under
the map taking germs in both tensor factors. -/
theorem tensorDifferentialsSheafStalkPresheafLinearEquiv_germ_toAssociatedModule
    (U : Opens Z) (hx : x ∈ U) (t : (tensorPresheaf φ'.hom a'.hom).obj (op U)) :
    tensorDifferentialsSheafStalkPresheafLinearEquiv R' A' B' a' φ' x
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Z) R' A' B' a'
            φ').val.presheaf U x hx).hom
          (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Z) A' B' φ'
            (tensorPresheaf φ'.hom a'.hom) (op U) t)) =
      germTensorₛₗ φ'.hom a'.hom x U hx t := by
  refine Eq.trans (congrArg (tensorPresheafStalkLinearEquiv φ'.hom a'.hom x)
    ((LinearEquiv.symm_apply_eq _).mpr
      (tensorSheafStalkSheafifyLinearEquiv_germ (X := Z) R' A' B' a' φ' x U hx t).symm)) ?_
  exact tensorStalkHom_germ φ'.hom a'.hom x U hx t

end TensorDifferentialsStalk

end Stacks.Sites.Conormal


namespace Stacks.Sites.FreeAlgebra

/-- The canonical polynomial presentation of a sheaf of commutative rings is locally
surjective. -/
instance isLocallySurjective_canonicalPresentation {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    Presheaf.IsLocallySurjective J (canonicalPresentation J A B a).hom :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    (canonicalPresentation_isLocallySurjective J A B a)

/-- The canonical polynomial presentation of a sheaf of commutative rings on a topological space
is locally surjective. This repeats
`Stacks.Sites.FreeAlgebra.isLocallySurjective_canonicalPresentation` at the spelling
`TopCat.Sheaf`, which instance search does not unfold. -/
instance isLocallySurjective_canonicalPresentation_opens {X : TopCat.{u}}
    (A B : TopCat.Sheaf CommRingCat.{u} X) (a : A ⟶ B) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (canonicalPresentation (Opens.grothendieckTopology X) A B a).hom :=
  isLocallySurjective_canonicalPresentation (Opens.grothendieckTopology X) A B a

end Stacks.Sites.FreeAlgebra

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom inverseImageAdjunction)

/-! ### The inverse image of the canonical presentation -/

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (A B : TopCat.Sheaf CommRingCat.{u} X) (a : A ⟶ B)

/-- The morphism of sheaves of commutative rings `A[B] ⟶ f_*((f⁻¹A)[f⁻¹B])` transposing the
identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`. -/
noncomputable def inverseImagePresentationHom :
    freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B) ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          (underlyingPresheaf (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _
    (underlyingInverseImageIso f A B).hom

/-- **The inverse image of the canonical presentation is the canonical presentation of `f⁻¹a`.**
The transposed identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` carries the canonical presentation of
`f⁻¹B` over `f⁻¹A` to the inverse-image section of the canonical presentation of `B` over `A`. -/
theorem inverseImagePresentationHom_comp_canonicalPresentation :
    inverseImagePresentationHom f A B ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
        (canonicalPresentation (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)) =
      canonicalPresentation (Opens.grothendieckTopology X) A B a ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B :=
  ((Adjunction.homEquiv_naturality_right
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f) _ _).symm.trans
    ((congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _)
        (underlyingInverseImageIso_comp_canonicalPresentation f A B a)).trans
      ((Adjunction.homEquiv_unit _ _ _ _).trans
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.naturality
          (canonicalPresentation (Opens.grothendieckTopology X) A B a)).symm))))

/-- The transposed identification is a morphism of `A`-algebras: it carries the structural
morphism of `A[B]` to the inverse-image section of the structural morphism of `(f⁻¹A)[f⁻¹B]`. -/
theorem freeAlgebraSheafCoefficientMap_comp_inverseImagePresentationHom :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫
        inverseImagePresentationHom f A B =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app A ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            (underlyingPresheaf (Opens.grothendieckTopology Y)
              ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))) :=
  (Adjunction.homEquiv_naturality_left
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f) _ _).symm.trans
    ((congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _)
        (map_freeAlgebraSheafCoefficientMap_comp_underlyingInverseImageIso f A B)).trans
      (Adjunction.homEquiv_unit _ _ _ _))

/-- **The inverse image carries the kernel ideal of the canonical presentation into the kernel
ideal of the canonical presentation of `f⁻¹a`.** -/
theorem kernelIdeal_le_comap_inverseImagePresentationHom (U : (Opens X)ᵒᵖ) :
    kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X) A B a).hom U ≤
      (kernelIdeal (canonicalPresentation (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).hom
          ((Opens.map f).op.obj U)).comap
        (sectionsMapAlong f (inverseImagePresentationHom f A B) U).hom :=
  kernelIdeal_le_comap_sectionsMapAlong f B _ _ _
    (inverseImagePresentationHom_comp_canonicalPresentation f A B a) U

/-! ### The two comparison maps -/

/-- The comparison of the degree `-1` terms, in transposed form:
`I/I² ⟶ f_*(I'/(I')²)`. -/
noncomputable def inverseImageConormalPushforwardMap :
    (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X₁ ⟶
      (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).obj
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).X₁ :=
  conormalSheafMapAlong f B _ _ _
    (inverseImagePresentationHom_comp_canonicalPresentation f A B a)

/-- The comparison of the degree `0` terms, in transposed form:
`B ⊗[A[B]] Ω[A[B]/A] ⟶ f_*(f⁻¹B ⊗[(f⁻¹A)[f⁻¹B]] Ω[(f⁻¹A)[f⁻¹B]/f⁻¹A])`. -/
noncomputable def inverseImageTensorPushforwardMap :
    (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X₂ ⟶
      (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).obj
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).X₂ :=
  tensorSheafMapAlong f B _ _ _
    (inverseImagePresentationHom_comp_canonicalPresentation f A B a) A _ _
    (freeAlgebraSheafCoefficientMap_comp_inverseImagePresentationHom f A B)

/-- **The comparison of the degree `-1` terms.** The map
`f⁻¹(I/I²) ⟶ I'/(I')²` obtained by transposing
`Stacks.SheafOfModules.inverseImageConormalPushforwardMap`. -/
noncomputable def inverseImageConormalMap :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X₁ ⟶
      (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).X₁ :=
  ((inverseImageAdjunction f B).homEquiv _ _).symm
    (inverseImageConormalPushforwardMap f A B a)

/-- **The comparison of the degree `0` terms.** The map
`f⁻¹(B ⊗[A[B]] Ω[A[B]/A]) ⟶ f⁻¹B ⊗[(f⁻¹A)[f⁻¹B]] Ω[(f⁻¹A)[f⁻¹B]/f⁻¹A]` obtained by transposing
`Stacks.SheafOfModules.inverseImageTensorPushforwardMap`. -/
noncomputable def inverseImageTensorMap :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X₂ ⟶
      (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).X₂ :=
  ((inverseImageAdjunction f B).homEquiv _ _).symm
    (inverseImageTensorPushforwardMap f A B a)

/-! ### The chain map -/

/-- Transport of a commutative square along identifications of two of its vertices. -/
private theorem comm_of_eqToHom {D : Type*} [Category D] {S₀ S₁ T₀ T₁ K₀ K₁ : D}
    (e₀ : K₀ = T₀) (e₁ : K₁ = T₁) {d : K₀ ⟶ K₁} {dT : T₀ ⟶ T₁}
    (hd : d = eqToHom e₀ ≫ dT ≫ eqToHom e₁.symm)
    {g : S₀ ⟶ S₁} {p : S₀ ⟶ T₀} {q : S₁ ⟶ T₁} (sq : g ≫ q = p ≫ dT) :
    (p ≫ eqToHom e₀.symm) ≫ d = g ≫ q ≫ eqToHom e₁.symm := by
  subst e₀
  subst e₁
  subst hd
  simpa using sq.symm

/-- Composing with a zero morphism. -/
private theorem comp_eq_zero_of_eq_zero {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    {W X' Y' : D} (u : W ⟶ X') {d : X' ⟶ Y'} (hd : d = 0) : u ≫ d = 0 := by
  rw [hd, Limits.comp_zero]

/-- The naive cotangent complex has no differential out of degree `0`. -/
theorem naiveCotangentComplex_d_zero {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (A' B' : Sheaf J CommRingCat.{w}) (a' : A' ⟶ B') (k : ℤ) :
    (naiveCotangentComplex.{v₁, u₁, w, z} J A' B' a').d 0 k = 0 := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u₁ v₁ z} (Stacks.SheafOfModules.Tensor.ringSheaf B')) :=
    hasZeroObject_of_hasTerminal_object
  show (HomologicalComplex.double
    (canonicalConormalSequence.{v₁, u₁, w, z} J A' B' a').f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d 0 k = 0
  exact HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide)

/-- The inverse image of sheaves of modules along a continuous map is additive: it is a left
adjoint between preadditive categories with binary biproducts. -/
instance additive_inverseImage :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).Additive := by
  have hc : Limits.PreservesColimitsOfSize.{u, u}
      (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)) :=
    Adjunction.leftAdjoint_preservesColimits (inverseImageAdjunction f B)
  have hz : (_root_.SheafOfModules.pullback.{u}
      (inverseImageRingHom f B)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **The two comparison maps commute with the left-hand maps of the two conormal
sequences.** -/
theorem inverseImageConormalMap_comp_conormalSequence_f :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map
          (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f ≫
        inverseImageTensorMap f A B a =
      inverseImageConormalMap f A B a ≫
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).f :=
  (Adjunction.homEquiv_naturality_left_symm (inverseImageAdjunction f B) _ _).symm.trans
    ((congrArg ((inverseImageAdjunction f B).homEquiv _ _).symm
        (conormalSequence_f_naturality_along f B _ _ _
          (inverseImagePresentationHom_comp_canonicalPresentation f A B a) A _ _
          (freeAlgebraSheafCoefficientMap_comp_inverseImagePresentationHom f A B))).trans
      (Adjunction.homEquiv_naturality_right_symm (inverseImageAdjunction f B) _ _))

/-- The square expressing that the comparison maps commute with the differentials of
`f⁻¹ NL_{B/A}` and `NL_{f⁻¹B/f⁻¹A}`. -/
theorem inverseImageConormalMap_comm :
    (inverseImageConormalMap f A B a ≫
          eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm) ≫
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).d (-1) 0 =
      (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map
          (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f ≫
        inverseImageTensorMap f A B a ≫
          eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm :=
  comm_of_eqToHom
    (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))
    (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))
    (naiveCotangentComplex_d_negOne_zero (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))
    (inverseImageConormalMap_comp_conormalSequence_f f A B a)

/-- The degree `0` component of the comparison is killed by every differential out of degree
`0`, since `NL_{f⁻¹B/f⁻¹A}` has none.

The source of the composite is read over the ring sheaf
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf` of `f⁻¹B`, which is the target ring
sheaf of `Stacks.SheafOfModules.inverseImageRingHom`, while its target is read over
`Stacks.SheafOfModules.Tensor.ringSheaf` of `f⁻¹B`, in which the naive cotangent complex is
built. The two sheaves of rings are equal by definition but not by reducible unfolding, so
instance search cannot place the two ends of the composite in one category and the zero
morphism is named with its `CategoryTheory.Limits.HasZeroMorphisms` structure supplied. -/
theorem inverseImageTensorMap_comp_d (k : ℤ) :
    (inverseImageTensorMap f A B a ≫
        eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm) ≫
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).d 0 k =
      (Limits.HasZeroMorphisms.zero (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))) _ _).zero :=
  comp_eq_zero_of_eq_zero _
    (naiveCotangentComplex_d_zero (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a) k)

/-- The comparison chain map `f⁻¹ NL_{B/A} ⟶ NL_{f⁻¹B/f⁻¹A}` from the inverse image of the naive
cotangent complex of `a : A ⟶ B` to the naive cotangent complex of the inverse-image morphism. -/
noncomputable def naiveCotangentComplexInverseImageMap :
    ((_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a) ⟶
      naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a) :=
  HomologicalComplex.homFromMapDouble
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B))
    (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (inverseImageConormalMap f A B a ≫
      eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm)
    (inverseImageTensorMap f A B a ≫
      eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm)
    (inverseImageConormalMap_comm f A B a)
    (fun k _ ↦ inverseImageTensorMap_comp_d f A B a k)

/-- In degree `-1` the comparison chain map is the comparison of the conormal sheaves. -/
theorem naiveCotangentComplexInverseImageMap_f_negOne :
    (naiveCotangentComplexInverseImageMap f A B a).f (-1) =
      (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map
          (eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a)) ≫
        inverseImageConormalMap f A B a ≫
          eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm := by
  have h₀ : (HomologicalComplex.doubleXIso₀
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a) := by
    simp only [HomologicalComplex.doubleXIso₀]
    congr 1
  refine (@HomologicalComplex.homFromMapDouble_f₀ _ _ _ _ _ _ _ _
    (additive_inverseImage f B) _ _ _ _ _ _ _ _ _ _ _ _
    (inverseImageConormalMap_comm f A B a)
    (fun k _ ↦ inverseImageTensorMap_comp_d f A B a k)).trans ?_
  exact congrArg (fun t ↦ (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map t ≫
    (inverseImageConormalMap f A B a ≫
      eqToHom (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm)) h₀

/-- In degree `0` the comparison chain map is the comparison of the scalar extensions of the
differentials. -/
theorem naiveCotangentComplexInverseImageMap_f_zero :
    (naiveCotangentComplexInverseImageMap f A B a).f 0 =
      (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map
          (eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a)) ≫
        inverseImageTensorMap f A B a ≫
          eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm := by
  have h₁ : (HomologicalComplex.doubleXIso₁
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a) := by
    simp only [HomologicalComplex.doubleXIso₁]
    congr 1
  refine (@HomologicalComplex.homFromMapDouble_f₁ _ _ _ _ _ _ _ _
    (additive_inverseImage f B) _ _ _ _ _ _ _ _ _ _ _ _
    (inverseImageConormalMap_comm f A B a)
    (fun k _ ↦ inverseImageTensorMap_comp_d f A B a k)).trans ?_
  exact congrArg (fun t ↦ (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).map t ≫
    (inverseImageTensorMap f A B a ≫
      eqToHom (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm)) h₁

/-! ### The comparison of conormal sheaves along `f` is an isomorphism

Let `φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ f⁻¹B` be locally surjective presentations and let
`ψ : A₁ ⟶ f_*A₂` be compatible with them. Then `ψ` induces a map `(A₁)_{f y} → (A₂)_y` on ring
stalks, and as soon as that map is bijective at every point of `Y` the comparison
`f⁻¹(I₁/I₁²) ⟶ I₂/I₂²` of conormal sheaves is an isomorphism, isomorphy of a morphism of
sheaves of modules being a stalkwise condition.
-/

open AlgebraicGeometry.SheafOfModules (inverseImageRingUnitApp underlyingRingSheaf
  pullbackPushforwardAdjunction_homEquiv_app_apply)

variable {A₁ : TopCat.Sheaf CommRingCat.{u} X} {A₂ : TopCat.Sheaf CommRingCat.{u} Y}
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ (TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
  (ψ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂) (y : Y)

/-- Transposing a morphism out of an inverse image, on sections: the transpose of `h` at a
section `s` is the morphism evaluated at the inverse-image section of `s`. -/
theorem inverseImageAdjunction_homEquiv_symm_val_app_unit
    {M : _root_.SheafOfModules.{u} (underlyingRingSheaf B)}
    {N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))}
    (h : M ⟶ (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).obj N)
    (U : (Opens X)ᵒᵖ) (s : M.val.obj U) :
    (((inverseImageAdjunction f B).homEquiv M N).symm h).val.app ((Opens.map f).op.obj U)
        (((inverseImageAdjunction f B).unit.app M).val.app U s) = h.val.app U s := by
  conv_rhs => rw [← ((inverseImageAdjunction f B).homEquiv M N).apply_symm_apply h]
  rw [Adjunction.homEquiv_unit]
  rfl

/-- On stalks, the transpose of `h` carries the germ at `f y` of a section `m` to the germ at `y`
of `h m`, under the identification of the stalk of an inverse image. -/
private theorem stalkMap_homEquiv_symm_inverseImageModuleStalkEquiv_germ
    {M : _root_.SheafOfModules.{u} (underlyingRingSheaf B)}
    {N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))}
    (h : M ⟶ (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f B)).obj N)
    (U : Opens X) (hU : f y ∈ U) (m : M.val.obj (op U)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (((inverseImageAdjunction f B).homEquiv M N).symm h)).hom
        (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y M
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U (f y) hU).hom m)) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.val.presheaf
        ((Opens.map f).obj U) y hU).hom (h.val.app (op U) m) := by
  refine Eq.trans (congrArg (AlgebraicGeometry.SheafOfModules.stalkMap
      (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
      (((inverseImageAdjunction f B).homEquiv M N).symm h)).hom
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv_germ f B y M U hU m)) ?_
  refine Eq.trans (AlgebraicGeometry.SheafOfModules.stalkMap_germ
    (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
    (((inverseImageAdjunction f B).homEquiv M N).symm h) ((Opens.map f).obj U) hU _) ?_
  exact congrArg _ (inverseImageAdjunction_homEquiv_symm_val_app_unit f B h (op U) m)

/-! ### The map on ring stalks induced by a change of presentation along `f` -/

/-- The ring homomorphism `(A₁)_{f y} → (A₂)_y` on stalks induced by `ψ : A₁ ⟶ f_*A₂`: the
isomorphism `(A₁)_{f y} ≅ (f⁻¹A₁)_y` of stalks along `f` followed by the stalk of the transpose
of `ψ`. -/
noncomputable def stalkRingMapAlong :
    ↑(TopCat.Presheaf.stalk A₁.obj (f y)) →+* ↑(TopCat.Presheaf.stalk A₂.obj y) :=
  (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
          A₁ A₂).symm ψ).hom).hom).comp
    (Stacks.InverseImageStalk.ringStalkEquiv f A₁ y).toRingHom

/-- The induced map on ring stalks carries the germ at `f y` of a section `s` of `A₁` to the
germ at `y` of `ψ s`. -/
theorem stalkRingMapAlong_germ (U : Opens X) (hU : f y ∈ U) (s : A₁.obj.obj (op U)) :
    stalkRingMapAlong f ψ y ((TopCat.Presheaf.germ A₁.obj U (f y) hU).hom s) =
      (TopCat.Presheaf.germ A₂.obj ((Opens.map f).obj U) y hU).hom
        ((sectionsMapAlong f ψ (op U)).hom s) := by
  refine Eq.trans (congrArg (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
        A₁ A₂).symm ψ).hom).hom)
    (Stacks.InverseImageStalk.ringStalkEquiv_germ f A₁ y U hU s)) ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj U) y hU _ _).trans ?_
  refine congrArg (TopCat.Presheaf.germ A₂.obj ((Opens.map f).obj U) y hU).hom ?_
  refine Eq.symm (Eq.trans ?_ (pullbackPushforwardAdjunction_homEquiv_app_apply f A₂
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
        A₁ A₂).symm ψ) (op U) s))
  exact congrArg (fun t : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂ ↦
      (t.hom.app (op U)).hom s)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
      A₁ A₂).apply_symm_apply ψ).symm

/-- The induced map on ring stalks is bijective as soon as the stalk of the transpose of `ψ` is
an isomorphism: the other factor is the isomorphism `(A₁)_{f y} ≅ (f⁻¹A₁)_y`. -/
theorem bijective_stalkRingMapAlong
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
        A₁ A₂).symm ψ).hom)) :
    Function.Bijective (stalkRingMapAlong f ψ y) := by
  have hb := (ConcreteCategory.isIso_iff_bijective _).1 hiso
  show Function.Bijective ((ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
          A₁ A₂).symm ψ).hom)) ∘ (Stacks.InverseImageStalk.ringStalkEquiv f A₁ y))
  exact hb.comp (Stacks.InverseImageStalk.ringStalkEquiv f A₁ y).bijective

variable (hψ : ψ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map φ₂ =
  φ₁ ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)

include hψ in
/-- **The induced map on ring stalks is compatible with the two presentations**: composing it
with the stalk of `φ₂` is composing the stalk of `φ₁` with the isomorphism `B_{f y} ≅ (f⁻¹B)_y`
of the stalks of the target. -/
theorem stalkRingMapAlong_comp_presentation (z : ↑(TopCat.Presheaf.stalk A₁.obj (f y))) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map φ₂.hom).hom
        (stalkRingMapAlong f ψ y z) =
      Stacks.InverseImageStalk.ringStalkEquiv f B y
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map φ₁.hom).hom z) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq A₁.obj z
  refine Eq.trans (congrArg (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map φ₂.hom).hom)
    (stalkRingMapAlong_germ f ψ y U hU s)) ?_
  refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj U) y hU _ _) ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B).obj ((Opens.map f).obj U) y hU).hom
    (sectionsMapAlong_comp_apply f B φ₁ φ₂ ψ hψ (op U) s)) ?_
  refine Eq.symm (Eq.trans (congrArg (Stacks.InverseImageStalk.ringStalkEquiv f B y)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f y) hU φ₁.hom s)) ?_)
  exact Stacks.InverseImageStalk.ringStalkEquiv_germ f B y U hU _

include hψ in
/-- The induced map on ring stalks carries the kernel ideal of `φ₁` at `f y` into the kernel
ideal of `φ₂` at `y`. -/
theorem stalkKernelIdeal_le_comap_stalkRingMapAlong :
    stalkKernelIdeal φ₁.hom (f y) ≤
      (stalkKernelIdeal φ₂.hom y).comap (stalkRingMapAlong f ψ y) := by
  intro z hz
  refine (stalkRingMapAlong_comp_presentation f B φ₁ φ₂ ψ y hψ z).trans ?_
  refine Eq.trans (congrArg (Stacks.InverseImageStalk.ringStalkEquiv f B y)
    (hz : ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map φ₁.hom).hom z = 0)) ?_
  exact map_zero _

include hψ in
/-- When the induced map on ring stalks is bijective its inverse carries the kernel ideal of
`φ₂` at `y` into the kernel ideal of `φ₁` at `f y`. -/
theorem stalkKernelIdeal_le_comap_stalkRingMapAlong_symm
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y)) :
    stalkKernelIdeal φ₂.hom y ≤ (stalkKernelIdeal φ₁.hom (f y)).comap
      (RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm.toRingHom := by
  intro w hw
  have hsq := stalkRingMapAlong_comp_presentation f B φ₁ φ₂ ψ y hψ
    ((RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm w)
  rw [show stalkRingMapAlong f ψ y
      ((RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm w) = w from
    (RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).apply_symm_apply w] at hsq
  refine (Stacks.InverseImageStalk.ringStalkEquiv f B y).injective
    (Eq.trans (hsq.symm.trans ?_) (map_zero _).symm)
  exact hw

include hψ in
/-- **The comparison of the conormal modules of the two kernels on stalks is bijective** as soon
as the induced map on ring stalks is: a ring isomorphism matching two ideals matches their
conormal modules. -/
theorem bijective_cotangentMap_stalkRingMapAlong
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y)) :
    Function.Bijective (cotangentMap (stalkKernelIdeal φ₁.hom (f y))
      (stalkKernelIdeal φ₂.hom y) (stalkRingMapAlong f ψ y)
      (stalkKernelIdeal_le_comap_stalkRingMapAlong f B φ₁ φ₂ ψ y hψ)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cotangentMap _ _
    (RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm.toRingHom
    (stalkKernelIdeal_le_comap_stalkRingMapAlong_symm f B φ₁ φ₂ ψ y hψ hbij), ?_, ?_⟩
  · intro c
    obtain ⟨c, rfl⟩ := (stalkKernelIdeal φ₁.hom (f y)).toCotangent_surjective c
    exact congrArg (stalkKernelIdeal φ₁.hom (f y)).toCotangent (Subtype.ext
      ((RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm_apply_apply _))
  · intro c
    obtain ⟨c, rfl⟩ := (stalkKernelIdeal φ₂.hom y).toCotangent_surjective c
    exact congrArg (stalkKernelIdeal φ₂.hom y).toCotangent (Subtype.ext
      ((RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).apply_symm_apply _))

include hψ in
/-- The induced map `(A₁)_{f y}/(I₁)_{f y} → (A₂)_y/(I₂)_y` on the stalks of the quotients,
semilinear over the induced map on ring stalks. -/
noncomputable def stalkQuotientMapAlongₛₗ :
    (ToType (TopCat.Presheaf.stalk A₁.obj (f y)) ⧸ stalkKernelIdeal φ₁.hom (f y))
        →ₛₗ[stalkRingMapAlong f ψ y]
      (ToType (TopCat.Presheaf.stalk A₂.obj y) ⧸ stalkKernelIdeal φ₂.hom y) where
  toFun := Ideal.quotientMap (stalkKernelIdeal φ₂.hom y) (stalkRingMapAlong f ψ y)
    (stalkKernelIdeal_le_comap_stalkRingMapAlong f B φ₁ φ₂ ψ y hψ)
  map_add' := map_add _
  map_smul' r z := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk _ (stalkRingMapAlong f ψ y (r * z)) = _
    rw [map_mul]
    rfl

include hψ in
/-- **The induced map on the stalks of the quotients is bijective** as soon as the induced map
on ring stalks is: a ring isomorphism matching two ideals matches their quotients. -/
theorem bijective_stalkQuotientMapAlongₛₗ
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y)) :
    Function.Bijective (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ) := by
  refine Function.bijective_iff_has_inverse.2 ⟨Ideal.quotientMap _
    (RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm.toRingHom
    (stalkKernelIdeal_le_comap_stalkRingMapAlong_symm f B φ₁ φ₂ ψ y hψ hbij), ?_, ?_⟩
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact congrArg (Ideal.Quotient.mk (stalkKernelIdeal φ₁.hom (f y)))
      ((RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).symm_apply_apply z)
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact congrArg (Ideal.Quotient.mk (stalkKernelIdeal φ₂.hom y))
      ((RingEquiv.ofBijective (stalkRingMapAlong f ψ y) hbij).apply_symm_apply z)

include hψ in
/-- The induced map on the stalks of the quotients carries the germ of the class of a section of
`A₁` to the germ of the class of its image under `ψ`. -/
theorem stalkQuotientMapAlongₛₗ_germQuotient (U : Opens X) (hU : f y ∈ U)
    (b : A₁.obj.obj (op U) ⧸ kernelIdeal φ₁.hom (op U)) :
    stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ (germQuotientₛₗ φ₁.hom (f y) U hU b) =
      germQuotientₛₗ φ₂.hom y ((Opens.map f).obj U) hU
        (quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ (op U) b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (Ideal.Quotient.mk (stalkKernelIdeal φ₂.hom y))
    (stalkRingMapAlong_germ f ψ y U hU b)

/-! ### The map on the stalks of the sectionwise differentials induced by a change of
presentation along `f` -/

variable (R : TopCat.Sheaf CommRingCat.{u} X) (a₁ : R ⟶ A₁)
  (a₂ : (TopCat.Sheaf.pullback CommRingCat.{u} f).obj R ⟶ A₂)
  (ha : a₁ ≫ ψ =
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app R ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f).map a₂)

include ha in
/-- The stalk at `y` of the sectionwise differentials of `a₂`, as a cocone over the diagram of
the sections of the sectionwise differentials of `a₁` near `f y`. -/
noncomputable def omegaStalkCoconeAlong :
    Cocone ((OpenNhds.inclusion (f y)).op ⋙ (differentialsPresheaf a₁.hom).presheaf) where
  pt := AddCommGrpCat.of (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (differentialsPresheaf a₂.hom).presheaf y))
  ι :=
    { app := fun V => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun ω => (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj V.unop.1) y V.unop.2).hom
          (differentialsMapAlong f ψ R a₁ a₂ ha (op V.unop.1) ω))
        (fun ω ω' => (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj V.unop.1) y V.unop.2).hom
            (map_add (differentialsMapAlong f ψ R a₁ a₂ ha (op V.unop.1)) ω ω')).trans
          (map_add _ _ _)))
      naturality := by
        intro V W g
        ext ω
        refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj W.unop.1) y W.unop.2).hom
          (differentialsMapAlong_naturality f ψ R a₁ a₂ ha
            ((OpenNhds.inclusion (f y)).op.map g) ω)) ?_
        exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₂.hom).presheaf
          ((Opens.map f).map ((OpenNhds.inclusion (f y)).map g.unop)) y W.unop.2 _ }

include ha in
/-- The map `(Ω[A₁/R])_{f y} → (Ω[A₂/f⁻¹R])_y` on the stalks of the sectionwise differentials
induced by `ψ`. -/
noncomputable def omegaStalkHomAlong :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₁.hom).presheaf (f y)) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf y) :=
  (colimit.desc _ (omegaStalkCoconeAlong f ψ y R a₁ a₂ ha)).hom

include ha in
/-- The induced map on the stalks of the sectionwise differentials carries the germ at `f y` of
a section `ω` to the germ at `y` of its image. -/
theorem omegaStalkHomAlong_germ (U : Opens X) (hU : f y ∈ U)
    (ω : (differentialsPresheaf a₁.hom).obj (op U)) :
    omegaStalkHomAlong f ψ y R a₁ a₂ ha
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₁.hom).presheaf U (f y) hU).hom ω) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj U) y hU).hom
        (differentialsMapAlong f ψ R a₁ a₂ ha (op U) ω) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (omegaStalkCoconeAlong f ψ y R a₁ a₂ ha)
      (op (⟨U, hU⟩ : OpenNhds (f y)))) ω


include ha in
/-- The induced map on the stalks of the sectionwise differentials is semilinear over the
induced map on ring stalks. -/
theorem omegaStalkHomAlong_smul (r : ToType (TopCat.Presheaf.stalk A₁.obj (f y)))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (differentialsPresheaf a₁.hom).presheaf (f y))) :
    omegaStalkHomAlong f ψ y R a₁ a₂ ha (r • ξ) =
      stalkRingMapAlong f ψ y r • omegaStalkHomAlong f ψ y R a₁ a₂ ha ξ := by
  obtain ⟨Ur, hr, r₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq A₁.obj r
  obtain ⟨Uw, hw, ω₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (differentialsPresheaf a₁.hom).presheaf ξ
  have hU : f y ∈ Ur ⊓ Uw := ⟨hr, hw⟩
  have er := TopCat.Presheaf.germ_res_apply A₁.obj
    (homOfLE (inf_le_left : Ur ⊓ Uw ≤ Ur)) (f y) hU r₁
  have ew := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    (differentialsPresheaf a₁.hom).presheaf (homOfLE (inf_le_right : Ur ⊓ Uw ≤ Uw)) (f y) hU ω₁
  rw [← er, ← ew]
  refine Eq.trans (congrArg (omegaStalkHomAlong f ψ y R a₁ a₂ ha)
    (PresheafOfModules.germ_smul (differentialsPresheaf a₁.hom) (f y) (Ur ⊓ Uw) hU _ _).symm) ?_
  refine (omegaStalkHomAlong_germ f ψ y R a₁ a₂ ha (Ur ⊓ Uw) hU _).trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj (Ur ⊓ Uw)) y hU).hom
    (map_smulₛₗ (differentialsMapAlong f ψ R a₁ a₂ ha (op (Ur ⊓ Uw))) _ _)) ?_
  refine (PresheafOfModules.germ_smul (differentialsPresheaf a₂.hom) y
    ((Opens.map f).obj (Ur ⊓ Uw)) hU _ _).trans ?_
  refine congrArg₂ (· • ·) (stalkRingMapAlong_germ f ψ y (Ur ⊓ Uw) hU _).symm ?_
  exact (omegaStalkHomAlong_germ f ψ y R a₁ a₂ ha (Ur ⊓ Uw) hU _).symm

include ha in
/-- **The map on the stalks of the sectionwise differentials induced by `ψ`**, semilinear over
the induced map on ring stalks. -/
noncomputable def stalkOmegaMapAlongₛₗ :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₁.hom).presheaf (f y)) →ₛₗ[stalkRingMapAlong f ψ y]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf y) where
  toFun := omegaStalkHomAlong f ψ y R a₁ a₂ ha
  map_add' := map_add _
  map_smul' := omegaStalkHomAlong_smul f ψ y R a₁ a₂ ha


include ha in
/-- **The induced map on ring stalks is compatible with the two structural morphisms**:
composing it with the stalk of `a₁` is composing the stalk of `a₂` with the isomorphism
`R_{f y} ≅ (f⁻¹R)_y` of the stalks of the base. -/
theorem stalkRingMapAlong_comp_structureMap (r : ToType (TopCat.Presheaf.stalk R.obj (f y))) :
    stalkRingMapAlong f ψ y
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map a₁.hom).hom r) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map a₂.hom).hom
        (Stacks.InverseImageStalk.ringStalkHom f R y r) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
  refine Eq.trans (congrArg (stalkRingMapAlong f ψ y)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f y) hU a₁.hom s)) ?_
  refine (stalkRingMapAlong_germ f ψ y U hU _).trans ?_
  refine Eq.symm (Eq.trans (congrArg
    (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map a₂.hom).hom)
    (Stacks.InverseImageStalk.ringStalkEquiv_germ f R y U hU s)) ?_)
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj U) y hU a₂.hom _).trans ?_
  refine congrArg (TopCat.Presheaf.germ A₂.obj ((Opens.map f).obj U) y hU).hom ?_
  exact congrArg (fun t : R.obj.obj (op U) ⟶ A₂.obj.obj ((Opens.map f).op.obj (op U)) => t.hom s)
    (differentialsSquareAlong f ψ R a₁ a₂ ha (op U))


include ha in
/-- The induced map on the stalks of the sectionwise differentials, on germs. -/
theorem stalkOmegaMapAlongₛₗ_germ (U : Opens X) (hU : f y ∈ U)
    (ω : (differentialsPresheaf a₁.hom).obj (op U)) :
    stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₁.hom).presheaf U (f y) hU).hom ω) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj U) y hU).hom
        (differentialsMapAlong f ψ R a₁ a₂ ha (op U) ω) :=
  omegaStalkHomAlong_germ f ψ y R a₁ a₂ ha U hU ω

include ha in
/-- **The induced map on the stalks of the sectionwise differentials is bijective** as soon as
the induced map on ring stalks is. Under the identification of the stalk of the sectionwise
differentials with the differentials of the stalk map it is the map induced by a square of ring
isomorphisms, since the map on the stalks of the base is one. -/
theorem bijective_stalkOmegaMapAlongₛₗ
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y)) :
    Function.Bijective (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha) := by
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds (f y))) := Classical.decEq _
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds y)) := Classical.decEq _
  let := Stacks.RelativeDifferentialStalk.algebraStalk a₁.hom (f y)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a₂.hom y
  set e₁ := Stacks.RelativeDifferentialStalk.stalkLinearEquiv a₁.hom (f y) with he₁
  set e₂ := Stacks.RelativeDifferentialStalk.stalkLinearEquiv a₂.hom y with he₂
  have hadd : ∀ x z, e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha (e₁.symm (x + z))) =
      e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha (e₁.symm x)) +
        e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha (e₁.symm z)) := fun x z => by
    rw [map_add, map_add, map_add]
  have hsmul : ∀ (s : ToType (TopCat.Presheaf.stalk A₁.obj (f y))) ω,
      e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha (e₁.symm (s • ω))) =
        stalkRingMapAlong f ψ y s •
          e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha (e₁.symm ω)) := by
    intro s ω
    refine Eq.trans (congrArg (fun ζ => e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha ζ))
      (map_smul e₁.symm s ω)) ?_
    refine Eq.trans (congrArg e₂
      (map_smulₛₗ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha) s (e₁.symm ω))) ?_
    exact map_smul e₂ _ _
  have hT : ∀ s : ToType (TopCat.Presheaf.stalk A₁.obj (f y)),
      e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha
          (e₁.symm (KaehlerDifferential.D _ _ s))) =
        KaehlerDifferential.D _ _ (stalkRingMapAlong f ψ y s) := by
    intro s
    obtain ⟨U, hU, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq A₁.obj s
    have h₁ : e₁.symm (KaehlerDifferential.D _ _
          ((TopCat.Presheaf.germ A₁.obj U (f y) hU).hom s₀)) =
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₁.hom).presheaf U (f y) hU).hom
          (CommRingCat.KaehlerDifferential.d (f := a₁.hom.app (op U)) s₀) :=
      (LinearEquiv.symm_apply_eq _).mpr
        (Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D a₁.hom (f y)
          (OrderDual.toDual (⟨U, hU⟩ : TopologicalSpace.OpenNhds (f y))) s₀).symm
    refine Eq.trans (congrArg (fun ζ => e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha ζ)) h₁) ?_
    refine Eq.trans (congrArg e₂ (stalkOmegaMapAlongₛₗ_germ f ψ y R a₁ a₂ ha U hU _)) ?_
    refine Eq.trans (congrArg (fun ω : (differentialsPresheaf a₂.hom).obj
        ((Opens.map f).op.obj (op U)) => e₂ ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj U) y hU).hom ω))
      (differentialsMapAlong_d f ψ R a₁ a₂ ha (op U) s₀)) ?_
    refine Eq.trans (Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D a₂.hom y
      (OrderDual.toDual (⟨(Opens.map f).obj U, hU⟩ : TopologicalSpace.OpenNhds y)) _) ?_
    exact congrArg (KaehlerDifferential.D _ _) (stalkRingMapAlong_germ f ψ y U hU s₀).symm
  exact .of_equivLike_comp_eq e₁.symm (Equiv.refl _) e₂
    (Stacks.KaehlerDifferentialSquare.bijective_of_map_D
      (T := fun ω => e₂ (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha (e₁.symm ω)))
      (stalkRingMapAlong_comp_structureMap f ψ y R a₁ a₂ ha)
      (Stacks.InverseImageStalk.ringStalkEquiv f R y).bijective hbij hadd hsmul hT)
    fun _ => rfl

/-! ### Germs of conormal classes in a stalk of a conormal sheaf -/

section ConormalStalkGerms

variable {Z : TopCat.{u}} {A' B' : TopCat.Sheaf CommRingCat.{u} Z} (φ : A' ⟶ B')
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z) φ.hom] (x : Z)

/-- **Every element of the stalk of the conormal sheaf is the germ of a conormal class.** The
stalk is the conormal module of the kernel on stalks, and every element of that is the conormal
class of a germ. -/
theorem exists_germ_toAssociatedModule_toCotangent_eq
    (ξ : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Z) A' B' φ).val.presheaf x)) :
    ∃ (U : Opens Z) (hx : x ∈ U) (s : kernelIdeal φ.hom (op U)),
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Z) A' B' φ).val.presheaf
        U x hx).hom
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Z) A' B' φ
          (conormalPresheaf φ.hom) (op U)
          ((kernelIdeal φ.hom (op U)).toCotangent s)) = ξ := by
  obtain ⟨d, hd⟩ := (stalkKernelIdeal φ.hom x).toCotangent_surjective
    (conormalSheafStalkLinearEquiv A' B' φ x ξ)
  obtain ⟨U, hx, s, hs, hgs⟩ := exists_germ_eq_of_mem_stalkKernelIdeal φ.hom x
    (d : ↑(TopCat.Presheaf.stalk A'.obj x)) d.2
  refine ⟨U, hx, ⟨s, hs⟩, (conormalSheafStalkLinearEquiv A' B' φ x).injective ?_⟩
  refine (conormalSheafStalkLinearEquiv_germ_toAssociatedModule A' B' φ x U hx ⟨s, hs⟩).trans ?_
  exact Eq.trans (congrArg (stalkKernelIdeal φ.hom x).toCotangent (Subtype.ext hgs)) hd

end ConormalStalkGerms

/-! ### The comparison of conormal sheaves along `f` is an isomorphism -/

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom]

include hψ in
/-- **The comparison of conormal sheaves along `f`**, in untransposed form:
`f⁻¹(I₁/I₁²) ⟶ I₂/I₂²`. -/
noncomputable def inverseImageConormalMapAlong :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁) ⟶
      conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ :=
  ((inverseImageAdjunction f B).homEquiv _ _).symm (conormalSheafMapAlong f B φ₁ φ₂ ψ hψ)

include hψ in
/-- **The comparison of conormal sheaves on stalks, on germs of conormal classes.** Composed
with the identification of the stalk of an inverse image, it carries the germ at `f y` of the
conormal class of a section `s` of `I₁` to the germ at `y` of the conormal class of `ψ s`. -/
theorem stalkMap_inverseImageConormalMapAlong_germ
    (U : Opens X) (hU : f y ∈ U) (s : kernelIdeal φ₁.hom (op U)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (inverseImageConormalMapAlong f B φ₁ φ₂ ψ hψ)).hom
        (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
          (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁)
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁).val.presheaf
            U (f y) hU).hom
            (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
              (conormalPresheaf φ₁.hom) (op U)
              ((kernelIdeal φ₁.hom (op U)).toCotangent s)))) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂).val.presheaf
        ((Opens.map f).obj U) y hU).hom
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ (conormalPresheaf φ₂.hom)
          ((Opens.map f).op.obj (op U))
          ((kernelIdeal φ₂.hom ((Opens.map f).op.obj (op U))).toCotangent
            ⟨(sectionsMapAlong f ψ (op U)).hom s,
              kernelIdeal_le_comap_sectionsMapAlong f B φ₁ φ₂ ψ hψ (op U) s.2⟩)) := by
  refine (stalkMap_homEquiv_symm_inverseImageModuleStalkEquiv_germ f B y
    (conormalSheafMapAlong f B φ₁ φ₂ ψ hψ) U hU _).trans (congrArg _ ?_)
  refine (conormalSheafMapAlong_toAssociatedModule f B φ₁ φ₂ ψ hψ (op U) _).trans ?_
  exact congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ (conormalPresheaf φ₂.hom)
      ((Opens.map f).op.obj (op U)))
    (cotangentMap_toCotangent _ _ _ _ s)

include hψ in
/-- **Under the two identifications of stalks the comparison of conormal sheaves is the map on
conormal modules induced by the map on ring stalks.** Conormal classes generate the stalk, so
this determines the comparison on stalks. -/
theorem conormalSheafStalkLinearEquiv_stalkMap_inverseImageConormalMapAlong
    (c : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁).val.presheaf (f y))) :
    conormalSheafStalkLinearEquiv A₂ ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ y
        ((AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (inverseImageConormalMapAlong f B φ₁ φ₂ ψ hψ)).hom
          (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
            (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁) c)) =
      cotangentMap (stalkKernelIdeal φ₁.hom (f y)) (stalkKernelIdeal φ₂.hom y)
          (stalkRingMapAlong f ψ y)
          (stalkKernelIdeal_le_comap_stalkRingMapAlong f B φ₁ φ₂ ψ y hψ)
        (conormalSheafStalkLinearEquiv A₁ B φ₁ (f y) c) := by
  obtain ⟨U, hU, s, rfl⟩ := exists_germ_toAssociatedModule_toCotangent_eq φ₁ (f y) c
  refine Eq.trans (congrArg (conormalSheafStalkLinearEquiv A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ y)
    (stalkMap_inverseImageConormalMapAlong_germ f B φ₁ φ₂ ψ y hψ U hU s)) ?_
  refine Eq.trans (conormalSheafStalkLinearEquiv_germ_toAssociatedModule A₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ y ((Opens.map f).obj U) hU _) ?_
  refine Eq.symm (Eq.trans (congrArg (cotangentMap (stalkKernelIdeal φ₁.hom (f y))
      (stalkKernelIdeal φ₂.hom y) (stalkRingMapAlong f ψ y)
      (stalkKernelIdeal_le_comap_stalkRingMapAlong f B φ₁ φ₂ ψ y hψ))
    (conormalSheafStalkLinearEquiv_germ_toAssociatedModule A₁ B φ₁ (f y) U hU s)) ?_)
  refine (cotangentMap_toCotangent _ _ _ _ _).trans ?_
  exact congrArg (stalkKernelIdeal φ₂.hom y).toCotangent
    (Subtype.ext (stalkRingMapAlong_germ f ψ y U hU s))

include hψ in
/-- **The comparison of conormal sheaves along `f` is bijective on the stalk at `y`** as soon as
the induced map on ring stalks at `y` is bijective. -/
theorem bijective_stalkMap_inverseImageConormalMapAlong
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y)) :
    Function.Bijective (AlgebraicGeometry.SheafOfModules.stalkMap
      (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
      (inverseImageConormalMapAlong f B φ₁ φ₂ ψ hψ)).hom :=
  .of_equivLike_comp_eq
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
      (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁))
    (conormalSheafStalkLinearEquiv A₁ B φ₁ (f y))
    (conormalSheafStalkLinearEquiv A₂ ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ y)
    (bijective_cotangentMap_stalkRingMapAlong f B φ₁ φ₂ ψ y hψ hbij)
    (conormalSheafStalkLinearEquiv_stalkMap_inverseImageConormalMapAlong f B φ₁ φ₂ ψ y hψ)

include hψ in
/-- **The comparison of conormal sheaves along `f` is an isomorphism** as soon as the induced
map on ring stalks is bijective at every point of `Y`: isomorphy of a morphism of sheaves of
modules is detected on stalks. -/
theorem isIso_inverseImageConormalMapAlong
    (hbij : ∀ w : Y, Function.Bijective (stalkRingMapAlong f ψ w)) :
    IsIso (inverseImageConormalMapAlong f B φ₁ φ₂ ψ hψ) :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (inverseImageConormalMapAlong f B φ₁ φ₂ ψ hψ)).2
    fun w => bijective_stalkMap_inverseImageConormalMapAlong f B φ₁ φ₂ ψ w hψ (hbij w)

/-! ### The comparison of the scalar extensions of the differentials along `f` is an
isomorphism -/

include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f`**, in untransposed
form: `f⁻¹(B ⊗[A₁] Ω[A₁/R]) ⟶ f⁻¹B ⊗[A₂] Ω[A₂/f⁻¹R]`. -/
noncomputable def inverseImageTensorMapAlong :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁) ⟶
      tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ :=
  ((inverseImageAdjunction f B).homEquiv _ _).symm
    (tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha)

include hψ ha in
/-- **The comparison of the scalar extensions on stalks, on germs of sections of the tensor
presheaf.** Composed with the identification of the stalk of an inverse image, it carries the
germ at `f y` of a tensor `t` to the germ at `y` of the image of `t`. -/
theorem stalkMap_inverseImageTensorMapAlong_germ
    (U : Opens X) (hU : f y ∈ U) (t : (tensorPresheaf φ₁.hom a₁.hom).obj (op U)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (inverseImageTensorMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha)).hom
        (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
          (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁)
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁
              φ₁).val.presheaf U (f y) hU).hom
            (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
              (tensorPresheaf φ₁.hom a₁.hom) (op U) t))) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂).val.presheaf
        ((Opens.map f).obj U) y hU).hom
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ (tensorPresheaf φ₂.hom a₂.hom)
          ((Opens.map f).op.obj (op U))
          (tensorMapAlongₛₗ f B φ₁ φ₂ ψ hψ R a₁ a₂ ha (op U) t)) := by
  refine (stalkMap_homEquiv_symm_inverseImageModuleStalkEquiv_germ f B y
    (tensorSheafMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha) U hU _).trans (congrArg _ ?_)
  exact tensorSheafMapAlong_toAssociatedModule f B φ₁ φ₂ ψ hψ R a₁ a₂ ha (op U) t

include hψ ha in
/-- **Under the identifications of the stalks the comparison of the scalar extensions of the
differentials is the tensor product of the map on the stalks of the quotients with the map on
the stalks of the differentials.** -/
theorem tensorDifferentialsSheafStalkPresheafLinearEquiv_stalkMap_inverseImageTensorMapAlong
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁
        φ₁).val.presheaf (f y))) :
    tensorDifferentialsSheafStalkPresheafLinearEquiv
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y
        ((AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (inverseImageTensorMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha)).hom
          (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
            (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁)
            ξ)) =
      TensorProduct.map (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ)
          (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha)
        (tensorDifferentialsSheafStalkPresheafLinearEquiv R A₁ B a₁ φ₁ (f y) ξ) := by
  obtain ⟨U, hU, ω, rfl⟩ := exists_germ_one_tmul_eq R A₁ B a₁ φ₁ (f y) ξ
  refine Eq.trans (congrArg (tensorDifferentialsSheafStalkPresheafLinearEquiv
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y)
    (stalkMap_inverseImageTensorMapAlong_germ f B φ₁ φ₂ ψ y hψ R a₁ a₂ ha U hU _)) ?_
  refine Eq.trans (tensorDifferentialsSheafStalkPresheafLinearEquiv_germ_toAssociatedModule
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y ((Opens.map f).obj U) hU _) ?_
  refine Eq.trans (congrArg (germTensorₛₗ φ₂.hom a₂.hom y ((Opens.map f).obj U) hU)
    (TensorProduct.map_tmul (quotientMapAlongₛₗ f B φ₁ φ₂ ψ hψ (op U))
      (differentialsMapAlong f ψ R a₁ a₂ ha (op U)) 1 ω)) ?_
  refine Eq.trans (TensorProduct.map_tmul (germQuotientₛₗ φ₂.hom y ((Opens.map f).obj U) hU)
    (germOmegaₛₗ a₂.hom y ((Opens.map f).obj U) hU) _ _) ?_
  refine Eq.symm (Eq.trans (congrArg (TensorProduct.map
      (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ) (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha))
    ((tensorDifferentialsSheafStalkPresheafLinearEquiv_germ_toAssociatedModule R A₁ B a₁ φ₁
      (f y) U hU _).trans
      (TensorProduct.map_tmul (germQuotientₛₗ φ₁.hom (f y) U hU)
        (germOmegaₛₗ a₁.hom (f y) U hU) 1 ω))) ?_)
  refine Eq.trans (TensorProduct.map_tmul (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ)
    (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha) _ _) ?_
  exact congrArg₂ (fun (q : ToType (TopCat.Presheaf.stalk A₂.obj y) ⧸ stalkKernelIdeal φ₂.hom y)
      (η : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf y)) =>
      q ⊗ₜ[ToType (TopCat.Presheaf.stalk A₂.obj y)] η)
    (stalkQuotientMapAlongₛₗ_germQuotient f B φ₁ φ₂ ψ y hψ U hU 1)
    (stalkOmegaMapAlongₛₗ_germ f ψ y R a₁ a₂ ha U hU ω)


include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f` is bijective on the
stalk at `y`** as soon as the induced map on ring stalks at `y` is bijective. -/
theorem bijective_stalkMap_inverseImageTensorMapAlong
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y)) :
    Function.Bijective (AlgebraicGeometry.SheafOfModules.stalkMap
      (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
      (inverseImageTensorMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha)).hom :=
  .of_equivLike_comp_eq
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
      (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁))
    (tensorDifferentialsSheafStalkPresheafLinearEquiv R A₁ B a₁ φ₁ (f y))
    (tensorDifferentialsSheafStalkPresheafLinearEquiv
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj R) A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y)
    (TensorProduct.bijective_map hbij (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ)
      (stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha)
      (bijective_stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ hbij)
      (bijective_stalkOmegaMapAlongₛₗ f ψ y R a₁ a₂ ha hbij))
    (tensorDifferentialsSheafStalkPresheafLinearEquiv_stalkMap_inverseImageTensorMapAlong
      f B φ₁ φ₂ ψ y hψ R a₁ a₂ ha)

include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f` is an
isomorphism** as soon as the induced map on ring stalks is bijective at every point of `Y`. -/
theorem isIso_inverseImageTensorMapAlong
    (hbij : ∀ w : Y, Function.Bijective (stalkRingMapAlong f ψ w)) :
    IsIso (inverseImageTensorMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha) :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (inverseImageTensorMapAlong f B φ₁ φ₂ ψ hψ R a₁ a₂ ha)).2
    fun w => bijective_stalkMap_inverseImageTensorMapAlong f B φ₁ φ₂ ψ w hψ R a₁ a₂ ha (hbij w)

/-! ### The degree `-1` component of the comparison chain map is an isomorphism -/

/-- The transpose of `Stacks.SheafOfModules.inverseImagePresentationHom` is the identification
`f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`. -/
theorem homEquiv_symm_inverseImagePresentationHom :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (freeAlgebraSheaf (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          (underlyingPresheaf (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)))).symm
        (inverseImagePresentationHom f A B) = (underlyingInverseImageIso f A B).hom :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv _ _).symm_apply_apply _

/-- **The stalks of the two polynomial algebras agree.** The map
`(A[B])_{f y} → ((f⁻¹A)[f⁻¹B])_y` induced by
`Stacks.SheafOfModules.inverseImagePresentationHom` is bijective, being the isomorphism
`(A[B])_{f y} ≅ (f⁻¹(A[B]))_y` of stalks along `f` followed by the stalk of the isomorphism
`f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`. -/
theorem bijective_stalkRingMapAlong_inverseImagePresentationHom (w : Y) :
    Function.Bijective (stalkRingMapAlong f (inverseImagePresentationHom f A B) w) := by
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} w).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (freeAlgebraSheaf (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
          (underlyingPresheaf (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)))).symm
        (inverseImagePresentationHom f A B)).hom) := by
    rw [homEquiv_symm_inverseImagePresentationHom]
    exact ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} w).mapIso
      ((TopCat.Sheaf.forget CommRingCat.{u} Y).mapIso
        (underlyingInverseImageIso f A B))).isIso_hom
  exact bijective_stalkRingMapAlong f (inverseImagePresentationHom f A B) w hiso

/-- **The degree `-1` component of the comparison chain map is an isomorphism**: the inverse
image of the conormal sheaf of the canonical presentation of `B` over `A` is the conormal sheaf
of the canonical presentation of `f⁻¹B` over `f⁻¹A`. -/
instance isIso_inverseImageConormalMap : IsIso (inverseImageConormalMap f A B a) :=
  isIso_inverseImageConormalMapAlong f B
    (canonicalPresentation (Opens.grothendieckTopology X) A B a)
    (canonicalPresentation (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))
    (inverseImagePresentationHom f A B)
    (inverseImagePresentationHom_comp_canonicalPresentation f A B a)
    (bijective_stalkRingMapAlong_inverseImagePresentationHom f A B)

/-- **The degree `-1` component of the comparison chain map
`f⁻¹ NL_{B/A} ⟶ NL_{f⁻¹B/f⁻¹A}` is an isomorphism.** -/
instance isIso_naiveCotangentComplexInverseImageMap_f_negOne :
    IsIso ((naiveCotangentComplexInverseImageMap f A B a).f (-1)) := by
  rw [naiveCotangentComplexInverseImageMap_f_negOne]
  exact IsIso.comp_isIso'
    ((_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).mapIso
      (eqToIso (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a))).isIso_hom
    (IsIso.comp_isIso' (isIso_inverseImageConormalMap f A B a)
      (eqToIso (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm).isIso_hom)


/-! ### The comparison chain map is an isomorphism -/

section Canonical

/-- **The degree `0` component of the comparison chain map is an isomorphism**: the inverse
image of the scalar extension of the differentials of the canonical presentation of `B` over `A`
is the corresponding scalar extension for the canonical presentation of `f⁻¹B` over `f⁻¹A`. -/
instance isIso_inverseImageTensorMap : IsIso (inverseImageTensorMap f A B a) :=
  isIso_inverseImageTensorMapAlong f B
    (canonicalPresentation (Opens.grothendieckTopology X) A B a)
    (canonicalPresentation (Opens.grothendieckTopology Y)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a))
    (inverseImagePresentationHom f A B)
    (inverseImagePresentationHom_comp_canonicalPresentation f A B a) A _ _
    (freeAlgebraSheafCoefficientMap_comp_inverseImagePresentationHom f A B)
    (bijective_stalkRingMapAlong_inverseImagePresentationHom f A B)

/-- **The degree `0` component of the comparison chain map
`f⁻¹ NL_{B/A} ⟶ NL_{f⁻¹B/f⁻¹A}` is an isomorphism.** -/
instance isIso_naiveCotangentComplexInverseImageMap_f_zero :
    IsIso ((naiveCotangentComplexInverseImageMap f A B a).f 0) := by
  rw [naiveCotangentComplexInverseImageMap_f_zero]
  exact IsIso.comp_isIso'
    ((_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).mapIso
      (eqToIso (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a))).isIso_hom
    (IsIso.comp_isIso' (isIso_inverseImageTensorMap f A B a)
      (eqToIso (naiveCotangentComplex_X_zero (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a)).symm).isIso_hom)

/-- **The comparison chain map `f⁻¹ NL_{B/A} ⟶ NL_{f⁻¹B/f⁻¹A}` is an isomorphism.** Both
complexes vanish outside the degrees `-1` and `0`, where the comparison is the isomorphism of
conormal sheaves and the isomorphism of the scalar extensions of the differentials. -/
@[stacks 08TM "invertibility of the canonical map"]
instance isIso_naiveCotangentComplexInverseImageMap :
    IsIso (naiveCotangentComplexInverseImageMap f A B a) := by
  have h : ∀ k : ℤ, IsIso ((naiveCotangentComplexInverseImageMap f A B a).f k) := by
    intro k
    by_cases h₁ : k = -1
    · subst h₁; infer_instance
    by_cases h₀ : k = 0
    · subst h₀; infer_instance
    refine ⟨0, ?_, ?_⟩
    · exact (Functor.map_isZero (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B))
        (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology X) A B a k h₁
          h₀)).eq_of_src _ _
    · exact (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a) k h₁ h₀).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The inverse image of the naive cotangent complex is the naive cotangent complex of the
inverse image**: `f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}`. -/
@[stacks 08TM]
noncomputable def naiveCotangentComplexInverseImageIso :
    ((_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a) ≅
      naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).map a) :=
  asIso (naiveCotangentComplexInverseImageMap f A B a)

end Canonical

end Stacks.SheafOfModules

end
