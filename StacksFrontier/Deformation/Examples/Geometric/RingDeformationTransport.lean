module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceInjection
public import StacksFrontier.Deformation.Smooth.Pi
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential

/-!
# Transporting a deformation category along an isomorphism of algebras

An isomorphism `R ≅ S` of `k`-algebras carries deformations of `R` to deformations of `S`: a flat
algebra over an Artinian base reducing to `R` reduces to `S` through the isomorphism. The
deformation category of a `k`-algebra is the slice category over the flat algebra `(k, R)`, so the
transport is `CategoryTheory.Over.map` along the induced isomorphism `(k, R) ≅ (k, S)`.

This file builds that based functor and proves that it preserves the two properties the chain of
**Stacks 0DZF** is about: it is smooth, and it is an isomorphism on tangent spaces; hence so is
any composite with it. That is what lets a statement proved at one presentation of a ring be read
at another — concretely, it carries the conclusions of **Stacks 0DZ5** and **Stacks 0DZD**, which
hold for `P` and the ideal `J = 𝔪 1 ∩ … ∩ 𝔪 n`, over to the completion and the henselization in
their decomposed forms `∏ P^∧_{𝔪 i}`, `∏ P^h_{𝔪 i}`, which is the step the proof of Stacks 0DZF
makes when it says "since `P^∧ = ∏ P^∧_{𝔪 i}`".

## Main definitions

* `Deformation.Examples.residueFieldAlgebraIso`: an isomorphism of `k`-algebras `R ≃ S` as an
  isomorphism of the flat algebras `(k, R) ≅ (k, S)` over the residue field.
* `Deformation.Examples.ringDeformationTransport`: the induced based functor `𝓓_R ⟶ 𝓓_S` over
  `𝒞_Λ`.

## Main results

* `Deformation.Examples.isSmooth_ringDeformationTransport`: the transport is smooth.
* `Deformation.Examples.bijective_differential_ringDeformationTransport`: the transport induces a
  bijection on tangent spaces.
* `Deformation.Examples.isSmooth_comp_ringDeformationTransport` and
  `Deformation.Examples.bijective_differential_comp_ringDeformationTransport`: both properties
  pass to a composite, which is the form in which a caller uses the transport.
* `Deformation.bijective_mapIsomorphismClasses_of_fiberwise`: a based functor whose fibre functors
  reflect isomorphy and are essentially surjective is bijective on fibrewise isomorphism classes.
  This is the general criterion the transport is an instance of.

## Implementation notes

The isomorphism is taken as a `RingEquiv` together with the equation saying it commutes with the
two structural maps from `k`, rather than as an `AlgEquiv`. Every isomorphism this file is applied
to arises as a ring isomorphism between two completions, henselizations or products of such, where
the `k`-algebra structures are the ones inherited from `P`; the commutation is then a statement
about elements, which is what a caller can discharge, while producing an `AlgEquiv` first would
require matching `Algebra` instances up to definitional equality.

The facts about `CategoryTheory.Over.map` along an isomorphism that the two proofs need — that a
morphism of images descends, and that every object of the target slice is the image of one of the
source slice up to an isomorphism which is the identity on carriers — are isolated in the first
section, stated for an arbitrary category. Inside the deformation category they would be stated
for `(ringDeformationBasedCategory Λ k R).obj`, whose unfolding to a slice category Lean does not
perform while elaborating `CategoryTheory.Over.w`.

Smoothness is proved from those two facts directly rather than through a general "an equivalence
over `𝒞_Λ` is smooth" lemma, of which the repository has only private instances.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
-/

@[expose] public section

open CategoryTheory

universe u w v₁ u₁ v₂ u₂

/-! ### Slices along an isomorphism -/

namespace CategoryTheory.Over

variable {T : Type u₂} [Category.{v₂} T] {X Y : T} (h : X ≅ Y)

/-- **A morphism between images under `Over.map` of an isomorphism descends.** The underlying
morphism is the same; its compatibility with the structural morphisms to `X` follows from the one
over `Y` because an isomorphism may be cancelled on the right. -/
public def mapIsoPreimage {U V : Over X}
    (m : (Over.map h.hom).obj U ⟶ (Over.map h.hom).obj V) : U ⟶ V :=
  Over.homMk m.left <| (Iso.cancel_iso_hom_right _ _ h).mp <| by simpa using Over.w m

/-- The underlying morphism of `CategoryTheory.Over.mapIsoPreimage h m` is that of `m`. -/
@[simp]
public theorem mapIsoPreimage_left {U V : Over X}
    (m : (Over.map h.hom).obj U ⟶ (Over.map h.hom).obj V) :
    (mapIsoPreimage h m).left = m.left :=
  rfl

/-- The image of `CategoryTheory.Over.mapIsoPreimage h m` under `Over.map h.hom` is `m`. -/
@[simp]
public theorem map_mapIsoPreimage {U V : Over X}
    (m : (Over.map h.hom).obj U ⟶ (Over.map h.hom).obj V) :
    (Over.map h.hom).map (mapIsoPreimage h m) = m :=
  Over.OverMorphism.ext rfl

/-- The object of `Over X` whose image under `Over.map h.hom` is isomorphic to a given object of
`Over Y`: compose its structural morphism with the inverse isomorphism. -/
public def mapIsoSection (V : Over Y) : Over X :=
  Over.mk (V.hom ≫ h.inv)

/-- The underlying object of `CategoryTheory.Over.mapIsoSection h V` is that of `V`. -/
@[simp]
public theorem mapIsoSection_left (V : Over Y) : (mapIsoSection h V).left = V.left :=
  rfl

/-- **Every object of the target slice is the image of one of the source slice**, by an
isomorphism which is the identity on the underlying object. -/
public def mapIsoSectionIso (V : Over Y) :
    (Over.map h.hom).obj (mapIsoSection h V) ≅ V :=
  Over.isoMk (Iso.refl _) (by simp [mapIsoSection])

/-- The forward morphism of `CategoryTheory.Over.mapIsoSectionIso h V` is the identity on the
underlying object. -/
@[simp]
public theorem mapIsoSectionIso_hom_left (V : Over Y) :
    (mapIsoSectionIso h V).hom.left = 𝟙 V.left :=
  rfl

/-- The inverse morphism of `CategoryTheory.Over.mapIsoSectionIso h V` is the identity on the
underlying object. -/
@[simp]
public theorem mapIsoSectionIso_inv_left (V : Over Y) :
    (mapIsoSectionIso h V).inv.left = 𝟙 V.left :=
  rfl

end CategoryTheory.Over

namespace Deformation

/-! ### Bijectivity on isomorphism classes from the fibres -/

/-- **A based functor is bijective on fibrewise isomorphism classes as soon as its fibre functor
reflects isomorphy and is essentially surjective.** Injectivity is the first hypothesis read
through `Deformation.classOf_eq_iff_nonempty_iso`, surjectivity the second read through
`Deformation.classOf_surjective`. -/
public theorem bijective_mapIsomorphismClasses_of_fiberwise
    {C : Type u₁} [Category.{v₁} C]
    {𝓕 : BasedCategory C} {𝓖 : BasedCategory C}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (A : C)
    (hrefl : ∀ x y : 𝓕.p.Fiber A,
      Nonempty ((fiberFunctor φ A).obj x ≅ (fiberFunctor φ A).obj y) → Nonempty (x ≅ y))
    (hess : ∀ z : 𝓖.p.Fiber A, ∃ x : 𝓕.p.Fiber A, Nonempty ((fiberFunctor φ A).obj x ≅ z)) :
    Function.Bijective (mapIsomorphismClasses h𝓕 h𝓖 φ A) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := classOf_surjective 𝓕 h𝓕 A a
    obtain ⟨y, rfl⟩ := classOf_surjective 𝓕 h𝓕 A b
    rw [mapIsomorphismClasses_classOf, mapIsomorphismClasses_classOf] at hab
    exact (classOf_eq_iff_nonempty_iso h𝓕 x y).mpr
      (hrefl x y ((classOf_eq_iff_nonempty_iso h𝓖 _ _).mp hab))
  · intro b
    obtain ⟨z, rfl⟩ := classOf_surjective 𝓖 h𝓖 A b
    obtain ⟨x, hx⟩ := hess z
    exact ⟨classOf 𝓕 h𝓕 x, by
      rw [mapIsomorphismClasses_classOf]
      exact (classOf_eq_iff_nonempty_iso h𝓖 _ _).mpr hx⟩

end Deformation

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {R S : Type w} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-! ### An isomorphism of algebras as an isomorphism of flat algebras over the residue field -/

/-- The underlying map of commutative rings of a ring isomorphism of the fibres. -/
public noncomputable abbrev transportMap (e : R ≃+* S) :
    CommRingCat.of R ⟶ CommRingCat.of S :=
  CommRingCat.ofHom (e : R →+* S)

/-- The map of commutative rings underlying a ring isomorphism is an isomorphism. -/
public instance isIso_transportMap (e : R ≃+* S) : IsIso (transportMap e) :=
  ⟨CommRingCat.ofHom (e.symm : S →+* R), by ext x; simp, by ext x; simp⟩

/-- A commuting square whose left-hand vertical side is an identity and whose upper horizontal
side is an isomorphism is a pushout square. -/
public theorem isPushout_id_of_isIso {A B C : CommRingCat.{w}} (f : A ⟶ B) (g : A ⟶ C)
    (i : B ⟶ C) [IsIso i] (h : f ≫ i = g) : IsPushout f (𝟙 A) i g :=
  IsPushout.of_vert_isIso ⟨by simpa using h⟩

/-- **An isomorphism of `k`-algebras is an isomorphism of the flat algebras over the residue
field.** Both flat algebras have base the residue field `k`; the morphism is the identity on the
base and the given isomorphism on the fibre, and the square of rings is a pushout because the two
vertical sides of it are isomorphisms. -/
public noncomputable def residueFieldAlgebraIso (e : R ≃+* S)
    (he : ∀ a : k, e (algebraMap k R a) = algebraMap k S a) :
    residueFieldAlgebra (Λ := Λ) (k := k) R ≅ residueFieldAlgebra (Λ := Λ) (k := k) S where
  hom :=
    { base := 𝟙 _
      map := transportMap e
      cartesian := isPushout_id_of_isIso _ _ (transportMap e) (by ext a; exact he a) }
  inv :=
    { base := 𝟙 _
      map := transportMap e.symm
      cartesian := isPushout_id_of_isIso _ _ (transportMap e.symm)
        (by ext a; exact e.symm_apply_eq.mpr (he a).symm) }
  hom_inv_id := by
    apply FlatAlgebraCategory.Hom.ext
    · exact Category.comp_id _
    · ext x
      exact e.symm_apply_apply x
  inv_hom_id := by
    apply FlatAlgebraCategory.Hom.ext
    · exact Category.comp_id _
    · ext x
      exact e.apply_symm_apply x

/-! ### The transport of deformation categories -/

/-- **Transport of deformations along an isomorphism of algebras.** The deformation category of a
`k`-algebra is the slice category over the flat algebra `(k, R)`, so an isomorphism
`(k, R) ≅ (k, S)` induces a functor on the slices by composing the structural morphism with it.
It is a functor over `𝒞_Λ` because the slice functor does not change the underlying flat algebra,
hence not its Artinian base. -/
public noncomputable def ringDeformationTransport (e : R ≃+* S)
    (he : ∀ a : k, e (algebraMap k R a) = algebraMap k S a) :
    BasedFunctor (ringDeformationBasedCategory Λ k R) (ringDeformationBasedCategory Λ k S) where
  toFunctor := Over.map (residueFieldAlgebraIso (Λ := Λ) e he).hom
  w := rfl

section Transport

variable (e : R ≃+* S) (he : ∀ a : k, e (algebraMap k R a) = algebraMap k S a)

/-- The comparison isomorphism `(k, R) ≅ (k, S)` the transport is `CategoryTheory.Over.map`
along. -/
private noncomputable abbrev transportIso :
    residueFieldAlgebra (Λ := Λ) (k := k) R ≅ residueFieldAlgebra (Λ := Λ) (k := k) S :=
  residueFieldAlgebraIso (Λ := Λ) e he

/-- The comparison isomorphism of `CategoryTheory.Over.mapIsoSectionIso` is vertical in both
directions. -/
private theorem isHomLift_id_mapIsoSectionIso {B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (z : (ringDeformationBasedCategory Λ k S).obj)
    (hz : (ringDeformationBasedCategory Λ k S).p.obj z = B) :
    (ringDeformationBasedCategory Λ k S).p.IsHomLift (𝟙 B)
      (Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) z).hom ∧
    (ringDeformationBasedCategory Λ k S).p.IsHomLift (𝟙 B)
      (Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) z).inv :=
  by
  subst hz
  exact ⟨IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl),
    IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl)⟩

/-- A morphism between images under the transport lying over `f` descends to one over `f`. -/
private theorem isHomLift_mapIsoPreimage {B B' : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ B')
    {x y : (ringDeformationBasedCategory Λ k R).obj}
    (m : (ringDeformationTransport (Λ := Λ) e he).obj x ⟶
      (ringDeformationTransport (Λ := Λ) e he).obj y)
    (hm : (ringDeformationBasedCategory Λ k S).p.IsHomLift f m) :
    (ringDeformationBasedCategory Λ k R).p.IsHomLift f
      (Over.mapIsoPreimage (transportIso (Λ := Λ) e he) m) := by
  have : (ringDeformationBasedCategory Λ k S).p.IsHomLift f
      ((ringDeformationTransport (Λ := Λ) e he).map
        (Over.mapIsoPreimage (transportIso (Λ := Λ) e he) m)) := by
    rw [show (ringDeformationTransport (Λ := Λ) e he).map
        (Over.mapIsoPreimage (transportIso (Λ := Λ) e he) m) = m from
      Over.map_mapIsoPreimage _ _]
    exact hm
  exact BasedFunctor.isHomLift_map (ringDeformationTransport (Λ := Λ) e he) f _

/-! #### Smoothness -/

/-- **The transport of deformations along an isomorphism of algebras is smooth.** A lifting
problem for the transport is solved by the preimage of the target deformation: the comparison
isomorphism of `CategoryTheory.Over.mapIsoSectionIso` is the identity on the underlying flat
algebra, hence vertical, and the lift itself is the descent of its composite with the given
morphism. -/
public theorem isSmooth_ringDeformationTransport :
    IsSmooth (ringDeformationTransport (Λ := Λ) (k := k) e he) := by
  intro B A f _ y x g hg
  have hyB : y.left.base = B :=
    IsHomLift.domain_eq (ringDeformationBasedCategory Λ k S).p f g
  obtain ⟨ha, -⟩ := isHomLift_id_mapIsoSectionIso e he y hyB
  refine ⟨Over.mapIsoSection (transportIso (Λ := Λ) e he) y,
    Over.mapIsoPreimage (transportIso (Λ := Λ) e he)
      ((Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) y).hom ≫ g),
    (Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) y).hom, ?_,
    ha, ?_⟩
  · have h₁ : (ringDeformationBasedCategory Λ k S).p.IsHomLift f
        ((Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) y).hom ≫ g) :=
      IsHomLift.comp_lift_id_left' (ringDeformationBasedCategory Λ k S).p B _ f g
    exact isHomLift_mapIsoPreimage e he f _ h₁
  · exact Over.map_mapIsoPreimage _ _

/-! #### The differential -/

/-- **The transport of deformations along an isomorphism of algebras is bijective on fibrewise
isomorphism classes.** The fibre functors reflect isomorphy, by
`CategoryTheory.Over.mapIsoPreimage`, and are essentially surjective, by
`CategoryTheory.Over.mapIsoSectionIso`; so this is
`Deformation.bijective_mapIsomorphismClasses_of_fiberwise`. -/
public theorem bijective_mapIsomorphismClasses_ringDeformationTransport
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k) :
    Function.Bijective (mapIsomorphismClasses
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := R))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S))
      (ringDeformationTransport (Λ := Λ) e he) A) := by
  classical
  refine bijective_mapIsomorphismClasses_of_fiberwise _ _ _ A ?_ ?_
  · rintro x y ⟨i⟩
    refine ⟨⟨⟨Over.mapIsoPreimage (transportIso (Λ := Λ) e he) i.hom.val,
      isHomLift_mapIsoPreimage e he (𝟙 A) _ i.hom.property⟩,
      ⟨Over.mapIsoPreimage (transportIso (Λ := Λ) e he) i.inv.val,
      isHomLift_mapIsoPreimage e he (𝟙 A) _ i.inv.property⟩, ?_, ?_⟩⟩
    · exact Subtype.ext (Over.OverMorphism.ext
        (congrArg (fun m => (Subtype.val m).left) i.hom_inv_id))
    · exact Subtype.ext (Over.OverMorphism.ext
        (congrArg (fun m => (Subtype.val m).left) i.inv_hom_id))
  · intro z
    refine ⟨⟨Over.mapIsoSection (transportIso (Λ := Λ) e he) z.1, z.2⟩, ⟨?_⟩⟩
    have hz := isHomLift_id_mapIsoSectionIso e he z.1 z.2
    refine ⟨⟨(Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) z.1).hom, hz.1⟩,
      ⟨(Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) z.1).inv, hz.2⟩, ?_, ?_⟩
    · exact Subtype.ext (Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) z.1).hom_inv_id
    · exact Subtype.ext (Over.mapIsoSectionIso (transportIso (Λ := Λ) e he) z.1).inv_hom_id

/-- **The transport of deformations along an isomorphism of algebras is an isomorphism on tangent
spaces.** This is `Deformation.Examples.bijective_mapIsomorphismClasses_ringDeformationTransport`
at the dual numbers. -/
public theorem bijective_differential_ringDeformationTransport :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := R))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S))
      (ringDeformationTransport (Λ := Λ) e he)) :=
  bijective_mapIsomorphismClasses_ringDeformationTransport e he _

/-! #### Transport of a conclusion about a functor into a deformation category -/

section Comp

variable {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- **Composing with the transport preserves smoothness.** This is the form in which a caller uses
the transport: a smooth functor into the deformations of `R` composes to a smooth functor into the
deformations of `S`. -/
public theorem isSmooth_comp_ringDeformationTransport
    (φ : BasedFunctor 𝓕 (ringDeformationBasedCategory Λ k R)) (hφ : IsSmooth φ) :
    IsSmooth (BasedFunctor.comp φ (ringDeformationTransport (Λ := Λ) e he)) :=
  isSmooth_comp φ _ hφ (isSmooth_ringDeformationTransport e he)

/-- **Composing with the transport preserves the tangent-space isomorphism.** The map on
isomorphism classes of a composite is the composite of the maps, by
`Deformation.mapIsomorphismClasses_comp`, and the transport's is bijective. -/
public theorem bijective_differential_comp_ringDeformationTransport
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (φ : BasedFunctor 𝓕 (ringDeformationBasedCategory Λ k R))
    (hφ : Function.Bijective (differential h𝓕
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := R)) φ)) :
    Function.Bijective (differential h𝓕
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S))
      (BasedFunctor.comp φ (ringDeformationTransport (Λ := Λ) e he))) := by
  have h := mapIsomorphismClasses_comp h𝓕
    (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := R))
    (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S))
    φ (ringDeformationTransport (Λ := Λ) e he) (augmentedDualNumbers (Λ := Λ) (k := k))
  change Function.Bijective (mapIsomorphismClasses h𝓕
    (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S))
    (BasedFunctor.comp φ (ringDeformationTransport (Λ := Λ) e he))
    (augmentedDualNumbers (Λ := Λ) (k := k)))
  rw [h]
  exact (bijective_differential_ringDeformationTransport e he).comp hφ

end Comp

end Transport

end Deformation.Examples
