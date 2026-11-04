module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections

/-!
# The degree `0` term of a presentation, against its polynomial model

Let `A ⟶ B` be a morphism of sheaves of commutative rings on a site `(C, J)` and let
`e : E ⟶ B` be a family of generators, so that `A[E] ⟶ B` is a presentation of `B`.  The free
algebra sheaf `A[E]` is the sheafification of the presheaf `U ↦ A(U)[E(U)]` of polynomial
rings, so a section of `A[E]` is only locally a polynomial, and the affine description of the
degree `-1` cohomology of a polynomial presentation — the classes of those elements of the
kernel all of whose partial derivatives lie in the kernel — cannot be read off the sections of
`A[E]`.

What makes it available is the statement proved here: the comparison of the degree `0` term
`(A(U)[E(U)]/I(U)) ⊗ Ω[A(U)[E(U)]/A(U)]` of the polynomial model with the degree `0` term
`B ⊗[A[E]] Ω[A[E]/A]` of the conormal sequence is *locally injective*.  The comparison is
retracted by a morphism of sheaves of `B`-modules, obtained from the universal differential of
the polynomial model: that family of maps is a derivation with values in a sheaf, so the
extension theorem along a locally bijective morphism of presheaves of commutative rings
(Stacks 08TP, `AlgebraicGeometry.SheafOfModules.existsUnique_derivation_extension`) extends it
along the sheafification unit `A(-)[E(-)] ⟶ A[E]`, and the extension classifies a map out of
the degree `0` term.

## Main definitions

* `Stacks.Sites.Conormal.quotientToRingSheafOfPresheaf`,
  `Stacks.Sites.Conormal.presheafTensorSheaf` and
  `Stacks.Sites.Conormal.toPresheafTensorSheaf`: the sheaf of `B`-modules associated with the
  tensor presheaf of a presentation whose source is only a *presheaf* of commutative rings,
  and the sheafification unit on its sections.
* `Stacks.Sites.Conormal.sectionsExtension`: a presentation of presheaves of commutative
  rings, read on the sections over one object as an extension of the image ring.
* `Stacks.Sites.FreeAlgebra.polynomialDerivation`: the relative derivation of `A[E]` over `A`
  with values in the sheafified polynomial model which extends `q ↦ 1 ⊗ d q`.
* `Stacks.Sites.FreeAlgebra.polynomialTensorDesc`: the morphism of sheaves of `B`-modules
  `B ⊗[A[E]] Ω[A[E]/A] ⟶ (polynomial model)^#` that it classifies.

## Main results

* `Stacks.Sites.Conormal.vanishingSieve_mem_of_toPresheafTensorSheaf_eq_zero`: a local section
  of the tensor presheaf dying in the associated sheaf restricts to zero on a covering.
* `Stacks.Sites.FreeAlgebra.existsUnique_polynomialDerivation`: the universal differential of
  the polynomial model extends uniquely to `A[E]`.
* `Stacks.Sites.FreeAlgebra.polynomialTensorDesc_tensorDifferential`: the retraction carries
  the local section `1 ⊗ d x` to the value of the derivation.
* `Stacks.Sites.FreeAlgebra.vanishingSieve_mem_of_tensorDifferential_eq_zero` and
  `Stacks.Sites.FreeAlgebra.exists_covering_forall_pderiv_mem`: **the derivative criterion for
  a presentation by a free algebra sheaf**.  A polynomial in the kernel whose universal
  differential dies in the degree `0` term of the conormal sequence has, on a covering, all of
  its partial derivatives in the kernel.

## Implementation notes

The module universe of the sheaves of modules is `max w u v z` while the ring universe is `w`;
the two sheafification instances for abelian groups are the local instances of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalSequence.lean`, declared again here because
they are local to that file.

The maps out of the degree `0` term are built with
`Stacks.NaiveCotangent.cotangentSpaceDesc`, which consumes an `Algebra.Extension`; the
extension is `Stacks.Sites.Conormal.sectionsExtension`, a `reducible` definition so that its
`Ring` field is seen through by instance search, and its `CotangentSpace` is the tensor object
of the conormal sequence on the nose.  Every application of `cotangentSpaceDesc` and of
`cotangentSpaceDesc_tmul` passes all four of its explicit arguments: leaving them to
unification makes the elaborator diverge at `whnf`.

The scalar actions are the delicate point.  A section of the sheafified polynomial model
carries an action of `B`, and the one used by the derivation is the restriction of scalars
along the presentation, while the one used by `cotangentSpaceDesc` is the restriction along
the inclusion of the image presheaf into `B`; the two are definitionally equal, and the local
instances above record each of them once, at the spelling of the type whose sections they act
on.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra
  sheaf.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal
  sequence.
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP), the extension of a
  derivation along a sheafification.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), the affine
  description of the degree `-1` cohomology.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of
  the naive cotangent complex from the presentation, for whose degree `-1` comparison this is
  the local input.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w z

namespace Stacks.Sites.Conormal



variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Over an essentially small site, presheaves of abelian groups admit sheafification. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- Over an essentially small site, the morphisms of presheaves of abelian groups inverted by
sheafification are the locally bijective ones. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₀ : Cᵒᵖ ⥤ CommRingCat.{w}} (B : Sheaf J CommRingCat.{w}) (φ₀ : A₀ ⟶ B.obj)

/-- The locally bijective ring map from the image presheaf of a presentation by a *presheaf*
of commutative rings to the target sheaf. -/
noncomputable def quotientToRingSheafOfPresheaf :
    quotientPresheaf φ₀ ⋙ forget₂ CommRingCat RingCat ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf B).obj :=
  Functor.whiskerRight (quotientToTarget φ₀) (forget₂ CommRingCat RingCat)

/-- The map from the image presheaf to the target sheaf is locally injective. -/
instance : Presheaf.IsLocallyInjective J (quotientToRingSheafOfPresheaf J B φ₀) :=
  Presheaf.isLocallyInjective_of_injective _ _ (quotientToTarget_injective φ₀)

/-- If the presentation is locally surjective, so is the map from its image presheaf to the
target sheaf. -/
instance [Presheaf.IsLocallySurjective J φ₀] :
    Presheaf.IsLocallySurjective J (quotientToRingSheafOfPresheaf J B φ₀) where
  imageSieve_mem x := Presheaf.imageSieve_mem J (quotientToTarget φ₀) x

variable [Presheaf.IsLocallySurjective J φ₀]
  {R₀ : Cᵒᵖ ⥤ CommRingCat.{w}} (a₀ : R₀ ⟶ A₀)

/-- The sheaf of `B`-modules associated with the tensor presheaf of a presentation by a
presheaf of commutative rings. -/
noncomputable abbrev presheafTensorSheaf :
    _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  (PresheafOfModules.sheafification.{max w u v z}
      (quotientToRingSheafOfPresheaf J B φ₀)).obj
    ((liftModules.{v, u, w, z} _).obj (tensorPresheaf φ₀ a₀))

/-- The unit of the sheafification of the tensor presheaf, as a morphism of presheaves of
modules. -/
noncomputable def presheafTensorUnit :
    (liftModules.{v, u, w, z} _).obj (tensorPresheaf φ₀ a₀) ⟶
      (PresheafOfModules.restrictScalars (quotientToRingSheafOfPresheaf J B φ₀)).obj
        (presheafTensorSheaf.{v, u, w, z} J B φ₀ a₀).val :=
  PresheafOfModules.toSheafify _ _

/-- The sheafification unit of the tensor presheaf is locally injective. -/
instance : PresheafOfModules.IsLocallyInjective J
    (presheafTensorUnit.{v, u, w, z} J B φ₀ a₀) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective J
    (PresheafOfModules.toSheafify (quotientToRingSheafOfPresheaf J B φ₀) _))

/-- The image of a section of the tensor presheaf in the associated sheaf. -/
noncomputable def toPresheafTensorSheaf (X : Cᵒᵖ) (t : (tensorPresheaf φ₀ a₀).obj X) :
    (presheafTensorSheaf.{v, u, w, z} J B φ₀ a₀).val.obj X :=
  (presheafTensorUnit.{v, u, w, z} J B φ₀ a₀).app X (ULift.up t)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A local section of the tensor presheaf whose image in the associated sheaf vanishes
restricts to zero on a covering sieve. -/
theorem vanishingSieve_mem_of_toPresheafTensorSheaf_eq_zero (X : Cᵒᵖ)
    (t : (tensorPresheaf φ₀ a₀).obj X)
    (h : toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X t = 0) :
    vanishingSieve (tensorPresheaf φ₀ a₀) t ∈ J X.unop := by
  have h0 : ((PresheafOfModules.toPresheaf _).map
      (presheafTensorUnit.{v, u, w, z} J B φ₀ a₀)).app X (ULift.up t) =
      ((PresheafOfModules.toPresheaf _).map
      (presheafTensorUnit.{v, u, w, z} J B φ₀ a₀)).app X 0 := by
    refine h.trans ?_
    exact (map_zero ((presheafTensorUnit.{v, u, w, z} J B φ₀ a₀).app X).hom).symm
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
    ((PresheafOfModules.toPresheaf _).map (presheafTensorUnit.{v, u, w, z} J B φ₀ a₀))
    (ULift.up t) 0 h0)
  intro Y k hk
  have hk' : ULift.up ((tensorPresheaf φ₀ a₀).map k.op t) =
      (0 : ULift.{max u v z} ((tensorPresheaf φ₀ a₀).obj (op Y))) := by
    refine hk.trans ?_
    exact map_zero (((liftModules.{v, u, w, z} _).obj (tensorPresheaf φ₀ a₀)).map k.op).hom
  exact congrArg ULift.down hk'

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheafification unit is additive on sections of the tensor presheaf. -/
theorem toPresheafTensorSheaf_add (X : Cᵒᵖ) (t t' : (tensorPresheaf φ₀ a₀).obj X) :
    toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X (t + t') =
      toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X t +
        toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X t' :=
  map_add ((presheafTensorUnit.{v, u, w, z} J B φ₀ a₀).app X).hom (ULift.up t) (ULift.up t')

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheafification unit is semilinear over the inclusion of the image presheaf. -/
theorem toPresheafTensorSheaf_smul (X : Cᵒᵖ) (r : (quotientPresheaf φ₀).obj X)
    (t : (tensorPresheaf φ₀ a₀).obj X) :
    toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X (r • t) =
      (quotientToRingSheafOfPresheaf J B φ₀).app X r •
        toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X t :=
  ((presheafTensorUnit.{v, u, w, z} J B φ₀ a₀).app X).hom.map_smul r (ULift.up t)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheafification unit commutes with the restriction maps. -/
theorem toPresheafTensorSheaf_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : (tensorPresheaf φ₀ a₀).obj X) :
    toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ Y ((tensorPresheaf φ₀ a₀).map f t) =
      (presheafTensorSheaf.{v, u, w, z} J B φ₀ a₀).val.map f
        (toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X t) :=
  PresheafOfModules.naturality_apply (presheafTensorUnit.{v, u, w, z} J B φ₀ a₀) f (ULift.up t)

section Extension

variable {A B' : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : A ⟶ B') {R : Cᵒᵖ ⥤ CommRingCat.{w}} (a : R ⟶ A)
  (X : Cᵒᵖ)

/-- The algebra structure of the image presheaf over the base, on sections. -/
noncomputable abbrev quotientAlgebra :
    letI := (a.app X).hom.toAlgebra
    Algebra (R.obj X) (A.obj X ⧸ kernelIdeal φ X) :=
  letI := (a.app X).hom.toAlgebra
  ((Ideal.Quotient.mk (kernelIdeal φ X)).comp (a.app X).hom).toAlgebra

/-- A presentation of presheaves of commutative rings, read on the sections over one object as
an extension of the image ring. -/
noncomputable abbrev sectionsExtension :
    letI := (a.app X).hom.toAlgebra
    letI := quotientAlgebra φ a X
    Algebra.Extension (R.obj X) (A.obj X ⧸ kernelIdeal φ X) :=
  letI := (a.app X).hom.toAlgebra
  letI := quotientAlgebra φ a X
  { Ring := A.obj X
    σ := Function.surjInv Ideal.Quotient.mk_surjective
    algebraMap_σ := Function.surjInv_eq Ideal.Quotient.mk_surjective
    isScalarTower := IsScalarTower.of_algebraMap_eq' rfl }

end Extension

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The image of a zero section vanishes. -/
theorem toPresheafTensorSheaf_zero (X : Cᵒᵖ) :
    toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X 0 = 0 :=
  map_zero ((presheafTensorUnit.{v, u, w, z} J B φ₀ a₀).app X).hom

/-- The local section `1 ⊗ d x` of the associated sheaf of the tensor presheaf. -/
noncomputable def presheafTensorDifferential (X : Cᵒᵖ) (x : A₀.obj X) :
    (presheafTensorSheaf.{v, u, w, z} J B φ₀ a₀).val.obj X :=
  toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X
    ((1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X]
      CommRingCat.KaehlerDifferential.d (f := a₀.app X) x)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The local section `1 ⊗ d x` is additive in `x`. -/
theorem presheafTensorDifferential_add (X : Cᵒᵖ) (x y : A₀.obj X) :
    presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X (x + y) =
      presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X x +
        presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X y := by
  refine Eq.trans (congrArg (toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X) ?_)
    (toPresheafTensorSheaf_add.{v, u, w, z} J B φ₀ a₀ X _ _)
  refine Eq.trans (congrArg (fun ω : (differentialsPresheaf a₀).obj X ↦
    (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X] ω)
      (ModuleCat.Derivation.d_add (CommRingCat.KaehlerDifferential.D (a₀.app X)) x y)) ?_
  exact TensorProduct.tmul_add _ _ _

/-- A section `1 ⊗ s • ω` is `s` times `1 ⊗ ω`. -/
private theorem toPresheafTensorSheaf_one_tmul_smul (X : Cᵒᵖ) (s : A₀.obj X)
    (ω : (differentialsPresheaf a₀).obj X) :
    toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X
        ((1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X] (s • ω)) =
      φ₀.app X s • toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X
        ((1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X] ω) := by
  refine Eq.trans (congrArg (toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X)
    (show (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X] (s • ω) =
        (Ideal.Quotient.mk (kernelIdeal φ₀ X) s) •
          ((1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X] ω) from ?_)) ?_
  · rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
    rfl
  · exact toPresheafTensorSheaf_smul.{v, u, w, z} J B φ₀ a₀ X _ _

/-- The local section `1 ⊗ d x` satisfies the Leibniz rule over the presentation. -/
theorem presheafTensorDifferential_mul (X : Cᵒᵖ) (x y : A₀.obj X) :
    presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X (x * y) =
      φ₀.app X x • presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X y +
        φ₀.app X y • presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X x := by
  refine Eq.trans (congrArg (toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X)
    (show (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X]
          CommRingCat.KaehlerDifferential.d (f := a₀.app X) (x * y) =
        (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X]
            (x • CommRingCat.KaehlerDifferential.d (f := a₀.app X) y) +
          (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X]
            (y • CommRingCat.KaehlerDifferential.d (f := a₀.app X) x) from ?_)) ?_
  · have hd : CommRingCat.KaehlerDifferential.d (f := a₀.app X) (x * y) =
        x • CommRingCat.KaehlerDifferential.d (f := a₀.app X) y +
          y • CommRingCat.KaehlerDifferential.d (f := a₀.app X) x :=
      ModuleCat.Derivation.d_mul (CommRingCat.KaehlerDifferential.D (a₀.app X)) x y
    rw [hd]
    exact TensorProduct.tmul_add _ _ _
  · refine Eq.trans (toPresheafTensorSheaf_add.{v, u, w, z} J B φ₀ a₀ X _ _) ?_
    exact congrArg₂ (· + ·)
      (toPresheafTensorSheaf_one_tmul_smul.{v, u, w, z} J B φ₀ a₀ X x _)
      (toPresheafTensorSheaf_one_tmul_smul.{v, u, w, z} J B φ₀ a₀ X y _)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The local section `1 ⊗ d x` vanishes on coefficients. -/
theorem presheafTensorDifferential_coefficient (X : Cᵒᵖ) (r : R₀.obj X) :
    presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X (a₀.app X r) = 0 := by
  refine Eq.trans (congrArg (toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ X)
    (show (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X]
          CommRingCat.KaehlerDifferential.d (f := a₀.app X) (a₀.app X r) = 0 from ?_)) ?_
  · refine Eq.trans (congrArg (fun ω : (differentialsPresheaf a₀).obj X ↦
      (1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X] ω)
        (ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D (a₀.app X)) r)) ?_
    exact TensorProduct.tmul_zero _ _
  · exact toPresheafTensorSheaf_zero.{v, u, w, z} J B φ₀ a₀ X

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [Presheaf.IsLocallySurjective J φ₀] in
/-- Restriction carries the local section `1 ⊗ d x` to `1 ⊗ d` of the restriction. -/
theorem tensorPresheaf_map_one_tmul_d {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : A₀.obj X) :
    (tensorPresheaf φ₀ a₀).map f
        ((1 : A₀.obj X ⧸ kernelIdeal φ₀ X) ⊗ₜ[A₀.obj X]
          CommRingCat.KaehlerDifferential.d (f := a₀.app X) x) =
      (1 : A₀.obj Y ⧸ kernelIdeal φ₀ Y) ⊗ₜ[A₀.obj Y]
        CommRingCat.KaehlerDifferential.d (f := a₀.app Y) (A₀.map f x) := by
  show (quotientPresheaf φ₀).map f 1 ⊗ₜ[A₀.obj Y]
      (differentialsPresheaf a₀).map f (CommRingCat.KaehlerDifferential.d x) = _
  rw [map_one ((quotientPresheaf φ₀).map f).hom]
  exact congrArg (fun ω : (differentialsPresheaf a₀).obj Y ↦
      (1 : A₀.obj Y ⧸ kernelIdeal φ₀ Y) ⊗ₜ[A₀.obj Y] ω)
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d a₀ f x)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The local section `1 ⊗ d x` is compatible with restriction. -/
theorem presheafTensorDifferential_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : A₀.obj X) :
    presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ Y (A₀.map f x) =
      (presheafTensorSheaf.{v, u, w, z} J B φ₀ a₀).val.map f
        (presheafTensorDifferential.{v, u, w, z} J B φ₀ a₀ X x) := by
  refine Eq.trans (congrArg (toPresheafTensorSheaf.{v, u, w, z} J B φ₀ a₀ Y)
    (tensorPresheaf_map_one_tmul_d J B φ₀ a₀ f x).symm)
    (toPresheafTensorSheaf_map.{v, u, w, z} J B φ₀ a₀ f _)

end Stacks.Sites.Conormal

/-! ### The polynomial model of a presentation by a free algebra sheaf -/

namespace Stacks.Sites.FreeAlgebra

open Stacks.Sites.Conormal


variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Over an essentially small site, presheaves of abelian groups admit sheafification. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- Over an essentially small site, the morphisms of presheaves of abelian groups inverted by
sheafification are the locally bijective ones. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B)
  (e : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E a e).hom]

/-- The evaluation `A(-)[E(-)] ⟶ B` of the polynomial model is locally surjective. -/
instance isLocallySurjective_polynomialEvaluation :
    Presheaf.IsLocallySurjective J (polynomialEvaluation J A B E a e) := by
  rw [← polynomialUnit_comp_desc J A B E a e]
  infer_instance

/-- The presentation, read as the structure map making a sheaf of `B`-modules a presheaf of
modules over the free algebra sheaf. -/
noncomputable def freeAlgebraToRingSheaf :
    (freeAlgebraSheaf J A E).obj ⋙ forget₂ CommRingCat RingCat ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf B).obj :=
  Functor.whiskerRight (freeAlgebraSheafDesc J A B E a e).hom (forget₂ CommRingCat RingCat)

/-- The sheaf of `B`-modules associated with the tensor presheaf of the polynomial model of
the presentation `A[E] ⟶ B`. -/
noncomputable abbrev polynomialTensorSheaf :
    _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  presheafTensorSheaf.{v, u, w, z} J B (polynomialEvaluation J A B E a e)
    (polynomialCoefficientMap J A E)

/-- That sheaf, read as a presheaf of modules over the free algebra sheaf. -/
noncomputable abbrev polynomialTensorOverFree :
    PresheafOfModules.{max w u v z}
      ((freeAlgebraSheaf J A E).obj ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars (freeAlgebraToRingSheaf J A B E a e)).obj
    ((_root_.SheafOfModules.forget _).obj (polynomialTensorSheaf.{v, u, w, z} J A B E a e))

/-- The local section `1 ⊗ d q` of the sheafified polynomial model. -/
noncomputable abbrev polynomialDifferential (X : Cᵒᵖ)
    (q : (polynomialPresheaf J A E).obj X) :
    (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj X :=
  presheafTensorDifferential.{v, u, w, z} J B (polynomialEvaluation J A B E a e)
    (polynomialCoefficientMap J A E) X q

/-- The local section `1 ⊗ d q`, as an additive map in `q`. -/
noncomputable def polynomialDifferentialHom (X : Cᵒᵖ) :
    (polynomialPresheaf J A E).obj X →+
      (polynomialTensorOverFree.{v, u, w, z} J A B E a e).obj X :=
  AddMonoidHom.mk' (polynomialDifferential.{v, u, w, z} J A B E a e X)
    (presheafTensorDifferential_add.{v, u, w, z} J B (polynomialEvaluation J A B E a e)
      (polynomialCoefficientMap J A E) X)

/-- **The universal differential of the polynomial model extends to the free algebra sheaf.**
The sheafification unit `A(-)[E(-)] ⟶ A[E]` is locally bijective, so the family of maps
`q ↦ 1 ⊗ d q` into the sheafified polynomial model, being a derivation with values in a sheaf,
extends in exactly one way to a relative derivation of `A[E]` over `A`. -/
theorem existsUnique_polynomialDerivation :
    ∃! D : (polynomialTensorOverFree.{v, u, w, z} J A B E a e).Derivation'
      (freeAlgebraSheafCoefficientMap J A E).hom,
      ∀ (X : Cᵒᵖ) (q : (polynomialPresheaf J A E).obj X),
        D.d ((polynomialUnit J A E).app X q) =
          polynomialDifferential.{v, u, w, z} J A B E a e X q := by
  refine AlgebraicGeometry.SheafOfModules.existsUnique_derivation_extension.{max u v z}
    J (polynomialUnit J A E) (polynomialCoefficientMap J A E)
    (freeAlgebraSheafCoefficientMap J A E).hom (𝟙 A.obj) (fun X s ↦ rfl)
    (polynomialTensorSheaf.{v, u, w, z} J A B E a e).isSheaf
    (fun {X} ↦ polynomialDifferentialHom.{v, u, w, z} J A B E a e X)
    (fun {X} x y ↦ ?_) (fun {X Y} g x ↦ ?_) (fun {X} s ↦ ?_)
  · refine Eq.trans (presheafTensorDifferential_mul.{v, u, w, z} J B
      (polynomialEvaluation J A B E a e) (polynomialCoefficientMap J A E) X x y) ?_
    exact congrArg₂ (· + ·)
      (congrArg (· • _) (app_apply_of_fac (polynomialUnit_comp_desc J A B E a e) X x).symm)
      (congrArg (· • _) (app_apply_of_fac (polynomialUnit_comp_desc J A B E a e) X y).symm)
  · exact presheafTensorDifferential_map.{v, u, w, z} J B (polynomialEvaluation J A B E a e)
      (polynomialCoefficientMap J A E) g x
  · exact presheafTensorDifferential_coefficient.{v, u, w, z} J B
      (polynomialEvaluation J A B E a e) (polynomialCoefficientMap J A E) X s

/-- The relative derivation of `A[E]` over `A` with values in the sheafified polynomial model
extending the universal differential of the polynomial model. -/
noncomputable def polynomialDerivation :
    (polynomialTensorOverFree.{v, u, w, z} J A B E a e).Derivation'
      (freeAlgebraSheafCoefficientMap J A E).hom :=
  (existsUnique_polynomialDerivation.{v, u, w, z} J A B E a e).choose

/-- On the image of the sheafification unit the derivation is `q ↦ 1 ⊗ d q`. -/
theorem polynomialDerivation_d_unit (X : Cᵒᵖ) (q : (polynomialPresheaf J A E).obj X) :
    (polynomialDerivation.{v, u, w, z} J A B E a e).d ((polynomialUnit J A E).app X q) =
      polynomialDifferential.{v, u, w, z} J A B E a e X q :=
  (existsUnique_polynomialDerivation.{v, u, w, z} J A B E a e).choose_spec.1 X q

/-- The sections of the free algebra sheaf, as an algebra over the base. -/
noncomputable local instance algebraSectionsFree (X : Cᵒᵖ) :
    Algebra (A.obj.obj X) ((freeAlgebraSheaf J A E).obj.obj X) :=
  ((freeAlgebraSheafCoefficientMap J A E).hom.app X).hom.toAlgebra

/-- The image presheaf of the presentation, as an algebra over the base. -/
noncomputable local instance algebraSectionsQuotient (X : Cᵒᵖ) :
    Algebra (A.obj.obj X) ((freeAlgebraSheaf J A E).obj.obj X ⧸
      kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X) :=
  quotientAlgebra (freeAlgebraSheafDesc J A B E a e).hom
    (freeAlgebraSheafCoefficientMap J A E).hom X

/-- The sections of the sheafified polynomial model as a module over the target. -/
noncomputable local instance moduleTargetOverFree (X : Cᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X)
      ((polynomialTensorOverFree.{v, u, w, z} J A B E a e).obj X) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X)
    ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj X))

/-- The sections of the sheafified polynomial model as a module over the image presheaf. -/
noncomputable local instance moduleQuotientOverFree (X : Cᵒᵖ) :
    Module ((freeAlgebraSheaf J A E).obj.obj X ⧸
        kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X)
      ((polynomialTensorOverFree.{v, u, w, z} J A B E a e).obj X) :=
  Module.compHom _ ((quotientToRingSheaf J (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafDesc J A B E a e)).app X).hom

/-- The map on sections classifying the derivation: it sends `b ⊗ d p` to `b • D p`. -/
noncomputable def polynomialTensorDescHom (X : Cᵒᵖ) :
    (sectionsExtension (freeAlgebraSheafDesc J A B E a e).hom
          (freeAlgebraSheafCoefficientMap J A E).hom X).CotangentSpace →ₗ[
        (freeAlgebraSheaf J A E).obj.obj X ⧸
          kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X]
      ((polynomialTensorOverFree.{v, u, w, z} J A B E a e).obj X) :=
  Stacks.NaiveCotangent.cotangentSpaceDesc
    (sectionsExtension (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom X)
    ((polynomialDerivation.{v, u, w, z} J A B E a e).d (X := X))
    (fun x y ↦ (polynomialDerivation.{v, u, w, z} J A B E a e).d_mul x y)
    (fun r ↦ (polynomialDerivation.{v, u, w, z} J A B E a e).d_app r)

/-- The classifying map, on sections of the tensor presheaf. -/
noncomputable def polynomialTensorDescApp (X : Cᵒᵖ)
    (t : (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom).obj X) :
    (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj X :=
  polynomialTensorDescHom.{v, u, w, z} J A B E a e X t

/-- The classifying map sends `b ⊗ d p` to `b • D p`. -/
theorem polynomialTensorDescHom_tmul (X : Cᵒᵖ)
    (b : (freeAlgebraSheaf J A E).obj.obj X ⧸
      kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X)
    (p : (freeAlgebraSheaf J A E).obj.obj X) :
    polynomialTensorDescHom.{v, u, w, z} J A B E a e X
        (b ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj X]
          KaehlerDifferential.D (A.obj.obj X) ((freeAlgebraSheaf J A E).obj.obj X) p) =
      b • (polynomialDerivation.{v, u, w, z} J A B E a e).d p :=
  Stacks.NaiveCotangent.cotangentSpaceDesc_tmul
    (sectionsExtension (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom X)
    ((polynomialDerivation.{v, u, w, z} J A B E a e).d (X := X))
    (fun x y ↦ (polynomialDerivation.{v, u, w, z} J A B E a e).d_mul x y)
    (fun r ↦ (polynomialDerivation.{v, u, w, z} J A B E a e).d_app r) b p

/-- The classifying map is additive. -/
theorem polynomialTensorDescApp_add (X : Cᵒᵖ)
    (t t' : (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom).obj X) :
    polynomialTensorDescApp.{v, u, w, z} J A B E a e X (t + t') =
      polynomialTensorDescApp.{v, u, w, z} J A B E a e X t +
        polynomialTensorDescApp.{v, u, w, z} J A B E a e X t' :=
  map_add (polynomialTensorDescHom.{v, u, w, z} J A B E a e X) t t'

/-- The classifying map is semilinear over the inclusion of the image presheaf. -/
theorem polynomialTensorDescApp_smul (X : Cᵒᵖ)
    (r : (quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).obj X)
    (t : (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom).obj X) :
    polynomialTensorDescApp.{v, u, w, z} J A B E a e X (r • t) =
      (quotientToRingSheaf J (freeAlgebraSheaf J A E) B
          (freeAlgebraSheafDesc J A B E a e)).app X r •
        polynomialTensorDescApp.{v, u, w, z} J A B E a e X t :=
  map_smul (polynomialTensorDescHom.{v, u, w, z} J A B E a e X) r t

section Naturality

variable {X Y : Cᵒᵖ} (f : X ⟶ Y)

/-- The sections over a later object, as a module over the image presheaf at an earlier one. -/
noncomputable abbrev moduleQuotientRestricted :
    Module ((freeAlgebraSheaf J A E).obj.obj X ⧸
        kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X)
      ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj Y) :=
  Module.compHom _ ((((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map f).hom).comp
    ((quotientToRingSheaf J (freeAlgebraSheaf J A E) B
      (freeAlgebraSheafDesc J A B E a e)).app X).hom)

/-- Restricting a section and then classifying it, as a semilinear map. -/
noncomputable def polynomialTensorDescRestrict :
    letI := moduleQuotientRestricted.{v, u, w, z} J A B E a e f
    tensorObj (freeAlgebraSheafDesc J A B E a e).hom
        (freeAlgebraSheafCoefficientMap J A E).hom X →ₗ[
      (quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).obj X]
      ModuleCat.of ((quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).obj X)
        ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj Y) :=
  letI := moduleQuotientRestricted.{v, u, w, z} J A B E a e f
  { toFun := fun t ↦ polynomialTensorDescApp.{v, u, w, z} J A B E a e Y
      ((tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
        (freeAlgebraSheafCoefficientMap J A E).hom).map f t)
    map_add' := fun t t' ↦
      (congrArg (polynomialTensorDescApp.{v, u, w, z} J A B E a e Y)
        (map_add (tensorMapₛₗ (freeAlgebraSheafDesc J A B E a e).hom
          (freeAlgebraSheafCoefficientMap J A E).hom f) t t')).trans
        (polynomialTensorDescApp_add.{v, u, w, z} J A B E a e Y _ _)
    map_smul' := fun r t ↦
      ((congrArg (polynomialTensorDescApp.{v, u, w, z} J A B E a e Y)
        (tensorMapₛₗ_smul (freeAlgebraSheafDesc J A B E a e).hom
          (freeAlgebraSheafCoefficientMap J A E).hom f r t)).trans
        (polynomialTensorDescApp_smul.{v, u, w, z} J A B E a e Y _ _)).trans
        (congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj Y ↦
            s • polynomialTensorDescApp.{v, u, w, z} J A B E a e Y
              ((tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
                (freeAlgebraSheafCoefficientMap J A E).hom).map f t))
          (NatTrans.naturality_apply (quotientToRingSheaf J (freeAlgebraSheaf J A E) B
            (freeAlgebraSheafDesc J A B E a e)) f r)) }

/-- Classifying a section and then restricting it, as a semilinear map. -/
noncomputable def polynomialTensorRestrictDesc :
    letI := moduleQuotientRestricted.{v, u, w, z} J A B E a e f
    tensorObj (freeAlgebraSheafDesc J A B E a e).hom
        (freeAlgebraSheafCoefficientMap J A E).hom X →ₗ[
      (quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).obj X]
      ModuleCat.of ((quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).obj X)
        ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj Y) :=
  letI := moduleQuotientRestricted.{v, u, w, z} J A B E a e f
  { toFun := fun t ↦ (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f
      (polynomialTensorDescApp.{v, u, w, z} J A B E a e X t)
    map_add' := fun t t' ↦
      (congrArg ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f)
        (polynomialTensorDescApp_add.{v, u, w, z} J A B E a e X t t')).trans
        (map_add (((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f)).hom _ _)
    map_smul' := fun r t ↦
      (congrArg ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f)
        (polynomialTensorDescApp_smul.{v, u, w, z} J A B E a e X r t)).trans
        (PresheafOfModules.map_smul
          ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val) f _ _) }

/-- **The classifying map commutes with the restriction maps.**  Both sides are semilinear in
the section, so it is enough to compare them on the local sections `b ⊗ d p`, where the
derivation's own compatibility with restriction gives the equality. -/
theorem polynomialTensorDescApp_map
    (t : (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom).obj X) :
    polynomialTensorDescApp.{v, u, w, z} J A B E a e Y
        ((tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
          (freeAlgebraSheafCoefficientMap J A E).hom).map f t) =
      (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f
        (polynomialTensorDescApp.{v, u, w, z} J A B E a e X t) := by
  refine DFunLike.congr_fun (tensor_hom_ext (freeAlgebraSheafDesc J A B E a e).hom
    (freeAlgebraSheafCoefficientMap J A E).hom X
    (polynomialTensorDescRestrict J A B E a e f)
    (polynomialTensorRestrictDesc J A B E a e f) ?_) t
  intro b p
  show polynomialTensorDescApp.{v, u, w, z} J A B E a e Y
      ((tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
        (freeAlgebraSheafCoefficientMap J A E).hom).map f
        (b ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj X]
          KaehlerDifferential.D (A.obj.obj X) ((freeAlgebraSheaf J A E).obj.obj X) p)) =
    (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f
      (polynomialTensorDescApp.{v, u, w, z} J A B E a e X
        (b ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj X]
          KaehlerDifferential.D (A.obj.obj X) ((freeAlgebraSheaf J A E).obj.obj X) p))
  have hleft : (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
        (freeAlgebraSheafCoefficientMap J A E).hom).map f
        (b ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj X]
          KaehlerDifferential.D (A.obj.obj X) ((freeAlgebraSheaf J A E).obj.obj X) p) =
      (quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).map f b
        ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj Y]
        KaehlerDifferential.D (A.obj.obj Y) ((freeAlgebraSheaf J A E).obj.obj Y)
          ((freeAlgebraSheaf J A E).obj.map f p) :=
    (TensorProduct.map_tmul _ _ _ _).trans
      (congrArg (fun ω : (differentialsPresheaf
          (freeAlgebraSheafCoefficientMap J A E).hom).obj Y ↦
        (quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).map f b
          ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj Y] ω)
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
          (freeAlgebraSheafCoefficientMap J A E).hom f p))
  refine Eq.trans (congrArg (polynomialTensorDescApp.{v, u, w, z} J A B E a e Y) hleft) ?_
  refine Eq.trans (polynomialTensorDescHom_tmul.{v, u, w, z} J A B E a e Y _ _) ?_
  refine Eq.trans ?_ (congrArg ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f)
    (polynomialTensorDescHom_tmul.{v, u, w, z} J A B E a e X b p)).symm
  refine Eq.trans ?_ (PresheafOfModules.map_smul
    ((polynomialTensorSheaf.{v, u, w, z} J A B E a e).val) f _ _).symm
  refine Eq.trans (congrArg (fun m : (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.obj Y ↦
      (quotientToRingSheaf J (freeAlgebraSheaf J A E) B
          (freeAlgebraSheafDesc J A B E a e)).app Y
        ((quotientPresheaf (freeAlgebraSheafDesc J A B E a e).hom).map f b) • m)
    ((polynomialDerivation.{v, u, w, z} J A B E a e).d_map f p)) ?_
  exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj Y ↦
      s • (polynomialTensorSheaf.{v, u, w, z} J A B E a e).val.map f
        ((polynomialDerivation.{v, u, w, z} J A B E a e).d p))
    (NatTrans.naturality_apply (quotientToRingSheaf J (freeAlgebraSheaf J A E) B
      (freeAlgebraSheafDesc J A B E a e)) f b)

end Naturality

/-- **The degree `0` term of the conormal sequence maps to the sheafified polynomial
model.**  The derivation of `A[E]` with values in the sheafified polynomial model classifies a
morphism of sheaves of `B`-modules out of `B ⊗[A[E]] Ω[A[E]/A]`, and that morphism is a
retraction of the comparison of the two models. -/
noncomputable def polynomialTensorDesc :
    tensorDifferentialsSheaf.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafDesc J A B E a e) ⟶
      polynomialTensorSheaf.{v, u, w, z} J A B E a e :=
  sheafifyLiftDesc.{v, u, w, z} J (freeAlgebraSheaf J A E) B (freeAlgebraSheafDesc J A B E a e)
    (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom)
    (polynomialTensorSheaf.{v, u, w, z} J A B E a e)
    (polynomialTensorDescApp.{v, u, w, z} J A B E a e)
    (polynomialTensorDescApp_add.{v, u, w, z} J A B E a e)
    (polynomialTensorDescApp_smul.{v, u, w, z} J A B E a e)
    (fun _ _ f t ↦ polynomialTensorDescApp_map.{v, u, w, z} J A B E a e f t)

/-- The retraction sends the local section `1 ⊗ d x` to the value of the derivation. -/
theorem polynomialTensorDesc_tensorDifferential (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J A E).obj.obj X) :
    (polynomialTensorDesc.{v, u, w, z} J A B E a e).val.app X
        (tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
          (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafDesc J A B E a e) X x) =
      (polynomialDerivation.{v, u, w, z} J A B E a e).d x := by
  refine Eq.trans (sheafifyLiftDesc_toAssociatedModule.{v, u, w, z} J
    (freeAlgebraSheaf J A E) B (freeAlgebraSheafDesc J A B E a e) _
    (polynomialTensorSheaf.{v, u, w, z} J A B E a e)
    (polynomialTensorDescApp.{v, u, w, z} J A B E a e)
    (polynomialTensorDescApp_add.{v, u, w, z} J A B E a e)
    (polynomialTensorDescApp_smul.{v, u, w, z} J A B E a e)
    (fun _ _ f t ↦ polynomialTensorDescApp_map.{v, u, w, z} J A B E a e f t) X _) ?_
  refine Eq.trans (polynomialTensorDescHom_tmul.{v, u, w, z} J A B E a e X 1 x) ?_
  exact one_smul ((freeAlgebraSheaf J A E).obj.obj X ⧸
      kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X)
    ((polynomialDerivation.{v, u, w, z} J A B E a e).d x)

/-- **A polynomial whose universal differential dies in the degree `0` term of the conormal
sequence has all of its partial derivatives in the kernel, locally.**  The sheafification unit
of the polynomial model is locally injective and the retraction above carries `1 ⊗ d q` to the
class of `1 ⊗ d q` in the sheafified polynomial model, so the vanishing of `1 ⊗ d q` on the
sheaf forces it to vanish on a covering of the polynomial model. -/
theorem vanishingSieve_mem_of_tensorDifferential_eq_zero (X : Cᵒᵖ)
    (q : (polynomialPresheaf J A E).obj X)
    (h : tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafDesc J A B E a e) X
        ((polynomialUnit J A E).app X q) = 0) :
    vanishingSieve (tensorPresheaf (polynomialEvaluation J A B E a e)
        (polynomialCoefficientMap J A E))
      ((1 : (polynomialPresheaf J A E).obj X ⧸
            kernelIdeal (polynomialEvaluation J A B E a e) X) ⊗ₜ
        CommRingCat.KaehlerDifferential.d
          (f := (polynomialCoefficientMap J A E).app X) q) ∈ J X.unop := by
  refine vanishingSieve_mem_of_toPresheafTensorSheaf_eq_zero.{v, u, w, z} J B
    (polynomialEvaluation J A B E a e) (polynomialCoefficientMap J A E) X _ ?_
  refine Eq.trans (polynomialDerivation_d_unit.{v, u, w, z} J A B E a e X q).symm ?_
  refine Eq.trans (polynomialTensorDesc_tensorDifferential.{v, u, w, z} J A B E a e X _).symm ?_
  refine Eq.trans (congrArg ((polynomialTensorDesc.{v, u, w, z} J A B E a e).val.app X) h) ?_
  exact map_zero ((polynomialTensorDesc.{v, u, w, z} J A B E a e).val.app X).hom

/-- **The derivative criterion for a presentation by a free algebra sheaf.**  A polynomial `q`
in the kernel of the polynomial model whose universal differential `1 ⊗ d q` vanishes in the
degree `0` term `B ⊗[A[E]] Ω[A[E]/A]` of the conormal sequence has, on a covering sieve, all of
its partial derivatives in the kernel of the polynomial model.

This is the transport to a presentation by a free algebra sheaf of the affine description of
the degree `-1` cohomology of a polynomial presentation, `{f ∈ I : ∀ i, ∂f/∂xᵢ ∈ I}/I²`.  The
sections of `A[E]` are not polynomials, so the criterion cannot be read on them directly; what
replaces it is that the comparison of the polynomial model with the sheaf is locally injective
on the degree `0` term, which is the content of
`Stacks.Sites.FreeAlgebra.polynomialTensorDesc`. -/
theorem exists_covering_forall_pderiv_mem (X : Cᵒᵖ)
    (q : kernelIdeal (polynomialEvaluation J A B E a e) X)
    (h : tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
      (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafDesc J A B E a e) X
      ((polynomialUnit J A E).app X (q : (polynomialPresheaf J A E).obj X)) = 0) :
    ∃ S : Sieve X.unop, S ∈ J X.unop ∧ ∀ (Y : C) (g : Y ⟶ X.unop), S g →
      ∀ i : E.obj (op Y), MvPolynomial.pderiv i
          ((polynomialPresheaf J A E).map g.op (q : (polynomialPresheaf J A E).obj X)) ∈
        kernelIdeal (polynomialEvaluation J A B E a e) (op Y) := by
  refine ⟨_, vanishingSieve_mem_of_tensorDifferential_eq_zero.{v, u, w, z} J A B E a e X
    (q : (polynomialPresheaf J A E).obj X) h, fun Y g hg ↦ ?_⟩
  refine (conormalToTensorApp_toCotangent_eq_zero_iff J A B E a e (op Y)
    ⟨(polynomialPresheaf J A E).map g.op (q : (polynomialPresheaf J A E).obj X),
      map_kernel (polynomialEvaluation J A B E a e) g.op q.2⟩).mp ?_
  refine Eq.trans (conormalToTensorApp_toCotangent (polynomialEvaluation J A B E a e)
    (polynomialCoefficientMap J A E) (op Y) _) ?_
  refine Eq.trans (tensorPresheaf_map_one_tmul_d J B (polynomialEvaluation J A B E a e)
    (polynomialCoefficientMap J A E) g.op (q : (polynomialPresheaf J A E).obj X)).symm ?_
  exact hg

end Stacks.Sites.FreeAlgebra

end
