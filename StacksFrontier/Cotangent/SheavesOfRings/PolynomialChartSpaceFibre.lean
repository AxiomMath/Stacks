module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionTransfer
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
public import StacksFrontier.Cotangent.ResolutionPointCriterion
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceRingedTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# The fibres of the category of polynomial charts of an algebraic space

Let `X` be an algebraic space over a ring `Λ` and let `C_{X/Λ}` be its category of polynomial
charts, fibred over the small étale site `X_étale`. For an object `U` of `X_étale` the ring
`𝒪_X(U)` of sections over `U` is a `Λ`-algebra through the structure morphism `U ⟶ Spec Λ`, and
the fibre of `C_{X/Λ}` over `U` is the site `C_{𝒪_X(U)/Λ}` of Tag 08PR, whose objects are the
polynomial `Λ`-algebras augmented to `𝒪_X(U)`.

The identification is the `Γ`–`Spec` adjunction: giving a chart `U ⟶ A` over `Spec Λ` with `A`
an affine space is the same as giving a map of `Λ`-algebras from the ring of functions on `A` to
`𝒪_X(U)`, and the affine spaces over `Spec Λ` are exactly the spectra of the polynomial
`Λ`-algebras.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.sectionsAlgebra`: the ring `𝒪_X(U)` as a `Λ`-algebra.
* `AlgebraicGeometry.Space.PolynomialChart.sectionsAlgebraPresheaf`: the presheaf of
  `Λ`-algebras `U ↦ 𝒪_X(U)` on the small étale site of `X`.
* `AlgebraicGeometry.Space.PolynomialChart.specChart`: the polynomial chart on `U` attached to a
  polynomial `Λ`-algebra augmented to `𝒪_X(U)`.
* `AlgebraicGeometry.Space.PolynomialChart.specFunctor`: the functor from `C_{𝒪_X(U)/Λ}` to the
  fibre of `C_{X/Λ}` over `U` built from `specChart`.
* `AlgebraicGeometry.Space.PolynomialChart.standardChartCosimplicialObject`: the cosimplicial
  object `𝐀_{•,U} = Spec(P_{•,U})` of the fibre over `U`, for `P_{•,U}` the standard resolution
  of `𝒪_X(U)` over `Λ`.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.fibreEquivalence`: the fibre of `C_{X/Λ}` over an
  object `U` of `X_étale` is the site `C_{𝒪_X(U)/Λ}` of Tag 08PR.
* `AlgebraicGeometry.Space.PolynomialChart.exists_homotopyEquivalences_standardChartMor`: every
  simplicial set `Mor(𝐀_{•,U}, W)` is homotopy equivalent to a singleton, which is the hypothesis
  the criterion of Tag 08Q9 asks of `𝐀_{•,U}`.

These are the first assertions of Stacks 08VL, which is registered in full, together with the
functoriality in `U` and the computation of `Lπ_!`, in
`StacksFrontier/Cotangent/SheavesOfRings/PolynomialChartSpaceStandardResolution.lean`.

## Implementation notes

The fibre is `CategoryTheory.Functor.Fiber` of the forgetful functor `C_{X/Λ} ⥤ X_étale`: its
objects are the charts `P` together with a proof that `P.openPart = U`, and its morphisms are
the morphisms of charts lying over the identity of `U`. The equivalence is produced from the
functor in the direction of `Spec`, which lands on charts whose underlying object of `X_étale`
is `U` on the nose, so that no transport along an equality of objects is needed; the transport
is confined to essential surjectivity, where the equality can simply be substituted.

The affine space of a chart is given together with an isomorphism to the spectrum of a
polynomial algebra, so its ring of functions is a polynomial algebra only up to isomorphism;
conversely the presentation used to build a chart out of a polynomial algebra is the chosen one
of `CommAlgCat.IsPolynomialAlgebra`, which is an existential statement.

The condition of Tag 08Q9 on `𝐀_{•,U}` is stated in the existential form
`∃ f, SimplicialObject.homotopyEquivalences _ f` rather than through
`Stacks.ChaoticSite.IsPointResolution`, which asks for a small category: the objects of the fibre
form a type one universe above its morphisms, as do those of `C_{𝒪_X(U)/Λ}`. For the same reason
the comparison of morphism complexes is built here from full faithfulness of `fibreEquivalence`
directly instead of `Stacks.ChaoticSite.yonedaCosimplicialFullyFaithfulIso`.

## References

* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08VI](https://stacks.math.columbia.edu/tag/08VI)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

noncomputable section

/-! ### Auxiliary facts about morphisms into affine schemes -/

section Affine

variable {V : Scheme.{u}} {R S : CommRingCat.{u}}

/-- A morphism from a scheme to the spectrum of a ring is recovered from the induced map on
global sections. -/
theorem toSpecΓ_specMap_appTop (f : V ⟶ Spec R) :
    V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The map on global sections induced by the morphism to `Spec R` attached to a ring map
`R ⟶ Γ(V, ⊤)` is that ring map. -/
theorem appTop_toSpecΓ_specMap (g : R ⟶ Γ(V, ⊤)) :
    (Scheme.ΓSpecIso R).inv ≫ (V.toSpecΓ ≫ Spec.map g).appTop = g := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A ring map `R ⟶ Γ(V, ⊤)` is determined by the morphism `V ⟶ Spec R` it induces. -/
theorem toSpecΓ_specMap_injective {g h : R ⟶ Γ(V, ⊤)}
    (e : V.toSpecΓ ≫ Spec.map g = V.toSpecΓ ≫ Spec.map h) : g = h := by
  rw [← appTop_toSpecΓ_specMap g, ← appTop_toSpecΓ_specMap h, e]

/-- Two ring maps inducing the same morphism of spectra are equal. -/
theorem specMap_injective {f g : R ⟶ S} (h : Spec.map f = Spec.map g) : f = g := by
  have h' : Scheme.Spec.map f.op = Scheme.Spec.map g.op := h
  exact Quiver.Hom.op_inj (Scheme.Spec.map_injective h')

/-- The ring map inducing a given morphism between the spectra of two rings. -/
def specPreimage (f : Spec S ⟶ Spec R) : R ⟶ S :=
  (Scheme.Spec.preimage (X := op S) (Y := op R) f).unop

/-- The spectrum of the ring map underlying a morphism of spectra is that morphism. -/
theorem specMap_specPreimage (f : Spec S ⟶ Spec R) : Spec.map (specPreimage f) = f :=
  Scheme.Spec.map_preimage (X := op S) (Y := op R) f

/-- Equal maps of rings agree on elements. -/
theorem commRingCat_apply_congr {f g : R ⟶ S} (h : f = g) (x : R) : f.hom x = g.hom x :=
  congrArg (fun φ : R ⟶ S => φ.hom x) h

end Affine

/-! ### Chosen presentations of polynomial algebras -/

variable (Λ : Type u) [CommRing Λ]

/-- Equal maps of `Λ`-algebras agree on elements. -/
theorem commAlgCat_apply_congr {A C : CommAlgCat.{u} Λ} {f g : A ⟶ C} (h : f = g) (x : A) :
    f.hom x = g.hom x :=
  congrArg (fun φ : A ⟶ C => φ.hom x) h

/-- A map of `Λ`-algebras between the carriers of two objects of `CommAlgCat Λ`, as a morphism
of that category. -/
def ofAlgHom {A C : CommAlgCat.{u} Λ} (f : (A : Type u) →ₐ[Λ] (C : Type u)) : A ⟶ C :=
  ConcreteCategory.ofHom f

/-- A chosen set of variables presenting a polynomial `Λ`-algebra. -/
def polyIndex {P : CommAlgCat.{u} Λ} (hP : CommAlgCat.IsPolynomialAlgebra Λ P) : Type u :=
  hP.choose

/-- A chosen presentation of a polynomial `Λ`-algebra as a multivariate polynomial algebra. -/
def polyEquiv {P : CommAlgCat.{u} Λ} (hP : CommAlgCat.IsPolynomialAlgebra Λ P) :
    MvPolynomial (polyIndex Λ hP) Λ ≃ₐ[Λ] P :=
  hP.choose_spec.some

/-- The spectrum of a polynomial `Λ`-algebra, presented as an affine space over `Spec Λ`
through the chosen presentation. -/
def polySpecIso {P : CommAlgCat.{u} Λ} (hP : CommAlgCat.IsPolynomialAlgebra Λ P) :
    Spec (CommRingCat.of (P : Type u)) ≅
      Spec (CommRingCat.of (MvPolynomial (polyIndex Λ hP) Λ)) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso (polyEquiv Λ hP).toRingEquiv).op

/-- Read through the chosen presentation, the structural arrow of the spectrum of a polynomial
`Λ`-algebra is the spectrum of the structure map of the algebra. -/
theorem polySpecIso_hom_comp {P : CommAlgCat.{u} Λ} (hP : CommAlgCat.IsPolynomialAlgebra Λ P) :
    (polySpecIso Λ hP).hom ≫ Scheme.Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Λ →+* MvPolynomial (polyIndex Λ hP) Λ)).op =
      Spec.map (CommRingCat.ofHom (algebraMap Λ (P : Type u))) := by
  have h : CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial (polyIndex Λ hP) Λ) ≫
      (RingEquiv.toCommRingCatIso (polyEquiv Λ hP).toRingEquiv).hom =
      CommRingCat.ofHom (algebraMap Λ (P : Type u)) := by
    ext r
    exact (polyEquiv Λ hP).commutes r
  change Spec.map (RingEquiv.toCommRingCatIso (polyEquiv Λ hP).toRingEquiv).hom ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : Λ →+* _)) = _
  rw [← Spec.map_comp, h]

/-! ### The `Λ`-algebra of sections over an object of the small étale site -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)

/-- The structure morphism of an object `U` of the small étale site of `X`, read on global
sections as a map of rings `Λ ⟶ 𝒪_X(U)`. -/
def sectionsRingHom (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    CommRingCat.of Λ ⟶ Γ((smallEtaleToScheme Λ B hS X).obj U, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ (openPartToBase Λ B hS X U).appTop

/-- The ring of sections over an object `U` of the small étale site of `X` is a `Λ`-algebra
through the structure morphism `U ⟶ Spec Λ`. -/
instance sectionsAlgebraStructure (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    Algebra Λ (Γ((smallEtaleToScheme Λ B hS X).obj U, ⊤) : Type u) :=
  (sectionsRingHom Λ B hS X U).hom.toAlgebra

/-- The ring `𝒪_X(U)` of sections over an object `U` of the small étale site of `X`, as a
`Λ`-algebra. -/
def sectionsAlgebra (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) : CommAlgCat.{u} Λ :=
  CommAlgCat.of Λ (Γ((smallEtaleToScheme Λ B hS X).obj U, ⊤) : Type u)

/-- The structure map of the `Λ`-algebra `𝒪_X(U)` is the structure morphism of `U`. -/
theorem ofHom_algebraMap_sectionsAlgebra (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    CommRingCat.ofHom (algebraMap Λ (sectionsAlgebra Λ B hS X U : Type u)) =
      sectionsRingHom Λ B hS X U :=
  rfl

/-- Restriction along an arrow of the small étale site is compatible with the structure maps
from `Λ`. -/
theorem sectionsRingHom_comp {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (f : U ⟶ V) :
    sectionsRingHom Λ B hS X V ≫ ((smallEtaleToScheme Λ B hS X).map f).appTop =
      sectionsRingHom Λ B hS X U := by
  rw [sectionsRingHom, sectionsRingHom, Category.assoc, ← Scheme.Hom.comp_appTop,
    map_comp_openPartToBase]

/-- Restriction of sections along an arrow of the small étale site, as a map of
`Λ`-algebras. -/
def sectionsAlgebraRestrict {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (f : U ⟶ V) :
    sectionsAlgebra Λ B hS X V ⟶ sectionsAlgebra Λ B hS X U :=
  ofAlgHom Λ
    { __ := ((smallEtaleToScheme Λ B hS X).map f).appTop.hom
      commutes' := fun r => commRingCat_apply_congr (sectionsRingHom_comp Λ B hS X f) r }

/-- The presheaf of `Λ`-algebras `U ↦ 𝒪_X(U)` on the small étale site of `X`. -/
def sectionsAlgebraPresheaf :
    (SmallEtale B (Spec (CommRingCat.of Λ)) hS X)ᵒᵖ ⥤ CommAlgCat.{u} Λ where
  obj U := sectionsAlgebra Λ B hS X U.unop
  map f := sectionsAlgebraRestrict Λ B hS X f.unop
  map_id U := by
    refine CommAlgCat.hom_ext (AlgHom.ext fun x => ?_)
    change (((smallEtaleToScheme Λ B hS X).map (𝟙 U.unop)).appTop).hom x = x
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
    rfl
  map_comp f g := by
    refine CommAlgCat.hom_ext (AlgHom.ext fun x => ?_)
    change (((smallEtaleToScheme Λ B hS X).map (g.unop ≫ f.unop)).appTop).hom x =
      (((smallEtaleToScheme Λ B hS X).map g.unop).appTop).hom
        ((((smallEtaleToScheme Λ B hS X).map f.unop).appTop).hom x)
    rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

/-! ### The chart attached to a polynomial augmentation -/

variable (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)
  (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)

/-- The map of rings underlying an augmentation `P ⟶ 𝒪_X(U)`. -/
def augmentationRingHom {P : CommAlgCat.{u} Λ} (α : P ⟶ sectionsAlgebra Λ B hS X U) :
    CommRingCat.of (P : Type u) ⟶ Γ((smallEtaleToScheme Λ B hS X).obj U, ⊤) :=
  CommRingCat.ofHom α.hom.toRingHom

/-- An augmentation `P ⟶ 𝒪_X(U)` is a map of `Λ`-algebras. -/
theorem algebraMap_comp_augmentationRingHom {P : CommAlgCat.{u} Λ}
    (α : P ⟶ sectionsAlgebra Λ B hS X U) :
    CommRingCat.ofHom (algebraMap Λ (P : Type u)) ≫ augmentationRingHom Λ B hS X U α =
      sectionsRingHom Λ B hS X U := by
  ext r
  exact α.hom.commutes r

/-- The morphism `U ⟶ Spec P` attached, by the `Γ`–`Spec` adjunction, to an augmentation
`P ⟶ 𝒪_X(U)`. -/
def specAugmentation {P : CommAlgCat.{u} Λ} (α : P ⟶ sectionsAlgebra Λ B hS X U) :
    (smallEtaleToScheme Λ B hS X).obj U ⟶ Spec (CommRingCat.of (P : Type u)) :=
  ((smallEtaleToScheme Λ B hS X).obj U).toSpecΓ ≫ Spec.map (augmentationRingHom Λ B hS X U α)

/-- The morphism `U ⟶ Spec P` attached to an augmentation `P ⟶ 𝒪_X(U)` lies over
`Spec Λ`. -/
theorem specAugmentation_comp {P : CommAlgCat.{u} Λ} (α : P ⟶ sectionsAlgebra Λ B hS X U) :
    specAugmentation Λ B hS X U α ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ (P : Type u))) =
      openPartToBase Λ B hS X U := by
  rw [specAugmentation, Category.assoc, ← Spec.map_comp, algebraMap_comp_augmentationRingHom,
    sectionsRingHom, toSpecΓ_specMap_appTop]

/-- The polynomial chart on `U` attached to an object of the site
`C_{𝒪_X(U)/Λ}`: the spectrum of the polynomial algebra, together with the morphism from `U`
determined by the augmentation. -/
def specChart (a : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)) :
    PolynomialChart Λ B hS X hX where
  openPart := U
  variableIndex := polyIndex Λ a.unop.property
  affineSpace := Spec (CommRingCat.of (a.unop.obj.left : Type u))
  affineEquiv := polySpecIso Λ a.unop.property
  toAffine := specAugmentation Λ B hS X U a.unop.obj.hom
  comm := by
    rw [polySpecIso_hom_comp]
    exact specAugmentation_comp Λ B hS X U a.unop.obj.hom

/-- The structural arrow to `Spec Λ` of the chart attached to an object of `C_{𝒪_X(U)/Λ}` is
the spectrum of the structure map of its algebra. -/
theorem specChart_toBase (a : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)) :
    (specChart Λ B hS X hX U a).toBase =
      Spec.map (CommRingCat.ofHom (algebraMap Λ (a.unop.obj.left : Type u))) :=
  polySpecIso_hom_comp Λ a.unop.property

/-- The map of rings underlying a morphism of the site `C_{𝒪_X(U)/Λ}`. -/
def siteRingHom {a b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)} (f : a ⟶ b) :
    CommRingCat.of (b.unop.obj.left : Type u) ⟶ CommRingCat.of (a.unop.obj.left : Type u) :=
  CommRingCat.ofHom f.unop.hom.left.hom.toRingHom

/-- A morphism of the site `C_{𝒪_X(U)/Λ}` is compatible with the augmentations. -/
theorem siteRingHom_comp_augmentation
    {a b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)} (f : a ⟶ b) :
    siteRingHom Λ B hS X U f ≫ augmentationRingHom Λ B hS X U a.unop.obj.hom =
      augmentationRingHom Λ B hS X U b.unop.obj.hom := by
  ext x
  exact commAlgCat_apply_congr Λ (Over.w f.unop.hom) x

/-- A morphism of the site `C_{𝒪_X(U)/Λ}` is a map of `Λ`-algebras. -/
theorem algebraMap_comp_siteRingHom
    {a b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)} (f : a ⟶ b) :
    CommRingCat.ofHom (algebraMap Λ (b.unop.obj.left : Type u)) ≫ siteRingHom Λ B hS X U f =
      CommRingCat.ofHom (algebraMap Λ (a.unop.obj.left : Type u)) := by
  ext r
  exact f.unop.hom.left.hom.commutes r

/-- The morphism of polynomial charts attached to a morphism of the site `C_{𝒪_X(U)/Λ}`. -/
def specChartHom {a b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)} (f : a ⟶ b) :
    specChart Λ B hS X hX U a ⟶ specChart Λ B hS X hX U b where
  openMap := 𝟙 U
  affine := Spec.map (siteRingHom Λ B hS X U f)
  map_comm := by
    change specAugmentation Λ B hS X U a.unop.obj.hom ≫ Spec.map (siteRingHom Λ B hS X U f) =
      (smallEtaleToScheme Λ B hS X).map (𝟙 U) ≫ specAugmentation Λ B hS X U b.unop.obj.hom
    rw [CategoryTheory.Functor.map_id, Category.id_comp, specAugmentation, specAugmentation,
      Category.assoc, ← Spec.map_comp, siteRingHom_comp_augmentation]
  base_comm := by
    change Spec.map (siteRingHom Λ B hS X U f) ≫ (specChart Λ B hS X hX U b).toBase =
      (specChart Λ B hS X hX U a).toBase
    rw [specChart_toBase, specChart_toBase, ← Spec.map_comp, algebraMap_comp_siteRingHom]

/-- A morphism of charts attached to a morphism of the site `C_{𝒪_X(U)/Λ}` lies over the
identity of `U`. -/
theorem specChartHom_isHomLift
    {a b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)} (f : a ⟶ b) :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsHomLift (𝟙 U)
      (specChartHom Λ B hS X hX U f) :=
  Functor.IsHomLift.map (specChartHom Λ B hS X hX U f)

/-- The functor from the site `C_{𝒪_X(U)/Λ}` to the fibre over `U` of the category of polynomial
charts of `X`. -/
def specFunctor : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U) ⥤
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).Fiber U where
  obj a := ⟨specChart Λ B hS X hX U a, rfl⟩
  map f := ⟨specChartHom Λ B hS X hX U f, specChartHom_isHomLift Λ B hS X hX U f⟩
  map_id a := by
    refine Functor.Fiber.hom_ext (Hom.ext rfl ?_)
    change Spec.map (siteRingHom Λ B hS X U (𝟙 a)) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    refine Functor.Fiber.hom_ext (Hom.ext (Category.id_comp _).symm ?_)
    change Spec.map (siteRingHom Λ B hS X U (f ≫ g)) =
      Spec.map (siteRingHom Λ B hS X U f) ≫ Spec.map (siteRingHom Λ B hS X U g)
    rw [← Spec.map_comp]
    rfl

/-! ### The functor is fully faithful -/

/-- A morphism of the site `C_{𝒪_X(U)/Λ}` is determined by the morphism of charts it induces,
because `Spec` is faithful. -/
instance specFunctor_faithful : (specFunctor Λ B hS X hX U).Faithful where
  map_injective {a b} {f g} h := by
    have h1 : specChartHom Λ B hS X hX U f = specChartHom Λ B hS X hX U g :=
      congrArg Functor.Fiber.fiberInclusion.map h
    have h2 : Spec.map (siteRingHom Λ B hS X U f) = Spec.map (siteRingHom Λ B hS X U g) :=
      congrArg Hom.affine h1
    have h3 := specMap_injective h2
    refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      (CommAlgCat.hom_ext (AlgHom.ext fun x => ?_))))
    exact commRingCat_apply_congr h3 x

/-- Every morphism of the fibre over `U` comes from a morphism of the site `C_{𝒪_X(U)/Λ}`,
because `Spec` is full and a morphism to an affine scheme over `Spec Λ` is a map of
`Λ`-algebras on global sections. -/
instance specFunctor_full : (specFunctor Λ B hS X hX U).Full where
  map_surjective {a b} φ := by
    obtain ⟨ψ, hlift, rfl⟩ :
        ∃ (ψ : specChart Λ B hS X hX U a ⟶ specChart Λ B hS X hX U b)
          (h : (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
            (hX := hX)).IsHomLift (𝟙 U) ψ), φ = ⟨ψ, h⟩ :=
      ⟨φ.1, φ.2, rfl⟩
    have hopen : ψ.openMap = 𝟙 U :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _
        (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX))
        (specChart Λ B hS X hX U a) (specChart Λ B hS X hX U b) (𝟙 U) ψ hlift).symm
    obtain ⟨g, hgspec⟩ : ∃ g : CommRingCat.of (b.unop.obj.left : Type u) ⟶
        CommRingCat.of (a.unop.obj.left : Type u), Spec.map g = ψ.affine :=
      ⟨specPreimage ψ.affine, specMap_specPreimage ψ.affine⟩
    have hbc := ψ.base_comm
    rw [specChart_toBase, specChart_toBase] at hbc
    have hbase : CommRingCat.ofHom (algebraMap Λ (b.unop.obj.left : Type u)) ≫ g =
        CommRingCat.ofHom (algebraMap Λ (a.unop.obj.left : Type u)) := by
      refine specMap_injective ?_
      rw [Spec.map_comp, hgspec]
      exact hbc
    have hmc : specAugmentation Λ B hS X U a.unop.obj.hom ≫ ψ.affine =
        (smallEtaleToScheme Λ B hS X).map (𝟙 U) ≫
          specAugmentation Λ B hS X U b.unop.obj.hom := by
      rw [← hopen]
      exact ψ.map_comm
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at hmc
    have haug : g ≫ augmentationRingHom Λ B hS X U a.unop.obj.hom =
        augmentationRingHom Λ B hS X U b.unop.obj.hom := by
      refine toSpecΓ_specMap_injective ?_
      rw [Spec.map_comp, ← Category.assoc, hgspec]
      exact hmc
    refine ⟨(ObjectProperty.homMk (Over.homMk (ofAlgHom Λ
      ({ __ := g.hom, commutes' := fun r => commRingCat_apply_congr hbase r } :
        (b.unop.obj.left : Type u) →ₐ[Λ] (a.unop.obj.left : Type u))) ?_)).op, ?_⟩
    · exact CommAlgCat.hom_ext (AlgHom.ext fun x => commRingCat_apply_congr haug x)
    · exact Functor.Fiber.hom_ext (Hom.ext hopen.symm hgspec)

/-! ### The functor is essentially surjective -/

/-- The affine space of a polynomial chart is an affine scheme: it is isomorphic to the
spectrum of a polynomial algebra. -/
instance isAffine_affineSpace (P : PolynomialChart Λ B hS X hX) : IsAffine P.affineSpace :=
  IsAffine.of_isIso P.affineEquiv.hom

/-- The ring of global functions on the affine space of a polynomial chart is a `Λ`-algebra
through the structural arrow of the chart. -/
instance chartAlgebraStructure (P : PolynomialChart Λ B hS X hX) :
    Algebra Λ (Γ(P.affineSpace, ⊤) : Type u) :=
  ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop).hom.toAlgebra

/-- The `Λ`-algebra of global functions on the affine space of a polynomial chart. -/
def chartAlgebra (P : PolynomialChart Λ B hS X hX) : CommAlgCat.{u} Λ :=
  CommAlgCat.of Λ (Γ(P.affineSpace, ⊤) : Type u)

/-- The structure map of the `Λ`-algebra of functions on the affine space of a chart is the
structural arrow of the chart. -/
theorem ofHom_algebraMap_chartAlgebra (P : PolynomialChart Λ B hS X hX) :
    CommRingCat.ofHom (algebraMap Λ (chartAlgebra Λ B hS X hX P : Type u)) =
      (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop :=
  rfl

/-- The augmentation `Γ(A, 𝒪_A) ⟶ 𝒪_X(U)` of a polynomial chart `U ⟶ A`, given by pullback of
functions along the chart map. -/
def chartAugmentation (P : PolynomialChart Λ B hS X hX) :
    chartAlgebra Λ B hS X hX P ⟶ sectionsAlgebra Λ B hS X P.openPart :=
  ofAlgHom Λ
    { __ := P.toAffine.appTop.hom
      commutes' := fun r => by
        have h : (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ (P.toAffine ≫ P.toBase).appTop =
            sectionsRingHom Λ B hS X P.openPart := by
          rw [show P.toAffine ≫ P.toBase = openPartToBase Λ B hS X P.openPart from P.comm]
          rfl
        exact commRingCat_apply_congr h r }

/-- The presentation, through the affine space of a chart, of its ring of functions as a
polynomial algebra. -/
def chartAlgebraIso (P : PolynomialChart Λ B hS X hX) :
    CommRingCat.of (MvPolynomial P.variableIndex Λ) ≅ Γ(P.affineSpace, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial P.variableIndex Λ))).symm ≪≫
    Scheme.Γ.mapIso P.affineEquiv.op

/-- The presentation of the ring of functions on the affine space of a chart is a map of
`Λ`-algebras. -/
theorem chartAlgebraIso_hom_comp (P : PolynomialChart Λ B hS X hX) :
    CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ) ≫
        (chartAlgebraIso Λ B hS X hX P).hom =
      CommRingCat.ofHom (algebraMap Λ (chartAlgebra Λ B hS X hX P : Type u)) := by
  rw [ofHom_algebraMap_chartAlgebra]
  change CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial P.variableIndex Λ))).inv ≫
        P.affineEquiv.hom.appTop =
    (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop]
  rfl

/-- The presentation of the ring of functions on the affine space of a chart as a polynomial
algebra, as an equivalence of `Λ`-algebras. -/
def chartAlgebraAlgEquiv (P : PolynomialChart Λ B hS X hX) :
    MvPolynomial P.variableIndex Λ ≃ₐ[Λ] (chartAlgebra Λ B hS X hX P : Type u) :=
  { (chartAlgebraIso Λ B hS X hX P).commRingCatIsoToRingEquiv with
    commutes' := fun r =>
      commRingCat_apply_congr (chartAlgebraIso_hom_comp Λ B hS X hX P) r }

/-- The ring of functions on the affine space of a polynomial chart is a polynomial
`Λ`-algebra. -/
theorem isPolynomialAlgebra_chartAlgebra (P : PolynomialChart Λ B hS X hX) :
    CommAlgCat.IsPolynomialAlgebra Λ (chartAlgebra Λ B hS X hX P) :=
  ⟨P.variableIndex, ⟨chartAlgebraAlgEquiv Λ B hS X hX P⟩⟩

/-- The object of the site `C_{𝒪_X(U)/Λ}` attached to a polynomial chart on `U`. -/
def chartObject (P : PolynomialChart Λ B hS X hX) :
    CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X P.openPart) :=
  op ⟨Over.mk (chartAugmentation Λ B hS X hX P),
    isPolynomialAlgebra_chartAlgebra Λ B hS X hX P⟩

/-- The comparison from the chart attached to the augmentation of a polynomial chart `P` to `P`
itself, given by the identification of the affine space of `P` with the spectrum of its ring of
functions. -/
def chartSpecHom (P : PolynomialChart Λ B hS X hX) :
    specChart Λ B hS X hX P.openPart (chartObject Λ B hS X hX P) ⟶ P where
  openMap := 𝟙 P.openPart
  affine := P.affineSpace.isoSpec.inv
  map_comm := by
    change (((smallEtaleToScheme Λ B hS X).obj P.openPart).toSpecΓ ≫
        Spec.map P.toAffine.appTop) ≫ P.affineSpace.isoSpec.inv =
      (smallEtaleToScheme Λ B hS X).map (𝟙 P.openPart) ≫ P.toAffine
    rw [CategoryTheory.Functor.map_id, Category.id_comp, ← Scheme.toSpecΓ_naturality,
      Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  base_comm := by
    rw [specChart_toBase]
    change P.affineSpace.isoSpec.inv ≫ P.toBase =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop)
    rw [Iso.inv_comp_eq, Scheme.isoSpec_hom]
    exact (toSpecΓ_specMap_appTop P.toBase).symm

/-- The comparison from a polynomial chart `P` to the chart attached to its augmentation,
inverse to `chartSpecHom`. -/
def chartSpecInv (P : PolynomialChart Λ B hS X hX) :
    P ⟶ specChart Λ B hS X hX P.openPart (chartObject Λ B hS X hX P) where
  openMap := 𝟙 P.openPart
  affine := P.affineSpace.isoSpec.hom
  map_comm := by
    change P.toAffine ≫ P.affineSpace.isoSpec.hom =
      (smallEtaleToScheme Λ B hS X).map (𝟙 P.openPart) ≫
        ((smallEtaleToScheme Λ B hS X).obj P.openPart).toSpecΓ ≫
          Spec.map P.toAffine.appTop
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_naturality]
  base_comm := by
    rw [specChart_toBase]
    change P.affineSpace.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ P.toBase.appTop) = P.toBase
    rw [Scheme.isoSpec_hom]
    exact toSpecΓ_specMap_appTop P.toBase

/-- The comparison to a polynomial chart from the chart attached to its augmentation lies over
the identity. -/
theorem chartSpecHom_isHomLift (P : PolynomialChart Λ B hS X hX) :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsHomLift (𝟙 P.openPart)
      (chartSpecHom Λ B hS X hX P) :=
  Functor.IsHomLift.map (chartSpecHom Λ B hS X hX P)

/-- The comparison from a polynomial chart to the chart attached to its augmentation lies over
the identity. -/
theorem chartSpecInv_isHomLift (P : PolynomialChart Λ B hS X hX) :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsHomLift (𝟙 P.openPart)
      (chartSpecInv Λ B hS X hX P) :=
  Functor.IsHomLift.map (chartSpecInv Λ B hS X hX P)

/-- Every object of the fibre over `U` is isomorphic to the chart attached to its own
augmentation. -/
def chartSpecIso (P : PolynomialChart Λ B hS X hX) :
    (specFunctor Λ B hS X hX P.openPart).obj (chartObject Λ B hS X hX P) ≅
      (⟨P, rfl⟩ : (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).Fiber
        P.openPart) where
  hom := ⟨chartSpecHom Λ B hS X hX P, chartSpecHom_isHomLift Λ B hS X hX P⟩
  inv := ⟨chartSpecInv Λ B hS X hX P, chartSpecInv_isHomLift Λ B hS X hX P⟩
  hom_inv_id :=
    Functor.Fiber.hom_ext (Hom.ext (Category.comp_id _) P.affineSpace.isoSpec.inv_hom_id)
  inv_hom_id :=
    Functor.Fiber.hom_ext (Hom.ext (Category.comp_id _) P.affineSpace.isoSpec.hom_inv_id)

/-- Every object of the fibre over `U` comes from an object of the site `C_{𝒪_X(U)/Λ}`, namely
from its own ring of functions with its augmentation. -/
instance specFunctor_essSurj : (specFunctor Λ B hS X hX U).EssSurj where
  mem_essImage Z := by
    obtain ⟨P, rfl⟩ := Z
    exact ⟨chartObject Λ B hS X hX P, ⟨chartSpecIso Λ B hS X hX P⟩⟩

/-- The functor from the site `C_{𝒪_X(U)/Λ}` to the fibre over `U` is an equivalence. -/
instance specFunctor_isEquivalence : (specFunctor Λ B hS X hX U).IsEquivalence where

/-- The fibre of the category `C_{X/Λ}` of polynomial charts of an algebraic space `X` over an
object `U` of the small étale site of `X` is the site `C_{𝒪_X(U)/Λ}` of Tag 08PR. This is the
first assertion of Stacks 08VL, which is registered in full at
`standardResolutionChart_computes_derivedAbelianLowerShriek`. -/
def fibreEquivalence :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).Fiber U ≌
      CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U) :=
  (specFunctor Λ B hS X hX U).asEquivalence.symm

/-! ### The standard resolution as a cosimplicial object of the fibre -/

/-- The cosimplicial object `𝐀_{•,U} = Spec(P_{•,U})` of the fibre of `C_{X/Λ}` over `U`, where
`P_{•,U}` is the standard resolution of `𝒪_X(U)` over `Λ`. -/
def standardChartCosimplicialObject :
    CosimplicialObject
      ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).Fiber U) :=
  CommAlgCat.resolutionCosimplicialObject
      (CommAlgCat.standardResolution.{u, u} Λ (sectionsAlgebra Λ B hS X U)).hom
      (CommAlgCat.standardResolution_isResolution.{u, u} Λ
        (sectionsAlgebra Λ B hS X U)).isPolynomialAlgebra ⋙
    (fibreEquivalence Λ B hS X hX U).inverse

/-- For every object `W` of the fibre of `C_{X/Λ}` over `U` the simplicial set
`Mor(𝐀_{•,U}, W)` is homotopy equivalent to the constant simplicial set on a singleton, which is
the hypothesis the criterion of Tag 08Q9 asks of the cosimplicial object `𝐀_{•,U}`. It holds
because `fibreEquivalence` carries `𝐀_{•,U}` to the cosimplicial object of the standard
resolution of `𝒪_X(U)` over `Λ` in the site `C_{𝒪_X(U)/Λ}`, for which it is Tag 08PT. -/
theorem exists_homotopyEquivalences_standardChartMor
    (W : (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).Fiber U) :
    ∃ f : (standardChartCosimplicialObject Λ B hS X hX U).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f := by
  obtain ⟨f, hf⟩ := CommAlgCat.exists_homotopyEquivalences_standardResolutionMor Λ
    (sectionsAlgebra Λ B hS X U) ((fibreEquivalence Λ B hS X hX U).functor.obj W)
  have γ : standardChartCosimplicialObject Λ B hS X hX U ⋙
      (fibreEquivalence Λ B hS X hX U).functor ≅ _ :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (fibreEquivalence Λ B hS X hX U).counitIso ≪≫
        Functor.rightUnitor _
  have α : (standardChartCosimplicialObject Λ B hS X hX U).op ⋙ yoneda.obj W ≅
      (standardChartCosimplicialObject Λ B hS X hX U ⋙
          (fibreEquivalence Λ B hS X hX U).functor).op ⋙
        yoneda.obj ((fibreEquivalence Λ B hS X hX U).functor.obj W) :=
    NatIso.ofComponents
      (fun _ => Equiv.toIso (fibreEquivalence Λ B hS X hX U).fullyFaithfulFunctor.homEquiv)
      (by intro _ _ _; ext x; simp)
  exact ⟨(α ≪≫ (Functor.isoWhiskerRight (NatIso.op γ)
    (yoneda.obj ((fibreEquivalence Λ B hS X hX U).functor.obj W))).symm).hom ≫ f,
    SimplicialObject.homotopyEquivalences_iso_comp _ hf⟩

end

end AlgebraicGeometry.Space.PolynomialChart

end
