module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification

/-!
# Morphisms into a space affine over the base are maps of direct-image algebras

Let `X` be an algebraic space over `S`, let `π : Z ⟶ X` be an affine morphism of algebraic
spaces and let `T` be an arbitrary algebraic space over `X`.  This file proves that

`Mor_X(T, Z) ⟶ Hom_{𝒪_X}(π_* 𝒪_Z, (T ⟶ X)_* 𝒪_T)`,  `u ↦ u_*`,

is a bijection, `AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`: the mapping
property of the relative spectrum `Z = \underline{Spec}_X(π_* 𝒪_Z)`.

## Main results

* `AlgebraicGeometry.Space.eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable` and
  `AlgebraicGeometry.Space.exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable`: the two
  halves of the bijection for a source representable over `X`.
* `AlgebraicGeometry.Space.mono_pushforwardAlgebraMap_objectPointOverHom`: a surjective étale atlas
  `U ⟶ T` induces a monomorphism `T_* 𝒪_T ⟶ U_* 𝒪_U`.
* `AlgebraicGeometry.Space.eq_of_pushforwardAlgebraMap_eq` and
  `AlgebraicGeometry.Space.exists_pushforwardAlgebraMap_eq_of_affineOver`: the two halves for an
  arbitrary source.
* `AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`: the bijection.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representable sources -/

/-- The structure morphism of an algebraic space affine over `X` is representable. -/
private theorem relativelyRepresentable_of_affineOver {X : AlgebraicSpaces B S hS}
    (Z : AffineOver B S hS X) : yoneda.relativelyRepresentable Z.obj.hom.hom :=
  relativelyRepresentable_of_isAffineHom B S hS Z.obj.hom Z.property

/-- Two morphisms over `X`, from an algebraic space representable over `X` to one affine over
`X`, with the same direct-image map are equal. -/
theorem eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable {X : AlgebraicSpaces B S hS}
    {Y : Over X} (hY : yoneda.relativelyRepresentable Y.hom.hom) (Z : AffineOver B S hS X)
    {f g : Y ⟶ Z.obj}
    (e : pushforwardAlgebraMap B S hS f = pushforwardAlgebraMap B S hS g) : f = g := by
  have hZ := relativelyRepresentable_of_affineOver B S hS Z
  have e' : pushforwardRingMap B S hS f = pushforwardRingMap B S hS g :=
    congrArg (fun m => m.right) e
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  refine hom_ext_of_affineChartBaseChange B S hS Y hY Z.obj.left.property.isSheaf ?_
  intro V hV
  rw [← yoneda_map_smallBaseChangeOverMap_fst B S hS f hY hZ V,
    ← yoneda_map_smallBaseChangeOverMap_fst B S hS g hY hZ V,
    smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq B S hS Z f g hY hZ e' V hV]

/-- From a source representable over `X` into a target affine over `X`, every morphism of
direct-image algebras is the direct-image map of a morphism over `X`. -/
theorem exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable {X : AlgebraicSpaces B S hS}
    {Y : Over X} (hY : yoneda.relativelyRepresentable Y.hom.hom) (Z : AffineOver B S hS X)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y) :
    ∃ f : Y ⟶ Z.obj, pushforwardAlgebraMap B S hS f = φ := by
  have hZ := relativelyRepresentable_of_affineOver B S hS Z
  obtain ⟨d, hdover, hdchart⟩ := exists_overHom_of_algebraHom B S hS Z hY hZ φ
  exact ⟨Over.homMk (ObjectProperty.homMk d) (ObjectProperty.hom_ext _ hdover),
    pushforwardAlgebraMap_eq_of_affineChartHom B S hS Z _ hY hZ φ hdchart⟩

/-! ### Objects of the site over an algebraic space over `X` -/

variable {B S hS} in
/-- A morphism `a : U ⟶ T` from an object of the site to an algebraic space, as a morphism of
algebraic spaces. -/
abbrev objectPointHom {T : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ T.1) :
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ T :=
  ObjectProperty.homMk a

variable {B S hS} in
/-- An object `U` of the site with a morphism `a : U ⟶ T` to an algebraic space over `X`, as an
algebraic space over `X`. -/
abbrev objectPointOver {X : AlgebraicSpaces B S hS} (T : Over X) {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ T.left.1) : Over X :=
  Over.mk (objectPointHom a ≫ T.hom)

variable {B S hS} in
/-- The morphism `a : U ⟶ T` over `X`. -/
abbrev objectPointOverHom {X : AlgebraicSpaces B S hS} (T : Over X) {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ T.left.1) : objectPointOver T a ⟶ T :=
  Over.homMk (objectPointHom a)

/-- An object of the site over an algebraic space over `X` is representable over `X`. -/
theorem relativelyRepresentable_objectPointOver {X : AlgebraicSpaces B S hS} (T : Over X)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ T.left.1) :
    yoneda.relativelyRepresentable (objectPointOver T a).hom.hom :=
  relativelyRepresentable_of_isAlgebraicSpace B S hS X.property _

/-- The structure map `𝒪_T ⟶ a_* 𝒪_U` of a surjective étale atlas `a : U ⟶ T` is injective on
the sections over every étale chart of `T`. -/
theorem injective_fSharp_app {T : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ T.1)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) (V : SmallEtale B S hS T.1) :
    Function.Injective
      ((smallEtaleRingedToposHom B S hS (objectPointHom a)).fSharp.hom.app (op V)) := by
  have hw : yoneda.relativelyRepresentable (Over.mk (objectPointHom a)).hom.hom := hetale.rep
  have key := fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (Over.mk (objectPointHom a)) hw V
  have : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hw.snd V.1.hom)) :=
    hsurj.property_snd V.1.hom
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (hw.snd V.1.hom)) :=
    hetale.property_snd V.1.hom
  have hinj := Scheme.Hom.appTop_injective_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map (hw.snd V.1.hom))
  refine fun x y hxy ↦ hinj ?_
  rw [← key]
  exact congrArg
    (fun m => (pushforwardAlgebraSectionsIso B S hS (Over.mk (objectPointHom a)) hw V).hom m)
    hxy

/-- The structure map `𝒪_T ⟶ a_* 𝒪_U` of a surjective étale atlas `a : U ⟶ T` is a
monomorphism of sheaves of commutative rings on the small étale site of `T`. -/
theorem mono_fSharp_of_etale_atlas {T : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ T.1)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Mono (smallEtaleRingedToposHom B S hS (objectPointHom a)).fSharp := by
  have happ : ∀ V : (SmallEtale B S hS T.1)ᵒᵖ,
      Mono ((smallEtaleRingedToposHom B S hS (objectPointHom a)).fSharp.hom.app V) := by
    rintro ⟨V⟩
    exact ConcreteCategory.mono_of_injective _ (injective_fSharp_app B S hS a hsurj hetale V)
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _ (h := NatTrans.mono_of_mono_app _)

/-- The direct-image map of a morphism whose structure map is a monomorphism is a
monomorphism. -/
theorem mono_pushforwardAlgMap {A₁ A₂ X : AlgebraicSpaces B S hS} (a : A₁ ⟶ A₂) (y : A₂ ⟶ X)
    (ha : Mono (smallEtaleRingedToposHom B S hS a).fSharp) :
    Mono (pushforwardAlgMap B S hS a y) := by
  have := Functor.preservesMonomorphisms_of_adjunction
    (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (smallEtaleRingedToposHom B S hS y).toToposHom)
  have h1 : Mono ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS y).toToposHom).map
      (smallEtaleRingedToposHom B S hS a).fSharp) := Functor.map_mono _ _
  have h2 : IsIso (Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallEtaleRingedToposHom B S hS y).toToposHom
      (smallEtaleRingedTopos B S hS A₁).O).hom :=
    Iso.isIso_hom _
  have h3 : IsIso ((smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
      (smallEtaleRingedTopos B S hS A₁).O) := inferInstance
  exact mono_comp' h1 (mono_comp' h2.mono_of_iso h3.mono_of_iso)

/-- A surjective étale atlas `a : U ⟶ T` of an algebraic space over `X` induces a monomorphism
`T_* 𝒪_T ⟶ U_* 𝒪_U` of direct-image algebras. -/
theorem mono_pushforwardAlgebraMap_objectPointOverHom {X : AlgebraicSpaces B S hS} (T : Over X)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ T.left.1)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Mono (pushforwardAlgebraMap B S hS (objectPointOverHom T a)) := by
  have hm : Mono (pushforwardRingMap B S hS (objectPointOverHom T a)) := by
    have h := mono_pushforwardAlgMap B S hS (objectPointOverHom T a).left T.hom
      (mono_fSharp_of_etale_atlas B S hS a hsurj hetale)
    rw [pushforwardRingMap_eq]
    have h4 : IsIso (eqToHom (congrArg
        (fun q : (objectPointOver T a).left ⟶ X =>
          (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS q).toToposHom).obj
              (smallEtaleRingedTopos B S hS (objectPointOver T a).left).O)
        (Over.w (objectPointOverHom T a)))) := inferInstance
    exact mono_comp' h (@IsIso.mono_of_iso _ _ _ _ _ h4)
  refine ⟨fun g h e => AlgebraSheaf.Hom.ext ?_⟩
  have e' := congrArg (fun m => m.right) e
  simp only [AlgebraSheaf.comp_right, pushforwardAlgebraMap_right] at e'
  exact (cancel_mono _).1 e'

/-! ### Arbitrary sources -/

/-- Two morphisms over `X`, from an algebraic space over `X` to one affine over `X`, with the
same direct-image map are equal. -/
theorem eq_of_pushforwardAlgebraMap_eq {X : AlgebraicSpaces B S hS} {T : Over X}
    (Z : AffineOver B S hS X) {f g : T ⟶ Z.obj}
    (e : pushforwardAlgebraMap B S hS f = pushforwardAlgebraMap B S hS g) : f = g := by
  obtain ⟨U, a, hsurj, hetale⟩ := T.left.property.exists_atlas
  have hcomp : objectPointOverHom T a ≫ f = objectPointOverHom T a ≫ g :=
    eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
      (relativelyRepresentable_objectPointOver B S hS T a) Z
      (by rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_comp, e])
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  exact hom_ext_of_etale_atlas B S hS T.left.property.isSheaf Z.obj.left.property.isSheaf a
    hsurj hetale (congrArg (fun m => m.left.hom) hcomp)

/-- From an algebraic space over `X` into one affine over `X`, every morphism of direct-image
algebras is the direct-image map of a morphism over `X`. -/
theorem exists_pushforwardAlgebraMap_eq_of_affineOver {X : AlgebraicSpaces B S hS}
    (T : Over X) (Z : AffineOver B S hS X)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS T) :
    ∃ f : T ⟶ Z.obj, pushforwardAlgebraMap B S hS f = φ := by
  obtain ⟨U, a, hsurj, hetale⟩ := T.left.property.exists_atlas
  obtain ⟨dU, hdU⟩ := exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
    (relativelyRepresentable_objectPointOver B S hS T a) Z
    (φ ≫ pushforwardAlgebraMap B S hS (objectPointOverHom T a))
  have hcompat : ∀ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) a a →
        yoneda.map s ≫ dU.left.hom = yoneda.map t ≫ dU.left.hom := by
    intro R s t hR
    let s' : objectPointOver T (yoneda.map s ≫ a) ⟶ objectPointOver T a :=
      Over.homMk (ObjectProperty.homMk (yoneda.map s))
    let t' : objectPointOver T (yoneda.map s ≫ a) ⟶ objectPointOver T a :=
      Over.homMk (ObjectProperty.homMk (yoneda.map t)) (by
        refine ObjectProperty.hom_ext _ ?_
        show yoneda.map t ≫ a ≫ T.hom.hom = (yoneda.map s ≫ a) ≫ T.hom.hom
        rw [← Category.assoc, hR.w])
    have hst : s' ≫ objectPointOverHom T a = t' ≫ objectPointOverHom T a :=
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ hR.w)
    have heq : s' ≫ dU = t' ≫ dU :=
      eq_of_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
        (relativelyRepresentable_objectPointOver B S hS T _) Z (by
          rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_comp, hdU, Category.assoc,
            Category.assoc, ← pushforwardAlgebraMap_comp, ← pushforwardAlgebraMap_comp, hst])
    exact congrArg (fun m => m.left.hom) heq
  obtain ⟨d, hd, -⟩ := existsUnique_hom_of_atlas_invariant B S hS T.left.property.isSheaf
    Z.obj.left.property.isSheaf a hsurj hetale dU.left.hom hcompat
  have hdover : d ≫ Z.obj.hom.hom = T.hom.hom := by
    refine hom_ext_of_etale_atlas B S hS T.left.property.isSheaf X.property.isSheaf a hsurj
      hetale ?_
    rw [← Category.assoc, hd]
    exact congrArg (fun m => m.hom) (Over.w dU)
  let dO : T ⟶ Z.obj := Over.homMk (ObjectProperty.homMk d) (ObjectProperty.hom_ext _ hdover)
  have hfac : objectPointOverHom T a ≫ dO = dU :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hd)
  refine ⟨dO, ?_⟩
  have := mono_pushforwardAlgebraMap_objectPointOverHom B S hS T a hsurj hetale
  refine (cancel_mono (pushforwardAlgebraMap B S hS (objectPointOverHom T a))).1 ?_
  rw [← pushforwardAlgebraMap_comp, hfac, hdU]

/-- For an algebraic space `T` over `X` and an algebraic space `Z` affine over `X`, direct image
is a bijection from morphisms `T ⟶ Z` over `X` to morphisms `π_* 𝒪_Z ⟶ (T ⟶ X)_* 𝒪_T` of
`𝒪_X`-algebras. -/
def overHomEquivPushforwardAlgebraHom {X : AlgebraicSpaces B S hS} (T : Over X)
    (Z : AffineOver B S hS X) :
    (T ⟶ Z.obj) ≃ (pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS T) :=
  Equiv.ofBijective (fun f => pushforwardAlgebraMap B S hS f)
    ⟨fun _ _ e => eq_of_pushforwardAlgebraMap_eq B S hS Z e,
      fun φ => exists_pushforwardAlgebraMap_eq_of_affineOver B S hS T Z φ⟩

/-- `AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom` sends a morphism to its
direct-image map. -/
@[simp]
theorem overHomEquivPushforwardAlgebraHom_apply {X : AlgebraicSpaces B S hS} (T : Over X)
    (Z : AffineOver B S hS X) (f : T ⟶ Z.obj) :
    overHomEquivPushforwardAlgebraHom B S hS T Z f = pushforwardAlgebraMap B S hS f :=
  rfl

end AlgebraicGeometry.Space

end
