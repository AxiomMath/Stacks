module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Faithful
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Mono
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundle
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicPro
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# Vector bundles and quasi-coherent modules

Let `S` be a scheme. Tag 062N asserts that the category of vector bundles over `S` is
anti-equivalent to the category of quasi-coherent `𝒪_S`-modules, the two functors being
`V ↦ (π_* 𝒪_V)_1` and `ℰ ↦ 𝐕(ℰ) = Spec_S(Sym(ℰ))`. A morphism of vector bundles over `S` acts on
functions in the direction opposite to the morphism of total spaces, so the degree-one piece is a
*contravariant* functor of the bundle, and the anti-equivalence is an equivalence

`(VectorBundle S)ᵒᵖ ≌ QCoh(𝒪_S)`.

The opposite is taken on the geometric side because that is the side the source's two functors
are contravariant on, and because the anti-equivalence of Tag 01SA that this one restricts,
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence`, is already stated as
`(AffineOver S)ᵒᵖ ≌ QuasicoherentAlgebra S`.

This file constructs the functor `V ↦ ℰ_1`, unconditionally, proves that it is **faithful**, and
proves that a cone whose direct-image algebra is the symmetric algebra of a module is a vector
bundle whose degree-one piece is that module, which gives essential surjectivity from a
symmetric presentation of each quasi-coherent module. The remaining two clauses are in sibling
files and the tag is **closed**: fullness is
`AlgebraicGeometry.VectorBundle.full_degreeOneModules` in
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleAntiEquivalence`, and the unconditional
essential surjectivity `AlgebraicGeometry.VectorBundle.essSurj_degreeOneFunctor'` together with
the assembled anti-equivalence `AlgebraicGeometry.VectorBundle.degreeOneEquivalence` are in
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEssSurj`.

The decomposition axioms of a cone are shown here to identify `π_* 𝒪_C` with the coproduct of the
homogeneous pieces, which makes every piece a direct summand of a quasi-coherent module and so
quasi-coherent.

## Main definitions

* `AlgebraicGeometry.VectorBundle.degreeOneModules` is the functor
  `(VectorBundle S)ᵒᵖ ⥤ S.Modules` sending a vector bundle to the degree-one piece `ℰ_1` of its
  direct-image algebra and a morphism to its graded component in degree one.
* `AlgebraicGeometry.VectorBundle.degreeOneFunctor` is the same functor read into the
  quasi-coherent modules, `(VectorBundle S)ᵒᵖ ⥤ AlgebraicGeometry.Scheme.QuasicoherentModules S`.
* `AlgebraicGeometry.AbstractCone.directSumHom` and
  `AlgebraicGeometry.AbstractCone.coprodDirectSumHom` are the comparison morphisms from the
  objectwise direct sum of the homogeneous pieces into `π_* 𝒪_C`, over all degrees and over the
  nonnegative ones, and `AlgebraicGeometry.AbstractCone.coprodIsoPushforward` is the resulting
  identification of `π_* 𝒪_C` with the coproduct of the pieces.
* `AlgebraicGeometry.AbstractCone.Hom.unitalGraded` is the graded part of a morphism of cones,
  as a *unital* homomorphism of sheaves of graded algebras.
* `AlgebraicGeometry.AbstractCone.SymmetricPresentation` is a cone over `S` together with an
  invertible degree-one generator exhibiting its direct-image algebra as the symmetric algebra of
  a given `𝒪_S`-module.

## Main results

* `AlgebraicGeometry.AbstractCone.Hom.ext_f`: **a morphism of cones is determined by its
  morphism of total spaces alone.** The map on direct images is the pullback on functions, and
  the graded map is determined by it because every homogeneous piece injects into the direct
  image.
* `AlgebraicGeometry.AbstractCone.hom_ext_of_comp_ι`: **a morphism out of `π_* 𝒪_C` is determined
  by its restrictions to the homogeneous pieces**, which generate it locally.
* `AlgebraicGeometry.AbstractCone.Hom.pullback_eq_of_graded_eq`,
  `AlgebraicGeometry.AbstractCone.Hom.f_eq_of_pullback_eq` and
  `AlgebraicGeometry.AbstractCone.Hom.ext_graded`: **a morphism of cones is determined by its
  graded part**, through the map on direct images and then the morphism of total spaces.
* `AlgebraicGeometry.AbstractCone.isQuasicoherent_pushforward`: the direct-image algebra of a
  cone is quasi-coherent, the projection being affine.
* `AlgebraicGeometry.AbstractCone.isQuasicoherent_piece_natCast`: **every homogeneous piece of a
  cone is quasi-coherent**, and `AlgebraicGeometry.AbstractCone.isQuasicoherent_piece_one` in
  degree one. `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_split` is the general
  statement it rests on: a split subobject of a quasi-coherent module on a scheme is
  quasi-coherent.
* `AlgebraicGeometry.VectorBundle.graded_eq_of_app_one`: **a morphism of vector bundles is
  determined by the degree-one component of its graded part**, by the universal property of the
  symmetric algebra; this is the faithfulness of `degreeOneModules` on graded parts.
* `AlgebraicGeometry.AbstractCone.SymmetricPresentation.vectorBundle`: **a cone whose
  direct-image algebra is the symmetric algebra of an `𝒪_S`-module is a vector bundle**, and
  `AlgebraicGeometry.AbstractCone.SymmetricPresentation.pieceOneIso` identifies that module with
  its degree-one piece.
* `AlgebraicGeometry.VectorBundle.faithful_degreeOneModules` and
  `AlgebraicGeometry.VectorBundle.faithful_degreeOneFunctor`: **the functor `V ↦ ℰ_1` is
  faithful**, which is the faithfulness clause of Tag 062N.
* `AlgebraicGeometry.VectorBundle.essSurj_degreeOneFunctor`: **essential surjectivity of
  `V ↦ ℰ_1`** from a symmetric presentation for every quasi-coherent module.

## Implementation notes

### Why `π_* 𝒪_C` is the coproduct of the homogeneous pieces

The two decomposition axioms of a cone are exactly local bijectivity of the comparison morphism
`AlgebraicGeometry.AbstractCone.directSumHom` out of the objectwise direct sum of the pieces:
`decomposition_unique` is injectivity on sections, hence local injectivity, and
`decomposition_locally` is local surjectivity, the covering sieves of the site of opens being
the pointwise ones. A presheaf of modules mapping locally bijectively into a sheaf of modules
exhibits that sheaf as its sheafification
(`Stacks.sheafifyIsoOfLocallyBijective`), and the sheafification of the objectwise direct sum of
a family of sheaves is their coproduct (`Stacks.sheafifyDirectSumIso`); the restriction to the
nonnegative degrees loses nothing because the negative pieces vanish
(`Stacks.directSumNatToInt` and `Stacks.bijective_directSumNatToIntApp`). The composite is
`AlgebraicGeometry.AbstractCone.coprodIsoPushforward`.

Quasi-coherence of `ℰ_n` follows: the coproduct inclusion of the degree-`n` summand is split by
the morphism `Limits.Sigma.desc` builds from the Kronecker family, so `ℰ_n` is a split subobject
of `π_* 𝒪_C`, which is quasi-coherent because `π` is affine
(`AlgebraicGeometry.AbstractCone.isQuasicoherent_pushforward`, from
`Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf`, Tag 02KG). A split subobject of a
quasi-coherent module on a *general* scheme is quasi-coherent, because a split epimorphism is the
coequalizer of the identity and the complementary idempotent and quasi-coherence is stable under
colimits
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`); affineness is
not needed, unlike in `Stacks.AffineTilde.isQuasicoherent_of_retract`.

This is the content of Tag 062R that `AlgebraicGeometry.AbstractCone` does not record as data:
there the grading of `π_* 𝒪_C` is a grading in the category of quasi-coherent `𝒪_S`-modules.
No field has to be added, and the forward functor
`AlgebraicGeometry.VectorBundle.degreeOneFunctor` is unconditional.

### What is carried as a hypothesis *here*, and where it is discharged

`AlgebraicGeometry.VectorBundle.essSurj_degreeOneFunctor` below takes **a symmetric presentation
of each quasi-coherent module** as an argument. That hypothesis is **no longer open**: it is
discharged in `StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEssSurj` by
`AlgebraicGeometry.AbstractCone.symmetricPresentation`, which builds the cone
`𝐕(ℰ) = Spec_S(Sym(ℰ))` of Tag 01M2 — the grading of `π_* 𝒪` by the symmetric powers, with all
four of the `ι_mul`, `ι_zero`, `degreeZero_mul` and `degreeZero_one` axioms and with
`AlgebraicGeometry.GradedAlgebraCone.decomposition_unique` for the uniqueness of a homogeneous
decomposition — and the unconditional
`AlgebraicGeometry.VectorBundle.essSurj_degreeOneFunctor'` is the result. The conditional form
below is kept only because it is the statement this file can make from its own imports.

### How faithfulness is proved, and why the coproduct is not needed for it

Faithfulness is a chain of three determinations. `AlgebraicGeometry.VectorBundle`
`.graded_eq_of_app_one` recovers the whole graded part of a morphism from its degree-one
component, by the universal property of the symmetric algebra.
`AlgebraicGeometry.AbstractCone.Hom.pullback_eq_of_graded_eq` recovers the map on direct images
from the graded part: `ι_naturality` makes the graded part realize it on every homogeneous
piece, and `AlgebraicGeometry.AbstractCone.hom_ext_of_comp_ι` cancels the comparison morphism
`AlgebraicGeometry.AbstractCone.directSumHom` on the left, which is legitimate because
`decomposition_locally` makes that morphism locally surjective and the target is a sheaf
(`Stacks.ClosedImmersion.eq_of_isLocallySurjective_comp_eq`). Note that this uses local
surjectivity directly and *not*
`AlgebraicGeometry.AbstractCone.coprodIsoPushforward`: no identification of the coproduct
inclusion with `AlgebraicGeometry.AbstractCone.ι n` through the sheafification unit is needed.
Finally `AlgebraicGeometry.AbstractCone.Hom.f_eq_of_pullback_eq` recovers the morphism of total
spaces, by assembling the sections of the map on direct images into
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap` — the two agree because
`Hom.pullback_app` identifies the stored map with the pullback on functions and
`Scheme.Hom.appLE_eq_app` removes the restriction, the two opens agreeing — and applying
`Stacks.AffineAlgebraEquivalence.left_eq_of_pushforwardAlgebraMap_eq`, whose hypothesis that the
target be affine over `S` is the cone axiom `isAffine`.

### What was open here, and where it went

Fullness and essential surjectivity were both open when this file was written; both are now
proved, and Tag 062N's anti-equivalence is assembled. Fullness is
`AlgebraicGeometry.VectorBundle.full_degreeOneModules` and `full_degreeOneFunctor` in
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleAntiEquivalence`; essential
surjectivity is `essSurj_degreeOneFunctor'` and the equivalence `degreeOneEquivalence` in
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEssSurj`.

The route this note predicted for fullness is not the one that worked. It asked for a graded
homomorphism to induce a morphism of the ungraded sheaves of **rings** the two direct images
are, and recorded `Stacks.RelativeSpec.ungradedAlgebraSheaf` as unavailable here. That
unavailability was a misdiagnosis -- there is no name clash and no import cycle -- but the
construction was not needed either: sheafifying in `RingCat` rather than `CommRingCat` asks
nothing extra, whereas the commutative version demands a heterogeneous commutativity that
`AbstractCone` does not record. See `AbstractCone.isIso_ringSheafHom`.

### Why a symmetric presentation asks for an *invertible* generator

`AlgebraicGeometry.AbstractCone.SymmetricPresentation` requires its degree-one generator
`E ⟶ ℰ_1` to be an isomorphism, and that is not redundant. Tag 062M's condition is that the
direct-image algebra be the symmetric algebra on *its own* degree-one piece, so a cone with
`π_* 𝒪_C = Sym(E)` is a vector bundle only once `Sym¹(E) = E`; without that the universal
property is about the wrong module. The identification is harmless — for a vector bundle it is
`AlgebraicGeometry.VectorBundle.symmetricPowerComparison_one_comp_symmetricAlgebraGen`, the
degree-one comparison being inverse to
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen` — but it is an input, and it is recorded
in the structure rather than assumed silently.

### Why `IsIso` of a named generator

`AlgebraicGeometry.AbstractCone.SymmetricPresentation` records its generator as a morphism
together with `IsIso`, rather than as a bundled isomorphism, for the reason given in the
implementation notes of `StacksFrontier.AlgebraicGeometry.Constructions.VectorBundle`: the
homogeneous pieces are sheaves of modules over the structure sheaf of a scheme and the type of an
isomorphism between two of them is expensive to check.

## References

* [Stacks Project, Tag 062N](https://stacks.math.columbia.edu/tag/062N)
* [Stacks Project, Tag 062M](https://stacks.math.columbia.edu/tag/062M)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

/-- **A split subobject of a quasi-coherent module on a scheme is quasi-coherent.** A split
epimorphism `r` with section `i` exhibits its target as the coequalizer of `𝟙` and the
complementary idempotent `r ≫ i`, and quasi-coherence is stable under colimits. -/
theorem Scheme.Modules.isQuasicoherent_of_split {X : Scheme.{u}} {F H : X.Modules}
    (i : F ⟶ H) (r : H ⟶ F) (hir : i ≫ r = 𝟙 F) (hH : H.IsQuasicoherent) :
    F.IsQuasicoherent := by
  have hcond : (𝟙 H) ≫ r = (r ≫ i) ≫ r := by
    rw [Category.id_comp, Category.assoc, hir, Category.comp_id]
  have hcolim : IsColimit (Cofork.ofπ r hcond) :=
    Cofork.IsColimit.mk _ (fun s => i ≫ s.π)
      (fun s => by
        have h := s.condition
        rw [Category.id_comp, Category.assoc] at h
        exact h.symm)
      (fun s m hm => by
        rw [Cofork.π_ofπ] at hm
        rw [← hm, ← Category.assoc, hir]
        exact (Category.id_comp m).symm)
  exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
    (fun k => by cases k <;> exact hH) hcolim

namespace AbstractCone

variable {S : Scheme.{u}}

/-! ### Quasi-coherence of the direct image of a cone -/

/-- The direct-image algebra of a cone is a quasi-coherent `𝒪_S`-module, the projection of a
cone being an affine morphism. -/
theorem isQuasicoherent_pushforward (X : AbstractCone S) :
    (Stacks.Morphisms.pushforwardStructureSheaf X.π).IsQuasicoherent :=
  have := X.isAffine
  Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf X.π

/-- The degree-zero piece of a cone is quasi-coherent, being isomorphic to the structure sheaf
of the base. -/
theorem isQuasicoherent_piece_zero (X : AbstractCone S) : (X.grading.piece 0).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso X.degreeZero.symm
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S)

/-- The inclusion of the degree-zero piece of a cone carries the algebra unit to the unit
function: it is the structure map `𝒪_S ⟶ π_* 𝒪_C`, and the degree-zero identification carries
the unit to `1`. -/
theorem ι_zero_one (X : AbstractCone S) (U : S.Opens) :
    ((X.ι 0).val.app (op U) (X.grading.one.eval (op U)) :
        X.C.presheaf.obj (op (X.π ⁻¹ᵁ U))) =
      (1 : X.C.presheaf.obj (op (X.π ⁻¹ᵁ U))) :=
  (X.ι_zero U (X.grading.one.eval (op U))).trans
    ((congrArg (fun r : S.presheaf.obj (op U) => X.π.c.app (op U) r)
      (X.degreeZero_one U)).trans (map_one _))

/-! ### The direct image of a cone is the coproduct of its homogeneous pieces -/

/-- The comparison morphism from the objectwise direct sum of the homogeneous pieces of a cone
into its direct image, assembled from the inclusions `ℰ_n ⟶ π_* 𝒪_C`. -/
noncomputable def directSumHom (X : AbstractCone S) :
    Stacks.directSum (fun n : ℤ => (X.grading.piece n).val) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf X.π).val :=
  Stacks.directSumDesc _ fun n => (X.ι n).val

/-- The finite-support sum of homogeneous local sections used by `AbstractCone` is the comparison
morphism `AlgebraicGeometry.AbstractCone.directSumHom` on sections. -/
theorem pushforwardHomogeneousSum_eq (X : AbstractCone S) (U : S.Opens) :
    pushforwardHomogeneousSum X.π X.grading X.ι U =
      Stacks.homToAddMonoidHom (fun n : ℤ => (X.grading.piece n).val) X.directSumHom (op U) := by
  refine DFinsupp.addHom_ext fun n x => ?_
  simp only [pushforwardHomogeneousSum, DFinsupp.sumAddHom_single]
  exact congrArg (fun f : (X.grading.piece n).val ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf X.π).val => f.app (op U) x)
    (Stacks.inclHom_directSumDesc (fun k : ℤ => (X.grading.piece k).val)
      (fun k => (X.ι k).val) n).symm

/-- The comparison morphism is injective on sections: that is the uniqueness of a finite
homogeneous decomposition. -/
theorem injective_directSumHom_app (X : AbstractCone S) (U : S.Opens) :
    Function.Injective (X.directSumHom.app (op U)) := fun z z' h =>
  X.decomposition_unique U
    ((DFunLike.congr_fun (X.pushforwardHomogeneousSum_eq U) z).trans
      (h.trans (DFunLike.congr_fun (X.pushforwardHomogeneousSum_eq U) z').symm))

/-- The comparison morphism is locally injective, being injective. -/
theorem isLocallyInjective_directSumHom (X : AbstractCone S) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (S : TopCat))
      ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map X.directSumHom) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun W => by
    induction W with
    | op U => exact X.injective_directSumHom_app U

/-- The comparison morphism is locally surjective: that is the local existence of a finite
homogeneous decomposition. -/
theorem isLocallySurjective_directSumHom (X : AbstractCone S) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (S : TopCat))
      ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map X.directSumHom) where
  imageSieve_mem {U} a := fun x hx => by
    obtain ⟨V, hVU, hxV, s, hs⟩ := X.decomposition_locally U a x hx
    exact ⟨V, homOfLE hVU,
      ⟨s, (DFunLike.congr_fun (X.pushforwardHomogeneousSum_eq V) s).symm.trans hs⟩, hxV⟩

/-- The comparison morphism restricted to the degree-`n` summand is the inclusion `ℰ_n ⟶ π_* 𝒪_C`,
the comparison being assembled from those inclusions. -/
theorem inclHom_directSumHom (X : AbstractCone S) (n : ℤ) :
    Stacks.inclHom (fun k : ℤ => (X.grading.piece k).val) n ≫ X.directSumHom = (X.ι n).val :=
  Stacks.inclHom_directSumDesc _ _ n

/-- **A morphism out of the direct image of a cone is determined by its restrictions to the
homogeneous pieces.** Every local section of `π_* 𝒪_C` is locally a finite sum of homogeneous
ones, so the comparison morphism out of the objectwise direct sum is locally surjective and can
be cancelled on the left against a morphism into a sheaf. -/
theorem hom_ext_of_comp_ι (X : AbstractCone S) {T : S.Modules}
    {g₁ g₂ : Stacks.Morphisms.pushforwardStructureSheaf X.π ⟶ T}
    (h : ∀ n : ℤ, X.ι n ≫ g₁ = X.ι n ≫ g₂) : g₁ = g₂ := by
  have hval : X.directSumHom ≫ g₁.val = X.directSumHom ≫ g₂.val := by
    refine Stacks.directSum_hom_ext _ fun n => ?_
    refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.assoc _ _ _))
    refine Eq.trans (congrArg (fun k => k ≫ g₁.val) (X.inclHom_directSumHom n)) ?_
    refine Eq.trans ?_ (congrArg (fun k => k ≫ g₂.val) (X.inclHom_directSumHom n)).symm
    exact congrArg (fun k : X.grading.piece n ⟶ T => k.val) (h n)
  have hpre : (PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map g₁.val =
      (PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map g₂.val := by
    refine Stacks.ClosedImmersion.eq_of_isLocallySurjective_comp_eq
      (J := Opens.grothendieckTopology (S : TopCat))
      X.isLocallySurjective_directSumHom T.isSheaf.isSeparated ?_
    refine Eq.trans ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map_comp _ _).symm ?_
    refine Eq.trans (congrArg (PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map hval) ?_
    exact (PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map_comp _ _
  exact SheafOfModules.hom_ext
    ((PresheafOfModules.toPresheaf S.ringCatSheaf.obj).map_injective hpre)

/-- The comparison morphism restricted to the nonnegative degrees, where the cone's grading
lives. -/
noncomputable def coprodDirectSumHom (X : AbstractCone S) :
    Stacks.directSum (fun n : ℕ => (X.grading.piece (n : ℤ)).val) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf X.π).val :=
  Stacks.directSumNatToInt (fun n : ℤ => (X.grading.piece n).val) ≫ X.directSumHom

/-- **The direct image `π_* 𝒪_C` of a cone is the coproduct of its homogeneous pieces.** The two
decomposition axioms say exactly that the comparison morphism out of the objectwise direct sum is
locally bijective, so the direct image is the sheafification of that direct sum, which is the
coproduct of the pieces. -/
noncomputable def coprodIsoPushforward (X : AbstractCone S) :
    (∐ fun n : ℕ => X.grading.piece (n : ℤ)) ≅
      Stacks.Morphisms.pushforwardStructureSheaf X.π :=
  (Stacks.sheafifyDirectSumIso fun n : ℕ => X.grading.piece (n : ℤ)).symm ≪≫
    Stacks.sheafifyIsoOfLocallyBijective X.coprodDirectSumHom
      (Stacks.isLocallyInjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallyInjective_directSumNatToInt _ _
          fun n hn W => Stacks.subsingleton_of_isZero (X.negative_isZero n hn) W)
        X.isLocallyInjective_directSumHom)
      (Stacks.isLocallySurjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallySurjective_directSumNatToInt _ _
          fun n hn W => Stacks.subsingleton_of_isZero (X.negative_isZero n hn) W)
        X.isLocallySurjective_directSumHom)

/-- **Every homogeneous piece of a cone is quasi-coherent.** The piece of degree `n` is a direct
summand of the coproduct of all the pieces, which is the direct image `π_* 𝒪_C`, and that is
quasi-coherent because the projection of a cone is affine. -/
theorem isQuasicoherent_piece_natCast (X : AbstractCone S) (n : ℕ) :
    (X.grading.piece (n : ℤ)).IsQuasicoherent := by
  let N : ℕ → S.Modules := fun m => X.grading.piece (m : ℤ)
  exact Scheme.Modules.isQuasicoherent_of_split (X := S) (F := N n) (H := ∐ N) (Sigma.ι N n)
    (Sigma.desc (Function.update (β := fun m : ℕ => N m ⟶ N n) (fun _ => 0) n (𝟙 (N n))))
    ((Sigma.ι_desc _ n).trans (Function.update_self n _ _))
    ((SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso X.coprodIsoPushforward.symm
      X.isQuasicoherent_pushforward)

/-- **The degree-one piece of a cone is quasi-coherent.** -/
theorem isQuasicoherent_piece_one (X : AbstractCone S) :
    (X.grading.piece 1).IsQuasicoherent := by
  simpa using X.isQuasicoherent_piece_natCast 1

/-! ### A morphism of cones is determined by its morphism of total spaces -/

/-- Two morphisms of `𝒪_S`-modules are equal when they agree on all sections. -/
private theorem modules_hom_ext_of_app_apply {M N : S.Modules} {f g : M ⟶ N}
    (h : ∀ (U : S.Opens) x, f.val.app (op U) x = g.val.app (op U) x) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => by
    induction W with
    | op U => exact ModuleCat.hom_ext (LinearMap.ext (h U)))

/-- Equal morphisms of `𝒪_S`-modules agree on sections. -/
private theorem modules_hom_app_apply_congr {M N : S.Modules} {f g : M ⟶ N} (h : f = g)
    (U : S.Opens) (x) : f.val.app (op U) x = g.val.app (op U) x :=
  h ▸ rfl

namespace Hom

variable {X Y Z : AbstractCone S}

/-- **A morphism of cones is determined by its morphism of total spaces.** The stored map on
direct images is the pullback on functions, hence determined on sections, and the graded map is
then determined because every homogeneous piece injects into the direct image on sections. -/
theorem ext_f {φ ψ : Hom X Y} (h : φ.f = ψ.f) : φ = ψ := by
  revert h
  obtain ⟨f₁, c₁, p₁, pa₁, g₁, n₁⟩ := φ
  obtain ⟨f₂, c₂, p₂, pa₂, g₂, n₂⟩ := ψ
  rintro rfl
  obtain rfl : p₁ = p₂ :=
    modules_hom_ext_of_app_apply fun U a => (pa₁ U a).trans (pa₂ U a).symm
  obtain rfl : g₁ = g₂ :=
    SheafOfModules.GradedAlgebra.Hom.ext fun n =>
      modules_hom_ext_of_app_apply fun U x => X.ι_app_injective n U
        ((modules_hom_app_apply_congr (n₁ n) U x).symm.trans
          (modules_hom_app_apply_congr (n₂ n) U x))
  rfl

/-- The transport along the identification of the structure morphism of the source of a morphism
over `S` turns the map on functions into the canonical map `Γ(CY, pY⁻¹U) ⟶ Γ(CX, pX⁻¹U)`:
substituting the identification removes the transport, after which the two opens agree and the
restriction in `appLE` is the identity. -/
theorem c_app_eq_appLE {CX CY : Scheme.{u}} {pX : CX ⟶ S} {pY : CY ⟶ S}
    {f : CX ⟶ CY} (comm : f ≫ pY = pX) (U : S.Opens)
    (hle : pX ⁻¹ᵁ U ≤ f ⁻¹ᵁ (pY ⁻¹ᵁ U)) (a : CY.presheaf.obj (op (pY ⁻¹ᵁ U))) :
    (comm ▸ f.c.app (op (pY ⁻¹ᵁ U)) a : CX.presheaf.obj (op (pX ⁻¹ᵁ U))) =
      (f.appLE (pY ⁻¹ᵁ U) (pX ⁻¹ᵁ U) hle) a := by
  subst comm
  rw [show f.appLE (pY ⁻¹ᵁ U) ((f ≫ pY) ⁻¹ᵁ U) hle = f.app (pY ⁻¹ᵁ U) from f.appLE_eq_app]
  rfl

/-- **A morphism of cones is determined by the map it carries on direct images.** The sections of
that map are the canonical maps `Γ(C_Y, π'⁻¹U) ⟶ Γ(C_X, π⁻¹U)`, which assemble into the morphism
of pushed-forward structure sheaves attached to the morphism of total spaces over `S`; the
projection of the target being affine, that morphism determines it. -/
theorem f_eq_of_pullback_eq {φ ψ : Hom X Y} (h : φ.pullback = ψ.pullback) : φ.f = ψ.f := by
  have : IsAffineHom (Over.mk Y.π).hom := Y.isAffine
  have key : Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (Over.homMk φ.f φ.comm : Over.mk X.π ⟶ Over.mk Y.π) =
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (Over.homMk ψ.f ψ.comm : Over.mk X.π ⟶ Over.mk Y.π) := by
    ext1
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun V => ?_)
    obtain ⟨U⟩ := V
    rw [Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app _ U
        (Stacks.AffineAlgebraEquivalence.preimage_le_preimage_preimage _ _),
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app _ U
        (Stacks.AffineAlgebraEquivalence.preimage_le_preimage_preimage _ _)]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    refine Eq.trans (c_app_eq_appLE (f := φ.f) φ.comm U _ a).symm ?_
    refine Eq.trans (φ.pullback_app U a).symm ?_
    refine Eq.trans (modules_hom_app_apply_congr h U a) ?_
    refine Eq.trans (ψ.pullback_app U a) ?_
    exact c_app_eq_appLE (f := ψ.f) ψ.comm U _ a
  exact Stacks.AffineAlgebraEquivalence.left_eq_of_pushforwardAlgebraMap_eq key

/-- **The map a morphism of cones carries on direct images is determined by its graded part.**
The graded part realizes it on every homogeneous piece, and those generate the direct image
locally. -/
theorem pullback_eq_of_graded_eq {φ ψ : Hom X Y} (h : φ.graded = ψ.graded) :
    φ.pullback = ψ.pullback :=
  Y.hom_ext_of_comp_ι fun n =>
    (φ.ι_naturality n).trans
      ((congrArg (fun g : SheafOfModules.GradedAlgebra.Hom Y.grading X.grading =>
          g.app n ≫ X.ι n) h).trans (ψ.ι_naturality n).symm)

/-- **A morphism of cones is determined by its graded part.** -/
theorem ext_graded {φ ψ : Hom X Y} (h : φ.graded = ψ.graded) : φ = ψ :=
  ext_f (f_eq_of_pullback_eq (pullback_eq_of_graded_eq h))

/-- The transport along the identification of the structure morphism of the source of a morphism
over `S` does not move the unit section: substituting the identification removes the transport,
after which the statement is that a pullback of functions is a homomorphism of rings. -/
theorem comm_transport_one {C₁ C₂ : Scheme.{u}} {p₁ : C₁ ⟶ S} {p₂ : C₂ ⟶ S} {f : C₁ ⟶ C₂}
    (c : f ≫ p₂ = p₁) (U : S.Opens) :
    (c ▸ f.c.app (op (p₂ ⁻¹ᵁ U)) (1 : C₂.presheaf.obj (op (p₂ ⁻¹ᵁ U))) :
      C₁.presheaf.obj (op (p₁ ⁻¹ᵁ U))) = 1 := by
  subst c
  exact map_one _

/-- The map on direct images carried by a morphism of cones preserves the unit section, being
the pullback of functions. -/
theorem pullback_app_one (φ : Hom X Y) (U : S.Opens) :
    φ.pullback.val.app (op U) (1 : Y.C.presheaf.obj (op (Y.π ⁻¹ᵁ U))) =
      (1 : X.C.presheaf.obj (op (X.π ⁻¹ᵁ U))) :=
  (φ.pullback_app U 1).trans (comm_transport_one φ.comm U)

/-- The graded part of a morphism of cones preserves the algebra unit: the pullback of functions
does, and the degree-zero piece injects into the direct image. -/
theorem graded_app_zero_one (φ : Hom X Y) (U : S.Opens) :
    (φ.graded.app 0).val.app (op U) (Y.grading.one.eval (op U)) =
      X.grading.one.eval (op U) := by
  refine X.ι_app_injective 0 U ?_
  refine (modules_hom_app_apply_congr (φ.ι_naturality 0) U _).symm.trans ?_
  refine ((congrArg (fun a : Y.C.presheaf.obj (op (Y.π ⁻¹ᵁ U)) =>
    φ.pullback.val.app (op U) a) (Y.ι_zero_one U)).trans (φ.pullback_app_one U)).trans ?_
  exact (X.ι_zero_one U).symm

/-- **The graded part of a morphism of cones, as a unital homomorphism** of sheaves of graded
algebras: it preserves the distinguished degree-zero unit, which `AbstractCone.Hom` does not
record. -/
def unitalGraded (φ : Hom X Y) :
    SheafOfModules.GradedAlgebra.UnitalHom Y.grading X.grading :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofHom φ.graded
    ((SheafOfModules.GradedAlgebra.UnitalHom.map_one_iff φ.graded).1 fun W => by
      induction W with
      | op U => exact φ.graded_app_zero_one U)

/-- The degree-`n` component of `φ.unitalGraded` is that of `φ.graded`. -/
@[simp] theorem unitalGraded_app (φ : Hom X Y) (n : ℤ) : φ.unitalGraded.app n = φ.graded.app n :=
  rfl

/-- The underlying morphism of graded algebras of `φ.unitalGraded` is `φ.graded`. -/
@[simp] theorem toHom_unitalGraded (φ : Hom X Y) : φ.unitalGraded.toHom = φ.graded := rfl

end Hom

/-! ### Cones presented as a symmetric algebra -/

/-- A cone whose direct-image algebra is the symmetric algebra of a sheaf of modules on an
invertible degree-one generator is the symmetric algebra on its own degree-one piece: transport
the universal property along the generator. -/
theorem isSymmetricAlgebra_id_of_isIso (X : AbstractCone S)
    {E : SheafOfModules.{u} S.ringCatSheaf} (gen : E ⟶ X.grading.piece 1) [IsIso gen]
    (h : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra X.grading gen) :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra X.grading (𝟙 (X.grading.piece 1)) := by
  have h2 := SheafOfModules.GradedAlgebra.isSymmetricAlgebra_of_iso_source (asIso gen) h
  have he : (asIso gen).inv ≫ gen = 𝟙 (X.grading.piece 1) := (asIso gen).inv_hom_id
  rwa [he] at h2

/-- A presentation of a cone over `S` as the relative spectrum of the symmetric algebra of an
`𝒪_S`-module `E`: a cone whose direct-image algebra is the symmetric algebra of `E` on a
degree-one generator which is an isomorphism onto the degree-one piece. -/
structure SymmetricPresentation (S : Scheme.{u}) (E : SheafOfModules.{u} S.ringCatSheaf) where
  /-- The underlying cone. -/
  cone : AbstractCone S
  /-- The degree-one generator. -/
  gen : E ⟶ cone.grading.piece 1
  /-- The generator identifies `E` with the degree-one piece. -/
  isIso_gen : IsIso gen
  /-- The direct-image algebra is the symmetric algebra of `E` on that generator. -/
  isSymmetricAlgebra :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra cone.grading gen

namespace SymmetricPresentation

variable {E : SheafOfModules.{u} S.ringCatSheaf}

/-- **A cone whose direct-image algebra is the symmetric algebra of an `𝒪_S`-module is a vector
bundle.** This is the geometric half of Tag 062N: it is what makes the relative spectrum of
`Sym(ℰ)` a vector bundle in the sense of Tag 062M. -/
def vectorBundle (P : SymmetricPresentation S E) : VectorBundle S :=
  haveI := P.isIso_gen
  VectorBundle.ofIsSymmetricAlgebra P.cone
    (P.cone.isSymmetricAlgebra_id_of_isIso P.gen P.isSymmetricAlgebra)

/-- The cone underlying the vector bundle presented by `P` is `P.cone`. -/
@[simp] theorem toAbstractCone_vectorBundle (P : SymmetricPresentation S E) :
    P.vectorBundle.toAbstractCone = P.cone := rfl

/-- The degree-one piece of the vector bundle presented by `P` is `E`. -/
def pieceOneIso (P : SymmetricPresentation S E) : E ≅ P.vectorBundle.grading.piece 1 :=
  @asIso _ _ _ _ P.gen P.isIso_gen

/-- The degree-one piece of a presented vector bundle is quasi-coherent as soon as the presented
module is: the generator is an isomorphism. -/
theorem isQuasicoherent_piece_one (P : SymmetricPresentation S E) (hE : E.IsQuasicoherent) :
    (P.vectorBundle.grading.piece 1).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso P.pieceOneIso hE

end SymmetricPresentation

end AbstractCone

/-! ### The functor `V ↦ ℰ_1` -/

namespace VectorBundle

variable {S : Scheme.{u}}

/-- **The degree-one piece of a vector bundle, as a contravariant functor** of the bundle: the
underlying `𝒪_S`-module of `(π_* 𝒪_V)_1`, with a morphism of vector bundles acting by the
degree-one component of its graded part. -/
def degreeOneModules (S : Scheme.{u}) : (VectorBundle S)ᵒᵖ ⥤ S.Modules where
  obj V := V.unop.grading.piece 1
  map φ := φ.unop.graded.app 1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `degreeOneModules S` sends a vector bundle to its degree-one piece. -/
@[simp] theorem degreeOneModules_obj (V : (VectorBundle S)ᵒᵖ) :
    (degreeOneModules S).obj V = V.unop.grading.piece 1 := rfl

/-- `degreeOneModules S` sends a morphism of vector bundles to the degree-one component of its
graded part. -/
@[simp] theorem degreeOneModules_map {V W : (VectorBundle S)ᵒᵖ} (φ : V ⟶ W) :
    (degreeOneModules S).map φ = φ.unop.graded.app 1 := rfl

/-- **The degree-one piece of every vector bundle over `S` is a quasi-coherent `𝒪_S`-module.**

This is the content of Tag 062R that `AlgebraicGeometry.AbstractCone` does not record as data:
there the grading of `π_* 𝒪_C` is a grading in the category of quasi-coherent `𝒪_S`-modules. It
is a consequence of the two decomposition axioms, by
`AlgebraicGeometry.AbstractCone.isQuasicoherent_piece_one`. -/
theorem isQuasicoherent_piece_one (V : VectorBundle S) :
    (V.grading.piece 1).IsQuasicoherent :=
  V.toAbstractCone.isQuasicoherent_piece_one

/-- **The functor `V ↦ ℰ_1` from vector bundles over `S`, contravariantly, to quasi-coherent
`𝒪_S`-modules.** This is one of the two functors of Tag 062N. -/
def degreeOneFunctor (S : Scheme.{u}) :
    (VectorBundle S)ᵒᵖ ⥤ Scheme.QuasicoherentModules S :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent S.ringCatSheaf) (degreeOneModules S)
    fun V => isQuasicoherent_piece_one V.unop

/-- Composing `V ↦ ℰ_1` with the inclusion of the quasi-coherent modules returns the functor
into all `𝒪_S`-modules. -/
def degreeOneFunctorCompι (S : Scheme.{u}) :
    degreeOneFunctor S ⋙ (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ≅
      degreeOneModules S :=
  ObjectProperty.liftCompιIso _ _ _

/-! ### Faithfulness on graded parts -/

/-- **A morphism of vector bundles is determined by the degree-one component of its graded
part.** The direct-image algebra of a vector bundle is the symmetric algebra on its own
degree-one piece, and a unital homomorphism out of a symmetric algebra is determined by its
restriction to the degree-one generator. -/
theorem graded_eq_of_app_one {V W : VectorBundle S} {φ ψ : V ⟶ W}
    (h : φ.graded.app 1 = ψ.graded.app 1) : φ.graded = ψ.graded := by
  have hκ : SheafOfModules.GradedAlgebra.PairwiseCommutes (φ.graded.app 1) :=
    fun U s t => V.pairwiseCommutes U ((φ.graded.app 1).val.app U s)
      ((φ.graded.app 1).val.app U t)
  have hu : φ.unitalGraded = ψ.unitalGraded :=
    W.isSymmetricAlgebra.isUniversal.hom_ext hκ (Category.id_comp _)
      ((Category.id_comp _).trans h.symm)
  exact congrArg SheafOfModules.GradedAlgebra.UnitalHom.toHom hu

/-- **The functor `V ↦ ℰ_1` is faithful**, which in the contravariant reading is the faithfulness
of the anti-equivalence of Tag 062N. A morphism of vector bundles is determined by the
degree-one component of its graded part, which determines the whole graded part by the universal
property of the symmetric algebra; the graded part determines the map on direct images because
the homogeneous pieces generate `π_* 𝒪_V` locally, and that map determines the morphism of total
spaces because the projection is affine. -/
instance faithful_degreeOneModules (S : Scheme.{u}) : (degreeOneModules S).Faithful where
  map_injective h :=
    Quiver.Hom.unop_inj (AbstractCone.Hom.ext_graded (graded_eq_of_app_one h))

/-- **The functor `V ↦ ℰ_1` into the quasi-coherent modules is faithful.** -/
instance faithful_degreeOneFunctor (S : Scheme.{u}) : (degreeOneFunctor S).Faithful :=
  Functor.Faithful.of_comp_iso (H := degreeOneModules S) (degreeOneFunctorCompι S)

/-! ### Essential surjectivity -/

/-- **The functor `V ↦ ℰ_1` is essentially surjective**, given a presentation of each
quasi-coherent `𝒪_S`-module as the degree-one piece of a cone whose direct-image algebra is its
symmetric algebra. For `ℰ` quasi-coherent such a presentation is Tag 01M2's
`𝐕(ℰ) = Spec_S(Sym(ℰ))`, once the grading of `π_* 𝒪_{𝐕(ℰ)}` by the `Symⁿ ℰ` is available. -/
theorem essSurj_degreeOneFunctor (S : Scheme.{u})
    (pres : ∀ E : SheafOfModules.{u} S.ringCatSheaf, E.IsQuasicoherent →
      AbstractCone.SymmetricPresentation S E) :
    (degreeOneFunctor S).EssSurj where
  mem_essImage E :=
    ⟨op (pres E.obj E.property).vectorBundle,
      ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.preimageIso
        (pres E.obj E.property).pieceOneIso.symm⟩⟩

end VectorBundle

end AlgebraicGeometry

end
