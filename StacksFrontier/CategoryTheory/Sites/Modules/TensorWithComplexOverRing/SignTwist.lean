module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.Adjunction

/-!
# The derived tensor product with a complex over the source's base ring: its value at the regular
module, and its exactness through the sign-twisted identity

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded `R`-algebra. This file
proves, for the derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX formed over `R`:

* the comparison with ordinary tensoring is invertible at the objects orthogonal on the left to
  the acyclic modules, and `E ⊗_E^𝐋 K = K`;
* composed with the sign-twisted identity of `D(O)`, it is an exact functor (Tag 09LW).

## Main results

* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerivedCounit_appOver`
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedObjRegularIsoOver`
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulatedOver`

## References

* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard

section Cone

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory
omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- `Hom(K, K)`, as a module over the endomorphism differential graded algebra of `K`, is
orthogonal on the left to the acyclic modules: it is the regular module over that algebra. -/
theorem leftOrthogonal_acyclic_rep_selfOver :
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
      ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).obj
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))) :=
  General.leftOrthogonal_acyclic_of_iso _ DGCategory.representableSelfIsoRegular.symm
    (leftOrthogonal_acyclic_regularModule _)

/-- The comparison of `- ⊗_E^𝐋 K` with plain tensoring is invertible at every object of
`K(Mod_(E, d))` orthogonal on the left to the acyclic modules. -/
theorem isIso_tensorWithComplexDerivedCounit_appOver
    (P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra)
    (hP : (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal P) :
    IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P) := by
  have hpw :
      (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).HasPointwiseLeftDerivedFunctor
        (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) := by
    rw [← acyclic_trW_eq_quasiIsomorphisms]
    exact (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra)
      |>.hasPointwiseLeftDerivedFunctor_of_leftOrthogonal_resolutions _
        (exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, o} X R K)
  have hloc : (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.IsLocalization
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).trW := by
    rw [acyclic_trW_eq_quasiIsomorphisms]
    infer_instance
  have hbij := fun Y => ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated hP
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q Y
  have h := Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
    (F' := tensorWithComplexDerived.{u, v, w, t, s, o} X R K)
    (α := tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
  simpa using (h _).isIso_π_app_of_isInitial _
    (structuredArrowMkIdIsInitial _ P hbij)

/-- Every value of `- ⊗_E^𝐋 K` is the plain tensor product with `K` of a differential graded
`E`-module orthogonal on the left to the acyclic modules. -/
theorem exists_leftOrthogonal_iso_tensorWithComplexDerived_objOver
    (M : DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra) :
    ∃ P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra,
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal P ∧
        Nonempty ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj M ≅
          (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).obj P) := by
  have hess : (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.EssSurj :=
    Localization.essSurj _ (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
  obtain ⟨P, f, hf, hP⟩ :=
    exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, o} X R K
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.objPreimage M)
  refine ⟨P, hP, ⟨?_⟩⟩
  have hfiso : IsIso ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map f) := by
    rw [acyclic_trW_eq_quasiIsomorphisms] at hf
    exact Localization.inverts (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) f hf
  have hcounit := isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K P hP
  exact (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).mapIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.objObjPreimageIso M).symm ≪≫
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).mapIso (asIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map f)).symm ≪≫
    asIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P)

/-- Tensoring `Hom(K, K)` with `K` gives back `K`: the image of the regular module under the
differential graded tensor functor of Tag 09LV, read in the homotopy category of complexes of
ambient `O`-modules. -/
noncomputable def tensorWithComplexHomotopyRegularIsoOver :
    (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).obj
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj
          ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))) ≅
      (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).obj
        (liftComplex.{u, v, w, t, s} X K) :=
  (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).mapIso
    ((CochainComplex.complexesToCochainFunctor (TensorModO.{u, v, w, t, s} X)).mapIso
      (tensorWithComplexDG_regular.{u, v, w, t, s, o} X R K))

/-- **The value of `- ⊗_E^𝐋 K` at the regular module `E` is `K`.** The comparison with plain
tensoring is invertible there, because `Hom(K, K)` is orthogonal on the left to the acyclic
modules, and plain tensoring sends it to `K`. -/
noncomputable def tensorWithComplexDerivedObjRegularIsoOver :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj
        ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).obj
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)))) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) := by
  have hcounit := isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K _
    (leftOrthogonal_acyclic_rep_selfOver.{u, v, w, t, s, o} X R K)
  exact asIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app _) ≪≫
    DerivedCategory.Qh.mapIso (tensorWithComplexHomotopyRegularIsoOver.{u, v, w, t, s, o} X R K) ≪≫
    (DerivedCategory.quotientCompQhIso (TensorModO.{u, v, w, t, s} X)).app
      (liftComplex.{u, v, w, t, s} X K)


/-- The object `E` of `D(E, d)`: the class of the endomorphism differential graded algebra of `K`
regarded as a right module over itself. -/
abbrev repRegularDerivedOver :
    DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra :=
  (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj
    ((toHomotopyCategory _).obj (regularModule (Rep.{u, v, w, t, s, o} X R K).algebra))

/-! ### Tag 09LW, read in the admissible structure -/

end Cone

section Admissible

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- **Tag 09LW.** Tensoring with `K`, followed by the localization of `K(O)`, carries the
triangle of an admissible short exact sequence of differential graded `E`-modules to a
distinguished triangle of `D(O)`.

The class of admissible triangles is named directly, as
`DifferentialGradedModule.IsDistinguishedTriangle`, and not through a `Pretriangulated`
instance, so this statement does not depend on which of the two structures on `K(Mod_(E, d))` is
in force. -/
theorem tensorWithComplexToDerivedCategory_mapTriangle_mem_distTriangOver
    (T : Triangle (DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra))
    (hT : IsDistinguishedTriangle (Rep.{u, v, w, t, s, o} X R K).algebra T) :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).mapTriangle.obj T ∈
      distTriang (DerivedCategory (TensorModO.{u, v, w, t, s} X)) := by
  let : (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).IsTriangulated :=
    tensorWithComplexHomotopy_isTriangulated.{u, v, w, t, s, o} X R K
  let : (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).IsTriangulated :=
    show (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙
      DerivedCategory.Qh (C := TensorModO.{u, v, w, t, s} X)).IsTriangulated from inferInstance
  exact mapTriangle_mem_distTriang_of_isTriangulated _
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K) T hT

end Admissible

/-! ### The twist, in the cone structure -/

section Cone

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory
  DifferentialGradedModule.instPreadditiveHomotopyCategory

/-- The quasi-isomorphisms of `K(Mod_(E, d))` admit a right calculus of fractions. -/
instance quasiIsomorphismsRepHasRightCalculusOfFractionsOver :
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).HasRightCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms]
  infer_instance

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Every object of `K(Mod_(E, d))` receives a quasi-isomorphism from an object orthogonal on the
left to the acyclic modules. -/
theorem exists_quasiIso_leftOrthogonal_acyclic_repOver
    (Y : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra) :
    ∃ (P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra)
      (_ : (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal P) (f : P ⟶ Y),
      quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra f := by
  obtain ⟨P, f, hf, hP⟩ := exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, o} X R K Y
  exact ⟨P, hP, f, by rwa [← acyclic_trW_eq_quasiIsomorphisms]⟩

/-- **Every morphism of `D(E, d)` is resolved by a distinguished triangle of `K(Mod_(E, d))` on
which the comparison with the underived functor is invertible.** For every morphism `g` of
`D(E, d)` there is a distinguished triangle `T` of `K(Mod_(E, d))` such that the comparison
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCounit` is invertible at its three vertices
and the image of `T.mor₁` in `D(E, d)` is isomorphic to `g` as an arrow. -/
theorem exists_distTriang_isIso_tensorWithComplexDerivedCounitOver
    {Y Z : DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra} (g : Y ⟶ Z) :
    ∃ (T : Pretriangulated.Triangle
        (DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, o} X R K).algebra))
      (_ : T ∈ distTriang
        (DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, o} X R K).algebra))
      (_ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app T.obj₁))
      (_ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app T.obj₂))
      (_ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app T.obj₃)),
      Nonempty (Arrow.mk ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map T.mor₁) ≅
        Arrow.mk g) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal).HasLeftResolutions :=
    fun Y => by
      obtain ⟨P, hP, f, hf⟩ :=
        exists_quasiIso_leftOrthogonal_acyclic_repOver.{u, v, w, t, s, o} X R K Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := f, hw := hf }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
  have : ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).IsLocalization
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).inverseImage
        (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism
        (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
        (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q)
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).inverseImage
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).mapArrow) (Arrow.mk g)
  obtain ⟨W, p, q, hT⟩ := distinguished_cocone_triangle
    ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι.map a.hom)
  have h₁ : (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
    (Triangle.mk ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι.map a.hom)
      p q).obj₁ := a.left.property
  have h₂ : (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal
    (Triangle.mk ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι.map a.hom)
      p q).obj₂ := a.right.property
  exact ⟨Triangle.mk ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ι.map a.hom)
      p q, hT,
    isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K _ h₁,
    isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K _ h₂,
    isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K _
      ((acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal.ext_of_isTriangulatedClosed₃
        _ hT h₁ h₂), ⟨ea⟩⟩

/-- **Tag 09LW, transferred to the cone structure.** Tensoring with `K` followed by the
localization of `K(O)` is, after precomposition with the sign-twisted identity of
`K(Mod_(E, d))`, an exact functor for the pretriangulated structure whose distinguished triangles
are the cone triangles.

Without the twist this is false, by the witness in the docstring of
`AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_isTriangulated'`. -/
theorem signTwist_tensorWithComplexToDerivedCategory_isTriangulatedOver :
    (DifferentialGradedModule.signTwist (Rep.{u, v, w, t, s, o} X R K).algebra ⋙
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).IsTriangulated :=
  isTriangulated_signTwist_comp (Rep.{u, v, w, t, s, o} X R K).algebra
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K)
    (tensorWithComplexToDerivedCategory_mapTriangle_mem_distTriangOver.{u, v, w, t, s, o} X R K)

/-- Tensoring with `K` followed by the localization of `K(O)` is additive. -/
instance tensorWithComplexToDerivedCategory_additiveOver :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).Additive :=
  let := signTwist_tensorWithComplexToDerivedCategory_isTriangulatedOver.{u, v, w, t, s, o} X R K
  inferInstanceAs ((DifferentialGradedModule.signTwist (Rep.{u, v, w, t, s, o} X R K).algebra ⋙
    tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).Additive)

/-- **Tag 09LW, transferred with the twist on the target.** The same exactness as
`AlgebraicGeometry.RingedSite.signTwist_tensorWithComplexToDerivedCategory_isTriangulatedOver`,
with the sign-twisted identity applied to `D(O)` instead of to `K(Mod_(E, d))`. -/
theorem tensorWithComplexToDerivedCategory_signTwist_isTriangulatedOver :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).IsTriangulated where
  map_distinguished T hT := by
    let := signTwist_tensorWithComplexToDerivedCategory_isTriangulatedOver.{u, v, w, t, s, o} X R K
    rw [CategoryTheory.comp_signTwist_mapTriangle_obj_eq]
    exact (DifferentialGradedModule.signTwist (Rep.{u, v, w, t, s, o} X R K).algebra ⋙
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).map_distinguished T hT

/-- **The derived tensor product is exact, through the twist**: the functor `- ⊗_E^𝐋 K` of
Tag 09LX, composed with the sign-twisted identity of `D(O)`, carries distinguished triangles of
`D(E, d)` to distinguished triangles of `D(O)` — the pretriangulated structure on `D(E, d)`
being the one induced from the cone triangles of `K(Mod_(E, d))`.

`- ⊗_E^𝐋 K ⋙ signTwist _` is the functor `- ⊗_E^𝐋 K` itself — `signTwist` is the identity on
objects and on morphisms — carrying a different comparison with the translation. -/
theorem tensorWithComplexDerived_signTwist_isTriangulatedOver :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).IsTriangulated := by
  let := tensorWithComplexToDerivedCategory_signTwist_isTriangulatedOver.{u, v, w, t, s, o} X R K
  let := CategoryTheory.NatTrans.commShift_signTwist'
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K)
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K)
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
  exact Functor.isTriangulated_of_rightExtension _
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
        (tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⋙
          CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))) ⟶
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K ⋙
        CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (fun {_ _} g =>
      exists_distTriang_isIso_tensorWithComplexDerivedCounitOver.{u, v, w, t, s, o} X R K g)

/-- **`- ⊗_E^𝐋 K` is additive.** -/
instance tensorWithComplexDerived_additiveOver :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).Additive :=
  let := tensorWithComplexDerived_signTwist_isTriangulatedOver.{u, v, w, t, s, o} X R K
  inferInstanceAs ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⋙
    CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).Additive)

end Cone



end AlgebraicGeometry.RingedSite

end
