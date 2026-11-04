module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexConeExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentImage

/-!
# The image of the derived tensor product with a complex of quasi-coherent cohomology

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The derived
tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX sends every object into `D_QCoh(O)` as
soon as the cohomology sheaves of `K` do.

The dévissage of Tag 0FQE reduces this to the shifts of the free rank-one module, where the
value of the functor is `K` itself. Its coproduct clause comes from Tag 09LY: `- ⊗_E^𝐋 K` is a
left adjoint, so it commutes with direct sums, and `D_QCoh(O)` is closed under them. Its
two-out-of-three clause reads the exactness of Tag 09LW across the sign of Tag 09KF: a
distinguished triangle of `D(E, d)` is isomorphic to the image of a cone triangle whose three
vertices are orthogonal on the left to the acyclic modules, at which the comparison between
`- ⊗_E^𝐋 K` and ordinary tensoring is invertible, and negating the third arrow of that cone
triangle makes its image a distinguished triangle of `D(O)` on the same three vertices. For a
scheme, read as the ringed site of its opens, the closure properties of quasi-coherence that the
dévissage consumes are theorems.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coneTriangle_leftOrthogonal_iso`: a distinguished triangle
  of `D(E, d)` is isomorphic to the image of a cone triangle with left-orthogonal vertices.
* `AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsum`:
  the image of `- ⊗_E^𝐋 K` lies in `D_QCoh(O)`, for a ringed site on which quasi-coherence is a
  weak Serre class closed under direct sums.
* `AlgebraicGeometry.RingedSite.tensorModOQuasicoherent_schemeRingedSite_eq`: on the site of
  opens of a scheme, quasi-coherence of ambient modules is quasi-coherence of its sheaves of
  modules.
* `AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_scheme`:
  **Stacks 09M3**, the same containment for a scheme, where those closure properties are
  discharged.

## References

* [Stacks Project, Tag 09M3](https://stacks.math.columbia.edu/tag/09M3)
* [Stacks Project, Tag 09LY](https://stacks.math.columbia.edu/tag/09LY), the adjunction.
* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW), the exactness of
  tensoring with `K`, and [Tag 09KF](https://stacks.math.columbia.edu/tag/09KF), the sign that
  relates the two classes of triangles on `K(Mod_(E, d))`.
* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE), the dévissage.
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1), the closure properties.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-! ### Cone triangles with left-orthogonal vertices -/

/-- Every distinguished triangle of `D(E, d)` is isomorphic to the image of a cone triangle of
`K(Mod_(E, d))` whose three vertices are orthogonal on the left to the acyclic modules: its first
arrow comes from an arrow between such objects, and a cone leaves the third vertex of that kind. -/
theorem exists_coneTriangle_leftOrthogonal_iso
    (Δ : Triangle (DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))
    (hΔ : Δ ∈ distTriang (DifferentialGradedModule.derivedCategory.{0, max u v w t s,
      max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)) :
    ∃ T : Triangle (DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra),
      T ∈ distinguishedConeTriangles.{0, max u v w t s, max u v w t s}
          (A := (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) ∧
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal T.obj₁ ∧
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal T.obj₂ ∧
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal T.obj₃ ∧
      Nonempty (Δ ≅
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapTriangle.obj T) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal).HasLeftResolutions :=
    fun Y => by
      obtain ⟨P, hP, f, hf⟩ := exists_quasiIso_leftOrthogonal_acyclic_rep.{u, v, w, t, s} X K Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := f, hw := hf }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
  have : ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).IsLocalization
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).inverseImage
        (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
        (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q)
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).inverseImage
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).mapArrow) (Arrow.mk Δ.mor₁)
  obtain ⟨W, p, q, hT⟩ := distinguished_cocone_triangle
    ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι.map a.hom)
  refine ⟨Triangle.mk
      ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι.map a.hom) p q,
    hT, a.left.property, a.right.property,
    (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ext_of_isTriangulatedClosed₃
      _ hT a.left.property a.right.property, ⟨?_⟩⟩
  exact (isoTriangleOfIso₁₂ _ _
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.map_distinguished _ hT) hΔ
    (Arrow.leftFunc.mapIso ea) (Arrow.rightFunc.mapIso ea) ea.hom.w.symm).symm

/-! ### The image of the derived tensor product -/

/-- **The image of `- ⊗_E^𝐋 K` lies in `D_QCoh(O)`** when the cohomology sheaves of `K` are
quasi-coherent, quasi-coherence is a weak Serre class and `hqcsum`, a direct sum of
quasi-coherent `O`-modules is quasi-coherent. -/
theorem derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsum
    [ObjectProperty.IsWeakSerreClass (tensorModOQuasicoherent.{u, v, w, t, s} X)]
    (hqcsum : ∀ {ι : Type (max u v w t s)} (Mf : ι → TensorModO.{u, v, w, t, s} X)
      (c : Cofan Mf), IsColimit c →
      (∀ i, tensorModOQuasicoherent.{u, v, w, t, s} X (Mf i)) →
      tensorModOQuasicoherent.{u, v, w, t, s} X c.pt)
    (hK : tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (M : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj M) := by
  classical
  let _hgr : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hqc : WeakSerre.IsWeakSerre (tensorModOQuasicoherent.{u, v, w, t, s} X) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc
  have hqcsum' : ∀ {ι : Type (max u v w t s)} (Mf : ι → TensorModO.{u, v, w, t, s} X),
      (∀ i, tensorModOQuasicoherent.{u, v, w, t, s} X (Mf i)) →
      tensorModOQuasicoherent.{u, v, w, t, s} X (∐ Mf) := fun Mf hMf =>
    hqcsum Mf _ (coproductIsCoproduct Mf) hMf
  refine General.property_of_coproducts_of_two_out_of_three_of_shifts
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
    (fun N => tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj N)) ?_ ?_ ?_ M
  · intro ι Mfam hMfam
    let _ := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
      (TensorModO.{u, v, w, t, s} X) ι
    refine hcl.of_iso
      (PreservesCoproduct.iso (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K) Mfam).symm ?_
    exact Stacks.Duality.derivedCategoryB_prop_coproduct (TensorModO.{u, v, w, t, s} X)
      (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc hqcsum' _ hMfam
  · intro Δ hΔ
    obtain ⟨T, hT, hO₁, hO₂, hO₃, ⟨e⟩⟩ :=
      exists_coneTriangle_leftOrthogonal_iso.{u, v, w, t, s} X K Δ hΔ
    have hmap := tensorWithComplexToDerivedCategory_negMor₃_distinguished.{u, v, w, t, s} X K T hT
    have htri := DerivedCategoryB.derivedCategoryB_isTriangulated
      (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc
    have eiso : ∀ {A : DifferentialGradedModule.derivedCategory.{0, max u v w t s,
        max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra}
        {O : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra},
        (A ≅ (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj O) →
        (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal O →
        ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj A ≅
          (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).obj O) :=
      fun f hO => (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso f ≪≫
        @asIso _ _ _ _ ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app _)
          (isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _ hO)
    have e₁ := eiso (Triangle.π₁.mapIso e) hO₁
    have e₂ := eiso (Triangle.π₂.mapIso e) hO₂
    have e₃ := eiso (Triangle.π₃.mapIso e) hO₃
    refine ⟨fun h₁ h₂ => ?_, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
    · exact hcl.of_iso e₃.symm
        ((tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₃
          _ hmap (hcl.of_iso e₁ h₁) (hcl.of_iso e₂ h₂))
    · exact hcl.of_iso e₂.symm
        ((tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₂
          _ hmap (hcl.of_iso e₁ h₁) (hcl.of_iso e₃ h₃))
    · exact hcl.of_iso e₁.symm
        ((tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₁
          _ hmap (hcl.of_iso e₂ h₂) (hcl.of_iso e₃ h₃))
  · intro k
    have hreg := derivedCategoryB_tensorWithComplexDerived_obj_regular.{u, v, w, t, s} X K hK
    have h0 : tensorModOQuasicoherentDerived.{u, v, w, t, s} X
        ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).obj
              (regularModule (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))) :=
      hcl.of_iso
        ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).mapIso
              DGCategory.representableSelfIsoRegular)) hreg
    exact hcl.of_iso
      (((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso k).app _).symm
      (DerivedCategoryB.derivedCategoryB_shift_mem
        (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc k h0)

/-! ### A scheme -/

/-- The standard model of the derived category of the ambient modules on the site of opens of a
scheme. -/
local instance hasDerivedCategorySchemeRingedSite (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1, u, u + 1} (TensorModO.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) :=
  HasDerivedCategory.standard _

/-- On the site of opens of a scheme, quasi-coherence of ambient modules is the quasi-coherence
of its sheaves of modules: the site and the sections of the structure sheaf lie in one
universe. -/
theorem tensorModOQuasicoherent_schemeRingedSite_eq (Y : Scheme.{u}) :
    tensorModOQuasicoherent.{u, u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) =
      SheafOfModules.isQuasicoherent Y.ringCatSheaf := by
  ext M
  exact (SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite M).symm

/-- Quasi-coherence on the site of opens of a scheme is a weak Serre class: it contains the zero
module and is closed under kernels, cokernels and extensions. -/
instance tensorModOQuasicoherent_schemeRingedSite_isWeakSerreClass (Y : Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass
      (tensorModOQuasicoherent.{u, u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) := by
  rw [tensorModOQuasicoherent_schemeRingedSite_eq Y]
  exact Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass Y

/-- A colimit of quasi-coherent modules on the site of opens of a scheme is quasi-coherent;
applied to a cofan, this is closure under direct sums. -/
theorem tensorModOQuasicoherent_schemeRingedSite_colimit (Y : Scheme.{u}) {ι : Type u}
    (Mf : ι → TensorModO.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y))
    (c : Cofan Mf) (hc : IsColimit c)
    (hMf : ∀ i, tensorModOQuasicoherent.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) (Mf i)) :
    tensorModOQuasicoherent.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) c.pt := by
  rw [tensorModOQuasicoherent_schemeRingedSite_eq Y] at hMf ⊢
  exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
    (fun i => hMf i.as) hc

/-- **Stacks 09M3.** *"Let `X` be a scheme, `K` a complex of `O_X`-modules with quasi-coherent
cohomology sheaves, `(E, d) = Hom(K, K)`. Then `- ⊗_E^𝐋 K : D(E, d) ⟶ D(O_X)` of Tag 09LX has
image contained in `D_QCoh(O_X)`."* The scheme is read as the ringed site of its opens. -/
@[stacks 09M3 "for the site of opens of the scheme"]
theorem derivedCategoryB_tensorWithComplexDerived_obj_scheme (Y : Scheme.{u})
    (K : CochainComplex (ModO.{u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) ℤ)
    (hK : tensorModOQuasicoherentDerived.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)
      (DerivedCategory.Q.obj (liftComplex.{u, u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) K)))
    (M : DifferentialGradedModule.derivedCategory.{0, u, u}
      (Rep.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) ℤ K).algebra) :
    tensorModOQuasicoherentDerived.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)
      ((tensorWithComplexDerived.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) ℤ K).obj M) :=
  derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsum.{u, u, u, u, u} _ K
    (fun Mf c hc hMf =>
      tensorModOQuasicoherent_schemeRingedSite_colimit Y Mf c hc hMf)
    hK M

/-- **Stacks 09M3.** Every cohomology sheaf of `M ⊗_E^𝐋 K` is a quasi-coherent `O_Y`-module, for
`Y` a scheme and `K` a complex of `O_Y`-modules with quasi-coherent cohomology sheaves. -/
@[stacks 09M3]
theorem derivedCategoryB_isQuasicoherent_tensorWithComplexDerived_obj_scheme (Y : Scheme.{u})
    (K : CochainComplex (ModO.{u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)) ℤ)
    (hK : tensorModOQuasicoherentDerived.{u, u, u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y)
      (DerivedCategory.Q.obj (liftComplex.{u, u, u, u, u}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) K)))
    (M : DifferentialGradedModule.derivedCategory.{0, u, u}
      (Rep.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) ℤ K).algebra) :
    DerivedCategoryB.derivedCategoryB
        (A := TensorModO.{u, u, u, u, u}
          (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y))
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      ((tensorWithComplexDerived.{u, u, u, u, u, 0}
        (Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite Y) ℤ K).obj M) := by
  have h := derivedCategoryB_tensorWithComplexDerived_obj_scheme Y K hK M
  rwa [tensorModOQuasicoherentDerived, tensorModOQuasicoherent_schemeRingedSite_eq Y] at h

end AlgebraicGeometry.RingedSite

end
