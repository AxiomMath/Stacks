module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceProof
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite

/-!
# The relative spectrum of a finite quasi-coherent algebra on an algebraic space

The relative spectrum `\underline{Spec}_X(𝒜)` of Stacks 081W exists for every quasi-coherent
`𝒪_X`-algebra `𝒜` with fewer than `B.cutoff` sections over every étale chart of `X`, which is
the bound every direct image of an affine morphism satisfies.  This file shows that an algebra of
finite type satisfies that bound outright, so that a quasi-coherent algebra of finite type — in
particular a finite one, or one of finite presentation — has a relative spectrum with no size
hypothesis at all, and it records the finiteness properties of that relative spectrum.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType`: an algebra sheaf of
  finite type has fewer than `B.cutoff` sections over every étale chart.
* `AlgebraicGeometry.Space.finiteTypeRelativeSpec`: the relative spectrum of a quasi-coherent
  algebra of finite type, with
  `AlgebraicGeometry.Space.pushforwardAlgebraFiniteTypeRelativeSpecIso` the identification of its
  direct image with the algebra.
* `AlgebraicGeometry.Space.isFinite_finiteTypeRelativeSpec` and
  `AlgebraicGeometry.Space.isFinitePresentation_finiteTypeRelativeSpec`: the relative spectrum of
  a finite, respectively finitely presented, quasi-coherent algebra is finite, respectively of
  finite presentation, over the base.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIntegral_of_isIntegral_affineChart`: a quasi-coherent
  algebra of finite type which is integral over one affine surjective étale chart is integral.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-- **An algebra sheaf of finite type has fewer than `B.cutoff` sections over every étale
chart.** -/
theorem AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsFiniteType) :
    AlgebraSheaf.SectionsBelowCutoff B S hS A := by
  intro V
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (A.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ A.right.property)
  set μ : Cardinal.{u} := (chartScheme V).size with hμ
  have hμ0 : ℵ₀ ≤ μ := Scheme.aleph0_le_size _
  have hμc : μ < B.cutoff := SmallEtale.contains_chartScheme B S hS X.1 V
  let r : A.right.obj.obj (op V) → ∀ O : (chartScheme V).affineOpens,
      A.right.obj.obj (op (openChart B S hS X.1 V O.1)) :=
    fun s O => A.right.obj.map (openChartInclusion B S hS X.1 V O.1).op s
  have hr : Function.Injective r := by
    intro s t hst
    refine (hsheaf _
      (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X.1 V)).isSeparatedFor.ext
        fun Y f hf => ?_
    obtain ⟨O, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    rw [op_comp, Functor.map_comp, types_comp_apply, types_comp_apply]
    exact congrArg _ (congrFun hst O.down)
  have hfac : ∀ O : (chartScheme V).affineOpens,
      #(A.right.obj.obj (op (openChart B S hS X.1 V O.1))) ≤ μ := by
    intro O
    have hf := hA (openChart B S hS X.1 V O.1) (isAffine_chartScheme_openChart B S hS X.1 V O)
    let : Algebra
        (↥((structureSheaf B S hS X.1 X.2).obj.obj (op (openChart B S hS X.1 V O.1))))
        (↥(A.right.obj.obj (op (openChart B S hS X.1 V O.1)))) :=
      (A.algebraMap (op (openChart B S hS X.1 V O.1))).toAlgebra
    have : Algebra.FiniteType
        (↥((structureSheaf B S hS X.1 X.2).obj.obj (op (openChart B S hS X.1 V O.1))))
        (↥(A.right.obj.obj (op (openChart B S hS X.1 V O.1)))) := hf
    exact (mk_le_of_algebra_finiteType
        (↥((structureSheaf B S hS X.1 X.2).obj.obj (op (openChart B S hS X.1 V O.1))))
        (↥(A.right.obj.obj (op (openChart B S hS X.1 V O.1))))).trans (max_le hμ0
      ((Scheme.mk_sections_coe_opens (chartScheme V) O.1).le.trans
        (Scheme.mk_sections_le_size (chartScheme V) O)))
  calc #(A.right.obj.obj (op V))
      ≤ #(∀ O : (chartScheme V).affineOpens,
          A.right.obj.obj (op (openChart B S hS X.1 V O.1))) := mk_le_of_injective hr
    _ = Cardinal.prod fun O : (chartScheme V).affineOpens =>
          #(A.right.obj.obj (op (openChart B S hS X.1 V O.1))) := mk_pi _
    _ ≤ Cardinal.prod fun _ : (chartScheme V).affineOpens => μ := Cardinal.prod_le_prod _ _ hfac
    _ = μ ^ #(chartScheme V).affineOpens := prod_const' _ _
    _ ≤ μ ^ μ := power_le_power_left (ne_of_gt (aleph0_pos.trans_le hμ0))
          (Scheme.mk_affineOpens_le_size _)
    _ = 2 ^ μ := power_self_eq hμ0
    _ < B.cutoff := B.cutoff_isStrongPrelimit hμc

/-- **The relative spectrum of a quasi-coherent algebra of finite type**, as an algebraic space
affine over `X`. -/
def finiteTypeRelativeSpec (A : QuasicoherentAlgebra B S hS X) (hA : A.obj.IsFiniteType) :
    AffineOver B S hS X :=
  boundedRelativeSpec B S hS A (AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType B S hS A.obj hA)

/-- **The direct image of the structure sheaf of the relative spectrum of a quasi-coherent algebra
of finite type is that algebra.** -/
def pushforwardAlgebraFiniteTypeRelativeSpecIso (A : QuasicoherentAlgebra B S hS X)
    (hA : A.obj.IsFiniteType) :
    pushforwardAlgebra B S hS (finiteTypeRelativeSpec B S hS A hA).obj ≅ A.obj :=
  pushforwardAlgebraBoundedRelativeSpecIso B S hS A
    (AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType B S hS A.obj hA)

/-- **The relative spectrum of a finite quasi-coherent algebra is finite over the base.** -/
theorem isFinite_finiteTypeRelativeSpec (A : QuasicoherentAlgebra B S hS X)
    (hA : A.obj.IsFinite) :
    IsFinite B S hS (finiteTypeRelativeSpec B S hS A hA.isFiniteType).obj.hom.hom :=
  isFinite_affineOver_of_isFinite_pushforwardAlgebra B S hS _
    (AlgebraSheaf.IsFinite.of_iso
      (pushforwardAlgebraFiniteTypeRelativeSpecIso B S hS A hA.isFiniteType).symm hA)

/-- **The relative spectrum of a quasi-coherent algebra of finite presentation is of finite
presentation over the base.** -/
theorem isFinitePresentation_finiteTypeRelativeSpec (A : QuasicoherentAlgebra B S hS X)
    (hA : A.obj.IsFinitePresentation) :
    IsFinitePresentation B S hS
      (finiteTypeRelativeSpec B S hS A hA.isFiniteType).obj.hom.hom :=
  isFinitePresentation_affineOver_of_isFinitePresentation_pushforwardAlgebra B S hS _
    (AlgebraSheaf.IsFinitePresentation.of_iso
      (pushforwardAlgebraFiniteTypeRelativeSpecIso B S hS A hA.isFiniteType).symm hA)

/-- **The relative spectrum of a bounded integral quasi-coherent algebra is integral over the
base.** -/
theorem isIntegralHom_boundedRelativeSpec (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) (hint : A.obj.IsIntegral) :
    IsIntegralHom B S hS (boundedRelativeSpec B S hS A hA).obj.hom.hom :=
  isIntegralHom_of_isIntegral_pushforwardAlgebra B S hS _
    (AlgebraSheaf.IsIntegral.of_iso (pushforwardAlgebraBoundedRelativeSpecIso B S hS A hA).symm
      hint)

/-! ### Integrality from one affine chart -/

/-- **Integrality of the structure-algebra map passes to a smaller chart over which the algebra is
a base change.** -/
theorem AlgebraSheaf.isIntegral_algebraMap_of_surjective_sectionsBaseChange
    (C : AlgebraSheaf.{u, u} B S hS X.1 X.2) {U V : SmallEtale B S hS X.1} (h : V ⟶ U)
    (hsurj : letI := chartAlgebra (hF := X.2) h
      Function.Surjective (sectionsBaseChange (AlgebraSheaf.underlyingModule C) h))
    (hint : RingHom.IsIntegral (C.algebraMap (op U))) :
    RingHom.IsIntegral (C.algebraMap (op V)) := by
  let := chartAlgebra (hF := X.2) h
  have hres : ∀ c : C.right.obj.obj (op U),
      (C.algebraMap (op V)).IsIntegralElem ((C.right.obj.map h.op).hom c) := by
    intro c
    obtain ⟨P, hPm, hP⟩ := hint c
    refine ⟨P.map ((structureSheaf B S hS X.1 X.2).obj.map h.op).hom, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (C.algebraMap (op V)).comp ((structureSheaf B S hS X.1 X.2).obj.map h.op).hom =
        (C.right.obj.map h.op).hom.comp (C.algebraMap (op U)) :=
      RingHom.ext fun r => (C.algebraMap_natural h.op r).symm
    rw [hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  intro y
  obtain ⟨t, rfl⟩ := hsurj y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | add a b ha hb => rw [map_add]; exact RingHom.IsIntegralElem.add _ ha hb
  | tmul o c =>
    rw [chartBaseChange_tmul]
    exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) (hres c)

/-- **A quasi-coherent algebra of finite type which is integral over one affine surjective étale
chart is integral.** -/
theorem AlgebraSheaf.isIntegral_of_isIntegral_affineChart (C : QuasicoherentAlgebra B S hS X)
    (hC : C.obj.IsFiniteType) {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ X.1}
    (hqs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hint : RingHom.IsIntegral (C.obj.algebraMap (op ⟨CostructuredArrow.mk q, hqe⟩))) :
    C.obj.IsIntegral := by
  let C0 : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk q, hqe⟩
  have hCc : IsCartesianOnAffineCharts (AlgebraSheaf.underlyingModule C.obj) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ C.property
  let P := finiteTypeRelativeSpec B S hS C hC
  let e := pushforwardAlgebraFiniteTypeRelativeSpecIso B S hS C hC
  have hP : IsIntegralHom B S hS P.obj.hom.hom := by
    refine isIntegralHom_of_isIntegral_pushforwardAlgebra_affineOpens B S hS P hqs hqe fun V => ?_
    let CV : SmallEtale B S hS X.1 :=
      ⟨CostructuredArrow.mk (yoneda.map (openObjHom B S hS U V.1) ≫ q),
        presheaf_etale_openObjHom_comp B S hS hqe V.1⟩
    let ιV : CV ⟶ C0 := ObjectProperty.homMk (CostructuredArrow.homMk (openObjHom B S hS U V.1) rfl)
    have hCV : RingHom.IsIntegral (C.obj.algebraMap (op CV)) :=
      AlgebraSheaf.isIntegral_algebraMap_of_surjective_sectionsBaseChange B S hS C.obj ιV
        (hCc C0 CV hU V.2 ιV).2 hint
    have hcomp : (pushforwardAlgebra B S hS P.obj).algebraMap (op CV) =
        (e.inv.right.hom.app (op CV)).hom.comp (C.obj.algebraMap (op CV)) :=
      RingHom.ext fun r => (e.inv.comm (op CV) r).symm
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ hCV
      (RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _
        (AlgebraSheaf.bijective_iso_right_app e.symm (op CV)).2))
  exact AlgebraSheaf.IsIntegral.of_iso e
    (isIntegral_pushforwardAlgebra_over_of_isIntegralHom B S hS P.obj
      (relativelyRepresentable_hom_of_isAffineHom B S hS P.obj.hom P.property) hP)

/-! ### Lifting a presentation by algebras of finite type to the bounded algebras -/

section Lift

universe v w

variable {B S hS} {I : Type w} [Category.{v} I]

/-- A diagram of quasi-coherent algebras of finite type, as a diagram of bounded ones. -/
abbrev boundedLift (D : I ⥤ QuasicoherentAlgebra B S hS X)
    (hD : ∀ i, (D.obj i).obj.IsFiniteType) : I ⥤ BoundedQuasicoherentAlgebra B S hS X :=
  ObjectProperty.lift _ D
    (fun i => AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType B S hS (D.obj i).obj (hD i))

/-- A cocone on a diagram of quasi-coherent algebras of finite type whose vertex is bounded, read
in the bounded algebras. -/
def boundedCocone (D : I ⥤ QuasicoherentAlgebra B S hS X)
    (hD : ∀ i, (D.obj i).obj.IsFiniteType) (A : BoundedQuasicoherentAlgebra B S hS X)
    (φ : D ⟶ (Functor.const I).obj
      ((boundedQuasicoherentAlgebraInclusion B S hS X).obj A)) :
    Cocone (boundedLift D hD) where
  pt := A
  ι :=
    { app := fun i => ObjectProperty.homMk (φ.app i)
      naturality := fun i j f => by
        apply ObjectProperty.hom_ext
        simp }

/-- **A colimit presentation by algebras of finite type is a colimit in the bounded
algebras.** -/
def isColimitBoundedCocone (D : I ⥤ QuasicoherentAlgebra B S hS X)
    (hD : ∀ i, (D.obj i).obj.IsFiniteType) (A : BoundedQuasicoherentAlgebra B S hS X)
    (φ : D ⟶ (Functor.const I).obj
      ((boundedQuasicoherentAlgebraInclusion B S hS X).obj A))
    (h : IsColimit (Cocone.mk
      ((boundedQuasicoherentAlgebraInclusion B S hS X).obj A) φ)) :
    IsColimit (boundedCocone D hD A φ) :=
  isColimitOfReflects (boundedQuasicoherentAlgebraInclusion B S hS X) h

end Lift


end AlgebraicGeometry.Space

end
