module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElement
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.CotangentPushout

/-!
# Square-zero thickenings of `Spec A` in the site

The trivial square-zero extensions, the pushout algebra and its image as square-zero
thickenings of `Spec A` over the base, their kernels, the morphisms between them, and the
base ring map of a thickening, as used in the proof of 07YY.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

/-! ### Square-zero thickenings of `Spec A` in the site -/

section Thickenings

open TensorProduct

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- A subring of a ring whose spectrum occurs in a big fppf site has its spectrum there too. -/
public theorem contains_Spec_subring (B : BigFppfSite.{u}) {R : Type u} [CommRing R]
    (R' : Subring R) (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of R')) :=
  Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R' hR

/-- The source of an open immersion into a scheme of a big fppf site occurs in that site; in
particular so does the affine open through which a structure morphism factors. -/
public theorem contains_of_isOpenImmersion (B : BigFppfSite.{u}) {U S : Scheme.{u}}
    (f : U ⟶ S) (hf : IsOpenImmersion f) (hS : B.Contains S) : B.Contains U :=
  have := hf
  Scheme.size_lt_of_isOpenImmersion f hS

/-- The pushout algebra of an extension with finite cotangent space occurs in any big fppf site
containing `Spec A`. -/
private theorem cotangentPushout_mem_site_of_finite_cotangentSpace
    (E : Algebra.Extension.{u} Λ A) [Module.Finite A E.CotangentSpace] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A))) : B.Contains (Spec (.of (cotangentPushout E))) := by
  have : Module.Finite A (cotangentPushout E) := by
    change Module.Finite A (A × E.CotangentSpace)
    infer_instance
  have : Algebra.FiniteType A (cotangentPushout E) := Module.Finite.finiteType _
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A
    (cotangentPushout E) hA

/-- The pushout algebra of a finite presentation occurs in any big fppf site containing
`Spec A`, the cotangent space of such a presentation being a finite free `A`-module. -/
public theorem cotangentPushout_mem_site {n : ℕ} (P : Algebra.Generators Λ A (Fin n))
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (cotangentPushout P.toExtension))) :=
  haveI := Module.Finite.of_basis P.cotangentSpaceBasis
  cotangentPushout_mem_site_of_finite_cotangentSpace P.toExtension B hA

/-- The image `C'` of `P/J²` in the pushout algebra occurs in any big fppf site that the
pushout algebra occurs in, being a subring of it. -/
public theorem cotangentPushoutImage_mem_site (E : Algebra.Extension.{u} Λ A)
    (B : BigFppfSite.{u}) (hC : B.Contains (Spec (.of (cotangentPushout E)))) :
    B.Contains (Spec (.of (cotangentPushoutImage E))) :=
  contains_Spec_subring B (cotangentPushoutImage E) hC

/-- The polynomial ring of a finite presentation of `A` over `Λ` occurs in any big fppf site
containing `Spec Λ`, being of finite type over `Λ`. -/
public theorem presentation_mem_site {n : ℕ} (P : Algebra.Generators Λ A (Fin n))
    (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ))) :
    B.Contains (Spec (.of P.Ring)) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit Λ P.Ring hΛ

/-- The infinitesimal extension `P/J²` of an extension of `A` over `Λ` is a quotient of the
extension ring, so its spectrum occurs in any big fppf site containing that of the extension
ring. -/
public theorem infinitesimal_mem_site (E : Algebra.Extension.{u} Λ A) (B : BigFppfSite.{u})
    (hE : B.Contains (Spec (.of E.Ring))) :
    B.Contains (Spec (.of E.infinitesimal.Ring)) := by
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hE ?_
  refine le_trans (Cardinal.mk_le_of_surjective
    (f := fun x : E.Ring => Ideal.Quotient.mk (E.ker ^ 2) x) ?_) (le_max_right _ _)
  exact Ideal.Quotient.mk_surjective

/-- An algebra of finite type admits a presentation whose generators are indexed by a finite
type in the universe of the algebra. -/
public theorem exists_finite_generators (hft : Algebra.FiniteType Λ A) :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (Algebra.Generators Λ A ι) := by
  obtain ⟨s, hs⟩ := hft.out
  exact ⟨((s : Set A) : Type u), inferInstance, ⟨Algebra.Generators.ofSet hs⟩⟩

/-- The pushout algebra of a presentation with finitely many generators occurs in any big fppf
site containing `Spec A`, the cotangent space of such a presentation being finite free. -/
public theorem cotangentPushout_mem_site_of_finite {ι : Type u} [Finite ι]
    (P : Algebra.Generators Λ A ι) (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (cotangentPushout P.toExtension))) :=
  haveI := Module.Finite.of_basis P.cotangentSpaceBasis
  cotangentPushout_mem_site_of_finite_cotangentSpace P.toExtension B hA

/-- The polynomial ring of a presentation with finitely many generators occurs in any big fppf
site containing `Spec Λ`, being of finite type over `Λ`. -/
public theorem presentation_mem_site_of_finite {ι : Type u} [Finite ι]
    (P : Algebra.Generators Λ A ι) (B : BigFppfSite.{u})
    (hΛ : B.Contains (Spec (.of Λ))) :
    B.Contains (Spec (.of P.Ring)) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit Λ P.Ring hΛ

/-- The image under a ring map over `A` of an element of the kernel of a square-zero
surjection lies in the kernel of the target surjection. -/
public theorem mem_ker_comp {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] {q₁ : A₁ →+* A}
    {q₂ : A₂ →+* A} (f : A₁ →+* A₂) (hf : q₂.comp f = q₁) (y : RingHom.ker q₁) :
    f y.1 ∈ RingHom.ker q₂ := by
  have hy : q₁ y.1 = 0 := y.2
  rw [RingHom.mem_ker, ← RingHom.comp_apply, hf, hy]

/-- The restriction to kernels of a ring map over `A` between square-zero surjections onto
`A`, as a map of `A`-modules: a scalar of `A` acts on either kernel through any of its
preimages, and the map carries a preimage to a preimage. -/
public def kerRestrict {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] {q₁ : A₁ →+* A}
    {q₂ : A₂ →+* A} (h₁ : IsDeformationSituation q₁) (h₂ : IsDeformationSituation q₂)
    (f : A₁ →+* A₂) (hf : q₂.comp f = q₁) :
    letI := Stacks.Smooth.kerModule h₁.1 h₁.2
    letI := Stacks.Smooth.kerModule h₂.1 h₂.2
    RingHom.ker q₁ →ₗ[A] RingHom.ker q₂ := by
  letI := Stacks.Smooth.kerModule h₁.1 h₁.2
  letI := Stacks.Smooth.kerModule h₂.1 h₂.2
  refine
    { toFun := fun y => ⟨f y.1, mem_ker_comp f hf y⟩
      map_add' := fun y z => Subtype.ext (by simp)
      map_smul' := ?_ }
  intro a y
  obtain ⟨x, hx⟩ := h₁.1 a
  have hfx : q₂ (f x) = q₁ x := by rw [← RingHom.comp_apply, hf]
  subst hx
  simp only [RingHom.id_apply]
  rw [Stacks.Smooth.kerModule_smul h₁.1 h₁.2, ← hfx,
    Stacks.Smooth.kerModule_smul h₂.1 h₂.2]
  exact Subtype.ext (by simp)

/-! ### The kernels of the thickenings of the proof of 07YY -/

/-- On an extension whose kernel squares to zero the conormal projection is injective. -/
public theorem extensionCotangentMk_injective (F : Algebra.Extension.{u} Λ A)
    (hsq : F.ker ^ 2 = ⊥) {a b : RingHom.ker (algebraMap F.Ring A)}
    (h : Algebra.Extension.Cotangent.mk (P := F) a = Algebra.Extension.Cotangent.mk b) :
    a.1 = b.1 := by
  have hz : Algebra.Extension.Cotangent.mk (P := F) (a - b) = 0 := by
    rw [map_sub, h, sub_self]
  have hs := (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := F) (a - b)).mp hz
  rw [hsq, Ideal.mem_bot] at hs
  exact sub_eq_zero.mp (by simpa using hs)

/-- For an extension whose kernel squares to zero the kernel is its own conormal module. -/
public def extensionKernelCotangentEquiv (F : Algebra.Extension.{u} Λ A)
    (hsq : F.ker ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule F.algebraMap_surjective hsq
    RingHom.ker (algebraMap F.Ring A) ≃ₗ[A] F.Cotangent := by
  letI := Stacks.Smooth.kerModule F.algebraMap_surjective hsq
  letI : IsScalarTower F.Ring A (RingHom.ker (algebraMap F.Ring A)) :=
    IsScalarTower.of_algebraMap_smul fun a i =>
      Stacks.Smooth.kerModule_smul F.algebraMap_surjective hsq a i
  refine LinearEquiv.ofBijective
    ((Algebra.Extension.Cotangent.mk (P := F)).extendScalarsOfSurjective
      F.algebraMap_surjective) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (extensionCotangentMk_injective F hsq h)
  · exact Algebra.Extension.Cotangent.mk_surjective

/-- The equivalence `extensionKernelCotangentEquiv F hsq` sends an element of the kernel to
its class in the conormal module. -/
@[simp] public theorem extensionKernelCotangentEquiv_apply (F : Algebra.Extension.{u} Λ A)
    (hsq : F.ker ^ 2 = ⊥) (y : RingHom.ker (algebraMap F.Ring A)) :
    letI := Stacks.Smooth.kerModule F.algebraMap_surjective hsq
    extensionKernelCotangentEquiv F hsq y = Algebra.Extension.Cotangent.mk y :=
  rfl

/-- The kernel of `P/J² → A` is the conormal module `J/J²` of the extension. -/
public def infinitesimalKernelEquiv (E : Algebra.Extension.{u} Λ A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal E).1
      (isDeformationSituation_infinitesimal E).2
    RingHom.ker (algebraMap E.infinitesimal.Ring A) ≃ₗ[A] E.Cotangent :=
  letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal E).1
    (isDeformationSituation_infinitesimal E).2
  (extensionKernelCotangentEquiv E.infinitesimal
      (isDeformationSituation_infinitesimal E).2).trans
    (LinearEquiv.ofBijective (Algebra.Extension.Cotangent.map E.toInfinitesimal)
      (Algebra.Extension.Cotangent.map_toInfinitesimal_bijective E)).symm

/-- The identification of the kernel of `P/J² → A` with `J/J²` is characterized by the
comparison of conormal modules along the quotient by `J²`. -/
public theorem map_toInfinitesimal_infinitesimalKernelEquiv (E : Algebra.Extension.{u} Λ A)
    (y : RingHom.ker (algebraMap E.infinitesimal.Ring A)) :
    Algebra.Extension.Cotangent.map E.toInfinitesimal (infinitesimalKernelEquiv E y) =
      Algebra.Extension.Cotangent.mk y :=
  (LinearEquiv.ofBijective (Algebra.Extension.Cotangent.map E.toInfinitesimal)
    (Algebra.Extension.Cotangent.map_toInfinitesimal_bijective E)).apply_symm_apply _

/-- The map `P/J² → A` sends the class of `g` to the image of `g` in `A`. -/
private theorem algebraMap_infinitesimal_mk (E : Algebra.Extension.{u} Λ A) (g : E.Ring) :
    algebraMap E.infinitesimal.Ring A (Ideal.Quotient.mk (E.ker ^ 2) g) =
      algebraMap E.Ring A g :=
  rfl

/-- The class in `P/J²` of an element of the kernel of the presentation lies in the kernel of
`P/J² → A`. -/
public theorem quotient_mk_mem_ker_infinitesimal (E : Algebra.Extension.{u} Λ A) (x : E.ker) :
    Ideal.Quotient.mk (E.ker ^ 2) x.1 ∈ RingHom.ker (algebraMap E.infinitesimal.Ring A) :=
  (algebraMap_infinitesimal_mk E x.1).trans x.2

/-- The identification of the kernel of `P/J² → A` with `J/J²` carries the class of `j ∈ J`
in `P/J²` to the class of `j` in `J/J²`. -/
public theorem infinitesimalKernelEquiv_mk (E : Algebra.Extension.{u} Λ A) (x : E.ker) :
    infinitesimalKernelEquiv E
        ⟨Ideal.Quotient.mk (E.ker ^ 2) x.1, quotient_mk_mem_ker_infinitesimal E x⟩ =
      Algebra.Extension.Cotangent.mk x := by
  refine (Algebra.Extension.Cotangent.map_toInfinitesimal_bijective E).1 ?_
  rw [map_toInfinitesimal_infinitesimalKernelEquiv, Algebra.Extension.Cotangent.map_mk]
  rfl

/-- The kernel of the projection `A[M] → A` of a trivial square-zero extension is `M`: a
scalar of `A` acts on the kernel through any of its preimages, and multiplying by a preimage
multiplies the second component by the scalar. -/
public def squareZeroExtKernelEquiv (M : ModuleCat.{u} A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
      (isDeformationSituation_squareZeroExt M).2
    RingHom.ker (squareZeroExtProj M) ≃ₗ[A] M := by
  letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
    (isDeformationSituation_squareZeroExt M).2
  refine
    { toFun := fun y => (y : squareZeroExt M).snd
      map_add' := fun y z => rfl
      map_smul' := ?_
      invFun := fun v => ⟨TrivSqZeroExt.inr v, TrivSqZeroExt.fst_inr A v⟩
      left_inv := fun y => Subtype.ext (TrivSqZeroExt.ext y.2.symm rfl)
      right_inv := fun v => rfl }
  intro a y
  obtain ⟨x, hx⟩ := (isDeformationSituation_squareZeroExt M).1 a
  subst hx
  simp only [RingHom.id_apply]
  rw [Stacks.Smooth.kerModule_smul (isDeformationSituation_squareZeroExt M).1
    (isDeformationSituation_squareZeroExt M).2]
  have hy : (y : squareZeroExt M).fst = 0 := y.2
  have hcoe : ((x • y : RingHom.ker (squareZeroExtProj M)) : squareZeroExt M) =
      x * (y : squareZeroExt M) := rfl
  rw [hcoe, TrivSqZeroExt.snd_mul, hy]
  simp

/-- The equivalence `squareZeroExtKernelEquiv M` sends an element of the kernel of
`A[M] → A` to its module component. -/
@[simp] public theorem squareZeroExtKernelEquiv_apply (M : ModuleCat.{u} A)
    (y : RingHom.ker (squareZeroExtProj M)) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
      (isDeformationSituation_squareZeroExt M).2
    squareZeroExtKernelEquiv M y = (y : squareZeroExt M).snd :=
  rfl

/-- Under the identifications of the two kernels with the conormal module and the cotangent
space, the map of kernels of `P/J² ⟶ C` is the differential of the naive cotangent complex of
the presentation. -/
public theorem squareZeroExtKernelEquiv_kerRestrict_infinitesimal
    (E : Algebra.Extension.{u} Λ A)
    (y : RingHom.ker (algebraMap E.infinitesimal.Ring A)) :
    squareZeroExtKernelEquiv (cotangentSpaceModule E)
        (kerRestrict (isDeformationSituation_infinitesimal E)
          (isDeformationSituation_cotangentPushout E) (cotangentPushoutInfinitesimalMap E)
          (cotangentPushoutProj_comp_infinitesimalMap E) y) =
      E.cotangentComplex (infinitesimalKernelEquiv E y) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hg : g ∈ E.ker := (algebraMap_infinitesimal_mk E g).symm.trans hy
  have hlhs : squareZeroExtKernelEquiv (cotangentSpaceModule E)
      (kerRestrict (isDeformationSituation_infinitesimal E)
        (isDeformationSituation_cotangentPushout E) (cotangentPushoutInfinitesimalMap E)
        (cotangentPushoutProj_comp_infinitesimalMap E)
        ⟨Ideal.Quotient.mk (E.ker ^ 2) g, hy⟩) = (cotangentPushoutFun E g).snd := rfl
  have hsub : (⟨Ideal.Quotient.mk (E.ker ^ 2) g, hy⟩ :
      RingHom.ker (algebraMap E.infinitesimal.Ring A)) =
      ⟨Ideal.Quotient.mk (E.ker ^ 2) (⟨g, hg⟩ : E.ker).1,
        quotient_mk_mem_ker_infinitesimal E ⟨g, hg⟩⟩ := rfl
  rw [hlhs, cotangentPushoutFun_snd, hsub, infinitesimalKernelEquiv_mk,
    Algebra.Extension.cotangentComplex_mk]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- A trivial square-zero extension `A[M]` whose spectrum occurs in the site is a square-zero
thickening of `Spec A` over `S`: its projection to `A` is a square-zero surjection, and it
lies over `S` through the section `A ⟶ A[M]`. -/
public def squareZeroExtThickening (M : ModuleCat.{u} A)
    (hM : B.Contains (Spec (squareZeroRing A M))) :
    SquareZeroThickening A B S hS toS hA (squareZeroExt M) where
  q := squareZeroExtProj M
  squareZeroSurjection := isDeformationSituation_squareZeroExt M
  hA' := hM
  toS' := (squareZeroOver A B S hS toS (⟨M, hM⟩ : SiteModule A B)).hom
  arrow := squareZeroArrow A B S hS toS hA ⟨M, hM⟩
  arrow_spec := rfl

/-- The trivial square-zero extension `C̄ = A[Ω_{A/Λ}]` is a square-zero thickening of
`Spec A` over `S` when `A` is of finite type over `Λ`. -/
public def differentialsThickening (hft : Algebra.FiniteType Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    SquareZeroThickening A B S hS toS hA (squareZeroExt (differentialsModule Λ A)) :=
  squareZeroExtThickening B S hS toS hA (differentialsModule Λ A)
    (differentialsSquareZero_mem_site Λ A B hA hft)

/-- A square-zero surjection `A' → A` whose spectrum occurs in the site and which carries a
ring map from `Λ` over `A` is a square-zero thickening of `Spec A` over `S`: it lies over `S`
through the affine open `Spec Λ` of the base. This is the structure morphism used for the
thickenings of the proof of 07YY which admit no section. -/
public def thickeningOverBase (A' : Type u) [CommRing A'] (q : A' →+* A)
    (hq : IsDeformationSituation q) (hA' : B.Contains (Spec (.of A'))) (g : Λ →+* A')
    (hg : q.comp g = algebraMap Λ A) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening A B S hS toS hA A' where
  q := q
  squareZeroSurjection := hq
  hA' := hA'
  toS' := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom g) ≫ affineOpen)
  arrow := by
    refine Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom q)) :
      B.obj hA ⟶ B.obj hA') ?_
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom q) ≫
      Spec.map (CommRingCat.ofHom g) ≫ affineOpen = toS
    have hcomp : CommRingCat.ofHom g ≫ CommRingCat.ofHom q =
        CommRingCat.ofHom (algebraMap Λ A) := by
      rw [← CommRingCat.ofHom_comp, hg]
    rw [← Category.assoc, ← Spec.map_comp, hcomp]
    exact hfact
  arrow_spec := rfl

/-- A morphism of square-zero thickenings of `Spec A` from a ring map over `A` which lies
over the base, its map of kernels being the restriction of the ring map. -/
public def thickeningHom {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D₁ : SquareZeroThickening A B S hS toS hA A₁)
    (D₂ : SquareZeroThickening A B S hS toS hA A₂) (f : A₁ →+* A₂)
    (hf : D₂.q.comp f = D₁.q)
    (hover : Spec.map (CommRingCat.ofHom f) ≫ B.inclusion.map D₁.toS' =
      B.inclusion.map D₂.toS') :
    SquareZeroThickening.Hom D₁ D₂ where
  ringHom := f
  overBase := hf
  overS := hover
  kernelMap :=
    letI := Stacks.Smooth.kerModule D₁.squareZeroSurjection.1 D₁.squareZeroSurjection.2
    letI := Stacks.Smooth.kerModule D₂.squareZeroSurjection.1 D₂.squareZeroSurjection.2
    ModuleCat.ofHom (kerRestrict D₁.squareZeroSurjection D₂.squareZeroSurjection f hf)
  kernelMap_spec _ := rfl

/-! ### The thickenings of the proof of 07YY -/

/-- The canonical map of a presentation into the pushout algebra is a map of `Λ`-algebras:
the universal derivation kills a scalar of `Λ`, so such a scalar is carried to the
corresponding element of the section of the pushout algebra. -/
public theorem cotangentPushoutMap_algebraMap (E : Algebra.Extension.{u} Λ A) (r : Λ) :
    cotangentPushoutMap E (algebraMap Λ E.Ring r) =
      TrivSqZeroExt.inl (algebraMap Λ A r) := by
  ext
  · rw [cotangentPushoutMap_apply, cotangentPushoutFun_fst, TrivSqZeroExt.fst_inl,
      ← IsScalarTower.algebraMap_apply]
  · rw [cotangentPushoutMap_apply, cotangentPushoutFun_snd, TrivSqZeroExt.snd_inl,
      Derivation.map_algebraMap, TensorProduct.tmul_zero]

/-- The map `Λ ⟶ A[M]` into a trivial square-zero extension, the structure map of `A`
followed by the section. -/
public def squareZeroExtBaseMap (M : ModuleCat.{u} A) : Λ →+* squareZeroExt M :=
  (TrivSqZeroExt.inlHom A M).comp (algebraMap Λ A)

/-- The map `Λ ⟶ A[M]` lies over `A`. -/
public theorem squareZeroExtBaseMap_spec (M : ModuleCat.{u} A) :
    (squareZeroExtProj M).comp (squareZeroExtBaseMap M) = algebraMap Λ A := by
  refine RingHom.ext fun r => ?_
  show (TrivSqZeroExt.inl (algebraMap Λ A r) : squareZeroExt M).fst = algebraMap Λ A r
  rw [TrivSqZeroExt.fst_inl]

/-- The map `Λ ⟶ C` of the proof of 07YY, the structure map of the presentation followed by
the canonical map into the pushout algebra. -/
public def cotangentPushoutBaseMap (E : Algebra.Extension.{u} Λ A) :
    Λ →+* cotangentPushout E :=
  (cotangentPushoutMap E).comp (algebraMap Λ E.Ring)

/-- The map `Λ ⟶ C` lies over `A`. -/
public theorem cotangentPushoutBaseMap_spec (E : Algebra.Extension.{u} Λ A) :
    (cotangentPushoutProj E).comp (cotangentPushoutBaseMap E) = algebraMap Λ A := by
  refine RingHom.ext fun r => ?_
  show (cotangentPushoutMap E (algebraMap Λ E.Ring r)).fst = algebraMap Λ A r
  rw [cotangentPushoutMap_algebraMap, TrivSqZeroExt.fst_inl]

/-- The map `Λ ⟶ P/J²` of the proof of 07YY, the structure map of the presentation followed
by the quotient by `J²`. -/
public def infinitesimalBaseMap (E : Algebra.Extension.{u} Λ A) :
    Λ →+* E.infinitesimal.Ring :=
  (Ideal.Quotient.mk (E.ker ^ 2)).comp (algebraMap Λ E.Ring)

/-- The map `Λ ⟶ P/J²` lies over `A`. -/
public theorem infinitesimalBaseMap_spec (E : Algebra.Extension.{u} Λ A) :
    (algebraMap E.infinitesimal.Ring A).comp (infinitesimalBaseMap E) = algebraMap Λ A := by
  refine RingHom.ext fun r => ?_
  exact (algebraMap_infinitesimal_mk E _).trans (IsScalarTower.algebraMap_apply Λ E.Ring A r).symm

/-- The map `Λ ⟶ C'` of the proof of 07YY: a scalar of `Λ` lands in the image of `P/J²` in
the pushout algebra. -/
public def cotangentPushoutImageBaseMap (E : Algebra.Extension.{u} Λ A) :
    Λ →+* cotangentPushoutImage E :=
  (cotangentPushoutInfinitesimalMap E).rangeRestrict.comp (infinitesimalBaseMap E)

/-- The map `Λ ⟶ C'` lies over `A`. -/
public theorem cotangentPushoutImageBaseMap_spec (E : Algebra.Extension.{u} Λ A) :
    (cotangentPushoutImageProj E).comp (cotangentPushoutImageBaseMap E) = algebraMap Λ A :=
  cotangentPushoutBaseMap_spec E

/-- **`P/J² → A` is a square-zero thickening of `Spec A` over `S`.** -/
public def infinitesimalThickening (E : Algebra.Extension.{u} Λ A)
    (hE : B.Contains (Spec (.of E.Ring))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening A B S hS toS hA E.infinitesimal.Ring :=
  thickeningOverBase B S hS toS hA _ (algebraMap E.infinitesimal.Ring A)
    (isDeformationSituation_infinitesimal E) (infinitesimal_mem_site E B hE)
    (infinitesimalBaseMap E) (infinitesimalBaseMap_spec E) affineOpen hfact

/-- **`C' → A` is a square-zero thickening of `Spec A` over `S`**, where `C'` is the image of
`P/J²` in the pushout algebra `C`. -/
public def cotangentPushoutImageThickening (E : Algebra.Extension.{u} Λ A)
    (hC' : B.Contains (Spec (.of (cotangentPushoutImage E))))
    (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening A B S hS toS hA (cotangentPushoutImage E) :=
  thickeningOverBase B S hS toS hA _ (cotangentPushoutImageProj E)
    (isDeformationSituation_cotangentPushoutImage E) hC'
    (cotangentPushoutImageBaseMap E) (cotangentPushoutImageBaseMap_spec E) affineOpen hfact

/-- **`C → A` is a square-zero thickening of `Spec A` over `S`**, where `C` is the pushout
algebra of the presentation. -/
public def cotangentPushoutThickening (E : Algebra.Extension.{u} Λ A)
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening A B S hS toS hA (cotangentPushout E) :=
  thickeningOverBase B S hS toS hA _ (cotangentPushoutProj E)
    (isDeformationSituation_cotangentPushout E) hC
    (cotangentPushoutBaseMap E) (cotangentPushoutBaseMap_spec E) affineOpen hfact

/-- **`A[M] → A` is a square-zero thickening of `Spec A` over `S`**, lying over `S` through
the affine open `Spec Λ` rather than through its own section. -/
public def squareZeroExtBaseThickening (M : ModuleCat.{u} A)
    (hM : B.Contains (Spec (squareZeroRing A M))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening A B S hS toS hA (squareZeroExt M) :=
  thickeningOverBase B S hS toS hA _ (squareZeroExtProj M)
    (isDeformationSituation_squareZeroExt M) hM (squareZeroExtBaseMap M)
    (squareZeroExtBaseMap_spec M) affineOpen hfact

/-- **`C̄ = A[Ω_{A/Λ}] → A` is a square-zero thickening of `Spec A` over `S`** when `A` is of
finite type over `Λ`, lying over `S` through the affine open `Spec Λ`. -/
public def differentialsBaseThickening (hft : Algebra.FiniteType Λ A)
    (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    SquareZeroThickening A B S hS toS hA (squareZeroExt (differentialsModule Λ A)) :=
  squareZeroExtBaseThickening B S hS toS hA (differentialsModule Λ A)
    (differentialsSquareZero_mem_site Λ A B hA hft) affineOpen hfact

/-! ### Morphisms between the thickenings of the proof of 07YY -/

/-- A ring map over `A` and over `Λ` between two square-zero thickenings of `Spec A` which
lie over `S` through the affine open `Spec Λ` is a morphism of square-zero thickenings. -/
public def thickeningOverBaseHom (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
    (q₁ : A₁ →+* A) (hq₁ : IsDeformationSituation q₁) (hA₁ : B.Contains (Spec (.of A₁)))
    (g₁ : Λ →+* A₁) (hg₁ : q₁.comp g₁ = algebraMap Λ A) (q₂ : A₂ →+* A)
    (hq₂ : IsDeformationSituation q₂) (hA₂ : B.Contains (Spec (.of A₂))) (g₂ : Λ →+* A₂)
    (hg₂ : q₂.comp g₂ = algebraMap Λ A) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS)
    (f : A₁ →+* A₂) (hf : q₂.comp f = q₁) (hgf : f.comp g₁ = g₂) :
    SquareZeroThickening.Hom
      (thickeningOverBase B S hS toS hA A₁ q₁ hq₁ hA₁ g₁ hg₁ affineOpen hfact)
      (thickeningOverBase B S hS toS hA A₂ q₂ hq₂ hA₂ g₂ hg₂ affineOpen hfact) :=
  thickeningHom B S hS toS hA _ _ f hf (by
    have hcomp : CommRingCat.ofHom g₁ ≫ CommRingCat.ofHom f = CommRingCat.ofHom g₂ := by
      rw [← CommRingCat.ofHom_comp, hgf]
    change Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g₁) ≫ affineOpen =
      Spec.map (CommRingCat.ofHom g₂) ≫ affineOpen
    rw [← Category.assoc, ← Spec.map_comp, hcomp])

/-- **The morphism `(x, C → A) → (x, C' → A)` of the proof of 07YY**: the inclusion of the
image of `P/J²` into the pushout algebra, as a morphism of square-zero thickenings. -/
public def cotangentPushoutImageToPushoutHom (E : Algebra.Extension.{u} Λ A)
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening.Hom
      (cotangentPushoutImageThickening B S hS toS hA E
        (cotangentPushoutImage_mem_site E B hC) affineOpen hfact)
      (cotangentPushoutThickening B S hS toS hA E hC affineOpen hfact) :=
  thickeningOverBaseHom B S hS toS hA (cotangentPushoutImage E) (cotangentPushout E)
    (cotangentPushoutImageProj E) (isDeformationSituation_cotangentPushoutImage E)
    (cotangentPushoutImage_mem_site E B hC) (cotangentPushoutImageBaseMap E)
    (cotangentPushoutImageBaseMap_spec E) (cotangentPushoutProj E)
    (isDeformationSituation_cotangentPushout E) hC (cotangentPushoutBaseMap E)
    (cotangentPushoutBaseMap_spec E) affineOpen hfact (cotangentPushoutImage E).subtype rfl
    rfl

/-- **The morphism `(x, C → A) → (x, P/J² → A)` of the proof of 07YY**: the canonical map of
the infinitesimal extension of the presentation into the pushout algebra, as a morphism of
square-zero thickenings. -/
public def infinitesimalToPushoutHom (E : Algebra.Extension.{u} Λ A)
    (hE : B.Contains (Spec (.of E.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening.Hom
      (infinitesimalThickening B S hS toS hA E hE affineOpen hfact)
      (cotangentPushoutThickening B S hS toS hA E hC affineOpen hfact) :=
  thickeningOverBaseHom B S hS toS hA E.infinitesimal.Ring (cotangentPushout E)
    (algebraMap E.infinitesimal.Ring A) (isDeformationSituation_infinitesimal E)
    (infinitesimal_mem_site E B hE) (infinitesimalBaseMap E) (infinitesimalBaseMap_spec E)
    (cotangentPushoutProj E) (isDeformationSituation_cotangentPushout E) hC
    (cotangentPushoutBaseMap E) (cotangentPushoutBaseMap_spec E) affineOpen hfact
    (cotangentPushoutInfinitesimalMap E) (cotangentPushoutProj_comp_infinitesimalMap E) rfl

/-- **The morphism `(x, C' → A) → (x, P/J² → A)` of the proof of 07YY**: the surjection of
the infinitesimal extension onto its image in the pushout algebra, as a morphism of
square-zero thickenings. -/
public def infinitesimalToPushoutImageHom (E : Algebra.Extension.{u} Λ A)
    (hE : B.Contains (Spec (.of E.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening.Hom
      (infinitesimalThickening B S hS toS hA E hE affineOpen hfact)
      (cotangentPushoutImageThickening B S hS toS hA E
        (cotangentPushoutImage_mem_site E B hC) affineOpen hfact) :=
  thickeningOverBaseHom B S hS toS hA E.infinitesimal.Ring (cotangentPushoutImage E)
    (algebraMap E.infinitesimal.Ring A) (isDeformationSituation_infinitesimal E)
    (infinitesimal_mem_site E B hE) (infinitesimalBaseMap E) (infinitesimalBaseMap_spec E)
    (cotangentPushoutImageProj E) (isDeformationSituation_cotangentPushoutImage E)
    (cotangentPushoutImage_mem_site E B hC) (cotangentPushoutImageBaseMap E)
    (cotangentPushoutImageBaseMap_spec E) affineOpen hfact
    (cotangentPushoutInfinitesimalMap E).rangeRestrict
    (cotangentPushoutProj_comp_infinitesimalMap E) rfl

/-- **The morphism `(x, A[M] → A) → (x, C → A)` of the proof of 07YY**, induced by a map out
of the cotangent space of the presentation; for the conormal surjection onto `Ω_{A/Λ}` this
is the map `C ⟶ C̄` of the source. -/
public def cotangentPushoutToSquareZeroExtHom (E : Algebra.Extension.{u} Λ A)
    (M : ModuleCat.{u} A) (f : cotangentSpaceModule E ⟶ M)
    (hC : B.Contains (Spec (.of (cotangentPushout E))))
    (hM : B.Contains (Spec (squareZeroRing A M))) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    SquareZeroThickening.Hom
      (cotangentPushoutThickening B S hS toS hA E hC affineOpen hfact)
      (squareZeroExtBaseThickening B S hS toS hA M hM affineOpen hfact) :=
  thickeningOverBaseHom B S hS toS hA (cotangentPushout E) (squareZeroExt M)
    (cotangentPushoutProj E) (isDeformationSituation_cotangentPushout E) hC
    (cotangentPushoutBaseMap E) (cotangentPushoutBaseMap_spec E) (squareZeroExtProj M)
    (isDeformationSituation_squareZeroExt M) hM (squareZeroExtBaseMap M)
    (squareZeroExtBaseMap_spec M) affineOpen hfact (cotangentPushoutHom E f)
    (RingHom.ext fun x => fst_cotangentPushoutHom E f x)
    (by
      refine RingHom.ext fun r => ?_
      change cotangentPushoutHom E f (cotangentPushoutMap E (algebraMap Λ E.Ring r)) =
        TrivSqZeroExt.inl (algebraMap Λ A r)
      rw [cotangentPushoutMap_algebraMap]
      exact TrivSqZeroExt.map_inl f.hom _)

/-- **The morphism `(x, C → A) → (x, C̄ → A)` of the proof of 07YY**, the derivation-twisted
surjection of the pushout algebra onto `A[Ω_{A/Λ}]` as a morphism of square-zero
thickenings. -/
public def cotangentPushoutToDifferentialsThickeningHom (E : Algebra.Extension.{u} Λ A)
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (hft : Algebra.FiniteType Λ A)
    (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    SquareZeroThickening.Hom
      (cotangentPushoutThickening B S hS toS hA E hC affineOpen hfact)
      (differentialsBaseThickening B S hS toS hA hft affineOpen hfact) :=
  letI := oppositeModule A (differentialsModule Λ A)
  letI := centralScalar A (differentialsModule Λ A)
  thickeningOverBaseHom B S hS toS hA (cotangentPushout E)
    (squareZeroExt (differentialsModule Λ A)) (cotangentPushoutProj E)
    (isDeformationSituation_cotangentPushout E) hC (cotangentPushoutBaseMap E)
    (cotangentPushoutBaseMap_spec E) (squareZeroExtProj (differentialsModule Λ A))
    (isDeformationSituation_squareZeroExt _)
    (differentialsSquareZero_mem_site Λ A B hA hft)
    (squareZeroExtBaseMap (differentialsModule Λ A))
    (squareZeroExtBaseMap_spec (differentialsModule Λ A)) affineOpen hfact
    (cotangentPushoutToDifferentialsTwisted E)
    (RingHom.ext fun x => fst_cotangentPushoutToDifferentialsTwisted E x)
    (by
      refine RingHom.ext fun r => ?_
      have h : cotangentPushoutBaseMap E r = TrivSqZeroExt.inl (algebraMap Λ A r) :=
        cotangentPushoutMap_algebraMap E r
      rw [RingHom.comp_apply, h]
      have hb : squareZeroExtBaseMap (differentialsModule Λ A) r =
          TrivSqZeroExt.inl (algebraMap Λ A r) := rfl
      rw [hb]
      have hfst : (TrivSqZeroExt.inl (algebraMap Λ A r) :
          squareZeroExt (differentialsModule Λ A)).fst = algebraMap Λ A r :=
        TrivSqZeroExt.fst_inl A _
      have hsnd : (TrivSqZeroExt.inl (algebraMap Λ A r) :
          squareZeroExt (differentialsModule Λ A)).snd = 0 := rfl
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_cotangentPushoutToDifferentialsTwisted, hfst, TrivSqZeroExt.fst_inl]
      · rw [snd_cotangentPushoutToDifferentialsTwisted, hsnd, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.snd_inl, map_zero, sub_zero, Derivation.map_algebraMap])

/-! ### Retractions and the base ring map of a thickening -/

/-- A ring-theoretic section of the surjection of a square-zero thickening produced by
`thickeningOverBase`, compatible with the map from the base, retracts the thickening onto
`Spec A` inside the big fppf category over `S`. -/
public def thickeningOverBaseRetraction (A' : Type u) [CommRing A'] (q : A' →+* A)
    (hq : IsDeformationSituation q) (hA' : B.Contains (Spec (.of A'))) (g : Λ →+* A')
    (hg : q.comp g = algebraMap Λ A) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS)
    (s : A →+* A') (hsg : s.comp (algebraMap Λ A) = g) :
    (Over.mk (thickeningOverBase B S hS toS hA A' q hq hA' g hg affineOpen hfact).toS' :
        BigFppfOver B S hS) ⟶ algebraOver A B S hS toS hA := by
  refine Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom s)) :
    B.obj hA' ⟶ B.obj hA) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom s) ≫ toS =
    Spec.map (CommRingCat.ofHom g) ≫ affineOpen
  have hcomp : CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom s =
      CommRingCat.ofHom g := by
    rw [← CommRingCat.ofHom_comp, hsg]
  rw [← hfact, ← Category.assoc, ← Spec.map_comp, hcomp]

/-- The retraction attached to a section of the surjection is a retraction of the closed
immersion of the thickening. -/
public theorem arrow_comp_thickeningOverBaseRetraction (A' : Type u) [CommRing A']
    (q : A' →+* A) (hq : IsDeformationSituation q) (hA' : B.Contains (Spec (.of A')))
    (g : Λ →+* A') (hg : q.comp g = algebraMap Λ A) (affineOpen : Spec (.of Λ) ⟶ S)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS)
    (s : A →+* A') (hsg : s.comp (algebraMap Λ A) = g) (hs : q.comp s = RingHom.id A) :
    (thickeningOverBase B S hS toS hA A' q hq hA' g hg affineOpen hfact).arrow ≫
        thickeningOverBaseRetraction B S hS toS hA A' q hq hA' g hg affineOpen hfact s hsg =
      𝟙 (algebraOver A B S hS toS hA) := by
  ext
  show Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom s) =
    𝟙 (Spec (.of A))
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom s ≫ CommRingCat.ofHom q = 𝟙 (CommRingCat.of A) := by
    rw [← CommRingCat.ofHom_comp, hs]
    rfl
  rw [h, Spec.map_id]

/-- The section `A ⟶ C` of the pushout algebra of a presentation, the structure map of its
trivial square-zero extension. -/
public def cotangentPushoutSection (E : Algebra.Extension.{u} Λ A) :
    A →+* cotangentPushout E :=
  TrivSqZeroExt.inlHom A _

/-- The section of the pushout algebra extends the map from the base. -/
public theorem cotangentPushoutSection_comp_algebraMap (E : Algebra.Extension.{u} Λ A) :
    (cotangentPushoutSection E).comp (algebraMap Λ A) = cotangentPushoutBaseMap E :=
  RingHom.ext fun r => (cotangentPushoutMap_algebraMap E r).symm

/-- The section of the pushout algebra is a section of its projection to `A`. -/
public theorem cotangentPushoutProj_comp_section (E : Algebra.Extension.{u} Λ A) :
    (cotangentPushoutProj E).comp (cotangentPushoutSection E) = RingHom.id A :=
  RingHom.ext fun a => TrivSqZeroExt.fst_inl A a

/-- The section `A ⟶ C` of the pushout algebra followed by the derivation-twisted surjection
onto `C̄ = A[Ω_{A/Λ}]` is the map `(1, d)` attached to the universal derivation. -/
public theorem cotangentPushoutToDifferentialsTwisted_section
    (E : Algebra.Extension.{u} Λ A) (a : A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    cotangentPushoutToDifferentialsTwisted E (cotangentPushoutSection E a) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (KaehlerDifferential.D Λ A a) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  have hfst : (cotangentPushoutSection E a).fst = a := rfl
  have hsnd : (cotangentPushoutSection E a).snd = 0 := rfl
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_cotangentPushoutToDifferentialsTwisted, hfst, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  · rw [snd_cotangentPushoutToDifferentialsTwisted, hfst, hsnd, map_zero, sub_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- The closed immersion of a square-zero thickening is surjective on points, the kernel of
the surjection being nilpotent. -/
public theorem surjective_comap_of_isDeformationSituation {A' : Type u} [CommRing A']
    (q : A' →+* A) (hq : IsDeformationSituation q) :
    Function.Surjective (PrimeSpectrum.comap q) := by
  rw [← Set.range_eq_univ, _root_.range_comap_of_surjective A q hq.1,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  refine ⟨2, ?_⟩
  have h : x ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow hx 2
  rwa [hq.2, Ideal.mem_bot] at h

/-- The morphism of spectra attached to a square-zero surjection is surjective. -/
public theorem surjective_Spec_map_of_isDeformationSituation {A' : Type u} [CommRing A']
    (q : A' →+* A) (hq : IsDeformationSituation q) :
    Surjective (Spec.map (CommRingCat.ofHom q)) :=
  ⟨surjective_comap_of_isDeformationSituation q hq⟩

/-- **Every square-zero thickening of `Spec A` over `S` lies over an affine open of the base
through a ring map.** If `Spec A ⟶ S` factors through an open immersion `Spec Λ ⟶ S`, then so
does the structure morphism of any square-zero thickening `Spec A'` of `Spec A`, by a morphism
coming from a ring map `Λ ⟶ A'` over `A`: the closed immersion `Spec A ⟶ Spec A'` is surjective
on points, so the two structure morphisms have the same image, and a morphism of affine schemes
is the spectrum of a ring map. -/
public theorem exists_baseRingHom {A' : Type u} [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') (affineOpen : Spec (.of Λ) ⟶ S)
    (hopen : IsOpenImmersion affineOpen)
    (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    ∃ f : Λ →+* A',
      Spec.map (CommRingCat.ofHom f) ≫ affineOpen = B.inclusion.map D.toS' ∧
        D.q.comp f = algebraMap Λ A := by
  have := hopen
  have := surjective_Spec_map_of_isDeformationSituation D.q D.squareZeroSurjection
  have hw : D.arrow.left ≫ D.toS' = (algebraOver A B S hS toS hA).hom := Over.w D.arrow
  have harrow : B.inclusion.map D.arrow.left ≫ B.inclusion.map D.toS' = toS := by
    rw [← Functor.map_comp, hw]
    rfl
  have harrow' : Spec.map (CommRingCat.ofHom D.q) ≫ B.inclusion.map D.toS' = toS := by
    rwa [← D.arrow_spec]
  have hrange : Set.range (B.inclusion.map D.toS') ⊆ Set.range affineOpen := by
    rw [← range_eq_range_of_surjective toS (B.inclusion.map D.toS')
      (Spec.map (CommRingCat.ofHom D.q)) harrow', ← hfact]
    simp [Set.range_comp]
  let l := IsOpenImmersion.lift affineOpen (B.inclusion.map D.toS') hrange
  have hl : l ≫ affineOpen = B.inclusion.map D.toS' :=
    IsOpenImmersion.lift_fac affineOpen (B.inclusion.map D.toS') hrange
  refine ⟨(Spec.preimage l).hom, ?_, ?_⟩
  · rwa [show CommRingCat.ofHom (Spec.preimage l).hom = Spec.preimage l from rfl,
      Spec.map_preimage]
  · have hcomp : (Spec.map (CommRingCat.ofHom D.q) ≫ l) ≫ affineOpen =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen := by
      rw [Category.assoc, hl, harrow', hfact]
    have h2 : Spec.map (CommRingCat.ofHom D.q) ≫ l =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) := (cancel_mono affineOpen).1 hcomp
    rw [show l = Spec.map (Spec.preimage l) from (Spec.map_preimage l).symm,
      ← Spec.map_comp] at h2
    exact CommRingCat.hom_ext_iff.1 (Spec.map_injective h2)

end Thickenings

end Deformation.Artin

end
