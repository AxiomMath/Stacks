module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationIso
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationKernelInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquareHomotopy
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionHomology

/-!
# The degree `-1` cohomology of the naive cotangent complex of a quotient

Let `a : A ⟶ B` be a locally surjective homomorphism of sheaves of commutative rings on a site,
with kernel `I`. The naive cotangent complex `NL_{B/A}` of the canonical presentation
`A[B] ⟶ B` has degree `-1` cohomology sheaf `I/I²`.

Indeed `a` itself is a presentation of `B` over `A`, whose conormal sequence is
`I/I² ⟶ B ⊗[A] Ω[A/A] ⟶ Ω[B/A]` with middle term zero, so the kernel of its conormal map is
`I/I²`; and the factorisation of `a` through the canonical presentation by the coefficient map
`A ⟶ A[B]` induces an isomorphism of the kernels of the two conormal maps, by Stacks 08TY in
degree `-1` (`Stacks.SheafOfModules.isIso_presentationKernelMap`) applied to the presentation
by the empty family of generators, whose free algebra is `A` itself.

## Main definitions

* `Stacks.SheafOfModules.freeAlgebraSheafEmptyIso`: the free algebra on no generators is the
  base.
* `Stacks.SheafOfModules.naiveCotangentHomologyNegOneIsoConormal`: `H^{-1}(NL_{B/A}) ≅ I/I²`.

## Main results

* `Stacks.SheafOfModules.naiveCotangentHomologyNegOneIsoConormal_inv_ι`: the isomorphism sends
  the class of a section of `I` to the class of the same section, read as a coefficient, in the
  conormal sheaf of the canonical presentation.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u w z

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The empty family of generators. -/
abbrev emptyGenerators : Cᵒᵖ ⥤ Type w := (Functor.const Cᵒᵖ).obj PEmpty.{w + 1}

/-- The empty family of generators maps to every presheaf of sets. -/
def emptyGeneratorsMap (F : Cᵒᵖ ⥤ Type w) : emptyGenerators.{v, u, w} (C := C) ⟶ F where
  app _ := TypeCat.ofHom fun x => x.elim
  naturality _ _ _ := by ext x; exact x.elim

variable [HasWeakSheafify J CommRingCat.{w}]

/-- **The free algebra on no generators is the base.** -/
noncomputable def freeAlgebraSheafEmptyIso (A : Sheaf J CommRingCat.{w}) :
    A ≅ freeAlgebraSheaf J A emptyGenerators.{v, u, w} where
  hom := freeAlgebraSheafCoefficientMap J A _
  inv := freeAlgebraSheafDesc J A A _ (𝟙 A) (emptyGeneratorsMap _)
  hom_inv_id := freeAlgebraSheafCoefficientMap_comp_desc J A A _ _ _
  inv_hom_id := freeAlgebraSheaf_hom_ext J A _ _
    (by rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_desc, Category.id_comp,
      Category.comp_id])
    (by ext _ x; exact x.elim)

variable [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The presentation of `B` by the empty family of generators is `a`, read through the
identification of the free algebra on no generators with `A`. -/
theorem presentation_emptyGenerators :
    presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _) =
      freeAlgebraSheafDesc J A A _ (𝟙 A) (emptyGeneratorsMap _) ≫ a :=
  freeAlgebraSheaf_hom_ext J A B _
    ((freeAlgebraSheafCoefficientMap_comp_desc J A B _ a _).trans
      ((Category.id_comp a).symm.trans
        ((congrArg (· ≫ a) (freeAlgebraSheafCoefficientMap_comp_desc J A A _ (𝟙 A) _)).symm.trans
          (Category.assoc _ _ _))))
    (by ext _ x; exact x.elim)

variable [Presheaf.IsLocallySurjective J a.hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- The presentation by the empty family of generators is locally surjective when `a` is. -/
instance isLocallySurjective_presentation_emptyGenerators :
    Presheaf.IsLocallySurjective J
      (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _)).hom := by
  have h : (freeAlgebraSheafCoefficientMap J A emptyGenerators.{v, u, w}).hom ≫
      (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _)).hom = a.hom :=
    hom_of_comp_eq (freeAlgebraSheafCoefficientMap_comp_desc J A B _ a _)
  have : Presheaf.IsLocallySurjective J
      ((freeAlgebraSheafCoefficientMap J A emptyGenerators.{v, u, w}).hom ≫
        (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _)).hom) := by
    rw [h]; infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J
    (freeAlgebraSheafCoefficientMap J A emptyGenerators.{v, u, w}).hom _

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **`B ⊗[A] Ω[A/A] = 0`**: the middle term of the conormal sequence of `a`, read as a
presentation of `B` over `A` itself, vanishes. -/
theorem isZero_tensorDifferentialsSheaf_self :
    IsZero (tensorDifferentialsSheaf.{v, u, w, z} J A A B (𝟙 A) a) := by
  refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext X t
  show t = 0
  induction t using TensorProduct.induction_on with
  | zero => rfl
  | tmul b ω =>
    have hω : ω = 0 :=
      @Subsingleton.elim _ (KaehlerDifferential.subsingleton_of_surjective _ _
        (fun x => ⟨x, rfl⟩)) ω 0
    rw [hω, TensorProduct.tmul_zero]
    rfl
  | add x y hx hy =>
    rw [hx, hy]
    exact add_zero _

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}] in
/-- The conormal map of `a`, read as a presentation of `B` over `A` itself, vanishes, so its
kernel is the conormal sheaf of `a`. -/
noncomputable def trivialKernelIso :
    kernel (conormalSequence.{v, u, w, z} J A A B (𝟙 A) a).f ≅
      conormalSheaf.{v, u, w, z} J A B a :=
  kernelIsoOfEq ((isZero_tensorDifferentialsSheaf_self.{v, u, w, z} J A B a).eq_of_tgt _ _) ≪≫
    kernelZeroIsoSource

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identification of the kernel with the conormal sheaf is the inclusion of the kernel. -/
theorem trivialKernelIso_hom :
    (trivialKernelIso.{v, u, w, z} J A B a).hom =
      kernel.ι (conormalSequence.{v, u, w, z} J A A B (𝟙 A) a).f :=
  kernelIsoOfEq_hom_comp_ι _

/-- The map from the kernel of the conormal map of `a` to that of the presentation by the empty
family of generators. -/
noncomputable abbrev trivialToEmptyKernelMap :=
  kernelMapOfFac.{v, u, w, z} J A B A (freeAlgebraSheaf J A emptyGenerators.{v, u, w}) (𝟙 A)
    (freeAlgebraSheafCoefficientMap J A _) a
    (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _))
    (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap_comp_desc J A B _ a _)
    (Category.id_comp _)

/-- The map from the kernel of the conormal map of the presentation by the empty family of
generators to that of the canonical presentation. -/
noncomputable abbrev emptyToCanonicalKernelMap :=
  kernelMapOfFac.{v, u, w, z} J A B (freeAlgebraSheaf J A emptyGenerators.{v, u, w})
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) (freeAlgebraSheafCoefficientMap J A _)
    (freeAlgebraSheafCoefficientMap J A _)
    (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
    (freeAlgebraMap J A _ _ (emptyGeneratorsMap _))
    (freeAlgebraMap_comp_presentation J A _ _ (emptyGeneratorsMap _) B a _ _
      (Category.comp_id _))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A _ _ _)

/-- The comparison of the kernels of the trivial and of the empty presentation is an
isomorphism. -/
instance isIso_trivialToEmptyKernelMap :
    IsIso (trivialToEmptyKernelMap.{v, u, w, z} J A B a) := by
  refine ⟨kernelMapOfFac.{v, u, w, z} J A B (freeAlgebraSheaf J A emptyGenerators.{v, u, w}) A
    (freeAlgebraSheafCoefficientMap J A _) (𝟙 A)
    (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _)) a
    (freeAlgebraSheafDesc J A A _ (𝟙 A) (emptyGeneratorsMap _))
    (presentation_emptyGenerators J A B a).symm
    (freeAlgebraSheafCoefficientMap_comp_desc J A A _ _ _), ?_, ?_⟩
  · unfold trivialToEmptyKernelMap
    rw [kernelMapOfFac_comp]
    refine (kernelMapOfFac_eq.{v, u, w, z} J A B A A (𝟙 A) (𝟙 A) a a _ (𝟙 A) _
      (Category.id_comp a) _ (Category.comp_id _)).trans (kernelMapOfFac_id J A B A (𝟙 A) a)
  · unfold trivialToEmptyKernelMap
    rw [kernelMapOfFac_comp]
    refine (kernelMapOfFac_eq.{v, u, w, z} J A B _ _ _ _ _ _ _ (𝟙 _) _
      (Category.id_comp _) _ (Category.comp_id _)).trans (kernelMapOfFac_id J A B _ _ _)

/-- The comparison of the kernels of the empty and of the canonical presentation is an
isomorphism. -/
instance isIso_emptyToCanonicalKernelMap :
    IsIso (emptyToCanonicalKernelMap.{v, u, w, z} J A B a) :=
  isIso_presentationKernelMap.{v, u, w, z} J A B a _ _ _ _ _ (Category.comp_id _)

/-- The degree `-1` cohomology sheaf of `NL_{B/A}` is the kernel of the conormal map of the
canonical presentation. -/
noncomputable def naiveCotangentHomologyNegOneIsoKernel :
    (naiveCotangentComplex.{v, u, w, z} J A B a).homology (-1) ≅
      kernel (presentationConormalSequence.{v, u, w, z} J A B a
        (underlyingPresheaf J B) (𝟙 _)).f :=
  presentationNaiveCotangentComplexHomologyNegOneIso.{v, u, w, z} J A B a
    (underlyingPresheaf J B) (𝟙 _)

/-- **`H^{-1}(NL_{B/A}) ≅ I/I²`** for a locally surjective homomorphism `a : A ⟶ B` of sheaves
of commutative rings, with `I` its kernel. -/
noncomputable def naiveCotangentHomologyNegOneIsoConormal :
    (naiveCotangentComplex.{v, u, w, z} J A B a).homology (-1) ≅
      conormalSheaf.{v, u, w, z} J A B a :=
  naiveCotangentHomologyNegOneIsoKernel.{v, u, w, z} J A B a ≪≫
    (asIso (emptyToCanonicalKernelMap.{v, u, w, z} J A B a)).symm ≪≫
    (asIso (trivialToEmptyKernelMap.{v, u, w, z} J A B a)).symm ≪≫
    trivialKernelIso.{v, u, w, z} J A B a

/-- The map of conormal sheaves induced by a factorisation only depends on the morphism `ψ`. -/
private theorem conormalSheafMapOfFac_congr {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {A B P : Sheaf J CommRingCat.{w}} (a : A ⟶ B) (φ : P ⟶ B)
    [Presheaf.IsLocallySurjective J a.hom] [Presheaf.IsLocallySurjective J φ.hom]
    {ψ ψ' : A ⟶ P} (e : ψ = ψ') (h : ψ ≫ φ = a) (h' : ψ' ≫ φ = a) :
    conormalSheafMapOfFac.{v, u, w, z} J B A P a φ ψ h =
      conormalSheafMapOfFac.{v, u, w, z} J B A P a φ ψ' h' := by
  subst e
  rfl

/-- **The class of a section of `I` goes to the class of the same section, read as a
coefficient.** The inverse of `naiveCotangentHomologyNegOneIsoConormal`, followed by the
inclusion of `H^{-1}(NL_{B/A})` in the conormal sheaf of the canonical presentation, is the
map of conormal sheaves induced by the coefficient map `A ⟶ A[B]`. -/
theorem naiveCotangentHomologyNegOneIsoConormal_inv_ι :
    (naiveCotangentHomologyNegOneIsoConormal.{v, u, w, z} J A B a).inv ≫
        (naiveCotangentHomologyNegOneIsoKernel.{v, u, w, z} J A B a).hom ≫
        kernel.ι (presentationConormalSequence.{v, u, w, z} J A B a
          (underlyingPresheaf J B) (𝟙 _)).f =
      conormalSheafMapOfFac.{v, u, w, z} J B A (freeAlgebraSheaf J A (underlyingPresheaf J B)) a
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
        (freeAlgebraSheafCoefficientMap J A _)
        (freeAlgebraSheafCoefficientMap_comp_desc J A B _ a _) := by
  simp only [naiveCotangentHomologyNegOneIsoConormal, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  have h₁ := kernelMapOfFac_comp_ι.{v, u, w, z} J A B
    (freeAlgebraSheaf J A emptyGenerators.{v, u, w})
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) (freeAlgebraSheafCoefficientMap J A _)
    (freeAlgebraSheafCoefficientMap J A _)
    (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
    (freeAlgebraMap J A _ _ (emptyGeneratorsMap _))
    (freeAlgebraMap_comp_presentation J A _ _ (emptyGeneratorsMap _) B a _ _
      (Category.comp_id _))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A _ _ _)
  have h₂ := kernelMapOfFac_comp_ι.{v, u, w, z} J A B A
    (freeAlgebraSheaf J A emptyGenerators.{v, u, w}) (𝟙 A)
    (freeAlgebraSheafCoefficientMap J A _) a
    (presentation J A B a emptyGenerators.{v, u, w} (emptyGeneratorsMap _))
    (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap_comp_desc J A B _ a _)
    (Category.id_comp _)
  refine (congrArg (fun t => (trivialKernelIso.{v, u, w, z} J A B a).inv ≫
    trivialToEmptyKernelMap.{v, u, w, z} J A B a ≫ t) h₁).trans ?_
  refine ((congrArg (fun t => (trivialKernelIso.{v, u, w, z} J A B a).inv ≫ t)
    (Category.assoc _ _ _).symm).trans ?_)
  refine (congrArg (fun t => (trivialKernelIso.{v, u, w, z} J A B a).inv ≫ t ≫ _) h₂).trans ?_
  refine (congrArg (fun t => (trivialKernelIso.{v, u, w, z} J A B a).inv ≫ t)
    (Category.assoc _ _ _)).trans ?_
  refine ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) ((congrArg (_ ≫ ·)
    (trivialKernelIso_hom.{v, u, w, z} J A B a).symm).trans
      (trivialKernelIso.{v, u, w, z} J A B a).inv_hom_id)).trans ?_
  refine (Category.id_comp _).trans ?_
  refine (conormalSheafMapOfFac_comp.{v, u, w, z} J B _ _ _ _ _ _ _ _ _ _).trans ?_
  exact conormalSheafMapOfFac_congr.{v, u, w, z} _ _
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A _ _ _) _ _

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Presheaf.IsLocallySurjective J a.hom] [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}] in
/-- The naive cotangent complex of the canonical presentation has no differential into degree
`-1`. -/
theorem naiveCotangentComplex_d_prev_negOne :
    (naiveCotangentComplex.{v, u, w, z} J A B a).d ((ComplexShape.up ℤ).prev (-1)) (-1) = 0 :=
  (naiveCotangentComplex_isZero_X.{v, u, w, z} J A B a _ (by simp) (by simp)).eq_of_src _ _

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Presheaf.IsLocallySurjective J a.hom] [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}] in
/-- The conormal sheaf of the canonical presentation is the degree `-1` term of `NL_{B/A}`. -/
theorem naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf :
    (naiveCotangentComplex.{v, u, w, z} J A B a).X (-1) =
      conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (canonicalPresentation J A B a) :=
  naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a

/-- **The class of a section of `I` goes to the class of the same section, read as a
coefficient**, stated with the inclusion of `H^{-1}(NL_{B/A})` in the conormal sheaf of the
canonical presentation. -/
theorem naiveCotangentHomologyNegOneIsoConormal_inv_homologyToX :
    (naiveCotangentHomologyNegOneIsoConormal.{v, u, w, z} J A B a).inv ≫
        (naiveCotangentComplex.{v, u, w, z} J A B a).homologyToX (-1)
          (naiveCotangentComplex_d_prev_negOne J A B a) ≫
        eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a) =
      conormalSheafMapOfFac.{v, u, w, z} J B A (freeAlgebraSheaf J A (underlyingPresheaf J B)) a
        (canonicalPresentation J A B a) (freeAlgebraSheafCoefficientMap J A _)
        (canonicalPresentation_comp_coefficientMap J A B a) := by
  have h1 := naiveCotangentHomologyNegOneIsoConormal_inv_ι.{v, u, w, z} J A B a
  have h2 := HomologicalComplex.doubleHomologyIsoKernel_hom_comp_ι
    (presentationConormalSequence.{v, u, w, z} J A B a (underlyingPresheaf J B) (𝟙 _)).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (naiveCotangentComplex_d_prev_negOne J A B a)
  have h3 : (naiveCotangentHomologyNegOneIsoConormal.{v, u, w, z} J A B a).inv ≫
      (HomologicalComplex.double
        (presentationConormalSequence.{v, u, w, z} J A B a (underlyingPresheaf J B) (𝟙 _)).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).homologyToX (-1)
          (naiveCotangentComplex_d_prev_negOne J A B a) ≫
        (HomologicalComplex.doubleXIso₀
          (presentationConormalSequence.{v, u, w, z} J A B a (underlyingPresheaf J B) (𝟙 _)).f
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      conormalSheafMapOfFac.{v, u, w, z} J B A (freeAlgebraSheaf J A (underlyingPresheaf J B)) a
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
        (freeAlgebraSheafCoefficientMap J A _)
        (freeAlgebraSheafCoefficientMap_comp_desc J A B _ a _) :=
    (congrArg ((naiveCotangentHomologyNegOneIsoConormal.{v, u, w, z} J A B a).inv ≫ ·)
      h2).symm.trans h1
  exact h3

/-- **`H^{-1}(NL_{B/A}) = I/I²` read on another presentation.** For a presentation `φ : P ⟶ B`
over `ψ : A ⟶ P` identified with the canonical one by `e : P ≅ A[B]`, the identification
`H^{-1}(NL_{B/A}) ≅ I/I²` followed by the maps of conormal sheaves along `ψ` and `e` is the
inclusion of `H^{-1}` into the degree `-1` term of `NL_{B/A}`. -/
theorem naiveCotangentHomologyNegOneIsoConormal_hom_conormalSheafMapOfFac
    (P : Sheaf J CommRingCat.{w}) (ψ : A ⟶ P) (φ : P ⟶ B) [Presheaf.IsLocallySurjective J φ.hom]
    (hψ : ψ ≫ φ = a) (e : P ≅ freeAlgebraSheaf J A (underlyingPresheaf J B))
    (he : e.hom ≫ canonicalPresentation J A B a = φ)
    (hc : ψ ≫ e.hom = freeAlgebraSheafCoefficientMap J A _) :
    (naiveCotangentHomologyNegOneIsoConormal.{v, u, w, z} J A B a).hom ≫
        conormalSheafMapOfFac.{v, u, w, z} J B A P a φ ψ hψ ≫
          (conormalSheafIsoOfFac.{v, u, w, z} J B P _ φ (canonicalPresentation J A B a) e he).hom =
      (naiveCotangentComplex.{v, u, w, z} J A B a).homologyToX (-1)
          (naiveCotangentComplex_d_prev_negOne J A B a) ≫
        eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a) := by
  refine (cancel_epi (naiveCotangentHomologyNegOneIsoConormal.{v, u, w, z} J A B a).inv).1 ?_
  rw [Iso.inv_hom_id_assoc]
  refine Eq.trans ?_ (naiveCotangentHomologyNegOneIsoConormal_inv_homologyToX J A B a).symm
  exact (conormalSheafMapOfFac_comp.{v, u, w, z} J B A P _ a φ (canonicalPresentation J A B a) ψ
    e.hom hψ he).trans (conormalSheafMapOfFac_congr.{v, u, w, z} _ _ hc _ _)

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [Presheaf.IsLocallySurjective J a.hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}] in
/-- **The comparison of Stacks 08TY in degree `-1`** is the map of conormal sheaves induced by the
morphism of presentations `A[E] ⟶ A[B]`, read in the conormal sheaf of the canonical
presentation. -/
theorem naiveCotangentComplexComparison_f_negOne (E : Cᵒᵖ ⥤ Type w)
    (α : E ⟶ underlyingPresheaf J B)
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] :
    (naiveCotangentComplexComparison.{v, u, w, z} J A B a E α).f (-1) ≫
        eqToHom (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, w, z} J A B a) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E α) ≫
        conormalSheafMapOfFac.{v, u, w, z} J B (freeAlgebraSheaf J A E)
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) (presentation J A B a E α)
          (canonicalPresentation J A B a) (freeAlgebraMap J A _ _ α)
          (freeAlgebraMap_comp_presentation J A _ _ α B a α (𝟙 _) (Category.comp_id α)) := by
  have h := presentationNaiveCotangentComplexMap_f_negOne.{v, u, w, z} J A E
    (underlyingPresheaf J B) α B a α (𝟙 _) (Category.comp_id α)
  have hcong : ∀ (φ φ' : freeAlgebraSheaf J A (underlyingPresheaf J B) ⟶ B) (e : φ = φ')
      [Presheaf.IsLocallySurjective J φ.hom] [Presheaf.IsLocallySurjective J φ'.hom]
      (hψ : freeAlgebraMap J A _ _ α ≫ φ = presentation J A B a E α)
      (hψ' : freeAlgebraMap J A _ _ α ≫ φ' = presentation J A B a E α),
      conormalSheafMapOfFac.{v, u, w, z} J B (freeAlgebraSheaf J A E) _
          (presentation J A B a E α) φ (freeAlgebraMap J A _ _ α) hψ ≫
        eqToHom (by subst e; rfl) =
      conormalSheafMapOfFac.{v, u, w, z} J B (freeAlgebraSheaf J A E) _
          (presentation J A B a E α) φ' (freeAlgebraMap J A _ _ α) hψ' := by
    intro φ φ' e _ _ hψ hψ'
    subst e
    exact Category.comp_id _
  calc (naiveCotangentComplexComparison.{v, u, w, z} J A B a E α).f (-1) ≫
        eqToHom (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, w, z} J A B a)
      = (eqToHom (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E α) ≫
          presentationConormalMap.{v, u, w, z} J A E (underlyingPresheaf J B) α B a α (𝟙 _)
            (Category.comp_id α) ≫
          eqToHom (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a
            (underlyingPresheaf J B) (𝟙 _)).symm) ≫
        eqToHom (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, w, z} J A B a) :=
        congrArg (· ≫ _) h
    _ = eqToHom (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E α) ≫
          presentationConormalMap.{v, u, w, z} J A E (underlyingPresheaf J B) α B a α (𝟙 _)
            (Category.comp_id α) ≫
          eqToHom ((presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a
            (underlyingPresheaf J B) (𝟙 _)).symm.trans
              (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, w, z} J A B a)) :=
        (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
          (congrArg _ (eqToHom_trans _ _))))
    _ = _ := congrArg _ (hcong _ _ (presentation_id J A B a) _ _)

end Stacks.SheafOfModules

namespace Stacks.Sites.Conormal

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A₀ A₁ A₂ A₃ B₁ B₂ : Sheaf J CommRingCat.{w})
  (φ₀ : A₀ ⟶ B₁) (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (φ₃ : A₃ ⟶ B₂)
  (χ₀ : A₀ ⟶ A₁) (ψ : A₁ ⟶ A₂) (χ : A₂ ⟶ A₃) (β : B₁ ⟶ B₂)
  (hχ₀ : χ₀ ≫ φ₁ = φ₀) (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hχ : χ ≫ φ₃ = φ₂)
  [Presheaf.IsLocallySurjective J φ₀.hom] [Presheaf.IsLocallySurjective J φ₁.hom]
  [Presheaf.IsLocallySurjective J φ₂.hom] [Presheaf.IsLocallySurjective J φ₃.hom]

include hχ₀ hsq in
/-- A factorisation followed by a square induces the map of the composite square. -/
theorem conormalSheafMapOfFac_comp_conormalSheafMapOfSquare :
    conormalSheafMapOfFac.{v, u, w, z} J B₁ A₀ A₁ φ₀ φ₁ χ₀ hχ₀ ≫
        conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq =
      conormalSheafMapOfSquare.{v, u, w, z} J A₀ A₂ B₁ B₂ φ₀ φ₂ (χ₀ ≫ ψ) β
        (by rw [Category.assoc, hsq, ← Category.assoc, hχ₀]) := by
  refine conormal_hom_ext.{v, u, w, z} (J := J) φ₀ _ fun X x => ?_
  show ((conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq).val.app X)
      (((conormalSheafMapOfFac.{v, u, w, z} J B₁ A₀ A₁ φ₀ φ₁ χ₀ hχ₀).val.app X)
        (conormalClass.{v, u, w, z} J A₀ A₀ B₁ (𝟙 A₀) φ₀ X x)) =
    ((conormalSheafMapOfSquare.{v, u, w, z} J A₀ A₂ B₁ B₂ φ₀ φ₂ (χ₀ ≫ ψ) β _).val.app X)
      (conormalClass.{v, u, w, z} J A₀ A₀ B₁ (𝟙 A₀) φ₀ X x)
  rw [conormalSheafMapOfFac_conormalClass.{v, u, w, z} J A₀ B₁ A₀ A₁ (𝟙 A₀) χ₀ φ₀ φ₁ χ₀ hχ₀,
    conormalSheafMapOfSquare_conormalClass.{v, u, w, z} J A₀ A₀ A₁ A₂ B₁ B₂ χ₀ (χ₀ ≫ ψ),
    conormalSheafMapOfSquare_conormalClass.{v, u, w, z} J A₀ A₀ A₀ A₂ B₁ B₂ (𝟙 A₀) (χ₀ ≫ ψ)]
  rfl

include hsq hχ in
/-- A square followed by a factorisation induces the map of the composite square. -/
theorem conormalSheafMapOfSquare_comp_map_conormalSheafMapOfFac :
    conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalSheafMapOfFac.{v, u, w, z} J B₂ A₂ A₃ φ₂ φ₃ χ hχ) =
      conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₃ B₁ B₂ φ₁ φ₃ (ψ ≫ χ) β
        (by rw [Category.assoc, hχ, hsq]) := by
  refine conormal_hom_ext.{v, u, w, z} (J := J) φ₁ _ fun X x => ?_
  show ((conormalSheafMapOfFac.{v, u, w, z} J B₂ A₂ A₃ φ₂ φ₃ χ hχ).val.app X)
      (((conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq).val.app X)
        (conormalClass.{v, u, w, z} J A₁ A₁ B₁ (𝟙 A₁) φ₁ X x)) =
    ((conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₃ B₁ B₂ φ₁ φ₃ (ψ ≫ χ) β _).val.app X)
      (conormalClass.{v, u, w, z} J A₁ A₁ B₁ (𝟙 A₁) φ₁ X x)
  rw [conormalSheafMapOfSquare_conormalClass.{v, u, w, z} J A₁ A₁ A₁ A₂ B₁ B₂ (𝟙 A₁) ψ,
    conormalSheafMapOfFac_conormalClass.{v, u, w, z} J A₁ B₂ A₂ A₃ ψ (ψ ≫ χ) φ₂ φ₃ χ hχ,
    conormalSheafMapOfSquare_conormalClass.{v, u, w, z} J A₁ A₁ A₁ A₃ B₁ B₂ (𝟙 A₁) (ψ ≫ χ)]
  rfl

variable (R₁ R₂ : Sheaf J CommRingCat.{w}) (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (ρ : R₁ ⟶ R₂)
  (ψ' : A₁ ⟶ A₂) (hsq' : ψ' ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ ≫ a₂ = a₁ ≫ ψ')

include hsq hsq' ha ha' in
/-- **On sections killed by the conormal map, the map of conormal sheaves attached to a square
does not depend on the morphism of presentations**, as long as it is fixed on the base: two such
maps differ by a homotopy precomposed with the conormal map (Stacks 00S1 (2)). -/
theorem comp_conormalSheafMapOfSquare_eq {P : _root_.SheafOfModules.{max w u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf B₁)}
    (x : P ⟶ conormalSheaf.{v, u, w, z} J A₁ B₁ φ₁)
    (hx : x ≫ (conormalSequence.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁).f = 0) :
    x ≫ conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq =
      x ≫ conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ' β hsq' := by
  rw [conormalSheafMapOfSquare_eq_add.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ ψ' β ρ
    hsq hsq' ha ha', Preadditive.comp_add]
  refine Eq.trans (congrArg (· + _) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hx).trans zero_comp))) (zero_add _)

end Stacks.Sites.Conormal

/-! ### First Ext classes of `NL` on `H^{-1}` -/

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max w u v}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  (A B : Sheaf J CommRingCat.{max w u v}) (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]
  (E : Cᵒᵖ ⥤ Type (max w u v)) (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{max w u v} (Tensor.ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v} (Tensor.ringSheaf B))

/-- A section of the kernel of `a`, read through a factorisation `ψ ≫ φ = a`, lies in the kernel
of `φ`. -/
private theorem coeff_mem_kernelIdeal_of_comp_eq {J : GrothendieckTopology C}
    {A B P : Sheaf J CommRingCat.{w}} (a : A ⟶ B) (ψ : A ⟶ P) (φ : P ⟶ B) (h : ψ ≫ φ = a)
    (U : Cᵒᵖ) (r : kernelIdeal a.hom U) : ψ.hom.app U r ∈ kernelIdeal φ.hom U := by
  change (ψ ≫ φ).hom.app U r = 0
  rw [h]
  exact r.2

omit [J.WEqualsLocallyBijective CommRingCat.{max w u v}] [Presheaf.IsLocallySurjective J a.hom]
  [HasSheafify J AddCommGrpCat.{max w u v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})] in
/-- A section of the kernel of `a`, read as a coefficient of the canonical presentation, lies in
its kernel. -/
theorem coeff_mem_kernelIdeal_canonicalPresentation (U : Cᵒᵖ) (r : kernelIdeal a.hom U) :
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom.app U r ∈
      kernelIdeal (canonicalPresentation J A B a).hom U :=
  coeff_mem_kernelIdeal_of_comp_eq a _ _ (canonicalPresentation_comp_coefficientMap J A B a) U r

omit [J.WEqualsLocallyBijective CommRingCat.{max w u v}] [Presheaf.IsLocallySurjective J a.hom]
  [HasSheafify J AddCommGrpCat.{max w u v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] in
/-- A section of the kernel of `a`, read as a coefficient of the presentation by `E`, lies in the
kernel of the presentation. -/
theorem coeff_mem_kernelIdeal_presentation (U : Cᵒᵖ) (r : kernelIdeal a.hom U) :
    (freeAlgebraSheafCoefficientMap J A E).hom.app U r ∈
      kernelIdeal (presentation J A B a E α).hom U :=
  coeff_mem_kernelIdeal_of_comp_eq a _ _ (freeAlgebraSheafCoefficientMap_comp_desc J A B E a α) U r

omit [J.WEqualsLocallyBijective CommRingCat.{max w u v}] [Presheaf.IsLocallySurjective J a.hom] in
/-- **The map on `H^{-1}` of a first Ext class of `NL_{B/A}` given by a conormal functional.**
If `ζ`, read on a presentation by `E`, is the class of `δ : I_E/I_E² ⟶ G`, then the map `ζ`
induces on `H^{-1}(NL_{B/A})` sends a section whose image in the conormal sheaf of the canonical
presentation is the class of a section `r` of the kernel of `a`, read as a coefficient, to `δ` of
the class of `r` read as a coefficient of the presentation by `E`, followed by the automorphism
`negOneHomologySingleIso` of `G`. -/
theorem negOneHomologyMap_app_eq_of_homologyToX
    (ζ : DerivedCategory.Q.obj (naiveCotangentComplex.{v, u, max w u v, w} J A B a) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧)
    (δ : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).X₁ ⟶ G)
    (hζ : DerivedCategory.Q.map
        (naiveCotangentComplexComparison.{v, u, max w u v, w} J A B a E α) ≫ ζ =
      presentationConormalExtClass.{v, u, w, t} J A B a E α G δ)
    (U : Cᵒᵖ) (r : kernelIdeal a.hom U)
    (y : ((naiveCotangentComplex.{v, u, max w u v, w} J A B a).homology (-1)).val.obj U)
    (hy : ((naiveCotangentComplex.{v, u, max w u v, w} J A B a).homologyToX (-1)
        (naiveCotangentComplex_d_prev_negOne J A B a) ≫
          eqToHom (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, max w u v, w}
            J A B a)).val.app U y =
      conormalClass.{v, u, max w u v, w} J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A _) (canonicalPresentation J A B a) U
        ⟨_, coeff_mem_kernelIdeal_canonicalPresentation J A B a U r⟩) :
    (DerivedCategory.negOneHomologyMap _ G ζ).val.app U y =
      (DerivedCategory.negOneHomologySingleIso G
          (((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
            (by decide)).inv.app G)).hom.val.app U
        (δ.val.app U (conormalClass.{v, u, max w u v, w} J A (freeAlgebraSheaf J A E) B
          (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) U
          ⟨_, coeff_mem_kernelIdeal_presentation J A B a E α U r⟩)) := by
  set s := conormalClass.{v, u, max w u v, w} J A (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) U
    ⟨_, coeff_mem_kernelIdeal_presentation J A B a E α U r⟩ with hs_def
  have hX := presentationNaiveCotangentComplex_X_negOne.{v, u, max w u v, w} J A B a E α
  have hdE : (presentationNaiveCotangentComplex.{v, u, max w u v, w} J A B a E α).d
      ((ComplexShape.up ℤ).prev (-1)) (-1) = 0 :=
    (presentationNaiveCotangentComplex_isZero_X.{v, u, max w u v, w} J A B a E α _ (by simp)
      (by simp)).eq_of_src _ _
  -- the class of a coefficient is a cycle
  have hcyc : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f.val.app U s =
      0 := by
    rw [hs_def, conormalSequence_f_class]
    show toAssociatedModule.{v, u, max w u v, w} J (freeAlgebraSheaf J A E) B
      (presentation J A B a E α) (tensorPresheaf (presentation J A B a E α).hom
        (freeAlgebraSheafCoefficientMap J A E).hom) U
      ((1 : _) ⊗ₜ CommRingCat.KaehlerDifferential.d
        (f := (freeAlgebraSheafCoefficientMap J A E).hom.app U)
        ((freeAlgebraSheafCoefficientMap J A E).hom.app U r)) = 0
    rw [CommRingCat.KaehlerDifferential.d, ModuleCat.Derivation.d_map]
    exact (congrArg _ (TensorProduct.tmul_zero _ _)).trans (map_zero _)
  have hd : (presentationNaiveCotangentComplex.{v, u, max w u v, w} J A B a E α).d (-1) 0 =
      eqToHom hX ≫ (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f ≫
        eqToHom (presentationNaiveCotangentComplex_X_zero.{v, u, max w u v, w} J A B a E α).symm :=
    HomologicalComplex.double_d (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
  have hn : (ComplexShape.up ℤ).next (-1) = 0 := by simp
  have h0 := presentationNaiveCotangentComplex_X_zero.{v, u, max w u v, w} J A B a E α
  obtain ⟨e, he⟩ := HomologicalComplex.exists_homologyToX_app_eq
    (presentationNaiveCotangentComplex.{v, u, max w u v, w} J A B a E α) (-1) hdE U
    ((eqToHom hX.symm).val.app U s) (by
      rw [hn]
      show (eqToHom hX.symm ≫
        (presentationNaiveCotangentComplex.{v, u, max w u v, w} J A B a E α).d (-1) 0).val.app
          U s = 0
      rw [hd, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact (congrArg (fun t => (eqToHom h0.symm).val.app U t) hcyc).trans (map_zero _))
  have h3 : ((presentationNaiveCotangentComplex.{v, u, max w u v, w} J A B a E α).homologyToX
      (-1) hdE ≫ eqToHom hX).val.app U e = s := by
    show (eqToHom hX).val.app U (((presentationNaiveCotangentComplex.{v, u, max w u v, w}
      J A B a E α).homologyToX (-1) hdE).val.app U e) = s
    rw [he]
    show (eqToHom hX.symm ≫ eqToHom hX).val.app U s = s
    rw [eqToHom_trans, eqToHom_refl]
    rfl
  have hdC := naiveCotangentComplex_d_prev_negOne.{v, u, max w u v, w} J A B a
  have hinj := _root_.SheafOfModules.injective_app_of_mono
    ((naiveCotangentComplex.{v, u, max w u v, w} J A B a).homologyToX (-1) hdC ≫
      eqToHom (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, max w u v, w}
        J A B a)) U
  have hH : (HomologicalComplex.homologyMap
      (naiveCotangentComplexComparison.{v, u, max w u v, w} J A B a E α) (-1)).val.app U e =
      y := by
    refine hinj ?_
    have h1 := HomologicalComplex.homologyMap_homologyToX_assoc (-1)
      (naiveCotangentComplexComparison.{v, u, max w u v, w} J A B a E α) hdE hdC
      (eqToHom
        (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{v, u, max w u v, w} J A B a))
    rw [naiveCotangentComplexComparison_f_negOne] at h1
    refine (congrArg (fun m => m.val.app U e) h1).trans (Eq.trans ?_ hy.symm)
    refine (congrArg ((conormalSheafMapOfFac.{v, u, max w u v, w} J B (freeAlgebraSheaf J A E)
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) (presentation J A B a E α)
      (canonicalPresentation J A B a) (freeAlgebraMap J A _ _ α)
      (freeAlgebraMap_comp_presentation J A _ _ α B a α (𝟙 _) (Category.comp_id α))).val.app U)
        h3).trans ?_
    refine (conormalSheafMapOfFac_conormalClass.{v, u, max w u v, w} J A B
      (freeAlgebraSheaf J A E) (freeAlgebraSheaf J A (underlyingPresheaf J B))
      (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafCoefficientMap J A _)
      (presentation J A B a E α) (canonicalPresentation J A B a) (freeAlgebraMap J A _ _ α)
      (freeAlgebraMap_comp_presentation J A _ _ α B a α (𝟙 _) (Category.comp_id α)) U
      ⟨_, coeff_mem_kernelIdeal_presentation J A B a E α U r⟩).trans ?_
    exact congrArg _ (Subtype.ext (congrArg (fun m => m.hom.app U (r : A.obj.obj U))
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E _ α)))
  have hneg : HomologicalComplex.homologyMap
      (naiveCotangentComplexComparison.{v, u, max w u v, w} J A B a E α) (-1) ≫
        DerivedCategory.negOneHomologyMap _ G ζ =
      (presentationNaiveCotangentComplex.{v, u, max w u v, w} J A B a E α).homologyToX
        (-1) hdE ≫ (eqToHom hX ≫ δ) ≫
        (DerivedCategory.negOneHomologySingleIso G
          (((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
            (by decide)).inv.app G)).hom := by
    rw [← DerivedCategory.negOneHomologyMap_Q_map_comp, hζ, presentationConormalExtClass,
      DerivedCategory.negOneHomologyMap_Q_map_comp_single _ _ _ hdE,
      HomologicalComplex.mkHomToSingle_f, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      Category.assoc]
  have step3 := congrArg (fun m => m.val.app U e) hneg
  have step4 : (DerivedCategory.negOneHomologyMap _ G ζ).val.app U
      ((HomologicalComplex.homologyMap
        (naiveCotangentComplexComparison.{v, u, max w u v, w} J A B a E α) (-1)).val.app U e) =
      (HomologicalComplex.homologyMap
        (naiveCotangentComplexComparison.{v, u, max w u v, w} J A B a E α) (-1) ≫
          DerivedCategory.negOneHomologyMap _ G ζ).val.app U e := rfl
  rw [← hH, step4]
  refine step3.trans ?_
  rw [← h3]
  rfl

end Stacks.SheafOfModules

end
