module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.Length.Comparison

/-!
# The torsion in the first cohomology of the structure sheaf

Let `X` be a scheme over `Spec A` and let `a ∈ A`. Multiplication by `a` is an endomorphism of
`𝒪_X`, and for a short exact sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X ⟶ 𝒞 ⟶ 0` whose first map is that
multiplication there is a connecting map `Γ(X, 𝒞) ⟶ H¹(X, 𝒪_X)` whose kernel is the image of
`Γ(X, 𝒪_X)` and whose image is the `a`-torsion of `H¹(X, 𝒪_X)`. Hence the `a`-torsion of
`H¹(X, 𝒪_X)` and the cokernel of `Γ(X, 𝒪_X) ⟶ Γ(X, 𝒞)` have the same length.

## Main definitions

* `Stacks.Cohomology.endComplex` is the degreewise action of an endomorphism of the identity
  functor on a homological complex.
* `AlgebraicGeometry.globalSectionsAsBaseModule` is `Γ(X, ℱ)` regarded as a module over the base
  ring of a morphism `X ⟶ Spec A`, matching `AlgebraicGeometry.firstCohomologyAsBaseModule`.
* `AlgebraicGeometry.baseSmulModules` is multiplication by an element of the base ring, as an
  endomorphism of a sheaf of modules on `X`.

## Main results

* `AlgebraicGeometry.Scheme.rightDerived_sectionsFunctor_map_smulEnd`: the right derived functors
  of `Γ(X, -)` send multiplication by a global function to multiplication by that function. This
  is what makes the connecting map of the sequence above land in the torsion.
* `AlgebraicGeometry.exists_connecting_firstCohomology`: the connecting map, with its kernel and
  its image identified.
* `AlgebraicGeometry.length_torsionBy_firstCohomology_eq`: the `a`-torsion of `H¹(X, 𝒪_X)` and the
  cokernel of `Γ(X, 𝒪_X) ⟶ Γ(X, 𝒞)` have equal length.

## Implementation notes

Multiplication by a global function on every sheaf of modules at once is
`Stacks.SheafOfModules.terminalSectionToEnd`, for the terminal open `⊤`. Its interaction with the
derived functors of `Γ(X, -)` is computed by lifting it to an injective resolution, where it is
again multiplication by that function, degree by degree.

The long exact cohomology sequence is the one in the object variable,
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`. Its connecting morphism
depends on a resolution of the short exact sequence, so the statements here are existential in
the connecting map. The identification of `R⁰Γ(X, -)` with `Γ(X, -)` is
`CategoryTheory.Functor.toRightDerivedZero`, invertible because `Γ(X, -)` is left exact.

The scalar is taken in `X.ringCatSheaf.obj.obj (op ⊤)` rather than in the notationally identical
`Γ(X, ⊤)`: the two have the same elements, but the linear structure on `ModuleCat` is found by
unification on the first spelling only.

## References

* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- An endomorphism of the identity functor acts on a homological complex degree by degree. -/
def endComplex (τ : End (𝟭 C)) (K : HomologicalComplex C c) : End K :=
  .of
    { f n := τ.asHom.app (K.X n)
      comm' i j _ := (τ.asHom.naturality (K.d i j)).symm }

/-- The component in degree `n` of `endComplex τ K` is `τ` at `K.X n`. -/
@[simp] lemma endComplex_f (τ : End (𝟭 C)) (K : HomologicalComplex C c) (n : ι) :
    HomologicalComplex.Hom.f (endComplex τ K).asHom n = τ.asHom.app (K.X n) := rfl

end Stacks.Cohomology

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The ring of sections of the structure sheaf of `X` over `U` is commutative. -/
local instance commRingRingCatSheafObj (U : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- The ring of global functions of `X`, in the spelling used by its sheaf of rings. -/
abbrev sectionsRing : Type u := X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))

variable (b : sectionsRing X)

/-- Multiplication by a global function of `X` on every sheaf of modules at once. -/
abbrev smulEnd : End (𝟭 (SheafOfModules.{u} X.ringCatSheaf)) :=
  Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop b

/-- Multiplication by `b` on an injective resolution of `M` lifts multiplication by `b` on `M`
along the augmentation `P.ι`. -/
lemma ι_comp_endComplex {M : SheafOfModules.{u} X.ringCatSheaf} (P : InjectiveResolution M) :
    P.ι ≫ (Stacks.Cohomology.endComplex (smulEnd X b) P.cocomplex).asHom
      = (CochainComplex.single₀ _).map ((smulEnd X b).asHom.app M) ≫ P.ι := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  simp only [CochainComplex.fromSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
    Stacks.Cohomology.endComplex_f, CochainComplex.single₀_map_f_zero]
  exact (smulEnd X b).asHom.naturality (P.ι.f 0)

/-- Global sections of a sheaf of modules on `X`. -/
abbrev sectionsFunctor : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} (sectionsRing X) :=
  SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))

/-- The global sections functor is additive. -/
instance : (sectionsFunctor X).Additive := {}

/-- Global sections send multiplication by `b` on `N` to multiplication by `b` on `Γ(X, N)`. -/
lemma sectionsFunctor_map_smulEnd (N : SheafOfModules.{u} X.ringCatSheaf) :
    (sectionsFunctor X).map ((smulEnd X b).asHom.app N) = b • 𝟙 ((sectionsFunctor X).obj N) := by
  ext x
  change X.ringCatSheaf.obj.map (isTerminalTop.from (⊤ : X.Opens)).op b • x = _
  rw [show isTerminalTop.from (⊤ : X.Opens) = 𝟙 _ by subsingleton]
  simp only [op_id, X.ringCatSheaf.obj.map_id]
  rfl

/-- Applying global sections degreewise to multiplication by `b` on a cochain complex of sheaves
of modules gives multiplication by `b` on the resulting complex of modules. -/
lemma mapHomologicalComplex_map_endComplex
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℕ) :
    ((sectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Stacks.Cohomology.endComplex (smulEnd X b) K).asHom
      = b • 𝟙 (((sectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  HomologicalComplex.hom_ext _ _ fun _ => sectionsFunctor_map_smulEnd X b _

/-- **The derived functors of global sections send multiplication by a global function to
multiplication by that function.** -/
lemma rightDerived_sectionsFunctor_map_smulEnd (n : ℕ)
    (M : SheafOfModules.{u} X.ringCatSheaf) :
    ((sectionsFunctor X).rightDerived n).map ((smulEnd X b).asHom.app M)
      = b • 𝟙 ((((sectionsFunctor X).rightDerived n)).obj M) := by
  let P : InjectiveResolution M := injectiveResolution M
  rw [Functor.rightDerived_map_eq (sectionsFunctor X) n ((smulEnd X b).asHom.app M)
      (P := P) (Q := P) (Stacks.Cohomology.endComplex (smulEnd X b) P.cocomplex).asHom
      (ι_comp_endComplex X b P)]
  dsimp only [Functor.comp_map]
  rw [mapHomologicalComplex_map_endComplex, Functor.map_smul, CategoryTheory.Functor.map_id,
    Linear.smul_comp, Linear.comp_smul]
  congr 1
  rw [Category.id_comp]
  exact Iso.hom_inv_id _

/-- The element-level form of `rightDerived_sectionsFunctor_map_smulEnd`, which does not mention
the scalar action on morphisms. -/
lemma rightDerived_sectionsFunctor_map_smulEnd_apply (n : ℕ)
    (M : SheafOfModules.{u} X.ringCatSheaf)
    (x : ((sectionsFunctor X).rightDerived n).obj M) :
    (((sectionsFunctor X).rightDerived n).map ((smulEnd X b).asHom.app M)).hom x = b • x := by
  rw [rightDerived_sectionsFunctor_map_smulEnd]
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

attribute [local instance] Scheme.commRingRingCatSheafObj HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- The global sections of a sheaf of modules on `X`, regarded as a module over the base ring of
a morphism `X ⟶ Spec A`. -/
def globalSectionsAsBaseModule (F : SheafOfModules.{u} X.ringCatSheaf) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
    ((Scheme.sectionsFunctor X).obj F)

/-- The map on global sections induced by a morphism of sheaves of modules, as a map of modules
over the base ring. -/
def globalSectionsMapAsBaseModule {F G : SheafOfModules.{u} X.ringCatSheaf} (π : F ⟶ G) :
    globalSectionsAsBaseModule X f F ⟶ globalSectionsAsBaseModule X f G :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
    ((Scheme.sectionsFunctor X).map π)

/-- The image of an element of the base ring in the global functions of `X`. -/
def baseSection (a : A) : Scheme.sectionsRing X :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a

/-- Multiplication by an element of the base ring, as an endomorphism of a sheaf of modules on
`X`. -/
def baseSmulModules (a : A) (M : SheafOfModules.{u} X.ringCatSheaf) : M ⟶ M :=
  (Scheme.smulEnd X (baseSection X f a)).asHom.app M

/-- An element of `H¹(X, 𝒪_X)` is `a`-torsion iff `R¹Γ` of multiplication by `a` kills it. -/
lemma mem_torsionBy_firstCohomologyAsBaseModule_iff (a : A)
    (y : firstCohomologyAsBaseModule X f) :
    y ∈ Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a ↔
      (((Scheme.sectionsFunctor X).rightDerived 1).map
        (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))).hom y = 0 := by
  rw [Submodule.mem_torsionBy_iff, baseSmulModules,
    Scheme.rightDerived_sectionsFunctor_map_smulEnd]
  exact Iff.rfl

/-- **The connecting map of a short exact sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X ⟶ 𝒞 ⟶ 0` whose first map is
multiplication by `a` has the image of `Γ(X, 𝒪_X)` as its kernel and the `a`-torsion of
`H¹(X, 𝒪_X)` as its image.** -/
theorem exists_connecting_firstCohomology (a : A)
    (C : SheafOfModules.{u} X.ringCatSheaf) (π : SheafOfModules.unit X.ringCatSheaf ⟶ C)
    (hz : baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf) ≫ π = 0)
    (hS : (ShortComplex.mk (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))
      π hz).ShortExact) :
    ∃ δ : globalSectionsAsBaseModule X f C →ₗ[A] firstCohomologyAsBaseModule X f,
      LinearMap.ker δ = LinearMap.range (globalSectionsMapAsBaseModule X f π).hom ∧
      LinearMap.range δ = Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.sectionsFunctor X)
  let δ' : ((Scheme.sectionsFunctor X).rightDerived 0).obj C ⟶
      ((Scheme.sectionsFunctor X).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf) :=
    D.δ hS 0
  let u : Scheme.sectionsFunctor X ⟶ (Scheme.sectionsFunctor X).rightDerived 0 :=
    (Scheme.sectionsFunctor X).toRightDerivedZero
  have e1 : LinearMap.range (((Scheme.sectionsFunctor X).rightDerived 0).map π).hom
      = LinearMap.ker δ'.hom := (D.exact_δ₁ hS 0).moduleCat_range_eq_ker
  have e2 : LinearMap.range δ'.hom
      = LinearMap.ker (((Scheme.sectionsFunctor X).rightDerived 1).map
        (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))).hom :=
    (D.exact_δ₂ hS 0).moduleCat_range_eq_ker
  have hbijC : Function.Bijective (u.app C).hom :=
    ConcreteCategory.bijective_of_isIso (u.app C)
  have hnat : ∀ z, (((Scheme.sectionsFunctor X).rightDerived 0).map π).hom
      ((u.app (SheafOfModules.unit X.ringCatSheaf)).hom z)
        = (u.app C).hom (((Scheme.sectionsFunctor X).map π).hom z) :=
    fun _ => by simp
  refine ⟨((ModuleCat.restrictScalars _).map (u.app C ≫ δ')).hom, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := e1.ge hx
      obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (u.app _)).2 y
      exact ⟨z, hbijC.1 ((hnat z).symm.trans hy)⟩
    · rintro ⟨z, rfl⟩
      change δ'.hom ((u.app C).hom (((Scheme.sectionsFunctor X).map π).hom z)) = 0
      rw [← hnat z]
      exact e1.le ⟨_, rfl⟩
  · ext y
    rw [mem_torsionBy_firstCohomologyAsBaseModule_iff X f a y]
    constructor
    · rintro ⟨x, rfl⟩
      exact e2.le ⟨(u.app C).hom x, rfl⟩
    · intro hy
      obtain ⟨w, rfl⟩ := e2.ge hy
      obtain ⟨x, rfl⟩ := hbijC.2 w
      exact ⟨x, rfl⟩

/-- The `a`-torsion of `H¹(X, 𝒪_X)` and the cokernel of `Γ(X, 𝒪_X) ⟶ Γ(X, 𝒞)` have the same
length, for a short exact sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X ⟶ 𝒞 ⟶ 0` whose first map is multiplication
by `a`. -/
theorem length_torsionBy_firstCohomology_eq (a : A)
    (C : SheafOfModules.{u} X.ringCatSheaf) (π : SheafOfModules.unit X.ringCatSheaf ⟶ C)
    (hz : baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf) ≫ π = 0)
    (hS : (ShortComplex.mk (baseSmulModules X f a (SheafOfModules.unit X.ringCatSheaf))
      π hz).ShortExact) :
    Module.length A (Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a)
      = Module.length A (globalSectionsAsBaseModule X f C ⧸
          LinearMap.range (globalSectionsMapAsBaseModule X f π).hom) := by
  obtain ⟨δ, hker, hrange⟩ := exists_connecting_firstCohomology X f a C π hz hS
  rw [← hrange, ← hker]
  exact δ.quotKerEquivRange.length_eq.symm

end AlgebraicGeometry

end
