module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticGlobalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInjectiveChaoticRestriction
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimit
public import StacksFrontier.RingTheory.Koszul.LiftedSheafAlgebras

/-!
# The derived global sections on `ℕ` are a derived limit

Let `R` be a commutative ring, let `O` be the constant sheaf of rings with value `R` on the
natural numbers with the chaotic topology (in the universe of `R`, `Stacks.LiftedNat`), and let
`ℬ` be a sheaf of differential graded `O`-algebras. For an object `M` of `D(ℬ, d)` the derived
global sections `RΓ(M)` are the derived limit `R lim RΓ(n, M)` of the derived sections over the
stages, read as complexes of `R`-modules.

The argument is the one of Remark 0H1E. Represent `M` by a graded injective K-injective module
`I`. Then `RΓ(M)` is the complex `Γ(I) = lim_n I(n)`, where `I(n)` is the complex of sections of
`I` over the stage `n`. The restriction maps `I(n + 1) ⟶ I(n)` are surjective in every degree,
because `I` is injective as a graded module (`SheafOfModules.surjective_map_of_injective`), so
`0 ⟶ lim I(n) ⟶ ∏ I(n) ⟶ ∏ I(n) ⟶ 0` with middle map `1 - shift` is a degreewise short exact
sequence of complexes, which gives the defining triangle of the derived limit in `D(R)`
(`DerivedCategory.isDerivedLimit_of_limit_cone_of_epi`).

## Main definitions

* `Stacks.LiftedNat.equivalence`: the order isomorphism `ℕ ≃ LiftedNat`, as an equivalence of
  categories.
* `Stacks.ChaoticSite.limitConeAsFunctor`: for a complex `K` of functors `J ⥤ V`, the complex
  `lim K` with its projections, a limit cone of the functor `J ⥤ HomologicalComplex V c` that `K`
  is.
* `Stacks.ChaoticSite.sectionsTower`: the tower `n ↦ K(n)` of complexes of `R`-modules of
  sections of a complex `K` of sheaves of `O`-modules over the stages `n : ℕ`, and
  `Stacks.ChaoticSite.sectionsTowerCone` its limit cone, with point the complex of global
  sections.

## Main results

* `Stacks.ChaoticSite.surjective_sections_map_of_isDGInjective`: the restriction maps of the
  sections of a graded injective K-injective module are surjective, in every degree.
* `Stacks.ChaoticSite.isDerivedLimit_derivedGlobalSections_of_isDGInjective`: **at a graded
  injective K-injective module `I` the derived global sections are a derived limit of the tower
  of complexes of sections of `I`.**
* `Stacks.ChaoticSite.exists_isDerivedLimit_derivedGlobalSections`: the same for an arbitrary
  object of `D(ℬ, d)`, with the tower of a graded injective K-injective representative.

## Implementation notes

The tower is indexed by `ℕ`, as `CategoryTheory.Pretriangulated.IsDerivedLimit` requires, and is
the restriction along `Stacks.LiftedNat.ofNat` of the presheaf of complexes of sections; since
`ofNat` is an equivalence, the limit cone of the latter restricts to a limit cone of the former.
For a graded injective K-injective `I` the stage-`n` term of the tower is the complex of sections
of `I` over `n`, which computes `RΓ(n, I)`, read over `R`.

No flatness of `ℬ` over `O` is used: surjectivity of the restriction maps is deduced from graded
injectivity alone, by extending homomorphisms along the inclusion of the truncated free graded
module on one generator over `n` into the one over `n + 1`.

## References

* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Stacks.PresheafOfModules

universe u

namespace Stacks.LiftedNat

/-- The order isomorphism between `ℕ` and `LiftedNat`, as an equivalence of categories. -/
def equivalence : ℕ ≌ LiftedNat.{u} :=
  CategoryTheory.Equivalence.mk ofNat toNat (NatIso.ofComponents (fun _ => Iso.refl _))
    (NatIso.ofComponents (fun _ => Iso.refl _))

/-- The functor of the equivalence is `ofNat`. -/
@[simp] theorem equivalence_functor : equivalence.{u}.functor = ofNat := rfl

end Stacks.LiftedNat

namespace Stacks.ChaoticSite

/-! ### Surjectivity of the restriction maps -/

section Surjective

variable {C : Type u} [Preorder C] {R : Type u} [CommRing R]
  {ℬ : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R)}

/-- The restriction maps of the sections of a graded injective right differential graded
`ℬ`-module are surjective, in every degree. -/
theorem surjective_sections_map_of_gradedInjective
    {I : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} ℬ}
    (hI : _root_.SheafOfModules.DifferentialGradedModule.GradedInjective I) (k : ℤ) {n n' : C}
    (h : n ≤ n') :
    Function.Surjective (((sectionsFunctor R).obj (I.complex.X k)).map (homOfLE h).op) :=
  _root_.SheafOfModules.DifferentialGradedModule.surjective_map_of_gradedInjective hI h k

/-- **The restriction maps of the sections of a graded injective K-injective right differential
graded `ℬ`-module are surjective**, in every degree. -/
theorem surjective_sections_map_of_isDGInjective
    {I : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} ℬ}
    (hI : _root_.SheafOfModules.DifferentialGradedModule.IsDGInjective I) (k : ℤ) {n n' : C}
    (h : n ≤ n') :
    Function.Surjective (((sectionsFunctor R).obj (I.complex.X k)).map (homOfLE h).op) :=
  surjective_sections_map_of_gradedInjective hI.1 k h

end Surjective

/-! ### The limit of a complex of functors -/

section LimitCone

variable {J : Type*} [Category J] {V : Type*} [Category V] [Preadditive V] [HasLimitsOfShape J V]
  {ι : Type*} {c : ComplexShape ι}

/-- For a complex `K` of functors `J ⥤ V`, the complex `lim K` with its projections, as a cone of
the functor `J ⥤ HomologicalComplex V c` that `K` is. -/
def limitConeAsFunctor (K : HomologicalComplex (J ⥤ V) c) : Cone K.asFunctor where
  pt := (lim.mapHomologicalComplex c).obj K
  π :=
    { app j :=
        { f i := limit.π (K.X i) j
          comm' i i' _ := (limMap_π (K.d i i') j).symm }
      naturality j j' g := by
        ext i
        exact (Category.id_comp _).trans (limit.w (K.X i) g).symm }

/-- The complex `lim K` is a limit of the functor `J ⥤ HomologicalComplex V c` that `K` is: limits
of complexes are computed degreewise. -/
def isLimitLimitConeAsFunctor (K : HomologicalComplex (J ⥤ V) c) :
    IsLimit (limitConeAsFunctor K) :=
  HomologicalComplex.isLimitOfEval _ _ fun i => limit.isLimit (K.X i)

end LimitCone

/-! ### The derived limit -/

section DerivedLimit

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule Pretriangulated

/-- Being a derived limit is invariant under isomorphism of the limit object. -/
theorem isDerivedLimit_of_iso {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K K' : D} (e : K ≅ K')
    (h : IsDerivedLimit F K) : IsDerivedLimit F K' := by
  obtain ⟨p, δ, hT⟩ := h
  refine ⟨e.inv ≫ p, δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_)⟩
  simp [← Functor.map_comp]

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The tower `n ↦ K(n)` of complexes of `R`-modules of sections of a complex `K` of sheaves of
modules over the stages `n : ℕ`, with the restriction maps as transition maps. -/
def sectionsTower
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  LiftedNat.ofNat.op ⋙ (((sectionsFunctor R).mapHomologicalComplex _).obj K).asFunctor

/-- The stage-`n` term of the tower is the complex of sections over `n`. -/
theorem sectionsTower_obj_X
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ)
    (n : ℕ) (k : ℤ) :
    ((sectionsTower R K).obj (op n)).X k =
      ((sectionsFunctor R).obj (K.X k)).obj (op (LiftedNat.up n)) := rfl

/-- The transition maps of the tower are the restriction maps of the sections. -/
theorem sectionsTower_map_f
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ)
    {n n' : ℕ} (g : op n' ⟶ op n) (k : ℤ) :
    ((sectionsTower R K).map g).f k =
      ((sectionsFunctor R).obj (K.X k)).map (LiftedNat.ofNat.op.map g) := rfl

/-- The limit cone of the tower of complexes of sections: its point is the complex of global
sections. -/
def sectionsTowerCone
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ) :
    Cone (sectionsTower R K) :=
  (limitConeAsFunctor (((sectionsFunctor R).mapHomologicalComplex _).obj K)).whisker
    LiftedNat.ofNat.op

/-- The point of the limit cone is the complex of global sections. -/
theorem sectionsTowerCone_pt
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ) :
    (sectionsTowerCone R K).pt = ((globalSections R).mapHomologicalComplex _).obj K := rfl

/-- The complex of global sections is the limit of the tower of complexes of sections. -/
def isLimitSectionsTowerCone
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ) :
    IsLimit (sectionsTowerCone R K) :=
  (isLimitLimitConeAsFunctor _).whiskerEquivalence LiftedNat.equivalence.op

/-- If the restriction maps of the sections of a complex of sheaves are surjective in every
degree, the transition maps of its tower of complexes of sections are epimorphisms. -/
theorem epi_sectionsTower_map
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ)
    (hK : ∀ (k : ℤ) (n n' : LiftedNat.{u}) (h : n ≤ n'),
      Function.Surjective (((sectionsFunctor R).obj (K.X k)).map (homOfLE h).op)) (n : ℕ) :
    Epi ((sectionsTower R K).map (homOfLE (Nat.le_succ n)).op) := by
  refine HomologicalComplex.epi_of_epi_f _ fun k => ?_
  have e : LiftedNat.ofNat.op.map (homOfLE (Nat.le_succ n)).op =
      (homOfLE (LiftedNat.up_le_up_iff.{u}.2 (Nat.le_succ n))).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [sectionsTower_map_f, e]
  exact (ModuleCat.epi_iff_surjective _).2 (hK k _ _ _)

variable (ℬ : DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := LiftedNat.{u}) R))

/-- **The derived global sections of a graded injective K-injective module are a derived limit**:
at such a module `I`, `RΓ(I)` is `R lim_n I(n)`, the derived limit in `D(R)` of the tower of
complexes of sections of `I` over the stages `n`. -/
theorem isDerivedLimit_derivedGlobalSections_of_isDGInjective
    {I : DifferentialGradedModule.{u, u, u} ℬ} (hI : IsDGInjective I) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit (sectionsTower R I.complex ⋙ DerivedCategory.Q)
      ((derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I))) := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have := epi_sectionsTower_map R I.complex
    (fun k _ _ h => surjective_sections_map_of_isDGInjective hI k h)
  rw [derivedGlobalSections_obj_of_isDGInjective R ℬ hI]
  exact isDerivedLimit_of_iso ((DerivedCategory.quotientCompQhIso _).app _).symm
    (DerivedCategory.isDerivedLimit_of_limit_cone_of_epi _ _ (isLimitSectionsTowerCone R I.complex))

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **The derived global sections are a derived limit**: every object `M` of `D(ℬ, d)` is
represented by a graded injective K-injective module `I`, and `RΓ(M)` is the derived limit of the
tower of complexes of sections of `I`. -/
theorem exists_isDerivedLimit_derivedGlobalSections (M : derivedCategory.{u, u, u} ℬ) :
    ∃ I : DifferentialGradedModule.{u, u, u} ℬ, IsDGInjective I ∧
      Nonempty (M ≅ (toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I)) ∧
      letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
        Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
      IsDerivedLimit (sectionsTower R I.complex ⋙ DerivedCategory.Q)
        ((derivedGlobalSections R ℬ).obj M) := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have : (toDerivedCategory.{u, u, u} ℬ).EssSurj :=
    Localization.essSurj _ (quasiIsomorphisms.{u, u, u} ℬ)
  obtain ⟨I, s, hs, hK, hG⟩ := exists_quasiIso_isDGInjective.{u, u, u}
    (X := constRingedSite LiftedNat.{u} R) ℬ ((toDerivedCategory.{u, u, u} ℬ).objPreimage M)
  have : IsIso ((toDerivedCategory.{u, u, u} ℬ).map s) :=
    Localization.inverts _ (quasiIsomorphisms.{u, u, u} ℬ) s hs
  let e : M ≅ (toDerivedCategory.{u, u, u} ℬ).obj I :=
    ((toDerivedCategory.{u, u, u} ℬ).objObjPreimageIso M).symm ≪≫
      asIso ((toDerivedCategory.{u, u, u} ℬ).map s)
  obtain ⟨I₀⟩ := I
  exact ⟨I₀, ⟨hG, hK⟩, ⟨e⟩, isDerivedLimit_of_iso ((derivedGlobalSections R ℬ).mapIso e.symm)
    (isDerivedLimit_derivedGlobalSections_of_isDGInjective R ℬ ⟨hG, hK⟩)⟩

end DerivedLimit

end Stacks.ChaoticSite
