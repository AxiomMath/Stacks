module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.EssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Lifting a pseudo-coherent complex from a quasi-compact open of an affine scheme

On a quasi-compact open `U` of an affine scheme `X`, every pseudo-coherent object of
`D(𝒪_U)` is the restriction of a bounded-above complex of finite free `𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.exists_boundedAbove_finiteFree_lift`: **Stacks 08EE.**

## Implementation notes

A finite free sheaf is a sheaf isomorphic to a finite coproduct of copies of the structure
sheaf. The witness is built over `Γ(X, ⊤)`: a bounded-above complex of finite free modules
approximating a representative of the lift, degree by degree, where at each step the next term
is chosen finite free and surjective on the top cohomology of the cone after localizing at each
of finitely many elements cutting out `U`. Sheafifying that complex gives the lift.

The statement is stated for an arbitrary derived-category closure on `𝒪_U`-modules; the proof
transports the object to `HasDerivedCategory.standard`, in which the pseudo-coherence API lives,
along the universal comparison of two localizations at the quasi-isomorphisms.

## References

* [Stacks Project, Tag 08EE](https://stacks.math.columbia.edu/tag/08EE)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u d v w z

open StacksDraft.PseudoCoherence CategoryTheory.Pretriangulated
open scoped ZeroObject TensorProduct

namespace PseudoCoherentOpenLift

/-- Being an isomorphism depends only on the morphism, so it transports along an equality of
morphisms. Used in place of `rw` where the two sides of the equality are spelled with different
but definitionally equal objects: the transport then happens in term mode, where definitional
equality is checked at the default transparency. -/
private lemma isIso_of_eq {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (h : f = g) (hf : IsIso f) : IsIso g := h ▸ hf

/-- A four-fold composite whose first, third and fourth factors are invertible is carried to an
epimorphism by any functor carrying its second factor to one.

Stated with the objects abstract so that the distribution of the functor over the composite
happens once, away from the concrete objects of the application. -/
private lemma epi_map_of_epi_middle
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W V : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : W ⟶ V)
    (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) (hb : Epi (F.map b)) :
    Epi (F.map ((a ≫ b ≫ c) ≫ d)) := by
  have := ha
  have := hb
  have := hc
  have := hd
  rw [F.map_comp, F.map_comp, F.map_comp]
  infer_instance

/-- The components of the inverse of a natural isomorphism are isomorphisms. -/
private lemma isIso_natIso_inv_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (Z : C) :
    IsIso (e.inv.app Z) := (e.app Z).symm.isIso_hom

private noncomputable def derivedCategoryUniverseEquiv
    {C : Type u} [Category.{v} C] [Abelian C]
    (h₁ : HasDerivedCategory.{d} C) (h₂ : HasDerivedCategory.{w} C) :
    @DerivedCategory C _ _ h₁ ≌ @DerivedCategory C _ _ h₂ :=
  Localization.uniq
    (@DerivedCategory.Q C _ _ h₁)
    (@DerivedCategory.Q C _ _ h₂)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

private noncomputable def derivedCategoryUniverseEquiv_Q_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    (h₁ : HasDerivedCategory.{d} C) (h₂ : HasDerivedCategory.{w} C)
    (K : CochainComplex C ℤ) :
    (derivedCategoryUniverseEquiv h₁ h₂).functor.obj
        ((@DerivedCategory.Q C _ _ h₁).obj K) ≅
      (@DerivedCategory.Q C _ _ h₂).obj K :=
  Localization.compUniqFunctor
    (@DerivedCategory.Q C _ _ h₁)
    (@DerivedCategory.Q C _ _ h₂)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) |>.app K

/-- The comparison of two derived-category closures of `C` identifies their cohomology
functors. -/
private noncomputable def derivedCategoryUniverseHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (h₁ : HasDerivedCategory.{d} C) (h₂ : HasDerivedCategory.{w} C) (n : ℤ) :
    (derivedCategoryUniverseEquiv h₁ h₂).functor ⋙
        @DerivedCategory.homologyFunctor C _ _ h₂ n ≅
      @DerivedCategory.homologyFunctor C _ _ h₁ n :=
  Localization.liftNatIso (@DerivedCategory.Q C _ _ h₁)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (@DerivedCategory.Q C _ _ h₁ ⋙ ((derivedCategoryUniverseEquiv h₁ h₂).functor ⋙
      @DerivedCategory.homologyFunctor C _ _ h₂ n))
    (@DerivedCategory.Q C _ _ h₁ ⋙ @DerivedCategory.homologyFunctor C _ _ h₁ n) _ _
    (Functor.isoWhiskerRight
        (Localization.compUniqFunctor (@DerivedCategory.Q C _ _ h₁)
          (@DerivedCategory.Q C _ _ h₂) (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)))
        (@DerivedCategory.homologyFunctor C _ _ h₂ n) ≪≫
      @DerivedCategory.homologyFunctorFactors C _ _ h₂ n ≪≫
      (@DerivedCategory.homologyFunctorFactors C _ _ h₁ n).symm)

/-- The derived functor of an exact functor is compatible with the comparison of two
derived-category closures on its source and on its target. -/
private noncomputable def mapDerivedCategoryUniverseIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (c₁ : HasDerivedCategory.{d} C) (c₂ : HasDerivedCategory.{w} C)
    (d₁ : HasDerivedCategory.{v} D) (d₂ : HasDerivedCategory.{z} D)
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] :
    (@Functor.mapDerivedCategory C _ _ c₁ D _ _ d₁ R _ _ _) ⋙
      (derivedCategoryUniverseEquiv d₁ d₂).functor ≅
    (derivedCategoryUniverseEquiv c₁ c₂).functor ⋙
      (@Functor.mapDerivedCategory C _ _ c₂ D _ _ d₂ R _ _ _) := by
  let Q₁ := @DerivedCategory.Q C _ _ c₁
  let QD₁ := @DerivedCategory.Q D _ _ d₁
  let QD₂ := @DerivedCategory.Q D _ _ d₂
  let G := (derivedCategoryUniverseEquiv d₁ d₂).functor
  let R₁ := @Functor.mapDerivedCategory C _ _ c₁ D _ _ d₁ R _ _ _
  let R₂ := @Functor.mapDerivedCategory C _ _ c₂ D _ _ d₂ R _ _ _
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let a : Q₁ ⋙ (R₁ ⋙ G) ≅ R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD₂ :=
    Functor.isoWhiskerRight (@Functor.mapDerivedCategoryFactors C _ _ c₁ D _ _ d₁ R _ _ _) G ≪≫
      Functor.isoWhiskerLeft _ (Localization.compUniqFunctor QD₁ QD₂
        (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)))
  let b : Q₁ ⋙ ((derivedCategoryUniverseEquiv c₁ c₂).functor ⋙ R₂) ≅
      R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QD₂ :=
    Functor.isoWhiskerRight
        (Localization.compUniqFunctor Q₁ (@DerivedCategory.Q C _ _ c₂) W) R₂ ≪≫
      (@Functor.mapDerivedCategoryFactors C _ _ c₂ D _ _ d₂ R _ _ _)
  exact Localization.liftNatIso Q₁ W (Q₁ ⋙ (R₁ ⋙ G))
    (Q₁ ⋙ ((derivedCategoryUniverseEquiv c₁ c₂).functor ⋙ R₂)) _ _ (a ≪≫ b.symm)


private lemma exists_finite_family_generating_localizations
    {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
    {ι : Type v} [Finite ι] (f : ι → R)
    (hM : ∀ i, Module.Finite (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M)) :
    ∃ (J : Type v) (_ : Finite J) (g : J → M),
      ∀ i, Submodule.span (Localization.Away (f i))
        (Set.range (fun j : J => LocalizedModule.mkLinearMap
          (Submonoid.powers (f i)) M (g j))) = ⊤ := by
  classical
  let n : ι → ℕ := fun i => Classical.choose
    (Module.Finite.exists_fin (R := Localization.Away (f i))
      (M := LocalizedModule (Submonoid.powers (f i)) M))
  let z : ∀ i, Fin (n i) → LocalizedModule (Submonoid.powers (f i)) M := fun i =>
    Classical.choose (Classical.choose_spec (Module.Finite.exists_fin
      (R := Localization.Away (f i))
      (M := LocalizedModule (Submonoid.powers (f i)) M)))
  have hz (i : ι) : Submodule.span (Localization.Away (f i)) (Set.range (z i)) = ⊤ :=
    Classical.choose_spec (Classical.choose_spec
      (Module.Finite.exists_fin (R := Localization.Away (f i))
        (M := LocalizedModule (Submonoid.powers (f i)) M)))
  let J : Type v := Σ i, Fin (n i)
  let q (i : ι) : M →ₗ[R] LocalizedModule (Submonoid.powers (f i)) M :=
    LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M
  let w (i : ι) (j : Fin (n i)) :
      M × Submonoid.powers (f i) :=
    Classical.choose (IsLocalizedModule.surj (Submonoid.powers (f i)) (q i) (z i j))
  let g (a : J) : M :=
    (w a.1 a.2).1
  have hg (i : ι) (j : Fin (n i)) :
      q i (g ⟨i, j⟩) =
        (algebraMap R (Localization.Away (f i)) ((w i j).2 : R)) • z i j := by
    simpa [g, w, Submonoid.smul_def] using
      (Classical.choose_spec (IsLocalizedModule.surj
        (Submonoid.powers (f i)) (q i) (z i j))).symm
  have hspan (i : ι) : Submodule.span (Localization.Away (f i))
      (Set.range (fun a : J => q i (g a))) = ⊤ := by
    apply le_antisymm
    · exact le_top
    · rw [← hz i]
      apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨j, rfl⟩ := hx
      let s := (w i j).2
      have hs : IsUnit (algebraMap R (Localization.Away (f i)) (s : R)) :=
        IsLocalization.map_units (Localization.Away (f i)) s
      have hxmem : (q i (g ⟨i, j⟩)) ∈
          Submodule.span (Localization.Away (f i))
            (Set.range (fun a : J => q i (g a))) :=
        Submodule.subset_span ⟨⟨i, j⟩, rfl⟩
      rw [hg i j] at hxmem
      exact (Submodule.smul_mem_iff_of_isUnit
        (p := Submodule.span (Localization.Away (f i))
          (Set.range (fun a : J => q i (g a)))) hs).mp hxmem
  exact ⟨J, inferInstance, g, hspan⟩

private lemma exists_uniform_local_homology_bound
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι] (f : ι → R)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (m : ℤ)
    (hlocal : ∀ i, StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K) m) :
    ∃ N : ℤ, ∀ i j, N ≤ j → IsZero
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{max v u} (Localization.Away (f i))) j).obj
          ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K)) := by
  classical
  choose b hb using fun i ↦
    StacksDraft.PseudoCoherence.isPseudoCoherentFrom_boundedAbove (hlocal i)
  obtain ⟨B, hB⟩ := Finite.bddAbove_range b
  refine ⟨max m B, fun i j hj ↦ hb i j ?_⟩
  exact le_trans (hB ⟨i, rfl⟩) (le_trans (le_max_right m B) hj)

private lemma exists_finite_principal_cover_of_compact_open
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → Γ(X, ⊤)),
      (∀ i, X.basicOpen (f i) ≤ U) ∧
        (U : Set X) = ⋃ i, (X.basicOpen (f i) : Set X) := by
  classical
  obtain ⟨s, hs, hUs⟩ :=
    (AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
      (X := X) (U := (U : Set X))).mp ⟨hU, U.isOpen⟩
  let ι : Type u := {r // r ∈ s}
  refine ⟨ι, hs.to_subtype, fun i => i.1, ?_, ?_⟩
  · intro i
    show (X.basicOpen i.1 : Set X) ⊆ (U : Set X)
    intro x hx
    rw [hUs]
    exact Set.mem_iUnion₂.mpr ⟨i.1, i.2, hx⟩
  · rw [hUs]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨⟨i, hi⟩, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i.1, i.2, hx⟩

private lemma exists_finite_free_sheaf_iso
    {R : Type u} [CommRing R] [Nontrivial R] (M : ModuleCat.{u} R)
    (hfinite : Module.Finite R M) (hfree : Module.Free R M) :
    ∃ I : Type u, Finite I ∧ Nonempty
      ((tilde.functor (CommRingCat.of R)).obj M ≅ SheafOfModules.free I) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis ι R M := Module.Free.chooseBasis R M
  let : Module.Finite R M := hfinite
  let : Module.Free R M := hfree
  let : Finite ι := Module.Finite.finite_basis b
  refine ⟨ι, inferInstance, ?_⟩
  exact ⟨(tilde.functor (CommRingCat.of R)).mapIso b.repr.toModuleIso ≪≫
    AlgebraicGeometry.tildeFinsupp ι⟩

private lemma quasiCompact_opens_ι
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) : QuasiCompact (Scheme.Opens.ι U) := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  have hUV : IsCompact ((U : Set X) ∩ (V : Set X)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU V.isOpen hV.isCompact
  have h := (Scheme.Opens.ι U).isOpenEmbedding.isInducing.isCompact_preimage' hUV
    (by
      rintro x ⟨hxU, hxV⟩
      exact ⟨⟨x, hxU⟩, rfl⟩)
  convert h using 1
  ext x
  simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, Set.mem_inter_iff]
  exact (and_iff_right x.property).symm

/-- The canonical identification of the cycles of a complex concentrated in one degree with the
module sitting there, stated for the spelling `CochainComplex.singleFunctor` of the single-degree
complex.

Mathlib's `HomologicalComplex.singleObjCyclesSelfIso` is stated for
`HomologicalComplex.single`; the two spellings are definitionally equal but not syntactically so,
and rewriting with an equation whose two sides carry different spellings of the same object
produces terms that are only definitionally well typed. -/
private noncomputable def singleFunctorObjCyclesSelfIso
    {C : Type*} [Category C] [Abelian C] (m : ℤ) (P : C) :
    HomologicalComplex.cycles ((CochainComplex.singleFunctor C m).obj P) m ≅ P :=
  HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) m P

/-- `PseudoCoherentOpenLift.singleFunctorObjCyclesSelfIso` is the inclusion of the cycles followed
by the identification of the degree-`m` term with the module, with every object spelled through
`CochainComplex.singleFunctor`. -/
private lemma singleFunctorObjCyclesSelfIso_hom
    {C : Type*} [Category C] [Abelian C] (m : ℤ) (P : C) :
    (singleFunctorObjCyclesSelfIso m P).hom =
      HomologicalComplex.iCycles ((CochainComplex.singleFunctor C m).obj P) m ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m P).hom := rfl

/-- A map from a projective object to the degree-`m` homology of a complex is induced by a chain
map out of the complex concentrated in degree `m`, compatibly with the canonical identification
of the cycles there.

Both sides of the conclusion are morphisms
`cycles ((singleFunctor C m).obj P) m ⟶ homology K m` as spelled, so the equation can be used to
rewrite with no definitional repair. -/
private lemma exists_hom_from_single_factoring
    {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ) (m : ℤ)
    (P : C) [Projective P] (f : P ⟶ HomologicalComplex.homology K m) :
    ∃ φ : (CochainComplex.singleFunctor C m).obj P ⟶ K,
      HomologicalComplex.homologyπ ((CochainComplex.singleFunctor C m).obj P) m ≫
          HomologicalComplex.homologyMap φ m =
        (singleFunctorObjCyclesSelfIso m P).hom ≫ f := by
  let g : P ⟶ HomologicalComplex.cycles K m := Projective.factorThru f (K.homologyπ m)
  have hg : g ≫ K.homologyπ m = f := Projective.factorThru_comp f (K.homologyπ m)
  let φ : (CochainComplex.singleFunctor C m).obj P ⟶ K :=
    HomologicalComplex.mkHomFromSingle (g ≫ K.iCycles m) (fun j _ ↦ by simp)
  refine ⟨φ, ?_⟩
  have hcycles : HomologicalComplex.cyclesMap φ m =
      (singleFunctorObjCyclesSelfIso m P).hom ≫ g := by
    apply (cancel_mono (K.iCycles m)).1
    simp [φ, singleFunctorObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i,
      Category.assoc]
  rw [HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc, hg]

/-- If the first map of a distinguished triangle is iso on `Hⁱ` for `i > m` and epi on `Hᵐ`,
then the third object lies in degrees `≤ m - 1`. -/
private lemma triangle_obj₃_isLE_of_approximation
    {R : Type u} [Ring R]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang _) {m : ℤ}
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁))
    (hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hi' : m ≤ i := by omega
  have hαepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁) := by
    rcases hi'.eq_or_lt with rfl | hlt
    · exact hepi
    · exact @IsIso.epi_of_iso _ _ _ _ _ (hiso i hlt)
  have hβ : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂ = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hαepi
  have hδα : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT i (i + 1) rfl).1
    exact @IsIso.mono_of_iso _ _ _ _ _ (hiso (i + 1) (by omega))
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros
    hβ hδα


private lemma exists_finite_free_epi_after_localization
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι] (f : ι → R)
    (M : ModuleCat.{max u v} R)
    (hM : ∀ i, Module.Finite (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M)) :
    ∃ P : ModuleCat.{max u v} R, Module.Finite R P ∧ Module.Free R P ∧
      ∃ p : P ⟶ M, ∀ i,
        Epi ((ModuleCat.extendScalars (algebraMap R (Localization.Away (f i)))).map p) := by
  classical
  obtain ⟨J, hJ, g, hg⟩ := exists_finite_family_generating_localizations f hM
  let := hJ
  let P := ModuleCat.of R (J →₀ R)
  let p : P ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination R g)
  refine ⟨P, inferInstance, inferInstance, p, fun i => ?_⟩
  let S := Localization.Away (f i)
  show Epi (let := (algebraMap R S).toAlgebra;
    ModuleCat.ofHom (p.hom.baseChange S))
  rw [toAlgebra_algebraMap]
  let e := (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M).symm
  let q := p.hom.baseChange S
  have hgen (j : J) : e (q (1 ⊗ₜ[R] Finsupp.single j 1)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (g j) := by
    have hsingle : p.hom (Finsupp.single j 1) = g j := by
      show (Finsupp.linearCombination R g) (Finsupp.single j 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
    show e (1 ⊗ₜ[R] p.hom (Finsupp.single j 1)) = _
    rw [hsingle]
    exact LocalizedModule.equivTensorProduct_symm_apply_tmul_one (Submonoid.powers (f i)) (g j)
  have hsurj : Function.Surjective (e.toLinearMap.comp q) := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    rw [← hg i]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨1 ⊗ₜ[R] Finsupp.single j 1, hgen j⟩
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := hsurj (e y)
  exact ⟨x, e.injective hx⟩

/-- Derived localization at `f` followed by cohomology in degree `n` carries a morphism to the
base change of its cohomology map: it is epi (resp. iso) as soon as the base change is. -/
private lemma localizationAway_homologyMap_epi_and_isIso
    {R : Type u} [CommRing R] (f : R)
    {K L : DerivedCategory (ModuleCat.{max u v} R)} (α : K ⟶ L) (n : ℤ) :
    (Epi ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map α)) →
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away f)) n).map
        ((localizationAwayFunctorAux f).map α))) ∧
    (IsIso ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map α)) →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away f)) n).map
        ((localizationAwayFunctorAux f).map α))) := by
  let F := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
  let : F.Additive := extendScalars_additive _
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
  let : PreservesFiniteColimits F := inferInstance
  let h := mapDerivedCategoryCompHomologyFunctorIso F n
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · show Epi ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ n).map α)
    rw [← NatIso.naturality_2 h α]
    dsimp only [Functor.comp_map]
    infer_instance
  · show IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ n).map α)
    rwa [NatIso.isIso_map_iff h]

private lemma exists_local_top_approximation
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι] (f : ι → R)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (n : ℤ)
    (hfinite : ∀ i, Module.Finite (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i))
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K)))
    (hvan : ∀ i j, n < j → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f i))) j).obj
        ((localizationAwayFunctorAux (f i)).obj K))) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      IsBoundedFiniteFree P ∧ P.IsStrictlyGE n ∧ P.IsStrictlyLE n ∧
      ∃ α : DerivedCategory.Q.obj P ⟶ K,
        (∀ k i, n < i → IsIso
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) i).map
            ((localizationAwayFunctorAux (f k)).map α))) ∧
        (∀ k, Epi
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) n).map
            ((localizationAwayFunctorAux (f k)).map α))) := by
  obtain ⟨P, hfin, hfree, p, hp⟩ := exists_finite_free_epi_after_localization f
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K) hfinite
  have hproj : Projective P := ModuleCat.projective_of_free (Module.Free.chooseBasis R P)
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let eh : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K ≅
      HomologicalComplex.homology L n :=
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n).app L
  obtain ⟨φ, hφ⟩ := exists_hom_from_single_factoring L n P (p ≫ eh.hom)
  let E := (CochainComplex.singleFunctor (ModuleCat.{max u v} R) n).obj P
  refine ⟨E, isBoundedFiniteFree_single P n, inferInstance, inferInstance,
    DerivedCategory.Q.map φ ≫ e.hom, ?_, ?_⟩
  · intro k i hi
    apply (localizationAway_homology_isZero (f k) (DerivedCategory.Q.obj E) i
      ((DerivedCategory.isLE_iff (DerivedCategory.Q.obj E) n).mp inferInstance i hi)).isIso
      (hvan k i hi)
  · intro k
    let F := ModuleCat.extendScalars (algebraMap R (Localization.Away (f k)))
    have hp' : Epi (F.map p) := hp k
    have hh : Epi (F.map (HomologicalComplex.homologyMap φ n)) := by
      have hcomp : Epi (F.map (HomologicalComplex.homologyπ
            ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) n).obj P) n) ≫
          F.map (HomologicalComplex.homologyMap φ n)) := by
        rw [← F.map_comp, hφ, F.map_comp, F.map_comp]
        infer_instance
      exact epi_of_epi (F.map (HomologicalComplex.homologyπ
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) n).obj P) n)) _
    have heq : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map
        (DerivedCategory.Q.map φ) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n).hom.app
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) n).obj P) ≫
        HomologicalComplex.homologyMap φ n ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n).inv.app L := by
      exact (NatIso.naturality_2
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n) φ).symm
    have hresult : Epi (F.map ((DerivedCategory.homologyFunctor _ n).map
        (DerivedCategory.Q.map φ ≫ e.hom))) := by
      rw [Functor.map_comp, heq]
      exact epi_map_of_epi_middle F _ _ _ _
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n).app
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) n).obj P)).isIso_hom
        (isIso_natIso_inv_app
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n) L)
        inferInstance hh
    exact (localizationAway_homologyMap_epi_and_isIso (f k) _ n).1 hresult

attribute [local instance] localizationAwayCommShift localizationAway_isTriangulated

/-- A finite free approximation on finitely many principal opens can be extended one
more degree to the left while retaining its previously constructed terms. -/
private lemma exists_next_local_approximation
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι] (f : ι → R)
    {E K : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (hE : IsBoundedFiniteFree E) (α : E ⟶ K) (n b : ℤ) (hnb : n ≤ b + 1)
    [E.IsStrictlyGE n] [E.IsStrictlyLE b]
    (hlocal : ∀ k m, IsPseudoCoherentFrom
      ((localizationAwayFunctorAux (f k)).obj (DerivedCategory.Q.obj K)) m)
    (hiso : ∀ k i, n < i → IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) i).map
        ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map α))))
    (hepi : ∀ k, Epi
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) n).map
        ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map α)))) :
    ∃ (F : CochainComplex (ModuleCat.{max u v} R) ℤ) (ι : E ⟶ F) (β : F ⟶ K),
      IsBoundedFiniteFree F ∧ F.IsStrictlyGE (n - 1) ∧ F.IsStrictlyLE b ∧
      ι ≫ β = α ∧ (∀ i, n ≤ i → IsIso (ι.f i)) ∧
      (∀ k i, n - 1 < i → IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) i).map
          ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map β)))) ∧
      (∀ k, Epi
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{max u v} (Localization.Away (f k))) (n - 1)).map
          ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map β)))) := by
  let T₀ := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)
  have hT₀ : T₀ ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished α
  let T := T₀.invRotate
  have hT : T ∈ distTriang _ := inv_rot_of_distTriang _ hT₀
  have hCn (k : ι) : ((localizationAwayFunctorAux (f k)).obj T.obj₁).IsLE n := by
    let G := localizationAwayFunctorAux (f k)
    have hC : (G.obj T₀.obj₃).IsLE (n - 1) :=
      triangle_obj₃_isLE_of_approximation (G.mapTriangle.obj T₀)
        (G.map_distinguished T₀ hT₀) (hiso k) (hepi k)
    have hs : ((G.obj T₀.obj₃)⟦(-1 : ℤ)⟧).IsLE n :=
      DerivedCategory.TStructure.t.isLE_shift (G.obj T₀.obj₃) (n - 1) (-1) n (by omega)
    apply (DerivedCategory.isLE_iff _ n).mpr
    intro i hi
    exact ((DerivedCategory.isLE_iff _ n).mp hs i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso ((G.commShiftIso (-1)).app T₀.obj₃))
  have hfinite (k : ι) : Module.Finite (Localization.Away (f k))
      (LocalizedModule (Submonoid.powers (f k))
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj T.obj₁)) := by
    let G := localizationAwayFunctorAux (f k)
    have hpc : IsPseudoCoherentFrom (G.obj T.obj₁) n := by
      have ht := _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_three (n - 1)
        (G.mapTriangle.obj T) (G.map_distinguished T hT)
        (localizationAway_isPseudoCoherentFrom_of_boundedFiniteFree (f k) E hE (n - 1 + 1))
        (hlocal k (n - 1))
      rwa [sub_add_cancel] at ht
    have := _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom
      (G.obj T.obj₁) n hpc ((DerivedCategory.isLE_iff _ n).mp (hCn k))
    exact Module.Finite.equiv (localizationAwayHomologyIso (f k) T.obj₁ n).toLinearEquiv
  obtain ⟨P, hP, hPge, hPle, g, hgiso, hgepi⟩ :=
    exists_local_top_approximation f T.obj₁ n hfinite
      (fun k => (DerivedCategory.isLE_iff _ n).mp (hCn k))
  have := isKProjective_of_boundedFiniteFree hP
  have := isKProjective_of_boundedFiniteFree hE
  obtain ⟨δ, hδ⟩ := exists_chainMap_of_isKProjective P E (g ≫ T.mor₁)
  let F := CochainComplex.mappingCone δ
  have hF : IsBoundedFiniteFree F := boundedFiniteFree_mappingCone hP hE δ
  have := isKProjective_of_boundedFiniteFree hF
  let S := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle δ)
  have hS : S ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished δ
  have hsq : S.mor₁ ≫ 𝟙 _ = g ≫ T.mor₁ := by
    show DerivedCategory.Q.map δ ≫ 𝟙 _ = g ≫ T.mor₁
    rw [Category.comp_id]
    exact hδ
  obtain ⟨ψ, hψ₁, hψ₂⟩ := complete_distinguished_triangle_morphism S T hS hT g (𝟙 _) hsq
  let φ : S ⟶ T := Triangle.homMk _ _ g (𝟙 _) ψ hsq hψ₁ hψ₂
  let j := CochainComplex.mappingCone.inr δ
  obtain ⟨β, hβ, hQβ⟩ := exists_chainMap_lift_under j
    (fun i => (CochainComplex.mappingCone.snd δ).v i i (add_zero i))
    (fun i => CochainComplex.mappingCone.inr_f_snd_v δ i) α ψ (by
      have h : DerivedCategory.Q.map j ≫ ψ = 𝟙 _ ≫ DerivedCategory.Q.map α := hψ₁
      rw [Category.id_comp] at h
      exact h)
  refine ⟨F, j, β, hF, ?_, ?_, hβ, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P.isZero_of_isStrictlyGE n (i + 1) (by omega),
      E.isZero_of_isStrictlyGE n i (by omega)⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P.isZero_of_isStrictlyLE n (i + 1) (by omega),
      E.isZero_of_isStrictlyLE b i hi⟩
  · intro i hi
    let r := (CochainComplex.mappingCone.snd δ).v i i (add_zero i)
    refine ⟨r, CochainComplex.mappingCone.inr_f_snd_v δ i, ?_⟩
    have hz := P.isZero_of_isStrictlyLE n (i + 1) (by omega)
    have hh := CochainComplex.mappingCone.id_X δ i (i + 1) rfl
    have hzero : (CochainComplex.mappingCone.fst δ).1.v i (i + 1) rfl = 0 :=
      hz.eq_of_tgt _ _
    simpa only [hzero, HasZeroMorphisms.zero_comp, zero_add] using hh
  · intro k i hi
    rw [hQβ]
    let G := localizationAwayFunctorAux (f k)
    apply _root_.PseudoCoherence.isIso_homology_of_triangleMorphism
      (G.map_distinguished S hS) (G.map_distinguished T hT) (G.mapTriangle.map φ) i
    · show Epi ((DerivedCategory.homologyFunctor _ i).map (G.map g))
      rcases (show n ≤ i by omega).eq_or_lt with rfl | h
      · exact hgepi k
      · have := hgiso k i h
        infer_instance
    · show IsIso ((DerivedCategory.homologyFunctor _ i).map (G.map (𝟙 _)))
      infer_instance
    · exact hgiso k (i + 1) (by omega)
    · show Mono ((DerivedCategory.homologyFunctor _ (i + 1)).map (G.map (𝟙 _)))
      infer_instance
  · intro k
    rw [hQβ]
    let G := localizationAwayFunctorAux (f k)
    apply _root_.PseudoCoherence.epi_homology_of_triangleMorphism
      (G.map_distinguished S hS) (G.map_distinguished T hT) (G.mapTriangle.map φ) (n - 1)
    · show Epi ((DerivedCategory.homologyFunctor _ (n - 1)).map (G.map (𝟙 _)))
      infer_instance
    · show Epi ((DerivedCategory.homologyFunctor _ (n - 1 + 1)).map (G.map g))
      rw [sub_add_cancel]
      exact hgepi k
    · show Mono ((DerivedCategory.homologyFunctor _ (n - 1 + 1)).map (G.map (𝟙 _)))
      infer_instance

/-- An approximation accurate above a degree on a finite family of principal opens. -/
private structure LocalFiniteFreeApproximation {R : Type u} [CommRing R]
    {ι : Type v} (f : ι → R)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b n : ℤ) where
  complex : CochainComplex (ModuleCat.{max u v} R) ℤ
  map : complex ⟶ K
  finiteFree : IsBoundedFiniteFree complex
  ge : complex.IsStrictlyGE n
  le : complex.IsStrictlyLE b
  iso : ∀ k i, n < i → IsIso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) i).map
      ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map map)))
  epi : ∀ k, Epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) n).map
      ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map map)))

/-- The degreewise stationary colimit of the local approximations is a finite free
complex inducing a quasi-isomorphism on each principal open. -/
private lemma exists_local_finiteFree_resolution
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι] (f : ι → R)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (b : ℤ)
    (hK : ∀ k m, IsPseudoCoherentFrom
      ((localizationAwayFunctorAux (f k)).obj (DerivedCategory.Q.obj K)) m)
    (hvan : ∀ k i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) i).obj
        ((localizationAwayFunctorAux (f k)).obj (DerivedCategory.Q.obj K)))) :
    ∃ (F : CochainComplex (ModuleCat.{max u v} R) ℤ) (α : F ⟶ K),
      (∀ i, Module.Finite R (F.X i) ∧ Module.Free R (F.X i)) ∧
      F.IsStrictlyLE b ∧ ∀ k,
        IsIso ((localizationAwayFunctorAux (f k)).map (DerivedCategory.Q.map α)) := by
  classical
  have hzero : IsBoundedFiniteFree (0 : CochainComplex (ModuleCat.{max u v} R) ℤ) := by
    refine ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, fun i => ?_⟩
    have : Subsingleton ((0 : CochainComplex (ModuleCat.{max u v} R) ℤ).X i) :=
      ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _))
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩
  have hzeroiso (k : ι) (i : ℤ) (hi : b < i) : IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f k))) i).map
        ((localizationAwayFunctorAux (f k)).map
          (DerivedCategory.Q.map (0 : (0 : CochainComplex (ModuleCat.{max u v} R) ℤ) ⟶ K)))) :=
    (localizationAway_homology_isZero (f k) _ i
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map_isZero
        (DerivedCategory.Q.map_isZero (isZero_zero _)))).isIso (hvan k i hi) _
  let a₀ : LocalFiniteFreeApproximation f K b (b + 1 - (0 : ℕ)) := {
    complex := 0
    map := 0
    finiteFree := hzero
    ge := by infer_instance
    le := by infer_instance
    iso := fun k i hi => hzeroiso k i (by omega)
    epi := fun k => by have := hzeroiso k (b + 1 - (0 : ℕ)) (by omega); infer_instance }
  have hnext (k : ℕ) (a : LocalFiniteFreeApproximation f K b (b + 1 - k)) :
      ∃ a' : LocalFiniteFreeApproximation f K b (b + 1 - (k + 1 : ℕ)),
        ∃ f : a.complex ⟶ a'.complex, f ≫ a'.map = a.map ∧
          ∀ i, b + 1 - k ≤ i → IsIso (f.f i) := by
    have := a.ge
    have := a.le
    obtain ⟨F, f, β, hF, hge, hle, hcomm, hf, hi, he⟩ :=
      exists_next_local_approximation f a.finiteFree a.map (b + 1 - k) b (by omega)
        hK a.iso a.epi
    have heq : b + 1 - (k + 1 : ℕ) = b + 1 - k - 1 := by omega
    refine ⟨⟨F, β, hF, ?_, hle, ?_, ?_⟩, f, hcomm, hf⟩
    · simpa only [heq] using hge
    · simpa only [heq] using hi
    · rw [heq]
      exact he
  choose next trans hcomm hf using hnext
  let a : ∀ k : ℕ, LocalFiniteFreeApproximation f K b (b + 1 - k) :=
    Nat.rec a₀ (fun k x => next k x)
  let D : ℕ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ :=
    Functor.ofSequence (fun k => trans k (a k))
  let coc : Cocone D := ⟨K, NatTrans.ofSequence (fun k => (a k).map) (fun k => by
    show D.map (homOfLE (Nat.le_succ k)) ≫ (a (k + 1)).map = (a k).map ≫ 𝟙 _
    rw [Category.comp_id]
    dsimp only [D]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hcomm k (a k))⟩
  have hstable (k : ℕ) (i : ℤ) (hi : b + 1 - k ≤ i) :
      (D ⋙ HomologicalComplex.eval _ _ i).IsEventuallyConstantFrom k := by
    intro l g
    have hg : k ≤ l := leOfHom g
    have heq : g = homOfLE hg := Subsingleton.elim _ _
    rw [heq]
    apply isIso_map_of_nat
    intro j hj
    show IsIso ((D.map (homOfLE (Nat.le_succ j))).f i)
    rw [show D.map (homOfLE (Nat.le_succ j)) = trans j (a j) from
      Functor.ofSequence_map_homOfLE_succ (fun k => trans k (a k)) j]
    exact hf j (a j) i (by omega)
  have hι (k : ℕ) (i : ℤ) (hi : b + 1 - k ≤ i) :
      IsIso ((colimit.ι D k).f i) :=
    (hstable k i hi).isIso_ι_of_isColimit
      (isColimitOfPreserves (HomologicalComplex.eval _ _ i) (colimit.isColimit D))
  let α := colimit.desc D coc
  have hfac (k : ℕ) : colimit.ι D k ≫ α = (a k).map := colimit.ι_desc _ _
  refine ⟨colimit D, α, ?_, ?_, ?_⟩
  · intro i
    let k := (b + 1 - i).toNat
    have := hι k i (by dsimp [k]; omega)
    obtain ⟨hfinite, hfree⟩ := (a k).finiteFree.finiteFree i
    have : Module.Finite R ((D.obj k).X i) := hfinite
    have : Module.Free R ((D.obj k).X i) := hfree
    let e := (asIso ((colimit.ι D k).f i)).toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := hι 0 i (by omega)
    have := (a 0).le
    exact ((a 0).complex.isZero_of_isStrictlyLE b i hi).of_iso
      (asIso ((colimit.ι D 0).f i)).symm
  · intro l
    rw [DerivedCategory.isIso_iff]
    intro i
    let k := (b + 2 - i).toNat
    have hm := hι k (i - 1) (by dsimp [k]; omega)
    have hz := hι k i (by dsimp [k]; omega)
    have hp := hι k (i + 1) (by dsimp [k]; omega)
    have hq := quasiIsoAt_of_isIso_components (colimit.ι D k) i
    have hmap : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
        (DerivedCategory.Q.map (colimit.ι D k))) := by
      show IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor _ i).map _)
      rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ i)]
      exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp hq
    have hmapLocal := (localizationAway_homologyMap_epi_and_isIso (f l)
      (DerivedCategory.Q.map (colimit.ι D k)) i).2 inferInstance
    have hcomp := (a k).iso l i (by dsimp [k]; omega)
    have hmapeq := congrArg (fun m =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f l))) i).map
        ((localizationAwayFunctorAux (f l)).map (DerivedCategory.Q.map m))) (hfac k)
    have hsplit :
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f l))) i).map
            ((localizationAwayFunctorAux (f l)).map
              (DerivedCategory.Q.map (colimit.ι D k ≫ α))) =
          (DerivedCategory.homologyFunctor
              (ModuleCat.{max u v} (Localization.Away (f l))) i).map
            ((localizationAwayFunctorAux (f l)).map
              (DerivedCategory.Q.map (colimit.ι D k))) ≫
            (DerivedCategory.homologyFunctor
                (ModuleCat.{max u v} (Localization.Away (f l))) i).map
              ((localizationAwayFunctorAux (f l)).map (DerivedCategory.Q.map α)) := by
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    have hcomp' := isIso_of_eq hsplit (isIso_of_eq hmapeq.symm hcomp)
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f l))) i).map
        ((localizationAwayFunctorAux (f l)).map (DerivedCategory.Q.map (colimit.ι D k))))
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away (f l))) i).map
        ((localizationAwayFunctorAux (f l)).map (DerivedCategory.Q.map α)))


private noncomputable local instance restriction_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Y) :=
    preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj f.opensFunctor.op) := inferInstance
  have : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X) :=
    preservesFiniteLimits_of_natIso (Iso.refl
      (Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf X)

/-- The comparison of two left derived functors of isomorphic functors, with the localization
datum and the two derived-functor data supplied as hypotheses instead of synthesized.

`CategoryTheory.Functor.leftDerivedNatIso` takes them as instance arguments, and the application
below has the two sides reaching the category of `𝒪_Y`-modules by different routes —
`AlgebraicGeometry.Scheme.Modules` on the restriction side and
`SheafOfModules (structureSheafRing _)` on the derived-pullback side, whose `Preadditive` instances
are the direct one and the one through `Abelian`. Instance search does not cross the two spellings;
unification of explicit arguments does. -/
private noncomputable def leftDerivedIsoOfIso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : C ⥤ D} {W : MorphismProperty C} (hW : L.IsLocalization W)
    (LF' LF : D ⥤ H) {F F' : C ⥤ H} {α' : L ⋙ LF' ⟶ F'} {α : L ⋙ LF ⟶ F}
    (h' : haveI := hW; LF'.IsLeftDerivedFunctor α' W)
    (h : haveI := hW; LF.IsLeftDerivedFunctor α W)
    (τ : F' ≅ F) : LF' ≅ LF :=
  haveI := hW
  haveI := h'
  haveI := h
  Functor.leftDerivedNatIso LF' LF α' α W τ

private noncomputable def derivedPullbackIsoRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ≅
      (Scheme.Modules.restrictFunctor f).mapDerivedCategory := by
  have hrestrict : (Scheme.Modules.restrictFunctor f).mapDerivedCategory.IsLeftDerivedFunctor
      (Scheme.Modules.restrictFunctor f).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  have hpull : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).IsLeftDerivedFunctor
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        f.toLRSHom.toShHom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing Y.toRingedSpace)) (ComplexShape.up ℤ)) :=
    inferInstance
  exact (leftDerivedIsoOfIso
    (inferInstanceAs ((DerivedCategory.Qh (C := Y.Modules)).IsLocalization
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))))
    (Scheme.Modules.restrictFunctor f).mapDerivedCategory
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom)
    hrestrict hpull
    (Functor.isoWhiskerRight
      { hom := NatTrans.mapHomotopyCategory (Scheme.Modules.restrictFunctorIsoPullback f).hom _
        inv := NatTrans.mapHomotopyCategory (Scheme.Modules.restrictFunctorIsoPullback f).inv _
        hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
        inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
      DerivedCategory.Qh)).symm


private noncomputable def mapDerivedCategoryIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ _ _ (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)

private noncomputable def mapDerivedCategoryCompIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory := by
  let e : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ≅
      (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)) _
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) _ _ _ _
      (e ≪≫ (F ⋙ G).mapDerivedCategoryFactors.symm)

private lemma isIso_of_restriction_cover
    {Y : Scheme.{u}} {ι : Type*} (X : ι → Scheme.{u}) (j : ∀ i, X i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)] (hcover : ∀ y : Y, ∃ i x, j i x = y)
    {M N : Y.Modules} (α : M ⟶ N)
    (hα : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (j i)).map α)) : IsIso α := by
  have hs (y : Y) : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map α) := by
    obtain ⟨i, x, rfl⟩ := hcover y
    have := hα i
    rw [← NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso (j i) x)]
    show IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((Scheme.Modules.toPresheaf (X i)).map ((Scheme.Modules.restrictFunctor (j i)).map α)))
    infer_instance
  let : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map α).hom) := hs
  have hsheaf : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map α) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  have : IsIso ((Scheme.Modules.toPresheaf Y).map α) := by
    show IsIso ((TopCat.Sheaf.forget Ab.{u} _).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map α))
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ hsheaf
  exact isIso_of_reflects_iso α (Scheme.Modules.toPresheaf Y)

private lemma isIso_derived_of_restriction_cover
    {Y : Scheme.{u}} {ι : Type*} (X : ι → Scheme.{u}) (j : ∀ i, X i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)] (hcover : ∀ y : Y, ∃ i x, j i x = y)
    {M N : DerivedCategory Y.Modules} (α : M ⟶ N)
    (hα : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (j i)).mapDerivedCategory.map α)) :
    IsIso α := by
  rw [DerivedCategory.isIso_iff]
  intro n
  apply isIso_of_restriction_cover X j hcover
  intro i
  have := hα i
  let e := StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (Scheme.Modules.restrictFunctor (j i)) n
  exact (NatIso.isIso_map_iff e α).mp (by dsimp; infer_instance)

private lemma isPseudoCoherentFrom_of_iso
    {X : RingedSpace.{u, u}} {K L : DerivedCategory (StrictlyPerfect.OXMod.{u} X)}
    (e : K ≅ L) (m : ℤ) (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) K m) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) L m := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := h
  exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

private lemma isPseudoCoherentFrom_restriction
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (E : DerivedCategory Y.Modules) (m : ℤ)
    (hE : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) E m) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace)
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E) m :=
  isPseudoCoherentFrom_of_iso ((derivedPullbackIsoRestrict j).app E) m
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
      j.toLRSHom.toShHom E m hE)

private lemma exists_principal_cover_of_open_immersion
    {A : CommRingCat.{u}} {Y : Scheme.{u}} (j : Y ⟶ Spec A)
    [IsOpenImmersion j] [CompactSpace Y] :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → A)
      (l : ∀ i, Spec (.of (Localization.Away (f i))) ⟶ Y),
      (∀ i, IsOpenImmersion (l i)) ∧
      (∀ i, l i ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f i))))) ∧
      (∀ y : Y, ∃ i x, l i x = y) := by
  classical
  have hc : IsCompact (Set.range j) := isCompact_range j.continuous
  obtain ⟨s, hs, heq⟩ :=
    (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
      PrimeSpectrum.isTopologicalBasis_basic_opens PrimeSpectrum.isCompact_basicOpen
        (Set.range j)).mp
        ⟨hc, j.isOpenEmbedding.isOpen_range⟩
  let ι : Type u := {a : A // a ∈ s}
  let g (a : A) := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))
  have hg (a : A) : Set.range (g a) =
      ((PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  have hle (i : ι) : Set.range (g i.1) ⊆ Set.range j := by
    intro x hx
    rw [hg] at hx
    exact heq ▸ Set.mem_iUnion₂.mpr ⟨i.1, i.2, hx⟩
  let l (i : ι) := IsOpenImmersion.lift j (g i.1) (hle i)
  refine ⟨ι, hs.to_subtype, Subtype.val, l, fun i => inferInstance, ?_, ?_⟩
  · intro i
    exact IsOpenImmersion.lift_fac j (g i.1) (hle i)
  · intro y
    have hy : j y ∈ ⋃ i ∈ s, ((PrimeSpectrum.basicOpen i : Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)) := heq ▸ (⟨y, rfl⟩ : j y ∈ Set.range j)
    obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp hy
    have hya' : j y ∈ Set.range (g a) := by rwa [hg]
    obtain ⟨x, hx⟩ := hya'
    refine ⟨⟨a, ha⟩, x, j.isOpenEmbedding.injective ?_⟩
    show (l ⟨a, ha⟩ ≫ j) x = j y
    rw [IsOpenImmersion.lift_fac]
    exact hx

private local instance tilde_additive (A : CommRingCat.{u}) :
    (tilde.functor A).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

private noncomputable local instance tilde_limits (A : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor A) :=
  AlgebraicGeometry.tilde.preservesFiniteLimits A


private noncomputable def restrictionCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctor (f ≫ g)).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor g).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor f).mapDerivedCategory :=
  mapDerivedCategoryIso (Scheme.Modules.restrictFunctorComp f g) ≪≫
    (mapDerivedCategoryCompIso _ _).symm

private local instance localization_additive (A : CommRingCat.{u}) (f : A) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))).Additive :=
  extendScalars_additive _

private noncomputable local instance localization_preservesFiniteLimits
    (A : CommRingCat.{u}) (f : A) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) :=
  extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))

private noncomputable local instance tilde_localization_colimits (A : CommRingCat.{u}) (f : A) :
    PreservesFiniteColimits (tilde.functor (CommRingCat.of (Localization.Away f))) :=
  by
  let : (tilde.functor (CommRingCat.of (Localization.Away f))).IsLeftAdjoint :=
    (tilde.adjunction (R := CommRingCat.of (Localization.Away f))).isLeftAdjoint
  infer_instance

private noncomputable def localizationTildeIso (A : CommRingCat.{u}) (f : A) :
    (tilde.functor A).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))).mapDerivedCategory ≅
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory ⋙
      (tilde.functor (CommRingCat.of (Localization.Away f))).mapDerivedCategory :=
  by
  let B := CommRingCat.of (Localization.Away f)
  let L := ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))
  letI : PreservesFiniteLimits L := localization_preservesFiniteLimits A f
  letI : PreservesFiniteColimits (tilde.functor B) := tilde_localization_colimits A f
  exact mapDerivedCategoryCompIso (tilde.functor A)
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) ≪≫
    mapDerivedCategoryIso
      (Functor.isoWhiskerLeft (tilde.functor A)
        (Scheme.Modules.restrictFunctorIsoPullback _) ≪≫
        AlgebraicGeometry.pullbackTildeIso A _
          (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) ≪≫
    (mapDerivedCategoryCompIso
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f)))
      (tilde.functor (CommRingCat.of (Localization.Away f)))).symm

private lemma isPseudoCoherentFrom_of_tildeDerived
    (A : CommRingCat.{u}) (M : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hM : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := (Spec A).toRingedSpace)
      ((tilde.functor A).mapDerivedCategory.obj M) m) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom M m := by
  let K := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  have h := isPseudoCoherentFrom_of_iso
    ((tilde.functor A).mapDerivedCategory.mapIso e).symm m hM
  have h' := isPseudoCoherentFrom_of_iso ((tilde.functor A).mapDerivedCategoryFactors.app K) m h
  exact ((AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff K m).mp h').ofIso e


/-- **Every object of `D_QCoh(𝒪_{Spec A})` is the derived sheafification of a complex of
`A`-modules.**

This is the affine derived Spec–Γ equivalence `AlgebraicGeometry.derivedTilde_isEquivalence`,
read at an arbitrary pair of derived-category closures. That theorem is proved for the locally
small closures `ModuleCat.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphism types are in `Type u`,
whereas the pseudo-coherence API in use here is stated for `HasDerivedCategory.standard`. The
statement is carried between the two along the canonical comparison of the localizations. -/
private lemma exists_iso_derivedTilde_obj (A : CommRingCat.{u})
    (F : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).FullSubcategory) :
    ∃ K : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty ((tilde.functor A).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅ F.obj) := by
  have := AlgebraicGeometry.derivedTilde_isEquivalence A
  let Ψ := derivedCategoryUniverseEquiv
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
    (HasDerivedCategory.standard ((Spec A).Modules))
  let F₁ := Ψ.inverse.obj F.obj
  have hF₁ : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((@DerivedCategory.homologyFunctor ((Spec A).Modules) _ _
        (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A)) n).obj F₁) := by
    intro n
    refine (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso ?_ (F.2 n)
    exact ((@DerivedCategory.homologyFunctor ((Spec A).Modules) _ _
        (HasDerivedCategory.standard ((Spec A).Modules)) n).mapIso
        (Ψ.counitIso.app F.obj)).symm ≪≫
      (derivedCategoryUniverseHomologyIso
        (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
        (HasDerivedCategory.standard ((Spec A).Modules)) n).app F₁
  let F₁' : (@DerivedCategoryB.derivedCategoryB ((Spec A).Modules) _ _
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
      (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).FullSubcategory := ⟨F₁, hF₁⟩
  let M₁ := (@AlgebraicGeometry.derivedTilde A ModuleCat.hasDerivedCategory
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))).objPreimage F₁'
  refine ⟨(@DerivedCategory.Q (ModuleCat.{u} A) _ _
    ModuleCat.hasDerivedCategory).objPreimage M₁, ⟨?_⟩⟩
  have eT : (@Functor.mapDerivedCategory (ModuleCat.{u} A) _ _ ModuleCat.hasDerivedCategory
        ((Spec A).Modules) _ _ (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
        (tilde.functor A) _ _ _).obj
      ((@DerivedCategory.Q (ModuleCat.{u} A) _ _ ModuleCat.hasDerivedCategory).obj
        ((@DerivedCategory.Q (ModuleCat.{u} A) _ _
          ModuleCat.hasDerivedCategory).objPreimage M₁)) ≅ F₁ :=
    (@Functor.mapDerivedCategoryFactors (ModuleCat.{u} A) _ _ ModuleCat.hasDerivedCategory
        ((Spec A).Modules) _ _ (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
        (tilde.functor A) _ _ _).app _ ≪≫
      ((@AlgebraicGeometry.derivedTildeFactors A ModuleCat.hasDerivedCategory
        (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))).app _).symm ≪≫
      (@DerivedCategoryB.derivedCategoryB ((Spec A).Modules) _ _
          (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
          (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).ι.mapIso
        ((@AlgebraicGeometry.derivedTilde A ModuleCat.hasDerivedCategory
            (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))).mapIso
          ((@DerivedCategory.Q (ModuleCat.{u} A) _ _
            ModuleCat.hasDerivedCategory).objObjPreimageIso M₁) ≪≫
          (@AlgebraicGeometry.derivedTilde A ModuleCat.hasDerivedCategory
            (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
              (Spec A))).objObjPreimageIso F₁')
  exact (@Functor.mapDerivedCategory (ModuleCat.{u} A) _ _
          (HasDerivedCategory.standard (ModuleCat.{u} A)) ((Spec A).Modules) _ _
          (HasDerivedCategory.standard ((Spec A).Modules)) (tilde.functor A) _ _ _).mapIso
        (derivedCategoryUniverseEquiv_Q_iso ModuleCat.hasDerivedCategory
          (HasDerivedCategory.standard (ModuleCat.{u} A)) _).symm ≪≫
      ((mapDerivedCategoryUniverseIso ModuleCat.hasDerivedCategory
        (HasDerivedCategory.standard (ModuleCat.{u} A))
        (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory (Spec A))
        (HasDerivedCategory.standard ((Spec A).Modules))
        (tilde.functor A)).app _).symm ≪≫
      Ψ.functor.mapIso eT ≪≫ Ψ.counitIso.app F.obj

private lemma exists_finiteFree_resolution_on_open
    (A : CommRingCat.{u}) {Y : Scheme.{u}} (j : Y ⟶ Spec A)
    [IsOpenImmersion j] [QuasiCompact j] [CompactSpace Y]
    (E : DerivedCategory Y.Modules)
    (hE : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ),
      P.IsStrictlyLE b ∧ (∀ i, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
      Nonempty ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        ((tilde.functor A).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅ E) := by
  classical
  let EQC : AlgebraicGeometry.QuasicoherentDerivedCategory Y :=
    ⟨E, AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent Y E hE⟩
  obtain ⟨F, ⟨eF⟩⟩ := AlgebraicGeometry.exists_quasicoherentDerived_lift j EQC
  obtain ⟨K, ⟨eK⟩⟩ := exists_iso_derivedTilde_obj A F
  let T := (tilde.functor A).mapDerivedCategory
  let R := (Scheme.Modules.restrictFunctor j).mapDerivedCategory
  let e : R.obj (T.obj (DerivedCategory.Q.obj K)) ≅ E :=
    R.mapIso eK ≪≫ ((derivedPullbackIsoRestrict j).app F.obj).symm ≪≫ eF
  obtain ⟨ι, hι, f, l, hlopen, hfac, hcover⟩ := exists_principal_cover_of_open_immersion j
  let := hι
  let := hlopen
  let g (i : ι) := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f i))))
  let eg (i : ι) : (Scheme.Modules.restrictFunctor (g i)).mapDerivedCategory ≅
      R ⋙ (Scheme.Modules.restrictFunctor (l i)).mapDerivedCategory :=
    mapDerivedCategoryIso (Scheme.Modules.restrictFunctorCongr (hfac i).symm) ≪≫
      restrictionCompIso (l i) j
  have hlocal (i : ι) (m : ℤ) : IsPseudoCoherentFrom
      ((localizationAwayFunctorAux (f i)).obj (DerivedCategory.Q.obj K)) m := by
    apply isPseudoCoherentFrom_of_tildeDerived (.of (Localization.Away (f i)))
    have hm : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) E m := by
      obtain ⟨L, hL, eL⟩ := hE
      exact ⟨L, hL m, eL⟩
    have hj := isPseudoCoherentFrom_of_iso e.symm m hm
    have hl := isPseudoCoherentFrom_restriction (l i) _ m hj
    exact isPseudoCoherentFrom_of_iso
      (((localizationTildeIso A (f i)).symm.app (DerivedCategory.Q.obj K) ≪≫
        (eg i).app (T.obj (DerivedCategory.Q.obj K))).symm) m hl
  obtain ⟨b, hb⟩ := exists_uniform_local_homology_bound f (DerivedCategory.Q.obj K) 0
    (fun i => hlocal i 0)
  obtain ⟨P, α, hP, hPb, hα⟩ := exists_local_finiteFree_resolution f K b hlocal
    (fun i n hn => hb i n (le_of_lt hn))
  let φ := T.map (DerivedCategory.Q.map α)
  have hφ : IsIso (R.map φ) := by
    apply isIso_derived_of_restriction_cover (fun i => Spec (.of (Localization.Away (f i))))
      l hcover
    intro i
    have := hα i
    have hg : IsIso ((Scheme.Modules.restrictFunctor (g i)).mapDerivedCategory.map φ) := by
      refine (NatIso.isIso_map_iff (localizationTildeIso A (f i))
        (DerivedCategory.Q.map α)).mpr ?_
      dsimp
      exact (Functor.mapIso _ (asIso ((localizationAwayFunctorAux (f i)).map
        (DerivedCategory.Q.map α)))).isIso_hom
    exact (NatIso.isIso_map_iff (eg i) φ).mp hg
  exact ⟨P, b, hPb, hP, ⟨asIso (R.map φ) ≪≫ e⟩⟩

private lemma exists_finite_free_sheaf_iso_general
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (hfinite : Module.Finite R M) (hfree : Module.Free R M) :
    ∃ I : Type u, Finite I ∧ Nonempty
      ((tilde.functor (CommRingCat.of R)).obj M ≅ SheafOfModules.free I) := by
  classical
  by_cases hR : Nontrivial R
  · exact exists_finite_free_sheaf_iso M hfinite hfree
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have : Subsingleton M := Module.subsingleton R M
    let e : M ≃ₗ[R] (PEmpty.{u + 1} →₀ R) := LinearEquiv.ofSubsingleton _ _
    exact ⟨PEmpty.{u + 1}, inferInstance,
      ⟨(tilde.functor (CommRingCat.of R)).mapIso e.toModuleIso ≪≫
        AlgebraicGeometry.tildeFinsupp PEmpty.{u + 1}⟩⟩

end PseudoCoherentOpenLift

open PseudoCoherentOpenLift

/-- A pseudo-coherent derived object on a quasi-compact open of an affine
scheme is the restriction of a bounded-above complex of finite free modules. -/
@[stacks 08EE]
theorem exists_boundedAbove_finiteFree_lift
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{d} (OXMod.{u} (X.toRingedSpace.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u} (X.toRingedSpace.restrict U.isOpenEmbedding)))
    (hE : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := X.toRingedSpace.restrict U.isOpenEmbedding) E) :
    ∃ P : CochainComplex (OXMod.{u} X.toRingedSpace) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → CategoryTheory.Limits.IsZero (P.X i)) ∧
      (∀ i : ℤ, ∃ I : Type u, Finite I ∧ Nonempty
        (P.X i ≅ SheafOfModules.free (R := structureSheafOfRings X.toRingedSpace) I)) ∧
      Nonempty (DerivedCategory.Q.obj
        (((RingedSpace.restrictModules X.toRingedSpace U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅ E) := by
  classical
  let C := OXMod.{u} (X.toRingedSpace.restrict U.isOpenEmbedding)
  let hD : HasDerivedCategory.{d} C := inferInstance
  let hStd : HasDerivedCategory.{u + 1} C :=
    HasDerivedCategory.standard _
  let eU := derivedCategoryUniverseEquiv hD hStd
  let E' := eU.functor.obj E
  have hE' : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := (X.toRingedSpace.restrict U.isOpenEmbedding)) E' := by
    obtain ⟨K, hK, ⟨e⟩⟩ := hE
    exact ⟨K, hK, ⟨(derivedCategoryUniverseEquiv_Q_iso hD hStd K).symm ≪≫
      eU.functor.mapIso e⟩⟩
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let : QuasiCompact U.ι := quasiCompact_opens_ι X U hU
  let j := U.ι ≫ X.isoSpec.hom
  obtain ⟨F, b, hFb, hFfree, ⟨eF⟩⟩ := exists_finiteFree_resolution_on_open
    Γ(X, ⊤) j E' hE'
  let T := tilde.functor Γ(X, ⊤)
  let RX := Scheme.Modules.restrictFunctor X.isoSpec.hom
  let RU := Scheme.Modules.restrictFunctor U.ι
  have : (show OXMod.{u} X.toRingedSpace ⥤
      OXMod.{u} (X.toRingedSpace.restrict U.isOpenEmbedding) from
      Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms :=
    ⟨fun _ _ => by ext V x; rfl⟩
  let L := (T.mapHomologicalComplex (.up ℤ)).obj F
  let P := (RX.mapHomologicalComplex (.up ℤ)).obj L
  have hP : ∀ i, ∃ I : Type u, Finite I ∧ Nonempty
      (P.X i ≅ SheafOfModules.free (R := structureSheafOfRings X.toRingedSpace) I) := by
    intro i
    obtain ⟨I, hI, ⟨ei⟩⟩ := exists_finite_free_sheaf_iso_general
      (F.X i) (hFfree i).1 (hFfree i).2
    exact ⟨I, hI, ⟨RX.mapIso ei ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom).app _ ≪≫
      Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjFreeIso X.isoSpec.hom I⟩⟩
  let RP := ((RingedSpace.restrictModules X.toRingedSpace U).mapHomologicalComplex
    (.up ℤ)).obj P
  let ep : (@DerivedCategory.Q C _ _ hStd).obj RP ≅ E' :=
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U)
        (.up ℤ)).app P) ≪≫
    (RU.mapDerivedCategoryFactors.app P).symm ≪≫
    RU.mapDerivedCategory.mapIso (RX.mapDerivedCategoryFactors.app L).symm ≪≫
    RU.mapDerivedCategory.mapIso
      (RX.mapDerivedCategory.mapIso (T.mapDerivedCategoryFactors.app F).symm) ≪≫
    ((restrictionCompIso U.ι X.isoSpec.hom).app
      (T.mapDerivedCategory.obj (DerivedCategory.Q.obj F))).symm ≪≫ eF
  refine ⟨P, ⟨b, ?_⟩, hP, ?_⟩
  · intro i hi
    exact RX.map_isZero (T.map_isZero (F.isZero_of_isStrictlyLE b i hi))
  · exact ⟨eU.functor.preimageIso
      (derivedCategoryUniverseEquiv_Q_iso hD hStd RP ≪≫ ep)⟩


end AlgebraicGeometry

end
