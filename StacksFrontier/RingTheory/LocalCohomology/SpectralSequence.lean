module

public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic

/-!
# The local cohomology spectral sequence

For specialization-closed subsets `T` and `T'` of the spectrum of a Noetherian ring,
the local cohomology of a bounded-below derived object with support in their intersection
is the abutment of the Grothendieck spectral sequence for successive local cohomology.

## Main results

* `Stacks.LocalCohomology.exists_localCohomologySpectralSequence` gives the spectral sequence
  with second page `H^p_T(H^q_{T'}(K))` and abutment `H^{p+q}_{T ∩ T'}(K)`.

## Implementation notes

Convergence is expressed as in the Grothendieck spectral sequence of Tag 015N: the
spectral sequence belongs to a filtered complex whose cohomology is identified with
local cohomology of the intersection. Its page identifications, boundedness, finite
abutment filtration, eventual vanishing of differentials, and stable cycles and
boundaries are retained explicitly.

The two inputs to Tag 015N are supplied here. Sections with support in `T` of an injective
module are again injective, which is checked by Baer's criterion: a map from a finitely
generated ideal into the supported sections is killed by the finite intersection `I` of the
annihilators of the images of a generating set, so it factors through the `I`-power torsion
of the ambient module, which is injective by Tag 08XW and is contained in the supported
sections. And sections with support in `T'` followed by sections with support in `T` is
sections with support in `T ∩ T'`, because an element of the inner submodule lies in the
outer one exactly when the zero locus of its annihilator — computed in the ambient module,
the annihilator being insensitive to passing to a submodule — lies in `T`.

## References

* [Stacks Project, Tag 0EF6](https://stacks.math.columbia.edu/tag/0EF6)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- A prime in the zero locus of a finite infimum of ideals lies in the zero locus of one
of them. -/
private lemma mem_zeroLocus_finset_inf {A : Type u} [CommRing A]
    {ι : Type v} (s : Finset ι) (I : ι → Ideal A) {p : PrimeSpectrum A}
    (hp : p ∈ PrimeSpectrum.zeroLocus ((s.inf I : Ideal A) : Set A)) :
    ∃ i ∈ s, p ∈ PrimeSpectrum.zeroLocus (I i : Set A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hp
  | @insert i s hi ih =>
      have hp' : p ∈ PrimeSpectrum.zeroLocus ((I i ⊓ s.inf I : Ideal A) : Set A) := by
        simpa [Finset.inf_insert] using hp
      rw [PrimeSpectrum.zeroLocus_inf] at hp'
      rcases hp' with hpi | hps
      · exact ⟨i, by simp, hpi⟩
      · obtain ⟨j, hj, hpj⟩ := ih hps
        exact ⟨j, Finset.mem_insert_of_mem hj, hpj⟩

/-- Sections with support in `T` of an injective module over a Noetherian ring are injective. -/
private lemma sectionsWithSupportInFunctor_map_injective
    (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) [Injective M] :
    Module.Injective A (sectionsWithSupportIn A T M) := by
  classical
  let Q := sectionsWithSupportIn A T (M : Type (max u v))
  have : Module.Injective A (M : Type (max u v)) :=
    (Module.injective_iff_injective_object A (M : Type (max u v))).2 inferInstance
  have hBaer : Module.Baer A Q := by
    intro J g
    obtain ⟨s, hs, rfl⟩ := Submodule.fg_def.mp (Ideal.FG.of_isNoetherianRing J)
    let S := {x : A // x ∈ s}
    let : Finite S := hs.to_subtype
    let : Fintype S := Fintype.ofFinite S
    let τ : S → Ideal A := fun x => Ideal.torsionOf A (M : Type (max u v))
      (g ⟨x.val, Submodule.subset_span x.property⟩).val
    let I : Ideal A := Finset.univ.inf τ
    have hIsupport : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T := by
      intro p hp
      obtain ⟨x, -, hp⟩ := mem_zeroLocus_finset_inf _ τ hp
      exact (mem_sectionsWithSupportIn_iff A T M _).mp (g _).property hp
    let P : Submodule A (M : Type (max u v)) := Ideal.primaryComponent (M : Type (max u v)) I
    have hP : Module.Injective A P := Module.injective_primaryComponent
      (M : Type (max u v)) I
    let gM : Submodule.span A s →ₗ[A] (M : Type (max u v)) := Q.subtype.comp g
    have hkill (a : I) : a.val • gM = 0 := by
      refine LinearMap.ext_on Submodule.span_span_coe_preimage ?_
      rintro ⟨x, hx'⟩ hx
      show a.val • (g ⟨x, hx'⟩).val = 0
      exact (Ideal.mem_torsionOf_iff _ _).mp
        (Finset.inf_le (f := τ) (Finset.mem_univ ⟨x, hx⟩) a.property)
    have hmem (y : Submodule.span A s) : gM y ∈ P := by
      show gM y ∈ Ideal.primaryComponent (M : Type (max u v)) I
      apply (Ideal.primaryComponent_mem (M := (M : Type (max u v))) I (gM y)).2
      refine ⟨1, ?_⟩
      simp only [Submodule.mem_torsionBySet_iff]
      intro a
      exact LinearMap.congr_fun (hkill ⟨a, by simpa using a.property⟩) y
    have hPQ : P ≤ Q :=
      le_iSup₂ (f := fun (I : Ideal A) (_ : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T) =>
        I.primaryComponent (M : Type (max u v))) I hIsupport
    obtain ⟨e, he⟩ := Module.Baer.of_injective hP _ (gM.codRestrict P hmem)
    let j : P →ₗ[A] Q := P.subtype.codRestrict Q (fun x => hPQ x.property)
    refine ⟨j.comp e, fun x hx => Subtype.ext ?_⟩
    show (j (e x)).val = (g ⟨x, hx⟩).val
    rw [he x hx]
    rfl
  exact hBaer.injective

/-- An additive functor commutes with the single-object embedding into the bounded-below
homotopy category. -/
private noncomputable def mapHomotopyCategoryPlusObjSingleIso
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (n : ℤ) (X : C) :
    F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C n).obj X) ≅
      (HomotopyCategory.Plus.singleFunctor D n).obj (F.obj X) :=
  (HomotopyCategory.Plus.ι D).preimageIso
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app X))

/-- The plus-derived functor of an additive endofunctor of `A`-modules is a right derived
functor of its unit. -/
private theorem isRightDerivedFunctor_rightDerivedFunctorPlus {A : Type u} [CommRing A]
    (F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A) [F.Additive] :
    F.rightDerivedFunctorPlus.IsRightDerivedFunctor F.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A)) := by
  infer_instance

/-- **Stacks 0EF6.** The Grothendieck spectral sequence for local cohomology with two
supports: for specialization-closed subsets `T` and `T'` of the spectrum of a Noetherian
ring and a bounded-below derived object `X`, there is a spectral sequence with second page
`H^p_T(H^q_{T'}(X))` converging to `H^{p+q}_{T ∩ T'}(X)`.

Two points where this departs from the printed form of the tag. Its hypothesis reads
"let `A` be a ring", but `H^0_T` is introduced in that section only for a Noetherian ring,
every other statement of the section carries the hypothesis, and the tag's own proof invokes
the adjointness of `RΓ_T`, established only over a Noetherian ring (Tags 0EF2, 0EF3, 0EF4).
Noetherianity is what the proof below needs too: it is Baer's criterion that makes sections
with support in `T` of an injective module injective, and that is the acyclicity input of
Tag 015N. Second, the displayed second page of the tag is `H^p_T(H^p_{T'}(K))`, where the
inner `p` is a slip — its own abutment `H^{p + q}` exhibits two independent indices — and the
Grothendieck form `H^q_{T'}` is the one proved here. -/
@[stacks 0EF6]
theorem exists_localCohomologySpectralSequence
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A))
    (_hT : StableUnderSpecialization T) (_hT' : StableUnderSpecialization T')
    (X : DerivedCategory.Plus (ModuleCat.{max u v} A)) :
    ∃ K : FilteredObject (CochainComplex (ModuleCat.{max u v} A) ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (K.X.homology n ≅
        localCohomologyWithSupportInPlus A (T ∩ T') X n)) ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence (ModuleCat.{max u v} A) 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          localCohomologyWithSupportInPlus A T
            ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj
              (localCohomologyWithSupportInPlus A T' X q)) p)) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (K.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (K.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) := by
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let F := sectionsWithSupportInFunctor.{u, v} A T'
  let G := sectionsWithSupportInFunctor.{u, v} A T
  let : F.Additive := sectionsWithSupportInFunctor_additive A T'
  let : G.Additive := sectionsWithSupportInFunctor_additive A T
  let : (F ⋙ G).Additive := inferInstance
  let W := HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A)
  let Gplus := G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let : Gplus.HasPointwiseRightDerivedFunctor W :=
    (HomotopyCategory.Plus.localizerMorphism_derives Gplus).hasPointwiseRightDerivedFunctor
  let : Gplus.HasRightDerivedFunctor W :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor Gplus W
  have hFG : ∀ I : ModuleCat.{max u v} A, Injective I → G.rightAcyclic (F.obj I) := by
    intro I _
    let J : InjectiveObject (ModuleCat.{max u v} A) :=
      ⟨F.obj I, (Module.injective_iff_injective_object A _).1
        (sectionsWithSupportInFunctor_map_injective A T' I)⟩
    have hunit : IsIso ((Gplus.totalRightDerivedUnit DerivedCategory.Plus.Qh W).app
        (((InjectiveObject.ι (ModuleCat.{max u v} A)).mapHomotopyCategoryPlus).obj
          ((HomotopyCategory.Plus.singleFunctor
            (InjectiveObject (ModuleCat.{max u v} A)) 0).obj J))) :=
      (HomotopyCategory.Plus.localizerMorphism_derives Gplus).isIso_of_isRightDerivedFunctor _ _
    exact (NatTrans.isIso_app_iff_of_iso (Gplus.totalRightDerivedUnit DerivedCategory.Plus.Qh W)
      (mapHomotopyCategoryPlusObjSingleIso (InjectiveObject.ι _) 0 J)).1 hunit
  obtain ⟨K, hK, -, hRest⟩ :=
    CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp F G hFG X
  have := isRightDerivedFunctor_rightDerivedFunctorPlus (F ⋙ G)
  let H := sectionsWithSupportInFunctor.{u, v} A (T ∩ T')
  let : H.Additive := sectionsWithSupportInFunctor_additive A (T ∩ T')
  have := isRightDerivedFunctor_rightDerivedFunctorPlus H
  let τ : (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
    Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).symm.trans
        (Functor.mapHomotopyCategoryPlusCompIso (sectionsWithSupportInCompIso A T T')))
      DerivedCategory.Plus.Qh
  let e : (F ⋙ G).rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
    CategoryTheory.Functor.rightDerivedNatIso
      (F ⋙ G).rightDerivedFunctorPlus
      H.rightDerivedFunctorPlus
      ((F ⋙ G).rightDerivedFunctorPlusUnith)
      H.rightDerivedFunctorPlusUnith W τ
  refine ⟨K, fun n => ?_, hRest⟩
  obtain ⟨hn⟩ := hK n
  refine ⟨hn ≪≫ ?_⟩
  show _ ≅
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) n).obj
      ((sectionsWithSupportInFunctor.{u, v} A (T ∩ T')).rightDerivedFunctorPlus.obj X)
  exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) n).mapIso (e.app X)

end Stacks.LocalCohomology

end
