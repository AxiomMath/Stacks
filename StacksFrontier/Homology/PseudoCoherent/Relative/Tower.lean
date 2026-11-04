module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Relative.Locality
public import StacksFrontier.Homology.PseudoCoherent.Relative.TorIndependentBaseChange
public import StacksFrontier.Homology.Tor.DerivedTensorBoundedAbove
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Relative pseudo-coherence after derived extension of scalars along a tower

Let `R → A → B` be finite-type maps of commutative rings and suppose `B`, as a `B`-module, is
pseudo-coherent relative to `A`. Then derived extension of scalars from `A` to `B` carries
relative `m`-pseudo-coherence over `R` to relative `m`-pseudo-coherence over `R`, and likewise
for relative pseudo-coherence: the base is unchanged, only the ring over which the complex
lives moves up the tower.

## Main definitions

* `PseudoCoherence.derivedExtensionScalars`: derived extension of scalars along `A → B`, at the
  common universe of the rings and their modules.

## Main results

* `PseudoCoherence.derivedExtensionScalars_preserves_relativelyPseudoCoherent`: if `B` is
  pseudo-coherent relative to `A`, derived extension of scalars from `A` to `B` preserves relative
  `m`-pseudo-coherence and relative pseudo-coherence over `R`.

## References

* [The Stacks Project, Lemma 15.82.8 (067B)](https://stacks.math.columbia.edu/tag/067B)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Derived extension of scalars for rings and modules in one universe. -/
public noncomputable def derivedExtensionScalars {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (_hB : IsModuleRelativelyPseudoCoherent (R := A) (A := B) B) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor

private lemma isPseudoCoherentFrom_of_isLE {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{u} R)) (m : ℤ) [K.IsLE (m - 1)] :
    IsPseudoCoherentFrom K m := by
  refine ⟨0, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, ?_⟩, 0, ?_, ?_⟩
  · intro i
    have : Subsingleton ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero _))
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩
  · intro i hi
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map_isZero
      (DerivedCategory.Q.map_isZero (isZero_zero _))).isIso
      (DerivedCategory.isZero_of_isLE K (m - 1) i (by lia)) _
  · exact (DerivedCategory.isZero_of_isLE K (m - 1) m (by lia)).epi _

/-- A zero object of the derived category is pseudo-coherent from any degree. -/
private lemma isPseudoCoherentFrom_of_isZero {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : IsZero K) (m : ℤ) :
    IsPseudoCoherentFrom K m :=
  have : K.IsLE (m - 1) :=
    (DerivedCategory.isLE_iff _ _).2 fun i _ ↦ (DerivedCategory.homologyFunctor _ i).map_isZero hK
  isPseudoCoherentFrom_of_isLE _ m

private lemma isRelativelyPseudoCoherentFrom_of_isZero
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsZero K) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m := by
  intro n f hf
  exact isPseudoCoherentFrom_of_isZero
    ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.map_isZero hK) m

private lemma isRelativelyPseudoCoherentFrom_of_iso
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    {K L : DerivedCategory (ModuleCat.{u} A)} {m : ℤ}
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) (e : K ≅ L) :
    IsRelativelyPseudoCoherentFrom (R := R) L m := by
  intro n f hf
  exact isPseudoCoherentFrom_of_iso (hK n f hf)
    ((ModuleCat.restrictScalars f.toRingHom).mapDerivedCategory.mapIso e)

section Truncation

variable {R : Type u} [Ring R]

private lemma exists_distinguished_single_stupidTrunc
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    ∃ (f : (DerivedCategory.singleFunctor (ModuleCat.{u} R) b).obj (L.X b) ⟶
        DerivedCategory.Q.obj L)
      (g : DerivedCategory.Q.obj L ⟶
        DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))))
      (h : DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) b).obj (L.X b))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles := by
  obtain ⟨ι, hιb⟩ := DerivedCategory.exists_hom_from_single_isIso_f L b
  obtain ⟨π, hπ⟩ := DerivedCategory.exists_hom_to_stupidTrunc_isIso_f L b
  have hMb : IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))).X b) :=
    DerivedCategory.isZero_stupidTrunc_X_of_lt L (by lia)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi
      exact hMb.eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  have hSE : (ShortComplex.mk ι π hcomp).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    by_cases hi : i = b
    · subst hi
      exact ShortComplex.shortExact_of_isIso_f_of_isZero_X₃ _ hιb hMb
    · exact ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) b (L.X b) i hi) (hπ i hi)
  exact ⟨_, _, _, Pretriangulated.mk_mem_distTriang_of_iso _
    (DerivedCategory.triangleOfSES_distinguished hSE)
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) b).app (L.X b))⟩


private lemma boundedFiniteFreeShift
    {E : CochainComplex (ModuleCat.{u} R) ℤ} (hE : IsBoundedFiniteFree E) (n : ℤ) :
    IsBoundedFiniteFree (E⟦n⟧) := by
  obtain ⟨a, ha⟩ := hE.lowerBound
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨⟨a - n, ?_⟩, ⟨b - n, ?_⟩, ?_⟩
  · exact CochainComplex.isStrictlyGE_shift E a n (a - n) (by ring)
  · exact CochainComplex.isStrictlyLE_shift E b n (b - n) (by ring)
  · intro i
    rw [show ((shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj E).X i =
      E.X (i + n) from rfl]
    exact hE.finiteFree (i + n)

private alias epiMapIffOfNatIso := StacksDraft.PseudoCoherence.epi_map_iff_of_natIso

private noncomputable def homologyShiftIso (n i : ℤ) :
    shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n + i) :=
  Functor.ShiftSequence.shiftIso
    (F := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0) n i (n + i) rfl

private lemma pseudoCoherentShift {K : DerivedCategory (ModuleCat.{u} R)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) (n : ℤ) :
    IsPseudoCoherentFrom (K⟦n⟧) (m - n) := by
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  refine ⟨E⟦n⟧, boundedFiniteFreeShift hE n,
    ((DerivedCategory.Q).commShiftIso n).hom.app E ≫ (α⟦n⟧'), ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp]
    have h : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map (α⟦n⟧')) := by
      rw [show (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map (α⟦n⟧') =
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map α from rfl,
        NatIso.isIso_map_iff (homologyShiftIso n i) α]
      exact hiso (n + i) (by lia)
    exact IsIso.comp_isIso
  · rw [Functor.map_comp]
    have h : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (m - n)).map (α⟦n⟧')) := by
      rwa [show (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (m - n)).map (α⟦n⟧') =
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R) (m - n)).map α from rfl,
        epiMapIffOfNatIso (homologyShiftIso n (m - n)) α, show n + (m - n) = m from by ring]
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (m - n)).map
        (((DerivedCategory.Q).commShiftIso n).hom.app E)) := IsIso.epi_of_iso _
    exact epi_comp _ _

private lemma isPseudoCoherentFrom_map_of_boundedAbove
    {S : Type u} [Ring S]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (a : ℤ) (hF : ∀ (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ),
      X.IsLE n → (F.obj X).IsLE (n + a))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b m : ℤ) [K.IsStrictlyLE b]
    (hterms : ∀ i : ℤ, IsPseudoCoherentFrom
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) i).obj (K.X i))) m) :
    IsPseudoCoherentFrom (F.obj (DerivedCategory.Q.obj K)) m := by
  have hz (M : ModuleCat.{u} R) (i : ℤ) (hM : IsZero M) :
      IsPseudoCoherentFrom
        (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) i).obj M)) m :=
    isPseudoCoherentFrom_of_isZero
      (F.map_isZero ((DerivedCategory.singleFunctor _ i).map_isZero hM)) m
  have aux : ∀ (n : ℕ) (L : CochainComplex (ModuleCat.{u} R) ℤ),
      L.IsStrictlyLE (m - 1 - a + n) →
      (∀ i : ℤ, IsPseudoCoherentFrom
        (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) i).obj (L.X i))) m) →
      IsPseudoCoherentFrom (F.obj (DerivedCategory.Q.obj L)) m := by
    intro n
    induction n with
    | zero =>
        intro L hL _
        have : L.IsStrictlyLE (m - 1 - a) := by simpa using hL
        have : (F.obj (DerivedCategory.Q.obj L)).IsLE (m - 1) := by
          convert hF (DerivedCategory.Q.obj L) (m - 1 - a) inferInstance using 1
          ring
        exact isPseudoCoherentFrom_of_isLE _ m
    | succ n ih =>
        intro L hL hterms
        let c : ℤ := m - 1 - a + (n + 1 : ℕ)
        have : L.IsStrictlyLE c := hL
        obtain ⟨f, g, h, hT⟩ := exists_distinguished_single_stupidTrunc L c
        let L' : CochainComplex (ModuleCat.{u} R) ℤ :=
          L.stupidTrunc (ComplexShape.embeddingUpIntLE (c - 1))
        have hL' : L'.IsStrictlyLE (m - 1 - a + n) := by
          rw [CochainComplex.isStrictlyLE_iff]
          intro i hi
          exact DerivedCategory.isZero_stupidTrunc_X_of_lt L (by dsimp [c]; lia)
        have hterms' : ∀ i : ℤ, IsPseudoCoherentFrom
            (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) i).obj (L'.X i))) m := by
          intro i
          by_cases hi : i ≤ c - 1
          · exact isPseudoCoherentFrom_of_iso (hterms i)
              (F.mapIso ((DerivedCategory.singleFunctor _ i).mapIso
                (L.stupidTruncXIso _
                  (DerivedCategory.embeddingUpIntLE_f_toNat (c - 1) i hi)).symm))
          · exact hz (L'.X i) i (DerivedCategory.isZero_stupidTrunc_X_of_lt L (by lia))
        exact PseudoCoherence.isPseudoCoherent_of_distinguished_two m
          (F.mapTriangle.obj (Triangle.mk f g h)) (F.map_distinguished _ hT)
          (hterms c) (ih L' hL' hterms')
  let n := (b - (m - 1 - a)).toNat
  have hn : b ≤ m - 1 - a + n := by dsimp [n]; lia
  have hK : K.IsStrictlyLE (m - 1 - a + n) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact K.isZero_of_isStrictlyLE b i (by lia)
  exact aux n K hK hterms

private lemma isPseudoCoherentFrom_map_finiteFree
    {S : Type u} [Ring S]
    (F : ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} S)) [F.Additive]
    (m : ℤ) (hF : IsPseudoCoherentFrom (F.obj (ModuleCat.of R (ULift.{u} R))) m)
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Free R M] :
    IsPseudoCoherentFrom (F.obj M) m := by
  classical
  let motive (N : Type u) [AddCommGroup N] [Module R N] : Prop :=
    IsPseudoCoherentFrom (F.obj (ModuleCat.of R N)) m
  have he : ∀ {N N' : Type u} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive N' := by
    intro N N' _ _ _ _ e h
    exact isPseudoCoherentFrom_of_iso h (F.mapIso e.toModuleIso)
  have hzero : motive PUnit := by
    exact isPseudoCoherentFrom_of_isZero
      (F.map_isZero (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit))) m
  have hprod : ∀ {N N' : Type u} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], motive N → motive N' → motive (N × N') := by
    intro N N' _ _ _ _ hN hN'
    let X := ModuleCat.of R N
    let Y := ModuleCat.of R N'
    let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
    let : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBiproducts F
    have hsum := PseudoCoherence.isPseudoCoherent_of_distinguished_two m
      (binaryBiproductTriangle (F.obj X) (F.obj Y))
      (binaryBiproductTriangle_distinguished _ _) hN hN'
    exact isPseudoCoherentFrom_of_iso hsum
      ((F.mapBiprod X Y).symm ≪≫ F.mapIso (ModuleCat.biprodIsoProd X Y))
  let I := Module.Free.ChooseBasisIndex R M
  have hpi : motive (I → ULift.{u} R) :=
    Module.pi_induction' R motive motive he he hzero hprod (fun _ : I ↦ ULift.{u} R)
      (fun _ ↦ hF)
  let e : M ≃ₗ[R] (I → ULift.{u} R) :=
    (Module.Free.chooseBasis R M).equivFun.trans
      (LinearEquiv.piCongrRight fun _ ↦ (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm)
  exact he e.symm hpi

private lemma isPseudoCoherentFrom_map_of_modulePseudoCoherent
    {S : Type u} [Ring S]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (a m : ℤ) (hF : ∀ (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ),
      X.IsLE n → (F.obj X).IsLE (n + a))
    (hunit : IsPseudoCoherentFrom
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} R)))) m)
    (M : ModuleCat.{u} R) (hM : ∀ q : ℤ, IsModulePseudoCoherentFrom (R := R) M q) :
    IsPseudoCoherentFrom
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) m := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hMX : IsPseudoCoherent X :=
    (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective X 0).1.mpr hM
  obtain ⟨E, α, hE, hE0, hα⟩ :=
    (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective X 0).2.2
      hMX (fun i hi ↦ DerivedCategory.isZero_of_isLE X 0 i hi)
  have hFE : IsPseudoCoherentFrom (F.obj (DerivedCategory.Q.obj E)) m := by
    apply isPseudoCoherentFrom_map_of_boundedAbove F a hF E 0 m
    intro i
    by_cases hi : i ≤ 0
    · have := (hE i).1
      have := (hE i).2
      have hsingle := isPseudoCoherentFrom_map_finiteFree
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ F) m hunit (E.X i)
      have hshift : IsPseudoCoherentFrom
          ((F.obj ((DerivedCategory.singleFunctor _ 0).obj (E.X i)))⟦-i⟧) (m + i) := by
        simpa only [sub_neg_eq_add, Functor.comp_obj] using pseudoCoherentShift hsingle (-i)
      have hshift' : IsPseudoCoherentFrom
          ((F.obj ((DerivedCategory.singleFunctor _ 0).obj (E.X i)))⟦-i⟧) m := by
        obtain ⟨P, hP, β, hβ, hβm⟩ := hshift
        refine ⟨P, hP, β, fun j hj ↦ hβ j (by lia), ?_⟩
        by_cases hi0 : i = 0
        · rwa [show m + i = m by lia] at hβm
        · have := hβ m (by lia)
          infer_instance
      exact isPseudoCoherentFrom_of_iso hshift'
        ((F.commShiftIso (-i)).symm.app _ ≪≫
          F.mapIso (((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
            (-i) i 0 (by lia)).app (E.X i)))
    · exact isPseudoCoherentFrom_of_isZero
        (F.map_isZero ((DerivedCategory.singleFunctor _ i).map_isZero
          (E.isZero_of_isStrictlyLE 0 i (by lia)))) m
  exact isPseudoCoherentFrom_of_iso hFE (F.mapIso (asIso α))

end Truncation

section Tensor

open CategoryTheory.MonoidalCategory CochainComplex.DerivedTensor

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

private lemma exists_projective_representative
    {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [K.IsLE a] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, Projective (P.X i)) ∧ P.IsStrictlyLE a ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨L, e, hL⟩ := ‹K.IsLE a›
  let W : ObjectProperty (ModuleCat.{u} R) := fun X ↦ Projective X
  let : W.ContainsZero := ⟨ModuleCat.of R (Fin 0 → R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  obtain ⟨P, f, -, hf, hP, hPa⟩ := (CochainComplex.exists_quasiIso_prop W
    (fun X ↦ ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩) a).1 L
  exact ⟨P, hP, hPa, ⟨e ≪≫ (asIso (DerivedCategory.Q.map f)).symm⟩⟩


private lemma derivedTensorProduct_obj_iso_tensor
    {R : Type u} [CommRing R]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (eP : K ≅ DerivedCategory.Q.obj P) (eQ : L ≅ DerivedCategory.Q.obj Q)
    (hQ : Q.KFlat) :
    Nonempty ((derivedTensorProduct L).obj K ≅
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q)) := by
  have eQ' : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q) ≅ L :=
    (DerivedCategory.quotientCompQhIso _).app Q ≪≫ eQ.symm
  obtain ⟨e⟩ := (derivedTensorProduct_iso_lift_of_kFlat_resolution L Q Q
    (𝟙 Q) hQ eQ').1
  exact ⟨(derivedTensorProduct L).mapIso
      (eP ≪≫ ((DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
    e.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app (HomologicalComplex.tensorObj P Q)⟩

/-- The derived tensor product of an object of `D^{≤ a}` with an object of `D^{≤ b}` lies in
`D^{≤ a + b}`, with no lower bound on either factor. -/
@[sga "6 I 2.16" "special case", sga "6 III 1.11" "Part (a), special case"]
private lemma derivedTensorProduct_isLE
    {R : Type u} [CommRing R]
    (K L : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] : ((derivedTensorProduct L).obj K).IsLE (a + b) :=
  CochainComplex.DerivedTensor.isLE_of_kFlatComparison.{u, u}
    ((derivedTensorProduct L).obj K) K L a b
    fun P Q eP eQ _ hQ => derivedTensorProduct_obj_iso_tensor K L P Q eP eQ hQ


set_option backward.isDefEq.respectTransparency false in
private theorem isZero_tensorSingle_summand {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₂ : ℤ) (h : i₁ ≠ 0) :
    Limits.IsZero
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X)
          (i₁, i₂)) := by
  have hz : Limits.IsZero
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X i₁) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N i₁ h
  show Limits.IsZero (((curriedTensor (ModuleCat.{u} R)).obj
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X i₁)).obj (C.X i₂))
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
  exact (Unique.instSubsingleton : Subsingleton (TensorProduct R
      (↥(((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X i₁)) (↥(C.X i₂))))


set_option backward.isDefEq.respectTransparency false in
private theorem tensorSingle_surviving_summand {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ)
    (b : ↑((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j})) (hi : b.1.1 = 0) :
    (((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X).mapObjFun
        (fun x => x.1 + x.2) j b
    = (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X j := by
  obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
  simp only at hi
  subst hi
  have : i₂ = j := by lia
  subst this
  rfl


set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorSingleXIso {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).obj
        C).X j
      ≅ (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X
        j := by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{u} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X
  let RHS : ModuleCat.{u} R := (((tensorLeft N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).X j
  have iLHS : IsColimit (Z.cofanMapObj p j) := Z.isColimitCofanMapObj p j
  have h0 : p (0, j) = j := by change (0:ℤ) + j = j; ring
  let injFn : (b : ↑(p ⁻¹' {j})) → Z.mapObjFun p j b ⟶ RHS :=
    fun b => if hi : b.1.1 = 0 then eqToHom (tensorSingle_surviving_summand N C j b hi) else 0
  refine
    { hom := Cofan.IsColimit.desc iLHS injFn
      inv := Z.ιMapObj p (0, j) j h0
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Cofan.IsColimit.hom_ext iLHS
    intro b
    rw [← Category.assoc, Cofan.IsColimit.fac iLHS injFn b]
    erw [Category.comp_id]
    by_cases hi : b.1.1 = 0
    · obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
      dsimp only [p] at hb
      simp only at hi
      subst hi
      have hj : i₂ = j := by lia
      subst hj
      change injFn ⟨(0,i₂), _⟩ ≫ Z.ιMapObj p (0, i₂) i₂ h0 = (Z.cofanMapObj p i₂).inj ⟨(0,i₂), _⟩
      simp only [injFn, dite_eq_left]
      rw [show (eqToHom (tensorSingle_surviving_summand N C i₂ ⟨(0,i₂), hb⟩ rfl)) = 𝟙 _ from rfl,
          Category.id_comp]
      rfl
    · exact (isZero_tensorSingle_summand N C b.1.1 b.1.2 hi).eq_of_src _ _
  · rw [show Z.ιMapObj p (0, j) j h0 = (Z.cofanMapObj p j).inj ⟨(0,j), h0⟩ from rfl,
      Cofan.IsColimit.fac iLHS injFn ⟨(0,j), h0⟩]
    change injFn ⟨(0,j), h0⟩ = 𝟙 RHS
    simp only [injFn, dite_eq_left]
    rfl


set_option backward.isDefEq.respectTransparency false in
private theorem tensorSingleXIso_hom_comm {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensorSingleXIso N C i).hom ≫ (((tensorLeft N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).d i j
      = ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          N)).obj C).d i j
        ≫ (tensorSingleXIso N C j).hom := by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{u} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X
  have iLHS : IsColimit (Z.cofanMapObj p i) := Z.isColimitCofanMapObj p i
  apply Cofan.IsColimit.hom_ext iLHS
  intro b
  by_cases hi : b.1.1 = 0
  · obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    dsimp only [p] at hb
    simp only at hi
    subst hi
    have hi2 : i₂ = i := by lia
    subst hi2
    have hjv : i₂ + 1 = j := hij
    subst hjv
    rw [← Category.assoc]
    have hL : (Z.cofanMapObj p i₂).inj ⟨(0,i₂), hb⟩ ≫ (tensorSingleXIso N C i₂).hom = 𝟙 _ := by
      have he : (Z.cofanMapObj p i₂).inj ⟨(0,i₂), hb⟩ = (tensorSingleXIso N C i₂).inv := rfl
      rw [he]; exact (tensorSingleXIso N C i₂).inv_hom_id
    rw [hL, Category.id_comp, ← Category.assoc]
    have hR : (Z.cofanMapObj p i₂).inj ⟨(0,i₂), hb⟩
        ≫ ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            N)).obj C).d i₂ (i₂+1)
      = HomologicalComplex.ιMapBifunctor
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) C
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) 0 i₂ i₂ hb
        ≫ (HomologicalComplex.mapBifunctor
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) C
            (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).d i₂ (i₂+1) :=
                rfl
    rw [hR]
    have hrel1 : (ComplexShape.up ℤ).Rel (0:ℤ) 1 := by change (0:ℤ)+1 = 1; ring
    have hrel2 : (ComplexShape.up ℤ).Rel i₂ (i₂+1) := by change i₂+1 = i₂+1; ring
    have hπ1 :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ((0:ℤ)+1, i₂) = i₂+1 := by
      show (1:ℤ) + i₂ = i₂+1; ring
    have hπ2 :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ((0:ℤ), i₂+1) = i₂+1 := by
      show (0:ℤ) + (i₂+1) = i₂+1; ring
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hrel1 i₂ (i₂+1) hπ1,
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 hrel2 (i₂+1) hπ2,
        CochainComplex.singleFunctor_obj_d N 0 0 1]
    simp only [Functor.map_zero, Limits.zero_app, Limits.zero_comp, smul_zero, zero_add]
    rw [show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, i₂) = 1 from rfl,
        one_smul, Category.assoc,
        show HomologicalComplex.ιMapBifunctor
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) C
            (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) 0 (i₂+1) (i₂+1) hπ2
          ≫ (tensorSingleXIso N C (i₂+1)).hom = 𝟙 _ from (tensorSingleXIso N C (i₂+1)).inv_hom_id,
        Category.comp_id]
    rfl
  · exact (isZero_tensorSingle_summand N C b.1.1 b.1.2 hi).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSingleIso {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    Nonempty ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        N)).obj C
      ≅ ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  ⟨HomologicalComplex.Hom.isoOfComponents (fun j => tensorSingleXIso N C j)
    (fun i j hij => tensorSingleXIso_hom_comm N C i j hij)⟩


private lemma derivedTensorProduct_unit_iso
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [K.IsLE a] :
    Nonempty ((derivedTensorProduct K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} R))) ≅ K) := by
  obtain ⟨P, hP, hPa, ⟨eP⟩⟩ := exists_projective_representative K a
  have : ∀ i, Module.Flat R (P.X i) := fun i ↦ by
    have := hP i
    infer_instance
  let U := HomologicalComplex.tensorUnit (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let eU : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (ULift.{u} R)) ≅ DerivedCategory.Q.obj U :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
      (ModuleCat.of R (ULift.{u} R))
  obtain ⟨e⟩ := derivedTensorProduct_obj_iso_tensor _ K U P eU eP
    (CochainComplex.KFlat.kFlat_of_flat P a)
  exact ⟨e ≪≫ DerivedCategory.Q.mapIso (HomologicalComplex.leftUnitor P) ≪≫ eP.symm⟩

private lemma mapDerivedCategory_isLE
    {R : Type u} {S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [K.IsLE a] :
    (F.mapDerivedCategory.obj K).IsLE a := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isLE K a i hi)).of_iso
    ((mapDerivedCategoryHomologyIso F i).app K)

private lemma isPseudoCoherentFrom_restrictScalars_derivedTensorProduct
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : S →+* R)
    (K : DerivedCategory (ModuleCat.{u} R)) (a m : ℤ) [K.IsLE a]
    (hK : IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) m)
    (M : ModuleCat.{u} R)
    (hM : ∀ q : ℤ, IsModulePseudoCoherentFrom (R := R) M q) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
      ((derivedTensorProduct K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) m := by
  let G := ModuleCat.restrictScalars.{u} f
  let F := derivedTensorProduct K ⋙ G.mapDerivedCategory
  have hF (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) (hn : X.IsLE n) :
      (F.obj X).IsLE (n + a) := by
    have := derivedTensorProduct_isLE X K n a
    exact mapDerivedCategory_isLE G _ (n + a)
  obtain ⟨e⟩ := derivedTensorProduct_unit_iso K a
  have hunit := isPseudoCoherentFrom_of_iso hK (G.mapDerivedCategory.mapIso e.symm)
  exact isPseudoCoherentFrom_map_of_modulePseudoCoherent F a m hF hunit M hM

set_option backward.isDefEq.respectTransparency false in
private lemma derivedExtensionScalars_restrictIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ) [K.IsLE a] :
    Nonempty ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K) ≅
      (derivedTensorProduct K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))) := by
  let G := ModuleCat.restrictScalars.{u} f
  let E := ModuleCat.extendScalars.{u, u, u} f
  let : E.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  have : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits E; infer_instance)
  let M := G.obj (ModuleCat.of B B)
  let B' := (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B)
  let eM : M ≃ₗ[A] B' := LinearEquiv.refl A B'
  let e : tensorLeft M ≅ E ⋙ G := NatIso.ofComponents
    (fun N ↦ (TensorProduct.congr eM (LinearEquiv.refl A N)).toModuleIso)
    (by
      intro N N' g
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl)
  obtain ⟨P, hP, hPa, ⟨eP⟩⟩ := exists_projective_representative K a
  have : ∀ i, Module.Flat A (P.X i) := fun i ↦ by
    have := hP i
    infer_instance
  let D := derivedExtensionScalarsGeneral.{u, u, u} f
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P a
  let eL := G.mapDerivedCategory.mapIso
    (D.functor.mapIso eP ≪≫ asIso (D.comparison.app P)) ≪≫
      G.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  let V := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let eV : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M ≅
      DerivedCategory.Q.obj V :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M
  obtain ⟨eT⟩ := derivedTensorProduct_obj_iso_tensor _ K V P eV eP
    (CochainComplex.KFlat.kFlat_of_flat P a)
  obtain ⟨eS⟩ := tensorSingleIso M P
  let eR := eT ≪≫ DerivedCategory.Q.mapIso
    (eS ≪≫ (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ G))
        (ComplexShape.up ℤ)).symm.app P)
  exact ⟨eL ≪≫ eR.symm⟩

end Tensor

private lemma exists_isLE_of_isPseudoCoherentFrom
    {R : Type u} [Ring R] {K : DerivedCategory (ModuleCat.{u} R)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) : ∃ a : ℤ, K.IsLE a := by
  obtain ⟨E, hE, α, hα, -⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨max b m, (DerivedCategory.isLE_iff _ _).2 ?_⟩
  intro i hi
  have := hα i (lt_of_le_of_lt (le_max_right b m) hi)
  exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) b i
    (lt_of_le_of_lt (le_max_left b m) hi)).of_iso
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map α)).symm

private lemma isLE_of_restrictScalars
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ)
    [((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsLE a] : K.IsLE a := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  let G := ModuleCat.restrictScalars.{u} f
  have h := (DerivedCategory.isZero_of_isLE (G.mapDerivedCategory.obj K) a i hi).of_iso
    ((mapDerivedCategoryHomologyIso G i).app K).symm
  have hs := (ModuleCat.isZero_iff_subsingleton (M := G.obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))).mp h
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

private lemma exists_isLE_of_isRelativelyPseudoCoherentFrom
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    {K : DerivedCategory (ModuleCat.{u} A)} {m : ℤ}
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) : ∃ a : ℤ, K.IsLE a := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  obtain ⟨a, ha⟩ := exists_isLE_of_isPseudoCoherentFrom (hK n f hf)
  exact ⟨a, isLE_of_restrictScalars f.toRingHom K a⟩

private lemma derivedExtensionScalars_comp_obj
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B)
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [K.IsLE a] :
    Nonempty (((derivedExtensionScalarsGeneral.{u, u, u} g).functor.obj
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K)) ≅
        (derivedExtensionScalarsGeneral.{u, u, u} (g.comp f)).functor.obj K) := by
  obtain ⟨P, hP, hPa, ⟨eP⟩⟩ := exists_projective_representative K a
  let F := ModuleCat.extendScalars.{u, u, u} f
  let : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  have : F.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits F; infer_instance)
  let PA : CochainComplex (ModuleCat.{u} A) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : PA.IsStrictlyLE a := by dsimp [PA]; infer_instance
  let : Algebra R A := f.toAlgebra
  have : ∀ i, Projective (PA.X i) := fun i ↦ by
    have := hP i
    show Projective (ModuleCat.of A (TensorProduct R A (P.X i)))
    infer_instance
  let Df := derivedExtensionScalarsGeneral.{u, u, u} f
  let Dg := derivedExtensionScalarsGeneral.{u, u, u} g
  let Dh := derivedExtensionScalarsGeneral.{u, u, u} (g.comp f)
  have : IsIso (Df.comparison.app P) := Df.comparison_isIso_of_projective P a
  have hg : IsIso (Dg.comparison.app PA) := Dg.comparison_isIso_of_projective PA a
  let ePg := @asIso _ _ _ _ (Dg.comparison.app PA) hg
  have : IsIso (Dh.comparison.app P) := Dh.comparison_isIso_of_projective P a
  let e : extensionOfScalarsComplex.{u, u, u} (g.comp f) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplex.{u, u, u} g :=
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f g) (ComplexShape.up ℤ))
      DerivedCategory.Q
  exact ⟨Dg.functor.mapIso (Df.functor.mapIso eP ≪≫ asIso (Df.comparison.app P)) ≪≫
    ePg ≪≫ (e.app P).symm ≪≫
    (asIso (Dh.comparison.app P)).symm ≪≫ (Dh.functor.mapIso eP).symm⟩

private lemma isPseudoCoherentFrom_restrictScalars_derivedExtensionScalars
    {R : Type u} {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B)
    (K : DerivedCategory (ModuleCat.{u} A)) (a m : ℤ) [K.IsLE a]
    (hK : IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) m)
    (hB : ∀ q : ℤ, IsModulePseudoCoherentFrom (R := A)
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of B B)) q) :
    IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars (g.comp f)).mapDerivedCategory.obj
        ((derivedExtensionScalarsGeneral.{u, u, u} g).functor.obj K)) m := by
  obtain ⟨e⟩ := derivedExtensionScalars_restrictIso g K a
  exact isPseudoCoherentFrom_of_iso
    (isPseudoCoherentFrom_restrictScalars_derivedTensorProduct f K a m hK _ hB)
    (((ModuleCat.restrictScalars f).mapDerivedCategory.mapIso e).symm ≪≫
      (restrictScalarsDerivedCompIso f g _).symm)

private lemma isRelativelyPseudoCoherentFrom_restrictScalars_algEquiv
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (e : A ≃ₐ[R] B) (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    IsRelativelyPseudoCoherentFrom (R := R)
      ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).mapDerivedCategory.obj K) m := by
  intro n f hf
  exact isPseudoCoherentFrom_of_iso
    (hK n (e.toAlgHom.comp f) (e.surjective.comp hf))
    (restrictScalarsDerivedCompIso f.toRingHom e.toRingEquiv.toRingHom K)

private lemma isRelativelyPseudoCoherentFrom_derivedExtensionScalars_of_surjective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (g : A →ₐ[R] B) (hg : Function.Surjective g)
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m)
    (hB : ∀ q : ℤ, IsModulePseudoCoherentFrom (R := A)
      ((ModuleCat.restrictScalars g.toRingHom).obj (ModuleCat.of B B)) q) :
    IsRelativelyPseudoCoherentFrom (R := R)
      ((derivedExtensionScalarsGeneral.{u, u, u} g.toRingHom).functor.obj K) m := by
  obtain ⟨a, ha⟩ := exists_isLE_of_isRelativelyPseudoCoherentFrom hK
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  exact (isPseudoCoherentFrom_polynomialPresentation_independent _ m).1.mp
    ⟨n, g.comp f, hg.comp hf, isPseudoCoherentFrom_restrictScalars_derivedExtensionScalars
      f.toRingHom g.toRingHom K a m (hK n f hf) hB⟩

private lemma isRelativelyPseudoCoherentFrom_of_polynomial_base
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (k : ℕ) [Algebra (MvPolynomial (Fin k) R) B]
    [IsScalarTower R (MvPolynomial (Fin k) R) B]
    [Algebra.FiniteType (MvPolynomial (Fin k) R) B] [Algebra.FiniteType R B]
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom
      (R := MvPolynomial (Fin k) R) K m) :
    IsRelativelyPseudoCoherentFrom (R := R) K m := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType (MvPolynomial (Fin k) R) B)
  let e : MvPolynomial (Fin (n + k)) R ≃ₐ[R]
      MvPolynomial (Fin n) (MvPolynomial (Fin k) R) :=
    (MvPolynomial.renameEquiv R (finSumFinEquiv (m := n) (n := k)).symm).trans
      (MvPolynomial.sumAlgEquiv R (Fin n) (Fin k))
  let g := (f.restrictScalars R).comp e.toAlgHom
  exact (isPseudoCoherentFrom_polynomialPresentation_independent K m).1.mp
    ⟨n + k, g, hf.comp e.surjective, isPseudoCoherentFrom_of_iso
      (isPseudoCoherentFrom_restrictScalars_of_ringEquiv e.toRingEquiv _ m (hK n f hf))
      (restrictScalarsDerivedCompIso e.toRingEquiv.toRingHom f.toRingHom K).symm⟩

private lemma isModulePseudoCoherentFrom_restrictScalars_comp_ringEquiv
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) (M : ModuleCat.{u} T) (m : ℤ)
    (hM : IsModulePseudoCoherentFrom (R := S) ((ModuleCat.restrictScalars f).obj M) m) :
    IsModulePseudoCoherentFrom (R := R)
      ((ModuleCat.restrictScalars (f.comp e.toRingHom)).obj M) m := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} T) 0).obj M
  have hK := isPseudoCoherentFrom_of_iso hM
    (((ModuleCat.restrictScalars f).mapDerivedCategorySingleFunctor 0).app M).symm
  exact isPseudoCoherentFrom_of_iso (isPseudoCoherentFrom_restrictScalars_of_ringEquiv e _ m hK)
    ((restrictScalarsDerivedCompIso e.toRingHom f K).symm ≪≫
      ((ModuleCat.restrictScalars (f.comp e.toRingHom)).mapDerivedCategorySingleFunctor 0).app M)

private lemma torIndependent_polynomial
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    TorIndependent R A (MvPolynomial (Fin n) R) := by
  apply (torIndependent_iff_isZero_tor R A (MvPolynomial (Fin n) R)).2
  intro p hp
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact CategoryTheory.isZero_Tor_succ_of_projective _ _ _ p

open scoped TensorProduct in
private noncomputable def polynomialTensorAlgEquiv
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (k : ℕ) : (MvPolynomial (Fin k) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin k) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin k) R) A).trans
    ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin k) R A).restrictScalars R)

open scoped TensorProduct in
private noncomputable def polynomialTensorPresentation
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (k : ℕ) (β : MvPolynomial (Fin k) A →ₐ[A] B) :
    (MvPolynomial (Fin k) R ⊗[R] A) →ₐ[R] B :=
  (β.restrictScalars R).comp (polynomialTensorAlgEquiv (R := R) (A := A) k).toAlgHom

private lemma polynomialTensorPresentation_surjective
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (k : ℕ) (β : MvPolynomial (Fin k) A →ₐ[A] B) (hβ : Function.Surjective β) :
    Function.Surjective (polynomialTensorPresentation (R := R) k β) :=
  hβ.comp (polynomialTensorAlgEquiv (R := R) (A := A) k).surjective

open scoped TensorProduct in
private lemma polynomialTensorPresentation_comp_includeRight
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (k : ℕ) (β : MvPolynomial (Fin k) A →ₐ[A] B) :
    (polynomialTensorPresentation (R := R) k β).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R)
          (A := MvPolynomial (Fin k) R) (B := A)).toRingHom = algebraMap A B := by
  apply RingHom.ext
  intro a
  show β ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin k) R A)
    (algebraMap A (A ⊗[R] MvPolynomial (Fin k) R) a)) = _
  rw [AlgEquiv.commutes]
  exact β.commutes a

open scoped TensorProduct in
private lemma isModulePseudoCoherentFrom_polynomialTensorPresentation
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType A B]
    (k : ℕ) (β : MvPolynomial (Fin k) A →ₐ[A] B) (hβ : Function.Surjective β)
    (hB : IsModuleRelativelyPseudoCoherent (R := A) (A := B) B) (q : ℤ) :
    IsModulePseudoCoherentFrom (R := MvPolynomial (Fin k) R ⊗[R] A)
      ((ModuleCat.restrictScalars.{u}
        (polynomialTensorPresentation (R := R) k β).toRingHom).obj
          (ModuleCat.of B B)) q := by
  have hβB : IsModulePseudoCoherentFrom (R := MvPolynomial (Fin k) A)
      ((ModuleCat.restrictScalars.{u} β.toRingHom).obj (ModuleCat.of B B)) q :=
    isPseudoCoherentFrom_of_iso (hB q k β hβ)
      (((ModuleCat.restrictScalars.{u} β.toRingHom).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of B B))
  exact isModulePseudoCoherentFrom_restrictScalars_comp_ringEquiv
    (polynomialTensorAlgEquiv (R := R) (A := A) k).toRingEquiv
    β.toRingHom (ModuleCat.of B B) q hβB

open scoped TensorProduct in
private lemma isRelativelyPseudoCoherentFrom_derivedExtensionScalars_polynomialTensor
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    (k : ℕ) (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    IsRelativelyPseudoCoherentFrom (R := MvPolynomial (Fin k) R)
      ((derivedExtensionScalarsGeneral.{u, u, u}
        (Algebra.TensorProduct.includeRight (R := R)
          (A := MvPolynomial (Fin k) R) (B := A)).toRingHom).functor.obj K) m :=
  (derivedExtensionScalars_preserves_relativelyPseudoCoherent_of_torIndependent
    (R := R) (A := A) (R' := MvPolynomial (Fin k) R)
    K (torIndependent_polynomial (R := R) (A := A) k)).1 m hK

open scoped TensorProduct in
private lemma isRelativelyPseudoCoherentFrom_derivedExtensionScalars_polynomialTensor_quotient
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (k : ℕ) (g : (MvPolynomial (Fin k) R ⊗[R] A) →ₐ[R] B)
    (hg : Function.Surjective g)
    (L : DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin k) R ⊗[R] A)))
    (m : ℤ)
    (hL : IsRelativelyPseudoCoherentFrom (R := MvPolynomial (Fin k) R) L m)
    (hBC : ∀ q : ℤ, IsModulePseudoCoherentFrom (R := MvPolynomial (Fin k) R ⊗[R] A)
      ((ModuleCat.restrictScalars.{u} g.toRingHom).obj
        (ModuleCat.of B B)) q) :
    IsRelativelyPseudoCoherentFrom (R := R)
      ((derivedExtensionScalarsGeneral.{u, u, u} g.toRingHom).functor.obj L) m := by
  let R' := MvPolynomial (Fin k) R
  let C := R' ⊗[R] A
  let : Algebra R' B := (g.toRingHom.comp (algebraMap R' C)).toAlgebra
  let g' : C →ₐ[R'] B := { g.toRingHom with commutes' := fun _ ↦ rfl }
  have : IsScalarTower R R' B := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro r
    show algebraMap R B r = g (algebraMap R' C (algebraMap R R' r))
    rw [← IsScalarTower.algebraMap_apply R R' C, g.commutes])
  have : Algebra.FiniteType R' B := Algebra.FiniteType.of_surjective g' hg
  exact isRelativelyPseudoCoherentFrom_of_polynomial_base (R := R) (B := B) k _ m
    (isRelativelyPseudoCoherentFrom_derivedExtensionScalars_of_surjective
      (R := R') (A := C) (B := B) g' hg L m hL hBC)

open scoped TensorProduct in
private lemma isRelativelyPseudoCoherentFrom_derivedExtensionScalars_common
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B] [Algebra.FiniteType R B]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hB : IsModuleRelativelyPseudoCoherent (R := A) (A := B) B)
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    IsRelativelyPseudoCoherentFrom (R := R)
      ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor.obj K)
        m := by
  obtain ⟨k, β, hβ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let C := MvPolynomial (Fin k) R ⊗[R] A
  let g : C →ₐ[R] B := polynomialTensorPresentation (R := R) k β
  let f : A →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let L := (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K
  have hL : IsRelativelyPseudoCoherentFrom (R := MvPolynomial (Fin k) R) L m :=
    isRelativelyPseudoCoherentFrom_derivedExtensionScalars_polynomialTensor
      (R := R) (A := A) k K m hK
  have hRLB :=
    isRelativelyPseudoCoherentFrom_derivedExtensionScalars_polynomialTensor_quotient
      (R := R) (A := A) (B := B) k g
      (polynomialTensorPresentation_surjective (R := R) k β hβ) L m hL
      (isModulePseudoCoherentFrom_polynomialTensorPresentation
        (R := R) k β hβ hB)
  obtain ⟨a, ha⟩ := exists_isLE_of_isRelativelyPseudoCoherentFrom hK
  obtain ⟨ec⟩ := derivedExtensionScalars_comp_obj f g.toRingHom K a
  have hgf : g.toRingHom.comp f = algebraMap A B :=
    polynomialTensorPresentation_comp_includeRight (R := R) k β
  exact isRelativelyPseudoCoherentFrom_of_iso hRLB
    (ec ≪≫ eqToIso (congrArg (fun t : A →+* B ↦
      (derivedExtensionScalarsGeneral.{u, u, u} t).functor.obj K) hgf))

/-- If `B` is pseudo-coherent relative to `A`, derived extension of scalars from `A` to `B`
preserves relative `m`-pseudo-coherence and relative pseudo-coherence over the base ring `R`. -/
@[stacks 067B]
public theorem derivedExtensionScalars_preserves_relativelyPseudoCoherent
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hB : IsModuleRelativelyPseudoCoherent.{u}
      (R := A) (A := B) B) :
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
    (IsRelativelyPseudoCoherentFrom (R := R) K m →
      IsRelativelyPseudoCoherentFrom (R := R)
        ((derivedExtensionScalars hB).obj K) m) ∧
    (IsRelativelyPseudoCoherent (R := R) K →
      IsRelativelyPseudoCoherent (R := R)
        ((derivedExtensionScalars hB).obj K)) := by
  let : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
  exact ⟨fun hK ↦ isRelativelyPseudoCoherentFrom_derivedExtensionScalars_common K m hB hK,
    fun hK q ↦ isRelativelyPseudoCoherentFrom_derivedExtensionScalars_common K q hB (hK q)⟩

end PseudoCoherence
