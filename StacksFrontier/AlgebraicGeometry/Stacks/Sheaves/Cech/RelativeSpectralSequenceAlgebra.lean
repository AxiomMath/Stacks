module

public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Algebra.Homology.HomologicalBicomplex
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Algebra.Homology.SpectralSequence.Renumbering
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Statement
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Homology.Ext.DerivedCoyoneda
import StacksFrontier.Algebra.Homology.SpectralSequence.ExtBoundedConvergence

/-!
# Homological input for the relative Čech-to-cohomology spectral sequence

A functor out of an abelian category which carries a degreewise-injective resolution of each
object to a complex quasi-isomorphic to that object in degree zero produces a first-quadrant
cohomological spectral sequence: take an injective resolution of the object, apply the functor
in one direction and the resolution in the other, and read off the two filtrations of the
resulting double complex. This file assembles that spectral sequence, together with the
identification of sheaf cohomology as the homology of the derived sections of an injective
resolution, in a form that is independent of the Čech construction.

## Main definitions

* `Stacks.RelativeCech.sheafCohomologyIso` identifies the `n`-th sheaf cohomology of an abelian
  sheaf with the `n`-th homology of the complex obtained by applying global sections to an
  injective resolution.
* `Stacks.RelativeCech.mapInjectiveResolution` transports an injective resolution along a
  homology-preserving additive functor which preserves the injectivity of the resolution.
* `Stacks.RelativeCech.mapExtendIso` commutes an additive functor with the extension of an
  `ℕ`-indexed complex to a `ℤ`-indexed one.

## Main results

* `Stacks.RelativeCech.exists_spectralSequence_of_natFunctorResolution`: the first-quadrant
  spectral sequence attached to a functorial resolution and an injective resolution.
* `Stacks.RelativeCech.quasiIso_fromSingle₀_of_exact`: an exact augmented complex is a
  resolution.
* `Stacks.RelativeCech.quasiIso_map_of_injective`: an additive functor preserves
  quasi-isomorphisms between degreewise-injective complexes.
* `Stacks.RelativeCech.enoughInjectives_of_site_size`: a category of abelian sheaves on an
  essentially small site has enough injectives.
* `Stacks.RelativeCech.hasEqualizers_of_faithful_isFiberedInGroupoids`: a category fibred in
  groupoids over a category with equalizers, by a faithful functor, has equalizers.

## Implementation notes

The spectral sequence is produced from the first filtration of the total complex of the double
complex whose rows are the functorial resolution and whose columns come from the injective
resolution. Vanishing outside the first quadrant makes the total complex exist and the
filtration finite in each degree, which is what turns the abstract convergence statement into a
finite filtration of the abutment. Complexes indexed by `ℕ` are extended to `ℤ` so that the two
directions can be compared in a single bidegree lattice.

## References

* [Stacks Project, Tag 06XF](https://stacks.math.columbia.edu/tag/06XF)
* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
* [Stacks Project, Tag 06XA](https://stacks.math.columbia.edu/tag/06XA)
* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

/-- A category fibred in groupoids by a faithful functor over a category with equalizers has
equalizers: the lift of the equalizer of the images is an equalizer. -/
public lemma hasEqualizers_of_faithful_isFiberedInGroupoids
    {D E : Type*} [Category D] [Category E] (P : D ⥤ E) [P.Faithful]
    (hP : P.IsFiberedInGroupoids) [HasEqualizers E] : HasEqualizers D := by
  have : ∀ {A B : D} {g h : A ⟶ B}, HasLimit (parallelPair g h) := by
    intro A B g h
    obtain ⟨y, e, he⟩ := hP.exists_lift (equalizer.ι (P.map g) (P.map h)) A rfl
    have hy := IsHomLift.domain_eq P (equalizer.ι (P.map g) (P.map h)) e
    have hemap : P.map e = eqToHom hy ≫ equalizer.ι (P.map g) (P.map h) := by
      simpa using IsHomLift.fac' P (equalizer.ι (P.map g) (P.map h)) e
    have heq : e ≫ g = e ≫ h := by
      apply P.map_injective
      simp only [P.map_comp, hemap, Category.assoc]
      exact congrArg (eqToHom hy ≫ ·) (equalizer.condition (P.map g) (P.map h))
    let t := Fork.ofι e heq
    have hm : Mono (P.map e) := by
      rw [hemap]
      infer_instance
    have hc (s : Fork g h) : P.map s.ι ≫ P.map g = P.map s.ι ≫ P.map h := by
      rw [← P.map_comp, ← P.map_comp, s.condition]
    let b (s : Fork g h) := equalizer.lift (P.map s.ι) (hc s) ≫ eqToHom hy.symm
    have hb (s : Fork g h) : b s ≫ P.map e = P.map s.ι := by
      simp [b, hemap]
    choose l hl huniq using fun s : Fork g h => hP.unique_lift e s.ι (b s) (hb s)
    refine ⟨⟨⟨t, Fork.IsLimit.mk t l (fun s => (hl s).2) fun s m hms => ?_⟩⟩⟩
    apply P.map_injective
    apply (cancel_mono (P.map e)).mp
    change m ≫ e = s.ι at hms
    rw [← P.map_comp, ← P.map_comp, hms, (hl s).2]
  exact hasEqualizers_of_hasLimit_parallelPair D

/-- A monomorphism `ι : F ⟶ K⁰` whose cokernel pair with `d⁰` is exact, into a complex that is
exact in every positive degree, is a resolution of `F`. -/
public lemma quasiIso_fromSingle₀_of_exact
    {D : Type*} [Category D] [Abelian D] (K : CochainComplex D ℕ)
    {F : D} (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
    (hzero : (ShortComplex.mk ι (K.d 0 1) hι).Exact)
    (hpos : ∀ n, K.ExactAt (n + 1)) :
    QuasiIso ((K.fromSingle₀Equiv F).symm ⟨ι, hι⟩) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨hzero, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          show 𝟙 F ≫ ι = ((K.fromSingle₀Equiv F).symm ⟨ι, hι⟩).f 0 ≫ 𝟙 (K.X 0)
          rw [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
          simp)
        (by
          show 𝟙 (K.X 0) ≫ K.d 0 1 = K.d 0 1 ≫ 𝟙 (K.X 1)
          simp)
    all_goals first | rfl | exact K.shape 0 0 (by simp)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact hpos n
    · exact CochainComplex.exactAt_succ_single_obj _ _

/-- An additive functor preserves quasi-isomorphisms between degreewise-injective cochain
complexes, since such a quasi-isomorphism is a homotopy equivalence. -/
public lemma quasiIso_map_of_injective
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    (Γ : D ⥤ E) [Γ.Additive] {K L : CochainComplex D ℕ}
    [∀ n, Injective (K.X n)] [∀ n, Injective (L.X n)]
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso ((Γ.mapHomologicalComplex (.up ℕ)).map φ) := by
  obtain ⟨e, he⟩ := (CochainComplex.quasiIso_iff_of_injective φ).mp inferInstance
  rw [← he]
  exact (Γ.mapHomotopyEquiv e).quasiIso_hom

section SheafInjectives

universe u v a
/-- Abelian sheaves on a site, valued in a universe containing the objects and morphisms of the
site, form a Grothendieck abelian category and therefore have enough injectives. -/
public lemma enoughInjectives_of_site_size {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v a}] :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u v a}) := by
  let e := equivSmallModel.{max u v a} C
  have : e.symm.inverse.IsDenseSubsite J (e.inverse.inducedTopology J) :=
    inferInstanceAs (e.functor.IsDenseSubsite J (e.inverse.inducedTopology J))
  let : HasSheafify (e.inverse.inducedTopology J) AddCommGrpCat.{max u v a} :=
    e.symm.hasSheafify _ J _
  let : IsGrothendieckAbelian.{max u v a} (Sheaf J AddCommGrpCat.{max u v a}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v a, max u v a, v, (max u v a)+1, u}
      J AddCommGrpCat.{max u v a}
  infer_instance

end SheafInjectives

section ExtHomology

universe w

open Opposite CochainComplex.HomComplex

/-- Applying `Hom(X, -)` degreewise to a cochain complex gives the `Hom`-complex out of `X`
placed in degree zero. -/
public def homComplexSingleZeroIso
    {C : Type*} [Category C] [Abelian C] (X : C) (K : CochainComplex C ℤ) :
    ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AddEquiv.toAddCommGrpIso (Cochain.fromSingleEquiv (zero_add n)).symm)
    (fun i j h => by
      ext f
      symm
      change Cochain.fromSingleMk (f ≫ K.d i j) (zero_add j) =
        δ i j (Cochain.fromSingleMk f (zero_add i))
      exact (Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)).symm)
/-- `Extⁿ(X, Y)` is the `n`-th homology of `Hom(X, I⁻)` for an injective resolution `I` of
`Y`. -/
public def extAddEquivHomology
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (X Y : C) (I : InjectiveResolution Y) (n : ℕ) :
    Abelian.Ext X Y n ≃+
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex).homology (n : ℤ) :=
  I.extAddEquivCohomologyClass.trans ((homologyAddEquiv _ _ (n : ℤ)).symm.trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      (HomologicalComplex.homologyMapIso (homComplexSingleZeroIso X I.cochainComplex) n).symm))

end ExtHomology

section SheafCohomologyComparison

universe u v w a b

open Opposite

/-- The `n`-th sheaf cohomology of an abelian sheaf is the `n`-th homology of the complex
obtained by applying global sections to an injective resolution of the sheaf. -/
public def sheafCohomologyIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{a}]
    [HasExt.{b} (Sheaf J AddCommGrpCat.{a})]
    (F : Sheaf J AddCommGrpCat.{a}) (I : InjectiveResolution F) (n : ℕ) :
    (Sheaf.functorH J n).obj F ≅
      (((Sheaf.functorH J 0).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex).homology (n : ℤ) := by
  let T := (constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift ℤ))
  let K := ((preadditiveCoyoneda.obj (op T)).mapHomologicalComplex (.up ℤ)).obj
    I.cochainComplex
  let L := ((Sheaf.functorH J 0).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let e : ∀ i, K.X i ≃+ L.X i := fun i => Abelian.Ext.addEquiv₀.symm
  have he : ∀ i j (x : K.X i), e j ((K.d i j).hom x) = (L.d i j).hom (e i x) := by
    intro i j x
    apply Abelian.Ext.addEquiv₀.injective
    change Abelian.Ext.addEquiv₀ (e j (x ≫ I.cochainComplex.d i j)) =
      Abelian.Ext.addEquiv₀ (Sheaf.H.map (I.cochainComplex.d i j) 0 (e i x))
    exact (Abelian.Ext.addEquiv₀.apply_symm_apply (x ≫ I.cochainComplex.d i j)).trans
      ((congrArg (fun z => z ≫ I.cochainComplex.d i j)
        (Abelian.Ext.addEquiv₀.apply_symm_apply x)).symm.trans
          (Sheaf.H.addEquiv₀_map (I.cochainComplex.d i j) (e i x)).symm)
  exact ((extAddEquivHomology T F I n).trans
    (StacksDraft.DerivedCoyoneda.homologyAddEquivOfComponents K L e he n)).toAddCommGrpIso

end SheafCohomologyComparison

/-- An additive functor commutes with the extension of an `ℕ`-indexed cochain complex to a
`ℤ`-indexed one. This is `Stacks.DerivedIndexing.mapExtendIsoSymm` at the embedding `ℕ ↪ ℤ`. -/
public noncomputable def mapExtendIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat K

/-- The image of an injective resolution under a homology-preserving additive functor which
keeps the terms of the resolution injective is an injective resolution. -/
public def mapInjectiveResolution
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
    {F : D} (I : InjectiveResolution F)
    (hI : ∀ n, Injective (G.obj (I.cocomplex.X n))) :
    InjectiveResolution (G.obj F) where
  cocomplex := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective := hI
  ι := (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app F ≫
    (G.mapHomologicalComplex (.up ℕ)).map I.ι

section FilteredAbutment

open Opposite

private lemma hasPageInfinityAt_of_finite_page
    {A : Type*} [Category* A] [Abelian A] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence A r₀) (hr₀ : r₀ ≤ 1)
    (h : ∀ n : ℤ,
      {p : ℤ | ¬ IsZero ((E.page 1 hr₀).X (p, n - p))}.Finite)
    (p q : ℤ) : E.HasPageInfinityAt (p, q) := by
  obtain ⟨b₀, hb₀⟩ := (h (p + q - 1)).bddBelow
  obtain ⟨b₁, hb₁⟩ := (h (p + q + 1)).bddAbove
  have hmem (n i j : ℤ) (hij : i + j = n) (hn : ¬ IsZero ((E.page 1 hr₀).X (i, j))) :
      i ∈ {i : ℤ | ¬ IsZero ((E.page 1 hr₀).X (i, n - i))} := by
    simpa only [Set.mem_ofPred_eq, show n - i = j by omega] using hn
  refine ⟨⟨max 1 (p - b₀ + 1), by omega, ?_⟩,
    ⟨max 1 (b₁ - p + 1), by omega, ?_⟩⟩
  · intro r hr
    exact {
      le := by omega
      zero := by
        rintro ⟨p', q'⟩
        by_cases hrel : (ComplexShape.up' (⟨r, 1-r⟩ : ℤ × ℤ)).Rel (p', q') (p, q)
        · obtain ⟨rfl, rfl⟩ : p' = p-r ∧ q' = q+r-1 := by
            simp [ComplexShape.up'] at hrel
            omega
          have hz : IsZero ((E.page 1 hr₀).X (p-r, q+r-1)) := by
            by_contra hn
            have := hb₀ (hmem (p + q - 1) _ _ (by omega) hn)
            omega
          exact (SpectralSequence.isZero_page_of_le E hr₀ _ hz r
            (by omega) (by omega)).eq_of_src _ _
        · exact (E.page r).shape _ _ hrel }
  · intro r hr
    exact {
      le := by omega
      zero := by
        rintro ⟨p', q'⟩
        by_cases hrel : (ComplexShape.up' (⟨r, 1-r⟩ : ℤ × ℤ)).Rel (p, q) (p', q')
        · obtain ⟨rfl, rfl⟩ : p' = p+r ∧ q' = q-r+1 := by
            simp [ComplexShape.up'] at hrel
            omega
          have hz : IsZero ((E.page 1 hr₀).X (p+r, q-r+1)) := by
            by_contra hn
            have := hb₁ (hmem (p + q + 1) _ _ (by omega) hn)
            omega
          exact (SpectralSequence.isZero_page_of_le E hr₀ _ hz r
            (by omega) (by omega)).eq_of_tgt _ _
        · exact (E.page r).shape _ _ hrel }

private noncomputable def imagePrecompCokernelIso {C : Type*} [Category* C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cokernel (Subobject.ofLE (imageSubobject (f ≫ g)) (imageSubobject g)
      (imageSubobject_comp_le f g)) ≅ cokernel (image.preComp f g) := by
  let s := (imageSubobjectIso (f ≫ g)).hom ≫ image.ι (f ≫ g)
  let t := (imageSubobjectIso g).hom ≫ image.ι g
  let u := (imageSubobjectIso (f ≫ g)).hom ≫ image.preComp f g ≫
    (imageSubobjectIso g).inv
  have hs : Subobject.mk s = imageSubobject (f ≫ g) := by
    simp [s, imageSubobject_arrow]
  have ht : Subobject.mk t = imageSubobject g := by
    simp [t, imageSubobject_arrow]
  have hu : u ≫ t = s := by
    simp [u, t, s, Category.assoc]
  let e₀ := Classical.choose <| FilteredComplexSpectralSequence.exists_iso_cokernel_ofLE_of_eq
    (imageSubobject_comp_le f g) s t u hu hs.symm ht.symm
  have hsq : u ≫ (imageSubobjectIso g).hom =
      (imageSubobjectIso (f ≫ g)).hom ≫ image.preComp f g := by
    simp [u, Category.assoc]
  exact e₀ ≪≫ cokernel.mapIso u (image.preComp f g)
    (imageSubobjectIso (f ≫ g)) (imageSubobjectIso g) hsq

private alias nonempty_cokernel_sup_iso := Stacks.Injectives.nonempty_cokernel_sup_iso

private lemma nonempty_cokernel_inf_iso_of_le_sup {C : Type*} [Category* C] [Abelian C]
    {X : C} {U H A D Z : Subobject X} (hAU : A ≤ U) (hAD : A ≤ D) (hDA : D ≤ A ⊔ H)
    (hHU : H ⊓ U ≤ D) (hZ : Z = U ⊔ H) :
    Nonempty (cokernel (Subobject.ofLE (D ⊓ U) U inf_le_right) ≅
      cokernel (Subobject.ofLE ((A ⊔ H) ⊓ Z) Z inf_le_right)) := by
  subst hZ
  have hDU : D ⊓ U = (A ⊔ H) ⊓ U := by
    refine le_antisymm (inf_le_inf hDA le_rfl) (le_inf ?_ inf_le_right)
    rw [sup_inf_assoc_of_le _ hAU]
    exact sup_le hAD hHU
  have hstable : D ⊓ U ⊔ H = (A ⊔ H) ⊓ (U ⊔ H) := by
    rw [← inf_sup_assoc_of_le U (le_sup_right : H ≤ A ⊔ H), hDU]
  have hHU' : U ⊓ H ≤ D ⊓ U := by
    rw [inf_comm U H]
    exact le_inf hHU inf_le_right
  obtain ⟨e⟩ := nonempty_cokernel_sup_iso U (D ⊓ U) H inf_le_right hHU'
  exact ⟨e ≪≫ Subobject.cokernelOfLEIsoOfEq (sup_le_sup_right inf_le_right H) inf_le_right
    hstable rfl⟩

private lemma homologyMap_filtration_ι_comp
    {A : Type*} [Category A] [Abelian A] (N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    {p p' : ℤ} (hp : p ≤ p') (n : ℤ) :
    HomologicalComplex.homologyMap (N.filtration.diagram.map (homOfLE hp).op) n ≫
        HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n =
      HomologicalComplex.homologyMap (N.filtration.ι.app (op p')) n := by
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  exact N.filtration.diagram_map_comp_ι_app (homOfLE hp).op

private lemma imageSubobject_homologyMap_filtration_ι_le
    {A : Type*} [Category A] [Abelian A] (N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    {p p' : ℤ} (hp : p ≤ p') (n : ℤ) :
    imageSubobject (HomologicalComplex.homologyMap (N.filtration.ι.app (op p')) n) ≤
      imageSubobject (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n) := by
  rw [← homologyMap_filtration_ι_comp N hp n]
  exact imageSubobject_comp_le _ _

private lemma boundaries_eq_of_isIso_homologyMap
    {A : Type*} [Category A] [Abelian A] (N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (N.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((N.filtration.ι.app (op p)).f n))
    (S p n : ℤ) (hS : 1 ≤ S)
    [IsIso (HomologicalComplex.homologyMap (N.filtration.ι.app (op (p - S + 1))) n)] :
    FilteredComplexSpectralSequence.boundaries N.X F S p n =
      FilteredComplexSpectralSequence.cycles N.X F (S - 1) (p + 1) n ⊔
        (imageSubobject (N.X.d (n - 1) n) ⊓ F p n) := by
  have hsecond : (Subobject.exists (N.X.d (n - 1) n)).obj
      (FilteredComplexSpectralSequence.cycles N.X F (S - 1) (p - (S - 1)) (n - 1)) =
      F p n ⊓ (Subobject.exists (N.X.d (n - 1) n)).obj (F (p - S + 1) (n - 1)) := by
    rw [show p - (S - 1) = p - S + 1 by omega]
    dsimp only [FilteredComplexSpectralSequence.cycles]
    rw [show n - 1 + 1 = n by omega, show p - S + 1 + (S - 1) = p by omega,
      Regular.exists_inf_pullback_eq_exists_inf]
    simp [inf_comm]
  have hinf := CochainComplex.boundaries_inf_eq_of_mono_homologyMap N F hF p (p - S + 1) n
    (by omega)
  rw [show S = (S - 1) + 1 by omega, FilteredComplexSpectralSequence.boundaries_succ_eq,
    hsecond, show (S - 1) + 1 - 1 = S - 1 by omega, hinf]

private lemma nonempty_cokernel_boundaries_inf_cycles_iso
    {A : Type*} [Category A] [Abelian A] (N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (N.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((N.filtration.ι.app (op p)).f n))
    (S p n : ℤ) (hS : 1 ≤ S)
    [Mono (HomologicalComplex.homologyMap (N.filtration.ι.app (op (p + S))) (n + 1))]
    [IsIso (HomologicalComplex.homologyMap (N.filtration.ι.app (op (p - S + 1))) n)] :
    Nonempty (cokernel (Subobject.ofLE
        (FilteredComplexSpectralSequence.boundaries N.X F S p n ⊓
          FilteredComplexSpectralSequence.cycles N.X F S p n)
        (FilteredComplexSpectralSequence.cycles N.X F S p n) inf_le_right) ≅
      cokernel (Subobject.ofLE
        ((imageSubobject (N.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n) ⊓
          (kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n))
        (kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) inf_le_right)) := by
  let Z := FilteredComplexSpectralSequence.cycles N.X F
  let D := FilteredComplexSpectralSequence.boundaries N.X F
  let U := Z S p n
  let H := F (p + 1) n
  let A0 := imageSubobject (N.X.d (n - 1) n) ⊓ F p n
  have hcycleSup : U ⊔ H = kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n := by
    show F p n ⊓ (Subobject.pullback (N.X.d n (n + 1))).obj
      (F (p + S) (n + 1)) ⊔ F (p + 1) n = _
    exact CochainComplex.cycles_sup_eq_of_mono_homologyMap N F hF p (p + S) n (by omega)
  have hDformula : D S p n = Z (S - 1) (p + 1) n ⊔ A0 :=
    boundaries_eq_of_isIso_homologyMap N F hF S p n hS
  have hA0D : A0 ≤ D S p n := by
    rw [hDformula]
    exact le_sup_right
  have hDle : D S p n ≤ A0 ⊔ H := by
    rw [hDformula]
    exact sup_le ((FilteredComplexSpectralSequence.cycles_le_F N.X F (S - 1) (p + 1) n).trans
      le_sup_right) le_sup_left
  have hA0U : A0 ≤ U := by
    apply le_inf inf_le_right
    apply (CategoryTheory.Subobject.le_pullback_iff _ _ _).2
    have hzero : A0.arrow ≫ N.X.d n (n + 1) = 0 := by
      rw [← Subobject.ofLE_arrow inf_le_left,
        Category.assoc, imageSubobject_arrow_comp_eq_zero (N.X.d_comp_d _ _ _)]
      simp
    rw [hzero]
    exact Subobject.factors_zero
  have hHUle : H ⊓ U ≤ D S p n := by
    have hUpull : U ≤ (Subobject.pullback (N.X.d n (n + 1))).obj
        (F (p + S) (n + 1)) := by
      show Z S p n ≤ (Subobject.pullback (N.X.d n (n + 1))).obj
        (F (p + S) (n + 1))
      exact inf_le_right
    have hcycle : H ⊓ U ≤ Z (S - 1) (p + 1) n :=
      FilteredComplexSpectralSequence.le_cycles N.X F
        (by simp [H])
        (by simpa only [show p + 1 + (S - 1) = p + S by omega] using
          le_trans inf_le_right hUpull)
    dsimp only [D, Z]
    rw [show S = (S - 1) + 1 by omega,
      FilteredComplexSpectralSequence.boundaries_succ_eq]
    exact le_sup_of_le_left hcycle
  exact nonempty_cokernel_inf_iso_of_le_sup hA0U hA0D hDle hHUle hcycleSup.symm

private lemma nonempty_pageInfinity_iso_stable
    {A : Type*} [Category A] [Abelian A]
    (N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (hzeroN : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((N.filtration.obj (op p)).homology n))
    (hisoN : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n))
    (p q : ℤ) (h₀ : (CochainComplex.filteredSpectralSequence N).HasPageInfinityAt (p, q))
    (h₁ : ((CochainComplex.filteredSpectralSequence N).restrictPages 1
      (by omega)).HasPageInfinityAt (p, q)) :
    let F := CochainComplex.filtrationSubobject N
    let n := p + q
    Nonempty (((CochainComplex.filteredSpectralSequence N).restrictPages 1
        (by omega)).pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE
        ((imageSubobject (N.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n) ⊓
          (kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n))
        (kernelSubobject (N.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) inf_le_right)) := by
  intro F n
  let E0 := CochainComplex.filteredSpectralSequence N
  let E1 := E0.restrictPages 1 (by omega)
  have : E0.HasPageInfinityAt (p, q) := h₀
  have : E1.HasPageInfinityAt (p, q) := h₁
  let R := max (E0.rMin (p, q)) (E1.rMin (p, q))
  have hR0 : E0.rMin (p, q) ≤ R := le_max_left _ _
  have hR1 : E1.rMin (p, q) ≤ R := le_max_right _ _
  obtain ⟨b, hb⟩ := hzeroN (n + 1)
  obtain ⟨a, ha⟩ := hisoN n
  let S := max R (max (b - p) (p + 1 - a))
  have hS0 : E0.rMin (p, q) ≤ S := le_trans hR0 (le_max_left _ _)
  have hS1 : E1.rMin (p, q) ≤ S := le_trans hR1 (le_max_left _ _)
  have hSb : b ≤ p + S := by dsimp [S]; omega
  have hSa : p - S + 1 ≤ a := by dsimp [S]; omega
  have hSpos : 1 ≤ S := by
    have h : 1 ≤ E1.rMin (p, q) := by simpa using E1.LE_rMin (p, q)
    omega
  have : Mono (HomologicalComplex.homologyMap
      (N.filtration.ι.app (op (p + S))) (n + 1)) := (hb (p + S) hSb).mono _
  have : IsIso (HomologicalComplex.homologyMap
      (N.filtration.ι.app (op (p - S + 1))) n) := ha _ hSa
  obtain ⟨eStablePage⟩ :=
    nonempty_cokernel_boundaries_inf_cycles_iso N F (fun _ _ => rfl) S p n hSpos
  have hEStable : (E0.page S (by omega)).X (p, q) ≅
      cokernel (Subobject.ofLE (FilteredComplexSpectralSequence.boundaries N.X F S p n ⊓
        FilteredComplexSpectralSequence.cycles N.X F S p n)
        (FilteredComplexSpectralSequence.cycles N.X F S p n) inf_le_right) :=
    FilteredComplexSpectralSequence.eIso N.X F (CochainComplex.filtrationSubobject_antitone N)
      S p q n (by omega) rfl
  have hpageEq : (E1.page R ((E1.LE_rMin (p, q)).trans hR1)).X (p, q) =
      (E0.page R ((E0.LE_rMin (p, q)).trans hR0)).X (p, q) := rfl
  exact ⟨E1.pageInfinityIso (p, q) R ≪≫ eqToIso hpageEq ≪≫
    (E0.pageInfinityIso (p, q) R).symm ≪≫ E0.pageInfinityIso (p, q) S ≪≫ hEStable ≪≫
      eStablePage⟩

private lemma filteredSpectralSequence_abutsTo
    {A : Type*} [Category A] [Abelian A]
    (N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (hzeroN : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((N.filtration.obj (op p)).homology n))
    (hisoN : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n)) :
    Stacks.RelativeLeray.AbutsTo
      ((CochainComplex.filteredSpectralSequence N).restrictPages 1 (by omega))
      (fun n => N.X.homology n) := by
  let F := CochainComplex.filtrationSubobject N
  let Z := FilteredComplexSpectralSequence.cycles N.X F
  let D := FilteredComplexSpectralSequence.boundaries N.X F
  let FH : ∀ n p : ℤ, Subobject (N.X.homology n) := fun n p =>
    imageSubobject (HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n)
  let E0 := CochainComplex.filteredSpectralSequence N
  have hE (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) :
      (E0.page r (by omega)).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) := by
    subst hn
    exact FilteredComplexSpectralSequence.eIso N.X F
      (CochainComplex.filtrationSubobject_antitone N) r p q (p + q) (by omega) rfl
  obtain ⟨hpageFinite, hfinite, -, -, hcompat⟩ :=
    CochainComplex.isBounded_and_converges_of_eventually_isZero_of_eventually_isIso
      N F (fun _ _ => rfl) Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) FH
      (fun _ _ => rfl) E0 hE hzeroN hisoN
  let E1 := E0.restrictPages 1 (by omega)
  have hpageFinite1 : ∀ n : ℤ,
      {p : ℤ | ¬ IsZero ((E1.page 1).X (p, n - p))}.Finite := hpageFinite
  have hFHanti : ∀ n p p' : ℤ, p ≤ p' → FH n p' ≤ FH n p := fun n _ _ hp =>
    imageSubobject_homologyMap_filtration_ι_le N hp n
  have hInfinity0 (p q : ℤ) : E0.HasPageInfinityAt (p, q) :=
    hasPageInfinityAt_of_finite_page E0 (by omega) hpageFinite p q
  have hInfinity1 (p q : ℤ) : E1.HasPageInfinityAt (p, q) :=
    hasPageInfinityAt_of_finite_page E1 (by omega) hpageFinite1 p q
  refine ⟨hInfinity1, FH, hFHanti, hfinite, fun p q => ?_⟩
  let n := p + q
  let transition := HomologicalComplex.homologyMap
    (N.filtration.diagram.map (homOfLE (show p ≤ p + 1 by omega)).op) n
  let inclusion := HomologicalComplex.homologyMap (N.filtration.ι.app (op p)) n
  have hcomp : transition ≫ inclusion =
      HomologicalComplex.homologyMap (N.filtration.ι.app (op (p + 1))) n :=
    homologyMap_filtration_ι_comp N (show p ≤ p + 1 by omega) n
  let P := imageSubobject (transition ≫ inclusion)
  let Q := imageSubobject inclusion
  have hP' : P = FH n (p + 1) := by
    dsimp [P, FH]
    rw [hcomp]
  have hQ' : Q = FH n p := rfl
  have hPQ : P ≤ Q := imageSubobject_comp_le transition inclusion
  obtain ⟨_, _, eStable, -⟩ := hcompat p n
  obtain ⟨eInfinity⟩ :=
    nonempty_pageInfinity_iso_stable N hzeroN hisoN p q (hInfinity0 p q) (hInfinity1 p q)
  exact ⟨eInfinity ≪≫ eStable ≪≫ (imagePrecompCokernelIso transition inclusion).symm ≪≫
    Subobject.cokernelOfLEIsoOfEq hPQ (hFHanti n p (p + 1) (by omega)) hP' hQ'⟩

end FilteredAbutment

section FirstQuadrant

open Opposite

private lemma totalFiltration₁_eventually_isZero
    {A : Type*} [Category A] [Abelian A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((K.totalFiltration₁.filtration.obj (op p)).homology n) := by
  intro n
  refine ⟨n + 1, fun p hp => ?_⟩
  have he : K.totalProjector (fun i (_ : ℤ) => p ≤ i) n = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    rw [HomologicalComplex₂.ι_totalProjector, comp_zero]
    split_ifs with hi
    · exact (hK i j (Or.inr (by change i + j = n at hij; omega))).eq_of_src _ _
    · rfl
  apply ShortComplex.isZero_homology_of_isZero_X₂
  show IsZero (imageSubobject (K.totalProjector (fun i (_ : ℤ) => p ≤ i) n) : A)
  exact IsZero.of_mono_eq_zero _
    (zero_of_epi_comp _ ((imageSubobject_arrow_comp _).trans he))

private lemma totalFiltration₁_eventually_isIso
    {A : Type*} [Category A] [Abelian A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (K.totalFiltration₁.filtration.ι.app (op p)) n) := by
  intro n
  refine ⟨0, fun p hp => ?_⟩
  have hi (m : ℤ) : IsIso ((K.totalFiltration₁.filtration.ι.app (op p)).f m) := by
    have he : K.totalProjector (fun i (_ : ℤ) => p ≤ i) m = 𝟙 _ := by
      apply HomologicalComplex₂.total.hom_ext
      intro i j hij
      rw [HomologicalComplex₂.ι_totalProjector, Category.comp_id]
      split_ifs with hi
      · rfl
      · exact (hK i j (Or.inl (by omega))).eq_of_src _ _
    show IsIso (imageSubobject (K.totalProjector (fun i (_ : ℤ) => p ≤ i) m)).arrow
    have : Epi (imageSubobject (K.totalProjector (fun i (_ : ℤ) => p ≤ i) m)).arrow :=
      epi_of_epi_fac ((imageSubobject_arrow_comp _).trans he)
    exact isIso_of_mono_of_epi _
  have := HomologicalComplex.Hom.isIso_of_components
    (K.totalFiltration₁.filtration.ι.app (op p))
  infer_instance

private lemma exists_firstQuadrant_doubleComplex_spectralSequence
    {A : Type*} [Category A] [Abelian A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    ∃ E : CohomologicalSpectralSequence A 1,
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ (K.X p).homology q)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      Stacks.RelativeLeray.AbutsTo E (fun n => (K.total (.up ℤ)).homology n) := by
  let T := K.totalFiltration₁
  let F := CochainComplex.filtrationSubobject T
  let Z := FilteredComplexSpectralSequence.cycles T.X F
  let D := FilteredComplexSpectralSequence.boundaries T.X F
  let E := CochainComplex.filteredSpectralSequence T
  let e := FilteredComplexSpectralSequence.eIso T.X F
    (CochainComplex.filtrationSubobject_antitone T)
  have hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
      ∃ δ : (Z r p n : A) ⟶ (Z r (p + r) (n + 1) : A),
        δ ≫ (Z r (p + r) (n + 1)).arrow = (Z r p n).arrow ≫ T.X.d n (n + 1) ∧
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
            (e r p q n hr hn).inv ≫ (E.page r hr).d (p, q) (p + r, q - r + 1) =
          δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
              D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
            (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv := by
    intro r p q n hr hn
    refine ⟨FilteredComplexSpectralSequence.deltaCycles T.X F r p n,
      FilteredComplexSpectralSequence.deltaCycles_arrow T.X F r p n, ?_⟩
    subst hn
    rw [FilteredComplexSpectralSequence.spectralSequence_d,
      FilteredComplexSpectralSequence.eIso_inv_rfl, Category.id_comp,
      ← Category.assoc, FilteredComplexSpectralSequence.π_comp_pageMap, Category.assoc]
  obtain ⟨_, ⟨β, _⟩, _⟩ := K.exists_iso_pages_totalFiltration₁ F (fun _ _ => rfl)
    Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) E e hδ
  exact ⟨E.restrictPages 1 (by omega), fun p q => ⟨β p q⟩,
    fun p q hpq => (β p q).isZero_iff.mpr
      (ShortComplex.isZero_homology_of_isZero_X₂ _ (hK p q hpq)),
    filteredSpectralSequence_abutsTo T
      (totalFiltration₁_eventually_isZero K hK) (totalFiltration₁_eventually_isIso K hK)⟩

private lemma hasTotal_of_firstQuadrant
    {A : Type*} [Category A] [Abelian A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ))
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    K.HasTotal (.up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine ((Set.finite_Icc 0 n).image (fun i : ℤ => (i, n - i))).subset ?_
  rintro ⟨i, j⟩ ⟨hij, hne⟩
  change i + j = n at hij
  have hi : 0 ≤ i := by by_contra h; exact hne (hK i j (Or.inl (by omega)))
  have hj : 0 ≤ j := by by_contra h; exact hne (hK i j (Or.inr (by omega)))
  exact ⟨i, ⟨hi, by omega⟩, Prod.ext rfl (show n - i = j by omega)⟩

end FirstQuadrant

private lemma cokernel_mapSubobject_iso
    {A : Type*} [Category A] [Abelian A] {X Y : A} (e : X ≅ Y)
    (P Q : Subobject X) (h : P ≤ Q) :
    Nonempty (cokernel (Subobject.ofLE P Q h) ≅
      cokernel (Subobject.ofLE ((Subobject.map e.hom).obj P)
        ((Subobject.map e.hom).obj Q) ((Subobject.map e.hom).monotone h))) := by
  have hmk (R : Subobject X) :
      Subobject.mk (R.arrow ≫ e.hom) = (Subobject.map e.hom).obj R := by
    rw [← Subobject.map_mk, Subobject.mk_arrow]
  obtain ⟨i⟩ := FilteredComplexSpectralSequence.exists_iso_cokernel_ofLE_of_eq
    ((Subobject.map e.hom).monotone h) (P.arrow ≫ e.hom) (Q.arrow ≫ e.hom)
    (Subobject.ofLE P Q h) (by rw [← Category.assoc, Subobject.ofLE_arrow])
    (hmk P).symm (hmk Q).symm
  exact ⟨i.symm⟩

/-- Convergence of a spectral sequence transports along a degreewise isomorphism of the graded
abutment. -/
public lemma spectralSequence_abutsTo_of_iso
    {A : Type*} [Category A] [Abelian A] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence A r₀) {H H' : ℤ → A}
    (hE : Stacks.RelativeLeray.AbutsTo E H) (e : ∀ n, H n ≅ H' n) :
    Stacks.RelativeLeray.AbutsTo E H' := by
  obtain ⟨hinf, F, hF, hfin, he⟩ := hE
  let F' := fun n p => (Subobject.mapIsoToOrderIso (e n)) (F n p)
  have hF' : ∀ n, Antitone (F' n) := fun n =>
    (Subobject.mapIsoToOrderIso (e n)).monotone.comp_antitone (hF n)
  refine ⟨hinf, F', hF', ?_, ?_⟩
  · intro n
    obtain ⟨a, b, hab, ha, hb⟩ := hfin n
    refine ⟨a, b, hab, ?_, ?_⟩
    · dsimp [F']
      rw [ha]
      exact (Subobject.mapIsoToOrderIso (e n)).map_top
    · dsimp [F']
      rw [hb]
      exact (Subobject.mapIsoToOrderIso (e n)).map_bot
  · intro p q
    obtain ⟨i⟩ := he p q
    obtain ⟨j⟩ := cokernel_mapSubobject_iso (e (p + q))
      (F (p + q) (p + 1)) (F (p + q) p) (hF (p + q) (by omega))
    exact ⟨i ≪≫ j⟩

private lemma exists_spectralSequence_of_rowResolution
    {A : Type*} [Category A] [Abelian A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ))
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j))
    (C : CochainComplex A ℤ) [C.IsStrictlyGE 0]
    (α : StacksDraft.TotalComplexQuasiIso.singleRowZero C ⟶ K.flip)
    (hα : ∀ n, QuasiIso (α.f n)) :
    ∃ E : CohomologicalSpectralSequence A 1,
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ (K.X p).homology q)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      Stacks.RelativeLeray.AbutsTo E (fun n => C.homology n) := by
  let := hasTotal_of_firstQuadrant K hK
  let S := StacksDraft.TotalComplexQuasiIso.singleRowZero C
  have hS : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((S.X i).X j) := by
    rintro i j (hi | hj)
    · exact (HomologicalComplex.eval A (.up ℤ) j).map_isZero
        (StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X C 0 i hi)
    · exact StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X_X C i j hj
  let := hasTotal_of_firstQuadrant S hS
  have hneg (i : ℤ) (hi : i < 0) : IsZero (K.flip.X i) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    ext j
    exact (hK j i (Or.inr hi)).eq_of_src _ _
  have := StacksDraft.TotalComplexQuasiIso.quasiIso_total_map α 0
    (fun i j hj => hS i j (Or.inr hj))
    (fun i hi => StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X C 0 i hi)
    (fun i j hj => hK j i (Or.inl hj)) hneg hα
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleRowZeroUnit C
  let g : C ⟶ K.total (.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit C ≫
      HomologicalComplex₂.total.map α (.up ℤ) ≫ (K.totalFlipIso (.up ℤ)).hom
  have : QuasiIso g := inferInstance
  obtain ⟨E, hp, hq, ha⟩ := exists_firstQuadrant_doubleComplex_spectralSequence K hK
  exact ⟨E, hp, hq, spectralSequence_abutsTo_of_iso E ha fun n =>
    (asIso (HomologicalComplex.homologyMap g n)).symm⟩

private lemma exists_spectralSequence_of_functorResolution
    {D A : Type*} [Category D] [Abelian D] [Category A] [Abelian A]
    (Γ : D ⥤ A) [Γ.Additive] (R : D ⥤ CochainComplex A ℤ) [R.Additive]
    (α : Γ ⋙ HomologicalComplex.single A (.up ℤ) 0 ⟶ R)
    (hR : ∀ X i, i < 0 → IsZero ((R.obj X).X i))
    (I : CochainComplex D ℤ) [I.IsStrictlyGE 0]
    (hα : ∀ n, QuasiIso (α.app (I.X n))) :
    ∃ E : CohomologicalSpectralSequence A 1,
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅
        (((R ⋙ HomologicalComplex.eval A (.up ℤ) p).mapHomologicalComplex (.up ℤ)).obj
          I).homology q)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      Stacks.RelativeLeray.AbutsTo E
        (fun n => ((Γ.mapHomologicalComplex (.up ℤ)).obj I).homology n) := by
  let K := HomologicalComplex₂.flip ((R.mapHomologicalComplex (.up ℤ)).obj I)
  have hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j) := by
    rintro i j (hi | hj)
    · exact hR (I.X j) i hi
    · exact (HomologicalComplex.eval A (.up ℤ) i).map_isZero
        (R.map_isZero (CochainComplex.isZero_of_isStrictlyGE I 0 j hj))
  exact exists_spectralSequence_of_rowResolution K hK
    ((Γ.mapHomologicalComplex (.up ℤ)).obj I)
    ((α.mapHomologicalComplex (.up ℤ)).app I) hα

private def extendSingleNatIso (A : Type*) [Category A] [Abelian A] :
    HomologicalComplex.single A (.up ℕ) 0 ⋙ ComplexShape.embeddingUpNat.extendFunctor A ≅
      HomologicalComplex.single A (.up ℤ) 0 :=
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := by simp
  NatIso.ofComponents (fun X => HomologicalComplex.extendSingleIso
    ComplexShape.embeddingUpNat X 0 0 h0) (by
    intro X Y f
    apply HomologicalComplex.to_single_hom_ext
    change (HomologicalComplex.extendMap ((HomologicalComplex.single A (.up ℕ) 0).map f)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat Y 0 0 h0).hom).f 0 =
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 h0).hom ≫
        (HomologicalComplex.single A (.up ℤ) 0).map f).f 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat h0,
      HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
      HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc])

/-- A functorial `ℕ`-indexed resolution `R` whose comparison with the identity becomes a
quasi-isomorphism after applying `Γ` to each term of a bounded-below complex `I` gives a
first-quadrant spectral sequence whose first page is the homology of the columns of `Γ ∘ R`
applied to `I`, abutting to the homology of `Γ` applied to `I`. -/
public lemma exists_spectralSequence_of_natFunctorResolution
    {D A : Type*} [Category D] [Abelian D] [Category A] [Abelian A]
    (Γ : D ⥤ A) [Γ.Additive] (R : D ⥤ CochainComplex D ℕ) [R.Additive]
    (α : HomologicalComplex.single D (.up ℕ) 0 ⟶ R)
    (I : CochainComplex D ℤ) [I.IsStrictlyGE 0]
    (hα : ∀ n, QuasiIso ((Γ.mapHomologicalComplex (.up ℕ)).map (α.app (I.X n)))) :
    let G := R ⋙ Γ.mapHomologicalComplex (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor A
    ∃ E : CohomologicalSpectralSequence A 1,
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅
        (((G ⋙ HomologicalComplex.eval A (.up ℤ) p).mapHomologicalComplex (.up ℤ)).obj
          I).homology q)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      Stacks.RelativeLeray.AbutsTo E
        (fun n => ((Γ.mapHomologicalComplex (.up ℤ)).obj I).homology n) := by
  intro G
  let a : Γ ⋙ HomologicalComplex.single A (.up ℕ) 0 ⟶
      R ⋙ Γ.mapHomologicalComplex (.up ℕ) :=
    (HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).inv ≫
      Functor.whiskerRight α (Γ.mapHomologicalComplex (.up ℕ))
  let a' : Γ ⋙ HomologicalComplex.single A (.up ℤ) 0 ⟶ G :=
    (Functor.isoWhiskerLeft Γ (extendSingleNatIso A)).inv ≫
      Functor.whiskerRight a (ComplexShape.embeddingUpNat.extendFunctor A)
  refine exists_spectralSequence_of_functorResolution Γ G a' ?_ I ?_
  · intro X i hi
    exact (((Γ.mapHomologicalComplex (.up ℕ)).obj (R.obj X))).isZero_extend_X
      ComplexShape.embeddingUpNat i (fun n => by change (n : ℤ) ≠ i; omega)
  · intro n
    have := hα n
    have ha : QuasiIso (a.app (I.X n)) := by
      dsimp [a]
      infer_instance
    exact quasiIso_comp ((extendSingleNatIso A).inv.app (Γ.obj (I.X n)))
      (HomologicalComplex.extendMap (a.app (I.X n)) ComplexShape.embeddingUpNat)
      (hφ' := (HomologicalComplex.quasiIso_extendMap_iff
        (a.app (I.X n)) ComplexShape.embeddingUpNat).mpr ha)

end Stacks.RelativeCech

end
