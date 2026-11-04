module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksCore.CategoryTheory.Filtration.GradedExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# The filtered Hom complex of a filtered complex

Let `A` be a Grothendieck abelian category, let `K` be an object of its derived category and let
`M` be a filtered cochain complex in `A`.  Choosing a K-injective complex `I` with injective
terms representing `K`, the Hom complex `C^• = Hom^•(M^•, I^•)` carries a decreasing filtration
whose `p`-th step is `F^pC^• = Hom^•(M^• / F^{-p+1}M^•, I^•)`: a homomorphism out of the
quotient is the same thing as a homomorphism out of `M^•` killing `F^{-p+1}M^•`.

Because the terms of `I` are injective, restricting homomorphisms along the short exact sequence
`0 → gr^{-p}M^• → M^•/F^{-p+1}M^• → M^•/F^{-p}M^• → 0` stays exact termwise, which identifies the
`p`-th graded piece of this filtration with `Hom^•(gr^{-p}M^•, I^•)`.  Since `I` is K-injective,
the cohomology of a Hom complex out of a complex `L` computes `Ext^n(L, K)`, compatibly with
precomposition.

## Main definitions

* `Stacks.Injectives.KInjectiveRepresentative`: a K-injective complex with injective terms
  representing a given object of the derived category.
* `Stacks.Injectives.kInjectiveRepresentative`: the chosen such representative.
* `Stacks.Injectives.filteredHomComplex`, `Stacks.Injectives.filteredHomComplexStep`: the Hom
  complex `Hom^•(M^•, I^•)` and the Hom complex `Hom^•(M^•/F^{-p+1}M^•, I^•)` out of a quotient.
* `Stacks.Injectives.FilteredHomComplexData`: the filtration on the Hom complex together with
  all of its identifications.
* `Stacks.Injectives.filteredHomComplexFiltration`,
  `Stacks.Injectives.filteredHomFilteredComplex`: the filtration itself and the Hom complex
  bundled with it.

## Main results

* `Stacks.Injectives.filteredHomComplexData_nonempty`: such data exists.
* `Stacks.Injectives.filteredHomComplexFiltrationStepIso`,
  `Stacks.Injectives.filteredHomComplexFiltrationGrIso`: the steps and the graded pieces of the
  filtration are the expected Hom complexes.
* `Stacks.Injectives.filteredHomComplexStepHomologyAddEquivExt`,
  `Stacks.Injectives.filteredHomComplexHomologyAddEquivExt`: the cohomology of a step and of the
  whole Hom complex are the corresponding Ext groups.
* `Stacks.Injectives.filteredHomComplexHomologyAddEquivExt_quotientPrecomp`,
  `Stacks.Injectives.filteredHomComplexHomologyAddEquivExt_ι`: these identifications intertwine
  the filtration inclusion with the canonical map from the Ext group of the quotient.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0G1Z](https://stacks.math.columbia.edu/tag/0G1Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Injectives

universe u₁ v₁

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- A K-injective complex with injective terms representing an object of the derived category. -/
structure KInjectiveRepresentative (K : DerivedCategory A) where
  /-- The chosen complex. -/
  complex : CochainComplex A ℤ
  /-- The chosen complex represents `K` in the derived category. -/
  represents : DerivedCategory.Q.obj complex ≅ K
  /-- Every term of the chosen complex is injective. -/
  injective (n : ℤ) : Injective (complex.X n)
  /-- The chosen complex is K-injective. -/
  isKInjective : complex.IsKInjective

variable [IsGrothendieckAbelian.{w} A]

/-- A chosen K-injective complex with injective terms representing `K`. -/
noncomputable def kInjectiveRepresentative (K : DerivedCategory A) :
    KInjectiveRepresentative A K := by
  let M := DerivedCategory.Q.objPreimage K
  let I := (kInjectiveResolutionFunctor A).obj M
  let i := (kInjectiveResolutionInclusion A).app M
  refine
    { complex := I
      represents := (asIso (DerivedCategory.Q.map i)).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso K
      injective := fun n ↦ ?_
      isKInjective := ?_ }
  · dsimp [I]
    infer_instance
  · dsimp [I]
    infer_instance

/-- The chosen representative of `K` is K-injective. -/
noncomputable instance kInjectiveRepresentative_isKInjective (K : DerivedCategory A) :
    (kInjectiveRepresentative A K).complex.IsKInjective :=
  (kInjectiveRepresentative A K).isKInjective

/-- Every term of the chosen representative of `K` is injective. -/
noncomputable instance kInjectiveRepresentative_injective
    (K : DerivedCategory A) (n : ℤ) :
    Injective ((kInjectiveRepresentative A K).complex.X n) :=
  (kInjectiveRepresentative A K).injective n

/-- The Hom complex `C• = Hom•(M•, I•)` associated to a filtered complex and a derived
category object. -/
noncomputable abbrev filteredHomComplex
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    CochainComplex AddCommGrpCat ℤ :=
  M.X.HomComplex (kInjectiveRepresentative A K).complex

/-- The `p`-th step
`FᵖC• = Hom•(M• / F⁻ᵖ⁺¹M•, I•)` of the filtration on the Hom complex. -/
noncomputable abbrev filteredHomComplexStep
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p : ℤ) :
    CochainComplex AddCommGrpCat ℤ :=
  ((FilteredObject.quot (op (-p + 1))).obj M).HomComplex
    (kInjectiveRepresentative A K).complex

/-- The object of the derived category represented by the underlying complex `M•`. -/
noncomputable abbrev filteredComplexDerivedObject (M : CochainComplex.Filtered A) :
    DerivedCategory A :=
  DerivedCategory.Q.obj M.X

/-- The object of the derived category represented by `M• / FᵖM•`. -/
noncomputable abbrev filteredComplexQuotientDerivedObject
    (M : CochainComplex.Filtered A) (p : ℤ) : DerivedCategory A :=
  DerivedCategory.Q.obj ((FilteredObject.quot (op p)).obj M)

/-- The object of the derived category represented by `grᵖ M•`. -/
noncomputable abbrev filteredComplexGradedDerivedObject
    (M : CochainComplex.Filtered A) (p : ℤ) : DerivedCategory A :=
  DerivedCategory.Q.obj ((FilteredObject.gr p).obj M)

/-- The components of a cochain obtained by precomposition. -/
private lemma precompCM_v {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {X Y I : CochainComplex B ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain Y I n) (p q : ℤ) (hpq : p + n = q) :
    ((Stacks.Cohomology.Locality.precompCM (L := I) f).f n z).v p q hpq =
      f.f p ≫ z.v p q hpq := by
  show ((CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)).v p q hpq = _
  simp only [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]

/-- The components of a cochain obtained by precomposition, in bundled-group form. -/
private lemma precompCM_hom_v {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {X Y I : CochainComplex B ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : (Y.HomComplex I).X n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.Cohomology.Locality.precompCM (L := I) f).f n).hom z).v p q hpq =
      f.f p ≫ (z : CochainComplex.HomComplex.Cochain Y I n).v p q hpq := by
  show ((Stacks.Cohomology.Locality.precompCM (L := I) f).f n
    (z : CochainComplex.HomComplex.Cochain Y I n)).v p q hpq = _
  exact precompCM_v f n z p q hpq

/-- Precomposition with a termwise epimorphism is a monomorphism of Hom complexes. -/
private lemma mono_precompCM_of_epi {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {X Y I : CochainComplex B ℤ} (f : X ⟶ Y)
    (hf : ∀ i : ℤ, Epi (f.f i)) : Mono (Stacks.Cohomology.Locality.precompCM (L := I) f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  have hv := congrArg (fun z => z.v p q hpq) hxy
  simp only [precompCM_hom_v] at hv
  exact (cancel_epi (f.f p)).1 hv

omit [IsGrothendieckAbelian.{w} A] in
/-- The quotient map onto `M• / FⁱM•` is termwise epic. -/
private lemma epi_quotπ_f (M : CochainComplex.Filtered A) (i n : ℤ) :
    Epi ((FilteredObject.quotπ (op i) M).f n) := by
  infer_instance

/-- Precomposition on Hom complexes reverses composition. -/
lemma precompCM_comp {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {X Y Z I : CochainComplex B ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.Cohomology.Locality.precompCM (L := I) g ≫ Stacks.Cohomology.Locality.precompCM f =
      Stacks.Cohomology.Locality.precompCM (L := I) (f ≫ g) := by
  ext n z
  rw [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
  change CochainComplex.HomComplex.Cochain Z I n at z
  change
    (CochainComplex.HomComplex.Cochain.ofHom f).comp
        ((CochainComplex.HomComplex.Cochain.ofHom g).comp z (zero_add n)) (zero_add n) =
      (CochainComplex.HomComplex.Cochain.ofHom (f ≫ g)).comp z (zero_add n)
  rw [← CochainComplex.HomComplex.Cochain.comp_assoc
      (CochainComplex.HomComplex.Cochain.ofHom f)
      (CochainComplex.HomComplex.Cochain.ofHom g) z (zero_add 0) (zero_add n) (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_comp]

/-- Precomposition with the identity is the identity of the Hom complex. -/
lemma precompCM_id {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {X I : CochainComplex B ℤ} :
    Stacks.Cohomology.Locality.precompCM (L := I) (𝟙 X) = 𝟙 (X.HomComplex I) := by
  ext n z
  simp only [Stacks.Cohomology.Locality.precompCM, CochainComplex.HomComplex.Cochain.id_comp,
    HomologicalComplex.id_f, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
  rfl

/-- Conjugating by isomorphisms of the source and the target is an isomorphism of the additive
groups of homomorphisms. -/
noncomputable def homCongrAddEquiv
    {B : Type u₁} [Category.{v₁} B] [Preadditive B]
    {X X' Y Y' : B} (eX : X ≅ X') (eY : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun f : X ⟶ Y => eX.inv ≫ f ≫ eY.hom)
      (by intros; simp))
    (eX.homCongr eY).bijective

/-- The underlying function of `homCongrAddEquiv`. -/
lemma homCongrAddEquiv_apply
    {B : Type u₁} [Category.{v₁} B] [Preadditive B]
    {X X' Y Y' : B} (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) :
    homCongrAddEquiv eX eY f = eX.inv ≫ f ≫ eY.hom := rfl

/-- The cohomology of `Hom•(L•, I•)` for the chosen K-injective representative `I` of `K` is
`Extⁿ(L•, K)`. -/
noncomputable def homologyToExt
    (K : DerivedCategory A) (L : CochainComplex A ℤ) (n : ℤ) :
    (L.HomComplex (kInjectiveRepresentative A K).complex).homology n ≃+
      DerivedCategory.Ext (DerivedCategory.Q.obj L) K n := by
  let I := (kInjectiveRepresentative A K).complex
  letI : I.IsKInjective := (kInjectiveRepresentative A K).isKInjective
  let QH := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let eL : DerivedCategory.Qh.obj (QH.obj L) ≅ DerivedCategory.Q.obj L :=
    (DerivedCategory.quotientCompQhIso A).app L
  let eI : DerivedCategory.Qh.obj (QH.obj (I⟦n⟧)) ≅
      DerivedCategory.Q.obj (I⟦n⟧) := (DerivedCategory.quotientCompQhIso A).app (I⟦n⟧)
  let eShift : DerivedCategory.Q.obj (I⟦n⟧) ≅ (DerivedCategory.Q.obj I)⟦n⟧ :=
    (DerivedCategory.Q.commShiftIso n).app I
  let eRep : DerivedCategory.Q.obj I ≅ K := (kInjectiveRepresentative A K).represents
  let eK : DerivedCategory.Qh.obj (QH.obj (I⟦n⟧)) ≅ K⟦n⟧ :=
    eI ≪≫ eShift ≪≫ (shiftFunctor (DerivedCategory A) n).mapIso eRep
  exact
    (CochainComplex.HomComplex.homologyAddEquiv L I n).trans <|
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans <|
        (qhMapAddEquivOfBijective
          (CochainComplex.IsKInjective.Qh_map_bijective (QH.obj L) (I⟦n⟧))).trans <|
          homCongrAddEquiv eL eK)

/-- The identification of Hom-complex cohomology with Ext turns precomposition by `f` into the
contravariant Ext map along `f`. -/
lemma homologyToExt_precomp
    (K : DerivedCategory A) {L L' : CochainComplex A ℤ} (f : L' ⟶ L) (n : ℤ)
    (x : (L.HomComplex (kInjectiveRepresentative A K).complex).homology n) :
    homologyToExt A K L' n (HomologicalComplex.homologyMap
        (Stacks.Cohomology.Locality.precompCM f) n x) =
      DerivedCategory.Q.map f ≫ homologyToExt A K L n x := by
  let I := (kInjectiveRepresentative A K).complex
  obtain ⟨c, rfl⟩ := (CochainComplex.HomComplex.homologyAddEquiv L I n).symm.surjective x
  obtain ⟨z, rfl⟩ := c.mk_surjective
  rw [Stacks.Cohomology.Locality.precompCM_homologyAddEquiv_symm]
  dsimp only [I]
  simp only [homologyToExt, AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply,
    CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
    Functor.map_comp, qhMapAddEquivOfBijective_apply, homCongrAddEquiv_apply]
  have hnat : ((DerivedCategory.quotientCompQhIso A).app L').inv ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) =
        DerivedCategory.Q.map f ≫ ((DerivedCategory.quotientCompQhIso A).app L).inv :=
    ((DerivedCategory.quotientCompQhIso A).inv.naturality f).symm
  rw [← Category.assoc, ← Category.assoc, hnat]
  simp only [Category.assoc]

/-- Precomposition with the zero morphism is zero. -/
private lemma precompCM_zero {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {X Y I : CochainComplex B ℤ} :
    Stacks.Cohomology.Locality.precompCM (L := I) (0 : X ⟶ Y) = 0 := by
  ext n z
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  rw [precompCM_hom_v]
  simp only [HomologicalComplex.zero_f, zero_comp, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply]
  rfl

/-- Restricting homomorphisms into a complex with injective terms along a short exact sequence of
complexes gives a short exact sequence of Hom complexes. -/
private lemma homComplexShortExactOfInjective
    {B : Type u₁} [Category.{v₁} B] [Abelian B]
    (S : ShortComplex (CochainComplex B ℤ)) (hS : S.ShortExact)
    (I : CochainComplex B ℤ) (hI : ∀ q : ℤ, Injective (I.X q)) :
    (let T : ShortComplex (CochainComplex AddCommGrpCat.{v₁} ℤ) := ShortComplex.mk
      (Stacks.Cohomology.Locality.precompCM (L := I) S.g)
      (Stacks.Cohomology.Locality.precompCM (L := I) S.f)
      (by
        rw [precompCM_comp]
        rw [S.zero, precompCM_zero]); T.ShortExact) := by
  have _inst (q : ℤ) : Injective (I.X q) := hI q
  let T : ShortComplex (CochainComplex AddCommGrpCat.{v₁} ℤ) :=
    ShortComplex.mk (Stacks.Cohomology.Locality.precompCM (L := I) S.g)
      (Stacks.Cohomology.Locality.precompCM (L := I) S.f) (by
        rw [precompCM_comp, S.zero, precompCM_zero])
  apply HomologicalComplex.shortExact_of_degreewise_shortExact T
  intro n
  have hSp (p : ℤ) :
      (S.map (HomologicalComplex.eval B (ComplexShape.up ℤ) p)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.eval B (ComplexShape.up ℤ) p)
  let U : ShortComplex AddCommGrpCat.{v₁} := T.map (HomologicalComplex.eval _ _ n)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_mono_cokernel_desc, AddCommGrpCat.mono_iff_injective]
    let d := cokernel.desc U.f U.g U.zero
    intro x y hxy
    have hd : d.hom (x - y) = 0 := by
      change d.hom x = d.hom y at hxy
      simp only [map_sub, hxy, sub_self]
    have hπ : Function.Surjective (cokernel.π U.f).hom :=
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨z, hzπ⟩ := hπ (x - y)
    have hz0 : U.g.hom z = 0 := by
      have heq : d.hom ((cokernel.π U.f).hom z) = U.g.hom z := by
        exact congrArg (fun f => f z) (cokernel.π_desc U.f U.g U.zero)
      rw [← heq, hzπ, hd]
    have hc (p : ℤ) :=
      (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
        (S.map (HomologicalComplex.eval B (ComplexShape.up ℤ) p))).mp
        ⟨(hSp p).exact, (hSp p).epi_g⟩
    have hz (p q : ℤ) (hpq : p + n = q) :
        S.f.f p ≫ (z : CochainComplex.HomComplex.Cochain S.X₂ I n).v p q hpq = 0 := by
      rw [← precompCM_hom_v S.f n z p q hpq]
      exact congrArg (fun w : CochainComplex.HomComplex.Cochain S.X₁ I n => w.v p q hpq) hz0
    let c (p q : ℤ) (hpq : p + n = q) : CokernelCofork (S.f.f p) :=
      CokernelCofork.ofπ (z.v p q hpq) (hz p q hpq)
    let v : CochainComplex.HomComplex.Cochain S.X₃ I n :=
      CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
        (Classical.choice (hc p)).desc (c p q hpq)
    have hv : ((Stacks.Cohomology.Locality.precompCM (L := I) S.g).f n v) = z := by
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      exact (precompCM_hom_v S.g n (v : (S.X₃.HomComplex I).X n) p q hpq).trans
        ((Classical.choice (hc p)).fac (c p q hpq) WalkingParallelPair.one)
    have hzπzero : (cokernel.π U.f).hom z = 0 := by
      have hfac : (cokernel.π U.f).hom ((U.f.hom) v) = 0 := by
        show ((U.f ≫ cokernel.π U.f).hom v) = 0
        rw [cokernel.condition U.f]
        rfl
      rw [← hv]
      exact hfac
    exact sub_eq_zero.mp (hzπ.symm.trans hzπzero)
  · have := mono_precompCM_of_epi (I := I) S.g fun p => (hSp p).epi_g
    exact inferInstanceAs (Mono (T.f.f n))
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro z
    classical
    have hMono (p : ℤ) : Mono (S.f.f p) := (hSp p).mono_f
    let v : CochainComplex.HomComplex.Cochain S.X₂ I n :=
      CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
        Injective.factorThru
          ((z : CochainComplex.HomComplex.Cochain S.X₁ I n).v p q hpq) (S.f.f p)
    refine ⟨v, ?_⟩
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    exact (precompCM_hom_v S.f n (v : (S.X₂.HomComplex I).X n) p q hpq).trans
      (Injective.comp_factorThru _ _)

/-- The filtration of `Hom•(M•, I•)` by the Hom complexes out of the quotients of `M•`. -/
private noncomputable def filteredHomComplexFiltrationCore
    (A : Type u) [Category.{v} A] [Abelian A]
    (M : CochainComplex.Filtered A) (I : CochainComplex A ℤ) :
    Filtration (M.X.HomComplex I) ℤᵒᵖ := by
  let Q (p : ℤ) := (FilteredObject.quot (op (-p + 1))).obj M
  let π (p : ℤ) : M.X ⟶ Q p := FilteredObject.quotπ (op (-p + 1)) M
  let j (p : ℤ) : (Q p).HomComplex I ⟶ M.X.HomComplex I :=
    Stacks.Cohomology.Locality.precompCM (L := I) (π p)
  have hj (p : ℤ) : Mono (j p) :=
    mono_precompCM_of_epi (π p) (fun n => epi_quotπ_f A M (-p + 1) n)
  exact
    { toMonoOver :=
        { obj := fun i => MonoOver.mk (j i.unop)
          map := fun {i k} f =>
            MonoOver.homMk
              (Stacks.Cohomology.Locality.precompCM (L := I)
                (FilteredObject.quotStep
                  (opHomOfLE (show -i.unop + 1 ≤ -k.unop + 1 by
                    have hki : k.unop ≤ i.unop := leOfHom f.unop
                    omega)) M)) (by
                dsimp [j, Q, π]
                rw [precompCM_comp]
                congr 1
                have hki : k.unop ≤ i.unop := leOfHom f.unop
                exact FilteredObject.quotπ_quotStep
                  (opHomOfLE (show -i.unop + 1 ≤ -k.unop + 1 by omega)) M)
          map_id := fun _ => Subsingleton.elim _ _
          map_comp := fun _ _ => Subsingleton.elim _ _ } }

/-- The Hom complex bundled with the filtration `filteredHomComplexFiltrationCore`. -/
private noncomputable def filteredHomFilteredComplexCore
    (M : CochainComplex.Filtered A) (I : CochainComplex A ℤ) :
    CochainComplex.Filtered AddCommGrpCat.{v} :=
  { X := M.X.HomComplex I
    filtration := filteredHomComplexFiltrationCore A M I }

/-- The index morphism `op (-p + 1) ⟶ op (-(p+1) + 1)`. -/
private def filteredHomStepIndex (p : ℤ) : op (-p + 1) ⟶ op (-(p + 1) + 1) :=
  opHomOfLE (show -(p + 1) + 1 ≤ -p + 1 by omega)

/-- The `p`-th graded piece of `filteredHomComplexFiltrationCore` is `Hom•(gr⁻ᵖ M•, I•)`,
compatibly with the canonical inclusion of the graded piece into the quotient. -/
private noncomputable def filteredHomComplexGrIsoCore
    (M : CochainComplex.Filtered A) (I : CochainComplex A ℤ)
    (hI : ∀ q : ℤ, Injective (I.X q)) (p : ℤ) :
    { e : (FilteredObject.gr p).obj (filteredHomFilteredComplexCore A M I) ≅
        ((FilteredObject.gr (-p)).obj M).HomComplex I //
      FilteredObject.grMapπ (FilteredObject.succHom p)
          (filteredHomFilteredComplexCore A M I) ≫ e.hom =
        Stacks.Cohomology.Locality.precompCM (L := I)
          (FilteredObject.grMapι (FilteredObject.succHom (-p)) M) } := by
  classical
  let φ := filteredHomStepIndex p
  let S : ShortComplex (CochainComplex A ℤ) :=
    FilteredObject.quotStepShortComplex φ M
  have hS : S.ShortExact :=
    FilteredObject.quotStepShortComplex_shortExact φ M
  let T₀ : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) :=
    ShortComplex.mk (Stacks.Cohomology.Locality.precompCM (L := I) S.g)
      (Stacks.Cohomology.Locality.precompCM (L := I) S.f) (by
        rw [precompCM_comp, S.zero, precompCM_zero])
  have hT₀ : T₀.ShortExact :=
    homComplexShortExactOfInjective S hS I hI
  let C : CochainComplex.Filtered AddCommGrpCat.{v} :=
    filteredHomFilteredComplexCore A M I
  have hstep : C.filtration.step (FilteredObject.succHom p) = T₀.f := by
    dsimp [C, filteredHomFilteredComplexCore, filteredHomComplexFiltrationCore,
      Filtration.step, T₀, S, FilteredObject.quotStepShortComplex, φ,
      filteredHomStepIndex]
    congr 1
  let T : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) :=
    ShortComplex.mk (C.filtration.step (FilteredObject.succHom p)) T₀.g (by
      rw [hstep]
      exact T₀.zero)
  have hT : T.ShortExact := by
    apply ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
        dsimp [T]
        exact hstep.symm) (by rfl)) hT₀
  let hGr : IsColimit
      (CokernelCofork.ofπ (FilteredObject.grMapπ (FilteredObject.succHom p) C)
        (FilteredObject.step_grMapπ (FilteredObject.succHom p) C)) :=
    FilteredObject.grMapIsCokernel (FilteredObject.succHom p) C
  have hColT : IsColimit (CokernelCofork.ofπ T.g T.zero) :=
    Classical.choice ((ShortComplex.exact_and_epi_g_iff_g_is_cokernel T).mp
      ⟨hT.exact, hT.epi_g⟩)
  have hCol : IsColimit
      (CokernelCofork.ofπ (f := C.filtration.step (FilteredObject.succHom p)) T.g T.zero) :=
    hColT
  let hIso : (FilteredObject.gr p).obj C ≅ (S.X₁.HomComplex I) :=
    hGr.coconePointUniqueUpToIso hCol
  have hComp : FilteredObject.grMapπ (FilteredObject.succHom p) C ≫ hIso.hom =
      Stacks.Cohomology.Locality.precompCM (L := I) (FilteredObject.grMapι φ M) := by
    have hh := IsColimit.comp_coconePointUniqueUpToIso_hom hGr hCol
      WalkingParallelPair.one
    change _ = T.g at hh
    simpa [T, T₀, S, FilteredObject.quotStepShortComplex] using hh
  let hidx : op (-p) ≅ op (-(p + 1) + 1) :=
    eqToIso (congrArg op (show -p = -(p + 1) + 1 by ring))
  let hstepIso : M.filtration.obj (op (-p)) ≅ M.filtration.obj (op (-(p + 1) + 1)) :=
    M.filtration.diagram.mapIso hidx
  have hφ : φ = FilteredObject.succHom (-p) ≫ hidx.hom := by
    dsimp [φ, hidx, filteredHomStepIndex]
    apply Subsingleton.elim
  have hstep' : M.filtration.step (FilteredObject.succHom (-p)) ≫ hstepIso.hom =
      M.filtration.step φ := by
    rw [hφ]
    change M.filtration.step (FilteredObject.succHom (-p)) ≫
        M.filtration.step hidx.hom =
      M.filtration.step (FilteredObject.succHom (-p) ≫ hidx.hom)
    exact M.filtration.step_comp _ _
  let eStd : (FilteredObject.gr (-p)).obj M ≅ (S.X₁) :=
    cokernel.mapIso (f := M.filtration.step (FilteredObject.succHom (-p)))
      (M.filtration.step φ) (Iso.refl _) hstepIso (by
      rw [hstep']
      simp)
  have hinc : hstepIso.hom ≫ M.filtration.ι.app (op (-(p + 1) + 1)) =
      M.filtration.ι.app (op (-p)) := by
    simp [hstepIso]
  have hπ : FilteredObject.grMapπ (FilteredObject.succHom (-p)) M ≫ eStd.hom =
      hstepIso.hom ≫ FilteredObject.grMapπ φ M := by
    dsimp [FilteredObject.grMapπ, eStd, cokernel.mapIso, cokernel.map]
    exact cokernel.π_desc _ _ _
  have hι : eStd.hom ≫ FilteredObject.grMapι φ M =
      FilteredObject.grMapι (FilteredObject.succHom (-p)) M := by
    apply (cancel_epi (FilteredObject.grMapπ (FilteredObject.succHom (-p)) M)).1
    calc
      FilteredObject.grMapπ (FilteredObject.succHom (-p)) M ≫ eStd.hom ≫
          FilteredObject.grMapι φ M =
          hstepIso.hom ≫ FilteredObject.grMapπ φ M ≫ FilteredObject.grMapι φ M := by
            rw [← Category.assoc, hπ, Category.assoc]
      _ = hstepIso.hom ≫ M.filtration.ι.app (op (-(p + 1) + 1)) ≫
          FilteredObject.quotπ (op (-p + 1)) M := by
            rw [FilteredObject.grMapπ_grMapι]
      _ = M.filtration.ι.app (op (-p)) ≫ FilteredObject.quotπ (op (-p + 1)) M := by
            rw [← Category.assoc, hinc]
      _ = FilteredObject.grMapπ (FilteredObject.succHom (-p)) M ≫
          FilteredObject.grMapι (FilteredObject.succHom (-p)) M := by
            rw [FilteredObject.grMapπ_grMapι]
  let eHom : (S.X₁.HomComplex I) ≅ ((FilteredObject.gr (-p)).obj M).HomComplex I :=
    { hom := Stacks.Cohomology.Locality.precompCM (L := I) eStd.hom
      inv := Stacks.Cohomology.Locality.precompCM (L := I) eStd.inv
      hom_inv_id := by
        rw [precompCM_comp, Iso.inv_hom_id]
        exact precompCM_id
      inv_hom_id := by
        rw [precompCM_comp, Iso.hom_inv_id]
        exact precompCM_id }
  refine ⟨hIso ≪≫ eHom, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hComp]
  dsimp [C, filteredHomFilteredComplexCore, filteredHomComplexFiltrationCore, eHom]
  change Stacks.Cohomology.Locality.precompCM (L := I) (FilteredObject.grMapι φ M) ≫
      Stacks.Cohomology.Locality.precompCM (L := I) eStd.hom =
    𝟙 (((FilteredObject.quot (op (-p + 1))).obj M).HomComplex I) ≫
      Stacks.Cohomology.Locality.precompCM (L := I)
        (FilteredObject.grMapι (FilteredObject.succHom (-p)) M)
  rw [precompCM_comp, hι]
  simp

/-- The quotient map `M• ⟶ M•/F⁻ᵖ⁺¹M•`, acting contravariantly on the Hom
complex.  This is the inclusion which defines the `p`-th filtration step. -/
noncomputable def filteredHomComplexQuotientPrecomp
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p : ℤ) :
    filteredHomComplexStep A K M p ⟶ filteredHomComplex A K M :=
  Stacks.Cohomology.Locality.precompCM
    (FilteredObject.quotπ (op (-p + 1)) M)

/-- The filtration on the Hom complex, together with its identification with the quotient Hom
complexes, the identification of its associated graded, and the cohomology computations. -/
structure FilteredHomComplexData
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) where
  /-- The decreasing filtration of the Hom complex. -/
  filtration : Filtration (filteredHomComplex A K M) ℤᵒᵖ
  /-- Its `p`-th step is the Hom complex out of the corresponding quotient. -/
  stepIso (p : ℤ) : filtration.obj (op p) ≅ filteredHomComplexStep A K M p
  /-- Under `stepIso`, the inclusion of the `p`-th step is precomposition with the quotient
  map `M• ⟶ M•/F⁻ᵖ⁺¹M•`. -/
  stepIso_hom_comp (p : ℤ) :
    (stepIso p).hom ≫ filteredHomComplexQuotientPrecomp A K M p =
      filtration.ι.app (op p)
  /-- Its associated graded in degree `p` is the Hom complex out of `gr⁻ᵖ M`. -/
  grIso (p : ℤ) :
    (FilteredObject.gr p).obj
        ({ X := filteredHomComplex A K M, filtration := filtration } :
          CochainComplex.Filtered AddCommGrpCat.{v}) ≅
      ((FilteredObject.gr (-p)).obj M).HomComplex (kInjectiveRepresentative A K).complex
  /-- The graded isomorphism is the one induced by restricting homomorphisms along the
  canonical inclusion `gr⁻ᵖ M• ⟶ M•/F⁻ᵖ⁺¹M•`. -/
  grIso_hom_comp (p : ℤ) :
    FilteredObject.grMapπ (FilteredObject.succHom p)
          ({ X := filteredHomComplex A K M, filtration := filtration } :
            CochainComplex.Filtered AddCommGrpCat.{v}) ≫
        (grIso p).hom =
      (stepIso p).hom ≫
        Stacks.Cohomology.Locality.precompCM
          (FilteredObject.grMapι (FilteredObject.succHom (-p)) M)
  /-- The cohomology of a filtration step is the corresponding Ext group. -/
  stepHomologyAddEquivExt (p n : ℤ) :
    (filteredHomComplexStep A K M p).homology n ≃+
      DerivedCategory.Ext (filteredComplexQuotientDerivedObject A M (-p + 1)) K n
  /-- The cohomology of the underlying Hom complex is the corresponding Ext group. -/
  homologyAddEquivExt (n : ℤ) :
    (filteredHomComplex A K M).homology n ≃+
      DerivedCategory.Ext (filteredComplexDerivedObject A M) K n
  /-- The cohomology identifications intertwine the filtration inclusion with the canonical
  map from Ext of the quotient to Ext of the underlying complex. -/
  homologyAddEquivExt_quotientPrecomp (p n : ℤ)
      (x : (filteredHomComplexStep A K M p).homology n) :
    homologyAddEquivExt n
        (HomologicalComplex.homologyMap (filteredHomComplexQuotientPrecomp A K M p) n x) =
      DerivedCategory.Q.map (FilteredObject.quotπ (op (-p + 1)) M) ≫
        stepHomologyAddEquivExt p n x

/-- The Hom complex admits filtered-complex data whose structure maps are fixed by the quotient
maps and the canonical inclusions of the graded pieces, and whose cohomology identifications
commute with the maps induced by the quotients. -/
theorem filteredHomComplexData_nonempty
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    Nonempty (FilteredHomComplexData A K M) := by
  classical
  let I := (kInjectiveRepresentative A K).complex
  refine ⟨{
    filtration := filteredHomComplexFiltrationCore A M I
    stepIso := fun p => Iso.refl _
    stepIso_hom_comp := by intros; rfl
    grIso := fun p =>
      (filteredHomComplexGrIsoCore A M I
        (fun q => kInjectiveRepresentative_injective A K q) p).1
    grIso_hom_comp := fun p => by
      show FilteredObject.grMapπ (FilteredObject.succHom p)
          (filteredHomFilteredComplexCore A M I) ≫
        (filteredHomComplexGrIsoCore A M I
          (fun q => kInjectiveRepresentative_injective A K q) p).1.hom =
        Stacks.Cohomology.Locality.precompCM (L := I)
          (FilteredObject.grMapι (FilteredObject.succHom (-p)) M)
      exact (filteredHomComplexGrIsoCore A M I
        (fun q => kInjectiveRepresentative_injective A K q) p).2
    stepHomologyAddEquivExt := fun p n =>
      homologyToExt A K ((FilteredObject.quot (op (-p + 1))).obj M) n
    homologyAddEquivExt := fun n => homologyToExt A K M.X n
    homologyAddEquivExt_quotientPrecomp := fun p n x =>
      homologyToExt_precomp A K (FilteredObject.quotπ (op (-p + 1)) M) n x }⟩

/-- The filtered Hom complex data supplied by `filteredHomComplexData_nonempty`. -/
noncomputable def filteredHomComplexData
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    FilteredHomComplexData A K M :=
  Classical.choice (filteredHomComplexData_nonempty A K M)

/-- The decreasing filtration on `Hom•(M•, I•)` whose `p`-th step is
`Hom•(M• / F⁻ᵖ⁺¹M•, I•)`. -/
noncomputable def filteredHomComplexFiltration
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    Filtration (filteredHomComplex A K M) ℤᵒᵖ :=
  (filteredHomComplexData A K M).filtration

/-- The Hom complex together with its decreasing filtration. -/
noncomputable def filteredHomFilteredComplex
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) :
    CochainComplex.Filtered AddCommGrpCat.{v} where
  X := filteredHomComplex A K M
  filtration := filteredHomComplexFiltration A K M

/-- The `p`-th step of the filtered Hom complex is
`Hom•(M• / F⁻ᵖ⁺¹M•, I•)`. -/
noncomputable def filteredHomComplexFiltrationStepIso
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p : ℤ) :
    (filteredHomComplexFiltration A K M).obj (op p) ≅
      filteredHomComplexStep A K M p :=
  (filteredHomComplexData A K M).stepIso p

/-- The `p`-th associated graded complex of the filtered Hom complex is the Hom complex from
`gr⁻ᵖ M•` to the chosen K-injective representative of `K`. -/
noncomputable def filteredHomComplexFiltrationGrIso
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p : ℤ) :
    (FilteredObject.gr p).obj (filteredHomFilteredComplex A K M) ≅
      ((FilteredObject.gr (-p)).obj M).HomComplex (kInjectiveRepresentative A K).complex :=
  (filteredHomComplexData A K M).grIso p

/-- The cohomology of the `p`-th filtration step is
`Extⁿ(M• / F⁻ᵖ⁺¹M•, K)`. -/
noncomputable def filteredHomComplexStepHomologyAddEquivExt
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p n : ℤ) :
    (filteredHomComplexStep A K M p).homology n ≃+
      DerivedCategory.Ext (filteredComplexQuotientDerivedObject A M (-p + 1)) K n :=
  (filteredHomComplexData A K M).stepHomologyAddEquivExt p n

/-- The cohomology of the underlying Hom complex is `Extⁿ(M•, K)`. -/
noncomputable def filteredHomComplexHomologyAddEquivExt
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (n : ℤ) :
    (filteredHomComplex A K M).homology n ≃+
      DerivedCategory.Ext (filteredComplexDerivedObject A M) K n :=
  (filteredHomComplexData A K M).homologyAddEquivExt n

/-- The quotient-induced map on Hom-complex cohomology is the canonical contravariant map
on Ext under the chosen additive equivalences. -/
theorem filteredHomComplexHomologyAddEquivExt_quotientPrecomp
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p n : ℤ)
    (x : (filteredHomComplexStep A K M p).homology n) :
    filteredHomComplexHomologyAddEquivExt A K M n
        (HomologicalComplex.homologyMap (filteredHomComplexQuotientPrecomp A K M p) n x) =
      DerivedCategory.Q.map (FilteredObject.quotπ (op (-p + 1)) M) ≫
        filteredHomComplexStepHomologyAddEquivExt A K M p n x :=
  (filteredHomComplexData A K M).homologyAddEquivExt_quotientPrecomp p n x

/-- The filtration inclusion induces the quotient map on Ext, after identifying the
filtration step with the quotient Hom complex. -/
theorem filteredHomComplexHomologyAddEquivExt_ι
    (K : DerivedCategory A) (M : CochainComplex.Filtered A) (p n : ℤ)
    (x : ((filteredHomComplexFiltration A K M).obj (op p)).homology n) :
    filteredHomComplexHomologyAddEquivExt A K M n
        (HomologicalComplex.homologyMap
          ((filteredHomComplexFiltration A K M).ι.app (op p)) n x) =
      DerivedCategory.Q.map (FilteredObject.quotπ (op (-p + 1)) M) ≫
        filteredHomComplexStepHomologyAddEquivExt A K M p n
          (HomologicalComplex.homologyMap
            (filteredHomComplexFiltrationStepIso A K M p).hom n x) := by
  have key : HomologicalComplex.homologyMap
        ((filteredHomComplexFiltration A K M).ι.app (op p)) n =
      HomologicalComplex.homologyMap (filteredHomComplexFiltrationStepIso A K M p).hom n ≫
        HomologicalComplex.homologyMap (filteredHomComplexQuotientPrecomp A K M p) n :=
    (congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        ((filteredHomComplexData A K M).stepIso_hom_comp p)).symm.trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [key, AddCommGrpCat.comp_apply]
  exact filteredHomComplexHomologyAddEquivExt_quotientPrecomp A K M p n _

end Stacks.Injectives
