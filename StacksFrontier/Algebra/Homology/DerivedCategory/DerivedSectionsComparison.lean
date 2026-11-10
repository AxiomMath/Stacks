module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic

/-!
# The comparison map into a bounded below right derived functor

Let `Γ : A ⥤ B` be an additive functor between abelian categories, with `A` having enough
injectives, and let `T : A ⥤ CochainComplex B ℤ` be an additive functor whose values vanish
in negative degrees, equipped with an augmentation `ε X : Γ(X)[0] ⟶ T(X)` natural in `X`.
Assume that `ε I` is a quasi-isomorphism whenever `I` is injective — that is, `T(I)` is a
resolution of `Γ(I)` for injective `I`.

This module constructs, out of a *functorial* injective resolution of the objects of `A`
(Tags 0139 and 0141), a natural transformation

  `α : T ⟶ R⁺Γ ∘ (-)[0]`

of functors `A ⥤ D⁺(B)`, and proves that it is compatible with the augmentation and with the
unit of the right derived functor, and that it is an isomorphism at every injective object.

This is the construction in the proof of [Stacks, Tag 09VX]: there `A` is the category of
abelian sheaves on a site, `Γ` is the sections over a presheaf of sets, and `T` is the Čech
complex of a hypercovering, whose acyclicity at injective sheaves is [Stacks, Tag 09VW]
together with the degree-zero identification [Stacks, Tag 09VV].  The double complex of that
proof is `A^{p,q} = T(I^q)^p`, its total complex is formed with
`StacksDraft.TotalComplexQuasiIso`, and the degeneration of the first spectral sequence is
[Stacks, Tag 0133] in the form `quasiIso_total_of_resolution`.

## Main definitions

* `singlePlus`: the single-complex functor, landing in bounded below complexes.
* `quotientQhIsoQ`, `singlePlusQIso`: the two identifications of `DerivedCategory.Plus.Q`
  needed to compare the derived functor unit with the localisation functor.
* `bicx`, `totcx`: the double complex `T(I^•)` and its total complex, functorially in the
  object.
* `gammaToTot`, `tToTot`: the two legs `Γ(I^•) ⟶ Tot` and `T(X) ⟶ Tot` of the comparison.
* `alpha`: the comparison natural transformation.
* `psi`: the canonical map `Γ(X)[0] ⟶ R⁺Γ(X[0])` through the resolution, i.e. the derived
  functor unit read at the single complex.

## Main results

* `quasiIso_gammaToTot`: the first leg is a quasi-isomorphism ([Stacks, Tag 0133]).
* `eps_comp_tToTot`: the augmentation triangle at the level of complexes.
* `epsNat_comp_alpha`: **the pin** — `Q(ε) ≫ α = ψ`.
* `isIso_alpha_app`: `α` is an isomorphism at every injective object.
* `isZero_of_pin_zero`: the zero natural transformation satisfies the pin only if `Γ` has
  zero sections at every injective object; so the pin is not satisfied by `0`.
* `exists_comparison`, `exists_comparison_of_hasFunctorialInjectiveEmbeddings`: the packaged
  statements.

## Implementation notes

The statements are the *construction* used in the proof of Tag 09VX, for an arbitrary
additive `Γ` and an arbitrary augmented `T`; they are not the statement of Tag 09VX itself,
which is about the Čech complex of a hypercovering of a presheaf of sets, and the three
defining conditions of a hypercovering play no role here.

Three design points are forced rather than chosen.

First, `HasCoproducts.{0} B` is assumed, rather than the per-double-complex
`HomologicalComplex₂.HasTotal`: the latter is a `Prop` but not a class, so with it the total
complex cannot be formed functorially without threading a proof through every definition.
With `HasCoproducts.{0} B` the instance is found by synthesis and
`HomologicalComplex₂.totalFunctor` applies; for `AddCommGrpCat.{w}` the hypothesis holds.

Second, the first leg `gammaToTot` is *chosen* from the existential of
`StacksDraft.TotalComplexQuasiIso.exists_comparisonMap_p`.  This is harmless because that
existential pins every component of the map (`gammaToTot_f`), so naturality can be — and is —
proved from the component formula rather than from the choice.

Third, the comparison is assembled at the level of bounded below complexes and only then
pushed into `D⁺(B)`, with the two isomorphisms `quotientQhIsoQ` and `singlePlusQIso` lifted
through the fully faithful `DerivedCategory.Plus.ι` by `liftNatIso`.  Working in the
unbounded derived category instead would avoid the boundedness of the total complex but
would then require the comparison to be lifted back along `DerivedCategory.Plus.ι` at the end.

## References

* [Stacks, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks, Tag 0141](https://stacks.math.columbia.edu/tag/0141)
-/

@[expose] public section

namespace StacksDraft.DerivedSectionsComparison

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCategory
open StacksDraft.TotalComplexQuasiIso

universe v u v₁ u₁ v₂ u₂ v₃ u₃

section

/-- Lift a natural isomorphism through a fully faithful functor. -/
noncomputable def liftNatIso {C D E : Type*} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) [H.Full] [H.Faithful] (e : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (e.app X)) (fun {X Y} f => H.map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    rw [Functor.preimageIso_hom, Functor.preimageIso_hom, Functor.map_preimage,
      Functor.map_preimage]
    exact e.hom.naturality f))

/-- The image under `H` of a component of `liftNatIso F G H e` is the corresponding component
of `e`. -/
@[simp]
lemma liftNatIso_hom_app {C D E : Type*} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) [H.Full] [H.Faithful] (e : F ⋙ H ≅ G ⋙ H) (X : C) :
    H.map ((liftNatIso F G H e).hom.app X) = e.hom.app X :=
  H.map_preimage _

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- Tag 0139 in the `(K, η)` form that Tag 0141 consumes. -/
theorem exists_injectiveEmbeddingData (A : Type u) [Category.{v} A] [Abelian A]
    (h : HasFunctorialInjectiveEmbeddings A) :
    ∃ (K : A ⥤ InjectiveObject A) (η : 𝟭 A ⟶ K ⋙ InjectiveObject.ι A),
      ∀ B, Mono (η.app B) := by
  obtain ⟨Jf, h₁, h₂, h₃⟩ := h
  refine ⟨ObjectProperty.lift _ (Jf ⋙ Arrow.rightFunc) h₃,
    eqToHom h₁.symm ≫ Functor.whiskerLeft Jf Arrow.leftToRight, fun B => ?_⟩
  have := h₂ B
  rw [NatTrans.comp_app, eqToHom_app]
  exact mono_comp' (IsIso.mono_of_iso _) this

/-- `Plus.Q` is the composite of the homotopy quotient and `Plus.Qh`. -/
noncomputable def quotientQhIsoQ :
    HomotopyCategory.Plus.quotient A ⋙ DerivedCategory.Plus.Qh ≅ DerivedCategory.Plus.Q :=
  liftNatIso _ _ DerivedCategory.Plus.ι
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι A) (DerivedCategory.quotientCompQhIso A))

/-- Lift of the single functor to bounded-below complexes. -/
noncomputable def singlePlus : A ⥤ CochainComplex.Plus A :=
  ObjectProperty.lift _ (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
    (fun _ => ⟨0, inferInstance⟩)

example : CochainComplex.singleFunctor A 0 = HomologicalComplex.single A (ComplexShape.up ℤ) 0 :=
  rfl

/-- `Plus.Q` of the single complex is the single functor into `D⁺`. -/
noncomputable def singlePlusQIso :
    singlePlus A ⋙ DerivedCategory.Plus.Q ≅ DerivedCategory.Plus.singleFunctor A 0 :=
  liftNatIso _ _ DerivedCategory.Plus.ι
    (((SingleFunctors.evaluation A (DerivedCategory A) (0 : ℤ)).mapIso
      (DerivedCategory.singleFunctorsPostcompQIso A)).symm)

omit [HasDerivedCategory A] in
/-- **A functorial injective resolution of the objects of `A`**, from functorial injective
embeddings (Tag 0139) through Tag 0141. -/
theorem exists_resolutionData (h : HasFunctorialInjectiveEmbeddings A) :
    ∃ (Rs : A ⥤ CochainComplex.Plus (InjectiveObject A))
      (ν : singlePlus A ⟶ Rs ⋙ (InjectiveObject.ι A).mapCochainComplexPlus),
      ∀ X : A, QuasiIso ((CochainComplex.Plus.ι A).map (ν.app X)) := by
  obtain ⟨Kf, η, hη⟩ := exists_injectiveEmbeddingData A h
  obtain ⟨Fr, α, hα⟩ :=
    (CochainComplex.Plus.exists_functorial_injective_resolution_and_exists_resolutionFunctor
      A).1 Kf η hη
  exact ⟨singlePlus A ⋙ Fr, Functor.whiskerLeft (singlePlus A) α,
    fun X => hα ((singlePlus A).obj X)⟩

end

section

variable {B : Type u} [Category.{v} B] [Abelian B]

/-- The degree-zero part of a chain map out of a single complex. -/
noncomputable def augZero (Z : B) (L : CochainComplex B ℤ)
    (g : (single B (ComplexShape.up ℤ) 0).obj Z ⟶ L) : Z ⟶ L.X 0 :=
  (singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv ≫ g.f 0

/-- The degree-zero part of a chain map out of a single complex is killed by the first
differential of the target. -/
lemma augZero_comp_d (Z : B) (L : CochainComplex B ℤ)
    (g : (single B (ComplexShape.up ℤ) 0).obj Z ⟶ L) :
    augZero Z L g ≫ L.d 0 1 = 0 := by
  rw [augZero, Category.assoc, g.comm 0 1, single_obj_d, zero_comp, comp_zero]

/-- A quasi-isomorphism from a single complex in degree `0` to a complex vanishing in
negative degrees identifies the source with the kernel of the first differential. -/
lemma isIso_kernelLift_augZero (Z : B) (L : CochainComplex B ℤ)
    (hL : IsZero (L.X (-1)))
    (g : (single B (ComplexShape.up ℤ) 0).obj Z ⟶ L) [QuasiIso g] :
    IsIso (kernel.lift (L.d 0 1) (augZero Z L g) (augZero_comp_d Z L g)) := by
  have h1 : IsIso (((single B (ComplexShape.up ℤ) 0).obj Z).iCycles 0) :=
    ((single B (ComplexShape.up ℤ) 0).obj Z).isIso_iCycles 0 1 (by simp)
      (single_obj_d _ _ _ _ _)
  have h2 : IsIso (((single B (ComplexShape.up ℤ) 0).obj Z).homologyπ 0) :=
    ((single B (ComplexShape.up ℤ) 0).obj Z).isIso_homologyπ (-1) 0 (by simp)
      (single_obj_d _ _ _ _ _)
  have h3 : IsIso (L.homologyπ 0) :=
    L.isIso_homologyπ (-1) 0 (by simp) (hL.eq_of_src _ _)
  have h4 : IsIso (homologyMap g 0) := (quasiIsoAt_iff_isIso_homologyMap g 0).1 inferInstance
  let hK := L.cyclesIsKernel 0 1 (by simp)
  let e : L.cycles 0 ≅ kernel (L.d 0 1) :=
    IsLimit.conePointUniqueUpToIso hK (limit.isLimit _)
  have heq : cyclesMap g 0 ≫ e.hom =
      ((single B (ComplexShape.up ℤ) 0).obj Z).iCycles 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫
          kernel.lift (L.d 0 1) (augZero Z L g) (augZero_comp_d Z L g) := by
    apply (cancel_mono (kernel.ι (L.d 0 1))).mp
    have he : e.hom ≫ kernel.ι (L.d 0 1) = L.iCycles 0 :=
      IsLimit.conePointUniqueUpToIso_hom_comp hK (limit.isLimit _) WalkingParallelPair.zero
    simp only [Category.assoc, he, kernel.lift_ι, cyclesMap_i, augZero]
    rw [Iso.hom_inv_id_assoc]
  have h5 : IsIso (cyclesMap g 0 ≫ L.homologyπ 0) := by
    rw [← homologyπ_naturality]
    infer_instance
  have h6 : IsIso (cyclesMap g 0) := IsIso.of_isIso_comp_right _ (L.homologyπ 0)
  have h7 : IsIso (((single B (ComplexShape.up ℤ) 0).obj Z).iCycles 0 ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫
        kernel.lift (L.d 0 1) (augZero Z L g) (augZero_comp_d Z L g)) := by
    rw [← heq]
    infer_instance
  have h8 : IsIso ((singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫
      kernel.lift (L.d 0 1) (augZero Z L g) (augZero_comp_d Z L g)) :=
    IsIso.of_isIso_comp_left (((single B (ComplexShape.up ℤ) 0).obj Z).iCycles 0) _
  exact IsIso.of_isIso_comp_left (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom _

/-- A quasi-isomorphism from a single complex in degree `0` forces exactness in every
nonzero degree. -/
lemma exactAt_of_quasiIso_single (Z : B) (L : CochainComplex B ℤ)
    (g : (single B (ComplexShape.up ℤ) 0).obj Z ⟶ L) [QuasiIso g] (q : ℤ) (hq : q ≠ 0) :
    L.ExactAt q :=
  (quasiIsoAt_iff_exactAt g q
    (ExactAt.of_isZero (isZero_single_obj_X (ComplexShape.up ℤ) 0 Z q hq))).1 inferInstance

end

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasCoproducts.{0} B]

omit [Abelian A] in
/-- Naturality of the degree-zero part of an augmentation out of a single complex. -/
lemma augZero_nat {A' : Type u₃} [Category.{v₃} A'] [Abelian A']
    (G : A ⥤ A') (L : A ⥤ CochainComplex A' ℤ)
    (ν : ∀ X : A, (single A' (ComplexShape.up ℤ) 0).obj (G.obj X) ⟶ L.obj X)
    (hν : ∀ {X Y : A} (φ : X ⟶ Y),
      (single A' (ComplexShape.up ℤ) 0).map (G.map φ) ≫ ν Y = ν X ≫ L.map φ)
    {X Y : A} (φ : X ⟶ Y) :
    G.map φ ≫ augZero (G.obj Y) (L.obj Y) (ν Y) =
      augZero (G.obj X) (L.obj X) (ν X) ≫ (L.map φ).f 0 := by
  have h := HomologicalComplex.congr_hom (hν φ) 0
  simp only [comp_f] at h
  rw [single_map_f_self] at h
  simp only [augZero, Category.assoc]
  rw [← h]
  simp

section

variable (Γ : A ⥤ B) [Γ.Additive] (T : A ⥤ CochainComplex B ℤ) [T.Additive]
  (I : A ⥤ CochainComplex A ℤ)

/-- The total complex functor on double complexes of `B`. -/
noncomputable abbrev Tot : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
    CochainComplex B ℤ :=
  HomologicalComplex₂.totalFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)

/-- The double complex functor `X ↦ T(I(X)^•)`. -/
noncomputable abbrev bicx : A ⥤ HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  I ⋙ T.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total complex of the double complex, functorially. -/
noncomputable abbrev totcx : A ⥤ CochainComplex B ℤ := bicx T I ⋙ Tot

/-- `Γ` applied to the resolution complex, functorially. -/
noncomputable abbrev gammaI : A ⥤ CochainComplex B ℤ :=
  I ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℤ)

variable (ε : ∀ X : A, (single B (ComplexShape.up ℤ) 0).obj (Γ.obj X) ⟶ T.obj X)
  (hε : ∀ {X Y : A} (φ : X ⟶ Y),
    (single B (ComplexShape.up ℤ) 0).map (Γ.map φ) ≫ ε Y = ε X ≫ T.map φ)

/-- The augmentation `Γ(I^q) → T(I^q)^0` assembled into a chain map. -/
@[simps]
noncomputable def rowAug (X : A) : (gammaI Γ I).obj X ⟶ rowZero ((bicx T I).obj X) where
  f q := augZero (Γ.obj ((I.obj X).X q)) (T.obj ((I.obj X).X q)) (ε ((I.obj X).X q))
  comm' q q' _ := (augZero_nat Γ T ε (fun {_ _} φ => hε φ) ((I.obj X).d q q')).symm

variable (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
  (hI : ∀ X : A, ∃ n : ℤ, (I.obj X).IsStrictlyGE n)
  (hinj : ∀ (X : A) (n : ℤ), Injective ((I.obj X).X n))
  (hεinj : ∀ Y : A, Injective Y → QuasiIso (ε Y))

include hT0 hI in
omit [HasCoproducts.{0} B] in
/-- If `T` vanishes in negative degrees and `I(X)` is bounded below, then each antidiagonal
of the double complex `T(I(X)^•)` has only finitely many nonzero terms. -/
lemma diagonalFinite_bicx (X : A) : DiagonalFinite ((bicx T I).obj X) := by
  obtain ⟨n₀, hn₀⟩ := hI X
  have := hn₀
  intro n
  refine (Set.finite_Icc n₀ n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp ((HomologicalComplex.eval B (ComplexShape.up ℤ) (n - p)).map_isZero
      (T.map_isZero ((I.obj X).isZero_of_isStrictlyGE n₀ p (by omega))))
  · by_contra h
    exact hp (hT0 ((I.obj X).X p) (n - p) (by omega))

omit [HasCoproducts.{0} B] in
include hT0 hI hinj hεinj in
/-- The double complex `T(I(X)^•)`, augmented by `rowAug` from `Γ(I(X)^•)`, satisfies the
hypotheses of `StacksDraft.TotalComplexQuasiIso.Hypotheses`. -/
lemma hypotheses_bicx (X : A) :
    Hypotheses ((gammaI Γ I).obj X) ((bicx T I).obj X) (rowAug Γ T I ε hε X) where
  diagonalFinite := diagonalFinite_bicx T I hT0 hI X
  zero_of_neg p q hq := hT0 ((I.obj X).X p) q hq
  exactAt_of_ne_zero p q hq := by
    have := hεinj ((I.obj X).X p) (hinj X p)
    exact exactAt_of_quasiIso_single _ _ (ε ((I.obj X).X p)) q hq
  inducesIsoKernel p := by
    have := hεinj ((I.obj X).X p) (hinj X p)
    exact ⟨augZero_comp_d _ _ _,
      isIso_kernelLift_augZero _ _ (hT0 ((I.obj X).X p) (-1) (by omega)) _⟩

/-! ### The two legs of the comparison -/

/-- The chosen comparison `Γ(I^•) ⟶ Tot(A)` of Tag 0133. -/
noncomputable def gammaToTot (X : A) :
    (gammaI Γ I).obj X ⟶ ((bicx T I).obj X).total (ComplexShape.up ℤ) :=
  (exists_comparisonMap_p ((gammaI Γ I).obj X) ((bicx T I).obj X) (rowAug Γ T I ε hε X)
    (hypotheses_bicx Γ T I ε hε hT0 hI hinj hεinj X) inferInstance).choose

/-- In degree `n`, `gammaToTot` is `rowAug` followed by the inclusion of the `(n, 0)` term
into the total complex. -/
lemma gammaToTot_f (X : A) (n : ℤ) :
    (gammaToTot Γ T I ε hε hT0 hI hinj hεinj X).f n =
      (rowAug Γ T I ε hε X).f n ≫
        ((bicx T I).obj X).ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  ((exists_comparisonMap_p ((gammaI Γ I).obj X) ((bicx T I).obj X) (rowAug Γ T I ε hε X)
    (hypotheses_bicx Γ T I ε hε hT0 hI hinj hεinj X) inferInstance).choose_spec).1 n

/-- The map `gammaToTot` from `Γ(I(X)^•)` to the total complex is a quasi-isomorphism. -/
instance quasiIso_gammaToTot (X : A) :
    QuasiIso (gammaToTot Γ T I ε hε hT0 hI hinj hεinj X) :=
  ((exists_comparisonMap_p ((gammaI Γ I).obj X) ((bicx T I).obj X) (rowAug Γ T I ε hε X)
    (hypotheses_bicx Γ T I ε hε hT0 hI hinj hεinj X) inferInstance).choose_spec).2

include hT0 hI hinj hεinj in
/-- The maps `gammaToTot` are natural in the object. -/
lemma gammaToTot_naturality {X Y : A} (φ : X ⟶ Y) :
    (gammaI Γ I).map φ ≫ gammaToTot Γ T I ε hε hT0 hI hinj hεinj Y =
      gammaToTot Γ T I ε hε hT0 hI hinj hεinj X ≫
        HomologicalComplex₂.total.map ((bicx T I).map φ) (ComplexShape.up ℤ) := by
  ext n
  rw [comp_f, comp_f, gammaToTot_f, gammaToTot_f, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact augZero_nat Γ T ε (fun {_ _} ψ => hε ψ) ((I.map φ).f n)

/-! ### The second leg: `T(X) ⟶ Tot(A)` -/

section

variable (ν : ∀ X : A, (single A (ComplexShape.up ℤ) 0).obj X ⟶ I.obj X)
  (hν : ∀ {X Y : A} (φ : X ⟶ Y),
    (single A (ComplexShape.up ℤ) 0).map φ ≫ ν Y = ν X ≫ I.map φ)

/-- The augmentation of the double complex by `T(X)` placed in outer degree zero. -/
noncomputable def tAug (X : A) : singleObjComplex (T.obj X) ⟶ (bicx T I).obj X :=
  mkHomFromSingle (T.map (augZero X (I.obj X) (ν X))) (fun k hk => by
    obtain rfl : 1 = k := by simpa using hk
    rw [show ((bicx T I).obj X).d 0 1 = T.map ((I.obj X).d 0 1) from rfl,
      ← T.map_comp, augZero_comp_d, T.map_zero])

/-- The induced map from `T(X)` into the total complex. -/
noncomputable def tToTot (X : A) :
    T.obj X ⟶ ((bicx T I).obj X).total (ComplexShape.up ℤ) :=
  totalAlpha (T.obj X) ((bicx T I).obj X) (tAug T I ν X)

/-- In degree `i`, `tToTot` is the degree-zero component of `tAug` followed by the inclusion
of the `(0, i)` term into the total complex. -/
lemma tToTot_f (X : A) (i : ℤ) :
    (tToTot T I ν X).f i =
      (singleObjXSelf (ComplexShape.up ℤ) 0 (T.obj X)).inv.f i ≫
        ((tAug T I ν X).f 0).f i ≫
          ((bicx T I).obj X).ιTotal (ComplexShape.up ℤ) 0 i i (by simp) := rfl

include hν in
omit [HasCoproducts.{0} B] in
/-- Naturality of the outer-degree-zero component of `tAug`. -/
lemma tAug_key {X Y : A} (φ : X ⟶ Y) :
    (singleObjXSelf (ComplexShape.up ℤ) 0 (T.obj X)).inv ≫ (tAug T I ν X).f 0 ≫
        ((bicx T I).map φ).f 0 =
      T.map φ ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (T.obj Y)).inv ≫
        (tAug T I ν Y).f 0 := by
  simp only [tAug, mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc]
  rw [show ((bicx T I).map φ).f 0 = T.map ((I.map φ).f 0) from rfl, ← T.map_comp, ← T.map_comp]
  exact congrArg T.map (augZero_nat (𝟭 A) I ν (fun {_ _} ψ => hν ψ) φ).symm

include hν in
/-- The maps `tToTot` are natural in the object. -/
lemma tToTot_naturality {X Y : A} (φ : X ⟶ Y) :
    T.map φ ≫ tToTot T I ν Y =
      tToTot T I ν X ≫
        HomologicalComplex₂.total.map ((bicx T I).map φ) (ComplexShape.up ℤ) := by
  ext i
  simp only [comp_f, tToTot_f, Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  congr 1
  have h := HomologicalComplex.congr_hom (tAug_key T I ν hν φ) i
  simp only [comp_f, ← Category.assoc] at h
  exact h.symm

/-- The augmentation of the resolution, pushed through `Γ` and regarded as a chain map out
of the single complex. -/
noncomputable def gammaNu (X : A) :
    (single B (ComplexShape.up ℤ) 0).obj (Γ.obj X) ⟶ (gammaI Γ I).obj X :=
  mkHomFromSingle (Γ.map (augZero X (I.obj X) (ν X))) (fun k hk => by
    obtain rfl : 1 = k := by simpa using hk
    rw [show ((gammaI Γ I).obj X).d 0 1 = Γ.map ((I.obj X).d 0 1) from rfl,
      ← Γ.map_comp, augZero_comp_d, Γ.map_zero])

omit [HasCoproducts.{0} B] in
/-- The outer-degree-zero component of `tAug`, read on `T(X)`, is `T` applied to the
degree-zero part of the augmentation `ν X`. -/
lemma singleObjXSelf_inv_comp_tAug_f_zero (X : A) :
    (singleObjXSelf (ComplexShape.up ℤ) 0 (T.obj X)).inv ≫ (tAug T I ν X).f 0 =
      T.map (augZero X (I.obj X) (ν X)) := by
  rw [tAug, mkHomFromSingle_f, Iso.inv_hom_id_assoc]

/-- In degree `i`, `tToTot` is `T` applied to the degree-zero part of `ν X`, followed by the
inclusion of the `(0, i)` term into the total complex. -/
lemma tToTot_f' (X : A) (i : ℤ) :
    (tToTot T I ν X).f i = (T.map (augZero X (I.obj X) (ν X))).f i ≫
      ((bicx T I).obj X).ιTotal (ComplexShape.up ℤ) 0 i i (by simp) := by
  rw [tToTot_f, ← Category.assoc, ← comp_f, singleObjXSelf_inv_comp_tAug_f_zero]

omit [HasCoproducts.{0} B] in
/-- `gammaNu` is `Γ` applied to the resolution's augmentation, read through the
single-complex comparison of `Γ`. -/
lemma gammaNu_eq (X : A) :
    gammaNu Γ I ν X = (singleMapHomologicalComplex Γ (ComplexShape.up ℤ) 0).inv.app X ≫
      (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map (ν X) := by
  ext
  · rw [gammaNu, mkHomFromSingle_f, comp_f,
      singleMapHomologicalComplex_inv_app_self, augZero, Γ.map_comp]
    simp only [Category.assoc, Functor.mapHomologicalComplex_map_f]

include hT0 hI hinj hεinj in
/-- **The augmentation triangle at the level of complexes.** Composing the augmentation
`Γ(X)[0] → T(X)` with the second leg gives the same map into the total complex as composing
the resolution's augmentation with the first leg. -/
lemma eps_comp_tToTot (X : A) :
    ε X ≫ tToTot T I ν X =
      gammaNu Γ I ν X ≫ gammaToTot Γ T I ε hε hT0 hI hinj hεinj X := by
  ext
  · rw [comp_f, comp_f, tToTot_f', gammaToTot_f, gammaNu, mkHomFromSingle_f]
    have hn := augZero_nat Γ T ε (fun {_ _} ψ => hε ψ) (augZero X (I.obj X) (ν X))
    have h0 : (ε X).f 0 = (singleObjXSelf (ComplexShape.up ℤ) 0 (Γ.obj X)).hom ≫
        augZero (Γ.obj X) (T.obj X) (ε X) := by
      rw [augZero, Iso.hom_inv_id_assoc]
    rw [h0]
    simp only [Category.assoc, rowAug_f]
    congr 1
    have h2 := congrArg
      (fun k => k ≫ ((bicx T I).obj X).ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp)) hn
    simp only [Category.assoc] at h2
    exact h2.symm

end

end

end

section

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasCoproducts.{0} B]

variable [HasDerivedCategory B]

omit [HasCoproducts.{0} B] in
/-- A quasi-isomorphism of bounded below complexes becomes invertible in `D⁺`. -/
lemma isIso_PlusQ_map {K L : CochainComplex.Plus B} (f : K ⟶ L)
    (_ : QuasiIso ((CochainComplex.Plus.ι B).map f)) :
    IsIso (DerivedCategory.Plus.Q.map f) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) := by
    change IsIso (DerivedCategory.Q.map ((CochainComplex.Plus.ι B).map f))
    infer_instance
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

omit [HasCoproducts.{0} B] in
/-- A morphism of bounded below complexes becomes invertible under `Plus.Q` if and only if
its image in the homotopy category becomes invertible under `Plus.Qh`. -/
lemma isIso_PlusQ_map_iff {K L : CochainComplex.Plus B} (f : K ⟶ L) :
    IsIso (DerivedCategory.Plus.Q.map f) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map f)) :=
  (NatIso.isIso_map_iff (quotientQhIsoQ B) f).symm

section Main

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  [EnoughInjectives A]
variable (Γ : A ⥤ B) [Γ.Additive]
variable (Rs : A ⥤ CochainComplex.Plus (InjectiveObject A))

/-- The injective resolution, as a functor to bounded below complexes. -/
noncomputable abbrev IPlus : A ⥤ CochainComplex.Plus A :=
  Rs ⋙ (InjectiveObject.ι A).mapCochainComplexPlus

/-- The injective resolution, as a functor to cochain complexes. -/
noncomputable abbrev Icx : A ⥤ CochainComplex A ℤ := IPlus Rs ⋙ CochainComplex.Plus.ι A

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- Each complex `Icx Rs X` is strictly bounded below. -/
lemma exists_isStrictlyGE_Icx (X : A) : ∃ n : ℤ, ((Icx Rs).obj X).IsStrictlyGE n :=
  ((IPlus Rs).obj X).2

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- Every term of the complex `Icx Rs X` is injective. -/
lemma injective_Icx_X (X : A) (n : ℤ) : Injective (((Icx Rs).obj X).X n) :=
  ((Rs.obj X).obj.X n).2

variable (ν : singlePlus A ⟶ IPlus Rs)

/-- The augmentation of the resolution, at the level of cochain complexes. -/
noncomputable abbrev nucx (X : A) :
    (single A (ComplexShape.up ℤ) 0).obj X ⟶ (Icx Rs).obj X :=
  (CochainComplex.Plus.ι A).map (ν.app X)

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- The augmentations `nucx Rs ν` are natural in the object. -/
lemma nucx_naturality {X Y : A} (φ : X ⟶ Y) :
    (single A (ComplexShape.up ℤ) 0).map φ ≫ nucx Rs ν Y =
      nucx Rs ν X ≫ (Icx Rs).map φ := by
  have h := congrArg (CochainComplex.Plus.ι A).map (ν.naturality φ)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The augmentation becomes a natural isomorphism in `D⁺`. -/
noncomputable def nuQIso (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) :
    singlePlus A ⋙ DerivedCategory.Plus.Q ≅ IPlus Rs ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents
    (fun X =>
      haveI := isIso_PlusQ_map (ν.app X) (hν X)
      asIso (DerivedCategory.Plus.Q.map (ν.app X)))
    (fun f => (Functor.whiskerRight ν DerivedCategory.Plus.Q).naturality f)

omit [HasCoproducts.{0} B] in
/-- The unit of the right derived functor `Γ.rightDerivedFunctorPlus` is an isomorphism on
the injective resolutions `IPlus Rs`. -/
lemma isIso_unitWhisker :
    IsIso (Functor.whiskerLeft (IPlus Rs ⋙ HomotopyCategory.Plus.quotient A)
      Γ.rightDerivedFunctorPlusUnith) := by
  have h : ∀ X : A, IsIso ((Functor.whiskerLeft (IPlus Rs ⋙ HomotopyCategory.Plus.quotient A)
      Γ.rightDerivedFunctorPlusUnith).app X) := by
    intro X
    dsimp only [Functor.whiskerLeft_app, Functor.comp_obj]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

omit [HasCoproducts.{0} B] in
/-- The derived functor unit, whiskered with the resolution: a natural isomorphism. -/
noncomputable def unitWhiskerIso :
    (IPlus Rs ⋙ HomotopyCategory.Plus.quotient A) ⋙
        Γ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      (IPlus Rs ⋙ HomotopyCategory.Plus.quotient A) ⋙
        DerivedCategory.Plus.Qh ⋙ Γ.rightDerivedFunctorPlus :=
  haveI := isIso_unitWhisker Γ Rs
  asIso (Functor.whiskerLeft (IPlus Rs ⋙ HomotopyCategory.Plus.quotient A)
    Γ.rightDerivedFunctorPlusUnith)

/-- `δ`: the identification of `Q(Γ(I^•))` with the right derived functor at the single
complex, natural in the object. -/
noncomputable def delta (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) :
    (IPlus Rs ⋙ Γ.mapCochainComplexPlus) ⋙ DerivedCategory.Plus.Q ≅
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus :=
  Functor.isoWhiskerLeft (IPlus Rs ⋙ Γ.mapCochainComplexPlus) (quotientQhIsoQ B).symm ≪≫
    unitWhiskerIso Γ Rs ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (IPlus Rs) (quotientQhIsoQ A))
      Γ.rightDerivedFunctorPlus ≪≫
    Functor.isoWhiskerRight (nuQIso Rs ν hν).symm Γ.rightDerivedFunctorPlus ≪≫
    Functor.isoWhiskerRight (singlePlusQIso A) Γ.rightDerivedFunctorPlus

/-! ### The data on the `T` side -/

variable (T : A ⥤ CochainComplex B ℤ) [T.Additive]
  (ε : ∀ X : A, (single B (ComplexShape.up ℤ) 0).obj (Γ.obj X) ⟶ T.obj X)
  (hε : ∀ {X Y : A} (φ : X ⟶ Y),
    (single B (ComplexShape.up ℤ) 0).map (Γ.map φ) ≫ ε Y = ε X ≫ T.map φ)
  (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
  (hεinj : ∀ Y : A, Injective Y → QuasiIso (ε Y))

example : Γ.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B =
    CochainComplex.Plus.ι A ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℤ) := rfl

/-- `T` as a functor to bounded below complexes. -/
noncomputable def TPlus : A ⥤ CochainComplex.Plus B :=
  ObjectProperty.lift _ T (fun X => ⟨0, (CochainComplex.isStrictlyGE_iff _ 0).2
    (fun i hi => hT0 X i hi)⟩)

/-- The total complex of the double complex, as a functor to bounded below complexes. -/
noncomputable def totPlus : A ⥤ CochainComplex.Plus B :=
  ObjectProperty.lift _ (totcx T (Icx Rs)) (fun X => by
    obtain ⟨n₀, hn₀⟩ := exists_isStrictlyGE_Icx Rs X
    have := hn₀
    exact ⟨n₀, (CochainComplex.isStrictlyGE_iff _ n₀).2 (fun n hn =>
      isZero_total_X _ n₀ (fun _ q hq => hT0 _ q hq)
        (fun p hp => T.map_isZero
          (((Icx Rs).obj X).isZero_of_isStrictlyGE n₀ p hp)) n hn)⟩)

/-! ### Assembling the comparison -/

/-- The `T`-side leg, as a natural transformation of functors to bounded below complexes. -/
noncomputable def tTotNat : TPlus T hT0 ⟶ totPlus Rs T hT0 where
  app X := ObjectProperty.homMk (tToTot T (Icx Rs) (nucx Rs ν) X)
  naturality _ _ φ := by
    apply (CochainComplex.Plus.ι B).map_injective
    simp only [Functor.map_comp]
    exact tToTot_naturality T (Icx Rs) (nucx Rs ν) (fun {_ _} ψ => nucx_naturality Rs ν ψ) φ

/-- The `Γ`-side leg, as a natural transformation of functors to bounded below complexes. -/
noncomputable def gTotNat : IPlus Rs ⋙ Γ.mapCochainComplexPlus ⟶ totPlus Rs T hT0 where
  app X := ObjectProperty.homMk (gammaToTot Γ T (Icx Rs) ε hε hT0
    (exists_isStrictlyGE_Icx Rs) (injective_Icx_X Rs) hεinj X)
  naturality _ _ φ := by
    apply (CochainComplex.Plus.ι B).map_injective
    simp only [Functor.map_comp]
    exact gammaToTot_naturality Γ T (Icx Rs) ε hε hT0
      (exists_isStrictlyGE_Icx Rs) (injective_Icx_X Rs) hεinj φ

/-- The `Γ`-side leg becomes invertible in `D⁺`: this is Tag 0133. -/
noncomputable def gTotQIso :
    (IPlus Rs ⋙ Γ.mapCochainComplexPlus) ⋙ DerivedCategory.Plus.Q ≅
      totPlus Rs T hT0 ⋙ DerivedCategory.Plus.Q :=
  haveI _h : ∀ X : A, IsIso ((Functor.whiskerRight (gTotNat Γ Rs T ε hε hT0 hεinj)
      DerivedCategory.Plus.Q).app X) := fun X =>
    isIso_PlusQ_map _ (quasiIso_gammaToTot Γ T (Icx Rs) ε hε hT0
      (exists_isStrictlyGE_Icx Rs) (injective_Icx_X Rs) hεinj X)
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (gTotNat Γ Rs T ε hε hT0 hεinj) DerivedCategory.Plus.Q)
  asIso (Functor.whiskerRight (gTotNat Γ Rs T ε hε hT0 hεinj) DerivedCategory.Plus.Q)

/-- **The comparison map of Tag 09VX, abstractly.** -/
noncomputable def alpha (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) :
    TPlus T hT0 ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus :=
  Functor.whiskerRight (tTotNat Rs ν T hT0) DerivedCategory.Plus.Q ≫
    (gTotQIso Γ Rs T ε hε hT0 hεinj).inv ≫ (delta Γ Rs ν hν).hom

/-! ### The pin: the augmentation triangle -/

/-- The single-complex comparison for `Γ`, at the level of bounded below complexes. -/
noncomputable def singleGammaPlusIso :
    Γ ⋙ singlePlus B ≅ singlePlus A ⋙ Γ.mapCochainComplexPlus :=
  liftNatIso _ _ (CochainComplex.Plus.ι B)
    (singleMapHomologicalComplex Γ (ComplexShape.up ℤ) 0).symm

/-- The augmentation `Γ(X)[0] ⟶ Γ(I^•)`, as a natural transformation. -/
noncomputable def gammaNuNat : Γ ⋙ singlePlus B ⟶ IPlus Rs ⋙ Γ.mapCochainComplexPlus :=
  (singleGammaPlusIso Γ).hom ≫ Functor.whiskerRight ν Γ.mapCochainComplexPlus

omit [HasCoproducts.{0} B] [HasDerivedCategory B] [HasDerivedCategory A]
  [EnoughInjectives A] in
/-- The component of `gammaNuNat` at `X`, as a map of cochain complexes, is `gammaNu`. -/
lemma gammaNuNat_app_ι (X : A) :
    (CochainComplex.Plus.ι B).map ((gammaNuNat Γ Rs ν).app X) =
      gammaNu Γ (Icx Rs) (nucx Rs ν) X := by
  rw [gammaNu_eq, gammaNuNat, NatTrans.comp_app, Functor.map_comp, singleGammaPlusIso]
  congr 1
  exact liftNatIso_hom_app (Γ ⋙ singlePlus B) (singlePlus A ⋙ Γ.mapCochainComplexPlus)
    (CochainComplex.Plus.ι B) (singleMapHomologicalComplex Γ (ComplexShape.up ℤ) 0).symm X

/-- The augmentation `Γ(X)[0] ⟶ T(X)`, as a natural transformation. -/
noncomputable def epsNat : Γ ⋙ singlePlus B ⟶ TPlus T hT0 where
  app X := ObjectProperty.homMk (ε X)
  naturality _ _ φ := by
    apply (CochainComplex.Plus.ι B).map_injective
    simp only [Functor.map_comp]
    exact hε φ

/-- The right-hand side of the pin: the canonical map from the sections of `X` to the right
derived functor, through the resolution. -/
noncomputable def psi (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) :
    (Γ ⋙ singlePlus B) ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus :=
  Functor.whiskerRight (gammaNuNat Γ Rs ν) DerivedCategory.Plus.Q ≫ (delta Γ Rs ν hν).hom

/-- **The pin.** The comparison composed with the augmentation is the canonical map through
the resolution; in particular the comparison is compatible with the derived functor unit. -/
theorem epsNat_comp_alpha (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) :
    Functor.whiskerRight (epsNat Γ T ε hε hT0) DerivedCategory.Plus.Q ≫
        alpha Γ Rs ν T ε hε hT0 hεinj hν =
      psi Γ Rs ν hν := by
  have key : epsNat Γ T ε hε hT0 ≫ tTotNat Rs ν T hT0 =
      gammaNuNat Γ Rs ν ≫ gTotNat Γ Rs T ε hε hT0 hεinj := by
    refine NatTrans.ext (funext fun X => ?_)
    apply (CochainComplex.Plus.ι B).map_injective
    simp only [NatTrans.comp_app, Functor.map_comp, gammaNuNat_app_ι]
    exact eps_comp_tToTot Γ T (Icx Rs) ε hε hT0 (exists_isStrictlyGE_Icx Rs)
      (injective_Icx_X Rs) hεinj (nucx Rs ν) X
  have h2 : Functor.whiskerRight (epsNat Γ T ε hε hT0) DerivedCategory.Plus.Q ≫
      Functor.whiskerRight (tTotNat Rs ν T hT0) DerivedCategory.Plus.Q =
      Functor.whiskerRight (gammaNuNat Γ Rs ν) DerivedCategory.Plus.Q ≫
        (gTotQIso Γ Rs T ε hε hT0 hεinj).hom := by
    rw [← Functor.whiskerRight_comp, key, Functor.whiskerRight_comp]
    rfl
  rw [alpha, psi, ← Category.assoc, h2, Category.assoc, Iso.hom_inv_id_assoc]

/-! ### Non-vacuity: the comparison is invertible at every injective object -/

omit [HasCoproducts.{0} B] [HasDerivedCategory A] [EnoughInjectives A] in
/-- Every term of the single complex on an injective object is injective. -/
lemma injective_single_obj_X (X : A) [Injective X] (n : ℤ) :
    Injective (((single A (ComplexShape.up ℤ) 0).obj X).X n) := by
  by_cases hn : n = 0
  · subst hn
    exact Injective.of_iso (singleObjXSelf (ComplexShape.up ℤ) 0 X).symm inferInstance
  · refine ⟨fun {_ _} _ _ _ => ⟨0, ?_⟩⟩
    exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 X n hn).eq_of_tgt _ _

omit [HasCoproducts.{0} B] in
/-- At an injective object the derived functor unit is already invertible on the single
complex. -/
lemma isIso_unit_app_singlePlus (X : A) [Injective X] :
    IsIso (Γ.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj ((singlePlus A).obj X))) := by
  have h : ∀ n : ℤ, Injective ((((singlePlus A).obj X)).obj.X n) :=
    injective_single_obj_X X
  have h2 : ∀ n : ℤ, Injective (((HomotopyCategory.Plus.quotient A).obj
      ((singlePlus A).obj X)).obj.as.X n) := h
  infer_instance

omit [HasCoproducts.{0} B] in
/-- The right-hand side of the pin is invertible at every injective object. -/
lemma isIso_psi_app (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) (X : A) [Injective X] :
    IsIso ((psi Γ Rs ν hν).app X) := by
  have hq : IsIso (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient A).map (ν.app X))) :=
    (isIso_PlusQ_map_iff (B := A) (ν.app X)).1 (isIso_PlusQ_map (ν.app X) (hν X))
  have hu := isIso_unit_app_singlePlus Γ X
  have hinj2 : ∀ n : ℤ, Injective (((HomotopyCategory.Plus.quotient A).obj
      ((IPlus Rs).obj X)).obj.as.X n) := fun n => ((Rs.obj X).obj.X n).2
  have hnat := Γ.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient A).map (ν.app X))
  simp only [Functor.comp_map] at hnat
  have h1 : IsIso (Γ.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj ((singlePlus A).obj X)) ≫
      Γ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient A).map (ν.app X)))) := inferInstance
  rw [← hnat] at h1
  have h2 : IsIso (DerivedCategory.Plus.Qh.map (Γ.mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient A).map (ν.app X)))) :=
    IsIso.of_isIso_comp_right _ (Γ.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj ((IPlus Rs).obj X)))
  have h3 : IsIso (DerivedCategory.Plus.Q.map (Γ.mapCochainComplexPlus.map (ν.app X))) :=
    (isIso_PlusQ_map_iff (Γ.mapCochainComplexPlus.map (ν.app X))).2 h2
  rw [psi, NatTrans.comp_app, Functor.whiskerRight_app, gammaNuNat, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp]
  infer_instance

/-- **The comparison is an isomorphism at every injective object.** -/
theorem isIso_alpha_app (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) (X : A) [Injective X] :
    IsIso ((alpha Γ Rs ν T ε hε hT0 hεinj hν).app X) := by
  have h0 : IsIso (DerivedCategory.Plus.Q.map ((epsNat Γ T ε hε hT0).app X)) :=
    isIso_PlusQ_map _ (hεinj X inferInstance)
  have h1 := isIso_psi_app Γ Rs ν hν X
  have h := congrArg (fun k => NatTrans.app k X)
    (epsNat_comp_alpha Γ Rs ν T ε hε hT0 hεinj hν)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  have h2 : IsIso (DerivedCategory.Plus.Q.map ((epsNat Γ T ε hε hT0).app X) ≫
      (alpha Γ Rs ν T ε hε hT0 hεinj hν).app X) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Plus.Q.map ((epsNat Γ T ε hε hT0).app X)) _

/-! ### The packaged statement -/

include hεinj in
/-- **Stacks Project, Tag 09VX, abstract form.**  Let `Γ : A ⥤ B` be an additive functor
between abelian categories, `A` with enough injectives and admitting a functorial injective
resolution, and let `T : A ⥤ CochainComplex B ℤ` be an additive functor vanishing in negative
degrees, equipped with an augmentation `ε : Γ(X)[0] ⟶ T(X)` which is a quasi-isomorphism at
every injective object.  Then there is a natural transformation
`T ⟶ R⁺Γ ∘ (single 0)` in `D⁺(B)`, compatible with the augmentation and with the derived
functor unit, and it is an isomorphism at every injective object. -/
theorem exists_comparison (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) :
    ∃ α : TPlus T hT0 ⋙ DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus,
      Functor.whiskerRight (epsNat Γ T ε hε hT0) DerivedCategory.Plus.Q ≫ α =
          psi Γ Rs ν hν ∧
        ∀ X : A, Injective X → IsIso (α.app X) :=
  ⟨alpha Γ Rs ν T ε hε hT0 hεinj hν, epsNat_comp_alpha Γ Rs ν T ε hε hT0 hεinj hν,
    fun X _hX => isIso_alpha_app Γ Rs ν T ε hε hT0 hεinj hν X⟩

omit [HasCoproducts.{0} B] [T.Additive] in
/-- **Non-vacuity of the pin.**  If the zero natural transformation satisfied the pin, then
`Γ` would have zero sections at every injective object. -/
theorem isZero_of_pin_zero (hν : ∀ X : A, QuasiIso (nucx Rs ν X))
    (h : Functor.whiskerRight (epsNat Γ T ε hε hT0) DerivedCategory.Plus.Q ≫ 0 =
      psi Γ Rs ν hν) (X : A) [Injective X] :
    IsZero (((Γ ⋙ singlePlus B) ⋙ DerivedCategory.Plus.Q).obj X) := by
  have h1 := isIso_psi_app Γ Rs ν hν X
  have h0 : (psi Γ Rs ν hν).app X = 0 := by
    rw [← h]
    simp
  have h3 : IsIso (0 : ((Γ ⋙ singlePlus B) ⋙ DerivedCategory.Plus.Q).obj X ⟶
      (DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus).obj X) := h0 ▸ h1
  exact ((isIsoZero_iff_source_target_isZero _ _).1 h3).1

omit [HasCoproducts.{0} B] [T.Additive] in
/-- **The zero natural transformation fails the conclusion of `exists_comparison`.**  At an
object `X` whose complex `T(X)` is not acyclic, the zero natural transformation is not an
isomorphism, so it does not satisfy the second clause; and by `isZero_of_pin_zero` it does
not satisfy the pin either.  This is what makes the statement non-vacuous: the ambient
hom-type is inhabited by `0`, but neither clause is. -/
theorem not_isIso_zero_app (X : A)
    (hz : ¬ IsZero ((TPlus T hT0 ⋙ DerivedCategory.Plus.Q).obj X)) :
    ¬ IsIso ((0 : TPlus T hT0 ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus).app X) := by
  intro h
  refine hz ?_
  have h0 : (0 : TPlus T hT0 ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus).app X = 0 := rfl
  rw [h0] at h
  exact ((isIsoZero_iff_source_target_isZero _ _).1 h).1

include hεinj in
/-- **Stacks Project, Tag 09VX, abstract form, unconditional in the resolution.**  Under the
hypotheses above and functorial injective embeddings on `A` (Tags 0139/01DP), there are a
canonical map `ψ` from the sections of `X` to the right derived functor at the single complex
and a natural transformation `α : T ⟶ R⁺Γ(-[0])` with `Q(ε) ≫ α = ψ`, and both `ψ` and `α`
are isomorphisms at every injective object.

The last clause is what makes the statement non-vacuous: `α = 0` would force every
`Q(T(X))`, `X` injective, to be a zero object. -/
theorem exists_comparison_of_hasFunctorialInjectiveEmbeddings
    (hFIE : HasFunctorialInjectiveEmbeddings A) :
    ∃ (ψ' : (Γ ⋙ singlePlus B) ⋙ DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus)
      (α : TPlus T hT0 ⋙ DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus),
      Functor.whiskerRight (epsNat Γ T ε hε hT0) DerivedCategory.Plus.Q ≫ α = ψ' ∧
        (∀ X : A, Injective X → IsIso (ψ'.app X)) ∧
        (∀ X : A, Injective X → IsIso (α.app X)) := by
  obtain ⟨Rs, ν, hν⟩ := exists_resolutionData (A := A) hFIE
  exact ⟨psi Γ Rs ν hν, alpha Γ Rs ν T ε hε hT0 hεinj hν,
    epsNat_comp_alpha Γ Rs ν T ε hε hT0 hεinj hν,
    fun X _hX => isIso_psi_app Γ Rs ν hν X,
    fun X _hX => isIso_alpha_app Γ Rs ν T ε hε hT0 hεinj hν X⟩

end Main

end

end StacksDraft.DerivedSectionsComparison

end
