module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge

/-!
# The injective horseshoe for `ℕ`-indexed resolutions of objects

The horseshoe lemma for injective resolutions is available in this project for cochain complexes
indexed by `ℤ`: `CategoryTheory.ShortComplex.ShortExact.exists_shortExact_injectiveResolution`
(Stacks 013T) for a short exact sequence of complexes, and
`StacksDraft.CartanEilenbergResolutions.horseshoeProperty` for a short exact sequence of objects
with the resolutions of *both* outer terms prescribed. Mathlib's
`CategoryTheory.InjectiveResolution`, on the other hand, is indexed by `ℕ`, and it is the
`ℕ`-indexed form that computes `CategoryTheory.Functor.rightDerived`.

This file transports the `ℤ`-indexed horseshoe to the `ℕ`-indexed world along
`CochainComplex.InjectiveResolution.toNatResolution`, which needs two degree-zero comparisons:
the degree-zero component of the round-trip isomorphism
`CochainComplex.extendRestrictionUpNatIso`, and the degree-zero component of the augmentation of
`toNatResolution`.

Both of those carry the transport isomorphism `HomologicalComplex.restrictionXIso` explicitly.
That is deliberate: `(K.restriction ComplexShape.embeddingUpNat).X 0` and `K.X 0` are
definitionally equal but not syntactically equal, so a statement which elides the comparison is
accepted by the elaborator and then blocks `Category.assoc` and `Category.id_comp`, neither of
which can rewrite under a composition whose intermediate object is only definitionally the one
written. Carrying the isomorphism keeps every composite honestly typed.

## Main results

* `CochainComplex.extendRestrictionUpNatIso_hom_f_zero`: in degree zero the round trip
  `ℤ → ℕ → ℤ` is the comparison isomorphism of the extension by zero.
* `CochainComplex.InjectiveResolution.toNatResolution_ι_f_zero`: the degree-zero component of the
  augmentation of the `ℕ`-indexed resolution obtained from a `ℤ`-indexed one is the degree-zero
  component of the given augmentation.
* `CategoryTheory.ShortComplex.ShortExact.exists_injectiveResolution_shortExact`: the horseshoe
  itself, with the two commuting squares and the degreewise splitting.

## References

* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
* [Stacks Project, Tag 013I](https://stacks.math.columbia.edu/tag/013I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **The round trip `ℤ → ℕ → ℤ` in degree zero.** For a cochain complex `K` of `A` vanishing in
the negative degrees, the degree-zero component of `CochainComplex.extendRestrictionUpNatIso` is
the inverse of the comparison isomorphism of the extension by zero, read through the transport
`HomologicalComplex.restrictionXIso` between `K.X 0` and the degree-zero term of the restriction.
The identity holds because `CochainComplex.toExtendRestrictionUpNat` is the extension of the
identity of that restriction, so `ComplexShape.Embedding.homRestrict` carries it back to the
identity. -/
theorem extendRestrictionUpNatIso_hom_f_zero (K : CochainComplex A ℤ) [K.IsStrictlyGE 0]
    (h : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ)) :
    K.extendRestrictionUpNatIso.hom.f 0 =
      (HomologicalComplex.restrictionXIso K ComplexShape.embeddingUpNat h).inv ≫
        (HomologicalComplex.extendXIso (K.restriction ComplexShape.embeddingUpNat)
          ComplexShape.embeddingUpNat h).inv := by
  have hh : h = rfl := rfl
  subst hh
  have hR : ComplexShape.embeddingUpNat.homRestrict K.toExtendRestrictionUpNat = 𝟙 _ :=
    ComplexShape.Embedding.homRestrict_liftExtend _ _ _
  have h1 := congrArg (fun ψ ↦ HomologicalComplex.Hom.f ψ 0) hR
  rw [ComplexShape.Embedding.homRestrict_f _ _
      (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ)), HomologicalComplex.id_f] at h1
  have h2 := (Iso.eq_inv_comp _).2 h1
  rw [Category.comp_id] at h2
  exact (Iso.eq_comp_inv _).2 h2

namespace InjectiveResolution

variable {X : A}

/-- **The augmentation of `CochainComplex.InjectiveResolution.toNatResolution` in degree zero.**
Passing a `ℤ`-indexed injective resolution of `X[0]` vanishing in the negative degrees to the
`ℕ`-indexed world leaves the degree-zero component of the augmentation unchanged, up to the
canonical identification of `X` with the degree-zero term of `X[0]` on either side and the
transport between the degree-zero term of the resolving complex and that of its restriction. -/
theorem toNatResolution_ι_f_zero
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X))
    [R.cocomplex.IsStrictlyGE 0] (h : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ)) :
    (toNatResolution R).ι.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ R.ι.f 0 ≫
          (HomologicalComplex.restrictionXIso R.cocomplex ComplexShape.embeddingUpNat h).inv := by
  have hι : (toNatResolution R).ι.f 0 =
      (HomologicalComplex.extendXIso
          ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).obj X)
          ComplexShape.embeddingUpNat h).inv ≫
        ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 h).hom ≫
          R.ι ≫ R.cocomplex.extendRestrictionUpNatIso.hom).f 0 ≫
        (HomologicalComplex.extendXIso (R.cocomplex.restriction ComplexShape.embeddingUpNat)
          ComplexShape.embeddingUpNat h).hom := rfl
  rw [hι, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f _ _ _ _ h,
    CochainComplex.extendRestrictionUpNatIso_hom_f_zero _ h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end InjectiveResolution

end CochainComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The identification of the degree-zero term of `X[0]` with `X`, for `ℕ`-indexed cochain
complexes, is natural in `X`. -/
private theorem singleObjXSelf_naturality {X Y : A} (f : X ⟶ Y) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).hom ≫ f =
      f ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 Y).hom := by
  have h := (HomologicalComplex.single_map_f_self (ComplexShape.up ℕ) 0 f).symm.trans
    (CochainComplex.single₀_map_f_zero f)
  rw [← Category.assoc] at h
  exact (Iso.comp_inv_eq _).1 h

/-- A morphism of `ℤ`-indexed resolutions which lifts `u` in degree zero restricts to a morphism
of the `ℕ`-indexed resolutions which lifts `u` in degree zero. -/
private theorem toNatResolution_ι_f_zero_comp {X Y : A} (u : X ⟶ Y)
    {R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)}
    {R' : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj Y)}
    [R.cocomplex.IsStrictlyGE 0] [R'.cocomplex.IsStrictlyGE 0] (φ : R.cocomplex ⟶ R'.cocomplex)
    (hf : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))
    (h0 : R.ι.f 0 ≫ φ.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ u ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv ≫ R'.ι.f 0) :
    (CochainComplex.InjectiveResolution.toNatResolution R).ι.f 0 ≫
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingUpNat).f 0 =
      u ≫ (CochainComplex.InjectiveResolution.toNatResolution R').ι.f 0 := by
  rw [CochainComplex.InjectiveResolution.toNatResolution_ι_f_zero _ hf,
    CochainComplex.InjectiveResolution.toNatResolution_ι_f_zero _ hf,
    HomologicalComplex.restrictionMap_f' _ _ hf]
  dsimp only [CochainComplex.single₀, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, CochainComplex.InjectiveResolution.toNatResolution_cocomplex]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (R.ι.f 0), h0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).hom),
    singleObjXSelf_naturality u]
  exact Category.assoc _ _ _

/-- **The injective horseshoe for `ℕ`-indexed resolutions of objects.** Let `A` be an abelian
category with enough injectives and let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of
objects of `A`. Then there are injective resolutions `J₁`, `J₂`, `J₃` of the three terms and a
short exact sequence `0 ⟶ J₁ ⟶ J₂ ⟶ J₃ ⟶ 0` of the resolving complexes over it: the two squares
built from the augmentations commute in degree zero, and the sequence is split in every degree.

This is the `ℕ`-indexed form of Stacks 013T for a sequence of objects. It is deduced from the
`ℤ`-indexed `StacksDraft.CartanEilenbergResolutions.horseshoeProperty`, with the two outer
resolutions prescribed to be the extensions by zero of arbitrary `ℕ`-indexed ones, by restricting
the resulting sequence of complexes back along `ComplexShape.embeddingUpNat`.

The degreewise splitting is what makes the sequence stay short exact under an arbitrary additive
functor applied degreewise; it is not read off the twisted-biproduct construction of the
horseshoe but recovered afterwards from
`CategoryTheory.ShortComplex.ShortExact.splittingOfInjective`, the first term of the sequence in
degree `n` being the injective object `J₁.cocomplex.X n`. -/
@[stacks 013T "the `ℕ`-graded form for a short exact sequence of objects, with the degreewise \
  splitting of the resulting sequence of resolving complexes"]
theorem exists_injectiveResolution_shortExact [EnoughInjectives A]
    {S : ShortComplex A} (hS : S.ShortExact) :
    ∃ (J₁ : InjectiveResolution S.X₁) (J₂ : InjectiveResolution S.X₂)
      (J₃ : InjectiveResolution S.X₃) (f : J₁.cocomplex ⟶ J₂.cocomplex)
      (g : J₂.cocomplex ⟶ J₃.cocomplex) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      J₁.ι.f 0 ≫ f.f 0 = S.f ≫ J₂.ι.f 0 ∧ J₂.ι.f 0 ≫ g.f 0 = S.g ≫ J₃.ι.f 0 ∧
      ∀ n, ∃ _ : (ShortComplex.mk (f.f n) (g.f n)
        (congrFun (congrArg HomologicalComplex.Hom.f w) n)).Splitting, True := by
  have hf : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  obtain ⟨K₁⟩ := HasInjectiveResolution.out (Z := S.X₁)
  obtain ⟨K₃⟩ := HasInjectiveResolution.out (Z := S.X₃)
  obtain ⟨T₂, f', g', w', ι₂, hse', hge₂, hinj₂, hqi₂, hc₁, hc₂⟩ :=
    StacksDraft.CartanEilenbergResolutions.horseshoeProperty A S hS
      K₁.cochainComplex K₃.cochainComplex inferInstance inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) K₁.ι' K₃.ι' inferInstance inferInstance
  -- the three `ℤ`-indexed resolutions, the outer two coming from `K₁` and `K₃`
  let R₁ := K₁.toCochainComplexResolution
  let R₃ := K₃.toCochainComplexResolution
  let R₂ : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj S.X₂) :=
    { cocomplex := T₂
      boundedBelow := (CochainComplex.plus_iff A T₂).2 ⟨0, hge₂⟩
      injective := hinj₂
      ι := ι₂
      quasiIso := hqi₂ }
  have i₂ : R₂.cocomplex.IsStrictlyGE 0 := hge₂
  let f : (CochainComplex.InjectiveResolution.toNatResolution R₁).cocomplex ⟶
      (CochainComplex.InjectiveResolution.toNatResolution R₂).cocomplex :=
    HomologicalComplex.restrictionMap f' ComplexShape.embeddingUpNat
  let g : (CochainComplex.InjectiveResolution.toNatResolution R₂).cocomplex ⟶
      (CochainComplex.InjectiveResolution.toNatResolution R₃).cocomplex :=
    HomologicalComplex.restrictionMap g' ComplexShape.embeddingUpNat
  have hw : f ≫ g = 0 :=
    HomologicalComplex.hom_ext _ _ fun n ↦
      congrFun (congrArg HomologicalComplex.Hom.f w') (ComplexShape.embeddingUpNat.f n)
  refine ⟨CochainComplex.InjectiveResolution.toNatResolution R₁,
    CochainComplex.InjectiveResolution.toNatResolution R₂,
    CochainComplex.InjectiveResolution.toNatResolution R₃, f, g, hw, ?_, ?_, ?_, ?_⟩
  · -- short exactness, degree by degree
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
    exact (HomologicalComplex.shortExact_iff_degreewise_shortExact
      (ShortComplex.mk f' g' w')).1 hse' (ComplexShape.embeddingUpNat.f n)
  · -- the first square
    refine toNatResolution_ι_f_zero_comp S.f (R := R₁) (R' := R₂) f' hf ?_
    have h0 := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ (0 : ℤ)) hc₁
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      Category.assoc] at h0
    exact h0
  · -- the second square
    refine toNatResolution_ι_f_zero_comp S.g (R := R₂) (R' := R₃) g' hf ?_
    have h0 := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ (0 : ℤ)) hc₂
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      Category.assoc] at h0
    exact h0
  · -- the degreewise splitting
    intro n
    have hdeg : (ShortComplex.mk (f.f n) (g.f n)
        (congrFun (congrArg HomologicalComplex.Hom.f hw) n)).ShortExact :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact
        (ShortComplex.mk f' g' w')).1 hse' (ComplexShape.embeddingUpNat.f n)
    have : Injective ((CochainComplex.InjectiveResolution.toNatResolution R₁).cocomplex.X n) :=
      (CochainComplex.InjectiveResolution.toNatResolution R₁).injective n
    exact ⟨hdeg.splittingOfInjective, trivial⟩

end CategoryTheory.ShortComplex.ShortExact

end
