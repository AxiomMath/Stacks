module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleInjectiveComparison

/-!
# Derived lower shriek of the constant sheaf, from a comparison of cohomology

Let `J` be a Grothendieck topology on a site `C`, let `K` be one on a site `D`, and let

`L : D(Ab(C)) ⥤ D(Ab(D))`

be a left adjoint of the functor induced on unbounded derived categories by an exact restriction
functor `R : Ab(D) ⥤ Ab(C)`. This file proves that `L` carries the constant sheaf `ℤ` of `C`,
placed in degree zero, to the constant sheaf `ℤ` of `D`, placed in degree zero, provided two
things: that the unit of the adjunction is invertible, and that restriction identifies the
cohomology of `D` with the cohomology of `C` in every degree,

`H^n(C, R F) ≅ H^n(D, F)` naturally in `F`.

The conclusion is stated as invertibility of the *counit* of the adjunction at the single complex
on the constant sheaf of `D`. That is the sharp form: the counit is the canonical map
`L (R ℤ_D) ⟶ ℤ_D`, and `R ℤ_D` is the constant sheaf of `C` — see
`Stacks.Cohomology.DerivedLowerShriek.restriction_constantSheafIso` — so invertibility of the
counit says that the canonical comparison out of `L ℤ_C` is an isomorphism, rather than merely
that the two objects are isomorphic by some unspecified map.

## The argument

Two steps, neither of which needs anything about the sites beyond the cohomology comparison.

*The object `L ℤ_C` is concentrated in degree zero.* For a single complex on an injective object
`I` of `Ab(D)` the adjunction gives

`Hom(L ℤ_C[0], I[q]) ≅ Hom(ℤ_C[0], (R I)[q]) ≅ Ext^q(ℤ_C, R I) = H^q(C, R I)`,

which vanishes for `q > 0` because the cohomology comparison identifies it with `H^q(D, I)` and
`I` is injective, and for `q < 0` because the single complexes are in the heart of the canonical
t-structure. By `Stacks.Cohomology.DerivedLowerShriek.isZero_homology_of_subsingleton_hom_single`
that forces the homology of `L ℤ_C` to vanish away from degree zero, and an object of the
derived category that is both `IsGE 0` and `IsLE 0` is a single complex.

*Its degree-zero term is the constant sheaf of `D`.* Writing `L ℤ_C[0] ≅ Y[0]`, the same chain of
bijections computes `Hom(Y, T)` as `H^0(C, R T) ≅ H^0(D, T) ≅ Hom(ℤ_D, T)`, naturally in `T`, so
Yoneda gives `Y ≅ ℤ_D`. The unit being invertible makes `L` fully faithful, and for a fully
faithful left adjoint the counit is invertible exactly at the objects in its essential image.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.isZero_homology_of_subsingleton_hom_single`: vanishing of
  the degree-`q` homology of an object of the derived category all of whose maps to single
  complexes on injectives in degree `q` are trivial.
* `Stacks.Cohomology.DerivedLowerShriek.exists_iso_single_of_leftAdjoint_ext_vanishing`: the image
  under a left adjoint of a single complex is a single complex, given the vanishing of the
  positive-degree `Ext` groups out of its term into the restrictions of the injectives.
* `Stacks.Cohomology.DerivedLowerShriek.nonempty_iso_single_of_coyoneda_iso`: Yoneda identifies
  the degree-zero term of that single complex.
* `Stacks.Cohomology.DerivedLowerShriek.constantSheafCoyonedaIso`: degree-zero cohomology of
  abelian sheaves is corepresented by the constant sheaf `ℤ`.
* `Stacks.Cohomology.DerivedLowerShriek.isIso_counit_app_single_constantSheaf`: the conclusion
  described above.

## References

* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.DerivedLowerShriek

universe w v u

attribute [local instance] HasDerivedCategory.standard

/-! ### Vanishing of homology against single complexes on injectives -/

/-- **Maps into the single complexes on injective objects detect homology.** If every map from
`X` to the single complex in degree `q` on an injective object is trivial, then the degree-`q`
homology of `X` vanishes.

The point is that `K.homology q` is realized as the kernel of a map of injective objects by
`Stacks.HomologyComparison.exists_injective_homology_kernel`, so it is killed by a map which the
hypothesis forces to be zero. -/
theorem isZero_homology_of_subsingleton_hom_single
    {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    (X : DerivedCategory A) (q : ℤ)
    (h : ∀ (I : A) [Injective I],
      Subsingleton (X ⟶ (DerivedCategory.singleFunctor A q).obj I)) :
    IsZero ((DerivedCategory.homologyFunctor A q).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  obtain ⟨I, J, hI, hJ, f, g, z, hm, he⟩ :=
    Stacks.HomologyComparison.exists_injective_homology_kernel K q
  let es := (DerivedCategory.singleFunctorIsoCompQ A q).app I
  have hf : DerivedCategory.Q.map f = 0 := by
    simpa using congrArg (fun k => e.hom ≫ k ≫ es.hom)
      ((h I).elim (e.inv ≫ DerivedCategory.Q.map f ≫ es.inv) 0)
  have hfun : (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map f = 0 := by
    have hn := (DerivedCategory.homologyFunctorFactors A q).hom.naturality f
    dsimp at hn
    rw [hf, Functor.map_zero, zero_comp] at hn
    exact (cancel_epi ((DerivedCategory.homologyFunctorFactors A q).hom.app K)).mp
      (hn.symm.trans comp_zero.symm)
  have hK : IsZero (K.homology q) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_mono (HomologicalComplex.homologyMap f q)).mp
    simp [show HomologicalComplex.homologyMap f q = 0 from hfun]
  exact hK.of_iso
    ((DerivedCategory.homologyFunctor A q).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors A q).app K)

/-! ### The image of a single complex under a left adjoint -/

/-- **A left adjoint of an exact restriction carries a single complex to a single complex**, as
soon as the positive-degree `Ext` groups out of its degree-zero term into the restrictions of the
injective objects vanish.

Those `Ext` groups compute, through the adjunction, the maps from the image to the single
complexes on injectives in nonzero degree; the negative degrees are handled by the canonical
t-structure instead, the single complexes lying in its heart. -/
theorem exists_iso_single_of_leftAdjoint_ext_vanishing
    {A B : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    [Category* B] [Abelian B] [HasExt.{v} B]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (L : DerivedCategory B ⥤ DerivedCategory A) (adj : L ⊣ R.mapDerivedCategory)
    (Z : B)
    (h : ∀ (I : A) [Injective I] (n : ℕ),
      Subsingleton (Abelian.Ext.{v} Z (R.obj I) (n + 1))) :
    ∃ Y, Nonempty (L.obj ((DerivedCategory.singleFunctor B 0).obj Z) ≅
      (DerivedCategory.singleFunctor A 0).obj Y) := by
  let X := L.obj ((DerivedCategory.singleFunctor B 0).obj Z)
  have hz (q : ℤ) (hq : q ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor A q).obj X) := by
    apply isZero_homology_of_subsingleton_hom_single
    intro I hI
    let e : (X ⟶ (DerivedCategory.singleFunctor A q).obj I) ≃
        ((DerivedCategory.singleFunctor B 0).obj Z ⟶
          (DerivedCategory.singleFunctor B q).obj (R.obj I)) := (adj.homEquiv _ _).trans
      (((R.mapDerivedCategorySingleFunctor q).app I).homToEquiv)
    refine e.subsingleton_congr.mpr ?_
    obtain hq | hq := lt_or_gt_of_ne hq
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -q - 1 by omega)
      let t := ((DerivedCategory.singleFunctors B).shiftIso ((n + 1 : ℕ) : ℤ) q 0
        (by omega)).app (R.obj I)
      exact (Abelian.Ext.homEquiv.trans t.homToEquiv).subsingleton_congr.mp (h I n)
    · exact ⟨fun f g => by
        rw [DerivedCategory.TStructure.t.zero f 0 q hq,
          DerivedCategory.TStructure.t.zero g 0 q hq]⟩
  have : X.IsGE 0 := (DerivedCategory.isGE_iff X 0).mpr fun q hq => hz q (by omega)
  have : X.IsLE 0 := (DerivedCategory.isLE_iff X 0).mpr fun q hq => hz q (by omega)
  exact DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0

/-- **Yoneda identifies the degree-zero term.** If a left adjoint carries the single complex on
`Z` to the single complex on `Y`, and if the functor corepresented by `Z` along the restriction
is corepresented by `W` instead, then the term is `W`.

The composite bijection `(Y ⟶ T) ≅ (Z ⟶ R T) ≅ (W ⟶ T)` is natural in `T`, so `Y ≅ W`. -/
theorem nonempty_iso_single_of_coyoneda_iso
    {A B : Type*} [Category.{v} A] [Abelian A] [Category.{v} B] [Abelian B]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (L : DerivedCategory B ⥤ DerivedCategory A) (adj : L ⊣ R.mapDerivedCategory)
    (Z : B) (W Y : A)
    (e : L.obj ((DerivedCategory.singleFunctor B 0).obj Z) ≅
      (DerivedCategory.singleFunctor A 0).obj Y)
    (h : R ⋙ coyoneda.obj (op Z) ≅ coyoneda.obj (op W)) :
    Nonempty (L.obj ((DerivedCategory.singleFunctor B 0).obj Z) ≅
      (DerivedCategory.singleFunctor A 0).obj W) := by
  let SA := DerivedCategory.singleFunctor A 0
  let SB := DerivedCategory.singleFunctor B 0
  let fa := Functor.FullyFaithful.ofFullyFaithful SA
  let fb := Functor.FullyFaithful.ofFullyFaithful SB
  let eh (T : A) : (Y ⟶ T) ≃ (Z ⟶ R.obj T) :=
    fa.homEquiv.trans (e.symm.homFromEquiv.trans
      ((adj.homEquiv _ _).trans
        (((R.mapDerivedCategorySingleFunctor 0).app T).homToEquiv.trans
          fb.homEquiv.symm)))
  let i : coyoneda.obj (op Y) ≅ R ⋙ coyoneda.obj (op Z) :=
    NatIso.ofComponents (fun T => (eh T).toIso) (by
      intro T T' f
      ext g
      show eh T' (g ≫ f) = eh T g ≫ R.map f
      apply SB.map_injective
      simp only [eh, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_symm_apply, Iso.homFromEquiv_apply,
        Iso.symm_inv, Iso.homToEquiv, Equiv.coe_fn_mk, Functor.map_comp,
        Functor.FullyFaithful.map_preimage, Category.assoc]
      rw [← Category.assoc, adj.homEquiv_naturality_right]
      simp only [Category.assoc]
      congr 1
      exact (R.mapDerivedCategorySingleFunctor 0).hom.naturality f)
  exact ⟨e ≪≫ SA.mapIso (coyoneda.preimageIso (i ≪≫ h)).unop.symm⟩

/-! ### Restriction carries the constant sheaf to the constant sheaf -/

/-- **Restriction along a continuous functor of sites carries the constant sheaf `ℤ` to the
constant sheaf `ℤ`.** This is compatibility of restriction with sheafification,
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`, read at the constant
presheaf on `ℤ`.

It is what makes the counit of
`Stacks.Cohomology.DerivedLowerShriek.isIso_counit_app_single_constantSheaf` a map *out of*
`L ℤ_C`: the counit at `ℤ_D[0]` has source `L (R ℤ_D)[0]`, and this identifies `R ℤ_D` with
`ℤ_C`. -/
def restriction_constantSheafIso
    {C D : Type*} [Category* C] [Category* D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
    (a : A) :
    (constantSheaf J A).obj a ≅ (u.sheafPushforwardContinuous A J K).obj
      ((constantSheaf K A).obj a) :=
  (u.pushforwardContinuousSheafificationCompatibility A J K).app ((Functor.const _).obj a)

/-! ### Degree-zero cohomology is corepresented by the constant sheaf -/

/-- **Degree-zero cohomology of abelian sheaves is corepresented by the constant sheaf `ℤ`.**
This is the additive bijection `Ext^0(ℤ_C, F) ≅ (ℤ_C ⟶ F)` of `CategoryTheory.Ext.addEquiv₀`,
read as a natural isomorphism of functors to types. -/
def constantSheafCoyonedaIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] :
    Sheaf.functorH.{u + 1, u + 1} J 0 ⋙ forget AddCommGrpCat.{u + 1} ≅
      coyoneda.obj (op ((constantSheaf J AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) :=
  NatIso.ofComponents (fun F => Abelian.Ext.addEquiv₀.toEquiv.toIso) fun f => by
    ext x
    exact Sheaf.H.addEquiv₀_map f x

/-! ### The counit at the constant sheaf -/

/-- **`L ℤ = ℤ`.** Let `R : Ab(D) ⥤ Ab(C)` be an exact restriction functor of abelian sheaves and
`L : D(Ab(C)) ⥤ D(Ab(D))` a left adjoint of the functor it induces on unbounded derived
categories. If the unit of the adjunction is invertible and if `R` identifies the cohomology of
`D` with the cohomology of `C` in every degree, then the counit of the adjunction is invertible at
the single complex on the constant sheaf `ℤ` of `D`.

Since the counit at `ℤ_D[0]` is the canonical map `L (R ℤ_D)[0] ⟶ ℤ_D[0]`, and `R ℤ_D` is the
constant sheaf of `C`, this says that the canonical comparison from `L ℤ_C` to `ℤ_D` is an
isomorphism — which is **Stacks 0H0Z** for any `L` of this shape.

The cohomology comparison enters twice: in degree zero to identify the term of the single
complex, and in positive degrees to make it a single complex at all. -/
theorem isIso_counit_app_single_constantSheaf
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify K AddCommGrpCat.{u + 1}]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf K AddCommGrpCat.{u + 1})]
    (R : Sheaf K AddCommGrpCat.{u + 1} ⥤ Sheaf J AddCommGrpCat.{u + 1})
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (L : DerivedCategory (Sheaf J AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u + 1}))
    (adj : L ⊣ R.mapDerivedCategory) (hu : IsIso adj.unit)
    (h : ∀ n : ℕ, R ⋙ Sheaf.functorH.{u + 1, u + 1} J n ≅
      Sheaf.functorH.{u + 1, u + 1} K n) :
    IsIso (adj.counit.app ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf K AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  let Z := (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let W := (constantSheaf K AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_single_of_leftAdjoint_ext_vanishing R L adj Z (by
    intro I hI n
    have : Subsingleton ((Sheaf.functorH.{u + 1, u + 1} K (n + 1)).obj I) :=
      inferInstanceAs (Subsingleton (Sheaf.H I (n + 1)))
    exact (ConcreteCategory.bijective_of_isIso ((h (n + 1)).hom.app I)).1.subsingleton)
  let h0 : R ⋙ coyoneda.obj (op Z) ≅ coyoneda.obj (op W) :=
    Functor.isoWhiskerLeft R (constantSheafCoyonedaIso J).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (h 0) (forget AddCommGrpCat.{u + 1}) ≪≫
      constantSheafCoyonedaIso K
  obtain ⟨i⟩ := nonempty_iso_single_of_coyoneda_iso R L adj Z W Y e h0
  have := adj.fullyFaithfulLOfIsIsoUnit.full
  have := adj.fullyFaithfulLOfIsIsoUnit.faithful
  exact adj.isIso_counit_app_of_iso i.symm

end Stacks.Cohomology.DerivedLowerShriek

end
