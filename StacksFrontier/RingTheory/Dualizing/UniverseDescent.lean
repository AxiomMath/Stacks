module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.RingTheory.Dualizing.Complex
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Dualizing complexes in the module universe of the ring

Whether a Noetherian ring `A : Type u` admits a dualizing complex does not depend on the universe
of the modules in which the complex is taken: a dualizing complex in `D(ModuleCat.{v} A)` gives one
in `D(ModuleCat.{u} A)`.

## Main results

* `Dualizing.isDualizingComplex_uliftFunctor` — the universe lift of a dualizing complex to
  `ModuleCat.{max u v} A` is dualizing.
* `Dualizing.isDualizingComplex_of_uliftFunctor` — an object of `D(ModuleCat.{u} A)` whose universe
  lift is dualizing is dualizing.
* `Dualizing.exists_isDualizingComplex_of_isDualizingComplex` — a dualizing complex in any module
  universe yields one in the universe of the ring.

## Implementation notes

The descent goes through a common lift. A dualizing complex `K` in `D(ModuleCat.{v} A)` is
pseudo-coherent, so it is represented by a bounded-above complex `P` of finite free modules; each
term of `P` is `u`-small, so `P` shrinks termwise to a complex `P₀` of `ModuleCat.{u} A`, and the
lifts of `P` and `P₀` to `ModuleCat.{max u v} A` are isomorphic. The lift of `K` is dualizing
because the identity of `A` is a localization ([Stacks, Tag 0A7G]), and the three conditions of
[Stacks, Tag 0A7B] descend along the fully faithful exact lift `ModuleCat.{u} A ⥤
ModuleCat.{max u v} A`: finiteness of cohomology because the lift commutes with cohomology, the
homothety condition because the lift identifies the endomorphism complexes of a bounded complex of
injectives with those of its lift, and finite injective dimension through the Ext criterion of
[Stacks, Tag 0DW2], since the lift is injective on maps into bounded-below objects (it preserves
injective modules, hence bounded-below complexes of injectives and their homotopy classes of maps).

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0DW2](https://stacks.math.columbia.edu/tag/0DW2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

/-! ### The universe lift on maps into bounded-below objects -/

/-- Finite injective dimension descends along the universe lift, for a bounded-below object with
finite cohomology: by the Ext criterion of [Stacks, Tag 0DW2] it suffices that the Ext groups out
of the cyclic modules vanish in high degrees, and they do after the lift. -/
private theorem hasFiniteInjectiveDimension_of_uliftFunctor
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [K.IsGE a]
    (hfinite : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K))
    (h : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      ((ModuleCat.uliftFunctor.{v, u} R).mapDerivedCategory.obj K)) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K := by
  let U := ModuleCat.uliftFunctor.{v, u} R
  have key : ∀ (X Y : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [Y.IsGE a],
      Subsingleton (U.mapDerivedCategory.obj X ⟶ U.mapDerivedCategory.obj Y) →
        Subsingleton (X ⟶ Y) := by
    intro X Y a _ h
    have := h
    obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE Y a
    obtain ⟨J, i, hi, hJinj, hJ⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L a
    let eY : Y ≅ DerivedCategory.Q.obj J := eL ≪≫ asIso (DerivedCategory.Q.map i)
    have : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
    let JU := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
    have : CochainComplex.IsStrictlyGE JU a :=
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := J) U a).2 hJ
    have : ∀ n, Injective (JU.X n) := fun n => U.injective_obj_of_injective (hJinj n)
    have : CochainComplex.IsKInjective JU := CochainComplex.isKInjective_of_injective JU a
    let q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
    let q' := HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
    let UH := U.mapHomotopyCategory (ComplexShape.up ℤ)
    let Xh := DerivedCategory.Qh.objPreimage X
    let eX : DerivedCategory.Qh.obj Xh ≅ X := DerivedCategory.Qh.objObjPreimageIso X
    let eJ : DerivedCategory.Qh.obj (q.obj J) ≅ Y :=
      (DerivedCategory.quotientCompQhIso _).app J ≪≫ eY.symm
    let eUX : DerivedCategory.Qh.obj (UH.obj Xh) ≅ U.mapDerivedCategory.obj X :=
      (U.mapDerivedCategoryFactorsh.app Xh).symm ≪≫ U.mapDerivedCategory.mapIso eX
    let eUJ : DerivedCategory.Qh.obj (q'.obj JU) ≅ U.mapDerivedCategory.obj Y :=
      (DerivedCategory.quotientCompQhIso _).app JU ≪≫
        (U.mapDerivedCategoryFactors.app J).symm ≪≫ U.mapDerivedCategory.mapIso eY.symm
    have : Subsingleton (DerivedCategory.Qh.obj (UH.obj Xh) ⟶
        DerivedCategory.Qh.obj (q'.obj JU)) :=
      (Iso.homCongr eUX eUJ).subsingleton
    have h' : Subsingleton (UH.obj Xh ⟶ q'.obj JU) :=
      (CochainComplex.IsKInjective.Qh_map_bijective (UH.obj Xh) JU).injective.subsingleton
    have : Subsingleton (UH.obj Xh ⟶ UH.obj (q.obj J)) :=
      @Equiv.subsingleton _ _
        (Iso.homCongr (Iso.refl _) ((U.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app J)) h'
    have : Subsingleton (Xh ⟶ q.obj J) := UH.map_injective.subsingleton
    have : Subsingleton (DerivedCategory.Qh.obj Xh ⟶ DerivedCategory.Qh.obj (q.obj J)) :=
      (CochainComplex.IsKInjective.Qh_map_bijective Xh J).surjective.subsingleton
    exact (Iso.homCongr eX eJ).symm.subsingleton
  obtain ⟨c, b, hAmp⟩ := h
  let Kplus : DerivedCategory.Plus (ModuleCat.{u} R) := ⟨K, ⟨a, inferInstance⟩⟩
  refine (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_quotient_ext_vanishing
    (⊥ : Ideal R) bot_le Kplus hfinite).2 ⟨b, fun J _ i hi => ?_⟩
  let M := ModuleCat.of R (Shrink.{u} (R ⧸ J))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hvan :=
    (StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      (U.mapDerivedCategory.obj K) c b).1.1 hAmp (U.obj M) i (Or.inr hi)
  change Subsingleton ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
    (U.obj M) ⟶ (U.mapDerivedCategory.obj K)⟦i⟧) at hvan
  have : Subsingleton (U.mapDerivedCategory.obj X ⟶ U.mapDerivedCategory.obj (K⟦i⟧)) :=
    @Equiv.subsingleton _ _ (Iso.homCongr ((U.mapDerivedCategorySingleFunctor 0).app M)
      ((U.mapDerivedCategory.commShiftIso i).app K)) hvan
  have : (K⟦i⟧).IsGE (a - i) :=
    DerivedCategory.TStructure.t.isGE_shift K a i (a - i) (by omega)
  exact key X (K⟦i⟧) (a - i) inferInstance

/-- The scalar homothety of a complex and that of its universe lift differ by isomorphisms of
complexes, so one is a quasi-isomorphism exactly when the other is. -/
private theorem quasiIso_homothety_uliftFunctor_iff {A : Type u} [CommRing A]
    (J : CochainComplex (ModuleCat.{v} A) ℤ) :
    QuasiIso (homothety
      (((ModuleCat.uliftFunctor.{w, v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ↔
      QuasiIso (homothety J) := by
  let U := ModuleCat.uliftFunctor.{w, v} A
  let V := AddCommGrpCat.uliftFunctor.{w, max u v}
  let JU := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let eH : (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj (liftedEndomorphismComplex J) ≅
      liftedEndomorphismComplex JU :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => ((AddEquiv.ulift.trans AddEquiv.ulift).trans
        ((cochainAddEquivOfFullyFaithful U J J n).trans AddEquiv.ulift.symm)).toAddCommGrpIso)
  let eA : V.obj (AddCommGrpCat.of (ULift.{v} A)) ≅ AddCommGrpCat.of (ULift.{max v w} A) :=
    ((AddEquiv.ulift.trans AddEquiv.ulift).trans AddEquiv.ulift.symm).toAddCommGrpIso
  let eS := (Functor.mapCochainComplexSingleFunctor V 0).app
      (AddCommGrpCat.of (ULift.{v} A)) ≪≫
    (CochainComplex.singleFunctor AddCommGrpCat 0).mapIso eA
  have he : eS.inv ≫ (V.mapHomologicalComplex (ComplexShape.up ℤ)).map (homothety J) ≫
      eH.hom = homothety JU := by
    apply HomologicalComplex.from_single_hom_ext
    ext a
    simp only [Functor.mapHomologicalComplex_obj_X, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, Functor.comp_obj, CochainComplex.shiftFunctor_obj_X',
      Functor.mapCochainComplexSingleFunctor, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      homothety, cochainAddEquivOfFullyFaithful, Category.assoc, HomologicalComplex.comp_f,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom, eqToIso.inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      AddCommGrpCat.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, JU, U, V, eS, eA, eH]
    show ULift.up ((a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 J)).map U) =
      ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 JU))
    apply ULift.ext
    calc
      ((a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 J)).map U) =
          a.down • ((CochainComplex.HomComplex.Cochain.ofHom (𝟙 J)).map U) := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro i j hij
        simp only [CochainComplex.HomComplex.Cochain.map_v,
          CochainComplex.HomComplex.Cochain.smul_v, U.map_smul]
      _ = _ := by
        rw [CochainComplex.HomComplex.Cochain.map_ofHom,
          (U.mapHomologicalComplex (ComplexShape.up ℤ)).map_id]
  rw [← he, quasiIso_iff_comp_left, quasiIso_iff_comp_right,
    HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ V]

/-- **Descent of dualizing complexes along the universe lift.** An object of
`D(ModuleCat.{u} A)` whose lift to `D(ModuleCat.{max u v} A)` is a dualizing complex is itself a
dualizing complex. -/
theorem isDualizingComplex_of_uliftFunctor {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDualizingComplex ((ModuleCat.uliftFunctor.{v, u} A).mapDerivedCategory.obj K)) :
    IsDualizingComplex K := by
  let U := ModuleCat.uliftFunctor.{v, u} A
  let e (i : ℤ) := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso U i).app K
  have hfinite (i : ℤ) : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
    @Module.Finite.equiv A _ _ _ _ _ _ _ (hK.finiteCohomology i)
      ((e i).toLinearEquiv.trans (ULift.moduleEquiv (R := A)))
  obtain ⟨a, b, I, hGE, hLE, hIinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
  have hUge : (U.mapDerivedCategory.obj K).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have : K.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    have hz := (DerivedCategory.isGE_iff _ a).mp hUge i hi
    apply (IsZero.iff_id_eq_zero _).mpr
    apply U.map_injective
    rw [U.map_id, U.map_zero]
    exact (hz.of_iso (e i).symm).eq_of_src _ _
  refine ⟨hasFiniteInjectiveDimension_of_uliftFunctor K a hfinite hK.finiteInjectiveDimension,
    hfinite, ?_⟩
  intro J hJ hJinj hbounds
  obtain ⟨c, d, hc, hd⟩ := hbounds
  let JU := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  have hJUinj (i : ℤ) : Injective (JU.X i) := U.injective_obj_of_injective (hJinj i)
  have hJUrep : Nonempty (DerivedCategory.Q.obj JU ≅ U.mapDerivedCategory.obj K) :=
    ⟨(U.mapDerivedCategoryFactors.app J).symm ≪≫ U.mapDerivedCategory.mapIso hJ.some⟩
  have hJU := hK.homothetyQuasiIso JU hJUrep hJUinj
    ⟨c, d, (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := J) U c).mpr hc,
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := J) U d).mpr hd⟩
  exact (quasiIso_homothety_uliftFunctor_iff J).mp hJU

/-- **The universe lift of a dualizing complex is a dualizing complex.** The identity of `A` is a
localization, along which dualizing complexes extend ([Stacks, Tag 0A7G]), and derived extension
of scalars along the identity is the universe lift. -/
theorem isDualizingComplex_uliftFunctor {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    IsDualizingComplex ((ModuleCat.uliftFunctor.{u, v} A).mapDerivedCategory.obj K) := by
  have : IsLocalization (⊥ : Submonoid A) A := IsLocalization.self bot_le
  exact isDualizingComplex_of_iso
    (StacksDraft.Perfect.derivedExtensionScalarsId
      ((ModuleCat.uliftFunctor.{u, v} A).mapDerivedCategory.obj K))
    (isDualizingComplex_localization (B := A) (⊥ : Submonoid A) K hK)

/-! ### Shrinking a complex of small modules -/

/-- A complex of modules whose terms are `u`-small, shrunk termwise to `ModuleCat.{u}`. -/
private noncomputable def shrinkComplex {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{v} A) ℤ) [∀ i, Small.{u} (P.X i)] :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X i := ModuleCat.of A (Shrink.{u} (P.X i))
  d i j := ModuleCat.ofHom ((Shrink.linearEquiv A (P.X j)).symm.toLinearMap.comp
    ((P.d i j).hom.comp (Shrink.linearEquiv A (P.X i)).toLinearMap))
  shape i j h := by
    rw [P.shape i j h]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Shrink.linearEquiv A (P.X k)).injective
    have h := congrArg (fun g : P.X i ⟶ P.X k => g.hom
      (Shrink.linearEquiv A (P.X i) x)) (P.d_comp_d i j k)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply, map_zero] using h

/-- The universe lift of the termwise shrinking of a complex of small modules is the complex. -/
private noncomputable def shrinkComplexULiftIso {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) [∀ i, Small.{u} (P.X i)] :
    ((ModuleCat.uliftFunctor.{max u v, u} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (shrinkComplex P) ≅ P := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    ((ULift.moduleEquiv (R := A)).trans (Shrink.linearEquiv A (P.X i))).toModuleIso) ?_
  intro i j _
  ext x
  change (P.d i j).hom (Shrink.linearEquiv A (P.X i) x.down) =
    Shrink.linearEquiv A (P.X j) ((Shrink.linearEquiv A (P.X j)).symm
      ((P.d i j).hom (Shrink.linearEquiv A (P.X i) x.down)))
  rw [LinearEquiv.apply_symm_apply]

/-! ### The main result -/

/-- **A dualizing complex can be taken in the module universe of the ring.** If a Noetherian ring
`A : Type u` has a dualizing complex in `D(ModuleCat.{v} A)` for some universe `v`, it has one in
`D(ModuleCat.{u} A)`. The lift of the given complex to `ModuleCat.{max u v} A` is dualizing; being
pseudo-coherent it is represented by a bounded-above complex of finite free modules, which shrinks
to `ModuleCat.{u} A`; and the shrunk complex is dualizing because its lift is isomorphic to the
dualizing lift. -/
theorem exists_isDualizingComplex_of_isDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A] {K : DerivedCategory (ModuleCat.{v} A)}
    (hK : IsDualizingComplex K) :
    ∃ L : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex L := by
  let V := ModuleCat.uliftFunctor.{u, v} A
  let K' := V.mapDerivedCategory.obj K
  have hK' : IsDualizingComplex K' := isDualizingComplex_uliftFunctor K hK
  have hPC : StacksDraft.PseudoCoherence.IsPseudoCoherent K' :=
    pseudoCoherent_of_finiteInjectiveDimension_finiteCohomology K'
      hK'.finiteInjectiveDimension hK'.finiteCohomology
  obtain ⟨P, hP, ⟨eP⟩⟩ := hPC
  have (i : ℤ) : Module.Finite A (P.X i) := (hP.finiteFree i).1
  have (i : ℤ) : Small.{u} (P.X i) := Module.Finite.small.{u} A (P.X i)
  let L := DerivedCategory.Q.obj (shrinkComplex P)
  let U := ModuleCat.uliftFunctor.{max u v, u} A
  let e : U.mapDerivedCategory.obj L ≅ K' :=
    U.mapDerivedCategoryFactors.app (shrinkComplex P) ≪≫
      DerivedCategory.Q.mapIso (shrinkComplexULiftIso P) ≪≫ eP
  exact ⟨L, isDualizingComplex_of_uliftFunctor L (isDualizingComplex_of_iso e.symm hK')⟩

end Dualizing

end
