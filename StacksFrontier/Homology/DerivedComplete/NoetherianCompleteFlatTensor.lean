module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.Tor.Balancing




/-!
# Derived completion of tensor products and localizations

Let `I` be an ideal of a Noetherian ring `A`. If `M` is a finite `A`-module and
`N` is a flat `A`-module, then the derived `I`-adic completion of `M ⊗[A] N`
is its usual `I`-adic completion. The same conclusion holds for the localization
of `M` at one element of `A`.

## Main results

* `derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization` identifies
  derived completion with ordinary adic completion in both cases.

## References

* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AdicCompletionFlatTensor

end AdicCompletionFlatTensor
end


public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AdicCompletionFlatTensor

private def homologyMapFunctorIso {A : Type u} [CommRing A]
    (G : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [G.Additive] [G.PreservesHomology]
    (i : ℕ) :
    G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
      HomologicalComplex.homologyFunctor _ _ i ≅
    HomologicalComplex.homologyFunctor _ _ i ⋙ G :=
  NatIso.ofComponents (fun C => (C.sc i).mapHomologyIso G)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ i).map f) G)

set_option backward.isDefEq.respectTransparency false in
private def leftDerivedCompIso {A : Type u} [CommRing A]
    (F G H : ModuleCat.{u} A ⥤ ModuleCat.{u} A)
    [F.Additive] [G.Additive] [H.Additive] [G.PreservesHomology]
    (e : F ⋙ G ≅ H) (i : ℕ) : H.leftDerived i ≅ F.leftDerived i ⋙ G := by
  let c := ComplexShape.down ℕ
  let E : H.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor _ c i ≅
      F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor _ c i ⋙ G :=
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e c).symm _ ≪≫
      Functor.isoWhiskerLeft _ (homologyMapFunctorIso G i)
  refine NatIso.ofComponents (fun X =>
    ((ProjectiveResolution.of X).isoLeftDerivedObj H i) ≪≫ E.app _ ≪≫
      (G.mapIso ((ProjectiveResolution.of X).isoLeftDerivedObj F i)).symm) ?_
  intro X Y f
  let P := ProjectiveResolution.of X
  let Q := ProjectiveResolution.of Y
  let φ := ProjectiveResolution.lift f P Q
  have hc : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
    HomologicalComplex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Functor.comp_map, Iso.app_hom]
  rw [← Category.assoc, P.isoLeftDerivedObj_hom_naturality f Q φ hc H i]
  simp only [Category.assoc]
  rw [E.hom.naturality_assoc φ, ← G.map_comp, P.isoLeftDerivedObj_inv_naturality f Q φ hc F i]
  simp only [Functor.comp_map, G.map_comp]
  rfl

private def torTensorFlatIso {A : Type u} [CommRing A]
    (M N : ModuleCat.{u} A) [Module.Flat A N] (i : ℕ) :
    (Tor (ModuleCat.{u} A) i).obj (M ⊗ N) ≅
      (Tor (ModuleCat.{u} A) i).obj M ⋙ tensorRight N := by
  have : PreservesFiniteColimits (tensorRight N) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have : (tensorRight N).PreservesHomology := Functor.preservesHomologyOfExact _
  let e : tensorLeft M ⋙ tensorRight N ≅ tensorLeft (M ⊗ N) :=
    NatIso.ofComponents (fun X =>
      (α_ M X N) ≪≫ (tensorLeft M).mapIso (β_ X N) ≪≫ (α_ M N X).symm) (by
        intro X Y f
        dsimp
        simp only [associator_naturality_middle_assoc, Category.assoc,
          ← associator_inv_naturality_right]
        rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left]
        simp only [whiskerLeft_comp, Category.assoc])
  exact leftDerivedCompIso _ _ _ e i

set_option backward.isDefEq.respectTransparency false in
private theorem tor_tensor_flat_proZero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M N : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Flat A N] {i : ℕ} (hi : 0 < i) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor (ModuleCat.{u} A) i).obj (M ⊗ N)).map
        (torProZeroTransition I (Nat.sub_le n c)) = 0 := by
  obtain ⟨c, hc, h⟩ := _root_.tor_pro_zero I M hi
  refine ⟨c, hc, fun n hn => ?_⟩
  let e := torTensorFlatIso M N i
  have he := congrArg (fun k => k ≫ e.inv.app (torProZeroQuot I (n - c)))
    (e.hom.naturality (torProZeroTransition I (Nat.sub_le n c)))
  simpa only [Functor.comp_map, h n hn, Functor.map_zero, comp_zero, zero_comp,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using he

private theorem isIso_difference_of_uniform_proZero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasProductsOfShape ℕ C]
    (F : ℕᵒᵖ ⥤ C) (c : ℕ)
    (hF : ∀ n : ℕ, F.map (homOfLE (Nat.le_add_right n c)).op = 0) :
    IsIso (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) := by
  let X := fun n : ℕ => F.obj (Opposite.op n)
  let t : End (∏ᶜ X) := .of <| Pi.lift fun n => Pi.π X (n + 1) ≫
    F.map (homOfLE (Nat.le_succ n)).op
  have hp (k n : ℕ) : (t ^ k).asHom ≫ Pi.π X n =
      Pi.π X (n + k) ≫ F.map (homOfLE (Nat.le_add_right n k)).op := by
    induction k generalizing n with
    | zero => simp [X]
    | succ k ih =>
      rw [pow_succ, End.mul_asHom, Category.assoc, ih, ← Category.assoc,
        show t.asHom ≫ Pi.π X (n + k) = Pi.π X (n + k + 1) ≫
          F.map (homOfLE (Nat.le_succ (n + k))).op from Pi.lift_comp_π _ _,
        Category.assoc, ← F.map_comp]
      rfl
  have hz : t ^ c = 0 := by
    ext : 1
    apply Pi.hom_ext
    intro n
    rw [hp, hF]
    simp
  have ht : IsIso ((1 : End (∏ᶜ X)) - t).asHom :=
    (isUnit_iff_isIso _).mp (IsNilpotent.isUnit_one_sub ⟨c, hz⟩)
  have hd : (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫
      F.map (homOfLE (Nat.le_succ n)).op) = ((1 : End (∏ᶜ X)) - t).asHom := by
    apply Pi.hom_ext
    intro n
    rw [End.sub_asHom, End.one_asHom, Preadditive.sub_comp, Category.id_comp]
    simp only [t, Pi.lift_comp_π]
  rwa [hd]

private def adicCompletionCone {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) : Cone (AdicCompletionTor.adicQuotientSystem I M) where
  pt := ModuleCat.of A (AdicCompletion I M)
  π :=
    { app n := ModuleCat.ofHom (AdicCompletion.eval I M (n.unop + 1))
      naturality := by
        intro n m f
        ext x
        exact (AdicCompletion.transitionMap_comp_eval_apply I M
          (Nat.add_le_add_right (leOfHom f.unop) 1) x).symm }

/-- The `0`-th adic quotient of a module is trivial. -/
private theorem adicQuotient_zero_eq {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    (x y : M ⧸ (I ^ 0 • ⊤ : Submodule A M)) : x = y := by
  have : Subsingleton (M ⧸ (I ^ 0 • ⊤ : Submodule A M)) := by
    simp only [pow_zero, one_smul]
    infer_instance
  exact Subsingleton.elim _ _

private def adicCompletionConeIsLimit {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) : IsLimit (adicCompletionCone I M) where
  lift s := ModuleCat.ofHom
    { toFun x := ⟨fun n => match n with
          | 0 => 0
          | k + 1 => s.π.app (Opposite.op k) x,
        by
          intro m n h
          cases m with
          | zero => exact adicQuotient_zero_eq I M _ _
          | succ m =>
            cases n with
            | zero => omega
            | succ n =>
              have hn := ConcreteCategory.congr_hom (s.w (homOfLE (Nat.le_of_succ_le_succ h)).op) x
              change AdicCompletion.transitionMap I M h _ = _ at hn
              exact hn⟩
      map_add' x y := by
        apply AdicCompletion.ext
        intro n
        cases n with
        | zero => exact adicQuotient_zero_eq I M _ _
        | succ n => exact (s.π.app (Opposite.op n)).hom.map_add x y
      map_smul' a x := by
        apply AdicCompletion.ext
        intro n
        cases n with
        | zero => exact adicQuotient_zero_eq I M _ _
        | succ n => exact (s.π.app (Opposite.op n)).hom.map_smul a x }
  fac s n := by ext x; rfl
  uniq s m hm := by
    ext x
    apply AdicCompletion.ext
    intro n
    cases n with
    | zero => exact adicQuotient_zero_eq I M _ _
    | succ n => exact ConcreteCategory.congr_hom (hm (Opposite.op n)) x

private def limitAdicQuotientIso {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) :
    limit (AdicCompletionTor.adicQuotientSystem I M) ≅ ModuleCat.of A (AdicCompletion I M) :=
  (limit.isLimit _).conePointUniqueUpToIso (adicCompletionConeIsLimit I M)

private def limitTorZeroIso {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) :
    limit (AdicCompletionTor.torIdealPowerSystem I M 0) ≅ ModuleCat.of A (AdicCompletion I M) := by
  let e : AdicCompletionTor.torIdealPowerSystem I M 0 ≅ AdicCompletionTor.adicQuotientSystem I M :=
    Functor.isoWhiskerLeft _ ((Tor_iso_Tor' A 0).app M).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftDerivedZeroIsoSelf (tensorLeft M)) ≪≫
    (AdicCompletionTor.adicQuotientSystemTensorIso I M).symm
  exact HasLimit.isoOfNatIso e ≪≫ limitAdicQuotientIso I M

private theorem isZero_reflector_obj_zero
    {A : Type u} [CommRing A]
    (P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)))
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory) (adj : L ⊣ P.ι) :
    IsZero ((L ⋙ P.ι).obj 0) := by
  rw [IsZero.iff_id_eq_zero]
  have h : 𝟙 (L.obj 0) = 0 := (adj.homEquiv 0 (L.obj 0)).injective
    ((isZero_zero _).eq_of_src _ _)
  simpa using congrArg P.ι.map h

private theorem reflector_single_isLE
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun K => IsDerivedComplete I K).FullSubcategory)
    (adj : L ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun K => IsDerivedComplete I K).ι)
    (M : ModuleCat.{u} A) :
    ((L ⋙ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun K => IsDerivedComplete I K).ι).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).IsLE 0 := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  subst I
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K => IsDerivedComplete (Ideal.span (Set.range f)) K
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  have hzero := isZero_reflector_obj_zero P L adj
  have hS : S.IsLE 0 := by dsimp [S]; infer_instance
  have h := (CompletionAdjunction.derivedCompletion_finiteCohomologicalDimension A f L adj
    (0 : S ⟶ 0)).1
  have hz0 (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (0 : DerivedCategory (ModuleCat.{u} A))) :=
    (DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _)
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((L ⋙ P.ι).obj 0)) := (DerivedCategory.homologyFunctor _ i).map_isZero hzero
  have hh := h (by
    constructor
    · intro i hi
      have h1 := (DerivedCategory.isLE_iff S 0).mp hS i (by omega)
      exact h1.isIso (hz0 i) _
    · exact (hz0 0).epi _)
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have := hh.1 i (by omega)
  exact IsZero.of_iso (hz i) (asIso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((L ⋙ P.ι).map (0 : S ⟶ 0))))

/-- An object of `D(A)` with cohomology only in degree `0` is the single complex on it. -/
private theorem nonempty_iso_singleFunctor_of_homology
    {A : Type u} [CommRing A] (X : DerivedCategory (ModuleCat.{u} A)) (Y : ModuleCat.{u} A)
    (hzero : ∀ p : ℤ, p ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj X))
    (h0 : Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X ≅ Y)) :
    Nonempty (X ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Y) := by
  have : X.IsGE 0 := (DerivedCategory.isGE_iff X 0).2 fun p hp => hzero p (by omega)
  have : X.IsLE 0 := (DerivedCategory.isLE_iff X 0).2 fun p hp => hzero p (by omega)
  obtain ⟨Z, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  obtain ⟨h0⟩ := h0
  let e' : Z ≅ Y := ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Z).symm ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫ h0
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e'⟩

/-- If `Φ` agrees with adic completion on tensor products of a finite module with a flat
module, it agrees with adic completion on localizations of a finite module at one element. -/
private theorem isUsual_localization_of_isUsual_tensor
    (A : Type u) [CommRing A] (I : Ideal A)
    (Φ : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (htensor : ∀ (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        [AddCommGroup N] [Module A N] [Module.Flat A N],
      Nonempty (Φ.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (TensorProduct A M N))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (AdicCompletion I (TensorProduct A M N)))))
    (M Mf : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup Mf] [Module A Mf] (f : A) (φ : M →ₗ[A] Mf)
    [IsLocalizedModule (Submonoid.powers f) φ] :
    Nonempty (Φ.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A Mf)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I Mf))) := by
  let S := Localization.Away f
  let t : M →ₗ[A] TensorProduct A S M := TensorProduct.mk A S M 1
  let e : TensorProduct A M S ≃ₗ[A] Mf :=
    (TensorProduct.comm A M S).trans
      (IsLocalizedModule.linearEquiv (Submonoid.powers f) t φ)
  obtain ⟨h⟩ := htensor M S
  exact ⟨Φ.mapIso ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      e.symm.toModuleIso) ≪≫ h ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      ((AdicCompletion.congr I e).restrictScalars A).toModuleIso⟩

private theorem torIdealPowerSystem_isZero_limits
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M N : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Flat A N] {i : ℕ} (hi : 0 < i) :
    IsZero (limit (AdicCompletionTor.torIdealPowerSystem I (M ⊗ N) i)) ∧
      IsZero (AdicCompletionTor.firstDerivedInverseLimit
        (AdicCompletionTor.torIdealPowerSystem I (M ⊗ N) i)) := by
  obtain ⟨c, _, hc⟩ := tor_tensor_flat_proZero A I M N hi
  have hF := AdicCompletionTor.torIdealPowerSystem_uniform_proZero I (M ⊗ N) i c hc
  constructor
  · apply Rlim.Pro.isZero_limit_of_proZero
    intro n
    exact ⟨Opposite.op (n.unop + c), (homOfLE (Nat.le_add_right n.unop c)).op, hF n.unop⟩
  · have := isIso_difference_of_uniform_proZero
      (AdicCompletionTor.torIdealPowerSystem I (M ⊗ N) i) c hF
    exact isZero_cokernel_of_epi _

private theorem isUsual_tensor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K => IsDerivedComplete I K
    ∀ (L : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory), (L ⊣ P.ι) →
    ∀ (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Flat A N],
      Nonempty ((L ⋙ P.ι).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (M ⊗ N)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (AdicCompletion I (TensorProduct A M N)))) := by
  intro P L adj M N _ _
  obtain ⟨L', ⟨adj'⟩, _, hMilnor, _⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (M ⊗ N)
  let X := (L' ⋙ P.ι).obj S
  let e := P.ι.mapIso ((adj.leftAdjointUniq adj').app S)
  refine Nonempty.map (fun e' => e ≪≫ e') ?_
  apply nonempty_iso_singleFunctor_of_homology
  · intro p hp
    by_cases hpos : 0 < p
    · exact (DerivedCategory.isLE_iff X 0).mp
        (reflector_single_isLE A I I.fg_of_isNoetherianRing L' adj' (M ⊗ N)) p hpos
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, p = -(i : ℤ) := ⟨(-p).toNat, by omega⟩
      have hi : 0 < i := by omega
      obtain ⟨a, b, w, hs⟩ := hMilnor (M ⊗ N) i
      exact hs.exact.isZero_of_both_zeros
        ((torIdealPowerSystem_isZero_limits I M N (Nat.succ_pos i)).2.eq_of_src _ _)
        ((torIdealPowerSystem_isZero_limits I M N hi).1.eq_of_tgt _ _)
  · obtain ⟨a, b, w, hs⟩ := hMilnor (M ⊗ N) 0
    have : Mono b := hs.exact.mono_g
      ((torIdealPowerSystem_isZero_limits I M N (Nat.succ_pos 0)).2.eq_of_src _ _)
    have : Epi b := hs.epi_g
    have : IsIso b := isIso_of_mono_of_epi b
    exact ⟨asIso b ≪≫ limitTorZeroIso I (M ⊗ N)⟩

end AdicCompletionFlatTensor

end





public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AdicCompletionFlatTensor

/-- Let `I` be an ideal of a Noetherian ring `A`. Derived `I`-adic
completion agrees with ordinary `I`-adic completion for the tensor product of a finite
module with a flat module, and for the localization of a finite module at one element. -/
@[stacks 0EEU]
public theorem derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K ↦ IsDerivedComplete I K
    ∀ (L : Functor (DerivedCategory (ModuleCat.{u} A)) P.FullSubcategory),
    Nonempty (L ⊣ P.ι) →
    (∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K)
      ((L ⋙ P.ι).obj K)) →
    let isUsual (Q : Type u) [AddCommGroup Q] [Module A Q] : Prop :=
      Nonempty
        ((L ⋙ P.ι).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A Q)) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (AdicCompletion I Q)))
    (∀ (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        [AddCommGroup N] [Module A N] [Module.Flat A N],
      isUsual (TensorProduct A M N)) ∧
    (∀ (M Mf : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
        [AddCommGroup Mf] [Module A Mf] (f : A) (φ : M →ₗ[A] Mf)
        [IsLocalizedModule (Submonoid.powers f) φ],
      isUsual Mf) := by
  intro P L hAdj _hLim isUsual
  obtain ⟨adj⟩ := hAdj
  have htensor : ∀ (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
      [AddCommGroup N] [Module A N] [Module.Flat A N],
      isUsual (TensorProduct A M N) := by
    intro M N _ _ _ _ _ _
    exact isUsual_tensor A I T L adj (ModuleCat.of A M) (ModuleCat.of A N)
  refine ⟨htensor, ?_⟩
  intro M Mf _ _ _ _ _ f φ _
  exact isUsual_localization_of_isUsual_tensor A I (L ⋙ P.ι) htensor M Mf f φ

end AdicCompletionFlatTensor

end
