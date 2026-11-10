module

public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.CechTerms
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
import all StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.DerivedAdjunction
import all StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.CechTerms

/-!
# The counit isomorphism and the equivalence in a large universe

Third part of `StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence`.
It contains the invertibility of the counit of the derived restriction-of-scalars adjunction on
derived complete complexes, the resulting equivalence of derived complete objects in the
universe `max uA uB v`, the case of derived complete modules and of complexes with complete
terms, and the reduction lemmas to quotient rings of small cardinality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe uA uB v u w

namespace CompleteRestrictScalarsEquivalence

set_option backward.isDefEq.respectTransparency false


open StacksDraft.TotalComplexQuasiIso
open scoped ZeroObject

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open scoped DirectSum

open scoped ModuleCat.Algebra

open HomologicalComplex

open scoped ChangeOfRings

private theorem rankOne_unit_iso
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] (f : A →+* B) :
    let P := ModuleCat.of A (ULift.{v} (ULift.{uB} A))
    let Q := ModuleCat.of B (ULift.{v} (ULift.{uA} B))
    ∃ e : (ModuleCat.extendScalars.{uA, uB, max uA uB v} f).obj P ≅ Q,
      ∀ a : A, e.hom ((ModuleCat.extendRestrictScalarsAdj.{max uA uB v} f).unit.app P
        (ULift.up (ULift.up a))) = ULift.up (ULift.up (f a)) := by
  dsimp only
  let : Algebra A B := f.toAlgebra
  let P := ModuleCat.of A (ULift.{v} (ULift.{uB} A))
  let Q := ModuleCat.of B (ULift.{v} (ULift.{uA} B))
  let g : P ⟶ (ModuleCat.restrictScalars f).obj Q := ModuleCat.ofHom (X := P) (Y :=
    (ModuleCat.restrictScalars f).obj Q) {
    toFun x := ULift.up (ULift.up (f x.down.down))
    map_add' x y := by apply ULift.ext; apply ULift.ext; exact map_add f _ _
    map_smul' a x := by apply ULift.ext; apply ULift.ext; exact map_mul f _ _ }
  let e := (ModuleCat.extendRestrictScalarsAdj.{max uA uB v} f).homEquiv P Q |>.symm g
  have he (x : P) : e ((1 : B) ⊗ₜ[A,f] x) = g x :=
    congrArg (fun k : P ⟶ (ModuleCat.restrictScalars f).obj Q => k x)
      (((ModuleCat.extendRestrictScalarsAdj.{max uA uB v} f).homEquiv P Q).apply_symm_apply g)
  have hex (b : B) (x : P) : e (b ⊗ₜ[A,f] x) = b • g x := by
    have h := e.hom.map_smul b ((1 : B) ⊗ₜ[A,f] x)
    change e (b • ((1 : B) ⊗ₜ[A,f] x)) = b • e ((1 : B) ⊗ₜ[A,f] x) at h
    change e ((b * 1) ⊗ₜ[A,f] x) = b • e ((1 : B) ⊗ₜ[A,f] x) at h
    simpa only [mul_one, he] using h
  let inv (x : Q) : (ModuleCat.extendScalars.{uA, uB, max uA uB v} f).obj P :=
    x.down.down • ((1 : B) ⊗ₜ[A,f] (ULift.up (ULift.up 1)))
  have hright : Function.RightInverse inv e := by
    intro x
    obtain ⟨⟨x⟩⟩ := x
    simp only [inv, map_smul, he]
    change ULift.up (ULift.up (x * f 1)) = ULift.up (ULift.up x)
    rw [map_one, mul_one]
  have hleft : Function.LeftInverse inv e := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      change (e (z + z')).down.down • _ = _
      rw [map_add]
      change ((e z).down.down + (e z').down.down) • _ = _
      rw [add_smul]
      exact congrArg₂ (· + ·) hz hz'
    | tmul b x =>
      change B at b
      obtain ⟨⟨x⟩⟩ := x
      rw [hex]
      change (b * f x) • ((1 : B) ⊗ₜ[A,f] (ULift.up (ULift.up (1 : A)))) =
        b ⊗ₜ[A,f] (ULift.up (ULift.up x))
      change ((b * f x) * 1) ⊗ₜ[A,f] (ULift.up (ULift.up (1 : A))) = _
      rw [mul_one]
      have hx : ULift.up (ULift.up x) = x • (ULift.up (ULift.up (1 : A)) : P) := by
        apply ULift.ext
        apply ULift.ext
        exact (mul_one x).symm
      rw [hx, TensorProduct.tmul_smul]
      change (b * f x) ⊗ₜ[A,f] _ = (f x * b) ⊗ₜ[A,f] _
      rw [mul_comm]
  let iso := (LinearEquiv.ofBijective e.hom ⟨hleft.injective, hright.surjective⟩).toModuleIso
  exact ⟨iso, fun a => he _⟩

private theorem preservesFiniteLimits_extendScalars_of_flat
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{uA, uB, max uA uB v} f) := by
  let : Algebra A B := f.toAlgebra
  let : Module.Flat A B := hf
  let : (ModuleCat.extendScalars.{uA, uB, max uA uB v} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uA uB v} f).left_adjoint_additive
  have h : ∀ S : ShortComplex (ModuleCat.{max uA uB v} A), S.Exact →
      (S.map (ModuleCat.extendScalars.{uA, uB, max uA uB v} f)).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact B hS
  have hh : PreservesFiniteLimits (ModuleCat.extendScalars.{uA, uB, max uA uB v} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{uA, uB, max uA uB v} f) :=
    ((Functor.exact_tfae (ModuleCat.extendScalars.{uA, uB, max uA uB v} f)).out 2 4).mp h
  exact hh.1
private theorem bijective_precomp_scalarExtensionUnit
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max uA uB v} A))]
    (K : DerivedCategory (ModuleCat.{max uA uB v} A))
    (hK : IsDerivedComplete I K) :
    let P := ModuleCat.of A (ULift.{v} (ULift.{uB} A))
    let adj := ModuleCat.extendRestrictScalarsAdj.{max uA uB v} (algebraMap A B)
    Function.Bijective (fun g : (DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj P)) ⟶ K =>
      (DerivedCategory.singleFunctor _ 0).map (adj.unit.app P) ≫ g) := by
  let P := ModuleCat.of A (ULift.{v} (ULift.{uB} A))
  let res := ModuleCat.restrictScalars.{max uA uB v} (algebraMap A B)
  let H := ModuleCat.uliftFunctor.{v, max uA uB} A
  let g₀ : (ModuleCat.uliftFunctor.{uB} A).obj (ModuleCat.of A A) ⟶
      (ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B B) := ModuleCat.ofHom {
    toFun x := ULift.up (algebraMap A B x.down)
    map_add' x y := by apply ULift.ext; exact map_add _ _ _
    map_smul' a x := by apply ULift.ext; exact map_mul _ _ _ }
  have h := bijective_precomp_algebraMap A B I hI hflat hquot g₀ (fun a => rfl) H K hK
  obtain ⟨e, he⟩ := rankOne_unit_iso.{uA, uB, v} A B (algebraMap A B)
  let adj := ModuleCat.extendRestrictScalarsAdj.{max uA uB v} (algebraMap A B)
  have hu : adj.unit.app P ≫ res.map e.hom = H.map g₀ := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨⟨x⟩⟩ := x
    exact he x
  let S := DerivedCategory.singleFunctor (ModuleCat.{max uA uB v} A) 0
  apply bijective_precomp_of_iso_square _ (S.map (H.map g₀)) (Iso.refl _)
    (S.mapIso (res.mapIso e)) _ K h
  simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom]
  change S.map (H.map g₀) = S.map (adj.unit.app P) ≫ S.map (res.map e.hom)
  rw [← S.map_comp, hu]

private theorem isZero_module_of_rankOne_hom_eq_zero
    (A : Type uA) [CommRing A] (M : ModuleCat.{max uA uB v} A)
    (h : ∀ f : ModuleCat.of A (ULift.{v} (ULift.{uB} A)) ⟶ M, f = 0) : IsZero M := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  let f : ModuleCat.of A (ULift.{v} (ULift.{uB} A)) ⟶ M :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton A M x).comp
      (ULift.moduleEquiv.trans ULift.moduleEquiv).toLinearMap)
  have hx := congrArg (fun g : ModuleCat.of A (ULift.{v} (ULift.{uB} A)) ⟶ M =>
    g (ULift.up (ULift.up 1))) (h f)
  simpa [f] using hx

private theorem bijective_map_of_isIso_unit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (X Y : C) [IsIso (adj.unit.app Y)] :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  have he (f : X ⟶ Y) : adj.homEquiv X (F.obj Y) (F.map f) =
      f ≫ adj.unit.app Y := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      adj.homEquiv_naturality_left f (𝟙 (F.obj Y))
  refine ⟨?_, ?_⟩
  · intro f g h
    apply (cancel_mono (adj.unit.app Y)).mp
    simpa only [he] using congrArg (adj.homEquiv X (F.obj Y)) h
  · intro f
    refine ⟨adj.homEquiv X (F.obj Y) f ≫ inv (adj.unit.app Y), ?_⟩
    apply (adj.homEquiv X (F.obj Y)).injective
    rw [he]
    simp

private theorem exists_restrictScalars_derivedAdjunction_isIso_counit
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max uA uB v} A))] :
    ∃ (G : DerivedCategory (ModuleCat.{max uA uB v} A) ⥤
        DerivedCategory (ModuleCat.{max uA uB v} B))
      (adj : (ModuleCat.restrictScalars.{max uA uB v}
        (algebraMap A B)).mapDerivedCategory ⊣ G),
      ∀ K, IsDerivedComplete I K → IsIso (adj.counit.app K) := by
  let R := ModuleCat.restrictScalars.{max uA uB v} (algebraMap A B)
  let L := ModuleCat.extendScalars.{uA, uB, max uA uB v} (algebraMap A B)
  let adj := ModuleCat.extendRestrictScalarsAdj.{max uA uB v} (algebraMap A B)
  let : L.Additive := adj.left_adjoint_additive
  let : L.IsLeftAdjoint := ⟨R, ⟨adj⟩⟩
  let : PreservesFiniteColimits L := inferInstance
  let : PreservesFiniteLimits L := preservesFiniteLimits_extendScalars_of_flat A B
    (algebraMap A B) (RingHom.flat_algebraMap_iff.mpr hflat)
  let adj₁ := adj.mapDerivedCategory
  obtain ⟨G, ⟨adj₂⟩⟩ := exists_restrictScalars_derivedAdjunction.{uA, uB, v}
    A B (algebraMap A B)
  have hε (K : DerivedCategory (ModuleCat.{max uA uB v} A))
      (hK : IsDerivedComplete I K) : IsIso (adj₂.counit.app K) := by
    apply isIso_of_bijective_single_postcomp
      (ModuleCat.of A (ULift.{v} (ULift.{uB} A)))
      (isZero_module_of_rankOne_hom_eq_zero A)
    intro n
    apply (bijective_postcomp_counit_iff_precomp_unit adj₁ adj₂ _ K).mpr
    apply bijective_precomp_derivedUnit adj
    apply bijective_precomp_singleUnit adj
    exact bijective_precomp_single_shift (adj.unit.app _) K n
      (bijective_precomp_scalarExtensionUnit A B I hI hflat hquot (K⟦n⟧)
        (isDerivedComplete_shift A I K hK n))
  exact ⟨G, adj₂, hε⟩

theorem isEquivalence_restrictScalars_large
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max uA uB v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max uA uB v} B))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{max uA uB v} A)) :=
      fun K => IsDerivedComplete I K
    let Q : ObjectProperty (DerivedCategory (ModuleCat.{max uA uB v} B)) :=
      fun K => IsDerivedComplete (I.map (algebraMap A B)) K
    let F := (ModuleCat.restrictScalars.{max uA uB v} (algebraMap A B)).mapDerivedCategory
    ∀ hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj),
      (P.lift (Q.ι ⋙ F) hF).IsEquivalence := by
  dsimp only
  let R := ModuleCat.restrictScalars.{max uA uB v} (algebraMap A B)
  let P : ObjectProperty (DerivedCategory (ModuleCat.{max uA uB v} A)) :=
    fun K => IsDerivedComplete I K
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{max uA uB v} B)) :=
    fun K => IsDerivedComplete (I.map (algebraMap A B)) K
  intro hF
  obtain ⟨G, adj₂, hε₀⟩ :=
    exists_restrictScalars_derivedAdjunction_isIso_counit A B I hI hflat hquot
  have hε (K : P.FullSubcategory) : IsIso (adj₂.counit.app K.obj) := hε₀ K.obj K.property
  let : R.mapDerivedCategory.ReflectsIsomorphisms := reflectsIsomorphisms_mapDerivedCategory R
  apply isEquivalence_lift_of_counit adj₂ P Q hF _ hε
  intro K
  apply (isDerivedComplete_restrictScalars_iff
    A B (algebraMap A B) I (G.obj K.obj)).mp
  have := hε K
  exact isDerivedComplete_of_iso A I (asIso (adj₂.counit.app K.obj)).symm K.property

/-- Countable products exist in the derived category of `R`-modules, in every universe. -/
private theorem hasProductsOfShape_derivedCategory_moduleCat (R : Type u) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} R)) := by
  have := moduleCat_hasExactLimitsOfShape_discrete.{w} R ℕ
  exact Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- The derived universe-lift functor preserves countable products. -/
private theorem preservesLimitsOfShape_discrete_mapDerivedCategory_uliftFunctor
    (R : Type u) [CommRing R] :
    PreservesLimitsOfShape (Discrete ℕ) (ModuleCat.uliftFunctor.{w, v} R).mapDerivedCategory := by
  have := moduleCat_hasExactLimitsOfShape_discrete.{v} R ℕ
  have := moduleCat_hasExactLimitsOfShape_discrete.{max v w} R ℕ
  have := hasProductsOfShape_derivedCategory_moduleCat.{u, v} R
  have := hasProductsOfShape_derivedCategory_moduleCat.{u, max v w} R
  have := preservesSmallestLimits_of_preservesLimits (F := ModuleCat.uliftFunctor.{w, v} R)
  exact CategoryTheory.Functor.preservesProducts_mapDerivedCategory ℕ _

private theorem exists_restrictScalars_iso_of_isDerivedCompleteModule
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (M : ModuleCat.{v} A) (hM : IsDerivedCompleteModule I M) :
    ∃ N : ModuleCat.{v} B,
      Nonempty ((ModuleCat.restrictScalars (algebraMap A B)).obj N ≅ M) := by
  have := hasProductsOfShape_derivedCategory_moduleCat.{uA, max uA uB v} A
  have := hasProductsOfShape_derivedCategory_moduleCat.{uB, max uA uB v} B
  let U := ModuleCat.uliftFunctor.{max uA uB, v} A
  have := preservesLimitsOfShape_discrete_mapDerivedCategory_uliftFunctor.{v, uA, max uA uB} A
  let P : ObjectProperty (DerivedCategory (ModuleCat.{max uA uB v} A)) :=
    fun K => IsDerivedComplete I K
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{max uA uB v} B)) :=
    fun K => IsDerivedComplete (I.map (algebraMap A B)) K
  let R := ModuleCat.restrictScalars.{max uA uB v} (algebraMap A B)
  let hR : ∀ K : Q.FullSubcategory, P (R.mapDerivedCategory.obj K.obj) :=
    fun K => (isDerivedComplete_restrictScalars_iff
      A B (algebraMap A B) I K.obj).mpr K.property
  let F := P.lift (Q.ι ⋙ R.mapDerivedCategory) hR
  let : F.IsEquivalence := isEquivalence_restrictScalars_large A B I hI hflat hquot hR
  let X : P.FullSubcategory := ⟨U.mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M),
      isDerivedComplete_map A I U.mapDerivedCategory _ hM⟩
  let Y := F.objPreimage X
  let e := P.ι.mapIso (F.objObjPreimageIso X)
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{max uA uB v} B) 0).obj Y.obj
  let eA : R.obj N ≅ U.obj M :=
    (KoszulLiftReflectionAudit.homologyMapDerivedCategoryObjIso R Y.obj 0).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max uA uB v} A) 0).mapIso e ≪≫
    KoszulLiftReflectionAudit.homologyMapDerivedCategoryObjIso U _ 0 ≪≫
    U.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M)
  have : Small.{v} N := small_of_injective
    (ULift.down_injective.comp eA.toLinearEquiv.injective)
  let N' := ModuleCat.of B (Shrink.{v} N)
  let eB : (ModuleCat.uliftFunctor.{max uA uB, v} B).obj N' ≅ N :=
    (ULift.moduleEquiv.trans (Shrink.linearEquiv B N)).toModuleIso
  let e' : U.obj ((ModuleCat.restrictScalars.{v} (algebraMap A B)).obj N') ≅ U.obj M :=
    R.mapIso eB ≪≫ eA
  exact ⟨N', ⟨U.preimageIso e'⟩⟩

private theorem bijective_map_restrictScalars_of_isDerivedCompleteModule
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))]
    (M N : ModuleCat.{v} B)
    (hN : IsDerivedCompleteModule (I.map (algebraMap A B)) N) :
    Function.Bijective ((ModuleCat.restrictScalars (algebraMap A B)).map :
      (M ⟶ N) → _) := by
  have := hasProductsOfShape_derivedCategory_moduleCat.{uA, max uA uB v} A
  have := hasProductsOfShape_derivedCategory_moduleCat.{uB, max uA uB v} B
  let UA := ModuleCat.uliftFunctor.{max uA uB, v} A
  let UB := ModuleCat.uliftFunctor.{max uA uB, v} B
  have := preservesLimitsOfShape_discrete_mapDerivedCategory_uliftFunctor.{v, uB, max uA uB} B
  let R := ModuleCat.restrictScalars.{max uA uB v} (algebraMap A B)
  let R₀ := ModuleCat.restrictScalars.{v} (algebraMap A B)
  let U := UB ⋙ DerivedCategory.singleFunctor (ModuleCat.{max uA uB v} B) 0
  let V := UA ⋙ DerivedCategory.singleFunctor (ModuleCat.{max uA uB v} A) 0
  let e : U ⋙ R.mapDerivedCategory ≅ R₀ ⋙ V :=
    Functor.isoWhiskerLeft UB (R.mapDerivedCategorySingleFunctor 0)
  have hY : IsDerivedComplete (I.map (algebraMap A B)) (U.obj N) :=
    isDerivedComplete_of_iso B (I.map (algebraMap A B))
      ((UB.mapDerivedCategorySingleFunctor 0).app N)
      (isDerivedComplete_map B (I.map (algebraMap A B)) UB.mapDerivedCategory _ hN)
  obtain ⟨G, adj, hε⟩ :=
    exists_restrictScalars_derivedAdjunction_isIso_counit A B I hI hflat hquot
  let : R.mapDerivedCategory.ReflectsIsomorphisms := reflectsIsomorphisms_mapDerivedCategory R
  have : IsIso (adj.counit.app (R.mapDerivedCategory.obj (U.obj N))) :=
    hε _ ((isDerivedComplete_restrictScalars_iff
      A B (algebraMap A B) I (U.obj N)).mpr hY)
  have : IsIso (R.mapDerivedCategory.map (adj.unit.app (U.obj N)) ≫
      adj.counit.app (R.mapDerivedCategory.obj (U.obj N))) := by
    have ht := adj.left_triangle_components (U.obj N)
    change R.mapDerivedCategory.map (adj.unit.app (U.obj N)) ≫
      adj.counit.app (R.mapDerivedCategory.obj (U.obj N)) = 𝟙 _ at ht
    rw [ht]
    infer_instance
  have : IsIso (R.mapDerivedCategory.map (adj.unit.app (U.obj N))) :=
    IsIso.of_isIso_comp_right _ (adj.counit.app (R.mapDerivedCategory.obj (U.obj N)))
  have : IsIso (adj.unit.app (U.obj N)) :=
    isIso_of_reflects_iso _ R.mapDerivedCategory
  have hb := bijective_map_of_isIso_unit adj (U.obj M) (U.obj N)
  refine ⟨R₀.map_injective, ?_⟩
  intro f
  obtain ⟨g, hg⟩ := hb.surjective (e.hom.app M ≫ V.map f ≫ e.inv.app N)
  refine ⟨U.preimage g, ?_⟩
  apply V.map_injective
  apply (cancel_epi (e.hom.app M)).mp
  have he := e.hom.naturality (U.preimage g)
  change R.mapDerivedCategory.map (U.map (U.preimage g)) ≫ e.hom.app N =
    e.hom.app M ≫ V.map (R₀.map (U.preimage g)) at he
  rw [← he, U.map_preimage, hg]
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, NatIso.cancel_natIso_hom_left]
  exact Category.comp_id _

private theorem isDerivedCompleteModule_restrictScalars_iff
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))]
    (N : ModuleCat.{v} B) :
    IsDerivedCompleteModule I ((ModuleCat.restrictScalars f).obj N) ↔
      IsDerivedCompleteModule (I.map f) N := by
  let R := ModuleCat.restrictScalars.{v} f
  let e := (R.mapDerivedCategorySingleFunctor 0).app N
  exact ⟨fun h => (isDerivedComplete_restrictScalars_iff A B f I _).mp
      (isDerivedComplete_of_iso A I e.symm h),
    fun h => isDerivedComplete_of_iso A I e
      ((isDerivedComplete_restrictScalars_iff A B f I _).mpr h)⟩

private theorem isEquivalence_restrictScalars_completeModules
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))] :
    let P : ObjectProperty (ModuleCat.{v} A) :=
      fun M => IsDerivedCompleteModule I M
    let Q : ObjectProperty (ModuleCat.{v} B) :=
      fun M => IsDerivedCompleteModule (I.map (algebraMap A B)) M
    let R := ModuleCat.restrictScalars.{v} (algebraMap A B)
    ∀ hR : ∀ N : Q.FullSubcategory, P (R.obj N.obj),
      (P.lift (Q.ι ⋙ R) hR).IsEquivalence := by
  dsimp only
  let P : ObjectProperty (ModuleCat.{v} A) :=
    fun M => IsDerivedCompleteModule I M
  let Q : ObjectProperty (ModuleCat.{v} B) :=
    fun M => IsDerivedCompleteModule (I.map (algebraMap A B)) M
  let R := ModuleCat.restrictScalars.{v} (algebraMap A B)
  intro hR
  let F := P.lift (Q.ι ⋙ R) hR
  let : F.Full := ⟨fun {X Y} f => by
    obtain ⟨g, hg⟩ := (bijective_map_restrictScalars_of_isDerivedCompleteModule
      A B I hI hflat hquot X.obj Y.obj Y.property).surjective f.hom
    exact ⟨ObjectProperty.homMk g, by apply P.ι.map_injective; exact hg⟩⟩
  let : F.EssSurj := ⟨fun X => by
    obtain ⟨N, ⟨e⟩⟩ := exists_restrictScalars_iso_of_isDerivedCompleteModule
      A B I hI hflat hquot X.obj X.property
    have hN : Q N := by
      apply (isDerivedCompleteModule_restrictScalars_iff A B (algebraMap A B) I N).mp
      exact isDerivedComplete_of_iso A I
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).mapIso e.symm) X.property
    exact ⟨⟨N, hN⟩, ⟨P.isoMk e⟩⟩⟩
  exact Functor.IsEquivalence.mk

private theorem exists_restrictScalars_complex_iso_of_complete_terms
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))]
    (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : ∀ n, IsDerivedCompleteModule I (K.X n)) :
    ∃ L : CochainComplex (ModuleCat.{v} B) ℤ,
      Nonempty (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L ≅ K) := by
  let P : ObjectProperty (ModuleCat.{v} A) :=
    fun M => IsDerivedCompleteModule I M
  let Q : ObjectProperty (ModuleCat.{v} B) :=
    fun M => IsDerivedCompleteModule (I.map (algebraMap A B)) M
  let R := ModuleCat.restrictScalars.{v} (algebraMap A B)
  let hR : ∀ N : Q.FullSubcategory, P (R.obj N.obj) := fun N =>
    (isDerivedCompleteModule_restrictScalars_iff A B (algebraMap A B) I N.obj).mpr N.property
  let F := P.lift (Q.ι ⋙ R) hR
  let : F.IsEquivalence := isEquivalence_restrictScalars_completeModules A B I hI hflat hquot hR
  let K' : CochainComplex P.FullSubcategory ℤ :=
    { X n := ⟨K.X n, hK n⟩
      d i j := ObjectProperty.homMk (K.d i j)
      shape i j h := by apply P.ι.map_injective; exact K.shape i j h
      d_comp_d' i j k _ _ := by apply P.ι.map_injective; exact K.d_comp_d i j k }
  let E := F.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := (Q.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj (E.inverse.obj K')
  exact ⟨L, ⟨(P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (E.counitIso.app K')⟩⟩

private theorem bijective_mapHomologicalComplex_of_surjective
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Faithful]
    {ι : Type w} (c : ComplexShape ι) (K L : HomologicalComplex C c)
    (h : ∀ i, Function.Surjective
      (F.map : (K.X i ⟶ L.X i) → (F.obj (K.X i) ⟶ F.obj (L.X i)))) :
    Function.Bijective ((F.mapHomologicalComplex c).map : (K ⟶ L) → _) := by
  refine ⟨(F.mapHomologicalComplex c).map_injective, ?_⟩
  intro f
  choose g hg using fun i => h i (f.f i)
  refine ⟨{ f := g, comm' := ?_ }, ?_⟩
  · intro i j _
    apply F.map_injective
    simpa only [Functor.map_comp, hg, Functor.mapHomologicalComplex_obj_d] using f.comm i j
  · ext i
    exact hg i

private theorem exists_small_quotient_annihilator
    (R : Type u) [CommRing R] {ι : Type w} [Small.{v} ι]
    (M : ι → ModuleCat.{v} R) :
    ∃ J : Ideal R, Small.{v} (R ⧸ J) ∧ ∀ i, J ≤ Module.annihilator R (M i) := by
  classical
  let P := ∀ i, M i
  let J := Module.annihilator R P
  refine ⟨J, small_of_injective (DFunLike.coe_injective.comp
    (RingHom.kerLift_injective (Module.toAddMonoidEnd R P))), ?_⟩
  intro i
  exact (show J = ⨅ i, Module.annihilator R (M i) from Module.annihilator_pi).le.trans (iInf_le _ i)

private theorem isTorsionBySet_map_of_restrictScalars
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (M : ModuleCat.{v} B)
    (h : Module.IsTorsionBySet A ((ModuleCat.restrictScalars f).obj M) J) :
    Module.IsTorsionBySet B M (J.map f) := by
  rw [Module.isTorsionBySet_iff_subset_annihilator] at h ⊢
  change J.map f ≤ Module.annihilator B M
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  exact Module.mem_annihilator.mpr (Module.mem_annihilator.mp (h ha))

private theorem exists_quotient_complex
    (R : Type u) [CommRing R] {ι : Type w} (J : Ideal R)
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{v} R) c)
    (hK : ∀ i, Module.IsTorsionBySet R (K.X i) J) :
    ∃ L : HomologicalComplex (ModuleCat.{v} (R ⧸ J)) c,
      Nonempty (((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapHomologicalComplex c).obj L ≅
        K) := by
  let (i : ι) : Module (R ⧸ J) (K.X i) := (hK i).module
  let (i : ι) : IsScalarTower R (R ⧸ J) (K.X i) := (hK i).isScalarTower
  let L : HomologicalComplex (ModuleCat.{v} (R ⧸ J)) c :=
    { X i := ModuleCat.of (R ⧸ J) (K.X i)
      d i j := ModuleCat.ofHom
        ((K.d i j).hom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
      shape i j h := by
        ext x
        change (K.d i j).hom x = 0
        rw [K.shape i j h]
        rfl
      d_comp_d' i j k _ _ := by
        ext x
        change (K.d j k).hom ((K.d i j).hom x) = 0
        have h := congrArg (fun f : K.X i ⟶ K.X k => f.hom x) (K.d_comp_d i j k)
        exact h }
  refine ⟨L, ⟨HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_⟩⟩
  · exact (LinearEquiv.refl R (K.X i)).toModuleIso
  · intro i j _
    ext x
    rfl

private theorem exists_small_quotient_complex
    (R : Type u) [CommRing R] {ι : Type w} [Small.{v} ι]
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{v} R) c) :
    ∃ J : Ideal R, Small.{v} (R ⧸ J) ∧
      ∃ L : HomologicalComplex (ModuleCat.{v} (R ⧸ J)) c,
        Nonempty (((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapHomologicalComplex c).obj L
          ≅ K) := by
  obtain ⟨J, hJ, hK⟩ := exists_small_quotient_annihilator R K.X
  obtain ⟨L, hL⟩ := exists_quotient_complex R J c K
    (fun i => (Module.isTorsionBySet_iff_subset_annihilator R _).mpr (hK i))
  exact ⟨J, hJ, L, hL⟩

private theorem exists_small_quotient_complex_family
    (R : Type u) [CommRing R] {ι : Type w} {κ : Type u₁}
    [Small.{v} ι] [Small.{v} κ] (c : ComplexShape ι)
    (K : κ → HomologicalComplex (ModuleCat.{v} R) c) :
    ∃ J : Ideal R, Small.{v} (R ⧸ J) ∧
      ∀ k, ∃ L : HomologicalComplex (ModuleCat.{v} (R ⧸ J)) c,
        Nonempty (((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapHomologicalComplex c).obj L
          ≅ K k) := by
  obtain ⟨J, hJ, hK⟩ := exists_small_quotient_annihilator R
    (fun p : κ × ι => (K p.1).X p.2)
  refine ⟨J, hJ, fun k => exists_quotient_complex R J c (K k) ?_⟩
  intro i
  exact (Module.isTorsionBySet_iff_subset_annihilator R _).mpr (hK (k, i))

private theorem full_restrictScalars_of_surjective
    {R : Type u} {S : Type w} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom { __ := g.hom.toAddMonoidHom, map_smul' := ?_ }, ?_⟩
    · intro s x
      obtain ⟨r, rfl⟩ := hf s
      exact g.hom.map_smul r x
    · ext x
      rfl

private theorem exists_small_quotient_derived
    (R : Type u) [CommRing R] (K : DerivedCategory (ModuleCat.{v} R)) :
    ∃ J : Ideal R, Small.{v} (R ⧸ J) ∧
      ∃ L : DerivedCategory (ModuleCat.{v} (R ⧸ J)),
        Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapDerivedCategory.obj L ≅ K) :=
          by
  let C := DerivedCategory.Q.objPreimage K
  obtain ⟨J, hJ, L, ⟨e⟩⟩ := exists_small_quotient_complex R (ComplexShape.up ℤ) C
  exact ⟨J, hJ, DerivedCategory.Q.obj L,
    ⟨(ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapDerivedCategoryFactors.app L ≪≫
      DerivedCategory.Q.mapIso e ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

private theorem bijective_tensorUnit_of_idealPowerTorsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I) :
    Function.Bijective ((TensorProduct.mk R M S).flip 1) := by
  let := hflat
  let e : ULift.{max u v} M ≃ₗ[R] M := ULift.moduleEquiv
  have hM' : IsIPowerTorsion R (ULift.{max u v} M) I := by
    intro m
    obtain ⟨n, hn, hnm⟩ := hM (e m)
    refine ⟨n, hn, fun a ha => e.injective ?_⟩
    simpa only [map_smul, map_zero] using hnm a ha
  have h :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
      R S I inferInstance).mpr hq (ULift.{max u v} M) hM'
  let E := TensorProduct.congr e (LinearEquiv.refl R S)
  have hcomp : Function.Bijective
      (((TensorProduct.mk R M S).flip 1) ∘ e) := by
    have heq : ((TensorProduct.mk R M S).flip 1) ∘ e =
        E ∘ ((TensorProduct.mk R (ULift.{max u v} M) S).flip 1) := by
      funext m
      simp [E]
    rw [heq]
    exact E.bijective.comp h
  exact (Function.Bijective.of_comp_iff _ e.bijective).mp hcomp



private theorem small_quotient_map_sup_pow
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (J : Ideal A) [Small.{w} (A ⧸ J)] (n : ℕ) :
    Small.{w} (B ⧸ (J ⊔ I ^ n).map (algebraMap A B)) := by
  let : Small.{w} (A ⧸ (J ⊔ I ^ n)) :=
    small_of_surjective (Ideal.Quotient.factor_surjective le_sup_left)
  exact small_of_surjective
    (Ideal.quotientMap_bijective_of_le (algebraMap A B) le_sup_right
      (@quotientMap_pow_bijective_of_flat _ _ _ _ _ hflat I hquot n)).surjective

private theorem small_quotient_iInf_map_sup_pow
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (J : Ideal A) [Small.{w} (A ⧸ J)] :
    Small.{w} (B ⧸ ⨅ n : ℕ, (J ⊔ I ^ n).map (algebraMap A B)) := by
  have (n : ℕ) : Small.{w} (B ⧸ (J ⊔ I ^ n).map (algebraMap A B)) :=
    small_quotient_map_sup_pow I hflat hquot J n
  exact Ideal.small_quotient_iInf _

private theorem flat_quotient_map
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (hflat : Module.Flat A B) :
    Module.Flat (A ⧸ J) (B ⧸ J.map (algebraMap A B)) := by
  let := hflat
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B J).toLinearEquiv

private theorem bijective_quotientMap_quotient
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (f : A →+* B) (I J : Ideal A)
    (h : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    let fJ := Ideal.quotientMap (J.map f) f Ideal.le_comap_map
    Function.Bijective (Ideal.quotientMap
      ((I.map (Ideal.Quotient.mk J)).map fJ) fJ Ideal.le_comap_map) := by
  let fI := Ideal.quotientMap (I.map f) f Ideal.le_comap_map
  let fJ := Ideal.quotientMap (J.map f) f Ideal.le_comap_map
  have hI : (I.map (Ideal.Quotient.mk J)).map fJ =
      (I.map f).map (Ideal.Quotient.mk (J.map f)) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun g => I.map g) (Ideal.quotientMap_comp_mk (f := f) Ideal.le_comap_map)
  have hJ : (J.map (Ideal.Quotient.mk I)).map fI =
      (J.map f).map (Ideal.Quotient.mk (I.map f)) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun g => J.map g) (Ideal.quotientMap_comp_mk (f := f) Ideal.le_comap_map)
  let eI := RingEquiv.ofBijective fI h
  let e := (DoubleQuot.quotQuotEquivComm J I).trans
    ((Ideal.quotientEquiv (J.map (Ideal.Quotient.mk I))
      ((J.map f).map (Ideal.Quotient.mk (I.map f))) eI hJ.symm).trans
      ((DoubleQuot.quotQuotEquivComm (J.map f) (I.map f)).symm.trans
        (Ideal.quotEquivOfEq hI.symm)))
  have he : (e : _ → _) = Ideal.quotientMap
      ((I.map (Ideal.Quotient.mk J)).map fJ) fJ Ideal.le_comap_map := by
    funext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [DoubleQuot.quotQuotEquivComm_symm, RingEquiv.coe_trans, Function.comp_apply,
      DoubleQuot.quotQuotEquivComm_mk_mk, Ideal.quotientEquiv_apply, RingHom.toMonoidHom_eq_coe,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_ofClass,
      Ideal.quotientMap_algebraMap,
      Ideal.Quotient.algebraMap_eq, RingHom.coe_coe, RingEquiv.coe_ofBijective,
      Ideal.quotientMap_mk, fJ, e, eI, fI]
    exact Ideal.quotEquivOfEq_mk hI.symm _
  change Function.Bijective (Ideal.quotientMap
    ((I.map (Ideal.Quotient.mk J)).map fJ) fJ Ideal.le_comap_map)
  rw [← he]
  exact e.bijective

end CompleteRestrictScalarsEquivalence

end
