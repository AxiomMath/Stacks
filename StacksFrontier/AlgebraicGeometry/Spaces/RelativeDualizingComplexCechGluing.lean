module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexCechSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpacesEtaleTransitionCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftEtaleDescent
public import StacksFrontier.CategoryTheory.Functor.DescentOfMorphismsTransport
public import StacksFrontier.Homology.PseudoCoherent.Ext

/-!
# Gluing a relative dualizing complex along a Čech hypercovering

Let `f : X ⟶ Y` be proper, flat and of finite presentation, `b₀ : V₀ ⟶ Y` étale, surjective and
relatively representable, `U_n = V_n ×_Y X` for the Čech nerve `V` of `b₀`, and `D₀` a relative
dualizing complex on `U_0 ⟶ V_0`. An object `K` of `D_QCoh` of the spaces-étale site of `X` with
`La_0^* K ≅ ι ω_0` (the output of Stacks 0DLA for the descent datum of `D₀`) is the transport
`ι ω` of an object `ω` of `D_QCoh(𝒪_{X_étale})`, and `ω|_{U_0} ≅ ω_0`. This is the descent step
of the proof of Stacks 0E61.

## Main results

* `CategoryTheory.Functor.exists_iso_map_hom_eq_of_bijective`: a functor bijective on the
  relevant morphism sets lifts isomorphisms.
* `AlgebraicGeometry.BigFppfSpaceSite.etaleRepresentable_cechOverPullback_augmentation_zero`,
  `AlgebraicGeometry.BigFppfSpaceSite.isSurjective_cechOverPullback_augmentation_zero`.
* `AlgebraicGeometry.BigFppfSpaceSite.exists_iso_smallEtaleDerivedModulePullback_cechOverPullback`:
  the descended object `ω` with `ι ω ≅ K` and `ω|_{U_0} ≅ ω_0`.
* `AlgebraicGeometry.BigFppfSpaceSite.exists_hom_smallEtaleDerivedModulePullback_cechOver_eq`:
  descent of morphisms along the Čech nerve of `b₀` on the small étale sites, from Stacks 0DL9.
* `AlgebraicGeometry.BigFppfSpaceSite.hom_shift_eq_zero_derivedPullback_cechOver`: the vanishing
  of negative extensions required by Stacks 0DL9 for the gluing of the trace.
* `AlgebraicGeometry.BigFppfSpaceSite.cechOverPullbackSmallEtaleTransitionIso_inv_comp_map_comp`:
  the restriction `ω|_{U_0} ≅ ω_0` is compatible with the descent isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- The universe-polymorphic sheafification instances of the cotangent complex (imported through
-- the small-étale duality files) leave universe constraints of the spaces-étale sites stuck.
attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]

/-- **Lifting an isomorphism along a functor bijective on morphisms**: if `F` is bijective on
`A ⟶ B` and `B ⟶ A` and injective on `A ⟶ A` and `B ⟶ B`, every isomorphism `F A ≅ F B` is the
image of an isomorphism `A ≅ B`. -/
theorem exists_iso_map_hom_eq_of_bijective (F : C ⥤ D) {A B : C}
    (hAB : Function.Bijective (F.map : (A ⟶ B) → _))
    (hBA : Function.Bijective (F.map : (B ⟶ A) → _))
    (hAA : Function.Injective (F.map : (A ⟶ A) → _))
    (hBB : Function.Injective (F.map : (B ⟶ B) → _)) (i : F.obj A ≅ F.obj B) :
    ∃ ε : A ≅ B, F.map ε.hom = i.hom := by
  obtain ⟨u, hu⟩ := hAB.2 i.hom
  obtain ⟨v, hv⟩ := hBA.2 i.inv
  exact ⟨⟨u, v, hAA (by rw [F.map_comp, hu, hv, i.hom_inv_id, F.map_id]),
    hBB (by rw [F.map_comp, hu, hv, i.inv_hom_id, F.map_id])⟩, hu⟩

end CategoryTheory.Functor

namespace CategoryTheory

/-- Rewriting the last factor `θ.hom.app X` of a composite along an equality of isomorphisms. -/
theorem Iso.eq_comp_comp_hom_app_of_eq {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    {θ θ' : F ≅ G} (hθ : θ = θ') {X : C} {W₀ W₁ : D} {R : W₀ ⟶ G.obj X} {A : W₀ ⟶ W₁}
    {B : W₁ ⟶ F.obj X} (h : R = A ≫ B ≫ θ'.hom.app X) : R = A ≫ B ≫ θ.hom.app X := by
  subst hθ
  exact h

end CategoryTheory

namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale sites; at low
-- priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.CategoryTheory.Hypercovering

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)

/-- The augmentation `U_0 ⟶ X` of `n ↦ V_n ×_Y X` is étale and relatively representable when
`b₀` is. -/
theorem etaleRepresentable_cechOverPullback_augmentation_zero (hb₀ : etaleRepresentable T b₀) :
    etaleRepresentable T ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌)) :=
  (Stacks.CategoryTheory.Hypercovering.singleton_mem_pretopology _ _).1
    (isHypercoveringAugmentation_cechOverPullback (etaleRepresentable T).pretopology b₀ f
      ((Stacks.CategoryTheory.Hypercovering.singleton_mem_pretopology _ b₀).2 hb₀)).1

/-- The augmentation `U_0 ⟶ X` of `n ↦ V_n ×_Y X` is surjective when `b₀` is: it is the base
change of `V_0 ⟶ Y`, which is `b₀` up to isomorphism. -/
theorem isSurjective_cechOverPullback_augmentation_zero
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem b₀.hom) :
    Space.IsSurjective T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌)).hom := by
  let e : (cechOver b₀).obj (op ⦋0⦌) ≅ Over.mk b₀ :=
    Limits.productUniqueIso (fun _ : Fin 1 => Over.mk b₀)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Y).map e.hom))
  refine Space.isSurjective_of_isPullback T.schemeSite S T.scheme_mem
    (IsPullback.of_hasPullback ((cechOver b₀).obj (op ⦋0⦌)).hom f) ?_
  rw [← Over.w e.hom]
  exact Space.isSurjective_comp T.schemeSite S T.scheme_mem
    (Space.isSurjective_of_isIso T.schemeSite S T.scheme_mem e.hom.left.hom) hsurj

/-- **The descended relative dualizing complex** (the descent step of Stacks 0E61). Let `K` be
an object of `D_QCoh` of the spaces-étale site of `X` and `e : La_0^* K ≅ ι ω_0`, for the
augmentation `a_0 : U_0 ⟶ X` of `n ↦ V_n ×_Y X` and a relative dualizing complex `D₀` on
`U_0 ⟶ V_0` (the output of Stacks 0DLA). Then `K ≅ ι ω` for some `ω ∈ D_QCoh(𝒪_{X_étale})`, and
`La_0^* ω ≅ ω_0` by an isomorphism whose transport is
`ι(La_0^* ω) ≅ La_0^*(ι ω) ≅ La_0^* K ≅ ι ω_0`.
-/
theorem exists_iso_smallEtaleDerivedModulePullback_cechOverPullback
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u})) (hb₀ : etaleRepresentable T b₀)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem b₀.hom)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _))
    (hK : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) K)
    (e : (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
          (op ⦋0⦌)))).obj K ≅
      (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω) :
    ∃ ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2),
      Space.QcohDerived T.schemeSite S T.scheme_mem X ω ∧
      ∃ (eω : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj ω ≅ K)
        (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω),
        (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).map ε.hom =
          (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀).1).hom.app ω ≫
          (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
              ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
            (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
            (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
              (op ⦋0⦌)))).map eω.hom ≫ e.hom := by
  have ha := etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀
  have hdesc := BigEtaleSpaceSite.exists_toSpacesEtaleDerivedModules_obj_iso_of_derivedPullback_iso
    T.bigEtaleSpaceSite _ ha.1 (isSurjective_cechOverPullback_augmentation_zero b₀ f hsurj) K hK
    D₀.ω e
  let ω := hdesc.choose
  let eω : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj ω ≅ K :=
    hdesc.choose_spec.2.some
  let ι₀ := Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
    ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))
  let A := (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
    ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω
  let i : ι₀.obj A ≅ ι₀.obj D₀.ω :=
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ ha.1).app ω ≪≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
          (op ⦋0⦌)))).mapIso eω ≪≫ e
  have hB : Space.QcohDerived T.schemeSite S T.scheme_mem _ D₀.ω :=
    D₀.toRelativeDualizingPair.qcohDerived_ω
  have hA : Space.QcohDerived T.schemeSite S T.scheme_mem _ A := by
    let := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
      ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))
    have hB' := (Space.qcohDerived_iff_toSpacesEtaleDerivedModules_obj _ _ _ _ D₀.ω).1 hB
    exact (Space.qcohDerived_iff_toSpacesEtaleDerivedModules_obj _ _ _ _ A).2 fun n =>
      SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso i).symm (hB' n)
  -- `obtain` on this existence statement re-checks the large goal; `Exists.choose` does not.
  have hε := ι₀.exists_iso_map_hom_eq_of_bijective
    (Space.bijective_toSpacesEtaleDerivedModules_map _ _ _ _ A D₀.ω hB)
    (Space.bijective_toSpacesEtaleDerivedModules_map _ _ _ _ D₀.ω A hA)
    (Space.bijective_toSpacesEtaleDerivedModules_map _ _ _ _ A A hA).1
    (Space.bijective_toSpacesEtaleDerivedModules_map _ _ _ _ D₀.ω D₀.ω hB).1 i
  exact ⟨ω, hdesc.choose_spec.1, eω, hε.choose, hε.choose_spec⟩
/-- An augmentation component `a_n` is étale and relatively representable when `a_m` and the
transition `W(φ)` are, by the simplicial identity `W(φ) ≫ a_m = a_n`. -/
private theorem etaleRepresentable_augmentation_app_of_map {W : SimplicialObject T.Spaces}
    {Z : T.Spaces} (a : W ⟶ (SimplicialObject.const _).obj Z) {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : etaleRepresentable T (W.map φ.op)) (hm : etaleRepresentable T (a.app (op m))) :
    etaleRepresentable T (a.app (op n)) := by
  rw [← augmentation_map_comp_app a φ]
  exact MorphismProperty.comp_mem _ _ _ hφ hm

/-- The face maps of the Čech nerve `V` of `b₀` are étale and relatively representable when
`b₀` is (Stacks 0DER for the hypercovering `V ⟶ Y`). -/
theorem etaleRepresentable_cechOver_delta (hb₀ : etaleRepresentable T b₀) (n : ℕ)
    (i : Fin (n + 2)) :
    etaleRepresentable T ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ i).op) := by
  have hs : ∀ {A Z : T.Spaces} (g : A ⟶ Z),
      Presieve.singleton g ∈ (etaleRepresentable T).pretopology Z ↔ etaleRepresentable T g :=
    fun g => Stacks.CategoryTheory.Hypercovering.singleton_mem_pretopology _ g
  have h := isHypercoveringAugmentation_cechOver (etaleRepresentable T).pretopology b₀
    ((hs b₀).2 hb₀)
  let A : SimplicialObject.Augmented T.Spaces :=
    { left := cechOver b₀ ⋙ Over.forget Y, right := Y
      hom := overAugmentation (cechOver b₀) }
  have hA : (etaleRepresentable T).IsHypercovering A :=
    { map_zero := (hs _).1 h.1
      map_one := (hs _).1 h.2.1
      matching := fun n hn => (hs _).1 (h.2.2 n hn) }
  exact MorphismProperty.IsHypercovering.face_mem _ hA n i

/-- The augmentation `V_0 ⟶ Y` of the Čech nerve of `b₀` is étale and relatively representable
when `b₀` is. -/
theorem etaleRepresentable_cechOver_augmentation_zero (hb₀ : etaleRepresentable T b₀) :
    etaleRepresentable T ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) :=
  (Stacks.CategoryTheory.Hypercovering.singleton_mem_pretopology _ _).1
    (isHypercoveringAugmentation_cechOver (etaleRepresentable T).pretopology b₀
      ((Stacks.CategoryTheory.Hypercovering.singleton_mem_pretopology _ b₀).2 hb₀)).1

/-- The augmentation `V_1 ⟶ Y` of the Čech nerve of `b₀` is étale and relatively representable
when `b₀` is. -/
theorem etaleRepresentable_cechOver_augmentation_one (hb₀ : etaleRepresentable T b₀) :
    etaleRepresentable T ((overAugmentation (cechOver b₀)).app (op ⦋1⦌)) := by
  exact etaleRepresentable_augmentation_app_of_map _ (SimplexCategory.δ (0 : Fin 2))
    (etaleRepresentable_cechOver_delta b₀ hb₀ 0 0)
    (etaleRepresentable_cechOver_augmentation_zero b₀ hb₀)

/-- The transitions `L V(δ¹ᵢ)^* ⋙ L b_0^* ≅ L b_1^*` of the small-étale derived pullbacks to the
Čech nerve of `b₀`. -/
def cechOverSmallEtaleTransitionIso (i : Fin 2) :
    Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) ⋙
      Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ i).op) ≅
      Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOver b₀)).app (op ⦋1⦌)) :=
  Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem _ _ ≪≫
    Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
      (augmentation_map_comp_app (overAugmentation (cechOver b₀)) (SimplexCategory.δ i))


/-- `ι` turns the transition of the Čech nerve of `b₀` on the small étale sites into that of
Stacks 0DLA/0DL9 on the spaces-étale sites, through `N_g : ι(Lg^*K) ≅ Lg^*(ιK)`. -/
theorem cechOverSmallEtaleTransitionIso_comparison (hb₀ : etaleRepresentable T b₀) (i : Fin 2)
    (M : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem Y.1 Y.2)) :
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem Y
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
      ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋0⦌))
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
      ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋1⦌))
    (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
        ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋1⦌))).map
        ((cechOverSmallEtaleTransitionIso b₀ i).hom.app M) ≫
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
        (etaleRepresentable_cechOver_augmentation_one b₀ hb₀).1).hom.app M =
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
        (etaleRepresentable_cechOver_delta b₀ hb₀ 0 i).1).hom.app
        ((Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).obj M) ≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋1⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋0⦌)))
        (spacesEtaleRingedToposHom ((cechOver b₀ ⋙ Over.forget Y).map
          (SimplexCategory.δ i).op))).map
        ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
          (etaleRepresentable_cechOver_augmentation_zero b₀ hb₀).1).hom.app M) ≫
      (augmentationTransitionDerivedIso (overAugmentation (cechOver b₀))
        (SimplexCategory.δ i)).hom.app
        ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Y).obj M) := by
  have hθ := augmentationTransitionDerivedIso_eq (cechOver b₀ ⋙ Over.forget Y)
    (overAugmentation (cechOver b₀)) (SimplexCategory.δ i)
  have key := smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp_congr _ _ _
    (augmentation_map_comp_app (overAugmentation (cechOver b₀)) (SimplexCategory.δ i))
    (etaleRepresentable_cechOver_augmentation_zero b₀ hb₀)
    (etaleRepresentable_cechOver_delta b₀ hb₀ 0 i)
    (etaleRepresentable_cechOver_augmentation_one b₀ hb₀) M
  exact Iso.eq_comp_comp_hom_app_of_eq hθ
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr))))
/-- **Descent of morphisms along the Čech nerve of `b₀`, on the small étale sites.** Let
`M, N ∈ D(𝒪_{Y_étale})` with `N` in `D_QCoh`, and assume that morphisms
`La_0^*(ιM) ⟶ La_0^*(ιN)` on the spaces-étale sites whose two face transports agree come from
`ιM ⟶ ιN` (the conclusion of Stacks 0DL9 for the hypercovering `V ⟶ Y`). Then every
`φ₀ : L b_0^* M ⟶ L b_0^* N` whose two pullbacks to `V_1` agree is `L b_0^* φ`. -/
theorem exists_hom_smallEtaleDerivedModulePullback_cechOver_eq (hb₀ : etaleRepresentable T b₀)
    (M N : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem Y.1 Y.2))
    (hN : Space.QcohDerived T.schemeSite S T.scheme_mem Y N)
    (hdesc : ∀ ψ : (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)))).obj
          ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Y).obj M) ⟶
        (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)))).obj
          ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Y).obj N),
      augmentationFaceTransport (overAugmentation (cechOver b₀)) 0 ψ =
        augmentationFaceTransport (overAugmentation (cechOver b₀)) 1 ψ →
      ∃ g, (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)))).map g = ψ)
    (φ₀ : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).obj M ⟶
      (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).obj N)
    (hφ : (cechOverSmallEtaleTransitionIso b₀ 0).inv.app M ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ (0 : Fin 2)).op)).map φ₀ ≫
        (cechOverSmallEtaleTransitionIso b₀ 0).hom.app N =
      (cechOverSmallEtaleTransitionIso b₀ 1).inv.app M ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ (1 : Fin 2)).op)).map φ₀ ≫
        (cechOverSmallEtaleTransitionIso b₀ 1).hom.app N) :
    ∃ φ : M ⟶ N, (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).map φ = φ₀ :=
  exists_map_eq_of_descent_of_comparison
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOver_augmentation_zero b₀ hb₀).1)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOver_delta b₀ hb₀ 0 0).1)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOver_delta b₀ hb₀ 0 1).1)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOver_augmentation_one b₀ hb₀).1)
    (cechOverSmallEtaleTransitionIso b₀ 0) (cechOverSmallEtaleTransitionIso b₀ 1)
    (augmentationTransitionDerivedIso (overAugmentation (cechOver b₀)) (SimplexCategory.δ 0))
    (augmentationTransitionDerivedIso (overAugmentation (cechOver b₀)) (SimplexCategory.δ 1))
    (cechOverSmallEtaleTransitionIso_comparison b₀ hb₀ 0 M)
    (cechOverSmallEtaleTransitionIso_comparison b₀ hb₀ 0 N)
    (cechOverSmallEtaleTransitionIso_comparison b₀ hb₀ 1 M)
    (cechOverSmallEtaleTransitionIso_comparison b₀ hb₀ 1 N) hdesc
    (Space.bijective_toSpacesEtaleDerivedModules_map T.schemeSite S T.scheme_mem Y M N hN).2
    (Space.bijective_toSpacesEtaleDerivedModules_map T.schemeSite S T.scheme_mem _ _ _
      (Space.derivedQuasicoherent_smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem _ N
        hN)).1 φ₀ hφ
/-- The maps `V(τ) : V_n ⟶ V_0` to the last vertex of the Čech nerve of `b₀` are étale and
relatively representable when `b₀` is: they are composites of face maps. -/
theorem etaleRepresentable_cechOver_const_last (hb₀ : etaleRepresentable T b₀) (n : ℕ) :
    etaleRepresentable T ((cechOver b₀ ⋙ Over.forget Y).map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op) := by
  induction n with
  | zero =>
    have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ (Fin.last 0) = 𝟙 _ :=
      SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦
        Subsingleton.elim (α := Fin 1) _ _))
    rw [h0, op_id, CategoryTheory.Functor.map_id]
    exact MorphismProperty.id_mem _ _
  | succ n ih =>
    have e : SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)) =
        SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n) ≫ SimplexCategory.δ 0 :=
      SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by
        simp [SimplexCategory.δ]))
    rw [e, op_comp, CategoryTheory.Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (etaleRepresentable_cechOver_delta b₀ hb₀ n 0) ih

/-- The augmentation `V_n ⟶ Y` of the Čech nerve of `b₀` is étale and relatively representable
when `b₀` is. -/
theorem etaleRepresentable_cechOver_augmentation (hb₀ : etaleRepresentable T b₀)
    (n : SimplexCategory) :
    etaleRepresentable T ((overAugmentation (cechOver b₀)).app (op n)) := by
  obtain ⟨k⟩ := n
  exact etaleRepresentable_augmentation_app_of_map _ (SimplexCategory.const ⦋0⦌ ⦋k⦌ (Fin.last k))
    (etaleRepresentable_cechOver_const_last b₀ hb₀ k)
    (etaleRepresentable_cechOver_augmentation_zero b₀ hb₀)

/-- **The direct image of the glued complex has no positive cohomology after pullback to `V_n`**:
`L b_n^* Rf_* ω ∈ D^{≤ 0}`, for `ω` with `L a_0^* ω ≅ ω_0`. Indeed
`L b_n^* Rf_* ω ≅ Rf_{n*} L a_n^* ω` (flat base change, Stacks 08IR) and `L a_n^* ω` is the base
change of `ω_0` to `U_n`, a relative dualizing complex (Stacks 0E6C), so Stacks 0E5Y applies. -/
theorem isLE_smallEtaleDerivedModulePullback_derivedModulePushforward_cechOver
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2))
    (hω : Space.QcohDerived T.schemeSite S T.scheme_mem X ω)
    (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω)
    (n : SimplexCategory) :
    ((Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOver b₀)).app (op n))).obj
        ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω)).IsLE 0 := by
  let φ : (op n : SimplexCategoryᵒᵖ) ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ n 0).op
  let Dn := D₀.baseChange (isPullback_cechOverPullback_map b₀ f φ)
  have hsq := isPullback_cechOverPullbackFst b₀ f (op n)
  have := Space.isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent T.schemeSite S T.scheme_mem
    _ _ _ _ hsq hfp.2.1 hfp.2.2 (Space.torIndependent_of_isFlat_left f _ hfl) ω hω
  let e₁ := asIso (Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f _ _ _
    hsq.w ω)
  let e₂ : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op n))).obj ω ≅ Dn.ω :=
    ((Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem _ _ ≪≫
      Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
        (augmentation_map_comp_app (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.const ⦋0⦌ n 0))).app ω).symm ≪≫
      (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem _).mapIso ε
  have := (Space.RelativeDualizingComplex.isIso_smallEtaleDerivedHomothety_and_isLE Dn).2
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((e₁ ≪≫ (Space.derivedModulePushforward T.schemeSite S T.scheme_mem _).mapIso e₂).symm) 0

/-- **The negative extensions of `ι(Rf_* ω)` by `ι 𝒪_Y` vanish on the Čech nerve of `b₀`** (the
hypothesis of Stacks 0DL9 for the gluing of the trace in Stacks 0E61): `L b_n^*` of these objects
are `ι(L b_n^* Rf_* ω)` and `ι 𝒪_{V_n}` (through `N`), `ι` is bijective on morphisms into
`D_QCoh` and commutes with shifts, and `L b_n^* Rf_* ω ∈ D^{≤ 0}` while `𝒪_{V_n}[i] ∈ D^{≥ 1}`. -/
theorem hom_shift_eq_zero_derivedPullback_cechOver (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hb₀ : etaleRepresentable T b₀)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2))
    (hω : Space.QcohDerived T.schemeSite S T.scheme_mem X ω)
    (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω)
    (n : SimplexCategory) (i : ℤ) (hi : i < 0)
    (g : (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op n)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOver b₀)).app (op n)))).obj
          ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Y).obj
            ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω)) ⟶
      ((derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).obj (op n)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem Y)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOver b₀)).app (op n)))).obj
          ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem Y).obj
            (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj))⟦i⟧) :
    g = 0 := by
  let := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
    ((cechOver b₀ ⋙ Over.forget Y).obj (op n))
  have hbn := etaleRepresentable_cechOver_augmentation b₀ hb₀ n
  let A := (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOver b₀)).app (op n))).obj
        ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω)
  let B := (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem
    ((cechOver b₀ ⋙ Over.forget Y).obj (op n)).1 ((cechOver b₀ ⋙ Over.forget Y).obj (op n)).2).obj
  have : A.IsLE (1 - 1) :=
    isLE_smallEtaleDerivedModulePullback_derivedModulePushforward_cechOver b₀ f hZ hf hfl hfp D₀ ω
      hω ε n
  have hA : ∀ h : A ⟶ B⟦i⟧, h = 0 := fun h =>
    StacksDraft.PseudoCoherence.hom_eq_zero_of_isLE_of_single_shift A 1 _ i (by omega) h
  let ιn := Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
    ((cechOver b₀ ⋙ Over.forget Y).obj (op n))
  let eA := (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ hbn.1).app
    ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω)
  let eB : ιn.obj B ≅ _ := ιn.mapIso (Space.smallEtaleDerivedModulePullbackUnitIso
      (B := T.schemeSite) (S := S) (hS := T.scheme_mem)
      ((overAugmentation (cechOver b₀)).app (op n))).symm ≪≫
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _ hbn.1).app
      (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj
  exact ιn.eq_zero_of_hom_shift_eq_zero_of_surjective eA eB i
    (Space.bijective_toSpacesEtaleDerivedModules_map T.schemeSite S T.scheme_mem _ A (B⟦i⟧)
      (Space.qcohDerived_shift B i
        (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem _ _).2)).2
    hA g
/-- The augmentation `U_1 ⟶ X` of `n ↦ V_n ×_Y X` is étale and relatively representable when
`b₀` is. -/
theorem etaleRepresentable_cechOverPullback_augmentation_one (hb₀ : etaleRepresentable T b₀) :
    etaleRepresentable T ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋1⦌)) := by
  exact etaleRepresentable_augmentation_app_of_map _ (SimplexCategory.δ (0 : Fin 2))
    (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 0)
    (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀)

/-- The transitions `L U(δ¹ᵢ)^* ⋙ L a_0^* ≅ L a_1^*` of the small-étale derived pullbacks to
`n ↦ V_n ×_Y X`. -/
def cechOverPullbackSmallEtaleTransitionIso (i : Fin 2) :
    Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌)) ⋙
      Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f ⋙ Over.forget X).map (SimplexCategory.δ i).op) ≅
      Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋1⦌)) :=
  Space.smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem _ _ ≪≫
    Space.smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
      (augmentation_map_comp_app (overAugmentation (cechOverPullback b₀ f)) (SimplexCategory.δ i))

/-- `ι` turns the transitions of `n ↦ V_n ×_Y X` on the small étale sites into those of
Stacks 0DLA on the spaces-étale sites, through `N_g : ι(Lg^*K) ≅ Lg^*(ιK)`. -/
theorem cechOverPullbackSmallEtaleTransitionIso_comparison (hb₀ : etaleRepresentable T b₀)
    (i : Fin 2) (M : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2)) :
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
      ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))
    letI := Space.spacesEtaleHasDerivedCategory T.schemeSite S T.scheme_mem
      ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌))
    (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌))).map
        ((cechOverPullbackSmallEtaleTransitionIso b₀ f i).hom.app M) ≫
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
        (etaleRepresentable_cechOverPullback_augmentation_one b₀ f hb₀).1).hom.app M =
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
        (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 i).1).hom.app
        ((Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj M) ≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
        (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ i).op))).map
        ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
          (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀).1).hom.app M) ≫
      (augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
        (SimplexCategory.δ i)).hom.app
        ((Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj M) := by
  have hθ := augmentationTransitionDerivedIso_eq (cechOverPullback b₀ f ⋙ Over.forget X)
    (overAugmentation (cechOverPullback b₀ f)) (SimplexCategory.δ i)
  have key := smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp_congr _ _ _
    (augmentation_map_comp_app (overAugmentation (cechOverPullback b₀ f)) (SimplexCategory.δ i))
    (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀)
    (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 i)
    (etaleRepresentable_cechOverPullback_augmentation_one b₀ f hb₀) M
  exact Iso.eq_comp_comp_hom_app_of_eq hθ
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr))))

/-- **The restriction of the glued complex is compatible with the descent isomorphism** (the
compatibility of `ι_0 : ω|_{U_0} ≅ ω_0` with `ι_{δ¹₀}`, `ι_{δ¹₁}` in the proof of Stacks 0E61):
with `κ_i : L a_1^* ω ≅ L U(δ¹ᵢ)^* L a_0^* ω ≅ L U(δ¹ᵢ)^* ω_0`, `κ_1 ≫ α = κ_0`. It is read through
`ι` from the compatibility of Stacks 0DLA on the spaces-étale sites. -/
theorem cechOverPullbackSmallEtaleTransitionIso_inv_comp_map_comp
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u})) (hb₀ : etaleRepresentable T b₀)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (α : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left).obj D₀.ω ≅
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left).obj D₀.ω)
    (K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _))
    (e : (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
          (op ⦋0⦌)))).obj K ≅
      (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω)
    (he : (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
        (((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 1).1).app D₀.ω).symm ≪≫
          (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌))).mapIso α ≪≫
          (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 0).1).app D₀.ω).hom =
      ((augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
        (augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.δ (0 : Fin 2))).inv.app K) ≫
        (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ (0 : Fin 2)).op))).map e.hom)
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2))
    (eω : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj ω ≅ K)
    (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω)
    (hε : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).map ε.hom =
        (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
          (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀).1).hom.app ω ≫
        (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
            (op ⦋0⦌)))).map eω.hom ≫ e.hom) :
    ((cechOverPullbackSmallEtaleTransitionIso b₀ f 1).inv.app ω ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).map (SimplexCategory.δ (1 : Fin 2)).op)).map
          ε.hom) ≫ α.hom =
      (cechOverPullbackSmallEtaleTransitionIso b₀ f 0).inv.app ω ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).map (SimplexCategory.δ (0 : Fin 2)).op)).map
          ε.hom :=
  comp_eq_of_descent_of_comparison
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀).1)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 0).1)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 1).1)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
      (etaleRepresentable_cechOverPullback_augmentation_one b₀ f hb₀).1)
    (cechOverPullbackSmallEtaleTransitionIso b₀ f 0)
    (cechOverPullbackSmallEtaleTransitionIso b₀ f 1)
    (augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
      (SimplexCategory.δ 0))
    (augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
      (SimplexCategory.δ 1))
    (cechOverPullbackSmallEtaleTransitionIso_comparison b₀ f hb₀ 0 ω)
    (cechOverPullbackSmallEtaleTransitionIso_comparison b₀ f hb₀ 1 ω) eω e ε hε α _ rfl he
    (Space.bijective_toSpacesEtaleDerivedModules_map T.schemeSite S T.scheme_mem _ _ _
      (Space.derivedQuasicoherent_smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem _
        D₀.ω D₀.toRelativeDualizingPair.qcohDerived_ω)).1

end AlgebraicGeometry.BigFppfSpaceSite

end
