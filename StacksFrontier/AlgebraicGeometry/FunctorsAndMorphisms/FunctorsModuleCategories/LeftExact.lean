module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Indization.ParallelPair
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Additivity
public import StacksFrontier.RingTheory.Coherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Left exactness of the extension from finitely presented modules

Let `A` be a commutative ring, `B` an additive category and `F` a left exact functor from
finitely presented `A`-modules to `B`. Its filtered-colimit extension is additive and preserves
arbitrary direct sums. If `A` is coherent, `B` has kernels, and filtered colimits in `B` commute
with kernels, the extension is also left exact.

## Main results

* `ModuleCat.moduleCat_filteredColimit_preservesKernels`: in a module category, filtered
  colimits commute with kernels.
* `ModuleCat.filteredColimitExtension_preservesFiniteLimits`: left exactness of the extension.

## Implementation notes

The extension may be any functor equipped with the filtered-colimit preservation and
identification of `ModuleCat.FilteredColimitExtension`. Additivity and preservation of direct
sums are the more general results of `ModuleCat.filteredColimitExtension_additive` and
`ModuleCat.filteredColimitExtension_preservesCoproducts`; finite-limit preservation makes `F`
additive because binary products of finitely presented modules are biproducts, and neither
coherence nor the commutation of filtered colimits with kernels is needed for them. That
commutation hypothesis on `B` is stated as preservation, by each filtered-colimit functor, of
the limits of the parallel pairs that define kernels.

Coherence of `A` enters only through the closure of the finitely presented modules under
kernels, which is what makes the inclusion of the subcategory left exact.

## References

* [Stacks Project, Tag 0GNM](https://stacks.math.columbia.edu/tag/0GNM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x u₁

namespace ModuleCat

variable (A : Type u) [CommRing A]
variable {B : Type w} [Category.{x} B] [Preadditive B] [HasFiniteBiproducts B]
variable {F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B}


variable (A : Type u) [CommRing A]
variable {B : Type w} [Category.{x} B] [Preadditive B] [HasFiniteBiproducts B]
variable {F : CategoryTheory.Functor
  (FinitelyPresentedModuleCat.{u, max u v} A) B}

private lemma fp_ker (A : Type u) [CommRing A] [IsCoherentRing A]
    {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y)
    (hX : Module.FinitePresentation A X) (hY : Module.FinitePresentation A Y) :
    Module.FinitePresentation A (LinearMap.ker f.hom) := by
  have : Module.IsCoherent A X :=
    (coherent_iff_finitePresentation_of_coherentRing A IsCoherentRing.isCoherent X).2 hX
  have : Module.IsCoherent A Y :=
    (coherent_iff_finitePresentation_of_coherentRing A IsCoherentRing.isCoherent Y).2 hY
  exact (coherent_iff_finitePresentation_of_coherentRing A IsCoherentRing.isCoherent _).1
    (coherent_ker_and_coker_of_coherent f.hom).1

private instance fpClosedKernels (A : Type u) [CommRing A] [IsCoherentRing A] :
    (finitelyPresentedModule.{u, max u v} A).IsClosedUnderKernels where
  kernels_le := by
    rintro Z ⟨f, k, hk, hX, hY⟩
    let e := (ModuleCat.kernelIsLimit f).conePointUniqueUpToIso hk
    have : Module.FinitePresentation A (↑(ModuleCat.kernelCone f).pt) := fp_ker A f hX hY
    exact (finitelyPresentedModule_iff A k.pt).2 (.of_equiv e.toLinearEquiv)

private instance fpClosedIsomorphisms (A : Type u) [CommRing A] :
    (finitelyPresentedModule.{u, max u v} A).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    have : Module.FinitePresentation A _ := (finitelyPresentedModule_iff A _).1 hX
    exact (finitelyPresentedModule_iff A _).2
      (Module.FinitePresentation.of_equiv e.toLinearEquiv)

private instance fpContainsZero (A : Type u) [CommRing A] :
  (finitelyPresentedModule.{u, max u v} A).ContainsZero where
  exists_zero := by
    let Z : ModuleCat.{max u v} A := ModuleCat.of A (ULift.{max u v} (Fin 0 → A))
    refine ⟨Z, ModuleCat.isZero_of_subsingleton Z, ?_⟩
    exact (finitelyPresentedModule_iff A _).2 inferInstance

private instance fpClosedBinaryProducts (A : Type u) [CommRing A] :
    (finitelyPresentedModule.{u, max u v} A).IsClosedUnderBinaryProducts := by
  refine ⟨?_⟩
  rintro Z ⟨hZ⟩
  let Z' : WalkingPair → ModuleCat.{max u v} A := fun j => hZ.diag.obj ⟨j⟩
  let (j : WalkingPair) : Module.FinitePresentation A (Z' j) :=
    (finitelyPresentedModule_iff A _).1 (hZ.prop_diag_obj ⟨j⟩)
  let c : Cone hZ.diag :=
    { pt := ModuleCat.of A (∀ j, Z' j)
      π :=
        { app := fun j => ModuleCat.ofHom (LinearMap.proj j.as)
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ f
            obtain rfl := Discrete.eq_of_hom f
            simp } }
  have hc : IsLimit c :=
    { lift := fun s => ModuleCat.ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).hom)
      fac := fun s j => by
        cases j with
        | mk j =>
          apply ModuleCat.hom_ext
          ext x
          simp [c]
      uniq := fun s m hm => by
        apply ModuleCat.hom_ext
        ext x j
        simpa [c] using congrArg (fun q : s.pt ⟶ Z' j => q.hom x) (hm ⟨j⟩) }
  let e : c.pt ≅ Z := hc.conePointUniqueUpToIso hZ.toLimitPresentation.isLimit
  exact (finitelyPresentedModule_iff A Z).2
    (Module.FinitePresentation.of_equiv e.toLinearEquiv)

/-- Filtered colimits of `R`-modules preserve kernels. -/
public lemma moduleCat_filteredColimit_preservesKernels
    {R : Type u₁} [Ring R] (J : Type (v))
    [Category.{v} J] [IsFiltered J] :
    ∀ {X Y : J ⥤ ModuleCat.{v} R} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (colim : (J ⥤ ModuleCat.{v} R) ⥤ _) := by
  intro X Y f
  have : AB5OfSize.{v, v} (AddCommGrpCat.{v}) := AB5OfSize_of_univLE.{v, v, v, v} _
  have : HasExactColimitsOfShape J (ModuleCat.{v} R) :=
    HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat R) AddCommGrpCat)
  infer_instance

private structure ModuleFPPresentationData (A : Type u) [CommRing A]
    (X : ModuleCat.{max u v} A) where
  I : Type (max u v)
  [cat : SmallCategory I]
  [filtered : IsFiltered I]
  cX : ColimitPresentation I X
  fp : ∀ i, Module.FinitePresentation A (cX.diag.obj i)

private noncomputable def moduleFPPresentationData (A : Type u) [CommRing A]
    (X : ModuleCat.{max u v} A) : ModuleFPPresentationData A X := by
  classical
  apply Classical.choice
  obtain ⟨ι, hpre, hdir, hnon, hdec, G, hadd, hmod, f, hsys, hfp, ⟨e⟩⟩ :=
    Module.exists_linearEquiv_directLimit_finitePresentation_max A X
  let : Preorder ι := hpre
  let : IsDirected ι (· ≤ ·) := hdir
  let : Nonempty ι := hnon
  let : DecidableEq ι := hdec
  let : (i : ι) → AddCommGroup (G i) := hadd
  let : (i : ι) → Module A (G i) := hmod
  let : DirectedSystem G (fun i j h => f i j h) := hsys
  let : IsFiltered ι := inferInstance
  let p : ColimitPresentation ι (ModuleCat.of A (Module.DirectLimit G f)) :=
    { diag := ModuleCat.directLimitDiagram G f
      ι := (ModuleCat.directLimitCocone G f).ι
      isColimit := ModuleCat.directLimitIsColimit G f }
  exact ⟨{ I := ι, cX := p.ofIso e.symm.toModuleIso, fp := hfp }⟩

private def fpRestrictedYoneda (A : Type u) [CommRing A]
    (X : ModuleCat.{max u v} A) :
    (FinitelyPresentedModuleCat.{u, max u v} A)ᵒᵖ ⥤ Type (max u v) :=
  (finitelyPresentedModule.{u, max u v} A).ι.op ⋙ yoneda.obj X

private def fpRestrictedYonedaMap (A : Type u) [CommRing A]
    {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) :
    fpRestrictedYoneda A X ⟶ fpRestrictedYoneda A Y :=
  Functor.whiskerLeft (finitelyPresentedModule.{u, max u v} A).ι.op
    (yoneda.map f)

private def fpYonedaComparison (A : Type u) [CommRing A]
    (X : FinitelyPresentedModuleCat.{u, max u v} A) :
    yoneda.obj X ≅
      (finitelyPresentedModule.{u, max u v} A).ι.op ⋙
        yoneda.obj X.obj := by
  classical
  let hι := (finitelyPresentedModule.{u, max u v} A).fullyFaithfulι
  refine NatIso.ofComponents
    (fun T => Equiv.toIso
      (hι.homEquiv (X := T.unop) (Y := X))) ?_
  intro T S f
  ext g
  rfl

private noncomputable def fpRestrictedYonedaPresentationOf
    (A : Type u) [CommRing A] {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    {X : ModuleCat.{max u v} A} (cX : ColimitPresentation I X)
    (hPX : ∀ i, Module.FinitePresentation A (cX.diag.obj i)) :
    IndObjectPresentation (fpRestrictedYoneda A X) := by
  classical
  let C := FinitelyPresentedModuleCat.{u, max u v} A
  let D : I ⥤ C :=
    { obj := fun i => ⟨cX.diag.obj i, (finitelyPresentedModule_iff A _).2 (hPX i)⟩
      map := fun {i j} f => ObjectProperty.homMk (cX.diag.map f)
      map_id i := ObjectProperty.hom_ext _ (cX.diag.map_id i)
      map_comp f g := ObjectProperty.hom_ext _ (cX.diag.map_comp f g) }
  let c : Cocone (D ⋙ yoneda) :=
    { pt := fpRestrictedYoneda A X
      ι :=
        { app := fun i =>
            (fpYonedaComparison A (D.obj i)).hom ≫
              Functor.whiskerLeft
                (finitelyPresentedModule.{u, max u v} A).ι.op
                (yoneda.map (cX.ι.app i))
          naturality := by
            intro i j f
            ext T g
            change (g.hom ≫ cX.diag.map f) ≫ cX.ι.app j =
              g.hom ≫ cX.ι.app i
            rw [Category.assoc, cX.w f] } }
  have hc : IsColimit c := by
    apply Limits.evaluationJointlyReflectsColimits
    intro T
    letI : Module.FinitePresentation A
        ((finitelyPresentedModule.{u, max u v} A).ι.obj T.unop) := T.unop.property
    let : IsFinitelyPresentable.{max u v}
        ((finitelyPresentedModule.{u, max u v} A).ι.obj T.unop) :=
      finitePresentation_isFinitelyPresentable A _ T.unop.property
    let ev := (evaluation Cᵒᵖ (Type (max u v))).obj T
    let q := coyoneda.obj (Opposite.op
      ((finitelyPresentedModule.{u, max u v} A).ι.obj T.unop))
    let D₁ : I ⥤ Type (max u v) := (D ⋙ yoneda) ⋙ ev
    let D₂ : I ⥤ Type (max u v) := cX.diag ⋙ q
    let hι := (finitelyPresentedModule.{u, max u v} A).fullyFaithfulι
    let α : D₁ ≅ D₂ := NatIso.ofComponents
      (fun i => Equiv.toIso (hι.homEquiv (X := T.unop) (Y := D.obj i))) (by
        intro i j f
        ext g
        rfl)
    let c₁ : Cocone D₁ := ev.mapCocone c
    let cXc : Cocone cX.diag := Cocone.mk X cX.ι
    let c₂ : Cocone D₂ := q.mapCocone cXc
    let w : (Cocone.precompose α.inv).obj c₁ ≅ c₂ := Cocone.ext
      (Iso.refl _) (by
        intro i
        ext g
        rfl)
    exact (IsColimit.equivOfNatIsoOfIso α c₁ c₂ w).symm (isColimitOfPreserves q cX.isColimit)
  exact IndObjectPresentation.ofCocone c hc

private def moduleHomEquiv (A : Type u) [CommRing A]
    (M : ModuleCat.{max u v} A) :
    (ModuleCat.of A (ULift.{max u v} A) ⟶ M) ≃ M where
  toFun f := f.hom (ULift.up 1)
  invFun m := ModuleCat.ofHom
    ((LinearMap.toSpanSingleton A M m).comp ULift.moduleEquiv.toLinearMap)
  left_inv f := by
    ext a
    calc
      _ = (ULift.down a) • f.hom (ULift.up 1) := by
        simp [LinearMap.toSpanSingleton_apply]
      _ = f.hom ((ULift.down a) • ULift.up (1 : A)) := by rw [map_smul]
      _ = f.hom a := by
        congr 1
        cases a with
        | up b =>
          change ULift.up (b * 1) = ULift.up b
          simp
  right_inv m := by
    simp [LinearMap.toSpanSingleton_apply]

private noncomputable def restrictedYonedaModuleCocone
    (A : Type u) [CommRing A] {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ FinitelyPresentedModuleCat.{u, max u v} A}
    (X : ModuleCat.{max u v} A)
    (ι : D ⋙ yoneda ⟶ (Functor.const I).obj (fpRestrictedYoneda A X)) : Cocone (D ⋙
      (finitelyPresentedModule.{u, max u v} A).ι) := by
  refine ⟨X, ?_⟩
  let P := finitelyPresentedModule.{u, max u v} A
  refine
    { app := fun i =>
        (yonedaEquiv (F := fpRestrictedYoneda A X) (ι.app i) : P.ι.obj (D.obj i) ⟶ X)
      naturality := ?_ }
  intro i j f
  change (fpRestrictedYoneda A X).map (Opposite.op (D.map f))
      (yonedaEquiv (ι.app j)) = yonedaEquiv (ι.app i)
  calc
    _ = yonedaEquiv (yoneda.map (D.map f) ≫ ι.app j) :=
      yonedaEquiv_naturality (ι.app j) (D.map f)
    _ = yonedaEquiv (ι.app i) := by
      have h := congrArg (yonedaEquiv (F := fpRestrictedYoneda A X)) (ι.naturality f)
      simpa using h

private noncomputable def restrictedYonedaModuleCocone_isColimit
    (A : Type u) [CommRing A] {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ FinitelyPresentedModuleCat.{u, max u v} A}
    (X : ModuleCat.{max u v} A)
    (ι : D ⋙ yoneda ⟶ (Functor.const I).obj (fpRestrictedYoneda A X))
    (hc : IsColimit (Cocone.mk (fpRestrictedYoneda A X) ι)) :
    IsColimit (restrictedYonedaModuleCocone A X ι) := by
  classical
  let P := finitelyPresentedModule.{u, max u v} A
  let U := forget (ModuleCat.{max u v} A)
  have hR : P (ModuleCat.of A (ULift.{max u v} A)) :=
    (finitelyPresentedModule_iff A _).2 (.of_equiv ULift.moduleEquiv.symm)
  let R : P.FullSubcategory := ⟨ModuleCat.of A (ULift.{max u v} A), hR⟩
  let ev := (evaluation P.FullSubcategoryᵒᵖ (Type (max u v))).obj (Opposite.op R)
  let D₁ : I ⥤ Type (max u v) := (D ⋙ yoneda) ⋙ ev
  let D₂ : I ⥤ Type (max u v) := D ⋙ P.ι ⋙ U
  let hι := P.fullyFaithfulι
  let α : D₁ ≅ D₂ := NatIso.ofComponents (fun i => Equiv.toIso <|
    (hι.homEquiv (X := R) (Y := D.obj i)).trans (moduleHomEquiv A (D.obj i).obj)) (by
      intro i j f
      ext x
      rfl)
  let c := Cocone.mk (fpRestrictedYoneda A X) ι
  let c₁ : Cocone D₁ := ev.mapCocone c
  let c₂ : Cocone D₂ := U.mapCocone (restrictedYonedaModuleCocone A X ι)
  let w : (Cocone.precompose α.inv).obj c₁ ≅ c₂ := Cocone.ext
    (Equiv.toIso (moduleHomEquiv A X)) (by
      intro i
      ext x
      let g : R ⟶ D.obj i := (hι.homEquiv (X := R) (Y := D.obj i)).symm
        ((moduleHomEquiv A (D.obj i).obj).symm x)
      have hg : (hι.homEquiv (X := R) (Y := D.obj i) g).hom (ULift.up (1 : A)) = x := by
        change moduleHomEquiv A (D.obj i).obj
          (hι.homEquiv (X := R) (Y := D.obj i)
            ((hι.homEquiv (X := R) (Y := D.obj i)).symm
            ((moduleHomEquiv A (D.obj i).obj).symm x))) = x
        simp
      let eY := yonedaEquiv (X := D.obj i) (F := fpRestrictedYoneda A X)
      have hη : ι.app i = eY.symm (eY (ι.app i)) := (eY.symm_apply_apply _).symm
      change moduleHomEquiv A X ((ι.app i).app (Opposite.op R) g) =
        (eY (ι.app i)).hom x
      rw [hη]
      simp only [eY]
      change (eY (ι.app i)).hom
        ((hι.homEquiv (X := R) (Y := D.obj i) g).hom (ULift.up (1 : A))) =
        (eY (ι.app i)).hom x
      rw [hg])
  have hc₂ : IsColimit c₂ := IsColimit.equivOfNatIsoOfIso α c₁ c₂ w (isColimitOfPreserves ev hc)
  let S := ULift.{max u v} A
  let e : A ≃+* S := ULift.ringEquiv.symm
  let E : ModuleCat.{max u v} S ≌ ModuleCat.{max u v} A :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have hforget : E.symm.functor ⋙ forget (ModuleCat.{max u v} S) = U := rfl
  letI : ReflectsFilteredColimits U := by
    rw [← hforget]
    infer_instance
  exact isColimitOfReflects U hc₂

/-- Preserving the limit of `parallelPair (H.map f) 0` gives preserving that of
`parallelPair f 0 ⋙ H`. -/
private lemma preservesLimit_parallelPair_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (H : C ⥤ D) [H.PreservesZeroMorphisms]
    (K : D ⥤ E) {X Y : C} (f : X ⟶ Y) (_ : PreservesLimit (parallelPair (H.map f) 0) K) :
    PreservesLimit (parallelPair f 0 ⋙ H) K :=
  preservesLimit_of_iso_diagram K
    (parallelPair.ext (Iso.refl _) (Iso.refl _) :
      parallelPair (H.map f) 0 ≅ parallelPair f 0 ⋙ H)

private lemma whiskeringRight_preservesKernel
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasKernels C]
    (G : C ⥤ D) {X Y : J ⥤ C} (f : X ⟶ Y)
    [∀ j, PreservesLimit (parallelPair (f.app j) 0) G] :
    PreservesLimit (parallelPair f 0) ((Functor.whiskeringRight J C D).obj G) := by
  apply preservesLimit_of_evaluation
  intro j
  change PreservesLimit (parallelPair f 0) ((evaluation J C).obj j ⋙ G)
  have : PreservesLimit (parallelPair f 0) ((evaluation J C).obj j) :=
    evaluation_preservesLimit_of_hasKernel_app f j
  have : PreservesLimit (parallelPair f 0 ⋙ (evaluation J C).obj j) G :=
    preservesLimit_parallelPair_comp _ G f
      (inferInstanceAs (PreservesLimit (parallelPair (f.app j) 0) G))
  infer_instance

add_to_stacks 0GNM "additivity" ModuleCat.filteredColimitExtension_additive
add_to_stacks 0GNM "arbitrary direct sums" ModuleCat.filteredColimitExtension_preservesCoproducts

/-- If filtered colimits commute with kernels in the target, the filtered-colimit extension
of a left exact functor on finitely presented modules is left exact. -/
@[stacks 0GNM "left exactness"]
public lemma filteredColimitExtension_preservesFiniteLimits
    [IsCoherentRing A] (E : FilteredColimitExtension A F) [HasKernels B]
    [PreservesFiniteLimits F]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J],
      ∀ {X Y : J ⥤ B} (f : X ⟶ Y),
        PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)] :
    PreservesFiniteLimits E.functor := by
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have : E.functor.Additive := ModuleCat.filteredColimitExtension_additive A E
  have hker : ∀ {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) E.functor := by
    intro X Y f
    let dx := moduleFPPresentationData A X
    let dy := moduleFPPresentationData A Y
    let : SmallCategory dx.I := dx.cat
    let : IsFiltered dx.I := dx.filtered
    let : SmallCategory dy.I := dy.cat
    let : IsFiltered dy.I := dy.filtered
    let PX := fpRestrictedYonedaPresentationOf A dx.cX dx.fp
    let PY := fpRestrictedYonedaPresentationOf A dy.cX dy.fp
    let η := fpRestrictedYonedaMap A f
    let ζ : fpRestrictedYoneda A X ⟶ fpRestrictedYoneda A Y :=
      fpRestrictedYonedaMap A (0 : X ⟶ Y)
    let P : IndParallelPairPresentation η ζ :=
      NonemptyParallelPairPresentationAux.presentation η ζ PX PY
    let cX := restrictedYonedaModuleCocone A X P.ι₁
    let cY := restrictedYonedaModuleCocone A Y P.ι₂
    have hcX : IsColimit cX :=
      restrictedYonedaModuleCocone_isColimit A X P.ι₁ P.isColimit₁
    have hcY : IsColimit cY :=
      restrictedYonedaModuleCocone_isColimit A Y P.ι₂ P.isColimit₂
    let hι := (finitelyPresentedModule.{u, max u v} A).ι
    let D := P.F₁ ⋙ hι
    let G := P.F₂ ⋙ hι
    let fD : D ⟶ G := Functor.whiskerRight P.φ hι
    have hstage (i : P.I) : cX.ι.app i ≫ f = fD.app i ≫ cY.ι.app i := by
      have hnat := congrArg (fun t => P.ι₁.app i ≫ t) P.hf
      have hmap : P.ι₁.app i ≫ P.isColimit₁.map
          (Cocone.mk _ P.ι₂) (Functor.whiskerRight P.φ yoneda) =
          (Functor.whiskerRight P.φ yoneda).app i ≫ P.ι₂.app i :=
        P.isColimit₁.ι_map _ _ i
      rw [hmap] at hnat
      have hh := congrArg (yonedaEquiv (X := P.F₁.obj i)) hnat
      rwa [yonedaEquiv_comp, yonedaEquiv_comp] at hh
    let C := FinitelyPresentedModuleCat.{u, max u v} A
    let HI := (Functor.whiskeringRight P.I C (ModuleCat.{max u v} A)).obj hι
    let E₀ : C ⥤ B := hι ⋙ E.functor
    let H₀ := (Functor.whiskeringRight P.I C B).obj E₀
    let T : (P.I ⥤ C) ⥤ ModuleCat.{max u v} A := HI ⋙ colim
    have : HasKernel P.φ := hasKernel_of_hasKernel_app P.φ
    have : ∀ i, PreservesLimit (parallelPair (P.φ.app i) 0) hι :=
      fun i => (finitelyPresentedModule A).preservesKernels_ι (P.φ.app i)
    have : PreservesLimit (parallelPair P.φ 0) HI :=
      whiskeringRight_preservesKernel hι P.φ
    have : PreservesLimit (parallelPair fD 0)
        (colim : (P.I ⥤ ModuleCat.{max u v} A) ⥤ _) :=
      moduleCat_filteredColimit_preservesKernels P.I fD
    have : PreservesLimit (parallelPair P.φ 0 ⋙ HI)
        (colim : (P.I ⥤ ModuleCat.{max u v} A) ⥤ _) :=
      preservesLimit_parallelPair_comp HI _ P.φ ‹_›
    have : PreservesLimit (parallelPair P.φ 0) T := inferInstance
    have : PreservesFiniteLimits E₀ := preservesFiniteLimits_of_natIso E.iso.symm
    have : ∀ i, PreservesLimit (parallelPair (P.φ.app i) 0) E₀ := fun _ => inferInstance
    have : PreservesLimit (parallelPair P.φ 0) H₀ :=
      whiskeringRight_preservesKernel E₀ P.φ
    have : PreservesLimit (parallelPair P.φ 0 ⋙ H₀) (colim : (P.I ⥤ B) ⥤ B) :=
      preservesLimit_parallelPair_comp H₀ _ P.φ inferInstance
    have : PreservesLimit (parallelPair P.φ 0) (H₀ ⋙ colim) := inferInstance
    let e : T ⋙ E.functor ≅ H₀ ⋙ colim :=
      Functor.isoWhiskerLeft HI (preservesColimitNatIso E.functor)
    have : PreservesLimit (parallelPair P.φ 0) (T ⋙ E.functor) :=
      preservesLimit_of_natIso _ e.symm
    have : PreservesLimit (parallelPair P.φ 0 ⋙ T) E.functor :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves T (kernelIsKernel P.φ))
        (isLimitOfPreserves (T ⋙ E.functor) (kernelIsKernel P.φ))
    have : PreservesLimit (parallelPair (T.map P.φ) 0) E.functor :=
      preservesLimit_of_iso_diagram _
        (diagramIsoParallelPair (parallelPair P.φ 0 ⋙ T) ≪≫
          parallelPair.eqOfHomEq rfl (by simp))
    let eX : colimit D ≅ X := (colimit.isColimit D).coconePointUniqueUpToIso hcX
    let eY : colimit G ≅ Y := (colimit.isColimit G).coconePointUniqueUpToIso hcY
    have heX (i : P.I) : colimit.ι D i ≫ eX.hom = cX.ι.app i :=
      colimit.comp_coconePointUniqueUpToIso_hom hcX i
    have heY (i : P.I) : colimit.ι G i ≫ eY.hom = cY.ι.app i :=
      colimit.comp_coconePointUniqueUpToIso_hom hcY i
    apply preservesLimit_of_iso_diagram E.functor
      (parallelPair.ext eX eY ?_ ?_ :
        parallelPair (T.map P.φ) 0 ≅ parallelPair f 0)
    · apply colimit.hom_ext
      intro i
      change colimit.ι D i ≫ colimMap fD ≫ eY.hom =
        colimit.ι D i ≫ eX.hom ≫ f
      rw [ι_colimMap_assoc, heY, ← Category.assoc, heX]
      exact (hstage i).symm
    · simp
  let : ∀ {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) E.functor := hker
  exact Functor.preservesFiniteLimits_of_preservesKernels E.functor

end ModuleCat
