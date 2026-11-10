module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Assembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AlgSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.ChartFromE
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.ThickeningRings
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartBiconditional
public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.RingTheory.Etale.FaithfullyFlatLift

/-!
# Formal smoothness of morphisms of algebraic spaces on étale charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` admitting a commuting square of étale
scheme charts `a : U ⟶ X`, `b : V ⟶ Y`, `ψ : U ⟶ V` with `a` surjective and `ψ` formally smooth.
Then `f` is formally smooth. Together with the converse implications, formal smoothness of `f` is
equivalent to formal smoothness of `ψ` for every, or for some surjective, such square.

## Main results

* `AlgebraicGeometry.Space.exists_chart_setup`: an infinitesimal lifting problem for `f` admits an
  affine object `E` étale over `U ×_Y T'` and an affine étale surjection onto `T` through which `x`
  factors over `E`.
* `AlgebraicGeometry.Space.exists_isLift_of_chart`: if `a : U ⟶ X` is a surjective étale chart with
  `a ≫ f` formally smooth, every affine infinitesimal lifting problem for `f` has a solution.
* `AlgebraicGeometry.Space.formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme`: a
  chart square with `a` surjective and `ψ` formally smooth makes `f` formally smooth.
* `AlgebraicGeometry.Space.formallySmooth_tfae_etaleCharts`: the equivalence of formal smoothness
  of `f`, of `ψ` on every étale chart square, and of `ψ` on some surjective étale chart square.
* `AlgebraicGeometry.Space.formallySmooth_iff_holdsOnEveryEtaleChart`,
  `AlgebraicGeometry.Space.formallySmooth_iff_holdsOnSurjectiveEtaleChart_of_isAlgebraicSpace`:
  the two equivalences with formal smoothness of `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Cardinal

universe u

namespace AlgebraicGeometry.Space

open ChartGlue

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The geometric setup of a lifting problem.** For an infinitesimal lifting problem for `f`,
there is an affine object `E` étale over `U ×_Y T'` and an affine étale surjection `Wa ⟶ T`
through which `x` factors over `E`. -/
theorem exists_chart_setup (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {T T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (i : T ⟶ T')
    (x : X.obj (op T)) (y : Y.obj (op T')) (hxy : f.app (op T) x = Y.map i.op y) :
    let hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hY (a ≫ f)
    ∃ (E : BigFppfOver B S hS) (eZ : E ⟶ UZ B S hS T' f y a hrep) (Wa : BigFppfOver B S hS)
      (wa : Wa ⟶ T) (m : Wa ⟶ E), IsAffine ((BigFppfOver.toScheme B S hS).obj E) ∧
      Etale ((BigFppfOver.toScheme B S hS).map eZ) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Wa) ∧
      Etale ((BigFppfOver.toScheme B S hS).map wa) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map wa) ∧
      m ≫ eZ ≫ UZsnd B S hS T' f y a hrep = wa ≫ i ∧
      a.app _ (m ≫ eZ ≫ UZfst B S hS T' f y a hrep) = X.map wa.op x := by
  intro hrep
  let W := ha.rep.pullback (yonedaEquiv.symm x)
  let wU : W ⟶ U := ha.rep.fst' (yonedaEquiv.symm x)
  let wT : W ⟶ T := ha.rep.snd (yonedaEquiv.symm x)
  have hwsq : yoneda.map wU ≫ a = yoneda.map wT ≫ yonedaEquiv.symm x := by
    rw [Functor.relativelyRepresentable.map_fst']
    exact ha.rep.w (yonedaEquiv.symm x)
  have hwEt : Etale ((BigFppfOver.toScheme B S hS).map wT) :=
    ha.property _ _ _ (ha.rep.isPullback (yonedaEquiv.symm x))
  have hwSurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map wT) :=
    (haSurj.property _ _ _ (ha.rep.isPullback (yonedaEquiv.symm x))).surj
  have hcomp : yoneda.map wU ≫ (a ≫ f) = yoneda.map (wT ≫ i) ≫ yonedaEquiv.symm y := by
    rw [← Category.assoc, hwsq, Category.assoc, Functor.map_comp, Category.assoc]
    congr 1
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp, yonedaEquiv_apply, yonedaEquiv_symm_app_apply] using hxy
  let g : W ⟶ UZ B S hS T' f y a hrep := hrep.lift' wU (wT ≫ i) hcomp
  have hgsnd : g ≫ UZsnd B S hS T' f y a hrep = wT ≫ i := hrep.lift'_snd _ _ _
  have hgfst : g ≫ UZfst B S hS T' f y a hrep = wU := hrep.lift'_fst _ _ _
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := inferInstance
  obtain ⟨E, eZ, Wa, wa, m, w', hEaff, hEet, hWaff, hwaEt, hwaSurj, hw'T, hw'Z⟩ :=
    exists_affine_etale_cover_through B S hS g wT hwEt hwSurj
  refine ⟨E, eZ, Wa, wa, m, hEaff, hEet, hWaff, hwaEt, hwaSurj, ?_, ?_⟩
  · rw [← Category.assoc, ← hw'Z, Category.assoc, hgsnd, ← Category.assoc, hw'T]
  · rw [← Category.assoc, ← hw'Z, Category.assoc, hgfst]
    have h1 : a.app _ wU = X.map wT.op x := by
      have := congrArg yonedaEquiv hwsq
      simpa [yonedaEquiv_comp, yonedaEquiv_apply, yonedaEquiv_symm_app_apply] using this
    have h2 : a.app _ (w' ≫ wU) = X.map w'.op (a.app _ wU) := (aPt_comp (a := a) w' wU).symm
    rw [h2, h1, ← Functor.map_comp_apply, ← op_comp, hw'T]

/-- **Infinitesimal lifts against a surjective étale chart with formally smooth composite.**
Let `a : U ⟶ X` be a surjective étale chart of the algebraic space `X` with `a ≫ f` formally
smooth. Then every infinitesimal lifting problem for `f` over an affine square-zero thickening
`T ⟶ T'` has a solution. -/
theorem exists_isLift_of_chart (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hfs : FormallySmooth (a ≫ f))
    {T T' : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (x : X.obj (op T)) (y : Y.obj (op T')) (hxy : f.app (op T) x = Y.map i.op y) :
    ∃ z, IsLift f i x y z := by
  obtain ⟨E, eZ, Wa, wa, m, hEaff, hEet, hWaff, hwaEt, hwaSurj, hsnd, hfst⟩ :=
    exists_chart_setup hX hY a ha haSurj i x y hxy
  have := hEaff
  have := hWaff
  have hε : FormallyEtale (yoneda.map eZ) :=
    formallyEtale_of_etale B S hS _ (presheaf_yoneda_map_of_inverseImage B S hS (P := @Etale)
      inferInstance eZ hEet)
  obtain ⟨hg₀, hrel, hRsm⟩ := chart_of_etale (hfa := formallyEtale_of_etale B S hS a ha) hfs hε
  let : Algebra (ringOf B S hS T') (ringE B S hS (E := E)) :=
    ringAlg B S hS T' (eZ ≫ UZsnd B S hS T' f y a _)
  let : Algebra (ringOf B S hS T') (ringE B S hS (E := T)) := ringAlg B S hS T' i
  let : Algebra (ringOf B S hS T') (ringE B S hS (E := Wa)) := ringAlg B S hS T' (wa ≫ i)
  have : Algebra.FormallySmooth (ringOf B S hS T') (ringE B S hS (E := E)) := hRsm
  have hA : Function.Surjective (algebraMap (ringOf B S hS T') (ringE B S hS (E := T))) :=
    surjective_thickening B S hS T' i hi
  have hI : RingHom.ker (algebraMap (ringOf B S hS T') (ringE B S hS (E := T))) ^ 2 = ⊥ :=
    ker_sq_thickening B S hS T' i hi
  have : Fact (Function.Surjective
      (algebraMap (ringOf B S hS T') (ringE B S hS (E := T)))) := ⟨hA⟩
  have : Fact (RingHom.ker (algebraMap (ringOf B S hS T') (ringE B S hS (E := T))) ^ 2 = ⊥) :=
    ⟨hI⟩
  let hW := homRing B S hS T' (wa ≫ i) i wa rfl
  let : Algebra (ringE B S hS (E := T)) (ringE B S hS (E := Wa)) := hW.toRingHom.toAlgebra
  have : IsScalarTower (ringOf B S hS T') (ringE B S hS (E := T)) (ringE B S hS (E := Wa)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (hW.commutes r).symm
  have : Algebra.Etale (ringE B S hS (E := T)) (ringE B S hS (E := Wa)) := by
    change RingHom.Etale ((BigFppfOver.toScheme B S hS).map wa).appTop.hom
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hwaEt
  have : Module.FaithfullyFlat (ringE B S hS (E := T)) (ringE B S hS (E := Wa)) := by
    change RingHom.FaithfullyFlat ((BigFppfOver.toScheme B S hS).map wa).appTop.hom
    have := hwaEt
    exact (AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp
      ⟨inferInstance, ⟨hwaSurj⟩⟩
  obtain ⟨C, _, _, hCet, hCff, hCcard, ⟨e⟩⟩ := Stacks.ChartGlue.exists_etale_faithfullyFlat_lift
    (ringOf B S hS T') (ringE B S hS (E := T)) (ringE B S hS (E := Wa)) hA hI
  let ū₀ := homRing B S hS T' (wa ≫ i) (eZ ≫ UZsnd B S hS T' f y a _) m hsnd
  let fr : ringE B S hS (E := E) →ₐ[ringOf B S hS T']
      ringE B S hS (E := T) ⊗[ringOf B S hS T'] C :=
    (e.symm.restrictScalars (ringOf B S hS T')).toAlgHom.comp ū₀
  let : Algebra (ringE B S hS (E := E)) (ringE B S hS (E := T) ⊗[ringOf B S hS T'] C) :=
    fr.toRingHom.toAlgebra
  have : IsScalarTower (ringOf B S hS T') (ringE B S hS (E := E))
      (ringE B S hS (E := T) ⊗[ringOf B S hS T'] C) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (fr.commutes r).symm
  have : Module.Projective (ringE B S hS (E := E))
      Ω[ringE B S hS (E := E)⁄ringOf B S hS T'] :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  let κ : Cardinal.{u} := max (max #(ringOf B S hS T') #C) (max #(ringE B S hS (E := E)) ℵ₀)
  have hκ : ℵ₀ ≤ κ := le_max_of_le_right (le_max_right _ _)
  have hκlt : κ < B.cutoff :=
    max_lt (max_lt (mk_ringOf_lt B S hS T')
      (hCcard.trans_lt (max_lt (mk_ringOf_lt B S hS T') B.aleph0_lt_cutoff)))
      (max_lt (mk_lt_of_contains_spec B (contains_specRingE B S hS)) B.aleph0_lt_cutoff)
  have hA' : #(ringOf B S hS T') ≤ κ := le_max_of_le_left (le_max_left _ _)
  have hC : #C ≤ κ := le_max_of_le_left (le_max_right _ _)
  have hR : #(ringE B S hS (E := E)) ≤ κ := le_max_of_le_right (le_max_left _ _)
  let P : ObjectProperty (CommAlgCat.{u} (ringOf B S hS T')) := fun D ↦ #D ≤ κ
  have hP : ∀ (D : Type u) [CommRing D] [Algebra (ringOf B S hS T') D], #D ≤ κ →
      P (CommAlgCat.of (ringOf B S hS T') D) := fun _ _ _ h ↦ h
  have hPs : ∀ D : P.FullSubcategory, B.Contains (Spec (CommRingCat.of D.obj)) :=
    fun D ↦ contains_spec_of_mk_lt B (D.property.trans_lt hκlt)
  let Φ := algChart B S hS T' f y P hPs (ringE B S hS (E := E)) (contains_specRingE B S hS)
    (chartPoint B S hS T' f y a _ eZ) hg₀ hrel
  have hnil : IsNilpotent (RingHom.ker
      (Stacks.ChartGlue.Concrete.π₁ (ringOf B S hS T') (ringE B S hS (E := T)) C :
        C →+* ringE B S hS (E := T) ⊗[ringOf B S hS T'] C)) :=
    ⟨2, by rw [Ideal.zero_eq_bot]; exact Stacks.ChartGlue.Concrete.ker_bc_sq _ _ hA hI C⟩
  let u' := Algebra.FormallySmooth.liftOfSurjective fr
    (Stacks.ChartGlue.Concrete.π₁ (ringOf B S hS T') (ringE B S hS (E := T)) C)
    (Stacks.ChartGlue.Concrete.bc_surjective _ _ hA C) hnil
  have hu' : (Stacks.ChartGlue.Concrete.π₁ (ringOf B S hS T') (ringE B S hS (E := T)) C).comp u' =
      Stacks.ChartGlue.FrameDescent.frame (ringE B S hS (E := E))
        (Stacks.ChartGlue.Concrete.Bb (ringOf B S hS T') (ringE B S hS (E := T)) C) :=
    AlgHom.ext fun r ↦ Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ hnil r
  have hBb : B.Contains (Spec (CommRingCat.of (ringE B S hS (E := T) ⊗[ringOf B S hS T'] C))) :=
    contains_spec_of_mk_lt B ((Stacks.ChartGlue.Assembly.mk_Bb hκ _ hA C hA' hC).trans_lt hκlt)
  have hWc := contains_specRingE B S hS (E := Wa)
  let K := Stacks.ChartGlue.Assembly.Kc hκ hP (ringE B S hS (E := T)) C hA' hC
  let x₀ : (algFunctor B S hS T' P hPs f y).obj K.O' :=
    ⟨X.map (specIso B S hS T' i).hom.op x, by
      rw [f.naturality_apply, hxy, ← Functor.map_comp_apply, ← op_comp,
        specIso_hom_comp]⟩
  let e' := (e.symm.restrictScalars (ringOf B S hS T')).toAlgHom
  let ι'' := (Algebra.ofId (ringE B S hS (E := T))
    (ringE B S hS (E := T) ⊗[ringOf B S hS T'] C)).restrictScalars (ringOf B S hS T')
  have he' : e'.comp hW = ι'' := AlgHom.ext fun r ↦ e.symm.commutes r
  have hfst' : aPt (a := a) (m ≫ eZ ≫ UZfst B S hS T' f y a _) = X.map wa.op x := hfst
  have hū : Φ.pt K.B₁' (Stacks.ChartGlue.FrameDescent.frame (ringE B S hS (E := E))
      (Stacks.ChartGlue.Concrete.Bb (ringOf B S hS T') (ringE B S hS (E := T)) C)) =
      (algFunctor B S hS T' P hPs f y).map K.ι' x₀ := by
    apply Subtype.ext
    change X.map (specMap B S hS T' (contains_specRingE B S hS) hBb fr).op
        (X.map (specIso B S hS T' (eZ ≫ UZsnd B S hS T' f y a _)).hom.op
          (aPt (a := a) (eZ ≫ UZfst B S hS T' f y a _))) =
      X.map (specMap B S hS T' (contains_specRingE B S hS) hBb ι'').op
        (X.map (specIso B S hS T' i).hom.op x)
    have hfr : specMap B S hS T' (contains_specRingE B S hS) hBb fr =
        specMap B S hS T' hWc hBb e' ≫ specMap B S hS T' (contains_specRingE B S hS) hWc ū₀ :=
      specMap_comp B S hS T' _ hWc hBb ū₀ e'
    have hι : specMap B S hS T' (contains_specRingE B S hS) hBb ι'' =
        specMap B S hS T' hWc hBb e' ≫ specMap B S hS T' (contains_specRingE B S hS) hWc hW := by
      rw [← he']; exact specMap_comp B S hS T' _ hWc hBb hW e'
    rw [aPt_comp, aPt_comp, hfr, Category.assoc, ← Category.assoc (specMap _ _ _ _ _ _ ū₀),
      specMap_homRing_comp B S hS T' (wa ≫ i) (eZ ≫ UZsnd B S hS T' f y a _) m hsnd,
      Category.assoc, ← aPt_comp, ← aPt_comp, hfst', hι, ← Functor.map_comp_apply,
      ← op_comp, ← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply,
      ← op_comp]
    simp only [Category.assoc]
    rw [← specMap_homRing_comp B S hS T' (wa ≫ i) i wa rfl]
  have hsep : ∀ y₁ y₂ : (algFunctor B S hS T' P hPs f y).obj K.O',
      (algFunctor B S hS T' P hPs f y).map K.ι' y₁ =
        (algFunctor B S hS T' P hPs f y).map K.ι' y₂ → y₁ = y₂ := by
    intro y₁ y₂ h
    apply Subtype.ext
    have hff : (ι'' : ringE B S hS (E := T) →+*
        ringE B S hS (E := T) ⊗[ringOf B S hS T'] C).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
    have := hCet
    have hfp : (ι'' : ringE B S hS (E := T) →+*
        ringE B S hS (E := T) ⊗[ringOf B S hS T'] C).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.2 inferInstance
    exact eq_of_map_specMap_eq B S hS T' (contains_specRingE B S hS) hBb ι'' hX.isSheaf hff hfp
      y₁.1 y₂.1 (congrArg Subtype.val h)
  have hCc : B.Contains (Spec (CommRingCat.of C)) := contains_spec_of_mk_lt B (hC.trans_lt hκlt)
  have hCC : B.Contains (Spec (CommRingCat.of (C ⊗[ringOf B S hS T'] C))) :=
    contains_spec_of_mk_lt B ((Stacks.ChartGlue.Assembly.mk_B₂ hκ C hC).trans_lt hκlt)
  have hffC : (algebraMap (ringOf B S hS T') C).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 hCff
  have := hCet
  have hfpC : (algebraMap (ringOf B S hS T') C).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.2 inferInstance
  have hglue : ∀ z : (algFunctor B S hS T' P hPs f y).obj K.B₁,
      (algFunctor B S hS T' P hPs f y).map K.p₁ z = (algFunctor B S hS T' P hPs f y).map K.p₂ z →
        ∃ z₀, (algFunctor B S hS T' P hPs f y).map K.ι z₀ = z := by
    intro z hz
    obtain ⟨z₀, hz₀⟩ := exists_of_map_specMap_eq B S hS T' (contains_specRingOf B S hS T') hCc hCC
      hX.isSheaf hffC hfpC z.1 (congrArg Subtype.val hz)
    have hcompat : f.app _ z₀ =
        Y.map (specToT B S hS T' _ (contains_specRingOf B S hS T')).op y := by
      refine eq_of_map_specMap_eq B S hS T' (contains_specRingOf B S hS T') hCc
        (Algebra.ofId _ C) hY.isSheaf hffC hfpC _ _ ?_
      rw [← f.naturality_apply, hz₀, z.2, ← Functor.map_comp_apply, ← op_comp,
        specMap_specToT]
    exact ⟨⟨z₀, hcompat⟩, Subtype.ext hz₀⟩
  obtain ⟨z, hz⟩ := Stacks.ChartGlue.Assembly.exists_lift hκ hP Φ (ringE B S hS (E := T)) C hA' hC
    hR x₀ hū u' hu' hglue hsep
  have hz' : X.map (specMap B S hS T' (contains_specRingOf B S hS T') (contains_specRingE B S hS)
      (Algebra.ofId _ (ringE B S hS (E := T)))).op z.1 = X.map (specIso B S hS T' i).hom.op x :=
    congrArg Subtype.val hz
  have hmor : i ≫ (specSelfIso B S hS T').inv = (specIso B S hS T' i).inv ≫
      specMap B S hS T' (contains_specRingOf B S hS T') (contains_specRingE B S hS)
        (Algebra.ofId _ (ringE B S hS (E := T))) := by
    apply eq_of_specObj_self
    rw [Category.assoc, ← specSelfIso_hom, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      specSelfIso_hom, specMap_specToT, ← specIso_hom_comp B S hS T' i, Iso.inv_hom_id_assoc]
  refine ⟨X.map (specSelfIso B S hS T').inv.op z.1, ?_, ?_⟩
  · rw [← Functor.map_comp_apply, ← op_comp, hmor, op_comp, Functor.map_comp_apply,
      hz', ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
      Functor.map_id_apply]
  · have h2 : f.app _ z.1 = Y.map (specSelfIso B S hS T').hom.op y := z.2
    rw [f.naturality_apply, h2, ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id,
      op_id, Functor.map_id_apply]

variable (B S hS)

/-- **Formal smoothness from a surjective étale chart.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` admitting a commuting square of étale scheme charts `a : U ⟶ X`,
`b : V ⟶ Y`, `ψ : U ⟶ V` whose chart of the source is surjective and whose morphism of schemes
`ψ` is formally smooth. Then `f` is formally smooth. -/
theorem formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hsq : a ≫ f = yoneda.map ψ ≫ b)
    (hψ : Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallySmooth f := fun _ _ hT hT' i hi x y hxy ↦
  exists_isLift_of_chart hX hY a ha haSurj
    (formallySmooth_chart_comp_of_formallySmoothScheme B S hS hb hsq hψ) hT hT' i hi x y hxy

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S`, the following are equivalent:
1. `f` is formally smooth;
2. for every commuting square of étale scheme charts `a : U ⟶ X`, `b : V ⟶ Y`, `ψ : U ⟶ V`, the
   morphism of schemes `ψ` is formally smooth;
3. there is a commuting square of étale scheme charts with `a` and `b` surjective and `ψ`
   formally smooth. -/
@[stacks 061K]
theorem formallySmooth_tfae_etaleCharts (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [FormallySmooth f,
      HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f,
      ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        yoneda.map ψ ≫ b = a ≫ f ∧
        Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ)] := by
  tfae_have 1 → 2 := holdsOnEveryEtaleChart_formallySmoothScheme'
  tfae_have 2 → 3 := fun hall ↦ by
    obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
    obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
    exact ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm,
      hall U V a b ψ haEtale hbEtale hdiag.symm⟩
  tfae_have 3 → 1 := fun ⟨U, V, a, b, ψ, ha, hb, haSurj, _, hdiag, hψ⟩ ↦
    formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme B S hS hX hY a b ψ ha hb
      haSurj hdiag.symm hψ
  tfae_finish

/-- A morphism of algebraic spaces is formally smooth if and only if, for every commuting square
of étale scheme charts, the morphism of schemes between the charts is formally smooth. -/
theorem formallySmooth_iff_holdsOnEveryEtaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f :=
  (formallySmooth_tfae_etaleCharts B S hS hX hY f).out 1 2

/-- A morphism of algebraic spaces is formally smooth if and only if there is a commuting square
of étale scheme charts, with surjective chart of the source, whose morphism of schemes between
the charts is formally smooth (`AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart`). -/
theorem formallySmooth_iff_holdsOnSurjectiveEtaleChart_of_isAlgebraicSpace
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  refine ⟨holdsOnSurjectiveEtaleChart_formallySmoothScheme' hX hY, ?_⟩
  rintro ⟨U, V, a, b, ψ, ha, hb, haSurj, hdiag, hψ⟩
  exact formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme B S hS hX hY a b ψ ha hb
    haSurj hdiag.symm hψ

end AlgebraicGeometry.Space

end
