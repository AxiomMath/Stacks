module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionDeformationEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.ResidueFibreLimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic

/-!
# Deforming a contraction étale locally on the base (Stacks 0E7C for schemes)

Let `S` be a scheme, `s ∈ S`, let `X` be a proper flat scheme of finite presentation over `S` and
let `h₀ : X_s ⟶ Y₀` be a morphism from the fibre over `s` to a proper scheme of dimension at most
one over `κ(s)` with `𝒪_{Y₀} ≅ h₀,*𝒪_{X_s}` and `R¹h₀,*𝒪_{X_s} = 0`. Then there are an étale
`U ⟶ S` with a point `u` over `s` of residue field `κ(s)`, a proper flat `Y ⟶ U` of finite
presentation and a morphism `h : X_U ⟶ Y` over `U` whose fibre over `u` is `h₀`. This is
[Stacks, Tag 0E7C] for schemes.

The proof is the source's. For `S` affine it is reduced to a scheme of finite type over `ℤ` by
absolute Noetherian approximation: `X` comes from a stage `S_i` of the system of the spectra of
the finitely generated subrings of `Γ(S, 𝒪_S)`, and since `κ(s)` is the colimit of the residue
fields `κ(s_i)` ([Stacks, Tag 0CUG]), `Y₀` and `h₀` come from a stage, with the same properties
(they descend along the faithfully flat field extension). The ring of a stage is of finite type
over `ℤ`, hence a G-ring ([Stacks, Tag 07PX]), and
`AlgebraicGeometry.C1590Private.ContractionDeformation.exists_etale_contraction_of_isGRing` gives
an elementary étale neighbourhood of `s_i` over which the contraction deforms; it is pulled back
to `S`.

## Main results

* `AlgebraicGeometry.C1590Private.ContractionDeformation.exists_etale_contraction_of_isAffine`:
  the affine case.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0CUG](https://stacks.math.columbia.edu/tag/0CUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.C1590Private

namespace ContractionDeformation

/-- A cartesian square stays cartesian after composing its bottom right corner with an
isomorphism. -/
theorem isPullback_comp_iso_right {P X Y Z Z' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback a b f g) (e : Z ⟶ Z') [IsIso e] :
    IsPullback a b (f ≫ e) (g ≫ e) := by
  have := H.paste_vert (IsPullback.of_vert_isIso ⟨by simp⟩ : IsPullback g (𝟙 _) e (g ≫ e))
  simpa using this

/-- A scheme over a one-point space has the dimension of its fibre. -/
theorem topologicalKrullDim_le_of_fiber {Y T : Scheme.{u}} (f : Y ⟶ T) (t : T)
    (ht : ∀ y, f y = t) {n : WithBot ℕ∞} (h : topologicalKrullDim (f.fiber t) ≤ n) :
    topologicalKrullDim Y ≤ n := by
  have hu : f ⁻¹' {t} = Set.univ := Set.eq_univ_of_forall fun y => ht y
  let e : f.fiber t ≃ₜ Y := (f.fiberHomeo t).trans
    ((Homeomorph.setCongr hu).trans (Homeomorph.Set.univ Y))
  exact (e.symm.isInducing.topologicalKrullDim_le).trans h

/-- The dimension of a scheme over a field is that of its base change along a field
extension, at most: a cartesian square over `Spec K' ⟶ Spec K` bounds the dimension of the bottom
scheme by that of the top one. -/
theorem topologicalKrullDim_le_of_isPullback_field {K K' : Type u} [Field K] [Field K']
    {V V' : Scheme.{u}} {f : V ⟶ Spec (.of K)} {f' : V' ⟶ Spec (.of K')} {g' : V' ⟶ V}
    {g : Spec (.of K') ⟶ Spec (.of K)} (H : IsPullback g' f' f g) (hf : LocallyOfFiniteType f)
    (hdim : topologicalKrullDim V' ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have := hf
  have h1 :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback' H 1
      (IsLocalRing.closedPoint K') (topologicalKrullDim_fiber_le_of_le f' hdim _)
  exact topologicalKrullDim_le_of_fiber f _ (fun _ => Subsingleton.elim _ _) h1

/-- A morphism `h : X ⟶ Y` over `U` induces a morphism between the base changes along any
`ψ : U' ⟶ U`, compatible with both projections. -/
private theorem exists_pullback_map_of_comp_eq {X Y U U' : Scheme.{u}} {fX : X ⟶ U} {fY : Y ⟶ U}
    (h : X ⟶ Y) (hh : h ≫ fY = fX) (ψ : U' ⟶ U) :
    ∃ h' : pullback fX ψ ⟶ pullback fY ψ, h' ≫ pullback.snd fY ψ = pullback.snd fX ψ ∧
      h' ≫ pullback.fst fY ψ = pullback.fst fX ψ ≫ h :=
  ⟨pullback.lift (pullback.fst fX ψ ≫ h) (pullback.snd fX ψ)
    (by rw [Category.assoc, hh, pullback.condition]), pullback.lift_snd _ _ _,
    pullback.lift_fst _ _ _⟩

/-- A cartesian square over `t ≫ g` gives a cartesian square over `t` after base change of its
bottom map along `g`. -/
private theorem isPullback_lift_snd_of_isPullback {A Y Z T U : Scheme.{u}} {i : A ⟶ Y} {gA : A ⟶ T}
    {f : Y ⟶ Z} {g : U ⟶ Z} {t : T ⟶ U} (H : IsPullback i gA f (t ≫ g)) :
    IsPullback (pullback.lift i (gA ≫ t) (by simpa using H.w)) gA (pullback.snd f g) t :=
  IsPullback.of_right (by rwa [pullback.lift_fst]) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f g)

open GaloisCoverLimits in
/-- **Deforming a contraction étale locally over an affine base** ([Stacks, Tag 0E7C] for an
affine scheme). Let `S` be affine, `s ∈ S`, `X` proper, flat and of finite presentation over `S`,
`e : T ⟶ Spec κ(s)` an isomorphism, `V ⟶ X` a cartesian presentation of the fibre over
`e ≫ (Spec κ(s) ⟶ S)`, of dimension at most one, and `h₀ : V ⟶ Y₀` a morphism over `T` to a proper
scheme of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_V` and `R¹h₀,*𝒪_V = 0`. Then there are an
étale `φ : U ⟶ S` with a lift `t_U : T ⟶ U` of the point, a cartesian presentation `X_U` of the
base change of `X`, a proper flat `Y ⟶ U` of finite presentation, a morphism `h : X_U ⟶ Y` over
`U`, and cartesian presentations `V ⟶ X_U`, `Y₀ ⟶ Y` of the fibres over `t_U` carrying `h₀` to
`h`. -/
theorem exists_etale_contraction_of_isAffine {S : Scheme.{u}} [IsAffine S] (s : S)
    {X : Scheme.{u}} (fX : X ⟶ S) [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX]
    {T V Y₀ : Scheme.{u}} (e₀ : T ⟶ Spec (S.residueField s)) [IsIso e₀] (qV : V ⟶ X)
    (v : V ⟶ T) (hV : IsPullback qV v fX (e₀ ≫ S.fromSpecResidueField s))
    (gY₀ : Y₀ ⟶ T) [IsProper gY₀] (h₀ : V ⟶ Y₀) (hh₀ : h₀ ≫ gY₀ = v)
    (hdimV : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf)))
    (hdimY : topologicalKrullDim Y₀ ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (tU : T ⟶ U), Etale φ ∧ IsAffineHom φ ∧
      tU ≫ φ = e₀ ≫ S.fromSpecResidueField s ∧
      ∃ (XU : Scheme.{u}) (pXU : XU ⟶ X) (fXU : XU ⟶ U), IsPullback pXU fXU fX φ ∧
      ∃ (Y : Scheme.{u}) (fY : Y ⟶ U) (h : XU ⟶ Y), h ≫ fY = fXU ∧ IsProper fY ∧ Flat fY ∧
        LocallyOfFinitePresentation fY ∧ ∃ (qVU : V ⟶ XU) (iY : Y₀ ⟶ Y), qVU ≫ pXU = qV ∧
          qVU ≫ fXU = v ≫ tU ∧ IsPullback iY gY₀ fY tU ∧ h₀ ≫ iY = qVU ≫ h := by
  -- absolute Noetherian approximation of `S`
  let B := specAdjoinFinsetDiagram Γ(S, ⊤)
  let c₀ := specAdjoinFinsetCone Γ(S, ⊤)
  let cS : Cone B :=
    { pt := S
      π := { app := fun i => S.isoSpec.hom ≫ c₀.π.app i
             naturality := fun _ _ a => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
               exact ((Category.assoc _ _ _).trans
                 (congrArg (S.isoSpec.hom ≫ ·) (c₀.w a))).symm } }
  have hS : IsLimit cS := IsLimit.ofIsoLimit (isLimit_specAdjoinFinsetCone Γ(S, ⊤))
    (Cones.ext (S.isoSpec.symm : c₀.pt ≅ S) fun i => (Iso.inv_hom_id_assoc _ _).symm)
  have : ∀ i, CompactSpace (B.obj i) := fun i => inferInstance
  have : ∀ i, QuasiSeparatedSpace (B.obj i) := fun i => quasiSeparatedSpace_of_isAffine _
  obtain ⟨i₀, X₀, fX₀, gX, hX₀p, hX₀f, hX₀l, sqX₀⟩ := exists_properFlat_stageModel B cS hS fX
  have := hX₀p
  -- the residue fields of the images of `s`
  let Rd := ptResidueSpecDiagram B cS s
  let cR : Cone Rd :=
    { pt := Spec (S.residueField s)
      π := { app := fun i => (ptResidueSpecCone B cS s).π.app i
             naturality := fun _ _ a => (ptResidueSpecCone B cS s).π.naturality a } }
  have hRl : IsLimit cR := isLimitPtResidueSpecCone B cS s hS
  have hπR : ∀ k, cR.π.app k ≫ (B.obj k).fromSpecResidueField (cS.π.app k s) =
      S.fromSpecResidueField s ≫ cS.π.app k := fun k => ptResidueSpecCone_π_app_comp B cS s k
  have : ∀ k, Flat (cR.π.app k) := fun k =>
    inferInstanceAs (Flat ((ptResidueSpecCone B cS s).π.app k))
  have : ∀ k, Surjective (cR.π.app k) := fun k =>
    inferInstanceAs (Surjective ((ptResidueSpecCone B cS s).π.app k))
  let g' : Y₀ ⟶ cR.pt := gY₀ ≫ e₀
  have : IsProper g' := inferInstanceAs (IsProper (gY₀ ≫ e₀))
  have : Flat g' := inferInstanceAs (Flat (gY₀ ≫ e₀))
  have : LocallyOfFinitePresentation g' := inferInstanceAs (LocallyOfFinitePresentation (gY₀ ≫ e₀))
  obtain ⟨k₁, W₁, fW₁, gW, hW₁p, hW₁f, hW₁l, sqW⟩ := exists_properFlat_stageModel Rd cR hRl g'
  -- a common stage
  let k := IsCofiltered.min i₀ k₁
  let a₀ : k ⟶ i₀ := IsCofiltered.minToLeft i₀ k₁
  let a₁ : k ⟶ k₁ := IsCofiltered.minToRight i₀ k₁
  let tk : Rd.obj k ⟶ B.obj i₀ := (B.obj k).fromSpecResidueField (cS.π.app k s) ≫ B.map a₀
  have htk : cR.π.app k ≫ tk = S.fromSpecResidueField s ≫ cS.π.app i₀ := by
    simp only [tk]
    rw [← Category.assoc, hπR, Category.assoc, cS.w a₀]
  have hV' := (isPullback_comp_iso_iff qV v fX e₀ (S.fromSpecResidueField s)).1 hV
  -- the fibre of `X` at the stage `k`
  let fVk := pullback.snd fX₀ tk
  have sqVk₀ : IsPullback (pullback.fst fX₀ tk) fVk fX₀ tk := IsPullback.of_hasPullback fX₀ tk
  have : IsProper fVk := MorphismProperty.of_isPullback sqVk₀ inferInstance
  let lV : V ⟶ pullback fX₀ tk := sqVk₀.lift (qV ≫ gX) ((v ≫ e₀) ≫ cR.π.app k) (by
    rw [Category.assoc, sqX₀.w, reassoc_of% hV'.w, Category.assoc, Category.assoc, htk])
  have sqV : IsPullback lV (v ≫ e₀) fVk (cR.π.app k) := by
    refine IsPullback.of_right ?_ (sqVk₀.lift_snd _ _ _) sqVk₀
    rw [sqVk₀.lift_fst, htk]
    exact hV'.paste_horiz sqX₀
  -- the model of `Y₀` at the stage `k`, and the model of `h₀`
  have sqWk := isPullback_stageLift (E := Rd) (c := cR) sqW a₁
  let fWk := pullback.fst (Rd.map a₁) fW₁
  have : IsProper fWk := prop_fst_stage @IsProper a₁ hW₁p
  have : LocallyOfFinitePresentation fWk := prop_fst_stage @LocallyOfFinitePresentation a₁ hW₁l
  have hh₀' : h₀ ≫ g' = v ≫ e₀ := by rw [← reassoc_of% hh₀]
  obtain ⟨j, b, h₂, hh₂, hh₂c⟩ := exists_stageModel_hom Rd cR hRl sqV sqWk h₀ hh₀'
  let fVj := pullback.fst (Rd.map b) fVk
  let fWj := pullback.fst (Rd.map b) fWk
  have sqVj := isPullback_stageLift (E := Rd) (c := cR) sqV b
  have sqWj := isPullback_stageLift (E := Rd) (c := cR) sqWk b
  have : IsProper fVj := prop_fst_stage @IsProper b inferInstance
  have : IsProper fWj := prop_fst_stage @IsProper b inferInstance
  have : IsProper (pullback.fst (Rd.map b) fVk) := inferInstanceAs (IsProper fVj)
  have : IsProper (pullback.fst (Rd.map b) (pullback.fst (Rd.map a₁) fW₁)) :=
    inferInstanceAs (IsProper fWj)
  -- the conditions descend
  have : IsProper h₂ := by
    have : IsProper (h₂ ≫ fWj) := by rw [hh₂]; infer_instance
    exact IsProper.of_comp h₂ fWj
  have H : IsPullback (stageLift (E := Rd) (c := cR) sqV b) h₀ h₂
      (stageLift (E := Rd) (c := cR) sqWk b) := by
    refine IsPullback.of_bot ?_ hh₂c sqWj
    rw [hh₀', hh₂]
    exact sqVj
  have : Flat (stageLift (E := Rd) (c := cR) sqWk b) :=
    MorphismProperty.of_isPullback sqWj.flip inferInstance
  have : Surjective (stageLift (E := Rd) (c := cR) sqWk b) :=
    MorphismProperty.of_isPullback sqWj.flip inferInstance
  have hdim₂ : ∀ y, topologicalKrullDim (h₂.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    obtain ⟨y', rfl⟩ := (stageLift (E := Rd) (c := cR) sqWk b).surjective y
    exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback'
      H 1 y' (topologicalKrullDim_fiber_le_of_le h₀ hdimV y')
  obtain ⟨h0₂, hR₂⟩ := fibreConditions_of_isPullback_of_surjective H hdim₂ h0 hR
  let Vj : Scheme.{u} := pullback (Rd.map b) fVk
  let Wj : Scheme.{u} := pullback (Rd.map b) fWk
  have hdimVj : topologicalKrullDim Vj ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_isPullback_field sqVj (inferInstance : LocallyOfFiniteType fVj) hdimV
  have hdimWj : topologicalKrullDim Wj ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_isPullback_field sqWj (inferInstance : LocallyOfFiniteType fWj) hdimY
  -- the stage `j` is the spectrum of a G-ring
  let c : j ⟶ i₀ := b ≫ a₀
  let A : Type u := Algebra.adjoin ℤ ((j.unop : Finset Γ(S, ⊤)) : Set Γ(S, ⊤))
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have hGA : IsGRing A :=
    isGRing_basic_examples.{0, u}.2.2.2.2 ℤ A isGRing_basic_examples.{0, 0}.2.2.1
  let x : PrimeSpectrum A := cS.π.app j s
  let ιA : B.obj j ≅ Spec (CommRingCat.of A) := Iso.refl _
  let ιR : Rd.obj j ≅ Spec ((Spec (CommRingCat.of A)).residueField x) := Iso.refl _
  let e₀' : Rd.obj j ⟶ Spec (.of x.asIdeal.ResidueField) :=
    ιR.hom ≫ Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) x).inv
  have hιpt : ιR.hom ≫ (Spec (CommRingCat.of A)).fromSpecResidueField x =
      (B.obj j).fromSpecResidueField (cS.π.app j s) ≫ ιA.hom :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hpt : e₀' ≫ Spec.map (CommRingCat.ofHom (algebraMap A x.asIdeal.ResidueField)) =
      (B.obj j).fromSpecResidueField (cS.π.app j s) ≫ ιA.hom := by
    simp only [e₀', Category.assoc]
    exact (congrArg (ιR.hom ≫ ·)
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _)).trans hιpt
  -- the fibre of the model of `X` at the stage `j`
  let fXj := pullback.fst (B.map c) fX₀
  let fXj' : pullback (B.map c) fX₀ ⟶ Spec (CommRingCat.of A) := fXj ≫ ιA.hom
  have : IsProper fXj := prop_fst_stage @IsProper c hX₀p
  have : Flat fXj := prop_fst_stage @Flat c hX₀f
  have : IsProper fXj' := inferInstanceAs (IsProper (fXj ≫ ιA.hom))
  have : Flat fXj' := inferInstanceAs (Flat (fXj ≫ ιA.hom))
  have sqXj := isPullback_comp_iso_right (isPullback_stageLift (E := B) (c := cS) sqX₀ c) ιA.hom
  have hjk : (B.obj j).fromSpecResidueField (cS.π.app j s) ≫ B.map c = Rd.map b ≫ tk := by
    simp only [c, tk, B.map_comp, ← Category.assoc]
    congr 1
    exact (specMap_ptResidueTransition_fromSpecResidueField B cS s b).symm
  let qVj : Vj ⟶ pullback (B.map c) fX₀ := pullback.lift
    (fVj ≫ (B.obj j).fromSpecResidueField (cS.π.app j s))
    (pullback.snd (Rd.map b) fVk ≫ pullback.fst fX₀ tk) (by
      rw [Category.assoc, hjk, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, sqVk₀.w])
  have hVj0 : IsPullback qVj fVj fXj ((B.obj j).fromSpecResidueField (cS.π.app j s)) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (B.map c) fX₀).flip
    rw [pullback.lift_snd, hjk]
    exact (IsPullback.of_hasPullback (Rd.map b) fVk).flip.paste_horiz sqVk₀
  have hVj : IsPullback qVj fVj fXj' (e₀' ≫ Spec.map (CommRingCat.ofHom
      (algebraMap A x.asIdeal.ResidueField))) := by
    rw [hpt]
    exact isPullback_comp_iso_right hVj0 ιA.hom
  -- the elementary étale neighbourhood at the stage `j`
  obtain ⟨Bet, _, _, _, aug, XB, pXB, fXB, sqXB, Y, fY, h, hh, hYp, hYf, qVB, iY, hqVB₁, hqVB₂,
      hiY, hhh⟩ := exists_etale_contraction_of_isGRing (R := A) hGA x.asIdeal fXj' e₀' qVj fVj hVj
    fWj h₂ hh₂ hdimVj h0₂ hR₂ hdimWj
  have := hYp
  have := hYf
  -- pulling back to `S`
  let πj : S ⟶ Spec (CommRingCat.of A) := cS.π.app j ≫ ιA.hom
  let ψ0 : Spec (CommRingCat.of Bet) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A Bet))
  have : Etale ψ0 := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let ψ := pullback.fst ψ0 πj
  let φ := pullback.snd ψ0 πj
  let ptB : T ⟶ Spec (CommRingCat.of Bet) :=
    e₀ ≫ cR.π.app j ≫ e₀' ≫ Spec.map (CommRingCat.ofHom aug.toRingHom)
  have haug : Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ ψ0 =
      Spec.map (CommRingCat.ofHom (algebraMap A x.asIdeal.ResidueField)) :=
    (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun y => aug.commutes y)))
  have hptB : ptB ≫ ψ0 = (e₀ ≫ S.fromSpecResidueField s) ≫ πj := by
    simp only [ptB, πj, Category.assoc]
    rw [haug, hpt, reassoc_of% (hπR j)]
  let tU : T ⟶ pullback ψ0 πj := pullback.lift ptB (e₀ ≫ S.fromSpecResidueField s) hptB
  have htUψ : tU ≫ ψ = ptB := pullback.lift_fst _ _ _
  have htUφ : tU ≫ φ = e₀ ≫ S.fromSpecResidueField s := pullback.lift_snd _ _ _
  -- the base change of `X`
  let fXU := pullback.snd fXB ψ
  let gXj := stageLift (E := B) (c := cS) sqX₀ c
  have hUc : ψ ≫ ψ0 = φ ≫ πj := pullback.condition
  let pXU : pullback fXB ψ ⟶ X := sqXj.lift (pullback.fst fXB ψ ≫ pXB) (fXU ≫ φ) (by
    calc (pullback.fst fXB ψ ≫ pXB) ≫ fXj' = pullback.fst fXB ψ ≫ fXB ≫ ψ0 := by
          rw [Category.assoc, sqXB.w]
      _ = fXU ≫ ψ ≫ ψ0 := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = (fXU ≫ φ) ≫ πj := by rw [hUc, Category.assoc])
  have hpXU₁ : pXU ≫ gXj = pullback.fst fXB ψ ≫ pXB := sqXj.lift_fst _ _ _
  have hpXU₂ : pXU ≫ fX = fXU ≫ φ := sqXj.lift_snd _ _ _
  have hXU : IsPullback pXU fXU fX φ := by
    refine IsPullback.of_right ?_ hpXU₂ sqXj
    rw [hpXU₁, ← hUc]
    exact (IsPullback.of_hasPullback fXB ψ).paste_horiz sqXB
  -- the base change of `Y` and of `h`
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : IsNoetherianRing Bet := Algebra.FiniteType.isNoetherianRing A Bet
  have : LocallyOfFinitePresentation fY := inferInstance
  have sqYU : IsPullback (pullback.fst fY ψ) (pullback.snd fY ψ) fY ψ :=
    IsPullback.of_hasPullback fY ψ
  obtain ⟨hU, hhU, hhU₁⟩ := exists_pullback_map_of_comp_eq h hh ψ
  -- the fibres
  let lVj := stageLift (E := Rd) (c := cR) sqV b
  let lWj := stageLift (E := Rd) (c := cR) sqWk b
  have e3 : lVj ≫ qVj = qV ≫ gXj := by
    refine (IsPullback.of_hasPullback (B.map c) fX₀).hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, stageLift_fst, ← Category.assoc,
        stageLift_fst, Category.assoc, hπR j, ← Category.assoc, ← Category.assoc, hV.w]
      simp only [Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, stageLift_snd, ← Category.assoc,
        stageLift_snd, sqVk₀.lift_fst]
  let qVU : V ⟶ pullback fXB ψ := pullback.lift (lVj ≫ qVB) (v ≫ tU) (by
    rw [Category.assoc, hqVB₂, ← Category.assoc lVj, stageLift_fst, Category.assoc v tU ψ, htUψ]
    simp only [ptB, Category.assoc])
  have hqVU₁ : qVU ≫ pXU = qV := by
    refine sqXj.hom_ext ?_ ?_
    · rw [Category.assoc, hpXU₁, pullback.lift_fst_assoc, Category.assoc, hqVB₁, e3]
    · rw [Category.assoc, hpXU₂, pullback.lift_snd_assoc, Category.assoc, htUφ, hV.w]
  let iYU : Y₀ ⟶ pullback fY ψ := pullback.lift (lWj ≫ iY) (gY₀ ≫ tU) (by
    rw [Category.assoc, hiY.w, ← Category.assoc lWj, stageLift_fst, Category.assoc gY₀ tU ψ, htUψ]
    simp only [g', ptB, Category.assoc])
  refine ⟨pullback ψ0 πj, φ, tU, inferInstance, inferInstance, htUφ, pullback fXB ψ, pXU, fXU, hXU,
    pullback fY ψ, pullback.snd fY ψ, hU, hhU, MorphismProperty.of_isPullback sqYU inferInstance,
    MorphismProperty.of_isPullback sqYU inferInstance,
    MorphismProperty.of_isPullback sqYU inferInstance, qVU, iYU, hqVU₁, pullback.lift_snd _ _ _,
    ?_, ?_⟩
  · refine isPullback_lift_snd_of_isPullback ?_
    rw [htUψ]
    exact (isPullback_comp_iso_iff _ _ _ e₀ _).2 (sqWj.paste_horiz hiY)
  · refine sqYU.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hhU₁, pullback.lift_fst_assoc,
        Category.assoc, ← hhh, ← reassoc_of% hh₂c]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hhU, pullback.lift_snd,
        reassoc_of% hh₀]

/-- **Deforming a contraction étale locally over an affine base, with fibres of dimension at most
one.** The statement of `exists_etale_contraction_of_isAffine`, with the point given as any
`t = e ≫ (Spec κ(s) ⟶ S)`, the étale morphism `U ⟶ S` quasi-compact, and the neighbourhood
shrunk so that every fibre of `Y ⟶ U` has dimension at most one (the dimension of the fibres of a
proper morphism is upper semicontinuous, [Stacks, Tag 0D4I]). -/
theorem exists_etale_contraction_of_isAffine_of_fiberDimension {S : Scheme.{u}} [IsAffine S]
    (s : S) {X : Scheme.{u}} (fX : X ⟶ S) [IsProper fX] [Flat fX]
    [LocallyOfFinitePresentation fX] {T V Y₀ : Scheme.{u}} (t : T ⟶ S)
    (e₀ : T ⟶ Spec (S.residueField s)) [IsIso e₀] (het : e₀ ≫ S.fromSpecResidueField s = t)
    (qV : V ⟶ X) (v : V ⟶ T) (hV : IsPullback qV v fX t)
    (gY₀ : Y₀ ⟶ T) [IsProper gY₀] (h₀ : V ⟶ Y₀) (hh₀ : h₀ ≫ gY₀ = v)
    (hdimV : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf)))
    (hdimY : topologicalKrullDim Y₀ ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (tU : T ⟶ U), Etale φ ∧ QuasiCompact φ ∧ tU ≫ φ = t ∧
      ∃ (XU : Scheme.{u}) (pXU : XU ⟶ X) (fXU : XU ⟶ U), IsPullback pXU fXU fX φ ∧
      ∃ (Y : Scheme.{u}) (fY : Y ⟶ U) (h : XU ⟶ Y), h ≫ fY = fXU ∧ IsProper fY ∧ Flat fY ∧
        LocallyOfFinitePresentation fY ∧ (∀ y, fY.fiberDimension y ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
        ∃ (qVU : V ⟶ XU) (iY : Y₀ ⟶ Y), qVU ≫ pXU = qV ∧
          qVU ≫ fXU = v ≫ tU ∧ IsPullback iY gY₀ fY tU ∧ h₀ ≫ iY = qVU ≫ h := by
  subst het
  obtain ⟨U, φ, tU, hφe, hφq, htU, XU, pXU, fXU, hXU, Y, fY, h, hh, hYp, hYf, hYl, qVU, iY, hq₁,
    hq₂, hiY, hhh⟩ := exists_etale_contraction_of_isAffine s fX e₀ qV v hV gY₀ h₀ hh₀ hdimV h0 hR
      hdimY
  have := hφe
  have := hφq
  have := hYp
  have := hYf
  have := hYl
  -- the locus of fibres of dimension at most one
  let bad : Set Y := {x | ¬ topologicalKrullDimAt (fY.fiber (fY x)) (fY.asFiber x) ≤
    ((1 : ℕ) : WithBot ℕ∞)}
  have hbad : IsClosed bad := (isOpen_setOf_fiberDimensionAt_le fY 1).isClosed_compl
  let O : U.Opens := ⟨(fY.base '' bad)ᶜ, (fY.isClosedMap _ hbad).isOpen_compl⟩
  have hO : ∀ y ∈ O, fY.fiberDimension y ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y hy =>
    (Scheme.Hom.fiberDimension_le_iff fY y _).2 fun x hx => by
      by_contra hc
      exact hy ⟨x, hc, hx⟩
  have htO : ∀ x : T, tU x ∈ O := by
    intro x ⟨y, hy, hyx⟩
    have h1 : fY.fiberDimension (tU x) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
      have := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hiY) x
      rw [Function.comp_apply] at this
      rw [← this]
      exact topologicalKrullDim_fiber_le_of_le gY₀ hdimY x
    exact hy ((Scheme.Hom.topologicalKrullDimAt_fiber_le_fiberDimension fY hyx).trans h1)
  -- an affine neighbourhood of the image of `T` inside `O`
  obtain ⟨x₀⟩ : Nonempty T := by
    obtain ⟨y⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
    exact ⟨inv e₀ y⟩
  obtain ⟨O', hO', hxO', hO'O⟩ := exists_isAffineOpen_mem_and_subset (x := tU x₀) (U := O) (htO x₀)
  have : IsAffine O'.toScheme := hO'
  have hT : ∀ x : T, x = x₀ := fun x =>
    (Scheme.homeoOfIso (asIso e₀)).injective (Subsingleton.elim _ _)
  have hrange : Set.range tU ⊆ Set.range O'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hT x]
    exact hxO'
  let tU' := IsOpenImmersion.lift O'.ι tU hrange
  have htU' : tU' ≫ O'.ι = tU := IsOpenImmersion.lift_fac _ _ _
  have : QuasiCompact O'.ι := by
    have : IsAffine U := isAffine_of_isAffineHom φ
    infer_instance
  -- the restricted data
  have sqX : IsPullback (pullback.fst fXU O'.ι) (pullback.snd fXU O'.ι) fXU O'.ι :=
    IsPullback.of_hasPullback fXU O'.ι
  have sqY : IsPullback (pullback.fst fY O'.ι) (pullback.snd fY O'.ι) fY O'.ι :=
    IsPullback.of_hasPullback fY O'.ι
  obtain ⟨h', hh', hh'₁⟩ := exists_pullback_map_of_comp_eq h hh O'.ι
  let qVU' : V ⟶ pullback fXU O'.ι := pullback.lift qVU (v ≫ tU') (by
    rw [hq₂, Category.assoc, htU'])
  let iY' : Y₀ ⟶ pullback fY O'.ι := pullback.lift iY (gY₀ ≫ tU') (by
    rw [hiY.w, Category.assoc, htU'])
  refine ⟨O'.toScheme, O'.ι ≫ φ, tU', inferInstance, inferInstance, by rw [reassoc_of% htU', htU],
    pullback fXU O'.ι, pullback.fst fXU O'.ι ≫ pXU, pullback.snd fXU O'.ι, sqX.paste_horiz hXU,
    pullback fY O'.ι, pullback.snd fY O'.ι, h', hh', MorphismProperty.of_isPullback sqY hYp,
    MorphismProperty.of_isPullback sqY hYf, MorphismProperty.of_isPullback sqY hYl, ?_, qVU', iY',
    by rw [pullback.lift_fst_assoc, hq₁], pullback.lift_snd _ _ _, ?_, ?_⟩
  · intro y
    have := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback sqY) y
    rw [Function.comp_apply] at this
    rw [this]
    refine hO _ (hO'O ?_)
    have hy := Set.mem_range_self (f := O'.ι.base) y
    rwa [Scheme.Opens.range_ι] at hy
  · exact isPullback_lift_snd_of_isPullback (by rwa [htU'])
  · refine sqY.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hh'₁, pullback.lift_fst_assoc, hhh]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hh', pullback.lift_snd,
        reassoc_of% hh₀]

end ContractionDeformation

end AlgebraicGeometry.C1590Private

end
