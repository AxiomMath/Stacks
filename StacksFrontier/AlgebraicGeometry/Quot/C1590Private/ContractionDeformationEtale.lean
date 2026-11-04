module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionDeformationHenselian
public import StacksFrontier.RingTheory.Henselian.Henselization.EtaleNeighborhood
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.Cotangent.Henselization

/-!
# Deforming a contraction over an elementary étale neighbourhood (a step of Stacks 0E7C)

Let `R` be a G-ring, `p` a prime of `R` with residue field `κ(p)`, let `X` be a proper flat scheme
over `Spec R` and let `h₀ : X_p ⟶ Y₀` be a morphism from the fibre over `p` to a proper scheme of
dimension at most one over `κ(p)` with `𝒪_{Y₀} ≅ h₀,*𝒪_{X_p}` and `R¹h₀,*𝒪_{X_p} = 0`. Then there
are an étale `R`-algebra `B` with an `R`-algebra map `B ⟶ κ(p)` (an elementary étale
neighbourhood of `p`), a proper flat `Y ⟶ Spec B` and a morphism `h : X_B ⟶ Y` over `Spec B`
whose fibre over the point `Spec κ(p) ⟶ Spec B` is `h₀`.

This is the step "we may assume `S` is the spectrum of the henselization of a local ring of a
scheme of finite type over `ℤ`" of the proof of [Stacks, Tag 0E7C], proved as the source proves it.
The henselization `R_p^h` is a henselian local G-ring ([Stacks, Tag 07QR]), so the henselian case
(`AlgebraicGeometry.C1590Private.ContractionDeformation.exists_contraction_of_henselian_isGRing`)
gives `(Y^h, h^h)` over it. The henselization is the filtered colimit of the étale neighbourhoods
of `p` ([Stacks, Tag 04GV]), so `Spec R_p^h` is the limit of their spectra, and `(Y^h, h^h)`
descends to one of them ([Stacks, Tags 01ZM, 04AI, 01ZC]).

## Main results

* `AlgebraicGeometry.C1590Private.ContractionDeformation.exists_etale_contraction_of_isGRing`: the
  statement above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 04GV](https://stacks.math.columbia.edu/tag/04GV)
* [Stacks Project, Tag 07QR](https://stacks.math.columbia.edu/tag/07QR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

attribute [local instance] Stacks.Henselization.EtaleColimit.etale_essentiallySmall

namespace AlgebraicGeometry.C1590Private

namespace ContractionDeformation

/-- **Deforming a contraction over an elementary étale neighbourhood** (a step of
[Stacks, Tag 0E7C]). Let `R` be a G-ring and `p` a prime of `R`, with `t : Spec κ(p) ⟶ Spec R`.
Let `X` be proper and flat over `Spec R`, `e : T ⟶ Spec κ(p)` an isomorphism, `V ⟶ X` a cartesian
presentation of the fibre over `e ≫ t`, of dimension at most one, and `h₀ : V ⟶ Y₀` a morphism over
`T` to a proper scheme of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_V` and `R¹h₀,*𝒪_V = 0`. Then
there are an étale `R`-algebra `B` with an `R`-algebra map `a : B ⟶ κ(p)`, a cartesian
presentation `X_B` of the base change of `X` to `Spec B`, a proper flat `Y ⟶ Spec B` and a morphism
`h : X_B ⟶ Y` over `Spec B`, and cartesian presentations `V ⟶ X_B`, `Y₀ ⟶ Y` of the fibres over
`e ≫ Spec a` carrying `h₀` to `h`. -/
theorem exists_etale_contraction_of_isGRing {R : Type u} [CommRing R] (hG : IsGRing R)
    (p : Ideal R) [p.IsPrime] {X : Scheme.{u}} (fX : X ⟶ Spec (.of R)) [IsProper fX] [Flat fX]
    {T V Y₀ : Scheme.{u}} (e₀ : T ⟶ Spec (.of p.ResidueField)) [IsIso e₀] (qV : V ⟶ X)
    (v : V ⟶ T)
    (hV : IsPullback qV v fX (e₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))))
    (gY₀ : Y₀ ⟶ T) [IsProper gY₀] (h₀ : V ⟶ Y₀) (hh₀ : h₀ ≫ gY₀ = v)
    (hdimV : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf)))
    (hdimY : topologicalKrullDim Y₀ ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Etale R B)
      (a : B →ₐ[R] p.ResidueField) (XB : Scheme.{u}) (pXB : XB ⟶ X) (fXB : XB ⟶ Spec (.of B)),
      IsPullback pXB fXB fX (Spec.map (CommRingCat.ofHom (algebraMap R B))) ∧
      ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of B)) (h : XB ⟶ Y), h ≫ fY = fXB ∧ IsProper fY ∧
        Flat fY ∧ ∃ (qVB : V ⟶ XB) (iY : Y₀ ⟶ Y), qVB ≫ pXB = qV ∧
          qVB ≫ fXB = v ≫ e₀ ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ∧
          IsPullback iY gY₀ fY (e₀ ≫ Spec.map (CommRingCat.ofHom a.toRingHom)) ∧
            h₀ ≫ iY = qVB ≫ h := by
  -- the henselization of the local ring at `p`, a henselian local G-ring
  have hGp : IsGRing (Localization.AtPrime p) := isGRing_of_essFiniteType hG
  obtain ⟨Rh, _, _, _, hh⟩ := exists_isHenselization_residueField (Localization.AtPrime p)
  obtain ⟨Rsh, _, _, _, hsh⟩ :=
    exists_isHenselization_separableClosure (Localization.AtPrime p)
  have hGh : IsGRing Rh := (isGRing_henselization_and_strictHenselization
    (Localization.AtPrime p) Rh Rsh (SeparableClosure (ResidueField (Localization.AtPrime p)))
    hGp).1
  have : HenselianLocalRing Rh := hh.henselian
  have : IsLocalHom (algebraMap (Localization.AtPrime p) Rh) :=
    IsLocalRing.IsHenselization.isLocalHom (R := Localization.AtPrime p)
      (L := ResidueField (Localization.AtPrime p)) (Rh := Rh)
  let : Algebra R Rh := ((algebraMap (Localization.AtPrime p) Rh).comp
    (algebraMap R (Localization.AtPrime p))).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) Rh := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the residue fields
  let t := Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))
  let π : Spec (.of Rh) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Rh))
  let cp := ContractionUniquenessComplete.closedPoint Rh
  let τ : Spec (.of (ResidueField Rh)) ⟶ Spec (.of p.ResidueField) :=
    Spec.map (CommRingCat.ofHom (ResidueField.map (algebraMap (Localization.AtPrime p) Rh)))
  have : IsIso τ := by
    have : IsIso (CommRingCat.ofHom (ResidueField.map
        (algebraMap (Localization.AtPrime p) Rh))) :=
      inferInstanceAs (IsIso (RingEquiv.ofBijective _
        (IsLocalRing.IsHenselization.residueField_map_bijective
          (R := Localization.AtPrime p) (Rh := Rh))).toCommRingCatIso.hom)
    infer_instance
  have hτ : cp ≫ π = τ ≫ t := by
    simp only [cp, ContractionUniquenessComplete.closedPoint, π, τ, t, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
  let e := e₀ ≫ inv τ
  have he : (e ≫ cp) ≫ π = e₀ ≫ t := by
    simp only [e, Category.assoc, hτ, IsIso.inv_hom_id_assoc]
  -- the base change to the henselization, and the henselian case
  let fXh := pullback.snd fX π
  have sqXh := IsPullback.of_hasPullback fX π
  have : IsProper fXh := MorphismProperty.of_isPullback sqXh inferInstance
  let qVh : V ⟶ pullback fX π := sqXh.lift qV (v ≫ e ≫ cp)
    (by rw [hV.w, Category.assoc, Category.assoc, ← Category.assoc e, he])
  have hqVh₁ : qVh ≫ pullback.fst fX π = qV := sqXh.lift_fst _ _ _
  have hqVh₂ : qVh ≫ fXh = v ≫ e ≫ cp :=
    sqXh.lift_snd _ _ _
  have hVh : IsPullback qVh v fXh (e ≫ cp) := by
    refine IsPullback.of_right ?_ hqVh₂ sqXh
    rw [hqVh₁, he]
    exact hV
  obtain ⟨Yh, fYh, hhh, hhh', hprh, hflh, iYh, hiYh, hiYhh⟩ :=
    exists_contraction_of_henselian_isGRing hGh fXh e qVh v hVh gY₀ h₀ hh₀ hdimV h0 hR hdimY
  have : IsNoetherianRing Rh := hGh.1
  have : LocallyOfFinitePresentation fYh := inferInstance
  -- the henselization as a limit of étale neighbourhoods
  obtain ⟨hfilt, ι, hres, -, ⟨hcol⟩, -⟩ :=
    IsLocalRing.IsHenselization.isFiltered_etaleNeighborhood_and_isColimit p Rh
  -- a small model of the index category
  let N := Ideal.EtaleNeighborhood p
  let eq := equivSmallModel.{u} N
  let J := SmallModel.{u} N
  have : IsFiltered J := IsFiltered.of_equivalence eq
  let F : J ⥤ CommAlgCat.{u} R := eq.inverse ⋙ Ideal.EtaleNeighborhood.forget p
  have hcolJ : IsColimit ((Cocone.mk _ ι).whisker eq.inverse) :=
    IsColimit.whiskerEquivalence hcol eq.symm
  have : PreservesColimit F (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
    (CommAlgCat.preservesColimitsOfShape_forget₂CommRingCat R J).preservesColimit
  have hcolR := isColimitOfPreserves (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) hcolJ
  let D : Jᵒᵖ ⥤ Scheme.{u} := (F ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).op ⋙ Scheme.Spec
  let c₀ : Cone D := Scheme.Spec.mapCone
    ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone ((Cocone.mk _ ι).whisker eq.inverse)).op
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec hcolR.op
  let c : Cone D :=
    { pt := Spec (.of Rh)
      π := { app := fun i => c₀.π.app i, naturality := fun _ _ a => c₀.π.naturality a } }
  have hc : IsLimit c := hc₀
  have : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a => by
    dsimp [D]
    infer_instance
  have : ∀ i : Jᵒᵖ, IsAffine (D.obj i) := fun _ => inferInstanceAs (IsAffine (Spec _))
  have : ∀ i : Jᵒᵖ, CompactSpace (D.obj i) := fun _ => inferInstance
  have : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun _ => quasiSeparatedSpace_of_isAffine _
  -- the stages lie over `Spec R`
  let ρ : ∀ i : Jᵒᵖ, D.obj i ⟶ Spec (.of R) := fun i =>
    Spec.map (CommRingCat.ofHom (algebraMap R (F.obj i.unop)))
  have hρπ : ∀ i, c.π.app i ≫ ρ i = π := fun i =>
    (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun r => (ι.app (eq.inverse.obj i.unop)).hom.commutes r)))
  have hρ : ∀ {i j : Jᵒᵖ} (a : j ⟶ i), D.map a ≫ ρ i = ρ j := fun a =>
    (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun r => (F.map a.unop).hom.commutes r)))
  -- the points
  have hpt : ∀ j : Jᵒᵖ, cp ≫ c.π.app j =
      τ ≫ Spec.map (CommRingCat.ofHom (eq.inverse.obj j.unop).hom.hom.toRingHom) := fun j =>
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun x => hres (eq.inverse.obj j.unop) x))).trans (Spec.map_comp _ _))
  -- descending `Yʰ`
  obtain ⟨i, Y₁, fY₁, gY, hY₁p, hY₁f, hY₁l, sqY⟩ := exists_properFlat_stageModel D c hc fYh
  let fX₁ := pullback.snd fX (ρ i)
  have sqX₁ := IsPullback.of_hasPullback fX (ρ i)
  have : IsProper fX₁ := MorphismProperty.of_isPullback sqX₁ inferInstance
  let gX : pullback fX π ⟶ pullback fX (ρ i) := sqX₁.lift (pullback.fst fX π)
    (fXh ≫ c.π.app i) (by rw [pullback.condition, Category.assoc, hρπ])
  have sqX : IsPullback gX fXh fX₁ (c.π.app i) := by
    refine IsPullback.of_right ?_ (sqX₁.lift_snd _ _ _) sqX₁
    rw [sqX₁.lift_fst, hρπ]
    exact sqXh
  obtain ⟨j, a, h₂, hh₂, hh₂c⟩ := exists_stageModel_hom D c hc sqX sqY hhh hhh'
  let fX₂ := pullback.fst (D.map a) fX₁
  have sqY₂ := isPullback_stageLift (E := D) (c := c) sqY a
  let pX₂ : pullback (D.map a) fX₁ ⟶ X := pullback.snd (D.map a) fX₁ ≫ pullback.fst fX (ρ i)
  have hX₂ : IsPullback pX₂ fX₂ fX (ρ j) := by
    have := (IsPullback.of_hasPullback (D.map a) fX₁).flip.paste_horiz sqX₁
    rwa [hρ a] at this
  let A := eq.inverse.obj j.unop
  have e1 : stageLift (E := D) (c := c) sqX a ≫ pX₂ = pullback.fst fX π := by
    simp only [pX₂]
    rw [stageLift_snd_assoc]
    exact sqX₁.lift_fst _ _ _
  have e2 : stageLift (E := D) (c := c) sqX a ≫ fX₂ = fXh ≫ c.π.app j := stageLift_fst sqX a
  have hbot : (e ≫ cp) ≫ c.π.app j =
      e₀ ≫ Spec.map (CommRingCat.ofHom A.hom.hom.toRingHom) := by
    simp only [e, Category.assoc, hpt, IsIso.inv_hom_id_assoc]
  refine ⟨A.left.obj, inferInstance, inferInstance, A.left.property, A.hom.hom,
    pullback (D.map a) fX₁, pX₂, fX₂, hX₂, pullback (D.map a) fY₁, pullback.fst (D.map a) fY₁, h₂,
    hh₂, prop_fst_stage @IsProper a hY₁p, prop_fst_stage @Flat a hY₁f,
    qVh ≫ stageLift (E := D) (c := c) sqX a, iYh ≫ stageLift (E := D) (c := c) sqY a,
    ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, e1, hqVh₁]
  · rw [Category.assoc, e2, reassoc_of% hqVh₂, ← hbot]
    simp only [Category.assoc]
  · rw [← hbot]
    exact hiYh.paste_horiz sqY₂
  · rw [reassoc_of% hiYhh, ← hh₂c, Category.assoc]

end ContractionDeformation

end AlgebraicGeometry.C1590Private

end
