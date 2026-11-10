module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.Limits.ClopenLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# The limiting closed subscheme of the finite vanishing stratifications

For a commutative ring `A`, the spectrum `X_w = Spec A_w` of the colimit of the finite
stratification rings is the inverse limit of the finite-stage spectra `X_E`, and the inverse
limit `Z` of the closed strata `Z_E` is a closed subscheme of it.

## Main definitions

* `AlgebraicGeometry.ProEtale.stratificationLimitScheme`: the spectrum of the colimit ring.
* `AlgebraicGeometry.ProEtale.StratificationLimit`: the bundle recording the two inverse
  systems, their limiting cones, and the closed immersion between their limits.

## Main results

* `AlgebraicGeometry.ProEtale.stratificationLimit`: the canonical limiting closed subscheme.
* `AlgebraicGeometry.ProEtale.stratificationLimitClosedScheme`,
  `AlgebraicGeometry.ProEtale.stratificationLimitInclusion`: the scheme `Z` and the closed
  immersion `Z ⟶ X_w` that the canonical bundle provides, named so that the results about them
  can be stated without quantifying over a bundle.

## Implementation notes

Both displayed equalities of schemes are expressed as limiting cones rather than as abstract
isomorphisms of limits. The stage isomorphisms pin down which diagram is meant, by identifying
each object of the diagram with the specified finite-stage scheme and each transition map with
the specified one; the two cones then exhibit `X_w` and `Z` as the respective limits, and the
compatibility of the inclusion with the finite-stage inclusions makes the inclusion canonical.

The limits are computed on rings: the spectrum functor turns the direct limit of the finite
stratification rings into the limit of their spectra, and likewise for the global sections of
the closed strata. Each closed stratum is affine because it is a finite coproduct of affine
schemes, which is what makes the second system a system of spectra as well.

## References

* [Stacks Project, Tag 0974](https://stacks.math.columbia.edu/tag/0974)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-- The diagram of finite stratification rings `A_E`, indexed by the finite subsets of `A`
ordered by inclusion. -/
def stratificationRingDiagram : Finset A ⥤ CommRingCat where
  obj E := CommRingCat.of (stratificationRing E)
  map f := CommRingCat.ofHom (stratificationRingMap _ _ (leOfHom f))
  map_id E := by
    apply CommRingCat.hom_ext
    simpa using stratificationRingMap_id E
  map_comp f g := by
    apply CommRingCat.hom_ext
    simpa using (stratificationRingMap_comp _ _ _ (leOfHom f) (leOfHom g)).symm

/-- The inverse system of finite stratification schemes `X_E = Spec A_E`. -/
def stratificationSchemeDiagram : (Finset A)ᵒᵖ ⥤ Scheme :=
  (stratificationRingDiagram (A := A)).op ⋙ Scheme.Spec

/-- A closed stratum is affine: it is a coproduct of affine schemes over a finite index. -/
theorem closedStrata_isAffine (E : Finset A) : IsAffine (closedStrata E) := by
  classical
  have := finite_subtype_subset_finset E
  dsimp [closedStrata]
  infer_instance

/-- The inverse system of finite closed strata `Z_E`, with the transition maps restricted from
the transition maps of the ambient affine schemes. -/
def closedStrataDiagram : (Finset A)ᵒᵖ ⥤ Scheme where
  obj i := closedStrata i.unop
  map f := (closedStrataTransition _ _ (leOfHom f.unop)).val
  map_id i := by
    have := closedStrataMap_isClosedImmersion i.unop
    refine (cancel_mono (closedStrataMap i.unop)).1 ?_
    simpa [stratificationSchemeMap, stratificationRingMap_id] using
      (closedStrataTransition i.unop i.unop (Finset.Subset.refl _)).property
  map_comp := by
    intro i j k f g
    let E₁ := k.unop
    let E₂ := j.unop
    let E₃ := i.unop
    let h₁₂ : E₁ ⊆ E₂ := leOfHom g.unop
    let h₂₃ : E₂ ⊆ E₃ := leOfHom f.unop
    let h₁₃ : E₁ ⊆ E₃ := h₁₂.trans h₂₃
    let t₁₂ := closedStrataTransition E₁ E₂ h₁₂
    let t₂₃ := closedStrataTransition E₂ E₃ h₂₃
    let t₁₃ := closedStrataTransition E₁ E₃ h₁₃
    have hcomp : t₂₃.val ≫ t₁₂.val ≫ closedStrataMap E₁ = t₁₃.val ≫ closedStrataMap E₁ := by
      calc
        t₂₃.val ≫ t₁₂.val ≫ closedStrataMap E₁ =
            t₂₃.val ≫ (t₁₂.val ≫ closedStrataMap E₁) := rfl
        _ = t₂₃.val ≫ (closedStrataMap E₂ ≫ stratificationSchemeMap E₁ E₂ h₁₂) := by
          rw [t₁₂.property]
        _ = (t₂₃.val ≫ closedStrataMap E₂) ≫ stratificationSchemeMap E₁ E₂ h₁₂ := by
          simp [Category.assoc]
        _ = (closedStrataMap E₃ ≫ stratificationSchemeMap E₂ E₃ h₂₃) ≫
            stratificationSchemeMap E₁ E₂ h₁₂ := by rw [t₂₃.property]
        _ = closedStrataMap E₃ ≫ stratificationSchemeMap E₁ E₃ h₁₃ := by
          rw [Category.assoc]
          apply congrArg (fun q => closedStrataMap E₃ ≫ q)
          rw [stratificationSchemeMap, stratificationSchemeMap, stratificationSchemeMap,
            ← Spec.map_comp, Spec.map_inj]
          simpa only [CommRingCat.ofHom_comp] using
            congrArg CommRingCat.ofHom (stratificationRingMap_comp E₁ E₂ E₃ h₁₂ h₂₃)
        _ = t₁₃.val ≫ closedStrataMap E₁ := t₁₃.property.symm
    have : Mono (closedStrataMap E₁) := by
      have := closedStrataMap_isClosedImmersion E₁
      infer_instance
    exact (cancel_mono (closedStrataMap E₁)).1 hcomp.symm

/-- The transition map of closed strata for an identity inclusion is the identity. -/
theorem closedStrataTransition_refl (E : Finset A) :
    (closedStrataTransition E E (Finset.Subset.refl E)).val = 𝟙 (closedStrata E) :=
  (closedStrataDiagram (A := A)).map_id (Opposite.op E)

/-- The transition maps of closed strata compose along a chain of inclusions. -/
theorem closedStrataTransition_comp (E₁ E₂ E₃ : Finset A) (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (closedStrataTransition E₂ E₃ h₂₃).val ≫ (closedStrataTransition E₁ E₂ h₁₂).val =
      (closedStrataTransition E₁ E₃ (h₁₂.trans h₂₃)).val :=
  ((closedStrataDiagram (A := A)).map_comp (homOfLE h₂₃).op (homOfLE h₁₂).op).symm

/-- The direct system of global sections of the finite closed strata. -/
@[reducible] def closedSectionDiagram : Finset A ⥤ CommRingCat where
  obj E := Γ(closedStrata E, ⊤)
  map f := (closedStrataTransition _ _ (leOfHom f)).val.appTop
  map_id E := by rw [closedStrataTransition_refl, Scheme.Hom.id_appTop]
  map_comp f g := by
    rw [← closedStrataTransition_comp _ _ _ (leOfHom f) (leOfHom g), Scheme.Hom.comp_appTop]

/-- The transition map of global sections is the one induced by the transition map of closed
strata. -/
theorem closedSectionDiagram_map (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    (closedSectionDiagram (A := A)).map (homOfLE h) =
      (closedStrataTransition E₁ E₂ h).val.appTop :=
  rfl

/-- The inverse system of the spectra of the global sections of the finite closed strata. -/
@[reducible] def closedSchemeDiagram : (Finset A)ᵒᵖ ⥤ Scheme :=
  (closedSectionDiagram (A := A)).op ⋙ Scheme.Spec

/-- The direct limit of a direct system of commutative rings indexed by the finite subsets
of `A`. -/
abbrev ringDirectLimit (D : Finset A ⥤ CommRingCat) : Type u :=
  Ring.DirectLimit (fun E => D.obj E) (fun _ _ h => (D.map (homOfLE h)).hom)

/-- The direct limit of a direct system of commutative rings, as a cocone on the system. -/
def ringDirectLimitCocone (D : Finset A ⥤ CommRingCat) : Cocone D where
  pt := CommRingCat.of (ringDirectLimit D)
  ι :=
    { app := fun E => CommRingCat.ofHom
        (Ring.DirectLimit.of (fun E => D.obj E)
          (fun _ _ h => (D.map (homOfLE h)).hom) E)
      naturality := by
        intro E₁ E₂ f
        ext x
        exact Ring.DirectLimit.of_f
          (G := fun E => D.obj E)
          (f := fun _ _ h => (D.map (homOfLE h)).hom)
          (leOfHom f) x }

/-- The direct-limit cocone is a colimit cocone. -/
def ringDirectLimitIsColimit (D : Finset A ⥤ CommRingCat) :
    IsColimit (ringDirectLimitCocone D) where
  desc s := CommRingCat.ofHom <| Ring.DirectLimit.lift
    (fun E => D.obj E) (fun _ _ h => (D.map (homOfLE h)).hom) s.pt
    (fun E => (s.ι.app E).hom)
    (by
      intro E₁ E₂ h x
      exact congr($(s.w (homOfLE h)).hom x))
  fac s E := by
    ext x
    simp [ringDirectLimitCocone, ringDirectLimit, Ring.DirectLimit.lift_of]
  uniq s m hm := by
    apply CommRingCat.hom_ext
    apply Ring.DirectLimit.hom_ext
    intro E
    ext x
    change
      m.hom (Ring.DirectLimit.of (fun E => D.obj E)
        (fun _ _ h => (D.map (homOfLE h)).hom) E x) =
        (Ring.DirectLimit.lift (fun E => D.obj E)
          (fun _ _ h => (D.map (homOfLE h)).hom) s.pt
          (fun E => (s.ι.app E).hom)
          (by intro E₁ E₂ h x; exact congr($(s.w (homOfLE h)).hom x)))
          (Ring.DirectLimit.of (fun E => D.obj E)
            (fun _ _ h => (D.map (homOfLE h)).hom) E x)
    rw [Ring.DirectLimit.lift_of]
    exact congrArg (fun f : D.obj E ⟶ s.pt => f.hom x) (hm E)

/-- The cone exhibiting `Spec A_w` over the finite-stage schemes `X_E`. -/
def stratificationLimitCone : Cone (stratificationSchemeDiagram (A := A)) :=
  Scheme.Spec.mapCone (ringDirectLimitCocone (stratificationRingDiagram (A := A))).op

/-- `Spec A_w` is the limit of the finite-stage schemes `X_E`. -/
def stratificationLimitCone_isLimit : IsLimit (stratificationLimitCone (A := A)) :=
  isLimitOfPreserves Scheme.Spec
    (ringDirectLimitIsColimit (stratificationRingDiagram (A := A))).op

/-- The cone exhibiting the spectrum of the direct limit of sections over the finite closed
strata. -/
@[reducible] def closedLimitCone : Cone (closedSchemeDiagram (A := A)) :=
  Scheme.Spec.mapCone (ringDirectLimitCocone (closedSectionDiagram (A := A))).op

/-- The spectrum of the direct limit of sections is the limit of the finite closed strata. -/
def closedLimitCone_isLimit : IsLimit (closedLimitCone (A := A)) :=
  isLimitOfPreserves Scheme.Spec
    (ringDirectLimitIsColimit (closedSectionDiagram (A := A))).op

/-- The projection of the limiting cone at a finite stage is the spectrum of the
colimit-ring map. -/
theorem stratificationLimitCone_π_app (E : Finset A) :
    (stratificationLimitCone (A := A)).π.app (Opposite.op E) =
      Spec.map (CommRingCat.ofHom (stratificationColimitMap E)) := by
  simp [stratificationLimitCone, ringDirectLimitCocone, stratificationRingDiagram,
    stratificationColimitMap]
  congr 1

/-- The projection of the closed limiting cone at a finite stage is the spectrum of the
direct-limit structure map. -/
theorem closedLimitCone_π_app (E : Finset A) :
    (closedLimitCone (A := A)).π.app (Opposite.op E) =
      Spec.map ((ringDirectLimitCocone (closedSectionDiagram (A := A))).ι.app E) :=
  rfl

/-- Global sections of a closed immersion of affine schemes are surjective. -/
theorem closedStrataMap_appTop_surjective (E : Finset A) :
    Function.Surjective (closedStrataMap E).appTop := by
  have : IsClosedImmersion (closedStrataMap E) := closedStrataMap_isClosedImmersion E
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (closedStrataMap E)).2

/-- The ring map from `A_E` to the global sections of the closed stratum `Z_E`. -/
def closedStrataRingMap (E : Finset A) :
    CommRingCat.of (stratificationRing E) ⟶ (closedSectionDiagram (A := A)).obj E :=
  (Scheme.ΓSpecIso (.of (stratificationRing E))).inv ≫ (closedStrataMap E).appTop

/-- The ring map onto the sections of a closed stratum is surjective. -/
theorem closedStrataRingMap_surjective (E : Finset A) :
    Function.Surjective (closedStrataRingMap E).hom := by
  intro y
  obtain ⟨z, hz⟩ := closedStrataMap_appTop_surjective E y
  refine ⟨(Scheme.ΓSpecIso (.of (stratificationRing E))).hom.hom z, ?_⟩
  change (closedStrataMap E).appTop.hom
      ((Scheme.ΓSpecIso (.of (stratificationRing E))).inv.hom
        ((Scheme.ΓSpecIso (.of (stratificationRing E))).hom.hom z)) = y
  rw [Iso.hom_inv_id_apply]
  exact hz

/-- The ring maps onto the sections of the closed strata are compatible with the transition
maps of both systems. -/
theorem closedStrataRingMap_naturality (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂)
    (x : stratificationRing E₁) :
    (closedStrataRingMap E₂).hom (stratificationRingMap E₁ E₂ h x) =
      ((closedSectionDiagram (A := A)).map (homOfLE h)).hom ((closedStrataRingMap E₁).hom x) := by
  have ht : (closedStrataMap E₁).appTop ≫ (closedStrataTransition E₁ E₂ h).val.appTop =
      (Spec.map (CommRingCat.ofHom (stratificationRingMap E₁ E₂ h))).appTop ≫
        (closedStrataMap E₂).appTop :=
    congrArg Scheme.Hom.appTop (closedStrataTransition E₁ E₂ h).property
  have hmap : CommRingCat.ofHom (stratificationRingMap E₁ E₂ h) ≫ closedStrataRingMap E₂ =
      closedStrataRingMap E₁ ≫ (closedStrataTransition E₁ E₂ h).val.appTop := by
    dsimp only [closedStrataRingMap]
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← ht, ← Category.assoc]
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    closedSectionDiagram_map] using congr($(hmap).hom x)

/-- The ring map from the stratification colimit onto the direct limit of the sections of the
closed strata. -/
def stratificationLimitToClosedLimitRingMap :
    stratificationColimitRing (A := A) →+* ringDirectLimit (closedSectionDiagram (A := A)) :=
  Ring.DirectLimit.lift
    (fun E => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h)
    (ringDirectLimit (closedSectionDiagram (A := A)))
    (fun E => (Ring.DirectLimit.of
      (fun E => (closedSectionDiagram (A := A)).obj E)
      (fun _ _ h => ((closedSectionDiagram (A := A)).map (homOfLE h)).hom) E).comp
        (closedStrataRingMap E).hom)
    (by
      intro E₁ E₂ h x
      simp only [RingHom.comp_apply]
      change (Ring.DirectLimit.of
        (fun E => (closedSectionDiagram (A := A)).obj E)
        (fun _ _ h => ((closedSectionDiagram (A := A)).map (homOfLE h)).hom) E₂)
          ((closedStrataRingMap E₂).hom (stratificationRingMap E₁ E₂ h x)) = _
      rw [closedStrataRingMap_naturality E₁ E₂ h x]
      exact Ring.DirectLimit.of_f
        (G := fun E => (closedSectionDiagram (A := A)).obj E)
        (f := fun _ _ h => ((closedSectionDiagram (A := A)).map (homOfLE h)).hom)
        h _)

/-- The ring map onto the direct limit of the sections of the closed strata is surjective. -/
theorem stratificationLimitToClosedLimitRingMap_surjective :
    Function.Surjective (stratificationLimitToClosedLimitRingMap (A := A)) := by
  intro y
  obtain ⟨E, x, hx⟩ := Ring.DirectLimit.exists_of
    (G := fun E => (closedSectionDiagram (A := A)).obj E)
    (f := fun _ _ h => ((closedSectionDiagram (A := A)).map (homOfLE h)).hom) y
  obtain ⟨x', hx'⟩ := closedStrataRingMap_surjective E x
  refine ⟨Ring.DirectLimit.of
    (fun E => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) E x', ?_⟩
  simp only [stratificationLimitToClosedLimitRingMap, Ring.DirectLimit.lift_of,
    RingHom.comp_apply]
  rw [hx', hx]

/-- The ring map onto the direct limit of sections is compatible with the colimit-ring maps at
the finite stages. -/
theorem closedStrataRingMap_comp_ι (E : Finset A) :
    CommRingCat.ofHom (stratificationColimitMap E) ≫
        CommRingCat.ofHom (stratificationLimitToClosedLimitRingMap (A := A)) =
      closedStrataRingMap E ≫ (ringDirectLimitCocone (closedSectionDiagram (A := A))).ι.app E := by
  apply CommRingCat.hom_ext
  ext x
  simp [stratificationLimitToClosedLimitRingMap, Ring.DirectLimit.lift_of,
    stratificationColimitMap, ringDirectLimitCocone]

/-- The spectrum `X_w` of the colimit of the finite stratification rings. -/
abbrev stratificationLimitScheme : Scheme.{u} :=
  Spec (.of (stratificationColimitRing (A := A)))

/-- The canonical limiting diagram of finite stratifications and its closed subdiagram. The
stage identifications specify the transition maps, and the cones exhibit `X_w` and `Z` as the
respective limits. -/
structure StratificationLimit (A : Type u) [CommRing A] where
  /-- The inverse system of finite stratification schemes. -/
  schemeDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{u}
  /-- Its identification with the schemes `X_E`. -/
  schemeStage : ∀ E : Finset A,
    schemeDiagram.obj (Opposite.op E) ≅ Spec (.of (stratificationRing E))
  /-- The specified transition map between stages. -/
  schemeTransition : ∀ (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂),
    schemeDiagram.map (homOfLE h).op ≫ (schemeStage E₁).hom =
      (schemeStage E₂).hom ≫ stratificationSchemeMap E₁ E₂ h
  /-- The inverse system of finite closed strata. -/
  closedDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{u}
  /-- Its identification with the schemes `Z_E`. -/
  closedStage : ∀ E : Finset A, closedDiagram.obj (Opposite.op E) ≅ closedStrata E
  /-- The specified transition map between closed strata. -/
  closedTransition : ∀ (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂),
    closedDiagram.map (homOfLE h).op ≫ (closedStage E₁).hom =
      (closedStage E₂).hom ≫ (closedStrataTransition E₁ E₂ h).val
  /-- The canonical cone from `Spec A_w` to the finite-stage schemes. -/
  schemeProjection :
    (Functor.const (Finset A)ᵒᵖ).obj (stratificationLimitScheme (A := A)) ⟶ schemeDiagram
  /-- The projection is induced by the colimit-ring map at each stage. -/
  schemeProjection_spec : ∀ E : Finset A,
    schemeProjection.app (Opposite.op E) ≫ (schemeStage E).hom =
      Spec.map (CommRingCat.ofHom (stratificationColimitMap E))
  /-- `Spec A_w` is the limit of the finite-stage schemes. -/
  schemeIsLimit : IsLimit (Cone.mk (stratificationLimitScheme (A := A)) schemeProjection)
  /-- The limiting closed subscheme `Z`. -/
  closedScheme : Scheme.{u}
  /-- The canonical cone from `Z` to the finite closed strata. -/
  closedProjection : (Functor.const (Finset A)ᵒᵖ).obj closedScheme ⟶ closedDiagram
  /-- `Z` is the limit of the finite closed strata. -/
  closedIsLimit : IsLimit (Cone.mk closedScheme closedProjection)
  /-- The inclusion of the limiting closed subscheme. -/
  inclusion : closedScheme ⟶ stratificationLimitScheme (A := A)
  /-- The inclusion is compatible with the inclusions at finite stages. -/
  inclusion_spec : ∀ E : Finset A,
    inclusion ≫ schemeProjection.app (Opposite.op E) ≫ (schemeStage E).hom =
      closedProjection.app (Opposite.op E) ≫ (closedStage E).hom ≫ closedStrataMap E
  /-- The limit of the closed strata is a closed subscheme. -/
  isClosedImmersion : IsClosedImmersion inclusion

/-- **Stacks 0974.** The canonical closed subscheme `Z = lim Z_E` of
`X_w = Spec A_w = lim X_E`. -/
@[stacks 0974]
def stratificationLimit : StratificationLimit A := by
  classical
  refine
      { schemeDiagram := stratificationSchemeDiagram (A := A)
        schemeStage := fun E => Iso.refl _
        schemeTransition := ?_
        closedDiagram := closedSchemeDiagram (A := A)
        closedStage := fun E => by
          have := closedStrata_isAffine E
          exact (Scheme.isoSpec (closedStrata E)).symm
        closedTransition := ?_
        schemeProjection := (stratificationLimitCone (A := A)).π
        schemeProjection_spec := ?_
        schemeIsLimit := ?_
        closedScheme := (closedLimitCone (A := A)).pt
        closedProjection := (closedLimitCone (A := A)).π
        closedIsLimit := ?_
        inclusion := Spec.map (CommRingCat.ofHom
          (stratificationLimitToClosedLimitRingMap (A := A)))
        inclusion_spec := ?_
        isClosedImmersion := ?_ }
  · intro E₁ E₂ h
    change stratificationSchemeMap E₁ E₂ h ≫ 𝟙 _ = 𝟙 _ ≫ stratificationSchemeMap E₁ E₂ h
    simp
  · intro E₁ E₂ h
    have := closedStrata_isAffine E₁
    have := closedStrata_isAffine E₂
    have hIso := Scheme.isoSpec_inv_naturality (closedStrataTransition E₁ E₂ h).val
    change Spec.map ((closedSectionDiagram (A := A)).map (homOfLE h)) ≫
        (Scheme.isoSpec (closedStrata E₁)).inv =
      (Scheme.isoSpec (closedStrata E₂)).inv ≫ (closedStrataTransition E₁ E₂ h).val
    rw [closedSectionDiagram_map]
    exact hIso
  · intro E
    change Spec.map (CommRingCat.ofHom (stratificationColimitMap E)) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (stratificationColimitMap E))
    simp
  · change IsLimit (stratificationLimitCone (A := A))
    exact stratificationLimitCone_isLimit (A := A)
  · change IsLimit (closedLimitCone (A := A))
    exact closedLimitCone_isLimit (A := A)
  · intro E
    have := closedStrata_isAffine E
    have hspec : Spec.map (closedStrataRingMap E) =
        (Scheme.isoSpec (closedStrata E)).inv ≫ closedStrataMap E := by
      change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (stratificationRing E))).inv ≫
        (closedStrataMap E).appTop) = _
      rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
      exact Scheme.isoSpec_inv_naturality (closedStrataMap E)
    have e1 : (stratificationLimitCone (A := A)).π.app (Opposite.op E) ≫ 𝟙 _ =
        Spec.map (CommRingCat.ofHom (stratificationColimitMap E)) :=
      (Category.comp_id _).trans (stratificationLimitCone_π_app E)
    have e2 : (closedLimitCone (A := A)).π.app (Opposite.op E) ≫
          ((Scheme.isoSpec (closedStrata E)).inv ≫ closedStrataMap E) =
        Spec.map ((ringDirectLimitCocone (closedSectionDiagram (A := A))).ι.app E) ≫
          Spec.map (closedStrataRingMap E) := by
      rw [closedLimitCone_π_app, ← hspec]
    have e3 : Spec.map (CommRingCat.ofHom (stratificationLimitToClosedLimitRingMap (A := A))) ≫
          Spec.map (CommRingCat.ofHom (stratificationColimitMap E)) =
        Spec.map ((ringDirectLimitCocone (closedSectionDiagram (A := A))).ι.app E) ≫
          Spec.map (closedStrataRingMap E) := by
      rw [← Spec.map_comp, ← Spec.map_comp, closedStrataRingMap_comp_ι]
      rfl
    exact ((congrArg (fun q => Spec.map (CommRingCat.ofHom
      (stratificationLimitToClosedLimitRingMap (A := A))) ≫ q) e1).trans e3).trans e2.symm
  · exact IsClosedImmersion.spec_of_surjective _
      (stratificationLimitToClosedLimitRingMap_surjective (A := A))

/-- The limiting closed subscheme `Z = lim Z_E` of `X_w`, as a scheme in its own right. -/
abbrev stratificationLimitClosedScheme : Scheme.{u} :=
  (stratificationLimit (A := A)).closedScheme

/-- The closed immersion `Z ⟶ X_w` of the limiting closed subscheme. -/
abbrev stratificationLimitInclusion :
    stratificationLimitClosedScheme (A := A) ⟶ stratificationLimitScheme (A := A) :=
  (stratificationLimit (A := A)).inclusion

/-- The inclusion `Z ⟶ X_w` is a closed immersion. -/
instance stratificationLimitInclusion_isClosedImmersion :
    IsClosedImmersion (stratificationLimitInclusion (A := A)) :=
  (stratificationLimit (A := A)).isClosedImmersion

end AlgebraicGeometry.ProEtale

end
