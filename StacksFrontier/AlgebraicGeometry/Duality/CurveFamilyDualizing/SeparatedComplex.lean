module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexExistence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexUniqueIso
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeTheorem
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexProperFlatBaseChange

/-!
# A chosen relative dualizing complex of a flat morphism locally of finite presentation

Let `f : X ⟶ S` be flat and locally of finite presentation. The relative diagonal of `f` is an
immersion, so it factors as a closed immersion into the open `W = coborder(Δ(X)) ⊆ X ×_S X`
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.coborder`). By Stacks 0E2X there is a relative
dualizing complex `(K, ξ)` for `f` relative to that open (Stacks 0E2T), and by Stacks 0E2W it is
unique up to unique isomorphism. This file fixes one,
`AlgebraicGeometry.Scheme.Hom.relDualizingComplex f`, together with its map
`AlgebraicGeometry.Scheme.Hom.relDualizingMap f`.

It also provides `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictOpen`, the restriction of a
diagonal open to a smaller open still containing the diagonal, which is how two relative
dualizing complexes given relative to different opens are compared.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The standard model of `D(𝒪_T)`, for `letI`. -/
local macro "stdᴰ[" T:term "]" : term => `(HasDerivedCategory.standard (OXMod $T))

/-- The standard models of `D(𝒪_{T|_U})` for all opens `U` of `T`, for `letI`. -/
local macro "stdOpens[" T:term "]" : term =>
  `(fun (U : TopologicalSpace.Opens ($T).carrier) =>
    HasDerivedCategory.standard (OXMod (($T).restrict U.isOpenEmbedding)))

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

namespace DiagonalOpen

variable {X S : Scheme.{u}}

/-- **The coborder diagonal open.** The relative diagonal of any morphism of schemes is an
immersion, hence a closed immersion into the coborder of its image, the largest open of
`X ×_S X` in which the diagonal is closed. -/
def coborder (f : X ⟶ S) : DiagonalOpen f where
  W := (pullback.diagonal f).coborderRange
  ι := (pullback.diagonal f).coborderRange.ι
  isOpenImmersion := inferInstance
  diag := (pullback.diagonal f).liftCoborder
  isClosedImmersion := inferInstance
  fac := Scheme.Hom.liftCoborder_ι _

variable {f : X ⟶ S}

/-- **Restriction of a diagonal open to a smaller open containing the diagonal.** If `O` is an
open of `W` containing the image of `Δ : X ⟶ W`, then `Δ` factors through `O` as a closed
immersion. -/
def restrictOpen (D : DiagonalOpen f) (O : D.W.Opens) (hO : Set.range D.diag ⊆ O) :
    DiagonalOpen f where
  W := O
  ι := O.ι ≫ D.ι
  isOpenImmersion := by
    have := D.isOpenImmersion
    infer_instance
  diag := IsOpenImmersion.lift O.ι D.diag (by simpa using hO)
  isClosedImmersion := by
    have := D.isClosedImmersion
    have h : IsOpenImmersion.lift O.ι D.diag (by simpa using hO) ≫ O.ι = D.diag :=
      IsOpenImmersion.lift_fac _ _ _
    have : IsClosedImmersion (IsOpenImmersion.lift O.ι D.diag (by simpa using hO) ≫ O.ι) := by
      rw [h]; infer_instance
    exact IsClosedImmersion.of_comp _ O.ι
  fac := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, D.fac]

/-- The inclusion of a restricted diagonal open into the original one. -/
abbrev restrictOpenInclusion (D : DiagonalOpen f) (O : D.W.Opens) (hO : Set.range D.diag ⊆ O) :
    (D.restrictOpen O hO).W ⟶ D.W :=
  O.ι

/-- The inclusion of a restricted diagonal open followed by the original immersion is the
immersion of the restricted diagonal open. -/
theorem restrictOpenInclusion_ι (D : DiagonalOpen f) (O : D.W.Opens)
    (hO : Set.range D.diag ⊆ O) :
    D.restrictOpenInclusion O hO ≫ D.ι = (D.restrictOpen O hO).ι :=
  rfl

end DiagonalOpen

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]

/-- Stacks 0E2X at the coborder diagonal open. -/
theorem exists_isRelativeDualizingComplex_coborder :
    letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
    letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
    ∃ (K : @DerivedCategory (OXMod.{u, u} X.toRingedSpace) _ _ (HasDerivedCategory.standard _))
      (ξ : (DiagonalOpen.coborder f).diagonalObject ⟶
        (DiagonalOpen.coborder f).derivedPullbackProj K),
      IsRelativeDualizingComplex f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base))
        (DiagonalOpen.coborder f) K ξ :=
  letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
  letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
  exists_isRelativeDualizingComplex_canonicalFamily (DiagonalOpen.coborder f)

/-- **The chosen relative dualizing complex** `ω^•_{X/S}` of a flat morphism locally of finite
presentation, relative to the coborder diagonal open. -/
def relDualizingComplex :
    @DerivedCategory (OXMod.{u, u} X.toRingedSpace) _ _ (HasDerivedCategory.standard _) :=
  (exists_isRelativeDualizingComplex_coborder f).choose

/-- The map `ξ : Δ_*𝒪_X ⟶ L pr₁^*ω^•_{X/S}|_W` accompanying the chosen relative dualizing
complex. -/
def relDualizingMap :
    (DiagonalOpen.coborder f).diagonalObject ⟶
      (DiagonalOpen.coborder f).derivedPullbackProj (relDualizingComplex f) :=
  (exists_isRelativeDualizingComplex_coborder f).choose_spec.choose

/-- The chosen pair is a relative dualizing complex. -/
theorem isRelativeDualizingComplex_relDualizing :
    letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
    letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
    IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base))
      (DiagonalOpen.coborder f) (relDualizingComplex f) (relDualizingMap f) :=
  letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
  letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
  (exists_isRelativeDualizingComplex_coborder f).choose_spec.choose_spec


section BaseChange

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  [Flat f] [LocallyOfFinitePresentation f] (hpb : IsPullback g' f' f g)

/-- The open of the coborder diagonal open of `f'` mapped by `g' × g'` into the coborder
diagonal open of `f`. -/
def baseChangeOpen : (DiagonalOpen.coborder f').W.Opens :=
  ((DiagonalOpen.coborder f').ι ≫ pullbackMapOfIsPullback hpb) ⁻¹ᵁ
    (pullback.diagonal f).coborderRange

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The diagonal of `f'` lands in `baseChangeOpen`, so that the coborder diagonal open of `f'`
can be restricted to it. -/
theorem range_diag_subset_baseChangeOpen :
    Set.range (DiagonalOpen.coborder f').diag ⊆ baseChangeOpen hpb := by
  rintro _ ⟨x, rfl⟩
  change ((DiagonalOpen.coborder f').ι ≫ pullbackMapOfIsPullback hpb)
    ((DiagonalOpen.coborder f').diag x) ∈ (pullback.diagonal f).coborderRange
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, (DiagonalOpen.coborder f').fac,
    diagonal_comp_pullbackMapOfIsPullback hpb, Scheme.Hom.comp_apply]
  exact subset_coborder ⟨_, rfl⟩

/-- The diagonal open of `f'` on which the base change of the chosen relative dualizing complex of
`f` is compared with the chosen one of `f'`. -/
def baseChangeDiagonalOpen : DiagonalOpen f' :=
  (DiagonalOpen.coborder f').restrictOpen (baseChangeOpen hpb)
    (range_diag_subset_baseChangeOpen hpb)

/-- `g' × g'` restricted to `baseChangeDiagonalOpen`, landing in the coborder of `f`. -/
def baseChangeW : (baseChangeDiagonalOpen hpb).W ⟶ (DiagonalOpen.coborder f).W :=
  IsOpenImmersion.lift (DiagonalOpen.coborder f).ι
    ((baseChangeDiagonalOpen hpb).ι ≫ pullbackMapOfIsPullback hpb) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨_, x.2⟩, rfl⟩)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `baseChangeW` followed by the immersion of the coborder of `f` is the immersion of
`baseChangeDiagonalOpen` followed by `g' × g'`. -/
theorem baseChangeW_ι :
    baseChangeW hpb ≫ (DiagonalOpen.coborder f).ι =
      (baseChangeDiagonalOpen hpb).ι ≫ pullbackMapOfIsPullback hpb := by
  unfold baseChangeW
  exact IsOpenImmersion.lift_fac _ _ _

/-- The derived base change of the chosen pair of `f`, as a relative dualizing complex for `f'`
relative to `baseChangeDiagonalOpen` (Stacks 0E2Y). -/
theorem isRelativeDualizingComplex_baseChange_relDualizing :
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb (inferInstance : Flat f)
    haveI : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb
        (inferInstance : LocallyOfFinitePresentation f)
    letI := stdᴰ[RingedSpace.inverseImage S'.toRingedSpace f'.base]
    letI := stdOpens[RingedSpace.inverseImage S'.toRingedSpace f'.base]
    IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S'.toRingedSpace f'.base)) (baseChangeDiagonalOpen hpb)
      (DiagonalOpen.baseChangeComplex g' (relDualizingComplex f))
      ((DiagonalOpen.coborder f).baseChangeDiagonalMap (baseChangeDiagonalOpen hpb) g'
        (baseChangeW hpb)
        (DiagonalOpen.proj_baseChange hpb _ _ (baseChangeW hpb) (baseChangeW_ι hpb))
        (DiagonalOpen.baseChangeDiagonalIso hpb _ _ (baseChangeW hpb) (baseChangeW_ι hpb))
        (relDualizingComplex f) (relDualizingMap f)) :=
  letI := stdᴰ[RingedSpace.inverseImage S'.toRingedSpace f'.base]
  letI := stdOpens[RingedSpace.inverseImage S'.toRingedSpace f'.base]
  (isRelativeDualizingComplex_relDualizing f).baseChange hpb _ (baseChangeW hpb)
    (baseChangeW_ι hpb)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The chosen pair of `f'`, restricted to `baseChangeDiagonalOpen` (derived base change along the
identity square), as a relative dualizing complex for `f'` there. -/
theorem isRelativeDualizingComplex_restrict_relDualizing [Flat f']
    [LocallyOfFinitePresentation f'] :
    letI := stdᴰ[RingedSpace.inverseImage S'.toRingedSpace f'.base]
    letI := stdOpens[RingedSpace.inverseImage S'.toRingedSpace f'.base]
    IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S'.toRingedSpace f'.base)) (baseChangeDiagonalOpen hpb)
      (DiagonalOpen.baseChangeComplex (𝟙 X') (relDualizingComplex f'))
      ((DiagonalOpen.coborder f').baseChangeDiagonalMap (baseChangeDiagonalOpen hpb) (𝟙 X')
        ((DiagonalOpen.coborder f').restrictOpenInclusion _ (range_diag_subset_baseChangeOpen hpb))
        (DiagonalOpen.proj_baseChange (isPullback_id f') _ _ _
          (DiagonalOpen.comp_ι_eq_isPullback_id _ _ _
            ((DiagonalOpen.coborder f').restrictOpenInclusion_ι _ _)))
        (DiagonalOpen.baseChangeDiagonalIso (isPullback_id f') _ _ _
          (DiagonalOpen.comp_ι_eq_isPullback_id _ _ _
            ((DiagonalOpen.coborder f').restrictOpenInclusion_ι _ _)))
        (relDualizingComplex f') (relDualizingMap f')) :=
  letI := stdᴰ[RingedSpace.inverseImage S'.toRingedSpace f'.base]
  letI := stdOpens[RingedSpace.inverseImage S'.toRingedSpace f'.base]
  (isRelativeDualizingComplex_relDualizing f').baseChange (isPullback_id f') _ _
    (DiagonalOpen.comp_ι_eq_isPullback_id _ _ _
      ((DiagonalOpen.coborder f').restrictOpenInclusion_ι _ _))

end BaseChange

end AlgebraicGeometry.Scheme.Hom

end
