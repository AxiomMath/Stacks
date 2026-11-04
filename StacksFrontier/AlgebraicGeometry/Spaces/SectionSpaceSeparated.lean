module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart

/-!
# The space of sections is an algebraic space étale over the base, in the separated case

Let `Z ⟶ U` be a finite morphism of the big fppf site of `U` and let `w : W ⟶ h_Z` be an étale
morphism of presheaves on that site with `W` an algebraic space. Sending a section of
`W_T ⟶ Z_T` to the pair of Stacks 04PC it defines, which is
`AlgebraicGeometry.Space.sectionPair`, is a morphism of presheaves from the space of sections of
Stacks 05XR to the finite part `(W/U)_fin` of the structure morphism `W ⟶ U`, and it is a
monomorphism.

That comparison is in fact an open immersion: over a scheme-valued point of the finite part it
cuts out the locus on which the comparison of the named open subspace with `T × Z` becomes an
isomorphism, and that locus is open. Since the finite part of a separated morphism locally of
finite type is an algebraic space étale over `U` by Stacks 04QH, the space of sections is an
algebraic space étale over `U` as soon as `w` is separated. This is **Stacks 05XR for a
separated `w`**, the case from which the source deduces the general one.

## Main definitions

* `AlgebraicGeometry.Space.sectionSpaceToFinitePart`: the comparison morphism.
* `AlgebraicGeometry.Space.finitePairComparison`: the comparison of the open subspace of a pair of
  Stacks 04PC with `T × Z`.
* `AlgebraicGeometry.Space.finitePairProjection`: the projection of that open subspace to `T`.
* `AlgebraicGeometry.Space.terminalAmbientProjection`: a base change of `w` formed inside the
  fibre product of two morphisms to the terminal presheaf.

## Main results

* `AlgebraicGeometry.Space.mono_sectionSpaceToFinitePart` and
  `AlgebraicGeometry.Space.isOpenImmersion_sectionSpaceToFinitePart`: the comparison morphism is
  a monomorphism, and an open immersion.
* `AlgebraicGeometry.Space.exists_sectionPair_eq_iff`: a pair of Stacks 04PC comes from a
  section exactly when its comparison with `T × Z` is an isomorphism.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_finitePairComparison_isIso`: the open locus in the
  base over which that comparison becomes an isomorphism.
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isSeparated` and
  `AlgebraicGeometry.Space.isEtale_sectionSpace_of_isSeparated`: **Stacks 05XR for a separated
  `w`**.

## Implementation notes

Naturality of the comparison morphism is the statement that the pair of a restricted section is
the base change of the pair, which is `AlgebraicGeometry.Space.isBaseChange_sectionPair`,
together with the uniqueness of a base change of a pair,
`AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange.unique`. The restriction maps of the
two sides are only described through the identifications of their sections, so both are
transported through those identifications rather than computed.

The base morphism of a pair of Stacks 04PC for `W ⟶ U` is a morphism to the terminal presheaf
and therefore equal to `CategoryTheory.Limits.terminal.from`, but only propositionally, so the
fibre product it sits over is not the one `terminal.from` names. Everything about a pair is
therefore phrased through that pair's own base morphism —
`AlgebraicGeometry.Space.finitePairComparison`,
`AlgebraicGeometry.Space.finitePairProjection` and the two-argument
`AlgebraicGeometry.Space.terminalAmbientProjection` — rather than through the canonical
representative.

The isomorphism locus used is the unconditional one for a flat morphism,
`AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange_of_isFlat`, available
because the comparison of the open subspace of a pair with `T × Z` is étale. In particular no
flat-locus hypothesis is carried. The general case of Stacks 05XR, which the source deduces
from this one by the bootstrap theorem Stacks 04S6, is
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_and_isEtale`, which reaches it from this one
without the bootstrap theorem; that result carries the tag.

No hypothesis is carried: every input is an unconditional result of the library.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}

/-- Restriction in `AlgebraicGeometry.Space.sectionSpace` is restriction of sections. -/
theorem sectionSpaceEquiv_restrict (w : W ⟶ yoneda.obj Z) {T T' : BigFppfOver B U hU}
    (h : T' ⟶ T) (s : (sectionSpace B U hU Z W w).obj (op T)) :
    sectionSpaceEquiv B U hU Z T' W w ((sectionSpace B U hU Z W w).map h.op s) =
      SectionsOver.restrict h (sectionSpaceEquiv B U hU Z T W w s) :=
  Subtype.ext ((sectionSpaceEquiv_map B U hU Z T T' W w h s).trans
    (SectionsOver.restrict_coe h _).symm)

/-- **The comparison of the space of sections of `W ⟶ Z` with the finite part of `W ⟶ U`**: a
section of `W_T ⟶ Z_T` is sent to the pair of Stacks 04PC it defines. -/
noncomputable def sectionSpaceToFinitePart (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    sectionSpace B U hU Z W w ⟶
      (finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)).toFunctor where
  app T := ↾fun s =>
    ((finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)).sections T.unop).symm
      (sectionPair hW hw hZfin (sectionSpaceEquiv B U hU Z T.unop W w s))
  naturality := by
    rintro ⟨T⟩ ⟨T'⟩ f
    ext s
    set P := finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)
    change (P.sections T').symm (sectionPair hW hw hZfin
        (sectionSpaceEquiv B U hU Z T' W w ((sectionSpace B U hU Z W w).map f.unop.op s))) =
      P.toFunctor.map f.unop.op ((P.sections T).symm
        (sectionPair hW hw hZfin (sectionSpaceEquiv B U hU Z T W w s)))
    have h1 := P.map_isBaseChange f.unop
      ((P.sections T).symm (sectionPair hW hw hZfin (sectionSpaceEquiv B U hU Z T W w s)))
    rw [Equiv.apply_symm_apply] at h1
    apply (P.sections T').injective
    rw [Equiv.apply_symm_apply, sectionSpaceEquiv_restrict]
    exact FiniteOpenSubspace.IsBaseChange.unique B U hU
      (isBaseChange_sectionPair hW hw hZfin f.unop (sectionSpaceEquiv B U hU Z T W w s)) h1

/-- The components of the comparison morphism: a section is sent to the pair it defines. -/
theorem sectionSpaceToFinitePart_sections (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    (T : BigFppfOver B U hU) (s : (sectionSpace B U hU Z W w).obj (op T)) :
    (finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)).sections T
        ((sectionSpaceToFinitePart hW hw hZfin).app (op T) s) =
      sectionPair hW hw hZfin (sectionSpaceEquiv B U hU Z T W w s) :=
  Equiv.apply_symm_apply _ _

/-- The comparison morphism is a monomorphism: a section is determined by its pair. -/
theorem mono_sectionSpaceToFinitePart (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    Mono (sectionSpaceToFinitePart hW hw hZfin) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨T⟩
  rw [mono_iff_injective]
  intro s s' hss
  refine (sectionSpaceEquiv B U hU Z T W w).injective (sectionPair_injective hW hw hZfin ?_)
  show sectionPair hW hw hZfin (sectionSpaceEquiv B U hU Z T W w s) =
    sectionPair hW hw hZfin (sectionSpaceEquiv B U hU Z T W w s')
  rw [← sectionSpaceToFinitePart_sections hW hw hZfin T s,
    ← sectionSpaceToFinitePart_sections hW hw hZfin T s', hss]

/-! ### Pairs that come from a section -/

/-- Two pairs of Stacks 04PC agree as soon as their base morphisms and their open subspaces
do. -/
private theorem finiteOpenSubspace_ext {X Y T : AlgebraicSpaces B U hU} {f : X ⟶ Y}
    {p q : FiniteOpenSubspace B U hU f T} (ha : p.toBase = q.toBase)
    (hS : HEq p.subspace q.subspace) : p = q := by
  cases p
  cases q
  cases ha
  cases hS
  rfl

/-- **The comparison of the open subspace of a pair of Stacks 04PC with `T × Z`**: the
projection to `T` on the first component and the projection to `W` followed by `w` on the
second. -/
noncomputable def finitePairComparison (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z)
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    q.subspace.toFunctor ⟶ yoneda.obj T ⨯ yoneda.obj Z :=
  prod.lift (q.subspace.ι ≫ pullback.fst q.toBase.hom (toTerminalPresheaf B U hU hW).hom)
    (q.subspace.ι ≫ pullback.snd q.toBase.hom (toTerminalPresheaf B U hU hW).hom ≫ w)

/-- The first component of `finitePairComparison` is the projection of the open subspace to `T`. -/
theorem finitePairComparison_comp_fst (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z)
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    finitePairComparison hW w q ≫ prod.fst =
      q.subspace.ι ≫ pullback.fst q.toBase.hom (toTerminalPresheaf B U hU hW).hom :=
  prod.lift_fst _ _

/-- The second component of `finitePairComparison` is the projection of the open subspace to `W`
followed by `w`. -/
theorem finitePairComparison_comp_snd (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z)
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    finitePairComparison hW w q ≫ prod.snd =
      q.subspace.ι ≫ pullback.snd q.toBase.hom (toTerminalPresheaf B U hU hW).hom ≫ w :=
  prod.lift_snd _ _

/-- For a pair coming from a section the comparison with `T × Z` is the inverse of the
comparison of `T × Z` with the image of `sectionLift`, hence an isomorphism. -/
theorem finitePairComparison_sectionPair (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    finitePairComparison hW w (sectionPair hW hw hZfin σ) = (sectionLiftRangeIso σ).inv := by
  show prod.lift ((Subfunctor.range (sectionLift σ)).ι ≫
      pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W))
      ((Subfunctor.range (sectionLift σ)).ι ≫
        pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) ≫ w) = _
  rw [← range_sectionLift_ι_comp_sectionAmbientProjection σ]
  refine prod.hom_ext ?_ ?_
  · rw [prod.lift_fst, Category.assoc, sectionAmbientProjection_comp_fst]
  · rw [prod.lift_snd, Category.assoc, sectionAmbientProjection_comp_snd]

/-- **An open subspace of `T ×_U W` whose comparison with `T × Z` is an isomorphism is the
image of a section.** The inverse of the comparison, followed by the projection to `W`, is the
section, and the image of its lift is the given subspace. -/
theorem exists_sectionLift_range_eq {w : W ⟶ yoneda.obj Z} {T : BigFppfOver B U hU}
    (S : Subfunctor (pullback (terminal.from (yoneda.obj T)) (terminal.from W)))
    (hiso : IsIso (S.ι ≫ sectionAmbientProjection T w)) :
    ∃ σ : SectionsOver B U hU Z T W w, Subfunctor.range (sectionLift σ) = S := by
  have hsec : (inv (S.ι ≫ sectionAmbientProjection T w) ≫ S.ι ≫
      pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W)) ≫ w = prod.snd := by
    calc (inv (S.ι ≫ sectionAmbientProjection T w) ≫ S.ι ≫
            pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W)) ≫ w
        = inv (S.ι ≫ sectionAmbientProjection T w) ≫
            (S.ι ≫ sectionAmbientProjection T w) ≫ prod.snd := by
          simp only [Category.assoc, sectionAmbientProjection_comp_snd]
      _ = prod.snd := IsIso.inv_hom_id_assoc _ _
  refine ⟨⟨inv (S.ι ≫ sectionAmbientProjection T w) ≫ S.ι ≫
      pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W), hsec⟩, ?_⟩
  have hlift : sectionLift (⟨inv (S.ι ≫ sectionAmbientProjection T w) ≫ S.ι ≫
        pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W), hsec⟩ :
      SectionsOver B U hU Z T W w) = inv (S.ι ≫ sectionAmbientProjection T w) ≫ S.ι := by
    refine pullback.hom_ext ?_ ?_
    · rw [sectionLift_comp_fst]
      calc (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)
          = inv (S.ι ≫ sectionAmbientProjection T w) ≫
              (S.ι ≫ sectionAmbientProjection T w) ≫ prod.fst := (IsIso.inv_hom_id_assoc _ _).symm
        _ = (inv (S.ι ≫ sectionAmbientProjection T w) ≫ S.ι) ≫
              pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W) := by
            simp only [Category.assoc, sectionAmbientProjection_comp_fst]
    · rw [sectionLift_comp_snd]
      simp only [Category.assoc]
  rw [hlift, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
    Subfunctor.range_ι]

/-- **A pair of Stacks 04PC for `W ⟶ U` comes from a section of `W_T ⟶ Z_T` exactly when its
comparison with `T × Z` is an isomorphism.** -/
theorem exists_sectionPair_eq_iff (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    (∃ σ : SectionsOver B U hU Z T W w, sectionPair hW hw hZfin σ = q) ↔
      IsIso (finitePairComparison hW w q) := by
  constructor
  · rintro ⟨σ, rfl⟩
    rw [finitePairComparison_sectionPair]
    exact ⟨(sectionLiftRangeIso σ).hom, (sectionLiftRangeIso σ).inv_hom_id,
      (sectionLiftRangeIso σ).hom_inv_id⟩
  · intro hiso
    obtain ⟨a, S, hSopen, hSfin⟩ := q
    obtain rfl : a = schemeToTerminalPresheaf B U hU T :=
      ObjectProperty.hom_ext _ (terminal.hom_ext _ _)
    have hcomp : finitePairComparison hW w
        (⟨schemeToTerminalPresheaf B U hU T, S, hSopen, hSfin⟩ :
          FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) =
        S.ι ≫ sectionAmbientProjection T w := by
      show prod.lift (S.ι ≫ pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W))
          (S.ι ≫ pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) ≫ w) =
        S.ι ≫ prod.lift (pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W))
          (pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) ≫ w)
      exact (prod.comp_lift _ _ _).symm
    rw [hcomp] at hiso
    obtain ⟨σ, hσ⟩ := exists_sectionLift_range_eq S hiso
    exact ⟨σ, finiteOpenSubspace_ext rfl (heq_of_eq hσ)⟩

/-! ### Étaleness of the comparison of a pair with `T × Z` -/

/-- Étaleness of a morphism of presheaves follows from the relatively representable étale
property, étaleness of morphisms of schemes being multiplicative. -/
theorem isEtale_of_presheafEtaleProperty (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsEtale B S hS f :=
  fun _ _ hφ => (isMultiplicative_presheaf_etale B S hS).comp_mem _ _ hφ hf

/-- The base change of `w : W ⟶ h_Z` along the projection `A × Z ⟶ h_Z`, formed inside the
fibre product of two arbitrary morphisms to the terminal presheaf. -/
noncomputable def terminalAmbientProjection {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    (a : A ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u))
    (b : W ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u)) (w : W ⟶ yoneda.obj Z) :
    pullback a b ⟶ A ⨯ yoneda.obj Z :=
  prod.lift (pullback.fst a b) (pullback.snd a b ≫ w)

/-- The first component of `terminalAmbientProjection` is the first projection. -/
theorem terminalAmbientProjection_comp_fst {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    (a : A ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u))
    (b : W ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u)) (w : W ⟶ yoneda.obj Z) :
    terminalAmbientProjection a b w ≫ prod.fst = pullback.fst a b :=
  prod.lift_fst _ _

/-- The second component of `terminalAmbientProjection` is the second projection followed
by `w`. -/
theorem terminalAmbientProjection_comp_snd {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    (a : A ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u))
    (b : W ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u)) (w : W ⟶ yoneda.obj Z) :
    terminalAmbientProjection a b w ≫ prod.snd = pullback.snd a b ≫ w :=
  prod.lift_snd _ _

/-- `terminalAmbientProjection` is a base change of `w`. -/
theorem isPullback_terminalAmbientProjection {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    (a : A ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u))
    (b : W ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u)) (w : W ⟶ yoneda.obj Z) :
    IsPullback (terminalAmbientProjection a b w) (pullback.snd a b)
      (prod.snd : A ⨯ yoneda.obj Z ⟶ yoneda.obj Z) w := by
  refine IsPullback.mk' (terminalAmbientProjection_comp_snd a b w) ?_ ?_
  · intro C φ φ' h₁ h₂
    refine pullback.hom_ext ?_ h₂
    simpa only [Category.assoc, terminalAmbientProjection_comp_fst] using
      congrArg (fun t => t ≫ (prod.fst : A ⨯ yoneda.obj Z ⟶ A)) h₁
  · intro C α β hαβ
    refine ⟨pullback.lift (α ≫ prod.fst) β (terminal.hom_ext _ _), ?_, pullback.lift_snd _ _ _⟩
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, terminalAmbientProjection_comp_fst, pullback.lift_fst]
    · rw [Category.assoc, terminalAmbientProjection_comp_snd, ← Category.assoc,
        pullback.lift_snd]
      exact hαβ.symm

/-- A base change of an étale `w` along the projection `T × Z ⟶ h_Z` is étale. -/
theorem isEtale_terminalAmbientProjection (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w) {T : BigFppfOver B U hU}
    (a : yoneda.obj T ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u))
    (b : W ⟶ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u)) :
    IsEtale B U hU (terminalAmbientProjection a b w) :=
  isEtale_of_isPullback_of_isAlgebraicSpace B U hU (isPullback_terminalAmbientProjection a b w)
    (isAlgebraicSpace_pullback B U hU a b (isAlgebraicSpace_yoneda B U hU T) hW
      (isAlgebraicSpace_terminal B U hU))
    (isAlgebraicSpace_yoneda_prod_yoneda T Z) hW (isAlgebraicSpace_yoneda B U hU Z) hw

/-- The comparison of the open subspace of a pair with `T × Z` is the inclusion of the open
subspace followed by a base change of `w`. -/
theorem finitePairComparison_eq (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z)
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    finitePairComparison hW w q =
      q.subspace.ι ≫
        terminalAmbientProjection q.toBase.hom (toTerminalPresheaf B U hU hW).hom w :=
  (prod.comp_lift _ _ _).symm

/-- The comparison of the open subspace of a pair with `T × Z` is étale: the inclusion of an
open subspace is étale and so is a base change of `w`. -/
theorem isEtale_finitePairComparison (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w) {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    IsEtale B U hU (finitePairComparison hW w q) := by
  rw [finitePairComparison_eq]
  exact isEtale_comp B U hU (isEtale_of_isOpenImmersion B U hU q.isOpen.2)
    (isEtale_terminalAmbientProjection hW hw _ _)

/-- The projection of the open subspace of a pair of Stacks 04PC to the base. -/
noncomputable def finitePairProjection (hW : IsAlgebraicSpace B U hU W) {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    q.subspace.toFunctor ⟶ yoneda.obj T :=
  q.subspace.ι ≫ pullback.fst q.toBase.hom (toTerminalPresheaf B U hU hW).hom

/-- The comparison of the open subspace of a pair with `T × Z`, followed by the projection to
`T`, is the projection of the open subspace to `T`. -/
theorem finitePairComparison_comp_prodFst (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z)
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    finitePairComparison hW w q ≫ prod.fst = finitePairProjection hW q :=
  prod.lift_fst _ _

/-- The projection of the open subspace of a pair to the base is finite. -/
theorem isFinite_finitePairProjection (hW : IsAlgebraicSpace B U hU W) {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    IsFinite B U hU (finitePairProjection hW q) :=
  q.finite_projection

/-- **The open locus in the base over which the comparison of a pair with `T × Z` becomes an
isomorphism.** The comparison is étale, hence flat and locally of finite presentation, the
projection of the open subspace to the base is finite, hence locally of finite type and
universally closed, and the projection `T × Z ⟶ T` is finite, hence separated and closed; so
the isomorphism locus of a flat morphism applies. -/
theorem exists_isOpenSubspace_finitePairComparison_isIso (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU}
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T)) :
    ∃ V : Subfunctor (yoneda.obj T), IsOpenSubspace B U hU V ∧
      ∀ (A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B U hU A)
        (g : A ⟶ yoneda.obj T),
        (∃ r : A ⟶ V.toFunctor, r ≫ V.ι = g) ↔
          IsIso (baseChangeOverBase B U hU (finitePairComparison hW w q) (finitePairProjection hW q)
            (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)
            (finitePairComparison_comp_prodFst hW w q) g) := by
  have halgS := q.isOpen.1
  have halgP := isAlgebraicSpace_yoneda_prod_yoneda T Z
  have halgT := isAlgebraicSpace_yoneda B U hU T
  have hfet := isEtale_finitePairComparison hW hw q
  have hpproper := (isFinite_iff_isAffineHom_and_isProper B U hU halgS halgT
    (finitePairProjection hW q)).mp (isFinite_finitePairProjection hW q)
  have hqproper := (isFinite_iff_isAffineHom_and_isProper B U hU halgP halgT
    (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)).mp (isFinite_prod_fst T Z hZfin)
  exact exists_isOpenSubspace_iff_isIso_baseChange_of_isFlat B U hU halgS halgP halgT
    (finitePairComparison hW w q) (finitePairProjection hW q) prod.fst
    (finitePairComparison_comp_prodFst hW w q) (isFlat_of_isEtale B U hU hfet)
    (isLocallyOfFinitePresentation_of_isEtale B U hU hfet)
    hpproper.2.2.1.1 hpproper.2.2.2 hqproper.2.1
    (isClosed_of_universallyClosed B U hU halgT _ hqproper.2.2.2)

/-! ### The comparison morphism is an open immersion -/

/-- A morphism of the site lies in a subfunctor of the presheaf its target represents exactly
when it factors through that subfunctor. -/
private theorem mem_subfunctor_iff {T₀ : BigFppfOver B U hU} (V : Subfunctor (yoneda.obj T₀))
    {T' : BigFppfOver B U hU} (x : T' ⟶ T₀) :
    x ∈ V.obj (op T') ↔ ∃ r : yoneda.obj T' ⟶ V.toFunctor, r ≫ V.ι = yoneda.map x := by
  constructor
  · intro hx
    refine ⟨Subfunctor.lift (yoneda.map x) ?_, Subfunctor.lift_ι _ _⟩
    rintro ⟨A⟩ _ ⟨y, rfl⟩
    exact V.map y.op hx
  · rintro ⟨r, hr⟩
    have hle : Subfunctor.range (yoneda.map x) ≤ V := by
      rw [← hr]
      exact (Subfunctor.range_comp_le r V.ι).trans (le_of_eq (Subfunctor.range_ι V))
    exact hle (op T') ⟨𝟙 T', by simp⟩

/-- A section over `T'` of a presheaf named by a morphism out of a representable presheaf is the
restriction of the section naming that morphism. -/
private theorem app_eq_map_app_id {F : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    {T₀ : BigFppfOver B U hU} (g : yoneda.obj T₀ ⟶ F) {T' : BigFppfOver B U hU}
    (x : T' ⟶ T₀) : g.app (op T') x = F.map x.op (g.app (op T₀) (𝟙 T₀)) := by
  simpa using NatTrans.naturality_apply g x.op (𝟙 T₀)

/-- **The comparison of a base-changed pair with `T' × Z` is the base change of the comparison
of the original pair with `T × Z`**, up to the two canonical isomorphisms, so one is an
isomorphism exactly when the other is. -/
private theorem isIso_finitePairComparison_iff (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} {T T' : BigFppfOver B U hU}
    (p : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T))
    (q : FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T'))
    (x : T' ⟶ T)
    (hbc : FiniteOpenSubspace.IsBaseChange B U hU (toTerminalPresheaf B U hU hW) x p q) :
    IsIso (finitePairComparison hW w q) ↔
      IsIso (baseChangeOverBase B U hU (finitePairComparison hW w p) (finitePairProjection hW p)
        (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)
        (finitePairComparison_comp_prodFst hW w p) (yoneda.map x)) := by
  obtain ⟨-, j, hj, hjx⟩ := hbc
  have hj' : IsPullback (finitePairProjection hW q) j (yoneda.map x)
      (finitePairProjection hW p) := hj
  have hbase := IsPullback.of_hasPullback (finitePairProjection hW p) (yoneda.map x)
  have hprodbase := IsPullback.of_hasPullback
    (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) (yoneda.map x)
  set e₁ := hj'.flip.isoIsPullback _ _ hbase
  set e₂ := (isPullback_prod_map_fst x Z).flip.isoIsPullback _ _ hprodbase
  have he₁fst : e₁.hom ≫ pullback.fst (finitePairProjection hW p) (yoneda.map x) = j :=
    hj'.flip.isoIsPullback_hom_fst _ _ hbase
  have he₁snd : e₁.hom ≫ pullback.snd (finitePairProjection hW p) (yoneda.map x) =
      finitePairProjection hW q :=
    hj'.flip.isoIsPullback_hom_snd _ _ hbase
  have he₂fst : e₂.hom ≫ pullback.fst
      (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) (yoneda.map x) =
      prod.map (yoneda.map x) (𝟙 (yoneda.obj Z)) :=
    (isPullback_prod_map_fst x Z).flip.isoIsPullback_hom_fst _ _ hprodbase
  have he₂snd : e₂.hom ≫ pullback.snd
      (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) (yoneda.map x) = prod.fst :=
    (isPullback_prod_map_fst x Z).flip.isoIsPullback_hom_snd _ _ hprodbase
  have hmid : finitePairComparison hW w q ≫ prod.map (yoneda.map x) (𝟙 (yoneda.obj Z)) =
      j ≫ finitePairComparison hW w p := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, ← Category.assoc, finitePairComparison_comp_prodFst,
        Category.assoc, finitePairComparison_comp_prodFst]
      exact hj'.w
    · rw [Category.assoc, prod.map_snd, Category.comp_id, finitePairComparison_comp_snd,
        Category.assoc, finitePairComparison_comp_snd, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun t => t ≫ w) hjx.symm
  have hsq : finitePairComparison hW w q ≫ e₂.hom = e₁.hom ≫
      baseChangeOverBase B U hU (finitePairComparison hW w p) (finitePairProjection hW p) prod.fst
        (finitePairComparison_comp_prodFst hW w p) (yoneda.map x) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, he₂fst, Category.assoc]
      simp only [baseChangeOverBase, pullback.lift_fst]
      rw [← Category.assoc, he₁fst, hmid]
    · rw [Category.assoc, he₂snd, Category.assoc]
      simp only [baseChangeOverBase, pullback.lift_snd]
      rw [he₁snd, finitePairComparison_comp_prodFst]
  rw [← isIso_comp_right_iff _ e₂.hom, hsq, isIso_comp_left_iff]

/-- **The comparison of the space of sections with the finite part is an open immersion.** Over
a scheme-valued point of the finite part, the sections of the space of sections are the
morphisms of the site over which the comparison of the named pair with `T × Z` becomes an
isomorphism, and that locus is an open subspace. -/
theorem isOpenImmersion_sectionSpaceToFinitePart (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsOpenImmersion B U hU (sectionSpaceToFinitePart hW hw hZfin) := by
  refine @isOpenImmersion_of_isOpenSubspace_range_preimage B U hU _ _
    (sectionSpaceToFinitePart hW hw hZfin) (mono_sectionSpaceToFinitePart hW hw hZfin) ?_
  set P := finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)
  intro T₀ g
  obtain ⟨V, hV, hVprop⟩ := exists_isOpenSubspace_finitePairComparison_isIso hW hw hZfin
    (P.sections T₀ (g.app (op T₀) (𝟙 T₀)))
  have key : ∀ (T' : BigFppfOver B U hU) (x : T' ⟶ T₀),
      g.app (op T') x ∈ Set.range ((sectionSpaceToFinitePart hW hw hZfin).app (op T')) ↔
        x ∈ V.obj (op T') := by
    intro T' x
    have hq := P.map_isBaseChange x (g.app (op T₀) (𝟙 T₀))
    have h1 : (x ∈ V.obj (op T')) ↔
        IsIso (finitePairComparison hW w
          (P.sections T' (P.toFunctor.map x.op (g.app (op T₀) (𝟙 T₀))))) := by
      rw [mem_subfunctor_iff V x,
        hVprop (yoneda.obj T') (isAlgebraicSpace_yoneda B U hU T') (yoneda.map x)]
      exact (isIso_finitePairComparison_iff hW _ _ x hq).symm
    rw [h1, ← exists_sectionPair_eq_iff hW hw hZfin]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨sectionSpaceEquiv B U hU Z T' W w s,
        (sectionSpaceToFinitePart_sections hW hw hZfin T' s).symm.trans
          (congrArg (P.sections T') (hs.trans (app_eq_map_app_id g x)))⟩
    · rintro ⟨σ, hσ⟩
      refine ⟨(sectionSpaceEquiv B U hU Z T' W w).symm σ, ?_⟩
      have hs := sectionSpaceToFinitePart_sections hW hw hZfin T'
        ((sectionSpaceEquiv B U hU Z T' W w).symm σ)
      rw [Equiv.apply_symm_apply, hσ] at hs
      exact ((P.sections T').injective hs).trans (app_eq_map_app_id g x).symm
  have hEq : (Subfunctor.range (sectionSpaceToFinitePart hW hw hZfin)).preimage g = V :=
    le_antisymm (fun (T' : (BigFppfOver B U hU)ᵒᵖ) x hx => (key T'.unop x).1 hx)
      (fun (T' : (BigFppfOver B U hU)ᵒᵖ) x hx => (key T'.unop x).2 hx)
  rw [hEq]
  exact hV

/-! ### Stacks 05XR for a separated étale `w` -/

/-- The structure morphism of `W` factors through `w`, as any two morphisms to the terminal
presheaf agree. -/
private theorem toTerminalPresheaf_hom_eq (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z) :
    (toTerminalPresheaf B U hU hW).hom = w ≫ terminal.from (yoneda.obj Z) :=
  terminal.hom_ext _ _

/-- The structure morphism `W ⟶ U` is separated when `w` is: the structure morphism of `Z` is
finite, hence separated, and separatedness is stable under composition. -/
private theorem isSeparated_toTerminalPresheaf (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hwsep : IsSeparated B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsSeparated B U hU (toTerminalPresheaf B U hU hW).hom := by
  rw [toTerminalPresheaf_hom_eq hW w]
  exact isSeparated_comp B U hU w _ hwsep
    (isSeparated_of_isFinite B U hU _ (isAlgebraicSpace_yoneda B U hU Z)
      (isAlgebraicSpace_terminal B U hU) (isFinite_terminal_from_yoneda Z hZfin))

/-- The structure morphism `W ⟶ U` is locally of finite type: `w` is étale and the structure
morphism of `Z` is finite. -/
private theorem isLocallyOfFiniteType_toTerminalPresheaf (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsLocallyOfFiniteType B U hU (toTerminalPresheaf B U hU hW).hom := by
  rw [toTerminalPresheaf_hom_eq hW w]
  exact isLocallyOfFiniteType_comp B U hU hW (isAlgebraicSpace_yoneda B U hU Z)
    (isAlgebraicSpace_terminal B U hU) w _
    (isLocallyOfFiniteType_of_isEtale B U hU (isAlgebraicSpace_yoneda B U hU Z) hw)
    (isLocallyOfFiniteType_of_isFinite B U hU (isAlgebraicSpace_yoneda B U hU Z)
      (isAlgebraicSpace_terminal B U hU) (isFinite_terminal_from_yoneda Z hZfin))

/-- **The space of sections of a separated étale `w : W ⟶ h_Z` over a finite `Z ⟶ U` is an
algebraic space.** It receives an open immersion, in particular a representable morphism, into
the finite part of `W ⟶ U`, which is an algebraic space by Stacks 04QH. -/
theorem isAlgebraicSpace_sectionSpace_of_isSeparated (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w) (hwsep : IsSeparated B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) :=
  isAlgebraicSpace_of_relativelyRepresentable B U hU (sectionSpaceToFinitePart hW hw hZfin)
    (isOpenImmersion_sectionSpaceToFinitePart hW hw hZfin).1
    (isAlgebraicSpace_finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)
      (isSeparated_toTerminalPresheaf hW hwsep hZfin)
      (isLocallyOfFiniteType_toTerminalPresheaf hW hw hZfin))

/-- **The space of sections of a separated étale `w : W ⟶ h_Z` over a finite `Z ⟶ U` is étale
over `U`.** Its structure morphism is the comparison with the finite part of `W ⟶ U`, which is
an open immersion, followed by the projection of the finite part to `U`, which is étale by
Stacks 04QH. -/
theorem isEtale_sectionSpace_of_isSeparated (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w) (hwsep : IsSeparated B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU (terminal.from (sectionSpace B U hU Z W w)) := by
  rw [show terminal.from (sectionSpace B U hU Z W w) =
      sectionSpaceToFinitePart hW hw hZfin ≫
        (finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)).baseMap from
    terminal.hom_ext _ _]
  exact isEtale_comp B U hU
    (isEtale_of_isOpenImmersion B U hU (isOpenImmersion_sectionSpaceToFinitePart hW hw hZfin))
    (isEtale_baseMap_finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW)
      (isSeparated_toTerminalPresheaf hW hwsep hZfin)
      (isLocallyOfFiniteType_toTerminalPresheaf hW hw hZfin))

end AlgebraicGeometry.Space

end
