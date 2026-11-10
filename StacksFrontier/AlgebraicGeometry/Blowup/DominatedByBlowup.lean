module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal

/-!
# A proper modification is dominated by an admissible blowup

Let `f : X ⟶ S` be proper and an isomorphism over an open `U ⊆ S`. Then there is a
`U`-admissible blowup `b : S' ⟶ S` which factors as `S' ⟶ X ⟶ S`.

## Main definitions

* `AlgebraicGeometry.CartierBoundaryReduction` is the conclusion of [Stacks, Tag 080Y] used
  here: a `U`-admissible blowup whose exceptional divisor is exactly the boundary.
* `AlgebraicGeometry.StrictTransformOpenImmersion` is the conclusion of [Stacks, Tag 081S]: a
  `U`-admissible blowup along which the strict transform of `X` is an open subscheme.

## Main results

* `AlgebraicGeometry.cartierBoundaryReduction` is [Stacks, Tag 080Y]: on a quasi-compact and
  quasi-separated scheme every quasi-compact open admits such a reduction.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating` is [Stacks, Tag 081T].
* `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_isCompact` is the same conclusion
  under the source's quasi-compactness assumptions, with the boundary reduction supplied.

## Implementation notes

The reduction of [Stacks, Tag 080Y] is proved here: a quasi-compact open of a quasi-compact
quasi-separated scheme is the complement of the vanishing locus of a finite type quasi-coherent
ideal sheaf ([Stacks, Tag 01PH], here
`AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl`), finite type for such a
sheaf is finite presentation of the closed immersion it cuts out
(`Stacks.Flatness.finitePresentation_subschemeι_iff`), and the support of the exceptional ideal
is the inverse image of the support of the centre, because the exceptional ideal is the
inverse-image ideal sheaf.

The remaining cited result, [Stacks, Tag 081S] — the flattening statement putting the strict
transform of `X` inside the blowup as an open subscheme — is not available in this development
and is carried as a hypothesis, in exactly the form the argument consumes.

The source also assumes `S` quasi-compact and quasi-separated and `U` quasi-compact. Those
hypotheses enter its proof only through [Stacks, Tag 080Y] and [Stacks, Tag 081S], so
`AlgebraicGeometry.exists_isAdmissibleBlowup_dominating` drops them: once those two conclusions
are hypotheses the remaining argument uses nothing of them.

The blowup is `AlgebraicGeometry.blowUp` and the strict transform is
`AlgebraicGeometry.strictTransformToBlowUp` of
`StacksFrontier/AlgebraicGeometry/Blowup/Separation.lean`, so that the support lemmas of
`StacksFrontier/AlgebraicGeometry/StrictTransform/Support.lean` apply directly. Admissibility is
`Stacks.Blowup.IsAdmissibleBlowup`, which is phrased against the parallel construction
`Stacks.Blowup.blowUp`; `Stacks.Blowup.isAdmissibleBlowup_iff` passes between the two.

## References

* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### The strict transform covers the blowup over the isomorphism locus -/

/-- Over the open where `f` is an isomorphism, every point of the blowup away from the
exceptional divisor lies on the strict transform of `X`. -/
private theorem mem_range_strictTransformToBlowUp_of_notMem {f : X ⟶ S} (I : S.IdealSheafData)
    {U : S.Opens} [IsIso (f ∣_ U)] (z : blowUp I) (hzU : z ∈ blowUpToBase I ⁻¹ᵁ U)
    (hzE : z ∉ ((exceptionalIdeal I).support : Set (blowUp I))) :
    z ∈ Set.range (strictTransformToBlowUp f I).base := by
  let u : U.toScheme := ⟨blowUpToBase I z, hzU⟩
  let x : (f ⁻¹ᵁ U).toScheme := inv (f ∣_ U) u
  have hx : (f ∣_ U) x = u := by
    change (inv (f ∣_ U) ≫ (f ∣_ U)) u = u
    rw [IsIso.inv_hom_id]
    rfl
  have hfx : f ((f ⁻¹ᵁ U).ι x) = blowUpToBase I z := by
    have hrestr := congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ S ↦ g x) (morphismRestrict_ι f U)
    change U.ι ((f ∣_ U) x) = f ((f ⁻¹ᵁ U).ι x) at hrestr
    rw [← hrestr, hx]
    rfl
  obtain ⟨y, -, hyz⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := blowUpToBase I)
      ((f ⁻¹ᵁ U).ι x) z hfx
  have hyE : y ∉ Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I)
      (exceptionalIdeal I) := by
    change (pullback.snd f (blowUpToBase I)).base y ∉
      ((exceptionalIdeal I).support : Set (blowUp I))
    rw [hyz]
    exact hzE
  obtain ⟨t, ht⟩ :
      y ∈ Set.range (Stacks.StrictTransform.ideal f (blowUpToBase I)
        (exceptionalIdeal I)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Stacks.StrictTransform.mem_support_ideal_of_notMem_exceptionalPreimage f
      (blowUpToBase I) (exceptionalIdeal I) hyE
  exact ⟨t, by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ht] using hyz⟩

/-! ### Density of the complement of an effective Cartier divisor -/

/-- The complement of an effective Cartier divisor is topologically dense: it is
scheme-theoretically dense and its inclusion is affine, hence dominant. -/
private theorem dense_compl_support_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Dense (D.support.compl : Set Y) := by
  have : IsAffineHom (Scheme.Opens.ι D.support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι D.support.compl) :=
    (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      D.support.compl).mp
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
  have hdense := (Scheme.Opens.ι D.support.compl).denseRange
  rwa [DenseRange, Scheme.Opens.range_ι] at hdense

/-- If `c ≫ b = b'` and `z` lies over `U` along `b'`, then `c z` lies over `U` along `b`. -/
private theorem mem_preimage_of_comp_eq {A B C : Scheme.{u}} {U : C.Opens} {c : A ⟶ B}
    {b : B ⟶ C} {b' : A ⟶ C} (h : c ≫ b = b') {z : A} (hz : z ∈ b' ⁻¹ᵁ U) :
    c z ∈ b ⁻¹ᵁ U := by
  subst h
  exact hz

/-- If an open is the complement of an effective Cartier divisor, its inverse image under any
admissible blowup is dense: that inverse image contains the complement of the pulled-back
divisor, which is dense. -/
private theorem dense_preimage_of_isAdmissibleBlowup {Y Y' : Scheme.{u}} (U : Y.Opens)
    (g : Y' ⟶ Y) (hg : Stacks.Blowup.IsAdmissibleBlowup U g) (D : Y.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hU : (D.support.compl : Set Y) = (U : Set Y)) :
    Dense ((g ⁻¹ᵁ U : Y'.Opens) : Set Y') := by
  obtain ⟨K, -, -, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff U g).mp hg
  set p : blowUp K ⟶ Y := blowUpToBase K with hp
  have hD' : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap p) :=
    isPullbackDefined_blowUpToBase K D hD
  have hinv : e.inv ≫ g = p := by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have himage : e.inv '' ((D.comap p).support.compl : Set (blowUp K)) ⊆
      ((g ⁻¹ᵁ U : Y'.Opens) : Set Y') := by
    rintro _ ⟨y, hy, rfl⟩
    have hyD : p y ∉ D.support := by simpa using hy
    have hyU : p y ∈ U := by
      have : p y ∈ (D.support.compl : Set Y) := by simpa using hyD
      rwa [hU] at this
    exact mem_preimage_of_comp_eq hinv (U := U) hyU
  refine Dense.mono himage ?_
  exact e.inv.denseRange.dense_image e.inv.continuous
    (dense_compl_support_of_isEffectiveCartierDivisor _ hD')

/-! ### The two cited inputs -/

/-- The conclusion of [Stacks, Tag 080Y] used below: a `U`-admissible blowup of `S` whose
exceptional divisor is exactly the complement of the inverse image of `U`. -/
public def CartierBoundaryReduction (S : Scheme.{u}) (U : S.Opens) : Prop :=
  ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
    Disjoint (U : Set S) (I.support : Set S) ∧
      ((exceptionalIdeal I).support : Set (blowUp I)) =
        ((blowUpToBase I ⁻¹ᵁ U : (blowUp I).Opens) : Set (blowUp I))ᶜ

/-- **Stacks Project, Tag 080Y.** On a quasi-compact and quasi-separated scheme `S`, a
quasi-compact open `U` becomes the complement of an effective Cartier divisor after a single
`U`-admissible blowup: a finite type quasi-coherent ideal sheaf `I` cutting out `S ∖ U` is
finitely presented as a closed subscheme, is disjoint from `U`, and the exceptional divisor of
the blowup of `S` in `I` is exactly the complement of the inverse image of `U`. -/
@[stacks 080Y]
public theorem cartierBoundaryReduction [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens)
    (hU : IsCompact (U : Set S)) : CartierBoundaryReduction S U := by
  obtain ⟨I, hIft, hIsupp⟩ := exists_isFiniteType_idealSheafData_support_eq_compl U hU
  refine ⟨I, (Stacks.Flatness.finitePresentation_subschemeι_iff I).mpr hIft, ?_, ?_⟩
  · rw [hIsupp]
    exact disjoint_compl_right
  · have hcomap : ((exceptionalIdeal I).support : Set (blowUp I)) =
        (blowUpToBase I).base ⁻¹' (I.support : Set S) := by
      change ((I.comap (blowUpToBase I)).support : Set (blowUp I)) = _
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    rw [hcomap, hIsupp, Set.preimage_compl, Scheme.Hom.coe_preimage]

/-- The conclusion of [Stacks, Tag 081S]: a `U`-admissible blowup of `S` along which the strict
transform of `X` is an open subscheme of the blowup. -/
public def StrictTransformOpenImmersion (f : X ⟶ S) (U : S.Opens) : Prop :=
  ∃ J : S.IdealSheafData, FinitePresentation J.subschemeι ∧
    Disjoint (U : Set S) (J.support : Set S) ∧
      IsOpenImmersion (strictTransformToBlowUp f J)

/-! ### Tag 081T -/

/-- **Stacks Project, Tag 081T.** A proper morphism `f : X ⟶ S` which is an isomorphism over an
open `U ⊆ S` is dominated by a `U`-admissible blowup: there are a `U`-admissible blowup
`b : S' ⟶ S` and a morphism `g : S' ⟶ X` with `g ≫ f = b`. -/
@[stacks 081T "conditional on cited 080Y and 081S, carried as hypotheses; qc/qs dropped"]
public theorem exists_isAdmissibleBlowup_dominating (f : X ⟶ S) [IsProper f] (U : S.Opens)
    [IsIso (f ∣_ U)] (h080Y : CartierBoundaryReduction S U)
    (h081S : StrictTransformOpenImmersion f U) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ g : S' ⟶ X, g ≫ f = b := by
  classical
  obtain ⟨I, hI, hIU, hIboundary⟩ := h080Y
  obtain ⟨J, hJ, hJU, hJopen⟩ := h081S
  set b₁ : blowUp I ⟶ S := blowUpToBase I with hb₁
  set b₂ : blowUp J ⟶ S := blowUpToBase J with hb₂
  -- One admissible blowup dominating both, by Stacks tag 080N.
  let Y : Bool → Scheme.{u} := fun
    | false => blowUp I
    | true => blowUp J
  let q : ∀ i : Bool, Y i ⟶ S := fun
    | false => b₁
    | true => b₂
  obtain ⟨S₃, b₃, hb₃, c, hc, hcAdm⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_dominating U Y q
      (by
        intro i
        cases i
        · exact (Stacks.Blowup.isAdmissibleBlowup_iff U b₁).mpr
            ⟨I, hI, hIU, Iso.refl _, Category.id_comp _⟩
        · exact (Stacks.Blowup.isAdmissibleBlowup_iff U b₂).mpr
            ⟨J, hJ, hJU, Iso.refl _, Category.id_comp _⟩)
  set c₁ : S₃ ⟶ blowUp I := c false with hc₁def
  set c₂ : S₃ ⟶ blowUp J := c true with hc₂def
  have hc₁ : c₁ ≫ b₁ = b₃ := hc false
  have hc₂ : c₂ ≫ b₂ = b₃ := hc true
  -- Upstairs the inverse image of `U` is dense, because on `blowUp I` it is the complement of
  -- an effective Cartier divisor.
  have hdense₃ : Dense ((b₃ ⁻¹ᵁ U : S₃.Opens) : Set S₃) := by
    have hU₁ : (((exceptionalIdeal I).support.compl : (blowUp I).Opens) : Set (blowUp I)) =
        ((b₁ ⁻¹ᵁ U : (blowUp I).Opens) : Set (blowUp I)) := by
      rw [show (((exceptionalIdeal I).support.compl : (blowUp I).Opens) : Set (blowUp I)) =
        ((exceptionalIdeal I).support : Set (blowUp I))ᶜ from rfl, hIboundary, compl_compl]
    have h := dense_preimage_of_isAdmissibleBlowup (b₁ ⁻¹ᵁ U) c₁ (hcAdm false)
      (exceptionalIdeal I)
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) hU₁
    rwa [← Scheme.Hom.comp_preimage, hc₁] at h
  -- The strict transform of `X` in `blowUp J` is proper, hence has closed range, and it covers
  -- `b₂⁻¹(U)`: it covers everything off the exceptional divisor, whose complement is dense.
  have : IsProper (Stacks.StrictTransform.ideal f b₂ (exceptionalIdeal J)).subschemeι :=
    inferInstance
  have : IsProper (strictTransformToBlowUp f J) := inferInstance
  have hopen₂ : IsOpenImmersion (strictTransformToBlowUp f J) := hJopen
  have hrange₂ : ((b₂ ⁻¹ᵁ U : (blowUp J).Opens) : Set (blowUp J)) ⊆
      Set.range (strictTransformToBlowUp f J).base := by
    intro z hz
    by_contra hzr
    have hopen : IsOpen ((Set.range (strictTransformToBlowUp f J).base)ᶜ ∩
        ((b₂ ⁻¹ᵁ U : (blowUp J).Opens) : Set (blowUp J))) :=
      ((strictTransformToBlowUp f J).isClosedMap.isClosed_range).isOpen_compl.inter
        (b₂ ⁻¹ᵁ U).2
    obtain ⟨w, hw, hwE⟩ :=
      (dense_compl_support_of_isEffectiveCartierDivisor _
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal
          J)).inter_open_nonempty _ hopen ⟨z, hzr, hz⟩
    exact hw.1 (mem_range_strictTransformToBlowUp_of_notMem J w hw.2 hwE)
  -- Pull the strict transform back to `S₃`: an open immersion with closed dense range, hence an
  -- isomorphism.
  set j₃ : pullback (strictTransformToBlowUp f J) c₂ ⟶ S₃ :=
    pullback.snd (strictTransformToBlowUp f J) c₂ with hj₃
  have : IsOpenImmersion j₃ := inferInstance
  have : IsProper j₃ := inferInstance
  have hrange₃ : ((b₃ ⁻¹ᵁ U : S₃.Opens) : Set S₃) ⊆ Set.range j₃.base := by
    intro z hz
    obtain ⟨t, ht⟩ := hrange₂ (mem_preimage_of_comp_eq hc₂ hz)
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := strictTransformToBlowUp f J) (g := c₂) t z ht
    exact ⟨w, hw⟩
  have hsurj₃ : Function.Surjective j₃.base := by
    rw [← Set.range_eq_univ, ← j₃.isClosedMap.isClosed_range.closure_eq]
    exact (hdense₃.mono hrange₃).closure_eq
  have : IsIso j₃ := isIso_of_isOpenImmersion_of_opensRange_eq_top j₃
    (by ext z; exact ⟨fun _ ↦ trivial, fun _ ↦ hsurj₃ z⟩)
  -- Assemble the factorization.
  set k₂ : Stacks.StrictTransform.scheme f b₂ (exceptionalIdeal J) ⟶ X :=
    (Stacks.StrictTransform.ideal f b₂ (exceptionalIdeal J)).subschemeι ≫
      pullback.fst f b₂ with hk₂d
  have hk₂ : k₂ ≫ f = strictTransformToBlowUp f J ≫ b₂ := by
    rw [hk₂d, strictTransformToBlowUp, Category.assoc, Category.assoc]
    exact congrArg
      (fun r ↦ (Stacks.StrictTransform.ideal f b₂ (exceptionalIdeal J)).subschemeι ≫ r)
      pullback.condition
  refine ⟨S₃, b₃, hb₃,
    (asIso j₃).inv ≫ pullback.fst (strictTransformToBlowUp f J) c₂ ≫ k₂, ?_⟩
  have hk₃ : (pullback.fst (strictTransformToBlowUp f J) c₂ ≫ k₂) ≫ f = j₃ ≫ b₃ := by
    rw [Category.assoc, hk₂, ← Category.assoc, pullback.condition, Category.assoc, hc₂]
  rw [Category.assoc, hk₃, ← Category.assoc]
  simp

/-- A proper morphism `f : X ⟶ S` over a quasi-compact and quasi-separated scheme which is an
isomorphism over a quasi-compact open `U ⊆ S` is dominated by a `U`-admissible blowup, granted
the strict transform of `X` is an open subscheme of some `U`-admissible blowup. Here the
boundary reduction is no longer a hypothesis: it is
`AlgebraicGeometry.cartierBoundaryReduction`. -/
public theorem exists_isAdmissibleBlowup_dominating_of_isCompact (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) [IsIso (f ∣_ U)]
    (hU : IsCompact (U : Set S)) (h081S : StrictTransformOpenImmersion f U) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ g : S' ⟶ X, g ≫ f = b :=
  exists_isAdmissibleBlowup_dominating f U (cartierBoundaryReduction U hU) h081S

end AlgebraicGeometry

end
