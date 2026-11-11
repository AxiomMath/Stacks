module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAgreementQuotientRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatImageOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianImmersionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap

/-!
# The quotient of an étale space by the agreement relation of a morphism

Let `π : E ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` and `ψ : E ⟶ Y` a
morphism into an fppf sheaf. Let `K ⊆ E ×_X E` be the largest open subspace on which
`ψ ∘ pr₁ = ψ ∘ pr₂` (`AlgebraicGeometry.Space.etaleAgreementLocus`); it is an equivalence
relation on `E` over `X` (`AlgebraicGeometry.Space.isEquivalenceRelation_etaleAgreementPreRelation`)
whose inclusion into `E ×_X E` is an open immersion. By Stacks 0DU1 the quotient sheaf
`X' = E/K` is an algebraic space étale over `X`. The quotient map `ε : E ⟶ X'` is étale and
surjective, `ψ` descends to `χ : X' ⟶ Y`, and two points of `E` with the same image in `X`
whose pair lies in `K` have the same image in `X'`. If `π` is quasi-compact so is `X' ⟶ X`;
if moreover `X` is locally Noetherian, `X' ⟶ X` is quasi-separated, its diagonal being, after
the fppf base change `E ×_X E ⟶ X' ×_X X'`, the open immersion `K ⟶ E ×_X E` into a locally
Noetherian space.

## Main results

* `AlgebraicGeometry.Space.exists_isEtale_quotient_etaleAgreementLocus`: the quotient, packaged
  as an existence statement.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isPullback_of_isQuasiCompact`: a morphism
  `q : X' ⟶ X` is quasi-separated when an fppf covering `ε : E ⟶ X'` has a quasi-compact
  relation `E ×_{X'} E ⟶ E ×_X E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasSheafify_bigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Quasi-separatedness from the relation -/

section QuasiSeparated

/-- Surjective flat morphisms locally of finite presentation compose. -/
private instance surjectiveFlatLfp_isStableUnderComposition :
    (surjectiveFlatLfp B S hS).IsStableUnderComposition :=
  { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
      ⟨isSurjective_comp B S hS hu.1 hv.1,
        isFlat_comp B S hS A₁.property A₂.property A₃.property u.hom v.hom hu.2.1 hv.2.1,
        isLocallyOfFinitePresentation_comp B S hS A₁.property A₂.property A₃.property
          u.hom v.hom hu.2.2 hv.2.2⟩ }

/-- A quasi-compact morphism composed with an isomorphism is quasi-compact. -/
private theorem isQuasiCompact_comp_isIso {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (e : G ⟶ G') [IsIso e] (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (f ≫ e) :=
  isQuasiCompact_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := 𝟙 F) (snd := f ≫ e) (f := f) (g := inv e) ⟨by simp⟩) hf

/-- **Quasi-separatedness from a quasi-compact relation.** Let `ε : E ⟶ X'` be surjective, flat
and locally of finite presentation, `q : X' ⟶ X`, and let `s, t : R ⟶ E` exhibit `R` as
`E ×_{X'} E`. If the induced `j : R ⟶ E ×_X E` is quasi-compact, then `q` is quasi-separated: the
diagonal of `q` becomes `R ⟶ E ×_X E` after the fppf base change `E ×_X E ⟶ X' ×_X X'`, and
quasi-compactness is fppf local on the target (Stacks 041L). -/
theorem isQuasiSeparated_of_isPullback_of_isQuasiCompact
    {R E X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R)
    (hE : IsAlgebraicSpace B S hS E) (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) {ε : E ⟶ X'} {q : X' ⟶ X} {s t : R ⟶ E}
    (hst : IsPullback s t ε ε) (hεs : IsSurjective B S hS ε) (hεf : IsFlat B S hS ε)
    (hεl : IsLocallyOfFinitePresentation B S hS ε)
    {π : E ⟶ X} (hεq : ε ≫ q = π) (j : R ⟶ pullback π π)
    (hj₁ : j ≫ pullback.fst π π = s) (hj₂ : j ≫ pullback.snd π π = t)
    (hj : IsQuasiCompact B S hS j) :
    IsQuasiSeparated B S hS q := by
  subst hεq
  have := isQuasiCompact_isLocalAtTarget_fppf.{u, 0} B S hS
  let Rs : AlgebraicSpaces B S hS := ⟨R, hR⟩
  let Es : AlgebraicSpaces B S hS := ⟨E, hE⟩
  let X's : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let εs : Es ⟶ X's := ObjectProperty.homMk ε
  let qs : X's ⟶ Xs := ObjectProperty.homMk q
  have hPq : IsAlgebraicSpace B S hS (pullback (ε ≫ q) (ε ≫ q)) :=
    isAlgebraicSpace_pullback B S hS _ _ hE hE hX
  let Ps : AlgebraicSpaces B S hS := ⟨pullback (ε ≫ q) (ε ≫ q), hPq⟩
  have hr : IsPullback (ObjectProperty.homMk s : Rs ⟶ Es) (ObjectProperty.homMk t : Rs ⟶ Es)
      εs εs :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hst.w) hst
  have hp : IsPullback (ObjectProperty.homMk (pullback.fst (ε ≫ q) (ε ≫ q)) : Ps ⟶ Es)
      (ObjectProperty.homMk (pullback.snd (ε ≫ q) (ε ≫ q)) : Ps ⟶ Es) (εs ≫ qs) (εs ≫ qs) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ pullback.condition)
      (IsPullback.of_hasPullback (ε ≫ q) (ε ≫ q))
  let js : Rs ⟶ Ps := ObjectProperty.homMk j
  have hcomm : js ≫ hp.isoPullback.hom =
      hr.isoPullback.hom ≫ pullback.map εs εs (εs ≫ qs) (εs ≫ qs) (𝟙 Es) (𝟙 Es) qs
        (Category.id_comp _).symm (Category.id_comp _).symm := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
        Category.comp_id]
      exact ObjectProperty.hom_ext _ hj₁
    · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd,
        Category.comp_id]
      exact ObjectProperty.hom_ext _ hj₂
  have hjs : quasiCompactProperty B S hS js := hj
  have hmap : quasiCompactProperty B S hS
      (pullback.map εs εs (εs ≫ qs) (εs ≫ qs) (𝟙 Es) (𝟙 Es) qs
        (Category.id_comp _).symm (Category.id_comp _).symm) := by
    have h₁ : quasiCompactProperty B S hS (js ≫ hp.isoPullback.hom) :=
      MorphismProperty.RespectsIso.postcomp _ hp.isoPullback.hom js hjs
    rw [hcomm] at h₁
    exact ((quasiCompactProperty B S hS).cancel_left_of_respectsIso hr.isoPullback.hom _).mp h₁
  have hM : surjectiveFlatLfp B S hS
      (pullback.map (εs ≫ qs) (εs ≫ qs) qs qs εs εs (𝟙 Xs) (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (f := εs ≫ qs) (g := εs ≫ qs) (f' := qs) (g' := qs)
      (i₁ := εs) (i₂ := εs) ⟨hεs, hεf, hεl⟩ ⟨hεs, hεf, hεl⟩ rfl rfl
  have hd : quasiCompactProperty B S hS (pullback.diagonal qs) :=
    prop_of_isPullback_of_fppf.{u, 0} B S hS (quasiCompactProperty B S hS)
      (pullback_map_diagonal_isPullback εs εs qs) hM.1 hM.2.1 hM.2.2 hmap
  -- Transport from the chosen fibre product of algebraic spaces to the presheaf one.
  have hsq : IsPullback (pullback.fst qs qs).hom (pullback.snd qs qs).hom qs.hom qs.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback qs qs)
  have hdiageq : (pullback.diagonal qs).hom ≫ hsq.isoPullback.hom = pullback.diagonal qs.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.diagonal_fst]
      exact congrArg (fun m : X's ⟶ X's => m.hom) (pullback.diagonal_fst qs)
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.diagonal_snd]
      exact congrArg (fun m : X's ⟶ X's => m.hom) (pullback.diagonal_snd qs)
  change IsQuasiCompact B S hS (pullback.diagonal qs.hom)
  rw [← hdiageq]
  exact isQuasiCompact_comp_isIso _ hd

end QuasiSeparated

/-! ### The quotient -/

section Quotient

variable {E X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The groupoid in algebraic spaces over `X` of the agreement relation
`AlgebraicGeometry.Space.etaleAgreementPreRelation`, by Stacks 043Y. -/
abbrev etaleAgreementGroupoid (hE : IsAlgebraicSpace B S hS E) (hX : IsAlgebraicSpace B S hS X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {π : E ⟶ X}
    (hπ : IsEtale B S hS π) (ψ : E ⟶ Y) : GroupoidInAlgebraicSpaces B S hS ⟨X, hX⟩ :=
  @groupoidOfIsEquivalenceRelation _ _ _ _ ⟨E, hE⟩
    ⟨(etaleAgreementLocus π ψ).toFunctor,
      (isOpenSubspace_agreementOpenSubspace (isAlgebraicSpace_pullback B S hS π π hE hE hX) _ _).1⟩
    (ObjectProperty.homMk π)
    (ObjectProperty.homMk ((etaleAgreementLocus π ψ).ι ≫ pullback.fst π π ≫ π))
    (etaleAgreementPreRelation π ψ)
    (isEquivalenceRelation_etaleAgreementPreRelation hE hX hY hπ ψ)

/-- The pre-relation of the agreement groupoid is the agreement relation. -/
theorem groupoidPreRelation_etaleAgreementGroupoid (hE : IsAlgebraicSpace B S hS E)
    (hX : IsAlgebraicSpace B S hS X) (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {π : E ⟶ X} (hπ : IsEtale B S hS π) (ψ : E ⟶ Y) :
    groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ) =
      etaleAgreementPreRelation π ψ := by
  apply prod.hom_ext
  · ext1
    simp only [groupoidPreRelation, prod.lift_fst, Over.homMk_left]
    rfl
  · ext1
    simp only [groupoidPreRelation, prod.lift_snd, Over.homMk_left]
    rfl

/-- **The quotient of an étale space by the agreement relation of a morphism.** Let
`π : E ⟶ X` be an étale, quasi-compact morphism of algebraic spaces over `S`, with `X` locally
Noetherian, and let `ψ : E ⟶ Y` be a morphism into an fppf sheaf. Let `K ⊆ E ×_X E` be the
largest open subspace on which `ψ ∘ pr₁ = ψ ∘ pr₂`. There are an algebraic space `X'`, an étale
surjection `ε : E ⟶ X'`, an étale, quasi-compact, quasi-separated `q : X' ⟶ X` with
`ε ≫ q = π` and a morphism `χ : X' ⟶ Y` with `ε ≫ χ = ψ`, such that two morphisms
`a, b : T ⟶ E` with `a ≫ π = b ≫ π` whose pair factors through `K` satisfy
`a ≫ ε = b ≫ ε`.

`X'` is the quotient sheaf `E/K`, an algebraic space étale over `X` by Stacks 0DU1. -/
theorem exists_isEtale_quotient_etaleAgreementLocus (hE : IsAlgebraicSpace B S hS E)
    (hX : IsAlgebraicSpace B S hS X)
    (hXn : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {π : E ⟶ X}
    (hπ : IsEtale B S hS π) (hπqc : IsQuasiCompact B S hS π) (ψ : E ⟶ Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X')
      (ε : E ⟶ X') (q : X' ⟶ X) (χ : X' ⟶ Y),
      ε ≫ q = π ∧ ε ≫ χ = ψ ∧ IsEtale B S hS ε ∧ IsSurjective B S hS ε ∧
      IsEtale B S hS q ∧ IsQuasiCompact B S hS q ∧ IsQuasiSeparated B S hS q ∧
      ∀ {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ E) (h : a ≫ π = b ≫ π),
        Subfunctor.range (pullback.lift a b h) ≤ etaleAgreementLocus π ψ →
          a ≫ ε = b ≫ ε := by
  have hP : IsAlgebraicSpace B S hS (pullback π π) := isAlgebraicSpace_pullback B S hS π π hE hE hX
  have hK : IsOpenSubspace B S hS (etaleAgreementLocus π ψ) :=
    isOpenSubspace_agreementOpenSubspace hP _ _
  have hagree := etaleAgreementLocus_ι_comp_eq hY π ψ
  have hjG := groupoidPreRelation_etaleAgreementGroupoid hE hX hY hπ ψ
  have hrel : CategoryTheory.IsEquivalenceRelation
      (groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ)).target
      (groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ)).source := by
    rw [hjG]
    exact isEquivalenceRelation_etaleAgreementPreRelation hE hX hY hπ ψ
  have htarget : (groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ)).target.left =
      (etaleAgreementLocus π ψ).ι ≫ pullback.fst π π := by
    rw [hjG]
    exact etaleAgreementPreRelation_target_left π ψ
  have hsource : (groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ)).source.left =
      (etaleAgreementLocus π ψ).ι ≫ pullback.snd π π := by
    rw [hjG]
    exact etaleAgreementPreRelation_source_left π ψ
  have hflat : IsFlat B S hS (etaleAgreementGroupoid hE hX hY hπ ψ).objectsToBase.hom :=
    isFlat_of_isEtale B S hS hπ
  have hlfp : IsLocallyOfFinitePresentation B S hS
      (etaleAgreementGroupoid hE hX hY hπ ψ).objectsToBase.hom :=
    isLocallyOfFinitePresentation_of_isEtale B S hS hπ
  have hopen : IsOpenImmersion B S hS
      (groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ)).left := by
    rw [hjG, etaleAgreementPreRelation_left]
    exact isOpenImmersion_comp B S hS _ _ hK.2
      (isOpenImmersion_of_isIso B S hS (isPullback_prod_mk_left π).isoPullback.inv)
  -- Clean names for the quotient and its maps.
  let jG := groupoidPreRelation (etaleAgreementGroupoid hE hX hY hπ ψ)
  let Q := (quotientSheaf jG).obj
  let ε : E ⟶ Q := toQuotientSheaf jG
  let q : Q ⟶ X := (quotientSheafToBase hX.isSheaf jG).hom
  let tK : (etaleAgreementLocus π ψ).toFunctor ⟶ E := jG.target.left
  let sK : (etaleAgreementLocus π ψ).toFunctor ⟶ E := jG.source.left
  have ht : tK = (etaleAgreementLocus π ψ).ι ≫ pullback.fst π π := htarget
  have hs : sK = (etaleAgreementLocus π ψ).ι ≫ pullback.snd π π := hsource
  have hX' : IsAlgebraicSpace B S hS Q :=
    isAlgebraicSpace_quotientSheaf_of_isOpenImmersion hflat hlfp hopen
  have hq : IsEtale B S hS q := isEtale_quotientSheafToBase_of_isOpenImmersion hflat hlfp hopen
  have hεq : ε ≫ q = π := toQuotientSheaf_quotientSheafToBase hX.isSheaf jG
  have hts : tK ≫ ε = sK ≫ ε := target_toQuotientSheaf_eq_source jG
  have hdesc' : tK ≫ ψ = sK ≫ ψ := by
    rw [ht, hs]
    simpa only [Category.assoc] using hagree
  let χ : Q ⟶ Y := (quotientSheafDesc jG ⟨Y, hY⟩ ψ hdesc').hom
  have hεχ : ε ≫ χ = ψ := toQuotientSheaf_quotientSheafDesc jG ⟨Y, hY⟩ ψ hdesc'
  have hε : IsEtale B S hS ε := isEtale_of_isEtale_over B S hS hE hX' hX ε π q hπ hq hεq
  have hεs : IsSurjective B S hS ε := isSurjective_toQuotientSheaf jG
  have hqc : IsQuasiCompact B S hS q :=
    isQuasiCompact_of_comp_surjective B S hS hE hX' hX ε π q hεq.symm hεs hπqc
  -- Quasi-separatedness: the relation `K ⟶ E ×_X E` is quasi-compact.
  have hKqc : IsQuasiCompact B S hS (etaleAgreementLocus π ψ).ι := by
    obtain ⟨V, φ, hφs, hφe, hV⟩ := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hP hX
      (pullback.fst π π ≫ π) (isLocallyOfFiniteType_of_isEtale B S hS hX
        (isEtale_comp B S hS (isEtale_pullback_fst B S hS hE hX hE π π hπ) hπ)) hXn
    refine isQuasiCompact_of_surjectiveEtale_atlas B S hS _ hK.1 hP V φ
      ((presheafSurjective_iff_isSurjective_yoneda B S hS _ hP V φ).mp hφs)
      (isEtale_of_presheaf_etale B S hS hφe) ?_
    refine isQuasiCompact_of_isImmersion_yoneda B S hS (isImmersion_of_isOpenImmersion B S hS ?_) hV
    exact (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (IsPullback.of_hasPullback (etaleAgreementLocus π ψ).ι φ) hK.2
  have hpb : IsPullback sK tK ε ε := isPullback_toQuotientSheaf jG hrel
    (etaleAgreementGroupoid hE hX hY hπ ψ).arrows.property.isSheaf hE.isSheaf
  have hqs : IsQuasiSeparated B S hS q := by
    refine isQuasiSeparated_of_isPullback_of_isQuasiCompact hK.1 hE hX' hX hpb hεs
      (isFlat_of_isEtale B S hS hε) (isLocallyOfFinitePresentation_of_isEtale B S hS hε) hεq
      ((etaleAgreementLocus π ψ).ι ≫ (pullbackSymmetry π π).hom) ?_ ?_
      (isQuasiCompact_comp_isIso _ hKqc)
    · rw [hs, Category.assoc, pullbackSymmetry_hom_comp_fst]
    · rw [ht, Category.assoc, pullbackSymmetry_hom_comp_snd]
  refine ⟨Q, hX', ε, q, χ, hεq, hεχ, hε, hεs, hq, hqc, hqs, ?_⟩
  intro T a b h hab
  have hk : Subfunctor.lift _ hab ≫ (etaleAgreementLocus π ψ).ι = pullback.lift a b h :=
    Subfunctor.lift_ι _ _
  have ha : a = Subfunctor.lift _ hab ≫ tK := by
    rw [ht, reassoc_of% hk]
    exact (pullback.lift_fst _ _ _).symm
  have hb : b = Subfunctor.lift _ hab ≫ sK := by
    rw [hs, reassoc_of% hk]
    exact (pullback.lift_snd _ _ _).symm
  calc a ≫ ε = Subfunctor.lift _ hab ≫ tK ≫ ε := by rw [← Category.assoc, ← ha]
    _ = Subfunctor.lift _ hab ≫ sK ≫ ε := by rw [hts]
    _ = b ≫ ε := by rw [← Category.assoc, ← hb]

end Quotient

end AlgebraicGeometry.Space

end
