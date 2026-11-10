module

public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationQuasicoherentCode
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparatedFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.BlowupEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedFieldBase

public import StacksFrontier.AlgebraicGeometry.Size.Basic
/-!
# Axiom [-1] for `Coh_{X/Y}`

Let `f : X ⟶ Y` be a separated morphism of finite presentation of algebraic spaces over `S`. For
a test scheme `T` over `Y` with affine underlying scheme, the base change `X_T` is quasi-compact
and separated over `T`, so it has a presentation by an affine scheme `U` étale over it whose
relation scheme `R = U ×_{X_T} U` is again affine; both are of finite type over `T`, so their
sizes are bounded by that of `T`. The finitely presented quasi-coherent modules on `X_T` thus have
at most `size T` isomorphism classes.
-/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Space.C1573

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

/-- **An injection up to isomorphism bounds the number of isomorphism classes.** -/
theorem Cardinal.mk_quotient_isIsomorphic_le {C : Type (u + 1)} [Category.{u + 1} C]
    {ι : Type (u + 1)} (f : C → ι) (hf : ∀ a b, f a = f b → Nonempty (a ≅ b)) :
    #(Quotient (isIsomorphicSetoid C)) ≤ #ι := by
  refine mk_le_of_injective (f := fun q => f q.out) fun q q' h => ?_
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound (hf _ _ h)

/-- **An injection up to isomorphism bounds the number of isomorphism classes.** -/
theorem Cardinal.lift_mk_quotient_isIsomorphic_le {C : Type*} [Category* C] {ι : Type*}
    (f : C → ι) (hf : ∀ a b, f a = f b → Nonempty (a ≅ b)) :
    Nonempty (Quotient (isIsomorphicSetoid C) ↪ ι) := by
  refine ⟨⟨fun q => f q.out, fun q q' h => ?_⟩⟩
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound (hf _ _ h)

/-- **Morphisms from the spectrum of a field `K` to a scheme `X` are at most
`2 ^ size X * #K ^ size X`**: such a morphism is a point of `X` together with an embedding of its
residue field into `K`. -/
theorem AlgebraicGeometry.Scheme.mk_hom_spec_field_le (K : Type u) [Field K] (X : Scheme.{u}) :
    #(Spec (.of K) ⟶ X) ≤ 2 ^ X.size * #K ^ X.size := by
  rw [mk_congr (Scheme.SpecToEquivOfField K X), mk_sigma]
  calc sum (fun x : X => #(X.residueField x ⟶ CommRingCat.of K))
      ≤ sum (fun _ : X => #K ^ X.size) := sum_le_sum _ _ fun x => by
        calc #(X.residueField x ⟶ CommRingCat.of K) ≤ #(X.residueField x → K) :=
              mk_le_of_injective (f := fun g => ⇑(g.hom)) fun g g' h =>
                CommRingCat.hom_ext (RingHom.ext (congrFun h))
          _ = #K ^ #(X.residueField x) := by simp
          _ ≤ #K ^ X.size := power_le_power_left (mk_ne_zero K) (Scheme.residueField_size_le X x)
    _ = #X * #K ^ X.size := sum_const' _ _
    _ ≤ 2 ^ X.size * #K ^ X.size := by
      gcongr
      exact Scheme.mk_le_two_pow_size X

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  preservesLimitsOfShape_walkingCospan_toScheme

/-- **The relation of an affine chart of a space separated over an affine scheme is affine.** -/
theorem exists_isAffine_selfPullback_of_isSeparated_to_affine
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f) (φ : yoneda.obj T ⟶ X) :
    ∃ (Q : BigFppfOver B S hS) (_ : pullback φ φ ≅ yoneda.obj Q),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Q) := by
  have _ := hY₀
  have _ := hT
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨t, ht⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (φ ≫ f)
  have sq1 := Stacks.Spaces.isPullback_selfPullback_diagonal f φ ht.symm
  set isoP := PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) t t
  have hgc : (pullback.fst (yoneda.map t) (yoneda.map t) ≫ φ) ≫ f =
      (pullback.snd (yoneda.map t) (yoneda.map t) ≫ φ) ≫ f := by
    rw [Category.assoc, Category.assoc, ← ht, pullback.condition]
  set g : yoneda.obj (pullback t t) ⟶ pullback f f :=
    isoP.hom ≫ pullback.lift (pullback.fst (yoneda.map t) (yoneda.map t) ≫ φ)
      (pullback.snd (yoneda.map t) (yoneda.map t) ≫ φ) hgc with hg
  have sq2 : IsPullback (pullback.fst φ φ ≫ φ)
      (pullback.lift (pullback.fst φ φ) (pullback.snd φ φ)
        (by rw [ht, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ isoP.inv)
      (pullback.diagonal f) g :=
    Stacks.Spaces.isPullback_of_iso_right (by simpa [hg] using sq1)
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g)) := hf.property_snd g
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback t t)) :=
    IsAffine.of_isPullback ((IsPullback.of_hasPullback t t).map (BigFppfOver.toScheme B S hS))
  have hQaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.rep.pullback g)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g))
  exact ⟨hf.rep.pullback g, sq2.isoIsPullback _ _ (hf.rep.isPullback g), hQaff⟩

/-- A morphism from a representable presheaf to a representable presheaf which is locally of finite
type, read on the underlying schemes, bounds the size of an affine source by that of the target. -/
theorem size_le_of_isLocallyOfFiniteType_yoneda {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (k : yoneda.obj U ⟶ yoneda.obj V)
    (hk : IsLocallyOfFiniteType B S hS k) :
    ((BigFppfOver.toScheme B S hS).obj U).size ≤ ((BigFppfOver.toScheme B S hS).obj V).size := by
  obtain ⟨g, rfl⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective k
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 hk
  exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g)

/-- The ring of functions on the identity chart of an affine representable space is bounded by
the size of the scheme. -/
theorem mk_chartRing_idChart_le (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    #(chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) (idChart B S hS U)) ≤
      ((BigFppfOver.toScheme B S hS).obj U).size :=
  Scheme.mk_sections_le_size ((BigFppfOver.toScheme B S hS).obj U) ⟨⊤, isAffineOpen_top _⟩

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- **The base change of `X` to an affine test scheme has a presentation by affine schemes of size
at most that of the test scheme.** -/
theorem exists_affine_presentation (hsep : IsSeparated B S hS D.f.hom) (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    ∃ P : Presentation B S hS (D.space T).1 (D.space T).2,
      IsAffine ((BigFppfOver.toScheme B S hS).obj P.U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj P.R) ∧
      ((BigFppfOver.toScheme B S hS).obj P.U).size ≤
        ((BigFppfOver.toScheme B S hS).obj T.left).size ∧
      ((BigFppfOver.toScheme B S hS).obj P.R).size ≤
        ((BigFppfOver.toScheme B S hS).obj T.left).size := by
  have sq := AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeSpace D.f T)
  have hqcT : IsQuasiCompactSpace B S hS (yoneda.obj T.left) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS T.left hT
  have hqc : IsQuasiCompactSpace B S hS (D.space T).1 :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS (isAlgebraicSpace_yoneda B S hS T.left) hqcT
      (D.projection T).hom (IsQuasiCompact.of_isPullback B S hS sq D.finitePresentation.2.1)
  obtain ⟨U, φ, hUa, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ (D.space T).2).1 hqc
  let P := bundledAtlasPresentation (D.space T) φ hsurj
    ((isEtale_iff_presheaf_of_yoneda B S hS φ).1 het)
  have hsepT : IsSeparated B S hS (D.projection T).hom := isSeparated_of_isPullback B S hS sq hsep
  obtain ⟨Q, eQ, hQ⟩ := exists_isAffine_selfPullback_of_isSeparated_to_affine hT hUa hsepT φ
  have eR : yoneda.obj P.R ≅ yoneda.obj Q := P.isPullback.isoPullback ≪≫ eQ
  have eR' : P.R ≅ Q := (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).preimageIso eR
  have hRa : IsAffine ((BigFppfOver.toScheme B S hS).obj P.R) :=
    IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map eR'.hom)
  have hφl : IsLocallyOfFiniteType B S hS (φ ≫ (D.projection T).hom) :=
    isLocallyOfFiniteType_comp' B S hS φ _ (D.space T).2 (isAlgebraicSpace_yoneda B S hS T.left)
      (isLocallyOfFiniteType_of_isEtale' B S hS φ het)
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
        (isPullback_baseChangeSpace D.f T)
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS D.finitePresentation.1))
  have htl : IsLocallyOfFiniteType B S hS (yoneda.map P.target ≫ φ ≫ (D.projection T).hom) :=
    isLocallyOfFiniteType_comp' B S hS _ _ (isAlgebraicSpace_yoneda B S hS P.U)
      (isAlgebraicSpace_yoneda B S hS T.left)
      (isLocallyOfFiniteType_of_isEtale' B S hS _
        (presentationGroupoid_target_isEtale P)) hφl
  exact ⟨P, hUa, hRa, size_le_of_isLocallyOfFiniteType_yoneda hUa _ hφl,
    size_le_of_isLocallyOfFiniteType_yoneda hRa _ htl⟩

/-- **The finitely presented quasi-coherent modules on the base change of `X` to an affine test
scheme `T` have at most `size T` isomorphism classes.** -/
theorem exists_code_baseChange (hsep : IsSeparated B S hS D.f.hom) (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    ∃ (ι : Type u) (_ : #ι ≤ ((BigFppfOver.toScheme B S hS).obj T.left).size)
      (c : FinitePresentationModules (D.space T).1 (D.space T).2 → ι),
        ∀ M M', c M = c M' → Nonempty (M.1 ≅ M'.1) := by
  obtain ⟨P, hUa, hRa, hUs, hRs⟩ := D.exists_affine_presentation hsep T hT
  obtain ⟨ι, hι, c, hc⟩ := exists_code_of_presentation P hUa hRa
  refine ⟨ι, hι.trans (max_le (Scheme.aleph0_le_size _) (max_le ?_ ?_)), c, hc⟩
  · exact (mk_chartRing_idChart_le P.U hUa).trans hUs
  · exact (mk_chartRing_idChart_le P.R hRa).trans hRs

/-- Two objects of `Coh_{X/Y}` with the same test scheme and isomorphic modules are isomorphic in
the fibre over that scheme. -/
theorem nonempty_iso_fiber_of_iso {U : BigFppfOver B S hS} {T : SchemesOver D.Y}
    {F F' : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {q q' fp fp' fl fl' ps ps'} (hU : T.left = U) (hU' : T.left = U) (e : F ≅ F') :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Nonempty ((Functor.Fiber.mk (p := coherentSiteProjection D.categoryData)
        (a := (⟨T, F, q, fp, fl, ps⟩ : CoherentObject D)) hU) ≅
      Functor.Fiber.mk (p := coherentSiteProjection D.categoryData)
        (a := (⟨T, F', q', fp', fl', ps'⟩ : CoherentObject D)) hU') := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  subst hU
  let A : CoherentObject D := ⟨T, F, q, fp, fl, ps⟩
  let A' : CoherentObject D := ⟨T, F', q', fp', fl', ps'⟩
  let m : A ⟶ A' := (⟨𝟙 T, (D.idComparison (modulePushforwardCoherence B S hS) T).hom.app F' ≫
    e.inv, inferInstance⟩ : CoherentHom A A')
  have hm : (coherentSiteProjection D.categoryData).IsHomLift (𝟙 T.left) m :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl)
  have hmi : IsIso m :=
    Functor.isIso_of_isHomLift_id' _ D.isFiberedInGroupoids_siteProjection m hm
  let i : A ≅ A' := @asIso _ _ _ _ m hmi
  have hi : (coherentSiteProjection D.categoryData).IsHomLift (𝟙 T.left) i.hom := hm
  let φ : Functor.Fiber.mk (p := coherentSiteProjection D.categoryData) (a := A) rfl ⟶
      Functor.Fiber.mk (p := coherentSiteProjection D.categoryData) (a := A') rfl := ⟨i.hom, hi⟩
  let ψ : Functor.Fiber.mk (p := coherentSiteProjection D.categoryData) (a := A') rfl ⟶
      Functor.Fiber.mk (p := coherentSiteProjection D.categoryData) (a := A) rfl :=
    ⟨i.inv, @IsHomLift.lift_id_inv _ _ _ _ _ _ _ _ i hi⟩
  exact ⟨⟨φ, ψ, Functor.Fiber.hom_ext i.hom_inv_id, Functor.Fiber.hom_ext i.inv_hom_id⟩⟩

/-- The objects of `SchemesOver D.Y` with underlying object `U` are at most `#Y(U)`. -/
private theorem mk_schemesOver_left_eq_le (U : BigFppfOver B S hS) :
    #{T : SchemesOver D.Y // T.left = U} ≤ lift.{u + 1} #(D.Y.1.obj (op U)) := by
  have emb : {T : SchemesOver D.Y // T.left = U} ↪ D.Y.1.obj (op U) := ⟨fun T => yonedaEquiv
    (eqToHom (congrArg (fun V => yoneda.obj V) T.2.symm) ≫ T.1.hom.hom), by
      rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
      obtain ⟨Tl, ⟨⟩, Th⟩ := T
      obtain ⟨Tl', ⟨⟩, Th'⟩ := T'
      change Tl = U at hT
      change Tl' = U at hT'
      subst hT hT'
      have h' := yonedaEquiv.injective h
      simp only [eqToHom_refl] at h'
      have hh : Th = Th' := ObjectProperty.hom_ext _ h'
      subst hh
      rfl⟩
  have := lift_mk_le'.{u + 1, u}.2 ⟨emb⟩
  rwa [lift_id'.{u, u + 1}] at this

/-- **The fibre of `Coh_{X/Y}` over an affine object `U` of the site has at most
`#Y(U) · size U` isomorphism classes.** -/
theorem mk_quotient_fiber_le (hsep : IsSeparated B S hS D.f.hom) (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    #(Quotient (isIsomorphicSetoid ((coherentSiteProjection D.categoryData).Fiber U))) ≤
      lift.{u + 1} (#(D.Y.1.obj (op U)) * ((BigFppfOver.toScheme B S hS).obj U).size) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  classical
  let 𝒯 := {T : SchemesOver D.Y // T.left = U}
  have hcode : ∀ T : 𝒯, ∃ (ι : Type u) (_ : #ι ≤ ((BigFppfOver.toScheme B S hS).obj U).size)
      (c : FinitePresentationModules (D.space T.1).1 (D.space T.1).2 → ι),
        ∀ M M', c M = c M' → Nonempty (M.1 ≅ M'.1) := fun T => by
    obtain ⟨T, rfl⟩ := T
    exact D.exists_code_baseChange hsep T hU
  choose ι hι c hc using hcode
  let code : (coherentSiteProjection D.categoryData).Fiber U → Σ T : 𝒯, ULift.{u + 1} (ι T) :=
    fun a => ⟨⟨a.1.T, a.2⟩, ⟨c ⟨a.1.T, a.2⟩ ⟨a.1.F, a.1.quasicoherent, a.1.finitePresentation⟩⟩⟩
  have hinj : ∀ a b, code a = code b → Nonempty (a ≅ b) := by
    rintro ⟨⟨T, F, q, fp, fl, ps⟩, ha⟩ ⟨⟨T', F', q', fp', fl', ps'⟩, hb⟩ h
    obtain ⟨hT, hcd⟩ := Sigma.mk.inj_iff.mp h
    have hTT : T = T' := congrArg Subtype.val hT
    subst hTT
    obtain ⟨e⟩ := hc ⟨T, ha⟩ ⟨F, q, fp⟩ ⟨F', q', fp'⟩ (congrArg ULift.down (eq_of_heq hcd))
    exact D.nonempty_iso_fiber_of_iso ha hb e
  have h𝒯 : #𝒯 ≤ lift.{u + 1} #(D.Y.1.obj (op U)) := mk_schemesOver_left_eq_le D U
  have hsig : #(Σ T : 𝒯, ULift.{u + 1} (ι T)) ≤
      #𝒯 * lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).size := by
    rw [mk_sigma]
    calc sum (fun T : 𝒯 => #(ULift.{u + 1} (ι T)))
        ≤ sum (fun _ : 𝒯 => lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).size) :=
          sum_le_sum _ _ fun T => by
            rw [mk_uLift]
            exact lift_le.2 (hι T)
      _ = #𝒯 * lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).size := sum_const' _ _
  obtain ⟨emb⟩ := Cardinal.lift_mk_quotient_isIsomorphic_le code hinj
  calc #(Quotient (isIsomorphicSetoid ((coherentSiteProjection D.categoryData).Fiber U)))
      ≤ #(Σ T : 𝒯, ULift.{u + 1} (ι T)) := mk_le_of_injective emb.injective
    _ ≤ #𝒯 * lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).size := hsig
    _ ≤ lift.{u + 1} #(D.Y.1.obj (op U)) *
          lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).size := by gcongr
    _ = lift.{u + 1} (#(D.Y.1.obj (op U)) * ((BigFppfOver.toScheme B S hS).obj U).size) :=
        (lift_mul _ _).symm

/-- **Axiom [-1] for `Coh_{X/Y}`, with `Y` represented by an object `V₀` of the site**, given an
object of the site of size at least `2 ^ max (size S) (size V₀)`. A finite type field point
`U = Spec k` of `S` has size at most that of `S`; its morphisms to `V₀` are at most
`2 ^ size V₀ · #k ^ size V₀`; and over each of them the finitely presented modules on `X_U` have
at most `size U` isomorphism classes. -/
theorem isSizeBounded_coherentCFG_of_le (hsep : IsSeparated B S hS D.f.hom)
    (V₀ : BigFppfOver B S hS) (hY : D.Y = (schemeSpaceFunctor B S hS).obj V₀)
    (T₀ : BigFppfOver B S hS)
    (hT₀ : (2 : Cardinal.{u}) ^ max S.size ((BigFppfOver.toScheme B S hS).obj V₀).size ≤
      T₀.left.1.size) :
    Stack.IsSizeBounded B S hS D.coherentCFG := by
  refine ⟨T₀, fun U k _ hk hft => ?_⟩
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have hUS : ((BigFppfOver.toScheme B S hS).obj U).size ≤ S.size := by
    have := hft.1
    have := hft.2
    exact Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (B.inclusion.map U.hom)
  have hUk : (BigFppfOver.toScheme B S hS).obj U = Spec (.of k) := hk
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := by
    rw [hUk]
    infer_instance
  have hfib := D.mk_quotient_fiber_le hsep U hUa
  set m := max S.size ((BigFppfOver.toScheme B S hS).obj V₀).size
  have hm0 : ℵ₀ ≤ m := (Scheme.aleph0_le_size S).trans (le_max_left _ _)
  have hm2 : ℵ₀ ≤ 2 ^ m := hm0.trans (cantor m).le
  have hSm : S.size ≤ 2 ^ m := (le_max_left _ _).trans (cantor m).le
  have hk : #k ≤ S.size := by
    have : #k ≤ (Spec (.of k)).size := by
      rw [Scheme.size_Spec]
      exact le_max_right _ _
    rw [← hUk] at this
    exact this.trans hUS
  have hmul : ∀ a b : Cardinal.{u}, a ≤ 2 ^ m → b ≤ 2 ^ m → a * b ≤ 2 ^ m := fun a b ha hb =>
    (mul_le_mul' ha hb).trans_eq (mul_eq_self hm2)
  have hYU : #(D.Y.1.obj (op U)) ≤ 2 ^ m := by
    have h₁ : #(D.Y.1.obj (op U)) ≤ #((BigFppfOver.toScheme B S hS).obj U ⟶
        (BigFppfOver.toScheme B S hS).obj V₀) := by
      rw [hY]
      exact mk_le_of_injective (BigFppfOver.toScheme B S hS).map_injective
    rw [hUk] at h₁
    refine h₁.trans ((Scheme.mk_hom_spec_field_le k _).trans ?_)
    have e₁ : (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj V₀).size ≤ 2 ^ m :=
      power_le_power_left two_ne_zero (le_max_right _ _)
    have e₂ : #k ^ ((BigFppfOver.toScheme B S hS).obj V₀).size ≤ 2 ^ m := by
      calc #k ^ ((BigFppfOver.toScheme B S hS).obj V₀).size
          ≤ (2 ^ m) ^ m := by
            refine (power_le_power_right (hk.trans hSm)).trans ?_
            exact power_le_power_left (power_ne_zero m two_ne_zero) (le_max_right _ _)
        _ = 2 ^ (m * m) := power_mul.symm
        _ = 2 ^ m := by rw [mul_eq_self hm0]
    exact hmul _ _ e₁ e₂
  have hbound : #(D.Y.1.obj (op U)) * ((BigFppfOver.toScheme B S hS).obj U).size ≤
      T₀.left.1.size := hmul _ _ hYU (hUS.trans hSm) |>.trans hT₀
  calc lift.{u} #(Quotient (isIsomorphicSetoid (D.coherentCFG.val.p.Fiber U)))
      = #(Quotient (isIsomorphicSetoid ((coherentSiteProjection D.categoryData).Fiber U))) :=
        lift_id'.{u, u + 1} _
    _ ≤ lift.{u + 1} (#(D.Y.1.obj (op U)) * ((BigFppfOver.toScheme B S hS).obj U).size) := hfib
    _ ≤ lift.{u + 1} T₀.left.1.size := lift_le.2 hbound

end CoherentSituation

/-- **Objects of arbitrary size below the cutoff.** For a cardinal `κ` below the cutoff of a big
fppf site containing the final scheme, the spectrum of a polynomial ring in `κ` variables over `ℤ`
is an object of the site over the final scheme, of size at least `κ`. -/
theorem exists_size_ge {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u})) {κ : Cardinal.{u}}
    (hκ : κ < B.cutoff) : ∃ T : BigFppfOver B (⊤_ Scheme.{u}) hZ, κ ≤ T.left.1.size := by
  have hK : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))) := by
    refine lt_of_le_of_lt (le_of_eq (Scheme.size_Spec _)) ?_
    refine lt_of_le_of_lt (max_le le_rfl ?_) B.aleph0_lt_cutoff
    change #(ULift.{u} ℤ) ≤ ℵ₀
    simp
  have hI : #κ.out < B.cutoff := by rwa [Cardinal.mk_out]
  have hT := contains_Spec_mvPolynomial B (I := κ.out) hK hI
  refine ⟨Over.mk (ObjectProperty.homMk (terminal.from _) : B.obj hT ⟶ B.obj hZ), ?_⟩
  change κ ≤ (Spec (CommRingCat.of (MvPolynomial κ.out (ULift.{u} ℤ)))).size
  rw [Scheme.size_Spec]
  refine le_trans ?_ (le_max_right _ _)
  calc κ = #κ.out := (Cardinal.mk_out κ).symm
    _ ≤ #(MvPolynomial κ.out (ULift.{u} ℤ)) :=
      mk_le_of_injective (MvPolynomial.X_injective (σ := κ.out) (R := ULift.{u} ℤ))

namespace CoherentSituation

/-- **Axiom [-1] for `Coh_{X/Y}` over `Spec ℤ`, with `Y` represented by an object of the
site.** -/
theorem isSizeBounded_coherentCFG_overIntegers {B : BigFppfSite.{u}}
    {hZ : B.Contains (⊤_ Scheme.{u})} (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)
    (hsep : IsSeparated B _ hZ D.f.hom) (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hY : D.Y = (schemeSpaceFunctor B _ hZ).obj V₀) :
    Stack.IsSizeBounded B _ hZ D.coherentCFG := by
  have hm : max (⊤_ Scheme.{u}).size ((BigFppfOver.toScheme B _ hZ).obj V₀).size < B.cutoff :=
    max_lt hZ V₀.left.2
  obtain ⟨T₀, hT₀⟩ := exists_size_ge hZ (B.cutoff_isStrongPrelimit hm)
  exact D.isSizeBounded_coherentCFG_of_le hsep V₀ hY T₀ hT₀

end CoherentSituation

end AlgebraicGeometry.Space

end
