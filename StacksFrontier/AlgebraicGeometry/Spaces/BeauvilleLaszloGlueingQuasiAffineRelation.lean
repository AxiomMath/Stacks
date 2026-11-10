module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineQuotientSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful

/-!
# The relation of Stacks 0F9U

Given an affine glueable algebraic space `T` over `X = Spec R` and a morphism of triples
`q : G(T) ⟶ (V, V', Y')` whose components are separated affine charts (Stacks 0F9U, steps 1–3),
the proof of Stacks 0F9U realizes the kernel pair of `q` — a triple with affine components — as
the image of an affine glueable `W` (Stacks 0F9Q), obtains two morphisms `p₀, p₁ : W ⟶ T`, and
shows by Stacks 0F9R that they are flat and locally of finite presentation, that
`(p₀, p₁) : W ⟶ T ×_X T` is a closed immersion, and that `W` is an equivalence relation on `T`.

## Main results

* `BeauvilleLaszlo.Space.canonical_comm`: the canonical square of a glueing pair commutes.
* `BeauvilleLaszlo.Space.isAffineSpace_product`: a product of affine algebraic spaces over an
  affine base is affine.
* `BeauvilleLaszlo.Space.isGlueableAlgebraicSpace_of_isFlat`: an affine algebraic space flat over
  an affine glueable one is glueable.
* `BeauvilleLaszlo.Space.exists_relation_data`: **Stacks 0F9U, steps 4–5**, the kernel pair of
  `q` realized by an affine glueable `W` with `p₀, p₁ : W ⟶ T`.
* `BeauvilleLaszlo.Space.relation_flat`, `BeauvilleLaszlo.Space.relation_isClosedImmersion` and
  `BeauvilleLaszlo.Space.relation_isEquivalenceRelation`: **Stacks 0F9U, steps 6–8**, `p₀` and
  `p₁` are flat and locally of finite presentation, `(p₀, p₁)` is a closed immersion, and `W` is
  an equivalence relation on `T`.

## References

* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-- **The canonical square of a glueing pair commutes**: `U' → U → X` and `U' → X' → X` agree. -/
theorem canonical_comm {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R))) :
    canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX := by
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Localization.awayMap g f)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
    Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f)))) ≫
      Spec.map (CommRingCat.ofHom g)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq]

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The fibre product of a separated affine chart with itself is affine. -/
theorem IsSeparatedAffineChart.isAffineSpace_of_isPullback {X Y P : AlgebraicSpaces B S hS}
    {φ : X ⟶ Y} (hφ : IsSeparatedAffineChart φ) {fst snd : P ⟶ X}
    (sq : IsPullback fst snd φ φ) : AlgebraicGeometry.Space.IsAffineSpace B S hS P.obj := by
  have hX := hφ.isAffineSpace_source
  obtain ⟨E, V, eE, eV, h, -, -, hV, -⟩ := hφ
  exact isAffineSpace_of_isPullback_of_isSeparated sq hX hX eV hV

/-- A pair whose morphism into the product is a monomorphism is jointly monic. -/
theorem jointlyMono₂_of_mono_prodLift {C : Type*} [Category C] [HasBinaryProducts C]
    {R X : C} (a b : R ⟶ X) [Mono (prod.lift a b)] : JointlyMono₂ a b where
  right_cancellation _ x y h₁ h₂ := (cancel_mono (prod.lift a b)).1 (by
    apply prod.hom_ext <;> simpa)

/-- A functor carrying one fibre product of a cospan to a fibre product carries the chosen one
to a fibre product. -/
theorem isPullback_map_pullback_of_isPullback {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsq : IsPullback fst snd f g) [HasPullback f g]
    (hF : IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)) :
    IsPullback (F.map (pullback.fst f g)) (F.map (pullback.snd f g)) (F.map f) (F.map g) := by
  refine IsPullback.of_iso hF (F.mapIso hsq.isoPullback) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp) <;> simp [← F.map_comp]

/-- The algebraic space of the terminal object of the big fppf site over `S` is terminal among
algebraic spaces over `S`. -/
noncomputable def isTerminal_schemeSpace_terminal :
    IsTerminal (schemeSpace (Over.mk (𝟙 (B.obj hS)))) :=
  have ht : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  IsTerminal.ofUniqueHom (fun A => ObjectProperty.homMk (ht.from A.obj))
    (fun _ _ => ObjectProperty.hom_ext _ (ht.hom_ext _ _))

/-- **A product of affine algebraic spaces over an affine base is affine.** -/
theorem isAffineSpace_product [IsAffine S] {T T' : AlgebraicSpaces B S hS}
    (hT : AlgebraicGeometry.Space.IsAffineSpace B S hS T.obj)
    (hT' : AlgebraicGeometry.Space.IsAffineSpace B S hS T'.obj) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS
      (AlgebraicGeometry.AlgebraicSpaces.product B S hS T T').obj := by
  have sq := IsPullback.of_is_product
    (AlgebraicGeometry.AlgebraicSpaces.isLimitBinaryFanProduct B S hS T T')
    (isTerminal_schemeSpace_terminal (B := B) (hS := hS))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) :=
    inferInstanceAs (IsAffine S)
  exact isAffineSpace_of_isPullback_of_isSeparated sq hT hT' (Iso.refl _) inferInstance

end General

/-! ### The components of the fibre product of triples -/

section Components

variable (B : BigFppfSite.{u}) {U' U X' : Scheme.{u}} {hU' : B.Contains U'}
  {hU : B.Contains U} {hX' : B.Contains X'}
  {gU : B.obj hU' ⟶ B.obj hU} {gX' : B.obj hU' ⟶ B.obj hX'}
  {D E T : GlueingData B U' U X' hU' hU hX' gU gX'} (a : D ⟶ T) (b : E ⟶ T)

/-- The `U`-component of the componentwise fibre product of `a` and `b` is a pullback square. -/
theorem isPullback_overU_glueingDataPullback :
    IsPullback ((overU B U' U X' hU' hU hX' gU gX').map (glueingDataPullbackFst B a b))
      ((overU B U' U X' hU' hU hX' gU gX').map (glueingDataPullbackSnd B a b))
      ((overU B U' U X' hU' hU hX' gU gX').map a) ((overU B U' U X' hU' hU hX' gU gX').map b) :=
  IsPullback.of_hasPullback a.hom.left.right b.hom.left.right

/-- The `U'`-component of the componentwise fibre product of `a` and `b` is a pullback square. -/
theorem isPullback_overU'_glueingDataPullback :
    IsPullback ((overU' B U' U X' hU' hU hX' gU gX').map (glueingDataPullbackFst B a b))
      ((overU' B U' U X' hU' hU hX' gU gX').map (glueingDataPullbackSnd B a b))
      ((overU' B U' U X' hU' hU hX' gU gX').map a) ((overU' B U' U X' hU' hU hX' gU gX').map b) :=
  IsPullback.of_hasPullback a.hom.left.left b.hom.left.left

/-- The `X'`-component of the componentwise fibre product of `a` and `b` is a pullback square. -/
theorem isPullback_overX'_glueingDataPullback :
    IsPullback ((overX' B U' U X' hU' hU hX' gU gX').map (glueingDataPullbackFst B a b))
      ((overX' B U' U X' hU' hU hX' gU gX').map (glueingDataPullbackSnd B a b))
      ((overX' B U' U X' hU' hU hX' gU gX').map a) ((overX' B U' U X' hU' hU hX' gU gX').map b) :=
  IsPullback.of_hasPullback a.hom.right b.hom.right

end Components

section Glueable

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))

/-- Glueability of an algebraic space over `Spec R` is invariant under isomorphism. -/
theorem isGlueableAlgebraicSpace_of_iso_ringHom {Y Y' : AlgebraicSpaces B (Spec (.of R)) hX}
    (e : Y ≅ Y') (hY : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y' := by
  intro W p hW hp
  refine hY W (p ≫ e.inv.hom) hW ?_
  have : IsIso e.inv.hom := ((ObjectProperty.ι _).mapIso e.symm).isIso_hom
  exact (isEtale_respectsIso B _ hX).postcomp _ _ _ hp

/-- **An affine algebraic space flat over an affine glueable one is glueable** (the case of a flat
morphism of the closure property of Stacks 0F9P). -/
theorem isGlueableAlgebraicSpace_of_isFlat (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    {P W : AlgebraicSpaces B (Spec (.of R)) hX} (m : P ⟶ W)
    (hP : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX P.obj)
    (hW : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX W.obj)
    (hWg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX W)
    (hm : AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX m.hom) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX P := by
  obtain ⟨P₀, hP₀, ⟨eP⟩⟩ := hP
  obtain ⟨W₀, hW₀, ⟨eW⟩⟩ := hW
  let μ : P₀ ⟶ W₀ := Yoneda.fullyFaithful.preimage (eP.inv ≫ m.hom ≫ eW.hom)
  have hμ : yoneda.map μ = eP.inv ≫ m.hom ≫ eW.hom := Yoneda.fullyFaithful.map_preimage _
  have hflat : Flat ((BigFppfOver.toScheme B (Spec (.of R)) hX).map μ) := by
    refine (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff B (Spec (.of R)) hX
      Flat.isEtaleLocalOnSourceAndTarget μ).1 ?_
    rw [hμ]
    have hR := AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf B
      (Spec (.of R)) hX (@Flat.{u})
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _ hm)
  have hW₀g : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX W₀ :=
    hWg W₀ eW.inv hW₀ (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX eW.inv)
  have hP₀g := AlgebraicGeometry.Space.isGlueableGlobalSections_of_flat g f B hX μ hW₀ hP₀
    hflat hW₀g
  exact isGlueableAlgebraicSpace_of_iso_ringHom g f B hX
    (ObjectProperty.isoMk _ eP.symm)
    (isGlueableAlgebraicSpace_schemeSpace g f B hX hglue P₀ hP₀ hP₀g)

end Glueable

/-! ### The relation -/

section Relation

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))

/-- The gluing functor of Stacks 0F9N at the canonical square of a glueing pair, with the
commutativity of the square supplied. -/
noncomputable abbrev canonicalSpec := canonicalGlueingFunctorSpec g f B hU' hU hX' hX
  (canonical_comm g f B hU' hU hX' hX)

/-- Flatness of the two members of a kernel pair of a separated affine chart. -/
theorem flat_of_isPullback_chart {S : Scheme.{u}} {hS : B.Contains S}
    {W' T' Z' : AlgebraicSpaces B S hS} {a b : W' ⟶ T'} {φ' : T' ⟶ Z'}
    (hk : IsPullback a b φ' φ') (hφ : IsSeparatedAffineChart φ') :
    (AlgebraicGeometry.Space.IsFlat B S hS a.hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a.hom) ∧
    (AlgebraicGeometry.Space.IsFlat B S hS b.hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS b.hom) :=
  ⟨⟨MorphismProperty.of_isPullback (P := AlgebraicGeometry.Space.flatProperty B S hS)
      hk.flip hφ.isFlat,
    MorphismProperty.of_isPullback
      (P := AlgebraicGeometry.Space.locallyOfFinitePresentationProperty B S hS)
      hk.flip hφ.isLocallyOfFinitePresentation⟩,
    ⟨MorphismProperty.of_isPullback (P := AlgebraicGeometry.Space.flatProperty B S hS)
      hk hφ.isFlat,
    MorphismProperty.of_isPullback
      (P := AlgebraicGeometry.Space.locallyOfFinitePresentationProperty B S hS)
      hk hφ.isLocallyOfFinitePresentation⟩⟩

variable {Z : GlueingData B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX')}
    {T : AlgebraicSpaces B (Spec (.of R)) hX}

/-- The kernel-pair condition of the relation of Stacks 0F9U on the three legs. -/
def RelationLegs (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z)
    {W : AlgebraicSpaces B (Spec (.of R)) hX} (p₀ p₁ : W ⟶ T) : Prop :=
  IsPullback ((baseChange B _ _ hU hX (canJU f B hU hX)).map p₀)
      ((baseChange B _ _ hU hX (canJU f B hU hX)).map p₁)
      ((canonicalSpec g f B hU' hU hX' hX).overUIso.inv.app T ≫
        (overU B _ _ _ hU' hU hX' _ _).map q)
      ((canonicalSpec g f B hU' hU hX' hX).overUIso.inv.app T ≫
        (overU B _ _ _ hU' hU hX' _ _).map q) ∧
  IsPullback ((baseChange B _ _ hU' hX (canGU g f B hU' hU ≫ canJU f B hU hX)).map p₀)
      ((baseChange B _ _ hU' hX (canGU g f B hU' hU ≫ canJU f B hU hX)).map p₁)
      ((canonicalSpec g f B hU' hU hX' hX).overU'Iso.inv.app T ≫
        (overU' B _ _ _ hU' hU hX' _ _).map q)
      ((canonicalSpec g f B hU' hU hX' hX).overU'Iso.inv.app T ≫
        (overU' B _ _ _ hU' hU hX' _ _).map q) ∧
  IsPullback ((baseChange B _ _ hX' hX (canJX' g B hX' hX)).map p₀)
      ((baseChange B _ _ hX' hX (canJX' g B hX' hX)).map p₁)
      ((canonicalSpec g f B hU' hU hX' hX).overX'Iso.inv.app T ≫
        (overX' B _ _ _ hU' hU hX' _ _).map q)
      ((canonicalSpec g f B hU' hU hX' hX).overX'Iso.inv.app T ≫
        (overX' B _ _ _ hU' hU hX' _ _).map q)

/-- The charts read through the comparison isomorphisms of the gluing functor. -/
def ChartLegs (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z) : Prop :=
  IsSeparatedAffineChart ((canonicalSpec g f B hU' hU hX' hX).overUIso.inv.app T ≫
      (overU B _ _ _ hU' hU hX' _ _).map q) ∧
  IsSeparatedAffineChart ((canonicalSpec g f B hU' hU hX' hX).overU'Iso.inv.app T ≫
      (overU' B _ _ _ hU' hU hX' _ _).map q) ∧
  IsSeparatedAffineChart ((canonicalSpec g f B hU' hU hX' hX).overX'Iso.inv.app T ≫
      (overX' B _ _ _ hU' hU hX' _ _).map q)

/-- If the three components of `q` are separated affine charts, then `ChartLegs` holds for `q`. -/
theorem chartLegs_of (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z)
    (hqU : IsSeparatedAffineChart ((overU B _ _ _ hU' hU hX' _ _).map q))
    (hqM : IsSeparatedAffineChart ((overU' B _ _ _ hU' hU hX' _ _).map q))
    (hqX : IsSeparatedAffineChart ((overX' B _ _ _ hU' hU hX' _ _).map q)) :
    ChartLegs g f B hU' hU hX' hX q :=
  ⟨hqU.iso_comp ((canonicalSpec g f B hU' hU hX' hX).overUIso.app T).symm,
    hqM.iso_comp ((canonicalSpec g f B hU' hU hX' hX).overU'Iso.app T).symm,
    hqX.iso_comp ((canonicalSpec g f B hU' hU hX' hX).overX'Iso.app T).symm⟩

/-- **Stacks 0F9U, steps 4–5: the relation.** The kernel pair of `q`, realized as the image of
an affine glueable `W` with two morphisms to `T`. -/
theorem exists_relation_data (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (hTa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1)
    (hTg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T)
    (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z)
    (hqU : IsSeparatedAffineChart ((overU B _ _ _ hU' hU hX' _ _).map q))
    (hqM : IsSeparatedAffineChart ((overU' B _ _ _ hU' hU hX' _ _).map q))
    (hqX : IsSeparatedAffineChart ((overX' B _ _ _ hU' hU hX' _ _).map q)) :
    ∃ (W : AlgebraicSpaces B (Spec (.of R)) hX) (p₀ p₁ : W ⟶ T)
      (eW : (canonicalSpec g f B hU' hU hX' hX).functor.obj W ≅ glueingDataPullback B q q),
      AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX W.1 ∧
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX W ∧
      (canonicalSpec g f B hU' hU hX' hX).functor.map p₀ =
        eW.hom ≫ glueingDataPullbackFst B q q ∧
      (canonicalSpec g f B hU' hU hX' hX).functor.map p₁ =
        eW.hom ≫ glueingDataPullbackSnd B q q ∧
      RelationLegs g f B hU' hU hX' hX q p₀ p₁ := by
  have hcomm := canonical_comm g f B hU' hU hX' hX
  let G := canonicalSpec g f B hU' hU hX' hX
  have hP : affineComponents B _ _ _ hU' hU hX' _ _ (glueingDataPullback B q q) :=
    ⟨hqU.isAffineSpace_of_isPullback (isPullback_overU_glueingDataPullback B q q),
      hqM.isAffineSpace_of_isPullback (isPullback_overU'_glueingDataPullback B q q),
      hqX.isAffineSpace_of_isPullback (isPullback_overX'_glueingDataPullback B q q)⟩
  obtain ⟨W, hWa, hWg, ⟨eW⟩⟩ := exists_affineGlueable_iso_of_affineComponents g f B hU' hU hX'
    hX hcomm hglue _ hP
  have lift := fun c => exists_hom_of_hom_glueingFunctor g f B hU' hU hX' hX hcomm hglue W T
    hWa hWg hTa hTg (eW.hom ≫ c)
  obtain ⟨p₀, hp₀⟩ := lift (glueingDataPullbackFst B q q)
  obtain ⟨p₁, hp₁⟩ := lift (glueingDataPullbackSnd B q q)
  exact ⟨W, p₀, p₁, eW, hWa, hWg, hp₀, hp₁,
    isPullback_map_of_isPullback_of_iso G.overUIso q _ _
      (isPullback_overU_glueingDataPullback B q q) eW p₀ p₁ hp₀ hp₁,
    isPullback_map_of_isPullback_of_iso G.overU'Iso q _ _
      (isPullback_overU'_glueingDataPullback B q q) eW p₀ p₁ hp₀ hp₁,
    isPullback_map_of_isPullback_of_iso G.overX'Iso q _ _
      (isPullback_overX'_glueingDataPullback B q q) eW p₀ p₁ hp₀ hp₁⟩

/-- **Stacks 0F9U, step 6: the projections of the relation are flat and locally of finite
presentation** (Stacks 0F9R). -/
theorem relation_flat (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (hTa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1)
    (hTg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T)
    (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z)
    (hc : ChartLegs g f B hU' hU hX' hX q)
    {W : AlgebraicSpaces B (Spec (.of R)) hX} (p₀ p₁ : W ⟶ T)
    (hWa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX W.1)
    (hk : RelationLegs g f B hU' hU hX' hX q p₀ p₁) :
    (AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX p₀.hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B (Spec (.of R)) hX p₀.hom) ∧
    (AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX p₁.hom ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B (Spec (.of R)) hX p₁.hom) := by
  obtain ⟨hU₀, hU₁⟩ := flat_of_isPullback_chart B hk.1 hc.1
  obtain ⟨hM₀, hM₁⟩ := flat_of_isPullback_chart B hk.2.1 hc.2.1
  obtain ⟨hX₀, hX₁⟩ := flat_of_isPullback_chart B hk.2.2 hc.2.2
  exact ⟨isFlat_and_isLocallyOfFinitePresentation_of_glueingComponents g f hglue B hU' hU
      hX' hX p₀ hWa hTa hTg hU₀ hM₀ hX₀,
    isFlat_and_isLocallyOfFinitePresentation_of_glueingComponents g f hglue B hU' hU
      hX' hX p₁ hWa hTa hTg hU₁ hM₁ hX₁⟩

/-- **Stacks 0F9U, step 7: the relation is a closed subspace of `T ⨯ T`** (Stacks 0F9R). -/
theorem relation_isClosedImmersion (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (hTa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1)
    (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z)
    (hc : ChartLegs g f B hU' hU hX' hX q)
    {W : AlgebraicSpaces B (Spec (.of R)) hX} (p₀ p₁ : W ⟶ T)
    (hWa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX W.1)
    (hk : RelationLegs g f B hU' hU hX' hX q p₀ p₁) :
    AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R)) hX (prod.lift p₀.hom p₁.hom) :=
  isClosedImmersion_of_isClosedImmersion_glueingComponents g f hglue B hU' hU hX' hX
    (ObjectProperty.homMk (prod.lift p₀.hom p₁.hom) :
      W ⟶ AlgebraicGeometry.AlgebraicSpaces.product B _ hX T T) hWa
    (isAffineSpace_product hTa hTa)
    (isClosedImmersion_baseChange_map_prodLift B _ _ hX hU _ p₀ p₁ _ hk.1
      hc.1.isSeparatedOver_target)
    (isClosedImmersion_baseChange_map_prodLift B _ _ hX hU' _ p₀ p₁ _ hk.2.1
      hc.2.1.isSeparatedOver_target)
    (isClosedImmersion_baseChange_map_prodLift B _ _ hX hX' _ p₀ p₁ _ hk.2.2
      hc.2.2.isSeparatedOver_target)

/-- **Stacks 0F9U, step 8: the relation is an equivalence relation**, reflected along the
affine equivalence of Stacks 0F9Q from the kernel pair of `q`. -/
theorem relation_isEquivalenceRelation (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (hTa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1)
    (hTg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T)
    (q : (canonicalSpec g f B hU' hU hX' hX).functor.obj T ⟶ Z)
    {W : AlgebraicSpaces B (Spec (.of R)) hX} (p₀ p₁ : W ⟶ T)
    (eW : (canonicalSpec g f B hU' hU hX' hX).functor.obj W ≅ glueingDataPullback B q q)
    (hWa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX W.1)
    (hWg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX W)
    (hp₀ : (canonicalSpec g f B hU' hU hX' hX).functor.map p₀ =
      eW.hom ≫ glueingDataPullbackFst B q q)
    (hp₁ : (canonicalSpec g f B hU' hU hX' hX).functor.map p₁ =
      eW.hom ≫ glueingDataPullbackSnd B q q)
    (hp₁f : AlgebraicGeometry.Space.IsFlat B (Spec (.of R)) hX p₁.hom)
    (hci : AlgebraicGeometry.Space.IsClosedImmersion B (Spec (.of R)) hX
      (prod.lift p₀.hom p₁.hom)) :
    IsEquivalenceRelation p₀.hom p₁.hom := by
  have hcomm := canonical_comm g f B hU' hU hX' hX
  let G := canonicalSpec g f B hU' hU hX' hX
  -- Step 8: the equivalence relation, reflected along the affine equivalence of Stacks 0F9Q.
  have := canonicalAffineGlueableRestriction_isEquivalence g f B hU' hU hX' hX hcomm hglue
  let F := canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm ⋙ ObjectProperty.ι _
  let W₀ : (affineGlueableSpaces g f B hX).FullSubcategory := ⟨W, hWa, hWg⟩
  let T₀ : (affineGlueableSpaces g f B hX).FullSubcategory := ⟨T, hTa, hTg⟩
  let p₀C : W₀ ⟶ T₀ := ObjectProperty.homMk p₀
  let p₁C : W₀ ⟶ T₀ := ObjectProperty.homMk p₁
  have h : ∀ (p : W ⟶ T) (c), G.functor.map p = eW.hom ≫ c →
      eW.symm.hom ≫ F.map (ObjectProperty.homMk p : W₀ ⟶ T₀) = c := fun p c hp => by
    change eW.inv ≫ G.functor.map p = _
    rw [hp, Iso.inv_hom_id_assoc]
  have e' : EquivalenceRelation (eW.symm.hom ≫ F.map p₀C) (eW.symm.hom ≫ F.map p₁C) := by
    rw [h p₀ _ hp₀, h p₁ _ hp₁]
    exact IsKernelPair.equivalenceRelation q (glueingDataPullbackFst B q q)
      (glueingDataPullbackSnd B q q)
      (isPullback_glueingDataPullback B (glueingDataPullbackSnd B q q)
        (glueingDataPullbackFst B q q)).isLimit (isPullback_glueingDataPullback B q q)
  -- the fibre product `W ×_T W` is affine and glueable
  obtain ⟨T₁, hT₁, ⟨eT⟩⟩ := hTa
  have : IsAffine ((BigFppfOver.toScheme B _ hX).obj T₁) := hT₁
  have sq := IsPullback.of_hasPullback p₁ p₀
  have hQa := isAffineSpace_of_isPullback_of_isSeparated sq hWa hWa
    (ObjectProperty.isoMk _ eT) inferInstance
  have hQg := isGlueableAlgebraicSpace_of_isFlat g f B hX hglue (pullback.snd p₁ p₀) hQa hWa hWg
    (MorphismProperty.of_isPullback (P := AlgebraicGeometry.Space.flatProperty B _ hX) sq hp₁f)
  let Q₀ : (affineGlueableSpaces g f B hX).FullSubcategory := ⟨pullback p₁ p₀, hQa, hQg⟩
  have hQ : IsPullback (ObjectProperty.homMk (pullback.fst p₁ p₀) : Q₀ ⟶ W₀)
      (ObjectProperty.homMk (pullback.snd p₁ p₀) : Q₀ ⟶ W₀) p₁C p₀C :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ pullback.condition) sq
  have : HasPullback p₁C p₀C := hQ.hasPullback
  let eC := EquivalenceRelation.reflect F eW.symm p₀C p₁C e'
  let F' := ObjectProperty.ι (affineGlueableSpaces g f B hX) ⋙
    ObjectProperty.ι (fun F => IsAlgebraicSpace B (Spec (.of R)) hX F)
  have hpb : IsPullback (F'.map (pullback.fst p₁C p₀C)) (F'.map (pullback.snd p₁C p₀C))
      (F'.map p₁C) (F'.map p₀C) :=
    isPullback_map_pullback_of_isPullback F' hQ (sq.map (ObjectProperty.ι _))
  have : Mono (prod.lift p₀.hom p₁.hom) :=
    AlgebraicGeometry.Space.mono_of_isClosedImmersion B _ hX _ hci
  exact isEquivalenceRelation_map_of_isPullback F' eC hpb
    (show JointlyMono₂ p₀.hom p₁.hom from jointlyMono₂_of_mono_prodLift p₀.hom p₁.hom)

end Relation

end BeauvilleLaszlo.Space

end
