module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutAbstractSquares
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFiniteCover
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout

/-!
# Lifts of a family of curves over square-zero extensions of a field
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **A cocartesian square of bases with a thickening edge glues the total spaces.** For a
commutative square of families of curves whose square of base schemes is a pushout along a
thickening and an affine morphism, the square of total spaces is a pushout of schemes: the total
space of the target is flat over its base, so it is glued from its restrictions (the closing
paragraph of Stacks 07RX). -/
theorem isPushout_toScheme_totalSiteMap {b₀ b₁ b₂ c : CurveFamily B hZ}
    (h₀ : b₀.total.obj.IsRepresentable) (h₁ : b₁.total.obj.IsRepresentable)
    (h₂ : b₂.total.obj.IsRepresentable) (hc : c.total.obj.IsRepresentable)
    (ψ₁ : b₀ ⟶ b₁) (ψ₂ : b₀ ⟶ b₂) (φ₁ : b₁ ⟶ c) (φ₂ : b₂ ⟶ c) (hcomm : ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂)
    (hthick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map ψ₂.baseMap))
    [IsAffineHom ((BigFppfOver.toScheme B integerBase hZ).map ψ₁.baseMap)]
    (hpo : IsPushout ((BigFppfOver.toScheme B integerBase hZ).map ψ₂.baseMap)
      ((BigFppfOver.toScheme B integerBase hZ).map ψ₁.baseMap)
      ((BigFppfOver.toScheme B integerBase hZ).map φ₂.baseMap)
      ((BigFppfOver.toScheme B integerBase hZ).map φ₁.baseMap)) :
    IsPushout ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap h₂ h₀ ψ₂))
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap h₁ h₀ ψ₁))
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hc h₂ φ₂))
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hc h₁ φ₁)) := by
  refine Stacks.Pushout.isPushout_restrictions_of_flat hthick hpo
    (flat_toScheme_map_totalSiteToBase hc) ?_
    ((isPullback_totalSite hc h₁ φ₁).map (BigFppfOver.toScheme B integerBase hZ))
    ((isPullback_totalSite hc h₂ φ₂).map (BigFppfOver.toScheme B integerBase hZ))
    ((isPullback_totalSite h₁ h₀ ψ₁).map (BigFppfOver.toScheme B integerBase hZ))
    ((isPullback_totalSite h₂ h₀ ψ₂).map (BigFppfOver.toScheme B integerBase hZ))
  rw [← Functor.map_comp, ← Functor.map_comp, totalSiteMap_comp, totalSiteMap_comp, hcomm]

variable {y y' : CurveFamily B hZ} (hy : y.total.obj.IsRepresentable)
  (hy' : y'.total.obj.IsRepresentable)

/-- The identification of the total space of a family of curves with the presheaf of points of
the scheme representing it, as an isomorphism of algebraic spaces. -/
abbrev totalSpaceIso : schemeSpace (totalSite hy) ≅ y.total :=
  ObjectProperty.isoMk _ (totalSiteIso hy)

/-- **A morphism of families of curves from a cartesian square of schemes.** A morphism of base
schemes and a morphism of the representing schemes of the total spaces forming a cartesian
square with the structure morphisms is a morphism of families of curves. -/
def homOfToScheme (bm : y.base ⟶ y'.base)
    (g : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy'))
    (hg : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy))
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy'))
      ((BigFppfOver.toScheme B integerBase hZ).map bm)) : y ⟶ y' where
  baseMap := bm
  totalMap := (totalSpaceIso hy).inv ≫ schemeSpaceMap (integerSiteHom g) ≫ (totalSpaceIso hy').hom
  cartesian := by
    have hsite : IsPullback (integerSiteHom (U := totalSite hy) (V := totalSite hy') g)
        (totalSiteToBase hy) (totalSiteToBase hy') bm :=
      FiniteFreeAlgebra.isPullback_of_isPullback_toScheme hg
    refine IsPullback.of_iso (isPullback_schemeSpaceMap hsite) (totalSpaceIso hy)
      (totalSpaceIso hy') (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Iso.hom_inv_id_assoc (totalSpaceIso hy) _).symm
    · apply ObjectProperty.hom_ext
      change yoneda.map (totalSiteToBase hy) ≫ 𝟙 _ = _
      rw [Category.comp_id, yoneda_map_totalSiteToBase]
      rfl
    · apply ObjectProperty.hom_ext
      change yoneda.map (totalSiteToBase hy') ≫ 𝟙 _ = _
      rw [Category.comp_id, yoneda_map_totalSiteToBase]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The morphism of base schemes of `homOfToScheme hy hy' bm g hg` is `bm`. -/
@[simp]
theorem homOfToScheme_baseMap (bm : y.base ⟶ y'.base)
    (g : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy'))
    (hg : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy))
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy'))
      ((BigFppfOver.toScheme B integerBase hZ).map bm)) :
    (homOfToScheme hy hy' bm g hg).baseMap = bm := rfl

/-- The morphism of representing schemes of the total spaces underlying
`homOfToScheme hy hy' bm g hg` is `g`. -/
theorem totalSiteMap_homOfToScheme (bm : y.base ⟶ y'.base)
    (g : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy'))
    (hg : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy))
      ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy'))
      ((BigFppfOver.toScheme B integerBase hZ).map bm)) :
    totalSiteMap hy' hy (homOfToScheme hy hy' bm g hg) = integerSiteHom g := by
  apply yoneda.map_injective
  rw [yoneda_map_totalSiteMap]
  show (totalSiteIso hy).hom ≫ ((totalSiteIso hy).inv ≫ yoneda.map (integerSiteHom g) ≫
    (totalSiteIso hy').hom) ≫ (totalSiteIso hy').inv = _
  simp

/-- A morphism of families of curves with representable total spaces is determined by its
morphism of base schemes and the morphism of schemes underlying its morphism of total spaces. -/
theorem hom_ext_of_toScheme {f g : y ⟶ y'} (hb : f.baseMap = g.baseMap)
    (ht : (BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hy' hy f) =
      (BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hy' hy g)) : f = g := by
  have hsite := congrArg integerSiteHom ht
  rw [integerSiteHom_toScheme_map, integerSiteHom_toScheme_map] at hsite
  have hyo := congrArg yoneda.map hsite
  rw [yoneda_map_totalSiteMap, yoneda_map_totalSiteMap] at hyo
  refine Hom.ext hb (ObjectProperty.hom_ext _ ?_)
  simpa only [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right] using hyo

end CurveFamily

/-- The spectrum of a surjection onto a field whose kernel consists of nilpotent elements is a
thickening. -/
theorem isThickening_specMap_of_surjective_of_ker_le_nilradical {R K : Type u} [CommRing R]
    [Field K] (f : R →+* K) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R) :
    Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ hf, ?_⟩
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  intro (q : PrimeSpectrum R)
  obtain ⟨t⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  refine ⟨t, ?_⟩
  show PrimeSpectrum.comap f t = q
  ext1
  have h1 : (PrimeSpectrum.comap f t).asIdeal = RingHom.ker f := by
    have := t.isPrime
    have ht : t.asIdeal = ⊥ := Ideal.eq_bot_of_prime t.asIdeal
    show Ideal.comap f t.asIdeal = _
    rw [ht]
    rfl
  have := q.isPrime
  have h2 : q.asIdeal = RingHom.ker f :=
    (hmax.eq_of_le q.isPrime.ne_top (hker.trans (nilradical_le_prime q.asIdeal))).symm
  rw [h1, h2]

namespace CurveLift

open Deformation.Artin

variable {k : Type u} [Field k] {toS : Spec (.of k) ⟶ integerBase}
  {hk : B.Contains (Spec (.of k))} (x : CurveFamily B hZ)
  (hx : (curvesProjectionOver B hZ).obj x = algebraOver k B integerBase hZ toS hk)

/-- The square-zero arrow `Spec k ⟶ Spec k[M]` out of the base of `x`. -/
abbrev arrow (M : SiteModule k B) :
    (curvesProjectionOver B hZ).obj x ⟶ squareZeroOver k B integerBase hZ toS M :=
  eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk M

/-- The lifts of `x` to `Spec k[M]`. -/
abbrev Lift (M : SiteModule k B) := LiftAlong (curvesProjectionOver B hZ) x (arrow x hx M)

include hx in
/-- The total space of a family of curves over `Spec k` is representable. -/
theorem isRepresentable_total : x.total.obj.IsRepresentable :=
  x.isRepresentable_total_of_base_eq (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hx)

/-- The square-zero immersion `Spec k ⟶ Spec k[M]` is a thickening. -/
theorem isThickening_toScheme_squareZeroArrow (M : SiteModule k B) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B integerBase hZ).map
      (squareZeroArrow k B integerBase hZ toS hk M)) := by
  refine isThickening_specMap_of_surjective_of_ker_le_nilradical
    (TrivSqZeroExt.fstHom k k M.obj).toRingHom (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) ?_
  intro a ha
  refine mem_nilradical.mpr ⟨2, ?_⟩
  have h0 : a.fst = 0 := ha
  rw [pow_two]
  refine TrivSqZeroExt.ext ?_ ?_
  · show (a * a).fst = 0
    rw [TrivSqZeroExt.fst_mul, h0, zero_mul]
  · show (a * a).snd = 0
    rw [TrivSqZeroExt.snd_mul, h0]
    simp

omit [Field k] in
/-- Conjugating a thickening by identifications of its source and target gives a thickening. -/
theorem isThickening_map_eqToHom_comp_comp {U V W Y : BigFppfOver B integerBase hZ} (h₁ : U = V)
    (g : V ⟶ W) (h₂ : W = Y)
    (hg : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B integerBase hZ).map g)) :
    Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map (eqToHom h₁ ≫ g ≫ eqToHom h₂)) := by
  subst h₁ h₂
  simpa using hg

/-- The morphism of base schemes from `x` to a lift of `x` to `Spec k[M]` is a thickening. -/
theorem isThickening_lift_hom {M : SiteModule k B} (t : Lift x hx M) :
    Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map t.1.hom.baseMap) := by
  have := liftAlong_isHomLift (curvesProjectionOver B hZ) x (arrow x hx M) t
  have h := IsHomLift.fac' (curvesProjectionOver B hZ) (arrow x hx M) t.1.hom
  change t.1.hom.baseMap = _ at h
  rw [h]
  simp only [arrow, Category.assoc, eqToHom_trans_assoc]
  exact isThickening_map_eqToHom_comp_comp _ _ _
    (isThickening_toScheme_squareZeroArrow (hk := hk) (toS := toS) M)

/-- The total space of a lift of `x` to `Spec k[M]` is representable. -/
theorem isRepresentable_total_lift {M : SiteModule k B} (t : Lift x hx M) :
    t.1.right.total.obj.IsRepresentable :=
  CurveFamily.isRepresentable_total_of_hom t.1.hom (isThickening_lift_hom x hx t)
    (isRepresentable_total x hx)

omit [Field k] in
/-- A cocartesian square of schemes conjugated by identifications of its corners. -/
theorem isPushout_map_of_eqToHom_conj {U₀ U₁ U₂ U₃ V₀ V₁ V₂ V₃ : BigFppfOver B integerBase hZ}
    (e₀ : U₀ = V₀) (e₁ : U₁ = V₁) (e₂ : U₂ = V₂) (e₃ : U₃ = V₃)
    {i : V₀ ⟶ V₂} {f : V₀ ⟶ V₁} {g : V₂ ⟶ V₃} {h : V₁ ⟶ V₃}
    (H : IsPushout ((BigFppfOver.toScheme B integerBase hZ).map i)
      ((BigFppfOver.toScheme B integerBase hZ).map f)
      ((BigFppfOver.toScheme B integerBase hZ).map g)
      ((BigFppfOver.toScheme B integerBase hZ).map h))
    {i' : U₀ ⟶ U₂} {f' : U₀ ⟶ U₁} {g' : U₂ ⟶ U₃} {h' : U₁ ⟶ U₃}
    (hi : i' = eqToHom e₀ ≫ i ≫ eqToHom e₂.symm) (hf : f' = eqToHom e₀ ≫ f ≫ eqToHom e₁.symm)
    (hg : g' = eqToHom e₂ ≫ g ≫ eqToHom e₃.symm) (hh : h' = eqToHom e₁ ≫ h ≫ eqToHom e₃.symm) :
    IsPushout ((BigFppfOver.toScheme B integerBase hZ).map i')
      ((BigFppfOver.toScheme B integerBase hZ).map f')
      ((BigFppfOver.toScheme B integerBase hZ).map g')
      ((BigFppfOver.toScheme B integerBase hZ).map h') := by
  subst e₀ e₁ e₂ e₃
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hi hf hg hh
  subst hi hf hg hh
  exact H

omit [Field k] in
/-- Two morphisms of families of curves lying over the same morphism of the base have the same
morphism of base schemes. -/
theorem baseMap_eq_of_isHomLift {y y' : CurveFamily B hZ} {U V : BigFppfOver B integerBase hZ}
    (a : U ⟶ V) {f g : y ⟶ y'} (hf : (curvesProjectionOver B hZ).IsHomLift a f)
    (hg : (curvesProjectionOver B hZ).IsHomLift a g) : f.baseMap = g.baseMap :=
  (IsHomLift.fac' (curvesProjectionOver B hZ) a f).trans
    (IsHomLift.fac' (curvesProjectionOver B hZ) a g).symm

section Product

variable (M N : SiteModule k B)

/-- The arrow `Spec k[M] ⟶ Spec k[M × N]`, as a morphism of arrows out of the base of `x`. -/
abbrev baseFst : (Under.mk (arrow x hx M) : Under ((curvesProjectionOver B hZ).obj x)) ⟶
    Under.mk (arrow x hx (siteModuleProd k B hk M N)) :=
  Under.homMk (squareZeroOverMap k B integerBase hZ toS (siteModuleFst k B hk M N)) (by
    change (eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk M) ≫ _ =
      eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk (siteModuleProd k B hk M N)
    rw [Category.assoc, squareZeroArrow_naturality])

/-- The arrow `Spec k[N] ⟶ Spec k[M × N]`, as a morphism of arrows out of the base of `x`. -/
abbrev baseSnd : (Under.mk (arrow x hx N) : Under ((curvesProjectionOver B hZ).obj x)) ⟶
    Under.mk (arrow x hx (siteModuleProd k B hk M N)) :=
  Under.homMk (squareZeroOverMap k B integerBase hZ toS (siteModuleSnd k B hk M N)) (by
    change (eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk N) ≫ _ =
      eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk (siteModuleProd k B hk M N)
    rw [Category.assoc, squareZeroArrow_naturality])

omit hx in
/-- `k[M × N]` is the fibre product `k[M] ×_k k[N]`. -/
theorem isPullback_squareZeroRingMap :
    IsPullback (squareZeroRingMap k B (siteModuleFst k B hk M N))
      (squareZeroRingMap k B (siteModuleSnd k B hk M N))
      (squareZeroProjection k M.obj) (squareZeroProjection k N.obj) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext z
    show (TrivSqZeroExt.map (LinearMap.fst k M.obj N.obj) z).fst =
      (TrivSqZeroExt.map (LinearMap.snd k M.obj N.obj) z).fst
    exact (TrivSqZeroExt.fst_map _ z).trans (TrivSqZeroExt.fst_map _ z).symm
  · intro a b hab
    change TrivSqZeroExt.map (LinearMap.fst k M.obj N.obj) a =
        TrivSqZeroExt.map (LinearMap.fst k M.obj N.obj) b ∧
      TrivSqZeroExt.map (LinearMap.snd k M.obj N.obj) a =
        TrivSqZeroExt.map (LinearMap.snd k M.obj N.obj) b at hab
    have hfst : TrivSqZeroExt.fst a = TrivSqZeroExt.fst b :=
      ((TrivSqZeroExt.fst_map _ a).symm.trans
        (congrArg TrivSqZeroExt.fst hab.1)).trans (TrivSqZeroExt.fst_map _ b)
    have h₁ : (TrivSqZeroExt.snd a).1 = (TrivSqZeroExt.snd b).1 :=
      ((TrivSqZeroExt.snd_map _ a).symm.trans
        (congrArg TrivSqZeroExt.snd hab.1)).trans (TrivSqZeroExt.snd_map _ b)
    have h₂ : (TrivSqZeroExt.snd a).2 = (TrivSqZeroExt.snd b).2 :=
      ((TrivSqZeroExt.snd_map _ a).symm.trans
        (congrArg TrivSqZeroExt.snd hab.2)).trans (TrivSqZeroExt.snd_map _ b)
    exact TrivSqZeroExt.ext hfst (Prod.ext h₁ h₂)
  · intro a b hab
    change a.fst = b.fst at hab
    refine ⟨⟨a.fst, (a.snd, b.snd)⟩, ?_, ?_⟩
    · show TrivSqZeroExt.map (LinearMap.fst k M.obj N.obj) _ = a
      exact TrivSqZeroExt.ext (TrivSqZeroExt.fst_map _ _) (TrivSqZeroExt.snd_map _ _)
    · show TrivSqZeroExt.map (LinearMap.snd k M.obj N.obj) _ = b
      exact TrivSqZeroExt.ext ((TrivSqZeroExt.fst_map _ _).trans hab)
        (TrivSqZeroExt.snd_map _ _)

omit hx in
/-- `Spec k[M × N]` is the pushout `Spec k[M] ⨿_{Spec k} Spec k[N]` (Stacks 0ET0). -/
theorem isPushout_toScheme_squareZero :
    IsPushout ((BigFppfOver.toScheme B integerBase hZ).map
        (squareZeroArrow k B integerBase hZ toS hk N))
      ((BigFppfOver.toScheme B integerBase hZ).map (squareZeroArrow k B integerBase hZ toS hk M))
      ((BigFppfOver.toScheme B integerBase hZ).map
        (squareZeroOverMap k B integerBase hZ toS (siteModuleSnd k B hk M N)))
      ((BigFppfOver.toScheme B integerBase hZ).map
        (squareZeroOverMap k B integerBase hZ toS (siteModuleFst k B hk M N))) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective
    (squareZeroProjection k N.obj) (squareZeroProjection k M.obj)
    (squareZeroRingMap k B (siteModuleFst k B hk M N))
    (squareZeroRingMap k B (siteModuleSnd k B hk M N))
    (isPullback_squareZeroRingMap M N) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)

variable {M N}

/-- The base of a lift of `x` to `Spec k[L]` is `Spec k[L]`. -/
private theorem lift_right_base {L : SiteModule k B} (b : Lift x hx L) :
    b.1.right.base = squareZeroOver k B integerBase hZ toS L :=
  liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx L) b

/-- The morphism of base schemes from `x` to a lift of `x` to `Spec k[L]` is the square-zero
immersion `Spec k ⟶ Spec k[L]`, up to identification of the bases. -/
theorem baseMap_lift_hom {L : SiteModule k B} (t : Lift x hx L) :
    t.1.hom.baseMap = eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk L ≫
      eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx L) t).symm := by
  have := liftAlong_isHomLift (curvesProjectionOver B hZ) x (arrow x hx L) t
  refine (IsHomLift.fac' (curvesProjectionOver B hZ) (arrow x hx L) t.1.hom).trans ?_
  simp

/-- A morphism of lifts lying over a morphism of arrows `β` has morphism of base schemes
`β.right`, up to identification of the bases. -/
theorem baseMap_right_of_isHomLift {L L' : SiteModule k B} {b : Lift x hx L} {c : Lift x hx L'}
    {β : (Under.mk (arrow x hx L) : Under ((curvesProjectionOver B hZ).obj x)) ⟶
      Under.mk (arrow x hx L')} {φ : b.1 ⟶ c.1}
    (hφ : (Under.post (curvesProjectionOver B hZ)).IsHomLift β φ) :
    φ.right.baseMap =
      eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx L) b) ≫ β.right ≫
        eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx L') c).symm := by
  have := underPost_isHomLift_right (curvesProjectionOver B hZ) β φ hφ
  exact IsHomLift.fac' (curvesProjectionOver B hZ) β.right φ.right

/-- The morphism of base schemes of a morphism of lifts over `baseFst` is `squareZeroOverMap` of
`siteModuleFst`, up to identification of the bases. -/
private theorem baseMap_right_fst {c : Lift x hx (siteModuleProd k B hk M N)}
    {b : Lift x hx M} {φ : b.1 ⟶ c.1}
    (hφ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseFst x hx M N) φ)
    (e : b.1.right.base = squareZeroOver k B integerBase hZ toS M)
    (e' : c.1.right.base = squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N)) :
    φ.right.baseMap = eqToHom e ≫
      squareZeroOverMap k B integerBase hZ toS (siteModuleFst k B hk M N) ≫ eqToHom e'.symm := by
  have h := baseMap_right_of_isHomLift (L := M) (L' := siteModuleProd k B hk M N) (b := b)
    (c := c) (β := baseFst x hx M N) x hx hφ
  exact h

/-- The morphism of base schemes of a morphism of lifts over `baseSnd` is `squareZeroOverMap` of
`siteModuleSnd`, up to identification of the bases. -/
private theorem baseMap_right_snd {c : Lift x hx (siteModuleProd k B hk M N)}
    {b : Lift x hx N} {φ : b.1 ⟶ c.1}
    (hφ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseSnd x hx M N) φ)
    (e : b.1.right.base = squareZeroOver k B integerBase hZ toS N)
    (e' : c.1.right.base = squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N)) :
    φ.right.baseMap = eqToHom e ≫
      squareZeroOverMap k B integerBase hZ toS (siteModuleSnd k B hk M N) ≫ eqToHom e'.symm := by
  have h := baseMap_right_of_isHomLift (L := N) (L' := siteModuleProd k B hk M N) (b := b)
    (c := c) (β := baseSnd x hx M N) x hx hφ
  exact h

/-- **A lift over `k[M × N]` is glued from its two restrictions.** -/
theorem isPushout_lift {c : Lift x hx (siteModuleProd k B hk M N)} {b₁ : Lift x hx M}
    {b₂ : Lift x hx N} {φ₁ : b₁.1 ⟶ c.1}
    (hφ₁ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseFst x hx M N) φ₁)
    {φ₂ : b₂.1 ⟶ c.1}
    (hφ₂ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseSnd x hx M N) φ₂) :
    IsPushout ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx b₂) (isRepresentable_total x hx) b₂.1.hom))
      ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx b₁) (isRepresentable_total x hx) b₁.1.hom))
      ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx c) (isRepresentable_total_lift x hx b₂) φ₂.right))
      ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx c) (isRepresentable_total_lift x hx b₁) φ₁.right)) := by
  have := (isThickening_lift_hom x hx b₁).1
  have e₁ := lift_right_base x hx b₁
  have e₂ := lift_right_base x hx b₂
  have e₃ := lift_right_base x hx c
  have hi := baseMap_lift_hom x hx b₂
  have hf := baseMap_lift_hom x hx b₁
  have hg := baseMap_right_snd x hx hφ₂ e₂ e₃
  have hh := baseMap_right_fst x hx hφ₁ e₁ e₃
  have hpo := isPushout_map_of_eqToHom_conj hx e₁ e₂ e₃ (isPushout_toScheme_squareZero M N)
    hi hf hg hh
  exact CurveFamily.isPushout_toScheme_totalSiteMap _ _ _ _ b₁.1.hom b₂.1.hom φ₁.right φ₂.right
    ((Under.w φ₁).trans (Under.w φ₂).symm) (isThickening_lift_hom x hx b₂) hpo

omit [Field k] in
/-- The morphism of total schemes of a composite of families of curves is the composite of the
morphisms of total schemes. -/
theorem toScheme_map_totalSiteMap_comp {y₀ y₁ y₂ : CurveFamily B hZ}
    (h₀ : y₀.total.obj.IsRepresentable) (h₁ : y₁.total.obj.IsRepresentable)
    (h₂ : y₂.total.obj.IsRepresentable) (f : y₀ ⟶ y₁) (g : y₁ ⟶ y₂) :
    (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap h₁ h₀ f) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap h₂ h₁ g) =
        (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap h₂ h₀ (f ≫ g)) := by
  rw [← Functor.map_comp, CurveFamily.totalSiteMap_comp]

omit [Field k] in
/-- The morphism of total schemes of the identity of a family of curves is the identity. -/
theorem toScheme_map_totalSiteMap_id {y : CurveFamily B hZ} (h : y.total.obj.IsRepresentable) :
    (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap h h (𝟙 y)) = 𝟙 _ := by
  rw [CurveFamily.totalSiteMap_id, CategoryTheory.Functor.map_id]

omit [Field k] in
/-- The morphism of total schemes of a morphism of families of curves commutes with the
structure morphisms to the base schemes. -/
theorem toScheme_map_totalSiteMap_toBase {y y' : CurveFamily B hZ}
    (h : y.total.obj.IsRepresentable) (h' : y'.total.obj.IsRepresentable) (f : y ⟶ y') :
    (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap h' h f) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteToBase h') =
        (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteToBase h) ≫
          (BigFppfOver.toScheme B integerBase hZ).map f.baseMap := by
  rw [← Functor.map_comp, ← Functor.map_comp, (CurveFamily.isPullback_totalSite h' h f).w]

/-- A morphism of lifts of `x` to `Spec k[L]` induces the identity on base schemes, up to
identification of the bases. -/
theorem baseMap_of_fiber_hom {L : SiteModule k B} {b b' : Lift x hx L} (θ : b ⟶ b') :
    θ.1.right.baseMap =
      eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx L) b) ≫
        eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx L) b').symm := by
  have := liftAlong_morphism_isHomLift (curvesProjectionOver B hZ) x (arrow x hx L) θ
  refine (IsHomLift.fac' (curvesProjectionOver B hZ)
    (𝟙 (squareZeroOver k B integerBase hZ toS L)) θ.1.right).trans ?_
  simp

section HomExtension

variable {c c' : Lift x hx (siteModuleProd k B hk M N)} {b₁ b₁' : Lift x hx M}
  {b₂ b₂' : Lift x hx N} {φ₁ : b₁.1 ⟶ c.1}
  (hφ₁ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseFst x hx M N) φ₁)
  {φ₂ : b₂.1 ⟶ c.1}
  (hφ₂ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseSnd x hx M N) φ₂)
  {φ₁' : b₁'.1 ⟶ c'.1}
  (hφ₁' : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseFst x hx M N) φ₁')
  {φ₂' : b₂'.1 ⟶ c'.1}
  (hφ₂' : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseSnd x hx M N) φ₂')

include hφ₁ hφ₂ in
/-- The morphism of total schemes glued from morphisms of the two restrictions. -/
def glueTotal (θ₁ : b₁.1 ⟶ b₁'.1) (θ₂ : b₂.1 ⟶ b₂'.1) :
    (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite
        (isRepresentable_total_lift x hx c)) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.totalSite
          (isRepresentable_total_lift x hx c')) :=
  (isPushout_lift x hx hφ₁ hφ₂).desc
    ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx b₂') (isRepresentable_total_lift x hx b₂)
        θ₂.right) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
          (isRepresentable_total_lift x hx c') (isRepresentable_total_lift x hx b₂')
        φ₂'.right))
    ((BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx b₁') (isRepresentable_total_lift x hx b₁)
        θ₁.right) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
          (isRepresentable_total_lift x hx c') (isRepresentable_total_lift x hx b₁')
        φ₁'.right)) (by
    rw [toScheme_map_totalSiteMap_comp, toScheme_map_totalSiteMap_comp,
      toScheme_map_totalSiteMap_comp, toScheme_map_totalSiteMap_comp]
    congr 2
    rw [← Category.assoc, ← Category.assoc, Under.w θ₂, Under.w θ₁, Under.w φ₂',
      Under.w φ₁'])

/-- `glueTotal` restricts on the total scheme of `b₂` to the morphism induced by `θ₂`. -/
theorem inl_glueTotal (θ₁ : b₁.1 ⟶ b₁'.1) (θ₂ : b₂.1 ⟶ b₂'.1) :
    (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx c) (isRepresentable_total_lift x hx b₂)
        φ₂.right) ≫ glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁ θ₂ =
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
          (isRepresentable_total_lift x hx b₂') (isRepresentable_total_lift x hx b₂)
        θ₂.right) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
          (isRepresentable_total_lift x hx c') (isRepresentable_total_lift x hx b₂')
        φ₂'.right) :=
  (isPushout_lift x hx hφ₁ hφ₂).inl_desc _ _ _

/-- `glueTotal` restricts on the total scheme of `b₁` to the morphism induced by `θ₁`. -/
theorem inr_glueTotal (θ₁ : b₁.1 ⟶ b₁'.1) (θ₂ : b₂.1 ⟶ b₂'.1) :
    (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
        (isRepresentable_total_lift x hx c) (isRepresentable_total_lift x hx b₁)
        φ₁.right) ≫ glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁ θ₂ =
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
          (isRepresentable_total_lift x hx b₁') (isRepresentable_total_lift x hx b₁)
        θ₁.right) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
          (isRepresentable_total_lift x hx c') (isRepresentable_total_lift x hx b₁')
        φ₁'.right) :=
  (isPushout_lift x hx hφ₁ hφ₂).inr_desc _ _ _

/-- The morphism of total schemes glued from `inv θ₁` and `inv θ₂` is a right inverse of the one
glued from `θ₁` and `θ₂`. -/
theorem glueTotal_comp_glueTotal_inv (θ₁ : b₁.1 ⟶ b₁'.1) (θ₂ : b₂.1 ⟶ b₂'.1) [IsIso θ₁]
    [IsIso θ₂] :
    glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁ θ₂ ≫
      glueTotal x hx hφ₁' hφ₂' (φ₁' := φ₁) (φ₂' := φ₂) (inv θ₁) (inv θ₂) = 𝟙 _ := by
  apply (isPushout_lift x hx hφ₁ hφ₂).hom_ext
  · rw [← Category.assoc, inl_glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁ θ₂,
      Category.assoc,
      inl_glueTotal x hx hφ₁' hφ₂' (φ₁' := φ₁) (φ₂' := φ₂) (inv θ₁) (inv θ₂), ← Category.assoc,
      toScheme_map_totalSiteMap_comp, ← Under.comp_right, IsIso.hom_inv_id, Under.id_right,
      toScheme_map_totalSiteMap_id, Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, inr_glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁ θ₂,
      Category.assoc,
      inr_glueTotal x hx hφ₁' hφ₂' (φ₁' := φ₁) (φ₂' := φ₂) (inv θ₁) (inv θ₂), ← Category.assoc,
      toScheme_map_totalSiteMap_comp, ← Under.comp_right, IsIso.hom_inv_id, Under.id_right,
      toScheme_map_totalSiteMap_id, Category.id_comp, Category.comp_id]

include hφ₁' hφ₂' in
/-- The morphism of total schemes glued from isomorphisms of the two restrictions is an
isomorphism. -/
theorem isIso_glueTotal (θ₁ : b₁.1 ⟶ b₁'.1) (θ₂ : b₂.1 ⟶ b₂'.1) [IsIso θ₁] [IsIso θ₂] :
    IsIso (glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁ θ₂) :=
  ⟨glueTotal x hx hφ₁' hφ₂' (φ₁' := φ₁) (φ₂' := φ₂) (inv θ₁) (inv θ₂),
    glueTotal_comp_glueTotal_inv x hx hφ₁ hφ₂ hφ₁' hφ₂' θ₁ θ₂,
    by simpa using glueTotal_comp_glueTotal_inv x hx hφ₁' hφ₂' hφ₁ hφ₂ (inv θ₁) (inv θ₂)⟩

omit [Field k] in
/-- A morphism of lifts lies over a morphism of arrows out of the base of `x` as soon as its
morphism of families of curves lies over the morphism of targets. -/
theorem underPost_isHomLift_of_isHomLift_right {U V : Under ((curvesProjectionOver B hZ).obj x)}
    {s : (Under.post (curvesProjectionOver B hZ)).Fiber U}
    {t : (Under.post (curvesProjectionOver B hZ)).Fiber V} (g : U ⟶ V) (m : s.1 ⟶ t.1)
    (hm : (curvesProjectionOver B hZ).IsHomLift g.right m.right) :
    (Under.post (curvesProjectionOver B hZ)).IsHomLift g m := by
  refine IsHomLift.of_fac' (Under.post (curvesProjectionOver B hZ)) _ _ s.2 t.2 ?_
  apply Under.UnderMorphism.ext
  have := hm
  simp only [Under.comp_right, Under.eqToHom_right, Under.post_map, Under.homMk_right]
  rw [IsHomLift.fac' (curvesProjectionOver B hZ) g.right m.right]

include hφ₁ hφ₂ hφ₁' hφ₂' in
/-- **Morphisms of lifts over `k[M × N]` are glued from their two restrictions.** -/
theorem existsUnique_fiberHom (θ₁ : b₁ ⟶ b₁') (θ₂ : b₂ ⟶ b₂') :
    ∃! θ : c ⟶ c', θ₁.1 ≫ φ₁' = φ₁ ≫ θ.1 ∧ θ₂.1 ≫ φ₂' = φ₂ ≫ θ.1 := by
  have hq := underPost_isFiberedInGroupoids (curvesProjectionOver B hZ)
    CurveDeformation.curvesProjectionOver_isFiberedInGroupoids x
  have : IsIso θ₁.1 := isIso_of_isHomLift_id_fibered _ hq θ₁.1 θ₁.2
  have : IsIso θ₂.1 := isIso_of_isHomLift_id_fibered _ hq θ₂.1 θ₂.2
  set g := glueTotal x hx hφ₁ hφ₂ (φ₁' := φ₁') (φ₂' := φ₂') θ₁.1 θ₂.1 with hgdef
  have : IsIso g := isIso_glueTotal x hx hφ₁ hφ₂ hφ₁' hφ₂' θ₁.1 θ₂.1
  have e₂ := lift_right_base x hx b₂
  have e₂' := lift_right_base x hx b₂'
  have e₁ := lift_right_base x hx b₁
  have e₁' := lift_right_base x hx b₁'
  have e₃ := lift_right_base x hx c
  have e₃' := lift_right_base x hx c'
  have hθ₁b : θ₁.1.right.baseMap = eqToHom e₁ ≫ eqToHom e₁'.symm := baseMap_of_fiber_hom x hx θ₁
  have hθ₂b : θ₂.1.right.baseMap = eqToHom e₂ ≫ eqToHom e₂'.symm := baseMap_of_fiber_hom x hx θ₂
  have hφ₁b := baseMap_right_fst x hx hφ₁ e₁ e₃
  have hφ₂b := baseMap_right_snd x hx hφ₂ e₂ e₃
  have hφ₁'b := baseMap_right_fst x hx hφ₁' e₁' e₃'
  have hφ₂'b := baseMap_right_snd x hx hφ₂' e₂' e₃'
  let bm : c.1.right.base ⟶ c'.1.right.base := eqToHom (e₃.trans e₃'.symm)
  have hcomm : g ≫ (BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx c')) =
      (BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx c)) ≫
        (BigFppfOver.toScheme B integerBase hZ).map bm := by
    apply (isPushout_lift x hx hφ₁ hφ₂).hom_ext
    · rw [← Category.assoc, hgdef, inl_glueTotal, Category.assoc, toScheme_map_totalSiteMap_toBase,
        ← Category.assoc, toScheme_map_totalSiteMap_toBase, Category.assoc,
        ← Category.assoc ((BigFppfOver.toScheme B integerBase hZ).map
          (CurveFamily.totalSiteMap _ _ φ₂.right)), toScheme_map_totalSiteMap_toBase,
              Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, hθ₂b, hφ₂'b, hφ₂b]
      simp [bm]
    · rw [← Category.assoc, hgdef, inr_glueTotal, Category.assoc, toScheme_map_totalSiteMap_toBase,
        ← Category.assoc, toScheme_map_totalSiteMap_toBase, Category.assoc,
        ← Category.assoc ((BigFppfOver.toScheme B integerBase hZ).map
          (CurveFamily.totalSiteMap _ _ φ₁.right)), toScheme_map_totalSiteMap_toBase,
              Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, hθ₁b, hφ₁'b, hφ₁b]
      simp [bm]
  have hpb : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx c)))
      ((BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx c')))
      ((BigFppfOver.toScheme B integerBase hZ).map bm) :=
    IsPullback.of_horiz_isIso ⟨hcomm⟩
  have hxr := isRepresentable_total x hx
  have hcr := isRepresentable_total_lift x hx c
  have hcr' := isRepresentable_total_lift x hx c'
  let Θ : c.1.right ⟶ c'.1.right := CurveFamily.homOfToScheme hcr hcr' bm g hpb
  have hΘt : (BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteMap hcr' hcr Θ) = g := by
    rw [CurveFamily.totalSiteMap_homOfToScheme]
    rfl
  have hc₁ := Under.w φ₁
  have hc₁' := Under.w φ₁'
  have hcb : c.1.hom.baseMap = eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk _ ≫
      eqToHom e₃.symm := baseMap_lift_hom x hx c
  have hcb' : c'.1.hom.baseMap = eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk _ ≫
      eqToHom e₃'.symm := baseMap_lift_hom x hx c'
  have hw : c.1.hom ≫ Θ = c'.1.hom := by
    apply CurveFamily.hom_ext_of_toScheme hxr hcr'
    · show c.1.hom.baseMap ≫ bm = c'.1.hom.baseMap
      rw [hcb, hcb']
      show (eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk _ ≫ eqToHom e₃.symm) ≫
        eqToHom (e₃.trans e₃'.symm) = _
      rw [Category.assoc, Category.assoc, eqToHom_trans]
    · rw [← toScheme_map_totalSiteMap_comp hxr hcr hcr', hΘt, ← hc₁,
        ← toScheme_map_totalSiteMap_comp hxr (isRepresentable_total_lift x hx b₁) hcr,
        Category.assoc, hgdef, inr_glueTotal, ← hc₁', ← Under.w θ₁.1,
        toScheme_map_totalSiteMap_comp, toScheme_map_totalSiteMap_comp, Category.assoc]
  have hΘlift : (curvesProjectionOver B hZ).IsHomLift
      (Under.Hom.right (𝟙 (Under.mk (arrow x hx (siteModuleProd k B hk M N))))) Θ := by
    refine IsHomLift.of_fac' (curvesProjectionOver B hZ) _ Θ e₃ e₃' ?_
    show eqToHom (e₃.trans e₃'.symm) = eqToHom e₃ ≫ 𝟙 _ ≫ eqToHom e₃'.symm
    simp
  let θ : c ⟶ c' := ⟨Under.homMk Θ hw, underPost_isHomLift_of_isHomLift_right x _ _ hΘlift⟩
  have key₁ : θ₁.1 ≫ φ₁' = φ₁ ≫ θ.1 := by
    apply Under.UnderMorphism.ext
    apply CurveFamily.hom_ext_of_toScheme (isRepresentable_total_lift x hx b₁) hcr'
    · show θ₁.1.right.baseMap ≫ φ₁'.right.baseMap = φ₁.right.baseMap ≫ bm
      rw [hθ₁b, hφ₁'b, hφ₁b]
      simp [bm]
    · show (BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteMap _ _ (θ₁.1.right ≫ φ₁'.right)) =
        (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ (φ₁.right ≫ Θ))
      rw [← toScheme_map_totalSiteMap_comp _ (isRepresentable_total_lift x hx b₁') hcr',
        ← toScheme_map_totalSiteMap_comp _ hcr hcr', hΘt, hgdef, inr_glueTotal]
  have key₂ : θ₂.1 ≫ φ₂' = φ₂ ≫ θ.1 := by
    apply Under.UnderMorphism.ext
    apply CurveFamily.hom_ext_of_toScheme (isRepresentable_total_lift x hx b₂) hcr'
    · show θ₂.1.right.baseMap ≫ φ₂'.right.baseMap = φ₂.right.baseMap ≫ bm
      rw [hθ₂b, hφ₂'b, hφ₂b]
      simp [bm]
    · show (BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteMap _ _ (θ₂.1.right ≫ φ₂'.right)) =
        (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap _ _ (φ₂.right ≫ Θ))
      rw [← toScheme_map_totalSiteMap_comp _ (isRepresentable_total_lift x hx b₂') hcr',
        ← toScheme_map_totalSiteMap_comp _ hcr hcr', hΘt, hgdef, inl_glueTotal]
  refine ⟨θ, ⟨key₁, key₂⟩, fun θ' ⟨h₁, h₂⟩ => ?_⟩
  apply Functor.Fiber.hom_ext
  apply Under.UnderMorphism.ext
  apply CurveFamily.hom_ext_of_toScheme hcr hcr'
  · exact (baseMap_of_fiber_hom x hx θ').trans (eqToHom_trans _ _)
  · show (BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteMap hcr' hcr θ'.1.right) =
      (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap hcr' hcr Θ)
    rw [hΘt]
    apply (isPushout_lift x hx hφ₁ hφ₂).hom_ext
    · rw [hgdef, inl_glueTotal, toScheme_map_totalSiteMap_comp, toScheme_map_totalSiteMap_comp,
        ← Under.comp_right, ← Under.comp_right, h₂]
    · rw [hgdef, inr_glueTotal, toScheme_map_totalSiteMap_comp, toScheme_map_totalSiteMap_comp,
        ← Under.comp_right, ← Under.comp_right, h₁]

end HomExtension

/-- **Restriction of endomorphisms of a lift over `k[M × N]` to the two factors is bijective.** -/
theorem fiberEndRestrict_pair_bijective {c : Lift x hx (siteModuleProd k B hk M N)}
    {b₁ : Lift x hx M} {b₂ : Lift x hx N} {φ₁ : b₁.1 ⟶ c.1}
    (hφ₁ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseFst x hx M N) φ₁)
    {φ₂ : b₂.1 ⟶ c.1}
    (hφ₂ : (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseSnd x hx M N) φ₂) :
    let hq := underPost_isFiberedInGroupoids (curvesProjectionOver B hZ)
      CurveDeformation.curvesProjectionOver_isFiberedInGroupoids x
    Function.Bijective (fun θ : c ⟶ c =>
      (fiberEndRestrict (Under.post (curvesProjectionOver B hZ)) hq φ₁ hφ₁ θ,
        fiberEndRestrict (Under.post (curvesProjectionOver B hZ)) hq φ₂ hφ₂ θ)) := by
  intro hq
  refine ⟨fun θ θ' h => ?_, fun ⟨θ₁, θ₂⟩ => ?_⟩
  · have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp only at h₁ h₂
    obtain ⟨θ₀, -, huniq⟩ := existsUnique_fiberHom x hx hφ₁ hφ₂ hφ₁ hφ₂
      (fiberEndRestrict (Under.post (curvesProjectionOver B hZ)) hq φ₁ hφ₁ θ)
      (fiberEndRestrict (Under.post (curvesProjectionOver B hZ)) hq φ₂ hφ₂ θ)
    have hθ := huniq θ ⟨fiberEndRestrict_fac _ hq φ₁ hφ₁ θ, fiberEndRestrict_fac _ hq φ₂ hφ₂ θ⟩
    have hθ' := huniq θ' ⟨h₁ ▸ fiberEndRestrict_fac _ hq φ₁ hφ₁ θ',
      h₂ ▸ fiberEndRestrict_fac _ hq φ₂ hφ₂ θ'⟩
    exact hθ.trans hθ'.symm
  · obtain ⟨θ, ⟨h₁, h₂⟩, -⟩ := existsUnique_fiberHom x hx hφ₁ hφ₂ hφ₁ hφ₂ θ₁ θ₂
    exact ⟨θ, Prod.ext (fiberEndRestrict_eq _ hq φ₁ hφ₁ θ θ₁ h₁).symm
      (fiberEndRestrict_eq _ hq φ₂ hφ₂ θ θ₂ h₂).symm⟩

/-- **The infinitesimal automorphisms of a family of curves over a field turn products of
modules into products of sets.** -/
theorem infinitesimalAutomorphismSetFunctor_product_bijective
    (hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids) :
    Function.Bijective (fun θ : (infinitesimalAutomorphismSetFunctor k B integerBase hZ toS hk
        (curvesProjectionOver B hZ) x hx hp).obj (siteModuleProd k B hk M N) =>
      ((infinitesimalAutomorphismSetFunctor k B integerBase hZ toS hk
          (curvesProjectionOver B hZ) x hx hp).map (siteModuleFst k B hk M N) θ,
        (infinitesimalAutomorphismSetFunctor k B integerBase hZ toS hk
          (curvesProjectionOver B hZ) x hx hp).map (siteModuleSnd k B hk M N) θ)) := by
  let := underPost_isFibered (curvesProjectionOver B hZ) hp x
  have hφ₁ := Functor.pullbackFiberMap_isHomLift (Under.post (curvesProjectionOver B hZ))
    (liftId k B integerBase hZ toS hk (curvesProjectionOver B hZ) x hx)
    (liftBaseOverMap k B integerBase hZ toS hk (curvesProjectionOver B hZ) x hx
      (siteModuleFst k B hk M N))
  have hφ₂ := Functor.pullbackFiberMap_isHomLift (Under.post (curvesProjectionOver B hZ))
    (liftId k B integerBase hZ toS hk (curvesProjectionOver B hZ) x hx)
    (liftBaseOverMap k B integerBase hZ toS hk (curvesProjectionOver B hZ) x hx
      (siteModuleSnd k B hk M N))
  have hfun : (fun θ : (infinitesimalAutomorphismSetFunctor k B integerBase hZ toS hk
        (curvesProjectionOver B hZ) x hx hp).obj (siteModuleProd k B hk M N) =>
      ((infinitesimalAutomorphismSetFunctor k B integerBase hZ toS hk
          (curvesProjectionOver B hZ) x hx hp).map (siteModuleFst k B hk M N) θ,
        (infinitesimalAutomorphismSetFunctor k B integerBase hZ toS hk
          (curvesProjectionOver B hZ) x hx hp).map (siteModuleSnd k B hk M N) θ)) =
      (fun θ => (fiberEndRestrict (Under.post (curvesProjectionOver B hZ))
          (underPost_isFiberedInGroupoids (curvesProjectionOver B hZ) hp x) _ hφ₁ θ,
        fiberEndRestrict (Under.post (curvesProjectionOver B hZ))
          (underPost_isFiberedInGroupoids (curvesProjectionOver B hZ) hp x) _ hφ₂ θ)) :=
    funext fun θ => Prod.ext
      (infinitesimalAutomorphismSetFunctor_map k B integerBase hZ toS hk
        (curvesProjectionOver B hZ) x hx hp (siteModuleFst k B hk M N) θ)
      (infinitesimalAutomorphismSetFunctor_map k B integerBase hZ toS hk
        (curvesProjectionOver B hZ) x hx hp (siteModuleSnd k B hk M N) θ)
  rw [hfun]
  exact fiberEndRestrict_pair_bijective x hx (M := M) (N := N) hφ₁ hφ₂

end Product

end CurveLift

end AlgebraicGeometry
