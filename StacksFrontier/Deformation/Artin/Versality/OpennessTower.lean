module

public import StacksFrontier.Deformation.Artin.Versality.OpennessAtGeneralization
public import StacksFrontier.RingTheory.FibreProduct.CompatibleTuples
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness

/-!
# Glueing countably many square-zero lifting problems

Let `x` be an object of a category fibred in groupoids `𝒳` with (RS*) over the spectrum of a
`Λ`-algebra `R₀`, and for every `n : ℕ` let `(i n : y n ⟶ z n, a n : y n ⟶ x)` be a lifting
problem along a surjection `f n : A' n ⟶ A n` with square-zero kernel. Glueing by (RS*) one
problem at a time gives objects `x = x₀ ⟶ x₁ ⟶ x₂ ⟶ ⋯` over the spectra of the stages
`R₀ ×_{A 0} A' 0 ×_{A 1} ⋯ ×_{A (n-1)} A' (n-1)` of `Stacks.CompatibleTuples`, together with
arrows `z n ⟶ x (n + 1)` compatible with `i n` and `a n`. This is the system of objects of the
proof of Stacks 0CXU.

## Main results

* `Deformation.Artin.exists_glued_of_isPullback`: one glueing step, for a cartesian square of
  `Λ`-algebras.
* `Deformation.Artin.exists_tower`: the system of objects.
* `Deformation.Artin.contains_spec_compatibleTuples_limit`: the limit of the stages lies in the
  site.
* `Deformation.Artin.exists_limit_object`: under hypothesis (4) of Stacks 0CXU
  (`Deformation.Artin.IsSquareZeroEffective`), the system comes from an object over the spectrum
  of the limit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.Over.post

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity of a spectrum, as a morphism of the site induced by an algebra map. -/
theorem specAlgSiteHom_id {Λ T : Type u} [CommRing Λ] [CommRing T] [Algebra Λ T]
    (iΛ : Spec (.of Λ) ⟶ S) (hT : B.Contains (Spec (.of T))) :
    specAlgSiteHom B S hS iΛ hT hT (AlgHom.id Λ T) = 𝟙 _ := by
  apply (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
  rw [CategoryTheory.Functor.map_id]
  show Spec.map (CommRingCat.ofHom (RingHom.id T)) = 𝟙 _
  exact Spec.map_id _

/-- Composition of arrows lying over morphisms of the site induced by algebra maps. -/
theorem isHomLift_specAlgSiteHom_comp {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {Λ T T' T'' : Type u} [CommRing Λ] [CommRing T] [CommRing T']
    [CommRing T''] [Algebra Λ T] [Algebra Λ T'] [Algebra Λ T''] (iΛ : Spec (.of Λ) ⟶ S)
    {hT : B.Contains (Spec (.of T))} {hT' : B.Contains (Spec (.of T'))}
    {hT'' : B.Contains (Spec (.of T''))} {g : T' →ₐ[Λ] T} {g' : T'' →ₐ[Λ] T'}
    {a b c : X} {φ : a ⟶ b} {ψ : b ⟶ c}
    (hφ : p.IsHomLift (specAlgSiteHom B S hS iΛ hT hT' g) φ)
    (hψ : p.IsHomLift (specAlgSiteHom B S hS iΛ hT' hT'' g') ψ) :
    p.IsHomLift (specAlgSiteHom B S hS iΛ hT hT'' (g.comp g')) (φ ≫ ψ) := by
  rw [← specAlgSiteHom_comp B S hS iΛ hT hT' hT'' g g']
  exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hφ hψ

/-- **One glueing step by (RS*).** Let `P = R ×_Q T` be a cartesian square of `Λ`-algebras with
`T ⟶ Q` surjective with square-zero kernel, and let `x_Q ⟶ x_R`, `x_Q ⟶ x_T` be arrows over the
spectra of `R ⟶ Q` and `T ⟶ Q`. They are glued to an object over `Spec P`. -/
theorem exists_glued_of_isPullback {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S)
    {P R T Q : Type u} [CommRing P] [CommRing R] [CommRing T] [CommRing Q] [Algebra Λ P]
    [Algebra Λ R] [Algebra Λ T] [Algebra Λ Q]
    (hP : B.Contains (Spec (.of P))) (hR : B.Contains (Spec (.of R)))
    (hT : B.Contains (Spec (.of T))) (hQ : B.Contains (Spec (.of Q)))
    (a : P →ₐ[Λ] R) (b : P →ₐ[Λ] T) (f : R →ₐ[Λ] Q) (g : T →ₐ[Λ] Q)
    (hpb : IsPullback (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom)
      (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom))
    (hg : Function.Surjective g) (hker : RingHom.ker g.toRingHom ^ 2 = ⊥)
    {xR xT xQ : X}
    (hxR : p.obj xR = siteObject B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ))
    (hxT : p.obj xT = siteObject B S hS hT (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ))
    (sR : xQ ⟶ xR) (sT : xQ ⟶ xT)
    (hsR : p.IsHomLift (specAlgSiteHom B S hS iΛ hQ hR f) sR)
    (hsT : p.IsHomLift (specAlgSiteHom B S hS iΛ hQ hT g) sT) :
    ∃ (e : X) (_ : p.obj e =
        siteObject B S hS hP (Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ iΛ))
      (rR : xR ⟶ e) (rT : xT ⟶ e),
      p.IsHomLift (specAlgSiteHom B S hS iΛ hR hP a) rR ∧
      p.IsHomLift (specAlgSiteHom B S hS iΛ hT hP b) rT ∧ sR ≫ rR = sT ≫ rT := by
  let : p.IsFibered := hp.isFibered
  let QS := siteObject B S hS hQ (Spec.map (CommRingCat.ofHom (algebraMap Λ Q)) ≫ iΛ)
  let RS := siteObject B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ)
  let TS := siteObject B S hS hT (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ)
  let PS := siteObject B S hS hP (Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ iΛ)
  let fT := specAlgSiteHom B S hS iΛ hQ hR f
  let gT := specAlgSiteHom B S hS iΛ hQ hT g
  let iT := specAlgSiteHom B S hS iΛ hR hP a
  let jT := specAlgSiteHom B S hS iΛ hT hP b
  have hsq : fT ≫ iT = gT ≫ jT := by
    rw [specAlgSiteHom_comp, specAlgSiteHom_comp]
    congr 1
    ext t
    exact (congrArg (fun m : CommRingCat.of P ⟶ CommRingCat.of Q => m.hom t) hpb.w)
  let QQ : AlgebraicGeometry.BigAffineFppf B S hS := ⟨QS, inferInstanceAs (IsAffine (Spec _))⟩
  let RR : AlgebraicGeometry.BigAffineFppf B S hS := ⟨RS, inferInstanceAs (IsAffine (Spec _))⟩
  let TT : AlgebraicGeometry.BigAffineFppf B S hS := ⟨TS, inferInstanceAs (IsAffine (Spec _))⟩
  let PP : AlgebraicGeometry.BigAffineFppf B S hS := ⟨PS, inferInstanceAs (IsAffine (Spec _))⟩
  have hpb' : IsPullback
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk iT : RR ⟶ PP)).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk jT : TT ⟶ PP)).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk fT : QQ ⟶ RR)).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (ObjectProperty.homMk gT : QQ ⟶ TT)).appTop :=
    specMap_appTop_isPullback hpb
  have hsurj : Function.Surjective ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (ObjectProperty.homMk gT : QQ ⟶ TT)).appTop.hom :=
    specMap_appTop_surjective (CommRingCat.ofHom g.toRingHom) hg
  have hker' : RingHom.ker ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (ObjectProperty.homMk gT : QQ ⟶ TT)).appTop.hom ^ 2 = ⊥ :=
    specMap_appTop_ker_sq (CommRingCat.ofHom g.toRingHom) hker
  have hE := hRS QQ RR TT PP (ObjectProperty.homMk fT) (ObjectProperty.homMk gT)
    (ObjectProperty.homMk iT) (ObjectProperty.homMk jT)
    (by apply ObjectProperty.hom_ext; exact hsq) hpb' hsurj hker'
  have : (fiberSquareComparison p (Functor.chosenPullbacks p) fT gT iT jT hsq).IsEquivalence :=
    hE
  have : (fiberSquareComparison p (Functor.chosenPullbacks p) fT gT iT jT hsq).EssSurj :=
    inferInstance
  have := hsR
  have := hsT
  exact exists_glued_object_of_fiberSquareComparison_essSurj p hp (Functor.chosenPullbacks p)
    fT gT iT jT hsq hxR hxT sR sT

/-! ### Failed lifting problems -/

section Tower

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
  {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S)
  {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] (hR₀ : B.Contains (Spec (.of R₀)))
  (x : 𝒳.val.obj)

/-- **A lifting problem without solution** for an object `x` over `Spec R₀`, at the point
`point` of `Spec R₀`: a surjection `f : A' ⟶ A` of `Λ`-algebras with square-zero kernel, `A` local
Artinian, a map `R₀ ⟶ A` whose spectrum maps to `point`, and arrows `i : y ⟶ z`, `a : y ⟶ x` of
`𝒳` over the spectra of `f` and of `R₀ ⟶ A`, such that no `b : z ⟶ x` has `i ≫ b = a`. -/
structure FailedLift where
  /-- The target of the small extension. -/
  A : Type u
  /-- The source of the small extension. -/
  A' : Type u
  [commRingA : CommRing A]
  [commRingA' : CommRing A']
  [algebraA : Algebra Λ A]
  [algebraA' : Algebra Λ A']
  [isLocalRingA : IsLocalRing A]
  [isArtinianRingA : IsArtinianRing A]
  /-- The small extension. -/
  f : A' →ₐ[Λ] A
  surjective : Function.Surjective f
  ker_sq : RingHom.ker f.toRingHom ^ 2 = ⊥
  /-- The spectrum of `A` lies in the site. -/
  memA : B.Contains (Spec (.of A))
  /-- The spectrum of `A'` lies in the site. -/
  memA' : B.Contains (Spec (.of A'))
  /-- The map `R₀ ⟶ A`. -/
  φ : R₀ →ₐ[Λ] A
  /-- The point of `Spec R₀` under `Spec A`. -/
  point : Spec (.of R₀)
  point_eq : ∀ t, Spec.map (CommRingCat.ofHom φ.toRingHom) t = point
  /-- The object over `Spec A`. -/
  y : 𝒳.val.obj
  /-- The object over `Spec A'`. -/
  z : 𝒳.val.obj
  hy : 𝒳.val.p.obj y = siteObject B S hS memA (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
  hz : 𝒳.val.p.obj z =
    siteObject B S hS memA' (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ)
  /-- The arrow over the spectrum of the small extension. -/
  i : y ⟶ z
  hi : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ memA memA' f) i
  /-- The arrow to `x`. -/
  a : y ⟶ x
  ha : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ memA hR₀ φ) a
  not_lift : ¬ ∃ b : z ⟶ x, i ≫ b = a

attribute [instance] FailedLift.commRingA FailedLift.commRingA' FailedLift.algebraA
  FailedLift.algebraA' FailedLift.isLocalRingA FailedLift.isArtinianRingA

variable {B S hS 𝒳 iΛ hR₀ x}

variable (P : ℕ → FailedLift B S hS 𝒳 iΛ hR₀ x)

/-- The family of the maps `R₀ ⟶ A n` of a sequence of failed lifting problems. -/
abbrev towerφ (n : ℕ) : R₀ →ₐ[Λ] (P n).A := (P n).φ

/-- The family of the small extensions of a sequence of failed lifting problems. -/
abbrev towerf (n : ℕ) : (P n).A' →ₐ[Λ] (P n).A := (P n).f

/-- The spectrum of the source of a small extension of a sequence of failed lifting problems
lies in the site. -/
theorem towerMemA' (n : ℕ) : B.Contains (Spec (.of (P n).A')) := (P n).memA'

/-- The projection of a stage of a sequence of failed lifting problems to its last factor. -/
abbrev towerLast (n : ℕ) :
    Stacks.CompatibleTuples.stage (towerφ P) (towerf P) (n + 1) →ₐ[Λ] (P n).A' :=
  Stacks.CompatibleTuples.stageLast (towerφ P) (towerf P) n

/-- The arrow `z n ⟶ x (n + 1)` of the system of objects lies over the projection of the stage
`n + 1` to its last factor. -/
abbrev IsTowerLastLift (n : ℕ)
    (h : B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) (n + 1)))))
    {o : 𝒳.val.obj} (sz : (P n).z ⟶ o) : Prop :=
  𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (towerMemA' P n) h (towerLast P n)) sz

/-- The arrow `x ⟶ x n` of the system of objects lies over the projection of the stage `n` to
`R₀`. -/
abbrev IsTowerFstLift (n : ℕ)
    (h : B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))))
    {o : 𝒳.val.obj} (fx : x ⟶ o) : Prop :=
  𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ h
    (Stacks.CompatibleTuples.stageFst (towerφ P) (towerf P) n)) fx

/-- The arrow `x n ⟶ x (n + 1)` of the system of objects lies over the transition map. -/
abbrev IsTowerStepLift (n : ℕ)
    (h : B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))))
    (h' : B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) (n + 1)))))
    {o o' : 𝒳.val.obj} (st : o ⟶ o') : Prop :=
  𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ h h'
    (Stacks.CompatibleTuples.restrict (towerφ P) (towerf P) (Nat.le_succ n))) st

variable (B S hS 𝒳 iΛ hR₀ x) in
/-- The object `x` over `Spec R₀`, read over the spectrum of the stage `0`, which is `R₀`. -/
theorem exists_stageZero_object
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (h0 : B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) 0)))) :
    ∃ (x0 : 𝒳.val.obj) (_ : 𝒳.val.p.obj x0 = siteObject B S hS h0
        (Spec.map (CommRingCat.ofHom (algebraMap Λ
          (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) 0))) ≫ iΛ))
      (t0 : x ⟶ x0),
      𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ h0
        (Stacks.CompatibleTuples.stageFst (towerφ P) (towerf P) 0)) t0 := by
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let e0 := Stacks.CompatibleTuples.stageZeroEquiv (towerφ P) (towerf P)
  obtain ⟨x0, c0, hc0⟩ := hp.exists_lift
    (specAlgSiteHom B S hS iΛ h0 hR₀ e0.symm.toAlgHom) x hx
  have hx0 := IsHomLift.domain_eq p (specAlgSiteHom B S hS iΛ h0 hR₀ e0.symm.toAlgHom) c0
  have := hp.isStronglyCartesian_homLift
    (specAlgSiteHom B S hS iΛ h0 hR₀ e0.symm.toAlgHom) c0
  have : p.IsHomLift (𝟙 (siteObject B S hS hR₀
      (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))) (𝟙 x) :=
    IsHomLift.of_fac' p _ _ hx hx (by simp)
  have hid : 𝟙 (siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)) =
      specAlgSiteHom B S hS iΛ hR₀ h0 (Stacks.CompatibleTuples.stageFst (towerφ P) (towerf P) 0) ≫
        specAlgSiteHom B S hS iΛ h0 hR₀ e0.symm.toAlgHom := by
    rw [specAlgSiteHom_comp, Stacks.CompatibleTuples.stageFst_comp_stageZeroEquiv_symm,
      specAlgSiteHom_id]
  exact ⟨x0, hx0, IsStronglyCartesian.map p _ c0 hid (𝟙 x),
    IsStronglyCartesian.map_isHomLift p _ c0 hid (𝟙 x)⟩

variable (B S hS 𝒳 iΛ hR₀ x) in
/-- **One step of the system of objects.** -/
theorem exists_tower_step (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hRn : ∀ n, B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))))
    (n : ℕ) {o : 𝒳.val.obj}
    (ho : 𝒳.val.p.obj o = siteObject B S hS (hRn n) (Spec.map (CommRingCat.ofHom (algebraMap Λ
      (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))) ≫ iΛ))
    (fx : x ⟶ o)
    (hfx : IsTowerFstLift P n (hRn n) fx) :
    ∃ (o' : 𝒳.val.obj) (_ : 𝒳.val.p.obj o' = siteObject B S hS (hRn (n + 1))
        (Spec.map (CommRingCat.ofHom (algebraMap Λ
          (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) (n + 1)))) ≫ iΛ))
      (st : o ⟶ o') (sz : (P n).z ⟶ o'),
      IsTowerStepLift P n (hRn n) (hRn (n + 1)) st ∧
      IsTowerFstLift P (n + 1) (hRn (n + 1)) (fx ≫ st) ∧
      IsTowerLastLift P n (hRn (n + 1)) sz ∧ (P n).a ≫ fx ≫ st = (P n).i ≫ sz := by
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  have hsR : p.IsHomLift (specAlgSiteHom B S hS iΛ (P n).memA (hRn n)
      ((towerφ P n).comp (Stacks.CompatibleTuples.stageFst (towerφ P) (towerf P) n)))
      ((P n).a ≫ fx) :=
    isHomLift_specAlgSiteHom_comp B S hS p iΛ (P n).ha hfx
  obtain ⟨e, he, rR, rT, hrR, hrT, hcomm⟩ := exists_glued_of_isPullback B S hS p hp hRS iΛ
    (hRn (n + 1)) (hRn n) (towerMemA' P n) (P n).memA
    (Stacks.CompatibleTuples.restrict (towerφ P) (towerf P) (Nat.le_succ n))
    (towerLast P n) ((towerφ P n).comp (Stacks.CompatibleTuples.stageFst (towerφ P) (towerf P) n))
    (towerf P n) (Stacks.CompatibleTuples.isPullback_stage_succ (towerφ P) (towerf P) n)
    (P n).surjective (P n).ker_sq ho (P n).hz ((P n).a ≫ fx) (P n).i hsR (P n).hi
  have htoObj : p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ (hRn (n + 1))
      ((Stacks.CompatibleTuples.stageFst (towerφ P) (towerf P) n).comp
        (Stacks.CompatibleTuples.restrict (towerφ P) (towerf P) (Nat.le_succ n)))) (fx ≫ rR) :=
    isHomLift_specAlgSiteHom_comp B S hS p iΛ hfx hrR
  exact ⟨e, he, rR, rT, hrR, htoObj, hrT, by rw [← Category.assoc, hcomm]⟩

variable (B S hS 𝒳 iΛ hR₀ x)

/-- **The system of objects of the proof of Stacks 0CXU.** Glueing the failed lifting problems
`P n` to `x` one at a time by (RS*) gives objects `x n` over the spectra of the stages of
`Stacks.CompatibleTuples`, with arrows `x n ⟶ x (n + 1)`, `x ⟶ x n` and `z n ⟶ x (n + 1)` over the
spectra of the transition maps, the projections to `R₀` and the projections to `A' n`, such that
`a n ≫ (x ⟶ x (n + 1)) = i n ≫ (z n ⟶ x (n + 1))`. -/
theorem exists_tower (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (hRn : ∀ n, B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n)))) :
    ∃ (obj : ℕ → 𝒳.val.obj)
      (_ : ∀ n, 𝒳.val.p.obj (obj n) = siteObject B S hS (hRn n)
        (Spec.map (CommRingCat.ofHom (algebraMap Λ
          (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))) ≫ iΛ))
      (step : ∀ n, obj n ⟶ obj (n + 1)) (toObj : ∀ n, x ⟶ obj n)
      (sz : ∀ n, (P n).z ⟶ obj (n + 1)),
      (∀ n, IsTowerStepLift P n (hRn n) (hRn (n + 1)) (step n)) ∧
      (∀ n, IsTowerFstLift P n (hRn n) (toObj n)) ∧
      (∀ n, toObj (n + 1) = toObj n ≫ step n) ∧
      (∀ n, IsTowerLastLift P n (hRn (n + 1)) (sz n)) ∧
      (∀ n, (P n).a ≫ toObj (n + 1) = (P n).i ≫ sz n) := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let St : ℕ → Type _ := fun n => { s : Σ o : 𝒳.val.obj, (x ⟶ o) //
    p.obj s.1 = siteObject B S hS (hRn n)
      (Spec.map (CommRingCat.ofHom (algebraMap Λ
        (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))) ≫ iΛ) ∧
    IsTowerFstLift P n (hRn n) s.2 }
  -- the stage `0`
  obtain ⟨x0, hx0, t0, ht0⟩ := exists_stageZero_object B S hS 𝒳 iΛ hR₀ x P hx (hRn 0)
  let s0 : St 0 := ⟨⟨x0, t0⟩, hx0, ht0⟩
  -- the glueing step
  have hnext : ∀ n (s : St n), ∃ (s' : St (n + 1)) (st : s.1.1 ⟶ s'.1.1) (sz : (P n).z ⟶ s'.1.1),
      IsTowerStepLift P n (hRn n) (hRn (n + 1)) st ∧
      s'.1.2 = s.1.2 ≫ st ∧ IsTowerLastLift P n (hRn (n + 1)) sz ∧
      (P n).a ≫ s'.1.2 = (P n).i ≫ sz := by
    intro n s
    obtain ⟨e, he, st, sz, hst, hfx, hsz, hcomm⟩ :=
      exists_tower_step B S hS 𝒳 iΛ hR₀ x P hRS hRn n s.2.1 s.1.2 s.2.2
    exact ⟨⟨⟨e, s.1.2 ≫ st⟩, he, hfx⟩, st, sz, hst, rfl, hsz, hcomm⟩
  choose nxt st sz h1 h2 h3 h4 using hnext
  let stages : ∀ n, St n := fun n => Nat.rec (motive := St) s0 (fun n s => nxt n s) n
  refine ⟨fun n => (stages n).1.1, fun n => (stages n).2.1, fun n => st n (stages n),
    fun n => (stages n).1.2, fun n => sz n (stages n), fun n => h1 n (stages n),
    fun n => (stages n).2.2, fun n => h2 n (stages n), fun n => h3 n (stages n),
    fun n => h4 n (stages n)⟩

end Tower

/-! ### The limit of the system -/

section Limit

variable {Λ R₀ : Type u} [CommRing Λ] [CommRing R₀] [Algebra Λ R₀]
  {A A' : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, CommRing (A' n)] [∀ n, Algebra Λ (A n)]
  [∀ n, Algebra Λ (A' n)] (φ : ∀ n, R₀ →ₐ[Λ] A n) (f : ∀ n, A' n →ₐ[Λ] A n)

/-- **The limit of the stages lies in the site**, as soon as `Spec R₀` and every `Spec (A' n)` do:
the site is closed under countable products of rings, its cutoff being a strong limit of
uncountable cofinality. -/
theorem contains_spec_compatibleTuples_limit (hR₀ : B.Contains (Spec (.of R₀)))
    (hA' : ∀ n, B.Contains (Spec (.of (A' n)))) :
    B.Contains (Spec (.of (Stacks.CompatibleTuples.limit φ f))) := by
  let μ : Cardinal.{u} :=
    max (Spec (.of R₀)).size (⨆ n : ULift.{u} ℕ, (Spec (.of (A' n.down))).size)
  have hμ : μ < B.cutoff := max_lt hR₀ (Cardinal.iSup_lt_of_lt_cof_ord
    (by simpa using B.aleph0_lt_cutoff_cof) (fun n => hA' n.down))
  have hR₀μ : Cardinal.mk R₀ ≤ μ := by
    refine le_trans ?_ (le_max_left _ _)
    rw [Scheme.size_Spec]
    exact le_max_right _ _
  have hA'μ : ∀ n, Cardinal.mk (A' n) ≤ μ := by
    intro n
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_ciSup Cardinal.bddAbove_of_small (ULift.up n))
    rw [Scheme.size_Spec]
    exact le_max_right _ _
  have hmk : Cardinal.mk (Stacks.CompatibleTuples.limit φ f) ≤ μ ^ Cardinal.aleph0 := by
    refine (Cardinal.mk_subtype_le _).trans ?_
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_pi]
    calc Cardinal.mk R₀ * Cardinal.prod (fun n => Cardinal.mk (A' n))
        ≤ μ ^ Cardinal.aleph0 * μ ^ Cardinal.aleph0 := by
          refine mul_le_mul' (hR₀μ.trans (Cardinal.self_le_power μ Cardinal.one_le_aleph0)) ?_
          refine (Cardinal.prod_le_prod _ _ hA'μ).trans ?_
          rw [Cardinal.prod_const, Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0]
      _ = μ ^ Cardinal.aleph0 := by
          rw [← Cardinal.power_add, Cardinal.aleph0_add_aleph0]
  show (Spec (.of (Stacks.CompatibleTuples.limit φ f))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (hmk.trans_lt
    (Cardinal.power_aleph0_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hμ))

end Limit

/-! ### Effectiveness of square-zero systems -/

/-- **Hypothesis (4) of Stacks 0CXU**: systems of objects over the spectra of an inverse system of
algebras over an affine open `Spec Λ ⊆ S` as in Stacks 0CXT, whose transition maps are surjective
with square-zero kernels, are effective. This is
`Deformation.Artin.IsStronglyFormallyEffective` with "locally nilpotent" replaced by "square-zero".
-/
abbrev IsSquareZeroEffective {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (_hp : p.IsFiberedInGroupoids) : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] (chart : Spec (.of Λ) ⟶ S) [IsOpenImmersion chart]
    (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ) (cR : Cone R) (_hcR : IsLimit cR)
    (_hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (_hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥)
    (ξ : ℕ ⥤ X) (c : Cocone (ξ ⋙ p))
    (e : ∀ n : ℕ, (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj ((ξ ⋙ p).obj n) ≅
      Spec (.of (R.obj (.op n))))
    (eLimit : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)),
    (∀ {i j : ℕ} (f : i ⟶ j),
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ((ξ ⋙ p).map f) ≫ (e j).hom =
        (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op) →
    (∀ n : ℕ, (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
      (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op) →
    (eLimit.inv ≫ B.inclusion.map c.pt.hom =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap Λ cR.pt)).op ≫ chart) →
    IsEffectiveSystem p ξ c

/-- The legs of a cocone lifting a prescribed cocone lie over the legs of the latter. -/
theorem map_ι_of_mapCocone_eq {J : Type*} [Category J] {X C : Type*} [Category X] [Category C]
    (p : X ⥤ C) {ξ : J ⥤ X} {c : Cocone (ξ ⋙ p)} (d : Cocone ξ) (h : p.mapCocone d = c)
    (j : J) : p.map (d.ι.app j) = c.ι.app j ≫ eqToHom (congrArg Cocone.pt h).symm := by
  subst h
  simp

section LimitObject

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
  {Λ R₀ : Type u} [CommRing Λ] [CommRing R₀] [Algebra Λ R₀] (iΛ : Spec (.of Λ) ⟶ S)
  [IsOpenImmersion iΛ]
  {A A' : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, CommRing (A' n)] [∀ n, Algebra Λ (A n)]
  [∀ n, Algebra Λ (A' n)] (φ : ∀ n, R₀ →ₐ[Λ] A n) (f : ∀ n, A' n →ₐ[Λ] A n)

omit [IsOpenImmersion iΛ] in
/-- The arrows of a system of objects over the transition maps of the stages, composed. -/
theorem isHomLift_ofSequence_map
    (hRn : ∀ n, B.Contains (Spec (.of (Stacks.CompatibleTuples.stage φ f n))))
    (obj : ℕ → 𝒳.val.obj)
    (hobj : ∀ n, 𝒳.val.p.obj (obj n) = siteObject B S hS (hRn n)
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (Stacks.CompatibleTuples.stage φ f n))) ≫ iΛ))
    (step : ∀ n, obj n ⟶ obj (n + 1))
    (hstep : ∀ n, 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (hRn n) (hRn (n + 1))
      (Stacks.CompatibleTuples.restrict φ f (Nat.le_succ n))) (step n))
    {i j : ℕ} (h : i ≤ j) :
    𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (hRn i) (hRn j)
      (Stacks.CompatibleTuples.restrict φ f h)) ((Functor.ofSequence step).map (homOfLE h)) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [show homOfLE (le_refl i) = 𝟙 i from rfl, CategoryTheory.Functor.map_id,
      Stacks.CompatibleTuples.restrict_refl, specAlgSiteHom_id]
    exact IsHomLift.id (hobj i)
  | succ j hij ih =>
    rw [show homOfLE (hij.trans (Nat.le_succ j)) = homOfLE hij ≫ homOfLE (Nat.le_succ j) from rfl,
      CategoryTheory.Functor.map_comp, Functor.ofSequence_map_homOfLE_succ,
      ← Stacks.CompatibleTuples.restrict_comp φ f hij (Nat.le_succ j)]
    exact isHomLift_specAlgSiteHom_comp B S hS 𝒳.val.p iΛ ih (hstep j)

/-- **The limit object.** By effectiveness of square-zero systems, a system of objects over the
spectra of the stages, with arrows over the transition maps, comes from an object over the
spectrum of the limit. -/
theorem exists_limit_object
    (heff : IsSquareZeroEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hf : ∀ k, Function.Surjective (f k)) (hker : ∀ k, RingHom.ker (f k).toRingHom ^ 2 = ⊥)
    (hRn : ∀ n, B.Contains (Spec (.of (Stacks.CompatibleTuples.stage φ f n))))
    (hRlim : B.Contains (Spec (.of (Stacks.CompatibleTuples.limit φ f))))
    (obj : ℕ → 𝒳.val.obj)
    (hobj : ∀ n, 𝒳.val.p.obj (obj n) = siteObject B S hS (hRn n)
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (Stacks.CompatibleTuples.stage φ f n))) ≫ iΛ))
    (step : ∀ n, obj n ⟶ obj (n + 1))
    (hstep : ∀ n, 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (hRn n) (hRn (n + 1))
      (Stacks.CompatibleTuples.restrict φ f (Nat.le_succ n))) (step n)) :
    ∃ (ξ : 𝒳.val.obj) (_ : 𝒳.val.p.obj ξ = siteObject B S hS hRlim
        (Spec.map (CommRingCat.ofHom (algebraMap Λ (Stacks.CompatibleTuples.limit φ f))) ≫ iΛ))
      (ι : ∀ n, obj n ⟶ ξ),
      (∀ n, 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (hRn n) hRlim
        (Stacks.CompatibleTuples.proj φ f n)) (ι n)) ∧ (∀ n, step n ≫ ι (n + 1) = ι n) := by
  let p := 𝒳.val.p
  let ξ := Functor.ofSequence step
  have hobj' : ∀ n, p.obj (ξ.obj n) = siteObject B S hS (hRn n)
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (Stacks.CompatibleTuples.stage φ f n))) ≫ iΛ) :=
    hobj
  let LS := siteObject B S hS hRlim
    (Spec.map (CommRingCat.ofHom (algebraMap Λ (Stacks.CompatibleTuples.limit φ f))) ≫ iΛ)
  have hfac : ∀ {i j : ℕ} (g : i ⟶ j), p.map (ξ.map g) = eqToHom (hobj' i) ≫
      specAlgSiteHom B S hS iΛ (hRn i) (hRn j)
        (Stacks.CompatibleTuples.restrict φ f (leOfHom g)) ≫ eqToHom (hobj' j).symm := by
    intro i j g
    rw [show g = homOfLE (leOfHom g) from rfl]
    have := isHomLift_ofSequence_map B S hS 𝒳 iΛ φ f hRn obj hobj step hstep (leOfHom g)
    exact IsHomLift.fac' p _ _
  let c : Cocone (ξ ⋙ p) :=
    { pt := LS
      ι :=
        { app := fun n => eqToHom (hobj' n) ≫ specAlgSiteHom B S hS iΛ (hRn n) hRlim
            (Stacks.CompatibleTuples.proj φ f n)
          naturality := fun i j g => by
            show p.map (ξ.map g) ≫ _ = _ ≫ 𝟙 _
            simp only [hfac, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
              Category.comp_id]
            rw [specAlgSiteHom_comp, Stacks.CompatibleTuples.restrict_comp_proj] } }
  have heq1 : ∀ {i j : ℕ} (g : i ⟶ j),
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ((ξ ⋙ p).map g) ≫
          eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (hobj' j)) =
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (hobj' i)) ≫
          Scheme.Spec.map (CommRingCat.ofHom
            ((Stacks.CompatibleTuples.diagram φ f).map g.op).hom.toRingHom).op := by
    intro i j g
    show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (ξ.map g)) ≫ _ = _ ≫ Spec.map _
    simp only [hfac, CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
    rfl
  have heq2 : ∀ n : ℕ, (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫
      (Iso.refl _).hom = eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        (hobj' n)) ≫ Scheme.Spec.map (CommRingCat.ofHom
          ((Stacks.CompatibleTuples.cone φ f).π.app (.op n)).hom.toRingHom).op := by
    intro n
    show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (eqToHom (hobj' n) ≫ _) ≫ 𝟙 _ = _
    rw [CategoryTheory.Functor.map_comp, eqToHom_map, Category.comp_id]
    rfl
  obtain ⟨d, hd⟩ := heff Λ iΛ (Stacks.CompatibleTuples.diagram φ f)
    (Stacks.CompatibleTuples.cone φ f) (Stacks.CompatibleTuples.isLimitCone φ f)
    (fun g => Stacks.CompatibleTuples.surjective_restrict hf (leOfHom g.unop))
    (fun g => Stacks.CompatibleTuples.ker_restrict_sq hker (leOfHom g.unop)) ξ c
    (fun n => eqToIso (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (hobj' n)))
    (Iso.refl _) (fun g => heq1 g) heq2 (by simp; rfl)
  have hpt : p.obj d.pt = LS := congrArg Cocone.pt hd
  refine ⟨d.pt, hpt, d.ι.app, fun n => ?_, fun n => ?_⟩
  · refine IsHomLift.of_fac' p _ (d.ι.app n) (hobj n) hpt ?_
    rw [map_ι_of_mapCocone_eq p d hd n]
    rfl
  · have := d.w (homOfLE (Nat.le_succ n))
    rw [Functor.ofSequence_map_homOfLE_succ] at this
    exact this

end LimitObject

/-- The arrow `z n ⟶ x (n + 1) ⟶ ξ ⟶ x'` lies over the projection of a subalgebra of the limit to
the factor `A' n`. -/
theorem isHomLift_towerLast_comp {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)}
    {Λ : Type u} [CommRing Λ] {iΛ : Spec (.of Λ) ⟶ S}
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] {hR₀ : B.Contains (Spec (.of R₀))}
    {x : 𝒳.val.obj} (P : ℕ → FailedLift B S hS 𝒳 iΛ hR₀ x)
    (hRn : ∀ n, B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))))
    (hRlim : B.Contains (Spec (.of (Stacks.CompatibleTuples.limit (towerφ P) (towerf P)))))
    (Asub : Subalgebra Λ (Stacks.CompatibleTuples.limit (towerφ P) (towerf P)))
    (hR' : B.Contains (Spec (.of Asub)))
    (n : ℕ) {o ξ x' : 𝒳.val.obj} (sz : (P n).z ⟶ o) (ι : o ⟶ ξ) (δ : ξ ⟶ x')
    (hsz : IsTowerLastLift P n (hRn (n + 1)) sz)
    (hι : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (hRn (n + 1)) hRlim
      (Stacks.CompatibleTuples.proj (towerφ P) (towerf P) (n + 1))) ι)
    (hδ : 𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hRlim hR' Asub.val) δ) :
    𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ (P n).memA' hR'
      ((Stacks.CompatibleTuples.limitEval (towerφ P) (towerf P) n).comp Asub.val))
      (sz ≫ ι ≫ δ) := by
  have h := isHomLift_specAlgSiteHom_comp B S hS 𝒳.val.p iΛ hsz
    (isHomLift_specAlgSiteHom_comp B S hS 𝒳.val.p iΛ hι hδ)
  rw [← AlgHom.comp_assoc] at h
  exact h

/-- An arrow out of the object over `Spec (A' n)` of a failed lifting problem lies over the
spectrum of an algebra map into `A' n`. -/
abbrev IsFailedLiftZArrow {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)}
    {Λ : Type u} [CommRing Λ] {iΛ : Spec (.of Λ) ⟶ S}
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] {hR₀ : B.Contains (Spec (.of R₀))}
    {x : 𝒳.val.obj} (P : FailedLift B S hS 𝒳 iΛ hR₀ x)
    {R' : Type u} [CommRing R'] [Algebra Λ R'] (hR' : B.Contains (Spec (.of R')))
    (g : R' →ₐ[Λ] P.A') {o : 𝒳.val.obj} (ζ : P.z ⟶ o) : Prop :=
  𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ P.memA' hR' g) ζ

/-- A diagram chase in a category: the compatibility of the glued arrows passes to a cocone. -/
theorem comp_cocone_eq {C : Type*} [Category C] {y z x o o₀ o₁ ξ x' : C} (a : y ⟶ x) (i : y ⟶ z)
    (t₀ : x ⟶ o₀) (t₁ : x ⟶ o₁) (ι₀ : o₀ ⟶ ξ) (ι₁ : o₁ ⟶ ξ) (s : z ⟶ o₁) (δ : ξ ⟶ x')
    (hι : t₁ ≫ ι₁ = t₀ ≫ ι₀) (hc : a ≫ t₁ = i ≫ s) :
    a ≫ t₀ ≫ ι₀ ≫ δ = i ≫ s ≫ ι₁ ≫ δ := by
  rw [← Category.assoc t₀, ← hι, Category.assoc, ← Category.assoc, hc, Category.assoc]

end Deformation.Artin

end
