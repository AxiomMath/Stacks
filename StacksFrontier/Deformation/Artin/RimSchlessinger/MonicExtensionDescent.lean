module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMonicExtensionLift
public import StacksFrontier.Deformation.Artin.LimitPreserving.FiniteTypeDescent
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArrowGluing
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction
public import StacksFrontier.RingTheory.Artinian.MonicExtensionRetraction

/-!
# Descending a lift along a monogenic extension

Let `𝒳` satisfy (RS*), let `f : A' ⟶ A` be a surjection of `Λ`-algebras with square-zero kernel
and `g ∈ A'[X]` monic of positive degree. A lifting problem `(i : y ⟶ z, a : y ⟶ x)` over
`Spec A ⟶ Spec A'` whose target `x` lies over an affine scheme has a solution as soon as its
base change along `A' ⟶ A'[X]/(g)` has one. The base-changed solution and `a` glue, by (RS*),
over `Spec (A'[X]/(g) ×_{A[X]/(f g)} A)`, and the glued arrow is pulled back along the retraction
of `Stacks.MonicExtension.retraction`.

## Main results

* `Deformation.Artin.exists_lift_of_monicExtension`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Polynomial

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.Over.post

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a map of `Λ`-algebras `g : R →ₐ[Λ] T`, the morphism `Spec g` followed by the structure
map `Spec R ⟶ Spec Λ` is the structure map `Spec T ⟶ Spec Λ`. -/
@[reassoc]
theorem specMap_algHom_comp {Λ R T : Type u} [CommRing Λ] [CommRing R] [CommRing T]
    [Algebra Λ R] [Algebra Λ T] (g : R →ₐ[Λ] T) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ T)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact g.comp_algebraMap

/-- The morphism of the site between spectra of `Λ`-algebras induced by an algebra map. -/
abbrev specAlgSiteHom {Λ R T : Type u} [CommRing Λ] [CommRing R] [CommRing T]
    [Algebra Λ R] [Algebra Λ T] (iΛ : Spec (.of Λ) ⟶ S)
    (hT : B.Contains (Spec (.of T))) (hR : B.Contains (Spec (.of R))) (g : R →ₐ[Λ] T) :
    siteObject B S hS hT (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ) ⟶
      siteObject B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ) :=
  specSiteHom B S hS hT hR _ _ (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    rw [← Category.assoc, specMap_algHom_comp])

/-- The spectrum of a monogenic extension by a monic polynomial of a ring whose spectrum lies in
the site lies in the site. -/
theorem contains_spec_adjoinRoot {R : Type u} [CommRing R] (hR : B.Contains (Spec (.of R)))
    {g : R[X]} (hg : g.Monic) : B.Contains (Spec (.of (AdjoinRoot g))) := by
  refine lt_of_le_of_lt ?_ hR
  rw [Scheme.size_Spec, Scheme.size_Spec]
  let pb := AdjoinRoot.powerBasis' hg
  have hcard : Cardinal.mk (AdjoinRoot g) = Cardinal.mk (Fin pb.dim → R) :=
    Cardinal.mk_congr pb.basis.equivFun.toEquiv
  rw [hcard, Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.lift_uzero, Cardinal.lift_natCast]
  refine max_le (le_max_left _ _) (Cardinal.power_nat_le_max.trans ?_)
  rw [max_comm]

/-- An arrow whose underlying scheme map is that of a morphism of the site lies over it. -/
theorem isHomLift_of_schemeMap {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) {y x : F}
    {Y X : AlgebraicGeometry.BigFppfOver B S hS} (hyY : p.obj y = Y) (hxX : p.obj x = X)
    (m : Y ⟶ X) (a : y ⟶ x)
    (h : schemeMap (p ⋙ Over.post B.inclusion) (congrArg (Over.post B.inclusion).obj hyY)
      (congrArg (Over.post B.inclusion).obj hxX) a =
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) :
    p.IsHomLift m a := by
  subst hyY hxX
  have hm : p.map a = m := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective (by
    simpa [schemeMap] using h)
  subst hm
  infer_instance

/-- The ring map underlying a morphism of affine schemes out of a spectrum into a spectrum,
over a monomorphism `Spec Λ ⟶ S`, is `Λ`-linear. -/
theorem exists_algHom_of_specMap {Λ R T : Type u} [CommRing Λ] [CommRing R] [CommRing T]
    [Algebra Λ R] [Algebra Λ T] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (m : Spec (.of T) ⟶ Spec (.of R))
    (hm : m ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ) :
    ∃ φ : R →ₐ[Λ] T, Spec.map (CommRingCat.ofHom φ.toRingHom) = m := by
  let φ₀ := Spec.preimage m
  have hφ₀ : Spec.map φ₀ = m := Spec.map_preimage m
  have hlin : φ₀.hom.comp (algebraMap Λ R) = algebraMap Λ T := by
    apply ringHom_eq_of_specMap_comp_eq iΛ
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    change Spec.map φ₀ ≫ _ = _
    rw [hφ₀, hm]
  exact ⟨{ φ₀.hom with commutes' := fun l => RingHom.congr_fun hlin l }, hφ₀⟩

/-- The ring map `B'[X]/(g) → A[X]/(f g)` induced by `f`, as a map of `Λ`-algebras. -/
def extAlgHom {Λ A A' : Type u} [CommRing Λ] [CommRing A] [CommRing A'] [Algebra Λ A]
    [Algebra Λ A'] (f : A' →ₐ[Λ] A) (G : A'[X]) :
    AdjoinRoot G →ₐ[Λ] AdjoinRoot (G.map f.toRingHom) :=
  { Stacks.MonicExtension.extMap f.toRingHom (G := G) with
    commutes' := fun l => by
      change Stacks.MonicExtension.extMap f.toRingHom (AdjoinRoot.of G (algebraMap Λ A' l)) =
        AdjoinRoot.of _ (algebraMap Λ A l)
      rw [Stacks.MonicExtension.extMap_of]
      exact congrArg _ (f.commutes l) }

/-- **Descending a lift along a monogenic extension.** Let `f : A' ⟶ A` be a surjection of
`Λ`-algebras with square-zero kernel and `g ∈ A'[X]` monic of positive degree; write
`A'' = A[X]/(f g)` and `B'' = A'[X]/(g)`. Let `i : y ⟶ z` lie over `Spec A ⟶ Spec A'` and
`a : y ⟶ x` with `x` over an affine scheme `Spec R₀`. If the base change
`i'' : y'' ⟶ z''` of `i` over `Spec A'' ⟶ Spec B''` admits `b'' : z'' ⟶ x` extending the base
change of `a`, then `i` admits `b : z ⟶ x` extending `a`. -/
theorem exists_lift_of_monicExtension
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    {A A' R₀ : Type u} [CommRing A] [CommRing A'] [CommRing R₀] [Algebra Λ A] [Algebra Λ A']
    [Algebra Λ R₀]
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (hR₀ : B.Contains (Spec (.of R₀)))
    (f : A' →ₐ[Λ] A) (hf : Function.Surjective f) (hker : RingHom.ker f.toRingHom ^ 2 = ⊥)
    {G : A'[X]} (hG : G.Monic) (hdeg : 0 < G.natDegree)
    (hA'' : B.Contains (Spec (.of (AdjoinRoot (G.map f.toRingHom)))))
    (hB'' : B.Contains (Spec (.of (AdjoinRoot G))))
    {x y z y'' z'' : X}
    (hx : p.obj x = siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (i : y ⟶ z) (hi : p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f) i) (a : y ⟶ x)
    (py : y'' ⟶ y) (hpy : p.IsHomLift (specAlgSiteHom B S hS iΛ hA'' hA
      (IsScalarTower.toAlgHom Λ A (AdjoinRoot (G.map f.toRingHom)))) py)
    (pz : z'' ⟶ z) (hpz : p.IsHomLift (specAlgSiteHom B S hS iΛ hB'' hA'
      (IsScalarTower.toAlgHom Λ A' (AdjoinRoot G))) pz)
    (i'' : y'' ⟶ z'') (hi'' : p.IsHomLift (specAlgSiteHom B S hS iΛ hA'' hB''
      (extAlgHom f G)) i'')
    (hcomm : i'' ≫ pz = py ≫ i) (b'' : z'' ⟶ x) (hb'' : i'' ≫ b'' = py ≫ a) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  classical
  let gA := G.map f.toRingHom
  let ext := Stacks.MonicExtension.extMap f.toRingHom (G := G)
  -- the fibre product `D = B'' ×_{A''} A` as a `Λ`-algebra
  let D := Stacks.MonicExtension.Pullback f.toRingHom (G := G)
  let algD : Λ →+* D := RingHom.codRestrict
    ((algebraMap Λ (AdjoinRoot G)).prod (algebraMap Λ A)) D (fun l => by
      change ext (AdjoinRoot.of G (algebraMap Λ A' l)) = AdjoinRoot.of gA (algebraMap Λ A l)
      rw [Stacks.MonicExtension.extMap_of]
      exact congrArg (AdjoinRoot.of gA) (f.commutes l))
  let : Algebra Λ D := algD.toAlgebra
  let fstD : D →ₐ[Λ] AdjoinRoot G :=
    { ext.pullbackFst (algebraMap A (AdjoinRoot gA)) with commutes' := fun _ => rfl }
  let sndD : D →ₐ[Λ] A :=
    { ext.pullbackSnd (algebraMap A (AdjoinRoot gA)) with commutes' := fun _ => rfl }
  let toD : A' →ₐ[Λ] D :=
    { Stacks.MonicExtension.toPullback f.toRingHom (G := G) with
      commutes' := fun l => Subtype.ext (Prod.ext rfl (f.commutes l)) }
  let retD : D →ₐ[Λ] A' :=
    { Stacks.MonicExtension.retraction f.toRingHom hG hdeg hker with
      commutes' := fun l => Stacks.MonicExtension.constCoeff_of hG hdeg (algebraMap Λ A' l) }
  have hD : B.Contains (Spec (.of D)) := by
    refine lt_of_le_of_lt ?_ (max_lt hB'' hA)
    have hmk : Cardinal.mk D ≤ Cardinal.mk (AdjoinRoot G × A) := Cardinal.mk_subtype_le _
    rw [Scheme.size_Spec, Scheme.size_Spec, Scheme.size_Spec]
    refine (max_le_max le_rfl hmk).trans ?_
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    refine (max_le_max le_rfl (Cardinal.mul_le_max _ _)).trans ?_
    exact max_le (le_max_of_le_left (le_max_left _ _))
      (max_le (max_le (le_max_of_le_left (le_max_right _ _))
        (le_max_of_le_right (le_max_right _ _))) (le_max_of_le_left (le_max_left _ _)))
  -- the five affine objects and the maps between them
  let ob : ∀ {T : Type u} [CommRing T] [Algebra Λ T], B.Contains (Spec (.of T)) →
      AlgebraicGeometry.BigAffineFppf B S hS := fun {T} _ _ hT =>
    ⟨siteObject B S hS hT (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ),
      inferInstanceAs (IsAffine (Spec _))⟩
  let mk : ∀ {T T' : Type u} [CommRing T] [Algebra Λ T] [CommRing T'] [Algebra Λ T']
      (hT : B.Contains (Spec (.of T))) (hT' : B.Contains (Spec (.of T'))),
      (T' →ₐ[Λ] T) → (ob hT ⟶ ob hT') := fun {T T'} _ _ _ _ hT hT' g =>
    ObjectProperty.homMk (specAlgSiteHom B S hS iΛ hT hT' g)
  have hmk : ∀ {T T' : Type u} [CommRing T] [Algebra Λ T] [CommRing T'] [Algebra Λ T']
      (hT : B.Contains (Spec (.of T))) (hT' : B.Contains (Spec (.of T'))) (g : T' →ₐ[Λ] T),
      (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (mk hT hT' g) =
        Spec.map (CommRingCat.ofHom g.toRingHom) := fun _ _ _ => rfl
  have hext : ∀ {X Y : AlgebraicGeometry.BigAffineFppf B S hS} (m m' : X ⟶ Y),
      (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map m =
        (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map m' → m = m' := fun _ _ h =>
    ObjectProperty.hom_ext _ ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective h)
  have hcompMk : ∀ {T T' T'' : Type u} [CommRing T] [Algebra Λ T] [CommRing T'] [Algebra Λ T']
      [CommRing T''] [Algebra Λ T'']
      (hT : B.Contains (Spec (.of T))) (hT' : B.Contains (Spec (.of T')))
      (hT'' : B.Contains (Spec (.of T''))) (g : T' →ₐ[Λ] T) (g' : T'' →ₐ[Λ] T'),
      mk hT hT' g ≫ mk hT' hT'' g' = mk hT hT'' (g.comp g') := by
    intro T T' T'' _ _ _ _ _ _ hT hT' hT'' g g'
    apply hext
    rw [Functor.map_comp, hmk, hmk, hmk, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let algA'' := IsScalarTower.toAlgHom Λ A (AdjoinRoot gA)
  let algB'' := IsScalarTower.toAlgHom Λ A' (AdjoinRoot G)
  let gAm := mk hA'' hA algA''
  let jm := mk hA'' hB'' (extAlgHom f G)
  let lAm := mk hA hD sndD
  let lBm := mk hB'' hD fstD
  let inclm := mk hD hA' toD
  let ρm := mk hA' hD retD
  have hsq : gAm ≫ lAm = jm ≫ lBm := by
    rw [hcompMk, hcompMk]
    congr 1
    ext d
    exact d.2.symm
  have hpb : IsPullback ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map lAm).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map lBm).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map gAm).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map jm).appTop :=
    specMap_appTop_isPullback (Stacks.Pushout.isPullback_ofHom_pullback ext
      (algebraMap A (AdjoinRoot gA))).flip
  have hsurj : Function.Surjective
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map jm).appTop.hom :=
    specMap_appTop_surjective (CommRingCat.ofHom ext)
      (Stacks.MonicExtension.extMap_surjective f.toRingHom hf)
  have hkerj : RingHom.ker
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map jm).appTop.hom ^ 2 = ⊥ :=
    specMap_appTop_ker_sq (CommRingCat.ofHom ext)
      (Stacks.MonicExtension.ker_extMap_sq f.toRingHom hG hker)
  have hρ : ρm ≫ inclm = 𝟙 _ := by
    rw [hcompMk]
    apply hext
    rw [hmk, CategoryTheory.Functor.map_id]
    have : retD.comp toD = AlgHom.id Λ A' := AlgHom.ext fun a =>
      RingHom.congr_fun (Stacks.MonicExtension.retraction_comp_toPullback f.toRingHom hG hdeg
        hker) a
    rw [this]
    exact Spec.map_id _
  have hρA : lAm ≫ inclm ≫ ρm = lAm := by
    rw [hcompMk, hcompMk]
    congr 1
    ext d
    exact RingHom.congr_fun (Stacks.MonicExtension.comp_retraction f.toRingHom hG hdeg hker) d
  have : p.IsHomLift (lAm ≫ inclm).hom i := by rw [hcompMk]; exact hi
  have : p.IsHomLift (lBm ≫ inclm).hom pz := by rw [hcompMk]; exact hpz
  have : p.IsHomLift gAm.hom py := hpy
  have : p.IsHomLift jm.hom i'' := hi''
  refine exists_lift_of_lift_after_retract p hp hRS gAm jm lAm lBm hsq hpb hsurj hkerj inclm ρm
    hρ hρA ?_ i a pz py i'' hcomm b'' hb''
  -- maps out of the pushout into the affine target of `x`
  intro g₁ g₂ hg
  have hring : ∀ {T : Type u} [CommRing T] [Algebra Λ T] (hT : B.Contains (Spec (.of T)))
      (g : (ob hT).obj ⟶ p.obj x), ∃ ψ : R₀ →ₐ[Λ] T,
        (mk hT hR₀ ψ).hom = g ≫ eqToHom hx := by
    intro T _ _ hT g
    obtain ⟨ψ, hψ⟩ := exists_algHom_of_specMap S iΛ
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (g ≫ eqToHom hx))
      (AlgebraicGeometry.BigFppfOver.toScheme_map_comp_hom (g ≫ eqToHom hx))
    exact ⟨ψ, (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective hψ⟩
  obtain ⟨ψ₁, hψ₁⟩ := hring hB'' g₁
  obtain ⟨ψ₂, hψ₂⟩ := hring hA g₂
  have hψ : ext.comp ψ₁.toRingHom = (algebraMap A (AdjoinRoot gA)).comp ψ₂.toRingHom := by
    have h := congrArg (fun m => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (m ≫ eqToHom hx)) hg
    simp only [Category.assoc] at h
    rw [← hψ₁, ← hψ₂] at h
    simp only [Functor.map_comp] at h
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ at h
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  let ψ : R₀ →ₐ[Λ] D :=
    { RingHom.codRestrict (ψ₁.toRingHom.prod ψ₂.toRingHom) D (fun r => RingHom.congr_fun hψ r)
      with commutes' := fun l => Subtype.ext (Prod.ext (ψ₁.commutes l) (ψ₂.commutes l)) }
  refine ⟨(mk hD hR₀ ψ).hom ≫ eqToHom hx.symm, ?_, ?_⟩
  · rw [← Category.assoc]
    change (lBm ≫ mk hD hR₀ ψ).hom ≫ _ = _
    rw [hcompMk, show fstD.comp ψ = ψ₁ from AlgHom.ext fun _ => rfl, hψ₁]
    simp
  · rw [← Category.assoc]
    change (lAm ≫ mk hD hR₀ ψ).hom ≫ _ = _
    rw [hcompMk, show sndD.comp ψ = ψ₂ from AlgHom.ext fun _ => rfl, hψ₂]
    simp

/-- `Deformation.Artin.exists_lift_of_monicExtension`, with the objects over the two monogenic
extensions given up to equality, and the three arrows of the site over which `py`, `pz` and
`i''` lie given up to the corresponding `eqToHom`s. -/
theorem exists_lift_of_monicExtension'
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    {A A' R₀ : Type u} [CommRing A] [CommRing A'] [CommRing R₀] [Algebra Λ A] [Algebra Λ A']
    [Algebra Λ R₀]
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (hR₀ : B.Contains (Spec (.of R₀)))
    (f : A' →ₐ[Λ] A) (hf : Function.Surjective f) (hker : RingHom.ker f.toRingHom ^ 2 = ⊥)
    {G : A'[X]} (hG : G.Monic) (hdeg : 0 < G.natDegree)
    (hA'' : B.Contains (Spec (.of (AdjoinRoot (G.map f.toRingHom)))))
    (hB'' : B.Contains (Spec (.of (AdjoinRoot G))))
    {x y z y'' z'' : X}
    (hx : p.obj x = siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (i : y ⟶ z) (hi : p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f) i) (a : y ⟶ x)
    {Y'' Z'' : AlgebraicGeometry.BigFppfOver B S hS}
    (hY : Y'' = siteObject B S hS hA''
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (AdjoinRoot (G.map f.toRingHom)))) ≫ iΛ))
    (hZ : Z'' = siteObject B S hS hB''
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (AdjoinRoot G))) ≫ iΛ))
    (py : y'' ⟶ y) (hpy : p.IsHomLift (eqToHom hY ≫ specAlgSiteHom B S hS iΛ hA'' hA
      (IsScalarTower.toAlgHom Λ A (AdjoinRoot (G.map f.toRingHom)))) py)
    (pz : z'' ⟶ z) (hpz : p.IsHomLift (eqToHom hZ ≫ specAlgSiteHom B S hS iΛ hB'' hA'
      (IsScalarTower.toAlgHom Λ A' (AdjoinRoot G))) pz)
    (i'' : y'' ⟶ z'') (hi'' : p.IsHomLift (eqToHom hY ≫ specAlgSiteHom B S hS iΛ hA'' hB''
      (extAlgHom f G) ≫ eqToHom hZ.symm) i'')
    (hcomm : i'' ≫ pz = py ≫ i) (b'' : z'' ⟶ x) (hb'' : i'' ≫ b'' = py ≫ a) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  subst hY hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hpy hpz hi''
  exact exists_lift_of_monicExtension B S hS p hp hRS iΛ hA hA' hR₀ f hf hker hG hdeg hA'' hB''
    hx i hi a py hpy pz hpz i'' hi'' hcomm b'' hb''

end Deformation.Artin
