module

public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extensions of finitely presented sheaves of modules on a site

Let `R` be a sheaf of rings on an arbitrary site.  The middle term of a short exact sequence of
sheaves of `R`-modules whose outer terms are of finite presentation is of finite presentation.
This is the finite-presentation form of part (4) of Stacks 01BY, for the rendering of
Stacks 03DL(7) by universal properties, `SheafOfModules.IsFinitePresentationOnSite`.

## Main definitions

* `Stacks.SheafOfModules.HasSectionsPresentation`: section-level finite presentation data for a
  module over an object of the site — finitely many sections generating it, together with
  finitely many vectors of coefficients which are relations among them and generate all
  relations locally.
* `Stacks.SheafOfModules.liftPowCoeff`: the coefficient matrix of a morphism between finite
  coproducts of copies of the structure sheaf.
* `Stacks.SheafOfModules.relationCombinationSieve`: the sieve along which a given relation is a
  combination of given rows.

## Main results

* `Stacks.SheafOfModules.isFinitePresentationOnSite_middle`,
  `Stacks.SheafOfModules.isFinitePresentationOnSite_X₂_of_kernel_cokernel` and
  `Stacks.SheafOfModules.isFinitePresentationOnSite_X₂_of_shortExact`: **finite presentation of
  sheaves of modules on a site is closed under extensions**, with the exactness given
  respectively as a kernel fork together with local surjectivity, as a kernel fork and a cokernel
  cofork, and as a short exact sequence in a balanced category.
* `Stacks.SheafOfModules.exists_sections_relations_of_hasFiniteGlobalPresentation` and
  `Stacks.SheafOfModules.hasSectionsPresentation_of_hasFiniteGlobalPresentation`: **a finite
  global presentation read on sections**, the converse of
  `SheafOfModules.hasFiniteGlobalPresentation_of_sections` and of
  `SheafOfModules.hasFiniteGlobalPresentation_over_of_generates`.
* `Stacks.SheafOfModules.imageSieveOfHom_mem_of_isColimit`: a section killed by a cokernel
  projection is locally in the image of the map it is a cokernel of.
* `Stacks.SheafOfModules.hasSectionsPresentation_of_data`: the local step, producing section-level
  presentation data for the middle term from such data for the outer terms.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01B7](https://stacks.math.columbia.edu/tag/01B7)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules SheafOfModules

universe u v w m

namespace Stacks.SheafOfModules

section LocalImage

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A section killed by a cokernel projection is locally in the image.**  If `b` is a cokernel
of `a`, then every section of `P` killed by `b` is locally in the image of `a`. -/
theorem imageSieveOfHom_mem_of_isColimit [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {Q P N : SheafOfModules.{m} R} {a : Q ⟶ P} {b : P ⟶ N}
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    (X : Cᵒᵖ) (x : P.val.obj X) (hx : Hom.app b.val X x = 0) :
    LocalImage.imageSieveOfHom a x ∈ J X.unop := by
  have haz : a ≫ cokernel.π (LocalImage.localImage a).ι = 0 := by
    have h1 : LocalImage.toLocalImage a ≫ ((LocalImage.localImage a).ι ≫
        cokernel.π (LocalImage.localImage a).ι) = 0 := by
      rw [cokernel.condition, comp_zero]
    rw [← Category.assoc, LocalImage.toLocalImage_comp_ι] at h1
    exact h1
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hb
    (cokernel.π (LocalImage.localImage a).ι) haz
  simp only [CokernelCofork.π_ofπ] at hd
  have hker := Abelian.monoIsKernelOfCokernel (f := (LocalImage.localImage a).ι) _
    (cokernelIsCokernel (LocalImage.localImage a).ι)
  have hx' : Hom.app (cokernel.π (LocalImage.localImage a).ι).val X x = 0 := by
    rw [← hd, comp_val_app_apply, hx, map_zero]
  obtain ⟨y, hy⟩ := exists_app_eq_of_isLimit
    (cokernel.condition (LocalImage.localImage a).ι) hker X x hx'
  refine (LocalImage.mem_localImage a x).1 ?_
  rw [← hy, LocalImage.submodule_ι_app]
  exact y.2

end LocalImage

section Coordinates

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

open _root_.SheafOfModules

/-- A morphism out of the universe-lifted structure sheaf is determined by its value at `1`. -/
theorem liftUnit_hom_app {T : SheafOfModules.{max u v w} R} (φ : liftUnit R ⟶ T) (X : Cᵒᵖ)
    (c : R.obj.obj X) :
    Hom.app φ.val X (liftUnitOf c) = c • Hom.app φ.val X (liftUnitOf (1 : R.obj.obj X)) := by
  have hc : (c • liftUnitOf (1 : R.obj.obj X) : (liftUnit R).val.obj X) = liftUnitOf c :=
    congrArg ULift.up (mul_one c)
  rw [← hc, map_smul]

/-- The section `1` of the universe-lifted structure sheaf restricts to `1`. -/
theorem liftUnit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (liftUnit R).val.map f (liftUnitOf (1 : R.obj.obj X)) = liftUnitOf (1 : R.obj.obj Y) :=
  congrArg ULift.up (PresheafOfModules.unit_map_one R.obj f)

/-- Acting by a ring element on a section of `SheafOfModules.liftPow` multiplies its
coefficients. -/
theorem smul_powMk (n : ℕ) (X : Cᵒᵖ) (c : R.obj.obj X) (d : Fin n → R.obj.obj X) :
    c • powMk R n X d = powMk R n X (fun i ↦ c * d i) := by
  rw [powMk_def, powMk_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← map_smul]
  rfl

/-- The `i`-th coefficient of a section of `SheafOfModules.liftPow` with prescribed
coefficients is the `i`-th prescribed one. -/
theorem liftUnitVal_π_powMk (n : ℕ) (X : Cᵒᵖ) (c : Fin n → R.obj.obj X) (i : Fin n) :
    liftUnitVal (Hom.app (biproduct.π (fun _ : Fin n ↦ liftUnit R) i).val X
      (powMk R n X c)) = c i := by
  have h : ∀ j : Fin n, Hom.app (biproduct.π (fun _ : Fin n ↦ liftUnit R) i).val X
      (Hom.app (biproduct.ι (fun _ : Fin n ↦ liftUnit R) j).val X (liftUnitOf (c j)))
      = if j = i then liftUnitOf (c i) else 0 := by
    intro j
    rw [← comp_val_app_apply]
    by_cases hj : j = i
    · subst hj
      rw [biproduct.ι_π_self, ite_eq_left rfl]
      rfl
    · rw [biproduct.ι_π_ne _ hj, ite_eq_right hj]
      rfl
  rw [powMk_def, map_sum,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj ↦ by
      rw [h j, ite_eq_right hj], h i,
    ite_eq_left rfl]

/-- Restriction of a section of the sheaf of rings is additive. -/
theorem ring_map_add {X Y : Cᵒᵖ} (f : X ⟶ Y) (a b : R.obj.obj X) :
    R.obj.map f (a + b) = R.obj.map f a + R.obj.map f b :=
  map_add (ConcreteCategory.hom (R.obj.map f)) a b

/-- Restriction of a section of the sheaf of rings commutes with negation. -/
theorem ring_map_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : R.obj.obj X) :
    R.obj.map f (-a) = -R.obj.map f a :=
  map_neg (ConcreteCategory.hom (R.obj.map f)) a

/-- Restriction of the zero section of the sheaf of rings. -/
theorem ring_map_zero {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    R.obj.map f (0 : R.obj.obj X) = 0 :=
  map_zero (ConcreteCategory.hom (R.obj.map f))

/-- The coefficients of a section of `SheafOfModules.liftPow` are determined by it. -/
theorem powMk_coeff_eq {n : ℕ} {X : Cᵒᵖ} {c d : Fin n → R.obj.obj X}
    (h : powMk R n X c = powMk R n X d) (i : Fin n) : c i = d i := by
  rw [← liftUnitVal_π_powMk n X c i, ← liftUnitVal_π_powMk n X d i, h]

end Coordinates

section Extraction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

open _root_.SheafOfModules

/-- The coefficient matrix of a morphism between finite coproducts of copies of the
universe-lifted structure sheaf: the `i`-th coefficient of the image of the `k`-th generator. -/
noncomputable abbrev liftPowCoeff {p n : ℕ} (φ : liftPow R p ⟶ liftPow R n) (X : Cᵒᵖ)
    (k : Fin p) (i : Fin n) : R.obj.obj X :=
  liftUnitVal (Hom.app (biproduct.π (fun _ : Fin n ↦ liftUnit R) i).val X
    (Hom.app (biproduct.ι (fun _ : Fin p ↦ liftUnit R) k ≫ φ).val X
      (liftUnitOf (1 : R.obj.obj X))))

/-- The image of the `k`-th generator is the section with the `k`-th row of the coefficient
matrix as its coefficients. -/
theorem powMk_liftPowCoeff {p n : ℕ} (φ : liftPow R p ⟶ liftPow R n) (X : Cᵒᵖ) (k : Fin p) :
    powMk R n X (liftPowCoeff φ X k) =
      Hom.app (biproduct.ι (fun _ : Fin p ↦ liftUnit R) k ≫ φ).val X
        (liftUnitOf (1 : R.obj.obj X)) :=
  powMk_coord n X _

/-- The coefficient matrix is a matrix of global sections: it is compatible with restriction. -/
theorem liftPowCoeff_map {p n : ℕ} (φ : liftPow R p ⟶ liftPow R n) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (k : Fin p) (i : Fin n) :
    R.obj.map f (liftPowCoeff φ X k i) = liftPowCoeff φ Y k i := by
  have hφ := PresheafOfModules.naturality_apply
    (biproduct.ι (fun _ : Fin p ↦ liftUnit R) k ≫ φ).val f (liftUnitOf (1 : R.obj.obj X))
  rw [liftUnit_map_one] at hφ
  have hπ := PresheafOfModules.naturality_apply
    (biproduct.π (fun _ : Fin n ↦ liftUnit R) i).val f
    (Hom.app (biproduct.ι (fun _ : Fin p ↦ liftUnit R) k ≫ φ).val X
      (liftUnitOf (1 : R.obj.obj X)))
  rw [← hφ] at hπ
  exact congrArg ULift.down hπ.symm

/-- **A morphism between finite coproducts of copies of the structure sheaf is given by its
coefficient matrix.** -/
theorem hom_liftPow_powMk {p n : ℕ} (φ : liftPow R p ⟶ liftPow R n) (X : Cᵒᵖ)
    (d : Fin p → R.obj.obj X) :
    Hom.app φ.val X (powMk R p X d)
      = powMk R n X (fun i ↦ ∑ k, d k * liftPowCoeff φ X k i) := by
  rw [powMk_sum Finset.univ n X (fun k i ↦ d k * liftPowCoeff φ X k i), powMk_def, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← comp_val_app_apply, liftUnit_hom_app, ← powMk_liftPowCoeff, smul_powMk]

/-- **The section-level reading of a finite global presentation.**  A sheaf of modules carrying
a finite global presentation in the sense of Stacks 03DE(7) — a cokernel of a map between finite
coproducts of copies of the structure sheaf — carries finitely many global sections generating it
locally, together with finitely many vectors of coefficients which are relations among those
sections and generate all relations locally.

This is the converse of `SheafOfModules.hasFiniteGlobalPresentation_of_sections`: the three
conclusions are its three hypotheses. -/
theorem exists_sections_relations_of_hasFiniteGlobalPresentation (N : SheafOfModules.{w} R)
    (h : N.HasFiniteGlobalPresentation) :
    ∃ (n p : ℕ) (σ : Fin n → N.sections) (ρ : Fin p → Fin n → (unit R).sections),
      (∀ (k : Fin p) (X : Cᵒᵖ), ∑ i, unitVal ((ρ k i).eval X) • (σ i).eval X = 0) ∧
      (∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
        ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : Fin n → R.obj.obj (op B),
          ∑ i, c i • (σ i).eval (op B) = N.val.map g.op x) ∧
      (∀ (V : C) (τ : Fin n → R.obj.obj (op V)), (∑ i, τ i • (σ i).eval (op V) = 0) →
        ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
          ∃ d : Fin p → R.obj.obj (op B), ∀ i,
            ∑ k, d k * unitVal ((ρ k i).eval (op B)) = R.obj.map g.op (τ i)) := by
  have hsh : HasSheafify J AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u} J
  have hlb : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v} J
  obtain ⟨n, p, P, Q, iP, iQ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  let eP : liftPow R n ≅ P := (biproduct.isColimit _).coconePointUniqueUpToIso hP
  let eQ : liftPow R p ≅ Q := (biproduct.isColimit _).coconePointUniqueUpToIso hQ
  let q : liftPow R n ⟶ liftMod N := eP.hom ≫ b
  let c : liftPow R p ⟶ liftPow R n := eQ.hom ≫ a ≫ eP.inv
  let σ : Fin n → N.sections := fun i =>
    PresheafOfModules.sectionsMk
      (fun X => (Hom.app (biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ q).val X
        (liftUnitOf (1 : R.obj.obj X))).down)
      (fun {X Y} f => by
        have hnat := PresheafOfModules.naturality_apply
          (biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ q).val f
          (liftUnitOf (1 : R.obj.obj X))
        rw [liftUnit_map_one] at hnat
        exact congrArg ULift.down hnat.symm)
  let ρ : Fin p → Fin n → (unit R).sections := fun k i =>
    PresheafOfModules.sectionsMk (fun X => liftPowCoeff c X k i)
      (fun {X Y} f => liftPowCoeff_map c f k i)
  have hqd : powDesc N σ = q := by
    refine biproduct.hom_ext' _ _ fun i => ?_
    rw [show biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ powDesc N σ
        = liftSectionHom (σ i) from biproduct.ι_desc _ i]
    ext X z
    rw [liftSectionHom_val_app_apply]
    have hz : (liftUnitVal z • liftUnitOf (1 : R.obj.obj X) : (liftUnit R).val.obj X) = z :=
      congrArg ULift.up (mul_one (liftUnitVal z))
    have hsm : Hom.app (biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ q).val X
          (liftUnitVal z • liftUnitOf (1 : R.obj.obj X))
        = liftUnitVal z • Hom.app (biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ q).val X
          (liftUnitOf (1 : R.obj.obj X)) :=
      map_smul (Hom.app (biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ q).val X).hom _ _
    have hup : (ULift.up (liftUnitVal z • (σ i).eval X) : (liftMod N).val.obj X)
        = liftUnitVal z • Hom.app (biproduct.ι (fun _ : Fin n ↦ liftUnit R) i ≫ q).val X
          (liftUnitOf (1 : R.obj.obj X)) := rfl
    rw [hup, ← hsm, hz]
  have hcz : c ≫ q = 0 := by
    change (eQ.hom ≫ a ≫ eP.inv) ≫ eP.hom ≫ b = 0
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hab, comp_zero]
  refine ⟨n, p, σ, ρ, fun k X => ?_, fun V x => ?_, fun V τ hτ => ?_⟩
  · have h0 : Hom.app q.val X (powMk R n X (liftPowCoeff c X k)) = 0 := by
      rw [powMk_liftPowCoeff, ← comp_val_app_apply,
        show (biproduct.ι (fun _ : Fin p ↦ liftUnit R) k ≫ c) ≫ q = 0 from by
          rw [Category.assoc, hcz, comp_zero]]
      rfl
    rw [← hqd, powDesc_val_app_powMk] at h0
    exact congrArg ULift.down h0
  · have hbe : Epi b := epi_of_isColimit_cofork hb
    have hepi : Epi (powDesc N σ) := by
      rw [hqd]
      exact epi_comp eP.hom b
    have hls := EpiMono.isLocallySurjective_of_epi (powDesc N σ)
    refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (powDesc N σ).val)
        (ULift.up x : (liftMod N).val.obj (op V)), hls.imageSieve_mem _, ?_⟩
    intro B g hg
    obtain ⟨t, ht⟩ := hg
    refine ⟨fun i =>
      liftUnitVal (Hom.app (biproduct.π (fun _ : Fin n ↦ liftUnit R) i).val (op B) t), ?_⟩
    have ht' : Hom.app (powDesc N σ).val (op B) t = ULift.up (N.val.map g.op x) := ht
    rw [← powMk_coord n (op B) t, powDesc_val_app_powMk] at ht'
    exact congrArg ULift.down ht'
  · have hx : Hom.app b.val (op V) (Hom.app eP.hom.val (op V) (powMk R n (op V) τ)) = 0 := by
      rw [← comp_val_app_apply, show eP.hom ≫ b = powDesc N σ from hqd.symm,
        powDesc_val_app_powMk, hτ]
      rfl
    refine ⟨LocalImage.imageSieveOfHom a (Hom.app eP.hom.val (op V) (powMk R n (op V) τ)),
      imageSieveOfHom_mem_of_isColimit hab hb (op V) _ hx, ?_⟩
    intro B g hg
    obtain ⟨z, hz⟩ := (LocalImage.mem_imageSieveOfHom a _ g).1 hg
    refine ⟨fun k => liftUnitVal (Hom.app (biproduct.π (fun _ : Fin p ↦ liftUnit R) k).val (op B)
      (Hom.app eQ.inv.val (op B) z)), fun i => ?_⟩
    have e1 : Hom.app eP.inv.val (op B) (Hom.app a.val (op B) z)
        = powMk R n (op B) (fun i => R.obj.map g.op (τ i)) := by
      rw [hz, PresheafOfModules.naturality_apply eP.inv.val g.op, ← comp_val_app_apply,
        eP.hom_inv_id, ← powMk_restrict g.op τ]
      rfl
    have e2 : Hom.app eP.inv.val (op B) (Hom.app a.val (op B) z)
        = powMk R n (op B) (fun i => ∑ k,
          liftUnitVal (Hom.app (biproduct.π (fun _ : Fin p ↦ liftUnit R) k).val (op B)
            (Hom.app eQ.inv.val (op B) z)) * liftPowCoeff c (op B) k i) := by
      rw [← comp_val_app_apply,
        show a ≫ eP.inv = eQ.inv ≫ c from (Iso.inv_hom_id_assoc eQ (a ≫ eP.inv)).symm,
        comp_val_app_apply]
      conv_lhs => rw [← powMk_coord p (op B) (Hom.app eQ.inv.val (op B) z)]
      rw [hom_liftPow_powMk]
    exact (powMk_coeff_eq (e1.symm.trans e2) i).symm

end Extraction

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

open _root_.SheafOfModules

/-- **Section-level finite presentation data over an object.**  Finitely many sections of `M`
over `Z` generating `M` on the slice site at `Z`, together with finitely many vectors of
coefficients which are relations among them and generate all relations locally.

This is Stacks 03DL(7) read on sections over a single object. -/
@[sga "6 I 2.8" "partial"]
def HasSectionsPresentation (J : GrothendieckTopology C) (M : SheafOfModules.{w} R)
    (Z : C) : Prop :=
  ∃ (n p : ℕ) (s : Fin n → M.val.obj (op Z)) (r : Fin p → Fin n → R.obj.obj (op Z)),
    (∀ k, ∑ i, r k i • s i = 0) ∧ PresheafOfModules.Generates J M.val s ∧
      ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n → R.obj.obj (op V)),
        (∑ i, τ i • M.val.restrictₛₗ hV.op (s i) = 0) →
        ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
          ∃ d : Fin p → R.obj.obj (op B), ∀ i,
            ∑ k, d k * R.obj.map (g ≫ hV).op (r k i) = R.obj.map g.op (τ i)

/-- Section-level finite presentation data over `Z` presents the restriction of the module to
the slice site at `Z`. -/
theorem hasFiniteGlobalPresentation_over_of_hasSectionsPresentation {M : SheafOfModules.{w} R}
    {Z : C} (h : HasSectionsPresentation J M Z) :
    (M.over Z).HasFiniteGlobalPresentation := by
  obtain ⟨n, p, s, r, hr, hs, hrel⟩ := h
  exact hasFiniteGlobalPresentation_over_of_generates M Z s r hr hs hrel

/-- A covering sieve of `Over.mk f` over the slice topology gives a covering sieve of the source
`W` of `f : W ⟶ Z`, and a property of arrows into `W` follows from its pullback to the slice. -/
private theorem exists_sieve_of_mem_over {Z W : C} (f : W ⟶ Z) {T : Sieve (Over.mk f)}
    (hT : T ∈ J.over Z (Over.mk f)) {P : ∀ ⦃B : C⦄, (B ⟶ W) → Prop}
    (h : ∀ ⦃B : C⦄ (g : B ⟶ W), T.arrows (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f) → P g) :
    ∃ S : Sieve W, S ∈ J W ∧ ∀ ⦃B : C⦄ (g : B ⟶ W), S.arrows g → P g :=
  ⟨Sieve.overEquiv (Over.mk f) T, (J.mem_over_iff T).mp hT,
    fun _ g hg => h g ((Sieve.overEquiv_iff T g).mp hg)⟩

/-- **A finite global presentation of a restriction is section-level presentation data.**  If
the restriction of `M` to the slice site at `Z` has a finite global presentation, then `M`
carries section-level finite presentation data over `Z`. -/
theorem hasSectionsPresentation_of_hasFiniteGlobalPresentation (M : SheafOfModules.{w} R) (Z : C)
    (h : (M.over Z).HasFiniteGlobalPresentation) : HasSectionsPresentation J M Z := by
  obtain ⟨n, p, σ, ρ, hρ, hgen, hrel⟩ :=
    exists_sections_relations_of_hasFiniteGlobalPresentation (M.over Z) h
  have hσ : ∀ (i : Fin n) {W : C} (f : W ⟶ Z), (σ i).eval (op (Over.mk f))
      = M.val.restrictₛₗ f.op ((σ i).eval (op (Over.mk (𝟙 Z)))) := fun i {W} f =>
    ((σ i).property
      (Over.homMk f (Category.comp_id _) : Over.mk f ⟶ Over.mk (𝟙 Z)).op).symm
  have hρeval : ∀ (k : Fin p) (i : Fin n) {W : C} (f : W ⟶ Z),
      unitVal ((ρ k i).eval (op (Over.mk f)))
        = R.obj.map f.op (unitVal ((ρ k i).eval (op (Over.mk (𝟙 Z))))) := fun k i {W} f =>
    ((ρ k i).property
      (Over.homMk f (Category.comp_id _) : Over.mk f ⟶ Over.mk (𝟙 Z)).op).symm
  refine ⟨n, p, fun i => (σ i).eval (op (Over.mk (𝟙 Z))),
    fun k i => unitVal ((ρ k i).eval (op (Over.mk (𝟙 Z)))),
    fun k => hρ k (op (Over.mk (𝟙 Z))), ?_, ?_⟩
  · intro W f t
    obtain ⟨T, hT, hc⟩ := hgen (Over.mk f) t
    refine exists_sieve_of_mem_over f hT fun _ g hg => ?_
    obtain ⟨cc, hceq⟩ := hc _ hg
    refine ⟨cc, ?_⟩
    change ∑ i, cc i • (σ i).eval (op (Over.mk (g ≫ f))) = M.val.restrictₛₗ g.op t at hceq
    simp only [hσ _ (g ≫ f)] at hceq
    exact hceq
  · intro V hV τ hτ
    obtain ⟨T, hT, hd⟩ := hrel (Over.mk hV) τ (by
      simp only [hσ _ hV]
      exact hτ)
    refine exists_sieve_of_mem_over hV hT fun _ g hg => ?_
    obtain ⟨d, hdeq⟩ := hd _ hg
    refine ⟨d, fun i => ?_⟩
    have h := hdeq i
    change ∑ k, d k * unitVal ((ρ k i).eval (op (Over.mk (g ≫ hV))))
      = R.obj.map g.op (τ i) at h
    simp only [hρeval _ i (g ≫ hV)] at h
    exact h

end Sections

section Middle

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

open _root_.SheafOfModules Sectionwise

/-- A morphism of presheaves of modules carries a linear combination of sections to the
combination of the images. -/
lemma hom_app_sum_smul {R' : Cᵒᵖ ⥤ RingCat.{w}} {P Q : PresheafOfModules.{m} R'} (φ : P ⟶ Q)
    (X : Cᵒᵖ) {n : ℕ} (a : Fin n → R'.obj X) (z : Fin n → P.obj X) :
    Hom.app φ X (∑ i, a i • z i) = ∑ i, a i • Hom.app φ X (z i) :=
  (map_sum (ConcreteCategory.hom (Hom.app φ X)) (fun i => a i • z i) Finset.univ).trans
    (Finset.sum_congr rfl fun i _ => hom_app_smul φ X (a i) (z i))

/-- If every relation among the sections `s` over an object of the slice at `Z` is locally a
combination of the rows `r`, then the same holds for their restrictions along `g : W ⟶ Z`. -/
theorem generatesRelations_restrict {M : SheafOfModules.{w} R} {Z : C} {n q : ℕ}
    (s : Fin n → M.val.obj (op Z)) (r : Fin q → Fin n → R.obj.obj (op Z))
    (hrel : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n → R.obj.obj (op V)),
      (∑ i, τ i • M.val.restrictₛₗ hV.op (s i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin q → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r k i) = R.obj.map g.op (τ i))
    {W : C} (g : W ⟶ Z) (V : C) (hV : V ⟶ W) (τ : Fin n → R.obj.obj (op V))
    (hτ : ∑ i, τ i • M.val.restrictₛₗ hV.op (M.val.restrictₛₗ g.op (s i)) = 0) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (gg : B ⟶ V), T.arrows gg →
      ∃ d : Fin q → R.obj.obj (op B), ∀ i,
        ∑ k, d k * R.obj.map (gg ≫ hV).op (R.obj.map g.op (r k i))
          = R.obj.map gg.op (τ i) := by
  obtain ⟨T, hT, hd⟩ := hrel V (hV ≫ g) τ (by simpa only [restrict_restrict] using hτ)
  refine ⟨T, hT, fun B gg hgg => ?_⟩
  obtain ⟨d, hdeq⟩ := hd gg hgg
  refine ⟨d, fun i => Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (hdeq i)⟩
  exact congrArg (fun z => d k * z)
    ((ring_map_map g (gg ≫ hV) (r k i)).trans
      (congrArg (fun f : B ⟶ Z => R.obj.map f.op (r k i)) (Category.assoc gg hV g)))

/-- **Section-level finite presentation data restricts along an arrow of the site.** -/
theorem HasSectionsPresentation.restrict {M : SheafOfModules.{w} R} {Z W : C} (g : W ⟶ Z)
    (h : HasSectionsPresentation J M Z) : HasSectionsPresentation J M W := by
  obtain ⟨n, q, s, r, hr, hs, hrel⟩ := h
  exact ⟨n, q, fun i => M.val.restrictₛₗ g.op (s i), fun k i => R.obj.map g.op (r k i),
    fun k => by rw [← restrict_sum_smul g (r k) s, hr k, map_zero],
    generates_restrict g s hs, generatesRelations_restrict s r hrel g⟩

/-- A finite family of covering sieves has a covering sieve refining all of them. -/
theorem exists_sieve_le_of_fin {U : C} : (n : ℕ) → (S : Fin n → Sieve U) → (∀ i, S i ∈ J U) →
    ∃ T : Sieve U, T ∈ J U ∧ ∀ i, T ≤ S i
  | 0, _, _ => ⟨⊤, J.top_mem U, fun i => Fin.elim0 i⟩
  | n + 1, S, hS => by
      obtain ⟨T, hT, hle⟩ := exists_sieve_le_of_fin n (fun i => S i.succ) fun i => hS i.succ
      refine ⟨S 0 ⊓ T, J.intersection_covering (hS 0) hT, fun i => ?_⟩
      rcases i with ⟨i, hi⟩
      rcases i with _ | i
      · exact fun Y f hf => hf.1
      · exact fun Y f hf => hle ⟨i, by omega⟩ f hf.2

/-- **The sieve along which a given relation is a combination of given rows.**  It consists of
the arrows `g` along which the restriction of `τ` is a combination of the restricted rows `r`. -/
def relationCombinationSieve {Z : C} {n q : ℕ} (r : Fin q → Fin n → R.obj.obj (op Z)) {V : C}
    (hV : V ⟶ Z) (τ : Fin n → R.obj.obj (op V)) : Sieve V where
  arrows B g := ∃ d : Fin q → R.obj.obj (op B), ∀ i,
    ∑ k, d k * R.obj.map (g ≫ hV).op (r k i) = R.obj.map g.op (τ i)
  downward_closed := by
    rintro B B' f ⟨d, hd⟩ g
    refine ⟨fun k => R.obj.map g.op (d k), fun i => ?_⟩
    rw [← ring_map_map f g (τ i), ← hd i, ring_map_sum_mul]
    refine Finset.sum_congr rfl fun k _ =>
      congrArg (fun z => R.obj.map g.op (d k) * z) ?_
    rw [ring_map_map (f ≫ hV) g (r k i)]
    exact congrArg (fun m : B' ⟶ Z => R.obj.map m.op (r k i)) (Category.assoc g f hV)

/-- **The local step of Stacks 01BY (4) for finite presentation.**  Let `ι` be a kernel of `pr`.
Suppose that over `Z` the outer terms carry section-level finite presentation data, that each
generator of `X₃` lifts to a section `t` of the middle term, and that each relation `r₃ k` among
the generators of `X₃`, applied to those lifts, lands in `X₁` on a combination of the generators
of `X₁` with coefficients `cc k`.  Then the middle term carries section-level finite presentation
data over `Z`. -/
theorem hasSectionsPresentation_of_data {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {ι : X₁ ⟶ X₂} {pr : X₂ ⟶ X₃} (hz : ι ≫ pr = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    {Z : C} {n₁ q₁ n₃ q₃ : ℕ}
    (s₁ : Fin n₁ → X₁.val.obj (op Z)) (r₁ : Fin q₁ → Fin n₁ → R.obj.obj (op Z))
    (hr₁ : ∀ k, ∑ i, r₁ k i • s₁ i = 0) (hs₁ : Generates J X₁.val s₁)
    (hrel₁ : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n₁ → R.obj.obj (op V)),
      (∑ i, τ i • X₁.val.restrictₛₗ hV.op (s₁ i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin q₁ → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r₁ k i) = R.obj.map g.op (τ i))
    (s₃ : Fin n₃ → X₃.val.obj (op Z)) (r₃ : Fin q₃ → Fin n₃ → R.obj.obj (op Z))
    (hs₃ : Generates J X₃.val s₃)
    (hrel₃ : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n₃ → R.obj.obj (op V)),
      (∑ i, τ i • X₃.val.restrictₛₗ hV.op (s₃ i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin q₃ → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r₃ k i) = R.obj.map g.op (τ i))
    (t : Fin n₃ → X₂.val.obj (op Z)) (ht : ∀ j, Hom.app pr.val (op Z) (t j) = s₃ j)
    (cc : Fin q₃ → Fin n₁ → R.obj.obj (op Z))
    (hcc : ∀ k, Hom.app ι.val (op Z) (∑ i, cc k i • s₁ i) = ∑ j, r₃ k j • t j) :
    HasSectionsPresentation J X₂ Z := by
  have hmono : Mono ι := mono_of_isLimit_fork hι
  have hinj : ∀ X : Cᵒᵖ, Function.Injective (Hom.app ι.val X) := injective_val_of_mono ι
  refine ⟨n₁ + n₃, q₁ + q₃,
    Fin.append (fun i => Hom.app ι.val (op Z) (s₁ i)) t,
    Fin.append (fun l => Fin.append (r₁ l) (fun _ => 0))
      (fun k => Fin.append (fun i => -(cc k i)) (r₃ k)),
    ?_, generates_middle_of_lifts hz hι s₁ s₃ t hs₁ hs₃ ht, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun k => ?_)
    · simp only [Fin.append_left, Fin.sum_univ_add, Fin.append_right, zero_smul,
        Finset.sum_const_zero, add_zero]
      rw [← hom_app_sum_smul ι.val (op Z) (r₁ l) s₁, hr₁ l, map_zero]
    · simp only [Fin.append_right, Fin.sum_univ_add, Fin.append_left]
      have e : ∑ i, -(cc k i) • Hom.app ι.val (op Z) (s₁ i)
          = -(Hom.app ι.val (op Z) (∑ i, cc k i • s₁ i)) := by
        rw [hom_app_sum_smul ι.val (op Z) (cc k) s₁, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => neg_smul (cc k i) _
      rw [e, hcc k, neg_add_cancel]
  · intro V hV τ hτ
    refine ⟨relationCombinationSieve (Fin.append (fun l => Fin.append (r₁ l) (fun _ => 0))
      (fun k => Fin.append (fun i => -(cc k i)) (r₃ k))) hV τ, ?_, fun B g hg => hg⟩
    have hβ : ∑ j, τ (Fin.natAdd n₁ j) • X₃.val.restrictₛₗ hV.op (s₃ j) = 0 := by
      have h0 := congrArg (Hom.app pr.val (op V)) hτ
      rw [hom_app_sum_smul pr.val (op V), map_zero, Fin.sum_univ_add] at h0
      have hzero : ∀ i : Fin n₁,
          Hom.app pr.val (op Z) (Hom.app ι.val (op Z) (s₁ i)) = 0 := fun i => by
        rw [← comp_val_app_apply, hz]
        rfl
      have hnat : ∀ x, Hom.app pr.val (op V) (X₂.val.restrictₛₗ hV.op x)
          = X₃.val.restrictₛₗ hV.op (Hom.app pr.val (op Z) x) := fun x =>
        PresheafOfModules.naturality_apply pr.val hV.op x
      simpa only [Fin.append_left, Fin.append_right, hnat, hzero, ht, map_zero,
        smul_zero, Finset.sum_const_zero, zero_add] using h0
    obtain ⟨T₃, hT₃, hd₃⟩ := hrel₃ V hV (fun j => τ (Fin.natAdd n₁ j)) hβ
    refine J.transitive hT₃ _ fun B g hg => ?_
    obtain ⟨d, hd⟩ := hd₃ g hg
    have hα : ∑ i, (R.obj.map g.op (τ (Fin.castAdd n₃ i))
          + ∑ k, d k * R.obj.map (g ≫ hV).op (cc k i)) •
        X₁.val.restrictₛₗ (g ≫ hV).op (s₁ i) = 0 := by
      refine hinj (op B) ?_
      rw [hom_app_sum_smul ι.val (op B), map_zero]
      have hres : ∀ i, Hom.app ι.val (op B) (X₁.val.restrictₛₗ (g ≫ hV).op (s₁ i))
          = X₂.val.restrictₛₗ (g ≫ hV).op (Hom.app ι.val (op Z) (s₁ i)) := fun i =>
        PresheafOfModules.naturality_apply ι.val (g ≫ hV).op (s₁ i)
      simp only [hres, add_smul, Finset.sum_add_distrib]
      have hone : ∑ i, R.obj.map g.op (τ (Fin.castAdd n₃ i)) •
            X₂.val.restrictₛₗ (g ≫ hV).op (Hom.app ι.val (op Z) (s₁ i))
          = -∑ j, R.obj.map g.op (τ (Fin.natAdd n₁ j)) •
            X₂.val.restrictₛₗ (g ≫ hV).op (t j) := by
        have h0 := congrArg (X₂.val.restrictₛₗ g.op) hτ
        rw [restrict_sum_smul g τ _, map_zero, Fin.sum_univ_add] at h0
        simp only [restrict_restrict, Fin.append_left, Fin.append_right] at h0
        exact add_eq_zero_iff_eq_neg.mp h0
      have htwo : ∑ i, (∑ k, d k * R.obj.map (g ≫ hV).op (cc k i)) •
            X₂.val.restrictₛₗ (g ≫ hV).op (Hom.app ι.val (op Z) (s₁ i))
          = ∑ j, R.obj.map g.op (τ (Fin.natAdd n₁ j)) •
            X₂.val.restrictₛₗ (g ≫ hV).op (t j) := by
        rw [← sum_smul_sum_smul_of_fin d (fun k i => R.obj.map (g ≫ hV).op (cc k i))
          (fun i => X₂.val.restrictₛₗ (g ≫ hV).op (Hom.app ι.val (op Z) (s₁ i)))]
        have hk : ∀ k, ∑ i, R.obj.map (g ≫ hV).op (cc k i) •
              X₂.val.restrictₛₗ (g ≫ hV).op (Hom.app ι.val (op Z) (s₁ i))
            = ∑ j, R.obj.map (g ≫ hV).op (r₃ k j) •
              X₂.val.restrictₛₗ (g ≫ hV).op (t j) := fun k => by
          rw [← restrict_sum_smul (g ≫ hV) (cc k)
              (fun i => Hom.app ι.val (op Z) (s₁ i)),
            ← hom_app_sum_smul ι.val (op Z) (cc k) s₁, hcc k,
            restrict_sum_smul (g ≫ hV) (r₃ k) t]
        rw [Finset.sum_congr rfl fun k _ => congrArg (fun z => d k • z) (hk k),
          sum_smul_sum_smul_of_fin d (fun k j => R.obj.map (g ≫ hV).op (r₃ k j))
          (fun j => X₂.val.restrictₛₗ (g ≫ hV).op (t j))]
        exact Finset.sum_congr rfl fun j _ => congrArg
          (fun z => z • X₂.val.restrictₛₗ (g ≫ hV).op (t j)) (hd j)
      rw [hone, htwo, neg_add_cancel]
    obtain ⟨T₁, hT₁, hd₁⟩ := hrel₁ B (g ≫ hV) _ hα
    refine J.superset_covering (fun B' h hh => ?_) hT₁
    obtain ⟨e, he⟩ := hd₁ h hh
    refine ⟨Fin.append e (fun k => R.obj.map h.op (d k)), ?_⟩
    have hcomp : ∀ (x : R.obj.obj (op Z)), R.obj.map (h ≫ g ≫ hV).op x
        = R.obj.map h.op (R.obj.map (g ≫ hV).op x) := fun x =>
      (ring_map_map (g ≫ hV) h x).symm
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      rw [show ((h ≫ g) ≫ hV) = h ≫ g ≫ hV from Category.assoc h g hV]
      have h3 : ∑ l, e l * R.obj.map (h ≫ g ≫ hV).op (r₁ l i)
          = R.obj.map h.op (R.obj.map g.op (τ (Fin.castAdd n₃ i)))
            + ∑ k, R.obj.map h.op (d k) * R.obj.map (h ≫ g ≫ hV).op (cc k i) := by
        rw [show (h ≫ g ≫ hV) = h ≫ (g ≫ hV) from rfl, he i, ring_map_add,
          ring_map_sum_mul]
        simp only [hcomp]
      have h2 : ∑ k, R.obj.map h.op (d k) * R.obj.map (h ≫ g ≫ hV).op (-(cc k i))
          = -∑ k, R.obj.map h.op (d k) * R.obj.map (h ≫ g ≫ hV).op (cc k i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [ring_map_neg, mul_neg]
      rw [h3, h2, add_neg_cancel_right, ring_map_map]
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      rw [show ((h ≫ g) ≫ hV) = h ≫ g ≫ hV from Category.assoc h g hV]
      have hz0 : ∑ l : Fin q₁, e l * R.obj.map (h ≫ g ≫ hV).op (0 : R.obj.obj (op Z)) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [ring_map_zero, mul_zero]
      have h4 : ∑ k, R.obj.map h.op (d k) * R.obj.map (h ≫ g ≫ hV).op (r₃ k j)
          = R.obj.map h.op (R.obj.map g.op (τ (Fin.natAdd n₁ j))) := by
        rw [← hd j, ring_map_sum_mul]
        simp only [hcomp]
      rw [hz0, h4, zero_add, ring_map_map]

/-- **Stacks 01BY (4) for finite presentation, the second refinement.**  Given section-level
presentation data for the outer terms over `Z` and lifts `t` of the generators of `X₃`, the middle
term carries section-level presentation data on a covering of `Z`. -/
theorem exists_sieve_hasSectionsPresentation_of_lifts {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {ι : X₁ ⟶ X₂} {pr : X₂ ⟶ X₃} (hz : ι ≫ pr = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    {Z : C} {n₁ q₁ n₃ q₃ : ℕ}
    (s₁ : Fin n₁ → X₁.val.obj (op Z)) (r₁ : Fin q₁ → Fin n₁ → R.obj.obj (op Z))
    (hr₁ : ∀ k, ∑ i, r₁ k i • s₁ i = 0) (hs₁ : Generates J X₁.val s₁)
    (hrel₁ : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n₁ → R.obj.obj (op V)),
      (∑ i, τ i • X₁.val.restrictₛₗ hV.op (s₁ i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin q₁ → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r₁ k i) = R.obj.map g.op (τ i))
    (s₃ : Fin n₃ → X₃.val.obj (op Z)) (r₃ : Fin q₃ → Fin n₃ → R.obj.obj (op Z))
    (hr₃ : ∀ k, ∑ i, r₃ k i • s₃ i = 0) (hs₃ : Generates J X₃.val s₃)
    (hrel₃ : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n₃ → R.obj.obj (op V)),
      (∑ i, τ i • X₃.val.restrictₛₗ hV.op (s₃ i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin q₃ → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r₃ k i) = R.obj.map g.op (τ i))
    (t : Fin n₃ → X₂.val.obj (op Z)) (ht : ∀ j, Hom.app pr.val (op Z) (t j) = s₃ j) :
    ∃ T : Sieve Z, T ∈ J Z ∧ ∀ ⦃B : C⦄ (g : B ⟶ Z), T.arrows g →
      HasSectionsPresentation J X₂ B := by
  have hker : ∀ k : Fin q₃, Hom.app pr.val (op Z) (∑ j, r₃ k j • t j) = 0 := fun k => by
    rw [hom_app_sum_smul pr.val (op Z)]
    simp only [ht]
    exact hr₃ k
  choose y hy using fun k => exists_app_eq_of_isLimit hz hι (op Z) _ (hker k)
  choose S hS hcomb using fun k => hs₁ Z (𝟙 Z) (y k)
  obtain ⟨T, hT, hle⟩ := exists_sieve_le_of_fin q₃ S hS
  refine ⟨T, hT, fun B g hg => ?_⟩
  choose cc hcc using fun k => hcomb k B g (hle k g hg)
  refine hasSectionsPresentation_of_data hz hι
    (fun i => X₁.val.restrictₛₗ g.op (s₁ i)) (fun k i => R.obj.map g.op (r₁ k i))
    (fun k => by rw [← restrict_sum_smul g (r₁ k) s₁, hr₁ k, map_zero])
    (generates_restrict g s₁ hs₁) (generatesRelations_restrict s₁ r₁ hrel₁ g)
    (fun j => X₃.val.restrictₛₗ g.op (s₃ j)) (fun k j => R.obj.map g.op (r₃ k j))
    (generates_restrict g s₃ hs₃) (generatesRelations_restrict s₃ r₃ hrel₃ g)
    (fun j => X₂.val.restrictₛₗ g.op (t j)) (fun j => ?_) cc (fun k => ?_)
  · exact (PresheafOfModules.naturality_apply pr.val g.op (t j)).trans
      (congrArg (X₃.val.restrictₛₗ g.op) (ht j))
  · have hccg : ∑ i, cc k i • X₁.val.restrictₛₗ g.op (s₁ i) = X₁.val.restrictₛₗ g.op (y k) := by
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hcc k)
      exact congrArg (fun z => cc k i • z)
        (congrArg (fun f : B ⟶ Z => X₁.val.restrictₛₗ f.op (s₁ i)) (Category.comp_id g).symm)
    rw [hccg, show Hom.app ι.val (op B) (X₁.val.restrictₛₗ g.op (y k))
      = X₂.val.restrictₛₗ g.op (Hom.app ι.val (op Z) (y k)) from
        PresheafOfModules.naturality_apply ι.val g.op (y k), hy k, restrict_sum_smul g (r₃ k) t]

/-- **Stacks 01BY (4) for finite presentation, both refinements.**  If `ι` is a kernel of a
locally surjective `pr` and the outer terms carry section-level presentation data over `Z`, then
the middle term carries it on a covering of `Z`. -/
theorem exists_sieve_hasSectionsPresentation {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {ι : X₁ ⟶ X₂} {pr : X₂ ⟶ X₃} (hz : ι ≫ pr = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    (hp : PresheafOfModules.IsLocallySurjective J pr.val) {Z : C}
    (h₁ : HasSectionsPresentation J X₁ Z) (h₃ : HasSectionsPresentation J X₃ Z) :
    ∃ T : Sieve Z, T ∈ J Z ∧ ∀ ⦃B : C⦄ (g : B ⟶ Z), T.arrows g →
      HasSectionsPresentation J X₂ B := by
  obtain ⟨n₁, q₁, s₁, r₁, hr₁, hs₁, hrel₁⟩ := h₁
  obtain ⟨n₃, q₃, s₃, r₃, hr₃, hs₃, hrel₃⟩ := h₃
  have hstage : ∀ (W : C) (g : W ⟶ Z), (commonLiftSieve pr n₃ s₃).arrows g →
      ∃ T : Sieve W, T ∈ J W ∧ ∀ ⦃B : C⦄ (gg : B ⟶ W), T.arrows gg →
        HasSectionsPresentation J X₂ B := by
    intro W g hg
    choose t ht using fun j =>
      (LocalImage.mem_imageSieveOfHom pr (s₃ j) g).1 (commonLiftSieve_le pr n₃ s₃ j g hg)
    exact exists_sieve_hasSectionsPresentation_of_lifts hz hι
      (fun i => X₁.val.restrictₛₗ g.op (s₁ i)) (fun k i => R.obj.map g.op (r₁ k i))
      (fun k => by rw [← restrict_sum_smul g (r₁ k) s₁, hr₁ k, map_zero])
      (generates_restrict g s₁ hs₁) (generatesRelations_restrict s₁ r₁ hrel₁ g)
      (fun j => X₃.val.restrictₛₗ g.op (s₃ j)) (fun k j => R.obj.map g.op (r₃ k j))
      (fun k => by rw [← restrict_sum_smul g (r₃ k) s₃, hr₃ k, map_zero])
      (generates_restrict g s₃ hs₃) (generatesRelations_restrict s₃ r₃ hrel₃ g) t ht
  choose Rs hRs hdata using hstage
  refine ⟨Sieve.bind (commonLiftSieve pr n₃ s₃).arrows (fun {Y} {f} hf => Rs Y f hf),
    J.bind_covering (commonLiftSieve_mem pr hp n₃ s₃) (fun {Y} {f} hf => hRs Y f hf), ?_⟩
  rintro B g ⟨W, u, v, hv, hu, rfl⟩
  exact hdata W v hv u hu

/-- **Stacks 01BY (4) for finite presentation on a site.**  If `ι` is a kernel of `pr`, `pr` is
locally surjective and the outer terms are of finite presentation, then so is the middle term. -/
theorem isFinitePresentationOnSite_middle {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {ι : X₁ ⟶ X₂} {pr : X₂ ⟶ X₃} (hz : ι ≫ pr = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    (hp : PresheafOfModules.IsLocallySurjective J pr.val)
    (h₁ : X₁.IsFinitePresentationOnSite) (h₃ : X₃.IsFinitePresentationOnSite) :
    X₂.IsFinitePresentationOnSite := by
  constructor
  intro U
  refine ⟨{ V : Over U // HasSectionsPresentation J X₂ V.left }, fun i => i.1.left,
    fun i => i.1.hom, ?_,
    fun i => hasFiniteGlobalPresentation_over_of_hasSectionsPresentation i.2⟩
  obtain ⟨I₁, V₁, f₁, hc₁, hpr₁⟩ := h₁.locally_hasFiniteGlobalPresentation U
  obtain ⟨I₃, V₃, f₃, hc₃, hpr₃⟩ := h₃.locally_hasFiniteGlobalPresentation U
  refine J.transitive (J.intersection_covering hc₁ hc₃) _ fun Y g hg => ?_
  obtain ⟨i₁, b₁, hb₁⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg.1
  obtain ⟨i₃, b₃, hb₃⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg.2
  obtain ⟨T, hT, hdata⟩ := exists_sieve_hasSectionsPresentation hz hι hp
    (HasSectionsPresentation.restrict b₁
      (hasSectionsPresentation_of_hasFiniteGlobalPresentation X₁ (V₁ i₁) (hpr₁ i₁)))
    (HasSectionsPresentation.restrict b₃
      (hasSectionsPresentation_of_hasFiniteGlobalPresentation X₃ (V₃ i₃) (hpr₃ i₃)))
  refine J.superset_covering (fun B u hu => ?_) hT
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr
    ⟨⟨Over.mk (u ≫ g), hdata u hu⟩, 𝟙 B, (Category.id_comp (u ≫ g)).symm⟩

/-- **Stacks 01BY (4) for finite presentation on a site, from a kernel fork and a cokernel
cofork.**  If `φ` is a kernel of `ψ`, `ψ` is a cokernel of `φ` and the outer terms are of finite
presentation, then so is the middle term. -/
theorem isFinitePresentationOnSite_X₂_of_kernel_cokernel {X₁ X₂ X₃ : SheafOfModules.{w} R}
    {φ : X₁ ⟶ X₂} {ψ : X₂ ⟶ X₃} (hz : φ ≫ ψ = 0)
    (hφ : IsLimit (KernelFork.ofι φ hz)) (hψ : IsColimit (CokernelCofork.ofπ ψ hz))
    (h₁ : X₁.IsFinitePresentationOnSite) (h₃ : X₃.IsFinitePresentationOnSite) :
    X₂.IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_middle hz hφ (isLocallySurjective_of_isColimit hz hψ) h₁ h₃

/-- **Stacks 01BY (4) for finite presentation on a site, for a short exact sequence.**  When the
category of sheaves of modules is balanced, the middle term of a short exact sequence whose outer
terms are of finite presentation is of finite presentation. -/
theorem isFinitePresentationOnSite_X₂_of_shortExact [Balanced (SheafOfModules.{w} R)]
    {T : ShortComplex (SheafOfModules.{w} R)} (hT : T.ShortExact)
    (h₁ : T.X₁.IsFinitePresentationOnSite) (h₃ : T.X₃.IsFinitePresentationOnSite) :
    T.X₂.IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_X₂_of_kernel_cokernel T.zero hT.fIsKernel hT.gIsCokernel h₁ h₃

end Middle

end Stacks.SheafOfModules

end
