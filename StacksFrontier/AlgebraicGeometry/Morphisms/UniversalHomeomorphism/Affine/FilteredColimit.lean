module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal homeomorphisms and filtered colimits of algebras

Let `A` be a commutative ring and let a commutative `A`-algebra `B` be exhibited as the
filtered colimit of a diagram of commutative `A`-algebras. Each of the properties "universally
closed", "universally injective", "universal homeomorphism" and "induces isomorphisms on
residue fields" holds for the spectrum morphism of `B` over `Spec A` as soon as it holds for
every algebra in the diagram.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.universallyClosed_specMap_of_isColimit`,
  `AlgebraicGeometry.universallyInjective_specMap_of_isColimit` and
  `AlgebraicGeometry.universalHomeomorphism_specMap_of_isColimit`: the three morphism
  properties pass to a filtered colimit.
* `AlgebraicGeometry.isIso_residueFieldMap_specMap_of_colimitPresentation`: so does inducing
  isomorphisms on residue fields.

## Implementation notes

The equation `B = colim Bλ` is represented by a cocone in `CommAlgCat A` together with its
universal property, or, for the residue-field statement, by a `ColimitPresentation`. Its apex
is therefore the algebra denoted by `B` above. Filtered colimits of commutative algebras are
computed on their underlying rings, which is the content of
`AlgebraicGeometry.isColimit_forget₂_commRingCat` and is what lets the point-set arguments
descend to a stage of the diagram.

## References

* [Stacks Project, Tag 0CN8](https://stacks.math.columbia.edu/tag/0CN8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A filtered colimit of commutative `A`-algebras is computed on the underlying rings. -/
noncomputable def isColimit_forget₂_commRingCat
    (A : Type u) [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : Functor J (CommAlgCat.{u} A)) (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} A) CommRingCat).mapCocone c) := by
  have : IsConnected J := IsFiltered.isConnected J
  have : PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} A) CommRingCat) := by
    change PreservesColimitsOfShape J
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙ Under.forget (CommRingCat.of A))
    infer_instance
  exact isColimitOfPreserves _ hc

/-- Every element of a filtered colimit of commutative `A`-algebras comes from some stage. -/
lemma exists_rep_of_isColimit_commAlgCat (A : Type u) [CommRing A] {J : Type v}
    [Category.{w} J] [IsFiltered J] {F : Functor J (CommAlgCat.{u} A)} {c : Cocone F}
    (hc : IsColimit c) (b : c.pt) : ∃ i y, (c.ι.app i).hom y = b := by
  have : Nonempty J := IsFiltered.nonempty
  have hw {i j : J} (g : i ⟶ j) (y : F.obj i) :
      (c.ι.app j).hom ((F.map g).hom y) = (c.ι.app i).hom y :=
    congrArg (fun h => h.hom y) (c.w g)
  let S : Subalgebra A c.pt := {
    carrier := { b | ∃ i y, (c.ι.app i).hom y = b }
    zero_mem' := ⟨Classical.arbitrary J, 0, by simp⟩
    add_mem' := by
      rintro _ _ ⟨i, y, rfl⟩ ⟨j, z, rfl⟩
      exact ⟨IsFiltered.max i j, (F.map (IsFiltered.leftToMax i j)).hom y +
        (F.map (IsFiltered.rightToMax i j)).hom z, by rw [map_add, hw, hw]⟩
    one_mem' := ⟨Classical.arbitrary J, 1, by simp⟩
    mul_mem' := by
      rintro _ _ ⟨i, y, rfl⟩ ⟨j, z, rfl⟩
      exact ⟨IsFiltered.max i j, (F.map (IsFiltered.leftToMax i j)).hom y *
        (F.map (IsFiltered.rightToMax i j)).hom z, by rw [map_mul, hw, hw]⟩
    algebraMap_mem' a := ⟨Classical.arbitrary J, algebraMap A (F.obj (Classical.arbitrary J)) a,
      (c.ι.app (Classical.arbitrary J)).hom.commutes a⟩ }
  let d : Cocone F := {
    pt := CommAlgCat.of A S
    ι := {
      app i := CommAlgCat.ofHom ((c.ι.app i).hom.codRestrict S fun y => ⟨i, y, rfl⟩)
      naturality i j g := by
        apply CommAlgCat.hom_ext
        ext y
        exact Subtype.ext (hw g y) } }
  have hd : hc.desc d ≫ CommAlgCat.ofHom S.val = 𝟙 c.pt := by
    refine hc.hom_ext fun i => ?_
    rw [← Category.assoc, hc.fac, Category.comp_id]
    apply CommAlgCat.hom_ext
    ext y
    rfl
  obtain ⟨i, y, hy⟩ := ((hc.desc d).hom b).property
  exact ⟨i, y, hy.trans (congrArg (fun h => h.hom b) hd)⟩

/-- A filtered colimit of integral `A`-algebras is integral: the colimit maps onto the integral
closure of `A` in it, by the cocone into that integral closure. -/
lemma colimit_algebra_isIntegral (A : Type u) [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : Functor J (CommAlgCat.{u} A)) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ j, Algebra.IsIntegral A (F.obj j)) : Algebra.IsIntegral A c.pt :=
  Algebra.isIntegral_def.mpr fun x => by
    obtain ⟨j, y, rfl⟩ := exists_rep_of_isColimit_commAlgCat A hc x
    exact ((Algebra.isIntegral_def.mp (h j)) y).map (c.ι.app j).hom

/-- **Stacks 0CN8.** A filtered colimit of commutative `A`-algebras whose spectrum morphisms to
`Spec A` are universally closed again has universally closed spectrum morphism to `Spec A`. -/
@[stacks 0CN8 "universally_closed"]
lemma universallyClosed_specMap_of_isColimit
    (A : Type u) [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : Functor J (CommAlgCat.{u} A)) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ j, UniversallyClosed
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op)) :
    UniversallyClosed
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A c.pt)).op) := by
  have hstage (j : J) : Algebra.IsIntegral A (F.obj j) :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp
      (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨h j, inferInstance⟩))
  exact (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp
    (IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr
      (colimit_algebra_isIntegral A F c hc hstage)))).1

/-- The spectrum of an `A`-algebra map commutes with the structure maps to `Spec A`. -/
private lemma specMap_algHom_comp_specMap_algebraMap {A R S : Type u} [CommRing A] [CommRing R]
    [CommRing S] [Algebra A R] [Algebra A S] (φ : R →ₐ[A] S) :
    Scheme.Spec.map (CommRingCat.ofHom φ.toRingHom).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op := by
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A R)) =
    Spec.map (CommRingCat.ofHom (algebraMap A S))
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact φ.commutes a

/-- **Stacks 0CN8.** A filtered colimit of commutative `A`-algebras whose spectrum morphisms to
`Spec A` are universally injective again has universally injective spectrum morphism to
`Spec A`. -/
@[stacks 0CN8 "closed_injective"]
lemma universallyInjective_specMap_of_isColimit
    (A : Type u) [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : Functor J (CommAlgCat.{u} A)) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ j, UniversallyInjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op)) :
    UniversallyInjective
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A c.pt)).op) := by
  apply ((tfae_universallyInjective
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A c.pt)).op)).out 2 1).mp
  intro K _ g₁ g₂ hg
  apply (Spec.homEquiv).injective
  refine (isColimit_forget₂_commRingCat A F c hc).hom_ext fun j => ?_
  apply (Spec.homEquiv).symm.injective
  simp only [Spec.homEquiv_symm_apply, Spec.homEquiv_apply, Spec.map_comp,
    Spec.map_preimage]
  change g₁ ≫ Scheme.Spec.map (CommRingCat.ofHom (c.ι.app j).hom.toRingHom).op =
    g₂ ≫ Scheme.Spec.map (CommRingCat.ofHom (c.ι.app j).hom.toRingHom).op
  have hj := ((tfae_universallyInjective
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op)).out 1 2).mp (h j)
  exact hj K (by simpa only [Category.assoc, specMap_algHom_comp_specMap_algebraMap] using hg)

/-- If `Spec R → Spec A` is universally injective, any two `A`-algebra maps from `R` to a field
agree. -/
lemma algHom_eq_of_universallyInjective {A R K : Type u} [CommRing A] [CommRing R]
    [Algebra A R] [Field K] [Algebra A K]
    (h : UniversallyInjective (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op))
    (φ₁ φ₂ : R →ₐ[A] K) : φ₁ = φ₂ := by
  have hinj := ((tfae_universallyInjective
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op)).out 1 2).mp h
  have hspec : Scheme.Spec.map ((CommRingCat.ofHom φ₁.toRingHom).op) =
      Scheme.Spec.map ((CommRingCat.ofHom φ₂.toRingHom).op) :=
    hinj K <| (specMap_algHom_comp_specMap_algebraMap φ₁).trans
      (specMap_algHom_comp_specMap_algebraMap φ₂).symm
  exact AlgHom.toRingHom_injective
    (congrArg CommRingCat.Hom.hom ((Spec.homEquiv).symm.injective hspec))

/-- If every stage of a filtered colimit of `A`-algebras has universally homeomorphic spectrum
morphism to `Spec A`, then every prime of `A` contains the kernel of `A → colim`. -/
lemma ker_algebraMap_le_of_isColimit
    (A : Type u) [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : Functor J (CommAlgCat.{u} A)) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ j, UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op))
    (p : PrimeSpectrum A) : RingHom.ker (algebraMap A c.pt) ≤ p.asIdeal := by
  classical
  have hstage (j : J) := (universalHomeomorphism_iff_integral_universallyInjective_surjective
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op)).mp (h j)
  let Ω := AlgebraicClosure p.asIdeal.ResidueField
  let q (j : J) : PrimeSpectrum (F.obj j) :=
    Classical.choose ((surjective_iff _).mp (hstage j).2.2 p)
  have hq (j : J) : (q j).comap (algebraMap A (F.obj j)) = p :=
    Classical.choose_spec ((surjective_iff _).mp (hstage j).2.2 p)
  have hq' (j : J) : p.asIdeal = (q j).asIdeal.comap (algebraMap A (F.obj j)) := by
    rw [← hq j, PrimeSpectrum.comap_asIdeal]
  let μ (j : J) : F.obj j →ₐ[A] Ω := by
    have : Algebra.IsIntegral A (F.obj j) :=
      algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp (hstage j).1)
    have : (q j).asIdeal.LiesOver p.asIdeal := (Ideal.liesOver_iff _ _).2 (hq' j)
    let : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (q j).asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal (q j).asIdeal
    have : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (q j).asIdeal) := inferInstance
    have : Algebra.IsAlgebraic p.asIdeal.ResidueField (q j).asIdeal.ResidueField :=
      inferInstance
    let ψ' : (q j).asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] Ω := IsAlgClosed.lift
    let θ : F.obj j →ₐ[A] (q j).asIdeal.ResidueField :=
      { toRingHom := algebraMap (F.obj j) (q j).asIdeal.ResidueField
        commutes' a :=
          (IsScalarTower.algebraMap_apply A (F.obj j) (q j).asIdeal.ResidueField a).symm }
    exact (ψ'.restrictScalars A).comp θ
  let d : Cocone F := {
    pt := CommAlgCat.of A Ω
    ι := {
      app j := CommAlgCat.ofHom (μ j)
      naturality i j g := by
        change F.map g ≫ CommAlgCat.ofHom (μ j) =
          CommAlgCat.ofHom (μ i) ≫ 𝟙 (CommAlgCat.of A Ω)
        rw [Category.comp_id]
        change CommAlgCat.ofHom ((μ j).comp (F.map g).hom) = CommAlgCat.ofHom (μ i)
        exact congrArg CommAlgCat.ofHom (algHom_eq_of_universallyInjective (hstage i).2.1
          ((μ j).comp (F.map g).hom) (μ i)) } }
  intro a ha
  have hzero : algebraMap A Ω a = 0 := by
    have hcomm := (hc.desc d).hom.commutes a
    rw [RingHom.mem_ker.mp ha] at hcomm
    simpa using hcomm.symm
  have hzero' : algebraMap p.asIdeal.ResidueField Ω
      (algebraMap A p.asIdeal.ResidueField a) = 0 :=
    (IsScalarTower.algebraMap_apply A p.asIdeal.ResidueField Ω a).symm.trans hzero
  exact Ideal.algebraMap_residueField_eq_zero.mp
    ((FaithfulSMul.algebraMap_injective p.asIdeal.ResidueField Ω) (by simpa using hzero'))

/-- **Stacks 0CN8.** A filtered colimit of commutative `A`-algebras whose spectrum morphisms to
`Spec A` are universal homeomorphisms again has universal-homeomorphic spectrum morphism to
`Spec A`. -/
@[stacks 0CN8 "universal_homeomorphism"]
lemma universalHomeomorphism_specMap_of_isColimit
    (A : Type u) [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : Functor J (CommAlgCat.{u} A)) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ j, UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A c.pt)).op) := by
  classical
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A c.pt)).op
  have hstage (j : J) := (universalHomeomorphism_iff_integral_universallyInjective_surjective
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (F.obj j))).op)).mp (h j)
  have hcolim : Algebra.IsIntegral A c.pt := colimit_algebra_isIntegral A F c hc fun j =>
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp (hstage j).1)
  have hsurj : Surjective f := by
    rw [surjective_iff]
    change Function.Surjective (PrimeSpectrum.comap (algebraMap A c.pt))
    intro p
    obtain ⟨Q, _, hQ, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal
      (⊥ : Ideal c.pt) (ker_algebraMap_le_of_isColimit A F c hc h p)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQcomap⟩
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mpr
    ⟨IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr hcolim),
      universallyInjective_specMap_of_isColimit A F c hc fun j => (hstage j).2.1, hsurj⟩

/-- The residue-field map of `φ` at `y`, with source any prime equal to the contraction of `y`,
is an isomorphism as soon as the residue-field map of `Spec.map φ` at `y` is. -/
lemma isIso_idealResidueFieldMap_of_eq_comap {R S : CommRingCat.{u}} (φ : R ⟶ S) (y : Spec S)
    (P : Ideal R) [P.IsPrime] (hP : P = y.asIdeal.comap φ.hom)
    (h : IsIso ((Spec.map φ).residueFieldMap y)) :
    IsIso (CommRingCat.ofHom (Ideal.ResidueField.map P y.asIdeal φ.hom hP)) := by
  have : (Spec.map φ y).asIdeal.IsPrime := (Spec.map φ y).isPrime
  have hr : (Spec.map φ y).asIdeal = y.asIdeal.comap φ.hom := by
    simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal φ.hom y
  have hPr : P = (Spec.map φ y).asIdeal := hP.trans hr.symm
  have hPr' : P = (Spec.map φ y).asIdeal.comap (RingHom.id R) := by simpa using hPr
  have hcomp : CommRingCat.ofHom (Ideal.ResidueField.map P y.asIdeal φ.hom hP) =
      CommRingCat.ofHom (Ideal.ResidueField.map P _ (RingHom.id R) hPr') ≫
        CommRingCat.ofHom (Ideal.ResidueField.map _ y.asIdeal φ.hom hr) := by
    apply CommRingCat.hom_ext
    simpa [RingHom.comp_apply] using
      idealResidueFieldMap_comp P _ y.asIdeal (RingHom.id R) φ.hom hPr' hr
  have := idealResidueFieldMap_id_isIso P _ hPr
  have := idealResidueFieldMap_isIso_of_specMap φ y h
  rw [hcomp]
  infer_instance

/-- A ring map out of a ring covered by the images of a family of maps has kernel `Q` as soon as
each composite has kernel the contraction of `Q`. -/
lemma ker_eq_of_forall_exists_rep {R T : Type*} [CommRing R] [Semiring T] {ι : Type*}
    {S : ι → Type*} [∀ i, CommRing (S i)] (t : ∀ i, S i →+* R) (L : R →+* T) (Q : Ideal R)
    (hrep : ∀ b, ∃ i y, t i y = b) (hker : ∀ i, RingHom.ker (L.comp (t i)) = Q.comap (t i)) :
    RingHom.ker L = Q := by
  ext b
  obtain ⟨i, y, rfl⟩ := hrep b
  simpa using SetLike.ext_iff.mp (hker i) y

/-- The residue-field map of `f` from `P` to `Q` is bijective as soon as some ring map
`L : S → κ(P)` with kernel `Q` composes with it to the residue map of `S` at `Q`. -/
lemma bijective_residueFieldMap_of_comp_eq {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f)
    (L : S →+* P.ResidueField) (hker : RingHom.ker L = Q)
    (hL : (Ideal.ResidueField.map P Q f hPQ).comp L = algebraMap S Q.ResidueField) :
    Function.Bijective (Ideal.ResidueField.map P Q f hPQ) := by
  let e : Q.ResidueField →+* P.ResidueField :=
    Ideal.ResidueField.lift Q L (by rw [hker])
      fun b hb => isUnit_iff_ne_zero.mpr fun hzero => hb (hker ▸ hzero)
  have hround : (Ideal.ResidueField.map P Q f hPQ).comp e = RingHom.id _ := by
    apply Ideal.ResidueField.ringHom_ext
    ext b
    change Ideal.ResidueField.map P Q f hPQ (e (algebraMap S Q.ResidueField b)) = _
    rw [show e (algebraMap S Q.ResidueField b) = L b by
      simpa [e] using Ideal.ResidueField.lift_algebraMap (I := Q) (f := L) _ _ b]
    simpa using RingHom.congr_fun hL b
  refine ⟨RingHom.injective _, fun y => ⟨e y, ?_⟩⟩
  simpa using RingHom.congr_fun hround y

/-- A ring map `φ : R → S` whose residue-field map from `P` to `Q'` is bijective admits, for
every factorisation `f = ψ ∘ φ` with `Q'` the contraction of `Q`, a map `S → κ(P)` with kernel
`Q'` lifting the residue map of `ψ` at `Q`. -/
lemma exists_lift_residueField_of_bijective {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] (φ : R →+* S) (ψ : S →+* T) (f : R →+* T) (hf : ψ.comp φ = f)
    (P : Ideal R) [P.IsPrime] (Q' : Ideal S) [Q'.IsPrime] (Q : Ideal T) [Q.IsPrime]
    (hP : P = Q'.comap φ) (hQ' : Q' = Q.comap ψ) (hPQ : P = Q.comap f)
    (h : Function.Bijective (Ideal.ResidueField.map P Q' φ hP)) :
    ∃ ℓ : S →+* P.ResidueField, RingHom.ker ℓ = Q' ∧
      ∀ s, Ideal.ResidueField.map P Q f hPQ (ℓ s) = algebraMap T Q.ResidueField (ψ s) := by
  subst hf
  let e := RingEquiv.ofBijective _ h
  refine ⟨e.symm.toRingHom.comp (algebraMap S Q'.ResidueField), ?_, fun s => ?_⟩
  · ext s
    simp [RingHom.mem_ker, Ideal.algebraMap_residueField_eq_zero]
  · have he : Ideal.ResidueField.map P Q' φ hP (e.symm (algebraMap S _ s)) =
        algebraMap S Q'.ResidueField s := e.apply_symm_apply _
    refine (RingHom.congr_fun (idealResidueFieldMap_comp P Q' Q φ ψ hP hQ') _).trans ?_
    change Ideal.ResidueField.map Q' Q ψ hQ'
      (Ideal.ResidueField.map P Q' φ hP (e.symm (algebraMap S _ s))) = _
    rw [he]
    simp [Ideal.ResidueField.map_algebraMap]

/-- **Stacks 0CN8.** A filtered colimit of affine maps which induce isomorphisms on residue
fields still induces an isomorphism on the residue field at every point. -/
@[stacks 0CN8 "homeomorphism_equal_residue_fields"]
lemma isIso_residueFieldMap_specMap_of_colimitPresentation
    {A : Type u} [CommRing A] {J : Type v} [Category.{w} J] [IsFiltered J]
    {B : CommAlgCat.{u} A} (pres : ColimitPresentation J B)
    (hresidue : ∀ i x, IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(pres.diag.obj i))).op).residueFieldMap x)) :
    ∀ x, IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A ↥B)).op).residueFieldMap x) := by
  rintro (q : Spec (CommRingCat.of ↥B))
  let F := pres.diag ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat
  let c := (forget₂ (CommAlgCat.{u} A) CommRingCat).mapCocone pres.cocone
  let hc := isColimit_forget₂_commRingCat A pres.diag pres.cocone pres.isColimit
  let f : CommRingCat.of A ⟶ CommRingCat.of ↥B := CommRingCat.ofHom (algebraMap A ↥B)
  have : q.asIdeal.IsPrime := q.isPrime
  let fi (i : J) : CommRingCat.of A ⟶ F.obj i :=
    CommRingCat.ofHom (algebraMap A ↥(pres.diag.obj i))
  let ti (i : J) : F.obj i ⟶ CommRingCat.of ↥B :=
    (forget₂ (CommAlgCat.{u} A) CommRingCat).map (pres.ι.app i)
  let qi (i : J) : Spec (F.obj i) := Spec.map (ti i) q
  have hfac (i : J) : (ti i).hom.comp (fi i).hom = f.hom :=
    RingHom.ext (pres.ι.app i).hom.commutes
  let pI := (Spec.map f q).asIdeal
  have : pI.IsPrime := (Spec.map f q).isPrime
  have hfI : pI = q.asIdeal.comap f.hom := PrimeSpectrum.comap_asIdeal f.hom q
  have htiI (i : J) : (qi i).asIdeal = q.asIdeal.comap (ti i).hom :=
    PrimeSpectrum.comap_asIdeal (ti i).hom q
  have hpiI (i : J) : pI = (qi i).asIdeal.comap (fi i).hom := by
    rw [hfI, htiI i, Ideal.comap_comap, hfac i]
  have hst (i : J) := exists_lift_residueField_of_bijective (fi i).hom (ti i).hom f.hom (hfac i)
    pI (qi i).asIdeal q.asIdeal (hpiI i) (htiI i) hfI ((ConcreteCategory.isIso_iff_bijective _).1
      (isIso_idealResidueFieldMap_of_eq_comap (fi i) (qi i) pI (hpiI i) (hresidue i (qi i))))
  choose ℓ hℓker hℓ using hst
  let dRes : Cocone F := {
    pt := CommRingCat.of pI.ResidueField
    ι := {
      app i := CommRingCat.ofHom (ℓ i)
      naturality i j g := by
        ext s
        apply RingHom.injective (Ideal.ResidueField.map pI q.asIdeal f.hom hfI)
        change Ideal.ResidueField.map pI q.asIdeal f.hom hfI (ℓ j ((F.map g).hom s)) =
          Ideal.ResidueField.map pI q.asIdeal f.hom hfI (ℓ i s)
        rw [hℓ, hℓ]
        exact congrArg (fun k => algebraMap (↥B) q.asIdeal.ResidueField (k.hom s)) (c.w g) } }
  let L := hc.desc dRes
  have hL (i : J) : ti i ≫ L = CommRingCat.ofHom (ℓ i) := hc.fac dRes i
  have hker : RingHom.ker L.hom = q.asIdeal :=
    ker_eq_of_forall_exists_rep (fun i => (ti i).hom) L.hom q.asIdeal
      (exists_rep_of_isColimit_commAlgCat A pres.isColimit) fun i =>
      (congrArg (fun k => RingHom.ker k.hom) (hL i)).trans ((hℓker i).trans (htiI i))
  have hLm : (Ideal.ResidueField.map pI q.asIdeal f.hom hfI).comp L.hom =
      algebraMap (↥B) q.asIdeal.ResidueField := by
    ext b
    obtain ⟨i, y, rfl⟩ := exists_rep_of_isColimit_commAlgCat A pres.isColimit b
    change Ideal.ResidueField.map pI q.asIdeal f.hom hfI ((ti i ≫ L).hom y) = _
    rw [hL i]
    exact hℓ i y
  change IsIso ((Spec.map f).residueFieldMap q)
  exact specResidueFieldMap_isIso_of_idealResidueFieldMap f q
    ((ConcreteCategory.isIso_iff_bijective _).2
      (bijective_residueFieldMap_of_comp_eq f.hom pI q.asIdeal hfI L.hom hker hLm))

end AlgebraicGeometry

end
