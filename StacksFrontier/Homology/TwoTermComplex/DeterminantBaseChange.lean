module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
import all StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLineIsBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TwoTermComplex.PresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic

/-!
# The determinant of a two-term perfect complex along a ring map

Let `f : R → S` be a homomorphism of commutative rings, `K` a perfect object of `D(R)` of Tor
amplitude in `[-1, 0]`, `L` one of `D(S)`, and `e : S ⊗ᴸ_R K ≅ L` an isomorphism in `D(S)`. This
file constructs the base change map of determinants `det(K) → det(L)`, semilinear over `f`, and
proves that it exhibits `det(L)` as `S ⊗_R det(K)`, that it is natural in `K` and `L`, and that it
carries the canonical element of a rank-zero `K` to that of `L`.

The map is computed on a two-term finite-projective presentation `P` of `K`: termwise base change
`S ⊗_R P` presents `S ⊗ᴸ_R K`, and the determinant line of `P` base-changes to that of `S ⊗_R P`.
The result does not depend on the presentation, because the base change of determinant lines
intertwines the determinant equivalences of degreewise-surjective quasi-isomorphisms.

## Main definitions

* `TwoTermDeterminant.baseChangeMap`: the map `det(K) → det(L)` attached to `e`.

## Main results

* `TwoTermDeterminant.isBaseChangeAlong_baseChangeMap`: it exhibits `det(L)` as `S ⊗_R det(K)`.
* `TwoTermDeterminant.baseChangeMap_trans` and `TwoTermDeterminant.baseChangeMap_mapIso`:
  naturality in `L` and in `K`.
* `TwoTermDeterminant.baseChangeMap_delta`: the canonical element is preserved.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

attribute [local irreducible] determinantTransport

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-! ### Termwise base change of a module -/

attribute [local instance] TwoTermDeterminant.finite_extendScalars
  TwoTermDeterminant.projective_extendScalars

section Module

variable (M : ModuleCat.{u} R)

/-- The `R`-module structure on an extension of scalars, by restriction along `f`. -/
instance extendScalarsModule : Module R ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
  Module.compHom _ f

/-- The unit `m ↦ 1 ⊗ m` of extension of scalars. -/
def extendScalarsUnit : M →ₗ[R] (ModuleCat.extendScalars.{u, u, u} f).obj M :=
  ((ModuleCat.extendRestrictScalarsAdj f).unit.app M).hom

/-- The unit `extendScalarsUnit f M` sends `m` to `1 ⊗ m`. -/
@[simp]
theorem extendScalarsUnit_apply (m : M) :
    extendScalarsUnit f M m = (1 : S) ⊗ₜ[R, f] m := rfl

/-- The `R`- and `S`-actions on `S ⊗_R M` form a scalar tower, for the algebra structure
`f.toAlgebra`. -/
theorem isScalarTower_extendScalars :
    letI := f.toAlgebra
    IsScalarTower R S ((ModuleCat.extendScalars.{u, u, u} f).obj M) := by
  let := f.toAlgebra
  exact ⟨fun r s x => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

/-- The unit `m ↦ 1 ⊗ m` exhibits `S ⊗_R M` as the base change of `M` along `f`. -/
theorem isBaseChange_extendScalarsUnit :
    letI := f.toAlgebra
    letI := isScalarTower_extendScalars f M
    IsBaseChange S (extendScalarsUnit f M) := by
  let := f.toAlgebra
  let := isScalarTower_extendScalars f M
  let e : (ModuleCat.extendScalars f).obj (ModuleCat.of R M) ≅
      ModuleCat.of S ((ModuleCat.extendScalars.{u, u, u} f).obj M) := Iso.refl _
  exact AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso f rfl e
    (extendScalarsUnit f M) fun _ => rfl

end Module

/-! ### Termwise base change of a presentation -/

section Presentation

/-- Termwise extension of scalars of a complex. -/
def bcComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} S) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- Termwise extension of scalars of a chain map. -/
abbrev bcMap {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (g : P ⟶ P') :
    bcComplex f P ⟶ bcComplex f P' :=
  ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map g

/-- Derived extension of scalars along `f`. -/
abbrev Lext : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (totalDerivedExtensionScalars.{u, u, u} f).functor

/-- The comparison from derived to termwise extension of scalars at a complex. -/
def cmpA (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (Lext f).obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (bcComplex f P) :=
  (totalDerivedExtensionScalars.{u, u, u} f).comparison.app P

/-- The comparison `cmpA` from derived to termwise extension of scalars is natural in the
complex. -/
theorem cmpA_naturality {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (g : P ⟶ P') :
    cmpA f P ≫ DerivedCategory.Q.map (bcMap f g) =
      (Lext f).map (DerivedCategory.Q.map g) ≫ cmpA f P' :=
  ((totalDerivedExtensionScalars.{u, u, u} f).comparison.naturality g).symm

/-- The `R`-module structure on each term of the termwise base change of a complex, by restriction
along `f`. -/
instance bcComplexModule (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module R ((bcComplex f P).X i) :=
  extendScalarsModule f (P.X i)

/-- The unit `m ↦ 1 ⊗ m` in degree `i`. -/
def bcUnit (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) : P.X i →ₗ[R] (bcComplex f P).X i :=
  extendScalarsUnit f (P.X i)

/-- The `R`- and `S`-actions on each term of `bcComplex f P` form a scalar tower. -/
theorem isScalarTower_bc (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    letI := f.toAlgebra
    IsScalarTower R S ((bcComplex f P).X i) :=
  isScalarTower_extendScalars f (P.X i)

/-- In each degree, the unit `bcUnit f P i` exhibits the term of `bcComplex f P` as the base
change of the term of `P`. -/
theorem isBaseChange_bcUnit (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    letI := f.toAlgebra
    letI := isScalarTower_bc f P i
    IsBaseChange S (bcUnit f P i) :=
  isBaseChange_extendScalarsUnit f (P.X i)

variable {K L : DerivedCategory (ModuleCat.{u} R)}

/-- For a two-term finite-projective presentation, the comparison from derived to termwise
extension of scalars is an isomorphism. -/
theorem isIso_cmpA (P : TwoTermPresentation K) : IsIso (cmpA f P.complex) := by
  let := P.strictlyLE
  have : ∀ i, Projective (P.complex.X i) := fun i => by
    let := P.projective i
    exact (IsProjective.iff_projective _).1 inferInstance
  exact (totalDerivedExtensionScalars.{u, u, u} f).comparison_isIso_of_projective P.complex 0

/-- The comparison `S ⊗ᴸ_R P ≅ S ⊗_R P` for a two-term finite-projective presentation. -/
def comparisonIso (P : TwoTermPresentation K) :
    (Lext f).obj (DerivedCategory.Q.obj P.complex) ≅
      DerivedCategory.Q.obj (bcComplex f P.complex) :=
  @asIso _ _ _ _ (cmpA f P.complex) (isIso_cmpA f P)

/-- **Termwise base change of a two-term presentation presents the derived base change.** -/
abbrev TwoTermPresentation.bcPresentation (P : TwoTermPresentation K) :
    TwoTermPresentation ((Lext f).obj K) where
  complex := bcComplex f P.complex
  finite i := by
    let := P.finite i
    exact finite_extendScalars f (P.complex.X i)
  projective i := by
    let := P.projective i
    exact projective_extendScalars f (P.complex.X i)
  strictlyGE := by
    let := P.strictlyGE
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (ModuleCat.extendScalars.{u, u, u} f).map_isZero
      (P.complex.isZero_of_isStrictlyGE (-1) i hi)
  strictlyLE := by
    let := P.strictlyLE
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (ModuleCat.extendScalars.{u, u, u} f).map_isZero
      (P.complex.isZero_of_isStrictlyLE 0 i hi)
  iso := (Lext f).mapIso P.iso ≪≫ comparisonIso f P

/-- A presentation with its comparison isomorphism replaced. -/
abbrev TwoTermPresentation.withIso {T : Type u} [CommRing T]
    {K L : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K)
    (i : L ≅ DerivedCategory.Q.obj P.complex) : TwoTermPresentation L :=
  { P with iso := i }

/-- A presentation transported along an isomorphism of the presented objects. -/
abbrev TwoTermPresentation.ofIso {T : Type u} [CommRing T] {K L : DerivedCategory (ModuleCat.{u} T)}
    (P : TwoTermPresentation K) (e : K ≅ L) : TwoTermPresentation L :=
  P.withIso (e.symm ≪≫ P.iso)

/-- The comparison isomorphism depends on a presentation only through its complex. -/
@[simp]
theorem comparisonIso_withIso {K₂ : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K)
    (i : K₂ ≅ DerivedCategory.Q.obj P.complex) :
    comparisonIso f (P.withIso i) = comparisonIso f P :=
  rfl

/-- The base change of the determinant line of a presentation, `f`-semilinear. -/
def bcLine (P : TwoTermPresentation K) :
    presentationDeterminant P →ₛₗ[f] presentationDeterminant (P.bcPresentation f) :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  letI := (P.bcPresentation f).finite (-1)
  letI := (P.bcPresentation f).projective (-1)
  letI := (P.bcPresentation f).finite 0
  letI := (P.bcPresentation f).projective 0
  letI := f.toAlgebra
  letI := isScalarTower_bc f P.complex (-1)
  letI := isScalarTower_bc f P.complex 0
  let φ := TwoTermComplex.detLineMap (isBaseChange_bcUnit f P.complex (-1))
    (isBaseChange_bcUnit f P.complex 0) (P.complex.d (-1) 0).hom
    ((bcComplex f P.complex).d (-1) 0).hom
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun r x => by
      rw [φ.map_smul]
      exact (algebraMap_smul S r (φ x)).symm }

end Presentation

/-! ### Base change intertwines the determinant equivalences -/

section Transport

variable {K L : DerivedCategory (ModuleCat.{u} R)}

/-- Termwise base change of a quasi-isomorphism between presentations is a quasi-isomorphism. -/
theorem isIso_Q_map_bcMap (P : TwoTermPresentation K) (P' : TwoTermPresentation L)
    (g : P.complex ⟶ P'.complex) [IsIso (DerivedCategory.Q.map g)] :
    IsIso (DerivedCategory.Q.map (bcMap f g)) := by
  have := isIso_cmpA f P
  have := isIso_cmpA f P'
  have h : DerivedCategory.Q.map (bcMap f g) =
      inv (cmpA f P.complex) ≫ (Lext f).map (DerivedCategory.Q.map g) ≫ cmpA f P'.complex := by
    rw [IsIso.eq_inv_comp]
    exact cmpA_naturality f g
  rw [h]
  infer_instance

/-- Termwise base change of a degreewise-surjective map of presentations is degreewise
surjective. -/
theorem isDegreewiseSurjective_bcMap (P : TwoTermPresentation K) (P' : TwoTermPresentation L)
    (g : P.complex ⟶ P'.complex) (hs : (P.hom P' g).IsDegreewiseSurjective) :
    ((P.bcPresentation f).hom (P'.bcPresentation f) (bcMap f g)).IsDegreewiseSurjective := by
  let := f.toAlgebra
  let := isScalarTower_bc f P.complex (-1)
  let := isScalarTower_bc f P.complex 0
  let := isScalarTower_bc f P'.complex (-1)
  let := isScalarTower_bc f P'.complex 0
  exact ⟨IsBaseChange.surjective_of_surjective (σ := bcUnit f P.complex (-1))
      _ (isBaseChange_bcUnit f P'.complex (-1)) (LinearMap.ext fun _ => rfl) hs.1,
    IsBaseChange.surjective_of_surjective (σ := bcUnit f P.complex 0)
      _ (isBaseChange_bcUnit f P'.complex 0) (LinearMap.ext fun _ => rfl) hs.2⟩

/-- Brings into scope the finiteness, projectivity and scalar tower instances for a presentation
and its termwise base change. -/
private theorem of_bcPresentation_instances (P : TwoTermPresentation K) {C : Prop}
    (h : let := P.finite (-1)
      let := P.projective (-1)
      let := P.finite 0
      let := P.projective 0
      let := (P.bcPresentation f).finite (-1)
      let := (P.bcPresentation f).projective (-1)
      let := (P.bcPresentation f).finite 0
      let := (P.bcPresentation f).projective 0
      let := f.toAlgebra
      let := isScalarTower_bc f P.complex (-1)
      let := isScalarTower_bc f P.complex 0
      C) : C := h

/-- **Base change intertwines the determinant equivalences of a degreewise-surjective
quasi-isomorphism of presentations.** -/
private theorem surjectiveDeterminantEquiv_bcLine (P : TwoTermPresentation K)
    (P' : TwoTermPresentation L) (g : P.complex ⟶ P'.complex)
    (hs : (P.hom P' g).IsDegreewiseSurjective) (hq : (P.hom P' g).IsQuasiIso)
    (hsB : ((P.bcPresentation f).hom (P'.bcPresentation f) (bcMap f g)).IsDegreewiseSurjective)
    (hqB : ((P.bcPresentation f).hom (P'.bcPresentation f) (bcMap f g)).IsQuasiIso)
    (x : presentationDeterminant P) :
    surjectiveDeterminantEquiv (P.bcPresentation f) (P'.bcPresentation f) (bcMap f g) hsB hqB
        (bcLine f P x) = bcLine f P' (surjectiveDeterminantEquiv P P' g hs hq x) := by
  refine of_bcPresentation_instances f P ?_
  intros
  refine of_bcPresentation_instances f P' ?_
  intros
  exact TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_isBaseChange
    (P.complex.d (-1) 0).hom (P'.complex.d (-1) 0).hom
    ((bcComplex f P.complex).d (-1) 0).hom ((bcComplex f P'.complex).d (-1) 0).hom
    (isBaseChange_bcUnit f P.complex (-1)) (isBaseChange_bcUnit f P.complex 0)
    (isBaseChange_bcUnit f P'.complex (-1)) (isBaseChange_bcUnit f P'.complex 0)
    (LinearMap.ext fun _ => rfl) (P.hom P' g)
    ((P.bcPresentation f).hom (P'.bcPresentation f) (bcMap f g))
    (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl) hs hq hsB hqB x

/-- The derived base change of an isomorphism between the classes of two complexes, read as an
isomorphism between the classes of their termwise base changes. -/
def bcIso {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsIso (cmpA f P)) (hP' : IsIso (cmpA f P'))
    (c : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    DerivedCategory.Q.obj (bcComplex f P) ≅ DerivedCategory.Q.obj (bcComplex f P') :=
  (@asIso _ _ _ _ _ hP).symm ≪≫ (Lext f).mapIso c ≪≫ @asIso _ _ _ _ _ hP'

/-- If `Q(l) ≫ c = Q(r)`, then the termwise base changes satisfy
`Q(bcMap f l) ≫ bcIso f hP hP' c = Q(bcMap f r)`. -/
theorem bcIso_comm {M P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hM : IsIso (cmpA f M)) (hP : IsIso (cmpA f P)) (hP' : IsIso (cmpA f P'))
    (c : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') (l : M ⟶ P) (r : M ⟶ P')
    (hc : DerivedCategory.Q.map l ≫ c.hom = DerivedCategory.Q.map r) :
    DerivedCategory.Q.map (bcMap f l) ≫ (bcIso f hP hP' c).hom =
      DerivedCategory.Q.map (bcMap f r) := by
  rw [← cancel_epi (cmpA f M)]
  simp only [bcIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Functor.mapIso_hom]
  rw [reassoc_of% (cmpA_naturality f l), IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc, hc,
    cmpA_naturality f r]

/-- **Base change intertwines the transport of determinant lines along an isomorphism of
presentations.** -/
theorem determinantTransport_bcLine (P : TwoTermPresentation K) (P' : TwoTermPresentation L)
    (c : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex)
    (x : presentationDeterminant P) :
    determinantTransport (P.bcPresentation f) (P'.bcPresentation f)
        (bcIso f (isIso_cmpA f P) (isIso_cmpA f P') c) (bcLine f P x) =
      bcLine f P' (determinantTransport P P' c x) := by
  obtain ⟨s⟩ := nonempty_surjectiveSpan P P' c
  have := s.left_isIso
  have := s.right_isIso
  have hl := isIso_Q_map_bcMap f s.middle P s.left
  have hr := isIso_Q_map_bcMap f s.middle P' s.right
  let sB : SurjectiveSpan (P.bcPresentation f) (P'.bcPresentation f)
      (bcIso f (isIso_cmpA f P) (isIso_cmpA f P') c) :=
    { middle := s.middle.bcPresentation f
      left := bcMap f s.left
      right := bcMap f s.right
      left_surjective := isDegreewiseSurjective_bcMap f _ _ _ s.left_surjective
      right_surjective := isDegreewiseSurjective_bcMap f _ _ _ s.right_surjective
      left_isIso := hl
      right_isIso := hr
      comm := bcIso_comm f (isIso_cmpA f s.middle) _ _ c s.left s.right s.comm }
  have : IsIso (DerivedCategory.Q.map sB.left) := hl
  have : IsIso (DerivedCategory.Q.map sB.right) := hr
  rw [determinantTransport_eq_span sB, determinantTransport_eq_span s]
  change (isoSurjectiveDeterminant sB.middle (P'.bcPresentation f) sB.right sB.right_surjective)
      ((isoSurjectiveDeterminant sB.middle (P.bcPresentation f) sB.left sB.left_surjective).symm
        (bcLine f P x)) =
    bcLine f P' ((isoSurjectiveDeterminant s.middle P' s.right s.right_surjective)
      ((isoSurjectiveDeterminant s.middle P s.left s.left_surjective).symm x))
  set y := (isoSurjectiveDeterminant s.middle P s.left s.left_surjective).symm x with hy
  have hx : x = isoSurjectiveDeterminant s.middle P s.left s.left_surjective y := by
    rw [hy, LinearEquiv.apply_symm_apply]
  have h1 :
      (isoSurjectiveDeterminant sB.middle (P.bcPresentation f) sB.left sB.left_surjective).symm
        (bcLine f P x) = bcLine f s.middle y := by
    rw [LinearEquiv.symm_apply_eq, hx]
    exact (surjectiveDeterminantEquiv_bcLine f s.middle P s.left _ _ _ _ y).symm
  rw [h1]
  exact surjectiveDeterminantEquiv_bcLine f s.middle P' s.right _ _ _ _ y

end Transport

/-! ### Semilinear base changes -/

section AlongBaseChange

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- An `f`-semilinear map `φ : M → N` *exhibits `N` as `S ⊗_R M`*: every `f`-semilinear map out
of `M` into an `S`-module factors uniquely through an `S`-linear map out of `N`. -/
def IsBaseChangeAlong (φ : M →ₛₗ[f] N) : Prop :=
  ∀ (N' : Type u) [AddCommGroup N'] [Module S N'] (g : M →ₛₗ[f] N'),
    ∃! h : N →ₗ[S] N', h.comp φ = g

variable {f}

/-- An `S`-linear equivalence after a base change is a base change. -/
theorem IsBaseChangeAlong.comp_linearEquiv {N₂ : Type u} [AddCommGroup N₂] [Module S N₂]
    {φ : M →ₛₗ[f] N} (h : IsBaseChangeAlong f φ) (e : N ≃ₗ[S] N₂) :
    IsBaseChangeAlong f (e.toLinearMap.comp φ) := by
  intro N' _ _ g
  obtain ⟨k, hk, hu⟩ := h N' g
  refine ⟨k.comp e.symm.toLinearMap, ?_, fun k' hk' => ?_⟩
  · rw [← hk]
    ext x
    simp
  · have := hu (k'.comp e.toLinearMap) (by rw [← hk']; ext; simp)
    rw [← this]
    ext x
    simp

/-- A base change after an `R`-linear equivalence is a base change. -/
theorem IsBaseChangeAlong.comp_linearEquiv_right {M₀ : Type u} [AddCommGroup M₀] [Module R M₀]
    {φ : M →ₛₗ[f] N} (h : IsBaseChangeAlong f φ) (e : M₀ ≃ₗ[R] M) :
    IsBaseChangeAlong f (φ.comp e.toLinearMap) := by
  intro N' _ _ g
  obtain ⟨k, hk, hu⟩ := h N' (g.comp e.symm.toLinearMap)
  refine ⟨k, ?_, fun k' hk' => hu k' ?_⟩
  · ext x
    have := LinearMap.congr_fun hk (e x)
    simpa using this
  · rw [← hk']
    ext x
    simp

/-- A base change in the sense of `IsBaseChange`, read through an algebra structure inducing
`f`. -/
theorem isBaseChangeAlong_of_isBaseChange [Algebra R S] (hf : ∀ r, algebraMap R S r = f r)
    [Module R N] [IsScalarTower R S N] (φ : M →ₛₗ[f] N) (φ' : M →ₗ[R] N) (hφ' : ∀ x, φ' x = φ x)
    (hb : IsBaseChange S φ') : IsBaseChangeAlong f φ := by
  intro N' _ _ g
  let : Module R N' := Module.compHom N' f
  have : IsScalarTower R S N' := ⟨fun r s x => by
    rw [Algebra.smul_def, mul_smul, hf]
    rfl⟩
  let g' : M →ₗ[R] N' := { toFun := g, map_add' := g.map_add, map_smul' := g.map_smulₛₗ }
  refine ⟨hb.lift g', ?_, fun k hk => ?_⟩
  · ext x
    rw [LinearMap.comp_apply, ← hφ']
    exact hb.lift_eq g' x
  · refine hb.algHom_ext _ _ fun x => ?_
    rw [hb.lift_eq g', hφ']
    exact LinearMap.congr_fun hk x

end AlongBaseChange

/-! ### The base change map of determinants -/

section Map

variable {K K' : PerfectTwoTermComplex R} {L L' : PerfectTwoTermComplex S}

/-- Determinant transport depends on its presentations only through their complexes. -/
private theorem determinantTransport_withIso_withIso {T : Type u} [CommRing T]
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (P' : TwoTermPresentation L₁) (i : K₂ ≅ DerivedCategory.Q.obj P.complex)
    (j : L₂ ≅ DerivedCategory.Q.obj P'.complex)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex) :
    determinantTransport (P.withIso i) (P'.withIso j) a = determinantTransport P P' a := by
  obtain ⟨s⟩ := nonempty_surjectiveSpan P P' a
  have := s.left_isIso
  have := s.right_isIso
  let s' : SurjectiveSpan (P.withIso i) (P'.withIso j) a :=
    { middle := s.middle.withIso (i ≪≫ P.iso.symm ≪≫ s.middle.iso)
      left := s.left
      right := s.right
      left_surjective := s.left_surjective
      right_surjective := s.right_surjective
      left_isIso := s.left_isIso
      right_isIso := s.right_isIso
      comm := s.comm }
  have : IsIso (DerivedCategory.Q.map s'.left) := s.left_isIso
  have : IsIso (DerivedCategory.Q.map s'.right) := s.right_isIso
  rw [determinantTransport_eq_span s', determinantTransport_eq_span s]
  rfl

/-- Determinant transport depends on its source presentation only through its complex. -/
theorem determinantTransport_withIso_left {T : Type u} [CommRing T]
    {K₁ K₂ L₁ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (P' : TwoTermPresentation L₁) (i : K₂ ≅ DerivedCategory.Q.obj P.complex)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex) :
    determinantTransport (P.withIso i) P' a = determinantTransport P P' a :=
  determinantTransport_withIso_withIso P P' i P'.iso a

/-- Determinant transport depends on its target presentation only through its complex. -/
theorem determinantTransport_withIso_right {T : Type u} [CommRing T]
    {K₁ L₁ L₂ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (P' : TwoTermPresentation L₁) (i : L₂ ≅ DerivedCategory.Q.obj P'.complex)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex) :
    determinantTransport P (P'.withIso i) a = determinantTransport P P' a :=
  determinantTransport_withIso_withIso P P' P.iso i a

/-- Determinant transport is unchanged by transporting both presentations along isomorphisms of
the presented objects. -/
theorem determinantTransport_ofIso {T : Type u} [CommRing T]
    {K₁ K₂ L₁ L₂ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (P' : TwoTermPresentation L₁) (e : K₁ ≅ K₂) (e' : L₁ ≅ L₂)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex) :
    determinantTransport (P.ofIso e) (P'.ofIso e') a = determinantTransport P P' a := by
  rw [determinantTransport_withIso_left, determinantTransport_withIso_right]

/-- Determinant transport is unchanged by transporting the source presentation along an
isomorphism of the presented objects. -/
theorem determinantTransport_ofIso_left' {T : Type u} [CommRing T]
    {K₁ K₂ L₁ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (P' : TwoTermPresentation L₁) (e : K₁ ≅ K₂)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex) :
    determinantTransport (P.ofIso e) P' a = determinantTransport P P' a :=
  determinantTransport_withIso_left P P' _ a

/-- Determinant transport is unchanged by transporting the target presentation along an
isomorphism of the presented objects. -/
theorem determinantTransport_ofIso_right' {T : Type u} [CommRing T]
    {K₁ L₁ L₂ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (P' : TwoTermPresentation L₁) (e' : L₁ ≅ L₂)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj P'.complex) :
    determinantTransport P (P'.ofIso e') a = determinantTransport P P' a :=
  determinantTransport_withIso_right P P' _ a

/-- The base change of `P.withIso i` is the base change of `P` with comparison isomorphism
`(Lext f).mapIso i ≪≫ comparisonIso f P`. -/
theorem baseChange_withIso {K K₂ : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K)
    (i : K₂ ≅ DerivedCategory.Q.obj P.complex) :
    (P.withIso i).bcPresentation f =
      (P.bcPresentation f).withIso ((Lext f).mapIso i ≪≫ comparisonIso f P) :=
  rfl

/-- Determinant transport into the base change of `P.withIso i` agrees with transport into the
base change of `P`. -/
theorem determinantTransport_baseChange_withIso_right
    {M₁ : DerivedCategory (ModuleCat.{u} S)} {K K₂ : DerivedCategory (ModuleCat.{u} R)}
    (X : TwoTermPresentation M₁) (P : TwoTermPresentation K)
    (i : K₂ ≅ DerivedCategory.Q.obj P.complex)
    (a : DerivedCategory.Q.obj X.complex ≅ DerivedCategory.Q.obj (P.bcPresentation f).complex) :
    determinantTransport X ((P.withIso i).bcPresentation f) a =
      determinantTransport X (P.bcPresentation f) a :=
  determinantTransport_withIso_right X (P.bcPresentation f)
    ((Lext f).mapIso i ≪≫ comparisonIso f P) a

/-- The transport between two presentations with the same complex, along the identity of that
complex, is the identity. -/
theorem determinantTransport_withIso_refl {T : Type u} [CommRing T]
    {K₁ K₂ K₃ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁)
    (i : K₂ ≅ DerivedCategory.Q.obj P.complex) (j : K₃ ≅ DerivedCategory.Q.obj P.complex)
    (y : presentationDeterminant P) :
    determinantTransport (P.withIso i) (P.withIso j) (Iso.refl _) y = y := by
  rw [determinantTransport_withIso_left, determinantTransport_withIso_right,
    determinantTransport_id]
  rfl

/-- The transport from `P.ofIso e` to `P` along the identity of their common complex is the
identity. -/
theorem determinantTransport_ofIso_refl {T : Type u} [CommRing T]
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} T)} (P : TwoTermPresentation K₁) (e : K₁ ≅ K₂)
    (y : presentationDeterminant P) :
    determinantTransport (P.ofIso e) P (Iso.refl _) y = y := by
  rw [determinantTransport_withIso_left, determinantTransport_id]
  rfl

/-- Comparison with two presentations of the same object differs by the transport between them. -/
theorem presentationTransport_detPresentationIso {T : Type u} [CommRing T]
    (M : PerfectTwoTermComplex T) (P P' : TwoTermPresentation M.obj)
    (x : ((det T).obj ⟨M⟩).of.obj) :
    presentationTransport P P' (Iso.refl _) (detPresentationIso M P x) =
      detPresentationIso M P' x := by
  change ((presentationTransport (presentation T M) P (Iso.refl M.obj)).trans
    (presentationTransport P P' (Iso.refl M.obj))) x = _
  rw [presentationTransport_comp]
  rfl

/-- The base change map of determinants computed on a presentation `P` of `K`. -/
def baseChangeMapVia (P : TwoTermPresentation K.obj) (e : (Lext f).obj K.obj ≅ L.obj) :
    ((det R).obj ⟨K⟩).of.obj →ₛₗ[f] ((det S).obj ⟨L⟩).of.obj :=
  ((detPresentationIso L ((P.bcPresentation f).ofIso e)).symm.toLinearMap.comp (bcLine f P)).comp
    (detPresentationIso K P).toLinearMap

/-- The base change of the comparison between two presentations of `K` is the comparison between
their base changes, transported along `e`. -/
theorem bcIso_eq (P : TwoTermPresentation K.obj) (P' : TwoTermPresentation K.obj)
    (e : (Lext f).obj K.obj ≅ L.obj) :
    bcIso f (isIso_cmpA f P) (isIso_cmpA f P') (P.iso.symm ≪≫ Iso.refl _ ≪≫ P'.iso) =
      ((P.bcPresentation f).ofIso e).iso.symm ≪≫ Iso.refl _ ≪≫
        ((P'.bcPresentation f).ofIso e).iso := by
  ext
  simp [bcIso, comparisonIso, TwoTermPresentation.bcPresentation, TwoTermPresentation.ofIso]

/-- `baseChangeMapVia f P e` is `bcLine f P` read through the identifications of `det(K)` and
`det(L)` with the determinant lines of `P` and of its base change. -/
theorem baseChangeMapVia_apply (P : TwoTermPresentation K.obj) (e : (Lext f).obj K.obj ≅ L.obj)
    (x : ((det R).obj ⟨K⟩).of.obj) :
    baseChangeMapVia f P e x =
      (detPresentationIso L ((P.bcPresentation f).ofIso e)).symm
        (bcLine f P (detPresentationIso K P x)) :=
  rfl

/-- **The base change map does not depend on the presentation.** -/
theorem baseChangeMapVia_eq (P P' : TwoTermPresentation K.obj) (e : (Lext f).obj K.obj ≅ L.obj) :
    baseChangeMapVia f P e = baseChangeMapVia f P' e := by
  refine LinearMap.ext fun x => ?_
  rw [baseChangeMapVia_apply, baseChangeMapVia_apply]
  have h1 : detPresentationIso K P' x =
      determinantTransport P P' (P.iso.symm ≪≫ Iso.refl _ ≪≫ P'.iso) (detPresentationIso K P x) :=
    (presentationTransport_detPresentationIso K P P' x).symm
  have h3 := determinantTransport_bcLine f P P' (P.iso.symm ≪≫ Iso.refl _ ≪≫ P'.iso)
    (detPresentationIso K P x)
  have h4 := determinantTransport_ofIso (P.bcPresentation f) (P'.bcPresentation f) e e
    (bcIso f (isIso_cmpA f P) (isIso_cmpA f P') (P.iso.symm ≪≫ Iso.refl _ ≪≫ P'.iso))
  have h5 := bcIso_eq f P P' e
  have h6 := presentationTransport_detPresentationIso L ((P.bcPresentation f).ofIso e)
    ((P'.bcPresentation f).ofIso e)
    ((detPresentationIso L ((P.bcPresentation f).ofIso e)).symm
      (bcLine f P (detPresentationIso K P x)))
  rw [LinearEquiv.apply_symm_apply] at h6
  rw [LinearEquiv.eq_symm_apply]
  refine h6.symm.trans ?_
  change determinantTransport ((P.bcPresentation f).ofIso e) ((P'.bcPresentation f).ofIso e)
    (((P.bcPresentation f).ofIso e).iso.symm ≪≫ Iso.refl _ ≪≫ ((P'.bcPresentation f).ofIso e).iso)
    (bcLine f P (detPresentationIso K P x)) = _
  rw [← h5, h4, h3, h1]

/-- **The base change map of determinants.** For an isomorphism `e : S ⊗ᴸ_R K ≅ L`, the
`f`-semilinear map `det(K) → det(L)`, computed on any two-term finite-projective presentation. -/
def baseChangeMap (K : PerfectTwoTermComplex R) (L : PerfectTwoTermComplex S)
    (e : (Lext f).obj K.obj ≅ L.obj) : ((det R).obj ⟨K⟩).of.obj →ₛₗ[f] ((det S).obj ⟨L⟩).of.obj :=
  baseChangeMapVia f (presentation R K) e

/-- The base change map of determinants may be computed on any presentation of `K`. -/
theorem baseChangeMap_eq (P : TwoTermPresentation K.obj) (e : (Lext f).obj K.obj ≅ L.obj) :
    baseChangeMap f K L e = baseChangeMapVia f P e :=
  baseChangeMapVia_eq f _ P e

end Map

section Naturality

variable {K K' : PerfectTwoTermComplex R} {L L' : PerfectTwoTermComplex S}

/-- The determinant of an isomorphism, computed on arbitrary presentations of source and
target. -/
theorem detPresentationIso_det_map_apply {T : Type u} [CommRing T] {M M' : PerfectTwoTermComplex T}
    (b : (⟨M⟩ : Core (PerfectTwoTermComplex T)) ⟶ ⟨M'⟩) (Q : TwoTermPresentation M.obj)
    (Q' : TwoTermPresentation M'.obj) (y : ((det T).obj ⟨M⟩).of.obj) :
    detPresentationIso M' Q' (((det T).map b).iso.hom y) =
      presentationTransport Q Q' ((perfectTwoTermComplexProperty T).ι.mapIso b.iso)
        (detPresentationIso M Q y) := by
  rw [show ((det T).map b).iso.hom y = presentationTransport (presentation T M) (presentation T M')
    ((perfectTwoTermComplexProperty T).ι.mapIso b.iso) y from det_map_apply (R := T) b y]
  change ((presentationTransport (presentation T M) (presentation T M')
      ((perfectTwoTermComplexProperty T).ι.mapIso b.iso)).trans
    (presentationTransport (presentation T M') Q' (Iso.refl _))) y =
    ((presentationTransport (presentation T M) Q (Iso.refl _)).trans
      (presentationTransport Q Q' ((perfectTwoTermComplexProperty T).ι.mapIso b.iso))) y
  rw [presentationTransport_comp, presentationTransport_comp, Iso.trans_refl, Iso.refl_trans]

/-- **Naturality of the base change map in the target.** -/
theorem baseChangeMap_trans (e : (Lext f).obj K.obj ≅ L.obj)
    (b : (⟨L⟩ : Core (PerfectTwoTermComplex S)) ⟶ ⟨L'⟩) (x : ((det R).obj ⟨K⟩).of.obj) :
    baseChangeMap f K L' (e ≪≫ (perfectTwoTermComplexProperty S).ι.mapIso b.iso) x =
      ((det S).map b).iso.hom (baseChangeMap f K L e x) := by
  set P := presentation R K
  set Q := (P.bcPresentation f).ofIso e
  set Q' := (P.bcPresentation f).ofIso (e ≪≫ (perfectTwoTermComplexProperty S).ι.mapIso b.iso)
  set z := bcLine f P (detPresentationIso K P x)
  rw [baseChangeMap, baseChangeMap, baseChangeMapVia_apply, baseChangeMapVia_apply,
    LinearEquiv.symm_apply_eq, detPresentationIso_det_map_apply b Q Q',
    LinearEquiv.apply_symm_apply]
  have h : Q.iso.symm ≪≫ (perfectTwoTermComplexProperty S).ι.mapIso b.iso ≪≫ Q'.iso =
      Iso.refl _ := by
    ext
    simp [Q, Q']
  change z = determinantTransport Q Q' (Q.iso.symm ≪≫
    (perfectTwoTermComplexProperty S).ι.mapIso b.iso ≪≫ Q'.iso) z
  rw [h, determinantTransport_ofIso, determinantTransport_id]
  rfl

/-- **Naturality of the base change map in the source.** -/
theorem baseChangeMap_mapIso (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨K'⟩)
    (e : (Lext f).obj K'.obj ≅ L.obj) (x : ((det R).obj ⟨K⟩).of.obj) :
    baseChangeMap f K L ((Lext f).mapIso ((perfectTwoTermComplexProperty R).ι.mapIso a.iso) ≪≫ e)
        x = baseChangeMap f K' L e (((det R).map a).iso.hom x) := by
  let ι := (perfectTwoTermComplexProperty R).ι.mapIso a.iso
  let P' := presentation R K'
  let P'' : TwoTermPresentation K.obj := P'.ofIso ι.symm
  rw [baseChangeMap_eq f P'' ((Lext f).mapIso ι ≪≫ e), baseChangeMap_eq f P' e,
    baseChangeMapVia_apply, baseChangeMapVia_apply,
    detPresentationIso_det_map_apply a P'' P']
  have h1 : P''.iso.symm ≪≫ ι ≪≫ P'.iso = Iso.refl _ := by
    ext
    simp [P'']
  have h3 : presentationTransport P'' P' ι (detPresentationIso K P'' x) =
      detPresentationIso K P'' x := by
    change determinantTransport P'' P' (P''.iso.symm ≪≫ ι ≪≫ P'.iso) _ = _
    rw [h1]
    exact determinantTransport_ofIso_refl P' _ _
  rw [h3]
  let Q := (P'.bcPresentation f).ofIso e
  let Q'' := (P''.bcPresentation f).ofIso ((Lext f).mapIso ι ≪≫ e)
  let z := bcLine f P'' (detPresentationIso K P'' x)
  change (detPresentationIso L Q'').symm z = (detPresentationIso L Q).symm z
  rw [LinearEquiv.symm_apply_eq]
  have h4 : Q.iso.symm ≪≫ Iso.refl _ ≪≫ Q''.iso = Iso.refl _ := by
    ext
    simp [Q, Q'', P'', ι]
  have h5 := presentationTransport_detPresentationIso L Q Q'' ((detPresentationIso L Q).symm z)
  rw [LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  change z = determinantTransport Q Q'' (Q.iso.symm ≪≫ Iso.refl _ ≪≫ Q''.iso) z
  rw [h4]
  exact (determinantTransport_withIso_refl (P'.bcPresentation f) Q.iso Q''.iso z).symm

end Naturality

section Delta

variable {K : PerfectTwoTermComplex R} {L : PerfectTwoTermComplex S}

/-- The termwise base change of a rank-zero presentation has rank zero. -/
theorem isRankZero_bcPresentation (P : TwoTermPresentation K.obj) (hP : P.IsRankZero) :
    (P.bcPresentation f).IsRankZero := by
  refine of_bcPresentation_instances f P ?_
  intros
  exact TwoTermComplex.isRankZero_of_isBaseChange (isBaseChange_bcUnit f P.complex (-1))
    (isBaseChange_bcUnit f P.complex 0) _ hP

/-- The base change of determinant lines carries the canonical element of a rank-zero presentation
to that of its base change. -/
theorem bcLine_delta (P : TwoTermPresentation K.obj) (hP : P.IsRankZero) :
    bcLine f P (presentationDelta P hP) =
      presentationDelta (P.bcPresentation f) (isRankZero_bcPresentation f P hP) := by
  refine of_bcPresentation_instances f P ?_
  intros
  exact TwoTermComplex.detLineMap_delta (isBaseChange_bcUnit f P.complex (-1))
    (isBaseChange_bcUnit f P.complex 0) (LinearMap.ext fun _ => rfl) hP

/-- The derived base change of a rank-zero object has rank zero. -/
theorem isRankZero_of_iso (hK : IsRankZero K.obj) (e : (Lext f).obj K.obj ≅ L.obj) :
    IsRankZero L.obj :=
  ⟨(hK.choose.bcPresentation f).ofIso e, isRankZero_bcPresentation f hK.choose hK.choose_spec⟩

/-- **The base change map carries the canonical element to the canonical element.** -/
theorem baseChangeMap_delta (e : (Lext f).obj K.obj ≅ L.obj) (hK : IsRankZero K.obj)
    (hL : IsRankZero L.obj) : baseChangeMap f K L e (delta K hK) = delta L hL := by
  rw [baseChangeMap_eq f hK.choose, baseChangeMapVia_apply]
  have h1 : detPresentationIso K hK.choose (delta K hK) =
      presentationDelta hK.choose hK.choose_spec :=
    detPresentationIso_delta K hK.choose hK.choose_spec
  rw [h1, bcLine_delta, LinearEquiv.symm_apply_eq]
  exact (detPresentationIso_delta L ((hK.choose.bcPresentation f).ofIso e)
    (isRankZero_bcPresentation f hK.choose hK.choose_spec)).symm

end Delta

section IsBaseChange

variable {K : PerfectTwoTermComplex R} {L : PerfectTwoTermComplex S}

/-- The base change of determinant lines exhibits the determinant line of `P.bcPresentation f` as
`S ⊗_R` the determinant line of `P`. -/
theorem isBaseChangeAlong_bcLine (P : TwoTermPresentation K.obj) :
    IsBaseChangeAlong f (bcLine f P) := by
  refine of_bcPresentation_instances f P ?_
  intros
  exact isBaseChangeAlong_of_isBaseChange (fun _ => rfl) (bcLine f P) _ (fun _ => rfl)
    (TwoTermComplex.isBaseChange_detLineMap (isBaseChange_bcUnit f P.complex (-1))
      (isBaseChange_bcUnit f P.complex 0) _ _)

/-- **The base change map exhibits `det(L)` as `S ⊗_R det(K)`.** -/
theorem isBaseChangeAlong_baseChangeMap (e : (Lext f).obj K.obj ≅ L.obj) :
    IsBaseChangeAlong f (baseChangeMap f K L e) :=
  ((isBaseChangeAlong_bcLine f (presentation R K)).comp_linearEquiv _).comp_linearEquiv_right _

end IsBaseChange

end TwoTermDeterminant

end
