module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# The vanishing of `H⁻¹(NL_{B/A})` does not depend on the universe of the sections

Let `a : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site `(C, J)`, with
sections in a universe `w` which need not contain the universes of the objects and morphisms of
the site, and let `↑a : ↑A ⟶ ↑B` be its universe lift to sections in `max w u v`
(`AlgebraicGeometry.SheafOfModules.sheafULift`).  This file proves that the degree `-1`
cohomology sheaf of the naive cotangent complex `NL_{B/A}` of Stacks 08TW vanishes exactly when
that of `NL_{↑B/↑A}` does.

## Main results

* `Stacks.Sites.Conormal.isLocallyInjective_conormalToTensor_iff_of_transport`: the local
  injectivity of the conormal map `I(U)/I(U)² → (A(U)/I(U)) ⊗ Ω[A(U)/R(U)]` of a presentation of
  presheaves of rings is invariant under ring isomorphisms of the presentation data, in
  arbitrary universes.
* `Stacks.Sites.Conormal.mono_conormalSequence_f_iff`: the conormal map of sheaves is a
  monomorphism exactly when the conormal map of presheaves is locally injective.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafULiftComparison` and its invertibility: the free
  algebra sheaf `↑A[↑B]` is the lift of `A[B]`.
* `Stacks.SheafOfModules.isZero_homology_negOne_naiveCotangentComplex_iff_sheafULift`: the
  vanishing of `H⁻¹(NL_{B/A})` is the vanishing of `H⁻¹(NL_{↑B/↑A})`.

## Implementation notes

`H⁻¹(NL_{B/A})` is the kernel of the conormal map of sheaves, so it vanishes exactly when that
map is a monomorphism; the conormal map of sheaves is the sheafification of a map of presheaves
of modules, and it is a monomorphism exactly when that map of presheaves is locally injective.
The presheaf maps of `a` and of `↑a` are compared sectionwise along the ring isomorphisms
`P(U) ≅ ↑A[↑B](U)` given by the comparison of free algebra sheaves, which commute with the
structure maps, so local injectivity passes from one to the other.

## References

* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w w₁ w₂ z z'

namespace Stacks.Sites.Conormal

section RingTransport

variable {R P R' P' : Type*} [CommRing R] [CommRing P] [CommRing R'] [CommRing P']
  (σ : R →+* P) (σ' : R' →+* P') (eR : R →+* R') (eP : P →+* P')
  (h : eP.comp σ = σ'.comp eR)

/-- The map `Ω[P⁄R] → Ω[P'⁄R']` induced by a commutative square of ring maps
`eP ∘ σ = σ' ∘ eR`, with the two rows in arbitrary universes, semilinear over `eP`. -/
noncomputable def kaehlerTransport :
    (letI := σ.toAlgebra; Ω[P⁄R]) →ₛₗ[eP] (letI := σ'.toAlgebra; Ω[P'⁄R']) :=
  letI := σ.toAlgebra
  letI := σ'.toAlgebra
  letI := eR.toAlgebra
  letI := eP.toAlgebra
  letI : Algebra R P' := (eP.comp σ).toAlgebra
  haveI : IsScalarTower R P P' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' P' := IsScalarTower.of_algebraMap_eq' h
  { toFun := fun x ↦ KaehlerDifferential.map R R' P P' x
    map_add' := map_add _
    map_smul' := fun s x ↦ by
      rw [LinearMap.map_smul]
      exact algebraMap_smul P' s _ }

/-- `kaehlerTransport` sends the differential `d x` to `d (eP x)`. -/
theorem kaehlerTransport_D (x : P) :
    letI := σ.toAlgebra
    letI := σ'.toAlgebra
    kaehlerTransport σ σ' eR eP h (KaehlerDifferential.D R P x) =
      KaehlerDifferential.D R' P' (eP x) := by
  let := σ.toAlgebra
  let := σ'.toAlgebra
  let := eR.toAlgebra
  let := eP.toAlgebra
  let : Algebra R P' := (eP.comp σ).toAlgebra
  have : IsScalarTower R P P' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R' P' := IsScalarTower.of_algebraMap_eq' h
  exact KaehlerDifferential.map_D R R' P P' x

end RingTransport

section PresheafTransport

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R P B : Cᵒᵖ ⥤ CommRingCat.{w₁}} (σ : R ⟶ P) (φ : P ⟶ B)
  {R' P' B' : Cᵒᵖ ⥤ CommRingCat.{w₂}} (σ' : R' ⟶ P') (φ' : P' ⟶ B')
  (eR : ∀ X, R.obj X ≃+* R'.obj X) (eP : ∀ X, P.obj X ≃+* P'.obj X)
  (eB : ∀ X, B.obj X ≃+* B'.obj X)
  (hσ : ∀ X, (eP X).toRingHom.comp (σ.app X).hom = (σ'.app X).hom.comp (eR X).toRingHom)
  (hφ : ∀ X, (eB X).toRingHom.comp (φ.app X).hom = (φ'.app X).hom.comp (eP X).toRingHom)
  (hP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
    (eP Y).toRingHom.comp (P.map f).hom = (P'.map f).hom.comp (eP X).toRingHom)

/-- If `eB (φ x) = φ' (eP x)` for a ring isomorphism `eB`, then `φ x = 0` iff `φ' (eP x) = 0`. -/
private lemma app_eq_zero_iff_of_transport (X : Cᵒᵖ) (x : P.obj X)
    (h : eB X (φ.app X x) = φ'.app X (eP X x)) : φ.app X x = 0 ↔ φ'.app X (eP X x) = 0 :=
  h ▸ (map_eq_zero_iff _ (eB X).injective).symm

include hφ in
/-- A commutative square of presentations carries the kernel of `φ` into the kernel of `φ'`. -/
lemma kernelIdeal_le_comap_transport (X : Cᵒᵖ) :
    kernelIdeal φ X ≤ (kernelIdeal φ' X).comap (eP X).toRingHom :=
  fun _ hx ↦ (app_eq_zero_iff_of_transport φ φ' eP eB X _ (RingHom.congr_fun (hφ X) _)).1 hx

/-- The transport of conormal modules `I/I² → I'/I'²` along the ring isomorphisms `eP`. -/
noncomputable def conormalTransport (X : Cᵒᵖ) :
    (kernelIdeal φ X).Cotangent →+ (kernelIdeal φ' X).Cotangent :=
  (cotangentMap _ _ (eP X).toRingHom
    (kernelIdeal_le_comap_transport φ φ' eP eB hφ X)).toAddMonoidHom

/-- `conormalTransport` sends the class of `x ∈ I` in `I/I²` to the class of `eP x` in `I'/I'²`. -/
@[simp]
lemma conormalTransport_toCotangent (X : Cᵒᵖ) (x : kernelIdeal φ X) :
    conormalTransport φ φ' eP eB hφ X ((kernelIdeal φ X).toCotangent x) =
      (kernelIdeal φ' X).toCotangent
        ⟨eP X x, kernelIdeal_le_comap_transport φ φ' eP eB hφ X x.2⟩ := rfl

include hP in
/-- `conormalTransport` commutes with the restriction maps of the conormal presheaves. -/
lemma conormalTransport_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (conormalPresheaf φ).obj X) :
    conormalTransport φ φ' eP eB hφ Y ((conormalPresheaf φ).map f x) =
      (conormalPresheaf φ').map f (conormalTransport φ φ' eP eB hφ X x) := by
  obtain ⟨x, rfl⟩ := (kernelIdeal φ X).toCotangent_surjective x
  change (kernelIdeal φ' Y).toCotangent ⟨eP Y (P.map f x), _⟩ =
    (kernelIdeal φ' Y).toCotangent ⟨P'.map f (eP X x), _⟩
  congr 1
  ext
  exact RingHom.congr_fun (hP f) (x : P.obj X)

/-- The induced ring map on the quotients `P/I → P'/I'`, semilinear over `eP`. -/
noncomputable def quotientTransportₛₗ (X : Cᵒᵖ) :
    (P.obj X ⧸ kernelIdeal φ X) →ₛₗ[(eP X).toRingHom] (P'.obj X ⧸ kernelIdeal φ' X) where
  toFun := Ideal.quotientMap _ (eP X).toRingHom (kernelIdeal_le_comap_transport φ φ' eP eB hφ X)
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (eP X (r * x)) = Ideal.Quotient.mk _ (eP X r * eP X x)
    rw [map_mul]

/-- The transport of the tensor terms `(P/I) ⊗[P] Ω[P/R] → (P'/I') ⊗[P'] Ω[P'/R']`. -/
noncomputable def tensorTransport (X : Cᵒᵖ) :
    (P.obj X ⧸ kernelIdeal φ X) ⊗[P.obj X] ((differentialsPresheaf σ).obj X) →+
      (P'.obj X ⧸ kernelIdeal φ' X) ⊗[P'.obj X] ((differentialsPresheaf σ').obj X) :=
  (TensorProduct.map (quotientTransportₛₗ φ φ' eP eB hφ X)
    (kaehlerTransport (σ.app X).hom (σ'.app X).hom (eR X).toRingHom (eP X).toRingHom
      (hσ X))).toAddMonoidHom

include hσ in
/-- The transports of conormal modules and of tensor terms commute with the conormal maps. -/
lemma tensorTransport_conormalToTensorApp (X : Cᵒᵖ) (x : (conormalPresheaf φ).obj X) :
    tensorTransport σ φ σ' φ' eR eP eB hσ hφ X (conormalToTensorApp φ σ X x) =
      conormalToTensorApp φ' σ' X (conormalTransport φ φ' eP eB hφ X x) := by
  obtain ⟨x, rfl⟩ := (kernelIdeal φ X).toCotangent_surjective x
  rw [conormalToTensorApp_toCotangent, conormalTransport_toCotangent,
    conormalToTensorApp_toCotangent]
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  congr 1
  · exact map_one (Ideal.quotientMap _ (eP X).toRingHom
      (kernelIdeal_le_comap_transport φ φ' eP eB hφ X))
  · exact kaehlerTransport_D (σ.app X).hom (σ'.app X).hom (eR X).toRingHom (eP X).toRingHom
      (hσ X) (x : P.obj X)

include hφ in
/-- The inverse ring isomorphism `(eP X).symm` carries the kernel of `φ'` into the kernel of
`φ`. -/
lemma kernelIdeal_le_comap_transport_symm (X : Cᵒᵖ) :
    kernelIdeal φ' X ≤ (kernelIdeal φ X).comap (eP X).symm.toRingHom := by
  intro x hx
  refine (app_eq_zero_iff_of_transport φ φ' eP eB X ((eP X).symm x)
    (RingHom.congr_fun (hφ X) _)).2 ?_
  rw [RingEquiv.apply_symm_apply]
  exact hx

include hφ in
/-- The transport of conormal modules `I/I² → I'/I'²` is injective. -/
lemma conormalTransport_injective (X : Cᵒᵖ) :
    Function.Injective (conormalTransport φ φ' eP eB hφ X) := by
  let g := cotangentMap _ _ (eP X).symm.toRingHom
    (kernelIdeal_le_comap_transport_symm φ φ' eP eB hφ X)
  have hg : ∀ x, g (conormalTransport φ φ' eP eB hφ X x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := (kernelIdeal φ X).toCotangent_surjective x
    change (kernelIdeal φ X).toCotangent ⟨(eP X).symm (eP X x), _⟩ = _
    congr 1
    ext
    exact (eP X).symm_apply_apply _
  exact Function.LeftInverse.injective hg

include hσ hφ hP in
/-- The elementwise form of `isLocallyInjective_conormalToTensor_of_transport`. -/
lemma equalizerSieve_mem_of_transport
    (h : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ' σ')))
    {X : Cᵒᵖ} (x y : (conormalPresheaf φ).obj X)
    (hxy : conormalToTensorApp φ σ X x = conormalToTensorApp φ σ X y) :
    Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf _).obj (conormalPresheaf φ))
      x y ∈ J X.unop := by
  have h' : conormalToTensorApp φ' σ' X (conormalTransport φ φ' eP eB hφ X x) =
      conormalToTensorApp φ' σ' X (conormalTransport φ φ' eP eB hφ X y) := by
    rw [← tensorTransport_conormalToTensorApp σ φ σ' φ' eR eP eB hσ hφ,
      ← tensorTransport_conormalToTensorApp σ φ σ' φ' eR eP eB hσ hφ, hxy]
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
    ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ' σ'))
    (conormalTransport φ φ' eP eB hφ X x) (conormalTransport φ φ' eP eB hφ X y) h')
  intro Z g hg
  change (conormalPresheaf φ').map g.op (conormalTransport φ φ' eP eB hφ X x) =
    (conormalPresheaf φ').map g.op (conormalTransport φ φ' eP eB hφ X y) at hg
  change (conormalPresheaf φ).map g.op x = (conormalPresheaf φ).map g.op y
  apply conormalTransport_injective φ φ' eP eB hφ (op Z)
  rwa [conormalTransport_naturality φ φ' eP eB hφ hP, conormalTransport_naturality φ φ' eP eB hφ hP]

include hσ hφ hP in
/-- **Local injectivity of the conormal map is transported along ring isomorphisms.** If the
conormal map of `(φ', σ')` is locally injective, so is that of `(φ, σ)`, for ring isomorphisms
`eR`, `eP`, `eB` between the two triples of presheaves of rings, compatible with the structure
maps and natural in the object for `eP`. The two triples may have their sections in different
universes. -/
theorem isLocallyInjective_conormalToTensor_of_transport
    (h : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ' σ'))) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ σ)) where
  equalizerSieve_mem {_X} x y hxy :=
    equalizerSieve_mem_of_transport J σ φ σ' φ' eR eP eB hσ hφ hP h x y hxy

end PresheafTransport

/-- A square of ring homomorphisms commuting along ring isomorphisms also commutes along their
inverses. -/
lemma symm_comp_eq_comp_symm_of_comp_eq {A B A' B' : Type*} [Semiring A] [Semiring B]
    [Semiring A'] [Semiring B'] (e₁ : A ≃+* A') (e₂ : B ≃+* B') (f : A →+* B) (f' : A' →+* B')
    (h : e₂.toRingHom.comp f = f'.comp e₁.toRingHom) :
    e₂.symm.toRingHom.comp f' = f.comp e₁.symm.toRingHom := by
  ext r
  apply e₂.injective
  simpa using (RingHom.congr_fun h (e₁.symm r)).symm

section PresheafTransportIff

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R P B : Cᵒᵖ ⥤ CommRingCat.{w₁}} (σ : R ⟶ P) (φ : P ⟶ B)
  {R' P' B' : Cᵒᵖ ⥤ CommRingCat.{w₂}} (σ' : R' ⟶ P') (φ' : P' ⟶ B')
  (eR : ∀ X, R.obj X ≃+* R'.obj X) (eP : ∀ X, P.obj X ≃+* P'.obj X)
  (eB : ∀ X, B.obj X ≃+* B'.obj X)
  (hσ : ∀ X, (eP X).toRingHom.comp (σ.app X).hom = (σ'.app X).hom.comp (eR X).toRingHom)
  (hφ : ∀ X, (eB X).toRingHom.comp (φ.app X).hom = (φ'.app X).hom.comp (eP X).toRingHom)
  (hP : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
    (eP Y).toRingHom.comp (P.map f).hom = (P'.map f).hom.comp (eP X).toRingHom)

include hσ hφ hP in
/-- **Local injectivity of the conormal map is invariant under ring isomorphisms** of the
presentation data, with the two triples of presheaves of rings in arbitrary universes. -/
theorem isLocallyInjective_conormalToTensor_iff_of_transport :
    Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ σ)) ↔
      Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ' σ')) :=
  ⟨isLocallyInjective_conormalToTensor_of_transport J σ' φ' σ φ
    (fun X ↦ (eR X).symm) (fun X ↦ (eP X).symm) (fun X ↦ (eB X).symm)
    (fun X ↦ symm_comp_eq_comp_symm_of_comp_eq _ _ _ _ (hσ X))
    (fun X ↦ symm_comp_eq_comp_symm_of_comp_eq _ _ _ _ (hφ X))
    (fun f ↦ symm_comp_eq_comp_symm_of_comp_eq _ _ _ _ (hP f)),
    isLocallyInjective_conormalToTensor_of_transport J σ φ σ' φ' eR eP eB hσ hφ hP⟩

end PresheafTransportIff

section Sheafified

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Raising the universe of the values of a morphism of presheaves of modules does not change
its local injectivity. -/
theorem isLocallyInjective_liftModules_map_iff {S : Cᵒᵖ ⥤ RingCat.{w₁}}
    {M N : PresheafOfModules.{w₁} S} (g : M ⟶ N) :
    Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf _).map ((liftModules.{v, u, w₁, w₂} S).map g)) ↔
      Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map g) := by
  refine ⟨fun h ↦ ⟨fun {X} x y hxy ↦ ?_⟩, fun h ↦ ⟨fun {X} x y hxy ↦ ?_⟩⟩
  · have hxy' : ((liftModules.{v, u, w₁, w₂} S).map g).app X (ULift.up x) =
        ((liftModules.{v, u, w₁, w₂} S).map g).app X (ULift.up y) :=
      congrArg ULift.up hxy
    exact J.superset_covering (fun Z f hf ↦ congrArg ULift.down hf)
      (Presheaf.equalizerSieve_mem J
        ((PresheafOfModules.toPresheaf _).map ((liftModules.{v, u, w₁, w₂} S).map g))
        (ULift.up x) (ULift.up y) hxy')
  · have hxy' : g.app X x.down = g.app X y.down := congrArg ULift.down hxy
    exact J.superset_covering (fun Z f hf ↦ congrArg ULift.up hf)
      (Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map g) x.down y.down hxy')

variable [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  (R A B : Sheaf J CommRingCat.{w₁}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]
  [HasWeakSheafify J AddCommGrpCat.{max w₁ u v w₂}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w₁ u v w₂}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})] in
/-- **The conormal map of sheaves is a monomorphism exactly when the conormal map of
presheaves `I(U)/I(U)² → (A(U)/I(U)) ⊗ Ω[A(U)/R(U)]` is locally injective.** The conormal map
of sheaves is the sheafification of the presheaf one, and sheafification of presheaves of
abelian groups detects local injectivity. -/
theorem mono_conormalSequence_f_iff :
    Mono (conormalSequence.{v, u, w₁, w₂} J R A B a φ).f ↔
      Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf _).map (conormalToTensor φ.hom a.hom)) := by
  rw [← isLocallyInjective_liftModules_map_iff.{v, u, w₁, w₂} J,
    ← Presheaf.isLocallyInjective_presheafToSheaf_map_iff,
    Sheaf.isLocallyInjective_iff_injective]
  refine ⟨fun hm X ↦ ?_, fun hinj ↦ ?_⟩
  · have : Mono (conormalSequence.{v, u, w₁, w₂} J R A B a φ).f.val :=
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf B)).map_mono
        (conormalSequence.{v, u, w₁, w₂} J R A B a φ).f
    change Function.Injective ((conormalSequence.{v, u, w₁, w₂} J R A B a φ).f.val.app X)
    exact PresheafOfModules.injective_of_mono _ X
  · exact (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf B)).mono_of_mono_map
      (PresheafOfModules.mono_of_injective hinj)

end Sheafified

end Stacks.Sites.Conormal


namespace Stacks.Sites.FreeAlgebra

open AlgebraicGeometry.SheafOfModules (sheafULift commRingCatULift)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Raising the universe of the sections of a morphism of presheaves of commutative rings
preserves local injectivity. -/
theorem isLocallyInjective_whiskerRight_commRingCatULift {P Q : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : P ⟶ Q) [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective J (Functor.whiskerRight f commRingCatULift.{w, max u v}) where
  equalizerSieve_mem {X} x y h := by
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J f x.down y.down
      (congrArg ULift.down h))
    intro Z g hg
    exact congrArg ULift.up hg

/-- Raising the universe of the sections of a morphism of presheaves of commutative rings
preserves local surjectivity. -/
theorem isLocallySurjective_whiskerRight_commRingCatULift {P Q : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f commRingCatULift.{w, max u v}) where
  imageSieve_mem {X} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f s.down)
    rintro Z g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- The ring isomorphism `↑R[↑σ] ≃ R[σ]` between a polynomial ring with lifted coefficients and
lifted variables and the polynomial ring it lifts. -/
noncomputable def mvPolynomialULiftEquiv (σ : Type w) (R : Type w) [CommRing R] :
    MvPolynomial (ULift.{max u v} σ) (ULift.{max u v} R) ≃+* MvPolynomial σ R :=
  (MvPolynomial.renameEquiv (ULift.{max u v} R) Equiv.ulift).toRingEquiv.trans
    (MvPolynomial.mapEquiv σ ULift.ringEquiv)

/-- `mvPolynomialULiftEquiv` sends the constant `C r` to `C r.down`. -/
@[simp]
lemma mvPolynomialULiftEquiv_C (σ : Type w) (R : Type w) [CommRing R] (r : ULift.{max u v} R) :
    mvPolynomialULiftEquiv.{v, u, w} σ R (MvPolynomial.C r) = MvPolynomial.C r.down := by
  simp [mvPolynomialULiftEquiv]
  rfl

/-- `mvPolynomialULiftEquiv` sends the variable `X x` to `X x.down`. -/
@[simp]
lemma mvPolynomialULiftEquiv_X (σ : Type w) (R : Type w) [CommRing R] (x : ULift.{max u v} σ) :
    mvPolynomialULiftEquiv.{v, u, w} σ R (MvPolynomial.X x) = MvPolynomial.X x.down := by
  simp [mvPolynomialULiftEquiv]

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [HasWeakSheafify J CommRingCat.{max w u v}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}]
  (A B : Sheaf J CommRingCat.{w})

/-- The variables of the lifted free algebra, `↑B ⟶ ↑(A[B])`, `x ↦ ↑[x↓]`. -/
noncomputable def liftedVariable :
    underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B) ⟶
      underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj
        (freeAlgebraSheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B))) :=
  Functor.whiskerRight (freeAlgebraSheafVariable.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B))
    uliftFunctor.{max u v}

/-- **The comparison `↑A[↑B] ⟶ ↑(A[B])`** of the free algebra sheaf over the lifted rings with the
lift of the free algebra sheaf: the `↑A`-algebra map sending the variable `[x]` to `↑[x↓]`. -/
noncomputable def freeAlgebraSheafULiftComparison :
    freeAlgebraSheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
        (underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B)) ⟶
      (sheafULift.{w, u, v} J).obj
        (freeAlgebraSheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)) :=
  freeAlgebraSheafDesc.{v, u, max w u v} J _ _ _
    ((sheafULift.{w, u, v} J).map
      (freeAlgebraSheafCoefficientMap.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)))
    (liftedVariable J A B)

/-- The polynomial evaluation underlying `freeAlgebraSheafULiftComparison`, on the polynomial
presheaf `U ↦ ↑A(U)[↑B(U)]`. -/
noncomputable abbrev freeAlgebraSheafULiftEvaluation :=
  polynomialEvaluation.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
    ((sheafULift.{w, u, v} J).obj
      (freeAlgebraSheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)))
    (underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B))
    ((sheafULift.{w, u, v} J).map
      (freeAlgebraSheafCoefficientMap.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)))
    (liftedVariable J A B)

/-- The ring map underlying the polynomial evaluation of the comparison over `U`, with its
source and target spelled as a polynomial ring and a universe lift. -/
noncomputable abbrev freeAlgebraSheafULiftEvaluationRingHom (U : Cᵒᵖ) :
    MvPolynomial (ULift.{max u v} (ToType (B.obj.obj U)))
        (ULift.{max u v} (ToType (A.obj.obj U))) →+*
      ULift.{max u v} (ToType ((freeAlgebraSheaf.{v, u, w} J A
        (underlyingPresheaf.{v, u, w} J B)).obj.obj U)) :=
  MvPolynomial.eval₂Hom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((freeAlgebraSheafCoefficientMap.{v, u, w} J A
        (underlyingPresheaf.{v, u, w} J B)).hom.app U).hom.comp ULift.ringEquiv.toRingHom))
    (fun x ↦ ULift.up ((freeAlgebraSheafVariable.{v, u, w} J A
      (underlyingPresheaf.{v, u, w} J B)).app U x.down))

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- Over `U`, the ring map of `freeAlgebraSheafULiftEvaluation` is
`freeAlgebraSheafULiftEvaluationRingHom`. -/
lemma freeAlgebraSheafULiftEvaluation_app_hom (U : Cᵒᵖ) :
    ((freeAlgebraSheafULiftEvaluation J A B).app U).hom =
      freeAlgebraSheafULiftEvaluationRingHom J A B U := rfl

/-- The sheafification unit of `U ↦ A(U)[B(U)]` over `U`, with its source spelled as a
polynomial ring. -/
noncomputable def polynomialToFreeAlgebraRingHom (U : Cᵒᵖ) :
    MvPolynomial (ToType (B.obj.obj U)) (ToType (A.obj.obj U)) →+*
      ToType ((freeAlgebraSheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)).obj.obj U) :=
  ((toSheafify J (polynomialPresheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B))).app U).hom

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- The coefficient map of `A[B]` over `U` sends `r` to the image of the constant `C r` under
the sheafification unit. -/
lemma freeAlgebraSheafCoefficientMap_app_eq_polynomialToFreeAlgebraRingHom_C (U : Cᵒᵖ)
    (r : ToType (A.obj.obj U)) :
    (freeAlgebraSheafCoefficientMap.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)).hom.app U r =
      polynomialToFreeAlgebraRingHom J A B U (MvPolynomial.C r) := rfl

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- The variable map of `A[B]` over `U` sends `x` to the image of the variable `X x` under the
sheafification unit. -/
lemma freeAlgebraSheafVariable_app_apply (U : Cᵒᵖ) (x : ToType (B.obj.obj U)) :
    (freeAlgebraSheafVariable.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)).app U x =
      polynomialToFreeAlgebraRingHom J A B U (MvPolynomial.X x) := rfl

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- On sections, the polynomial evaluation underlying the comparison is the lift of the
sheafification unit of `U ↦ A(U)[B(U)]`, read through `↑A(U)[↑B(U)] ≃ A(U)[B(U)]`. -/
lemma freeAlgebraSheafULiftEvaluationRingHom_apply_down (U : Cᵒᵖ)
    (p : MvPolynomial (ULift.{max u v} (ToType (B.obj.obj U)))
      (ULift.{max u v} (ToType (A.obj.obj U)))) :
    (freeAlgebraSheafULiftEvaluationRingHom J A B U p).down =
      polynomialToFreeAlgebraRingHom J A B U (mvPolynomialULiftEquiv.{v, u, w} _ _ p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.eval₂Hom_C, mvPolynomialULiftEquiv_C]
    exact freeAlgebraSheafCoefficientMap_app_eq_polynomialToFreeAlgebraRingHom_C J A B U r.down
  | add p q hp hq =>
    rw [map_add, ULift.add_down, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    rw [map_mul, ULift.mul_down, hp, map_mul, map_mul, MvPolynomial.eval₂Hom_X',
      mvPolynomialULiftEquiv_X]
    exact congrArg _ (freeAlgebraSheafVariable_app_apply J A B U x.down)

/-- The restriction maps of `U ↦ ↑A(U)[↑B(U)]`, with their source and target spelled as
polynomial rings. -/
noncomputable def liftedPolynomialRestrictRingHom {U V : Cᵒᵖ} (f : U ⟶ V) :
    MvPolynomial (ULift.{max u v} (ToType (B.obj.obj U))) (ULift.{max u v} (ToType (A.obj.obj U)))
      →+* MvPolynomial (ULift.{max u v} (ToType (B.obj.obj V)))
        (ULift.{max u v} (ToType (A.obj.obj V))) :=
  ((polynomialPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
    (underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B))).map f).hom

/-- The restriction maps of `U ↦ A(U)[B(U)]`, with their source and target spelled as
polynomial rings. -/
noncomputable def polynomialRestrictRingHom {U V : Cᵒᵖ} (f : U ⟶ V) :
    MvPolynomial (ToType (B.obj.obj U)) (ToType (A.obj.obj U)) →+*
      MvPolynomial (ToType (B.obj.obj V)) (ToType (A.obj.obj V)) :=
  ((polynomialPresheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)).map f).hom

omit [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [HasWeakSheafify J CommRingCat.{max w u v}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- `liftedPolynomialRestrictRingHom` is the polynomial map applying the restriction maps of
`↑A` to the coefficients and of `↑B` to the variables. -/
lemma liftedPolynomialRestrictRingHom_eq {U V : Cᵒᵖ} (f : U ⟶ V) :
    liftedPolynomialRestrictRingHom J A B f =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp
        (ULift.ringEquiv.symm.toRingHom.comp ((A.obj.map f).hom.comp ULift.ringEquiv.toRingHom)))
        (fun e ↦ MvPolynomial.X (ULift.up ((B.obj.map f) e.down))) := rfl

omit [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [HasWeakSheafify J CommRingCat.{max w u v}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- `polynomialRestrictRingHom` is the polynomial map applying the restriction maps of `A` to
the coefficients and of `B` to the variables. -/
lemma polynomialRestrictRingHom_eq {U V : Cᵒᵖ} (f : U ⟶ V) :
    polynomialRestrictRingHom J A B f =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map f).hom)
        (fun e ↦ MvPolynomial.X ((B.obj.map f) e)) := rfl

omit [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [HasWeakSheafify J CommRingCat.{max w u v}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- The identification `↑A(U)[↑B(U)] ≃ A(U)[B(U)]` commutes with the restriction maps. -/
lemma mvPolynomialULiftEquiv_restrict {U V : Cᵒᵖ} (f : U ⟶ V)
    (p : MvPolynomial (ULift.{max u v} (ToType (B.obj.obj U)))
      (ULift.{max u v} (ToType (A.obj.obj U)))) :
    mvPolynomialULiftEquiv.{v, u, w} _ _ (liftedPolynomialRestrictRingHom J A B f p) =
      polynomialRestrictRingHom J A B f (mvPolynomialULiftEquiv.{v, u, w} _ _ p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [liftedPolynomialRestrictRingHom_eq, polynomialRestrictRingHom_eq, MvPolynomial.eval₂Hom_C,
      mvPolynomialULiftEquiv_C, MvPolynomial.eval₂Hom_C]
    simp only [RingHom.comp_apply, mvPolynomialULiftEquiv_C]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    rw [map_mul, map_mul, hp, map_mul, map_mul, liftedPolynomialRestrictRingHom_eq,
      polynomialRestrictRingHom_eq, MvPolynomial.eval₂Hom_X', mvPolynomialULiftEquiv_X,
      mvPolynomialULiftEquiv_X, MvPolynomial.eval₂Hom_X']

omit [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- Two polynomials in `↑A(U)[↑B(U)]` with the same image under the evaluation of the comparison
agree locally. -/
lemma equalizerSieve_freeAlgebraSheafULiftEvaluation_mem {U : Cᵒᵖ}
    (x y : MvPolynomial (ULift.{max u v} (ToType (B.obj.obj U)))
      (ULift.{max u v} (ToType (A.obj.obj U))))
    (hxy : freeAlgebraSheafULiftEvaluationRingHom J A B U x =
      freeAlgebraSheafULiftEvaluationRingHom J A B U y) :
    Presheaf.equalizerSieve (F := polynomialPresheaf.{v, u, max w u v} J
      ((sheafULift.{w, u, v} J).obj A)
      (underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B))) x y ∈
      J U.unop := by
  have h₀ : polynomialToFreeAlgebraRingHom J A B U (mvPolynomialULiftEquiv.{v, u, w} _ _ x) =
      polynomialToFreeAlgebraRingHom J A B U (mvPolynomialULiftEquiv.{v, u, w} _ _ y) := by
    rw [← freeAlgebraSheafULiftEvaluationRingHom_apply_down,
      ← freeAlgebraSheafULiftEvaluationRingHom_apply_down]
    exact congrArg ULift.down hxy
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
    (toSheafify J (polynomialPresheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)))
    (mvPolynomialULiftEquiv.{v, u, w} _ _ x) (mvPolynomialULiftEquiv.{v, u, w} _ _ y) h₀)
  intro Z g hg
  change polynomialRestrictRingHom J A B g.op (mvPolynomialULiftEquiv.{v, u, w} _ _ x) =
    polynomialRestrictRingHom J A B g.op (mvPolynomialULiftEquiv.{v, u, w} _ _ y) at hg
  change liftedPolynomialRestrictRingHom J A B g.op x = liftedPolynomialRestrictRingHom J A B g.op y
  apply (mvPolynomialULiftEquiv.{v, u, w} _ _).injective
  rwa [mvPolynomialULiftEquiv_restrict, mvPolynomialULiftEquiv_restrict]

/-- The polynomial evaluation underlying the comparison is locally injective. -/
instance isLocallyInjective_freeAlgebraSheafULiftEvaluation :
    Presheaf.IsLocallyInjective J (freeAlgebraSheafULiftEvaluation J A B) where
  equalizerSieve_mem {_U} x y hxy :=
    equalizerSieve_freeAlgebraSheafULiftEvaluation_mem J A B x y hxy

omit [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- Every section of `↑(A[B])` over `U` is locally in the image of the evaluation of the
comparison. -/
lemma imageSieve_freeAlgebraSheafULiftEvaluation_mem {U : Cᵒᵖ}
    (s : ULift.{max u v} (ToType ((freeAlgebraSheaf.{v, u, w} J A
      (underlyingPresheaf.{v, u, w} J B)).obj.obj U))) :
    Presheaf.imageSieve (freeAlgebraSheafULiftEvaluation J A B) s ∈ J U.unop := by
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J
    (toSheafify J (polynomialPresheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B))) s.down)
  rintro Z g ⟨q, hq⟩
  refine ⟨(mvPolynomialULiftEquiv.{v, u, w} _ _).symm q, ?_⟩
  apply ULift.ext
  refine (freeAlgebraSheafULiftEvaluationRingHom_apply_down J A B (op Z) _).trans ?_
  exact (congrArg (polynomialToFreeAlgebraRingHom J A B (op Z))
    (RingEquiv.apply_symm_apply (mvPolynomialULiftEquiv.{v, u, w} _ _) q)).trans hq

/-- The polynomial evaluation underlying the comparison is locally surjective. -/
instance isLocallySurjective_freeAlgebraSheafULiftEvaluation :
    Presheaf.IsLocallySurjective J (freeAlgebraSheafULiftEvaluation J A B) where
  imageSieve_mem {_U} s := imageSieve_freeAlgebraSheafULiftEvaluation_mem J A B s

/-- The comparison `↑A[↑B] ⟶ ↑(A[B])` of free algebra sheaves is an isomorphism. -/
instance isIso_freeAlgebraSheafULiftComparison :
    IsIso (freeAlgebraSheafULiftComparison J A B) := by
  have hθ : J.W (freeAlgebraSheafULiftEvaluation J A B) := J.W_of_isLocallyBijective _
  have hfac := freeAlgebraSheafDesc_spec.{v, u, max w u v} J _ _ _
    ((sheafULift.{w, u, v} J).map
      (freeAlgebraSheafCoefficientMap.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)))
    (liftedVariable J A B)
  rw [← J.W_sheafToPresheaf_map_iff_isIso]
  exact MorphismProperty.of_precomp _ _ _ (J.W_toSheafify _) (hfac ▸ hθ)

omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- The comparison of free algebra sheaves respects the coefficient maps from `↑A`. -/
lemma freeAlgebraSheafCoefficientMap_comp_freeAlgebraSheafULiftComparison :
    freeAlgebraSheafCoefficientMap.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
        (underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B)) ≫
      freeAlgebraSheafULiftComparison J A B =
    (sheafULift.{w, u, v} J).map
      (freeAlgebraSheafCoefficientMap.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)) :=
  freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (a : A ⟶ B)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}] in
/-- The comparison of free algebra sheaves carries the lift of the canonical presentation
`A[B] ⟶ B` to the canonical presentation `↑A[↑B] ⟶ ↑B`. -/
lemma freeAlgebraSheafULiftComparison_comp_canonicalPresentation :
    freeAlgebraSheafULiftComparison J A B ≫
        (sheafULift.{w, u, v} J).map (canonicalPresentation.{v, u, w} J A B a) =
      canonicalPresentation.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
        ((sheafULift.{w, u, v} J).obj B) ((sheafULift.{w, u, v} J).map a) := by
  apply freeAlgebraSheaf_hom_ext
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraSheafULiftComparison,
      ← Functor.map_comp, canonicalPresentation_comp_coefficientMap,
      canonicalPresentation_comp_coefficientMap]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc]
    change (freeAlgebraSheafVariable _ _ _ ≫ Functor.whiskerRight ((sheafToPresheaf _ _).map
      (freeAlgebraSheafULiftComparison J A B)) (forget _)) ≫ _ = _
    rw [freeAlgebraSheafULiftComparison, freeAlgebraSheafVariable_comp_desc,
      canonicalPresentation_eq_desc.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
        ((sheafULift.{w, u, v} J).obj B) ((sheafULift.{w, u, v} J).map a),
      freeAlgebraSheafVariable_comp_desc]
    ext U x
    exact congrArg ULift.up (congrFun (congrArg (fun t ↦ (t.app U : _ → _))
      (freeAlgebraSheafVariable_comp_desc.{v, u, w} J A B (underlyingPresheaf.{v, u, w} J B) a
        (𝟙 _))) x.down)

end Stacks.Sites.FreeAlgebra


namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (sheafULift)
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section MonoCriterion

variable [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `H⁻¹(NL_{B/A})` vanishes exactly when the conormal map `I/I² ⟶ B ⊗[A[B]] Ω[A[B]/A]` of the
canonical presentation is a monomorphism: it is the kernel of that map. -/
theorem isZero_homology_negOne_naiveCotangentComplex_iff_mono
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    IsZero ((naiveCotangentComplex.{v, u, w, z} J A B a).homology (-1)) ↔
      Mono (canonicalConormalSequence.{v, u, w, z} J A B a).f := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  have e : (naiveCotangentComplex.{v, u, w, z} J A B a).homology (-1) ≅
      kernel (canonicalConormalSequence.{v, u, w, z} J A B a).f := by
    change (HomologicalComplex.double (canonicalConormalSequence.{v, u, w, z} J A B a).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).homology (-1) ≅ _
    exact HomologicalComplex.doubleHomologyIsoKernel _ _ (by decide)
  exact ⟨fun h ↦ Preadditive.mono_of_isZero_kernel _ (h.of_iso e.symm),
    fun h ↦ (isZero_kernel_of_mono _).of_iso e⟩

end MonoCriterion

section ULift

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J CommRingCat.{max w u v}] [J.WEqualsLocallyBijective CommRingCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  [HasSheafify J AddCommGrpCat.{max w u v z'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z'}]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- The sectionwise ring isomorphism `A[B](U) ≅ ↑A[↑B](U)`: the universe lift followed by the
inverse of the comparison of free algebra sheaves. -/
noncomputable def freeAlgebraSheafULiftRingEquiv (X : Cᵒᵖ) :
    ToType ((freeAlgebraSheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)).obj.obj X) ≃+*
      ToType ((freeAlgebraSheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj A)
        (underlyingPresheaf.{v, u, max w u v} J ((sheafULift.{w, u, v} J).obj B))).obj.obj X) :=
  (ULift.ringEquiv.symm : ToType ((freeAlgebraSheaf.{v, u, w} J A
      (underlyingPresheaf.{v, u, w} J B)).obj.obj X) ≃+*
      ToType (((sheafULift.{w, u, v} J).obj (freeAlgebraSheaf.{v, u, w} J A
        (underlyingPresheaf.{v, u, w} J B))).obj.obj X)).trans
    (((sheafToPresheaf J _).mapIso
      (asIso (freeAlgebraSheafULiftComparison J A B))).app X).commRingCatIsoToRingEquiv.symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  [HasSheafify J AddCommGrpCat.{max w u v z'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z'}] in
/-- The comparison of free algebra sheaves sends `freeAlgebraSheafULiftRingEquiv J A B X p` to
the lift `ULift.up p`. -/
lemma freeAlgebraSheafULiftComparison_freeAlgebraSheafULiftRingEquiv (X : Cᵒᵖ)
    (p : ToType ((freeAlgebraSheaf.{v, u, w} J A (underlyingPresheaf.{v, u, w} J B)).obj.obj X)) :
    (freeAlgebraSheafULiftComparison J A B).hom.app X (freeAlgebraSheafULiftRingEquiv J A B X p) =
      ULift.up p :=
  (((sheafToPresheaf J _).mapIso
    (asIso (freeAlgebraSheafULiftComparison J A B))).app
      X).commRingCatIsoToRingEquiv.apply_symm_apply _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})] in
include a in
/-- **The vanishing of `H⁻¹(NL_{B/A})` is the vanishing of `H⁻¹(NL_{↑B/↑A})`**, for the universe
lift `↑a : ↑A ⟶ ↑B` of a homomorphism of sheaves of commutative rings to sections in a universe
containing the universes of the site. -/
theorem isZero_homology_negOne_naiveCotangentComplex_iff_sheafULift :
    IsZero ((naiveCotangentComplex.{v, u, w, z} J A B a).homology (-1)) ↔
      IsZero ((naiveCotangentComplex.{v, u, max w u v, z'} J ((sheafULift.{w, u, v} J).obj A)
        ((sheafULift.{w, u, v} J).obj B) ((sheafULift.{w, u, v} J).map a)).homology (-1)) := by
  rw [isZero_homology_negOne_naiveCotangentComplex_iff_mono,
    isZero_homology_negOne_naiveCotangentComplex_iff_mono]
  refine (mono_conormalSequence_f_iff.{v, u, w, z} J A _ B _ _).trans
    (Iff.trans ?_ (mono_conormalSequence_f_iff.{v, u, max w u v, z'} J _ _ _ _ _).symm)
  have hc := freeAlgebraSheafCoefficientMap_comp_freeAlgebraSheafULiftComparison J A B
  have hp := freeAlgebraSheafULiftComparison_comp_canonicalPresentation J A B a
  have key : ∀ X p y, (freeAlgebraSheafULiftComparison J A B).hom.app X y = ULift.up p →
      freeAlgebraSheafULiftRingEquiv J A B X p = y := fun X p y h ↦
    (((sheafToPresheaf J _).mapIso (asIso (freeAlgebraSheafULiftComparison J A B))).app
      X).commRingCatIsoToRingEquiv.injective
        ((freeAlgebraSheafULiftComparison_freeAlgebraSheafULiftRingEquiv J A B X p).trans h.symm)
  refine isLocallyInjective_conormalToTensor_iff_of_transport J _ _ _ _
    (fun X ↦ (ULift.ringEquiv.symm : ToType (A.obj.obj X) ≃+*
      ToType (((sheafULift.{w, u, v} J).obj A).obj.obj X)))
    (freeAlgebraSheafULiftRingEquiv J A B)
    (fun X ↦ (ULift.ringEquiv.symm : ToType (B.obj.obj X) ≃+*
      ToType (((sheafULift.{w, u, v} J).obj B).obj.obj X))) ?_ ?_ ?_
  · intro X
    ext r
    have hcX := congr_arg (fun t ↦ ((sheafToPresheaf J CommRingCat.{max w u v}).map t).app X) hc
    exact key _ _ _ (ConcreteCategory.congr_hom hcX (ULift.up r))
  · intro X
    ext p
    have hpX := congr_arg (fun t ↦ ((sheafToPresheaf J CommRingCat.{max w u v}).map t).app X) hp
    refine Eq.trans ?_ (ConcreteCategory.congr_hom hpX (freeAlgebraSheafULiftRingEquiv J A B X p))
    exact (congrArg
      (((sheafULift.{w, u, v} J).map (canonicalPresentation.{v, u, w} J A B a)).hom.app X)
      (freeAlgebraSheafULiftComparison_freeAlgebraSheafULiftRingEquiv J A B X p)).symm
  · intro X Y f
    ext p
    exact key _ _ _ ((NatTrans.naturality_apply (freeAlgebraSheafULiftComparison J A B).hom f
      (freeAlgebraSheafULiftRingEquiv J A B X p)).trans (congrArg
        (((sheafULift.{w, u, v} J).obj (freeAlgebraSheaf.{v, u, w} J A
          (underlyingPresheaf.{v, u, w} J B))).obj.map f)
        (freeAlgebraSheafULiftComparison_freeAlgebraSheafULiftRingEquiv J A B X p)))

end ULift

end Stacks.SheafOfModules
