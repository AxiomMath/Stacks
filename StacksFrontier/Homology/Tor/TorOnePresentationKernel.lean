module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.Homology.Tor.ChangeOfRingsSystem
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTorSmul

/-!
# `Tor_1^R(A, B)` as a kernel, from a polynomial presentation of `B`

Let `R → A` and `R → B` be ring maps and let `P = R[X] → B` be a polynomial presentation with
kernel `I`. The short exact sequence `0 → I → P → B → 0` of `R`-modules has a free middle term,
so the long exact sequence of the left derived functors of `A ⊗_R -` gives

`Tor_1^R(A, B) ≅ Ker(A ⊗_R I → A ⊗_R P)`.

Under this isomorphism, multiplication by `a ∈ A` on `Tor` (functoriality in the first variable)
corresponds to multiplication by `a` on `A ⊗_R I`, and functoriality of `Tor` in the second
variable along multiplication by the image of `p ∈ P` is `A ⊗_R (p · -)` on `A ⊗_R I`.

## Main definitions

* `RingTheory.TorIndependence.presentationShortComplex`: the sequence `0 → I → P → B → 0`.
* `RingTheory.TorIndependence.presentationTorKerMap`: the connecting map
  `L_1(A ⊗_R -)(B) → A ⊗_R I`.
* `RingTheory.TorIndependence.torOnePresentationKerEquiv`:
  `Tor_1^R(A, B) ≃ Ker(A ⊗_R I → A ⊗_R P)`.

## Main results

* `RingTheory.TorIndependence.torOnePresentationKerEquiv_smul` and
  `RingTheory.TorIndependence.torOnePresentationKerEquiv_mul`: the compatibilities of
  `torOnePresentationKerEquiv` with multiplication by `a ∈ A` and by `p ∈ P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace RingTheory.TorIndependence

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {B : Type u} [CommRing B] [Algebra R B] {X T : Type u} (P : Algebra.Presentation R B X T)

/-- The kernel `I` of `P → B`, as an `R`-module. -/
abbrev presentationKer : Submodule R P.Ring := P.ker.restrictScalars R

/-- The short exact sequence `0 → I → P → B → 0` of `R`-modules of a presentation. -/
def presentationShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (presentationKer P).subtype)
    (ModuleCat.ofHom (IsScalarTower.toAlgHom R P.Ring B).toLinearMap)
    (by ext x; exact (RingHom.mem_ker (f := algebraMap P.Ring B)).1 x.2)

/-- The sequence `0 → I → P → B → 0` of a presentation is short exact. -/
theorem presentationShortComplex_shortExact : (presentationShortComplex P).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    exact ⟨⟨y, RingHom.mem_ker.2 hy⟩, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).2 fun a b h => Subtype.ext h
  · exact (ModuleCat.epi_iff_surjective _).2 P.algebraMap_surjective

/-- The polynomial ring `P` of a presentation is a projective `R`-module. -/
instance projective_presentationRing : Projective (ModuleCat.of R P.Ring) :=
  ModuleCat.projective_of_free (MvPolynomial.basisMonomials X R)

variable (R) in
/-- Extension of scalars along `R → A`. -/
abbrev extA : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap R A)

/-- **The connecting map** `L_1(A ⊗_R -)(B) → A ⊗_R I` of `0 → I → P → B → 0`, with the degree
zero left derived functor identified with `A ⊗_R -`. -/
def presentationTorKerMap :
    ((extA R A).leftDerived 1).obj (ModuleCat.of R B) ⟶
      (extA R A).obj (ModuleCat.of R (presentationKer P)) :=
  (extA R A).leftDerivedδ (presentationShortComplex_shortExact P) 0 ≫
    ((extA R A).leftDerivedZeroIsoSelf).hom.app _

/-- The connecting map `L_1(A ⊗_R -)(B) → A ⊗_R I` is injective. -/
theorem presentationTorKerMap_injective :
    Function.Injective (presentationTorKerMap A P).hom := by
  have hz : IsZero (((extA R A).leftDerived (0 + 1)).obj (ModuleCat.of R P.Ring)) :=
    (extA R A).isZero_leftDerived_obj_projective_succ 0 _
  have hex := (extA R A).leftDerived_exact_δ₁ (presentationShortComplex_shortExact P) 0
  have hmono : Mono ((extA R A).leftDerivedδ (presentationShortComplex_shortExact P) 0) :=
    (ShortComplex.mk _ _ ((extA R A).leftDerived_map_g_comp_δ
      (presentationShortComplex_shortExact P) 0)).exact_iff_mono (hz.eq_of_src _ _) |>.1 hex
  rw [← ModuleCat.mono_iff_injective]
  exact @mono_comp _ _ _ _ _ _ hmono _ (IsIso.mono_of_iso
    (((extA R A).leftDerivedZeroIsoSelf).app _).hom)

/-- The range of the connecting map `L_1(A ⊗_R -)(B) → A ⊗_R I` is the kernel of
`A ⊗_R I → A ⊗_R P`. -/
theorem range_presentationTorKerMap :
    LinearMap.range (presentationTorKerMap A P).hom =
      LinearMap.ker ((extA R A).map (presentationShortComplex P).f).hom := by
  have hex := (extA R A).leftDerived_exact_δ₂ (presentationShortComplex_shortExact P) 0
  let e := ((extA R A).leftDerivedZeroIsoSelf)
  have hnat := e.hom.naturality (presentationShortComplex P).f
  let φ : ShortComplex.mk _ _ ((extA R A).leftDerivedδ_comp_map_f
      (presentationShortComplex_shortExact P) 0) ⟶
      ShortComplex.mk (presentationTorKerMap A P) ((extA R A).map (presentationShortComplex P).f)
        ((Category.assoc _ _ _).trans ((whisker_eq _ hnat.symm).trans
          ((Category.assoc _ _ _).symm.trans ((eq_whisker ((extA R A).leftDerivedδ_comp_map_f
            (presentationShortComplex_shortExact P) 0) _).trans zero_comp)))) :=
    { τ₁ := 𝟙 _
      τ₂ := e.hom.app _
      τ₃ := e.hom.app _
      comm₁₂ := Category.id_comp _
      comm₂₃ := hnat.symm }
  have : IsIso φ := by
    have : IsIso φ.τ₁ := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (e.hom.app _))
    have : IsIso φ.τ₃ := inferInstanceAs (IsIso (e.hom.app _))
    exact ShortComplex.isIso_of_isIso φ
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    ((ShortComplex.exact_iff_of_iso (asIso φ)).1 hex)

/-! ### Multiplication by an element of `P` -/

/-- Multiplication by `p ∈ P` on the kernel `I`. -/
def presentationKerMul (p : P.Ring) :
    ModuleCat.of R (presentationKer P) ⟶ ModuleCat.of R (presentationKer P) :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨p * x, P.ker.mul_mem_left p x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add p x y)
      map_smul' := fun r x => Subtype.ext (mul_smul_comm r p (x : P.Ring)) }

/-- Multiplication by `p ∈ P` as an endomorphism of `0 → I → P → B → 0`. -/
def presentationShortComplexMul (p : P.Ring) :
    presentationShortComplex P ⟶ presentationShortComplex P where
  τ₁ := presentationKerMul P p
  τ₂ := ModuleCat.ofHom (TorChangeOfRings.mulLinear R P.Ring p)
  τ₃ := ModuleCat.ofHom (TorChangeOfRings.mulLinear R B (algebraMap P.Ring B p))
  comm₁₂ := by ext x; rfl
  comm₂₃ := by
    ext x
    exact map_mul (algebraMap P.Ring B) p x

/-- **The connecting map is compatible with multiplication by `p ∈ P`.** -/
theorem presentationTorKerMap_mul (p : P.Ring) :
    ((extA R A).leftDerived 1).map (presentationShortComplexMul P p).τ₃ ≫
        presentationTorKerMap A P =
      presentationTorKerMap A P ≫ (extA R A).map (presentationKerMul P p) :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker ((extA R A).leftDerivedδ_naturality
    (presentationShortComplex_shortExact P) (presentationShortComplex_shortExact P)
    (presentationShortComplexMul P p) 0) _).trans ((Category.assoc _ _ _).trans
    ((whisker_eq _ (((extA R A).leftDerivedZeroIsoSelf).hom.naturality
      (presentationShortComplexMul P p).τ₁)).trans (Category.assoc _ _ _).symm)))

/-! ### The identification with `Tor` -/

variable (R B) in
/-- The identification `L_1(A ⊗_R -)(B) ≅ Tor_1^R(A, B)` of `R`-modules. -/
abbrev leftDerivedTorIso :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (((extA R A).leftDerived 1).obj
        (ModuleCat.of R B)) ≅
      ((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).obj (ModuleCat.of R B) :=
  (leftDerivedExtendRestrictIsoTor (R := R) (R' := A) 1).app (ModuleCat.of R B)

/-- The kernel of `A ⊗_R I → A ⊗_R P`. -/
abbrev presentationTensorKer : Submodule A ((extA R A).obj (ModuleCat.of R (presentationKer P))) :=
  LinearMap.ker ((extA R A).map (presentationShortComplex P).f).hom

/-- The connecting map, corestricted to `Ker(A ⊗_R I → A ⊗_R P)`. -/
def presentationTorKerMapCod :
    ((extA R A).leftDerived 1).obj (ModuleCat.of R B) →ₗ[A] presentationTensorKer A P :=
  (presentationTorKerMap A P).hom.codRestrict (presentationTensorKer A P) fun z =>
    (range_presentationTorKerMap A P).le ⟨z, rfl⟩

/-- The corestricted connecting map `L_1(A ⊗_R -)(B) → Ker(A ⊗_R I → A ⊗_R P)` is bijective. -/
theorem presentationTorKerMapCod_bijective : Function.Bijective (presentationTorKerMapCod A P) := by
  refine ⟨fun z z' h => presentationTorKerMap_injective A P (congrArg Subtype.val h), fun k => ?_⟩
  obtain ⟨z, hz⟩ := (range_presentationTorKerMap A P).ge k.2
  exact ⟨z, Subtype.ext hz⟩

/-- **`Tor_1^R(A, B) ≅ Ker(A ⊗_R I → A ⊗_R P)`**, for a polynomial presentation `P → B` with
kernel `I`. -/
def torOnePresentationKerEquiv : TorChangeOfRings.torObj R 1 A B ≃+ presentationTensorKer A P :=
  (leftDerivedTorIso R A B).symm.toLinearEquiv.toAddEquiv.trans
    (LinearEquiv.ofBijective (presentationTorKerMapCod A P)
      (presentationTorKerMapCod_bijective A P)).toAddEquiv

/-- `torOnePresentationKerEquiv` is the connecting map applied after the identification of
`Tor_1^R(A, B)` with `L_1(A ⊗_R -)(B)`. -/
theorem torOnePresentationKerEquiv_apply (y : TorChangeOfRings.torObj R 1 A B) :
    (torOnePresentationKerEquiv A P y).1 =
      (presentationTorKerMap A P).hom ((leftDerivedTorIso R A B).inv.hom y) :=
  rfl

/-- **Functoriality of `Tor` in the first variable along multiplication by `a ∈ A` is
multiplication by `a`.** -/
theorem torOnePresentationKerEquiv_smul (a : A) (y : TorChangeOfRings.torObj R 1 A B) :
    (torOnePresentationKerEquiv A P
        (((Tor (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).app (ModuleCat.of R B) y)).1 =
      a • (torOnePresentationKerEquiv A P y).1 := by
  have h := leftDerivedExtendRestrictIsoTor_smul (R := R) (R' := A) a 1 (ModuleCat.of R B)
  have hx := congrArg (fun φ => (leftDerivedTorIso R A B).inv.hom
    (φ.hom ((leftDerivedTorIso R A B).inv.hom y))) h
  have h' : (leftDerivedTorIso R A B).inv.hom
      ((((Tor (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).app (ModuleCat.of R B)) y) =
        a • (leftDerivedTorIso R A B).inv.hom y := by
    have e1 : (leftDerivedTorIso R A B).hom.hom ((leftDerivedTorIso R A B).inv.hom y) = y :=
      Iso.inv_hom_id_apply _ _
    have e2 := Iso.hom_inv_id_apply (leftDerivedTorIso R A B)
      (((ModuleCat.restrictScalars (algebraMap R A)).map
        (a • 𝟙 (((extA R A).leftDerived 1).obj (ModuleCat.of R B)))).hom
          ((leftDerivedTorIso R A B).inv.hom y))
    refine (Eq.trans ?_ hx.symm).trans (e2.trans rfl)
    show _ = (leftDerivedTorIso R A B).inv.hom
      ((((Tor (ModuleCat.{u} R) 1).map (mulByAlg (R := R) a)).app (ModuleCat.of R B)).hom
        ((leftDerivedTorIso R A B).hom.hom ((leftDerivedTorIso R A B).inv.hom y)))
    rw [e1]
    rfl
  rw [torOnePresentationKerEquiv_apply, torOnePresentationKerEquiv_apply, h']
  exact LinearMap.map_smul (presentationTorKerMap A P).hom a
    ((leftDerivedTorIso R A B).inv.hom y)

/-- **Functoriality of `Tor` in the second variable along multiplication by the image of
`p ∈ P` is multiplication by `p` on `A ⊗_R I`.** -/
theorem torOnePresentationKerEquiv_mul (p : P.Ring) (y : TorChangeOfRings.torObj R 1 A B) :
    (torOnePresentationKerEquiv A P
        ((((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).map
          (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B (algebraMap P.Ring B p)))) y)).1 =
      ((extA R A).map (presentationKerMul P p)).hom (torOnePresentationKerEquiv A P y).1 := by
  have hnat := (leftDerivedExtendRestrictIsoTor (R := R) (R' := A) 1).inv.naturality
    (presentationShortComplexMul P p).τ₃
  have h' : (leftDerivedTorIso R A B).inv.hom
      ((((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).map
          (presentationShortComplexMul P p).τ₃) y) =
        (((extA R A).leftDerived 1).map (presentationShortComplexMul P p).τ₃).hom
          ((leftDerivedTorIso R A B).inv.hom y) :=
    congrArg (fun φ => φ.hom y) hnat
  have hδ := congrArg (fun φ => φ.hom ((leftDerivedTorIso R A B).inv.hom y))
    (presentationTorKerMap_mul A P p)
  rw [torOnePresentationKerEquiv_apply, torOnePresentationKerEquiv_apply]
  exact (congrArg _ h').trans hδ

end RingTheory.TorIndependence
