module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat

/-!
# Localizing a sheaf of rings at a global section

Let `O` be a sheaf of commutative rings on a site and let `h` be a global section of `O`. The
canonical map from `O` to the sheaf associated to the presheaf `U ↦ O(U)[1/h|_U]` is flat and is
an epimorphism of sheaves of rings.

## Main results

* `AlgebraicGeometry.SheafOfModules.localizationMap_isFlat` — the localization map is flat.
* `AlgebraicGeometry.SheafOfModules.localizationMap_epi` — it is an epimorphism.

## Implementation notes

The localization presheaf is presented by a presheaf `P` together with its objectwise
localization map `a`, and an associated sheaf is presented, independently of any choice of
sheafification, by a locally bijective map `b : P ⟶ Oh.obj`; the hypothesis `hf` records that
the canonical map `O ⟶ Oh` factors as `a ≫ b`.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace AlgebraicGeometry.SheafOfModules

private def evalIntPolynomial {A : Type w} [CommRing A] (x : A) :
    Polynomial (ULift.{w} ℤ) →+* A :=
  Polynomial.eval₂RingHom
    ((Int.castRingHom A).comp (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).toRingHom) x

private lemma evalIntPolynomial_comp {A B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (x : A) :
    f.comp (evalIntPolynomial x) = evalIntPolynomial (f x) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [evalIntPolynomial]
  · simp [evalIntPolynomial]

/-- A localization map away from an element is flat and an epimorphism of commutative rings. -/
private lemma flat_and_ringHom_ext_of_away {R S : Type w} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : R) (h : letI := φ.toAlgebra; IsLocalization.Away x S) :
    (letI := φ.toAlgebra; Module.Flat R S) ∧
      ∀ {T : Type w} [CommRing T] (g₁ g₂ : S →+* T), g₁.comp φ = g₂.comp φ → g₁ = g₂ := by
  let := φ.toAlgebra
  exact ⟨IsLocalization.flat S (Submonoid.powers x),
    fun g₁ g₂ hg => IsLocalization.ringHom_ext (Submonoid.powers x) hg⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sections of a sheaf of commutative rings, read through the forgetful composite that
`Presheaf.globalSections` uses, carry the commutative ring structure of the sections
themselves. -/
private instance commRing_comp_forget_obj (O : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ) :
    CommRing ((O.obj ⋙ forget CommRingCat.{w}).obj U) :=
  inferInstanceAs (CommRing (O.obj.obj U))

private lemma localizationMap_isFlat_and_epi
    (O : Sheaf J CommRingCat.{w})
    (h : Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{w}))
    (P : Cᵒᵖ ⥤ CommRingCat.{w}) (a : O.obj ⟶ P)
    (hP : ∀ U, letI : Algebra (O.obj.obj U) (P.obj U) := (a.app U).hom.toAlgebra
      IsLocalization.Away
        (show O.obj.obj U from (Presheaf.globalSectionsEquivSections _ h).1 U) (P.obj U))
    (Oh : Sheaf J CommRingCat.{w}) (b : P ⟶ Oh.obj)
    [Presheaf.IsLocallyInjective J b] [Presheaf.IsLocallySurjective J b]
    (f : O ⟶ Oh) (hf : f.hom = a ≫ b) :
    IsFlatMap f ∧ Epi f := by
  let bAdd := Functor.whiskerRight b
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  have hbS : Presheaf.IsLocallySurjective J bAdd := by
    constructor
    intro U x
    change Presheaf.imageSieve b x ∈ J U
    exact Presheaf.imageSieve_mem J b x
  constructor
  · let α : ringPresheaf O.obj ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj := 𝟙 _
    let M : PresheafOfModules (ringPresheaf O.obj) :=
      PresheafOfModules.restrictScalars
        (Functor.whiskerRight a (forget₂ CommRingCat RingCat)) |>.obj
        (PresheafOfModules.unit (ringPresheaf P))
    have hM : PresheafOfModules.IsFlat M := by
      apply PresheafOfModules.isFlat_of_objectwise_flat M
      intro U
      exact (flat_and_ringHom_ext_of_away _ _ (hP U)).1
    let : Presheaf.IsLocallyInjective J α :=
      Presheaf.isLocallyInjective_of_injective J α fun _ => Function.injective_id
    let : Presheaf.IsLocallySurjective J α :=
      Presheaf.isLocallySurjective_of_surjective J α fun _ x => ⟨x, rfl⟩
    have hMs := Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J α M hM
    let fR : Stacks.SheafOfModules.Tensor.ringSheaf O ⟶ Stacks.SheafOfModules.Tensor.ringSheaf Oh :=
      (sheafCompose J (forget₂ CommRingCat RingCat)).map f
    let G : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
      (SheafOfModules.restrictScalars fR).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Oh))
    let Gpre := (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj G
    have hbI : Presheaf.IsLocallyInjective J bAdd := by
      constructor
      intro U x y hxy
      apply Presheaf.equalizerSieve_mem J b x y
      change (b.app U).hom x = (b.app U).hom y
      exact hxy
    let gm : M ⟶ (PresheafOfModules.restrictScalars α).obj Gpre :=
      PresheafOfModules.homMk bAdd (by
        intro U r m
        let : Module (P.obj U) (M.obj U) := by
          change Module (P.obj U) (P.obj U)
          infer_instance
        dsimp [M]
        let mP : P.obj U := m
        change (b.app U).hom ((a.app U).hom r * mP) =
          (f.hom.app U).hom r * (b.app U).hom mP
        have hfU : (f.hom.app U).hom = (b.app U).hom.comp (a.app U).hom :=
          congrArg CommRingCat.Hom.hom (congrArg (fun k => k.app U) hf)
        rw [hfU, RingHom.comp_apply, map_mul])
    let q : (PresheafOfModules.sheafification α).obj M ⟶ G :=
      (PresheafOfModules.sheafificationHomEquiv α).symm gm
    have hgm : (PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map gm = bAdd := by
      ext U x
      rfl
    let η := CategoryTheory.toSheafify J M.presheaf
    let qpre :=
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map q.val
    have hfac : (PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map gm =
        η ≫ qpre := by
      have heq : (PresheafOfModules.sheafificationHomEquiv α) q = gm :=
        (PresheafOfModules.sheafificationHomEquiv α).apply_symm_apply gm
      rw [← heq]
      exact PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def α q
    let : Presheaf.IsLocallyInjective J (η ≫ qpre) := by
      rw [← hfac, hgm]
      exact hbI
    let : Presheaf.IsLocallySurjective J (η ≫ qpre) := by
      rw [← hfac, hgm]
      exact hbS
    let : Presheaf.IsLocallySurjective J η := inferInstance
    let : Presheaf.IsLocallyInjective J η := inferInstance
    have hqI : Presheaf.IsLocallyInjective J qpre :=
      Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J η qpre
    have hqS : Presheaf.IsLocallySurjective J qpre :=
      Presheaf.isLocallySurjective_of_isLocallySurjective J η qpre
    have hqTo :
        IsIso ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map q) := by
      exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hqI, hqS⟩
    have hqIso : IsIso q := by
      apply isIso_of_reflects_iso q
        (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O))
    let Q := (PresheafOfModules.sheafification α).obj M
    change IsFlat Q at hMs
    have eS : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj Q ≅
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G :=
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.mapIso
        (@asIso _ _ _ _ q hqIso)
    change IsFlat G
    exact (exactFunctor _ _).prop_of_iso eS hMs
  · refine ⟨?_⟩
    intro T g₁ g₂ hfg
    have hcomp : (a ≫ b) ≫ g₁.hom = (a ≫ b) ≫ g₂.hom := by
      calc
        (a ≫ b) ≫ g₁.hom = f.hom ≫ g₁.hom := by rw [hf]
        _ = f.hom ≫ g₂.hom := by simpa using congrArg (fun k => k.hom) hfg
        _ = (a ≫ b) ≫ g₂.hom := by rw [hf]
    have hbg (U : Cᵒᵖ) : b.app U ≫ g₁.hom.app U = b.app U ≫ g₂.hom.app U := by
      have hU := congrArg (fun k => k.app U) hcomp
      exact CommRingCat.hom_ext ((flat_and_ringHom_ext_of_away _ _ (hP U)).2 _ _
        (congrArg CommRingCat.Hom.hom hU))
    have hTR : Presheaf.IsSheaf J
        (T.obj ⋙ forget₂ CommRingCat RingCat) :=
      GrothendieckTopology.HasSheafCompose.isSheaf T.obj T.2
    let E : RingCat.{w} := RingCat.of (Polynomial (ULift.{w} ℤ))
    have hTE : Presieve.IsSheaf J
        ((T.obj ⋙ forget₂ CommRingCat RingCat) ⋙ coyoneda.obj (Opposite.op E)) := hTR E
    have hhom : g₁.hom = g₂.hom := by
      apply NatTrans.ext
      funext U
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      let e₁ : E ⟶ (T.obj ⋙ forget₂ CommRingCat RingCat).obj U :=
        RingCat.ofHom (evalIntPolynomial ((g₁.hom.app U).hom x))
      let e₂ : E ⟶ (T.obj ⋙ forget₂ CommRingCat RingCat).obj U :=
        RingCat.ofHom (evalIntPolynomial ((g₂.hom.app U).hom x))
      have he : e₁ = e₂ := by
        apply (hTE (Presheaf.imageSieve bAdd x)
          (Presheaf.imageSieve_mem J bAdd x)).isSeparatedFor.ext
        intro V k hk
        obtain ⟨p, hp⟩ := hk
        have hp' : (b.app (Opposite.op V)).hom p = (Oh.obj.map k.op).hom x := hp
        have hnat₁ : (T.obj.map k.op).hom ((g₁.hom.app U).hom x) =
            (g₁.hom.app (Opposite.op V)).hom ((Oh.obj.map k.op).hom x) := by
          simp
        have hnat₂ : (T.obj.map k.op).hom ((g₂.hom.app U).hom x) =
            (g₂.hom.app (Opposite.op V)).hom ((Oh.obj.map k.op).hom x) := by
          simp
        have hval : (T.obj.map k.op).hom ((g₁.hom.app U).hom x) =
            (T.obj.map k.op).hom ((g₂.hom.app U).hom x) := by
          rw [hnat₁, hnat₂, ← hp']
          exact congrArg (fun φ => φ p) (hbg (Opposite.op V))
        change (RingCat.ofHom (evalIntPolynomial ((g₁.hom.app U).hom x)) ≫
            (T.obj ⋙ forget₂ CommRingCat RingCat).map k.op) =
          (RingCat.ofHom (evalIntPolynomial ((g₂.hom.app U).hom x)) ≫
            (T.obj ⋙ forget₂ CommRingCat RingCat).map k.op)
        apply RingCat.hom_ext
        change (T.obj.map k.op).hom.comp (evalIntPolynomial ((g₁.hom.app U).hom x)) =
          (T.obj.map k.op).hom.comp (evalIntPolynomial ((g₂.hom.app U).hom x))
        rw [evalIntPolynomial_comp, evalIntPolynomial_comp, hval]
      have hx := congrArg (fun e : E ⟶ (T.obj ⋙ forget₂ CommRingCat RingCat).obj U =>
        e (Polynomial.X : Polynomial (ULift.{w} ℤ))) he
      change (Polynomial.X.eval₂
          ((Int.castRingHom (T.obj.obj U)).comp
            (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).toRingHom)
          ((g₁.hom.app U).hom x)) =
        (Polynomial.X.eval₂
          ((Int.castRingHom (T.obj.obj U)).comp
            (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).toRingHom)
          ((g₂.hom.app U).hom x)) at hx
      simpa only [Polynomial.eval₂_X] using hx
    exact Sheaf.hom_ext hhom

/-- The map from a sheaf of commutative rings to its localization at a global section is flat.
Here `P` is the objectwise localization presheaf and `Oh` is any associated sheaf of `P`. -/
public lemma localizationMap_isFlat
    (O : Sheaf J CommRingCat.{w})
    (h : Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{w}))
    (P : Cᵒᵖ ⥤ CommRingCat.{w}) (a : O.obj ⟶ P)
    (hP : ∀ U, letI : Algebra (O.obj.obj U) (P.obj U) := (a.app U).hom.toAlgebra
      IsLocalization.Away
        (show O.obj.obj U from (Presheaf.globalSectionsEquivSections _ h).1 U) (P.obj U))
    (Oh : Sheaf J CommRingCat.{w}) (b : P ⟶ Oh.obj)
    [Presheaf.IsLocallyInjective J b] [Presheaf.IsLocallySurjective J b]
    (f : O ⟶ Oh) (hf : f.hom = a ≫ b) :
    IsFlatMap f :=
  (localizationMap_isFlat_and_epi O h P a hP Oh b f hf).1

/-- The map from a sheaf of commutative rings to its localization at a global section is an
epimorphism. The target may be any sheaf associated to the objectwise localization presheaf. -/
public lemma localizationMap_epi
    (O : Sheaf J CommRingCat.{w})
    (h : Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{w}))
    (P : Cᵒᵖ ⥤ CommRingCat.{w}) (a : O.obj ⟶ P)
    (hP : ∀ U, letI : Algebra (O.obj.obj U) (P.obj U) := (a.app U).hom.toAlgebra
      IsLocalization.Away
        (show O.obj.obj U from (Presheaf.globalSectionsEquivSections _ h).1 U) (P.obj U))
    (Oh : Sheaf J CommRingCat.{w}) (b : P ⟶ Oh.obj)
    [Presheaf.IsLocallyInjective J b] [Presheaf.IsLocallySurjective J b]
    (f : O ⟶ Oh) (hf : f.hom = a ≫ b) : Epi f :=
  (localizationMap_isFlat_and_epi O h P a hP Oh b f hf).2

end AlgebraicGeometry.SheafOfModules
