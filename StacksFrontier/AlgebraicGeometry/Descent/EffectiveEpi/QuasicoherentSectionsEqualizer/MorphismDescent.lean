module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections

/-!
# Descent of morphisms to affine schemes

If the structure sheaf of an affine scheme satisfies the global-section equalizer condition
for a family of morphisms of affine schemes, then compatible morphisms to an affine scheme
descend, so the family is effective epimorphic. This file also records the invariance of
(universal) effective epimorphic families under isomorphisms, the identification of a
family with the family of spectra of its rings of global sections, and the square-zero
extension `R ⊕ M` together with its base change along a ring map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

open scoped ChangeOfRings TensorProduct

namespace SectionsEqualizer

open Stacks.Ample (unitModule)

-- Once the structure-sheaf sections have been identified with a ring equalizer,
-- compatible morphisms into affine schemes descend by applying that equalizer
-- separately to each element of the target coordinate ring. Uniqueness in the
-- equalizer forces the chosen lifts to preserve zero, one, addition, and
-- multiplication.
private theorem ringHom_descends_of_sectionEqualizer
    {A : Type u} [CommRing A] {I : Type w}
    {C : I → Type u} [∀ i, CommRing (C i)]
    {D : I → I → Type u} [∀ i j, CommRing (D i j)]
    (ρ : ∀ i, A →+* C i) (α : ∀ i j, C i →+* D i j)
    (β : ∀ i j, C j →+* D i j)
    (heq : ∀ x : ∀ i, C i,
      (∀ i j, α i j (x i) = β i j (x j)) →
      ∃! a : A, ∀ i, ρ i a = x i)
    {E : Type u} [CommRing E] (φ : ∀ i, E →+* C i)
    (hφ : ∀ i j x, α i j (φ i x) = β i j (φ j x)) :
    ∃! ψ : E →+* A, ∀ i, (ρ i).comp ψ = φ i := by
  classical
  let lift : E → A := fun x => Classical.choose
    (heq (fun i => φ i x) (fun i j => hφ i j x) |>.exists)
  have hlift (x : E) : ∀ i, ρ i (lift x) = φ i x :=
    Classical.choose_spec (heq (fun i => φ i x) (fun i j => hφ i j x) |>.exists)
  have huniq (x : E) (a : A) (ha : ∀ i, ρ i a = φ i x) : a = lift x :=
    (heq (fun i => φ i x) (fun i j => hφ i j x)).unique ha (hlift x)
  let ψ : E →+* A := {
    toFun := lift
    map_zero' := (huniq 0 0 (by simp)).symm
    map_one' := (huniq 1 1 (by simp)).symm
    map_add' x y := (huniq (x + y) (lift x + lift y) (by simp [hlift])).symm
    map_mul' x y := (huniq (x * y) (lift x * lift y) (by simp [hlift])).symm
  }
  refine ⟨ψ, fun i => ?_, fun ψ' hψ' => ?_⟩
  · ext x
    exact hlift x i
  · ext x
    exact huniq x (ψ' x) fun i => DFunLike.congr_fun (hψ' i) x

private noncomputable def affineHomEquiv (X Y : AffineScheme.{u}) :
    (X ⟶ Y) ≃ (Γ(Y.obj, ⊤) →+* Γ(X.obj, ⊤)) where
  toFun f := f.hom.appTop.hom
  invFun φ := AffineScheme.ofHom
    (X.obj.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ Y.obj.isoSpec.inv)
  left_inv f := by
    apply InducedCategory.Hom.ext
    apply AlgebraicGeometry.ext_of_isAffine
    let : IsAffine X.obj := inferInstance
    let : IsAffine Y.obj := inferInstance
    have hscheme : X.obj.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom f.hom.appTop.hom) ≫ Y.obj.isoSpec.inv = f.hom := by
      have hn := Scheme.isoSpec_hom_naturality f.hom
      have h1 : X.obj.isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom f.hom.appTop.hom) = f.hom ≫ Y.obj.isoSpec.hom := by
        simpa only [CommRingCat.ofHom_hom] using hn
      change (X.obj.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom f.hom.appTop.hom)) ≫ Y.obj.isoSpec.inv = f.hom
      calc
        _ = (f.hom ≫ Y.obj.isoSpec.hom) ≫ Y.obj.isoSpec.inv :=
          congrArg (fun q => q ≫ Y.obj.isoSpec.inv) h1
        _ = f.hom := by simp
    exact congrArg Scheme.Hom.appTop hscheme
  right_inv φ := by
    let : IsAffine X.obj := inferInstance
    let : IsAffine Y.obj := inferInstance
    have hY : Y.obj.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).inv := by
      apply (cancel_mono (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).hom).1
      have h := congrArg Scheme.Hom.appTop (Scheme.toSpecΓ_isoSpec_inv Y.obj)
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
      change Y.obj.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).hom = 𝟙 _ at h
      calc
        Y.obj.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).hom = 𝟙 _ := h
        _ = (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).inv ≫
            (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).hom := by simp
    have hX : X.obj.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X.obj, ⊤)).hom := by
      simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]
    have hmap : Y.obj.isoSpec.inv.appTop ≫
        (Spec.map (CommRingCat.ofHom φ)).appTop ≫ X.obj.isoSpec.hom.appTop =
        CommRingCat.ofHom φ := by
      rw [hY, hX]
      calc
        (Scheme.ΓSpecIso Γ(Y.obj, ⊤)).inv ≫
            (Spec.map (CommRingCat.ofHom φ)).appTop ≫
            (Scheme.ΓSpecIso Γ(X.obj, ⊤)).hom =
          CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso Γ(X.obj, ⊤)).inv ≫
            (Scheme.ΓSpecIso Γ(X.obj, ⊤)).hom := by
              have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
              exact (congrArg (fun z => z ≫ (Scheme.ΓSpecIso Γ(X.obj, ⊤)).hom) hn).symm
        _ = CommRingCat.ofHom φ := by simp
    ext x
    exact congrArg (fun q : CommRingCat.Hom (Γ(Y.obj, ⊤)) (Γ(X.obj, ⊤)) => q.hom x) hmap

-- Ring equalizers of structure sheaf sections glue maps between affine schemes.
-- The elementwise ring-hom construction above is the only algebra needed: the
-- affine-scheme/ring equivalence turns the resulting ring map back into a map
-- of affine schemes.
private theorem affineHomEquiv_comp {X Y Z : AffineScheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    affineHomEquiv X Z (f ≫ g) =
      (affineHomEquiv X Y f).comp (affineHomEquiv Y Z g) := by
  ext x
  show (CommRingCat.Hom.hom (Scheme.Hom.appTop (f.hom ≫ g.hom))) x = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

private theorem affineMorphism_descends_of_ringSectionEqualizer
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (heq : ∀ x : ∀ i, Γ((U i).obj, ⊤),
      (∀ i j,
        ((pairwiseFst X U f i j).left).appTop.hom (x i) =
        ((pairwiseSnd X U f i j).left).appTop.hom (x j)) →
      ∃! a : Γ(X.obj, ⊤), ∀ i, (AffineScheme.forgetToScheme.map (f i)).appTop.hom a = x i)
    (T : AffineScheme.{u}) (g : ∀ i, U i ⟶ T)
    (hg : ∀ i j,
      (pairwiseFst X U f i j).left ≫ AffineScheme.forgetToScheme.map (g i) =
      (pairwiseSnd X U f i j).left ≫ AffineScheme.forgetToScheme.map (g j)) :
    ∃! h : X ⟶ T, ∀ i, f i ≫ h = g i := by
  let ρ : ∀ i, Γ(X.obj, ⊤) →+* Γ((U i).obj, ⊤) :=
    fun i => (AffineScheme.forgetToScheme.map (f i)).appTop.hom
  let α : ∀ i j, Γ((U i).obj, ⊤) →+* Γ((pairwiseOver X U f i j).left, ⊤) :=
    fun i j => ((pairwiseFst X U f i j).left).appTop.hom
  let β : ∀ i j, Γ((U j).obj, ⊤) →+* Γ((pairwiseOver X U f i j).left, ⊤) :=
    fun i j => ((pairwiseSnd X U f i j).left).appTop.hom
  have hα : ∀ i j,
      α i j = (pullback.fst (AffineScheme.forgetToScheme.map (f i))
          (AffineScheme.forgetToScheme.map (f j))).appTop.hom := by
    intro i j
    rfl
  have hβ : ∀ i j,
      β i j = (pullback.snd (AffineScheme.forgetToScheme.map (f i))
          (AffineScheme.forgetToScheme.map (f j))).appTop.hom := by
    intro i j
    rfl
  let φ : ∀ i, Γ(T.obj, ⊤) →+* Γ((U i).obj, ⊤) :=
    fun i => (AffineScheme.forgetToScheme.map (g i)).appTop.hom
  have hφ : ∀ i j x, α i j (φ i x) = β i j (φ j x) := by
    intro i j x
    have hc := congrArg CommRingCat.Hom.hom (congrArg Scheme.Hom.appTop (hg i j))
    have hc' : (α i j).comp (φ i) = (β i j).comp (φ j) := by
      change (α i j).comp (φ i) = (β i j).comp (φ j) at hc
      exact hc
    exact DFunLike.congr_fun hc' x
  obtain ⟨ψ, hψ, hψuniq⟩ := ringHom_descends_of_sectionEqualizer ρ α β
    (by
      intro x hx
      apply heq x
      intro i j
      show α i j (x i) = β i j (x j)
      exact hx i j)
    (E := Γ(T.obj, ⊤)) φ hφ
  let h := (affineHomEquiv X T).symm ψ
  refine ⟨h, ?_, ?_⟩
  · intro i
    apply (affineHomEquiv (U i) T).injective
    show (ρ i).comp ((affineHomEquiv X T) h) = φ i
    rw [Equiv.apply_symm_apply]
    exact hψ i
  · intro h' hh'
    apply (affineHomEquiv X T).injective
    have hψ' : affineHomEquiv X T h' = ψ := hψuniq _ (by
      intro i
      have hc := congrArg (affineHomEquiv (U i) T) (hh' i)
      rw [affineHomEquiv_comp] at hc
      exact hc)
    simpa [h] using hψ'

private theorem isEffectiveEpiFamily_of_ringSectionsEqualizer
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (heq : ∀ x : ∀ i, Γ((U i).obj, ⊤),
      (∀ i j, (pairwiseFst X U f i j).left.appTop (x i) =
        (pairwiseSnd X U f i j).left.appTop (x j)) →
      ∃! a : Γ(X.obj, ⊤), ∀ i,
        (AffineScheme.forgetToScheme.map (f i)).appTop a = x i) :
    StacksEffectiveEpi.IsEffectiveEpiFamily U f := by
  refine ⟨fun i => inferInstance, ?_⟩
  intro T g hg
  apply affineMorphism_descends_of_ringSectionEqualizer X U f heq T g
  intro i j
  let : IsAffine (AffineScheme.forgetToScheme.obj X) := inferInstanceAs (IsAffine X.obj)
  let : IsAffine (AffineScheme.forgetToScheme.obj (U i)) := inferInstanceAs (IsAffine (U i).obj)
  let : IsAffine (AffineScheme.forgetToScheme.obj (U j)) := inferInstanceAs (IsAffine (U j).obj)
  let : IsAffine (pullback (AffineScheme.forgetToScheme.map (f i))
      (AffineScheme.forgetToScheme.map (f j))) :=
    inferInstance
  let P := AffineScheme.of (pullback (AffineScheme.forgetToScheme.map (f i))
    (AffineScheme.forgetToScheme.map (f j)))
  let a : P ⟶ U i := AffineScheme.ofHom (pairwiseFst X U f i j).left
  let b : P ⟶ U j := AffineScheme.ofHom (pairwiseSnd X U f i j).left
  have hp : IsPullback a b (f i) (f j) := by
    apply IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u}
    exact IsPullback.of_hasPullback _ _
  exact congrArg (fun z => AffineScheme.forgetToScheme.map z) (hg i j P a b hp)

theorem isEffectiveEpiFamily_of_quasicoherentSectionsEqualizer
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) (h : IsQuasicoherentSectionsEqualizer X U f) :
    StacksEffectiveEpi.IsEffectiveEpiFamily U f :=
  isEffectiveEpiFamily_of_ringSectionsEqualizer X U f
    (ringSectionsEqualizer_of_quasicoherentSectionsEqualizer X U f h)

private theorem isEffectiveEpiFamily_of_iso
    {I : Type w} {X : AffineScheme.{u}} {U V : I → AffineScheme.{u}}
    (f : ∀ i, U i ⟶ X) (g : ∀ i, V i ⟶ X)
    (e : ∀ i, U i ≅ V i) (he : ∀ i, (e i).hom ≫ g i = f i)
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily U f) :
    StacksEffectiveEpi.IsEffectiveEpiFamily V g := by
  constructor
  · intro i
    infer_instance
  · intro T k hk
    let kU i := (e i).hom ≫ k i
    have hkU : ∀ (i j : I) (Z : AffineScheme.{u}) (a : Z ⟶ U i)
        (b : Z ⟶ U j), IsPullback a b (f i) (f j) →
        a ≫ kU i = b ≫ kU j := by
      intro i j Z a b hab
      have hab' : IsPullback (a ≫ (e i).hom) (b ≫ (e j).hom)
          (g i) (g j) := by
        apply hab.of_iso (Iso.refl _) (e i) (e j) (Iso.refl _)
        all_goals simp [← he]
      simpa [kU, Category.assoc] using
        hk i j Z (a ≫ (e i).hom) (b ≫ (e j).hom) hab'
    obtain ⟨t, ht, htuniq⟩ := h.2 T kU hkU
    refine ⟨t, ?_, ?_⟩
    · intro i
      apply (cancel_epi (e i).hom).1
      rw [← Category.assoc, he i, ht]
    · intro t' ht'
      apply htuniq t'
      intro i
      rw [← he i, Category.assoc, ht']

private theorem isUniversalEffectiveEpiFamily_of_iso
    {I : Type w} {X : AffineScheme.{u}} {U V : I → AffineScheme.{u}}
    (f : ∀ i, U i ⟶ X) (g : ∀ i, V i ⟶ X)
    (e : ∀ i, U i ≅ V i) (he : ∀ i, (e i).hom ≫ g i = f i)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily V g := by
  constructor
  · intro i
    infer_instance
  · intro Y k W q p hp
    apply h.2 k W q (fun i => p i ≫ (e i).inv)
    intro i
    apply (hp i).of_iso (Iso.refl _) (Iso.refl _) (e i).symm (Iso.refl _)
    · simp
    · simp
    · simp
    · simp [← he i]

private theorem isUniversalEffectiveEpiFamily_comp_iso
    {I : Type w} {X Y : AffineScheme.{u}}
    (U : I → AffineScheme.{u}) (f : ∀ i, U i ⟶ X) (e : X ≅ Y)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U
      (fun i => f i ≫ e.hom) := by
  constructor
  · intro i
    infer_instance
  · intro Z k W q p hp
    apply h.2 (k ≫ e.inv) W q p
    intro i
    apply (hp i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm
    · simp
    · simp
    · simp
    · simp

private noncomputable def affineSchemeIsoSpec (X : AffineScheme.{u}) :
    X ≅ AffineScheme.Spec.obj (op Γ(X.obj, ⊤)) where
  hom := AffineScheme.ofHom X.obj.isoSpec.hom
  inv := AffineScheme.ofHom X.obj.isoSpec.inv
  hom_inv_id := by
    apply InducedCategory.Hom.ext
    exact X.obj.isoSpec.hom_inv_id
  inv_hom_id := by
    apply InducedCategory.Hom.ext
    exact X.obj.isoSpec.inv_hom_id

private lemma affineSchemeIsoSpec_hom_naturality {X Y : AffineScheme.{u}}
    (f : X ⟶ Y) :
    f ≫ (affineSchemeIsoSpec Y).hom =
      (affineSchemeIsoSpec X).hom ≫
        AffineScheme.ofHom (Spec.map f.hom.appTop) := by
  apply InducedCategory.Hom.ext
  exact (Scheme.isoSpec_hom_naturality f.hom).symm

theorem isUniversalEffectiveEpiFamily_spec
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op Γ((U i).obj, ⊤)))
      (fun i => AffineScheme.Spec.map (f i).hom.appTop.op) := by
  apply isUniversalEffectiveEpiFamily_of_iso
    (fun i => f i ≫ (affineSchemeIsoSpec X).hom)
    (fun i => AffineScheme.Spec.map (f i).hom.appTop.op)
    (fun i => affineSchemeIsoSpec (U i))
  · intro i
    exact (affineSchemeIsoSpec_hom_naturality (f i)).symm
  · exact isUniversalEffectiveEpiFamily_comp_iso U f (affineSchemeIsoSpec X) h

private theorem isUniversalEffectiveEpiFamily_of_affineBaseChangeEqualizer
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : ∀ (Y : AffineScheme.{u}) (g : Y ⟶ X),
      IsQuasicoherentSectionsEqualizer Y
        (fun i => pullback (f i) g)
        (fun i => pullback.snd (f i) g)) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f := by
  refine ⟨?_, ?_⟩
  · intro i
    infer_instance
  · intro Y g V q p hp
    let W i := pullback (f i) g
    let r i : W i ⟶ Y := pullback.snd (f i) g
    have hW : StacksEffectiveEpi.IsEffectiveEpiFamily W r :=
      isEffectiveEpiFamily_of_quasicoherentSectionsEqualizer Y W r (h Y g)
    let e (i) : W i ≅ V i :=
      ((hp i).flip.isoIsPullback _ _ (IsPullback.of_hasPullback (f i) g)).symm
    have he : ∀ i, (e i).hom ≫ q i = r i := by
      intro i
      simp [e, r, IsPullback.isoIsPullback_inv_snd]
    exact isEffectiveEpiFamily_of_iso r q e he hW

private noncomputable def affineLineHomEquiv (X : AffineScheme.{u}) :
    (X ⟶ AffineScheme.of (Spec (CommRingCat.of
      (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))) ≃ Γ(X.obj, ⊤) where
  toFun f := AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} f.hom PUnit.unit
  invFun s := AffineScheme.ofHom
    ((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ => s))
  left_inv f := by
    apply InducedCategory.Hom.ext
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective
    funext i
    cases i
    exact congrFun ((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).apply_symm_apply _) _
  right_inv s :=
    congrFun ((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).apply_symm_apply _) _

private lemma affineLineHomEquiv_comp {X Y : AffineScheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ AffineScheme.of (Spec (CommRingCat.of
      (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))) :
    affineLineHomEquiv X (f ≫ g) = f.hom.appTop (affineLineHomEquiv Y g) := rfl

theorem ringSectionsEqualizer_of_isEffectiveEpiFamily
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) (h : StacksEffectiveEpi.IsEffectiveEpiFamily U f)
    (s : ∀ i, Γ((U i).obj, ⊤))
    (hs : ∀ i j, (pairwiseFst X U f i j).left.appTop (s i) =
      (pairwiseSnd X U f i j).left.appTop (s j)) :
    ∃! a : Γ(X.obj, ⊤), ∀ i,
      (AffineScheme.forgetToScheme.map (f i)).appTop a = s i := by
  let T := AffineScheme.of (Spec (CommRingCat.of
    (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))
  let g (i) : U i ⟶ T := (affineLineHomEquiv (U i)).symm (s i)
  have hg : ∀ (i j : I) (Z : AffineScheme.{u}) (a : Z ⟶ U i) (b : Z ⟶ U j),
      IsPullback a b (f i) (f j) → a ≫ g i = b ≫ g j := by
    intro i j Z a b hab
    apply (affineLineHomEquiv Z).injective
    simp only [affineLineHomEquiv_comp, g, Equiv.apply_symm_apply]
    let k : Z.obj ⟶ (pairwiseOver X U f i j).left :=
      pullback.lift a.hom b.hom (congrArg (fun q => q.hom) hab.w)
    have hka : k ≫ (pairwiseFst X U f i j).left = a.hom := pullback.lift_fst _ _ _
    have hkb : k ≫ (pairwiseSnd X U f i j).left = b.hom := pullback.lift_snd _ _ _
    have hc := congrArg (fun t => k.appTop t) (hs i j)
    have ha' := congrArg (fun q => q.appTop (s i)) hka
    have hb' := congrArg (fun q => q.appTop (s j)) hkb
    change k.appTop ((pairwiseFst X U f i j).left.appTop (s i)) =
      a.hom.appTop (s i) at ha'
    change k.appTop ((pairwiseSnd X U f i j).left.appTop (s j)) =
      b.hom.appTop (s j) at hb'
    exact ha'.symm.trans (hc.trans hb')
  obtain ⟨t, ht, hu⟩ := h.2 T g hg
  refine ⟨affineLineHomEquiv X t, ?_, ?_⟩
  · intro i
    exact (affineLineHomEquiv_comp (f i) t).symm.trans
      ((congrArg (affineLineHomEquiv (U i)) (ht i)).trans
        ((affineLineHomEquiv (U i)).apply_symm_apply _))
  · intro a ha
    have hga : (affineLineHomEquiv X).symm a = t := hu _ (by
      intro i
      apply (affineLineHomEquiv (U i)).injective
      simp only [affineLineHomEquiv_comp, Equiv.apply_symm_apply, g]
      exact ha i)
    simpa using congrArg (affineLineHomEquiv X) hga

section SquareZero

open scoped TensorProduct
open TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
def trivSqZeroExtProdLinearEquiv (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    TrivSqZeroExt R M ≃ₗ[R] R × M where
  toFun x := (x.fst, x.snd)
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def trivSqZeroExtTensorLinearEquiv :
    S ⊗[R] TrivSqZeroExt R M ≃ₗ[S] TrivSqZeroExt S (S ⊗[R] M) :=
  AlgebraTensorModule.congr (.refl S S) (trivSqZeroExtProdLinearEquiv R M) ≪≫ₗ
    TensorProduct.prodRight R S S R M ≪≫ₗ
      (AlgebraTensorModule.rid R S S).prodCongr (.refl S _) ≪≫ₗ
        (trivSqZeroExtProdLinearEquiv S (S ⊗[R] M)).symm

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
private lemma trivSqZeroExtTensorLinearEquiv_tmul (s : S) (a : TrivSqZeroExt R M) :
    trivSqZeroExtTensorLinearEquiv R S M (s ⊗ₜ[R] a) =
      (s * algebraMap R S a.fst, s ⊗ₜ[R] a.snd) := by
  simp [trivSqZeroExtTensorLinearEquiv, trivSqZeroExtProdLinearEquiv, Algebra.smul_def, mul_comm]
  rfl

noncomputable def trivSqZeroExtTensorAlgEquiv :
    S ⊗[R] TrivSqZeroExt R M ≃ₐ[S] TrivSqZeroExt S (S ⊗[R] M) :=
  AlgEquiv.ofLinearEquiv (trivSqZeroExtTensorLinearEquiv R S M)
    (by change trivSqZeroExtTensorLinearEquiv R S M ((1 : S) ⊗ₜ[R] (1 : TrivSqZeroExt R M)) = _
        rw [trivSqZeroExtTensorLinearEquiv_tmul]
        apply TrivSqZeroExt.ext <;> simp)
    (by
      intro x y
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => simp [add_mul, hx, hx']
      | tmul s a =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' hy hy' => simp [mul_add, hy, hy']
        | tmul t b =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [trivSqZeroExtTensorLinearEquiv_tmul]
          apply TrivSqZeroExt.ext
          · change (s * t) * algebraMap R S (a * b).fst =
              (s * algebraMap R S a.fst) * (t * algebraMap R S b.fst)
            simp [TrivSqZeroExt.fst_mul, mul_assoc, mul_left_comm, mul_comm]
          · change (s * t) ⊗ₜ[R] (a * b).snd =
              (s * algebraMap R S a.fst) • (t ⊗ₜ[R] b.snd) +
                (MulOpposite.op (t * algebraMap R S b.fst)) • (s ⊗ₜ[R] a.snd)
            simp [TrivSqZeroExt.snd_mul, TensorProduct.tmul_add, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', smul_tmul', Algebra.smul_def,
              mul_assoc, mul_left_comm, mul_comm, op_smul_eq_smul])

private lemma trivSqZeroExtTensorAlgEquiv_tmul (s : S) (a : TrivSqZeroExt R M) :
    trivSqZeroExtTensorAlgEquiv R S M (s ⊗ₜ[R] a) =
      (s * algebraMap R S a.fst, s ⊗ₜ[R] a.snd) :=
  trivSqZeroExtTensorLinearEquiv_tmul R S M s a

noncomputable def trivSqZeroExtBaseChange :
    TrivSqZeroExt R M →+* TrivSqZeroExt S (S ⊗[R] M) :=
  (trivSqZeroExtTensorAlgEquiv R S M).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

lemma trivSqZeroExtBaseChange_apply (a : TrivSqZeroExt R M) :
    trivSqZeroExtBaseChange R S M a = (algebraMap R S a.fst, (1 : S) ⊗ₜ[R] a.snd) := by
  simp [trivSqZeroExtBaseChange, trivSqZeroExtTensorAlgEquiv_tmul]
  rfl

lemma trivSqZeroExtBaseChange_isPushout
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsPushout
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom R M))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom S (S ⊗[R] M)))
      (CommRingCat.ofHom (trivSqZeroExtBaseChange R S M)) := by
  apply (CommRingCat.isPushout_tensorProduct R S (TrivSqZeroExt R M)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (trivSqZeroExtTensorAlgEquiv R S M).toRingEquiv.toCommRingCatIso
  · simp
  · rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    show trivSqZeroExtTensorAlgEquiv R S M (s ⊗ₜ[R] (1 : TrivSqZeroExt R M)) = _
    rw [trivSqZeroExtTensorAlgEquiv_tmul]
    apply TrivSqZeroExt.ext <;> simp
  · rfl

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

lemma trivSqZeroExtBaseChange_isPullback
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsPullback
      (AffineScheme.Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.inlHom S (S ⊗[R] M))).op)
      (AffineScheme.Spec.map (CommRingCat.ofHom (trivSqZeroExtBaseChange R S M)).op)
      (AffineScheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)
      (AffineScheme.Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom R M)).op) := by
  apply IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u}
  apply isPullback_SpecMap_of_isPushout
  exact trivSqZeroExtBaseChange_isPushout R S M

end SquareZero

end SectionsEqualizer

end AlgebraicGeometry
