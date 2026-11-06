module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescentNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusFieldExtension

/-!
# Powers of the canonical Frobenius action on `RΓ(Y_k̄, -)`

Let `k` be a finite field with `q = p ^ f` elements and `Y` a scheme over `k`.  The canonical
action `π_Y^*` on `RΓ(Y_k̄, C|_{Y_k̄})`
(`Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo`) is the endomorphism attached to the
base change twist of `π̄ = π_Y × id` and the Frobenius descent isomorphism `L ≅ (F_Y^f)_* L` of
[Stacks, Tag 03SR].  This file proves that its `m`-th power is the endomorphism attached to the
base change twist of `π̄ ^ m` and the descent isomorphism `L ≅ (F_Y^{f m})_* L`.  This is the form
in which the `m`-th power of `π_X^*` is compared, in the proof of [Stacks, Tag 03V0], with the
Frobenius of the base change of `X` to the extension of degree `m` of `k`.

## Main results

* `CategoryTheory.Functor.derivedTwistEndo_eq_of_iso`: the endomorphism attached to a twist only
  depends on the functor `P` up to an isomorphism compatible with the comparisons.
* `Stacks.EtaleCohomology.derivedTwistEndo_baseChangeTwist_comp`: the base change twist of a
  composite induces the composite of the endomorphisms.
* `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo_pow`: the `m`-th power of `π_Y^*`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P P' : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [P'.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects]
  [F₁.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁ ≅ F₁) (ρ : P' ≅ P)

/-- The componentwise `ρ : P'(K) ≅ P(K)`, as a morphism of bounded below complexes. -/
abbrev isoTwistMap (K : CochainComplex.Plus C) :
    P'.mapCochainComplexPlus.obj K ⟶ P.mapCochainComplexPlus.obj K :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ρ.hom _).app K.obj)

omit [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D] in
/-- Pasting a triangle behind a functor; stated on variables. -/
private lemma map_comp_comp_eq {X Y Z : C} {V : D} (G : C ⥤ D) (g : X ⟶ Y) (r : Y ⟶ Z)
    (t : G.obj Z ⟶ V) (t' : G.obj Y ⟶ V) (h : G.map r ≫ t = t') :
    G.map (g ≫ r) ≫ t = G.map g ≫ t' := by
  rw [G.map_comp, Category.assoc, h]

omit [EnoughInjectives C] [EnoughInjectives D] [P.PreservesInjectiveObjects]
  [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects] in
/-- The chain models of the twisted endomorphisms attached to `g'` and to `g' ≫ ρ` agree. -/
lemma twistChainEndo_comp_isoTwistMap
    (hρ : ∀ X, F₁.map (ρ.hom.app X) ≫ θ.hom.app X = θ'.hom.app X)
    (T : CochainComplex.Plus C) (g' : T ⟶ P'.mapCochainComplexPlus.obj T) :
    twistChainEndo P F₁ F₂ θ T (g' ≫ isoTwistMap P P' ρ T) = twistChainEndo P' F₁ F₂ θ' T g' := by
  unfold twistChainEndo
  congr 1
  ext n : 2
  exact map_comp_comp_eq F₁ (g'.hom.f n) (ρ.hom.app (T.obj.X n)) _ _ (hρ _)

/-- **The twisted endomorphism only depends on `P` up to isomorphism.**  For an isomorphism
`ρ : P' ≅ P` carrying the comparison `θ` to `θ'`, the endomorphism attached to a twist `τ'` of `P'`
is the one attached to the twist `τ' ≫ ρ` of `P`. -/
theorem derivedTwistEndo_eq_of_iso
    (hρ : ∀ X, F₁.map (ρ.hom.app X) ≫ θ.hom.app X = θ'.hom.app X)
    (K : CochainComplex.Plus C) (τ' : K ⟶ P'.mapCochainComplexPlus.obj K) :
    derivedTwistEndo P' F₁ F₂ θ' K τ' =
      derivedTwistEndo P F₁ F₂ θ K (τ' ≫ isoTwistMap P P' ρ K) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsStrictlyGE a := ha
  have : K.obj.IsGE a := inferInstance
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a K.obj
  let T : CochainComplex.Plus C := ⟨R.cocomplex, R.boundedBelow⟩
  let ψ : K ⟶ T := ObjectProperty.homMk R.ι
  have : QuasiIso ψ.hom := R.quasiIso
  have hT : ∀ n, Injective (T.obj.X n) := R.injective
  obtain ⟨g', hg'⟩ := exists_twist_lift P' ψ hT τ'
  have hnat : isoTwistMap P P' ρ K ≫ P.mapCochainComplexPlus.map ψ =
      P'.mapCochainComplexPlus.map ψ ≫ isoTwistMap P P' ρ T := by
    ext n : 2
    exact (ρ.hom.naturality (ψ.hom.f n)).symm
  have hg : DerivedCategory.Plus.Q.map ((τ' ≫ isoTwistMap P P' ρ K) ≫
        P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g' ≫ isoTwistMap P P' ρ T) := by
    rw [Category.assoc, hnat, ← Category.assoc, Functor.map_comp, hg', ← Functor.map_comp,
      Category.assoc]
  have e₁ := twistResolutionIso_hom_comp P F₁ F₂ θ ψ hT _ _ hg
  have e₂ := twistResolutionIso_hom_comp P' F₁ F₂ θ' ψ hT τ' g' hg'
  rw [twistChainEndo_comp_isoTwistMap P P' F₁ F₂ θ θ' ρ hρ] at e₁
  refine DerivedCategory.Plus.ι.map_injective ?_
  rw [← cancel_mono (twistResolutionIso F₁ F₂ ψ hT).hom, e₁, e₂]

end CategoryTheory.Functor


open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Composites of base change twists at the derived level -/

section Composite

variable (Λ : Type r) [Ring Λ] {Y' Y S : Scheme.{u}} (g : Y' ⟶ Y) (s : Y' ⟶ S)
  {E : Type*} [Category* E] [Abelian E] (F₂ : EtaleModules.{u, r} Λ S ⥤ E) [F₂.Additive]

/-- The comparison `a_* ⋙ s_* ≅ s_*` for an endomorphism `a` over `s`. -/
abbrev overDirectImageComp (a : Y' ⟶ Y') (hs : s = a ≫ s) :
    etaleModuleDirectImage.{u, r} Λ a ⋙ etaleModuleDirectImage.{u, r} Λ s ≅
      etaleModuleDirectImage.{u, r} Λ s :=
  etaleModuleDirectImageComp.{u, r} Λ a s s hs

/-- The base change twist `g⁻¹ C ⟶ a_* g⁻¹ C`, applied degreewise to a bounded below complex. -/
abbrev baseChangeTwistComplex (a : Y' ⟶ Y') (b : Y ⟶ Y) (w : a ≫ g = g ≫ b)
    (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b)
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y)) :
    (etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C ⟶
      (etaleModuleDirectImage.{u, r} Λ a).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ) (ComplexShape.up ℤ)).app C.obj)

variable (a₁ a₂ A : Y' ⟶ Y') (b₁ b₂ B : Y ⟶ Y) (w₁ : a₁ ≫ g = g ≫ b₁) (w₂ : a₂ ≫ g = g ≫ b₂)
  (w : A ≫ g = g ≫ B) (hs₁ : s = a₁ ≫ s) (hs₂ : s = a₂ ≫ s) (hs : s = A ≫ s)
  (ψ₁ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b₁)
  (ψ₂ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b₂)
  (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ B)

/-- The comparisons over `s` are compatible with the composition of direct images. -/
lemma map_etaleModuleDirectImageComp_comp_overDirectImageComp (hA : A = a₁ ≫ a₂)
    (X : EtaleModules.{u, r} Λ Y') :
    (etaleModuleDirectImage.{u, r} Λ s).map
        ((etaleModuleDirectImageComp.{u, r} Λ a₁ a₂ A hA).hom.app X) ≫
      (overDirectImageComp Λ s A hs).hom.app X =
    (Functor.twistCompIso (etaleModuleDirectImage.{u, r} Λ a₁) (etaleModuleDirectImage.{u, r} Λ s)
      (etaleModuleDirectImage.{u, r} Λ a₂) (overDirectImageComp Λ s a₁ hs₁)
      (overDirectImageComp Λ s a₂ hs₂)).hom.app X := by
  have h := congrArg (fun z => z.hom.app X) (smallEtalePushforwardComp'_assoc a₁ a₂ s A hA s hs₂
    s hs hs₁ (ModuleCat.{max (u + 1) r} Λ))
  simpa [Functor.twistCompIso, overDirectImageComp, etaleModuleDirectImageComp] using h

/-- **The base change twist of a composite induces the composite endomorphism.**  If `A = a₁ ≫ a₂`
over `B = b₁ ≫ b₂` and `ψ` is `ψ₂` followed by `(b₂)_*` of `ψ₁`, then the endomorphism of
`RF₂(Rs_*(g⁻¹ C))` attached to the twist of `(A, B, ψ)` is the one attached to `(a₂, b₂, ψ₂)`
followed by the one attached to `(a₁, b₁, ψ₁)`. -/
theorem derivedTwistEndo_baseChangeTwist_comp (hA : A = a₁ ≫ a₂) (hB : B = b₁ ≫ b₂)
    (hψ : ∀ L, ψ₂.app L ≫ (etaleModuleDirectImage.{u, r} Λ b₂).map (ψ₁.app L) ≫
      (etaleModuleDirectImageComp.{u, r} Λ b₁ b₂ B hB).hom.app L = ψ.app L)
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y)) :
    Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ A)
        (etaleModuleDirectImage.{u, r} Λ s) F₂ (overDirectImageComp Λ s A hs)
        ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C)
        (baseChangeTwistComplex Λ g A B w ψ C) =
      Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ a₂)
          (etaleModuleDirectImage.{u, r} Λ s) F₂ (overDirectImageComp Λ s a₂ hs₂)
          ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C)
          (baseChangeTwistComplex Λ g a₂ b₂ w₂ ψ₂ C) ≫
        Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ a₁)
          (etaleModuleDirectImage.{u, r} Λ s) F₂ (overDirectImageComp Λ s a₁ hs₁)
          ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C)
          (baseChangeTwistComplex Λ g a₁ b₁ w₁ ψ₁ C) := by
  rw [← Functor.derivedTwistEndo_comp, Functor.derivedTwistEndo_eq_of_iso
    (etaleModuleDirectImage.{u, r} Λ A)
    (etaleModuleDirectImage.{u, r} Λ a₁ ⋙ etaleModuleDirectImage.{u, r} Λ a₂)
    (etaleModuleDirectImage.{u, r} Λ s) F₂ (overDirectImageComp Λ s A hs) _
    (etaleModuleDirectImageComp.{u, r} Λ a₁ a₂ A hA)
    (map_etaleModuleDirectImageComp_comp_overDirectImageComp Λ s a₁ a₂ A hs₁ hs₂ hs hA)]
  congr 1
  subst hA hB
  ext n : 2
  exact etaleModuleBaseChangeTwist_comp Λ g a₁ a₂ b₁ b₂ w₁ w₂ w ψ₁ ψ₂ ψ hψ (C.obj.X n)

/-- The endomorphism attached to a base change twist only depends on the endomorphism `A` through
its value: stated with two names for it, so that an equation `A = A'` can be substituted. -/
lemma derivedTwistEndo_baseChangeTwist_congr (A' : Y' ⟶ Y') (hA : A = A') (w' : A' ≫ g = g ≫ B)
    (hs' : s = A' ≫ s) (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y)) :
    Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ A)
        (etaleModuleDirectImage.{u, r} Λ s) F₂ (overDirectImageComp Λ s A hs)
        ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C)
        (baseChangeTwistComplex Λ g A B w ψ C) =
      Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ A')
        (etaleModuleDirectImage.{u, r} Λ s) F₂ (overDirectImageComp Λ s A' hs')
        ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C)
        (baseChangeTwistComplex Λ g A' B w' ψ C) := by
  subst hA
  rfl

end Composite

/-! ### Powers of the canonical Frobenius action -/

section Power

open Stacks.Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The Frobenius descent isomorphism `L ≅ (F_Y^n)_* L` of [Stacks, Tag 03SR] for the `n`-fold
absolute Frobenius, `n ≠ 0`. -/
abbrev frobeniusPowDescent (n : ℕ) (hn : n ≠ 0) :
    𝟭 (EtaleModules.{u, r} Λ Y.left) ⟶
      etaleModuleDirectImage.{u, r} Λ
        (absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) n) :=
  (etaleSheafPushforwardComparison Y.left
    (absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) n)
    (absoluteFrobeniusPowEtaleSiteIso Y.left p (isInCharacteristic_of_over Y) hn)
    (ModuleCat.{max (u + 1) r} Λ)).hom

/-- The endomorphism of `RΓ(Y_k̄, C|_{Y_k̄})` attached to the base change twist of `π̄ ^ m` over
the `n`-fold absolute Frobenius, `n = q m`. -/
abbrev frobeniusPowCohomologyEndo (m n : ℕ) (hn : n ≠ 0)
    (w : geometricFrobeniusBaseChangePow Y kbar p q hcard m ≫ fieldBaseChangeProj Y kbar =
      fieldBaseChangeProj Y kbar ≫ absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) n)
    (hs : pullback.snd Y.hom (specAlgebraMap k kbar) =
      geometricFrobeniusBaseChangePow Y kbar p q hcard m ≫
        pullback.snd Y.hom (specAlgebraMap k kbar))
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :=
  Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChangePow Y kbar p q hcard m))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (overDirectImageComp Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) _ hs)
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)
    (baseChangeTwistComplex Λ (fieldBaseChangeProj Y kbar) _ _ w (frobeniusPowDescent Λ Y p n hn) C)

/-- `π̄ ^ 1 = π̄`. -/
lemma geometricFrobeniusBaseChangePow_one :
    geometricFrobeniusBaseChangePow Y kbar p q hcard 1 =
      geometricFrobeniusBaseChange Y kbar p q hcard := by
  simp only [geometricFrobeniusBaseChangePow, pow_one]

/-- `π̄ ^ (m + 1) = π̄ ^ m ≫ π̄`. -/
lemma geometricFrobeniusBaseChangePow_succ' (m : ℕ) :
    geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1) =
      geometricFrobeniusBaseChangePow Y kbar p q hcard m ≫
        geometricFrobeniusBaseChange Y kbar p q hcard := by
  simp only [geometricFrobeniusBaseChangePow, pow_succ', End.mul_asHom]

/-- **The `m`-th power of `π_Y^*`.**  The `(m + 1)`-st power of the canonical endomorphism of
`RΓ(Y_k̄, C|_{Y_k̄})` is the endomorphism attached to the base change twist of `π̄ ^ (m + 1)` over
the `q (m + 1)`-fold absolute Frobenius, with the Frobenius descent isomorphism of that power. -/
theorem frobeniusRestrictionCohomologyEndo_pow
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) (m n : ℕ) (hn : n ≠ 0)
    (hnm : n = q * (m + 1))
    (w : geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1) ≫ fieldBaseChangeProj Y kbar =
      fieldBaseChangeProj Y kbar ≫ absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) n)
    (hs : pullback.snd Y.hom (specAlgebraMap k kbar) =
      geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1) ≫
        pullback.snd Y.hom (specAlgebraMap k kbar)) :
    (End.of (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) ^ (m + 1) =
      End.of (frobeniusPowCohomologyEndo Λ Y kbar p q hcard (m + 1) n hn w hs C) := by
  induction m generalizing n with
  | zero =>
      obtain rfl : n = q := by omega
      rw [pow_one, frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
      refine congrArg End.of ?_
      exact (derivedTwistEndo_baseChangeTwist_congr Λ (fieldBaseChangeProj Y kbar) _ _ _ _ w _ _ _
        (geometricFrobeniusBaseChangePow_one Y kbar p _ hcard).symm _ _ C).symm
  | succ m ih =>
      have hq : q ≠ 0 := by
        rintro rfl
        exact hn (by simp [hnm])
      have hqm : q * (m + 1) ≠ 0 := Nat.mul_ne_zero hq (Nat.succ_ne_zero m)
      obtain rfl : n = q + q * (m + 1) := by rw [hnm]; ring
      rw [pow_succ, ih (q * (m + 1)) hqm rfl
          ((geometricFrobeniusBaseChangePow_fst Y kbar p q hcard (m + 1)))
          (geometricFrobeniusBaseChangePow_snd Y kbar p q hcard (m + 1)).symm,
        frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
      ext1
      rw [End.mul_asHom]
      exact (derivedTwistEndo_baseChangeTwist_comp Λ (fieldBaseChangeProj Y kbar) _ _ _ _ _ _ _ _
        _ _ w _ _ hs _ _ _ (geometricFrobeniusBaseChangePow_succ' Y kbar p q hcard (m + 1))
        (absoluteFrobeniusPow_add_eq_comp p (isInCharacteristic_of_over Y))
        (etaleSheafPushforwardComparison_add p (isInCharacteristic_of_over Y) hq hqm _ _) C).symm

end Power

end Stacks.EtaleCohomology

end
