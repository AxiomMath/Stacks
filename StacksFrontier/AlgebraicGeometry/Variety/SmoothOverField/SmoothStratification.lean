module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen

/-!
# Smooth stratification after a purely inseparable extension

A scheme of finite type over a field admits, after a finite purely inseparable extension of
that field, a finite filtration by closed subschemes beginning with its reduction and ending
with the empty scheme, whose successive differences are smooth over the extended field.

## Main results

* `AlgebraicGeometry.exists_finite_purelyInseparable_extension_smooth_stratification`: the
  field extension together with the finite filtration by closed subschemes with smooth strata.

## Implementation notes

Closed subschemes are represented by their ideal sheaves, whose order is opposite to inclusion
of closed subschemes; so the filtration is an increasing family of ideal sheaves. Each stratum
is given as an open subscheme of the preceding closed subscheme whose underlying set is the
complement of the next closed subscheme. The first ideal sheaf is the vanishing ideal of the
whole base-changed scheme, hence that scheme's reduction; the last is the top ideal sheaf,
hence the empty subscheme.

The induction is on a natural-number bound for the dimension, which exists because a
quasi-compact morphism locally of finite type has fibre dimension bounded uniformly and the
base here is a point. At each stage the reduction is made geometrically reduced by a finite
purely inseparable extension, a dense smooth open is extracted, and the induction hypothesis is
applied to the closed complement, whose dimension has dropped. A purely inseparable extension
induces a homeomorphism on base change, which is what keeps the dimension bound available
after each extension.

## References

* [Stacks Project, Tag 0H3W](https://stacks.math.columbia.edu/tag/0H3W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

private theorem pullback_congrHom_hom_snd {X Y S : Scheme.{u}}
    {f₁ f₂ : X ⟶ S} {g₁ g₂ : Y ⟶ S} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst f₂ g₂
  simp [pullback.congrHom_hom, pullback.map]

private theorem purelyInseparable_baseChange_homeomorph {k k₁ : Type u}
    [Field k] [Field k₁] [Algebra k k₁] [Module.Finite k k₁]
    [IsPurelyInseparable k k₁] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsHomeomorph (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k₁))) : pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k k₁))) ⟶ X) := by
  let g : Spec (.of k₁) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k₁))
  let π := pullback.fst f g
  have : UniversallyInjective g :=
    universallyInjective_specMap_of_isPurelyInseparable k k₁
  have : Surjective g := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  have hfinite : (CommRingCat.ofHom (algebraMap k k₁)).hom.Finite := by
    show (algebraMap k k₁).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : IsFinite g := (IsFinite.SpecMap_iff _).2 hfinite
  have : UniversallyInjective π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g).flip ‹UniversallyInjective g›
  have : Surjective π := inferInstance
  have : UniversallyClosed π := inferInstance
  have hopen : IsOpenMap π := by
    intro U hU
    have hclosed := π.isClosedMap (Uᶜ) hU.isClosed_compl
    have heq : π '' U = (π '' Uᶜ)ᶜ := by
      simpa using (Set.image_compl_eq (s := Uᶜ) ⟨π.injective, π.surjective⟩)
    rw [heq]
    exact hclosed.isOpen_compl
  exact ⟨π.continuous, hopen, ⟨π.injective, π.surjective⟩⟩

private theorem comap_geometricallyReduced_eq_vanishingIdeal_top {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] [Algebra k₁ k₂] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k₁)) (I : X.IdealSheafData)
    (hI : I.support = ⊤) (hgeom : GeometricallyReduced (I.subschemeι ≫ f)) :
    let g : Spec (.of k₂) ⟶ Spec (.of k₁) :=
      Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))
    let Y := pullback f g
    I.comap (pullback.fst f g) =
      Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y) := by
  let g : Spec (.of k₂) ⟶ Spec (.of k₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))
  let Y : Scheme := pullback f g
  let π := pullback.fst f g
  have hsupport : (I.comap π).support = (⊤ : Closeds Y) := by
    rw [Scheme.IdealSheafData.support_comap, hI]
    exact TopologicalSpace.Closeds.ext (by simp)
  let e : (I.comap π).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
    I.comapIso π ≪≫ pullbackSymmetry π I.subschemeι ≪≫
      pullbackRightPullbackFstIso f g I.subschemeι
  have hred : IsReduced (pullback (I.subschemeι ≫ f) g) := inferInstance
  have : IsReduced (I.comap π).subscheme :=
    ObjectProperty.prop_of_iso (P := fun Z : Scheme => IsReduced Z) e.symm hred
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
    (I.comap π) ⊤ hsupport

private theorem smooth_pullback_of_extension {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] [Algebra k₁ k₂]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of k₁)) (g : Spec (.of k₂) ⟶ Spec (.of k₁))
    (hf : Smooth f) : Smooth (pullback.snd f g) :=
  inferInstance

private theorem smooth_open_baseChange_of_extension {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] [Algebra k₁ k₂]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of k₁))
    (g : Spec (.of k₂) ⟶ Spec (.of k₁)) (U : V.Opens)
    (hsm : Smooth (U.ι ≫ f)) :
    Smooth ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g) := by
  let π := pullback.fst f g
  let e := (pullbackRestrictIsoRestrict π U).symm ≪≫
    pullbackSymmetry π U.ι ≪≫ pullbackRightPullbackFstIso f g U.ι
  have hsm' : Smooth (pullback.snd (U.ι ≫ f) g) :=
    smooth_pullback_of_extension (U.ι ≫ f) g hsm
  have he : e.hom ≫ pullback.snd (U.ι ≫ f) g =
      (π ⁻¹ᵁ U).ι ≫ pullback.snd f g := by
    dsimp [e]
    simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd]
    rw [pullbackSymmetry_hom_comp_snd_assoc (f := π) (g := U.ι)
      (h := pullback.snd f g), pullbackRestrictIsoRestrict_inv_fst_assoc]
  have hsm'' : Smooth (e.hom ≫ pullback.snd (U.ι ≫ f) g) := inferInstance
  rwa [he] at hsm''

private noncomputable def pushedSubschemeIso {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (Q : I.subscheme.IdealSheafData) :
    (Q.map I.subschemeι).subscheme ≅ Q.subscheme := by
  let P := Q.map I.subschemeι
  let j : Q.subscheme ⟶ Y := Q.subschemeι ≫ I.subschemeι
  let e : Q.subscheme ⟶ P.subscheme :=
    IsClosedImmersion.lift P.subschemeι j (by simp [P, j, Scheme.Hom.ker_comp])
  have he : e ≫ P.subschemeι = j := by
    exact IsClosedImmersion.lift_fac P.subschemeι j (by simp [P, j, Scheme.Hom.ker_comp])
  have hker : j.ker = P := by
    simp [j, P, Scheme.Hom.ker_comp]
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq j P.subschemeι e he (by
    rw [hker, Scheme.IdealSheafData.ker_subschemeι])
  exact (asIso e).symm

private theorem pushedSubschemeIso_hom_subschemeι {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (Q : I.subscheme.IdealSheafData) :
    (pushedSubschemeIso I Q).hom ≫ Q.subschemeι ≫ I.subschemeι =
      (Q.map I.subschemeι).subschemeι := by
  simp only [pushedSubschemeIso, Iso.symm_hom, asIso_inv]
  rw [IsIso.inv_comp_eq]
  exact (IsClosedImmersion.lift_fac _ _ (by simp [Scheme.Hom.ker_comp])).symm

private theorem smooth_preimageIso {A B S : Scheme.{u}} (e : A ≅ B) (f : B ⟶ S)
    (U : B.Opens) (hU : Smooth (U.ι ≫ f)) :
    Smooth (((e.hom ⁻¹ᵁ U).ι ≫ e.hom) ≫ f) := by
  let V := e.hom ⁻¹ᵁ U
  let eU := e.hom.preimageIso U
  have hfac : eU.hom ≫ U.ι = V.ι ≫ e.hom :=
    Scheme.Hom.preimageIso_hom_ι e.hom U
  have h' : Smooth (eU.hom ≫ (U.ι ≫ f)) := inferInstance
  rw [← Category.assoc, hfac] at h'
  simpa only [Category.assoc] using h'

private theorem smooth_pushedSubscheme {Y S : Scheme.{u}} (I : Y.IdealSheafData)
    (Q : I.subscheme.IdealSheafData) (p : Y ⟶ S) (U : Q.subscheme.Opens)
    (hU : Smooth (U.ι ≫ Q.subschemeι ≫ I.subschemeι ≫ p)) :
    Smooth (((((pushedSubschemeIso I Q).hom ⁻¹ᵁ U).ι) ≫
      (Q.map I.subschemeι).subschemeι) ≫ p) := by
  let e := pushedSubschemeIso I Q
  let V := e.hom ⁻¹ᵁ U
  have h := smooth_preimageIso e (Q.subschemeι ≫ I.subschemeι ≫ p) U hU
  have h' : Smooth (V.ι ≫ (e.hom ≫ Q.subschemeι ≫ I.subschemeι) ≫ p) := by
    simpa [Category.assoc] using h
  rw [pushedSubschemeIso_hom_subschemeι] at h'
  simpa only [Category.assoc] using h'

private theorem support_map_subschemeι {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (Q : I.subscheme.IdealSheafData) :
    (Q.map I.subschemeι).support =
      ⟨I.subschemeι '' (Q.support : Set I.subscheme), by
        exact (I.subschemeι.isClosedEmbedding.isClosedMap _ Q.support.isClosed)⟩ := by
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.IdealSheafData.support_map]
  calc
    closure (I.subschemeι '' (Q.support : Set I.subscheme)) =
        I.subschemeι '' closure (Q.support : Set I.subscheme) :=
      I.subschemeι.isClosedEmbedding.closure_image_eq _
    _ = I.subschemeι '' (Q.support : Set I.subscheme) := by
      rw [Q.support.isClosed.closure_eq]

private theorem transportedOpen_compl_support {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (Q R : I.subscheme.IdealSheafData) (U : Q.subscheme.Opens)
    (hU : (U : Set Q.subscheme) = {x | Q.subschemeι x ∉ R.support}) :
    (((pushedSubschemeIso I Q).hom ⁻¹ᵁ U : (Q.map I.subschemeι).subscheme.Opens) :
      Set (Q.map I.subschemeι).subscheme) =
    {x | (Q.map I.subschemeι).subschemeι x ∉ (R.map I.subschemeι).support} := by
  ext x
  show ((pushedSubschemeIso I Q).hom x ∈ (U : Set Q.subscheme)) ↔ _
  have hpoint :
      I.subschemeι (Q.subschemeι ((pushedSubschemeIso I Q).hom x)) =
        (Q.map I.subschemeι).subschemeι x := by
    simpa using congrArg (fun g : (Q.map I.subschemeι).subscheme ⟶ Y => g x)
      (pushedSubschemeIso_hom_subschemeι I Q)
  rw [hU, support_map_subschemeι]
  constructor
  · rintro hx ⟨z, hz, hzx⟩
    obtain rfl := I.subschemeι.isClosedEmbedding.injective (hzx.trans hpoint.symm)
    exact hx hz
  · exact fun hx hq => hx ⟨Q.subschemeι ((pushedSubschemeIso I Q).hom x), hq, hpoint⟩

private theorem comap_vanishingIdeal_top_of_iso {A B : Scheme.{u}}
    (e : A ≅ B) :
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds A)).comap e.inv =
      Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds B) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds A)
  let f := e.inv
  have hsupport : (I.comap f).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    have hI : I.support = ⊤ := by simp [I]
    rw [hI]
    ext x
    simp
  let pbiso : pullback f I.subschemeι ≅ I.subscheme := asIso (pullback.snd f I.subschemeι)
  let subiso : (I.comap f).subscheme ≅ I.subscheme := I.comapIso f ≪≫ pbiso
  have hred : IsReduced (I.comap f).subscheme :=
    ObjectProperty.prop_of_iso (P := fun X : Scheme => IsReduced X) subiso.symm
      (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (⊤ : Closeds A))
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme (I.comap f) ⊤ hsupport

/-- The canonical map from the comapped subscheme to the original one commutes with the
closed immersions. -/
private theorem comapIso_hom_snd_comp_subschemeι {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) :
    ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) ≫ I.subschemeι =
      (I.comap f).subschemeι ≫ f := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]

/-- Pulling back an open of the form "complement of the support of `S`" along a map commuting
with `c` gives the complement of the support of `S.comap c`. -/
private theorem preimage_eq_compl_support_comap {P Q X X' : Scheme.{u}} (a : P ⟶ X)
    (b : Q ⟶ X') (c : X' ⟶ X) (β : Q ⟶ P) (hfac : β ≫ a = b ≫ c) (S : X.IdealSheafData)
    (U : P.Opens) (hU : (U : Set P) = {x | a x ∉ S.support}) :
    ((β ⁻¹ᵁ U : Q.Opens) : Set Q) = {x | b x ∉ (S.comap c).support} := by
  ext x
  have hpoint : a (β x) = c (b x) := congrArg (fun q : Q ⟶ X => q x) hfac
  show β x ∈ (U : Set P) ↔ _
  rw [hU, Scheme.IdealSheafData.support_comap]
  show a (β x) ∉ S.support ↔ _
  rw [hpoint]
  rfl

private theorem transportSmoothFiltrationIso {A B S : Scheme.{u}}
    (e : A ≅ B) (pA : A ⟶ S) (pB : B ⟶ S)
    (he : e.hom ≫ pB = pA)
    (t : ℕ) (Z : Fin (t + 1) → A.IdealSheafData)
    (hstart : Z 0 = Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds A))
    (hend : Z (Fin.last t) = ⊤)
    (hmono : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
    (hstrata : ∀ i : Fin t, ∃ U : (Z i.castSucc).subscheme.Opens,
      (U : Set (Z i.castSucc).subscheme) =
        {x | (Z i.castSucc).subschemeι x ∉ (Z i.succ).support} ∧
      Smooth (U.ι ≫ (Z i.castSucc).subschemeι ≫ pA)) :
    ∃ Z' : Fin (t + 1) → B.IdealSheafData,
      Z' 0 = Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds B) ∧
      Z' (Fin.last t) = ⊤ ∧
      (∀ i : Fin t, Z' i.castSucc ≤ Z' i.succ) ∧
      (∀ i : Fin t, ∃ U : (Z' i.castSucc).subscheme.Opens,
        (U : Set (Z' i.castSucc).subscheme) =
          {x | (Z' i.castSucc).subschemeι x ∉ (Z' i.succ).support} ∧
        Smooth (U.ι ≫ (Z' i.castSucc).subschemeι ≫ pB)) := by
  let Z' : Fin (t + 1) → B.IdealSheafData := fun i => (Z i).comap e.inv
  refine ⟨Z', ?_, ?_, ?_, ?_⟩
  · show (Z 0).comap e.inv = _
    rw [hstart]
    exact comap_vanishingIdeal_top_of_iso e
  · show (Z (Fin.last t)).comap e.inv = ⊤
    rw [hend, Scheme.IdealSheafData.comap_top]
  · exact fun i => Scheme.IdealSheafData.comap_mono e.inv (hmono i)
  · intro i
    obtain ⟨U, hU, hsm⟩ := hstrata i
    let I := Z i.castSucc
    let Ic := I.comap e.inv
    let ei : Ic.subscheme ≅ I.subscheme :=
      I.comapIso e.inv ≪≫ asIso (pullback.snd e.inv I.subschemeι)
    have hfac : ei.hom ≫ I.subschemeι = Ic.subschemeι ≫ e.inv :=
      comapIso_hom_snd_comp_subschemeι I e.inv
    let V := ei.hom ⁻¹ᵁ U
    refine ⟨V, preimage_eq_compl_support_comap _ _ _ _ hfac _ U hU, ?_⟩
    have he' : e.inv ≫ pA = pB := by rw [← he, Iso.inv_hom_id_assoc]
    have hsm' := smooth_preimageIso ei (I.subschemeι ≫ pA) U hsm
    have heq : (V.ι ≫ ei.hom) ≫ (I.subschemeι ≫ pA) = (V.ι ≫ Ic.subschemeι) ≫ pB := by
      rw [← he', ← Category.assoc, ← Category.assoc, Category.assoc V.ι, hfac]
      simp only [Category.assoc]
    rw [heq] at hsm'
    simpa only [Category.assoc] using hsm'

private noncomputable def subschemeBaseChangeIso {X S T : Scheme.{u}}
    (p : X ⟶ S) (I : X.IdealSheafData) (g : T ⟶ S) :
    (I.comap (pullback.fst p g)).subscheme ≅ pullback (I.subschemeι ≫ p) g :=
  I.comapIso (pullback.fst p g) ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso p g I.subschemeι

private theorem subschemeBaseChangeIso_hom_fst {X S T : Scheme.{u}}
    (p : X ⟶ S) (I : X.IdealSheafData) (g : T ⟶ S) :
    (subschemeBaseChangeIso p I g).hom ≫ pullback.fst (I.subschemeι ≫ p) g =
      (I.comapIso (pullback.fst p g)).hom ≫ pullback.snd _ _ := by
  simp [subschemeBaseChangeIso, Category.assoc]

private theorem subschemeBaseChangeIso_hom_snd {X S T : Scheme.{u}}
    (p : X ⟶ S) (I : X.IdealSheafData) (g : T ⟶ S) :
    (subschemeBaseChangeIso p I g).hom ≫ pullback.snd (I.subschemeι ≫ p) g =
      (I.comap (pullback.fst p g)).subschemeι ≫ pullback.snd p g := by
  simp [subschemeBaseChangeIso, Category.assoc,
    pullbackSymmetry_hom_comp_snd_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

private theorem smooth_open_comap {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] [Algebra k₁ k₂] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k₁)) (I : X.IdealSheafData)
    (g : Spec (.of k₂) ⟶ Spec (.of k₁)) (U : I.subscheme.Opens)
    (hU : Smooth (U.ι ≫ I.subschemeι ≫ p)) :
    let β := (I.comapIso (pullback.fst p g)).hom ≫ pullback.snd _ _
    Smooth ((β ⁻¹ᵁ U).ι ≫ (I.comap (pullback.fst p g)).subschemeι ≫
      pullback.snd p g) := by
  let e := subschemeBaseChangeIso p I g
  let V := pullback.fst (I.subschemeι ≫ p) g ⁻¹ᵁ U
  have hV : Smooth (V.ι ≫ pullback.snd (I.subschemeι ≫ p) g) :=
    smooth_open_baseChange_of_extension (I.subschemeι ≫ p) g U hU
  have h := smooth_preimageIso e (pullback.snd (I.subschemeι ≫ p) g) V hV
  rw [Category.assoc, subschemeBaseChangeIso_hom_snd] at h
  have he : e.hom ⁻¹ᵁ V =
      ((I.comapIso (pullback.fst p g)).hom ≫ pullback.snd _ _) ⁻¹ᵁ U := by
    show (e.hom ≫ pullback.fst (I.subschemeι ≫ p) g) ⁻¹ᵁ U = _
    rw [subschemeBaseChangeIso_hom_fst]
  rwa [he] at h

/-- An ideal sheaf lies below the pushforward of any ideal sheaf on its own subscheme. -/
private theorem le_map_subschemeι {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (R : I.subscheme.IdealSheafData) : I ≤ R.map I.subschemeι :=
  calc
    I = (⊥ : I.subscheme.IdealSheafData).map I.subschemeι := by simp
    _ ≤ R.map I.subschemeι := Scheme.IdealSheafData.map_mono _ bot_le

private theorem prependSmoothFiltration {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) (I J : Y.IdealSheafData) (hIJ : I ≤ J)
    (U₀ : I.subscheme.Opens)
    (hU₀ : (U₀ : Set I.subscheme) = {x | I.subschemeι x ∉ J.support})
    (hsm₀ : Smooth (U₀.ι ≫ I.subschemeι ≫ p))
    (t : ℕ) (Z' : Fin (t + 1) → J.subscheme.IdealSheafData)
    (hstart : Z' 0 = Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds J.subscheme))
    (hend : Z' (Fin.last t) = ⊤)
    (hmono : ∀ i : Fin t, Z' i.castSucc ≤ Z' i.succ)
    (hstrata : ∀ i : Fin t, ∃ U : (Z' i.castSucc).subscheme.Opens,
      (U : Set (Z' i.castSucc).subscheme) =
        {x | (Z' i.castSucc).subschemeι x ∉ (Z' i.succ).support} ∧
      Smooth (U.ι ≫ (Z' i.castSucc).subschemeι ≫ J.subschemeι ≫ p)) :
    ∃ Z : Fin (t + 2) → Y.IdealSheafData,
      Z 0 = I ∧ Z (Fin.last (t + 1)) = ⊤ ∧
      (∀ i : Fin (t + 1), Z i.castSucc ≤ Z i.succ) ∧
      (∀ i : Fin (t + 1), ∃ U : (Z i.castSucc).subscheme.Opens,
        (U : Set (Z i.castSucc).subscheme) =
          {x | (Z i.castSucc).subschemeι x ∉ (Z i.succ).support} ∧
        Smooth (U.ι ≫ (Z i.castSucc).subschemeι ≫ p)) := by
  classical
  let Z : Fin (t + 2) → Y.IdealSheafData :=
    Fin.cases I (fun i => (Z' i).map J.subschemeι)
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · simp [Z]
  · show (Z' (Fin.last t)).map J.subschemeι = ⊤
    rw [hend]
    simp
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hIJ.trans (le_map_subschemeι J _)
    · show (Z' j.castSucc).map J.subschemeι ≤ (Z' j.succ).map J.subschemeι
      exact Scheme.IdealSheafData.map_mono J.subschemeι (hmono j)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨U₀, ?_, hsm₀⟩
      show (U₀ : Set I.subscheme) =
        {x | I.subschemeι x ∉ ((Z' 0).map J.subschemeι).support}
      rw [hstart]
      have hs : ((Scheme.IdealSheafData.vanishingIdeal
          (⊤ : Closeds J.subscheme)).map J.subschemeι).support = J.support := by
        ext x
        simp only [support_map_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
          Closeds.coe_mk, Closeds.coe_top, Set.image_univ,
          Scheme.IdealSheafData.range_subschemeι]
      rwa [hs]
    · obtain ⟨U', hU', hsm'⟩ := hstrata j
      let V := (pushedSubschemeIso J (Z' j.castSucc)).hom ⁻¹ᵁ U'
      refine ⟨V, ?_, ?_⟩
      · show (↑V) =
          {x | ((Z' j.castSucc).map J.subschemeι).subschemeι x ∉
            ((Z' j.succ).map J.subschemeι).support}
        have hV : (↑V : Set (((Z' j.castSucc).map J.subschemeι).subscheme)) =
            (pushedSubschemeIso J (Z' j.castSucc)).hom ⁻¹' (U' : Set _) := rfl
        rw [hV]
        exact transportedOpen_compl_support J
          (Z' j.castSucc) (Z' j.succ) U' hU'
      · simpa [Z, V] using smooth_pushedSubscheme J (Z' j.castSucc) p U' hsm'

/-- In a Noetherian space of dimension at most `n`, the complement of a dense open subset has
dimension `< n`: it contains no irreducible component, so every chain of irreducible closed subsets
in it extends by a component. -/
theorem topologicalKrullDim_compl_lt_nat {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {U : Set X} (hU : IsOpen U) (hdense : Dense U)
    {n : ℕ} (hdim : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (Uᶜ : Set X) < n := by
  rw [show topologicalKrullDim (Uᶜ : Set X) =
    Order.krullDim (TopologicalSpace.IrreducibleCloseds (Uᶜ : Set X)) by rfl,
    Order.krullDim_lt_coe_iff]
  intro p
  let incl : (Uᶜ : Set X) → X := Subtype.val
  have hind : Topology.IsInducing incl := Topology.IsEmbedding.subtypeVal.isInducing
  have hcont : Continuous incl := continuous_subtype_val
  let φ : TopologicalSpace.IrreducibleCloseds (Uᶜ : Set X) →
      TopologicalSpace.IrreducibleCloseds X :=
    TopologicalSpace.IrreducibleCloseds.map incl hcont
  have hφ : StrictMono φ :=
    TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing hind
  let q := p.map φ hφ
  have hlastsub : (φ p.last : Set X) ⊆ Uᶜ := by
    rw [TopologicalSpace.IrreducibleCloseds.coe_map]
    refine closure_minimal ?_ hU.isClosed_compl
    rintro x ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨C, hC, hCcontains⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (φ p.last : Set X) (φ p.last).2
  have hCnot : ¬ (C : Set X) ⊆ Uᶜ := by
    intro hCF
    obtain ⟨O, hOopen, hOnonempty, hOC⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
        C hC
    obtain ⟨x, hxO, hxU⟩ := (dense_iff_inter_open.mp hdense) O hOopen hOnonempty
    exact hCF (hOC hxO) hxU
  let C' : TopologicalSpace.IrreducibleCloseds X :=
    ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have hCcontains' : φ p.last ≤ C' := hCcontains
  have hlt : φ p.last < C' := by
    apply lt_of_le_of_ne hCcontains'
    intro heq
    apply hCnot
    have hc : (C : Set X) = (φ p.last : Set X) :=
      congrArg (fun T : TopologicalSpace.IrreducibleCloseds X => (T : Set X)) heq.symm
    rw [hc]
    exact hlastsub
  have hltq : q.last < C' := by simpa [q] using hlt
  let r := q.snoc C' hltq
  have hrlen : r.length = p.length + 1 := by
    show q.length + 0 + 1 = p.length + 1
    rfl
  have hrle : (r.length : WithBot ℕ∞) ≤ n :=
    (Order.LTSeries.length_le_krullDim r).trans hdim
  have hrlenNat : r.length ≤ n := by exact_mod_cast hrle
  rw [hrlen] at hrlenNat
  omega

private theorem topologicalKrullDim_subscheme_eq_support {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set X) := by
  have hrange : I.subschemeι '' (Set.univ : Set I.subscheme) = (I.support : Set X) := by
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι]
  let e : I.subscheme ≃ₜ (I.support : Set X) :=
    (Homeomorph.Set.univ I.subscheme).symm.trans
      (I.subschemeι.isClosedEmbedding.isEmbedding.homeomorphImage Set.univ) |>.trans
        (Homeomorph.setCongr hrange)
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

private theorem topologicalKrullDim_vanishingIdeal_compl_lt_nat {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {U : Set X}
    (hU : IsOpen U) (hdense : Dense U) {n : ℕ}
    (hdim : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (X := X)
      (⟨Uᶜ, hU.isClosed_compl⟩ : Closeds X)).subscheme < n := by
  rw [topologicalKrullDim_subscheme_eq_support,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact topologicalKrullDim_compl_lt_nat hU hdense hdim

private theorem topologicalKrullDim_lt_nat_succ_le {X : Type u} [TopologicalSpace X]
    {n : ℕ} (h : topologicalKrullDim X < n + 1) : topologicalKrullDim X ≤ n := by
  cases hd : topologicalKrullDim X with
  | bot => exact bot_le
  | coe d =>
    have h' : d < n + 1 := (WithBot.lt_coe_iff.mp h) d hd
    cases d with
    | top => simp at h'
    | coe m =>
      have hm' : m < n + 1 := by exact_mod_cast h'
      have hm : m ≤ n := by omega
      exact WithBot.coe_le_coe.mpr (WithBot.coe_le_coe.mpr hm)

private theorem topologicalKrullDim_lt_zero_iff_isEmpty {X : Type u}
    [TopologicalSpace X] : topologicalKrullDim X < 0 ↔ IsEmpty X := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨x⟩ := not_isEmpty_iff.mp hne
    have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have hnonneg : (0 : WithBot ℕ∞) ≤ topologicalKrullDim X := Order.krullDim_nonneg
    exact (not_lt_of_ge hnonneg) h
  · intro h
    let : IsEmpty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨fun C => h.false (Classical.choose C.isIrreducible'.nonempty)⟩
    show Order.krullDim (TopologicalSpace.IrreducibleCloseds X) < 0
    rw [Order.krullDim_eq_bot]
    simp

private theorem exists_nat_bound_topologicalKrullDim {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ n : ℕ, topologicalKrullDim X ≤ n := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_fiber_le f
  have hfiber : f ⁻¹' {default} = (Set.univ : Set X) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ]
    exact ⟨fun _ => True.intro, fun _ => Subsingleton.elim _ _⟩
  let e₀ : (Set.univ : Set X) ≃ₜ f ⁻¹' {default} := Homeomorph.setCongr hfiber.symm
  let e : X ≃ₜ f.fiber default :=
    (Homeomorph.Set.univ X).symm.trans (e₀.trans (f.fiberHomeo default).symm)
  exact ⟨n, (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans_le (hn default)⟩

private abbrev SmoothStratificationResult {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :=
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : Module.Finite k k') (_ : IsPurelyInseparable k k'),
      let g : Spec (.of k') ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k k'))
      let Y : Scheme.{u} := pullback f g
      let p : Y ⟶ Spec (.of k') := pullback.snd f g
      ∃ (t : ℕ) (Z : Fin (t + 1) → Y.IdealSheafData),
        Z 0 = Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y) ∧
        Z ⟨t, Nat.lt_succ_self t⟩ = ⊤ ∧
        (∀ i : Fin t, Z i.castSucc ≤ Z i.succ) ∧
        (∀ i : Fin t, ∃ U : (Z i.castSucc).subscheme.Opens,
          (U : Set (Z i.castSucc).subscheme) =
            {x | (Z i.castSucc).subschemeι x ∉ (Z i.succ).support} ∧
          Smooth (U.ι ≫ (Z i.castSucc).subschemeι ≫ p))

private theorem exists_smoothStratification_of_dim_le :
    ∀ n : ℕ, ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f],
      topologicalKrullDim X ≤ n → SmoothStratificationResult f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k _ X f _ _ hdim
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let : IsNoetherian X := {}
    have hX : (irreducibleComponents X).Finite :=
      AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
    obtain ⟨k₁, hk₁, hAlg₁, hFinite₁, hPure₁, hgeom⟩ :=
      exists_finite_purelyInseparable_extension_geometricallyReduced_reduction k f hX
    let : Field k₁ := hk₁
    let : Algebra k k₁ := hAlg₁
    let : Module.Finite k k₁ := hFinite₁
    let : IsPurelyInseparable k k₁ := hPure₁
    let g₁ : Spec (.of k₁) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k k₁))
    let Y₁ : Scheme.{u} := pullback f g₁
    let p₁ : Y₁ ⟶ Spec (.of k₁) := pullback.snd f g₁
    let I₁ : Y₁.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y₁)
    have : LocallyOfFiniteType p₁ := by infer_instance
    have : QuasiCompact p₁ := by infer_instance
    have : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian p₁
    have : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace p₁
    have : IsNoetherian Y₁ := {}
    have : IsReduced I₁.subscheme :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (⊤ : Closeds Y₁)
    change GeometricallyReduced (I₁.subschemeι ≫ p₁) at hgeom
    have : LocallyOfFiniteType (I₁.subschemeι ≫ p₁) := by infer_instance
    have : QuasiCompact (I₁.subschemeι ≫ p₁) := by infer_instance
    have : IsLocallyNoetherian I₁.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (I₁.subschemeι ≫ p₁)
    have : CompactSpace I₁.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (I₁.subschemeι ≫ p₁)
    have : IsNoetherian I₁.subscheme := {}
    obtain ⟨U₁, hU₁dense, hU₁smooth⟩ :=
      (geometricallyReduced_iff_exists_dense_open_smooth
        (I₁.subschemeι ≫ p₁)).mp hgeom
    have hhomeo₁ : IsHomeomorph (pullback.fst f g₁ : Y₁ ⟶ X) :=
      purelyInseparable_baseChange_homeomorph (k₁ := k₁) f
    have hdimY₁ : topologicalKrullDim Y₁ ≤ n := by
      calc
        topologicalKrullDim Y₁ = topologicalKrullDim X :=
          IsHomeomorph.topologicalKrullDim_eq (pullback.fst f g₁) hhomeo₁
        _ ≤ n := hdim
    have hdimI₁ : topologicalKrullDim I₁.subscheme ≤ n :=
      I₁.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le |>.trans hdimY₁
    let R : I₁.subscheme.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      ⟨U₁ᶜ, U₁.2.isClosed_compl⟩
    have hdimR : topologicalKrullDim R.subscheme < n :=
      topologicalKrullDim_vanishingIdeal_compl_lt_nat U₁.isOpen hU₁dense hdimI₁
    let J₁ : Y₁.IdealSheafData := R.map I₁.subschemeι
    let eRJ := pushedSubschemeIso I₁ R
    have hdimJ₁ : topologicalKrullDim J₁.subscheme < n := by
      have heq : topologicalKrullDim J₁.subscheme = topologicalKrullDim R.subscheme :=
        IsHomeomorph.topologicalKrullDim_eq (Scheme.homeoOfIso eRJ)
          (Scheme.homeoOfIso eRJ).isHomeomorph
      rw [heq]
      exact hdimR
    let pJ : J₁.subscheme ⟶ Spec (.of k₁) := J₁.subschemeι ≫ p₁
    cases n with
    | zero =>
      have hRempty : IsEmpty R.subscheme :=
        (topologicalKrullDim_lt_zero_iff_isEmpty).mp hdimR
      have hU₁all : U₁ = ⊤ := by
        ext x
        show x ∈ U₁ ↔ True
        simp only [iff_true]
        by_contra hx
        have hxR : x ∈ (R.support : Set I₁.subscheme) := by
          simpa [R, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hx
        rw [← Scheme.IdealSheafData.range_subschemeι] at hxR
        obtain ⟨y, _⟩ := hxR
        exact hRempty.false y
      let Z : Fin 2 → Y₁.IdealSheafData := Fin.cases I₁ (fun _ => ⊤)
      refine ⟨k₁, hk₁, hAlg₁, hFinite₁, hPure₁, 1, Z, ?_, ?_, ?_, ?_⟩
      · show I₁ = Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y₁)
        rfl
      · show ⊤ = ⊤
        rfl
      · intro i
        fin_cases i
        exact le_top
      · intro i
        fin_cases i
        refine ⟨U₁, ?_, ?_⟩
        · rw [hU₁all]
          ext x
          show x ∈ (⊤ : I₁.subscheme.Opens) ↔
            x ∈ {x | I₁.subschemeι x ∉ (⊤ : Y₁.IdealSheafData).support}
          simp only [Scheme.IdealSheafData.support_top]
          show True ↔ ¬ False
          simp
        · exact hU₁smooth
    | succ m =>
      have hdimJ : topologicalKrullDim J₁.subscheme ≤ m :=
        topologicalKrullDim_lt_nat_succ_le hdimJ₁
      obtain ⟨k₂, hk₂, hAlg₂, hFinite₂, hPure₂, t, Z', hstart, hend, hmono, hstrata⟩ :=
        ih m (Nat.lt_succ_self m) k₁ pJ hdimJ
      let : Field k₂ := hk₂
      let : Algebra k₁ k₂ := hAlg₂
      let : Module.Finite k₁ k₂ := hFinite₂
      let : IsPurelyInseparable k₁ k₂ := hPure₂
      let : Algebra k k₂ := (algebraMap k₁ k₂).comp (algebraMap k k₁) |>.toAlgebra
      let : IsScalarTower k k₁ k₂ := IsScalarTower.of_algebraMap_eq' rfl
      let : Module.Finite k k₂ := Module.Finite.trans k₁ k₂
      let : IsPurelyInseparable k k₂ := IsPurelyInseparable.trans k k₁ k₂
      let g₂ : Spec (.of k₂) ⟶ Spec (.of k₁) :=
        Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))
      let Y₂ := pullback p₁ g₂
      let p₂ : Y₂ ⟶ Spec (.of k₂) := pullback.snd p₁ g₂
      let π : Y₂ ⟶ Y₁ := pullback.fst p₁ g₂
      let I₂ := I₁.comap π
      let J₂ := J₁.comap π
      let eJ := subschemeBaseChangeIso p₁ J₁ g₂
      have heJ : eJ.symm.hom ≫ (J₂.subschemeι ≫ p₂) = pullback.snd pJ g₂ := by
        rw [← subschemeBaseChangeIso_hom_snd p₁ J₁ g₂]
        simp [eJ, pJ]
      obtain ⟨ZJ, hJstart, hJend, hJmono, hJstrata⟩ :=
        transportSmoothFiltrationIso eJ.symm (pullback.snd pJ g₂)
          (J₂.subschemeι ≫ p₂) heJ t Z' hstart hend hmono hstrata
      have hIJ : I₁ ≤ J₁ := le_map_subschemeι I₁ R
      have hU₁ : (U₁ : Set I₁.subscheme) =
          {x | I₁.subschemeι x ∉ J₁.support} := by
        ext x
        show x ∈ U₁ ↔ I₁.subschemeι x ∉ (R.map I₁.subschemeι).support
        rw [support_map_subschemeι]
        show x ∈ U₁ ↔ I₁.subschemeι x ∉ I₁.subschemeι '' (R.support : Set _)
        rw [I₁.subschemeι.isClosedEmbedding.injective.mem_set_image]
        simp [R]
      let β := (I₁.comapIso π).hom ≫ pullback.snd π I₁.subschemeι
      let U₂ := β ⁻¹ᵁ U₁
      have hβ : β ≫ I₁.subschemeι = I₂.subschemeι ≫ π :=
        comapIso_hom_snd_comp_subschemeι I₁ π
      have hU₂ : (U₂ : Set I₂.subscheme) =
          {x | I₂.subschemeι x ∉ J₂.support} :=
        preimage_eq_compl_support_comap _ _ _ _ hβ J₁ U₁ hU₁
      have hsm₂ : Smooth (U₂.ι ≫ I₂.subschemeι ≫ p₂) :=
        smooth_open_comap p₁ I₁ g₂ U₁ hU₁smooth
      obtain ⟨Z₂, h₂start, h₂end, h₂mono, h₂strata⟩ :=
        prependSmoothFiltration p₂ I₂ J₂
          (Scheme.IdealSheafData.comap_mono π hIJ) U₂ hU₂ hsm₂
          t ZJ hJstart hJend hJmono hJstrata
      have hI₂ : I₂ = Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y₂) :=
        comap_geometricallyReduced_eq_vanishingIdeal_top p₁ I₁ (by simp [I₁]) hgeom
      let g : Spec (.of k₂) ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k k₂))
      let e : Y₂ ≅ pullback f g := iteratedBaseChangeIso f g₁ g₂ (g₂ ≫ g₁) rfl ≪≫
        pullback.congrHom rfl (specMap_algebraMap_comp k k₁ k₂)
      have he : e.hom ≫ pullback.snd f g = p₂ := by
        dsimp [e]
        rw [Category.assoc, pullback_congrHom_hom_snd]
        simpa [p₂] using iteratedBaseChangeIso_snd f g₁ g₂ (g₂ ≫ g₁) rfl
      obtain ⟨Z, hZstart, hZend, hZmono, hZstrata⟩ :=
        transportSmoothFiltrationIso e p₂ (pullback.snd f g) he (t + 1) Z₂
          (h₂start.trans hI₂) h₂end h₂mono h₂strata
      exact ⟨k₂, hk₂, inferInstance, inferInstance, inferInstance,
        t + 1, Z, hZstart, hZend, hZmono, hZstrata⟩

/- `Stacks.SmoothStrata.field_stratification_as_schemes`, in
`StacksFrontier/AlgebraicGeometry/GenericFlatness/SmoothStratification.lean`, carries exactly the
hypotheses below and is proved from this theorem rather than independently of it: it
repackages the filtration by `Y.IdealSheafData` produced here as a chain of closed immersions
`Z i ⟶ Y`, and strengthens the conclusion by asserting that each defining ideal sheaf is of
finite type, that the first closed immersion is a thickening, and that `Z (Fin.last t)` is
empty. -/
/-- A finite-type scheme over a field has a finite smooth stratification after a finite purely
inseparable extension of the field. -/
@[stacks 0H3W, ega "IV 17.15.13"]
theorem exists_finite_purelyInseparable_extension_smooth_stratification
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : Module.Finite k k') (_ : IsPurelyInseparable k k'),
      let g : Spec (.of k') ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k k'))
      let Y : Scheme.{u} := pullback f g
      let p : Y ⟶ Spec (.of k') := pullback.snd f g
      ∃ (t : ℕ) (Z : Fin (t + 1) → Y.IdealSheafData),
        Z 0 = Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y) ∧
        Z ⟨t, Nat.lt_succ_self t⟩ = ⊤ ∧
        (∀ i : Fin t, Z i.castSucc ≤ Z i.succ) ∧
        (∀ i : Fin t, ∃ U : (Z i.castSucc).subscheme.Opens,
          (U : Set (Z i.castSucc).subscheme) =
            {x | (Z i.castSucc).subschemeι x ∉ (Z i.succ).support} ∧
          Smooth (U.ι ≫ (Z i.castSucc).subschemeι ≫ p)) := by
  obtain ⟨n, hn⟩ := exists_nat_bound_topologicalKrullDim f
  exact exists_smoothStratification_of_dim_le n k f hn

end AlgebraicGeometry
