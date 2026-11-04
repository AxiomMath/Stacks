module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ConstantSheafFiniteSubgroups
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveClassKillingDefs
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic

/-!
# Reduction of a class of degree one to a finite constant class over `\bar k`

Let `K/k` be a field extension, `X` a scheme over `k`, and `F` an abelian sheaf on
`Spec(K)_étale` annihilated by a positive integer `n`. Let `Ω` be an algebraic closure of `K`.
Over `Spec Ω` the sheaf `F` becomes constant, with value a group `Γ` annihilated by `n`
(`Stacks.EtaleCohomology.SepClosedField.isIso_counit_app`), so the inverse image of `F` to
`X_Ω` is the constant sheaf `Γ`, and a class `ξ ∈ H^q(X_K, F)` restricts on `X_Ω` to a class
coming from a finite subgroup `S` of `Γ` (Tag 03Q5,
`Stacks.EtaleCohomology.exists_fg_sheafH_map_eq`). This is the first paragraph of the case
`q = 1` of the proof of [Stacks, Tag 0EYT].

## Main definitions

* `Stacks.EtaleCohomology.algebraicClosureSections` — the group `Γ` of global sections of `F`
  over `Spec Ω`.
* `Stacks.EtaleCohomology.inverseImageConstantIso` — the inverse image of `F` to `X_Ω` is the
  constant sheaf `Γ`.

## Main results

* `Stacks.EtaleCohomology.exists_finite_constant_class` — the restriction of `ξ` to `X_Ω` comes
  from a finite subgroup `S` of `Γ`.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

variable (K) in
/-- An algebraic closure of `K`. -/
abbrev Ωbar : Type u := AlgebraicClosure K

/-- The base change `X_Ω = Spec Ω ×_{Spec K} X_K`. -/
abbrev XOmega : Scheme.{u} :=
  pullback (spectrumMap K (Ωbar K)) (pullback.fst (spectrumMap k K) f)

/-- The structure morphism `X_Ω ⟶ Spec Ω`. -/
abbrev XOmegaFst : XOmega (K := K) f ⟶ Spec (.of (Ωbar K)) := pullback.fst _ _

/-- The projection `X_Ω ⟶ X_K`. -/
abbrev XOmegaSnd : XOmega (K := K) f ⟶ pullback (spectrumMap k K) f := pullback.snd _ _

variable (K) in
/-- **The value of `F` over `Spec Ω`**: the global sections of its inverse image. -/
abbrev algebraicClosureSections
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    AddCommGrpCat.{u + 1} :=
  ((etaleAbelianInverseImage.{u, u + 1} (spectrumMap K (Ωbar K))).obj F).obj.obj
    (op (SepClosedField.terminal (Ωbar K)))

/-- **The inverse image of `F` to `X_Ω` is constant**, with value `Γ = F(Spec Ω)`. -/
def inverseImageConstantIso (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImage.{u, u + 1} (XOmegaSnd f)).obj
        ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) ≅
      (constantSheaf (XOmega (K := K) f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (algebraicClosureSections K F) :=
  (etaleAbelianInverseImageCompIso'.{u, u + 1} (XOmegaSnd f) (pullback.fst (spectrumMap k K) f)
      _ rfl).symm.app F ≪≫
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (XOmegaFst f) (spectrumMap K (Ωbar K))
      (XOmegaSnd f ≫ pullback.fst (spectrumMap k K) f) pullback.condition.symm).app F ≪≫
    (etaleAbelianInverseImage.{u, u + 1} (XOmegaFst f)).mapIso
      (asIso ((constantSheafAdj (smallEtaleTopology (Spec (.of (Ωbar K)))) AddCommGrpCat.{u + 1}
        (SepClosedField.terminalIsTerminal (Ωbar K))).counit.app _)).symm ≪≫
    (etaleAbelianInverseImageConstantIso.{u, u + 1} (XOmegaFst f)).app _

/-- Elements of the value of `F` over `Spec Ω` are killed by `n` if `n • 𝟙 F = 0`. -/
private theorem nsmul_eq_zero_algebraicClosureSections
    {F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ}
    (hF : n • 𝟙 F = 0) (x : algebraicClosureSections K F) : n • x = 0 := by
  have h := congrArg (fun φ ↦ ((sheafToPresheaf _ _).map φ).app
    (op (SepClosedField.terminal (Ωbar K)))) (nsmul_id_inverseImage_eq_zero
      (spectrumMap K (Ωbar K)) hF)
  simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero,
    NatTrans.app_nsmul, NatTrans.id_app, NatTrans.app_zero] at h
  simpa using congrArg (fun φ ↦ φ x) h

/-- The value of `F` over `Spec Ω` is annihilated by `n` if `F` is. -/
theorem isTorsion_algebraicClosureSections
    {F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) : IsAddTorsion (algebraicClosureSections K F) := fun x =>
  (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨n, hn, nsmul_eq_zero_algebraicClosureSections hF x⟩

/-- **The restriction of a class to `X_Ω` comes from a finite constant sheaf.** If `F` is
annihilated by `n > 0` and `X_K` is quasi-compact and quasi-separated, then for every class
`ξ ∈ H^q(X_K, F)` there are a finite subgroup `S` of `Γ = F(Spec Ω)` and a class
`ζ ∈ H^q(X_Ω, S)` whose image under `S ⊆ Γ` and the identification of the constant sheaf `Γ` with
the inverse image of `F` is the restriction of `ξ` to `X_Ω`. -/
theorem exists_finite_constant_class [CompactSpace ↥(pullback (spectrumMap k K) f)]
    [QuasiSeparatedSpace ↥(pullback (spectrumMap k K) f)]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) {q : ℕ}
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q) :
    ∃ (S : AddSubgroup (algebraicClosureSections K F)) (_ : Finite S)
      (ζ : Sheaf.H.{u + 1, u + 1}
        ((constantSheaf (XOmega (K := K) f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of S)) q),
      Sheaf.H.map ((constantSheaf _ AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom S.subtype) ≫
          (inverseImageConstantIso f F).inv) q ζ =
        etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (XOmegaSnd f) _ q ξ := by
  have : CompactSpace (XOmega (K := K) f) :=
    compactSpace_pullback_spectrumMap (pullback.fst (spectrumMap k K) f) (Ωbar K)
  have : QuasiSeparatedSpace (XOmega (K := K) f) :=
    quasiSeparatedSpace_pullback_spectrumMap (pullback.fst (spectrumMap k K) f) (Ωbar K)
  obtain ⟨S, hS, ζ, hζ⟩ := exists_fg_sheafH_map_eq (Y := XOmega (K := K) f)
    (algebraicClosureSections K F) q
    (Sheaf.H.map (inverseImageConstantIso f F).hom q
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (XOmegaSnd f) _ q ξ))
  refine ⟨S, finite_of_fg_of_isTorsion (isTorsion_algebraicClosureSections hn hF) S hS, ζ, ?_⟩
  rw [Sheaf.H.map_comp_apply, hζ, ← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]

/-! ### Descent to the algebraic closure of `k` -/

/-- An integer invertible in a field is coprime to its exponential characteristic. -/
private theorem coprime_ringExpChar_of_isUnit {L : Type*} [Field L] {n : ℕ} (hn : IsUnit (n : L)) :
    n.Coprime (ringExpChar L) := by
  have hq : ExpChar L (ringExpChar L) := ringExpChar.of_eq rfl
  generalize ringExpChar L = q at hq ⊢
  obtain _ | ⟨hp⟩ := hq
  · exact Nat.coprime_one_right n
  · refine (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_))
    have : ((n : ℕ) : L) = 0 := (CharP.cast_eq_zero_iff L q n).2 hdvd
    exact hn.ne_zero this

variable (k K) in
/-- The algebraic closure `ar k` of `k` inside `Ω`. -/
abbrev kbar : IntermediateField k (Ωbar K) := algebraicClosure k (Ωbar K)

/-- The algebraic closure of `k` inside `Ω` is algebraically closed. -/
instance : IsAlgClosed (kbar k K) := IsAlgClosure.isAlgClosed k

/-- The base change `X_{ar k} = Spec ar k ×_{Spec k} X`. -/
abbrev Xkbar : Scheme.{u} := pullback (spectrumMap k (kbar k K)) f

/-- The comparison morphism `X_Ω ⟶ X_{ar k}`. -/
def XOmegaToXkbar : XOmega (K := K) f ⟶ Xkbar (K := K) f :=
  pullback.lift (XOmegaFst f ≫ spectrumMap (kbar k K) (Ωbar K)) (XOmegaSnd f ≫ pullback.snd _ _)
    (by
      rw [Category.assoc, spectrumMap_comp_spectrumMap k (kbar k K) (Ωbar K),
        ← spectrumMap_comp_spectrumMap k K (Ωbar K), ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, pullback.condition])

/-- The first component of `XOmegaToXkbar f` is the projection `X_Ω ⟶ Spec Ω` followed by the
map `Spec Ω ⟶ Spec (kbar k K)`. -/
theorem XOmegaToXkbar_fst : XOmegaToXkbar (K := K) f ≫ pullback.fst _ _ =
    XOmegaFst (K := K) f ≫ spectrumMap (kbar k K) (Ωbar K) := pullback.lift_fst _ _ _

/-- The second component of `XOmegaToXkbar f` is the projection `X_Ω ⟶ X_K` followed by the
projection `X_K ⟶ X`. -/
theorem XOmegaToXkbar_snd : XOmegaToXkbar (K := K) f ≫ pullback.snd _ _ =
    XOmegaSnd (K := K) f ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

/-- `X_Ω` is the base change of `X_{ar k}` along `ar k ⊆ Ω`. -/
theorem isPullback_XOmegaToXkbar :
    IsPullback (XOmegaToXkbar (K := K) f) (XOmegaFst (K := K) f)
      (pullback.fst (spectrumMap k (kbar k K)) f)
      (spectrumMap (kbar k K) (Ωbar K)) := by
  have hK := (IsPullback.of_hasPullback (spectrumMap K (Ωbar K))
    (pullback.fst (spectrumMap k K) f)).flip.paste_horiz
      (IsPullback.of_hasPullback (spectrumMap k K) f).flip
  rw [spectrumMap_comp_spectrumMap k K (Ωbar K),
    ← spectrumMap_comp_spectrumMap k (kbar k K) (Ωbar K), ← XOmegaToXkbar_snd] at hK
  exact IsPullback.of_right hK (XOmegaToXkbar_fst f)
    (IsPullback.of_hasPullback (spectrumMap k (kbar k K)) f).flip

section MapTo

variable {X₁ X₂ X₃ : Scheme.{u}}

/-- **Restriction along a composite is restriction along the factors**, in the form of the
cohomology map attached to a morphism and a map of sheaves. -/
theorem etaleCohomologyMapTo_eq_comp_restriction (k₁ : X₃ ⟶ X₂) (k₂ : X₂ ⟶ X₁) (k : X₃ ⟶ X₁)
    (hk : k = k₁ ≫ k₂) {A : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {C : Sheaf X₃.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ C) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k w p x = etaleCohomologyMapTo k₁
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} k₁ k₂ k hk).inv.app A ≫ w) p
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p x) := by
  rw [← etaleCohomologyMapTo_id k₂ A p x, etaleCohomologyMapTo_comp k₁ k₂ k hk (𝟙 _) _ w
    (by simp)]

/-- The cohomology map of a morphism and a map of sheaves, on the image of a map of sheaves. -/
theorem etaleCohomologyMapTo_sheafH_map (k : X₂ ⟶ X₁)
    {A B : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : A ⟶ B)
    {C : Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj B ⟶ C) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k w p (Sheaf.H.map φ p x) =
      etaleCohomologyMapTo k ((etaleAbelianInverseImage.{u, u + 1} k).map φ ≫ w) p x := by
  rw [etaleCohomologyMapTo_apply, etaleCohomologyMapTo_apply, Sheaf.H.map_apply,
    etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1},
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

end MapTo

/-- **The restriction of a class to `X_Ω` comes from a finite constant class on `X_{ar k}`.**
Let `X` be an affine curve over `k` and `F` an abelian sheaf on `Spec(K)_étale` annihilated by an
integer `n` invertible in `k`. For every `ξ ∈ H^1(X_K, F)` there are a finite abelian group `S`
annihilated by `n`, a class `ζ ∈ H^1(X_{ar k}, S)` and a map of sheaves on `X_Ω` from the
inverse image of the constant sheaf `S` to that of `F`, carrying the restriction of `ζ` to the
restriction of `ξ`. This uses Theorem 03SC (6) for `X_{ar k}` (Tag 0A58), with `Ω/ar k` an
extension of algebraically closed fields. -/
theorem exists_kbar_class [IsCurve k f] [IsAffine X]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn0 : 0 < n)
    (hn : IsUnit (n : k)) (hF : n • 𝟙 F = 0) {q : ℕ}
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q) :
    ∃ (S : AddCommGrpCat.{u + 1}) (_ : Finite S) (_ : n • 𝟙 S = 0)
      (ζ : Sheaf.H.{u + 1, u + 1}
        ((constantSheaf (Xkbar (K := K) f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj S) q)
      (ψ : (etaleAbelianInverseImage.{u, u + 1} (XOmegaToXkbar (K := K) f)).obj
          ((constantSheaf _ AddCommGrpCat.{u + 1}).obj S) ⟶
        (etaleAbelianInverseImage.{u, u + 1} (XOmegaSnd (K := K) f)).obj
          ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F)),
      Sheaf.H.map ψ q (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
          (XOmegaToXkbar (K := K) f) _ q ζ) =
        etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (XOmegaSnd (K := K) f) _ q ξ := by
  obtain ⟨S, hS, ζ', hζ'⟩ := exists_finite_constant_class f F hn0 hF ξ
  let Sab := AddCommGrpCat.of S
  have hy : ∀ y : S, n • y = 0 := fun y =>
    Subtype.ext (by simpa using nsmul_eq_zero_algebraicClosureSections hF y.1)
  have hSn : n • 𝟙 Sab = 0 := by
    ext x
    simpa using hy x
  have hconst : n • 𝟙 ((constantSheaf (Xkbar (K := K) f).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj Sab) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hSn, Functor.map_zero]
  have hdim : topologicalKrullDim ↥(Xkbar (K := K) f) ≤ 1 := by
    rw [topologicalKrullDim_baseChange k (kbar k K) (pullback.snd _ _) (pullback.fst _ _) f
      (IsPullback.of_hasPullback _ _).flip]
    exact (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  let S0 : TorsionSheafSituation.{u, 0} :=
    { k := kbar k K
      X := Xkbar (K := K) f
      structureMorphism := pullback.fst _ _
      dimension_le_one := hdim
      F := (constantSheaf _ AddCommGrpCat.{u + 1}).obj Sab
      isTorsion := torsionSheafProperty_of_pos_nsmul_id_eq_zero hn0 hconst }
  have hnk : IsUnit (n : kbar k K) := by simpa using hn.map (algebraMap k (kbar k K))
  have hbij := S0.baseChangePrimeToCharacteristic
    (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hn0 (coprime_ringExpChar_of_isUnit hnk)
      hconst) (Ωbar K) q
  -- restriction along `X_Ω ⟶ X_{\bar k}` is surjective
  let hpb := isPullback_XOmegaToXkbar (K := K) f
  have hφ : hpb.isoPullback.hom ≫ pullback.fst _ _ = XOmegaToXkbar (K := K) f :=
    hpb.isoPullback_hom_fst
  have hsurj : Function.Surjective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (XOmegaToXkbar (K := K) f) ((constantSheaf _ AddCommGrpCat.{u + 1}).obj Sab) q) := by
    intro y
    have := universalHomeomorphism_of_isIso hpb.isoPullback.hom
    have hiso := etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, u + 1, u + 1}
      hpb.isoPullback.hom ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst _ _)).obj
        ((constantSheaf _ AddCommGrpCat.{u + 1}).obj Sab)) q
    let c := (etaleAbelianInverseImageCompIso'.{u, u + 1} hpb.isoPullback.hom (pullback.fst _ _)
      _ hφ.symm).app ((constantSheaf _ AddCommGrpCat.{u + 1}).obj Sab)
    obtain ⟨z, hz⟩ := hiso.2 (Sheaf.H.map c.hom q y)
    obtain ⟨x, hx⟩ := hbij.2 z
    refine ⟨x, ?_⟩
    rw [← etaleCohomologyMapTo_id, etaleCohomologyMapTo_eq_comp_restriction _ _ _ hφ.symm,
      Category.comp_id, etaleCohomologyMapTo_apply]
    change (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} hpb.isoPullback.hom _ q
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.fst _ _) _ q x)).comp
        (Abelian.Ext.mk₀ c.inv) (add_zero q) = y
    rw [show etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.fst _ _) _ q x = z from hx,
      hz]
    change Sheaf.H.map c.inv q (Sheaf.H.map c.hom q y) = y
    rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
  let cr := (etaleAbelianInverseImageConstantIso.{u, u + 1} (XOmegaToXkbar (K := K) f)).app Sab
  obtain ⟨ζ, hζ⟩ := hsurj (Sheaf.H.map cr.inv q ζ')
  refine ⟨Sab, hS, hSn, ζ, cr.hom ≫ (constantSheaf _ AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.ofHom S.subtype) ≫ (inverseImageConstantIso f F).inv, ?_⟩
  rw [hζ, ← Sheaf.H.map_comp_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, hζ']

end Stacks.EtaleCohomology

end
