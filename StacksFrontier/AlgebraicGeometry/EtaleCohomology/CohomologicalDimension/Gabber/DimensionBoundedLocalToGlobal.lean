module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.LocalSectionsAtPointProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.PuncturedStalkBaseChange

/-!
# Exposé XVIII-A, Lemma 2.2, in bounded dimension

Travaux de Gabber, Exposé XVIII-A, Lemma 2.2 bounds the cohomology of a Noetherian scheme `X` by
`sup_x (c(x) + 2 dim 𝒪_{X,x})`, from bounds `c(x)` for its residue fields. Its proof uses the
punctured bound of Lemma 2.1 only for the strict henselizations of the local rings of `X`, whose
dimension is at most that of the local ring (Stacks 06LK). So the punctured bound for local rings
of dimension at most `D` gives Lemma 2.2 for every Noetherian `X` all of whose local rings have
dimension at most `D`. This is the form used in the proof by induction on the dimension of the
punctured bound itself
(`AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`),
where `X` is the punctured spectrum of a local ring of dimension `D + 1`.

The proofs are those of
`AlgebraicGeometry.Scheme.puncturedStalkVanishing_of_puncturedSpectrumVanishingBound`,
`AlgebraicGeometry.Scheme.genericPointSupportKilling_of_localInputs` and
`AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_of_genericPointSupportKilling`, with the
dimension hypothesis carried along.

## Main definitions

* `AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBoundUpTo n D`: the punctured bound for
  strictly henselian Noetherian local rings of dimension `1 ≤ d ≤ D`.
* `AlgebraicGeometry.Scheme.PuncturedStalkVanishingUpTo n D` and
  `AlgebraicGeometry.Scheme.GenericPointSupportKillingUpTo n D`: the punctured input and the local
  killing statement of the dévissage, at points `η` with `dim 𝒪_{X,η} ≤ D`.

## Main results

* `AlgebraicGeometry.Scheme.puncturedStalkVanishingUpTo_of_puncturedSpectrumVanishingBoundUpTo`
* `AlgebraicGeometry.Scheme.genericPointSupportKillingUpTo_of_puncturedStalkVanishingUpTo`
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_of_puncturedSpectrumVanishingBoundUpTo`:
  Lemma 2.2 for Noetherian schemes whose local rings have dimension at most `D`.

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Lemmas 2.1 and 2.2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 06LK](https://stacks.math.columbia.edu/tag/06LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Exposé XVIII-A, Lemma 2.1, up to dimension `D`**: for every strictly henselian Noetherian
local ring `A` of dimension `d` with `1 ≤ d ≤ D` in which `n` is invertible, the punctured
spectrum of `A` has étale cohomology with coefficients killed by `n` vanishing above `2d - 1`. -/
def PuncturedSpectrumVanishingBoundUpTo (n D : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [StrictlyHenselianLocalRing A] (d : ℕ),
    ringKrullDim A = d → 0 < d → d ≤ D → IsUnit (n : A) →
      IsTorsionVanishingBound (Stacks.puncturedSpectrum A).toScheme n ((2 * d - 1 : ℕ) : WithBot ℕ∞)

/-- The punctured bound in every dimension gives it up to every dimension. -/
theorem PuncturedSpectrumVanishingBound.upTo {n : ℕ} (h : PuncturedSpectrumVanishingBound.{u} n)
    (D : ℕ) : PuncturedSpectrumVanishingBoundUpTo.{u} n D :=
  fun A _ _ _ d hd hpos _ hn => h A d hd hpos hn

/-- **The punctured input at points of dimension at most `D`**: as
`AlgebraicGeometry.Scheme.PuncturedStalkVanishing`, for maximal points `η` of `X ∖ U` with
`dim 𝒪_{X,η} ≤ D`. -/
def PuncturedStalkVanishingUpTo (n D : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], IsUnit (n : Γ(X, ⊤)) →
    ∀ (U : X.Opens) (η : X), η ∉ U → (∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) →
      ringKrullDim (X.presheaf.stalk η) ≤ D →
      ∀ G : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1},
        (∀ (T : U.toScheme.Etale) (x : G.obj.obj (op T)), n • x = 0) →
          ∀ m : ℕ, 2 * ringKrullDim (X.presheaf.stalk η) ≤ m →
            ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) = η →
              IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj
                (((Stacks.EtaleCohomology.smallEtalePushforwardAb U.ι).rightDerived m).obj G))

/-- **The local killing statement at points of dimension at most `D`**: as
`AlgebraicGeometry.Scheme.GenericPointSupportKilling`, for maximal points `η` of `X ∖ U` with
`dim 𝒪_{X,η} ≤ D`. -/
def GenericPointSupportKillingUpTo (n D : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], IsUnit (n : Γ(X, ⊤)) →
    ∀ (U : X.Opens) (η : X), η ∉ U → (∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) →
      ringKrullDim (X.presheaf.stalk η) ≤ D →
      ∀ c : WithBot ℕ∞, IsTorsionVanishingBound (Spec (.of (X.residueField η))) n c →
        ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          (∀ (T : X.Etale) (x : F.obj.obj (op T)), n • x = 0) →
            ∀ i : ℕ, c + 2 * ringKrullDim (X.presheaf.stalk η) < i →
              ∀ ξ : ((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F,
                ∃ V : X.Opens, η ∈ V ∧
                  (NatTrans.rightDerived (opensSupportRestrict (le_top : U ≤ ⊤)
                    (inf_le_left : V ⊓ U ≤ V) le_top inf_le_right) i).app F ξ = 0

variable {n : ℕ}

/-- **The punctured bound at the strict henselization, up to dimension `D`.** As
`AlgebraicGeometry.Scheme.exists_isTorsionVanishingBound_puncturedSpectrum_etaleLocalRing`, when
the local ring at the image of `s` has dimension at most `D`: the strict henselization then has
dimension at most `D` (Stacks 06LK). -/
theorem exists_isTorsionVanishingBound_puncturedSpectrum_etaleLocalRing_of_le {D : ℕ}
    (h : PuncturedSpectrumVanishingBoundUpTo.{u} n D) (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (hS : B.Contains X) (s : GeometricPoint X)
    [IsNoetherianRing ↥(X.presheaf.stalk (s.hom (closedPoint s.residueField)))]
    (hD : ringKrullDim ↥(X.presheaf.stalk (s.hom (closedPoint s.residueField))) ≤ D)
    (hn : IsUnit (n : ↥(etaleLocalRing B X hS s))) (m : ℕ)
    (hm : 2 * ringKrullDim ↥(X.presheaf.stalk (s.hom (closedPoint s.residueField))) ≤ m) :
    ∃ d : WithBot ℕ∞, d < m ∧
      IsTorsionVanishingBound (Stacks.puncturedSpectrum ↥(etaleLocalRing B X hS s)).toScheme n
        d := by
  have := isNoetherianRing_etaleLocalRing_of_stalk B hS s
  have := etaleLocalRing_strictHenselian B X hS s
  have hdim := ringKrullDim_etaleLocalRing_le_stalk B hS s
  have h2 : 2 * ringKrullDim ↥(etaleLocalRing B X hS s) ≤ m :=
    (mul_le_mul_of_nonneg_left hdim (by norm_num)).trans hm
  have hdD : ringKrullDim ↥(etaleLocalRing B X hS s) ≤ D := hdim.trans hD
  have hnn : 0 ≤ ringKrullDim ↥(etaleLocalRing B X hS s) := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim ↥(etaleLocalRing B X hS s) = d := by
    revert hdD hnn
    generalize ringKrullDim ↥(etaleLocalRing B X hS s) = δ
    intro hdD hnn
    induction δ using WithBot.recBotCoe with
    | bot => exact absurd hnn (not_le.2 (WithBot.bot_lt_coe _))
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd hdD (not_le.2 (by exact_mod_cast ENat.natCast_lt_top D))
      | coe d => exact ⟨d, rfl⟩
  rw [hd] at h2 hdD
  have h2' : 2 * d ≤ m := by exact_mod_cast h2
  have hdD' : d ≤ D := by exact_mod_cast hdD
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    exact ⟨⊥, WithBot.bot_lt_coe _,
      isTorsionVanishingBound_puncturedSpectrum_of_ringKrullDim_eq_zero _ (by exact_mod_cast hd)⟩
  · refine ⟨((2 * d - 1 : ℕ) : WithBot ℕ∞), by exact_mod_cast (by omega : 2 * d - 1 < m), ?_⟩
    exact h _ d hd hdpos hdD' hn

/-- **The punctured input up to dimension `D`, from the punctured bound up to dimension `D`.**
The proof of `AlgebraicGeometry.Scheme.puncturedStalkVanishing_of_puncturedSpectrumVanishingBound`:
the stalk of `R^m j_* 𝓖` at `s` is the cohomology of the punctured spectrum of `𝒪^{sh}_{X,s}`
(Stacks 03Q9), whose dimension is at most `dim 𝒪_{X,η} ≤ D`. -/
theorem puncturedStalkVanishingUpTo_of_puncturedSpectrumVanishingBoundUpTo {D : ℕ}
    (h : PuncturedSpectrumVanishingBoundUpTo.{u} n D) : PuncturedStalkVanishingUpTo.{u} n D := by
  intro X _ hn U η hηU hmax hD G hG m hm s hs
  rw [← hs] at hηU hmax hm hD
  let B := BigEtaleSite.containing X
  have hS : B.Contains X := BigEtaleSite.contains_containing _
  -- instance search for these goals wanders off in the present import closure
  have : QuasiCompact U.ι := @instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion X U.toScheme
    IsNoetherian.toIsLocallyNoetherian U.ι (Scheme.Opens.instIsOpenImmersionι U)
  have : QuasiSeparated U.ι := @IsSeparated.instQuasiSeparated _ _ U.ι
    (@IsSeparated.isSeparated_of_mono _ _ U.ι
      (@IsOpenImmersion.mono _ _ U.ι (Scheme.Opens.instIsOpenImmersionι U)))
  have : IsNoetherianRing ↥(X.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    @instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian X
      IsNoetherian.toIsLocallyNoetherian _
  refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS U.ι s G m).2 ?_
  have hnO : IsUnit (n : ↥(etaleLocalRing B X hS s)) := by
    have := hn.map ((structureSheafStalkFromLocalRing B X hS s).comp
      (X.presheaf.germ ⊤ (s.hom (closedPoint s.residueField)) trivial).hom)
    rwa [map_natCast] at this
  obtain ⟨d, hdm, hb⟩ :=
    exists_isTorsionVanishingBound_puncturedSpectrum_etaleLocalRing_of_le h B hS s hD hnO m hm
  have hb' : IsTorsionVanishingBound (strictHenselizationBaseChange B hS U.ι s) n d :=
    IsTorsionVanishingBound.of_iso
      (strictHenselizationBaseChangeOpensιIsoPuncturedSpectrum B hS s U hηU hmax) hb
  have hG' : ∀ (T : (strictHenselizationBaseChange B hS U.ι s).Etale)
      (x : ((etaleAbelianInverseImage.{u, 0} (strictHenselizationBaseChangeToSource B hS U.ι s)).obj
        G).obj.obj (op T)), n • x = 0 :=
    forall_nsmul_eq_zero_etaleAbelianInverseImage _ hG
  have hH : Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (strictHenselizationBaseChangeToSource B hS U.ι s)).obj G)
      m) := hb' _ hG' m hdm
  exact (subsingleton_H_iff_of_iso
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage
      (strictHenselizationBaseChangeToSource B hS U.ι s)).app G) m).2 hH

/-- **The local killing statement up to dimension `D`**, from the punctured input up to
dimension `D` and the local-sections input (`AlgebraicGeometry.Scheme.localSectionsAtPoint`).
The proof of `AlgebraicGeometry.Scheme.genericPointSupportKilling_of_localInputs`. -/
theorem genericPointSupportKillingUpTo_of_puncturedStalkVanishingUpTo {D : ℕ}
    (h₁ : PuncturedStalkVanishingUpTo.{u} n D) : GenericPointSupportKillingUpTo.{u} n D := by
  intro X _ hn U η hηU hmax hD c hc F hF i hi ξ
  obtain ⟨D'⟩ := localSectionsAtPoint n X hn U η hηU hmax c hc
  let 𝒦 := supportedSubsheaf U
  let δ := ringKrullDim (X.presheaf.stalk η)
  have hδ : 0 ≤ 2 * δ := mul_nonneg (by norm_num) ringKrullDim_nonneg_of_nontrivial
  -- the vanishing of `R^i(Ψ ∘ 𝒦_U)(𝓕)`
  have hvan : IsZero (((𝒦 ⋙ D'.Ψ).rightDerived i).obj F) := by
    refine Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero 𝒦 D'.Ψ F i
      fun q hq => ?_
    let G := (𝒦.rightDerived q).obj F
    have hGn : ∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0 :=
      (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero G).2 (nsmul_id_obj_eq_zero (𝒦.rightDerived q)
        ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF))
    have hGU : ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∈ U →
        IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj G) := fun s hs =>
      isZero_stalk_rightDerived_supportedSubsheaf_of_mem U F q s.hom hs
    by_cases hq' : 2 * δ < (q : WithBot ℕ∞)
    · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := by
        rcases q with _ | m
        · exact absurd hq' (not_lt.2 (by simpa using hδ))
        · exact ⟨m, rfl⟩
      refine D'.vanish' G (fun s hs => ?_) _
      rcases hs with hs | hs
      · exact hGU s hs
      · refine isZero_stalk_rightDerived_supportedSubsheaf_succ U F m s.hom ?_
        exact h₁ X hn U η hηU hmax hD _ (fun T x => hF _ x) m
          (le_natCast_of_lt_natCast_succ hq') s hs
    · exact D'.vanish G hGn hGU _ (lt_natCast_sub_of_add_lt hi (not_lt.1 hq'))
  exact exists_opensSupport_eq_zero_of_isZero U η D' F i hvan ξ

/-- **Exposé XVIII-A, Lemma 2.2, with supports, up to dimension `D`**: on a Noetherian scheme all
of whose local rings have dimension at most `D`, `H^i_{X∖U}(X, 𝓕) = 0` as soon as
`i > sup_{t ∉ U} (c(t) + 2 dim 𝒪_{X,t})`. The Noetherian induction of
`AlgebraicGeometry.Scheme.isZero_rightDerived_opensSupport_of_genericPointSupportKilling`. -/
theorem isZero_rightDerived_opensSupport_of_genericPointSupportKillingUpTo {D : ℕ}
    (h : GenericPointSupportKillingUpTo.{u} n D) (X : Scheme.{u}) [IsNoetherian X]
    (hn : IsUnit (n : Γ(X, ⊤))) (hD : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ D)
    (c : X → WithBot ℕ∞)
    (hc : ∀ x, IsTorsionVanishingBound (Spec (.of (X.residueField x))) n (c x))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (T : X.Etale) (x : F.obj.obj (op T)), n • x = 0) (U : X.Opens) :
    ∀ i : ℕ, (⨆ (x : X) (_ : x ∉ U), (c x + 2 * ringKrullDim (X.presheaf.stalk x))) < i →
      IsZero (((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F) := by
  induction U using WellFoundedGT.induction with
  | ind U ih =>
  intro i hi
  by_cases hU : U = ⊤
  · subst hU
    exact isZero_rightDerived_opensSupport_self ⊤ F i
  obtain ⟨η, hηT, hηmax⟩ := exists_mem_forall_mem_closure_eq (T := ((U : Set X)ᶜ))
    U.isOpen.isClosed_compl (by
      by_contra hne
      exact hU (Opens.ext (Set.compl_empty_iff.1 (Set.not_nonempty_iff_eq_empty.1 hne))))
  have hb : c η + 2 * ringKrullDim (X.presheaf.stalk η) < i :=
    (le_iSup₂ η hηT).trans_lt hi
  suffices hξ : ∀ ξ : ((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F, ξ = 0 by
    have : Subsingleton (((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F) :=
      ⟨fun a b => (hξ a).trans (hξ b).symm⟩
    exact AddCommGrpCat.isZero_of_subsingleton _
  intro ξ
  obtain ⟨V, hηV, hV⟩ := h X hn U η hηT (fun x hx hxU => hηmax x hxU hx) (hD η) (c η) (hc η) F
    hF i hb ξ
  have hlt : U < U ⊔ V := by
    refine lt_of_le_of_ne le_sup_left fun he => hηT ?_
    rw [he]
    exact (le_sup_right : V ≤ U ⊔ V) hηV
  have hi' : (⨆ (x : X) (_ : x ∉ U ⊔ V), (c x + 2 * ringKrullDim (X.presheaf.stalk x))) < i :=
    (iSup₂_le fun x hx =>
      le_iSup₂_of_le x (fun hxU => hx ((le_sup_left : U ≤ U ⊔ V) hxU)) le_rfl).trans_lt hi
  have hzero := ih (U ⊔ V) hlt i hi'
  have hcomp := opensSupportRestrict_comp (le_top : U ≤ ⊤) (le_sup_left : U ≤ U ⊔ V)
    (inf_le_left : V ⊓ U ≤ V) (le_top : U ⊔ V ≤ ⊤) (le_refl U) (le_sup_right : V ≤ U ⊔ V)
    (inf_le_right : V ⊓ U ≤ U)
  have h2 : (NatTrans.rightDerived (opensSupportRestrict (le_top : U ≤ ⊤)
      (le_sup_left : U ≤ U ⊔ V) (le_top : U ⊔ V ≤ ⊤) (le_refl U)) i).app F ξ = 0 := by
    have hiso : IsIso ((NatTrans.rightDerived (opensSupportRestrict (le_sup_left : U ≤ U ⊔ V)
        (inf_le_left : V ⊓ U ≤ V) (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U)) i).app
          F) :=
      Iso.isIso_hom ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
        (asIso (opensSupportRestrict (le_sup_left : U ≤ U ⊔ V) (inf_le_left : V ⊓ U ≤ V)
          (le_sup_right : V ≤ U ⊔ V) (inf_le_right : V ⊓ U ≤ U))) i).app F)
    refine ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1 ?_
    rwa [map_zero, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← NatTrans.rightDerived_comp, hcomp]
  obtain ⟨y, hy⟩ := exists_rightDerived_opensSupportRestrict_eq (le_sup_left : U ≤ U ⊔ V)
    (le_top : U ⊔ V ≤ ⊤) F i ξ h2
  rw [← hy, (AddCommGrpCat.subsingleton_of_isZero hzero).elim y 0, map_zero]

/-- **Exposé XVIII-A, Lemma 2.2, up to dimension `D`.** Granting the punctured bound for strictly
henselian Noetherian local rings of dimension at most `D`, every Noetherian scheme `X` on which
`n` is invertible and all of whose local rings have dimension at most `D` has étale cohomology
with coefficients killed by `n` vanishing above `sup_x (c(x) + 2 dim 𝒪_{X,x})`, for bounds `c(x)`
of the residue fields. -/
theorem isTorsionVanishingBound_of_puncturedSpectrumVanishingBoundUpTo {D : ℕ}
    (h : PuncturedSpectrumVanishingBoundUpTo.{u} n D) (X : Scheme.{u}) [IsNoetherian X]
    (hn : IsUnit (n : Γ(X, ⊤))) (hD : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ D)
    (c : X → WithBot ℕ∞)
    (hc : ∀ x, IsTorsionVanishingBound (Spec (.of (X.residueField x))) n (c x)) :
    IsTorsionVanishingBound X n (⨆ x : X, (c x + 2 * ringKrullDim (X.presheaf.stalk x))) := by
  intro G hG p hp
  apply subsingleton_sheafH_of_isZero_rightDerived_opensSupport_bot
  refine isZero_rightDerived_opensSupport_of_genericPointSupportKillingUpTo
    (genericPointSupportKillingUpTo_of_puncturedStalkVanishingUpTo
      (puncturedStalkVanishingUpTo_of_puncturedSpectrumVanishingBoundUpTo h))
    X hn hD c hc G hG ⊥ p ?_
  exact lt_of_le_of_lt (iSup₂_le fun x _ => le_iSup (fun x : X =>
    c x + 2 * ringKrullDim (X.presheaf.stalk x)) x) hp

end AlgebraicGeometry.Scheme

end
