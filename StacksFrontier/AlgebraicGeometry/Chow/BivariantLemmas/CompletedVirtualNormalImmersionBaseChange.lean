module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionOfComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalRestrictionExcess

/-!
# Base change of the class of a virtual normal bundle for an immersion, at arbitrary rank

Stacks 0FBQ (3) attaches to a virtual normal bundle `𝒩` of arbitrary rank for an immersion
`i : Z ⟶ X` the class `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* ∈ A^*(Z ⟶ X)^∧`
(`Stacks.Chow.completedVirtualNormalGysinClassOfOpen`), and says that all the lemmas on the class
of a closed immersion have immediate counterparts. This file gives the counterparts of the
base-change clause of Stacks 0FBK and of Stacks 0FV7 in `A^*(Z ⟶ X)^∧`.

## Main results

* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_cap_baseChange` — on cap operations, degree
  by degree: `c(Z' ⟶ X', g^*𝒩)` caps on `t : T ⟶ X'` as `c(Z ⟶ X, 𝒩)` does on `t ≫ f`.
* `Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen`,
  `Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClassOfImmersion` — the
  same for the chosen fibre product `Z ×_X X'`.
* `Stacks.Chow.completedVirtualNormalGysinRestrictionOfOpen_eq_of_isTopChernComposition` — the
  counterpart of Stacks 0FV7: `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`.

The counterpart of the base-change clause of Stacks 0FBK, for a cartesian square of immersions, is
`completedBivariantTransport_completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen`
(in the namespace `Stacks.Chow`): the restriction of `c(Z ⟶ X, 𝒩)` along `X' ⟶ X` is
`c(Z' ⟶ X', g^*𝒩)`.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)
  (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hU : i' ≫ U.ι = i)

/-! ### The counterpart of the base-change clause of Stacks 0FBK -/

section BaseChange

variable {X' Z' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f] (i₂ : Z' ⟶ X') [IsImmersion i₂]
  (g' : Z' ⟶ Z) (sq : IsPullback i₂ g' f i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
  (hi₂ : i₂ ≫ (f ≫ sX) = sZ') (𝒩 : VirtualNormalBundle i)

/-- **The completed class of `g^*𝒩` on `f⁻¹(U)`, as a base change of that on `U`.** For a
cartesian square `Z' = Z ×_X X'` of immersions and a closed factor `iW : Z' ⟶ f⁻¹(U)` of
`Z' ⟶ X'`, the degree-`n` part of `c(Z' ⟶ f⁻¹(U), g^*𝒩)` caps on a test scheme `t'` as the
degree-`n` part of `c(Z ⟶ U, 𝒩)` does on `t' ≫ (f⁻¹(U) ⟶ U)`. -/
theorem completedVirtualNormalGysinClass_toOpenFactor_baseChange_cap
    (iW : Z' ⟶ (f ⁻¹ᵁ U).toScheme) [IsClosedImmersion iW] (hW : iW ≫ (f ⁻¹ᵁ U).ι = i₂)
    (sqW : IsPullback iW g' (f ∣_ U) i') (hiW' : iW ≫ (f ∣_ U ≫ (U.ι ≫ sX)) = sZ') (n : ℤ)
    {T : Scheme.{u}} (t' : T ⟶ (f ⁻¹ᵁ U).toScheme) [LocallyOfFiniteType t'] (k : ℤ)
    (a : chowGroup C (t' ≫ ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX))) k) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
    haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    haveI : IsLocallyNoetherian (f ⁻¹ᵁ U).toScheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX))
    (completedBivariantSequenceOfInvertible C sZ' ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) iW
        (by rw [← Category.assoc, hW, hi₂])
        (completedVirtualNormalGysinClass C sZ' ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) iW
          (by rw [← Category.assoc, hW, hi₂]) ((𝒩.baseChange i i₂ g' f sq).toOpenFactor hW)) n).cap
        t' k a =
      chowPushforwardOfIso C (pullback.fst i' (t' ≫ f ∣_ U) ≫ sZ) (pullback.fst iW t' ≫ sZ')
        (subschemeTestBaseChangeIso i' iW g' (f ∣_ U) sqW t').hom
        (by rw [← hiW', ← openFactor_comp_structureMorphism C sZ sX i hi hU]
            exact subschemeTestBaseChangeIso_hom_comp_structure i' iW g' (f ∣_ U) sqW t'
              (U.ι ≫ sX))
        (k - n)
        ((completedBivariantSequenceOfInvertible C sZ (U.ι ≫ sX) i'
            (openFactor_comp_structureMorphism C sZ sX i hi hU)
            (completedVirtualNormalGysinClass C sZ (U.ι ≫ sX) i'
              (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU)) n).cap
          (t' ≫ f ∣_ U) k
          (chowGroupCongr C (by rw [Category.assoc, morphismRestrict_ι_assoc]) k a)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  have : IsLocallyNoetherian (f ⁻¹ᵁ U).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX))
  have hiW : iW ≫ ((f ⁻¹ᵁ U).ι ≫ (f ≫ sX)) = sZ' := by rw [← Category.assoc, hW, hi₂]
  have hB : (𝒩.baseChange i i₂ g' f sq).toOpenFactor hW =
      (𝒩.toOpenFactor hU).baseChange i' iW g' (f ∣_ U) sqW :=
    VirtualNormalBundle.toOpenFactor_baseChange hU hW 𝒩 sq (morphismRestrict_ι f U) sqW
  have hbase : ∀ (s s' : (f ⁻¹ᵁ U).toScheme ⟶ C.S) [LocallyOfFiniteType s]
      [LocallyOfFiniteType s'] (_ : s = s') (h₁ : iW ≫ s = sZ') (h₂ : iW ≫ s' = sZ')
      (N : VirtualNormalBundle iW) (b : chowGroup C (t' ≫ s) k) (b' : chowGroup C (t' ≫ s') k),
      b ≍ b' →
      (completedBivariantSequenceOfInvertible C sZ' s iW h₁
          (completedVirtualNormalGysinClass C sZ' s iW h₁ N) n).cap t' k b =
        (completedBivariantSequenceOfInvertible C sZ' s' iW h₂
          (completedVirtualNormalGysinClass C sZ' s' iW h₂ N) n).cap t' k b' := by
    intro s s' _ _ hs h₁ h₂ N b b' hb
    subst hs
    cases hb
    rfl
  rw [hB, hbase _ (f ∣_ U ≫ (U.ι ≫ sX)) (morphismRestrict_ι_assoc f U sX).symm hiW hiW' _ a
    (chowGroupCongr C (by rw [morphismRestrict_ι_assoc]) k a) (chowGroupCongr_heq C _ k a).symm,
    completedVirtualNormalGysinClass_cap_baseChange C sZ (U.ι ≫ sX) i'
      (openFactor_comp_structureMorphism C sZ sX i hi hU) iW g' (f ∣_ U) sqW
      (𝒩.toOpenFactor hU) sZ' hiW' n t' k, chowGroupCongr_chowGroupCongr]

/-- **The counterpart for immersions of the base-change clause of Stacks 0FBK, on cap
operations, at arbitrary rank.** For a cartesian square `Z' = Z ×_X X'` of immersions with
`X' ⟶ X` locally of finite type and a test scheme `t : T ⟶ X'`, the degree-`n` part of
`c(Z' ⟶ X', g^*𝒩) ∈ A^*(Z' ⟶ X')^∧` caps as the degree-`n` part of `c(Z ⟶ X, 𝒩)` does on
`t ≫ f`, through `Z ×_X T ≅ Z' ×_{X'} T`; the opens through which the two immersions factor as
closed immersions are arbitrary. -/
theorem completedVirtualNormalGysinClassOfOpen_cap_baseChange (V : X'.Opens)
    (iV : Z' ⟶ V.toScheme) [IsClosedImmersion iV] (hV : iV ≫ V.ι = i₂) (n : ℤ) {T : Scheme.{u}}
    (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    (completedBivariantSequenceOfInvertible C sZ' (f ≫ sX) i₂ hi₂
        (completedVirtualNormalGysinClassOfOpen C sZ' (f ≫ sX) i₂ hi₂ V iV hV
          (𝒩.baseChange i i₂ g' f sq)) n).cap t k α =
      chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i₂ t ≫ sZ')
        ((IsPullback.of_hasPullback i₂ t).paste_horiz sq.flip).isoPullback.inv
        (by rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, ← hi₂,
          ← Category.assoc i₂, sq.w, Category.assoc, hi])
        (k - n)
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
          (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) n).cap (t ≫ f) k
          (chowGroupCongr C (Category.assoc t f sX).symm k α)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  -- the open `W = f⁻¹(U)` of `X'` and the closed factor `iW : Z' ⟶ W` of `i₂`
  have hrange : Set.range i₂.base ⊆ Set.range (f ⁻¹ᵁ U).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (i₂ ≫ f).base z ∈ U
    rw [sq.w, ← hU]
    exact ((g' ≫ i').base z).2
  let iW : Z' ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι i₂ hrange
  have hW : iW ≫ (f ⁻¹ᵁ U).ι = i₂ := IsOpenImmersion.lift_fac _ _ _
  have commW : iW ≫ f ∣_ U = g' ≫ i' := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hW, sq.w,
      Category.assoc, hU]
  have sqW : IsPullback iW g' (f ∣_ U) i' :=
    IsPullback.of_right (by rw [hW, hU]; exact sq) commW (isPullback_morphismRestrict f U).flip
  have : IsClosedImmersion iW := MorphismProperty.of_isPullback sqW.flip inferInstance
  have hiW' : iW ≫ (f ∣_ U ≫ (U.ι ≫ sX)) = sZ' := by
    rw [morphismRestrict_ι_assoc, ← Category.assoc, hW, hi₂]
  refine (congrArg (fun c ↦ (completedBivariantSequenceOfInvertible C sZ' (f ≫ sX) i₂ hi₂ c n).cap
      t k α)
    (completedVirtualNormalGysinClassOfOpen_independent C sZ' (f ≫ sX) i₂ hi₂
      (𝒩.baseChange _ i₂ g' f sq) V (f ⁻¹ᵁ U) iV hV iW hW)).trans ?_
  -- the left side: through `f⁻¹(U) ×_{X'} T`, then `U ×_X T`
  have hL := completedVirtualNormalGysinClassOfOpen_cap_heq C sZ' (f ≫ sX) i₂ hi₂ (f ⁻¹ᵁ U) iW hW
    (𝒩.baseChange _ i₂ g' f sq) n t k α
  rw [completedVirtualNormalGysinClass_toOpenFactor_baseChange_cap C sZ sX i hi U i' hU f i₂ g' sq
      sZ' hi₂ 𝒩 iW hW sqW hiW' n (pullback.fst (f ⁻¹ᵁ U).ι t) k,
    chowGroupCongr_chowGroupRestrict,
    BivariantClass.cap_preimageTest C sZ sX i hi U i' hU f rfl _ t k α] at hL
  refine eq_of_heq (hL.trans ?_)
  -- the right side: through `U ×_X T`
  subst hU
  rw [eq_of_heq (completedVirtualNormalGysinClassOfOpen_cap_heq C sZ sX _ hi U i' rfl 𝒩 n
      (t ≫ f) k _),
    chowGroupRestrict_chowGroupCongr, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  refine (chowPushforwardOfIso_congrHom_heq hW t (by simp) (k - n) _).symm.trans (heq_of_eq ?_)
  rw [chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [← cancel_mono ((IsPullback.of_hasPullback i₂ t).paste_horiz sq.flip).isoPullback.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine pullback.hom_ext ?_ ?_
  · simp [pullback.congrHom]
  · simp [pullback.congrHom]
  · simp [pullback.condition_assoc]

/-- **The counterpart for immersions of the base-change clause of Stacks 0FBK, at arbitrary
rank.** For a cartesian square `Z' = Z ×_X X'` of immersions with `f : X' ⟶ X` locally of finite
type, the restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` along `f`, carried to `Z'`
along `Z ×_X X' ≅ Z'`, is `c(Z' ⟶ X', g^*𝒩) ∈ A^*(Z' ⟶ X')^∧`, with `g^*𝒩` the virtual normal
bundle of Stacks 0FBJ; the opens through which the two immersions factor as closed immersions are
arbitrary. Both sides are read degree by degree (Stacks 0FE0), and in each degree the cap
operations agree by `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_cap_baseChange`. -/
@[stacks 0FBQ "(3), counterparts: the counterpart of the base-change clause of Lemma 0FBK, the \
restriction of c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ along X' → X is c(Z' → X', g^*𝒩), for a cartesian \
square of immersions and 𝒩 of arbitrary rank"]
theorem completedBivariantTransport_completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen
    (V : X'.Opens) (iV : Z' ⟶ V.toScheme) [IsClosedImmersion iV] (hV : iV ≫ V.ι = i₂) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    completedBivariantTransport C (pullback.fst i f ≫ sZ) sZ' (f ≫ sX) (pullback.snd i f)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) i₂ hi₂ sq.flip.isoPullback.symm
        sq.flip.isoPullback_inv_snd
        (completedBivariantRestrictionViaSequence C sZ sX i hi f
          (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩)) =
      completedVirtualNormalGysinClassOfOpen C sZ' (f ≫ sX) i₂ hi₂ V iV hV
        (𝒩.baseChange i i₂ g' f sq) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian (pullback i f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
  refine completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (funext fun n ↦ ?_)
  refine (completedBivariantSequenceOfInvertible_completedBivariantTransport C _ _ _ _ _ _ _ _ _
    _ n).trans ?_
  rw [completedBivariantSequenceOfInvertible_completedBivariantRestriction]
  refine eq_of_isBivariantTransport C _ _ _ _ _ _ _ _ _ _ _
    (isBivariantTransport_bivariantTransport C _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  intro T t _ k α
  refine (completedVirtualNormalGysinClassOfOpen_cap_baseChange C sZ sX i hi U i' hU f i₂ g' sq sZ'
    hi₂ 𝒩 V iV hV n t k α).trans ?_
  rw [bivariantTransportCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [← cancel_mono ((IsPullback.of_hasPullback i₂ t).paste_horiz sq.flip).isoPullback.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

end BaseChange

/-! ### The chosen fibre product -/

section ChosenBaseChange

variable {X' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f] (𝒩 : VirtualNormalBundle i)

/-- **The counterpart for immersions of the base-change clause of Stacks 0FBK, at arbitrary rank,
for the chosen fibre product.** The restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`
along `f : X' ⟶ X` is `c(Z ×_X X' ⟶ X', g^*𝒩)`, for any open `V ⊆ X'` through which
`Z ×_X X' ⟶ X'` factors as a closed immersion. -/
theorem completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen (V : X'.Opens)
    (iV : pullback i f ⟶ V.toScheme) [IsClosedImmersion iV] (hV : iV ≫ V.ι = pullback.snd i f) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    completedBivariantRestrictionViaSequence C sZ sX i hi f
        (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩) =
      completedVirtualNormalGysinClassOfOpen C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) V iV hV
        (𝒩.baseChange i (pullback.snd i f) (pullback.fst i f) f (isPullback_pullbackSnd i f)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian (pullback i f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
  refine completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (funext fun n ↦ ?_)
  refine (completedBivariantSequenceOfInvertible_completedBivariantRestriction C sZ sX i hi f
    _ n).trans (BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_)
  refine Eq.trans ?_ (completedVirtualNormalGysinClassOfOpen_cap_baseChange C sZ sX i hi U i' hU f
    (pullback.snd i f) (pullback.fst i f) (isPullback_pullbackSnd i f) _
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) 𝒩 V iV hV n t k α).symm
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine ((IsPullback.of_hasPullback (pullback.snd i f) t).paste_horiz
    (isPullback_pullbackSnd i f).flip).hom_ext ?_ ?_
  · simp
  · simp

/-- **The counterpart for immersions of the base-change clause of Stacks 0FBK, at arbitrary rank,
at the canonical opens.** The restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` along
`f : X' ⟶ X` is `c(Z ×_X X' ⟶ X', g^*𝒩)`, both classes built at the largest opens in which the
two immersions are closed. -/
theorem completedBivariantRestriction_completedVirtualNormalGysinClassOfImmersion :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    completedBivariantRestrictionViaSequence C sZ sX i hi f
        (completedVirtualNormalGysinClassOfImmersion C sZ sX i hi 𝒩) =
      completedVirtualNormalGysinClassOfImmersion C (pullback.fst i f ≫ sZ) (f ≫ sX)
        (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
        (𝒩.baseChange i (pullback.snd i f) (pullback.fst i f) f (isPullback_pullbackSnd i f)) :=
  completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen C sZ sX i hi
    i.coborderRange i.liftCoborder i.liftCoborder_ι f 𝒩 (pullback.snd i f).coborderRange
    (pullback.snd i f).liftCoborder (pullback.snd i f).liftCoborder_ι

end ChosenBaseChange

/-! ### The counterpart of Stacks 0FV7 -/

section RestrictionExcess

variable {X' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f] (N : VirtualNormalBundle i)
  (𝒩' : VirtualNormalBundle (pullback.snd i f)) (Eb : (pullback i f).Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eb]
  (inc : 𝒩'.bundle ⟶ (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle)
  (pr : (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle ⟶ Eb)

/-- **The counterpart of Stacks 0FV7 for immersions, at arbitrary rank.** Let `Z' = Z ×_X X'` be
the chosen base change of an immersion `i : Z ⟶ X` along `f : X' ⟶ X`, let `𝒩` be a virtual normal
bundle for `Z ⟶ X` and `𝒩'` one for `Z' ⟶ X'`, of arbitrary ranks, and let
`0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_{Z'}`-modules such
that the square of `hcomm` commutes. Then

  `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`

in `A^*(Z' ⟶ X')^∧`, for the classes of Stacks 0FBQ (3) built from arbitrary opens through which
the two immersions factor as closed immersions. By the counterpart of the base-change clause of
Stacks 0FBK and the counterpart of Stacks 0FBL. -/
@[stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FV7, res(c(Z → X, N)) = c_top(E) ∘ \
c(Z' → X', N') in A^*(Z' → X')^∧ for the chosen base change Z' = Z ×_X X' of an immersion, virtual \
normal bundles N, N' of arbitrary rank and a short exact sequence 0 → N' → g^*N → E → 0 of finite \
locally free modules whose dual square against the conormal sheaves commutes"]
theorem completedVirtualNormalGysinRestrictionOfOpen_eq_of_isTopChernComposition (V : X'.Opens)
    (iV : pullback i f ⟶ V.toScheme) [IsClosedImmersion iV] (hV : iV ≫ V.ι = pullback.snd i f)
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hcomm : pullbackDualMap (pullback.fst i f) N.bundle ≫
        dualMap inc ≫ 𝒩'.surjection =
      (modulePullback (pullback.fst i f).toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (pullback.snd i f) i (pullback.fst i f) f
          (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i f).w)) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    completedBivariantRestrictionViaSequence C sZ sX i hi f
        (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU N) =
      completedBivariantGroup.copy C (Category.id_comp (pullback.snd i f)) _
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
        (completedBivariantCompositeOfInvertible C (pullback.fst i f ≫ sZ)
          (pullback.fst i f ≫ sZ) (f ≫ sX) (𝟙 _) (pullback.snd i f) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
          (topChernClassOfInvertible C (pullback.fst i f ≫ sZ) Eb)
          (completedVirtualNormalGysinClassOfOpen C (pullback.fst i f ≫ sZ) (f ≫ sX)
            (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) V iV hV
            𝒩')) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian (pullback i f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
  rw [completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU f N
    V iV hV]
  exact completedVirtualNormalGysinClassOfOpen_eq_of_isTopChernComposition C
    (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) V iV hV _ 𝒩' Eb inc pr w hseq
    (dualMap_comp_surjection_eq_baseChange_surjection i (pullback.snd i f) (pullback.fst i f) f
      (isPullback_pullbackSnd i f) N 𝒩' inc hcomm)

end RestrictionExcess

end Stacks.Chow

end
