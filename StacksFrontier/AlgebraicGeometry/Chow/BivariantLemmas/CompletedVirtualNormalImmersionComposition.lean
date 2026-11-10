module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalClassDualIso
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionClass
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality

/-!
# Stacks 0FEC for immersions, at arbitrary rank

Stacks 0FBQ (3) attaches to a virtual normal bundle `𝒩` of arbitrary rank for an immersion
`i : Z ⟶ X` the class `c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* ∈ A^*(Z ⟶ X)^∧`
(`Stacks.Chow.completedVirtualNormalGysinClassOfOpen`), for an open `U ⊆ X` in which `Z` is
closed, and says that all the lemmas on the class of a closed immersion have immediate
counterparts. This file gives the counterpart of Stacks 0FEC: for immersions `Z ⟶ Y ⟶ X` of
schemes locally of finite type over the base and a conormal-compatible triple `𝒩, 𝒩', 𝒩''` of
virtual normal bundles for `Z ⊆ X`, `Z ⊆ Y` and `Y ⊆ X`,

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`.

The proof restricts both sides (Stacks 0F9Z) to the open `W = (Z ⟶ X).coborderRange ∩
(Y ⟶ X).coborderRange` of `X`, which contains `Z` and in which `Z` and `Y ∩ W` are closed; a
class on `Z ⟶ X` is determined by its restriction to such an open
(`Stacks.Chow.eq_of_completedBivariantRestriction_eq`). Over `W` the three immersions become
closed immersions, the classes of Stacks 0FBQ (3) become those of Stacks 0FBK
(`Stacks.Chow.completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass`), the
restrictions of the three classes are the classes of the base-changed triple (the counterpart of
the base-change clause of Stacks 0FBK, and the restriction of composites on completions), and
Stacks 0FEC for closed immersions (`Stacks.Chow.completedVirtualNormalGysinClass_comp`) applies to
the base-changed triple.

## Main results

* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass` — for
  a closed immersion the class of Stacks 0FBQ (3) is that of Stacks 0FBK, at arbitrary rank.
* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_comp`,
  `Stacks.Chow.completedVirtualNormalGysinClassOfImmersion_comp` — the counterpart of Stacks 0FEC
  for immersions, at arbitrary rank.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-- Two completed classes are equal when their components in every degree are. -/
private theorem completedBivariantGroup_ext_of_sequence_eq (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {c d : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    (h : ∀ n, completedBivariantSequenceOfInvertible C sX sY f hf c n =
      completedBivariantSequenceOfInvertible C sX sY f hf d n) : c = d :=
   completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (funext h)

/-! ### For a closed immersion, the class of Stacks 0FBQ (3) is that of Stacks 0FBK -/

section ThroughOpen

variable {C : ChowSituation.{u}} {G : GysinSystem C} {Z X : Scheme.{u}} {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {U : X.Opens}
  {i' : Z ⟶ U.toScheme} [LocallyOfFiniteType (i' ≫ U.ι)] {hi : (i' ≫ U.ι) ≫ sX = sZ} {p : ℤ}

/-- **Capping through an open containing the source.** For a class `c` on `Z ⟶ X` whose morphism
factors through an open `U ⊆ X`, and a test scheme `t : T ⟶ X`, capping a class `α` on `T` with
`c` is capping its restriction to `U ×_X T` with `c`, read back on `Z ×_X T` through the
isomorphism `Z ×_X (U ×_X T) ≅ Z ×_X T`. This is the flat-pullback axiom of Stacks 0B76 along the
open immersion `U ×_X T ⟶ T`, whose base change to `Z` is an isomorphism. -/
theorem BivariantClass.cap_eq_chowPushforwardOfIso_cap_preimage
    (c : BivariantClass C G sZ sX (i' ≫ U.ι) hi p) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k)
    (φ : pullback (i' ≫ U.ι) (pullback.fst U.ι t ≫ U.ι) ⟶ pullback (i' ≫ U.ι) t) [IsIso φ]
    (hφ₁ : φ ≫ pullback.fst (i' ≫ U.ι) t = pullback.fst (i' ≫ U.ι) (pullback.fst U.ι t ≫ U.ι))
    (hφ₂ : φ ≫ pullback.snd (i' ≫ U.ι) t =
      pullback.snd (i' ≫ U.ι) (pullback.fst U.ι t ≫ U.ι) ≫ pullback.snd U.ι t)
    (hφ : φ ≫ pullback.fst (i' ≫ U.ι) t ≫ sZ =
      pullback.fst (i' ≫ U.ι) (pullback.fst U.ι t ≫ U.ι) ≫ sZ)
    (h₁ : pullback.snd U.ι t ≫ t ≫ sX = pullback.fst U.ι t ≫ U.ι ≫ sX)
    (h₂ : pullback.fst U.ι t ≫ U.ι ≫ sX = (pullback.fst U.ι t ≫ U.ι) ≫ sX) :
    chowPushforwardOfIso C (pullback.fst (i' ≫ U.ι) (pullback.fst U.ι t ≫ U.ι) ≫ sZ)
        (pullback.fst (i' ≫ U.ι) t ≫ sZ) φ hφ (k - p)
        (c.cap (pullback.fst U.ι t ≫ U.ι) k (chowGroupCongr C h₂ k
          (chowGroupRestrict C (t ≫ sX) (pullback.fst U.ι t ≫ U.ι ≫ sX) (pullback.snd U.ι t) h₁ k
            α))) =
      c.cap t k α := by
  have hm : pullback.snd U.ι t ≫ t = pullback.fst U.ι t ≫ U.ι := pullback.condition.symm
  set b := baseChangeMapOfEq (i' ≫ U.ι) t (pullback.snd U.ι t) (pullback.fst U.ι t ≫ U.ι) hm
  have sqv := isPullback_baseChangeMapOfEq (i' ≫ U.ι) t (pullback.snd U.ι t)
    (pullback.fst U.ι t ≫ U.ι) hm
  have : IsOpenImmersion b := MorphismProperty.of_isPullback sqv (P := @IsOpenImmersion)
    inferInstance
  have hφb : φ = b := pullback.hom_ext (by rw [hφ₁, baseChangeMapOfEq_fst])
    (by rw [hφ₂, baseChangeMapOfEq_snd])
  subst hφb
  have hcap := BivariantClass.cap_chowGroupRestrict C G sZ sX (i' ≫ U.ι) hi p c t
    (pullback.snd U.ι t) (pullback.fst U.ι t ≫ U.ι) hm b sqv (baseChangeMapOfEq_fst _ _ _ _ _) k
    (by rw [← Category.assoc, hm]) hφ α
  rw [chowGroupCongr_chowGroupRestrict C (t ≫ sX) _ _ (pullback.snd U.ι t) h₁
      (by rw [← Category.assoc, hm]) h₂ k α, ← hcap,
    chowGroupRestrict_of_isIso C _ _ (k - p) b hφ, chowPushforwardOfIso_comp_apply]
  exact (chowPushforwardOfIso_congr_apply C _ _ _ _ (IsIso.inv_hom_id b) _
    (Category.id_comp _) _ _).trans (chowPushforwardOfIso_id C _ _ _)

end ThroughOpen

section OfOpenClosed

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **For a closed immersion the construction of Stacks 0FBQ (3) is that of Stacks 0FBK, at
arbitrary rank.** If `i : Z ⟶ X` is a closed immersion, then for every open `U ⊆ X` through which
`i` factors as a closed immersion `i' : Z ⟶ U`,

  `c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^* = c(Z ⟶ X, 𝒩)`   in `A^*(Z ⟶ X)^∧`.

Both are compared degree by degree on cap operations: `c(Z ⟶ U, 𝒩)` is the base change of
`c(Z ⟶ X, 𝒩)` along `U ⟶ X` (Stacks 0FBK, with `𝒩` read through
`Stacks.Chow.completedVirtualNormalGysinClass_eq_of_dualIso`), and capping with `c(Z ⟶ X, 𝒩)`
through `U ×_X T` is capping on `T`
(`Stacks.Chow.BivariantClass.cap_eq_chowPushforwardOfIso_cap_preimage`). -/
theorem completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (U : X.Opens) (i' : Z ⟶ U.toScheme)
    [IsClosedImmersion i'] (hU : i' ≫ U.ι = i) (N : VirtualNormalBundle i) :
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU N =
      completedVirtualNormalGysinClass C sZ sX i hi N := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  subst hU
  refine completedBivariantGroup_ext_of_sequence_eq C sZ sX _ _
    fun n ↦ BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  refine (eq_of_heq (completedVirtualNormalGysinClassOfOpen_cap_heq C sZ sX _ hi U i' rfl N n t k
    α)).trans ?_
  rw [← completedVirtualNormalGysinClass_eq_of_dualIso C sZ (U.ι ≫ sX) i'
    (openFactor_comp_structureMorphism C sZ sX _ hi rfl)
    (N.baseChange _ i' (𝟙 Z) U.ι (isPullback_id_ι rfl)) (N.toOpenFactor rfl)
    (N.baseChangeIdDualIso U.ι (isPullback_id_ι rfl))
    (N.baseChangeIdDualIso_hom_comp_surjection_ι rfl)]
  rw [completedVirtualNormalGysinClass_cap_baseChange C sZ sX (i' ≫ U.ι) hi i' (𝟙 Z) U.ι
    (isPullback_id_ι rfl) N sZ (openFactor_comp_structureMorphism C sZ sX _ hi rfl) n
    (pullback.fst U.ι t) k _, chowPushforwardOfIso_comp_apply]
  have hσ := subschemeTestBaseChangeIso_hom_fst (i' ≫ U.ι) i' (𝟙 Z) U.ι (isPullback_id_ι rfl)
    (pullback.fst U.ι t)
  rw [Category.comp_id] at hσ
  exact BivariantClass.cap_eq_chowPushforwardOfIso_cap_preimage _ t k α _
    (by simp [hσ]) (by simp) _ _ _

end OfOpenClosed

/-! ### Restriction to an open containing the source -/

/-- An immersion `f : A ⟶ B` becomes a closed immersion after base change to an open `W ⊆ B`
contained in `f.coborderRange`, the largest open in which `A` is closed. -/
theorem isClosedImmersion_pullbackSnd_of_le_coborderRange {A B : Scheme.{u}} (f : A ⟶ B)
    [IsImmersion f] (W : B.Opens) (hW : W ≤ f.coborderRange) :
    IsClosedImmersion (pullback.snd f W.ι) := by
  have h := isClosedImmersion_resLE_of_le_coborderRange f W hW
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at h
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

section Transport

variable (C : ChowSituation.{u}) {A B W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA) (u : B ⟶ W) [LocallyOfFiniteType u]
  (hu : u ≫ sW = sB) [IsLocallyNoetherian A] [IsLocallyNoetherian B] [IsLocallyNoetherian W]

/-- **Transporting back along an inverse isomorphism, on completions.** For isomorphisms
`θ : A ≅ B` and `θ' : B ≅ A` over `W` with `θ ≫ θ' = 𝟙`, transporting a completed class along `θ`
and then along `θ'` gives the class back; degree by degree this is
`Stacks.Chow.bivariantTransport_bivariantTransport_of_hom_comp_hom_eq_id`. -/
theorem completedBivariantTransport_completedBivariantTransport_of_hom_comp_hom_eq_id
    (θ : A ≅ B) (hθ : θ.hom ≫ u = v) (θ' : B ≅ A) (hθ' : θ'.hom ≫ v = u) (h : θ.hom ≫ θ'.hom = 𝟙 A)
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv) :
    completedBivariantTransport C sB sA sW u hu v hv θ' hθ'
        (completedBivariantTransport C sA sB sW v hv u hu θ hθ c) = c := by
  refine completedBivariantGroup_ext_of_sequence_eq C sA sW _ _ fun n ↦ ?_
  refine (completedBivariantSequenceOfInvertible_completedBivariantTransport C sB sA sW u hu v hv
    θ' hθ' _ n).trans ?_
  rw [completedBivariantSequenceOfInvertible_completedBivariantTransport]
  exact bivariantTransport_bivariantTransport_of_hom_comp_hom_eq_id C (gysinSystemOfInvertible C)
    sA sB sW v hv u hu n (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) θ hθ θ' hθ' h _

end Transport

section RestrictionInjective

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [LocallyOfFiniteType f]
  (hf : f ≫ sX = sZ) [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- **A completed class is determined by its restriction to an open containing the image of its
source.** If `W ⊆ X` is an open containing the image of `f : Z ⟶ X`, two completed classes in
`A^*(Z ⟶ X)^∧` with the same restriction (Stacks 0F9Z) along `W ⟶ X` are equal: degree by degree
this is `Stacks.Chow.BivariantClass.eq_of_bivariantRestriction_eq` for the constant family
`W`. -/
theorem eq_of_completedBivariantRestriction_eq (W : X.Opens) (hW : ∀ z : Z, f.base z ∈ W)
    [IsLocallyNoetherian W.toScheme] [IsLocallyNoetherian (pullback f W.ι)]
    {c d : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX f hf}
    (h : completedBivariantRestrictionViaSequence C sZ sX f hf W.ι c =
      completedBivariantRestrictionViaSequence C sZ sX f hf W.ι d) :
    c = d := by
  refine completedBivariantGroup_ext_of_sequence_eq C sZ sX _ _ fun n ↦ ?_
  refine BivariantClass.eq_of_bivariantRestriction_eq C sZ sX f hf (fun _ ↦ W)
    (fun _ x _ ↦ hW x) fun _ ↦ ?_
  exact (completedBivariantSequenceOfInvertible_completedBivariantRestriction C sZ sX f hf W.ι c
    n).symm.trans ((congrArg (fun e ↦ completedBivariantSequenceOfInvertible C _ _ _ _ e n) h).trans
      (completedBivariantSequenceOfInvertible_completedBivariantRestriction C sZ sX f hf W.ι d n))

end RestrictionInjective

/-! ### The counterpart of Stacks 0FEC for immersions -/

section Composition

variable {C : ChowSituation.{u}} {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ Y}
  {j : Y ⟶ X} [IsImmersion i] [IsImmersion j] (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY)
  (D : ConormalCompatibleVirtualNormalBundles i j)

/-- **The counterpart of Stacks 0FEC for immersions, at arbitrary rank.** Let `Z ⟶ Y ⟶ X` be
immersions of schemes locally of finite type over the base, and let `D` be a conormal-compatible
triple of virtual normal bundles `𝒩`, `𝒩'`, `𝒩''` for `Z ⊆ X`, `Z ⊆ Y` and `Y ⊆ X`, of arbitrary
(locally constant) ranks. Then

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`,

for the classes of Stacks 0FBQ (3) built from arbitrary opens `W`, `V`, `U` in which the three
immersions are closed. -/
@[stacks 0FBQ "(3), counterparts: the counterpart of Lemma 0FEC, c(Z → X, 𝒩) = c(Z → Y, 𝒩') ∘ \
c(Y → X, 𝒩'') in A^*(Z → X)^∧ for immersions Z → Y → X and a conormal-compatible triple of \
virtual normal bundles of arbitrary rank"]
theorem completedVirtualNormalGysinClassOfOpen_comp
    (W : X.Opens) (iW : Z ⟶ W.toScheme) [IsClosedImmersion iW] (hW : iW ≫ W.ι = i ≫ j)
    (V : Y.Opens) (iV : Z ⟶ V.toScheme) [IsClosedImmersion iV] (hV : iV ≫ V.ι = i)
    (U : X.Opens) (jU : Y ⟶ U.toScheme) [IsClosedImmersion jU] (hU : jU ≫ U.ι = j) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedVirtualNormalGysinClassOfOpen C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj)
        W iW hW D.bundleZX =
      completedBivariantCompositeOfInvertible C sZ sY sX i j hi hj
        (completedVirtualNormalGysinClassOfOpen C sZ sY i hi V iV hV D.bundleZY)
        (completedVirtualNormalGysinClassOfOpen C sY sX j hj U jU hU D.bundleYX) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  -- the open `W₀` of `X` over which the three immersions are closed
  set W₀ : X.Opens := (i ≫ j).coborderRange ⊓ j.coborderRange
  set g := W₀.ι
  have : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : IsLocallyNoetherian (pullback j g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst j g ≫ sY)
  have : IsLocallyNoetherian (pullback (i ≫ j) g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ j) g ≫ sZ)
  have : IsLocallyNoetherian (pullback i (pullback.fst j g)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i (pullback.fst j g) ≫ sZ)
  have : IsClosedImmersion (pullback.snd j g) :=
    isClosedImmersion_pullbackSnd_of_le_coborderRange j W₀ inf_le_right
  have : IsClosedImmersion (pullback.snd (i ≫ j) g) :=
    isClosedImmersion_pullbackSnd_of_le_coborderRange (i ≫ j) W₀ inf_le_left
  have : IsClosedImmersion (pullback.snd i (pullback.fst j g) ≫ pullback.snd j g) := by
    rw [← pullbackRightPullbackFstIso_hom_snd j g i]
    infer_instance
  have : IsClosedImmersion (pullback.snd i (pullback.fst j g)) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.snd j g)
  have hrange : ∀ z : Z, (i ≫ j).base z ∈ W₀ := fun z ↦
    ⟨subset_coborder ⟨z, rfl⟩, subset_coborder ⟨i.base z, rfl⟩⟩
  -- the squares and identifications of the base change to `W₀`
  set i₁ := pullback.snd i (pullback.fst j g)
  set j₁ := pullback.snd j g
  have hi₁ := pullbackSnd_comp_structureMorphism_eq C sZ sY i hi (pullback.fst j g)
  have hj₁ := pullbackSnd_comp_structureMorphism_eq C sY sX j hj g
  have sqP := IsPullback.paste_horiz (isPullback_pullbackSnd i (pullback.fst j g))
      (isPullback_pullbackSnd j g)
  have hφθ : sqP.flip.isoPullback.symm.hom ≫ (pullbackRightPullbackFstIso j g i).hom = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, Category.id_comp]
      exact sqP.flip.isoPullback_inv_snd
  -- the restriction of the right-hand side
  have hR := completedBivariantRestriction_completedBivariantCompositeOfInvertible C sZ sY sX i j
    hi hj g (completedVirtualNormalGysinClassOfOpen C sZ sY i hi V iV hV D.bundleZY)
    (completedVirtualNormalGysinClassOfOpen C sY sX j hj U jU hU D.bundleYX)
  rw [completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen C sZ sY i hi V iV hV
      (pullback.fst j g) D.bundleZY i₁.coborderRange i₁.liftCoborder i₁.liftCoborder_ι,
    completedBivariantRestriction_completedVirtualNormalGysinClassOfOpen C sY sX j hj U jU hU g
      D.bundleYX j₁.coborderRange j₁.liftCoborder j₁.liftCoborder_ι,
    completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass C _ _ i₁,
    completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass C _ _ j₁] at hR
  -- the restriction of the left-hand side
  have hL :=
    completedBivariantTransport_completedBivariantRestriction_completedVirtualNormalGysinClass
    C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) W iW hW g (i₁ ≫ j₁)
    (pullback.fst i (pullback.fst j g)) sqP (pullback.fst i (pullback.fst j g) ≫ sZ)
    (comp_comp_structureMorphism_eq hi₁ hj₁) D.bundleZX (i₁ ≫ j₁).coborderRange
    (i₁ ≫ j₁).liftCoborder (i₁ ≫ j₁).liftCoborder_ι
  rw [completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass C _ _ (i₁ ≫ j₁)]
    at hL
  refine eq_of_completedBivariantRestriction_eq C sZ sX (i ≫ j) _ W₀ hrange ?_
  refine (completedBivariantTransport_completedBivariantTransport_of_hom_comp_hom_eq_id C
    (pullback.fst (i ≫ j) g ≫ sZ) (pullback.fst i (pullback.fst j g) ≫ sZ) (g ≫ sX)
    (pullback.snd (i ≫ j) g)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) g)
    (i₁ ≫ j₁) (comp_comp_structureMorphism_eq hi₁ hj₁) sqP.flip.isoPullback.symm
    sqP.flip.isoPullback_inv_snd (pullbackRightPullbackFstIso j g i)
    (pullbackRightPullbackFstIso_hom_snd j g i) hφθ _).symm.trans ?_
  rw [hL, hR]
  -- Stacks 0FEC for the closed immersions over `W₀`
  exact congrArg (completedBivariantTransport C _ _ (g ≫ sX) _ _ _ _
    (pullbackRightPullbackFstIso j g i) (pullbackRightPullbackFstIso_hom_snd j g i))
    (completedVirtualNormalGysinClass_comp (pullback.fst i (pullback.fst j g) ≫ sZ)
      (pullback.fst j g ≫ sY) (g ≫ sX) hi₁ hj₁
      (D.baseChange i₁ j₁ (pullback.fst i (pullback.fst j g)) (pullback.fst j g) g
        (isPullback_pullbackSnd j g) (isPullback_pullbackSnd i (pullback.fst j g))))

/-- **The counterpart of Stacks 0FEC for immersions, at arbitrary rank, at the canonical opens.**
For immersions `Z ⟶ Y ⟶ X` and a conormal-compatible triple `D` of virtual normal bundles of
arbitrary ranks, `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')` in `A^*(Z ⟶ X)^∧`, the three
classes of Stacks 0FBQ (3) being built at the largest opens in which the immersions are
closed. -/
theorem completedVirtualNormalGysinClassOfImmersion_comp :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedVirtualNormalGysinClassOfImmersion C sZ sX (i ≫ j)
        (comp_comp_structureMorphism_eq hi hj) D.bundleZX =
      completedBivariantCompositeOfInvertible C sZ sY sX i j hi hj
        (completedVirtualNormalGysinClassOfImmersion C sZ sY i hi D.bundleZY)
        (completedVirtualNormalGysinClassOfImmersion C sY sX j hj D.bundleYX) :=
  completedVirtualNormalGysinClassOfOpen_comp sZ sY sX hi hj D (i ≫ j).coborderRange
    (i ≫ j).liftCoborder (i ≫ j).liftCoborder_ι i.coborderRange i.liftCoborder i.liftCoborder_ι
    j.coborderRange j.liftCoborder j.liftCoborder_ι

end Composition

end Stacks.Chow

end
