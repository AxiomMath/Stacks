module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Statement
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.InfinityClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.OpenImmersionComposite

/-!
# Stacks 0FBP: the class of a virtual normal sheaf commutes with every bivariant class

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `Z ⊆ X` be a
closed subscheme with virtual normal sheaf `𝒩`, let `Y ⟶ X` be locally of finite type and let
`c ∈ A^*(Y ⟶ X)`. **Stacks 0FBP** says that `c` and the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of
Stacks 0FBK commute in the sense of Remark 0FA2.

The class is `Stacks.Chow.VirtualNormalBundle.completedClass`, the class of Stacks 0FBK of this
repository: on a connected component `Z_k` of `Z`, on which `𝒩` has constant rank `r_k`, its
degree `r_k` part is `Stacks.Chow.VirtualNormalBundle.virtualNormalClass`, the unique class with
`p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`, where `p : N ⟶ Z` is the vector bundle of `𝒩`, `C` the class
of Stacks 0F9J computed on the deformation space and `ι : C_ZX ⟶ N` the closed immersion of the
normal cone.

## The argument

The source reduces, by Stacks 02UC, to `X` integral and, after blowing up, to an effective
Cartier divisor, where `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ i^*` (Stacks 0FBL, 0FBN) and the result is the
centrality of Chern classes (Stacks 02UA) together with the commutation of `c` with the Gysin map
`i^*` (Stacks 0FA3). The argument here reads the commutation off the construction of the class
instead, and needs no reduction:

* the class `j^* ∘ C` of the construction commutes with every bivariant class: it is the class of
  Stacks 0F9J of the divisor `Z(t⁻¹)` of the deformation space, and the argument of Stacks 0FAS
  applies to it (`Stacks.Chow.GysinAtInfinity.infinityClass_bivariantCommute`);
* proper pushforward along `ι` and flat pullback preserve the property, so `ι_* ∘ j^* ∘ C`
  commutes with every class, and so does `p^*` (condition (2) of Stacks 0B76);
* the cap operations of `p^*` are injective (Stacks 02TY), so `p^*` can be cancelled from
  `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`: the class `c(Z ⟶ X, 𝒩)` of constant rank commutes with
  every class;
* in general, the class restricts on each connected component `Z_k` to the class of constant rank
  `r_k` of `𝒩|_{Z_k}`, and commuting is checked on the connected components.

## Main results

* `Stacks.Deformation.normalConeClass_commutesWithEveryClass` — `j^* ∘ C` commutes with every
  class.
* `Stacks.Chow.VirtualNormalBundle.virtualNormalClass_commutesWithEveryClass` — the class of
  constant rank commutes with every class.

## References

* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

/-! ### The class at infinity of the deformation to the normal cone -/

namespace Stacks.Deformation

variable (C : Stacks.Chow.ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i]

/-- **The class `σ = j^* ∘ C ∈ A⁰(C_ZX ⟶ X)` commutes with every bivariant class.** It is the class
of Stacks 0F9J for the divisor `Z(t⁻¹)` of the deformation space, whose complement is flat of
relative dimension one over `X`, and Stacks 0FAS holds for every such class
(`Stacks.Chow.GysinAtInfinity.infinityClass_bivariantCommute`). -/
theorem normalConeClass_commutesWithEveryClass :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    (normalConeClass C sX i).CommutesWithEveryClass := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  intro Y g _ q d
  exact Stacks.Chow.GysinAtInfinity.infinityClass_bivariantCommute C sX (deformationProjection i)
    (complementOpen (Stacks.Conormal.coborderIdeal i)).ι
    (relativeDimension_complementOpen_deformationProjection i)
    (Scheme.unitModule (deformationSpace (Stacks.Conormal.coborderIdeal i)))
    (paramGlobal (Stacks.Conormal.coborderIdeal i))
    (range_zeroScheme_paramGlobal (Stacks.Conormal.coborderIdeal i))
    (Stacks.Chow.isTrivial_pullback_unitModule _) g q d

end Stacks.Deformation

namespace Stacks.Chow

/-! ### The canonical proper pushforward -/

section Pushforward

variable {C : ChowSituation.{u}} {X A B : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {p : ℤ}

/-- The canonical proper pushforward of Stacks 0EPK is the proper pushforward at the Gysin system
of the first Chern class rule: the two classes cap by the same rule. -/
theorem canonicalBivariantProperPushforward_eq (h : A ⟶ B) [IsProper h] (g : B ⟶ X)
    [LocallyOfFiniteType g] [LocallyOfFiniteType (h ≫ g)] (hh : h ≫ sB = sA) (hg : g ≫ sX = sB)
    (c : BivariantClass C (gysinSystemOfInvertible C) sA sX (h ≫ g)
      (comp_comp_structureMorphism_eq hh hg) p) :
    canonicalBivariantProperPushforward C sA sB sX h g hh hg p c =
      bivariantProperPushforwardOfInvertible C sA sB sX h g hh hg p c :=
  BivariantClass.ext _ _ _ _ _ _ _ fun t _ k α ↦
    (canonicalBivariantProperPushforward_cap C sA sB sX h g hh hg p c t k α).trans
      (bivariantProperPushforwardOfInvertible_cap C sA sB sX h g hh hg p c t k α).symm

/-- The canonical proper pushforward of a class commuting with every class commutes with every
class. -/
theorem commutesWithEveryClass_canonicalBivariantProperPushforward (h : A ⟶ B) [IsProper h]
    (g : B ⟶ X) [LocallyOfFiniteType g] [LocallyOfFiniteType (h ≫ g)] (hh : h ≫ sB = sA)
    (hg : g ≫ sX = sB)
    (c : BivariantClass C (gysinSystemOfInvertible C) sA sX (h ≫ g)
      (comp_comp_structureMorphism_eq hh hg) p)
    (hc : c.CommutesWithEveryClass) :
    (canonicalBivariantProperPushforward C sA sB sX h g hh hg p c).CommutesWithEveryClass := by
  rw [canonicalBivariantProperPushforward_eq]
  exact commutesWithEveryClass_bivariantProperPushforward h g hh hg c hc

end Pushforward

/-! ### Pullbacks along a monomorphism -/

section PullbackMono

variable {𝒞 : Type*} [Category 𝒞] {X' X Y' Y S : 𝒞} {ιX : X' ⟶ X} {ιY : Y' ⟶ Y} [Mono ιY]
  {f : X ⟶ Y} {fw : X' ⟶ Y'} (w : fw ≫ ιY = ιX ≫ f) (s : S ⟶ Y')

/-- For a monomorphism `ιY` and a commutative square `fw ≫ ιY = ιX ≫ f`, the pullback of
`ιX ≫ f` along `s ≫ ιY` is the pullback of `fw` along `s`. -/
private def pullbackCompIsoOfMono [HasPullback (ιX ≫ f) (s ≫ ιY)] [HasPullback fw s] :
    pullback (ιX ≫ f) (s ≫ ιY) ≅ pullback fw s where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [← cancel_mono ιY, Category.assoc, w, Category.assoc]
    exact pullback.condition)
  inv := pullback.lift (pullback.fst fw s) (pullback.snd fw s)
    (by rw [← w, ← Category.assoc, pullback.condition, Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- The isomorphism `pullbackCompIsoOfMono` is compatible with the first projections. -/
@[reassoc]
private theorem pullbackCompIsoOfMono_hom_fst [HasPullback (ιX ≫ f) (s ≫ ιY)] [HasPullback fw s] :
    (pullbackCompIsoOfMono w s).hom ≫ pullback.fst fw s = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The isomorphism `pullbackCompIsoOfMono` is compatible with the second projections. -/
@[reassoc]
private theorem pullbackCompIsoOfMono_hom_snd [HasPullback (ιX ≫ f) (s ≫ ιY)] [HasPullback fw s] :
    (pullbackCompIsoOfMono w s).hom ≫ pullback.snd fw s = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

variable (ιY) in
/-- For a monomorphism `ιY`, a morphism `s` to its source is the pullback of `ιY` along
`s ≫ ιY`. -/
private def isoPullbackCompOfMono [HasPullback ιY (s ≫ ιY)] : S ≅ pullback ιY (s ≫ ιY) where
  hom := pullback.lift s (𝟙 S) (Category.id_comp _).symm
  inv := pullback.snd ιY (s ≫ ιY)
  hom_inv_id := pullback.lift_snd _ _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono ιY, Category.assoc]
      exact pullback.condition.symm
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

variable (ιY) in
/-- The isomorphism `isoPullbackCompOfMono` followed by the first projection is `s`. -/
@[reassoc]
private theorem isoPullbackCompOfMono_hom_fst [HasPullback ιY (s ≫ ιY)] :
    (isoPullbackCompOfMono ιY s).hom ≫ pullback.fst ιY (s ≫ ιY) = s :=
  pullback.lift_fst _ _ _

end PullbackMono

/-- For opens `U ⊆ X`, `V ⊆ Y` and a restriction `fU : U ⟶ V` of `f`, the identification
`U ×_Y S ≅ U ×_V S` of `pullbackCompIsoOfMono` followed by `opensPullbackComparison` is the base
change of `U ⟶ X`. -/
private theorem pullbackCompIsoOfMono_hom_opensPullbackComparison {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (fU : (U : Scheme.{u}) ⟶ (V : Scheme.{u}))
    (hfU : fU ≫ V.ι = U.ι ≫ f) (s : S ⟶ (V : Scheme.{u})) :
    (pullbackCompIsoOfMono hfU s).hom ≫ opensPullbackComparison f U V fU hfU s =
      bivariantPushforwardBaseChange U.ι f (s ≫ V.ι) := by
  apply pullback.hom_ext
  · rw [Category.assoc, opensPullbackComparison_fst, bivariantPushforwardBaseChange_fst,
      pullbackCompIsoOfMono_hom_fst_assoc]
  · rw [Category.assoc, opensPullbackComparison_snd, bivariantPushforwardBaseChange_snd,
      pullbackCompIsoOfMono_hom_snd]

/-! ### A class on a connected component, extended by zero -/

section PieceExtension

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] {J : Type u} (UY : J → Y.Opens)
  (a : _root_.ConnectedComponents X → J)
  (ha : ∀ w, X.connectedComponentOpens w ≤ f ⁻¹ᵁ UY (a w)) (w : _root_.ConnectedComponents X)
  {n : ℤ}

/-- **A class on a connected component, extended by zero.** For a connected component `X_w` of `X`,
an open `V ⊆ Y` with `f(X_w) ⊆ V` and a class `b ∈ A^n(X_w ⟶ V)`, the class
`ι_* (b ∘ j^*) ∈ A^n(X ⟶ Y)`: the composite (Stacks 0B75) of `b` with the flat pullback along the
open immersion `j : V ⟶ Y` (Stacks 0B78), read as a class for `X_w ⟶ X ⟶ Y`, pushed forward
(Stacks 0EPK) along the inclusion `ι : X_w ⟶ X`, which is a closed immersion. -/
def bivariantPieceExtension
    (b : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((UY (a w)).ι ≫ sY) (pieceMap f X.connectedComponentOpens UY a ha w)
      (pieceMap_comp_structureMorphism C sX sY f hf X.connectedComponentOpens UY a ha w) n) :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n :=
  bivariantProperPushforwardOfInvertible C ((X.connectedComponentOpens w).ι ≫ sX) sX sY
    (X.connectedComponentOpens w).ι f rfl hf n
    (bivariantTransport C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((X.connectedComponentOpens w).ι ≫ sX) sY
      (pieceMap f X.connectedComponentOpens UY a ha w ≫ (UY (a w)).ι)
      (comp_comp_structureMorphism_eq
        (pieceMap_comp_structureMorphism C sX sY f hf X.connectedComponentOpens UY a ha w) rfl)
      ((X.connectedComponentOpens w).ι ≫ f) (comp_comp_structureMorphism_eq rfl hf)
      (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp, pieceMap_comp_ι]) n
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (BivariantClass.copy C (gysinSystemOfInvertible C) _ sY rfl _ _ (add_zero n)
        (openImmersionComposite C ((X.connectedComponentOpens w).ι ≫ sX) ((UY (a w)).ι ≫ sY) sY
          (pieceMap f X.connectedComponentOpens UY a ha w) (UY (a w)).ι
          (pieceMap_comp_structureMorphism C sX sY f hf X.connectedComponentOpens UY a ha w) rfl
          n b)))

variable {C sX sY f hf UY a ha w} in
/-- A class on a connected component commuting with every class extends by zero to a class that
does too: composition with the flat pullback of an open immersion, transport and proper
pushforward preserve the property. -/
theorem BivariantClass.CommutesWithEveryClass.bivariantPieceExtension
    {b : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((UY (a w)).ι ≫ sY) (pieceMap f X.connectedComponentOpens UY a ha w)
      (pieceMap_comp_structureMorphism C sX sY f hf X.connectedComponentOpens UY a ha w) n}
    (hb : b.CommutesWithEveryClass) :
    (bivariantPieceExtension C sX sY f hf UY a ha w b).CommutesWithEveryClass :=
  commutesWithEveryClass_bivariantProperPushforward _ _ _ _ _ (by
    rw [bivariantTransport_refl (pieceMap_comp_ι f X.connectedComponentOpens UY a ha w)]
    exact (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2
      ((BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2
        (hb.bivariantCompositeOfInvertible
          (commutesWithEveryClass_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible _))))

/-- **A class on a connected component, extended by zero, restricts to it** (Stacks 0FDZ): the
restriction of `ι_* (b ∘ j^*)` to `X_w ⟶ V` is `b`. On a test scheme, restricting the pushforward
along the open and closed immersion `X_w ×_Y T ⟶ X ×_Y T` to its image undoes it, and restricting
`b ∘ j^*` back to `V` gives `b`. -/
theorem bivariantPieceRestrictionOfInvertible_bivariantPieceExtension
    (b : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((UY (a w)).ι ≫ sY) (pieceMap f X.connectedComponentOpens UY a ha w)
      (pieceMap_comp_structureMorphism C sX sY f hf X.connectedComponentOpens UY a ha w) n) :
    bivariantPieceRestrictionOfInvertible C sX sY f hf n X.connectedComponentOpens UY a ha w
        (bivariantPieceExtension C sX sY f hf UY a ha w b) = b := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {S} s _ k β ↦ ?_
  rw [bivariantPieceRestrictionOfInvertible, bivariantPieceRestriction_cap,
    bivariantPieceRestrictionCap_apply, bivariantPieceExtension,
    bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  set ιX := (X.connectedComponentOpens w).ι
  set ιY := (UY (a w)).ι
  set fw := pieceMap f X.connectedComponentOpens UY a ha w
  set t := s ≫ ιY
  let θ := pullbackCompIsoOfMono (pieceMap_comp_ι f X.connectedComponentOpens UY a ha w) s
  have hθq : θ.hom ≫ opensPullbackComparison f (X.connectedComponentOpens w) (UY (a w)) fw
      (pieceMap_comp_ι f X.connectedComponentOpens UY a ha w) s =
      bivariantPushforwardBaseChange ιX f t :=
    pullbackCompIsoOfMono_hom_opensPullbackComparison _ _ _ _ _ s
  have hθs : θ.hom ≫ (pullback.fst fw s ≫ (ιX ≫ sX)) = pullback.fst (ιX ≫ f) t ≫ (ιX ≫ sX) := by
    rw [pullbackCompIsoOfMono_hom_fst_assoc]
  rw [chowGroupRestrict_properChowPushforward C _ _ _ _ (bivariantPushforwardBaseChange ιX f t) _
    (𝟙 _) (Category.id_comp _) _ _ θ.hom hθs
    (IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hθq]⟩) _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ θ.hom hθs _),
    chowGroupRestrict_id, properChowPushforward_eq_chowPushforwardOfIso, bivariantTransport_cap,
    bivariantTransportCap_apply, chowPushforwardOfIso_comp_apply]
  -- `S ≅ V ×_Y S` along the open immersion `ιY`
  let ψ := isoPullbackCompOfMono ιY s
  apply eq_of_heq
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k _)).trans ?_
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (openImmersionComposite_cap_heq C _ _ _ _ _ _ _ _ b t k _)).trans (heq_of_eq ?_)
  have hγ : chowGroupRestrict C (t ≫ sY) (pullback.fst ιY t ≫ (ιY ≫ sY)) (pullback.snd ιY t)
      (pullbackSnd_comp_structureMorphism rfl t) k
        (chowGroupCongr C (Category.assoc s ιY sY).symm k β) =
      chowPushforwardOfIso C (t ≫ sY) (pullback.fst ιY t ≫ (ιY ≫ sY)) ψ.hom
        (by rw [isoPullbackCompOfMono_hom_fst_assoc, Category.assoc]) k
        (chowGroupCongr C (Category.assoc s ιY sY).symm k β) :=
    chowGroupRestrict_eq_chowPushforwardOfIso_inv C _ _ ψ.symm _ k _
  rw [chowPushforwardOfIso_comp_apply, hγ,
    BivariantClass.cap_chowPushforwardOfIso b (pullback.fst ιY t) ψ.hom s
      (isoPullbackCompOfMono_hom_fst _ _) (t ≫ sY) (Category.assoc s ιY sY) k _ _ β
      (by rw [chowGroupCongr_chowGroupCongr]; rfl),
    chowPushforwardOfIso_comp_apply]
  refine eq_of_heq (chowPushforwardOfIso_heq_of_eq_id _ ?_ _ _)
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Category.assoc, pullbackCompIsoOfMono_hom_fst,
      transportPullbackIso_hom_fst, Iso.refl_hom, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, testBaseChangeIso_hom_fst, Category.id_comp]
  · rw [Category.assoc, Category.assoc, Category.assoc, pullbackCompIsoOfMono_hom_snd,
      transportPullbackIso_hom_snd, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc,
      testBaseChangeIso_hom_snd, Category.assoc, Category.id_comp]
    exact (congrArg (pullback.snd fw s ≫ ·) ψ.hom_inv_id).trans (Category.comp_id _)

end PieceExtension

/-! ### The class of constant rank -/

namespace VirtualNormalBundle

section ConstantRank

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **The class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` of the construction commutes with every bivariant
class**: `j^* ∘ C` does (`Stacks.Deformation.normalConeClass_commutesWithEveryClass`) and proper
pushforward preserves the property. -/
theorem pushforwardClass_commutesWithEveryClass :
    haveI := 𝒩.locallyOfFiniteType_projection r
    (𝒩.pushforwardClass C sX sZ hZ r).CommutesWithEveryClass := by
  have := 𝒩.locallyOfFiniteType_projection r
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  refine (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2 ?_
  refine commutesWithEveryClass_canonicalBivariantProperPushforward _ _ _ _ _ ?_
  exact (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2
    (Stacks.Deformation.normalConeClass_commutesWithEveryClass C sX i)

/-- The flat pullback `p^*` along the vector bundle of `𝒩` has bijective cap operations
(Stacks 02TY). -/
theorem capBijective_pullbackClass :
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩.flat_projection r
    (𝒩.pullbackClass C sZ r).CapBijective :=
  𝒩.capBijective_projectionPullbackClass C sZ i r

/-- **The class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of constant rank commutes with every bivariant class.**
In `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C` the right-hand side commutes with every class
(`Stacks.Chow.VirtualNormalBundle.pushforwardClass_commutesWithEveryClass`), and the left factor
`p^*` commutes with every class and has injective cap operations (Stacks 02TY), so it can be
cancelled. -/
theorem virtualNormalClass_commutesWithEveryClass :
    (𝒩.virtualNormalClass C sX sZ hZ r).CommutesWithEveryClass := by
  subst hZ
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  refine commutesWithEveryClass_of_bivariantCompositeOfInvertible 𝒩.proj i rfl (-(r : ℤ)) r
    (𝒩.pullbackClass C (i ≫ sX) r) _
    (commutesWithEveryClass_flatPullbackBivariantClass rfl r _ (flatPullbackDescends C) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (𝒩.proj ≫ (i ≫ sX))
        (i ≫ sX) 𝒩.proj rfl r (𝒩.relativeDimension_projection r)))
    (BivariantClass.CapBijective.capInjective (𝒩.capBijective_pullbackClass C (i ≫ sX) r)) ?_
  have heq : bivariantCompositeOfInvertible C (𝒩.proj ≫ (i ≫ sX)) (i ≫ sX) sX 𝒩.proj i rfl rfl
      (-(r : ℤ)) r (𝒩.pullbackClass C (i ≫ sX) r) (𝒩.virtualNormalClass C sX (i ≫ sX) rfl r) =
      𝒩.pushforwardClass C sX (i ≫ sX) rfl r :=
    eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
      (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)
      (𝒩.isBivariantClassComposition_virtualNormalClass C sX (i ≫ sX) rfl r)
  rw [heq]
  exact 𝒩.pushforwardClass_commutesWithEveryClass C sX (i ≫ sX) rfl r

end ConstantRank

/-! ### The class of arbitrary rank -/

section Completed

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

/-- The class `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` of a connected component commutes with every class: it is
a class of constant rank. -/
theorem componentClass_commutesWithEveryClass [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (k : _root_.ConnectedComponents Z) :
    (𝒩.componentClass C sX sZ hZ k).CommutesWithEveryClass :=
  (𝒩.restrictComponent k).virtualNormalClass_commutesWithEveryClass C _ _ _ (𝒩.componentRank k)

/-- **The degree `n` part `c_n ∈ A^n(Z ⟶ X)` of `c(Z ⟶ X, 𝒩)` commutes with every bivariant
class.** Commuting is checked on the connected components `Z_k` of `Z`
(`Stacks.Chow.BivariantClass.commutesWithEveryClass_of_connectedComponentRestriction`). On a
component where `𝒩` does not have rank `n` the class restricts to zero. On a component where it
has rank `n`, the class `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` of constant rank, extended by zero, commutes with
every class and has the same restriction to `Z_k ⟶ W_k`, hence to `Z_k ⟶ X_{a(k)}`
(`Stacks.Chow.bivariantPieceRestriction_eq_of_shrink`). -/
theorem degreeClass_commutesWithEveryClass [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (n : ℤ) : (𝒩.degreeClass C sX sZ hZ n).CommutesWithEveryClass := by
  refine BivariantClass.commutesWithEveryClass_of_connectedComponentRestriction
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ fun k ↦ ?_
  by_cases h : (𝒩.componentRank k : ℤ) = n
  · subst h
    refine ⟨bivariantPieceExtension C sZ sX i hZ (componentAmbient i) id
      (le_preimage_componentAmbient i) k (𝒩.componentClass C sX sZ hZ k),
      (𝒩.componentClass_commutesWithEveryClass C sX sZ hZ k).bivariantPieceExtension, ?_⟩
    refine bivariantPieceRestriction_eq_of_shrink C (gysinSystemOfInvertible C) sZ sX i hZ _
      Z.connectedComponentOpens X.connectedComponentOpens i.continuous.connectedComponentsMap
      i.connectedComponentOpens_le_preimage (componentAmbient i) id
      (le_preimage_componentAmbient i) k (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      _ _ ?_
    exact (bivariantPieceRestrictionOfInvertible_bivariantPieceExtension C sZ sX i hZ
      (componentAmbient i) id (le_preimage_componentAmbient i) k _).trans
      ((𝒩.bivariantPieceRestrictionOfInvertible_degreeClass C sX sZ hZ _ k).trans
        (𝒩.componentFamily_rank C sX sZ hZ k)).symm
  · refine ⟨0, BivariantClass.commutesWithEveryClass_zero, ?_⟩
    rw [map_zero, Pi.zero_apply,
      𝒩.bivariantConnectedComponentRestriction_degreeClass_of_ne C sX sZ hZ h]

/-- **Every homogeneous part of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` commutes with every bivariant
class**, in the sense of commuting on completions
(`Stacks.Chow.completedCommutesWithEveryClass`). -/
theorem completedClass_completedCommutesWithEveryClass :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    completedCommutesWithEveryClass C sZ sX i hZ (𝒩.completedClass C sX sZ hZ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  intro n
  rw [completedBivariantSequenceOfInvertible_completedClass]
  exact 𝒩.degreeClass_commutesWithEveryClass C sX sZ hZ n

end Completed

end VirtualNormalBundle

/-! ### Stacks 0FBP -/

section Statement

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Stacks 0FBP.** Let `(S, δ)` be as in Situation 02QL, let `X` be a scheme locally of finite
type over `S`, let `Z ⊆ X` be a closed subscheme with virtual normal sheaf `𝒩`, let `g : Y ⟶ X`
be locally of finite type and let `c ∈ A^p(Y ⟶ X)`. Then `c` and the class
`c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBK commute in the sense of Remark 0FA2: for every
degree `n`, the degree `n` part of `c(Z ⟶ X, 𝒩)` and `c` satisfy
`c(Z ⟶ X, 𝒩)_n ∩ (c ∩ α) = c ∩ (c(Z ⟶ X, 𝒩)_n ∩ α)` in `CH_{k-n-p}(Z ×_X Y ×_X T)` for every
`α ∈ CH_k(T)` and every `T ⟶ X` locally of finite type (`Stacks.Chow.BivariantCommute`). As
commuting is additive in `c`, this is the commutation with every `c ∈ A^*(Y ⟶ X)`.

The rank of `𝒩` is arbitrary. The class is `Stacks.Chow.VirtualNormalBundle.completedClass`, the
class constructed in Stacks 0FBK from the class `C` of Stacks 0F9J, the normal cone and the vector
bundle of `𝒩`; `Z` lies over `S` through `X`. -/
@[stacks 0FBP "c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ of Tag 0FBK commutes (Remark 0FA2) with every \
c ∈ A^p(Y → X), Y → X locally of finite type: each homogeneous part c(Z → X, 𝒩)_n and c commute \
on every test scheme T → X; 𝒩 a virtual normal sheaf of arbitrary rank"]
theorem VirtualNormalBundle.completedClass_bivariantCommute (𝒩 : VirtualNormalBundle i)
    {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl p) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    BivariantCommute C (gysinSystemOfInvertible C) sX i g n p
      (completedBivariantSequenceOfInvertible C (i ≫ sX) sX i rfl
        (𝒩.completedClass C sX (i ≫ sX) rfl) n) c := by
  have := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  intro T t _ k α
  exact (BivariantClass.commutesWithEveryClass_iff _).1
    (𝒩.completedClass_completedCommutesWithEveryClass C sX (i ≫ sX) rfl n) g p c t k α

end Statement

end Stacks.Chow

end
