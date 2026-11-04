module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentLift
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem
import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedImmersionCoverExactSequence

/-!
# Bivariant classes extended from one member of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme locally
of finite type over `S`, and let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions whose images
cover `X`. The first paragraph of the proof of Stacks 0F9H turns a class on `X₂` which kills
everything coming from `X₁ ∩ X₂` into a bivariant class `a' ∈ A^p(X₂ ⟶ X)` characterized by

  `a' ∩ i_{2,*} α₂ = a ∩ α₂`   and   `a' ∩ i_{1,*} α₁ = 0`

for `α_j ∈ CH_k(X_j)`, and similarly after every base change `X' ⟶ X` locally of finite type.
The only property of the class used there is that it is a class `a ∈ A^p(X₂) = A^p(X₂ ⟶ X₂)`
whose cap product vanishes on every test scheme lying over `X₁ ×_X X₂`; this file carries out the
construction for every such class.

Given a test scheme `g : T ⟶ X` with base changes `j_ν : T ×_X X_ν ⟶ T`, every `α ∈ CH_k(T)` is
`j_{1,*} α₁ + j_{2,*} α₂` by Stacks 0F94, and `α₂` is well defined up to classes pushed forward
from `(T ×_X X₁) ×_T (T ×_X X₂)`, which lies over `X₁ ×_X X₂`. So `a' ∩ α = a ∩ α₂` is well
defined, and it is a bivariant class: each of the three conditions of Stacks 0B76 reduces, along
the same decomposition, to the corresponding condition for `a`.

## Main definitions

* `Stacks.Chow.BivariantClass.VanishesOver` — a class `a ∈ A^p(Z)` vanishes over `z : W ⟶ Z`
  when it caps to zero on every test scheme factoring through `z`.
* `Stacks.Chow.closedCoverExtensionCap` — the cap operation `α ↦ a ∩ α₂` of the extension.
* `Stacks.Chow.closedCoverExtension` — the extension `a' ∈ A^p(X₂ ⟶ X)`.
* `Stacks.Chow.IsClosedCoverExtension` — the two formulas characterizing the extension, on every
  test scheme over `X`.
* `Stacks.Chow.vanishesOverAddSubgroup`, `Stacks.Chow.closedCoverExtensionAddHom` — the extension
  as a homomorphism of groups.

## Main results

* `Stacks.Chow.BivariantClass.idRule_chowPush`,
  `Stacks.Chow.BivariantClass.idRule_flatPullbackChow`,
  `Stacks.Chow.BivariantClass.idRule_gysin` — the three conditions of Stacks 0B76 for a class of
  `A^p(Z)`, read on the test schemes themselves.
* `Stacks.Chow.chowCohomologyRestriction_eq_zero_iff_vanishesOver` — vanishing over `z : W ⟶ Z`
  is the vanishing of the restriction of Stacks 0B7F to `W`.
* `Stacks.Chow.closedCoverExtensionCap_proper_naturality`,
  `Stacks.Chow.closedCoverExtensionCap_flat_naturality`,
  `Stacks.Chow.closedCoverExtensionCap_gysin_naturality` — the three conditions of Stacks 0B76 for
  the extension.
* `Stacks.Chow.closedCoverExtension_cap_second`, `Stacks.Chow.closedCoverExtension_cap_first` — the
  two characterizing formulas.
* `Stacks.Chow.IsClosedCoverExtension.eq_closedCoverExtension`,
  `Stacks.Chow.existsUnique_isClosedCoverExtension` — the formulas determine the extension.
* `Stacks.Chow.closedCoverExtension_add`, `_neg`, `_sub`, `_zero` — the extension is additive.
* `Stacks.Chow.closedCoverExtension_eq_of_closedCover` — the extension does not depend on the
  first member of the cover.
* `Stacks.Chow.bivariantRestriction_closedCoverExtension` — the restriction (Stacks 0F9Z) of the
  extension along `X' ⟶ X` is the extension of the restriction along the base-changed cover.

## Implementation notes

The structure morphism of `X₂` is an arbitrary `sX₂` with `i₂ ≫ sX = sX₂`; the case of the
source is `sX₂ = i₂ ≫ sX`.

The cap operation is the homomorphism induced on `CH_k(T)` by `(α₁, α₂) ↦ a ∩ α₂` along the
surjective sum of pushforwards (`AddMonoidHom.liftOfSurjective`); its kernel condition is the
exactness statement of Stacks 0F94 for two closed immersions together with the vanishing of `a`.
The formula `a' ∩ e_* γ = h_*(a ∩ γ)` is proved for every proper `e : T₀ ⟶ T` whose composite with
the test morphism factors through `X₂`, and `a' ∩ e_* γ = 0` for every one factoring through
`X₁`; every condition of Stacks 0B76 is then a short computation on the two summands, using
Stacks 02RG for the flat condition and Stacks 02TA for the Gysin condition.

The cap product of `a` on a test scheme `T ⟶ X₂` lands in the Chow group of `X₂ ×_{X₂} T`, and is
read on `T` through the projection, as `Stacks.Chow.BivariantClass.idRule`. The proper and flat
conditions hold for every Gysin system; the Gysin condition uses Stacks 02TA for the Gysin system
of the first Chern class rule, at which the extension is constructed.

## References

* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The operation of a Chow cohomology class on the test schemes -/

section IdentityRule

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] {p : ℤ}

/-- **Stacks 0B76 (1), read on the test schemes.** The operation of a class `a ∈ A^p(Z)` commutes
with proper pushforward along a morphism `h : T' ⟶ T` of test schemes over `Z`, the structure
morphism of `T'` being presented by an equality `h ≫ g = m`. -/
theorem BivariantClass.idRule_chowPush
    (a : BivariantClass C G sZ sZ (𝟙 Z) (Category.id_comp sZ) p) {T T' : Scheme.{u}}
    (g : T ⟶ Z) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (m : T' ⟶ Z)
    [LocallyOfFiniteType m] (hm : h ≫ g = m) (k : ℤ) (x : chowGroup C (m ≫ sZ) k) :
    a.idRule C sZ G g k (chowPush C (m ≫ sZ) (g ≫ sZ) h (by rw [← hm, Category.assoc]) k x) =
      chowPush C (m ≫ sZ) (g ≫ sZ) h (by rw [← hm, Category.assoc]) (k - p)
        (a.idRule C sZ G m k x) := by
  subst hm
  exact a.idRule_properNaturality C sZ G g h k _ _ x

/-- **Stacks 0B76 (2), read on the test schemes.** The operation of a class `a ∈ A^p(Z)` commutes
with flat pullback along a flat morphism `h : T' ⟶ T` of test schemes over `Z` of relative
dimension `r`, the structure morphism of `T'` being presented by an equality `h ≫ g = m`. The two
sides lie in the Chow groups of degrees `(k + r) - p` and `(k - p) + r`. -/
theorem BivariantClass.idRule_flatPullbackChow
    (a : BivariantClass C G sZ sZ (𝟙 Z) (Category.id_comp sZ) p) {T T' : Scheme.{u}}
    (g : T ⟶ Z) [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (m : T' ⟶ Z) [LocallyOfFiniteType m]
    (hm : h ≫ g = m) (k : ℤ) (x : chowGroup C (g ≫ sZ) k) :
    HEq (a.idRule C sZ G m (k + (r : ℤ))
        (flatPullbackChow C (m ≫ sZ) (g ≫ sZ) h (by rw [← hm, Category.assoc]) r hr k
          (flatPullbackDescends C _ _ _ _ r hr k) x))
      (flatPullbackChow C (m ≫ sZ) (g ≫ sZ) h (by rw [← hm, Category.assoc]) r hr (k - p)
        (flatPullbackDescends C _ _ _ _ r hr (k - p)) (a.idRule C sZ G g k x)) := by
  subst hm
  set h' := bivariantBaseChangeMap (𝟙 Z) g h
  have sq := isPullback_bivariantBaseChangeMap (𝟙 Z) g h
  have hfst : h' ≫ pullback.fst (𝟙 Z) g = pullback.fst (𝟙 Z) (h ≫ g) :=
    bivariantBaseChangeMap_fst (𝟙 Z) g h
  let : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  let : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hr' : AlgebraicGeometry.RelativeDimension h' r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  have hflat := a.flat_naturality g h r hr h' sq hfst k hr'
    (flatPullbackDescends C _ _ _ _ r hr k) (flatPullbackDescends C _ _ _ _ r hr' (k - p)) x
  have hpush := heq_map_index (by omega : (k + (r : ℤ)) - p = (k - p) + (r : ℤ)) hflat
    (fun n ↦ pullbackSndPush C sZ (Category.id_comp sZ) (h ≫ g) n)
  refine hpush.trans (heq_of_eq ?_)
  have hRG := flatPullbackChow_properChowPushforward_of_isProper C
    (pullback.fst (𝟙 Z) g ≫ sZ) (g ≫ sZ) (pullback.fst (𝟙 Z) (h ≫ g) ≫ sZ) ((h ≫ g) ≫ sZ)
    (pullback.snd (𝟙 Z) g) h h' (pullback.snd (𝟙 Z) (h ≫ g)) sq.flip
    (pullbackSnd_comp_structureMorphism (Category.id_comp sZ) g) (by rw [Category.assoc])
    (by rw [← Category.assoc, hfst]) r hr (k - p) (a.cap g k x)
  exact hRG.symm

/-- If the cap product of a class `a ∈ A^p(Z)` on a test scheme `m : T ⟶ Z` kills a class, so
does the operation of `a` on `T`. -/
theorem BivariantClass.idRule_eq_zero_of_cap_eq_zero
    (a : BivariantClass C G sZ sZ (𝟙 Z) (Category.id_comp sZ) p) {T : Scheme.{u}} (m : T ⟶ Z)
    [LocallyOfFiniteType m] (k : ℤ) (x : chowGroup C (m ≫ sZ) k) (hx : a.cap m k x = 0) :
    a.idRule C sZ G m k x = 0 := by
  rw [BivariantClass.idRule_apply, hx, map_zero]

/-- If the operation of a class `a ∈ A^p(Z)` on a test scheme `m : T ⟶ Z` kills a class, so does
the cap product of `a`. -/
private theorem BivariantClass.cap_eq_zero_of_idRule_eq_zero
    (a : BivariantClass C G sZ sZ (𝟙 Z) (Category.id_comp sZ) p) {T : Scheme.{u}} (m : T ⟶ Z)
    [LocallyOfFiniteType m] (k : ℤ) (x : chowGroup C (m ≫ sZ) k)
    (hx : a.idRule C sZ G m k x = 0) : a.cap m k x = 0 :=
  chowPushforwardOfIso_injective C _ _ (pullback.snd (𝟙 Z) m)
    (pullbackSnd_comp_structureMorphism (Category.id_comp _) m) (k - p)
    (hx.trans (map_zero _).symm)

/-- **Stacks 0B76 (3), read on the test schemes.** The operation of a class `a ∈ A^p(Z)`, for the
Gysin system of the first Chern class rule, commutes with the Gysin map of the zero scheme `D` of a
section `s` of an invertible module on a test scheme `w : P ⟶ Z`. The two sides lie in the Chow
groups of degrees `(k + 1) - p` and `(k - p) + 1`.

This is the Gysin axiom of `a` read through the base-change isomorphisms `Z ×_Z P ≅ P` and
`Z ×_Z D ≅ D`; the comparison of the Gysin map on `Z ×_Z P` with the one on `P` is Stacks 02TA for
the isomorphism `Z ×_Z P ⟶ P`. -/
theorem BivariantClass.idRule_gysin
    (a : BivariantClass C (gysinSystemOfInvertible C) sZ sZ (𝟙 Z) (Category.id_comp sZ) p)
    {P : Scheme.{u}} (w : P ⟶ Z) [LocallyOfFiniteType w] (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (β : chowGroup C (w ≫ sZ) (k + 1)) :
    a.idRule C sZ (gysinSystemOfInvertible C) ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ w)
        k ((gysinSystemOfInvertible C).onChow (w ≫ sZ) L s k β) =
      (gysinSystemOfInvertible C).onChow (w ≫ sZ) L s (k - p)
        (Eq.mp (congrArg (chowGroup C (w ≫ sZ)) (by omega : (k + 1) - p = (k - p) + 1))
          (a.idRule C sZ (gysinSystemOfInvertible C) w (k + 1) β)) := by
  have hidx : (k + 1) - p = (k - p) + 1 := by omega
  have hu : pullback.snd (𝟙 Z) w ≫ (w ≫ sZ) = pullback.fst (𝟙 Z) w ≫ sZ :=
    pullbackSnd_comp_structureMorphism (Category.id_comp sZ) w
  have he := bivariantDivisorBaseChangeIso_hom_subschemeι (𝟙 Z) w L s
  have hbase : (bivariantDivisorBaseChangeIso (𝟙 Z) w L s).hom ≫
      ((pullbackZeroScheme (pullback.snd (𝟙 Z) w) L s).subschemeι ≫
        pullback.fst (𝟙 Z) w ≫ sZ) =
      pullback.fst (𝟙 Z) ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ w) ≫ sZ := by
    rw [← Category.assoc, he, ← Category.assoc, bivariantBaseChangeMap_fst]
  have hR1 : Eq.mp (congrArg (chowGroup C (w ≫ sZ)) hidx)
      (a.idRule C sZ (gysinSystemOfInvertible C) w (k + 1) β) =
      chowPush C _ _ (pullback.snd (𝟙 Z) w) hu ((k - p) + 1)
        (Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 Z) w ≫ sZ)) hidx) (a.cap w (k + 1) β)) := by
    rw [BivariantClass.idRule_apply]
    exact properChowPushforward_cast C _ _ _ hu hidx (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) _
  have hR2 := gysinSystemOfInvertible_isNaturalUnderProperPushforward C
    (pullback.fst (𝟙 Z) w ≫ sZ) (w ≫ sZ) (pullback.snd (𝟙 Z) w) hu L s (k - p)
    (zeroSchemePullbackHom (pullback.snd (𝟙 Z) w) L s)
    (zeroSchemePullbackHom_subschemeι (pullback.snd (𝟙 Z) w) L s)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 Z) w ≫ sZ)) hidx) (a.cap w (k + 1) β))
  have hR3 := a.gysin_naturality w L s k (bivariantDivisorBaseChangeIso (𝟙 Z) w L s) he hbase
    (properPushforwardDescends C _ _ _ _ _) β
  have huv : (bivariantDivisorBaseChangeIso (𝟙 Z) w L s).hom ≫
      zeroSchemePullbackHom (pullback.snd (𝟙 Z) w) L s =
      pullback.snd (𝟙 Z) ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ w) := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme P L s).subschemeι).1 ?_
    rw [Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc, he]
    simp [bivariantBaseChangeMap]
  rw [hR1, hR2, ← hR3]
  exact properChowPushforward_comp_apply C _ _ _ (bivariantDivisorBaseChangeIso (𝟙 Z) w L s).hom
    (zeroSchemePullbackHom (pullback.snd (𝟙 Z) w) L s)
    (pullback.snd (𝟙 Z) ((Stacks.Divisors.zeroScheme P L s).subschemeι ≫ w)) huv _ _ _ (k - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _

end IdentityRule

/-! ### Vanishing over a morphism -/

section Vanishing

variable {C : ChowSituation.{u}} {G : GysinSystem C} {Z W : Scheme.{u}} {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ] {p : ℤ}

/-- A class `a ∈ A^p(Z)` *vanishes over* a morphism `z : W ⟶ Z` when its cap product is zero on
every test scheme over `Z` whose structure morphism factors through `z`. Equivalently, the
restriction of `a` to `W` (Stacks 0B7F) is zero; see
`Stacks.Chow.chowCohomologyRestriction_eq_zero_iff_vanishesOver`. -/
def BivariantClass.VanishesOver (a : chowCohomologyComponent C G sZ p) (z : W ⟶ Z)
    [LocallyOfFiniteType z] : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C ((t ≫ z) ≫ sZ) k), a.cap (t ≫ z) k α = 0

/-- A class vanishing over `z` caps to zero on every test scheme whose structure morphism is
presented as a composite through `z`. -/
theorem BivariantClass.VanishesOver.cap_eq_zero {a : chowCohomologyComponent C G sZ p}
    {z : W ⟶ Z} [LocallyOfFiniteType z] (ha : BivariantClass.VanishesOver a z) {T : Scheme.{u}}
    (t : T ⟶ W) (m : T ⟶ Z) [LocallyOfFiniteType m] (hm : t ≫ z = m) (k : ℤ)
    (x : chowGroup C (m ≫ sZ) k) :
    a.cap m k x = 0 := by
  subst hm
  have : LocallyOfFiniteType t := locallyOfFiniteType_of_comp t z
  exact ha t k x

/-- A class vanishing over `z` has vanishing operation on every test scheme whose structure
morphism is presented as a composite through `z`. -/
theorem BivariantClass.VanishesOver.idRule_eq_zero {a : chowCohomologyComponent C G sZ p}
    {z : W ⟶ Z} [LocallyOfFiniteType z] (ha : BivariantClass.VanishesOver a z) {T : Scheme.{u}}
    (t : T ⟶ W) (m : T ⟶ Z) [LocallyOfFiniteType m] (hm : t ≫ z = m) (k : ℤ)
    (x : chowGroup C (m ≫ sZ) k) :
    a.idRule C sZ G m k x = 0 :=
  a.idRule_eq_zero_of_cap_eq_zero C G sZ m k x (ha.cap_eq_zero t m hm k x)

namespace BivariantClass.VanishesOver

variable {z : W ⟶ Z} [LocallyOfFiniteType z]

/-- The zero class vanishes over every morphism. -/
theorem zero : BivariantClass.VanishesOver (0 : chowCohomologyComponent C G sZ p) z := by
  intro T t _ k α
  exact BivariantClass.zero_cap C G sZ sZ (𝟙 Z) (Category.id_comp sZ) p (t ≫ z) k α

/-- A sum of classes vanishing over `z` vanishes over `z`. -/
theorem add {a b : chowCohomologyComponent C G sZ p} (ha : BivariantClass.VanishesOver a z)
    (hb : BivariantClass.VanishesOver b z) : BivariantClass.VanishesOver (a + b) z := by
  intro T t _ k α
  rw [BivariantClass.add_cap, ha t k α, hb t k α, add_zero]

/-- The negation of a class vanishing over `z` vanishes over `z`. -/
theorem neg {a : chowCohomologyComponent C G sZ p} (ha : BivariantClass.VanishesOver a z) :
    BivariantClass.VanishesOver (-a) z := by
  intro T t _ k α
  rw [BivariantClass.neg_cap, ha t k α, neg_zero]

/-- A difference of classes vanishing over `z` vanishes over `z`. -/
theorem sub {a b : chowCohomologyComponent C G sZ p} (ha : BivariantClass.VanishesOver a z)
    (hb : BivariantClass.VanishesOver b z) : BivariantClass.VanishesOver (a - b) z := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

end BivariantClass.VanishesOver

variable (C G sZ p) in
/-- The subgroup of `A^p(Z)` of the classes vanishing over a morphism `z : W ⟶ Z`. -/
def vanishesOverAddSubgroup (z : W ⟶ Z) [LocallyOfFiniteType z] :
    AddSubgroup (chowCohomologyComponent C G sZ p) where
  carrier := {a | BivariantClass.VanishesOver a z}
  add_mem' ha hb := BivariantClass.VanishesOver.add ha hb
  zero_mem' := BivariantClass.VanishesOver.zero
  neg_mem' ha := BivariantClass.VanishesOver.neg ha

end Vanishing

/-! ### The cap operation of the extension -/

/-- A morphism into a fibre product along a separated morphism is proper as soon as its second
component is: composed with the separated second projection it is that component. -/
instance isProper_pullbackLift {A B D E : Scheme.{u}} (f : A ⟶ D) (g : B ⟶ D) [IsSeparated f]
    (a : E ⟶ A) (b : E ⟶ B) [IsProper b] (h : a ≫ f = b ≫ g) :
    IsProper (pullback.lift a b h) := by
  have : IsProper (pullback.lift a b h ≫ pullback.snd f g) := by
    rw [pullback.lift_snd]; infer_instance
  exact IsProper.of_comp _ (pullback.snd f g)

section ClosedCover

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂) {p : ℤ}

/-- On a test scheme `g : T ⟶ X`, the sum of the pushforwards
`A_k(T ×_X X₁) × A_k(T ×_X X₂) ⟶ A_k(T)` along the two members of the base-changed cover. -/
def closedCoverPullbackSum {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k ×
        chowGroup C (pullback.fst i₂ g ≫ sX₂) k →+
      chowGroup C (g ≫ sX) k :=
  (chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k).coprod
    (chowPush C _ _ (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism hi₂ g) k)

/-- The sum of the pushforwards, read on a pair of classes. -/
theorem closedCoverSum_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (x : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k ×
      chowGroup C (pullback.fst i₂ g ≫ sX₂) k) :
    closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ g k x =
      chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k x.1 +
        chowPush C _ _ (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism hi₂ g) k x.2 :=
  rfl

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- The images of the two members of the base change of a closed cover to a test scheme cover
the test scheme. -/
theorem range_pullbackSnd_union_eq_univ (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {T : Scheme.{u}} (g : T ⟶ X) :
    Set.range (pullback.snd i₁ g) ∪ Set.range (pullback.snd i₂ g) = Set.univ := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hcover,
    Set.preimage_univ]

/-- **Stacks 0F94** on a test scheme: every class on `T` is the sum of the pushforwards of classes
on the two members `T ×_X X₁` and `T ×_X X₂` of the base-changed cover. -/
theorem surjective_closedCoverPullbackSum (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    Function.Surjective (closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ g k) :=
  surjective_chowPushforwardOfIsClosedImmersion_coprod C (g ≫ sX) (pullback.snd i₁ g)
    (pullback.snd i₂ g) _ _ (pullbackSnd_comp_structureMorphism rfl g)
    (pullbackSnd_comp_structureMorphism hi₂ g) k (range_pullbackSnd_union_eq_univ i₁ i₂ hcover g)

/-- The operation of a class `a ∈ A^p(X₂)` vanishing over `X₁ ×_X X₂ ⟶ X₂` kills the
`X₂`-component of every pair of classes whose pushforwards to a test scheme cancel. This is the
well-definedness of the extension: by **Stacks 0F94** such a pair comes from
`T ×_X X₁ ×_T T ×_X X₂`, which lies over `X₁ ×_X X₂`. -/
theorem idRule_snd_eq_zero_of_closedCoverSum_eq_zero
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {a : chowCohomologyComponent C G sX₂ p}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ)
    (x : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k ×
      chowGroup C (pullback.fst i₂ g ≫ sX₂) k)
    (hx : closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ g k x = 0) :
    a.idRule C sX₂ G (pullback.fst i₂ g) k x.2 = 0 := by
  set j₁ := pullback.snd i₁ g
  set j₂ := pullback.snd i₂ g
  obtain ⟨γ, hγ⟩ := (exact_chowPushforwardOfIsClosedImmersion_prod_coprod C (g ≫ sX) j₁ j₂ _ _
    (pullbackSnd_comp_structureMorphism rfl g) (pullbackSnd_comp_structureMorphism hi₂ g) k
    (range_pullbackSnd_union_eq_univ i₁ i₂ hcover g) x).mp hx
  have hx₂ := congrArg Prod.snd hγ
  change -chowPush C _ _ (pullback.snd j₁ j₂) _ k γ = x.2 at hx₂
  rw [← hx₂]
  set m : pullback j₁ j₂ ⟶ X₂ := pullback.snd j₁ j₂ ≫ pullback.fst i₂ g with hm
  have hγs : pullback.fst j₁ j₂ ≫ (pullback.fst i₁ g ≫ (i₁ ≫ sX)) = m ≫ sX₂ := by
    rw [← pullbackSnd_comp_structureMorphism_eq_fst C (g ≫ sX) j₁ j₂ _ _
      (pullbackSnd_comp_structureMorphism rfl g) (pullbackSnd_comp_structureMorphism hi₂ g),
      hm, Category.assoc]
  have hpush : chowPush C _ _ (pullback.snd j₁ j₂)
      (pullbackSnd_comp_structureMorphism_eq_fst C (g ≫ sX) j₁ j₂ _ _
        (pullbackSnd_comp_structureMorphism rfl g) (pullbackSnd_comp_structureMorphism hi₂ g))
      k γ =
      chowPush C (m ≫ sX₂) _ (pullback.snd j₁ j₂) (by rw [hm, Category.assoc]) k
        (chowGroupCongr C hγs k γ) :=
    properChowPushforward_chowGroupCongr C hγs rfl _ _ _ k
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) γ
  have hlift : (pullback.fst j₁ j₂ ≫ pullback.fst i₁ g) ≫ i₁ =
      (pullback.snd j₁ j₂ ≫ pullback.fst i₂ g) ≫ i₂ := by
    have e₁ : pullback.fst i₁ g ≫ i₁ = j₁ ≫ g := pullback.condition
    have e₂ : pullback.fst i₂ g ≫ i₂ = j₂ ≫ g := pullback.condition
    simp only [Category.assoc, e₁, e₂]
    exact pullback.condition_assoc g
  rw [map_neg, hpush, a.idRule_chowPush C G sX₂ (pullback.fst i₂ g) (pullback.snd j₁ j₂) m
    rfl k, ha.idRule_eq_zero (pullback.lift _ _ hlift) m (pullback.lift_snd _ _ _) k,
    map_zero, neg_zero]

variable {a : chowCohomologyComponent C G sX₂ p}

/-- **The cap operation of the extension.** On a test scheme `g : T ⟶ X`, a class is written as
`j₁_* α₁ + j₂_* α₂` along the two members of the base-changed cover (Stacks 0F94), and the cap
product is the operation of `a` on `α₂`; it is well defined by
`Stacks.Chow.idRule_snd_eq_zero_of_closedCoverSum_eq_zero`. -/
def closedCoverExtensionCap (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst i₂ g ≫ sX₂) (k - p) :=
  (closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ g k).liftOfSurjective
    (surjective_closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ hcover g k)
    ⟨(a.idRule C sX₂ G (pullback.fst i₂ g) k).comp (AddMonoidHom.snd _ _), fun x hx ↦
      (AddMonoidHom.mem_ker).mpr (idRule_snd_eq_zero_of_closedCoverSum_eq_zero C G sX i₁ i₂ sX₂ hi₂
        hcover ha g k x ((AddMonoidHom.mem_ker).mp hx))⟩

/-- The cap operation of the extension on a decomposed class. -/
theorem closedCoverExtensionCap_closedCoverSum (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ)
    (x : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k ×
      chowGroup C (pullback.fst i₂ g ≫ sX₂) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ g k x) =
      a.idRule C sX₂ G (pullback.fst i₂ g) k x.2 :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- The cap operation of the extension is the operation of `a` on classes pushed forward from the
second member `T ×_X X₂` of the base-changed cover. -/
theorem closedCoverExtensionCap_second (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C _ _ (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism hi₂ g) k α) =
      a.idRule C sX₂ G (pullback.fst i₂ g) k α := by
  have h := closedCoverExtensionCap_closedCoverSum C G sX i₁ i₂ sX₂ hi₂ hcover ha g k (0, α)
  rwa [closedCoverSum_apply, map_zero, zero_add] at h

/-- The cap operation of the extension kills the classes pushed forward from the first member
`T ×_X X₁` of the base-changed cover. -/
theorem closedCoverExtensionCap_first (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k α) =
      0 := by
  have h := closedCoverExtensionCap_closedCoverSum C G sX i₁ i₂ sX₂ hi₂ hcover ha g k (α, 0)
  rwa [closedCoverSum_apply, map_zero, add_zero, map_zero] at h

/-- **The cap operation of the extension on classes from schemes over `X₂`.** For a proper
`e : T₀ ⟶ T` whose composite with the test morphism factors as `m ≫ i₂`, the cap product of
`e_* γ` is the pushforward of the operation of `a` on `γ` along the induced morphism
`T₀ ⟶ T ×_X X₂`. -/
theorem closedCoverExtensionCap_chowPush_second (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T₀ : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ X₂) [LocallyOfFiniteType m]
    (hm : m ≫ i₂ = e ≫ g) (k : ℤ) (γ : chowGroup C (m ≫ sX₂) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C _ _ e (by rw [← hi₂, ← Category.assoc, ← hm, Category.assoc]) k γ) =
      chowPush C _ _ (pullback.lift m e hm) (by rw [← Category.assoc, pullback.lift_fst]) (k - p)
        (a.idRule C sX₂ G m k γ) := by
  rw [← chowPush_comp C _ _ _ (pullback.lift m e hm) (pullback.snd i₂ g) e (pullback.lift_snd _ _ _)
    (by rw [← Category.assoc, pullback.lift_fst]) (pullbackSnd_comp_structureMorphism hi₂ g),
    closedCoverExtensionCap_second]
  exact a.idRule_chowPush C G sX₂ (pullback.fst i₂ g) (pullback.lift m e hm) m
    (pullback.lift_fst _ _ _) k γ

/-- **The cap operation of the extension on classes from schemes over `X₁`.** For a proper
`e : T₀ ⟶ T` whose composite with the test morphism factors as `m ≫ i₁`, the cap product of
`e_* γ` vanishes. -/
theorem closedCoverExtensionCap_chowPush_first (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T₀ : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ X₁) [LocallyOfFiniteType m]
    (hm : m ≫ i₁ = e ≫ g) (k : ℤ) (γ : chowGroup C (m ≫ (i₁ ≫ sX)) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C _ _ e (by rw [← Category.assoc, ← hm, Category.assoc]) k γ) = 0 := by
  rw [← chowPush_comp C _ _ _ (pullback.lift m e hm) (pullback.snd i₁ g) e (pullback.lift_snd _ _ _)
    (by rw [← Category.assoc, pullback.lift_fst]) (pullbackSnd_comp_structureMorphism rfl g),
    closedCoverExtensionCap_first]

/-- The cap operation of the extension on a test scheme presented as a composite `t ≫ g` is
additive on the Chow group of `T'` read through `t ≫ (g ≫ sX)`. -/
theorem closedCoverExtensionCap_comp_add (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (t : T' ⟶ T) [LocallyOfFiniteType t] (k : ℤ)
    (x y : chowGroup C (t ≫ (g ≫ sX)) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) k (x + y) =
      closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) k x +
        closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) k y :=
  map_add _ x y

/-- `Stacks.Chow.closedCoverExtensionCap_chowPush_first` on a test scheme presented as a composite
`t ≫ g`, for a pushforward along `e : T₀ ⟶ T'` from an arbitrary structure morphism of `T₀`. -/
theorem closedCoverExtensionCap_comp_properChowPushforward_first
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T' T₀ : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (t : T' ⟶ T) [LocallyOfFiniteType t] (e : T₀ ⟶ T') [IsProper e]
    (sT₀ : T₀ ⟶ C.S) [LocallyOfFiniteType sT₀] (hse : e ≫ (t ≫ (g ≫ sX)) = sT₀)
    (m : T₀ ⟶ X₁) [LocallyOfFiniteType m] (hm : m ≫ i₁ = e ≫ t ≫ g) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sT₀ (t ≫ (g ≫ sX)) e hse k)
    (γ : chowGroup C sT₀ k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) k
        (properChowPushforward C sT₀ (t ≫ (g ≫ sX)) e hse k hfac γ) = 0 := by
  have hγ : m ≫ (i₁ ≫ sX) = sT₀ := by
    rw [← hse, ← Category.assoc, hm]
    simp only [Category.assoc]
  subst hγ
  exact closedCoverExtensionCap_chowPush_first C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) e m hm k γ

/-- `Stacks.Chow.closedCoverExtensionCap_chowPush_second` on a test scheme presented as a
composite `t ≫ g`, for a pushforward along `e : T₀ ⟶ T'` and a morphism `T₀ ⟶ X₂` presented as a
composite `w ≫ v`. -/
theorem closedCoverExtensionCap_comp_properChowPushforward_second
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T' T₀ W : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (t : T' ⟶ T) [LocallyOfFiniteType t] (e : T₀ ⟶ T')
    [IsProper e] (w : T₀ ⟶ W) [LocallyOfFiniteType w] (v : W ⟶ X₂) [LocallyOfFiniteType v]
    (hm : (w ≫ v) ≫ i₂ = e ≫ t ≫ g) (hse : e ≫ (t ≫ (g ≫ sX)) = w ≫ (v ≫ sX₂)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (w ≫ (v ≫ sX₂))
      (t ≫ (g ≫ sX)) e hse k)
    (γ : chowGroup C (w ≫ (v ≫ sX₂)) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) k
        (properChowPushforward C (w ≫ (v ≫ sX₂)) (t ≫ (g ≫ sX)) e hse k hfac γ) =
      chowPush C ((w ≫ v) ≫ sX₂) (pullback.fst i₂ (t ≫ g) ≫ sX₂)
        (pullback.lift (w ≫ v) e hm) (by rw [← Category.assoc, pullback.lift_fst]) (k - p)
        (a.idRule C sX₂ G (w ≫ v) k γ) :=
  closedCoverExtensionCap_chowPush_second C G sX i₁ i₂ sX₂ hi₂ hcover ha (t ≫ g) e (w ≫ v) hm k γ

/-- The cap operation of the extension on the pushforward along a proper `h : T' ⟶ T` of a
decomposed class on `T'`: only the second component contributes. -/
private theorem closedCoverExtensionCap_chowPush_closedCoverSum
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (k : ℤ)
    (x : chowGroup C (pullback.fst i₁ (h ≫ g) ≫ (i₁ ≫ sX)) k ×
      chowGroup C (pullback.fst i₂ (h ≫ g) ≫ sX₂) k) :
    closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C _ _ h (by simp [Category.assoc]) k
          (closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ (h ≫ g) k x)) =
      chowPush C _ _ (pullback.lift (pullback.fst i₂ (h ≫ g)) (pullback.snd i₂ (h ≫ g) ≫ h)
        (by rw [pullback.condition, Category.assoc])) (by rw [← Category.assoc, pullback.lift_fst])
        (k - p) (a.idRule C sX₂ G (pullback.fst i₂ (h ≫ g)) k x.2) := by
  have hm₁ : pullback.fst i₁ (h ≫ g) ≫ i₁ = (pullback.snd i₁ (h ≫ g) ≫ h) ≫ g := by
    rw [pullback.condition, Category.assoc]
  have hm₂ : pullback.fst i₂ (h ≫ g) ≫ i₂ = (pullback.snd i₂ (h ≫ g) ≫ h) ≫ g := by
    rw [pullback.condition, Category.assoc]
  rw [closedCoverSum_apply, map_add, map_add,
    chowPush_comp C _ _ _ (pullback.snd i₁ (h ≫ g)) h _ rfl _ _
      (by rw [← Category.assoc, ← hm₁, Category.assoc]),
    chowPush_comp C _ _ _ (pullback.snd i₂ (h ≫ g)) h _ rfl _ _
      (by rw [← hi₂, ← Category.assoc, ← hm₂, Category.assoc]),
    closedCoverExtensionCap_chowPush_first C G sX i₁ i₂ sX₂ hi₂ hcover ha g _ _ hm₁,
    closedCoverExtensionCap_chowPush_second C G sX i₁ i₂ sX₂ hi₂ hcover ha g _ _ hm₂, zero_add]

/-- **Stacks 0B76 (1) for the extension.** The cap operation of the extension commutes with proper
pushforward along a morphism of test schemes. -/
theorem closedCoverExtensionCap_proper_naturality
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (h' : pullback i₂ (h ≫ g) ⟶ pullback i₂ g)
    (sq : IsPullback (pullback.snd i₂ (h ≫ g)) h' h (pullback.snd i₂ g))
    (hfst : h' ≫ pullback.fst i₂ g = pullback.fst i₂ (h ≫ g)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst i₂ (h ≫ g) ≫ sX₂) (pullback.fst i₂ g ≫ sX₂) h'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((h ≫ g) ≫ sX) k),
      closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
          (properChowPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) k hfac
            α) =
        properChowPushforward C (pullback.fst i₂ (h ≫ g) ≫ sX₂)
          (pullback.fst i₂ g ≫ sX₂) h' (by rw [← Category.assoc, hfst]) (k - p) hfac'
          (closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (h ≫ g) k α) := by
  let : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  intro hfac hfac' α
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ hcover (h ≫ g) k α
  rw [closedCoverExtensionCap_closedCoverSum]
  change closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k
      (chowPush C _ _ h (by simp [Category.assoc]) k
        (closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ (h ≫ g) k (α₁, α₂))) =
    chowPush C _ _ h' (by rw [← Category.assoc, hfst]) (k - p)
      (a.idRule C sX₂ G (pullback.fst i₂ (h ≫ g)) k α₂)
  rw [closedCoverExtensionCap_chowPush_closedCoverSum]
  refine chowPush_congr C _ _ (pullback.hom_ext ?_ ?_) _ _ (k - p) _
  · rw [pullback.lift_fst, hfst]
  · rw [pullback.lift_snd, sq.w]

/-- **Stacks 0B76 (2) for the extension.** The cap operation of the extension commutes with flat
pullback along a morphism of test schemes of fixed relative dimension. -/
theorem closedCoverExtensionCap_flat_naturality
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (h' : pullback i₂ (h ≫ g) ⟶ pullback i₂ g)
    (sq : IsPullback (pullback.snd i₂ (h ≫ g)) h' h (pullback.snd i₂ g))
    (hfst : h' ≫ pullback.fst i₂ g = pullback.fst i₂ (h ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst i₂ (h ≫ g) ≫ sX₂) (pullback.fst i₂ g ≫ sX₂) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (g ≫ sX) k),
      HEq
        (closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha (h ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst i₂ (h ≫ g) ≫ sX₂)
          (pullback.fst i₂ g ≫ sX₂) h' (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
          (closedCoverExtensionCap C G sX i₁ i₂ sX₂ hi₂ hcover ha g k α)) := by
  let : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  let : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  intro hr' hfac hfac' α
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ hcover g k α
  rw [closedCoverExtensionCap_closedCoverSum, closedCoverSum_apply, map_add]
  have h₁ := flatPullbackChow_properChowPushforward_of_isProper C
    (pullback.fst i₁ g ≫ (i₁ ≫ sX)) (g ≫ sX) (pullback.fst i₁ (h ≫ g) ≫ (i₁ ≫ sX))
    ((h ≫ g) ≫ sX) (pullback.snd i₁ g) h (bivariantBaseChangeMap i₁ g h)
    (pullback.snd i₁ (h ≫ g)) (isPullback_bivariantBaseChangeMap i₁ g h).flip
    (pullbackSnd_comp_structureMorphism rfl g) (by rw [Category.assoc])
    (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) r hr k α₁
  have h₂ := flatPullbackChow_properChowPushforward_of_isProper C
    (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.fst i₂ (h ≫ g) ≫ sX₂)
    ((h ≫ g) ≫ sX) (pullback.snd i₂ g) h h' (pullback.snd i₂ (h ≫ g)) sq.flip
    (pullbackSnd_comp_structureMorphism hi₂ g) (by rw [Category.assoc])
    (by rw [← Category.assoc, hfst]) r hr k α₂
  rw [h₁, h₂, map_add, closedCoverExtensionCap_first, closedCoverExtensionCap_second, zero_add]
  exact a.idRule_flatPullbackChow C G sX₂ (pullback.fst i₂ g) h' r hr'
    (pullback.fst i₂ (h ≫ g)) hfst k α₂

end ClosedCover

/-- Pushing a class forward along `l : A ⟶ B` and then along a left inverse `e' : B ⟶ A` of `l`
returns the class, the structure morphism of `A` being read once as `(w ≫ v) ≫ s` and once as
`w ≫ (v ≫ s)`. -/
theorem properChowPushforward_chowPush_of_comp_eq_id (C : ChowSituation.{u}) {A B W V : Scheme.{u}}
    (w : A ⟶ W) [LocallyOfFiniteType w] (v : W ⟶ V) [LocallyOfFiniteType v] (s : V ⟶ C.S)
    [LocallyOfFiniteType s] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (l : A ⟶ B) [IsProper l]
    (e' : B ⟶ A) [IsProper e'] (hle : l ≫ e' = 𝟙 A) (hl : l ≫ sB = (w ≫ v) ≫ s)
    (he : e' ≫ (w ≫ (v ≫ s)) = sB) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sB (w ≫ (v ≫ s)) e' he k)
    (x : chowGroup C ((w ≫ v) ≫ s) k) :
    properChowPushforward C sB (w ≫ (v ≫ s)) e' he k hfac (chowPush C _ sB l hl k x) = x :=
  (properChowPushforward_comp_apply C _ _ _ l e' (𝟙 A) hle hl he (Category.id_comp _) k _ hfac
    (properPushforwardDescends C _ _ _ _ _) x).symm.trans
    (DFunLike.congr_fun (properChowPushforward_id C _ k _) x)

/-! ### The Gysin axiom and the extended class -/

section Extension

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂) {p : ℤ}
  {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}

/-- **Stacks 0B76 (3) for the extension.** The cap operation of the extension commutes with the
Gysin map of every pulled-back divisor. -/
theorem closedCoverExtensionCap_gysin_naturality
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback i₂ g).sheaf.obj
      (pullback i₂ g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd i₂ g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd i₂ g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s
    let E := Stacks.Divisors.zeroScheme (pullback i₂ g) L' s'
    ∀ (e : pullback i₂ (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap i₂ g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst i₂ g ≫ sX₂) =
        pullback.fst i₂ (D.subschemeι ≫ g) ≫ sX₂)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst i₂ (D.subschemeι ≫ g) ≫ sX₂)
        (E.subschemeι ≫ pullback.fst i₂ g ≫ sX₂) e.hom hbase (k - p))
      (α : chowGroup C (g ≫ sX) (k + 1)),
      properChowPushforward C (pullback.fst i₂ (D.subschemeι ≫ g) ≫ sX₂)
          (E.subschemeι ≫ pullback.fst i₂ g ≫ sX₂) e.hom hbase (k - p) hfac
          (closedCoverExtensionCap C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha
            (D.subschemeι ≫ g) k ((gysinSystemOfInvertible C).onChow (g ≫ sX) L s k α)) =
        (gysinSystemOfInvertible C).onChow (pullback.fst i₂ g ≫ sX₂) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst i₂ g ≫ sX₂))
            (by omega : (k + 1) - p = (k - p) + 1))
            (closedCoverExtensionCap C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha g
              (k + 1) α)) := by
  intro D L' s' E e he hbase hfac α
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ hcover g (k + 1) α
  rw [closedCoverExtensionCap_closedCoverSum,
    ← a.idRule_gysin C sX₂ (pullback.fst i₂ g) L' s' k α₂]
  have hm₁ : ((pullbackZeroScheme (pullback.snd i₁ g) L s).subschemeι ≫ pullback.fst i₁ g) ≫ i₁ =
      zeroSchemePullbackHom (pullback.snd i₁ g) L s ≫ D.subschemeι ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
      zeroSchemePullbackHom_subschemeι]
  have hm₂ : (E.subschemeι ≫ pullback.fst i₂ g) ≫ i₂ =
      zeroSchemePullbackHom (pullback.snd i₂ g) L s ≫ D.subschemeι ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
      zeroSchemePullbackHom_subschemeι]
  rw [closedCoverSum_apply, map_add,
    gysinSystemOfInvertible_isNaturalUnderProperPushforward C _ _ (pullback.snd i₁ g)
      (pullbackSnd_comp_structureMorphism rfl g) L s k
      (zeroSchemePullbackHom (pullback.snd i₁ g) L s) (zeroSchemePullbackHom_subschemeι _ L s)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    gysinSystemOfInvertible_isNaturalUnderProperPushforward C _ _ (pullback.snd i₂ g)
      (pullbackSnd_comp_structureMorphism hi₂ g) L s k
      (zeroSchemePullbackHom (pullback.snd i₂ g) L s) (zeroSchemePullbackHom_subschemeι _ L s)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    closedCoverExtensionCap_comp_add,
    closedCoverExtensionCap_comp_properChowPushforward_first C (gysinSystemOfInvertible C) sX i₁ i₂
      sX₂ hi₂ hcover ha g D.subschemeι _ _ _ _ hm₁,
    closedCoverExtensionCap_comp_properChowPushforward_second C (gysinSystemOfInvertible C) sX i₁
      i₂ sX₂ hi₂ hcover ha g D.subschemeι _ E.subschemeι (pullback.fst i₂ g) hm₂, zero_add]
  have hid : pullback.lift (E.subschemeι ≫ pullback.fst i₂ g)
      (zeroSchemePullbackHom (pullback.snd i₂ g) L s) hm₂ ≫ e.hom = 𝟙 _ := by
    refine (cancel_mono E.subschemeι).1 ?_
    rw [Category.assoc, he, Category.id_comp]
    refine pullback.hom_ext ?_ ?_
    · simp only [bivariantBaseChangeMap, Category.assoc, pullbackMap_fst, Category.comp_id]
      exact pullback.lift_fst _ _ _
    · simp only [bivariantBaseChangeMap, Category.assoc, pullbackMap_snd]
      exact (pullback.lift_snd_assoc _ _ _ _).trans (zeroSchemePullbackHom_subschemeι _ L s)
  exact properChowPushforward_chowPush_of_comp_eq_id C E.subschemeι (pullback.fst i₂ g) sX₂
    _ _ e.hom hid _ hbase (k - p) hfac _

variable (a) in
/-- **The extension of a class from one member of a closed cover.** Let `i₁ : X₁ ⟶ X` and
`i₂ : X₂ ⟶ X` be closed immersions whose images cover `X`, and let `a ∈ A^p(X₂)` vanish over
`X₁ ×_X X₂ ⟶ X₂`. The class `a' ∈ A^p(X₂ ⟶ X)` acts on a test scheme `T ⟶ X` by writing a class
as `j₁_* α₁ + j₂_* α₂` along the base-changed cover `T ×_X X₁, T ×_X X₂` (Stacks 0F94) and
setting `a' ∩ (j₁_* α₁ + j₂_* α₂) = a ∩ α₂`. -/
def closedCoverExtension (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p where
  cap g _ k := closedCoverExtensionCap C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    exact closedCoverExtensionCap_proper_naturality C (gysinSystemOfInvertible C) sX
      i₁ i₂ sX₂ hi₂ hcover ha g h h' sq hfst k _ _ α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ r hr h' sq hfst k α
    exact closedCoverExtensionCap_flat_naturality C (gysinSystemOfInvertible C) sX
      i₁ i₂ sX₂ hi₂ hcover ha g h r hr h' sq hfst k _ _ _ α
  cap_gysin := by
    intro T g _ L _ s k
    dsimp only
    intro e he hbase α
    exact closedCoverExtensionCap_gysin_naturality C sX i₁ i₂ sX₂ hi₂ hcover ha g L s k e he
      hbase _ α

/-- The cap operation of the extension is `Stacks.Chow.closedCoverExtensionCap`. -/
theorem closedCoverExtension_cap (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    (closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha).cap g k =
      closedCoverExtensionCap C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha g k :=
  rfl

/-- **The extension on the second member of the cover.** On every test scheme `g : T ⟶ X`, the
extension caps a class pushed forward from `T ×_X X₂` as `a` caps it on `T ×_X X₂ ⟶ X₂`, read on
`T ×_X X₂` itself through the isomorphism `X₂ ×_{X₂} (T ×_X X₂) ≅ T ×_X X₂`. -/
theorem closedCoverExtension_cap_second (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k) :
    (closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha).cap g k
        (chowPush C _ _ (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism hi₂ g) k α) =
      a.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k α :=
  closedCoverExtensionCap_second C _ sX i₁ i₂ sX₂ hi₂ hcover ha g k α

/-- **The extension on the first member of the cover.** On every test scheme `g : T ⟶ X`, the
extension kills the classes pushed forward from `T ×_X X₁`. -/
theorem closedCoverExtension_cap_first (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k) :
    (closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha).cap g k
        (chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k α) = 0 :=
  closedCoverExtensionCap_first C _ sX i₁ i₂ sX₂ hi₂ hcover ha g k α

end Extension

/-! ### The characterization and its consequences -/

section Characterization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂) {p : ℤ}

/-- A class `c ∈ A^p(X₂ ⟶ X)` *extends* `a ∈ A^p(X₂)` along the closed cover `X = X₁ ∪ X₂` when,
on every test scheme `g : T ⟶ X`, it caps the classes pushed forward from `T ×_X X₂` as `a` does
and kills the classes pushed forward from `T ×_X X₁`. These are the two formulas of Stacks 0F9H,
`c ∩ i_{2,*} α₂ = a ∩ α₂` and `c ∩ i_{1,*} α₁ = 0`, after every base change. -/
def IsClosedCoverExtension (a : chowCohomologyComponent C G sX₂ p)
    (c : BivariantClass C G sX₂ sX i₂ hi₂ p) : Prop :=
  (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k),
      c.cap g k
          (chowPush C _ _ (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism hi₂ g) k α) =
        a.idRule C sX₂ G (pullback.fst i₂ g) k α) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k),
      c.cap g k
          (chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k α) =
        0

variable {C G sX i₁ i₂ sX₂ hi₂}

/-- **Uniqueness of the extension.** Two classes of `A^p(X₂ ⟶ X)` extending the same class along
a closed cover are equal: by Stacks 0F94 every class on a test scheme is a sum of classes pushed
forward from the two members of the base-changed cover. -/
theorem IsClosedCoverExtension.eq (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {a : chowCohomologyComponent C G sX₂ p} {c d : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c)
    (hd : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a d) : c = d := by
  refine BivariantClass.ext C G sX₂ sX i₂ hi₂ p fun {T} g _ k α ↦ ?_
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ hcover g k α
  rw [closedCoverSum_apply, map_add, map_add, hc.1, hc.2, hd.1, hd.2]

/-- The sum of two extensions is an extension of the sum. -/
theorem IsClosedCoverExtension.add {a b : chowCohomologyComponent C G sX₂ p}
    {c d : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c)
    (hd : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ b d) :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (a + b) (c + d) := by
  refine ⟨fun g _ k α ↦ ?_, fun g _ k α ↦ ?_⟩
  · rw [BivariantClass.add_cap, hc.1, hd.1, BivariantClass.idRule_add]
  · rw [BivariantClass.add_cap, hc.2, hd.2, add_zero]

/-- The negation of an extension is an extension of the negation. -/
theorem IsClosedCoverExtension.neg {a : chowCohomologyComponent C G sX₂ p}
    {c : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c) :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (-a) (-c) := by
  refine ⟨fun g _ k α ↦ ?_, fun g _ k α ↦ ?_⟩
  · rw [BivariantClass.neg_cap, hc.1, BivariantClass.idRule_neg]
  · rw [BivariantClass.neg_cap, hc.2, neg_zero]

/-- The zero class extends the zero class. -/
theorem IsClosedCoverExtension.zero :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (0 : chowCohomologyComponent C G sX₂ p) 0 :=
  ⟨fun g _ k α ↦ by rw [BivariantClass.zero_cap, BivariantClass.idRule_zero],
    fun g _ k α ↦ by rw [BivariantClass.zero_cap]⟩

variable {a b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}

variable (C sX i₁ i₂ sX₂ hi₂) in
/-- The extension of `a` extends `a`. -/
theorem isClosedCoverExtension_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ a
      (closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha) :=
  ⟨fun g _ k α ↦ closedCoverExtension_cap_second C sX i₁ i₂ sX₂ hi₂ hcover ha g k α,
    fun g _ k α ↦ closedCoverExtension_cap_first C sX i₁ i₂ sX₂ hi₂ hcover ha g k α⟩

/-- **Uniqueness of the extension.** A class of `A^p(X₂ ⟶ X)` satisfying the two formulas of
Stacks 0F9H is the extension. -/
theorem IsClosedCoverExtension.eq_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    {c : BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ a c) :
    c = closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha :=
  hc.eq hcover (isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover ha)

variable (C sX i₁ i₂ sX₂ hi₂) in
/-- **Existence and uniqueness of the extension.** For closed immersions `i₁, i₂` whose images
cover `X` and a class `a ∈ A^p(X₂)` vanishing over `X₁ ×_X X₂ ⟶ X₂`, exactly one class of
`A^p(X₂ ⟶ X)` satisfies `c ∩ i_{2,*} α₂ = a ∩ α₂` and `c ∩ i_{1,*} α₁ = 0` after every base
change. -/
theorem existsUnique_isClosedCoverExtension (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    ∃! c : BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p,
      IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ a c :=
  ⟨closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha,
    isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover ha,
    fun _ hc ↦ hc.eq_closedCoverExtension hcover ha⟩

variable (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)

/-- The extension is additive in the class extended. -/
theorem closedCoverExtension_add (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (hb : BivariantClass.VanishesOver b (pullback.snd i₁ i₂)) :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ (a + b) hcover (ha.add hb) =
      closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha +
        closedCoverExtension C sX i₁ i₂ sX₂ hi₂ b hcover hb :=
  ((isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover ha).add
    (isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover hb)
    ).eq_closedCoverExtension hcover (ha.add hb) |>.symm

/-- The extension commutes with negation. -/
theorem closedCoverExtension_neg (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ (-a) hcover ha.neg =
      -closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha :=
  ((isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover ha).neg
    ).eq_closedCoverExtension hcover ha.neg |>.symm

/-- The extension of the zero class is zero. -/
theorem closedCoverExtension_zero :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ (0 : chowCohomologyComponent C _ sX₂ p) hcover
      BivariantClass.VanishesOver.zero = 0 :=
  (IsClosedCoverExtension.zero.eq_closedCoverExtension hcover _).symm

/-- The extension commutes with subtraction. -/
theorem closedCoverExtension_sub (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (hb : BivariantClass.VanishesOver b (pullback.snd i₁ i₂)) :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ (a - b) hcover (ha.sub hb) =
      closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha -
        closedCoverExtension C sX i₁ i₂ sX₂ hi₂ b hcover hb := by
  refine (IsClosedCoverExtension.eq_closedCoverExtension hcover (ha.sub hb) ?_).symm
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact (isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover ha).add
    (isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover hb).neg

variable (C sX i₁ i₂ sX₂ hi₂ p) in
/-- The extension along a closed cover, as a homomorphism from the subgroup of `A^p(X₂)` of the
classes vanishing over `X₁ ×_X X₂ ⟶ X₂` to `A^p(X₂ ⟶ X)`. -/
def closedCoverExtensionAddHom :
    vanishesOverAddSubgroup C (gysinSystemOfInvertible C) sX₂ p (pullback.snd i₁ i₂) →+
      BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p where
  toFun a := closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a.1 hcover a.2
  map_zero' := closedCoverExtension_zero hcover
  map_add' a b := closedCoverExtension_add hcover a.2 b.2

end Characterization

/-! ### Vanishing over a closed subscheme as the vanishing of the restriction -/

section Restriction

variable (C : ChowSituation.{u}) {Z Z' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  {p : ℤ}

/-- **Stacks 0B7F on the test schemes.** The operation of the restriction of a class
`a ∈ A^p(Z)` along `f : Z' ⟶ Z` on a test scheme `n : T ⟶ Z'` is the operation of `a` on
`n ≫ f`. -/
theorem chowCohomologyRestriction_idRule (f : Z' ⟶ Z) [LocallyOfFiniteType f]
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p) {T : Scheme.{u}}
    (n : T ⟶ Z') [LocallyOfFiniteType n] (k : ℤ) (α : chowGroup C (n ≫ (f ≫ sZ)) k) :
    (chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a).idRule C (f ≫ sZ)
        (gysinSystemOfInvertible C) n k α =
      a.idRule C sZ (gysinSystemOfInvertible C) (n ≫ f) k
        (chowGroupCongr C (Category.assoc n f sZ).symm k α) :=
  chowCohomologyRestriction_cap C (gysinSystemOfInvertible C) sZ f p _ a n k α

/-- **Vanishing over a morphism is the vanishing of the restriction.** A class `a ∈ A^p(Z)`
vanishes over `z : W ⟶ Z` exactly when its restriction `z^* a ∈ A^p(W)` (Stacks 0B7F) is zero.
For a closed immersion `z`, this is the assertion that `a` restricts to zero on `W`. -/
theorem chowCohomologyRestriction_eq_zero_iff_vanishesOver {W : Scheme.{u}} (z : W ⟶ Z)
    [LocallyOfFiniteType z] (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ z p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a = 0 ↔
      BivariantClass.VanishesOver a z := by
  constructor
  · intro h T t _ k α
    have hcap := chowCohomologyRestriction_idRule C sZ z a t k
      (chowGroupCongr C (Category.assoc t z sZ) k α)
    rw [h, BivariantClass.idRule_zero, chowGroupCongr_chowGroupCongr] at hcap
    have hzero : a.idRule C sZ (gysinSystemOfInvertible C) (t ≫ z) k α = 0 := hcap.symm
    exact BivariantClass.cap_eq_zero_of_idRule_eq_zero C _ sZ _ _ k α hzero
  · intro ha
    refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
    rw [BivariantClass.zero_cap]
    refine BivariantClass.cap_eq_zero_of_idRule_eq_zero C _ _ _ t k α ?_
    rw [chowCohomologyRestriction_idRule]
    exact ha.idRule_eq_zero t (t ≫ z) rfl k _

end Restriction

/-! ### Independence of the first member of the cover -/

section Independence

variable (C : ChowSituation.{u}) {X X₁ X₁' X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₁' : X₁' ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₁'] [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂]
  (hi₂ : i₂ ≫ sX = sX₂) {p : ℤ} {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}

/-- **The extension does not depend on the first member of the cover.** If `X = X₁ ∪ X₂` and
`X = X₁' ∪ X₂` are two closed covers with the same second member and `a ∈ A^p(X₂)` vanishes over
both `X₁ ×_X X₂` and `X₁' ×_X X₂`, the two extensions of `a` agree. Indeed the extension along
the first cover already kills the classes pushed forward from `T ×_X X₁'`: such a class is a sum
of classes from `T ×_X X₁' ×_X X₁`, which the extension kills, and from `T ×_X X₁' ×_X X₂`, which
lies over `X₁' ×_X X₂`. -/
theorem closedCoverExtension_eq_of_closedCover (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hcover' : Set.range i₁' ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (ha' : BivariantClass.VanishesOver a (pullback.snd i₁' i₂)) :
    closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha =
      closedCoverExtension C sX i₁' i₂ sX₂ hi₂ a hcover' ha' := by
  refine IsClosedCoverExtension.eq_closedCoverExtension hcover' ha'
    ⟨fun g _ k α ↦ closedCoverExtension_cap_second C sX i₁ i₂ sX₂ hi₂ hcover ha g k α,
      fun {T} g _ k α ↦ ?_⟩
  have hb : pullback.fst i₁' g ≫ (i₁' ≫ sX) = (pullback.snd i₁' g ≫ g) ≫ sX :=
    (pullbackSnd_comp_structureMorphism rfl g).symm.trans (Category.assoc _ _ _).symm
  obtain ⟨⟨β₁, β₂⟩, hβ⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ sX₂ hi₂ hcover
    (pullback.snd i₁' g ≫ g) k (chowGroupCongr C hb k α)
  have hα : chowPush C _ (g ≫ sX) (pullback.snd i₁' g) (pullbackSnd_comp_structureMorphism rfl g)
      k α =
      chowPush C ((pullback.snd i₁' g ≫ g) ≫ sX) (g ≫ sX) (pullback.snd i₁' g)
        (Category.assoc _ _ _).symm k (chowGroupCongr C hb k α) :=
    properChowPushforward_chowGroupCongr C hb rfl _ _ _ k
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) α
  have hn : (pullback.snd i₂ (pullback.snd i₁' g ≫ g) ≫ pullback.fst i₁' g) ≫ i₁' =
      pullback.fst i₂ (pullback.snd i₁' g ≫ g) ≫ i₂ := by
    rw [Category.assoc, pullback.condition]
    exact pullback.condition.symm
  rw [hα, ← hβ, closedCoverExtension_cap, closedCoverExtensionCap_chowPush_closedCoverSum,
    ha'.idRule_eq_zero (pullback.lift _ _ hn) _ (pullback.lift_snd _ _ _), map_zero]

end Independence

/-! ### Base change -/

section BaseChange

variable (C : ChowSituation.{u}) {X X' X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
  (h : X' ⟶ X) [LocallyOfFiniteType h] {p : ℤ}
  {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}

omit [IsClosedImmersion i₂] in
/-- The restriction of a class vanishing over `X₁ ×_X X₂ ⟶ X₂` to the base change `X' ×_X X₂`
vanishes over the base change `X'₁ ×_{X'} X'₂ ⟶ X'₂` of the cover. -/
theorem BivariantClass.VanishesOver.chowCohomologyRestriction
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ (pullback.fst i₂ h)
        p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a)
      (pullback.snd (pullback.snd i₁ h) (pullback.snd i₂ h)) := by
  intro T t _ k α
  have hn : (pullback.fst (pullback.snd i₁ h) (pullback.snd i₂ h) ≫ pullback.fst i₁ h) ≫ i₁ =
      (pullback.snd (pullback.snd i₁ h) (pullback.snd i₂ h) ≫ pullback.fst i₂ h) ≫ i₂ := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := i₁),
      pullback.condition (f := i₂), ← Category.assoc, ← Category.assoc, pullback.condition]
  refine BivariantClass.cap_eq_zero_of_idRule_eq_zero C _ _ _ _ k α ?_
  rw [chowCohomologyRestriction_idRule]
  exact ha.idRule_eq_zero (t ≫ pullback.lift _ _ hn) _
    (by rw [Category.assoc]; exact congrArg (t ≫ ·) (pullback.lift_snd _ _ _)) k _

/-- **Stacks 0F9Z for the extension (the generic form of Stacks 0GUG).** The restriction of the
extension of `a` along a morphism `h : X' ⟶ X` is the extension of the restriction of `a` to
`X'₂ = X₂ ×_X X'` along the base-changed cover `X' = X'₁ ∪ X'₂`. -/
theorem bivariantRestriction_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    bivariantRestriction C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ h p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha) =
      closedCoverExtension C (h ≫ sX) (pullback.snd i₁ h) (pullback.snd i₂ h)
        (pullback.fst i₂ h ≫ sX₂) (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ h)
        (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂
          (pullback.fst i₂ h) p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a)
        (range_pullbackSnd_union_eq_univ i₁ i₂ hcover h)
        (ha.chowCohomologyRestriction C i₁ i₂ sX₂ h) := by
  refine IsClosedCoverExtension.eq_closedCoverExtension _ _ ⟨fun {T} g _ k α ↦ ?_,
    fun {T} g _ k α ↦ ?_⟩
  · have hm : (pullback.fst (pullback.snd i₂ h) g ≫ pullback.fst i₂ h) ≫ i₂ =
        pullback.snd (pullback.snd i₂ h) g ≫ g ≫ h := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc]
    have h0 := closedCoverExtensionCap_comp_properChowPushforward_second C
      (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha h g
      (pullback.snd (pullback.snd i₂ h) g) (pullback.fst (pullback.snd i₂ h) g)
      (pullback.fst i₂ h) hm
      (pullbackSnd_comp_structureMorphism (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ h)
        g) k (properPushforwardDescends C _ _ _ _ _) α
    have hid : pullback.lift (pullback.fst (pullback.snd i₂ h) g ≫ pullback.fst i₂ h)
        (pullback.snd (pullback.snd i₂ h) g) hm ≫ (pullbackLeftPullbackSndIso i₂ h g).inv =
        𝟙 _ := by
      rw [Iso.comp_inv_eq, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · exact (pullback.lift_fst _ _ _).trans (pullbackLeftPullbackSndIso_hom_fst i₂ h g).symm
      · exact (pullback.lift_snd _ _ _).trans (pullbackLeftPullbackSndIso_hom_snd i₂ h g).symm
    rw [bivariantRestriction_cap, bivariantRestrictionCap_apply, closedCoverExtension_cap]
    refine (congrArg _ h0).trans ?_
    rw [chowCohomologyRestriction_idRule]
    exact properChowPushforward_chowPush_of_comp_eq_id C _ _ sX₂ _ _ _ hid _ _ (k - p) _ _
  · have hm : (pullback.fst (pullback.snd i₁ h) g ≫ pullback.fst i₁ h) ≫ i₁ =
        pullback.snd (pullback.snd i₁ h) g ≫ g ≫ h := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc]
    have h0 := closedCoverExtensionCap_comp_properChowPushforward_first C
      (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha h g
      (pullback.snd (pullback.snd i₁ h) g) _ (pullbackSnd_comp_structureMorphism rfl g) _ hm k
      (properPushforwardDescends C _ _ _ _ _) α
    rw [bivariantRestriction_cap, bivariantRestrictionCap_apply, closedCoverExtension_cap]
    exact (congrArg _ h0).trans (map_zero _)

end BaseChange

end Stacks.Chow

end
