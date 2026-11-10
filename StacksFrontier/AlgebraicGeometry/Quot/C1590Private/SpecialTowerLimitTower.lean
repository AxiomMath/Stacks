module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerInterfaces
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# Étale limit towers

Let `V` be an affine object of the big fppf site of `S` and `Wₙ ⟶ V` a sequence of thickenings
with transition maps `Wₙ ⟶ Wₙ₊₁`. The tower is an *étale limit tower* if for every affine `P`
étale over `V`, with base changes `Qₙ = P ×_V Wₙ`, the ring `Γ(P)` is the limit of the rings
`Γ(Qₙ)`. For a special tower `⋯ → R₁ → R₀` (Stacks 0G2S) this is the content of
`AlgebraicGeometry.C1590Private.SpecialTowerEtaleCompatible`, for `V = Spec (lim Rₙ)` and
`Wₙ = Spec Rₙ`.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsEtaleLimitTower`: an étale limit tower.

## Main results

* `AlgebraicGeometry.C1590Private.IsEtaleLimitTower.existsUnique_hom`: morphisms from `P` to an
  affine scheme are the compatible systems of morphisms from the `Qₙ`.
* `AlgebraicGeometry.C1590Private.existsUnique_section_of_isThickening`: a section of an étale
  morphism over a thickening extends uniquely (Stacks 039R, 0BTY).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.C1590Private

/-! ### Sections of étale morphisms along thickenings -/

/-- **Sections of an étale morphism extend uniquely along a thickening.** Let `i : X₀ ⟶ X` be a
thickening and `q : E ⟶ X` étale. A morphism `s : X₀ ⟶ E` with `s ≫ q = i` is the restriction of a
unique section of `q` (Stacks 039R, through Stacks 0BTY). -/
theorem existsUnique_section_of_isThickening {X₀ X E : Scheme.{u}} (i : X₀ ⟶ X)
    (hi : Stacks.Thickenings.IsThickening i) (q : E ⟶ X) [Etale q] (s : X₀ ⟶ E)
    (hs : s ≫ q = i) : ∃! t : X ⟶ E, t ≫ q = 𝟙 X ∧ i ≫ t = s := by
  have : IsClosedImmersion i := hi.1
  have : UniversalHomeomorphism i :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i hi.2
  obtain ⟨t, ht, hts⟩ := Stacks.Etale.exists_section_of_universalHomeomorphism i q s hs
  refine ⟨t, ⟨ht, hts⟩, fun t' ⟨ht', hts'⟩ => ?_⟩
  have : Etale (Over.mk q).hom := ‹Etale q›
  have hinj := Stacks.Etale.injective_baseChange_hom_of_universalHomeomorphism i (Over.mk q)
    (Over.mk (𝟙 X))
  have hfst : pullback.fst (𝟙 X) i = pullback.snd (𝟙 X) i ≫ i := by
    simpa using pullback.condition (f := 𝟙 X) (g := i)
  have : (Over.homMk t' (by simpa using ht') : Over.mk (𝟙 X) ⟶ Over.mk q) =
      Over.homMk t (by simpa using ht) := by
    apply hinj
    ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst, Over.homMk_left]
      change pullback.fst (𝟙 X) i ≫ t' = pullback.fst (𝟙 X) i ≫ t
      rw [hfst, Category.assoc, Category.assoc, hts, hts']
    · simp only [Over.pullback_map_left, pullback.lift_snd]
  exact congrArg CommaMorphism.left this

/-! ### Étale limit towers -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- **An étale limit tower.** Morphisms `κₙ : Wₙ ⟶ V` to an affine object `V` of the site, `κ₀` a
thickening, with transition maps `ℓₙ : Wₙ ⟶ Wₙ₊₁` over `V` which are thickenings, such that for
every affine `P` étale over `V` and base changes `Qₙ = P ×_V Wₙ` (with transition maps `cₙ` over
those of the tower) every compatible sequence of global sections of the `Qₙ` comes from exactly one
global section of `P`: `Γ(P) = lim Γ(Qₙ)`. -/
structure IsEtaleLimitTower {V : BigFppfOver B S hS} (W : ℕ → BigFppfOver B S hS)
    (κ : ∀ n, W n ⟶ V) (ℓ : ∀ n, W n ⟶ W (n + 1)) : Prop where
  /-- The transition maps commute with the maps to `V`: `ℓₙ ≫ κₙ₊₁ = κₙ`. -/
  comp : ∀ n, ℓ n ≫ κ (n + 1) = κ n
  /-- The map `κ₀ : W₀ ⟶ V` is a thickening. -/
  isThickening_zero : Stacks.Thickenings.IsThickening ((𝒯).map (κ 0))
  /-- Each transition map `ℓₙ : Wₙ ⟶ Wₙ₊₁` is a thickening. -/
  isThickening_ℓ : ∀ n, Stacks.Thickenings.IsThickening ((𝒯).map (ℓ n))
  /-- The top `V` is affine. -/
  isAffine : IsAffine ((𝒯).obj V)
  /-- For every affine `P` étale over `V` with base changes `Qₙ = P ×_V Wₙ`, every compatible
  sequence of global sections of the `Qₙ` comes from exactly one global section of `P`. -/
  existsUnique : ∀ ⦃P : BigFppfOver B S hS⦄ (e : P ⟶ V), Etale ((𝒯).map e) →
    IsAffine ((𝒯).obj P) →
    ∀ (Q : ℕ → BigFppfOver B S hS) (a : ∀ n, Q n ⟶ P) (b : ∀ n, Q n ⟶ W n)
      (c : ∀ n, Q n ⟶ Q (n + 1)),
      (∀ n, IsPullback ((𝒯).map (a n)) ((𝒯).map (b n)) ((𝒯).map e) ((𝒯).map (κ n))) →
      (∀ n, c n ≫ a (n + 1) = a n) →
      (∀ n, c n ≫ b (n + 1) = b n ≫ ℓ n) →
      ∀ s : ∀ n, Γ((𝒯).obj (Q n), ⊤), (∀ n, ((𝒯).map (c n)).appTop (s (n + 1)) = s n) →
        ∃! g : Γ((𝒯).obj P, ⊤), ∀ n, ((𝒯).map (a n)).appTop g = s n

variable {V : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)}

/-- **Morphisms to an affine scheme along an étale limit tower.** For `P` affine étale over the
top `V` of an étale limit tower, with base changes `Qₙ`, compatible morphisms `Qₙ ⟶ X` to an affine
scheme come from exactly one morphism `P ⟶ X`. -/
theorem IsEtaleLimitTower.existsUnique_hom (hW : IsEtaleLimitTower W κ ℓ) {P : BigFppfOver B S hS}
    (e : P ⟶ V) (he : Etale ((𝒯).map e)) (hP : IsAffine ((𝒯).obj P))
    (Q : ℕ → BigFppfOver B S hS) (a : ∀ n, Q n ⟶ P) (b : ∀ n, Q n ⟶ W n)
    (c : ∀ n, Q n ⟶ Q (n + 1))
    (hpb : ∀ n, IsPullback ((𝒯).map (a n)) ((𝒯).map (b n)) ((𝒯).map e) ((𝒯).map (κ n)))
    (hca : ∀ n, c n ≫ a (n + 1) = a n) (hcb : ∀ n, c n ≫ b (n + 1) = b n ≫ ℓ n)
    {X : Scheme.{u}} [IsAffine X] (h : ∀ n, (𝒯).obj (Q n) ⟶ X)
    (hh : ∀ n, (𝒯).map (c n) ≫ h (n + 1) = h n) :
    ∃! g : (𝒯).obj P ⟶ X, ∀ n, (𝒯).map (a n) ≫ g = h n := by
  have hs : ∀ (x : Γ(X, ⊤)) n, ((𝒯).map (c n)).appTop ((h (n + 1)).appTop x) = (h n).appTop x :=
    fun x n => by rw [← hh n, Scheme.Hom.comp_appTop]; rfl
  choose φ hφ hφu using fun x =>
    hW.existsUnique e he hP Q a b c hpb hca hcb (fun n => (h n).appTop x) (hs x)
  let ψ : Γ(X, ⊤) →+* Γ((𝒯).obj P, ⊤) :=
    { toFun := φ
      map_one' := (hφu 1 1 fun n => by rw [map_one, map_one]).symm
      map_mul' := fun x y =>
        (hφu (x * y) (φ x * φ y) fun n => by rw [map_mul, map_mul, hφ, hφ]).symm
      map_zero' := (hφu 0 0 fun n => by rw [map_zero, map_zero]).symm
      map_add' := fun x y =>
        (hφu (x + y) (φ x + φ y) fun n => by rw [map_add, map_add, hφ, hφ]).symm }
  let g : (𝒯).obj P ⟶ X :=
    ((𝒯).obj P).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv
  have hg : ∀ x, g.appTop x = φ x := by
    intro x
    have h1 : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
      rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp [Scheme.isoSpec]
    have h2 := ConcreteCategory.congr_hom h1 x
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply (Spec.map _).appTop, Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply]
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at h2
    exact congrArg φ h2
  have hgn : ∀ n, (𝒯).map (a n) ≫ g = h n := fun n => by
    apply ext_of_isAffine
    ext x
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hg, hφ]
  refine ⟨g, hgn, fun g' hg' => ?_⟩
  apply ext_of_isAffine
  ext x
  rw [hg]
  refine hφu x _ (fun n => ?_)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg' n]

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- **An étale limit tower restricts to affine objects étale over its top.** For `P` affine
étale over the top of an étale limit tower, base changes `Qₙ = P ×_V Wₙ` (with transition maps over
those of the tower) form an étale limit tower over `P`. -/
theorem IsEtaleLimitTower.of_isPullback (hW : IsEtaleLimitTower W κ ℓ) {P : BigFppfOver B S hS}
    (e : P ⟶ V) (he : Etale ((𝒯).map e)) (hP : IsAffine ((𝒯).obj P))
    (Q : ℕ → BigFppfOver B S hS) (a : ∀ n, Q n ⟶ P) (b : ∀ n, Q n ⟶ W n)
    (c : ∀ n, Q n ⟶ Q (n + 1))
    (hpb : ∀ n, IsPullback ((𝒯).map (a n)) ((𝒯).map (b n)) ((𝒯).map e) ((𝒯).map (κ n)))
    (hca : ∀ n, c n ≫ a (n + 1) = a n) (hcb : ∀ n, c n ≫ b (n + 1) = b n ≫ ℓ n) :
    IsEtaleLimitTower Q a c where
  comp := hca
  isThickening_zero :=
    Stacks.Thickenings.isThickening_of_isPullback (hpb 0) hW.isThickening_zero
  isThickening_ℓ n := by
    have h1 : IsPullback ((𝒯).map (c n)) ((𝒯).map (b n)) ((𝒯).map (b (n + 1)))
        ((𝒯).map (ℓ n)) := by
      refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, hcb n])
        (hpb (n + 1))
      rw [← Functor.map_comp, ← Functor.map_comp, hca n, hW.comp n]
      exact hpb n
    exact Stacks.Thickenings.isThickening_of_isPullback h1 (hW.isThickening_ℓ n)
  isAffine := hP
  existsUnique P' e' he' hP' Q' a' b' c' hpb' hca' hcb' s hs := by
    have : Etale ((𝒯).map e') := he'
    have : Etale ((𝒯).map e) := he
    refine hW.existsUnique (e' ≫ e) (by rw [Functor.map_comp]; infer_instance) hP' Q' a'
      (fun n => b' n ≫ b n) c' (fun n => by
        rw [Functor.map_comp, Functor.map_comp]
        exact (hpb' n).paste_vert (hpb n)) hca'
      (fun n => ?_) s hs
    rw [← Category.assoc, hcb' n, Category.assoc, hcb n, Category.assoc]

/-- **Morphisms into an étale scheme agree as soon as they agree on a thickening.** -/
theorem ext_of_etale_of_isThickening {X₀ X E Y : Scheme.{u}} (i : X₀ ⟶ X)
    (hi : Stacks.Thickenings.IsThickening i) (q : E ⟶ Y) [Etale q] {g g' : X ⟶ E}
    (hq : g ≫ q = g' ≫ q) (hig : i ≫ g = i ≫ g') : g = g' := by
  obtain ⟨t, -, ht⟩ := existsUnique_section_of_isThickening i hi (pullback.snd q (g ≫ q))
    (pullback.lift (i ≫ g) i (by rw [Category.assoc])) (pullback.lift_snd _ _ _)
  have h1 := ht (pullback.lift g (𝟙 X) (by simp)) ⟨pullback.lift_snd _ _ _, by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]⟩
  have h2 := ht (pullback.lift g' (𝟙 X) (by simp [hq])) ⟨pullback.lift_snd _ _ _, by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hig]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]⟩
  simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst q (g ≫ q)) (h1.trans h2.symm)

/-- The composite `W₀ ⟶ Wₙ` of the transition maps of a tower. -/
def towerToLevel (ℓ : ∀ n, W n ⟶ W (n + 1)) : ∀ n, W 0 ⟶ W n
  | 0 => 𝟙 _
  | n + 1 => towerToLevel ℓ n ≫ ℓ n

/-- In an étale limit tower, the composite `W₀ ⟶ Wₙ ⟶ V` is `κ₀`. -/
theorem IsEtaleLimitTower.towerToLevel_comp (hW : IsEtaleLimitTower W κ ℓ) (n : ℕ) :
    towerToLevel ℓ n ≫ κ n = κ 0 := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih => rw [towerToLevel, Category.assoc, hW.comp, ih]

/-- In an étale limit tower, the composite `W₀ ⟶ Wₙ` of the transition maps is a thickening. -/
theorem IsEtaleLimitTower.isThickening_towerToLevel (hW : IsEtaleLimitTower W κ ℓ) (n : ℕ) :
    Stacks.Thickenings.IsThickening ((𝒯).map (towerToLevel ℓ n)) := by
  induction n with
  | zero =>
    rw [towerToLevel, CategoryTheory.Functor.map_id]
    exact ⟨inferInstance, Function.surjective_id⟩
  | succ n ih =>
    rw [towerToLevel, Functor.map_comp]
    have := ih.1
    have := (hW.isThickening_ℓ n).1
    exact ⟨inferInstance, (hW.isThickening_ℓ n).2.comp ih.2⟩

/-- **Morphisms to an affine scheme along an étale limit tower, at the top.** -/
theorem IsEtaleLimitTower.existsUnique_hom_self (hW : IsEtaleLimitTower W κ ℓ) {X : Scheme.{u}}
    [IsAffine X] (h : ∀ n, (𝒯).obj (W n) ⟶ X) (hh : ∀ n, (𝒯).map (ℓ n) ≫ h (n + 1) = h n) :
    ∃! g : (𝒯).obj V ⟶ X, ∀ n, (𝒯).map (κ n) ≫ g = h n :=
  have := hW.isAffine
  hW.existsUnique_hom (𝟙 V) (by rw [CategoryTheory.Functor.map_id]; infer_instance) hW.isAffine W
    κ (fun n => 𝟙 _) ℓ (fun n => by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact IsPullback.id_vert _) hW.comp (fun n => by simp) h hh

/-- Two morphisms from the top of an étale limit tower into an affine open of a scheme which agree
on every level are equal. -/
theorem IsEtaleLimitTower.ext_of_range_subset (hW : IsEtaleLimitTower W κ ℓ) {X : Scheme.{u}}
    (O : X.Opens) (hO : IsAffineOpen O) {g g' : (𝒯).obj V ⟶ X}
    (hg : Set.range g ⊆ O) (hg' : Set.range g' ⊆ O)
    (h : ∀ n, (𝒯).map (κ n) ≫ g = (𝒯).map (κ n) ≫ g') : g = g' := by
  have : IsAffine O := hO
  have hr : Set.range O.ι = O := Scheme.Opens.range_ι O
  let g₁ := IsOpenImmersion.lift O.ι g (by rw [hr]; exact hg)
  let g₁' := IsOpenImmersion.lift O.ι g' (by rw [hr]; exact hg')
  have e₁ : g₁ ≫ O.ι = g := IsOpenImmersion.lift_fac _ _ _
  have e₁' : g₁' ≫ O.ι = g' := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, -, hk⟩ := hW.existsUnique_hom_self (X := O) (fun n => (𝒯).map (κ n) ≫ g₁)
    (fun n => by rw [← Category.assoc, ← Functor.map_comp, hW.comp])
  have : g₁ = g₁' := (hk g₁ fun n => rfl).trans (hk g₁' fun n => by
    rw [← cancel_mono O.ι, Category.assoc, Category.assoc, e₁, e₁', h n]).symm
  rw [← e₁, ← e₁', this]

/-- Compatible morphisms from the levels of an étale limit tower into an affine open of a scheme
come from a morphism from the top into that open. -/
theorem IsEtaleLimitTower.exists_hom_of_range_subset (hW : IsEtaleLimitTower W κ ℓ)
    {X : Scheme.{u}} (O : X.Opens) (hO : IsAffineOpen O) (h : ∀ n, (𝒯).obj (W n) ⟶ X)
    (hh : ∀ n, (𝒯).map (ℓ n) ≫ h (n + 1) = h n) (hO' : ∀ n, Set.range (h n) ⊆ O) :
    ∃ g : (𝒯).obj V ⟶ X, Set.range g ⊆ O ∧ ∀ n, (𝒯).map (κ n) ≫ g = h n := by
  have : IsAffine O := hO
  have hr : Set.range O.ι = O := Scheme.Opens.range_ι O
  let h₁ := fun n => IsOpenImmersion.lift O.ι (h n) (by rw [hr]; exact hO' n)
  have e : ∀ n, h₁ n ≫ O.ι = h n := fun n => IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, hk, -⟩ := hW.existsUnique_hom_self (X := O) h₁ (fun n => by
    rw [← cancel_mono O.ι, Category.assoc, e, e, hh])
  refine ⟨k ≫ O.ι, ?_, fun n => by rw [← Category.assoc, hk, e]⟩
  rintro _ ⟨v, rfl⟩
  rw [← hr]
  exact ⟨k v, rfl⟩

end Site

/-! ### Moving an étale limit tower to the site of its top -/

section Slice

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)}

/-- The levels of a tower, as objects of the big fppf site of its top. -/
abbrev sliceLevel (κ : ∀ n, W n ⟶ V) (n : ℕ) : BigFppfOver B V.left.1 V.left.2 :=
  Over.mk (κ n).left

/-- The top of a tower, as the final object of its own big fppf site. -/
abbrev sliceTop (V : BigFppfOver B S hS) : BigFppfOver B V.left.1 V.left.2 :=
  Over.mk (𝟙 V.left)

/-- The maps of the levels to the top, in the big fppf site of the top. -/
abbrev sliceκ (κ : ∀ n, W n ⟶ V) (n : ℕ) : sliceLevel κ n ⟶ sliceTop V :=
  Over.homMk (κ n).left

/-- The transition maps, in the big fppf site of the top. -/
abbrev sliceℓ (hcomp : ∀ n, ℓ n ≫ κ (n + 1) = κ n) (n : ℕ) :
    sliceLevel κ n ⟶ sliceLevel κ (n + 1) :=
  Over.homMk (ℓ n).left (by
    change (ℓ n).left ≫ (κ (n + 1)).left = (κ n).left
    rw [← Over.comp_left, hcomp n])

/-- **An étale limit tower over `V` is an étale limit tower in the big fppf site of `V`.** -/
theorem IsEtaleLimitTower.slice (hW : IsEtaleLimitTower W κ ℓ) :
    IsEtaleLimitTower (sliceLevel κ) (sliceκ κ) (sliceℓ hW.comp) where
  comp n := Over.OverMorphism.ext (by
    change (ℓ n).left ≫ (κ (n + 1)).left = (κ n).left
    rw [← Over.comp_left, hW.comp n])
  isThickening_zero := hW.isThickening_zero
  isThickening_ℓ := hW.isThickening_ℓ
  isAffine := hW.isAffine
  existsUnique P' e' he' hP' Q' a' b' c' hpb' hca' hcb' s hs := by
    let P : BigFppfOver B S hS := Over.mk (P'.hom ≫ V.hom)
    let e : P ⟶ V := Over.homMk e'.left (by
      change e'.left ≫ V.hom = P'.hom ≫ V.hom
      rw [← Over.w e']
      simp)
    let Q : ℕ → BigFppfOver B S hS := fun n => Over.mk ((Q' n).hom ≫ V.hom)
    let a : ∀ n, Q n ⟶ P := fun n => Over.homMk (a' n).left (by
      change (a' n).left ≫ P'.hom ≫ V.hom = (Q' n).hom ≫ V.hom
      rw [← Category.assoc, Over.w (a' n)])
    let b : ∀ n, Q n ⟶ W n := fun n => Over.homMk (b' n).left (by
      change (b' n).left ≫ (W n).hom = (Q' n).hom ≫ V.hom
      rw [← Over.w (b' n), ← Over.w (κ n)]
      simp)
    let c : ∀ n, Q n ⟶ Q (n + 1) := fun n => Over.homMk (c' n).left (by
      change (c' n).left ≫ (Q' (n + 1)).hom ≫ V.hom = (Q' n).hom ≫ V.hom
      rw [← Category.assoc, Over.w (c' n)])
    exact hW.existsUnique e he' hP' Q a b c hpb'
      (fun n => Over.OverMorphism.ext (by
        change (c' n).left ≫ (a' (n + 1)).left = (a' n).left
        rw [← Over.comp_left, hca' n]))
      (fun n => Over.OverMorphism.ext (by
        change (c' n).left ≫ (b' (n + 1)).left = (b' n).left ≫ (ℓ n).left
        rw [← Over.comp_left, hcb' n]
        rfl)) s hs

end Slice

end AlgebraicGeometry.C1590Private

end
