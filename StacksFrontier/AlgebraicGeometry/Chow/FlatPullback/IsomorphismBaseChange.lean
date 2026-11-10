module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.TransposeGraph

/-!
# Flat pullback and pushforward along an isomorphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and consider a square

  `A₁ --u₁--> B₁`
  `|d          |v`
  `A₀ --u₀--> B₀`

of schemes locally of finite type over `S`, commuting over the base, in which `u₀` and `u₁` are
isomorphisms and `d` and `v` are flat of relative dimension `r`. Such a square is cartesian, and
this file proves for it that flat pullback commutes with proper pushforward (Stacks 02RG), first on
cycles and then on Chow groups, together with the invariance of the flat pullback multiplicity
`Stacks.Chow.flatPullbackWeight` under relabelling the square by the two isomorphisms.

## Main definitions

* `Stacks.Chow.comapSubschemeIsoOfIsIso` — for an isomorphism `f : A ⟶ B` and an ideal sheaf `J`
  on `B`, the identification of the subscheme of `J.comap f` with the subscheme of `J`.

## Main results

* `Stacks.Chow.comap_vanishingIdeal_closure_singleton_of_isIso` — an isomorphism matches the
  vanishing ideals of the reduced closures of corresponding points.
* `Stacks.Chow.properPushforward_apply_of_isIso` — pushforward along an isomorphism over the base
  reindexes the coefficients of a cycle.
* `Stacks.Chow.flatPullbackWeight_eq_of_isIso` — the flat pullback multiplicity is invariant
  under relabelling the square by the two isomorphisms.
* `Stacks.Chow.flatPullback_properPushforward_of_isIso` — **Stacks 02RG for two isomorphism
  legs**, on cycles.
* `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso` — **Stacks 02RG for two isomorphism legs**,
  on Chow groups.
* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso_square` — Stacks 02S1 along
  `v` implies Stacks 02S1 along `d`.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open TopologicalSpace

/-! ### Points -/

/-- An isomorphism of schemes is surjective on points. -/
theorem exists_base_eq_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] (b : B) :
    ∃ a : A, f.base a = b := by
  refine ⟨(inv f).base b, ?_⟩
  change ((inv f ≫ f) b) = b
  rw [IsIso.inv_hom_id]
  rfl

/-! ### Ideal sheaves along an isomorphism -/

/-- Pulling an ideal sheaf back along an isomorphism is pushing it forward along the inverse
isomorphism. -/
theorem comap_eq_map_inv_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : B.IdealSheafData) : J.comap f = J.map (inv f) := by
  have h : pullback.snd f J.subschemeι ≫ (J.subschemeι ≫ inv f) =
      pullback.fst f J.subschemeι := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map, ← h,
    Scheme.Hom.ker_comp_of_isIso]

/-- The vanishing ideal of the reduced closure of a point pulls back, along an isomorphism, to
the vanishing ideal of the reduced closure of the preimage point. -/
theorem comap_vanishingIdeal_closure_singleton_of_isIso {A B : Scheme.{u}} (f : A ⟶ B)
    [IsIso f] (x : A) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({f.base x} : Set B))).comap f =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set A)) := by
  have hmap : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({f.base x} : Set B))).map (inv f) =
      Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (⇑(inv f) '' ((Closeds.closure ({f.base x} : Set B)) : Set B))) :=
    Scheme.IdealSheafData.map_vanishingIdeal (inv f) _
  rw [comap_eq_map_inv_of_isIso f, hmap]
  congr 1
  refine Closeds.ext ?_
  calc ((Closeds.closure (⇑(inv f) ''
        ((Closeds.closure ({f.base x} : Set B)) : Set B))) : Set A)
      = closure (⇑(inv f) '' closure ({f.base x} : Set B)) := rfl
    _ = closure (closure (⇑(inv f) '' ({f.base x} : Set B))) :=
        congrArg closure (Homeomorph.image_closure (Scheme.homeoOfIso (asIso f).symm) _)
    _ = closure ({x} : Set A) := by
        rw [closure_closure, Set.image_singleton, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
        rfl
    _ = ((Closeds.closure ({x} : Set A)) : Set A) := rfl

/-- For an isomorphism `f : A ⟶ B` and an ideal sheaf `J` on `B`, the isomorphism from the
subscheme cut out by the pullback ideal sheaf `J.comap f` to the subscheme of `J`, through the
fibre product of `f` with the closed immersion of the subscheme of `J`. -/
def comapSubschemeIsoOfIsIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] (J : B.IdealSheafData) :
    (J.comap f).subscheme ≅ J.subscheme :=
  J.comapIso f ≪≫ asIso (pullback.snd f J.subschemeι)

/-- The isomorphism `Stacks.Chow.comapSubschemeIsoOfIsIso` carries the closed immersion of the
subscheme of `J.comap f` into `A`, followed by `f`, to the closed immersion of the subscheme of
`J` into `B`. -/
theorem comapSubschemeIsoOfIsIso_hom_subschemeι {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : B.IdealSheafData) :
    (comapSubschemeIsoOfIsIso f J).hom ≫ J.subschemeι = (J.comap f).subschemeι ≫ f := by
  simp only [comapSubschemeIsoOfIsIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-! ### Cycles along an isomorphism -/

/-- The coefficient of the cycle of the closed subscheme cut out by an ideal sheaf depends only
on that ideal sheaf. -/
theorem closedSubschemeCycleCoeff_congr_idealSheaf (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {I J : X.IdealSheafData} (h : I = J) (k : ℤ)
    (x : X) :
    closedSubschemeCycleCoeff C sX I.subschemeι k x =
      closedSubschemeCycleCoeff C sX J.subschemeι k x := by
  subst h
  rfl

/-- The coefficient of the proper pushforward of a cycle along an isomorphism over the base is
the coefficient at the preimage point. -/
theorem properPushforward_apply_of_isIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ) (c : CycleGroup C sA k) (a : A) :
    (properPushforward C sA sB f hf k c).1 (f.base a) = c.1 a := by
  have hpre : f.base ⁻¹' ({f.base a} : Set B) = {a} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hw ↦ f.isClosedEmbedding.injective hw, fun hw ↦ hw ▸ rfl⟩
  have hdim : relativeDimension C.dimensionFunction sA a =
      relativeDimension C.dimensionFunction sB (f.base a) := by
    rw [← hf]
    exact relativeDimension_comp_closedImmersion C.dimensionFunction f sB a
  rw [properPushforward_apply, hpre]
  simp [hdim, residueDegree_eq_one_of_isClosedImmersion f a]

/-- The coefficient of the cycle of a closed subscheme is unchanged by transporting the ambient
scheme along an isomorphism over the base. -/
theorem closedSubschemeCycleCoeff_of_isIso_ambient (C : ChowSituation.{u}) {A B Z : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (i : Z ⟶ A) [IsClosedImmersion i] (k : ℤ)
    (a : A) :
    closedSubschemeCycleCoeff C sA i k a =
      closedSubschemeCycleCoeff C sB (i ≫ f) k (f.base a) := by
  have h2 : (properPushforward C sA sB f hf k
        (cycleAssociatedToClosedSubscheme C sA i k)).1 (f.base a) =
      (cycleAssociatedToClosedSubscheme C sB (i ≫ f) k).1 (f.base a) :=
    congrArg (fun c : CycleGroup C sB k ↦ c.1 (f.base a))
      (properPushforward_cycleAssociatedToClosedSubscheme_of_isIso C sA sB (asIso f) hf i k)
  rwa [properPushforward_apply_of_isIso] at h2

/-! ### The weight of the flat pullback is invariant under relabelling -/

/-- A commuting square of schemes commutes on points. -/
private theorem base_apply_eq_of_comp_eq {A₀ A₁ B₀ B₁ : Scheme.{u}} {d : A₁ ⟶ A₀}
    {u₀ : A₀ ⟶ B₀} {u₁ : A₁ ⟶ B₁} {v : B₁ ⟶ B₀} (hsq : d ≫ u₀ = u₁ ≫ v) (a : A₁) :
    u₀.base (d.base a) = v.base (u₁.base a) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq]

/-- The multiplicity `Stacks.Chow.flatPullbackWeight` is invariant under relabelling a flat
morphism by isomorphisms over the base: if `d ≫ u₀ = u₁ ≫ v` with `u₀` and `u₁` isomorphisms,
the weight of `a₁` for `d` is the weight of `u₁ a₁` for `v`. -/
theorem flatPullbackWeight_eq_of_isIso (C : ChowSituation.{u}) {A₀ A₁ B₀ B₁ : Scheme.{u}}
    (sA₁ : A₁ ⟶ C.S) [LocallyOfFiniteType sA₁] (sB₁ : B₁ ⟶ C.S) [LocallyOfFiniteType sB₁]
    (u₀ : A₀ ⟶ B₀) [IsIso u₀] (u₁ : A₁ ⟶ B₁) [IsIso u₁] (hu₁ : u₁ ≫ sB₁ = sA₁)
    (d : A₁ ⟶ A₀) (v : B₁ ⟶ B₀) (hsq : d ≫ u₀ = u₁ ≫ v) (j : ℤ) (a₁ : A₁) :
    flatPullbackWeight C sA₁ d j a₁ = flatPullbackWeight C sB₁ v j (u₁.base a₁) := by
  have hpt := base_apply_eq_of_comp_eq hsq a₁
  have hIA : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({v.base (u₁.base a₁)} : Set B₀))).comap u₀ =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({d.base a₁} : Set A₀)) := by
    rw [← hpt]
    exact comap_vanishingIdeal_closure_singleton_of_isIso u₀ (d.base a₁)
  have hJ : ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({v.base (u₁.base a₁)} : Set B₀))).comap v).comap u₁ =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({d.base a₁} : Set A₀))).comap d := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hsq, Scheme.IdealSheafData.comap_comp, hIA]
  rw [flatPullbackWeight, flatPullbackWeight,
    closedSubschemeCycleCoeff_congr_idealSheaf C sA₁ hJ.symm j a₁,
    closedSubschemeCycleCoeff_of_isIso_ambient C sA₁ sB₁ u₁ hu₁ _ j a₁]
  exact closedSubschemeCycleCoeff_eq_of_iso C sB₁ _ _
    (comapSubschemeIsoOfIsIso u₁ _) (comapSubschemeIsoOfIsIso_hom_subschemeι u₁ _) j
    (u₁.base a₁)

/-! ### The isomorphism case of Stacks 02RG -/

/-- **Flat pullback commutes with pushforward along two isomorphism legs, on cycles.** In a
square

  `A₁ --u₁--> B₁`
  `|d          |v`
  `A₀ --u₀--> B₀`

over the base, with `u₀` and `u₁` isomorphisms and `d`, `v` flat of relative dimension `r`, flat
pullback commutes with pushforward along the isomorphisms. -/
@[stacks 02RG "the case of two isomorphism legs, on cycles"]
theorem flatPullback_properPushforward_of_isIso (C : ChowSituation.{u})
    {A₀ A₁ B₀ B₁ : Scheme.{u}} (sA₀ : A₀ ⟶ C.S) [LocallyOfFiniteType sA₀]
    (sA₁ : A₁ ⟶ C.S) [LocallyOfFiniteType sA₁] (sB₀ : B₀ ⟶ C.S) [LocallyOfFiniteType sB₀]
    (sB₁ : B₁ ⟶ C.S) [LocallyOfFiniteType sB₁]
    (u₀ : A₀ ⟶ B₀) [IsIso u₀] (hu₀ : u₀ ≫ sB₀ = sA₀)
    (u₁ : A₁ ⟶ B₁) [IsIso u₁] (hu₁ : u₁ ≫ sB₁ = sA₁)
    (d : A₁ ⟶ A₀) [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sA₀ = sA₁)
    (v : B₁ ⟶ B₀) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB₀ = sB₁)
    (hsq : d ≫ u₀ = u₁ ≫ v) (r : ℕ)
    (hdr : AlgebraicGeometry.RelativeDimension d r)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ) (z : CycleGroup C sA₀ k) :
    flatPullback C sB₁ sB₀ v hv r hvr k (properPushforward C sA₀ sB₀ u₀ hu₀ k z) =
      properPushforward C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ))
        (flatPullback C sA₁ sA₀ d hd r hdr k z) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun b₁ ↦ ?_)
  obtain ⟨a₁, rfl⟩ := exists_base_eq_of_isIso u₁ b₁
  have hpt := base_apply_eq_of_comp_eq hsq a₁
  rw [properPushforward_apply_of_isIso C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ)) _ a₁,
    flatPullback_apply, flatPullback_apply, ← hpt,
    properPushforward_apply_of_isIso C sA₀ sB₀ u₀ hu₀ k z (d.base a₁),
    flatPullbackWeight_eq_of_isIso C sA₁ sB₁ u₀ u₁ hu₁ d v hsq (k + (r : ℤ)) a₁]

/-- **Flat pullback commutes with pushforward along two isomorphism legs, on Chow groups.** In a
square over the base whose two horizontal legs are isomorphisms — hence automatically cartesian —
flat pullback commutes with pushforward along the isomorphisms, on Chow groups. -/
@[stacks 02RG "the case of two isomorphism legs"]
theorem flatPullbackChow_chowPushforwardOfIso (C : ChowSituation.{u})
    {A₀ A₁ B₀ B₁ : Scheme.{u}} (sA₀ : A₀ ⟶ C.S) [LocallyOfFiniteType sA₀]
    (sA₁ : A₁ ⟶ C.S) [LocallyOfFiniteType sA₁] (sB₀ : B₀ ⟶ C.S) [LocallyOfFiniteType sB₀]
    (sB₁ : B₁ ⟶ C.S) [LocallyOfFiniteType sB₁]
    (u₀ : A₀ ⟶ B₀) [IsIso u₀] (hu₀ : u₀ ≫ sB₀ = sA₀)
    (u₁ : A₁ ⟶ B₁) [IsIso u₁] (hu₁ : u₁ ≫ sB₁ = sA₁)
    (d : A₁ ⟶ A₀) [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sA₀ = sA₁)
    (v : B₁ ⟶ B₀) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB₀ = sB₁)
    (hsq : d ≫ u₀ = u₁ ≫ v) (r : ℕ)
    (hdr : AlgebraicGeometry.RelativeDimension d r)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hfacd : FlatPullbackFactorsThroughRationalEquivalence C sA₁ sA₀ d hd r hdr k)
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sB₁ sB₀ v hv r hvr k)
    (α : chowGroup C sA₀ k) :
    flatPullbackChow C sB₁ sB₀ v hv r hvr k hfacv
        (chowPushforwardOfIso C sA₀ sB₀ u₀ hu₀ k α) =
      chowPushforwardOfIso C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ))
        (flatPullbackChow C sA₁ sA₀ d hd r hdr k hfacd α) := by
  induction α using QuotientAddGroup.induction_on with
  | H z =>
    change flatPullbackChow C sB₁ sB₀ v hv r hvr k hfacv
        (chowPushforwardOfIso C sA₀ sB₀ u₀ hu₀ k
          (QuotientAddGroup.mk' (rationalEquivalences C sA₀ k) z)) =
      chowPushforwardOfIso C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ))
        (flatPullbackChow C sA₁ sA₀ d hd r hdr k hfacd
          (QuotientAddGroup.mk' (rationalEquivalences C sA₀ k) z))
    simp only [chowPushforwardOfIso_mk, flatPullbackChow_mk]
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sB₁ (k + (r : ℤ))))
      (flatPullback_properPushforward_of_isIso C sA₀ sA₁ sB₀ sB₁ u₀ hu₀ u₁ hu₁ d hd v hv hsq r
        hdr hvr k z)

/-! ### Stacks 02S1 along a transported flat morphism -/

/-- **Stacks 02S1 along a transported flat morphism.** In a square `d ≫ u₀ = u₁ ≫ v` over the
base with `u₀` and `u₁` isomorphisms, flat pullback along `d` factors through rational
equivalence as soon as flat pullback along `v` does. -/
theorem flatPullbackFactorsThroughRationalEquivalence_of_isIso_square (C : ChowSituation.{u})
    {A₀ A₁ B₀ B₁ : Scheme.{u}} (sA₀ : A₀ ⟶ C.S) [LocallyOfFiniteType sA₀]
    (sA₁ : A₁ ⟶ C.S) [LocallyOfFiniteType sA₁] (sB₀ : B₀ ⟶ C.S) [LocallyOfFiniteType sB₀]
    (sB₁ : B₁ ⟶ C.S) [LocallyOfFiniteType sB₁]
    (u₀ : A₀ ⟶ B₀) [IsIso u₀] (hu₀ : u₀ ≫ sB₀ = sA₀)
    (u₁ : A₁ ⟶ B₁) [IsIso u₁] (hu₁ : u₁ ≫ sB₁ = sA₁)
    (d : A₁ ⟶ A₀) [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sA₀ = sA₁)
    (v : B₁ ⟶ B₀) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB₀ = sB₁)
    (hsq : d ≫ u₀ = u₁ ≫ v) (r : ℕ)
    (hdr : AlgebraicGeometry.RelativeDimension d r)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sB₁ sB₀ v hv r hvr k) :
    FlatPullbackFactorsThroughRationalEquivalence C sA₁ sA₀ d hd r hdr k := by
  intro a ha
  have hinv : inv u₁ ≫ sA₁ = sB₁ := by rw [← hu₁]; simp
  have h2 := hfacv _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA₀ sB₀ u₀ hu₀ k a ha)
  rw [flatPullback_properPushforward_of_isIso C sA₀ sA₁ sB₀ sB₁ u₀ hu₀ u₁ hu₁ d hd v hv hsq r
    hdr hvr k a] at h2
  have h3 := properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB₁ sA₁ (inv u₁)
    hinv (k + (r : ℤ)) _ h2
  rwa [properPushforward_properPushforward C sA₁ sB₁ sA₁ u₁ (inv u₁) hu₁ hinv (k + (r : ℤ)),
    properPushforward_congr C sA₁ sA₁ (u₁ ≫ inv u₁) (𝟙 A₁) (by simp) (by simp)
      (Category.id_comp sA₁) (k + (r : ℤ)), properPushforward_id] at h3

end Stacks.Chow

end
