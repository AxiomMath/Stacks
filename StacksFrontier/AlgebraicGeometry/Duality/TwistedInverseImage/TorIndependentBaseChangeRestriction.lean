module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangePasteHoriz
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionQcqs
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalization
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction

/-!
# The base change map of the twisted inverse image restricted to opens

Consider a cartesian square of quasi-compact and quasi-separated schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` and `g` Tor independent, and quasi-compact opens `V ⊆ Y`, `V' ⊆ Y'` with `g(V') ⊆ V`.
Set `U = f⁻¹(V)` and `U' = (f')⁻¹(V')`. The square

```
U' --g'|--> U
|           |
f'|         f|
v           v
V' --g|---> V
```

is again cartesian
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare`) and Tor
independent (`AlgebraicGeometry.torIndependent_morphismRestrict_resLE`). [Stacks, Tag 0E9S] says
that if the maps
`(j')^* ∘ a ⟶ a_U ∘ j^*` of [Stacks, Tag 0A9L] for `U ⊆ X` over `V ⊆ Y` at `K` and for `U' ⊆ X'`
over `V' ⊆ Y'` at `Lg^* K` are isomorphisms, then the restriction to `U'` of the base change map
`L(g')^* a(K) ⟶ a'(Lg^* K)` of [Stacks, Tag 0AA6] is isomorphic to the base change map of the
square of opens at `K|_V`. The proof is the source's: the map of Tag 0A9L is the base change map
of the square `U ⟶ X` over `V ⟶ Y` once restriction is identified with derived pullback, and the
base change maps of the two factorizations of the outer rectangle
`U' ⟶ X' ⟶ X = U' ⟶ U ⟶ X` agree by [Stacks, Tag 0ATR].

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedPullbackRestrictIso` — `Li^* ≅ i^*` on `D_QCoh` for an open
  immersion `i`.
* `Stacks.Duality.quasiCoherentDerivedRestrictPullbackIso` — `(i')^* ∘ Lk^* ≅ Lh^* ∘ i^*` for a
  commutative square whose horizontal sides are open immersions.
* `Stacks.Duality.torIndependentTwistedInverseImageBaseChangeRestrictArrowIso` —
  [Stacks, Tag 0E9S].

## Main results

* `Stacks.Duality.torIndependentTwistedInverseImageBaseChange_restrict_app` — the map of
  Tag 0A9L is the base change map of Tag 0AA6 for the open square.
* `Stacks.Duality.torIndependentTwistedInverseImageBaseChange_restrict_comm` — the commutative
  square identifying the restriction of the base change map with that of the square of opens.

## Implementation notes

The source takes `V` and `V'` affine; only their quasi-compactness is used, which is what the
map of Tag 0A9L needs, so the opens are quasi-compact here. Restriction to `U'` is the exact
restriction `Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrict`, as in Tag 0A9L.

## References

* [Stacks Project, Tag 0E9S](https://stacks.math.columbia.edu/tag/0E9S)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open OpenImmersion
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology (preimage_le_of_comm
  isPullback_restrictBasesSquare)

local notation "Lq[" f "]" => quasiCoherentDerivedPullback' f
local notation "Rs[" j "]" =>
  quasiCoherentDerivedRestrict j (isQuasicoherent_homology_derivedRestrict j)
local notation "a[" f "]" =>
  twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)

section Comparison

/-- A functor applied to the components of an isomorphism of functors and its inverse. -/
@[reassoc]
private lemma map_inv_hom_app {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (X : C) :
    H.map (e.inv.app X) ≫ H.map (e.hom.app X) = 𝟙 _ := by
  rw [← H.map_comp, Iso.inv_hom_id_app, H.map_id]

/-- A functor applied to the components of an isomorphism of functors and its inverse. -/
@[reassoc]
private lemma map_hom_inv_app {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (X : C) :
    H.map (e.hom.app X) ≫ H.map (e.inv.app X) = 𝟙 _ := by
  rw [← H.map_comp, Iso.hom_inv_id_app, H.map_id]

variable {A B A' B' : Scheme.{u}} [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace B]
  [QuasiSeparatedSpace B] [CompactSpace A'] [QuasiSeparatedSpace A'] [CompactSpace B']
  [QuasiSeparatedSpace B']

/-- **Derived pullback along an open immersion is restriction.** For an open immersion
`i : A ⟶ B` of quasi-compact quasi-separated schemes, `Li^*` and the exact restriction `i^*` are
both left adjoint to `Ri_*` on `D_QCoh`, hence canonically isomorphic. -/
def quasiCoherentDerivedPullbackRestrictIso (i : A ⟶ B) [IsOpenImmersion i] : Lq[i] ≅ Rs[i] :=
  Adjunction.leftAdjointUniq
    (quasiCoherentDerivedAdjunction i (isQuasicoherent_homology_derivedPullback' i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i))
    (quasiCoherentDerivedRestrictAdjunction i (isQuasicoherent_homology_derivedRestrict i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i))

/-- **Restriction to opens commutes with derived pullback.** For a commutative square
`i' ≫ k = h ≫ i` of quasi-compact quasi-separated schemes whose horizontal sides `i`, `i'` are
open immersions, `(i')^* ∘ Lk^* ≅ Lh^* ∘ i^*` on `D_QCoh`: identify the restrictions with derived
pullbacks and compose. -/
def quasiCoherentDerivedRestrictPullbackIso (i : A ⟶ B) (i' : A' ⟶ B') (h : A' ⟶ A)
    (k : B' ⟶ B) [IsOpenImmersion i] [IsOpenImmersion i'] (w : i' ≫ k = h ≫ i) :
    Lq[k] ⋙ Rs[i'] ≅ Rs[i] ⋙ Lq[h] :=
  Functor.isoWhiskerLeft Lq[k] (quasiCoherentDerivedPullbackRestrictIso i').symm ≪≫
    quasiCoherentDerivedPullbackCompIso i' k ≪≫ quasiCoherentDerivedPullbackCongr w ≪≫
    (quasiCoherentDerivedPullbackCompIso h i).symm ≪≫
    Functor.isoWhiskerRight (quasiCoherentDerivedPullbackRestrictIso i) Lq[h]

end Comparison

section Square

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The base change map of the twisted inverse image along equal morphisms: the two maps differ by
the identifications of the derived pullbacks. -/
theorem twistedInverseImageBaseChangeMap_congr_app {t₁ t₂ : X' ⟶ X} {b₁ b₂ : Y' ⟶ Y}
    (ht : t₁ = t₂) (hb : b₁ = b₂) (sq₁ : IsPullback t₁ f' f b₁) (sq₂ : IsPullback t₂ f' f b₂)
    [IsIso (twistedInverseImagePushforwardBaseChange t₁ f' f b₁
      (isQuasicoherent_homology_derivedPushforward_of_qcqs t₁)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b₁) sq₁)]
    [IsIso (twistedInverseImagePushforwardBaseChange t₂ f' f b₂
      (isQuasicoherent_homology_derivedPushforward_of_qcqs t₂)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b₂) sq₂)]
    (K : quasiCoherentDerivedCategory Y) :
    (twistedInverseImageBaseChangeMap t₁ f' f b₁
        (isQuasicoherent_homology_derivedPushforward_of_qcqs t₁)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs b₁) sq₁).app K =
      (quasiCoherentDerivedPullbackCongr ht).hom.app (a[f].obj K) ≫
        (twistedInverseImageBaseChangeMap t₂ f' f b₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs t₂)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b₂) sq₂).app K ≫
        a[f'].map ((quasiCoherentDerivedPullbackCongr hb).inv.app K) := by
  subst ht hb
  have h₁ : (quasiCoherentDerivedPullbackCongr (rfl : t₁ = t₁)).hom.app (a[f].obj K) = 𝟙 _ :=
    rfl
  have h₂ : (quasiCoherentDerivedPullbackCongr (rfl : b₁ = b₁)).inv.app K = 𝟙 _ := rfl
  rw [h₁, h₂, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

end Square

section Open

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (f : X ⟶ Y) (V : Y.Opens) [CompactSpace V]

/-- **The map of [Stacks, Tag 0A9L] is a special case of the base change map of
[Stacks, Tag 0AA6]**: for the cartesian square `U = f⁻¹(V) ⟶ X` over `V ⟶ Y`, Tor independent
since `V ⟶ Y` is flat, the base change map `L(j')^* a(K) ⟶ a'(Lj^* K)` is the map
`(j')^* a(K) ⟶ a'(j^* K)` of Tag 0A9L once restriction is identified with derived pullback. -/
theorem torIndependentTwistedInverseImageBaseChange_restrict_app
    (K : quasiCoherentDerivedCategory Y) :
    (torIndependentTwistedInverseImageBaseChange (isPullback_morphismRestrict f V).flip
        (torIndependent_of_flat_right f V.ι)).app K =
      (quasiCoherentDerivedPullbackRestrictIso (f ⁻¹ᵁ V).ι).hom.app (a[f].obj K) ≫
        (qcqsTwistedInverseImageRestrictionMap f V).app K ≫
        a[f ∣_ V].map ((quasiCoherentDerivedPullbackRestrictIso V.ι).inv.app K) := by
  have := isIso_rightAdjointSquare_of_isOpenImmersion (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
    (isPullback_morphismRestrict f V).flip
  simp only [torIndependentTwistedInverseImageBaseChange]
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange,
    rightAdjointBaseChange_app_eq_twistedInverseImageRestrictionMap]
  rfl

/-- The map of Tag 0A9L in terms of the base change map of Tag 0AA6 and the identifications of
restriction with derived pullback. -/
private theorem qcqsTwistedInverseImageRestrictionMap_app_eq
    (K : quasiCoherentDerivedCategory Y) :
    (qcqsTwistedInverseImageRestrictionMap f V).app K =
      (quasiCoherentDerivedPullbackRestrictIso (f ⁻¹ᵁ V).ι).inv.app (a[f].obj K) ≫
        (torIndependentTwistedInverseImageBaseChange (isPullback_morphismRestrict f V).flip
          (torIndependent_of_flat_right f V.ι)).app K ≫
        a[f ∣_ V].map ((quasiCoherentDerivedPullbackRestrictIso V.ι).hom.app K) := by
  rw [torIndependentTwistedInverseImageBaseChange_restrict_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, map_inv_hom_app]
  exact (Category.comp_id _).symm

end Open

section Restriction

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) (hTor : TorIndependent f g) (V : Y.Opens) (V' : Y'.Opens)
  [CompactSpace V] [CompactSpace V'] (hVV' : V' ≤ g ⁻¹ᵁ V)

/-- **The restriction of the base change map to `U'`, as a commutative square.** For a Tor
independent cartesian square of quasi-compact quasi-separated schemes and quasi-compact opens
`V ⊆ Y`, `V' ⊆ Y'` with `g(V') ⊆ V`, write `γ` for the base change map of [Stacks, Tag 0AA6],
`γ_V` for that of the square of opens `U' ⟶ U` over `V' ⟶ V`, and `ρ`, `ρ'` for the maps of
[Stacks, Tag 0A9L] for `U ⊆ X` over `V ⊆ Y` and `U' ⊆ X'` over `V' ⊆ Y'`. Then
```
γ(K)|_{U'} ≫ ρ'(Lg^* K) ≫ a_{U'}((Lg^*K)|_{V'} ≅ L(g|)^*(K|_V))
  = ((L(g')^* a(K))|_{U'} ≅ L(g'|)^*(a(K)|_U)) ≫ L(g'|)^* ρ(K) ≫ γ_V(K|_V).
``` -/
@[stacks 0E9S "the commutative square of maps exhibiting the isomorphism: the two maps of 0A9L \
and the identifications of restriction with derived pullback carry the restriction to U' of the \
base change map 0AA6 to that of the square of opens"]
theorem torIndependentTwistedInverseImageBaseChange_restrict_comm
    (K : quasiCoherentDerivedCategory Y) :
    Rs[(f' ⁻¹ᵁ V').ι].map ((torIndependentTwistedInverseImageBaseChange sq hTor).app K) ≫
        (qcqsTwistedInverseImageRestrictionMap f' V').app (Lq[g].obj K) ≫
        a[f' ∣_ V'].map ((quasiCoherentDerivedRestrictPullbackIso V.ι V'.ι (g.resLE V V' hVV') g
          (Scheme.Hom.resLE_comp_ι g hVV').symm).hom.app K) =
      (quasiCoherentDerivedRestrictPullbackIso (f ⁻¹ᵁ V).ι (f' ⁻¹ᵁ V').ι
          (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
            (preimage_le_of_comm sq.w hVV')) g'
          (Scheme.Hom.resLE_comp_ι g'
            (preimage_le_of_comm sq.w hVV')).symm).hom.app
          (a[f].obj K) ≫
        Lq[g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
            (preimage_le_of_comm sq.w hVV')].map
          ((qcqsTwistedInverseImageRestrictionMap f V).app K) ≫
        (torIndependentTwistedInverseImageBaseChange (isPullback_restrictBasesSquare sq V hVV')
          (torIndependent_morphismRestrict_resLE f g hTor hVV')).app (Rs[V.ι].obj K) := by
  have hU := preimage_le_of_comm sq.w hVV'
  set g'U := g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') hU
  set gV := g.resLE V V' hVV'
  have ht : (f' ⁻¹ᵁ V').ι ≫ g' = g'U ≫ (f ⁻¹ᵁ V).ι := (Scheme.Hom.resLE_comp_ι g' hU).symm
  have hb : V'.ι ≫ g = gV ≫ V.ι := (Scheme.Hom.resLE_comp_ι g hVV').symm
  have sqR1 := (isPullback_morphismRestrict f' V').flip.paste_horiz sq
  have sqR2 := (isPullback_restrictBasesSquare sq V hVV').paste_horiz
    (isPullback_morphismRestrict f V).flip
  have := isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz sq
    (isPullback_morphismRestrict f' V').flip hTor (torIndependent_of_flat_right f' V'.ι)
  have := isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz
    (isPullback_morphismRestrict f V).flip (isPullback_restrictBasesSquare sq V hVV')
    (torIndependent_of_flat_right f V.ι) (torIndependent_morphismRestrict_resLE f g hTor hVV')
  have hC := twistedInverseImageBaseChangeMap_congr_app ht hb sqR1 sqR2 K
  rw [twistedInverseImageBaseChangeMap_paste_horiz_app sq (isPullback_morphismRestrict f' V').flip
      hTor (torIndependent_of_flat_right f' V'.ι) K,
    twistedInverseImageBaseChangeMap_paste_horiz_app (isPullback_morphismRestrict f V).flip
      (isPullback_restrictBasesSquare sq V hVV') (torIndependent_of_flat_right f V.ι)
      (torIndependent_morphismRestrict_resLE f g hTor hVV') K] at hC
  have hstar := hC
  rw [← cancel_epi ((quasiCoherentDerivedPullbackCompIso (f' ⁻¹ᵁ V').ι g').hom.app
    (a[f].obj K))] at hstar
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at hstar
  rw [qcqsTwistedInverseImageRestrictionMap_app_eq f V K,
    qcqsTwistedInverseImageRestrictionMap_app_eq f' V' (Lq[g].obj K)]
  simp only [quasiCoherentDerivedRestrictPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    map_hom_inv_app_assoc]
  have hnat := (torIndependentTwistedInverseImageBaseChange
    (isPullback_restrictBasesSquare sq V hVV')
      (torIndependent_morphismRestrict_resLE f g hTor hVV')).naturality
      ((quasiCoherentDerivedPullbackRestrictIso V.ι).hom.app K)
  simp only [Functor.comp_map] at hnat
  have hnat₂ := (quasiCoherentDerivedPullbackRestrictIso (f' ⁻¹ᵁ V').ι).inv.naturality
    ((torIndependentTwistedInverseImageBaseChange sq hTor).app K)
  rw [hnat, reassoc_of% hnat₂, reassoc_of% hstar]
  simp only [map_hom_inv_app_assoc, map_inv_hom_app_assoc]

/-- **[Stacks, Tag 0E9S].** Consider a cartesian square of quasi-compact and quasi-separated
schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` and `g` Tor independent, and quasi-compact (for instance affine) opens `V ⊆ Y`,
`V' ⊆ Y'` with `g(V') ⊆ V`; set `U = f⁻¹(V)`, `U' = (f')⁻¹(V')`. Assume that the map of
[Stacks, Tag 0A9L] for `U ⊆ X` over `V ⊆ Y` is an isomorphism at `K`, and that for `U' ⊆ X'` over
`V' ⊆ Y'` it is an isomorphism at `Lg^* K`. Then the restriction to `U'` of the base change map
`L(g')^* a(K) ⟶ a'(Lg^* K)` of [Stacks, Tag 0AA6] is isomorphic, as an arrow, to the base change
map of Tag 0AA6 for `K|_V` and the cartesian square `U' ⟶ U` over `V' ⟶ V`
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare`, Tor
independent by `AlgebraicGeometry.torIndependent_morphismRestrict_resLE`). The two components are
the two maps of Tag 0A9L composed with the identifications of restriction and derived pullback;
the square commutes by
`Stacks.Duality.torIndependentTwistedInverseImageBaseChange_restrict_comm`. -/
@[stacks 0E9S]
def torIndependentTwistedInverseImageBaseChangeRestrictArrowIso
    (K : quasiCoherentDerivedCategory Y)
    [IsIso ((qcqsTwistedInverseImageRestrictionMap f V).app K)]
    [IsIso ((qcqsTwistedInverseImageRestrictionMap f' V').app (Lq[g].obj K))] :
    Arrow.mk (Rs[(f' ⁻¹ᵁ V').ι].map ((torIndependentTwistedInverseImageBaseChange sq hTor).app K)) ≅
      Arrow.mk ((torIndependentTwistedInverseImageBaseChange
        (isPullback_restrictBasesSquare sq V hVV')
          (torIndependent_morphismRestrict_resLE f g hTor hVV')).app
          (Rs[V.ι].obj K)) :=
  Arrow.isoMk
    ((quasiCoherentDerivedRestrictPullbackIso (f ⁻¹ᵁ V).ι (f' ⁻¹ᵁ V').ι
        (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
          (preimage_le_of_comm sq.w hVV')) g'
        (Scheme.Hom.resLE_comp_ι g'
          (preimage_le_of_comm sq.w hVV')).symm).app (a[f].obj K) ≪≫
      Lq[g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V')
          (preimage_le_of_comm sq.w hVV')].mapIso
        (asIso ((qcqsTwistedInverseImageRestrictionMap f V).app K)))
    (asIso ((qcqsTwistedInverseImageRestrictionMap f' V').app (Lq[g].obj K)) ≪≫
      a[f' ∣_ V'].mapIso ((quasiCoherentDerivedRestrictPullbackIso V.ι V'.ι (g.resLE V V' hVV') g
        (Scheme.Hom.resLE_comp_ι g hVV').symm).app K))
    (by
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom, Arrow.mk_hom,
        Category.assoc]
      exact (torIndependentTwistedInverseImageBaseChange_restrict_comm sq hTor V V' hVV' K).symm)

end Restriction

end Stacks.Duality
