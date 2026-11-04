module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.CoverRepresentatives
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic

/-!
# The induction of Stacks 0DJ9 over the quasi-compact opens of the source

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, and
let `T ⟶ S`, `T' ⟶ S'` be open immersions with `g(T') ⊆ T` through `g_T : T' ⟶ T`.  An open
`U ⊆ X` lying over `T` is *good* when for every open immersion `j : Z ⟶ X` with image `U` and
every cartesian square

```
Z' --g_Z--> Z
|           |
v           v
T' --g_T--> T
```

over it, with `j' : Z' ⟶ X'` an open immersion compatible with `g'`, the composition
`Lg_T^*R(Z ⟶ T)_*(Lj^*K) ⟶ R(Z' ⟶ T')_*(L(j')^*K')` attached to the pulled-back datum is
invertible.  Goodness passes from two opens and their intersection to their union, and so, by the
induction principle of Stacks 08DR, from the affine opens to every quasi-compact open.

## Main definitions

* `Stacks.Cohomology.BaseChangeCover.RepGood`: goodness of an open of `X`.

## Main results

* `Stacks.Cohomology.BaseChangeCover.repGood_sup`: the Mayer--Vietoris step.
* `Stacks.Cohomology.BaseChangeCover.repGood_of_isCompact`: the induction.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChangeCover

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.DerivedMayerVietoris
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Invariance under an isomorphism of data.** -/
theorem isIso_bc_iff_of_iso {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    {L₁ L₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {L₁' L₂' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (φ₁ : (derivedPullback g').obj L₁ ⟶ L₁') (φ₂ : (derivedPullback g').obj L₂ ⟶ L₂')
    (u : L₁ ⟶ L₂) (v : L₁' ⟶ L₂') [IsIso u] [IsIso v]
    (h : (derivedPullback g').map u ≫ φ₂ = φ₁ ≫ v) :
    IsIso (derivedBaseChangeMap g' f' f g sq L₁ ≫ (derivedPushforward f').map φ₁) ↔
      IsIso (derivedBaseChangeMap g' f' f g sq L₂ ≫ (derivedPushforward f').map φ₂) :=
  isIso_iff_of_comm _ ((derivedPullback g).map ((derivedPushforward f).map u)) _
    ((derivedPushforward f').map v)
    (chase_of_naturality _ _ _ _ _ _ _ (derivedBaseChangeMap_naturality g' f' f g sq u)
      (((derivedPushforward f').map_comp _ _).symm.trans
        ((congrArg (derivedPushforward f').map h).trans ((derivedPushforward f').map_comp _ _))))

variable {X X' S S' T T' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (iT : T ⟶ S) (iT' : T' ⟶ S') (gT : T' ⟶ T)
  (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
  (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
  (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')

/-- The composition over a representative square, attached to the pulled-back datum. -/
scoped macro "repComp% " g':term:max ppSpace gT:term:max ppSpace K:term:max ppSpace
    K':term:max ppSpace φ:term:max ppSpace j:term:max ppSpace j':term:max ppSpace
    fZ:term:max ppSpace fZ':term:max ppSpace gZ:term:max ppSpace hg:term:max ppSpace
    hq:term:max : term =>
  `((bcNatTrans (Scheme.Hom.toLRSHom $gZ).toShHom (Scheme.Hom.toLRSHom $fZ').toShHom
      (Scheme.Hom.toLRSHom $fZ).toShHom (Scheme.Hom.toLRSHom $gT).toShHom
      (comp_toShHom_of_comm $hq)).app
      ((derivedPullback (Scheme.Hom.toLRSHom $j).toShHom).obj $K) ≫
    (derivedPushforward (Scheme.Hom.toLRSHom $fZ').toShHom).map
      (pullDatum (Scheme.Hom.toLRSHom $gZ).toShHom (Scheme.Hom.toLRSHom $j').toShHom
        (Scheme.Hom.toLRSHom $j).toShHom (Scheme.Hom.toLRSHom $g').toShHom
        (comp_toShHom_of_comm $hg) $K $K' $φ))

/-- **Goodness of an open `U` of `X`**: the composition over every representative square of `U`
is invertible. -/
scoped macro "repGood% " f:term:max ppSpace f':term:max ppSpace g':term:max ppSpace
    iT:term:max ppSpace iT':term:max ppSpace gT:term:max ppSpace K:term:max ppSpace
    K':term:max ppSpace φ:term:max ppSpace U:term:max : term =>
  `(∀ ⦃Z Z' : Scheme⦄ (j : Z ⟶ _) (j' : Z' ⟶ _) (fZ : Z ⟶ _) (fZ' : Z' ⟶ _) (gZ : Z' ⟶ Z)
      [IsOpenImmersion j] [IsOpenImmersion j'], Scheme.Hom.opensRange j = $U →
      fZ ≫ $iT = j ≫ $f → fZ' ≫ $iT' = j' ≫ $f' →
      ∀ (hg : gZ ≫ j = j' ≫ $g') (hq : IsPullback gZ fZ' fZ $gT),
        IsIso (repComp% $g' $gT $K $K' $φ j j' fZ fZ' gZ hg hq.w))

/-- The restriction to an open of a representative is a representative. -/
theorem isIso_rectComp_of_repComp {Z Z' : Scheme.{u}} (j : Z ⟶ X) (j' : Z' ⟶ X') (fZ : Z ⟶ T)
    (fZ' : Z' ⟶ T') (gZ : Z' ⟶ Z) (hg : gZ ≫ j = j' ≫ g') (hq : gZ ≫ fZ = fZ' ≫ gT)
    (Z₀ : Z.Opens) (Z₀' : Z'.Opens) (e : Z₀' ≤ gZ ⁻¹ᵁ Z₀)
    (hg₀ : gZ.resLE Z₀ Z₀' e ≫ Z₀.ι ≫ j = (Z₀'.ι ≫ j') ≫ g')
    (hq₀ : gZ.resLE Z₀ Z₀' e ≫ Z₀.ι ≫ fZ = (Z₀'.ι ≫ fZ') ≫ gT)
    (h : IsIso (repComp% g' gT K K' φ (Z₀.ι ≫ j) (Z₀'.ι ≫ j') (Z₀.ι ≫ fZ) (Z₀'.ι ≫ fZ')
      (gZ.resLE Z₀ Z₀' e) hg₀ hq₀)) :
    IsIso (rectComp fZ gT fZ' gZ (comp_toShHom_of_comm hq) Z₀ Z₀' e
      ((derivedPullback j.toLRSHom.toShHom).obj K) ((derivedPullback j'.toLRSHom.toShHom).obj K')
      (pullDatum gZ.toLRSHom.toShHom j'.toLRSHom.toShHom j.toLRSHom.toShHom g'.toLRSHom.toShHom
        (comp_toShHom_of_comm hg) K K' φ)) := by
  rw [bcNatTrans_app] at h
  exact (isIso_bc_iff_of_iso (resMap gZ Z₀ Z₀' e) (incl Z₀' ≫ fZ'.toLRSHom.toShHom)
    (incl Z₀ ≫ fZ.toLRSHom.toShHom) gT.toLRSHom.toShHom
    (comp_square _ _ _ _ _ _ _ (resMap_comp gZ Z₀ Z₀' e) (comp_toShHom_of_comm hq)) _ _
    ((derivedPullbackCompIsoCanonical (incl Z₀) j.toLRSHom.toShHom).hom.app K)
    ((derivedPullbackCompIsoCanonical (incl Z₀') j'.toLRSHom.toShHom).hom.app K')
    (pullDatum_comp (resMap gZ Z₀ Z₀' e) (incl Z₀') (incl Z₀) gZ.toLRSHom.toShHom
      j'.toLRSHom.toShHom j.toLRSHom.toShHom g'.toLRSHom.toShHom (resMap_comp gZ Z₀ Z₀' e)
      (comp_toShHom_of_comm hg) K K' φ)).2 h

/-- The square of a representative restricted to an open and its preimage is cartesian. -/
theorem isPullback_resLE_of_isPullback {Z Z' : Scheme.{u}} (fZ : Z ⟶ T) (fZ' : Z' ⟶ T')
    (gZ : Z' ⟶ Z) (hq : IsPullback gZ fZ' fZ gT) (Z₀ : Z.Opens) (Z₀' : Z'.Opens)
    (h : gZ ⁻¹ᵁ Z₀ = Z₀') :
    IsPullback (gZ.resLE Z₀ Z₀' h.ge) (Z₀'.ι ≫ fZ') (Z₀.ι ≫ fZ) gT :=
  (IsOpenImmersion.isPullback (gZ.resLE Z₀ Z₀' h.ge) Z₀'.ι Z₀.ι gZ
    (gZ.resLE_comp_ι _).symm (by simpa using h)).paste_vert hq

variable {f g f' g' iT iT' gT K K' φ}

/-- A good open restricts, along a representative, to an invertible composition. -/
theorem isIso_rectComp_of_repGood {Z Z' : Scheme.{u}} (j : Z ⟶ X) (j' : Z' ⟶ X') (fZ : Z ⟶ T)
    (fZ' : Z' ⟶ T') (gZ : Z' ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion j']
    (hf : fZ ≫ iT = j ≫ f) (hf' : fZ' ≫ iT' = j' ≫ f') (hg : gZ ≫ j = j' ≫ g')
    (hq : IsPullback gZ fZ' fZ gT) (Z₀ : Z.Opens) (Z₀' : Z'.Opens) (h : gZ ⁻¹ᵁ Z₀ = Z₀')
    (W : X.Opens) (hW : Scheme.Hom.opensRange (Z₀.ι ≫ j) = W)
    (hgood : repGood% f f' g' iT iT' gT K K' φ W) :
    IsIso (rectComp fZ gT fZ' gZ (comp_toShHom_of_comm hq.w) Z₀ Z₀' h.ge
        ((derivedPullback j.toLRSHom.toShHom).obj K)
        ((derivedPullback j'.toLRSHom.toShHom).obj K')
        (pullDatum gZ.toLRSHom.toShHom j'.toLRSHom.toShHom j.toLRSHom.toShHom
          g'.toLRSHom.toShHom (comp_toShHom_of_comm hg) K K' φ)) :=
  isIso_rectComp_of_repComp g' gT K K' φ j j' fZ fZ' gZ hg hq.w _ _ h.ge
    (by rw [Scheme.Hom.resLE_comp_ι_assoc, hg, Category.assoc])
    (isPullback_resLE_of_isPullback gT fZ fZ' gZ hq _ _ h).w
    (hgood (Z₀.ι ≫ j) (Z₀'.ι ≫ j') (Z₀.ι ≫ fZ) (Z₀'.ι ≫ fZ') (gZ.resLE Z₀ Z₀' h.ge) hW
      (by rw [Category.assoc, hf, Category.assoc]) (by rw [Category.assoc, hf', Category.assoc])
      (by rw [Scheme.Hom.resLE_comp_ι_assoc, hg, Category.assoc])
      (isPullback_resLE_of_isPullback gT fZ fZ' gZ hq _ _ h))

/-- **The Mayer--Vietoris step for goodness.** -/
theorem repGood_sup (U V : X.Opens) (hU : repGood% f f' g' iT iT' gT K K' φ U)
    (hV : repGood% f f' g' iT iT' gT K K' φ V)
    (hUV : repGood% f f' g' iT iT' gT K K' φ (U ⊓ V)) :
    repGood% f f' g' iT iT' gT K K' φ (U ⊔ V) := by
  intro Z Z' j j' fZ fZ' gZ _ _ hr hf hf' hg hq
  have hpre : ∀ W : X.Opens, W ≤ U ⊔ V → Scheme.Hom.opensRange ((j ⁻¹ᵁ W).ι ≫ j) = W := by
    intro W hW
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_eq_right.mpr hW]
  have hAB : j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ← hr, Scheme.Hom.preimage_opensRange]
  have key := fun W (hW : W ≤ U ⊔ V) =>
    isIso_rectComp_of_repGood (K := K) (K' := K') (φ := φ) j j' fZ fZ' gZ hf hf' hg hq
      (j ⁻¹ᵁ W) _ rfl W (hpre W hW)
  exact isIso_of_cover fZ gT fZ' gZ (comp_toShHom_of_comm hq.w) (j ⁻¹ᵁ U) (j ⁻¹ᵁ V) hAB
    ((derivedPullback j.toLRSHom.toShHom).obj K) ((derivedPullback j'.toLRSHom.toShHom).obj K')
    (pullDatum gZ.toLRSHom.toShHom j'.toLRSHom.toShHom j.toLRSHom.toShHom
      g'.toLRSHom.toShHom (comp_toShHom_of_comm hg) K K' φ) (key U le_sup_left hU)
    (key V le_sup_right hV) (key (U ⊓ V) (inf_le_left.trans le_sup_left) hUV)

/-- The image of a union under an open immersion. -/
theorem image_sup_of_isOpenImmersion {W Y : Scheme.{u}} (ι : W ⟶ Y) [IsOpenImmersion ι]
    (U V : W.Opens) : ι ''ᵁ (U ⊔ V) = ι ''ᵁ U ⊔ ι ''ᵁ V :=
  TopologicalSpace.Opens.ext (Set.image_union _ _ _)

/-- The image of an intersection under an open immersion. -/
theorem image_inf_of_isOpenImmersion {W Y : Scheme.{u}} (ι : W ⟶ Y) [IsOpenImmersion ι]
    (U V : W.Opens) : ι ''ᵁ (U ⊓ V) = ι ''ᵁ U ⊓ ι ''ᵁ V :=
  TopologicalSpace.Opens.ext (Set.image_inter ι.isOpenEmbedding.injective)

/-- The Mayer--Vietoris step for goodness, read on images of opens of an open subscheme. -/
theorem repGood_image_sup (W : X.Opens) (U₀ V₀ : W.toScheme.Opens)
    (hU : repGood% f f' g' iT iT' gT K K' φ (W.ι ''ᵁ U₀))
    (hV : repGood% f f' g' iT iT' gT K K' φ (W.ι ''ᵁ V₀))
    (hUV : repGood% f f' g' iT iT' gT K K' φ (W.ι ''ᵁ (U₀ ⊓ V₀))) :
    repGood% f f' g' iT iT' gT K K' φ (W.ι ''ᵁ (U₀ ⊔ V₀)) := by
  rw [image_sup_of_isOpenImmersion]
  rw [image_inf_of_isOpenImmersion] at hUV
  exact repGood_sup _ _ hU hV hUV

/-- **The induction of Stacks 0DJ9.** Over an affine `T`, with `f` quasi-compact and
quasi-separated, goodness of the affine opens over `T` implies goodness of `f^{-1}(T)`. -/
theorem repGood_of_affineOpens [IsAffine T] [IsOpenImmersion iT] [QuasiCompact f]
    [QuasiSeparated f]
    (hbase : ∀ U : X.Opens, IsAffineOpen U → U ≤ f ⁻¹ᵁ iT.opensRange →
      repGood% f f' g' iT iT' gT K K' φ U) :
    repGood% f f' g' iT iT' gT K K' φ (f ⁻¹ᵁ iT.opensRange) := by
  have hV : IsAffineOpen iT.opensRange := isAffineOpen_opensRange iT
  have : IsAffine (iT.opensRange : S.Opens).toScheme := hV
  have : QuasiSeparatedSpace (f ⁻¹ᵁ iT.opensRange).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ iT.opensRange)
  have : CompactSpace (f ⁻¹ᵁ iT.opensRange).toScheme :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ (f ∣_ iT.opensRange) inferInstance
      inferInstance
  have hW := Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (X := (f ⁻¹ᵁ iT.opensRange).toScheme)
    (P := fun U₀ => repGood% f f' g' iT iT' gT K K' φ ((f ⁻¹ᵁ iT.opensRange).ι ''ᵁ U₀))
    (fun U₀ hU₀ => hbase _ (hU₀.image_of_isOpenImmersion _)
      ((Scheme.Hom.image_le_opensRange _ U₀).trans_eq (Scheme.Opens.opensRange_ι _)))
    (fun U₀ V₀ _ _ hU hV hUV => repGood_image_sup _ U₀ V₀ hU hV hUV) ⊤
    (by simpa using isCompact_univ (X := (f ⁻¹ᵁ iT.opensRange).toScheme))
  rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at hW

end Stacks.Cohomology.BaseChangeCover
