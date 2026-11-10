module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareLowerDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareProperCompletion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionBaseChangeTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ClosedPointIsoDetection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverField

/-!
# The induction on `dim(X) + dim(Y)` of [Stacks, Tag 0F1H]

Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K`, `Y` a scheme
of finite type over `K`, and `𝓕` an abelian sheaf on `U_étale` whose stalks are torsion of orders
invertible in `K`. [Stacks, Tag 0F1H] says that the base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` of
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
is an isomorphism. This file assembles the source's proof:

* `𝓕 = colim 𝓕[n]` reduces to `𝓕` annihilated by one `n` invertible in `K`
  (`OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_forall_annihilated`);
* induction on `dim(X) + dim(Y)`: by the induction hypothesis the stalks at the points over
  non-closed points are isomorphisms
  (`OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_of_lt`);
* the question is local, so `X` and `Y` may be taken affine
  (`OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_affineOpens`), and then `Y` is
  replaced by a projective completion of the same dimension
  (`OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_isProper_completion`);
* for `Y` proper, after base change to `K^{sep}`
  (`OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_extension`), the cone of the base
  change map is supported at closed points, so by [Stacks, Tag 0F1G] it suffices that the map
  induces isomorphisms on hypercohomology
  (`Stacks.EtaleCohomology.isIso_iff_forall_isIso_hypercohomology_of_closedPointSupport`).

The last input, that for `Y` proper over a separably closed field the base change map induces
isomorphisms `H^i(Y ×_K X, q⁻¹Rj_*𝓕) ⟶ H^i(Y ×_K X, Rh_*p⁻¹𝓕)`, is the Künneth computation of
the source with [Stacks, Tag 0F14]. It is not proved here: it is the proposition
`OpenImmersionProductSquare.HypercohomologyIsoOfProperFactor`, an explicit argument of every
result of this file, and **nothing here is registered**.

## Main definitions

* `OpenImmersionProductSquare.HypercohomologyIsoOfProperFactor` — the Künneth input.

## Main results

* `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_isProper` — the case of a proper `Y`
  whose base change map is invertible at the points over non-closed points.
* `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_zsmul_eq_zero` — the induction.
* `OpenImmersionProductSquare.isIso_baseChangeMap_of_hypercohomologyIsoOfProperFactor` — the
  statement of [Stacks, Tag 0F1H], given the Künneth input.

## Implementation notes

`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BaseChangeCondition.lean:220`)
and `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedEtale.lean:196`) are formed for the
standard model of the derived categories, which fixes the model here.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F1G](https://stacks.math.columbia.edu/tag/0F1G)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

-- `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/`
-- `BaseChangeCondition.lean:220`)
-- and `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedEtale.lean:196`) are formed for the
-- standard model of the derived categories.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The Künneth input of [Stacks, Tag 0F1H]**: for every separably closed field `K`, every open
immersion `j : U ⟶ X` of schemes of finite type over `K`, every scheme `Y` proper over `K`, every
integer `n` invertible in `K` and every abelian sheaf `𝓕` on `U_étale` annihilated by `n`, the
base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` induces isomorphisms on all hypercohomology groups
`H^i(Y ×_K X, -)`.

In the source this is the last paragraph of the proof: by [Stacks, Tag 0F14] both sides are
`RΓ(U, 𝓕) ⊗^L_{ℤ/n} RΓ(Y, ℤ/n)`. It is stated here as a proposition, the explicit argument of
the results of this file. -/
def HypercohomologyIsoOfProperFactor : Prop :=
  ∀ (K : Type u) [Field K] [IsSepClosed K] (X U Y : Scheme.{u}) (sX : X ⟶ Spec (.of K))
    (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sU]
    [QuasiCompact sU] [IsProper sY] (n : ℤ), IsUnit (n : K) →
    ∀ (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}),
      (∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) →
      ∀ i : ℤ, IsIso ((DerivedCategory.homologyFunctor Ab.{u + 1} i).map
        ((smallEtaleDerivedGlobalSections (pullback sY sX)).map
          (DerivedCategory.Plus.ι.map (baseChangeMap sX sU sY j hj 𝓕))))

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [QuasiCompact sX]
  [LocallyOfFiniteType sU] [QuasiCompact sU]

/-! ### A proper `Y` -/

/-- **The case of a proper `Y` over a separably closed field** (the last paragraph of the proof
of [Stacks, Tag 0F1H]). Let `K` be separably closed, `Y` proper over `K` and `𝓕` annihilated by
an integer `n` invertible in `K`. If the stalks of every `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` are
invertible at the geometric points over non-closed points of `Y ×_K X`, then every base change
map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible: the cohomology sheaves of the base change map
`q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` are the base change maps on higher direct images, so by
[Stacks, Tag 0F1G] it is an isomorphism once it is one on hypercohomology, which is the Künneth
input. -/
theorem isIso_higherBaseChangeMapAb_of_isProper_of_isSepClosed
    (hK : HypercohomologyIsoOfProperFactor.{u}) [IsSepClosed K] [IsProper sY] {n : ℤ}
    (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0)
    (hnc : ∀ (i : ℕ) (z : GeometricPoint (pullback sY sX)),
      ¬ IsClosed ({z.hom default} : Set _) →
        IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
          (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (i : ℕ) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  let M := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology U) Ab.{u + 1}) 0).obj 𝓕
  have hφ : IsIso (DerivedCategory.Plus.ι.map (baseChangeMap sX sU sY j hj 𝓕)) := by
    refine (isIso_iff_forall_isIso_hypercohomology_of_closedPointSupport K
      (pullback.snd sY sX ≫ sX) _ fun z m hz => ?_).2 (hK K X U Y sX sU sY j hj n hn 𝓕 h𝓕)
    change IsIso ((smallEtaleStalkAb z.hom).map
      ((DerivedCategory.Plus.homologyFunctor _ m).map (baseChangeMap sX sU sY j hj 𝓕)))
    rcases le_or_gt 0 m with hm | hm
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      have e := baseChangeSourceIso_hom_app_comp (q sX sY) j (h sX sU sY j hj) (p sU sY)
        (h_comp_q sX sU sY j hj) k 𝓕
      have e' : (DerivedCategory.Plus.homologyFunctor _ (k : ℤ)).map
          (baseChangeMap sX sU sY j hj 𝓕) =
          ((baseChangeSourceIso (q sX sY) j k).app 𝓕).inv ≫
            (higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
              (h_comp_q sX sU sY j hj) k).app 𝓕 ≫
            ((baseChangeTargetIso (h sX sU sY j hj) (p sU sY) k).app 𝓕).hom := by
        rw [Iso.eq_inv_comp]
        exact e
      rw [e', Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
      exact hnc k z hz
    · have : ((smallEtalePushforwardAb j).rightDerivedFunctorPlus.obj M).IsGE 0 :=
        Functor.isGE_rightDerivedFunctorPlus_obj _ M 0
      have : ((smallEtalePullbackAb (q sX sY)).rightDerivedFunctorPlus.obj
          ((smallEtalePushforwardAb j).rightDerivedFunctorPlus.obj M)).IsGE 0 :=
        Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
      have : ((smallEtalePullbackAb (p sU sY)).rightDerivedFunctorPlus.obj M).IsGE 0 :=
        Functor.isGE_rightDerivedFunctorPlus_obj _ M 0
      have : ((smallEtalePushforwardAb (h sX sU sY j hj)).rightDerivedFunctorPlus.obj
          ((smallEtalePullbackAb (p sU sY)).rightDerivedFunctorPlus.obj M)).IsGE 0 :=
        Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
      have z₁ := DerivedCategory.Plus.isZero_homology_of_isGE
        ((smallEtalePullbackAb (q sX sY)).rightDerivedFunctorPlus.obj
          ((smallEtalePushforwardAb j).rightDerivedFunctorPlus.obj M)) 0 m hm
      have z₂ := DerivedCategory.Plus.isZero_homology_of_isGE
        ((smallEtalePushforwardAb (h sX sU sY j hj)).rightDerivedFunctorPlus.obj
          ((smallEtalePullbackAb (p sU sY)).rightDerivedFunctorPlus.obj M)) 0 m hm
      have : IsIso ((DerivedCategory.Plus.homologyFunctor _ m).map
          (baseChangeMap sX sU sY j hj 𝓕)) :=
        ⟨⟨0, z₁.eq_of_src _ _, z₂.eq_of_src _ _⟩⟩
      infer_instance
  have : IsIso (baseChangeMap sX sU sY j hj 𝓕) :=
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  exact (BaseChangeOverField.isIso_smallEtaleDerivedBaseChangeAb_app_single_iff _ _ _ _ _ 𝓕).1
    this i

/-- **The case of a proper `Y`** ([Stacks, Tag 0F1H]): *"Consider a diagram as in the statement
of the lemma such that `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` is an isomorphism at all non-closed points of
`X ×_K Y` and such that `Y` is projective. [...] Thus we may and do assume `K` is separably
algebraically closed."* Let `Y` be proper over `K` and `𝓕` annihilated by an integer `n`
invertible in `K`. If the stalks of every `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` are invertible at the
geometric points over non-closed points, then every base change map is invertible: after base
change to `K^{sep}`, which preserves the hypothesis, this is
`isIso_higherBaseChangeMapAb_of_isProper_of_isSepClosed`. -/
theorem isIso_higherBaseChangeMapAb_of_isProper
    (hK : HypercohomologyIsoOfProperFactor.{u}) [IsProper sY] {n : ℤ}
    (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0)
    (hnc : ∀ (i : ℕ) (z : GeometricPoint (pullback sY sX)),
      ¬ IsClosed ({z.hom default} : Set _) →
        IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
          (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (i : ℕ) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  have : QuasiCompact j := quasiCompact_of_finiteType sX sU j hj
  have : QuasiSeparated j := quasiSeparated_of_isOpenImmersion j
  have : IsOpenImmersion (extensionOpen K (SeparableClosure K) sX sU j hj) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (FieldExtensionBaseChange.isPullback_baseChangeMap _ sX sU j hj).flip inferInstance
  have hnL : IsUnit (n : SeparableClosure K) := by
    simpa using hn.map (algebraMap K (SeparableClosure K))
  refine isIso_higherBaseChangeMapAb_of_extension (L := SeparableClosure K) i n hn 𝓕 h𝓕 ?_
  exact isIso_higherBaseChangeMapAb_of_isProper_of_isSepClosed
    (pullback.fst (extensionMap K (SeparableClosure K)) sX)
    (pullback.fst (extensionMap K (SeparableClosure K)) sU)
    (pullback.fst (extensionMap K (SeparableClosure K)) sY)
    (extensionOpen K (SeparableClosure K) sX sU j hj)
    (extensionOpen_fst K (SeparableClosure K) sX sU j hj) hK hnL _
    (SmoothBaseChange.zsmul_pullbackAb_eq_zero _ 𝓕 n h𝓕)
    (fun i' w hw => isIso_stalk_higherBaseChangeMapAb_extension_of_not_isClosed i' n hn 𝓕 h𝓕
      (fun z hz => hnc i' z hz) w hw) i

/-! ### The induction -/

/-- **The induction step of [Stacks, Tag 0F1H].** Assume [Stacks, Tag 0F1H] below dimension `d`
and `dim(X) + dim(Y) ≤ d`, with `Y` of finite type over `K`. Then for `𝓕` annihilated by an
integer invertible in `K` the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible.

The question is local on `X` and on `Y`, so `X` and `Y` may be taken affine; an affine `Y` is
replaced by a projective completion `Y'` with `dim(Y') = dim(Y)`. At the points over non-closed
points the stalks are invertible by the induction hypothesis
(`isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_of_lt`), and then the base change map of
the square of `Y'` is invertible by `isIso_higherBaseChangeMapAb_of_isProper`. -/
theorem isIso_higherBaseChangeMapAb_of_baseChangeBelowDimension
    (hK : HypercohomologyIsoOfProperFactor.{u}) {d : WithBot ℕ∞}
    (IH : BaseChangeBelowDimension.{u} d) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hd : topologicalKrullDim X + topologicalKrullDim Y ≤ d) {n : ℤ} (hn : IsUnit (n : K))
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) (i : ℕ) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  have : QuasiCompact j := quasiCompact_of_finiteType sX sU j hj
  have : QuasiSeparated j := quasiSeparated_of_isOpenImmersion j
  refine isIso_higherBaseChangeMapAb_of_affineOpens sX sU sY j hj i 𝓕 fun ⟨V, hV⟩ ⟨W, hW⟩ => ?_
  have : IsAffine V := hV
  have : IsAffine W := hW
  have qc : ∀ {T : Scheme.{u}} [IsAffine T] (f : T ⟶ Spec (.of K)), QuasiCompact f := fun f =>
    @AlgebraicGeometry.instQuasiCompactOfIsAffineHom _ _ _ (isAffineHom_of_isAffine f)
  have hjV := comp_comp_eq sX sU j hj _ _ _ (isPullback_morphismRestrict j V)
  have : QuasiCompact (V.ι ≫ sX) := qc _
  have : QuasiCompact ((j ⁻¹ᵁ V).ι ≫ sU) :=
    hjV ▸ (inferInstance : QuasiCompact ((j ∣_ V) ≫ V.ι ≫ sX))
  have : LocallyOfFiniteType (W.ι ≫ sY) := inferInstance
  have : QuasiCompact (W.ι ≫ sY) := qc _
  have hdV : topologicalKrullDim V ≤ topologicalKrullDim X :=
    V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hdW : topologicalKrullDim W ≤ topologicalKrullDim Y :=
    W.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
  refine isIso_higherBaseChangeMapAb_of_isProper_completion (V.ι ≫ sX)
    ((j ⁻¹ᵁ V).ι ≫ sU) (W.ι ≫ sY) (j ∣_ V) hjV i _
    fun Y' sY' ι _ hprop _ _ hdimY' => ?_
  have := hprop
  have 𝓕V := SmoothBaseChange.zsmul_pullbackAb_eq_zero (j ⁻¹ᵁ V).ι 𝓕 n h𝓕
  refine isIso_higherBaseChangeMapAb_of_isProper (V.ι ≫ sX)
    ((j ⁻¹ᵁ V).ι ≫ sU) sY' (j ∣_ V) hjV hK hn _ 𝓕V (fun i' z hz => ?_) i
  refine isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_of_lt (V.ι ≫ sX)
    ((j ⁻¹ᵁ V).ι ≫ sU) sY' (j ∣_ V) hjV IH ?_ hn _ 𝓕V i' z hz
  rw [hdimY']
  exact (add_le_add hdV hdW).trans hd

/-- **[Stacks, Tag 0F1H] for sheaves annihilated by one integer**, given the Künneth input. For
every open immersion `j : U ⟶ X` of schemes of finite type over a field `K`, every scheme `Y` of
finite type over `K` and every abelian sheaf `𝓕` on `U_étale` annihilated by an integer `n`
invertible in `K`, the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible: induction on
`dim(X) + dim(Y)` in the well-founded order of `WithBot ℕ∞`, with
`isIso_higherBaseChangeMapAb_of_baseChangeBelowDimension` as the step. -/
theorem isIso_higherBaseChangeMapAb_of_zsmul_eq_zero (hK : HypercohomologyIsoOfProperFactor.{u})
    [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℤ} (hn : IsUnit (n : K))
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) (i : ℕ) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  suffices H : ∀ e : WithBot ℕ∞, ∀ (K : Type u) [Field K] (X U Y : Scheme.{u})
      (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) (j : U ⟶ X)
      [IsOpenImmersion j] (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [QuasiCompact sX]
      [LocallyOfFiniteType sU] [QuasiCompact sU] [LocallyOfFiniteType sY] [QuasiCompact sY],
      topologicalKrullDim X + topologicalKrullDim Y = e →
      ∀ (n : ℤ), IsUnit (n : K) → ∀ (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}),
        (∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) →
        ∀ i : ℕ, IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕) from
    H _ K X U Y sX sU sY j hj rfl n hn 𝓕 h𝓕 i
  intro e
  induction e using WellFoundedLT.induction with
  | _ e IHe =>
    intro K _ X U Y sX sU sY j _ hj _ _ _ _ _ _ he n hn 𝓕 h𝓕 i
    have IH : BaseChangeBelowDimension.{u} e :=
      fun K' _ X' U' Y' sX' sU' sY' j' _ hj' _ _ _ _ _ _ hlt n' hn' 𝓕' h𝓕' i' =>
        IHe _ hlt K' X' U' Y' sX' sU' sY' j' hj' rfl n' hn' 𝓕' h𝓕' i'
    exact isIso_higherBaseChangeMapAb_of_baseChangeBelowDimension sX sU sY j hj hK IH he.le hn 𝓕
      h𝓕 i

/-- **[Stacks, Tag 0F1H] on higher direct images**, given the Künneth input: for `𝓕` an abelian
sheaf on `U_étale` whose stalks are torsion of orders invertible in `K`, every base change map
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible. `𝓕` is the filtered colimit of its subsheaves
`𝓕[n]`, `n` invertible in `K` (`isIso_higherBaseChangeMapAb_of_forall_annihilated`). -/
theorem isIso_higherBaseChangeMapAb_of_hypercohomologyIsoOfProperFactor
    (hK : HypercohomologyIsoOfProperFactor.{u}) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (t : GeometricPoint U) (a : (smallEtaleStalkAb t.hom).obj 𝓕),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : K) ∧ n • a = 0) (i : ℕ) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  have : QuasiCompact j := quasiCompact_of_finiteType sX sU j hj
  have : QuasiSeparated j := quasiSeparated_of_isOpenImmersion j
  exact isIso_higherBaseChangeMapAb_of_forall_annihilated sX sU sY j hj i
    (fun n _ hu G hG => isIso_higherBaseChangeMapAb_of_zsmul_eq_zero sX sU sY j hj hK hu G hG i)
    𝓕 h𝓕

/-- **[Stacks, Tag 0F1H]**, given the Künneth input `HypercohomologyIsoOfProperFactor`. Let `K` be
a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K` and `Y` a scheme of
finite type over `K`. For every abelian sheaf `𝓕` on `U_étale` whose stalks are torsion of
orders invertible in `K`, the base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` of the square
`Y ×_K X ⟵ Y ×_K U` over `X ⟵ U` is an isomorphism (in `D⁺((Y ×_K X)_étale)`, `𝓕` placed in
degree zero): its cohomology sheaves are the base change maps on higher direct images. -/
theorem isIso_baseChangeMap_of_hypercohomologyIsoOfProperFactor
    (hK : HypercohomologyIsoOfProperFactor.{u}) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (t : GeometricPoint U) (a : (smallEtaleStalkAb t.hom).obj 𝓕),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : K) ∧ n • a = 0) :
    IsIso (baseChangeMap sX sU sY j hj 𝓕) :=
  (BaseChangeOverField.isIso_smallEtaleDerivedBaseChangeAb_app_single_iff _ _ _ _ _ 𝓕).2
    fun i => isIso_higherBaseChangeMapAb_of_hypercohomologyIsoOfProperFactor sX sU sY j hj hK 𝓕
      h𝓕 i

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end
