module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.QuasicoherentPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Groupoids.Coinduction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.PushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuasicoherentFromBase
public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidQuasiCoherentComparison

/-!
# The cocycle condition for the coinduction descent morphism

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` flat and `s` quasi-compact and
quasi-separated, and let `𝒢` be a quasi-coherent module on `U`.  The module `s_* t^* 𝒢` carries
the canonical descent morphism `α` of `Stacks.Groupoids.GroupoidScheme.coinductionAlpha`.  This
file proves that `α` satisfies the cocycle condition and the normalization along the identity
section.

## Main results

* `Stacks.Groupoids.GroupoidScheme.cocycle_coinductionAlpha`: the descent morphism `α` of
  `s_* t^* 𝒢` satisfies the cocycle condition on the scheme of composable arrows.
* `Stacks.Groupoids.GroupoidScheme.identity_coinductionAlpha`: it is normalized along the
  identity section.
* `Stacks.Groupoids.GroupoidScheme.reindexHom_conj` records, for a descent morphism obtained by
  conjugating one along the base-change morphisms of two squares, how its reindexings are
  computed.  It refers to no groupoid and is stated for arbitrary schemes.

## Implementation notes

The cocycle condition is not verified by expanding the two base-change isomorphisms.  Instead the
comparison isomorphism `pr_0^* t^* 𝒢 ≅ c^* t^* 𝒢` is recognized as the transport of the trivial
descent morphism of `𝒢` along the base change `t`, whose cocycle law is
`Stacks.Modules.cocycle_transport`; the cocycle condition for `α` then follows by the reindexing
calculus of `reindexHom_conj` together with the invertibility of the base-change morphism of the
pasted rectangle.

## References

* [Stacks Project, Tag 07TR](https://stacks.math.columbia.edu/tag/07TR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology (pasteBase
  baseChangeNatTrans_pasteBase_app isIso_baseChangeNatTrans_of_flat)

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-! ### Generic lemmas -/

/-- **The generic reindexing lemma.**  Let `β` be a morphism `gT^* p_* N ⟶ gS^* p_* N` which is
the conjugate, by the base-change morphisms of the two squares `dT ≫ p = a ≫ gT` and
`dS ≫ p = a ≫ gS`, of a morphism `α : dT^* N ⟶ dS^* N`.  Then reindexing `β` along a morphism
`b` which lifts, over `q`, to a morphism `bV`, is — measured against the base-change morphisms
of the two pasted rectangles — the direct image along `q` of the reindexing of `α` along `bV`.

This is the groupoid-free form of
`Stacks.Groupoids.GroupoidScheme.reindexHom_pushforwardDescent`. -/
theorem reindexHom_conj {V W W' V' X Y : Scheme.{u}}
    {p : V ⟶ W} {a : V' ⟶ W'} {gT gS : W' ⟶ W} {dT dS : V' ⟶ V}
    (wT : dT ≫ p = a ≫ gT) (wS : dS ≫ p = a ≫ gS)
    {N : V.Modules}
    {α : (Scheme.Modules.pullback dT).obj N ⟶ (Scheme.Modules.pullback dS).obj N}
    {β : (Scheme.Modules.pullback gT).obj ((Scheme.Modules.pushforward p).obj N) ⟶
      (Scheme.Modules.pullback gS).obj ((Scheme.Modules.pushforward p).obj N)}
    (hβ : β ≫ (baseChangeNatTrans wS).app N =
      (baseChangeNatTrans wT).app N ≫ (Scheme.Modules.pushforward a).map α)
    (q : X ⟶ Y) (b : Y ⟶ W') (bV : X ⟶ V') (w : bV ≫ a = q ≫ b) :
    Stacks.Groupoids.reindexHom b β ≫ (baseChangeNatTrans (pasteBase wS w)).app N =
      (baseChangeNatTrans (pasteBase wT w)).app N ≫
        (Scheme.Modules.pushforward q).map (Stacks.Groupoids.reindexHom bV α) := by
  have hkey := congrArg (Scheme.Modules.pullback b).map hβ
  simp only [Functor.map_comp] at hkey
  have hnat := (baseChangeNatTrans w).naturality α
  simp only [Functor.comp_map] at hnat
  have hR : (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackComp bV dT).hom.app N) ≫
      (Scheme.Modules.pushforward q).map (Stacks.Groupoids.reindexHom bV α) =
      (Scheme.Modules.pushforward q).map ((Scheme.Modules.pullback bV).map α) ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackComp bV dS).hom.app N) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Stacks.Groupoids.reindexHom]
    simp
  have PT := baseChangeNatTrans_pasteBase_app wT w N
  have PS := baseChangeNatTrans_pasteBase_app wS w N
  rw [Stacks.Groupoids.reindexHom, PS, PT]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hR, reassoc_of% hkey, ← reassoc_of% hnat]

/-! ### The scheme of composable triples -/

namespace Triple

open Stacks.Groupoids

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The scheme of composable triples, as the scheme of composable arrows of the auxiliary
groupoid `(R, R ×_{s,t} R, c, pr₀)`. -/
noncomputable def obj : Over S :=
  Limits.pullback G.comp (Limits.pullback.fst G.source G.target)

/-- The first projection of the scheme of composable triples. -/
noncomputable def fst : obj G ⟶ Limits.pullback G.source G.target :=
  Limits.pullback.fst _ _

/-- The second projection of the scheme of composable triples. -/
noncomputable def snd : obj G ⟶ Limits.pullback G.source G.target :=
  Limits.pullback.snd _ _

/-- The composite of the first composable pair of a triple is the first arrow of the second. -/
theorem cond : fst G ≫ G.comp = snd G ≫ Limits.pullback.fst G.source G.target :=
  Limits.pullback.condition

/-- The second arrows of the two composable pairs of a triple are composable, so that `mid` is
defined. -/
theorem mid_w : (fst G ≫ Limits.pullback.snd G.source G.target) ≫ G.source =
    (snd G ≫ Limits.pullback.snd G.source G.target) ≫ G.target :=
  calc (fst G ≫ Limits.pullback.snd G.source G.target) ≫ G.source
      = fst G ≫ (Limits.pullback.snd G.source G.target ≫ G.source) := Category.assoc _ _ _
    _ = fst G ≫ (G.comp ≫ G.source) := by rw [G.source_comp]
    _ = (fst G ≫ G.comp) ≫ G.source := (Category.assoc _ _ _).symm
    _ = (snd G ≫ Limits.pullback.fst G.source G.target) ≫ G.source := by rw [cond]
    _ = snd G ≫ (Limits.pullback.fst G.source G.target ≫ G.source) := Category.assoc _ _ _
    _ = snd G ≫ (Limits.pullback.snd G.source G.target ≫ G.target) := by
        rw [Limits.pullback.condition]
    _ = (snd G ≫ Limits.pullback.snd G.source G.target) ≫ G.target := (Category.assoc _ _ _).symm

/-- The middle arrow of a composable triple, i.e. the composable pair formed by the second
members of the two composable pairs. -/
noncomputable def mid : obj G ⟶ Limits.pullback G.source G.target :=
  Limits.pullback.lift (fst G ≫ Limits.pullback.snd G.source G.target)
    (snd G ≫ Limits.pullback.snd G.source G.target) (mid_w G)

/-- The first component of the middle composable pair is the second arrow of the first pair. -/
theorem mid_fst : mid G ≫ Limits.pullback.fst G.source G.target =
    fst G ≫ Limits.pullback.snd G.source G.target :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of the middle composable pair is the second arrow of the second pair. -/
theorem mid_snd : mid G ≫ Limits.pullback.snd G.source G.target =
    snd G ≫ Limits.pullback.snd G.source G.target :=
  Limits.pullback.lift_snd _ _ _

/-- The first arrow of the first pair and the composite of the middle pair are composable, so
that `comp` is defined. -/
theorem comp_w : (fst G ≫ Limits.pullback.fst G.source G.target) ≫ G.source =
    (mid G ≫ G.comp) ≫ G.target :=
  calc (fst G ≫ Limits.pullback.fst G.source G.target) ≫ G.source
      = fst G ≫ (Limits.pullback.fst G.source G.target ≫ G.source) := Category.assoc _ _ _
    _ = fst G ≫ (Limits.pullback.snd G.source G.target ≫ G.target) := by
        rw [Limits.pullback.condition]
    _ = (fst G ≫ Limits.pullback.snd G.source G.target) ≫ G.target := (Category.assoc _ _ _).symm
    _ = (mid G ≫ Limits.pullback.fst G.source G.target) ≫ G.target := by rw [mid_fst]
    _ = mid G ≫ (Limits.pullback.fst G.source G.target ≫ G.target) := Category.assoc _ _ _
    _ = mid G ≫ (G.comp ≫ G.target) := by rw [G.target_comp]
    _ = (mid G ≫ G.comp) ≫ G.target := (Category.assoc _ _ _).symm

/-- Composition in the auxiliary groupoid: the composable pair formed by the first member of the
first pair and the composite of the middle pair. -/
noncomputable def comp : obj G ⟶ Limits.pullback G.source G.target :=
  Limits.pullback.lift (fst G ≫ Limits.pullback.fst G.source G.target) (mid G ≫ G.comp)
    (comp_w G)

/-- The first component of `comp` is the first arrow of the first pair. -/
theorem comp_fst : comp G ≫ Limits.pullback.fst G.source G.target =
    fst G ≫ Limits.pullback.fst G.source G.target :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of `comp` is the composite of the middle pair. -/
theorem comp_snd : comp G ≫ Limits.pullback.snd G.source G.target = mid G ≫ G.comp :=
  Limits.pullback.lift_snd _ _ _

/-- **Associativity.**  The source of the composite in the auxiliary groupoid is the source of
the second factor. -/
theorem comp_comp : comp G ≫ G.comp = snd G ≫ G.comp := by
  have wfg : (fst G ≫ Limits.pullback.fst G.source G.target) ≫ G.source =
      (fst G ≫ Limits.pullback.snd G.source G.target) ≫ G.target := by
    rw [Category.assoc, Limits.pullback.condition, Category.assoc]
  have wgh : (fst G ≫ Limits.pullback.snd G.source G.target) ≫ G.source =
      (snd G ≫ Limits.pullback.snd G.source G.target) ≫ G.target := mid_w G
  have h1 : Limits.pullback.lift (fst G ≫ Limits.pullback.fst G.source G.target)
      (fst G ≫ Limits.pullback.snd G.source G.target) wfg = fst G := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst]
    · rw [Limits.pullback.lift_snd]
  have h2 : Limits.pullback.lift (fst G ≫ Limits.pullback.snd G.source G.target)
      (snd G ≫ Limits.pullback.snd G.source G.target) wgh = mid G := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst, mid_fst]
    · rw [Limits.pullback.lift_snd, mid_snd]
  have w₁ : (Limits.pullback.lift (fst G ≫ Limits.pullback.fst G.source G.target)
        (fst G ≫ Limits.pullback.snd G.source G.target) wfg ≫ G.comp) ≫ G.source =
      (snd G ≫ Limits.pullback.snd G.source G.target) ≫ G.target := by
    rw [h1, Category.assoc, G.source_comp, ← Category.assoc]
    exact wgh
  have w₂ : (fst G ≫ Limits.pullback.fst G.source G.target) ≫ G.source =
      (Limits.pullback.lift (fst G ≫ Limits.pullback.snd G.source G.target)
        (snd G ≫ Limits.pullback.snd G.source G.target) wgh ≫ G.comp) ≫ G.target := by
    rw [h2]
    exact comp_w G
  have key := G.assoc (obj G) (fst G ≫ Limits.pullback.fst G.source G.target)
    (fst G ≫ Limits.pullback.snd G.source G.target)
    (snd G ≫ Limits.pullback.snd G.source G.target) wfg wgh w₁ w₂
  have h3 : Limits.pullback.lift (Limits.pullback.lift
        (fst G ≫ Limits.pullback.fst G.source G.target)
        (fst G ≫ Limits.pullback.snd G.source G.target) wfg ≫ G.comp)
      (snd G ≫ Limits.pullback.snd G.source G.target) w₁ = snd G := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst, h1, cond]
    · rw [Limits.pullback.lift_snd]
  have h4 : Limits.pullback.lift (fst G ≫ Limits.pullback.fst G.source G.target)
      (Limits.pullback.lift (fst G ≫ Limits.pullback.snd G.source G.target)
        (snd G ≫ Limits.pullback.snd G.source G.target) wgh ≫ G.comp) w₂ = comp G := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst, comp_fst]
    · rw [Limits.pullback.lift_snd, comp_snd, h2]
  rw [h3, h4] at key
  exact key.symm

/-- A commutative square of morphisms in `Over S` gives one on the underlying schemes. -/
private theorem left_comp_eq_left_comp {S : Scheme.{u}} {A B C D : Over S} {f : A ⟶ B}
    {g : B ⟶ D} {f' : A ⟶ C} {g' : C ⟶ D} (h : f ≫ g = f' ≫ g') :
    f.left ≫ g.left = f'.left ≫ g'.left := by
  rw [← Over.comp_left, ← Over.comp_left, h]

/-- The scheme of composable triples is a fibre product on underlying schemes. -/
theorem isPullback_left :
    IsPullback (fst G).left (snd G).left G.comp.left
      (Limits.pullback.fst G.source G.target).left :=
  (IsPullback.of_hasPullback G.comp (Limits.pullback.fst G.source G.target)).map (Over.forget S)

/-- `cond` on underlying schemes. -/
theorem cond_left : (fst G).left ≫ G.comp.left =
    (snd G).left ≫ (Limits.pullback.fst G.source G.target).left :=
  left_comp_eq_left_comp (cond G)

/-- `mid_fst` on underlying schemes. -/
theorem mid_fst_left : (mid G).left ≫ (Limits.pullback.fst G.source G.target).left =
    (fst G).left ≫ (Limits.pullback.snd G.source G.target).left :=
  left_comp_eq_left_comp (mid_fst G)

/-- `mid_snd` on underlying schemes. -/
theorem mid_snd_left : (mid G).left ≫ (Limits.pullback.snd G.source G.target).left =
    (snd G).left ≫ (Limits.pullback.snd G.source G.target).left :=
  left_comp_eq_left_comp (mid_snd G)

/-- `comp_fst` on underlying schemes. -/
theorem comp_fst_left : (comp G).left ≫ (Limits.pullback.fst G.source G.target).left =
    (fst G).left ≫ (Limits.pullback.fst G.source G.target).left :=
  left_comp_eq_left_comp (comp_fst G)

/-- `comp_snd` on underlying schemes. -/
theorem comp_snd_left : (comp G).left ≫ (Limits.pullback.snd G.source G.target).left =
    (mid G).left ≫ G.comp.left :=
  left_comp_eq_left_comp (comp_snd G)

/-- `comp_comp` on underlying schemes. -/
theorem comp_comp_left : (comp G).left ≫ G.comp.left = (snd G).left ≫ G.comp.left :=
  left_comp_eq_left_comp (comp_comp G)

end Triple

/-! ### The cocycle law for the comparison isomorphism -/

section Comparison

open Stacks.Groupoids Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- **The cocycle law for the comparison isomorphism** `pr₀^* t^* 𝒢 ≅ c^* t^* 𝒢`, on any scheme
carrying three morphisms into the scheme of composable arrows which satisfy the three groupoid
identities of the auxiliary groupoid `(R, R ×_{s,t} R, c, pr₀)`.  This is
`Stacks.Modules.cocycle_of_trivialDescent` at the comparison isomorphism of
`Stacks.Groupoids.GroupoidScheme.coinductionComparison`. -/
theorem comparison_cocycle (𝒢 : G.objects.left.Modules) {T : Scheme.{u}}
    (p₀ p₁ cc : T ⟶ (Limits.pullback G.source G.target).left)
    (htc : cc ≫ (Limits.pullback.fst G.source G.target).left =
      p₀ ≫ (Limits.pullback.fst G.source G.target).left)
    (hcond : p₀ ≫ G.comp.left = p₁ ≫ (Limits.pullback.fst G.source G.target).left)
    (hsc : cc ≫ G.comp.left = p₁ ≫ G.comp.left) :
    (Scheme.Modules.pullbackCongr htc).hom.app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        reindexHom p₀ ((coinductionComparison G).app 𝒢).hom ≫
        (Scheme.Modules.pullbackCongr hcond).hom.app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        reindexHom p₁ ((coinductionComparison G).app 𝒢).hom ≫
        (Scheme.Modules.pullbackCongr hsc.symm).hom.app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) =
      reindexHom cc ((coinductionComparison G).app 𝒢).hom :=
  Stacks.Modules.cocycle_of_trivialDescent G 𝒢 p₀ p₁ cc htc hcond hsc
    ((coinductionComparison G).app 𝒢).hom
    (by simp only [coinductionComparison, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app])

/-- The defining property of `coinductionAlpha`: composed with the base-change morphism of the
source square it is the direct image of the comparison isomorphism transported through the
base-change morphism of the target square. -/
theorem coinductionAlpha_comp_sourceBaseChange
    [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent] :
    (coinductionAlpha G 𝒢).hom ≫
        (coinductionSourceBaseChange G).app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) =
      (coinductionTargetBaseChange G).app
          ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        (Scheme.Modules.pushforward (Limits.pullback.snd G.source G.target).left).map
          ((coinductionComparison G).app 𝒢).hom := by
  have := isQuasicoherent_pullbackTarget G 𝒢
  simp only [coinductionAlpha, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    coinductionTargetBaseChangeIso_hom]
  rw [← coinductionSourceBaseChangeIso_hom G ((Scheme.Modules.pullback G.target.left).obj 𝒢),
    Iso.inv_hom_id, Category.comp_id]

/-- **The cocycle condition for the coinduction descent isomorphism.**  On the scheme of
composable arrows, applying `α` to the two arrows in succession agrees with applying it to their
composite. -/
@[stacks 07TR "the cocycle condition for `α`, the first of the two conditions making \
`(s_* t^* 𝒢, α)` a quasi-coherent module on the groupoid scheme"]
theorem cocycle_coinductionAlpha
    [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent] :
    successiveDescent G (coinductionAlpha G 𝒢).hom =
      reindexHom G.comp.left (coinductionAlpha G 𝒢).hom := by
  have hqcN := isQuasicoherent_pullbackTarget G 𝒢
  have wT : (Limits.pullback.fst G.source G.target).left ≫ G.source.left =
      (Limits.pullback.snd G.source G.target).left ≫ G.target.left :=
    (isPullback_composableArrows G).w
  have wS : G.comp.left ≫ G.source.left =
      (Limits.pullback.snd G.source G.target).left ≫ G.source.left :=
    (isPullback_comp_snd_source G).w
  have hβ : (coinductionAlpha G 𝒢).hom ≫
        (baseChangeNatTrans wS).app ((Scheme.Modules.pullback G.target.left).obj 𝒢) =
      (baseChangeNatTrans wT).app ((Scheme.Modules.pullback G.target.left).obj 𝒢) ≫
        (Scheme.Modules.pushforward (Limits.pullback.snd G.source G.target).left).map
          ((coinductionComparison G).app 𝒢).hom :=
    coinductionAlpha_comp_sourceBaseChange G 𝒢
  have hq1 : (Triple.fst G).left ≫ (Limits.pullback.snd G.source G.target).left =
      (Triple.mid G).left ≫ (Limits.pullback.fst G.source G.target).left :=
    (Triple.mid_fst_left G).symm
  have hq2 : (Triple.snd G).left ≫ (Limits.pullback.snd G.source G.target).left =
      (Triple.mid G).left ≫ (Limits.pullback.snd G.source G.target).left :=
    (Triple.mid_snd_left G).symm
  have hqc : (Triple.comp G).left ≫ (Limits.pullback.snd G.source G.target).left =
      (Triple.mid G).left ≫ G.comp.left := Triple.comp_snd_left G
  -- the outer rectangle is cartesian, so its base-change morphism is invertible
  have hG2 : IsPullback (Limits.pullback.fst G.source G.target).left
      (Limits.pullback.snd G.source G.target).left G.source.left G.target.left :=
    isPullback_composableArrows G
  have hsq : IsPullback (Limits.pullback.snd G.source G.target).left G.comp.left
      G.source.left G.source.left := (isPullback_comp_snd_source G).flip
  have houter : IsPullback ((Triple.mid G).left ≫ (Limits.pullback.fst G.source G.target).left)
      (Triple.snd G).left G.source.left
      ((Limits.pullback.snd G.source G.target).left ≫ G.target.left) := by
    have hp := (Triple.isPullback_left G).paste_horiz hsq
    rw [hq1, wT] at hp
    exact hp
  have hq2pb : IsPullback (Triple.mid G).left (Triple.snd G).left
      (Limits.pullback.snd G.source G.target).left
      (Limits.pullback.snd G.source G.target).left :=
    IsPullback.of_right houter hq2.symm hG2
  have hpbf : IsPullback ((Triple.comp G).left ≫ G.comp.left) (Triple.mid G).left
      G.source.left (G.comp.left ≫ G.source.left) := by
    rw [Triple.comp_comp_left G, wS]
    exact hq2pb.flip.paste_horiz hsq.flip
  have hflat2 : Flat (Limits.pullback.snd G.source G.target).left :=
    MorphismProperty.of_isPullback (P := @Flat) hG2 ‹Flat G.source.left›
  have hflat : Flat (G.comp.left ≫ G.source.left) := by rw [wS]; infer_instance
  have hiso : IsIso ((baseChangeNatTrans (pasteBase wS hqc)).app
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)) :=
    isIso_baseChangeNatTrans_of_flat hpbf _
  haveI hmono : Mono ((baseChangeNatTrans (pasteBase wS hqc)).app
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)) := IsIso.mono_of_iso _
  -- the six steps
  have stepF := reindexHom_conj wT wS hβ (Triple.mid G).left G.comp.left (Triple.comp G).left hqc
  have stepB := reindexHom_conj wT wS hβ (Triple.mid G).left
    (Limits.pullback.snd G.source G.target).left (Triple.snd G).left hq2
  have stepD := reindexHom_conj wT wS hβ (Triple.mid G).left
    (Limits.pullback.fst G.source G.target).left (Triple.fst G).left hq1
  have stepA := pullbackCongr_comp_baseChangeNatTrans wS.symm (Triple.comp_comp_left G).symm
    (pasteBase wS hq2) (pasteBase wS hqc) ((Scheme.Modules.pullback G.target.left).obj 𝒢)
  have stepC := pullbackCongr_comp_baseChangeNatTrans wT (Triple.cond_left G)
    (pasteBase wS hq1) (pasteBase wT hq2) ((Scheme.Modules.pullback G.target.left).obj 𝒢)
  have stepE := pullbackCongr_comp_baseChangeNatTrans (comp_left_comp_target_left G)
    (Triple.comp_fst_left G) (pasteBase wT hqc) (pasteBase wT hq1)
    ((Scheme.Modules.pullback G.target.left).obj 𝒢)
  have hcoc := congrArg (Scheme.Modules.pushforward (Triple.mid G).left).map
    (comparison_cocycle G 𝒢 (Triple.fst G).left (Triple.snd G).left (Triple.comp G).left
      (Triple.comp_fst_left G) (Triple.cond_left G) (Triple.comp_comp_left G))
  simp only [Functor.map_comp] at hcoc
  rw [← cancel_mono ((baseChangeNatTrans (pasteBase wS hqc)).app
    ((Scheme.Modules.pullback G.target.left).obj 𝒢))]
  unfold successiveDescent
  simp only [Category.assoc]
  rw [stepF, stepA, reassoc_of% stepB, reassoc_of% stepC, reassoc_of% stepD,
    reassoc_of% stepE, hcoc]

/-- **The normalization of the coinduction descent isomorphism along the identity section.**
Pulling `α` back along the identity section gives the identity of `s_* t^* 𝒢`.  With
`cocycle_coinductionAlpha` this exhibits `(s_* t^* 𝒢, α)` as a quasi-coherent module on the
groupoid scheme. -/
@[stacks 07TR "the normalization of `α` along the identity section, the second of the two \
conditions making `(s_* t^* 𝒢, α)` a quasi-coherent module on the groupoid scheme"]
theorem identity_coinductionAlpha
    [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (𝒢 : G.objects.left.Modules) [𝒢.IsQuasicoherent] :
    identityDescent G (coinductionAlpha G 𝒢).hom =
      𝟙 ((Scheme.Modules.pushforward G.source.left).obj
        ((Scheme.Modules.pullback G.target.left).obj 𝒢)) :=
  identityDescent_eq_id_of_cocycle G _ (cocycle_coinductionAlpha G 𝒢)

end Comparison

end Stacks.Groupoids.GroupoidScheme

end
