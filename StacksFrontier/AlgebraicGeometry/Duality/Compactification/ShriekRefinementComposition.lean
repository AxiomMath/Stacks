module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeStackingMate
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionUnits
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement

/-!
# The cocycle identity for the comparison of two compactifications

The comparison `α_g : f^!_j ≅ f^!_k` of `Stacks.Duality.refinementIso`, attached to an
interior-preserving morphism `g : j ⟶ k` of compactifications, is built from two pieces: the
comparison `ā_j ≅ ā_k ⋙ c̄_g` of [Stacks, Tag 0ATX], read through a transport along
`j.toBase = G ≫ k.toBase`; and the base change map of [Stacks, Tag 0AA6] for the cartesian square
of `g`. This file proves the cocycle identity

  `α_{g ≫ h} = α_g ≫ α_h`.

## Main results

All in the namespace `Stacks.Duality`.

* `refinementIso_comp` — **the cocycle identity**.
* `alphaComp_app` and `alphaIso_comp` — **the formal half**: for comparisons built as
  `α = (Rj ⋆ E) ≫ (A ⋆ b) ≫ (A ⋆ Rk ⋆ u)` out of a comparison `E` of the twisted inverse images,
  a base change map `b` and the identification `u` of `(𝟙)^×` with the identity functor, the
  cocycle identity for `α` follows from the cocycle identity for `E`, the cocycle identity for
  `b`, and the naturality of `u`. The comparisons are read through a functor `W` into their
  common source, here the inclusion of `D⁺_QCoh(𝒪_Y)`, and the base change maps are required to
  be invertible only after restriction along it.
* `twistedInverseImageCompIso_cocycle_app` — the cocycle condition of [Stacks, Tag 0ATY] for the
  comparison of [Stacks, Tag 0ATX], read on an object and solved for the comparison of the triple
  composite.
* `twistedInverseImageCongr_compIso` — transporting the second factor of the comparison of
  [Stacks, Tag 0ATX] along an equality of morphisms commutes with the comparison.
* `twistedInverseImageCongrCompIso_comp_app` and `twistedInverseImageCongrCompIso_comp` — the two
  previous results combined: the cocycle identity for the comparison of [Stacks, Tag 0ATX] read
  through the transports, on an object and as an identity of isomorphisms.
* `twistedInverseImageBaseChangeMap_comp` — **[Stacks, Tag 0ATQ] for a vertical stack of two
  cartesian squares whose left edges are the identity**.
* `refinementTwistedComp` — the comparison `c̄_{g ≫ h} ≅ c̄_h ⋙ c̄_g` of [Stacks, Tag 0ATX] for
  two composable morphisms of compactifications.
* `refinementTwistedCompIso_comp` and `refinementBaseChange_comp` — the cocycle identity of
  [Stacks, Tag 0ATY] and the one of [Stacks, Tag 0ATQ], at the compactifications of a morphism of
  `AlgebraicGeometry.FTS S`.
* `isQuasicoherentPush_*` and `isLeftAdjointPush_*` — the argument of [Stacks, Tag 08D5] part (1)
  and the adjointness instance of [Stacks, Tag 0A9E] for each morphism of the diagram.

## Implementation notes

The assumptions are those of `Stacks.Duality.refinementIso`: the invertibility of the
transformation `ξ` of [Stacks, Tag 0A9K] and of the base change map **on the bounded-below part**,
`Stacks.Duality.refinementBaseChangePlus`, which is [Stacks, Tag 0A9P], for each of the three
squares, as instance arguments.

The identities whose content is formal are proved with the categories as variables:
`alphaComp_app`, `alphaIso_comp`, and, with the schemes as variables,
`twistedInverseImageCongrCompIso_comp` and `twistedInverseImageBaseChangeMap_comp`. Each
conversion between a `refinement*` constant and the `twistedInverseImage*` term it unfolds to is a
separate `rfl` lemma between isomorphisms: `refinementTwistedCompIso_eq`,
`refinementTwistedCompIso_comp_eq` and `refinementTwistedComp_eq`. The geometric cocycle
identities are then assembled by rewriting, and `refinementIso_comp` is an identity of
isomorphisms.

## References

* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆ u

namespace Stacks.Duality

/-! ### The formal half -/

/-- The formal half of the cocycle identity for the comparison `α`. -/
theorem alphaComp_app
    {Yc : Type u₁} {Jc : Type u₂} {Kc : Type u₃} {Lc : Type u₄} {Xc : Type u₅}
    [Category.{v₁} Yc] [Category.{v₂} Jc] [Category.{v₃} Kc] [Category.{v₄} Lc]
    [Category.{v₅} Xc]
    {Aj : Yc ⥤ Jc} {Ak : Yc ⥤ Kc} {Al : Yc ⥤ Lc}
    {Cg : Kc ⥤ Jc} {Ch : Lc ⥤ Kc} {Cgh : Lc ⥤ Jc}
    {Rj : Jc ⥤ Xc} {Rk : Kc ⥤ Xc} {Rl : Lc ⥤ Xc}
    (Eg : Aj ⟶ Ak ⋙ Cg) (Eh : Ak ⟶ Al ⋙ Ch) (Egh : Aj ⟶ Al ⋙ Cgh)
    (Phi : Cgh ≅ Ch ⋙ Cg)
    (bg : Cg ⋙ Rj ⟶ Rk) (bh : Ch ⋙ Rk ⟶ Rl) (bgh : Cgh ⋙ Rj ⟶ Rl)
    (hE : ∀ K, Egh.app K = Eg.app K ≫ Cg.map (Eh.app K) ≫ Phi.inv.app (Al.obj K))
    (hb : ∀ Z, bgh.app Z = Rj.map (Phi.hom.app Z) ≫ bg.app (Ch.obj Z) ≫ bh.app Z)
    (K : Yc) :
    Rj.map (Egh.app K) ≫ bgh.app (Al.obj K) =
      (Rj.map (Eg.app K) ≫ bg.app (Ak.obj K)) ≫
        (Rk.map (Eh.app K) ≫ bh.app (Al.obj K)) := by
  rw [hE, hb]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Category.assoc (Rj.map (Phi.inv.app (Al.obj K))) (Rj.map (Phi.hom.app (Al.obj K))),
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have hnat := bg.naturality (Eh.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [← Category.assoc (Rj.map (Cg.map (Eh.app K))), hnat]
  simp only [Category.assoc]

/-- **The cocycle identity for the comparison `α` as an identity of isomorphisms.**  For
comparisons built, as `Stacks.Duality.refinementIso` is, by whiskering a comparison `E` of the
twisted inverse images with a base change map `b` and the identification `u` of `(𝟙)^×` with the
identity functor, the cocycle identity follows from the cocycle identity for `E`, the cocycle
identity for `b`, and the naturality of `u`.

The comparisons are read through a functor `W` into their common source (for
`Stacks.Duality.refinementIso`, the inclusion of `D⁺_QCoh(𝒪_Y)`): the cocycle identities `hE` and
`hb` are identities of transformations on the whole source, and the base change maps are invertible
after restriction along `W`. -/
theorem alphaIso_comp
    {Yc' : Type u₆} {Yc : Type u₁} {Jc : Type u₂} {Kc : Type u₃} {Lc : Type u₄} {Xc : Type u₅}
    [Category.{v₆} Yc'] [Category.{v₁} Yc] [Category.{v₂} Jc] [Category.{v₃} Kc]
    [Category.{v₄} Lc] [Category.{v₅} Xc]
    {Aj : Yc ⥤ Jc} {Ak : Yc ⥤ Kc} {Al : Yc ⥤ Lc}
    {Cg : Kc ⥤ Jc} {Ch : Lc ⥤ Kc} {Cgh : Lc ⥤ Jc}
    {Rj : Jc ⥤ Xc} {Rk : Kc ⥤ Xc} {Rl : Lc ⥤ Xc} {I : Xc ⥤ Xc} (W : Yc' ⥤ Yc) (u : I ≅ 𝟭 Xc)
    (Eg : Aj ≅ Ak ⋙ Cg) (Eh : Ak ≅ Al ⋙ Ch) (Egh : Aj ≅ Al ⋙ Cgh) (Phi : Cgh ≅ Ch ⋙ Cg)
    (bg : Cg ⋙ Rj ⟶ Rk ⋙ I) (bh : Ch ⋙ Rk ⟶ Rl ⋙ I) (bgh : Cgh ⋙ Rj ⟶ Rl ⋙ I)
    [IsIso (Functor.whiskerLeft (W ⋙ Ak) bg)] [IsIso (Functor.whiskerLeft (W ⋙ Al) bh)]
    [IsIso (Functor.whiskerLeft (W ⋙ Al) bgh)]
    (hE : Egh = Eg ≪≫ isoWhiskerRight Eh Cg ≪≫ associator Al Ch Cg ≪≫
      isoWhiskerLeft Al Phi.symm)
    (hb : bgh = Functor.whiskerRight Phi.hom Rj ≫ (associator Ch Cg Rj).hom ≫
      Functor.whiskerLeft Ch bg ≫ (associator Ch Rk I).inv ≫ Functor.whiskerRight bh I ≫
        (associator Rl I I).hom ≫
          Functor.whiskerLeft Rl (Functor.whiskerLeft I u.hom ≫ (rightUnitor I).hom)) :
    isoWhiskerRight (isoWhiskerLeft W Egh) Rj ≪≫ associator (W ⋙ Al) Cgh Rj ≪≫
          asIso (Functor.whiskerLeft (W ⋙ Al) bgh) ≪≫
        isoWhiskerLeft (W ⋙ Al) (isoWhiskerLeft Rl u ≪≫ rightUnitor Rl) =
      (isoWhiskerRight (isoWhiskerLeft W Eg) Rj ≪≫ associator (W ⋙ Ak) Cg Rj ≪≫
            asIso (Functor.whiskerLeft (W ⋙ Ak) bg) ≪≫
          isoWhiskerLeft (W ⋙ Ak) (isoWhiskerLeft Rk u ≪≫ rightUnitor Rk)) ≪≫
        (isoWhiskerRight (isoWhiskerLeft W Eh) Rk ≪≫ associator (W ⋙ Al) Ch Rk ≪≫
            asIso (Functor.whiskerLeft (W ⋙ Al) bh) ≪≫
          isoWhiskerLeft (W ⋙ Al) (isoWhiskerLeft Rl u ≪≫ rightUnitor Rl)) := by
  have hE' : ∀ K, Egh.hom.app K =
      Eg.hom.app K ≫ Cg.map (Eh.hom.app K) ≫ Phi.inv.app (Al.obj K) := by
    intro K; rw [hE]; simp
  have hb' : ∀ Z, (bgh ≫ Functor.whiskerLeft Rl u.hom ≫ (rightUnitor Rl).hom).app Z =
      Rj.map (Phi.hom.app Z) ≫
        (bg ≫ Functor.whiskerLeft Rk u.hom ≫ (rightUnitor Rk).hom).app (Ch.obj Z) ≫
          (bh ≫ Functor.whiskerLeft Rl u.hom ≫ (rightUnitor Rl).hom).app Z := by
    intro Z
    rw [hb]
    simp
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  have key := alphaComp_app Eg.hom Eh.hom Egh.hom Phi
    (bg ≫ Functor.whiskerLeft Rk u.hom ≫ (rightUnitor Rk).hom)
    (bh ≫ Functor.whiskerLeft Rl u.hom ≫ (rightUnitor Rl).hom)
    (bgh ≫ Functor.whiskerLeft Rl u.hom ≫ (rightUnitor Rl).hom) hE' hb' (W.obj K)
  simpa using key

/-! ### The cocycle identity of Tag 0ATY, read on an object -/

section Cocycle

variable {V W Z T : Scheme.{u}} {G : V ⟶ W} {H : W ⟶ Z} {q : Z ⟶ T}
  (hG : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward G).obj K.obj)).IsQuasicoherent)
  (hH : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward H).obj K.obj)).IsQuasicoherent)
  (hq : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward q).obj K.obj)).IsQuasicoherent)
  (hGH : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (G ≫ H)).obj K.obj)).IsQuasicoherent)
  (hHq : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (H ≫ q)).obj K.obj)).IsQuasicoherent)
  (hTot : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (G ≫ H ≫ q)).obj K.obj)).IsQuasicoherent)
  [iG : (quasiCoherentDerivedPushforward G hG).IsLeftAdjoint]
  [iH : (quasiCoherentDerivedPushforward H hH).IsLeftAdjoint]
  [iq : (quasiCoherentDerivedPushforward q hq).IsLeftAdjoint]
  [iGH : (quasiCoherentDerivedPushforward (G ≫ H) hGH).IsLeftAdjoint]
  [iHq : (quasiCoherentDerivedPushforward (H ≫ q) hHq).IsLeftAdjoint]
  [iTot : (quasiCoherentDerivedPushforward (G ≫ H ≫ q) hTot).IsLeftAdjoint]

/-- The cocycle identity of [Stacks, Tag 0ATY], read on an object and with the comparison for
the triple composite moved to the other side. -/
theorem twistedInverseImageCompIso_cocycle_app (K : quasiCoherentDerivedCategory T) :
    (@twistedInverseImageCompIso V Z T (G ≫ H) q hGH hq hTot iGH iq iTot).hom.app K =
      (twistedInverseImageCompIso G (H ≫ q) hG hHq hTot).hom.app K ≫
        ((twistedInverseImage G hG).map
            ((twistedInverseImageCompIso H q hH hq hHq).hom.app K) ≫
          (twistedInverseImageCompIso G H hG hH hGH).inv.app
            ((twistedInverseImage q hq).obj K)) := by
  have h2 := NatTrans.congr_app
    (@twistedInverseImageCompIso_hom_assoc_whiskering V W Z T G H q hG hH hq hGH hHq hTot
      iG iH iq iGH iHq iTot) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at h2
  exact ((Iso.eq_comp_inv (Iso.app (twistedInverseImageCompIso G H hG hH hGH)
    ((twistedInverseImage q hq).obj K))).2 h2).trans (Category.assoc _ _ _)

end Cocycle

/-! ### Transport in the second factor -/

section Transport

variable {V W Z T : Scheme.{u}} {G : V ⟶ W} {H : W ⟶ Z} {c : Z ⟶ T} {p : V ⟶ T} {b : W ⟶ T}
  (hG : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward G).obj K.obj)).IsQuasicoherent)
  (hb : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward b).obj K.obj)).IsQuasicoherent)
  (hp : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward p).obj K.obj)).IsQuasicoherent)
  (hHc : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (H ≫ c)).obj K.obj)).IsQuasicoherent)
  (hGb : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (G ≫ b)).obj K.obj)).IsQuasicoherent)
  (hTot : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (G ≫ H ≫ c)).obj K.obj)).IsQuasicoherent)
  [iG : (quasiCoherentDerivedPushforward G hG).IsLeftAdjoint]
  [ib : (quasiCoherentDerivedPushforward b hb).IsLeftAdjoint]
  [ip : (quasiCoherentDerivedPushforward p hp).IsLeftAdjoint]
  [iHc : (quasiCoherentDerivedPushforward (H ≫ c) hHc).IsLeftAdjoint]
  [iGb : (quasiCoherentDerivedPushforward (G ≫ b) hGb).IsLeftAdjoint]
  [iTot : (quasiCoherentDerivedPushforward (G ≫ H ≫ c) hTot).IsLeftAdjoint]

/-- Transporting the second factor of the comparison of [Stacks, Tag 0ATX] along an equality of
morphisms commutes with the comparison. -/
theorem twistedInverseImageCongr_compIso (e₁ : G ≫ b = p) (e₂ : H ≫ c = b)
    (K : quasiCoherentDerivedCategory T) :
    (twistedInverseImageCongrIso hp hTot (by rw [← e₁, ← e₂])).hom.app K ≫
        (twistedInverseImageCompIso G (H ≫ c) hG hHc hTot).hom.app K =
      (twistedInverseImageCongrIso hp hGb e₁.symm).hom.app K ≫
        (twistedInverseImageCompIso G b hG hb hGb).hom.app K ≫
          (twistedInverseImage G hG).map
            ((twistedInverseImageCongrIso hb hHc e₂.symm).hom.app K) := by
  subst e₂ e₁
  simp only [twistedInverseImageCongrIso_self, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

end Transport

/-! ### The cocycle identity with the transports -/

section Combined

variable {V W Z T : Scheme.{u}} {G : V ⟶ W} {H : W ⟶ Z} {c : Z ⟶ T} {p : V ⟶ T} {b : W ⟶ T}
  (hG : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((derivedPushforward G).obj K.obj)).IsQuasicoherent)
  (hH : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward H).obj K.obj)).IsQuasicoherent)
  (hc : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward c).obj K.obj)).IsQuasicoherent)
  (hb : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward b).obj K.obj)).IsQuasicoherent)
  (hp : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward p).obj K.obj)).IsQuasicoherent)
  (hGH : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (G ≫ H)).obj K.obj)).IsQuasicoherent)
  (hHc : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (H ≫ c)).obj K.obj)).IsQuasicoherent)
  (hGb : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (G ≫ b)).obj K.obj)).IsQuasicoherent)
  (hTot : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor T.Modules i).obj
      ((derivedPushforward (G ≫ H ≫ c)).obj K.obj)).IsQuasicoherent)
  [iG : (quasiCoherentDerivedPushforward G hG).IsLeftAdjoint]
  [iH : (quasiCoherentDerivedPushforward H hH).IsLeftAdjoint]
  [ic : (quasiCoherentDerivedPushforward c hc).IsLeftAdjoint]
  [ib : (quasiCoherentDerivedPushforward b hb).IsLeftAdjoint]
  [ip : (quasiCoherentDerivedPushforward p hp).IsLeftAdjoint]
  [iGH : (quasiCoherentDerivedPushforward (G ≫ H) hGH).IsLeftAdjoint]
  [iHc : (quasiCoherentDerivedPushforward (H ≫ c) hHc).IsLeftAdjoint]
  [iGb : (quasiCoherentDerivedPushforward (G ≫ b) hGb).IsLeftAdjoint]
  [iTot : (quasiCoherentDerivedPushforward (G ≫ H ≫ c) hTot).IsLeftAdjoint]

/-- **The cocycle identity for the comparison `ā ≅ ā' ⋙ c̄` of [Stacks, Tag 0ATX] read through a
transport along an equality of morphisms**, read on an object. -/
theorem twistedInverseImageCongrCompIso_comp_app (e₁ : G ≫ b = p) (e₂ : H ≫ c = b)
    (K : quasiCoherentDerivedCategory T) :
    (twistedInverseImageCongrIso hp hTot (by rw [← e₁, ← e₂])).hom.app K ≫
        (@twistedInverseImageCompIso V Z T (G ≫ H) c hGH hc hTot iGH ic iTot).hom.app K =
      ((twistedInverseImageCongrIso hp hGb e₁.symm).hom.app K ≫
          (twistedInverseImageCompIso G b hG hb hGb).hom.app K) ≫
        ((twistedInverseImage G hG).map
            ((twistedInverseImageCongrIso hb hHc e₂.symm).hom.app K ≫
              (twistedInverseImageCompIso H c hH hc hHc).hom.app K) ≫
          (twistedInverseImageCompIso G H hG hH hGH).inv.app
            ((twistedInverseImage c hc).obj K)) := by
  rw [twistedInverseImageCompIso_cocycle_app hG hH hc hGH hHc hTot K, ← Category.assoc,
    twistedInverseImageCongr_compIso hG hb hp hHc hGb hTot e₁ e₂ K]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The cocycle identity for the comparison `ā ≅ ā' ⋙ c̄` of [Stacks, Tag 0ATX] read through
the transports, as an identity of isomorphisms.** -/
theorem twistedInverseImageCongrCompIso_comp (e₁ : G ≫ b = p) (e₂ : H ≫ c = b) :
    twistedInverseImageCongrIso hp hTot (by rw [← e₁, ← e₂]) ≪≫
        @twistedInverseImageCompIso V Z T (G ≫ H) c hGH hc hTot iGH ic iTot =
      (twistedInverseImageCongrIso hp hGb e₁.symm ≪≫
          twistedInverseImageCompIso G b hG hb hGb) ≪≫
        isoWhiskerRight (twistedInverseImageCongrIso hb hHc e₂.symm ≪≫
            twistedInverseImageCompIso H c hH hc hHc) (twistedInverseImage G hG) ≪≫
          associator (twistedInverseImage c hc) (twistedInverseImage H hH)
              (twistedInverseImage G hG) ≪≫
            isoWhiskerLeft (twistedInverseImage c hc)
              (twistedInverseImageCompIso G H hG hH hGH).symm := by
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.id_comp]
  exact twistedInverseImageCongrCompIso_comp_app hG hH hc hb hp hGH hHc hGb hTot e₁ e₂ K

end Combined

/-! ### The quasi-coherence and adjointness inputs

The argument of [Stacks, Tag 08D5] part (1) and the adjointness instance of [Stacks, Tag 0A9E] for
each morphism of the diagram of the compactifications of a morphism of `AlgebraicGeometry.FTS S`,
over a Noetherian base, from
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` and
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`. -/

section Inputs

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k l : CompactificationOf (Over.mk f.left)}

open CompactificationOf

/-- [Stacks, Tag 08D5] part (1) for the structure morphism of a compactification. -/
theorem isQuasicoherentPush_toBase (j : CompactificationOf (Over.mk f.left)) :
    ∀ (K : quasiCoherentDerivedCategory j.space) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((derivedPushforward j.toBase).obj K.obj)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase

/-- [Stacks, Tag 08D5] part (1) for the morphism of ambient schemes of a morphism of
compactifications. -/
theorem isQuasicoherentPush_homMap (g : j ⟶ k) :
    ∀ (K : quasiCoherentDerivedCategory j.space) (i : ℤ),
      ((DerivedCategory.homologyFunctor k.space.Modules i).obj
        ((derivedPushforward (Hom.map g)).obj K.obj)).IsQuasicoherent :=
  let := isProper_homMap g
  isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map g)

/-- [Stacks, Tag 08D5] part (1) for `G ≫ k.toBase`. -/
theorem isQuasicoherentPush_homMap_comp_toBase (g : j ⟶ k) :
    ∀ (K : quasiCoherentDerivedCategory j.space) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((derivedPushforward (Hom.map g ≫ k.toBase)).obj K.obj)).IsQuasicoherent :=
  let := isProper_homMap g
  isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map g ≫ k.toBase)

/-- [Stacks, Tag 08D5] part (1) for `G ≫ H`. -/
theorem isQuasicoherentPush_homMap_comp (g : j ⟶ k) (h : k ⟶ l) :
    ∀ (K : quasiCoherentDerivedCategory j.space) (i : ℤ),
      ((DerivedCategory.homologyFunctor l.space.Modules i).obj
        ((derivedPushforward (Hom.map g ≫ Hom.map h)).obj K.obj)).IsQuasicoherent :=
  let := isProper_homMap g
  let := isProper_homMap h
  isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map g ≫ Hom.map h)

/-- [Stacks, Tag 08D5] part (1) for `G ≫ H ≫ l.toBase`. -/
theorem isQuasicoherentPush_homMap_comp_comp_toBase (g : j ⟶ k) (h : k ⟶ l) :
    ∀ (K : quasiCoherentDerivedCategory j.space) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((derivedPushforward (Hom.map g ≫ Hom.map h ≫ l.toBase)).obj K.obj)).IsQuasicoherent :=
  let := isProper_homMap g
  let := isProper_homMap h
  isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map g ≫ Hom.map h ≫ l.toBase)

/-- [Stacks, Tag 0A9E] for the structure morphism of a compactification. -/
theorem isLeftAdjointPush_toBase (j : CompactificationOf (Over.mk f.left)) :
    (quasiCoherentDerivedPushforward j.toBase (isQuasicoherentPush_toBase f j)).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j.toBase

/-- [Stacks, Tag 0A9E] for the morphism of ambient schemes of a morphism of compactifications. -/
theorem isLeftAdjointPush_homMap (g : j ⟶ k) :
    (quasiCoherentDerivedPushforward (Hom.map g)
      (isQuasicoherentPush_homMap f g)).IsLeftAdjoint :=
  let := isProper_homMap g
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (Hom.map g)

/-- [Stacks, Tag 0A9E] for `G ≫ k.toBase`. -/
theorem isLeftAdjointPush_homMap_comp_toBase (g : j ⟶ k) :
    (quasiCoherentDerivedPushforward (Hom.map g ≫ k.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f g)).IsLeftAdjoint :=
  let := isProper_homMap g
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (Hom.map g ≫ k.toBase)

/-- [Stacks, Tag 0A9E] for `G ≫ H`. -/
theorem isLeftAdjointPush_homMap_comp (g : j ⟶ k) (h : k ⟶ l) :
    (quasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h)
      (isQuasicoherentPush_homMap_comp f g h)).IsLeftAdjoint :=
  let := isProper_homMap g
  let := isProper_homMap h
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h)

/-- [Stacks, Tag 0A9E] for `G ≫ H ≫ l.toBase`. -/
theorem isLeftAdjointPush_homMap_comp_comp_toBase (g : j ⟶ k) (h : k ⟶ l) :
    (quasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h ≫ l.toBase)
      (isQuasicoherentPush_homMap_comp_comp_toBase f g h)).IsLeftAdjoint :=
  let := isProper_homMap g
  let := isProper_homMap h
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h ≫ l.toBase)

end Inputs


/-! ### The base change maps of a vertical stack of two squares with identity left edges -/

section BaseChangeComp

variable {Xs Vj Vk Vl : Scheme.{u}} {ij : Xs ⟶ Vj} {ik : Xs ⟶ Vk} {il : Xs ⟶ Vl}
  {G : Vj ⟶ Vk} {H : Vk ⟶ Vl}
  (hij : ∀ (K : quasiCoherentDerivedCategory Xs) (i : ℤ),
    ((DerivedCategory.homologyFunctor Vj.Modules i).obj
      ((derivedPushforward ij).obj K.obj)).IsQuasicoherent)
  (hik : ∀ (K : quasiCoherentDerivedCategory Xs) (i : ℤ),
    ((DerivedCategory.homologyFunctor Vk.Modules i).obj
      ((derivedPushforward ik).obj K.obj)).IsQuasicoherent)
  (hil : ∀ (K : quasiCoherentDerivedCategory Xs) (i : ℤ),
    ((DerivedCategory.homologyFunctor Vl.Modules i).obj
      ((derivedPushforward il).obj K.obj)).IsQuasicoherent)
  (hG : ∀ (K : quasiCoherentDerivedCategory Vj) (i : ℤ),
    ((DerivedCategory.homologyFunctor Vk.Modules i).obj
      ((derivedPushforward G).obj K.obj)).IsQuasicoherent)
  (hH : ∀ (K : quasiCoherentDerivedCategory Vk) (i : ℤ),
    ((DerivedCategory.homologyFunctor Vl.Modules i).obj
      ((derivedPushforward H).obj K.obj)).IsQuasicoherent)
  (hGH : ∀ (K : quasiCoherentDerivedCategory Vj) (i : ℤ),
    ((DerivedCategory.homologyFunctor Vl.Modules i).obj
      ((derivedPushforward (G ≫ H)).obj K.obj)).IsQuasicoherent)
  (hid : ∀ (K : quasiCoherentDerivedCategory Xs) (i : ℤ),
    ((DerivedCategory.homologyFunctor Xs.Modules i).obj
      ((derivedPushforward (𝟙 Xs)).obj K.obj)).IsQuasicoherent)
  [iG : (quasiCoherentDerivedPushforward G hG).IsLeftAdjoint]
  [iH : (quasiCoherentDerivedPushforward H hH).IsLeftAdjoint]
  [iGH : (quasiCoherentDerivedPushforward (G ≫ H) hGH).IsLeftAdjoint]
  [iId : (quasiCoherentDerivedPushforward (𝟙 Xs) hid).IsLeftAdjoint]
  (sq₁ : IsPullback ij (𝟙 Xs) G ik) (sq₂ : IsPullback ik (𝟙 Xs) H il)
  (sqr : IsPullback ij (𝟙 Xs) (G ≫ H) il)
  [iXi₁ : IsIso (twistedInverseImagePushforwardBaseChange ij (𝟙 Xs) G ik hij hG hid hik sq₁)]
  [iXi₂ : IsIso (twistedInverseImagePushforwardBaseChange ik (𝟙 Xs) H il hik hH hid hil sq₂)]
  [iXir : IsIso (twistedInverseImagePushforwardBaseChange ij (𝟙 Xs) (G ≫ H) il hij hGH hid hil
    sqr)]

/-- **[Stacks, Tag 0ATQ] for a vertical stack of two cartesian squares whose left edges are the
identity of `Xs`**: the base change maps of [Stacks, Tag 0AA6] for the two squares compose to the
base change map of the rectangle, through the comparison
`Stacks.Duality.twistedInverseImageCompIso` of [Stacks, Tag 0ATX] on the right vertical and,
on the left vertical, the left unit law of [Stacks, Tag 0ATY]: the identity of `Xs` composed with
itself is the identity, and `(𝟙)^×` is identified with the identity functor by
`Stacks.Duality.twistedInverseImageIdIso`. -/
theorem twistedInverseImageBaseChangeMap_comp :
    twistedInverseImageBaseChangeMap ij (𝟙 Xs) (G ≫ H) il hij hGH hid hil sqr =
      Functor.whiskerRight (twistedInverseImageCompIso G H hG hH hGH).hom
          (quasiCoherentDerivedPullback' ij) ≫
        (associator (twistedInverseImage H hH) (twistedInverseImage G hG)
            (quasiCoherentDerivedPullback' ij)).hom ≫
          Functor.whiskerLeft (twistedInverseImage H hH)
              (twistedInverseImageBaseChangeMap ij (𝟙 Xs) G ik hij hG hid hik sq₁) ≫
            (associator (twistedInverseImage H hH) (quasiCoherentDerivedPullback' ik)
                (twistedInverseImage (𝟙 Xs) hid)).inv ≫
              Functor.whiskerRight
                  (twistedInverseImageBaseChangeMap ik (𝟙 Xs) H il hik hH hid hil sq₂)
                  (twistedInverseImage (𝟙 Xs) hid) ≫
                (associator (quasiCoherentDerivedPullback' il)
                    (twistedInverseImage (𝟙 Xs) hid) (twistedInverseImage (𝟙 Xs) hid)).hom ≫
                  Functor.whiskerLeft (quasiCoherentDerivedPullback' il)
                    (Functor.whiskerLeft (twistedInverseImage (𝟙 Xs) hid)
                        (twistedInverseImageIdIso Xs hid).hom ≫
                      (rightUnitor (twistedInverseImage (𝟙 Xs) hid)).hom) := by
  let : (quasiCoherentDerivedPushforward (𝟙 Xs ≫ 𝟙 Xs) hid).IsLeftAdjoint := iId
  have hv := twistedInverseImageBaseChangeMap_vcomp ij (𝟙 Xs) G ik (𝟙 Xs) H il hij hG hid hik
    hH hid hil hGH hid sq₁ sq₂
  refine hv.trans ?_
  rw [twistedInverseImageCompIso_id_comp_eq_rightUnitor_symm (𝟙 Xs) hid hid]
  refine NatTrans.ext (funext fun Z => ?_)
  refine (Stacks.CategoryTheory.whiskerBottom_whiskerTop_hComp_app _ _ _ _ Z).trans ?_
  simp only [TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Iso.trans_hom, Iso.symm_inv, Category.id_comp]
  rfl

end BaseChangeComp

/-! ### The cocycle identity for the comparisons of three compactifications -/

section Refinement

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k l : CompactificationOf (Over.mk f.left)} (g : j ⟶ k) (h : k ⟶ l)

/-- **The comparison `c̄_{g ≫ h} ≅ c̄_h ⋙ c̄_g` of [Stacks, Tag 0ATX]** for two composable
morphisms of compactifications. -/
def refinementTwistedComp :
    refinementTwisted f (g ≫ h) ≅ refinementTwisted f h ⋙ refinementTwisted f g :=
  letI := CompactificationOf.isProper_homMap g
  letI := CompactificationOf.isProper_homMap h
  @twistedInverseImageCompIso j.space k.space l.space
    (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map h))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs
      (CompactificationOf.Hom.map g ≫ CompactificationOf.Hom.map h))
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map g))
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map h))
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map g ≫ CompactificationOf.Hom.map h))

open CompactificationOf

/-! #### The comparison of Tag 0ATX at a morphism of compactifications, unfolded

The definitional content of `Stacks.Duality.refinementTwistedCompIso` and
`Stacks.Duality.refinementTwistedComp`, each by `rfl`. -/

section Raw

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k l : CompactificationOf (Over.mk f.left)} (g : j ⟶ k) (h : k ⟶ l)
  [(quasiCoherentDerivedPushforward j.toBase
      (isQuasicoherentPush_toBase f j)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward k.toBase
      (isQuasicoherentPush_toBase f k)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward l.toBase
      (isQuasicoherentPush_toBase f l)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g)
      (isQuasicoherentPush_homMap f g)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map h)
      (isQuasicoherentPush_homMap f h)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h)
      (isQuasicoherentPush_homMap_comp f g h)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ k.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f g)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map h ≫ l.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f h)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h ≫ l.toBase)
      (isQuasicoherentPush_homMap_comp_comp_toBase f g h)).IsLeftAdjoint]

/-- The comparison `ā_j ≅ ā_k ⋙ c̄_g` of [Stacks, Tag 0ATX] for a morphism of compactifications,
with the transport along `j.toBase = G ≫ k.toBase` and the comparison of the two factors
written out. -/
theorem refinementTwistedCompIso_eq :
    refinementTwistedCompIso f g =
      twistedInverseImageCongrIso (isQuasicoherentPush_toBase f j)
          (isQuasicoherentPush_homMap_comp_toBase f g)
        (homMap_comp_toBase g).symm ≪≫
      twistedInverseImageCompIso (Hom.map g) k.toBase (isQuasicoherentPush_homMap f g)
          (isQuasicoherentPush_toBase f k)
        (isQuasicoherentPush_homMap_comp_toBase f g) :=
  rfl

omit [(quasiCoherentDerivedPushforward k.toBase
      (isQuasicoherentPush_toBase f k)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward l.toBase
      (isQuasicoherentPush_toBase f l)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g)
      (isQuasicoherentPush_homMap f g)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map h)
      (isQuasicoherentPush_homMap f h)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h)
      (isQuasicoherentPush_homMap_comp f g h)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ k.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f g)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map h ≫ l.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f h)).IsLeftAdjoint] in
/-- The comparison of [Stacks, Tag 0ATX] for a composite morphism of compactifications, read
through the composite `G ≫ H` of the two underlying morphisms of ambient schemes. -/
theorem refinementTwistedCompIso_comp_eq :
    refinementTwistedCompIso f (g ≫ h) =
      twistedInverseImageCongrIso (isQuasicoherentPush_toBase f j)
        (isQuasicoherentPush_homMap_comp_comp_toBase f g h) (homMap_comp_toBase (g ≫ h)).symm ≪≫
      @twistedInverseImageCompIso j.space l.space Y.left (Hom.map g ≫ Hom.map h) l.toBase
        (isQuasicoherentPush_homMap_comp f g h) (isQuasicoherentPush_toBase f l)
        (isQuasicoherentPush_homMap_comp_comp_toBase f g h)
        (isLeftAdjointPush_homMap_comp f g h) (isLeftAdjointPush_toBase f l)
        (isLeftAdjointPush_homMap_comp_comp_toBase f g h) :=
  rfl

omit [(quasiCoherentDerivedPushforward j.toBase
      (isQuasicoherentPush_toBase f j)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward k.toBase
      (isQuasicoherentPush_toBase f k)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward l.toBase
      (isQuasicoherentPush_toBase f l)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ k.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f g)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map h ≫ l.toBase)
      (isQuasicoherentPush_homMap_comp_toBase f h)).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (Hom.map g ≫ Hom.map h ≫ l.toBase)
      (isQuasicoherentPush_homMap_comp_comp_toBase f g h)).IsLeftAdjoint] in
/-- `Stacks.Duality.refinementTwistedComp` with its arguments written out. -/
theorem refinementTwistedComp_eq :
    refinementTwistedComp f g h =
      twistedInverseImageCompIso (Hom.map g) (Hom.map h) (isQuasicoherentPush_homMap f g)
        (isQuasicoherentPush_homMap f h)
        (isQuasicoherentPush_homMap_comp f g h) :=
  rfl

end Raw

/-! #### The cocycle identity for the comparison of Tag 0ATX -/

section Cocycle0ATX

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k l : CompactificationOf (Over.mk f.left)} (g : j ⟶ k) (h : k ⟶ l)

open CompactificationOf

/-- **The cocycle identity for the comparison of [Stacks, Tag 0ATX] at the compactifications of a
morphism of `AlgebraicGeometry.FTS S`**: the comparison attached to `g ≫ h` is the comparison
attached to `g`, then the comparison attached to `h` pushed into `c̄_g`, then the comparison
`c̄_h ⋙ c̄_g ≅ c̄_{g ≫ h}` of [Stacks, Tag 0ATX] for the two morphisms of ambient schemes. -/
theorem refinementTwistedCompIso_comp :
    refinementTwistedCompIso f (g ≫ h) =
      refinementTwistedCompIso f g ≪≫
        isoWhiskerRight (refinementTwistedCompIso f h) (refinementTwisted f g) ≪≫
          associator (compactificationTwisted f l) (refinementTwisted f h)
              (refinementTwisted f g) ≪≫
            isoWhiskerLeft (compactificationTwisted f l)
              (refinementTwistedComp f g h).symm := by
  let := isLeftAdjointPush_toBase f j
  let := isLeftAdjointPush_toBase f k
  let := isLeftAdjointPush_toBase f l
  let := isLeftAdjointPush_homMap f g
  let := isLeftAdjointPush_homMap f h
  let := isLeftAdjointPush_homMap_comp f g h
  let := isLeftAdjointPush_homMap_comp_toBase f g
  let := isLeftAdjointPush_homMap_comp_toBase f h
  let := isLeftAdjointPush_homMap_comp_comp_toBase f g h
  rw [refinementTwistedCompIso_comp_eq f g h, refinementTwistedCompIso_eq f g,
    refinementTwistedCompIso_eq f h, refinementTwistedComp_eq f g h]
  exact twistedInverseImageCongrCompIso_comp (isQuasicoherentPush_homMap f g)
    (isQuasicoherentPush_homMap f h) (isQuasicoherentPush_toBase f l)
    (isQuasicoherentPush_toBase f k) (isQuasicoherentPush_toBase f j)
    (isQuasicoherentPush_homMap_comp f g h)
    (isQuasicoherentPush_homMap_comp_toBase f h)
    (isQuasicoherentPush_homMap_comp_toBase f g)
    (isQuasicoherentPush_homMap_comp_comp_toBase f g h)
    (homMap_comp_toBase g) (homMap_comp_toBase h)

end Cocycle0ATX

/-! #### The cocycle identity for the base change maps of Tag 0AA6 -/

section CocycleBaseChange

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k l : CompactificationOf (Over.mk f.left)} (g : j ⟶ k) (h : k ⟶ l)

open CompactificationOf

/-- **The cocycle identity for the base change map of [Stacks, Tag 0AA6] at the compactifications
of a morphism of `AlgebraicGeometry.FTS S`**: the base change map of the square of `g ≫ h` is the
base change map of the square of `g`, then the base change map of the square of `h`, read through
the comparison `Stacks.Duality.refinementTwistedComp` of [Stacks, Tag 0ATX] and the
identification `Stacks.Duality.twistedInverseImageIdIso` of `(𝟙_X)^×` with the identity functor
([Stacks, Tag 0ATQ]). -/
theorem refinementBaseChange_comp (hg : PreservesInterior g) (hh : PreservesInterior h)
    (hgh : PreservesInterior (g ≫ h)) [IsIso (refinementXi f g hg)]
    [IsIso (refinementXi f h hh)] [IsIso (refinementXi f (g ≫ h) hgh)] :
    refinementBaseChange f (g ≫ h) hgh =
      Functor.whiskerRight (refinementTwistedComp f g h).hom (compactificationRestrict f j) ≫
        (associator (refinementTwisted f h) (refinementTwisted f g)
            (compactificationRestrict f j)).hom ≫
          Functor.whiskerLeft (refinementTwisted f h) (refinementBaseChange f g hg) ≫
            (associator (refinementTwisted f h) (compactificationRestrict f k)
                (twistedInverseImage (𝟙 X.left)
                  (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))).inv ≫
              Functor.whiskerRight (refinementBaseChange f h hh)
                  (twistedInverseImage (𝟙 X.left)
                    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))) ≫
                (associator (compactificationRestrict f l)
                    (twistedInverseImage (𝟙 X.left)
                      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
                    (twistedInverseImage (𝟙 X.left)
                      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))).hom ≫
                  Functor.whiskerLeft (compactificationRestrict f l)
                    (Functor.whiskerLeft (twistedInverseImage (𝟙 X.left)
                          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
                        (twistedInverseImageIdIso X.left
                          (isQuasicoherent_homology_derivedPushforward_of_qcqs
                            (𝟙 X.left))).hom ≫
                      (rightUnitor (twistedInverseImage (𝟙 X.left)
                        (isQuasicoherent_homology_derivedPushforward_of_qcqs
                          (𝟙 X.left)))).hom) := by
  let := isLeftAdjointPush_homMap f g
  let := isLeftAdjointPush_homMap f h
  let := isLeftAdjointPush_homMap_comp f g h
  exact twistedInverseImageBaseChangeMap_comp (Xs := X.left)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs k.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs l.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map g))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map h))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (Hom.map g ≫ Hom.map h))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))
    (isPullback_of_preservesInterior g hg).flip
    (isPullback_of_preservesInterior h hh).flip
    (isPullback_of_preservesInterior (g ≫ h) hgh).flip
    (iXi₁ := inferInstanceAs (IsIso (refinementXi f g hg)))
    (iXi₂ := inferInstanceAs (IsIso (refinementXi f h hh)))
    (iXir := inferInstanceAs (IsIso (refinementXi f (g ≫ h) hgh)))

end CocycleBaseChange

/-! #### The cocycle identity -/

section Cocycle

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k l : CompactificationOf (Over.mk f.left)} (g : j ⟶ k) (h : k ⟶ l)

open CompactificationOf

/-- **The cocycle identity `α_{g ≫ h} = α_g ≫ α_h`** for the comparison
`Stacks.Duality.refinementIso` of the upper shriek functors of two compactifications: the
comparison attached to a composite of two interior-preserving morphisms of compactifications is
the composite of the two comparisons. -/
theorem refinementIso_comp (hg : PreservesInterior g) (hh : PreservesInterior h)
    (hgh : PreservesInterior (g ≫ h)) [IsIso (refinementXi f g hg)]
    [IsIso (refinementXi f h hh)] [IsIso (refinementXi f (g ≫ h) hgh)]
    [IsIso (refinementBaseChangePlus f g hg)] [IsIso (refinementBaseChangePlus f h hh)]
    [IsIso (refinementBaseChangePlus f (g ≫ h) hgh)] :
    refinementIso f (g ≫ h) hgh = refinementIso f g hg ≪≫ refinementIso f h hh :=
  alphaIso_comp (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left))
    (twistedInverseImageIdIso X.left
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
    (refinementTwistedCompIso f g) (refinementTwistedCompIso f h)
    (refinementTwistedCompIso f (g ≫ h)) (refinementTwistedComp f g h)
    (refinementBaseChange f g hg) (refinementBaseChange f h hh)
    (refinementBaseChange f (g ≫ h) hgh) (refinementTwistedCompIso_comp f g h)
    (refinementBaseChange_comp f g h hg hh hgh)

end Cocycle

end Refinement

end Stacks.Duality

end
