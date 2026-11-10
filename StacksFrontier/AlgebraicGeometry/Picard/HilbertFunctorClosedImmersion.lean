module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.WeilRestriction
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ProperSupport
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpenRepresentable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed immersion induces a closed immersion of Hilbert schemes

Let `i : X ⟶ Y` be a closed immersion of schemes over a base `S` and let `d` be a natural
number.  If the degree-`d` Hilbert functor of `Y` is representable by a scheme `H_Y` over `S`,
then the degree-`d` Hilbert functor of `X` is representable as well, by a closed subscheme of
`H_Y`.

## Main results

* `Stacks.Hilbert.exists_closedSubschemeRepresentingHilbertFunctor` is Tag 0B97.

## Implementation notes

The representing closed subscheme is the Weil restriction of Tag 07AI.  Write `Z ⊂ Y ×_S H_Y`
for the universal family and `p : Z ⟶ H_Y` for its structure morphism, which is finite locally
free of rank `d`; let `Z' = Z ×_{Y ×_S H_Y} (X ×_S H_Y)` be the part of the universal family
lying in `X`, a closed subscheme of `Z`.  A morphism `T ⟶ H_Y` classifies a family that lies in
`X` exactly when the base change `Z'_T ⟶ Z_T` is an isomorphism, so the locus to be cut out is
the Weil restriction of `Z'` along `p`, which Tag 07AI represents by a closed immersion
`W ⟶ H_Y`: the hypotheses of Tag 07AI hold because `p` is finite locally free, hence of finite
presentation and flat by Tag 02KB, and pure relative to `H_Y` because it is proper.

Identifying the base change of the universal family with the family classified by the
base-changed morphism is what the bulk of this file does.  Both the Weil restriction and the
Hilbert functor are formulated through fibre products, and the two presentations of
`Z_T ⊂ Y ×_S T` — pull back along `T ⟶ H_Y` inside `Y ×_S H_Y`, or form the fibre product of
`Z ⟶ H_Y` with `T ⟶ H_Y` — differ by a canonical isomorphism; `intersectionIso` and
`iteratedBaseChangeIso` are those comparisons, and `universalFamilyRestrictionProperty_iff`
transports the isomorphism condition across them.

Once that is available, the bijection between morphisms `T ⟶ W` and degree-`d` families in `X`
is the one of `H_Y` restricted along the closed immersion: a family in `X` is sent to its image
in `Y ×_S T`, and a family in `Y` lying in `X` is recovered as the inverse image ideal of its
ideal sheaf along `X ×_S T ⟶ Y ×_S T`.  The two operations are mutually inverse because, for a
closed immersion `k`, the inverse image of the image ideal is the ideal itself, and conversely
when the family already lies in `X`.

## References

* [Stacks Project, Tag 0B94](https://stacks.math.columbia.edu/tag/0B94)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 07AI](https://stacks.math.columbia.edu/tag/07AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

namespace Bridge
variable {X Y D S T : Scheme.{u}}
variable (k : X ⟶ Y) (a : D ⟶ Y) (q : Y ⟶ S) (g : T ⟶ S)

private noncomputable abbrev bcmap (f : X ⟶ Y) (q : Y ⟶ S) (g : T ⟶ S) :
    pullback (f ≫ q) g ⟶ pullback q g :=
  pullback.map (f ≫ q) g q g f (𝟙 _) (𝟙 _) (by simp) (by simp)

private noncomputable abbrev xT := pullback (k ≫ q) g
private noncomputable abbrev dT := pullback (a ≫ q) g
private noncomputable abbrev kT := bcmap k q g
private noncomputable abbrev aT := bcmap a q g
private noncomputable abbrev common := pullback k (pullback.fst (a ≫ q) g ≫ a)

@[reassoc (attr := simp)] private lemma bcmap_fst (f : X ⟶ Y) (q : Y ⟶ S) (g : T ⟶ S) :
    bcmap f q g ≫ pullback.fst q g = pullback.fst (f ≫ q) g ≫ f := by
  dsimp [bcmap, pullback.map]
  rw [pullback.lift_fst]

@[reassoc (attr := simp)] private lemma bcmap_snd (f : X ⟶ Y) (q : Y ⟶ S) (g : T ⟶ S) :
    bcmap f q g ≫ pullback.snd q g = pullback.snd (f ≫ q) g := by
  dsimp [bcmap, pullback.map]
  rw [pullback.lift_snd]
  simp

private noncomputable def eW : pullback ((pullback.snd k a) ≫ (a ≫ q)) g ≅ common k a q g :=
  (pullbackRightPullbackFstIso (a ≫ q) g (pullback.snd k a)).symm ≪≫
    pullbackLeftPullbackSndIso k a (pullback.fst (a ≫ q) g)

private noncomputable def wMap : pullback ((pullback.snd k a) ≫ (a ≫ q)) g ⟶ pullback (a ≫ q) g :=
  pullback.map ((pullback.snd k a) ≫ (a ≫ q)) g (a ≫ q) g (pullback.snd k a) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

private noncomputable abbrev dToY : dT a q g ⟶ Y := pullback.fst (a ≫ q) g ≫ a

private noncomputable def eB : pullback (kT k q g) (aT a q g) ≅ common k a q g where
  hom := pullback.lift (pullback.fst _ _ ≫ pullback.fst (k ≫ q) g) (pullback.snd _ _) (by
    simpa [dToY] using
      pullback.condition_assoc (f := kT k q g) (g := aT a q g) (h := pullback.fst q g))
  inv := pullback.lift
    (pullback.lift (pullback.fst k (dToY a q g))
      (pullback.snd k (dToY a q g) ≫ pullback.snd (a ≫ q) g) (by
        simp [dToY, pullback.condition_assoc, pullback.condition]))
    (pullback.snd k (dToY a q g)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, bcmap_fst, pullback.lift_fst_assoc]
        exact pullback.condition
      · simp only [Category.assoc, Category.comp_id, pullback.lift_snd])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_snd_assoc]
        simpa using
          (pullback.condition_assoc (f := kT k q g) (g := aT a q g) (h := pullback.snd q g)).symm
    · simp only [Category.assoc, Category.id_comp, pullback.lift_snd]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc]

private lemma eW_hom_snd :
    (eW k a q g).hom ≫ pullback.snd k (dToY a q g) = wMap k a q g := by
  let u := pullback.snd k a
  let p := a ≫ q
  let r := pullbackRightPullbackFstIso p g u
  let l := pullbackLeftPullbackSndIso k a (pullback.fst p g)
  apply pullback.hom_ext
  · calc
      ((eW k a q g).hom ≫ pullback.snd k (dToY a q g)) ≫ pullback.fst p g =
          r.inv ≫ (l.hom ≫ pullback.snd k (dToY a q g) ≫ pullback.fst p g) := by
            rfl
      _ = r.inv ≫ (pullback.snd u (pullback.fst p g) ≫ pullback.fst p g) := by
            rw [pullbackLeftPullbackSndIso_hom_snd_assoc]
      _ = r.inv ≫ (pullback.fst u (pullback.fst p g) ≫ u) := by
            rw [← pullback.condition]
      _ = pullback.fst (u ≫ p) g ≫ u := by
            rw [pullbackRightPullbackFstIso_inv_fst_assoc]
      _ = wMap k a q g ≫ pullback.fst p g := by
            dsimp [wMap, pullback.map]
            rw [pullback.lift_fst]
  · calc
      (eW k a q g).hom ≫ pullback.snd k (dToY a q g) ≫ pullback.snd p g =
          r.inv ≫ (l.hom ≫ pullback.snd k (dToY a q g)) ≫ pullback.snd p g := by
            rfl
      _ = r.inv ≫ pullback.snd u (pullback.fst p g) ≫ pullback.snd p g := by
            rw [pullbackLeftPullbackSndIso_hom_snd]
      _ = pullback.snd (u ≫ p) g := by
            rw [pullbackRightPullbackFstIso_inv_snd_snd]
      _ = wMap k a q g ≫ pullback.snd p g := by
            dsimp [wMap, pullback.map]
            rw [pullback.lift_snd]
            simp [u, p]

private lemma eB_hom_snd :
    (eB k a q g).hom ≫ pullback.snd k (dToY a q g) =
      pullback.snd (kT k q g) (aT a q g) := by
  simp [eB, dToY, common]

private noncomputable def intersectionIso :
    pullback ((pullback.snd k a) ≫ (a ≫ q)) g ≅ pullback (kT k q g) (aT a q g) :=
  eW k a q g ≪≫ (eB k a q g).symm

private lemma intersectionIso_map :
    (intersectionIso k a q g).hom ≫ pullback.snd (kT k q g) (aT a q g) = wMap k a q g := by
  calc
    (intersectionIso k a q g).hom ≫ pullback.snd (kT k q g) (aT a q g) =
        (eW k a q g).hom ≫ pullback.snd k (dToY a q g) := by
          simp only [intersectionIso, Iso.trans_hom, Category.assoc]
          rw [← eB_hom_snd]
          simp
    _ = wMap k a q g := eW_hom_snd k a q g

end Bridge

private noncomputable def idealMapSubschemeIso {X Y : Scheme.{u}} (k : X ⟶ Y)
    [IsClosedImmersion k] (I : X.IdealSheafData) :
    I.subscheme ≅ (I.map k).subscheme := by
  let c := I.subschemeι ≫ k
  have hfac : c.toImage ≫ (I.map k).subschemeι = c := by
    simp [c, Scheme.Hom.image, Scheme.IdealSheafData.map]
  have hker : c.ker = (I.map k).subschemeι.ker := by
    simp [c, Scheme.IdealSheafData.map]
  haveI : IsClosedImmersion c := by dsimp [c]; infer_instance
  have hc : IsIso c.toImage :=
    IsClosedImmersion.isIso_of_ker_eq c (I.map k).subschemeι c.toImage hfac hker
  letI : IsIso c.toImage := hc
  exact asIso c.toImage ≪≫ eqToIso (show c.image = (I.map k).subscheme from rfl)

private theorem idealMapSubschemeIso_fac {X Y : Scheme.{u}} (k : X ⟶ Y)
    [IsClosedImmersion k] (I : X.IdealSheafData) :
    (idealMapSubschemeIso k I).hom ≫ (I.map k).subschemeι = I.subschemeι ≫ k := by
  let c := I.subschemeι ≫ k
  have hImage : c.image = (I.map k).subscheme := rfl
  have hback : eqToHom hImage ≫ (I.map k).subschemeι = c.imageι := by
    cases hImage
    rfl
  change c.toImage ≫ eqToHom hImage ≫ (I.map k).subschemeι = I.subschemeι ≫ k
  rw [hback]
  exact c.toImage_imageι

private lemma pullback_snd_isIso_of_map {X Y : Scheme.{u}} (k : X ⟶ Y)
    [IsClosedImmersion k] (I : X.IdealSheafData) :
    IsIso (pullback.snd k (I.map k).subschemeι) := by
  let e := idealMapSubschemeIso k I
  let q : I.subscheme ⟶ pullback k (I.map k).subschemeι :=
    pullback.lift I.subschemeι e.hom (by simpa using (idealMapSubschemeIso_fac k I).symm)
  have hq : q ≫ pullback.snd k (I.map k).subschemeι = e.hom := pullback.lift_snd _ _ _
  let : IsSplitEpi (pullback.snd k (I.map k).subschemeι) :=
    IsSplitEpi.mk' ⟨e.inv ≫ q, by rw [Category.assoc, hq, e.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi _

private lemma map_comap_eq_of_pullback_snd_isIso {X Y : Scheme.{u}} (k : X ⟶ Y)
    (K : Y.IdealSheafData) (h : IsIso (pullback.snd k K.subschemeι)) :
    (K.comap k).map k = K := by
  let J := K.comap k
  have hker : (J.subschemeι ≫ k).ker = K.subschemeι.ker := by
    let e := K.comapIso k
    let : IsIso (pullback.snd k K.subschemeι) := h
    have heq : J.subschemeι ≫ k = (e.hom ≫ pullback.snd k K.subschemeι) ≫
        K.subschemeι := by
      change (K.comap k).subschemeι ≫ k =
        (e.hom ≫ pullback.snd k K.subschemeι) ≫ K.subschemeι
      rw [← Scheme.IdealSheafData.comapIso_hom_fst K k, Category.assoc,
        pullback.condition, ← Category.assoc]
    rw [heq]
    exact Scheme.Hom.ker_comp_of_isIso (e.hom ≫ pullback.snd k K.subschemeι) K.subschemeι
  calc
    (K.comap k).map k = (J.subschemeι ≫ k).ker := by simp [J, Scheme.IdealSheafData.map]
    _ = K.subschemeι.ker := hker
    _ = K := K.ker_subschemeι

/-- Finite local freeness of rank `d` transported along an isomorphism of sources compatible with
the two morphisms. -/
private theorem isFiniteLocallyFreeOfRank_of_iso_comp {A B T : Scheme.{u}} (e : A ≅ B)
    {a : A ⟶ T} {b : B ⟶ T} (h : e.hom ≫ b = a) {d : ℕ}
    (hb : Stacks.Morphisms.IsFiniteLocallyFreeOfRank b d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank a d :=
  h ▸ Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp e b hb

private theorem map_preserves_rank {X Y T : Scheme.{u}} (k : X ⟶ Y)
    [IsClosedImmersion k] (I : X.IdealSheafData) (fX : X ⟶ T) (fY : Y ⟶ T)
    (hk : k ≫ fY = fX) (d : ℕ)
    (hI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ fX) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I.map k).subschemeι ≫ fY) d := by
  refine isFiniteLocallyFreeOfRank_of_iso_comp (idealMapSubschemeIso k I).symm ?_ hI
  rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, idealMapSubschemeIso_fac,
    Category.assoc, hk]

private theorem comap_preserves_rank_of_pullback_snd_isIso {X Y T : Scheme.{u}}
    (k : X ⟶ Y) (pX : X ⟶ T) (pY : Y ⟶ T) (hk : k ≫ pY = pX)
    (K : Y.IdealSheafData) (hIso : IsIso (pullback.snd k K.subschemeι)) (d : ℕ)
    (hK : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (K.subschemeι ≫ pY) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((K.comap k).subschemeι ≫ pX) d := by
  let : IsIso (pullback.snd k K.subschemeι) := hIso
  refine isFiniteLocallyFreeOfRank_of_iso_comp
    ((K.comapIso k) ≪≫ asIso (pullback.snd k K.subschemeι)) ?_ hK
  simp [← hk]

private theorem comap_map_eq_of_closedImmersion {X Y : Scheme.{u}} (k : X ⟶ Y)
    [IsClosedImmersion k] (I : X.IdealSheafData) : (I.map k).comap k = I := by
  let K := I.map k
  let c := I.subschemeι ≫ k
  let e₀ := idealMapSubschemeIso k I
  let P := pullback k K.subschemeι
  let s := pullback.snd k K.subschemeι
  let : IsIso s := pullback_snd_isIso_of_map k I
  let e₁ := asIso s
  let q : I.subscheme ⟶ P := pullback.lift I.subschemeι e₀.hom (by
    simpa [e₀] using (idealMapSubschemeIso_fac k I).symm)
  have hq : q ≫ s = e₀.hom := pullback.lift_snd _ _ _
  have hqeq : q = e₀.hom ≫ e₁.inv := by
    apply (cancel_mono s).1
    simp [Category.assoc, hq, e₁]
  have : IsIso q := by
    rw [hqeq]
    infer_instance
  let e₂ := K.comapIso k
  let e : I.subscheme ≅ (K.comap k).subscheme := asIso q ≪≫ e₂.symm
  have hefac : e.hom ≫ (K.comap k).subschemeι = I.subschemeι := by
    calc
      e.hom ≫ (K.comap k).subschemeι =
          q ≫ (e₂.inv ≫ (K.comap k).subschemeι) := by simp [e]
      _ = q ≫ pullback.fst k K.subschemeι := by
        rw [Scheme.IdealSheafData.comapIso_inv_subschemeι]
      _ = I.subschemeι := by
        dsimp [q, P]
        rw [pullback.lift_fst]
  calc
    (K.comap k) = (K.comap k).subschemeι.ker := (K.comap k).ker_subschemeι.symm
    _ = (e.hom ≫ (K.comap k).subschemeι).ker := by
      rw [Scheme.Hom.ker_comp_of_isIso e.hom, (K.comap k).ker_subschemeι]
    _ = I.subschemeι.ker := by rw [hefac]
    _ = I := I.ker_subschemeι

private instance familyAmbientMap_isClosedImmersion {S : Scheme.{u}} {X Y : Over S}
    (i : X ⟶ Y) [IsClosedImmersion i.left] (T : Over S) :
    IsClosedImmersion (familyAmbientMap i T) := by
  have hmap : familyAmbientMap i T = ((Over.pullback T.hom).map i).left := by
    dsimp [familyAmbientMap]
    apply pullback.hom_ext <;> simp [pullback.map]
  rw [hmap]
  exact MorphismProperty.overPullbackMap T.hom i
    (show IsClosedImmersion i.left from inferInstance)

private alias familyAmbientMap_naturality := familyAmbientMap_familyBaseChangeMap

private noncomputable abbrev iteratedBaseChangeIso {S : Scheme.{u}} {X : Over S} {H T : Over S}
    (g : T ⟶ H) :
    ((Over.pullback g.left).obj ((Over.pullback H.hom).obj X)).left ≅
      ((Over.pullback T.hom).obj X).left :=
  pullbackLeftPullbackSndIso X.hom H.hom g.left ≪≫
    pullback.congrHom rfl (Over.w g)

private theorem congrHom_inv_fst {A B C : Scheme.{u}} (f : A ⟶ C) (g₁ g₂ : B ⟶ C)
    (h : g₁ = g₂) :
    (pullback.congrHom rfl h).inv ≫ pullback.fst f g₁ = pullback.fst f g₂ := by
  rw [pullback.congrHom_inv]
  dsimp [pullback.map]
  rw [pullback.lift_fst]
  simp

private theorem congrHom_inv_snd {A B C : Scheme.{u}} (f : A ⟶ C) (g₁ g₂ : B ⟶ C)
    (h : g₁ = g₂) :
    (pullback.congrHom rfl h).inv ≫ pullback.snd f g₁ = pullback.snd f g₂ := by
  rw [pullback.congrHom_inv]
  dsimp [pullback.map]
  rw [pullback.lift_snd]
  simp

private theorem iteratedBaseChangeIso_inv_fst_fst {S : Scheme.{u}} {X : Over S}
    {H T : Over S} (g : T ⟶ H) :
    (iteratedBaseChangeIso g).inv ≫ pullback.fst (pullback.snd X.hom H.hom) g.left ≫
      pullback.fst X.hom H.hom = pullback.fst X.hom T.hom := by
  change ((pullback.congrHom rfl (Over.w g)).inv ≫
      (pullbackLeftPullbackSndIso X.hom H.hom g.left).inv) ≫
      pullback.fst (pullback.snd X.hom H.hom) g.left ≫ pullback.fst X.hom H.hom = _
  calc
    _ = (pullback.congrHom rfl (Over.w g)).inv ≫ pullback.fst X.hom (g.left ≫ H.hom) := by
      simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
    _ = pullback.fst X.hom T.hom :=
      congrHom_inv_fst X.hom (g.left ≫ H.hom) T.hom (Over.w g)

private theorem iteratedBaseChangeIso_inv_snd {S : Scheme.{u}} {X : Over S}
    {H T : Over S} (g : T ⟶ H) :
    (iteratedBaseChangeIso g).inv ≫ pullback.snd (pullback.snd X.hom H.hom) g.left =
      pullback.snd X.hom T.hom := by
  change ((pullback.congrHom rfl (Over.w g)).inv ≫
      (pullbackLeftPullbackSndIso X.hom H.hom g.left).inv) ≫
      pullback.snd (pullback.snd X.hom H.hom) g.left = _
  calc
    _ = (pullback.congrHom rfl (Over.w g)).inv ≫ pullback.snd X.hom (g.left ≫ H.hom) := by
      simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    _ = pullback.snd X.hom T.hom :=
      congrHom_inv_snd X.hom (g.left ≫ H.hom) T.hom (Over.w g)

private theorem iteratedBaseChangeIso_hom_fst_fst {S : Scheme.{u}} {X : Over S}
    {H T : Over S} (g : T ⟶ H) :
    (iteratedBaseChangeIso g).hom ≫ pullback.fst X.hom T.hom =
      pullback.fst (pullback.snd X.hom H.hom) g.left ≫ pullback.fst X.hom H.hom := by
  rw [← iteratedBaseChangeIso_inv_fst_fst g, Iso.hom_inv_id_assoc]

private theorem iteratedBaseChangeIso_hom_snd {S : Scheme.{u}} {X : Over S}
    {H T : Over S} (g : T ⟶ H) :
    (iteratedBaseChangeIso g).hom ≫ pullback.snd X.hom T.hom =
      pullback.snd (pullback.snd X.hom H.hom) g.left := by
  rw [← iteratedBaseChangeIso_inv_snd g, Iso.hom_inv_id_assoc]

private theorem iteratedBaseChangeIso_inv_fst {S : Scheme.{u}} {X : Over S}
    {H T : Over S} (g : T ⟶ H) :
    (iteratedBaseChangeIso g).inv ≫ pullback.fst (pullback.snd X.hom H.hom) g.left =
      familyBaseChangeMap X g := by
  apply pullback.hom_ext
  · calc
      (iteratedBaseChangeIso g).inv ≫ pullback.fst (pullback.snd X.hom H.hom) g.left ≫
          pullback.fst X.hom H.hom = pullback.fst X.hom T.hom :=
            iteratedBaseChangeIso_inv_fst_fst g
      _ = familyBaseChangeMap X g ≫ pullback.fst X.hom H.hom := by
            symm
            dsimp [familyBaseChangeMap, pullback.map]
            rw [pullback.lift_fst]
            simp
  · calc
      (iteratedBaseChangeIso g).inv ≫ pullback.fst (pullback.snd X.hom H.hom) g.left ≫
          pullback.snd X.hom H.hom = pullback.snd X.hom T.hom ≫ g.left := by
            change ((pullback.congrHom rfl (Over.w g)).inv ≫
                (pullbackLeftPullbackSndIso X.hom H.hom g.left).inv) ≫
                pullback.fst (pullback.snd X.hom H.hom) g.left ≫ pullback.snd X.hom H.hom = _
            simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]
            rw [reassoc_of% (congrHom_inv_snd X.hom (g.left ≫ H.hom) T.hom (Over.w g))]
      _ = familyBaseChangeMap X g ≫ pullback.snd X.hom H.hom := by
            symm
            dsimp [familyBaseChangeMap, pullback.map]
            rw [pullback.lift_snd]

private theorem ideal_comap_baseChange_naturality {S : Scheme.{u}} {X Y : Over S}
    (i : X ⟶ Y) {T' T : Over S} (g : T' ⟶ T)
    (I : ((Over.pullback T.hom).obj Y).left.IdealSheafData) :
    (I.comap (familyAmbientMap i T)).comap (familyBaseChangeMap X g) =
      (I.comap (familyBaseChangeMap Y g)).comap (familyAmbientMap i T') := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    familyAmbientMap_naturality]

/-- The part of the universal family of `H_Y` lying in `X`, as a closed subscheme of the
universal family: the fibre product of the universal family with `X ×_S H_Y`. -/
private noncomputable abbrev universalFamilyInX {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y)
    {d : ℕ} {H_Y : Over S} (hY : RepresentsHilbertFunctorOfRank Y H_Y d) :
    pullback (familyAmbientMap i H_Y) (hY.family (𝟙 H_Y)).ideal.subschemeι ⟶
      (hY.family (𝟙 H_Y)).ideal.subscheme :=
  pullback.snd (familyAmbientMap i H_Y) (hY.family (𝟙 H_Y)).ideal.subschemeι

/-- The structure morphism of the universal family of `H_Y`, which is finite locally free of
rank `d`. -/
private noncomputable abbrev universalFamilyHom {S : Scheme.{u}} {Y : Over S} {d : ℕ}
    {H_Y : Over S} (hY : RepresentsHilbertFunctorOfRank Y H_Y d) :
    (hY.family (𝟙 H_Y)).ideal.subscheme ⟶ H_Y.left :=
  (hY.family (𝟙 H_Y)).ideal.subschemeι ≫ ((Over.pullback H_Y.hom).obj Y).hom

/-- **The closed subscheme of `H_Y` to be constructed, as a Weil restriction.**  The locus in
`H_Y` over which the universal family lies in `X` is the Weil restriction of the closed
subscheme `universalFamilyInX` along the universal family's structure morphism, and Tag 07AI
represents it by a closed immersion: the structure morphism is finite locally free of rank `d`,
hence flat and of finite presentation by Tag 02KB, and it is pure relative to `H_Y` because it
is proper. -/
@[sga "3 VIB 6.5.2" "(i), special case"]
private theorem exists_universal_family_weil_restriction {S : Scheme.{u}}
    {X Y : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left] (d : ℕ)
    (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d) :
    ∃ (W : Over H_Y.left), IsClosedImmersion W.hom ∧
      Nonempty ((Stacks.Flatness.weilRestrictionFunctor
        (universalFamilyInX i hY) (universalFamilyHom hY)).RepresentableBy W) := by
  let F := hY.family (𝟙 H_Y)
  let YH := (Over.pullback H_Y.hom).obj Y
  let k := familyAmbientMap i H_Y
  let p : F.ideal.subscheme ⟶ H_Y.left := F.ideal.subschemeι ≫ YH.hom
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p d := by
    change Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (F.ideal.subschemeι ≫ YH.hom) d
    exact F.isFiniteLocallyFreeOfRank
  let : Stacks.Morphisms.IsFiniteLocallyFree p :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p d
  have hfinite :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
      (inferInstance : Stacks.Morphisms.IsFiniteLocallyFree p)
  let : IsFinite p := hfinite.1
  let : Flat p := hfinite.2.1
  let : LocallyOfFinitePresentation p := hfinite.2.2
  let : LocallyOfFiniteType p := inferInstance
  let : QuasiCompact p := inferInstance
  let : QuasiSeparated p := inferInstance
  have hpure : AlgebraicGeometry.IsSchemePureRelative p := by
    have hu := AlgebraicGeometry.isSchemeUniversallyPureRelative_of_isProper p
    intro s D hEtale hElementary
    exact hu s D
  let : IsClosedImmersion k := familyAmbientMap_isClosedImmersion i H_Y
  let iD : pullback k F.ideal.subschemeι ⟶ F.ideal.subscheme :=
    pullback.snd k F.ideal.subschemeι
  have : IsClosedImmersion iD := by
    dsimp [iD]
    infer_instance
  exact Stacks.Flatness.weilRestriction_representableBy_closedImmersion_of_affineTests iD p hpure

private def universalFamilyRestrictionProperty {S : Scheme.{u}}
    {X Y H_Y : Over S} (i : X ⟶ Y) (d : ℕ)
    (hY : RepresentsHilbertFunctorOfRank Y H_Y d)
    {T : Over S} (f : T ⟶ H_Y) : Prop := by
  let U := hY.family (𝟙 H_Y)
  let YH := (Over.pullback H_Y.hom).obj Y
  let iD := pullback.snd (familyAmbientMap i H_Y) U.ideal.subschemeι
  let p := U.ideal.subschemeι ≫ YH.hom
  let test : Over H_Y.left := Over.mk f.left
  let idOver : Over.mk (iD ≫ p) ⟶ Over.mk p := Over.homMk iD (by simp [p])
  exact IsIso ((Over.pullback test.hom).map idOver).left

private theorem universalFamilyBaseChange_subscheme_fac {S : Scheme.{u}}
    {Y H_Y : Over S} (d : ℕ)
    (hY : RepresentsHilbertFunctorOfRank Y H_Y d) {T : Over S} (f : T ⟶ H_Y) :
    ∃ e : pullback
        ((hY.family (𝟙 H_Y)).ideal.subschemeι ≫
          ((Over.pullback H_Y.hom).obj Y).hom) f.left ≅
          ((hY.family (𝟙 H_Y)).ideal.comap (familyBaseChangeMap Y f)).subscheme,
      e.hom ≫
          ((hY.family (𝟙 H_Y)).ideal.comap (familyBaseChangeMap Y f)).subschemeι =
        Bridge.aT (hY.family (𝟙 H_Y)).ideal.subschemeι
          ((Over.pullback H_Y.hom).obj Y).hom f.left ≫
          (iteratedBaseChangeIso (X := Y) f).hom := by
  let U := hY.family (𝟙 H_Y)
  let YH := (Over.pullback H_Y.hom).obj Y
  let j := familyBaseChangeMap Y f
  let q := YH.hom
  let a := U.ideal.subschemeι
  let eY := iteratedBaseChangeIso (X := Y) f
  let r := pullbackRightPullbackFstIso q f.left a
  have hInv : eY.inv ≫ pullback.fst q f.left = j :=
    iteratedBaseChangeIso_inv_fst (X := Y) f
  have hb : pullback.fst q f.left = eY.hom ≫ j := by rw [← hInv, Iso.hom_inv_id_assoc]
  let cF : pullback a (pullback.fst q f.left) ⟶ pullback a j :=
    pullback.lift (pullback.fst a (pullback.fst q f.left))
      (pullback.snd a (pullback.fst q f.left) ≫ eY.hom) (by
        rw [Category.assoc, ← hb]
        exact pullback.condition)
  let cB : pullback a j ⟶ pullback a (pullback.fst q f.left) :=
    pullback.lift (pullback.fst a j) (pullback.snd a j ≫ eY.inv) (by
      rw [Category.assoc, hInv]
      exact pullback.condition)
  have hc₁ : cF ≫ cB = 𝟙 _ := by
    apply pullback.hom_ext
    · dsimp [cF, cB]
      simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · dsimp [cF, cB]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      simp [Category.assoc]
  have hc₂ : cB ≫ cF = 𝟙 _ := by
    apply pullback.hom_ext
    · dsimp [cF, cB]
      simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · dsimp [cF, cB]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      simp [Category.assoc]
  let c : pullback a (pullback.fst q f.left) ≅ pullback a j := Iso.mk cF cB hc₁ hc₂
  let e : pullback (a ≫ q) f.left ≅ (U.ideal.comap j).subscheme :=
    r.symm ≪≫ c ≪≫ (pullbackSymmetry j a).symm ≪≫ (U.ideal.comapIso j).symm
  have hr : r.inv ≫ pullback.snd a (pullback.fst q f.left) = Bridge.aT a q f.left := by
    apply pullback.hom_ext <;> simp [r, Bridge.aT, Bridge.bcmap, Category.assoc]
  have hs : (pullbackSymmetry j a).symm.hom ≫ pullback.fst j a = pullback.snd a j := by
    simp
  have hfac : e.hom ≫ (U.ideal.comap j).subschemeι =
      Bridge.aT a q f.left ≫ eY.hom := by
    change r.symm.hom ≫ c.hom ≫ (pullbackSymmetry j a).symm.hom ≫
      (U.ideal.comapIso j).inv ≫ (U.ideal.comap j).subschemeι = _
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι, hs]
    change r.inv ≫ cF ≫ pullback.snd a j = _
    dsimp [cF]
    rw [pullback.lift_snd, reassoc_of% hr]
  exact ⟨e, hfac⟩

private theorem universalFamilyRestrictionProperty_iff {S : Scheme.{u}}
    {X Y H_Y : Over S} (i : X ⟶ Y) (d : ℕ) [IsClosedImmersion i.left]
    (hY : RepresentsHilbertFunctorOfRank Y H_Y d) {T : Over S} (f : T ⟶ H_Y) :
    universalFamilyRestrictionProperty i d hY f ↔
      IsIso (pullback.snd (familyAmbientMap i T) (hY.family f).ideal.subschemeι) := by
  classical
  let U := hY.family (𝟙 H_Y)
  let YH := (Over.pullback H_Y.hom).obj Y
  let XH := (Over.pullback H_Y.hom).obj X
  let q := YH.hom
  let a := U.ideal.subschemeι
  let j := familyBaseChangeMap Y f
  let K := U.ideal.comap j
  have hnat : (hY.family f).ideal = K := by
    simpa [K, j, familyBaseChangeMap] using hY.naturality f (𝟙 H_Y)
  obtain ⟨eU, heU⟩ := universalFamilyBaseChange_subscheme_fac d hY f
  let eX := iteratedBaseChangeIso (X := X) f
  let eY := iteratedBaseChangeIso (X := Y) f
  let k := familyAmbientMap i H_Y
  have hkq : k ≫ q = XH.hom := by
    dsimp [k, q, XH, YH, familyAmbientMap, pullback.map]
    rw [pullback.lift_snd]
    simp
  let eXc := pullback.congrHom (X := XH.left) (Y := T.left) (Z := H_Y.left)
    (f₁ := k ≫ q) (f₂ := XH.hom) (g₁ := f.left) (g₂ := f.left) hkq rfl
  have heXc_fst : eXc.hom ≫ pullback.fst XH.hom f.left =
      pullback.fst (k ≫ q) f.left := by
    dsimp [eXc]
    rw [pullback.congrHom_hom]
    dsimp [pullback.map]
    rw [pullback.lift_fst]
    simp
  have heXc_snd : eXc.hom ≫ pullback.snd XH.hom f.left =
      pullback.snd (k ≫ q) f.left := by
    dsimp [eXc]
    rw [pullback.congrHom_hom]
    dsimp [pullback.map]
    rw [pullback.lift_snd]
    simp
  have heXc_fst' : eXc.hom ≫ pullback.fst (pullback.snd X.hom H_Y.hom) f.left =
      pullback.fst (k ≫ q) f.left := by
    simpa [XH] using heXc_fst
  have heXc_snd' : eXc.hom ≫ pullback.snd (pullback.snd X.hom H_Y.hom) f.left =
      pullback.snd (k ≫ q) f.left := by
    simpa [XH] using heXc_snd
  let eX' := eXc ≪≫ eX
  have heXfst : eX'.hom ≫ pullback.fst X.hom T.hom =
      pullback.fst (k ≫ q) f.left ≫ pullback.fst X.hom H_Y.hom := by
    dsimp [eX']
    rw [Category.assoc, iteratedBaseChangeIso_hom_fst_fst]
    rw [← Category.assoc, heXc_fst']
  have heXsnd : eX'.hom ≫ pullback.snd X.hom T.hom =
      pullback.snd (k ≫ q) f.left := by
    dsimp [eX']
    rw [Category.assoc, iteratedBaseChangeIso_hom_snd]
    exact heXc_snd'
  let kT := Bridge.kT k q f.left
  let aT := Bridge.aT a q f.left
  let kDirect := familyAmbientMap i T
  have hkfst : k ≫ pullback.fst Y.hom H_Y.hom =
      pullback.fst X.hom H_Y.hom ≫ i.left := by
    dsimp [k, familyAmbientMap, pullback.map]
    rw [pullback.lift_fst]
  have hDirectFst : kDirect ≫ pullback.fst Y.hom T.hom =
      pullback.fst X.hom T.hom ≫ i.left := by
    dsimp [kDirect, familyAmbientMap, pullback.map]
    rw [pullback.lift_fst]
  have hDirectSnd : kDirect ≫ pullback.snd Y.hom T.hom =
      pullback.snd X.hom T.hom := by
    dsimp [kDirect, familyAmbientMap, pullback.map]
    rw [pullback.lift_snd]
    simp
  have hk : kT ≫ eY.hom = eX'.hom ≫ kDirect := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, iteratedBaseChangeIso_hom_fst_fst, hDirectFst,
        reassoc_of% heXfst, ← hkfst]
      exact Bridge.bcmap_fst_assoc k q f.left _
    · rw [Category.assoc, Category.assoc, iteratedBaseChangeIso_hom_snd, hDirectSnd, heXsnd]
      exact Bridge.bcmap_snd k q f.left
  have ha : aT ≫ eY.hom = eU.hom ≫ K.subschemeι := heU.symm
  let m := pullback.map kT aT kDirect K.subschemeι eX'.hom eU.hom eY.hom hk ha
  let : IsIso m := by
    dsimp [m]
    infer_instance
  let eI : pullback kT aT ≅ pullback kDirect K.subschemeι := asIso m
  have hm : m ≫ pullback.snd kDirect K.subschemeι =
      pullback.snd kT aT ≫ eU.hom := by
    dsimp [m, pullback.map]
    rw [pullback.lift_snd]
  let eAll := Bridge.intersectionIso k a q f.left ≪≫ eI
  have heq : Bridge.wMap k a q f.left ≫ eU.hom =
      eAll.hom ≫ pullback.snd kDirect K.subschemeι := by
    calc
      Bridge.wMap k a q f.left ≫ eU.hom =
          (Bridge.intersectionIso k a q f.left).hom ≫
            pullback.snd kT aT ≫ eU.hom := by
              simpa [kT, aT, Category.assoc] using
                (congrArg (fun m => m ≫ eU.hom)
                  (Bridge.intersectionIso_map k a q f.left)).symm
      _ = (Bridge.intersectionIso k a q f.left).hom ≫
            (m ≫ pullback.snd kDirect K.subschemeι) := by rw [hm]
      _ = eAll.hom ≫ pullback.snd kDirect K.subschemeι := by
            simp [eAll, eI, Category.assoc]
  change IsIso (Bridge.wMap k a q f.left) ↔
    IsIso (pullback.snd kDirect (hY.family f).ideal.subschemeι)
  rw [hnat, ← isIso_comp_right_iff (Bridge.wMap k a q f.left) eU.hom, heq,
    isIso_comp_left_iff eAll.hom]

private alias familyAmbientMap_comp_hom := familyAmbientMap_hom

private theorem isIso_of_factors_through_weilRestriction {S : Scheme.{u}}
    {X Y : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left] (d : ℕ)
    (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d) (W : Over H_Y.left)
    (hW : Nonempty ((Stacks.Flatness.weilRestrictionFunctor
      (universalFamilyInX i hY) (universalFamilyHom hY)).RepresentableBy W))
    {T : Over S} (f : T ⟶ Over.mk (W.hom ≫ H_Y.hom)) :
    IsIso (pullback.snd (familyAmbientMap i T) (hY.family (f ≫
      (Over.homMk W.hom (by rfl) : Over.mk (W.hom ≫ H_Y.hom) ⟶ H_Y))).ideal.subschemeι) := by
  let U := hY.family (𝟙 H_Y)
  let YH := (Over.pullback H_Y.hom).obj Y
  let k := familyAmbientMap i H_Y
  let p := U.ideal.subschemeι ≫ YH.hom
  let iD := pullback.snd k U.ideal.subschemeι
  let fY : T ⟶ H_Y := f ≫ Over.homMk W.hom (by rfl)
  let T_H : Over H_Y.left := Over.mk fY.left
  let g : T_H ⟶ W := Over.homMk f.left (by rfl)
  obtain ⟨e⟩ := hW
  have hp : IsIso ((Over.pullback T_H.hom).map
      (Over.homMk iD (by simp [p]) : Over.mk (iD ≫ p) ⟶ Over.mk p)).left :=
    (e.homEquiv g).down
  have hprop : universalFamilyRestrictionProperty i d hY fY := by
    simpa [universalFamilyRestrictionProperty, T_H, iD, p, U, YH, k] using hp
  exact (universalFamilyRestrictionProperty_iff i d hY fY).mp hprop

private theorem exists_factor_through_weilRestriction {S : Scheme.{u}}
    {X Y : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left] (d : ℕ)
    (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d) (W : Over H_Y.left)
    (hW : Nonempty ((Stacks.Flatness.weilRestrictionFunctor
      (universalFamilyInX i hY) (universalFamilyHom hY)).RepresentableBy W))
    {T : Over S} (fY : T ⟶ H_Y)
    (hIso : IsIso (pullback.snd (familyAmbientMap i T) (hY.family fY).ideal.subschemeι)) :
    ∃ fX : T ⟶ Over.mk (W.hom ≫ H_Y.hom),
      fX ≫ (Over.homMk W.hom (by rfl) : Over.mk (W.hom ≫ H_Y.hom) ⟶ H_Y) = fY := by
  let U := hY.family (𝟙 H_Y)
  let YH := (Over.pullback H_Y.hom).obj Y
  let k := familyAmbientMap i H_Y
  let p := U.ideal.subschemeι ≫ YH.hom
  let iD := pullback.snd k U.ideal.subschemeι
  let T_H : Over H_Y.left := Over.mk fY.left
  have hweil : IsIso ((Over.pullback T_H.hom).map
      (Over.homMk iD (by simp [p]) : Over.mk (iD ≫ p) ⟶ Over.mk p)).left := by
    simpa [universalFamilyRestrictionProperty, T_H, iD, p, U, YH, k] using
      (universalFamilyRestrictionProperty_iff i d hY fY).mpr hIso
  obtain ⟨e⟩ := hW
  obtain ⟨g, -⟩ := (e.homEquiv (X := T_H)).surjective (PLift.up hweil)
  refine ⟨Over.homMk g.left ?_, Over.OverMorphism.ext g.w⟩
  calc
    g.left ≫ (W.hom ≫ H_Y.hom) = (g.left ≫ W.hom) ≫ H_Y.hom := by simp
    _ = fY.left ≫ H_Y.hom := by simp [T_H]
    _ = T.hom := fY.w

/-- **Stacks Project, Tag 0B97.** Let `i : X ⟶ Y` be a closed immersion of schemes over `S`.
If the degree-`d` Hilbert functor of `Y` is represented by a scheme `H_Y` over `S`, then the
degree-`d` Hilbert functor of `X` is represented by a scheme `H_X` over `S` together with a
closed immersion `H_X ⟶ H_Y` over which the universal families correspond. -/
@[stacks 0B97 "if the degree-d Hilbert functor of Y is representable by a scheme, so is that of \
X, by a closed subscheme of it, compatibly with the universal families"]
public theorem exists_closedSubschemeRepresentingHilbertFunctor {S : Scheme.{u}}
    {X Y : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left] (d : ℕ)
    (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d) :
    Nonempty (ClosedSubschemeRepresentingHilbertFunctor i d H_Y hY) := by
  classical
  obtain ⟨W, hWclosed, hW⟩ := exists_universal_family_weil_restriction i d H_Y hY
  let : IsClosedImmersion W.hom := hWclosed
  let H_X := Over.mk (W.hom ≫ H_Y.hom)
  let inclusion : H_X ⟶ H_Y := Over.homMk W.hom (by rfl)
  have hIso_of_map {T : Over S} (f : T ⟶ H_X) :
      IsIso (pullback.snd (familyAmbientMap i T)
        (hY.family (f ≫ inclusion)).ideal.subschemeι) :=
    isIso_of_factors_through_weilRestriction i d H_Y hY W hW f
  let familyX : ∀ {T : Over S}, (T ⟶ H_X) → HilbertFamily X T d :=
    fun {T} f => by
      let : IsClosedImmersion (familyAmbientMap i T) := familyAmbientMap_isClosedImmersion i T
      let F := hY.family (f ≫ inclusion)
      exact ⟨F.ideal.comap (familyAmbientMap i T),
        comap_preserves_rank_of_pullback_snd_isIso _ _ _ (familyAmbientMap_comp_hom i T)
          F.ideal (hIso_of_map f) d F.isFiniteLocallyFreeOfRank⟩
  have familyX_ideal {T : Over S} (f : T ⟶ H_X) :
      (familyX f).ideal =
        (hY.family (f ≫ inclusion)).ideal.comap (familyAmbientMap i T) := rfl
  refine ⟨{
    H_X := H_X
    represents := ?_
    inclusion := inclusion
    isClosedImmersion := hWclosed
    family_ideal := ?_
  }⟩
  · let : IsClosedImmersion inclusion.left := hWclosed
    refine {
      family := ?_
      naturality := ?_ }
    · intro T
      let kT := familyAmbientMap i T
      let : IsClosedImmersion kT := familyAmbientMap_isClosedImmersion i T
      refine Equiv.ofBijective (familyX (T := T)) ⟨fun f g hfg => ?_, fun F => ?_⟩
      · refine (cancel_mono inclusion).1
          (Equiv.injective (hY.family (T := T)) (HilbertFamily.ext ?_))
        calc
          (hY.family (f ≫ inclusion)).ideal = (familyX f).ideal.map kT :=
            (map_comap_eq_of_pullback_snd_isIso kT _ (hIso_of_map f)).symm
          _ = (familyX g).ideal.map kT := by rw [hfg]
          _ = (hY.family (g ≫ inclusion)).ideal :=
            map_comap_eq_of_pullback_snd_isIso kT _ (hIso_of_map g)
      · let FY : HilbertFamily Y T d := ⟨F.ideal.map kT,
          map_preserves_rank kT F.ideal _ _ (familyAmbientMap_comp_hom i T) d
            F.isFiniteLocallyFreeOfRank⟩
        have hFY : hY.family ((hY.family).symm FY) = FY := (hY.family).apply_symm_apply FY
        obtain ⟨fX, hcomp⟩ := exists_factor_through_weilRestriction i d H_Y hY W hW
          ((hY.family).symm FY) (by rw [hFY]; exact pullback_snd_isIso_of_map kT F.ideal)
        have hcomp' : fX ≫ inclusion = (hY.family).symm FY := hcomp
        refine ⟨fX, HilbertFamily.ext ?_⟩
        change (hY.family (fX ≫ inclusion)).ideal.comap kT = F.ideal
        rw [hcomp', hFY]
        exact comap_map_eq_of_closedImmersion kT F.ideal
    · intro T' T g f
      change (familyX (g ≫ f)).ideal = (familyX f).ideal.comap (familyBaseChangeMap X g)
      rw [familyX_ideal, familyX_ideal]
      rw [show (g ≫ f) ≫ inclusion = g ≫ (f ≫ inclusion) from by simp [Category.assoc]]
      rw [hY.naturality g (f ≫ inclusion)]
      exact (ideal_comap_baseChange_naturality i g (hY.family (f ≫ inclusion)).ideal).symm
  · intro T f
    let kT := familyAmbientMap i T
    let : IsClosedImmersion kT := familyAmbientMap_isClosedImmersion i T
    exact (map_comap_eq_of_pullback_snd_isIso kT
      (hY.family (f ≫ inclusion)).ideal (hIso_of_map f)).symm

end Stacks.Hilbert

end
