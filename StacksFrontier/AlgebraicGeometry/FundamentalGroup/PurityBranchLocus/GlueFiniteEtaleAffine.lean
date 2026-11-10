module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction

/-!
# Glueing extensions of a finite étale cover over the affine opens

Let `U ⊆ X` be an open subscheme and `E` a finite étale cover of `U`. Suppose that for every
affine open `A ⊆ X` the restriction of `E` to `U ∩ A` extends to a finite étale cover of `A`, and
that restriction of finite étale covers from `A` to `U ∩ A` is fully faithful. Then `E` extends to
a finite étale cover of `X`.

Full faithfulness makes the local extensions unique up to unique isomorphism, so that for
affine opens `A ⊆ A'` the extension over `A'` restricts to the one over `A`, compatibly with
composition. The local extensions therefore form a relative glueing datum over the directed
cover of `X` by its affine opens ([Stacks, Tag 01LH], `Scheme.Cover.RelativeGluingData`), whose
glued scheme is finite étale over `X`, both properties being local on the target, and restricts
to `E` over `U`.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_extension_of_affine_extensions`: the glueing statement
  above.

## Implementation notes

The cover of `X` is `X.directedAffineCover`, whose members are the affine opens of `X` as open
subschemes and whose transition morphisms are the inclusions. The open `U` is covered by the
opens `U ⊓ A` and the cover `E` by the fibre products `E ×_U (U ⊓ A)`; the latter cover is
locally directed with the base changes of the inclusions as transition morphisms, which lets the
comparison morphism from `E` to the glued scheme be glued from its restrictions.
Both covers are reducible definitions built directly rather than as pulled back covers
`𝒰.pullback₁ f`: their index type is then literally `X.affineOpens` and their members literally
the opens `U ⊓ A` and the fibre products along their inclusions, which is the form in which the
hypotheses are stated.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Lemma 58.31.2 (0H2W)](https://stacks.math.columbia.edu/tag/0H2W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Morphisms between finite étale covers agree as soon as they agree after a faithful base
change. -/
private lemma finiteEtale_hom_ext_of_faithful {V T Z : Scheme.{u}} (j : T ⟶ V)
    [(finiteEtaleBaseChange j).Faithful]
    (A : FiniteEtaleOver V) (g : Z ⟶ V) [IsFinite g] [Etale g]
    (a b : A.left ⟶ Z) (ha : a ≫ g = A.hom) (hb : b ≫ g = A.hom)
    (hab : pullback.fst A.hom j ≫ a = pullback.fst A.hom j ≫ b) : a = b := by
  let B : FiniteEtaleOver V := MorphismProperty.Over.mk _ g ⟨inferInstance, inferInstance⟩
  let a' : A ⟶ B := MorphismProperty.Over.homMk a ha trivial
  let b' : A ⟶ B := MorphismProperty.Over.homMk b hb trivial
  exact congrArg (·.left) (show a' = b' from
    (finiteEtaleBaseChange j).map_injective (finiteEtaleOver_hom_ext j (by
      rwa [finiteEtaleBaseChangeProj_naturality, finiteEtaleBaseChangeProj_naturality])))

/-- Two morphisms from a finite étale cover of `V` to one of `W` lying over the same morphism
`V ⟶ W` agree once they agree on the part of the source over `T`, provided base change along
`T ⟶ V` is faithful. -/
private lemma finiteEtale_map_ext_of_faithful {V W T D : Scheme.{u}} (j : T ⟶ V)
    [(finiteEtaleBaseChange j).Faithful]
    (A : FiniteEtaleOver V) (B : FiniteEtaleOver W)
    (k : V ⟶ W) (a : D ⟶ A.left) (s : D ⟶ T)
    (ha : IsPullback a s A.hom j)
    (f g : A.left ⟶ B.left) (hf : f ≫ B.hom = A.hom ≫ k)
    (hg : g ≫ B.hom = A.hom ≫ k) (hfg : a ≫ f = a ≫ g) : f = g := by
  have : IsFinite B.hom := B.prop.1
  have : Etale B.hom := B.prop.2
  simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst B.hom k)
    (finiteEtale_hom_ext_of_faithful j A (pullback.snd B.hom k)
      (pullback.lift f A.hom hf) (pullback.lift g A.hom hg)
      (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (by
        apply (cancel_epi ha.isoPullback.hom).mp
        apply pullback.hom_ext
        · rwa [Category.assoc, Category.assoc, pullback.lift_fst, Category.assoc,
            Category.assoc, pullback.lift_fst, ha.isoPullback_hom_fst_assoc,
            ha.isoPullback_hom_fst_assoc]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.assoc,
            Category.assoc, pullback.lift_snd]))

/-- If base change along `T ⟶ V` is fully faithful, a finite étale cover `A` of `V` maps to the
base change of a finite étale cover `B` of `W` along `V ⟶ W` as soon as their parts over `T` are
identified. -/
private lemma exists_finiteEtale_map_of_fullyFaithful {V W T D : Scheme.{u}} (j : T ⟶ V)
    (H : (finiteEtaleBaseChange j).FullyFaithful)
    (A : FiniteEtaleOver V) (B : FiniteEtaleOver W)
    (k : V ⟶ W) (a : D ⟶ A.left) (s : D ⟶ T) (b : D ⟶ B.left)
    (ha : IsPullback a s A.hom j)
    (hb : IsPullback b s B.hom (j ≫ k)) :
    ∃ f : A.left ⟶ B.left, IsPullback f A.hom B.hom k ∧ a ≫ f = b := by
  have : IsFinite B.hom := B.prop.1
  have : Etale B.hom := B.prop.2
  let F : FiniteEtaleOver V :=
    MorphismProperty.Over.mk ⊤ (pullback.snd B.hom k) ⟨inferInstance, inferInstance⟩
  let p : D ≅ pullback (pullback.snd B.hom k) j :=
    hb.isoPullback ≪≫ (pullbackLeftPullbackSndIso B.hom k j).symm
  have hp : p.hom ≫ pullback.snd (pullback.snd B.hom k) j = s := by
    change (hb.isoPullback.hom ≫ (pullbackLeftPullbackSndIso B.hom k j).inv) ≫ _ = s
    rw [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hb.isoPullback_hom_snd]
  have hp' : p.hom ≫ pullback.fst (pullback.snd B.hom k) j ≫ pullback.fst B.hom k = b := by
    change (hb.isoPullback.hom ≫ (pullbackLeftPullbackSndIso B.hom k j).inv) ≫ _ = b
    rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, hb.isoPullback_hom_fst]
  let e : (finiteEtaleBaseChange j).obj A ≅ (finiteEtaleBaseChange j).obj F :=
    MorphismProperty.Over.isoMk (ha.isoPullback.symm ≪≫ p) (by
      change (ha.isoPullback.inv ≫ p.hom) ≫ pullback.snd (pullback.snd B.hom k) j =
        pullback.snd A.hom j
      rw [Category.assoc, hp, ha.isoPullback_inv_snd])
  let e' := H.preimageIso e
  let v : A.left ⟶ pullback B.hom k := e'.hom.left
  let f : A.left ⟶ B.left := v ≫ pullback.fst B.hom k
  have hv : v ≫ pullback.snd B.hom k = A.hom := e'.hom.w
  have hf : f ≫ B.hom = A.hom ≫ k := by
    change (v ≫ pullback.fst B.hom k) ≫ B.hom = A.hom ≫ k
    rw [Category.assoc, pullback.condition, ← Category.assoc, hv]
  let eS : A.left ≅ pullback B.hom k :=
    (MorphismProperty.Over.forget finiteEtale ⊤ V ⋙ Over.forget V).mapIso e'
  refine ⟨f, IsPullback.of_iso_pullback ⟨hf⟩ eS rfl hv, ?_⟩
  have hnat : ((finiteEtaleBaseChange j).map e'.hom).left ≫ pullback.fst F.hom j =
      pullback.fst A.hom j ≫ e'.hom.left := finiteEtaleBaseChange_map_left_fst j e'.hom
  have he : (finiteEtaleBaseChange j).map e'.hom = e.hom := H.map_preimage e.hom
  rw [he] at hnat
  have hfst : pullback.fst A.hom j ≫ v = (ha.isoPullback.inv ≫ p.hom) ≫
      pullback.fst (pullback.snd B.hom k) j := hnat.symm
  calc a ≫ f = (ha.isoPullback.hom ≫ pullback.fst A.hom j) ≫ v ≫ pullback.fst B.hom k := by
        rw [ha.isoPullback_hom_fst]
    _ = ha.isoPullback.hom ≫ (pullback.fst A.hom j ≫ v) ≫ pullback.fst B.hom k := by
        simp only [Category.assoc]
    _ = b := by
        rw [hfst, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hp']

/-- The glued scheme of a relative glueing datum over a locally directed open cover is finite
étale over the base when every piece is. -/
private lemma finiteEtale_toBase_of_relativeGluingData {X : Scheme.{u}} {𝒰 : X.OpenCover}
    [Category 𝒰.I₀] [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (d : 𝒰.RelativeGluingData)
    (h : ∀ i, IsFinite (d.natTrans.app i) ∧ Etale (d.natTrans.app i)) :
    IsFinite d.toBase ∧ Etale d.toBase := by
  have hloc (i : 𝒰.I₀) :
      ∃ e : (d.functor.obj i) ≅ pullback d.toBase (𝒰.f i),
        e.hom ≫ pullback.snd d.toBase (𝒰.f i) = d.natTrans.app i :=
    ⟨(d.isPullback_natTrans_ι_toBase i).flip.isoPullback,
      (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd⟩
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  have : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  have key (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (hP : ∀ i, P (d.natTrans.app i)) : P d.toBase := by
    refine IsZariskiLocalAtTarget.of_openCover (P := P) 𝒰 fun i ↦ ?_
    change P (pullback.snd d.toBase (𝒰.f i))
    obtain ⟨e, he⟩ := hloc i
    rw [← MorphismProperty.cancel_left_of_respectsIso P e.hom _, he]
    exact hP i
  exact ⟨key @IsFinite fun i ↦ (h i).1, key @Etale fun i ↦ (h i).2⟩

section Covers

variable {X : Scheme.{u}}

/-- Every point of an open `U ⊆ X` lies in `U ⊓ A` for some affine open `A` of `X`. -/
private lemma exists_mem_inf_affineOpens (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ A : X.affineOpens, x ∈ U ⊓ A.1 := by
  obtain ⟨A, hA, hxA, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x)
  exact ⟨⟨A, hA⟩, hx, hxA⟩

variable (U : X.Opens) {Y : Scheme.{u}} (g : Y ⟶ U.toScheme)

/-- The open cover of `U` by its intersections `U ⊓ A` with the affine opens `A` of `X`. -/
private abbrev infAffineCover : U.toScheme.OpenCover where
  I₀ := X.affineOpens
  X A := (U ⊓ A.1).toScheme
  f A := X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)
  mem₀ := (Scheme.Cover.mkOfCovers X.affineOpens (fun A ↦ (U ⊓ A.1).toScheme)
    (fun A ↦ X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) (fun x ↦ by
      obtain ⟨A, hA⟩ := exists_mem_inf_affineOpens U x.1 x.2
      exact ⟨A, ⟨x.1, hA⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩)).mem₀

/-- A point of `Y` over `U` whose image lies in `U ⊓ A` comes from the restriction of `Y` to
`U ⊓ A`. -/
private lemma exists_preimage_infAffine (A : X.affineOpens) (x : Y) (hx : (g ≫ U.ι) x ∈ A.1) :
    ∃ z : ↑(pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U))),
      pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) z = x := by
  obtain ⟨w, hw⟩ : (g ≫ U.ι) x ∈ Set.range (Scheme.Opens.ι (U ⊓ A.1)) := by
    rw [Scheme.Opens.range_ι]
    exact ⟨(g x).2, hx⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g)
    (g := X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) x w (by
      apply U.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, hw])
  exact ⟨z, hz⟩

/-- The restrictions of `Y` to the opens `U ⊓ A` cover `Y`. -/
private lemma infAffine_covers (x : Y) :
    ∃ (A : X.affineOpens) (z : ↑(pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)))),
      pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) z = x := by
  obtain ⟨A, hA⟩ := exists_mem_inf_affineOpens U ((g ≫ U.ι) x) (g x).2
  exact ⟨A, exists_preimage_infAffine U g A x hA.2⟩

/-- The open cover of a scheme `Y` over `U` by its restrictions to the opens `U ⊓ A`, for `A` an
affine open of `X`. -/
private abbrev infAffineCoverPullback : Y.OpenCover where
  I₀ := X.affineOpens
  X A := pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U))
  f A := pullback.fst _ _
  mem₀ := (Scheme.Cover.mkOfCovers X.affineOpens
    (fun A ↦ pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)))
    (fun A ↦ pullback.fst _ _) (infAffine_covers U g)).mem₀

/-- The transition morphisms of `infAffineCoverPullback`: the restriction of `Y` to `U ⊓ A`
includes into its restriction to `U ⊓ A'` for `A ≤ A'`. -/
private def infAffineTrans {A A' : X.affineOpens} (h : A ≤ A') :
    pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) ⟶
      pullback g (X.homOfLE (inf_le_left : U ⊓ A'.1 ≤ U)) :=
  pullback.map _ _ _ _ (𝟙 _) (X.homOfLE (inf_le_inf_left U (show A.1 ≤ A'.1 from h))) (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)]
private lemma infAffineTrans_fst {A A' : X.affineOpens} (h : A ≤ A') :
    infAffineTrans U g h ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
private lemma infAffineTrans_snd {A A' : X.affineOpens} (h : A ≤ A') :
    infAffineTrans U g h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ X.homOfLE (inf_le_inf_left U (show A.1 ≤ A'.1 from h)) :=
  pullback.lift_snd _ _ _

private lemma infAffineTrans_refl (A : X.affineOpens) :
    infAffineTrans U g (le_refl A) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

private lemma infAffineTrans_trans {A A' A'' : X.affineOpens} (h : A ≤ A') (h' : A' ≤ A'') :
    infAffineTrans U g (h.trans h') = infAffineTrans U g h ≫ infAffineTrans U g h' := by
  apply pullback.hom_ext <;> simp

private lemma isPullback_infAffineTrans {A A' : X.affineOpens} (h : A ≤ A') :
    IsPullback (infAffineTrans U g h) (pullback.snd _ _) (pullback.snd _ _)
      (X.homOfLE (inf_le_inf_left U (show A.1 ≤ A'.1 from h))) := by
  have hOuter : IsPullback (infAffineTrans U g h ≫ pullback.fst _ _) (pullback.snd _ _) g
      (X.homOfLE (inf_le_inf_left U (show A.1 ≤ A'.1 from h)) ≫
        X.homOfLE (inf_le_left : U ⊓ A'.1 ≤ U)) := by
    rw [infAffineTrans_fst, Scheme.homOfLE_homOfLE]
    exact IsPullback.of_hasPullback _ _
  exact hOuter.of_right (infAffineTrans_snd U g h) (IsPullback.of_hasPullback _ _)

private instance {A A' : X.affineOpens} (h : A ≤ A') : IsOpenImmersion (infAffineTrans U g h) := by
  have : IsOpenImmersion (infAffineTrans U g h ≫ pullback.fst _ _) := by
    rw [infAffineTrans_fst]
    infer_instance
  exact .of_comp _ (pullback.fst _ _)

/-- Any point in the overlap of the restrictions of `Y` to `U ⊓ A` and `U ⊓ A'` comes from the
restriction of `Y` to `U ⊓ A''` for some affine open `A'' ≤ A, A'`. -/
private lemma infAffineTrans_directed {A A' : X.affineOpens}
    (x : ↑(pullback (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)))
      (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A'.1 ≤ U))))) :
    ∃ (A'' : X.affineOpens) (h : A'' ≤ A) (h' : A'' ≤ A')
      (y : ↑(pullback g (X.homOfLE (inf_le_left : U ⊓ A''.1 ≤ U)))),
      pullback.lift (infAffineTrans U g h) (infAffineTrans U g h') (by simp) y = x := by
  let p := pullback.fst (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)))
      (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A'.1 ≤ U)))
  let q := pullback.snd (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)))
      (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A'.1 ≤ U)))
  let e : Y := pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) (p x)
  have he : e = pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A'.1 ≤ U)) (q x) := by
    simp only [e, p, q, ← Scheme.Hom.comp_apply, pullback.condition]
  have hmem {B : X.affineOpens}
      (z : ↑(pullback g (X.homOfLE (inf_le_left : U ⊓ B.1 ≤ U))))
      (hz : e = pullback.fst g (X.homOfLE (inf_le_left : U ⊓ B.1 ≤ U)) z) :
      (g ≫ U.ι) e ∈ B.1 := by
    rw [hz, ← Scheme.Hom.comp_apply, pullback.condition_assoc, Scheme.homOfLE_ι]
    exact (pullback.snd g (X.homOfLE (inf_le_left : U ⊓ B.1 ≤ U)) z).2.2
  obtain ⟨K, hK, hxK, hKle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show (g ≫ U.ι) e ∈ A.1 ⊓ A'.1 from ⟨hmem (p x) rfl, hmem (q x) he⟩)
  obtain ⟨y, hy⟩ := exists_preimage_infAffine U g ⟨K, hK⟩ e hxK
  refine ⟨⟨K, hK⟩, hKle.trans inf_le_left, hKle.trans inf_le_right, y, ?_⟩
  apply (p ≫ pullback.fst g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U))).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, infAffineTrans_fst, hy,
    Scheme.Hom.comp_apply]

private instance : (infAffineCoverPullback U g).LocallyDirected where
  trans h := infAffineTrans U g (leOfHom h)
  trans_id A := infAffineTrans_refl U g A
  trans_comp h h' := infAffineTrans_trans U g (leOfHom h) (leOfHom h')
  w h := infAffineTrans_fst U g (leOfHom h)
  directed x := by
    obtain ⟨A'', h, h', y, hy⟩ := infAffineTrans_directed U g x
    exact ⟨A'', homOfLE h, homOfLE h', y, hy⟩
  property_trans h := inferInstanceAs (IsOpenImmersion (infAffineTrans U g (leOfHom h)))

end Covers

/-- The glued scheme of a relative glueing datum `d` over the affine opens of `X` restricts to a
scheme `Y` over `U`, as soon as the restrictions of `Y` to the opens `U ⊓ A` are identified with
the restrictions of the pieces of `d`, compatibly with the transition morphisms. -/
private lemma exists_isPullback_of_relativeGluingData {X : Scheme.{u}} (U : X.Opens)
    {Y : Scheme.{u}} (g : Y ⟶ U.toScheme) (d : X.directedAffineCover.RelativeGluingData)
    (hd : ∀ i, IsFinite (d.natTrans.app i) ∧ Etale (d.natTrans.app i))
    (a : ∀ A : X.affineOpens,
      pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) ⟶ d.functor.obj A)
    (ha : ∀ A : X.affineOpens, IsPullback (a A) (pullback.snd _ _) (d.natTrans.app A)
      (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1)))
    (hc : ∀ (A A' : X.affineOpens) (h : A ≤ A'),
      a A ≫ d.functor.map (homOfLE h) = infAffineTrans U g h ≫ a A') :
    ∃ (Z : Scheme.{u}) (t : Z ⟶ X) (v : Y ⟶ Z), (IsFinite t ∧ Etale t) ∧
      IsPullback g v U.ι t := by
  have hcompat {i l : (infAffineCoverPullback U g).I₀} (h : i ⟶ l) :
      (infAffineCoverPullback U g).trans h ≫ (a l ≫ d.cover.f l) =
        a i ≫ d.cover.f i := by
    change infAffineTrans U g (leOfHom h) ≫ (a l ≫ d.cover.f l) = _
    calc infAffineTrans U g (leOfHom h) ≫ (a l ≫ d.cover.f l)
        = (infAffineTrans U g (leOfHom h) ≫ a l) ≫ d.cover.f l := (Category.assoc _ _ _).symm
      _ = (a i ≫ d.functor.map (homOfLE (leOfHom h))) ≫ d.cover.f l :=
          congrArg (fun v ↦ v ≫ d.cover.f l) (hc i l (leOfHom h)).symm
      _ = a i ≫ (d.functor.map (homOfLE (leOfHom h)) ≫ d.cover.f l) := Category.assoc _ _ _
      _ = a i ≫ d.cover.f i := congrArg (fun v ↦ a i ≫ v) (d.cover.trans_map h)
  let v : Y ⟶ d.glued := (infAffineCoverPullback U g).glueMorphismsOfLocallyDirected
    (fun i ↦ a i ≫ d.cover.f i) hcompat
  have hv (i : X.affineOpens) :
      pullback.fst g (X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U)) ≫ v =
        a i ≫ d.cover.f i :=
    (infAffineCoverPullback U g).map_glueMorphismsOfLocallyDirected _ _ i
  refine ⟨d.glued, d.toBase, v, finiteEtale_toBase_of_relativeGluingData d hd, ?_⟩
  apply Scheme.isPullback_of_openCover g v U.ι d.toBase (infAffineCover U)
  intro i
  change IsPullback (pullback.snd g (X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U)))
    (pullback.fst g (X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U)) ≫ v)
    (X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U) ≫ U.ι) d.toBase
  rw [hv i, show X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U) ≫ U.ι =
      X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1) ≫ i.1.ι by
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]]
  exact (ha i).flip.paste_vert (d.isPullback_natTrans_ι_toBase i)

/-- The glueing step, for a scheme `Y` over `U` together with extensions `F A` over the affine
opens `A` of `X` of its restrictions to `U ⊓ A`: if base change from `A` to `U ⊓ A` is fully
faithful, then `Y` is the restriction to `U` of a finite étale scheme over `X`. -/
private lemma exists_isPullback_of_affine_extensions {X : Scheme.{u}} (U : X.Opens)
    {Y : Scheme.{u}} (g : Y ⟶ U.toScheme)
    (F : ∀ A : X.affineOpens, FiniteEtaleOver A.1.toScheme)
    (a : ∀ A : X.affineOpens, pullback g (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U)) ⟶ (F A).left)
    (ha : ∀ A : X.affineOpens, IsPullback (a A) (pullback.snd _ _) (F A).hom
      (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1)))
    (hFF : ∀ A : X.affineOpens, Nonempty
      (finiteEtaleBaseChange (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1))).FullyFaithful) :
    ∃ (Z : Scheme.{u}) (t : Z ⟶ X) (v : Y ⟶ Z), (IsFinite t ∧ Etale t) ∧
      IsPullback g v U.ι t := by
  have hfaith (i : X.affineOpens) :
      (finiteEtaleBaseChange (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1))).Faithful :=
    (Classical.choice (hFF i)).faithful
  have hex (i l : X.affineOpens) (h : i ≤ l) :
      ∃ m : (F i).left ⟶ (F l).left,
        IsPullback m (F i).hom (F l).hom (X.homOfLE (show i.1 ≤ l.1 from h)) ∧
          a i ≫ m = infAffineTrans U g h ≫ a l := by
    apply exists_finiteEtale_map_of_fullyFaithful (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1))
      (Classical.choice (hFF i)) (F i) (F l) (X.homOfLE (show i.1 ≤ l.1 from h)) (a i)
      (pullback.snd _ _) (infAffineTrans U g h ≫ a l) (ha i)
    have ht : X.homOfLE (inf_le_inf_left U (show i.1 ≤ l.1 from h)) ≫
        X.homOfLE (inf_le_right : U ⊓ l.1 ≤ l.1) =
        X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1) ≫ X.homOfLE (show i.1 ≤ l.1 from h) := by
      rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]
    rw [← ht]
    exact (isPullback_infAffineTrans U g h).paste_horiz (ha l)
  choose m hm hc using hex
  have hid (i : X.affineOpens) : m i i le_rfl = 𝟙 _ := by
    have := hfaith i
    refine finiteEtale_map_ext_of_faithful (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1))
      (F i) (F i) (X.homOfLE (le_refl i.1)) (a i) (pullback.snd _ _) (ha i) _ _
      (hm i i _).w ?_ ?_
    · rw [Scheme.homOfLE_rfl, Category.id_comp]
      exact (Category.comp_id (F i).hom).symm
    · rw [hc i i _, infAffineTrans_refl, Category.id_comp, Category.comp_id]
  have hcomp (i l n : X.affineOpens) (h : i ≤ l) (k : l ≤ n) :
      m i n (h.trans k) = m i l h ≫ m l n k := by
    have := hfaith i
    refine finiteEtale_map_ext_of_faithful (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1))
      (F i) (F n) (X.homOfLE (show i.1 ≤ n.1 from h.trans k)) (a i) (pullback.snd _ _) (ha i)
      _ _ (hm i n _).w ?_ ?_
    · rw [Category.assoc, (hm l n _).w, ← Category.assoc, (hm i l _).w, Category.assoc,
        Scheme.homOfLE_homOfLE]
    · rw [hc i n _, infAffineTrans_trans U g h k, Category.assoc, ← hc l n _,
        ← Category.assoc, ← hc i l _, Category.assoc]
  let G : X.directedAffineCover.I₀ ⥤ Scheme.{u} :=
    { obj i := (F i).left
      map {i l} h := m i l (leOfHom h)
      map_id i := hid i
      map_comp {i l n} h k := hcomp i l n (leOfHom h) (leOfHom k) }
  exact exists_isPullback_of_relativeGluingData U g
    { functor := G
      natTrans :=
        { app i := (F i).hom
          naturality {i l} h := (hm i l (leOfHom h)).w }
      equifibered {i l} h := hm i l (leOfHom h) }
    (fun i ↦ (F i).prop) a ha hc

/-- **Glueing local extensions of a finite étale cover.** Let `U ⊆ X` be open and `E` a finite
étale cover of `U`. If for every affine open `A ⊆ X` the restriction of `E` to `U ∩ A` extends to
a finite étale cover of `A`, and base change of finite étale covers from `A` to `U ∩ A` is fully
faithful, then `E` extends to a finite étale cover of `X`. -/
theorem exists_finiteEtale_extension_of_affine_extensions {X : Scheme.{u}} (U : X.Opens)
    (E : FiniteEtaleOver U.toScheme)
    (hExt : ∀ A : X.affineOpens, ∃ F : FiniteEtaleOver (A : X.Opens).toScheme,
      Nonempty ((finiteEtaleBaseChange (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1))).obj F ≅
        (finiteEtaleBaseChange (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U))).obj E))
    (hFF : ∀ A : X.affineOpens, Nonempty
      (finiteEtaleBaseChange (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1))).FullyFaithful) :
    ∃ F : FiniteEtaleOver X, Nonempty ((finiteEtaleBaseChange U.ι).obj F ≅ E) := by
  choose F hF using hExt
  let e (i : X.affineOpens) := Classical.choice (hF i)
  have ha (i : X.affineOpens) : IsPullback
      ((e i).inv.left ≫ pullback.fst (F i).hom (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1)))
      (pullback.snd E.hom (X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U))) (F i).hom
      (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1)) := by
    let ei := (MorphismProperty.Over.forget finiteEtale ⊤ (U ⊓ i.1).toScheme ⋙
      Over.forget _).mapIso (e i).symm
    have hei : ei.hom ≫ pullback.snd (F i).hom (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1)) =
        pullback.snd E.hom (X.homOfLE (inf_le_left : U ⊓ i.1 ≤ U)) := (e i).inv.w
    apply IsPullback.of_iso_pullback _ ei rfl hei
    constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1)) hei
  obtain ⟨Z, t, v, ht, hpb⟩ := exists_isPullback_of_affine_extensions U E.hom F
    (fun i ↦ (e i).inv.left ≫ pullback.fst (F i).hom (X.homOfLE (inf_le_right : U ⊓ i.1 ≤ i.1)))
    ha hFF
  exact ⟨MorphismProperty.Over.mk _ t ht, ⟨MorphismProperty.Over.isoMk hpb.flip.isoPullback.symm
    hpb.flip.isoPullback_inv_snd⟩⟩

end AlgebraicGeometry

end
