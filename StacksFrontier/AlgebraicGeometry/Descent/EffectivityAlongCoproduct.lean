module

public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumAlongRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.FamilyCoproduct
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal

/-!
# Effectivity of a descent datum and of the datum for the morphism out of the coproduct

Let `f i : X i ⟶ S` be a family of morphisms of schemes with fixed target. Descent data for
the family are equivalent to descent data for the single morphism `∐ X i ⟶ S`, and under that
equivalence the canonical descent datum of a scheme over `S` relative to the family goes to the
canonical descent datum of the same scheme relative to the single morphism. Consequently a
descent datum for the family is effective as soon as the corresponding datum for the single
morphism is.

## Main definitions

* `AlgebraicGeometry.DescentData.canonicalCoproductIso`: the canonical descent datum of a
  scheme over `S` relative to the family corresponds to the canonical descent datum of that
  scheme relative to the morphism out of the coproduct.

## Main results

* `AlgebraicGeometry.isPullback_sigmaDesc_sigmaMap`: a scheme over `S` based changed to the
  coproduct `∐ X i` is the coproduct of its base changes to the members.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_coproduct`: a descent datum for a family
  is effective as soon as the corresponding datum for the morphism out of the coproduct is.

## References

* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : I → Scheme.{u}}

/-- **A scheme over `S` base changed to a coproduct is the coproduct of its base changes.** For
a family `f i : X i ⟶ S` and a scheme `W` over `S`, the fibre product `W ×_S ∐ X i` is the
coproduct of the fibre products `W ×_S X i`. -/
theorem isPullback_sigmaDesc_sigmaMap (f : ∀ i, X i ⟶ S) (W : Over S) :
    IsPullback (Sigma.desc (fun i ↦ pullback.fst W.hom (f i)))
      (Limits.Sigma.map (fun i ↦ pullback.snd W.hom (f i))) W.hom (Sigma.desc f) :=
  (isUniversalColimit_sigmaCofan X).isPullback_of_isColimit_left f (Sigma.desc f) W.hom
    (fun i ↦ pullback.fst W.hom (f i)) (fun i ↦ pullback.snd W.hom (f i))
    (fun i ↦ IsPullback.of_hasPullback W.hom (f i)) (coproductIsCoproduct _)

/-- A binary product of two coproducts of schemes over a base is the coproduct of the pairwise
binary products. -/
private def isColimitCofanProdOver {J : Type v} [Small.{u} J]
    {A : I → Over S} {B : J → Over S} {c : Cofan A} {d : Cofan B}
    (hc : IsColimit c) (hd : IsColimit d) :
    IsColimit (Cofan.mk (c.pt ⨯ d.pt) (fun p : I × J ↦ prod.map (c.inj p.1) (d.inj p.2))) :=
  Nonempty.some <|
    (isUniversalColimit_of_isColimit_cofanOver hc).nonempty_isColimit_prod_of_isPullback
      (isUniversalColimit_of_isColimit_cofanOver hd) (fun i ↦ terminal.from (A i))
      (fun j ↦ terminal.from (B j)) (terminal.from c.pt) (terminal.from d.pt)
      (fun i j ↦ IsPullback.of_hasBinaryProduct' (A i) (B j))
      (IsPullback.of_hasBinaryProduct' c.pt d.pt) (Iso.refl _)

namespace DescentData

variable {f : ∀ i, X i ⟶ S}

/-- The inclusion of the member at `i` of a descent datum, pushed forward to `S`, into the
member of the corresponding datum for the morphism out of the coproduct. -/
private def coproductInclusion (c : FamilyCoproductEquivalence f) (D : DescentData f) (i : I) :
    (Over.map (f i)).obj (D.obj i) ⟶
      (Over.map (Sigma.desc f)).obj ((c.equivalence.functor.obj D).obj ()) :=
  Over.homMk (Sigma.ι (fun i ↦ (D.obj i).left) i ≫ (c.objIso D).inv.left) (by
    change (Sigma.ι _ i ≫ (c.objIso D).inv.left) ≫
      (((c.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f) = _
    rw [Category.assoc, ← Category.assoc (c.objIso D).inv.left, Over.w]
    simp)

/-- The inclusion of the member at `j` of the family, over `S`, into the coproduct. -/
private def sigmaInclusionOver (f : ∀ i, X i ⟶ S) (j : I) :
    Over.mk (f j) ⟶ Over.mk (Sigma.desc f) :=
  Over.homMk (Sigma.ι X j) (by simp)

/-- The sources of the gluing isomorphisms of a descent datum, pushed forward to `S`, are the
legs of a colimit cofan on the source of the gluing isomorphism of the corresponding datum for
the morphism out of the coproduct. -/
private def isColimitCofanCoproductSource (c : FamilyCoproductEquivalence f)
    (D : DescentData f) :
    IsColimit (Cofan.mk
      ((Over.map (Sigma.desc f)).obj ((c.equivalence.functor.obj D).obj ()) ⨯
        Over.mk (Sigma.desc f))
      (fun p : I × I ↦ prod.map (coproductInclusion c D p.1)
        (sigmaInclusionOver f p.2))) := by
  refine isColimitCofanProdOver (c := Cofan.mk _ (coproductInclusion c D))
    (d := Cofan.mk (Over.mk (Sigma.desc f)) (sigmaInclusionOver f)) ?_ ?_
  · refine isColimitCofanOfIsColimitLeft _ ?_
    refine IsColimit.ofIsoColimit (coproductIsCoproduct (fun i ↦ (D.obj i).left)) ?_
    exact Cocone.ext ((Over.forget _).mapIso (c.objIso D).symm) (by intro i; rfl)
  · exact isColimitCofanOfIsColimitLeft _ (coproductIsCoproduct X)

/-- Two morphisms out of the source of the gluing isomorphism of the datum corresponding to `D`
for the morphism out of the coproduct agree as soon as they agree after composing with the
comparison map of every pair of members. -/
private lemma coproductSourceMap_hom_ext (c : FamilyCoproductEquivalence f)
    (D : DescentData f) {Z : Scheme.{u}}
    {a b : pullback (((c.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f)
      (Sigma.desc f) ⟶ Z}
    (h : ∀ i j, c.sourceMap D i j ≫ a = c.sourceMap D i j ≫ b) : a = b := by
  let E := c.equivalence.functor.obj D
  let e := Over.prodLeftIsoPullback ((Over.map (Sigma.desc f)).obj (E.obj ()))
    (Over.mk (Sigma.desc f))
  apply (cancel_epi e.hom).mp
  apply (isColimitOfPreserves (Over.forget S) (isColimitCofanCoproductSource c D)).hom_ext
  rintro ⟨i, j⟩
  let ei := Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))
  let inc := prod.map (coproductInclusion c D i) (sigmaInclusionOver f j)
  have he₁ : e.hom ≫ pullback.fst
      (((c.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f) (Sigma.desc f) =
      (prod.fst : (Over.map (Sigma.desc f)).obj (E.obj ()) ⨯ Over.mk (Sigma.desc f) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have he₂ : e.hom ≫ pullback.snd
      (((c.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f) (Sigma.desc f) =
      (prod.snd : (Over.map (Sigma.desc f)).obj (E.obj ()) ⨯ Over.mk (Sigma.desc f) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have hei₁ : ei.hom ≫ pullback.fst ((D.obj i).hom ≫ f i) (f j) =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have hei₂ : ei.hom ≫ pullback.snd ((D.obj i).hom ≫ f i) (f j) =
      (prod.snd : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have hi : inc.left ≫ e.hom = ei.hom ≫ c.sourceMap D i j := by
    apply pullback.hom_ext
      (f := ((c.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f)
      (g := Sigma.desc f)
    · rw [Category.assoc, he₁, Category.assoc, c.sourceMap_fst, ← Category.assoc, hei₁,
        ← Over.comp_left]
      simp only [inc, prod.map_fst, Over.comp_left, coproductInclusion, Over.homMk_left]
    · rw [Category.assoc, he₂, Category.assoc, c.sourceMap_snd, ← Category.assoc, hei₂,
        ← Over.comp_left]
      exact congrArg Over.Hom.left (prod.map_snd _ _)
  change inc.left ≫ e.hom ≫ a = inc.left ≫ e.hom ≫ b
  simp only [← Category.assoc, hi]
  simp only [Category.assoc, h]

/-- **The gluing isomorphism of the corresponding datum preserves a projection assembled from
the members.** If a family of morphisms out of the members of `D` to a scheme `U` is preserved
by the gluing isomorphisms of `D` and assembles to a morphism out of the member of the
corresponding datum for the morphism out of the coproduct, then that morphism is preserved by
the gluing isomorphism of the corresponding datum. -/
private lemma coproduct_gluing_proj (c : FamilyCoproductEquivalence f)
    (D : DescentData f) {U : Scheme.{u}} (p : ∀ i, (D.obj i).left ⟶ U)
    (q : ((c.equivalence.functor.obj D).obj ()).left ⟶ U)
    (hq : ∀ i, Sigma.ι (fun i ↦ (D.obj i).left) i ≫ (c.objIso D).inv.left ≫ q = p i)
    (hp : ∀ i j, (D.gluingPullbackIso i j).hom ≫ pullback.snd _ _ ≫ p j =
      pullback.fst _ _ ≫ p i) :
    ((c.equivalence.functor.obj D).gluingPullbackIso () ()).hom ≫
        pullback.snd _ _ ≫ q = pullback.fst _ _ ≫ q := by
  apply coproductSourceMap_hom_ext c D
  intro i j
  rw [← Category.assoc, c.gluing, Category.assoc, ← Category.assoc (c.targetMap D i j),
    c.targetMap_snd, Category.assoc, Category.assoc, hq, hp, ← Category.assoc, c.sourceMap_fst,
    Category.assoc, Category.assoc, hq]

/-- The member of the datum corresponding to the canonical descent datum of `W`, identified with
the base change of `W` along the morphism out of the coproduct. -/
private def canonicalCoproductComponentIso (f : ∀ i, X i ⟶ S) (W : Over S) :
    ((familyCoproductEquivalence f).equivalence.functor.obj
        ((canonicalFamilyDescentFunctor f).functor.obj W)).obj () ≅
      (Over.pullback (Sigma.desc f)).obj W := by
  let C := (canonicalFamilyDescentFunctor f).functor.obj W
  let e (i : I) : C.obj i ≅ (Over.pullback (f i)).obj W :=
    eqToIso ((canonicalFamilyDescentFunctor f).obj W i)
  let a : Over.mk (Limits.Sigma.map (fun i ↦ (C.obj i).hom)) ≅
      Over.mk (Limits.Sigma.map (fun i ↦ pullback.snd W.hom (f i))) :=
    Over.isoMk (Sigma.mapIso (fun i ↦ (Over.forget (X i)).mapIso (e i))) (by
      apply Sigma.hom_ext
      intro i
      simp [Category.assoc, ← Over.w (e i).hom])
  exact (familyCoproductEquivalence f).objIso C ≪≫ a ≪≫
    Over.isoMk (isPullback_sigmaDesc_sigmaMap f W).isoPullback
      (isPullback_sigmaDesc_sigmaMap f W).isoPullback_hom_snd

/-- The identification of the member of the corresponding datum with the base change of `W`
assembles the projections to `W` of the members of the canonical descent datum. -/
private lemma canonicalCoproductComponentIso_proj (f : ∀ i, X i ⟶ S) (W : Over S) (i : I) :
    let c := familyCoproductEquivalence f
    let C := (canonicalFamilyDescentFunctor f).functor.obj W
    Sigma.ι (fun i ↦ (C.obj i).left) i ≫ (c.objIso C).inv.left ≫
        (canonicalCoproductComponentIso f W).hom.left ≫
          pullback.fst W.hom (Sigma.desc f) =
      (eqToHom ((canonicalFamilyDescentFunctor f).obj W i)).left ≫
        pullback.fst W.hom (f i) := by
  dsimp only
  simp only [canonicalCoproductComponentIso, Iso.trans_hom, Over.comp_left,
    Over.isoMk_hom_left, Category.assoc, IsPullback.isoPullback_hom_fst]
  simp only [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  simp only [Category.assoc]
  simp only [Over.mk_left, Category.id_comp, Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc]
  rfl

/-- **The canonical descent datum corresponds to the canonical descent datum.** Under the
equivalence between descent data for a family and descent data for the morphism out of its
coproduct, the canonical descent datum of a scheme over the base relative to the family
corresponds to the canonical descent datum of that scheme relative to the morphism out of the
coproduct. -/
@[no_expose]
def canonicalCoproductIso (f : ∀ i, X i ⟶ S) (W : Over S) :
    (familyCoproductEquivalence f).equivalence.functor.obj
        ((canonicalFamilyDescentFunctor f).functor.obj W) ≅
      (canonicalFamilyDescentFunctor (fun _ : Unit ↦ Sigma.desc f)).functor.obj W :=
  DescentData.isoCanonicalDatum _ W (fun _ ↦ canonicalCoproductComponentIso f W) (by
    rintro ⟨⟩ ⟨⟩
    exact coproduct_gluing_proj (familyCoproductEquivalence f)
      ((canonicalFamilyDescentFunctor f).functor.obj W)
      (fun i ↦ (eqToHom ((canonicalFamilyDescentFunctor f).obj W i)).left ≫
        pullback.fst W.hom (f i))
      ((canonicalCoproductComponentIso f W).hom.left ≫
        pullback.fst W.hom (Sigma.desc f))
      (canonicalCoproductComponentIso_proj f W)
      ((canonicalFamilyDescentFunctor f).gluing W))

/-- **A descent datum is effective as soon as the datum for the morphism out of the coproduct
is.** Let `f i : X i ⟶ S` be a family of morphisms of schemes with fixed target and let `D` be a
descent datum relative to it. If the descent datum relative to `∐ X i ⟶ S` corresponding to `D`
is effective, then so is `D`. -/
theorem isFamilyEffective_of_coproduct (f : ∀ i, X i ⟶ S) {D : DescentData f}
    (h : ((familyCoproductEquivalence f).equivalence.functor.obj D).IsFamilyEffective) :
    D.IsFamilyEffective := by
  have := (familyCoproductEquivalence f).equivalence.fullyFaithfulFunctor.full
  have := (familyCoproductEquivalence f).equivalence.fullyFaithfulFunctor.faithful
  obtain ⟨W, ⟨e⟩⟩ := h
  exact Functor.essImage_of_essImage_comp_obj (canonicalFamilyDescentFunctor f).functor
    (familyCoproductEquivalence f).equivalence.functor ⟨W, ⟨canonicalCoproductIso f W ≪≫ e⟩⟩

end DescentData

end AlgebraicGeometry

end

end
