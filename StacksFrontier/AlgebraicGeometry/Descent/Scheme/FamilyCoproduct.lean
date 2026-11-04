module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Products
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Products

/-!
# A family of morphisms of schemes as a single morphism

Let `f i : X i ⟶ S` be a family of morphisms of schemes. Descent data for this family are
canonically equivalent to descent data for the single morphism `(∐ i, X i) ⟶ S`, so nothing
is lost by treating a family as one morphism out of its disjoint union.

## Main definitions

* `AlgebraicGeometry.DescentData.FamilyCoproductEquivalence`: an equivalence between the two
  categories of descent data, together with its action on objects, gluing isomorphisms and
  morphisms.

## Main results

* `AlgebraicGeometry.DescentData.sigma_universal`: the coproduct of a small family of schemes is a
  universal colimit.
* `AlgebraicGeometry.DescentData.familyCoproductEquivalence`: the canonical equivalence between
  the two categories of descent data.

## Implementation notes

Descent data for a single morphism are represented by the singleton family indexed by
`Unit`. The specification identifies its object with the coproduct of the objects of the
family; its gluing map restricts on the `(i, j)`-summand to the original gluing map, and its
action on morphisms is the coproduct of the component maps.

## References

* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
-/

@[expose] public section

noncomputable section

universe u v w

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

variable {I : Type v} [Small.{u} I] (X : I → Scheme.{u})
/-- **Coproducts of schemes are universal colimits.** Alias of
`AlgebraicGeometry.isUniversalColimit_sigmaCofan`. -/
alias sigma_universal := AlgebraicGeometry.isUniversalColimit_sigmaCofan

private lemma scheme_cofan_universal {c : Cofan X} (hc : IsColimit c) :
    IsUniversalColimit c :=
  (sigma_universal X).of_iso ((coproductIsCoproduct X).uniqueUpToIso hc)

private alias scheme_discrete_universal :=
  AlgebraicGeometry.isUniversalColimit_of_isColimit_discrete

private alias over_cofan_universal :=
  AlgebraicGeometry.isUniversalColimit_of_isColimit_cofanOver

private def over_prod_cofan_isColimit {S : Scheme.{u}} {J : Type*}
    [Small.{u} J] {A : I → Over S} {B : J → Over S}
    {c : Cofan A} {d : Cofan B} (hc : IsColimit c) (hd : IsColimit d) :
    IsColimit (Cofan.mk (c.pt ⨯ d.pt) (fun p : I × J ↦ prod.map (c.inj p.1) (d.inj p.2))) := by
  apply Nonempty.some
  exact (over_cofan_universal hc).nonempty_isColimit_prod_of_isPullback
    (over_cofan_universal hd) (fun i ↦ terminal.from (A i))
    (fun j ↦ terminal.from (B j)) (terminal.from c.pt) (terminal.from d.pt)
    (fun i j ↦ IsPullback.of_hasBinaryProduct' (A i) (B j))
    (IsPullback.of_hasBinaryProduct' c.pt d.pt) (Iso.refl _)

variable {S : Scheme.{u}} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- The object over `∐ X` obtained as the coproduct of a family of objects `V i` over `X i`. -/
public abbrev totalObj (V : ∀ i, Over (X i)) : Over (∐ X) :=
  Over.mk (Limits.Sigma.map (fun i ↦ (V i).hom))
private abbrev baseι (i : I) : Over.mk (f i) ⟶ Over.mk (Sigma.desc f) :=
  Over.homMk (Sigma.ι X i) (by simp)
private instance mono_baseι (i : I) : Mono (baseι f i) := Over.mono_of_mono_left _
private abbrev totalι (V : ∀ i, Over (X i)) (i : I) :
    (Over.map (f i)).obj (V i) ⟶ (Over.map (Sigma.desc f)).obj (totalObj V) :=
  Over.homMk (Sigma.ι (fun i ↦ (V i).left) i) (by simp)
private abbrev baseCofan : Cofan (fun i ↦ Over.mk (f i)) :=
  Cofan.mk _ (baseι f)
private abbrev totalCofan (V : ∀ i, Over (X i)) :
    Cofan (fun i ↦ (Over.map (f i)).obj (V i)) := Cofan.mk _ (totalι f V)
private def baseCofanIsColimit : IsColimit (baseCofan f) :=
  AlgebraicGeometry.isColimitCofanOfIsColimitLeft _ (coproductIsCoproduct X)
private def totalCofanIsColimit (V : ∀ i, Over (X i)) : IsColimit (totalCofan f V) :=
  AlgebraicGeometry.isColimitCofanOfIsColimitLeft _
    (coproductIsCoproduct (fun i ↦ (V i).left))

private abbrev sourceCofan (V : ∀ i, Over (X i)) :=
  Cofan.mk ((Over.map (Sigma.desc f)).obj (totalObj V) ⨯ Over.mk (Sigma.desc f))
    (fun p : I × I ↦ prod.map (totalι f V p.1) (baseι f p.2))
private abbrev targetCofan (V : ∀ i, Over (X i)) :=
  Cofan.mk (Over.mk (Sigma.desc f) ⨯ (Over.map (Sigma.desc f)).obj (totalObj V))
    (fun p : I × I ↦ prod.map (baseι f p.1) (totalι f V p.2))
private def sourceCofanIsColimit (V : ∀ i, Over (X i)) : IsColimit (sourceCofan f V) :=
  over_prod_cofan_isColimit (totalCofanIsColimit f V) (baseCofanIsColimit f)
private def targetCofanIsColimit (V : ∀ i, Over (X i)) : IsColimit (targetCofan f V) :=
  over_prod_cofan_isColimit (baseCofanIsColimit f) (totalCofanIsColimit f V)

private def totalGluing (D : DescentData f) :
    (Over.map (Sigma.desc f)).obj (totalObj D.obj) ⨯ Over.mk (Sigma.desc f) ≅
    Over.mk (Sigma.desc f) ⨯ (Over.map (Sigma.desc f)).obj (totalObj D.obj) where
  hom := Cofan.IsColimit.desc (sourceCofanIsColimit f D.obj)
    (fun p : I × I ↦ (D.gluing p.1 p.2).hom.left ≫ (targetCofan f D.obj).inj p)
  inv := Cofan.IsColimit.desc (targetCofanIsColimit f D.obj)
    (fun p : I × I ↦ (D.gluing p.1 p.2).inv.left ≫ (sourceCofan f D.obj).inj p)
  hom_inv_id := by
    apply Cofan.IsColimit.hom_ext (sourceCofanIsColimit f D.obj)
    intro p
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.assoc, Cofan.IsColimit.fac,
      ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id]
    simp
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (targetCofanIsColimit f D.obj)
    intro p
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.assoc, Cofan.IsColimit.fac,
      ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
    simp

@[reassoc]
private lemma totalGluing_ι (D : DescentData f) (i j : I) :
    prod.map (totalι f D.obj i) (baseι f j) ≫ (totalGluing f D).hom =
    (D.gluing i j).hom.left ≫ prod.map (baseι f i) (totalι f D.obj j) :=
  Cofan.IsColimit.fac (sourceCofanIsColimit f D.obj) _ (i, j)

@[reassoc]
private lemma totalι_structure (V : ∀ i, Over (X i)) (i : I) :
    totalι f V i ≫ structureMap (Sigma.desc f) (totalObj V) =
      structureMap (f i) (V i) ≫ baseι f i := by
  ext
  simp

private def totalGluingOver (D : DescentData f) :
    Over.mk (prod.map (structureMap (Sigma.desc f) (totalObj D.obj))
      (𝟙 (Over.mk (Sigma.desc f)))) ≅
    Over.mk (prod.map (𝟙 (Over.mk (Sigma.desc f)))
      (structureMap (Sigma.desc f) (totalObj D.obj))) :=
  Over.isoMk (totalGluing f D) (by
    apply Cofan.IsColimit.hom_ext (sourceCofanIsColimit f D.obj)
    intro p
    dsimp only [sourceCofan, cofan_mk_inj, Over.mk_hom]
    rw [← Category.assoc, totalGluing_ι]
    apply prod.hom_ext
    · simp [Category.assoc, totalι_structure]
    · simp [Category.assoc, totalι_structure])

/-- Splitting `prod.map (f ≫ g) h` into a map on the first factor followed by `prod.map g h`. -/
private lemma prod_map_comp_left {C : Type*} [Category C] [HasBinaryProducts C]
    {A A' A'' B B' : C} (f : A ⟶ A') (g : A' ⟶ A'') (h : B ⟶ B') :
    prod.map (f ≫ g) h = prod.map f (𝟙 B) ≫ prod.map g h := by simp

private lemma totalGluing_cocycle (D : DescentData f) :
    prod.map (totalGluing f D).hom (𝟙 _) ≫ prodMapLastTwo (totalGluing f D).hom =
      prodMapFirstThird (totalGluing f D).hom := by
  apply Cofan.IsColimit.hom_ext
    (over_prod_cofan_isColimit (sourceCofanIsColimit f D.obj) (baseCofanIsColimit f))
  rintro ⟨⟨i, j⟩, k⟩
  dsimp only [cofan_mk_inj, sourceCofan, baseCofan]
  rw [← Category.assoc, prod.map_map, totalGluing_ι, Category.comp_id (baseι f k),
    prod_map_comp_left, Category.assoc,
    prodMapLastTwo_naturality (baseι f i) (totalι f D.obj j) (baseι f k) (baseι f j)
    (totalι f D.obj k) _ _ (totalGluing_ι f D j k), ← Category.assoc,
    D.cocycle]
  exact (prodMapFirstThird_naturality (totalι f D.obj i) (baseι f j) (baseι f k)
    (baseι f i) (totalι f D.obj k) _ _ (totalGluing_ι f D i k)).symm

@[reducible] private def totalDescentData (D : DescentData f) :
    DescentData (fun _ : Unit ↦ Sigma.desc f) where
  obj _ := totalObj D.obj
  gluing _ _ := totalGluingOver f D
  cocycle _ _ _ := totalGluing_cocycle f D

private def totalHom {V W : ∀ i, Over (X i)} (α : ∀ i, V i ⟶ W i) :
    totalObj V ⟶ totalObj W :=
  Over.homMk (Limits.Sigma.map (fun i ↦ (α i).left)) (Sigma.hom_ext _ _ fun i ↦ by simp)

@[reassoc]
private lemma totalHom_ι {V W : ∀ i, Over (X i)} (α : ∀ i, V i ⟶ W i) (i : I) :
    totalι f V i ≫ (Over.map (Sigma.desc f)).map (totalHom α) =
    (Over.map (f i)).map (α i) ≫ totalι f W i := by
  ext
  simp [totalHom]

private def totalMap {D E : DescentData f} (α : D ⟶ E) :
    totalDescentData f D ⟶ totalDescentData f E where
  hom _ := totalHom α.hom
  comm _ _ := by
    apply Cofan.IsColimit.hom_ext (sourceCofanIsColimit f D.obj)
    rintro ⟨i, j⟩
    change prod.map (totalι f D.obj i) (baseι f j) ≫
      prod.map ((Over.map (Sigma.desc f)).map (totalHom α.hom)) (𝟙 _) ≫
        (totalGluing f E).hom =
      prod.map (totalι f D.obj i) (baseι f j) ≫
        (totalGluing f D).hom ≫ prod.map (𝟙 _)
          ((Over.map (Sigma.desc f)).map (totalHom α.hom))
    rw [← Category.assoc, prod.map_map, totalHom_ι, Category.comp_id (baseι f j),
      prod_map_comp_left, Category.assoc, totalGluing_ι, ← Category.assoc, α.comm,
      totalGluing_ι_assoc]
    simp only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id, totalHom_ι]

/-- The underlying morphism of `totalMap` is the coproduct of the component morphisms. -/
private lemma totalMap_hom_left {D E : DescentData f} (α : D ⟶ E) :
    ((totalMap f α).hom ()).left = Limits.Sigma.map (fun i ↦ (α.hom i).left) := rfl

private def totalFunctor : DescentData f ⥤ DescentData (fun _ : Unit ↦ Sigma.desc f) where
  obj := totalDescentData f
  map := totalMap f
  map_id D := by
    apply DescentData.hom_ext
    intro i
    apply Over.OverMorphism.ext
    dsimp [totalMap, totalHom, totalDescentData]
    simp
  map_comp α β := by
    apply DescentData.hom_ext
    intro i
    apply Over.OverMorphism.ext
    dsimp [totalMap, totalHom, totalDescentData]
    apply Sigma.hom_ext
    intro i
    simp

/-- A coproduct of morphisms carries the `j`-th summand into the `j`-th summand. -/
private lemma sigmaMap_sigmaι_apply {Y : I → Scheme.{u}} (α : ∀ i, Y i ⟶ X i) (j : I)
    (z : Y j) : Limits.Sigma.map α (Sigma.ι Y j z) = Sigma.ι X j (α j z) := by
  rw [← Scheme.Hom.comp_apply, Sigma.ι_map, Scheme.Hom.comp_apply]

private lemma isPullback_sigmaι_sigmaMap {Y : I → Scheme.{u}}
    (α : ∀ i, Y i ⟶ X i) (i : I) :
    IsPullback (α i) (Sigma.ι Y i) (Sigma.ι X i) (Limits.Sigma.map α) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨j, z, rfl⟩ := (AlgebraicGeometry.sigmaOpenCover Y).exists_eq y
    change Sigma.ι X i x = Limits.Sigma.map α (Sigma.ι Y j z) at hx
    have heq : Sigma.ι X i x = Sigma.ι X j (α j z) :=
      hx.trans (sigmaMap_sigmaι_apply α j z)
    have hij : i = j :=
      congrArg Sigma.fst ((AlgebraicGeometry.sigmaι_eq_iff X i j x (α j z)).mp heq)
    subst j
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨α i z, by simp only [← Scheme.Hom.comp_apply, Sigma.ι_map]⟩

private def restrictTotalHom {V W : ∀ i, Over (X i)}
    (β : totalObj V ⟶ totalObj W) (i : I) : V i ⟶ W i :=
  Over.homMk ((isPullback_sigmaι_sigmaMap (fun i ↦ (W i).hom) i).lift
    (V i).hom (Sigma.ι (fun i ↦ (V i).left) i ≫ β.left) (by
      rw [Category.assoc, show β.left ≫ Limits.Sigma.map (fun i ↦ (W i).hom) =
        Limits.Sigma.map (fun i ↦ (V i).hom) from Over.w β]
      simp)) (by simp)

@[reassoc]
private lemma restrictTotalHom_ι {V W : ∀ i, Over (X i)}
    (β : totalObj V ⟶ totalObj W) (i : I) :
    (restrictTotalHom β i).left ≫ Sigma.ι (fun i ↦ (W i).left) i =
      Sigma.ι (fun i ↦ (V i).left) i ≫ β.left :=
  IsPullback.lift_snd _ _ _ _

private lemma totalHom_restrictTotalHom {V W : ∀ i, Over (X i)}
    (β : totalObj V ⟶ totalObj W) : totalHom (restrictTotalHom β) = β := by
  ext1
  apply Sigma.hom_ext
  intro i
  simpa [totalHom] using restrictTotalHom_ι β i

private lemma restrictTotalHom_totalHom {V W : ∀ i, Over (X i)}
    (α : ∀ i, V i ⟶ W i) (i : I) : restrictTotalHom (totalHom α) i = α i := by
  ext1
  apply (cancel_mono (Sigma.ι (fun i ↦ (W i).left) i)).mp
  simp [restrictTotalHom_ι, totalHom]

private def restrictMap {D E : DescentData f}
    (β : totalDescentData f D ⟶ totalDescentData f E) : D ⟶ E where
  hom := restrictTotalHom (β.hom ())
  comm i j := by
    have ht (k : I) : (Over.map (f k)).map (restrictTotalHom (β.hom ()) k) ≫
        totalι f E.obj k = totalι f D.obj k ≫ (Over.map (Sigma.desc f)).map (β.hom ()) := by
      ext1
      exact restrictTotalHom_ι (β.hom ()) k
    have hm : Mono (prod.map (baseι f i) (totalι f E.obj j)) := by
      have : Mono (totalι f E.obj j) := by apply Over.mono_of_mono_left
      infer_instance
    apply (cancel_mono (prod.map (baseι f i) (totalι f E.obj j))).mp
    have h := congrArg (fun t ↦ prod.map (totalι f D.obj i) (baseι f j) ≫ t)
      (β.comm () ())
    change prod.map (totalι f D.obj i) (baseι f j) ≫
      (prod.map ((Over.map (Sigma.desc f)).map (β.hom ())) (𝟙 _) ≫
        (totalGluing f E).hom) =
      prod.map (totalι f D.obj i) (baseι f j) ≫
        ((totalGluing f D).hom ≫ prod.map (𝟙 _)
          ((Over.map (Sigma.desc f)).map (β.hom ()))) at h
    simp only [prod.map_map_assoc] at h
    rw [← ht] at h
    simp only [Category.comp_id] at h
    rw [prod_map_comp_left, Category.assoc, totalGluing_ι, totalGluing_ι_assoc] at h
    simpa only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id, ht] using h

private def totalFunctorFullyFaithful : (totalFunctor f).FullyFaithful where
  preimage := restrictMap f
  map_preimage β := by
    apply DescentData.hom_ext
    rintro ⟨⟩
    exact totalHom_restrictTotalHom (β.hom ())
  preimage_map α := by
    apply DescentData.hom_ext
    intro i
    exact restrictTotalHom_totalHom α.hom i

/-- A scheme `Y` over `∐ X` is the coproduct of its pullbacks along the inclusions
`Sigma.ι X i`. -/
public lemma isIso_sigmaDesc_pullback_fst {Y : Scheme.{u}} (g : Y ⟶ ∐ X) :
    IsIso (Sigma.desc (fun i ↦ pullback.fst g (Sigma.ι X i))) := by
  apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk Y (fun i ↦ pullback.fst g (Sigma.ι X i)))).mp
  exact sigma_universal X (Cofan.mk Y (fun i ↦ pullback.fst g (Sigma.ι X i)))
    (Discrete.natTrans (fun i ↦ pullback.snd g (Sigma.ι X i.as))) g
    (by ext; simp [pullback.condition]) (.of_discrete _)
    (fun i ↦ IsPullback.of_hasPullback _ _)

private abbrev totalSourceMap (D : DescentData f) (i j : I) :
    pullback ((D.obj i).hom ≫ f i) (f j) ⟶
    pullback ((totalObj D.obj).hom ≫ Sigma.desc f) (Sigma.desc f) :=
  pullback.map _ _ _ _ (Sigma.ι (fun i ↦ (D.obj i).left) i) (Sigma.ι X j)
    (𝟙 S) (by simp) (by simp)
private abbrev totalTargetMap (D : DescentData f) (i j : I) :
    pullback (f i) ((D.obj j).hom ≫ f j) ⟶
    pullback (Sigma.desc f) ((totalObj D.obj).hom ≫ Sigma.desc f) :=
  pullback.map _ _ _ _ (Sigma.ι X i) (Sigma.ι (fun i ↦ (D.obj i).left) j)
    (𝟙 S) (by simp) (by simp)

private lemma totalGluingPullback_ι (D : DescentData f) (i j : I) :
    totalSourceMap f D i j ≫ ((totalDescentData f D).gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso i j).hom ≫ totalTargetMap f D i j := by
  have h := congrArg (fun t ↦ t.left) (totalGluing_ι f D i j)
  dsimp only [Over.comp_left] at h
  simp only [DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, DescentData.gluingIso, Over.forget_map, Category.assoc]
  show totalSourceMap f D i j ≫
      (Over.prodLeftIsoPullback ((Over.map (Sigma.desc f)).obj (totalObj D.obj))
        (Over.mk (Sigma.desc f))).inv ≫ (totalGluing f D).hom.left ≫
        (Over.prodLeftIsoPullback (Over.mk (Sigma.desc f))
          ((Over.map (Sigma.desc f)).obj (totalObj D.obj))).hom =
    (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv ≫
      (D.gluing i j).hom.left.left ≫
      (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))).hom ≫
      totalTargetMap f D i j
  rw [show totalSourceMap f D i j = _ from
    (prodMap_left (totalι f D.obj i) (baseι f j)).symm,
    show totalTargetMap f D i j = _ from (prodMap_left (baseι f i) (totalι f D.obj j)).symm]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (prod.map (totalι f D.obj i) (baseι f j)).left, h]
  simp only [Category.assoc]

/-- The first projection of `totalSourceMap` is the inclusion of the `i`-th summand. -/
private lemma totalSourceMap_fst (D : DescentData f) (i j : I) :
    totalSourceMap f D i j ≫ pullback.fst _ _ =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫
        Sigma.ι (fun i ↦ (D.obj i).left) i :=
  pullback.lift_fst _ _ _

/-- The second projection of `totalSourceMap` is the inclusion of the `j`-th summand. -/
private lemma totalSourceMap_snd (D : DescentData f) (i j : I) :
    totalSourceMap f D i j ≫ pullback.snd _ _ =
      pullback.snd ((D.obj i).hom ≫ f i) (f j) ≫ Sigma.ι X j :=
  pullback.lift_snd _ _ _

/-- The first projection of `totalTargetMap` is the inclusion of the `i`-th summand. -/
private lemma totalTargetMap_fst (D : DescentData f) (i j : I) :
    totalTargetMap f D i j ≫ pullback.fst _ _ =
      pullback.fst (f i) ((D.obj j).hom ≫ f j) ≫ Sigma.ι X i :=
  pullback.lift_fst _ _ _

/-- The second projection of `totalTargetMap` is the inclusion of the `j`-th summand. -/
private lemma totalTargetMap_snd (D : DescentData f) (i j : I) :
    totalTargetMap f D i j ≫ pullback.snd _ _ =
      pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫
        Sigma.ι (fun i ↦ (D.obj i).left) j :=
  pullback.lift_snd _ _ _

private abbrev restrictObject (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i : I) :
    Over (X i) := (Over.pullback (Sigma.ι X i)).obj (E.obj ())

private def restrictedObjectCofanMap
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) :
    totalObj (fun i ↦ restrictObject f E i) ⟶ E.obj () :=
  Over.homMk (Sigma.desc (fun i ↦ pullback.fst (E.obj ()).hom (Sigma.ι X i))) (by
    apply Sigma.hom_ext
    intro i
    simp [totalObj, restrictObject, pullback.condition])

private def restrictedObjectIso
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) :
    totalObj (fun i ↦ restrictObject f E i) ≅ E.obj () := by
  let h := restrictedObjectCofanMap f E
  have : IsIso h.left := isIso_sigmaDesc_pullback_fst (E.obj ()).hom
  exact Over.isoMk (asIso h.left) (Over.w h)

private def restrictedObjectInclusion
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i : I) :
  (Over.map (f i)).obj (restrictObject f E i) ⟶
      (Over.map (Sigma.desc f)).obj (E.obj ()) :=
  Over.homMk (pullback.fst (E.obj ()).hom (Sigma.ι X i)) (by
    change pullback.fst (E.obj ()).hom (Sigma.ι X i) ≫
        (E.obj ()).hom ≫ Sigma.desc f =
      pullback.snd (E.obj ()).hom (Sigma.ι X i) ≫ f i
    rw [← Category.assoc, pullback.condition]
    simp [Category.assoc])

private lemma restrictedObject_isPullback
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i : I) :
    IsPullback (restrictedObjectInclusion f E i)
      (structureMap (f i) (restrictObject f E i))
      (structureMap (Sigma.desc f) (E.obj ())) (baseι f i) := by
  have hw : restrictedObjectInclusion f E i ≫ structureMap (Sigma.desc f) (E.obj ()) =
      structureMap (f i) (restrictObject f E i) ≫ baseι f i := by
    apply Over.OverMorphism.ext
    simp [restrictedObjectInclusion, baseι, pullback.condition]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk hw (fun s ↦ ?_) ?_ ?_ ?_
  · have hs : s.fst.left ≫ (E.obj ()).hom = s.snd.left ≫ Sigma.ι X i :=
      (congrArg (fun t ↦ t.left) s.condition :)
    apply Over.homMk (pullback.lift s.fst.left s.snd.left hs) (by
      show pullback.lift s.fst.left s.snd.left _ ≫
        pullback.snd (E.obj ()).hom (Sigma.ι X i) ≫ f i = s.pt.hom
      rw [← Category.assoc, pullback.lift_snd]
      exact Over.w s.snd)
  · intro s
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  · intro s
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  · intro s m hm₁ hm₂
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (congrArg (fun t ↦ t.left) hm₁).trans ?_
      exact (pullback.lift_fst _ _ _).symm
    · refine (congrArg (fun t ↦ t.left) hm₂).trans ?_
      exact (pullback.lift_snd _ _ _).symm

private lemma restrictedSource_isPullback
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    IsPullback
      (prod.map (restrictedObjectInclusion f E i) (baseι f j))
      (prod.map (structureMap (f i) (restrictObject f E i)) (𝟙 (Over.mk (f j))))
      (prod.map (structureMap (Sigma.desc f) (E.obj ()))
        (𝟙 (Over.mk (Sigma.desc f))))
      (prod.map (baseι f i) (baseι f j)) :=
  IsPullback.prod (restrictedObject_isPullback f E i) IsPullback.of_id_snd

private lemma restrictedTarget_isPullback
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    IsPullback
      (prod.map (baseι f i) (restrictedObjectInclusion f E j))
      (prod.map (𝟙 (Over.mk (f i)))
        (structureMap (f j) (restrictObject f E j)))
      (prod.map (𝟙 (Over.mk (Sigma.desc f)))
        (structureMap (Sigma.desc f) (E.obj ())))
      (prod.map (baseι f i) (baseι f j)) :=
  IsPullback.prod IsPullback.of_id_snd (restrictedObject_isPullback f E j)

private def restrictedSourceComparison
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    Over.mk (prod.map (structureMap (f i) (restrictObject f E i))
      (𝟙 (Over.mk (f j)))) ≅
    (Over.pullback (prod.map (baseι f i) (baseι f j))).obj
      (Over.mk (prod.map (structureMap (Sigma.desc f) (E.obj ()))
        (𝟙 (Over.mk (Sigma.desc f))))) := by
  let h := restrictedSource_isPullback f E i j
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

private def restrictedTargetComparison
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    Over.mk (prod.map (𝟙 (Over.mk (f i)))
      (structureMap (f j) (restrictObject f E j))) ≅
    (Over.pullback (prod.map (baseι f i) (baseι f j))).obj
      (Over.mk (prod.map (𝟙 (Over.mk (Sigma.desc f)))
        (structureMap (Sigma.desc f) (E.obj ())))) := by
  let h := restrictedTarget_isPullback f E i j
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

private def restrictedGluing
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    Over.mk (prod.map (structureMap (f i) (restrictObject f E i))
      (𝟙 (Over.mk (f j)))) ≅
    Over.mk (prod.map (𝟙 (Over.mk (f i)))
      (structureMap (f j) (restrictObject f E j))) :=
  restrictedSourceComparison f E i j ≪≫
    (Over.pullback (prod.map (baseι f i) (baseι f j))).mapIso (E.gluing () ()) ≪≫
    (restrictedTargetComparison f E i j).symm

@[reassoc]
private lemma restrictedGluing_naturality
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    prod.map (restrictedObjectInclusion f E i) (baseι f j) ≫
        (E.gluing () ()).hom.left =
      (restrictedGluing f E i j).hom.left ≫
        prod.map (baseι f i) (restrictedObjectInclusion f E j) := by
  rw [← (restrictedSource_isPullback f E i j).isoPullback_hom_fst,
    ← (restrictedTarget_isPullback f E i j).isoPullback_hom_fst]
  simp only [restrictedGluing, restrictedSourceComparison, restrictedTargetComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.comp_left, Over.isoMk_hom_left,
    Over.isoMk_inv_left, Category.assoc, Iso.inv_hom_id_assoc, Over.pullback_map_left,
    Over.mk_hom, pullback.lift_fst]

private lemma restrictedObjectInclusion_mono
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i : I) :
    Mono (restrictedObjectInclusion f E i) := by
  have hfst : Mono (pullback.fst (E.obj ()).hom (Sigma.ι X i)) := by
    apply MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
    infer_instance
  have hleft : Mono (restrictedObjectInclusion f E i).left := by
    simpa [restrictedObjectInclusion] using hfst
  exact Over.mono_of_mono_left (restrictedObjectInclusion f E i)

private lemma restrictedCocycle
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j k : I) :
    prod.map (restrictedGluing f E i j).hom.left (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (restrictedGluing f E j k).hom.left =
      prodMapFirstThird (restrictedGluing f E i k).hom.left := by
  let a := restrictedObjectInclusion f E i
  let b := restrictedObjectInclusion f E j
  let c := restrictedObjectInclusion f E k
  let ai := baseι f i
  let bj := baseι f j
  let ck := baseι f k
  let sourceIncl := prod.map (prod.map a bj) ck
  let targetIncl := prod.map (prod.map ai bj) c
  let middleIncl := prod.map (prod.map ai b) ck
  let localFirst := prod.map (restrictedGluing f E i j).hom.left
    (𝟙 (Over.mk (f k)))
  let globalFirst := prod.map (E.gluing () ()).hom.left
    (𝟙 (Over.mk (Sigma.desc f)))
  let localTail := prodMapLastTwo (A := Over.mk (f i))
    (restrictedGluing f E j k).hom.left
  let globalTail := prodMapLastTwo (A := Over.mk (Sigma.desc f))
    (E.gluing () ()).hom.left
  have hc : Mono c := restrictedObjectInclusion_mono f E k
  have htarget : Mono targetIncl := by
    dsimp [targetIncl]
    infer_instance
  have hhead : localFirst ≫ middleIncl = sourceIncl ≫ globalFirst := by
    simp only [localFirst, middleIncl, sourceIncl, globalFirst,
      prod.map_map, Category.id_comp, Category.comp_id]
    rw [restrictedGluing_naturality f E i j]
  have htail : middleIncl ≫ globalTail = localTail ≫ targetIncl :=
    prodMapLastTwo_naturality ai b ck bj c _ _ (restrictedGluing_naturality f E j k)
  apply (cancel_mono targetIncl).mp
  calc
    (localFirst ≫ localTail) ≫ targetIncl =
        sourceIncl ≫ (globalFirst ≫ globalTail) := by
      rw [Category.assoc, ← htail, ← Category.assoc, hhead, Category.assoc]
    _ = sourceIncl ≫ prodMapFirstThird (E.gluing () ()).hom.left := by
      rw [E.cocycle () () ()]
    _ = prodMapFirstThird (restrictedGluing f E i k).hom.left ≫ targetIncl :=
      prodMapFirstThird_naturality a bj ck ai c _ _ (restrictedGluing_naturality f E i k)

@[reducible] private def restrictedDescentData
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) : DescentData f where
  obj i := restrictObject f E i
  gluing i j := restrictedGluing f E i j
  cocycle i j k := restrictedCocycle f E i j k

@[simp]
private lemma restrictedDescentData_gluing
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i j : I) :
    (restrictedDescentData f E).gluing i j = restrictedGluing f E i j := rfl

private def descentIsoMk {J : Type w} {Y : J → Scheme.{u}}
    {g : ∀ i, Y i ⟶ S} {D E : DescentData g}
    (e : ∀ i, D.obj i ≅ E.obj i)
    (comm : ∀ i j,
      prod.map ((Over.map (g i)).map (e i).hom) (𝟙 (Over.mk (g j))) ≫
          (E.gluing i j).hom.left =
        (D.gluing i j).hom.left ≫
          prod.map (𝟙 (Over.mk (g i))) ((Over.map (g j)).map (e j).hom)) :
    D ≅ E where
  hom :=
    { hom := fun i ↦ (e i).hom
      comm := comm }
  inv :=
    { hom := fun i ↦ (e i).inv
      comm := by
        intro i j
        apply (cancel_epi
          (prod.map ((Over.map (g i)).map (e i).hom) (𝟙 (Over.mk (g j))))).mp
        apply (cancel_mono
          (prod.map (𝟙 (Over.mk (g i))) ((Over.map (g j)).map (e j).hom))).mp
        simpa [Category.assoc, prod.map_map, Functor.map_comp] using (comm i j).symm }
  hom_inv_id := by
    apply DescentData.hom_ext
    intro i
    exact (e i).hom_inv_id
  inv_hom_id := by
    apply DescentData.hom_ext
    intro i
    exact (e i).inv_hom_id

@[reassoc]
private lemma restrictedTotalObjectIso_ι
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i : I) :
    totalι f (fun i ↦ restrictObject f E i) i ≫
        (Over.map (Sigma.desc f)).map (restrictedObjectIso f E).hom =
      restrictedObjectInclusion f E i := by
  ext
  simp [totalι, restrictedObjectIso, restrictedObjectCofanMap,
    restrictedObjectInclusion, totalObj]

@[reassoc]
private lemma restrictedTotalObjectIso_ι'
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) (i : I) :
    totalι f (restrictedDescentData f E).obj i ≫
        (Over.map (Sigma.desc f)).map (restrictedObjectIso f E).hom =
      restrictedObjectInclusion f E i := by
  simpa [restrictedDescentData] using restrictedTotalObjectIso_ι f E i

private def restrictedTotalIso
    (E : DescentData (fun _ : Unit ↦ Sigma.desc f)) :
    totalDescentData f (restrictedDescentData f E) ≅ E :=
  descentIsoMk (g := fun _ : Unit ↦ Sigma.desc f)
    (D := totalDescentData f (restrictedDescentData f E)) (E := E)
    (fun _ ↦ restrictedObjectIso f E) (by
    intro i j
    obtain rfl : i = () := Subsingleton.elim _ _
    obtain rfl : j = () := Subsingleton.elim _ _
    apply Cofan.IsColimit.hom_ext
      (sourceCofanIsColimit f (restrictedDescentData f E).obj)
    rintro ⟨i', j'⟩
    dsimp only [sourceCofan, cofan_mk_inj]
    simp only [prod.map_map_assoc, restrictedTotalObjectIso_ι']
    simp only [Category.comp_id]
    rw [restrictedGluing_naturality f E i' j']
    simp only [totalGluingOver, Over.isoMk_hom_left]
    rw [totalGluing_ι_assoc (D := restrictedDescentData f E)]
    simp only [prod.map_map, Category.comp_id, restrictedTotalObjectIso_ι'])

private theorem totalFunctor_essSurj : (totalFunctor f).EssSurj where
  mem_essImage E := ⟨restrictedDescentData f E, ⟨restrictedTotalIso f E⟩⟩

/-- The complete specification of the equivalence between descent data for a family and
descent data for the morphism from its coproduct. -/
public structure FamilyCoproductEquivalence where
  /-- The equivalence of categories. -/
  equivalence :
    DescentData f ≌ DescentData (fun _ : Unit ↦ Sigma.desc f)
  /-- The object over the coproduct is the coproduct of the component objects. -/
  objIso (D : DescentData f) :
    (equivalence.functor.obj D).obj () ≅
      Over.mk (Limits.Sigma.map (fun i ↦ (D.obj i).hom))
  /-- The canonical map from a pairwise fibre product for the family to the corresponding
  fibre product for the coproduct morphism. -/
  sourceMap (D : DescentData f) (i j : I) :
    pullback ((D.obj i).hom ≫ f i) (f j) ⟶
      pullback
        (((equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f)
        (Sigma.desc f)
  /-- The first projection of `sourceMap` is the inclusion of the `i`-th summand. -/
  sourceMap_fst (D : DescentData f) (i j : I) :
    sourceMap D i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Sigma.ι (fun i ↦ (D.obj i).left) i ≫ (objIso D).inv.left
  /-- The second projection of `sourceMap` is the inclusion of the `j`-th summand. -/
  sourceMap_snd (D : DescentData f) (i j : I) :
    sourceMap D i j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Sigma.ι X j
  /-- The canonical map on the fibre products occurring as targets of the gluing maps. -/
  targetMap (D : DescentData f) (i j : I) :
    pullback (f i) ((D.obj j).hom ≫ f j) ⟶
      pullback
        (Sigma.desc f)
        (((equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f)
  /-- The first projection of `targetMap` is the inclusion of the `i`-th summand. -/
  targetMap_fst (D : DescentData f) (i j : I) :
    targetMap D i j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Sigma.ι X i
  /-- The second projection of `targetMap` is the inclusion of the `j`-th summand. -/
  targetMap_snd (D : DescentData f) (i j : I) :
    targetMap D i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Sigma.ι (fun i ↦ (D.obj i).left) j ≫ (objIso D).inv.left
  /-- On each pair of summands, the gluing isomorphism is the given family gluing
  isomorphism. -/
  gluing (D : DescentData f) (i j : I) :
    sourceMap D i j ≫
        ((equivalence.functor.obj D).gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso i j).hom ≫ targetMap D i j
  /-- The functor sends a morphism to the coproduct of its component maps. -/
  map {D E : DescentData f} (α : D ⟶ E) :
    (objIso D).hom.left ≫ Limits.Sigma.map (fun i ↦ (α.hom i).left) =
      ((equivalence.functor.map α).hom ()).left ≫ (objIso E).hom.left

/-- Descent data relative to a family `X i ⟶ S` are canonically equivalent to descent data
relative to the single morphism `(∐ i, X i) ⟶ S`. Under this equivalence both objects and gluing
maps are formed by coproduct, as specified by `FamilyCoproductEquivalence`. -/
@[no_expose, stacks 023X]
noncomputable def familyCoproductEquivalence :
    FamilyCoproductEquivalence f := by
  have hff := totalFunctorFullyFaithful f
  have := totalFunctor_essSurj f
  have := hff.full
  have := hff.faithful
  have : (totalFunctor f).IsEquivalence := { }
  exact
    { equivalence := (totalFunctor f).asEquivalence
      objIso := fun D ↦ Iso.refl _
      sourceMap := totalSourceMap f
      sourceMap_fst := fun D i j ↦ by
        simp only [Iso.refl_inv, Over.id_left]
        exact totalSourceMap_fst f D i j
      sourceMap_snd := totalSourceMap_snd f
      targetMap := totalTargetMap f
      targetMap_fst := totalTargetMap_fst f
      targetMap_snd := fun D i j ↦ by
        simp only [Iso.refl_inv, Over.id_left]
        exact totalTargetMap_snd f D i j
      gluing := totalGluingPullback_ι f
      map := fun α ↦ by
        simp only [Iso.refl_hom, Over.id_left]
        exact (totalMap_hom_left f α).symm }

end AlgebraicGeometry.DescentData
