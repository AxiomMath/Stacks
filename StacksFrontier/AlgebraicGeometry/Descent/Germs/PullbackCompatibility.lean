module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.FamilyCoproduct
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare

/-!
# Compatibility of pullback with coproducts of families

Pullback of descent data along a morphism of families agrees, under the family–coproduct
equivalences, with pullback along the induced morphism of coproducts. The agreement is natural
in the descent datum and is determined by its restrictions to the members of the source family.

## Main definitions

* `AlgebraicGeometry.MorphismOfSchemeFamilies.PullbackCompatibility` specifies the canonical
  natural isomorphism together with its two projections on each member of the source family.

## Main results

* `AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackCompatibility` constructs this comparison
  for any morphism of families.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.MorphismOfSchemeFamilies

open CategoryTheory CategoryTheory.Limits

attribute [local simp] pullback.lift_fst pullback.lift_snd

variable {I : Type v} [Small.{u} I]

section SchemeCoproducts

variable {I : Type v} [Small.{u} I]

private lemma schemeCofanUniversal {X : I → Scheme.{u}} {c : Cofan X} (hc : IsColimit c) :
    IsUniversalColimit c :=
  (DescentData.sigma_universal X).of_iso ((coproductIsCoproduct X).uniqueUpToIso hc)

end SchemeCoproducts

private abbrev globalObject (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) : Over F.targetCoproduct :=
  Over.mk (Limits.Sigma.map (fun j ↦ (D.obj j).hom))

private abbrev globalPullback (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) : Over F.sourceCoproduct :=
  (Over.pullback F.coproductHom).obj (globalObject F D)

private def localToGlobalPullback (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    (localObj F D i).left ⟶ (globalPullback F D).left := by
  let j := F.familyHom.s₀ i
  let p := pullback.fst (D.obj j).hom (F.familyHom.h₀ i)
  let q := pullback.snd (D.obj j).hom (F.familyHom.h₀ i)
  refine pullback.lift (p ≫ Sigma.ι (fun k ↦ (D.obj k).left) j)
    (q ≫ Sigma.ι (fun k ↦ F.sourceFamily.X k) i) ?_
  change p ≫ Sigma.ι (fun k ↦ (D.obj k).left) j ≫
      Limits.Sigma.map (fun k ↦ (D.obj k).hom) =
    q ≫ Sigma.ι (fun k ↦ F.sourceFamily.X k) i ≫ F.coproductHom
  dsimp [MorphismOfSchemeFamilies.coproductHom]
  simp only [Limits.Sigma.ι_map]
  rw [← Category.assoc, pullback.condition]
  simp [j, q, Category.assoc]

/-- The coproduct of a family of morphisms, evaluated on a point of a summand, is the image
of that point under the corresponding component. -/
private lemma sigmaMap_sigmaι_apply {Y X : I → Scheme.{u}} (α : ∀ i, Y i ⟶ X i) (j : I)
    (z : Y j) : Limits.Sigma.map α (Sigma.ι Y j z) = Sigma.ι X j (α j z) := by
  rw [← Scheme.Hom.comp_apply, Sigma.ι_map, Scheme.Hom.comp_apply]

private lemma isPullback_sigmaι_sigmaMap {Y : I → Scheme.{u}}
    {X : I → Scheme.{u}} (α : ∀ i, Y i ⟶ X i) (i : I) :
    IsPullback (α i) (Sigma.ι Y i) (Sigma.ι X i) (Limits.Sigma.map α) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨j, z, rfl⟩ := (AlgebraicGeometry.sigmaOpenCover Y).exists_eq y
    change Sigma.ι X i x = Limits.Sigma.map α (Sigma.ι Y j z) at hx
    have heq : Sigma.ι X i x = Sigma.ι X j (α j z) :=
      hx.trans (sigmaMap_sigmaι_apply α j z)
    have hij : i = j := congrArg Sigma.fst
      ((AlgebraicGeometry.sigmaι_eq_iff X i j x (α j z)).mp heq)
    subst j
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨α i z, (sigmaMap_sigmaι_apply α i z).symm⟩

private lemma sourceι_coproductHom (F : MorphismOfSchemeFamilies.{u})
    (i : F.sourceFamily.I₀) :
    Sigma.ι (fun k ↦ F.sourceFamily.X k) i ≫ F.coproductHom =
      F.familyHom.h₀ i ≫ Sigma.ι F.targetFamily.X (F.familyHom.s₀ i) := by
  simp [MorphismOfSchemeFamilies.coproductHom]

private lemma localToGlobalPullback_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    localToGlobalPullback F D i ≫
        pullback.fst (Limits.Sigma.map (fun k ↦ (D.obj k).hom)) F.coproductHom =
      pullback.fst (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) ≫
        Sigma.ι (fun k ↦ (D.obj k).left) (F.familyHom.s₀ i) := by
  change pullback.lift _ _ _ ≫ _ = _
  exact pullback.lift_fst _ _ _

private lemma localGlobalPullback_isPullback (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    IsPullback (localToGlobalPullback F D i)
      (pullback.snd (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i))
      (globalPullback F D).hom
      (Sigma.ι (fun k ↦ F.sourceFamily.X k) i) := by
  let j := F.familyHom.s₀ i
  let hp₁ := IsPullback.of_hasPullback (D.obj j).hom (F.familyHom.h₀ i)
  let hp₂ := (isPullback_sigmaι_sigmaMap (fun k ↦ (D.obj k).hom) j).flip
  have hp := hp₁.paste_horiz hp₂
  have hbot : Sigma.ι (fun k ↦ F.sourceFamily.X k) i ≫ F.coproductHom =
      F.familyHom.h₀ i ≫ Sigma.ι F.targetFamily.X j :=
    sourceι_coproductHom F i
  have hp' : IsPullback
      (localToGlobalPullback F D i ≫
        pullback.fst (Limits.Sigma.map (fun k ↦ (D.obj k).hom)) F.coproductHom)
      (pullback.snd (D.obj j).hom (F.familyHom.h₀ i))
      (Limits.Sigma.map (fun k ↦ (D.obj k).hom))
      (Sigma.ι (fun k ↦ F.sourceFamily.X k) i ≫ F.coproductHom) := by
    simpa [j, localToGlobalPullback_fst, hbot] using hp
  exact hp'.of_right (by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback (Limits.Sigma.map (fun k ↦ (D.obj k).hom))
        F.coproductHom)

private lemma localToGlobalPullback_sigmaDesc_isIso
    (F : MorphismOfSchemeFamilies.{u}) (D : DescentData F.targetFamily.f) :
    IsIso (Sigma.desc (fun i ↦ localToGlobalPullback F D i)) := by
  let e (i : F.sourceFamily.I₀) :=
    (localGlobalPullback_isPullback F D i).isoPullback
  have hcomp :
      Limits.Sigma.map (fun i ↦ (e i).hom) ≫
          Sigma.desc (fun i ↦ pullback.fst (globalPullback F D).hom
            (Sigma.ι (fun k ↦ F.sourceFamily.X k) i)) =
        Sigma.desc (fun i ↦ localToGlobalPullback F D i) := by
    apply Sigma.hom_ext
    intro i
    calc
      _ = (Sigma.ι (fun k ↦ (localObj F D k).left) i ≫
          Limits.Sigma.map (fun k ↦ (e k).hom) ≫
          Sigma.desc (fun k ↦ pullback.fst (globalPullback F D).hom
            (Sigma.ι (fun l ↦ F.sourceFamily.X l) k))) := by rfl
      _ = (Sigma.ι (fun k ↦ (localObj F D k).left) i ≫
          Limits.Sigma.map (fun k ↦ (e k).hom)) ≫
          Sigma.desc (fun k ↦ pullback.fst (globalPullback F D).hom
            (Sigma.ι (fun l ↦ F.sourceFamily.X l) k)) := by rw [← Category.assoc]
      _ = ((e i).hom ≫
          Sigma.ι (fun k ↦ pullback (globalPullback F D).hom
            (Sigma.ι (fun l ↦ F.sourceFamily.X l) k)) i) ≫
          Sigma.desc (fun k ↦ pullback.fst (globalPullback F D).hom
            (Sigma.ι (fun l ↦ F.sourceFamily.X l) k)) := by
              rw [Limits.Sigma.ι_map]
      _ = (e i).hom ≫
          (Sigma.ι (fun k ↦ pullback (globalPullback F D).hom
            (Sigma.ι (fun l ↦ F.sourceFamily.X l) k)) i ≫
          Sigma.desc (fun k ↦ pullback.fst (globalPullback F D).hom
            (Sigma.ι (fun l ↦ F.sourceFamily.X l) k))) := by rw [Category.assoc]
      _ = (e i).hom ≫ pullback.fst (globalPullback F D).hom
          (Sigma.ι (fun k ↦ F.sourceFamily.X k) i) := by rw [Sigma.ι_comp_desc]
      _ = localToGlobalPullback F D i :=
        (localGlobalPullback_isPullback F D i).isoPullback_hom_fst
      _ = Sigma.ι (fun k ↦ (localObj F D k).left) i ≫
          Sigma.desc (fun k ↦ localToGlobalPullback F D k) := by
            rw [Sigma.ι_comp_desc]
  have h₁ : IsIso (Limits.Sigma.map (fun i ↦ (e i).hom)) := by
    dsimp [e]
    infer_instance
  have h₂ : IsIso (Sigma.desc (fun i ↦
      pullback.fst (globalPullback F D).hom
        (Sigma.ι (fun k ↦ F.sourceFamily.X k) i))) := by
    apply AlgebraicGeometry.DescentData.isIso_sigmaDesc_pullback_fst
  rw [← hcomp]
  infer_instance

private def localTotalToGlobalPullback (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :
    AlgebraicGeometry.DescentData.totalObj (fun i ↦ localObj F D i) ⟶ globalPullback F D :=
  Over.homMk (Sigma.desc (fun i ↦ localToGlobalPullback F D i)) (by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc]
    change localToGlobalPullback F D i ≫ (globalPullback F D).hom =
      Sigma.ι (fun k ↦ (localObj F D k).left) i ≫
        Limits.Sigma.map (fun k ↦ (localObj F D k).hom)
    rw [Limits.Sigma.ι_map]
    exact (localGlobalPullback_isPullback F D i).w)

private def localTotalToGlobalPullbackIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :
    AlgebraicGeometry.DescentData.totalObj (fun i ↦ localObj F D i) ≅ globalPullback F D := by
  let m := localTotalToGlobalPullback F D
  have hm : IsIso m.left := by
    change IsIso (Sigma.desc (fun i ↦ localToGlobalPullback F D i))
    exact localToGlobalPullback_sigmaDesc_isIso F D
  exact Over.isoMk (asIso m.left) (Over.w m)

private def totalOverIso {X : I → Scheme.{u}} {V W : ∀ i, Over (X i)}
    (e : ∀ i, V i ≅ W i) :
    AlgebraicGeometry.DescentData.totalObj V ≅ AlgebraicGeometry.DescentData.totalObj W := by
  let m : AlgebraicGeometry.DescentData.totalObj V ⟶ AlgebraicGeometry.DescentData.totalObj W :=
    Over.homMk (Limits.Sigma.map (fun i ↦ (e i).hom.left)) (by
      apply Sigma.hom_ext
      intro i
      dsimp [AlgebraicGeometry.DescentData.totalObj]
      calc
        _ = ((e i).hom.left ≫ Sigma.ι (fun k ↦ (W k).left) i) ≫
            Limits.Sigma.map (fun k ↦ (W k).hom) := by
              rw [← Category.assoc, Limits.Sigma.ι_map]
        _ = (e i).hom.left ≫
            ((W i).hom ≫ Sigma.ι X i) := by
              rw [Category.assoc, Limits.Sigma.ι_map]
        _ = (V i).hom ≫ Sigma.ι X i := by
              rw [← Category.assoc, Over.w (e i).hom]
        _ = Sigma.ι (fun k ↦ (V k).left) i ≫
            Limits.Sigma.map (fun k ↦ (V k).hom) :=
              (Limits.Sigma.ι_map (fun k ↦ (V k).hom) i).symm)
  have hm : IsIso m.left := by
    change IsIso (Limits.Sigma.map (fun i ↦ (e i).hom.left))
    have hcomp (i) : IsIso (e i).hom.left := by
      change IsIso ((Over.forget (X i)).map (e i).hom)
      infer_instance
    infer_instance
  exact Over.isoMk (asIso m.left) (Over.w m)

private abbrev targetEquiv (F : MorphismOfSchemeFamilies.{u}) :=
  DescentData.familyCoproductEquivalence F.targetFamily.f
private abbrev sourceEquiv (F : MorphismOfSchemeFamilies.{u}) :=
  DescentData.familyCoproductEquivalence F.sourceFamily.f
private abbrev familyPB (F : MorphismOfSchemeFamilies.{u}) :=
  MorphismOfSchemeFamilies.pullbackFunctor F
private abbrev singletonPB (F : MorphismOfSchemeFamilies.{u}) :=
  DescentData.pullbackFunctor (Sigma.desc F.targetFamily.f)
    (Sigma.desc F.sourceFamily.f) F.baseHom F.coproductHom F.coproductHom_comp
private abbrev localDatum (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) := (familyPB F).functor.obj D
private abbrev totalDatum (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :=
  (sourceEquiv F).equivalence.functor.obj (localDatum F D)
private abbrev globalDatum (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :=
  (singletonPB F).functor.obj ((targetEquiv F).equivalence.functor.obj D)
private def componentIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    (localDatum F D).obj i ≅ localObj F D i :=
  (DescentData.evaluation i).mapIso (eqToIso ((familyPB F).obj_eq D)) ≪≫
    MorphismOfSchemeFamilies.pulledBackDatumObjIso F D i

private def pullbackObjectComparisonIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :
    ((DescentData.pullbackFunctor (Sigma.desc F.targetFamily.f)
      (Sigma.desc F.sourceFamily.f) F.baseHom F.coproductHom
      F.coproductHom_comp).functor.obj
        ((DescentData.familyCoproductEquivalence
          F.targetFamily.f).equivalence.functor.obj D)).obj () ≅
      ((DescentData.familyCoproductEquivalence F.sourceFamily.f).equivalence.functor.obj
        ((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj D)).obj () := by
  let T := DescentData.familyCoproductEquivalence F.targetFamily.f
  let U := DescentData.familyCoproductEquivalence F.sourceFamily.f
  letI : HasTerminal (Over F.sourceBase) := CategoryTheory.Over.over_hasTerminal _
  letI : HasBinaryProducts (Over F.sourceBase) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  let PF := DescentData.pullbackFunctor (Sigma.desc F.targetFamily.f)
    (Sigma.desc F.sourceFamily.f) F.baseHom F.coproductHom F.coproductHom_comp
  let P := MorphismOfSchemeFamilies.pullbackFunctor F
  let globalIso := PF.objIso (T.equivalence.functor.obj D) ≪≫
    (Over.pullback F.coproductHom).mapIso (T.objIso D)
  let localIso := U.objIso (P.functor.obj D) ≪≫ totalOverIso (componentIso F D)
  exact globalIso ≪≫ (localTotalToGlobalPullbackIso F D).symm ≪≫ localIso.symm

private lemma descentData_isIso_of_isIso_components {S : Scheme.{u}}
    {K : Type v} [Small.{u} K] {X : K → Scheme.{u}} {f : ∀ k, X k ⟶ S}
    {D E : DescentData f} (φ : D ⟶ E)
    (h : ∀ k, IsIso (φ.hom k)) : IsIso φ := by
  let (k : K) : IsIso (φ.hom k) := h k
  let ψ : E ⟶ D :=
    { hom := fun k ↦ inv (φ.hom k)
      comm := by
        intro i j
        have hglue : (D.gluing i j).hom.left =
            prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j))) ≫
              (E.gluing i j).hom.left ≫
              prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (inv (φ.hom j))) := by
          calc
            _ = (D.gluing i j).hom.left ≫
                prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (φ.hom j)) ≫
                prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (inv (φ.hom j))) := by simp
            _ = _ := by
              have h := congrArg (fun q => q ≫
                prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (inv (φ.hom j))))
                (φ.comm i j)
              simpa [Category.assoc] using h.symm
        calc
          prod.map ((Over.map (f i)).map (inv (φ.hom i))) (𝟙 (Over.mk (f j))) ≫
                (D.gluing i j).hom.left =
              prod.map ((Over.map (f i)).map (inv (φ.hom i))) (𝟙 (Over.mk (f j))) ≫
                prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j))) ≫
                (E.gluing i j).hom.left ≫
                prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (inv (φ.hom j))) := by
                  rw [hglue]
          _ = (E.gluing i j).hom.left ≫
                prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (inv (φ.hom j))) := by
                  simp
          _ = _ := by simp }
  refine ⟨⟨ψ, ?_, ?_⟩⟩ <;> refine DescentData.hom_ext fun i ↦ ?_ <;>
    apply CategoryTheory.Comma.hom_ext <;> simp [ψ]

section Transition
variable {J : Type*} {S : Scheme.{u}} {X : J → Scheme.{u}} {f : ∀ i, X i ⟶ S}

private abbrev transition (D : DescentData f) (i j : J) :=
  (D.gluingPullbackIso i j).hom ≫ pullback.snd _ _

/-- The comparison of the product with the pullback commutes with the second projections. -/
private lemma prodLeftIsoPullback_hom_snd_left (D : DescentData f) (i j : J) :
    (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) = (prod.snd :
        Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ (Over.map (f j)).obj (D.obj j)).left :=
  Over.prodLeftIsoPullback_hom_snd _ _

private lemma transition_hom (D : DescentData f) (i j : J) :
    transition D i j ≫ (D.obj j).hom = pullback.snd _ _ := by
  have h := congrArg (fun k ↦ k.left) (D.gluing_hom_snd_structureMap i j)
  simp only [Over.comp_left, structureMap, Over.homMk_left] at h
  simp only [transition, DescentData.gluingPullbackIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
  rw [reassoc_of% (prodLeftIsoPullback_hom_snd_left D i j), h, Over.prodLeftIsoPullback_inv_snd]
  rfl

private lemma transition_eq (D : DescentData f) (i j : J) :
    transition D i j =
      (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv ≫
        (D.gluing i j).hom.left.left ≫
          (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left := by
  dsimp only [transition, DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map]
  simp only [Category.assoc, prodLeftIsoPullback_hom_snd_left D i j]

private def sourceMapOfHom {D E : DescentData f} (m : ∀ i, D.obj i ⟶ E.obj i)
    (i j : J) : pullback ((D.obj i).hom ≫ f i) (f j) ⟶
      pullback ((E.obj i).hom ≫ f i) (f j) :=
  pullback.lift (pullback.fst _ _ ≫ (m i).left) (pullback.snd _ _)
    (by simp [Category.assoc, pullback.condition])

private def homOfTransition {D E : DescentData f} (m : ∀ i, D.obj i ⟶ E.obj i)
    (h : ∀ i j, sourceMapOfHom m i j ≫ transition E i j =
      transition D i j ≫ (m j).left) : D ⟶ E where
  hom := m
  comm i j := by
    apply prod.hom_ext
    · simp only [Category.assoc, E.gluing_hom_fst i j,
        prod.map_fst_assoc]
      rw [prod.map_fst, Category.comp_id, D.gluing_hom_fst i j]
      apply congrArg (fun k ↦ prod.fst ≫ k)
      apply Over.OverMorphism.ext
      exact Over.w (m i)
    · apply Over.OverMorphism.ext
      apply (cancel_epi (Over.prodLeftIsoPullback
        ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv).mp
      have hs : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i))
          (Over.mk (f j))).inv ≫
          (prod.map ((Over.map (f i)).map (m i)) (𝟙 (Over.mk (f j)))).left ≫
          (Over.prodLeftIsoPullback ((Over.map (f i)).obj (E.obj i))
            (Over.mk (f j))).hom = sourceMapOfHom m i j := by
        apply pullback.hom_ext
        · simp only [Category.assoc,
            Over.prodLeftIsoPullback_hom_fst ((Over.map (f i)).obj (E.obj i)) (Over.mk (f j))]
          rw [← Over.comp_left, prod.map_fst, Over.comp_left]
          simp [sourceMapOfHom]
        · simp only [Category.assoc,
            Over.prodLeftIsoPullback_hom_snd ((Over.map (f i)).obj (E.obj i)) (Over.mk (f j))]
          rw [← Over.comp_left, prod.map_snd, Over.comp_left]
          simp [sourceMapOfHom]
      have hh := h i j
      rw [transition_eq, transition_eq, ← hs] at hh
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left,
        prod.map_snd,
        Over.id_left, Category.id_comp] using! hh
end Transition

private lemma familySource_hom_ext {S : Scheme.{u}} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (T : DescentData.FamilyCoproductEquivalence f) (D : DescentData f)
    {Z : Scheme.{u}}
    {a b : pullback (((T.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f)
      (Sigma.desc f) ⟶ Z}
    (h : ∀ i j, T.sourceMap D i j ≫ a = T.sourceMap D i j ≫ b) : a = b := by
  let c := Cofan.mk ((T.equivalence.functor.obj D).obj ()).left
    (fun i ↦ Sigma.ι (fun i ↦ (D.obj i).left) i ≫ (T.objIso D).inv.left)
  have hc : IsColimit c :=
    (coproductIsCoproduct (fun i ↦ (D.obj i).left)).ofIsoColimit
      (Cocone.ext ((Over.forget _).mapIso (T.objIso D)).symm (by intro j; rfl))
  let d := Cofan.mk _ (fun p : I × I ↦ T.sourceMap D p.1 p.2)
  have hd : Nonempty (IsColimit d) :=
    (schemeCofanUniversal hc).nonempty_isColimit_prod_of_isPullback
      (DescentData.sigma_universal X) (fun i ↦ (D.obj i).hom ≫ f i) f
      (((T.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f) (Sigma.desc f)
      (fun i j ↦ IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      (d := d) (Iso.refl _)
      (by intro i; dsimp [c]; simp [Category.assoc, Over.w_assoc])
      (by intro i; simp)
      (by intro i j; simpa [d, c] using T.sourceMap_fst D i j)
      (by intro i j; simpa [d] using T.sourceMap_snd D i j)
  exact Cofan.IsColimit.hom_ext hd.some a b (fun p ↦ h p.1 p.2)

private abbrev objectComparison (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) : (totalDatum F D).obj () ≅ (globalDatum F D).obj () :=
  (pullbackObjectComparisonIso F D).symm

private lemma objectComparison_ι (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    Sigma.ι (fun i ↦ ((localDatum F D).obj i).left) i ≫
      ((sourceEquiv F).objIso (localDatum F D)).inv.left ≫
      (objectComparison F D).hom.left ≫
      ((singletonPB F).objIso ((targetEquiv F).equivalence.functor.obj D)).hom.left =
    (componentIso F D i).hom.left ≫ localToGlobalPullback F D i ≫
      ((Over.pullback F.coproductHom).map ((targetEquiv F).objIso D).inv).left := by
  simp [objectComparison, pullbackObjectComparisonIso, totalOverIso,
    localTotalToGlobalPullbackIso, localTotalToGlobalPullback, Category.assoc,
    ← Over.comp_left]
  simp [Over.comp_left]

private lemma objectComparison_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    Sigma.ι (fun i ↦ ((localDatum F D).obj i).left) i ≫
      ((sourceEquiv F).objIso (localDatum F D)).inv.left ≫
      (objectComparison F D).hom.left ≫
      ((singletonPB F).objIso ((targetEquiv F).equivalence.functor.obj D)).hom.left ≫
      pullback.fst _ _ =
    (componentIso F D i).hom.left ≫ pullback.fst _ _ ≫
      Sigma.ι (fun j ↦ (D.obj j).left) (F.familyHom.s₀ i) ≫
      ((targetEquiv F).objIso D).inv.left := by
  have h := congrArg (fun k ↦ k ≫ pullback.fst _ _) (objectComparison_ι F D i)
  simpa [Over.pullback_map_left, Category.assoc,
    reassoc_of% (localToGlobalPullback_fst F D i)] using h

private lemma objectComparison_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    Sigma.ι (fun i ↦ ((localDatum F D).obj i).left) i ≫
      ((sourceEquiv F).objIso (localDatum F D)).inv.left ≫
      (objectComparison F D).hom.left ≫
      ((singletonPB F).objIso ((targetEquiv F).equivalence.functor.obj D)).hom.left ≫
      pullback.snd _ _ =
    ((localDatum F D).obj i).hom ≫ Sigma.ι F.sourceFamily.X i := by
  rw [← Over.pullback_obj_hom, Over.w, Over.w, Over.w]
  simp

private abbrev componentMap (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :=
  (componentIso F D i).hom.left ≫ pullback.fst _ _

private lemma componentMap_w (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    componentMap F D i ≫ (D.obj (F.familyHom.s₀ i)).hom =
      ((localDatum F D).obj i).hom ≫ F.familyHom.h₀ i := by
  dsimp only [componentMap]
  rw [Category.assoc, pullback.condition, ← Over.pullback_obj_hom, Over.w_assoc]

private def componentSource (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pullback (((localDatum F D).obj i).hom ≫ F.sourceFamily.f i) (F.sourceFamily.f j) ⟶
      pullback ((D.obj (F.familyHom.s₀ i)).hom ≫ F.targetFamily.f (F.familyHom.s₀ i))
        (F.targetFamily.f (F.familyHom.s₀ j)) :=
  pullback.lift (pullback.fst _ _ ≫ componentMap F D i)
    (pullback.snd _ _ ≫ F.familyHom.h₀ j) (by
      simp only [Category.assoc, reassoc_of% (componentMap_w F D i), F.familyHom.w₀]
      simpa only [Category.assoc] using
        (pullback.condition_assoc (f := ((localDatum F D).obj i).hom ≫ F.sourceFamily.f i)
          (g := F.sourceFamily.f j) F.baseHom))

private lemma component_transition (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    transition (localDatum F D) i j ≫ componentMap F D j =
      componentSource F D i j ≫ transition D (F.familyHom.s₀ i) (F.familyHom.s₀ j) := by
  have aux (E : DescentData F.sourceFamily.f)
      (h : E = MorphismOfSchemeFamilies.pulledBackDatum F D)
      (s : pullback ((E.obj i).hom ≫ F.sourceFamily.f i) (F.sourceFamily.f j) ⟶
        pullback ((D.obj (F.familyHom.s₀ i)).hom ≫ F.targetFamily.f (F.familyHom.s₀ i))
          (F.targetFamily.f (F.familyHom.s₀ j)))
      (hs₁ : s ≫ pullback.fst _ _ = pullback.fst _ _ ≫
        ((DescentData.evaluation i).map (eqToHom h)).left ≫
        (MorphismOfSchemeFamilies.pulledBackDatumObjIso F D i).hom.left ≫
          pullback.fst _ _)
      (hs₂ : s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ F.familyHom.h₀ j) :
      transition E i j ≫ ((DescentData.evaluation j).map (eqToHom h)).left ≫
        (MorphismOfSchemeFamilies.pulledBackDatumObjIso F D j).hom.left ≫ pullback.fst _ _ =
      s ≫ transition D (F.familyHom.s₀ i) (F.familyHom.s₀ j) := by
    subst E
    have hs : s = MorphismOfSchemeFamilies.pulledBackDatumSourceMap F D i j := by
      apply pullback.hom_ext <;>
        simpa [MorphismOfSchemeFamilies.pulledBackDatumSourceMap] using
          (by assumption)
    rw [hs]
    have h := congrArg (fun k ↦ k ≫ pullback.snd _ _)
      (MorphismOfSchemeFamilies.pulledBackDatum_gluing F D i j)
    simpa [transition, MorphismOfSchemeFamilies.pulledBackDatumTargetMap,
      Category.assoc] using h
  exact aux (localDatum F D) ((familyPB F).obj_eq D) (componentSource F D i j)
    (by simp [componentSource, componentMap, componentIso, Category.assoc])
    (by simp [componentSource])

private lemma family_transition {S : Scheme.{u}} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (T : DescentData.FamilyCoproductEquivalence f)
    (D : DescentData f) (i j : I) :
    T.sourceMap D i j ≫ transition (T.equivalence.functor.obj D) () () =
      transition D i j ≫ Sigma.ι (fun i ↦ (D.obj i).left) j ≫ (T.objIso D).inv.left := by
  have h := congrArg (fun k ↦ k ≫ pullback.snd _ _) (T.gluing D i j)
  simpa only [transition, Category.assoc, T.targetMap_snd D i j] using h

private lemma singleton_transition (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :
    transition (globalDatum F D) () () ≫
      ((singletonPB F).objIso ((targetEquiv F).equivalence.functor.obj D)).hom.left ≫
      pullback.fst _ _ =
    (singletonPB F).sourceMap ((targetEquiv F).equivalence.functor.obj D) ≫
      transition ((targetEquiv F).equivalence.functor.obj D) () () := by
  have h := congrArg (fun k ↦ k ≫ pullback.snd _ _)
    ((singletonPB F).gluing ((targetEquiv F).equivalence.functor.obj D))
  simpa only [transition, Category.assoc,
    (singletonPB F).targetMap_snd ((targetEquiv F).equivalence.functor.obj D)] using h

private lemma comparison_source (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (sourceEquiv F).sourceMap (localDatum F D) i j ≫
      sourceMapOfHom (fun _ : Unit ↦ (objectComparison F D).hom) () () ≫
      (singletonPB F).sourceMap ((targetEquiv F).equivalence.functor.obj D) =
    componentSource F D i j ≫
      (targetEquiv F).sourceMap D (F.familyHom.s₀ i) (F.familyHom.s₀ j) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,
      (singletonPB F).sourceMap_fst ((targetEquiv F).equivalence.functor.obj D),
      sourceMapOfHom, pullback.lift_fst_assoc,
      reassoc_of% ((sourceEquiv F).sourceMap_fst (localDatum F D) i j),
      objectComparison_fst F D i,
      (targetEquiv F).sourceMap_fst D (F.familyHom.s₀ i) (F.familyHom.s₀ j),
      componentSource, pullback.lift_fst_assoc, componentMap]
  · simp only [Category.assoc,
      (singletonPB F).sourceMap_snd ((targetEquiv F).equivalence.functor.obj D),
      sourceMapOfHom, pullback.lift_snd_assoc,
      reassoc_of% ((sourceEquiv F).sourceMap_snd (localDatum F D) i j),
      sourceι_coproductHom F j,
      (targetEquiv F).sourceMap_snd D (F.familyHom.s₀ i) (F.familyHom.s₀ j),
      componentSource, pullback.lift_snd_assoc]

private lemma comparison_transition (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :
    sourceMapOfHom (fun _ : Unit ↦ (objectComparison F D).hom) () () ≫
      transition (globalDatum F D) () () =
    transition (totalDatum F D) () () ≫ (objectComparison F D).hom.left := by
  apply (cancel_mono
    ((singletonPB F).objIso ((targetEquiv F).equivalence.functor.obj D)).hom.left).mp
  apply pullback.hom_ext
  · have hs := singleton_transition F D
    simp only [transition, Category.assoc] at hs
    simp only [Category.assoc, hs]
    apply familySource_hom_ext (sourceEquiv F) (localDatum F D)
    intro i j
    simp only [Category.assoc, reassoc_of% (comparison_source F D i j),
      family_transition (targetEquiv F) D (F.familyHom.s₀ i) (F.familyHom.s₀ j),
      reassoc_of% (family_transition (sourceEquiv F) (localDatum F D) i j),
      objectComparison_fst F D j]
    simpa only [componentMap, Category.assoc] using
      congrArg (fun k ↦ k ≫ Sigma.ι (fun j ↦ (D.obj j).left) (F.familyHom.s₀ j) ≫
        ((targetEquiv F).objIso D).inv.left) (component_transition F D i j).symm
  · simp only [Category.assoc]
    rw [← Over.pullback_obj_hom, Over.w, Over.w]
    have ha := transition_hom (globalDatum F D) () ()
    have hb := transition_hom (totalDatum F D) () ()
    simp only [transition, Category.assoc] at ha hb
    rw [ha, hb]
    simp [sourceMapOfHom]

private def comparisonHom (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) : totalDatum F D ⟶ globalDatum F D :=
  homOfTransition (fun _ ↦ (objectComparison F D).hom)
    (fun _ _ ↦ comparison_transition F D)

private def comparisonIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) : totalDatum F D ≅ globalDatum F D := by
  letI : IsIso (comparisonHom F D) :=
    descentData_isIso_of_isIso_components _ (fun _ ↦ inferInstanceAs
      (IsIso (objectComparison F D).hom))
  exact asIso (comparisonHom F D)

private lemma family_map_ι {S : Scheme.{u}} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (T : DescentData.FamilyCoproductEquivalence f)
    {D E : DescentData f} (φ : D ⟶ E) (i : I) :
    Sigma.ι (fun i ↦ (D.obj i).left) i ≫ (T.objIso D).inv.left ≫
      ((T.equivalence.functor.map φ).hom ()).left =
    (φ.hom i).left ≫ Sigma.ι (fun i ↦ (E.obj i).left) i ≫ (T.objIso E).inv.left := by
  apply (cancel_mono (T.objIso E).hom.left).mp
  simp only [Category.assoc, ← T.map φ]
  simp [← Over.comp_left]

private lemma componentMap_naturality (F : MorphismOfSchemeFamilies.{u})
    {D E : DescentData F.targetFamily.f} (φ : D ⟶ E) (i : F.sourceFamily.I₀) :
    (((familyPB F).functor.map φ).hom i).left ≫ componentMap F E i =
      componentMap F D i ≫ (φ.hom (F.familyHom.s₀ i)).left := by
  have h := congrArg (fun k ↦ k.left ≫ pullback.fst _ _) ((familyPB F).map D E φ i)
  simpa [componentMap, componentIso, Over.pullback_map_left, Category.assoc] using h.symm

private lemma comparison_naturality (F : MorphismOfSchemeFamilies.{u})
    {D E : DescentData F.targetFamily.f} (φ : D ⟶ E) :
    (((familyPB F).functor ⋙ (sourceEquiv F).equivalence.functor).map φ) ≫
      (comparisonIso F E).hom =
    (comparisonIso F D).hom ≫
      (((targetEquiv F).equivalence.functor ⋙ (singletonPB F).functor).map φ) := by
  apply DescentData.hom_ext
  rintro ⟨⟩
  apply Over.OverMorphism.ext
  change (((sourceEquiv F).equivalence.functor.map ((familyPB F).functor.map φ)).hom ()).left ≫
      (objectComparison F E).hom.left =
    (objectComparison F D).hom.left ≫
      (((singletonPB F).functor.map ((targetEquiv F).equivalence.functor.map φ)).hom ()).left
  apply (cancel_mono
    ((singletonPB F).objIso ((targetEquiv F).equivalence.functor.obj E)).hom.left).mp
  apply pullback.hom_ext
  · have h := congrArg (fun k ↦ k.left)
      ((singletonPB F).map ((targetEquiv F).equivalence.functor.map φ))
    simp only [Over.comp_left] at h
    simp only [Category.assoc, ← reassoc_of% h, Over.pullback_map_left, pullback.lift_fst]
    have : IsIso ((sourceEquiv F).objIso (localDatum F D)).inv.left :=
      ((Over.forget _).mapIso ((sourceEquiv F).objIso (localDatum F D)).symm).isIso_hom
    apply (cancel_epi ((sourceEquiv F).objIso (localDatum F D)).inv.left).mp
    apply Sigma.hom_ext
    intro i
    simp only [reassoc_of% (family_map_ι (sourceEquiv F) ((familyPB F).functor.map φ) i),
      objectComparison_fst F E i, reassoc_of% (objectComparison_fst F D i)]
    change (((familyPB F).functor.map φ).hom i).left ≫ componentMap F E i ≫
        Sigma.ι (fun j ↦ (E.obj j).left) (F.familyHom.s₀ i) ≫ ((targetEquiv F).objIso E).inv.left =
      componentMap F D i ≫ Sigma.ι (fun j ↦ (D.obj j).left) (F.familyHom.s₀ i) ≫
        ((targetEquiv F).objIso D).inv.left ≫
        (((targetEquiv F).equivalence.functor.map φ).hom ()).left
    simp only [componentMap, Category.assoc]
    rw [reassoc_of% (componentMap_naturality F φ i), family_map_ι]
  · simp only [Category.assoc]
    rw [← Over.pullback_obj_hom, Over.w, Over.w, Over.w, Over.w]
    exact (Over.w (objectComparison F D).hom).symm

/-- Agreement between pullback for a family and pullback for its coproduct
morphism, including the canonical description of every component. -/
public structure PullbackCompatibility (F : MorphismOfSchemeFamilies.{u}) where
  /-- The natural comparison after the two family–coproduct equivalences. -/
  iso :
    (DescentData.familyCoproductEquivalence F.targetFamily.f).equivalence.functor ⋙
        (DescentData.pullbackFunctor (Sigma.desc F.targetFamily.f)
          (Sigma.desc F.sourceFamily.f) F.baseHom F.coproductHom
          F.coproductHom_comp).functor ≅
      (MorphismOfSchemeFamilies.pullbackFunctor F).functor ⋙
        (DescentData.familyCoproductEquivalence F.sourceFamily.f).equivalence.functor
  /-- On each member, the comparison has the canonical projection to the
  original descent object. -/
  fst (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    Sigma.ι
        (fun i ↦
          (((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj D).obj i).left) i ≫
        ((DescentData.familyCoproductEquivalence F.sourceFamily.f).objIso
          ((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj D)).inv.left ≫
        ((iso.inv.app D).hom ()).left ≫
        ((DescentData.pullbackFunctor (Sigma.desc F.targetFamily.f)
          (Sigma.desc F.sourceFamily.f) F.baseHom F.coproductHom
          F.coproductHom_comp).objIso
            ((DescentData.familyCoproductEquivalence
              F.targetFamily.f).equivalence.functor.obj D)).hom.left ≫
        pullback.fst _ _ =
      ((eqToHom ((MorphismOfSchemeFamilies.pullbackFunctor F).obj_eq D)).hom i).left ≫
        (MorphismOfSchemeFamilies.pulledBackDatumObjIso F D i).hom.left ≫
        pullback.fst _ _ ≫
        Sigma.ι (fun j ↦ (D.obj j).left) (F.familyHom.s₀ i) ≫
        ((DescentData.familyCoproductEquivalence F.targetFamily.f).objIso D).inv.left
  /-- On each member, the comparison has the canonical projection to the
  source coproduct. -/
  snd (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    Sigma.ι
        (fun i ↦
          (((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj D).obj i).left) i ≫
        ((DescentData.familyCoproductEquivalence F.sourceFamily.f).objIso
          ((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj D)).inv.left ≫
        ((iso.inv.app D).hom ()).left ≫
        ((DescentData.pullbackFunctor (Sigma.desc F.targetFamily.f)
          (Sigma.desc F.sourceFamily.f) F.baseHom F.coproductHom
          F.coproductHom_comp).objIso
            ((DescentData.familyCoproductEquivalence
              F.targetFamily.f).equivalence.functor.obj D)).hom.left ≫
        pullback.snd _ _ =
      (((MorphismOfSchemeFamilies.pullbackFunctor F).functor.obj D).obj i).hom ≫
        Sigma.ι (fun i ↦ F.sourceFamily.X i) i

private theorem pullbackCompatibility_nonempty (F : MorphismOfSchemeFamilies.{u}) :
  Nonempty (PullbackCompatibility F) := by
  refine ⟨⟨(NatIso.ofComponents (comparisonIso F)
    (fun φ ↦ comparison_naturality F φ)).symm, ?_, ?_⟩⟩
  · intro D i
    simpa only [componentIso, Functor.mapIso_hom, Iso.trans_hom, eqToIso.hom,
      Over.comp_left, DescentData.evaluation_map, Category.assoc] using!
        objectComparison_fst F D i
  · intro D i
    exact objectComparison_snd F D i

/-- Pullback of descent data commutes canonically with the equivalence between
a family and its coproduct morphism. -/
@[stacks 02VS "compatibility"]
public noncomputable def pullbackCompatibility
    (F : MorphismOfSchemeFamilies.{u}) : PullbackCompatibility F :=
  Classical.choice (by exact pullbackCompatibility_nonempty F)

end AlgebraicGeometry.MorphismOfSchemeFamilies
