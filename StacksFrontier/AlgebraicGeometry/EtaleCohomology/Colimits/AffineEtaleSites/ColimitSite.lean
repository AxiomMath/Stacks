module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.StrictModels
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.BaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.CoveringsAndDescent
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.StrictModels

/-!
# The affine étale site of a limit as a colimit site

The canonical datum `Stacks.EtaleCohomology.affineEtaleSiteColimit` and the clauses of
Stacks 0EYL: the level coverings, descent of objects and morphisms, the coverings of the limit
site, and `Stacks.EtaleCohomology.affineEtaleSiteColimit_isColimitPrecoverage`, the colimit site
in the sense of Stacks 09YL.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)

section Construction

/-- **Stacks 0EYL.** Let `I` be a directed set, let `(X_i, f_{i'i})` be an inverse system of
schemes over `I` with affine transition morphisms and let `X = lim X_i`.  Then
`X_{affine, étale} = colim (X_i)_{affine, étale}` as sites in the sense of Stacks 09YL. -/
@[stacks 0EYL "canonical site system", no_expose]
public noncomputable def affineEtaleSiteColimit (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] :
    AffineEtaleSiteColimit D c B hD hX where
  system := smallModelSystem D c B hD hX hc
  indexEquiv := CategoryTheory.Equivalence.refl
  levelEquiv := smallModelEquiv D c B hD hX hc
  toLimit := smallModelToLimit D c B hD hX
  toLimit_transition := smallModelRestrict_toLimit D c B hD hX
  transitionFst := smallModelTransitionFst D c B hD hX hc
  transition_isPullback a A := modelTransitionFst_isPullback D c B hD hX a (ULift.down A)
  transitionFst_id i A := by
    change modelTransitionFst D c B hD hX (𝟙 i) (ULift.down A) = 𝟙 _
    exact modelTransitionFst_id D c B hD hX i (ULift.down A)
  transitionFst_comp a b A := by
    change modelTransitionFst D c B hD hX (a ≫ b) (ULift.down A) = 𝟙 _ ≫ _ ≫ _
    rw [Category.id_comp]
    exact modelTransitionFst_comp D c B hD hX a b (ULift.down A)
  toLimitFst := smallModelLimitFst D c B hD hX hc
  toLimit_isPullback i A := modelLimitFst_isPullback D c B hD hX (ULift.down A)
  toLimitFst_transition a A := by
    change modelLimitFst D c B hD hX (ULift.down A) = 𝟙 _ ≫ _ ≫ _
    rw [Category.id_comp]
    exact (modelLimitFst_transition D c B hD hX a (ULift.down A)).symm

variable (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- An object of a stage site, pulled back to the limit, remains affine étale. -/
private noncomputable abbrev limitBaseChangeObject (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    AlgebraicGeometry.SmallAffineEtale B c.pt hX := by
  letI : IsAffineHom (c.π.app i) := limitProjection_affine hc i
  exact affineEtaleBaseChangeObject B (hD i) hX (c.π.app i) Y

/-- Pullback to the limit has its canonical projection square. -/
private lemma limitBaseChangeObject_isPullback (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    IsPullback (pullback.fst (affineEtaleStructureMorphism D B hD i Y) (c.π.app i))
      (limitAffineEtaleStructureMorphism D c B hX (limitBaseChangeObject D c B hD hX hc i Y))
      (affineEtaleStructureMorphism D B hD i Y) (c.π.app i) := by
  let : IsAffineHom (c.π.app i) := limitProjection_affine hc i
  exact affineEtaleBaseChangeObject_isPullback B (hD i) hX (c.π.app i) Y

/-- The level equivalences identify the Grothendieck topologies: a presieve is covering at a
stage exactly when its image generates a covering sieve of the corresponding affine étale site.
Finiteness is not imposed here, since an equivalence can identify distinct isomorphic source
objects and need not reflect finiteness of a particular presieve. -/
@[stacks 0EYL "level coverings"]
public theorem affineEtaleSiteColimit_level_cover
    (i : (affineEtaleSiteColimit D c B hD hX hc).system.I)
    (Y : (affineEtaleSiteColimit D c B hD hX hc).system.C i) (R : Presieve Y) :
    R ∈ ((affineEtaleSiteColimit D c B hD hX hc).system.J i).toPrecoverage Y ↔
      R.map ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor ∈
        (AlgebraicGeometry.SmallAffineEtale.topology B
          (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
          (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj
            i))).toPrecoverage
          (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y) :=
  smallModelTopology_cover D c B hD hX hc i Y R

/-- **The level equivalences identify the Grothendieck topologies, in the form of a dense
subsite.** The topology of a level is the topology induced on the category of representatives by
the level equivalence, so that equivalence's functor is a dense subsite of the small affine étale
site of the corresponding `X_i`.

This is `affineEtaleSiteColimit_level_cover` in the form typeclass inference consumes.  The
covering correspondence is a statement about presieves; transporting sheaves across a level needs
continuity of the functor as an *instance*, and `CategoryTheory.Functor.IsDenseSubsite` carries
both that and the cover-lifting direction.  Nothing is asserted beyond the covering
correspondence: the content is that it holds for sieves at every object, which is what makes the
induced topology the topology of the level. -/
@[stacks 0EYL "level coverings, as a dense subsite"]
public theorem affineEtaleSiteColimit_levelEquiv_isDenseSubsite
    (i : (affineEtaleSiteColimit D c B hD hX hc).system.I) :
    ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.IsDenseSubsite
      ((affineEtaleSiteColimit D c B hD hX hc).system.J i)
      (AlgebraicGeometry.SmallAffineEtale.topology B
        (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
        (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))) :=
  smallModelEquiv_dense D c B hD hX hc i

/-- **A level of the system, carried into the small étale site of its scheme, is a morphism of
sites.** The composite of the level equivalence with the inclusion of Stacks 04HR is continuous
from the topology of the level to the small étale topology of `X_i`.

This is the level-side counterpart of
`Stacks.EtaleCohomology.AffineLimitCohomology.isContinuous_limitToSmallEtale`, and unlike that one
it is not a universe raising followed by 04HR: a level of this system is a category of
representatives, equivalent to the small affine étale site of `X_i` but not equal to it, so the
first factor is the level equivalence and its continuity is
`affineEtaleSiteColimit_levelEquiv_isDenseSubsite`.  Without this a sheaf on the small étale site
of `X_i` cannot be read on the level at all. -/
@[stacks 0EYL "levels as morphisms of sites to the small étale sites"]
public theorem affineEtaleSiteColimit_levelToSmallEtale_isContinuous
    (i : (affineEtaleSiteColimit D c B hD hX hc).system.I) :
    (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor ⋙
        AlgebraicGeometry.SmallAffineEtale.inclusion B
          (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
          (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj
            i))).IsContinuous
      ((affineEtaleSiteColimit D c B hD hX hc).system.J i)
      (AlgebraicGeometry.SmallEtale.topology B
        (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
        (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))) :=
  smallModelToEtale_continuous D c B hD hX hc i

/-- **Restriction of sheaves of sets from the small étale site of `X_i` to a level is an
equivalence.** Both factors of the crossing are: the level equivalence by
`affineEtaleSiteColimit_levelEquiv_isDenseSubsite`, and the inclusion of the small affine étale
site by Stacks 04HR.

This says that reading a sheaf of a level as the restriction of a sheaf on the small étale site of
`X_i` is no restriction on the level sheaf: every one of them is isomorphic to such a restriction,
and every map of them to a map of those. -/
@[stacks 0EYL "sheaves of a level are sheaves of the small étale site of its scheme"]
public theorem affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv
    (i : (affineEtaleSiteColimit D c B hD hX hc).system.I) :
    letI := affineEtaleSiteColimit_levelToSmallEtale_isContinuous D c B hD hX hc i
    ((((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor ⋙
      AlgebraicGeometry.SmallAffineEtale.inclusion B
        (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
        (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj
          i))).sheafPushforwardContinuous (Type (max u v + 1))
      ((affineEtaleSiteColimit D c B hD hX hc).system.J i)
      (AlgebraicGeometry.SmallEtale.topology B
        (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
        (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj
          i)))).IsEquivalence :=
  smallModelToEtale_sheafEquiv D c B hD hX hc i

/-- A morphism into the image of an object of an equivalence lifts, up to the counit, to a
morphism of the source category. -/
private lemma exists_functor_map_eq_comp {J K : Type*} [Category J] [Category K] (Φ : J ≌ K)
    {i : J} {k : K} (e : k ⟶ Φ.functor.obj i) :
    ∃ (j : J) (a : j ⟶ i) (b : Φ.functor.obj j ⟶ k), Φ.functor.map a = b ≫ e :=
  ⟨Φ.inverse.obj k, Φ.functor.preimage (Φ.counitIso.hom.app k ≫ e), Φ.counitIso.hom.app k,
    Φ.functor.map_preimage _⟩

/-- Every affine étale object over the limit descends to a finite stage. -/
@[stacks 0EYL "objects"]
public theorem affineEtaleSiteColimit_obj_descends
    (Z : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    ∃ (i : (affineEtaleSiteColimit D c B hD hX hc).system.I)
      (Y : (affineEtaleSiteColimit D c B hD hX hc).system.C i),
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y = Z :=
  smallModel_obj_descends D c B hD hX hc Z

/-- Every morphism between objects descended from one stage descends after increasing the
stage. -/
@[stacks 0EYL "morphisms"]
public theorem affineEtaleSiteColimit_hom_descends
    (i : (affineEtaleSiteColimit D c B hD hX hc).system.I)
    (X Y : (affineEtaleSiteColimit D c B hD hX hc).system.C i)
    (f : ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj X ⟶
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y) :
    ∃ (j : (affineEtaleSiteColimit D c B hD hX hc).system.I) (a : j ⟶ i)
      (g : ((affineEtaleSiteColimit D c B hD hX hc).system.u a).obj X ⟶
        ((affineEtaleSiteColimit D c B hD hX hc).system.u a).obj Y),
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit j).map g =
        eqToHom (Functor.congr_obj
          ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a) X) ≫ f ≫
          eqToHom (Functor.congr_obj
            ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a) Y).symm := by
  let E := affineEtaleSiteColimit D c B hD hX hc
  let i₀ := E.indexEquiv.functor.obj i
  let F := (E.levelEquiv i).functor ⋙ affineEtaleToOver B (D.obj i₀) (hD i₀)
  let Q := affineEtaleToOver B c.pt hX
  have : Q.Faithful := {
    map_injective := by
      intro A A' f g h
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      exact congrArg Over.Hom.left h }
  obtain ⟨j₀, hij, g₀, s, t, hs₁, hs₂, ht₁, ht₂, hst⟩ :=
    exists_hom_of_isPullback D c hc i₀.unop (F.obj X) (F.obj Y)
      (affineEtaleSource_compact D B hD i₀ ((E.levelEquiv i).functor.obj X))
      (affineEtaleSource_quasiSeparated D B hD i₀ ((E.levelEquiv i).functor.obj X))
      (affineEtaleSource_compact D B hD i₀ ((E.levelEquiv i).functor.obj Y))
      (affineEtaleSource_quasiSeparated D B hD i₀ ((E.levelEquiv i).functor.obj Y))
      (affineEtaleStructureMorphism_locallyFinitePresentation D B hD i₀
        ((E.levelEquiv i).functor.obj X))
      (affineEtaleStructureMorphism_locallyFinitePresentation D B hD i₀
        ((E.levelEquiv i).functor.obj Y))
      (Q.obj ((E.toLimit i).obj X)) (Q.obj ((E.toLimit i).obj Y))
      ((E.toLimitFst i).app X) ((E.toLimitFst i).app Y)
      (E.toLimit_isPullback i X) (E.toLimit_isPullback i Y) (Q.map f)
  let e : Opposite.op j₀ ⟶ i₀ := (homOfLE hij).op
  obtain ⟨j, a, b, ha⟩ := exists_functor_map_eq_comp E.indexEquiv e
  change s ≫ pullback.fst (F.obj X).hom (D.map e) = (E.toLimitFst i).app X at hs₁
  change s ≫ pullback.snd (F.obj X).hom (D.map e) =
    (Q.obj ((E.toLimit i).obj X)).hom ≫ c.π.app (Opposite.op j₀) at hs₂
  change t ≫ pullback.fst (F.obj Y).hom (D.map e) = (E.toLimitFst i).app Y at ht₁
  have hg₀ : g₀.left ≫ pullback.snd (F.obj Y).hom (D.map e) =
      pullback.snd (F.obj X).hom (D.map e) := Over.w g₀
  let G := (E.levelEquiv j).functor ⋙
    affineEtaleToOver B (D.obj (E.indexEquiv.functor.obj j)) (hD _)
  let Xj := (E.system.u a).obj X
  let Yj := (E.system.u a).obj Y
  let p : (G.obj Xj).left ⟶ (F.obj X).left := (E.transitionFst a).app X
  have hw : p ≫ (F.obj X).hom = ((G.obj Xj).hom ≫ D.map b) ≫ D.map e :=
    by
      rw [Category.assoc, ← D.map_comp, ← ha]
      exact (E.transition_isPullback a X).w
  let s₀ := pullback.lift p ((G.obj Xj).hom ≫ D.map b) hw
  have hs₀₁ : s₀ ≫ pullback.fst (F.obj X).hom (D.map e) = p :=
    pullback.lift_fst _ _ _
  have hs₀₂ : s₀ ≫ pullback.snd (F.obj X).hom (D.map e) =
      (G.obj Xj).hom ≫ D.map b := pullback.lift_snd _ _ _
  have hr : (s₀ ≫ g₀.left ≫ pullback.fst (F.obj Y).hom (D.map e)) ≫
      (F.obj Y).hom = (G.obj Xj).hom ≫ D.map (E.indexEquiv.functor.map a) := by
    calc
      _ = s₀ ≫ g₀.left ≫ pullback.snd (F.obj Y).hom (D.map e) ≫ D.map e := by
        rw [Category.assoc, Category.assoc, pullback.condition]
      _ = s₀ ≫ pullback.snd (F.obj X).hom (D.map e) ≫ D.map e := by
        rw [← Category.assoc g₀.left, hg₀]
      _ = _ := by rw [← Category.assoc, hs₀₂, Category.assoc, ← D.map_comp, ← ha]
  let r := (E.transition_isPullback a Y).lift
    (s₀ ≫ g₀.left ≫ pullback.fst (F.obj Y).hom (D.map e)) (G.obj Xj).hom hr
  let k₀ : G.obj Xj ⟶ G.obj Yj :=
    Over.homMk r ((E.transition_isPullback a Y).lift_snd _ _ _)
  let k : Xj ⟶ Yj := G.preimage k₀
  have hk : (G.map k).left = r := congrArg Over.Hom.left (G.map_preimage k₀)
  let δ (T : E.system.C i) : (E.toLimit j).obj ((E.system.u a).obj T) ⟶
      (E.toLimit i).obj T := eqToHom (Functor.congr_obj (E.toLimit_transition a) T)
  have hδ (T : E.system.C i) :
      (Q.map (δ T)).left ≫ (E.toLimitFst i).app T =
        (E.toLimitFst j).app ((E.system.u a).obj T) ≫ (E.transitionFst a).app T := by
    change (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map (δ T) ≫ _ = _
    rw [E.toLimitFst_transition a T]
    simp [δ, ← Category.assoc]
  have hpj : (E.toLimitFst j).app Xj ≫ (G.obj Xj).hom =
      (Q.obj ((E.toLimit j).obj Xj)).hom ≫
        c.π.app (E.indexEquiv.functor.obj j) := (E.toLimit_isPullback j Xj).w
  have hs : (E.toLimitFst j).app Xj ≫ s₀ = (Q.map (δ X)).left ≫ s := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (E.toLimitFst j).app Xj ≫ z) hs₀₁).trans ?_
      refine (hδ X).symm.trans ?_
      refine (congrArg (fun z => (Q.map (δ X)).left ≫ z) hs₁).symm.trans ?_
      exact (Category.assoc _ _ _).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (E.toLimitFst j).app Xj ≫ z) hs₀₂).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ D.map b) hpj).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (Q.obj ((E.toLimit j).obj Xj)).hom ≫ z) (c.w b)).trans ?_
      refine (congrArg (fun z => z ≫ c.π.app (Opposite.op j₀))
        (Over.w (Q.map (δ X))).symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (Q.map (δ X)).left ≫ z) hs₂.symm).trans ?_
      exact (Category.assoc _ _ _).symm
  have hnat : (Q.map ((E.toLimit j).map k)).left ≫ (E.toLimitFst j).app Yj =
      (E.toLimitFst j).app Xj ≫ r := by
    have h := (E.toLimitFst j).naturality k
    change (Q.map ((E.toLimit j).map k)).left ≫ (E.toLimitFst j).app Yj =
      (E.toLimitFst j).app Xj ≫ (G.map k).left at h
    rwa [hk] at h
  have hdesc : (E.toLimit j).map k ≫ δ Y = δ X ≫ f := by
    apply Q.map_injective
    apply Over.OverMorphism.ext
    apply (E.toLimit_isPullback i Y).hom_ext
    · change ((Q.map ((E.toLimit j).map k)).left ≫ (Q.map (δ Y)).left) ≫
          (E.toLimitFst i).app Y =
        ((Q.map (δ X)).left ≫ (Q.map f).left) ≫ (E.toLimitFst i).app Y
      have hsg : s ≫ g₀.left ≫ pullback.fst (F.obj Y).hom (D.map e) =
          (Q.map f).left ≫ (E.toLimitFst i).app Y := by
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (fun z => z ≫ pullback.fst (F.obj Y).hom (D.map e)) hst).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        exact congrArg (fun z => (Q.map f).left ≫ z) ht₁
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (Q.map ((E.toLimit j).map k)).left ≫ z) (hδ Y)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ (E.transitionFst a).app Y) hnat).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (E.toLimitFst j).app Xj ≫ z)
        ((E.transition_isPullback a Y).lift_fst _ _ _)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun z => z ≫ g₀.left ≫ pullback.fst (F.obj Y).hom (D.map e))
        hs).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => (Q.map (δ X)).left ≫ z) hsg).trans ?_
      exact (Category.assoc _ _ _).symm
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨j, a, k, ?_⟩
  change (E.toLimit j).map k = f
  change (E.toLimit j).map k ≫ 𝟙 _ = 𝟙 _ ≫ f at hdesc
  simpa only [Category.comp_id, Category.id_comp] using hdesc


/-- Two morphisms that agree over the limit agree after increasing the stage. -/
@[stacks 0EYL "faithfulness"]
public theorem affineEtaleSiteColimit_hom_eventually_eq
    (i : (affineEtaleSiteColimit D c B hD hX hc).system.I)
    (X Y : (affineEtaleSiteColimit D c B hD hX hc).system.C i)
    (f g : X ⟶ Y)
    (hfg : ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).map f =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).map g) :
    ∃ (j : (affineEtaleSiteColimit D c B hD hX hc).system.I) (a : j ⟶ i),
      ((affineEtaleSiteColimit D c B hD hX hc).system.u a).map f =
        ((affineEtaleSiteColimit D c B hD hX hc).system.u a).map g  := by
  let E := affineEtaleSiteColimit D c B hD hX hc
  let i₀ := E.indexEquiv.functor.obj i
  let F := (E.levelEquiv i).functor ⋙ affineEtaleToOver B (D.obj i₀) (hD i₀)
  have hlim : (Over.pullback (c.π.app i₀)).map (F.map f) =
      (Over.pullback (c.π.app i₀)).map (F.map g) := by
    apply pullback_map_eq_of_comp_eq (c.π.app i₀)
      ((E.toLimitFst i).app X)
      (limitAffineEtaleStructureMorphism D c B hX ((E.toLimit i).obj X))
      (E.toLimit_isPullback i X)
    change (E.toLimitFst i).app X ≫
        ((E.levelEquiv i).functor ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B
          (D.obj i₀) (hD i₀)).map f =
      (E.toLimitFst i).app X ≫
        ((E.levelEquiv i).functor ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B
          (D.obj i₀) (hD i₀)).map g
    rw [← (E.toLimitFst i).naturality f, ← (E.toLimitFst i).naturality g]
    change (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map ((E.toLimit i).map f) ≫ _ = _
    rw [hfg]
    rfl
  obtain ⟨j₀, hij, heq⟩ :=
    AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_small D c hc i₀.unop
    (F.obj X) (F.obj Y)
    (affineEtaleSource_compact D B hD i₀ ((E.levelEquiv i).functor.obj X))
    (affineEtaleSource_quasiSeparated D B hD i₀ ((E.levelEquiv i).functor.obj X))
    (affineEtaleSource_compact D B hD i₀ ((E.levelEquiv i).functor.obj Y))
    (affineEtaleSource_quasiSeparated D B hD i₀ ((E.levelEquiv i).functor.obj Y))
    (affineEtaleStructureMorphism_locallyFinitePresentation D B hD i₀
      ((E.levelEquiv i).functor.obj X))
    (affineEtaleStructureMorphism_locallyFinitePresentation D B hD i₀
      ((E.levelEquiv i).functor.obj Y))
    (F.map f) (F.map g) hlim
  let e : Opposite.op j₀ ⟶ i₀ := (homOfLE hij).op
  obtain ⟨j, a, b, ha⟩ := exists_functor_map_eq_comp E.indexEquiv e
  refine ⟨j, a, ?_⟩
  apply (E.levelEquiv j).functor.map_injective
  apply (affineEtaleToOver B (D.obj (E.indexEquiv.functor.obj j))
    (hD (E.indexEquiv.functor.obj j))).map_injective
  apply Over.OverMorphism.ext
  apply (E.transition_isPullback a Y).hom_ext
  · have heq' := comp_eq_of_pullback_map_eq (D.map e) (F.map f) (F.map g) heq
    let p : (AlgebraicGeometry.SmallAffineEtale.toScheme B
        (D.obj (E.indexEquiv.functor.obj j)) (hD (E.indexEquiv.functor.obj j))).obj
          ((E.levelEquiv j).functor.obj ((E.system.u a).obj X)) ⟶ (F.obj X).left :=
      (E.transitionFst a).app X
    let t := affineEtaleStructureMorphism D B hD (E.indexEquiv.functor.obj j)
      ((E.levelEquiv j).functor.obj ((E.system.u a).obj X))
    have hw : p ≫ (F.obj X).hom = (t ≫ D.map b) ≫ D.map e := by
      rw [Category.assoc, ← D.map_comp, ← ha]
      exact (E.transition_isPullback a X).w
    have hcomp : p ≫ (F.map f).left = p ≫ (F.map g).left := by
      have h := congrArg (fun z => pullback.lift p (t ≫ D.map b) hw ≫ z) heq'
      simpa only [← Category.assoc, pullback.lift_fst] using h
    change ((E.system.u a ⋙ (E.levelEquiv j).functor ⋙
        AlgebraicGeometry.SmallAffineEtale.toScheme B _ _).map f) ≫
        (E.transitionFst a).app Y =
      ((E.system.u a ⋙ (E.levelEquiv j).functor ⋙
        AlgebraicGeometry.SmallAffineEtale.toScheme B _ _).map g) ≫
        (E.transitionFst a).app Y
    rw [(E.transitionFst a).naturality f, (E.transitionFst a).naturality g]
    exact hcomp
  · exact (Over.w _).trans (Over.w _).symm




private lemma exists_stage_range_subset_index (hc : IsLimit c)
    {Y : Scheme.{max u v}} [IsAffine Y] (i : Iᵒᵖ) (q : Y ⟶ D.obj i)
    (E : Set Y) (hE : Topology.IsConstructible E)
    (hlim : ∀ (p : c.pt) (y : Y), (c.π.app i) p = q y → y ∈ E) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i), ∀ (p : D.obj j) (y : Y), D.map a p = q y → y ∈ E := by
  let F : AsSmall.{max u v} Iᵒᵖ ⥤ Iᵒᵖ := AsSmall.down
  have : F.IsEquivalence :=
    (AsSmall.equiv : Iᵒᵖ ≌ AsSmall.{max u v} Iᵒᵖ).isEquivalence_inverse
  have : IsCofiltered (AsSmall.{max u v} Iᵒᵖ) :=
    IsCofiltered.of_equivalence (AsSmall.equiv : Iᵒᵖ ≌ AsSmall.{max u v} Iᵒᵖ)
  have {j k : AsSmall.{max u v} Iᵒᵖ} (a : j ⟶ k) : IsAffineHom ((F ⋙ D).map a) :=
    show IsAffineHom (D.map (F.map a)) from inferInstance
  obtain ⟨j, a, ha⟩ := exists_stage_range_subset (F ⋙ D) (c.whisker F)
    ((Functor.Initial.isLimitWhiskerEquiv F c).symm hc) (AsSmall.up.obj i) q E hE hlim
  exact ⟨F.obj j, F.map a, ha⟩

private lemma smallModel_cover_eventually (i : Iᵒᵖ)
    (A : SmallModelAt D c B hD hX i) (E : PreZeroHypercover.{max u v + 1} A)
    [Finite E.I₀]
    (hE : E.presieve₀.map (smallModelToLimit D c B hD hX i) ∈
      AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX
        ((smallModelToLimit D c B hD hX i).obj A)) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i), E.presieve₀.map (smallModelRestrict D c B hD hX a) ∈
      (smallModelTopology D c B hD hX hc j).toPrecoverage
        ((smallModelRestrict D c B hD hX a).obj A) := by
  let F := smallModelToOver D c B hD hX hc i
  let G := smallModelToLimit D c B hD hX i ⋙ affineEtaleToOver B c.pt hX
  let p := smallModelLimitFst D c B hD hX hc i
  have hp (V) : IsPullback (p.app V) (G.obj V).hom (F.obj V).hom (c.π.app i) :=
    modelLimitFst_isPullback D c B hD hX (ULift.down V)
  have : IsAffine (F.obj A).left :=
    ((smallModelEquiv D c B hD hX hc i).functor.obj A).property
  have (t : E.I₀) : IsAffine (F.obj (E.X t)).left :=
    ((smallModelEquiv D c B hD hX hc i).functor.obj (E.X t)).property
  have (t : E.I₀) : Etale (F.map (E.f t)).left :=
    affineEtale_hom_etale B (D.obj i) (hD i)
      ((smallModelEquiv D c B hD hX hc i).functor.map (E.f t))
  let U : Set (F.obj A).left := ⋃ t, Set.range (F.map (E.f t)).left
  have hU : Topology.IsConstructible U := Topology.IsConstructible.iUnion fun t => by
    simpa only [Set.image_univ] using
      ((F.map (E.f t)).left.isLocallyConstructible_image
        Topology.IsLocallyConstructible.univ).isConstructible
  have hcov : ∀ z : (G.obj A).left, ∃ t, z ∈ Set.range (G.map (E.f t)).left := by
    have h := ((mem_smallAffineEtale_precoverage_iff B c.pt hX _ _).mp hE).2
    rw [← PreZeroHypercover.presieve₀_map, ← PreZeroHypercover.presieve₀_map] at h
    exact (Scheme.presieve₀_mem_precoverage_iff _).mp h |>.1
  have hlim (x : c.pt) (y : (F.obj A).left)
      (hxy : (c.π.app i) x = (F.obj A).hom y) : y ∈ U := by
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback y x hxy.symm
    let w := (hp A).isoPullback.inv z
    have hw : p.app A w = y :=
      (congrArg (fun f => f z) (hp A).isoPullback_inv_fst).trans hz
    obtain ⟨t, v, hv⟩ := hcov w
    apply Set.mem_iUnion.mpr
    refine ⟨t, p.app (E.X t) v, ?_⟩
    have hn := congrArg (fun f => f v) (p.naturality (E.f t))
    change p.app A ((G.map (E.f t)).left v) = (F.map (E.f t)).left (p.app (E.X t) v) at hn
    exact hn.symm.trans (hv ▸ hw)
  obtain ⟨j, a, ha⟩ := exists_stage_range_subset_index D c hc i (F.obj A).hom U hU hlim
  refine ⟨j, a, ?_⟩
  apply (smallModelTopology_cover D c B hD hX hc j _ _).mpr
  apply (AlgebraicGeometry.SmallAffineEtale.precoverage B (D.obj j)
    (hD j)).generate_mem_toGrothendieck
  apply (mem_smallAffineEtale_precoverage_iff B (D.obj j) (hD j) _ _).mpr
  refine ⟨finite_presieve_map _
    (finite_presieve_map _ (Precoverage.ofArrows_mem_finite E.X E.f)), ?_⟩
  rw [← PreZeroHypercover.presieve₀_map, ← PreZeroHypercover.presieve₀_map,
    ← PreZeroHypercover.presieve₀_map]
  apply (Scheme.presieve₀_mem_precoverage_iff _).mpr
  constructor
  · intro y
    let G' := smallModelRestrict D c B hD hX a ⋙ smallModelToOver D c B hD hX hc j
    let p' := smallModelTransitionFst D c B hD hX hc a
    have hp' (V) : IsPullback (p'.app V) (G'.obj V).hom (F.obj V).hom (D.map a) :=
      modelTransitionFst_isPullback D c B hD hX a (ULift.down V)
    have hy : D.map a ((G'.obj A).hom y) = (F.obj A).hom (p'.app A y) :=
      (congrArg (fun f => f y) (hp' A).w).symm
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (ha ((G'.obj A).hom y) (p'.app A y) hy)
    refine ⟨t, ?_⟩
    exact (mem_range_of_isPullback
      (chosen_baseChange_map_isPullback (D.map a) F G' p' hp' (E.f t)) y).mpr ht
  · intro t
    exact affineEtale_hom_etale B (D.obj j) (hD j)
      ((smallModelEquiv D c B hD hX hc j).functor.map
        ((smallModelRestrict D c B hD hX a).map (E.f t)))

-- Comparing these concrete functors unfolds their dependent representative object types.
omit [Nonempty I] [IsDirected I (· ≤ ·)] in
private lemma smallModelRestrict_toLimit_map {i j : Iᵒᵖ} (a : i ⟶ j)
    {X Y : SmallModelAt D c B hD hX j} (f : X ⟶ Y) :
    (smallModelToLimit D c B hD hX i).map
      ((smallModelRestrict D c B hD hX a).map f) =
        (smallModelToLimit D c B hD hX j).map f :=
  eq_of_heq (Functor.hcongr_hom (smallModelRestrict_toLimit D c B hD hX a) f)

-- Synchronizing the family unfolds several compositions of representative functors.
private lemma smallModel_family_descends (hc : IsLimit c)
    {Z : AlgebraicGeometry.SmallAffineEtale B c.pt hX}
    (E : PreZeroHypercover.{max u v + 1} Z) [Finite E.I₀] :
    ∃ (i : Iᵒᵖ) (A : SmallModelAt D c B hD hX i)
      (hA : (smallModelToLimit D c B hD hX i).obj A = Z)
      (E' : PreZeroHypercover.{max u v + 1} A), Finite E'.I₀ ∧
        E.presieve₀ = hA ▸ E'.presieve₀.map (smallModelToLimit D c B hD hX i) := by
  classical
  obtain ⟨i, A, rfl⟩ := smallModel_obj_descends D c B hD hX hc Z
  choose k X hXk using fun t => smallModel_obj_descends D c B hD hX hc (E.X t)
  let : Fintype E.I₀ := Fintype.ofFinite _
  let indices : Finset Iᵒᵖ := insert i (Finset.univ.image k)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists indices
  let a₀ : j ⟶ i := Classical.choice (hj (Finset.mem_insert_self _ _))
  let a (t : E.I₀) : j ⟶ k t := Classical.choice
    (hj (Finset.mem_insert_of_mem (Finset.mem_image_of_mem k (Finset.mem_univ t))))
  let A' := (smallModelRestrict D c B hD hX a₀).obj A
  let V (t : E.I₀) := (smallModelRestrict D c B hD hX (a t)).obj (X t)
  have hV (t : E.I₀) : (smallModelToLimit D c B hD hX j).obj (V t) = E.X t := hXk t
  let f (t : E.I₀) : (smallModelToLimit D c B hD hX j).obj (V t) ⟶
      (smallModelToLimit D c B hD hX j).obj A' := eqToHom (hV t) ≫ E.f t
  have hhom (t : E.I₀) : ∃ (l : Iᵒᵖ) (b : l ⟶ j)
      (g : (smallModelRestrict D c B hD hX b).obj (V t) ⟶
        (smallModelRestrict D c B hD hX b).obj A'),
      (smallModelToLimit D c B hD hX l).map g = f t := by
    obtain ⟨l, b, g, hg⟩ :=
      affineEtaleSiteColimit_hom_descends D c B hD hX hc j (V t) A' (f t)
    refine ⟨l, b, g, ?_⟩
    change (smallModelToLimit D c B hD hX l).map g = 𝟙 _ ≫ f t ≫ 𝟙 _ at hg
    exact hg.trans ((Category.id_comp _).trans (Category.comp_id _))
  choose l b g hg using hhom
  obtain ⟨m, d, e, he⟩ := IsCofiltered.wideCospan b
  let A'' := (smallModelRestrict D c B hD hX d).obj A'
  let E' : PreZeroHypercover.{max u v + 1} A'' := {
    I₀ := E.I₀
    X t := (smallModelRestrict D c B hD hX d).obj (V t)
    f t := (smallModelRestrict D c B hD hX (e t)).map
      (X := (smallModelRestrict D c B hD hX (b t)).obj (V t))
      (Y := (smallModelRestrict D c B hD hX (b t)).obj A') (g t) }
  have hmap (t : E.I₀) : (smallModelToLimit D c B hD hX m).map (E'.f t) =
      eqToHom (hV t) ≫ E.f t := by
    change (smallModelRestrict D c B hD hX (e t) ⋙ smallModelToLimit D c B hD hX m).map
      (X := (smallModelRestrict D c B hD hX (b t)).obj (V t))
      (Y := (smallModelRestrict D c B hD hX (b t)).obj A') (g t) = _
    exact (smallModelRestrict_toLimit_map D c B hD hX (e t) (g t)).trans (hg t)
  refine ⟨m, A'', rfl, E', inferInstance, ?_⟩
  rw [← PreZeroHypercover.presieve₀_map]
  apply le_antisymm
  · rintro _ _ ⟨t⟩
    apply PreZeroHypercover.presieve₀_of_eq (E'.map (smallModelToLimit D c B hD hX m)) t
      (E.f t) (hV t).symm
    change E.f t = eqToHom (hV t).symm ≫
      (smallModelToLimit D c B hD hX m).map (X := E'.X t) (Y := A'') (E'.f t)
    refine Eq.symm ?_
    refine (congrArg (fun z => eqToHom (hV t).symm ≫ z) (hmap t)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ E.f t) (eqToHom_trans (hV t).symm (hV t))).trans ?_
    refine (congrArg (fun z => z ≫ E.f t) (eqToHom_refl _ _)).trans ?_
    exact Category.id_comp _
  · rintro _ _ ⟨t⟩
    exact PreZeroHypercover.presieve₀_of_eq E t _ (hV t) (hmap t)

/-- Coverings of the small affine étale site of the limit are exactly the images of finite
coverings from a stage. -/
@[stacks 0EYL "coverings"]
public theorem affineEtaleSiteColimit_mem_precoverage_iff
    (Z : AlgebraicGeometry.SmallAffineEtale B c.pt hX) (R : Presieve Z) :
    R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Z ↔
      ∃ (i : (affineEtaleSiteColimit D c B hD hX hc).system.I)
        (Y : (affineEtaleSiteColimit D c B hD hX hc).system.C i)
        (h : ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y = Z)
        (S : Presieve Y),
        S ∈ ((affineEtaleSiteColimit D c B hD hX hc).system.J i).toPrecoverage Y ∧
          S ∈ Precoverage.finite ((affineEtaleSiteColimit D c B hD hX hc).system.C i) Y ∧
          R = h ▸ S.map ((affineEtaleSiteColimit D c B hD hX hc).toLimit i) := by
  classical
  constructor
  · intro hR
    obtain ⟨E, rfl, hE⟩ :=
      (AlgebraicGeometry.SmallAffineEtale.mem_precoverage_iff B c.pt hX).mp hR
    have : Finite E.I₀ := hE.2
    obtain ⟨i, A, hA, E', hfin, hEq⟩ := smallModel_family_descends D c B hD hX hc E
    subst Z
    change E.presieve₀ = E'.presieve₀.map (smallModelToLimit D c B hD hX i) at hEq
    have : Finite E'.I₀ := hfin
    have hcov : E'.presieve₀.map (smallModelToLimit D c B hD hX i) ∈
        AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX _ := by
      rw [← hEq]
      exact (AlgebraicGeometry.SmallAffineEtale.mem_precoverage_iff B c.pt hX).mpr ⟨E, rfl, hE⟩
    obtain ⟨j, a, ha⟩ := smallModel_cover_eventually D c B hD hX hc i A E' hcov
    refine ⟨j, (smallModelRestrict D c B hD hX a).obj A, rfl,
      E'.presieve₀.map (smallModelRestrict D c B hD hX a), ha,
      finite_presieve_map (smallModelRestrict D c B hD hX a)
        (Precoverage.ofArrows_mem_finite E'.X E'.f), ?_⟩
    change E.presieve₀ = (E'.presieve₀.map (smallModelRestrict D c B hD hX a)).map
      (smallModelToLimit D c B hD hX j)
    rw [hEq]
    simp only [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
    congr 1
    funext t
    exact (smallModelRestrict_toLimit_map D c B hD hX a (E'.f t)).symm
  · rintro ⟨i, Y, h, S, hS, hfin, rfl⟩
    subst Z
    have := smallModelToLimit_continuous D c B hD hX hc i
    apply affineEtale_topology_finite_cover B c.pt hX _ _ (finite_presieve_map _ hfin)
    change S.map (smallModelToLimit D c B hD hX i) ∈
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX).toPrecoverage _
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    exact Set.mem_of_eq_of_mem
      (Sieve.generate_map_eq_functorPushforward (smallModelToLimit D c B hD hX i))
      ((CoverPreserving.of_isContinuous (smallModelToLimit D c B hD hX i)
        (smallModelTopology D c B hD hX hc i)
        (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX)).cover_preserve hS)

/-- **Stacks 0EYL**, the clause "as sites in the sense of Stacks 09YL". The standard étale
precoverage of the small affine étale site of the limit `X = lim X_i` *is* the colimit
precoverage that Stacks 09YL produces from the canonical system: its coverings are exactly the
images of the finite coverings of the stages, and it therefore satisfies the three axioms of a
site in the sense of Stacks 00VH — a one-element family given by an isomorphism is a covering,
coverings are stable under refinement by coverings, and the fibre products of a covering along
any morphism exist and again form a covering. -/
@[stacks 0EYL "colimit site"]
public theorem affineEtaleSiteColimit_isColimitPrecoverage :
    (∀ (Z : AlgebraicGeometry.SmallAffineEtale B c.pt hX) (R : Presieve Z),
        R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Z ↔
          ∃ (i : (affineEtaleSiteColimit D c B hD hX hc).system.I)
            (Y : (affineEtaleSiteColimit D c B hD hX hc).system.C i)
            (h : ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y = Z)
            (S : Presieve Y),
            S ∈ ((affineEtaleSiteColimit D c B hD hX hc).system.J i).toPrecoverage Y ∧
              S ∈ Precoverage.finite
                  ((affineEtaleSiteColimit D c B hD hX hc).system.C i) Y ∧
                R = h ▸ S.map ((affineEtaleSiteColimit D c B hD hX hc).toLimit i)) ∧
      (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX).HasIsos ∧
      (∀ (Z : AlgebraicGeometry.SmallAffineEtale B c.pt hX) (R : Presieve Z)
          (T : ∀ ⦃Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX⦄ (f : Y ⟶ Z),
            R f → Presieve Y),
          R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Z →
            (∀ ⦃Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX⦄ (f : Y ⟶ Z) (hf : R f),
                T f hf ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Y) →
              R.bind T ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Z) ∧
        ∃ _ : (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX).HasPullbacks,
          ∀ (Z W : AlgebraicGeometry.SmallAffineEtale B c.pt hX) (f : W ⟶ Z)
              (R : Presieve Z) [R.HasPullbacks f],
            R ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Z →
              R.pullbackArrows f ∈
                AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX W := by
  obtain ⟨K, hK, hisos, hbind, hpb, hpbcov⟩ :=
    CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.exists_precoverage_of_colimit
      (affineEtaleSiteColimit D c B hD hX hc).system
      (affineEtaleSiteColimit D c B hD hX hc).toLimit
      (affineEtaleSiteColimit D c B hD hX hc).toLimit_transition
      (affineEtaleSiteColimit_obj_descends D c B hD hX hc)
      (affineEtaleSiteColimit_hom_descends D c B hD hX hc)
      (affineEtaleSiteColimit_hom_eventually_eq D c B hD hX hc)
  obtain rfl : K = AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX :=
    Precoverage.ext (funext fun Z => Set.ext fun R =>
      (hK Z R).trans (affineEtaleSiteColimit_mem_precoverage_iff D c B hD hX hc Z R).symm)
  exact ⟨hK, hisos, hbind, hpb, hpbcov⟩

end Construction


private alias affineEtale_mem_precoverage_iff := mem_smallAffineEtale_precoverage_iff

end Stacks.EtaleCohomology

end
