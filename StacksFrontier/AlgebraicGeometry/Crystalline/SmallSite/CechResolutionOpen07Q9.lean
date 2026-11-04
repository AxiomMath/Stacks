module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionGood07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareEval07Q9
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ProCechInjective

/-!
# The sections over an open mapped into the Čech double complex

Fix a global crystalline situation `(p, (S, I, γ), X)`, an open `W` of `X`, and a cosimplicial
system `T(n)_e` of objects of `Cris(X/S)` which is a *pro-covering of `W`* in the sense of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ProCechInjective.lean` (`IsOpenProCovering`): its
members lie over `W`, the objects with affine ambient scheme cover, every such object over `W`
maps to some `T(0)_e`, and they satisfy the pro-product condition.  This file is the "α" half of
the derived Čech comparison in the proof of [Stacks, Tag 07Q9]; the "β" half is
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechResolutionGood07Q9.lean`, and both land
in the total complex of `...SmallSite.cechDoubleComplex T K`.

For a complex `K^•` of *injective* abelian sheaves on `Cris(X/S)` the Čech complex
`lim_e K^a(T(•)_e)` of each `K^a` is, by `Stacks.ProCech.quasiIso_augmentationMap`, a resolution
of the sections of `K^a` over the objects lying over `W`, which are the sections over `W` of the
direct image `u_{X/S, *}K^a` (`zariskiSectionsIso`).  So the augmentation

`Γ(W, u_{X/S, *}K^•) ⟶ Tot(lim_e K^•(T(•)_e))`

is a quasi-isomorphism, by [Stacks, Tag 0133] applied to the flip of the Čech double complex.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `LiesOver`, `HasAffineAmbient` — the two properties of objects of `Cris(X/S)` involved.
* `zariskiSectionsIso` — **`Γ(W, u_{X/S, *}G) ≅ lim_{B over W} G(B)`**, natural in `G`
  (`zariskiSectionsIso_hom_naturality`), with projections `zariskiDirectImageEval`
  (`zariskiSectionsIso_hom_π`).
* `IsOpenProCovering` — the hypotheses on `T`.
* `openAugmentation` — `Γ(W, u_{X/S, *}G) ⟶ lim_e G(T(0)_e)`, with projections
  `zariskiDirectImageEval` (`openAugmentation_π`).
* `openSectionsComplex` — the complex `Γ(W, u_{X/S, *}K^•)`.
* `openRowAugmentation` — the augmentation into the row `n = 0` of the flip of the Čech double
  complex.
* **`cechAugmentationOpen`** — the comparison `Γ(W, u_{X/S, *}K^•) ⟶ Tot(cechDoubleComplex T K)`.

## Main results

* `exact_openAugmentation` — `0 → Γ(W, u_* G) → lim_e G(T(0)_e) → lim_e G(T(1)_e)` is exact.
* `openRowAugmentation_hypotheses` — the hypotheses of [Stacks, Tag 0133] for the flip.
* **`quasiIso_cechAugmentationOpen`** — the comparison is a quasi-isomorphism.
* `cechAugmentationOpen_f_eq` — its components.
* **`cechAugmentationOpen_naturality`** — it is natural in the complex of injectives.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- The property of an object of `Cris(X/S)` of lying over the open `W` of `X`. -/
abbrev LiesOver (W : S.X.Opens) : ObjectProperty (CrystallineThickening S) :=
  fun B => (forgetToOpens S).obj B ≤ W

/-- Lying over `W` is inherited along morphisms. -/
theorem liesOver_of_hom (W : S.X.Opens) ⦃B' B : CrystallineThickening S⦄ (f : B' ⟶ B)
    (h : LiesOver S W B) : LiesOver S W B' :=
  (leOfHom ((forgetToOpens S).map f)).trans h

/-- The property of an object of `Cris(X/S)` of having affine ambient scheme. -/
abbrev HasAffineAmbient : ObjectProperty (CrystallineThickening S) :=
  fun B => IsAffine B.obj.thickening.target.scheme

/-- The objects lying over `W` index the limit computing `Γ(W, u_{X/S, *}G)`: the comparison
functor from the full subcategory of objects lying over `W` to the structured arrows of
`forgetToOpens` under `W`.  It is an equivalence, the category of opens being thin. -/
def liesOverToStructuredArrow (W : S.X.Opens) :
    (LiesOver S W).FullSubcategoryᵒᵖ ⥤ StructuredArrow (op W) (forgetToOpens S).op where
  obj B := StructuredArrow.mk (Y := op B.unop.obj) (homOfLE B.unop.property).op
  map f := StructuredArrow.homMk f.unop.hom.op (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The comparison functor is faithful. -/
instance (W : S.X.Opens) : (liesOverToStructuredArrow S W).Faithful where
  map_injective {B B'} f g h := by
    have := congrArg (fun k => k.right.unop) h
    exact Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ this)

/-- The comparison functor is full. -/
instance (W : S.X.Opens) : (liesOverToStructuredArrow S W).Full where
  map_surjective {B B'} g :=
    ⟨(ObjectProperty.homMk g.right.unop : B'.unop ⟶ B.unop).op, by
      ext; rfl⟩

/-- The comparison functor is essentially surjective. -/
instance (W : S.X.Opens) : (liesOverToStructuredArrow S W).EssSurj where
  mem_essImage X := ⟨op ⟨X.right.unop, leOfHom X.hom.unop⟩,
    ⟨StructuredArrow.isoMk (Iso.refl _) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))⟩⟩

/-- The comparison functor is an equivalence. -/
instance (W : S.X.Opens) : (liesOverToStructuredArrow S W).IsEquivalence where

/-- **`Γ(W, u_{X/S, *}G)` is the limit of `G` over the objects lying over `W`**: the limit over
the structured arrows of `zariskiDirectImageObjObjIsoLimit`, reindexed along the equivalence
`liesOverToStructuredArrow`. -/
def zariskiSectionsIso (W : S.X.Opens) (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((zariskiDirectImage S).obj G).obj.obj (op W) ≅
      Stacks.ProCech.sectionsOver (LiesOver S W) G.obj :=
  zariskiDirectImageObjObjIsoLimit S G W ≪≫
    asIso (limit.pre (StructuredArrow.proj (op W) (forgetToOpens S).op ⋙ G.obj)
      (liesOverToStructuredArrow S W)) ≪≫
    HasLimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _))

/-- The projections of `zariskiSectionsIso` are `zariskiDirectImageEval`. -/
@[reassoc]
theorem zariskiSectionsIso_hom_π (W : S.X.Opens) (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (B : CrystallineThickening S) (hB : LiesOver S W B) :
    (zariskiSectionsIso S W G).hom ≫ Stacks.ProCech.sectionsOverπ (LiesOver S W) G.obj B hB =
      zariskiDirectImageEval S hB G := by
  simp only [zariskiSectionsIso, Stacks.ProCech.sectionsOverπ, Iso.trans_hom, asIso_hom,
    Category.assoc, HasLimit.isoOfNatIso_hom_π, limit.pre_π_assoc]
  exact zariskiDirectImageObjObjIsoLimit_hom_π S hB G


/-- The projections of `zariskiSectionsIso`, indexed by the full subcategory. -/
@[reassoc]
theorem zariskiSectionsIso_hom_limit_π (W : S.X.Opens)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (B : (LiesOver S W).FullSubcategoryᵒᵖ) :
    (zariskiSectionsIso S W G).hom ≫ limit.π ((LiesOver S W).ι.op ⋙ G.obj) B =
      zariskiDirectImageEval S B.unop.property G :=
  zariskiSectionsIso_hom_π S W G B.unop.obj B.unop.property

/-- **`zariskiSectionsIso` is natural in the sheaf.** -/
theorem zariskiSectionsIso_hom_naturality (W : S.X.Opens)
    {G H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : G ⟶ H) :
    ((zariskiDirectImage S).map φ).hom.app (op W) ≫ (zariskiSectionsIso S W H).hom =
      (zariskiSectionsIso S W G).hom ≫
        limMap (Functor.whiskerLeft (LiesOver S W).ι.op φ.hom) := by
  refine limit.hom_ext fun B => ?_
  rw [Category.assoc, zariskiSectionsIso_hom_limit_π, Category.assoc, limMap_π,
    Functor.whiskerLeft_app, zariskiSectionsIso_hom_limit_π_assoc]
  exact zariskiDirectImageEval_naturality S B.unop.property φ

/-- **The system `T` is a pro-covering of the open `W`**: the hypotheses of
`Stacks.ProCech.quasiIso_augmentationMap` for `P = LiesOver S W` and `𝒜 = HasAffineAmbient S`.
The remaining hypothesis there, that `P` is inherited along morphisms, is `liesOver_of_hom`. -/
structure IsOpenProCovering (W : S.X.Opens) (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) :
    Prop where
  /-- The members of `T` lie over `W`. -/
  liesOver : ∀ n e, LiesOver S W ((T.obj (op ⦋n⦌)).obj e)
  /-- The objects with affine ambient scheme cover. -/
  affine_covers : ∀ B : CrystallineThickening S,
    Sieve.generate (fun (B' : CrystallineThickening S) (_ : B' ⟶ B) => HasAffineAmbient S B') ∈
      smallTopology S B
  /-- Every object with affine ambient scheme over `W` maps to some `T(0)_e`. -/
  reach : ∀ B : CrystallineThickening S, HasAffineAmbient S B → LiesOver S W B →
    ∃ e, Nonempty (B ⟶ (T.obj (op ⦋0⦌)).obj e)
  /-- The pro-product condition at the objects with affine ambient scheme. -/
  isProProductAt : ∀ B : CrystallineThickening S, HasAffineAmbient S B →
    Stacks.ProCech.IsProProductAt T B

variable {S} {W : S.X.Opens} {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}

/-- **The augmentation `Γ(W, u_{X/S, *}G) ⟶ lim_e G(T(0)_e)`**, whose projection to the level
`e` is `zariskiDirectImageEval`. -/
def openAugmentation (hT : IsOpenProCovering S W T)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((zariskiDirectImage S).obj G).obj.obj (op W) ⟶ limit ((T.obj (op ⦋0⦌)).op ⋙ G.obj) :=
  limit.lift ((T.obj (op ⦋0⦌)).op ⋙ G.obj)
    { pt := ((zariskiDirectImage S).obj G).obj.obj (op W)
      π :=
        { app e := zariskiDirectImageEval S (hT.liesOver 0 e.unop) G
          naturality _ _ _ :=
            (Category.id_comp _).trans (zariskiDirectImageEval_comp S _ _ _ G).symm } }

/-- The projections of the augmentation are `zariskiDirectImageEval`. -/
@[reassoc]
theorem openAugmentation_π (hT : IsOpenProCovering S W T)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (e : ℕ) :
    openAugmentation hT G ≫ limit.π ((T.obj (op ⦋0⦌)).op ⋙ G.obj) (op e) =
      zariskiDirectImageEval S (hT.liesOver 0 e) G :=
  limit.lift_π _ _

/-- The augmentation is `Stacks.ProCech.augmentation` through `zariskiSectionsIso`. -/
theorem openAugmentation_eq (hT : IsOpenProCovering S W T)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (openAugmentation hT G : _ ⟶ (Stacks.ProCech.sectionsComplex T G.obj).X 0) =
      (zariskiSectionsIso S W G).hom ≫ Stacks.ProCech.augmentation hT.liesOver G.obj :=
  Stacks.ProCech.sectionsComplex_hom_ext T G.obj fun e => by
    rw [Category.assoc, Stacks.ProCech.augmentation_π, zariskiSectionsIso_hom_π]
    exact openAugmentation_π hT G e

/-- The augmentation followed by the first Čech differential vanishes. -/
theorem openAugmentation_comp_d (hT : IsOpenProCovering S W T)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    openAugmentation hT G ≫ (sectionsComplex T G.obj).d 0 1 = 0 := by
  have h := Stacks.ProCech.augmentation_comp_d hT.liesOver G.obj
  have h' : (openAugmentation hT G : _ ⟶ (Stacks.ProCech.sectionsComplex T G.obj).X 0) ≫
      (Stacks.ProCech.sectionsComplex T G.obj).d 0 1 = 0 :=
    (congrArg (· ≫ (Stacks.ProCech.sectionsComplex T G.obj).d 0 1)
      (openAugmentation_eq hT G)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) h).trans Limits.comp_zero))
  exact h'

/-- **`0 → Γ(W, u_{X/S, *}G) → lim_e G(T(0)_e) → lim_e G(T(1)_e)` is exact**, for every abelian
sheaf `G`: `Stacks.ProCech.augmentation_exact` and `Stacks.ProCech.mono_augmentation`. -/
theorem exact_openAugmentation (hT : IsOpenProCovering S W T)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (ShortComplex.mk _ _ (openAugmentation_comp_d hT G)).Exact ∧
      Mono (openAugmentation hT G) := by
  have h1 := Stacks.ProCech.augmentation_exact G (liesOver_of_hom S W) hT.liesOver
    hT.affine_covers hT.reach hT.isProProductAt
  have h2 := Stacks.ProCech.mono_augmentation G (liesOver_of_hom S W) hT.liesOver
    hT.affine_covers hT.reach
  let e : ShortComplex.mk _ _ (openAugmentation_comp_d hT G) ≅
      ShortComplex.mk _ _ (Stacks.ProCech.augmentation_comp_d hT.liesOver G.obj) :=
    ShortComplex.isoMk (zariskiSectionsIso S W G) (Iso.refl _) (Iso.refl _)
      ((openAugmentation_eq hT G).symm.trans (Category.comp_id _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  refine ⟨(ShortComplex.exact_iff_of_iso e).2 h1, ?_⟩
  have : Mono ((zariskiSectionsIso S W G).hom ≫ Stacks.ProCech.augmentation hT.liesOver G.obj) :=
    mono_comp _ _
  exact (openAugmentation_eq hT G) ▸ this

/-- **The Čech complex of an injective abelian sheaf along a pro-covering is exact in positive
degrees**, `Stacks.ProCech.isZero_homology_sectionsComplex`. -/
theorem isZero_homology_sectionsComplex_of_injective (hT : IsOpenProCovering S W T)
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective G] (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((sectionsComplex T G.obj).homology n) :=
  Stacks.ProCech.isZero_homology_sectionsComplex G hT.affine_covers hT.isProProductAt n hn

/-- The augmentation is natural in the sheaf. -/
theorem openAugmentation_naturality (hT : IsOpenProCovering S W T)
    {G H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : G ⟶ H) :
    openAugmentation hT G ≫ limMap (Functor.whiskerLeft (T.obj (op ⦋0⦌)).op φ.hom) =
      ((zariskiDirectImage S).map φ).hom.app (op W) ≫ openAugmentation hT H :=
  limit.hom_ext fun e => by
    rw [Category.assoc, limMap_π, openAugmentation_π_assoc, Category.assoc, openAugmentation_π]
    exact (zariskiDirectImageEval_naturality S _ φ).symm

/-- **The complex `Γ(W, u_{X/S, *}K^•)`** of a complex of abelian sheaves on `Cris(X/S)`. -/
abbrev openSectionsComplex (W : S.X.Opens)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
    _).obj (((zariskiDirectImage S).mapHomologicalComplex _).obj K)

/-- The augmentation `Γ(W, u_{X/S, *}K^•) ⟶ lim_e K^•(T(0)_e)` of `ℕ`-indexed complexes, the
target being the row `0` of the complex of cosimplicial groups of `K^•`. -/
def openAugmentationNat (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    openSectionsComplex W K ⟶ cosimplicialRowComplex ((cechCosimplicialComplex T).obj K) 0 where
  f a := openAugmentation hT (K.X a)
  comm' a a' _ := openAugmentation_naturality hT (K.d a a')

/-- The identification of the row `0` of the double complex with the extension of the row `0` of
`cechCosimplicialComplex T K`, read through `cechDoubleComplexXXIso`, is the canonical one. -/
theorem cosimplicialDoubleComplexRowIso_inv_f_comp
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (a : ℕ) :
    (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv.f (a : ℤ) ≫
        (cechDoubleComplexXXIso T K 0 a).hom =
      ((cosimplicialRowComplex ((cechCosimplicialComplex T).obj K) 0).extendXIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)).hom := by
  let K' := (cechCosimplicialComplex T).obj K
  have h := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
    (HomologicalComplex.eval AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) ((0 : ℕ) : ℤ))
    (cosimplicialDoubleComplexInner K') (cosimplicialRowInnerIso K' 0).inv
    ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
  show (HomologicalComplex.extendMap (cosimplicialRowInnerIso K' 0).inv
      ComplexShape.embeddingUpNat ≫ (cosimplicialRowOuterIso K' 0).hom).f (a : ℤ) ≫
      ((cosimplicialDoubleComplexColumnIso K' a).hom.f ((0 : ℕ) : ℤ) ≫
        (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a)).extendXIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f 0)).hom) = _
  refine (congrArg (· ≫ ((cosimplicialDoubleComplexColumnIso K' a).hom.f ((0 : ℕ) : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a)).extendXIso
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f 0)).hom)) h).trans ?_
  have k1 : (HomologicalComplex.eval AddCommGrpCat.{u + 1} (ComplexShape.up ℤ)
      ((0 : ℕ) : ℤ)).map ((cosimplicialDoubleComplexInner K').extendXIso
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)).inv ≫
      (cosimplicialDoubleComplexColumnIso K' a).hom.f ((0 : ℕ) : ℤ) = 𝟙 _ :=
    (congrArg (fun φ => HomologicalComplex.Hom.f φ ((0 : ℕ) : ℤ))
      (Iso.inv_hom_id (cosimplicialDoubleComplexColumnIso K' a))).trans
        (HomologicalComplex.id_f _ _)
  have k2 : (cosimplicialRowInnerIso K' 0).inv.f a ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a)).extendXIso
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f 0)).hom = 𝟙 _ :=
    Iso.inv_hom_id (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K'.X a)).extendXIso
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f 0))
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) k1)).trans
      (Category.id_comp _)))))).trans ((congrArg (_ ≫ ·) k2).trans (Category.comp_id _))

/-- **The augmentation into the row `n = 0` of the flip of the Čech double complex**: the
extension of `openAugmentationNat`, read in the row through
`Crystalline.cosimplicialDoubleComplexRowIso`. -/
def openRowAugmentation (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    (openSectionsComplex W K).extend ComplexShape.embeddingUpNat ⟶
      rowZero ((cechDoubleComplex T).obj K).flip :=
  HomologicalComplex.extendMap (openAugmentationNat hT K) ComplexShape.embeddingUpNat ≫
    (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv

/-- The augmentation in degree `a`, read through `cechDoubleComplexXXIso`. -/
theorem openRowAugmentation_f_comp (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (a : ℕ) :
    (openRowAugmentation hT K).f (a : ℤ) ≫ (cechDoubleComplexXXIso T K 0 a).hom =
      ((openSectionsComplex W K).extendXIso ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f a)).hom ≫ openAugmentation hT (K.X a) := by
  have h1 := HomologicalComplex.extendMap_f (openAugmentationNat hT K)
    ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
  have h2 := cosimplicialDoubleComplexRowIso_inv_f_comp (T := T) K a
  show (HomologicalComplex.extendMap (openAugmentationNat hT K) ComplexShape.embeddingUpNat).f
      (a : ℤ) ≫ ((cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv.f
        (a : ℤ) ≫ (cechDoubleComplexXXIso T K 0 a).hom) = _
  rw [h2, h1]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _))))

/-- In degree `a` the augmentation identifies `Γ(W, u_* K^a)` with the kernel of the first
Čech differential. -/
theorem openRowAugmentation_inducesIsoKernel_nat (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (a : ℕ) :
    ∃ hα : (openRowAugmentation hT K).f (a : ℤ) ≫
        ((((cechDoubleComplex T).obj K).flip).X (a : ℤ)).d 0 1 = 0,
      IsIso (kernel.lift _ _ hα) := by
  obtain ⟨hex, hm⟩ := exact_openAugmentation hT (K.X a)
  have sq1 := openRowAugmentation_f_comp hT K a
  have sq2 := cechDoubleComplex_d_f_comp (T := T) K 0 1 a
  have hα : (openRowAugmentation hT K).f (a : ℤ) ≫
      ((((cechDoubleComplex T).obj K).flip).X (a : ℤ)).d 0 1 = 0 := by
    have h2 : (openRowAugmentation hT K).f (a : ℤ) ≫
        ((((cechDoubleComplex T).obj K).flip).X (a : ℤ)).d 0 1 ≫
          (cechDoubleComplexXXIso T K 1 a).hom = 0 :=
      (congrArg (_ ≫ ·) sq2).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) sq1).trans <| (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (openAugmentation_comp_d hT (K.X a))).trans Limits.comp_zero
    exact (cancel_mono (cechDoubleComplexXXIso T K 1 a).hom).1
      ((Category.assoc _ _ _).trans (h2.trans Limits.zero_comp.symm))
  refine ⟨hα, ?_⟩
  let e : ShortComplex.mk _ _ hα ≅ ShortComplex.mk _ _ (openAugmentation_comp_d hT (K.X a)) :=
    ShortComplex.isoMk ((openSectionsComplex W K).extendXIso ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f a))
      (cechDoubleComplexXXIso T K 0 a) (cechDoubleComplexXXIso T K 1 a) sq1.symm sq2.symm
  have : Mono ((openRowAugmentation hT K).f (a : ℤ)) := by
    have : Mono ((openRowAugmentation hT K).f (a : ℤ) ≫
        (cechDoubleComplexXXIso T K 0 a).hom) := by
      rw [sq1]
      exact @mono_comp _ _ _ _ _ _ _ _ hm
    exact mono_of_mono _ (cechDoubleComplexXXIso T K 0 a).hom
  exact isIso_kernelLift_of_exact _ _ hα ((ShortComplex.exact_iff_of_iso e).2 hex)

/-- **The flip of the Čech double complex of a complex of injectives resolves
`Γ(W, u_{X/S, *}K^•)`**: the hypotheses of [Stacks, Tag 0133]. -/
theorem openRowAugmentation_hypotheses (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] :
    Hypotheses ((openSectionsComplex W K).extend ComplexShape.embeddingUpNat)
      ((cechDoubleComplex T).obj K).flip (openRowAugmentation hT K) := by
  let K' := (cechCosimplicialComplex T).obj K
  have hz : ∀ p q : ℤ, (p < 0 ∨ q < 0) →
      IsZero (((((cechDoubleComplex T).obj K).flip).X p).X q) := by
    rintro p q (hp | hq)
    · exact (HomologicalComplex.eval _ _ q).map_isZero
        (isZero_cosimplicialDoubleComplex_X_of_neg K' hp)
    · exact isZero_cosimplicialDoubleComplex_X_X_of_neg K' p hq
  refine ⟨fun n => ?_, fun p q hq => hz p q (Or.inr hq), fun p q hq => ?_, fun p => ?_⟩
  · refine (Set.finite_Icc 0 n).subset fun p hp => ?_
    by_contra h
    exact hp (hz p (n - p) (by simp only [Set.mem_Icc, not_and_or, not_le] at h; omega))
  · by_cases hp : p < 0
    · exact ShortComplex.exact_of_isZero_X₂ _ (hz p q (Or.inl hp))
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = a := ⟨p.toNat, by omega⟩
      refine HomologicalComplex.ExactAt.of_iso ?_ (cosimplicialDoubleComplexColumnIso K' a).symm
      by_cases hq' : q < 0
      · exact HomologicalComplex.extend_exactAt _ _ _
          (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = m := ⟨q.toNat, by omega⟩
        refine (HomologicalComplex.extend_exactAt_iff _ _ (ComplexShape.embeddingUpNat_f m)).2 ?_
        rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact isZero_homology_sectionsComplex_of_injective hT (K.X a) m (by omega)
  · by_cases hp : p < 0
    · have h0 : IsZero (((openSectionsComplex W K).extend ComplexShape.embeddingUpNat).X p) :=
        HomologicalComplex.isZero_extend_X _ _ _
          (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
      refine ⟨h0.eq_of_src _ _, StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _ h0 ?_⟩
      exact IsZero.of_mono (kernel.ι _) (hz p 0 (Or.inl hp))
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = a := ⟨p.toNat, by omega⟩
      exact openRowAugmentation_inducesIsoKernel_nat hT K a

/-- **The comparison `Γ(W, u_{X/S, *}K^•) ⟶ Tot(lim_e K^•(T(•)_e))`** for a complex `K^•` of
injective abelian sheaves: `comparisonMapP` for the flip of the Čech double complex, followed by
`HomologicalComplex₂.totalFlipIso`. -/
def cechAugmentationOpen (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] :
    (openSectionsComplex W K).extend ComplexShape.embeddingUpNat ⟶
      ((cechDoubleComplex T).obj K).total (ComplexShape.up ℤ) :=
  comparisonMapP _ _ (openRowAugmentation hT K) (openRowAugmentation_hypotheses hT K) ≫
    (((cechDoubleComplex T).obj K).totalFlipIso (ComplexShape.up ℤ)).hom

/-- **The comparison is a quasi-isomorphism**, by [Stacks, Tag 0133]. -/
instance quasiIso_cechAugmentationOpen (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] : QuasiIso (cechAugmentationOpen hT K) := by
  unfold cechAugmentationOpen
  infer_instance

/-- The augmentation in degree `a`. -/
theorem openRowAugmentation_f (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (a : ℕ) :
    (openRowAugmentation hT K).f (a : ℤ) =
      (((openSectionsComplex W K).extendXIso ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f a)).hom ≫ openAugmentation hT (K.X a)) ≫
        (cechDoubleComplexXXIso T K 0 a).inv :=
  (Iso.eq_comp_inv _).2 (openRowAugmentation_f_comp hT K a)

/-- The comparison in degree `a` is the augmentation followed by the inclusion of the summand in
bidegree `(0, a)`. -/
theorem cechAugmentationOpen_f (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] (a : ℕ) :
    (cechAugmentationOpen hT K).f (a : ℤ) =
      (openRowAugmentation hT K).f (a : ℤ) ≫
        ((cechDoubleComplex T).obj K).ιTotal (ComplexShape.up ℤ) 0 a a (by simp) := by
  show (openRowAugmentation hT K).f (a : ℤ) ≫
      ((cechDoubleComplex T).obj K).flip.ιTotal (ComplexShape.up ℤ) a 0 a (by simp) ≫
        (((cechDoubleComplex T).obj K).totalFlipIso (ComplexShape.up ℤ)).hom.f a = _
  rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp

/-- **The component formula of `cechAugmentationOpen`**: in degree `a` it is the augmentation
`Γ(W, u_* K^a) ⟶ lim_e K^a(T(0)_e)` — whose projection to the level `e` is
`zariskiDirectImageEval`, `openAugmentation_π` — read into the term of bidegree `(0, a)` of the
Čech double complex by `cechDoubleComplexXXIso` and included into the total complex. -/
theorem cechAugmentationOpen_f_eq (hT : IsOpenProCovering S W T)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] (a : ℕ) :
    (cechAugmentationOpen hT K).f (a : ℤ) =
      ((((openSectionsComplex W K).extendXIso ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f a)).hom ≫ openAugmentation hT (K.X a)) ≫
        (cechDoubleComplexXXIso T K 0 a).inv) ≫
          ((cechDoubleComplex T).obj K).ιTotal (ComplexShape.up ℤ) 0 a a (by simp) :=
  (cechAugmentationOpen_f hT K a).trans (congrArg (· ≫ _) (openRowAugmentation_f hT K a))

/-- The map of complexes `Γ(W, u_{X/S, *}K^•) ⟶ Γ(W, u_{X/S, *}L^•)` induced by `K^• ⟶ L^•`. -/
abbrev openSectionsComplexMap (W : S.X.Opens)
    {K L : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ L) :
    openSectionsComplex W K ⟶ openSectionsComplex W L :=
  (((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
    _).map (((zariskiDirectImage S).mapHomologicalComplex _).map φ)

/-- The augmentation of `ℕ`-indexed complexes is natural. -/
theorem openAugmentationNat_naturality (hT : IsOpenProCovering S W T)
    {K L : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ L) :
    openAugmentationNat hT K ≫ cosimplicialRowMap ((cechCosimplicialComplex T).map φ) 0 =
      openSectionsComplexMap W φ ≫ openAugmentationNat hT L := by
  ext a : 1
  exact openAugmentation_naturality hT (φ.f a)

/-- **The comparison is natural** in the complex of injectives: for `φ : K^• ⟶ L^•` the square
formed with `Tot` of the Čech double complex of `φ` and the map `Γ(W, u_* φ)` commutes. -/
theorem cechAugmentationOpen_naturality (hT : IsOpenProCovering S W T)
    {K L : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ}
    [∀ a, Injective (K.X a)] [∀ a, Injective (L.X a)] (φ : K ⟶ L) :
    cechAugmentationOpen hT K ≫
        HomologicalComplex₂.total.map ((cechDoubleComplex T).map φ) (ComplexShape.up ℤ) =
      HomologicalComplex.extendMap (openSectionsComplexMap W φ) ComplexShape.embeddingUpNat ≫
        cechAugmentationOpen hT L := by
  have hnat := cosimplicialDoubleComplexRowIso_naturality ((cechCosimplicialComplex T).map φ) 0
  have hnat' : (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv ≫
      (StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map ((cechCosimplicialComplex T).map φ))).f
          ((0 : ℕ) : ℤ) =
      HomologicalComplex.extendMap (cosimplicialRowMap ((cechCosimplicialComplex T).map φ) 0)
          ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj L) 0).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hcomm : openRowAugmentation hT K ≫
      rowZeroMap (StacksDraft.TotalComplexQuasiIso.flipHom ((cechDoubleComplex T).map φ)) =
        HomologicalComplex.extendMap (openSectionsComplexMap W φ) ComplexShape.embeddingUpNat ≫
          openRowAugmentation hT L := by
    show (HomologicalComplex.extendMap (openAugmentationNat hT K) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv) ≫
      (StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map ((cechCosimplicialComplex T).map φ))).f
          ((0 : ℕ) : ℤ) =
      HomologicalComplex.extendMap (openSectionsComplexMap W φ) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendMap (openAugmentationNat hT L) ComplexShape.embeddingUpNat ≫
          (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj L) 0).inv)
    rw [Category.assoc, hnat', ← HomologicalComplex.extendMap_comp_assoc,
      ← HomologicalComplex.extendMap_comp_assoc, openAugmentationNat_naturality]
  have hP := comparisonMapP_naturality _ _ _ (openRowAugmentation_hypotheses hT K)
    (openRowAugmentation_hypotheses hT L) _ _ hcomm
  rw [cechAugmentationOpen, cechAugmentationOpen, Category.assoc,
    ← StacksDraft.TotalComplexQuasiIso.totalFlipIso_naturality, ← Category.assoc, hP,
    Category.assoc]

end Crystalline.GlobalCrystallineSituation.SmallSite
