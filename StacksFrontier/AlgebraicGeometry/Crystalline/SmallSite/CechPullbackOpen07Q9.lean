module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechPullback07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionOpen07Q9

/-!
# The Čech pullback against the two comparisons of the Čech double complex

Let `f : X' ⟶ X` be a morphism of global crystalline situations over `S' → S`, here
`S = X'/S` the source and `S' = X/S` the target, and `Φ : CechSystemHom fS fX hf T T'` a
morphism from a system of thickenings `T` of `Cris(X'/S)` to a system `T'` of `Cris(X/S)`, as in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechPullback07Q9.lean`.  It induces the
Čech pullback `Φ.cechDoubleMap K : Č_{T'}(f_{cris, *}K) ⟶ Č_T(K)` of Čech double complexes.  This
file checks it against the two comparisons that land in the total complexes of those double
complexes: the "α" comparison `cechAugmentationOpen` out of the sections over an open, of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechResolutionOpen07Q9.lean`, and the "β"
comparison `cechComparison` out of `M(•)`, of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechResolutionGood07Q9.lean`.

On the α side the sections over `W` of `u_{X/S, *}f_{cris, *}K` are identified with the sections
over `f^{-1}W` of `u_{X'/S, *}K` by the commutation `crisZariskiSquare` of the square of topoi of
[Stacks, Tag 07Q9]; at the level of the augmentations the compatibility is
`eval_comp_crisDirectImageEval_eq_crisZariskiSquare`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `openSectionsSquareIso` — `Γ(W, u_{X/S, *}f_{cris, *}K^•) ≅ Γ(f^{-1}W, u_{X'/S, *}K^•)`.
* `CechSystemHom.sectionsMap` — the map `M_{T'}(G') ⟶ M_T(G)` induced by `μ₀ : G' ⟶ f_{cris, *}G`
  followed by the Čech pullback.

## Main results

* `CechSystemHom.cechDoubleMap_f_f_comp` — the Čech pullback in bidegree `(n, a)`.
* `openSectionsSquareIso_hom_naturality` — the square isomorphism is natural.
* **`CechSystemHom.cechAugmentationOpen_comp_cechDoubleMap`** — the α comparison for `f_* K`
  followed by the Čech pullback is the square isomorphism followed by the α comparison for `K`;
  and `CechSystemHom.quasiIso_cechAugmentationOpen_comp_cechDoubleMap` — that composite is a
  quasi-isomorphism.
* **`CechSystemHom.cechComparison_comp_cechDoubleMap`** — the β comparison is compatible with a
  map of injective resolutions over `μ₀` followed by the Čech pullback.

## References

* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} {fS : S.S ⟶ S'.S} {fX : S.X ⟶ S'.X}
  {hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber}

namespace CechSystemHom

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom fS fX hf T T')

/-- **The Čech pullback in bidegree `(n, a)`**, read through `cechDoubleComplexXXIso`: it is the
Čech pullback of `K^a` in cosimplicial degree `n`. -/
theorem cechDoubleMap_f_f_comp
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (n a : ℕ) :
    ((Φ.cechDoubleMap K).f (n : ℤ)).f (a : ℤ) ≫ (cechDoubleComplexXXIso T K n a).hom =
      (cechDoubleComplexXXIso T'
          (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) n a).hom ≫
        (Φ.cosimplicialMap (K.X a)).app ⦋n⦌ := by
  let K₁' := (cechCosimplicialComplex T').obj
    (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K)
  let K₂' := (cechCosimplicialComplex T).obj K
  let c : (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₁'.X a) ⟶
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₂'.X a) :=
    (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map ((Φ.cechMap K).f a)
  have hd : (cosimplicialDoubleComplexFunctor.map (Φ.cechMap K)).f
      (a : ℤ) = (cosimplicialDoubleComplexColumnIso K₁' a).hom ≫
        HomologicalComplex.extendMap c ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₂' a).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
  have hd' : (cosimplicialDoubleComplexFunctor.map (Φ.cechMap K)).f
      (a : ℤ) ≫ (cosimplicialDoubleComplexColumnIso K₂' a).hom =
      (cosimplicialDoubleComplexColumnIso K₁' a).hom ≫
        HomologicalComplex.extendMap c ComplexShape.embeddingUpNat := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ)) hd'
  simp only [HomologicalComplex.comp_f] at h1
  rw [HomologicalComplex.extendMap_f c ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
    (ComplexShape.embeddingUpNat_f n)] at h1
  show ((cosimplicialDoubleComplexFunctor.map (Φ.cechMap K)).f
      (a : ℤ)).f (n : ℤ) ≫ ((cosimplicialDoubleComplexColumnIso K₂' a).hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₂'.X a)).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) =
    ((cosimplicialDoubleComplexColumnIso K₁' a).hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj (K₁'.X a)).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ))
        (ComplexShape.embeddingUpNat_f n)).hom) ≫ c.f n
  rw [← Category.assoc, h1]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CechSystemHom

variable (fS fX hf) in
/-- **The square of topoi of [Stacks, Tag 07Q9] on the sections over an open**:
`Γ(W, u_{X/S, *}f_{cris, *}K^•) ≅ Γ(f^{-1}W, u_{X'/S, *}K^•)`, degreewise the sections at `W` of
`crisZariskiSquare`, the sections of `f_{Zar, *}` at `W` being the sections at `f^{-1}W`. -/
def openSectionsSquareIso (W : S'.X.Opens)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    openSectionsComplex W (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) ≅
      openSectionsComplex (fX ⁻¹ᵁ W) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun a => ((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op W)).mapIso
      ((crisZariskiSquare S S' fS fX hf).app (K.X a)))
    (fun a b _ => ((Functor.map_comp _ _ _).symm.trans (congrArg
      ((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op W)).map
      ((crisZariskiSquare S S' fS fX hf).hom.naturality (K.d a b)).symm)).trans
        (Functor.map_comp _ _ _))

/-- The components of `openSectionsSquareIso`. -/
theorem openSectionsSquareIso_hom_f (W : S'.X.Opens)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) (a : ℕ) :
    (openSectionsSquareIso fS fX hf W K).hom.f a =
      ((crisZariskiSquare S S' fS fX hf).hom.app (K.X a)).hom.app (op W) := rfl

/-- `openSectionsSquareIso` is natural in the complex. -/
theorem openSectionsSquareIso_hom_naturality (W : S'.X.Opens)
    {K L : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ L) :
    openSectionsComplexMap W (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).map φ) ≫
        (openSectionsSquareIso fS fX hf W L).hom =
      (openSectionsSquareIso fS fX hf W K).hom ≫ openSectionsComplexMap (fX ⁻¹ᵁ W) φ := by
  ext a : 1
  exact ((Functor.map_comp _ _ _).symm.trans (congrArg
      ((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op W)).map
      ((crisZariskiSquare S S' fS fX hf).hom.naturality (φ.f a)))).trans
        (Functor.map_comp _ _ _)

namespace CechSystemHom

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom fS fX hf T T')
  {W : S'.X.Opens} (hT' : IsOpenProCovering S' W T') (hT : IsOpenProCovering S (fX ⁻¹ᵁ W) T)

/-- **The augmentations of the two pro-coverings are compatible with the Čech pullback**: the
augmentation of `T'` at `f_{cris, *}H` followed by the Čech pullback in degree `0` is the square at
`W` followed by the augmentation of `T` at `H`. -/
theorem openAugmentation_comp_app (H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    openAugmentation hT' ((crisDirectImage S S' fS fX hf).obj H) ≫ Φ.app H ⦋0⦌ =
      ((crisZariskiSquare S S' fS fX hf).hom.app H).hom.app (op W) ≫ openAugmentation hT H := by
  refine limit.hom_ext (F := (sectionSystem T H.obj).obj ⦋0⦌) fun e => ?_
  have h1 := Φ.app_π H ⦋0⦌ e.unop
  have h2 := openAugmentation_π_assoc hT' ((crisDirectImage S S' fS fX hf).obj H) (e.unop + Φ.k)
    (crisDirectImageEval S S' fS fX hf (Φ.τ ⦋0⦌ e.unop) H)
  have h3 := eval_comp_crisDirectImageEval_eq_crisZariskiSquare S S' fS fX hf H
    (hT'.liesOver 0 (e.unop + Φ.k)) (Φ.τ ⦋0⦌ e.unop) (hT.liesOver 0 e.unop)
  have h4 := openAugmentation_π hT H e.unop
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
    ((h2.trans h3).trans (congrArg (_ ≫ ·) h4.symm)))) |>.trans (Category.assoc _ _ _).symm

/-- The direct image of a complex of injective abelian sheaves has injective terms. -/
instance injective_crisDirectImage_mapHomologicalComplex_X
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] (a : ℕ) :
    Injective ((((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K).X a) :=
  inferInstanceAs (Injective ((crisDirectImage S S' fS fX hf).obj (K.X a)))

/-- The compatibility `openAugmentation_comp_app` on the augmentations of `ℕ`-indexed
complexes. -/
theorem openAugmentationNat_comp_cosimplicialRowMap
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    openAugmentationNat hT' (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) ≫
        cosimplicialRowMap (Φ.cechMap K) 0 =
      (openSectionsSquareIso fS fX hf W K).hom ≫ openAugmentationNat hT K := by
  ext a : 1
  exact Φ.openAugmentation_comp_app hT' hT (K.X a)

/-- **The α comparison against the Čech pullback**: for `K^•` of injective abelian sheaves,
`cechAugmentationOpen` for `f_{cris, *}K^•` followed by `Tot` of the Čech pullback is
`openSectionsSquareIso` followed by `cechAugmentationOpen` for `K^•`. -/
theorem cechAugmentationOpen_comp_cechDoubleMap
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] :
    cechAugmentationOpen hT' (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) ≫
        HomologicalComplex₂.total.map (Φ.cechDoubleMap K) (ComplexShape.up ℤ) =
      HomologicalComplex.extendMap (openSectionsSquareIso fS fX hf W K).hom
          ComplexShape.embeddingUpNat ≫ cechAugmentationOpen hT K := by
  let K₁ := ((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K
  have hnat := cosimplicialDoubleComplexRowIso_naturality (Φ.cechMap K) 0
  have hnat' : (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T').obj K₁) 0).inv ≫
      (StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map (Φ.cechMap K))).f ((0 : ℕ) : ℤ) =
      HomologicalComplex.extendMap (cosimplicialRowMap (Φ.cechMap K) 0)
          ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hcomm : openRowAugmentation hT' K₁ ≫
      rowZeroMap (StacksDraft.TotalComplexQuasiIso.flipHom (Φ.cechDoubleMap K)) =
        HomologicalComplex.extendMap (openSectionsSquareIso fS fX hf W K).hom
            ComplexShape.embeddingUpNat ≫ openRowAugmentation hT K := by
    show (HomologicalComplex.extendMap (openAugmentationNat hT' K₁) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T').obj K₁) 0).inv) ≫
      (StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map (Φ.cechMap K))).f ((0 : ℕ) : ℤ) =
      HomologicalComplex.extendMap (openSectionsSquareIso fS fX hf W K).hom
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendMap (openAugmentationNat hT K) ComplexShape.embeddingUpNat ≫
          (cosimplicialDoubleComplexRowIso ((cechCosimplicialComplex T).obj K) 0).inv)
    rw [Category.assoc, hnat', ← HomologicalComplex.extendMap_comp_assoc,
      ← HomologicalComplex.extendMap_comp_assoc, openAugmentationNat_comp_cosimplicialRowMap]
  have hP := comparisonMapP_naturality _ _ _ (openRowAugmentation_hypotheses hT' K₁)
    (openRowAugmentation_hypotheses hT K) _ _ hcomm
  rw [cechAugmentationOpen, cechAugmentationOpen, Category.assoc,
    ← StacksDraft.TotalComplexQuasiIso.totalFlipIso_naturality, ← Category.assoc, hP,
    Category.assoc]

include hT in
/-- **The α comparison followed by the Čech pullback is a quasi-isomorphism**, being the composite
of an isomorphism and the quasi-isomorphism `cechAugmentationOpen`. -/
theorem quasiIso_cechAugmentationOpen_comp_cechDoubleMap
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    [∀ a, Injective (K.X a)] :
    QuasiIso (cechAugmentationOpen hT'
        (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K) ≫
      HomologicalComplex₂.total.map (Φ.cechDoubleMap K) (ComplexShape.up ℤ)) := by
  rw [Φ.cechAugmentationOpen_comp_cechDoubleMap hT' hT K]
  have : IsIso (HomologicalComplex.extendMap (openSectionsSquareIso fS fX hf W K).hom
      ComplexShape.embeddingUpNat) :=
    inferInstanceAs (IsIso ((ComplexShape.embeddingUpNat.extendFunctor
      AddCommGrpCat.{u + 1}).map (openSectionsSquareIso fS fX hf W K).hom))
  infer_instance

end CechSystemHom

namespace CechSystemHom

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom fS fX hf T T')

/-- **The map `M_{T'}(G') ⟶ M_T(G)`** induced by `μ₀ : G' ⟶ f_{cris, *}G` followed by the Čech
pullback `Φ.cosimplicialMap G`. -/
def sectionsMap {G' : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (μ₀ : G' ⟶ (crisDirectImage S S' fS fX hf).obj G) :
    sectionsComplex T' G'.obj ⟶ sectionsComplex T G.obj :=
  sectionsComplexMap T' μ₀.hom ≫
    (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map (Φ.cosimplicialMap G)

/-- The Čech pullback on the row `a = 0` of the Čech double complexes. -/
theorem rowZeroMap_cechDoubleMap
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ) :
    rowZeroMap (Φ.cechDoubleMap K) =
      (cosimplicialDoubleComplexColumnIso ((cechCosimplicialComplex T').obj
          (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj K)) 0).hom ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
          ((Φ.cechMap K).f 0)) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso ((cechCosimplicialComplex T).obj K) 0).inv := by
  show (cosimplicialDoubleComplexFunctor.map (Φ.cechMap K)).f ((0 : ℕ) : ℤ) = _
  exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
    (i' := ((0 : ℕ) : ℤ)) (ComplexShape.embeddingUpNat_f 0)

/-- **The β comparison against the Čech pullback**: for `μ₀ : G' ⟶ f_{cris, *}G` and a map
`ψ : I'^• ⟶ f_{cris, *}I^•` of injective resolutions over `μ₀` (the shape of
`crisResolutionMap`), `cechComparison` for `I'` followed by `Tot` of the Čech double complex of
`ψ` and of the Čech pullback is `Φ.sectionsMap μ₀` followed by `cechComparison` for `I`. -/
theorem cechComparison_comp_cechDoubleMap
    (hT' : HasAffineMonoLevels T') {G' : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}}
    (hG' : VanishingOnLevels07Q9 T' G') (hGs' : HasSurjectiveLevelTransitions T' G')
    (hT : HasAffineMonoLevels T) {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (hG : VanishingOnLevels07Q9 T G) (hGs : HasSurjectiveLevelTransitions T G)
    (μ₀ : G' ⟶ (crisDirectImage S S' fS fX hf).obj G)
    (I' : InjectiveResolution G') (I : InjectiveResolution G)
    (ψ : I'.cocomplex ⟶ ((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj I.cocomplex)
    (hψ : I'.ι.f 0 ≫ ψ.f 0 = (HomologicalComplex.singleObjXSelf _ 0 G').hom ≫ μ₀ ≫
      (crisDirectImage S S' fS fX hf).map
        ((HomologicalComplex.singleObjXSelf _ 0 G).inv ≫ I.ι.f 0)) :
    cechComparison hT' hG' hGs' I' ≫
        HomologicalComplex₂.total.map ((cechDoubleComplex T').map ψ ≫
          Φ.cechDoubleMap I.cocomplex) (ComplexShape.up ℤ) =
      HomologicalComplex.extendMap (Φ.sectionsMap μ₀) ComplexShape.embeddingUpNat ≫
        cechComparison hT hG hGs I := by
  let K₁ := (cechCosimplicialComplex T').obj I'.cocomplex
  let K₂ := (cechCosimplicialComplex T').obj
    (((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj I.cocomplex)
  let K₃ := (cechCosimplicialComplex T).obj I.cocomplex
  let ψ₀ : I'.cocomplex.X 0 ⟶ (crisDirectImage S S' fS fX hf).obj (I.cocomplex.X 0) := ψ.f 0
  have haug : resolutionAugmentation I' ≫ ψ₀ =
      μ₀ ≫ (crisDirectImage S S' fS fX hf).map (resolutionAugmentation I) := by
    rw [resolutionAugmentation, Category.assoc]
    exact (congrArg (_ ≫ ·) hψ).trans (Iso.inv_hom_id_assoc _ _)
  let M := alternatingCofaceMapComplex AddCommGrpCat.{u + 1}
  let a₁ := (cosimplicialSectionsFunctor T').map (resolutionAugmentation I').hom
  let b₁ := (cosimplicialSectionsFunctor T').map ψ₀.hom
  let c₁ := Φ.cosimplicialMap (I.cocomplex.X 0)
  let d₁ := (cosimplicialSectionsFunctor T').map μ₀.hom
  let e₁ := Φ.cosimplicialMap G
  let f₁ := (cosimplicialSectionsFunctor T).map (resolutionAugmentation I).hom
  have hmap : a₁ ≫ b₁ = d₁ ≫ (cosimplicialSectionsFunctor T').map
      ((crisDirectImage S S' fS fX hf).map (resolutionAugmentation I)).hom :=
    ((Functor.map_comp _ _ _).symm.trans
      (congrArg (fun g => (cosimplicialSectionsFunctor T').map g.hom) haug)).trans
        (Functor.map_comp _ _ _)
  have hcos : a₁ ≫ b₁ ≫ c₁ = d₁ ≫ e₁ ≫ f₁ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c₁) hmap).trans ((Category.assoc _ _ _).trans
      (congrArg (d₁ ≫ ·) (Φ.cosimplicialMap_naturality (resolutionAugmentation I)))))
  have hN : cechAugmentationNat I' T' ≫
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
        (((cechCosimplicialComplex T').map ψ).f 0) ≫
      (alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map ((Φ.cechMap I.cocomplex).f 0) =
        Φ.sectionsMap μ₀ ≫ cechAugmentationNat I T := by
    show M.map a₁ ≫ M.map b₁ ≫ M.map c₁ = (M.map d₁ ≫ M.map e₁) ≫ M.map f₁
    exact (congrArg (M.map a₁ ≫ ·) (M.map_comp b₁ c₁).symm).trans
      ((M.map_comp a₁ (b₁ ≫ c₁)).symm.trans ((congrArg M.map hcos).trans
        ((M.map_comp d₁ (e₁ ≫ f₁)).trans ((congrArg (M.map d₁ ≫ ·) (M.map_comp e₁ f₁)).trans
          (Category.assoc _ _ _).symm))))
  have hcomm : cechAugmentation I' T' ≫
      rowZeroMap ((cechDoubleComplex T').map ψ ≫ Φ.cechDoubleMap I.cocomplex) =
        HomologicalComplex.extendMap (Φ.sectionsMap μ₀) ComplexShape.embeddingUpNat ≫
          cechAugmentation I T := by
    have h1 := rowZeroMap_cechDoubleComplex_map (T := T') ψ
    have h2 := Φ.rowZeroMap_cechDoubleMap I.cocomplex
    show (HomologicalComplex.extendMap (cechAugmentationNat I' T') ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₁ 0).inv) ≫
      (rowZeroMap ((cechDoubleComplex T').map ψ) ≫ rowZeroMap (Φ.cechDoubleMap I.cocomplex)) =
      HomologicalComplex.extendMap (Φ.sectionsMap μ₀) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendMap (cechAugmentationNat I T) ComplexShape.embeddingUpNat ≫
          (cosimplicialDoubleComplexColumnIso K₃ 0).inv)
    rw [h1, h2]
    show (HomologicalComplex.extendMap (cechAugmentationNat I' T') ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₁ 0).inv) ≫
      (((cosimplicialDoubleComplexColumnIso K₁ 0).hom ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
          (((cechCosimplicialComplex T').map ψ).f 0)) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₂ 0).inv) ≫
      ((cosimplicialDoubleComplexColumnIso K₂ 0).hom ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map
          ((Φ.cechMap I.cocomplex).f 0)) ComplexShape.embeddingUpNat ≫
        (cosimplicialDoubleComplexColumnIso K₃ 0).inv)) =
      HomologicalComplex.extendMap (Φ.sectionsMap μ₀) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendMap (cechAugmentationNat I T) ComplexShape.embeddingUpNat ≫
          (cosimplicialDoubleComplexColumnIso K₃ 0).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← HomologicalComplex.extendMap_comp_assoc, ← HomologicalComplex.extendMap_comp_assoc,
      ← HomologicalComplex.extendMap_comp_assoc, Category.assoc, hN]
  exact comparisonMapP_naturality _ _ _ _ (cechAugmentation_hypotheses I hT hG hGs) _ _ hcomm

end CechSystemHom

end Crystalline.GlobalCrystallineSituation.SmallSite
