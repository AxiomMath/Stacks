module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.GrassmannianChart.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Recovery27.Functor
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank
public import StacksFrontier.AlgebraicGeometry.Recovery27.Representable.ZariskiSheaf
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.ChartSubfunctors
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.ZariskiSheaf

/-!
# The coordinate charts cover the Grassmannian functor

The coordinate chart subfunctors of the Grassmannian functor `G(k, n)` are open, their
representing affine spaces cover `G(k, n)` (via the case of the spectrum of a field), and hence
`G(k, n)` is representable by the glued scheme `AlgebraicGeometry.Grassmannian.gluedScheme`,
together with its coordinate charts and the universal quotient on each chart.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Grassmannian

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.Hom
attribute [local implicit_reducible] CategoryTheory.Subfunctor.toFunctor
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pullback
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pseudofunctor
attribute [local implicit_reducible] CategoryTheory.Bicategory.Adj.forget₁
attribute [local implicit_reducible] CategoryTheory.Pseudofunctor.comp

/-- A module is zero exactly when its support is empty. -/
private lemma isZero_iff_supp_eq_empty {S : Scheme.{u}} (M : S.Modules) :
    IsZero M ↔ SheafOfModules.supp M = ∅ := by
  constructor
  · intro hM
    ext x
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨U, hx, s, rfl⟩ := M.presheaf.exists_germ_eq a
      have hs : s = 0 := by
        have hid := (IsZero.iff_id_eq_zero M).mp hM
        exact congrArg (fun k : M ⟶ M => k.val.app (op U) s) hid
      refine ha ?_
      rw [hs]
      exact map_zero _
    · simp
  · intro hM
    apply (IsZero.iff_id_eq_zero M).mpr
    apply SheafOfModules.hom_ext
    ext U s
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf S.ringCatSheaf).obj M) U.unop
    intro x hx
    have ha (a : M.presheaf.stalk x) : a = 0 := by
      by_contra h
      exact Set.notMem_empty x (hM ▸ (show x ∈ SheafOfModules.supp M from ⟨a, h⟩))
    exact (ha _).trans (ha _).symm

/-- The open locus where a morphism of modules with target of finite type is surjective, namely
the complement of the support of its cokernel. -/
private noncomputable def surjectiveOpen {S : Scheme.{u}} {M N : S.Modules}
    [N.IsFiniteType] (p : M ⟶ N) : S.Opens := by
  haveI hft : (cokernel p).IsFiniteType :=
    Scheme.Modules.isFiniteType_of_epi (cokernel.π p)
  exact ⟨(SheafOfModules.supp (cokernel p))ᶜ,
    (@SheafOfModules.isClosed_supp _ _ (cokernel p) hft).isOpen_compl⟩

/-- The pullback of a morphism of modules along `f` is surjective exactly when the image of `f`
lies in the surjectivity locus. -/
private lemma epi_pullback_iff_range_subset {S T : Scheme.{u}} {M N : S.Modules}
    [N.IsFiniteType] (p : M ⟶ N) (f : T ⟶ S) :
    Epi ((Scheme.Modules.pullback f).map p) ↔ Set.range f ⊆ surjectiveOpen p := by
  have : (cokernel p).IsFiniteType := Scheme.Modules.isFiniteType_of_epi (cokernel.π p)
  let P := Scheme.Modules.pullback f
  let : PreservesColimitsOfSize.{u, u} P :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  rw [Preadditive.epi_iff_isZero_cokernel,
    ← (PreservesCokernel.iso P p).isZero_iff, isZero_iff_supp_eq_empty,
    Stacks.Modules.supp_pullback]
  show f ⁻¹' SheafOfModules.supp (cokernel p) = ∅ ↔
    Set.range f ⊆ (SheafOfModules.supp (cokernel p))ᶜ
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_preimage, Set.range_subset_iff,
    Set.mem_compl_iff]

/-- A subfunctor whose points over a representable are cut out by the condition that the
morphism have image in a fixed open is representable by open immersions. -/
private lemma subfunctor_isOpenImmersion_of_range
    {F : Scheme.{u}ᵒᵖ ⥤ Type u} (G : Subfunctor F)
    (h : ∀ (S : Scheme.{u}) (g : yoneda.obj S ⟶ F), ∃ U : S.Opens,
      ∀ (T : Scheme.{u}) (f : T ⟶ S),
        g.app (op T) f ∈ G.obj (op T) ↔ Set.range f ⊆ U) :
    IsOpenImmersion.presheaf G.ι := by
  apply MorphismProperty.relative.of_exists
  intro S g
  obtain ⟨U, hU⟩ := h S g
  let a : yoneda.obj (U : Scheme) ⟶ G.toFunctor :=
    yonedaEquiv.symm ⟨g.app (op (U : Scheme)) U.ι,
      (hU U U.ι).mpr (by simp)⟩
  have w : a ≫ G.ι = yoneda.map U.ι ≫ g := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, a, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    rfl
  refine ⟨U, a, U.ι, ?_, inferInstance⟩
  rw [IsPullback.iff_app]
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun t => t.app T) w, ?_, ?_⟩
  · intro f₁ f₂ hf
    apply (cancel_mono U.ι).mp
    exact hf.2
  · intro x f hx
    have hf := (hU T.unop f).mp (hx ▸ x.property)
    let l : T.unop ⟶ (U : Scheme) :=
      IsOpenImmersion.lift U.ι f (by simpa only [Scheme.Opens.range_ι] using hf)
    have hl : l ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
    refine ⟨l, ?_, hl⟩
    apply Subtype.ext
    have hw := congrArg (fun t => t.app T l) w
    change (a.app T l).val = g.app T (l ≫ U.ι) at hw
    exact hw.trans ((congrArg (g.app T) hl).trans hx.symm)

/-- A module that is finite locally free of rank `r` is of finite type. -/
private lemma finiteType_of_rank {S : Scheme.{u}} (M : S.Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    M.IsFiniteType := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  constructor
  refine ⟨q, ?_⟩
  constructor
  intro i
  exact ⟨Finite.of_equiv (Fin r) (hr i).some.symm⟩

/-- The chart condition at a pullback point is the surjectivity of the pullback of the composite
with the coordinate inclusion. -/
private lemma coordinateChartCondition_map_iff_epi_pullback {S T : Scheme.{u}} {k n : ℕ}
    (ι : Fin (n - k) ↪ Fin n) (q : QuotientPresentation S k n)
    (f : T ⟶ S) :
    coordinateChartCondition k n ι T
      ((functor k n).map f.op
        (((functorData k n).objEquiv S).symm ⟦q⟧)) ↔
      Epi ((Scheme.Modules.pullback f).map (coordinateSubmap S k n ι ≫ q.map)) := by
  let q' := pullbackPresentation f q
  rw [coordinateChartCondition_iff_epi k n ι T _ q'
    (points_map_of_isPullback f q q'
      (pullbackPresentation_isPullback f q))]
  have he : (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι ≫ q.map) =
      (pullbackFreeIso f (n - k)).hom ≫
        (coordinateSubmap T k n ι ≫ q'.map) := by
    dsimp only [q', pullbackPresentation]
    rw [Functor.map_comp]
    rw [← Category.assoc, ← coordinateSubmap_pullback_naturality f k n ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [he]
  exact (epi_comp_iff_of_epi _ _).symm

/-- Every point of `G(k, n)` over `S` is the class of a quotient presentation. -/
private lemma exists_eq_objEquiv_symm_mk {S : Scheme.{u}} (k n : ℕ)
    (x : (functor.{u} k n).obj (op S)) :
    ∃ q : QuotientPresentation S k n, x = ((functorData.{u} k n).objEquiv S).symm ⟦q⟧ := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep (((functorData.{u} k n).objEquiv S) x)
  exact ⟨q, (Equiv.eq_symm_apply _).mpr hq.symm⟩

/-- The chart subfunctor is an open subfunctor of `G(k, n)`. -/
private lemma coordinateChartSubfunctor_open (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    IsOpenImmersion.presheaf (coordinateChartSubfunctor.{u} k n ι).ι := by
  apply subfunctor_isOpenImmersion_of_range
  intro S g
  obtain ⟨q, he⟩ := exists_eq_objEquiv_symm_mk k n (yonedaEquiv g)
  have : q.target.IsFiniteType := finiteType_of_rank _ (n - k) q.finiteLocallyFree
  refine ⟨surjectiveOpen (coordinateSubmap S k n ι ≫ q.map), ?_⟩
  intro T f
  have hg : g.app (op T) f = (functor k n).map f.op
      (((functorData.{u} k n).objEquiv S).symm ⟦q⟧) := by
    rw [← he]
    exact (map_yonedaEquiv g f).symm
  show coordinateChartCondition k n ι T (g.app (op T) f) ↔ _
  rw [hg, coordinateChartCondition_map_iff_epi_pullback,
    epi_pullback_iff_range_subset]

/-- The morphism from the chart to `G(k, n)` classifying the universal normalised quotient. -/
private noncomputable def coordinateChartMap (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    yoneda.obj (coordinateChartScheme.{u} ι) ⟶
      functor.{u} k n :=
  yonedaEquiv.symm
    ((coordinateChartPointsEquiv (coordinateChartScheme.{u} ι) k n ι (𝟙 _)).1)

/-- `coordinateChartMap` viewed as a morphism to the chart subfunctor. -/
private noncomputable def coordinateChartMapToSubfunctor (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    yoneda.obj (coordinateChartScheme.{u} ι) ⟶
      (coordinateChartSubfunctor.{u} k n ι).toFunctor :=
  yonedaEquiv.symm
    (coordinateChartPointsEquiv (coordinateChartScheme.{u} ι) k n ι (𝟙 _))

/-- `coordinateChartMap` factors through the chart subfunctor. -/
private lemma coordinateChartMap_factor (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    coordinateChartMapToSubfunctor k n ι ≫
      (coordinateChartSubfunctor.{u} k n ι).ι = coordinateChartMap k n ι := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, coordinateChartMapToSubfunctor, coordinateChartMap]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- The value of `coordinateChartMap` at a morphism into the chart. -/
private lemma coordinateChartMap_apply (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (S : Scheme.{u})
    (g : S ⟶ coordinateChartScheme.{u} ι) :
    (coordinateChartMap k n ι).app (op S) g =
      (coordinateChartPointsEquiv S k n ι g).1 := by
  have hmap := map_yonedaEquiv (coordinateChartMap k n ι) g
  simp only [coordinateChartMap, Equiv.apply_symm_apply] at hmap
  have h := congrArg Subtype.val
    (coordinateChartPointsEquiv_naturality g k n ι (𝟙 _))
  calc
    _ = (functor.{u} k n).map g.op
          ((coordinateChartPointsEquiv (coordinateChartScheme.{u} ι) k n ι (𝟙 _)).1) :=
      hmap.symm
    _ = (coordinateChartPointsEquiv S k n ι g).1 := by
      dsimp [Subfunctor.toFunctor] at h
      simpa only [Category.comp_id] using h.symm

/-- The chart represents the chart subfunctor, so the comparison morphism is an isomorphism. -/
private lemma coordinateChartMapToSubfunctor_isIso (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    IsIso (coordinateChartMapToSubfunctor.{u} k n ι) := by
  have h : (coordinateChartRepresentableBy.{u} k n ι).toIso.hom =
      coordinateChartMapToSubfunctor k n ι := by
    apply yonedaEquiv.injective
    rw [coordinateChartMapToSubfunctor]
    simp only [Equiv.apply_symm_apply]
    rfl
  rw [← h]
  infer_instance

/-- If the chart subfunctor is open in `G(k, n)` then the chart maps to `G(k, n)` by an open
immersion. -/
private lemma coordinateChartMap_open_of_subfunctor_open (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n)
    (h : IsOpenImmersion.presheaf (coordinateChartSubfunctor.{u} k n ι).ι) :
    IsOpenImmersion.presheaf (coordinateChartMap.{u} k n ι) := by
  rw [← coordinateChartMap_factor]
  let := coordinateChartMapToSubfunctor_isIso k n ι
  exact MorphismProperty.RespectsIso.precomp
    IsOpenImmersion.presheaf (coordinateChartMapToSubfunctor k n ι)
      (coordinateChartSubfunctor k n ι).ι h

section

open scoped DirectSum

variable (R : CommRingCat.{u})

/-- The global sections functor on sheaves of modules over `Spec R` is a right adjoint. -/
local instance : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint
/-- The global sections functor on sheaves of modules over `Spec R` is additive. -/
local instance : (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl

/-- The global sections of the structure sheaf of `Spec R` form `R`. -/
private noncomputable def gammaUnitLinearEquiv :
    ((moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf) : Type u) ≃ₗ[R] R :=
  {
    toFun := (Scheme.ΓSpecIso R).hom.hom
    invFun := (Scheme.ΓSpecIso R).inv.hom
    left_inv x := ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).hom_inv_id x
    right_inv x := ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).inv_hom_id x
    map_add' := map_add _
    map_smul' r x := by
      change Γ(Spec R, ⊤) at x
      change (Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv r * (x : Γ(Spec R, ⊤))) =
        r * (Scheme.ΓSpecIso R).hom x
      rw [map_mul]
      congr 1
      exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).inv_hom_id r }

/-- The global sections of the free module of rank `m` on `Spec R` are the direct sum of `m`
copies of `R`. -/
private noncomputable def gammaFreeCoproductIso (m : ℕ) :
    ModuleCat.of R (⨁ _ : ULift.{u} (Fin m),
      ((moduleSpecΓFunctor (R := R)).obj (SheafOfModules.unit (Spec R).ringCatSheaf))) ≅
    (moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin m))) := by
  let G := moduleSpecΓFunctor (R := R)
  let Z : ULift.{u} (Fin m) → ModuleCat R :=
    fun _ => G.obj (SheafOfModules.unit (Spec R).ringCatSheaf)
  let c : Cofan Z := G.mapCocone (SheafOfModules.freeCofan (R := (Spec R).ringCatSheaf)
    (ULift.{u} (Fin m)))
  exact (ModuleCat.coproductCoconeIsColimit Z).coconePointUniqueUpToIso
    (show IsColimit c from isColimitOfPreserves G
      (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin m))))

/-- The basis of the global sections of the free module of rank `m` on `Spec R`. -/
private noncomputable def gammaFreeBasis (m : ℕ) :
    Module.Basis (Fin m) R ((moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin m)))) :=
  ((DFinsupp.basis (fun _ : ULift.{u} (Fin m) =>
    (Module.Basis.singleton PUnit.{1} R).map (gammaUnitLinearEquiv R).symm)).map
      (gammaFreeCoproductIso R m).toLinearEquiv).reindex
        ((Equiv.sigmaUnique _ _).trans Equiv.ulift)

/-- The `i`-th basis vector is the image of `1` under the `i`-th inclusion of the free module. -/
private lemma gammaFreeBasis_apply (m : ℕ) (i : Fin m) :
    gammaFreeBasis R m i =
      (moduleSpecΓFunctor (R := R)).map (SheafOfModules.ιFree (ULift.up i))
        ((gammaUnitLinearEquiv R).symm 1) := by
  have h := (ModuleCat.coproductCoconeIsColimit
    (fun _ : ULift.{u} (Fin m) => (moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf))).comp_coconePointUniqueUpToIso_hom
        (isColimitOfPreserves (moduleSpecΓFunctor (R := R))
          (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin m)))) (Discrete.mk (ULift.up i))
  have hh := congrArg (fun f => f ((gammaUnitLinearEquiv R).symm 1)) h
  simpa [gammaFreeBasis, gammaFreeCoproductIso, ModuleCat.coproductCocone,
    DFinsupp.basis, Module.Basis.map_apply, Module.Basis.singleton_apply,
    SheafOfModules.freeCofan] using! hh

/-- Taking global sections of quasi-coherent modules on an affine scheme preserves surjections. -/
private lemma gamma_epi_of_epi {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    Epi ((moduleSpecΓFunctor (R := R)).map f) := by
  let E := tildeEquiv (R := R)
  let f' : (⟨M, inferInstance⟩ : (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).FullSubcategory) ⟶ ⟨N, inferInstance⟩ :=
    ObjectProperty.homMk f
  have : Epi f' := (ObjectProperty.ι _).epi_of_epi_map (show Epi f from inferInstance)
  exact Functor.map_epi E.inverse f'

/-- A morphism of quasi-coherent modules on an affine scheme which is an isomorphism on global
sections is an isomorphism. -/
private lemma isIso_of_gamma_isIso {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (h : IsIso ((moduleSpecΓFunctor (R := R)).map f)) : IsIso f := by
  let E := tildeEquiv (R := R)
  let f' : (⟨M, inferInstance⟩ : (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).FullSubcategory) ⟶ ⟨N, inferInstance⟩ :=
    ObjectProperty.homMk f
  have : IsIso (E.inverse.map f') := h
  have : IsIso f' := isIso_of_reflects_iso f' E.inverse
  exact Functor.map_isIso (ObjectProperty.ι _) f'

/-- The map of free modules induced by a map of index sets sends basis vectors to basis vectors. -/
private lemma gammaFreeMap_basis {r n : ℕ} (f : Fin r → Fin n) (i : Fin r) :
    (moduleSpecΓFunctor (R := R)).map
      (SheafOfModules.freeMap (R := (Spec R).ringCatSheaf)
        (fun j : ULift.{u} (Fin r) => ULift.up (f j.down))) (gammaFreeBasis R r i) =
      gammaFreeBasis R n (f i) := by
  rw [gammaFreeBasis_apply, gammaFreeBasis_apply]
  show ((moduleSpecΓFunctor (R := R)).map (SheafOfModules.ιFree (ULift.up i)) ≫
    (moduleSpecΓFunctor (R := R)).map (SheafOfModules.freeMap _))
      ((gammaUnitLinearEquiv R).symm 1) = _
  rw [← Functor.map_comp, SheafOfModules.ιFree_freeMap]

end

/-- A module that is finite locally free of rank `r` on the spectrum of a field is free of
rank `r`. -/
private lemma exists_free_iso_of_rank_spec_field (K : Type u) [Field K]
    (M : (Spec (CommRingCat.of K)).Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    Nonempty (M ≅ SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
      (ULift.{u} (Fin r))) := by
  let S := Spec (CommRingCat.of K)
  let x : S := ⟨⊥, inferInstance⟩
  obtain ⟨U, hx, ⟨e⟩⟩ := exists_free_pullback_of_rank M r h x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = x := Subsingleton.elim _ _
    exact hy ▸ hx
  have : IsIso U.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι (by simpa using hU)
  exact ⟨(Scheme.Modules.pullbackId S).symm.app M ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id U.ι).symm).app M ≪≫
    (Scheme.Modules.pullbackComp (inv U.ι) U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback (inv U.ι)).mapIso e ≪≫
    pullbackFreeIso (inv U.ι) r⟩

open Module in
/-- A family of `n` vectors spanning a vector space of dimension `r` contains a basis. -/
private lemma exists_basis_subfamily {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {n r : ℕ} (v : Fin n → V)
    (hs : Submodule.span K (Set.range v) = ⊤) (hr : Module.finrank K V = r) :
    ∃ (ι : Fin r ↪ Fin n) (b : Basis (Fin r) K V), ∀ j, b j = v (ι j) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  let b : Basis κ K V := Basis.mk hli (by rw [hspan, hs])
  have : Finite κ := Finite.of_injective a ha
  let := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := (Module.finrank_eq_card_basis b).symm.trans hr
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨⟨fun i => a (e.symm i), ha.comp e.symm.injective⟩, b.reindex e, ?_⟩
  intro j
  simp [b]

/-- Over a field, `n - k` of the coordinate sections of a quotient presentation already generate
its target. -/
private lemma exists_epi_coordinateSubmap_spec_field (K : Type u) [Field K]
    (k n : ℕ) (q : QuotientPresentation (Spec (CommRingCat.of K)) k n) :
    ∃ ι : Fin (n - k) ↪ Fin n,
      Epi (coordinateSubmap (Spec (CommRingCat.of K)) k n ι ≫ q.map) := by
  classical
  let R := CommRingCat.of K
  let G := moduleSpecΓFunctor (R := R)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} q.target (n - k) :=
    q.finiteLocallyFree
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} q.target :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree q.target (n - k)
  have : Epi q.map := q.map_epi
  have hsurj : Function.Surjective (G.map q.map).hom :=
    (ModuleCat.epi_iff_surjective _).mp (gamma_epi_of_epi R q.map)
  let v : Fin n → G.obj q.target := (G.map q.map).hom ∘ gammaFreeBasis R n
  have hs : Submodule.span K (Set.range v) = ⊤ := by
    rw [show Set.range v = (G.map q.map).hom '' Set.range (gammaFreeBasis R n) from
      Set.range_comp _ _, ← Submodule.map_span, (gammaFreeBasis R n).span_eq,
      Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  obtain ⟨e⟩ := exists_free_iso_of_rank_spec_field K q.target (n - k) q.finiteLocallyFree
  have hr : Module.finrank K (G.obj q.target) = n - k := by
    rw [(G.mapIso e).toLinearEquiv.finrank_eq,
      Module.finrank_eq_card_basis (gammaFreeBasis R (n - k)), Fintype.card_fin]
  obtain ⟨ι, b, hb⟩ := exists_basis_subfamily v hs hr
  refine ⟨ι, ?_⟩
  let p := coordinateSubmap (Spec R) k n ι ≫ q.map
  let e' := (gammaFreeBasis R (n - k)).repr.trans b.repr.symm
  have he' : G.map p = e'.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply (gammaFreeBasis R (n - k)).ext
    intro j
    have hg : (G.map p).hom (gammaFreeBasis R (n - k) j) = v (ι j) := by
      show (G.map (coordinateSubmap (Spec R) k n ι ≫ q.map)).hom _ = _
      rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
      show (G.map q.map).hom (G.map (SheafOfModules.freeMap _) _) = _
      rw [gammaFreeMap_basis]
      rfl
    rw [hg]
    show v (ι j) = b.repr.symm ((gammaFreeBasis R (n - k)).repr
      (gammaFreeBasis R (n - k) j))
    rw [Module.Basis.repr_self, Module.Basis.repr_symm_single]
    simpa using (hb j).symm
  have hΓ : IsIso (G.map p) := by rw [he']; infer_instance
  have : IsIso p := isIso_of_gamma_isIso R p hΓ
  infer_instance

/-- Every point of the base has a neighbourhood on which a given presentation satisfies the chart
condition for some embedding `ι`. -/
private lemma exists_coordinateChart_neighborhood {S : Scheme.{u}} (k n : ℕ)
    (q : QuotientPresentation S k n) (s : S) :
    ∃ (ι : Fin (n - k) ↪ Fin n) (U : S.Opens), s ∈ U ∧
      coordinateChartCondition k n ι U
        ((functor k n).map U.ι.op
          (((functorData k n).objEquiv S).symm ⟦q⟧)) := by
  let f := S.fromSpecResidueField s
  let q' := pullbackPresentation f q
  obtain ⟨ι, hi⟩ := exists_epi_coordinateSubmap_spec_field (S.residueField s) k n q'
  have hC : coordinateChartCondition k n ι (Spec (S.residueField s))
      ((functor k n).map f.op
        (((functorData k n).objEquiv S).symm ⟦q⟧)) :=
    (coordinateChartCondition_iff_epi k n ι _ _ q'
      (points_map_of_isPullback f q q'
        (pullbackPresentation_isPullback f q))).mpr hi
  have : q.target.IsFiniteType := finiteType_of_rank _ (n - k) q.finiteLocallyFree
  let p := coordinateSubmap S k n ι ≫ q.map
  let U := surjectiveOpen p
  have hrange : Set.range f ⊆ U := (epi_pullback_iff_range_subset p f).mp
    ((coordinateChartCondition_map_iff_epi_pullback ι q f).mp hC)
  refine ⟨ι, U, ?_, ?_⟩
  · apply hrange
    exact ⟨⟨⊥, inferInstance⟩, S.fromSpecResidueField_apply s _⟩
  · apply (coordinateChartCondition_map_iff_epi_pullback ι q U.ι).mpr
    apply (epi_pullback_iff_range_subset p U.ι).mpr
    rintro x ⟨y, rfl⟩
    exact y.property

/-- The charts cover `G(k, n)`: the morphism from their disjoint union is locally surjective for
the Zariski topology. -/
private lemma coordinateChartMap_isLocallySurjective (k n : ℕ) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun i : ULift.{u} (Fin (n - k) ↪ Fin n) =>
        coordinateChartMap.{u} k n i.down)) := by
  classical
  let F := functor.{u} k n
  let f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down
  constructor
  intro S x
  obtain ⟨q, hx⟩ := exists_eq_objEquiv_symm_mk k n x
  choose i U hs hi using exists_coordinateChart_neighborhood k n q
  have hU : IsOpenCover U := IsOpenCover.mk <| by
    apply top_unique
    intro s _
    exact Opens.mem_iSup.mpr ⟨s, hs s⟩
  apply Scheme.zariskiTopology.superset_covering _
    (openCoverOfOpens U hU).mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  intro T g hg
  obtain ⟨s⟩ := hg
  let y : (coordinateChartSubfunctor k n (i s)).obj (op (U s : Scheme)) :=
    ⟨F.map (U s).ι.op x, hx ▸ hi s⟩
  let a : (U s : Scheme) ⟶ coordinateChartScheme (i s) :=
    (coordinateChartPointsEquiv (U s) k n (i s)).symm y
  refine ⟨(Sigma.ι (fun j : ULift.{u} (Fin (n - k) ↪ Fin n) =>
    yoneda.obj (coordinateChartScheme.{u} j.down)) (ULift.up (i s))).app (op (U s : Scheme)) a,
    ?_⟩
  have h := congrArg (fun t => t.app (op (U s : Scheme)) a)
    (Sigma.ι_desc f (ULift.up (i s)))
  exact h.trans ((coordinateChartMap_apply k n (i s) (U s) a).trans
    (congrArg Subtype.val ((coordinateChartPointsEquiv (U s) k n (i s)).apply_symm_apply y)))

/-- The Grassmannian functor `G(k, n)` is representable by a scheme when `0 < k < n`. -/
@[stacks 089T, sga "6 VI 4.1" "Grassmannian, free case"]
public theorem functor_isRepresentable (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    (functor.{u} k n).IsRepresentable := by
  let := coordinateChartMap_isLocallySurjective.{u} k n
  exact Scheme.LocalRepresentability.isRepresentable
    (F := ⟨functor k n, functor_isSheaf k n⟩)
    (f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap k n i.down)
    (fun i => coordinateChartMap_open_of_subfunctor_open k n i.down
      (coordinateChartSubfunctor_open k n i.down))

/-- Each coordinate chart maps to `G(k, n)` by a relatively representable open immersion. -/
private theorem coordinateChartMap_isOpenImmersion (k n : ℕ)
    (i : ULift.{u} (Fin (n - k) ↪ Fin n)) :
    IsOpenImmersion.presheaf (coordinateChartMap.{u} k n i.down) :=
  coordinateChartMap_open_of_subfunctor_open k n i.down
    (coordinateChartSubfunctor_open k n i.down)

/-- The Grassmannian functor as a sheaf on the big Zariski site of schemes. -/
private noncomputable def functorSheaf (k n : ℕ) : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨functor.{u} k n, functor_isSheaf k n⟩

/-- The scheme glued from the coordinate charts of `G(k, n)`. It represents `G(k, n)` by
`AlgebraicGeometry.Grassmannian.representableBy`. -/
@[sga "6 VI 4.9" "special case"]
public noncomputable def gluedScheme (k n : ℕ) : Scheme.{u} :=
  (Scheme.LocalRepresentability.glueData (F := functorSheaf.{u} k n)
    (f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down)
    (coordinateChartMap_isOpenImmersion k n)).glued

/-- The universal representation of `G(k, n)`: a morphism from a scheme `S` to
`AlgebraicGeometry.Grassmannian.gluedScheme k n` is the same datum as an isomorphism class of
finite locally free rank-`n - k` quotients of the free module of rank `n` on `S`, for all `k`
and `n`. -/
public noncomputable def representableBy (k n : ℕ) :
    (functor.{u} k n).RepresentableBy (gluedScheme.{u} k n) :=
  @Scheme.LocalRepresentability.representableBy (functorSheaf.{u} k n) _ _
    (fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down)
    (coordinateChartMap_isOpenImmersion k n)
    (coordinateChartMap_isLocallySurjective k n)

/-! ### The coordinate charts

The charts of the glued scheme: for every embedding `ι` of
`Fin (n - k)` into `Fin n` the affine space over `Spec ℤ` on the chart coordinates maps to
`G(k, n)` by an open immersion, and these open immersions cover `G(k, n)`. -/

/-- The coordinates of the chart of `G(k, n)` attached to an embedding `ι`: for each basis
vector of the free module of rank `n` outside the range of `ι`, its `n - k` coordinates in the
normalised quotient. -/
public abbrev ChartIndex {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) : Type u :=
  ULift.{u} ({j // j ∉ Set.range ι} × Fin (n - k))

/-- The coordinate chart of `G(k, n)` attached to an embedding `ι`: the affine space over
`Spec ℤ` on the chart coordinates, mapped into the glued scheme. -/
public noncomputable def chartMap (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))) ⟶ gluedScheme.{u} k n :=
  Scheme.LocalRepresentability.toGlued (F := functorSheaf.{u} k n)
    (f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down)
    (coordinateChartMap_isOpenImmersion k n) (ULift.up ι)

/-- Each coordinate chart is an open immersion. -/
public instance isOpenImmersion_chartMap (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    IsOpenImmersion (chartMap.{u} k n ι) :=
  Scheme.LocalRepresentability.instIsOpenImmersionToGlued
    (F := functorSheaf.{u} k n)
    (f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down)
    (coordinateChartMap_isOpenImmersion k n) (ULift.up ι)

/-- The coordinate charts cover `G(k, n)`. -/
public theorem exists_mem_range_chartMap (k n : ℕ) (x : gluedScheme.{u} k n) :
    ∃ ι : Fin (n - k) ↪ Fin n, x ∈ Set.range (chartMap.{u} k n ι) := by
  let 𝒰 := (Scheme.LocalRepresentability.glueData
    (F := functorSheaf.{u} k n)
    (f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down)
    (coordinateChartMap_isOpenImmersion k n)).openCover
  obtain ⟨y, hy⟩ := 𝒰.covers x
  exact ⟨(𝒰.idx x).down, y, hy⟩

/-! ### The universal quotient on a chart

On the chart attached to `ι` the universal quotient `𝒪^n ⟶ 𝒪^{n - k}` sends `e_{ι i}` to `f_i`
and `e_j`, for `j` outside the range of `ι`, to `∑_i x_{j,i} f_i`. The statements below record
this, how two charts agreeing on a scheme compare, and when a point of one chart lies in
another. -/

/-- The normalised quotient attached to a morphism into the chart. -/
private noncomputable def chartNormalizedQuotient {T : Scheme.{u}} (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (g : T ⟶ coordinateChartScheme.{u} ι) :
    NormalizedQuotient T k n ι :=
  (normalizedQuotientCoefficientsEquiv T k n ι).symm
    (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} ι) g)

/-- **The quotient `𝒪_T^n ⟶ 𝒪_T^{n - k}` classified by a morphism `g` into the chart attached to
`ι`**: the universal normalised quotient of the chart pulled back along `g`. -/
public noncomputable def chartQuotientMap {T : Scheme.{u}} (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) :
    SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (n - k))) :=
  (chartNormalizedQuotient k n ι g).1

/-- The quotient classified by a morphism into the chart attached to `ι` sends `e_{ι i}` to
`f_i`. -/
public theorem ιFree_comp_chartQuotientMap {T : Scheme.{u}} (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) (i : Fin (n - k)) :
    SheafOfModules.ιFree (R := T.ringCatSheaf) (ULift.up.{u} (ι i)) ≫ chartQuotientMap k n ι g =
      SheafOfModules.ιFree (ULift.up.{u} i) := by
  have h := congrArg (fun f => SheafOfModules.ιFree (R := T.ringCatSheaf)
    (ULift.up i) ≫ f) (chartNormalizedQuotient k n ι g).2
  simp only [Category.comp_id] at h
  rw [← h, ← Category.assoc]
  exact congrArg (fun f => f ≫ chartQuotientMap k n ι g)
    (SheafOfModules.ιFree_freeMap (R := T.ringCatSheaf)
      (fun i : ULift.{u} (Fin (n - k)) => ULift.up (ι i.down)) (ULift.up i)).symm

/-- The quotient classified by a morphism `g` into the chart attached to `ι` sends `e_j`, for `j`
outside the range of `ι`, to the section whose `i`-th coordinate is the pullback along `g` of
the coordinate `x_{j,i}`. -/
public theorem chartQuotientMap_coeff {T : Scheme.{u}} (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))) (j : Fin n)
    (hj : j ∉ Set.range ι) (i : Fin (n - k)) :
    (((SheafOfModules.unit T.ringCatSheaf).unitHomEquiv
        (SheafOfModules.ιFree (R := T.ringCatSheaf) (ULift.up.{u} j) ≫ chartQuotientMap k n ι g ≫
          SheafOfModules.freeProjection (ULift.up.{u} i))).1 (op ⊤) : Γ(T, ⊤)) =
      AffineSpace.toSpecMvPolyIntEquiv _ g (ULift.up (⟨j, hj⟩, i)) := by
  have h1 := freeSectionsEquiv_unitHom_apply T (n - k)
    (SheafOfModules.ιFree (R := T.ringCatSheaf) (ULift.up j) ≫ chartQuotientMap k n ι g) i
  rw [Category.assoc] at h1
  show unitSectionsEquiv T ((SheafOfModules.unit T.ringCatSheaf).unitHomEquiv
    (SheafOfModules.ιFree (R := T.ringCatSheaf) (ULift.up.{u} j) ≫ chartQuotientMap k n ι g ≫
      SheafOfModules.freeProjection (ULift.up.{u} i))) = _
  rw [← h1]
  have h2 := congrArg (fun v => v (ULift.up (⟨j, hj⟩, i)))
    ((normalizedQuotientCoefficientsEquiv T k n ι).apply_symm_apply
      (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} ι) g))
  exact h2

/-- The point of `G(k, n)` given by a morphism into a chart is the class of its normalised
quotient. -/
private lemma homEquiv_comp_chartMap {T : Scheme.{u}} (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (g : T ⟶ coordinateChartScheme.{u} ι) :
    (representableBy.{u} k n).homEquiv (g ≫ chartMap k n ι) =
      (coordinateChartPointsEquiv T k n ι g).1 := by
  rw [(representableBy.{u} k n).homEquiv_comp]
  have h2 : (representableBy.{u} k n).homEquiv (chartMap k n ι) =
      yonedaEquiv (coordinateChartMap.{u} k n ι) :=
    Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued
      (F := functorSheaf.{u} k n)
      (f := fun i : ULift.{u} (Fin (n - k) ↪ Fin n) => coordinateChartMap.{u} k n i.down)
      (coordinateChartMap_isOpenImmersion k n) (i := ULift.up ι)
  rw [h2, map_yonedaEquiv, coordinateChartMap_apply]

/-- The class of the normalised quotient of a morphism into a chart. -/
private lemma objEquiv_homEquiv_comp_chartMap {T : Scheme.{u}} (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (g : T ⟶ coordinateChartScheme.{u} ι) :
    (functorData.{u} k n).objEquiv T ((representableBy.{u} k n).homEquiv (g ≫ chartMap k n ι)) =
      ⟦normalizedQuotientPresentation T k n ι (chartNormalizedQuotient k n ι g)⟧ := by
  rw [homEquiv_comp_chartMap]
  show (functorData.{u} k n).objEquiv T
    (((functorData.{u} k n).objEquiv T).symm ⟦normalizedQuotientPresentation T k n ι
      (chartNormalizedQuotient k n ι g)⟧) = _
  rw [Equiv.apply_symm_apply]

/-- **Two charts that agree on a scheme classify isomorphic quotients.** If
`g ≫ chart ι = h ≫ chart κ`, the two quotients `𝒪_T^n ⟶ 𝒪_T^{n - k}` differ by an automorphism
of `𝒪_T^{n - k}`. -/
public theorem exists_iso_chartQuotientMap_comp_eq_of_chartMap {T : Scheme.{u}} {k n : ℕ}
    {ι κ : Fin (n - k) ↪ Fin n}
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hgh : g ≫ chartMap k n ι = h ≫ chartMap k n κ) :
    ∃ e : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (n - k))) ≅
        SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (n - k))),
      chartQuotientMap k n ι g ≫ e.hom = chartQuotientMap k n κ h := by
  have hcl := (objEquiv_homEquiv_comp_chartMap k n ι g).symm.trans
    ((congrArg (fun x => (functorData.{u} k n).objEquiv T
      ((representableBy.{u} k n).homEquiv x)) hgh).trans
      (objEquiv_homEquiv_comp_chartMap k n κ h))
  obtain ⟨e, he⟩ := quotientPresentation_isomorphic_of_eq hcl
  exact ⟨e, he⟩

/-- **A point of the chart attached to `κ` lies in the chart attached to `ι` as soon as its
quotient restricted to the coordinates `ι` is an isomorphism.** -/
public theorem exists_comp_chartMap_eq_of_isIso {T : Scheme.{u}} {k n : ℕ}
    {ι κ : Fin (n - k) ↪ Fin n}
    (h : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))))
    (hiso : IsIso (SheafOfModules.freeMap (R := T.ringCatSheaf)
      (fun i : ULift.{u} (Fin (n - k)) => ULift.up (ι i.down)) ≫ chartQuotientMap k n κ h)) :
    ∃ g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))),
      g ≫ chartMap k n ι = h ≫ chartMap k n κ := by
  let q := normalizedQuotientPresentation T k n κ (chartNormalizedQuotient k n κ h)
  have hcond : coordinateChartCondition k n ι T
      ((coordinateChartPointsEquiv T k n κ h).1) := by
    refine ⟨q, ?_, ?_⟩
    · show (functorData.{u} k n).objEquiv T
        (((functorData.{u} k n).objEquiv T).symm ⟦q⟧) = _
      rw [Equiv.apply_symm_apply]
    · show Epi (SheafOfModules.freeMap (R := T.ringCatSheaf)
        (fun i : ULift.{u} (Fin (n - k)) => ULift.up (ι i.down)) ≫ chartQuotientMap k n κ h)
      infer_instance
  let y : (coordinateChartSubfunctor.{u} k n ι).obj (op T) :=
    ⟨(coordinateChartPointsEquiv T k n κ h).1, hcond⟩
  refine ⟨(coordinateChartPointsEquiv T k n ι).symm y, ?_⟩
  apply (representableBy.{u} k n).homEquiv.injective
  rw [homEquiv_comp_chartMap, homEquiv_comp_chartMap, Equiv.apply_symm_apply]

end AlgebraicGeometry.Grassmannian

end
