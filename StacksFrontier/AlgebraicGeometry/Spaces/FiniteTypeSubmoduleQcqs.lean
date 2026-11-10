module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCoveringAffineMemberCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleSquareExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
import all StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionCollections
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent modules on a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space and `M` a quasi-coherent
`𝒪_X`-module. This file proves [Stacks, Tag 0829]: `M` is the directed colimit of its
quasi-coherent submodules of finite type.

The heart of the proof is the statement that **finitely many sections of `M` over affine étale
charts lie in a quasi-coherent submodule of finite type**,
`AlgebraicGeometry.Space.exists_isFiniteType_submodule_mem_of_qcqs`. It is proved by the
induction principle [Stacks, Tag 08GP], `AlgebraicGeometry.Space.qcqs_induction_on_self`: the
affine case is `AlgebraicGeometry.Space.exists_isFiniteType_submodule_mem_of_isAffineSpace`, and
across an elementary distinguished square `(U ⊂ W, V ⟶ W)` with `V` affine:

* the sections are restricted to finitely many affine charts of `U` and of `V` covering their
  charts (`AlgebraicGeometry.Space.exists_finite_affine_eds_charts_covering`);
* those over charts of `V` are combinations of restrictions of finitely many sections `c` over
  the terminal chart `T_V` of `V`;
* the induction hypothesis on `U`, applied to the sections over charts of `U` together with the
  restrictions of the `c` to finitely many affine charts covering the part of `T_V` over `U`,
  gives `N₀ ⊆ M|_U`;
* `AlgebraicGeometry.Space.exists_isFiniteType_le_etaleSubmoduleRestrict_etaleSubmodulePushforward`
  extends `N₀` to `N ⊆ M|_V` containing the `c` and agreeing with `N₀` over `U ×_W V`;
* `AlgebraicGeometry.Space.etaleSubmoduleGlue` glues `N₀` and `N`
  (`AlgebraicGeometry.Space.edsMemberSubmodule_compatible_of_le`).

Directedness of the finite type quasi-coherent submodules is
`AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobject_isFiltered`, which is unconditional,
and the colimit assertion follows from the statement above because every section
over an affine chart lies in one of them.

## Main results

* `AlgebraicGeometry.Space.exists_isFiniteType_submodule_mem_of_qcqs`: finitely many sections
  over affine charts lie in a quasi-coherent submodule of finite type.
* `isFiltered_and_nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs`: the
  quasi-coherent submodules of finite type of `M` form a filtered family whose cocone is a colimit
  cocone.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Sections over affine charts as combinations of sections over a terminal chart -/

/-- **Finitely many sections of a quasi-coherent module over affine charts are combinations of
restrictions of finitely many sections over a terminal affine chart** (Stacks 03DX(2)). -/
theorem exists_fin_mem_span_chartRestrictLinear_of_isTerminal
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite) {T₀ : SmallEtale B S hS F}
    (hT₀ : IsTerminal T₀) (hT₀a : IsAffine (chartScheme T₀)) {ι : Type*} [Finite ι]
    (T : ι → SmallEtale B S hS F) (hT : ∀ i, IsAffine (chartScheme (T i)))
    (s : ∀ i, M.val.obj (op (T i))) :
    ∃ (n : ℕ) (c : Fin n → M.val.obj (op T₀)), ∀ i, s i ∈ Submodule.span
      (chartRing B S hS F hF (T i)) (Set.range fun l => chartRestrictLinear M (hT₀.from (T i)) (c
          l)) := by
  classical
  have hz : ∀ i, ∃ z, sectionsBaseChange M (hT₀.from (T i)) z = s i := fun i =>
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF M hM hT₀a (hT i)
      (hT₀.from (T i))).2 (s i)
  choose z hz using hz
  have hP : ∀ i, ∃ P : Finset (chartRing B S hS F hF (T i) × M.val.obj (op T₀)),
      let := chartAlgebra (hF := hF) (hT₀.from (T i))
      z i = P.sum fun p => p.1 ⊗ₜ[chartRing B S hS F hF T₀] p.2 := fun i => by
    let := chartAlgebra (hF := hF) (hT₀.from (T i))
    exact TensorProduct.exists_finset (z i)
  choose P hP using hP
  have := Fintype.ofFinite ι
  let Fall : Finset (M.val.obj (op T₀)) := Finset.univ.biUnion fun i => (P i).image Prod.snd
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Fall
  refine ⟨n, fun l => (e.symm l).1, fun i => ?_⟩
  rw [← hz, hP, map_sum]
  refine Submodule.sum_mem _ fun p hp => ?_
  rw [chartBaseChange_tmul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e ⟨p.2, ?_⟩, ?_⟩)
  · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hp⟩
  · simp

/-- Membership of a restricted section in a submodule is stable under further restriction. -/
private theorem map_comp_mem_submodule {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {M : Modules.{u, u} B S hS F hF} (N : M.Submodule)
    {A Y Z : SmallEtale B S hS F} (g : A ⟶ Y) (h : Z ⟶ A) {x : M.val.obj (op Y)}
    (hx : M.val.map g.op x ∈ N.obj (op A)) : M.val.map (h ≫ g).op x ∈ N.obj (op Z) :=
  mem_of_eq_of_mem (ConcreteCategory.congr_hom (M.val.map_comp g.op h.op) x) (N.map_mem h.op hx)

/-! ### The property proved by induction -/

variable (B S hS) in
/-- **Finitely many sections of a quasi-coherent module over affine charts lie in a
quasi-coherent submodule of finite type**: the property of an algebraic space `Y` proved for
quasi-compact quasi-separated `Y` by the induction principle of Stacks 08GP. -/
def HasFiniteTypeSubmoduleCapture (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B S hS Y) : Prop :=
  ∀ (M : Modules.{u, u} B S hS Y hY), M.IsQuasicoherentOnSite →
    ∀ (ι : Type u) [Finite ι] (T : ι → SmallEtale B S hS Y),
      (∀ i, IsAffine (chartScheme (T i))) → ∀ s : ∀ i, M.val.obj (op (T i)),
        ∃ N : M.Submodule, N.toSheafOfModules.IsQuasicoherentOnSite ∧
          N.toSheafOfModules.IsFiniteTypeOnSite ∧ ∀ i, s i ∈ N.obj (op (T i))

/-- An affine algebraic space has the property. -/
theorem hasFiniteTypeSubmoduleCapture_of_isAffineSpace {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYa : IsAffineSpace B S hS Y) :
    HasFiniteTypeSubmoduleCapture B S hS Y hY := fun M hM _ _ T hT s =>
  exists_isFiniteType_submodule_mem_of_isAffineSpace hYa M hM T hT s

/-! ### Affine charts of the two members of an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **An affine chart of the target of an elementary distinguished square is covered by
finitely many affine charts of its open member and of its étale member.** -/
theorem exists_finite_affine_eds_charts_covering (T : SmallEtale B S hS W.1)
    (hT : IsAffine (chartScheme T)) :
    ∃ (κ₀ κ₁ : Type) (_ : Finite κ₀) (_ : Finite κ₁)
      (E₀ : κ₀ → SmallEtale B S hS (edsOpen B S hS hsq).1)
      (g₀ : ∀ k, (smallEtalePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj (E₀ k) ⟶ T)
      (E₁ : κ₁ → SmallEtale B S hS (edsEtale B S hS hsq).1)
      (g₁ : ∀ k, (smallEtalePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj (E₁ k) ⟶ T),
      (∀ k, IsAffine (chartScheme (E₀ k))) ∧ (∀ k, IsAffine (chartScheme (E₁ k))) ∧
        Sieve.ofArrows _ g₀ ⊔ Sieve.ofArrows _ g₁ ∈ SmallEtale.topology B S hS W.1 T := by
  classical
  let Y := edsMember B S hS hsq Uo hsq.isOpenSubspace
  let f := edsMemberHom B S hS hsq Uo hsq.isOpenSubspace
  have hf := isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace
  have hsurj : ∀ x : points B S hS W.1, ∃ i, ∃ y : points B S hS (Y i).1,
      pointsMap B S hS (Y i).1 (f i).hom y = x := fun x => by
    have hx : x ∈ ⋃ i, Set.range (pointsMap B S hS (Y i).1 (f i).hom) :=
      (isEtaleCovering_edsMember hsq).jointly_surjective.symm ▸ Set.mem_univ x
    exact Set.mem_iUnion.1 hx
  obtain ⟨κ, _, b, E, g, hEa, hcov⟩ := exists_finite_affine_member_charts_covering B S hS
    Y f hf hsurj T hT
  let A : ∀ (i : ULift.{u} Bool) (E' : SmallEtale B S hS (Y i).1),
      ((smallEtalePostcomp B S hS (f i) (hf i)).obj E' ⟶ T) → Prop := fun i E' g' =>
    ∃ (E'' : SmallEtale B S hS (edsOpen B S hS hsq).1)
      (g'' : (smallEtalePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj E'' ⟶ T)
      (h : (smallEtalePostcomp B S hS (f i) (hf i)).obj E' ⟶ (smallEtalePostcomp B S hS
          (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).obj E''),
      IsAffine (chartScheme E'') ∧ g' = h ≫ g''
  let A' : ∀ (i : ULift.{u} Bool) (E' : SmallEtale B S hS (Y i).1),
      ((smallEtalePostcomp B S hS (f i) (hf i)).obj E' ⟶ T) → Prop := fun i E' g' =>
    ∃ (E'' : SmallEtale B S hS (edsEtale B S hS hsq).1)
      (g'' : (smallEtalePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj E'' ⟶ T)
      (h : (smallEtalePostcomp B S hS (f i) (hf i)).obj E' ⟶ (smallEtalePostcomp B S hS
          (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj E''),
      IsAffine (chartScheme E'') ∧ g' = h ≫ g''
  have key : ∀ i E' g', IsAffine (chartScheme E') → A i E' g' ∨ A' i E' g'
    | ⟨true⟩, E', g', hE' => Or.inl ⟨E', g', 𝟙 _, hE', (Category.id_comp _).symm⟩
    | ⟨false⟩, E', g', hE' => Or.inr ⟨E', g', 𝟙 _, hE', (Category.id_comp _).symm⟩
  let κ₀ := {k : κ // A (b k) (E k) (g k)}
  let κ₁ := {k : κ // ¬ A (b k) (E k) (g k)}
  have hA' : ∀ k : κ₁, A' (b k.1) (E k.1) (g k.1) := fun k =>
    (key (b k.1) (E k.1) (g k.1) (hEa k.1)).resolve_left k.2
  refine ⟨κ₀, κ₁, inferInstance, inferInstance, fun k => k.2.choose,
    fun k => k.2.choose_spec.choose, fun k => (hA' k).choose,
    fun k => (hA' k).choose_spec.choose, fun k => k.2.choose_spec.choose_spec.choose_spec.1,
    fun k => (hA' k).choose_spec.choose_spec.choose_spec.1, ?_⟩
  refine (SmallEtale.topology B S hS W.1).superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro k
  by_cases hAk : A (b k) (E k) (g k)
  · exact Or.inl ((Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨k, hAk⟩,
      hAk.choose_spec.choose_spec.choose, hAk.choose_spec.choose_spec.choose_spec.2⟩)
  · exact Or.inr ((Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨k, hAk⟩,
      (hA' ⟨k, hAk⟩).choose_spec.choose_spec.choose,
      (hA' ⟨k, hAk⟩).choose_spec.choose_spec.choose_spec.2⟩)

/-- **The induction step of the module form of Stacks 0829.** Across an elementary
distinguished square `(U ⊂ W, V ⟶ W)` with `W` quasi-separated, `U` quasi-compact and `V`
affine, the property `AlgebraicGeometry.Space.HasFiniteTypeSubmoduleCapture` passes from `U`
to `W`. -/
theorem hasFiniteTypeSubmoduleCapture_of_isElementaryDistinguishedSquare
    (hZ : B.Contains (⊤_ Scheme.{u})) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVa : IsAffineSpace B S hS Ve)
    (hU : HasFiniteTypeSubmoduleCapture B S hS Uo.toFunctor hsq.isOpenSubspace.1) :
    HasFiniteTypeSubmoduleCapture B S hS W.1 W.2 := by
  classical
  intro M hM ι _ T hT s
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ Ve :=
    isAbsolutelyQuasiSeparated_of_isAffineSpace_aux B S hS hZ Ve hVa
  obtain ⟨T₀, hT₀a, ⟨e⟩⟩ := hVa
  have hTV := isTerminalAffineSpaceChart (B := B) (S := S) (hS := hS) e
  have hTVa : IsAffine (chartScheme (affineSpaceChart (B := B) (S := S) (hS := hS) e)) := hT₀a
  have hMV : ((etaleModulePullback B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS
      hsq)).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS _ _ M hM
  have hMU : ((etaleModulePullback B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS
      hsq)).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS _ _ M hM
  -- the charts of `W` covered by affine charts of the two members
  choose κ₀ κ₁ hκ₀ hκ₁ E₀ g₀ E₁ g₁ hE₀a hE₁a hcovT using
    fun i => exists_finite_affine_eds_charts_covering hsq (T i) (hT i)
  -- the sections over charts of `V` from finitely many sections over the terminal chart
  obtain ⟨n, c, hc⟩ := exists_fin_mem_span_chartRestrictLinear_of_isTerminal ((etaleModulePullback
      B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj M) hMV hTV hTVa
    (fun p : Σ i, κ₁ i => E₁ p.1 p.2) (fun p => hE₁a p.1 p.2)
    (fun p => M.val.map (g₁ p.1 p.2).op (s p.1))
  -- the part of the terminal chart over `U`
  obtain ⟨κO, _, O, ιO, hOa, hcovO⟩ :=
    exists_finite_affine_cover_edsOverPart hsq hZ hWqs hUqc _ hTVa
  obtain ⟨cO, hcO⟩ : ∃ cO : ∀ j, yoneda.obj (O j).1.left ⟶ Uo.toFunctor,
      ∀ j, cO j ≫ Uo.ι = (O j).1.hom ≫ fV :=
    ⟨fun j => _, fun j => comp_ι_eq_of_hom (ιO j) (edsOverPart_comp_ι_eq hsq _)⟩
  -- the induction hypothesis on `U`
  obtain ⟨N₀, hN₀q, hN₀f, hN₀mem⟩ := hU ((etaleModulePullback B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj M) hMU ((Σ i, κ₀ i) ⊕ (Fin n × κO))
    (Sum.elim (fun p => E₀ p.1 p.2)
      (fun q => edsOpenChartOfFactor hsq (O q.2) (cO q.2) (hcO q.2)))
    (by rintro (p | q); exacts [hE₀a p.1 p.2, hOa q.2])
    (Sum.rec (fun p => M.val.map (g₀ p.1 p.2).op (s p.1))
      (fun q => edsReadOnOpen hsq (O q.2) (cO q.2) (hcO q.2)
        (((etaleModulePullback B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS
            hsq)).obj M).val.map (hTV.from (O q.2)).op (c q.1))))
  -- the sections `c` lie in the pullback to `V` of the pushforward of `N₀`
  have hcG : ∀ m, c m ∈ (etaleSubmoduleRestrict B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) N₀)).obj (op (affineSpaceChart e)) :=
    fun m => mem_etaleSubmoduleRestrict_etaleSubmodulePushforward_of_forall hsq N₀ hTV O ιO
      hcovO (c m) fun j Q p h => by
        have hO := (mem_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff_of_factor hsq N₀ (O j)
          (cO j) (hcO j) (((etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS
              hsq)).obj M).val.map (hTV.from (O j)).op (c m))).2 (hN₀mem (.inr (m, j)))
        obtain rfl : p = h ≫ hTV.from (O j) := hTV.hom_ext _ _
        exact map_comp_mem_submodule _ _ h hO
  -- the extension to `V`
  obtain ⟨N, hNq, hNf, hcN, hNG, hGN⟩ :=
    exists_isFiniteType_le_etaleSubmoduleRestrict_etaleSubmodulePushforward hsq N₀ hZ hVqs hM
      hN₀q hN₀f hTV hTVa O ιO hOa hcovO cO hcO c hcG
  have h₁ := (le_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
      N₀ N).2 fun T' T'' g x hx => hGN T'' (yoneda.map g.hom.left ≫ T'.1.hom)
        ((Category.assoc _ _ _).trans (CostructuredArrow.w g.hom))
        (map_mem_etaleSubmoduleRestrict_etaleSubmodulePushforward hsq N₀ T' T'' g hx)
  -- the glued submodule
  have hK := isQuasicoherentOnSite_and_isFiniteTypeOnSite_etaleSubmoduleGlue hsq N₀ N h₁ hNG hN₀q
    hN₀f hNq hNf
  have hKU := etaleSubmoduleRestrict_edsOpenHom_etaleSubmoduleGlue hsq N₀ N h₁ hNG
  have hKV := etaleSubmoduleRestrict_edsEtaleHom_etaleSubmoduleGlue hsq N₀ N h₁ hNG
  generalize etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
    (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
    (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
    (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀ N) = K at hK hKU hKV
  refine ⟨K, hK.1, hK.2, fun i => ?_⟩
  refine K.isSheaf (s i) ((SmallEtale.topology B S hS W.1).superset_covering ?_ (hcovT i))
  rintro Z f (hf | hf)
  · obtain ⟨k, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    have hk := hN₀mem (.inl ⟨i, k⟩)
    rw [← hKU] at hk
    have hk' := (mem_etaleSubmoduleRestrict_obj B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) K (E₀ i k) _).1 hk
    exact map_comp_mem_submodule K (g₀ i k) h hk'
  · obtain ⟨k, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    have hspan : Submodule.span (chartRing B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2 (E₁ i k)) (Set.range fun l => chartRestrictLinear
          ((etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj M) (hTV.from (E₁ i k)) (c l)) ≤
          N.obj (op (E₁ i k)) :=
      Submodule.span_le.2 (by
        rintro _ ⟨l, rfl⟩
        exact N.map_mem _ (hcN l))
    have hk : M.val.map (g₁ i k).op (s i) ∈ N.obj (op (E₁ i k)) := hspan (hc ⟨i, k⟩)
    rw [← hKV] at hk
    have hk' := (mem_etaleSubmoduleRestrict_obj B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) K (E₁ i k) _).1 hk
    exact map_comp_mem_submodule K (g₁ i k) h hk'

end Square

/-! ### The conclusion -/

/-- **Finitely many sections of a quasi-coherent module over affine charts of a quasi-compact
quasi-separated algebraic space lie in a quasi-coherent submodule of finite type.** The
induction principle of Stacks 08GP, with the affine case
`AlgebraicGeometry.Space.hasFiniteTypeSubmoduleCapture_of_isAffineSpace` and the step
`AlgebraicGeometry.Space.hasFiniteTypeSubmoduleCapture_of_isElementaryDistinguishedSquare`. -/
theorem hasFiniteTypeSubmoduleCapture_of_qcqs (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    HasFiniteTypeSubmoduleCapture B S hS X.1 X.2 :=
  qcqs_induction_on_self B S hS hZ X hqc hqs
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y, HasFiniteTypeSubmoduleCapture B S hS Y hY)
    (fun _ hV hY => hasFiniteTypeSubmoduleCapture_of_isAffineSpace hY hV)
    (fun _ _ _ _ _ hsq _ hWqs hUqc hVa hU _ _ _ =>
      hasFiniteTypeSubmoduleCapture_of_isElementaryDistinguishedSquare hsq hZ hWqs hUqc hVa
        (hU hsq.isOpenSubspace.1)) X.2

/-- **Finitely many sections of a quasi-coherent module over affine étale charts of a
quasi-compact quasi-separated algebraic space lie in a quasi-coherent submodule of finite
type.** -/
theorem exists_isFiniteType_submodule_mem_of_qcqs (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) {ι : Type u} [Finite ι] (T : ι → SmallEtale B S hS X.1)
    (hT : ∀ i, IsAffine (chartScheme (T i))) (s : ∀ i, M.val.obj (op (T i))) :
    ∃ N : M.Submodule, N.toSheafOfModules.IsQuasicoherentOnSite ∧
      N.toSheafOfModules.IsFiniteTypeOnSite ∧ ∀ i, s i ∈ N.obj (op (T i)) :=
  hasFiniteTypeSubmoduleCapture_of_qcqs hZ X hqc hqs M hM ι T hT s

set_option maxHeartbeats 800000 in
-- elaboration over the module sheaves of the small étale site, with their default abelian and
-- Grothendieck instances removed and the Grothendieck structure rebuilt in the proof
set_option synthInstance.maxHeartbeats 400000 in
-- instance search over the same module sheaves, with those instances removed
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **Stacks 0829.** On a quasi-compact quasi-separated algebraic space `X`, a quasi-coherent
`𝒪_X`-module `F` is the directed colimit of its quasi-coherent submodules of finite type: the
category `AlgebraicGeometry.Space.FiniteTypeQuasicoherentSubobject` of those submodules is
filtered and their canonical cocone with point `F` is a colimit cocone.

Directedness is `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobject_isFiltered`, which
uses Descent 03DX(2) and the cokernel clause of Stacks 03M1, that is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`. For the colimit, the
supremum of the submodules is `⊤`: its inclusion is surjective on sections over affine charts,
every section there lying in one of them by
`AlgebraicGeometry.Space.exists_isFiniteType_submodule_mem_of_qcqs`. -/
@[stacks 0829, sga "3 VIB 11.10" "more general"]
theorem isFiltered_and_nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) [hF : F.IsQuasicoherentOnSite] :
    IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 F) ∧
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2 F)) := by
  classical
  have hfil := finiteTypeQuasicoherentSubobject_isFiltered B S hS X.1 X.2 F
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X.1)
    infer_instance
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  refine ⟨hfil, ⟨isColimitSubobjectCocone_of_iSup_eq_top _ ?_⟩⟩
  set P := finiteTypeQuasicoherentSubobjectProperty B S hS X.1 X.2 F
  set Sup := ⨆ G : P.FullSubcategory, G.obj with hSup
  -- every finite type quasi-coherent submodule lies below the supremum
  have hle : ∀ N : F.Submodule, N.toSheafOfModules.IsQuasicoherentOnSite →
      N.toSheafOfModules.IsFiniteTypeOnSite → Subobject.mk N.ι ≤ Sup := fun N hNq hNf => by
    have e := Subobject.underlyingIso N.ι
    have hq : (Subobject.underlying.obj (Subobject.mk N.ι)).IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hNq
    have hf : (Subobject.underlying.obj (Subobject.mk N.ι)).IsFiniteTypeOnSite :=
      isFiniteTypeOnSite_of_epi B S hS X.1 X.2 e.inv hNf
    exact le_iSup (fun G : P.FullSubcategory => G.obj) ⟨Subobject.mk N.ι, hq,
      Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ hf⟩
  have : Epi Sup.arrow := by
    refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {W} x => ?_⟩
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X.1 W)
    rintro _ _ ⟨O', q, _, ⟨O''⟩, rfl⟩
    obtain ⟨N, hNq, hNf, hN⟩ := exists_isFiniteType_submodule_mem_of_qcqs hZ X hqc hqs F hF
      (ι := PUnit) (fun _ => openChart B S hS X.1 W O''.down.1)
      (fun _ => isAffine_chartScheme_openChart B S hS X.1 W O''.down)
      (fun _ => F.val.map (openChartInclusion B S hS X.1 W O''.down.1).op x)
    refine (Presheaf.imageSieve _ x).downward_closed ?_ q
    let u := Subobject.ofMkLE N.ι Sup (hle N hNq hNf)
    refine ⟨u.val.app _ ⟨_, hN PUnit.unit⟩, ?_⟩
    have hu : u ≫ Sup.arrow = N.ι := Subobject.ofMkLE_arrow _
    exact congrArg (fun φ : N.toSheafOfModules ⟶ F => φ.val.app _ ⟨_, hN PUnit.unit⟩) hu
  have : IsIso Sup.arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow Sup

end AlgebraicGeometry.Space

end
