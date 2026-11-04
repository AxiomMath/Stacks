module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ChartDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelExistsHom
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Being a stable model is étale local on the base

Let `c : X ⟶ x` be a morphism over the base from a family of curves `X ⟶ S` to a family
`x ⟶ S`, and let `{φᵢ : Xᵢ ⟶ X}` be morphisms of families whose base maps are étale and jointly
surjective. Suppose that each `Xᵢ` has a stable model `cᵢ : Xᵢ ⟶ Yᵢ` and that `Yᵢ` maps to `x`
over `φᵢ`, compatibly with the contractions. This file proves the conditions of a stable model
for `c` which are local on the base in the étale topology: nodality of `x`, condition (1) of
Stacks 0E8A, and, when `X` is prestable, prestability of `x`.

## Main results

* `AlgebraicGeometry.C1590Private.isAtWorstNodal_of_cover`: `x ⟶ S` is at-worst-nodal of
  relative dimension one.
* `AlgebraicGeometry.C1590Private.isUniversallyAcyclic_of_cover`: `c` satisfies condition (1) of
  Stacks 0E8A.
* `AlgebraicGeometry.C1590Private.isIso_structureSharp_of_isUniversallyAcyclic`: condition (1)
  gives `𝒪 = c'_*𝒪` after base change along any algebraic space, not only along schemes.
* `AlgebraicGeometry.C1590Private.isPrestableCurveFamily_of_cover`: if `X` is prestable, so is
  `x`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} {g : ℕ}

section Cover

variable {X x : CurveFamily B hZ} (hx : x.base = X.base) {ι : Type u}
  {Xi : ι → CurveFamily B hZ} (φ : ∀ i, Xi i ⟶ X)
  (hφ : ∀ i, Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ i).baseMap))
  (hsurj : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
    ∃ i, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ i).baseMap))
  {Yi : ι → CurveFamily B hZ} (bi : ∀ i, (Xi i).base ⟶ (Yi i).base) [∀ i, IsIso (bi i)]
  (ψ : ∀ i, Yi i ⟶ x)
  (hψb : ∀ i, bi i ≫ (ψ i).baseMap = (φ i).baseMap ≫ eqToHom hx.symm)

include hψb in
/-- The base map of `ψ i` is `(bi i)⁻¹ ≫ (φ i).baseMap`, followed by the identification of the
bases of `X` and `x`. -/
theorem baseMap_eq_of_cover (i : ι) :
    (ψ i).baseMap = inv (bi i) ≫ (φ i).baseMap ≫ eqToHom hx.symm := by
  rw [← hψb, IsIso.inv_hom_id_assoc]

include hφ hψb in
/-- The base maps of the `ψ i` are étale. -/
theorem etale_baseMap_of_cover (i : ι) :
    Etale ((BigFppfOver.toScheme B integerBase hZ).map (ψ i).baseMap) := by
  rw [baseMap_eq_of_cover hx φ bi ψ hψb i, Functor.map_comp, Functor.map_comp]
  have := hφ i
  infer_instance

omit [∀ i, IsIso (bi i)] in
include hsurj hψb in
/-- The base maps of the `ψ i` are jointly surjective. -/
theorem surjective_baseMap_of_cover (t : (BigFppfOver.toScheme B integerBase hZ).obj x.base) :
    ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (ψ i).baseMap) := by
  obtain ⟨i, s, hs⟩ := hsurj ((BigFppfOver.toScheme B integerBase hZ).map (eqToHom hx) t)
  refine ⟨i, (BigFppfOver.toScheme B integerBase hZ).map (bi i) s, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hψb, Functor.map_comp, Scheme.Hom.comp_apply,
    hs, ← Scheme.Hom.comp_apply, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  rfl

include hφ hsurj hψb in
/-- **Nodality descends along the cover.** -/
theorem isAtWorstNodal_of_cover
    (hY : ∀ i, Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ (Yi i).toBase.hom) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ x.toBase.hom :=
  holdsOnEveryEtaleChart_of_etaleCover
    AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
    (yonedaToBase x) (fun i => (Yi i).base) (fun i => (ψ i).baseMap)
    (etale_baseMap_of_cover hx φ hφ bi ψ hψb) (surjective_baseMap_of_cover hx φ hsurj bi ψ hψb)
    (fun i => (Yi i).total.obj) (fun i => yonedaToBase (Yi i)) (fun i => (ψ i).totalMap.hom)
    (fun i => AlgebraicSpaces.isPullback_hom B integerBase hZ (ψ i).cartesian) hY

end Cover

section Acyclic

/-- The maps of schemes induced by `eqToHom`s of the bases cancel. -/
private theorem schemeSpaceMap_eqToHom_comp_eqToHom {U V : BigFppfOver B integerBase hZ}
    (h : U = V) (h' : V = U) :
    schemeSpaceMap (eqToHom h) ≫ schemeSpaceMap (eqToHom h') = 𝟙 (schemeSpace U) := by
  rw [← schemeSpaceMap_comp, eqToHom_trans, eqToHom_refl]
  exact (schemeSpaceFunctor B integerBase hZ).map_id _

variable {X x : CurveFamily B hZ} (hx : x.base = X.base) {c : X.total ⟶ x.total}
  (hc : c ≫ x.toBase = X.toBase ≫ schemeSpaceMap (eqToHom hx.symm)) {ι : Type u}
  {Xi : ι → CurveFamily B hZ} (φ : ∀ i, Xi i ⟶ X)
  (hφ : ∀ i, Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ i).baseMap))
  (hsurj : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
    ∃ i, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ i).baseMap))
  {Yi : ι → CurveFamily B hZ} {bi : ∀ i, (Xi i).base ⟶ (Yi i).base}
  {ci : ∀ i, (Xi i).total ⟶ (Yi i).total} (hi : ∀ i, IsStableModel B hZ g (bi i) (ci i))
  (ψ : ∀ i, Yi i ⟶ x) (hψb : ∀ i, bi i ≫ (ψ i).baseMap = (φ i).baseMap ≫ eqToHom hx.symm)
  (hψc : ∀ i, ci i ≫ (ψ i).totalMap = (φ i).totalMap ≫ c)


include hc hi hψb hψc in
/-- The base change of `c` to a member of the covering is a base change of a local stable model. -/
theorem isAcyclic_piece {V : BigFppfOver B integerBase hZ} (v : V ⟶ x.base)
    {A' D' : AlgebraicSpaces B integerBase hZ} (a' : A' ⟶ D') (iA : A' ⟶ X.total)
    (iD : D' ⟶ x.total) (p' : D' ⟶ schemeSpace V)
    (hD : IsPullback iD p' x.toBase (schemeSpaceMap v))
    (hA : IsPullback iA (a' ≫ p') (c ≫ x.toBase) (schemeSpaceMap v))
    (hac : a' ≫ iD = iA ≫ c) (i : ι) {W : AlgebraicSpaces B integerBase hZ} (w : W ⟶ D')
    (pW : W ⟶ schemeSpace (pullback v (ψ i).baseMap))
    (hW : IsPullback w pW p' (schemeSpaceMap (pullback.fst v (ψ i).baseMap)))
    {A'' : AlgebraicSpaces B integerBase hZ} (jA : A'' ⟶ A') (a'' : A'' ⟶ W)
    (hsq : IsPullback jA a'' a' w) :
    IsIso (Space.structureSharp B integerBase hZ a'') ∧ IsZero (firstDirectImage B hZ a'') := by
  have := (hi i).isIso_base
  have hv := pullback.condition (f := v) (g := (ψ i).baseMap)
  -- the morphism to the total space of `Yᵢ`
  have hDw : (w ≫ iD) ≫ x.toBase =
      (pW ≫ schemeSpaceMap (pullback.snd v (ψ i).baseMap)) ≫ schemeSpaceMap (ψ i).baseMap := by
    rw [Category.assoc, hD.w, ← Category.assoc, hW.w, Category.assoc, Category.assoc,
      ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hv]
  let iDi := (ψ i).cartesian.lift _ _ hDw
  have hDi : IsPullback iDi pW (Yi i).toBase (schemeSpaceMap (pullback.snd v (ψ i).baseMap)) := by
    refine IsPullback.of_right ?_ ((ψ i).cartesian.lift_snd _ _ _) (ψ i).cartesian
    rw [(ψ i).cartesian.lift_fst, ← schemeSpaceMap_comp, ← hv, schemeSpaceMap_comp]
    exact hW.flip.paste_vert hD.flip |>.flip
  -- the morphism to the total space of `Xᵢ`
  have hXbase : iA ≫ X.toBase = (a' ≫ p') ≫ schemeSpaceMap (v ≫ eqToHom hx) := by
    have h₁ := hA.w
    rw [hc, ← Category.assoc] at h₁
    rw [schemeSpaceMap_comp, ← Category.assoc, ← h₁, Category.assoc,
      schemeSpaceMap_eqToHom_comp_eqToHom, Category.comp_id]
  have hφb : inv (bi i) ≫ (φ i).baseMap = (ψ i).baseMap ≫ eqToHom hx := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hψb i, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  have key : schemeSpaceMap (pullback.fst v (ψ i).baseMap) ≫ schemeSpaceMap (v ≫ eqToHom hx) =
      schemeSpaceMap (pullback.snd v (ψ i).baseMap ≫ inv (bi i)) ≫
        schemeSpaceMap (φ i).baseMap := by
    rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, Category.assoc, hφb,
      ← Category.assoc (pullback.fst v (ψ i).baseMap), hv, Category.assoc]
  have hAw : (jA ≫ iA) ≫ X.toBase = (a'' ≫ pW ≫ schemeSpaceMap
      (pullback.snd v (ψ i).baseMap ≫ inv (bi i))) ≫ schemeSpaceMap (φ i).baseMap :=
    calc (jA ≫ iA) ≫ X.toBase = jA ≫ a' ≫ p' ≫ schemeSpaceMap (v ≫ eqToHom hx) := by
          rw [Category.assoc, hXbase, Category.assoc]
      _ = a'' ≫ w ≫ p' ≫ schemeSpaceMap (v ≫ eqToHom hx) := by rw [reassoc_of% hsq.w]
      _ = a'' ≫ pW ≫ schemeSpaceMap (pullback.fst v (ψ i).baseMap) ≫
          schemeSpaceMap (v ≫ eqToHom hx) := by rw [reassoc_of% hW.w]
      _ = _ := by rw [key]; simp only [Category.assoc]
  let iAi := (φ i).cartesian.lift _ _ hAw
  have hAi : IsPullback iAi (a'' ≫ pW) (ci i ≫ (Yi i).toBase)
      (schemeSpaceMap (pullback.snd v (ψ i).baseMap)) := by
    rw [(hi i).comp_toBase]
    refine IsPullback.of_right ?_ ?_ (isPullback_totalMap_of_isIso (φ i) (ψ i) (eqToHom hx.symm)
      (bi i) (hψb i))
    · rw [(φ i).cartesian.lift_fst, ← hc, ← schemeSpaceMap_comp, ← hv, schemeSpaceMap_comp]
      exact (hsq.paste_vert hW).paste_horiz hA
    · rw [← Category.assoc, (φ i).cartesian.lift_snd, Category.assoc, Category.assoc,
        ← schemeSpaceMap_comp]
      simp
  have hci : a'' ≫ iDi = iAi ≫ ci i := by
    apply (ψ i).cartesian.hom_ext
    · calc (a'' ≫ iDi) ≫ (ψ i).totalMap = a'' ≫ w ≫ iD := by
            rw [Category.assoc, (ψ i).cartesian.lift_fst]
        _ = jA ≫ a' ≫ iD := by rw [reassoc_of% hsq.w]
        _ = (jA ≫ iA) ≫ c := by rw [hac, Category.assoc]
        _ = (iAi ≫ (φ i).totalMap) ≫ c := by rw [(φ i).cartesian.lift_fst]
        _ = (iAi ≫ ci i) ≫ (ψ i).totalMap := by rw [Category.assoc, Category.assoc, hψc]
    · calc (a'' ≫ iDi) ≫ (Yi i).toBase =
            a'' ≫ pW ≫ schemeSpaceMap (pullback.snd v (ψ i).baseMap) := by
            rw [Category.assoc, (ψ i).cartesian.lift_snd]
        _ = (a'' ≫ pW ≫ schemeSpaceMap (pullback.snd v (ψ i).baseMap ≫ inv (bi i))) ≫
            schemeSpaceMap (bi i) := by
            rw [Category.assoc, Category.assoc, ← schemeSpaceMap_comp, Category.assoc,
              IsIso.inv_hom_id, Category.comp_id]
        _ = (iAi ≫ (Xi i).toBase) ≫ schemeSpaceMap (bi i) := by rw [(φ i).cartesian.lift_snd]
        _ = (iAi ≫ ci i) ≫ (Yi i).toBase := by
            rw [Category.assoc, Category.assoc, (hi i).comp_toBase]
  exact (hi i).universallyAcyclic (pullback.snd v (ψ i).baseMap) a'' iAi iDi pW hDi hAi hci

include hc hφ hsurj hi hψb hψc in
/-- **Condition (1) of Stacks 0E8A descends along the cover.** -/
theorem isUniversallyAcyclic_of_cover :
    IsUniversallyAcyclicContraction B hZ c x.toBase := by
  have := fun i => (hi i).isIso_base
  intro V v A' D' a' iA iD p' hD hA hac
  let L := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan L :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ))
  -- the covering of `V`
  let Vi' := fun i => pullback v (ψ i).baseMap
  have hfst : ∀ i, Etale (L.map (pullback.fst v (ψ i).baseMap)) := fun i =>
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback v (ψ i).baseMap).map L).flip
      (etale_baseMap_of_cover hx φ hφ bi ψ hψb i)
  have hcovV := isEtaleCovering_yoneda_map B integerBase hZ (fun i => pullback.fst v (ψ i).baseMap)
    hfst
    (fun t => by
      obtain ⟨i, y, hy⟩ := surjective_baseMap_of_cover hx φ hsurj bi ψ hψb (L.map v t)
      obtain ⟨w, hw⟩ := Artin.ContractionSituation.exists_toScheme_map_pullback_fst_eq v
        (ψ i).baseMap (y := t) (z := y) hy.symm
      exact ⟨i, w, hw⟩)
  -- the covering of `D'`
  let W := fun i => AlgebraicSpaces.fiberProduct B integerBase hZ p'
    (schemeSpaceMap (pullback.fst v (ψ i).baseMap))
  let w : ∀ i, W i ⟶ D' := fun i => ObjectProperty.homMk (pullback.fst _ _)
  let pW : ∀ i, W i ⟶ schemeSpace (Vi' i) := fun i => ObjectProperty.homMk (pullback.snd _ _)
  have hW : ∀ i, IsPullback (w i) (pW i) p' (schemeSpaceMap (pullback.fst v (ψ i).baseMap)) :=
    fun i => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ _ _
  have hcov : Space.IsEtaleCovering B integerBase hZ (fun i => (W i).1) (fun i => (w i).hom) :=
    Space.isEtaleCovering_pullback B integerBase hZ p'.hom D'.2 _ _ hcovV
  -- the base change of `A'`
  let A'i := fun i => AlgebraicSpaces.fiberProduct B integerBase hZ a' (w i)
  let jA : ∀ i, A'i i ⟶ A' := fun i => ObjectProperty.homMk (pullback.fst _ _)
  let a'i : ∀ i, A'i i ⟶ W i := fun i => ObjectProperty.homMk (pullback.snd _ _)
  have hsq : ∀ i, IsPullback (jA i) (a'i i) a' (w i) :=
    fun i => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ _ _
  have hpiece := fun i => isAcyclic_piece hx hc φ hi ψ hψb hψc v a' iA iD p' hD hA hac i (w i)
    (pW i) (hW i) (jA i) (a'i i) (hsq i)
  exact ⟨isIso_structureSharp_of_isPullback_etale B integerBase hZ a' w jA a'i hcov hsq
      fun i => (hpiece i).1,
    isZero_firstDirectImage_of_isPullback_etale a' w jA a'i hcov hsq fun i => (hpiece i).2⟩

/-- **The structure map half of condition (1) of Stacks 0E8A after base change along an
algebraic space.** If `a : A ⟶ D` over a scheme `U` satisfies condition (1) of Stacks 0E8A, then
`𝒪_{D'} ⟶ a'_*𝒪_{A'}` is an isomorphism for the base change `a' : A' ⟶ D'` of `a` along any
morphism `Z ⟶ U` from an algebraic space. This is étale local on `D'`, and over an atlas of `Z`
it is condition (1) itself. -/
theorem isIso_structureSharp_of_isUniversallyAcyclic {A D : AlgebraicSpaces B integerBase hZ}
    {U : BigFppfOver B integerBase hZ} {a : A ⟶ D} {p : D ⟶ schemeSpace U}
    (h : IsUniversallyAcyclicContraction B hZ a p) {Z : AlgebraicSpaces B integerBase hZ}
    (gz : Z ⟶ schemeSpace U) {A' D' : AlgebraicSpaces B integerBase hZ} (a' : A' ⟶ D')
    (iA : A' ⟶ A) (iD : D' ⟶ D) (p' : D' ⟶ Z) (hD : IsPullback iD p' p gz)
    (hA : IsPullback iA (a' ≫ p') (a ≫ p) gz) (hac : a' ≫ iD = iA ≫ a) :
    IsIso (Space.structureSharp B integerBase hZ a') := by
  obtain ⟨T, q, hsurj, het⟩ := Z.property.exists_atlas
  let qZ : schemeSpace T ⟶ Z := ObjectProperty.homMk q
  let v : T ⟶ U := Yoneda.fullyFaithful.preimage (q ≫ gz.hom)
  have hv : schemeSpaceMap v = qZ ≫ gz :=
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)
  let W := AlgebraicSpaces.fiberProduct B integerBase hZ p' qZ
  let w : W ⟶ D' := ObjectProperty.homMk (pullback.fst _ _)
  let pW : W ⟶ schemeSpace T := ObjectProperty.homMk (pullback.snd _ _)
  have hW : IsPullback w pW p' qZ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ _ _
  have hcov : Space.IsEtaleCovering B integerBase hZ (fun _ : PUnit.{u + 1} => W.1)
      (fun _ => w.hom) :=
    Space.isEtaleCovering_pullback B integerBase hZ p'.hom D'.2 _ _
      (Space.isEtaleCovering_atlas B integerBase hZ Z.2 hsurj het)
  let A'' := AlgebraicSpaces.fiberProduct B integerBase hZ a' w
  let jA : A'' ⟶ A' := ObjectProperty.homMk (pullback.fst _ _)
  let a'' : A'' ⟶ W := ObjectProperty.homMk (pullback.snd _ _)
  have hsq : IsPullback jA a'' a' w := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ _ _
  have hD' : IsPullback (w ≫ iD) pW p (schemeSpaceMap v) := by
    rw [hv]
    exact hW.paste_horiz hD
  have hA' : IsPullback (jA ≫ iA) (a'' ≫ pW) (a ≫ p) (schemeSpaceMap v) := by
    rw [hv]
    exact (hsq.paste_vert hW).paste_horiz hA
  have hac' : a'' ≫ w ≫ iD = (jA ≫ iA) ≫ a := by
    rw [← Category.assoc, ← hsq.w, Category.assoc, hac, Category.assoc]
  have h'' := h v a'' (jA ≫ iA) (w ≫ iD) pW hD' hA' hac'
  exact isIso_structureSharp_of_isPullback_etale B integerBase hZ a' (fun _ : PUnit.{u + 1} => w)
    (fun _ => jA) (fun _ => a'') hcov (fun _ => hsq) fun _ => h''.1

include hc hφ hsurj hi hψb hψc in
/-- **`f_*𝒪 = 𝒪` universally descends along the cover.** If `X` has universally bijective global
functions, then so has `x`: over every algebraic space `Z ⟶ S`, the base change of `c` induces an
isomorphism on structure sheaves by condition (1), hence a bijection on global functions. -/
theorem hasUniversallyBijectiveGlobalFunctions_of_cover
    (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    HasUniversallyBijectiveGlobalFunctions B hZ x := by
  intro Z gz
  have hU := isUniversallyAcyclic_of_cover hx hc φ hφ hsurj hi ψ hψb hψc
  let e : schemeSpace X.base ⟶ schemeSpace x.base := schemeSpaceMap (eqToHom hx.symm)
  let g' : Z ⟶ schemeSpace X.base := gz ≫ schemeSpaceMap (eqToHom hx)
  have hg' : g' ≫ e = gz := by
    simp only [g', e, Category.assoc, schemeSpaceMap_eqToHom_comp_eqToHom, Category.comp_id]
  have hxZ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ x.toBase gz
  have hXZ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase g'
  have hXZ' : IsPullback (ObjectProperty.homMk (pullback.fst X.toBase.hom g'.hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g' ⟶ X.total)
      (ObjectProperty.homMk (pullback.snd X.toBase.hom g'.hom)) (c ≫ x.toBase) gz := by
    have : IsIso e :=
      inferInstanceAs (IsIso ((schemeSpaceFunctor B integerBase hZ).map (eqToHom hx.symm)))
    have t : IsPullback (𝟙 X.total) X.toBase (X.toBase ≫ e) e :=
      IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩
    have h₁ := hXZ.paste_horiz t
    rw [Category.comp_id, hg'] at h₁
    rw [hc]
    exact h₁
  let cZ := hxZ.lift (ObjectProperty.homMk (pullback.fst X.toBase.hom g'.hom) ≫ c)
    (ObjectProperty.homMk (pullback.snd X.toBase.hom g'.hom)) (by rw [Category.assoc]; exact hXZ'.w)
  have hcZ : IsIso (Space.structureSharp B integerBase hZ cZ) :=
    isIso_structureSharp_of_isUniversallyAcyclic hU gz cZ _ _ _ hxZ
      (by rw [hxZ.lift_snd]; exact hXZ') (hxZ.lift_fst _ _ _)
  rw [← Space.forgetCommRingSheaf_map_fSharp] at hcZ
  have : IsIso (Space.smallEtaleRingedToposHom B integerBase hZ cZ).fSharp :=
    @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      (Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf.{u}
        (Space.SmallEtale.topology B integerBase hZ
          (AlgebraicSpaces.fiberProduct B integerBase hZ x.toBase gz).1)) _ _ _ hcZ
  have hb := Space.bijective_globalFunctionsMap_of_isIso_fSharp cZ
  have hbX := hX Z g'
  have hcomp : (ObjectProperty.homMk (pullback.snd X.toBase.hom g'.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g' ⟶ Z) =
      cZ ≫ ObjectProperty.homMk (pullback.snd x.toBase.hom gz.hom) :=
    (hxZ.lift_snd _ _ _).symm
  rw [hcomp, Space.globalFunctionsMap_comp, RingHom.coe_comp] at hbX
  exact (Function.Bijective.of_comp_iff' hb _).1 hbX

include hc hφ hsurj hi hψb hψc in
/-- **Prestability descends along the cover.** -/
theorem isPrestableCurveFamily_of_cover (hX : IsPrestableCurveFamily B hZ X) :
    IsPrestableCurveFamily B hZ x :=
  have := fun i => (hi i).isIso_base
  ⟨isAtWorstNodal_of_cover hx φ hφ hsurj bi ψ hψb fun i => (hi i).isStable.1.1,
    hasUniversallyBijectiveGlobalFunctions_of_cover hx hc φ hφ hsurj hi ψ hψb hψc hX.2⟩

end Acyclic

end AlgebraicGeometry.C1590Private

end
