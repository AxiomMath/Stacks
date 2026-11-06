module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionNeighbourhood
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSubfunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative

/-!
# Infinitesimal neighbourhoods of the reduction: charts and colimit

Let `i : Z ⟶ X` be a representable thickening of fppf sheaves over `S` and let `X_n ⊂ X` be its
`n`th infinitesimal neighbourhood (`AlgebraicGeometry.FormalSpace.neighbourhood`). This file
proves the three facts of the proof of Stacks 0GHM which are local on `X`.

* *Base change.* If a cartesian square exhibits `r : R ⟶ Y` as the base change of `i` along
  `f : Y ⟶ X`, then the neighbourhoods of `R` in `Y` are the base changes of the neighbourhoods of
  `Z` in `X` (`AlgebraicGeometry.FormalSpace.pullbackIdeal_app_of_isPullback`). For reductions
  and `f` étale such a square exists
  (`AlgebraicGeometry.FormalSpace.exists_isPullback_of_isReduction_of_etale`): the reduction
  of an étale chart is the base change of the reduction.
* *The affine case.* If `Y` is the colimit of a chain `E_0 ⟶ E_1 ⟶ ⋯` of objects of the site
  along closed immersions, with `E_n` cut out of `E_m` by the `(n + 1)`st power of the ideal of
  `E_0`, then the `n`th neighbourhood of `E_0` in `Y` is `E_n`
  (`AlgebraicGeometry.FormalSpace.neighbourhood_eq_range_of_chain`). This is the computation
  `X_n = Spec (A ⧸ 𝔞 ^ n)` of the source for `X = Spf A`.
* *The colimit.* If every section of `X` lies, locally, in some `X_n`, then `X` is the colimit
  of the `X_n` (`AlgebraicGeometry.FormalSpace.isIso_colimitDesc_neighbourhoodCocone`).

## Implementation notes

The colimit statement is proved by local bijectivity of the comparison morphism from the
colimit: local surjectivity is the hypothesis, and injectivity is checked on the affine objects
of the site, over which a section of a filtered colimit of sheaves along monomorphisms comes
from a stage (`AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit`).
The affine objects over an object of the site generate a covering sieve
(`AlgebraicGeometry.FormalSpace.mem_topology_of_forall_isAffine`).

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] sheaf_hasColimits

/-- An arrow lies in a supremum of sieves exactly when it lies in one of them. -/
theorem sieve_arrows_iSup_iff {ι : Type*} {C : Type*} [Category C] {X : C} (R : ι → Sieve X)
    {Y : C} (f : Y ⟶ X) : (⨆ j, R j) f ↔ ∃ j, R j f := by
  rw [iSup, Sieve.sSup_apply]
  exact ⟨fun ⟨_, ⟨j, rfl⟩, h⟩ ↦ ⟨j, h⟩, fun ⟨j, h⟩ ↦ ⟨_, ⟨j, rfl⟩, h⟩⟩

/-! ### Affine objects generate a covering sieve -/

/-- A sieve on an object of the big fppf site containing every morphism out of an affine object
is a covering sieve: it contains the covering by the affine opens. -/
theorem mem_topology_of_forall_isAffine {T : BigFppfOver B S hS} (R : Sieve T)
    (hR : ∀ ⦃U : BigFppfOver B S hS⦄ (g : U ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) → R g) :
    R ∈ BigFppfOver.topology B S hS T := by
  classical
  choose V a ha harange hV using fun U => BigFppfOver.exists_affineOpen_restrict B S hS T U
  have hcover := CartesianColimit.openCover_mem_topology B S hS V a ha (by
    intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) := trivial
    rw [← AlgebraicGeometry.iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨U, by rwa [harange U]⟩)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hcover
  rintro Z g ⟨W, b, c, ⟨U⟩, rfl⟩
  exact R.downward_closed (hR (a U) (hV U)) b

/-! ### Sections of a filtered colimit over an affine object -/

/-- A section over an affine object of the site of a filtered colimit of fppf sheaves along
monomorphisms comes from a stage. -/
theorem exists_colimitι_app_eq_of_isAffine {I : Type} [Category.{0} I] [IsFiltered I]
    (F : I ⥤ FppfSheaf B S hS) (hmono : ∀ i j (f : i ⟶ j), Mono (F.map f))
    {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (s : (colimit F).obj.obj (op U)) :
    ∃ (n : I) (y : (F.obj n).obj.obj (op U)), (colimit.ι F n).hom.app (op U) y = s := by
  let JT := BigFppfOver.topology B S hS
  obtain ⟨n, g, hg⟩ := compact_map_factors_through_filtered_colimit F hmono U
    (isQuasiCompactObject_over_of_compact_scheme B S hS U) ((Sheaf.sectionEquiv JT).symm s)
  refine ⟨n, Sheaf.sectionEquiv JT g, ?_⟩
  rw [← Sheaf.sectionEquiv_comp, hg, Equiv.apply_symm_apply]

/-! ### The colimit of the neighbourhoods -/

section Colimit

variable {X Z : FppfSheaf B S hS} {i : Z ⟶ X}
  (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)

/-- The transition maps `X_n ⟶ X_m` of the diagram of infinitesimal neighbourhoods are
monomorphisms. -/
theorem mono_neighbourhoodDiagram_map {n m : ℕ} (f : n ⟶ m) :
    Mono ((neighbourhoodDiagram hi).map f) :=
  (sheafToPresheaf _ _).mono_of_mono_map
    (inferInstanceAs (Mono (Subfunctor.homOfLe (neighbourhood_mono hi (leOfHom f)))))

/-- **`X` is the colimit of its infinitesimal neighbourhoods** as soon as every section of `X`
lies, locally, in one of them. -/
theorem isIso_colimitDesc_neighbourhoodCocone
    (hloc : ∀ (T : BigFppfOver B S hS) (ξ : X.obj.obj (op T)),
      (⨆ n, (neighbourhood hi n).sieveOfSection ξ) ∈ BigFppfOver.topology B S hS T) :
    IsIso (colimit.desc (neighbourhoodDiagram hi) (neighbourhoodCocone hi)) := by
  let JT := BigFppfOver.topology B S hS
  let E := neighbourhoodDiagram hi
  let d := colimit.desc E (neighbourhoodCocone hi)
  have hdapp : ∀ n (T : (BigFppfOver B S hS)ᵒᵖ) (y : (E.obj n).obj.obj T),
      d.hom.app T ((colimit.ι E n).hom.app T y) = y.1 := fun n T y ↦
    ConcreteCategory.congr_hom
      (congr_app (congrArg (fun t ↦ t.hom) (colimit.ι_desc (neighbourhoodCocone hi) n)) T) y
  -- local surjectivity
  have hsurj : Sheaf.IsLocallySurjective d := by
    constructor
    intro T ξ
    refine JT.superset_covering ?_ (hloc T ξ)
    intro V g hg
    obtain ⟨n, hn⟩ := (sieve_arrows_iSup_iff _ g).mp hg
    exact ⟨(colimit.ι E n).hom.app (op V) ⟨X.obj.map g.op ξ, hn⟩, hdapp n (op V) _⟩
  -- injectivity
  have hinj : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Function.Injective (d.hom.app T) := by
    intro T s t hst
    have hsep := ((isSheaf_iff_isSheaf_of_type JT (colimit E).obj).1 (colimit E).property)
    have haff : ∀ ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ T.unop),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
          (colimit E).obj.map g.op s = (colimit E).obj.map g.op t := by
      intro V g hV
      obtain ⟨n, y, hy⟩ := exists_colimitι_app_eq_of_isAffine E
        (fun _ _ f ↦ mono_neighbourhoodDiagram_map hi f) hV ((colimit E).obj.map g.op s)
      obtain ⟨m, y', hy'⟩ := exists_colimitι_app_eq_of_isAffine E
        (fun _ _ f ↦ mono_neighbourhoodDiagram_map hi f) hV ((colimit E).obj.map g.op t)
      have hlift : ∀ (k : ℕ) (h : k ≤ max n m) (z : (E.obj k).obj.obj (op V)),
          (colimit.ι E k).hom.app (op V) z =
            (colimit.ι E (max n m)).hom.app (op V) ((E.map (homOfLE h)).hom.app (op V) z) :=
        fun k h z ↦ (ConcreteCategory.congr_hom (congr_app (congrArg (fun t ↦ t.hom)
          (colimit.w E (homOfLE h))) (op V)) z).symm
      rw [← hy, ← hy', hlift n (le_max_left n m), hlift m (le_max_right n m)]
      congr 1
      apply Subtype.ext
      rw [← hdapp, ← hdapp, ← hlift, ← hlift, hy, hy', NatTrans.naturality_apply,
        NatTrans.naturality_apply, hst]
    refine (hsep.isSeparated _ (mem_topology_of_forall_isAffine (T := T.unop)
      (Sieve.generate fun V _ ↦ IsAffine ((BigFppfOver.toScheme B S hS).obj V))
      (fun V g hV ↦ ⟨V, 𝟙 V, g, hV, Category.id_comp g⟩))).ext ?_
    rintro V g ⟨W, h, g', hg', rfl⟩
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, haff g' hg']
  have : Epi d := (Sheaf.isLocallySurjective_iff_epi d).mp hsurj
  have : ∀ T, Mono (d.hom.app T) := fun T ↦ (mono_iff_injective _).2 (hinj T)
  have : Mono d := (sheafToPresheaf JT (Type (u + 1))).mono_of_mono_map
    (NatTrans.mono_of_mono_app d.hom)
  exact isIso_of_mono_of_epi d

end Colimit

/-! ### The neighbourhoods along a cartesian square -/

section BaseChange

variable {X Y : FppfSheaf B S hS} {Z R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
  {i : Z ⟶ X.obj} {r : R ⟶ Y.obj}
  (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i)
  (hr : Space.IsRepresentableThickeningULift.{u + 1} B S hS r)

/-- **The ideal sheaf of a thickening is compatible with base change.** If `R = Z ×_X Y`
along `f : Y ⟶ X`, then for a section `y` of `Y` the ideal sheaf cut out by `r` along `y` is the
ideal sheaf cut out by `i` along `f ∘ y`. -/
theorem pullbackIdeal_app_of_isPullback {f : Y ⟶ X} {k : R ⟶ Z}
    (Q : IsPullback k r i f.hom) {T : BigFppfOver B S hS} (y : Y.obj.obj (op T)) :
    pullbackIdeal hi (f.hom.app (op T) y) = pullbackIdeal hr y := by
  have sq := (hr.rep.isPullback (uliftYonedaEquiv.{u + 1}.symm y)).paste_horiz Q
  have e : uliftYonedaEquiv.{u + 1}.symm y ≫ f.hom =
      uliftYonedaEquiv.{u + 1}.symm (f.hom.app (op T) y) := uliftYonedaEquiv_symm_comp y f.hom
  have sq' : IsPullback (hr.rep.fst (uliftYonedaEquiv.{u + 1}.symm y) ≫ k)
      (uliftYoneda.{u + 1}.map (hr.rep.snd (uliftYonedaEquiv.{u + 1}.symm y))) i
      (uliftYonedaEquiv.{u + 1}.symm (f.hom.app (op T) y)) := e ▸ sq
  exact (ker_eq_pullbackIdeal hi _ sq').symm

/-- If `R = Z ×_X Y` along `f : Y ⟶ X`, then a section `y` of `Y` lies in the `n`th infinitesimal
neighbourhood of `R` in `Y` exactly when `f ∘ y` lies in the `n`th infinitesimal neighbourhood of
`Z` in `X`. -/
theorem app_mem_neighbourhood_iff_of_isPullback {f : Y ⟶ X} {k : R ⟶ Z}
    (Q : IsPullback k r i f.hom) {n : ℕ} {T : BigFppfOver B S hS}
    (y : Y.obj.obj (op T)) :
    f.hom.app (op T) y ∈ (neighbourhood hi n).obj (op T) ↔
      y ∈ (neighbourhood hr n).obj (op T) := by
  rw [mem_neighbourhood_iff, mem_neighbourhood_iff, pullbackIdeal_app_of_isPullback hi hr Q]

end BaseChange

/-- **The reduction of an étale chart is the base change of the reduction.** If `i : Z ⟶ X` and
`r : R ⟶ Y` are reductions and `f : Y ⟶ X` is representable by algebraic spaces and étale, then
there is a cartesian square exhibiting `r` as the base change of `i` along `f`. -/
theorem exists_isPullback_of_isReduction_of_etale {X Z Y R : FppfSheaf B S hS} {i : Z ⟶ X}
    {r : R ⟶ Y} (hred : IsReduction B S hS X Z i) (hrY : IsReduction B S hS Y R r)
    (f : Y ⟶ X) (hf : IsRepresentableEtale B S hS f) :
    ∃ k : R ⟶ Z, IsPullback k r i f := by
  obtain ⟨hfr, hfe⟩ := hf
  obtain ⟨k, hk, -⟩ := hred.universal R hrY.algebraic hrY.reduced (r ≫ f)
  have hmi : Mono i.hom := mono_of_isRepresentableThickeningULift B S hS
    hred.isRepresentableThickening
  have : Mono r.hom := mono_of_isRepresentableThickeningULift B S hS
    hrY.isRepresentableThickening
  refine ⟨k, isPullback_of_mono_of_local_lift B S hS k r i f hk inferInstance
    fun T x y hxy ↦ ?_⟩
  refine ⟨⊤, (BigFppfOver.topology B S hS).top_mem T, fun T' h _ ↦ ?_⟩
  obtain ⟨z, hz⟩ := exists_app_eq_of_isReduction_of_etale B S hS hred.algebraic hred.reduced
    i f hfr hfe hrY (Z.obj.map h.op x) (Y.obj.map h.op y)
    (by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy])
  refine ⟨z, ?_, hz⟩
  refine (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app i.hom).1 hmi (op T')) ?_
  show (k ≫ i).hom.app (op T') z = _
  rw [hk]
  show f.hom.app (op T') (r.hom.app (op T') z) = _
  rw [hz, NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-! ### The neighbourhoods of the first stage of a chain -/

section Chain

variable {Y : FppfSheaf B S hS} (E : ℕ ⥤ BigFppfOver B S hS)
  (ρ : ∀ n, uliftYoneda.{u + 1}.obj (E.obj n) ⟶ Y.obj)
  (hρ : ∀ n, Space.IsRepresentableThickeningULift.{u + 1} B S hS (ρ n))
  (hw : ∀ (n m : ℕ) (h : n ≤ m), uliftYoneda.{u + 1}.map (E.map (homOfLE h)) ≫ ρ m = ρ n)
  (hci : ∀ (n m : ℕ) (h : n ≤ m),
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE h))))
  (hker : ∀ (n m : ℕ) (h : n ≤ m),
    ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE (Nat.zero_le m)))).ker ^ (n + 1) =
      ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE h))).ker)
  (hloc : ∀ (T : BigFppfOver B S hS) (y : Y.obj.obj (op T)),
    (⨆ m, (Subfunctor.range (ρ m)).sieveOfSection y) ∈ BigFppfOver.topology B S hS T)

/-- A morphism of the site into the target of a closed immersion of the site whose kernel contains
the kernel of the closed immersion factors through it. -/
theorem exists_comp_eq_of_ker_le {U V W : BigFppfOver B S hS} (c : V ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c)] (g : U ⟶ W)
    (hg : ((BigFppfOver.toScheme B S hS).map c).ker ≤ ((BigFppfOver.toScheme B S hS).map g).ker) :
    ∃ h : U ⟶ V, h ≫ c = g := by
  let l : U.left ⟶ V.left := B.inclusion.preimage (X := U.left) (Y := V.left)
    (AlgebraicGeometry.IsClosedImmersion.lift ((BigFppfOver.toScheme B S hS).map c)
      ((BigFppfOver.toScheme B S hS).map g) hg)
  have hl : l ≫ c.left = g.left := by
    apply B.inclusion.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]
    exact AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  exact ⟨Over.homMk l (by rw [← Over.w c, ← Category.assoc, hl, Over.w g]),
    Over.OverMorphism.ext hl⟩

include hw in
/-- The ideal sheaf cut out on `E_m` by the first stage, along the `m`th stage, is the kernel of
`E_0 ⟶ E_m`. -/
theorem pullbackIdeal_ρ (m : ℕ) :
    pullbackIdeal (hρ 0) (uliftYonedaEquiv.{u + 1} (ρ m)) =
      ((BigFppfOver.toScheme B S hS).map (E.map (homOfLE (Nat.zero_le m)))).ker := by
  have : Mono (ρ m) := mono_of_isRepresentableThickeningULift B S hS (hρ m)
  have sq := isPullback_comp_mono_of_eq
    (IsPullback.of_id_fst (f := uliftYoneda.{u + 1}.map (E.map (homOfLE (Nat.zero_le m)))))
    (ρ m) (hw 0 m (Nat.zero_le m))
  rw [Category.id_comp, ← Equiv.symm_apply_apply uliftYonedaEquiv.{u + 1} (ρ m)] at sq
  exact (ker_eq_pullbackIdeal (hρ 0) _ sq).symm

include hw hci hker hloc in
/-- **The `n`th neighbourhood of the first stage of a chain is the `n`th stage.** Let `Y` carry
stages `ρ_n : E_n ⟶ Y` along a chain of closed immersions `E_0 ⟶ E_1 ⟶ ⋯`, in which `E_n` is
cut out of `E_m` by the `(n + 1)`st power of the ideal of `E_0`, and whose stages cover `Y`
locally. Then the `n`th infinitesimal neighbourhood of `ρ_0` is the image of `ρ_n`. -/
theorem neighbourhood_eq_range_of_chain (n : ℕ) :
    neighbourhood (hρ 0) n = Subfunctor.range (ρ n) := by
  let JT := BigFppfOver.topology B S hS
  let G := BigFppfOver.toScheme B S hS
  have hρapp : ∀ (m : ℕ) {T : BigFppfOver B S hS} (t : T ⟶ E.obj m),
      (ρ m).app (op T) (ULift.up t) =
        Y.obj.map t.op (uliftYonedaEquiv.{u + 1} (ρ m)) := by
    intro m T t
    rw [uliftYonedaEquiv_naturality, Quiver.Hom.unop_op, uliftYonedaEquiv_comp]
    rfl
  have hmem : ∀ (m : ℕ) {T : BigFppfOver B S hS} (t : T ⟶ E.obj m),
      Y.obj.map t.op (uliftYonedaEquiv.{u + 1} (ρ m)) ∈ (neighbourhood (hρ 0) n).obj (op T)
        ↔ ((G.map (E.map (homOfLE (Nat.zero_le m)))).ker ^ (n + 1) ≤ (G.map t).ker) := by
    intro m T t
    rw [map_mem_neighbourhood_iff, pullbackIdeal_ρ E ρ hρ hw m]
  ext T y
  induction T using Opposite.rec with | _ T =>
  constructor
  · intro hy
    have : Mono (ρ n) := mono_of_isRepresentableThickeningULift B S hS (hρ n)
    have hY : Presieve.IsSheaf JT Y.obj := (isSheaf_iff_isSheaf_of_type JT Y.obj).1 Y.property
    have hRange : Presieve.IsSheaf JT (Subfunctor.range (ρ n)).toFunctor :=
      Presieve.isSheaf_iso JT (asIso (Subfunctor.toRange (ρ n)))
        ((isSheaf_iff_isSheaf_of_type JT _).1
          (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (E.obj n)).isSheaf)
    refine ((Subfunctor.range (ρ n)).isSheaf_iff hY).1 hRange (op T) y
      (JT.superset_covering ?_ (hloc T y))
    intro V g hg
    obtain ⟨m, x, hx⟩ := (sieve_arrows_iSup_iff _ g).mp hg
    have h1 : m ≤ max n m := le_max_right n m
    have h2 : n ≤ max n m := le_max_left n m
    let t : V ⟶ E.obj (max n m) := x.down ≫ E.map (homOfLE h1)
    have hxt : (ρ m).app (op V) x = (ρ (max n m)).app (op V) (ULift.up t) := by
      rw [← hw m (max n m) h1]
      rfl
    have hyg : Y.obj.map g.op y = Y.obj.map t.op (uliftYonedaEquiv.{u + 1} (ρ (max n m))) := by
      rw [← hρapp, ← hxt]
      exact hx.symm
    have hres : Y.obj.map g.op y ∈ (neighbourhood (hρ 0) n).obj (op V) :=
      (neighbourhood (hρ 0) n).map g.op hy
    rw [hyg, hmem, hker n (max n m) h2] at hres
    have := hci n (max n m) h2
    obtain ⟨h', hh'⟩ := exists_comp_eq_of_ker_le (E.map (homOfLE h2)) t hres
    refine ⟨ULift.up h', ?_⟩
    show (ρ n).app (op V) (ULift.up h') = Y.obj.map g.op y
    rw [hyg, ← hρapp, ← hh', ← hw n (max n m) h2]
    rfl
  · rintro ⟨⟨t⟩, rfl⟩
    rw [hρapp, hmem, hker n n le_rfl,
      show (homOfLE (le_refl n) : n ⟶ n) = 𝟙 n from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Scheme.Hom.ker_eq_bot_of_isIso]
    exact bot_le

end Chain

end AlgebraicGeometry.FormalSpace

end
