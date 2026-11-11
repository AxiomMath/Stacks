module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Size.PullbackModuleSections
public import StacksFrontier.AlgebraicGeometry.Size.RelativeProjPieceBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra

/-!
# The relative Proj of the restriction to a scheme point lies in the site

In Situation 0849 let `X` be an algebraic space over `S` and `𝒜` a quasi-coherent graded
`𝒪_X`-algebra, and let `f : T ⟶ X` be a scheme point, `T` an object of the big fppf site. The
first assertion of Stacks 084B needs the relative homogeneous spectrum `Proj_T(f^*𝒜)` to be an
object of the site, so that it represents the base change `T ×_X Proj_X(𝒜)` by a scheme of the
site. This file proves that it is.

By `Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj_of_pieces_degreewise` it is
enough to bound the sections of each homogeneous piece of `f^*𝒜` over the opens of `T` by a
cardinal below the cutoff, uniformly in the open. The only bound available is the size field of
the situation, `AlgebraicGeometry.Space.RelativeProjSituation.sections_hasCardinalLT`, which
bounds the sections of each piece of `𝒜` over each étale chart of `X` separately. The passage
from one to the other is the following, for a quasi-coherent `𝒪_X`-module `ℳ`.

Choose a surjective étale chart `U ⟶ X` whose scheme is a disjoint union of affine schemes
`Uᵢ` (Stacks 03FX), and let `P = T ×_X U`, with its étale surjection `P ⟶ T`. For an open
`V ⊆ T` the sections of `f^*ℳ` over `V` inject into its sections over the preimage of `V` in
`P`, by the sheaf property for the étale covering they form. The latter are sections of the
Zariski restriction of `f^*ℳ` to `P`, which is the pullback along `P ⟶ U` of the Zariski
restriction `ℳ|_U` of `ℳ` (the chart restriction commutes with base change). Over the
components `Uᵢ` the sections of `ℳ|_U` are quotients of its global sections, the `Uᵢ` being
open and closed, and the global sections are the sections of `ℳ` over the étale chart `U` itself,
which the size field bounds: this is where one cardinal for all the opens at once comes from, the
chart `U` seeing all its components together. Finally the sections of a pullback of a
quasi-coherent module over any open of `P` are bounded in terms of the size of `P` and that one
cardinal, `AlgebraicGeometry.Scheme.Modules.mk_sections_pullback_le`, and the size of `P` is below
the cutoff because `P` is an object of the site. The cutoff being a strong limit, the resulting
power is below it.

## Main results

* `AlgebraicGeometry.Space.exists_mk_modulePullback_sections_le`: for a quasi-coherent module on
  `X` whose sections over the étale charts are below the cutoff, the sections of its pullback to a
  scheme point over the Zariski opens of the point are bounded by one cardinal below the cutoff.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_mk_sectionPieces_pointAlgebra_le`: the
  same for each homogeneous piece of the restriction `f^*𝒜` of Situation 0849.
* `AlgebraicGeometry.Space.RelativeProjSituation.contains_relativeProj_pointAlgebra`: the relative
  `Proj` of `f^*𝒜` is a scheme of the site.

## Implementation notes

The bound is uniform in the open of `T` but depends on the point `f`, through the size of
`T ×_X U`. Nothing more is needed: the containment is a statement about one scheme point at a
time.

The restriction `f^*𝒜` is `AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`, whose
sections over a Zariski open of `T` are, by
`AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra_def`, the sections of the pullback of
modules along `f` over the étale chart which that open cuts out; the bound is proved for that
pullback.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal TopologicalSpace

universe u

namespace AlgebraicGeometry

section Coproduct

variable {I : Type u} {Y : I → Scheme.{u}} {Z : Scheme.{u}} (j : ∀ i, Y i ⟶ Z)
  (e : (∐ Y) ≅ Z) (hje : ∀ i, Sigma.ι Y i ≫ e.hom = j i)

include hje in
/-- The legs of a coproduct decomposition of a scheme cover it. -/
theorem iSup_opensRange_eq_top_of_sigma_iso [∀ i, IsOpenImmersion (j i)] :
    ⨆ i, (j i).opensRange = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨z, hz⟩ := (sigmaOpenCover Y).covers (e.inv y)
  let k : I := (sigmaOpenCover Y).idx (e.inv y)
  refine Opens.mem_iSup.mpr ⟨k, show Y k from z, ?_⟩
  have hz' : (Sigma.ι Y k) (show Y k from z) = e.inv y := hz
  change (j k) (show Y k from z) = y
  rw [← hje k, Scheme.Hom.comp_apply, hz', ← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

include hje in
/-- Distinct legs of a coproduct decomposition of a scheme have disjoint images. -/
theorem disjoint_opensRange_of_sigma_iso [∀ i, IsOpenImmersion (j i)] {i k : I} (hik : i ≠ k) :
    Disjoint (j i).opensRange (j k).opensRange := by
  rw [← Opens.coe_disjoint, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange,
    Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨z', hz'⟩
  have h : (Sigma.ι Y i) z = (Sigma.ι Y k) z' := by
    have h2 := congrArg (fun x => e.inv x) hz'
    simp only [← hje, ← Scheme.Hom.comp_apply, Category.assoc, e.hom_inv_id,
      Category.comp_id] at h2
    exact h2.symm
  exact hik (congrArg Sigma.fst ((sigmaι_eq_iff Y i k z z').mp h))

include hje in
/-- The sections of a module over one leg of a coproduct decomposition of a scheme are at most its
global sections. -/
theorem mk_sections_opensRange_le_of_sigma_iso [∀ i, IsOpenImmersion (j i)] (N : Z.Modules)
    (i : I) : #Γ(N, (j i).opensRange) ≤ #Γ(N, ⊤) := by
  have hbot : (j i).opensRange ⊓ ⨆ k : {k // k ≠ i}, (j k).opensRange = ⊥ := by
    rw [inf_iSup_eq]
    exact iSup_eq_bot.2 fun k => disjoint_iff.1
      (disjoint_opensRange_of_sigma_iso j e hje (Ne.symm k.2))
  have htop : (j i).opensRange ⊔ ⨆ k : {k // k ≠ i}, (j k).opensRange = ⊤ := by
    rw [eq_top_iff, ← iSup_opensRange_eq_top_of_sigma_iso j e hje]
    refine iSup_le fun k => ?_
    rcases eq_or_ne k i with rfl | hk
    · exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun k : {k // k ≠ i} => (j k).opensRange) ⟨k, hk⟩)
  have h := Scheme.Modules.mk_sections_le_of_inf_eq_bot N hbot
  rwa [htop] at h

end Coproduct

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Isomorphic sheaves of modules have the same number of sections over any object. -/
private theorem mk_sections_eq_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (e : M ≅ N) (U : Cᵒᵖ) :
    #(M.val.obj U) = #(N.val.obj U) :=
  Cardinal.mk_congr ((SheafOfModules.evaluation _ U ⋙ forget₂ _ AddCommGrpCat).mapIso
    e).addCommGroupIsoToAddEquiv.toEquiv

/-- The sections of the Zariski restriction of an `𝒪_X`-module to the scheme of an étale chart,
over a Zariski open of that scheme, are in bijection with the sections of the module over the
étale chart which the open cuts out. -/
theorem mk_restrictToChart_sections (X : AlgebraicSpaces B S hS)
    (N : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1)
    (O : (chartScheme A).Opens) :
    #Γ(restrictToChart B S hS X.2 N A, O) =
      #(N.val.obj (op ((openChartFunctor B S hS X.1 A).obj O))) := by
  have := isContinuous_openChartFunctor B S hS X A
  rw [restrictToChart_eq_restrictToChartScheme]
  exact mk_sections_eq_of_iso (restrictToChartSchemeIsoPushforward B S hS X.2 A N) _

/-- Restricting the sections of an `𝒪_X`-module along a surjective morphism of étale charts is
injective. -/
theorem injective_val_map_of_surjective (X : AlgebraicSpaces B S hS)
    (N : Modules.{u, u} B S hS X.1 X.2) {P W : SmallEtale B S hS X.1} (c : P ⟶ W)
    (hc : Surjective ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map c))) :
    Function.Injective (N.val.map c.op) := by
  intro s t hst
  have hsep := Stacks.SheafOfModules.isSeparated_presheaf N _
    (sieve_generate_singleton_chart_mem_topology B S hS X.1 c hc)
  exact (Presieve.isSeparatedFor_iff_generate.mpr hsep).ext fun _ _ hg => by
    cases hg
    exact hst

/-- **The sections of the pullback of a quasi-coherent module to a scheme point are uniformly
bounded below the cutoff.** Let `ℳ` be a quasi-coherent `𝒪_X`-module whose sections over every
étale chart of `X` are fewer than `B.cutoff`, and `f : T ⟶ X` a scheme point. Then a single
cardinal below `B.cutoff` bounds the sections of `f^*ℳ` over the étale charts cut out by all the
Zariski opens of `T`.

The cardinal is `(max (size P) c) ^ size P`, where `P = T ×_X U` for a surjective étale chart
`U ⟶ X` which is a disjoint union of affine schemes and `c` is the cardinality of the sections of
`ℳ` over `U`; see the module documentation. -/
theorem exists_mk_modulePullback_sections_le (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hbound : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ, HasCardinalLT (M.val.obj U) B.cutoff)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    ∃ c < B.cutoff, ∀ O : ((BigFppfOver.toScheme B S hS).obj T).Opens,
      #(((modulePullback B S hS (pointHom f)).obj M).val.obj
        (op ((selfOpensFunctor B S hS T).obj O))) ≤ c := by
  obtain ⟨U, u, I, W, j, e, hsurj, het, hWaff, hje, hjimm, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X.1 X.2
  let hf := het.rep
  let P' := hf.pullback f
  let snd : P' ⟶ T := hf.snd f
  let fst' : P' ⟶ U := hf.fst' f
  have hw : yoneda.map fst' ≫ u = yoneda.map snd ≫ f := (hf.isPullback' f).w
  let V0 : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk u, het⟩
  let W0 : SmallEtale B S hS (yoneda.obj T) := ⟨CostructuredArrow.mk (yoneda.map snd),
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ snd).2 (het.property_snd f)⟩
  obtain ⟨ebc⟩ := nonempty_chartRestrictionBaseChange B S hS (pointHom f) M hM V0 W0 fst' hw
  let P0 := restrictToChart B S hS X.2 M V0
  have : P0.IsQuasicoherent := isQuasicoherent_restrictToChart_viaIdEtaleChart B S hS X M hM V0
  set c := #Γ(P0, ⊤) with hc
  have : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)) := hjimm
  let O : I → (chartScheme V0).Opens := fun i =>
    ((BigFppfOver.toScheme B S hS).map (j i)).opensRange
  have hOaff : ∀ i, IsAffineOpen (O i) := fun i => have := hWaff i; isAffineOpen_opensRange _
  have hcov : ⨆ i, O i = ⊤ :=
    iSup_opensRange_eq_top_of_sigma_iso (fun i => (BigFppfOver.toScheme B S hS).map (j i)) e hje
  have hcO : ∀ i, #Γ(P0, O i) ≤ c :=
    mk_sections_opensRange_le_of_sigma_iso (fun i => (BigFppfOver.toScheme B S hS).map (j i)) e
      hje P0
  have hclt : c < B.cutoff := by
    rw [hc, mk_restrictToChart_sections]
    exact (hasCardinalLT_iff_cardinal_mk_lt _ _).1 (hbound _)
  set Y := (BigFppfOver.toScheme B S hS).obj P'
  have hY : Y.size < B.cutoff := P'.left.property
  refine ⟨max Y.size c ^ Y.size, power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit (max_lt hY hclt) hY, fun Ω => ?_⟩
  let M' := (modulePullback B S hS (pointHom f)).obj M
  let g : W0 ⟶ idEtaleChart B S hS T :=
    ObjectProperty.homMk (CostructuredArrow.homMk snd (Category.comp_id _))
  refine le_of_eq_of_le (congrArg (fun x => #(M'.val.obj (op x)))
    (selfOpensFunctor_obj B S hS T Ω)) ?_
  calc #(M'.val.obj (op ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj Ω)))
      ≤ #(M'.val.obj (op ((openChartFunctor B S hS (yoneda.obj T) W0).obj
          (chartSchemeMap g ⁻¹ᵁ Ω)))) := Cardinal.mk_le_of_injective
          (injective_val_map_of_surjective (yonedaSpace B S hS T) M'
            (openChartRestrict B S hS (yoneda.obj T) g Ω)
            (IsZariskiLocalAtTarget.restrict (hsurj.property_snd f) Ω))
    _ = #Γ(restrictToChart B S hS (yonedaSpace B S hS T).2 M' W0, chartSchemeMap g ⁻¹ᵁ Ω) :=
        (mk_restrictToChart_sections (yonedaSpace B S hS T) M' W0 _).symm
    _ = #Γ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map fst')).obj P0,
          chartSchemeMap g ⁻¹ᵁ Ω) :=
        (mk_sections_eq_of_iso ebc _).symm
    _ ≤ max Y.size c ^ Y.size :=
        Scheme.Modules.mk_sections_pullback_le _ P0 O hOaff hcov hcO _

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-- **The homogeneous pieces of the restriction `f^*𝒜` of Situation 0849 to a scheme point have
their sections over the opens of the point bounded by one cardinal below the cutoff**, degree by
degree. This is `AlgebraicGeometry.Space.exists_mk_modulePullback_sections_le` for the pieces of
`𝒜`, whose sections over the étale charts of `X` are bounded by the size field
`AlgebraicGeometry.Space.RelativeProjSituation.sections_hasCardinalLT`. -/
theorem exists_mk_sectionPieces_pointAlgebra_le
    (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) (n : ℕ) :
    ∃ c < s.site.cutoff, ∀ V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens,
      #((s.pointAlgebra T f).sectionPieces V n) ≤ c := by
  rw [pointAlgebra_def]
  apply exists_mk_modulePullback_sections_le s.space (s.algebra.piece n) (s.isQuasicoherent n)
    (s.sections_hasCardinalLT n) T f

/-- **The relative `Proj` of the restriction of the graded algebra of Situation 0849 to a scheme
point is a scheme of the site.** For an object `T` of the big fppf site and a point
`f : T ⟶ X` of the algebraic space, `Proj_T(f^*𝒜)` lies in the site; this is the size input of
the first assertion of Stacks 084B.

The homogeneous pieces of `f^*𝒜` have their sections bounded degree by degree, uniformly over the
opens of `T`, by
`AlgebraicGeometry.Space.RelativeProjSituation.exists_mk_sectionPieces_pointAlgebra_le`, and
`Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj_of_pieces_degreewise` turns such
bounds into membership in the site. -/
theorem contains_relativeProj_pointAlgebra
    (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) :
    s.site.Contains
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (s.pointAlgebra T f)).scheme := by
  choose c hc hpiece using s.exists_mk_sectionPieces_pointAlgebra_le T f
  exact Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj_of_pieces_degreewise
    s.site (s.pointAlgebra T f) T.left.property c hc fun n V _ => hpiece n V

end RelativeProjSituation

end AlgebraicGeometry.Space

end
