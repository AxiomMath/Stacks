module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RingSheafChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSizeBound

/-!
# Chart thickenings of a square-zero extension whose ideal is pulled back along a chart diagram

Let `E` be a square-zero extension `0 → ℐ → 𝒜 → 𝒪_X → 0` on the small étale site of an algebraic
space `X` (the data of Stacks 05ZT), and suppose that `ℐ ≅ g^*𝒥` for a morphism `g : X ⟶ T` of
algebraic spaces and a quasi-coherent `𝒪_T`-module `𝒥`. If an étale chart `U` of `X` maps to an
étale chart `W` of `T` over `g`, and the sections of `𝒥` over the affine opens of `W` are bounded
by a cardinal below the cutoff of the big fppf site, then the site contains the chart thickening
`U'` of `E` (the scheme `(U, 𝒜|_U)`).

The argument is the size bookkeeping implicit in the proof of Stacks 05ZT. An affine open `V` of
`U` is covered by finitely many affine opens `Vᵢ`, each mapping into an affine open `Oᵢ` of `W`.
Over `Vᵢ` the sections of `g^*𝒥` are `𝒪(Vᵢ) ⊗_{𝒪(Oᵢ)} 𝒥(Oᵢ)` (the chart form of Stacks 083K),
so they are bounded; the sections over `V` inject into the finite product of those over the
`Vᵢ` (the sheaf property for the Zariski covering), and `#𝒜(V) ≤ #𝒪_X(V) · #ℐ(V)`.

## Main results

* `AlgebraicGeometry.Space.mk_sections_chartOpens_le_of_iSup_eq`: the sections of a sheaf over
  an open of a chart covered by finitely many opens with bounded sections are bounded.
* `AlgebraicGeometry.Space.exists_finite_affineOpens_cover_le_preimage`: an affine open of a
  scheme is a finite union of affine opens each mapping into an affine open of the target.
* `AlgebraicGeometry.Space.mk_modulePullback_le_of_chartDiagram`: the sections of `g^*𝒥` over an
  affine chart lying over an affine chart are bounded.
* `SquareZeroExtension.contains_chartThickening_of_iso_modulePullback_of_chartDiagram`:
  the site contains the chart thickening.
* `SquareZeroExtension.nonempty_realization_of_iso_modulePullback_definingIdealSheaf`:
  Stacks 05ZT on the given site, when the ideal is pulled back from the ideal sheaf of a closed
  subspace of the target.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Cardinal TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Sections over a finitely covered open of a chart are bounded.** For an `𝒪_X`-module `M`
on the small étale site of an algebraic space `X`, an étale chart `U` and an open `V` of `U`
covered by finitely many opens `Wᵢ ⊆ V`, if every `M(Wᵢ)` has at most `κ ≥ ℵ₀` elements, then so
does `M(V)`: restriction embeds it in the finite product of the `M(Wᵢ)`, by the sheaf property
for the Zariski covering. -/
theorem mk_sections_chartOpens_le_of_iSup_eq {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (U : SmallEtale B S hS X.1)
    {ι : Type u} [Finite ι] (W : ι → (chartScheme U).Opens) (V : (chartScheme U).Opens)
    (hW : V ≤ ⨆ i, W i) (hWV : ∀ i, W i ≤ V) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (h : ∀ i, #(M.val.obj (op ((chartOpens B S hS U).obj (W i)))) ≤ κ) :
    #(M.val.obj (op ((chartOpens B S hS U).obj V))) ≤ κ := by
  have := isContinuous_chartOpens B S hS X.1 X.2 U
  let G : TopCat.Sheaf AddCommGrpCat.{u} (chartScheme U) :=
    ((chartOpens B S hS U).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS X.1)).obj
      ((SheafOfModules.toSheaf _).obj M)
  let res : M.val.obj (op ((chartOpens B S hS U).obj V)) →
      ∀ i, M.val.obj (op ((chartOpens B S hS U).obj (W i))) :=
    fun s i => G.1.map (homOfLE (hWV i)).op s
  refine (Cardinal.mk_le_of_injective (f := res) fun s t hst =>
    G.eq_of_locally_eq' W V (fun i => homOfLE (hWV i)) hW s t fun i => congrFun hst i).trans ?_
  rw [Cardinal.mk_pi]
  refine (Cardinal.prod_le_prod _ _ h).trans ?_
  have : Fintype ι := Fintype.ofFinite ι
  rw [Cardinal.prod_const, Cardinal.lift_id, Cardinal.mk_fintype, Cardinal.lift_natCast]
  exact Cardinal.power_nat_le hκ

/-- **An affine open is a finite union of affine opens mapping into affine opens.** For a
morphism of schemes `φ : U ⟶ W` and an affine open `V` of `U`, there are finitely many affine
opens `Vᵢ ⊆ V` covering `V`, each contained in the preimage of an affine open `Oᵢ` of `W`. -/
theorem exists_finite_affineOpens_cover_le_preimage {U W : Scheme.{u}} (φ : U ⟶ W)
    (V : U.affineOpens) :
    ∃ (ι : Type u) (_ : Finite ι) (Vs : ι → U.affineOpens) (Os : ι → W.affineOpens),
      V.1 ≤ ⨆ i, (Vs i).1 ∧ (∀ i, (Vs i).1 ≤ V.1) ∧ ∀ i, (Vs i).1 ≤ φ ⁻¹ᵁ (Os i).1 := by
  let b : {p : U.affineOpens × W.affineOpens // p.1.1 ≤ φ ⁻¹ᵁ p.2.1} → Set U :=
    fun p => (p.1.1.1 : Set U)
  have hb : IsTopologicalBasis (Set.range b) := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨p, rfl⟩
      exact p.1.1.1.isOpen
    · intro x G hx hG
      obtain ⟨_, ⟨O, hO, rfl⟩, hxO, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (φ.base x)) isOpen_univ
      obtain ⟨_, ⟨V', hV'a, rfl⟩, hxV', hV'⟩ := U.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ G ∩ (φ ⁻¹ᵁ O : Set U) from ⟨hx, hxO⟩)
        (hG.inter (φ ⁻¹ᵁ O).isOpen)
      exact ⟨_, ⟨⟨(⟨V', hV'a⟩, ⟨O, hO⟩), fun y hy => (hV' hy).2⟩, rfl⟩, hxV',
        fun y hy => (hV' hy).1⟩
  obtain ⟨s, hs, hVs⟩ := (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b hb
    (fun p => p.1.1.2.isCompact) (V.1 : Set U)).1 ⟨V.2.isCompact, V.1.isOpen⟩
  have : Finite s := hs
  refine ⟨ULift.{u} s, inferInstance, fun i => i.down.1.1.1, fun i => i.down.1.1.2, ?_, ?_,
    fun i => i.down.1.2⟩
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (hVs ▸ hx : x ∈ ⋃ i ∈ s, b i)
    exact Opens.mem_iSup.2 ⟨⟨⟨p, hp⟩⟩, hxp⟩
  · exact fun i x hx => (hVs ▸ Set.mem_iUnion₂.2 ⟨i.down.1, i.down.2, hx⟩ :)

/-- The scheme morphism of a chart diagram. -/
abbrev ChartDiagram.schemeMap {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) : chartScheme d.U ⟶ chartScheme d.V :=
  (BigFppfOver.toScheme B S hS).map d.g

/-- A chart diagram `g : U ⟶ W` restricted to a Zariski open `O` of `W` and a Zariski open `V` of
`U` contained in `g⁻¹O`. -/
def ChartDiagram.restrictChartOpensLE {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (O : (chartScheme d.V).Opens)
    (V : (chartScheme d.U).Opens) (h : V ≤ d.schemeMap ⁻¹ᵁ O) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (chartOpens B S hS d.U).obj V
  V := (chartOpens B S hS d.V).obj O
  g := chartOpenOverMap B S hS d.U (homOfLE h) ≫ chartOpenOverRestrict B S hS d.U d.V d.g O
  comm := by
    have key : (chartOpenOverMap B S hS d.U (homOfLE h) ≫
        chartOpenOverRestrict B S hS d.U d.V d.g O) ≫ chartOpenOverι B S hS d.V O =
          chartOpenOverι B S hS d.U V ≫ d.g := by
      rw [Category.assoc, chartOpenOverRestrict_comp_ι, ← Category.assoc,
        chartOpenOverMap_comp_ι]
    change (yoneda.map (chartOpenOverι B S hS d.U V) ≫ d.U.obj.hom) ≫ f.hom =
      yoneda.map (chartOpenOverMap B S hS d.U (homOfLE h) ≫
        chartOpenOverRestrict B S hS d.U d.V d.g O) ≫
          yoneda.map (chartOpenOverι B S hS d.V O) ≫ d.V.obj.hom
    rw [Category.assoc, d.comm, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, key]

/-- The regular functions on an affine open of an étale chart are bounded by the size of the
chart. -/
private theorem mk_chartRing_chartOpens_le_size {X : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X.1) (O : (chartScheme U).affineOpens) :
    #(chartRing B S hS X.1 X.2 ((chartOpens B S hS U).obj O.1)) ≤ (chartScheme U).size :=
  (Scheme.mk_sections_coe_opens (chartScheme U) O.1).trans_le
    (Scheme.mk_sections_le_size (chartScheme U) O)

/-- **The sections of a pulled-back quasi-coherent module over an affine chart lying over an
affine chart are bounded.** For `g : X ⟶ T`, a quasi-coherent `𝒪_T`-module `𝒥` and a chart
diagram `d` with both charts affine, the sections of `g^*𝒥` over `d.U` are
`𝒪_X(d.U) ⊗_{𝒪_T(d.V)} 𝒥(d.V)` (Stacks 083K), of cardinality at most
`max ℵ₀ (max #𝒪_X(d.U) #𝒥(d.V))`. -/
theorem mk_modulePullback_le_of_chartDiagram {X T : AlgebraicSpaces B S hS} (g : X ⟶ T)
    (M : Modules.{u, u} B S hS T.1 T.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 T.1 g.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS T.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    #(((modulePullback B S hS g).obj M).val.obj (op d.U)) ≤
      max ℵ₀ (max #(chartRing B S hS X.1 X.2 d.U) #(M.val.obj (op d.V))) := by
  let := chartDiagramAlgebra B S hS g d
  exact (Cardinal.mk_congr (Equiv.ofBijective _
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g M hM d haU
      haV))).symm.trans_le Cardinal.mk_tensorProduct_le

namespace SquareZeroExtension

/-- **A site contains the chart thickenings of an extension whose ideal is pulled back along a
chart diagram with small sections.** Let `E` be a square-zero extension over `f : X ⟶ Y` with
`ℐ ≅ g^*𝒥` for `g : X ⟶ T` and `𝒥` quasi-coherent, and let `d` be a chart diagram over `g`. If
the sections of `𝒥` over the affine opens of the chart `d.V` have at most `λ` elements, `λ`
below the cutoff, the site contains the chart thickening of `E` at `d.U`. -/
theorem contains_chartThickening_of_iso_modulePullback_of_chartDiagram
    {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f) (g : X ⟶ T)
    (M : Modules.{u, u} B S hS T.1 T.2) (hM : M.IsQuasicoherentOnSite)
    (eI : E.I ≅ (modulePullback B S hS g).obj M) (d : ChartDiagram B S hS X.1 T.1 g.hom)
    {lam : Cardinal.{u}} (hlam : lam < B.cutoff)
    (hMlam : ∀ O : (chartScheme d.V).affineOpens,
      #(M.val.obj (op ((chartOpens B S hS d.V).obj O.1))) ≤ lam) :
    B.Contains (chartThickening B S hS E d.U) := by
  have hκ : max ℵ₀ (max (chartScheme d.U).size lam) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt d.U.obj.left.left.2 hlam)
  have hsec : ∀ V : (chartScheme d.U).affineOpens,
      #(Space.chartRing B S hS X.1 X.2 ((chartOpens B S hS d.U).obj V.1)) ≤
        max ℵ₀ (max (chartScheme d.U).size lam) := fun V =>
    (mk_chartRing_chartOpens_le_size d.U V).trans ((le_max_left _ _).trans (le_max_right _ _))
  refine E.contains_chartThickening_of_mk_le d.U hκ fun V => (E.mk_A_le_mk_mul _).trans ?_
  obtain ⟨ι, _, Vs, Os, hcov, hle, hpre⟩ :=
    exists_finite_affineOpens_cover_le_preimage d.schemeMap V
  have hP : #(((modulePullback B S hS g).obj M).val.obj
      (op ((chartOpens B S hS d.U).obj V.1))) ≤ max ℵ₀ (max (chartScheme d.U).size lam) :=
    mk_sections_chartOpens_le_of_iSup_eq ((modulePullback B S hS g).obj M) d.U
      (fun i => (Vs i).1) V.1 hcov hle
      (le_max_left _ _) fun i =>
        (mk_modulePullback_le_of_chartDiagram g M hM
          (d.restrictChartOpensLE (Os i).1 (Vs i).1 (hpre i)) (Vs i).2 (Os i).2).trans
          (max_le (le_max_left _ _) (max_le (hsec (Vs i))
            ((hMlam (Os i)).trans ((le_max_right _ _).trans (le_max_right _ _)))))
  have hinj : Function.Injective (eI.hom.val.app (op ((chartOpens B S hS d.U).obj V.1))) :=
    Function.LeftInverse.injective (g := eI.inv.val.app (op ((chartOpens B S hS d.U).obj V.1)))
      fun x => congrArg (fun φ => (φ.val.app (op ((chartOpens B S hS d.U).obj V.1))).hom x)
        eI.hom_inv_id
  exact (mul_le_mul' (hsec V) ((Cardinal.mk_le_of_injective hinj).trans hP)).trans
    (Cardinal.mul_eq_self (le_max_left _ _)).le

end SquareZeroExtension

/-- The sections of the ideal sheaf of a closed subspace over an affine open of an étale chart
are bounded by the size of the chart: they are an ideal of the regular functions. -/
theorem mk_definingIdealSheaf_sections_le (Y : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS Y.1) (V : SmallEtale B S hS Y.1)
    (O : (chartScheme V).affineOpens) :
    #((definingIdealSheaf B S hS Y Z).toSheafOfModules.val.obj
      (op ((chartOpens B S hS V).obj O.1))) ≤ (chartScheme V).size :=
  (Cardinal.mk_subtype_le _).trans (mk_chartRing_chartOpens_le_size V O)

namespace SquareZeroExtension

/-- The canonical comparison `f⁻¹𝒪_Y ≅ i⁻¹g⁻¹𝒪_Y` for `i ≫ g = f` is, as a morphism, the
transport along `f = i ≫ g` followed by the inverse of the composition law of Stacks 03G8. -/
theorem canonicalBaseComparison_hom {X Y Z : AlgebraicSpaces B S hS} (i : X ⟶ Z) (g : Z ⟶ Y)
    (f : X ⟶ Y) (h : i ≫ g = f) :
    (canonicalBaseComparison B S hS i g f h).hom =
      eqToHom (congrArg (fun φ ↦ (smallEtaleInverseImageRing B S hS φ).obj
          (smallEtaleRingedTopos B S hS Y).O) h.symm) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i g).inv.app
          (smallEtaleRingedTopos B S hS Y).O := by
  subst h
  exact (Category.id_comp _).symm

/-- **The algebra compatibility of a realization, with the canonical comparison unfolded**: the
algebra structure of `𝒜` is the structure map of `h : X' ⟶ Y` read through the transport along
`f = i ≫ h` and the composition law `(i ≫ h)⁻¹𝒪_Y ≅ i⁻¹h⁻¹𝒪_Y` of Stacks 03G8. -/
theorem Realization.algebra_compatibility_eqToHom {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {E : SquareZeroExtension B S hS f} (r : Realization B S hS E) :
    E.toBase =
      eqToHom (congrArg (fun φ ↦ (smallEtaleInverseImageRing B S hS φ).obj
          (smallEtaleRingedTopos B S hS Y).O) r.over_base.symm) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS r.immersion r.toBase).inv.app
            (smallEtaleRingedTopos B S hS Y).O ≫
        (smallEtaleInverseImageRing B S hS r.immersion).map
          (smallEtaleRingedToposHom B S hS r.toBase).fSharpInverseImage ≫
        r.sheafIso.hom := by
  rw [r.algebra_compatibility, r.baseComparison_canonical, canonicalBaseComparison_hom,
    Category.assoc]

/-- **Stacks 05ZT on the given site, for an ideal pulled back from an ideal sheaf.** A
square-zero extension over `f : X ⟶ Y` whose ideal is `f^*ℐ_Z` for the ideal sheaf `ℐ_Z` of a
closed subspace `Z` of `Y` is realized by a first-order thickening `X ⊂ X'` over `Y` of the given
big fppf site: for a charted presentation of `f`, the site contains the thickening of the
presenting chart of `X`, by the size bound of
`SquareZeroExtension.contains_chartThickening_of_iso_modulePullback_of_chartDiagram` applied to
the chart diagram of the presentation, and hence that of the relation chart, so
`AlgebraicGeometry.Space.SquareZeroExtension.nonempty_realization` applies. -/
theorem nonempty_realization_of_iso_modulePullback_definingIdealSheaf
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
    (Z : ClosedSubspaces B S hS Y.1)
    (eI : E.I ≅ (modulePullback B S hS f).obj (definingIdealSheaf B S hS Y Z).toSheafOfModules) :
    Nonempty (Realization B S hS E) := by
  obtain ⟨C⟩ := nonempty_chartedPresentation B S hS f
  have hU : B.Contains (chartThickening B S hS E (presentationChart C.P)) :=
    E.contains_chartThickening_of_iso_modulePullback_of_chartDiagram f _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS Y Z) eI C.diagram
      C.diagram.V.obj.left.left.2 (mk_definingIdealSheaf_sections_le Y Z C.diagram.V)
  exact nonempty_realization E C hU
    (contains_chartThickening_of_hom E (presentationRelationSourceHom C.P) hU)

end SquareZeroExtension

end AlgebraicGeometry.Space

end
