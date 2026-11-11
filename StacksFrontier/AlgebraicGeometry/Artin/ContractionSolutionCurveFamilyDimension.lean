module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleFibreSupportDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Fibre dimension of an algebraic space dominated by a proper scheme

Let `X` be an algebraic space over `S` and `f : Z ⟶ X` a proper surjective morphism from a
scheme `Z` over `S` whose fibres over `S` have dimension at most `n` at every point. Then the
fibres of `X` over `S` have dimension at most `n` at every point; for `n = 1` this is the
relative-dimension clause of a family of curves.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_le_of_universallyClosed_of_etale`: the
  scheme-level statement. In a commutative square `q ≫ pV = e ≫ pZ` of schemes with `q`
  universally closed and surjective and `e` étale, a bound on the local dimensions of the fibres
  of `pZ` bounds the local dimensions of the fibres of `pV`.
* `AlgebraicGeometry.Space.exists_le_one_holdsOnEveryEtaleChartAtPoint_hasFiberDimensionAt`:
  at every point of `X` the fibre dimension of `X ⟶ S` is some natural number at most one, when
  a proper surjective scheme `Z ⟶ X` has fibres over `S` of dimension at most one.
* `AlgebraicGeometry.Space.hasRelativeDimensionLE_one_terminal_from_of_isProper_of_isSurjective`:
  the same, as relative dimension at most one (Stacks 06LR, part (1)).

## Implementation notes

The scheme statement compares fibres over a point `s` of the base. The fibre of `q ≫ pV` maps
to the fibre of `pV` by a base change of `q`, which is closed and surjective, so the latter has
dimension at most that of the former. The fibre of `q ≫ pV = e ≫ pZ` maps to the fibre of `pZ`
by a base change of `e`, which is étale, so it has the same local dimensions (Tag 04N4), and
its dimension is the supremum of those (Tag 0B7I).

For the space statement one étale chart at the point suffices: the target chart is the
terminal object `Over.mk (𝟙 S)` of the site, whose Yoneda presheaf is terminal, and the source
chart is an étale atlas `V` of `X`. The base change of `f` along the atlas is a scheme `W`
proper and surjective over `V` and étale over `Z`, and the scheme statement applies to the
square formed by `W`, `V`, `Z` and `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If the fibres of a morphism of schemes have local dimension at most `n` at the canonical
point over each point of the source, then they have local dimension at most `n` at every
point. -/
theorem topologicalKrullDimAt_fiber_le_of_forall {X Y : Scheme.{u}} (f : X ⟶ Y)
    {n : WithBot ℕ∞}
    (h : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ n) (y : Y)
    (x : f.fiber y) : topologicalKrullDimAt (f.fiber y) x ≤ n := by
  rw [topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo y) x]
  generalize f.fiberHomeo y x = w
  obtain ⟨z, hz⟩ := w
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
  subst hz
  have hz := h z
  rw [topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f z)) (f.asFiber z)] at hz
  simpa [Scheme.Hom.asFiber] using hz

/-- For an étale `e : X ⟶ Y` and `g : Y ⟶ S`, a bound on the local dimensions of the fibres
of `g` bounds the dimension of every fibre of `e ≫ g`: the fibre of `e ≫ g` is étale over the
fibre of `g`, so it has the same local dimensions, and its dimension is their supremum. -/
theorem topologicalKrullDim_fiber_comp_le_of_etale {X Y S : Scheme.{u}} (e : X ⟶ Y)
    (g : Y ⟶ S) [Etale e] {n : WithBot ℕ∞}
    (h : ∀ y : Y, topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y) ≤ n) (s : S) :
    topologicalKrullDim ((e ≫ g).fiber s) ≤ n := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun w => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    topologicalKrullDimAt_eq_of_etale (Scheme.Hom.fiberMapComp e g s) w]
  exact topologicalKrullDimAt_fiber_le_of_forall g h s _

/-- In a commutative square `q ≫ pV = e ≫ pZ` of schemes with `q` universally closed and
surjective and `e` étale, if the fibres of `pZ` have local dimension at most `n` everywhere,
then so do the fibres of `pV`. The fibre of `q ≫ pV` maps onto the fibre of `pV` by a closed
map, and it is étale over the fibre of `pZ`. -/
theorem topologicalKrullDimAt_fiber_le_of_universallyClosed_of_etale
    {V W Z S : Scheme.{u}} (q : W ⟶ V) (e : W ⟶ Z) (pV : V ⟶ S) (pZ : Z ⟶ S)
    (comm : q ≫ pV = e ≫ pZ) [UniversallyClosed q] [Surjective q] [Etale e]
    {n : WithBot ℕ∞}
    (h : ∀ z : Z, topologicalKrullDimAt (pZ.fiber (pZ z)) (pZ.asFiber z) ≤ n) (v : V) :
    topologicalKrullDimAt (pV.fiber (pV v)) (pV.asFiber v) ≤ n := by
  refine (topologicalKrullDimAt_le_topologicalKrullDim _).trans ?_
  have hW : topologicalKrullDim ((q ≫ pV).fiber (pV v)) ≤ n := by
    rw [comm]
    exact topologicalKrullDim_fiber_comp_le_of_etale e pZ h _
  have hpb := isPullback_fiberMapComp q pV (pV v)
  have : UniversallyClosed (Scheme.Hom.fiberMapComp q pV (pV v)) :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) hpb ‹_›
  have : Surjective (Scheme.Hom.fiberMapComp q pV (pV v)) :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb ‹_›
  exact (Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap _
    (Scheme.Hom.fiberMapComp q pV (pV v)).continuous
    (Scheme.Hom.fiberMapComp q pV (pV v)).surjective
    (Or.inl (Scheme.Hom.fiberMapComp q pV (pV v)).isClosedMap.specializingMap)).trans hW

namespace Space

/-- **Fibre dimension of an algebraic space dominated by a proper scheme.** Let `X` be an
algebraic space over `S` and `f : Z ⟶ X` a proper surjective morphism from a scheme `Z` over
`S` whose fibres over `S` have dimension at most one at every point. Then at every point of
`X` the fibre of `X ⟶ S` has dimension some natural number at most one, in every étale chart.
-/
theorem exists_le_one_holdsOnEveryEtaleChartAtPoint_hasFiberDimensionAt
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Z : BigFppfOver B S hS} (f : yoneda.obj Z ⟶ X) (hf : IsProper B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hdim : ∀ z : (BigFppfOver.toScheme B S hS).obj Z,
      topologicalKrullDimAt ((B.inclusion.map Z.hom).fiber (B.inclusion.map Z.hom z))
        ((B.inclusion.map Z.hom).asFiber z) ≤ 1)
    (x : points B S hS X) :
    ∃ e : ℕ, e ≤ 1 ∧
      HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (terminal.from X) x := by
  let T := BigFppfOver.toScheme B S hS
  let T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT₀ : IsTerminal T₀ := Over.mkIdTerminal
  have hyT₀ : IsTerminal (yoneda.obj T₀) := hT₀.isTerminalObj yoneda _
  obtain ⟨V, a, haSurj, haEt⟩ := hX.exists_atlas
  obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS X hX V a).mp haSurj x
  let v := pointsEquivScheme B S hS V u
  have hv : (pointsEquivScheme B S hS V).symm v = u := Equiv.symm_apply_apply _ u
  let hV : V ⟶ T₀ := Over.homMk V.hom
  let hZ : Z ⟶ T₀ := Over.homMk Z.hom
  let b : yoneda.obj T₀ ⟶ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (hyT₀.uniqueUpToIso terminalIsTerminal).hom
  have hb := presheaf_etale_of_iso B S hS (hyT₀.uniqueUpToIso terminalIsTerminal)
  -- the base change of `f` along the atlas
  have hrep : yoneda.relativelyRepresentable f := hX.diagonal_representable.of_diag f
  let q : hrep.pullback a ⟶ V := hrep.snd a
  let e : hrep.pullback a ⟶ Z := hrep.fst' a
  have hqP : _root_.AlgebraicGeometry.IsProper (T.map q) :=
    ((presheaf_isProper_iff B S hS f (isAlgebraicSpace_yoneda B S hS Z) hX hrep).mp hf).property
      a _ _ (hrep.isPullback a)
  have hqS : Surjective (T.map q) :=
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX Z f).mpr hsurj).property
      a _ _ (hrep.isPullback a)
  have heE : Etale (T.map e) := haEt.property f (yoneda.map q) e (hrep.isPullback' a).flip
  have hcomm : T.map q ≫ T.map hV = T.map e ≫ T.map hZ := by
    rw [← T.map_comp, ← T.map_comp, hT₀.hom_ext (q ≫ hV) (e ≫ hZ)]
  have hle : topologicalKrullDimAt ((T.map hV).fiber (T.map hV v)) ((T.map hV).asFiber v) ≤ 1 :=
    topologicalKrullDimAt_fiber_le_of_universallyClosed_of_etale (T.map q) (T.map e) (T.map hV)
      (T.map hZ) hcomm hdim v
  have hne := topologicalKrullDimAt_ne_bot ((T.map hV).asFiber v)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at hle
  have hd1 : d ≤ 1 := by exact_mod_cast hle
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = d :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top ENat.one_ne_top hd1)
  refine ⟨k, by exact_mod_cast hd1, ?_⟩
  rw [← hu, ← hv]
  exact (hasRelativeDimensionAt_pointsMap_iff B S hS (k : ℕ∞) (terminal.from X) V T₀ a b hV
    haEt hb (terminal.hom_ext _ _) v).mpr hd.symm

/-- **Relative dimension of an algebraic space dominated by a proper scheme.** If a proper
surjective morphism `Z ⟶ X` from a scheme over `S` to an algebraic space over `S` has fibres
over `S` of dimension at most one everywhere, then `X ⟶ S` has relative dimension at most one
(Stacks 06LR, part (1)). -/
theorem hasRelativeDimensionLE_one_terminal_from_of_isProper_of_isSurjective
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Z : BigFppfOver B S hS} (f : yoneda.obj Z ⟶ X) (hf : IsProper B S hS f)
    (hsurj : IsSurjective B S hS f)
    (hdim : ∀ z : (BigFppfOver.toScheme B S hS).obj Z,
      topologicalKrullDimAt ((B.inclusion.map Z.hom).fiber (B.inclusion.map Z.hom z))
        ((B.inclusion.map Z.hom).asFiber z) ≤ 1) :
    HasRelativeDimensionLE 1 B S hS (terminal.from X) :=
  exists_le_one_holdsOnEveryEtaleChartAtPoint_hasFiberDimensionAt hX f hf hsurj hdim

end Space

end AlgebraicGeometry
