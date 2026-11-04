module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentArtinRees
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealAnnihilatorSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# Sections of the annihilator subsheaf over an affine étale chart

Let `F` be an algebraic space, `I ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and `G` an
`𝒪_F`-module.  The subsheaf of sections annihilated by `I`, the object of [Stacks, Tag 0856],
is defined by a condition quantified over *all* charts lying over the given one.  Over an
*affine* chart that quantifier is redundant: a section is annihilated by `I` as soon as the
sections of `I` over that very chart kill it.

This is part (2) of [Stacks, Tag 0856].

## Main results

* `AlgebraicGeometry.Space.mem_annihilatorSubmodule_obj_of_isAffine`: over an affine étale
  chart `W` the sections of the annihilator subsheaf are exactly the `s ∈ G(W)` with
  `I(W) s = 0`.
* `AlgebraicGeometry.Space.smul_restrictₛₗ_eq_zero_of_isAffine`: if the sections of `I` over an
  affine chart `W` kill `s`, then the sections of `I` over an affine chart `W'` over `W` kill the
  restriction of `s`.

## Implementation notes

Quasi-coherence of `I` enters through Stacks 03DX(2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`: between affine
charts the sections of `I` are the base change of the sections over the larger chart, so
`I(W')` is spanned over `𝒪_F(W')` by the restrictions of the sections of `I(W)`.  That is
`AlgebraicGeometry.Space.span_image_chartRestrictLinear_eq`.  An arbitrary chart over `W` is
then covered by affine ones
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`) and the conclusion is local
because `G` is a sheaf.

No finiteness of `I` is needed for this part, and `G` is an arbitrary `𝒪_F`-module.  The tag
states its three parts under the single hypothesis that `I` is of finite type; that hypothesis
is not consumed here, so the statement below is the stronger one.

Charts are indexed by objects of `(SmallEtale B S hS F)ᵒᵖ` rather than by objects of
`SmallEtale B S hS F` together with `op`, matching
`AlgebraicGeometry.Space.mem_annihilatorSubmodule_obj`: the structure sheaf is indexed by
`(smallEtaleRingedSite B S hS F hF).C`, whose projection out of the ringed site is not
reducible, so a hand-written `op U` lands on a different spelling of the same object and the
scalar actions no longer share an instance.

## References

* [Stacks Project, Tag 0856](https://stacks.math.columbia.edu/tag/0856)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

variable {B S hS F hF}
  {I : (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).Submodule}
  {G : Modules.{u, u} B S hS F hF}

/-- If a section `a` of the structure sheaf annihilates a section `s` of an `𝒪_F`-module, then
the restriction of `a` annihilates the restriction of `s`. -/
theorem restrictₛₗ_smul_eq_zero {W W' : (SmallEtale B S hS F)ᵒᵖ} (g : W ⟶ W')
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj W)
    {s : G.val.obj W} (hs : a • s = 0) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.map g).hom a •
      G.val.restrictₛₗ g s = 0 := by
  rw [← map_smulₛₗ, hs, map_zero]

/-- **The affine-to-affine step of [Stacks, Tag 0856] part (2).**  Let `I` be a sheaf of ideals
which is cartesian on affine charts.  If every section of `I` over an affine chart `W` kills
`s ∈ G(W)`, then every section of `I` over an affine chart `W'` over `W` kills the restriction
of `s`. -/
theorem smul_restrictₛₗ_eq_zero_of_isAffine
    (hI : IsCartesianOnAffineCharts I.toSheafOfModules) {W W' : (SmallEtale B S hS F)ᵒᵖ}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W.unop))
    (hW' : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W'.unop))
    (g : W ⟶ W') {s : G.val.obj W}
    (hs : ∀ a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj W,
      a ∈ I.obj W → a • s = 0)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj W')
    (hb : b ∈ I.obj W') :
    b • G.val.restrictₛₗ g s = 0 := by
  have hspan := span_image_chartRestrictLinear_eq B S hS F hF
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) I g.unop
    (hI W.unop W'.unop hW hW' g.unop).2
  set t : G.val.obj (op W'.unop) := G.val.restrictₛₗ g s
  have hle : chartSubmodule B S hS F hF I W'.unop ≤
      LinearMap.ker (LinearMap.toSpanSingleton (chartRing B S hS F hF W'.unop)
        (G.val.obj (op W'.unop)) t) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact restrictₛₗ_smul_eq_zero g a (hs a ha)
  exact hle hb

/-- **[Stacks, Tag 0856], part (2): the sections of the annihilator subsheaf over an affine
chart.**  Over an affine étale chart `W` of an algebraic space, a section of `G` lies in the
subsheaf annihilated by a quasi-coherent sheaf of ideals `I` exactly when the sections of `I`
over `W` itself kill it — no restriction to a smaller chart has to be tested. -/
@[stacks 0856 "part (2)"]
theorem mem_annihilatorSubmodule_obj_of_isAffine
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (W : (SmallEtale B S hS F)ᵒᵖ)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W.unop))
    (s : G.val.obj W) :
    s ∈ (annihilatorSubmodule B S hS F hF I G).toSubmodule.obj W ↔
      ∀ a : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O).obj.obj W,
        a ∈ I.obj W → a • s = 0 := by
  rw [mem_annihilatorSubmodule_obj]
  refine ⟨fun hmem a ha => ?_, fun hs => ?_⟩
  · exact (congrArg (fun x : G.val.obj W => a • x)
      (Stacks.SheafOfModules.restrictₛₗ_id_apply G W s)).symm.trans (hmem W (𝟙 W) a ha)
  · intro W' g b hb
    obtain ⟨J, Y, p, hYaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F W'.unop
    refine G.isSheaf.isSeparated W'.unop _ hcov _ 0 ?_
    rintro Z k hk
    obtain ⟨j, k', rfl⟩ := (Sieve.mem_ofArrows_iff Y p k).mp hk
    have haff := smul_restrictₛₗ_eq_zero_of_isAffine
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hI) hW (hYaff j)
      (g ≫ (p j).op) hs
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O).obj.map (p j).op).hom b)
      (I.toSubmodule.map_mem (p j).op hb)
    have hYj : G.val.restrictₛₗ (p j).op (b • G.val.restrictₛₗ g s) = 0 := by
      refine (map_smulₛₗ (G.val.restrictₛₗ (p j).op) b _).trans ?_
      refine Eq.trans ?_ haff
      exact congrArg _ (G.val.map_comp_apply g (p j).op s).symm
    show G.val.map (k' ≫ p j).op _ = G.val.map (k' ≫ p j).op 0
    rw [map_zero]
    exact (G.val.map_comp_apply (p j).op k'.op _).trans
      ((congrArg (G.val.map k'.op).hom hYj).trans (map_zero _))

end AlgebraicGeometry.Space

end
