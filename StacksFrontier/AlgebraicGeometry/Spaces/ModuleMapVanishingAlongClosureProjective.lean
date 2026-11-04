module

public import StacksFrontier.AlgebraicGeometry.Etale.AffineEtaleOpenMap
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAlongClosureEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProjectiveSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFinitePresentationProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapVanishingPerPointChart

/-!
# Stacks 0CWB: a map of modules vanishing on a set of fibres vanishes on its closure

In Situation 0CWA — an affine base `S = \Spec R`, an algebraic space `X` over `S` and a map
`u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S` — suppose `X` is locally of
finite presentation over `S` and `𝒢` is of finite presentation.  Let `T` be a set of points of
`S` and let `s` be a point of its closure.  If `u_t = 0` for every `t ∈ T`, then `u_s = 0`.

This file proves that, Stacks Lemma 77.8.4.

## Main results

* `ModuleMapFlatTargetSituation.forall_mem_basePointIdeal_smul_top_of_projective_pullback`:
  the commutative algebra of the source's last paragraph, at one affine étale chart which
  Stacks 0CVY has refined and over whose further étale neighbourhood the sections of `𝒢` are
  projective.
* `ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure`: a map of modules with flat
  target vanishing on the fibres over a set `T` of base points vanishes on the fibre over every
  point of the closure of `T`.

## Implementation notes

**The source's proof, step by step, and where each step lives.**

The geometric reduction — "to check whether `u_s` is zero is étale local on the fibre `X_s`,
hence we may pick a point `x` of `|X_s| ⊆ |X|` and check in an étale neighbourhood" — is
`ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure_of_forall_point`: it reduces `u_s = 0`
to producing, for each point of `|X|`, one affine étale chart of `X` around it at which the ideal
condition passes from the points of `T` to `s`.  That is exactly the shape of Stacks 0CVY, which
is a statement about one prescribed point and may return a different chart for each.

The choice of chart is Stacks 0CVY,
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections_of_isFlatOverAt`, at
`f : X ⟶ \Spec R` read as the morphism to the final algebraic space.  Its three hypotheses are
discharged from the data at hand: quasi-coherence of `𝒢` on charts is
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, finite presentation on charts is
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChart`, and chartwise flatness over the
base is the hypothesis `flat_G` of Situation 0CWA read at the chart square.  **Stacks 0CVY and
not Stacks 0CVZ**: the latter assumes `f` of finite presentation, which is more than this tag's
"locally of finite presentation".

What Stacks 0CVY returns is a square of affine objects `U' ⟶ U` of `X` and `E' ⟶ V` of the base,
a morphism `k : U' ⟶ E'`, a point of `U'` over `x`, and projectivity of the sections of the
Zariski pullback of `𝒢|_U` to `U'` over the functions on `E'`.  Two translations follow.  First,
`U'` with the composite structure morphism *is* an affine étale chart `Z₀` of `X`, and the
morphism `U' ⟶ U` of the site *is* the morphism of chart schemes `Z₀ ⟶ U` — so the module whose
sections are projective is the pullback of `𝒢|_U` along a morphism of charts, and
`AlgebraicGeometry.Space.projective_sections_of_projective_pullback_restrictToChart` turns its
sections into `𝒢(Z₀)`.  Second, `E'` is étale over the base: it is an étale chart of the final
algebraic space, which is represented, so `AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff`
reads the chart condition as étaleness of the morphism of schemes.

The commutative algebra of the last paragraph — the flattening ideal of Stacks 083L, the
inclusion `T ⊆ V(I)`, and `s ∈ V(I)` by closedness — is
`Stacks.Flattening.forall_mem_ker_smul_top_of_projective_of_isOpenMap`, which asks for
projectivity only over the *upper* ring `\Gamma(E', ⊤)`, flatness over `R`, openness of
`\Spec \Gamma(E', ⊤) ⟶ \Spec R` and reducedness of the fibre.  Flatness over `R` is
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.flat_sections_G`; openness is
`AlgebraicGeometry.isOpenMap_comap_appTop_of_etale`; reducedness is
`AlgebraicGeometry.isReduced_appTop_tensorProduct_residueField`.  The two rings of scalars form a
tower over `R` because every morphism of the big fppf site over `S` is a morphism over `S`, so
the triangle of `k` is `CategoryTheory.Over.w`.

**The closure hypothesis crosses between two spellings.**  The source's `s ∈ \overline{T}` is a
statement about points of the scheme `S`, while the algebra lemma wants it in
`\Spec \Gamma(S, ⊤)`.  Rather than identify the two spaces, the set `T` is carried over by
`AlgebraicGeometry.Space.basePointIdeal` and the membership is re-derived from
`AlgebraicGeometry.Space.basePointIdeal_le_of_mem_closure`, the geometric form of the same
argument: the closure of a set in a prime spectrum is the zero locus of its vanishing ideal, and
an ideal of functions vanishing at every point of `T` vanishes at every point of `\overline{T}`.

## References

* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS)

namespace ModuleMapFlatTargetSituation

/-- **The commutative algebra of the last paragraph of Stacks 0CWB, at one chart.**

In Situation 0CWA, let `g : Z₀ ⟶ U` be a morphism of étale scheme charts of `X` with `Z₀` affine,
let `E'` be an affine object of the big fppf site which is étale over the base, and let `k` be a
morphism from the object of `Z₀` to `E'`.  Assume the sections of the Zariski pullback of `𝒢|_U`
along `g` form a projective module over the functions on `E'`.  Let `T` be a set of points of the
base and let `s` be a point of its closure.  If `u(ℱ(Z₀)) ⊆ 𝔭_t · 𝒢(Z₀)` for every `t ∈ T`, then
`u(ℱ(Z₀)) ⊆ 𝔭_s · 𝒢(Z₀)`.

Projectivity is moved onto the sections `𝒢(Z₀)` by
`AlgebraicGeometry.Space.projective_sections_of_projective_pullback_restrictToChart`, and
`Stacks.Flattening.forall_mem_ker_smul_top_of_projective_of_isOpenMap` concludes; see the
implementation notes of this file for the remaining inputs. -/
theorem forall_mem_basePointIdeal_smul_top_of_projective_pullback
    {Z₀ U : SmallEtale B S hS D.X.1} (g : Z₀ ⟶ U) (hZaff : IsAffine (chartScheme Z₀))
    (E' : BigFppfOver B S hS) (hE'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj E'))
    (k : (SmallEtale.toOver B S hS D.X.1).obj Z₀ ⟶ E')
    (hEet : Etale ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from E') :
      (BigFppfOver.toScheme B S hS).obj E' ⟶ S))
    (hproj :
      letI M := (Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChart B S hS D.X.2 D.G U)
      letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
        Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤))
    (T : Set S) (s : S) (hs : s ∈ closure T)
    (hT :
      letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
      ∀ t ∈ T, ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
        basePointIdeal B S hS t • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
      basePointIdeal B S hS s • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u)) := by
  have := hZaff
  have := hE'aff
  -- projectivity, carried from the pullback of the chart restriction to the sections over `Z₀`
  have hprojZ :
      let : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)
          (D.G.val.obj (op Z₀) : Type u) :=
        Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)
        (D.G.val.obj (op Z₀) : Type u) :=
    projective_sections_of_projective_pullback_restrictToChart B S hS D.X D.G
      D.quasicoherent_G g E' k hproj
  set f : (BigFppfOver.toScheme B S hS).obj E' ⟶ S :=
    (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from E') with hf
  have : Etale f := hEet
  let : Algebra Γ(S, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) (S.residueField s) := (S.Γevaluation s).hom.toAlgebra
  let : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  let : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
  let : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (D.F.val.obj (op Z₀) : Type u) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
  have : Module.Flat Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    D.flat_sections_G B S hS Z₀ hZaff
  have : _root_.IsReduced
      (Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) ⊗[Γ(S, ⊤)] S.residueField s) :=
    isReduced_appTop_tensorProduct_residueField f s
  -- the two rings of scalars form a tower over the base: every morphism of the site is one
  -- over the base
  have hcomp : (BigFppfOver.toScheme B S hS).map k ≫ f = chartToBase B S hS D.X Z₀ := by
    rw [hf, ← Functor.map_comp]
    exact congrArg (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.hom_ext _ _)
  have halg : ∀ r : Γ(S, ⊤),
      ((BigFppfOver.toScheme B S hS).map k).appTop.hom
          (algebraMap Γ(S, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) r) =
        chartToBaseRingHom B S hS D.X Z₀ r := by
    intro r
    show ((BigFppfOver.toScheme B S hS).map k).appTop.hom (f.appTop.hom r) =
      (chartToBase B S hS D.X Z₀).appTop.hom r
    rw [← hcomp, Scheme.Hom.comp_appTop]
    rfl
  have : IsScalarTower Γ(S, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)
      (D.G.val.obj (op Z₀) : Type u) := by
    refine ⟨fun r a x => ?_⟩
    show ((BigFppfOver.toScheme B S hS).map k).appTop.hom (r • a) • x =
      chartToBaseRingHom B S hS D.X Z₀ r •
        (((BigFppfOver.toScheme B S hS).map k).appTop.hom a • x)
    rw [Algebra.smul_def, map_mul, mul_smul, halg]
    rfl
  -- the map of sections, read as a map of modules over the upper ring
  let uL : (D.F.val.obj (op Z₀) : Type u) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)]
      (D.G.val.obj (op Z₀) : Type u) :=
    { toFun := fun z => D.u.val.app (op Z₀) z
      map_add' := fun z w => (D.u.val.app (op Z₀)).hom.map_add z w
      map_smul' := fun a z => (D.u.val.app (op Z₀)).hom.map_smul _ z }
  -- the points of `T`, read in the prime spectrum of the ring of functions on the base
  have hker : ∀ t : S, RingHom.ker (S.Γevaluation t).hom = basePointIdeal B S hS t :=
    fun t => (basePointIdeal_eq_ker_Γevaluation B S hS t).symm
  let P : S → PrimeSpectrum Γ(S, ⊤) := fun t => ⟨RingHom.ker (S.Γevaluation t).hom,
    RingHom.ker_isPrime _⟩
  have hsmem : P s ∈ closure (P '' T) := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.mem_zeroLocus]
    refine fun a ha => ?_
    show a ∈ RingHom.ker (S.Γevaluation s).hom
    rw [hker]
    refine basePointIdeal_le_of_mem_closure B S hS T hs (fun t ht b hb => ?_) ha
    rw [← hker]
    exact (PrimeSpectrum.mem_vanishingIdeal _ b).mp hb _ ⟨t, ht, rfl⟩
  have hres := Stacks.Flattening.forall_mem_ker_smul_top_of_projective_of_isOpenMap
    (R := Γ(S, ⊤)) (R' := Γ((BigFppfOver.toScheme B S hS).obj E', ⊤))
    (isOpenMap_comap_appTop_of_etale f) uL hprojZ (P '' T) (S.residueField s) hsmem
    (fun t' ht' m => by
      obtain ⟨t, ht, rfl⟩ := ht'
      exact (hker t ▸ hT t ht m : _ ∈ (P t).asIdeal • _))
  intro z
  have hz := hres z
  rwa [show RingHom.ker (algebraMap Γ(S, ⊤) (S.residueField s)) = _ from hker s] at hz

/-- In Situation 0CWA, let `T` be a subset of the base and let `s` be a point of the closure of
`T`.  If `X` is locally of finite presentation over the base, `𝒢` is of finite presentation, and
`u_t = 0` for every `t ∈ T`, then `u_s = 0`.

The geometric reduction is
`ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure_of_forall_point`, which asks for one
affine étale chart per point of `|X|` at which the ideal condition passes from `T` to `s`.  The
chart is produced by Stacks 0CVY,
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections_of_isFlatOverAt`,
whose three hypotheses are discharged from the two finite-presentation hypotheses and the
flatness carried by Situation 0CWA; the ideal condition at the chart it returns is
`ModuleMapFlatTargetSituation.forall_mem_basePointIdeal_smul_top_of_projective_pullback`.
See the implementation notes of this file. -/
@[stacks 0CWB]
theorem fibreMapEqZero_of_mem_closure
    (hfp : IsLocallyOfFinitePresentation B S hS (D.structureMorphism B S hS).hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (T : Set S) (s : S) (hs : s ∈ closure T)
    (hT : ∀ t ∈ T, D.FibreMapEqZero B S hS t) :
    D.FibreMapEqZero B S hS s := by
  refine D.fibreMapEqZero_of_mem_closure_of_forall_point B S hS T s (fun x => ?_) hT
  obtain ⟨U, V, U', E', p, q, k, x'', hpet, hqet, hU'aff, hE'aff, hsq, hbase, -, hproj⟩ :=
    exists_isAffine_etale_charts_projective_sections_of_isFlatOverAt B S hS D.X.2
      (terminalSpace B S hS).2 (D.structureMorphism B S hS).hom D.G x hfp
      (fun W => isQuasicoherent_restrictToChart B S hS D.X D.G D.quasicoherent_G W)
      (fun W => isFinitePresentation_restrictToChart B S hS D.X D.G D.quasicoherent_G hGfp W)
      (fun W W' gg x' hsquare _ =>
        D.flat_G ⟨W, W', gg, hsquare⟩ (pointsToScheme B S hS _ x'))
  let Z₀ : SmallEtale B S hS D.X.1 := ⟨CostructuredArrow.mk (yoneda.map p ≫ U.obj.hom), hpet⟩
  let g : Z₀ ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p rfl)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj E') := hE'aff
  have hEet : Etale ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from E') :
      (BigFppfOver.toScheme B S hS).obj E' ⟶ S) := by
    refine (presheaf_yoneda_map_etale_iff B S hS (Over.mkIdTerminal.from E')).mp ?_
    have heq : yoneda.map q ≫ V.obj.hom = yoneda.map (Over.mkIdTerminal.from E') :=
      (baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _
    rwa [heq] at hqet
  refine ⟨Z₀, hU'aff, ⟨x'', hbase⟩, fun hall => ?_⟩
  exact D.forall_mem_basePointIdeal_smul_top_of_projective_pullback B S hS g hU'aff E' hE'aff k
    hEet hproj T s hs hall

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
