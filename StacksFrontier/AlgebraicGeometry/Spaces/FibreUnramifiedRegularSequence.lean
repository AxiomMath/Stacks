module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.UnramifiedMinimalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspacePullbackGerm

/-!
# The slicing sequence of Stacks 06N3 in the étale local ring of the fibre

Let `ξ : F ⟶ X` be a morphism of algebraic spaces over a scheme `S` in a big fppf site and let
`z` be a geometric point of `F`. A sequence of germs of regular functions which is regular in
the ordinary local ring `𝒪_{V, v}` of a scheme chart `V` of `F` has images forming a regular
sequence in the étale local ring `𝒪_{F, z̄}`. When the chart morphism `V ⟶ U` over `ξ` is
unramified and `𝒪_{V, v}` is regular, this gives a regular sequence generating the maximal ideal
of `𝒪_{F, z̄}`.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `isRegular_etaleLocalRing_of_isRegular_chartLocalRing`: a sequence of pullbacks of regular
  functions on an étale chart of `X` which is regular in the local ring of a chart of `F` is
  regular in the étale local ring `𝒪_{F, z̄}`.
* `forall_isRegular_etaleLocalRingMap_germ_of_isRegular_chartLocalRing`: the same for global
  regular functions on `X`, read at every small étale neighbourhood of the image geometric point.
* `etaleLocalRingMap_etaleLocalRingGerm_eval_eq`: the image in `𝒪_{F, z̄}` of the germ of a
  global function does not depend on the étale neighbourhood of the image point it is read on.
* `exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt`: if the chart
  morphism `V ⟶ U` over `ξ` is unramified at the point `v` of `V` under `z` and the local ring
  `𝒪_{V, v}` is regular, then some `f₁, …, f_d` in the maximal ideal of `𝒪_{U, u}` have images in
  `𝒪_{F, z̄}` forming a regular sequence generating the maximal ideal of `𝒪_{F, z̄}`.

## References

* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The germ in `𝒪_{F, z̄}` of a regular function pulled back from an étale chart of `X` is the
image, under the comparison homomorphism of étale local rings of **Stacks 04NG**, of its germ in
`𝒪_{X, ξ(z̄)}` at the induced étale neighbourhood of the image geometric point. -/
theorem chartLocalRingToEtaleLocalRing_germ_pullback {Xs Fs : AlgebraicSpaces B S hS}
    (ξ : Fs ⟶ Xs) {z : GeometricPoint B S hS Fs.1} (N : SmallEtaleNeighborhood z)
    (Uch : SmallEtale B S hS Xs.1) (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map gNU ≫ Uch.obj.hom)
    (a : Γ(chartScheme Uch, ⊤)) :
    chartLocalRingToEtaleLocalRing B S hS Fs.1 Fs.2 N
        ((chartScheme N.chart).presheaf.germ ⊤ (chartPoint B S hS Fs.1 N) trivial
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map gNU).op).hom a)) =
      etaleLocalRingMap Fs.2 ξ.hom z
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom z)
          (op (targetNeighborhood B S hS N Uch gNU hsq)) a) :=
  (etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ B S hS ξ z N
    (targetNeighborhood B S hS N Uch gNU hsq) gNU hsq rfl a).symm.trans
      (congrArg (etaleLocalRingMap Fs.2 ξ.hom z)
        (chartLocalRingToEtaleLocalRing_germ B S hS Xs.1 Xs.2
          (targetNeighborhood B S hS N Uch gNU hsq) a))

/-- A regular sequence in the chart local ring has regular image in the étale local ring, read
off as any family equal to the images termwise. -/
private theorem isRegular_ofFn_etaleLocalRing_of_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) {z : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood z) {r : ℕ} (f : Fin r → chartLocalRing B S hS F N)
    (g : Fin r → etaleLocalRing B S hS F z)
    (hreg : RingTheory.Sequence.IsRegular (chartLocalRing B S hS F N) (List.ofFn f))
    (h : ∀ i, chartLocalRingToEtaleLocalRing B S hS F hF N (f i) = g i) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F z) (List.ofFn g) := by
  have hpush := (isRegular_map_chartLocalRingToEtaleLocalRing_iff B S hS F hF N _).mpr hreg
  rwa [List.map_ofFn, Function.comp_def, funext h] at hpush

/-- **A regular sequence of pullbacks on a chart of the fibre is regular in the étale local
ring.** Let `ξ : F ⟶ X` be a morphism of algebraic spaces, let `z` be a geometric point of `F`,
let `N` be a small étale neighbourhood of `z` whose chart maps to an étale chart `Uch` of `X`
over `ξ`, and let `a₁, …, a_r` be regular functions on that chart of `X`. If the germs at the
point `v` of `N` of their pullbacks form a regular sequence in the ordinary local ring
`𝒪_{V, v}`, then their germs in `𝒪_{X, ξ(z̄)}` have images forming a regular sequence in the
étale local ring `𝒪_{F, z̄}`. -/
theorem isRegular_etaleLocalRing_of_isRegular_chartLocalRing {Xs Fs : AlgebraicSpaces B S hS}
    (ξ : Fs ⟶ Xs) {z : GeometricPoint B S hS Fs.1} (N : SmallEtaleNeighborhood z)
    (Uch : SmallEtale B S hS Xs.1) (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map gNU ≫ Uch.obj.hom)
    {r : ℕ} (a : Fin r → Γ(chartScheme Uch, ⊤))
    (hreg : RingTheory.Sequence.IsRegular (chartLocalRing B S hS Fs.1 N)
      (List.ofFn fun i : Fin r =>
        (chartScheme N.chart).presheaf.germ ⊤ (chartPoint B S hS Fs.1 N) trivial
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map gNU).op).hom (a i)))) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 z)
      (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom z
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom z)
          (op (targetNeighborhood B S hS N Uch gNU hsq)) (a i))) := by
  exact isRegular_ofFn_etaleLocalRing_of_eq B S hS Fs.1 Fs.2 N _ _ hreg fun i =>
    chartLocalRingToEtaleLocalRing_germ_pullback B S hS ξ N Uch gNU hsq (a i)

/-- **The image of the germ of a global function in the étale local ring of the source does not
depend on the étale neighbourhood it is read on.** -/
theorem etaleLocalRingMap_etaleLocalRingGerm_eval_eq {Xs Fs : AlgebraicSpaces B S hS}
    (ξ : Fs ⟶ Xs) {z : GeometricPoint B S hS Fs.1} (Nz : SmallEtaleNeighborhood z)
    (s : (SheafOfModules.unit (structureRingSheaf B S hS Xs)).sections)
    (N N' : SmallEtaleNeighborhood (geometricPointMap ξ.hom z)) :
    etaleLocalRingMap Fs.2 ξ.hom z
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom z) (op N)
          (s.eval (op N.chart))) =
      etaleLocalRingMap Fs.2 ξ.hom z
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom z) (op N')
          (s.eval (op N'.chart))) :=
  (etaleLocalRingGerm_globalFunctionsMap B S hS ξ s z Nz N).symm.trans
    (etaleLocalRingGerm_globalFunctionsMap B S hS ξ s z Nz N')

/-- **The fibre hypothesis of Stacks 06MD, reduced to the source's regular sequence on a scheme
chart.** Let `ξ : F ⟶ X` be a morphism of algebraic spaces, let `N` be a small étale
neighbourhood of a geometric point `z` of `F` whose chart maps to an étale chart `Uch` of `X`
over `ξ`, and let `f₁, …, f_r` be global regular functions on `X`. If the germs at the point of
`N` of their pullbacks to the chart of `N` form a regular sequence in the ordinary local ring
`𝒪_{V, v}`, then **for every** small étale neighbourhood of the image geometric point the images
of their germs form a regular sequence in the étale local ring `𝒪_{F, z̄}`. -/
theorem forall_isRegular_etaleLocalRingMap_germ_of_isRegular_chartLocalRing
    {Xs Fs : AlgebraicSpaces B S hS} (ξ : Fs ⟶ Xs) {z : GeometricPoint B S hS Fs.1}
    (N : SmallEtaleNeighborhood z) (Uch : SmallEtale B S hS Xs.1)
    (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map gNU ≫ Uch.obj.hom)
    {r : ℕ} (fs : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Xs)).sections)
    (hreg : RingTheory.Sequence.IsRegular (chartLocalRing B S hS Fs.1 N)
      (List.ofFn fun i : Fin r =>
        (chartScheme N.chart).presheaf.germ ⊤ (chartPoint B S hS Fs.1 N) trivial
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map gNU).op).hom
            ((fs i).eval (op Uch))))) :
    ∀ M : SmallEtaleNeighborhood (geometricPointMap ξ.hom z),
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 z)
        (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom z
          (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom z) (op M)
            ((fs i).eval (op M.chart)))) := by
  intro M
  exact isRegular_ofFn_etaleLocalRing_of_eq B S hS Fs.1 Fs.2 N _ _ hreg fun i =>
    (chartLocalRingToEtaleLocalRing_germ_pullback B S hS ξ N Uch gNU hsq
        ((fs i).eval (op Uch))).trans
      (etaleLocalRingMap_etaleLocalRingGerm_eval_eq B S hS ξ N (fs i)
        (targetNeighborhood B S hS N Uch gNU hsq) M)

/-- **The slicing sequence of the chart construction of Stacks 06N3, in the étale local ring of
the fibre.** Let `ξ : F ⟶ X` be a morphism of algebraic spaces, let `z` be a geometric point of
`F`, and let a small étale neighbourhood `N` of `z` map to an étale chart `Uch` of `X` over `ξ`
by a morphism whose underlying morphism of schemes `q : V ⟶ U` is locally of finite type and
**unramified** at the point `v` of `V` under `z`. If the local ring `𝒪_{V, v}` is **regular**,
then there are `d = (𝔪_v).spanFinrank` elements of the maximal ideal of `𝒪_{U, u}` whose images
in the étale local ring `𝒪_{F, z̄}` form a regular sequence **generating** the maximal ideal of
`𝒪_{F, z̄}`. -/
theorem exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt
    {Xs Fs : AlgebraicSpaces B S hS} (ξ : Fs ⟶ Xs)
    {z : GeometricPoint B S hS Fs.1} (N : SmallEtaleNeighborhood z)
    (Uch : SmallEtale B S hS Xs.1) (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map gNU ≫ Uch.obj.hom)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map gNU)]
    (hunr : UnramifiedAt ((BigFppfOver.toScheme B S hS).map gNU)
      (chartPoint B S hS Fs.1 N))
    (hregular : IsRegularLocalRing (chartLocalRing B S hS Fs.1 N)) :
    letI : IsLocalRing (etaleLocalRing B S hS Fs.1 z) :=
      isLocalRing_etaleLocalRing B S hS Fs.1 Fs.2 z
    ∃ t : Fin (maximalIdeal (chartLocalRing B S hS Fs.1 N)).spanFinrank →
        chartLocalRing B S hS Xs.1 (targetNeighborhood B S hS N Uch gNU hsq),
      (∀ i, t i ∈ maximalIdeal
        (chartLocalRing B S hS Xs.1 (targetNeighborhood B S hS N Uch gNU hsq))) ∧
        RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 z)
            (List.ofFn fun i => etaleLocalRingMap Fs.2 ξ.hom z
              (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2
                (targetNeighborhood B S hS N Uch gNU hsq) (t i))) ∧
          Ideal.ofList (List.ofFn fun i => etaleLocalRingMap Fs.2 ξ.hom z
              (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2
                (targetNeighborhood B S hS N Uch gNU hsq) (t i))) =
            maximalIdeal (etaleLocalRing B S hS Fs.1 z) := by
  have : IsLocalRing (etaleLocalRing B S hS Fs.1 z) :=
    isLocalRing_etaleLocalRing B S hS Fs.1 Fs.2 z
  obtain ⟨t, htmem, htreg, htspan⟩ :=
    exists_fn_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt
      ((BigFppfOver.toScheme B S hS).map gNU) (chartPoint B S hS Fs.1 N) hunr hregular
  have hlist (i) : chartLocalRingToEtaleLocalRing B S hS Fs.1 Fs.2 N
          ((((BigFppfOver.toScheme B S hS).map gNU).stalkMap
            (chartPoint B S hS Fs.1 N)).hom (t i)) =
      etaleLocalRingMap Fs.2 ξ.hom z
        (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2
          (targetNeighborhood B S hS N Uch gNU hsq) (t i)) :=
    congrArg (fun k => k (t i))
      (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS ξ z N Uch gNU hsq)
  refine ⟨t, htmem, isRegular_ofFn_etaleLocalRing_of_eq B S hS Fs.1 Fs.2 N _ _ htreg hlist, ?_⟩
  have hspan := congrArg
    (Ideal.map (chartLocalRingToEtaleLocalRing B S hS Fs.1 Fs.2 N)) htspan
  rw [Ideal.map_ofList, List.map_ofFn, Function.comp_def, funext hlist] at hspan
  exact hspan.trans (map_maximalIdeal_chartLocalRingToEtaleLocalRing B S hS Fs.1 Fs.2 N)

end AlgebraicGeometry.Space

end
