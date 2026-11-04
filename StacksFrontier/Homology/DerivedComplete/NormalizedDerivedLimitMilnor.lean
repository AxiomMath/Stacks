module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The Milnor short exact sequence of a derived limit with specified projections

Let `A` be an abelian category with exact countable products and countable inverse limits, and
let `F : ℕᵒᵖ ⥤ D(A)` be an inverse system with a derived limit `K` whose projections
`π n : K ⟶ F n` are specified, that is
`NoetherianAdicCompletion.IsDerivedLimitWithProjections F K π`. In each degree `r` the Milnor
short exact sequence

`0 ⟶ R¹lim H^{r-1}(Fₙ) ⟶ Hʳ(K) ⟶ lim Hʳ(Fₙ) ⟶ 0`

then has a *named* right-hand map: the canonical map into the limit determined by the
projections, `DerivedCategory.derivedLimitHomologyToLimit`.

`DerivedCategory.exists_milnor_shortExact_of_distTriang` already gives this sequence for a
supplied derived-limit triangle, but its right-hand map is existentially quantified and
characterized only through the structural map `K ⟶ ∏ Fₙ`. A consumer that must compare that map
with a comparison map it has built from the projections cannot do so until the map is named. The
specified projections are exactly what names it: a bare `IsDerivedLimit` pins its object only up
to non-unique isomorphism, and two defining triangles over the same object differ by an
automorphism of it — `-1`, for instance, negates the projections and hence the comparison map.

## Main definitions

* `DerivedCategory.derivedLimitHomologyCone` — the cone on `n ↦ Hʳ(Fₙ)` induced on degree-`r`
  cohomology by a family of maps into the system compatible with its transition maps.
* `DerivedCategory.derivedLimitHomologyToLimit` — the comparison map `Hʳ(K) ⟶ lim Hʳ(Fₙ)`
  determined by given projections of a derived limit.

## Main results

* `DerivedCategory.derivedLimitHomologyToLimit_comp_limit_π` — the characterizing property of the
  comparison map: its composite with the `n`-th limit projection is `Hʳ(πₙ)`.
* `DerivedCategory.exists_milnor_shortExact_of_isDerivedLimitWithProjections` — **the Milnor short
  exact sequence of a derived limit with specified projections**, with the named comparison map as
  its right-hand map, and with the inclusion still characterized by the connecting morphism of the
  defining triangle.
* `DerivedCategory.map_comp_derivedLimitHomologyToLimit` and
  `DerivedCategory.map_comp_derivedLimitHomologyToLimit_eq_limitLift` — the comparison map
  normalized against a map `X ⟶ K`: precomposed with `Hʳ` of that map it is the canonical map
  into the limit induced by the composites with the projections.

## Implementation notes

`Dualizing.completedLocalCohomologyToLimitOfProjections` and
`Dualizing.completedLocalCohomologyToLimitOfProjections_shortExact` in
`StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit` are the
specializations of these declarations to the tower `n ↦ RΓ_Z(M/IⁿM)` of Stacks 0EEW, and are
defined as such there rather than reproved.

`R¹lim` appears as the cokernel of the difference map on the product rather than through a chosen
right-derived-limit functor, which is what lets the inclusion be characterized by the connecting
morphism without an arbitrary identification. The defining triangle's third map is existentially
quantified, since `IsDerivedLimitWithProjections` quantifies it; the first map is not, being the
product of the given projections.

## References

* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]

/-- A family of maps `X ⟶ Fₙ` compatible with the transition maps of an inverse system in `D(A)`
induces, on degree-`r` cohomology, a cone on the system `n ↦ Hʳ(Fₙ)`. -/
def derivedLimitHomologyCone (F : ℕᵒᵖ ⥤ DerivedCategory A) {X : DerivedCategory A}
    (γ : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = γ n) (r : ℤ) :
    Cone (F ⋙ DerivedCategory.homologyFunctor A r) :=
  ⟨(DerivedCategory.homologyFunctor A r).obj X,
    NatTrans.ofOpSequence (G := F ⋙ DerivedCategory.homologyFunctor A r)
      (fun n ↦ (DerivedCategory.homologyFunctor A r).map (γ n)) (by
        intro n
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
          Category.id_comp]
        exact (((DerivedCategory.homologyFunctor A r).map_comp _ _).symm.trans
          (congrArg (DerivedCategory.homologyFunctor A r).map (hγ n))).symm)⟩

omit [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A] [HasLimitsOfShape ℕᵒᵖ A] in
/-- The `n`-th leg of `derivedLimitHomologyCone` is the map `Hʳ(X) ⟶ Hʳ(Fₙ)` induced by `γ n`. -/
@[simp]
theorem derivedLimitHomologyCone_π (F : ℕᵒᵖ ⥤ DerivedCategory A) {X : DerivedCategory A}
    (γ : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = γ n) (r : ℤ) (n : ℕ) :
    (derivedLimitHomologyCone F γ hγ r).π.app (Opposite.op n) =
      (DerivedCategory.homologyFunctor A r).map (γ n) :=
  rfl

/-- **The comparison map of the Milnor short exact sequence.** The map from the degree-`r`
cohomology of a derived limit `K` of an inverse system `F` in `D(A)` to the inverse limit of the
modules `Hʳ(Fₙ)`: the canonical map into the limit induced by the projections of the derived
limit.

The projections are an explicit argument. A derived limit is unique only up to non-unique
isomorphism, and two defining triangles over the same object differ by an automorphism of it —
for instance `-1`, which negates the projections and hence this map. So the projections, and not
merely the derived-limit property, are what a statement identifying this map must fix. -/
def derivedLimitHomologyToLimit (F : ℕᵒᵖ ⥤ DerivedCategory A) {K : DerivedCategory A}
    (p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = p n) (r : ℤ) :
    (DerivedCategory.homologyFunctor A r).obj K ⟶
      limit (F ⋙ DerivedCategory.homologyFunctor A r) :=
  limit.lift _ (derivedLimitHomologyCone F p hp r)

omit [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A] in
/-- **The characterizing property of the comparison map.** Its composite with the `n`-th
projection of the limit is the `n`-th projection of the derived limit, on degree-`r`
cohomology. -/
@[reassoc]
theorem derivedLimitHomologyToLimit_comp_limit_π (F : ℕᵒᵖ ⥤ DerivedCategory A)
    {K : DerivedCategory A} (p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = p n) (r : ℤ) (n : ℕ) :
    derivedLimitHomologyToLimit F p hp r ≫
        limit.π (F ⋙ DerivedCategory.homologyFunctor A r) (Opposite.op n) =
      (DerivedCategory.homologyFunctor A r).map (p n) :=
  limit.lift_π _ (Opposite.op n)

omit [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A] in
/-- **The comparison map normalized against a map into the derived limit.** For any `η : X ⟶ K`,
the comparison map precomposed with `Hʳ(η)` is *the* map into the limit whose composite with the
`n`-th limit projection is `Hʳ(η ≫ pₙ)`. -/
theorem map_comp_derivedLimitHomologyToLimit (F : ℕᵒᵖ ⥤ DerivedCategory A)
    {K : DerivedCategory A} (p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = p n) (r : ℤ)
    {X : DerivedCategory A} (η : X ⟶ K) (γ : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩)
    (c : (DerivedCategory.homologyFunctor A r).obj X ⟶
      limit (F ⋙ DerivedCategory.homologyFunctor A r))
    (hc : ∀ n : ℕ, c ≫ limit.π (F ⋙ DerivedCategory.homologyFunctor A r) (Opposite.op n) =
      (DerivedCategory.homologyFunctor A r).map (γ n))
    (hη : ∀ n : ℕ, η ≫ p n = γ n) :
    (DerivedCategory.homologyFunctor A r).map η ≫ derivedLimitHomologyToLimit F p hp r = c := by
  refine limit.hom_ext fun j ↦ ?_
  obtain ⟨n⟩ := j
  rw [Category.assoc, derivedLimitHomologyToLimit_comp_limit_π, hc n,
    ← (DerivedCategory.homologyFunctor A r).map_comp, hη]

omit [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A] in
/-- **The comparison map normalized against a map into the derived limit**, with the map into the
limit written as the lift of the cone of the composites `η ≫ pₙ`. -/
theorem map_comp_derivedLimitHomologyToLimit_eq_limitLift (F : ℕᵒᵖ ⥤ DerivedCategory A)
    {K : DerivedCategory A} (p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = p n) (r : ℤ)
    {X : DerivedCategory A} (η : X ⟶ K) (γ : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = γ n)
    (hη : ∀ n : ℕ, η ≫ p n = γ n) :
    (DerivedCategory.homologyFunctor A r).map η ≫ derivedLimitHomologyToLimit F p hp r =
      limit.lift _ (derivedLimitHomologyCone F γ hγ r) :=
  map_comp_derivedLimitHomologyToLimit F p hp r η γ _
    (fun n ↦ limit.lift_π (derivedLimitHomologyCone F γ hγ r) (Opposite.op n)) hη

/-- **The Milnor short exact sequence of a derived limit with specified projections.** For an
inverse system `F` in `D(A)` and a derived limit `K` of it with specified projections `p`, the
degree-`r` cohomology `Hʳ(K)` sits in a short exact sequence between the first derived limit
`R¹lim H^{r-1}(Fₙ)`, presented as the cokernel of one minus shift, and the inverse limit
`lim Hʳ(Fₙ)`. The right-hand map is the named comparison map
`DerivedCategory.derivedLimitHomologyToLimit` determined by the projections, and the inclusion
descends the connecting morphism of the defining triangle through that cokernel.

This is `DerivedCategory.exists_milnor_shortExact_of_distTriang` with the structural map taken to
be the product of the given projections, which is what identifies its existentially quantified
right-hand map with the named comparison map. -/
theorem exists_milnor_shortExact_of_isDerivedLimitWithProjections
    (F : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K : DerivedCategory A} (p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hK : NoetherianAdicCompletion.IsDerivedLimitWithProjections F K p) (r : ℤ) :
    let X : ℕ → DerivedCategory A := fun n ↦ F.obj (Opposite.op n)
    let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
      Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    let H := DerivedCategory.homologyFunctor A r
    let H₁ := DerivedCategory.homologyFunctor A (r - 1)
    let P : A := ∏ᶜ fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)
    let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) (n + 1) ≫
          (F ⋙ H₁).map (homOfLE (Nat.le_succ n)).op
    let q := derivedLimitHomologyToLimit F p
      (NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_map_succ hK) r
    ∃ b : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
      let T := Triangle.mk (Pi.lift p) d b
      T ∈ distTriang (DerivedCategory A) ∧
        ∃ (e : H₁.obj (∏ᶜ X) ≅ P) (i : cokernel δ ⟶ H.obj K) (w : i ≫ q = 0),
          e.hom = piComparison H₁ X ∧
            cokernel.π δ ≫ i = e.inv ≫ DerivedCategory.HomologySequence.δ T (r - 1) r ∧
              (ShortComplex.mk i q w).ShortExact := by
  have hK' := hK
  obtain ⟨b, hb⟩ := hK'
  refine ⟨b, hb, ?_⟩
  obtain ⟨e, i, q', w, he, hi, hq, hse⟩ :=
    exists_milnor_shortExact_of_distTriang F K (Pi.lift p) b hb r
  have hqeq : q' = derivedLimitHomologyToLimit F p
      (NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_map_succ hK) r := by
    refine limit.hom_ext fun j ↦ ?_
    obtain ⟨n⟩ := j
    rw [hq n, derivedLimitHomologyToLimit_comp_limit_π,
      ← (DerivedCategory.homologyFunctor A r).map_comp]
    simp
  exact ⟨e, i, hqeq ▸ w, he, hi, hqeq ▸ hse⟩

end DerivedCategory

end
