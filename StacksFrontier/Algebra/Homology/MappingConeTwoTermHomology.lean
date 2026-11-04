module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksCore.Tactic.StacksAttribute

/-!
# The cone of a map of two-term complexes which is invertible in degree `0`

Let `g : L ⟶ M` be a morphism of cochain complexes in an abelian category with `L` zero in
degree `1` and `M` zero in degree `-2` — for instance a morphism of two-term complexes
concentrated in degrees `-1` and `0` — and suppose that `g` is an **isomorphism in degree `0`**.
Mathlib's mapping cone has `C(g)^n = L^{n+1} ⊕ M^n` with differential
`(l, m) ↦ (-d_L l, g l + d_M m)` (`CochainComplex.mappingCone.inl_v_d` and `inr_f_d`), so in
degrees `-2, -1, 0` the cone reads

`L^{-1} ⟶ L^0 ⊕ M^{-1} ⟶ M^0`.

Its cycles in degree `-1` are the pairs with `g l + d_M m = 0`, and since `g` is invertible in
degree `0` such a pair is determined by its second component: the second projection identifies
the cycles with `M^{-1}`, and carries the boundaries onto the image of `g` in degree `-1`.  So

`H^{-1}(C(g)) ≅ coker (g^{-1} : L^{-1} ⟶ M^{-1})`.

This is the computation that reduces the comparison of `NL_{B/A} ⊗_B C` with the shifted cone of
Stacks 0E1Y in degree `0` to a statement about one cokernel; the canonical map `g` of that tag
is invertible in degree `0` by
`Stacks.SheafOfModules.isIso_spaceRelativeNaiveCotangentComplexMap_zero`.

## Main definitions

* `CochainComplex.mappingCone.coneCycleι`: the identification of `M^{-1}` with the cycles of the
  cone in degree `-1`, as a map to `C(g)^{-1}`.
* `CochainComplex.mappingCone.twoTermLeftHomologyData`: the left homology data of the short
  complex of the cone in degree `-1` whose homology object is `coker (g^{-1})`.
* `CochainComplex.mappingCone.homologyNegOneIsoCokernel`: **the resulting identification
  `H^{-1}(C(g)) ≅ coker (g^{-1})`.**
* `CochainComplex.mappingCone.shiftedHomologyZeroIsoCokernel`: the same read through the shift,
  `H⁰(C(g)[-1]) ≅ coker (g^{-1})`, which is the degree the canonical map of Stacks 0E1Y to the
  shifted cone is compared in.
* `CochainComplex.toHomologyZero`: the canonical epimorphism `P^0 ⟶ H⁰(P)` of a cochain complex
  vanishing in degree `1`, through which `H⁰(P)` is the cokernel of `d_P^{-1}`.
* `CochainComplex.homologyZeroLeftHomologyData` and
  `CochainComplex.homologyZeroIsoCokernel`: the left homology data of `P.sc' (-1) 0 1` whose
  homology object is `coker (d_P^{-1})`, and the resulting identification
  `H⁰(P) ≅ coker (d_P^{-1})`.
* `CochainComplex.mappingCone.shiftedSndZero`: the degree `0` component of a morphism into the
  shifted cone, read against the second projection of the cone.

## Main results

* `CochainComplex.mappingCone.decomp_comp_d`: the differential of the cone out of degree `-1`,
  read on a decomposed morphism into `C(g)^{-1} = L^0 ⊕ M^{-1}`.
* `CochainComplex.mappingCone.coneCycleι_comp_d`: the identification lands in the cycles.
* `CochainComplex.mappingCone.coneCycleι_liftK`: a cycle of the cone in degree `-1` is the image
  of its second component, which is what makes the identification a kernel of the differential.
* `CochainComplex.mappingCone.toHomologyZero_comp_homologyMap_comp_shiftedHomologyZeroIsoCokernel`:
  **a morphism `c : P ⟶ C(g)[-1]` out of a complex vanishing in degree `1`, read on `H⁰` against
  the identification with `coker (g^{-1})`, is the map on cokernels induced by
  `CochainComplex.mappingCone.shiftedSndZero`** — for the canonical map of Stacks 0E1Y, by the
  degree `-1` component of its null homotopy.  With
  `CochainComplex.epi_toHomologyZero` and
  `CochainComplex.mappingCone.d_comp_shiftedSndZero` this determines `H⁰(c)`, and it is the step
  that turns `IsIso (H⁰ c)` into a statement about one commutative square with no cone, no shift
  and no connecting morphism in it.
* `CochainComplex.toHomologyZero_comp_homologyZeroIsoCokernel`: the canonical epimorphism
  `P^0 ⟶ H⁰(P)` *is* the cokernel projection onto `coker (d_P^{-1})`, not merely an epimorphism
  killing the boundaries.
* `CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`: **for the
  factorisation of Stacks 08RI (2) there is no sign** — the degree `0` component of
  `CochainComplex.factorThroughShiftedMappingCone f g H`, read against the second projection of
  the cone, is the null homotopy `H` in bidegree `(0, -1)` exactly.
* `CochainComplex.mappingCone.homologyMap_zero_eq_cokernelDesc` and
  `CochainComplex.mappingCone.isIso_homologyMap_zero_iff`: **`H⁰(c)` read through the two
  cokernel identifications is literally `cokernel.desc` of
  `CochainComplex.mappingCone.shiftedSndZero`, and it is an isomorphism exactly when that
  morphism of cokernels is.**  For the canonical map of Stacks 0E1Y this is the whole reduction:
  `IsIso (H⁰ c)` becomes invertibility of the map
  `coker (d_{NL_{B/A} ⊗ C}^{-1}) ⟶ coker (g^{-1})` induced by the degree `-1` component of the
  null homotopy of the proof.

## Implementation notes

Everything is written with the two inclusions `inl` and `inr` rather than the two projections
`fst` and `snd`, and morphisms into `C(g)^{-1}` are decomposed with
`CochainComplex.mappingCone.decomp_to` before anything is proved about them.  The reason is that
`CochainComplex.mappingCone.fst` is a `Cocycle`, so a statement mentioning it carries a coercion
out of a subtype, and an expression in which that coercion meets a composite is not type-correct
at `implicit` transparency: `rw` and `simp` then refuse to act on it.  The one place where `fst`
is unavoidable — the identification of the induced map `f'` with `g` in degree `-1`, where the
epimorphism needed by `CategoryTheory.Limits.isCokernelEpiComp` is the first projection — is
proved by a `congrArg` chain rather than by rewriting.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the consumer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open CategoryTheory.Preadditive

universe v u

namespace CochainComplex.mappingCone

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {L M : CochainComplex 𝒜 ℤ} (g : L ⟶ M)

/-- The right inclusion of the cone is a monomorphism in every degree, being split. -/
theorem mono_inr_f (n : ℤ) : Mono ((inr g).f n) :=
  mono_of_mono_fac (inr_f_snd_v g n)

/-- The first projection of the cone is an epimorphism, being split. -/
theorem epi_fst_v (p q : ℤ) (hpq : q + 1 = p) : Epi ((fst g).1.v q p hpq) :=
  epi_of_epi_fac (inl_v_fst_v g p q hpq)

/-- **The differential of the cone out of degree `-1`, on a decomposed morphism.**  A morphism
into `C(g)^{-1} = L^0 ⊕ M^{-1}` with components `a` and `b` is carried by the differential to
`a ≫ g + b ≫ d_M`, read in `M^0` — the `L^1`-component of the differential vanishing because
`L` is zero in degree `1`. -/
theorem decomp_comp_d (hL : IsZero (L.X 1)) {A : 𝒜} (a : A ⟶ L.X 0) (b : A ⟶ M.X (-1)) :
    (a ≫ (inl g).v 0 (-1) (by norm_num) + b ≫ (inr g).f (-1)) ≫ (mappingCone g).d (-1) 0 =
      (a ≫ g.f 0 + b ≫ M.d (-1) 0) ≫ (inr g).f 0 := by
  rw [add_comp, assoc, assoc, inl_v_d g 0 (-1) 1 (by norm_num) (by norm_num), inr_f_d,
    hL.eq_of_tgt (L.d 0 1) 0, zero_comp, sub_zero, add_comp, assoc, assoc]

/-- **The differential of the cone into degree `-1`, read on the second component**, is `g` in
degree `-1` precomposed with the first projection — the `M^{-2}`-term of the differential
vanishing because `M` is zero in degree `-2`.  This is the morphism whose cokernel the homology
of the cone in degree `-1` is. -/
theorem twoTermInducedMap (hM : IsZero (M.X (-2))) :
    (mappingCone g).d (-2) (-1) ≫ (snd g).v (-1) (-1) (add_zero _) =
      (fst g).1.v (-2) (-1) (by norm_num) ≫ g.f (-1) :=
  (d_snd_v g (-2) (-1) (by norm_num)).trans
    ((congrArg (fun t => (fst g).1.v (-2) (-1) (by norm_num) ≫ g.f (-1) + t)
      (show (snd g).v (-2) (-2) (add_zero _) ≫ M.d (-2) (-1) = 0 by
        rw [hM.eq_of_tgt ((snd g).v (-2) (-2) (add_zero _)) 0, zero_comp])).trans (add_zero _))

section TwoTerm

variable [IsIso (g.f 0)]

/-- **The cycles of the cone in degree `-1`, as a morphism out of `M^{-1}`.**  A cycle of
`C(g)^{-1} = L^0 ⊕ M^{-1}` is a pair `(l, m)` with `g l + d_M m = 0`, so when `g` is invertible
in degree `0` it is `(-g⁻¹ (d_M m), m)`. -/
noncomputable def coneCycleι : M.X (-1) ⟶ (mappingCone g).X (-1) :=
  (-(M.d (-1) 0 ≫ inv (g.f 0))) ≫ (inl g).v 0 (-1) (by norm_num) + (inr g).f (-1)

/-- The second component of `coneCycleι g` is the identity of `M^{-1}`. -/
@[reassoc (attr := simp)]
theorem coneCycleι_snd :
    coneCycleι g ≫ (snd g).v (-1) (-1) (add_zero _) = 𝟙 _ := by
  simp [coneCycleι]

/-- The morphism `coneCycleι g : M^{-1} ⟶ C(g)^{-1}` is a monomorphism. -/
theorem mono_coneCycleι : Mono (coneCycleι g) :=
  mono_of_mono_fac (coneCycleι_snd g)

attribute [local instance] mono_coneCycleι

/-- **The identification lands in the cycles**: the composite with the differential of the cone
vanishes, by the choice of the first component. -/
theorem coneCycleι_comp_d (hL : IsZero (L.X 1)) :
    coneCycleι g ≫ (mappingCone g).d (-1) 0 = 0 := by
  have h := decomp_comp_d g hL (-(M.d (-1) 0 ≫ inv (g.f 0))) (𝟙 _)
  simp only [id_comp] at h
  simp only [coneCycleι]
  rw [h]
  simp

/-- **A cycle of the cone in degree `-1` is the image of its second component.**  This is what
makes `CochainComplex.mappingCone.coneCycleι` a kernel of the differential. -/
theorem coneCycleι_liftK (hL : IsZero (L.X 1)) {A : 𝒜} (k : A ⟶ (mappingCone g).X (-1))
    (hk : k ≫ (mappingCone g).d (-1) 0 = 0) :
    (k ≫ (snd g).v (-1) (-1) (add_zero _)) ≫ coneCycleι g = k := by
  obtain ⟨a, b, rfl⟩ := decomp_to g k 0 (by norm_num)
  have hb : (a ≫ (inl g).v 0 (-1) (by norm_num) + b ≫ (inr g).f (-1)) ≫
      (snd g).v (-1) (-1) (add_zero _) = b := by
    simp
  have hcyc : a ≫ g.f 0 + b ≫ M.d (-1) 0 = 0 := by
    have hmono := mono_inr_f g 0
    rw [← cancel_mono ((inr g).f 0), zero_comp, ← decomp_comp_d g hL a b]
    exact hk
  have hbd : b ≫ M.d (-1) 0 = -(a ≫ g.f 0) := eq_neg_of_add_eq_zero_right hcyc
  have ha : b ≫ (-(M.d (-1) 0 ≫ inv (g.f 0))) = a := by
    rw [comp_neg, ← assoc, hbd, neg_comp, neg_neg, assoc, IsIso.hom_inv_id, comp_id]
  rw [hb, coneCycleι, comp_add, ← assoc, ha]

/-- **The left homology data of the short complex of the cone in degree `-1` whose homology
object is the cokernel of `g` in degree `-1`.**

It carries `@[implicit_reducible]` so that its `K`, `H`, `i` and `π` fields reduce to the
morphisms written below even at `implicit` transparency: a consumer comparing it with another
left homology data has to rewrite under an equation whose type mentions `H`, and `rw` checks
type-correctness at that transparency. -/
@[implicit_reducible]
noncomputable def twoTermLeftHomologyData (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2))) :
    ((mappingCone g).sc' (-2) (-1) 0).LeftHomologyData where
  K := M.X (-1)
  H := cokernel (g.f (-1))
  i := coneCycleι g
  π := cokernel.π _
  wi := coneCycleι_comp_d g hL
  hi := KernelFork.IsLimit.ofι' (coneCycleι g) (coneCycleι_comp_d g hL) fun k hk =>
    ⟨k ≫ (snd g).v (-1) (-1) (add_zero _), coneCycleι_liftK g hL k hk⟩
  wπ := by
    change ((mappingCone g).d (-2) (-1) ≫ (snd g).v (-1) (-1) (add_zero _)) ≫ cokernel.π _ = 0
    rw [twoTermInducedMap g hM, assoc, cokernel.condition, comp_zero]
  hπ := by
    haveI := epi_fst_v g (-1) (-2) (by norm_num)
    refine isCokernelEpiComp (cokernelIsCokernel (g.f (-1)))
      ((fst g).1.v (-2) (-1) (by norm_num)) ?_
    refine Eq.trans ?_ (twoTermInducedMap g hM)
    rfl

/-- **`H^{-1}` of the cone of a morphism of two-term complexes which is invertible in degree `0`
is the cokernel of that morphism in degree `-1`.** -/
noncomputable def homologyNegOneIsoCokernel (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2))) :
    (mappingCone g).homology (-1) ≅ cokernel (g.f (-1)) :=
  ((mappingCone g).homologyIsoSc' (-2) (-1) 0 (by rw [CochainComplex.prev]; omega)
      (by rw [CochainComplex.next]; omega)).trans
    (twoTermLeftHomologyData g hL hM).homologyIso

/-- **`H⁰` of the shifted cone of a morphism of two-term complexes which is invertible in degree
`0` is the cokernel of that morphism in degree `-1`.**  This is
`CochainComplex.mappingCone.homologyNegOneIsoCokernel` read through the shift, for which the
identification is `CochainComplex.shiftedMappingConeHomologyIso`.  It is the degree in which the
canonical map of Stacks 0E1Y to the shifted cone is to be compared. -/
noncomputable def shiftedHomologyZeroIsoCokernel (hL : IsZero (L.X 1))
    (hM : IsZero (M.X (-2))) :
    ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
        (mappingCone g)).homology 0 ≅ cokernel (g.f (-1)) :=
  (CochainComplex.shiftedMappingConeHomologyIso g 0 (-1) (by omega)).trans
    (homologyNegOneIsoCokernel g hL hM)

end TwoTerm

end CochainComplex.mappingCone

/-! ## `H⁰` of a complex that vanishes in degree `1` -/

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Every degree `0` element of a complex vanishing in degree `1` is a cycle, so the canonical
morphism `P^0 ⟶ Z^0(P)` is invertible. -/
instance isIso_liftCycles_id (P : CochainComplex 𝒜 ℤ) (hP : IsZero (P.X 1)) :
    IsIso (P.liftCycles (𝟙 (P.X 0)) 1 (by rw [CochainComplex.next]; omega)
      (by rw [Category.id_comp]; exact hP.eq_of_tgt (P.d 0 1) 0)) :=
  ⟨P.iCycles 0, HomologicalComplex.liftCycles_i _ _ _ _ _, by
    rw [← cancel_mono (P.iCycles 0), Category.assoc, HomologicalComplex.liftCycles_i,
      Category.comp_id, Category.id_comp]⟩

/-- **The canonical epimorphism `P^0 ⟶ H⁰(P)` of a complex vanishing in degree `1`.**  Since
every degree `0` element of such a complex is a cycle, `H⁰(P)` is a quotient of `P^0`, and this
is the quotient map; `CochainComplex.epi_toHomologyZero` records that it is an epimorphism and
`CochainComplex.d_comp_toHomologyZero` that it kills the boundaries, so that `H⁰(P)` is the
cokernel of `d_P^{-1}` read through it. -/
noncomputable def toHomologyZero (P : CochainComplex 𝒜 ℤ) (hP : IsZero (P.X 1)) :
    P.X 0 ⟶ P.homology 0 :=
  P.liftCycles (𝟙 (P.X 0)) 1 (by rw [CochainComplex.next]; omega) (by
    rw [Category.id_comp]; exact hP.eq_of_tgt (P.d 0 1) 0) ≫ P.homologyπ 0

/-- The map `P^0 ⟶ H⁰(P)` of a complex vanishing in degree `1` is an epimorphism. -/
instance epi_toHomologyZero (P : CochainComplex 𝒜 ℤ) (hP : IsZero (P.X 1)) :
    Epi (P.toHomologyZero hP) := by
  have := P.isIso_liftCycles_id hP
  exact epi_comp (P.liftCycles (𝟙 (P.X 0)) 1 (by rw [CochainComplex.next]; omega) (by
    rw [Category.id_comp]; exact hP.eq_of_tgt (P.d 0 1) 0)) (P.homologyπ 0)

/-- **The canonical epimorphism `P^0 ⟶ H⁰(P)` kills the boundaries.** -/
@[reassoc (attr := simp)]
theorem d_comp_toHomologyZero (P : CochainComplex 𝒜 ℤ) (hP : IsZero (P.X 1)) :
    P.d (-1) 0 ≫ P.toHomologyZero hP = 0 := by
  rw [toHomologyZero, ← Category.assoc, HomologicalComplex.comp_liftCycles]
  exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary P
    (P.d (-1) 0 ≫ 𝟙 (P.X 0)) 1 (by rw [CochainComplex.next]; omega) (𝟙 (P.X (-1)))
    (by rw [Category.id_comp, Category.comp_id])

/-- **The left homology data of `P.sc' (-1) 0 1` whose homology object is the cokernel of
`d_P^{-1}`.**  For a complex vanishing in degree `1` the cycles in degree `0` are all of `P^0`, so
the inclusion of cycles may be taken to be the identity and the homology object is then literally
`coker (d_P^{-1})`. -/
@[implicit_reducible]
noncomputable def homologyZeroLeftHomologyData (P : CochainComplex 𝒜 ℤ) (hP : IsZero (P.X 1)) :
    (P.sc' (-1) 0 1).LeftHomologyData where
  K := P.X 0
  H := cokernel (P.d (-1) 0)
  i := 𝟙 _
  π := cokernel.π _
  wi := hP.eq_of_tgt _ _
  hi := KernelFork.IsLimit.ofι' (𝟙 _) (hP.eq_of_tgt _ _) fun k _ => ⟨k, Category.comp_id k⟩
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

/-- **`H⁰` of a complex vanishing in degree `1` is the cokernel of its differential into degree
`0`.**  The compatibility with `CochainComplex.toHomologyZero` is
`CochainComplex.toHomologyZero_comp_homologyZeroIsoCokernel`. -/
noncomputable def homologyZeroIsoCokernel (P : CochainComplex 𝒜 ℤ) (hP : IsZero (P.X 1)) :
    P.homology 0 ≅ cokernel (P.d (-1) 0) :=
  (P.homologyIsoSc' (-1) 0 1 (by rw [CochainComplex.prev]; omega)
      (by rw [CochainComplex.next]; omega)).trans
    (homologyZeroLeftHomologyData P hP).homologyIso

/-- A cycle `x`, followed by `homologyπ` and the identification of the homology with the
object of a left homology data `h`, is `l ≫ h.π` for any lift `l` of `x` through `h.i`. -/
private theorem liftCycles_homologyπ_homologyIsoSc'_trans_hom {C : CochainComplex 𝒜 ℤ}
    {i j k : ℤ} (hi : (ComplexShape.up ℤ).prev j = i)
    (hk : (ComplexShape.up ℤ).next j = k) (h : (C.sc' i j k).LeftHomologyData)
    {A : 𝒜} (x : A ⟶ C.X j) (k' : ℤ) (hk' : (ComplexShape.up ℤ).next j = k')
    (hx : x ≫ C.d j k' = 0) (l : A ⟶ h.K) (hl : l ≫ h.i = x) :
    C.liftCycles x k' hk' hx ≫ C.homologyπ j ≫
        ((C.homologyIsoSc' i j k hi hk).trans h.homologyIso).hom = l ≫ h.π := by
  rw [Iso.trans_hom, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, ← Category.assoc,
    ← Category.assoc]
  refine congrArg (· ≫ h.π) ?_
  rw [← cancel_mono h.i, Category.assoc, Category.assoc,
    ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles, hl]
  exact HomologicalComplex.liftCycles_i C x k' hk' hx

/-- **The canonical epimorphism `P^0 ⟶ H⁰(P)` is the projection onto `coker (d_P^{-1})`.**
Together with `CochainComplex.homologyZeroIsoCokernel` this says that `P^0 ⟶ H⁰(P)` *is* a
cokernel of `d_P^{-1}`, not merely an epimorphism killing the boundaries. -/
@[reassoc]
theorem toHomologyZero_comp_homologyZeroIsoCokernel (P : CochainComplex 𝒜 ℤ)
    (hP : IsZero (P.X 1)) :
    P.toHomologyZero hP ≫ (homologyZeroIsoCokernel P hP).hom = cokernel.π (P.d (-1) 0) := by
  rw [toHomologyZero, homologyZeroIsoCokernel, Category.assoc]
  refine (liftCycles_homologyπ_homologyIsoSc'_trans_hom _ _ (homologyZeroLeftHomologyData P hP)
    _ _ _ _ (𝟙 (P.X 0)) ?_).trans (Category.id_comp _)
  exact Category.comp_id _

end CochainComplex

/-! ## The canonical map into the shifted cone, read on `H⁰` -/

namespace CochainComplex.mappingCone

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {L M : CochainComplex 𝒜 ℤ} (g : L ⟶ M)

variable {P : CochainComplex 𝒜 ℤ}
  (c : P ⟶ (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj (mappingCone g))

/-- **The degree `0` component of a morphism into the shifted cone, read against the second
projection of the cone.**  For the canonical map of Stacks 0E1Y this is exactly the degree `-1`
component of its null homotopy, with no sign:
`CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`. -/
noncomputable def shiftedSndZero : P.X 0 ⟶ M.X (-1) :=
  c.f 0 ≫ ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom ≫
    (snd g).v (-1) (-1) (add_zero _)

/-- **For the factorisation of Stacks 08RI (2) there is no sign.**  The degree `0` component of
`CochainComplex.factorThroughShiftedMappingCone f g H`, read against the second projection of the
cone, is the null homotopy `H` in its bidegree `(0, -1)`.

This is `CochainComplex.factorThroughShiftedMappingCone_comp_snd`, which states the same thing as
an equality of cochains of degree `-1`, read in the single bidegree the statement above is about:
the left shift by `-1` of a cochain of degree `0` carries the sign
`(a * n' + a * (a - 1) / 2).negOnePow` of `CochainComplex.HomComplex.Cochain.leftShift_v`, which
at `a = n' = -1` is `(2 : ℤ).negOnePow = 1`.  So for the canonical map of Stacks 0E1Y
`CochainComplex.mappingCone.shiftedSndZero` *is* the degree `-1` component of its null homotopy,
with no sign to carry through
`CochainComplex.mappingCone.toHomologyZero_comp_homologyMap_comp_shiftedHomologyZeroIsoCokernel`.
-/
theorem shiftedSndZero_factorThroughShiftedMappingCone (f : P ⟶ L)
    (H : Homotopy (f ≫ g) 0) :
    shiftedSndZero g (factorThroughShiftedMappingCone f g H) = H.hom 0 (-1) := by
  have h := congrArg (fun z : CochainComplex.HomComplex.Cochain P M (-1) =>
    z.v 0 (-1) (by omega)) (factorThroughShiftedMappingCone_comp_snd f g H)
  rw [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.leftShift_v (snd g) (-1) (-1) (by omega) 0 (-1)
      (by omega) (-1) (add_zero _)] at h
  rw [shiftedSndZero]
  refine Eq.trans ?_ h
  rw [show ((-1 : ℤ) * (-1) + (-1) * ((-1) - 1) / 2) = 2 by norm_num,
    show ((2 : ℤ).negOnePow) = 1 by decide, one_smul]

/-- **The composite `P^{-1} ⟶ P^0 ⟶ M^{-1}` lands in the image of `g` in degree `-1`.**  It is
minus the first component of `c` in degree `-1` followed by `g`, by the two-term form
`CochainComplex.mappingCone.twoTermInducedMap` of the differential of the cone into degree
`-1`. -/
theorem d_comp_shiftedSndZero (hM : IsZero (M.X (-2))) :
    P.d (-1) 0 ≫ shiftedSndZero g c =
      -((c.f (-1) ≫ ((mappingCone g).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).hom ≫
        (fst g).1.v (-2) (-1) (by omega)) ≫ g.f (-1)) := by
  have hd : ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
        (mappingCone g)).d (-1) 0 ≫
      ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom =
      -(((mappingCone g).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).hom ≫
        (mappingCone g).d (-2) (-1)) := by
    rw [CochainComplex.shiftFunctor_obj_d']
    simp [HomologicalComplex.XIsoOfEq]
  calc P.d (-1) 0 ≫ shiftedSndZero g c
      = (P.d (-1) 0 ≫ c.f 0) ≫
          ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom ≫
            (snd g).v (-1) (-1) (add_zero _) := by
        rw [shiftedSndZero, Category.assoc]
    _ = c.f (-1) ≫ (((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
            (mappingCone g)).d (-1) 0 ≫
          ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom) ≫
            (snd g).v (-1) (-1) (add_zero _) := by
        rw [← c.comm (-1) 0]
        simp only [Category.assoc]
    _ = c.f (-1) ≫ (-(((mappingCone g).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).hom ≫
            (mappingCone g).d (-2) (-1))) ≫ (snd g).v (-1) (-1) (add_zero _) := by
        rw [hd]
    _ = -(c.f (-1) ≫ ((mappingCone g).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).hom ≫
            ((mappingCone g).d (-2) (-1) ≫ (snd g).v (-1) (-1) (add_zero _))) := by
        simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
    _ = -((c.f (-1) ≫ ((mappingCone g).shiftFunctorObjXIso (-1) (-1) (-2) (by omega)).hom ≫
            (fst g).1.v (-2) (-1) (by omega)) ≫ g.f (-1)) := by
        rw [twoTermInducedMap g hM]
        simp only [Category.assoc]

/-- **`CochainComplex.mappingCone.shiftedSndZero` kills the boundaries of `P` modulo the image of
`g` in degree `-1`**, so it descends to a morphism `coker (d_P^{-1}) ⟶ coker (g^{-1})`.  This is
`CochainComplex.mappingCone.d_comp_shiftedSndZero` followed by the cokernel projection. -/
@[reassoc]
theorem d_comp_shiftedSndZero_comp_π (hM : IsZero (M.X (-2))) :
    P.d (-1) 0 ≫ shiftedSndZero g c ≫ cokernel.π (g.f (-1)) = 0 := by
  rw [← Category.assoc, d_comp_shiftedSndZero g c hM, Preadditive.neg_comp, Category.assoc,
    cokernel.condition, comp_zero, neg_zero]

/-- **The cycle condition in degree `0` of the shifted cone, transported to degree `-1` of the
cone.**  The differential of the shifted complex is minus that of the cone, reindexed, so the two
conditions agree. -/
theorem shiftedCycle_comp_d {A : 𝒜}
    (f : A ⟶ ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
      (mappingCone g)).X 0)
    (hf : f ≫ ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
      (mappingCone g)).d 0 1 = 0) :
    (f ≫ ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom) ≫
      (mappingCone g).d (-1) 0 = 0 := by
  have hd : ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom ≫
      (mappingCone g).d (-1) 0 =
      -(((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
          (mappingCone g)).d 0 1 ≫
        ((mappingCone g).shiftFunctorObjXIso (-1) 1 0 (by omega)).hom) := by
    rw [CochainComplex.shiftFunctor_obj_d']
    simp [HomologicalComplex.XIsoOfEq]
  rw [Category.assoc, hd, Preadditive.comp_neg, ← Category.assoc, hf, zero_comp, neg_zero]

/-- **The identification `H⁰(C(g)[-1]) ≅ H^{-1}(C(g))` of the shift, read on a cycle.**  This is
Mathlib's `CochainComplex.liftCycles_shift_homologyπ` with its type written through
`CochainComplex.shiftedMappingConeHomologyIso`: the lemma itself states the identification as
`CategoryTheory.Functor.shiftIso ... .inv.app`, a spelling which is only definitionally that
isomorphism, and a composite in which the two meet is not type-correct at `implicit`
transparency, so `rw` refuses to act on it.  Restating it here fixes the spelling once. -/
@[reassoc]
theorem liftCycles_homologyπ_shift {A : 𝒜}
    (f : A ⟶ ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
      (mappingCone g)).X 0)
    (hf : f ≫ ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
      (mappingCone g)).d 0 1 = 0) :
    ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
          (mappingCone g)).liftCycles f 1 (by rw [CochainComplex.next]; omega) hf ≫
        ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj
          (mappingCone g)).homologyπ 0 =
      (mappingCone g).liftCycles
          (f ≫ ((mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) (by omega)).hom) 0
          (by rw [CochainComplex.next]; omega) (shiftedCycle_comp_d g f hf) ≫
        (mappingCone g).homologyπ (-1) ≫
          (CochainComplex.shiftedMappingConeHomologyIso g 0 (-1) (by omega)).inv :=
  CochainComplex.liftCycles_shift_homologyπ (mappingCone g) f 1
    (by rw [CochainComplex.next]; omega) hf (-1) (by omega) 0
    (by rw [CochainComplex.next]; omega)

section TwoTermCompare

variable [IsIso (g.f 0)]

/-- **`H^{-1}` of the cone, read on a cycle against the identification with the cokernel.**  A
cycle of the cone in degree `-1` has, as its class in `coker (g^{-1})`, the class of its second
component. -/
theorem liftCycles_homologyπ_comp_homologyNegOneIsoCokernel (hL : IsZero (L.X 1))
    (hM : IsZero (M.X (-2))) {A : 𝒜} (k : A ⟶ (mappingCone g).X (-1))
    (hk : k ≫ (mappingCone g).d (-1) 0 = 0) :
    (mappingCone g).liftCycles k 0 (by rw [CochainComplex.next]; omega) hk ≫
        (mappingCone g).homologyπ (-1) ≫ (homologyNegOneIsoCokernel g hL hM).hom =
      (k ≫ (snd g).v (-1) (-1) (add_zero _)) ≫ cokernel.π (g.f (-1)) := by
  rw [homologyNegOneIsoCokernel]
  exact CochainComplex.liftCycles_homologyπ_homologyIsoSc'_trans_hom _ _
    (twoTermLeftHomologyData g hL hM) k _ _ _ (k ≫ (snd g).v (-1) (-1) (add_zero _))
    (coneCycleι_liftK g hL k hk)

/-- **The canonical map into the shifted cone, read on `H⁰` against the identification
`H⁰(C(g)[-1]) ≅ coker (g^{-1})`.**  On the canonical epimorphism `P^0 ⟶ H⁰(P)` of a complex `P`
vanishing in degree `1`, the induced map `H⁰(P) ⟶ H⁰(C(g)[-1]) ≅ coker (g^{-1})` is the degree
`0` component of `c` read against the second projection of the cone, followed by the projection
onto the cokernel.

Since `CochainComplex.toHomologyZero` is an epimorphism this determines `H⁰(c)` read through the
identification, and with `CochainComplex.mappingCone.d_comp_shiftedSndZero` it says that `H⁰(c)`
is the map `coker (d_P^{-1}) ⟶ coker (g^{-1})` induced by
`CochainComplex.mappingCone.shiftedSndZero` — which for the canonical map of Stacks 0E1Y is the
degree `-1` component of its null homotopy.  This is the step that turns `IsIso (H⁰ c)` into a
statement about one commutative square: no cone, no shift and no connecting morphism occur on the
right-hand side. -/
theorem toHomologyZero_comp_homologyMap_comp_shiftedHomologyZeroIsoCokernel
    (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2))) (hP : IsZero (P.X 1)) :
    P.toHomologyZero hP ≫ HomologicalComplex.homologyMap c 0 ≫
        (shiftedHomologyZeroIsoCokernel g hL hM).hom =
      shiftedSndZero g c ≫ cokernel.π (g.f (-1)) := by
  rw [CochainComplex.toHomologyZero, Category.assoc,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    shiftedHomologyZeroIsoCokernel, Iso.trans_hom, liftCycles_homologyπ_shift_assoc,
    Iso.inv_hom_id_assoc, liftCycles_homologyπ_comp_homologyNegOneIsoCokernel,
    shiftedSndZero]
  simp only [Category.id_comp, Category.assoc]

/-- **`H⁰(c)` is the morphism of cokernels induced by
`CochainComplex.mappingCone.shiftedSndZero`.**  Read through the identification
`CochainComplex.homologyZeroIsoCokernel` of `H⁰(P)` with `coker (d_P^{-1})` and the
identification `CochainComplex.mappingCone.shiftedHomologyZeroIsoCokernel` of `H⁰(C(g)[-1])` with
`coker (g^{-1})`, the map induced by `c` on `H⁰` *is* `cokernel.desc` of the degree `0` component
of `c` read against the second projection of the cone.

This is
`CochainComplex.mappingCone.toHomologyZero_comp_homologyMap_comp_shiftedHomologyZeroIsoCokernel`
with the epimorphism `P^0 ⟶ H⁰(P)` recognised as the cokernel projection it is
(`CochainComplex.toHomologyZero_comp_homologyZeroIsoCokernel`).  It is the final formal step of
the reduction: `IsIso (H⁰ c)` is now literally `IsIso` of a map of cokernels in which no cone, no
shift and no connecting morphism occur, and for the canonical map of Stacks 0E1Y the morphism
being descended is the degree `-1` component of its null homotopy
(`CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`). -/
theorem homologyMap_zero_eq_cokernelDesc
    (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2))) (hP : IsZero (P.X 1)) :
    (P.homologyZeroIsoCokernel hP).inv ≫ HomologicalComplex.homologyMap c 0 ≫
        (shiftedHomologyZeroIsoCokernel g hL hM).hom =
      cokernel.desc (P.d (-1) 0) (shiftedSndZero g c ≫ cokernel.π (g.f (-1)))
        (d_comp_shiftedSndZero_comp_π g c hM) := by
  refine (cancel_epi (cokernel.π (P.d (-1) 0))).mp ?_
  rw [cokernel.π_desc, ← CochainComplex.toHomologyZero_comp_homologyZeroIsoCokernel P hP,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact toHomologyZero_comp_homologyMap_comp_shiftedHomologyZeroIsoCokernel g c hL hM hP

/-- **`H⁰(c)` is an isomorphism exactly when the induced map of cokernels is.**  The two
identifications of `CochainComplex.mappingCone.homologyMap_zero_eq_cokernelDesc`
are isomorphisms, so they do not affect invertibility.  For the canonical map of Stacks 0E1Y this
is the whole reduction of `IsIso (H⁰ c)`: the right-hand side is the map
`coker (d_{NL_{B/A} ⊗ C}^{-1}) ⟶ coker (g^{-1})` induced by the degree `-1` component of the null
homotopy of the proof, with no cone, no shift and no connecting morphism in it. -/
theorem isIso_homologyMap_zero_iff (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2)))
    (hP : IsZero (P.X 1)) :
    IsIso (HomologicalComplex.homologyMap c 0) ↔
      IsIso (cokernel.desc (P.d (-1) 0) (shiftedSndZero g c ≫ cokernel.π (g.f (-1)))
        (d_comp_shiftedSndZero_comp_π g c hM)) := by
  rw [← homologyMap_zero_eq_cokernelDesc g c hL hM hP, isIso_comp_left_iff,
    isIso_comp_right_iff]

end TwoTermCompare

end CochainComplex.mappingCone

end
