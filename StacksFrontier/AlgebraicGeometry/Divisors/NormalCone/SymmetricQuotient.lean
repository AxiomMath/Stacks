module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.AlgebraicGeometry.Conormal.Charts
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.DegreeOnePiece
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map from the symmetric algebra of the conormal sheaf

Let `i : Z ⟶ X` be an immersion of schemes and let `𝒞_{Z/X,*}` be its conormal algebra, the
graded `𝒪_Z`-algebra whose degree-`n` piece is `ℐⁿ/ℐⁿ⁺¹` on every affine chart of `X` over
which `i` restricts to a closed immersion.  Its degree-one piece is the conormal sheaf
`𝒞_{Z/X}`, and this file builds the canonical map of graded `𝒪_Z`-algebras

`Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`

out of the universal property of the symmetric algebra.  The input that universal property
needs is that the degree-one local sections of `𝒞_{Z/X,*}` commute, and that comes from
graded commutativity of the conormal algebra, which is proved here chart by chart: a
homogeneous local section is locally the class of a section of a power of the chart ideal, and
multiplication of such classes is multiplication in the ring of functions on the chart.

## Main results

* `Stacks.Conormal.exists_affineChart_mem`: every point of an open of `Z` has a neighbourhood
  of the form `i ⁻¹ᵁ U` for an affine open `U` of `X` inside the coborder of the range of `i`,
  so the affine closed-immersion charts of `i` are a basis of opens of `Z`.
* `Stacks.Conormal.ConormalAlgebraData.mul_comm`: **homogeneous multiplication in the conormal
  algebra is commutative**, in every pair of nonnegative degrees, for any graded algebra with
  the local associated-graded presentations of Tag 0630.
* `Stacks.Conormal.pairwiseCommutes_conormalAlgebra`: its degree-one local sections commute
  pairwise, which is the hypothesis of the universal property of the symmetric algebra.
* `Stacks.Conormal.conormalSymmetricHom`: **the canonical map
  `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`**, with `conormalSymmetricHom_gen` saying that it is the
  identity on degree-one generators, `conormalSymmetricHom_app_one_gen` saying the same on
  local sections, and `conormalSymmetricHom_unique` saying that this property determines it.
* `Stacks.Conormal.isIso_conormalSymmetricHom_app_one` and
  `Stacks.Conormal.isIso_conormalSymmetricHom_app_zero`: **the canonical map is an isomorphism in
  degrees one and zero.**
* `Stacks.Conormal.epi_conormalSymmetricHom_app`: **the canonical map is surjective**, in every
  degree, with `Stacks.Conormal.exists_conormalSymmetricHom_app_eq_localMap` the chart statement
  it rests on and `Stacks.Conormal.isLocallySurjective_conormalSymmetricHom_app` the resulting
  local surjectivity.
* `Stacks.Conormal.ConormalAlgebraData.eq_zero_of_smul_one`: the graded unit of the conormal
  algebra is annihilated by no nonzero function, over any open of the source.
* `Stacks.Conormal.conormalPieceZeroIso`: **`𝒞_{Z/X,0} ≅ 𝒪_Z`**.

## Implementation notes

The conormal sheaf `𝒞_{Z/X}` is taken here to be the degree-one piece `𝒞_{Z/X,1}` of the
conormal algebra, which is the identification the source itself makes.  The independent
construction `Stacks.Conormal.conormalSheaf` of the conormal sheaf as `i.liftCoborder^* ℐ` is
not compared with it here.

`Stacks.Conormal.conormalSymmetricHom` is the `desc` of the universal property, so it is the
unique unital homomorphism which is the identity on degree-one generators; that uniqueness is
`Stacks.Conormal.conormalSymmetricHom_unique`, and it is what makes the map canonical.

Commutativity is stated as a `HEq` because the two products of a degree-`n` and a degree-`m`
section live in the pieces of degrees `n + m` and `m + n`, which are equal but not
syntactically so.  The two private lemmas `castEqOfHEq` and `castApply` move that single
equality of degrees past a cast and past the restriction maps.

Degree zero is settled by monomorphy together with epimorphy rather than by gluing the local
identifications into a global one.  Monomorphy is injectivity on the sections over every open,
which separatedness of the structure sheaf gives from the charts; epimorphy is local
surjectivity, which is the chart statement itself.  Gluing would additionally need the local
multiples of the unit to be amalgamated over a cover, and that step is what this route avoids.

### No `@[stacks 0632]`

Tag 0632 asserts three things about the map built here: that it exists and is canonical, that
it is **surjective**, and that it is an **isomorphism in degrees 0 and 1**.  All three are
proved here, and each attribute below is scoped to the clause it carries; **surjectivity** is
`Stacks.Conormal.epi_conormalSymmetricHom_app`, obtained from the chart statement that
`ℐⁿ/ℐⁿ⁺¹` is generated by products of `n` sections of `ℐ`.  No single declaration states all
three clauses, so the attributes stay scoped.

## References

* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-! ### The affine closed-immersion charts are a basis -/

/-- Every point of an open of `Z` lies in the preimage of an affine open of `X` contained both
in that open and in the coborder of the range of the immersion. -/
alias exists_affineChart_mem := Stacks.Conormal.exists_chart_near

/-- Every point of an open of `Z` lies in the preimage of an affine open of `X` contained in that
open, over which the immersion restricts to a closed immersion. -/
private theorem exists_closedImmersion_chart (i : Z ⟶ X) [IsImmersion i] (V : Z.Opens) (x : Z)
    (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ i ⁻¹ᵁ U.1 ∧ i ⁻¹ᵁ U.1 ≤ V ∧
      IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl) := by
  obtain ⟨U, hxU, hUV, hUcob⟩ := exists_affineChart_mem i V x hx
  exact ⟨U, hxU, hUV, isClosedImmersion_resLE_of_le_coborderRange i U.1 hUcob⟩

/-! ### Graded commutativity of the conormal algebra -/

private theorem castEqOfHEq {ι : Sort _} (A : ι → Type u) {j k : ι} (e : j = k) {a : A j}
    {b : A k} (h : HEq a b) : cast (congrArg A e) a = b :=
  eq_of_heq ((cast_heq _ a).trans h)

private theorem castApply {ι : Sort _} (A B : ι → Type u) {j k : ι} (e : j = k)
    (f : ∀ l, A l → B l) (a : A j) :
    f k (cast (congrArg A e) a) = cast (congrArg B e) (f j a) := by
  cases e
  rfl

/-- Homogeneous multiplication of the conormal algebra is commutative over an affine chart on
which the immersion restricts to a closed immersion. -/
private theorem ConormalAlgebraData.mul_comm_chart {i : Z ⟶ X} [IsImmersion i]
    (D : ConormalAlgebraData i)
    (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n m : ℕ)
    (a : (D.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)))
    (b : (D.algebra.piece (m : ℤ)).val.obj (op (i ⁻¹ᵁ U.1))) :
    HEq ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ U.1)) a b)
      ((D.algebra.mul (m : ℤ) (n : ℤ)).app (op (i ⁻¹ᵁ U.1)) b a) := by
  obtain ⟨x, hx⟩ := D.localMap_surjective U hU n a
  obtain ⟨y, hy⟩ := D.localMap_surjective U hU m b
  let c : ↥(chartIdeal i U ^ (n + m)) :=
    ⟨(x : Γ(X, U)) * (y : Γ(X, U)), by
      rw [Ideal.IsTwoSided.pow_add]
      exact Ideal.mul_mem_mul x.2 y.2⟩
  have hnm : n + m = m + n := Nat.add_comm n m
  let hpow := congrArg (fun k : ℕ => ↥(chartIdeal i U ^ k)) hnm
  let d : ↥(chartIdeal i U ^ (m + n)) := cast hpow c
  have hp : (⟨n + m, c⟩ : Σ k : ℕ, ↥(chartIdeal i U ^ k)) = ⟨m + n, d⟩ :=
    Sigma.ext hnm (cast_heq hpow c).symm
  have hv : (c : Γ(X, U)) = (d : Γ(X, U)) :=
    congrArg (fun p : Σ k : ℕ, ↥(chartIdeal i U ^ k) => (p.2 : Γ(X, U))) hp
  have hd : (d : Γ(X, U)) = (y : Γ(X, U)) * (x : Γ(X, U)) := by
    rw [← hv]
    exact mul_comm _ _
  have hf := congrArg
    (fun p : Σ k : ℕ, ↥(chartIdeal i U ^ k) =>
      (⟨p.1, D.localMap U hU p.1 p.2⟩ :
        Σ k : ℕ, (D.algebra.piece (k : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)))) hp
  rw [← hx, ← hy, ← D.localMap_mul U hU n m x y c rfl, ← D.localMap_mul U hU m n y x d hd]
  exact (Sigma.mk.inj hf).2

/-- **Homogeneous multiplication in the conormal algebra of an immersion is commutative**, in
every pair of nonnegative degrees. -/
theorem ConormalAlgebraData.mul_comm {i : Z ⟶ X} [IsImmersion i] (D : ConormalAlgebraData i)
    (n m : ℕ) (V : Z.Opens)
    (a : (D.algebra.piece (n : ℤ)).val.obj (op V))
    (b : (D.algebra.piece (m : ℤ)).val.obj (op V)) :
    HEq ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op V) a b)
      ((D.algebra.mul (m : ℤ) (n : ℤ)).app (op V) b a) := by
  classical
  have hnm : (n : ℤ) + (m : ℤ) = (m : ℤ) + (n : ℤ) := Int.add_comm _ _
  refine (cast_heq
      (congrArg (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op V))) hnm) _).symm.trans
    (heq_of_eq ?_)
  refine TopCat.Presheaf.IsSheaf.section_ext
    (D.algebra.piece ((m : ℤ) + (n : ℤ))).isSheaf (U := op V) ?_
  intro x hx
  obtain ⟨U, hxU, hUV, hU⟩ := exists_closedImmersion_chart i V x hx
  refine ⟨i ⁻¹ᵁ U.1, hUV, hxU, ?_⟩
  have hmul : ∀ (n m : ℕ) (a : (D.algebra.piece (n : ℤ)).val.obj (op V))
      (b : (D.algebra.piece (m : ℤ)).val.obj (op V)),
      (D.algebra.piece ((n : ℤ) + (m : ℤ))).val.map (homOfLE hUV).op
          ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op V) a b) =
        (D.algebra.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ U.1))
          ((D.algebra.piece (n : ℤ)).val.map (homOfLE hUV).op a)
          ((D.algebra.piece (m : ℤ)).val.map (homOfLE hUV).op b) := fun n m a b => by
    simpa only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] using
      (D.algebra.mul (n : ℤ) (m : ℤ)).naturality (homOfLE hUV).op a b
  have h3 : (D.algebra.piece ((m : ℤ) + (n : ℤ))).val.map (homOfLE hUV).op
        (cast (congrArg (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op V))) hnm)
          ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op V) a b)) =
      cast (congrArg (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op (i ⁻¹ᵁ U.1)))) hnm)
        ((D.algebra.piece ((n : ℤ) + (m : ℤ))).val.map (homOfLE hUV).op
          ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op V) a b)) :=
    castApply (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op V)))
      (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op (i ⁻¹ᵁ U.1)))) hnm
      (fun k s => (D.algebra.piece k).val.map (homOfLE hUV).op s)
      ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op V) a b)
  have h4 : cast (congrArg (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op (i ⁻¹ᵁ U.1)))) hnm)
        ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ U.1))
          ((D.algebra.piece (n : ℤ)).val.map (homOfLE hUV).op a)
          ((D.algebra.piece (m : ℤ)).val.map (homOfLE hUV).op b)) =
      (D.algebra.mul (m : ℤ) (n : ℤ)).app (op (i ⁻¹ᵁ U.1))
        ((D.algebra.piece (m : ℤ)).val.map (homOfLE hUV).op b)
        ((D.algebra.piece (n : ℤ)).val.map (homOfLE hUV).op a) :=
    castEqOfHEq (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op (i ⁻¹ᵁ U.1)))) hnm
      (D.mul_comm_chart U hU n m
        ((D.algebra.piece (n : ℤ)).val.map (homOfLE hUV).op a)
        ((D.algebra.piece (m : ℤ)).val.map (homOfLE hUV).op b))
  have hgoal : (D.algebra.piece ((m : ℤ) + (n : ℤ))).val.map (homOfLE hUV).op
        (cast (congrArg (fun k : ℤ => ↥((D.algebra.piece k).val.obj (op V))) hnm)
          ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op V) a b)) =
      (D.algebra.piece ((m : ℤ) + (n : ℤ))).val.map (homOfLE hUV).op
        ((D.algebra.mul (m : ℤ) (n : ℤ)).app (op V) b a) := by
    rw [h3, hmul, h4, hmul]
  have hconv : ∀ (k : ℤ) (s : ↥((D.algebra.piece k).val.obj (op V))),
      (D.algebra.piece k).val.presheaf.map (homOfLE hUV).op s =
        (D.algebra.piece k).val.map (homOfLE hUV).op s := fun _ _ => rfl
  rw [hconv, hconv]
  exact hgoal

/-- **The degree-one local sections of the conormal algebra commute pairwise.** -/
theorem pairwiseCommutes_conormalAlgebra (i : Z ⟶ X) [IsImmersion i] :
    SheafOfModules.GradedAlgebra.PairwiseCommutes
      (A := (conormalAlgebra i).algebra) (𝟙 ((conormalAlgebra i).algebra.piece 1)) := by
  intro V s t
  simpa using eq_of_heq ((conormalAlgebra i).mul_comm 1 1 V.unop s t)

/-! ### The canonical map out of the symmetric algebra -/

/-- `Sym*(𝒞_{Z/X})`, the symmetric algebra of the conormal sheaf of an immersion. -/
abbrev conormalSymmetricAlgebra (i : Z ⟶ X) [IsImmersion i] :
    SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf :=
  Scheme.Modules.symmetricAlgebra Z ((conormalAlgebra i).algebra.piece 1)

/-- **Stacks Project, Tag 0632.** The canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of graded
`𝒪_Z`-algebras, the unital homomorphism which is the identity on degree-one generators. -/
@[stacks 0632 "the canonical map Sym*(C_{Z/X}) → C_{Z/X,*} of graded algebras",
  ega "0 19.5.2" "more general",
  ega "0 22.1.1" "more general",
  ega "IV 17.12.1"]
def conormalSymmetricHom (i : Z ⟶ X) [IsImmersion i] :
    SheafOfModules.GradedAlgebra.UnitalHom (conormalSymmetricAlgebra i)
      (conormalAlgebra i).algebra :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra Z
      ((conormalAlgebra i).algebra.piece 1)).isUniversal.desc
    (conormalAlgebra i).algebra (𝟙 _) (pairwiseCommutes_conormalAlgebra i)

/-- The canonical map is the identity on the degree-one generators of the symmetric algebra. -/
theorem conormalSymmetricHom_gen (i : Z ⟶ X) [IsImmersion i] :
    Scheme.Modules.symmetricAlgebraGen Z ((conormalAlgebra i).algebra.piece 1) ≫
        (conormalSymmetricHom i).app 1 =
      𝟙 ((conormalAlgebra i).algebra.piece 1) :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra Z
      ((conormalAlgebra i).algebra.piece 1)).isUniversal.desc_extends
    (conormalAlgebra i).algebra (𝟙 _) (pairwiseCommutes_conormalAlgebra i)

/-- **Stacks Project, Tag 0632.** A unital homomorphism which is the identity on degree-one
generators is the canonical map, so the canonical map is well defined. -/
@[stacks 0632 "uniqueness of the canonical map Sym*(C_{Z/X}) → C_{Z/X,*}"]
theorem conormalSymmetricHom_unique (i : Z ⟶ X) [IsImmersion i]
    {g : SheafOfModules.GradedAlgebra.UnitalHom (conormalSymmetricAlgebra i)
      (conormalAlgebra i).algebra}
    (hg : Scheme.Modules.symmetricAlgebraGen Z ((conormalAlgebra i).algebra.piece 1) ≫
      g.app 1 = 𝟙 ((conormalAlgebra i).algebra.piece 1)) :
    g = conormalSymmetricHom i :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra Z
      ((conormalAlgebra i).algebra.piece 1)).isUniversal.desc_unique
    (conormalAlgebra i).algebra (𝟙 _) (pairwiseCommutes_conormalAlgebra i) hg

/-! ### The isomorphism in degree one -/

/-- **Stacks Project, Tag 0632.** The canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is an
isomorphism in degree one. The degree-one generator `𝒞_{Z/X} ⟶ Sym¹(𝒞_{Z/X})` is an isomorphism,
and the canonical map is the identity on it. -/
@[stacks 0632 "the canonical map Sym*(C_{Z/X}) → C_{Z/X,*} is an isomorphism in degree 1"]
theorem isIso_conormalSymmetricHom_app_one (i : Z ⟶ X) [IsImmersion i] :
    IsIso ((conormalSymmetricHom i).app 1) :=
  have : IsIso (Scheme.Modules.symmetricAlgebraGen Z ((conormalAlgebra i).algebra.piece 1)) :=
    Scheme.Modules.isIso_symmetricAlgebraGen Z _
  IsIso.of_isIso_fac_left (conormalSymmetricHom_gen i)

/-! ### Degree zero of the conormal algebra -/

/-- Over an affine chart, the degree-zero class of a function is that function's restriction times
the class of `1`. -/
private theorem ConormalAlgebraData.localMap_zero_eq_smul_one {i : Z ⟶ X} [IsImmersion i]
    (D : ConormalAlgebraData i) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (a : ↥(chartIdeal i U ^ 0)) :
    D.localMap U hU 0 a =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom (a : Γ(X, U))) •
        D.algebra.one.eval (op (i ⁻¹ᵁ U.1)) := by
  rw [← D.localMap_one U hU ⟨1, by simp⟩ rfl]
  exact D.localMap_smul U hU 0 (a : Γ(X, U)) ⟨1, by simp⟩ a (by simp)

/-- Over an affine chart on which the immersion restricts to a closed immersion, every
degree-zero local section of the conormal algebra is a multiple of the graded unit: the class of
a function on the chart is that function's restriction times the class of `1`. -/
private theorem ConormalAlgebraData.exists_smul_one_chart {i : Z ⟶ X} [IsImmersion i]
    (D : ConormalAlgebraData i) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (x : (D.algebra.piece 0).val.obj (op (i ⁻¹ᵁ U.1))) :
    ∃ s : Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)),
      s • D.algebra.one.eval (op (i ⁻¹ᵁ U.1)) = x := by
  obtain ⟨a, ha⟩ := D.localMap_surjective U hU 0 x
  exact ⟨_, ((D.localMap_zero_eq_smul_one U hU a).symm.trans ha)⟩

/-- Over an affine chart on which the immersion restricts to a closed immersion, a function
annihilating the graded unit of the conormal algebra vanishes: it lifts to the chart, where the
degree-zero class of its lift dies exactly when the lift is in the chart ideal. -/
private theorem ConormalAlgebraData.eq_zero_of_smul_one_chart {i : Z ⟶ X} [IsImmersion i]
    (D : ConormalAlgebraData i) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (s : Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
    (hs : s • D.algebra.one.eval (op (i ⁻¹ᵁ U.1)) = 0) : s = 0 := by
  obtain ⟨r, hr⟩ := app_surjective_of_closedRestriction i U hU s
  have h0 : D.localMap U hU 0 ⟨r, by simp⟩ = 0 := by
    rw [D.localMap_zero_eq_smul_one U hU ⟨r, by simp⟩]
    rw [show (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom r) = s from hr]
    exact hs
  rw [D.localMap_eq_zero_iff, pow_one] at h0
  rw [← hr]
  exact h0

/-- **The graded unit of the conormal algebra is annihilated by no nonzero function**, over any
open of the source. The affine closed-immersion charts are a basis, over each of them the
statement is that a function whose lift to the chart lies in the chart ideal vanishes, and the
structure sheaf is separated. -/
theorem ConormalAlgebraData.eq_zero_of_smul_one {i : Z ⟶ X} [IsImmersion i]
    (D : ConormalAlgebraData i) (V : Z.Opens) (s : Z.ringCatSheaf.obj.obj (op V))
    (hs : s • D.algebra.one.eval (op V) = 0) : s = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext Z.ringCatSheaf.property (U := op V)
    (s := s) (t := 0) ?_
  intro x hx
  obtain ⟨U, hxU, hUV, hU⟩ := exists_closedImmersion_chart i V x hx
  refine ⟨i ⁻¹ᵁ U.1, hUV, hxU, ?_⟩
  have hone : (D.algebra.piece 0).val.map (homOfLE hUV).op (D.algebra.one.eval (op V)) =
      D.algebra.one.eval (op (i ⁻¹ᵁ U.1)) :=
    PresheafOfModules.sections_property D.algebra.one (homOfLE hUV).op
  have hsm : (D.algebra.piece 0).val.map (homOfLE hUV).op (s • D.algebra.one.eval (op V)) =
      Z.ringCatSheaf.obj.map (homOfLE hUV).op s •
        (D.algebra.piece 0).val.map (homOfLE hUV).op (D.algebra.one.eval (op V)) :=
    PresheafOfModules.map_smul (D.algebra.piece 0).val (homOfLE hUV).op s
      (D.algebra.one.eval (op V))
  have key : Z.ringCatSheaf.obj.map (homOfLE hUV).op s •
      D.algebra.one.eval (op (i ⁻¹ᵁ U.1)) = 0 :=
    (congrArg (fun y : (D.algebra.piece 0).val.obj (op (i ⁻¹ᵁ U.1)) =>
        Z.ringCatSheaf.obj.map (homOfLE hUV).op s • y) hone.symm).trans
      (hsm.symm.trans ((congrArg
        ((D.algebra.piece 0).val.map (homOfLE hUV).op) hs).trans (map_zero _)))
  rw [D.eq_zero_of_smul_one_chart U hU _ key, map_zero]

/-! ### The isomorphism in degree zero -/

/-- The canonical map carries a multiple of the unit of `Sym*(𝒞_{Z/X})` to the same multiple of
the unit of `𝒞_{Z/X,*}`, being linear and unital. -/
private theorem conormalSymmetricHom_app_zero_smul_one (i : Z ⟶ X) [IsImmersion i] (V : Z.Opens)
    (t : Z.ringCatSheaf.obj.obj (op V)) :
    PresheafOfModules.Hom.app ((conormalSymmetricHom i).app 0).val (op V)
        (t • (conormalSymmetricAlgebra i).one.eval (op V)) =
      t • (conormalAlgebra i).algebra.one.eval (op V) := by
  rw [map_smul, (conormalSymmetricHom i).map_one (op V)]

/-- The canonical map is injective on the degree-zero sections over every open: both degree-zero
pieces are generated by their units, freely on the source by
`AlgebraicGeometry.Scheme.Modules.bijective_smul_one_symmetricAlgebra` and without torsion on the
target by `Stacks.Conormal.ConormalAlgebraData.eq_zero_of_smul_one`. -/
private theorem injective_conormalSymmetricHom_app_zero (i : Z ⟶ X) [IsImmersion i]
    (V : Z.Opens) :
    Function.Injective
      (PresheafOfModules.Hom.app ((conormalSymmetricHom i).app 0).val (op V)) := by
  intro y y' h
  obtain ⟨r, hr⟩ := (Scheme.Modules.bijective_smul_one_symmetricAlgebra Z
    ((conormalAlgebra i).algebra.piece 1) V).2 y
  obtain ⟨r', hr'⟩ := (Scheme.Modules.bijective_smul_one_symmetricAlgebra Z
    ((conormalAlgebra i).algebra.piece 1) V).2 y'
  replace hr : r • (conormalSymmetricAlgebra i).one.eval (op V) = y := hr
  replace hr' : r' • (conormalSymmetricAlgebra i).one.eval (op V) = y' := hr'
  have e : r • (conormalAlgebra i).algebra.one.eval (op V) =
      r' • (conormalAlgebra i).algebra.one.eval (op V) := by
    rw [← conormalSymmetricHom_app_zero_smul_one i V r,
      ← conormalSymmetricHom_app_zero_smul_one i V r', hr, hr', h]
  have e2 : (r - r') • (conormalAlgebra i).algebra.one.eval (op V) = 0 := by
    rw [sub_smul, e, sub_self]
  rw [← hr, ← hr', sub_eq_zero.mp ((conormalAlgebra i).eq_zero_of_smul_one V _ e2)]

/-- The canonical map is locally surjective in degree zero: on an affine closed-immersion chart
every degree-zero section of `𝒞_{Z/X,*}` is a multiple of the unit, and the same multiple of the
unit of `Sym*(𝒞_{Z/X})` is a preimage. -/
private theorem isLocallySurjective_conormalSymmetricHom_app_zero (i : Z ⟶ X) [IsImmersion i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : TopCat))
      ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        ((conormalSymmetricHom i).app 0).val) := by
  constructor
  intro V x p hp
  obtain ⟨U, hpU, hUV, hU⟩ := exists_closedImmersion_chart i V p hp
  obtain ⟨s, hs⟩ := (conormalAlgebra i).exists_smul_one_chart U hU
    (((conormalAlgebra i).algebra.piece 0).val.map (homOfLE hUV).op x)
  refine ⟨i ⁻¹ᵁ U.1, homOfLE hUV,
    ⟨s • (conormalSymmetricAlgebra i).one.eval (op (i ⁻¹ᵁ U.1)), ?_⟩, hpU⟩
  exact (conormalSymmetricHom_app_zero_smul_one i (i ⁻¹ᵁ U.1) s).trans hs

/-- **Stacks Project, Tag 0632.** The canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is an
isomorphism in degree zero. It is a monomorphism because both degree-zero pieces are generated
by their graded units, freely on the source and without torsion on the target, and an
epimorphism because on an affine closed-immersion chart every degree-zero section of the target
is a multiple of the unit. -/
@[stacks 0632 "the canonical map Sym*(C_{Z/X}) → C_{Z/X,*} is an isomorphism in degree 0"]
theorem isIso_conormalSymmetricHom_app_zero (i : Z ⟶ X) [IsImmersion i] :
    IsIso ((conormalSymmetricHom i).app 0) := by
  have hmono : Mono ((conormalSymmetricHom i).app 0) :=
    (SheafOfModules.forget Z.ringCatSheaf).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (f := ((conormalSymmetricHom i).app 0).val)
        fun V => injective_conormalSymmetricHom_app_zero i V.unop)
  have hepi : Epi ((conormalSymmetricHom i).app 0) :=
    Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
      (isLocallySurjective_conormalSymmetricHom_app_zero i)
  exact isIso_of_mono_of_epi _

/-- **`𝒞_{Z/X,0} ≅ 𝒪_Z`:** the degree-zero piece of the conormal algebra of an immersion is the
structure sheaf of the source, the canonical map being an isomorphism in degree zero and degree
zero of a symmetric algebra being the structure sheaf. -/
noncomputable def conormalPieceZeroIso (i : Z ⟶ X) [IsImmersion i] :
    (conormalAlgebra i).algebra.piece 0 ≅ SheafOfModules.unit Z.ringCatSheaf :=
  haveI := isIso_conormalSymmetricHom_app_zero i
  (asIso ((conormalSymmetricHom i).app 0)).symm ≪≫
    Scheme.Modules.symmetricAlgebraPieceZeroIso Z ((conormalAlgebra i).algebra.piece 1)

/-! ### Surjectivity -/

/-- The canonical map is the identity on the degree-one sections which come from the generator of
the symmetric algebra: the section-level form of
`Stacks.Conormal.conormalSymmetricHom_gen`. -/
private theorem conormalSymmetricHom_app_one_gen (i : Z ⟶ X) [IsImmersion i] (V : Z.Opens)
    (x : ((conormalAlgebra i).algebra.piece 1).val.obj (op V)) :
    PresheafOfModules.Hom.app ((conormalSymmetricHom i).app 1).val (op V)
        (PresheafOfModules.Hom.app
          (Scheme.Modules.symmetricAlgebraGen Z ((conormalAlgebra i).algebra.piece 1)).val
          (op V) x) =
      x :=
  congrArg
    (fun f : (conormalAlgebra i).algebra.piece 1 ⟶ (conormalAlgebra i).algebra.piece 1 =>
      PresheafOfModules.Hom.app f.val (op V) x) (conormalSymmetricHom_gen i)

/-- The public form of `conormalSymmetricHom_app_one_gen`. -/
alias conormalSymmetricHom_app_one_symmetricAlgebraGen := conormalSymmetricHom_app_one_gen

/-- **Over an affine closed-immersion chart the canonical map hits every homogeneous section of
the conormal algebra.** The `n`-th power of the chart ideal is generated by products of `n` of
its elements, and the canonical map carries the matching product of degree-one generators of
`Sym*(𝒞_{Z/X})` to the product of their degree-`1` classes; degree `0` is the chart multiple of
the graded unit. -/
theorem exists_conormalSymmetricHom_app_eq_localMap (i : Z ⟶ X) [IsImmersion i]
    (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n : ℕ)
    (a : ↥(chartIdeal i U ^ n)) :
    ∃ s : ((conormalSymmetricAlgebra i).piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)),
      PresheafOfModules.Hom.app ((conormalSymmetricHom i).app (n : ℤ)).val (op (i ⁻¹ᵁ U.1)) s =
        (conormalAlgebra i).localMap U hU n a := by
  revert a
  induction n with
  | zero =>
    intro a
    show ∃ s : ((conormalSymmetricAlgebra i).piece 0).val.obj (op (i ⁻¹ᵁ U.1)),
      PresheafOfModules.Hom.app ((conormalSymmetricHom i).app 0).val (op (i ⁻¹ᵁ U.1)) s =
        (conormalAlgebra i).localMap U hU 0 a
    obtain ⟨t, ht⟩ := (conormalAlgebra i).exists_smul_one_chart U hU
      ((conormalAlgebra i).localMap U hU 0 a)
    exact ⟨t • (conormalSymmetricAlgebra i).one.eval (op (i ⁻¹ᵁ U.1)),
      (conormalSymmetricHom_app_zero_smul_one i (i ⁻¹ᵁ U.1) t).trans ht⟩
  | succ n ih =>
    intro a
    have key : ∀ y ∈ chartIdeal i U ^ n * chartIdeal i U,
        ∃ hy : y ∈ chartIdeal i U ^ (n + 1),
          ∃ s : ((conormalSymmetricAlgebra i).piece ((n : ℤ) + 1)).val.obj (op (i ⁻¹ᵁ U.1)),
            PresheafOfModules.Hom.app
                ((conormalSymmetricHom i).app ((n : ℤ) + 1)).val (op (i ⁻¹ᵁ U.1)) s =
              (conormalAlgebra i).localMap U hU (n + 1) ⟨y, hy⟩ := by
      intro y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro b hb c hc
        have hc1 : c ∈ chartIdeal i U ^ 1 := by rwa [pow_one]
        refine ⟨by rw [pow_succ]; exact Ideal.mul_mem_mul hb hc, ?_⟩
        obtain ⟨s, hs⟩ := ih ⟨b, hb⟩
        refine ⟨((conormalSymmetricAlgebra i).mul (n : ℤ) 1).app (op (i ⁻¹ᵁ U.1)) s
          (PresheafOfModules.Hom.app
            (Scheme.Modules.symmetricAlgebraGen Z ((conormalAlgebra i).algebra.piece 1)).val
            (op (i ⁻¹ᵁ U.1)) ((conormalAlgebra i).localMap U hU 1 ⟨c, hc1⟩)), ?_⟩
        rw [(conormalSymmetricHom i).map_mul (n : ℤ) 1 (op (i ⁻¹ᵁ U.1)), hs,
          conormalSymmetricHom_app_one_gen]
        exact ((conormalAlgebra i).localMap_mul U hU n 1 ⟨b, hb⟩ ⟨c, hc1⟩ _ rfl).symm
      · intro p q hp hq
        obtain ⟨hpm, s, hs⟩ := hp
        obtain ⟨hqm, s', hs'⟩ := hq
        refine ⟨add_mem hpm hqm, s + s', ?_⟩
        have hsub : (⟨p + q, add_mem hpm hqm⟩ : ↥(chartIdeal i U ^ (n + 1))) =
            ⟨p, hpm⟩ + ⟨q, hqm⟩ := rfl
        rw [map_add, hs, hs', hsub, map_add]
    obtain ⟨hy, s, hs⟩ := key (a : Γ(X, U)) (by rw [← pow_succ]; exact a.2)
    exact ⟨s, hs⟩

/-- **The canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is locally surjective in every nonnegative
degree.** The affine closed-immersion charts are a basis, and over each of them every degree-`n`
section of the target is the class of a section of the `n`-th power of the chart ideal, hence in
the image of the canonical map. -/
theorem isLocallySurjective_conormalSymmetricHom_app (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : TopCat))
      ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        ((conormalSymmetricHom i).app (n : ℤ)).val) := by
  constructor
  intro V x p hp
  obtain ⟨U, hpU, hUV, hU⟩ := exists_closedImmersion_chart i V p hp
  obtain ⟨a, ha⟩ := (conormalAlgebra i).localMap_surjective U hU n
    (((conormalAlgebra i).algebra.piece (n : ℤ)).val.map (homOfLE hUV).op x)
  obtain ⟨s, hs⟩ := exists_conormalSymmetricHom_app_eq_localMap i U hU n a
  exact ⟨i ⁻¹ᵁ U.1, homOfLE hUV, ⟨s, hs.trans ha⟩, hpU⟩

/-- **Stacks Project, Tag 0632.** The canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is surjective:
an epimorphism of sheaves of modules in every degree. In a negative degree the target vanishes,
and in a nonnegative degree the map is locally surjective, because over an affine
closed-immersion chart `ℐⁿ/ℐⁿ⁺¹` is generated by products of `n` sections of `ℐ`. -/
@[stacks 0632 "the canonical map Sym*(C_{Z/X}) → C_{Z/X,*} is surjective"]
theorem epi_conormalSymmetricHom_app (i : Z ⟶ X) [IsImmersion i] (n : ℤ) :
    Epi ((conormalSymmetricHom i).app n) := by
  rcases lt_or_ge n 0 with hn | hn
  · exact ⟨fun g h _ => ((conormalAlgebra i).negative_isZero n hn).eq_of_src g h⟩
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
      (isLocallySurjective_conormalSymmetricHom_app i m)

end Stacks.Conormal

end
