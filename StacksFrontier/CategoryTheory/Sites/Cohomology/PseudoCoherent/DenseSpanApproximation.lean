module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSpanGenerators
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.SectionsCardinality

/-!
# Generators carrying the strictly perfect approximations of a pseudo-coherent complex

Let `(C, O)` be a ringed site, `c : ι → C` a dense family of objects and `K` a pseudo-coherent
complex of `O`-modules (Stacks 08FT).  For every integer `m` and every object `c i` there is a
covering of `c i` over each member `V` of which `K|_V` is approximated by a strictly perfect
complex `P` through a map `α : P ⟶ K|_V` inducing isomorphisms on cohomology in degrees `> m`.

This file collects, as generators in the sense of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSpanSubcomplex.lean`, the images under these
approximations of all the sections of the `P` over the objects of the family which lie above an
arrow of the covering factoring through the family.  If the family, its arrows and the rings of
sections over it are bounded by an infinite cardinal `ν`, so is this set of generators; and for
every set of generators containing it, every cycle of `K` over an object of the family is
locally homologous to a cycle of the locally spanned subcomplex.  This is the half of the
closure argument which makes the inclusion of that subcomplex surjective on cohomology.

## Main results

* `AlgebraicGeometry.RingedSite.exists_gens_approximation`: the bounded set of generators and
  the local homology property.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
open Stacks.SheafOfModules.DenseSpan

universe t u'

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u', t, t})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{t}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{t}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{t}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})]
  {ι : Type t} (c : ι → X.C)

/-- The local homology property of a set of generators: every cycle over an object of the family
is locally homologous to a cycle lying in the local closure of the span. -/
def HasLocalHomology {K : CochainComplex
    (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (G : Gens c K) : Prop :=
  ∀ (j n k : ℤ), j + 1 = n → n + 1 = k → ∀ (i : ι) (z : (K.X n).val.obj (op (c i))),
    (K.d n k).val.app (op (c i)) z = 0 → ∃ S : Sieve (c i), S ∈ X.J (c i) ∧
      ∀ ⦃W : X.C⦄ (b : W ⟶ c i), S b →
        ∃ p : (K.X n).val.obj (op W), p ∈ (closure G n).obj (op W) ∧
          (K.d n k).val.app (op W) p = 0 ∧
          ∃ y : (K.X j).val.obj (op W), (K.X n).val.map b.op z = p + (K.d j n).val.app (op W) y

variable {X c}

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{t}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{t}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{t}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})] in
/-- The local homology property passes to larger sets of generators. -/
theorem HasLocalHomology.mono {K : CochainComplex
    (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} {G G' : Gens c K}
    (h : X.HasLocalHomology c G) (hGG' : G ⊆ G') : X.HasLocalHomology c G' := by
  intro j n k hj hk i z hz
  obtain ⟨S, hS, hloc⟩ := h j n k hj hk i z hz
  refine ⟨S, hS, fun W b hb => ?_⟩
  obtain ⟨p, hp, hdp, y, hy⟩ := hloc b hb
  refine ⟨p, X.J.superset_covering (fun W' f hf => ?_) hp, hdp, y, hy⟩
  exact Submodule.span_mono (genSet_mono hGG' n _) hf

variable (X c) in
/-- **A dense choice of strictly perfect approximations** of a complex `K`: for every integer `m`
and every object `c i` of the family a covering sieve of `c i`, and above every arrow
`a : c j ⟶ c i` of it from the family, an object `V` of the site through which `a` factors as
`g ≫ _`, a strictly perfect complex `P` on the slice over `V` and a map `α : P ⟶ K|_V` inducing
isomorphisms on cohomology in every degree `> m`. -/
structure DenseApproximation (K : CochainComplex
    (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  /-- The covering sieves. -/
  S : ℤ → ∀ i : ι, Sieve (c i)
  /-- They are covering. -/
  hS : ∀ m i, S m i ∈ X.J (c i)
  /-- The object above an arrow of a covering sieve from the family. -/
  V : ∀ (m : ℤ) (i j : ι) (a : c j ⟶ c i), S m i a → X.C
  /-- The arrow from the object of the family to it. -/
  g : ∀ m i j a ha, c j ⟶ V m i j a ha
  /-- The strictly perfect complex on the slice. -/
  P : ∀ m i j a ha, CochainComplex
    (SheafOfModules.{t} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V m i j a ha))) ℤ
  /-- It is strictly perfect. -/
  hP : ∀ m i j a ha, IsStrictlyPerfect _ (P m i j a ha)
  /-- The approximation. -/
  α : ∀ m i j a ha, P m i j a ha ⟶ X.restrictComplex K (V m i j a ha)
  /-- It induces isomorphisms on cohomology above `m`. -/
  hα : ∀ m i j a ha (n : ℤ), m < n → IsIso (HomologicalComplex.homologyMap (α m i j a ha) n)

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})] in
/-- A pseudo-coherent complex admits a dense choice of strictly perfect approximations. -/
theorem nonempty_denseApproximation {K : CochainComplex
    (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hK : X.IsPseudoCoherentComplex K) : Nonempty (DenseApproximation X c K) := by
  choose S hS hP using fun (m : ℤ) (i : ι) => hK m (c i)
  choose P hPsp α hα _ using hP
  choose V g f hf _ using
    fun (m : ℤ) (i j : ι) (a : c j ⟶ c i) (ha : Sieve.generate (S m i) a) => ha
  exact ⟨{ S := fun m i => Sieve.generate (S m i)
           hS := hS
           V := V
           g := g
           P := fun m i j a ha => P m i (f m i j a ha) (hf m i j a ha)
           hP := fun m i j a ha => hPsp m i (f m i j a ha) (hf m i j a ha)
           α := fun m i j a ha => α m i (f m i j a ha) (hf m i j a ha)
           hα := fun m i j a ha => hα m i (f m i j a ha) (hf m i j a ha) }⟩

namespace DenseApproximation

variable {K : CochainComplex (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (A : DenseApproximation X c K)

/-- The sections of the strictly perfect complex of an approximation over the slice object
defined by an arrow into its object of the family. -/
def Sec (m : ℤ) (i j : ι) (a : c j ⟶ c i) (ha : A.S m i a) (d : ℤ) (l : ι) (h : c l ⟶ c j) :
    Type t :=
  ((A.P m i j a ha).X d).val.obj (op (Over.mk (h ≫ A.g m i j a ha)))

/-- The indices of the generators of a dense choice of approximations: an approximation, a
degree, an arrow into its object of the family from another one, and a section of the strictly
perfect complex over the slice object that arrow defines. -/
def Idx : Type t :=
  Σ (m : ℤ) (i j : ι) (a : {a : c j ⟶ c i // A.S m i a}) (d : ℤ) (l : ι) (h : c l ⟶ c j),
    A.Sec m i j a.1 a.2 d l h

/-- The generator attached to an index: the image of the section under the approximation. -/
def gen : A.Idx → GenType c K
  | ⟨m, i, j, a, d, l, h, p⟩ =>
    ⟨d, l, ((A.α m i j a.1 a.2).f d).val.app (op (Over.mk (h ≫ A.g m i j a.1 a.2))) p⟩

/-- **The generators of a dense choice of approximations.** -/
def gens : Gens c K := Set.range A.gen

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})] in
/-- **The generators of a dense choice of approximations are bounded by `ν`** when the family,
its arrows and its rings of sections are. -/
theorem mk_gens_le {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hι : #ι ≤ ν)
    (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν) (hO : ∀ i : ι, #(X.O.obj.obj (op (c i))) ≤ ν) :
    #A.gens ≤ ν := by
  refine Cardinal.mk_range_le.trans ?_
  refine mk_sigma_int_le hν (fun m => mk_sigma_le_of_le hν hι (fun i => mk_sigma_le_of_le hν hι
    (fun j => mk_sigma_le_of_le hν ((Cardinal.mk_subtype_le _).trans (hHom j i))
      (fun a => mk_sigma_int_le hν (fun d => mk_sigma_le_of_le hν hι
        (fun l => mk_sigma_le_of_le hν (hHom l j) (fun h =>
          mk_sections_le_of_isStrictlyPerfect (A.hP m i j a.1 a.2) d _ hν (hO l))))))))

variable [hc : (inducedFunctor c).IsCoverDense X.J]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})] in
include hc in
/-- **Every set of generators containing the generators of a dense choice of approximations has
the local homology property.**  A cycle `z` over `c i` is, above an arrow `a : c j ⟶ c i` of
the covering sieve of degree `m = n - 1`, a cycle over the slice object `c j ⟶ V`; the
approximation is surjective on cohomology in degree `n`, so after restriction along a covering
of `c j` the cycle is the image of a cycle of `P` up to a boundary, and that image lies in the
local closure of the span because its restrictions to the objects of the family are among the
generators. -/
theorem hasLocalHomology (G : Gens c K) (hG : A.gens ⊆ G) : X.HasLocalHomology c G := by
  intro j n k hj hk i z hz
  refine exists_mem_sieve_of_dense (c := c) (A.S j i) (A.hS j i) (fun j' a ha => ?_)
  have : IsIso (HomologicalComplex.homologyMap (A.α j i j' a ha) n) :=
    A.hα j i j' a ha n (by omega)
  have hz₁ : ((X.restrictComplex K (A.V j i j' a ha)).d n k).val.app
      (op (Over.mk (A.g j i j' a ha))) ((K.X n).val.map a.op z) = 0 := by
    change (K.d n k).val.app (op (c j')) ((K.X n).val.map a.op z) = 0
    rw [PresheafOfModules.naturality_apply, hz, map_zero]
    rfl
  obtain ⟨S₁, hS₁, h₁⟩ := SheafOfModules.exists_mem_sieve_of_epi_homologyMap
    (A.α j i j' a ha) j n k hj hk (Over.mk (A.g j i j' a ha)) ((K.X n).val.map a.op z) hz₁
  refine ⟨Sieve.overEquiv _ S₁, hS₁, fun W b hb => ?_⟩
  obtain ⟨p, hdp, y, hy⟩ := h₁ _ ((Sieve.overEquiv_iff S₁ b).1 hb)
  refine ⟨((A.α j i j' a ha).f n).val.app _ p, ?_, ?_, y, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q : (K.X n).val.obj (op W),
        q = ((A.α j i j' a ha).f n).val.app _ p := ⟨_, rfl⟩
    suffices hmem : q ∈ (closure G n).obj (op W) from hq ▸ hmem
    refine X.J.superset_covering (fun W₂ e₂ he₂ => ?_)
      (Functor.IsCoverDense.is_cover (G := inducedFunctor c) W)
    obtain ⟨⟨l, lift, map, fac⟩⟩ := he₂
    rw [← fac]
    change (K.X n).val.map (lift ≫ map).op q ∈ (span G n).obj (op W₂)
    rw [op_comp, PresheafOfModules.map_comp_apply]
    refine map_mem_span G lift.op (Submodule.subset_span ⟨l, _, 𝟙 _, hG ⟨⟨j, i, j', ⟨a, ha⟩, n, l,
      map ≫ b, ((A.P j i j' a ha).X n).val.map
        (Over.homMk map (by simp) : Over.mk ((map ≫ b) ≫ A.g j i j' a ha) ⟶
          Over.mk (b ≫ A.g j i j' a ha)).op p⟩, rfl⟩,
      ?_⟩)
    have key : ((A.α j i j' a ha).f n).val.app (op (Over.mk ((map ≫ b) ≫ A.g j i j' a ha)))
        (((A.P j i j' a ha).X n).val.map (Over.homMk map (by simp) :
          Over.mk ((map ≫ b) ≫ A.g j i j' a ha) ⟶ Over.mk (b ≫ A.g j i j' a ha)).op p) =
        (K.X n).val.map map.op q := by
      rw [hq]
      exact PresheafOfModules.naturality_apply ((A.α j i j' a ha).f n).val _ p
    exact (SheafOfModules.map_id_apply (K.X n) (c l) _).trans key
  · change ((X.restrictComplex K (A.V j i j' a ha)).d n k).val.app _
      (((A.α j i j' a ha).f n).val.app _ p) = 0
    rw [← SheafOfModules.comp_val_app_apply, (A.α j i j' a ha).comm,
      SheafOfModules.comp_val_app_apply, hdp, map_zero]
  · rw [op_comp, PresheafOfModules.map_comp_apply]
    exact hy

end DenseApproximation

end AlgebraicGeometry.RingedSite
