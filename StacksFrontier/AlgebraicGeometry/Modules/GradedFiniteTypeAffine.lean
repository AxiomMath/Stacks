module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.AffineGeneration

/-!
# Generation of a graded module on a scheme by sections over an affine open

Let `Y` be a scheme, `𝒜` a sheaf of `ℤ`-graded `𝒪_Y`-algebras and `ℳ` a graded `𝒜`-module whose
homogeneous pieces are quasi-coherent. `SheafOfModules.GradedModule.Generates` is a
covering-sieve condition: a finite family `s` of homogeneous sections over an open `V` generates
`ℳ` over `V` when *every* homogeneous section of *every* degree over *every* open below `V` is,
locally, an `𝒜`-combination of the restrictions of `s`. Having generators of the sections over
`V` itself is therefore not literally the condition, and this file supplies the two steps between
the two.

## Main results

* `SheafOfModules.GradedModule.generates_of_exists_localComb`: generation is exactly the
  existence, around each point of each open below `V` and for each homogeneous section there, of
  a neighbourhood on which that section is a combination of the restricted family. This is the
  covering sieve of the definition unwound, and it holds on an arbitrary scheme with no
  hypothesis.
* `SheafOfModules.GradedModule.isFiniteType_of_affine_span`: **the affine criterion for finite
  type**, the generation criterion below on the cover of `Y` by all of its affine opens.
* `SheafOfModules.GradedModule.generates_of_affine_span`: **the affine criterion.** If `V` is
  affine and, in every degree `k`, finitely many products `s i · c` of the family with
  homogeneous sections of `𝒜` over `V` span `Γ(V, ℳ_k)` over `Γ(Y, V)`, then `s` generates `ℳ`
  over `V`.

## Implementation notes

The descent from `V` to a neighbourhood of a point of a smaller open is
`AlgebraicGeometry.exists_sum_smul_sections_of_span_eq_top`, the ungraded statement that sections
spanning the sections over an affine open generate the module there; quasi-coherence of the piece
`ℳ_k` is what that statement consumes, and it is the only place any hypothesis on `ℳ` is used.
The coefficients it returns are sections of `𝒪_Y`, and they are absorbed into the homogeneous
sections of `𝒜` by `SheafOfModules.GradedModule.smulSection_smul_right`; this is why the spanning
family in the hypothesis is a family of *products* rather than the family `s` itself, and why the
hypothesis is not simply `Module.Finite`.

The spanning family is indexed by `Fin m × Fin q` — one block of coefficients of a single length
`q` for each of the `m` generators — rather than by a dependent sum, so that the coefficient
produced for the generator `i` is a sum inside the single type `Γ(V, 𝒜_{k - d i})` and no
transport along `d` is needed. Padding the blocks with zeros makes this no restriction. The
ungraded statement is indexed by `Fin (m * q)`, and the two are matched by `finProdFinEquiv`.

The ring of the span is written `Y.ringCatSheaf.obj.obj (op V)` rather than `Γ(Y, V)`: the pieces
of `ℳ` have type `SheafOfModules.{u} Y.ringCatSheaf`, which is only unfoldably — not reducibly —
`Y.Modules`, so instance resolution does not find the `Γ(Y, V)`-module structure of
`AlgebraicGeometry.Scheme.Modules` on them, while the `ModuleCat` structure of the sections is
found directly. The two are definitionally equal, which is why the ungraded statement still
applies.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafOfModules.GradedModule

variable {Y : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf}

/-- A section of `𝒪_Y` over `V`, read as a scalar for the sections of a sheaf of modules over
`Y.ringCatSheaf`. The two rings are definitionally equal — one is the image of the other under
the forgetful functor from commutative rings — but instance resolution is syntactic, so the
spelling has to be forced; a type ascription does not do it, because it does not survive into
the elaborated term. -/
private abbrev scalar {V : Y.Opens} (r : Γ(Y, V)) : ↥(Y.ringCatSheaf.obj.obj (op V)) := r

/-- **Generation is a pointwise local condition.** A finite family `s` of homogeneous sections of
`ℳ` over `V` generates `ℳ` over `V` as soon as every homogeneous section over an open below `V`
is, on a neighbourhood of each of its points, an `𝒜`-combination of the restrictions of `s`.

This is `SheafOfModules.GradedModule.combinationSieve` being covering, written out: a sieve on an
open of a scheme is covering exactly when it contains an open neighbourhood of each point. -/
public theorem generates_of_exists_localComb (M : SheafOfModules.GradedModule.{u, u, u} A)
    {V : Y.Opens} {m : ℕ} (d : Fin m → ℤ) (s : ∀ i, (M.piece (d i)).val.obj (op V))
    (h : ∀ (k : ℤ) (W : Y.Opens) (g : W ⟶ V) (x : (M.piece k).val.obj (op W)) (pt : Y),
      pt ∈ W → ∃ (W' : Y.Opens) (g' : W' ⟶ W), pt ∈ W' ∧
        ∃ c : ∀ i, (A.piece (k - d i)).val.obj (op W'),
          ∑ i, M.smulSection k ((M.piece (d i)).val.restrictₛₗ (g' ≫ g).op (s i)) (c i) =
            (M.piece k).val.restrictₛₗ g'.op x) :
    M.Generates (J := Opens.grothendieckTopology Y) d s := by
  intro k W g x
  rw [Opens.mem_grothendieckTopology]
  intro pt hpt
  obtain ⟨W', g', hptW', c, hc⟩ := h k W g x pt hpt
  exact ⟨W', g', ⟨c, hc⟩, hptW'⟩

/-- **The affine criterion for generation of a graded module.** Let `V` be an affine open of `Y`,
let `s` be a finite family of homogeneous sections of `ℳ` over `V` of degrees `d`, and suppose
that in every degree `k` finitely many products of the `s i` with homogeneous sections of `𝒜`
over `V` span `Γ(V, ℳ_k)` over `Γ(Y, V)`. Then `s` generates `ℳ` over `V`.

Each homogeneous piece of `ℳ` is assumed quasi-coherent, which is what the ungraded descent
`AlgebraicGeometry.exists_sum_smul_sections_of_span_eq_top` consumes: a section over a smaller
open becomes, near each of its points, an `𝒪_Y`-combination of the restrictions of the spanning
products, and each such coefficient is absorbed into the homogeneous section it multiplies. -/
public theorem generates_of_affine_span (M : SheafOfModules.GradedModule.{u, u, u} A)
    (hqc : ∀ k : ℤ, (M.piece k).IsQuasicoherent)
    {V : Y.Opens} (hV : IsAffineOpen V) {m : ℕ} (d : Fin m → ℤ)
    (s : ∀ i, (M.piece (d i)).val.obj (op V))
    (hspan : ∀ k : ℤ, ∃ (q : ℕ) (c : ∀ i : Fin m, Fin q → (A.piece (k - d i)).val.obj (op V)),
      Submodule.span ↥(Y.ringCatSheaf.obj.obj (op V))
          (Set.range fun ij : Fin m × Fin q => M.smulSection k (s ij.1) (c ij.1 ij.2)) = ⊤) :
    M.Generates (J := Opens.grothendieckTopology Y) d s := by
  classical
  refine generates_of_exists_localComb M d s fun k W g x pt hpt => ?_
  obtain ⟨q, c, hsp⟩ := hspan k
  have := hqc k
  set T : Fin m × Fin q → ↥((M.piece k).val.obj (op V)) :=
    fun ij => M.smulSection k (s ij.1) (c ij.1 ij.2) with hT
  set T' : Fin (m * q) → ↥((M.piece k).val.obj (op V)) :=
    fun t => T (finProdFinEquiv.symm t) with hT'
  have hrange : Set.range T' = Set.range T :=
    finProdFinEquiv.symm.surjective.range_comp T
  have hsp' : Submodule.span ↥(Y.ringCatSheaf.obj.obj (op V)) (Set.range T') = ⊤ := by
    rw [hrange]; exact hsp
  obtain ⟨W', hW'W, hW'V, hptW', a, ha⟩ :=
    AlgebraicGeometry.exists_sum_smul_sections_of_span_eq_top (M.piece k) hV T' hsp'
      (leOfHom g) x pt hpt
  refine ⟨W', homOfLE hW'W, hptW',
    fun i => ∑ j, scalar (a (finProdFinEquiv (i, j))) •
      (A.piece (k - d i)).val.restrictₛₗ (homOfLE hW'V).op (c i j), ?_⟩
  have harrow : (homOfLE hW'W ≫ g) = homOfLE hW'V := Subsingleton.elim _ _
  have hterm : ∀ i : Fin m,
      M.smulSection k ((M.piece (d i)).val.restrictₛₗ (homOfLE hW'V).op (s i))
          (∑ j, scalar (a (finProdFinEquiv (i, j))) •
            (A.piece (k - d i)).val.restrictₛₗ (homOfLE hW'V).op (c i j)) =
        ∑ j, scalar (a (finProdFinEquiv (i, j))) •
          (M.piece k).val.restrictₛₗ (homOfLE hW'V).op (T (i, j)) := by
    intro i
    refine Eq.trans (map_sum (M.smulSection k
      ((M.piece (d i)).val.restrictₛₗ (homOfLE hW'V).op (s i))) _ Finset.univ) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Eq.trans (smulSection_smul_right M k _ _ _) ?_
    exact congrArg (fun z => scalar (a (finProdFinEquiv (i, j))) • z)
      (smulSection_restrictₛₗ M k (homOfLE hW'V).op (s i) (c i j)).symm
  have hreindex : ∑ t : Fin (m * q), scalar (a t) •
        (M.piece k).val.restrictₛₗ (homOfLE hW'V).op (T' t) =
      ∑ i : Fin m, ∑ j : Fin q, scalar (a (finProdFinEquiv (i, j))) •
        (M.piece k).val.restrictₛₗ (homOfLE hW'V).op (T (i, j)) := by
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [hT', Equiv.symm_apply_apply]
  rw [harrow]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => hterm i) (Eq.trans hreindex.symm ?_)
  exact (ha.trans (Finset.sum_congr rfl fun t _ => rfl)).symm

/-- **The affine criterion for a graded module to be of finite type.** If every homogeneous piece
of `M` is quasi-coherent and, over every affine open `V` of `Y`, there is a finite family of
homogeneous sections of `M` whose products with homogeneous sections of the algebra span the
degree-`k` sections over `V` for every `k`, then `M` is of finite type.

The covering family is the family of all affine opens, which covers `Y` because the affine opens
are a basis of its topology. -/
public theorem isFiniteType_of_affine_span (M : SheafOfModules.GradedModule.{u, u, u} A)
    (hqc : ∀ k : ℤ, (M.piece k).IsQuasicoherent)
    (h : ∀ V : Y.affineOpens, ∃ (m : ℕ) (d : Fin m → ℤ)
        (s : ∀ i, (M.piece (d i)).val.obj (op V.1)),
      ∀ k : ℤ, ∃ (q : ℕ)
          (c : ∀ i : Fin m, Fin q → (A.piece (k - d i)).val.obj (op V.1)),
        Submodule.span ↥(Y.ringCatSheaf.obj.obj (op V.1))
          (Set.range fun ij : Fin m × Fin q => M.smulSection k (s ij.1) (c ij.1 ij.2)) = ⊤) :
    M.IsFiniteType (J := Opens.grothendieckTopology Y) where
  exists_generators := by
    refine ⟨Y.affineOpens, fun V => V.1, ?_, fun V => ?_⟩
    · refine (Opens.coversTop_iff Y _).2 (TopologicalSpace.IsOpenCover.mk ?_)
      ext y
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      simpa using ⟨U, hU, hyU⟩
    · obtain ⟨m, d, s, hs⟩ := h V
      exact ⟨m, d, s, generates_of_affine_span M hqc V.2 d s hs⟩

end SheafOfModules.GradedModule

end

end
