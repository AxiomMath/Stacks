module

public import StacksFrontier.Deformation.FlatModuleLift
public import StacksFrontier.Deformation.FlatModuleLiftEquivalence
public import StacksFrontier.Deformation.ToposThickening.FreeLiftBaseChange

/-!
# Square-zero corrections of a free differential lift, and their glueing along `(J', Q')`

Let `f : R' → R` be a surjection of commutative rings, `F` a complex of `R`-modules and `L` a
`Deformation.Obstruction.FreeDifferentialLift` of `F` across `f`: free `R'`-modules `L.X n`
reducing to `F.X n` modulo `ker f · L.X n`, carrying maps `L.d` which reduce to the differential
of `F`. Nothing forces `L.d ∘ L.d` to vanish; it only lands in `ker f · L`, by
`Deformation.Obligation.curvature_mem`.

A **square-zero correction** of `L` is a degree-one cochain `ε` valued in `ker f · L` with

`(L.d + ε) ∘ (L.d + ε) = 0`,

i.e. a solution of the Maurer–Cartan equation of the lift. By
`Deformation.Obligation.SquareZeroCorrection.lift` and
`Deformation.Obligation.squareZeroCorrection_of_d`, having one is the same as being able to lift
`F` to an honest complex of free `R'`-modules *on the given terms and with the given reduction*;
this is the criterion of Stacks 0DZ1 written on a free presentation, and it is what the nilpotent
form of Stacks 0DZ2 has to transfer along `P' → Q'`.

## Where the difficulty of the nilpotent form of Stacks 0DZ2 sits

Run the dévissage of Stacks 0DZ2 along the `𝔞`-adic filtration of `𝔞 = ker f`. Every step
`A'/I^(j+1) → A'/I^j` is square-zero, so the square-zero case applies at each one with no
refinement of the filtration; and the variation of the curvature under a correction `z` is
**exact**,

`(d + z)² = d² + (d z + z d) + z z`   (`Deformation.Obligation.curvature_add`),

with `d z + z d` a Bockstein and `z z` a Yoneda square. For `z` valued in `𝔞^m · L` the Yoneda
square is valued in `𝔞^(m+m) · L`, so it is **invisible modulo `𝔞^(m+2)` as soon as `2 ≤ m`**:
`Deformation.Obligation.curvature_add_sub_mem_of_two_le`. At `m = 0` there is nothing to vary,
the lifted differential being given. So the dévissage is linear at every window except `m = 1` —
the dependence of the level-`2` obstruction on the first-order correction — and that one window
carries the whole nonlinearity. It is exactly the window
`StacksDraft.Deformation.Examples.Linear.PartialLiftObstruction` attacks: over `A' = ℤ/8` the
partial lift `M₂ = ℤ/4` of `M = 𝔽₂` does not lift, while `M` does.

At a *linear* window the transfer input is supplied by Stacks 05EC, degree by degree. Fix the
corrected differential `D` in degree `n + 1`; solving for the degree-`n` component means finding
`ε` valued in `ker f · L` with `(L.d + ε) ≫ D = 0`, and because `L.X n` is free that is exactly
the membership

`D (L.d x) ∈ D (ker f · L.X (n+1))` for every `x : L.X n`,

an element of an `R'`-module lying in a submodule. Membership in a submodule is detected by the
formal glueing data: `Deformation.Obligation.mem_of_formalGlueing` says that for a finitely
generated `J' ⊆ P'` and a flat `P'`-algebra `Q'` with `P'/J' = Q'/J'Q'`, an element which lies in
the submodule after inverting every `g ∈ J'`, and after base change to `Q'`, lies in it. That is
the group the hypotheses of Stacks 0DZ2 kill, and
`Deformation.Obligation.exists_linearCorrection_of_local` turns it into the existence of the
correction in one degree.

At the nonlinear window no such transfer exists in the abstract. The local-to-global principle for
an equation `∂(e) + e ∘ e = ω` with `∂` merely `P`-linear is **false**: already three equations in
three unknowns over `𝔽₂[y]`, with `J = (y)` and `Q = 𝔽₂[y][1/(1+y)]`, satisfy every hypothesis of
Stacks 05EC and have local solutions on two different branches of an idempotent and none globally.
The solution set of such a system is a quadric and not a torsor, so it has disjoint branches on
which existence-only local data can sit, and there is nothing to glue them with.
`Deformation.Examples.MaurerCartan.not_exists_coset_isSquare` is the weaker statement that the
reachable obstructions are not a coset of a submodule. So the nilpotent form of Stacks 0DZ2 needs
an input specific to *obstruction* classes, and it needs it only at the window `m = 1`.

**But the structured realization of that window is solvable, so the abstract failure does not
descend to it.** The counterexample to the nilpotent form was being sought at the instance
`A' = 𝔽₂[t]/t³`, `R = 𝔽₂[y]`, `P' = A'[y, x]/(x² - t·x)`, `J' = (y)·P'`, `Q' = P'[1/(1 + y)]`,
where the `A'`-flat `P'`-module lifts of `M = R^n` with `x` acting by a square-zero matrix `X₀`
are *exactly* the pairs of matrices `(α, β)` over `R` with `X₀α + αX₀ = X₀` and
`α² + α + X₀β + βX₀ = 0` — the window `m = 1` written in coordinates, with `α` the first-order
correction and `β` the second-order one
(`Deformation.Examples.MaurerCartanWindow.lift3_sq_eq_tau_smul_iff`). Reading the first equation
as `X₀ ∘ α = (1 - α) ∘ X₀`, any **idempotent** `α` with image `ker X₀` satisfies it, since
`im X₀ ⊆ ker X₀`; and then `α² - α = 0`, so `β = 0` solves the second. Such an `α` exists
whenever `ker X₀` is a direct summand, i.e. whenever `im X₀` is projective
(`Deformation.Examples.MaurerCartanWindow.hasWindowSolution_of_projective_quotient`) — which over
the principal ideal domain `𝔽₂[y]` is automatic. So **every** `M = R^n` in that family lifts,
for every `n` and every `X₀`
(`Deformation.Examples.MaurerCartanWindow.exists_flat_lift_system`), and in particular the
two-Jordan-block instance `X₀ = J_y ⊕ J_{1+y}` at `n = 4` lifts with the explicit witness
`α = diag(1, 0, 1, 0)`, `β = 0`
(`Deformation.Examples.MaurerCartanWindow.jordanPair_flat_lift_system`). The quadratic term
vanishes identically there, so the two coboundary slack ideals `(y)` and `(1 + y)` are never
called on: the branch variable of the quadric is pinned to an idempotent rather than being forced
off every branch. A counterexample of this shape would need `im X₀` non-projective, hence a base
that is not a Dedekind domain, *and* no complemented submodule between `im X₀` and `ker X₀` —
while `D(y) ∪ D(1 + y)` is all of `Spec R`, so the non-projectivity cannot be arranged to
disappear on the cover. See `StacksFrontier.Deformation.Examples.Linear.MaurerCartanWindowSolvable`.

**The window is not solvable unconditionally, so the hypotheses must be consumed at it.** The
projectivity hypothesis above is not removable: a square-zero element `s` of a commutative ring
solving the window is zero
(`Deformation.Examples.MaurerCartanWindow.eq_zero_of_hasWindowSolution`), so the window fails
already at the rank-one module over `R = k[s]/(s²)` with `x` acting by `s`. That is not a
counterexample to Stacks 0DZ2 — the `P'` of that instance is artinian local, so `Spec(P')` is a
point and no `(J', Q')` satisfying the lemma's hypotheses is available there — but it does show
that the remaining gap is exactly the *local-to-global* question for the window and not the
unconditional one. The branch-splitting mechanism of the abstract refutation does not transport
to it either: the window's solution set is symmetric under `α ↦ 1 - α` with the same `β`
(`Deformation.Examples.MaurerCartanWindow.window_sol_one_sub`), so existence-only local data is
never pinned to one branch of the quadric. See
`StacksFrontier.Deformation.Examples.Linear.MaurerCartanWindowObstructed`.

## Main definitions

* `Deformation.Obligation.SquareZeroCorrection`: a degree-one cochain on a free differential
  lift, valued in `ker f · L`, whose addition to the lifted differential makes it square to zero.
  Indexed by pairs of degrees with a vanishing condition off the degree-one diagonal, exactly as
  `Deformation.Obstruction.FreeDifferentialLift.d` is.
* `Deformation.Obligation.HasSquareZeroCorrection`: the existence of such a cochain — the
  solvability of the Maurer–Cartan equation of the lift.
* `Deformation.Obligation.SquareZeroCorrection.lift`: the corrected free differential lift, whose
  differential squares to zero, and `.complex`: the resulting complex of free `R'`-modules.

## Main results

* `Deformation.Obligation.curvature_mem`: the curvature `L.d ∘ L.d` is valued in `ker f · L`, so
  the Maurer–Cartan equation is the right equation to solve.
* `Deformation.Obligation.curvature_add`: **the exact variation of the curvature**, Bockstein plus
  Yoneda square.
* `Deformation.Obligation.curvature_add_sub_mem_of_two_le`: **above the first window the curvature
  varies linearly.** The Yoneda square of a correction valued in `𝔞^m · L` is valued in
  `𝔞^(m+m) · L ⊆ 𝔞^(m+2) · L` once `2 ≤ m`, so the whole nonlinearity of the dévissage is
  concentrated in the single window `m = 1`.
* `Deformation.Obligation.SquareZeroCorrection.baseChange`: a correction base-changes, so the
  hypotheses of the glueing problem are necessary conditions.
* `Deformation.Obligation.mem_of_formalGlueing`: **membership in a submodule is detected by the
  formal glueing data.** An element of a `P'`-module which lands in a submodule after inverting
  every element of a finitely generated `J'`, and after base change to a flat `Q'` with
  `P'/J' = Q'/J'Q'`, lands in it. This is Stacks 05EC read on the quotient module.
* `Deformation.Obligation.exists_linearCorrection_of_local`: **one degree of the Maurer–Cartan
  equation glues along `(J', Q')`.** For `u : M → N` with `M` free and `v : N → K`, if `v (u x)`
  lies in `v (𝔞 · N)` locally on `J'` and over `Q'`, then there is a *global* `ε : M → N` valued
  in `𝔞 · N` with `v ∘ (u + ε) = 0`.
* `Deformation.Obligation.exists_correction_step_of_local`: the same statement in the language of
  a free differential lift: the degree-`n` component of a square-zero correction exists globally
  as soon as it exists after inverting every `g ∈ J'` and over `Q'`, the corrected differential
  in degree `n + 1` being fixed.
* `Deformation.Obligation.X_eq_bot_of_subsingleton`: where `F` vanishes the lifted terms vanish,
  by Nakayama for the nilpotent ideal `ker f`. So on a strictly bounded-above complex a correction
  is forced to be zero above the bound and the Maurer–Cartan equation holds automatically there:
  this is the base of the descending induction on degree.

## References

* [Stacks Project, Tag 0DZ1](https://stacks.math.columbia.edu/tag/0DZ1)
* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Deformation.Obligation

/-! ### Membership in a submodule is a formal glueing question -/

/-- **Membership in a submodule is detected by the formal glueing data.** Let `J' ⊆ P'` be a
finitely generated ideal and `Q'` a flat `P'`-algebra with `P'/J' = Q'/J'Q'`. An element `m` of a
`P'`-module which lands in a submodule `N` after multiplication by a power of each `g ∈ J'`, and
whose class modulo `N` dies after base change to `Q'`, already lies in `N`.

This is Stacks 05EC applied to `M ⧸ N`: the class of `m` is `J'`-power torsion by the first
hypothesis, and base change is injective on `J'`-power torsion. It is the only local-to-global
input the Maurer–Cartan equation of a free differential lift needs in each degree. -/
theorem mem_of_formalGlueing {P' Q' : Type u} [CommRing P'] [CommRing Q'] [Algebra P' Q']
    (J' : Ideal P') (hJ'fg : J'.FG) (hflat : Module.Flat P' Q')
    (hquot : Function.Bijective
      (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q') Ideal.le_comap_map))
    {M : Type u} [AddCommGroup M] [Module P' M] {N : Submodule P' M} {m : M}
    (hloc : ∀ g ∈ J', ∃ k : ℕ, g ^ k • m ∈ N)
    (hQ : (1 : Q') ⊗ₜ[P'] (N.mkQ m) = 0) : m ∈ N := by
  have htors : ∀ g ∈ J', ∃ k : ℕ, g ^ k • (N.mkQ m) = 0 := by
    intro g hg
    obtain ⟨k, hk⟩ := hloc g hg
    refine ⟨k, ?_⟩
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero N).mpr hk
  have h := Deformation.eq_zero_iff_one_tmul_eq_zero_of_localization.{u, u}
    (R := P') (S := Q') J' hJ'fg hflat hquot (M := M ⧸ N) (m := N.mkQ m) htors
  exact (Submodule.Quotient.mk_eq_zero N).mp (h.mpr hQ)

/-- **One degree of the Maurer–Cartan equation glues along `(J', Q')`.** Let `M` be a free
`P'`-module, `u : M →ₗ N` and `v : N →ₗ K`, and let `𝔞 ⊆ P'` be an ideal. If for every `x : M`
the element `v (u x)` lies in the submodule `v (𝔞 · N)` after multiplication by a power of each
`g ∈ J'`, and its class dies after base change to `Q'`, then there is a *global* correction
`ε : M →ₗ N` valued in `𝔞 · N` with `v ∘ (u + ε) = 0`.

Freeness of `M` is what turns the pointwise membership into a linear correction: the correction
is chosen on a basis and extended linearly. -/
theorem exists_linearCorrection_of_local {P' Q' : Type u} [CommRing P'] [CommRing Q']
    [Algebra P' Q'] (J' : Ideal P') (hJ'fg : J'.FG) (hflat : Module.Flat P' Q')
    (hquot : Function.Bijective
      (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q') Ideal.le_comap_map))
    (𝔞 : Ideal P') {M N K : Type u} [AddCommGroup M] [Module P' M] [Module.Free P' M]
    [AddCommGroup N] [Module P' N] [AddCommGroup K] [Module P' K]
    (u : M →ₗ[P'] N) (v : N →ₗ[P'] K)
    (hloc : ∀ x : M, ∀ g ∈ J', ∃ k : ℕ,
      g ^ k • v (u x) ∈ Submodule.map v (𝔞 • (⊤ : Submodule P' N)))
    (hQ : ∀ x : M, (1 : Q') ⊗ₜ[P']
      (Submodule.map v (𝔞 • (⊤ : Submodule P' N))).mkQ (v (u x)) = 0) :
    ∃ ε : M →ₗ[P'] N, LinearMap.range ε ≤ 𝔞 • (⊤ : Submodule P' N) ∧ v ∘ₗ (u + ε) = 0 := by
  classical
  have hmem : ∀ x : M, v (u x) ∈ Submodule.map v (𝔞 • (⊤ : Submodule P' N)) := fun x =>
    mem_of_formalGlueing J' hJ'fg hflat hquot (hloc x) (hQ x)
  set b := Module.Free.chooseBasis P' M with hb
  choose y hy hvy using fun i => Submodule.mem_map.mp (hmem (b i))
  refine ⟨b.constr P' (fun i => -(y i)), ?_, ?_⟩
  · rintro z ⟨x, rfl⟩
    rw [Module.Basis.constr_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (hy i))
  · refine b.ext fun i => ?_
    have hεi : (b.constr P' (fun i => -(y i))) (b i) = -(y i) := by
      simp
    simp only [LinearMap.comp_apply, LinearMap.add_apply, hεi, map_add, map_neg, hvy i,
      LinearMap.zero_apply]
    rw [add_neg_cancel]

/-! ### Square-zero corrections -/

variable {R' R : Type u} [CommRing R'] [CommRing R]

/-- **The curvature of a free differential lift is valued in `ker f · L`.** The square of the
lifted differential reduces to the square of the differential of `F`, which vanishes; so it lies
in the kernel of the reduction, which is `ker f · L`. This is why the Maurer–Cartan equation
`(L.d + ε)² = 0` can be asked for with `ε` valued in `ker f · L`, and is the cocycle representing
the canonical obstruction morphism of Stacks 0DYR. -/
theorem curvature_mem {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Obstruction.FreeDifferentialLift f F) (i j k : ℤ) (x : L.X i) :
    L.d j k (L.d i j x) ∈ RingHom.ker f • (⊤ : Submodule R' (L.X k)) := by
  rw [← L.reduction_ker, LinearMap.mem_ker, L.reduction_d, L.reduction_d]
  change (F.d i j ≫ F.d j k) (L.reduction i x) = 0
  rw [F.d_comp_d]
  rfl

/-- **A square-zero correction of a free differential lift.** A degree-one cochain `ε` on `L`
valued in `ker f · L` whose addition to the lifted differential makes it square to zero: a
solution of the Maurer–Cartan equation `(L.d + ε)² = 0` of the lift.

The cochain is indexed by pairs of degrees with `shape` forcing it to vanish away from the
degree-one diagonal, exactly as `Deformation.Obstruction.FreeDifferentialLift.d` is; this keeps
the square-zero condition free of transports along `n + 1 + 1 = n + 2`.

By `Deformation.Obligation.SquareZeroCorrection.lift` such a cochain is the same thing as a lift
of `F` to a complex of free `R'`-modules on the terms `L.X` and with the reduction of `L`, which
is the criterion of Stacks 0DZ1 written on a free presentation. -/
structure SquareZeroCorrection {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Obstruction.FreeDifferentialLift f F) where
  /-- The components of the correction. -/
  ε (i j : ℤ) : L.X i ⟶ L.X j
  /-- The correction vanishes away from the degree-one diagonal. -/
  shape (i j : ℤ) (h : i + 1 ≠ j) : ε i j = 0
  /-- The correction is valued in `ker f · L`. -/
  range_le (i j : ℤ) :
    LinearMap.range (ε i j).hom ≤ RingHom.ker f • (⊤ : Submodule R' (L.X j))
  /-- The Maurer–Cartan equation: the corrected differential squares to zero. -/
  d_comp_d (i j k : ℤ) : (L.d i j + ε i j) ≫ (L.d j k + ε j k) = 0

/-- **The Maurer–Cartan equation of a free differential lift is solvable.** The existence of a
`Deformation.Obligation.SquareZeroCorrection`: a degree-one cochain valued in `ker f · L` whose
addition to the lifted differential makes it square to zero.

This is the condition which the nilpotent form of Stacks 0DZ2 has to transfer from `Q'` and from
the localizations `(P')_g`, `g ∈ J'`, back to `P'`. -/
def HasSquareZeroCorrection {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Obstruction.FreeDifferentialLift f F) : Prop :=
  Nonempty (SquareZeroCorrection L)

namespace SquareZeroCorrection

variable {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
  {L : Obstruction.FreeDifferentialLift f F} (c : SquareZeroCorrection L)

/-- A correction is killed by the reduction, since it is valued in `ker f · L`. -/
lemma reduction_ε (i j : ℤ) (x : L.X i) : L.reduction j (c.ε i j x) = 0 := by
  rw [← LinearMap.mem_ker, L.reduction_ker]
  exact c.range_le i j ⟨x, rfl⟩

/-- **The corrected lift.** The free differential lift of `F` with the same terms and the same
reduction as `L`, and with differential `L.d + ε`. Its differential squares to zero, by
`Deformation.Obligation.SquareZeroCorrection.lift_d_comp_d`. -/
def lift : Obstruction.FreeDifferentialLift f F where
  X := L.X
  free := L.free
  d i j := L.d i j + c.ε i j
  shape i j h := by rw [L.shape i j h, c.shape i j h, add_zero]
  reduction := L.reduction
  reduction_surjective := L.reduction_surjective
  reduction_ker := L.reduction_ker
  reduction_d i j x := by
    change L.reduction j (L.d i j x + c.ε i j x) = F.d i j (L.reduction i x)
    rw [map_add, L.reduction_d, c.reduction_ε, add_zero]

/-- The corrected lift has the same terms as `L`. -/
@[simp] lemma lift_X (n : ℤ) : c.lift.X n = L.X n := rfl

/-- The differential of the corrected lift is `L.d + c.ε`. -/
@[simp] lemma lift_d (i j : ℤ) : c.lift.d i j = L.d i j + c.ε i j := rfl

/-- The corrected lift has the same reduction as `L`. -/
@[simp] lemma lift_reduction (n : ℤ) : c.lift.reduction n = L.reduction n := rfl

/-- The differential `L.d + c.ε` of the corrected lift squares to zero. -/
lemma lift_d_comp_d (i j k : ℤ) : c.lift.d i j ≫ c.lift.d j k = 0 := c.d_comp_d i j k

/-- **The complex a square-zero correction produces.** The terms of `L`, which are free
`R'`-modules, with the corrected differential. Its reduction is `F`, by
`Deformation.Obligation.SquareZeroCorrection.reduction_complex_d`: so a square-zero correction is
exactly a lift of `F` to a complex of free `R'`-modules on the given terms. -/
def complex : CochainComplex (ModuleCat.{u} R') ℤ where
  X := L.X
  d i j := L.d i j + c.ε i j
  shape i j h := by
    rw [L.shape i j (by simpa [ComplexShape.up_Rel] using h),
      c.shape i j (by simpa [ComplexShape.up_Rel] using h), add_zero]
  d_comp_d' i j k _ _ := c.d_comp_d i j k

/-- The corrected complex has the same terms as `L`. -/
@[simp] lemma complex_X (n : ℤ) : c.complex.X n = L.X n := rfl

/-- The differential of the corrected complex is `L.d + c.ε`. -/
@[simp] lemma complex_d (i j : ℤ) : c.complex.d i j = L.d i j + c.ε i j := rfl

/-- Every term of the corrected complex is a free `R'`-module. -/
lemma complex_free (n : ℤ) : Module.Free R' (c.complex.X n) := L.free n

/-- The corrected differential still reduces to the differential of `F`. -/
lemma reduction_complex_d (i j : ℤ) (x : L.X i) :
    L.reduction j (c.complex.d i j x) = F.d i j (L.reduction i x) :=
  c.lift.reduction_d i j x

end SquareZeroCorrection

/-- **A square-zero differential on the terms of `L` is a square-zero correction.** Let `D` be
any system of maps on the terms of `L` which vanishes off the degree-one diagonal, reduces to the
differential of `F`, and squares to zero. Then `D - L.d` is a square-zero correction of `L`.

Together with `Deformation.Obligation.SquareZeroCorrection.lift` this identifies the Maurer–Cartan
equation of `L` with the problem of lifting `F` to a complex of free `R'`-modules on the terms of
`L` and with its reduction: the criterion of Stacks 0DZ1 on a free presentation. In particular
`Deformation.Obligation.HasSquareZeroCorrection L` does not depend on the chosen lifted
differential `L.d`, only on the terms and the reduction. -/
def squareZeroCorrection_of_d {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Obstruction.FreeDifferentialLift f F) (D : ∀ i j : ℤ, L.X i ⟶ L.X j)
    (hshape : ∀ i j : ℤ, i + 1 ≠ j → D i j = 0)
    (hred : ∀ (i j : ℤ) (x : L.X i), L.reduction j (D i j x) = F.d i j (L.reduction i x))
    (hsq : ∀ i j k : ℤ, D i j ≫ D j k = 0) :
    SquareZeroCorrection L where
  ε i j := D i j - L.d i j
  shape i j h := by rw [hshape i j h, L.shape i j h, sub_zero]
  range_le i j := by
    rintro z ⟨x, rfl⟩
    rw [← L.reduction_ker, LinearMap.mem_ker]
    have h : ((D i j - L.d i j).hom x : L.X j) = D i j x - L.d i j x := rfl
    rw [h, map_sub, L.reduction_d, hred i j x, sub_self]
  d_comp_d i j k := by
    have h : ∀ a b : ℤ, L.d a b + (D a b - L.d a b) = D a b := by
      intro a b; rw [add_sub_cancel]
    rw [h, h]
    exact hsq i j k

/-! ### The variation of the curvature, and where it is quadratic -/

/-- A linear map valued in `J · N`, applied to an element of `I · M`, lands in `(I * J) · N`. -/
lemma map_mem_mul_smul {M N : Type u} [AddCommGroup M] [Module R' M] [AddCommGroup N]
    [Module R' N] (φ : M →ₗ[R'] N) (I J : Ideal R')
    (hφ : LinearMap.range φ ≤ J • (⊤ : Submodule R' N)) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R' M)) : φ x ∈ (I * J) • (⊤ : Submodule R' N) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr v _
    rw [map_smul, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (hφ ⟨v, rfl⟩)
  · intro v w hv hw
    rw [map_add]
    exact Submodule.add_mem _ hv hw

variable {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}

/-- **The exact variation of the curvature.** Adding a cochain `z` to the lifted differential
changes its square by the twisted Bockstein `d z + z d` *and* by the quadratic term `z z`:

`(d + z)² = d² + (d z + z d) + z z`.

The quadratic term is the Yoneda square of `z`. It is the whole reason the dévissage of the
nilpotent form of Stacks 0DZ2 is not a linear local-to-global problem: the reachable obstructions
are the image of a quadratic map, which is a quadric and not a coset
(`Deformation.Examples.MaurerCartan.not_exists_coset_isSquare`), and a quadric has disjoint
branches on which existence-only local data can sit. -/
theorem curvature_add (L : Obstruction.FreeDifferentialLift f F)
    (z : ∀ i j : ℤ, L.X i ⟶ L.X j) (i j k : ℤ) (x : L.X i) :
    (L.d j k + z j k) ((L.d i j + z i j) x) =
      (L.d j k (L.d i j x) + (L.d j k (z i j x) + z j k (L.d i j x))) + z j k (z i j x) := by
  have h1 : (L.d i j + z i j) x = L.d i j x + z i j x := rfl
  have h2 : ∀ w : L.X j, (L.d j k + z j k) w = L.d j k w + z j k w := fun _ => rfl
  rw [h1, h2, map_add, map_add]
  abel

/-- **The quadratic term lies two filtration steps deeper.** A cochain valued in `𝔞^m · L` has
Yoneda square valued in `𝔞^(m + m) · L`. -/
theorem quadratic_term_mem (L : Obstruction.FreeDifferentialLift f F)
    (z : ∀ i j : ℤ, L.X i ⟶ L.X j) (m : ℕ)
    (hz : ∀ i j : ℤ, LinearMap.range (z i j).hom ≤
      (RingHom.ker f ^ m) • (⊤ : Submodule R' (L.X j)))
    (i j k : ℤ) (x : L.X i) :
    z j k (z i j x) ∈ (RingHom.ker f ^ (m + m)) • (⊤ : Submodule R' (L.X k)) := by
  have h := map_mem_mul_smul (z j k).hom (RingHom.ker f ^ m) (RingHom.ker f ^ m) (hz j k)
    (hz i j ⟨x, rfl⟩)
  rwa [← pow_add] at h

/-- **Above the first window the curvature varies linearly.** Let `𝔞 = ker f`. A cochain `z`
valued in `𝔞^m · L` with `2 ≤ m` changes the curvature by the Bockstein `d z + z d` *modulo*
`𝔞^(m+2) · L`: its Yoneda square lies in `𝔞^(m+m) ⊆ 𝔞^(m+2)`.

Run the dévissage of Stacks 0DZ2 along the `𝔞`-adic filtration — each step `A'/I^(j+1) → A'/I^j`
is square-zero, so the square-zero case applies at every step — and this says that the
*only* window at which the choice perturbs the next obstruction quadratically is `m = 1`: the
dependence of the level-`2` obstruction on the first-order correction. At `m = 0` there is no
choice to perturb, since the lifted differential `L.d` is given. So the whole nonlinearity of the
nilpotent form of Stacks 0DZ2 is concentrated in a single window, and
`Deformation.Examples.Linear.PartialLiftObstruction` is a counterexample at exactly that window:
over `A' = ℤ/8` the partial lift `M₂ = ℤ/4` of `M = 𝔽₂` does not lift, while `M` does. -/
theorem curvature_add_sub_mem_of_two_le (L : Obstruction.FreeDifferentialLift f F)
    (z : ∀ i j : ℤ, L.X i ⟶ L.X j) {m : ℕ} (hm : 2 ≤ m)
    (hz : ∀ i j : ℤ, LinearMap.range (z i j).hom ≤
      (RingHom.ker f ^ m) • (⊤ : Submodule R' (L.X j)))
    (i j k : ℤ) (x : L.X i) :
    (L.d j k + z j k) ((L.d i j + z i j) x) -
        (L.d j k (L.d i j x) + (L.d j k (z i j x) + z j k (L.d i j x))) ∈
      (RingHom.ker f ^ (m + 2)) • (⊤ : Submodule R' (L.X k)) := by
  rw [curvature_add L z i j k x, add_sub_cancel_left]
  refine Submodule.smul_mono_left ?_ (quadratic_term_mem L z m hz i j k x)
  exact Ideal.pow_le_pow_right (by omega)

/-! ### Base change of a square-zero correction -/

/-- Base change carries a linear map valued in `I · N` to one valued in `J · (S' ⊗ N)`, for any
ideal `J` of `S'` containing the image of `I`. -/
lemma range_baseChange_le_smul {S' : Type u} [CommRing S'] [Algebra R' S']
    {M N : Type u} [AddCommGroup M] [Module R' M] [AddCommGroup N] [Module R' N]
    (φ : M →ₗ[R'] N) (I : Ideal R') (Jd : Ideal S')
    (hIJ : ∀ r ∈ I, algebraMap R' S' r ∈ Jd)
    (hφ : LinearMap.range φ ≤ I • (⊤ : Submodule R' N)) :
    LinearMap.range (LinearMap.baseChange S' φ) ≤ Jd • (⊤ : Submodule S' (S' ⊗[R'] N)) := by
  rintro z ⟨w, rfl⟩
  induction w with
  | tmul s y =>
      rw [LinearMap.baseChange_tmul]
      refine Submodule.smul_induction_on (hφ ⟨y, rfl⟩) ?_ ?_
      · intro r hr v _
        have hsm : (s ⊗ₜ[R'] (r • v) : S' ⊗[R'] N) = (algebraMap R' S' r) • (s ⊗ₜ[R'] v) := by
          rw [TensorProduct.tmul_smul, ← algebraMap_smul S' r (s ⊗ₜ[R'] v)]
        rw [hsm]
        exact Submodule.smul_mem_smul (hIJ r hr) Submodule.mem_top
      · intro v w hv hw
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hv hw
  | add v w hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw

/-- **A square-zero correction base-changes.** For a commuting square of ring maps whose two
vertical maps are surjective, a square-zero correction of `L` gives one of the base-changed lift
`Deformation.Obstruction.FreeDifferentialLift.baseChange`.

So `Deformation.Obligation.HasSquareZeroCorrection` is inherited by base change: the hypotheses
of the glueing problem — a correction over `Q'` and over each `(P')_g` — are *necessary* for a
correction over `P'`, and the glueing question is whether they are sufficient. -/
noncomputable def SquareZeroCorrection.baseChange {S' S : Type u} [CommRing S'] [CommRing S]
    {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Obstruction.FreeDifferentialLift f F} (c : SquareZeroCorrection L)
    (hf : Function.Surjective f) {fS : S' →+* S} (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp f = fS.comp a) :
    letI : Algebra R' S' := a.toAlgebra
    letI : Algebra R S := b.toAlgebra
    SquareZeroCorrection (L.baseChange hf hfS a b hcomm) := by
  letI : Algebra R' S' := a.toAlgebra
  letI : Algebra R S := b.toAlgebra
  have hker : ∀ r ∈ RingHom.ker f, algebraMap R' S' r ∈ RingHom.ker fS := by
    intro r hr
    have hr' := congrArg (fun φ => φ r) hcomm
    simp only [RingHom.coe_comp, Function.comp_apply] at hr'
    rw [RingHom.mem_ker, show algebraMap R' S' r = a r from rfl, ← hr',
      RingHom.mem_ker.mp hr, map_zero]
  have hdeq : ∀ p q : ℤ, (L.baseChange hf hfS a b hcomm).d p q =
      ModuleCat.ofHom (LinearMap.baseChange S' (L.d p q).hom) := fun _ _ => rfl
  refine
    { ε := fun i j => ModuleCat.ofHom (LinearMap.baseChange S' (c.ε i j).hom)
      shape := fun i j h => ?_
      range_le := fun i j => ?_
      d_comp_d := fun i j k => ?_ }
  · have h0 : LinearMap.baseChange S' (c.ε i j).hom = 0 := by
      rw [show (c.ε i j).hom = 0 by rw [c.shape i j h]; rfl, LinearMap.baseChange_zero]
    rw [h0]
    exact ModuleCat.ofHom_zero
  · exact range_baseChange_le_smul (c.ε i j).hom (RingHom.ker f) (RingHom.ker fS) hker
      (c.range_le i j)
  · have hcx : ∀ y : L.X i, (L.d j k).hom ((L.d i j).hom y + (c.ε i j).hom y) +
        (c.ε j k).hom ((L.d i j).hom y + (c.ε i j).hom y) = 0 := by
      intro y
      have h := congrArg (fun φ => ModuleCat.Hom.hom φ y) (c.d_comp_d i j k)
      simpa using h
    have key : ((LinearMap.baseChange S' (L.d j k).hom +
          LinearMap.baseChange S' (c.ε j k).hom) ∘ₗ
        (LinearMap.baseChange S' (L.d i j).hom +
          LinearMap.baseChange S' (c.ε i j).hom)) = 0 := by
      refine LinearMap.ext fun w => ?_
      induction w using TensorProduct.inductionOn with
      | tmul s y =>
          simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.baseChange_tmul,
            ← TensorProduct.tmul_add, hcx y, TensorProduct.tmul_zero, LinearMap.zero_apply]
      | add v w hv hw => simp only [map_add, hv, hw, add_zero, LinearMap.zero_apply]
    exact ModuleCat.hom_ext key

/-! ### The base of the descending induction on degree -/

/-- **Above the bound the lifted terms vanish.** If `F.X n = 0` and `ker f` is nilpotent then
`L.X n = 0`: the reduction is surjective with kernel `ker f · L.X n`, so `L.X n = ker f · L.X n`,
and Nakayama for a nilpotent ideal forces it to be zero.

So on a strictly bounded-above complex a square-zero correction is forced to be zero above the
bound and the Maurer–Cartan equation holds there automatically; this is the base of the
descending induction on degree. -/
theorem X_eq_bot_of_subsingleton {f : R' →+* R} {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Obstruction.FreeDifferentialLift f F) (hnil : IsNilpotent (RingHom.ker f)) (n : ℤ)
    (hF : ∀ y : F.X n, y = 0) : ∀ x : L.X n, x = 0 := by
  have htop : (⊥ : Submodule R' (L.X n)) ⊔ RingHom.ker f • (⊤ : Submodule R' (L.X n)) = ⊤ := by
    rw [bot_sup_eq, ← L.reduction_ker]
    refine le_antisymm le_top fun x _ => ?_
    rw [LinearMap.mem_ker]
    exact hF _
  have hbot := Submodule.eq_top_of_sup_ideal_smul_top_eq_top hnil htop
  intro x
  have hx : x ∈ (⊥ : Submodule R' (L.X n)) := by rw [hbot]; exact Submodule.mem_top
  simpa using hx

/-- **One degree of a square-zero correction glues along `(J', Q')`.** With the corrected
differential `D` in degree `n + 1` fixed, the degree-`n` component of a square-zero correction
exists globally as soon as the corresponding membership holds after inverting every `g ∈ J'` and
after base change to `Q'`.

This is `Deformation.Obligation.exists_linearCorrection_of_local` read on a free differential
lift over `P'`: the equation `(L.d + ε) ≫ D = 0` to be solved for `ε` valued in `ker f · L` is
linear, and solvability is membership of `D (L.d x)` in the submodule `D (ker f · L.X (n+1))`,
which Stacks 05EC transfers. -/
theorem exists_correction_step_of_local {P' Q' : Type u} [CommRing P'] [CommRing Q']
    [Algebra P' Q'] (J' : Ideal P') (hJ'fg : J'.FG) (hflat : Module.Flat P' Q')
    (hquot : Function.Bijective
      (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q') Ideal.le_comap_map))
    {P : Type u} [CommRing P] {f : P' →+* P} {F : CochainComplex (ModuleCat.{u} P) ℤ}
    (L : Obstruction.FreeDifferentialLift f F) (n : ℤ) (D : L.X (n + 1) ⟶ L.X (n + 2))
    (hloc : ∀ x : L.X n, ∀ g ∈ J', ∃ k : ℕ, g ^ k • D (L.d n (n + 1) x) ∈
      Submodule.map D.hom (RingHom.ker f • (⊤ : Submodule P' (L.X (n + 1)))))
    (hQ : ∀ x : L.X n, (1 : Q') ⊗ₜ[P']
      (Submodule.map D.hom
        (RingHom.ker f • (⊤ : Submodule P' (L.X (n + 1))))).mkQ (D (L.d n (n + 1) x)) = 0) :
    ∃ ε : L.X n ⟶ L.X (n + 1),
      LinearMap.range (ε).hom ≤ RingHom.ker f • (⊤ : Submodule P' (L.X (n + 1))) ∧
      (L.d n (n + 1) + ε) ≫ D = 0 := by
  have : Module.Free P' (L.X n) := L.free n
  obtain ⟨e, hrange, hcomp⟩ := exists_linearCorrection_of_local J' hJ'fg hflat hquot
    (RingHom.ker f) (L.d n (n + 1)).hom D.hom hloc hQ
  refine ⟨ModuleCat.ofHom e, hrange, ?_⟩
  ext x
  have h := congrArg (fun φ => φ x) hcomp
  simpa using h

end Deformation.Obligation

end
