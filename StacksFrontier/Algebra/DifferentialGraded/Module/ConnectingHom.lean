module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift

/-!
# The connecting homomorphism of an admissible short exact sequence

Let `K → L → M` be an admissible short exact sequence of right differential graded modules and
let `s : M → L` and `π : L → K` be compatible graded splittings of it. Then `π ∘ d_L ∘ s` is a
homomorphism of differential graded modules `M ⟶ K[1]`: the connecting homomorphism of the
sequence. Two compatible pairs of splittings give homotopic connecting homomorphisms, hence the
same morphism of the homotopy category; so the connecting arrow of the triangle of an admissible
short exact sequence does not depend on the splittings used to write it down.

## Main definitions

* `DifferentialGradedModule.connectingHom`: the connecting homomorphism, bundled with the formula
  `δ x = π (d_L (s x))` that specifies it.

## Main results

* `DifferentialGradedModule.IsAdmissibleShortExact.decomposition`: the pointwise splitting
  `f (π y) + s (g y) = y` of the middle term.
* `DifferentialGradedModule.connectingHom_homotopic`: the connecting homomorphisms of two
  compatible pairs of splittings are homotopic.
* `DifferentialGradedModule.toHomotopyCategory_map_connectingHom_eq`: hence they agree in the
  homotopy category.

## Implementation notes

The splittings are graded homomorphisms, i.e. they need not commute with the differentials; it is
exactly the failure of `s` to commute with them that the connecting homomorphism measures. The
hypotheses `hs`, `hπ` and `hker` are the compatibility of the two splittings, in the form used by
the source: `g ∘ s = id`, `π ∘ f = id`, and `ker π = im s`. From them the pointwise splitting
`f (π y) + s (g y) = y` of the middle term is derived, and it is what makes `π ∘ d_L ∘ s`
commute with the differentials after the shift.

The homotopy between the two connecting homomorphisms is `π ∘ (s' - s)`, which lands in `K`
because `s' - s` kills `g` and the sequence is exact.

## References

* [Stacks Project, Tag 09JU](https://stacks.math.columbia.edu/tag/09JU)
* [Stacks Project, Tag 09K6](https://stacks.math.columbia.edu/tag/09K6)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {K L M : DifferentialGradedModule A}

/-- If the kernel of `p` is the range of `t`, then `p ∘ t = 0`. -/
private theorem apply_eq_zero_of_ker_eq_range {V W X : Type*} [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup X] [Module R V] [Module R W] [Module R X] {p : V →ₗ[R] W} {t : X →ₗ[R] V}
    (h : LinearMap.ker p = LinearMap.range t) (x : X) : p (t x) = 0 :=
  LinearMap.mem_ker.mp (h ▸ LinearMap.mem_range_self t x)

/-- Compatible graded splittings of an admissible short exact sequence decompose the middle term
pointwise: `f (π y) + s (g y) = y`, the elementwise form of `L = f(K) ⊕ s(M)`. The hypotheses are
the source's, `g ∘ s = id`, `π ∘ f = id` and `ker π = im s`; the decomposition is what they are
good for, and it is what the degreewise `ShortComplex.Splitting` of the underlying sequence of
cochain complexes asks for. -/
theorem IsAdmissibleShortExact.decomposition {f : Hom K L} {g : Hom L M}
    (hfg : IsAdmissibleShortExact f g) {s : GradedHom M L} {π : GradedHom L K}
    (hs : ∀ x : M.M, g.toFun (s.toFun x) = x)
    (hπ : ∀ x : K.M, π.toFun (f.toFun x) = x)
    (hker : LinearMap.ker π.toFun = LinearMap.range s.toFun) (y : L.M) :
    f.toFun (π.toFun y) + s.toFun (g.toFun y) = y := by
  have hgf := apply_eq_zero_of_ker_eq_range hfg.exact.symm
  have hpi_s := apply_eq_zero_of_ker_eq_range hker
  let q := y - f.toFun (π.toFun y) - s.toFun (g.toFun y)
  have hqπ : π.toFun q = 0 := by simp [q, hπ, hpi_s]
  have hqg : g.toFun q = 0 := by simp [q, hgf, hs]
  obtain ⟨z, hz⟩ : q ∈ LinearMap.range s.toFun := by
    rw [← hker]
    exact hqπ
  have hz0 : z = 0 := by rw [← hs z, hz, hqg]
  have hq0 : q = 0 := by simpa [hz0] using hz.symm
  dsimp [q] at hq0
  have hy := sub_eq_zero.mp hq0
  rw [sub_eq_iff_eq_add] at hy
  simpa [add_comm] using hy.symm

/-- The connecting homomorphism `M ⟶ K[1]` associated to graded splittings of an admissible short
exact sequence of differential graded modules, bundled with the formula `δ x = π (d_L (s x))`.

This is the first half of Stacks 09JU: the family `π ∘ d_L ∘ s` is a morphism of
`Mod_{(A,d)}`, i.e. it is `A`-linear, of degree `0` as a map into the shift, and commutes with
the differentials. -/
@[stacks 09JU "clause (i): δ = π ∘ d_L ∘ s is a morphism M ⟶ K[1] of differential graded A-modules"]
noncomputable def connectingHom (f : Hom K L) (g : Hom L M)
    (hfg : IsAdmissibleShortExact f g) (s : GradedHom M L) (π : GradedHom L K)
    (hs : ∀ x : M.M, g.toFun (s.toFun x) = x)
    (hπ : ∀ x : K.M, π.toFun (f.toFun x) = x)
    (hker : LinearMap.ker π.toFun = LinearMap.range s.toFun) :
    {δ : Hom M (shift K 1) // ∀ x : M.M, δ.toFun x = π.toFun (L.d (s.toFun x))} := by
  let δfun : M.M →ₗ[R] K.M := π.toFun.comp (L.d.comp s.toFun)
  have hpi_s : ∀ x : M.M, π.toFun (s.toFun x) = 0 := by
    intro x
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact ⟨x, rfl⟩
  have hsplit := hfg.decomposition hs hπ hker
  refine ⟨⟨δfun, ?_, ?_, ?_⟩, ?_⟩
  · intro x a
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | homogeneous x =>
        have hx' := s.map_grading _ x x.property
        have hleib := L.leibniz_apply _ (s.toFun x) hx' a
        change π.toFun (L.d (s.toFun (MulOpposite.op a • (x : M.M)))) =
          MulOpposite.op a • π.toFun (L.d (s.toFun (x : M.M)))
        rw [s.map_smul, hleib, map_add, π.map_smul]
        have hkill : π.toFun (MulOpposite.op (A.d a) • s.toFun x) = 0 := by
          rw [← s.map_smul]
          exact hpi_s _
        simp only [map_zsmul, hkill, zsmul_zero, add_zero]
    | add x y hx hy => simp [map_add, hx, hy]
  · intro n x hx
    exact π.map_grading (n + 1) (L.d (s.toFun x)) (L.d_mem n _ (s.map_grading n x hx))
  · ext x
    rw [shift_d]
    change δfun (M.d x) = ((1 : ℤ).negOnePow • K.d) (δfun x)
    have hdecomp := hsplit (L.d (s.toFun x))
    have hgd : g.toFun (L.d (s.toFun x)) = M.d x := by
      calc
        g.toFun (L.d (s.toFun x)) = M.d (g.toFun (s.toFun x)) :=
          LinearMap.congr_fun g.map_d (s.toFun x)
        _ = M.d x := by rw [hs]
    have hdzero : L.d (L.d (s.toFun x)) = 0 :=
      LinearMap.congr_fun L.d_comp_d (s.toFun x)
    have hddecomp := congrArg L.d hdecomp
    have hdparts :
        L.d (f.toFun (π.toFun (L.d (s.toFun x)))) +
            L.d (s.toFun (g.toFun (L.d (s.toFun x)))) = 0 := by
      simpa [hdzero] using hddecomp
    have hdf : L.d (f.toFun (π.toFun (L.d (s.toFun x)))) =
        f.toFun (K.d (π.toFun (L.d (s.toFun x)))) :=
      (LinearMap.congr_fun f.map_d _).symm
    have hdrel : f.toFun (K.d (δfun x)) + L.d (s.toFun (M.d x)) = 0 := by
      simpa [δfun, hgd, hdf] using hdparts
    have hπrel := congrArg π.toFun hdrel
    have hπrel' : K.d (δfun x) + δfun (M.d x) = 0 := by
      simpa [δfun, hπ] using hπrel
    have hfinal : δfun (M.d x) = -K.d (δfun x) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hπrel')
    simpa [LinearMap.smul_apply, Int.negOnePow_one, Units.smul_def] using hfinal
  · intro x
    rfl

/-- The connecting homomorphisms of two compatible pairs of graded splittings are homotopic. -/
theorem connectingHom_homotopic (f : Hom K L) (g : Hom L M)
    (hfg : IsAdmissibleShortExact f g)
    (s s' : GradedHom M L) (π π' : GradedHom L K)
    (hs : ∀ x : M.M, g.toFun (s.toFun x) = x)
    (hs' : ∀ x : M.M, g.toFun (s'.toFun x) = x)
    (hπ : ∀ x : K.M, π.toFun (f.toFun x) = x)
    (hπ' : ∀ x : K.M, π'.toFun (f.toFun x) = x)
    (hker : LinearMap.ker π.toFun = LinearMap.range s.toFun)
    (hker' : LinearMap.ker π'.toFun = LinearMap.range s'.toFun) :
    Homotopic (connectingHom f g hfg s π hs hπ hker).val
      (connectingHom f g hfg s' π' hs' hπ' hker').val := by
  let h : M.M →ₗ[R] K.M := π.toFun.comp (s'.toFun - s.toFun)
  have hker'0 := apply_eq_zero_of_ker_eq_range hker'
  have hdiff (x : M.M) : f.toFun (h x) = s'.toFun x - s.toFun x := by
    have hgd : g.toFun (s'.toFun x - s.toFun x) = 0 := by
      rw [map_sub, hs' x, hs x, sub_self]
    have hmem : s'.toFun x - s.toFun x ∈ LinearMap.range f.toFun := by
      rw [hfg.exact]
      exact LinearMap.mem_ker.mpr hgd
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
    change f.toFun (π.toFun (s'.toFun x - s.toFun x)) = _
    rw [← hy, hπ y]
  have hs'form (x : M.M) : s'.toFun x = s.toFun x + f.toFun (h x) := by
    calc
      s'.toFun x = s.toFun x + (s'.toFun x - s.toFun x) := by abel
      _ = s.toFun x + f.toFun (h x) := by rw [← hdiff x]
  have hπ's (x : M.M) : π'.toFun (s.toFun x) = -h x := by
    rw [show s.toFun x = s'.toFun x - f.toFun (h x) by rw [hs'form]; abel]
    rw [map_sub, hker'0, hπ']
    simp
  have hπ'form (y : L.M) : π'.toFun y = π.toFun y - h (g.toFun y) := by
    conv_lhs => rw [← hfg.decomposition hs hπ hker y]
    rw [map_add, hπ', hπ's]
    abel
  let H : M.M →ₗ[MulOpposite A.A] (shift K 1).M :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro a x
        change h (MulOpposite.op (MulOpposite.unop a) • x) =
          MulOpposite.op (MulOpposite.unop a) • h x
        simp only [h, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply]
        rw [s'.map_smul, s.map_smul, ← smul_sub, π.map_smul] }
  refine ⟨{ toLinearMap := H, map_grading := ?_, homotopy_eq := ?_ }⟩
  · intro n x hx
    have hp : H x ∈ K.grading n := by
      change (π.toFun.comp (s'.toFun - s.toFun)) x ∈ K.grading n
      exact π.map_grading n (s'.toFun x - s.toFun x)
        (Submodule.sub_mem _ (s'.map_grading n x hx) (s.map_grading n x hx))
    change H x ∈ K.grading (n - 1 + 1)
    rwa [show n - 1 + 1 = n from by omega]
  · intro x
    have hchain (x : M.M) :
        π'.toFun (L.d (s'.toFun x)) =
          π.toFun (L.d (s.toFun x)) + K.d (h x) - h (M.d x) := by
      have hgchain (z : L.M) : g.toFun (L.d z) = M.d (g.toFun z) :=
        LinearMap.congr_fun g.map_d z
      have hfchain : L.d (f.toFun (h x)) = f.toFun (K.d (h x)) :=
        (LinearMap.congr_fun f.map_d (h x)).symm
      calc
        π'.toFun (L.d (s'.toFun x)) =
            π.toFun (L.d (s'.toFun x)) - h (g.toFun (L.d (s'.toFun x))) :=
          hπ'form _
        _ = π.toFun (L.d (s'.toFun x)) - h (M.d x) := by rw [hgchain, hs']
        _ = π.toFun (L.d (s.toFun x) + L.d (f.toFun (h x))) - h (M.d x) := by
          rw [hs'form, map_add]
        _ = π.toFun (L.d (s.toFun x)) + K.d (h x) - h (M.d x) := by
          rw [map_add, hfchain, hπ]
    rw [(connectingHom f g hfg s π hs hπ hker).property x,
      (connectingHom f g hfg s' π' hs' hπ' hker').property x]
    rw [hchain]
    simp [shift_d]
    abel

/-- The connecting arrow of the triangle of an admissible short exact sequence is independent, in
the homotopy category, of the compatible graded splittings used to write it down. -/
@[sga "4½ Etat_0 1.2.4" "partial"]
theorem toHomotopyCategory_map_connectingHom_eq (f : Hom K L) (g : Hom L M)
    (hfg : IsAdmissibleShortExact f g)
    (s s' : GradedHom M L) (π π' : GradedHom L K)
    (hs : ∀ x : M.M, g.toFun (s.toFun x) = x)
    (hs' : ∀ x : M.M, g.toFun (s'.toFun x) = x)
    (hπ : ∀ x : K.M, π.toFun (f.toFun x) = x)
    (hπ' : ∀ x : K.M, π'.toFun (f.toFun x) = x)
    (hker : LinearMap.ker π.toFun = LinearMap.range s.toFun)
    (hker' : LinearMap.ker π'.toFun = LinearMap.range s'.toFun) :
    (toHomotopyCategory A).map (connectingHom f g hfg s π hs hπ hker).val =
      (toHomotopyCategory A).map (connectingHom f g hfg s' π' hs' hπ' hker').val := by
  apply CategoryTheory.Quotient.sound
  exact connectingHom_homotopic f g hfg s s' π π' hs hs' hπ hπ' hker hker'

end DifferentialGradedModule
