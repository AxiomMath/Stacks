module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorGradedHom

/-! # Tensoring an admissible short exact sequence of bimodules

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, let
`K → L → M` be an admissible short exact sequence of differential graded `(A, B)`-bimodules — one
split by maps of *graded* bimodules — and let `X` be a right differential graded `A`-module. Then
`X ⊗_A K → X ⊗_A L → X ⊗_A M` is an admissible short exact sequence of right differential graded
`B`-modules.

Every part of the conclusion is a formal consequence of the graded splitting, so the only thing
needed is that the splittings can be tensored at all. They are graded homomorphisms of bimodules,
not homomorphisms, so the universal property of Tag 09LM does not reach them;
`DifferentialGraded.Bimodule.tensorGradedHomOfBimodule` does, through the all-degrees form of
Tag 09LN.
Every identity among the tensored maps is then checked on the pure tensors, which generate the
relative tensor product.

The splittings are made compatible first — a graded retraction of `K → L` and a graded section of
`L → M` whose images decompose `L` — exactly as
`DifferentialGradedModule.nonempty_compatibleSplittings` does for modules; the section is
corrected by `s₀ - f ∘ π₀ ∘ s₀`, and the correction is a graded homomorphism of bimodules because
each of its three factors commutes with the left action.

## Main definitions

* `DifferentialGraded.Bimodule.CompatibleSplittings`: a graded retraction and a graded section
  of a short exact sequence of bimodules whose images decompose the middle term.

## Main results

* `DifferentialGraded.Bimodule.GradedHom.map_leftActionTotal`: a graded homomorphism of bimodules
  commutes with the left action of an arbitrary element of `A`.
* `DifferentialGraded.Bimodule.nonempty_compatibleSplittings`: an admissible short exact sequence
  of bimodules has compatible graded splittings.
* `DifferentialGraded.Bimodule.tensorIsAdmissibleShortExact`: **tensoring preserves admissible
  short exact sequences of bimodules.**

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT) is admissibility,
  [Tag 09K8](https://stacks.math.columbia.edu/tag/09K8) the compatible splittings,
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) the relative tensor product and
  [Tag 09LN](https://stacks.math.columbia.edu/tag/09LN) the identification that tensors a graded
  homomorphism; [Tag 0FQL](https://stacks.math.columbia.edu/tag/0FQL) is where the admissible
  sequences of bimodules this serves come from.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### Graded homomorphisms of bimodules and the total left action -/

/-- The totalized left action on a homogeneous element is the homogeneous left action. -/
private theorem leftActionTotal_of_mem_grading (N : Bimodule A B) (m q : ℤ) (a : A.grading m)
    (y : N.rightModule.M) (hy : y ∈ N.rightModule.grading q) :
    leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) y =
      ((show N.rightModule.grading (q + m) from
        (N.leftAction.1.action m a).v q (q + m) (by omega) ⟨y, hy⟩) : N.rightModule.M) := by
  rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 m a]
  exact totalizeCochain_apply_of_eq B N.rightModule m q (q + m) rfl
    (N.leftAction.1.action m a) ⟨y, hy⟩

/-- **A graded homomorphism of bimodules commutes with the totalized left action**, for an
arbitrary element of `A` and not only a homogeneous one. -/
theorem GradedHom.map_leftActionTotal {N N' : Bimodule A B} (u : GradedHom A B N N') (a : A.A)
    (y : N.rightModule.M) :
    u.rightHom.toFun (leftActionTotal A B N.rightModule N.leftAction.1 a y) =
      leftActionTotal A B N'.rightModule N'.leftAction.1 a (u.rightHom.toFun y) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | @homogeneous m a =>
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | @homogeneous q y =>
      rw [leftActionTotal_of_mem_grading N m q a y y.2,
        leftActionTotal_of_mem_grading N' m q a _ (u.rightHom.map_grading q _ y.2)]
      exact u.map_left m q a y

/-- A graded homomorphism of the underlying right modules which commutes with the totalized left
action is a graded homomorphism of bimodules. -/
def gradedHomOfLeftActionTotal {N N' : Bimodule A B}
    (u : DifferentialGradedModule.GradedHom N.rightModule N'.rightModule)
    (hu : ∀ (a : A.A) (y : N.rightModule.M),
      u.toFun (leftActionTotal A B N.rightModule N.leftAction.1 a y) =
        leftActionTotal A B N'.rightModule N'.leftAction.1 a (u.toFun y)) :
    GradedHom A B N N' where
  rightHom := u
  map_left n p a x := by
    have h := hu (a : A.A) (x : N.rightModule.M)
    rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
      totalizeCochain_apply_of_eq B N.rightModule n p (p + n) rfl
        (N.leftAction.1.action n a) x,
      leftActionTotal_apply A B N'.rightModule N'.leftAction.1 n a,
      totalizeCochain_apply_of_eq B N'.rightModule n p (p + n) rfl
        (N'.leftAction.1.action n a)
        ⟨u.toFun (x : N.rightModule.M),
          u.map_grading p (x : N.rightModule.M) x.property⟩] at h
    exact h

/-! ### Compatible graded splittings of a sequence of bimodules -/

/-- A composite vanishes when the range of the first map is the kernel of the second. -/
private theorem apply_eq_zero_of_range_eq_ker {V W Z : Type*} [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup Z] [Module R V] [Module R W] [Module R Z] {u : V →ₗ[R] W} {v : W →ₗ[R] Z}
    (h : LinearMap.range u = LinearMap.ker v) (x : V) : v (u x) = 0 :=
  LinearMap.mem_ker.mp (h ▸ ⟨x, rfl⟩)

/-- The graded splittings of a short exact sequence of bimodules, made compatible: the kernel of
the retraction is the image of the section. -/
structure CompatibleSplittings {K L M : Bimodule A B} (f : K ⟶ L) (g : L ⟶ M) where
  /-- The graded section of `g`. -/
  s : GradedHom A B M L
  /-- The graded retraction of `f`. -/
  π : GradedHom A B L K
  /-- `s` is a section of `g`. -/
  hs : ∀ x : M.rightModule.M, g.rightHom.toFun (s.rightHom.toFun x) = x
  /-- `π` is a retraction of `f`. -/
  hπ : ∀ x : K.rightModule.M, π.rightHom.toFun (f.rightHom.toFun x) = x
  /-- The two splittings are compatible. -/
  hker : LinearMap.ker π.rightHom.toFun = LinearMap.range s.rightHom.toFun

/-- **An admissible short exact sequence of bimodules has compatible graded splittings.** The
retraction is the given one and the section is corrected by `s₀ - f ∘ π₀ ∘ s₀`, which is a graded
homomorphism of bimodules because each of its factors commutes with the left action. -/
theorem nonempty_compatibleSplittings {K L M : Bimodule A B} (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact A B f g) : Nonempty (CompatibleSplittings f g) := by
  obtain ⟨π, hπ⟩ := hfg.splitMono
  obtain ⟨s₀, hs₀⟩ := hfg.splitEpi
  have hgf := apply_eq_zero_of_range_eq_ker hfg.exact
  let sFun : DifferentialGradedModule.GradedHom M.rightModule L.rightModule :=
    { toFun := s₀.rightHom.toFun -
        f.rightHom.toFun.comp (π.rightHom.toFun.comp s₀.rightHom.toFun)
      map_smul := by
        intro x a
        show s₀.rightHom.toFun (MulOpposite.op a • x) -
            f.rightHom.toFun (π.rightHom.toFun (s₀.rightHom.toFun
              (MulOpposite.op a • x))) =
          MulOpposite.op a • (s₀.rightHom.toFun x -
            f.rightHom.toFun (π.rightHom.toFun (s₀.rightHom.toFun x)))
        rw [s₀.rightHom.map_smul, π.rightHom.map_smul, f.rightHom.map_smul, smul_sub]
      map_grading := by
        intro n x hx
        exact Submodule.sub_mem _ (s₀.rightHom.map_grading n x hx)
          (f.rightHom.map_grading n _ (π.rightHom.map_grading n _
            (s₀.rightHom.map_grading n x hx))) }
  have hf : ∀ (b : A.A) (z : K.rightModule.M),
      f.rightHom.toFun (leftActionTotal A B K.rightModule K.leftAction.1 b z) =
        leftActionTotal A B L.rightModule L.leftAction.1 b (f.rightHom.toFun z) :=
    fun b z => GradedHom.map_leftActionTotal (Hom.toGradedHom A B f) b z
  have hsFun : ∀ (a : A.A) (y : M.rightModule.M),
      sFun.toFun (leftActionTotal A B M.rightModule M.leftAction.1 a y) =
        leftActionTotal A B L.rightModule L.leftAction.1 a (sFun.toFun y) := by
    intro a y
    show s₀.rightHom.toFun _ - f.rightHom.toFun (π.rightHom.toFun
        (s₀.rightHom.toFun _)) = _
    rw [GradedHom.map_leftActionTotal s₀ a y, GradedHom.map_leftActionTotal π a _,
      hf a _]
    show _ = leftActionTotal A B L.rightModule L.leftAction.1 a
      (s₀.rightHom.toFun y - f.rightHom.toFun (π.rightHom.toFun (s₀.rightHom.toFun y)))
    rw [map_sub]
  let s : GradedHom A B M L := gradedHomOfLeftActionTotal sFun hsFun
  have hsval : ∀ x : M.rightModule.M, s.rightHom.toFun x =
      s₀.rightHom.toFun x - f.rightHom.toFun (π.rightHom.toFun (s₀.rightHom.toFun x)) :=
    fun _ => rfl
  have hgs : ∀ x : M.rightModule.M, g.rightHom.toFun (s.rightHom.toFun x) = x := by
    intro x
    rw [hsval, map_sub, hgf, hs₀, sub_zero]
  have hπs : ∀ x : M.rightModule.M, π.rightHom.toFun (s.rightHom.toFun x) = 0 := by
    intro x
    rw [hsval, map_sub, hπ, sub_self]
  refine ⟨⟨s, π, hgs, hπ, ?_⟩⟩
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hd : x - s.rightHom.toFun (g.rightHom.toFun x) ∈
        LinearMap.range f.rightHom.toFun := by
      rw [hfg.exact, LinearMap.mem_ker, map_sub, hgs, sub_self]
    obtain ⟨y, hy⟩ := hd
    have hy₀ : y = 0 := by
      have h := congrArg π.rightHom.toFun hy
      rw [hπ, map_sub, hπs, LinearMap.mem_ker.mp hx, sub_zero] at h
      exact h
    refine ⟨g.rightHom.toFun x, ?_⟩
    rw [hy₀, map_zero] at hy
    exact (sub_eq_zero.mp hy.symm).symm
  · obtain ⟨y, rfl⟩ := hx
    exact LinearMap.mem_ker.mpr (hπs y)

/-! ### The tensored sequence -/

/-- Two composites out of a relative tensor product agree when they agree on pure tensors. -/
private theorem tensorObj_comp_apply_eq {N : Bimodule A B}
    {X : DifferentialGradedModule.{u, u, u} A} {V W : Type u}
    [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (u : (tensorObj N X).M →ₗ[R] V) (v : V →ₗ[R] W) (w : (tensorObj N X).M →ₗ[R] W)
    (h : ∀ (x : X.M) (y : N.rightModule.M),
      v (u ((tensorPure N X).toLinearMap x y)) = w ((tensorPure N X).toLinearMap x y))
    (z : (tensorObj N X).M) : v (u z) = w z :=
  LinearMap.congr_fun (tensorObj_linearMap_ext N X (v.comp u) w h) z

variable {K L M : Bimodule A B} {X : DifferentialGradedModule.{u, u, u} A}

/-- The tensored retraction retracts the tensored first map. -/
theorem tensorGradedHom_tensorHomOfBimoduleHom_left {f : K ⟶ L} {g : L ⟶ M}
    (c : CompatibleSplittings f g) (z : (tensorObj K X).M) :
    (tensorGradedHomOfBimodule L K X c.π).toFun ((tensorHomOfBimoduleHom f X).toFun z) = z := by
  refine tensorObj_comp_apply_eq (tensorHomOfBimoduleHom f X).toFun
    (tensorGradedHomOfBimodule L K X c.π).toFun LinearMap.id (fun x y => ?_) z
  rw [tensorHomOfBimoduleHom_pure, tensorGradedHomOfBimodule_pure, c.hπ]
  rfl

/-- The tensored section sections the tensored second map. -/
theorem tensorHomOfBimoduleHom_tensorGradedHom_right {f : K ⟶ L} {g : L ⟶ M}
    (c : CompatibleSplittings f g) (z : (tensorObj M X).M) :
    (tensorHomOfBimoduleHom g X).toFun ((tensorGradedHomOfBimodule M L X c.s).toFun z) = z := by
  refine tensorObj_comp_apply_eq (tensorGradedHomOfBimodule M L X c.s).toFun
    (tensorHomOfBimoduleHom g X).toFun LinearMap.id (fun x y => ?_) z
  rw [tensorGradedHomOfBimodule_pure, tensorHomOfBimoduleHom_pure, c.hs]
  rfl

/-- The tensored composite of the two maps vanishes. -/
theorem tensorHomOfBimoduleHom_comp_eq_zero {f : K ⟶ L} {g : L ⟶ M}
    (hfg : IsAdmissibleShortExact A B f g) (z : (tensorObj K X).M) :
    (tensorHomOfBimoduleHom g X).toFun ((tensorHomOfBimoduleHom f X).toFun z) = 0 := by
  have hgf := apply_eq_zero_of_range_eq_ker hfg.exact
  refine tensorObj_comp_apply_eq (tensorHomOfBimoduleHom f X).toFun
    (tensorHomOfBimoduleHom g X).toFun 0 (fun x y => ?_) z
  rw [tensorHomOfBimoduleHom_pure, tensorHomOfBimoduleHom_pure, hgf, map_zero]
  rfl

/-- The tensored retraction kills the tensored section. -/
theorem tensorGradedHom_comp_eq_zero {f : K ⟶ L} {g : L ⟶ M}
    (c : CompatibleSplittings f g) (z : (tensorObj M X).M) :
    (tensorGradedHomOfBimodule L K X c.π).toFun
      ((tensorGradedHomOfBimodule M L X c.s).toFun z) = 0 := by
  have hπs := apply_eq_zero_of_range_eq_ker c.hker.symm
  refine tensorObj_comp_apply_eq (tensorGradedHomOfBimodule M L X c.s).toFun
    (tensorGradedHomOfBimodule L K X c.π).toFun 0 (fun x y => ?_) z
  rw [tensorGradedHomOfBimodule_pure, tensorGradedHomOfBimodule_pure, hπs, map_zero]
  rfl

/-- **The graded decomposition of the middle term survives tensoring.** -/
theorem tensorDecomposition {f : K ⟶ L} {g : L ⟶ M}
    (hfg : IsAdmissibleShortExact A B f g) (c : CompatibleSplittings f g)
    (z : (tensorObj L X).M) :
    (tensorHomOfBimoduleHom f X).toFun ((tensorGradedHomOfBimodule L K X c.π).toFun z) +
        (tensorGradedHomOfBimodule M L X c.s).toFun ((tensorHomOfBimoduleHom g X).toFun z) = z := by
  have hdec : ∀ y : L.rightModule.M,
      f.rightHom.toFun (c.π.rightHom.toFun y) +
        c.s.rightHom.toFun (g.rightHom.toFun y) = y := by
    intro y
    have hmem : y - c.s.rightHom.toFun (g.rightHom.toFun y) ∈
        LinearMap.range f.rightHom.toFun := by
      rw [hfg.exact, LinearMap.mem_ker, map_sub, c.hs, sub_self]
    obtain ⟨w, hw⟩ := hmem
    have hπy : c.π.rightHom.toFun y = w := by
      have h := congrArg c.π.rightHom.toFun hw
      rw [c.hπ, map_sub] at h
      rw [apply_eq_zero_of_range_eq_ker c.hker.symm, sub_zero] at h
      exact h.symm
    rw [hπy, hw, sub_add_cancel]
  refine LinearMap.congr_fun (tensorObj_linearMap_ext L X
    ((((tensorHomOfBimoduleHom f X).toFun).comp (tensorGradedHomOfBimodule L K X c.π).toFun) +
      (((tensorGradedHomOfBimodule M L X c.s).toFun).comp (tensorHomOfBimoduleHom g X).toFun))
    LinearMap.id fun x y => ?_) z
  show (tensorHomOfBimoduleHom f X).toFun
      ((tensorGradedHomOfBimodule L K X c.π).toFun ((tensorPure L X).toLinearMap x y)) +
    (tensorGradedHomOfBimodule M L X c.s).toFun
      ((tensorHomOfBimoduleHom g X).toFun ((tensorPure L X).toLinearMap x y)) = _
  rw [tensorGradedHomOfBimodule_pure, tensorHomOfBimoduleHom_pure, tensorHomOfBimoduleHom_pure,
    tensorGradedHomOfBimodule_pure, ← map_add, hdec]
  rfl

/-- **Tensoring preserves admissible short exact sequences of bimodules.** For an admissible
short exact sequence `K → L → M` of differential graded `(A, B)`-bimodules and a right
differential graded `A`-module `X`, the sequence `X ⊗_A K → X ⊗_A L → X ⊗_A M` is an admissible
short exact sequence of right differential graded `B`-modules.

The compatible graded splittings of the sequence are tensored by
`DifferentialGraded.Bimodule.tensorGradedHomOfBimodule`, which is where the all-degrees form of
Tag 09LN enters: a splitting does not commute with the differential, so the universal property of
Tag 09LM cannot tensor it. -/
theorem tensorIsAdmissibleShortExact {f : K ⟶ L} {g : L ⟶ M}
    (hfg : IsAdmissibleShortExact A B f g) (X : DifferentialGradedModule.{u, u, u} A) :
    DifferentialGradedModule.IsAdmissibleShortExact
      (tensorHomOfBimoduleHom f X) (tensorHomOfBimoduleHom g X) := by
  obtain ⟨c⟩ := nonempty_compatibleSplittings f g hfg
  refine
    { injective := fun z₁ z₂ h => ?_
      surjective := fun z => ⟨(tensorGradedHomOfBimodule M L X c.s).toFun z,
        tensorHomOfBimoduleHom_tensorGradedHom_right c z⟩
      exact := ?_
      admissibleMono := ⟨tensorGradedHomOfBimodule L K X c.π,
        fun z => tensorGradedHom_tensorHomOfBimoduleHom_left c z⟩
      admissibleEpi := ⟨tensorGradedHomOfBimodule M L X c.s,
        fun z => tensorHomOfBimoduleHom_tensorGradedHom_right c z⟩ }
  · rw [← tensorGradedHom_tensorHomOfBimoduleHom_left c z₁,
      ← tensorGradedHom_tensorHomOfBimoduleHom_left c z₂, h]
  · refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨w, rfl⟩ := hz
      exact LinearMap.mem_ker.mpr (tensorHomOfBimoduleHom_comp_eq_zero hfg w)
    · refine ⟨(tensorGradedHomOfBimodule L K X c.π).toFun z, ?_⟩
      have hd := tensorDecomposition hfg c z
      rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at hd
      exact hd

end DifferentialGraded.Bimodule

end
