module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleCokernel
public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleFactorization
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeAdmissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeHomotopyEquivalence

/-!
# The mapping-cone triangle and the triangles of admissible short exact sequences

The mapping cone of a homomorphism `f : K ⟶ L` of right differential graded modules gives a
triangle `K → L → C(f) → K[1]` in the homotopy category, with connecting morphism the negative of
the cone projection. For an admissible short exact sequence `K → L → M` the projection of `C(f)`
onto `M` is a homotopy equivalence and completes the identities of `K` and `L` to an isomorphism
from the cone triangle to the triangle of the sequence. Conversely every homomorphism can be
replaced, up to homotopy equivalence of the target, by an admissible monomorphism, so every cone
triangle is presented by an admissible short exact sequence.

## Main definitions

* `DifferentialGradedModule.mappingConeTriangle`: the standard triangle of a mapping cone.
* `DifferentialGradedModule.mappingConeToQuotient` and
  `DifferentialGradedModule.quotientToMappingCone`: the comparison between the cone of an
  admissible monomorphism and the third term of its sequence, in both directions.
* `DifferentialGradedModule.mappingConeSectionHomotopy`,
  `DifferentialGradedModule.mappingConeBoundaryHomotopyFun` and
  `DifferentialGradedModule.mappingConeBoundaryHomotopy`: the homotopies making that comparison
  an isomorphism of triangles.

## Main results

* `DifferentialGradedModule.CompatibleSplittings.decomposition`: compatible graded splittings
  decompose the middle term of an admissible short exact sequence.
* `DifferentialGradedModule.exists_mappingConeTriangle_iso_associatedTriangle`: for an
  admissible short exact sequence, the cone triangle is isomorphic to the triangle of the sequence.
* `DifferentialGradedModule.exists_associatedTriangle_iso_mappingConeTriangle`: every cone
  triangle is isomorphic to the triangle of an admissible short exact sequence.

## Implementation notes

Part (1) specifies the cone-to-quotient map on the canonical coordinates of the cone and states
that the other two components of the isomorphism are the identities; part (2) keeps the identity
on the first vertex and uses the comparison map from the admissible replacement of the second
vertex, which is compatible with the given homomorphism. The admissible short exact sequence
extending an admissible monomorphism is the one of `AdmissibleCokernel`, so the third term is the
cokernel of the abelian structure rather than a second model of it.

## References

* [Stacks Project, Tag 09KF](https://stacks.math.columbia.edu/tag/09KF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
variable {K L M : DifferentialGradedModule A}

/-- Homotopic homomorphisms have the same image in the homotopy category. -/
theorem quotient_map_eq_of_homotopic {X Y : DifferentialGradedModule A} {a b : X ⟶ Y}
    (h : Homotopic a b) :
    (toHomotopyCategory A).map a = (toHomotopyCategory A).map b :=
  (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) a b).2 h

/-- Equal homomorphisms are homotopic. -/
theorem homotopic_of_eq {X Y : DifferentialGradedModule A} {a b : X ⟶ Y} (h : a = b) :
    Homotopic a b := h ▸ Homotopic.refl a

/-- Compatible graded splittings of an admissible short exact sequence decompose the middle
term. -/
theorem CompatibleSplittings.decomposition {f : K ⟶ L} {g : L ⟶ M}
    (c : CompatibleSplittings A f g) (hfg : IsAdmissibleShortExact f g) (y : L.M) :
    f.toFun (c.π.toFun y) + c.s.toFun (g.toFun y) = y :=
  hfg.decomposition c.hs c.hπ c.hker y

/-- The underlying linear map of the connecting homomorphism of a chosen pair of compatible
graded splittings. -/
noncomputable def connectingLinearMap (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) : M.M →ₗ[R] K.M :=
  (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun

/-- The connecting map sends `x` to the `K`-component, under `c.π`, of the differential of
`c.s x`. -/
theorem connectingLinearMap_apply (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) (x : M.M) :
    connectingLinearMap f g hfg c x = c.π.toFun (L.d (c.s.toFun x)) :=
  (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).property x

/-- The projection of the cone of an admissible monomorphism onto the third term of its
sequence. -/
noncomputable def mappingConeToQuotient (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) : coneModule f ⟶ M where
  toFun := g.toFun.comp ((LinearMap.fst R L.M K.M).comp
    (cone f).coordinates.toLinearMap)
  map_smul x a := g.map_smul ((cone f).coordinates x).1 a
  map_grading n x hx := g.map_grading n _ (((cone f).grading_iff n x).mp hx).1
  map_d := by
    apply LinearMap.ext
    intro x
    change g.toFun ((cone f).coordinates ((coneModule f).d x)).1 =
      M.d (g.toFun ((cone f).coordinates x).1)
    rw [(cone f).differential]
    change g.toFun (L.d ((cone f).coordinates x).1 +
      f.toFun ((cone f).coordinates x).2) =
        M.d (g.toFun ((cone f).coordinates x).1)
    have hgf : g.toFun (f.toFun ((cone f).coordinates x).2) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hfg.exact]
      exact ⟨(cone f).coordinates x |>.2, rfl⟩
    rw [map_add, hgf, add_zero]
    exact LinearMap.congr_fun g.map_d x.1

/-- The cone-to-quotient projection applies `g` to the `L`-coordinate of an element of the
cone. -/
theorem mappingConeToQuotient_apply (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (x : (coneModule f).M) :
    (mappingConeToQuotient f g hfg).toFun x = g.toFun ((cone f).coordinates x).1 := rfl

/-- The differential of `L` on the image of the splitting `c.s` is the sum of the connecting
map pushed forward along `f` and the splitting of the differential of `M`. -/
theorem splitting_differential (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) (x : M.M) :
    L.d (c.s.toFun x) = f.toFun (connectingLinearMap f g hfg c x) + c.s.toFun (M.d x) := by
  have hdecomp := c.decomposition hfg (L.d (c.s.toFun x))
  have hg : g.toFun (L.d (c.s.toFun x)) = M.d x :=
    (LinearMap.congr_fun g.map_d (c.s.toFun x)).trans (congrArg M.d (c.hs x))
  rw [hg, ← connectingLinearMap_apply f g hfg c x] at hdecomp
  exact hdecomp.symm

/-- For `y : L`, the failure of `c.π` to commute with the differentials at `y` is the
connecting map applied to `g y`. -/
theorem boundary_formula (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) (y : L.M) :
    c.π.toFun (L.d y) - K.d (c.π.toFun y) =
      connectingLinearMap f g hfg c (g.toFun y) := by
  have hπs (x : M.M) : c.π.toFun (c.s.toFun x) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [c.hker]
    exact ⟨x, rfl⟩
  have hd := congrArg L.d (c.decomposition hfg y)
  rw [map_add] at hd
  have hds := splitting_differential f g hfg c (g.toFun y)
  have hfd : L.d (f.toFun (c.π.toFun y)) = f.toFun (K.d (c.π.toFun y)) :=
    (LinearMap.congr_fun f.map_d (c.π.toFun y)).symm
  have hwhole : L.d y = f.toFun (K.d (c.π.toFun y)) +
      f.toFun (connectingLinearMap f g hfg c (g.toFun y)) + c.s.toFun (M.d (g.toFun y)) := by
    rw [← hd, hfd, hds]
    abel
  have hp := congrArg c.π.toFun hwhole
  simp only [map_add, c.hπ, hπs, add_zero] at hp
  rw [hp]
  abel

/-- The section of the cone-to-quotient projection determined by compatible graded splittings. -/
noncomputable def quotientToMappingCone (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) :
    M ⟶ coneModule f := by
  refine {
    toFun := ((cone f).coordinates.symm.toLinearMap).comp
      (c.s.toFun.prod (-connectingLinearMap f g hfg c))
    map_smul := ?_
    map_grading := ?_
    map_d := ?_ }
  · intro x a
    change (c.s.toFun (MulOpposite.op a • x),
        -connectingLinearMap f g hfg c (MulOpposite.op a • x)) =
      (MulOpposite.op a • c.s.toFun x, MulOpposite.op a • -connectingLinearMap f g hfg c x)
    rw [c.s.map_smul]
    have hδ := (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.map_smul x a
    change connectingLinearMap f g hfg c (MulOpposite.op a • x) =
      MulOpposite.op a • connectingLinearMap f g hfg c x at hδ
    rw [hδ]
    simp [smul_neg]
  · intro n x hx
    rw [(cone f).grading_iff]
    refine ⟨c.s.map_grading n x hx, ?_⟩
    change -connectingLinearMap f g hfg c x ∈ K.grading (n + 1)
    refine (K.grading (n + 1)).neg_mem ?_
    have h := (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.map_grading n x hx
    rwa [shift_grading] at h
  · apply LinearMap.ext
    intro x
    have hδd : connectingLinearMap f g hfg c (M.d x) =
        -K.d (connectingLinearMap f g hfg c x) := by
      have h := LinearMap.congr_fun
        (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.map_d x
      change connectingLinearMap f g hfg c (M.d x) =
        (shift K 1).d (connectingLinearMap f g hfg c x) at h
      rw [h]
      simp [shift_d, Int.negOnePow_one, Units.smul_def]
    apply (cone f).coordinates.injective
    change (c.s.toFun (M.d x), -connectingLinearMap f g hfg c (M.d x)) =
      (L.d (c.s.toFun x) + f.toFun (-connectingLinearMap f g hfg c x),
        -K.d (-connectingLinearMap f g hfg c x))
    refine Prod.ext ?_ ?_
    · change c.s.toFun (M.d x) =
        L.d (c.s.toFun x) + f.toFun (-connectingLinearMap f g hfg c x)
      rw [splitting_differential f g hfg c x]
      simp only [map_neg]
      abel
    · change -connectingLinearMap f g hfg c (M.d x) =
        -K.d (-connectingLinearMap f g hfg c x)
      rw [hδd]
      simp

/-- The cone-to-quotient projection followed by its section is homotopic to the identity. -/
noncomputable def mappingConeSectionHomotopy (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) :
    Homotopy (𝟙 (coneModule f))
      (mappingConeToQuotient f g hfg ≫ quotientToMappingCone f g hfg c) := by
  let hmap : (coneModule f).M →ₗ[MulOpposite A.A] (coneModule f).M := {
    toFun := fun x => (cone f).coordinates.symm
      (0, c.π.toFun ((cone f).coordinates x).1)
    map_add' := by
      intro x y
      apply (cone f).coordinates.injective
      simp [map_add]
    map_smul' := by
      intro a x
      apply (cone f).coordinates.injective
      change (0, c.π.toFun (MulOpposite.op (MulOpposite.unop a) •
          ((cone f).coordinates x).1)) =
        (MulOpposite.op (MulOpposite.unop a) • (0 : L.M),
          MulOpposite.op (MulOpposite.unop a) •
            c.π.toFun ((cone f).coordinates x).1)
      rw [c.π.map_smul]
      simp }
  refine {
    toLinearMap := hmap
    map_grading := by
      intro n x hx
      rw [(cone f).grading_iff] at hx ⊢
      change ((cone f).coordinates ((cone f).coordinates.symm
        (0, c.π.toFun ((cone f).coordinates x).1))).1 ∈ L.grading (n - 1) ∧ _
      rw [LinearEquiv.apply_symm_apply]
      refine ⟨(L.grading (n - 1)).zero_mem, ?_⟩
      change c.π.toFun ((cone f).coordinates x).1 ∈ K.grading (n - 1 + 1)
      rw [show n - 1 + 1 = n by omega]
      exact c.π.map_grading n ((cone f).coordinates x).1 hx.1
    homotopy_eq := by
      intro x
      apply (cone f).coordinates.injective
      simp only [map_sub, map_add, Hom.comp_toFun_apply]
      have hqr : (cone f).coordinates
          ((quotientToMappingCone f g hfg c).toFun
            ((mappingConeToQuotient f g hfg).toFun x)) =
          (c.s.toFun (g.toFun ((cone f).coordinates x).1),
            -connectingLinearMap f g hfg c (g.toFun ((cone f).coordinates x).1)) := by
        change (cone f).coordinates ((cone f).coordinates.symm _) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      have hh : (cone f).coordinates (hmap x) =
          (0, c.π.toFun ((cone f).coordinates x).1) := by
        change (cone f).coordinates ((cone f).coordinates.symm _) = _
        rw [LinearEquiv.apply_symm_apply]
      have hdh : (cone f).coordinates ((coneModule f).d (hmap x)) =
          (f.toFun (c.π.toFun ((cone f).coordinates x).1),
            -K.d (c.π.toFun ((cone f).coordinates x).1)) := by
        rw [(cone f).differential, hh]
        simp
      have hmapd : (cone f).coordinates (hmap ((coneModule f).d x)) =
          (0, c.π.toFun (L.d ((cone f).coordinates x).1 +
            f.toFun ((cone f).coordinates x).2)) := by
        change (cone f).coordinates ((cone f).coordinates.symm
          (0, c.π.toFun ((cone f).coordinates
            ((coneModule f).d x)).1)) = _
        rw [LinearEquiv.apply_symm_apply, (cone f).differential]
      rw [hqr, hdh, hmapd]
      have hid : (cone f).coordinates
          (Hom.toFun (𝟙 (coneModule f)) x) = (cone f).coordinates x := rfl
      rw [hid]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub, Prod.fst_add, add_zero]
        exact sub_eq_iff_eq_add.mpr (c.decomposition hfg
          ((cone f).coordinates x).1).symm
      · simp only [Prod.snd_sub, Prod.snd_add]
        change ((cone f).coordinates x).2 -
            -connectingLinearMap f g hfg c (g.toFun ((cone f).coordinates x).1) =
          -K.d (c.π.toFun ((cone f).coordinates x).1) +
            c.π.toFun (L.d ((cone f).coordinates x).1 +
              f.toFun ((cone f).coordinates x).2)
        simp only [sub_neg_eq_add]
        rw [map_add, c.hπ ((cone f).coordinates x).2,
          ← boundary_formula f g hfg c ((cone f).coordinates x).1]
        abel }

/-- The degree `-1` map realizing the homotopy of `mappingConeBoundaryHomotopy`. -/
noncomputable def mappingConeBoundaryHomotopyFun (f : K ⟶ L) {g : L ⟶ M}
    (c : CompatibleSplittings A f g) :
    (coneModule f).M →ₗ[MulOpposite A.A] (shift K 1).M where
  toFun := fun x => -c.π.toFun ((cone f).coordinates x).1
  map_add' x y := by simp [add_comm]
  map_smul' := by
    intro a x
    change -c.π.toFun (MulOpposite.op (MulOpposite.unop a) •
        ((cone f).coordinates x).1) =
      MulOpposite.op (MulOpposite.unop a) • -c.π.toFun ((cone f).coordinates x).1
    rw [c.π.map_smul]
    simp

/-- `mappingConeBoundaryHomotopyFun` sends an element of the cone to the negative of `c.π`
applied to its `L`-coordinate. -/
@[simp] theorem mappingConeBoundaryHomotopyFun_apply (f : K ⟶ L) {g : L ⟶ M}
    (c : CompatibleSplittings A f g) (x : (coneModule f).M) :
    mappingConeBoundaryHomotopyFun f c x = -c.π.toFun ((cone f).coordinates x).1 := rfl

/-- The negative cone projection factors, up to homotopy, through the cone-to-quotient projection
and the connecting homomorphism. -/
noncomputable def mappingConeBoundaryHomotopy (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g) :
    Homotopy (-coneProjection f)
      (mappingConeToQuotient f g hfg ≫
        (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val) where
  toLinearMap := mappingConeBoundaryHomotopyFun f c
  map_grading := by
    intro n x hx
    change -c.π.toFun ((cone f).coordinates x).1 ∈ (shift K 1).grading (n - 1)
    rw [shift_grading, show n - 1 + 1 = n by omega]
    exact (K.grading n).neg_mem (c.π.map_grading n ((cone f).coordinates x).1
      (((cone f).grading_iff n x).mp hx).1)
  homotopy_eq := by
    intro x
    change -(coneProjection f).toFun x -
        (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun
          (g.toFun ((cone f).coordinates x).1) =
      (shift K 1).d (mappingConeBoundaryHomotopyFun f c x) +
        mappingConeBoundaryHomotopyFun f c ((coneModule f).d x)
    have hmapd : mappingConeBoundaryHomotopyFun f c ((coneModule f).d x) =
        -c.π.toFun (L.d ((cone f).coordinates x).1 +
          f.toFun ((cone f).coordinates x).2) := by
      rw [mappingConeBoundaryHomotopyFun_apply, (cone f).differential]
    have hδ : (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun
          (g.toFun ((cone f).coordinates x).1) =
        c.π.toFun (L.d ((cone f).coordinates x).1) -
          K.d (c.π.toFun ((cone f).coordinates x).1) :=
      (boundary_formula f g hfg c ((cone f).coordinates x).1).symm
    rw [hmapd, mappingConeBoundaryHomotopyFun_apply, hδ, map_add,
      c.hπ ((cone f).coordinates x).2, (cone f).projection_apply, shift_d,
      LinearMap.smul_apply, Int.negOnePow_one, Units.smul_def]
    simp only [map_neg, Units.val_neg, Units.val_one, neg_smul, one_smul, neg_neg,
      sub_eq_add_neg]
    abel

/-- A homomorphism with a section, whose composite with it is homotopic to the identity, becomes
an isomorphism in the homotopy category. -/
private noncomputable def isoOfHomotopicSection {X Y : DifferentialGradedModule A} (q : X ⟶ Y)
    (s : Y ⟶ X) (h : Homotopic (q ≫ s) (𝟙 X)) (h' : s ≫ q = 𝟙 Y) :
    (toHomotopyCategory A).obj X ≅ (toHomotopyCategory A).obj Y where
  hom := (toHomotopyCategory A).map q
  inv := (toHomotopyCategory A).map s
  hom_inv_id := ((toHomotopyCategory A).map_comp q s).symm.trans
    ((quotient_map_eq_of_homotopic h).trans ((toHomotopyCategory A).map_id _))
  inv_hom_id := ((toHomotopyCategory A).map_comp s q).symm.trans
    ((congrArg _ h').trans ((toHomotopyCategory A).map_id _))

/-- The standard triangle of a homomorphism of differential graded modules, with connecting
morphism the negative of the cone projection. -/
noncomputable def mappingConeTriangle (f : K ⟶ L) :
    Pretriangulated.Triangle (HomotopyCategory A) :=
  Pretriangulated.Triangle.mk
    ((toHomotopyCategory A).map f)
    ((toHomotopyCategory A).map (coneInclusion f))
    ((toHomotopyCategory A).map (-coneProjection f) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ K 1).symm)

/-- For an admissible short exact sequence, the projection of the cone onto the third term is a
homotopy equivalence and completes the identity maps on `K` and `L` to an isomorphism from the
cone triangle to the triangle of the sequence. -/
@[stacks 09KF "part (1)", sga "4 XVII 1.1.1" "DG modules over a DGA"]
theorem exists_mappingConeTriangle_iso_associatedTriangle (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    ∃ (q : coneModule f ⟶ M),
      (∀ x : (coneModule f).M,
        q.toFun x = g.toFun ((cone f).coordinates x).1) ∧
      ∃ e : mappingConeTriangle f ≅ associatedTriangle A f g hfg,
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧
          e.hom.hom₃ = (toHomotopyCategory A).map q := by
  classical
  refine ⟨mappingConeToQuotient f g hfg, fun x => rfl, ?_⟩
  let c : CompatibleSplittings A f g :=
    Classical.choice (nonempty_compatibleSplittings A f g hfg)
  let q := mappingConeToQuotient f g hfg
  let s := quotientToMappingCone f g hfg c
  let Q := toHomotopyCategory A
  have hscomp : s ≫ q = 𝟙 M := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    show g.toFun ((cone f).coordinates ((cone f).coordinates.symm
      (c.s.toFun x, -connectingLinearMap f g hfg c x))).1 = x
    rw [LinearEquiv.apply_symm_apply]
    exact c.hs x
  let e₃ : Q.obj (coneModule f) ≅ Q.obj M :=
    isoOfHomotopicSection q s ⟨(mappingConeSectionHomotopy f g hfg c).symm⟩ hscomp
  have hcomm₂ : coneInclusion f ≫ q = g := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    show g.toFun ((cone f).coordinates
      ((coneInclusion f).toFun x)).1 = g.toFun x
    rw [(cone f).inclusion_coordinates]
  have hcomm₃ : Q.map (-coneProjection f) =
      Q.map q ≫ Q.map (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val :=
    quotient_map_eq_of_homotopic ⟨mappingConeBoundaryHomotopy f g hfg c⟩
  let e := Pretriangulated.Triangle.isoMk (mappingConeTriangle f)
    (associatedTriangle A f g hfg) (Iso.refl _) (Iso.refl _) e₃
    (by simp [mappingConeTriangle, associatedTriangle, associatedTriangleOfSplittings])
    (by
      dsimp [mappingConeTriangle, associatedTriangle, associatedTriangleOfSplittings]
      show Q.map (coneInclusion f) ≫ Q.map q = (𝟙 (Q.obj L)) ≫ Q.map g
      rw [← Functor.map_comp, hcomm₂]
      simp)
    (by
      dsimp [Q, mappingConeTriangle, e₃, associatedTriangle, associatedTriangleOfSplittings]
      rw [show Classical.choice (nonempty_compatibleSplittings A f g hfg) = c from rfl,
        hcomm₃]
      simp
      rfl)
  exact ⟨e, rfl, rfl, rfl⟩

/-- Every cone triangle is isomorphic to the triangle of an admissible short exact sequence, by
the identity on the first vertex and a comparison to the original second vertex compatible with
the given homomorphism. -/
@[stacks 09KF "part (2)", sga "4 XVII 1.1.1" "DG modules over a DGA"]
theorem exists_associatedTriangle_iso_mappingConeTriangle (f : K ⟶ L) :
    ∃ (L' M' : DifferentialGradedModule A) (f' : K ⟶ L') (g' : L' ⟶ M')
      (hfg : IsAdmissibleShortExact f' g') (b : L' ⟶ L),
      f' ≫ b = f ∧
        ∃ e : associatedTriangle A f' g' hfg ≅ mappingConeTriangle f,
          e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = (toHomotopyCategory A).map b := by
  classical
  obtain ⟨L', f', π, s, hfactor, hmono, hsπ, hπs⟩ :=
    exists_factorization_isAdmissibleMono f
  obtain ⟨M', g', hfg⟩ := exists_isAdmissibleShortExact f' hmono
  let Q := toHomotopyCategory A
  let eπ : Q.obj L' ≅ Q.obj L := isoOfHomotopicSection π s hπs hsπ
  have hπiso : IsIso (Q.map π) := eπ.isIso_hom
  obtain ⟨cc, hinc, hproj⟩ := exists_mappingConeMap_of_homotopic_square f' f (𝟙 K) π
    (homotopic_of_eq (by simpa using hfactor))
  have hciso : IsIso (Q.map cc) :=
    isIso_mappingConeMap_of_isIso f' f (𝟙 K) π cc (homotopic_of_eq (by simpa using hfactor.symm))
      (homotopic_of_eq hinc.symm) (homotopic_of_eq hproj)
  let ec : Q.obj (coneModule f') ≅ Q.obj (coneModule f) := asIso (Q.map cc)
  let coneIso : mappingConeTriangle f' ≅ mappingConeTriangle f :=
    Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) eπ ec
      (by
        dsimp [mappingConeTriangle, eπ, isoOfHomotopicSection]
        rw [← Functor.map_comp, hfactor]
        simp)
      (by
        dsimp [mappingConeTriangle]
        show Q.map (coneInclusion f') ≫ Q.map cc =
          Q.map π ≫ Q.map (coneInclusion f)
        rw [← Functor.map_comp, ← Functor.map_comp, hinc])
      (by
        dsimp [mappingConeTriangle]
        have hshift : shiftMap (𝟙 K) 1 = 𝟙 (shift K 1) := by apply Hom.ext; rfl
        have hnegBase : -coneProjection f' = cc ≫ (-coneProjection f) := by
          rw [Preadditive.comp_neg, hproj, hshift, Category.comp_id]
        have hneg : Q.map (-coneProjection f') = Q.map cc ≫ Q.map (-coneProjection f) :=
          (congrArg Q.map hnegBase).trans (Q.map_comp _ _)
        dsimp only [ec]
        show ((Q.map (-coneProjection f') ≫
            eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ K 1).symm) ≫
            (CategoryTheory.shiftFunctor (HomotopyCategory A) 1).map (𝟙 (Q.obj K))) =
          Q.map cc ≫ Q.map (-coneProjection f) ≫
            eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ K 1).symm
        rw [CategoryTheory.Functor.map_id, Category.comp_id, hneg, Category.assoc])
  obtain ⟨q, _, e, he1, he2, he3⟩ :=
    exists_mappingConeTriangle_iso_associatedTriangle f' g' hfg
  have hid {X : HomotopyCategory A} {u v : X ⟶ X} (h : u ≫ v = 𝟙 X) (hu : u = 𝟙 X) :
      v = 𝟙 X := by
    simpa [hu] using h
  refine ⟨L', M', f', g', hfg, π, hfactor, e.symm ≪≫ coneIso, ?_, ?_⟩
  · change e.inv.hom₁ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id]
    exact hid (Iso.hom_inv_id_triangle_hom₁ e) he1
  · change e.inv.hom₂ ≫ Q.map π = Q.map π
    rw [hid (Iso.hom_inv_id_triangle_hom₂ e) he2]
    exact Category.id_comp _

end DifferentialGradedModule
