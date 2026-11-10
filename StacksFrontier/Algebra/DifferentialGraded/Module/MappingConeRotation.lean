module

public import Mathlib.CategoryTheory.Triangulated.Rotate
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeTriangle

/-!
# Rotating the triangle of an admissible short exact sequence

For an admissible short exact sequence `K → L → M` of right differential graded modules, moving
the connecting arrow `M → K[1]` to the front produces, after desuspending it to a morphism
`M[-1] → K`, a triangle isomorphic to the mapping-cone triangle of that desuspended connecting
morphism. With the sign convention of the standard cone triangle, the inverse rotation negates
the first arrow, and is then the standard cone triangle of the negative of the desuspended
connecting morphism.

## Main definitions

* `DifferentialGradedModule.desuspendedConnectingHom`: the connecting homomorphism shifted back
  by one degree, a morphism `M[-1] ⟶ K`.
* `DifferentialGradedModule.resuspensionHom`: the canonical identification `M ≅ M[-1][1]`.
* `DifferentialGradedModule.rotatedAssociatedTriangle`,
  `DifferentialGradedModule.connectingConeTriangle` and
  `DifferentialGradedModule.inverseRotatedAssociatedTriangle`: the triangles compared below.
* `DifferentialGradedModule.comparisonHom`, `DifferentialGradedModule.comparisonInv`,
  `DifferentialGradedModule.comparisonHomNeg` and
  `DifferentialGradedModule.comparisonInvNeg`: the comparison isomorphisms `L ≅ C(δ[-1])`,
  with and without the sign.

## Main results

* `DifferentialGradedModule.rotatedAssociatedTriangle_iso_connectingConeTriangle`: the rotated
  triangle is the cone triangle of the desuspended connecting morphism.
* `DifferentialGradedModule.inverseRotatedAssociatedTriangle_iso_mappingConeTriangle`: with the
  standard sign convention, the inverse rotation is the standard cone triangle of the negative
  desuspended connecting morphism.

## Implementation notes

The connecting homomorphism is computed from the same internal choice of compatible graded
splittings as `DifferentialGradedModule.associatedTriangle`, so no splitting appears in any
statement and independence of that choice is inherited from the associated triangle. Shifting the
connecting homomorphism by `-1` gives a morphism out of `M[-1]`, and the last arrow of the
rotated sequence uses the canonical identification of `M` with `M[-1][1]`.

## References

* [Stacks Project, Tag 09KC](https://stacks.math.columbia.edu/tag/09KC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
variable {K L M : DifferentialGradedModule A}

/-- The connecting homomorphism, shifted from `M ⟶ K[1]` to `M[-1] ⟶ K`. -/
noncomputable def desuspendedConnectingHom (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) : shift M (-1) ⟶ K :=
  let c := Classical.choice (nonempty_compatibleSplittings A f g hfg)
  shiftMap (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val (-1) ≫
    shiftAddInv A K 1 (-1) ≫ shiftZeroHom A K

/-- The canonical identification of `M` with `M[-1][1]`. -/
noncomputable def resuspensionHom (M : DifferentialGradedModule A) :
    M ⟶ shift (shift M (-1)) 1 :=
  shiftZeroInv A M ≫
    eqToHom (by norm_num : shift M 0 = shift M ((-1 : ℤ) + 1)) ≫
    shiftAddHom A M (-1) 1

/-- The triangle obtained by moving the connecting arrow to the first position. -/
noncomputable def rotatedAssociatedTriangle (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    Pretriangulated.Triangle (HomotopyCategory A) :=
  Pretriangulated.Triangle.mk
    ((toHomotopyCategory A).map (desuspendedConnectingHom f g hfg))
    (associatedTriangle A f g hfg).mor₁
    ((associatedTriangle A f g hfg).mor₂ ≫
      (toHomotopyCategory A).map (resuspensionHom M) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ (shift M (-1)) 1).symm)

/-- The cone triangle of the desuspended connecting homomorphism. -/
noncomputable def connectingConeTriangle (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    Pretriangulated.Triangle (HomotopyCategory A) :=
  Pretriangulated.Triangle.mk
    ((toHomotopyCategory A).map (desuspendedConnectingHom f g hfg))
    ((toHomotopyCategory A).map (coneInclusion (desuspendedConnectingHom f g hfg)))
    ((toHomotopyCategory A).map (coneProjection (desuspendedConnectingHom f g hfg)) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ (shift M (-1)) 1).symm)

/-- The inverse rotation with the sign convention of the standard cone triangle. Its first arrow
is the negative desuspended connecting map. -/
noncomputable def inverseRotatedAssociatedTriangle (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    Pretriangulated.Triangle (HomotopyCategory A) :=
  Pretriangulated.Triangle.mk
    ((toHomotopyCategory A).map (-desuspendedConnectingHom f g hfg))
    (associatedTriangle A f g hfg).mor₁
    ((associatedTriangle A f g hfg).mor₂ ≫
      (toHomotopyCategory A).map (resuspensionHom M) ≫
      eqToHom (CategoryTheory.Quotient.functor_obj_shift
        (homotopyRel A) ℤ (shift M (-1)) 1).symm)

/-- The desuspended connecting map sends `x` to `π (d (s x))`, where `s` and `π` are the chosen
compatible graded splittings. -/
theorem desuspendedConnectingHom_apply (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (x : M.M) :
    (desuspendedConnectingHom f g hfg).toFun x =
      (Classical.choice (nonempty_compatibleSplittings A f g hfg)).π.toFun
        (L.d ((Classical.choice (nonempty_compatibleSplittings A f g hfg)).s.toFun x)) := by
  let c := Classical.choice (nonempty_compatibleSplittings A f g hfg)
  change (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun x = _
  exact (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).property x

/-- The comparison `L ⟶ C(δ[-1])` built from compatible graded splittings. -/
noncomputable def comparisonHom (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g)
    (φ : shift M (-1) ⟶ K) (hφ : ∀ x : M.M, φ.toFun x = c.π.toFun (L.d (c.s.toFun x))) :
    L ⟶ coneModule φ where
  toFun := LinearMap.prod c.π.toFun g.toFun
  map_smul := by
    intro x a
    change (c.π.toFun (MulOpposite.op a • x), g.toFun (MulOpposite.op a • x)) =
      MulOpposite.op a • (c.π.toFun x, g.toFun x)
    simp [c.π.map_smul, g.map_smul]
  map_grading := by
    intro n x hx
    refine ((cone φ).grading_iff n _).mpr ?_
    rw [mappingCone_coordinates_apply]
    refine ⟨c.π.map_grading n x hx, ?_⟩
    change g.toFun x ∈ (shift M (-1)).grading (n + 1)
    rw [shift_grading, show n + 1 + (-1 : ℤ) = n by omega]
    exact g.map_grading n x hx
  map_d := by
    apply LinearMap.ext
    intro x
    refine Prod.ext ?_ ?_
    · change c.π.toFun (L.d x) = K.d (c.π.toFun x) + φ.toFun (g.toFun x)
      have hproj (y : K.M) : c.π.toFun (L.d (f.toFun y)) = K.d y := by
        have hf := LinearMap.congr_fun f.map_d y
        change f.toFun (K.d y) = L.d (f.toFun y) at hf
        exact (congrArg c.π.toFun hf.symm).trans (c.hπ _)
      calc
        c.π.toFun (L.d x) =
            c.π.toFun (L.d (f.toFun (c.π.toFun x) + c.s.toFun (g.toFun x))) :=
              congrArg (fun z => c.π.toFun (L.d z)) (c.decomposition hfg x).symm
        _ = K.d (c.π.toFun x) + φ.toFun (g.toFun x) := by
          simp only [map_add]
          rw [hproj, hφ]
    · change g.toFun (L.d x) = -(shift M (-1)).d (g.toFun x)
      have hg := LinearMap.congr_fun g.map_d x
      change g.toFun (L.d x) = M.d (g.toFun x) at hg
      rw [hg]
      simp [shift_d, Int.negOnePow_neg, Units.smul_def]

/-- The inverse of `comparisonHom`. -/
noncomputable def comparisonInv (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g)
    (φ : shift M (-1) ⟶ K) (hφ : ∀ x : M.M, φ.toFun x = c.π.toFun (L.d (c.s.toFun x))) :
    coneModule φ ⟶ L where
  toFun := (f.toFun.comp (LinearMap.fst R K.M (shift M (-1)).M) +
    c.s.toFun.comp (LinearMap.snd R K.M (shift M (-1)).M)).comp
      (cone φ).coordinates.toLinearMap
  map_smul := by
    intro z a
    change f.toFun ((cone φ).coordinates (MulOpposite.op a • z)).1 +
        c.s.toFun ((cone φ).coordinates (MulOpposite.op a • z)).2 =
      MulOpposite.op a • (f.toFun ((cone φ).coordinates z).1 +
        c.s.toFun ((cone φ).coordinates z).2)
    rw [mappingCone_coordinates_apply, mappingCone_coordinates_apply]
    change f.toFun (MulOpposite.op a • z.1) + c.s.toFun (MulOpposite.op a • z.2) =
      MulOpposite.op a • (f.toFun z.1 + c.s.toFun z.2)
    rw [f.map_smul, c.s.map_smul, smul_add]
  map_grading := by
    intro n z hz
    have hz' := ((cone φ).grading_iff n z).mp hz
    change f.toFun ((cone φ).coordinates z).1 +
      c.s.toFun ((cone φ).coordinates z).2 ∈ L.grading n
    refine (L.grading n).add_mem (f.map_grading n _ hz'.1) ?_
    refine c.s.map_grading n _ ?_
    have h2 := hz'.2
    rwa [shift_grading, show n + 1 + (-1 : ℤ) = n by omega] at h2
  map_d := by
    apply LinearMap.ext
    intro z
    change f.toFun ((cone φ).coordinates ((coneModule φ).d z)).1 +
        c.s.toFun ((cone φ).coordinates ((coneModule φ).d z)).2 =
      L.d (f.toFun ((cone φ).coordinates z).1 +
        c.s.toFun ((cone φ).coordinates z).2)
    rw [(cone φ).differential]
    change f.toFun (K.d ((cone φ).coordinates z).1 +
        φ.toFun ((cone φ).coordinates z).2) +
        c.s.toFun (-(shift M (-1)).d ((cone φ).coordinates z).2) =
      L.d (f.toFun ((cone φ).coordinates z).1 +
        c.s.toFun ((cone φ).coordinates z).2)
    have hshift : -(shift M (-1)).d ((cone φ).coordinates z).2 =
        M.d ((cone φ).coordinates z).2 := by
      simp [shift_d, Int.negOnePow_neg, Units.smul_def]
    rw [hshift]
    have hgchain : g.toFun (L.d (c.s.toFun ((cone φ).coordinates z).2)) =
        M.d ((cone φ).coordinates z).2 :=
      (LinearMap.congr_fun g.map_d _).trans (congrArg M.d (c.hs _))
    calc
      f.toFun (K.d ((cone φ).coordinates z).1 +
            φ.toFun ((cone φ).coordinates z).2) +
          c.s.toFun (M.d ((cone φ).coordinates z).2) =
          f.toFun (K.d ((cone φ).coordinates z).1) +
            f.toFun (c.π.toFun (L.d (c.s.toFun ((cone φ).coordinates z).2))) +
            c.s.toFun (g.toFun (L.d (c.s.toFun ((cone φ).coordinates z).2))) := by
              rw [map_add, hφ, hgchain]
      _ = f.toFun (K.d ((cone φ).coordinates z).1) +
            L.d (c.s.toFun ((cone φ).coordinates z).2) := by
            simpa [add_assoc] using congrArg
              (fun t => f.toFun (K.d ((cone φ).coordinates z).1) + t)
              (c.decomposition hfg (L.d (c.s.toFun ((cone φ).coordinates z).2)))
      _ = L.d (f.toFun ((cone φ).coordinates z).1 +
            c.s.toFun ((cone φ).coordinates z).2) := by
            rw [map_add]
            congr 1
            exact LinearMap.congr_fun f.map_d ((cone φ).coordinates z).1

/-- The comparison `L ⟶ C(-δ[-1])`, used for the sign-corrected inverse rotation. -/
noncomputable def comparisonHomNeg (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g)
    (φ : shift M (-1) ⟶ K) (hφ : ∀ x : M.M, φ.toFun x = c.π.toFun (L.d (c.s.toFun x))) :
    L ⟶ coneModule (-φ) where
  toFun := LinearMap.prod c.π.toFun (-g.toFun)
  map_smul := by
    intro x a
    change (c.π.toFun (MulOpposite.op a • x), -g.toFun (MulOpposite.op a • x)) =
      MulOpposite.op a • (c.π.toFun x, -g.toFun x)
    simp [c.π.map_smul, g.map_smul]
  map_grading := by
    intro n x hx
    refine ((cone (-φ)).grading_iff n _).mpr ?_
    rw [mappingCone_coordinates_apply]
    refine ⟨c.π.map_grading n x hx, ?_⟩
    change -g.toFun x ∈ (shift M (-1)).grading (n + 1)
    rw [shift_grading, show n + 1 + (-1 : ℤ) = n by omega]
    exact (M.grading n).neg_mem (g.map_grading n x hx)
  map_d := by
    apply LinearMap.ext
    intro x
    refine Prod.ext ?_ ?_
    · change c.π.toFun (L.d x) = K.d (c.π.toFun x) + (-φ).toFun (-g.toFun x)
      have hproj (y : K.M) : c.π.toFun (L.d (f.toFun y)) = K.d y := by
        have hf := LinearMap.congr_fun f.map_d y
        change f.toFun (K.d y) = L.d (f.toFun y) at hf
        exact (congrArg c.π.toFun hf.symm).trans (c.hπ _)
      have hfirst : c.π.toFun (L.d x) = K.d (c.π.toFun x) + φ.toFun (g.toFun x) := by
        calc
          c.π.toFun (L.d x) =
              c.π.toFun (L.d (f.toFun (c.π.toFun x) + c.s.toFun (g.toFun x))) :=
                congrArg (fun z => c.π.toFun (L.d z)) (c.decomposition hfg x).symm
          _ = K.d (c.π.toFun x) + φ.toFun (g.toFun x) := by
            simp only [map_add]
            rw [hproj, hφ]
      refine hfirst.trans ?_
      congr 1
      change φ.toFun (g.toFun x) = (-φ.toFun) (-g.toFun x)
      rw [LinearMap.neg_apply, map_neg, neg_neg]
    · change -g.toFun (L.d x) = -(shift M (-1)).d (-g.toFun x)
      have hg := LinearMap.congr_fun g.map_d x
      change g.toFun (L.d x) = M.d (g.toFun x) at hg
      rw [hg]
      simp [shift_d, Int.negOnePow_neg, Units.smul_def]

/-- The inverse of `comparisonHomNeg`. -/
noncomputable def comparisonInvNeg (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) (c : CompatibleSplittings A f g)
    (φ : shift M (-1) ⟶ K) (hφ : ∀ x : M.M, φ.toFun x = c.π.toFun (L.d (c.s.toFun x))) :
    coneModule (-φ) ⟶ L where
  toFun := (f.toFun.comp (LinearMap.fst R K.M (shift M (-1)).M) -
    c.s.toFun.comp (LinearMap.snd R K.M (shift M (-1)).M)).comp
      (cone (-φ)).coordinates.toLinearMap
  map_smul := by
    intro z a
    change f.toFun ((cone (-φ)).coordinates (MulOpposite.op a • z)).1 -
        c.s.toFun ((cone (-φ)).coordinates (MulOpposite.op a • z)).2 =
      MulOpposite.op a • (f.toFun ((cone (-φ)).coordinates z).1 -
        c.s.toFun ((cone (-φ)).coordinates z).2)
    rw [mappingCone_coordinates_apply, mappingCone_coordinates_apply]
    change f.toFun (MulOpposite.op a • z.1) - c.s.toFun (MulOpposite.op a • z.2) =
      MulOpposite.op a • (f.toFun z.1 - c.s.toFun z.2)
    rw [f.map_smul, c.s.map_smul, smul_sub]
  map_grading := by
    intro n z hz
    have hz' := ((cone (-φ)).grading_iff n z).mp hz
    change f.toFun ((cone (-φ)).coordinates z).1 -
      c.s.toFun ((cone (-φ)).coordinates z).2 ∈ L.grading n
    refine (L.grading n).sub_mem (f.map_grading n _ hz'.1) ?_
    refine c.s.map_grading n _ ?_
    have h2 := hz'.2
    rwa [shift_grading, show n + 1 + (-1 : ℤ) = n by omega] at h2
  map_d := by
    apply LinearMap.ext
    intro z
    change f.toFun ((cone (-φ)).coordinates ((coneModule (-φ)).d z)).1 -
        c.s.toFun ((cone (-φ)).coordinates ((coneModule (-φ)).d z)).2 =
      L.d (f.toFun ((cone (-φ)).coordinates z).1 -
        c.s.toFun ((cone (-φ)).coordinates z).2)
    rw [(cone (-φ)).differential]
    change f.toFun (K.d ((cone (-φ)).coordinates z).1 +
        (-φ).toFun ((cone (-φ)).coordinates z).2) -
        c.s.toFun (-(shift M (-1)).d ((cone (-φ)).coordinates z).2) =
      L.d (f.toFun ((cone (-φ)).coordinates z).1 -
        c.s.toFun ((cone (-φ)).coordinates z).2)
    have hshift : -(shift M (-1)).d ((cone (-φ)).coordinates z).2 =
        M.d ((cone (-φ)).coordinates z).2 := by
      simp [shift_d, Int.negOnePow_neg, Units.smul_def]
    rw [hshift]
    have hgchain : g.toFun (L.d (c.s.toFun ((cone (-φ)).coordinates z).2)) =
        M.d ((cone (-φ)).coordinates z).2 :=
      (LinearMap.congr_fun g.map_d _).trans (congrArg M.d (c.hs _))
    have hneg : (-φ).toFun ((cone (-φ)).coordinates z).2 =
        -φ.toFun ((cone (-φ)).coordinates z).2 := rfl
    calc
      f.toFun (K.d ((cone (-φ)).coordinates z).1 +
            (-φ).toFun ((cone (-φ)).coordinates z).2) -
          c.s.toFun (M.d ((cone (-φ)).coordinates z).2) =
          f.toFun (K.d ((cone (-φ)).coordinates z).1) -
            f.toFun (φ.toFun ((cone (-φ)).coordinates z).2) -
            c.s.toFun (g.toFun (L.d (c.s.toFun ((cone (-φ)).coordinates z).2))) := by
              rw [hneg, map_add, map_neg, hφ, hgchain]
              abel
      _ = f.toFun (K.d ((cone (-φ)).coordinates z).1) -
          (f.toFun (c.π.toFun (L.d (c.s.toFun ((cone (-φ)).coordinates z).2))) +
            c.s.toFun (g.toFun (L.d (c.s.toFun ((cone (-φ)).coordinates z).2)))) := by
              rw [hφ]
              abel
      _ = f.toFun (K.d ((cone (-φ)).coordinates z).1) -
          L.d (c.s.toFun ((cone (-φ)).coordinates z).2) := by
            rw [c.decomposition hfg (L.d (c.s.toFun ((cone (-φ)).coordinates z).2))]
      _ = L.d (f.toFun ((cone (-φ)).coordinates z).1 -
            c.s.toFun ((cone (-φ)).coordinates z).2) := by
            rw [map_sub]
            congr 1
            exact LinearMap.congr_fun f.map_d ((cone (-φ)).coordinates z).1

/-- The rotated admissible-sequence triangle is isomorphic to the cone triangle of its
desuspended connecting homomorphism. -/
@[stacks 09KC "source sign convention"]
theorem rotatedAssociatedTriangle_iso_connectingConeTriangle (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    Nonempty (rotatedAssociatedTriangle f g hfg ≅ connectingConeTriangle f g hfg) := by
  classical
  let c := Classical.choice (nonempty_compatibleSplittings A f g hfg)
  let φ := desuspendedConnectingHom f g hfg
  have hφ : ∀ x : M.M, φ.toFun x = c.π.toFun (L.d (c.s.toFun x)) := fun x =>
    desuspendedConnectingHom_apply f g hfg x
  let e := comparisonHom f g hfg c φ hφ
  let ei := comparisonInv f g hfg c φ hφ
  have hgf : ∀ y : K.M, g.toFun (f.toFun y) = 0 := by
    intro y
    apply LinearMap.mem_ker.mp
    rw [← hfg.exact]
    exact ⟨y, rfl⟩
  have hπs : ∀ z : M.M, c.π.toFun (c.s.toFun z) = 0 := by
    intro z
    apply LinearMap.mem_ker.mp
    rw [c.hker]
    exact ⟨z, rfl⟩
  have hleft : e ≫ ei = 𝟙 L := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change f.toFun (c.π.toFun x) + c.s.toFun (g.toFun x) = x
    exact c.decomposition hfg x
  have hright : ei ≫ e = 𝟙 (coneModule φ) := by
    apply Hom.ext
    apply LinearMap.ext
    intro z
    apply (cone φ).coordinates.injective
    change (c.π.toFun (f.toFun ((cone φ).coordinates z).1 +
        c.s.toFun ((cone φ).coordinates z).2),
      g.toFun (f.toFun ((cone φ).coordinates z).1 +
        c.s.toFun ((cone φ).coordinates z).2)) = (cone φ).coordinates z
    refine Prod.ext ?_ ?_
    · rw [map_add, c.hπ, hπs, add_zero]
    · dsimp only
      rw [map_add, hgf, c.hs, zero_add]
  let eIso : L ≅ coneModule φ :=
    { hom := e, inv := ei, hom_inv_id := hleft, inv_hom_id := hright }
  have hcomm2 : f ≫ e = coneInclusion φ := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    apply (cone φ).coordinates.injective
    rw [(cone φ).inclusion_coordinates]
    change (c.π.toFun (f.toFun x), g.toFun (f.toFun x)) = (x, 0)
    exact Prod.ext (c.hπ x) (hgf x)
  have hcomm3 : e ≫ coneProjection φ = g ≫ resuspensionHom M := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    rfl
  refine ⟨Pretriangulated.Triangle.isoMk (rotatedAssociatedTriangle f g hfg)
    (connectingConeTriangle f g hfg) (Iso.refl _) (Iso.refl _)
    ((toHomotopyCategory A).mapIso eIso) ?_ ?_ ?_⟩
  · rfl
  · change (toHomotopyCategory A).map f ≫ (toHomotopyCategory A).map e =
      (toHomotopyCategory A).map (coneInclusion φ)
    rw [← CategoryTheory.Functor.map_comp, hcomm2]
  · change ((toHomotopyCategory A).map g ≫
        (toHomotopyCategory A).map (resuspensionHom M) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift
          (homotopyRel A) ℤ (shift M (-1)) 1).symm) ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A) 1).map (𝟙 _) =
      (toHomotopyCategory A).map e ≫
        (toHomotopyCategory A).map (coneProjection φ) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift
          (homotopyRel A) ℤ (shift M (-1)) 1).symm
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, hcomm3]

/-- The standard inverse rotation of an admissible-sequence triangle is the standard cone
triangle of the negative desuspended connecting map. -/
@[stacks 09KC "standard cone sign convention"]
theorem inverseRotatedAssociatedTriangle_iso_mappingConeTriangle (f : K ⟶ L) (g : L ⟶ M)
    (hfg : IsAdmissibleShortExact f g) :
    Nonempty (inverseRotatedAssociatedTriangle f g hfg ≅
      mappingConeTriangle (-desuspendedConnectingHom f g hfg)) := by
  classical
  let c := Classical.choice (nonempty_compatibleSplittings A f g hfg)
  let φ := desuspendedConnectingHom f g hfg
  have hφ : ∀ x : M.M, φ.toFun x = c.π.toFun (L.d (c.s.toFun x)) := fun x =>
    desuspendedConnectingHom_apply f g hfg x
  let e := comparisonHomNeg f g hfg c φ hφ
  let ei := comparisonInvNeg f g hfg c φ hφ
  have hgf : ∀ y : K.M, g.toFun (f.toFun y) = 0 := by
    intro y
    apply LinearMap.mem_ker.mp
    rw [← hfg.exact]
    exact ⟨y, rfl⟩
  have hπs : ∀ z : M.M, c.π.toFun (c.s.toFun z) = 0 := by
    intro z
    apply LinearMap.mem_ker.mp
    rw [c.hker]
    exact ⟨z, rfl⟩
  have hleft : e ≫ ei = 𝟙 L := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change f.toFun (c.π.toFun x) - c.s.toFun (-g.toFun x) = x
    simpa [map_neg, sub_neg_eq_add] using c.decomposition hfg x
  have hright : ei ≫ e = 𝟙 (coneModule (-φ)) := by
    apply Hom.ext
    apply LinearMap.ext
    intro z
    apply (cone (-φ)).coordinates.injective
    change (c.π.toFun (f.toFun ((cone (-φ)).coordinates z).1 -
          c.s.toFun ((cone (-φ)).coordinates z).2),
      -g.toFun (f.toFun ((cone (-φ)).coordinates z).1 -
          c.s.toFun ((cone (-φ)).coordinates z).2)) =
      (cone (-φ)).coordinates z
    refine Prod.ext ?_ ?_
    · simp [map_sub, c.hπ, hπs]
    · simp [map_sub, hgf, c.hs]
  let eIso : L ≅ coneModule (-φ) :=
    { hom := e, inv := ei, hom_inv_id := hleft, inv_hom_id := hright }
  have hcomm2 : f ≫ e = coneInclusion (-φ) := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    apply (cone (-φ)).coordinates.injective
    rw [(cone (-φ)).inclusion_coordinates]
    change (c.π.toFun (f.toFun x), -g.toFun (f.toFun x)) = (x, 0)
    refine Prod.ext (c.hπ x) ?_
    simp [hgf]
  have hcomm3 : e ≫ (-coneProjection (-φ)) = g ≫ resuspensionHom M := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change -(-g.toFun x) = (resuspensionHom M).toFun (g.toFun x)
    simp [resuspensionHom, shiftZeroInv, shiftAddHom]
  refine ⟨Pretriangulated.Triangle.isoMk (inverseRotatedAssociatedTriangle f g hfg)
    (mappingConeTriangle (-φ)) (Iso.refl _) (Iso.refl _)
    ((toHomotopyCategory A).mapIso eIso) ?_ ?_ ?_⟩
  · rfl
  · change (toHomotopyCategory A).map f ≫ (toHomotopyCategory A).map e =
      (toHomotopyCategory A).map (coneInclusion (-φ))
    rw [← CategoryTheory.Functor.map_comp, hcomm2]
  · change ((toHomotopyCategory A).map g ≫
        (toHomotopyCategory A).map (resuspensionHom M) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift
          (homotopyRel A) ℤ (shift M (-1)) 1).symm) ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A) 1).map (𝟙 _) =
      (toHomotopyCategory A).map e ≫
        (toHomotopyCategory A).map (-coneProjection (-φ)) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift
          (homotopyRel A) ℤ (shift M (-1)) 1).symm
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, hcomm3]

end DifferentialGradedModule
