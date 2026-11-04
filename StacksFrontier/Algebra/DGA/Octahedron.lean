module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DGA.Pretriangulated

/-!
# The octahedron axiom for the homotopy category

Two composable homomorphisms `α : K ⟶ L` and `β : L ⟶ M` of right differential graded
`A`-modules give three cone triangles, on `α`, on `β`, and on `α ≫ β`, and these fit into an
octahedron: the two induced maps of cones satisfy the four commutations of (TR 4), and the
triangle they form is itself distinguished.

## Main definitions

* `DifferentialGradedModule.octaMap₁` and `DifferentialGradedModule.octaMap₃` are the two
  comparison maps of cones, `C(α) ⟶ C(α ≫ β)` and `C(α ≫ β) ⟶ C(β)`.
* `DifferentialGradedModule.coneCancel` and `DifferentialGradedModule.coneSection` exhibit
  `C(octaMap₁)` and `C(β)` as homotopy equivalent: the cone of the comparison map cancels.
* `DifferentialGradedModule.coneOctahedron` is the octahedron itself.

## Main results

* `DifferentialGradedModule.octahedron_of_admissible_monos` is the statement of Tag 09KI: the
  three distinguished triangles and the two connecting maps, with the four commutations and the
  fourth distinguished triangle.
* `DifferentialGradedModule.instIsTriangulatedHomotopyCategory`: the homotopy category of right
  differential graded `A`-modules is triangulated.

## Implementation notes

The three distinguished triangles are the cone triangles, so "distinguished" here is
`DifferentialGradedModule.distinguishedConeTriangles`, the class with which
`DifferentialGradedModule.instPretriangulatedHomotopyCategory` is instantiated, and therefore the
class that `CategoryTheory.Pretriangulated.Octahedron` and
`CategoryTheory.Pretriangulated.IsTriangulated` are about. The chapter's other
distinguished-triangle predicate, `DifferentialGradedModule.IsDistinguishedTriangle`, is defined
through admissible short exact sequences and is not used here; the two are not identified in this
file.

The two comparison maps are instances of `DifferentialGradedModule.coneMapOfHomotopy` for squares
that commute on the nose, so all four commutations of (TR 4) reduce to the already-established
`DifferentialGradedModule.coneIncl_coneMapOfHomotopy`,
`DifferentialGradedModule.coneMapOfHomotopy_coneProj`, and the third square of
`DifferentialGradedModule.coneTriangleMapOfHomotopy`.

The only new content is the last field. The triangle `C(α) ⟶ C(α ≫ β) ⟶ C(β) ⟶ C(α)[1]` is
shown distinguished by identifying it with the cone triangle of `octaMap₁`, whose third vertex
is `C(octaMap₁)` with underlying module `(M ⊕ K) ⊕ (L ⊕ K)`. The map `coneCancel` collapses this
to `C(β) = M ⊕ L` by `((m, k), (l, j)) ↦ (m, α k + l)`, with one-sided inverse `coneSection`
given by `(m, l) ↦ ((m, 0), (l, 0))`; the composite `coneSection ≫ coneCancel` is the identity on
the nose, and `coneCancel ≫ coneSection` is homotopic to the identity by the homotopy
`((m, k), (l, j)) ↦ ((0, 0), (0, -k))`. The remaining square needs the boundary homotopy
`((m, k), (l, j)) ↦ (0, k)`, which identifies `coneProj (octaMap₁)` with
`coneCancel ≫ coneProj β ≫ (coneIncl α)[1]` in the homotopy category.

Every differential and homotopy equation is checked in the single coordinate spelling
`(M.M × K.M) × (L.M × K.M)` that `coneObject` supplies, with `Prod.ext` splitting each equation
into its four scalar components and `abel` closing each one. No transport between two spellings
of the cone arises, so no reducibility, defeq or heartbeat option is used, and the connecting
arrows are the natural `DifferentialGradedModule.quotientShiftIso` throughout rather than an
`eqToHom` on the shift of a quotient.

## References

* [Stacks Project, Tag 09KI](https://stacks.math.columbia.edu/tag/09KI)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Triangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
variable {K L M : DifferentialGradedModule.{u, v, w} A}

/-- The shift of an identity homomorphism is an identity. -/
@[simp] theorem shiftMap_id (K : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    shiftMap (𝟙 K) k = 𝟙 (shift K k) := rfl

/-- A cone triangle is distinguished, written out as `Triangle.mk` of its three morphisms so that
it matches the hypotheses of `CategoryTheory.Pretriangulated.Octahedron`. -/
theorem coneTriangle_mk_mem (f : K ⟶ L) :
    Triangle.mk ((toHomotopyCategory A).map f) ((toHomotopyCategory A).map (coneIncl f))
        ((toHomotopyCategory A).map (coneProj f) ≫ (quotientShiftIso K 1).hom) ∈
      distTriang (HomotopyCategory.{u, v, w} A) :=
  ⟨K, L, f, ⟨Iso.refl _⟩⟩

section ConeOctahedron

variable (α : K ⟶ L) (β : L ⟶ M)

/-- The square `α ≫ β = 𝟙 K ≫ (α ≫ β)` commutes on the nose. -/
noncomputable def octaHomotopy₁ : Homotopy (α ≫ β) (𝟙 K ≫ (α ≫ β)) :=
  Homotopy.ofEq (Category.id_comp _).symm

/-- The square `(α ≫ β) ≫ 𝟙 M = α ≫ β` commutes on the nose. -/
noncomputable def octaHomotopy₃ : Homotopy ((α ≫ β) ≫ 𝟙 M) (α ≫ β) :=
  Homotopy.ofEq (Category.comp_id _)

/-- The comparison map of cones `C(α) ⟶ C(α ≫ β)`, which is `(l, k) ↦ (β l, k)`. -/
noncomputable def octaMap₁ : coneObject α ⟶ coneObject (α ≫ β) :=
  coneMapOfHomotopy (octaHomotopy₁ α β)

/-- The comparison map of cones `C(α ≫ β) ⟶ C(β)`, which is `(m, k) ↦ (m, α k)`. -/
noncomputable def octaMap₃ : coneObject (α ≫ β) ⟶ coneObject β :=
  coneMapOfHomotopy (octaHomotopy₃ α β)

/-- The first comparison map is compatible with the inclusions. -/
theorem coneIncl_octaMap₁ : coneIncl α ≫ octaMap₁ α β = β ≫ coneIncl (α ≫ β) :=
  coneIncl_coneMapOfHomotopy (octaHomotopy₁ α β)

/-- The first comparison map is compatible with the projections. -/
theorem octaMap₁_coneProj :
    octaMap₁ α β ≫ coneProj (α ≫ β) = coneProj α ≫ shiftMap (𝟙 K) 1 :=
  coneMapOfHomotopy_coneProj (octaHomotopy₁ α β)

/-- The second comparison map is compatible with the inclusions. -/
theorem coneIncl_octaMap₃ : coneIncl (α ≫ β) ≫ octaMap₃ α β = 𝟙 M ≫ coneIncl β :=
  coneIncl_coneMapOfHomotopy (octaHomotopy₃ α β)

/-- The second comparison map is compatible with the projections. -/
theorem octaMap₃_coneProj :
    octaMap₃ α β ≫ coneProj β = coneProj (α ≫ β) ≫ shiftMap α 1 :=
  coneMapOfHomotopy_coneProj (octaHomotopy₃ α β)

/-- The cancellation map `C(octaMap₁) ⟶ C(β)`, which is `((m, k), (l, j)) ↦ (m, α k + l)`. -/
noncomputable def coneCancel : coneObject (octaMap₁ α β) ⟶ coneObject β where
  toFun :=
    { toFun := fun x => (x.1.1, α.toFun x.1.2 + x.2.1)
      map_add' := fun x y => by
        refine Prod.ext rfl ?_
        change α.toFun (x.1.2 + y.1.2) + (x.2.1 + y.2.1) =
          α.toFun x.1.2 + x.2.1 + (α.toFun y.1.2 + y.2.1)
        rw [map_add]
        abel
      map_smul' := fun r x => by
        refine Prod.ext rfl ?_
        change α.toFun (r • x.1.2) + r • x.2.1 = r • (α.toFun x.1.2 + x.2.1)
        rw [map_smul, smul_add] }
  map_smul x a := by
    refine Prod.ext rfl ?_
    change α.toFun (MulOpposite.op a • x.1.2) + MulOpposite.op a • x.2.1 =
      MulOpposite.op a • (α.toFun x.1.2 + x.2.1)
    rw [α.map_smul, smul_add]
  map_grading n x hx := by
    obtain ⟨hx₁, hx₂⟩ := (coneGrading_mem n x).mp hx
    obtain ⟨hm, hk⟩ := (coneGrading_mem n x.1).mp hx₁
    obtain ⟨hl, -⟩ := (coneGrading_mem (n + 1) x.2).mp hx₂
    exact (coneGrading_mem n _).mpr
      ⟨hm, (L.grading (n + 1)).add_mem (α.map_grading (n + 1) x.1.2 hk) hl⟩
  map_d := by
    refine LinearMap.ext fun x => ?_
    have hα := LinearMap.congr_fun α.map_d x.1.2
    simp only [LinearMap.comp_apply] at hα
    refine Prod.ext ?_ ?_
    · change M.d x.1.1 + β.toFun (α.toFun x.1.2) + (β.toFun x.2.1 + 0) =
        M.d x.1.1 + β.toFun (α.toFun x.1.2 + x.2.1)
      rw [map_add]
      abel
    · change α.toFun (-K.d x.1.2 + x.2.2) + -(L.d x.2.1 + α.toFun x.2.2) =
        -L.d (α.toFun x.1.2 + x.2.1)
      rw [map_add, map_neg, hα, map_add]
      abel

/-- The cancellation map sends `((m, k), (l, j))` to `(m, α k + l)`. -/
@[simp] theorem coneCancel_toFun_apply (x : (M.M × K.M) × (L.M × K.M)) :
    (coneCancel α β).toFun x = (x.1.1, α.toFun x.1.2 + x.2.1) := rfl

/-- The section `C(β) ⟶ C(octaMap₁)` of the cancellation map, which is
`(m, l) ↦ ((m, 0), (l, 0))`. -/
noncomputable def coneSection : coneObject β ⟶ coneObject (octaMap₁ α β) where
  toFun :=
    { toFun := fun x => ((x.1, (0 : K.M)), (x.2, (0 : K.M)))
      map_add' := fun x y => by
        refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_) <;> exact (add_zero _).symm
      map_smul' := fun r x => by
        refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_) <;> exact (smul_zero r).symm }
  map_smul x a := by
    refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_) <;> exact (smul_zero _).symm
  map_grading n x hx := by
    obtain ⟨hm, hl⟩ := (coneGrading_mem n x).mp hx
    refine (coneGrading_mem n _).mpr ⟨?_, ?_⟩
    · exact (coneGrading_mem n _).mpr ⟨hm, (K.grading (n + 1)).zero_mem⟩
    · exact (coneGrading_mem (n + 1) _).mpr ⟨hl, (K.grading (n + 1 + 1)).zero_mem⟩
  map_d := by
    refine LinearMap.ext fun x => ?_
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change M.d x.1 + β.toFun x.2 =
        M.d x.1 + β.toFun (α.toFun 0) + (β.toFun x.2 + 0)
      rw [map_zero, map_zero]
      abel
    · change (0 : K.M) = -K.d 0 + 0
      rw [map_zero]
      abel
    · change -L.d x.2 = -(L.d x.2 + α.toFun 0)
      rw [map_zero]
      abel
    · change (0 : K.M) = - -K.d 0
      rw [map_zero]
      abel

/-- The section sends `(m, l)` to `((m, 0), (l, 0))`. -/
@[simp] theorem coneSection_toFun_apply (x : M.M × L.M) :
    (coneSection α β).toFun x = ((x.1, (0 : K.M)), (x.2, (0 : K.M))) := rfl

/-- The section followed by the cancellation map is the identity of `C(β)`, on the nose. -/
theorem coneSection_coneCancel : coneSection α β ≫ coneCancel α β = 𝟙 (coneObject β) := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  refine Prod.ext rfl ?_
  show α.toFun 0 + x.2 = x.2
  rw [map_zero, zero_add]

/-- The contracting homotopy for the cancellation map: on `(M ⊕ K) ⊕ (L ⊕ K)` it is
`((m, k), (l, j)) ↦ ((0, 0), (0, -k))`, which lowers the degree by one. -/
noncomputable def coneCancelHomotopy :
    Homotopy (coneCancel α β ≫ coneSection α β) (𝟙 (coneObject (octaMap₁ α β))) where
  toLinearMap :=
    { toFun := fun x => (((0 : M.M), (0 : K.M)), ((0 : L.M), -x.1.2))
      map_add' := fun x y => by
        refine Prod.ext (Prod.ext (add_zero _).symm (add_zero _).symm)
          (Prod.ext (add_zero _).symm ?_)
        change -(x.1.2 + y.1.2) = -x.1.2 + -y.1.2
        abel
      map_smul' := fun r x => by
        refine Prod.ext (Prod.ext (smul_zero _).symm (smul_zero _).symm)
          (Prod.ext (smul_zero _).symm ?_)
        change -(r • x.1.2) = r • -x.1.2
        rw [smul_neg] }
  map_grading n x hx := by
    obtain ⟨hx₁, -⟩ := (coneGrading_mem n x).mp hx
    obtain ⟨-, hk⟩ := (coneGrading_mem n x.1).mp hx₁
    refine (coneGrading_mem (n - 1) _).mpr ⟨?_, ?_⟩
    · exact (coneGrading_mem (n - 1) _).mpr
        ⟨(M.grading (n - 1)).zero_mem, (K.grading (n - 1 + 1)).zero_mem⟩
    · refine (coneGrading_mem (n - 1 + 1) _).mpr ⟨(L.grading (n - 1 + 1)).zero_mem, ?_⟩
      rw [show n - 1 + 1 + 1 = n + 1 by ring]
      exact (K.grading (n + 1)).neg_mem hk
  homotopy_eq x := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change x.1.1 - x.1.1 = M.d 0 + β.toFun (α.toFun 0) + (β.toFun 0 + 0) + 0
      simp
    · change (0 : K.M) - x.1.2 = -K.d 0 + -x.1.2 + 0
      simp
    · change α.toFun x.1.2 + x.2.1 - x.2.1 = -(L.d 0 + α.toFun (-x.1.2)) + 0
      simp
    · change (0 : K.M) - x.2.2 = - -K.d (-x.1.2) + -(-K.d x.1.2 + x.2.2)
      simp

/-- The cancellation map is an isomorphism of the homotopy category: the cone of the comparison
map `octaMap₁` is the cone of `β`. -/
noncomputable def coneCancelIso :
    (toHomotopyCategory A).obj (coneObject (octaMap₁ α β)) ≅
      (toHomotopyCategory A).obj (coneObject β) :=
  isoOfHomotopyInverse (coneCancel α β) (coneSection α β) (coneCancelHomotopy α β)
    (Homotopy.ofEq (coneSection_coneCancel α β))

/-- The forward map of `coneCancelIso` is the class of the cancellation map `coneCancel`. -/
@[simp] theorem coneCancelIso_hom :
    (coneCancelIso α β).hom = (toHomotopyCategory A).map (coneCancel α β) := rfl

/-- The inclusion into the cone of the first comparison map, followed by cancellation, is the
second comparison map, on the nose. -/
theorem coneIncl_coneCancel :
    coneIncl (octaMap₁ α β) ≫ coneCancel α β = octaMap₃ α β := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  refine Prod.ext (add_zero _).symm ?_
  show α.toFun x.2 + 0 = α.toFun x.2
  rw [add_zero]

/-- The boundary homotopy: on `(M ⊕ K) ⊕ (L ⊕ K)` the map `((m, k), (l, j)) ↦ (0, k)` is a
homotopy from the projection of the cone of `octaMap₁` to the composite of cancellation, the
projection of `C(β)`, and the shifted inclusion of `C(α)`. -/
noncomputable def coneBoundaryHomotopy :
    Homotopy (coneProj (octaMap₁ α β))
      (coneCancel α β ≫ coneProj β ≫ shiftMap (coneIncl α) 1) where
  toLinearMap :=
    { toFun := fun x => ((0 : L.M), x.1.2)
      map_add' := fun x y => Prod.ext (add_zero _).symm rfl
      map_smul' := fun r x => Prod.ext (smul_zero r).symm rfl }
  map_grading n x hx := by
    obtain ⟨hx₁, -⟩ := (coneGrading_mem n x).mp hx
    obtain ⟨-, hk⟩ := (coneGrading_mem n x.1).mp hx₁
    change ((0 : L.M), x.1.2) ∈ (shift (coneObject α) 1).grading (n - 1)
    rw [shift_grading]
    refine (coneGrading_mem (n - 1 + 1) _).mpr ⟨(L.grading (n - 1 + 1)).zero_mem, ?_⟩
    rw [show n - 1 + 1 + 1 = n + 1 by ring]
    exact hk
  homotopy_eq x := by
    rw [shift_one_d_apply]
    refine Prod.ext ?_ ?_
    · change x.2.1 - (α.toFun x.1.2 + x.2.1) = -(L.d 0 + α.toFun x.1.2) + 0
      rw [map_zero]
      abel
    · change x.2.2 - 0 = - -K.d x.1.2 + (-K.d x.1.2 + x.2.2)
      abel

/-- The fourth triangle of the octahedron, `C(α) ⟶ C(α ≫ β) ⟶ C(β) ⟶ C(α)[1]`, is
distinguished: it is isomorphic to the cone triangle of the first comparison map, by cancellation
of the cone. -/
theorem octaTriangle_mem :
    Triangle.mk ((toHomotopyCategory A).map (octaMap₁ α β))
        ((toHomotopyCategory A).map (octaMap₃ α β))
        (((toHomotopyCategory A).map (coneProj β) ≫ (quotientShiftIso L 1).hom) ≫
          ((toHomotopyCategory A).map (coneIncl α))⟦(1 : ℤ)⟧') ∈
      distTriang (HomotopyCategory.{u, v, w} A) := by
  have hb : (toHomotopyCategory A).map (coneProj (octaMap₁ α β)) =
      (toHomotopyCategory A).map
        (coneCancel α β ≫ coneProj β ≫ shiftMap (coneIncl α) 1) :=
    (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mpr
      ⟨coneBoundaryHomotopy α β⟩
  have hnat := quotient_map_shiftMap_comp_quotientShiftIso (coneIncl α) (1 : ℤ)
  refine isomorphic_distinguished _ (coneTriangle_mk_mem (octaMap₁ α β)) _ ?_
  refine Iso.symm ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneCancelIso α β) ?_ ?_ ?_
  · simp
  · simp [← Functor.map_comp, coneIncl_coneCancel]
  · simp [hb, hnat]

/-- The cone triangle of a composite, with its first morphism written as the composite of the two
classes, is distinguished. -/
theorem octaCompTriangle_mem :
    Triangle.mk ((toHomotopyCategory A).map α ≫ (toHomotopyCategory A).map β)
        ((toHomotopyCategory A).map (coneIncl (α ≫ β)))
        ((toHomotopyCategory A).map (coneProj (α ≫ β)) ≫ (quotientShiftIso K 1).hom) ∈
      distTriang (HomotopyCategory.{u, v, w} A) := by
  rw [← Functor.map_comp]
  exact coneTriangle_mk_mem (α ≫ β)

/-- **The octahedron.** The cone triangles on `α`, on `α ≫ β` and on `β` form an octahedron: the
two comparison maps of cones satisfy the four commutations of (TR 4), and the triangle
`C(α) ⟶ C(α ≫ β) ⟶ C(β) ⟶ C(α)[1]` that they form is distinguished. -/
noncomputable def coneOctahedron :
    Octahedron
      (rfl : (toHomotopyCategory A).map α ≫ (toHomotopyCategory A).map β =
        (toHomotopyCategory A).map α ≫ (toHomotopyCategory A).map β)
      (coneTriangle_mk_mem α) (coneTriangle_mk_mem β) (octaCompTriangle_mem α β) where
  m₁ := (toHomotopyCategory A).map (octaMap₁ α β)
  m₃ := (toHomotopyCategory A).map (octaMap₃ α β)
  comm₁ := by
    change (toHomotopyCategory A).map (coneIncl α) ≫
        (toHomotopyCategory A).map (octaMap₁ α β) =
      (toHomotopyCategory A).map β ≫ (toHomotopyCategory A).map (coneIncl (α ≫ β))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (toHomotopyCategory A).map (coneIncl_octaMap₁ α β)
  comm₂ := by
    change (toHomotopyCategory A).map (octaMap₁ α β) ≫
        ((toHomotopyCategory A).map (coneProj (α ≫ β)) ≫ (quotientShiftIso K 1).hom) =
      (toHomotopyCategory A).map (coneProj α) ≫ (quotientShiftIso K 1).hom
    calc (toHomotopyCategory A).map (octaMap₁ α β) ≫
          ((toHomotopyCategory A).map (coneProj (α ≫ β)) ≫ (quotientShiftIso K 1).hom)
        = (toHomotopyCategory A).map (octaMap₁ α β ≫ coneProj (α ≫ β)) ≫
            (quotientShiftIso K 1).hom := by
          rw [Functor.map_comp, Category.assoc]
      _ = (toHomotopyCategory A).map (coneProj α ≫ shiftMap (𝟙 K) 1) ≫
            (quotientShiftIso K 1).hom := by
          rw [octaMap₁_coneProj]
      _ = (toHomotopyCategory A).map (coneProj α) ≫ (quotientShiftIso K 1).hom := by
          rw [shiftMap_id, Category.comp_id]
  comm₃ := by
    rw [← Functor.map_comp, coneIncl_octaMap₃, Category.id_comp]
  comm₄ := (coneTriangleMapOfHomotopy (octaHomotopy₃ α β)).comm₃
  mem := octaTriangle_mem α β

end ConeOctahedron

/-- **Tag 09KI.** Two composable admissible monomorphisms of differential graded modules have
distinguished triangles completing them to an octahedron: there are distinguished triangles
`(K, L, Q₁)`, `(K, M, Q₂)` and `(L, M, Q₃)` on `α`, on `β ∘ α` and on `β`, together with maps
`a : Q₁ ⟶ Q₂` and `b : Q₂ ⟶ Q₃` satisfying the four commutations of (TR 4), for which the
triangle `(Q₁, Q₂, Q₃)` is itself distinguished. -/
@[stacks 09KI]
theorem octahedron_of_admissible_monos (α : K ⟶ L) (β : L ⟶ M)
    (_hα : IsAdmissibleMono α) (_hβ : IsAdmissibleMono β) :
    letI q := toHomotopyCategory A
    ∃ (Q₁ Q₂ Q₃ : HomotopyCategory.{u, v, w} A)
      (p₁ : q.obj L ⟶ Q₁) (d₁ : Q₁ ⟶ (q.obj K)⟦(1 : ℤ)⟧)
      (p₂ : q.obj M ⟶ Q₂) (d₂ : Q₂ ⟶ (q.obj K)⟦(1 : ℤ)⟧)
      (p₃ : q.obj M ⟶ Q₃) (d₃ : Q₃ ⟶ (q.obj L)⟦(1 : ℤ)⟧)
      (a : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃),
      Triangle.mk (q.map α) p₁ d₁ ∈ distTriang (HomotopyCategory.{u, v, w} A) ∧
      Triangle.mk (q.map α ≫ q.map β) p₂ d₂ ∈ distTriang (HomotopyCategory.{u, v, w} A) ∧
      Triangle.mk (q.map β) p₃ d₃ ∈ distTriang (HomotopyCategory.{u, v, w} A) ∧
      (p₁ ≫ a = q.map β ≫ p₂) ∧
      (a ≫ d₂ = d₁) ∧
      (p₂ ≫ b = p₃) ∧
      (d₂ ≫ (q.map α)⟦(1 : ℤ)⟧' = b ≫ d₃) ∧
      Triangle.mk a b (d₃ ≫ p₁⟦(1 : ℤ)⟧') ∈ distTriang (HomotopyCategory.{u, v, w} A) := by
  refine ⟨_, _, _, _, _, _, _, _, _,
    (coneOctahedron α β).m₁, (coneOctahedron α β).m₃,
    coneTriangle_mk_mem α, octaCompTriangle_mem α β, coneTriangle_mk_mem β,
    (coneOctahedron α β).comm₁, (coneOctahedron α β).comm₂, (coneOctahedron α β).comm₃,
    (coneOctahedron α β).comm₄, (coneOctahedron α β).mem⟩

/-- **The homotopy category of right differential graded `A`-modules is triangulated.** Every
object is the class of a differential graded module and every morphism the class of a
homomorphism, so every composable pair of morphisms is isomorphic to one of the form
`(α, β)` for which `DifferentialGradedModule.coneOctahedron` supplies the octahedron. -/
instance instIsTriangulatedHomotopyCategory :
    IsTriangulated (HomotopyCategory.{u, v, w} A) := by
  apply IsTriangulated.mk'
  intro X₁ X₂ X₃ u₁₂ u₂₃
  obtain ⟨α, rfl⟩ := (toHomotopyCategory A).map_surjective u₁₂
  obtain ⟨β, rfl⟩ := (toHomotopyCategory A).map_surjective u₂₃
  exact ⟨_, _, _, _, _, _, _, _, Iso.refl _, Iso.refl _, Iso.refl _,
    by simp, by simp,
    _, _, coneTriangle_mk_mem α, _, _, coneTriangle_mk_mem β,
    _, _, octaCompTriangle_mem α β, ⟨coneOctahedron α β⟩⟩

end DifferentialGradedModule

end
