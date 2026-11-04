module

public import StacksFrontier.Homology.DerivedCategory.ShiftSummandApproximation

/-!
# A retract splits off its cone, and the cone step of [Stacks, Tag 09IN]

Two steps are taken here, both free of geometry.

The first is additive-triangulated: in a pretriangulated category, a morphism `i : P ⟶ R`
admitting a retraction `r` has `R ≅ P ⊞ Z` for `Z` the cone of `i`, with `i` becoming the
biproduct injection. The third morphism of a distinguished triangle on a split monomorphism
vanishes, so the triangle is isomorphic to the split triangle of a biproduct, and the comparison
is an isomorphism by two-out-of-three.

The second runs in the derived category of an abelian category, and is the step
[Stacks, Tag 09IN] performs after applying [Stacks, Tag 09IM] a second time. Over the open `U`
the second application produces a map `φ : Q ⊞ Q' ⟶ P ⊞ Q` whose restriction to the first
summand is, by the compatibility clause of 09IM, the inclusion of `Q`; coning `φ` off then
leaves an object whose cohomology agrees, along the map `biprod.inl ≫ v` out of `P`, with that of
`P` in every degree above a bound for the cohomology of `Q'` alone. That is
`CategoryTheory.Limits.Biprod.shear_hom_comp` and
`CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp` fed into
`DerivedCategory.approximatesFrom_mor₂_iff`, assembled into one statement so that a consumer
supplies only `φ`, its triangle and the bound.

## Main results

* `CategoryTheory.Pretriangulated.mor₃_eq_zero_of_retraction`: the third morphism of a
  distinguished triangle whose first morphism has a retraction is zero.
* `CategoryTheory.Pretriangulated.isoBiprodOfRetraction` and
  `CategoryTheory.Pretriangulated.isoBiprodOfRetraction_hom_comp`: the resulting splitting
  `R ≅ P ⊞ Z`, and the fact that it carries `i` to `CategoryTheory.Limits.biprod.inl`. This is
  what turns the "direct summand" clause of [Stacks, Tag 09IM], which is a retract, into the
  biproduct that `DerivedCategory.approximatesFrom_biprod_inl_iff` is stated at.
* `DerivedCategory.approximatesFrom_comp_iso`: approximation from a degree survives composition
  with an isomorphism of the target.
* `DerivedCategory.approximatesFrom_cone_of_biprod_inl_comp`: **the cone step of
  [Stacks, Tag 09IN]**. For `φ : Q ⊞ Q' ⟶ P ⊞ Q` which is the inclusion of `Q` on the first
  summand, and a cone `v : P ⊞ Q ⟶ Z` of `φ`, a bound `m` above which `Q'` has no cohomology
  makes `CategoryTheory.Limits.biprod.inl ≫ v : P ⟶ Z` an isomorphism on cohomology in every
  degree `> m`.

## Implementation notes

`DerivedCategory.approximatesFrom_cone_of_biprod_inl_comp` names the approximating map, namely
`CategoryTheory.Limits.biprod.inl ≫ v`, rather than asserting that one exists. That is what
[Stacks, Tag 09IN] needs, its conclusion also naming the map to the ambient object; it is
available because `CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp`
carries the compatibility of its isomorphism `Z ≅ Z'` with the two maps into the two cones, so
the map through `Z'` supplied by `DerivedCategory.approximatesFrom_mor₂_iff` transports back to
`biprod.inl ≫ v` and not merely to some map approximating `Z`.

The splitting is stated for a bare `Pretriangulated` category with binary biproducts: no
abelian, no triangulated, no derived category. The retraction is taken as a morphism with
`i ≫ r = 𝟙 P` rather than as `CategoryTheory.IsSplitMono` or `CategoryTheory.Retract`, because
that is the form [Stacks, Tag 09IM]'s conclusion supplies.

## References

* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A distinguished triangle on a split monomorphism has vanishing third morphism.** If
`i ≫ r = 𝟙 P` then `w ≫ i⟦1⟧ = 0` forces `w = 0`, the shift of `i ≫ r` being the identity. -/
theorem mor₃_eq_zero_of_retraction {P R Z : D} {i : P ⟶ R} (r : R ⟶ P) (hir : i ≫ r = 𝟙 P)
    {v : R ⟶ Z} {w : Z ⟶ P⟦(1 : ℤ)⟧} (hT : Triangle.mk i v w ∈ distTriang D) :
    w = 0 := by
  have h₃₁ : w ≫ (shiftFunctor D (1 : ℤ)).map i = 0 := comp_distTriang_mor_zero₃₁ _ hT
  simpa [← Functor.map_comp, hir] using h₃₁ =≫ (shiftFunctor D (1 : ℤ)).map r

variable [HasBinaryBiproducts D]

/-- The comparison `⟨r, v⟩ : R ⟶ P ⊞ Z` carries the split monomorphism to the biproduct
injection. -/
private theorem comp_biprod_lift_of_retraction {P R Z : D} {i : P ⟶ R} (r : R ⟶ P)
    (hir : i ≫ r = 𝟙 P) {v : R ⟶ Z} {w : Z ⟶ P⟦(1 : ℤ)⟧}
    (hT : Triangle.mk i v w ∈ distTriang D) :
    i ≫ biprod.lift r v = (biprod.inl : P ⟶ P ⊞ Z) := by
  have hiv : i ≫ v = 0 := comp_distTriang_mor_zero₁₂ _ hT
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [hir, hiv]

/-- **A retract splits off its cone.** If `i : P ⟶ R` has a retraction `r` and `Z` is the cone
of `i`, then `⟨r, v⟩ : R ⟶ P ⊞ Z` is an isomorphism: the triangle on `i` is a morphism of
distinguished triangles to the split triangle of `P ⊞ Z` which is the identity on the outer two
vertices, so it is an isomorphism on the middle one.

The compatibility `i ≫ ⟨r, v⟩ = biprod.inl` is
`CategoryTheory.Pretriangulated.isoBiprodOfRetraction_hom_comp`. -/
theorem isIso_biprodLift_of_retraction {P R Z : D} {i : P ⟶ R} (r : R ⟶ P) (hir : i ≫ r = 𝟙 P)
    {v : R ⟶ Z} {w : Z ⟶ P⟦(1 : ℤ)⟧} (hT : Triangle.mk i v w ∈ distTriang D) :
    IsIso (biprod.lift r v) := by
  let φ : Triangle.mk i v w ⟶ binaryBiproductTriangle P Z :=
    { hom₁ := 𝟙 P, hom₂ := biprod.lift r v, hom₃ := 𝟙 Z
      comm₁ := (comp_biprod_lift_of_retraction r hir hT).trans (id_comp _).symm
      comm₂ := by simp [binaryBiproductTriangle]
      comm₃ := by simp [binaryBiproductTriangle, mor₃_eq_zero_of_retraction r hir hT] }
  exact isIso₂_of_isIso₁₃ φ hT (binaryBiproductTriangle_distinguished P Z) (IsIso.id P)
    (IsIso.id Z)

/-- **The splitting of a retract**, as an isomorphism `R ≅ P ⊞ Z` with `Z` the cone of the split
monomorphism. -/
def isoBiprodOfRetraction {P R Z : D} {i : P ⟶ R} (r : R ⟶ P) (hir : i ≫ r = 𝟙 P)
    {v : R ⟶ Z} {w : Z ⟶ P⟦(1 : ℤ)⟧} (hT : Triangle.mk i v w ∈ distTriang D) :
    R ≅ P ⊞ Z :=
  haveI := isIso_biprodLift_of_retraction r hir hT
  asIso (biprod.lift r v)

/-- The splitting of a retract carries the split monomorphism to the biproduct injection, so the
cohomological statements about `CategoryTheory.Limits.biprod.inl` apply to it. -/
theorem isoBiprodOfRetraction_hom_comp {P R Z : D} {i : P ⟶ R} (r : R ⟶ P) (hir : i ≫ r = 𝟙 P)
    {v : R ⟶ Z} {w : Z ⟶ P⟦(1 : ℤ)⟧} (hT : Triangle.mk i v w ∈ distTriang D) :
    i ≫ (isoBiprodOfRetraction r hir hT).hom = (biprod.inl : P ⟶ P ⊞ Z) := by
  exact comp_biprod_lift_of_retraction r hir hT

end CategoryTheory.Pretriangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **Approximation from a degree survives an isomorphism of the target.** Cohomology is
functorial, so composing with an isomorphism keeps every `H^i` of the composite isomorphic,
respectively epimorphic, where that of the original is. -/
theorem approximatesFrom_comp_iso {P E E' : DerivedCategory C} {α : P ⟶ E} {m : ℤ}
    (e : E ≅ E') (h : ApproximatesFrom α m) : ApproximatesFrom (α ≫ e.hom) m := by
  obtain ⟨hiso, hepi⟩ := h
  refine ⟨fun i hi => ?_, ?_⟩
  · have := hiso i hi
    rw [(homologyFunctor C i).map_comp]
    infer_instance
  · rw [(homologyFunctor C m).map_comp]
    infer_instance

/-- **The cone step of [Stacks, Tag 09IN].** Let `φ : Q ⊞ Q' ⟶ P ⊞ Q` restrict on the first
summand to the inclusion of `Q`, and let `v : P ⊞ Q ⟶ Z` be a cone of `φ`. If the cohomology of
`Q'` vanishes in every degree `> m`, then `biprod.inl ≫ v : P ⟶ Z`, the restriction of that cone
map to the `P` summand, is an isomorphism on cohomology in every degree `> m` and an epimorphism
in degree `m`.

This is the configuration the remark reaches after applying [Stacks, Tag 09IM] a second time, to
the inclusion of the complement `Q` into `R|_U ≅ P ⊞ Q`, and coning off the resulting morphism:
by `CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp` the cone of `φ` is
the cone of the single component `c : Q' ⟶ P` of `φ`, and
`DerivedCategory.approximatesFrom_mor₂_iff` converts a cohomological bound on `Q'` into the
degree range in which the map `P ⟶ cone c` is invertible. The complement `Q` contributes
nothing: the shear of `CategoryTheory.Limits.Biprod.shear_hom_comp` removes it. -/
theorem approximatesFrom_cone_of_biprod_inl_comp [IsTriangulated (DerivedCategory C)]
    {P Q Q' Z : DerivedCategory C} (φ : Q ⊞ Q' ⟶ P ⊞ Q)
    (hφ : (biprod.inl : Q ⟶ Q ⊞ Q') ≫ φ = (biprod.inr : Q ⟶ P ⊞ Q))
    {v : P ⊞ Q ⟶ Z} {w : Z ⟶ (Q ⊞ Q')⟦(1 : ℤ)⟧}
    (hT : Triangle.mk φ v w ∈ distTriang (DerivedCategory C))
    (m : ℤ) (hQ' : ∀ i : ℤ, m < i → IsZero ((homologyFunctor C i).obj Q')) :
    ApproximatesFrom ((biprod.inl : P ⟶ P ⊞ Q) ≫ v) m := by
  obtain ⟨Z', v', w', hT'⟩ := Pretriangulated.distinguished_cocone_triangle
    ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.fst : P ⊞ Q ⟶ P))
  obtain ⟨e, he⟩ := CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp
    φ hφ hT hT'
  have h := approximatesFrom_comp_iso e.symm
    ((approximatesFrom_mor₂_iff (Triangle.mk _ v' w') hT' m).2 hQ')
  rw [Iso.symm_hom, ← he] at h
  simpa using h

end DerivedCategory

end
