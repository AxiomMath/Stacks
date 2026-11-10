module

public import StacksFrontier.Algebra.DGA.ConeTriangle

/-!
# Morphisms out of a mapping cone

A homomorphism out of the cone of `f : K ⟶ L` is the same thing as a homomorphism `g : L ⟶ M`
together with a null-homotopy of `f ≫ g`: the cone has underlying module `L × K`, so a map out
of it is a pair of a map on `L` and a degree `-1` map on `K`, and compatibility with the
differentials says exactly that the second is a homotopy from `f ≫ g` to zero.  Applying this
to a square that commutes up to homotopy produces a homomorphism of cones, and hence a morphism
of cone triangles in the homotopy category completing the square.

## Main definitions

* `DifferentialGradedModule.coneDesc` is the homomorphism out of a cone determined by a
  homomorphism on the target and a null-homotopy.
* `DifferentialGradedModule.coneMapOfHomotopy` is the homomorphism of cones determined by a
  square commuting up to homotopy, and
  `DifferentialGradedModule.coneTriangleMapOfHomotopy` is the induced morphism of cone triangles.

## Main results

* `DifferentialGradedModule.complete_distinguishedConeTriangles_morphism`: a square between the
  first morphisms of two triangles in `DifferentialGradedModule.distinguishedConeTriangles`
  extends to a morphism of triangles.

## Implementation notes

The underlying map of a homotopy is linear over the opposite algebra, while the underlying map
of a homomorphism of differential graded modules is linear over the base ring; the two are
related by `LinearMap.restrictScalars`, which applies because the right action of the algebra
is compatible with the action of the base ring.

The two squares of the morphism of cones hold on the nose, before passing to the homotopy
category: a homomorphism of cones built from a homotopy commutative square agrees strictly with
the inclusion on the target and strictly with the projection to the shifted source.  Only the
square of first morphisms needs the homotopy, which is why the homotopy enters the construction
of the map on cones and not the verification of the squares.

The third square compares the shift of a morphism of the homotopy category with the class of a
shifted homomorphism, which is the naturality of
`DifferentialGradedModule.quotientShiftIso`, the isomorphism from which
`DifferentialGradedModule.coneTriangle` is built.

## References

* [Stacks Project, Tag 09KA](https://stacks.math.columbia.edu/tag/09KA)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

section Desc

variable {K L M : DifferentialGradedModule.{u, v, w} A}

/-- The homomorphism `C(f) ⟶ M` out of the cone of `f : K ⟶ L` determined by a homomorphism
`g : L ⟶ M` and a homotopy from `f ≫ g` to zero: on the underlying module `L × K` it is
`(l, k) ↦ g l + h k`, where `h` is the underlying map of the homotopy. -/
def coneDesc (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) : coneObject f ⟶ M where
  toFun := LinearMap.coprod g.toFun (H.toLinearMap.restrictScalars R)
  map_smul x a := by
    change g.toFun (MulOpposite.op a • x.1) + H.toLinearMap (MulOpposite.op a • x.2) =
      MulOpposite.op a • (g.toFun x.1 + H.toLinearMap x.2)
    rw [g.map_smul, H.toLinearMap.map_smul, smul_add]
  map_grading n x hx := by
    obtain ⟨hx₁, hx₂⟩ := (coneGrading_mem n x).mp hx
    have hH := H.map_grading (n + 1) x.2 hx₂
    rw [show n + 1 - 1 = n by ring] at hH
    exact (M.grading n).add_mem (g.map_grading n x.1 hx₁) hH
  map_d := by
    refine LinearMap.ext fun x => ?_
    have hg := LinearMap.congr_fun g.map_d x.1
    have hH := H.homotopy_eq x.2
    rw [Hom.comp_toFun_apply, Hom.hom_zero_toFun] at hH
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, sub_zero] at hg hH
    change g.toFun (L.d x.1 + f.toFun x.2) + H.toLinearMap (-K.d x.2) =
      M.d (g.toFun x.1 + H.toLinearMap x.2)
    rw [map_add, map_add, map_neg, hg, hH]
    abel

/-- On the underlying module `L × K`, the map out of the cone is `(l, k) ↦ g l + h k`. -/
@[simp] theorem coneDesc_toFun_apply (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0)
    (x : L.M × K.M) : (coneDesc f g H).toFun x = g.toFun x.1 + H.toLinearMap x.2 := rfl

/-- The inclusion of the target into the cone, followed by a map out of the cone, is the map on
the target it was built from. -/
@[simp] theorem coneIncl_coneDesc (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    coneIncl f ≫ coneDesc f g H = g := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  change g.toFun x + H.toLinearMap 0 = g.toFun x
  rw [map_zero, add_zero]

end Desc

section MapOfHomotopy

variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v, w} A}
  {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}

/-- The homomorphism of cones `C(f₁) ⟶ C(f₂)` induced by a square commuting up to homotopy: on
the underlying modules it is `(l, k) ↦ (b l + h k, a k)`, where `h` is the underlying map of the
homotopy from `f₁ ≫ b` to `a ≫ f₂`. -/
noncomputable def coneMapOfHomotopy (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    coneObject f₁ ⟶ coneObject f₂ where
  toFun := LinearMap.prod (LinearMap.coprod b.toFun (H.toLinearMap.restrictScalars R))
    (a.toFun.comp (LinearMap.snd R L₁.M K₁.M))
  map_smul x c := by
    refine Prod.ext ?_ ?_
    · change b.toFun (MulOpposite.op c • x.1) + H.toLinearMap (MulOpposite.op c • x.2) =
        MulOpposite.op c • (b.toFun x.1 + H.toLinearMap x.2)
      rw [b.map_smul, H.toLinearMap.map_smul, smul_add]
    · exact a.map_smul x.2 c
  map_grading n x hx := by
    obtain ⟨hx₁, hx₂⟩ := (coneGrading_mem n x).mp hx
    have hH := H.map_grading (n + 1) x.2 hx₂
    rw [show n + 1 - 1 = n by ring] at hH
    exact (coneGrading_mem n _).mpr
      ⟨(L₂.grading n).add_mem (b.map_grading n x.1 hx₁) hH, a.map_grading (n + 1) x.2 hx₂⟩
  map_d := by
    refine LinearMap.ext fun x => ?_
    have hb := LinearMap.congr_fun b.map_d x.1
    have ha := LinearMap.congr_fun a.map_d x.2
    have hH := H.homotopy_eq x.2
    rw [Hom.comp_toFun_apply, Hom.comp_toFun_apply] at hH
    simp only [LinearMap.comp_apply] at hb ha
    refine Prod.ext ?_ ?_
    · change b.toFun (L₁.d x.1 + f₁.toFun x.2) + H.toLinearMap (-K₁.d x.2) =
        L₂.d (b.toFun x.1 + H.toLinearMap x.2) + f₂.toFun (a.toFun x.2)
      have key : b.toFun (f₁.toFun x.2) =
          L₂.d (H.toLinearMap x.2) + H.toLinearMap (K₁.d x.2) + f₂.toFun (a.toFun x.2) := by
        rw [← hH]; abel
      rw [map_add, map_add, map_neg, hb, key]
      abel
    · change a.toFun (-K₁.d x.2) = -K₂.d (a.toFun x.2)
      rw [map_neg, ha]

/-- On the underlying modules, the homomorphism of cones is `(l, k) ↦ (b l + h k, a k)`. -/
@[simp] theorem coneMapOfHomotopy_toFun_apply (H : Homotopy (f₁ ≫ b) (a ≫ f₂))
    (x : L₁.M × K₁.M) :
    (coneMapOfHomotopy H).toFun x = (b.toFun x.1 + H.toLinearMap x.2, a.toFun x.2) := rfl

/-- The homomorphism of cones induced by a homotopy commutative square agrees with the given
homomorphism on the targets, through the canonical inclusions. -/
theorem coneIncl_coneMapOfHomotopy (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    coneIncl f₁ ≫ coneMapOfHomotopy H = b ≫ coneIncl f₂ := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  refine Prod.ext ?_ ?_
  · change b.toFun x + H.toLinearMap 0 = b.toFun x
    rw [map_zero, add_zero]
  · change a.toFun 0 = 0
    rw [map_zero]

/-- The homomorphism of cones induced by a homotopy commutative square agrees with the shift of
the given homomorphism on the sources, through the canonical projections. -/
theorem coneMapOfHomotopy_coneProj (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    coneMapOfHomotopy H ≫ coneProj f₂ = coneProj f₁ ≫ shiftMap a 1 := by
  apply Hom.ext; rfl

/-- The morphism of cone triangles induced by a square commuting up to homotopy. -/
@[simps]
noncomputable def coneTriangleMapOfHomotopy (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    coneTriangle f₁ ⟶ coneTriangle f₂ where
  hom₁ := (toHomotopyCategory A).map a
  hom₂ := (toHomotopyCategory A).map b
  hom₃ := (toHomotopyCategory A).map (coneMapOfHomotopy H)
  comm₁ := by
    change (toHomotopyCategory A).map f₁ ≫ (toHomotopyCategory A).map b =
      (toHomotopyCategory A).map a ≫ (toHomotopyCategory A).map f₂
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mpr ⟨H⟩
  comm₂ := by
    change (toHomotopyCategory A).map (coneIncl f₁) ≫
        (toHomotopyCategory A).map (coneMapOfHomotopy H) =
      (toHomotopyCategory A).map b ≫ (toHomotopyCategory A).map (coneIncl f₂)
    rw [← Functor.map_comp, ← Functor.map_comp, coneIncl_coneMapOfHomotopy]
  comm₃ := by
    change ((toHomotopyCategory A).map (coneProj f₁) ≫ (quotientShiftIso K₁ 1).hom) ≫
        ((toHomotopyCategory A).map a)⟦(1 : ℤ)⟧' =
      (toHomotopyCategory A).map (coneMapOfHomotopy H) ≫
        (toHomotopyCategory A).map (coneProj f₂) ≫ (quotientShiftIso K₂ 1).hom
    simp only [Category.assoc, ← quotient_map_shiftMap_comp_quotientShiftIso,
      ← Functor.map_comp_assoc, coneMapOfHomotopy_coneProj]

end MapOfHomotopy

/-- A square between the first morphisms of two cone triangles extends to a morphism of cone
triangles prescribed on the first two objects. -/
theorem exists_coneTriangleMap_of_fac {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v, w} A}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (a : (coneTriangle f₁).obj₁ ⟶ (coneTriangle f₂).obj₁)
    (b : (coneTriangle f₁).obj₂ ⟶ (coneTriangle f₂).obj₂)
    (fac : (coneTriangle f₁).mor₁ ≫ b = a ≫ (coneTriangle f₂).mor₁) :
    ∃ γ : coneTriangle f₁ ⟶ coneTriangle f₂, γ.hom₁ = a ∧ γ.hom₂ = b := by
  obtain ⟨a₀, rfl⟩ := (toHomotopyCategory A).map_surjective a
  obtain ⟨b₀, rfl⟩ := (toHomotopyCategory A).map_surjective b
  have hfac : (toHomotopyCategory A).map (f₁ ≫ b₀) = (toHomotopyCategory A).map (a₀ ≫ f₂) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact fac
  obtain ⟨H⟩ := (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mp hfac
  exact ⟨coneTriangleMapOfHomotopy H, rfl, rfl⟩

/-- A square between the first morphisms of two triangles extends to a morphism of triangles as
soon as it does for two triangles isomorphic to them.  Only the isomorphisms and the morphism of
triangles produced for the second pair are used, so the statement is about arbitrary
triangles. -/
theorem complete_morphism_of_triangleIso
    {T₁ T₂ T₁' T₂' : Triangle (HomotopyCategory.{u, v, w} A)}
    (e₁ : T₁ ≅ T₁') (e₂ : T₂ ≅ T₂')
    (hext : ∀ (a' : T₁'.obj₁ ⟶ T₂'.obj₁) (b' : T₁'.obj₂ ⟶ T₂'.obj₂),
      T₁'.mor₁ ≫ b' = a' ≫ T₂'.mor₁ →
      ∃ γ : T₁' ⟶ T₂', γ.hom₁ = a' ∧ γ.hom₂ = b')
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨γ, hγ₁, hγ₂⟩ := hext (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
    (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by
      simp only [reassoc_of% e₁.inv.comm₁, reassoc_of% fac, e₂.hom.comm₁, Category.assoc])
  refine ⟨(e₁.hom ≫ γ ≫ e₂.inv).hom₃, ?_, ?_⟩
  · simp [hγ₂]
  · simpa [hγ₁] using (e₁.hom ≫ γ ≫ e₂.inv).comm₃

/-- A square between the first morphisms of two triangles isomorphic to cone triangles extends
to a morphism of triangles.  This is the completion axiom of a pretriangulated category for
`DifferentialGradedModule.distinguishedConeTriangles`. -/
theorem complete_distinguishedConeTriangles_morphism
    (T₁ T₂ : Triangle (HomotopyCategory.{u, v, w} A))
    (hT₁ : T₁ ∈ distinguishedConeTriangles.{u, v, w} (A := A))
    (hT₂ : T₂ ∈ distinguishedConeTriangles.{u, v, w} (A := A))
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨K₁, L₁, f₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨K₂, L₂, f₂, ⟨e₂⟩⟩ := hT₂
  exact complete_morphism_of_triangleIso e₁ e₂
    (exists_coneTriangleMap_of_fac f₁ f₂) a b fac

end DifferentialGradedModule

end
