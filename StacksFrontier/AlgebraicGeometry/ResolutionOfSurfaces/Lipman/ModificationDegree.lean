module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.NormalizationInFractionField

/-!
# Degrees of function field extensions along squares of modifications

The inductive step of the proof of [Stacks, Tag 0BGN] compares the degree of the extension of
fraction fields of a finite map of rings `B → A` with the degree of the extension of function
fields of a finite morphism `π : X ⟶ Y` lying over it through modifications `X ⟶ Spec A` and
`Y ⟶ Spec B`. Modifications induce isomorphisms of function fields, so the two degrees agree.

## Main results

* `AlgebraicGeometry.finrank_eq_of_comp_eq_of_bijective`: in a commutative square of field
  extensions whose two vertical maps are isomorphisms, the horizontal degrees agree.
* `AlgebraicGeometry.finrank_functionField_eq_of_square`: the scheme form, for a commutative
  square of dominant morphisms of integral schemes with birational vertical sides.
* `AlgebraicGeometry.finrank_sections_eq_finrank_functionField`: for a dominant morphism of
  integral schemes, the degree over the sections on a nonempty affine open of the sections over
  an affine preimage is the degree of the function field extension.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **In a commutative square of field homomorphisms whose vertical maps are isomorphisms, the
horizontal degrees agree.** Here `a : K₁ ⟶ K₂` and `d : K₃ ⟶ K₄` are bijective and
`c ∘ a = d ∘ b`; the degree of `K₄` over `K₂` through `c` is that of `K₃` over `K₁` through
`b`. -/
theorem finrank_eq_of_comp_eq_of_bijective {K₁ K₂ K₃ K₄ : Type u} [Field K₁] [Field K₂]
    [Field K₃] [Field K₄] (a : K₁ →+* K₂) (b : K₁ →+* K₃) (c : K₂ →+* K₄) (d : K₃ →+* K₄)
    (ha : Function.Bijective a) (hd : Function.Bijective d) (h : c.comp a = d.comp b) :
    letI := c.toAlgebra; letI := b.toAlgebra; Module.finrank K₂ K₄ = Module.finrank K₁ K₃ := by
  let := c.toAlgebra
  let := b.toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective a ha)
    (RingEquiv.ofBijective d hd) h).symm

/-- **The degree of a dominant morphism of integral schemes is invariant under replacing source
and target by birational models.** In a commutative square `π ≫ g = f ≫ q` of dominant
morphisms of integral schemes with `f` and `g` birational, the extension of function fields of
`π` has the degree of that of `q`. -/
theorem finrank_functionField_eq_of_square {X Y S T : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral S] [IsIntegral T] (π : X ⟶ Y) (g : Y ⟶ T) (f : X ⟶ S) (q : S ⟶ T)
    [IsDominant π] [IsDominant g] [IsDominant f] [IsDominant q] (hcomm : π ≫ g = f ≫ q)
    (hf : IsBirational f) (hg : IsBirational g) :
    letI := (functionFieldMap π).toAlgebra; letI := (functionFieldMap q).toAlgebra
    Module.finrank Y.functionField X.functionField =
      Module.finrank T.functionField S.functionField := by
  have key : ∀ (k : X ⟶ T) [IsDominant k], k = π ≫ g → k = f ≫ q →
      (functionFieldMap π).comp (functionFieldMap g) =
        (functionFieldMap f).comp (functionFieldMap q) := by
    rintro k _ h1 h2
    rw [← functionFieldMap_comp, ← functionFieldMap_comp]
    have : ∀ (k₁ k₂ : X ⟶ T) [IsDominant k₁] [IsDominant k₂], k₁ = k₂ →
        functionFieldMap k₁ = functionFieldMap k₂ := by rintro _ _ _ _ rfl; rfl
    exact this _ _ hcomm
  have hsq := key (π ≫ g) rfl hcomm
  exact finrank_eq_of_comp_eq_of_bijective (functionFieldMap g) (functionFieldMap q)
    (functionFieldMap π) (functionFieldMap f)
    ⟨(functionFieldMap g).injective, hg.surjective_functionFieldMap⟩
    ⟨(functionFieldMap f).injective, hf.surjective_functionFieldMap⟩ hsq

/-- The two spellings of the function field map agree. -/
theorem functionFieldMap_eq_hom_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (h : X ⟶ Y) [IsDominant h] :
    functionFieldMap h = (Scheme.Hom.functionFieldMap h).hom := by
  simp [Scheme.Hom.functionFieldMap, functionFieldMap, TopCat.Presheaf.stalkCongr_hom]

/-- **The degree over the sections on an affine open is the degree of the function fields.**
For a dominant morphism `π : X ⟶ Y` of integral schemes and a nonempty affine open `V` of `Y`
whose preimage is affine and nonempty, `[Γ(X, π⁻¹V) : Γ(Y, V)]` is `[K(X) : K(Y)]`. -/
theorem finrank_sections_eq_finrank_functionField {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (π : X ⟶ Y) [IsDominant π] (V : Y.Opens) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (π ⁻¹ᵁ V)) [Nonempty V] [Nonempty (π ⁻¹ᵁ V)] :
    letI := (π.app V).hom.toAlgebra; letI := (functionFieldMap π).toAlgebra
    Module.finrank Γ(Y, V) Γ(X, π ⁻¹ᵁ V) = Module.finrank Y.functionField X.functionField := by
  let := (π.app V).hom.toAlgebra
  let := (functionFieldMap π).toAlgebra
  let : Algebra Γ(Y, V) X.functionField :=
    ((algebraMap Γ(X, π ⁻¹ᵁ V) X.functionField).comp (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V))).toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, π ⁻¹ᵁ V) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(Y, V) Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun d => ?_
    change (X.germToFunctionField (π ⁻¹ᵁ V)) (π.app V d) =
      functionFieldMap π (Y.germToFunctionField V d)
    rw [functionFieldMap_eq_hom_functionFieldMap,
      π.functionFieldMap_germToFunctionField (U := V) (V := π ⁻¹ᵁ V) le_rfl]
    simp [Scheme.Hom.appLE]
  have := functionField_isFractionRing_of_isAffineOpen (X := Y) V hV
  have := functionField_isFractionRing_of_isAffineOpen (X := X) (π ⁻¹ᵁ V) hV'
  exact (IsFractionRing.finrank_eq Γ(Y, V) Y.functionField Γ(X, π ⁻¹ᵁ V) X.functionField).symm

/-- **The degree of `Spec A ⟶ Spec B` on function fields is `[A : B]`**, for a finite injective
map of domains `B → A`, read on the global sections and transported along `Γ(Spec R, ⊤) ≅ R`. -/
theorem finrank_functionField_specMap (B A : Type u) [CommRing B] [IsDomain B] [CommRing A]
    [IsDomain A] [Algebra B A] [FaithfulSMul B A]
    [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap B A)))] :
    letI := (functionFieldMap (Spec.map (CommRingCat.ofHom (algebraMap B A)))).toAlgebra
    Module.finrank (Spec (.of B)).functionField (Spec (.of A)).functionField =
      Module.finrank B A := by
  let q : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B A))
  obtain ⟨b0⟩ : Nonempty (PrimeSpectrum B) := inferInstance
  obtain ⟨a0⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  have : Nonempty (⊤ : (Spec (.of B)).Opens) := ⟨⟨b0, trivial⟩⟩
  have : Nonempty (q ⁻¹ᵁ ⊤) := ⟨⟨a0, trivial⟩⟩
  rw [← finrank_sections_eq_finrank_functionField q ⊤ (isAffineOpen_top _)
    (isAffineOpen_top (Spec (.of A)))]
  let : Algebra Γ(Spec (.of B), ⊤) Γ(Spec (.of A), ⊤) := (q.app ⊤).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv
    (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv ?_).symm
  have := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap B A)))
  ext b
  exact (congrFun (congrArg DFunLike.coe this) b).symm

end AlgebraicGeometry

end
