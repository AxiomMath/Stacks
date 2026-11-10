module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.RingTheory.FilteredColimitFiniteProducts.SeparableTensorSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The fibre of a base change over a field-valued point

Let `X` be a presheaf on the big fppf site of `S ≅ Spec k`, let `Ω/k` be a field extension and
let `p : h_Ω ⟶ X` be an `Ω`-valued point. The fibre of the projection `X_Ω = h_Ω × X ⟶ X` over
the point of `p` is covered by the spectrum of any `k`-algebra `A` with two `k`-algebra maps
`i₁, i₂ : Ω ⟶ A` through which every pair of `k`-embeddings of `Ω` into a field factors: a point
of the fibre is a pair of such embeddings into a common field, and the morphism
`(Spec i₁, p ∘ Spec i₂) : Spec A ⟶ X_Ω` hits it.

For `Ω` algebraic over `k` the algebra `Ω ⊗_F Ω`, with `F` the perfect closure of `k` in `Ω`, has
this property, because two `k`-embeddings of `Ω` into a field agree on the purely inseparable
extension `F/k`. When `Ω` is algebraically closed this algebra is a filtered colimit of finite
products of copies of `Ω`, the shape the source's Groupoids, Lemma 0B7U asks for.

## Main definitions

* `AlgebraicGeometry.Space.GroupOverField.algObj`: the spectrum of a `k`-algebra as an object of
  the big fppf site of `S ≅ Spec k`, and `algMap` the morphism to the spectrum of a field
  extension attached to a `k`-algebra map.

## Main results

* `AlgebraicGeometry.Space.GroupOverField.mem_range_of_pointsMap_snd_eq`: the fibre statement.
* `AlgebraicGeometry.Space.GroupOverField.exists_algHom_perfectClosureTensor`: the factorisation
  property of `Ω ⊗_F Ω`.
* `AlgebraicGeometry.Space.GroupOverField.isFilteredColimitOfFiniteProducts_perfectClosureTensor`:
  for `Ω` algebraically closed and algebraic over `k`, `Ω ⊗_F Ω` is a filtered colimit of finite
  products of copies of `Ω`.

## References

* [Stacks Project, Tag 0B7U](https://stacks.math.columbia.edu/tag/0B7U)
* [Stacks Project, Tag 0B8G](https://stacks.math.columbia.edu/tag/0B8G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space.GroupOverField

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {k : Type u} [Field k] (e : S ≅ Spec (.of k))

/-- The spectrum of a `k`-algebra `A`, as an object of the big fppf site of `S ≅ Spec k`. -/
noncomputable abbrev algObj (A : Type u) [CommRing A] [Algebra k A]
    (hA : C.Contains (Spec (.of A))) : BigFppfOver C S hS :=
  Over.mk (⟨Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ e.inv⟩ : C.obj hA ⟶ C.obj hS)

/-- The morphism `Spec A ⟶ Spec K` of the big fppf site of `S` attached to a `k`-algebra map
`K ⟶ A` out of a field. -/
noncomputable def algMap {K A : Type u} [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    {hK : C.Contains (Spec (.of K))} {hA : C.Contains (Spec (.of A))} (φ : K →ₐ[k] A) :
    algObj C S hS e A hA ⟶ extObj C S hS e K hK :=
  Over.homMk ⟨Spec.map (CommRingCat.ofHom φ.toRingHom)⟩ (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ e.inv
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext φ.commutes))

/-- The morphism `Spec M ⟶ Spec A` of the big fppf site of `S` out of the object of a
field-valued point, attached to a `k`-algebra map `A ⟶ M` for the algebra structure of the
point. -/
noncomputable def pointAlgMap {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (r : FieldValuedPoint C S hS F) {A : Type u} [CommRing A] [Algebra k A]
    {hA : C.Contains (Spec (.of A))}
    (γ : letI := pointAlgebra C S hS e r; A →ₐ[k] r.carrier) :
    r.siteObject C S hS F ⟶ algObj C S hS e A hA :=
  letI := pointAlgebra C S hS e r
  Over.homMk ⟨Spec.map (CommRingCat.ofHom γ.toRingHom)⟩ (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom γ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ e.inv = r.toBase
    rw [toBase_eq_pointAlgebra C S hS e r, ← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext γ.commutes))

/-- A composite `Spec M ⟶ Spec A ⟶ Spec K` of `pointAlgMap γ` and `algMap φ` is the morphism of
the `k`-algebra map `γ ∘ φ`. -/
theorem pointAlgMap_comp_algMap {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (r : FieldValuedPoint C S hS F) {K A : Type u} [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] {hK : C.Contains (Spec (.of K))} {hA : C.Contains (Spec (.of A))}
    (γ : letI := pointAlgebra C S hS e r; A →ₐ[k] r.carrier) (φ : K →ₐ[k] A)
    (h : r.siteObject C S hS F ⟶ extObj C S hS e K hK)
    (β : letI := pointAlgebra C S hS e r; K →ₐ[k] r.carrier)
    (hβ : letI := pointAlgebra C S hS e r
      h.left.hom = Spec.map (CommRingCat.ofHom β.toRingHom))
    (hγ : letI := pointAlgebra C S hS e r; γ.comp φ = β) :
    pointAlgMap C S hS e r (hA := hA) γ ≫ algMap C S hS e φ = h := by
  let := pointAlgebra C S hS e r
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom γ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) = h.left.hom
  rw [hβ, ← Spec.map_comp, ← hγ]
  rfl

/-- **The fibre of `X_Ω ⟶ X` over an `Ω`-valued point.** Let `p : h_Ω ⟶ X` be an `Ω`-valued
point of a presheaf `X` and let `i₁, i₂ : Ω ⟶ A` be `k`-algebra maps through which every pair
of `k`-embeddings of `Ω` into a field factors. Then every point of `X_Ω = h_Ω × X` over the
point of `p` is in the image of `(Spec i₁, p ∘ Spec i₂) : Spec A ⟶ X_Ω`.

A point of the fibre is represented, over a common field `M`, by a point `(β, x)` of `X_Ω`
with `x = p ∘ α`; the factorisation `γ : A ⟶ M` of `(β, α)` exhibits it as the image of the
`M`-valued point `Spec γ` of `Spec A`. -/
theorem mem_range_of_pointsMap_snd_eq (X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) (Ω : Type u)
    [Field Ω] [Algebra k Ω] (hΩ : C.Contains (Spec (.of Ω)))
    (p : yoneda.obj (extObj C S hS e Ω hΩ) ⟶ X) (A : Type u) [CommRing A] [Algebra k A]
    (hA : C.Contains (Spec (.of A))) (i₁ i₂ : Ω →ₐ[k] A)
    (hfac : ∀ (M : Type u) [Field M] [Algebra k M] (α β : Ω →ₐ[k] M),
      ∃ γ : A →ₐ[k] M, γ.comp i₁ = α ∧ γ.comp i₂ = β)
    (y : points C S hS (yoneda.obj (extObj C S hS e Ω hΩ) ⨯ X))
    (hy : pointsMap C S hS _ prod.snd y = (ptOf C S hS e X Ω hΩ p).class C S hS X) :
    y ∈ Set.range (pointsMap C S hS (yoneda.obj (algObj C S hS e A hA))
      (prod.lift (yoneda.map (algMap C S hS e (hA := hA) (hK := hΩ) i₁))
        (yoneda.map (algMap C S hS e (hA := hA) (hK := hΩ) i₂) ≫ p))) := by
  obtain ⟨w, rfl⟩ := Quot.exists_rep y
  change (w.map C S hS _ prod.snd).class C S hS X = _ at hy
  obtain ⟨r, ⟨f₀, hf⟩, ⟨g₀, hg⟩⟩ := (FieldValuedPoint.class_eq_class_iff C S hS X _ _).mp hy
  let f : r.siteObject C S hS X ⟶ w.siteObject C S hS _ := f₀
  let g : r.siteObject C S hS X ⟶ extObj C S hS e Ω hΩ := g₀
  let := pointAlgebra C S hS e r
  let t := yonedaEquiv.symm w.value
  let t₁ : w.siteObject C S hS _ ⟶ extObj C S hS e Ω hΩ := yoneda.preimage (t ≫ prod.fst)
  obtain ⟨β, hβ⟩ := exists_algHom_of_hom C S hS e r (f ≫ t₁)
  obtain ⟨α, hα⟩ := exists_algHom_of_hom C S hS e r g
  obtain ⟨γ, hγ₁, hγ₂⟩ := hfac r.carrier β α
  let Ψ := prod.lift (yoneda.map (algMap C S hS e (hA := hA) (hK := hΩ) i₁))
      (yoneda.map (algMap C S hS e (hA := hA) (hK := hΩ) i₂) ≫ p)
  let c : r.siteObject C S hS X ⟶ algObj C S hS e A hA := pointAlgMap C S hS e r γ
  have hc₁ : c ≫ algMap C S hS e (hA := hA) (hK := hΩ) i₁ = f ≫ t₁ :=
    pointAlgMap_comp_algMap C S hS e r γ i₁ _ β hβ hγ₁
  have hc₂ : c ≫ algMap C S hS e (hA := hA) (hK := hΩ) i₂ = g :=
    pointAlgMap_comp_algMap C S hS e r γ i₂ _ α hα hγ₂
  -- the `M`-valued point `Spec γ` of `Spec A`
  let q : FieldValuedPoint C S hS (yoneda.obj (algObj C S hS e A hA)) :=
    { carrier := r.carrier, contained := r.contained, toBase := r.toBase, value := c }
  refine ⟨q.class C S hS _, ?_⟩
  rw [pointsMap_class]
  -- the restriction of `w` along `f`
  let r' : FieldValuedPoint C S hS (yoneda.obj (extObj C S hS e Ω hΩ) ⨯ X) :=
    { carrier := r.carrier, contained := r.contained, toBase := r.toBase
      value := (yoneda.obj (extObj C S hS e Ω hΩ) ⨯ X).map f.op w.value }
  have h1 : r'.class C S hS _ = w.class C S hS _ :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS _
      ⟨r', FieldValuedPoint.dominates_refl C S hS _ _, f, rfl⟩
  change _ = w.class C S hS _
  rw [← h1]
  congr 1
  change FieldValuedPoint.mk _ _ _ (Ψ.app _ c) = FieldValuedPoint.mk _ _ _ _
  congr 1
  apply yonedaEquiv.symm.injective
  rw [yonedaEquiv_symm_map]
  change yonedaEquiv.symm (Ψ.app _ (yonedaEquiv (yoneda.map c))) = yoneda.map f ≫ t
  rw [← yonedaEquiv_comp, Equiv.symm_apply_apply]
  apply prod.hom_ext
  · simp only [Category.assoc, Ψ, prod.lift_fst, ← Functor.map_comp, hc₁]
    simp [t₁, t]
  · have hsnd : yoneda.map f ≫ t ≫ prod.snd = yonedaEquiv.symm r.value := by
      rw [← hf, yonedaEquiv_symm_map]
      change yoneda.map f ≫ yonedaEquiv.symm w.value ≫ prod.snd = _
      rw [yonedaEquiv_symm_naturality_right _ (prod.snd : _ ⨯ X ⟶ X) w.value]
      rfl
    have hρ : yoneda.map g ≫ p = yonedaEquiv.symm r.value := by
      rw [← hg, yonedaEquiv_symm_map]
      exact congrArg (yoneda.map g ≫ ·) (Equiv.symm_apply_apply yonedaEquiv p).symm
    simp only [Category.assoc, Ψ, prod.lift_snd]
    rw [hsnd, ← hρ, ← hc₂, Functor.map_comp, Category.assoc]

/-! ### The algebra `Ω ⊗_F Ω` -/

section PerfectClosureTensor

variable (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- **Two embeddings into a field factor through `Ω ⊗_F Ω`.** For `F` the perfect closure of `k`
in `Ω`, every pair of `k`-embeddings `α, β : Ω ⟶ M` into a field factors through the two
inclusions of `Ω ⊗_F Ω`: the two embeddings agree on the purely inseparable extension `F/k`. -/
theorem exists_algHom_perfectClosureTensor (M : Type u) [Field M] [Algebra k M]
    (α β : Ω →ₐ[k] M) :
    ∃ γ : (Ω ⊗[perfectClosure k Ω] Ω) →ₐ[k] M,
      γ.comp ((Algebra.TensorProduct.includeLeft
          (S := perfectClosure k Ω)).restrictScalars k) = α ∧
        γ.comp ((Algebra.TensorProduct.includeRight
          (R := perfectClosure k Ω) (A := Ω) (B := Ω)).restrictScalars k) = β := by
  let F := perfectClosure k Ω
  let : Algebra F M := ((α : Ω →+* M).comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower k F M := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap k M x = α (algebraMap F Ω (algebraMap k F x))
    rw [← IsScalarTower.algebraMap_apply, α.commutes]
  have hβF : ∀ x : F, β x = algebraMap F M x :=
    DFunLike.congr_fun (Subsingleton.elim (β.comp (IsScalarTower.toAlgHom k F Ω))
      (α.comp (IsScalarTower.toAlgHom k F Ω)))
  let α' : Ω →ₐ[F] M := { α with commutes' := fun _ => rfl }
  let β' : Ω →ₐ[F] M := { β with commutes' := hβF }
  refine ⟨(Algebra.TensorProduct.lift α' β' (fun _ _ => Commute.all _ _)).restrictScalars k,
    ?_, ?_⟩
  all_goals
    ext x
    refine (Algebra.TensorProduct.lift_tmul α' β' (fun _ _ => Commute.all _ _) _ _).trans ?_
    simp
    rfl

/-- **`Ω ⊗_F Ω` is a filtered colimit of finite products of `Ω`.** For `Ω` algebraically closed
and algebraic over `k`, and `F` the perfect closure of `k` in `Ω`, the extension `Ω/F` is
separable (`F` is perfect), so `Ω ⊗_F Ω` is a filtered colimit of finite products of copies of
`Ω`. -/
theorem isFilteredColimitOfFiniteProducts_perfectClosureTensor [IsAlgClosed Ω]
    [Algebra.IsAlgebraic k Ω] :
    IsFilteredColimitOfFiniteProducts Ω (Ω ⊗[perfectClosure k Ω] Ω) := by
  have : Algebra.IsAlgebraic (perfectClosure k Ω) Ω :=
    Algebra.IsAlgebraic.tower_top (K := k) _
  exact isFilteredColimitOfFiniteProducts_tensorProduct_of_isSeparable
    (perfectClosure k Ω) Ω Ω

end PerfectClosureTensor

end AlgebraicGeometry.Space.GroupOverField

end
