module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Linear functors agree on finite biproducts of an object with scalar endomorphisms

Let `R` be a commutative ring, let `𝒜` and `𝒞` be `R`-linear categories, and let `a` be an object
of `𝒜` every endomorphism of which is a scalar multiple of the identity — for instance `R` itself
in the category of `R`-modules, or the structure sheaf of `Spec` of a field. Two `R`-linear
functors `Φ₁ Φ₂ : 𝒜 ⥤ 𝒞` together with an isomorphism `ε : Φ₁ a ≅ Φ₂ a` are then isomorphic on
the finite biproducts of copies of `a`, compatibly with every morphism between them: a morphism
`⨁ a ⟶ ⨁ a` is a matrix of scalars, both functors send it to the same matrix of scalars, and
scalars commute with `ε`.

This identifies, for an `R`-linear exact functor `F`, the functors `V ↦ F(V ⊗_R G)` and
`V ↦ V ⊗_R F(G)` on finite free `V` (taking the second category to be a functor category makes
the identification natural in `G` as well), which the construction of [Stacks, Section 0G07]
uses to compare its two Postnikov systems.

## Main definitions

* `CategoryTheory.Linear.scalarBiproductIso`: the isomorphism `Φ₁ W ≅ Φ₂ W` attached to a
  decomposition `W ≅ ⨁ᵢ a`.

## Main results

* `CategoryTheory.Linear.scalarBiproductIso_comm`: the isomorphisms attached to two
  decompositions commute with the images of every morphism under the two functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Linear

variable (R : Type*) [CommRing R] {𝒜 𝒞 : Type*} [Category* 𝒜] [Category* 𝒞]
  [Preadditive 𝒜] [Preadditive 𝒞] [CategoryTheory.Linear R 𝒜] [CategoryTheory.Linear R 𝒞]
  [HasFiniteBiproducts 𝒜] [HasFiniteBiproducts 𝒞]
  {a : 𝒜} (Φ₁ Φ₂ : 𝒜 ⥤ 𝒞) [Φ₁.Additive] [Φ₂.Additive] (ε : Φ₁.obj a ≅ Φ₂.obj a)

/-- The isomorphism `Φ₁ W ≅ Φ₂ W` attached to a decomposition `W ≅ ⨁_{i < n} a` and an
isomorphism `ε : Φ₁ a ≅ Φ₂ a`: transport along the decomposition, commute both functors with the
biproduct, and apply `ε` on every summand. -/
noncomputable def scalarBiproductIso {W : 𝒜} {n : ℕ} (e : W ≅ ⨁ fun _ : Fin n => a) :
    Φ₁.obj W ≅ Φ₂.obj W :=
  Φ₁.mapIso e ≪≫ Φ₁.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ => ε) ≪≫
    (Φ₂.mapBiproduct _).symm ≪≫ Φ₂.mapIso e.symm

section Canonical

variable {n : ℕ}

/-- The isomorphism `Φ₁ (⨁ a) ≅ Φ₂ (⨁ a)` applying `ε` on every summand. -/
private noncomputable abbrev β : Φ₁.obj (⨁ fun _ : Fin n => a) ≅ Φ₂.obj (⨁ fun _ : Fin n => a) :=
  Φ₁.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ => ε) ≪≫ (Φ₂.mapBiproduct _).symm

omit [HasFiniteBiproducts 𝒞] in
private theorem map_ι_comp_β_hom (j : Fin n) :
    Φ₁.map (biproduct.ι (fun _ : Fin n => a) j) ≫ (β Φ₁ Φ₂ ε).hom =
      ε.hom ≫ Φ₂.map (biproduct.ι (fun _ : Fin n => a) j) := by
  have h₁ : Φ₁.map (biproduct.ι (fun _ : Fin n => a) j) ≫ (Φ₁.mapBiproduct _).hom =
      biproduct.ι (Φ₁.obj ∘ fun _ : Fin n => a) j := by
    rw [← Iso.eq_comp_inv, Functor.mapBiproduct_inv]
    exact (biproduct.ι_desc (fun j => Φ₁.map (biproduct.ι (fun _ : Fin n => a) j)) j).symm
  have h₂ : biproduct.ι (Φ₂.obj ∘ fun _ : Fin n => a) j ≫ (Φ₂.mapBiproduct _).inv =
      Φ₂.map (biproduct.ι (fun _ : Fin n => a) j) := by
    rw [Functor.mapBiproduct_inv]
    exact biproduct.ι_desc (fun j => Φ₂.map (biproduct.ι (fun _ : Fin n => a) j)) j
  have h₃ : biproduct.ι (Φ₁.obj ∘ fun _ : Fin n => a) j ≫
      biproduct.map (fun _ : Fin n => ε.hom) =
        ε.hom ≫ biproduct.ι (Φ₂.obj ∘ fun _ : Fin n => a) j :=
    biproduct.ι_map (f := Φ₁.obj ∘ fun _ : Fin n => a) (g := Φ₂.obj ∘ fun _ : Fin n => a) _ j
  simp only [β, Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom, reassoc_of% h₁,
    biproduct.ι_map_assoc]
  exact congrArg (ε.hom ≫ ·) h₂

omit [HasFiniteBiproducts 𝒞] in
private theorem β_hom_comp_map_π (j : Fin n) :
    (β Φ₁ Φ₂ ε).hom ≫ Φ₂.map (biproduct.π (fun _ : Fin n => a) j) =
      Φ₁.map (biproduct.π (fun _ : Fin n => a) j) ≫ ε.hom := by
  have h₁ : (Φ₂.mapBiproduct (fun _ : Fin n => a)).inv ≫
      Φ₂.map (biproduct.π (fun _ : Fin n => a) j) =
        biproduct.π (Φ₂.obj ∘ fun _ : Fin n => a) j := by
    rw [Iso.inv_comp_eq, Functor.mapBiproduct_hom]
    exact (biproduct.lift_π (fun j => Φ₂.map (biproduct.π (fun _ : Fin n => a) j)) j).symm
  have h₂ : (Φ₁.mapBiproduct (fun _ : Fin n => a)).hom ≫
      biproduct.π (Φ₁.obj ∘ fun _ : Fin n => a) j =
        Φ₁.map (biproduct.π (fun _ : Fin n => a) j) := by
    rw [Functor.mapBiproduct_hom]
    exact biproduct.lift_π (fun j => Φ₁.map (biproduct.π (fun _ : Fin n => a) j)) j
  have h₃ : biproduct.map (fun _ : Fin n => ε.hom) ≫
      biproduct.π (Φ₂.obj ∘ fun _ : Fin n => a) j =
        biproduct.π (Φ₁.obj ∘ fun _ : Fin n => a) j ≫ ε.hom :=
    biproduct.map_π (f := Φ₁.obj ∘ fun _ : Fin n => a) (g := Φ₂.obj ∘ fun _ : Fin n => a) _ j
  simp only [β, Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom, Category.assoc, h₁]
  exact (congrArg (fun t => (Φ₁.mapBiproduct (fun _ : Fin n => a)).hom ≫ t) h₃).trans
    (by rw [← Category.assoc, h₂])

omit [HasFiniteBiproducts 𝒞] in
/-- The identity of `Φ (⨁ a)` is the sum of the images of the projections followed by the
inclusions. -/
private theorem id_eq_sum (Φ : 𝒜 ⥤ 𝒞) [Φ.Additive] :
    𝟙 (Φ.obj (⨁ fun _ : Fin n => a)) =
      ∑ j, Φ.map (biproduct.π (fun _ : Fin n => a) j) ≫
        Φ.map (biproduct.ι (fun _ : Fin n => a) j) := by
  rw [← Φ.map_id, ← biproduct.total, Φ.map_sum]
  simp only [Φ.map_comp]

omit [HasFiniteBiproducts 𝒞] in
/-- A morphism out of `Φ (⨁ a)` is determined by its composites with the images of the
inclusions. -/
private theorem hom_ext_map_ι (Φ : 𝒜 ⥤ 𝒞) [Φ.Additive] {Z : 𝒞}
    {f g : Φ.obj (⨁ fun _ : Fin n => a) ⟶ Z}
    (h : ∀ j, Φ.map (biproduct.ι (fun _ : Fin n => a) j) ≫ f =
      Φ.map (biproduct.ι (fun _ : Fin n => a) j) ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g, id_eq_sum Φ, Preadditive.sum_comp,
    Preadditive.sum_comp]
  simp only [Category.assoc, h]

omit [HasFiniteBiproducts 𝒞] in
/-- A morphism into `Φ (⨁ a)` is determined by its composites with the images of the
projections. -/
private theorem hom_ext_map_π (Φ : 𝒜 ⥤ 𝒞) [Φ.Additive] {Z : 𝒞}
    {f g : Z ⟶ Φ.obj (⨁ fun _ : Fin n => a)}
    (h : ∀ j, f ≫ Φ.map (biproduct.π (fun _ : Fin n => a) j) =
      g ≫ Φ.map (biproduct.π (fun _ : Fin n => a) j)) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, id_eq_sum Φ, Preadditive.comp_sum,
    Preadditive.comp_sum]
  simp only [← Category.assoc, h]

variable (ha : ∀ φ : a ⟶ a, ∃ r : R, φ = r • 𝟙 a) [Φ₁.Linear R] [Φ₂.Linear R]
include ha

omit [HasFiniteBiproducts 𝒞] in
/-- **The images of a morphism `⨁ a ⟶ ⨁ a` under two linear functors are intertwined by `ε`
applied on every summand.** -/
private theorem map_comp_β_hom {m : ℕ}
    (ψ : (⨁ fun _ : Fin n => a) ⟶ ⨁ fun _ : Fin m => a) :
    Φ₁.map ψ ≫ (β Φ₁ Φ₂ ε).hom = (β Φ₁ Φ₂ ε).hom ≫ Φ₂.map ψ := by
  refine hom_ext_map_ι Φ₁ fun j => hom_ext_map_π Φ₂ fun i => ?_
  obtain ⟨r, hr⟩ := ha (biproduct.ι (fun _ : Fin n => a) j ≫ ψ ≫
    biproduct.π (fun _ : Fin m => a) i)
  have hl : Φ₁.map (biproduct.ι (fun _ : Fin n => a) j) ≫ Φ₁.map ψ ≫ (β Φ₁ Φ₂ ε).hom ≫
      Φ₂.map (biproduct.π (fun _ : Fin m => a) i) = r • ε.hom := by
    rw [β_hom_comp_map_π, ← Φ₁.map_comp_assoc, ← Φ₁.map_comp_assoc, Category.assoc, hr,
      Φ₁.map_smul, Φ₁.map_id, Linear.smul_comp, Category.id_comp]
  have hr' : Φ₁.map (biproduct.ι (fun _ : Fin n => a) j) ≫ (β Φ₁ Φ₂ ε).hom ≫ Φ₂.map ψ ≫
      Φ₂.map (biproduct.π (fun _ : Fin m => a) i) = r • ε.hom := by
    rw [reassoc_of% map_ι_comp_β_hom, ← Φ₂.map_comp, ← Φ₂.map_comp, hr,
      Φ₂.map_smul, Φ₂.map_id, Linear.comp_smul, Category.comp_id]
  simpa only [Category.assoc] using hl.trans hr'.symm

end Canonical

variable (ha : ∀ φ : a ⟶ a, ∃ r : R, φ = r • 𝟙 a) [Φ₁.Linear R] [Φ₂.Linear R]
omit [HasFiniteBiproducts 𝒞] in
include ha in
/-- **The isomorphisms attached to decompositions into copies of `a` are natural**: for
decompositions `W ≅ ⨁ a` and `W' ≅ ⨁ a` and any morphism `φ : W ⟶ W'`, the square formed by
`Φ₁ φ`, `Φ₂ φ` and the two isomorphisms commutes. -/
theorem scalarBiproductIso_comm {W W' : 𝒜} {n m : ℕ} (e : W ≅ ⨁ fun _ : Fin n => a)
    (e' : W' ≅ ⨁ fun _ : Fin m => a) (φ : W ⟶ W') :
    Φ₁.map φ ≫ (scalarBiproductIso Φ₁ Φ₂ ε e').hom =
      (scalarBiproductIso Φ₁ Φ₂ ε e).hom ≫ Φ₂.map φ := by
  have key := map_comp_β_hom R Φ₁ Φ₂ ε ha (e.inv ≫ φ ≫ e'.hom)
  have h₁ : Φ₁.map φ = Φ₁.map e.hom ≫ Φ₁.map (e.inv ≫ φ ≫ e'.hom) ≫ Φ₁.map e'.inv := by
    simp only [← Φ₁.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have h₂ : Φ₂.map φ = Φ₂.map e.hom ≫ Φ₂.map (e.inv ≫ φ ≫ e'.hom) ≫ Φ₂.map e'.inv := by
    simp only [← Φ₂.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  simp only [scalarBiproductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    biproduct.mapIso_hom, Category.assoc, h₁, h₂]
  rw [← Φ₁.map_comp_assoc e'.inv e'.hom, Iso.inv_hom_id, Φ₁.map_id, Category.id_comp,
    ← Φ₂.map_comp_assoc e.inv e.hom, Iso.inv_hom_id, Φ₂.map_id, Category.id_comp]
  simp only [β, Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom, Category.assoc] at key
  rw [reassoc_of% key]

end CategoryTheory.Linear
