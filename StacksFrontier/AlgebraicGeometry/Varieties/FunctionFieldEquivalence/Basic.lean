module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Generic points, stalks and partial maps

Preliminaries on generic points used to compare dominant rational maps of varieties with maps
of their function fields: the generic point of an irreducible scheme lies in every dense open and
is preserved by dominant morphisms, the stalk of the spectrum of a field at its unique point is
that field, and the morphism attached to a partial map out of the generic stalk is compatible with
composition.

## Main results

* `AlgebraicGeometry.genericPoint_mem_of_dense` — the generic point lies in every dense open.
* `AlgebraicGeometry.map_genericPoint_of_isDominant` — dominant morphisms preserve generic points.
* `AlgebraicGeometry.fieldBaseStalkAlgebraMap_surjective` — the stalk of `Spec k` at its unique
  point is a quotient of `k`.
* `AlgebraicGeometry.partialMap_fromFunctionField_comp` — compatibility of the canonical morphism
  out of the generic stalk with composition of partial maps.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The generic point of an irreducible scheme lies in every dense open subset. -/
lemma genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) (hU : Dense (U : Set X)) : genericPoint X ∈ U := by
  let : Nonempty X := ⟨genericPoint X⟩
  exact (genericPoint_spec X).mem_open_set_iff U.2 |>.2 (by simpa using hU.nonempty)

/-- A dominant morphism of irreducible schemes carries the generic point to the generic point. -/
lemma map_genericPoint_of_isDominant {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact ((genericPoint_spec Y).eq h).symm

/-- Transporting the canonical map from a ring to the stalk of its spectrum along an equality of
points gives the canonical map at the second point. -/
lemma primeSpectrum_toStalk_congr {k : Type u} [Field k]
    {p q : PrimeSpectrum k} (h : p = q) :
    (eqToHom (congrArg (fun z : PrimeSpectrum k =>
      (Spec (.of k)).presheaf.stalk z) h)).hom.comp
      (StructureSheaf.toStalk k p).hom = (StructureSheaf.toStalk k q).hom := by
  cases h
  rfl

/-- On the spectrum of a field, every stalk map out of the field is surjective: the spectrum is
a single point, so the stalk at it is canonically the field itself. -/
lemma fieldBaseStalkAlgebraMap_surjective {k : Type u} [Field k]
    {p : PrimeSpectrum k} (hp : p = IsLocalRing.closedPoint k) :
    Function.Surjective ((StructureSheaf.toStalk k p).hom) := by
  let : Algebra k ((Spec (.of k)).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra k p
  let eR : (Spec (.of k)).presheaf.stalk p ≅ .of k :=
    (Spec (.of k)).presheaf.stalkCongr (Inseparable.of_eq hp) ≪≫
      stalkClosedPointIso (.of k)
  have heq : (StructureSheaf.toStalk k p).hom = eR.inv.hom := by
    ext s
    dsimp only [eR, Iso.trans_inv]
    rw [stalkClosedPointIso_inv]
    change (StructureSheaf.toStalk k p).hom s =
      (StructureSheaf.toStalk k (IsLocalRing.closedPoint k) ≫
        (Spec (.of k)).presheaf.stalkSpecializes (Inseparable.of_eq hp).le).hom s
    exact congrArg
      (fun h : .of k ⟶ (Spec (.of k)).presheaf.stalk p => h.hom s)
      (StructureSheaf.toStalk_stalkSpecializes (R := k) (Inseparable.of_eq hp).le).symm
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso eR.inv).surjective

/-- Two maps out of stalks at equal points which agree up to heterogeneous equality induce the same
morphism to the scheme after composing with the canonical map from the spectrum of the stalk. -/
lemma specMap_fromSpecStalk_eq_of_heq {X : Scheme.{u}} {R : CommRingCat.{u}}
    {x y : X} {f : X.presheaf.stalk x ⟶ R} {g : X.presheaf.stalk y ⟶ R}
    (h : x = y) (hf : HEq f g) :
    Spec.map f ≫ X.fromSpecStalk x = Spec.map g ≫ X.fromSpecStalk y := by
  cases h
  cases hf
  rfl

/-- The canonical morphism from the spectrum of the function field attached to a composition of
partial maps factors through the morphism attached to the first factor. -/
lemma partialMap_fromFunctionField_comp {X Y Z : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (φ : Spec X.functionField ⟶ Spec Y.functionField)
    (hφ : φ ≫ Y.fromSpecStalk (genericPoint Y) = f.fromFunctionField) :
    (f.comp g).fromFunctionField = φ ≫ g.fromFunctionField := by
  let h := f.comp g
  let x := genericPoint X
  let y := genericPoint Y
  let a := f.domain.fromSpecStalkOfMem x
    (genericPoint_mem_of_dense f.domain f.dense_domain)
  let b := g.domain.fromSpecStalkOfMem y
    (genericPoint_mem_of_dense g.domain g.dense_domain)
  let c := h.domain.fromSpecStalkOfMem x
    (genericPoint_mem_of_dense h.domain h.dense_domain)
  change Spec (X.presheaf.stalk x) ⟶
    (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).toScheme at c
  let e := (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv
  have hc : c ≫ e ≫ (f.hom ⁻¹ᵁ g.domain).ι = a := by
    apply (cancel_mono f.domain.ι).mp
    calc
      (c ≫ e ≫ (f.hom ⁻¹ᵁ g.domain).ι) ≫ f.domain.ι =
          c ≫ (e ≫ (f.hom ⁻¹ᵁ g.domain).ι ≫ f.domain.ι) := by
            exact congrArg (fun t ↦ t ≫ f.domain.ι)
              (Category.assoc c e (f.hom ⁻¹ᵁ g.domain).ι).symm
      _ = c ≫ (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).ι := by
        dsimp only [e]
        exact congrArg (fun t ↦ c ≫ t)
          (Scheme.Hom.isoImage_inv_ι f.domain.ι (f.hom ⁻¹ᵁ g.domain))
      _ = a ≫ f.domain.ι := by
        change h.domain.fromSpecStalkOfMem x _ ≫ h.domain.ι =
          f.domain.fromSpecStalkOfMem x _ ≫ f.domain.ι
        exact (h.domain.fromSpecStalkOfMem_ι x _).trans
          (f.domain.fromSpecStalkOfMem_ι x _).symm
  have hb : c ≫ e ≫ f.hom ∣_ g.domain = φ ≫ b := by
    apply (cancel_mono g.domain.ι).mp
    calc
      (c ≫ e ≫ f.hom ∣_ g.domain) ≫ g.domain.ι =
          (c ≫ e ≫ (f.hom ⁻¹ᵁ g.domain).ι) ≫ f.hom := by
            calc
              _ = (c ≫ e) ≫ ((f.hom ∣_ g.domain) ≫ g.domain.ι) := by
                exact congrArg (fun t ↦ t ≫ g.domain.ι)
                  (Category.assoc c e (f.hom ∣_ g.domain)).symm
              _ = (c ≫ e) ≫ ((f.hom ⁻¹ᵁ g.domain).ι ≫ f.hom) := by
                rw [morphismRestrict_ι]
              _ = _ := by
                exact congrArg (fun t ↦ t ≫ f.hom)
                  (Category.assoc c e (f.hom ⁻¹ᵁ g.domain).ι)
      _ = a ≫ f.hom := congrArg (fun t ↦ t ≫ f.hom) hc
      _ = φ ≫ Y.fromSpecStalk y := hφ.symm
      _ = (φ ≫ b) ≫ g.domain.ι := by simp [b, Category.assoc]
  change c ≫ (e ≫ f.hom ∣_ g.domain ≫ g.hom) = φ ≫ (b ≫ g.hom)
  calc
    _ = (c ≫ e ≫ f.hom ∣_ g.domain) ≫ g.hom := by
      exact congrArg (fun t ↦ t ≫ g.hom)
        (Category.assoc c e (f.hom ∣_ g.domain))
    _ = (φ ≫ b) ≫ g.hom := congrArg (fun t ↦ t ≫ g.hom) hb
    _ = _ := by simp only [Category.assoc]

end AlgebraicGeometry

end
