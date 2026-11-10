module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTransport

/-!
# The K-injective-resolution step for the tensor--Hom transpose

The chain-level value `derivedHomAdjunctionOverRing_homEquiv_apply` of the transpose of
[stacks 0A63] is available only at a **K-injective** target `I`: it is the specialization of the
structure field `DerivedHomData.homEquiv_symm_map_eq`, whose hypothesis `[I.IsKInjective]` cannot
be dropped, because the Hom comparison `DerivedHomData.homComparison` is a natural isomorphism
only on the K-injective part of the source.

Most targets occurring in practice are not of that form. The target of the transpose presenting
the lax monoidal structure map of derived base change, for instance, is a derived tensor product
`F.obj (X ⊗ᴸ Y)`, about which nothing is known.

This module removes that restriction. The content is the naturality field
`DerivedHomAdjunction.homEquiv_naturality_right`: an isomorphism `φ : M ≅ M'` of targets carries
the transpose at `M` to the transpose at `M'`, so the chain-level value at a K-injective complex
`I` *determines* the value at every object isomorphic to `Q.obj I` in the derived category — and,
by `exists_isKInjective_model`, that is every object at all.

## Main results

* `DerivedHomAdjunction.homEquiv_apply_of_iso` and
  `DerivedHomAdjunction.homEquiv_symm_apply_of_iso`: the transpose and its inverse transported
  along an isomorphism of the target. Stated for an arbitrary `DerivedHomAdjunction`.
* `exists_isKInjective_model`: every object of `D(R)`, in an arbitrary admissible module
  universe, is isomorphic to the scalar transport of `DerivedCategory.Q` of a K-injective complex
  of `ULift R`-modules. This is Stacks 079P read through `derivedScalarEquivalence`.
* `derivedHomAdjunctionOverRing_homEquiv_apply_of_resolution` and
  `derivedHomAdjunctionOverRing_homEquiv_symm_apply_of_resolution`: the chain-level transpose of
  [stacks 0A63] at a target that is **not** assumed K-injective, presented through a chosen
  K-injective resolution `φ` of it.
* `derivedHomAdjunctionOverRing_homEquiv_apply_eq_of_resolution`: the reduction in the form used
  by a consumer that holds an arbitrary morphism into the derived Hom object, with no model
  description of it: the transpose at `Z` is the transpose at the resolving K-injective complex,
  conjugated by `φ`.

## References

* [The Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [The Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory

namespace StacksDraft.DerivedHom

universe u v w

namespace DerivedHomAdjunction

section TargetIso

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- The derived Hom bifunctor at a composite in its second variable. -/
@[reassoc] theorem hom_map_comp_right {L : DerivedCategory (ModuleCat.{v} R)}
    {M M' M'' : DerivedCategory (ModuleCat.{v} R)} (g : M ⟶ M') (g' : M' ⟶ M'') :
    d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L, M') from (𝟙 (Opposite.op L), g)) ≫
        d.hom.map (show (Opposite.op L, M') ⟶ (Opposite.op L, M'') from
          (𝟙 (Opposite.op L), g')) =
      d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L, M'') from
        (𝟙 (Opposite.op L), g ≫ g')) := by
  rw [← d.hom.map_comp]
  congr 1
  simp only [prod_comp, Category.comp_id]

/-- The derived Hom bifunctor at an isomorphism of its second variable is an isomorphism, with
the evident inverse. -/
theorem hom_map_right_comp_hom_map_right_inv {L M M' : DerivedCategory (ModuleCat.{v} R)}
    (φ : M ≅ M') :
    d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L, M') from
        (𝟙 (Opposite.op L), φ.hom)) ≫
        d.hom.map (show (Opposite.op L, M') ⟶ (Opposite.op L, M) from
          (𝟙 (Opposite.op L), φ.inv)) =
      𝟙 (d.hom.obj (Opposite.op L, M)) := by
  rw [d.hom_map_comp_right, φ.hom_inv_id]
  exact d.hom.map_id _

/-- **The K-injective-resolution step for the transpose, abstract form.** The transpose at a
target `M` is the transpose at any isomorphic target `M'`, conjugated by the isomorphism. This is
the naturality field `DerivedHomAdjunction.homEquiv_naturality_right` read as a transport: it
transfers a *value* of the transpose from `M'`, where one is known, to `M`, where none is. -/
theorem homEquiv_apply_of_iso {K L M M' : DerivedCategory (ModuleCat.{v} R)} (φ : M ≅ M')
    (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.homEquiv K L M a =
      d.homEquiv K L M' (a ≫ d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L, M') from
        (𝟙 (Opposite.op L), φ.hom))) ≫ φ.inv := by
  rw [d.homEquiv_naturality_right φ.hom a, Category.assoc, φ.hom_inv_id, Category.comp_id]

/-- The inverse transpose at a target `M` is the inverse transpose at any isomorphic target `M'`,
conjugated by the isomorphism. -/
theorem homEquiv_symm_apply_of_iso {K L M M' : DerivedCategory (ModuleCat.{v} R)} (φ : M ≅ M')
    (h : d.tensor.obj (K, L) ⟶ M) :
    (d.homEquiv K L M).symm h =
      (d.homEquiv K L M').symm (h ≫ φ.hom) ≫
        d.hom.map (show (Opposite.op L, M') ⟶ (Opposite.op L, M) from
          (𝟙 (Opposite.op L), φ.inv)) := by
  have hnat := d.homEquiv_naturality_right (K := K) (L := L) (M := M) (M' := M') φ.hom
    ((d.homEquiv K L M).symm h)
  rw [AddEquiv.apply_symm_apply] at hnat
  rw [← hnat, AddEquiv.symm_apply_apply, Category.assoc,
    d.hom_map_right_comp_hom_map_right_inv, Category.comp_id]

end TargetIso

end DerivedHomAdjunction

attribute [local instance] HasDerivedCategory.standard

section Model

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- A complex whose localization is isomorphic to that of the chosen complex representing the
scalar-restricted inverse image of `Y` has a transport isomorphic to `Y`. -/
private theorem nonempty_iso_of_Q_iso (Y : DerivedCategory (ModuleCat.{max u v} R))
    {P : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj Y))) :
    Nonempty ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj P) ≅ Y) :=
  ⟨(derivedScalarEquivalence.{u, v, w} R).functor.mapIso
    (e ≪≫ DerivedCategory.Q.objObjPreimageIso
      ((derivedScalarEquivalence.{u, v, w} R).inverse.obj Y)) ≪≫
    (derivedScalarEquivalence.{u, v, w} R).counitIso.app Y⟩

/-- **Stacks 079P in an arbitrary admissible module universe.** Every object of `D(R)` is
isomorphic to the restriction-of-scalars transport of `DerivedCategory.Q` of a K-injective
cochain complex of `ULift R`-modules. This is the input to
`derivedHomAdjunctionOverRing_homEquiv_apply_of_resolution`: it is what makes the resolution step
unconditional. -/
theorem exists_isKInjective_model (Z : DerivedCategory (ModuleCat.{max u v} R)) :
    ∃ I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ, I.IsKInjective ∧
      Nonempty ((derivedScalarEquivalence.{u, v, w} R).functor.obj
        (DerivedCategory.Q.obj I) ≅ Z) := by
  obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage ((derivedScalarEquivalence.{u, v, w} R).inverse.obj Z))
  have := hf
  exact ⟨I, hI, nonempty_iso_of_Q_iso.{u, v, w} R Z (asIso (DerivedCategory.Q.map f)).symm⟩

/-- **Stacks 06Y4 in an arbitrary admissible module universe.** Every object of `D(R)` is
isomorphic to the restriction-of-scalars transport of `DerivedCategory.Q` of a **K-flat** cochain
complex of `ULift R`-modules. This supplies the hypothesis `hL : L.KFlat` of
`derivedTensorModelIso` at an arbitrary second argument of the transpose. -/
theorem exists_kFlat_model (Y : DerivedCategory (ModuleCat.{max u v} R)) :
    ∃ L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ, L.KFlat ∧
      Nonempty ((derivedScalarEquivalence.{u, v, w} R).functor.obj
        (DerivedCategory.Q.obj L) ≅ Y) := by
  obtain ⟨L, p, hL, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{max u v, max u v}
    (DerivedCategory.Q.objPreimage ((derivedScalarEquivalence.{u, v, w} R).inverse.obj Y))
  have := hp
  exact ⟨L, hL, nonempty_iso_of_Q_iso.{u, v, w} R Y (asIso (DerivedCategory.Q.map p))⟩

end Model

open CochainComplex HomComplex in
/-- **Chain-level transpose for Stacks 0A63 at an arbitrary target.** The hypothesis
`[I.IsKInjective]` of `derivedHomAdjunctionOverRing_homEquiv_apply` constrains the *target* of the
transpose, which in a consumer is typically a derived tensor product and never K-injective. Given
a K-injective resolution `φ` of the target `Z` — which always exists, by
`exists_isKInjective_model` — the value is obtained by transporting along `φ`: the transpose of
the localized chain map `Φ_{K,L}` of Stacks 0A62 followed by postcomposition with `h` and then by
`φ` is `h` itself, read through `derivedTensorModelIso` and then `φ`.

No K-injectivity is asserted of `Z`. -/
theorem derivedHomAdjunctionOverRing_homEquiv_apply_of_resolution {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat)
    [I.IsKInjective] (h : K ⊗ L ⟶ I)
    (Z : DerivedCategory (ModuleCat.{max u v} R))
    (φ : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I) ≅ Z) :
    (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)) Z
        ((derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map
              (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
                Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h)) ≫
            (derivedHomModelIso.{u, v, w} R L I).inv ≫
          (derivedHomAdjunctionOverRing.{u, v, w} R).hom.map
            (show (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L)),
                (derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj I)) ⟶
              (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L)), Z) from
              (𝟙 (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L))), φ.hom))) =
      (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) ≫ φ.hom := by
  rw [← Category.assoc ((derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map
        (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
          Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h))),
    (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv_naturality_right φ.hom,
    derivedHomAdjunctionOverRing_homEquiv_apply.{u, v, w} K L I hL h, Category.assoc]

open CochainComplex HomComplex in
/-- The inverse reading of `derivedHomAdjunctionOverRing_homEquiv_apply_of_resolution`: at a
target `Z` with a chosen K-injective resolution `φ`, the inverse transpose of a morphism
presented through `φ` is the localized chain-level transpose, read through `derivedHomModelIso`
and `φ`. -/
theorem derivedHomAdjunctionOverRing_homEquiv_symm_apply_of_resolution {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat)
    [I.IsKInjective] (h : K ⊗ L ⟶ I)
    (Z : DerivedCategory (ModuleCat.{max u v} R))
    (φ : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I) ≅ Z) :
    ((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)) Z).symm
        ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) ≫
            φ.hom) =
      (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map
            (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} R) K L ≫
              Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} R) L (K ⊗ L) I h)) ≫
          (derivedHomModelIso.{u, v, w} R L I).inv ≫
        (derivedHomAdjunctionOverRing.{u, v, w} R).hom.map
          (show (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                (DerivedCategory.Q.obj L)),
              (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I)) ⟶
            (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                (DerivedCategory.Q.obj L)), Z) from
            (𝟙 (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                (DerivedCategory.Q.obj L))), φ.hom)) :=
  (AddEquiv.symm_apply_eq _).mpr
    (derivedHomAdjunctionOverRing_homEquiv_apply_of_resolution.{u, v, w} K L I hL h Z φ).symm

/-- Every morphism of the derived category into the localization of a K-injective complex is the
localization of a map of complexes. This is K-injectivity in the form
`CochainComplex.IsKInjective.Qh_map_bijective`, read down from the homotopy category through
`DerivedCategory.quotientCompQhIso`. -/
theorem exists_eq_Q_map_of_isKInjective {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory.{w} C]
    (A I : CochainComplex C ℤ) [I.IsKInjective]
    (g : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :
    ∃ f : A ⟶ I, DerivedCategory.Q.map f = g := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let qiso := DerivedCategory.quotientCompQhIso C
  obtain ⟨g', hg'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj A) I).2
    (qiso.hom.app A ≫ g ≫ qiso.inv.app I)
  obtain ⟨f, rfl⟩ := q.map_surjective g'
  refine ⟨f, (cancel_epi (qiso.hom.app A)).1 ?_⟩
  rw [← qiso.hom.naturality f]
  change DerivedCategory.Qh.map (q.map f) ≫ qiso.hom.app I = _
  rw [hg']
  simp

open CochainComplex HomComplex in
/-- **The unconditional chain-level value of the transpose of Stacks 0A63.** At a K-flat second
argument `L`, the transpose of *any* morphism `a`, into the derived Hom object at *any* target
`Z`, is the localization of a map of complexes `h : K ⊗ L ⟶ I` into a K-injective resolution `I`
of `Z`, read through the K-flat tensor model `derivedTensorModelIso` and the resolution.

Neither K-injectivity of `Z` nor any model description of `a` is assumed: the existence of the
resolution is `exists_isKInjective_model`, the existence of `h` is
`exists_eq_Q_map_of_isKInjective` together with fullness of the scalar equivalence, and the value
is then the one computed by `derivedHomAdjunctionOverRing_homEquiv_apply_of_resolution`. -/
theorem derivedHomAdjunctionOverRing_homEquiv_eq_model {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat)
    (Z : DerivedCategory (ModuleCat.{max u v} R))
    (a : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K) ⟶
      (derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj
        (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
          (DerivedCategory.Q.obj L)), Z)) :
    ∃ (I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
      (_ : I.IsKInjective)
      (φ : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I) ≅ Z)
      (h : K ⊗ L ⟶ I),
      (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
          ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
          ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)) Z a =
        (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) ≫
            φ.hom := by
  obtain ⟨I, hI, ⟨φ⟩⟩ := exists_isKInjective_model.{u, v, w} R Z
  have := hI
  obtain ⟨ψ, hψ⟩ := (derivedScalarEquivalence.{u, v, w} R).functor.map_surjective
    ((derivedTensorModelIso.{u, v, w} R K L hL).inv ≫
      (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L)) Z a ≫
      φ.inv)
  obtain ⟨h, rfl⟩ := exists_eq_Q_map_of_isKInjective (K ⊗ L) I ψ
  refine ⟨I, hI, φ, h, ?_⟩
  rw [hψ, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Category.assoc, φ.inv_hom_id, Category.comp_id]

open CochainComplex HomComplex in
/-- **The chain-level value of the transpose of Stacks 0A63 at completely arbitrary arguments.**
For any three objects `X`, `Y`, `Z` of `D(R)` and any morphism `a : X ⟶ RHom(Y, Z)`, the
transpose of `a` is the localization of a map of complexes `h : K ⊗ L ⟶ I`, where `K` and `L` are
K-flat models of `X` and `Y` and `I` is a K-injective model of `Z`, read through the K-flat
tensor model `derivedTensorModelIso` and the three model isomorphisms.

The equation is stated with the tensor bifunctor applied to the two model isomorphisms on the
left, rather than with its inverse on the right; the left factor is an isomorphism, so this
determines the transpose.

No hypothesis is placed on `X`, `Y`, `Z` or `a`: the models come from `exists_kFlat_model` and
`exists_isKInjective_model`, the three-variable transport is
`DerivedHomAdjunction.homEquiv_comp_hom_map`, and the value at the models is
`derivedHomAdjunctionOverRing_homEquiv_eq_model`. This is the statement that the transpose of
[stacks 0A63] has a chain-level value everywhere, not only at a K-flat second argument and a
K-injective target. -/
theorem derivedHomAdjunctionOverRing_homEquiv_eq_model_general {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (X Y Z : DerivedCategory (ModuleCat.{max u v} R))
    (a : X ⟶ (derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj (Opposite.op Y, Z)) :
    ∃ (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hL : L.KFlat)
      (α : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K) ≅ X)
      (β : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L) ≅ Y)
      (φ : (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I) ≅ Z)
      (h : K ⊗ L ⟶ I),
      (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.map
            (show ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K),
                (derivedScalarEquivalence.{u, v, w} R).functor.obj
                  (DerivedCategory.Q.obj L)) ⟶ (X, Y) from (α.hom, β.hom)) ≫
          (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv X Y Z a =
        (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) ≫
            φ.hom := by
  obtain ⟨K, -, ⟨α⟩⟩ := exists_kFlat_model.{u, v, w} R X
  obtain ⟨L, hL, ⟨β⟩⟩ := exists_kFlat_model.{u, v, w} R Y
  obtain ⟨I, hI, φ, h, hval⟩ := derivedHomAdjunctionOverRing_homEquiv_eq_model.{u, v, w} K L hL Z
    (α.hom ≫ a ≫ (derivedHomAdjunctionOverRing.{u, v, w} R).hom.map
      (show (Opposite.op Y, Z) ⟶
          (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
            (DerivedCategory.Q.obj L)), Z) from (β.hom.op, 𝟙 Z)))
  refine ⟨K, L, I, hL, α, β, φ, h, ?_⟩
  have hnat := (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv_comp_hom_map
    (K := X) (L := Y) (M := Z)
    (K' := (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
    (L' := (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
    (M' := Z) α.hom β.hom (𝟙 Z) a
  rw [Category.comp_id] at hnat
  exact hnat.symm.trans hval

/-- **The resolution step in consumer form.** A consumer holding an arbitrary morphism `a` into
the derived Hom object at a target `Z` — with no model description of `a`, and no K-injectivity
for `Z` — may replace the transpose at `Z` by the transpose at a K-injective resolution of `Z`,
where `derivedHomAdjunctionOverRing_homEquiv_apply` applies. The two targets differ by the
resolution isomorphism only.

This is `DerivedHomAdjunction.homEquiv_apply_of_iso` at the canonical adjunction; it is recorded
separately because it is the shape in which the reduction is used. -/
theorem derivedHomAdjunctionOverRing_homEquiv_apply_eq_of_resolution {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (X Y Z W : DerivedCategory (ModuleCat.{max u v} R)) (φ : Z ≅ W)
    (a : X ⟶ (derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj (Opposite.op Y, Z)) :
    (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv X Y Z a =
      (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv X Y W
          (a ≫ (derivedHomAdjunctionOverRing.{u, v, w} R).hom.map
            (show (Opposite.op Y, Z) ⟶ (Opposite.op Y, W) from (𝟙 (Opposite.op Y), φ.hom))) ≫
        φ.inv :=
  (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv_apply_of_iso φ a

end StacksDraft.DerivedHom

end
