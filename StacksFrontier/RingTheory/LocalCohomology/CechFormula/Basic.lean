module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.BoundedFunctor
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.CechFlat
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Coreflection
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic

/-!
# Local cohomology as a derived tensor product with the Čech complex

Let `A` be a commutative ring, let `I = (f₁, …, f_r)` be a finitely generated ideal and let
`Z = V(I)`. Local cohomology `RΓ_Z` is defined as the right adjoint of the inclusion of the
complexes with `I`-power-torsion cohomology, so a priori its values are only accessible through
that universal property. Stacks 0A6R gives the formula

$$ RΓ_Z(K) \;=\; \bigl(A \to \textstyle\prod_i A_{f_i} \to \cdots \to A_{f_1 \cdots f_r}\bigr)
   \otimes^{\mathbf L}_A K, $$

*functorially in* `K ∈ D(A)`: the whole functor `RΓ_Z` is derived tensor product with the
extended alternating Čech complex `C(f)`.

This file proves that, as a natural isomorphism normalized by the counit. The strategy is the
uniqueness of a coreflection, in the form `exists_normalized_coreflectionIso`, applied to the
endofunctor `C(f) ⊗^L_A -` and the natural transformation `C(f) ⊗^L_A - ⟶ id` induced by the
Čech augmentation. Its three hypotheses are:

* the Čech tensor product lands in the power-torsion subcategory — the Čech object has
  power-torsion cohomology (Tag 0G6K) and the derived tensor product of a power-torsion object
  with anything is power-torsion, which is `powerTorsion_iff_localizedTensor_isZero` together
  with associativity;
* the augmentation is invertible on power-torsion objects — the Čech complex is bounded, its
  positive-degree terms are killed by tensoring with a power-torsion object, and its degree-zero
  term is the ring, so `isIso_map_to_single` applies;
* and tensoring with `C(f)` inverts the augmentation — the same argument with the roles of the
  two tensor factors exchanged, using that `C(f)` itself is power-torsion.

## Main results

* `Stacks.LocalCohomology.CechFormula.exists_localCohomologyCechIso` — the normalized Čech
  formula: `RΓ_Z ≅ C(f) ⊗^L_A -`, by an isomorphism carrying the Čech augmentation map to the
  adjunction counit.
* `Stacks.LocalCohomology.CechFormula.localCohomologyCechIso` — that isomorphism, selected.
* `Stacks.LocalCohomology.CechFormula.localCohomologyCechIso_comp_augmentation` — its
  normalization.

## Implementation notes

Everything happens at module universe equal to the ring's universe, because that is where the
canonical derived tensor product `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`
and the monoidal structure of `DerivedCategory.Invertible` are available. That is the
library's standard reading of the source's `D(A)` for a ring `A : Type u` — the same one used by
`Dualizing.localCohomologyOfRing` — and the source says nothing about universes, so the
`@[stacks 0A6R]` attribute for the formula half of the tag is placed here, on
`localCohomologyCechIso` and on its normalization. Obtaining the same formula with the module
universe independent of the ring's would need a `DerivedTensorProductGeneral` at a general
module universe together with its monoidal structure, which the library does not have; that is a
Lean-side generalization, not part of the tag. The auxiliary results of `Flatness` and `CechFlat`
are already stated at an independent module universe for an arbitrary
`DerivedTensorProductGeneral`, so only the assembly below is specialized.

The other half of the tag — existence of the right adjoint `RΓ_Z` — is tagged separately, on
`Dualizing.localCohomologyRightAdjoint`, where it is proved with the module universe independent
of the ring's.

The associativity and middle-whiskering steps are stated as standalone lemmas taking the
monoidal structure and its comparison with the canonical derived tensor product as explicit
arguments, since the library supplies them only as an existential statement
(`DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory`).

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology.CechFormula

variable (A : Type u) [CommRing A] {r : ℕ}

/-- The ring placed in degree zero: the unit of the derived tensor product. -/
abbrev unitObject : DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-- **The left unit isomorphism of the canonical derived tensor product.** The structure supplies
only a right unitor; the Koszul braiding converts it into a left one. -/
def derivedTensorLeftUnitor :
    (canonicalDerivedTensorProductFunctor A).obj (unitObject A) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  (derivedTensorProductKoszulBraiding A).iso.app (unitObject A) ≪≫
    (canonicalDerivedTensorProduct A).rightUnitor

/-- The Čech augmentation, with its target identified with the tensor unit. -/
def cechAugmentation (f : Fin r → A) :
    cechRegularObject.{u, u} f ⟶ unitObject A :=
  extendedCechAugmentationHom f (regularModule.{u, u} A) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      (ULift.moduleEquiv (R := A) (M := A)).toModuleIso.hom

/-- **The Čech comparison map.** Tensoring with the Čech complex, followed by the augmentation,
gives a natural transformation `C(f) ⊗^L_A - ⟶ id`. -/
def cechTensorToId (f : Fin r → A) :
    (canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f) ⟶
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  (canonicalDerivedTensorProductFunctor A).map (cechAugmentation A f) ≫
    (derivedTensorLeftUnitor A).hom

section Isos

variable {A}

/-- A natural isomorphism of functors transports invertibility of the image of a morphism. -/
theorem isIso_map_of_natIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (g : X ⟶ Y) (hg : IsIso (G.map g)) : IsIso (F.map g) := by
  have := hg
  have h : IsIso (e.hom.app X ≫ G.map g) := inferInstance
  rw [← e.hom.naturality g] at h
  exact (isIso_comp_right_iff _ _).mp h

end Isos

/-- `cechAugmentation` factors through the derived-category image of the chain-level
augmentation, followed by an isomorphism. -/
theorem cechAugmentation_eq (f : Fin r → A) :
    cechAugmentation A f =
      DerivedCategory.Q.map (extendedCechAugmentation f (regularModule.{u, u} A)) ≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
            (regularModule.{u, u} A)).inv ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
            (ULift.moduleEquiv (R := A) (M := A)).toModuleIso.hom) := by
  rw [cechAugmentation, extendedCechAugmentationHom, Category.assoc]

/-- **A functor killing the positive-degree Čech terms inverts the Čech augmentation.** The Čech
complex is concentrated in the degrees `0, …, r` and is the regular module in degree zero, so
`isIso_map_to_single` reduces invertibility of `F (aug)` to the vanishing of `F` on the
positive-degree terms. -/
theorem isIso_map_cechAugmentation
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    [F.CommShift ℤ] [F.IsTriangulated] (f : Fin r → A)
    (ht : ∀ p : ℕ, 0 < p → ∀ q : ℤ, IsZero (F.obj ((DerivedCategory.singleFunctor _ q).obj
      (ModuleCat.of A (Cech.cechTerm f (ULift.{u} A) p))))) :
    IsIso (F.map (cechAugmentation A f)) := by
  have hmain : IsIso (F.map (DerivedCategory.Q.map
      (extendedCechAugmentation f (regularModule.{u, u} A)))) := by
    refine isIso_map_to_single F (cechRegularComplex.{u, u} f) (regularModule.{u, u} A) 0 0 (r + 1)
      (extendedCechAugmentation f (regularModule.{u, u} A))
      (isIso_extendedCechAugmentation_f_zero f (regularModule.{u, u} A))
      (fun i hi => isZero_extendedCechComplex_X f (regularModule.{u, u} A) i (by
        push_cast at hi ⊢; omega)) (fun i hi q => ?_)
  -- the terms away from degree zero are the positive-degree Čech terms
    by_cases h : 0 ≤ i
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact absurd rfl hi
        · exact hn
      exact (ht n hn q).of_iso (F.mapIso ((DerivedCategory.singleFunctor _ q).mapIso
        (HomologicalComplex.extendXIso (Cech.cechComplex f (regularModule.{u, u} A))
          ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp))))
    · exact F.map_isZero ((DerivedCategory.singleFunctor _ q).map_isZero
        (isZero_extendedCechComplex_X f (regularModule.{u, u} A) i
          (Or.inl (lt_of_not_ge h))))
  rw [cechAugmentation_eq, F.map_comp]
  have htail : IsIso (F.map
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
          (regularModule.{u, u} A)).inv ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ULift.moduleEquiv (R := A) (M := A)).toModuleIso.hom)) := inferInstance
  exact IsIso.comp_isIso' hmain htail

/-- **The Čech comparison is invertible on power-torsion objects.** For `X` with `I`-power-torsion
cohomology, tensoring the positive-degree Čech terms with `X` gives zero, so the functor
`- ⊗^L_A X` inverts the Čech augmentation; the left unitor does the rest. -/
theorem isIso_cechTensorToId_app (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hIf : Ideal.span (Set.range f) = I)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : Dualizing.derivedPowerTorsionProperty A I hI X) :
    IsIso ((cechTensorToId A f).app X) := by
  let T := canonicalDerivedTensorProduct A
  let F := T.tensor.flip.obj X
  have hX' : ∀ i, IsIPowerTorsion A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)
      (Ideal.span (Set.range f)) := by
    rw [hIf]; exact hX
  have hm : IsIso (F.map (cechAugmentation A f)) :=
    isIso_map_cechAugmentation A F f fun p hp q =>
      cechTerm_derivedTensor_isZero T.toGeneral f X hX' p hp q
  change IsIso (F.map (cechAugmentation A f) ≫ (derivedTensorLeftUnitor A).hom.app X)
  exact IsIso.comp_isIso' hm ((derivedTensorLeftUnitor A).app X).isIso_hom

/-- The Čech object of `f` has `(f)`-power-torsion cohomology. -/
private theorem cechRegular_isIPowerTorsion_span (f : Fin r → A) (i : ℤ) :
    IsIPowerTorsion A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (cechRegularObject.{u, u} f))
      (Ideal.span (Set.range f)) :=
  cechRegular_derivedPowerTorsion.{u, u} f (Ideal.span (Set.range f))
    (Submodule.fg_span (Set.finite_range f)) rfl i

/-- **Tensoring with the Čech complex inverts the Čech augmentation.** The Čech object itself has
power-torsion cohomology, so after exchanging the two tensor factors by the Koszul braiding this
is the previous argument applied to the Čech object. -/
theorem isIso_tensorCech_map_cechAugmentation (f : Fin r → A) :
    IsIso ((canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f) |>.map
      (cechAugmentation A f)) := by
  classical
  let T := canonicalDerivedTensorProduct A
  let C := cechRegularObject.{u, u} f
  have hC := cechRegular_isIPowerTorsion_span A f
  refine isIso_map_cechAugmentation A (T.tensor.obj C) f fun p hp q => ?_
  refine (cechTerm_derivedTensor_isZero T.toGeneral f C hC p hp q).of_iso ?_
  exact ((derivedTensorProductKoszulBraiding A).iso.app C).app _

section Monoidal

variable {A}
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
  (t : curriedTensor (DerivedCategory (ModuleCat.{u} A)) ≅
    canonicalDerivedTensorProductFunctor A)

/-- **Associativity of the canonical derived tensor product**, transported from the monoidal
structure across the comparison `t`. -/
def tensorAssocIso (X Y Z : DerivedCategory (ModuleCat.{u} A)) :
    ((canonicalDerivedTensorProductFunctor A).obj
        (((canonicalDerivedTensorProductFunctor A).obj X).obj Y)).obj Z ≅
      ((canonicalDerivedTensorProductFunctor A).obj X).obj
        (((canonicalDerivedTensorProductFunctor A).obj Y).obj Z) :=
  ((t.app _).app _).symm ≪≫
    tensorIso ((t.app X).app Y).symm (Iso.refl Z) ≪≫
    associator X Y Z ≪≫ tensorIso (Iso.refl X) ((t.app Y).app Z) ≪≫
    (t.app X).app _

include t in
/-- **The Čech tensor product is power-torsion.** The Čech object has `I`-power-torsion
cohomology, and by the localization criterion that is the vanishing of its derived tensor
product with each `A_{f_j}`; associativity moves `A_{f_j}` next to the Čech object, so the
tensor product with any `X` inherits the vanishing. -/
theorem derivedPowerTorsion_cechTensor (f : Fin r → A)
    (X : DerivedCategory (ModuleCat.{u} A)) (q : ℤ) :
    IsIPowerTorsion A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        (((canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f)).obj X))
      (Ideal.span (Set.range f)) := by
  classical
  let T := (canonicalDerivedTensorProduct A).toGeneral
  let C := cechRegularObject.{u, u} f
  have hC := cechRegular_isIPowerTorsion_span A f
  revert q
  refine (powerTorsion_iff_localizedTensor_isZero T f _).2 fun j => ?_
  have hz := (powerTorsion_iff_localizedTensor_isZero T f C).1 hC j
  exact ((canonicalDerivedTensorProductFunctor A).flip.obj X).map_isZero hz |>.of_iso
    (tensorAssocIso t _ C X).symm

include t in
/-- **Tensoring with the Čech complex inverts every component of the Čech comparison.** The
middle-whiskering identity of the associator reduces this to invertibility of the Čech
augmentation after tensoring with the Čech complex. -/
theorem isIso_tensorCech_map_app (f : Fin r → A)
    (h : IsIso (((canonicalDerivedTensorProductFunctor A).obj
      (cechRegularObject.{u, u} f)).map (cechAugmentation A f)))
    (X : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (((canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f)).map
      (((canonicalDerivedTensorProductFunctor A).map (cechAugmentation A f)).app X)) := by
  let Tf := canonicalDerivedTensorProductFunctor A
  let C := cechRegularObject.{u, u} f
  let a := cechAugmentation A f
  let eR : tensorRight X ≅ Tf.flip.obj X :=
    NatIso.ofComponents (fun Y => (t.app Y).app X)
      (fun g => NatTrans.congr_app (t.hom.naturality g) X)
  have hwl : IsIso (C ◁ a) := isIso_map_of_natIso (t.app C) a h
  have hl : IsIso (C ◁ (a ▷ X)) := by
    have he := associator_naturality_middle C a X
    have hc : IsIso (((C ◁ a) ▷ X) ≫ (associator C (unitObject A) X).hom) := inferInstance
    rw [he] at hc
    exact (isIso_comp_left_iff _ _).mp hc
  have hm : IsIso ((Tf.obj C).map (a ▷ X)) := isIso_map_of_natIso (t.app C).symm (a ▷ X) hl
  exact isIso_map_of_natIso (Functor.isoWhiskerRight eR (Tf.obj C)).symm a hm

end Monoidal

/-- **The Čech formula for local cohomology, Stacks 0A6R.** For a finitely generated ideal
`I = (f₁, …, f_r)` of `A`, local cohomology with support in `V(I)` is, as a functor on `D(A)`,
the derived tensor product with the extended alternating Čech complex of `f`; and the
isomorphism may be chosen to carry the Čech comparison map to the counit of the adjunction
defining local cohomology.

This is the functorial statement of the tag, at module universe equal to the ring's. The
`@[stacks 0A6R]` attribute sits on `localCohomologyCechIso` and
`localCohomologyCechIso_comp_augmentation`, the chosen isomorphism and its normalization, which
together are this statement. -/
theorem exists_localCohomologyCechIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    ∃ e : Dualizing.localCohomologyFunctor A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι ≅
      (canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f),
      e.hom ≫ cechTensorToId A f = (Dualizing.localCohomologyAdjunction A I hI).counit := by
  obtain ⟨m, s, t, -⟩ :=
    DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A
  let := m
  let := s
  have haug : IsIso (((canonicalDerivedTensorProductFunctor A).obj
      (cechRegularObject.{u, u} f)).map (cechAugmentation A f)) :=
    isIso_tensorCech_map_cechAugmentation A f
  refine exists_normalized_coreflectionIso _ _ (Dualizing.localCohomologyAdjunction A I hI)
    _ (cechTensorToId A f) (fun X i => ?_) (fun Y hY => ?_) (fun X => ?_)
  · rw [← hf]
    exact derivedPowerTorsion_cechTensor (A := A) t f X i
  · exact isIso_cechTensorToId_app A f I hI hf Y hY
  · change IsIso (((canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f)).map
      (((canonicalDerivedTensorProductFunctor A).map (cechAugmentation A f)).app X ≫
        (derivedTensorLeftUnitor A).hom.app X))
    rw [Functor.map_comp]
    have h₁ := isIso_tensorCech_map_app (A := A) t f haug X
    exact IsIso.comp_isIso' h₁ (((canonicalDerivedTensorProductFunctor A).obj
      (cechRegularObject.{u, u} f)).mapIso ((derivedTensorLeftUnitor A).app X)).isIso_hom

/-- **Stacks 0A6R, the Čech formula.** For a finitely generated ideal `I = (f₁, …, f_r)` of `A`,
local cohomology `RΓ_Z` with `Z = V(I)` is, as a functor on `D(A)`, the derived tensor product
with the extended alternating Čech complex of `f`. Normalized by
`localCohomologyCechIso_comp_augmentation`. -/
@[stacks 0A6R "the Čech formula, functorially in K ∈ D(A); module universe = ring universe"]
def localCohomologyCechIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    Dualizing.localCohomologyFunctor A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι ≅
      (canonicalDerivedTensorProductFunctor A).obj (cechRegularObject.{u, u} f) :=
  Classical.choose (p := fun e => e.hom ≫ cechTensorToId A f =
      (Dualizing.localCohomologyAdjunction A I hI).counit)
    (exists_localCohomologyCechIso A I hI f hf)

/-- **Stacks 0A6R, the normalization of the Čech formula.** Composing it with the Čech comparison
map gives the counit of the adjunction that defines local cohomology, which is what makes the
isomorphism of `localCohomologyCechIso` the canonical one. -/
@[stacks 0A6R "normalization of the Čech formula against the local-cohomology counit"]
theorem localCohomologyCechIso_comp_augmentation (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    (localCohomologyCechIso A I hI f hf).hom ≫ cechTensorToId A f =
      (Dualizing.localCohomologyAdjunction A I hI).counit :=
  (exists_localCohomologyCechIso A I hI f hf).choose_spec

end Stacks.LocalCohomology.CechFormula
