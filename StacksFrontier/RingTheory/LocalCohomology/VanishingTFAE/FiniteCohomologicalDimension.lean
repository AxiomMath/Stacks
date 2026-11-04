module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.RingTheory.Dualizing.Ext
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor

/-!
# Local cohomology has finite cohomological dimension

Let `I` be a finitely generated ideal of a commutative ring `A`, with `Z = V(I)`, and let
`RΓ_Z : D(A) ⥤ D_{I^∞-torsion}(A)` be local cohomology, the right adjoint of Stacks 0A6R. This
file proves that `RΓ_Z` raises cohomological degree by at most the number of generators of `I`:
if the cohomology of `K` vanishes in degrees above `n`, then the cohomology of `RΓ_Z(K)`
vanishes in degrees above `n + r`, where `r` is the size of a chosen finite generating set.

The adjoint is produced in
`StacksFrontier/RingTheory/Dualizing/PowerTorsionComparison/LocalCohomologyFunctor.lean` from the
coreflection of `D(A)` onto the objects killed by the derived localizations at a finite
generating set `f₁, …, f_r` of `I`, and that coreflection is built by iterating the fibre of
the localization unit `K ⟶ K[1/f_j]`. Each such fibre sits in a distinguished triangle whose
other two objects are `K` and `K[1/f_j]`, so it raises the cohomological bound by exactly one;
after `r` steps the bound has risen by `r`. The adjoint itself is defined by an application of
`Classical.choice`, so the bound is transported to it through the uniqueness of a coreflection:
an object with the universal property of `RΓ_Z(K)` is canonically isomorphic to it.

## Main results

* `Stacks.LocalCohomology.isZero_homology_obj₁_of_isZero` — a distinguished triangle raises a
  cohomological vanishing bound on its second and third objects to a bound one higher on its
  first object.
* `Stacks.LocalCohomology.exists_coreflection_isZero_homology` — the coreflection onto the
  objects killed by a finite family of idempotent exact localizations, with its cohomology
  bounded by the size of the family.
* `Stacks.LocalCohomology.nonempty_localCohomology_iso_coreflection` — uniqueness of the
  coreflection: anything with its universal property is isomorphic to `RΓ_Z(K)`.
* `Stacks.LocalCohomology.isZero_homology_localCohomologyFunctor` — the cohomological
  dimension bound for `RΓ_Z`.
* `Stacks.LocalCohomology.exists_isZero_homology_localCohomologyFunctor_singleFunctor` — the
  resulting bound for a module placed in degree zero, in the form used to define the
  cohomological dimension of an ideal.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

section Coreflection

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle, a cohomological vanishing bound `m` for the second and the
third object gives the bound `m + 1` for the first object. -/
theorem isZero_homology_obj₁_of_isZero (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (m : ℤ)
    (h₂ : ∀ j, m < j → IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₂))
    (h₃ : ∀ j, m < j → IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₃))
    (j : ℤ) (hj : m + 1 < j) :
    IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₁) :=
  (DerivedCategory.HomologySequence.exact₁ T hT (j - 1) j (by omega)).isZero_of_both_isZero
    (h₃ (j - 1) (by omega)) (h₂ j (by omega))

/-- Iterating the fibre of the localization unit over a finite family of idempotent exact
localizations `F i` produces the coreflection of `X` onto the objects killed by all of them,
and raises a cohomological vanishing bound on `X` by at most the size of the family.

This is the construction behind `Dualizing.localCohomologyRightAdjoint`, carrying in addition
the cohomological bound that the triangles of the construction provide. -/
theorem exists_coreflection_isZero_homology {ι : Type*}
    (F : ι → DerivedCategory C ⥤ DerivedCategory C)
    [∀ i, (F i).Additive] [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    (η : ∀ i, 𝟭 (DerivedCategory C) ⟶ F i)
    (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) → IsZero ((F j).obj ((F i).obj X)))
    (hbd : ∀ (i : ι) (X : DerivedCategory C) (m : ℤ),
      (∀ j, m < j → IsZero ((DerivedCategory.homologyFunctor C j).obj X)) →
        ∀ j, m < j → IsZero ((DerivedCategory.homologyFunctor C j).obj ((F i).obj X)))
    (s : Finset ι) (X : DerivedCategory C) (n : ℤ)
    (hX : ∀ j, n < j → IsZero ((DerivedCategory.homologyFunctor C j).obj X)) :
    ∃ (Y : DerivedCategory C) (a : Y ⟶ X), (∀ i ∈ s, IsZero ((F i).obj Y)) ∧
      (∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) ∧
      ∀ j, n + s.card < j → IsZero ((DerivedCategory.homologyFunctor C j).obj Y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨X, 𝟙 X, by simp, ?_, ?_⟩
    · intro W _
      exact ⟨fun _ _ h => by simpa only [Category.comp_id] using h,
        fun g => ⟨g, Category.comp_id g⟩⟩
    · simpa using hX
  | @insert i s hi ih =>
    obtain ⟨U, b, hU, hb, hUbd⟩ := ih
    obtain ⟨T, hT, h₂, h₃, hFT, ha, -⟩ :=
      Dualizing.PowerTorsionBaseChange.exists_fiber_localization
        (F i) (η i) (hη i) (hFη i) (F i) (fun Z => hη i ((F i).obj Z)) U
    let e : T.obj₂ ≅ U := eqToIso h₂
    refine ⟨T.obj₁, T.mor₁ ≫ e.hom ≫ b, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hFT
      · apply Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
        · exact (hU j hj).of_iso ((F j).mapIso e)
        · rw [show ((F j).mapTriangle.obj T).obj₃ = (F j).obj T.obj₃ from rfl, h₃]
          exact hpres i j U (hU j hj)
    · intro W hW
      have h₁ := ha W (hW i (Finset.mem_insert_self _ _))
      have h₂' : Function.Bijective (fun g : W ⟶ T.obj₂ => g ≫ e.hom) :=
        ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun g => ⟨g ≫ e.inv, by simp⟩⟩
      have h₃' := hb W (fun j hj => hW j (Finset.mem_insert_of_mem hj))
      simpa only [Function.comp_def, Category.assoc] using h₃'.comp (h₂'.comp h₁)
    · intro j hj
      refine isZero_homology_obj₁_of_isZero T hT (n + s.card) (fun k hk => ?_)
        (fun k hk => ?_) j ?_
      · exact (hUbd k hk).of_iso ((DerivedCategory.homologyFunctor C k).mapIso e)
      · refine (hbd i U (n + s.card) hUbd k hk).of_iso ?_
        exact (DerivedCategory.homologyFunctor C k).mapIso (eqToIso h₃)
      · rw [Finset.card_insert_of_notMem hi] at hj
        push_cast at hj
        omega

end Coreflection

section Identification

/-- Two objects that are both universal among morphisms to `X` out of a given class of objects,
and both belong to that class, are isomorphic over `X`. -/
theorem nonempty_iso_of_coreflection {D : Type*} [Category D]
    (Q : ObjectProperty D) {X Y Y' : D} (hY : Q Y) (hY' : Q Y')
    (a : Y ⟶ X) (a' : Y' ⟶ X)
    (hb : ∀ W, Q W → Function.Bijective (fun g : W ⟶ Y => g ≫ a))
    (hb' : ∀ W, Q W → Function.Bijective (fun g : W ⟶ Y' => g ≫ a')) :
    Nonempty (Y' ≅ Y) := by
  obtain ⟨α, hα⟩ := (hb' Y hY).surjective a
  obtain ⟨β, hβ⟩ := (hb Y' hY').surjective a'
  dsimp only at hα hβ
  refine ⟨⟨β, α, ?_, ?_⟩⟩
  · exact (hb' Y' hY').injective (by rw [Category.assoc, hα, hβ, Category.id_comp])
  · exact (hb Y hY).injective (by rw [Category.assoc, hβ, hα, Category.id_comp])

/-- **Uniqueness of a coreflection, for a given morphism.** A morphism between two objects of a
class `Q` commuting with two morphisms to `X`, each universal among morphisms to `X` out of `Q`,
is an isomorphism. -/
theorem isIso_of_coreflection {D : Type*} [Category D]
    (Q : ObjectProperty D) {X Y Y' : D} (hY : Q Y) (hY' : Q Y')
    (a : Y ⟶ X) (a' : Y' ⟶ X) (φ : Y ⟶ Y') (hφ : φ ≫ a' = a)
    (hb : ∀ W, Q W → Function.Bijective (fun g : W ⟶ Y => g ≫ a))
    (hb' : ∀ W, Q W → Function.Bijective (fun g : W ⟶ Y' => g ≫ a')) :
    IsIso φ := by
  obtain ⟨ψ, hψ⟩ := (hb Y' hY').surjective a'
  have hψ' : ψ ≫ a = a' := hψ
  refine ⟨ψ, (hb Y hY).injective ?_, (hb' Y' hY').injective ?_⟩
  · show (φ ≫ ψ) ≫ a = 𝟙 Y ≫ a
    rw [Category.assoc, hψ', hφ, Category.id_comp]
  · show (ψ ≫ φ) ≫ a' = 𝟙 Y' ≫ a'
    rw [Category.assoc, hφ, hψ', Category.id_comp]

variable {A : Type u} [CommRing A]

/-- Morphisms into `RΓ_{V(I)}(X)` from objects with `I`-power-torsion cohomology correspond
bijectively to morphisms into `X`, by composition with the counit. -/
private theorem bijective_comp_counit_localCohomology (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{max v u} A)) :
    ∀ W : DerivedCategory (ModuleCat.{max v u} A),
      Dualizing.derivedPowerTorsionProperty A I hI W →
      Function.Bijective (fun h : W ⟶ (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj X) =>
          h ≫ (Dualizing.localCohomologyAdjunction A I hI).counit.app X) := by
  intro W hW
  set P := Dualizing.derivedPowerTorsionProperty A I hI with hP
  set adj := Dualizing.localCohomologyAdjunction A I hI with hadj
  have hcomp : Function.Bijective
      (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ (Dualizing.localCohomologyFunctor A I hI).obj X =>
        P.ι.map g ≫ adj.counit.app X) := by
    have : (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶
        (Dualizing.localCohomologyFunctor A I hI).obj X => P.ι.map g ≫ adj.counit.app X) =
        (adj.homEquiv ⟨W, hW⟩ X).symm := by
      funext g
      exact (adj.homEquiv_counit _ _ g).symm
    rw [this]
    exact (adj.homEquiv ⟨W, hW⟩ X).symm.bijective
  exact (P.fullyFaithfulι.homEquiv.bijective.of_comp_iff _).mp hcomp

/-- **Uniqueness of the coreflection.** If `Y` has `I`-power-torsion cohomology and `a : Y ⟶ X`
is universal among maps to `X` from objects with `I`-power-torsion cohomology, then `Y` is
isomorphic to the value `RΓ_{V(I)}(X)` of local cohomology, viewed in `D(A)`. -/
theorem nonempty_localCohomology_iso_coreflection
    (I : Ideal A) (hI : I.FG) {X Y : DerivedCategory (ModuleCat.{max v u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty A I hI Y) (a : Y ⟶ X)
    (hb : ∀ W : DerivedCategory (ModuleCat.{max v u} A),
      Dualizing.derivedPowerTorsionProperty A I hI W →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) :
    Nonempty ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj X) ≅ Y) := by
  exact nonempty_iso_of_coreflection _ hY ((Dualizing.localCohomologyFunctor A I hI).obj X).property
    a _ hb (bijective_comp_counit_localCohomology I hI X)

/-- **The canonical morphism to local cohomology.** The transpose along the local-cohomology
adjunction of a morphism `a : Y ⟶ X` out of an object with `I`-power-torsion cohomology; it is
built from the adjunction and uses no choice. -/
def coreflectionToLocalCohomology (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{max v u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty A I hI Y) (a : Y ⟶ X) :
    Y ⟶ (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj X) :=
  (Dualizing.derivedPowerTorsionProperty A I hI).ι.map
    ((Dualizing.localCohomologyAdjunction A I hI).homEquiv ⟨Y, hY⟩ X a)

/-- The canonical morphism to local cohomology lifts `a` along the counit. -/
theorem coreflectionToLocalCohomology_comp_counit (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{max v u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty A I hI Y) (a : Y ⟶ X) :
    coreflectionToLocalCohomology I hI hY a ≫
        (Dualizing.localCohomologyAdjunction A I hI).counit.app X = a := by
  have h := ((Dualizing.localCohomologyAdjunction A I hI).homEquiv
    ⟨Y, hY⟩ X).symm_apply_apply a
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- **Uniqueness of the coreflection, as an isomorphism of a specific morphism.** If `a` is
universal among morphisms to `X` from objects with `I`-power-torsion cohomology, its transpose
is an isomorphism. -/
theorem isIso_coreflectionToLocalCohomology (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{max v u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty A I hI Y) (a : Y ⟶ X)
    (hb : ∀ W : DerivedCategory (ModuleCat.{max v u} A),
      Dualizing.derivedPowerTorsionProperty A I hI W →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) :
    IsIso (coreflectionToLocalCohomology I hI hY a) := by
  exact isIso_of_coreflection _ hY
    ((Dualizing.localCohomologyFunctor A I hI).obj X).property a _
    (coreflectionToLocalCohomology I hI hY a)
    (coreflectionToLocalCohomology_comp_counit I hI hY a) hb
    (bijective_comp_counit_localCohomology I hI X)

/-- **Uniqueness of the coreflection, as a named isomorphism.** The choice-free form of
`Stacks.LocalCohomology.nonempty_localCohomology_iso_coreflection`: the isomorphism is the
transpose of `a` along the adjunction, so it carries a map rather than only its existence. -/
def coreflectionIsoLocalCohomology (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{max v u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty A I hI Y) (a : Y ⟶ X)
    (hb : ∀ W : DerivedCategory (ModuleCat.{max v u} A),
      Dualizing.derivedPowerTorsionProperty A I hI W →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) :
    Y ≅ (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj X) :=
  @asIso _ _ _ _ (coreflectionToLocalCohomology I hI hY a)
    (isIso_coreflectionToLocalCohomology I hI hY a hb)

/-- The named coreflection isomorphism, in the direction of
`Stacks.LocalCohomology.nonempty_localCohomology_iso_coreflection`. -/
def localCohomologyIsoCoreflection (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{max v u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty A I hI Y) (a : Y ⟶ X)
    (hb : ∀ W : DerivedCategory (ModuleCat.{max v u} A),
      Dualizing.derivedPowerTorsionProperty A I hI W →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a)) :
    (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj X) ≅ Y :=
  (coreflectionIsoLocalCohomology I hI hY a hb).symm

/-- **Finite cohomological dimension of `RΓ_{V(I)}`.** If the cohomology of `X` vanishes in
degrees above `n`, then the cohomology of `RΓ_{V(I)}(X)` vanishes in degrees above
`n + r`, where `r` is the size of a finite generating set of `I`. -/
theorem isZero_homology_localCohomologyFunctor
    (I : Ideal A) (hI : I.FG) (s : Finset A) (hs : Ideal.span (s : Set A) = I)
    (X : DerivedCategory (ModuleCat.{max v u} A)) (n : ℤ)
    (hX : ∀ j, n < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X))
    (j : ℤ) (hj : n + s.card < j) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj
      ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj X))) := by
  obtain ⟨Y, a, hYloc, hbY, hYbd⟩ :=
    exists_coreflection_isZero_homology
      (fun f : A => Dualizing.PowerTorsionBaseChange.locDerived.{v} f)
      (fun f : A => Dualizing.PowerTorsionBaseChange.locDerivedUnit.{v} f)
      (fun f => Dualizing.PowerTorsionBaseChange.isIso_locDerivedUnit_locDerived f)
      (fun f => Dualizing.PowerTorsionBaseChange.isIso_locDerived_map_locDerivedUnit f)
      (fun f g W h => Dualizing.PowerTorsionBaseChange.locDerived_isZero_locDerived g f W h)
      (fun f W m hW k hk => ((Dualizing.PowerTorsionBaseChange.locFunctor.{v} f).map_isZero
        (hW k hk)).of_iso
          ((Dualizing.mapDerivedCategoryHomologyIso
            (Dualizing.PowerTorsionBaseChange.locFunctor.{v} f) k).app W))
      s X n hX
  have hY : Dualizing.derivedPowerTorsionProperty A I hI Y :=
    (Dualizing.PowerTorsionBaseChange.derivedPowerTorsion_iff_locDerived_isZero
      I hI s hs Y).mpr hYloc
  obtain ⟨e⟩ := nonempty_localCohomology_iso_coreflection I hI hY a
    (fun W hW => hbY W
      ((Dualizing.PowerTorsionBaseChange.derivedPowerTorsion_iff_locDerived_isZero
        I hI s hs W).mp hW))
  exact (hYbd j hj).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).mapIso e)

section FreeModuleUniverse

universe w

/-- A module placed in degree zero has no cohomology outside degree zero.

The module universe `w` is unrelated to the universe of `A`: the statement is about the single
complex of an object of an arbitrary abelian category, and `ModuleCat.{w} A` is one for every `w`.
The rest of this file fixes the module universe at `max v u` because the local-cohomology functor
it uses is only available there, but nothing of that reaches this lemma. -/
theorem isZero_homology_singleFunctor_obj (M : ModuleCat.{w} A) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) j).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M)) :=
  IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M j hj)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} A) j).app _)

end FreeModuleUniverse

/-- **Stacks 0DX9, first part.** The local cohomology of a module supported on `V(I)` vanishes
in degrees above the number of generators of `I`; in particular some integer `d ≥ -1` is a
vanishing bound for it. -/
theorem exists_isZero_homology_localCohomologyFunctor_singleFunctor
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max v u} A) :
    ∃ d : ℤ, (-1 : ℤ) ≤ d ∧ ∀ i : ℤ, d < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M)))) := by
  obtain ⟨s, hs⟩ := id hI
  refine ⟨(s.card : ℤ), by omega, fun i hi => ?_⟩
  refine isZero_homology_localCohomologyFunctor I hI s hs _ 0 (fun j hj => ?_) i (by omega)
  exact isZero_homology_singleFunctor_obj M j (by omega)

end Identification

end Stacks.LocalCohomology
