module

public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.Commutation
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.Coreflection

/-!
# Base change for local cohomology

Let `A → B` be a homomorphism of commutative rings, let `I ⊆ A` be a finitely generated ideal
and put `J = IB`. Let `Z = V(I) ⊆ Spec(A)` and `Y = V(J) ⊆ Spec(B)`. Then

`RΓ_Z(K) ⊗ᴸ_A B = RΓ_Y(K ⊗ᴸ_A B)`

functorially in `K ∈ D(A)`. No flatness or finiteness hypothesis on `A → B` is needed.

## Main definitions

* `Stacks.LocalCohomology.coreflectionBaseChange` — for two coreflective subcategories and a
  functor carrying the one coreflection to the other, the canonical comparison of the two
  coreflections.
* `Stacks.LocalCohomology.coreflectionBaseChangeIso` — that comparison, as a natural isomorphism.

## Main results

* `Stacks.LocalCohomology.universal_baseChange` — the derived extension of scalars of the local
  cohomology counit is universal among power-torsion objects.
* `Stacks.LocalCohomology.localCohomologyBaseChangeIso` — the natural isomorphism
  `RΓ_Z(K) ⊗ᴸ_A B ≅ RΓ_Y(K ⊗ᴸ_A B)`.

## References

* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uA uB v

namespace Stacks.LocalCohomology

/-- Two objects universal among maps to `X` are isomorphic over `X`. -/
lemma exists_iso_over_of_universal {C : Type*} [Category C] {X Y Y' : C}
    (c : Y ⟶ X) (c' : Y' ⟶ X)
    (hYc' : Function.Bijective (fun g : Y ⟶ Y' => g ≫ c'))
    (hY'c : Function.Bijective (fun g : Y' ⟶ Y => g ≫ c))
    (hYc : Function.Injective (fun g : Y ⟶ Y => g ≫ c))
    (hY'c' : Function.Injective (fun g : Y' ⟶ Y' => g ≫ c')) :
    ∃ u : Y ≅ Y', u.hom ≫ c' = c := by
  obtain ⟨p, hp⟩ := hYc'.2 c
  obtain ⟨q, hq⟩ := hY'c.2 c'
  change p ≫ c' = c at hp
  change q ≫ c = c' at hq
  refine ⟨⟨p, q, hYc ?_, hY'c' ?_⟩, hp⟩ <;> simp [hp, hq]

/-- The counit of a coreflection is universal among maps from the subcategory. -/
lemma counit_bijective {C : Type*} [Category C] (P : ObjectProperty C)
    {Γ : C ⥤ P.FullSubcategory} (adj : P.ι ⊣ Γ) (Z : C) (W : P.FullSubcategory) :
    Function.Bijective (fun g : P.ι.obj W ⟶ P.ι.obj (Γ.obj Z) => g ≫ adj.counit.app Z) := by
  have h : (fun g : P.ι.obj W ⟶ P.ι.obj (Γ.obj Z) => g ≫ adj.counit.app Z) =
      P.fullyFaithfulι.homEquiv.symm.trans (adj.homEquiv W Z).symm := by
    funext g
    exact (congrArg (· ≫ adj.counit.app Z) (P.fullyFaithfulι.map_preimage g).symm).trans
      (adj.homEquiv_counit W Z _).symm
  rw [h]
  exact Equiv.bijective _

section Abstract

variable {C D : Type*} [Category C] [Category D] {P : ObjectProperty C} {Q : ObjectProperty D}
    {Γ : C ⥤ P.FullSubcategory} (adjP : P.ι ⊣ Γ)
    {Δ : D ⥤ Q.FullSubcategory} (adjQ : Q.ι ⊣ Δ) (L : C ⥤ D)
    (huniv : ∀ X : C, Q (L.obj (P.ι.obj (Γ.obj X))) ∧
      ∀ W, Q W → Function.Bijective (fun g : W ⟶ L.obj (P.ι.obj (Γ.obj X)) =>
        g ≫ L.map (adjP.counit.app X)))

/-- The comparison of the two coreflections, at an object: the unique map compatible with the
two counits. -/
def coreflectionBaseChangeApp (X : C) :
    L.obj (P.ι.obj (Γ.obj X)) ⟶ Q.ι.obj (Δ.obj (L.obj X)) :=
  Q.ι.map (adjQ.homEquiv ⟨_, (huniv X).1⟩ (L.obj X) (L.map (adjP.counit.app X)))

/-- The comparison `coreflectionBaseChangeApp` followed by the counit of the second
coreflection is the image under `L` of the counit of the first. -/
lemma coreflectionBaseChangeApp_counit (X : C) :
    coreflectionBaseChangeApp adjP adjQ L huniv X ≫ adjQ.counit.app (L.obj X) =
      L.map (adjP.counit.app X) := by
  have h := (adjQ.homEquiv ⟨_, (huniv X).1⟩ (L.obj X)).symm_apply_apply
    (L.map (adjP.counit.app X))
  rwa [Adjunction.homEquiv_counit] at h

/-- The comparison of two coreflections along a functor `L`: the natural transformation
`Γ ⋙ P.ι ⋙ L ⟶ L ⋙ Δ ⋙ Q.ι` compatible with the two counits. -/
def coreflectionBaseChange : Γ ⋙ P.ι ⋙ L ⟶ L ⋙ Δ ⋙ Q.ι where
  app X := coreflectionBaseChangeApp adjP adjQ L huniv X
  naturality {X X'} φ := by
    refine (counit_bijective Q adjQ (L.obj X') ⟨_, (huniv X).1⟩).1 ?_
    have hB : Q.ι.map (Δ.map (L.map φ)) ≫ adjQ.counit.app (L.obj X') =
        adjQ.counit.app (L.obj X) ≫ L.map φ := adjQ.counit.naturality (L.map φ)
    change (L.map (P.ι.map (Γ.map φ)) ≫ coreflectionBaseChangeApp adjP adjQ L huniv X') ≫
        adjQ.counit.app (L.obj X') = (coreflectionBaseChangeApp adjP adjQ L huniv X ≫
          Q.ι.map (Δ.map (L.map φ))) ≫ adjQ.counit.app (L.obj X')
    rw [Category.assoc, Category.assoc, coreflectionBaseChangeApp_counit, hB, ← Category.assoc,
      coreflectionBaseChangeApp_counit, ← L.map_comp, ← L.map_comp]
    exact congrArg L.map (adjP.counit.naturality φ)

/-- Each component of `coreflectionBaseChange` is an isomorphism. -/
instance coreflectionBaseChange_app_isIso (X : C) :
    IsIso ((coreflectionBaseChange adjP adjQ L huniv).app X) := by
  obtain ⟨w, hw⟩ := ((huniv X).2 _ (Q.prop_ι_obj (Δ.obj (L.obj X)))).2
    (adjQ.counit.app (L.obj X))
  change w ≫ L.map (adjP.counit.app X) = adjQ.counit.app (L.obj X) at hw
  refine ⟨w, ?_, ?_⟩
  · refine ((huniv X).2 _ (huniv X).1).1 ?_
    change (coreflectionBaseChangeApp adjP adjQ L huniv X ≫ w) ≫
      L.map (adjP.counit.app X) = (𝟙 _) ≫ L.map (adjP.counit.app X)
    rw [Category.assoc, hw, coreflectionBaseChangeApp_counit, Category.id_comp]
  · refine (counit_bijective Q adjQ (L.obj X) ⟨_, Q.prop_ι_obj (Δ.obj (L.obj X))⟩).1 ?_
    change (w ≫ coreflectionBaseChangeApp adjP adjQ L huniv X) ≫
      adjQ.counit.app (L.obj X) = (𝟙 _) ≫ adjQ.counit.app (L.obj X)
    rw [Category.assoc, coreflectionBaseChangeApp_counit, hw, Category.id_comp]

/-- The comparison `coreflectionBaseChange` of two coreflections, as a natural isomorphism. -/
def coreflectionBaseChangeIso : Γ ⋙ P.ι ⋙ L ≅ L ⋙ Δ ⋙ Q.ι :=
  haveI : IsIso (coreflectionBaseChange adjP adjQ L huniv) := NatIso.isIso_of_isIso_app _
  asIso (coreflectionBaseChange adjP adjQ L huniv)

end Abstract

section BaseChange

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG)

/-- The derived extension of scalars of `RΓ_Z(X)` has `IB`-power-torsion cohomology, and the
derived extension of scalars of the local cohomology counit at `X` is universal among maps from
objects of `D(B)` with `IB`-power-torsion cohomology to the derived extension of scalars of `X`. -/
lemma universal_baseChange (X : DerivedCategory (ModuleCat.{max uA uB v} A)) :
    Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)
        ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj
          ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
            ((Dualizing.localCohomologyRightAdjoint.{uA, max uA uB v} A I hI).1.obj X))) ∧
      ∀ W, Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f) W →
        Function.Bijective (fun g : W ⟶
            (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj
              ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
                ((Dualizing.localCohomologyRightAdjoint.{uA, max uA uB v} A I hI).1.obj X)) =>
          g ≫ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map
            ((Dualizing.localCohomologyAdjunction.{uA, max uA uB v} A I hI).counit.app X)) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset A, Ideal.span (s : Set A) = I := id hI
  have hs' : Ideal.span ((s.image f : Finset B) : Set B) = I.map f := by
    rw [Finset.coe_image, ← Ideal.map_span, hs]
  obtain ⟨Y, c, h1, h2, h3, h4⟩ := exists_coreflection_transport
    (fun a : A => derivedLoc.{uA, max uB v} a)
    (fun a : A => derivedLocUnit.{uA, max uB v} a)
    (fun a => derivedLocUnit_obj_isIso.{uA, max uB v} a)
    (fun a => derivedLocUnit_map_isIso.{uA, max uB v} a)
    (fun a b Z h => derivedLoc_preserves_kernel.{uA, max uB v} b a Z h)
    (fun a : A => derivedLoc.{uB, max uA v} (f a))
    (fun a : A => derivedLocUnit.{uB, max uA v} (f a))
    (fun a => derivedLocUnit_obj_isIso.{uB, max uA v} (f a))
    (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor
    (fun a Z => derivedExtendLocIso.{uA, uB, v} f a Z) s X
  have hPY : Dualizing.derivedPowerTorsionProperty A I hI Y :=
    (derivedPowerTorsion_iff_loc.{uA, max uB v} I hI s hs Y).mpr h1
  have univY : ∀ W, Dualizing.derivedPowerTorsionProperty A I hI W →
      Function.Bijective (fun g : W ⟶ Y => g ≫ c) :=
    fun W hW => h2 W ((derivedPowerTorsion_iff_loc.{uA, max uB v} I hI s hs W).mp hW)
  have univε := counit_bijective (Dualizing.derivedPowerTorsionProperty A I hI)
    (Dualizing.localCohomologyAdjunction.{uA, max uA uB v} A I hI) X
  obtain ⟨u, hu⟩ := exists_iso_over_of_universal c
    ((Dualizing.localCohomologyAdjunction.{uA, max uA uB v} A I hI).counit.app X)
    (univε ⟨Y, hPY⟩)
    (univY _ ((Dualizing.derivedPowerTorsionProperty A I hI).prop_ι_obj _))
    (univY Y hPY).1 (univε _).1
  refine ⟨?_, ?_⟩
  · rw [derivedPowerTorsion_iff_loc.{uB, max uA v} (I.map f) (hI.map f) (s.image f) hs']
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact (h3 a ha).of_iso (((derivedLoc.{uB, max uA v} (f a)).mapIso
      ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.mapIso u)).symm)
  intro W hW
  have hbij := h4 W (fun a ha =>
    (derivedPowerTorsion_iff_loc.{uB, max uA v} (I.map f) (hI.map f) (s.image f) hs' W).mp hW (f a)
      (Finset.mem_image_of_mem f ha))
  have hcomp : ∀ g : W ⟶ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj Y,
      g ≫ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map c =
        (g ≫ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map u.hom) ≫
          (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map
            ((Dualizing.localCohomologyAdjunction.{uA, max uA uB v} A I hI).counit.app X) :=
    fun g => by rw [Category.assoc, ← Functor.map_comp, hu]
  have hiso : Function.Bijective
      (fun g : W ⟶ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj Y =>
        g ≫ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map u.hom) := by
    refine ⟨fun g g' h =>
      (cancel_mono ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map u.hom)).1 h,
      fun g => ⟨g ≫ (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.map u.inv, ?_⟩⟩
    simp only [Category.assoc, ← Functor.map_comp, u.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [funext hcomp] at hbij
  exact (Function.Bijective.of_comp_iff _ hiso).mp hbij

/-- Local cohomology with support in a finitely generated ideal
commutes naturally with arbitrary derived extension of scalars. -/
@[stacks 0ALZ]
def localCohomologyBaseChangeIso :
    Dualizing.localCohomologyFunctor A I hI ⋙
          (Dualizing.derivedPowerTorsionProperty A I hI).ι ⋙
          (derivedExtensionScalarsGeneral f).functor ≅
      (derivedExtensionScalarsGeneral f).functor ⋙
          Dualizing.localCohomologyFunctor B (I.map f) (hI.map f) ⋙
          (Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι :=
  coreflectionBaseChangeIso (Dualizing.localCohomologyAdjunction.{uA, max uA uB v} A I hI)
    (Dualizing.localCohomologyAdjunction.{uB, max uA uB v} B (I.map f) (hI.map f))
    (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor
    (universal_baseChange.{uA, uB, v} f I hI)

end BaseChange

end Stacks.LocalCohomology

end
