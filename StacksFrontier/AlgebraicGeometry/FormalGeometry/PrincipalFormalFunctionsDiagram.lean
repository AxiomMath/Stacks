module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalKoszulTowerTriangles
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.PrincipalFormalFunctionsDegreeZero
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# The formal-functions diagram for a principal ideal on a ringed space

Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative
ring `A`, let `f ∈ A`, let `E ∈ D(𝒪_X)` and let `E_n = E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` be the
`f`-power Koszul tower of `E`.  Write `E^ = R lim E_n` for a derived limit of that tower.  This
file proves the nine-term commutative diagram with exact rows and columns of
[Stacks, Tag 0H3C], and then the same diagram with `E_n` replaced by the tower of honest
quotients `ℱ/f^(n+1)ℱ` of a sheaf of `𝒪_X`-modules, which is [Stacks, Tag 0H3E].

The hinge is the identification

`RΓ(X, E^) ≅ RΓ(X, E)^∧`,

the right-hand side being the derived `f`-adic completion of `RΓ(X, E)` in `D(A)`.  Its argument
is the one of [Stacks, Tag 0BLD], read on a ringed space and for an arbitrary object of `D(𝒪_X)`:
no quasi-coherence and no stabilization of torsion intervene, because the tower is the Koszul
tower itself rather than the tower of honest quotients.  Derived sections over the base ring
commute with derived limits (Tag 0D60), so `RΓ(X, E^)` is a derived limit of the tower
`n ↦ RΓ(X, E_n)`.  That tower is the `f`-power Koszul tower of `RΓ(X, E)` over `A`
(`KoszulTowerSections.nonempty_iso_koszulTower_derivedSections`, the step the source of
[Stacks, Tag 0H3C] asserts with details left out).  The derived completion of a complex is, by
Tag 0BKG, the mapping-cocone model of the Milnor limit of exactly that tower, and that model is
itself a derived limit of it, so the two agree by uniqueness of derived limits (Tag 07KZ).

The rest of the diagram is the diagram of [Stacks, Tag 0H32] for `K = RΓ(X, E)`, transported to
the geometric terms along that identification and along the comparison of the two Koszul towers.
That comparison is compatible with the cone triangles `E ⟶ E ⟶ E_n ⟶ E[1]` and
`K ⟶ K ⟶ K ⊗ᴸ_A (A --f^(n+1)--> A) ⟶ K[1]`, and the identification of `RΓ(X, E^)` is the first
component of an isomorphism between the image of the derived-limit triangle of `E^` and the
Milnor triangle of the algebraic tower, so the maps of the top row and of the middle column are
the ones induced by the geometric data.  For the quotient tower the per-level
normalizations are *not* available and are not claimed: a pro-isomorphism shifts the index, so
the two cohomology towers have the same limit and the same first derived limit as modules while
their individual projections do not correspond.

Derived completion is presented as in Tags 0BKG and 0H32: the statements are quantified over an
arbitrary left adjoint `completion` to the inclusion `P.ι` of the derived-complete objects, so
`(-)^∧` is `completion ⋙ P.ι` and no particular construction of it is privileged.  Such data
exists, by `Stacks.FormalFunctions.derivedComplete_principal_ι_isRightAdjoint`.

The derived limits `E^` and `ℱ^` are, for the same reason, taken as hypotheses rather than
constructed: a derived limit is unique only up to non-unique isomorphism.  They too always exist,
by `CategoryTheory.Pretriangulated.exists_isDerivedLimit` at the relevant tower, so neither
diagram theorem below is vacuous for want of an inhabitant of its hypotheses — for an arbitrary
`E` the binders `Ehat`, `hEhat`, `completion` and `adj` are jointly satisfiable with nothing
assumed.

## Main results

* `Stacks.Cohomology.PrincipalFormalFunctions.nonempty_iso_principalDerivedTensorSystem_of_iso` —
  the `f`-power Koszul tower of an object of `D(A)` depends on that object only up to isomorphism.
  The tower is defined through a chosen complex representing the object, so this is not a
  triviality: the isomorphism of towers is produced by realizing the given isomorphism of objects
  by an actual morphism of complexes through a K-injective resolution.
* `Stacks.Cohomology.PrincipalFormalFunctions`
  `.nonempty_iso_derivedSections_koszulTower_derivedCompletion` — the identification
  `RΓ(X, E^) ≅ RΓ(X, E)^∧` of [Stacks, Tag 0H3C], together with derived completeness of
  `RΓ(X, E^)` and the resulting identification `Hᵖ(X, E^) = Hᵖ(RΓ(X, E)^∧)` of cohomology
  modules.
* `Stacks.Cohomology.PrincipalFormalFunctions`
  `.nonempty_iso_koszulTower_comp_derivedSections_object` — derived sections over the base ring
  carry the `f`-power Koszul tower of `E ∈ D(𝒪_X)` to the `f`-power Koszul tower of `RΓ(X, E)`
  over `A`.  This is the preceding file's levelwise comparison, stated for an object of `D(𝒪_X)`
  rather than for a cochain complex.
* `Stacks.Cohomology.PrincipalFormalFunctions.formalFunctionsDiagram_principalKoszulTower` —
  **[Stacks, Tag 0H3C]**: for `E^ = R lim E_n` given with its derived-limit triangle, the
  identification `RΓ(X, E^) ≅ RΓ(X, E)^∧` and the nine-term commutative diagram with exact rows
  and columns, its top row induced by `E ⟶ E_n` and by the boundaries of the triangles
  `E ⟶ E ⟶ E_n ⟶ E[1]`, its middle column by the projections `E^ ⟶ E_n` and the derived-limit
  triangle, its left column and middle row the sequences of [Stacks, Tag 0BKG] and
  [Stacks, Tag 0H32].
* `Stacks.Cohomology.PrincipalFormalFunctions.exists_iso_milnorTriangle_derivedSections` — the
  image under `RΓ(X, -)` of the derived-limit triangle of `E^` is isomorphic to the Milnor
  triangle of the algebraic Koszul tower of `RΓ(X, E)`.
* `Stacks.Cohomology.PrincipalFormalFunctions`
  `.exists_formalFunctionsDiagram_principalKoszulTower` — the diagram of [Stacks, Tag 0H32] for
  `RΓ(X, E)`, read in the terms of the Koszul tower of `E` through some identifications.
* `Stacks.Cohomology.PrincipalFormalFunctions`
  `.nonempty_iso_principalKoszulComplexTower_of_iso` — the sheaf-side counterpart of the first
  item, and `.nonempty_iso_Ksys_principalKoszulTower`, which identifies the tower of cones of
  [Stacks, Tag 0H3D] with the `f`-power Koszul tower of `ℱ` in degree zero.
* `Stacks.Cohomology.PrincipalFormalFunctions`
  `.nonempty_iso_derivedSections_quotientTower_derivedCompletion` — `RΓ(X, ℱ^) = RΓ(X, ℱ)^∧` for
  a derived limit `ℱ^` of the tower of honest quotients, on an arbitrary ringed space and with no
  quasi-coherence hypothesis.  This is the displayed equality of [Stacks, Tag 0BLD] outside the
  world of schemes.
* `Stacks.Cohomology.PrincipalFormalFunctions.exists_formalFunctionsDiagram_quotientTower` —
  **the whole diagram of [Stacks, Tag 0H3E]**: the same nine terms with `E_n` replaced by
  `ℱ/f^(n+1)ℱ`.

## References

* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
* [Stacks Project, Tag 0H3E](https://stacks.math.columbia.edu/tag/0H3E)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase (baseSmul derivedSectionsOver principalKoszulTower
  smulComplex
  principalKoszulComplexTower isDerivedLimit_map_derivedSectionsOver)
open Stacks.Cohomology.KoszulTowerSections (principalComplexSystemMap koszulComplexTowerMap ksysIso
  nonempty_iso_koszulTower_derivedSections)
open Stacks.Cohomology.QuotientTowerFormalFunctions
  (nonempty_iso_isDerivedLimit_koszulTower_quotientTower
   exists_shortExact_homology_derivedSections_quotientTower)
open Stacks.Algebraization.PrincipalQuotientTowerCompletion (isDerivedLimit_milnorTriangle_obj₁)
open PrincipalTorsionTower (principalComplexSystem principalDerivedTensorSystem)

universe u

namespace Stacks.Cohomology.PrincipalFormalFunctions

attribute [local instance] HasDerivedCategory.standard

/-! ### The algebraic Koszul tower depends on its argument only up to isomorphism -/

/-- An isomorphism in the derived category between two complexes is realized by a morphism of
complexes into a K-injective resolution of the target, both it and the resolution map being
invertible in the derived category. -/
private theorem exists_isIso_Q_map_of_iso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    [IsGrothendieckAbelian.{u} 𝒜] {C C' : CochainComplex 𝒜 ℤ}
    (e : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj C') :
    ∃ (I : CochainComplex 𝒜 ℤ) (ψ : C ⟶ I) (p : C' ⟶ I),
      IsIso (DerivedCategory.Q.map ψ) ∧ IsIso (DerivedCategory.Q.map p) := by
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor 𝒜).obj C'
  let p : C' ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion 𝒜).app C'
  have hI : I.IsKInjective := inferInstance
  have hpQ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance
  -- The isomorphism `Q C ≅ Q I` induced by `e`.
  let u : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj I :=
    e ≪≫ asIso (DerivedCategory.Q.map p)
  -- Realise it by a morphism of complexes, using that `I` is K-injective.
  let cq := DerivedCategory.quotientCompQhIso 𝒜
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj C) I).surjective
    (cq.hom.app C ≫ u.hom ≫ cq.inv.app I)
  let ψ : C ⟶ I := (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).preimage h
  refine ⟨I, ψ, p, ?_, hpQ⟩
  have hnat : DerivedCategory.Qh.map
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map ψ) ≫ cq.hom.app I =
        cq.hom.app C ≫ DerivedCategory.Q.map ψ :=
    cq.hom.naturality ψ
  rw [Functor.map_preimage, hh] at hnat
  have h₁ : IsIso (cq.hom.app C ≫ DerivedCategory.Q.map ψ) := by
    rw [← hnat]; infer_instance
  exact IsIso.of_isIso_comp_left (cq.hom.app C) _

/-- **The `f`-power Koszul tower of an object of `D(A)` depends on the object only up to
isomorphism.** The tower `n ↦ K ⊗ᴸ_A (A --f^(n+1)--> A)` is realized through the complex
`DerivedCategory.Q.objPreimage K` chosen to represent `K`, so an isomorphism `K ≅ K'` does not
give an isomorphism of towers for free: it has to be realized by an actual morphism of complexes
first.  That is possible through a K-injective resolution of the complex representing `K'`, and
a morphism of complexes which is invertible in `D(A)` induces a levelwise isomorphism of Koszul
towers. -/
theorem nonempty_iso_principalDerivedTensorSystem_of_iso
    (A : Type u) [CommRing A] (f : A) {K K' : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ K') :
    Nonempty (principalDerivedTensorSystem A f K ≅ principalDerivedTensorSystem A f K') := by
  obtain ⟨I, ψ, p, hψ, hpQ⟩ := exists_isIso_Q_map_of_iso (𝒜 := ModuleCat.{u} A)
    (DerivedCategory.Q.objObjPreimageIso K ≪≫ e ≪≫ (DerivedCategory.Q.objObjPreimageIso K').symm)
  have h₁ : IsIso (Functor.whiskerRight (principalComplexSystemMap f ψ) DerivedCategory.Q) :=
    Stacks.Cohomology.KoszulTowerSections.isIso_whiskerRight_principalComplexSystemMap f ψ
  have h₂ : IsIso (Functor.whiskerRight (principalComplexSystemMap f p) DerivedCategory.Q) :=
    Stacks.Cohomology.KoszulTowerSections.isIso_whiskerRight_principalComplexSystemMap f p
  exact ⟨@asIso _ _ _ _ _ h₁ ≪≫ (@asIso _ _ _ _ _ h₂).symm⟩

/-! ### Derived sections of the Koszul tower of an object of `D(𝒪_X)` -/

section Sections

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) (f : A)

/-- **The step that the source of [Stacks, Tag 0H3C] omits, for an object of `D(𝒪_X)`.** Derived
sections over the base ring carry the `f`-power Koszul tower
`n ↦ E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` of `E ∈ D(𝒪_X)` to the `f`-power Koszul tower
`n ↦ RΓ(X, E) ⊗ᴸ_A (A --f^(n+1)--> A)` of `RΓ(X, E)` over `A`, compatibly with the transition
maps.

This is `KoszulTowerSections.nonempty_iso_koszulTower_derivedSections`, which is stated for a
cochain complex, at the complex chosen to represent `E`, followed by the transport of the
algebraic tower along `RΓ(X, Q (Q⁻¹ E)) ≅ RΓ(X, E)`. -/
theorem nonempty_iso_koszulTower_comp_derivedSections_object
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Nonempty (principalKoszulTower X ρ f E ⋙ derivedSectionsOver X ρ ≅
      principalDerivedTensorSystem A f ((derivedSectionsOver X ρ).obj E)) := by
  obtain ⟨e⟩ := nonempty_iso_koszulTower_derivedSections X ρ f
    (DerivedCategory.Q.objPreimage E)
  obtain ⟨t⟩ := nonempty_iso_principalDerivedTensorSystem_of_iso A f
    ((derivedSectionsOver X ρ).mapIso (DerivedCategory.Q.objObjPreimageIso E))
  exact ⟨Functor.associator _ _ _ ≪≫ e ≪≫ t⟩

/-- **`RΓ(X, E^) = RΓ(X, E)^∧`.** Let `(X, 𝒪_X)` be a ringed
space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative ring `A`, let `f ∈ A`, let
`E ∈ D(𝒪_X)`, let `E_n = E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` be the `f`-power Koszul tower and let
`E^` be a derived limit of that tower.  Let `completion` be a left adjoint to the inclusion of
the objects of `D(A)` that are derived complete for the ideal `(f)`, so that
`(-)^∧ = completion ⋙ P.ι` is derived `f`-adic completion as in [Stacks, Tag 0BKG].  Then

`RΓ(X, E^) ≅ RΓ(X, E)^∧`,

the object `RΓ(X, E^)` is itself derived complete for `(f)`, and for every `p` its `p`-th
cohomology module is that of `RΓ(X, E)^∧` — the identification
`Hᵖ(X, E^) = Hᵖ(RΓ(X, E)^∧)` of [Stacks, Tag 0H3C]. -/
theorem nonempty_iso_derivedSections_koszulTower_derivedCompletion
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hEhat : IsDerivedLimit (principalKoszulTower X ρ f E) Ehat) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      Nonempty ((derivedSectionsOver X ρ).obj Ehat ≅
          completed.obj ((derivedSectionsOver X ρ).obj E)) ∧
        IsDerivedComplete (Ideal.span {f}) ((derivedSectionsOver X ρ).obj Ehat) ∧
        ∀ p : ℤ, Nonempty
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
              ((derivedSectionsOver X ρ).obj Ehat) ≅
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
              (completed.obj ((derivedSectionsOver X ρ).obj E))) := by
  intro P completion adj completed
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  -- `RΓ(X, E^)` is a derived limit of the tower of derived sections, by Tag 0D60.
  obtain ⟨_, hRΓ⟩ := isDerivedLimit_map_derivedSectionsOver X ρ
    (principalKoszulTower X ρ f E) Ehat hEhat
  -- That tower is the `f`-power Koszul tower of `RΓ(X, E)` over `A`.
  obtain ⟨c⟩ := nonempty_iso_koszulTower_comp_derivedSections_object X ρ f E
  have hRΓ' : IsDerivedLimit
      (principalDerivedTensorSystem A f ((derivedSectionsOver X ρ).obj E))
      ((derivedSectionsOver X ρ).obj Ehat) :=
    IsDerivedLimit.of_natIso c hRΓ
  -- The mapping-cocone model of the Milnor limit is another derived limit of that same tower.
  have hmil : IsDerivedLimit
      (principalDerivedTensorSystem A f ((derivedSectionsOver X ρ).obj E))
      ((CompletionSequences.milnorTriangle A (principalComplexSystem A f
        (DerivedCategory.Q.objPreimage ((derivedSectionsOver X ρ).obj E)))).obj₁) :=
    isDerivedLimit_milnorTriangle_obj₁ A _
  -- Two derived limits of one system are isomorphic, by Tag 07KZ.
  obtain ⟨eu⟩ := (ModuleDerivedLimitTriangle.derivedLimit_iso_and_homology_shortExact A
    (principalDerivedTensorSystem A f ((derivedSectionsOver X ρ).obj E))).1 _ _ hRΓ' hmil
  -- The derived completion is that same mapping-cocone model, by Tag 0BKG.
  obtain ⟨S, -⟩ := CompletionSequences.derivedCompletion_principal_homology A f completion adj
  have eFhat : (derivedSectionsOver X ρ).obj Ehat ≅
      completed.obj ((derivedSectionsOver X ρ).obj E) :=
    eu ≪≫ (S.comparison.iso
        (DerivedCategory.Q.objPreimage ((derivedSectionsOver X ρ).obj E))).symm ≪≫
      completed.mapIso
        (DerivedCategory.Q.objObjPreimageIso ((derivedSectionsOver X ρ).obj E))
  refine ⟨⟨eFhat⟩, ?_, fun p ↦
    ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).mapIso eFhat⟩⟩
  exact DerivedCompleteRecurrence.isDerivedComplete_of_iso eFhat.symm
    (completion.obj ((derivedSectionsOver X ρ).obj E)).2

/-! ### The nine-term diagram -/

/-- Transporting a product of components along a levelwise isomorphism of towers. -/
private lemma pi_mapIso_hom_comp_lift {C : Type*} [Category C] [HasProductsOfShape ℕ C]
    {F G H : ℕᵒᵖ ⥤ C} (e : F ≅ G) (t : G ⟶ H) :
    (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩).hom ≫
        (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n ≫ t.app ⟨n⟩) =
      Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n ≫ (e.hom ≫ t).app ⟨n⟩ := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, Pi.lift_π, ← Category.assoc, Pi.mapIso_hom_π, Category.assoc, Pi.lift_π,
    NatTrans.comp_app, Iso.app_hom]

omit [CommRing A] in
private lemma map_comp_map_inv_of_comp_hom {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {g : x ⟶ y} {h : x ⟶ z} (i : y ≅ z) (H : g ≫ i.hom = h) :
    F.map h ≫ F.map i.inv = F.map g := by
  rw [← H, F.map_comp, Category.assoc, ← F.map_comp, i.hom_inv_id, F.map_id, Category.comp_id]

omit [CommRing A] in
private lemma comp_inv_hom_comp_comp {C : Type*} [Category C] {P Q R S T U : C} {x : P ⟶ Q}
    (i : R ≅ Q)
    {y : Q ⟶ S} {l : P ⟶ T} {m : T ⟶ S} (g : S ⟶ U) (h : x ≫ y = l ≫ m) :
    (x ≫ i.inv) ≫ i.hom ≫ y ≫ g = l ≫ m ≫ g := by
  rw [Category.assoc, i.inv_hom_id_assoc, reassoc_of% h]

omit [CommRing A] in
private lemma comp_comp_inv_of_comp_eq {C : Type*} [Category C] {P Q R S : C} {x : P ⟶ Q}
    {y : Q ⟶ R}
    {z : P ⟶ S} (i : S ≅ R) (h : x ≫ y = z ≫ i.hom) : x ≫ y ≫ i.inv = z := by
  rw [← Category.assoc, h, Category.assoc, i.hom_inv_id, Category.comp_id]

omit [CommRing A] in
private lemma map_comp_comp_comp_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₁ X₂ X₃ X₄ : C} {W : D} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {P : F.obj X₂ ⟶ W}
    {π : W ⟶ F.obj X₃} (hP : P ≫ π = F.map b) {r : X₁ ⟶ X₄} (hr : a ≫ b ≫ c = r) :
    F.map a ≫ P ≫ π ≫ F.map c = F.map r := by
  rw [reassoc_of% hP, ← F.map_comp, ← F.map_comp, hr]

omit [CommRing A] in
private lemma comp_comp_comp_map_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : D}
    {Z Z' W : C} {a : X ⟶ Y} {d : Y ⟶ F.obj Z} {d' : X ⟶ F.obj W} (φ : W ⟶ Z) (u : Z ⟶ Z')
    (v : Z' ⟶ W) (huv : φ ≫ u ≫ v = 𝟙 W) (h : a ≫ d = d' ≫ F.map φ) :
    a ≫ (d ≫ F.map u) ≫ F.map v = d' := by
  rw [Category.assoc, ← Category.assoc a, h, Category.assoc, ← F.map_comp, ← F.map_comp, huv,
    F.map_id, Category.comp_id]

omit [CommRing A] in
private lemma comp_comp_comp_inv_eq {C : Type*} [Category C] {P Q R S U V : C} {x : P ⟶ Q}
    {ι : Q ⟶ R}
    {φ : P ⟶ S} {t : S ⟶ R} (h₁ : x ≫ ι = φ ≫ t) {q : R ⟶ U} {pr : Q ⟶ V} (i : V ≅ U)
    (h₂ : ι ≫ q = pr ≫ i.hom) : φ ≫ t ≫ q ≫ i.inv = x ≫ pr := by
  rw [← Category.assoc, ← h₁, Category.assoc, ← Category.assoc ι, h₂, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

omit [CommRing A] in
private lemma map_comp_map_comp_map_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₁ X₂ X₃ X₄ X₅ X₆ : C} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {d : X₄ ⟶ X₅}
    {e : X₅ ⟶ X₆} {r : X₁ ⟶ X₆} (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    F.map a ≫ F.map (b ≫ c ≫ d) ≫ F.map e = F.map r := by
  rw [← F.map_comp, ← F.map_comp, ← h]
  simp only [Category.assoc]

omit [CommRing A] in
private lemma comp_comp_eq_of_square {C : Type*} [Category C] {P Q R S T : C} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : P ⟶ S} {d : S ⟶ R} {e : R ⟶ T} {g : Q ⟶ T} (h₁ : a ≫ b = c ≫ d)
    (h₂ : b ≫ e = g) : c ≫ d ≫ e = a ≫ g := by
  rw [← Category.assoc, ← h₁, Category.assoc, h₂]

omit [CommRing A] in
private lemma comp_comp_comp_comp_inv_eq {C : Type*} [Category C] {K M N P R S V : C}
    {x : K ⟶ M} {y : M ⟶ N} {e : K ⟶ P} {u : P ⟶ N} {t : N ⟶ R} {q : R ⟶ S} {i : P ⟶ S}
    {g : K ⟶ V} (j : V ≅ S) (h₁ : x ≫ y = e ≫ u) (h₂ : u ≫ t ≫ q = i)
    (h₃ : g ≫ j.hom = e ≫ i) : x ≫ y ≫ t ≫ q ≫ j.inv = g := by
  rw [← Category.assoc x, h₁, Category.assoc, reassoc_of% h₂, ← reassoc_of% h₃,
    j.hom_inv_id, Category.comp_id]

/-! ### The derived limit of the tower of derived sections -/

/-- **The derived-limit triangle of `RΓ(X, E^)` is the Milnor triangle of the algebraic Koszul
tower.** Let `E^` be a derived limit of the `f`-power Koszul tower `E_n` of `E ∈ D(𝒪_X)`, through
the distinguished triangle `E^ ⟶ ∏ E_n ⟶ ∏ E_n ⟶ E^[1]` whose middle map is `1 - shift`, and let
`c` identify the tower `n ↦ RΓ(X, E_n)` with the `f`-power Koszul tower of `K = RΓ(X, E)`. Then
the image of that triangle under `RΓ(X, -)` is isomorphic to the Milnor triangle of the tower of
cones on the chosen complex representing `K`, by an isomorphism of triangles which is the product
of the components of `c` on the two middle terms. -/
theorem exists_iso_milnorTriangle_derivedSections
    (E Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (a : Ehat ⟶ ∏ᶜ fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩)
    (b : (∏ᶜ fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩) ⟶ Ehat⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩) (n + 1) ≫
            (principalKoszulTower X ρ f E).map (homOfLE (Nat.le_succ n)).op) b ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (c : principalKoszulTower X ρ f E ⋙ derivedSectionsOver X ρ ≅
      principalDerivedTensorSystem A f ((derivedSectionsOver X ρ).obj E)) :
    let RΓ := derivedSectionsOver X ρ
    let Y := fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩
    let EA := principalComplexSystem A f (DerivedCategory.Q.objPreimage (RΓ.obj E))
    let T₂ := CompletionSequences.milnorTriangle A EA
    let T := Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π Y n - Pi.π Y (n + 1) ≫
          (principalKoszulTower X ρ f E).map (homOfLE (Nat.le_succ n)).op) b
    ∃ (φ : RΓ.obj Ehat ⟶ T₂.obj₁) (ι₂ : RΓ.obj (∏ᶜ Y) ⟶ T₂.obj₂)
      (ι₃ : RΓ.obj (∏ᶜ Y) ⟶ T₂.obj₃), IsIso φ ∧ IsIso ι₃ ∧
      (∀ n : ℕ, ι₂ ≫ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n) =
        RΓ.map (Pi.π Y n) ≫ c.hom.app ⟨n⟩) ∧
      (∀ n : ℕ, ι₃ ≫ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n) =
        RΓ.map (Pi.π Y n) ≫ c.hom.app ⟨n⟩) ∧
      RΓ.map a ≫ ι₂ = φ ≫ T₂.mor₁ ∧
      ∀ (r r' : ℤ) (hr : r + 1 = r'),
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map ι₃ ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ T₂ r r' hr =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
              (RΓ.mapTriangle.obj T) r r' hr ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r').map φ := by
  intro RΓ Y EA T₂ T
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
    moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
  let := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{u} A) (I := ℕ)
  have hRΓ : PreservesLimit (Discrete.functor Y) RΓ :=
    Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor
      (Stacks.Cohomology.DerivedSectionsOverBase.sectionsOver X ρ) RΓ
      (Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOverUnit X ρ) _
  have _ := Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver_isTriangulated X ρ
  let Z := principalDerivedTensorSystem A f (RΓ.obj E)
  let e : T₂.obj₂ ≅ ∏ᶜ fun n : ℕ ↦ Z.obj ⟨n⟩ :=
    PreservesProduct.iso DerivedCategory.Q (fun n : ℕ ↦ EA.obj ⟨n⟩)
  have heπ (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n =
      DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n) := by
    have h := piComparison_comp_π DerivedCategory.Q (fun n : ℕ ↦ EA.obj ⟨n⟩) n
    rwa [← PreservesProduct.iso_hom] at h
  have he : T₂.mor₂ ≫ e.hom = e.hom ≫ Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) (n + 1) ≫ Z.map (homOfLE (Nat.le_succ n)).op := by
    have key : DerivedCategory.Q.map (CompletionSequences.complexDifference A EA) ≫
        (PreservesProduct.iso DerivedCategory.Q (fun n : ℕ ↦ EA.obj ⟨n⟩)).hom =
        (PreservesProduct.iso DerivedCategory.Q (fun n : ℕ ↦ EA.obj ⟨n⟩)).hom ≫ Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (EA.obj ⟨n⟩)) n -
            Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (EA.obj ⟨n⟩)) (n + 1) ≫
              DerivedCategory.Q.map (EA.map (homOfLE (Nat.le_succ n)).op) := by
      refine Pi.hom_ext _ _ fun n ↦ ?_
      simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π, Pi.lift_π,
        Preadditive.comp_sub, ← Functor.map_comp, piComparison_comp_π_assoc,
        CompletionSequences.complexDifference, Functor.map_sub]
    exact key
  obtain ⟨τ, h₁, -, h₃, k₂, k₃⟩ :=
    Stacks.Cohomology.KoszulTowerSections.exists_triangleMorphism_map_derivedLimit RΓ
      (principalKoszulTower X ρ f E) Z c a b hT T₂
      (CompletionSequences.milnorTriangle_distinguished A EA) e e he
  exact ⟨τ.hom₁, τ.hom₂, τ.hom₃, h₁, h₃, fun n ↦ (congrArg (τ.hom₂ ≫ ·) (heπ n).symm).trans (k₂ n),
    fun n ↦ (congrArg (τ.hom₃ ≫ ·) (heπ n).symm).trans (k₃ n), τ.comm₁,
    fun r r' hr ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ_naturality
      τ r r' hr⟩

/-- **The diagram of [Stacks, Tag 0H32] read through a comparison of towers and of triangles.**
Let `K ∈ D(A)`, let `V` be an inverse system in `D(A)` with an isomorphism `c` to the `f`-power
Koszul tower `n ↦ K ⊗ᴸ_A (A --f^(n+1)--> A)`, and let `gIn n : K ⟶ Vₙ` and `δg` be maps which
`c` carries to the cone inclusions and to the boundaries of the cone triangles of the Koszul
tower. Let `L` be a triangle with maps `proj₂ n`, `proj₃ n` from its middle terms to `Vₙ`, and
let `(φ, ι₂, ι₃)` compare `L` with the Milnor triangle of the Koszul tower compatibly with `c`,
`φ` and `ι₃` being isomorphisms. Then the nine-term diagram of [Stacks, Tag 0H32] for `K` holds
with `lim Hᵖ(Vₙ)`, `R¹lim Hᵖ⁻¹(Vₙ)` and `Hᵖ(L.obj₁)` in place of the Koszul terms: its top row
is induced by `gIn` and `δg`, its middle column by `L` and the `proj`, and its middle row is
that of [Stacks, Tag 0H32] read through the identification `L.obj₁ ≅ K^∧` induced by `φ`, which
is compatible with the unit of the completion, `gIn` and the maps `L.obj₁ ⟶ Vₙ`. -/
theorem formalFunctionsDiagram_of_triangleComparison
    (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ)
    (V : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A))
    (c : V ≅ principalDerivedTensorSystem A f K)
    (gIn : ∀ n : ℕ, K ⟶ V.obj ⟨n⟩)
    (hgIn : ∀ n : ℕ, gIn n ≫ c.hom.app ⟨n⟩ = (DerivedCategory.Q.objObjPreimageIso K).inv ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr
        (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K))))
    (δg : ∀ (n : ℕ) (q q' : ℤ), q + 1 = q' →
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (V.obj ⟨n⟩) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q').obj K))
    (hδg : ∀ (n : ℕ) (q q' : ℤ) (hq : q + 1 = q'),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map (c.hom.app ⟨n⟩) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
              (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K)))) q q' hq ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q').map
            (DerivedCategory.Q.objObjPreimageIso K).hom = δg n q q' hq)
    (L : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (proj₂ : ∀ n : ℕ, L.obj₂ ⟶ V.obj ⟨n⟩) (proj₃ : ∀ n : ℕ, L.obj₃ ⟶ V.obj ⟨n⟩)
    (φ : L.obj₁ ⟶ (CompletionSequences.milnorTriangle A
      (principalComplexSystem A f (DerivedCategory.Q.objPreimage K))).obj₁)
    (ι₂ : L.obj₂ ⟶ (CompletionSequences.milnorTriangle A
      (principalComplexSystem A f (DerivedCategory.Q.objPreimage K))).obj₂)
    (ι₃ : L.obj₃ ⟶ (CompletionSequences.milnorTriangle A
      (principalComplexSystem A f (DerivedCategory.Q.objPreimage K))).obj₃)
    (hφ : IsIso φ) (hι₃ : IsIso ι₃)
    (hι₂π : ∀ n : ℕ, ι₂ ≫ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦
      (principalComplexSystem A f (DerivedCategory.Q.objPreimage K)).obj ⟨n⟩) n) =
        proj₂ n ≫ c.hom.app ⟨n⟩)
    (hι₃π : ∀ n : ℕ, ι₃ ≫ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦
      (principalComplexSystem A f (DerivedCategory.Q.objPreimage K)).obj ⟨n⟩) n) =
        proj₃ n ≫ c.hom.app ⟨n⟩)
    (hφ₁ : L.mor₁ ≫ ι₂ = φ ≫ (CompletionSequences.milnorTriangle A
      (principalComplexSystem A f (DerivedCategory.Q.objPreimage K))).mor₁)
    (hδ : ∀ (r r' : ℤ) (hr : r + 1 = r'),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map ι₃ ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
            (CompletionSequences.milnorTriangle A
              (principalComplexSystem A f (DerivedCategory.Q.objPreimage K))) r r' hr =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ L r r' hr ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r').map φ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let HH (q : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
      let H (q : ℤ) := (HH q).obj K
      let cohTower (q : ℤ) := V ⋙ HH q
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (H p) f)
      let limitCoh := limit (cohTower p)
      let tate := CompletionSequences.adicTateModule A (H (p + 1)) f
      let H0CompletedHp := (HH 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (H p)))
      let HpEhat := (HH p).obj L.obj₁
      let R1Torsion := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (H p) f)
      let R1PreviousCoh := CompletionSequences.firstDerivedLimit A (cohTower (p - 1))
      let productComparison : (HH (p - 1)).obj L.obj₃ ⟶
          CompletionSequences.moduleProduct A (cohTower (p - 1)) :=
        Pi.lift fun n : ℕ ↦ (HH (p - 1)).map (proj₃ n)
      ∃ (S : CompletionSequences.PrincipalCompletionSequences A f completed adj.unit)
        (Φ : L.obj₁ ≅ completed.obj K),
        let middleIn : H0CompletedHp ⟶ HpEhat :=
          (S.truncation K p).inclusion S.shift ≫ (HH p).map Φ.inv
        let middleOut : HpEhat ⟶ tate := (HH p).map Φ.hom ≫
          (S.truncation K p).projection f S.shift (S.moduleSequence (H (p + 1))).tateIso
        let leftIn : R1Torsion ⟶ H0CompletedHp := (S.moduleSequence (H p)).inclusion
        let leftOut : H0CompletedHp ⟶ ordinaryCompletion := (S.moduleSequence (H p)).projection
        ∃ (termIn : CompletionSequences.powerQuotientSystem A (H p) f ⟶ cohTower p)
          (termOut : cohTower p ⟶ PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f)
          (previousOut : cohTower (p - 1) ⟶
            PrincipalTorsionTower.powerTorsionSystem A (H p) f)
          (topIn : ordinaryCompletion ⟶ limitCoh)
          (topOut : limitCoh ⟶ tate)
          (htop : topIn ≫ topOut = 0)
          (hmiddle : middleIn ≫ middleOut = 0)
          (hleft : leftIn ≫ leftOut = 0)
          (columnIn : R1PreviousCoh ⟶ HpEhat)
          (columnOut : HpEhat ⟶ limitCoh)
          (hcolumn : columnIn ≫ columnOut = 0)
          (bottom : R1Torsion ≅ R1PreviousCoh),
          (∀ n : ℕ, adj.unit.app K ≫ Φ.inv ≫ L.mor₁ ≫ proj₂ n = gIn n) ∧
          (∀ n : ℕ,
            cokernel.π (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) ≫
                termIn.app ⟨n⟩ =
              (HH p).map (gIn n)) ∧
          (∀ n : ℕ,
            termOut.app ⟨n⟩ ≫
                kernel.ι (PrincipalTorsionTower.powerMultiplication A (H (p + 1)) (f ^ (n + 1))) =
              δg n p (p + 1) (by omega)) ∧
          (∀ n : ℕ,
            previousOut.app ⟨n⟩ ≫
                kernel.ι (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) =
              δg n (p - 1) p (by omega)) ∧
          (∀ n : ℕ, topIn ≫ limit.π (cohTower p) ⟨n⟩ =
            limit.π (CompletionSequences.powerQuotientSystem A (H p) f) ⟨n⟩ ≫ termIn.app ⟨n⟩) ∧
          (∀ n : ℕ, topOut ≫
              limit.π (PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f) ⟨n⟩ =
            limit.π (cohTower p) ⟨n⟩ ≫ termOut.app ⟨n⟩) ∧
          IsIso productComparison ∧
          (productComparison ≫
              cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ columnIn =
            (HH 0).homologySequenceδ L (p - 1) p (by omega)) ∧
          (∀ n : ℕ, columnOut ≫ limit.π (cohTower p) ⟨n⟩ = (HH p).map (L.mor₁ ≫ proj₂ n)) ∧
          (cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ bottom.inv =
            (Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ (cohTower (p - 1)).obj ⟨n⟩) n ≫ previousOut.app ⟨n⟩) ≫
              cokernel.π (CompletionSequences.moduleDifference A
                (PrincipalTorsionTower.powerTorsionSystem A (H p) f))) ∧
          (ShortComplex.mk topIn topOut htop).ShortExact ∧
          (ShortComplex.mk middleIn middleOut hmiddle).ShortExact ∧
          (ShortComplex.mk leftIn leftOut hleft).ShortExact ∧
          (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
          middleIn ≫ columnOut = leftOut ≫ topIn ∧
          middleOut = columnOut ≫ topOut ∧
          bottom.hom ≫ columnIn = leftIn ≫ middleIn := by
  intro P completion adj completed HH H cohTower
    ordinaryCompletion limitCoh tate H0CompletedHp HpEhat R1Torsion R1PreviousCoh productComparison
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  -- The algebraic diagram of Tag 0H32 at `K = RΓ(X, E)`.
  have h32 := PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison A f K p
  dsimp only at h32
  obtain ⟨S, hS⟩ := h32 completion adj
  obtain ⟨termIn, termOut, previousOut, productIso, topIn, topOut, htop, columnIn, columnOut,
    hcolumn, bottom, e1, e2, e3, e4, e5, e6, e7, e8, e9, hTop, hMiddle, hLeft, hColumn,
    hcomm1, hcomm2, hcomm3⟩ := hS
  let C' := DerivedCategory.Q.objPreimage K
  let eK := DerivedCategory.Q.objObjPreimageIso K
  let EA := principalComplexSystem A f C'
  let T := CompletionSequences.milnorTriangle A EA
  let completionIso := completed.mapIso eK.symm ≪≫ S.comparison.iso C'
  let Φ : L.obj₁ ≅ completed.obj K := @asIso _ _ _ _ φ hφ ≪≫ completionIso.symm
  refine ⟨S, Φ, ?_⟩
  intro middleIn middleOut leftIn leftOut
  let cp (q : ℤ) := Functor.isoWhiskerRight c (HH q)
  let α := HasLimit.isoOfNatIso (cp p)
  let β := CompletionSequences.firstDerivedLimitIso A (cp (p - 1))
  let M := Pi.mapIso fun n : ℕ ↦ (cp (p - 1)).app ⟨n⟩
  have hprod : productComparison = (HH (p - 1)).map ι₃ ≫ productIso.hom ≫ M.inv := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    have h₁ : M.inv ≫ Pi.π (fun n : ℕ ↦ (cohTower (p - 1)).obj ⟨n⟩) n =
        Pi.π _ n ≫ (HH (p - 1)).map (c.inv.app ⟨n⟩) := Pi.mapIso_inv_π _ n
    have h₂ := comp_comp_inv_of_comp_eq (c.app ⟨n⟩) (hι₃π n)
    have h₃ := map_comp_comp_comp_map (HH (p - 1)) (e6 n) h₂
    refine (Pi.lift_π _ _).trans (h₃.symm.trans ?_)
    simp only [Category.assoc, h₁]
    rfl
  have hlow : (bottom.hom ≫ β.inv) ≫ β.hom ≫ columnIn ≫ (HH p).map Φ.inv =
      leftIn ≫ middleIn :=
    comp_inv_hom_comp_comp β ((HH p).map Φ.inv) hcomm3
  let bottomGeo : R1Torsion ≅ R1PreviousCoh := bottom ≪≫ β.symm
  have hbottom : bottomGeo.hom = bottom.hom ≫ β.inv := rfl
  have hbottom' : bottomGeo.inv = β.hom ≫ bottom.inv := rfl
  refine ⟨termIn ≫ (cp p).inv, (cp p).hom ≫ termOut, (cp (p - 1)).hom ≫ previousOut,
    topIn ≫ α.inv, α.hom ≫ topOut, ?_, ?_, (S.moduleSequence (H p)).zero,
    β.hom ≫ columnIn ≫ (HH p).map Φ.inv, (HH p).map Φ.hom ≫ columnOut ≫ α.inv, ?_,
    bottomGeo,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the top row is a complex
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact htop
  · -- the middle row is a complex
    simp only [middleIn, middleOut, Category.assoc]
    rw [← (HH p).map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact S.truncation_zero K p
  · -- the middle column is a complex
    simp only [Category.assoc]
    rw [← (HH p).map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ← Category.assoc columnIn columnOut, hcolumn, zero_comp, comp_zero]
  · -- the identification `L.obj₁ ≅ K^∧` is compatible with the maps to the tower
    intro n
    have hu : adj.unit.app K ≫ completionIso.hom = eK.inv ≫
        DerivedCategory.Q.map (CompletionSequences.principalCompletionUnit A f C') :=
      comp_comp_eq_of_square (adj.unit.naturality eK.inv) (S.comparison.unit_iso C')
    have hT₁ : DerivedCategory.Q.map (CompletionSequences.principalCompletionUnit A f C') ≫
        T.mor₁ ≫ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n) =
          DerivedCategory.Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C')) := by
      have h := congrArg DerivedCategory.Q.map
        (CompletionSequences.principalCompletionUnit_fst_assoc A f C'
          (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n))
      rw [CompletionSequences.principalComplexUnit_π, Functor.map_comp, Functor.map_comp] at h
      exact h
    have hL : inv φ ≫ L.mor₁ ≫ proj₂ n = T.mor₁ ≫
        DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n) ≫ c.inv.app ⟨n⟩ := by
      rw [IsIso.inv_comp_eq]
      exact (comp_comp_comp_inv_eq hφ₁ (c.app ⟨n⟩) (hι₂π n)).symm
    have hΦ : Φ.inv = completionIso.hom ≫ inv φ := rfl
    rw [hΦ, Category.assoc, hL]
    exact comp_comp_comp_comp_inv_eq (c.app ⟨n⟩) hu hT₁ (hgIn n)
  · -- the reduction maps of the top row
    intro n
    have h := map_comp_map_inv_of_comp_hom (HH p) (c.app ⟨n⟩) (hgIn n)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (HH p).map (c.inv.app ⟨n⟩)) (e1 n)).trans h)
  · -- the torsion maps of the top row
    intro n
    exact (Category.assoc _ _ _).trans ((congrArg ((HH p).map (c.hom.app ⟨n⟩) ≫ ·)
      (e2 n)).trans (hδg n p (p + 1) (by omega)))
  · -- the torsion maps in degree `p - 1`
    intro n
    exact (Category.assoc _ _ _).trans ((congrArg ((HH (p - 1)).map (c.hom.app ⟨n⟩) ≫ ·)
      (e3 n)).trans (hδg n (p - 1) p (by omega)))
  · -- the left-hand map of the top row
    intro n
    simp only [α, NatTrans.comp_app, Category.assoc]
    rw [HasLimit.isoOfNatIso_inv_π, reassoc_of% e4 n]
  · -- the right-hand map of the top row
    intro n
    exact (Category.assoc _ _ _).trans ((congrArg (α.hom ≫ ·) (e5 n)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ termOut.app ⟨n⟩)
        (HasLimit.isoOfNatIso_hom_π (cp p) ⟨n⟩)).trans (Category.assoc _ _ _))))
  · -- the product comparison is an isomorphism
    rw [hprod]
    have : IsIso ((HH (p - 1)).map ι₃) := Functor.map_isIso _ _
    infer_instance
  · -- the top map of the middle column
    have hβ : cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ β.hom =
        M.hom ≫ cokernel.π (CompletionSequences.moduleDifference A
          (principalDerivedTensorSystem A f K ⋙ HH (p - 1))) :=
      CompletionSequences.firstDerivedLimitIso_π A (cp (p - 1))
    have huv : φ ≫ completionIso.inv ≫ Φ.inv = 𝟙 _ := by simp [Φ]
    rw [hprod, Category.assoc, Category.assoc, reassoc_of% hβ, M.inv_hom_id_assoc,
      reassoc_of% e7]
    exact comp_comp_comp_map_eq (HH p) φ completionIso.inv Φ.inv huv (hδ (p - 1) p (by omega))
  · -- the bottom map of the middle column
    intro n
    have h₁ : α.inv ≫ limit.π (cohTower p) ⟨n⟩ =
        limit.π (principalDerivedTensorSystem A f K ⋙ HH p) ⟨n⟩ ≫ (HH p).map (c.inv.app ⟨n⟩) :=
      HasLimit.isoOfNatIso_inv_π (cp p) ⟨n⟩
    have h₂ : Φ.hom ≫ completionIso.hom ≫ T.mor₁ ≫
        DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n) ≫ c.inv.app ⟨n⟩ =
          L.mor₁ ≫ proj₂ n := by
      have : Φ.hom ≫ completionIso.hom = φ := by simp [Φ]
      rw [reassoc_of% this]
      exact comp_comp_comp_inv_eq hφ₁ (c.app ⟨n⟩) (hι₂π n)
    rw [Category.assoc, Category.assoc, h₁, reassoc_of% (e9 n)]
    exact map_comp_map_comp_map_eq (HH p) h₂
  · -- the bottom comparison
    rw [hbottom', CompletionSequences.firstDerivedLimitIso_π_assoc, e8, ← Category.assoc,
      pi_mapIso_hom_comp_lift (cp (p - 1)) previousOut]
  · -- the top row is exact
    refine ShortComplex.shortExact_of_iso ?_ hTop
    refine ShortComplex.isoMk (Iso.refl _) α.symm (Iso.refl _) ?_ ?_ <;> simp
  · -- the middle row is exact
    refine ShortComplex.shortExact_of_iso ?_ hMiddle
    refine ShortComplex.isoMk (Iso.refl _) ((HH p).mapIso Φ).symm (Iso.refl _) ?_ ?_
    · simp only [middleIn, Iso.refl_hom, Category.id_comp, Iso.symm_hom, Functor.mapIso_inv]
    · simp only [middleOut, Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
      rw [← (HH p).map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
  · -- the left column is exact
    exact hLeft
  · -- the middle column is exact
    refine ShortComplex.shortExact_of_iso ?_ hColumn
    refine ShortComplex.isoMk β.symm ((HH p).mapIso Φ).symm α.symm ?_ ?_
    · simp
    · exact ((HH p).mapIso Φ).inv_hom_id_assoc _
  · -- the upper square commutes
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (((HH p).mapIso Φ).inv_hom_id_assoc _)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ α.inv) hcomm1).trans (Category.assoc _ _ _))))
  · -- the right-hand triangle commutes
    have r : (HH p).map Φ.hom ≫ columnOut ≫ topOut =
        ((HH p).map Φ.hom ≫ columnOut ≫ α.inv) ≫ α.hom ≫ topOut := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (congrArg ((HH p).map Φ.hom ≫ ·) hcomm2).trans r
  · -- the lower square commutes
    exact (congrArg (· ≫ β.hom ≫ columnIn ≫ (HH p).map Φ.inv) hbottom).trans hlow


/-- **Formal functions for a principal ideal on a ringed space: [Stacks, Tag 0H3C].** Let
`(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative ring
`A`, let `f ∈ A` and let `E ∈ D(𝒪_X)`. Let `E_n = E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` be the
`f`-power Koszul tower, the cone of multiplication by `f^(n+1)` on `E`, so that there are
distinguished triangles `E ⟶ E ⟶ E_n ⟶ E[1]`, and let `E^ = R lim E_n`, given with its
distinguished triangle `E^ ⟶ ∏ E_n ⟶ ∏ E_n ⟶ E^[1]` whose middle map is `1 - shift`. Write
`Hᵖ(X, -)` for the cohomology of `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, let `(-)^∧` be derived `f`-adic
completion (a left adjoint `completion` to the inclusion of the derived-complete objects), and
let `p ∈ ℤ`. Then `RΓ(X, E^) ≅ RΓ(X, E)^∧` by an isomorphism `Φ` which, composed with the unit
`RΓ(X, E) ⟶ RΓ(X, E)^∧` and the projections `RΓ(X, E^) ⟶ RΓ(X, E_n)`, gives the maps
`RΓ(X, E) ⟶ RΓ(X, E_n)` induced by `E ⟶ E_n`, and there is the commutative diagram with exact
rows and columns

* the top row `0 ⟶ Hᵖ(X, E)^ ⟶ lim Hᵖ(X, E_n) ⟶ T_f(Hᵖ⁺¹(X, E)) ⟶ 0`, where `Hᵖ(X, E)^` is the
  `f`-adic completion `lim Hᵖ(X, E)/fⁿ⁺¹` and `T_f` the `f`-adic Tate module `lim (-)[fⁿ⁺¹]`;
  its first map is the limit of the maps `Hᵖ(X, E)/fⁿ⁺¹ ⟶ Hᵖ(X, E_n)` induced by `E ⟶ E_n`, its
  second the limit of the boundaries `Hᵖ(X, E_n) ⟶ Hᵖ⁺¹(X, E)[fⁿ⁺¹]` of `E ⟶ E ⟶ E_n ⟶ E[1]`;
* the middle row `0 ⟶ H⁰(Hᵖ(X, E)^∧) ⟶ Hᵖ(X, E^) ⟶ T_f(Hᵖ⁺¹(X, E)) ⟶ 0`, the sequence of
  [Stacks, Tag 0H32] for `K = RΓ(X, E)` read through `Hᵖ(Φ)`;
* the left column `0 ⟶ R¹lim Hᵖ(X, E)[fⁿ] ⟶ H⁰(Hᵖ(X, E)^∧) ⟶ Hᵖ(X, E)^ ⟶ 0` of
  [Stacks, Tag 0BKG];
* the middle column `0 ⟶ R¹lim Hᵖ⁻¹(X, E_n) ⟶ Hᵖ(X, E^) ⟶ lim Hᵖ(X, E_n) ⟶ 0`, whose second
  map is induced by the projections `E^ ⟶ E_n` and whose first descends the boundary of the
  image under `RΓ(X, -)` of the triangle of `E^`, read through the isomorphism
  `Hᵖ⁻¹(X, ∏ E_n) ≅ ∏ Hᵖ⁻¹(X, E_n)`;
* the bottom isomorphism `R¹lim Hᵖ(X, E)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, E_n)`, inverse to `R¹lim` of the
  boundaries `Hᵖ⁻¹(X, E_n) ⟶ Hᵖ(X, E)[fⁿ⁺¹]`;

the right-hand column being the identity of `T_f(Hᵖ⁺¹(X, E))`. -/
@[stacks 0H3C "the whole diagram, with its maps the ones induced by E ⟶ E_n, the boundaries of \
E ⟶ E ⟶ E_n ⟶ E[1], the projections E^ ⟶ E_n and the triangle of E^, the sequences of Stacks \
0BKG and 0H32 read through RΓ(X, E^) ≅ RΓ(X, E)^∧ (compatible with the maps to RΓ(X, E_n)); \
exactness of rows and columns and the three commutativities"]
theorem formalFunctionsDiagram_principalKoszulTower
    (E Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (a : Ehat ⟶ ∏ᶜ fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩)
    (b : (∏ᶜ fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩) ⟶ Ehat⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩) (n + 1) ≫
            (principalKoszulTower X ρ f E).map (homOfLE (Nat.le_succ n)).op) b ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (p : ℤ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let HH (q : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
      let RΓ := derivedSectionsOver X ρ
      let K := RΓ.obj E
      let H (q : ℤ) := (HH q).obj K
      let CE := DerivedCategory.Q.objPreimage E
      let eE := DerivedCategory.Q.objObjPreimageIso E
      let koszulTriangle (n : ℕ) := RΓ.mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (smulComplex X (baseSmul X ρ f) CE ^ (n + 1))))
      let Y := fun n : ℕ ↦ (principalKoszulTower X ρ f E).obj ⟨n⟩
      let limitTriangle := RΓ.mapTriangle.obj (Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π Y n - Pi.π Y (n + 1) ≫
          (principalKoszulTower X ρ f E).map (homOfLE (Nat.le_succ n)).op) b)
      let cohTower (q : ℤ) := (principalKoszulTower X ρ f E ⋙ RΓ) ⋙ HH q
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (H p) f)
      let limitCoh := limit (cohTower p)
      let tate := CompletionSequences.adicTateModule A (H (p + 1)) f
      let H0CompletedHp := (HH 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (H p)))
      let HpEhat := (HH p).obj (RΓ.obj Ehat)
      let R1Torsion := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (H p) f)
      let R1PreviousCoh := CompletionSequences.firstDerivedLimit A (cohTower (p - 1))
      let productComparison : (HH (p - 1)).obj (RΓ.obj (∏ᶜ Y)) ⟶
          CompletionSequences.moduleProduct A (cohTower (p - 1)) :=
        Pi.lift fun n : ℕ ↦ (HH (p - 1)).map (RΓ.map (Pi.π Y n))
      ∃ (S : CompletionSequences.PrincipalCompletionSequences A f completed adj.unit)
        (Φ : RΓ.obj Ehat ≅ completed.obj K),
        let middleIn : H0CompletedHp ⟶ HpEhat :=
          (S.truncation K p).inclusion S.shift ≫ (HH p).map Φ.inv
        let middleOut : HpEhat ⟶ tate := (HH p).map Φ.hom ≫
          (S.truncation K p).projection f S.shift (S.moduleSequence (H (p + 1))).tateIso
        let leftIn : R1Torsion ⟶ H0CompletedHp := (S.moduleSequence (H p)).inclusion
        let leftOut : H0CompletedHp ⟶ ordinaryCompletion := (S.moduleSequence (H p)).projection
        ∃ (termIn : CompletionSequences.powerQuotientSystem A (H p) f ⟶ cohTower p)
          (termOut : cohTower p ⟶ PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f)
          (previousOut : cohTower (p - 1) ⟶
            PrincipalTorsionTower.powerTorsionSystem A (H p) f)
          (topIn : ordinaryCompletion ⟶ limitCoh)
          (topOut : limitCoh ⟶ tate)
          (htop : topIn ≫ topOut = 0)
          (hmiddle : middleIn ≫ middleOut = 0)
          (hleft : leftIn ≫ leftOut = 0)
          (columnIn : R1PreviousCoh ⟶ HpEhat)
          (columnOut : HpEhat ⟶ limitCoh)
          (hcolumn : columnIn ≫ columnOut = 0)
          (bottom : R1Torsion ≅ R1PreviousCoh),
          (∀ n : ℕ, adj.unit.app K ≫ Φ.inv ≫ RΓ.map a ≫ RΓ.map (Pi.π Y n) =
            RΓ.map (eE.inv ≫ DerivedCategory.Q.map
              (CochainComplex.mappingCone.inr (smulComplex X (baseSmul X ρ f) CE ^ (n + 1))))) ∧
          (∀ n : ℕ,
            cokernel.π (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) ≫
                termIn.app ⟨n⟩ =
              (HH p).map (RΓ.map (eE.inv ≫ DerivedCategory.Q.map
                (CochainComplex.mappingCone.inr (smulComplex X (baseSmul X ρ f) CE ^ (n + 1)))))) ∧
          (∀ n : ℕ,
            termOut.app ⟨n⟩ ≫
                kernel.ι (PrincipalTorsionTower.powerMultiplication A (H (p + 1)) (f ^ (n + 1))) =
              (HH 0).homologySequenceδ (koszulTriangle n) p (p + 1) (by omega) ≫
                (HH (p + 1)).map (RΓ.map eE.hom)) ∧
          (∀ n : ℕ,
            previousOut.app ⟨n⟩ ≫
                kernel.ι (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) =
              (HH 0).homologySequenceδ (koszulTriangle n) (p - 1) p (by omega) ≫
                (HH p).map (RΓ.map eE.hom)) ∧
          (∀ n : ℕ, topIn ≫ limit.π (cohTower p) ⟨n⟩ =
            limit.π (CompletionSequences.powerQuotientSystem A (H p) f) ⟨n⟩ ≫ termIn.app ⟨n⟩) ∧
          (∀ n : ℕ, topOut ≫
              limit.π (PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f) ⟨n⟩ =
            limit.π (cohTower p) ⟨n⟩ ≫ termOut.app ⟨n⟩) ∧
          IsIso productComparison ∧
          (productComparison ≫
              cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ columnIn =
            (HH 0).homologySequenceδ limitTriangle (p - 1) p (by omega)) ∧
          (∀ n : ℕ, columnOut ≫ limit.π (cohTower p) ⟨n⟩ =
            (HH p).map (RΓ.map a ≫ RΓ.map (Pi.π Y n))) ∧
          (cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ bottom.inv =
            (Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ (cohTower (p - 1)).obj ⟨n⟩) n ≫ previousOut.app ⟨n⟩) ≫
              cokernel.π (CompletionSequences.moduleDifference A
                (PrincipalTorsionTower.powerTorsionSystem A (H p) f))) ∧
          (ShortComplex.mk topIn topOut htop).ShortExact ∧
          (ShortComplex.mk middleIn middleOut hmiddle).ShortExact ∧
          (ShortComplex.mk leftIn leftOut hleft).ShortExact ∧
          (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
          middleIn ≫ columnOut = leftOut ≫ topIn ∧
          middleOut = columnOut ≫ topOut ∧
          bottom.hom ≫ columnIn = leftIn ≫ middleIn := by
  intro P completion adj completed HH RΓ K H CE eE koszulTriangle Y limitTriangle cohTower
    ordinaryCompletion limitCoh tate H0CompletedHp HpEhat R1Torsion R1PreviousCoh productComparison
  have hB :=
    Stacks.Cohomology.KoszulTowerSections.exists_iso_principalKoszulTower_derivedSections_cone
      X ρ f E
  obtain ⟨c, hc⟩ := hB
  have hC := exists_iso_milnorTriangle_derivedSections X ρ f E Ehat a b hT c
  obtain ⟨φ, ι₂, ι₃, hφ, hι₃, hι₂π, hι₃π, hφ₁, hδ⟩ := hC
  exact formalFunctionsDiagram_of_triangleComparison f K p (principalKoszulTower X ρ f E ⋙ RΓ) c
    (fun n ↦ RΓ.map (eE.inv ≫ DerivedCategory.Q.map
      (CochainComplex.mappingCone.inr (smulComplex X (baseSmul X ρ f) CE ^ (n + 1)))))
    (fun n ↦ (hc n).1)
    (fun n q q' hq ↦ (HH 0).homologySequenceδ (koszulTriangle n) q q' hq ≫
      (HH q').map (RΓ.map eE.hom))
    (fun n q q' hq ↦ (hc n).2 q q' hq) limitTriangle (fun n ↦ RΓ.map (Pi.π Y n))
    (fun n ↦ RΓ.map (Pi.π Y n)) φ ι₂ ι₃ hφ hι₃ hι₂π hι₃π hφ₁ hδ completion adj


/-- **The diagram of [Stacks, Tag 0H32] for `RΓ(X, E)`, in the terms of the Koszul tower of `E`.**
Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)`, let `f ∈ A`, let `E ∈ D(𝒪_X)` with
`f`-power Koszul tower `E_n` and let `E^` be a derived limit of that tower. Then for every `p`
there are an isomorphism `c` of the tower `n ↦ RΓ(X, E_n)` with the `f`-power Koszul tower of
`RΓ(X, E)`, an isomorphism `γ : Hᵖ(X, E^) ≅ Hᵖ(RΓ(X, E)^∧)` and short exact sequences

* `0 ⟶ Hᵖ(X, E)^ ⟶ lim Hᵖ(X, E_n) ⟶ T_f(Hᵖ⁺¹(X, E)) ⟶ 0`,
* `0 ⟶ H⁰(Hᵖ(X, E)^∧) ⟶ Hᵖ(X, E^) ⟶ T_f(Hᵖ⁺¹(X, E)) ⟶ 0`,
* `0 ⟶ R¹lim Hᵖ(X, E)[fⁿ] ⟶ H⁰(Hᵖ(X, E)^∧) ⟶ Hᵖ(X, E)^ ⟶ 0`,
* `0 ⟶ R¹lim Hᵖ⁻¹(X, E_n) ⟶ Hᵖ(X, E^) ⟶ lim Hᵖ(X, E_n) ⟶ 0`,

with an isomorphism `R¹lim Hᵖ(X, E)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, E_n)`, forming a commutative diagram, the
maps being those of [Stacks, Tag 0H32] for `RΓ(X, E)` read through `c` and `γ`. The form of
[Stacks, Tag 0H3C] whose maps are the geometric ones is
`formalFunctionsDiagram_principalKoszulTower`. -/
theorem exists_formalFunctionsDiagram_principalKoszulTower
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hEhat : IsDerivedLimit (principalKoszulTower X ρ f E) Ehat)
    (p : ℤ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let HH (q : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
      let K := (derivedSectionsOver X ρ).obj E
      let H (q : ℤ) := (HH q).obj K
      let cohSystem := principalKoszulTower X ρ f E ⋙ derivedSectionsOver X ρ
      let cohTower (q : ℤ) := cohSystem ⋙ HH q
      let C := DerivedCategory.Q.objPreimage K
      let eK := DerivedCategory.Q.objObjPreimageIso K
      let EA := principalComplexSystem A f C
      let T := CompletionSequences.milnorTriangle A EA
      let coneTriangle (n : ℕ) := DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (H p) f)
      let limitCoh := limit (cohTower p)
      let tate := CompletionSequences.adicTateModule A (H (p + 1)) f
      let H0CompletedHp := (HH 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (H p)))
      let HpEhat := (HH p).obj ((derivedSectionsOver X ρ).obj Ehat)
      let R1Torsion := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (H p) f)
      let R1PreviousCoh := CompletionSequences.firstDerivedLimit A (cohTower (p - 1))
      ∃ (S : CompletionSequences.PrincipalCompletionSequences A f completed adj.unit)
        (c : cohSystem ≅ principalDerivedTensorSystem A f K)
        (γ : HpEhat ≅ (HH p).obj (completed.obj K)),
        let completionIso := completed.mapIso eK.symm ≪≫ S.comparison.iso C
        let cp (q : ℤ) := Functor.isoWhiskerRight c (HH q)
        let middleIn : H0CompletedHp ⟶ HpEhat := (S.truncation K p).inclusion S.shift ≫ γ.inv
        let middleOut : HpEhat ⟶ tate := γ.hom ≫ (S.truncation K p).projection f S.shift
          (S.moduleSequence (H (p + 1))).tateIso
        let leftIn : R1Torsion ⟶ H0CompletedHp := (S.moduleSequence (H p)).inclusion
        let leftOut : H0CompletedHp ⟶ ordinaryCompletion := (S.moduleSequence (H p)).projection
        ∃ (termIn : CompletionSequences.powerQuotientSystem A (H p) f ⟶ cohTower p)
          (termOut : cohTower p ⟶ PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f)
          (previousOut : cohTower (p - 1) ⟶
            PrincipalTorsionTower.powerTorsionSystem A (H p) f)
          (productIso : (HH (p - 1)).obj T.obj₃ ≅
            CompletionSequences.moduleProduct A (cohTower (p - 1)))
          (topIn : ordinaryCompletion ⟶ limitCoh)
          (topOut : limitCoh ⟶ tate)
          (htop : topIn ≫ topOut = 0)
          (hmiddle : middleIn ≫ middleOut = 0)
          (hleft : leftIn ≫ leftOut = 0)
          (columnIn : R1PreviousCoh ⟶ HpEhat)
          (columnOut : HpEhat ⟶ limitCoh)
          (hcolumn : columnIn ≫ columnOut = 0)
          (bottom : R1Torsion ≅ R1PreviousCoh),
          (∀ n : ℕ,
            cokernel.π (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) ≫
                termIn.app ⟨n⟩ =
              (HH p).map (eK.inv ≫ (coneTriangle n).mor₂) ≫ (cp p).inv.app ⟨n⟩) ∧
          (∀ n : ℕ,
            termOut.app ⟨n⟩ ≫
                kernel.ι (PrincipalTorsionTower.powerMultiplication A (H (p + 1)) (f ^ (n + 1))) =
              (cp p).hom.app ⟨n⟩ ≫
                (HH 0).homologySequenceδ (coneTriangle n) p (p + 1) (by omega) ≫
                  (HH (p + 1)).map eK.hom) ∧
          (∀ n : ℕ,
            previousOut.app ⟨n⟩ ≫
                kernel.ι (PrincipalTorsionTower.powerMultiplication A (H p) (f ^ (n + 1))) =
              (cp (p - 1)).hom.app ⟨n⟩ ≫
                (HH 0).homologySequenceδ (coneTriangle n) (p - 1) p (by omega) ≫
                  (HH p).map eK.hom) ∧
          (∀ n : ℕ, topIn ≫ limit.π (cohTower p) ⟨n⟩ =
            limit.π (CompletionSequences.powerQuotientSystem A (H p) f) ⟨n⟩ ≫ termIn.app ⟨n⟩) ∧
          (∀ n : ℕ, topOut ≫
              limit.π (PrincipalTorsionTower.powerTorsionSystem A (H (p + 1)) f) ⟨n⟩ =
            limit.π (cohTower p) ⟨n⟩ ≫ termOut.app ⟨n⟩) ∧
          (∀ n : ℕ, productIso.hom ≫
              Pi.π (fun n : ℕ ↦ (cohTower (p - 1)).obj ⟨n⟩) n =
            (HH (p - 1)).map (DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n)) ≫
              (cp (p - 1)).inv.app ⟨n⟩) ∧
          (productIso.hom ≫
              cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ columnIn =
            (HH 0).homologySequenceδ T (p - 1) p (by omega) ≫
              (HH p).map completionIso.inv ≫ γ.inv) ∧
          (cokernel.π (CompletionSequences.moduleDifference A (cohTower (p - 1))) ≫ bottom.inv =
            (Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ (cohTower (p - 1)).obj ⟨n⟩) n ≫ previousOut.app ⟨n⟩) ≫
              cokernel.π (CompletionSequences.moduleDifference A
                (PrincipalTorsionTower.powerTorsionSystem A (H p) f))) ∧
          (∀ n : ℕ, columnOut ≫ limit.π (cohTower p) ⟨n⟩ =
            γ.hom ≫ (HH p).map (completionIso.hom ≫ T.mor₁ ≫
              DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ EA.obj ⟨n⟩) n)) ≫
              (cp p).inv.app ⟨n⟩) ∧
          (ShortComplex.mk topIn topOut htop).ShortExact ∧
          (ShortComplex.mk middleIn middleOut hmiddle).ShortExact ∧
          (ShortComplex.mk leftIn leftOut hleft).ShortExact ∧
          (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
          middleIn ≫ columnOut = leftOut ≫ topIn ∧
          middleOut = columnOut ≫ topOut ∧
          bottom.hom ≫ columnIn = leftIn ≫ middleIn ∧
          Nonempty ((derivedSectionsOver X ρ).obj Ehat ≅ completed.obj K) := by
  intro P completion adj completed HH K H cohSystem cohTower C eK EA T coneTriangle
    ordinaryCompletion limitCoh tate H0CompletedHp HpEhat R1Torsion R1PreviousCoh
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  -- The identification of the geometric tower with the algebraic one.
  obtain ⟨c⟩ := nonempty_iso_koszulTower_comp_derivedSections_object X ρ f E
  -- Clause (7): `RΓ(X, E^) ≅ RΓ(X, E)^∧`, and its cohomology.
  have h7 := nonempty_iso_derivedSections_koszulTower_derivedCompletion X ρ f E Ehat hEhat
  dsimp only at h7
  obtain ⟨hobj, -, hhom⟩ := h7 completion adj
  obtain ⟨γ⟩ := hhom p
  -- The algebraic diagram of Tag 0H32 at `K = RΓ(X, E)`.
  have h32 := PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison A f K p
  dsimp only at h32
  obtain ⟨S, hS⟩ := h32 completion adj
  obtain ⟨termIn, termOut, previousOut, productIso, topIn, topOut, htop, columnIn, columnOut,
    hcolumn, bottom, e1, e2, e3, e4, e5, e6, e7, e8, e9, hTop, hMiddle, hLeft, hColumn,
    hcomm1, hcomm2, hcomm3⟩ := hS
  refine ⟨S, c, γ, ?_⟩
  intro completionIso cp middleIn middleOut leftIn leftOut
  let α := HasLimit.isoOfNatIso (cp p)
  let β := CompletionSequences.firstDerivedLimitIso A (cp (p - 1))
  refine ⟨termIn ≫ (cp p).inv, (cp p).hom ≫ termOut, (cp (p - 1)).hom ≫ previousOut,
    productIso ≪≫ (Pi.mapIso fun n : ℕ ↦ (cp (p - 1)).app ⟨n⟩).symm,
    topIn ≫ α.inv, α.hom ≫ topOut, ?_, ?_, (S.moduleSequence (H p)).zero,
    β.hom ≫ columnIn ≫ γ.inv, γ.hom ≫ columnOut ≫ α.inv, ?_, bottom ≪≫ β.symm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hobj⟩
  · -- the top row is a complex
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact htop
  · -- the middle row is a complex
    simp only [middleIn, middleOut, Category.assoc, Iso.inv_hom_id_assoc]
    exact S.truncation_zero K p
  · -- the middle column is a complex
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc columnIn columnOut,
      hcolumn, zero_comp, comp_zero]
  · -- the reduction maps of the top row
    intro n
    simp only [H, HH, C, eK, coneTriangle, NatTrans.comp_app]
    exact Eq.trans (Category.assoc _ _ _).symm (by rw [e1 n]; rfl)
  · -- the torsion maps of the top row
    intro n
    simp only [H, HH, C, eK, coneTriangle, NatTrans.comp_app]
    exact Eq.trans (Category.assoc _ _ _) (by rw [e2 n]; rfl)
  · -- the torsion maps in degree `p - 1`
    intro n
    simp only [H, HH, C, eK, coneTriangle, NatTrans.comp_app]
    exact Eq.trans (Category.assoc _ _ _) (by rw [e3 n]; rfl)
  · -- the left-hand map of the top row
    intro n
    simp only [α, NatTrans.comp_app, Category.assoc]
    rw [HasLimit.isoOfNatIso_inv_π, reassoc_of% e4 n]
  · -- the right-hand map of the top row
    intro n
    simp only [α, NatTrans.comp_app, Category.assoc]
    rw [e5 n, ← Category.assoc, HasLimit.isoOfNatIso_hom_π, Category.assoc]
  · -- the product comparison
    intro n
    simp only [HH, EA, C]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Pi.mapIso_inv_π, ← Category.assoc, e6 n, Iso.app_inv]
    rfl
  · -- the top map of the middle column
    simp only [HH, T, EA, C, eK, completionIso, completed, P]
    simp only [β, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [CompletionSequences.firstDerivedLimitIso_π_assoc, Iso.inv_hom_id_assoc, reassoc_of% e7]
    exact Category.assoc _ _ _
  · -- the bottom comparison
    simp only [β, Iso.trans_inv, Iso.symm_inv]
    rw [CompletionSequences.firstDerivedLimitIso_π_assoc, e8, ← Category.assoc,
      pi_mapIso_hom_comp_lift (cp (p - 1)) previousOut]
  · -- the bottom map of the middle column
    intro n
    simp only [HH, T, EA, C, eK, completionIso, completed, P]
    simp only [α, Category.assoc]
    rw [HasLimit.isoOfNatIso_inv_π, reassoc_of% e9 n]
    rfl
  · -- the top row is exact
    refine ShortComplex.shortExact_of_iso ?_ hTop
    refine ShortComplex.isoMk (Iso.refl _) α.symm (Iso.refl _) ?_ ?_ <;> simp
  · -- the middle row is exact
    refine ShortComplex.shortExact_of_iso ?_ hMiddle
    refine ShortComplex.isoMk (Iso.refl _) γ.symm (Iso.refl _) ?_ ?_
    · simp only [middleIn, Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    · simp only [middleOut, H, HH, Iso.symm_hom, Iso.inv_hom_id_assoc, Iso.refl_hom,
        Category.comp_id]
  · -- the left column is exact
    exact hLeft
  · -- the middle column is exact
    refine ShortComplex.shortExact_of_iso ?_ hColumn
    refine ShortComplex.isoMk β.symm γ.symm α.symm ?_ ?_ <;> simp
  · -- the upper square commutes
    simp only [middleIn, leftOut, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc _ columnOut, hcomm1, Category.assoc]
  · -- the right-hand triangle commutes
    simp only [middleOut, Category.assoc, Iso.inv_hom_id_assoc]
    rw [hcomm2]
  · -- the lower square commutes
    simp only [middleIn, leftIn, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Category.assoc bottom.hom, hcomm3, Category.assoc]

end Sections


/-! ### Formal functions along the quotient tower -/

section Quotient

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) (f : A)

/-- **The `f`-power Koszul tower of a complex of sheaves of `𝒪_X`-modules depends on the complex
only through its image in `D(𝒪_X)`.** This is the sheaf-side counterpart of
`nonempty_iso_principalDerivedTensorSystem_of_iso`, and it is proved the same way: the given
isomorphism in `D(𝒪_X)` is realized by an actual morphism of complexes through a K-injective
resolution, and a morphism of complexes which is invertible in `D(𝒪_X)` induces a levelwise
isomorphism of Koszul towers. -/
theorem nonempty_iso_principalKoszulComplexTower_of_iso
    (a : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))))
    {C C' : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (e : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj C') :
    Nonempty (principalKoszulComplexTower X a C ⋙ DerivedCategory.Q ≅
      principalKoszulComplexTower X a C' ⋙ DerivedCategory.Q) := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  obtain ⟨I, ψ, p, hψ, hpQ⟩ := exists_isIso_Q_map_of_iso e
  have h₁ : IsIso (Functor.whiskerRight (koszulComplexTowerMap X a ψ) DerivedCategory.Q) :=
    Stacks.Cohomology.KoszulTowerSections.isIso_whiskerRight_koszulComplexTowerMap X a ψ
  have h₂ : IsIso (Functor.whiskerRight (koszulComplexTowerMap X a p) DerivedCategory.Q) :=
    Stacks.Cohomology.KoszulTowerSections.isIso_whiskerRight_koszulComplexTowerMap X a p
  exact ⟨@asIso _ _ _ _ _ h₁ ≪≫ (@asIso _ _ _ _ _ h₂).symm⟩

/-- **The tower of cones of the powers of multiplication by `f` is the `f`-power Koszul tower.**
The inverse system `Ksys` of [Stacks, Tag 0H3D] — the cones of the iterated multiplication by the
image of `f` on `ℱ` placed in degree zero — is the `f`-power Koszul tower of `ℱ`, viewed as an
object of `D(𝒪_X)` in cohomological degree zero. -/
theorem nonempty_iso_Ksys_principalKoszulTower (ℱ : SheafOfModules.{u} (structureSheafRing X)) :
    Nonempty (Ksys ((baseSmul X ρ f).app ℱ) ≅ principalKoszulTower X ρ f
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ)) := by
  obtain ⟨t⟩ := nonempty_iso_principalKoszulComplexTower_of_iso X (baseSmul X ρ f)
    (C := sgl.obj ℱ)
    (C' := DerivedCategory.Q.objPreimage
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ))
    (DerivedCategory.Q.objObjPreimageIso
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ)).symm
  exact ⟨ksysIso X (baseSmul X ρ f) ℱ ≪≫ t⟩

/-- A derived limit `Ê` of the tower `Ksys` of cones, which is also one of the `f`-power Koszul
tower of `ℱ` in degree zero, together with its comparisons with `ℱ^` and with that tower. -/
private theorem exists_isDerivedLimit_ksys_principalKoszulTower
    (ℱ : SheafOfModules.{u} (structureSheafRing X)) (hstab : Stabilizes ((baseSmul X ρ f).app ℱ))
    (Fhat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hFhat : IsDerivedLimit (Csys ((baseSmul X ρ f).app ℱ)) Fhat) :
    ∃ (Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
      (_ : IsDerivedLimit (Ksys ((baseSmul X ρ f).app ℱ)) Ehat)
      (_ : Ksys ((baseSmul X ρ f).app ℱ) ≅ principalKoszulTower X ρ f
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ)),
      Nonempty (Ehat ≅ Fhat) ∧ IsDerivedLimit (principalKoszulTower X ρ f
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ))
        Ehat := by
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨Ehat, hEhat⟩ := exists_isDerivedLimit (Ksys ((baseSmul X ρ f).app ℱ))
  obtain ⟨eEF⟩ := nonempty_iso_isDerivedLimit_koszulTower_quotientTower X ρ f ℱ hstab
    Ehat Fhat hEhat hFhat
  obtain ⟨t⟩ := nonempty_iso_Ksys_principalKoszulTower X ρ f ℱ
  have _ : HasProduct fun n : ℕ ↦ (principalKoszulTower X ρ f
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ)).obj
        ⟨n⟩ :=
    hasProduct_of_equiv_of_iso (fun n : ℕ ↦ (Ksys ((baseSmul X ρ f).app ℱ)).obj ⟨n⟩) _
      (Equiv.refl ℕ) fun n : ℕ ↦ (t.app ⟨n⟩).symm
  exact ⟨Ehat, hEhat, t, ⟨eEF⟩, IsDerivedLimit.of_natIso t hEhat⟩

/-- **Clause (7) of [Stacks, Tag 0H3E]: `RΓ(X, ℱ^) = RΓ(X, ℱ)^∧` on a ringed space.** Let
`(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative ring
`A`, let `f ∈ A` and let `ℱ` be a sheaf of `𝒪_X`-modules whose `f`-power torsion stabilizes.  Let
`ℱ^` be a derived limit of the tower of honest quotients `ℱ/f^(n+1)ℱ`.  Then

`RΓ(X, ℱ^) ≅ RΓ(X, ℱ)^∧`,

the object `RΓ(X, ℱ^)` is derived complete for `(f)`, and for every `p` its `p`-th cohomology
module is that of `RΓ(X, ℱ)^∧` — the identification `Hᵖ(X, ℱ^) = Hᵖ(RΓ(X, ℱ)^∧)` the diagram of
the source rests on.

This is the displayed equality of [Stacks, Tag 0BLD] on an arbitrary ringed space: the Koszul
form of it is `nonempty_iso_derivedSections_koszulTower_derivedCompletion`, and the
pro-isomorphism of [Stacks, Tag 0H3D] replaces the Koszul tower by the quotient tower.  No
quasi-coherence is needed, only stabilization of the `f`-power torsion. -/
@[stacks 0H3E "the identification RΓ(X, ℱ^) = RΓ(X, ℱ)^∧ and the resulting \
Hᵖ(X, ℱ^) = Hᵖ(RΓ(X, ℱ)^∧), on a ringed space, with derived f-adic completion presented as in \
Stacks 0BKG by an arbitrary left adjoint to the inclusion of the derived-complete objects; also \
derived completeness of RΓ(X, ℱ^)"]
theorem nonempty_iso_derivedSections_quotientTower_derivedCompletion
    (ℱ : SheafOfModules.{u} (structureSheafRing X)) (hstab : Stabilizes ((baseSmul X ρ f).app ℱ))
    (Fhat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hFhat : IsDerivedLimit (Csys ((baseSmul X ρ f).app ℱ)) Fhat) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let sglF :=
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ
      Nonempty ((derivedSectionsOver X ρ).obj Fhat ≅
          completed.obj ((derivedSectionsOver X ρ).obj sglF)) ∧
        IsDerivedComplete (Ideal.span {f}) ((derivedSectionsOver X ρ).obj Fhat) ∧
        ∀ p : ℤ, Nonempty
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
              ((derivedSectionsOver X ρ).obj Fhat) ≅
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
              (completed.obj ((derivedSectionsOver X ρ).obj sglF))) := by
  intro P completion adj completed sglF
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨Ehat, -, -, ⟨eEF⟩, hEhat'⟩ :=
    exists_isDerivedLimit_ksys_principalKoszulTower X ρ f ℱ hstab Fhat hFhat
  -- The Koszul form of the identification.
  have h7 := nonempty_iso_derivedSections_koszulTower_derivedCompletion X ρ f sglF Ehat hEhat'
  dsimp only at h7
  obtain ⟨hobj, -, -⟩ := h7 completion adj
  have eFhat : (derivedSectionsOver X ρ).obj Fhat ≅
      completed.obj ((derivedSectionsOver X ρ).obj sglF) :=
    ((derivedSectionsOver X ρ).mapIso eEF).symm ≪≫ hobj.some
  refine ⟨⟨eFhat⟩, ?_, fun p ↦
    ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).mapIso eFhat⟩⟩
  exact DerivedCompleteRecurrence.isDerivedComplete_of_iso eFhat.symm
    (completion.obj ((derivedSectionsOver X ρ).obj sglF)).2


/-- **Formal functions for a principal ideal along the quotient tower: the whole diagram of
[Stacks, Tag 0H3E].** Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism
from a commutative ring `A`, let `f ∈ A`, let `ℱ` be a sheaf of `𝒪_X`-modules whose `f`-power
torsion stabilizes, and let `ℱ^` be a derived limit of the tower of quotients `ℱ/f^(n+1)ℱ`.  Then
for every `p` the commutative diagram of the source exists, with exact rows and columns:

* the top row `0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`;
* the middle row `0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ^) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`;
* the left column `0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0`;
* the middle column `0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, ℱ^) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`;
* the bottom comparison `R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`;

the three commutativities that make the nine terms a diagram, and the identification
`RΓ(X, ℱ^) ≅ RΓ(X, ℱ)^∧`.  As in [Stacks, Tag 0H32], `S` is the data of the two completion
sequences of [Stacks, Tag 0BKG] for `RΓ(X, ℱ)`, so the middle row and the left column are that
source's own maps, and `γ` is the identification of `Hᵖ(X, ℱ^)` with `Hᵖ(RΓ(X, ℱ)^∧)`.

This is `exists_formalFunctionsDiagram_principalKoszulTower` with the `f`-power Koszul tower
replaced by the tower of honest quotients, the replacement being licensed by the pro-isomorphism
of [Stacks, Tag 0H3D].  Only the two tower-dependent terms and `Hᵖ(X, ℱ^)` change, and they
change by isomorphism: a pro-isomorphism shifts the index, so the limit and the first derived
limit of the two cohomology towers agree as modules while the individual projections do not
correspond, which is why the per-level normalizations of the Koszul form are not asserted here.
The middle column *is* available with its maps normalized directly by the Milnor triangle of the
quotient tower, as `Stacks.Cohomology.QuotientTowerFormalFunctions`
`.exists_shortExact_homology_derivedSections_quotientTower`. -/
@[stacks 0H3E "the whole diagram for the quotient tower ℱ/fⁿℱ: the top row, the middle row, the \
left column, the middle column, the bottom isomorphism, the three commutativities, and the \
identification RΓ(X, ℱ^) = RΓ(X, ℱ)^∧; derived f-adic completion presented as in Stacks 0BKG by \
an arbitrary left adjoint to the inclusion of the derived-complete objects"]
theorem exists_formalFunctionsDiagram_quotientTower
    (ℱ : SheafOfModules.{u} (structureSheafRing X)) (hstab : Stabilizes ((baseSmul X ρ f).app ℱ))
    (Fhat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hFhat : IsDerivedLimit (Csys ((baseSmul X ρ f).app ℱ)) Fhat)
    (p : ℤ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let HH (q : ℤ) := DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
      let sglF :=
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj ℱ
      let K := (derivedSectionsOver X ρ).obj sglF
      let H (q : ℤ) := (HH q).obj K
      let quotTower (q : ℤ) :=
        (Csys ((baseSmul X ρ f).app ℱ) ⋙ derivedSectionsOver X ρ) ⋙ HH q
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (H p) f)
      let limitQuot := limit (quotTower p)
      let tate := CompletionSequences.adicTateModule A (H (p + 1)) f
      let H0CompletedHp := (HH 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (H p)))
      let HpFhat := (HH p).obj ((derivedSectionsOver X ρ).obj Fhat)
      let R1Torsion := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (H p) f)
      let R1PreviousQuot := CompletionSequences.firstDerivedLimit A (quotTower (p - 1))
      ∃ (S : CompletionSequences.PrincipalCompletionSequences A f completed adj.unit)
        (γ : HpFhat ≅ (HH p).obj (completed.obj K)),
        let middleIn : H0CompletedHp ⟶ HpFhat := (S.truncation K p).inclusion S.shift ≫ γ.inv
        let middleOut : HpFhat ⟶ tate := γ.hom ≫ (S.truncation K p).projection f S.shift
          (S.moduleSequence (H (p + 1))).tateIso
        let leftIn : R1Torsion ⟶ H0CompletedHp := (S.moduleSequence (H p)).inclusion
        let leftOut : H0CompletedHp ⟶ ordinaryCompletion := (S.moduleSequence (H p)).projection
        ∃ (topIn : ordinaryCompletion ⟶ limitQuot)
          (topOut : limitQuot ⟶ tate)
          (htop : topIn ≫ topOut = 0)
          (hmiddle : middleIn ≫ middleOut = 0)
          (hleft : leftIn ≫ leftOut = 0)
          (columnIn : R1PreviousQuot ⟶ HpFhat)
          (columnOut : HpFhat ⟶ limitQuot)
          (hcolumn : columnIn ≫ columnOut = 0)
          (bottom : R1Torsion ≅ R1PreviousQuot),
          (ShortComplex.mk topIn topOut htop).ShortExact ∧
          (ShortComplex.mk middleIn middleOut hmiddle).ShortExact ∧
          (ShortComplex.mk leftIn leftOut hleft).ShortExact ∧
          (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
          middleIn ≫ columnOut = leftOut ≫ topIn ∧
          middleOut = columnOut ≫ topOut ∧
          bottom.hom ≫ columnIn = leftIn ≫ middleIn ∧
          Nonempty ((derivedSectionsOver X ρ).obj Fhat ≅ completed.obj K) := by
  intro P completion adj completed HH sglF K H quotTower ordinaryCompletion limitQuot tate
    H0CompletedHp HpFhat R1Torsion R1PreviousQuot
  have _ : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨Ehat, hEhat, t, ⟨eEF⟩, hEhat'⟩ :=
    exists_isDerivedLimit_ksys_principalKoszulTower X ρ f ℱ hstab Fhat hFhat
  -- The levelwise comparison of the two towers of cohomology.
  let tc (q : ℤ) : (Ksys ((baseSmul X ρ f).app ℱ) ⋙ derivedSectionsOver X ρ) ⋙ HH q ≅
      (principalKoszulTower X ρ f sglF ⋙ derivedSectionsOver X ρ) ⋙ HH q :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight t (derivedSectionsOver X ρ)) (HH q)
  -- The quotient-tower column, which carries the two identifications of outer terms.
  obtain ⟨-, a, b, -, hq⟩ :=
    exists_shortExact_homology_derivedSections_quotientTower X ρ f ℱ hstab Fhat Ehat hFhat hEhat
  obtain ⟨-, -, -, -, -, -, -, -, hlimQ, hfdlQ⟩ := hq p
  obtain ⟨lq⟩ := hlimQ
  obtain ⟨mq⟩ := hfdlQ
  -- The three identifications the transport runs along.
  let lam : limitQuot ≅ limit (
      (principalKoszulTower X ρ f sglF ⋙ derivedSectionsOver X ρ) ⋙ HH p) :=
    lq ≪≫ HasLimit.isoOfNatIso (tc p)
  let mu : R1PreviousQuot ≅ CompletionSequences.firstDerivedLimit A
      ((principalKoszulTower X ρ f sglF ⋙ derivedSectionsOver X ρ) ⋙ HH (p - 1)) :=
    mq ≪≫ CompletionSequences.firstDerivedLimitIso A (tc (p - 1))
  let nu : HpFhat ≅ (HH p).obj ((derivedSectionsOver X ρ).obj Ehat) :=
    (HH p).mapIso ((derivedSectionsOver X ρ).mapIso eEF).symm
  -- The Koszul form of the diagram.
  have h3c := exists_formalFunctionsDiagram_principalKoszulTower X ρ f sglF Ehat hEhat' p
  dsimp only at h3c
  obtain ⟨S, c, γ₀, termIn, termOut, previousOut, productIso, topIn, topOut, htop, hmiddle,
    hleft, columnIn, columnOut, hcolumn, bottom, -, -, -, -, -, -, -, -, -,
    hTop, hMiddle, hLeft, hColumn, hc1, hc2, hc3, hRΓ⟩ := h3c completion adj
  refine ⟨S, nu ≪≫ γ₀, ?_⟩
  intro middleIn middleOut leftIn leftOut
  refine ⟨topIn ≫ lam.inv, lam.hom ≫ topOut, ?_, ?_, (S.moduleSequence (H p)).zero,
    mu.hom ≫ columnIn ≫ nu.inv, nu.hom ≫ columnOut ≫ lam.inv, ?_, bottom ≪≫ mu.symm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨((derivedSectionsOver X ρ).mapIso eEF).symm ≪≫ hRΓ.some⟩⟩
  · -- the top row is a complex
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact htop
  · -- the middle row is a complex
    simp only [middleIn, middleOut, K, H, HH, Iso.trans_inv, Iso.trans_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact S.truncation_zero _ p
  · -- the middle column is a complex
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc columnIn columnOut,
      hcolumn, zero_comp, comp_zero]
  · -- the top row is exact
    refine ShortComplex.shortExact_of_iso ?_ hTop
    refine ShortComplex.isoMk (Iso.refl _) lam.symm (Iso.refl _) ?_ ?_ <;> simp
  · -- the middle row is exact
    refine ShortComplex.shortExact_of_iso ?_ hMiddle
    refine ShortComplex.isoMk (Iso.refl _) nu.symm (Iso.refl _) ?_ ?_
    · simp only [middleIn, K, H, HH, Iso.refl_hom, Category.id_comp, Iso.symm_hom,
        Iso.trans_inv, Category.assoc]
    · simp only [middleOut, K, H, HH, Iso.symm_hom, Iso.trans_hom, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
  · -- the left column is exact
    exact hLeft
  · -- the middle column is exact
    refine ShortComplex.shortExact_of_iso ?_ hColumn
    refine ShortComplex.isoMk mu.symm nu.symm lam.symm ?_ ?_ <;> simp
  · -- the upper square commutes
    simp only [middleIn, leftOut, K, H, HH, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [← Category.assoc]
    rw [hc1]
  · -- the right-hand triangle commutes
    simp only [middleOut, K, H, HH, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [hc2]
  · -- the lower square commutes
    simp only [middleIn, leftIn, K, H, HH, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc]
    simp only [← Category.assoc]
    rw [hc3]
    simp only [Category.assoc]

end Quotient

end Stacks.Cohomology.PrincipalFormalFunctions

end
